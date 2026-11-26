#!/usr/bin/env python3
"""Merge-gated posting for RoadmapLab: one file under posts/ = one outgoing post.

The human act is the merge: a post is sent only after a pull request that adds or changes its
file has been merged into main of this repository by the approver (repo variable POST_APPROVER).
Nothing else validates. Until the repo variable POSTING is `on`, everything is a dry run.

usage:
  post.py check FILE...                  gluing check (exit 1 on any violation)
  post.py plan BEFORE AFTER              post files added or changed in BEFORE..AFTER, not yet posted
  post.py verify-merge SHA APPROVER FILE exit 0 iff SHA is the merge of a PR, merged by APPROVER,
                                         whose own file list contains FILE
  post.py render FILE...                 the exact payload, as Markdown (for the PR's job summary)
  post.py send FILE [--dry-run]          send one post (needs GH_TOKEN = the poster's token)

File format: a front matter block between `---` lines, of flat `key: value` pairs, then the exact
body. Keys:
  kind     pr | review | comment                                   (required)
  repo     owner/name of the target repository                    (required)
  number   target PR or issue number                              (review, comment)
  event    COMMENT (default) | REQUEST_CHANGES                    (review; APPROVE is refused)
  title    PR title                                               (pr)
  base     base branch of the target (default main)               (pr)
  branch   branch name to create on the fork                      (pr)
  fork     owner/name of the poster's fork (default: repo variable POST_FORK)  (pr)
  patch    path, in this repository, of a `git diff` patch        (pr)
  cert1    URL of a passing cert1 run on the patched tree; required if the patch touches *.lean
  label_comment   text of a follow-up comment, e.g. `awaiting-review` (pr; optional)
  draft    true to open the PR as a draft (pr; optional)
Ledger: reports/posted.tsv (path, sha256 of the file, url, UTC date). A path is never posted twice;
a file changed after posting is reported, not re-sent. Stdlib only.
"""
import datetime, hashlib, json, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, "reports", "posted.tsv")
DISCLOSURE = re.compile(r"(AI-prepared|AI-assisted|prepared with|written with).{0,80}(Claude|GPT|Gemini|model)", re.I | re.S)
# Gluing check: these block a post until a human removes or rewrites them.
BLOCKERS = [
    (re.compile(r"OBSERVATION", re.I), "an OBSERVATION mark is still present"),
    (re.compile(r"\[INTERNAL"), "an [INTERNAL…] mark is still present"),
    (re.compile(r"TODO-USER|<!--\s*user:", re.I), "a placeholder for the user is still present"),
    (re.compile(r"<[^<>\n]*(once published|pending)[^<>\n]*>", re.I), "an unfilled <…pending…> placeholder"),
    (re.compile(r"machine-verified across versions", re.I), "forbidden wording: 'machine-verified across versions'"),
    (re.compile(r"/data/|/home/|/tmp/|\.internal\.cloudapp|~/work"), "a local path or hostname"),
    (re.compile(r"\bBoss\b|RoadmapLab session|MeaningOps session|cross-session", re.I), "internal session vocabulary"),
]


def parse(path):
    text = open(path, encoding="utf-8").read()
    m = re.match(r"---\n(.*?)\n---\n(.*)\Z", text, re.S)
    if not m:
        raise ValueError("no front matter block")
    meta = {}
    for line in m.group(1).splitlines():
        if line.strip() and not line.lstrip().startswith("#"):
            k, _, v = line.partition(":")
            meta[k.strip()] = v.strip()
    return meta, m.group(2).strip() + "\n", text


def check(path):
    errs = []
    try:
        meta, body, _ = parse(path)
    except ValueError as e:
        return [str(e)]
    kind = meta.get("kind")
    if kind not in ("pr", "review", "comment"):
        errs.append(f"kind must be pr | review | comment, not {kind!r}")
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", meta.get("repo", "")):
        errs.append("repo must be owner/name")
    if kind in ("review", "comment") and not meta.get("number", "").isdigit():
        errs.append("number is required for a review or a comment")
    if kind in ("review", "comment") and not body.lstrip().startswith("🤖"):
        errs.append("a review or comment written with AI assistance must start with 🤖 (TauCetiRoadmap CONTRIBUTING)")
    if kind == "review" and meta.get("event", "COMMENT") not in ("COMMENT", "REQUEST_CHANGES"):
        errs.append("review event must be COMMENT or REQUEST_CHANGES (approvals are never automated)")
    if kind == "pr":
        for k in ("title", "branch", "patch"):
            if not meta.get(k):
                errs.append(f"{k} is required for a pr")
        p = os.path.join(ROOT, meta.get("patch", ""))
        if meta.get("patch") and not os.path.isfile(p):
            errs.append(f"patch {meta['patch']} not found")
        elif meta.get("patch"):
            touched = re.findall(r"^\+\+\+ b/(\S+)", open(p, encoding="utf-8").read(), re.M)
            if any(t.endswith(".lean") for t in touched) and not meta.get("cert1", "").startswith("https://"):
                errs.append("the patch touches Lean files: cert1 must link a passing cert1 run")
            added = "\n".join(l[1:] for l in open(p, encoding="utf-8").read().splitlines()
                               if l.startswith("+") and not l.startswith("+++"))
            for rx, why in BLOCKERS:
                if rx.search(added):
                    errs.append(f"patch: {why}")
            for t in touched:
                if not t.startswith("TauCetiRoadmap/"):
                    errs.append(f"the patch touches {t}, outside TauCetiRoadmap/ (CONTRIBUTING: a roadmap PR touches only its own directory)")
    if not DISCLOSURE.search(body):
        errs.append("no AI-use disclosure line naming the model")
    for rx, why in BLOCKERS:
        for target in (body, json.dumps(meta, ensure_ascii=False)):
            if rx.search(target):
                errs.append(why)
                break
    return errs


def ledger():
    d = {}
    if os.path.isfile(LEDGER):
        for line in open(LEDGER, encoding="utf-8"):
            if line.strip() and not line.startswith("#"):
                c = line.rstrip("\n").split("\t")
                d[c[0]] = c
    return d


def sh(*a, check=True, capture=True, env=None):
    r = subprocess.run(a, capture_output=capture, text=True, env=env)
    if check and r.returncode:
        raise RuntimeError(f"{' '.join(a)} failed: {r.stderr.strip()[:500]}")
    return r.stdout.strip() if capture else ""


def plan(before, after):
    if re.fullmatch(r"0+", before):
        files = sh("git", "-C", ROOT, "ls-tree", "-r", "--name-only", after, "posts").split("\n")
    else:
        files = sh("git", "-C", ROOT, "diff", "--name-only", "--diff-filter=AM", before, after, "--", "posts").split("\n")
    files = [f for f in files if f.endswith(".md") and f.startswith("posts/") and "/patches/" not in f]
    done = ledger()
    out = []
    for f in files:
        if f in done:
            print(f"skip {f}: already posted at {done[f][2]}", file=sys.stderr)
            if hashlib.sha256(open(os.path.join(ROOT, f), "rb").read()).hexdigest() != done[f][1]:
                print(f"::warning::{f} changed after it was posted; it is not re-sent", file=sys.stderr)
            continue
        out.append(f)
    print("\n".join(out))


def verify_merge(sha, approver, path):
    """Validated iff a PR into main with merge_commit_sha == sha, merged by the approver, touches path."""
    import time
    repo = os.environ["GITHUB_REPOSITORY"]
    prs = []
    for delay in (0, 5, 15, 45):  # the commit-to-PR association can lag a few seconds
        time.sleep(delay)
        prs = [p for p in json.loads(sh("gh", "api", f"repos/{repo}/commits/{sha}/pulls"))
               if p.get("merged_at") and p.get("base", {}).get("ref") == "main"]
        if prs:
            break
    for pr in prs:
        full = json.loads(sh("gh", "api", f"repos/{repo}/pulls/{pr['number']}"))
        if full.get("merge_commit_sha") != sha:
            continue  # an open or other PR that merely contains the commit
        by = (full.get("merged_by") or {}).get("login", "")
        if by.lower() != approver.lower():
            print(f"::error::PR #{pr['number']} was merged by {by!r}, not the approver {approver!r} "
                  "(auto-merge and the merge queue are not accepted)")
            return 1
        files = json.loads(sh("gh", "api", "--paginate", f"repos/{repo}/pulls/{pr['number']}/files", "--jq", "[.[].filename]"))
        if path not in files:
            print(f"::error::PR #{pr['number']} does not touch {path}; its merge cannot validate it")
            return 1
        print(f"validated {path}: PR #{pr['number']} merged by {by} as {sha[:8]}")
        return 0
    print(f"::error::{sha[:8]} is not the merge commit of a merged PR into main (direct push, rebase merge, or squash "
          f"by someone else?); {path} is not posted")
    return 1


def probe():
    """Dry-run check that the poster's token can read the target (catches an org blocking classic PATs)."""
    who = sh("gh", "api", "user", "--jq", ".login", check=False)
    r = subprocess.run(["gh", "api", "repos/TauCetiProject/TauCetiRoadmap", "--jq", ".full_name"], capture_output=True, text=True)
    print(f"token probe: user={who or '?'}; TauCetiProject/TauCetiRoadmap read: {'ok' if r.returncode == 0 else 'FAILED ' + r.stderr.strip()[:200]}")
    return r.returncode


def key(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def already_on_remote(meta, k):
    """The real idempotency guard: look at the target repository itself."""
    repo = meta["repo"]
    if meta["kind"] == "pr":
        fork = meta.get("fork") or os.environ.get("POST_FORK", "")
        out = sh("gh", "pr", "list", "-R", repo, "--head", meta["branch"], "--state", "all", "--json", "url,headRepositoryOwner",
                 "--jq", f'[.[] | select(.headRepositoryOwner.login == "{fork.split("/")[0]}") | .url][0] // ""')
        return out or None
    endpoint = "issues/{}/comments" if meta["kind"] == "comment" else "pulls/{}/reviews"
    out = sh("gh", "api", "--paginate", f"repos/{repo}/" + endpoint.format(meta["number"]),
             "--jq", f'[.[] | select(.body | contains("roadmaplab-post:{k}")) | .html_url][0] // ""')
    return out or None


def render(path):
    meta, body, text = parse(path)
    errs = check(path)
    print(f"### {os.path.relpath(path, ROOT)}\n")
    print(f"- kind `{meta.get('kind')}` on `{meta.get('repo')}`" + (f" #{meta.get('number')}" if meta.get("number") else "")
          + (f", branch `{meta.get('branch')}` from `{meta.get('base', 'main')}`" if meta.get("kind") == "pr" else ""))
    print(f"- key `{key(text)}`; gluing check: {'**ok**' if not errs else '**BLOCKED**: ' + '; '.join(errs)}\n")
    if meta.get("title"):
        print(f"**Title:** {meta['title']}\n")
    print("<details><summary>Body, exactly as it will be posted</summary>\n\n````markdown\n" + body + "````\n</details>\n")
    if meta.get("patch") and os.path.isfile(os.path.join(ROOT, meta["patch"])):
        print("<details><summary>Patch</summary>\n\n````diff\n" + open(os.path.join(ROOT, meta["patch"]), encoding="utf-8").read() + "````\n</details>\n")


def send(path, dry):
    errs = check(path)
    if errs:
        raise SystemExit(f"{path}: blocked: " + "; ".join(errs))
    meta, body, text = parse(path)
    kind, repo = meta["kind"], meta["repo"]
    rel = os.path.relpath(path, ROOT)
    if rel in ledger():
        print(f"{rel}: already posted; skipping")
        return
    k = key(text)
    if kind != "pr":
        body = body + f"\n<!-- roadmaplab-post:{k} -->\n"
    tmp = tempfile.mkdtemp()
    bodyf = os.path.join(tmp, "body.md")
    open(bodyf, "w", encoding="utf-8").write(body)
    if not dry:
        prior = already_on_remote(meta, k)
        if prior:
            print(f"{rel}: already on the remote at {prior}; recording it, not re-sending")
            url = prior
            body = None
    if dry:
        print(f"DRY RUN {rel}: {kind} on {repo}" + (f"#{meta.get('number')}" if meta.get("number") else "")
              + f" ({len(body)} chars of body)")
        return
    if body is None:
        pass
    elif kind == "comment":
        url = json.loads(sh("gh", "api", f"repos/{repo}/issues/{meta['number']}/comments", "-F", f"body=@{bodyf}"))["html_url"]
    elif kind == "review":
        url = json.loads(sh("gh", "api", f"repos/{repo}/pulls/{meta['number']}/reviews",
                            "-f", f"event={meta.get('event', 'COMMENT')}", "-F", f"body=@{bodyf}"))["html_url"]
    else:
        fork = meta.get("fork") or os.environ.get("POST_FORK", "")
        if not fork:
            raise SystemExit("no fork: set front matter `fork` or repo variable POST_FORK")
        name, email = os.environ.get("POST_AUTHOR_NAME"), os.environ.get("POST_AUTHOR_EMAIL")
        if not (name and email):
            raise SystemExit("set repo variables POST_AUTHOR_NAME and POST_AUTHOR_EMAIL (the commit author)")
        base, branch, tok = meta.get("base", "main"), meta["branch"], os.environ["GH_TOKEN"]
        w = os.path.join(tmp, "w")
        sh("git", "clone", "--quiet", "--filter=blob:none", f"https://x-access-token:{tok}@github.com/{fork}.git", w)
        sh("git", "-C", w, "remote", "add", "upstream", f"https://github.com/{repo}.git")
        sh("git", "-C", w, "fetch", "--quiet", "upstream", base)
        sh("git", "-C", w, "checkout", "--quiet", "-b", branch, "FETCH_HEAD")
        sh("git", "-C", w, "apply", "--3way", os.path.join(ROOT, meta["patch"]))
        msg = meta["title"] + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n"
        sh("git", "-C", w, "-c", f"user.name={name}", "-c", f"user.email={email}", "commit", "--quiet", "-a", "-m", msg)
        sh("git", "-C", w, "push", "--quiet", "--force-with-lease", "origin", branch)
        create = ["gh", "pr", "create", "-R", repo, "--head", f"{fork.split('/')[0]}:{branch}", "--base", base,
                  "--title", meta["title"], "--body-file", bodyf] + (["--draft"] if meta.get("draft") == "true" else [])
        r = subprocess.run(create, capture_output=True, text=True)
        if r.returncode == 0:
            url = r.stdout.strip()
        else:  # e.g. 422 "already exists" after a lost response: find the existing PR instead of failing
            url = already_on_remote(meta, k)
            if not url:
                raise RuntimeError(f"gh pr create failed: {r.stderr.strip()[:500]}")
        if meta.get("label_comment"):
            sh("gh", "pr", "comment", url, "--body", meta["label_comment"])
    digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
    new = not os.path.isfile(LEDGER)
    with open(LEDGER, "a", encoding="utf-8") as o:
        if new:
            o.write("# path\tsha256\turl\tposted_utc\n")
        o.write(f"{rel}\t{digest}\t{url}\t{datetime.datetime.now(datetime.timezone.utc):%Y-%m-%dT%H:%MZ}\n")
    print(f"posted {rel}: {url}")


def main():
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == "check":
        bad = 0
        for f in args:
            errs = check(f)
            print(f"{f}: {'ok' if not errs else 'BLOCKED'}")
            for e in errs:
                print(f"  - {e}")
            bad |= bool(errs)
        sys.exit(1 if bad else 0)
    if cmd == "plan":
        plan(*args)
    elif cmd == "probe":
        sys.exit(probe())
    elif cmd == "render":
        for f in args:
            render(f)
    elif cmd == "verify-merge":
        sys.exit(verify_merge(*args))
    elif cmd == "send":
        send(args[0], "--dry-run" in args)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
