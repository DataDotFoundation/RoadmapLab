#!/usr/bin/env bash
# Cert 1: every ShortGRH Suggested.lean of a TauCetiRoadmap checkout elaborates at that checkout's
# pins, with no error and no warning other than `declaration uses sorry`.
# usage: cert1/cert1.sh TAUCETIROADMAP_CHECKOUT OUT_DIR
# Needs elan. Runs `lake exe cache get` (the Mathlib cache) in the checkout, then `lake env lean` on
# each file. Writes OUT_DIR/<roadmap>.log and OUT_DIR/summary.md; exits 1 if any file fails.
set -uo pipefail
repo=$(cd "$1" && pwd); out=$(mkdir -p "$2" && cd "$2" && pwd)
cd "$repo"
lake exe cache get > "$out/cache-get.log" 2>&1 || { echo "lake exe cache get failed"; tail -20 "$out/cache-get.log"; exit 1; }
commit=$(git rev-parse --short HEAD 2>/dev/null || echo unknown)
{
  echo "# Cert 1: ShortGRH Suggested.lean at TauCetiRoadmap \`$commit\`"
  echo
  echo "Toolchain \`$(cat lean-toolchain)\`. A file passes if \`lake env lean\` exits 0 and prints no error and no warning other than \`declaration uses sorry\`."
  echo
  echo "| roadmap | result | sorry | other diagnostics |"
  echo "|---|---|---|---|"
} > "$out/summary.md"
fail=0
for f in TauCetiRoadmap/ShortGRH/*/Suggested.lean; do
  rm_=$(basename "$(dirname "$f")")
  log="$out/$rm_.log"
  lake env lean "$f" > "$log" 2>&1; rc=$?
  sorry=$(grep -cE "declaration uses ['\`]sorry['\`]" "$log")
  other=$(grep -E '(error|warning):' "$log" | grep -vcE "declaration uses ['\`]sorry['\`]")
  if [ "$rc" -eq 0 ] && [ "$other" -eq 0 ]; then res=pass; else res=FAIL; fail=1; fi
  echo "| $rm_ | $res | $sorry | $other |" >> "$out/summary.md"
  # Strip the checkout path from logs so they can be published.
  sed -i "s#$repo/##g" "$log"
done
cat "$out/summary.md"
exit $fail
