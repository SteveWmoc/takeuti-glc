#!/usr/bin/env bash
set -euo pipefail

status=0

fail() {
  printf 'ERROR: %s\n' "$1" >&2
  status=1
}

echo '[lint] unfinished proof placeholders'
if grep -RInE --include='*.lean' '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' TakeutiGLC TakeutiGLC.lean; then
  fail 'Lean proof placeholders are not permitted.'
fi

echo '[lint] toolchain and mathlib alignment'
lean_tag=$(sed -n 's#^leanprover/lean4:\(v.*\)$#\1#p' lean-toolchain)
mathlib_tag=$(sed -n 's/.*@ "\(v[^"]*\)".*/\1/p' lakefile.lean | head -n 1)
manifest_mathlib_tag=$(
  grep -A 3 '"name": "mathlib"' lake-manifest.json |
    sed -n 's/.*"inputRev": "\([^"]*\)".*/\1/p' |
    head -n 1
)
if [[ -z "${lean_tag}" || -z "${mathlib_tag}" || -z "${manifest_mathlib_tag}" ]]; then
  fail 'Could not read the pinned Lean, mathlib, or manifest release tag.'
elif [[ "${lean_tag}" != "${mathlib_tag}" ]]; then
  fail "Lean toolchain ${lean_tag} does not match mathlib ${mathlib_tag}."
elif [[ "${manifest_mathlib_tag}" != "${mathlib_tag}" ]]; then
  fail "lake-manifest.json records mathlib ${manifest_mathlib_tag}, expected ${mathlib_tag}."
fi

echo '[lint] public module coverage'
while IFS= read -r file; do
  module="${file%.lean}"
  module="${module//\//.}"
  if ! grep -Fxq "import ${module}" TakeutiGLC.lean; then
    printf 'Missing from TakeutiGLC.lean: %s\n' "${module}" >&2
    status=1
  fi
done < <(find TakeutiGLC -type f -name '*.lean' | sort)

echo '[lint] trailing whitespace'
while IFS= read -r file; do
  if grep -nE '[[:blank:]]+$' "${file}"; then
    printf 'Trailing whitespace in %s\n' "${file}" >&2
    status=1
  fi
done < <(
  find TakeutiGLC docs .github scripts -type f \
    \( -name '*.lean' -o -name '*.md' -o -name '*.yml' -o -name '*.yaml' -o -name '*.sh' \) -print
  printf '%s\n' README.md ROADMAP.md CONTRIBUTING.md TakeutiGLC.lean lakefile.lean .editorconfig
)

echo '[lint] tabs in Lean source'
while IFS= read -r file; do
  if grep -n $'\t' "${file}"; then
    printf 'Tab character in %s\n' "${file}" >&2
    status=1
  fi
done < <(find TakeutiGLC -type f -name '*.lean' -print; printf '%s\n' TakeutiGLC.lean lakefile.lean)

if [[ "${status}" -eq 0 ]]; then
  echo '[lint] all project checks passed'
else
  echo '[lint] project checks failed' >&2
fi

exit "${status}"
