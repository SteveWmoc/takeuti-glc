import Lake

open Lake DSL

package «takeuti-glc» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib TakeutiGLC

/-- Project-level QA checks used locally and by CI. -/
@[lint_driver]
script lint do
  let process ← IO.Process.spawn {
    cmd := "bash"
    args := #["scripts/lint.sh"]
  }
  process.wait
