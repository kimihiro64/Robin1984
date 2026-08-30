import Lake

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Lake project configuration

This file pins the external Lean dependencies and defines the repository's
three libraries. The default `formalization` target reads the complete
topological module order from `scripts/build-order.txt`, builds one module job
at a time, and ends at `Solution`; this keeps the largest finite certificates
from elaborating concurrently. `Challenge` states the Palomar challenge, and
`Solution` supplies its proved instances from the public equivalence theorem.
-/

open Lake DSL

package Robin1984 where
  -- Bound Lean's internal task pool during certificate elaboration.
  weakLeanArgs := #["-j2"]

require PrimeNumberTheoremAnd from git
  "https://github.com/kimihiro64/PrimeNumberTheoremAnd.git" @
    "f8f58c749d6cde8a641348fcd5e4702993651cd6"

require leancert from git
  "https://github.com/alerad/leancert.git" @ "v4.33.1"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

private def buildModulesSequentially (moduleNames : Array Lean.Name) : FetchM (Job Unit) := do
  if moduleNames.size != 252 then
    error s!"Expected 252 modules in the default build order, found {moduleNames.size}."
  if moduleNames.back? != some `Solution then
    error "Solution must be the final module in the default build order."
  let mut seen : Lean.NameSet := {}
  let mut previous : Job Unit := Job.pure ()
  for moduleName in moduleNames do
    if seen.contains moduleName then
      error s!"Duplicate module in the default build order: {moduleName}"
    seen := seen.insert moduleName
    previous <- previous.bindM fun _ => do
      let some module <- findModule? moduleName
        | error s!"Module in the default build order was not found: {moduleName}"
      let moduleJob <- module.olean.fetch
      return moduleJob.map fun _ => ()
  return previous

@[default_target]
target formalization pkg : Unit := do
  let orderPath := pkg.dir / "scripts" / "build-order.txt"
  let contents <- IO.FS.readFile orderPath
  let moduleNames := contents.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else some line.toName
  buildModulesSequentially moduleNames.toArray

lean_lib Robin1984 where

lean_lib Challenge where
  roots := #[`Challenge]

lean_lib Solution where
  roots := #[`Solution]
