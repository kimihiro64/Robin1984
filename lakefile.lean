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

This file pins the external Lean dependencies and declares the project and
vendored libraries. The default targets are `Challenge` and `Solution` and use
Lake's ordinary scheduler, so unrelated modules may build concurrently. The
memory-intensive certificate modules encode their required order through
import dependencies.
Each Lean process still uses one internal task thread. `Challenge` states the
Palomar challenge, and `Solution` supplies its proved instances from the public
equivalence theorem.
-/

open Lake DSL

package Robin1984 where
  -- Keep one Lean worker per process; imports serialize heavy certificates.
  weakLeanArgs := #["-j1"]

require PrimeNumberTheoremAnd from git
  "https://github.com/kimihiro64/PrimeNumberTheoremAnd.git" @
    "f8f58c749d6cde8a641348fcd5e4702993651cd6"

require leancert from git
  "https://github.com/alerad/leancert.git" @ "v4.33.1"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

lean_lib Robin1984 where

-- The vendored entry points import siblings throughout their namespaces.
lean_lib DedekindZeta where
  globs := #[.submodules `DedekindZeta]

lean_lib TauCeti where
  globs := #[.submodules `TauCeti]

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
