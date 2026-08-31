import Robin1984.Arithmetic.Definitions

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Public statement vocabulary

Short names for the standard divisor sum and Robin inequality.  These aliases
make the public theorem surface readable while keeping the detailed proof
development free to use its more explicit internal names.
-/

namespace Robin1984

/-- Robin's strict inequality at a single natural number. -/
noncomputable def robinInequality (n : Nat) : Prop :=
  (sigmaOneNat n : Real) <
    Real.exp Real.eulerMascheroniConstant * (n : Real) *
      Real.log (Real.log (n : Real))


end Robin1984
