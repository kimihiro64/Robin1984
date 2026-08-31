import Robin1984.Analytic.PrimeProductBlocks
import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Reduced finite product checks

The first cutoff in a finite row can require products over a long prime
prefix. `RobinReducedProductChecks` isolates the remaining rational
inequalities after those three prefix products have been computed.

`RobinFiniteProductChecks.of_first_layer_products` reconstructs the ordinary
row product check from exact numerator, denominator, and base products.
`of_first_layer_blocks` obtains the same result by concatenating bounded
prime-product blocks, which is the form used by the largest finite row.
-/

namespace Robin1984

def RobinReducedProductChecks (r : RobinFiniteRow) (tail : List Nat) (u v w : Nat) : Prop :=
  And (1 <= r.gainUpper)
    (And ((2 : Rat)^(robinRatLogScale r.gainUpper) <= r.gainUpper)
    (And (1 <= r.heightMantissa)
    (And (((u * robinBoxProduct tail (fun x => x.1^(x.2 + 2) - 1) : Nat) : Rat) <=
      r.gainUpper * ((v * robinBoxProduct tail (fun x => x.1 * (x.1^(x.2 + 1) - 1)) : Nat) : Rat))
      ((2 : Rat)^r.heightExponent * r.heightMantissa <=
        ((w * robinBoxProduct tail Prod.fst : Nat) : Rat)))))

instance (r : RobinFiniteRow) (tail : List Nat) (u v w : Nat) :
    Decidable (RobinReducedProductChecks r tail u v w) :=
  inferInstanceAs (Decidable (And _ (And _ (And _ (And _ _)))))

theorem RobinFiniteProductChecks.of_first_layer_products
    {r : RobinFiniteRow} {c : Nat} {tail : List Nat} {u v w : Nat}
    (hCuts : r.cuts = c :: tail)
    (hNum : (Nat.primesLE c).prod (fun p => p^2 - 1) = u)
    (hDen : (Nat.primesLE c).prod (fun p => p * (p - 1)) = v)
    (hBase : (Nat.primesLE c).prod (fun p => p) = w)
    (h : RobinReducedProductChecks r tail u v w) :
    RobinFiniteProductChecks r := by
  unfold RobinFiniteProductChecks
  rw [hCuts]
  simp only [robinBoxProduct_cons c tail, Nat.reduceAdd, pow_one]
  rw [hNum, hDen, hBase]
  exact h

theorem RobinFiniteProductChecks.of_first_layer_blocks
    {r : RobinFiniteRow} {c : Nat} {tail : List Nat} {bs : List RobinPrimeProductBlock}
    (hCuts : r.cuts = c :: tail)
    (hCover : RobinPrimeBlocksCover 0 (c + 1) bs)
    (hBlocks : forall b, Membership.mem bs b -> RobinPrimeProductBlockChecks b)
    (h : RobinReducedProductChecks r tail
      (bs.map RobinPrimeProductBlock.numerator).prod
      (bs.map RobinPrimeProductBlock.denominator).prod
      (bs.map RobinPrimeProductBlock.baseProduct).prod) :
    RobinFiniteProductChecks r := by
  apply RobinFiniteProductChecks.of_first_layer_products hCuts
  . exact hCover.prime_prefix _ _ (fun b hb => (hBlocks b hb).numerator_eq)
  . exact hCover.prime_prefix _ _ (fun b hb => (hBlocks b hb).denominator_eq)
  . exact hCover.prime_prefix _ _ (fun b hb => (hBlocks b hb).baseProduct_eq)
  . exact h

end Robin1984
