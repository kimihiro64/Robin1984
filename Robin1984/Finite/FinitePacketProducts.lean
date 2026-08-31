import Robin1984.Finite.FiniteTangent
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Exact integer products for a finite prime-power packet

The numerator, denominator, and base products encode the logarithmic gain and
cost of every event in a finite packet. The main identities turn a sum of real
event weights into logarithms of these exact natural-number products, and
specialize the construction to the layer box determined by a cutoff list.
-/

namespace Robin1984

def robinPacketNumerator (S : Finset (Prod Nat Nat)) : Nat :=
  S.prod (fun v => v.1^(v.2 + 1) - 1)

def robinPacketDenominator (S : Finset (Prod Nat Nat)) : Nat :=
  S.prod (fun v => v.1 * (v.1^v.2 - 1))

def robinPacketBaseProduct (S : Finset (Prod Nat Nat)) : Nat :=
  S.prod Prod.fst

theorem robinRawEventWeight_eq_log_products {v : Prod Nat Nat}
    (hp : 2 <= v.1) (hj : 0 < v.2) (lambda : Real) :
    robinRawEventWeight lambda v =
      Real.log ((v.1^(v.2 + 1) - 1 : Nat) : Real) -
        Real.log ((v.1 * (v.1^v.2 - 1) : Nat) : Real) - lambda * Real.log v.1 := by
  have hpOne : 1 < v.1 := by omega
  have hPow : 1 < v.1^v.2 := Nat.one_lt_pow hj.ne' hpOne
  have hPowNext : 1 < v.1^(v.2 + 1) := Nat.one_lt_pow (Nat.succ_ne_zero _) hpOne
  have hpR : (0 : Real) < v.1 := by exact_mod_cast (by omega : 0 < v.1)
  have hPowR : (0 : Real) < (v.1 : Real)^v.2 - 1 := by
    have h : (1 : Real) < (v.1 : Real)^v.2 := by exact_mod_cast hPow
    linarith
  have hPowNextR : (0 : Real) < (v.1 : Real)^(v.2 + 1) - 1 := by
    have h : (1 : Real) < (v.1 : Real)^(v.2 + 1) := by exact_mod_cast hPowNext
    linarith
  have hRatio : 1 + ((v.1 : Real) - 1) / ((v.1 : Real) * ((v.1 : Real)^v.2 - 1)) =
      ((v.1 : Real)^(v.2 + 1) - 1) / ((v.1 : Real) * ((v.1 : Real)^v.2 - 1)) := by
    rw [pow_succ]
    field_simp
    ring
  unfold robinRawEventWeight Robin1984.FiniteSupport.simplifiedLayerGain
  rw [hRatio, Real.log_div hPowNextR.ne' (mul_pos hpR hPowR).ne']
  rw [Nat.cast_sub hPowNext.le, Nat.cast_mul, Nat.cast_sub hPow.le]
  push_cast
  rfl

theorem robinPacketProducts_pos {S : Finset (Prod Nat Nat)}
    (hShape : forall v, Membership.mem S v -> And (2 <= v.1) (0 < v.2)) :
    And (0 < robinPacketNumerator S)
      (And (0 < robinPacketDenominator S) (0 < robinPacketBaseProduct S)) := by
  have hNum : 0 < robinPacketNumerator S := by
    apply Finset.prod_pos
    intro v hv
    have h := hShape v hv
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero _) (by omega))
  have hDen : 0 < robinPacketDenominator S := by
    apply Finset.prod_pos
    intro v hv
    have h := hShape v hv
    exact Nat.mul_pos (by omega)
      (Nat.sub_pos_of_lt (Nat.one_lt_pow h.2.ne' (by omega)))
  have hBase : 0 < robinPacketBaseProduct S := by
    apply Finset.prod_pos
    intro v hv
    have h := hShape v hv
    omega
  exact And.intro hNum (And.intro hDen hBase)

theorem robinRawEventWeight_sum_eq_integer_products {S : Finset (Prod Nat Nat)}
    (hShape : forall v, Membership.mem S v -> And (2 <= v.1) (0 < v.2)) (lambda : Real) :
    S.sum (robinRawEventWeight lambda) =
      Real.log (robinPacketNumerator S : Real) -
        Real.log (robinPacketDenominator S : Real) -
          lambda * Real.log (robinPacketBaseProduct S : Real) := by
  have hNum : forall v, Membership.mem S v -> Not (((v.1^(v.2 + 1) - 1 : Nat) : Real) = 0) := by
    intro v hv
    have h := hShape v hv
    have hPos := Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero v.2) (by omega : 1 < v.1))
    exact_mod_cast hPos.ne'
  have hDen : forall v, Membership.mem S v -> Not (((v.1 * (v.1^v.2 - 1) : Nat) : Real) = 0) := by
    intro v hv
    have h := hShape v hv
    have hPos := Nat.mul_pos (by omega : 0 < v.1)
      (Nat.sub_pos_of_lt (Nat.one_lt_pow h.2.ne' (by omega : 1 < v.1)))
    exact_mod_cast hPos.ne'
  have hBase : forall v, Membership.mem S v -> Not ((v.1 : Real) = 0) := by
    intro v hv
    have h := hShape v hv
    exact_mod_cast (by omega : Not (v.1 = 0))
  unfold robinPacketNumerator robinPacketDenominator robinPacketBaseProduct
  rw [Finset.prod_natCast, Finset.prod_natCast, Finset.prod_natCast,
    Real.log_prod hNum, Real.log_prod hDen, Real.log_prod hBase,
    Finset.mul_sum, <- Finset.sum_sub_distrib, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  exact robinRawEventWeight_eq_log_products (hShape v hv).1 (hShape v hv).2 lambda

def robinBoxProduct (cuts : List Nat) (f : Prod Nat Nat -> Nat) : Nat :=
  (Finset.range cuts.length).prod (fun i =>
    (Nat.primesLE cuts[i]!).prod (fun p => f (p, i + 1)))

theorem robinLayerBox_prod (cuts : List Nat) (f : Prod Nat Nat -> Nat) :
    (robinLayerBox cuts).prod f = robinBoxProduct cuts f := by
  classical
  unfold robinLayerBox robinBoxProduct
  have hDisjoint : Set.PairwiseDisjoint (Finset.range cuts.length : Set Nat)
      (fun i => (Nat.primesLE cuts[i]!).image (fun p => (p, i + 1))) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hi hj
    choose p hp using Finset.mem_image.mp hi
    choose q hq using Finset.mem_image.mp hj
    have hiEq : i + 1 = v.2 := congrArg Prod.snd hp.2
    have hjEq : j + 1 = v.2 := congrArg Prod.snd hq.2
    exact hij (by omega)
  rw [Finset.prod_biUnion hDisjoint]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).1)]

theorem robinRawEventWeight_sum_eq_box_products (cuts : List Nat) (lambda : Real) :
    (robinLayerBox cuts).sum (robinRawEventWeight lambda) =
      Real.log (robinBoxProduct cuts (fun v => v.1^(v.2 + 1) - 1) : Real) -
        Real.log (robinBoxProduct cuts (fun v => v.1 * (v.1^v.2 - 1)) : Real) -
          lambda * Real.log (robinBoxProduct cuts Prod.fst : Real) := by
  have hShape : forall v, Membership.mem (robinLayerBox cuts) v -> And (2 <= v.1) (0 < v.2) := by
    intro v hv
    have h := robinLayerBox_mem.mp hv
    exact And.intro h.2.2.1.two_le h.1
  rw [robinRawEventWeight_sum_eq_integer_products hShape lambda]
  unfold robinPacketNumerator robinPacketDenominator robinPacketBaseProduct
  rw [robinLayerBox_prod, robinLayerBox_prod, robinLayerBox_prod]

end Robin1984
