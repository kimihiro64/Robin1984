import Robin1984.Lagarias.Certificates.Blocks05

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Lagarias (2001), finite verification through 5040.
- Formalization note: This selector composes the checked interval packets.
- PROVENANCE-END
-/

/-! # Complete finite verification for Lagarias' criterion -/

namespace Robin1984

/-- Lagarias' inequality for every integer from 2 through 5040. -/
theorem lagarias_finite_two_to_5040
    {n : Nat} (hLower : 2 <= n) (hUpper : n <= 5040) :
    ((ArithmeticFunction.sigma 1 n : Nat) : Real) <=
      (harmonic n : Real) +
        Real.exp (harmonic n : Real) * Real.log (harmonic n : Real) := by
  by_cases h00 : n < 3
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock00_valid
      lagariasFiniteBlock00_harmonicLower_le
    . simpa [lagariasFiniteBlock00] using hLower
    . simpa [lagariasFiniteBlock00] using h00
  by_cases h01 : n < 4
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock01_valid
      lagariasFiniteBlock01_harmonicLower_le
    . simpa [lagariasFiniteBlock01] using (Nat.le_of_not_gt h00)
    . simpa [lagariasFiniteBlock01] using h01
  by_cases h02 : n < 6
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock02_valid
      lagariasFiniteBlock02_harmonicLower_le
    . simpa [lagariasFiniteBlock02] using (Nat.le_of_not_gt h01)
    . simpa [lagariasFiniteBlock02] using h02
  by_cases h03 : n < 8
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock03_valid
      lagariasFiniteBlock03_harmonicLower_le
    . simpa [lagariasFiniteBlock03] using (Nat.le_of_not_gt h02)
    . simpa [lagariasFiniteBlock03] using h03
  by_cases h04 : n < 10
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock04_valid
      lagariasFiniteBlock04_harmonicLower_le
    . simpa [lagariasFiniteBlock04] using (Nat.le_of_not_gt h03)
    . simpa [lagariasFiniteBlock04] using h04
  by_cases h05 : n < 12
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock05_valid
      lagariasFiniteBlock05_harmonicLower_le
    . simpa [lagariasFiniteBlock05] using (Nat.le_of_not_gt h04)
    . simpa [lagariasFiniteBlock05] using h05
  by_cases h06 : n < 16
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock06_valid
      lagariasFiniteBlock06_harmonicLower_le
    . simpa [lagariasFiniteBlock06] using (Nat.le_of_not_gt h05)
    . simpa [lagariasFiniteBlock06] using h06
  by_cases h07 : n < 20
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock07_valid
      lagariasFiniteBlock07_harmonicLower_le
    . simpa [lagariasFiniteBlock07] using (Nat.le_of_not_gt h06)
    . simpa [lagariasFiniteBlock07] using h07
  by_cases h08 : n < 24
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock08_valid
      lagariasFiniteBlock08_harmonicLower_le
    . simpa [lagariasFiniteBlock08] using (Nat.le_of_not_gt h07)
    . simpa [lagariasFiniteBlock08] using h08
  by_cases h09 : n < 30
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock09_valid
      lagariasFiniteBlock09_harmonicLower_le
    . simpa [lagariasFiniteBlock09] using (Nat.le_of_not_gt h08)
    . simpa [lagariasFiniteBlock09] using h09
  by_cases h10 : n < 36
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock10_valid
      lagariasFiniteBlock10_harmonicLower_le
    . simpa [lagariasFiniteBlock10] using (Nat.le_of_not_gt h09)
    . simpa [lagariasFiniteBlock10] using h10
  by_cases h11 : n < 48
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock11_valid
      lagariasFiniteBlock11_harmonicLower_le
    . simpa [lagariasFiniteBlock11] using (Nat.le_of_not_gt h10)
    . simpa [lagariasFiniteBlock11] using h11
  by_cases h12 : n < 60
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock12_valid
      lagariasFiniteBlock12_harmonicLower_le
    . simpa [lagariasFiniteBlock12] using (Nat.le_of_not_gt h11)
    . simpa [lagariasFiniteBlock12] using h12
  by_cases h13 : n < 72
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock13_valid
      lagariasFiniteBlock13_harmonicLower_le
    . simpa [lagariasFiniteBlock13] using (Nat.le_of_not_gt h12)
    . simpa [lagariasFiniteBlock13] using h13
  by_cases h14 : n < 84
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock14_valid
      lagariasFiniteBlock14_harmonicLower_le
    . simpa [lagariasFiniteBlock14] using (Nat.le_of_not_gt h13)
    . simpa [lagariasFiniteBlock14] using h14
  by_cases h15 : n < 96
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock15_valid
      lagariasFiniteBlock15_harmonicLower_le
    . simpa [lagariasFiniteBlock15] using (Nat.le_of_not_gt h14)
    . simpa [lagariasFiniteBlock15] using h15
  by_cases h16 : n < 120
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock16_valid
      lagariasFiniteBlock16_harmonicLower_le
    . simpa [lagariasFiniteBlock16] using (Nat.le_of_not_gt h15)
    . simpa [lagariasFiniteBlock16] using h16
  by_cases h17 : n < 144
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock17_valid
      lagariasFiniteBlock17_harmonicLower_le
    . simpa [lagariasFiniteBlock17] using (Nat.le_of_not_gt h16)
    . simpa [lagariasFiniteBlock17] using h17
  by_cases h18 : n < 168
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock18_valid
      lagariasFiniteBlock18_harmonicLower_le
    . simpa [lagariasFiniteBlock18] using (Nat.le_of_not_gt h17)
    . simpa [lagariasFiniteBlock18] using h18
  by_cases h19 : n < 180
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock19_valid
      lagariasFiniteBlock19_harmonicLower_le
    . simpa [lagariasFiniteBlock19] using (Nat.le_of_not_gt h18)
    . simpa [lagariasFiniteBlock19] using h19
  by_cases h20 : n < 210
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock20_valid
      lagariasFiniteBlock20_harmonicLower_le
    . simpa [lagariasFiniteBlock20] using (Nat.le_of_not_gt h19)
    . simpa [lagariasFiniteBlock20] using h20
  by_cases h21 : n < 240
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock21_valid
      lagariasFiniteBlock21_harmonicLower_le
    . simpa [lagariasFiniteBlock21] using (Nat.le_of_not_gt h20)
    . simpa [lagariasFiniteBlock21] using h21
  by_cases h22 : n < 288
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock22_valid
      lagariasFiniteBlock22_harmonicLower_le
    . simpa [lagariasFiniteBlock22] using (Nat.le_of_not_gt h21)
    . simpa [lagariasFiniteBlock22] using h22
  by_cases h23 : n < 336
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock23_valid
      lagariasFiniteBlock23_harmonicLower_le
    . simpa [lagariasFiniteBlock23] using (Nat.le_of_not_gt h22)
    . simpa [lagariasFiniteBlock23] using h23
  by_cases h24 : n < 360
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock24_valid
      lagariasFiniteBlock24_harmonicLower_le
    . simpa [lagariasFiniteBlock24] using (Nat.le_of_not_gt h23)
    . simpa [lagariasFiniteBlock24] using h24
  by_cases h25 : n < 420
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock25_valid
      lagariasFiniteBlock25_harmonicLower_le
    . simpa [lagariasFiniteBlock25] using (Nat.le_of_not_gt h24)
    . simpa [lagariasFiniteBlock25] using h25
  by_cases h26 : n < 480
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock26_valid
      lagariasFiniteBlock26_harmonicLower_le
    . simpa [lagariasFiniteBlock26] using (Nat.le_of_not_gt h25)
    . simpa [lagariasFiniteBlock26] using h26
  by_cases h27 : n < 540
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock27_valid
      lagariasFiniteBlock27_harmonicLower_le
    . simpa [lagariasFiniteBlock27] using (Nat.le_of_not_gt h26)
    . simpa [lagariasFiniteBlock27] using h27
  by_cases h28 : n < 630
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock28_valid
      lagariasFiniteBlock28_harmonicLower_le
    . simpa [lagariasFiniteBlock28] using (Nat.le_of_not_gt h27)
    . simpa [lagariasFiniteBlock28] using h28
  by_cases h29 : n < 720
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock29_valid
      lagariasFiniteBlock29_harmonicLower_le
    . simpa [lagariasFiniteBlock29] using (Nat.le_of_not_gt h28)
    . simpa [lagariasFiniteBlock29] using h29
  by_cases h30 : n < 840
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock30_valid
      lagariasFiniteBlock30_harmonicLower_le
    . simpa [lagariasFiniteBlock30] using (Nat.le_of_not_gt h29)
    . simpa [lagariasFiniteBlock30] using h30
  by_cases h31 : n < 960
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock31_valid
      lagariasFiniteBlock31_harmonicLower_le
    . simpa [lagariasFiniteBlock31] using (Nat.le_of_not_gt h30)
    . simpa [lagariasFiniteBlock31] using h31
  by_cases h32 : n < 1080
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock32_valid
      lagariasFiniteBlock32_harmonicLower_le
    . simpa [lagariasFiniteBlock32] using (Nat.le_of_not_gt h31)
    . simpa [lagariasFiniteBlock32] using h32
  by_cases h33 : n < 1260
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock33_valid
      lagariasFiniteBlock33_harmonicLower_le
    . simpa [lagariasFiniteBlock33] using (Nat.le_of_not_gt h32)
    . simpa [lagariasFiniteBlock33] using h33
  by_cases h34 : n < 1440
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock34_valid
      lagariasFiniteBlock34_harmonicLower_le
    . simpa [lagariasFiniteBlock34] using (Nat.le_of_not_gt h33)
    . simpa [lagariasFiniteBlock34] using h34
  by_cases h35 : n < 1680
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock35_valid
      lagariasFiniteBlock35_harmonicLower_le
    . simpa [lagariasFiniteBlock35] using (Nat.le_of_not_gt h34)
    . simpa [lagariasFiniteBlock35] using h35
  by_cases h36 : n < 1980
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock36_valid
      lagariasFiniteBlock36_harmonicLower_le
    . simpa [lagariasFiniteBlock36] using (Nat.le_of_not_gt h35)
    . simpa [lagariasFiniteBlock36] using h36
  by_cases h37 : n < 2160
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock37_valid
      lagariasFiniteBlock37_harmonicLower_le
    . simpa [lagariasFiniteBlock37] using (Nat.le_of_not_gt h36)
    . simpa [lagariasFiniteBlock37] using h37
  by_cases h38 : n < 2520
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock38_valid
      lagariasFiniteBlock38_harmonicLower_le
    . simpa [lagariasFiniteBlock38] using (Nat.le_of_not_gt h37)
    . simpa [lagariasFiniteBlock38] using h38
  by_cases h39 : n < 2880
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock39_valid
      lagariasFiniteBlock39_harmonicLower_le
    . simpa [lagariasFiniteBlock39] using (Nat.le_of_not_gt h38)
    . simpa [lagariasFiniteBlock39] using h39
  by_cases h40 : n < 3360
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock40_valid
      lagariasFiniteBlock40_harmonicLower_le
    . simpa [lagariasFiniteBlock40] using (Nat.le_of_not_gt h39)
    . simpa [lagariasFiniteBlock40] using h40
  by_cases h41 : n < 3780
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock41_valid
      lagariasFiniteBlock41_harmonicLower_le
    . simpa [lagariasFiniteBlock41] using (Nat.le_of_not_gt h40)
    . simpa [lagariasFiniteBlock41] using h41
  by_cases h42 : n < 4200
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock42_valid
      lagariasFiniteBlock42_harmonicLower_le
    . simpa [lagariasFiniteBlock42] using (Nat.le_of_not_gt h41)
    . simpa [lagariasFiniteBlock42] using h42
  by_cases h43 : n < 4680
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock43_valid
      lagariasFiniteBlock43_harmonicLower_le
    . simpa [lagariasFiniteBlock43] using (Nat.le_of_not_gt h42)
    . simpa [lagariasFiniteBlock43] using h43
  by_cases h44 : n < 5040
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock44_valid
      lagariasFiniteBlock44_harmonicLower_le
    . simpa [lagariasFiniteBlock44] using (Nat.le_of_not_gt h43)
    . simpa [lagariasFiniteBlock44] using h44
  . apply LagariasFiniteBlock.sound lagariasFiniteBlock45_valid
      lagariasFiniteBlock45_harmonicLower_le
    . simpa [lagariasFiniteBlock45] using (Nat.le_of_not_gt h44)
    . simpa [lagariasFiniteBlock45] using (by omega : n < 5041)

end Robin1984
