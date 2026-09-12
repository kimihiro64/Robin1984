import Submission.Robin1984.Lagarias.FiniteCertificate

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Lagarias (2001) supplies the finite range.
- Formalization note: Generated exact factor and rational certificate data.
- PROVENANCE-END
-/

/-! # Lagarias finite certificate packet 00 -/

namespace Robin1984

def lagariasFiniteBlock00 : LagariasFiniteBlock where
  first := 2
  sigmaBound := 3
  harmonicLower := (3 / 2)
  expTerms := 32
  outerLogTerms := 32
  count := 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock00_harmonicLower_le :
    (lagariasFiniteBlock00.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock00.first : Real) := by
  norm_num [lagariasFiniteBlock00, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock00_analyticValid : lagariasFiniteBlock00.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock00
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock00_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock00.first lagariasFiniteBlock00.sigmaBound
        lagariasFiniteBlock00.count = true := by
  unfold lagariasFiniteBlock00
  decide +kernel

theorem lagariasFiniteBlock00_valid : lagariasFiniteBlock00.Valid :=
  And.intro lagariasFiniteBlock00_analyticValid lagariasFiniteBlock00_rangeValid

def lagariasFiniteBlock01 : LagariasFiniteBlock where
  first := 3
  sigmaBound := 4
  harmonicLower := (11 / 6)
  expTerms := 32
  outerLogTerms := 32
  count := 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock01_harmonicLower_le :
    (lagariasFiniteBlock01.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock01.first : Real) := by
  norm_num [lagariasFiniteBlock01, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock01_analyticValid : lagariasFiniteBlock01.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock01
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock01_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock01.first lagariasFiniteBlock01.sigmaBound
        lagariasFiniteBlock01.count = true := by
  unfold lagariasFiniteBlock01
  decide +kernel

theorem lagariasFiniteBlock01_valid : lagariasFiniteBlock01.Valid :=
  And.intro lagariasFiniteBlock01_analyticValid lagariasFiniteBlock01_rangeValid

def lagariasFiniteBlock02 : LagariasFiniteBlock where
  first := 4
  sigmaBound := 7
  harmonicLower := (25 / 12)
  expTerms := 32
  outerLogTerms := 32
  count := 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock02_harmonicLower_le :
    (lagariasFiniteBlock02.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock02.first : Real) := by
  norm_num [lagariasFiniteBlock02, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock02_analyticValid : lagariasFiniteBlock02.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock02
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock02_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock02.first lagariasFiniteBlock02.sigmaBound
        lagariasFiniteBlock02.count = true := by
  unfold lagariasFiniteBlock02
  decide +kernel

theorem lagariasFiniteBlock02_valid : lagariasFiniteBlock02.Valid :=
  And.intro lagariasFiniteBlock02_analyticValid lagariasFiniteBlock02_rangeValid

def lagariasFiniteBlock03 : LagariasFiniteBlock where
  first := 6
  sigmaBound := 12
  harmonicLower := (49 / 20)
  expTerms := 32
  outerLogTerms := 32
  count := 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock03_harmonicLower_le :
    (lagariasFiniteBlock03.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock03.first : Real) := by
  norm_num [lagariasFiniteBlock03, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock03_analyticValid : lagariasFiniteBlock03.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock03
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock03_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock03.first lagariasFiniteBlock03.sigmaBound
        lagariasFiniteBlock03.count = true := by
  unfold lagariasFiniteBlock03
  decide +kernel

theorem lagariasFiniteBlock03_valid : lagariasFiniteBlock03.Valid :=
  And.intro lagariasFiniteBlock03_analyticValid lagariasFiniteBlock03_rangeValid

def lagariasFiniteBlock04 : LagariasFiniteBlock where
  first := 8
  sigmaBound := 15
  harmonicLower := (761 / 280)
  expTerms := 32
  outerLogTerms := 32
  count := 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock04_harmonicLower_le :
    (lagariasFiniteBlock04.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock04.first : Real) := by
  norm_num [lagariasFiniteBlock04, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock04_analyticValid : lagariasFiniteBlock04.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock04
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock04_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock04.first lagariasFiniteBlock04.sigmaBound
        lagariasFiniteBlock04.count = true := by
  unfold lagariasFiniteBlock04
  decide +kernel

theorem lagariasFiniteBlock04_valid : lagariasFiniteBlock04.Valid :=
  And.intro lagariasFiniteBlock04_analyticValid lagariasFiniteBlock04_rangeValid

def lagariasFiniteBlock05 : LagariasFiniteBlock where
  first := 10
  sigmaBound := 18
  harmonicLower := (7381 / 2520)
  expTerms := 32
  outerLogTerms := 32
  count := 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock05_harmonicLower_le :
    (lagariasFiniteBlock05.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock05.first : Real) := by
  norm_num [lagariasFiniteBlock05, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock05_analyticValid : lagariasFiniteBlock05.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock05
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock05_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock05.first lagariasFiniteBlock05.sigmaBound
        lagariasFiniteBlock05.count = true := by
  unfold lagariasFiniteBlock05
  decide +kernel

theorem lagariasFiniteBlock05_valid : lagariasFiniteBlock05.Valid :=
  And.intro lagariasFiniteBlock05_analyticValid lagariasFiniteBlock05_rangeValid

def lagariasFiniteBlock06 : LagariasFiniteBlock where
  first := 12
  sigmaBound := 28
  harmonicLower := (86021 / 27720)
  expTerms := 32
  outerLogTerms := 32
  count := 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock06_harmonicLower_le :
    (lagariasFiniteBlock06.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock06.first : Real) := by
  norm_num [lagariasFiniteBlock06, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock06_analyticValid : lagariasFiniteBlock06.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock06
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock06_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock06.first lagariasFiniteBlock06.sigmaBound
        lagariasFiniteBlock06.count = true := by
  unfold lagariasFiniteBlock06
  decide +kernel

theorem lagariasFiniteBlock06_valid : lagariasFiniteBlock06.Valid :=
  And.intro lagariasFiniteBlock06_analyticValid lagariasFiniteBlock06_rangeValid

def lagariasFiniteBlock07 : LagariasFiniteBlock where
  first := 16
  sigmaBound := 39
  harmonicLower := (2436559 / 720720)
  expTerms := 32
  outerLogTerms := 32
  count := 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock07_harmonicLower_le :
    (lagariasFiniteBlock07.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock07.first : Real) := by
  norm_num [lagariasFiniteBlock07, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock07_analyticValid : lagariasFiniteBlock07.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock07
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock07_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock07.first lagariasFiniteBlock07.sigmaBound
        lagariasFiniteBlock07.count = true := by
  unfold lagariasFiniteBlock07
  decide +kernel

theorem lagariasFiniteBlock07_valid : lagariasFiniteBlock07.Valid :=
  And.intro lagariasFiniteBlock07_analyticValid lagariasFiniteBlock07_rangeValid

def lagariasFiniteBlock08 : LagariasFiniteBlock where
  first := 20
  sigmaBound := 42
  harmonicLower := (55835135 / 15519504)
  expTerms := 32
  outerLogTerms := 32
  count := 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock08_harmonicLower_le :
    (lagariasFiniteBlock08.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock08.first : Real) := by
  norm_num [lagariasFiniteBlock08, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock08_analyticValid : lagariasFiniteBlock08.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock08
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock08_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock08.first lagariasFiniteBlock08.sigmaBound
        lagariasFiniteBlock08.count = true := by
  unfold lagariasFiniteBlock08
  decide +kernel

theorem lagariasFiniteBlock08_valid : lagariasFiniteBlock08.Valid :=
  And.intro lagariasFiniteBlock08_analyticValid lagariasFiniteBlock08_rangeValid

def lagariasFiniteBlock09 : LagariasFiniteBlock where
  first := 24
  sigmaBound := 60
  harmonicLower := (1347822955 / 356948592)
  expTerms := 32
  outerLogTerms := 32
  count := 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock09_harmonicLower_le :
    (lagariasFiniteBlock09.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock09.first : Real) := by
  norm_num [lagariasFiniteBlock09, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock09_analyticValid : lagariasFiniteBlock09.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock09
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock09_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock09.first lagariasFiniteBlock09.sigmaBound
        lagariasFiniteBlock09.count = true := by
  unfold lagariasFiniteBlock09
  decide +kernel

theorem lagariasFiniteBlock09_valid : lagariasFiniteBlock09.Valid :=
  And.intro lagariasFiniteBlock09_analyticValid lagariasFiniteBlock09_rangeValid

def lagariasFiniteBlock10 : LagariasFiniteBlock where
  first := 30
  sigmaBound := 72
  harmonicLower := (9304682830147 / 2329089562800)
  expTerms := 32
  outerLogTerms := 32
  count := 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock10_harmonicLower_le :
    (lagariasFiniteBlock10.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock10.first : Real) := by
  norm_num [lagariasFiniteBlock10, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock10_analyticValid : lagariasFiniteBlock10.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock10
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock10_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock10.first lagariasFiniteBlock10.sigmaBound
        lagariasFiniteBlock10.count = true := by
  unfold lagariasFiniteBlock10
  decide +kernel

theorem lagariasFiniteBlock10_valid : lagariasFiniteBlock10.Valid :=
  And.intro lagariasFiniteBlock10_analyticValid lagariasFiniteBlock10_rangeValid

def lagariasFiniteBlock11 : LagariasFiniteBlock where
  first := 36
  sigmaBound := 96
  harmonicLower := (54801925434709 / 13127595717600)
  expTerms := 32
  outerLogTerms := 32
  count := 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock11_harmonicLower_le :
    (lagariasFiniteBlock11.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock11.first : Real) := by
  norm_num [lagariasFiniteBlock11, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock11_analyticValid : lagariasFiniteBlock11.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock11
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock11_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock11.first lagariasFiniteBlock11.sigmaBound
        lagariasFiniteBlock11.count = true := by
  unfold lagariasFiniteBlock11
  decide +kernel

theorem lagariasFiniteBlock11_valid : lagariasFiniteBlock11.Valid :=
  And.intro lagariasFiniteBlock11_analyticValid lagariasFiniteBlock11_rangeValid

def lagariasFiniteBlock12 : LagariasFiniteBlock where
  first := 48
  sigmaBound := 124
  harmonicLower := (282000222059796592919 / 63245806209101973600)
  expTerms := 32
  outerLogTerms := 32
  count := 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock12_harmonicLower_le :
    (lagariasFiniteBlock12.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock12.first : Real) := by
  norm_num [lagariasFiniteBlock12, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock12_analyticValid : lagariasFiniteBlock12.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock12
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock12_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock12.first lagariasFiniteBlock12.sigmaBound
        lagariasFiniteBlock12.count = true := by
  unfold lagariasFiniteBlock12
  decide +kernel

theorem lagariasFiniteBlock12_valid : lagariasFiniteBlock12.Valid :=
  And.intro lagariasFiniteBlock12_analyticValid lagariasFiniteBlock12_rangeValid

def lagariasFiniteBlock13 : LagariasFiniteBlock where
  first := 60
  sigmaBound := 168
  harmonicLower := (15117092380124150817026911 / 3230237388259077233637600)
  expTerms := 32
  outerLogTerms := 32
  count := 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock13_harmonicLower_le :
    (lagariasFiniteBlock13.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock13.first : Real) := by
  norm_num [lagariasFiniteBlock13, harmonic, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock13_analyticValid : lagariasFiniteBlock13.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock13
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock13_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock13.first lagariasFiniteBlock13.sigmaBound
        lagariasFiniteBlock13.count = true := by
  unfold lagariasFiniteBlock13
  decide +kernel

theorem lagariasFiniteBlock13_valid : lagariasFiniteBlock13.Valid :=
  And.intro lagariasFiniteBlock13_analyticValid lagariasFiniteBlock13_rangeValid

def lagariasFiniteBlock14 : LagariasFiniteBlock where
  first := 72
  sigmaBound := 195
  harmonicLower := (34792638131407194868409385908660284203942776416021772518626123969217743250507810558412988580637507052206346901417321103 / 7168011147853547071093076961253790699136930345194703489602257168628601718816890405290799093268033444500000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock14_harmonicLower_le :
    (lagariasFiniteBlock14.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock14.first : Real) := by
  change (((34792638131407194868409385908660284203942776416021772518626123969217743250507810558412988580637507052206346901417321103 / 7168011147853547071093076961253790699136930345194703489602257168628601718816890405290799093268033444500000000000000000) : Rat) : Real) <=     (harmonic 72 : Real)
  have hLog :
      (6 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((9 / 8) : Rat)           32 : Real) <=
        Real.log (72 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (72 : Real))
      (q := ((9 / 8) : Rat))
      (r := ((9 / 8) : Rat))
      6 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((34792638131407194868409385908660284203942776416021772518626123969217743250507810558412988580637507052206346901417321103 / 7168011147853547071093076961253790699136930345194703489602257168628601718816890405290799093268033444500000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((6 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((9 / 8) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock14_analyticValid : lagariasFiniteBlock14.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock14
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock14_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock14.first lagariasFiniteBlock14.sigmaBound
        lagariasFiniteBlock14.count = true := by
  unfold lagariasFiniteBlock14
  decide +kernel

theorem lagariasFiniteBlock14_valid : lagariasFiniteBlock14.Valid :=
  And.intro lagariasFiniteBlock14_analyticValid lagariasFiniteBlock14_rangeValid

def lagariasFiniteBlock15 : LagariasFiniteBlock where
  first := 84
  sigmaBound := 234
  harmonicLower := (31314038628315502208206148760739993306028159804405323405661072285221664567927737433306623245649395631260015240723155999804304562918959629063 / 6252769780614591738115410128300511371360497923363897749095680726251861402361571710667741530667534925396280523349434218184500000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock15_harmonicLower_le :
    (lagariasFiniteBlock15.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock15.first : Real) := by
  change (((31314038628315502208206148760739993306028159804405323405661072285221664567927737433306623245649395631260015240723155999804304562918959629063 / 6252769780614591738115410128300511371360497923363897749095680726251861402361571710667741530667534925396280523349434218184500000000000000000) : Rat) : Real) <=     (harmonic 84 : Real)
  have hLog :
      (6 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((21 / 16) : Rat)           32 : Real) <=
        Real.log (84 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (84 : Real))
      (q := ((21 / 16) : Rat))
      (r := ((21 / 16) : Rat))
      6 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((31314038628315502208206148760739993306028159804405323405661072285221664567927737433306623245649395631260015240723155999804304562918959629063 / 6252769780614591738115410128300511371360497923363897749095680726251861402361571710667741530667534925396280523349434218184500000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((6 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((21 / 16) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock15_analyticValid : lagariasFiniteBlock15.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock15
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock15_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock15.first lagariasFiniteBlock15.sigmaBound
        lagariasFiniteBlock15.count = true := by
  unfold lagariasFiniteBlock15
  decide +kernel

theorem lagariasFiniteBlock15_valid : lagariasFiniteBlock15.Valid :=
  And.intro lagariasFiniteBlock15_analyticValid lagariasFiniteBlock15_rangeValid

def lagariasFiniteBlock16 : LagariasFiniteBlock where
  first := 96
  sigmaBound := 280
  harmonicLower := (2841560429043158971489767567180329513999392342117410855151028872795541977 / 552665227782229364165957008481200318783521652221679687500000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock16_harmonicLower_le :
    (lagariasFiniteBlock16.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock16.first : Real) := by
  change (((2841560429043158971489767567180329513999392342117410855151028872795541977 / 552665227782229364165957008481200318783521652221679687500000000000000000) : Rat) : Real) <=     (harmonic 96 : Real)
  have hLog :
      (6 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((3 / 2) : Rat)           32 : Real) <=
        Real.log (96 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (96 : Real))
      (q := ((3 / 2) : Rat))
      (r := ((3 / 2) : Rat))
      6 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((2841560429043158971489767567180329513999392342117410855151028872795541977 / 552665227782229364165957008481200318783521652221679687500000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((6 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((3 / 2) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock16_analyticValid : lagariasFiniteBlock16.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock16
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock16_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock16.first lagariasFiniteBlock16.sigmaBound
        lagariasFiniteBlock16.count = true := by
  unfold lagariasFiniteBlock16
  decide +kernel

theorem lagariasFiniteBlock16_valid : lagariasFiniteBlock16.Valid :=
  And.intro lagariasFiniteBlock16_analyticValid lagariasFiniteBlock16_rangeValid

def lagariasFiniteBlock17 : LagariasFiniteBlock where
  first := 120
  sigmaBound := 360
  harmonicLower := (108153575491361642524820593965140159132940332285400640504221948641140236239052467774396664898756832639142544116058647712456367 / 20160221514062211232818033752821800024686566710570456122136630688802656097374701154651736613815620752419860500000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock17_harmonicLower_le :
    (lagariasFiniteBlock17.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock17.first : Real) := by
  change (((108153575491361642524820593965140159132940332285400640504221948641140236239052467774396664898756832639142544116058647712456367 / 20160221514062211232818033752821800024686566710570456122136630688802656097374701154651736613815620752419860500000000000000000) : Rat) : Real) <=     (harmonic 120 : Real)
  have hLog :
      (6 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((15 / 8) : Rat)           32 : Real) <=
        Real.log (120 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (120 : Real))
      (q := ((15 / 8) : Rat))
      (r := ((15 / 8) : Rat))
      6 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((108153575491361642524820593965140159132940332285400640504221948641140236239052467774396664898756832639142544116058647712456367 / 20160221514062211232818033752821800024686566710570456122136630688802656097374701154651736613815620752419860500000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((6 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((15 / 8) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock17_analyticValid : lagariasFiniteBlock17.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock17
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock17_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock17.first lagariasFiniteBlock17.sigmaBound
        lagariasFiniteBlock17.count = true := by
  unfold lagariasFiniteBlock17
  decide +kernel

theorem lagariasFiniteBlock17_valid : lagariasFiniteBlock17.Valid :=
  And.intro lagariasFiniteBlock17_analyticValid lagariasFiniteBlock17_rangeValid

def lagariasFiniteBlock18 : LagariasFiniteBlock where
  first := 144
  sigmaBound := 403
  harmonicLower := (79522249697528276581670221646691152876379605958198924577663225515872314353268197149780435728984986303088194436640415907 / 14336022295707094142186153922507581398273860690389406979204514337257203437633780810581598186536066889000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock18_harmonicLower_le :
    (lagariasFiniteBlock18.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock18.first : Real) := by
  change (((79522249697528276581670221646691152876379605958198924577663225515872314353268197149780435728984986303088194436640415907 / 14336022295707094142186153922507581398273860690389406979204514337257203437633780810581598186536066889000000000000000000) : Rat) : Real) <=     (harmonic 144 : Real)
  have hLog :
      (7 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((9 / 8) : Rat)           32 : Real) <=
        Real.log (144 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (144 : Real))
      (q := ((9 / 8) : Rat))
      (r := ((9 / 8) : Rat))
      7 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((79522249697528276581670221646691152876379605958198924577663225515872314353268197149780435728984986303088194436640415907 / 14336022295707094142186153922507581398273860690389406979204514337257203437633780810581598186536066889000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((7 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((9 / 8) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock18_analyticValid : lagariasFiniteBlock18.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock18
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock18_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock18.first lagariasFiniteBlock18.sigmaBound
        lagariasFiniteBlock18.count = true := by
  unfold lagariasFiniteBlock18
  decide +kernel

theorem lagariasFiniteBlock18_valid : lagariasFiniteBlock18.Valid :=
  And.intro lagariasFiniteBlock18_analyticValid lagariasFiniteBlock18_rangeValid

def lagariasFiniteBlock19 : LagariasFiniteBlock where
  first := 168
  sigmaBound := 480
  harmonicLower := (71296256744877868490488487172845622715195162376150666008693893950730559367103898299388535611711976220143446576082105455663952231810905801147 / 12505539561229183476230820256601022742720995846727795498191361452503722804723143421335483061335069850792561046698868436369000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock19_harmonicLower_le :
    (lagariasFiniteBlock19.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock19.first : Real) := by
  change (((71296256744877868490488487172845622715195162376150666008693893950730559367103898299388535611711976220143446576082105455663952231810905801147 / 12505539561229183476230820256601022742720995846727795498191361452503722804723143421335483061335069850792561046698868436369000000000000000000) : Rat) : Real) <=     (harmonic 168 : Real)
  have hLog :
      (7 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((21 / 16) : Rat)           32 : Real) <=
        Real.log (168 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (168 : Real))
      (q := ((21 / 16) : Rat))
      (r := ((21 / 16) : Rat))
      7 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((71296256744877868490488487172845622715195162376150666008693893950730559367103898299388535611711976220143446576082105455663952231810905801147 / 12505539561229183476230820256601022742720995846727795498191361452503722804723143421335483061335069850792561046698868436369000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((7 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((21 / 16) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock19_analyticValid : lagariasFiniteBlock19.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock19
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock19_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock19.first lagariasFiniteBlock19.sigmaBound
        lagariasFiniteBlock19.count = true := by
  unfold lagariasFiniteBlock19
  decide +kernel

theorem lagariasFiniteBlock19_valid : lagariasFiniteBlock19.Valid :=
  And.intro lagariasFiniteBlock19_analyticValid lagariasFiniteBlock19_rangeValid

def lagariasFiniteBlock20 : LagariasFiniteBlock where
  first := 180
  sigmaBound := 546
  harmonicLower := (300791474143888829322401212148490485149625945229362922040071781034228702261442221703016714582886957757323283391232127189869023255275405772476044923914808074679 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock20_harmonicLower_le :
    (lagariasFiniteBlock20.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock20.first : Real) := by
  change (((300791474143888829322401212148490485149625945229362922040071781034228702261442221703016714582886957757323283391232127189869023255275405772476044923914808074679 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000) : Rat) : Real) <=     (harmonic 180 : Real)
  have hLog :
      (7 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((45 / 32) : Rat)           32 : Real) <=
        Real.log (180 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (180 : Real))
      (q := ((45 / 32) : Rat))
      (r := ((45 / 32) : Rat))
      7 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((300791474143888829322401212148490485149625945229362922040071781034228702261442221703016714582886957757323283391232127189869023255275405772476044923914808074679 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((7 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((45 / 32) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock20_analyticValid : lagariasFiniteBlock20.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock20
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock20_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock20.first lagariasFiniteBlock20.sigmaBound
        lagariasFiniteBlock20.count = true := by
  unfold lagariasFiniteBlock20
  decide +kernel

theorem lagariasFiniteBlock20_valid : lagariasFiniteBlock20.Valid :=
  And.intro lagariasFiniteBlock20_analyticValid lagariasFiniteBlock20_rangeValid

def lagariasFiniteBlock21 : LagariasFiniteBlock where
  first := 210
  sigmaBound := 600
  harmonicLower := (1867966363647556887909543929835404376710992067875780321433971766557252081136902946530345820056993249897098049818137707584612780113946297070394508192621238827132253615347721293122399 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock21_harmonicLower_le :
    (lagariasFiniteBlock21.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock21.first : Real) := by
  change (((1867966363647556887909543929835404376710992067875780321433971766557252081136902946530345820056993249897098049818137707584612780113946297070394508192621238827132253615347721293122399 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000) : Rat) : Real) <=     (harmonic 210 : Real)
  have hLog :
      (7 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((105 / 64) : Rat)           32 : Real) <=
        Real.log (210 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (210 : Real))
      (q := ((105 / 64) : Rat))
      (r := ((105 / 64) : Rat))
      7 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((1867966363647556887909543929835404376710992067875780321433971766557252081136902946530345820056993249897098049818137707584612780113946297070394508192621238827132253615347721293122399 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((7 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((105 / 64) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock21_analyticValid : lagariasFiniteBlock21.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock21
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock21_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock21.first lagariasFiniteBlock21.sigmaBound
        lagariasFiniteBlock21.count = true := by
  unfold lagariasFiniteBlock21
  decide +kernel

theorem lagariasFiniteBlock21_valid : lagariasFiniteBlock21.Valid :=
  And.intro lagariasFiniteBlock21_analyticValid lagariasFiniteBlock21_rangeValid

def lagariasFiniteBlock22 : LagariasFiniteBlock where
  first := 240
  sigmaBound := 744
  harmonicLower := (244255152386595632101225500456073943426143977642947511162988354794731984601436066783102942283100005298482900057735177995731523 / 40320443028124422465636067505643600049373133421140912244273261377605312194749402309303473227631241504839721000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock22_harmonicLower_le :
    (lagariasFiniteBlock22.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock22.first : Real) := by
  change (((244255152386595632101225500456073943426143977642947511162988354794731984601436066783102942283100005298482900057735177995731523 / 40320443028124422465636067505643600049373133421140912244273261377605312194749402309303473227631241504839721000000000000000000) : Rat) : Real) <=     (harmonic 240 : Real)
  have hLog :
      (7 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((15 / 8) : Rat)           32 : Real) <=
        Real.log (240 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (240 : Real))
      (q := ((15 / 8) : Rat))
      (r := ((15 / 8) : Rat))
      7 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((244255152386595632101225500456073943426143977642947511162988354794731984601436066783102942283100005298482900057735177995731523 / 40320443028124422465636067505643600049373133421140912244273261377605312194749402309303473227631241504839721000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((7 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((15 / 8) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock22_analyticValid : lagariasFiniteBlock22.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock22
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock22_rangeChunk00 :
    lagariasSigmaRangeValidBool
      240 744 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock22_rangeChunk01 :
    lagariasSigmaRangeValidBool
      270 744 18 = true := by
  decide +kernel

theorem lagariasFiniteBlock22_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock22.first lagariasFiniteBlock22.sigmaBound
        lagariasFiniteBlock22.count = true := by
  unfold lagariasFiniteBlock22
  have hRange00 :
      lagariasSigmaRangeValidBool
        240 744 48 = true :=
    lagariasSigmaRangeValidBool_add
      240 744 30 18
      lagariasFiniteBlock22_rangeChunk00 lagariasFiniteBlock22_rangeChunk01
  exact hRange00

theorem lagariasFiniteBlock22_valid : lagariasFiniteBlock22.Valid :=
  And.intro lagariasFiniteBlock22_analyticValid lagariasFiniteBlock22_rangeValid

def lagariasFiniteBlock23 : LagariasFiniteBlock where
  first := 288
  sigmaBound := 868
  harmonicLower := (11182402891530270428315208934507717168109207385544288014759275386663642775690096647841861787086869812720461883805773701 / 1792002786963386767773269240313447674784232586298675872400564292157150429704222601322699773317008361125000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock23_harmonicLower_le :
    (lagariasFiniteBlock23.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock23.first : Real) := by
  change (((11182402891530270428315208934507717168109207385544288014759275386663642775690096647841861787086869812720461883805773701 / 1792002786963386767773269240313447674784232586298675872400564292157150429704222601322699773317008361125000000000000000) : Rat) : Real) <=     (harmonic 288 : Real)
  have hLog :
      (8 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((9 / 8) : Rat)           32 : Real) <=
        Real.log (288 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (288 : Real))
      (q := ((9 / 8) : Rat))
      (r := ((9 / 8) : Rat))
      8 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((11182402891530270428315208934507717168109207385544288014759275386663642775690096647841861787086869812720461883805773701 / 1792002786963386767773269240313447674784232586298675872400564292157150429704222601322699773317008361125000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((8 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((9 / 8) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock23_analyticValid : lagariasFiniteBlock23.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock23
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock23_rangeChunk00 :
    lagariasSigmaRangeValidBool
      288 868 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock23_rangeChunk01 :
    lagariasSigmaRangeValidBool
      318 868 18 = true := by
  decide +kernel

theorem lagariasFiniteBlock23_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock23.first lagariasFiniteBlock23.sigmaBound
        lagariasFiniteBlock23.count = true := by
  unfold lagariasFiniteBlock23
  have hRange00 :
      lagariasSigmaRangeValidBool
        288 868 48 = true :=
    lagariasSigmaRangeValidBool_add
      288 868 30 18
      lagariasFiniteBlock23_rangeChunk00 lagariasFiniteBlock23_rangeChunk01
  exact hRange00

theorem lagariasFiniteBlock23_valid : lagariasFiniteBlock23.Valid :=
  And.intro lagariasFiniteBlock23_analyticValid lagariasFiniteBlock23_rangeValid

def lagariasFiniteBlock24 : LagariasFiniteBlock where
  first := 336
  sigmaBound := 992
  harmonicLower := (9995554529140591570570584603026407352291750642936335650758205416377223699794040216520478091515645147220857833839737363964911917222986543021 / 1563192445153647934528852532075127842840124480840974437273920181562965350590392927666935382666883731349070130837358554546125000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock24_harmonicLower_le :
    (lagariasFiniteBlock24.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock24.first : Real) := by
  change (((9995554529140591570570584603026407352291750642936335650758205416377223699794040216520478091515645147220857833839737363964911917222986543021 / 1563192445153647934528852532075127842840124480840974437273920181562965350590392927666935382666883731349070130837358554546125000000000000000) : Rat) : Real) <=     (harmonic 336 : Real)
  have hLog :
      (8 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((21 / 16) : Rat)           32 : Real) <=
        Real.log (336 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (336 : Real))
      (q := ((21 / 16) : Rat))
      (r := ((21 / 16) : Rat))
      8 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((9995554529140591570570584603026407352291750642936335650758205416377223699794040216520478091515645147220857833839737363964911917222986543021 / 1563192445153647934528852532075127842840124480840974437273920181562965350590392927666935382666883731349070130837358554546125000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((8 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((21 / 16) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock24_analyticValid : lagariasFiniteBlock24.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock24
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock24_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock24.first lagariasFiniteBlock24.sigmaBound
        lagariasFiniteBlock24.count = true := by
  unfold lagariasFiniteBlock24
  decide +kernel

theorem lagariasFiniteBlock24_valid : lagariasFiniteBlock24.Valid :=
  And.intro lagariasFiniteBlock24_analyticValid lagariasFiniteBlock24_rangeValid

def lagariasFiniteBlock25 : LagariasFiniteBlock where
  first := 360
  sigmaBound := 1170
  harmonicLower := (42115544611046208681497294660109132374620813235096080827527095642134938390307433779314171485104155840711494655183398192992862196356078091373478401094972582097 / 6516091343560613252952815004446332120738098174420035701754078009877543690470139130502961508897452361461521086225916951753951560602825898016625000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock25_harmonicLower_le :
    (lagariasFiniteBlock25.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock25.first : Real) := by
  change (((42115544611046208681497294660109132374620813235096080827527095642134938390307433779314171485104155840711494655183398192992862196356078091373478401094972582097 / 6516091343560613252952815004446332120738098174420035701754078009877543690470139130502961508897452361461521086225916951753951560602825898016625000000000000000) : Rat) : Real) <=     (harmonic 360 : Real)
  have hLog :
      (8 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((45 / 32) : Rat)           32 : Real) <=
        Real.log (360 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (360 : Real))
      (q := ((45 / 32) : Rat))
      (r := ((45 / 32) : Rat))
      8 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((42115544611046208681497294660109132374620813235096080827527095642134938390307433779314171485104155840711494655183398192992862196356078091373478401094972582097 / 6516091343560613252952815004446332120738098174420035701754078009877543690470139130502961508897452361461521086225916951753951560602825898016625000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((8 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((45 / 32) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock25_analyticValid : lagariasFiniteBlock25.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock25
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock25_rangeChunk00 :
    lagariasSigmaRangeValidBool
      360 1170 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock25_rangeChunk01 :
    lagariasSigmaRangeValidBool
      390 1170 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock25_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock25.first lagariasFiniteBlock25.sigmaBound
        lagariasFiniteBlock25.count = true := by
  unfold lagariasFiniteBlock25
  have hRange00 :
      lagariasSigmaRangeValidBool
        360 1170 60 = true :=
    lagariasSigmaRangeValidBool_add
      360 1170 30 30
      lagariasFiniteBlock25_rangeChunk00 lagariasFiniteBlock25_rangeChunk01
  exact hRange00

theorem lagariasFiniteBlock25_valid : lagariasFiniteBlock25.Valid :=
  And.intro lagariasFiniteBlock25_analyticValid lagariasFiniteBlock25_rangeValid

def lagariasFiniteBlock26 : LagariasFiniteBlock where
  first := 420
  sigmaBound := 1344
  harmonicLower := (260814883511862691851439618046164357416404082073493730473648371845792469528485594159087300168081947963658099330241475159864890384761365639426164812819133169414604897525924470446057 / 39413112859881927534882515427247950352943011337110044582239105330458543653348729637953268971066996773984742366929014968874048081254942522723233743918539314847071625000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock26_harmonicLower_le :
    (lagariasFiniteBlock26.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock26.first : Real) := by
  change (((260814883511862691851439618046164357416404082073493730473648371845792469528485594159087300168081947963658099330241475159864890384761365639426164812819133169414604897525924470446057 / 39413112859881927534882515427247950352943011337110044582239105330458543653348729637953268971066996773984742366929014968874048081254942522723233743918539314847071625000000000000000) : Rat) : Real) <=     (harmonic 420 : Real)
  have hLog :
      (8 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((105 / 64) : Rat)           32 : Real) <=
        Real.log (420 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (420 : Real))
      (q := ((105 / 64) : Rat))
      (r := ((105 / 64) : Rat))
      8 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((260814883511862691851439618046164357416404082073493730473648371845792469528485594159087300168081947963658099330241475159864890384761365639426164812819133169414604897525924470446057 / 39413112859881927534882515427247950352943011337110044582239105330458543653348729637953268971066996773984742366929014968874048081254942522723233743918539314847071625000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((8 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((105 / 64) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock26_analyticValid : lagariasFiniteBlock26.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock26
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock26_rangeChunk00 :
    lagariasSigmaRangeValidBool
      420 1344 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock26_rangeChunk01 :
    lagariasSigmaRangeValidBool
      450 1344 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock26_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock26.first lagariasFiniteBlock26.sigmaBound
        lagariasFiniteBlock26.count = true := by
  unfold lagariasFiniteBlock26
  have hRange00 :
      lagariasSigmaRangeValidBool
        420 1344 60 = true :=
    lagariasSigmaRangeValidBool_add
      420 1344 30 30
      lagariasFiniteBlock26_rangeChunk00 lagariasFiniteBlock26_rangeChunk01
  exact hRange00

theorem lagariasFiniteBlock26_valid : lagariasFiniteBlock26.Valid :=
  And.intro lagariasFiniteBlock26_analyticValid lagariasFiniteBlock26_rangeValid

def lagariasFiniteBlock27 : LagariasFiniteBlock where
  first := 480
  sigmaBound := 1560
  harmonicLower := (34025394223808497394101226622733446073300911339386717664691601538397937090595899752176569346085793164835088985419132570818789 / 5040055378515552808204508438205450006171641677642614030534157672200664024343675288662934153453905188104965125000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock27_harmonicLower_le :
    (lagariasFiniteBlock27.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock27.first : Real) := by
  change (((34025394223808497394101226622733446073300911339386717664691601538397937090595899752176569346085793164835088985419132570818789 / 5040055378515552808204508438205450006171641677642614030534157672200664024343675288662934153453905188104965125000000000000000) : Rat) : Real) <=     (harmonic 480 : Real)
  have hLog :
      (8 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((15 / 8) : Rat)           32 : Real) <=
        Real.log (480 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (480 : Real))
      (q := ((15 / 8) : Rat))
      (r := ((15 / 8) : Rat))
      8 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((34025394223808497394101226622733446073300911339386717664691601538397937090595899752176569346085793164835088985419132570818789 / 5040055378515552808204508438205450006171641677642614030534157672200664024343675288662934153453905188104965125000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((8 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((15 / 8) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock27_analyticValid : lagariasFiniteBlock27.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock27
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock27_rangeChunk00 :
    lagariasSigmaRangeValidBool
      480 1560 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock27_rangeChunk01 :
    lagariasSigmaRangeValidBool
      510 1560 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock27_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock27.first lagariasFiniteBlock27.sigmaBound
        lagariasFiniteBlock27.count = true := by
  unfold lagariasFiniteBlock27
  have hRange00 :
      lagariasSigmaRangeValidBool
        480 1560 60 = true :=
    lagariasSigmaRangeValidBool_add
      480 1560 30 30
      lagariasFiniteBlock27_rangeChunk00 lagariasFiniteBlock27_rangeChunk01
  exact hRange00

theorem lagariasFiniteBlock27_valid : lagariasFiniteBlock27.Valid :=
  And.intro lagariasFiniteBlock27_analyticValid lagariasFiniteBlock27_rangeValid

def lagariasFiniteBlock28 : LagariasFiniteBlock where
  first := 540
  sigmaBound := 1860
  harmonicLower := (1562203362864643023504518955497327829149595656180839038526850939117157321155598233972281801689683383055365226219085941039851095051270979745571241291442733935494607533895250988382614718870891897 / 227435375504750421431092767989847777403801040879102089793752662262603042002336789886290636844117109258385325695792759001003997644936592594760603394260710852941576056165584037000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock28_harmonicLower_le :
    (lagariasFiniteBlock28.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock28.first : Real) := by
  change (((1562203362864643023504518955497327829149595656180839038526850939117157321155598233972281801689683383055365226219085941039851095051270979745571241291442733935494607533895250988382614718870891897 / 227435375504750421431092767989847777403801040879102089793752662262603042002336789886290636844117109258385325695792759001003997644936592594760603394260710852941576056165584037000000000000000000) : Rat) : Real) <=     (harmonic 540 : Real)
  have hLog :
      (9 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((135 / 128) : Rat)           32 : Real) <=
        Real.log (540 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (540 : Real))
      (q := ((135 / 128) : Rat))
      (r := ((135 / 128) : Rat))
      9 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((1562203362864643023504518955497327829149595656180839038526850939117157321155598233972281801689683383055365226219085941039851095051270979745571241291442733935494607533895250988382614718870891897 / 227435375504750421431092767989847777403801040879102089793752662262603042002336789886290636844117109258385325695792759001003997644936592594760603394260710852941576056165584037000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((9 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((135 / 128) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock28_analyticValid : lagariasFiniteBlock28.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock28
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock28_rangeChunk00 :
    lagariasSigmaRangeValidBool
      540 1860 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock28_rangeChunk01 :
    lagariasSigmaRangeValidBool
      570 1860 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock28_rangeChunk02 :
    lagariasSigmaRangeValidBool
      600 1860 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock28_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock28.first lagariasFiniteBlock28.sigmaBound
        lagariasFiniteBlock28.count = true := by
  unfold lagariasFiniteBlock28
  have hRange01 :
      lagariasSigmaRangeValidBool
        570 1860 60 = true :=
    lagariasSigmaRangeValidBool_add
      570 1860 30 30
      lagariasFiniteBlock28_rangeChunk01 lagariasFiniteBlock28_rangeChunk02
  have hRange00 :
      lagariasSigmaRangeValidBool
        540 1860 90 = true :=
    lagariasSigmaRangeValidBool_add
      540 1860 30 60
      lagariasFiniteBlock28_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock28_valid : lagariasFiniteBlock28.Valid :=
  And.intro lagariasFiniteBlock28_analyticValid lagariasFiniteBlock28_rangeValid

def lagariasFiniteBlock29 : LagariasFiniteBlock where
  first := 630
  sigmaBound := 2016
  harmonicLower := (3150600418315503931653630107796403277423444284876281229194672019441127067970363155185533361719780617113715080700808844349562569408018522308595719458638543592178747878882323985973630781549707928656121096847829514473 / 448616246971288039752649573894899215350321144577351242906115506289526510410468717976023470703322326738185640815486203348278409561843768982573391292454952354309987621063345521551593505523971131733000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock29_harmonicLower_le :
    (lagariasFiniteBlock29.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock29.first : Real) := by
  change (((3150600418315503931653630107796403277423444284876281229194672019441127067970363155185533361719780617113715080700808844349562569408018522308595719458638543592178747878882323985973630781549707928656121096847829514473 / 448616246971288039752649573894899215350321144577351242906115506289526510410468717976023470703322326738185640815486203348278409561843768982573391292454952354309987621063345521551593505523971131733000000000000000000) : Rat) : Real) <=     (harmonic 630 : Real)
  have hLog :
      (9 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((315 / 256) : Rat)           32 : Real) <=
        Real.log (630 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (630 : Real))
      (q := ((315 / 256) : Rat))
      (r := ((315 / 256) : Rat))
      9 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((3150600418315503931653630107796403277423444284876281229194672019441127067970363155185533361719780617113715080700808844349562569408018522308595719458638543592178747878882323985973630781549707928656121096847829514473 / 448616246971288039752649573894899215350321144577351242906115506289526510410468717976023470703322326738185640815486203348278409561843768982573391292454952354309987621063345521551593505523971131733000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((9 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((315 / 256) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock29_analyticValid : lagariasFiniteBlock29.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock29
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock29_rangeChunk00 :
    lagariasSigmaRangeValidBool
      630 2016 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock29_rangeChunk01 :
    lagariasSigmaRangeValidBool
      660 2016 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock29_rangeChunk02 :
    lagariasSigmaRangeValidBool
      690 2016 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock29_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock29.first lagariasFiniteBlock29.sigmaBound
        lagariasFiniteBlock29.count = true := by
  unfold lagariasFiniteBlock29
  have hRange01 :
      lagariasSigmaRangeValidBool
        660 2016 60 = true :=
    lagariasSigmaRangeValidBool_add
      660 2016 30 30
      lagariasFiniteBlock29_rangeChunk01 lagariasFiniteBlock29_rangeChunk02
  have hRange00 :
      lagariasSigmaRangeValidBool
        630 2016 90 = true :=
    lagariasSigmaRangeValidBool_add
      630 2016 30 60
      lagariasFiniteBlock29_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock29_valid : lagariasFiniteBlock29.Valid :=
  And.intro lagariasFiniteBlock29_analyticValid lagariasFiniteBlock29_rangeValid

def lagariasFiniteBlock30 : LagariasFiniteBlock where
  first := 720
  sigmaBound := 2418
  harmonicLower := (373057239632850509581555502413255632844307066532174371200361749239930311983476718766010029178779535694060631091702243898016771886421843689499609493604753238873 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 120
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock30_harmonicLower_le :
    (lagariasFiniteBlock30.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock30.first : Real) := by
  change (((373057239632850509581555502413255632844307066532174371200361749239930311983476718766010029178779535694060631091702243898016771886421843689499609493604753238873 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000) : Rat) : Real) <=     (harmonic 720 : Real)
  have hLog :
      (9 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((45 / 32) : Rat)           32 : Real) <=
        Real.log (720 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (720 : Real))
      (q := ((45 / 32) : Rat))
      (r := ((45 / 32) : Rat))
      9 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((373057239632850509581555502413255632844307066532174371200361749239930311983476718766010029178779535694060631091702243898016771886421843689499609493604753238873 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((9 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((45 / 32) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock30_analyticValid : lagariasFiniteBlock30.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock30
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock30_rangeChunk00 :
    lagariasSigmaRangeValidBool
      720 2418 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock30_rangeChunk01 :
    lagariasSigmaRangeValidBool
      750 2418 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock30_rangeChunk02 :
    lagariasSigmaRangeValidBool
      780 2418 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock30_rangeChunk03 :
    lagariasSigmaRangeValidBool
      810 2418 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock30_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock30.first lagariasFiniteBlock30.sigmaBound
        lagariasFiniteBlock30.count = true := by
  unfold lagariasFiniteBlock30
  have hRange02 :
      lagariasSigmaRangeValidBool
        780 2418 60 = true :=
    lagariasSigmaRangeValidBool_add
      780 2418 30 30
      lagariasFiniteBlock30_rangeChunk02 lagariasFiniteBlock30_rangeChunk03
  have hRange01 :
      lagariasSigmaRangeValidBool
        750 2418 90 = true :=
    lagariasSigmaRangeValidBool_add
      750 2418 30 60
      lagariasFiniteBlock30_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        720 2418 120 = true :=
    lagariasSigmaRangeValidBool_add
      720 2418 30 90
      lagariasFiniteBlock30_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock30_valid : lagariasFiniteBlock30.Valid :=
  And.intro lagariasFiniteBlock30_analyticValid lagariasFiniteBlock30_rangeValid

end Robin1984
