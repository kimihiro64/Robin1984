import Submission.Robin1984.Lagarias.FiniteCertificate

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Lagarias (2001) supplies the finite range.
- Formalization note: Generated exact factor and rational certificate data.
- PROVENANCE-END
-/

/-! # Lagarias finite certificate packet 01 -/

namespace Robin1984

def lagariasFiniteBlock31 : LagariasFiniteBlock where
  first := 840
  sigmaBound := 2880
  harmonicLower := (2305071772542246181713489958903225341951473245300119366144402182975427431318866560015050982632317917521431539465725894973225466042235553160424128812484891883501424745067070234014513 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 120
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock31_harmonicLower_le :
    (lagariasFiniteBlock31.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock31.first : Real) := by
  change (((2305071772542246181713489958903225341951473245300119366144402182975427431318866560015050982632317917521431539465725894973225466042235553160424128812484891883501424745067070234014513 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000) : Rat) : Real) <=     (harmonic 840 : Real)
  have hLog :
      (9 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((105 / 64) : Rat)           32 : Real) <=
        Real.log (840 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (840 : Real))
      (q := ((105 / 64) : Rat))
      (r := ((105 / 64) : Rat))
      9 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((2305071772542246181713489958903225341951473245300119366144402182975427431318866560015050982632317917521431539465725894973225466042235553160424128812484891883501424745067070234014513 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((9 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((105 / 64) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock31_analyticValid : lagariasFiniteBlock31.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock31
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock31_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock31.first lagariasFiniteBlock31.sigmaBound
        lagariasFiniteBlock31.count = true := by
  unfold lagariasFiniteBlock31
  decide +kernel

theorem lagariasFiniteBlock31_valid : lagariasFiniteBlock31.Valid :=
  And.intro lagariasFiniteBlock31_analyticValid lagariasFiniteBlock31_rangeValid

def lagariasFiniteBlock32 : LagariasFiniteBlock where
  first := 960
  sigmaBound := 3224
  harmonicLower := (300151155194340326204394125507661193746670603787239971472077269819635008848098329251722167254272685338878523708970943137369101 / 40320443028124422465636067505643600049373133421140912244273261377605312194749402309303473227631241504839721000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 120
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock32_harmonicLower_le :
    (lagariasFiniteBlock32.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock32.first : Real) := by
  change (((300151155194340326204394125507661193746670603787239971472077269819635008848098329251722167254272685338878523708970943137369101 / 40320443028124422465636067505643600049373133421140912244273261377605312194749402309303473227631241504839721000000000000000000) : Rat) : Real) <=     (harmonic 960 : Real)
  have hLog :
      (9 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((15 / 8) : Rat)           32 : Real) <=
        Real.log (960 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (960 : Real))
      (q := ((15 / 8) : Rat))
      (r := ((15 / 8) : Rat))
      9 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((300151155194340326204394125507661193746670603787239971472077269819635008848098329251722167254272685338878523708970943137369101 / 40320443028124422465636067505643600049373133421140912244273261377605312194749402309303473227631241504839721000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((9 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((15 / 8) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock32_analyticValid : lagariasFiniteBlock32.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock32
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock32_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock32.first lagariasFiniteBlock32.sigmaBound
        lagariasFiniteBlock32.count = true := by
  unfold lagariasFiniteBlock32
  decide +kernel

theorem lagariasFiniteBlock32_valid : lagariasFiniteBlock32.Valid :=
  And.intro lagariasFiniteBlock32_analyticValid lagariasFiniteBlock32_rangeValid

def lagariasFiniteBlock33 : LagariasFiniteBlock where
  first := 1080
  sigmaBound := 3844
  harmonicLower := (171984955215535322633783097764399854686604869152858796460906782989408161991914543279055512981353434243905284565437956184361294962636513495296772893515331169663221824709197154039881968763432433 / 22743537550475042143109276798984777740380104087910208979375266226260304200233678988629063684411710925838532569579275900100399764493659259476060339426071085294157605616558403700000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 180
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock33_harmonicLower_le :
    (lagariasFiniteBlock33.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock33.first : Real) := by
  change (((171984955215535322633783097764399854686604869152858796460906782989408161991914543279055512981353434243905284565437956184361294962636513495296772893515331169663221824709197154039881968763432433 / 22743537550475042143109276798984777740380104087910208979375266226260304200233678988629063684411710925838532569579275900100399764493659259476060339426071085294157605616558403700000000000000000) : Rat) : Real) <=     (harmonic 1080 : Real)
  have hLog :
      (10 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((135 / 128) : Rat)           32 : Real) <=
        Real.log (1080 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (1080 : Real))
      (q := ((135 / 128) : Rat))
      (r := ((135 / 128) : Rat))
      10 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((171984955215535322633783097764399854686604869152858796460906782989408161991914543279055512981353434243905284565437956184361294962636513495296772893515331169663221824709197154039881968763432433 / 22743537550475042143109276798984777740380104087910208979375266226260304200233678988629063684411710925838532569579275900100399764493659259476060339426071085294157605616558403700000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((10 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((135 / 128) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock33_analyticValid : lagariasFiniteBlock33.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock33
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock33_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock33.first lagariasFiniteBlock33.sigmaBound
        lagariasFiniteBlock33.count = true := by
  unfold lagariasFiniteBlock33
  decide +kernel

theorem lagariasFiniteBlock33_valid : lagariasFiniteBlock33.Valid :=
  And.intro lagariasFiniteBlock33_analyticValid lagariasFiniteBlock33_rangeValid

def lagariasFiniteBlock34 : LagariasFiniteBlock where
  first := 1260
  sigmaBound := 4368
  harmonicLower := (346155750505703634040866525301715593415102977299763765163413960349058353735560055486431096117351942141755132352056832727511874096978415503957309860871192229603467430887167403586523696104893612591127178205314390497 / 44861624697128803975264957389489921535032114457735124290611550628952651041046871797602347070332232673818564081548620334827840956184376898257339129245495235430998762106334552155159350552397113173300000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 180
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock34_harmonicLower_le :
    (lagariasFiniteBlock34.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock34.first : Real) := by
  change (((346155750505703634040866525301715593415102977299763765163413960349058353735560055486431096117351942141755132352056832727511874096978415503957309860871192229603467430887167403586523696104893612591127178205314390497 / 44861624697128803975264957389489921535032114457735124290611550628952651041046871797602347070332232673818564081548620334827840956184376898257339129245495235430998762106334552155159350552397113173300000000000000000) : Rat) : Real) <=     (harmonic 1260 : Real)
  have hLog :
      (10 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((315 / 256) : Rat)           32 : Real) <=
        Real.log (1260 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (1260 : Real))
      (q := ((315 / 256) : Rat))
      (r := ((315 / 256) : Rat))
      10 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((346155750505703634040866525301715593415102977299763765163413960349058353735560055486431096117351942141755132352056832727511874096978415503957309860871192229603467430887167403586523696104893612591127178205314390497 / 44861624697128803975264957389489921535032114457735124290611550628952651041046871797602347070332232673818564081548620334827840956184376898257339129245495235430998762106334552155159350552397113173300000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((10 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((315 / 256) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock34_analyticValid : lagariasFiniteBlock34.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock34
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock34_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock34.first lagariasFiniteBlock34.sigmaBound
        lagariasFiniteBlock34.count = true := by
  unfold lagariasFiniteBlock34
  decide +kernel

theorem lagariasFiniteBlock34_valid : lagariasFiniteBlock34.Valid :=
  And.intro lagariasFiniteBlock34_analyticValid lagariasFiniteBlock34_rangeValid

def lagariasFiniteBlock35 : LagariasFiniteBlock where
  first := 1440
  sigmaBound := 5082
  harmonicLower := (40919012237733134971113264754563820669164762718358009578050673334278111684449396729750668647672582466242930494193730225209064620199506264801139177844972582097 / 5212873074848490602362252003557065696590478539536028561403262407902034952376111304402369207117961889169216868980733561403161248482260718413300000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 240
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock35_harmonicLower_le :
    (lagariasFiniteBlock35.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock35.first : Real) := by
  change (((40919012237733134971113264754563820669164762718358009578050673334278111684449396729750668647672582466242930494193730225209064620199506264801139177844972582097 / 5212873074848490602362252003557065696590478539536028561403262407902034952376111304402369207117961889169216868980733561403161248482260718413300000000000000000) : Rat) : Real) <=     (harmonic 1440 : Real)
  have hLog :
      (10 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((45 / 32) : Rat)           32 : Real) <=
        Real.log (1440 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (1440 : Real))
      (q := ((45 / 32) : Rat))
      (r := ((45 / 32) : Rat))
      10 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((40919012237733134971113264754563820669164762718358009578050673334278111684449396729750668647672582466242930494193730225209064620199506264801139177844972582097 / 5212873074848490602362252003557065696590478539536028561403262407902034952376111304402369207117961889169216868980733561403161248482260718413300000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((10 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((45 / 32) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock35_analyticValid : lagariasFiniteBlock35.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock35
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock35_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock35.first lagariasFiniteBlock35.sigmaBound
        lagariasFiniteBlock35.count = true := by
  unfold lagariasFiniteBlock35
  decide +kernel

theorem lagariasFiniteBlock35_valid : lagariasFiniteBlock35.Valid :=
  And.intro lagariasFiniteBlock35_analyticValid lagariasFiniteBlock35_rangeValid

end Robin1984
