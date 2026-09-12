import Robin1984.Lagarias.FiniteCertificate

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Lagarias (2001) supplies the finite range.
- Formalization note: Generated exact factor and rational certificate data.
- PROVENANCE-END
-/

/-! # Lagarias finite certificate packet 04 -/

namespace Robin1984

def lagariasFiniteBlock41 : LagariasFiniteBlock where
  first := 3360
  sigmaBound := 12493
  harmonicLower := (2742177181436935475517435987971046307191954422724458410854832599393602781500830173499756145207642585145765029113314082361838151970524809250453749432348544939870595874786419174906627 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 420
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock41_harmonicLower_le :
    (lagariasFiniteBlock41.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock41.first : Real) := by
  change (((2742177181436935475517435987971046307191954422724458410854832599393602781500830173499756145207642585145765029113314082361838151970524809250453749432348544939870595874786419174906627 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000) : Rat) : Real) <=     (harmonic 3360 : Real)
  have hLog :
      (11 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((105 / 64) : Rat)           32 : Real) <=
        Real.log (3360 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (3360 : Real))
      (q := ((105 / 64) : Rat))
      (r := ((105 / 64) : Rat))
      11 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((2742177181436935475517435987971046307191954422724458410854832599393602781500830173499756145207642585145765029113314082361838151970524809250453749432348544939870595874786419174906627 / 315304902879055420279060123417983602823544090696880356657912842643668349226789837103626151768535974191877938935432119750992384650039540181785869951348314518776573000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((11 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((105 / 64) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock41_analyticValid : lagariasFiniteBlock41.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock41
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk00 :
    lagariasSigmaRangeValidBool
      3360 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk01 :
    lagariasSigmaRangeValidBool
      3390 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk02 :
    lagariasSigmaRangeValidBool
      3420 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk03 :
    lagariasSigmaRangeValidBool
      3450 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk04 :
    lagariasSigmaRangeValidBool
      3480 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk05 :
    lagariasSigmaRangeValidBool
      3510 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk06 :
    lagariasSigmaRangeValidBool
      3540 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk07 :
    lagariasSigmaRangeValidBool
      3570 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk08 :
    lagariasSigmaRangeValidBool
      3600 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk09 :
    lagariasSigmaRangeValidBool
      3630 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk10 :
    lagariasSigmaRangeValidBool
      3660 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk11 :
    lagariasSigmaRangeValidBool
      3690 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk12 :
    lagariasSigmaRangeValidBool
      3720 12493 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock41_rangeChunk13 :
    lagariasSigmaRangeValidBool
      3750 12493 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock41_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock41.first lagariasFiniteBlock41.sigmaBound
        lagariasFiniteBlock41.count = true := by
  unfold lagariasFiniteBlock41
  have hRange12 :
      lagariasSigmaRangeValidBool
        3720 12493 60 = true :=
    lagariasSigmaRangeValidBool_add
      3720 12493 30 30
      lagariasFiniteBlock41_rangeChunk12 lagariasFiniteBlock41_rangeChunk13
  have hRange11 :
      lagariasSigmaRangeValidBool
        3690 12493 90 = true :=
    lagariasSigmaRangeValidBool_add
      3690 12493 30 60
      lagariasFiniteBlock41_rangeChunk11 hRange12
  have hRange10 :
      lagariasSigmaRangeValidBool
        3660 12493 120 = true :=
    lagariasSigmaRangeValidBool_add
      3660 12493 30 90
      lagariasFiniteBlock41_rangeChunk10 hRange11
  have hRange09 :
      lagariasSigmaRangeValidBool
        3630 12493 150 = true :=
    lagariasSigmaRangeValidBool_add
      3630 12493 30 120
      lagariasFiniteBlock41_rangeChunk09 hRange10
  have hRange08 :
      lagariasSigmaRangeValidBool
        3600 12493 180 = true :=
    lagariasSigmaRangeValidBool_add
      3600 12493 30 150
      lagariasFiniteBlock41_rangeChunk08 hRange09
  have hRange07 :
      lagariasSigmaRangeValidBool
        3570 12493 210 = true :=
    lagariasSigmaRangeValidBool_add
      3570 12493 30 180
      lagariasFiniteBlock41_rangeChunk07 hRange08
  have hRange06 :
      lagariasSigmaRangeValidBool
        3540 12493 240 = true :=
    lagariasSigmaRangeValidBool_add
      3540 12493 30 210
      lagariasFiniteBlock41_rangeChunk06 hRange07
  have hRange05 :
      lagariasSigmaRangeValidBool
        3510 12493 270 = true :=
    lagariasSigmaRangeValidBool_add
      3510 12493 30 240
      lagariasFiniteBlock41_rangeChunk05 hRange06
  have hRange04 :
      lagariasSigmaRangeValidBool
        3480 12493 300 = true :=
    lagariasSigmaRangeValidBool_add
      3480 12493 30 270
      lagariasFiniteBlock41_rangeChunk04 hRange05
  have hRange03 :
      lagariasSigmaRangeValidBool
        3450 12493 330 = true :=
    lagariasSigmaRangeValidBool_add
      3450 12493 30 300
      lagariasFiniteBlock41_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        3420 12493 360 = true :=
    lagariasSigmaRangeValidBool_add
      3420 12493 30 330
      lagariasFiniteBlock41_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        3390 12493 390 = true :=
    lagariasSigmaRangeValidBool_add
      3390 12493 30 360
      lagariasFiniteBlock41_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        3360 12493 420 = true :=
    lagariasSigmaRangeValidBool_add
      3360 12493 30 390
      lagariasFiniteBlock41_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock41_valid : lagariasFiniteBlock41.Valid :=
  And.intro lagariasFiniteBlock41_analyticValid lagariasFiniteBlock41_rangeValid

def lagariasFiniteBlock42 : LagariasFiniteBlock where
  first := 3780
  sigmaBound := 14040
  harmonicLower := (88775833881475950442371652041511186212181026776035777860112210150726503866817962004600775630356607246541689341550961829795059785248179571638042874439327904893264751747965022652054071741001428607128856396844285985351862922202997673830415351 / 10071351465122208074039107536276979603760301809254116609612761403880126299452965266813718752492649891963231308642504342881586467342133231091935721613721704816871736694518701883181920402099501003093409345489614308762186249000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 420
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock42_harmonicLower_le :
    (lagariasFiniteBlock42.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock42.first : Real) := by
  change (((88775833881475950442371652041511186212181026776035777860112210150726503866817962004600775630356607246541689341550961829795059785248179571638042874439327904893264751747965022652054071741001428607128856396844285985351862922202997673830415351 / 10071351465122208074039107536276979603760301809254116609612761403880126299452965266813718752492649891963231308642504342881586467342133231091935721613721704816871736694518701883181920402099501003093409345489614308762186249000000000000000000) : Rat) : Real) <=     (harmonic 3780 : Real)
  have hLog :
      (11 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((945 / 512) : Rat)           32 : Real) <=
        Real.log (3780 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (3780 : Real))
      (q := ((945 / 512) : Rat))
      (r := ((945 / 512) : Rat))
      11 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((88775833881475950442371652041511186212181026776035777860112210150726503866817962004600775630356607246541689341550961829795059785248179571638042874439327904893264751747965022652054071741001428607128856396844285985351862922202997673830415351 / 10071351465122208074039107536276979603760301809254116609612761403880126299452965266813718752492649891963231308642504342881586467342133231091935721613721704816871736694518701883181920402099501003093409345489614308762186249000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((11 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((945 / 512) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock42_analyticValid : lagariasFiniteBlock42.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock42
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk00 :
    lagariasSigmaRangeValidBool
      3780 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk01 :
    lagariasSigmaRangeValidBool
      3810 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk02 :
    lagariasSigmaRangeValidBool
      3840 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk03 :
    lagariasSigmaRangeValidBool
      3870 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk04 :
    lagariasSigmaRangeValidBool
      3900 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk05 :
    lagariasSigmaRangeValidBool
      3930 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk06 :
    lagariasSigmaRangeValidBool
      3960 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk07 :
    lagariasSigmaRangeValidBool
      3990 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk08 :
    lagariasSigmaRangeValidBool
      4020 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk09 :
    lagariasSigmaRangeValidBool
      4050 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk10 :
    lagariasSigmaRangeValidBool
      4080 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk11 :
    lagariasSigmaRangeValidBool
      4110 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk12 :
    lagariasSigmaRangeValidBool
      4140 14040 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock42_rangeChunk13 :
    lagariasSigmaRangeValidBool
      4170 14040 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock42_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock42.first lagariasFiniteBlock42.sigmaBound
        lagariasFiniteBlock42.count = true := by
  unfold lagariasFiniteBlock42
  have hRange12 :
      lagariasSigmaRangeValidBool
        4140 14040 60 = true :=
    lagariasSigmaRangeValidBool_add
      4140 14040 30 30
      lagariasFiniteBlock42_rangeChunk12 lagariasFiniteBlock42_rangeChunk13
  have hRange11 :
      lagariasSigmaRangeValidBool
        4110 14040 90 = true :=
    lagariasSigmaRangeValidBool_add
      4110 14040 30 60
      lagariasFiniteBlock42_rangeChunk11 hRange12
  have hRange10 :
      lagariasSigmaRangeValidBool
        4080 14040 120 = true :=
    lagariasSigmaRangeValidBool_add
      4080 14040 30 90
      lagariasFiniteBlock42_rangeChunk10 hRange11
  have hRange09 :
      lagariasSigmaRangeValidBool
        4050 14040 150 = true :=
    lagariasSigmaRangeValidBool_add
      4050 14040 30 120
      lagariasFiniteBlock42_rangeChunk09 hRange10
  have hRange08 :
      lagariasSigmaRangeValidBool
        4020 14040 180 = true :=
    lagariasSigmaRangeValidBool_add
      4020 14040 30 150
      lagariasFiniteBlock42_rangeChunk08 hRange09
  have hRange07 :
      lagariasSigmaRangeValidBool
        3990 14040 210 = true :=
    lagariasSigmaRangeValidBool_add
      3990 14040 30 180
      lagariasFiniteBlock42_rangeChunk07 hRange08
  have hRange06 :
      lagariasSigmaRangeValidBool
        3960 14040 240 = true :=
    lagariasSigmaRangeValidBool_add
      3960 14040 30 210
      lagariasFiniteBlock42_rangeChunk06 hRange07
  have hRange05 :
      lagariasSigmaRangeValidBool
        3930 14040 270 = true :=
    lagariasSigmaRangeValidBool_add
      3930 14040 30 240
      lagariasFiniteBlock42_rangeChunk05 hRange06
  have hRange04 :
      lagariasSigmaRangeValidBool
        3900 14040 300 = true :=
    lagariasSigmaRangeValidBool_add
      3900 14040 30 270
      lagariasFiniteBlock42_rangeChunk04 hRange05
  have hRange03 :
      lagariasSigmaRangeValidBool
        3870 14040 330 = true :=
    lagariasSigmaRangeValidBool_add
      3870 14040 30 300
      lagariasFiniteBlock42_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        3840 14040 360 = true :=
    lagariasSigmaRangeValidBool_add
      3840 14040 30 330
      lagariasFiniteBlock42_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        3810 14040 390 = true :=
    lagariasSigmaRangeValidBool_add
      3810 14040 30 360
      lagariasFiniteBlock42_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        3780 14040 420 = true :=
    lagariasSigmaRangeValidBool_add
      3780 14040 30 390
      lagariasFiniteBlock42_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock42_valid : lagariasFiniteBlock42.Valid :=
  And.intro lagariasFiniteBlock42_analyticValid lagariasFiniteBlock42_rangeValid

end Robin1984
