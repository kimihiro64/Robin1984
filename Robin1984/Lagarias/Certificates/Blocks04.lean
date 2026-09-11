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
theorem lagariasFiniteBlock41_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock41.first lagariasFiniteBlock41.sigmaBound
        lagariasFiniteBlock41.count = true := by
  unfold lagariasFiniteBlock41
  decide +kernel

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
theorem lagariasFiniteBlock42_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock42.first lagariasFiniteBlock42.sigmaBound
        lagariasFiniteBlock42.count = true := by
  unfold lagariasFiniteBlock42
  decide +kernel

theorem lagariasFiniteBlock42_valid : lagariasFiniteBlock42.Valid :=
  And.intro lagariasFiniteBlock42_analyticValid lagariasFiniteBlock42_rangeValid

end Robin1984
