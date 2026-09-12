import Robin1984.Lagarias.Certificates.Blocks04

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Lagarias (2001) supplies the finite range.
- Formalization note: Generated exact factor and rational certificate data.
- PROVENANCE-END
-/

/-! # Lagarias finite certificate packet 05 -/

namespace Robin1984

def lagariasFiniteBlock43 : LagariasFiniteBlock where
  first := 4200
  sigmaBound := 16128
  harmonicLower := (63458349614496326526033673215711829766495903060056553235738979921254292573567100079281061295824625046563991650121450629072690084990493679146123630937870650615638396670302167229858242289441254456264563087563818238688443317421729 / 7114125033708738752187278455468409336027226640864876572880727909503502783391498130805360110216727989571503274496689968745962086604888972943859557561923596775437142504469321390783151323263006521141073963129281750000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 480
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock43_harmonicLower_le :
    (lagariasFiniteBlock43.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock43.first : Real) := by
  change (((63458349614496326526033673215711829766495903060056553235738979921254292573567100079281061295824625046563991650121450629072690084990493679146123630937870650615638396670302167229858242289441254456264563087563818238688443317421729 / 7114125033708738752187278455468409336027226640864876572880727909503502783391498130805360110216727989571503274496689968745962086604888972943859557561923596775437142504469321390783151323263006521141073963129281750000000000000000) : Rat) : Real) <=     (harmonic 4200 : Real)
  have hLog :
      (12 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((525 / 512) : Rat)           32 : Real) <=
        Real.log (4200 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (4200 : Real))
      (q := ((525 / 512) : Rat))
      (r := ((525 / 512) : Rat))
      12 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((63458349614496326526033673215711829766495903060056553235738979921254292573567100079281061295824625046563991650121450629072690084990493679146123630937870650615638396670302167229858242289441254456264563087563818238688443317421729 / 7114125033708738752187278455468409336027226640864876572880727909503502783391498130805360110216727989571503274496689968745962086604888972943859557561923596775437142504469321390783151323263006521141073963129281750000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((12 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((525 / 512) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock43_analyticValid : lagariasFiniteBlock43.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock43
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk00 :
    lagariasSigmaRangeValidBool
      4200 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk01 :
    lagariasSigmaRangeValidBool
      4230 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk02 :
    lagariasSigmaRangeValidBool
      4260 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk03 :
    lagariasSigmaRangeValidBool
      4290 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk04 :
    lagariasSigmaRangeValidBool
      4320 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk05 :
    lagariasSigmaRangeValidBool
      4350 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk06 :
    lagariasSigmaRangeValidBool
      4380 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk07 :
    lagariasSigmaRangeValidBool
      4410 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk08 :
    lagariasSigmaRangeValidBool
      4440 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk09 :
    lagariasSigmaRangeValidBool
      4470 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk10 :
    lagariasSigmaRangeValidBool
      4500 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk11 :
    lagariasSigmaRangeValidBool
      4530 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk12 :
    lagariasSigmaRangeValidBool
      4560 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk13 :
    lagariasSigmaRangeValidBool
      4590 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk14 :
    lagariasSigmaRangeValidBool
      4620 16128 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock43_rangeChunk15 :
    lagariasSigmaRangeValidBool
      4650 16128 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock43_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock43.first lagariasFiniteBlock43.sigmaBound
        lagariasFiniteBlock43.count = true := by
  unfold lagariasFiniteBlock43
  have hRange14 :
      lagariasSigmaRangeValidBool
        4620 16128 60 = true :=
    lagariasSigmaRangeValidBool_add
      4620 16128 30 30
      lagariasFiniteBlock43_rangeChunk14 lagariasFiniteBlock43_rangeChunk15
  have hRange13 :
      lagariasSigmaRangeValidBool
        4590 16128 90 = true :=
    lagariasSigmaRangeValidBool_add
      4590 16128 30 60
      lagariasFiniteBlock43_rangeChunk13 hRange14
  have hRange12 :
      lagariasSigmaRangeValidBool
        4560 16128 120 = true :=
    lagariasSigmaRangeValidBool_add
      4560 16128 30 90
      lagariasFiniteBlock43_rangeChunk12 hRange13
  have hRange11 :
      lagariasSigmaRangeValidBool
        4530 16128 150 = true :=
    lagariasSigmaRangeValidBool_add
      4530 16128 30 120
      lagariasFiniteBlock43_rangeChunk11 hRange12
  have hRange10 :
      lagariasSigmaRangeValidBool
        4500 16128 180 = true :=
    lagariasSigmaRangeValidBool_add
      4500 16128 30 150
      lagariasFiniteBlock43_rangeChunk10 hRange11
  have hRange09 :
      lagariasSigmaRangeValidBool
        4470 16128 210 = true :=
    lagariasSigmaRangeValidBool_add
      4470 16128 30 180
      lagariasFiniteBlock43_rangeChunk09 hRange10
  have hRange08 :
      lagariasSigmaRangeValidBool
        4440 16128 240 = true :=
    lagariasSigmaRangeValidBool_add
      4440 16128 30 210
      lagariasFiniteBlock43_rangeChunk08 hRange09
  have hRange07 :
      lagariasSigmaRangeValidBool
        4410 16128 270 = true :=
    lagariasSigmaRangeValidBool_add
      4410 16128 30 240
      lagariasFiniteBlock43_rangeChunk07 hRange08
  have hRange06 :
      lagariasSigmaRangeValidBool
        4380 16128 300 = true :=
    lagariasSigmaRangeValidBool_add
      4380 16128 30 270
      lagariasFiniteBlock43_rangeChunk06 hRange07
  have hRange05 :
      lagariasSigmaRangeValidBool
        4350 16128 330 = true :=
    lagariasSigmaRangeValidBool_add
      4350 16128 30 300
      lagariasFiniteBlock43_rangeChunk05 hRange06
  have hRange04 :
      lagariasSigmaRangeValidBool
        4320 16128 360 = true :=
    lagariasSigmaRangeValidBool_add
      4320 16128 30 330
      lagariasFiniteBlock43_rangeChunk04 hRange05
  have hRange03 :
      lagariasSigmaRangeValidBool
        4290 16128 390 = true :=
    lagariasSigmaRangeValidBool_add
      4290 16128 30 360
      lagariasFiniteBlock43_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        4260 16128 420 = true :=
    lagariasSigmaRangeValidBool_add
      4260 16128 30 390
      lagariasFiniteBlock43_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        4230 16128 450 = true :=
    lagariasSigmaRangeValidBool_add
      4230 16128 30 420
      lagariasFiniteBlock43_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        4200 16128 480 = true :=
    lagariasSigmaRangeValidBool_add
      4200 16128 30 450
      lagariasFiniteBlock43_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock43_valid : lagariasFiniteBlock43.Valid :=
  And.intro lagariasFiniteBlock43_analyticValid lagariasFiniteBlock43_rangeValid

def lagariasFiniteBlock44 : LagariasFiniteBlock where
  first := 4680
  sigmaBound := 16380
  harmonicLower := (569059016293272220780789698744589437430653854823745073274961356032680016931529143986504702529007372382326193027490981732238902907455957700060409136249321891304968010403123851577341358638574451213913745618495050792347143404281557703671 / 63030839019625585033830326244726921620757694180373830676628814915680121681981936553223824355885268873656504471372377904018566488372328879009469217515068363802543825457949774443588497357809495879465881765155649925768250000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 360
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock44_harmonicLower_le :
    (lagariasFiniteBlock44.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock44.first : Real) := by
  change (((569059016293272220780789698744589437430653854823745073274961356032680016931529143986504702529007372382326193027490981732238902907455957700060409136249321891304968010403123851577341358638574451213913745618495050792347143404281557703671 / 63030839019625585033830326244726921620757694180373830676628814915680121681981936553223824355885268873656504471372377904018566488372328879009469217515068363802543825457949774443588497357809495879465881765155649925768250000000000000000) : Rat) : Real) <=     (harmonic 4680 : Real)
  have hLog :
      (12 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((585 / 512) : Rat)           32 : Real) <=
        Real.log (4680 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (4680 : Real))
      (q := ((585 / 512) : Rat))
      (r := ((585 / 512) : Rat))
      12 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((569059016293272220780789698744589437430653854823745073274961356032680016931529143986504702529007372382326193027490981732238902907455957700060409136249321891304968010403123851577341358638574451213913745618495050792347143404281557703671 / 63030839019625585033830326244726921620757694180373830676628814915680121681981936553223824355885268873656504471372377904018566488372328879009469217515068363802543825457949774443588497357809495879465881765155649925768250000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((12 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((585 / 512) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock44_analyticValid : lagariasFiniteBlock44.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock44
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk00 :
    lagariasSigmaRangeValidBool
      4680 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk01 :
    lagariasSigmaRangeValidBool
      4710 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk02 :
    lagariasSigmaRangeValidBool
      4740 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk03 :
    lagariasSigmaRangeValidBool
      4770 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk04 :
    lagariasSigmaRangeValidBool
      4800 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk05 :
    lagariasSigmaRangeValidBool
      4830 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk06 :
    lagariasSigmaRangeValidBool
      4860 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk07 :
    lagariasSigmaRangeValidBool
      4890 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk08 :
    lagariasSigmaRangeValidBool
      4920 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk09 :
    lagariasSigmaRangeValidBool
      4950 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk10 :
    lagariasSigmaRangeValidBool
      4980 16380 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock44_rangeChunk11 :
    lagariasSigmaRangeValidBool
      5010 16380 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock44_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock44.first lagariasFiniteBlock44.sigmaBound
        lagariasFiniteBlock44.count = true := by
  unfold lagariasFiniteBlock44
  have hRange10 :
      lagariasSigmaRangeValidBool
        4980 16380 60 = true :=
    lagariasSigmaRangeValidBool_add
      4980 16380 30 30
      lagariasFiniteBlock44_rangeChunk10 lagariasFiniteBlock44_rangeChunk11
  have hRange09 :
      lagariasSigmaRangeValidBool
        4950 16380 90 = true :=
    lagariasSigmaRangeValidBool_add
      4950 16380 30 60
      lagariasFiniteBlock44_rangeChunk09 hRange10
  have hRange08 :
      lagariasSigmaRangeValidBool
        4920 16380 120 = true :=
    lagariasSigmaRangeValidBool_add
      4920 16380 30 90
      lagariasFiniteBlock44_rangeChunk08 hRange09
  have hRange07 :
      lagariasSigmaRangeValidBool
        4890 16380 150 = true :=
    lagariasSigmaRangeValidBool_add
      4890 16380 30 120
      lagariasFiniteBlock44_rangeChunk07 hRange08
  have hRange06 :
      lagariasSigmaRangeValidBool
        4860 16380 180 = true :=
    lagariasSigmaRangeValidBool_add
      4860 16380 30 150
      lagariasFiniteBlock44_rangeChunk06 hRange07
  have hRange05 :
      lagariasSigmaRangeValidBool
        4830 16380 210 = true :=
    lagariasSigmaRangeValidBool_add
      4830 16380 30 180
      lagariasFiniteBlock44_rangeChunk05 hRange06
  have hRange04 :
      lagariasSigmaRangeValidBool
        4800 16380 240 = true :=
    lagariasSigmaRangeValidBool_add
      4800 16380 30 210
      lagariasFiniteBlock44_rangeChunk04 hRange05
  have hRange03 :
      lagariasSigmaRangeValidBool
        4770 16380 270 = true :=
    lagariasSigmaRangeValidBool_add
      4770 16380 30 240
      lagariasFiniteBlock44_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        4740 16380 300 = true :=
    lagariasSigmaRangeValidBool_add
      4740 16380 30 270
      lagariasFiniteBlock44_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        4710 16380 330 = true :=
    lagariasSigmaRangeValidBool_add
      4710 16380 30 300
      lagariasFiniteBlock44_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        4680 16380 360 = true :=
    lagariasSigmaRangeValidBool_add
      4680 16380 30 330
      lagariasFiniteBlock44_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock44_valid : lagariasFiniteBlock44.Valid :=
  And.intro lagariasFiniteBlock44_analyticValid lagariasFiniteBlock44_rangeValid

def lagariasFiniteBlock45 : LagariasFiniteBlock where
  first := 5040
  sigmaBound := 19344
  harmonicLower := (1020867919635025289479683885864665311901550187310087624128268692897374119031518838555466540020249257506305952290021823281557771023328855125381964227214669925936631792212593533912112330011848130105393288115943171491 / 112154061742822009938162393473724803837580286144337810726528876572381627602617179494005867675830581684546410203871550837069602390460942245643347823113738088577496905265836380387898376380992782933250000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock45_harmonicLower_le :
    (lagariasFiniteBlock45.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock45.first : Real) := by
  change (((1020867919635025289479683885864665311901550187310087624128268692897374119031518838555466540020249257506305952290021823281557771023328855125381964227214669925936631792212593533912112330011848130105393288115943171491 / 112154061742822009938162393473724803837580286144337810726528876572381627602617179494005867675830581684546410203871550837069602390460942245643347823113738088577496905265836380387898376380992782933250000000000000000) : Rat) : Real) <=     (harmonic 5040 : Real)
  have hLog :
      (12 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((315 / 256) : Rat)           32 : Real) <=
        Real.log (5040 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (5040 : Real))
      (q := ((315 / 256) : Rat))
      (r := ((315 / 256) : Rat))
      12 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((1020867919635025289479683885864665311901550187310087624128268692897374119031518838555466540020249257506305952290021823281557771023328855125381964227214669925936631792212593533912112330011848130105393288115943171491 / 112154061742822009938162393473724803837580286144337810726528876572381627602617179494005867675830581684546410203871550837069602390460942245643347823113738088577496905265836380387898376380992782933250000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((12 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((315 / 256) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock45_analyticValid : lagariasFiniteBlock45.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock45
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock45_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock45.first lagariasFiniteBlock45.sigmaBound
        lagariasFiniteBlock45.count = true := by
  unfold lagariasFiniteBlock45
  decide +kernel

theorem lagariasFiniteBlock45_valid : lagariasFiniteBlock45.Valid :=
  And.intro lagariasFiniteBlock45_analyticValid lagariasFiniteBlock45_rangeValid

end Robin1984
