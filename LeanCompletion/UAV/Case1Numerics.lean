import LeanCompletion.UAV.Case1Certificate

namespace UAVProof.Case1Certificate

open Case1Data LPBridge

set_option maxRecDepth 32768
set_option maxHeartbeats 0

-- Exact rational witnesses. Each row is checked by kernel reduction;
-- no external evaluator or additional axiom supplies these equalities.
theorem penalty_row_0 : penaltyRow 0 = -5897294 := by decide +kernel

theorem penalty_row_1 : penaltyRow 1 = 0 := by decide +kernel

theorem penalty_row_2 : penaltyRow 2 = 0 := by decide +kernel

theorem penalty_row_3 : penaltyRow 3 = 0 := by decide +kernel

theorem penalty_row_4 : penaltyRow 4 = 0 := by decide +kernel

theorem penalty_row_5 : penaltyRow 5 = 0 := by decide +kernel

theorem penalty_row_6 : penaltyRow 6 = 0 := by decide +kernel

theorem penalty_row_7 : penaltyRow 7 = 0 := by decide +kernel

theorem penalty_row_8 : penaltyRow 8 = 0 := by decide +kernel

theorem penalty_row_9 : penaltyRow 9 = 0 := by decide +kernel

theorem penalty_row_10 : penaltyRow 10 = 0 := by decide +kernel

theorem penalty_row_11 : penaltyRow 11 = 0 := by decide +kernel

theorem penalty_row_12 : penaltyRow 12 = 0 := by decide +kernel

theorem penalty_row_13 : penaltyRow 13 = 0 := by decide +kernel

theorem penalty_row_14 : penaltyRow 14 = 0 := by decide +kernel

theorem penalty_row_15 : penaltyRow 15 = -2435304 := by decide +kernel

theorem penalty_row_16 : penaltyRow 16 = 0 := by decide +kernel

theorem penalty_row_17 : penaltyRow 17 = 0 := by decide +kernel

theorem penalty_row_18 : penaltyRow 18 = 0 := by decide +kernel

theorem penalty_row_19 : penaltyRow 19 = 0 := by decide +kernel

theorem penalty_row_20 : penaltyRow 20 = 0 := by decide +kernel

theorem penalty_row_21 : penaltyRow 21 = 0 := by decide +kernel

theorem penalty_row_22 : penaltyRow 22 = 0 := by decide +kernel

theorem penalty_row_23 : penaltyRow 23 = 0 := by decide +kernel

theorem penalty_row_24 : penaltyRow 24 = 0 := by decide +kernel

theorem penalty_row_25 : penaltyRow 25 = 0 := by decide +kernel

theorem penalty_row_26 : penaltyRow 26 = 0 := by decide +kernel

theorem penalty_row_27 : penaltyRow 27 = 0 := by decide +kernel

theorem penalty_row_28 : penaltyRow 28 = -8567454 := by decide +kernel

theorem penalty_row_29 : penaltyRow 29 = 0 := by decide +kernel

theorem penalty_row_30 : penaltyRow 30 = 0 := by decide +kernel

theorem penalty_row_31 : penaltyRow 31 = 0 := by decide +kernel

theorem penalty_row_32 : penaltyRow 32 = 0 := by decide +kernel

theorem penalty_row_33 : penaltyRow 33 = 0 := by decide +kernel

theorem penalty_row_34 : penaltyRow 34 = 0 := by decide +kernel

theorem penalty_row_35 : penaltyRow 35 = 0 := by decide +kernel

theorem penalty_row_36 : penaltyRow 36 = 0 := by decide +kernel

theorem penalty_row_37 : penaltyRow 37 = 0 := by decide +kernel

theorem penalty_row_38 : penaltyRow 38 = 0 := by decide +kernel

theorem penalty_row_39 : penaltyRow 39 = 0 := by decide +kernel

theorem penalty_row_40 : penaltyRow 40 = 0 := by decide +kernel

theorem penalty_row_41 : penaltyRow 41 = 0 := by decide +kernel

theorem penalty_row_42 : penaltyRow 42 = 0 := by decide +kernel

theorem penalty_row_43 : penaltyRow 43 = 0 := by decide +kernel

theorem penalty_row_44 : penaltyRow 44 = -599029 := by decide +kernel

theorem penalty_row_45 : penaltyRow 45 = -11533642 := by decide +kernel

theorem penalty_row_46 : penaltyRow 46 = -599029 := by decide +kernel

theorem penalty_row_47 : penaltyRow 47 = 0 := by decide +kernel

theorem penalty_row_48 : penaltyRow 48 = 0 := by decide +kernel

theorem penalty_row_49 : penaltyRow 49 = 0 := by decide +kernel

theorem penalty_row_50 : penaltyRow 50 = -5990755 := by decide +kernel

theorem penalty_row_51 : penaltyRow 51 = 0 := by decide +kernel

theorem penalty_row_52 : penaltyRow 52 = 0 := by decide +kernel

def rowValues : Node → ℚ :=
  ![-5897294,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    -2435304,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    -8567454,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    -599029,
    -11533642,
    -599029,
    0,
    0,
    0,
    -5990755,
    0,
    0]

theorem penalty_rows (i : Node) : penaltyRow i = rowValues i := by
  fin_cases i
  · exact penalty_row_0
  · exact penalty_row_1
  · exact penalty_row_2
  · exact penalty_row_3
  · exact penalty_row_4
  · exact penalty_row_5
  · exact penalty_row_6
  · exact penalty_row_7
  · exact penalty_row_8
  · exact penalty_row_9
  · exact penalty_row_10
  · exact penalty_row_11
  · exact penalty_row_12
  · exact penalty_row_13
  · exact penalty_row_14
  · exact penalty_row_15
  · exact penalty_row_16
  · exact penalty_row_17
  · exact penalty_row_18
  · exact penalty_row_19
  · exact penalty_row_20
  · exact penalty_row_21
  · exact penalty_row_22
  · exact penalty_row_23
  · exact penalty_row_24
  · exact penalty_row_25
  · exact penalty_row_26
  · exact penalty_row_27
  · exact penalty_row_28
  · exact penalty_row_29
  · exact penalty_row_30
  · exact penalty_row_31
  · exact penalty_row_32
  · exact penalty_row_33
  · exact penalty_row_34
  · exact penalty_row_35
  · exact penalty_row_36
  · exact penalty_row_37
  · exact penalty_row_38
  · exact penalty_row_39
  · exact penalty_row_40
  · exact penalty_row_41
  · exact penalty_row_42
  · exact penalty_row_43
  · exact penalty_row_44
  · exact penalty_row_45
  · exact penalty_row_46
  · exact penalty_row_47
  · exact penalty_row_48
  · exact penalty_row_49
  · exact penalty_row_50
  · exact penalty_row_51
  · exact penalty_row_52

theorem penalty_total : (∑ i : Node, penaltyRow i) = (-35622507 : ℚ) := by
  simp_rw [penalty_rows]
  decide +kernel

theorem degree_total :
    (∑ i : Node, (degreeDual (Sum.inl i) + degreeDual (Sum.inr i)) * prescribedDegree i) =
      (2164145799 : ℚ) / 2 := by decide +kernel

theorem cut_total : (∑ k : CutIndex, cutDual k) = (-111948712 : ℚ) := by decide +kernel

/-- The complete concrete certificate, in millionths of a kilometre. -/
theorem certificate_value : certificateBoundUnits = (2316798209 : ℚ) / 2 := by
  rw [certificate_decomposition, degree_total, cut_total, penalty_total]
  norm_num

theorem certificate_lower : (2316798209 : ℚ) / 2 ≤ certificateBoundUnits := by
  rw [certificate_value]

end UAVProof.Case1Certificate
