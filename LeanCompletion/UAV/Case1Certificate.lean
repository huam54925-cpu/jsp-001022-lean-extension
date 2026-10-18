import LeanCompletion.UAV.Case1Data

namespace UAVProof.Case1Certificate

open Case1Data LPBridge

set_option maxRecDepth 16384
set_option maxHeartbeats 0

def residual (e : Node × Node) : ℚ :=
  costUnits e - (degreeDual (Sum.inl e.1) + degreeDual (Sum.inr e.2)) +
    ∑ k : CutIndex, cutDual k * cutMatrix (cuts k) e

def penaltyRow (i : Node) : ℚ :=
  ∑ j : Node, if i = j then 0 else capacity prescribedDegree (i, j) * min 0 (residual (i, j))

theorem degree_sum (e : Node × Node) :
    (∑ h : Node ⊕ Node, degreeDual h * eqMatrix h e) =
      degreeDual (Sum.inl e.1) + degreeDual (Sum.inr e.2) := by
  simp [Fintype.sum_sum_type, eqMatrix]

theorem certificate_decomposition : certificateBoundUnits =
    (∑ i : Node, (degreeDual (Sum.inl i) + degreeDual (Sum.inr i)) * prescribedDegree i) -
      (∑ k : CutIndex, cutDual k) + ∑ i : Node, penaltyRow i := by
  unfold certificateBoundUnits certifiedBound
  simp_rw [degree_sum]
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  simp only [rhs, ← add_mul]
  congr 1
  simp only [arcSet, Finset.sum_filter, Fintype.sum_prod_type, penaltyRow, residual]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i = j <;> simp [h]

end UAVProof.Case1Certificate
