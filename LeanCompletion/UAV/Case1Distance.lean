import LeanCompletion.UAV.Case1Data

namespace UAVProof

/-- Integer square-root costs in millionths of a kilometre are conservative.
This proof is uniform in the squared coordinate distance and does not enumerate arcs. -/
theorem scaled_nat_sqrt_le_real (s : ℕ) :
    (Nat.sqrt (s * 10000000000) : ℝ) ≤ 100000 * Real.sqrt (s : ℝ) := by
  have hsq : (Nat.sqrt (s * 10000000000) : ℝ) ^ 2 ≤ (s : ℝ) * 10000000000 := by
    exact_mod_cast Nat.sqrt_le' (s * 10000000000)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg s)]

namespace Case1Distance

noncomputable section

open Case1Data

/-- Squared Euclidean distance in the original coordinate units, interpreted in ℝ. -/
def coordinateDistanceSq (e : Node × Node) : ℝ :=
  (((coordinates e.1).1 : ℝ) - ((coordinates e.2).1 : ℝ)) ^ 2 +
  (((coordinates e.1).2 : ℝ) - ((coordinates e.2).2 : ℝ)) ^ 2

/-- One coordinate unit is 0.1 kilometre. -/
def distanceKm (e : Node × Node) : ℝ := Real.sqrt (coordinateDistanceSq e) / 10

theorem squaredDistance_cast (e : Node × Node) :
    (squaredDistance e : ℝ) = coordinateDistanceSq e := by
  have hn : 0 ≤ ((coordinates e.1).1 - (coordinates e.2).1) ^ 2 +
      ((coordinates e.1).2 - (coordinates e.2).2) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hi : (squaredDistance e : ℤ) =
      ((coordinates e.1).1 - (coordinates e.2).1) ^ 2 +
      ((coordinates e.1).2 - (coordinates e.2).2) ^ 2 := Int.toNat_of_nonneg hn
  dsimp [coordinateDistanceSq]
  exact_mod_cast hi

theorem distanceKm_nonneg (e : Node × Node) : 0 ≤ distanceKm e := by
  unfold distanceKm
  positivity

/-- Applies to all ordered pairs, including the unused diagonal pairs. -/
theorem costUnits_km_le_distance (e : Node × Node) :
    (costUnits e : ℝ) / 1000000 ≤ distanceKm e := by
  have h := scaled_nat_sqrt_le_real (squaredDistance e)
  rw [squaredDistance_cast] at h
  simpa only [costUnits, Rat.cast_natCast, distanceKm] using
    (show (Nat.sqrt (squaredDistance e * 10000000000) : ℝ) / 1000000 ≤
      Real.sqrt (coordinateDistanceSq e) / 10 by linarith)

/-- Every traversal is counted, including repeated traversals of the same arc. -/
def routeDistanceKm (r : LegalRoute depot) : ℝ :=
  ∑ e : Node × Node, distanceKm e * (routeFlow r.vertices e.1 e.2 : ℝ)

def fleetDistanceKm {ι : Type*} (ks : Finset ι) (routes : ι → LegalRoute depot) : ℝ :=
  ∑ k ∈ ks, routeDistanceKm (routes k)

/-- The rational route objective, converted to kilometres, bounds actual geometric distance. -/
theorem routeCost_km_le_fleetDistance {ι : Type*} (ks : Finset ι)
    (routes : ι → LegalRoute depot) :
    (LPBridge.routeCost ks routes costUnits : ℝ) / 1000000 ≤ fleetDistanceKm ks routes := by
  simp only [LPBridge.routeCost, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
    Finset.sum_div, fleetDistanceKm, routeDistanceKm]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro e he
  have h := mul_le_mul_of_nonneg_right (costUnits_km_le_distance e)
    (Nat.cast_nonneg (routeFlow (routes k).vertices e.1 e.2) :
      (0 : ℝ) ≤ (routeFlow (routes k).vertices e.1 e.2 : ℝ))
  simpa only [div_mul_eq_mul_div] using h

/-- The fixed certificate expression is now connected to physical distance, without
assuming or evaluating its numerical value. -/
theorem three_routes_certificate_le_distance (routes : Vehicle → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount Finset.univ routes i = required i) :
    (certificateBoundUnits : ℝ) / 1000000 ≤ fleetDistanceKm Finset.univ routes := by
  have hq := three_routes_weak_duality routes hvisits
  have hr : (certificateBoundUnits : ℝ) ≤ (LPBridge.routeCost Finset.univ routes costUnits : ℝ) := by
    exact_mod_cast hq
  exact (div_le_div_of_nonneg_right hr (by norm_num)).trans
    (routeCost_km_le_fleetDistance Finset.univ routes)

end
end Case1Distance
end UAVProof
