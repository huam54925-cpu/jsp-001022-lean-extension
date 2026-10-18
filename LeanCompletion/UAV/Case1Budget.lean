import LeanCompletion.UAV.Case1Distance

namespace UAVProof.Case1Budget

noncomputable section

open Case1Data Case1Distance

/-- Flight at 55 km/h plus exactly five minutes per inspection occurrence.
No service time is charged at the depot. Any additional nonnegative delays can
only make the nine-hour feasibility condition stronger. -/
def routeTimeHours (r : LegalRoute depot) : ℝ :=
  routeDistanceKm r / 55 + (r.visits.length : ℝ) / 12

theorem sum_visit_count (visits : List Node) :
    (∑ i : Node, visits.count i) = visits.length := by
  induction visits with
  | nil => simp
  | cons a rest ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

/-- Service count is derived from actual route lists and exact coverage. -/
theorem fleet_inspection_count {ι : Type*} (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i) :
    (∑ k ∈ ks, (routes k).visits.length) = 72 := by
  have htotal : ∀ i, totalVisitCount ks routes i = required i := by
    intro i
    by_cases hi : i = depot
    · subst i
      have hz : ∀ k, (routes k).visits.count depot = 0 :=
        fun k => List.count_eq_zero.mpr (routes k).depot_not_mem
      simp only [totalVisitCount, hz, Finset.sum_const_zero]
      rfl
    · exact hvisits i hi
  calc
    _ = ∑ k ∈ ks, ∑ i : Node, (routes k).visits.count i := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (sum_visit_count _).symm
    _ = ∑ i : Node, totalVisitCount ks routes i := by
      rw [Finset.sum_comm]
      rfl
    _ = 72 := by simp_rw [htotal]; exact inspection_count

/-- A budget for any finite active fleet, derived from each vehicle's time bound. -/
theorem fleet_distance_budget {ι : Type*} (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (htime : ∀ k ∈ ks, routeTimeHours (routes k) ≤ 9) :
    fleetDistanceKm ks routes ≤ 55 * (9 * (ks.card : ℝ) - 6) := by
  have hcount : (∑ k ∈ ks, ((routes k).visits.length : ℝ)) = 72 := by
    exact_mod_cast fleet_inspection_count ks routes hvisits
  have hsum := Finset.sum_le_sum htime
  have hservice : (∑ k ∈ ks, ((routes k).visits.length : ℝ) / 12) = 6 := by
    rw [← Finset.sum_div, hcount]
    norm_num
  have hflight : (∑ k ∈ ks, routeDistanceKm (routes k) / 55) =
      fleetDistanceKm ks routes / 55 := by rw [← Finset.sum_div]; rfl
  simp only [routeTimeHours, Finset.sum_add_distrib, hservice, hflight,
    Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

/-- The physical upper budget also covers fewer than three active routes.
This does not extend the three-route dual certificate to smaller fleets. -/
theorem at_most_three_distance_budget {ι : Type*} (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (htime : ∀ k ∈ ks, routeTimeHours (routes k) ≤ 9) (hcard : ks.card ≤ 3) :
    fleetDistanceKm ks routes ≤ 1155 := by
  have hb := fleet_distance_budget ks routes hvisits htime
  have hc : (ks.card : ℝ) ≤ 3 := by exact_mod_cast hcard
  linarith

theorem three_routes_distance_budget (routes : Vehicle → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount Finset.univ routes i = required i)
    (htime : ∀ k, routeTimeHours (routes k) ≤ 9) :
    fleetDistanceKm Finset.univ routes ≤ 1155 :=
  at_most_three_distance_budget Finset.univ routes hvisits (fun k _ => htime k) (by decide)

/-- Pure arithmetic only: both distance inequalities are premises, in millionths of km. -/
theorem case1_distance_budget_contradiction (D : ℚ)
    (hlower : (2316798209 : ℚ) / 2 ≤ D)
    (hupper : D ≤ 1155 * 1000000) : False := by
  linarith

/-- A complete conditional structural chain. The concrete certificate's numerical
lower bound is the one outstanding premise; it is not proved or asserted as an axiom. -/
theorem three_routes_infeasible_of_certificate
    (hcertificate : (2316798209 : ℚ) / 2 ≤ certificateBoundUnits)
    (routes : Vehicle → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount Finset.univ routes i = required i)
    (htime : ∀ k, routeTimeHours (routes k) ≤ 9) : False := by
  have hupper := three_routes_distance_budget routes hvisits htime
  have hphysical := routeCost_km_le_fleetDistance Finset.univ routes
  have hcost : LPBridge.routeCost Finset.univ routes costUnits ≤ (1155 : ℚ) * 1000000 := by
    have hr : (LPBridge.routeCost Finset.univ routes costUnits : ℝ) ≤ 1155 * 1000000 := by
      linarith
    exact_mod_cast hr
  exact case1_distance_budget_contradiction _
    (hcertificate.trans (three_routes_weak_duality routes hvisits)) hcost

end
end UAVProof.Case1Budget
