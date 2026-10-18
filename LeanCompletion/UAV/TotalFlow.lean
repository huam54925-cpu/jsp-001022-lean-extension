import LeanCompletion.UAV.RouteToFlow

namespace UAVProof

variable {V ι : Type*} {depot : V} [DecidableEq V]

/-- Aggregate by vehicle identifiers, so identical routes of different vehicles
are counted separately. Only identifiers in `ks` contribute. -/
def totalRouteFlow (ks : Finset ι) (routes : ι → LegalRoute depot) (i j : V) : ℕ :=
  ∑ k ∈ ks, routeFlow (routes k).vertices i j

/-- Actual inspection multiplicity across the selected vehicles. -/
def totalVisitCount (ks : Finset ι) (routes : ι → LegalRoute depot) (i : V) : ℕ :=
  ∑ k ∈ ks, (routes k).visits.count i

/-- Prescribed degree: fleet size at the depot, required visits elsewhere.
The supplied visit requirement at the depot is intentionally irrelevant. -/
def fleetDegree (ks : Finset ι) (depot : V) (required : V → ℕ) (i : V) : ℕ :=
  if i = depot then ks.card else required i

/-- Legality of each route proves that the aggregate has no diagonal arcs. -/
theorem total_no_diagonal (ks : Finset ι) (routes : ι → LegalRoute depot) (i : V) :
    totalRouteFlow ks routes i i = 0 := by
  simp [totalRouteFlow, LegalRoute.routeFlow_self_eq_zero]

variable [Fintype V]

/-- Outgoing flow commutes with summation over vehicle identifiers. -/
theorem total_outFlow_eq_sum (ks : Finset ι) (routes : ι → LegalRoute depot) (i : V) :
    outFlow Finset.univ (totalRouteFlow ks routes) i =
      ∑ k ∈ ks, outFlow Finset.univ (routeFlow (routes k).vertices) i := by
  simp only [outFlow, totalRouteFlow]
  rw [Finset.sum_comm]

/-- Incoming flow commutes with summation over vehicle identifiers. -/
theorem total_inFlow_eq_sum (ks : Finset ι) (routes : ι → LegalRoute depot) (i : V) :
    inFlow Finset.univ (totalRouteFlow ks routes) i =
      ∑ k ∈ ks, inFlow Finset.univ (routeFlow (routes k).vertices) i := by
  simp only [inFlow, totalRouteFlow]
  rw [Finset.sum_comm]

/-- The aggregate outgoing degree is derived from the individual legal routes. -/
theorem total_outFlow_eq_sum_degree (ks : Finset ι)
    (routes : ι → LegalRoute depot) (i : V) :
    outFlow Finset.univ (totalRouteFlow ks routes) i =
      ∑ k ∈ ks, (routes k).degree i := by
  simp only [total_outFlow_eq_sum, LegalRoute.outFlow_eq_degree]

/-- The aggregate incoming degree is the same sum of single-route degrees. -/
theorem total_inFlow_eq_sum_degree (ks : Finset ι)
    (routes : ι → LegalRoute depot) (i : V) :
    inFlow Finset.univ (totalRouteFlow ks routes) i =
      ∑ k ∈ ks, (routes k).degree i := by
  simp only [total_inFlow_eq_sum, LegalRoute.inFlow_eq_degree]

/-- Every finite fleet of legal routes conserves flow at every vertex. -/
theorem total_flow_balance (ks : Finset ι) (routes : ι → LegalRoute depot) (i : V) :
    outFlow Finset.univ (totalRouteFlow ks routes) i =
      inFlow Finset.univ (totalRouteFlow ks routes) i := by
  rw [total_outFlow_eq_sum_degree, total_inFlow_eq_sum_degree]

/-- Away from the depot, outgoing flow counts actual inspection visits. -/
theorem total_outFlow_eq_visit_count (ks : Finset ι)
    (routes : ι → LegalRoute depot) (i : V) (hi : i ≠ depot) :
    outFlow Finset.univ (totalRouteFlow ks routes) i = totalVisitCount ks routes i := by
  simp only [total_outFlow_eq_sum, LegalRoute.outFlow_eq_visit_count _ i hi,
    totalVisitCount]

/-- Away from the depot, incoming flow counts the same actual inspection visits. -/
theorem total_inFlow_eq_visit_count (ks : Finset ι)
    (routes : ι → LegalRoute depot) (i : V) (hi : i ≠ depot) :
    inFlow Finset.univ (totalRouteFlow ks routes) i = totalVisitCount ks routes i := by
  simp only [total_inFlow_eq_sum, LegalRoute.inFlow_eq_visit_count _ i hi,
    totalVisitCount]

/-- Each selected nonempty mission contributes exactly one depot departure. -/
theorem total_outFlow_depot_eq_card (ks : Finset ι) (routes : ι → LegalRoute depot) :
    outFlow Finset.univ (totalRouteFlow ks routes) depot = ks.card := by
  simp [total_outFlow_eq_sum, LegalRoute.outFlow_depot_eq_one]

/-- Each selected nonempty mission contributes exactly one depot return. -/
theorem total_inFlow_depot_eq_card (ks : Finset ι) (routes : ι → LegalRoute depot) :
    inFlow Finset.univ (totalRouteFlow ks routes) depot = ks.card := by
  simp [total_inFlow_eq_sum, LegalRoute.inFlow_depot_eq_one]

/-- Exact coverage of the required inspections implies the prescribed outgoing degrees. -/
theorem total_outFlow_eq_fleetDegree (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i) (i : V) :
    outFlow Finset.univ (totalRouteFlow ks routes) i = fleetDegree ks depot required i := by
  by_cases hi : i = depot
  · subst i
    simp [fleetDegree, total_outFlow_depot_eq_card]
  · rw [total_outFlow_eq_visit_count ks routes i hi, hvisits i hi]
    simp [fleetDegree, hi]

/-- Exact coverage implies the prescribed incoming degrees as well. -/
theorem total_inFlow_eq_fleetDegree (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i) (i : V) :
    inFlow Finset.univ (totalRouteFlow ks routes) i = fleetDegree ks depot required i := by
  rw [← total_flow_balance ks routes i]
  exact total_outFlow_eq_fleetDegree ks routes required hvisits i

omit [DecidableEq V] in
/-- For any natural-valued flow with the given degrees, each arc is bounded
by both endpoint degrees. This lemma does not assume a route decomposition. -/
theorem flow_bounds_of_degrees (x : V → V → ℕ) (b : V → ℕ)
    (hout : ∀ i, outFlow Finset.univ x i = b i)
    (hin : ∀ i, inFlow Finset.univ x i = b i) (i j : V) :
    0 ≤ x i j ∧ x i j ≤ min (b i) (b j) := by
  have hi : x i j ≤ outFlow Finset.univ x i :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (x i k)) (Finset.mem_univ j)
  have hj : x i j ≤ inFlow Finset.univ x j :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (x k j)) (Finset.mem_univ i)
  rw [hout i] at hi
  rw [hin j] at hj
  exact ⟨Nat.zero_le _, le_min hi hj⟩

/-- Legal routes and exact inspection coverage yield the required arc capacities. -/
theorem total_routeFlow_bounds (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i) (i j : V) :
    0 ≤ totalRouteFlow ks routes i j ∧
      totalRouteFlow ks routes i j ≤
        min (fleetDegree ks depot required i) (fleetDegree ks depot required j) := by
  exact flow_bounds_of_degrees (totalRouteFlow ks routes) (fleetDegree ks depot required)
    (total_outFlow_eq_fleetDegree ks routes required hvisits)
    (total_inFlow_eq_fleetDegree ks routes required hvisits) i j

/-- The degree, diagonal, and capacity constraints derived from a finite legal fleet.
Coverage is a statement about inspection lists, not an assumed edge-flow constraint.
Connectivity cuts and numerical certificate evaluation are not included. -/
theorem totalFlow_constraints (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i) :
    (∀ i, outFlow Finset.univ (totalRouteFlow ks routes) i = fleetDegree ks depot required i) ∧
    (∀ i, inFlow Finset.univ (totalRouteFlow ks routes) i = fleetDegree ks depot required i) ∧
    (∀ i, totalRouteFlow ks routes i i = 0) ∧
    (∀ i j, 0 ≤ totalRouteFlow ks routes i j ∧
      totalRouteFlow ks routes i j ≤
        min (fleetDegree ks depot required i) (fleetDegree ks depot required j)) := by
  exact ⟨total_outFlow_eq_fleetDegree ks routes required hvisits,
    total_inFlow_eq_fleetDegree ks routes required hvisits,
    total_no_diagonal ks routes, total_routeFlow_bounds ks routes required hvisits⟩

end UAVProof
