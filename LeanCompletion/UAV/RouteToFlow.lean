import LeanCompletion.UAV.Flow

namespace UAVProof

variable {V : Type*}

/-- A route starts at the depot, performs its visits, and returns to the depot. -/
def depotRoute (depot : V) (visits : List V) : List V :=
  (depot :: visits) ++ [depot]

/-- A nonempty mission with no intermediate depot visit or equal adjacent vertices.
Only adjacent vertices must differ: repeated visits such as `a, b, a` are allowed. -/
structure LegalRoute (depot : V) where
  visits : List V
  visits_nonempty : visits ≠ []
  depot_not_mem : depot ∉ visits
  adjacent_ne : (depotRoute depot visits).IsChain (· ≠ ·)

/-- Every edge of a route with unequal adjacent vertices has distinct endpoints. -/
theorem route_edge_ne_of_isChain {route : List V}
    (hchain : route.IsChain (· ≠ ·)) {i j : V}
    (hedge : (i, j) ∈ route.zip route.tail) : i ≠ j := by
  induction route with
  | nil => simp at hedge
  | cons a rest ih =>
      cases rest with
      | nil => simp at hedge
      | cons b tail =>
          obtain ⟨hab, hrest⟩ := List.isChain_cons_cons.mp hchain
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hedge
          rcases hedge with heq | hedge
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            exact hab
          · exact ih hrest hedge

namespace LegalRoute

variable {depot : V}

/-- The complete vertex sequence, including both depot endpoints. -/
def vertices (r : LegalRoute depot) : List V :=
  depotRoute depot r.visits

/-- Every legal route satisfies the closed-route hypothesis from `Flow.lean`. -/
theorem closed (r : LegalRoute depot) :
    r.vertices.head? = r.vertices.getLast? := by
  change ((depot :: r.visits) ++ [depot]).head? =
    ((depot :: r.visits) ++ [depot]).getLast?
  rw [List.getLast?_append]
  rfl

variable [DecidableEq V] [Fintype V]

/-- Targets of consecutive edges are exactly the visits followed by the return depot. -/
theorem inFlow_eq_visits_add_depot (r : LegalRoute depot) (i : V) :
    inFlow Finset.univ (routeFlow r.vertices) i =
      r.visits.count i + (if depot = i then 1 else 0) := by
  have hlength : r.vertices.tail.length ≤ r.vertices.length := by simp
  rw [inFlow_eq_target_count, List.map_snd_zip hlength]
  simp [vertices, depotRoute, List.count_append, List.count_cons]

/-- At a non-depot inspection point, incoming flow counts all visits, including repeats. -/
theorem inFlow_eq_visit_count (r : LegalRoute depot) (i : V) (hi : i ≠ depot) :
    inFlow Finset.univ (routeFlow r.vertices) i = r.visits.count i := by
  simp [inFlow_eq_visits_add_depot, Ne.symm hi]

/-- The same visit count is the outgoing flow, by closed-route conservation. -/
theorem outFlow_eq_visit_count (r : LegalRoute depot) (i : V) (hi : i ≠ depot) :
    outFlow Finset.univ (routeFlow r.vertices) i = r.visits.count i := by
  rw [closed_route_flow_balance r.vertices r.closed i]
  exact r.inFlow_eq_visit_count i hi

/-- A legal route returns to the depot exactly once. -/
theorem inFlow_depot_eq_one (r : LegalRoute depot) :
    inFlow Finset.univ (routeFlow r.vertices) depot = 1 := by
  simp [inFlow_eq_visits_add_depot, List.count_eq_zero.mpr r.depot_not_mem]

/-- A legal route leaves the depot exactly once. -/
theorem outFlow_depot_eq_one (r : LegalRoute depot) :
    outFlow Finset.univ (routeFlow r.vertices) depot = 1 := by
  rw [closed_route_flow_balance r.vertices r.closed depot]
  exact r.inFlow_depot_eq_one

omit [Fintype V] in
/-- A legal route traverses no self-loop. This does not require a finite vertex type. -/
theorem routeFlow_self_eq_zero (r : LegalRoute depot) (i : V) :
    routeFlow r.vertices i i = 0 := by
  apply List.count_eq_zero.mpr
  intro hedge
  exact (route_edge_ne_of_isChain r.adjacent_ne hedge) rfl

/-- The single-route degree budget: one at the depot, visit multiplicity elsewhere. -/
def degree (r : LegalRoute depot) (i : V) : ℕ :=
  if i = depot then 1 else r.visits.count i

/-- The degree budget is the actual incoming flow, not an assumed flow constraint. -/
theorem inFlow_eq_degree (r : LegalRoute depot) (i : V) :
    inFlow Finset.univ (routeFlow r.vertices) i = r.degree i := by
  by_cases hi : i = depot
  · subst i
    simp [degree, r.inFlow_depot_eq_one]
  · simp [degree, hi, r.inFlow_eq_visit_count i hi]

/-- Closed-route conservation identifies the same budget with outgoing flow. -/
theorem outFlow_eq_degree (r : LegalRoute depot) (i : V) :
    outFlow Finset.univ (routeFlow r.vertices) i = r.degree i := by
  rw [closed_route_flow_balance r.vertices r.closed i]
  exact r.inFlow_eq_degree i

/-- An individual arc count is bounded by both endpoint degrees.
This also covers depot edges, repeated traversals, and zero-visit vertices. -/
theorem routeFlow_bounds (r : LegalRoute depot) (i j : V) :
    0 ≤ routeFlow r.vertices i j ∧
      routeFlow r.vertices i j ≤ min (r.degree i) (r.degree j) := by
  have hout : routeFlow r.vertices i j ≤
      outFlow Finset.univ (routeFlow r.vertices) i := by
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (routeFlow r.vertices i k))
      (Finset.mem_univ j)
  have hin : routeFlow r.vertices i j ≤
      inFlow Finset.univ (routeFlow r.vertices) j := by
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (routeFlow r.vertices k j))
      (Finset.mem_univ i)
  rw [r.outFlow_eq_degree i] at hout
  rw [r.inFlow_eq_degree j] at hin
  exact ⟨Nat.zero_le _, le_min hout hin⟩

end LegalRoute

end UAVProof
