import LeanCompletion.UAV.TotalFlow

namespace UAVProof

variable {V ι : Type*}

/-- A finite route that visits a set and ends outside it has an outgoing edge.
The starting vertex need not be outside the set. No route-legality assumption is needed. -/
theorem route_exit_exists (route : List V) (S : Set V) (last : V)
    (hlast : route.getLast? = some last) (houtside : last ∉ S)
    (hvisit : ∃ v ∈ route, v ∈ S) :
    ∃ i j, (i, j) ∈ route.zip route.tail ∧ i ∈ S ∧ j ∉ S := by
  classical
  induction route with
  | nil => simp at hvisit
  | cons a rest ih =>
      cases rest with
      | nil =>
          have halast : a = last := by simpa using hlast
          obtain ⟨v, hv, hvS⟩ := hvisit
          have hva : v = a := by simpa using hv
          exact False.elim (houtside (hva.trans halast ▸ hvS))
      | cons b tail =>
          have hlast' : (b :: tail).getLast? = some last := by simpa using hlast
          by_cases htail : ∃ v ∈ b :: tail, v ∈ S
          · obtain ⟨i, j, hedge, hi, hj⟩ := ih hlast' htail
            refine ⟨i, j, ?_, hi, hj⟩
            simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inr hedge
          · have ha : a ∈ S := by
              obtain ⟨v, hv, hvS⟩ := hvisit
              rcases List.mem_cons.mp hv with hva | hvrest
              · exact hva ▸ hvS
              · exact False.elim (htail ⟨v, hvrest, hvS⟩)
            have hb : b ∉ S := fun hb => htail ⟨b, by simp, hb⟩
            exact ⟨a, b, by simp, ha, hb⟩

variable [DecidableEq V]

/-- The witnessed exit edge occurs at least once in the natural-valued route flow. -/
theorem route_exit_flow_pos (route : List V) (S : Finset V) (last : V)
    (hlast : route.getLast? = some last) (houtside : last ∉ S)
    (hvisit : ∃ v ∈ route, v ∈ S) :
    ∃ i ∈ S, ∃ j, j ∉ S ∧ 1 ≤ routeFlow route i j := by
  obtain ⟨i, j, hedge, hi, hj⟩ := route_exit_exists route (↑S) last hlast houtside hvisit
  exact ⟨i, hi, j, hj, List.count_pos_iff.mpr hedge⟩

variable [Fintype V]

/-- Total outgoing cut flow, counting only arcs from `S` to its complement. -/
def outCutFlow (S : Finset V) (x : V → V → ℕ) : ℕ :=
  ∑ i ∈ S, ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), x i j

/-- Each nonnegative arc crossing the cut is bounded by the entire cut flow. -/
theorem arc_le_outCutFlow (S : Finset V) (x : V → V → ℕ)
    {i j : V} (hi : i ∈ S) (hj : j ∉ S) : x i j ≤ outCutFlow S x := by
  have hinner : x i j ≤ ∑ b ∈ Finset.univ.filter (fun b => b ∉ S), x i b :=
    Finset.single_le_sum (fun b _ => Nat.zero_le (x i b)) (by simp [hj])
  have houter : (∑ b ∈ Finset.univ.filter (fun b => b ∉ S), x i b) ≤ outCutFlow S x :=
    Finset.single_le_sum
      (fun a _ => Nat.zero_le (∑ b ∈ Finset.univ.filter (fun b => b ∉ S), x a b)) hi
  exact hinner.trans houter

/-- A legal depot route visiting a depot-free set sends at least one unit out of it. -/
theorem LegalRoute.outCutFlow_ge_one {depot : V} (r : LegalRoute depot)
    (S : Finset V) (hdepot : depot ∉ S) (hvisit : ∃ v ∈ r.visits, v ∈ S) :
    1 ≤ outCutFlow S (routeFlow r.vertices) := by
  have hlast : r.vertices.getLast? = some depot := by
    rw [← r.closed]
    rfl
  have hvisit' : ∃ v ∈ r.vertices, v ∈ S := by
    obtain ⟨v, hv, hvS⟩ := hvisit
    exact ⟨v, by simp [LegalRoute.vertices, depotRoute, hv], hvS⟩
  obtain ⟨i, hi, j, hj, hflow⟩ := route_exit_flow_pos r.vertices S depot hlast hdepot hvisit'
  exact hflow.trans (arc_le_outCutFlow S (routeFlow r.vertices) hi hj)

/-- One selected route visiting the set suffices for the finite fleet cut lower bound. -/
theorem total_outCutFlow_ge_one_of_visit {depot : V} (ks : Finset ι)
    (routes : ι → LegalRoute depot) (S : Finset V) (hdepot : depot ∉ S)
    (hvisit : ∃ k ∈ ks, ∃ v ∈ (routes k).visits, v ∈ S) :
    1 ≤ outCutFlow S (totalRouteFlow ks routes) := by
  obtain ⟨k, hk, hv⟩ := hvisit
  have hmono : outCutFlow S (routeFlow (routes k).vertices) ≤
      outCutFlow S (totalRouteFlow ks routes) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact Finset.single_le_sum (fun a _ => Nat.zero_le (routeFlow (routes a).vertices i j)) hk
  exact ((routes k).outCutFlow_ge_one S hdepot hv).trans hmono

/-- Positive actual inspection count at one vertex in the set supplies a visiting route. -/
theorem total_outCutFlow_ge_one_of_positive_visit {depot : V} (ks : Finset ι)
    (routes : ι → LegalRoute depot) (S : Finset V) (hdepot : depot ∉ S)
    (hpositive : ∃ v ∈ S, 0 < totalVisitCount ks routes v) :
    1 ≤ outCutFlow S (totalRouteFlow ks routes) := by
  obtain ⟨v, hvS, hv⟩ := hpositive
  obtain ⟨k, hk, hcount⟩ := Finset.sum_pos_iff.mp hv
  exact total_outCutFlow_ge_one_of_visit ks routes S hdepot
    ⟨k, hk, v, List.count_pos_iff.mp hcount, hvS⟩

/-- Exact inspection coverage and positive requirements on a nonempty depot-free
set imply its outgoing cut constraint. No cut constraint is assumed as a premise. -/
theorem total_outCutFlow_ge_one {depot : V} (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (S : Finset V) (hne : S.Nonempty) (hdepot : depot ∉ S)
    (hpositive : ∀ i ∈ S, 0 < required i) :
    1 ≤ outCutFlow S (totalRouteFlow ks routes) := by
  obtain ⟨i, hi⟩ := hne
  have hidepot : i ≠ depot := fun h => hdepot (h ▸ hi)
  apply total_outCutFlow_ge_one_of_positive_visit ks routes S hdepot
  refine ⟨i, hi, ?_⟩
  rw [hvisits i hidepot]
  exact hpositive i hi

end UAVProof
