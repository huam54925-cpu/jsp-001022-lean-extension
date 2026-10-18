import LeanCompletion.UAV.TotalFlow
import LeanCompletion.UAV.Connectivity
import LeanCompletion.UAV.WeakDuality

namespace UAVProof.LPBridge

variable {V ι κ : Type*} [DecidableEq V] [Fintype V]

/-- LP variables are ordered vertex pairs in this finite set; diagonal pairs are excluded. -/
def arcSet : Finset (V × V) :=
  Finset.univ.filter (fun e => e.1 ≠ e.2)

/-- Natural-valued edge multiplicities embedded into the rationals. -/
def flow (x : V → V → ℕ) (e : V × V) : ℚ :=
  x e.1 e.2

/-- The endpoint-degree upper bound, in the same rational units as the LP variables. -/
def capacity (b : V → ℕ) (e : V × V) : ℚ :=
  min (b e.1) (b e.2)

/-- Left rows impose outgoing degrees; right rows impose incoming degrees. -/
def eqMatrix : V ⊕ V → (V × V) → ℚ
  | Sum.inl i, e => if e.1 = i then 1 else 0
  | Sum.inr i, e => if e.2 = i then 1 else 0

/-- Both degree-row families use the same prescribed vertex degree. -/
def rhs (b : V → ℕ) : V ⊕ V → ℚ
  | Sum.inl i => b i
  | Sum.inr i => b i

/-- A cut row selects exactly the arcs leaving the specified vertex set. -/
def cutMatrix (S : Finset V) (e : V × V) : ℚ :=
  if e.1 ∈ S ∧ e.2 ∉ S then 1 else 0

/-- A valid cut excludes the depot and contains at least one positive-demand vertex.
The witness also ensures nonemptiness; not every vertex of the cut needs positive demand. -/
def ValidCut (depot : V) (required : V → ℕ) (S : Finset V) : Prop :=
  depot ∉ S ∧ ∃ i ∈ S, 0 < required i

/-- Removing diagonal terms loses nothing when their contributions are zero. -/
theorem sum_arcSet_eq_univ (f : (V × V) → ℚ) (hdiag : ∀ i, f (i, i) = 0) :
    (∑ e ∈ arcSet (V := V), f e) = ∑ e : V × V, f e := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  rintro ⟨i, j⟩ _ hnot
  have hij : i = j := by simpa [arcSet] using hnot
  subst j
  exact hdiag i

/-- The outgoing matrix row is the rational cast of the original natural outflow. -/
theorem eqMatrix_out_sum (x : V → V → ℕ) (hdiag : ∀ i, x i i = 0) (i : V) :
    (∑ e ∈ arcSet (V := V), eqMatrix (Sum.inl i) e * flow x e) =
      (outFlow Finset.univ x i : ℚ) := by
  rw [sum_arcSet_eq_univ _ (by intro j; simp [flow, hdiag])]
  rw [Fintype.sum_prod_type]
  simp [eqMatrix, flow, ite_mul, Finset.sum_ite_irrel, outFlow]

/-- The incoming matrix row is the rational cast of the original natural inflow. -/
theorem eqMatrix_in_sum (x : V → V → ℕ) (hdiag : ∀ i, x i i = 0) (i : V) :
    (∑ e ∈ arcSet (V := V), eqMatrix (Sum.inr i) e * flow x e) =
      (inFlow Finset.univ x i : ℚ) := by
  rw [sum_arcSet_eq_univ _ (by intro j; simp [flow, hdiag])]
  rw [Fintype.sum_prod_type]
  simp [eqMatrix, flow, ite_mul, inFlow]

/-- Cut-matrix sums coincide with the rational cast of the natural outgoing cut flow.
Even without a zero-diagonal assumption, no diagonal arc can cross a cut. -/
theorem cutMatrix_sum (S : Finset V) (x : V → V → ℕ) :
    (∑ e ∈ arcSet (V := V), cutMatrix S e * flow x e) = (outCutFlow S x : ℚ) := by
  rw [sum_arcSet_eq_univ _ (by intro i; simp [cutMatrix])]
  rw [Fintype.sum_prod_type]
  simp [cutMatrix, flow, outCutFlow, Finset.sum_filter, ite_mul, ite_and,
    Finset.sum_ite_irrel]

/-- The variable bounds survive the natural-to-rational embedding. -/
theorem legalFleet_variable_bounds {depot : V} (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i) (e : V × V) :
    0 ≤ flow (totalRouteFlow ks routes) e ∧
      flow (totalRouteFlow ks routes) e ≤ capacity (fleetDegree ks depot required) e := by
  constructor
  · exact Nat.cast_nonneg _
  · dsimp [flow, capacity]
    exact_mod_cast (total_routeFlow_bounds ks routes required hvisits e.1 e.2).2

/-- Both families of rational degree constraints are derived from legal route coverage. -/
theorem legalFleet_degree_rows {depot : V} (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i) (h : V ⊕ V) :
    (∑ e ∈ arcSet (V := V), eqMatrix h e * flow (totalRouteFlow ks routes) e) =
      rhs (fleetDegree ks depot required) h := by
  cases h with
  | inl i =>
      rw [eqMatrix_out_sum _ (total_no_diagonal ks routes),
        total_outFlow_eq_fleetDegree ks routes required hvisits]
      rfl
  | inr i =>
      rw [eqMatrix_in_sum _ (total_no_diagonal ks routes),
        total_inFlow_eq_fleetDegree ks routes required hvisits]
      rfl

/-- A valid cut yields a rational LP cut constraint through the proved connectivity theorem. -/
theorem legalFleet_cut_row {depot : V} (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (S : Finset V) (hvalid : ValidCut depot required S) :
    1 ≤ ∑ e ∈ arcSet (V := V), cutMatrix S e * flow (totalRouteFlow ks routes) e := by
  rw [cutMatrix_sum]
  obtain ⟨hdepot, i, hi, hpos⟩ := hvalid
  have hidepot : i ≠ depot := fun h => hdepot (h ▸ hi)
  have hnat := total_outCutFlow_ge_one_of_positive_visit ks routes S hdepot
    ⟨i, hi, by rw [hvisits i hidepot]; exact hpos⟩
  exact_mod_cast hnat

/-- Actual fleet cost: each vehicle pays for every occurrence of each directed edge.
The cost coefficients are abstract rationals; no Euclidean or Case1 numerical data is assumed. -/
def routeCost {depot : V} (ks : Finset ι) (routes : ι → LegalRoute depot)
    (cost : (V × V) → ℚ) : ℚ :=
  ∑ k ∈ ks, ∑ e : V × V, cost e * (routeFlow (routes k).vertices e.1 e.2 : ℚ)

/-- The non-diagonal LP objective equals the sum of the individual route costs. -/
theorem objective_eq_routeCost {depot : V} (ks : Finset ι)
    (routes : ι → LegalRoute depot) (cost : (V × V) → ℚ) :
    (∑ e ∈ arcSet (V := V), cost e * flow (totalRouteFlow ks routes) e) =
      routeCost ks routes cost := by
  rw [sum_arcSet_eq_univ _ (by intro i; simp [flow, total_no_diagonal])]
  simp only [flow, totalRouteFlow, Nat.cast_sum, Finset.mul_sum, routeCost]
  rw [Finset.sum_comm]

/-- The exact bounded-variable dual formula, with explicitly defined degree and cut matrices. -/
def certifiedBound (b : V → ℕ) (cost : (V × V) → ℚ)
    (cs : Finset κ) (cuts : κ → Finset V) (y : V ⊕ V → ℚ) (z : κ → ℚ) : ℚ :=
  (∑ h : V ⊕ V, y h * rhs b h) - (∑ k ∈ cs, z k) +
    ∑ e ∈ arcSet (V := V), capacity b e * min 0
      (cost e - (∑ h : V ⊕ V, y h * eqMatrix h e) +
        (∑ k ∈ cs, z k * cutMatrix (cuts k) e))

/-- Legal routes and exact visit coverage imply the dual lower bound on their actual cost.
Variable bounds, degree equations, and cut inequalities are proved above, not assumed here.
Only cut validity and the mathematical sign condition on the chosen dual multipliers are inputs. -/
theorem legalFleet_weak_duality {depot : V} (ks : Finset ι)
    (routes : ι → LegalRoute depot) (required : V → ℕ)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (cost : (V × V) → ℚ) (cs : Finset κ) (cuts : κ → Finset V)
    (hcuts : ∀ k ∈ cs, ValidCut depot required (cuts k))
    (y : V ⊕ V → ℚ) (z : κ → ℚ) (hz : ∀ k ∈ cs, z k ≤ 0) :
    certifiedBound (fleetDegree ks depot required) cost cs cuts y z ≤ routeCost ks routes cost := by
  calc
    _ ≤ ∑ e ∈ arcSet (V := V), cost e * flow (totalRouteFlow ks routes) e := by
      exact finite_weak_duality (arcSet (V := V)) Finset.univ cs
        (flow (totalRouteFlow ks routes)) (capacity (fleetDegree ks depot required)) cost
        eqMatrix (fun k => cutMatrix (cuts k)) (rhs (fleetDegree ks depot required)) y z
        (fun e _ => (legalFleet_variable_bounds ks routes required hvisits e).1)
        (fun e _ => (legalFleet_variable_bounds ks routes required hvisits e).2)
        (fun h _ => legalFleet_degree_rows ks routes required hvisits h)
        (fun k hk => legalFleet_cut_row ks routes required hvisits (cuts k) (hcuts k hk)) hz
    _ = _ := objective_eq_routeCost ks routes cost

end UAVProof.LPBridge
