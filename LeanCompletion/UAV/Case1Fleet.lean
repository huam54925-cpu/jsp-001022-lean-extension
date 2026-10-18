import LeanCompletion.UAV.Case1Budget

namespace UAVProof.Case1Fleet

open Case1Data LPBridge Case1Distance Case1Budget

def degree (n : ℕ) (i : Node) : ℕ := if i = depot then n else required i

def bound (n : ℕ) : ℚ :=
  certifiedBound (degree n) costUnits (Finset.univ : Finset CutIndex) cuts degreeDual cutDual

theorem degree_three : degree 3 = prescribedDegree := by
  funext i
  simp only [degree, prescribedDegree, fleetDegree, Finset.card_univ, Fintype.card_fin]

theorem degree_mono {n : ℕ} (hn : n ≤ 3) (i : Node) :
    degree n i ≤ prescribedDegree i := by
  rw [← degree_three]
  unfold degree
  split <;> omega

theorem depot_dual : degreeDual (Sum.inl depot) + degreeDual (Sum.inr depot) =
    (43200918 : ℚ) := by decide +kernel

theorem degree_term_difference (n : ℕ) :
    (∑ h : Node ⊕ Node, degreeDual h * rhs (degree n) h) -
      (∑ h : Node ⊕ Node, degreeDual h * rhs prescribedDegree h) =
      ((n : ℚ) - 3) * 43200918 := by
  simp only [Fintype.sum_sum_type, rhs, ← Finset.sum_add_distrib, ← add_mul]
  rw [← Finset.sum_sub_distrib]
  have ht (i : Node) :
      (degreeDual (Sum.inl i) + degreeDual (Sum.inr i)) * (degree n i : ℚ) -
        (degreeDual (Sum.inl i) + degreeDual (Sum.inr i)) * (prescribedDegree i : ℚ) =
      if i = depot then ((n : ℚ) - 3) * 43200918 else 0 := by
    rw [← degree_three]
    by_cases hi : i = depot
    · subst i
      simp only [degree, ↓reduceIte, Nat.cast_ofNat, depot_dual]
      ring
    · simp only [degree, if_neg hi, sub_self]
  simp_rw [ht]
  simp

/-- Smaller fleets have smaller arc capacities. Since each residual correction is
nonpositive, this can only improve the penalty part of the same certificate. -/
theorem bound_ge_three_adjusted {n : ℕ} (hn : n ≤ 3) :
    certificateBoundUnits + ((n : ℚ) - 3) * 43200918 ≤ bound n := by
  have hp :
      (∑ e ∈ arcSet (V := Node), capacity prescribedDegree e * min 0
        (costUnits e - (∑ h : Node ⊕ Node, degreeDual h * eqMatrix h e) +
          ∑ k : CutIndex, cutDual k * cutMatrix (cuts k) e)) ≤
      ∑ e ∈ arcSet (V := Node), capacity (degree n) e * min 0
        (costUnits e - (∑ h : Node ⊕ Node, degreeDual h * eqMatrix h e) +
          ∑ k : CutIndex, cutDual k * cutMatrix (cuts k) e) := by
    apply Finset.sum_le_sum
    intro e he
    apply mul_le_mul_of_nonpos_right _ (min_le_left _ _)
    dsimp only [capacity]
    exact_mod_cast min_le_min (degree_mono hn e.1) (degree_mono hn e.2)
  have hd := degree_term_difference n
  unfold certificateBoundUnits bound certifiedBound
  linarith

theorem fleet_weak_duality {ι : Type*} (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i) :
    bound ks.card ≤ routeCost ks routes costUnits := by
  exact legalFleet_weak_duality ks routes required hvisits costUnits Finset.univ
    cuts (fun k _ => cuts_valid k) degreeDual cutDual (fun k _ => cutDual_nonpos k)

/-- Conditional on the single three-fleet numerical certificate, every fleet of
at most three nonempty legal routes is infeasible, including zero, one and two. -/
theorem at_most_three_infeasible_of_certificate
    (hcertificate : (2316798209 : ℚ) / 2 ≤ certificateBoundUnits)
    {ι : Type*} (ks : Finset ι) (routes : ι → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (htime : ∀ k ∈ ks, routeTimeHours (routes k) ≤ 9) (hcard : ks.card ≤ 3) : False := by
  have hl := (bound_ge_three_adjusted hcard).trans (fleet_weak_duality ks routes hvisits)
  have hupper := fleet_distance_budget ks routes hvisits htime
  have hphysical := routeCost_km_le_fleetDistance ks routes
  have hlower : (2316798209 : ℝ) / 2 + ((ks.card : ℝ) - 3) * 43200918 ≤
      (routeCost ks routes costUnits : ℝ) := by
    have hq : (2316798209 : ℚ) / 2 + ((ks.card : ℚ) - 3) * 43200918 ≤
        routeCost ks routes costUnits := by linarith
    have hr : (((2316798209 : ℚ) / 2 + ((ks.card : ℚ) - 3) * 43200918 : ℚ) : ℝ) ≤
        (routeCost ks routes costUnits : ℝ) := Rat.cast_le.mpr hq
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_ofNat] using hr
  have hc : (ks.card : ℝ) ≤ 3 := by exact_mod_cast hcard
  linarith

end UAVProof.Case1Fleet
