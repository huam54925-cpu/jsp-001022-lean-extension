
import Mathlib

namespace UAVProof

theorem bounded_reduced_cost
    (x u q : ℚ)
    (hx : 0 ≤ x)
    (hxu : x ≤ u) :
    u * min 0 q ≤ q * x := by
  by_cases hq : 0 ≤ q
  · rw [min_eq_left hq]
    simp only [mul_zero]
    exact mul_nonneg hq hx
  · have hq' : q ≤ 0 := le_of_lt (lt_of_not_ge hq)
    rw [min_eq_right hq']
    rw [mul_comm u q]
    exact mul_le_mul_of_nonpos_left hxu hq'




theorem bounded_reduced_cost_sum
    {E : Type*}
    (s : Finset E)
    (x u q : E → ℚ)
    (hx : ∀ e ∈ s, 0 ≤ x e)
    (hxu : ∀ e ∈ s, x e ≤ u e) :
    (∑ e ∈ s, u e * min 0 (q e))
      ≤ ∑ e ∈ s, q e * x e := by
  apply Finset.sum_le_sum
  intro e he
  exact bounded_reduced_cost
    (x e) (u e) (q e)
    (hx e he) (hxu e he)



theorem weak_duality_from_decomposition
    {E : Type*}
    (s : Finset E)
    (x u q c : E → ℚ)
    (base cut : ℚ)
    (hx : ∀ e ∈ s, 0 ≤ x e)
    (hxu : ∀ e ∈ s, x e ≤ u e)
    (hdecomp :
      (∑ e ∈ s, c e * x e) =
        base - cut + (∑ e ∈ s, q e * x e)) :
    base - cut +
        (∑ e ∈ s, u e * min 0 (q e))
      ≤ ∑ e ∈ s, c e * x e := by
  have hsum := bounded_reduced_cost_sum s x u q hx hxu
  rw [hdecomp]
  linarith


/-- Weak duality for a bounded finite linear program
    with equality constraints and lower-bound inequalities. -/
theorem finite_weak_duality
    {E I K : Type*}
    (es : Finset E) (is : Finset I) (ks : Finset K)
    (x u c : E → ℚ)
    (A : I → E → ℚ)
    (C : K → E → ℚ)
    (b y : I → ℚ)
    (z : K → ℚ)
    (hx : ∀ e ∈ es, 0 ≤ x e)
    (hxu : ∀ e ∈ es, x e ≤ u e)
    (heq : ∀ i ∈ is,
      (∑ e ∈ es, A i e * x e) = b i)
    (hcut : ∀ k ∈ ks,
      1 ≤ ∑ e ∈ es, C k e * x e)
    (hz : ∀ k ∈ ks, z k ≤ 0) :
    (∑ i ∈ is, y i * b i)
      - (∑ k ∈ ks, z k)
      + (∑ e ∈ es,
          u e * min 0
            (c e
              - (∑ i ∈ is, y i * A i e)
              + (∑ k ∈ ks, z k * C k e)))
      ≤ ∑ e ∈ es, c e * x e := by
  classical
  let q : E → ℚ := fun e =>
    c e
      - (∑ i ∈ is, y i * A i e)
      + (∑ k ∈ ks, z k * C k e)

  have hres :
      (∑ e ∈ es, u e * min 0 (q e))
        ≤ ∑ e ∈ es, q e * x e :=
    bounded_reduced_cost_sum es x u q hx hxu

  have heq_sum :
      (∑ i ∈ is, y i * b i) =
        ∑ e ∈ es,
          (∑ i ∈ is, y i * A i e) * x e := by
    calc
      (∑ i ∈ is, y i * b i)
          = ∑ i ∈ is,
              y i * (∑ e ∈ es, A i e * x e) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [heq i hi]
      _ = ∑ e ∈ es,
            (∑ i ∈ is, y i * A i e) * x e := by
              simp_rw [Finset.mul_sum]
              simp_rw [← mul_assoc]
              rw [Finset.sum_comm]
              simp_rw [← Finset.sum_mul]


  have hcut_sum :
      -(∑ k ∈ ks, z k) ≤
        -(∑ e ∈ es,
          (∑ k ∈ ks, z k * C k e) * x e) := by
    have hk : ∀ k ∈ ks,
        -(z k) ≤
          -(z k * (∑ e ∈ es, C k e * x e)) := by
      intro k hk
      have h := mul_le_mul_of_nonpos_left
        (hcut k hk) (hz k hk)
      linarith

    have hsum :
        (∑ k ∈ ks, -(z k)) ≤
          ∑ k ∈ ks,
            -(z k * (∑ e ∈ es, C k e * x e)) :=
      Finset.sum_le_sum hk

    have hswap :
        (∑ e ∈ es,
          (∑ k ∈ ks, z k * C k e) * x e) =
        (∑ k ∈ ks,
          z k * (∑ e ∈ es, C k e * x e)) := by
      calc
        _ = ∑ e ∈ es,
              ∑ k ∈ ks, z k * C k e * x e := by
              simp_rw [Finset.sum_mul]
        _ = ∑ k ∈ ks,
              ∑ e ∈ es, z k * C k e * x e := by
              rw [Finset.sum_comm]

        _ = ∑ k ∈ ks,
              z k * (∑ e ∈ es, C k e * x e) := by
              simp_rw [mul_assoc, Finset.mul_sum]


    simp only [Finset.sum_neg_distrib] at hsum
    rw [hswap]
    exact hsum


  have hdecomp :
      (∑ e ∈ es, c e * x e) =
        (∑ e ∈ es,
          (∑ i ∈ is, y i * A i e) * x e)
        - (∑ e ∈ es,
          (∑ k ∈ ks, z k * C k e) * x e)
        + (∑ e ∈ es, q e * x e) := by
    dsimp [q]
    simp_rw [add_mul, sub_mul]
    simp only [Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring

  rw [heq_sum]
  rw [hdecomp]
  linarith






end UAVProof
/-#print axioms UAVProof.finite_weak_duality
#print UAVProof.finite_weak_duality-/
