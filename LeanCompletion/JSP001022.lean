import LeanMarathon.Main

set_option linter.all false
set_option maxHeartbeats 500000

set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_eventual_lower_bound :
∀ A : Set ℕ,
  0 < Filter.liminf (fun x : ℝ =>
    (∑' n : ℕ, (A ∩ real_initial_segment x).indicator (fun n : ℕ => (n : ℝ)⁻¹) n) / Real.log x) Filter.atTop →
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in Filter.atTop,
    c * Real.log x ≤ ∑' n : ℕ, (A ∩ real_initial_segment x).indicator (fun n : ℕ => (n : ℝ)⁻¹) n :=
by
  classical
  intro A hA
  let S : ℝ → ℝ := fun x =>
    ∑' n : ℕ, (A ∩ real_initial_segment x).indicator (fun n : ℕ => (n : ℝ)⁻¹) n
  let u : ℝ → ℝ := fun x => S x / Real.log x
  have hS (x : ℝ) : 0 ≤ S x := by
    apply tsum_nonneg
    intro n
    by_cases hn : n ∈ A ∩ real_initial_segment x
    · simpa only [Set.indicator_of_mem hn] using (inv_nonneg.mpr (Nat.cast_nonneg n) : (0 : ℝ) ≤ (n : ℝ)⁻¹)
    · simp only [Set.indicator_of_notMem hn, le_refl]
  have hu : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ u x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (hS x) (Real.log_pos hx).le
  have hL : 0 < Filter.liminf u Filter.atTop := hA
  refine ⟨Filter.liminf u Filter.atTop / 2, half_pos hL, ?_⟩
  have he := Filter.eventually_lt_of_lt_liminf (half_lt_self hL)
    (Filter.isBoundedUnder_of_eventually_ge hu)
  filter_upwards [he, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact ((lt_div_iff₀ (Real.log_pos hx1)).mp hx).le



set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_finite_abel_lower_bound :
∀ (a : ℕ → ℝ) (c : ℝ) (M N : ℕ),
  (∀ n : ℕ, 0 ≤ a n) → 0 < c → 2 ≤ M → M ≤ N →
  (∀ n ∈ Finset.Icc M N, c * Real.log (n : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), a k) →
  c * (∑ q ∈ Finset.Ico (M + 1) (N + 1),
    (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ))
    - (∑ k ∈ Finset.range M, a k) / Real.log (M : ℝ)
  ≤ ∑ n ∈ Finset.Ico 2 (N + 1), a n / Real.log (n : ℝ) :=
by
  intro a c M N ha hc hM hMN hprefix
  classical
  let S : ℕ → ℝ := fun t => ∑ k ∈ Finset.range (t + 1), a k
  let D : ℕ → ℝ := fun t => ∑ q ∈ Finset.Ico (M + 1) (t + 1),
    (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ)
  let W : ℕ → ℝ := fun t => ∑ n ∈ Finset.Ico M (t + 1), a n / Real.log (n : ℝ)
  let B : ℝ := ∑ k ∈ Finset.range M, a k
  have hlog : ∀ n : ℕ, 2 ≤ n → 0 < Real.log (n : ℝ) := by
    intro n hn
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have step (x y s v : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hs : c * x ≤ s) :
      c * ((y - x) / y) + (s + v) / y ≤ s / x + v / y := by
    have hy : 0 < y := lt_of_lt_of_le hx hxy
    have hh : (c * (y - x) + s) / y ≤ s / x := by
      apply (div_le_div_iff₀ hy hx).2
      nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hxy)]
    calc
      c * ((y - x) / y) + (s + v) / y = (c * (y - x) + s) / y + v / y := by ring
      _ ≤ s / x + v / y := by linarith only [hh]
  have strong : ∀ t, M ≤ t → t ≤ N →
      c * D t - B / Real.log (M : ℝ) + S t / Real.log (t : ℝ) ≤ W t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
        intro _
        simp [D, W, S, B, Finset.sum_range_succ, add_div] <;> linarith only []
    | succ t ht ih =>
        intro htN
        have ih' := ih (by omega)
        have hS : S (t + 1) = S t + a (t + 1) := by
          exact Finset.sum_range_succ a (t + 1)
        have hD : D (t + 1) = D t +
            (Real.log ((t + 1 : ℕ) : ℝ) - Real.log (t : ℝ)) /
              Real.log ((t + 1 : ℕ) : ℝ) := by
          dsimp [D]
          rw [Finset.sum_Ico_succ_top (by omega)]
          simp
        have hW : W (t + 1) = W t + a (t + 1) / Real.log ((t + 1 : ℕ) : ℝ) := by
          exact Finset.sum_Ico_succ_top (by omega) _
        have hs : c * Real.log (t : ℝ) ≤ S t :=
          hprefix t (Finset.mem_Icc.mpr ⟨ht, by omega⟩)
        have hxy : Real.log (t : ℝ) ≤ Real.log ((t + 1 : ℕ) : ℝ) := by
          apply Real.log_le_log
          · exact_mod_cast (show 0 < t by omega)
          · exact_mod_cast (show t ≤ t + 1 by omega)
        have hh := step (Real.log (t : ℝ)) (Real.log ((t + 1 : ℕ) : ℝ))
          (S t) (a (t + 1)) (hlog t (by omega)) hxy hs
        rw [hD, hS, hW]
        linarith only [ih', hh]
  have hstrong := strong N hMN le_rfl
  have hSnonneg : 0 ≤ S N / Real.log (N : ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun k _ => ha k)) (le_of_lt (hlog N (by omega)))
  have hext : W N ≤ ∑ n ∈ Finset.Ico 2 (N + 1), a n / Real.log (n : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
      exact Finset.mem_Ico.mpr ⟨by omega, hhi⟩
    · intro n hn _
      exact div_nonneg (ha n) (le_of_lt (hlog n (Finset.mem_Ico.mp hn).1))
  change c * D N - B / Real.log (M : ℝ) ≤ _
  linarith only [hstrong, hSnonneg, hext]


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_reciprocal_weight_specialization :
∀ (A : Set ℕ) (c : ℝ) (M : ℕ),
  0 < c → 2 ≤ M →
  let C : ℝ := (∑ k ∈ Finset.range M,
    A.indicator (fun n : ℕ => (n : ℝ)⁻¹) k) / Real.log (M : ℝ);
  ∀ N : ℕ, M ≤ N →
    (∀ n ∈ Finset.Icc M N, c * Real.log (n : ℝ) ≤
      ∑ k ∈ Finset.Ico 1 (n + 1), A.indicator (fun j : ℕ => (j : ℝ)⁻¹) k) →
    c * (∑ q ∈ Finset.Ico (M + 1) (N + 1),
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ)) - C
    ≤ ∑ n ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight n :=
by
  classical
  intro A c M hc hM
  dsimp only
  intro N hMN hprefix
  let a : ℕ → ℝ := A.indicator (fun j : ℕ => (j : ℝ)⁻¹)
  have ha : ∀ n : ℕ, 0 ≤ a n := by
    intro n
    by_cases hn : n ∈ A
    · simpa [a, hn] using (inv_nonneg.mpr (Nat.cast_nonneg n) : (0 : ℝ) ≤ (n : ℝ)⁻¹)
    · simp [a, hn]
  have hzero : a 0 = 0 := by
    by_cases h0 : 0 ∈ A <;> simp [a, h0]
  have hsum (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1), a k) =
        ∑ k ∈ Finset.Ico 1 (n + 1), a k := by
    rw [Finset.sum_range_eq_add_Ico a (Nat.zero_lt_succ n), hzero, zero_add]
  have hp : ∀ n ∈ Finset.Icc M N,
      c * Real.log (n : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), a k := by
    intro n hn
    rw [hsum]
    exact hprefix n hn
  have hw (n : ℕ) : a n / Real.log (n : ℝ) = A.indicator erdos_weight n := by
    by_cases hn : n ∈ A
    · simp [a, hn, erdos_weight, div_eq_mul_inv, mul_inv_rev, mul_comm]
    · simp [a, hn]
  have hAbel := LeanCompletion.jsp_001022_finite_abel_lower_bound a c M N
    ha hc hM hMN hp
  simpa only [hw] using hAbel


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_natural_loglog_lower_bound :
∀ (A : Set ℕ) (c : ℝ) (M : ℕ),
  0 < c → 2 ≤ M →
  (∀ n : ℕ, M ≤ n → c * Real.log (n : ℝ) ≤
    ∑ k ∈ Finset.Ico 1 (n + 1), A.indicator (fun j : ℕ => (j : ℝ)⁻¹) k) →
  ∃ C : ℝ, ∀ N : ℕ, M ≤ N →
    c * Real.log (Real.log (N : ℝ)) - C
      ≤ ∑ n ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight n :=
by
  classical
  intro A c M hc hM hprefix
  let term : ℕ → ℝ := fun q =>
    (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ)
  let E : ℕ → ℝ := fun t => ∑ q ∈ Finset.Ico 2 (t + 1), term q
  let B : ℝ := (∑ k ∈ Finset.range M,
    A.indicator (fun j : ℕ => (j : ℝ)⁻¹) k) / Real.log (M : ℝ)
  obtain ⟨K, hKnonneg, hK⟩ := mangoldt_log_reciprocal_main_term_bound
  refine ⟨c * (K + E M) + B, ?_⟩
  intro N hMN
  let D : ℝ := ∑ q ∈ Finset.Ico (M + 1) (N + 1), term q
  have hp : ∀ n ∈ Finset.Icc M N, c * Real.log (n : ℝ) ≤
      ∑ k ∈ Finset.Ico 1 (n + 1), A.indicator (fun j : ℕ => (j : ℝ)⁻¹) k := by
    intro n hn
    exact hprefix n (Finset.mem_Icc.mp hn).1
  have hw : c * D - B ≤
      ∑ n ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight n := by
    exact LeanCompletion.jsp_001022_reciprocal_weight_specialization
      A c M hc hM N hMN hp
  have hsplit : E M + D = E N := by
    exact Finset.sum_Ico_consecutive term (by omega : 2 ≤ M + 1)
      (by omega : M + 1 ≤ N + 1)
  have herr : |E N - Real.log (Real.log (N : ℝ))| ≤ K := by
    exact hK N (by omega)
  have hlower : -K ≤ E N - Real.log (Real.log (N : ℝ)) :=
    (abs_le.mp herr).1
  have hD : Real.log (Real.log (N : ℝ)) - K - E M ≤ D := by
    linarith only [hlower, hsplit]
  have hmul := mul_le_mul_of_nonneg_left hD (le_of_lt hc)
  linarith only [hmul, hw]



set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_eventual_to_finite_prefix :
∀ (A : Set ℕ) (c : ℝ),
  0 < c →
  (∀ᶠ x : ℝ in Filter.atTop, c * Real.log x ≤
    ∑' k : ℕ, (A ∩ real_initial_segment x).indicator (fun j : ℕ => (j : ℝ)⁻¹) k) →
  ∃ M : ℕ, 2 ≤ M ∧ ∀ n : ℕ, M ≤ n →
    c * Real.log (n : ℝ) ≤
      ∑ k ∈ Finset.Ico 1 (n + 1), A.indicator (fun j : ℕ => (j : ℝ)⁻¹) k :=
by
  classical
  intro A c hc hevent
  have hfinite (n : ℕ) :
      (∑' k : ℕ, (A ∩ real_initial_segment (n : ℝ)).indicator
        (fun j : ℕ => (j : ℝ)⁻¹) k) =
      ∑ k ∈ Finset.Ico 1 (n + 1), A.indicator (fun j : ℕ => (j : ℝ)⁻¹) k := by
    calc
      _ = ∑ k ∈ Finset.Ico 1 (n + 1),
          (A ∩ real_initial_segment (n : ℝ)).indicator
            (fun j : ℕ => (j : ℝ)⁻¹) k := by
        apply tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        intro k hk
        have hnot : k ∉ A ∩ real_initial_segment (n : ℝ) := by
          intro hmem
          have hseg : 1 ≤ k ∧ (k : ℝ) ≤ (n : ℝ) := hmem.2
          exact hk (Finset.mem_Ico.mpr
            ⟨hseg.1, Nat.lt_succ_of_le (Nat.cast_le.mp hseg.2)⟩)
        simp [Set.indicator, hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rcases Finset.mem_Ico.mp hk with ⟨hk1, hkn⟩
        have hseg : k ∈ real_initial_segment (n : ℝ) := by
          change 1 ≤ k ∧ (k : ℝ) ≤ (n : ℝ)
          refine ⟨hk1, ?_⟩
          exact_mod_cast (Nat.le_of_lt_succ hkn)
        by_cases hkA : k ∈ A <;> simp [Set.indicator, hkA, hseg]
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hevent
  obtain ⟨m, hm⟩ := exists_nat_ge R
  refine ⟨max 2 m, le_max_left _ _, ?_⟩
  intro n hn
  have hmn : m ≤ n := le_trans (le_max_right 2 m) hn
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hbound := hR (n : ℝ) (le_trans hm hmnR)
  rw [hfinite n] at hbound
  exact hbound


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_density_to_natural_erdos_lower_bound :
∀ A : Set ℕ,
  0 < Filter.liminf (fun x : ℝ =>
    (∑' k : ℕ, (A ∩ real_initial_segment x).indicator (fun j : ℕ => (j : ℝ)⁻¹) k) / Real.log x) Filter.atTop →
  ∃ c : ℝ, 0 < c ∧ ∃ M : ℕ, 2 ≤ M ∧ ∃ C : ℝ, ∀ N : ℕ, M ≤ N →
    c * Real.log (Real.log (N : ℝ)) - C ≤ erdos_sum_up_to A (N : ℝ) :=
by
  classical
  intro A hA
  obtain ⟨c, hc, hevent⟩ := LeanCompletion.jsp_001022_eventual_lower_bound A hA
  obtain ⟨M, hM, hprefix⟩ :=
    LeanCompletion.jsp_001022_eventual_to_finite_prefix A c hc hevent
  obtain ⟨C, hC⟩ :=
    LeanCompletion.jsp_001022_natural_loglog_lower_bound A c M hc hM hprefix
  have hfinite (N : ℕ) : erdos_sum_up_to A (N : ℝ) =
      ∑ k ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight k := by
    unfold erdos_sum_up_to erdos_sum
    calc
      _ = ∑ k ∈ Finset.Ico 2 (N + 1),
          (A ∩ real_initial_segment (N : ℝ)).indicator erdos_weight k := by
        apply tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        intro k hk
        by_cases hk1 : k = 1
        · subst k
          simp [Set.indicator, erdos_weight]
        · have hnot : k ∉ A ∩ real_initial_segment (N : ℝ) := by
            intro hmem
            have hseg : 1 ≤ k ∧ (k : ℝ) ≤ (N : ℝ) := hmem.2
            have hkN : k ≤ N := Nat.cast_le.mp hseg.2
            exact hk (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          simp [Set.indicator, hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rcases Finset.mem_Ico.mp hk with ⟨hk2, hkN⟩
        have hseg : k ∈ real_initial_segment (N : ℝ) := by
          change 1 ≤ k ∧ (k : ℝ) ≤ (N : ℝ)
          refine ⟨by omega, ?_⟩
          exact_mod_cast (Nat.le_of_lt_succ hkN)
        by_cases hkA : k ∈ A <;> simp [Set.indicator, hkA, hseg]
  refine ⟨c, hc, M, hM, C, ?_⟩
  intro N hMN
  rw [hfinite N]
  exact hC N hMN


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_density_bridge :
∀ A : Set ℕ,
  0 < Filter.liminf (fun x : ℝ =>
    (∑' n : ℕ, (A ∩ real_initial_segment x).indicator (fun n : ℕ => (n : ℝ)⁻¹) n) / Real.log x) Filter.atTop →
  0 < upper_doubly_log_density A :=
by
  classical
  intro A hA
  obtain ⟨c, hc, M, hM, C, hC⟩ :=
    LeanCompletion.jsp_001022_density_to_natural_erdos_lower_bound A hA
  have hfinite (N : ℕ) : erdos_sum_up_to A (N : ℝ) =
      ∑ k ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight k := by
    unfold erdos_sum_up_to erdos_sum
    calc
      _ = ∑ k ∈ Finset.Ico 2 (N + 1),
          (A ∩ real_initial_segment (N : ℝ)).indicator erdos_weight k := by
        apply tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        intro k hk
        by_cases hk1 : k = 1
        · subst k
          simp [Set.indicator, erdos_weight]
        · have hnot : k ∉ A ∩ real_initial_segment (N : ℝ) := by
            intro hmem
            have hseg : 1 ≤ k ∧ (k : ℝ) ≤ (N : ℝ) := hmem.2
            have hkN : k ≤ N := Nat.cast_le.mp hseg.2
            exact hk (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          simp [Set.indicator, hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rcases Finset.mem_Ico.mp hk with ⟨hk2, hkN⟩
        have hseg : k ∈ real_initial_segment (N : ℝ) := by
          change 1 ≤ k ∧ (k : ℝ) ≤ (N : ℝ)
          refine ⟨by omega, ?_⟩
          exact_mod_cast (Nat.le_of_lt_succ hkN)
        by_cases hkA : k ∈ A <;> simp [Set.indicator, hkA, hseg]
  have hfloor (x : ℝ) (hx : 0 ≤ x) :
      erdos_sum_up_to A x = erdos_sum_up_to A (⌊x⌋₊ : ℝ) := by
    have heq : real_initial_segment x = real_initial_segment (⌊x⌋₊ : ℝ) := by
      ext k
      change (1 ≤ k ∧ (k : ℝ) ≤ x) ↔ (1 ≤ k ∧ (k : ℝ) ≤ (⌊x⌋₊ : ℝ))
      constructor
      · rintro ⟨hk, hkx⟩
        exact ⟨hk, Nat.cast_le.mpr (Nat.le_floor hkx)⟩
      · rintro ⟨hk, hkx⟩
        exact ⟨hk, hkx.trans (Nat.floor_le hx)⟩
    unfold erdos_sum_up_to
    rw [heq]
  have hinc (q : ℕ) (hq : 2 ≤ q) :
      erdos_weight q ≤
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ) := by
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
    have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq1
    have hp : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < q - 1 by omega)
    have hpred : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    have hh := Real.log_le_sub_one_of_pos (div_pos hp hq0)
    rw [Real.log_div hp.ne' hq0.ne'] at hh
    have hid : ((q - 1 : ℕ) : ℝ) / (q : ℝ) - 1 = -(1 / (q : ℝ)) := by
      rw [hpred]
      field_simp
      <;> ring
    rw [hid] at hh
    have hrec : 1 / (q : ℝ) ≤ Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ) := by
      linarith only [hh]
    calc
      erdos_weight q = (1 / (q : ℝ)) / Real.log (q : ℝ) := by
        unfold erdos_weight
        rw [div_div]
      _ ≤ _ := div_le_div_of_nonneg_right hrec (Real.log_pos hq1).le
  obtain ⟨K, hK0, hK⟩ := mangoldt_log_reciprocal_main_term_bound
  have hnatup (N : ℕ) (hN : 2 ≤ N) :
      erdos_sum_up_to A (N : ℝ) ≤ Real.log (Real.log (N : ℝ)) + K := by
    rw [hfinite N]
    have hsum : (∑ k ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight k) ≤
        ∑ q ∈ Finset.Ico 2 (N + 1),
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq2 := (Finset.mem_Ico.mp hq).1
      have hw : 0 ≤ erdos_weight q := by
        unfold erdos_weight
        exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg q)
          (Real.log_pos (by exact_mod_cast (show 1 < q by omega))).le)
      by_cases hqa : q ∈ A
      · simpa only [Set.indicator_of_mem hqa] using hinc q hq2
      · simpa only [Set.indicator_of_notMem hqa] using hw.trans (hinc q hq2)
    have herr := (abs_le.mp (hK N hN)).2
    linarith only [hsum, herr]
  have hrealup (x : ℝ) (hx : 2 ≤ x) :
      erdos_sum_up_to A x ≤ Real.log (Real.log x) + K := by
    have hx0 : 0 ≤ x := by linarith only [hx]
    have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
    have hn1 : (1 : ℝ) < (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (show 1 < ⌊x⌋₊ by omega)
    have hmono : Real.log (Real.log (⌊x⌋₊ : ℝ)) ≤ Real.log (Real.log x) :=
      Real.log_le_log (Real.log_pos hn1)
        (Real.log_le_log (lt_trans zero_lt_one hn1) (Nat.floor_le hx0))
    rw [hfloor x hx0]
    have hbound := hnatup _ hn
    linarith only [hbound, hmono]
  have hgrowth : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hup : ∀ᶠ x : ℝ in Filter.atTop,
      erdos_sum_up_to A x / Real.log (Real.log x) ≤ K + 1 := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
      hgrowth.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with x hx hL
    apply (div_le_iff₀ (by linarith only [hL])).2
    have hbound := hrealup x hx
    have hmul := mul_nonneg hK0 (sub_nonneg.mpr hL)
    nlinarith only [hbound, hmul]
  have hlow : ∀ᶠ x : ℝ in Filter.atTop,
      c / 2 ≤ erdos_sum_up_to A x / Real.log (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop (M : ℝ),
      hgrowth.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
      hgrowth.eventually (Filter.eventually_ge_atTop (2 * (C + c * Real.log 2) / c))]
      with x hx hL hlarge
    have hx2 : 2 ≤ x := le_trans (by exact_mod_cast hM) hx
    have hx0 : 0 ≤ x := by linarith only [hx2]
    have hn : M ≤ ⌊x⌋₊ := Nat.le_floor hx
    have hnat := hC ⌊x⌋₊ hn
    have herr := (abs_le.mp (mangoldt_log_reciprocal_floor_loglog_bound x hx2)).1
    have hmul := mul_le_mul_of_nonneg_left herr hc.le
    have hlarge' := (div_le_iff₀ hc).mp hlarge
    apply (le_div_iff₀ (by linarith only [hL])).2
    rw [hfloor x hx0]
    nlinarith only [hnat, hmul, hlarge']
  unfold upper_doubly_log_density
  exact lt_of_lt_of_le (half_pos hc)
    (Filter.le_limsup_of_frequently_le hlow.frequently
      (Filter.isBoundedUnder_of_eventually_le hup))


set_option autoImplicit false in
theorem LeanCompletion.erdos_1217_explicit :
∀ A : Set ℕ,
  0 < Filter.limsup (fun x : ℝ => erdos_sum (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ x}) / Real.log (Real.log x)) Filter.atTop →
  ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ i, n i ∣ n (i + 1)) ∧ (∀ i, n i ∈ A) ∧
    ENNReal.ofReal (Filter.limsup (fun x : ℝ => erdos_sum (A ∩ {m : ℕ | 1 ≤ m ∧ (m : ℝ) ≤ x}) / Real.log (Real.log x)) Filter.atTop) ≤
    Filter.limsup (fun x : ℝ => ENNReal.ofReal ((Set.ncard {i : ℕ | (n i : ℝ) ≤ x} : ℝ) / Real.log (Real.log x))) Filter.atTop :=
by
  intro A hA
  have h := erdos_sarkozy_szemeredi_1217 A (by
    simpa [upper_doubly_log_density, erdos_sum_up_to, real_initial_segment] using hA)
  rcases h with ⟨n, hnchain, hset, hdensity⟩
  refine ⟨n, hnchain.1, hnchain.2, ?_, ?_⟩
  · simpa [chain_in_set] using hset
  · simpa [upper_chain_density_at_least, upper_chain_density,
      chain_count_up_to, upper_doubly_log_density, erdos_sum_up_to,
      real_initial_segment] using hdensity


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_chain_strict_cutoff :
∀ n : ℕ → ℕ, StrictMono n →
  Filter.limsup (fun x : ℝ => ENNReal.ofReal
    ((Set.ncard {i : ℕ | (n i : ℝ) < x} : ℝ) / Real.log (Real.log x))) Filter.atTop =
  Filter.limsup (fun x : ℝ => ENNReal.ofReal
    ((Set.ncard {i : ℕ | (n i : ℝ) ≤ x} : ℝ) / Real.log (Real.log x))) Filter.atTop :=
by
  classical
  intro n hn
  have hindex : ∀ i, i ≤ n i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i hi => exact Nat.succ_le_of_lt (lt_of_le_of_lt hi (hn (Nat.lt_succ_self i)))
  have hfinite (x : ℝ) : Set.Finite {i : ℕ | (n i : ℝ) ≤ x} := by
    apply (Set.finite_Iic (Nat.floor x)).subset
    intro i hi
    exact (hindex i).trans (Nat.le_floor hi)
  have hsub (x : ℝ) : {i : ℕ | (n i : ℝ) < x} ⊆ {i : ℕ | (n i : ℝ) ≤ x} := by
    intro i hi
    change (n i : ℝ) < x at hi
    exact hi.le
  have hstrictFinite (x : ℝ) : Set.Finite {i : ℕ | (n i : ℝ) < x} :=
    (hfinite x).subset (hsub x)
  have hcounts (x : ℝ) :
      Set.ncard {i : ℕ | (n i : ℝ) < x} ≤ Set.ncard {i : ℕ | (n i : ℝ) ≤ x} ∧
      Set.ncard {i : ℕ | (n i : ℝ) ≤ x} ≤ Set.ncard {i : ℕ | (n i : ℝ) < x} + 1 := by
    refine ⟨Set.ncard_le_ncard (hsub x) (hfinite x), ?_⟩
    have hefinite : Set.Finite {i : ℕ | (n i : ℝ) = x} :=
      (hfinite x).subset (fun i hi => le_of_eq hi)
    have heone : Set.ncard {i : ℕ | (n i : ℝ) = x} ≤ 1 := by
      apply (Set.ncard_le_one hefinite).2
      intro i hi j hj
      apply hn.injective
      exact_mod_cast (hi.trans hj.symm : (n i : ℝ) = (n j : ℝ))
    have hdecomp : {i : ℕ | (n i : ℝ) ≤ x} =
        {i : ℕ | (n i : ℝ) < x} ∪ {i : ℕ | (n i : ℝ) = x} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_union]
      exact le_iff_lt_or_eq
    rw [hdecomp]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left heone _)
  let L : ℝ → ENNReal := fun x => ENNReal.ofReal
    ((Set.ncard {i : ℕ | (n i : ℝ) < x} : ℝ) / Real.log (Real.log x))
  let U : ℝ → ENNReal := fun x => ENNReal.ofReal
    ((Set.ncard {i : ℕ | (n i : ℝ) ≤ x} : ℝ) / Real.log (Real.log x))
  let E : ℝ → ENNReal := fun x => ENNReal.ofReal (1 / Real.log (Real.log x))
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log (Real.log x) :=
    hlog.eventually (Filter.eventually_gt_atTop 0)
  have herr : Filter.Tendsto E Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun x : ℝ => 1 / Real.log (Real.log x)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop (tendsto_const_nhds (x := (1 : ℝ))) hlog
    simpa only [E, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hr
  have hLU : ∀ᶠ x in Filter.atTop, L x ≤ U x := by
    filter_upwards [hpos] with x hx
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ hx.le
    exact_mod_cast (hcounts x).1
  have hUL : ∀ᶠ x in Filter.atTop, U x ≤ (L + E) x := by
    filter_upwards [hpos] with x hx
    have hc : (Set.ncard {i : ℕ | (n i : ℝ) ≤ x} : ℝ) ≤
        (Set.ncard {i : ℕ | (n i : ℝ) < x} : ℝ) + 1 := by
      exact_mod_cast (hcounts x).2
    change ENNReal.ofReal _ ≤ ENNReal.ofReal _ + ENNReal.ofReal _
    calc
      ENNReal.ofReal ((Set.ncard {i : ℕ | (n i : ℝ) ≤ x} : ℝ) / Real.log (Real.log x))
          ≤ ENNReal.ofReal (((Set.ncard {i : ℕ | (n i : ℝ) < x} : ℝ) + 1) / Real.log (Real.log x)) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hc hx.le)
      _ = ENNReal.ofReal ((Set.ncard {i : ℕ | (n i : ℝ) < x} : ℝ) / Real.log (Real.log x) +
          1 / Real.log (Real.log x)) := by rw [add_div]
      _ ≤ _ := ENNReal.ofReal_add_le
  change Filter.limsup L Filter.atTop = Filter.limsup U Filter.atTop
  apply le_antisymm (Filter.limsup_le_limsup hLU)
  calc
    Filter.limsup U Filter.atTop ≤ Filter.limsup (L + E) Filter.atTop := Filter.limsup_le_limsup hUL
    _ = Filter.limsup L Filter.atTop := ENNReal.limsup_add_of_right_tendsto_zero herr L


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_reciprocal_strict_cutoff :
∀ A : Set ℕ,
  Filter.liminf (fun x : ℝ =>
    (∑' n : ℕ, (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}).indicator
      (fun n : ℕ => (n : ℝ)⁻¹) n) / Real.log x) Filter.atTop =
  Filter.liminf (fun x : ℝ =>
    (∑' n : ℕ, (A ∩ real_initial_segment x).indicator
      (fun n : ℕ => (n : ℝ)⁻¹) n) / Real.log x) Filter.atTop :=
by
  classical
  intro A
  let f (x : ℝ) := (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}).indicator (fun n : ℕ => (n : ℝ)⁻¹)
  let g (x : ℝ) := (A ∩ real_initial_segment x).indicator (fun n : ℕ => (n : ℝ)⁻¹)
  let S (x : ℝ) := ∑' n, f x n
  let T (x : ℝ) := ∑' n, g x n
  let L (x : ℝ) := S x / Real.log x
  let U (x : ℝ) := T x / Real.log x
  change Filter.liminf L Filter.atTop = Filter.liminf U Filter.atTop
  have repr (x : ℝ) (B : Set ℕ) (hB : B ⊆ real_initial_segment x) :
      (∑' n : ℕ, B.indicator (fun n : ℕ => (n : ℝ)⁻¹) n) =
        ∑ n ∈ Finset.Icc 1 (Nat.floor x), B.indicator (fun n : ℕ => (n : ℝ)⁻¹) n := by
    apply tsum_eq_sum
    intro n hn
    apply Set.indicator_of_notMem
    intro h
    have hm := hB h
    exact hn (Finset.mem_Icc.mpr ⟨hm.1, Nat.le_floor hm.2⟩)
  have rS (x : ℝ) : S x = ∑ n ∈ Finset.Icc 1 (Nat.floor x), f x n := by
    apply repr
    intro n hn
    exact ⟨hn.2.1, hn.2.2.le⟩
  have rT (x : ℝ) : T x = ∑ n ∈ Finset.Icc 1 (Nat.floor x), g x n := by
    apply repr
    exact Set.inter_subset_right
  have nf (x : ℝ) (n : ℕ) : 0 ≤ f x n := by
    dsimp [f]
    exact Set.indicator_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)) n
  have ng (x : ℝ) (n : ℕ) : 0 ≤ g x n := by
    dsimp [g]
    exact Set.indicator_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)) n
  have fg (x : ℝ) (n : ℕ) : f x n ≤ g x n := by
    by_cases h : n ∈ A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}
    · have h' : n ∈ A ∩ real_initial_segment x := ⟨h.1, h.2.1, h.2.2.le⟩
      simp [f, g, Set.indicator_of_mem h, Set.indicator_of_mem h']
    · simpa only [f, Set.indicator_of_notMem h] using ng x n
  have endpoint (x : ℝ) (n : ℕ) :
      g x n ≤ f x n + (if n = Nat.floor x then (1 : ℝ) else 0) := by
    by_cases h : n ∈ A ∩ real_initial_segment x
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.2.1
      by_cases ht : (n : ℝ) < x
      · have hf : n ∈ A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x} := ⟨h.1, h.2.1, ht⟩
        simp only [g, f, Set.indicator_of_mem h, Set.indicator_of_mem hf]
        split_ifs <;> linarith
      · have he : (n : ℝ) = x := le_antisymm h.2.2 (le_of_not_gt ht)
        have he' : n = Nat.floor x := by rw [← he]; simp
        have hi : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith only [hn])).mpr hn
        simpa only [g, Set.indicator_of_mem h, if_pos he'] using
          (show (n : ℝ)⁻¹ ≤ f x n + 1 by linarith only [hi, nf x n])
    · simp only [g, Set.indicator_of_notMem h]
      exact add_nonneg (nf x n) (by split_ifs <;> norm_num)
  have bounds (x : ℝ) (hx : 1 ≤ x) :
      0 ≤ S x ∧ S x ≤ T x ∧ T x ≤ S x + 1 ∧ T x ≤ 1 + Real.log x := by
    have hs : 0 ≤ S x := by rw [rS]; exact Finset.sum_nonneg (fun n _ => nf x n)
    have hst : S x ≤ T x := by
      rw [rS, rT]; exact Finset.sum_le_sum (fun n _ => fg x n)
    have he : T x ≤ S x + 1 := by
      rw [rT, rS]
      calc
        _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), (f x n + if n = Nat.floor x then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun n _ => endpoint x n)
        _ ≤ _ := by rw [Finset.sum_add_distrib]; simp [hx]
    have hh : T x ≤ (harmonic (Nat.floor x) : ℝ) := by
      rw [rT, harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_le_sum
      intro n hn
      by_cases h : n ∈ A ∩ real_initial_segment x
      · simp [g, Set.indicator_of_mem h]
      · simp only [g, Set.indicator_of_notMem h]
        positivity
    exact ⟨hs, hst, he, hh.trans (harmonic_floor_le_one_add_log x hx)⟩
  have tail : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ 1 ≤ Real.log x :=
    (Filter.eventually_ge_atTop 1).and (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1))
  have ev : ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ L x ∧ L x ≤ U x ∧ U x ≤ 2 ∧ U x ≤ L x + 1 / Real.log x := by
    filter_upwards [tail] with x hx
    obtain ⟨hs, hst, he, hh⟩ := bounds x hx.1
    have hp : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hx.2
    refine ⟨div_nonneg hs hp.le, div_le_div_of_nonneg_right hst hp.le, ?_, ?_⟩
    · apply (div_le_iff₀ hp).mpr
      linarith only [hh, hx.2]
    · dsimp [U, L]
      rw [← add_div]
      exact div_le_div_of_nonneg_right he hp.le
  have bl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop L := ⟨0, ev.mono (fun x h => h.1)⟩
  have bu : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop U :=
    ⟨0, ev.mono (fun x h => h.1.trans h.2.1)⟩
  have al : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop L :=
    ⟨2, ev.mono (fun x h => h.2.1.trans h.2.2.1)⟩
  have au : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop U :=
    ⟨2, ev.mono (fun x h => h.2.2.1)⟩
  apply le_antisymm
  · exact Filter.liminf_le_liminf (ev.mono (fun x h => h.2.1)) bl au.isCoboundedUnder_ge
  · have hz : Filter.Tendsto (fun x : ℝ => 1 / Real.log x) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
    apply le_of_forall_pos_le_add
    intro ε hε
    have heps : ∀ᶠ x : ℝ in Filter.atTop, U x ≤ L x + ε := by
      filter_upwards [ev, hz.eventually (gt_mem_nhds hε)] with x hx he
      linarith only [hx.2.2.2, he]
    have ae : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun x => L x + ε) := by
      refine ⟨2 + ε, ev.mono ?_⟩
      intro x hx
      change L x + ε ≤ 2 + ε
      linarith only [hx.2.1, hx.2.2.1]
    have h := Filter.liminf_le_liminf heps bu ae.isCoboundedUnder_ge
    rw [liminf_add_const Filter.atTop L ε al.isCoboundedUnder_ge bl] at h
    exact h


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_erdos_strict_cutoff :
∀ A : Set ℕ,
  Filter.limsup (fun x : ℝ =>
    erdos_sum (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}) /
      Real.log (Real.log x)) Filter.atTop =
  upper_doubly_log_density A :=
by
  classical
  intro A
  have hfinite (N : ℕ) : erdos_sum_up_to A (N : ℝ) =
      ∑ k ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight k := by
    unfold erdos_sum_up_to erdos_sum
    calc
      _ = ∑ k ∈ Finset.Ico 2 (N + 1),
          (A ∩ real_initial_segment (N : ℝ)).indicator erdos_weight k := by
        apply tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        intro k hk
        by_cases hk1 : k = 1
        · subst k
          simp [Set.indicator, erdos_weight]
        · have hnot : k ∉ A ∩ real_initial_segment (N : ℝ) := by
            intro hmem
            have hseg : 1 ≤ k ∧ (k : ℝ) ≤ (N : ℝ) := hmem.2
            have hkN : k ≤ N := Nat.cast_le.mp hseg.2
            exact hk (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          simp [Set.indicator, hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rcases Finset.mem_Ico.mp hk with ⟨hk2, hkN⟩
        have hseg : k ∈ real_initial_segment (N : ℝ) := by
          change 1 ≤ k ∧ (k : ℝ) ≤ (N : ℝ)
          refine ⟨by omega, ?_⟩
          exact_mod_cast (Nat.le_of_lt_succ hkN)
        by_cases hkA : k ∈ A <;> simp [Set.indicator, hkA, hseg]
  have hfloor (x : ℝ) (hx : 0 ≤ x) :
      erdos_sum_up_to A x = erdos_sum_up_to A (⌊x⌋₊ : ℝ) := by
    have heq : real_initial_segment x = real_initial_segment (⌊x⌋₊ : ℝ) := by
      ext k
      change (1 ≤ k ∧ (k : ℝ) ≤ x) ↔ (1 ≤ k ∧ (k : ℝ) ≤ (⌊x⌋₊ : ℝ))
      constructor
      · rintro ⟨hk, hkx⟩
        exact ⟨hk, Nat.cast_le.mpr (Nat.le_floor hkx)⟩
      · rintro ⟨hk, hkx⟩
        exact ⟨hk, hkx.trans (Nat.floor_le hx)⟩
    unfold erdos_sum_up_to
    rw [heq]
  have hinc (q : ℕ) (hq : 2 ≤ q) :
      erdos_weight q ≤
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ) := by
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
    have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq1
    have hp : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < q - 1 by omega)
    have hpred : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    have hh := Real.log_le_sub_one_of_pos (div_pos hp hq0)
    rw [Real.log_div hp.ne' hq0.ne'] at hh
    have hid : ((q - 1 : ℕ) : ℝ) / (q : ℝ) - 1 = -(1 / (q : ℝ)) := by
      rw [hpred]
      field_simp
      <;> ring
    rw [hid] at hh
    have hrec : 1 / (q : ℝ) ≤ Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ) := by
      linarith only [hh]
    calc
      erdos_weight q = (1 / (q : ℝ)) / Real.log (q : ℝ) := by
        unfold erdos_weight
        rw [div_div]
      _ ≤ _ := div_le_div_of_nonneg_right hrec (Real.log_pos hq1).le
  have hw (n : ℕ) : 0 ≤ erdos_weight n := by
    by_cases hn : n = 0
    · subst n; simp [erdos_weight]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hn1))
  obtain ⟨K, hK0, hK⟩ := mangoldt_log_reciprocal_main_term_bound
  have hnatup (N : ℕ) (hN : 2 ≤ N) :
      erdos_sum_up_to A (N : ℝ) ≤ Real.log (Real.log (N : ℝ)) + K := by
    rw [hfinite N]
    have hsum : (∑ k ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight k) ≤
        ∑ q ∈ Finset.Ico 2 (N + 1),
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq2 := (Finset.mem_Ico.mp hq).1
      by_cases hqa : q ∈ A
      · simpa only [Set.indicator_of_mem hqa] using hinc q hq2
      · simpa only [Set.indicator_of_notMem hqa] using (hw q).trans (hinc q hq2)
    have herr := (abs_le.mp (hK N hN)).2
    linarith only [hsum, herr]
  have hrealup (x : ℝ) (hx : 2 ≤ x) :
      erdos_sum_up_to A x ≤ Real.log (Real.log x) + K := by
    have hx0 : 0 ≤ x := by linarith only [hx]
    have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
    have hn1 : (1 : ℝ) < (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (show 1 < ⌊x⌋₊ by omega)
    have hmono : Real.log (Real.log (⌊x⌋₊ : ℝ)) ≤ Real.log (Real.log x) :=
      Real.log_le_log (Real.log_pos hn1)
        (Real.log_le_log (lt_trans zero_lt_one hn1) (Nat.floor_le hx0))
    rw [hfloor x hx0]
    have hbound := hnatup _ hn
    linarith only [hbound, hmono]
  let C : ℝ := 1 / Real.log 2
  have hp2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := (div_pos zero_lt_one hp2).le
  have hwC (n : ℕ) (hn : 1 ≤ n) : erdos_weight n ≤ C := by
    by_cases he : n = 1
    · subst n; simpa [erdos_weight] using hC0
    · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      have hn1 : (1 : ℝ) < n := by linarith only [hn2]
      have hl : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
      have hlp := Real.log_pos hn1
      have hm : Real.log 2 ≤ (n : ℝ) * Real.log (n : ℝ) := by
        nlinarith only [hl, hlp, hn1]
      unfold erdos_weight C
      apply (div_le_div_iff₀ (mul_pos (lt_trans zero_lt_one hn1) hlp) hp2).2
      simpa using hm
  let f (x : ℝ) := (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}).indicator erdos_weight
  let g (x : ℝ) := (A ∩ real_initial_segment x).indicator erdos_weight
  let S (x : ℝ) := ∑' n, f x n
  let T (x : ℝ) := ∑' n, g x n
  let L (x : ℝ) := S x / Real.log (Real.log x)
  let U (x : ℝ) := T x / Real.log (Real.log x)
  change Filter.limsup L Filter.atTop = Filter.limsup U Filter.atTop
  have repr (x : ℝ) (B : Set ℕ) (hB : B ⊆ real_initial_segment x) :
      (∑' n : ℕ, B.indicator erdos_weight n) =
        ∑ n ∈ Finset.Icc 1 (Nat.floor x), B.indicator erdos_weight n := by
    apply tsum_eq_sum (L := SummationFilter.unconditional ℕ)
    intro n hn
    apply Set.indicator_of_notMem
    intro h
    have hm := hB h
    exact hn (Finset.mem_Icc.mpr ⟨hm.1, Nat.le_floor hm.2⟩)
  have rS (x : ℝ) : S x = ∑ n ∈ Finset.Icc 1 (Nat.floor x), f x n := by
    apply repr
    intro n hn
    exact ⟨hn.2.1, hn.2.2.le⟩
  have rT (x : ℝ) : T x = ∑ n ∈ Finset.Icc 1 (Nat.floor x), g x n := by
    apply repr
    exact Set.inter_subset_right
  have nf (x : ℝ) (n : ℕ) : 0 ≤ f x n :=
    Set.indicator_nonneg (fun n _ => hw n) n
  have ng (x : ℝ) (n : ℕ) : 0 ≤ g x n :=
    Set.indicator_nonneg (fun n _ => hw n) n
  have fg (x : ℝ) (n : ℕ) : f x n ≤ g x n := by
    by_cases h : n ∈ A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}
    · have h' : n ∈ A ∩ real_initial_segment x := ⟨h.1, h.2.1, h.2.2.le⟩
      simp [f, g, Set.indicator_of_mem h, Set.indicator_of_mem h']
    · simpa only [f, Set.indicator_of_notMem h] using ng x n
  have endpoint (x : ℝ) (n : ℕ) :
      g x n ≤ f x n + (if n = Nat.floor x then C else 0) := by
    by_cases h : n ∈ A ∩ real_initial_segment x
    · by_cases ht : (n : ℝ) < x
      · have hf : n ∈ A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x} := ⟨h.1, h.2.1, ht⟩
        simp only [g, f, Set.indicator_of_mem h, Set.indicator_of_mem hf]
        split_ifs <;> linarith only [hC0]
      · have he : (n : ℝ) = x := le_antisymm h.2.2 (le_of_not_gt ht)
        have he' : n = Nat.floor x := by rw [← he]; simp
        have hi := hwC n h.2.1
        simpa only [g, Set.indicator_of_mem h, if_pos he'] using
          (show erdos_weight n ≤ f x n + C by linarith only [hi, nf x n])
    · simp only [g, Set.indicator_of_notMem h]
      exact add_nonneg (nf x n) (by split_ifs <;> positivity)
  have bounds (x : ℝ) (hx : 1 ≤ x) :
      0 ≤ S x ∧ S x ≤ T x ∧ T x ≤ S x + C := by
    have hs : 0 ≤ S x := by rw [rS]; exact Finset.sum_nonneg (fun n _ => nf x n)
    have hst : S x ≤ T x := by
      rw [rS, rT]; exact Finset.sum_le_sum (fun n _ => fg x n)
    have he : T x ≤ S x + C := by
      rw [rT, rS]
      calc
        _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), (f x n + if n = Nat.floor x then C else 0) :=
          Finset.sum_le_sum (fun n _ => endpoint x n)
        _ ≤ _ := by rw [Finset.sum_add_distrib]; simp [hx]
    exact ⟨hs, hst, he⟩
  have hgrowth : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ev : ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ L x ∧ L x ≤ U x ∧ U x ≤ K + 1 ∧ U x ≤ L x + C / Real.log (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
      hgrowth.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with x hx hL
    obtain ⟨hs, hst, he⟩ := bounds x (by linarith only [hx])
    have hp : 0 < Real.log (Real.log x) := lt_of_lt_of_le zero_lt_one hL
    refine ⟨div_nonneg hs hp.le, div_le_div_of_nonneg_right hst hp.le, ?_, ?_⟩
    · apply (div_le_iff₀ hp).mpr
      have hbound := hrealup x hx
      have hmul := mul_nonneg hK0 (sub_nonneg.mpr hL)
      change erdos_sum_up_to A x ≤ (K + 1) * Real.log (Real.log x)
      nlinarith only [hbound, hmul]
    · dsimp [U, L]
      rw [← add_div]
      exact div_le_div_of_nonneg_right he hp.le
  have bl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop L := ⟨0, ev.mono (fun x h => h.1)⟩
  have bu : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop U :=
    ⟨0, ev.mono (fun x h => h.1.trans h.2.1)⟩
  have al : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop L :=
    ⟨K + 1, ev.mono (fun x h => h.2.1.trans h.2.2.1)⟩
  have au : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop U :=
    ⟨K + 1, ev.mono (fun x h => h.2.2.1)⟩
  apply le_antisymm
  · exact Filter.limsup_le_limsup (ev.mono (fun x h => h.2.1)) bl.isCoboundedUnder_le au
  · have hz : Filter.Tendsto (fun x : ℝ => C / Real.log (Real.log x)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hgrowth
    apply le_of_forall_pos_le_add
    intro ε hε
    have heps : ∀ᶠ x : ℝ in Filter.atTop, U x ≤ L x + ε := by
      filter_upwards [ev, hz.eventually (gt_mem_nhds hε)] with x hx he
      linarith only [hx.2.2.2, he]
    have ae : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun x => L x + ε) := by
      refine ⟨K + 1 + ε, ev.mono ?_⟩
      intro x hx
      change L x + ε ≤ K + 1 + ε
      linarith only [hx.2.1, hx.2.2.1]
    have h := Filter.limsup_le_limsup heps bu.isCoboundedUnder_le ae
    rw [limsup_add_const Filter.atTop L ε al bl.isCoboundedUnder_le] at h
    exact h


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_erdos_density_ennreal :
∀ A : Set ℕ,
  ENNReal.ofReal (upper_doubly_log_density A) =
  Filter.limsup (fun x : ℝ => ENNReal.ofReal
    (erdos_sum (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}) /
      Real.log (Real.log x))) Filter.atTop :=
by
  classical
  intro A
  have hfinite (N : ℕ) : erdos_sum_up_to A (N : ℝ) =
      ∑ k ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight k := by
    unfold erdos_sum_up_to erdos_sum
    calc
      _ = ∑ k ∈ Finset.Ico 2 (N + 1),
          (A ∩ real_initial_segment (N : ℝ)).indicator erdos_weight k := by
        apply tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        intro k hk
        by_cases hk1 : k = 1
        · subst k
          simp [Set.indicator, erdos_weight]
        · have hnot : k ∉ A ∩ real_initial_segment (N : ℝ) := by
            intro hmem
            have hseg : 1 ≤ k ∧ (k : ℝ) ≤ (N : ℝ) := hmem.2
            have hkN : k ≤ N := Nat.cast_le.mp hseg.2
            exact hk (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          simp [Set.indicator, hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rcases Finset.mem_Ico.mp hk with ⟨hk2, hkN⟩
        have hseg : k ∈ real_initial_segment (N : ℝ) := by
          change 1 ≤ k ∧ (k : ℝ) ≤ (N : ℝ)
          refine ⟨by omega, ?_⟩
          exact_mod_cast (Nat.le_of_lt_succ hkN)
        by_cases hkA : k ∈ A <;> simp [Set.indicator, hkA, hseg]
  have hfloor (x : ℝ) (hx : 0 ≤ x) :
      erdos_sum_up_to A x = erdos_sum_up_to A (⌊x⌋₊ : ℝ) := by
    have heq : real_initial_segment x = real_initial_segment (⌊x⌋₊ : ℝ) := by
      ext k
      change (1 ≤ k ∧ (k : ℝ) ≤ x) ↔ (1 ≤ k ∧ (k : ℝ) ≤ (⌊x⌋₊ : ℝ))
      constructor
      · rintro ⟨hk, hkx⟩
        exact ⟨hk, Nat.cast_le.mpr (Nat.le_floor hkx)⟩
      · rintro ⟨hk, hkx⟩
        exact ⟨hk, hkx.trans (Nat.floor_le hx)⟩
    unfold erdos_sum_up_to
    rw [heq]
  have hinc (q : ℕ) (hq : 2 ≤ q) :
      erdos_weight q ≤
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ) := by
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
    have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq1
    have hp : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < q - 1 by omega)
    have hpred : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    have hh := Real.log_le_sub_one_of_pos (div_pos hp hq0)
    rw [Real.log_div hp.ne' hq0.ne'] at hh
    have hid : ((q - 1 : ℕ) : ℝ) / (q : ℝ) - 1 = -(1 / (q : ℝ)) := by
      rw [hpred]
      field_simp
      <;> ring
    rw [hid] at hh
    have hrec : 1 / (q : ℝ) ≤ Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ) := by
      linarith only [hh]
    calc
      erdos_weight q = (1 / (q : ℝ)) / Real.log (q : ℝ) := by
        unfold erdos_weight
        rw [div_div]
      _ ≤ _ := div_le_div_of_nonneg_right hrec (Real.log_pos hq1).le
  have hw (n : ℕ) : 0 ≤ erdos_weight n := by
    by_cases hn : n = 0
    · subst n; simp [erdos_weight]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hn1))
  obtain ⟨K, hK0, hK⟩ := mangoldt_log_reciprocal_main_term_bound
  have hnatup (N : ℕ) (hN : 2 ≤ N) :
      erdos_sum_up_to A (N : ℝ) ≤ Real.log (Real.log (N : ℝ)) + K := by
    rw [hfinite N]
    have hsum : (∑ k ∈ Finset.Ico 2 (N + 1), A.indicator erdos_weight k) ≤
        ∑ q ∈ Finset.Ico 2 (N + 1),
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq2 := (Finset.mem_Ico.mp hq).1
      by_cases hqa : q ∈ A
      · simpa only [Set.indicator_of_mem hqa] using hinc q hq2
      · simpa only [Set.indicator_of_notMem hqa] using (hw q).trans (hinc q hq2)
    have herr := (abs_le.mp (hK N hN)).2
    linarith only [hsum, herr]
  have hrealup (x : ℝ) (hx : 2 ≤ x) :
      erdos_sum_up_to A x ≤ Real.log (Real.log x) + K := by
    have hx0 : 0 ≤ x := by linarith only [hx]
    have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
    have hn1 : (1 : ℝ) < (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (show 1 < ⌊x⌋₊ by omega)
    have hmono : Real.log (Real.log (⌊x⌋₊ : ℝ)) ≤ Real.log (Real.log x) :=
      Real.log_le_log (Real.log_pos hn1)
        (Real.log_le_log (lt_trans zero_lt_one hn1) (Nat.floor_le hx0))
    rw [hfloor x hx0]
    have hbound := hnatup _ hn
    linarith only [hbound, hmono]
  let f (x : ℝ) := (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}).indicator erdos_weight
  let g (x : ℝ) := (A ∩ real_initial_segment x).indicator erdos_weight
  let S (x : ℝ) := ∑' n, f x n
  let T (x : ℝ) := ∑' n, g x n
  let u (x : ℝ) := S x / Real.log (Real.log x)
  have repr (x : ℝ) (B : Set ℕ) (hB : B ⊆ real_initial_segment x) :
      (∑' n : ℕ, B.indicator erdos_weight n) =
        ∑ n ∈ Finset.Icc 1 (Nat.floor x), B.indicator erdos_weight n := by
    apply tsum_eq_sum (L := SummationFilter.unconditional ℕ)
    intro n hn
    apply Set.indicator_of_notMem
    intro h
    have hm := hB h
    exact hn (Finset.mem_Icc.mpr ⟨hm.1, Nat.le_floor hm.2⟩)
  have rS (x : ℝ) : S x = ∑ n ∈ Finset.Icc 1 (Nat.floor x), f x n := by
    apply repr
    intro n hn
    exact ⟨hn.2.1, hn.2.2.le⟩
  have rT (x : ℝ) : T x = ∑ n ∈ Finset.Icc 1 (Nat.floor x), g x n := by
    apply repr
    exact Set.inter_subset_right
  have nf (x : ℝ) (n : ℕ) : 0 ≤ f x n :=
    Set.indicator_nonneg (fun n _ => hw n) n
  have ng (x : ℝ) (n : ℕ) : 0 ≤ g x n :=
    Set.indicator_nonneg (fun n _ => hw n) n
  have fg (x : ℝ) (n : ℕ) : f x n ≤ g x n := by
    by_cases h : n ∈ A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}
    · have h' : n ∈ A ∩ real_initial_segment x := ⟨h.1, h.2.1, h.2.2.le⟩
      simp [f, g, Set.indicator_of_mem h, Set.indicator_of_mem h']
    · simpa only [f, Set.indicator_of_notMem h] using ng x n
  have bounds (x : ℝ) : 0 ≤ S x ∧ S x ≤ T x := by
    constructor
    · rw [rS]; exact Finset.sum_nonneg (fun n _ => nf x n)
    · rw [rS, rT]; exact Finset.sum_le_sum (fun n _ => fg x n)
  have hgrowth : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ev : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ u x ∧ u x ≤ K + 1 := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
      hgrowth.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with x hx hL
    obtain ⟨hs, hst⟩ := bounds x
    have hp : 0 < Real.log (Real.log x) := lt_of_lt_of_le zero_lt_one hL
    refine ⟨div_nonneg hs hp.le, ?_⟩
    apply (div_le_iff₀ hp).mpr
    have hbound := hrealup x hx
    have hmul := mul_nonneg hK0 (sub_nonneg.mpr hL)
    change S x ≤ (K + 1) * Real.log (Real.log x)
    change S x ≤ erdos_sum_up_to A x at hst
    nlinarith only [hst, hbound, hmul]
  have bl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u :=
    ⟨0, ev.mono (fun x h => h.1)⟩
  have bu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u :=
    ⟨K + 1, ev.mono (fun x h => h.2)⟩
  have hB3 : Filter.limsup u Filter.atTop = upper_doubly_log_density A :=
    LeanCompletion.jsp_001022_erdos_strict_cutoff A
  rw [← hB3]
  exact ENNReal.ofReal_limsup bl.isCoboundedUnder_le bu


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_positive_enumeration_sums :
∀ a : ℕ+ → ℕ+, StrictMono a →
  let A : Set ℕ := Set.range (fun i : ℕ+ => (a i : ℕ))
  A.Infinite ∧ ∀ x : ℝ,
    Set.Finite {i : ℕ+ | ((a i : ℕ) : ℝ) < x} ∧
    Set.Finite (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}) ∧
    ∀ w : ℕ → ℝ,
      (∑' i : ℕ+, if ((a i : ℕ) : ℝ) < x then w (a i : ℕ) else 0) =
      ∑' n : ℕ, (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}).indicator w n :=
by
  classical
  intro a ha
  let g : ℕ+ → ℕ := fun i => (a i : ℕ)
  have hg : Function.Injective g := PNat.coe_injective.comp ha.injective
  change (Set.range g).Infinite ∧ ∀ x : ℝ, _
  refine ⟨Set.infinite_range_of_injective hg, ?_⟩
  intro x
  have hT : Set.Finite {n : ℕ | (n : ℝ) < x} := by
    apply (Set.finite_Iic (Nat.floor x)).subset
    intro n hn
    exact Nat.le_floor (le_of_lt hn)
  have hi : Set.Finite {i : ℕ+ | ((a i : ℕ) : ℝ) < x} :=
    hT.preimage hg.injOn
  let S : Set ℕ := Set.range g ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}
  have hS : S.Finite := hT.subset (fun n hn => hn.2.2)
  refine ⟨hi, hS, ?_⟩
  intro w
  have hsupp : Function.support (S.indicator w) ⊆ Set.range g := by
    intro n hn
    by_contra h
    have hnS : n ∉ S := fun hnS => h hnS.1
    exact hn (Set.indicator_of_notMem hnS w)
  calc
    _ = ∑' i : ℕ+, S.indicator w (g i) := by
      apply tsum_congr
      intro i
      change (if (g i : ℝ) < x then w (g i) else 0) = S.indicator w (g i)
      have hpos : 1 ≤ g i := (a i).pos
      have hr : g i ∈ Set.range g := ⟨i, rfl⟩
      by_cases hx : (g i : ℝ) < x
      · have hm : g i ∈ S := ⟨hr, hpos, hx⟩
        rw [if_pos hx, Set.indicator_of_mem hm]
      · have hm : g i ∉ S := fun h => hx h.2.2
        rw [if_neg hx, Set.indicator_of_notMem hm]
    _ = _ := hg.tsum_eq hsupp


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_positive_subsequence_indices :
∀ a : ℕ+ → ℕ+, StrictMono a →
  ∀ n : ℕ → ℕ, StrictMono n →
    (∀ j : ℕ, n j ∣ n (j + 1)) →
    (∀ j : ℕ, n j ∈ Set.range (fun i : ℕ+ => (a i : ℕ))) →
    ∃ k : ℕ+ → ℕ+, StrictMono k ∧
      (∀ i : ℕ+, (a (k i) : ℕ) = n i.natPred) ∧
      (∀ i : ℕ+, (a (k i) : ℕ) ∣ (a (k (i + 1)) : ℕ)) ∧
      ∀ x : ℝ,
        Set.Finite {i : ℕ+ | ((a (k i) : ℕ) : ℝ) < x} ∧
        Set.Finite {j : ℕ | (n j : ℝ) < x} ∧
        Set.ncard {i : ℕ+ | ((a (k i) : ℕ) : ℝ) < x} =
          Set.ncard {j : ℕ | (n j : ℝ) < x} :=
by
  classical
  intro a ha n hn hd hr
  choose f hf using hr
  change ∀ j : ℕ, (a (f j) : ℕ) = n j at hf
  have hfm : StrictMono f := by
    intro u v huv
    apply ha.lt_iff_lt.mp
    change (a (f u) : ℕ) < (a (f v) : ℕ)
    rw [hf u, hf v]
    exact hn huv
  let k : ℕ+ → ℕ+ := fun i => f i.natPred
  have hk : StrictMono k := hfm.comp PNat.natPred_strictMono
  have hv : ∀ i : ℕ+, (a (k i) : ℕ) = n i.natPred := by
    intro i
    exact hf i.natPred
  refine ⟨k, hk, hv, ?_, ?_⟩
  · intro i
    rw [hv i, hv (i + 1)]
    have hs : (i + 1).natPred = i.natPred + 1 := by
      have h₁ := PNat.natPred_add_one i
      have h₂ := PNat.natPred_add_one (i + 1)
      change (i + 1).natPred + 1 = (i : ℕ) + 1 at h₂
      omega
    rw [hs]
    exact hd i.natPred
  · intro x
    have hT : Set.Finite {m : ℕ | (m : ℝ) < x} := by
      apply (Set.finite_Iic (Nat.floor x)).subset
      intro m hm
      exact Nat.le_floor (le_of_lt hm)
    have hN : Set.Finite {j : ℕ | (n j : ℝ) < x} :=
      hT.preimage hn.injective.injOn
    have heq : {i : ℕ+ | ((a (k i) : ℕ) : ℝ) < x} =
        PNat.natPred ⁻¹' {j : ℕ | (n j : ℝ) < x} := by
      ext i
      change ((a (k i) : ℕ) : ℝ) < x ↔ (n i.natPred : ℝ) < x
      rw [hv i]
    rw [heq]
    refine ⟨hN.preimage PNat.natPred_injective.injOn, hN, ?_⟩
    apply Set.ncard_preimage_of_injective_subset_range PNat.natPred_injective
    intro j _
    exact Equiv.pnatEquivNat.surjective j


set_option autoImplicit false in
theorem LeanCompletion.jsp_001022_original_enumeration_chain :
∀ a : ℕ+ → ℕ+, StrictMono a →
  0 < Filter.liminf (fun x : ℝ =>
    (∑' i : ℕ+, if ((a i : ℕ) : ℝ) < x
      then ((a i : ℕ) : ℝ)⁻¹ else 0) / Real.log x) Filter.atTop →
  ∃ k : ℕ+ → ℕ+, StrictMono k ∧
    (∀ i : ℕ+, (a (k i) : ℕ) ∣ (a (k (i + 1)) : ℕ)) ∧
    Filter.limsup (fun x : ℝ => ENNReal.ofReal
      ((∑' i : ℕ+, if ((a i : ℕ) : ℝ) < x
        then 1 / (((a i : ℕ) : ℝ) * Real.log ((a i : ℕ) : ℝ)) else 0) /
        Real.log (Real.log x))) Filter.atTop ≤
    Filter.limsup (fun x : ℝ => ENNReal.ofReal
      ((Set.ncard {i : ℕ+ | ((a (k i) : ℕ) : ℝ) < x} : ℝ) /
        Real.log (Real.log x))) Filter.atTop :=
by
  classical
  intro a ha hpos
  let A : Set ℕ := Set.range (fun i : ℕ+ => (a i : ℕ))
  have hsums := (LeanCompletion.jsp_001022_positive_enumeration_sums a ha).2
  have hrec :
      (fun x : ℝ =>
        (∑' i : ℕ+, if ((a i : ℕ) : ℝ) < x
          then ((a i : ℕ) : ℝ)⁻¹ else 0) / Real.log x) =
      (fun x : ℝ =>
        (∑' n : ℕ, (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}).indicator
          (fun n : ℕ => (n : ℝ)⁻¹) n) / Real.log x) := by
    funext x
    rw [(hsums x).2.2 (fun n : ℕ => (n : ℝ)⁻¹)]
  rw [hrec, LeanCompletion.jsp_001022_reciprocal_strict_cutoff A] at hpos
  have hdelta := LeanCompletion.jsp_001022_density_bridge A hpos
  obtain ⟨n, hn, hd, hmem, hbound⟩ := LeanCompletion.erdos_1217_explicit A (by
    simpa only [upper_doubly_log_density, erdos_sum_up_to, real_initial_segment]
      using hdelta)
  obtain ⟨k, hk, hvalues, hdiv, hcounts⟩ :=
    LeanCompletion.jsp_001022_positive_subsequence_indices a ha n hn hd hmem
  refine ⟨k, hk, hdiv, ?_⟩
  have hwfun :
      (fun x : ℝ => ENNReal.ofReal
        ((∑' i : ℕ+, if ((a i : ℕ) : ℝ) < x
          then 1 / (((a i : ℕ) : ℝ) * Real.log ((a i : ℕ) : ℝ)) else 0) /
          Real.log (Real.log x))) =
      (fun x : ℝ => ENNReal.ofReal
        (erdos_sum (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}) /
          Real.log (Real.log x))) := by
    funext x
    have hw :
        (∑' i : ℕ+, if ((a i : ℕ) : ℝ) < x
          then 1 / (((a i : ℕ) : ℝ) * Real.log ((a i : ℕ) : ℝ)) else 0) =
        erdos_sum (A ∩ {n : ℕ | 1 ≤ n ∧ (n : ℝ) < x}) := by
      simpa only [erdos_sum, erdos_weight] using (hsums x).2.2 erdos_weight
    rw [hw]
  have hcountfun :
      (fun x : ℝ => ENNReal.ofReal
        ((Set.ncard {i : ℕ+ | ((a (k i) : ℕ) : ℝ) < x} : ℝ) /
          Real.log (Real.log x))) =
      (fun x : ℝ => ENNReal.ofReal
        ((Set.ncard {j : ℕ | (n j : ℝ) < x} : ℝ) /
          Real.log (Real.log x))) := by
    funext x
    rw [(hcounts x).2.2]
  rw [hwfun, hcountfun, ← LeanCompletion.jsp_001022_erdos_density_ennreal A,
    LeanCompletion.jsp_001022_chain_strict_cutoff n hn]
  simpa only [upper_doubly_log_density, erdos_sum_up_to, real_initial_segment]
    using hbound

