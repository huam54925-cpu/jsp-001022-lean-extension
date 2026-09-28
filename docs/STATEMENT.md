# Frozen statement

Target: `LeanCompletion.jsp_001022_original_enumeration_chain`.

Source: [JSP001022.lean](../LeanCompletion/JSP001022.lean#L1136).
The audit separately states this type as an example proved by the target.

```lean
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
        Real.log (Real.log x))) Filter.atTop
```
