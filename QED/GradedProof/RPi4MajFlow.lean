/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopParametricAlgebra

/-!
# (R-Π₄) step L10, two loops: line flows at the saddle and the ray monomials

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2, per-piece
bounds along the ray). Along the ray `k = √s v` the Symanzik `V` of a piece is `V₀ + s B` with
`B = remainder α z q` (`q` the routing coefficients of `k`). At the saddle of the loop momenta the
line `i` carries the fraction `τᵢ = αᵢ·y + qᵢ` of `k` (`y = -A⁻¹β`, the flow), and
`B = ∑ᵢ zᵢ τᵢ²`. The `k⁴` coefficient of a fermion-loop numerator at the saddle is a multiple of
the product of the flows of the fermion lines; by AM–GM a product of two flows is at most
`B / (2 √(zᵢ zⱼ))`, which removes the `1/B` weight of the top monomial along the ray.

* `majFlow α z q i`: the flow of line `i`;
* `maj_remainder_eq_flow`: `remainder α z q = ∑ᵢ zᵢ τᵢ²`; `maj_mul_sq_flow_le`: `zᵢ τᵢ² ≤ B`;
* **`maj_abs_flow_mul_le`**: `2 √(zᵢ zⱼ) |τᵢ τⱼ| ≤ B` for `i ≠ j` (`maj_two_sqrt_mul_le`);
* **`maj_ray_four_le`**, **`maj_ray_three_le`**: `s² |P| / (V₀ + sB)ⁿ ≤ s W / V₀ⁿ⁻¹` if
  `|P| ≤ B W`, and `s^{3/2} |P| / (V₀ + sB)ⁿ ≤ s W / (V₀ⁿ⁻¹ √V₀)` if `|P| ≤ √B W`.
-/

@[expose] public section

open Matrix

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {m : ℕ}

/-- **The flow of line `i` at the saddle**: `τᵢ = αᵢ·y + qᵢ`, `y = -A⁻¹β`. -/
noncomputable def majFlow (α : Fin (m + 1) → Fin 2 → ℝ) (z q : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) : ℝ :=
  ∑ s, α i s * (-((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q)) s + q i

/-- **`B = ∑ᵢ zᵢ τᵢ²`.** -/
theorem maj_remainder_eq_flow (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hdet : symanzikU α z ≠ 0) (q : Fin (m + 1) → ℝ) :
    remainder α z q = ∑ i, z i * majFlow α z q i ^ 2 := by
  have h := sum_mul_sq_eq_shift α z hdet q (-((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q))
  rw [neg_add_cancel, zero_dotProduct, zero_add] at h
  rw [← h]
  rfl

/-- `zᵢ τᵢ² ≤ B`. -/
theorem maj_mul_sq_flow_le (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hdet : symanzikU α z ≠ 0) (q : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    z i * majFlow α z q i ^ 2 ≤ remainder α z q := by
  rw [maj_remainder_eq_flow α hdet q]
  exact Finset.single_le_sum (f := fun j => z j * majFlow α z q j ^ 2)
    (fun j _ => mul_nonneg (hz j) (sq_nonneg _)) (Finset.mem_univ i)

/-- `2 √(x y) |a b| ≤ x a² + y b²` for `x, y ≥ 0`. -/
theorem maj_two_sqrt_mul_le {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) * |a * b| ≤ x * a ^ 2 + y * b ^ 2 := by
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  rw [Real.sqrt_mul hx, abs_mul]
  have e : x * a ^ 2 + y * b ^ 2 = Real.sqrt x ^ 2 * |a| ^ 2 + Real.sqrt y ^ 2 * |b| ^ 2 := by
    rw [hsx, hsy, sq_abs, sq_abs]
  rw [e]
  nlinarith [sq_nonneg (Real.sqrt x * |a| - Real.sqrt y * |b|)]

/-- **AM–GM for two flows**: `2 √(zᵢ zⱼ) |τᵢ τⱼ| ≤ B` for `i ≠ j`. -/
theorem maj_abs_flow_mul_le (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hdet : symanzikU α z ≠ 0) (q : Fin (m + 1) → ℝ) {i j : Fin (m + 1)}
    (hij : i ≠ j) :
    2 * Real.sqrt (z i * z j) * |majFlow α z q i * majFlow α z q j| ≤ remainder α z q := by
  have h2 : z i * majFlow α z q i ^ 2 + z j * majFlow α z q j ^ 2 ≤ remainder α z q := by
    rw [maj_remainder_eq_flow α hdet q]
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => z l * majFlow α z q l ^ 2)
      (Finset.subset_univ {i, j}) (fun l _ _ => mul_nonneg (hz l) (sq_nonneg _))
    rwa [Finset.sum_pair hij] at this
  exact (maj_two_sqrt_mul_le (hz i) (hz j)).trans h2

/-! ### The top monomials along the ray -/

/-- **`j = 4`**: `s² |P| / (V₀ + sB)ⁿ ≤ s W / V₀ⁿ⁻¹` if `|P| ≤ B W`, `V₀ > 0`, `B, s ≥ 0`,
`n ≥ 1`, `W ≥ 0`. -/
theorem maj_ray_four_le {V₀ B s P W : ℝ} {n : ℕ} (hV₀ : 0 < V₀) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hn : 1 ≤ n) (hW : 0 ≤ W) (hP : |P| ≤ B * W) :
    s ^ 2 * |P| / (V₀ + s * B) ^ n ≤ s * W / V₀ ^ (n - 1) := by
  have hV : 0 < V₀ + s * B := by positivity
  have hsB : s * B ≤ V₀ + s * B := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hVk : V₀ ^ k ≤ (V₀ + s * B) ^ k := pow_le_pow_left₀ hV₀.le
    (le_add_of_nonneg_right (mul_nonneg hs hB)) k
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  calc s ^ 2 * |P| * V₀ ^ k ≤ s ^ 2 * (B * W) * V₀ ^ k := by gcongr
    _ = s * W * (s * B) * V₀ ^ k := by ring
    _ ≤ s * W * (V₀ + s * B) * (V₀ + s * B) ^ k := by
        have := mul_nonneg hs hW
        gcongr
    _ = s * W * ((V₀ + s * B) ^ k * (V₀ + s * B)) := by ring

/-- **`j = 3`**: `s^{3/2} |P| / (V₀ + sB)ⁿ ≤ s W / (V₀ⁿ⁻¹ √V₀)` if `|P| ≤ √B W`, `V₀ > 0`,
`B, s ≥ 0`, `n ≥ 1`, `W ≥ 0`. -/
theorem maj_ray_three_le {V₀ B s P W : ℝ} {n : ℕ} (hV₀ : 0 < V₀) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hn : 1 ≤ n) (hW : 0 ≤ W) (hP : |P| ≤ Real.sqrt B * W) :
    Real.sqrt s ^ 3 * |P| / (V₀ + s * B) ^ n ≤ s * W / (V₀ ^ (n - 1) * Real.sqrt V₀) := by
  have hV : 0 < V₀ + s * B := by positivity
  have hsq := Real.sqrt_nonneg s
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hVk : V₀ ^ k ≤ (V₀ + s * B) ^ k := pow_le_pow_left₀ hV₀.le
    (le_add_of_nonneg_right (mul_nonneg hs hB)) k
  have hsV : Real.sqrt V₀ ≤ Real.sqrt (V₀ + s * B) := Real.sqrt_le_sqrt (by nlinarith)
  have hsV0 : 0 < Real.sqrt V₀ := Real.sqrt_pos.mpr hV₀
  -- `√(s B) ≤ √(V₀ + s B)`, and `√(V₀ + sB)² = V₀ + sB`
  have hsB : Real.sqrt s * Real.sqrt B ≤ Real.sqrt (V₀ + s * B) := by
    rw [← Real.sqrt_mul hs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq2 : Real.sqrt (V₀ + s * B) * Real.sqrt (V₀ + s * B) = V₀ + s * B :=
    Real.mul_self_sqrt hV.le
  have hs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  calc Real.sqrt s ^ 3 * |P| * (V₀ ^ k * Real.sqrt V₀)
      ≤ Real.sqrt s ^ 3 * (Real.sqrt B * W) * (V₀ ^ k * Real.sqrt V₀) := by gcongr
    _ = s * W * (Real.sqrt s * Real.sqrt B) * V₀ ^ k * Real.sqrt V₀ := by
        have e3 : Real.sqrt s ^ 3 = s * Real.sqrt s := by rw [pow_succ, hs2]
        rw [e3]; ring
    _ ≤ s * W * Real.sqrt (V₀ + s * B) * (V₀ + s * B) ^ k * Real.sqrt (V₀ + s * B) := by
        have := mul_nonneg hs hW
        gcongr
    _ = s * W * (Real.sqrt (V₀ + s * B) * Real.sqrt (V₀ + s * B)) * (V₀ + s * B) ^ k := by
        ring
    _ = s * W * ((V₀ + s * B) ^ k * (V₀ + s * B)) := by rw [hsq2]; ring

end QED.GradedProof.RPi4

end
