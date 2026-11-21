/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajFlow

/-!
# (R-Π₄) step L10, T2.UV: the gain of a piece along the ray from a cut lower bound of `B`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (input (A) of
`QED.GradedProof.RPi4.faceIdRay_of_size_rate`, see `QED.GradedProof.RPi4.FaceIdRayAPow`). Along
the ray the Symanzik `V` of a piece is `V₀ + s B` with `B = remainder α z q`; a term of the
parametric integrand of order `s (sB)^e / W^r` (`W ≥ V₀ + sB`, `r ≥ e + δ`) is at most
`s^{1-δ} B^{-δ} V₀^{e+δ-r}` (`faceIdRayA_gain_le`): the gain `s^{-δ}` costs the weight `B^{-δ}`.
That weight is a small power of Feynman parameters: if the affine system
`αₜ·y + qₜ = 0`, `t ∈ T`, has no solution, uniformly `∑_{t ∈ T} (αₜ·y + qₜ)² ≥ c > 0`, then
`B ≥ c min_{t ∈ T} zₜ ≥ c ∏_{t ∈ T} zₜ` (`faceIdRayA_remainder_ge`,
`faceIdRayA_remainder_ge_prod`), so `B^{-δ} ≤ c^{-δ} ∏_{t ∈ T} zₜ^{-δ}`
(`faceIdRayA_rpow_neg_remainder_le`). For the three directions `(1,0)`, `(0,1)`, `(1,-1)` the
constant is `(q₀ - q₁ - q₂)²/3` (`faceIdRayA_three_sq_ge`).

* `faceIdRayA_gain_le`;
* `faceIdRayA_remainder_ge`, `faceIdRayA_remainder_ge_prod`, `faceIdRayA_rpow_neg_remainder_le`;
* `faceIdRayA_three_sq_ge`, `faceIdRayA_two_sq_ge`, `faceIdRayA_cut_pair` (two parallel lines
  with different shifts, as the lines `0`, `3` of `VA` and `VB`, `0`, `1` of `VC`).
-/

@[expose] public section

open Matrix

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {m : ℕ}

/-- **The gain along the ray**: `s (sB)^e / W^r ≤ s^{1-δ} B^{-δ} V₀^{e+δ-r}` for
`W ≥ V₀ + sB`, `V₀, B, s > 0`, `e, δ ≥ 0`, `e + δ ≤ r`. -/
theorem faceIdRayA_gain_le {V₀ B s W e δ r : ℝ} (hV₀ : 0 < V₀) (hB : 0 < B) (hs : 0 < s)
    (hW : V₀ + s * B ≤ W) (he : 0 ≤ e) (hδ : 0 ≤ δ) (hr : e + δ ≤ r) :
    s * (s * B) ^ e / W ^ r ≤ s ^ (1 - δ) * B ^ (-δ) * V₀ ^ (e + δ - r) := by
  have hsB : 0 < s * B := mul_pos hs hB
  have hW0 : 0 < W := by linarith
  have h1 : (s * B) ^ (e + δ) ≤ W ^ (e + δ) :=
    Real.rpow_le_rpow hsB.le (by linarith) (by linarith)
  have h2 : W ^ (e + δ - r) ≤ V₀ ^ (e + δ - r) :=
    Real.rpow_le_rpow_of_nonpos hV₀ (by linarith) (by linarith)
  have e1 : s * (s * B) ^ e = s ^ (1 - δ) * B ^ (-δ) * (s * B) ^ (e + δ) := by
    rw [Real.rpow_add hsB, Real.mul_rpow hs.le hB.le, Real.mul_rpow hs.le hB.le,
      Real.rpow_neg hB.le, Real.rpow_sub hs, Real.rpow_one]
    field_simp
  have e2 : W ^ (e + δ) / W ^ r = W ^ (e + δ - r) := (Real.rpow_sub hW0 _ _).symm
  have hc : 0 ≤ s ^ (1 - δ) * B ^ (-δ) := by positivity
  rw [e1, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  calc (s * B) ^ (e + δ) / W ^ r ≤ W ^ (e + δ) / W ^ r :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = W ^ (e + δ - r) := e2
    _ ≤ V₀ ^ (e + δ - r) := h2

/-- **`B` from a cut**: if `∑_{t ∈ T} (αₜ·y + qₜ)² ≥ c` for all `y`, then `c w ≤ B` whenever
`0 ≤ w ≤ zₜ` for `t ∈ T`. -/
theorem faceIdRayA_remainder_ge (α : Fin (m + 1) → Fin 2 → ℝ) {z q : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hdet : symanzikU α z ≠ 0) (T : Finset (Fin (m + 1))) {c w : ℝ}
    (hc : ∀ y : Fin 2 → ℝ, c ≤ ∑ t ∈ T, (∑ s, α t s * y s + q t) ^ 2)
    (hw0 : 0 ≤ w) (hw : ∀ t ∈ T, w ≤ z t) :
    c * w ≤ remainder α z q := by
  rw [maj_remainder_eq_flow α hdet q]
  have h1 : ∑ t ∈ T, z t * majFlow α z q t ^ 2 ≤ ∑ i, z i * majFlow α z q i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      fun i _ _ => mul_nonneg (hz i) (sq_nonneg _)
  have h2 : w * ∑ t ∈ T, majFlow α z q t ^ 2 ≤ ∑ t ∈ T, z t * majFlow α z q t ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_right (hw t ht) (sq_nonneg _)
  have h3 : c ≤ ∑ t ∈ T, majFlow α z q t ^ 2 :=
    hc (-((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q))
  have h4 := mul_le_mul_of_nonneg_left h3 hw0
  linarith [mul_comm c w]

/-- **`B` from a cut, product form**: `c ∏_{t ∈ T} zₜ ≤ B` on the unit cube. -/
theorem faceIdRayA_remainder_ge_prod (α : Fin (m + 1) → Fin 2 → ℝ) {z q : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (hdet : symanzikU α z ≠ 0)
    (T : Finset (Fin (m + 1))) {c : ℝ}
    (hc : ∀ y : Fin 2 → ℝ, c ≤ ∑ t ∈ T, (∑ s, α t s * y s + q t) ^ 2) :
    c * ∏ t ∈ T, z t ≤ remainder α z q := by
  classical
  refine faceIdRayA_remainder_ge α hz hdet T hc (Finset.prod_nonneg fun i _ => hz i)
    fun t ht => ?_
  rw [← Finset.mul_prod_erase T z ht]
  calc z t * ∏ i ∈ T.erase t, z i ≤ z t * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun i _ => hz i) fun i _ => hz1 i) (hz t)
    _ = z t := mul_one _

/-- **The weight of the gain**: `B^{-δ} ≤ c^{-δ} ∏_{t ∈ T} zₜ^{-δ}` for a cut with `c > 0`,
at points with all `zₜ > 0` (`t ∈ T`) in the unit cube. -/
theorem faceIdRayA_rpow_neg_remainder_le (α : Fin (m + 1) → Fin 2 → ℝ)
    {z q : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1)
    (hdet : symanzikU α z ≠ 0) (T : Finset (Fin (m + 1))) {c δ : ℝ} (hc0 : 0 < c)
    (hδ : 0 ≤ δ) (hT : ∀ t ∈ T, 0 < z t)
    (hc : ∀ y : Fin 2 → ℝ, c ≤ ∑ t ∈ T, (∑ s, α t s * y s + q t) ^ 2) :
    remainder α z q ^ (-δ) ≤ c ^ (-δ) * ∏ t ∈ T, z t ^ (-δ) := by
  have hP : 0 < ∏ t ∈ T, z t := Finset.prod_pos hT
  have h := faceIdRayA_remainder_ge_prod α hz hz1 hdet T hc
  have hcP : 0 < c * ∏ t ∈ T, z t := mul_pos hc0 hP
  calc remainder α z q ^ (-δ) ≤ (c * ∏ t ∈ T, z t) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos hcP h (by linarith)
    _ = c ^ (-δ) * ∏ t ∈ T, z t ^ (-δ) := by
        rw [Real.mul_rpow hc0.le hP.le, Real.finsetProd_rpow T z fun i _ => (hT i ‹_›).le]

/-- **The cut constant of three directions** `(1,0)`, `(0,1)`, `(1,-1)`:
`(y₀ + a)² + (y₁ + b)² + (y₀ - y₁ + d)² ≥ (a - b - d)²/3`. -/
theorem faceIdRayA_three_sq_ge (y₀ y₁ a b d : ℝ) :
    (a - b - d) ^ 2 / 3 ≤ (y₀ + a) ^ 2 + (y₁ + b) ^ 2 + (y₀ - y₁ + d) ^ 2 := by
  nlinarith [sq_nonneg (y₀ + a + (y₁ + b)), sq_nonneg (y₀ + a + (y₀ - y₁ + d)),
    sq_nonneg (y₁ + b - (y₀ - y₁ + d))]

/-- **The cut constant of two parallel lines**: `(x + a)² + (x + b)² ≥ (a - b)²/2`. -/
theorem faceIdRayA_two_sq_ge (x a b : ℝ) : (a - b) ^ 2 / 2 ≤ (x + a) ^ 2 + (x + b) ^ 2 := by
  nlinarith [sq_nonneg (2 * x + a + b)]

/-- **A cut from two parallel lines with different shifts**: if `α t₁ = α t₂`, `t₁ ≠ t₂`, then
`∑_{t ∈ {t₁, t₂}} (αₜ·y + qₜ)² ≥ (q t₁ - q t₂)²/2` for all `y`. -/
theorem faceIdRayA_cut_pair (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → ℝ)
    {t₁ t₂ : Fin (m + 1)} (hne : t₁ ≠ t₂) (h : α t₁ = α t₂) (y : Fin 2 → ℝ) :
    (q t₁ - q t₂) ^ 2 / 2 ≤ ∑ t ∈ {t₁, t₂}, (∑ s, α t s * y s + q t) ^ 2 := by
  rw [Finset.sum_pair hne, ← h]
  exact faceIdRayA_two_sq_ge _ _ _

end QED.GradedProof.RPi4

end
