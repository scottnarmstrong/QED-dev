/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# (R-Π₄) step L10: growth from halving identities

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the majorant).
The profiles `G`, `φ` of the scaling form of the decoupling (step L9) obey, at the fixed
configuration `x = 4`, exact halving identities `2a(s) - a(s/2) = v(s)` for the increments
`a(s) = G(s) - G(s/2)`. Two model-free lemmas turn bounds on `v` into global growth bounds:

* `maj_norm_le_of_halving`: if `2u(s) - u(s/2) = v(s)` for `s ≥ 0`, `‖v‖ ≤ V` with `V`
  monotone, and `u = O(s)` near `0`, then `‖u‖ ≤ V` (the weights `2^{-k-1}` sum to `1`);
* `maj_norm_le_of_telescope`: if `‖u(s) - u(s/2)‖ ≤ W(s)` with `W` monotone and `u` bounded
  near `0`, then `‖u(s)‖ ≤ K₀ + C_δ w(s) W(s)`, `w(s) = 1 + log(1 + s)`: telescoping costs
  one logarithm.
-/

@[expose] public section

open Filter Topology

namespace QED.GradedProof.RPi4

/-- The logarithmic weight `w(s) = 1 + log(1 + s)`. -/
noncomputable def majW (s : ℝ) : ℝ := 1 + Real.log (1 + s)

theorem maj_one_le_majW {s : ℝ} (hs : 0 ≤ s) : 1 ≤ majW s := by
  have : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith)
  simp only [majW]
  linarith

theorem majW_pos {s : ℝ} (hs : 0 ≤ s) : 0 < majW s :=
  one_pos.trans_le (maj_one_le_majW hs)

theorem majW_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : majW s ≤ majW t := by
  have := Real.log_le_log (by linarith) (by linarith : 1 + s ≤ 1 + t)
  simp only [majW]
  linarith

/-! ### Halving -/

section Halving

variable {u v : ℝ → ℂ} {V : ℝ → ℝ} {δ K : ℝ}

theorem maj_norm_le_add_halving (huv : ∀ s, 0 ≤ s → 2 * u s - u (s / 2) = v s)
    (hv : ∀ s, 0 ≤ s → ‖v s‖ ≤ V s) (hV : ∀ s t, 0 ≤ s → s ≤ t → V s ≤ V t) :
    ∀ n : ℕ, ∀ s, 0 ≤ s → ‖u s‖ ≤ V s + ‖u (s / 2 ^ n)‖ / 2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro s hs
    have := (norm_nonneg _).trans (hv s hs)
    simp only [pow_zero, div_one]
    linarith
  | succ n ih =>
    intro s hs
    have hs2 : 0 ≤ s / 2 := by positivity
    have e : u s = (v s + u (s / 2)) / 2 := by
      rw [← huv s hs]
      ring
    have h1 : ‖u s‖ ≤ (‖v s‖ + ‖u (s / 2)‖) / 2 := by
      rw [e, norm_div, Complex.norm_two]
      gcongr
      exact norm_add_le _ _
    have h2 := ih (s / 2) hs2
    rw [show s / 2 / 2 ^ n = s / 2 ^ (n + 1) by rw [pow_succ]; ring] at h2
    have h3 := hV (s / 2) s hs2 (by linarith)
    have h4 := hv s hs
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have e2 : ‖u (s / 2 ^ (n + 1))‖ / 2 ^ (n + 1) =
        ‖u (s / 2 ^ (n + 1))‖ / 2 ^ n / 2 := by
      rw [pow_succ]
      ring
    rw [e2]
    linarith

/-- **Halving**: `2u(s) - u(s/2) = v(s)` with `‖v‖ ≤ V` monotone and `u = O(s)` near `0` give
`‖u‖ ≤ V`. -/
theorem maj_norm_le_of_halving (hδ : 0 < δ) (huv : ∀ s, 0 ≤ s → 2 * u s - u (s / 2) = v s)
    (hv : ∀ s, 0 ≤ s → ‖v s‖ ≤ V s) (hV : ∀ s t, 0 ≤ s → s ≤ t → V s ≤ V t)
    (hu0 : ∀ s, 0 ≤ s → s ≤ δ → ‖u s‖ ≤ K * s) {s : ℝ} (hs : 0 ≤ s) : ‖u s‖ ≤ V s := by
  have hq : Tendsto (fun n : ℕ => s * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).const_mul s
  have hlim : Tendsto (fun n : ℕ => V s + K * (s * (2⁻¹ : ℝ) ^ n) * (2⁻¹ : ℝ) ^ n) atTop
      (𝓝 (V s)) := by
    have h2 : Tendsto (fun n : ℕ => (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using tendsto_const_nhds.add ((hq.const_mul K).mul h2)
  refine ge_of_tendsto hlim ?_
  filter_upwards [hq.eventually_le_const hδ] with n hn
  have h1 := maj_norm_le_add_halving huv hv hV n s hs
  have e : s / 2 ^ n = s * (2⁻¹ : ℝ) ^ n := by rw [inv_pow, div_eq_mul_inv]
  rw [e] at h1
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h0 : 0 ≤ s * (2⁻¹ : ℝ) ^ n := by positivity
  have h2 := hu0 _ h0 hn
  have e' : ‖u (s * (2⁻¹ : ℝ) ^ n)‖ / 2 ^ n = ‖u (s * (2⁻¹ : ℝ) ^ n)‖ * (2⁻¹ : ℝ) ^ n := by
    rw [inv_pow, div_eq_mul_inv]
  rw [e'] at h1
  have h3 : ‖u (s * (2⁻¹ : ℝ) ^ n)‖ * (2⁻¹ : ℝ) ^ n ≤ K * (s * (2⁻¹ : ℝ) ^ n) * (2⁻¹ : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  linarith

end Halving

/-! ### Telescoping -/

section Telescope

variable {u a : ℝ → ℂ} {W : ℝ → ℝ} {δ K₀ : ℝ}

theorem maj_norm_le_of_telescope_nat (hua : ∀ s, 0 ≤ s → u s - u (s / 2) = a s)
    (ha : ∀ s, 0 ≤ s → ‖a s‖ ≤ W s) (hW : ∀ s t, 0 ≤ s → s ≤ t → W s ≤ W t)
    (hu0 : ∀ s, 0 ≤ s → s ≤ δ → ‖u s‖ ≤ K₀) :
    ∀ n : ℕ, ∀ s, 0 ≤ s → s ≤ δ * 2 ^ n → ‖u s‖ ≤ K₀ + n * W s := by
  intro n
  induction n with
  | zero =>
    intro s hs hsδ
    simpa using hu0 s hs (by simpa using hsδ)
  | succ n ih =>
    intro s hs hsδ
    have hs2 : 0 ≤ s / 2 := by positivity
    have h1 := ih (s / 2) hs2 (by rw [pow_succ] at hsδ; linarith)
    have e : u s = a s + u (s / 2) := by rw [← hua s hs]; ring
    have h2 := ha s hs
    have h3 := hW (s / 2) s hs2 (by linarith)
    have hW0 : 0 ≤ W (s / 2) := (norm_nonneg _).trans (ha _ hs2)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ‖u s‖ ≤ ‖a s‖ + ‖u (s / 2)‖ := by rw [e]; exact norm_add_le _ _
      _ ≤ W s + (K₀ + n * W (s / 2)) := add_le_add h2 h1
      _ ≤ K₀ + ((n + 1 : ℕ) : ℝ) * W s := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left h3 hn]

/-- The constant of the telescoping bound, `2 (1 + 2 log(1 + 1/δ))`. -/
noncomputable def majC (δ : ℝ) : ℝ := 2 * (1 + 2 * Real.log (1 + δ⁻¹))

theorem majC_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ majC δ := by
  have : 0 ≤ Real.log (1 + δ⁻¹) := Real.log_nonneg (by have := inv_pos.2 hδ; linarith)
  simp only [majC]
  positivity

/-- The number of halvings from `s` down to `δ` is at most `C_δ w(s) - 1`. -/
theorem maj_nat_add_one_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) {n : ℕ}
    (hn : (2 : ℝ) ^ n ≤ s / δ) : (n : ℝ) + 1 ≤ majC δ * majW s := by
  have hlam : 0 ≤ Real.log (1 + δ⁻¹) := Real.log_nonneg (by have := inv_pos.2 hδ; linarith)
  have hℓ : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith)
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h1 : (n : ℝ) * Real.log 2 ≤ Real.log (s / δ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hp hn
  have hsd : s / δ ≤ (1 + s) * (1 + δ⁻¹) := by
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.2 hδ]
  have h2 : Real.log (s / δ) ≤ Real.log (1 + s) + Real.log (1 + δ⁻¹) := by
    rw [← Real.log_mul (by linarith) (by have := inv_pos.2 hδ; linarith)]
    exact Real.log_le_log (hp.trans_le hn) hsd
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have h3 : (n : ℝ) ≤ 2 * (Real.log (1 + s) + Real.log (1 + δ⁻¹)) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  simp only [majC, majW]
  nlinarith [mul_nonneg hlam hℓ]

/-- **Telescoping**: `‖u(s) - u(s/2)‖ ≤ W(s)` with `W` monotone and `‖u‖ ≤ K₀` on `[0, δ]` give
`‖u(s)‖ ≤ K₀ + C_δ w(s) W(s)` for every `s ≥ 0`. -/
theorem maj_norm_le_of_telescope (hδ : 0 < δ) (hua : ∀ s, 0 ≤ s → u s - u (s / 2) = a s)
    (ha : ∀ s, 0 ≤ s → ‖a s‖ ≤ W s) (hW : ∀ s t, 0 ≤ s → s ≤ t → W s ≤ W t)
    (hu0 : ∀ s, 0 ≤ s → s ≤ δ → ‖u s‖ ≤ K₀) {s : ℝ} (hs : 0 ≤ s) :
    ‖u s‖ ≤ K₀ + majC δ * majW s * W s := by
  have hW0 : 0 ≤ W s := (norm_nonneg _).trans (ha s hs)
  have hCw : 0 ≤ majC δ * majW s := mul_nonneg (majC_nonneg hδ) (majW_pos hs).le
  rcases le_or_gt s δ with hsδ | hsδ
  · have := hu0 s hs hsδ
    nlinarith
  · have hx : 1 ≤ s / δ := by rw [le_div_iff₀ hδ]; linarith
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    have hsn : s ≤ δ * 2 ^ (n + 1) := by
      rw [div_lt_iff₀ hδ] at hn'
      linarith
    have h1 := maj_norm_le_of_telescope_nat hua ha hW hu0 (n + 1) s hs hsn
    have h2 := maj_nat_add_one_le hδ hs hn
    push_cast at h1
    nlinarith

end Telescope

end QED.GradedProof.RPi4

end
