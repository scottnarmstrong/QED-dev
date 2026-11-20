/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecRep
public import QED.GradedProof.RPi4MajRed
public import QED.GradedProof.RPi4MajGrow

/-!
# (R-Π₄) step L10: the limit majorant from global bounds on the scaling profiles

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, limit part
`MajLimBound`. Under the generic face-limit identity, the photon-regulator limit is a sum of
blocks of the per-flavour function `decT₀` (`dec_rep_decT₀`, step L9). If `decT₀` has the scaling
form `G(s/x) + κ log(x/μ²) φ(s/x)` up to an affine function of `x` (killed by a block), a block
is `h(μ²) + c₁ h(M₁²) + c₂ h(M₂²)` with `h(x) = G(s/x) + κ log(x/μ²) φ(s/x)`, and the
divided-difference bound `dec_norm_pv_le` controls the regulator terms, uniformly in the
coefficients, as soon as `h` is bounded and Lipschitz on the scale of `x`. This needs only
global bounds on the profiles:

* `MajScalGlob e`: the scaling form (as in `DecScalAff`) with `‖G(τ)‖ ≤ B w(τ)²`,
  `‖φ(τ)‖ ≤ B min(τ, 1) w(τ)` and the matching scale-Lipschitz bounds
  `‖f(τ) - f(τ')‖ ≤ (…) (τ - τ')/τ'`, `w(τ) = 1 + log(1 + τ)`;
* `maj_log_mul_min_le`: `log X · min(t/X, 1) ≤ w(t)` for `X ≥ 1`;
* `maj_norm_decT_le`, `maj_norm_decT_sub_le`, `maj_norm_decBlock_le`: the block bound
  `3B(1 + 2‖κ‖) w(s/μ²)²`;
* `maj_limBound_of_scalGlob`: **`DecFaceGen → MajScalGlob → MajLimBound`**.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

/-- **Global bounds on the scaling profiles**: the per-flavour function `decT₀` has the scaling
form up to an affine function of `x`, and its profiles grow at most like `w(τ)²` (`G`) and
`min(τ, 1) w(τ)` (`φ`), with matching bounds on the scale of `τ`. -/
def MajScalGlob (e : ℝ) : Prop :=
  ∃ (G φ : ℝ → ℂ) (κ : ℂ) (B : ℝ) (α β : ℝ → ℝ → ℂ), φ 0 = 0 ∧
    (∀ τ, 0 ≤ τ → ‖G τ‖ ≤ B * majW τ ^ 2) ∧
    (∀ τ τ', 0 < τ' → τ' ≤ τ → ‖G τ - G τ'‖ ≤ B * majW τ ^ 2 * ((τ - τ') / τ')) ∧
    (∀ τ, 0 ≤ τ → ‖φ τ‖ ≤ B * min τ 1 * majW τ) ∧
    (∀ τ τ', 0 < τ' → τ' ≤ τ → ‖φ τ - φ τ'‖ ≤ B * min τ 1 * majW τ * ((τ - τ') / τ')) ∧
    ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
      decT₀ e μ x s = decT G φ κ μ x s + (α μ s + β μ s * x)

/-- `log X · min(t/X, 1) ≤ w(t)` for `X ≥ 1`, `t ≥ 0`. -/
theorem maj_log_mul_min_le {X t : ℝ} (hX : 1 ≤ X) (ht : 0 ≤ t) :
    Real.log X * min (t / X) 1 ≤ majW t := by
  have hX0 : 0 < X := one_pos.trans_le hX
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hl1 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  simp only [majW]
  rcases le_or_gt 1 (t / X) with h | h
  · rw [min_eq_right h, mul_one]
    have hXt : X ≤ t := by rwa [le_div_iff₀ hX0, one_mul] at h
    have := Real.log_le_log hX0 (by linarith : X ≤ 1 + t)
    linarith
  · rw [min_eq_left h.le]
    rcases ht.eq_or_lt with rfl | ht0
    · simp
    have hq : 0 < t / X := by positivity
    have e : Real.log X = Real.log t + Real.log (X / t) := by
      rw [← Real.log_mul ht0.ne' (by positivity)]
      congr 1
      field_simp
    have h1 : t / X * Real.log (X / t) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < X / t by positivity)
      calc t / X * Real.log (X / t) ≤ t / X * (X / t - 1) := mul_le_mul_of_nonneg_left this hq.le
        _ = 1 - t / X := by field_simp
        _ ≤ 1 := by linarith
    have h2 : t / X * Real.log t ≤ Real.log (1 + t) := by
      rcases le_or_gt 0 (Real.log t) with hl | hl
      · have := Real.log_le_log ht0 (by linarith : t ≤ 1 + t)
        nlinarith
      · nlinarith
    rw [e]
    nlinarith

section Block

variable {G φ : ℝ → ℂ} {κ : ℂ} {B : ℝ}
  (hφ0 : φ 0 = 0)
  (hG : ∀ τ, 0 ≤ τ → ‖G τ‖ ≤ B * majW τ ^ 2)
  (hGL : ∀ τ τ', 0 < τ' → τ' ≤ τ → ‖G τ - G τ'‖ ≤ B * majW τ ^ 2 * ((τ - τ') / τ'))
  (hφ : ∀ τ, 0 ≤ τ → ‖φ τ‖ ≤ B * min τ 1 * majW τ)
  (hφL : ∀ τ τ', 0 < τ' → τ' ≤ τ → ‖φ τ - φ τ'‖ ≤ B * min τ 1 * majW τ * ((τ - τ') / τ'))

include hG in
theorem maj_B_nonneg : 0 ≤ B := by
  have := (norm_nonneg _).trans (hG 0 le_rfl)
  simpa [majW] using this

include hG hφ in
/-- The per-flavour scaling form is bounded by `B (1 + ‖κ‖) w(s/μ²)²` for `x ≥ μ²`. -/
theorem maj_norm_decT_le {μ x s : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hs : 0 ≤ s) :
    ‖decT G φ κ μ x s‖ ≤ B * (1 + ‖κ‖) * majW (s / μ ^ 2) ^ 2 := by
  have hB := maj_B_nonneg hG
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hx0 : 0 < x := hμ2.trans_le hx
  have hX : 1 ≤ x / μ ^ 2 := by rwa [le_div_iff₀ hμ2, one_mul]
  have hσ : 0 ≤ s / μ ^ 2 := by positivity
  have hτ : 0 ≤ s / x := by positivity
  have hτσ : s / x ≤ s / μ ^ 2 := div_le_div_of_nonneg_left hs hμ2 hx
  have e : s / x = s / μ ^ 2 / (x / μ ^ 2) := by field_simp
  have hw := majW_mono hτ hτσ
  have hw1 := maj_one_le_majW hσ
  have hlog := maj_log_mul_min_le hX hσ
  rw [← e] at hlog
  have hl0 : 0 ≤ Real.log (x / μ ^ 2) := Real.log_nonneg hX
  have h1 : ‖G (s / x)‖ ≤ B * majW (s / μ ^ 2) ^ 2 :=
    (hG _ hτ).trans (by gcongr; exact (majW_pos hτ).le)
  have h2 : ‖κ * (Real.log (x / μ ^ 2) : ℂ) * φ (s / x)‖ ≤ ‖κ‖ * (B * majW (s / μ ^ 2) ^ 2) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hmin0 : 0 ≤ min (s / x) 1 := le_min hτ zero_le_one
    calc Real.log (x / μ ^ 2) * ‖φ (s / x)‖ ≤
          Real.log (x / μ ^ 2) * (B * min (s / x) 1 * majW (s / x)) :=
          mul_le_mul_of_nonneg_left (hφ _ hτ) hl0
      _ = B * (Real.log (x / μ ^ 2) * min (s / x) 1) * majW (s / x) := by ring
      _ ≤ B * majW (s / μ ^ 2) * majW (s / μ ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlog hB) hw (majW_pos hτ).le
            (mul_nonneg hB (majW_pos hσ).le)
      _ = B * majW (s / μ ^ 2) ^ 2 := by ring
  calc ‖decT G φ κ μ x s‖ ≤ ‖G (s / x)‖ + ‖κ * (Real.log (x / μ ^ 2) : ℂ) * φ (s / x)‖ :=
        norm_add_le _ _
    _ ≤ B * majW (s / μ ^ 2) ^ 2 + ‖κ‖ * (B * majW (s / μ ^ 2) ^ 2) := add_le_add h1 h2
    _ = B * (1 + ‖κ‖) * majW (s / μ ^ 2) ^ 2 := by ring

include hφ0 hG hGL hφ hφL in
/-- The per-flavour scaling form is Lipschitz on the scale of `x` beyond `μ²`, with the constant
`B (1 + 2‖κ‖) w(s/μ²)²`. -/
theorem maj_norm_decT_sub_le {μ x y s : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hxy : x ≤ y)
    (hs : 0 ≤ s) :
    ‖decT G φ κ μ y s - decT G φ κ μ x s‖ ≤
      B * (1 + 2 * ‖κ‖) * majW (s / μ ^ 2) ^ 2 * ((y - x) / x) := by
  have hB := maj_B_nonneg hG
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hx0 : 0 < x := hμ2.trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hr : 0 ≤ (y - x) / x := div_nonneg (by linarith) hx0.le
  have hσ : 0 ≤ s / μ ^ 2 := by positivity
  have hw1 := maj_one_le_majW hσ
  have hK : 0 ≤ B * (1 + 2 * ‖κ‖) * majW (s / μ ^ 2) ^ 2 * ((y - x) / x) := by positivity
  rcases hs.eq_or_lt with rfl | hs0
  · simpa [decT, hφ0] using hK
  have hτ : 0 < s / x := by positivity
  have hτ' : 0 < s / y := by positivity
  have hττ : s / y ≤ s / x := div_le_div_of_nonneg_left hs hx0 hxy
  have hτσ : s / x ≤ s / μ ^ 2 := div_le_div_of_nonneg_left hs hμ2 hx
  have hratio : (s / x - s / y) / (s / y) = (y - x) / x := by field_simp
  have hX : 1 ≤ x / μ ^ 2 := by rwa [le_div_iff₀ hμ2, one_mul]
  have hl0 : 0 ≤ Real.log (x / μ ^ 2) := Real.log_nonneg hX
  have hw := majW_mono hτ.le hτσ
  have hw' := majW_mono hτ'.le (hττ.trans hτσ)
  have e : s / x = s / μ ^ 2 / (x / μ ^ 2) := by field_simp
  have hlog := maj_log_mul_min_le hX hσ
  rw [← e] at hlog
  -- the three pieces
  have hlyx : Real.log (y / μ ^ 2) - Real.log (x / μ ^ 2) = Real.log (y / x) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlyx0 : 0 ≤ Real.log (y / x) := Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith)
  have hlyx1 : Real.log (y / x) ≤ (y - x) / x := by
    have := Real.log_le_sub_one_of_pos (show 0 < y / x by positivity)
    rw [sub_div, div_self hx0.ne']
    exact this
  have split : decT G φ κ μ y s - decT G φ κ μ x s =
      -(G (s / x) - G (s / y)) + κ * ((Real.log (y / x) : ℂ) * φ (s / y)) -
        κ * ((Real.log (x / μ ^ 2) : ℂ) * (φ (s / x) - φ (s / y))) := by
    simp only [decT]
    rw [← hlyx]
    push_cast
    ring
  have h1 : ‖G (s / x) - G (s / y)‖ ≤ B * majW (s / μ ^ 2) ^ 2 * ((y - x) / x) := by
    refine (hGL _ _ hτ' hττ).trans ?_
    rw [hratio]
    gcongr
    exact (majW_pos hτ.le).le
  have h2 : ‖(Real.log (y / x) : ℂ) * φ (s / y)‖ ≤ B * majW (s / μ ^ 2) ^ 2 * ((y - x) / x) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlyx0]
    have hφy := hφ _ hτ'.le
    have hm : B * min (s / y) 1 * majW (s / y) ≤ B * majW (s / μ ^ 2) ^ 2 := by
      have : min (s / y) 1 ≤ 1 := min_le_right _ _
      have hmin0 : 0 ≤ min (s / y) 1 := le_min hτ'.le zero_le_one
      calc B * min (s / y) 1 * majW (s / y) ≤ B * 1 * majW (s / μ ^ 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left this hB) hw' (majW_pos hτ'.le).le
              (by positivity)
        _ ≤ B * majW (s / μ ^ 2) ^ 2 := by
            have := mul_le_mul_of_nonneg_left
              (show majW (s / μ ^ 2) ≤ majW (s / μ ^ 2) ^ 2 by nlinarith) hB
            linarith
    calc Real.log (y / x) * ‖φ (s / y)‖ ≤ ((y - x) / x) * (B * majW (s / μ ^ 2) ^ 2) :=
          mul_le_mul hlyx1 (hφy.trans hm) (norm_nonneg _) hr
      _ = _ := by ring
  have h3 : ‖(Real.log (x / μ ^ 2) : ℂ) * (φ (s / x) - φ (s / y))‖ ≤
      B * majW (s / μ ^ 2) ^ 2 * ((y - x) / x) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0]
    have hφd := hφL _ _ hτ' hττ
    rw [hratio] at hφd
    have hmin0 : 0 ≤ min (s / x) 1 := le_min hτ.le zero_le_one
    calc Real.log (x / μ ^ 2) * ‖φ (s / x) - φ (s / y)‖ ≤
          Real.log (x / μ ^ 2) * (B * min (s / x) 1 * majW (s / x) * ((y - x) / x)) :=
          mul_le_mul_of_nonneg_left hφd hl0
      _ = B * (Real.log (x / μ ^ 2) * min (s / x) 1) * majW (s / x) * ((y - x) / x) := by ring
      _ ≤ B * majW (s / μ ^ 2) * majW (s / μ ^ 2) * ((y - x) / x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hlog hB) hw
            (majW_pos hτ.le).le (mul_nonneg hB (majW_pos hσ).le)) hr
      _ = _ := by ring
  rw [split]
  calc _ ≤ ‖-(G (s / x) - G (s / y)) + κ * ((Real.log (y / x) : ℂ) * φ (s / y))‖ +
        ‖κ * ((Real.log (x / μ ^ 2) : ℂ) * (φ (s / x) - φ (s / y)))‖ := norm_sub_le _ _
    _ ≤ ‖G (s / x) - G (s / y)‖ + ‖κ‖ * ‖(Real.log (y / x) : ℂ) * φ (s / y)‖ +
        ‖κ‖ * ‖(Real.log (x / μ ^ 2) : ℂ) * (φ (s / x) - φ (s / y))‖ := by
        gcongr
        · exact (norm_add_le _ _).trans (by rw [norm_neg, norm_mul])
        · rw [norm_mul]
    _ ≤ B * majW (s / μ ^ 2) ^ 2 * ((y - x) / x) +
        ‖κ‖ * (B * majW (s / μ ^ 2) ^ 2 * ((y - x) / x)) +
        ‖κ‖ * (B * majW (s / μ ^ 2) ^ 2 * ((y - x) / x)) := by gcongr
    _ = _ := by ring

include hφ0 hG hGL hφ hφL in
/-- **A block of the scaling form** is bounded by `3B(1 + 2‖κ‖) w(s/μ²)²`, uniformly in the
regulator masses and coefficients. -/
theorem maj_norm_decBlock_le {μ M₁ M₂ c₁ c₂ s : ℝ} (hμ : 0 < μ) (h₁ : μ < M₁) (h₂ : μ < M₂)
    (hc : 1 + c₁ + c₂ = 0) (hc' : μ ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (hs : 0 ≤ s) :
    ‖decBlock (decT G φ κ) μ M₁ M₂ c₁ c₂ s‖ ≤
      3 * (B * (1 + 2 * ‖κ‖)) * majW (s / μ ^ 2) ^ 2 := by
  have hB := maj_B_nonneg hG
  set E : ℝ := B * (1 + 2 * ‖κ‖) * majW (s / μ ^ 2) ^ 2 with hE
  have hsq : ∀ {M : ℝ}, μ < M → μ ^ 2 < M ^ 2 := fun hM => pow_lt_pow_left₀ hM hμ.le two_ne_zero
  have hr : ∀ x, μ ^ 2 ≤ x → ‖decT G φ κ μ x s‖ ≤ E := fun x hx =>
    (maj_norm_decT_le hG hφ hμ hx hs).trans (by
      rw [hE]
      gcongr
      linarith [norm_nonneg κ])
  have hL : ∀ x y, μ ^ 2 ≤ x → x ≤ y →
      ‖decT G φ κ μ y s - decT G φ κ μ x s‖ ≤ E * ((y - x) / x) := fun x y hx hxy =>
    maj_norm_decT_sub_le hφ0 hG hGL hφ hφL hμ hx hxy hs
  have hpv := dec_norm_pv_le (r := fun x => decT G φ κ μ x s) hc hc' (by positivity) (hsq h₁)
    (hsq h₂) (hsq h₁).le (hsq h₂).le hr hL
  have h0 := hr (μ ^ 2) le_rfl
  simp only [decBlock]
  calc _ ≤ ‖decT G φ κ μ (μ ^ 2) s‖ +
        ‖(c₁ : ℂ) * decT G φ κ μ (M₁ ^ 2) s + (c₂ : ℂ) * decT G φ κ μ (M₂ ^ 2) s‖ := by
        rw [add_assoc]
        exact norm_add_le _ _
    _ ≤ E + 2 * E := add_le_add h0 hpv
    _ = _ := by rw [hE]; ring

end Block

section Frozen

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **(L10, limit part) `MajLimBound` from global bounds on the scaling profiles**, given the
generic face-limit identity. -/
theorem maj_limBound_of_scalGlob (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) (h : MajScalGlob P₀.e) : MajLimBound P₀ mH := by
  obtain ⟨G, φ, κ, B, α, β, hφ0, hG, hGL, hφ, hφL, hT⟩ := h
  have hB := maj_B_nonneg hG
  set E₀ : ℝ := 3 * (B * (1 + 2 * ‖κ‖)) with hE₀
  have hE₀0 : 0 ≤ E₀ := by positivity
  refine ⟨(n + 1) * E₀, 0, fun M₁ M₂ c₁ c₂ hM₁ hM₂ _ _ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ _ _
    hcH₁ hcH₂ s hs => ?_⟩
  have hs4 : -(4 * P₀.m ^ 2) < s := by nlinarith
  rw [dec_rep_decT₀ P₀ mH he hm hmH hF M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂
    hcH₁ hcH₂ s hs4]
  have hsq : ∀ {μ M : ℝ}, 0 < μ → μ < M → μ ^ 2 ≤ M ^ 2 := fun hμ hM =>
    pow_le_pow_left₀ hμ.le hM.le 2
  -- each block, with the affine part removed
  have hblock : ∀ {μ N₁ N₂ d₁ d₂ : ℝ}, P₀.m ≤ μ → μ < N₁ → μ < N₂ → 1 + d₁ + d₂ = 0 →
      μ ^ 2 + d₁ * N₁ ^ 2 + d₂ * N₂ ^ 2 = 0 →
      ‖decBlock (decT₀ P₀.e) μ N₁ N₂ d₁ d₂ s‖ ≤ E₀ * majW (s / P₀.m ^ 2) ^ 2 := by
    intro μ N₁ N₂ d₁ d₂ hmμ h₁ h₂ hd hd'
    have hμ : 0 < μ := hm.trans_le hmμ
    have hsμ : -(4 * μ ^ 2) < s := by nlinarith
    have e : decBlock (decT₀ P₀.e) μ N₁ N₂ d₁ d₂ s = decBlock (decT G φ κ) μ N₁ N₂ d₁ d₂ s := by
      refine dec_decBlock_add_affine (α μ s) (β μ s) hd hd' fun x hx' => ?_
      refine hT μ x s hμ ?_ hsμ
      rcases hx' with rfl | rfl | rfl
      · exact le_rfl
      · exact hsq hμ h₁
      · exact hsq hμ h₂
    rw [e]
    refine (maj_norm_decBlock_le hφ0 hG hGL hφ hφL hμ h₁ h₂ hd hd' hs).trans ?_
    have hσ : s / μ ^ 2 ≤ s / P₀.m ^ 2 :=
      div_le_div_of_nonneg_left hs (by positivity) (pow_le_pow_left₀ hm.le hmμ 2)
    have hw := majW_mono (by positivity) hσ
    have hw0 := (majW_pos (show 0 ≤ s / μ ^ 2 by positivity)).le
    rw [← hE₀]
    gcongr
  have hw0 : 0 ≤ E₀ * majW (s / P₀.m ^ 2) ^ 2 := by positivity
  have hA := hblock le_rfl hM₁ hM₂ hc₁ hc₂
  have hH : ∀ ℓ, ‖decBlock (decT₀ P₀.e) (mH ℓ) (MH₁ ℓ) (MH₂ ℓ) (cH₁ ℓ) (cH₂ ℓ) s‖ ≤
      E₀ * majW (s / P₀.m ^ 2) ^ 2 := fun ℓ =>
    hblock (hmH ℓ).le (hMH₁ ℓ) (hMH₂ ℓ) (hcH₁ ℓ) (hcH₂ ℓ)
  have hS : ‖∑ ℓ, decBlock (decT₀ P₀.e) (mH ℓ) (MH₁ ℓ) (MH₂ ℓ) (cH₁ ℓ) (cH₂ ℓ) s‖ ≤
      n * (E₀ * majW (s / P₀.m ^ 2) ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _ℓ : Fin n, E₀ * majW (s / P₀.m ^ 2) ^ 2 := Finset.sum_le_sum fun ℓ _ => hH ℓ
      _ = _ := by simp
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ E₀ * majW (s / P₀.m ^ 2) ^ 2 + n * (E₀ * majW (s / P₀.m ^ 2) ^ 2) := add_le_add hA hS
    _ = (n + 1) * E₀ * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 := by simp only [majW]; ring

end Frozen

end QED.GradedProof.RPi4

end
