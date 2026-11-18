/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerErrOuter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner error terms: domination and pointwise decay

With the bounds of `QED.TwoLoop.UnitSCCorner.abs_cornerE_le` (inner term) and
`QED.TwoLoop.UnitSCCorner.abs_cornerOut_le` (outer pair), for `(y₃, y₄)` in the open triangle and
`0 < x < 1`:

* `abs_cornerErr_le_dom`: for `0 < λ ≤ 1 ≤ Λ`,
  `|e(λ, Λ) + O(Λ; λ, Λ)| ≤ 20 - 3 log y₃ - 6 log(1 - Y) + 1/Y + 5/(Y √g)` (`cornerErrDom`), a bound
  independent of `λ`, `Λ` and `x`;
* `tendsto_cornerErr`: `e(λ, Λ) + O(Λ; λ, Λ) → 0` as `(λ, Λ) → (0⁺, ∞)`, pointwise.
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The dominating function** of the corner error terms on the triangle. -/
noncomputable def cornerErrDom (y3 y4 : ℝ) : ℝ :=
  20 - 3 * log y3 - 6 * log (1 - (y3 + y4)) + 1 / (y3 + y4) +
    5 / ((y3 + y4) * √(cornerG y3 y4))

section Dom

variable {lam Lam x y3 y4 : ℝ}

theorem log_cornerG (h3 : 0 < y3) (hY : y3 + y4 < 1) :
    log (cornerG y3 y4) = log y3 + log (1 - (y3 + y4)) := by
  unfold cornerG
  rw [show 1 - y3 - y4 = 1 - (y3 + y4) by ring, log_mul h3.ne' (by linarith)]

/-- The inner bound is dominated. -/
theorem cornerEBound_le_dom (hLam : 1 ≤ Lam) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    (10 + 2 * log (1 + Lam ^ 2 / cornerG y3 y4)) / cornerN Lam (y3 + y4) ≤
      20 - 3 * log y3 - 6 * log (1 - (y3 + y4)) := by
  have hg := cornerG_pos h3 hY
  have hg4 := cornerG_le_quarter h3 h4
  have hN := two_thirds_le_cornerN hLam (Y := y3 + y4) hY.le
  have hNpos : 0 < cornerN Lam (y3 + y4) := by linarith
  have hL2 : 1 ≤ Lam ^ 2 := by nlinarith
  have h1Y : 0 < 1 - (y3 + y4) := by linarith
  have hNΛ : (1 - (y3 + y4)) * Lam ^ 2 ≤ cornerN Lam (y3 + y4) := by
    unfold cornerN; nlinarith [sq_nonneg (y3 + y4)]
  -- `log(1 + Λ²/g) ≤ log 2 + log Λ² - log g`
  have hl1 : log (1 + Lam ^ 2 / cornerG y3 y4) ≤ log 2 + log (Lam ^ 2) - log (cornerG y3 y4) := by
    have : 1 + Lam ^ 2 / cornerG y3 y4 ≤ 2 * Lam ^ 2 / cornerG y3 y4 := by
      rw [le_div_iff₀ hg, add_mul, div_mul_cancel₀ _ hg.ne']
      nlinarith
    calc log (1 + Lam ^ 2 / cornerG y3 y4) ≤ log (2 * Lam ^ 2 / cornerG y3 y4) :=
          log_le_log (by positivity) this
      _ = log 2 + log (Lam ^ 2) - log (cornerG y3 y4) := by
          rw [log_div (by positivity) hg.ne', log_mul (by norm_num) (by positivity)]
  -- `log Λ² ≤ (1-Y) Λ² - log(1-Y)`
  have hl2 : log (Lam ^ 2) ≤ (1 - (y3 + y4)) * Lam ^ 2 - log (1 - (y3 + y4)) := by
    have := log_le_sub_one_of_pos (by positivity : 0 < (1 - (y3 + y4)) * Lam ^ 2)
    rw [log_mul h1Y.ne' (by positivity)] at this
    linarith
  have hlg := log_cornerG h3 hY
  have hly3 : log y3 ≤ 0 := log_nonpos h3.le (by linarith)
  have hl1Y : log (1 - (y3 + y4)) ≤ 0 := log_nonpos h1Y.le (by linarith)
  have hl2' := log_two_le_one
  have hl20 : 0 ≤ log 2 := log_nonneg (by norm_num)
  set A := 10 + 2 * log 2 - 2 * log y3 - 4 * log (1 - (y3 + y4)) with hA
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hnum : 10 + 2 * log (1 + Lam ^ 2 / cornerG y3 y4) ≤
      A + 2 * ((1 - (y3 + y4)) * Lam ^ 2) := by rw [hA]; linarith
  rw [div_le_iff₀ hNpos]
  have : A ≤ 3 / 2 * A * cornerN Lam (y3 + y4) := by nlinarith
  have hfin : (3 / 2 * A + 2) * cornerN Lam (y3 + y4) ≤
      (20 - 3 * log y3 - 6 * log (1 - (y3 + y4))) * cornerN Lam (y3 + y4) := by
    refine mul_le_mul_of_nonneg_right ?_ hNpos.le
    rw [hA]; linarith
  nlinarith

/-- `2 Y √g x ≤ P` (AM–GM: `Y² + g x ≥ 2 Y √g √x ≥ 2 Y √g x`). -/
theorem two_mul_sqrt_le_cornerP (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4)
    (hY : y3 + y4 < 1) :
    2 * ((y3 + y4) * √(cornerG y3 y4)) * x ≤ cornerP y3 y4 x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hg := cornerG_pos h3 hY
  have hgβ : cornerG y3 y4 ≤ betaG (cornerG y3 y4) (y3 * y4) x := le_betaG _ _ _
  have e12 : (√(cornerG y3 y4) * √x) ^ 2 = cornerG y3 y4 * x := by
    rw [mul_pow, Real.sq_sqrt hg.le, Real.sq_sqrt hx0.le]
  have hsx : x ≤ √x := by
    have h1 : √x ≤ 1 := Real.sqrt_le_one.mpr hx1.le
    have h0 := Real.sqrt_nonneg x
    have := mul_le_mul_of_nonneg_left h1 h0
    nlinarith [Real.sq_sqrt hx0.le]
  have hs := Real.sqrt_nonneg (cornerG y3 y4)
  have hY0 : 0 ≤ y3 + y4 := by linarith
  have amgm : 2 * ((y3 + y4) * √(cornerG y3 y4)) * √x ≤ (y3 + y4) ^ 2 + cornerG y3 y4 * x := by
    nlinarith [sq_nonneg (y3 + y4 - √(cornerG y3 y4) * √x)]
  have : 2 * ((y3 + y4) * √(cornerG y3 y4)) * x ≤ 2 * ((y3 + y4) * √(cornerG y3 y4)) * √x :=
    mul_le_mul_of_nonneg_left hsx (by positivity)
  unfold cornerP
  nlinarith

/-- The outer bound is dominated. -/
theorem cornerOutBound_le_dom (hLam : 1 ≤ Lam) (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3)
    (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    cornerOutBound Lam y3 y4 x ≤ 1 / (y3 + y4) + 5 / ((y3 + y4) * √(cornerG y3 y4)) := by
  have hg := cornerG_pos h3 hY
  have hP := cornerP_pos hx h3 h4 hY
  have hH := one_le_hLam hLam hx
  have hβ : 0 < betaG (cornerG y3 y4) (y3 * y4) x := betaG_pos hg
  have hgβ : cornerG y3 y4 ≤ betaG (cornerG y3 y4) (y3 * y4) x := le_betaG _ _ _
  have hY0 : 0 < y3 + y4 := by linarith
  have hsP : y3 + y4 ≤ √(cornerP y3 y4 x) := by
    rw [← Real.sqrt_sq hY0.le]; exact Real.sqrt_le_sqrt (sq_le_cornerP hx h3 hY)
  have hsH : 1 ≤ √(ladderInnerMass 1 Lam x / x) := by
    have := Real.sqrt_le_sqrt hH
    rwa [Real.sqrt_one] at this
  have hsβ : √(cornerG y3 y4) ≤ √(betaG (cornerG y3 y4) (y3 * y4) x) := Real.sqrt_le_sqrt hgβ
  have hsg : 0 < √(cornerG y3 y4) := Real.sqrt_pos.2 hg
  obtain ⟨hx0, hx1⟩ := hx
  have hamgm := two_mul_sqrt_le_cornerP ⟨hx0, hx1⟩ h3 h4 hY
  have t1 : x ^ 2 / (Lam * √(cornerP y3 y4 x)) ≤ 1 / (y3 + y4) :=
    div_le_div₀ (by norm_num) (by nlinarith) hY0 (by nlinarith)
  have t2 : 3 / 2 * x / (cornerP y3 y4 x * (ladderInnerMass 1 Lam x / x)) ≤
      3 / 4 / ((y3 + y4) * √(cornerG y3 y4)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : cornerP y3 y4 x ≤ cornerP y3 y4 x * (ladderInnerMass 1 Lam x / x) := by nlinarith
    nlinarith
  have t3 : 4 * x / (√(betaG (cornerG y3 y4) (y3 * y4) x) * √(cornerP y3 y4 x) *
      √(ladderInnerMass 1 Lam x / x)) ≤ 4 / ((y3 + y4) * √(cornerG y3 y4)) := by
    refine div_le_div₀ (by norm_num) (by linarith) (by positivity) ?_
    calc (y3 + y4) * √(cornerG y3 y4) = √(cornerG y3 y4) * (y3 + y4) * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hsβ hsP hY0.le (Real.sqrt_nonneg _)) hsH zero_le_one
          (by positivity)
  unfold cornerOutBound
  have : 3 / 4 / ((y3 + y4) * √(cornerG y3 y4)) + 4 / ((y3 + y4) * √(cornerG y3 y4)) ≤
      5 / ((y3 + y4) * √(cornerG y3 y4)) := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

/-- **The corner error terms are dominated**, uniformly in `λ ∈ (0, 1]`, `Λ ≥ 1` and `x`. -/
theorem abs_cornerErr_le_dom (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam)
    (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    |cornerE lam Lam y3 y4 x + cornerOut Lam lam Lam y3 y4 x| ≤ cornerErrDom y3 y4 := by
  have h1 := abs_cornerE_le hlam hlam1 hLam hx h3 h4 hY
  have h2 := abs_cornerOut_le hlam hlam1 hLam hx h3 h4 hY
  have h3' := cornerEBound_le_dom hLam h3 h4 hY
  have h4' := cornerOutBound_le_dom hLam hx h3 h4 hY
  unfold cornerErrDom
  calc _ ≤ |cornerE lam Lam y3 y4 x| + |cornerOut Lam lam Lam y3 y4 x| := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### Pointwise decay -/

theorem tendsto_hLam_atTop (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun Lam : ℝ => ladderInnerMass 1 Lam x / x) atTop atTop := by
  obtain ⟨hx0, hx1⟩ := hx
  unfold ladderInnerMass
  refine Tendsto.atTop_div_const hx0 (tendsto_atTop_add_const_left _ _ ?_)
  exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop (by linarith)

theorem tendsto_cornerOutBound (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4)
    (hY : y3 + y4 < 1) : Tendsto (fun Lam => cornerOutBound Lam y3 y4 x) atTop (𝓝 0) := by
  have hP := cornerP_pos hx h3 h4 hY
  have hβ : 0 < betaG (cornerG y3 y4) (y3 * y4) x := betaG_pos (cornerG_pos h3 hY)
  have hH := tendsto_hLam_atTop hx
  have t1 : Tendsto (fun Lam => x ^ 2 / (Lam * √(cornerP y3 y4 x))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const (Real.sqrt_pos.2 hP))
  have t2 : Tendsto (fun Lam => 3 / 2 * x / (cornerP y3 y4 x * (ladderInnerMass 1 Lam x / x)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (hH.const_mul_atTop hP)
  have t3 : Tendsto (fun Lam => 4 * x / (√(betaG (cornerG y3 y4) (y3 * y4) x) *
      √(cornerP y3 y4 x) * √(ladderInnerMass 1 Lam x / x))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((Real.tendsto_sqrt_atTop.comp hH).const_mul_atTop
      (mul_pos (Real.sqrt_pos.2 hβ) (Real.sqrt_pos.2 hP)))
  have := (t1.add t2).add t3
  simp only [add_zero] at this
  exact this

/-- `(10 + 2 log(1 + Λ²/g))/N_Λ ≤ (10 + 4 Λ/√g)/((1-Y) Λ²)`. -/
theorem cornerEBound_le_decay (hLam : 1 ≤ Lam) (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) :
    (10 + 2 * log (1 + Lam ^ 2 / cornerG y3 y4)) / cornerN Lam (y3 + y4) ≤
      (10 + 4 * (Lam / √(cornerG y3 y4))) / ((1 - (y3 + y4)) * Lam ^ 2) := by
  have hg := cornerG_pos h3 hY
  have h1Y : 0 < 1 - (y3 + y4) := by linarith
  have hL : 0 < Lam := by linarith
  have hNΛ : (1 - (y3 + y4)) * Lam ^ 2 ≤ cornerN Lam (y3 + y4) := by
    unfold cornerN; nlinarith [sq_nonneg (y3 + y4)]
  have hlog : log (1 + Lam ^ 2 / cornerG y3 y4) ≤ 2 * (Lam / √(cornerG y3 y4)) := by
    refine (log_one_add_le_two_sqrt (by positivity)).trans (le_of_eq ?_)
    rw [Real.sqrt_div' _ hg.le, Real.sqrt_sq hL.le]
  refine div_le_div₀ (by positivity) (by linarith) (by positivity) hNΛ

theorem tendsto_cornerEDecay (h3 : 0 < y3) (hY : y3 + y4 < 1) :
    Tendsto (fun Lam => (10 + 4 * (Lam / √(cornerG y3 y4))) / ((1 - (y3 + y4)) * Lam ^ 2))
      atTop (𝓝 0) := by
  have hg := Real.sqrt_pos.2 (cornerG_pos h3 hY)
  have h1Y : 0 < 1 - (y3 + y4) := by linarith
  have hsq : Tendsto (fun Lam : ℝ => (1 - (y3 + y4)) * Lam ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop h1Y
  have t1 : Tendsto (fun Lam : ℝ => 10 / ((1 - (y3 + y4)) * Lam ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  have t2 : Tendsto (fun Lam : ℝ => 4 / √(cornerG y3 y4) / (1 - (y3 + y4)) / Lam) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have := t1.add t2
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Lam hL
  field_simp

/-- **The corner error terms vanish pointwise** as `(λ, Λ) → (0⁺, ∞)`. -/
theorem tendsto_cornerErr (hx : x ∈ Ioo (0 : ℝ) 1) (h3 : 0 < y3) (h4 : 0 < y4)
    (hY : y3 + y4 < 1) :
    Tendsto (fun p : ℝ × ℝ => cornerE p.1 p.2 y3 y4 x + cornerOut p.2 p.1 p.2 y3 y4 x)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  have hb := (tendsto_cornerEDecay h3 hY).add (tendsto_cornerOutBound hx h3 h4 hY)
  rw [add_zero] at hb
  refine squeeze_zero_norm' ?_ (hb.comp tendsto_snd)
  have hl : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hl.prod_mk (eventually_ge_atTop (1 : ℝ))] with p hp
  obtain ⟨⟨hl0, hl1⟩, hL⟩ := hp
  rw [Real.norm_eq_abs]
  have h1 := abs_cornerE_le hl0 hl1.le hL hx h3 h4 hY
  have h2 := abs_cornerOut_le hl0 hl1.le hL hx h3 h4 hY
  have h5 := cornerEBound_le_decay hL h3 h4 hY
  simp only [Function.comp]
  calc _ ≤ |cornerE p.1 p.2 y3 y4 x| + |cornerOut p.2 p.1 p.2 y3 y4 x| := abs_add_le _ _
    _ ≤ _ := by linarith

end Dom

end QED.TwoLoop.UnitSCCorner

end
