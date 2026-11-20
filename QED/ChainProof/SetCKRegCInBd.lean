/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerMainBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Set (c), Stage K: the corner integrand at two photon masses, bound

Helper level (no frozen statement). The closed form `cornerGm la lb` of the corner `b`-integral
(outer photon mass `la`, inner photon mass `lb`) is bounded through its master integrals as in
`QED.TwoLoop.UnitSCCornerMain.abs_cForm_le`, which assumes `M ≤ 2`. With an inner photon of
mass² `lb²` the mass function `M = Y² + (1-Y) lb² - la² e` is at most `1 + lb²`, so the bound is
restated with a general upper bound `K` on `M`; only the subtracted logarithm `-c₀ log(M + βh)/h`
sees `K`:

* **`regCFormLog_abs_le`**: `|c₀ (-log(M + βh)/h)| ≤ (K + 3)/Y` for `Y²/4 ≤ M ≤ K`;
* **`regCForm_abs_le`**: the bound of `abs_cForm_le` with `7/2` replaced by `K + 3`;
* **`regCornerGm_abs_le`**: there is `C ≥ 0` with
  `|cornerGm la lb y₃ y₄ x| ≤ (C + lb²)/((y₃ + y₄) √x √(y₃ (1 - y₃ - y₄)))` (`cornerMaj`) for every
  `la² ≤ 1` and every `lb`, uniformly;
* **`continuousAt_regCornerGm`**: `cornerGm la lb y₃ y₄ x` is continuous in `la` at `la = 0`.

The bound was checked numerically before the proof (scratch `stageK/m5b/cpow.py`, 2·10⁵
log-uniform points near every face, `la ∈ {0} ∪ (10⁻⁶, 1)`, `lb² = t ∈ [10⁻², 10²]`): the ratio
`|cornerGm la √t| · Y √x √g/(1 + t)` stayed below `0.15`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCCornerMain
open QED.TwoLoop.UnitSCReduce (cornerP1 cornerP2)

/-- **The subtracted logarithm** for `Y²/4 ≤ M ≤ K`: `|c₀ (-log(M + β h)/h)| ≤ (K + 3)/Y` when
`0 ≤ c₀ ≤ x/2`, `c₀ β ≤ 1/2`, `x ≤ h`. -/
theorem regCFormLog_abs_le {c₀ β h M Y x K : ℝ} (hY : 0 < Y) (hY1 : Y ≤ 1) (hx : 0 < x)
    (hβ : 0 < β) (hxh : x ≤ h) (hM : Y ^ 2 / 4 ≤ M) (hMK : M ≤ K) (hc0 : 0 ≤ c₀)
    (hc0x : c₀ ≤ x / 2) (hc0β : c₀ * β ≤ 1 / 2) :
    |c₀ * (-log (M + β * h) / h)| ≤ (K + 3) * Y⁻¹ := by
  have hh : 0 < h := hx.trans_le hxh
  have hY4 : 0 < Y ^ 2 / 4 := by positivity
  have hMp : 0 < M := hY4.trans_le hM
  have hK : 0 < K := hMp.trans_le hMK
  set t := c₀ / h with ht
  have ht0 : 0 ≤ t := div_nonneg hc0 hh.le
  have ht1 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ hh]
    nlinarith
  have htβ : t * (β * h) = c₀ * β := by rw [ht]; field_simp
  set A := log (M + β * h) with hA
  have hAu : A ≤ M + β * h := by
    have := log_le_sub_one_of_pos (show 0 < M + β * h by positivity)
    linarith
  have hAl : -(4 / Y) ≤ A := by
    have h1 : log (Y ^ 2 / 4) ≤ A := log_le_log hY4 (by nlinarith [mul_pos hβ hh])
    have h2 : log (Y ^ 2 / 4) = 2 * log (Y / 2) := by
      rw [show Y ^ 2 / 4 = (Y / 2) ^ 2 by ring, log_pow]; push_cast; ring
    have h3 := one_sub_inv_le_log_of_pos (show 0 < Y / 2 by positivity)
    have h4 : (Y / 2)⁻¹ = 2 / Y := by field_simp
    rw [h4] at h3
    have h5 : 0 < 2 / Y := by positivity
    have h6 : 4 / Y = 2 * (2 / Y) := by ring
    rw [h6]
    linarith
  have e : c₀ * (-A / h) = -(t * A) := by rw [ht]; field_simp
  rw [e, abs_neg, abs_le]
  have hYi : 1 ≤ Y⁻¹ := one_le_inv₀ hY |>.mpr hY1
  have e4 : 4 / Y = 4 * Y⁻¹ := by rw [div_eq_mul_inv]
  rw [e4] at hAl
  have hKY : K + 3 ≤ (K + 3) * Y⁻¹ := le_mul_of_one_le_right (by linarith) hYi
  have hKY' : 2 * Y⁻¹ ≤ (K + 3) * Y⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hAl ht0, mul_nonneg ht0 (show 0 ≤ 4 * Y⁻¹ by positivity),
      mul_le_mul_of_nonneg_right ht1 (show 0 ≤ 4 * Y⁻¹ by positivity)]
  · have h1 : t * A ≤ t * (M + β * h) := mul_le_mul_of_nonneg_left hAu ht0
    have h2 : t * M ≤ 1 / 2 * K := mul_le_mul ht1 hMK hMp.le (by norm_num)
    nlinarith

/-- **The bound on the closed form** `cForm` through the masters, for `Y²/4 ≤ M ≤ K`, `h ≥ x`,
`β ≥ g` and coefficients bounded by `x`, `x g`, `x g²`, `1`, `g`, `g²` times constants. -/
theorem regCForm_abs_le {a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M Y x g K K₀ K₁ K₂ K₃ K₄ K₅ : ℝ}
    (hY : 0 < Y) (hY1 : Y ≤ 1) (hx : 0 < x) (hx1 : x ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1)
    (hgβ : g ≤ β) (hxh : x ≤ h) (hM : Y ^ 2 / 4 ≤ M) (hMK : M ≤ K) (hc0 : 0 ≤ c₀)
    (hc0x : c₀ ≤ x / 2) (hc0β : c₀ * β ≤ 1 / 2)
    (ha₀ : |a₀| ≤ x * K₀) (ha₁ : |a₁| ≤ x * g * K₁) (ha₂ : |a₂| ≤ x * g ^ 2 * K₂)
    (hc₁ : |c₁| ≤ K₃) (hc₂ : |c₂| ≤ g * K₄) (hc₃ : |c₃| ≤ g ^ 2 * K₅) :
    |cForm a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M (log (M + β * h)) (log (1 + M / (β * h)))| ≤
      (K + 3 + 4 * K₀ + 4 / 3 * K₁ + 4 / 5 * K₂ + 4 * K₃ + 4 / 3 * K₄ + 4 / 5 * K₅) *
        (Y * √x * √g)⁻¹ := by
  have hβ : 0 < β := hg.trans_le hgβ
  have hh : 0 < h := hx.trans_le hxh
  have hY4 : 0 < Y ^ 2 / 4 := by positivity
  have hMp : 0 < M := hY4.trans_le hM
  have hK : 0 < K := hMp.trans_le hMK
  have hsM : Y / 2 ≤ √M := by
    rw [show Y / 2 = √((Y / 2) ^ 2) from (sqrt_sq (by positivity)).symm]
    exact sqrt_le_sqrt (by linarith)
  have hsx : √x ≤ √h := sqrt_le_sqrt hxh
  have hsg : √g ≤ √β := sqrt_le_sqrt hgβ
  have hsx0 : 0 < √x := sqrt_pos.mpr hx
  have hsg0 : 0 < √g := sqrt_pos.mpr hg
  have hsx1 : √x ≤ 1 := sqrt_le_one.mpr hx1
  have hsg1 : √g ≤ 1 := sqrt_le_one.mpr hg1
  have hK₀ : 0 ≤ K₀ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans ha₀) hx
  have hK₁ : 0 ≤ K₁ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans ha₁) (by positivity)
  have hK₂ : 0 ≤ K₂ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans ha₂) (by positivity)
  have hK₃ : 0 ≤ K₃ := (abs_nonneg _).trans hc₁
  have hK₄ : 0 ≤ K₄ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hc₂) (by positivity)
  have hK₅ : 0 ≤ K₅ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hc₃) (by positivity)
  set W := (Y * √x * √g)⁻¹ with hW
  have hW0 : 0 ≤ W := by positivity
  have hYW : Y⁻¹ ≤ W := by
    rw [hW]
    refine inv_anti₀ (by positivity) ?_
    calc Y * √x * √g ≤ Y * 1 * 1 := by gcongr
      _ = Y := by ring
  obtain ⟨b4l, b4u⟩ := master4_bounds hMp hh hβ
  obtain ⟨b5l, b5u⟩ := master5_bounds hMp hh hβ
  obtain ⟨b6l, b6u⟩ := master6_bounds hMp hh hβ
  obtain ⟨b2l, b2u⟩ := master2_bounds hMp hh hβ
  obtain ⟨b3l, b3u⟩ := master3_bounds hMp hh hβ
  obtain ⟨b7l, b7u⟩ := master7_bounds hMp hh hβ
  have t0 := regCFormLog_abs_le hY hY1 hx hβ hxh hM hMK hc0 hc0x hc0β
  have t0' : (K + 3) * Y⁻¹ ≤ (K + 3) * W := mul_le_mul_of_nonneg_left hYW (by linarith)
  have t4 := abs_mul_le_of_le b4l b4u ha₀
  have t5 := abs_mul_le_of_le b5l b5u ha₁
  have t6 := abs_mul_le_of_le b6l b6u ha₂
  have t2 := abs_mul_le_of_le b2l b2u hc₁
  have t3 := abs_mul_le_of_le b3l b3u hc₂
  have t7 := abs_mul_le_of_le b7l b7u hc₃
  have s4 : x * K₀ * ((√M * (h * √h))⁻¹ * (2 * (√β)⁻¹)) ≤ 4 * K₀ * W := by
    calc x * K₀ * ((√M * (h * √h))⁻¹ * (2 * (√β)⁻¹)) ≤
        x * K₀ * ((Y / 2 * (x * √x))⁻¹ * (2 * (√g)⁻¹)) := by gcongr
      _ = 4 * K₀ * W := by rw [hW]; field_simp; ring
  have s5 : x * g * K₁ * ((√M * (h * √h))⁻¹ * (2 / 3 * (β * √β)⁻¹)) ≤ 4 / 3 * K₁ * W := by
    calc x * g * K₁ * ((√M * (h * √h))⁻¹ * (2 / 3 * (β * √β)⁻¹)) ≤
        x * g * K₁ * ((Y / 2 * (x * √x))⁻¹ * (2 / 3 * (g * √g)⁻¹)) := by gcongr
      _ = 4 / 3 * K₁ * W := by rw [hW]; field_simp; ring
  have s6 : x * g ^ 2 * K₂ * ((√M * (h * √h))⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹)) ≤
      4 / 5 * K₂ * W := by
    calc x * g ^ 2 * K₂ * ((√M * (h * √h))⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹)) ≤
        x * g ^ 2 * K₂ * ((Y / 2 * (x * √x))⁻¹ * (2 / 5 * (g ^ 2 * √g)⁻¹)) := by gcongr
      _ = 4 / 5 * K₂ * W := by rw [hW]; field_simp; ring
  have s2 : K₃ * ((√M * √h)⁻¹ * (2 * (√β)⁻¹)) ≤ 4 * K₃ * W := by
    calc K₃ * ((√M * √h)⁻¹ * (2 * (√β)⁻¹)) ≤ K₃ * ((Y / 2 * √x)⁻¹ * (2 * (√g)⁻¹)) := by gcongr
      _ = 4 * K₃ * W := by rw [hW]; field_simp; ring
  have s3 : g * K₄ * ((√M * √h)⁻¹ * (2 / 3 * (β * √β)⁻¹)) ≤ 4 / 3 * K₄ * W := by
    calc g * K₄ * ((√M * √h)⁻¹ * (2 / 3 * (β * √β)⁻¹)) ≤
        g * K₄ * ((Y / 2 * √x)⁻¹ * (2 / 3 * (g * √g)⁻¹)) := by gcongr
      _ = 4 / 3 * K₄ * W := by rw [hW]; field_simp; ring
  have s7 : g ^ 2 * K₅ * ((√M * √h)⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹)) ≤ 4 / 5 * K₅ * W := by
    calc g ^ 2 * K₅ * ((√M * √h)⁻¹ * (2 / 5 * (β ^ 2 * √β)⁻¹)) ≤
        g ^ 2 * K₅ * ((Y / 2 * √x)⁻¹ * (2 / 5 * (g ^ 2 * √g)⁻¹)) := by gcongr
      _ = 4 / 5 * K₅ * W := by rw [hW]; field_simp; ring
  unfold cForm
  set A := log (M + β * h)
  set L := log (1 + M / (β * h))
  calc _ ≤ |c₀ * (-A / h)| + |a₀ * (1 / (h * (M + β * h)))| +
        |a₁ * (L / M ^ 2 - 1 / (M * (M + β * h)))| +
        |a₂ * (1 / (M ^ 2 * β) - 2 * h * L / M ^ 3 + h / (M ^ 2 * (M + β * h)))| +
        |c₁ * (L / M)| + |c₂ * (1 / (M * β) - h * L / M ^ 2)| +
        |c₃ * (1 / (2 * M * β ^ 2) - h / (M ^ 2 * β) + h ^ 2 * L / M ^ 3)| := by
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
          exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- **The pointwise bound at two photon masses**: there is `C ≥ 0` with
`|cornerGm la lb y₃ y₄ x| ≤ (C + lb²)/((y₃ + y₄) √x √(y₃ (1 - y₃ - y₄)))` for every `la² ≤ 1`,
every `lb`, `(y₃, y₄)` in the open triangle and `0 < x < 1`. -/
theorem regCornerGm_abs_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ la lb y3 y4 x : ℝ, la ^ 2 ≤ 1 → 0 < y3 →
    0 < y4 → y3 + y4 < 1 → 0 < x → x < 1 →
      |cornerGm la lb y3 y4 x| ≤ (C + lb ^ 2) * cornerMaj y3 y4 x := by
  obtain ⟨K₀, hK₀⟩ := exists_bound_cube (f := fun x y3 y4 => cornerP1 x y3 y4 / 4)
    (by unfold cornerP1; fun_prop)
  obtain ⟨K₁, hK₁⟩ := exists_bound_cube
    (f := fun x y3 y4 => (cornerQ x y3 - cornerP1 x y3 y4) / 4)
    (by unfold cornerP1 cornerQ; fun_prop)
  obtain ⟨K₂, hK₂⟩ := exists_bound_cube (f := fun x y3 _ => -(cornerQ x y3 / 4))
    (by unfold cornerQ; fun_prop)
  obtain ⟨K₃, hK₃⟩ := exists_bound_cube (f := fun x y3 y4 => cornerC1 x y3 y4)
    (by unfold cornerC1 cornerP2 cornerG; fun_prop)
  obtain ⟨K₄, hK₄⟩ := exists_bound_cube
    (f := fun x y3 y4 => x * (cornerR x y3 + cornerP2 x y3 y4) / 4)
    (by unfold cornerR cornerP2; fun_prop)
  obtain ⟨K₅, hK₅⟩ := exists_bound_cube (f := fun x y3 _ => -(x * cornerR x y3 / 4))
    (by unfold cornerR; fun_prop)
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have n0 := (abs_nonneg _).trans (hK₀ 0 0 0 m0 m0 m0)
  have n1 := (abs_nonneg _).trans (hK₁ 0 0 0 m0 m0 m0)
  have n2 := (abs_nonneg _).trans (hK₂ 0 0 0 m0 m0 m0)
  have n3 := (abs_nonneg _).trans (hK₃ 0 0 0 m0 m0 m0)
  have n4 := (abs_nonneg _).trans (hK₄ 0 0 0 m0 m0 m0)
  have n5 := (abs_nonneg _).trans (hK₅ 0 0 0 m0 m0 m0)
  refine ⟨1 + 3 + 4 * K₀ + 4 / 3 * K₁ + 4 / 5 * K₂ + 4 * K₃ + 4 / 3 * K₄ + 4 / 5 * K₅,
    by positivity, fun la lb y3 y4 x hl h3 h4 hY hx0 hx1 => ?_⟩
  have mx : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  have m3 : y3 ∈ Icc (0 : ℝ) 1 := ⟨h3.le, by linarith⟩
  have m4 : y4 ∈ Icc (0 : ℝ) 1 := ⟨h4.le, by linarith⟩
  have hg : 0 < cornerG y3 y4 := by
    unfold cornerG; have : 0 < 1 - y3 - y4 := by linarith
    positivity
  have hg1 : cornerG y3 y4 ≤ 1 := by
    unfold cornerG; nlinarith
  have h1x : 0 < 1 - x := by linarith
  have hl0 : 0 ≤ la ^ 2 := sq_nonneg la
  have h1Y : 0 ≤ 1 - (y3 + y4) := by linarith
  have hxh : x ≤ ladderInnerMass 1 la x / x := by
    rw [le_div_iff₀ hx0]; unfold ladderInnerMass; nlinarith [mul_nonneg h1x.le hl0]
  have hM : (y3 + y4) ^ 2 / 4 ≤ cornerMass la lb y3 y4 := by
    unfold cornerMass
    nlinarith [mul_le_mul_of_nonneg_right hl (mul_pos h3 h4).le, sq_nonneg (y3 - y4),
      mul_nonneg h1Y (sq_nonneg lb)]
  have hMK : cornerMass la lb y3 y4 ≤ 1 + lb ^ 2 := by
    unfold cornerMass
    have hY1 : (y3 + y4) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hl0 (mul_pos h3 h4).le, mul_nonneg (add_pos h3 h4).le (sq_nonneg lb)]
  have hc0 : 0 ≤ cornerC0 x := by unfold cornerC0; positivity
  have hc0x : cornerC0 x ≤ x / 2 := by unfold cornerC0; nlinarith
  have hc0β : cornerC0 x * betaG (cornerG y3 y4) (y3 * y4) x ≤ 1 / 2 := by
    unfold betaG
    rw [mul_max_of_nonneg _ _ hc0]
    refine max_le ?_ ?_
    · unfold cornerC0
      have : x * (1 - x) ≤ 1 := by nlinarith
      have := mul_le_mul this hg1 hg.le zero_le_one
      nlinarith
    · unfold cornerC0
      have e : x * (1 - x) / 2 * (y3 * y4 * x / (1 - x)) = x ^ 2 * (y3 * y4) / 2 := by
        field_simp
      rw [e]
      have : y3 * y4 ≤ 1 := by nlinarith
      have : x ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul this (by assumption : y3 * y4 ≤ 1) (mul_pos h3 h4).le zero_le_one]
  have ha₀ : |cornerA0 x y3 y4| ≤ x * K₀ := by
    have := abs_mul_le_mul_of_abs_le hx0.le (hK₀ x y3 y4 mx m3 m4)
    rwa [show x * (cornerP1 x y3 y4 / 4) = cornerA0 x y3 y4 by unfold cornerA0; ring] at this
  have ha₁ : |cornerA1 x y3 y4| ≤ x * cornerG y3 y4 * K₁ := by
    have := abs_mul_le_mul_of_abs_le (mul_pos hx0 hg).le (hK₁ x y3 y4 mx m3 m4)
    rwa [show x * cornerG y3 y4 * ((cornerQ x y3 - cornerP1 x y3 y4) / 4) = cornerA1 x y3 y4 by
      unfold cornerA1; ring] at this
  have ha₂ : |cornerA2 x y3 y4| ≤ x * cornerG y3 y4 ^ 2 * K₂ := by
    have := abs_mul_le_mul_of_abs_le (by positivity : (0 : ℝ) ≤ x * cornerG y3 y4 ^ 2)
      (hK₂ x y3 y4 mx m3 m4)
    rwa [show x * cornerG y3 y4 ^ 2 * -(cornerQ x y3 / 4) = cornerA2 x y3 y4 by
      unfold cornerA2; ring] at this
  have hc₁ : |cornerC1 x y3 y4| ≤ K₃ := hK₃ x y3 y4 mx m3 m4
  have hc₂ : |cornerC2 x y3 y4| ≤ cornerG y3 y4 * K₄ := by
    have := abs_mul_le_mul_of_abs_le hg.le (hK₄ x y3 y4 mx m3 m4)
    rwa [show cornerG y3 y4 * (x * (cornerR x y3 + cornerP2 x y3 y4) / 4) = cornerC2 x y3 y4 by
      unfold cornerC2; ring] at this
  have hc₃ : |cornerC3 x y3 y4| ≤ cornerG y3 y4 ^ 2 * K₅ := by
    have := abs_mul_le_mul_of_abs_le (by positivity : (0 : ℝ) ≤ cornerG y3 y4 ^ 2)
      (hK₅ x y3 y4 mx m3 m4)
    rwa [show cornerG y3 y4 ^ 2 * -(x * cornerR x y3 / 4) = cornerC3 x y3 y4 by
      unfold cornerC3; ring] at this
  have key := regCForm_abs_le (by positivity) (by linarith) hx0 hx1.le hg hg1 (le_betaG _ _ _)
    hxh hM hMK hc0 hc0x hc0β ha₀ ha₁ ha₂ hc₁ hc₂ hc₃
  refine key.trans (le_of_eq ?_)
  unfold cornerMaj
  ring

/-- **Continuity at `la = 0`** of the closed form in the outer photon mass, at any inner photon
mass `lb`, for `(y₃, y₄)` in the triangle and `0 < x < 1`. -/
theorem continuousAt_regCornerGm {lb y3 y4 x : ℝ} (h3 : 0 < y3) (h4 : 0 < y4)
    (hY : y3 + y4 < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    ContinuousAt (fun la => cornerGm la lb y3 y4 x) 0 := by
  have hg : 0 < cornerG y3 y4 := by
    unfold cornerG; have : 0 < 1 - y3 - y4 := by linarith
    positivity
  have hβ : 0 < betaG (cornerG y3 y4) (y3 * y4) x := betaG_pos hg
  have h1x : 0 < 1 - x := by linarith
  have h1Y : 0 < 1 - (y3 + y4) := by linarith
  unfold cornerGm cForm cornerMass ladderInnerMass
  generalize betaG (cornerG y3 y4) (y3 * y4) x = β at hβ ⊢
  generalize 1 - (y3 + y4) = s at h1Y ⊢
  fun_prop (disch := (apply ne_of_gt; first
    | (simp only [one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, zero_mul, add_zero, sub_zero]; positivity)
    | positivity))

end QED.ChainProof.SetCK
