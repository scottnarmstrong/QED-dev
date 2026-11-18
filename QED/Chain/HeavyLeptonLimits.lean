/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.HeavyLeptonPrim
public import QED.Polylog.ExtraIntegrals
public import QED.Polylog.ExtraIntegralsX
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The heavy-lepton bubble: the endpoint limits of the antiderivative

Helper analysis for obligation O3-M3 of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

For `y ∈ (0,1)` the antiderivative `QED.Chain.HeavyLepton.hlPrim y` of
`QED/Chain/HeavyLeptonPrim.lean` has one-sided limits at both ends of `(0,1)`.

* `w → 0⁺` (that is, `x → 1⁻`): `Q₁ = w · Q̃₁` with `Q̃₁` regular, so `Q₁ ell → 0` from
  `w log w → 0`; the products `log w log(1+w)`, `log w log(1+yw)` tend to `0`; the rest is
  continuous. The limit is `hlPrimZero y`.
* `w → 1⁻` (that is, `x → 0⁺`): `Q₀` and `Q₁` have poles at `w = 1` which cancel. With
  `u = y(1-w²)/(y+w) → 0⁺` one has `ell = -log(1-u)`, and
  `Q₀ + Q₁ ell = B - U · logRem(u)/u⁴` with `B, U` rational and regular at `1`, `U(1) = 0`, and
  `logRem u/u⁴ → 0` (`QED.Polylog.abs_logRem_le`). The limit is `hlPrimOne y`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.Chain.HeavyLepton

/-! ### Tools -/

/-- `Li₂ ∘ g → Li₂ (g w₀)` along a filter `l ≤ 𝓝 w₀`, when `g` is continuous at `w₀` and takes
values in `[-1, 1]` at `w₀` and eventually along `l`. -/
theorem tendsto_Li₂_comp_of_continuousAt {g : ℝ → ℝ} {l : Filter ℝ} {w₀ : ℝ} (hl : l ≤ 𝓝 w₀)
    (hg : ContinuousAt g w₀) (h0 : g w₀ ∈ Icc (-1 : ℝ) 1)
    (hgs : ∀ᶠ w in l, g w ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun w => Li₂ (g w)) l (𝓝 (Li₂ (g w₀))) :=
  tendsto_Li₂_comp h0 (hg.tendsto.mono_left hl) hgs

/-- A continuous function tends to its value along `𝓝[s] w₀`. -/
theorem tendsto_nhdsWithin_of_continuousAt {g : ℝ → ℝ} {s : Set ℝ} {w₀ : ℝ}
    (hg : ContinuousAt g w₀) : Tendsto g (𝓝[s] w₀) (𝓝 (g w₀)) :=
  hg.tendsto.mono_left nhdsWithin_le_nhds

/-- `log w · log(1 + k w) → 0` as `w → 0⁺`, for `k ≥ 0`. -/
theorem tendsto_log_mul_log_one_add_mul_zero {k : ℝ} (hk : 0 ≤ k) :
    Tendsto (fun w => log w * log (1 + k * w)) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ ((tendsto_mul_log_zero.abs.const_mul k).trans ?_)
  · filter_upwards [self_mem_nhdsWithin] with w (hw : 0 < w)
    have hp : 0 < 1 + k * w := by positivity
    have h0 : 0 ≤ log (1 + k * w) := log_nonneg (by nlinarith [mul_nonneg hk hw.le])
    have h1 : log (1 + k * w) ≤ k * w := by
      have := log_le_sub_one_of_pos hp
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    calc |log w| * log (1 + k * w) ≤ |log w| * (k * w) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = k * |w * log w| := by rw [abs_mul, abs_of_pos hw]; ring
  · simp

theorem mem_Icc_of_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith, h1⟩

/-- Points of `𝓝[>] 0` eventually lie in `(0,1)`. -/
theorem eventually_mem_Ioo_zero : ∀ᶠ w in 𝓝[>] (0 : ℝ), w ∈ Ioo (0 : ℝ) 1 :=
  Ioo_mem_nhdsGT zero_lt_one

/-- Points of `𝓝[<] 1` eventually lie in `(0,1)`. -/
theorem eventually_mem_Ioo_one : ∀ᶠ w in 𝓝[<] (1 : ℝ), w ∈ Ioo (0 : ℝ) 1 :=
  Ioo_mem_nhdsLT zero_lt_one

/-! ### The endpoint `w → 0⁺` -/

/-- `Q̃₁ = Q₁/w`, regular at `0`. -/
noncomputable def hlQ1t (y w : ℝ) : ℝ :=
  ((-6 * (y ^ 2 - 3)) +
    (y * (y ^ 4 - 12 * y ^ 2 + 42)) * w +
    (-2 * (2 * y ^ 4 - 18 * y ^ 2 + 13)) * w ^ 2 +
    (-y * (2 * y ^ 4 - 19 * y ^ 2 + 64)) * w ^ 3 +
    (2 * (y ^ 4 - 27 * y ^ 2 + 2)) * w ^ 4 +
    (y * (y ^ 4 - 22 * y ^ 2 + 6)) * w ^ 5 +
    (-2 * y ^ 4) * w ^ 6 +
    (-y ^ 3) * w ^ 7) /
    (6 * y ^ 3 * (1 - w ^ 2) ^ 2 * (1 + y * w) ^ 2)

theorem hlQ1_eq_mul (y w : ℝ) : hlQ1 y w = w * hlQ1t y w := by
  unfold hlQ1 hlQ1t
  ring

theorem hlQ0_zero (y : ℝ) : hlQ0 y 0 = (5 * y ^ 2 - 11) * (5 * y ^ 2 - 9) / (36 * y ^ 4) := by
  unfold hlQ0
  ring

/-- The limit of the antiderivative at `w → 0⁺`. -/
noncomputable def hlPrimZero (y : ℝ) : ℝ :=
  (5 * y ^ 2 - 11) * (5 * y ^ 2 - 9) / (36 * y ^ 4) - (y ^ 2 - 9) / (3 * y ^ 2) * log y +
    (y ^ 2 - 5) / (2 * y ^ 3) * (Li₂ (1 / (1 + y)) - Li₂ (y / (1 + y)) - π ^ 2 / 6 + Li₂ (1 - y)) +
    2 / y ^ 4 * Li₂ (1 - y ^ 2)

theorem tendsto_hlPrim_zero {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (hlPrim y) (𝓝[>] 0) (𝓝 (hlPrimZero y)) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hyp : 0 < 1 + y := by linarith
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  -- the rational and logarithmic pieces
  have hQ0 : Tendsto (hlQ0 y) (𝓝[>] 0) (𝓝 (hlQ0 y 0)) := by
    refine tendsto_nhdsWithin_of_continuousAt ?_
    unfold hlQ0
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num; positivity)
  have hQ1t : Tendsto (hlQ1t y) (𝓝[>] 0) (𝓝 (hlQ1t y 0)) := by
    refine tendsto_nhdsWithin_of_continuousAt ?_
    unfold hlQ1t
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num; positivity)
  have hlog1 : Tendsto (fun w => log (1 + y * w)) (𝓝[>] 0) (𝓝 (log (1 + y * 0))) :=
    tendsto_nhdsWithin_of_continuousAt (ContinuousAt.log (by fun_prop) (by norm_num))
  have hlog2 : Tendsto (fun w => log (y + w)) (𝓝[>] 0) (𝓝 (log (y + 0))) :=
    tendsto_nhdsWithin_of_continuousAt (ContinuousAt.log (by fun_prop) (by simp; positivity))
  have hwl1 : Tendsto (fun w => w * log (y + w)) (𝓝[>] 0) (𝓝 (0 * log (y + 0))) :=
    (tendsto_nhdsWithin_of_continuousAt (g := id) continuousAt_id).mul hlog2
  have hwl3 : Tendsto (fun w => w * log (1 + y * w)) (𝓝[>] 0) (𝓝 (0 * log (1 + y * 0))) :=
    (tendsto_nhdsWithin_of_continuousAt (g := id) continuousAt_id).mul hlog1
  have hQ1ell := hQ1t.mul ((hwl1.sub tendsto_mul_log_zero).sub hwl3)
  -- the dilogarithms
  have hA1 : Tendsto (fun w => Li₂ ((1 - w) / (1 + y))) (𝓝[>] 0)
      (𝓝 (Li₂ ((1 - 0) / (1 + y)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop)
      (mem_Icc_of_nonneg (by positivity) (by rw [div_le_one hyp]; linarith)) ?_
    filter_upwards [eventually_mem_Ioo_zero] with w hw
    exact mem_Icc_of_nonneg (div_nonneg (by linarith [hw.2]) hyp.le)
      (by rw [div_le_one hyp]; linarith [hw.1])
  have hA2 : Tendsto (fun w => Li₂ (y * (1 - w) / (1 + y))) (𝓝[>] 0)
      (𝓝 (Li₂ (y * (1 - 0) / (1 + y)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop)
      (mem_Icc_of_nonneg (by positivity) (by rw [div_le_one hyp]; linarith)) ?_
    filter_upwards [eventually_mem_Ioo_zero] with w hw
    exact mem_Icc_of_nonneg (div_nonneg (mul_nonneg hy0.le (by linarith [hw.2])) hyp.le)
      (by rw [div_le_one hyp]; nlinarith [hw.1])
  have hA3 : Tendsto (fun w : ℝ => Li₂ (1 - w)) (𝓝[>] 0) (𝓝 (Li₂ (1 - 0))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop) ⟨by norm_num, by norm_num⟩ ?_
    filter_upwards [eventually_mem_Ioo_zero] with w hw
    exact mem_Icc_of_nonneg (by linarith [hw.2]) (by linarith [hw.1])
  have hB1 : Tendsto (fun w => Li₂ ((1 - y) / (1 + w))) (𝓝[>] 0)
      (𝓝 (Li₂ ((1 - y) / (1 + 0)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl
      (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
      (mem_Icc_of_nonneg (by norm_num; linarith) (by norm_num; linarith)) ?_
    filter_upwards [eventually_mem_Ioo_zero] with w hw
    have hwp : 0 < 1 + w := by linarith [hw.1]
    exact mem_Icc_of_nonneg (div_nonneg (by linarith) hwp.le)
      (by rw [div_le_one hwp]; linarith [hw.1])
  have hB2 : Tendsto (fun w : ℝ => Li₂ (-w)) (𝓝[>] 0) (𝓝 (Li₂ (-0))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop) ⟨by norm_num, by norm_num⟩ ?_
    filter_upwards [eventually_mem_Ioo_zero] with w hw
    exact ⟨by linarith [hw.2], by linarith [hw.1]⟩
  have hB3 : Tendsto (fun w => Li₂ ((1 - y) * w / (1 + w))) (𝓝[>] 0)
      (𝓝 (Li₂ ((1 - y) * 0 / (1 + 0)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl
      (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)) ⟨by norm_num, by norm_num⟩ ?_
    filter_upwards [eventually_mem_Ioo_zero] with w hw
    have hwp : 0 < 1 + w := by linarith [hw.1]
    exact mem_Icc_of_nonneg (div_nonneg (mul_nonneg (by linarith) hw.1.le) hwp.le)
      (by rw [div_le_one hwp]; nlinarith [hw.1])
  have hB4 : Tendsto (fun w => Li₂ (-(y * w))) (𝓝[>] 0) (𝓝 (Li₂ (-(y * 0)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop) ⟨by norm_num, by norm_num⟩ ?_
    filter_upwards [eventually_mem_Ioo_zero] with w hw
    exact ⟨by nlinarith [hw.1, hw.2], by nlinarith [hw.1]⟩
  have hC1 : Tendsto (fun w => Li₂ ((1 - y ^ 2) / (1 + y * w))) (𝓝[>] 0)
      (𝓝 (Li₂ ((1 - y ^ 2) / (1 + y * 0)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl
      (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
      (by rw [show (1 - y ^ 2) / (1 + y * 0) = 1 - y ^ 2 by simp]
          exact mem_Icc_of_nonneg hy2.le (by nlinarith)) ?_
    filter_upwards [eventually_mem_Ioo_zero] with w hw
    have hd : 0 < 1 + y * w := by nlinarith [hw.1]
    exact mem_Icc_of_nonneg (div_nonneg hy2.le hd.le) (by rw [div_le_one hd]; nlinarith [hw.1])
  have hLL1 := tendsto_log_mul_log_one_add_mul_zero (k := 1) zero_le_one
  have hLLy := tendsto_log_mul_log_one_add_mul_zero hy0.le
  have h := ((((hQ0.add ((hlog1.sub hlog2).const_mul ((y ^ 2 - 9) / (3 * y ^ 2)))).add
    hQ1ell).add ((((hA1.sub hA2).sub hA3).add ((((hB1.sub hLL1).sub (hB2.const_mul 2)).sub
      hB3).add hB4)).const_mul ((y ^ 2 - 5) / (2 * y ^ 3)))).add
    ((((hC1.sub (hlog1.const_mul (log y))).sub hLLy).sub hB4).const_mul (2 / y ^ 4)))
  have h2 : Tendsto (hlPrim y) (𝓝[>] 0) _ := h.congr' (Eventually.of_forall fun w => by
    simp only [hlPrim, hlK1, hlKm1, hlKy, hlQ1_eq_mul, ell, one_mul]
    ring)
  convert h2 using 2
  · simp only [hlPrimZero, hlQ0_zero, mul_zero, add_zero, sub_zero, zero_mul, neg_zero, Li₂_zero,
      log_one, Li₂_one, zero_div, one_div]
    ring_nf

/-! ### The endpoint `w → 1⁻` -/

/-- `u = y(1-w²)/(y+w) = 1/(1+p)`, so that `ell = -log(1-u)`. -/
noncomputable def hlu (y w : ℝ) : ℝ := y * (1 - w ^ 2) / (y + w)

theorem hlB_eq {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) :
    hlB y w = hlQ0 y w + hlQ1 y w *
      (hlu y w + hlu y w ^ 2 / 2 + hlu y w ^ 3 / 3 + hlu y w ^ 4 / 4) := by
  obtain ⟨h0, h1⟩ := hw
  have hd : 0 < 1 + y * w := by positivity
  have h4 : 0 < y + w := by positivity
  have hs : 1 - w ^ 2 ≠ 0 := by nlinarith
  unfold hlB hlQ0 hlQ1 hlu
  field_simp
  ring

theorem hlU_eq {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) :
    hlU y w = hlQ1 y w * hlu y w ^ 4 := by
  obtain ⟨h0, h1⟩ := hw
  have hd : 0 < 1 + y * w := by positivity
  have h4 : 0 < y + w := by positivity
  have hs : 1 - w ^ 2 ≠ 0 := by nlinarith
  unfold hlU hlQ1 hlu
  field_simp
  ring

theorem hlu_pos {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) : 0 < hlu y w := by
  obtain ⟨h0, h1⟩ := hw
  have hs : 0 < 1 - w ^ 2 := by nlinarith
  unfold hlu
  positivity

theorem log_one_sub_hlu {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) :
    log (1 - hlu y w) = -ell y w := by
  obtain ⟨h0, h1⟩ := hw
  have hd : 0 < 1 + y * w := by positivity
  have h4 : 0 < y + w := by positivity
  have : 1 - hlu y w = w * (1 + y * w) / (y + w) := by
    unfold hlu
    field_simp
    ring
  rw [this, log_div (by positivity) h4.ne', log_mul h0.ne' hd.ne']
  unfold ell
  ring

/-- Near `w = 1`: `Q₀ + Q₁ ell = B - U · logRem(u)/u⁴`. -/
theorem hlQ0_add_hlQ1_mul_ell {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) :
    hlQ0 y w + hlQ1 y w * ell y w =
      hlB y w - hlU y w * (logRem (hlu y w) / hlu y w ^ 4) := by
  have hu := (hlu_pos hy hw).ne'
  rw [hlB_eq hy hw, hlU_eq hy hw]
  unfold logRem
  rw [log_one_sub_hlu hy hw]
  generalize hlu y w = u at hu ⊢
  field_simp
  ring

theorem tendsto_hlu_one {y : ℝ} (hy : 0 < y) : Tendsto (hlu y) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : ContinuousAt (hlu y) 1 := by
      unfold hlu
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
    have := tendsto_nhdsWithin_of_continuousAt (s := Iio 1) hc
    rwa [show hlu y 1 = 0 by unfold hlu; ring] at this
  · filter_upwards [eventually_mem_Ioo_one] with w hw
    exact hlu_pos hy hw

/-- `logRem x / x⁴ → 0` as `x → 0⁺`. -/
theorem tendsto_logRem_div_pow_four : Tendsto (fun x => logRem x / x ^ 4) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_div_pow_four_of_abs_le (c := 1 / 2) (M := 2) (by norm_num)
    fun x hx => abs_logRem_le hx.1.le hx.2.le).1

theorem hlB_one {y : ℝ} (hy : 0 < y) : hlB y 1 = 11 * (4 * y ^ 2 + 9) / (36 * y ^ 4) := by
  unfold hlB
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem hlU_one (y : ℝ) : hlU y 1 = 0 := by
  unfold hlU
  ring

/-- The limit of the antiderivative at `w → 1⁻`. -/
noncomputable def hlPrimOne (y : ℝ) : ℝ :=
  11 * (4 * y ^ 2 + 9) / (36 * y ^ 4) + (y ^ 2 - 5) / (2 * y ^ 3) * (π ^ 2 / 6 + Li₂ (-y)) +
    2 / y ^ 4 * (Li₂ (1 - y) - log y * log (1 + y) - Li₂ (-y))

theorem tendsto_hlPrim_one {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (hlPrim y) (𝓝[<] 1) (𝓝 (hlPrimOne y)) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hyp : 0 < 1 + y := by linarith
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have hl : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have hB : Tendsto (hlB y) (𝓝[<] 1) (𝓝 (hlB y 1)) := by
    refine tendsto_nhdsWithin_of_continuousAt ?_
    unfold hlB
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hU : Tendsto (hlU y) (𝓝[<] 1) (𝓝 (hlU y 1)) := by
    refine tendsto_nhdsWithin_of_continuousAt ?_
    unfold hlU
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hR := tendsto_logRem_div_pow_four.comp (tendsto_hlu_one hy0)
  have hlog1 : Tendsto (fun w => log (1 + y * w)) (𝓝[<] 1) (𝓝 (log (1 + y * 1))) :=
    tendsto_nhdsWithin_of_continuousAt (ContinuousAt.log (by fun_prop) (by positivity))
  have hlog2 : Tendsto (fun w => log (y + w)) (𝓝[<] 1) (𝓝 (log (y + 1))) :=
    tendsto_nhdsWithin_of_continuousAt (ContinuousAt.log (by fun_prop) (by positivity))
  have hlogw : Tendsto (fun w => log w) (𝓝[<] 1) (𝓝 (log 1)) :=
    tendsto_nhdsWithin_of_continuousAt (continuousAt_log one_ne_zero)
  have hlog3 : Tendsto (fun w => log (1 + w)) (𝓝[<] 1) (𝓝 (log (1 + 1))) :=
    tendsto_nhdsWithin_of_continuousAt (ContinuousAt.log (by fun_prop) (by norm_num))
  -- the dilogarithms
  have hA1 : Tendsto (fun w => Li₂ ((1 - w) / (1 + y))) (𝓝[<] 1)
      (𝓝 (Li₂ ((1 - 1) / (1 + y)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop) (by norm_num) ?_
    filter_upwards [eventually_mem_Ioo_one] with w hw
    exact mem_Icc_of_nonneg (div_nonneg (by linarith [hw.2]) hyp.le)
      (by rw [div_le_one hyp]; linarith [hw.1])
  have hA2 : Tendsto (fun w => Li₂ (y * (1 - w) / (1 + y))) (𝓝[<] 1)
      (𝓝 (Li₂ (y * (1 - 1) / (1 + y)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop) (by norm_num) ?_
    filter_upwards [eventually_mem_Ioo_one] with w hw
    exact mem_Icc_of_nonneg (div_nonneg (mul_nonneg hy0.le (by linarith [hw.2])) hyp.le)
      (by rw [div_le_one hyp]; nlinarith [hw.1])
  have hA3 : Tendsto (fun w : ℝ => Li₂ (1 - w)) (𝓝[<] 1) (𝓝 (Li₂ (1 - 1))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop) (by norm_num) ?_
    filter_upwards [eventually_mem_Ioo_one] with w hw
    exact mem_Icc_of_nonneg (by linarith [hw.2]) (by linarith [hw.1])
  have hB1 : Tendsto (fun w => Li₂ ((1 - y) / (1 + w))) (𝓝[<] 1)
      (𝓝 (Li₂ ((1 - y) / (1 + 1)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl
      (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
      (mem_Icc_of_nonneg (by norm_num; linarith) (by norm_num; linarith)) ?_
    filter_upwards [eventually_mem_Ioo_one] with w hw
    have hwp : 0 < 1 + w := by linarith [hw.1]
    exact mem_Icc_of_nonneg (div_nonneg (by linarith) hwp.le)
      (by rw [div_le_one hwp]; linarith [hw.1])
  have hB2 : Tendsto (fun w : ℝ => Li₂ (-w)) (𝓝[<] 1) (𝓝 (Li₂ (-1))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop) ⟨by norm_num, by norm_num⟩ ?_
    filter_upwards [eventually_mem_Ioo_one] with w hw
    exact ⟨by linarith [hw.2], by linarith [hw.1]⟩
  have hB3 : Tendsto (fun w => Li₂ ((1 - y) * w / (1 + w))) (𝓝[<] 1)
      (𝓝 (Li₂ ((1 - y) * 1 / (1 + 1)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl
      (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
      (mem_Icc_of_nonneg (by norm_num; linarith) (by norm_num; linarith)) ?_
    filter_upwards [eventually_mem_Ioo_one] with w hw
    have hwp : 0 < 1 + w := by linarith [hw.1]
    exact mem_Icc_of_nonneg (div_nonneg (mul_nonneg (by linarith) hw.1.le) hwp.le)
      (by rw [div_le_one hwp]; nlinarith [hw.1])
  have hB4 : Tendsto (fun w => Li₂ (-(y * w))) (𝓝[<] 1) (𝓝 (Li₂ (-(y * 1)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop)
      ⟨by linarith, by linarith⟩ ?_
    filter_upwards [eventually_mem_Ioo_one] with w hw
    exact ⟨by nlinarith [hw.1, hw.2], by nlinarith [hw.1]⟩
  have hC1 : Tendsto (fun w => Li₂ ((1 - y ^ 2) / (1 + y * w))) (𝓝[<] 1)
      (𝓝 (Li₂ ((1 - y ^ 2) / (1 + y * 1)))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl
      (ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity))
      (mem_Icc_of_nonneg (div_nonneg hy2.le (by positivity))
        (by rw [div_le_one (by positivity)]; nlinarith))
      ?_
    filter_upwards [eventually_mem_Ioo_one] with w hw
    have hd : 0 < 1 + y * w := by nlinarith [hw.1]
    exact mem_Icc_of_nonneg (div_nonneg hy2.le hd.le) (by rw [div_le_one hd]; nlinarith [hw.1])
  have h := ((((hB.sub (hU.mul hR)).add ((hlog1.sub hlog2).const_mul
    ((y ^ 2 - 9) / (3 * y ^ 2)))).add ((((hA1.sub hA2).sub hA3).add ((((hB1.sub
      (hlogw.mul hlog3)).sub (hB2.const_mul 2)).sub hB3).add hB4)).const_mul
        ((y ^ 2 - 5) / (2 * y ^ 3)))).add ((((hC1.sub (hlog1.const_mul (log y))).sub
          (hlogw.mul hlog1)).sub hB4).const_mul (2 / y ^ 4)))
  have h2 : Tendsto (hlPrim y) (𝓝[<] 1) _ := h.congr' (by
    filter_upwards [eventually_mem_Ioo_one] with w hw
    simp only [Function.comp_apply]
    rw [hlPrim, ← sub_eq_zero, ← hlQ0_add_hlQ1_mul_ell hy0 hw]
    simp only [hlK1, hlKm1, hlKy]
    ring)
  convert h2 using 2
  have e1 : (1 - y ^ 2) / (1 + y) = 1 - y := by
    rw [div_eq_iff (by positivity)]
    ring
  simp only [hlPrimOne, hlB_one hy0, hlU_one, e1, sub_self, zero_div, mul_zero, Li₂_zero,
    log_one, zero_mul, mul_one, Li₂_neg_one]
  ring_nf

end QED.Chain.HeavyLepton
