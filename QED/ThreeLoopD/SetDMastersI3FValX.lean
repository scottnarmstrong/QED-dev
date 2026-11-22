/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3FValXClean
public import QED.ThreeLoopD.SetDMastersI3FValXFinal
public import QED.ThreeLoopD.SetDMastersI3FAnalytic
public import QED.ThreeLoopD.SetDMastersGamma2

/-!
# Set (d), master `I₃`: the value `i3FInt 0 = 2π⁴/15`

By `QED.ThreeLoopD.i3FInt_zero_eq_lintegral_g`, `i3FInt 0 = ∫₀¹ dx ∫₀^∞ de₁ g(x, e₁)`. Write
`c = x (1 - x)` and `Π = (1 + x α)(1 + (1 - x) α)`.

1. Substituting `e₁ = c α`, `c g(x, c α) = H(x, α)/(c α)` with `H = QED.ThreeLoopD.i3XH`.
2. `H(0, α) = 0`, `H` is symmetric under `x ↦ 1 - x`, and `∂ₓ H = D(x, α) =
   (1 - 2x) N(x α, (1 - x) α)/(c Π)` is nonnegative on `(0, 1/2]`. By the fundamental theorem
   of calculus, `H(x, α) = ∫₀^{min(x, 1 - x)} D(t, α) dt`.
3. Tonelli twice moves `t ∈ (0, 1/2)` outside; for fixed `t`, `x` then ranges over
   `(t, 1 - t)`.
4. `∫ₜ^{1-t} dx/(x (1 - x)) = 2 log ((1 - t)/t)` and `∫₀^∞ N/(α Π) dα = J(t)`
   (`QED.ThreeLoopD.i3X_lintegral_alpha`), so the integral is `∫₀^{1/2} 2 G(t) dt` with
   `G = QED.ThreeLoopD.i3XG`.
5. On `(0, 1/2)`, `2 G(t) = 4 (F(t) + F(1 - t))`, and `∫₀^{1/2} (F(t) + F(1 - t)) dt =
   ∫₀¹ F = π⁴/30` (`QED.ThreeLoopD.i3X_integral_F`).

## Main results

* `QED.ThreeLoopD.i3X_lintegral_VG_total`: `∫₀¹ dx ∫₀^∞ de₁ g(x, e₁) = 2π⁴/15`.
* `QED.ThreeLoopD.i3FInt_zero_eq`: `i3FInt 0 = 2π⁴/15`.
* `QED.ThreeLoopD.setDI3F_zero`: `F(0) = π⁴/15`.
* `QED.ThreeLoopD.hasTruncLaurent_I3_of_I3Rel`: the expansion of `I₃` from the IBP relation
  `QED.ThreeLoopD.SetDMasters.I3Rel` and the expansions of `I₁₂, I₁₃, I₁₄, I₁₈`;
  `QED.ThreeLoopD.hasTruncLaurent_I3_of_I3Rel_I14_I18` inserts the proved `I₁₄, I₁₈`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped ENNReal
open QED.TwoLoop.UnitXClose

namespace QED.ThreeLoopD

/-! ### The change of variables `e₁ = x (1 - x) α` -/

theorem i3X_lintegral_scale_Ioi {l : ℝ} (hl : 0 < l) (g : ℝ → ℝ≥0∞) :
    ∫⁻ e in Ioi (0 : ℝ), g e = ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal l * g (l * a) := by
  have hd : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s => l * s) l (Ioi 0) s :=
    fun s _ => ((hasDerivAt_id s).const_mul l).hasDerivWithinAt.congr_deriv (mul_one l)
  have hinj : InjOn (fun s : ℝ => l * s) (Ioi 0) :=
    fun s _ t _ h => mul_left_cancel₀ hl.ne' h
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj g
  rw [image_mul_left_Ioi hl, mul_zero, abs_of_pos hl] at h
  exact h

theorem i3X_lintegral_VG {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ e1 in Ioi (0 : ℝ), ENNReal.ofReal (i3VG x e1) =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (i3XH x a / (x * (1 - x) * a)) := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  rw [i3X_lintegral_scale_Ioi hc]
  refine setLIntegral_congr_fun measurableSet_Ioi fun a (ha : 0 < a) => ?_
  rw [← ENNReal.ofReal_mul hc.le, i3VG, i3XH_eq hx ha]
  congr 1
  field_simp

/-! ### The fundamental theorem of calculus in `x` -/

/-- `∂ₓ` of `QED.ThreeLoopD.i3XH`. -/
noncomputable def i3XD (t a : ℝ) : ℝ :=
  (1 - 2 * t) * i3XN (t * a) ((1 - t) * a) / (t * (1 - t) * ((1 + t * a) * (1 + (1 - t) * a)))

theorem i3XD_nonneg {t a : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) (ha : 0 < a) : 0 ≤ i3XD t a := by
  have hy : 0 < 1 - t := by linarith
  unfold i3XD
  exact div_nonneg (mul_nonneg (by linarith) (i3XN_nonneg (mul_pos ht0 ha) (mul_pos hy ha).le))
    (by positivity)

theorem i3X_ofReal_H_half {m a : ℝ} (hm0 : 0 < m) (hm : m ≤ 1 / 2) (ha : 0 < a) :
    ENNReal.ofReal (i3XH m a) = ∫⁻ t in Ioo (0 : ℝ) m, ENNReal.ofReal (i3XD t a) := by
  have hcont : ContinuousOn (fun x => i3XH x a) (Icc 0 m) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      have ht : Tendsto (fun x => i3XH x a) (𝓝[>] 0) (𝓝 (i3XH 0 a)) := by
        rw [i3XH_zero ha]; exact tendsto_i3XH_zero ha
      exact (continuousWithinAt_Ioi_iff_Ici.1 ht).mono Icc_subset_Ici_self
    · exact (hasDerivAt_i3XH ⟨h, by linarith [hx.2]⟩ ha).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo 0 m, HasDerivAt (fun x => i3XH x a) (i3XD x a) x :=
    fun x hx => hasDerivAt_i3XH ⟨hx.1, by linarith [hx.2]⟩ ha
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv
    fun x hx => i3XD_nonneg hx.1 (by linarith [hx.2]) ha
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hm0.le hcont hderiv
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hm0.le).2 hint)
  rw [i3XH_zero ha, sub_zero, intervalIntegral.integral_of_le hm0.le] at hftc
  rw [← hftc, ofReal_integral_eq_lintegral_ofReal hint, setLIntegral_congr Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact i3XD_nonneg hx.1 (hx.2.trans hm) ha

theorem i3X_setLIntegral_ite {s u : Set ℝ} (hs : MeasurableSet s) (hu : MeasurableSet u)
    {p : ℝ → Prop} [DecidablePred p] (f : ℝ → ℝ) (h : ∀ t, t ∈ u ↔ t ∈ s ∧ p t) :
    ∫⁻ t in s, ENNReal.ofReal (if p t then f t else 0) = ∫⁻ t in u, ENNReal.ofReal (f t) := by
  rw [← lintegral_indicator hs, ← lintegral_indicator hu]
  refine lintegral_congr fun t => ?_
  by_cases h1 : t ∈ s <;> by_cases h2 : p t <;> simp [indicator, h, h1, h2]

theorem i3X_ofReal_H {x a : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    ENNReal.ofReal (i3XH x a) = ∫⁻ t in Ioo (0 : ℝ) (1 / 2),
      ENNReal.ofReal (if t < x ∧ t < 1 - x then i3XD t a else 0) := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases le_total x (1 / 2) with h | h
  · rw [i3X_ofReal_H_half hx0 h ha, i3X_setLIntegral_ite measurableSet_Ioo measurableSet_Ioo]
    intro t
    simp only [mem_Ioo]
    constructor
    · intro ht; exact ⟨⟨ht.1, by linarith [ht.2]⟩, ht.2, by linarith [ht.2]⟩
    · intro ht; exact ⟨ht.1.1, ht.2.1⟩
  · rw [← i3XH_symm, i3X_ofReal_H_half (by linarith) (by linarith) ha,
      i3X_setLIntegral_ite measurableSet_Ioo measurableSet_Ioo]
    intro t
    simp only [mem_Ioo]
    constructor
    · intro ht; exact ⟨⟨ht.1, by linarith [ht.2]⟩, by linarith [ht.2], ht.2⟩
    · intro ht; exact ⟨ht.1.1, ht.2.2⟩

/-! ### Tonelli -/

/-- The triple integrand `1{t < min(x, 1 - x)} ∂ₜH(t, α) / (x (1 - x) α)`. -/
noncomputable def i3XPhi (x a t : ℝ) : ℝ :=
  if t < x ∧ t < 1 - x then i3XD t a / (x * (1 - x) * a) else 0

theorem measurable_i3XPhi : Measurable fun p : ℝ × ℝ × ℝ => i3XPhi p.1 p.2.1 p.2.2 := by
  unfold i3XPhi i3XD i3XN
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_fst).inter
    (measurableSet_lt (measurable_snd.comp measurable_snd) (measurable_const.sub measurable_fst))

theorem i3X_lintegral_H_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (i3XH x a / (x * (1 - x) * a)) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ t in Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (i3XPhi x a t) := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  refine setLIntegral_congr_fun measurableSet_Ioi fun a (ha : 0 < a) => ?_
  have hk : 0 ≤ 1 / (x * (1 - x) * a) := by positivity
  rw [div_eq_inv_mul, ← one_div, ENNReal.ofReal_mul hk, i3X_ofReal_H hx ha,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun t => ?_
  rw [← ENNReal.ofReal_mul hk, i3XPhi]
  split_ifs
  · congr 1; ring
  · simp

theorem i3X_lintegral_c {t : ℝ} (ht0 : 0 < t) (ht : t < 1 / 2) :
    ∫⁻ x in Ioo t (1 - t), ENNReal.ofReal (1 / (x * (1 - x))) =
      ENNReal.ofReal (2 * log ((1 - t) / t)) := by
  have hle : t ≤ 1 - t := by linarith
  have hd : ∀ x ∈ uIcc t (1 - t), HasDerivAt (fun x => log x - log (1 - x))
      (1 / (x * (1 - x))) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have h0 : 0 < x := by linarith [hx.1]
    have h1 : 0 < 1 - x := by linarith [hx.2]
    have : HasDerivAt (fun y => log y - log (1 - y)) (x⁻¹ - (-1) / (1 - x)) x :=
      (hasDerivAt_log h0.ne').sub (((hasDerivAt_id x).const_sub 1).log h1.ne')
    convert this using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun x => 1 / (x * (1 - x))) (uIcc t (1 - t)) := by
    rw [uIcc_of_le hle]
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
    have h0 : 0 < x := by linarith [hx.1]
    have h1 : 0 < 1 - x := by linarith [hx.2]
    positivity
  have hii := hcont.intervalIntegrable (μ := volume)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii
  rw [intervalIntegral.integral_of_le hle] at hftc
  have hio := (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hii
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hio, hftc]
  · congr 1
    rw [sub_sub_cancel, log_div (by linarith) ht0.ne']
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have h0 : 0 < x := by linarith [hx.1]
    have h1 : 0 < 1 - x := by linarith [hx.2]
    positivity

theorem i3X_lintegral_alpha_Phi {x t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ht0 : 0 < t)
    (ht : t < 1 / 2) :
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (i3XPhi x a t) =
      ENNReal.ofReal (if t < x ∧ t < 1 - x then
        1 / (x * (1 - x)) * ((1 - 2 * t) / (t * (1 - t)) * i3XJ t) else 0) := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hy : 0 < 1 - t := by linarith
  unfold i3XPhi
  split_ifs with hp
  · have hK : 0 ≤ 1 / (x * (1 - x)) * ((1 - 2 * t) / (t * (1 - t))) := by
      have : 0 ≤ 1 - 2 * t := by linarith
      positivity
    have hcg : ∀ a ∈ Ioi (0 : ℝ), ENNReal.ofReal (i3XD t a / (x * (1 - x) * a)) =
        ENNReal.ofReal (1 / (x * (1 - x)) * ((1 - 2 * t) / (t * (1 - t)))) *
        ENNReal.ofReal (i3XN (t * a) ((1 - t) * a) /
          (a * ((1 + t * a) * (1 + (1 - t) * a)))) := by
      intro a (ha : 0 < a)
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      unfold i3XD
      field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioi hcg,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      i3X_lintegral_alpha ⟨ht0, by linarith⟩ (by linarith), ← ENNReal.ofReal_mul hK]
    congr 1
    ring
  · simp

theorem i3X_lintegral_x_Phi {t : ℝ} (ht0 : 0 < t) (ht : t < 1 / 2) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (i3XPhi x a t) =
      ENNReal.ofReal (2 * i3XG t) := by
  have hy : 0 < 1 - t := by linarith
  have hC : 0 ≤ (1 - 2 * t) / (t * (1 - t)) * i3XJ t := by
    have : 0 ≤ 1 - 2 * t := by linarith
    have := i3XJ_nonneg ⟨ht0, by linarith⟩ (by linarith)
    positivity
  rw [setLIntegral_congr_fun measurableSet_Ioo fun x hx => i3X_lintegral_alpha_Phi hx ht0 ht,
    i3X_setLIntegral_ite measurableSet_Ioo measurableSet_Ioo]
  · have hcg : ∀ x ∈ Ioo t (1 - t), ENNReal.ofReal
        (1 / (x * (1 - x)) * ((1 - 2 * t) / (t * (1 - t)) * i3XJ t)) =
        ENNReal.ofReal ((1 - 2 * t) / (t * (1 - t)) * i3XJ t) *
          ENNReal.ofReal (1 / (x * (1 - x))) := by
      intro x hx
      rw [← ENNReal.ofReal_mul hC, mul_comm]
    rw [setLIntegral_congr_fun measurableSet_Ioo hcg,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, i3X_lintegral_c ht0 ht,
      ← ENNReal.ofReal_mul hC, i3XG]
    congr 1
    ring
  · intro x
    simp only [mem_Ioo]
    constructor
    · intro hx; exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hx.1, by linarith [hx.2]⟩
    · intro hx; exact ⟨hx.2.1, by linarith [hx.2.2]⟩

/-! ### The last integral over `(0, 1/2)` -/

theorem i3X_lintegral_final_half :
    ∫⁻ t in Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (2 * i3XG t) =
      ENNReal.ofReal (2 * π ^ 4 / 15) := by
  obtain ⟨hFi, hFv⟩ := i3X_integral_F
  set H : ℝ → ℝ := fun t => 4 * (i3XF t + i3XF (1 - t)) with hH
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hpos : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), 2 * i3XG t = H t := fun t ht => by
    rw [i3XG_eq ⟨ht.1, by linarith [ht.2]⟩ ht.2.ne, hH]; ring
  have hm : (1 / 2 : ℝ) ∈ uIcc (0 : ℝ) 1 := by rw [uIcc_of_le zero_le_one]; norm_num
  have h0m : (0 : ℝ) ∈ uIcc (0 : ℝ) 1 := left_mem_uIcc
  have h1m : (1 : ℝ) ∈ uIcc (0 : ℝ) 1 := right_mem_uIcc
  have hF0 : IntervalIntegrable i3XF volume 0 (1 / 2) := hFi.mono_set (uIcc_subset_uIcc h0m hm)
  have hF2 : IntervalIntegrable i3XF volume (1 / 2) 1 := hFi.mono_set (uIcc_subset_uIcc hm h1m)
  have hF1 : IntervalIntegrable (fun t => i3XF (1 - t)) volume 0 (1 / 2) := by
    have := hF2.comp_sub_left 1
    norm_num at this
    exact this.symm
  have hHi : IntervalIntegrable H volume 0 (1 / 2) := (hF0.add hF1).const_mul 4
  have hHo : IntegrableOn H (Ioo (0 : ℝ) (1 / 2)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hh).1 hHi).mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) (1 / 2))] H := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [← hpos t ht]
    exact mul_nonneg zero_le_two (i3XG_nonneg ⟨ht.1, by linarith [ht.2]⟩ ht.2.ne)
  rw [setLIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [hpos t ht],
    ← ofReal_integral_eq_lintegral_ofReal hHo hnn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hh, hH,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hF0 hF1,
    intervalIntegral.integral_comp_sub_left (fun t => i3XF t) 1]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, sub_zero,
    intervalIntegral.integral_add_adjacent_intervals hF0 hF2, hFv]
  ring

/-! ### Assembly -/

theorem i3X_lintegral_VG_total :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ e1 in Ioi (0 : ℝ), ENNReal.ofReal (i3VG x e1) =
      ENNReal.ofReal (2 * π ^ 4 / 15) := by
  have hm : ∀ x : ℝ, Measurable fun q : ℝ × ℝ => ENNReal.ofReal (i3XPhi x q.1 q.2) := fun x =>
    ENNReal.measurable_ofReal.comp (measurable_i3XPhi.comp
      (measurable_const.prodMk measurable_id))
  have hm2 : Measurable fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (i3XPhi q.1.1 q.2 q.1.2) :=
    ENNReal.measurable_ofReal.comp (measurable_i3XPhi.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  calc ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ e1 in Ioi (0 : ℝ), ENNReal.ofReal (i3VG x e1)
      = ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ a in Ioi (0 : ℝ), ∫⁻ t in Ioo (0 : ℝ) (1 / 2),
          ENNReal.ofReal (i3XPhi x a t) :=
        setLIntegral_congr_fun measurableSet_Ioo fun x hx => by
          rw [i3X_lintegral_VG hx, i3X_lintegral_H_eq hx]
    _ = ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) (1 / 2), ∫⁻ a in Ioi (0 : ℝ),
          ENNReal.ofReal (i3XPhi x a t) :=
        lintegral_congr fun x => lintegral_lintegral_swap (hm x).aemeasurable
    _ = ∫⁻ t in Ioo (0 : ℝ) (1 / 2), ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ a in Ioi (0 : ℝ),
          ENNReal.ofReal (i3XPhi x a t) :=
        lintegral_lintegral_swap (hm2.lintegral_prod_right').aemeasurable
    _ = ∫⁻ t in Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (2 * i3XG t) :=
        setLIntegral_congr_fun measurableSet_Ioo fun t ht => i3X_lintegral_x_Phi ht.1 ht.2
    _ = ENNReal.ofReal (2 * π ^ 4 / 15) := i3X_lintegral_final_half

/-- **The value of the dotted integral at `ε = 0`**: `i3FInt 0 = 2π⁴/15`. -/
theorem i3FInt_zero_eq : i3FInt 0 = 2 * (Real.pi : ℂ) ^ 4 / 15 := by
  rw [i3FInt_zero_eq_lintegral_g, i3X_lintegral_VG_total,
    ENNReal.toReal_ofReal (by positivity)]
  push_cast
  ring

/-- `F(0) = π⁴/15`. -/
theorem setDI3F_zero : setDI3F 0 = (Real.pi : ℂ) ^ 4 / 15 :=
  setDI3F_zero_of_i3FInt i3FInt_zero_eq

/-- **The `I₃` input**: only the IBP relation and the expansions of `I₁₂, I₁₃, I₁₄, I₁₈`
remain. -/
theorem hasTruncLaurent_I3_of_I3Rel {M : SetDMasters} (hrel : M.I3Rel setDI3F)
    (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h14 : HasTruncLaurent M.I14 setDLaurentI14 3)
    (h18 : HasTruncLaurent M.I18 setDLaurentI18 3) :
    HasTruncLaurent M.I3 setDLaurentI3 1 :=
  hasTruncLaurent_I3_of_i3FInt i3FInt_zero_eq hrel h12 h13 h14 h18

/-- The `I₃` input with the proved expansions of `I₁₄` and `I₁₈` inserted: the IBP relation and
the expansions of `I₁₂, I₁₃` remain. -/
theorem hasTruncLaurent_I3_of_I3Rel_I14_I18 {M : SetDMasters} (hrel : M.I3Rel setDI3F)
    (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h14 : M.I14 = setDMasterI14) (h18 : M.I18 = setDMasterI18) :
    HasTruncLaurent M.I3 setDLaurentI3 1 :=
  hasTruncLaurent_I3_of_I3Rel hrel h12 h13 (h14 ▸ hasTruncLaurent_setDMasterI14)
    (h18 ▸ hasTruncLaurent_setDMasterI18)

end QED.ThreeLoopD
