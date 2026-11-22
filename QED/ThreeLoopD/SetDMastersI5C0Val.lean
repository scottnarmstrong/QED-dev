/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C0Sub
public import QED.Polylog.Reflection
public import QED.Polylog.DilogPM
public import QED.Polylog.ExtraIntegralsC
public import QED.Polylog.Deriv

/-!
# Set (d), master `I₅`: the kernel at `ε = 0` in closed form

The function (`QED.ThreeLoopD.i5PsiP`)

  `P(v) = -Li₂((1 - ξ)(1 + vξ)) - 2 log ξ log (1 + vξ) - 3 log v log (1 + vξ) - 3 Li₂(-vξ)`
    `- log² (1 + vξ)/2 - Li₂(ξ/(1 + vξ))`

is a primitive of `QED.ThreeLoopD.i5Psi ξ` on `(0, 1)`, continuous on `[0, 1]`. With the
reflection, duplication and Landen identities, `P(1) - P(0) = 2 Li₂(ξ) + log ξ log (1 - ξ)`
(`QED.ThreeLoopD.integral_i5Psi`). With `QED.ThreeLoopD.lintegral_i5Phi0` this gives

  `t K₀(t) = 2 Li₂(ξ) + log ξ log (1 - ξ)`, `ξ = ξ(t)` (`QED.ThreeLoopD.i5Ker_zero_eq`).

## Main results

* `QED.ThreeLoopD.integral_i5Psi`, `QED.ThreeLoopD.i5Ker_zero_eq`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- The value `2 Li₂(ξ) + log ξ log (1 - ξ)` of `t K₀(t)`. -/
noncomputable def i5F0 (ξ : ℝ) : ℝ := 2 * Li₂ ξ + log ξ * log (1 - ξ)

/-- The primitive in `v` of `QED.ThreeLoopD.i5Psi ξ`. -/
noncomputable def i5PsiP (ξ v : ℝ) : ℝ :=
  -Li₂ ((1 - ξ) * (1 + v * ξ)) - 2 * log ξ * log (1 + v * ξ) - 3 * (log v * log (1 + v * ξ)) -
    3 * Li₂ (-(v * ξ)) - log (1 + v * ξ) ^ 2 / 2 - Li₂ (ξ / (1 + v * ξ))

theorem hasDerivAt_i5PsiP {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i5PsiP ξ) (i5Psi ξ v) v := by
  obtain ⟨h0, h1⟩ := hξ
  obtain ⟨v0, v1⟩ := hv
  have hw : 0 < 1 + v * ξ := by positivity
  have hy : 0 < 1 - ξ := by linarith
  have ha1 : (1 - ξ) * (1 + v * ξ) ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by
    nlinarith [mul_lt_mul_of_pos_right v1 (mul_pos h0 hy)]⟩
  have ha3 : ξ / (1 + v * ξ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one hw).mpr (by nlinarith)⟩
  have hvξ : |(-(v * ξ))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity)]; nlinarith
  have hvξ0 : -(v * ξ) ≠ 0 := by have : 0 < v * ξ := by positivity
                                 linarith
  have hd : HasDerivAt (fun v => 1 + v * ξ) ξ v := by
    simpa using ((hasDerivAt_id' v).mul_const ξ).const_add 1
  have hlw := hd.log hw.ne'
  have hL1 := (hasDerivAt_Li₂' ha1).comp v (hd.const_mul (1 - ξ))
  have hL2 := (hasDerivAt_Li₂ hvξ hvξ0).comp v ((hasDerivAt_id' v).mul_const ξ).neg
  have hL3 := (hasDerivAt_Li₂' ha3).comp v ((hasDerivAt_const v ξ).div hd hw.ne')
  have hlv := Real.hasDerivAt_log v0.ne'
  have e := ((((hL1.neg.sub (hlw.const_mul (2 * log ξ))).sub ((hlv.mul hlw).const_mul 3)).sub
    (hL2.const_mul 3)).sub ((hlw.pow 2).div_const 2)).sub hL3
  convert e using 1
  · funext y
    simp only [i5PsiP, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply,
      Function.comp_apply]
  rw [show 1 - (1 - ξ) * (1 + v * ξ) = ξ * (1 - v + v * ξ) by ring,
    show 1 - -(v * ξ) = 1 + v * ξ by ring,
    show 1 - ξ / (1 + v * ξ) = (1 - ξ + v * ξ) / (1 + v * ξ) by field_simp; ring,
    Real.log_mul h0.ne' (by nlinarith), Real.log_div (by nlinarith) hw.ne']
  unfold i5Psi
  field_simp
  ring

theorem continuousOn_log_mul_log_one_add {ξ : ℝ} (h0 : 0 < ξ) :
    ContinuousOn (fun v => log v * log (1 + v * ξ)) (Icc 0 1) := by
  intro v hv
  rcases eq_or_lt_of_le hv.1 with h | h
  · subst h
    refine (continuousWithinAt_Ioi_iff_Ici.mp ?_).mono Icc_subset_Ici_self
    have hm : Tendsto (fun v : ℝ => v * ξ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx =>
        mul_pos hx h0⟩
      have hc : Continuous fun v : ℝ => v * ξ := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hl : Tendsto (fun v : ℝ => log (1 + v * ξ)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun v : ℝ => log (1 + v * ξ)) (𝓝 0) (𝓝 (log (1 + 0 * ξ))) :=
        ((continuous_const.add (continuous_id.mul continuous_const)).continuousAt.log
          (by norm_num)).tendsto
      simpa using this.mono_left nhdsWithin_le_nhds
    have h2 := ((tendsto_log_mul_log_one_add_zero.comp hm).sub (hl.const_mul (log ξ)))
    rw [ContinuousWithinAt]
    simp only [log_zero, zero_mul]
    refine (h2.congr' ?_).trans (by simp)
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    simp only [Function.comp, Real.log_mul hx0.ne' h0.ne']
    ring
  · exact ((Real.continuousAt_log h.ne').mul ((continuous_const.add
      (continuous_id.mul (continuous_const (y := ξ)))).continuousAt.log
        (ne_of_gt (by positivity : (0 : ℝ) < 1 + v * ξ)))).continuousWithinAt

theorem continuousOn_i5PsiP {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (i5PsiP ξ) (Icc 0 1) := by
  obtain ⟨h0, h1⟩ := hξ
  have hw : ∀ v ∈ Icc (0 : ℝ) 1, 0 < 1 + v * ξ := fun v hv => by nlinarith [hv.1]
  have hg : Continuous fun v : ℝ => 1 + v * ξ := by fun_prop
  have hlw : ContinuousOn (fun v => log (1 + v * ξ)) (Icc 0 1) :=
    hg.continuousOn.log fun v hv => (hw v hv).ne'
  have c1 : ContinuousOn (fun v => Li₂ ((1 - ξ) * (1 + v * ξ))) (Icc 0 1) :=
    continuousOn_Li₂.comp (continuous_const.mul hg).continuousOn fun v hv => by
      have a := hv.1; have b := hv.2
      have hy : 0 ≤ 1 - ξ := by linarith
      have : 0 ≤ (1 - ξ) * (1 + v * ξ) := mul_nonneg hy (by nlinarith)
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right b (mul_nonneg h0.le hy)]
  have c2 : ContinuousOn (fun v => Li₂ (-(v * ξ))) (Icc 0 1) :=
    continuousOn_Li₂.comp (continuous_id.mul (continuous_const (y := ξ))).neg.continuousOn
      fun v hv => by
        have a := hv.1; have b := hv.2
        constructor <;> nlinarith [mul_le_mul_of_nonneg_right b h0.le, mul_nonneg a h0.le]
  have c3 : ContinuousOn (fun v => Li₂ (ξ / (1 + v * ξ))) (Icc 0 1) := by
    refine continuousOn_Li₂.comp (continuousOn_const.div hg.continuousOn
      fun v hv => (hw v hv).ne') fun v hv => ⟨?_, ?_⟩
    · have := hw v hv; have : 0 < ξ / (1 + v * ξ) := by positivity
      linarith
    · exact (div_le_one (hw v hv)).mpr (by nlinarith [hv.1])
  have c4 := continuousOn_log_mul_log_one_add h0
  have e : i5PsiP ξ = fun v => -Li₂ ((1 - ξ) * (1 + v * ξ)) - 2 * log ξ * log (1 + v * ξ) -
      3 * (log v * log (1 + v * ξ)) - 3 * Li₂ (-(v * ξ)) - log (1 + v * ξ) ^ 2 / 2 -
      Li₂ (ξ / (1 + v * ξ)) := rfl
  rw [e]
  exact (((((c1.neg.sub (continuousOn_const.mul hlw)).sub (continuousOn_const.mul c4)).sub
    (continuousOn_const.mul c2)).sub ((hlw.pow 2).div_const 2)).sub c3)

theorem i5Psi_nonneg {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 ≤ i5Psi ξ v := by
  obtain ⟨h0, h1⟩ := hξ
  obtain ⟨v0, v1⟩ := hv
  have ha : 0 < 1 - v + v * ξ := by nlinarith
  have hb : 0 < 1 - ξ + v * ξ := by nlinarith
  have hl : log ξ + 3 * log v + log (1 - ξ + v * ξ) = log (ξ * v ^ 3 * (1 - ξ + v * ξ)) := by
    rw [Real.log_mul (by positivity) hb.ne', Real.log_mul h0.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have hle : ξ * v ^ 3 * (1 - ξ + v * ξ) ≤ 1 - v + v * ξ := by
    have hv2 : v ^ 2 ≤ 1 := by nlinarith
    have hv3 : v ^ 3 ≤ v := by nlinarith [mul_le_mul_of_nonneg_left hv2 v0.le]
    have : ξ * v * (1 - ξ + v * ξ) ≤ 1 - v + v * ξ := by nlinarith [mul_pos h0 h0]
    nlinarith [mul_le_mul_of_nonneg_left hv3 (by positivity : 0 ≤ ξ * (1 - ξ + v * ξ))]
  have : log (ξ * v ^ 3 * (1 - ξ + v * ξ)) ≤ log (1 - v + v * ξ) :=
    Real.log_le_log (by positivity) hle
  unfold i5Psi
  exact mul_nonneg (by positivity) (by linarith)

theorem integrableOn_i5Psi {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (i5Psi ξ) (Ioo 0 1) :=
  (intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_i5PsiP hξ)
    (fun _ hv => hasDerivAt_i5PsiP hξ hv) fun _ hv => i5Psi_nonneg hξ hv).mono_set
    Ioo_subset_Ioc_self

/-- **The integral over `v`**: `∫₀¹ i5Psi ξ = 2 Li₂(ξ) + log ξ log (1 - ξ)`. -/
theorem integral_i5Psi {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ∫ v in Ioo (0 : ℝ) 1, i5Psi ξ v = i5F0 ξ := by
  obtain ⟨h0, h1⟩ := hξ
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_i5PsiP ⟨h0, h1⟩) (fun v hv => hasDerivAt_i5PsiP ⟨h0, h1⟩ hv)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact integrableOn_i5Psi ⟨h0, h1⟩))]
  have hR := Li₂_add_Li₂_one_sub h0.le h1.le
  have hR2 := Li₂_add_Li₂_one_sub (sq_nonneg ξ) (by nlinarith : ξ ^ 2 ≤ 1)
  have hD := Li₂_add_Li₂_neg (x := ξ) (by rw [abs_of_pos h0]; exact h1.le)
  have hLa : Li₂ (ξ / (1 + ξ)) = -Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2 :=
    Li_two_div_one_add (u := ξ) ⟨h0, h1⟩
  have hl2 : log (ξ ^ 2) = 2 * log ξ := by rw [Real.log_pow]; push_cast; ring
  have hl3 : log (1 - ξ ^ 2) = log (1 - ξ) + log (1 + ξ) := by
    rw [show 1 - ξ ^ 2 = (1 - ξ) * (1 + ξ) by ring, Real.log_mul (by linarith) (by linarith)]
  unfold i5PsiP i5F0
  simp only [zero_mul, add_zero, one_mul, neg_zero, Li₂_zero, log_zero, log_one, mul_zero,
    div_one, zero_pow two_ne_zero, zero_div, sub_zero]
  rw [show (1 - ξ) * (1 + ξ) = 1 - ξ ^ 2 by ring]
  rw [hl2, hl3] at hR2
  linear_combination (norm := skip) -hR2 + hR - 2 * hD - hLa
  ring_nf

/-- **The kernel at `ε = 0` in closed form**: `t K₀(t) = 2 Li₂(ξ) + log ξ log (1 - ξ)`. -/
theorem i5Ker_zero_eq {t : ℝ} (ht : 0 < t) :
    i5Ker 0 t = ((i5F0 (i13Xi t) / t : ℝ) : ℂ) := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have hL := lintegral_i5Phi0 ⟨hx0, hx1⟩
  rw [← hT] at hL
  rw [i5Ker_zero ht, integral_eq_lintegral_of_nonneg_ae
    (ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun q hq =>
      i5Phi0_nonneg ht hq) (measurable_i5Phi0 t).aestronglyMeasurable, hL,
    ← ofReal_integral_eq_lintegral_ofReal ((integrableOn_i5Psi ⟨hx0, hx1⟩).div_const t)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun _ hv =>
        div_nonneg (i5Psi_nonneg ⟨hx0, hx1⟩ hv) ht.le),
    integral_div, ENNReal.toReal_ofReal (div_nonneg (setIntegral_nonneg measurableSet_Ioo
      fun _ hv => i5Psi_nonneg ⟨hx0, hx1⟩ hv) ht.le), integral_i5Psi ⟨hx0, hx1⟩]

end QED.ThreeLoopD
