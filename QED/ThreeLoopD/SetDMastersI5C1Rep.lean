/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Sub

/-!
# Set (d), master `I₅`: `t K₁(t)` as an iterated integral in `(v, c)`

The integrands `QED.ThreeLoopD.i5Phi0` and `QED.ThreeLoopD.i5PhiQ1` are integrable on
`{a, c > 0}`: they are the angular integrals of the product-integrable functions
`QED.ThreeLoopD.i5H0` and `QED.ThreeLoopD.i5H1`. By `QED.ThreeLoopD.i5KerC_one_eq_integral`
and the substitutions `QED.ThreeLoopD.i5_integral_sub_ac`, with `y = 1 - ξ`, `t = y²/ξ`,
`x = v y`, `u = u(v) = t/x - x - t` and `U = (c + x)(t/x - c)/t`,

  `t K₁(t) = ∫₀¹ ∫₀^u |u'(v)| / (u (c + x)(t/x - c)) · B dc dv`,
  `B = (1 - 2 log 2 + 2 log U - log c)(y - x) - (y Λ(y, x) - x Λ(x, x)) - (y M(y) - x M(x))`

(`QED.ThreeLoopD.i5KerC_one_eq_rep`, the integrand is `QED.ThreeLoopD.i5K1F`).

## Main results

* `QED.ThreeLoopD.integrableOn_i5Phi0`, `QED.ThreeLoopD.integrableOn_i5PhiQ1`.
* `QED.ThreeLoopD.i5KerC_one_eq_rep`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ThreeLoopD

theorem integrableOn_i5PhiQ1 {t : ℝ} (ht : 0 < t) :
    IntegrableOn (i5PhiQ1 t) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have h := (integrable_i5H1 ht).integral_prod_right
  have h' : Integrable (fun q => ((i5PhiQ1 t q : ℝ) : ℂ))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :=
    h.congr (ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      fun q hq => i5_integral_i5H1 ht hq)
  exact h'.re

theorem integrableOn_i5Phi0 {t : ℝ} (ht : 0 < t) :
    IntegrableOn (i5Phi0 t) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have h := ((integrable_i5H0 ht).integral_prod_right).const_mul (i5Nrm 0)
  have h' : Integrable (fun q => ((i5Phi0 t q : ℝ) : ℂ))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :=
    h.congr (ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      fun q hq => i5Nrm_mul_integral_i5H0 ht hq)
  exact h'.re

theorem measurable_i5PhiQ1 (t : ℝ) : Measurable (i5PhiQ1 t) := by
  unfold i5PhiQ1 i5xq i5xA i5A i5Lx i5Mx
  fun_prop

/-- The integrand `t ((1 - 2 log 2) i5Phi0 + (2/π) i5PhiQ1)` of `t K₁(t)` over `(a, c)`. -/
noncomputable def i5G1q (t : ℝ) (q : ℝ × ℝ) : ℝ :=
  t * ((1 - 2 * Real.log 2) * i5Phi0 t q + 2 / Real.pi * i5PhiQ1 t q)

theorem i5KerC_one_eq_integral' {t : ℝ} (ht : 0 < t) :
    (t : ℂ) * i5KerC t 1 = ((∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5G1q t q : ℝ) : ℂ) := by
  rw [i5KerC_one_eq_integral ht]
  unfold i5G1q
  rw [integral_const_mul, integral_add ((integrableOn_i5Phi0 ht).const_mul _)
    ((integrableOn_i5PhiQ1 ht).const_mul _), integral_const_mul, integral_const_mul]
  push_cast
  ring

/-- The integrand of `t K₁(t)` in `(v, c)`: `|u'(v)| / (u (c + x)(t/x - c)) · B`. -/
noncomputable def i5K1F (ξ v c : ℝ) : ℝ :=
  (1 - ξ) / ξ * (1 / v ^ 2 + ξ) / (i5U ξ v * (c + v * (1 - ξ)) *
      ((1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) - c)) *
    ((1 - 2 * Real.log 2 + 2 * Real.log ((c + v * (1 - ξ)) *
        ((1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) - c) / ((1 - ξ) ^ 2 / ξ)) - Real.log c) *
        ((1 - ξ) - v * (1 - ξ)) -
      ((1 - ξ) * i5Lx ((1 - ξ) ^ 2 / ξ) (1 - ξ) (v * (1 - ξ)) -
        v * (1 - ξ) * i5Lx ((1 - ξ) ^ 2 / ξ) (v * (1 - ξ)) (v * (1 - ξ))) -
      ((1 - ξ) * i5Mx ((1 - ξ) ^ 2 / ξ) (1 - ξ) -
        v * (1 - ξ) * i5Mx ((1 - ξ) ^ 2 / ξ) (v * (1 - ξ))))

theorem i5xA_inv' {t x : ℝ} (ht : 0 < t) (hx : 0 < x) : i5xA t (t / x - x) = x := by
  unfold i5xA
  rw [i5A_inv ht hx]
  field_simp

/-- The pointwise form of the substituted integrand. -/
theorem i5K1F_eq {ξ v c : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo 0 (i5U ξ v)) :
    |-((1 - ξ) / ξ * (1 / v ^ 2 + ξ))| * (|c / ((1 - ξ) ^ 2 / ξ)| *
      i5G1q ((1 - ξ) ^ 2 / ξ) (c * (i5U ξ v - c) / ((1 - ξ) ^ 2 / ξ), c)) = i5K1F ξ v c := by
  obtain ⟨h0, h1⟩ := hξ
  obtain ⟨v0, v1⟩ := hv
  obtain ⟨c0, cu⟩ := hc
  have hy : 0 < 1 - ξ := by linarith
  set t := (1 - ξ) ^ 2 / ξ with ht
  have ht0 : 0 < t := by positivity
  set u := i5U ξ v with hu
  set x := v * (1 - ξ) with hx
  have hx0 : 0 < x := by positivity
  have hux : u = t / x - x - t := by rw [hu, i5U_eq ⟨h0, h1⟩ v0]
  have hyi : t / (1 - ξ) - (1 - ξ) = t := by rw [ht]; field_simp
  have hxy : i5xA t t = 1 - ξ := by
    have h := i5xA_inv' ht0 hy
    rwa [hyi] at h
  set a := c * (u - c) / t with ha
  have hX : c ^ 2 + a * t = c * u := by rw [ha]; field_simp; ring
  have hU : 1 + a + c = (c + x) * (t / x - c) / t := by rw [ha, hux]; field_simp; ring
  have hT : t + (c ^ 2 + a * t) / c = t / x - x := by
    rw [hX, mul_div_cancel_left₀ _ c0.ne', hux]; ring
  have hxq : i5xq t (a, c) = x := by
    unfold i5xq
    simp only
    rw [hT, i5xA_inv' ht0 hx0]
  have hcx : 0 < t / x - c := by linarith [show 0 < x by positivity]
  have hpos : 0 < c + x := by linarith
  have hu0 : 0 < u := c0.trans cu
  unfold i5G1q i5K1F
  rw [i5Phi0_eq ht0.le c0, hT, i5A_inv ht0 hx0]
  unfold i5PhiQ1
  simp only
  rw [hxq, hxy, hU, hX, ← ht, ← hu, ← hx]
  have hA : i5A t t = (1 - ξ) / (2 * t) := by
    have h := i5A_inv ht0 hy
    rwa [hyi] at h
  rw [hA, abs_neg, abs_of_pos (by positivity : 0 < (1 - ξ) / ξ * (1 / v ^ 2 + ξ)),
    abs_of_pos (by positivity : 0 < c / t)]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

/-- **`t K₁(t)` as an iterated integral in `(v, c)`.** -/
theorem i5KerC_one_eq_rep {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    (((1 - ξ) ^ 2 / ξ : ℝ) : ℂ) * i5KerC ((1 - ξ) ^ 2 / ξ) 1 =
      ((∫ v in Ioo (0 : ℝ) 1, ∫ c in Ioo 0 (i5U ξ v), i5K1F ξ v c : ℝ) : ℂ) := by
  have ht : 0 < (1 - ξ) ^ 2 / ξ := by
    have := hξ.1; have : 0 < 1 - ξ := by linarith [hξ.2]
    positivity
  have hm : Measurable (i5G1q ((1 - ξ) ^ 2 / ξ)) := by
    unfold i5G1q
    exact measurable_const.mul ((measurable_const.mul (measurable_i5Phi0 _)).add
      (measurable_const.mul (measurable_i5PhiQ1 _)))
  have hi : IntegrableOn (i5G1q ((1 - ξ) ^ 2 / ξ)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    (((integrableOn_i5Phi0 ht).const_mul _).add ((integrableOn_i5PhiQ1 ht).const_mul _)).const_mul _
  rw [i5KerC_one_eq_integral' ht, i5_integral_sub_ac hξ hm hi]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  rw [← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioo fun c hc => i5K1F_eq hξ hv hc

end QED.ThreeLoopD
