/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSBadF

/-!
# Set (d), master `I₁₂`: the bad part of the bulk remainder on one region, exactly in `ε`

The order-`n` statements `QED.ThreeLoopD.integral_i12RA3Dn_add_i12RB3Dn` and
`QED.ThreeLoopD.integral_i12HSW_split` hold already before the expansion in `ε`. For
`‖ε‖ < 1/100`, in the chart `(x, s, u)` of the sector `t < v`, the sector `v < t` is carried by
the reflection `(ρ, θ) = (xs, s⁻¹)` onto `i12HSDom = {s > 1, 0 < x < s⁻¹}`, where its main term
`SecWt(xs, s⁻¹) G_B(xs, s⁻¹, u) / s` is `SecWt(x, s) G_A(x, s, u)`
(`QED.ThreeLoopD.i12HS_pull_eps`, from `QED.ThreeLoopD.i12GA_reflect`). Hence

  `R_A(ε) + R_B(ε) = ∫_{Reg} W_ε`   (`QED.ThreeLoopD.integral_i12RA3_add_i12RB3_eps`),

`W_ε = QED.ThreeLoopD.i12HSWe`, `Reg = i12HSReg`, and for `‖ε‖ < 1/200` the bad part
`QED.ThreeLoopD.i12HSBadF` is

  `Bad(ε) = R₁(ε) + ∫_{Reg} (W_ε - Good_ε) - ∫_{(0,1) × (0,∞) × (0,1) \ Reg} Good_ε`

with all three integrals absolutely convergent (`QED.ThreeLoopD.i12HSBadF_eq_reg`). This is the
starting point of the `ε`-exact decomposition of the bad part: on `Reg` the difference
`W_ε - Good_ε` carries the factor `(1 - xs)^{-ε} - 1` (it lives on `t = xs = 1`).

## Main results

* `QED.ThreeLoopD.i12HS_cov_complex`: the reflection as a change of variables, complex values.
* `QED.ThreeLoopD.i12HS_pull_eps`.
* `QED.ThreeLoopD.integral_i12RA3_add_i12RB3_eps`, `QED.ThreeLoopD.i12HSBadF_eq_reg`.
-/

@[expose] public section

open Complex Set MeasureTheory Metric

namespace QED.ThreeLoopD

/-- The sector weight under the reflection: `SecWt(xs, s⁻¹) = s SecWt(x, s) (s⁻¹)^{3ε}`. -/
theorem i12HS_secWt_pull (ε : ℂ) {x s : ℝ} (hs0 : 0 < s) (hx : 0 < x) :
    i12SecWt ε (x * s) s⁻¹ = (s : ℂ) * i12SecWt ε x s * ((s⁻¹ : ℝ) : ℂ) ^ (3 * ε) := by
  have hsi : 0 < s⁻¹ := inv_pos.2 hs0
  simp only [i12SecWt]
  rw [i12_cpow_lin (mul_pos hx hs0), i12_cpow_lin hsi, i12_cpow_lin hx, i12_cpow_lin hs0,
    i12_cpow_lin hsi, Real.log_mul hx.ne' hs0.ne', Real.log_inv]
  have hsexp : (s : ℂ) = exp (Real.log s : ℂ) := by
    rw [← ofReal_exp, Real.exp_log hs0]
  rw [hsexp, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
  congr 1
  push_cast
  ring

/-- **The pulled-back integrand of `R_B`**: for `s > 1`, `0 < x`, `xs < 1`, `u ∈ (0, 1)`,
`D_B(xs, s⁻¹, u)/s = SecWt(x, s) G_A(x, s, u) + s⁻¹ SecWt(xs, s⁻¹) (faces of G_B)`. -/
theorem i12HS_pull_eps (ε : ℂ) {x s u : ℝ} (hs : 1 < s) (hx : 0 < x) (hxs : x * s < 1)
    (hu0 : 0 < u) (hu1 : u < 1) :
    i12RB3Ig ε (x * s, s⁻¹, u) / (s : ℂ) =
      i12SecWt ε x s * i12GA ε x s u + (s : ℂ)⁻¹ * (i12SecWt ε (x * s) s⁻¹ *
        (-i12GB ε 0 s⁻¹ u - i12GB0 ε (x * s) u + i12GB0 ε 0 u)) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hsi : 0 < s⁻¹ := inv_pos.2 hs0
  have hx1 : x < 1 := by
    have : x * 1 < x * s := mul_lt_mul_of_pos_left hs hx
    linarith
  have hR := i12GA_reflect ε (ρ := x * s) (θ := s⁻¹) hsi hu0 hu1
    (by rw [show x * s * s⁻¹ = x by field_simp]; exact i12H_pos (by linarith))
  rw [show x * s * s⁻¹ = x by field_simp, inv_inv] at hR
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs0.ne'
  simp only [i12RB3Ig]
  rw [hR, i12HS_secWt_pull ε hs0 hx]
  field_simp
  ring


/-- **The reflection as a change of variables**, for complex-valued integrands. -/
theorem i12HS_cov_complex {f : ℝ × ℝ × ℝ → ℂ} (hf : Measurable f) (hI : IntegrableOn f i12Cube) :
    IntegrableOn (fun z => f (z.1 * z.2.1, z.2.1⁻¹, z.2.2) / (z.2.1 : ℂ)) i12HSDom ∧
      ∫ z in i12Cube, f z = ∫ z in i12HSDom, f (z.1 * z.2.1, z.2.1⁻¹, z.2.2) / (z.2.1 : ℂ) := by
  have hre := i12HS_cov (f := fun z => (f z).re) (Complex.measurable_re.comp hf) hI.re
  have him := i12HS_cov (f := fun z => (f z).im) (Complex.measurable_im.comp hf) hI.im
  have hI' : IntegrableOn (fun z => f (z.1 * z.2.1, z.2.1⁻¹, z.2.2) / (z.2.1 : ℂ)) i12HSDom := by
    refine Integrable.re_im_iff.1 ⟨?_, ?_⟩
    · simp only [RCLike.re_to_complex, div_ofReal_re]; exact hre.1
    · simp only [RCLike.im_to_complex, div_ofReal_im]; exact him.1
  refine ⟨hI', Complex.ext ?_ ?_⟩
  · have e1 := integral_re hI
    have e2 := integral_re hI'
    simp only [RCLike.re_to_complex, div_ofReal_re] at e1 e2
    rw [← e1, ← e2, hre.2]
  · have e1 := integral_im hI
    have e2 := integral_im hI'
    simp only [RCLike.im_to_complex, div_ofReal_im] at e1 e2
    rw [← e1, ← e2, him.2]

theorem measurable_i12RA3Ig (ε : ℂ) : Measurable (i12RA3Ig ε) := by
  unfold i12RA3Ig i12SecWt i12GA i12GA0 i12Phi0 i12H; fun_prop

theorem measurable_i12RB3Ig (ε : ℂ) : Measurable (i12RB3Ig ε) := by
  unfold i12RB3Ig i12SecWt i12GB i12GB0 i12Phi0 i12H; fun_prop

theorem integrableOn_i12RA3Ig {ε : ℂ} (hε : ‖ε‖ < 1 / 100) : IntegrableOn (i12RA3Ig ε) i12Cube :=
  Integrable.mono' (integrable_i12Maj3.const_mul 20000) (measurable_i12RA3Ig ε).aestronglyMeasurable
    (ae_restrict_of_forall_mem i12_measurableSet3 fun _ hz => norm_i12RA3_integrand_le hε hz)

theorem integrableOn_i12RB3Ig {ε : ℂ} (hε : ‖ε‖ < 1 / 100) : IntegrableOn (i12RB3Ig ε) i12Cube :=
  Integrable.mono' (integrable_i12Maj3.const_mul 20000) (measurable_i12RB3Ig ε).aestronglyMeasurable
    (ae_restrict_of_forall_mem i12_measurableSet3 fun _ hz => norm_i12RB3_integrand_le hε hz)

/-- The integrand of `R_A + R_B` on `i12HSReg`, exactly in `ε`: the integrand of `R_A` for
`s < 1`, and for `s > 1` the main term `SecWt(x, s) G_A(x, s, u)` plus the reflected face
terms of `R_B`. -/
noncomputable def i12HSWe (ε : ℂ) (x s u : ℝ) : ℂ :=
  if s < 1 then i12RA3Ig ε (x, s, u) else
    i12SecWt ε x s * i12GA ε x s u + (s : ℂ)⁻¹ * (i12SecWt ε (x * s) s⁻¹ *
      (-i12GB ε 0 s⁻¹ u - i12GB0 ε (x * s) u + i12GB0 ε 0 u))

/-- **The two sectors as one integral**, exactly in `ε`:
`R_A(ε) + R_B(ε) = ∫_{i12HSReg} W_ε` for `‖ε‖ < 1/100`. -/
theorem integral_i12RA3_add_i12RB3_eps {ε : ℂ} (hε : ‖ε‖ < 1 / 100) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSWe ε z.1 z.2.1 z.2.2) i12HSReg ∧
      i12RA3 ε + i12RB3 ε = ∫ z in i12HSReg, i12HSWe ε z.1 z.2.1 z.2.2 := by
  obtain ⟨hP, hPe⟩ := i12HS_cov_complex (measurable_i12RB3Ig ε) (integrableOn_i12RB3Ig hε)
  have hC : MeasurableSet i12Cube :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have eA : EqOn (i12RA3Ig ε) (fun z => i12HSWe ε z.1 z.2.1 z.2.2) i12Cube := fun z hz => by
    simp only [i12HSWe, hz.2.1.2, ↓reduceIte]
  have eB : EqOn (fun z : ℝ × ℝ × ℝ => i12RB3Ig ε (z.1 * z.2.1, z.2.1⁻¹, z.2.2) / (z.2.1 : ℂ))
      (fun z => i12HSWe ε z.1 z.2.1 z.2.2) i12HSDom := fun z hz => by
    obtain ⟨hs, hx, hu⟩ := hz
    have hs1 : (1 : ℝ) < z.2.1 := hs
    have hs0 : 0 < z.2.1 := zero_lt_one.trans hs1
    have : ¬ z.2.1 < 1 := not_lt.2 hs1.le
    simp only [i12HSWe, this, ↓reduceIte]
    have hxs : z.1 * z.2.1 < 1 := by
      have := mul_lt_mul_of_pos_right hx.2 hs0
      rwa [inv_mul_cancel₀ hs0.ne'] at this
    exact i12HS_pull_eps ε hs1 hx.1 hxs hu.1 hu.2
  have iA := (integrableOn_i12RA3Ig hε).congr_fun eA hC
  have iB := hP.congr_fun eB measurableSet_i12HSDom
  refine ⟨iA.union iB, ?_⟩
  rw [setIntegral_union disjoint_i12Cube_i12HSDom measurableSet_i12HSDom iA iB,
    ← setIntegral_congr_fun hC eA, ← setIntegral_congr_fun measurableSet_i12HSDom eB, ← hPe]
  rfl


/-- **The bad part on one region**, exactly in `ε`: for `‖ε‖ < 1/200`,
`Bad(ε) = R₁(ε) + ∫_{Reg} (W_ε - Good_ε) - ∫_{(0,1) × (0,∞) × (0,1) \ Reg} Good_ε`. -/
theorem i12HSBadF_eq_reg {ε : ℂ} (hε : ‖ε‖ < 1 / 200) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSWe ε z.1 z.2.1 z.2.2 - i12HSGood ε z.1 z.2.1 z.2.2)
        i12HSReg ∧
      IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSGood ε z.1 z.2.1 z.2.2)
        ((Ioo 0 1 ×ˢ (Ioi 0 ×ˢ Ioo 0 1)) \ i12HSReg) ∧
      i12HSBadF ε = i12R1 ε + ((∫ z in i12HSReg,
        (i12HSWe ε z.1 z.2.1 z.2.2 - i12HSGood ε z.1 z.2.1 z.2.2)) -
          ∫ z in (Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1)) \ i12HSReg,
            i12HSGood ε z.1 z.2.1 z.2.2) := by
  have hε' : ‖ε‖ < 1 / 100 := by linarith
  obtain ⟨hW, hWe⟩ := integral_i12RA3_add_i12RB3_eps hε'
  have hG := integrableOn_i12HSGood hε'
  have hGR := hG.mono_set i12HSReg_subset
  have hReg : MeasurableSet i12HSReg :=
    (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)).union
      measurableSet_i12HSDom
  refine ⟨hW.sub hGR, hG.mono_set sdiff_subset, ?_⟩
  rw [integral_sub hW hGR, setIntegral_sdiff hReg hG i12HSReg_subset, ← hWe]
  simp only [i12HSBadF, i12HSGoodI]
  ring

end QED.ThreeLoopD
