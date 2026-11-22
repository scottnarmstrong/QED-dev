/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSDom
public import QED.ThreeLoopD.SetDMastersI12RHighSCov

/-!
# Set (d), master `I₁₂`: the good part of the bulk remainder is holomorphic near `ε = 0`

With the integrable majorant of `QED.ThreeLoopD.SetDMastersI12RHighSDom`, uniform on
`‖ε‖ < 1/100`, the good part `QED.ThreeLoopD.i12HSGood` is absolutely integrable over
`(0, 1) × (0, ∞) × (0, 1)`, so

* the closed form `QED.ThreeLoopD.i12HS_integral_good` holds unconditionally for
  `0 < re ε`, `‖ε‖ < 1/100` (`QED.ThreeLoopD.i12HS_integral_good_of_norm`);
* `ε ↦ ∫ Good` (`QED.ThreeLoopD.i12HSGoodI`) is holomorphic on `‖ε‖ < 1/100`
  (`QED.ThreeLoopD.differentiableOn_i12HSGoodI`);
* its `n`-th derivative at `0` is the integral of the pointwise coefficients
  `Good_n = QED.ThreeLoopD.i12HSGoodDn n` (`QED.ThreeLoopD.iteratedDeriv_i12HSGoodI`,
  `QED.ThreeLoopD.iteratedDeriv_i12HSGoodI_eq_real`), by
  `QED.ThreeLoopD.i12_iteratedDeriv_integral_center`.

Finally the region `i12HSReg` of the merged sectors lies in `(0, 1) × (0, ∞) × (0, 1)`, and the
order-`n` integrand `W_n` of the bulk part splits as `∫_{Reg} W_n = ∫ Good_n + rest_n`, with
`rest_n = ∫_{Reg} (W_n - Good_n) - ∫_{(0,1) × (0,∞) × (0,1) \ Reg} Good_n`
(`QED.ThreeLoopD.integral_i12HSW_split`).

## Main results

* `QED.ThreeLoopD.integrableOn_i12HSGood`, `QED.ThreeLoopD.i12HS_integral_good_of_norm`.
* `QED.ThreeLoopD.differentiableOn_i12HSGoodI`.
* `QED.ThreeLoopD.iteratedDeriv_i12HSGoodI`, `QED.ThreeLoopD.iteratedDeriv_i12HSGoodI_eq_real`.
* `QED.ThreeLoopD.integral_i12HSW_split`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter

namespace QED.ThreeLoopD

/-- The region `(0, 1) × (0, ∞) × (0, 1)` of the good part. -/
theorem measurableSet_i12HSGoodReg :
    MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1)) :=
  measurableSet_Ioo.prod (measurableSet_Ioi.prod measurableSet_Ioo)

/-- **The good part is absolutely integrable** for `‖ε‖ < 1/100`. -/
theorem integrableOn_i12HSGood {ε : ℂ} (hε : ‖ε‖ < 1 / 100) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSGood ε z.1 z.2.1 z.2.2)
      (Ioo 0 1 ×ˢ (Ioi 0 ×ˢ Ioo 0 1)) :=
  Integrable.mono' integrableOn_i12HSGoodMaj (measurable_i12HSGood ε).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_i12HSGoodReg).2 (Eventually.of_forall fun _ hz =>
      norm_i12HSGood_le hε hz.1 hz.2.1 hz.2.2))

/-- **The good part in closed form**, unconditionally for `0 < re ε` and `‖ε‖ < 1/100`. -/
theorem i12HS_integral_good_of_norm {ε : ℂ} (hε : ‖ε‖ < 1 / 100) (h0 : 0 < ε.re) :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1), i12HSGood ε z.1 z.2.1 z.2.2 =
      i12HSMphi ε / (1 - ε) * i12HSP (ε - 1) ε -
        (2 - 3 * ε) * i12HSBw ε / (2 * ε) * i12HSP (-ε - 1) ε -
        (2 - 3 * ε) * i12HSBw ε / ε * i12HSP (2 * ε - 1) ε :=
  i12HS_integral_good h0 (by linarith [(re_le_norm ε).trans hε.le])
    (integrableOn_i12HSGood hε)

/-- The good part is entire in `ε` at each point of the region. -/
theorem differentiable_i12HSGood {x s u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hs : 0 < s)
    (hu : u ∈ Ioo (0 : ℝ) 1) : Differentiable ℂ fun ε => i12HSGood ε x s u := by
  have hA := i12HS_h_pos (x := x) (by linarith [hx.2])
  have hB := i12HS_h_pos (x := 0) (by norm_num)
  have e : (fun ε => i12HSGood ε x s u) = fun ε =>
      (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
          (((i12H x : ℝ) : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / i12H x)) -
        (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
          (((i12H 0 : ℝ) : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / i12H 0)) := by
    funext ε; simp only [i12HSGood]; ring
  rw [e]
  exact (differentiable_i12HSGoodH hx.1 hs hu hA).sub (differentiable_i12HSGoodH hx.1 hs hu hB)

/-- The integral of the good part, `ε ↦ ∫ Good`. -/
noncomputable def i12HSGoodI (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1), i12HSGood ε z.1 z.2.1 z.2.2

theorem i12HS_dom_ball {w : ℂ} {r : ℝ} (hwr : ball w r ⊆ ball (0 : ℂ) (1 / 100)) :
    ∀ᵐ z ∂(volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1))),
      ∀ v ∈ ball w r, ‖i12HSGood v z.1 z.2.1 z.2.2‖ ≤ i12HSGoodMaj z.1 z.2.1 z.2.2 :=
  (ae_restrict_iff' measurableSet_i12HSGoodReg).2 (Eventually.of_forall fun z hz v hv =>
    norm_i12HSGood_le (by simpa using hwr hv) hz.1 hz.2.1 hz.2.2)

theorem i12HS_diff_ball (w : ℂ) (r : ℝ) :
    ∀ᵐ z ∂(volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1))),
      DifferentiableOn ℂ (fun v => i12HSGood v z.1 z.2.1 z.2.2) (ball w r) :=
  (ae_restrict_iff' measurableSet_i12HSGoodReg).2 (Eventually.of_forall fun _ hz =>
    (differentiable_i12HSGood hz.1 hz.2.1 hz.2.2).differentiableOn)

/-- **The integral of the good part is holomorphic** on `‖ε‖ < 1/100`. -/
theorem differentiableOn_i12HSGoodI : DifferentiableOn ℂ i12HSGoodI (ball 0 (1 / 100)) := by
  intro w hw
  have hw' : ‖w‖ < 1 / 100 := by simpa using hw
  have hr : 0 < 1 / 100 - ‖w‖ := by linarith
  have hsub : ball w (1 / 100 - ‖w‖) ⊆ ball (0 : ℂ) (1 / 100) := by
    intro v hv
    rw [mem_ball] at hv
    rw [mem_ball_zero_iff]
    calc ‖v‖ ≤ ‖v - w‖ + ‖w‖ := by simpa using norm_add_le (v - w) w
      _ < 1 / 100 := by rw [← dist_eq_norm]; linarith
  obtain ⟨-, hd⟩ := i12_deriv_integral_eventuallyEq (z₁ := w) hr integrableOn_i12HSGoodMaj
    (fun v _ => (measurable_i12HSGood v).aestronglyMeasurable) (i12HS_dom_ball hsub)
    (i12HS_diff_ball w _) w (mem_ball_self (half_pos hr))
  exact hd.differentiableAt.differentiableWithinAt

/-- **The Taylor coefficients of the good part at `ε = 0`**: for every `n`, the pointwise
derivatives `Good_n` are integrable over the region and
`(∫ Good)⁽ⁿ⁾(0) = ∫ (Good_n(h(x)) - Good_n(h(0)))`. -/
theorem iteratedDeriv_i12HSGoodI (n : ℕ) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ =>
        ((i12HSGoodHDn n z.1 z.2.1 z.2.2 (i12H z.1) : ℝ) : ℂ) -
          i12HSGoodHDn n z.1 z.2.1 z.2.2 (i12H 0))
        (Ioo 0 1 ×ˢ (Ioi 0 ×ˢ Ioo 0 1)) ∧
      iteratedDeriv n i12HSGoodI 0 =
        ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
          (((i12HSGoodHDn n z.1 z.2.1 z.2.2 (i12H z.1) : ℝ) : ℂ) -
            i12HSGoodHDn n z.1 z.2.1 z.2.2 (i12H 0)) := by
  have hsub : ball (0 : ℂ) (1 / 100) ⊆ ball (0 : ℂ) (1 / 100) := le_rfl
  obtain ⟨hI, hE⟩ := i12_iteratedDeriv_integral_center n (z₁ := 0) (by norm_num : (0 : ℝ) < 1 / 100)
    integrableOn_i12HSGoodMaj (fun v _ => (measurable_i12HSGood v).aestronglyMeasurable)
    (i12HS_dom_ball hsub) (i12HS_diff_ball 0 _)
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
      iteratedDeriv n (fun w => i12HSGood w z.1 z.2.1 z.2.2) 0 =
        ((i12HSGoodHDn n z.1 z.2.1 z.2.2 (i12H z.1) : ℝ) : ℂ) -
          i12HSGoodHDn n z.1 z.2.1 z.2.2 (i12H 0) := fun z hz =>
    iteratedDeriv_i12HSGood hz.1.1 (by linarith [hz.1.2]) hz.2.1 hz.2.2 n
  refine ⟨IntegrableOn.congr_fun hI hpt measurableSet_i12HSGoodReg, ?_⟩
  rw [show i12HSGoodI = fun w => ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
    i12HSGood w z.1 z.2.1 z.2.2 from rfl, hE]
  exact setIntegral_congr_fun measurableSet_i12HSGoodReg hpt


/-- The pointwise `n`-th `ε`-coefficient `Good_n` of the good part (scale `h(x)` minus scale
`h(0)`), real-valued. -/
noncomputable def i12HSGoodDn (n : ℕ) (x s u : ℝ) : ℝ :=
  i12HSGoodHDn n x s u (i12H x) - i12HSGoodHDn n x s u (i12H 0)

theorem integrableOn_i12HSGoodDn (n : ℕ) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSGoodDn n z.1 z.2.1 z.2.2)
      (Ioo 0 1 ×ˢ (Ioi 0 ×ˢ Ioo 0 1)) :=
  (iteratedDeriv_i12HSGoodI n).1.re

/-- `(∫ Good)⁽ⁿ⁾(0) = ∫ Good_n` with the real integrand. -/
theorem iteratedDeriv_i12HSGoodI_eq_real (n : ℕ) :
    iteratedDeriv n i12HSGoodI 0 =
      ((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
        i12HSGoodDn n z.1 z.2.1 z.2.2 : ℝ) : ℂ) := by
  rw [(iteratedDeriv_i12HSGoodI n).2, ← integral_complex_ofReal]
  simp only [i12HSGoodDn, ofReal_sub]

theorem i12HSReg_subset : i12HSReg ⊆ Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) := by
  rintro ⟨x, s, u⟩ (⟨hx, hs, hu⟩ | ⟨hs, hx, hu⟩)
  · exact ⟨hx, hs.1, hu⟩
  · have hs1 : (1 : ℝ) < s := hs
    exact ⟨⟨hx.1, hx.2.trans (inv_lt_one_of_one_lt₀ hs1)⟩, zero_lt_one.trans hs1, hu⟩

/-- **The order-`n` split of the bulk part** `∫_{Reg} W_n = ∫ Good_n + rest_n` with
`rest_n = ∫_{Reg} (W_n - Good_n) - ∫_{(0,1) × (0,∞) × (0,1) \ Reg} Good_n`, both pieces of the
rest absolutely convergent. -/
theorem integral_i12HSW_split (n : ℕ) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSW n z.1 z.2.1 z.2.2 - i12HSGoodDn n z.1 z.2.1 z.2.2)
        i12HSReg ∧
      IntegrableOn (fun z : ℝ × ℝ × ℝ => i12HSGoodDn n z.1 z.2.1 z.2.2)
        ((Ioo 0 1 ×ˢ (Ioi 0 ×ˢ Ioo 0 1)) \ i12HSReg) ∧
      ∫ z in i12HSReg, i12HSW n z.1 z.2.1 z.2.2 =
        (∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1), i12HSGoodDn n z.1 z.2.1 z.2.2) +
          ((∫ z in i12HSReg, (i12HSW n z.1 z.2.1 z.2.2 - i12HSGoodDn n z.1 z.2.1 z.2.2)) -
            ∫ z in (Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1)) \ i12HSReg,
              i12HSGoodDn n z.1 z.2.1 z.2.2) := by
  have hG := integrableOn_i12HSGoodDn n
  have hW := (integral_i12RA3Dn_add_i12RB3Dn n).1
  have hGR := hG.mono_set i12HSReg_subset
  have hReg : MeasurableSet i12HSReg :=
    (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)).union
      measurableSet_i12HSDom
  refine ⟨hW.sub hGR, hG.mono_set sdiff_subset, ?_⟩
  rw [integral_sub hW hGR, setIntegral_sdiff hReg hG i12HSReg_subset]
  ring

end QED.ThreeLoopD
