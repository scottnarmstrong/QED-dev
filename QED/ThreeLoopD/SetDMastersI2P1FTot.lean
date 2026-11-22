/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1FFin
public import QED.ThreeLoopD.SetDMastersI2P1Red

/-!
# Set (d), master `I₂`: the `ℱ`-part of `P'(0)` and the first `ε`-coefficient

From `V + R(h) = R(g)` (`QED.ThreeLoopD.i2P1FAsm_main`), where `V` is the lower integral of
`(1 - w) log (ℱ / 𝒰) / 𝒰² ≥ 0` over the domain of `I₂` and
`R(f) = ∫₀¹ ds 8 (1 + s²) / (s (1 - s²)) log² s ∫₀¹ dz 2 z f(r(s, z)²)`, we conclude:

* `R(h) < ∞`, since `h(r²) ≤ max(w(r), 0) + 2 · 1[z < s]`, the positive part of `w` is
  controlled by `∫₀¹ 2 z w(r(s, z)) dz = I(s²)` and the negative part by `s²`
  (`QED.ThreeLoopD.i2P1FFin_inner`), and `s ↦ 8 (1 + s²) / (s (1 - s²)) log² s · I(s²)` is
  integrable; and `g(r²) ≤ 2 h(r²)`, so both weights are integrable on the square;
* `V = R(g) - R(h) = ∫₀¹ ds 8 (1 + s²) / (s (1 - s²)) log² s ∫₀¹ dz 2 z w(r(s, z))` (Fubini,
  `g(r²) - h(r²) = w(r)`), which is `2 π⁴ / 45 - 4 ζ(3) + π² / 3` by
  `QED.ThreeLoopD.i2P1FZ_value`.

## Main results

* `QED.ThreeLoopD.i2P1F_integral`: `∫ (1 - w) log (ℱ / 𝒰) / 𝒰² = 2 π⁴ / 45 - 4 ζ(3) + π² / 3`.
* `QED.ThreeLoopD.iteratedDeriv_i2PInt_one`: `P'(0) = i2P1`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Function
open scoped ENNReal

namespace QED.ThreeLoopD

/-- The weight `8 (1 + s²) / (s (1 - s²)) log² s`. -/
noncomputable def i2P1FTwt (s : ℝ) : ℝ := 8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2

theorem i2P1FT_wt_nonneg {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : 0 ≤ i2P1FTwt s := by
  have := hs.1
  have : 0 < 1 - s ^ 2 := by nlinarith [hs.2]
  unfold i2P1FTwt
  positivity

theorem i2P1FT_meas {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun p : ℝ × ℝ => i2P1FTwt p.1 * (2 * p.2 * f (i2P1Fr p.1 p.2 ^ 2)) := by
  have hw : Measurable fun p : ℝ × ℝ => i2P1FTwt p.1 := by unfold i2P1FTwt; fun_prop
  have hr : Measurable fun p : ℝ × ℝ => i2P1Fr p.1 p.2 ^ 2 := by unfold i2P1Fr; fun_prop
  exact hw.mul ((by fun_prop : Measurable fun p : ℝ × ℝ => 2 * p.2).mul (hf.comp hr))

/-- The iterated lower integral over the square as a lower integral for the product measure. -/
theorem i2P1FT_sq {f : ℝ → ℝ} (hf : Measurable f) :
    ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2) *
        ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) *
          ENNReal.ofReal (f (((1 - s ^ 2) * z / (s * (1 - z ^ 2))) ^ 2)) =
      ∫⁻ p, ENNReal.ofReal (i2P1FTwt p.1 * (2 * p.2 * f (i2P1Fr p.1 p.2 ^ 2)))
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (i2P1FTwt p.1 *
    (2 * p.2 * f (i2P1Fr p.1 p.2 ^ 2))))
    (ENNReal.measurable_ofReal.comp (i2P1FT_meas hf)).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
  have := hz.1
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2
    from i2P1FT_wt_nonneg hs)]
  rfl

theorem i2P1FT_nonneg {z : ℝ × ℝ × ℝ × ℝ × ℝ} (hz : z ∈ i2Dom) :
    0 ≤ (1 - z.2.1) * Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hw0, hw1⟩, (h4 : 0 < z.2.2.1), (h7 : 0 < z.2.2.2.1),
    (h8 : 0 < z.2.2.2.2)⟩ := hz
  have ha : 0 < i2LineA z.1 z.2.1 z.2.2.2.1 := by
    unfold i2LineA; have : 0 < 1 - z.2.1 := by linarith
    positivity
  have hb : 0 < i2LineB z.1 z.2.1 z.2.2.2.2 := by
    unfold i2LineB; have : 0 < 1 - z.2.1 := by linarith
    have : 0 < 1 - z.1 := by linarith
    positivity
  have hc : 0 < i2LineC z.1 z.2.1 z.2.2.1 := by
    unfold i2LineC; have : 0 < 1 - z.1 := by linarith
    positivity
  have hU : 0 < i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 := by unfold i2U; positivity
  have hF : i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ≤
      i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 := by
    unfold i2F
    have : 0 ≤ z.2.2.1 ^ 2 * (i2LineA z.1 z.2.1 z.2.2.2.1 + i2LineB z.1 z.2.1 z.2.2.2.2) := by
      positivity
    linarith
  have hl : 0 ≤ Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := log_nonneg ((one_le_div hU).2 hF)
  have : 0 ≤ 1 - z.2.1 := by linarith
  positivity

/-- **The `ℱ`-part of `P'(0)`**: `∫ (1 - w) log (ℱ / 𝒰) / 𝒰² = 2 π⁴ / 45 - 4 ζ(3) + π² / 3`. -/
theorem i2P1F_integral :
    ∫ z in i2Dom, (1 - z.2.1) * Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 =
      2 * Real.pi ^ 4 / 45 - 4 * QED.Polylog.zeta3 + Real.pi ^ 2 / 3 := by
  set μ := (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)) with hμ
  set φh : ℝ × ℝ → ℝ := fun p => i2P1FTwt p.1 * (2 * p.2 * i2P1Fhr (i2P1Fr p.1 p.2 ^ 2))
    with hφh
  set φg : ℝ × ℝ → ℝ := fun p => i2P1FTwt p.1 * (2 * p.2 * i2P1Fgr (i2P1Fr p.1 p.2 ^ 2))
    with hφg
  have hsq : ∀ᵐ p ∂μ, p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
    rw [hμ, Measure.prod_restrict]
    exact (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2
      (Eventually.of_forall fun p hp => hp)
  have mh : Measurable φh := i2P1FT_meas measurable_i2P1Fhr
  have mg : Measurable φg := i2P1FT_meas measurable_i2P1Fgr
  have hh0 : ∀ᵐ p ∂μ, 0 ≤ φh p := hsq.mono fun p ⟨hs, hz⟩ =>
    mul_nonneg (i2P1FT_wt_nonneg hs) (mul_nonneg (by linarith [hz.1])
      (i2P1FFin_h_nonneg (i2P1FFin_r_pos hs hz).le))
  have hgh : ∀ᵐ p ∂μ, 0 ≤ φg p ∧ φg p ≤ 2 * φh p := hsq.mono fun p ⟨hs, hz⟩ => by
    have hr := (i2P1FFin_r_pos hs hz).le
    have e := i2P1FFin_diff hr
    have h1 := i2P1FFin_w_le_h hr
    have hw := i2P1FT_wt_nonneg hs
    have hz0 : 0 ≤ 2 * p.2 := by linarith [hz.1]
    have hg0 := i2P1Fgr_nonneg (sq_nonneg (i2P1Fr p.1 p.2))
    refine ⟨mul_nonneg hw (mul_nonneg hz0 hg0), ?_⟩
    have : i2P1Fgr (i2P1Fr p.1 p.2 ^ 2) ≤ 2 * i2P1Fhr (i2P1Fr p.1 p.2 ^ 2) := by linarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hw hz0)
    simp only [hφg, hφh]
    nlinarith
  have hRh : ∫⁻ p, ENNReal.ofReal (φh p) ∂μ < ⊤ := by
    rw [hμ, hφh, ← i2P1FT_sq measurable_i2P1Fhr]
    have hI := i2P1FFin_integrable.abs
    calc ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2) *
          ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) *
            ENNReal.ofReal (i2P1Fhr (((1 - s ^ 2) * z / (s * (1 - z ^ 2))) ^ 2))
        ≤ ∫⁻ s in Ioo (0 : ℝ) 1, (ENNReal.ofReal
            |8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2 * i2P1FI (s ^ 2)| +
              ENNReal.ofReal 192) := by
          refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
          have hw : 0 ≤ 8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2 := i2P1FT_wt_nonneg hs
          refine (mul_le_mul_of_nonneg_left (i2P1FFin_inner hs) zero_le).trans ?_
          rw [← ENNReal.ofReal_mul hw]
          refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
          rw [abs_mul, abs_of_nonneg hw]
          have := i2P1FFin_wt_sq hs
          nlinarith
      _ = (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal
            |8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2 * i2P1FI (s ^ 2)|) +
              ENNReal.ofReal 192 * volume (Ioo (0 : ℝ) 1) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hI.lintegral_lt_top, ENNReal.mul_lt_top
          ENNReal.ofReal_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)⟩
  have hih : Integrable φh μ := ⟨mh.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hh0).2 hRh⟩
  have hig : Integrable φg μ := (hih.const_mul 2).mono' mg.aestronglyMeasurable
    (hgh.mono fun p h => by rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2)
  have hRg := hig.lintegral_lt_top
  have hA := i2P1FAsm_main
  rw [i2P1FT_sq measurable_i2P1Fhr, i2P1FT_sq measurable_i2P1Fgr] at hA
  have hV : ∫⁻ z in i2Dom, ENNReal.ofReal ((1 - z.2.1) *
      log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top hRg.ne (hA ▸ le_self_add)
  have hT := congrArg ENNReal.toReal hA
  rw [ENNReal.toReal_add hV hRh.ne] at hT
  have hmΦ : Measurable fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) *
      log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 := by
    unfold i2F i2U i2LineA i2LineB i2LineC; fun_prop
  have hdom : MeasurableSet i2Dom :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioi.prod
      (measurableSet_Ioi.prod measurableSet_Ioi)))
  rw [integral_eq_lintegral_of_nonneg_ae ((ae_restrict_iff' hdom).2
    (Eventually.of_forall fun z hz => i2P1FT_nonneg hz)) hmΦ.aestronglyMeasurable]
  rw [← integral_eq_lintegral_of_nonneg_ae hh0 mh.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (hgh.mono fun p h => h.1) mg.aestronglyMeasurable]
    at hT
  rw [show (∫⁻ z in i2Dom, ENNReal.ofReal ((1 - z.2.1) *
      log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2)).toReal = ∫ p, φg p ∂μ - ∫ p, φh p ∂μ
    by linarith, ← integral_sub hig hih, hμ, integral_prod (fun p => φg p - φh p) (hig.sub hih),
    ← i2P1FZ_value]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
  simp only [hφg, hφh, i2P1FTwt]
  rw [← i2P1FFin_diff (i2P1FFin_r_pos hs hz).le]
  ring

/-- **`P'(0) = i2P1`**: the first `ε`-coefficient of the master `I₂`. -/
theorem iteratedDeriv_i2PInt_one : iteratedDeriv 1 i2PInt 0 = i2P1 :=
  iteratedDeriv_i2PInt_one_of_F i2P1F_integral

end QED.ThreeLoopD
