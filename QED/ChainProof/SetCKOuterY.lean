/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKInnerX
public import QED.TwoLoop.UnitXXiLimits
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Set (c), Stage K: the outer placement, `Y`-integration in closed form

Helper level (no frozen statement). In the outer placement of the ladder (massive photon outside
the vertex subgraph, massless photon inside), the inner mass is `M = Y²` and the outer photon
enters only through `h = (x² + (1-x) t)/x`. For fixed `x ∈ (0, 1)` and `h > 0`, `h ≠ 1`, the
`Y`-integral of the integrand (3.4) is

`∫₀¹ G(Y, x; M = Y², h) dY = Φ_out(x, h) = R_l log h + R_Li (Li₂(1 - 1/h) - π²/6) + R₀`

(`integral_outerG`, `phiOut`), with `Li₂(1 - 1/h)` the real dilogarithm `dilogI` (the argument
lies in `(-∞, 1)`). The antiderivative `outerF` is written so that its endpoint limits are
transparent: the infrared-singular terms at `Y = 0` appear only through the slopes
`(log(h + (1-h)Y) - log h)/Y → (1-h)/h` and `log(1-Y)/Y → -1`. The integrability of
`G(·, x; Y², h)` is a hypothesis here.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology MeasureTheory QED.Polylog QED.TwoLoop.UnitLLink
  QED.TwoLoop.UnitXClose QED.TwoLoop.UnitXXi

/-- The numerator `q` of `gForm` in the outer placement. -/
noncomputable def outerQ (x Y : ℝ) : ℝ :=
  x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) - 2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2)

/-- The outer-placement integrand `G(Y, x; M = Y², h)` of (3.4). -/
noncomputable def outerG (x h Y : ℝ) : ℝ :=
  gForm (Y * x * (1 - x) / 2) (Y * (1 - Y)) (outerQ x Y) h (Y ^ 2)
    (log (Y ^ 2 + Y * (1 - Y) * h)) (log (1 + Y ^ 2 / (Y * (1 - Y) * h)))

theorem ladderGm_zero_eq_outerG (la Y x : ℝ) :
    ladderGm la 0 Y x = outerG x (ladderInnerMass 1 la x / x) Y := by
  rw [ladderGm_eq_form]
  simp only [outerG, outerQ, ladderInnerMass]
  norm_num

/-- The coefficient of the dilogarithm. -/
noncomputable def outerKD (x h : ℝ) : ℝ := (x - 1) * (9 * h * x + 3 * x ^ 2 - 10 * x + 2) / 2

/-- The coefficient polynomial of `log(h + (1-h)Y)`. -/
noncomputable def outerPA (x h : ℝ) : ℝ → ℝ :=
  poly4
    (-(x - 1) * (27 * h ^ 4 * x + 9 * h ^ 3 * x ^ 2 - 61 * h ^ 3 * x + 6 * h ^ 3 -
      12 * h ^ 2 * x ^ 2 + 31 * h ^ 2 * x - 8 * h ^ 2 + 12 * h * x - 4 * x) / (4 * h * (h - 1) ^ 2))
    ((x - 1) * (18 * h * x + 6 * x ^ 2 - 21 * x + 4) / 2)
    (-(x - 1) * (9 * h ^ 2 * x + 3 * h * x ^ 2 - 13 * h * x + 2 * h - x) / (4 * h)) 0 0

/-- The coefficient polynomial of `log h`. -/
noncomputable def outerPH (x h : ℝ) : ℝ → ℝ :=
  poly4 0 (-(x - 1) * (18 * h * x + 6 * x ^ 2 - 21 * x + 4) / 2)
    ((x - 1) * (9 * h * x + 3 * x ^ 2 - 13 * x + 2) / 4) 0 0

/-- The coefficient polynomial of `(Y - 1) log(1 - Y)`. -/
noncomputable def outerP1 (x h : ℝ) : ℝ → ℝ :=
  poly4 (-(x - 1) * (27 * h * x + 9 * x ^ 2 - 29 * x + 6) / 4)
    ((x - 1) * (9 * h * x + 3 * x ^ 2 - 13 * x + 2) / 4) 0 0 0

/-- The rational part. -/
noncomputable def outerP0 (x h : ℝ) : ℝ → ℝ :=
  poly4 0
    ((x - 1) * (27 * h ^ 2 * x + 9 * h * x ^ 2 - 48 * h * x + 6 * h - 6 * x ^ 2 + 16 * x - 4) /
      (4 * h * (h - 1)))
    (-(x - 1) * (9 * h * x + 3 * x ^ 2 - 4 * x + 2) / (4 * h)) 0 0

/-- **The antiderivative in `Y`** of `outerG x h`. -/
noncomputable def outerF (x h Y : ℝ) : ℝ :=
  x * (x - 1) * ((log (h + (1 - h) * Y) - log h) / Y) +
    x * (x - 1) * ((Y - 1) * (log (1 - Y) / Y)) +
    outerPA x h Y * log (h + (1 - h) * Y) + outerPH x h Y * log h +
    x * (x - 1) / (4 * h) * (Y * (Y * log Y)) +
    outerP1 x h Y * ((Y - 1) * log (1 - Y)) +
    outerKD x h * (dilogI (-(1 - h) * Y / h) - Li₂ Y) + outerP0 x h Y

/-- **The `Y`-integral of the outer placement**:
`Φ_out = R_l log h + R_Li (Li₂(1 - 1/h) - π²/6) + R₀`. -/
noncomputable def phiOut (x h : ℝ) : ℝ :=
  (x - 1) * (18 * h ^ 3 * x + 6 * h ^ 2 * x ^ 2 - 46 * h ^ 2 * x + 4 * h ^ 2 - 9 * h * x ^ 2 +
      37 * h * x - 6 * h - 4 * x) / (4 * h * (h - 1) ^ 2) * log h +
    outerKD x h * (dilogI (1 - 1 / h) - π ^ 2 / 6) -
    (x - 1) * (-54 * h ^ 2 * x - 18 * h * x ^ 2 + 117 * h * x - 12 * h + 9 * x ^ 2 - 48 * x + 6) /
      (12 * h * (h - 1))

section

variable {x h Y : ℝ}

theorem outer_mass_pos (hh : 0 < h) (hY : Y ∈ Icc (0 : ℝ) 1) : 0 < h + (1 - h) * Y := by
  have e : h + (1 - h) * Y = h * (1 - Y) + Y := by ring
  rw [e]
  rcases eq_or_lt_of_le hY.2 with h1 | h1
  · subst h1
    norm_num
  · have : 0 < h * (1 - Y) := mul_pos hh (by linarith)
    linarith [hY.1]

theorem outer_dilog_arg_lt (hh : 0 < h) (hY : Y ∈ Icc (0 : ℝ) 1) : -(1 - h) * Y / h < 1 := by
  rw [div_lt_one hh]
  rcases le_or_gt h 1 with h1 | h1
  · nlinarith [hY.1]
  · nlinarith [hY.2]

/-- The two logarithms of `gForm` at `M = Y²`. -/
theorem outer_logs (hh : 0 < h) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    log (Y ^ 2 + Y * (1 - Y) * h) = log Y + log (h + (1 - h) * Y) ∧
      log (1 + Y ^ 2 / (Y * (1 - Y) * h)) =
        log (h + (1 - h) * Y) - log (1 - Y) - log h := by
  have hY0 := hY.1
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hA := outer_mass_pos hh (Ioo_subset_Icc_self hY)
  constructor
  · rw [← log_mul hY0.ne' hA.ne']
    congr 1
    ring
  · have e : 1 + Y ^ 2 / (Y * (1 - Y) * h) = (h + (1 - h) * Y) / ((1 - Y) * h) := by
      field_simp
      ring
    rw [e, log_div hA.ne' (by positivity), log_mul hY1.ne' hh.ne']
    ring

theorem hasDerivAt_outerF (hx0 : x ≠ 0) (hh : 0 < h) (hh1 : h ≠ 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (outerF x h) (outerG x h Y) Y := by
  have hY0 := hY.1
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hA := outer_mass_pos hh (Ioo_subset_Icc_self hY)
  have ha : 1 - h ≠ 0 := sub_ne_zero.2 (Ne.symm hh1)
  have dLA : HasDerivAt (fun y => log (h + (1 - h) * y)) ((1 - h) / (h + (1 - h) * Y)) Y := by
    have := (((hasDerivAt_id' Y).const_mul (1 - h)).const_add h).log hA.ne'
    simpa using this
  have dl1 : HasDerivAt (fun y => log (1 - y)) (-1 / (1 - Y)) Y := by
    have := ((hasDerivAt_id' Y).const_sub (1 : ℝ)).log hY1.ne'
    simpa using this
  have dlY : HasDerivAt log Y⁻¹ Y := hasDerivAt_log hY0.ne'
  have dS1 := (dLA.sub_const (log h)).div (hasDerivAt_id' Y) hY0.ne'
  have dS2 := ((hasDerivAt_id' Y).sub_const (1 : ℝ)).mul (dl1.div (hasDerivAt_id' Y) hY0.ne')
  have dYY := (hasDerivAt_id' Y).mul ((hasDerivAt_id' Y).mul dlY)
  have dY1 := ((hasDerivAt_id' Y).sub_const (1 : ℝ)).mul dl1
  have hf : HasDerivAt (fun y : ℝ => -(1 - h) * y / h) (-(1 - h) / h) Y := by
    simpa using ((hasDerivAt_id' Y).const_mul (-(1 - h))).div_const h
  have hf0 : -(1 - h) * Y / h ≠ 0 := by
    have : -(1 - h) * Y ≠ 0 := mul_ne_zero (neg_ne_zero.2 ha) hY0.ne'
    exact div_ne_zero this hh.ne'
  have dD := hasDerivAt_dilogI_comp hf (outer_dilog_arg_lt hh (Ioo_subset_Icc_self hY)) hf0
  have hYabs : |Y| < 1 := by rw [abs_of_pos hY0]; exact hY.2
  have dL := hasDerivAt_Li₂ hYabs hY0.ne'
  have dPA : HasDerivAt (outerPA x h) _ Y := hasDerivAt_poly4 _ _ _ _ _ Y
  have dPH : HasDerivAt (outerPH x h) _ Y := hasDerivAt_poly4 _ _ _ _ _ Y
  have dP1 : HasDerivAt (outerP1 x h) _ Y := hasDerivAt_poly4 _ _ _ _ _ Y
  have dP0 : HasDerivAt (outerP0 x h) _ Y := hasDerivAt_poly4 _ _ _ _ _ Y
  have H1 := (dS1.const_mul (x * (x - 1))).add (dS2.const_mul (x * (x - 1)))
  have H2 := (H1.add (dPA.mul dLA)).add (dPH.mul_const (log h))
  have H3 := (H2.add (dYY.const_mul (x * (x - 1) / (4 * h)))).add (dP1.mul dY1)
  have H := (H3.add ((dD.sub dL).const_mul (outerKD x h))).add dP0
  convert H using 1
  · funext y
    simp only [outerF, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
  · obtain ⟨e1, e2⟩ := outer_logs hh hY
    have e3 : log (1 - -(1 - h) * Y / h) = log (h + (1 - h) * Y) - log h := by
      rw [← log_div hA.ne' hh.ne']
      congr 1
      field_simp
      ring
    simp only [outerG, gForm, outerQ, outerKD, outerPA, outerP1, poly4, e1, e2, e3, Pi.mul_apply,
      Pi.div_apply]
    have hh0 : h - 1 ≠ 0 := sub_ne_zero.2 hh1
    generalize log (h + (1 - h) * Y) = LA at *
    generalize log (1 - Y) = l1 at *
    generalize log Y = lY at *
    generalize log h = Lh at *
    have hA' := hA.ne'
    have hY1' := hY1.ne'
    have hA'' : h + Y * (1 - h) ≠ 0 := by rw [mul_comm]; exact hA'
    field_simp
    ring

/-- The part of `outerF` that is continuous at both endpoints. -/
noncomputable def outerR (x h Y : ℝ) : ℝ :=
  outerPA x h Y * log (h + (1 - h) * Y) + outerPH x h Y * log h +
    x * (x - 1) / (4 * h) * (Y * (Y * log Y)) -
    outerP1 x h Y * ((1 - Y) * log (1 - Y)) +
    outerKD x h * (dilogI (-(1 - h) * Y / h) - Li₂ Y) + outerP0 x h Y

theorem outerF_eq (x h Y : ℝ) :
    outerF x h Y = x * (x - 1) * ((log (h + (1 - h) * Y) - log h) / Y) +
      x * (x - 1) * ((Y - 1) * (log (1 - Y) / Y)) + outerR x h Y := by
  simp only [outerF, outerR]
  ring

theorem outerF_eq_one (x h Y : ℝ) :
    outerF x h Y = x * (x - 1) * ((log (h + (1 - h) * Y) - log h) / Y) -
      x * (x - 1) * ((1 - Y) * log (1 - Y) / Y) + outerR x h Y := by
  rw [outerF_eq]
  ring

theorem continuousAt_outerR_zero (hh : 0 < h) : ContinuousAt (outerR x h) 0 := by
  have hA0 : (0 : ℝ) < h + (1 - h) * 0 := by simpa using hh
  have hD : ContinuousAt (fun Y : ℝ => dilogI (-(1 - h) * Y / h)) 0 := by
    have hc : ContinuousAt (fun Y : ℝ => -(1 - h) * Y / h) 0 := by fun_prop
    have h0 : -(1 - h) * (0 : ℝ) / h ∈ Iio (1 : ℝ) := by simp
    exact ContinuousAt.comp (f := fun Y : ℝ => -(1 - h) * Y / h) (g := dilogI)
      (continuousOn_dilogI.continuousAt (isOpen_Iio.mem_nhds h0)) hc
  have hL : ContinuousAt Li₂ 0 :=
    continuousOn_Li₂.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have hl1 : ContinuousAt (fun Y : ℝ => log (1 - Y)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  have hlA : ContinuousAt (fun Y : ℝ => log (h + (1 - h) * Y)) 0 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).log hA0.ne'
  have hYl : ContinuousAt (fun Y : ℝ => Y * (Y * log Y)) 0 :=
    continuousAt_id.mul continuous_mul_log.continuousAt
  unfold outerR outerPA outerPH outerP1 outerP0
  have hp := fun a b c d e => (continuous_poly4 a b c d e).continuousAt (x := (0 : ℝ))
  exact (((((hp _ _ _ _ _).mul hlA).add ((hp _ _ _ _ _).mul continuousAt_const)).add
    (continuousAt_const.mul hYl)).sub ((hp _ _ _ _ _).mul
      ((continuousAt_const.sub continuousAt_id).mul hl1))).add
    (continuousAt_const.mul (hD.sub hL)) |>.add (hp _ _ _ _ _)

theorem outerR_zero (x h : ℝ) : outerR x h 0 = outerPA x h 0 * log h := by
  simp [outerR, outerPA, outerPH, outerP1, outerP0, poly4]

theorem tendsto_outerF_zero (hh : 0 < h) :
    Tendsto (outerF x h) (𝓝[>] 0)
      (𝓝 (x * (x - 1) * ((1 - h) / h) + x * (x - 1) * ((0 - 1) * (-1)) +
        outerPA x h 0 * log h)) := by
  have hA0 : (0 : ℝ) < h + (1 - h) * 0 := by simpa using hh
  have dLA : HasDerivAt (fun y => log (h + (1 - h) * y)) ((1 - h) / (h + (1 - h) * 0)) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_mul (1 - h)).const_add h).log hA0.ne'
    simpa using this
  have hS1 : Tendsto (fun Y : ℝ => (log (h + (1 - h) * Y) - log h) / Y) (𝓝[>] 0)
      (𝓝 ((1 - h) / h)) := by
    have := dLA.tendsto_slope_zero_right
    simp only [zero_add, mul_zero, add_zero, smul_eq_mul] at this
    refine this.congr fun Y => ?_
    rw [div_eq_inv_mul]
  have hS2 : Tendsto (fun Y : ℝ => log (1 - Y) / Y) (𝓝[>] 0) (𝓝 (-1)) :=
    tendsto_log_one_sub_div.mono_left (nhdsGT_le_nhdsNE 0)
  have hY1 : Tendsto (fun Y : ℝ => Y - 1) (𝓝[>] 0) (𝓝 (0 - 1)) :=
    ((continuous_id.sub continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  have hR : Tendsto (outerR x h) (𝓝[>] 0) (𝓝 (outerR x h 0)) :=
    (continuousAt_outerR_zero hh).tendsto.mono_left nhdsWithin_le_nhds
  rw [outerR_zero] at hR
  have := ((hS1.const_mul (x * (x - 1))).add ((hY1.mul hS2).const_mul (x * (x - 1)))).add hR
  refine this.congr fun Y => ?_
  rw [outerF_eq]

theorem continuousOn_outerF (hh : 0 < h) : ContinuousOn (outerF x h) (Icc (1 / 2) 1) := by
  have hI : Icc (1 / 2 : ℝ) 1 ⊆ Icc 0 1 := Icc_subset_Icc (by norm_num) le_rfl
  have hY0 : ∀ Y ∈ Icc (1 / 2 : ℝ) 1, Y ≠ 0 := fun Y hY => by linarith [hY.1]
  have hlA : ContinuousOn (fun Y : ℝ => log (h + (1 - h) * Y)) (Icc (1 / 2) 1) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).log
      fun Y hY => (outer_mass_pos hh (hI hY)).ne'
  have hml : ContinuousOn (fun Y : ℝ => (1 - Y) * log (1 - Y)) (Icc (1 / 2) 1) :=
    (continuous_mul_log.comp (continuous_const.sub continuous_id)).continuousOn
  have hYl : ContinuousOn (fun Y : ℝ => Y * (Y * log Y)) (Icc (1 / 2) 1) :=
    (continuous_id.mul continuous_mul_log).continuousOn
  have hD : ContinuousOn (fun Y : ℝ => dilogI (-(1 - h) * Y / h)) (Icc (1 / 2) 1) :=
    continuousOn_dilogI.comp (by fun_prop) fun Y hY => outer_dilog_arg_lt hh (hI hY)
  have hL : ContinuousOn Li₂ (Icc (1 / 2) 1) :=
    continuousOn_Li₂.mono (Icc_subset_Icc (by norm_num) le_rfl)
  have hp := fun a b c d e => (continuous_poly4 a b c d e).continuousOn (s := Icc (1 / 2 : ℝ) 1)
  have hR : ContinuousOn (outerR x h) (Icc (1 / 2) 1) := by
    unfold outerR outerPA outerPH outerP1 outerP0
    exact (((((hp _ _ _ _ _).mul hlA).add ((hp _ _ _ _ _).mul continuousOn_const)).add
      (continuousOn_const.mul hYl)).sub ((hp _ _ _ _ _).mul hml)).add
      (continuousOn_const.mul (hD.sub hL)) |>.add (hp _ _ _ _ _)
  have e : outerF x h = fun Y => x * (x - 1) * ((log (h + (1 - h) * Y) - log h) / Y) -
      x * (x - 1) * ((1 - Y) * log (1 - Y) / Y) + outerR x h Y := funext (outerF_eq_one x h)
  rw [e]
  exact ((continuousOn_const.mul ((hlA.sub continuousOn_const).div continuousOn_id hY0)).sub
    (continuousOn_const.mul (hml.div continuousOn_id hY0))).add hR

theorem tendsto_outerF_one (hh : 0 < h) :
    Tendsto (outerF x h) (𝓝[<] 1) (𝓝 (outerF x h 1)) := by
  have hc := ((continuousOn_outerF (x := x) hh) 1 ⟨by norm_num, le_rfl⟩).tendsto
  rw [← nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)]
  exact hc.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)

/-- `outerF` at `Y = 1`. -/
theorem outerF_one (hh : 0 < h) :
    outerF x h 1 = -(x * (x - 1)) * log h + outerPH x h 1 * log h +
      outerKD x h * (dilogI (1 - 1 / h) - π ^ 2 / 6) + outerP0 x h 1 := by
  have e : -(1 - h) * 1 / h = 1 - 1 / h := by field_simp; ring
  have e2 : h + (1 - h) * 1 = 1 := by ring
  rw [outerF_eq_one]
  unfold outerR
  rw [e, e2, Li₂_one]
  simp only [sub_self, zero_mul, mul_zero, sub_zero, div_one, log_one, add_zero]
  ring

/-- **The outer `Y`-integration**: `∫₀¹ G(Y, x; Y², h) dY = Φ_out(x, h)`, given integrability. -/
theorem integral_outerG (hx0 : x ≠ 0) (hh : 0 < h) (hh1 : h ≠ 1)
    (hint : IntervalIntegrable (outerG x h) volume 0 1) :
    ∫ Y in (0 : ℝ)..1, outerG x h Y = phiOut x h := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun Y hY => hasDerivAt_outerF hx0 hh hh1 hY) hint (tendsto_outerF_zero hh)
    (tendsto_outerF_one hh), outerF_one hh]
  have hh0 : h - 1 ≠ 0 := sub_ne_zero.2 hh1
  simp only [phiOut, outerPA, outerPH, outerP0, outerKD, poly4]
  field_simp
  ring

end

end QED.ChainProof.SetCK
