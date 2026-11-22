/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondPt
public import QED.ThreeLoopD.SetDMastersI12RSecondG
public import QED.ThreeLoopD.SetDMastersI12RSecondTri
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₂`: reduction of `R_B'(0)` to the `(ρ, θ)` square

By `QED.ThreeLoopD.hasDerivAt_i12RB3_zero`, `R_B'(0)` is the integral over `(ρ, θ, u) ∈ (0, 1)³`
of an explicit real function (`QED.ThreeLoopD.i12RBf`). With `h = h(ρθ)`, `h₀ = h(0)`,
`d = 1/h - 1/h₀` and `g` evaluated at `θ h (1 - u) / u` resp. `θ h₀ (1 - u) / u`, it is affine in
`g(…)`, `log u`, `log (1 - u)`.

**`u` first.** With `G = QED.ThreeLoopD.i12RG` (and `u ↦ 1 - u` in its argument),
`∫₀¹ log u = ∫₀¹ log (1 - u) = -1`, the `u`-integral is

  `F(ρ, θ) = ((log ρ + 2 log θ) 2d + G(θh)/h - G(θh₀)/h₀ + (-2 log (1 - ρ) - 1) d
      + 4 (log h / h - log h₀ / h₀)) / (ρθ)`   (`QED.ThreeLoopD.i12RBF`).

**The square.** `F = E₁(ρ, θ) + Φ₂(ρθ) + Ψ₃(ρθ, θ)`, with `E₁` elementary
(`QED.ThreeLoopD.i12RBE1`), `Φ₂(x) = 16 log (1 - x/2) / (x (2 - x)) - 8 log 2 / (2 - x)`
(`QED.ThreeLoopD.i12RBPhi2`) and `Ψ₃(x, θ) = (G(θ h(x))/h(x) - G(θ h₀)/h₀) / x`
(`QED.ThreeLoopD.i12RBPsi3`). The `θ`-integral of `E₁` uses `∫₀¹ dθ / (2 - ρθ)` and
`∫₀¹ log θ dθ / (2 - ρθ) = -Li₂ (ρ/2) / ρ`; the other two pieces are integrated over the
triangle `0 < x < θ < 1` (`QED.ThreeLoopD.i12_integral_tri`), with `∫ₓ¹ dθ/θ = -log x` and
`∫ₓ¹ G(θ q) / θ dθ = K(q) - K(x q)` (`QED.ThreeLoopD.integral_i12RG_div`). Hence

  `R_B'(0) = B₁ + B₂ + B₃`,
  `B₁ = ∫₀¹ (-4 log ρ log (1 - ρ/2) - 8 Li₂ (ρ/2) + 2 (2 log (1 - ρ) + 1) log (1 - ρ/2)) / ρ`,
  `B₂ = ∫₀¹ -log x (16 log (1 - x/2) / (x (2 - x)) - 8 log 2 / (2 - x))`,
  `B₃ = ∫₀¹ (4/(2 - x) (K((2 - x)/4) - K(x(2 - x)/4)) - 2 (K(1/2) - K(x/2))) / x`.

## Main results

* `QED.ThreeLoopD.integral_i12RBf_u`, `QED.ThreeLoopD.deriv_i12RB3_zero_eq_square`.
* `QED.ThreeLoopD.deriv_i12RB3_zero_eq`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The real integrand of `R_B'(0)`. -/
noncomputable def i12RBf (z : ℝ × ℝ × ℝ) : ℝ :=
  ((Real.log z.1 + 2 * Real.log z.2.1) * (2 / i12H (z.1 * z.2.1) - 2 / i12H 0) +
    (i12RBd z.1 z.2.1 z.2.2 - i12RBd 0 z.2.1 z.2.2)) / (z.1 * z.2.1)

/-- The `u`-integral of the integrand of `R_B'(0)`. -/
noncomputable def i12RBF (ρ θ : ℝ) : ℝ :=
  ((Real.log ρ + 2 * Real.log θ) * (2 * (1 / i12H (ρ * θ) - 1 / i12H 0)) +
    i12RG (θ * i12H (ρ * θ)) / i12H (ρ * θ) - i12RG (θ * i12H 0) / i12H 0 +
    (-2 * Real.log (1 - ρ) - 1) * (1 / i12H (ρ * θ) - 1 / i12H 0) +
    4 * (Real.log (i12H (ρ * θ)) / i12H (ρ * θ) - Real.log (i12H 0) / i12H 0)) / (ρ * θ)

theorem integrableOn_log_Ioo : IntegrableOn Real.log (Ioo (0 : ℝ) 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
    intervalIntegral.intervalIntegrable_log'

theorem integral_log_Ioo : ∫ u in Ioo (0 : ℝ) 1, Real.log u = -1 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_log]
  simp

theorem integral_log_one_sub_Ioo : ∫ u in Ioo (0 : ℝ) 1, Real.log (1 - u) = -1 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left (fun u => Real.log u) 1, integral_log]
  simp

/-- **The `u`-integral** of the integrand of `R_B'(0)`. -/
theorem integral_i12RBf_u {ρ θ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ∫ u in Ioo (0 : ℝ) 1, i12RBf (ρ, θ, u) = i12RBF ρ θ := by
  have hx : 0 < ρ * θ := mul_pos hρ.1 hθ.1
  have hx1 : ρ * θ < 1 := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
  have hH : 0 < i12H (ρ * θ) := i12H_pos (by linarith)
  have hH0 : 0 < i12H 0 := i12H_pos (by norm_num)
  set h := i12H (ρ * θ) with hhd
  set h0 := i12H 0 with hh0d
  set D := ρ * θ with hDd
  set d := 1 / h - 1 / h0 with hdd
  set A0 := ((Real.log ρ + 2 * Real.log θ) * (2 * d) - 2 * Real.log (1 - ρ) * d +
    4 * (Real.log h / h - Real.log h0 / h0) - 3 * d) / D
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1, i12RBf (ρ, θ, u) =
      A0 + (1 / (h * D)) * i12Rg (θ * h * (1 - u) / u) +
        (-1 / (h0 * D)) * i12Rg (θ * h0 * (1 - u) / u) + (-4 * d / D) * Real.log u +
        (2 * d / D) * Real.log (1 - u) := by
    intro u hu
    have hP : Real.log (u * (1 - u)) = Real.log u + Real.log (1 - u) :=
      Real.log_mul hu.1.ne' (by linarith [hu.2])
    have e1 : (1 - u) * θ * h / u = θ * h * (1 - u) / u := by ring
    have e0 : (1 - u) * θ * h0 / u = θ * h0 * (1 - u) / u := by ring
    simp only [i12RBf, i12RBd, hP, zero_mul, sub_zero, Real.log_one, neg_zero, zero_add,
      sub_self, mul_zero, add_zero]
    rw [← hhd, ← hh0d, ← hDd, e1, e0]
    generalize i12Rg (θ * h * (1 - u) / u) = g1
    generalize i12Rg (θ * h0 * (1 - u) / u) = g0
    simp only [A0, d]
    field_simp
    ring
  have hG1 := integrableOn_i12RG_flip (mul_pos hθ.1 hH)
  have hG0 := integrableOn_i12RG_flip (mul_pos hθ.1 hH0)
  have hc : IntegrableOn (fun _ : ℝ => A0) (Ioo (0 : ℝ) 1) := integrableOn_const (by simp)
  have i1 : IntegrableOn (fun u => A0 + 1 / (h * D) * i12Rg (θ * h * (1 - u) / u))
      (Ioo (0 : ℝ) 1) := hc.add (hG1.const_mul _)
  have i2 : IntegrableOn (fun u => A0 + 1 / (h * D) * i12Rg (θ * h * (1 - u) / u) +
      -1 / (h0 * D) * i12Rg (θ * h0 * (1 - u) / u)) (Ioo (0 : ℝ) 1) := i1.add (hG0.const_mul _)
  have i3 : IntegrableOn (fun u => A0 + 1 / (h * D) * i12Rg (θ * h * (1 - u) / u) +
      -1 / (h0 * D) * i12Rg (θ * h0 * (1 - u) / u) + -4 * d / D * Real.log u)
      (Ioo (0 : ℝ) 1) := i2.add (integrableOn_log_Ioo.const_mul _)
  have i4 : IntegrableOn (fun u => 2 * d / D * Real.log (1 - u)) (Ioo (0 : ℝ) 1) :=
    integrableOn_log_one_sub.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_add i3 i4,
    integral_add i2 (integrableOn_log_Ioo.const_mul _), integral_add i1 (hG0.const_mul _),
    integral_add hc (hG1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_i12RG_flip, integral_i12RG_flip, integral_log_Ioo, integral_log_one_sub_Ioo,
    integral_const]
  have hm : max (1 - 0 : ℝ) 0 = 1 := by norm_num
  simp only [A0, d, i12RBF, measureReal_restrict_apply_univ, Real.volume_real_Ioo, hm,
    smul_eq_mul, one_mul]
  rw [← hDd, ← hhd, ← hh0d]
  field_simp
  ring

/-- The `u`-integral as an integral over the square: `R_B'(0) = ∫_{(0,1)²} F`. -/
theorem deriv_i12RB3_zero_eq_square :
    IntegrableOn (fun q : ℝ × ℝ => i12RBF q.1 q.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∧
      deriv i12RB3 0 = ((∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i12RBF q.1 q.2 : ℝ) : ℂ) := by
  obtain ⟨hi, hd⟩ := hasDerivAt_i12RB3_zero
  have hiR : Integrable i12RBf
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
    hi.re.congr (ae_of_all _ fun z => Complex.ofReal_re _)
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hμ : volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = μ.prod μ := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [volume_restrict_prod3] at hiR
  have hmp := measurePreserving_prodAssoc μ μ μ
  have hiA : Integrable (i12RBf ∘ MeasurableEquiv.prodAssoc) ((μ.prod μ).prod μ) :=
    (hmp.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).2 hiR
  have hae : ∀ᵐ q ∂(μ.prod μ), ∫ u, (i12RBf ∘ MeasurableEquiv.prodAssoc) (q, u) ∂μ =
      i12RBF q.1 q.2 := by
    rw [← hμ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    exact integral_i12RBf_u hq.1 hq.2
  have hF : Integrable (fun q : ℝ × ℝ => i12RBF q.1 q.2) (μ.prod μ) :=
    hiA.integral_prod_left.congr hae
  refine ⟨by rw [IntegrableOn, hμ]; exact hF, ?_⟩
  rw [hd.deriv, integral_complex_ofReal]
  congr 1
  change ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i12RBf z = _
  rw [volume_restrict_prod3]
  change ∫ z, i12RBf z ∂(μ.prod (μ.prod μ)) = _
  rw [← hmp.integral_comp' i12RBf, hμ]
  exact (integral_prod _ hiA).trans (integral_congr_ae hae)

/-- The elementary part of `F` without the `x = ρθ` pieces. -/
noncomputable def i12RBE1 (ρ θ : ℝ) : ℝ :=
  (2 * (Real.log ρ + 2 * Real.log θ) - 2 * Real.log (1 - ρ) - 1) * (2 / (2 - ρ * θ))

/-- The elementary part of `F` depending on `x = ρθ` only. -/
noncomputable def i12RBPhi2 (x : ℝ) : ℝ :=
  4 * (Real.log (i12H x) / i12H x - Real.log (i12H 0) / i12H 0) / x

/-- The `G` part of `F`, in the variables `x = ρθ` and `θ`. -/
noncomputable def i12RBPsi3 (x θ : ℝ) : ℝ :=
  (i12RG (θ * i12H x) / i12H x - i12RG (θ * i12H 0) / i12H 0) / x

theorem i12RBF_eq {ρ θ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    i12RBF ρ θ = i12RBE1 ρ θ + i12RBPhi2 (ρ * θ) + i12RBPsi3 (ρ * θ) θ := by
  have hx : 0 < ρ * θ := mul_pos hρ.1 hθ.1
  have hx1 : ρ * θ < 1 := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
  have h2 : (2 - ρ * θ) ≠ 0 := by linarith
  simp only [i12RBF, i12RBE1, i12RBPhi2, i12RBPsi3]
  generalize i12RG (θ * i12H (ρ * θ)) = a
  generalize i12RG (θ * i12H 0) = b
  simp only [i12H]
  field_simp [hρ.1.ne', hθ.1.ne']
  ring

theorem i12RBPhi2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i12RBPhi2 x = 16 * Real.log (1 - x / 2) / (x * (2 - x)) - 8 * Real.log 2 / (2 - x) := by
  have h2 : (2 - x) ≠ 0 := by linarith [hx.2]
  have hl : Real.log (i12H x) = Real.log (1 - x / 2) - Real.log 2 := by
    rw [← Real.log_div (by linarith [hx.2]) (by norm_num)]
    congr 1; unfold i12H; ring
  have hl0 : Real.log (i12H 0) = -Real.log 2 := by
    rw [i12H_zero, one_div, Real.log_inv]
  simp only [i12RBPhi2, hl, hl0]
  simp only [i12H]
  field_simp [hx.1.ne']
  ring

theorem abs_log_one_sub_half_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |Real.log (1 - x / 2)| ≤ x := by
  have h1 : 0 < 1 - x / 2 := by linarith [hx.2]
  have hu := Real.log_le_sub_one_of_pos h1
  have hl := Real.one_sub_inv_le_log_of_pos h1
  have e : 1 - (1 - x / 2)⁻¹ = -(x / (2 - x)) := by
    field_simp [show (2 - x) ≠ 0 by linarith [hx.2]]; ring
  have hb : x / (2 - x) ≤ x := by
    rw [div_le_iff₀ (by linarith [hx.2])]; nlinarith [hx.1, hx.2]
  rw [abs_le]
  constructor <;> linarith

theorem abs_i12RBPhi2_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : |i12RBPhi2 x| ≤ 24 := by
  rw [i12RBPhi2_eq hx]
  have h2 : 1 < 2 - x := by linarith [hx.2]
  have hl := abs_log_one_sub_half_le hx
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : |16 * Real.log (1 - x / 2) / (x * (2 - x))| ≤ 16 := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hx.1 (by linarith)), div_le_iff₀
      (mul_pos hx.1 (by linarith))]
    norm_num
    nlinarith [hx.1]
  have e2 : |8 * Real.log 2 / (2 - x)| ≤ 8 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 - x), div_le_iff₀ (by linarith),
      abs_of_pos (by positivity)]
    nlinarith
  calc _ ≤ |16 * Real.log (1 - x / 2) / (x * (2 - x))| + |8 * Real.log 2 / (2 - x)| :=
        abs_sub _ _
    _ ≤ 24 := by linarith

/-- `∫₀¹ 2 / (2 - ρθ) dθ = -2 log (1 - ρ/2) / ρ`. -/
theorem integral_i12_two_div {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun θ => 2 / (2 - ρ * θ)) (Ioo 0 1) ∧
      ∫ θ in Ioo (0 : ℝ) 1, 2 / (2 - ρ * θ) = -2 * Real.log (1 - ρ / 2) / ρ := by
  have hpos : ∀ θ ∈ uIcc (0 : ℝ) 1, 0 < 1 - ρ * θ / 2 := by
    intro θ hθ
    rw [uIcc_of_le zero_le_one] at hθ
    nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
  have hd : ∀ θ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun θ => -2 * Real.log (1 - ρ * θ / 2) / ρ)
      (2 / (2 - ρ * θ)) θ := by
    intro θ hθ
    have h1 := hpos θ hθ
    have h := ((((hasDerivAt_id' θ).const_mul ρ).div_const 2).const_sub 1).log h1.ne'
    refine ((h.const_mul (-2)).div_const ρ).congr_deriv ?_
    field_simp [hρ.1.ne', show (2 - ρ * θ) ≠ 0 by linarith]
  have hc : ContinuousOn (fun θ => 2 / (2 - ρ * θ)) (uIcc 0 1) := by
    refine continuousOn_const.div (by fun_prop) fun θ hθ => ?_
    have := hpos θ hθ; linarith
  have hii := hc.intervalIntegrable (μ := volume)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hii, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii]
  simp

/-- `∫₀¹ log θ / (2 - ρθ) dθ = -Li₂ (ρ/2) / ρ`. -/
theorem integral_i12_log_div {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun θ => Real.log θ / (2 - ρ * θ)) (Ioo 0 1) ∧
      ∫ θ in Ioo (0 : ℝ) 1, Real.log θ / (2 - ρ * θ) = -Li₂ (ρ / 2) / ρ := by
  set P : ℝ → ℝ := fun θ => -(Real.log θ * Real.log (1 - ρ * θ / 2) + Li₂ (ρ * θ / 2)) / ρ
    with hP
  have hd : ∀ θ ∈ Ioc (0 : ℝ) 1, HasDerivAt P (Real.log θ / (2 - ρ * θ)) θ := by
    intro θ hθ
    have h1 : 0 < 1 - ρ * θ / 2 := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
    have hq : 0 < ρ * θ / 2 := by have := mul_pos hρ.1 hθ.1; linarith
    have hq1 : |ρ * θ / 2| < 1 := by rw [abs_of_pos hq]; nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
    have hlin : HasDerivAt (fun θ => ρ * θ / 2) (ρ / 2) θ := by
      simpa using ((hasDerivAt_id' θ).const_mul ρ).div_const 2
    have hL := (hlin.const_sub 1).log h1.ne'
    have hLi := (hasDerivAt_Li₂ hq1 hq.ne').comp θ hlin
    have h := ((((hasDerivAt_log hθ.1.ne').mul hL).add hLi).neg).div_const ρ
    refine h.congr_deriv ?_
    have hθ0 := hθ.1.ne'
    field_simp [hρ.1.ne', show (2 - ρ * θ) ≠ 0 by nlinarith [hρ.2, hθ.2]]
    ring
  have hint : IntegrableOn (fun θ => Real.log θ / (2 - ρ * θ)) (Ioo 0 1) := by
    refine (integrableOn_log_Ioo.norm).mono' ?_ ?_
    · exact (ContinuousOn.div (continuousOn_log.mono fun θ hθ => hθ.1.ne')
        (by fun_prop) fun θ hθ => by nlinarith [hρ.2, hθ.2, hρ.1, hθ.1]).aestronglyMeasurable
        measurableSet_Ioo
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have h1 : 1 ≤ 2 - ρ * θ := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < 2 - ρ * θ)]
      exact div_le_self (abs_nonneg _) h1
  refine ⟨hint, ?_⟩
  have h0 : Tendsto P (𝓝[>] 0) (𝓝 0) := by
    have ha : Tendsto (fun θ => Real.log θ * Real.log (1 - ρ * θ / 2)) (𝓝[>] 0) (𝓝 0) := by
      have hb : Tendsto (fun θ : ℝ => ρ * |θ * Real.log θ|) (𝓝[>] 0) (𝓝 (ρ * |0|)) :=
        (tendsto_mul_log_zero.abs).const_mul ρ
      rw [abs_zero, mul_zero] at hb
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      have hx : ρ * θ ∈ Ioo (0 : ℝ) 1 :=
        ⟨mul_pos hρ.1 hθ.1, by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]⟩
      have hl := abs_log_one_sub_half_le hx
      rw [show ρ * θ / 2 = (ρ * θ) / 2 by ring] at *
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hθ.1]
      nlinarith [abs_nonneg (Real.log θ), abs_nonneg θ, abs_of_pos hθ.1]
    have hq : Tendsto (fun θ : ℝ => ρ * θ / 2) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous (fun θ : ℝ => ρ * θ / 2) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hLi : Tendsto (fun θ : ℝ => Li₂ (ρ * θ / 2)) (𝓝[>] 0) (𝓝 (Li₂ 0)) := by
      refine tendsto_Li₂_comp (by norm_num) hq ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      exact ⟨by nlinarith [hρ.1, hθ.1], by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]⟩
    rw [Li₂_zero] at hLi
    have := ((ha.add hLi).neg).div_const ρ
    simpa [hP] using this
  have h1 : Tendsto P (𝓝[<] 1) (𝓝 (P 1)) :=
    (hd 1 ⟨one_pos, le_rfl⟩).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
      (fun θ hθ => hd θ ⟨hθ.1, hθ.2.le⟩)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hint) h0 h1]
  simp [hP]

/-- The integrand of `B₁`. -/
noncomputable def i12RBB1 (ρ : ℝ) : ℝ :=
  -4 * Real.log ρ * Real.log (1 - ρ / 2) / ρ - 8 * Li₂ (ρ / 2) / ρ +
    2 * (2 * Real.log (1 - ρ) + 1) * Real.log (1 - ρ / 2) / ρ

theorem integral_i12RBE1_theta {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ∫ θ in Ioo (0 : ℝ) 1, i12RBE1 ρ θ = i12RBB1 ρ := by
  obtain ⟨hA, hAv⟩ := integral_i12_two_div hρ
  obtain ⟨hB, hBv⟩ := integral_i12_log_div hρ
  have hpt : ∀ θ ∈ Ioo (0 : ℝ) 1, i12RBE1 ρ θ = (2 * Real.log ρ - 2 * Real.log (1 - ρ) - 1) *
      (2 / (2 - ρ * θ)) + 8 * (Real.log θ / (2 - ρ * θ)) := by
    intro θ _; simp only [i12RBE1]; ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt,
    integral_add (hA.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul, hAv,
    hBv]
  simp only [i12RBB1]
  field_simp
  ring

/-- The integrand of `B₂`. -/
noncomputable def i12RBB2 (x : ℝ) : ℝ :=
  -Real.log x * (16 * Real.log (1 - x / 2) / (x * (2 - x)) - 8 * Real.log 2 / (2 - x))

/-- The integrand of `B₃`. -/
noncomputable def i12RBB3 (x : ℝ) : ℝ :=
  (4 / (2 - x) * (i12RK ((2 - x) / 4) - i12RK (x * (2 - x) / 4)) -
    2 * (i12RK (1 / 2) - i12RK (x / 2))) / x

theorem integrableOn_i12RBE1 :
    IntegrableOn (fun q : ℝ × ℝ => i12RBE1 q.1 q.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have : IsFiniteMeasure μ := by
    rw [isFiniteMeasure_restrict]; exact measure_Ioo_lt_top.ne
  have hl := integrableOn_log_Ioo.norm
  have hl1 := integrableOn_log_one_sub.norm
  have ha : Integrable (fun ρ : ℝ => 4 * ‖Real.log ρ‖ + 4 * ‖Real.log (1 - ρ)‖ + 2) μ :=
    ((hl.const_mul 4).add (hl1.const_mul 4)).add (integrable_const 2)
  have hb : Integrable (fun z : ℝ × ℝ => (4 * ‖Real.log z.1‖ + 4 * ‖Real.log (1 - z.1)‖ + 2) +
      8 * ‖Real.log z.2‖) (μ.prod μ) :=
    (ha.comp_fst μ).add ((hl.const_mul 8).comp_snd μ)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine hb.mono' (by unfold i12RBE1; fun_prop) ?_
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo) fun q hq => ?_
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  have hd : 1 < 2 - q.1 * q.2 := by nlinarith
  have hw : 0 < 2 / (2 - q.1 * q.2) ∧ 2 / (2 - q.1 * q.2) ≤ 2 :=
    ⟨by positivity, by rw [div_le_iff₀ (by linarith)]; linarith⟩
  simp only [i12RBE1, Real.norm_eq_abs]
  rw [abs_mul, abs_of_pos hw.1]
  have e : |2 * (Real.log q.1 + 2 * Real.log q.2) - 2 * Real.log (1 - q.1) - 1| ≤
      2 * |Real.log q.1| + 4 * |Real.log q.2| + 2 * |Real.log (1 - q.1)| + 1 := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (Real.log q.1), neg_abs_le (Real.log q.1),
      le_abs_self (Real.log q.2), neg_abs_le (Real.log q.2), le_abs_self (Real.log (1 - q.1)),
      neg_abs_le (Real.log (1 - q.1))]
  nlinarith [abs_nonneg (2 * (Real.log q.1 + 2 * Real.log q.2) - 2 * Real.log (1 - q.1) - 1)]

theorem integrableOn_i12RBPhi2 :
    IntegrableOn (fun q : ℝ × ℝ => i12RBPhi2 (q.1 * q.2)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hfin : volume (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  refine Measure.integrableOn_of_bounded (M := 24) hfin.ne
    (Measurable.aestronglyMeasurable (by unfold i12RBPhi2 i12H; fun_prop)) ?_
  refine ae_restrict_of_forall_mem hS fun q hq => ?_
  rw [Real.norm_eq_abs]
  exact abs_i12RBPhi2_le ⟨mul_pos hq.1.1 hq.2.1, by nlinarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]⟩

/-- **`R_B'(0)` in one dimension**: `R_B'(0) = B₁ + B₂ + B₃`, with
`B₁ = ∫₀¹ (-4 log ρ log (1 - ρ/2) - 8 Li₂ (ρ/2) + 2 (2 log (1 - ρ) + 1) log (1 - ρ/2)) / ρ dρ`,
`B₂ = ∫₀¹ -log x (16 log (1 - x/2) / (x (2 - x)) - 8 log 2 / (2 - x)) dx`,
`B₃ = ∫₀¹ (4/(2 - x) (K((2 - x)/4) - K(x(2 - x)/4)) - 2 (K(1/2) - K(x/2))) / x dx`;
the three integrands are integrable. -/
theorem deriv_i12RB3_zero_eq :
    IntegrableOn i12RBB1 (Ioo 0 1) ∧ IntegrableOn i12RBB2 (Ioo 0 1) ∧
      IntegrableOn i12RBB3 (Ioo 0 1) ∧
      deriv i12RB3 0 = ((∫ ρ in Ioo (0 : ℝ) 1, i12RBB1 ρ) + (∫ x in Ioo (0 : ℝ) 1, i12RBB2 x) +
        (∫ x in Ioo (0 : ℝ) 1, i12RBB3 x) : ℝ) := by
  obtain ⟨hF, hd⟩ := deriv_i12RB3_zero_eq_square
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hE := integrableOn_i12RBE1
  have hP := integrableOn_i12RBPhi2
  have hsplit : ∀ q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i12RBF q.1 q.2 - i12RBE1 q.1 q.2 -
      i12RBPhi2 (q.1 * q.2) = i12RBPsi3 (q.1 * q.2) q.2 := by
    intro q hq; rw [i12RBF_eq hq.1 hq.2]; ring
  have hQ : IntegrableOn (fun q : ℝ × ℝ => i12RBPsi3 (q.1 * q.2) q.2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := ((hF.sub hE).sub hP).congr_fun hsplit hS
  -- B₁: Fubini, then the `θ`-integral.
  have hE' := hE
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hE'
  have hB1 : IntegrableOn i12RBB1 (Ioo 0 1) :=
    (show IntegrableOn (fun ρ => ∫ θ in Ioo (0 : ℝ) 1, i12RBE1 ρ θ) (Ioo 0 1) volume from
      hE'.integral_prod_left).congr_fun (fun ρ hρ => integral_i12RBE1_theta hρ)
      measurableSet_Ioo
  have hvE : ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i12RBE1 q.1 q.2 =
      ∫ ρ in Ioo (0 : ℝ) 1, i12RBB1 ρ := by
    have hE'' := hE
    rw [Measure.volume_eq_prod] at hE''
    rw [Measure.volume_eq_prod, setIntegral_prod _ hE'']
    exact setIntegral_congr_fun measurableSet_Ioo fun ρ hρ => integral_i12RBE1_theta hρ
  -- B₂: the substitution `x = ρθ`.
  obtain ⟨-, hP2, hvP⟩ := i12_integral_tri (ψ := fun q => i12RBPhi2 q.1) hP
  have hin2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ θ in Ioo x 1, i12RBPhi2 x / θ = i12RBB2 x := by
    intro x hx
    simp only [div_eq_mul_inv, integral_const_mul]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.2.le,
      integral_inv_of_pos hx.1 one_pos, i12RBB2, i12RBPhi2_eq hx, one_div, Real.log_inv]
    ring
  -- B₃: the substitution `x = ρθ` and the `θ`-integral of `G(θ q)/θ`.
  obtain ⟨-, hP3, hvQ⟩ := i12_integral_tri (ψ := fun q => i12RBPsi3 q.1 q.2) hQ
  have hin3 : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ θ in Ioo x 1, i12RBPsi3 x θ / θ = i12RBB3 x := by
    intro x hx
    have hH : 0 < i12H x := i12H_pos (by linarith [hx.2])
    have hH0 : 0 < i12H 0 := i12H_pos (by norm_num)
    obtain ⟨hi1, hv1⟩ := integral_i12RG_div hH hx
    obtain ⟨hi0, hv0⟩ := integral_i12RG_div hH0 hx
    have hpt : ∀ θ ∈ Ioo x 1, i12RBPsi3 x θ / θ = (1 / (x * i12H x)) * (i12RG (θ * i12H x) / θ) -
        (1 / (x * i12H 0)) * (i12RG (θ * i12H 0) / θ) := by
      intro θ hθ
      have hθ0 : θ ≠ 0 := by linarith [hx.1, hθ.1]
      simp only [i12RBPsi3]
      field_simp [hx.1.ne', hH.ne', hH0.ne']
    rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_sub (hi1.const_mul _)
      (hi0.const_mul _), integral_const_mul, integral_const_mul, hv1, hv0, i12RBB3, i12H_zero]
    simp only [i12H]
    have h2 : (2 - x) ≠ 0 := by linarith [hx.2]
    have e1 : x * ((2 - x) / 4) = x * (2 - x) / 4 := by ring
    have e2 : x * (1 / 2) = x / 2 := by ring
    rw [e1, e2]
    field_simp [hx.1.ne']
  refine ⟨hB1, hP2.congr_fun hin2 measurableSet_Ioo, hP3.congr_fun hin3 measurableSet_Ioo, ?_⟩
  rw [hd]
  congr 1
  have hsum : ∀ q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i12RBF q.1 q.2 =
      i12RBE1 q.1 q.2 + i12RBPhi2 (q.1 * q.2) + i12RBPsi3 (q.1 * q.2) q.2 :=
    fun q hq => i12RBF_eq hq.1 hq.2
  have hEP : IntegrableOn (fun q : ℝ × ℝ => i12RBE1 q.1 q.2 + i12RBPhi2 (q.1 * q.2))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := hE.add hP
  rw [setIntegral_congr_fun hS hsum, integral_add hEP hQ, integral_add hE hP, hvE]
  simp only at hvP hvQ
  rw [hvP, hvQ, setIntegral_congr_fun measurableSet_Ioo hin2,
    setIntegral_congr_fun measurableSet_Ioo hin3]

end QED.ThreeLoopD
