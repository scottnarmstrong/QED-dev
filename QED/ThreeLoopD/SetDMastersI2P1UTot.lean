/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1USig

/-!
# Set (d), master `I₂`: the `U`-part of `P'(0)`

`T_U = ∫ (1 - w) log 𝒰 / 𝒰² = -3 π⁴ / 10 + 18 ζ(3)` over the domain of `I₂`
(`QED.ThreeLoopD.i2P1U_value`). With `σ = A B + (A + B) C` (the value of `𝒰` at
`y₄ = y₇ = y₈ = 0`), `log 𝒰 = log (𝒰 / σ) - (-log σ)` splits the integrand into two nonnegative
parts:

* `∫ (1 - w) log (𝒰 / σ) / 𝒰² = ∫∫ (1 - w) (Θ - log σ Ψ)` by
  `QED.ThreeLoopD.i2P1U_inner`, and
  `(1 - w)(Θ - log σ Ψ) = (1 - w)(Θ - 3 Ψ) + 3 (1 - w) Ψ + (-log σ)(1 - w) Ψ` has integral
  `-3 π⁴ / 10 + 18 ζ(3) + 2 π⁴ / 5`;
* `∫ (1 - w) (-log σ) / 𝒰² = ∫∫ (-log σ)(1 - w) Ψ = 2 π⁴ / 5`
  (`QED.ThreeLoopD.i2P1USig_lint`).

## Main results

* `QED.ThreeLoopD.i2P1UTheta_sub_nonneg`: `Θ - log s Ψ ≥ 0` for `s ≤ σ`.
* `QED.ThreeLoopD.i2P1U_value`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog Function
open scoped ENNReal

namespace QED.ThreeLoopD

/-- `Θ - log s Ψ ≥ 0`: it is the integral of `V₇ ≥ 0` over `(C, ∞)`. -/
theorem i2P1UTheta_sub_nonneg {A B C s : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hs : 0 < s) (hsC : s ≤ A * B + (A + B) * C) :
    0 ≤ i2P1UTheta A B C - log s * i2P0Psi A B C := by
  have hpos : ∀ c ∈ Ioi C, 0 ≤ i2P1UV7 A B c s := fun c (hc : C < c) =>
    i2P1UV7_nonneg hA hB (by linarith) hs (by nlinarith)
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := C) (l := -0)
    (g := fun c => -(i2P1UTheta A B c - log s * i2P0Psi A B c))
    (g' := fun c => i2P1UV7 A B c s)
    (fun c (hc : C ≤ c) => (hasDerivAt_i2P1UTheta (s := s) hA hB (by linarith)).neg.congr_deriv
      (neg_neg _)) hpos (tendsto_i2P1UTheta hA hB).neg
  have h2 := setIntegral_nonneg (μ := volume) measurableSet_Ioi hpos
  rw [h] at h2
  linarith

/-- The value of `𝒰` at `y = 0` in the coordinates `(x, w)`. -/
noncomputable def i2P1USigma (x w : ℝ) : ℝ :=
  w * (1 - w) * x * (w * (1 - w) * (1 - x)) +
    (w * (1 - w) * x + w * (1 - w) * (1 - x)) * ((1 - w) ^ 2 * x * (1 - x))

theorem i2P1USigma_eq (x w : ℝ) : i2P1USigma x w = w * (1 - w) ^ 2 * x * (1 - x) := by
  unfold i2P1USigma
  ring

theorem i2P1USigma_mem {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    i2P1USigma x w ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hA, hA1, hB, -, hC, hC1⟩ := i2_lines_pos hx hw
  rw [i2P1USigma_eq]
  have h1 : 0 < 1 - w := by linarith [hw.2]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  refine ⟨by have := hw.1; have := hx.1; positivity, ?_⟩
  rw [show w * (1 - w) ^ 2 * x * (1 - x) = w * ((1 - w) ^ 2 * x * (1 - x)) by ring]
  calc w * ((1 - w) ^ 2 * x * (1 - x)) < 1 * 1 :=
        mul_lt_mul hw.2 hC1 hC zero_le_one
    _ = 1 := one_mul 1

theorem i2U_ge_sigma {x w y₄ y₇ y₈ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
    (h4 : 0 < y₄) (h7 : 0 < y₇) (h8 : 0 < y₈) : i2P1USigma x w ≤ i2U x w y₄ y₇ y₈ := by
  obtain ⟨hA, -, hB, -, hC, -⟩ := i2_lines_pos hx hw
  unfold i2P1USigma i2U i2LineA i2LineB i2LineC
  nlinarith [mul_pos h4 h7, mul_pos h4 h8, mul_pos h7 h8, mul_pos h4 hA, mul_pos h4 hB,
    mul_pos h7 hB, mul_pos h7 hC, mul_pos h8 hA, mul_pos h8 hC, mul_pos h7 h4]

/-- The lower integral over the domain of `I₂` as an iterated integral. -/
theorem i2P1U_lint_dom {g : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z in i2Dom, g z = ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1,
      ∫⁻ y₄ in Ioi (0 : ℝ), ∫⁻ y₇ in Ioi (0 : ℝ), ∫⁻ y₈ in Ioi (0 : ℝ), g (x, w, y₄, y₇, y₈) := by
  rw [i2Dom, volume_restrict_prod5, lintegral_prod _ hg.aemeasurable]
  refine lintegral_congr fun x => ?_
  have m1 : Measurable fun y : ℝ × ℝ × ℝ × ℝ => g (x, y) := hg.comp measurable_prodMk_left
  rw [lintegral_prod _ m1.aemeasurable]
  refine lintegral_congr fun w => ?_
  have m2 : Measurable fun y : ℝ × ℝ × ℝ => g (x, w, y) := m1.comp measurable_prodMk_left
  rw [lintegral_prod _ m2.aemeasurable]
  refine lintegral_congr fun y₄ => ?_
  have m3 : Measurable fun y : ℝ × ℝ => g (x, w, y₄, y) := m2.comp measurable_prodMk_left
  rw [lintegral_prod _ m3.aemeasurable]

/-- The lower integral over the square as an iterated integral, for an a.e.-measurable
integrand. -/
theorem i2P1U_lint_square' {f : ℝ × ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :
    ∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, f p =
      ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, f (x, w) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf ⊢
  rw [lintegral_prod _ hf]

/-- `∫∫ (1 - w) Ψ = 6 ζ(3)` as a Bochner integral over the square. -/
theorem i2P0Q_integral :
    IntegrableOn (fun p : ℝ × ℝ => i2P0Q p.1 p.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∧
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i2P0Q p.1 p.2 = 6 * zeta3 := by
  have hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (i2P0Q p.1 p.2) :=
    ENNReal.measurable_ofReal.comp measurable_i2P0Q
  refine i2P1U_integrable_of_lint (by positivity [zeta3_pos]) measurable_i2P0Q ?_ ?_
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    obtain ⟨hA, -, hB, -, hC, -⟩ := i2_lines_pos hp.1 hp.2
    exact mul_nonneg (by linarith [hp.2.2]) (i2P0Psi_nonneg hA hB hC)
  · rw [i2P1U_lint_square (f := fun p => ENNReal.ofReal (i2P0Q p.1 p.2)) hm,
      lintegral_lintegral_swap hm.aemeasurable,
      setLIntegral_congr_fun measurableSet_Ioo fun w hw => i2P0_lint_x hw, i2P0_lint_w]

/-- `∫∫ (-log σ)(1 - w) Ψ = 2 π⁴ / 5` as a Bochner integral over the square. -/
theorem i2P1USig_integral :
    IntegrableOn (fun p : ℝ × ℝ => -log (i2P1USigma p.1 p.2) * i2P0Q p.1 p.2)
        (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∧
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, -log (i2P1USigma p.1 p.2) * i2P0Q p.1 p.2 =
        2 * π ^ 4 / 5 := by
  have hm0 : Measurable fun p : ℝ × ℝ => -log (i2P1USigma p.1 p.2) * i2P0Q p.1 p.2 :=
    (by unfold i2P1USigma; fun_prop : Measurable fun p : ℝ × ℝ =>
      -log (i2P1USigma p.1 p.2)).mul measurable_i2P0Q
  refine i2P1U_integrable_of_lint (by positivity) hm0 ?_ ?_
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    obtain ⟨hA, -, hB, -, hC, -⟩ := i2_lines_pos hp.1 hp.2
    exact i2P1USig_nn (i2P1USigma_mem hp.1 hp.2)
      (mul_nonneg (by linarith [hp.2.2]) (i2P0Psi_nonneg hA hB hC))
  · rw [i2P1U_lint_square (f := fun p => ENNReal.ofReal (-log (i2P1USigma p.1 p.2) *
      i2P0Q p.1 p.2)) (ENNReal.measurable_ofReal.comp hm0)]
    exact i2P1USig_lint

/-- `K = (1 - w)(Θ - log σ Ψ)`, the three line integrals of `(1 - w) log (𝒰 / σ) / 𝒰²`. -/
noncomputable def i2P1UK (x w : ℝ) : ℝ :=
  (1 - w) * (i2P1UTheta (w * (1 - w) * x) (w * (1 - w) * (1 - x)) ((1 - w) ^ 2 * x * (1 - x)) -
    log (i2P1USigma x w) * i2P0Psi (w * (1 - w) * x) (w * (1 - w) * (1 - x))
      ((1 - w) ^ 2 * x * (1 - x)))

theorem i2P1UK_lint :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1UK x w) =
      ENNReal.ofReal (π ^ 4 / 10 + 18 * zeta3) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  obtain ⟨h1, v1⟩ := i2P1U_theta_sub
  obtain ⟨h2, v2⟩ := i2P0Q_integral
  obtain ⟨h3, v3⟩ := i2P1USig_integral
  have eq : EqOn (fun p : ℝ × ℝ => i2P1UK p.1 p.2) (fun p : ℝ × ℝ => (1 - p.2) *
        (i2P1UTheta (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1)) -
        3 * i2P0Psi (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1))) + 3 * i2P0Q p.1 p.2 +
        -log (i2P1USigma p.1 p.2) * i2P0Q p.1 p.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rintro ⟨x, w⟩ -
    simp only [i2P1UK, i2P0Q]
    ring
  have hK : IntegrableOn (fun p : ℝ × ℝ => i2P1UK p.1 p.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    ((h1.add (h2.const_mul 3)).add h3).congr_fun eq.symm hS
  have hv : ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i2P1UK p.1 p.2 = π ^ 4 / 10 + 18 * zeta3 := by
    have h12 : IntegrableOn (fun p : ℝ × ℝ => (1 - p.2) *
        (i2P1UTheta (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1)) -
        3 * i2P0Psi (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1))) + 3 * i2P0Q p.1 p.2)
        (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := h1.add (h2.const_mul 3)
    rw [setIntegral_congr_fun hS eq, integral_add h12 h3,
      integral_add h1 (h2.const_mul 3), integral_const_mul, v1, v2, v3]
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)]
      fun p : ℝ × ℝ => i2P1UK p.1 p.2 := by
    filter_upwards [ae_restrict_mem hS] with p hp
    obtain ⟨hA, -, hB, -, hC, -⟩ := i2_lines_pos hp.1 hp.2
    exact mul_nonneg (by linarith [hp.2.2]) (i2P1UTheta_sub_nonneg hA hB hC
      (i2P1USigma_mem hp.1 hp.2).1 le_rfl)
  rw [← i2P1U_lint_square' (f := fun p => ENNReal.ofReal (i2P1UK p.1 p.2))
      (ENNReal.measurable_ofReal.comp_aemeasurable hK.aestronglyMeasurable.aemeasurable),
    ← ofReal_integral_eq_lintegral_ofReal hK hnn, hv]

/-- **`T_U = ∫ (1 - w) log 𝒰 / 𝒰² = -3 π⁴ / 10 + 18 ζ(3)`** over the domain of `I₂`. -/
theorem i2P1U_value :
    IntegrableOn (fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) *
        log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom ∧
      ∫ z in i2Dom, (1 - z.2.1) * log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 = -(3 * π ^ 4 / 10) + 18 * zeta3 := by
  have hS : MeasurableSet i2Dom :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioi.prod
      (measurableSet_Ioi.prod measurableSet_Ioi)))
  set f₁ : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun z => (1 - z.2.1) *
    log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 / i2P1USigma z.1 z.2.1) /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 with hf₁
  set f₂ : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun z => (1 - z.2.1) * (-log (i2P1USigma z.1 z.2.1)) /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 with hf₂
  have m₁ : Measurable f₁ := by
    rw [hf₁]; unfold i2U i2LineA i2LineB i2LineC i2P1USigma; fun_prop
  have m₂ : Measurable f₂ := by
    rw [hf₂]; unfold i2U i2LineA i2LineB i2LineC i2P1USigma; fun_prop
  have hσ : ∀ z ∈ i2Dom, i2P1USigma z.1 z.2.1 ∈ Ioo (0 : ℝ) 1 := fun z hz =>
    i2P1USigma_mem hz.1 hz.2.1
  have n₁ : ∀ z ∈ i2Dom, 0 ≤ f₁ z := fun z hz => by
    obtain ⟨hx, hw, h4, h7, h8⟩ := hz
    have hs := hσ z ⟨hx, hw, h4, h7, h8⟩
    have hU := i2U_ge_sigma hx hw h4 h7 h8
    have hl : 0 ≤ log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 / i2P1USigma z.1 z.2.1) :=
      log_nonneg ((one_le_div hs.1).2 hU)
    have : 0 ≤ 1 - z.2.1 := by linarith [hw.2]
    simp only [hf₁]
    positivity
  have n₂ : ∀ z ∈ i2Dom, 0 ≤ f₂ z := fun z hz => by
    have hs := hσ z hz
    have := log_nonpos hs.1.le hs.2.le
    have : 0 ≤ 1 - z.2.1 := by linarith [hz.2.1.2]
    have : 0 ≤ -log (i2P1USigma z.1 z.2.1) := by linarith
    simp only [hf₂]
    positivity
  have l₁ : ∫⁻ z in i2Dom, ENNReal.ofReal (f₁ z) = ENNReal.ofReal (π ^ 4 / 10 + 18 * zeta3) := by
    rw [i2P1U_lint_dom (g := fun z => ENNReal.ofReal (f₁ z)) (ENNReal.measurable_ofReal.comp m₁),
      ← i2P1UK_lint]
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    exact i2P1U_inner hx hw
  have l₂ : ∫⁻ z in i2Dom, ENNReal.ofReal (f₂ z) = ENNReal.ofReal (2 * π ^ 4 / 5) := by
    rw [i2P1U_lint_dom (g := fun z => ENNReal.ofReal (f₂ z)) (ENNReal.measurable_ofReal.comp m₂),
      ← i2P1USig_lint]
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have hs := i2P1USigma_mem hx hw
    have hl : 0 ≤ -log (i2P1USigma x w) := by linarith [log_nonpos hs.1.le hs.2.le]
    change _ = ENNReal.ofReal (-log (i2P1USigma x w) * i2P0Q x w)
    rw [ENNReal.ofReal_mul hl, ← i2P0_inner hx hw, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y₄ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y₇ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y₈ => ?_
    rw [← ENNReal.ofReal_mul hl]
    simp only [hf₂]
    congr 1
    ring
  obtain ⟨i₁, v₁⟩ := i2P1U_integrable_of_lint (μ := volume.restrict i2Dom)
    (by positivity [zeta3_pos]) m₁ (ae_restrict_of_forall_mem hS n₁) l₁
  obtain ⟨i₂, v₂⟩ := i2P1U_integrable_of_lint (μ := volume.restrict i2Dom)
    (by positivity) m₂ (ae_restrict_of_forall_mem hS n₂) l₂
  have eq : EqOn (fun z => f₁ z - f₂ z) (fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) *
      log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom := fun z hz => by
    have hs := hσ z hz
    obtain ⟨hU, -⟩ := i2UF_pos hz
    simp only [hf₁, hf₂]
    rw [log_div hU.ne' hs.1.ne']
    ring
  refine ⟨IntegrableOn.congr_fun (i₁.sub i₂) eq hS, ?_⟩
  rw [← setIntegral_congr_fun hS eq, integral_sub i₁ i₂, v₁, v₂]
  ring

end QED.ThreeLoopD
