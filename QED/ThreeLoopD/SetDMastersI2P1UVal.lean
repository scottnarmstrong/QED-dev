/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1ULines
public import QED.ThreeLoopD.SetDMastersI2P1UTri

/-!
# Set (d), master `I₂`: `∫∫ (1 - w) (Θ - 3 Ψ) dx dw = -3 π⁴ / 10`

The `y₄`-primitive `Θ(A, B, C)` of `QED.ThreeLoopD.SetDMastersI2P1ULines`, at
`A = α₁ α₂`, `B = α₂ α₃`, `C = α₁ α₃` with `α₁ + α₂ + α₃ = 1`, is
`Θ = 3 Ψ + T(α₂, α₁) + T(α₂, α₃) + T(α₁, α₃)` (`QED.ThreeLoopD.i2P1UTheta_eq`), with `T` from
`QED.ThreeLoopD.SetDMastersI2P1UTri`. In the coordinates of `I₂`, `α₁ = (1 - w) x`, `α₂ = w`,
`α₃ = (1 - w)(1 - x)`, and `(1 - w) dx dw` is the Lebesgue measure of the triangle in each of
the three pairs of Feynman parameters, so each `T` contributes `7 π⁴ / 60 - 13 π⁴ / 60`.

## Main results

* `QED.ThreeLoopD.i2P1UTheta_eq`.
* `QED.ThreeLoopD.i2P1U_lint_plus`, `QED.ThreeLoopD.i2P1U_lint_minus`: the lower integrals of
  the positive and negative parts.
* `QED.ThreeLoopD.i2P1U_theta_sub`: `(1 - w) (Θ - 3 Ψ)` is integrable on `(0, 1)²` with
  integral `-3 π⁴ / 10`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog Function
open scoped ENNReal

namespace QED.ThreeLoopD

/-- One dilogarithmic term of `Θ` is `T(u, v)`. -/
theorem i2P1UVal_term {P S₁ S₂ σ u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu1 : u < 1) (hv1 : v < 1)
    (hP : P = u * v) (h₁ : S₁ = u * (1 - u)) (h₂ : S₂ = v * (1 - v))
    (hσ : σ = u * v * (1 - u - v)) :
    (((log S₁ + log S₂) ^ 2 - log σ ^ 2) / 2 + Li₂ (P ^ 2 / (S₁ * S₂))) / P = i2P1UT u v := by
  subst hP h₁ h₂ hσ
  have h1 : 1 - u ≠ 0 := by linarith
  have h2 : 1 - v ≠ 0 := by linarith
  rw [i2P1UT, show (u * v) ^ 2 / (u * (1 - u) * (v * (1 - v))) = u * v / ((1 - u) * (1 - v)) by
    field_simp]

/-- **`Θ = 3 Ψ + T(α₂, α₁) + T(α₂, α₃) + T(α₁, α₃)`**, `α₃ = 1 - α₁ - α₂`. -/
theorem i2P1UTheta_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1) :
    i2P1UTheta (a * b) (b * (1 - a - b)) (a * (1 - a - b)) =
      3 * i2P0Psi (a * b) (b * (1 - a - b)) (a * (1 - a - b)) + i2P1UT b a +
        i2P1UT b (1 - a - b) + i2P1UT a (1 - a - b) := by
  have hc : 0 < 1 - a - b := by linarith
  have hσ : a * b * (b * (1 - a - b)) + (a * b + b * (1 - a - b)) * (a * (1 - a - b)) =
      a * b * (1 - a - b) := by ring
  unfold i2P1UTheta
  rw [i2P1UVal_term hb ha (by linarith) (by linarith) (mul_comm a b) (by ring) (by ring)
      (by rw [hσ]; ring),
    i2P1UVal_term hb hc (by linarith) (by linarith) rfl (by ring) (by ring) (by rw [hσ]; ring),
    i2P1UVal_term ha hc (by linarith) (by linarith) rfl (by ring) (by ring) (by rw [hσ]; ring)]

/-- `(x, w) ↦ (α₂, α₁) = (w, (1 - w) x)`. -/
theorem i2P1US_xw_A' {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (uncurry g)) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - w) * g w ((1 - w) * x) =
      ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), g u v := by
  rw [i2P1US_xw_A (g := fun a b => g b a) (hg.comp measurable_swap)]
  exact i2P1US_tri_swap (g := fun a b => g b a) (hg.comp measurable_swap)

/-- `(x, w) ↦ (α₂, α₃) = (w, (1 - w)(1 - x))`. -/
theorem i2P1US_xw_B {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (uncurry g)) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1 - w) * g w ((1 - w) * (1 - x)) =
      ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), g u v := by
  rw [← i2P1US_xw_A' hg]
  exact i2P1US_reflect 1 (fun x => ∫⁻ w in Ioo (0 : ℝ) 1,
    ENNReal.ofReal (1 - w) * g w ((1 - w) * x))

theorem measurable_i2P1UGp_real : Measurable (uncurry i2P1UGp) := by
  unfold i2P1UGp i2P1Ur
  fun_prop

theorem measurable_i2P1UGm_real : Measurable (uncurry i2P1UGm) := by
  unfold i2P1UGm i2P1Ur i2P1Uh i2P1Us
  fun_prop

/-- The three pair placements of a function on the triangle, weighted by `1 - w`. -/
noncomputable def i2P1USum (G : ℝ → ℝ → ℝ) (x w : ℝ) : ℝ :=
  (1 - w) * (G w ((1 - w) * x) + G w ((1 - w) * (1 - x)) + G ((1 - w) * x) ((1 - w) * (1 - x)))

theorem measurable_i2P1USum {G : ℝ → ℝ → ℝ} (hG : Measurable (uncurry G)) :
    Measurable fun p : ℝ × ℝ => i2P1USum G p.1 p.2 := by
  have h1 : Measurable fun p : ℝ × ℝ => G p.2 ((1 - p.2) * p.1) :=
    hG.comp (f := fun p : ℝ × ℝ => (p.2, (1 - p.2) * p.1)) (by fun_prop)
  have h2 : Measurable fun p : ℝ × ℝ => G p.2 ((1 - p.2) * (1 - p.1)) :=
    hG.comp (f := fun p : ℝ × ℝ => (p.2, (1 - p.2) * (1 - p.1))) (by fun_prop)
  have h3 : Measurable fun p : ℝ × ℝ => G ((1 - p.2) * p.1) ((1 - p.2) * (1 - p.1)) :=
    hG.comp (f := fun p : ℝ × ℝ => ((1 - p.2) * p.1, (1 - p.2) * (1 - p.1))) (by fun_prop)
  unfold i2P1USum
  fun_prop

/-- **The three placements together**: three times the triangle integral. -/
theorem i2P1U_lint_sum {G : ℝ → ℝ → ℝ} (hG : Measurable (uncurry G))
    (hnn : ∀ u v, 0 < u → 0 < v → u + v < 1 → 0 ≤ G u v) {c : ℝ}
    (hc : ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo (0 : ℝ) (1 - u), ENNReal.ofReal (G u v) =
      ENNReal.ofReal c) (hc0 : 0 ≤ c) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1USum G x w) =
      ENNReal.ofReal (3 * c) := by
  have hGe : Measurable (uncurry fun u v => ENNReal.ofReal (G u v)) :=
    ENNReal.measurable_ofReal.comp hG
  set f₁ : ℝ → ℝ → ℝ≥0∞ := fun x w => ENNReal.ofReal (1 - w) * ENNReal.ofReal (G w ((1 - w) * x))
  set f₂ : ℝ → ℝ → ℝ≥0∞ := fun x w =>
    ENNReal.ofReal (1 - w) * ENNReal.ofReal (G w ((1 - w) * (1 - x)))
  set f₃ : ℝ → ℝ → ℝ≥0∞ := fun x w =>
    ENNReal.ofReal (1 - w) * ENNReal.ofReal (G ((1 - w) * x) ((1 - w) * (1 - x)))
  have m₁ : Measurable (uncurry f₁) := (by fun_prop : Measurable fun p : ℝ × ℝ =>
    ENNReal.ofReal (1 - p.2)).mul (hGe.comp (f := fun p : ℝ × ℝ => (p.2, (1 - p.2) * p.1))
      (by fun_prop))
  have m₂ : Measurable (uncurry f₂) := (by fun_prop : Measurable fun p : ℝ × ℝ =>
    ENNReal.ofReal (1 - p.2)).mul (hGe.comp
      (f := fun p : ℝ × ℝ => (p.2, (1 - p.2) * (1 - p.1))) (by fun_prop))
  have m₃ : Measurable (uncurry f₃) := (by fun_prop : Measurable fun p : ℝ × ℝ =>
    ENNReal.ofReal (1 - p.2)).mul (hGe.comp
      (f := fun p : ℝ × ℝ => ((1 - p.2) * p.1, (1 - p.2) * (1 - p.1))) (by fun_prop))
  have e : ∀ x ∈ Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1USum G x w) =
      ((∫⁻ w in Ioo (0 : ℝ) 1, f₁ x w) + ∫⁻ w in Ioo (0 : ℝ) 1, f₂ x w) +
        ∫⁻ w in Ioo (0 : ℝ) 1, f₃ x w := by
    intro x hx
    have n₁ : Measurable fun w => f₁ x w := m₁.comp measurable_prodMk_left
    have n₂ : Measurable fun w => f₂ x w := m₂.comp measurable_prodMk_left
    rw [← lintegral_add_left (f := fun w => f₁ x w) n₁,
      ← lintegral_add_left (f := fun w => f₁ x w + f₂ x w) (n₁.add n₂)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have hv : 0 ≤ 1 - w := by linarith [hw.2]
    have hα1 : 0 < (1 - w) * x := mul_pos (by linarith [hw.2]) hx.1
    have hα3 : 0 < (1 - w) * (1 - x) := mul_pos (by linarith [hw.2]) (by linarith [hx.2])
    have g1 := hnn w ((1 - w) * x) hw.1 hα1 (by nlinarith [hx.2, hw.2])
    have g2 := hnn w ((1 - w) * (1 - x)) hw.1 hα3 (by nlinarith [hx.1, hw.2])
    have g3 := hnn ((1 - w) * x) ((1 - w) * (1 - x)) hα1 hα3 (by nlinarith [hw.1])
    simp only [f₁, f₂, f₃]
    rw [← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_mul hv,
      ← ENNReal.ofReal_add (mul_nonneg hv g1) (mul_nonneg hv g2),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg hv g3), i2P1USum]
    congr 1
    ring
  have l₁ : Measurable fun x => ∫⁻ w in Ioo (0 : ℝ) 1, f₁ x w := m₁.lintegral_prod_right'
  have l₂ : Measurable fun x => ∫⁻ w in Ioo (0 : ℝ) 1, f₂ x w := m₂.lintegral_prod_right'
  rw [setLIntegral_congr_fun measurableSet_Ioo e, lintegral_add_left
    (f := fun x => (∫⁻ w in Ioo (0 : ℝ) 1, f₁ x w) + ∫⁻ w in Ioo (0 : ℝ) 1, f₂ x w) (l₁.add l₂),
    lintegral_add_left (f := fun x => ∫⁻ w in Ioo (0 : ℝ) 1, f₁ x w) l₁, i2P1US_xw_A' hGe,
    i2P1US_xw_B hGe, i2P1US_xw_C hGe, hc,
    ← ENNReal.ofReal_add hc0 hc0, ← ENNReal.ofReal_add (by positivity) hc0]
  congr 1
  ring

/-- **The positive part**: `∫∫ (1 - w) Σ G₊ = 7 π⁴ / 20`. -/
theorem i2P1U_lint_plus :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1USum i2P1UGp x w) =
      ENNReal.ofReal (7 * π ^ 4 / 20) := by
  rw [i2P1U_lint_sum measurable_i2P1UGp_real (fun u v hu hv huv => i2P1UGp_nonneg hu hv huv)
    i2P1UTri_plus (by positivity)]
  congr 1
  ring

/-- **The negative part**: `∫∫ (1 - w) Σ G₋ = 13 π⁴ / 20`. -/
theorem i2P1U_lint_minus :
    ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1USum i2P1UGm x w) =
      ENNReal.ofReal (13 * π ^ 4 / 20) := by
  rw [i2P1U_lint_sum measurable_i2P1UGm_real (fun u v hu hv huv => i2P1UGm_nonneg hu hv huv)
    i2P1UTri_minus (by positivity)]
  congr 1
  ring

/-- Bochner integral of a nonnegative function from its lower integral. -/
theorem i2P1U_integrable_of_lint {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (hm : Measurable f) (hnn : ∀ᵐ x ∂μ, 0 ≤ f x)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal c) :
    Integrable f μ ∧ ∫ x, f x ∂μ = c := by
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩, ?_⟩
  · rw [h]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable, h,
      ENNReal.toReal_ofReal hc]

/-- The lower integral over the square as an iterated integral. -/
theorem i2P1U_lint_square {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, f p =
      ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, f (x, w) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hf.aemeasurable]

theorem i2P1USum_nonneg {G : ℝ → ℝ → ℝ}
    (hnn : ∀ u v, 0 < u → 0 < v → u + v < 1 → 0 ≤ G u v) {x w : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) : 0 ≤ i2P1USum G x w := by
  have hα1 : 0 < (1 - w) * x := mul_pos (by linarith [hw.2]) hx.1
  have hα3 : 0 < (1 - w) * (1 - x) := mul_pos (by linarith [hw.2]) (by linarith [hx.2])
  have g1 := hnn w ((1 - w) * x) hw.1 hα1 (by nlinarith [hx.2, hw.2])
  have g2 := hnn w ((1 - w) * (1 - x)) hw.1 hα3 (by nlinarith [hx.1, hw.2])
  have g3 := hnn ((1 - w) * x) ((1 - w) * (1 - x)) hα1 hα3 (by nlinarith [hw.1])
  have : 0 ≤ 1 - w := by linarith [hw.2]
  unfold i2P1USum
  positivity

theorem i2P1USum_integral {G : ℝ → ℝ → ℝ} (hG : Measurable (uncurry G))
    (hnn : ∀ u v, 0 < u → 0 < v → u + v < 1 → 0 ≤ G u v) {c : ℝ} (hc0 : 0 ≤ c)
    (h : ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P1USum G x w) =
      ENNReal.ofReal c) :
    IntegrableOn (fun p : ℝ × ℝ => i2P1USum G p.1 p.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∧
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i2P1USum G p.1 p.2 = c := by
  have hm := measurable_i2P1USum hG
  refine i2P1U_integrable_of_lint hc0 hm ?_ ?_
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact i2P1USum_nonneg hnn hp.1 hp.2
  · rw [i2P1U_lint_square (f := fun p => ENNReal.ofReal (i2P1USum G p.1 p.2))
      (ENNReal.measurable_ofReal.comp hm)]
    exact h

/-- **`∫∫ (1 - w) (Θ - 3 Ψ) dx dw = -3 π⁴ / 10`** on `(0, 1)²`, `p = (x, w)`. -/
theorem i2P1U_theta_sub :
    IntegrableOn (fun p : ℝ × ℝ => (1 - p.2) *
        (i2P1UTheta (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1)) -
        3 * i2P0Psi (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1)))) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∧
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, (1 - p.2) *
        (i2P1UTheta (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1)) -
        3 * i2P0Psi (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1))) = -(3 * π ^ 4 / 10) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := measurableSet_Ioo.prod
    measurableSet_Ioo
  obtain ⟨hp, vp⟩ := i2P1USum_integral measurable_i2P1UGp_real
    (fun u v hu hv huv => i2P1UGp_nonneg hu hv huv) (by positivity) i2P1U_lint_plus
  obtain ⟨hm, vm⟩ := i2P1USum_integral measurable_i2P1UGm_real
    (fun u v hu hv huv => i2P1UGm_nonneg hu hv huv) (by positivity) i2P1U_lint_minus
  have eq : EqOn (fun p : ℝ × ℝ => i2P1USum i2P1UGp p.1 p.2 - i2P1USum i2P1UGm p.1 p.2)
      (fun p : ℝ × ℝ => (1 - p.2) *
        (i2P1UTheta (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1)) -
        3 * i2P0Psi (p.2 * (1 - p.2) * p.1) (p.2 * (1 - p.2) * (1 - p.1))
          ((1 - p.2) ^ 2 * p.1 * (1 - p.1)))) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    have hα1 : 0 < (1 - w) * x := mul_pos (by linarith [hw.2]) hx.1
    have hα3 : 0 < (1 - w) * (1 - x) := mul_pos (by linarith [hw.2]) (by linarith [hx.2])
    have hab : (1 - w) * x + w < 1 := by nlinarith [hx.2, hw.1]
    have hT := i2P1UTheta_eq hα1 hw.1 hab
    have e3 : 1 - (1 - w) * x - w = (1 - w) * (1 - x) := by ring
    rw [e3, show (1 - w) * x * w = w * (1 - w) * x by ring,
      show w * ((1 - w) * (1 - x)) = w * (1 - w) * (1 - x) by ring,
      show (1 - w) * x * ((1 - w) * (1 - x)) = (1 - w) ^ 2 * x * (1 - x) by ring] at hT
    simp only
    rw [hT, i2P1USum, i2P1USum, i2P1UT_eq hw.1 hα1 (by linarith),
      i2P1UT_eq hw.1 hα3 (by nlinarith [hx.1, hw.2]), i2P1UT_eq hα1 hα3 (by nlinarith [hw.1])]
    ring
  refine ⟨(hp.sub hm).congr_fun eq hS, ?_⟩
  rw [← setIntegral_congr_fun hS eq, integral_sub hp hm, vp, vm]
  ring

end QED.ThreeLoopD
