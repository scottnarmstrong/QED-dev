/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rotating all loop energies by a common complex factor

For the joint energy-first integral at `L` loops, the integrand at fixed spatial momenta is a
rational function of the `L` loop energies whose denominators are Minkowski denominators
`-(ℓ⁰)² + E² - iε` of linear combinations `ℓ⁰` of the energies, possibly shifted by external
energies. Multiplying **all** energies by a common complex factor `z` with `Re z > 0`,
`Im z ≥ 0` small keeps every such denominator away from zero (`Im (z²) ≥ 0` makes the imaginary
part of a centred denominator at most `-ε`, and a small `Im z` keeps the shifted ones negative).
This file proves the resulting change of contour in its abstract form, with no residue theorem.

Let `f z τ` be defined for `z` in the closed rectangle `rotRect h` (`1/2 ≤ Re z ≤ 2`,
`0 ≤ Im z ≤ h`) and `τ ∈ ℝⁿ`, homogeneous in the sense `f z (r τ) = f (r z) τ` for real `r > 0`
(as for `f z τ = G (z τ)`), complex differentiable in `z` at every point of the rectangle, and
dominated there by one integrable function of `τ`. Then (`integral_eq_rotate`), for
`0 < s < h`,
`∫ f 1 τ dτ = (1 + s i)ⁿ ∫ f (1 + s i) τ dτ`.

## Proof

`Φ(z) = zⁿ ∫ f z τ dτ` is constant along real rays, `Φ(r z) = Φ(z)`, by the scaling
`τ ↦ r τ` of Lebesgue measure (`scaledIntegral_mul_ofReal`). It is complex differentiable at the
interior points (differentiation under the integral sign, with the derivative bounded by the
Cauchy estimate, `hasDerivAt_integral_of_rect`), so its derivative `D` there satisfies
`D z = 0`, the derivative along the ray. Hence `u ↦ Φ(1 + u i)` has zero derivative on
`(0, h)` and is constant there, and it tends to `Φ(1)` as `u → 0⁺` by dominated convergence.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set

namespace QED.Integration.ThreeLoop

/-- The closed rectangle `1/2 ≤ Re z ≤ 2`, `0 ≤ Im z ≤ h` of complex energy scale factors. -/
def rotRect (h : ℝ) : Set ℂ := {z | 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ 0 ≤ z.im ∧ z.im ≤ h}

theorem one_mem_rotRect {h : ℝ} (hh : 0 ≤ h) : (1 : ℂ) ∈ rotRect h := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [hh]

theorem one_add_mem_rotRect {h u : ℝ} (hu : 0 ≤ u) (huh : u ≤ h) :
    (1 + (u : ℂ) * I) ∈ rotRect h := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [hu, huh]

variable {n : ℕ} {f : ℂ → (Fin n → ℝ) → ℂ}

/-- `Φ(z) = zⁿ ∫ f z τ dτ`. -/
noncomputable def scaledIntegral (f : ℂ → (Fin n → ℝ) → ℂ) (z : ℂ) : ℂ :=
  z ^ n * ∫ τ, f z τ

/-- `Φ` is constant along real rays. -/
theorem scaledIntegral_mul_ofReal (hom : ∀ z τ (r : ℝ), 0 < r → f z (r • τ) = f (r * z) τ)
    (z : ℂ) {r : ℝ} (hr : 0 < r) : scaledIntegral f (r * z) = scaledIntegral f z := by
  unfold scaledIntegral
  have h1 : (∫ τ, f (↑r * z) τ) = ∫ τ, f z (r • τ) := by
    congr 1
    funext τ
    rw [hom z τ r hr]
  rw [h1, Measure.integral_comp_smul (μ := volume) (f z) r, Module.finrank_fin_fun,
    abs_of_pos (by positivity), Complex.real_smul, mul_pow, ← mul_assoc]
  congr 1
  have hr' : (r : ℂ) ^ n ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hr.ne')
  push_cast
  field_simp

section Deriv

variable {h : ℝ} {g : (Fin n → ℝ) → ℝ}

/-- The derivative in `z` is a pointwise limit of difference quotients, hence measurable. -/
theorem aestronglyMeasurable_deriv (hd : ∀ τ, ∀ z ∈ rotRect h, DifferentiableAt ℂ (fun w => f w τ) z)
    (hm : ∀ z ∈ rotRect h, AEStronglyMeasurable (f z) volume) {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hball : closedBall z₀ δ ⊆ rotRect h) :
    AEStronglyMeasurable (fun τ => deriv (fun w => f w τ) z₀) volume := by
  set q : ℕ → ℂ := fun k => z₀ + ((δ / (k + 2) : ℝ) : ℂ)
  have hq_mem : ∀ k, q k ∈ rotRect h := fun k => hball (by
    rw [mem_closedBall, dist_eq_norm]
    simp only [q, add_sub_cancel_left, norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hz₀ : z₀ ∈ rotRect h := hball (mem_closedBall_self hδ.le)
  have hq_tend : Tendsto q atTop (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have : Tendsto (fun k : ℕ => ((δ / (k + 2) : ℝ) : ℂ)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun k : ℕ => δ / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          have := tendsto_natCast_atTop_atTop (R := ℝ)
          exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 this)
        have h1 := (continuous_ofReal.tendsto 0).comp h0
        rw [ofReal_zero] at h1
        exact h1
      have h2 := (tendsto_const_nhds (x := z₀)).add this
      rw [add_zero] at h2
      exact h2
    · simp only [q, mem_compl_iff, mem_singleton_iff, add_eq_left, ofReal_eq_zero]
      exact (div_pos hδ (by positivity)).ne'
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun k τ => slope (fun w => f w τ) z₀ (q k)) (fun k => ?_)
    (Eventually.of_forall fun τ => ?_)
  · simp only [slope_def_module]
    exact ((hm _ (hq_mem k)).sub (hm _ hz₀)).const_smul ((q k - z₀)⁻¹)
  · exact ((hd τ z₀ hz₀).hasDerivAt.tendsto_slope).comp hq_tend

/-- **Differentiation under the integral sign** at a point `z₀` with `closedBall z₀ δ` in the
rectangle; the derivative of the integrand is bounded by the Cauchy estimate. -/
theorem hasDerivAt_integral_of_rect (hg : Integrable g)
    (hb : ∀ z ∈ rotRect h, ∀ τ, ‖f z τ‖ ≤ g τ)
    (hd : ∀ τ, ∀ z ∈ rotRect h, DifferentiableAt ℂ (fun w => f w τ) z)
    (hm : ∀ z ∈ rotRect h, AEStronglyMeasurable (f z) volume) {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hball : closedBall z₀ δ ⊆ rotRect h) :
    HasDerivAt (fun z => ∫ τ, f z τ) (∫ τ, deriv (fun w => f w τ) z₀) z₀ := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hz₀ : z₀ ∈ rotRect h := hball (mem_closedBall_self hδ.le)
  have hdiffOn : ∀ τ, DifferentiableOn ℂ (fun w => f w τ) (closedBall z₀ δ) :=
    fun τ w hw => (hd τ w (hball hw)).differentiableWithinAt
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball z₀ (δ / 2))
    (F' := fun x τ => deriv (fun w => f w τ) x)
    (bound := fun τ => g τ / (δ / 2)) (ball_mem_nhds z₀ hδ2) ?_ ?_
    (aestronglyMeasurable_deriv hd hm hδ hball) ?_ (hg.div_const _) ?_).2
  · exact Filter.mem_of_superset (ball_mem_nhds z₀ hδ) fun x hx =>
      hm x (hball (ball_subset_closedBall hx))
  · exact hg.mono' (hm z₀ hz₀) (ae_of_all _ (hb z₀ hz₀))
  · refine ae_of_all _ fun τ x hx => ?_
    have hsub : closedBall x (δ / 2) ⊆ closedBall z₀ δ := by
      refine closedBall_subset_closedBall' ?_
      rw [mem_ball] at hx
      linarith
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hδ2
      ((hdiffOn τ).diffContOnCl_ball hsub) fun w hw => ?_
    exact hb w (hball (hsub (sphere_subset_closedBall hw))) τ
  · refine ae_of_all _ fun τ x hx => ?_
    exact (hd τ x (hball (ball_subset_closedBall
      (ball_subset_ball (by linarith : δ / 2 ≤ δ) hx)))).hasDerivAt

/-- At an interior point `1 + u i`, `0 < u < h`, the derivative of `Φ` vanishes. -/
theorem hasDerivAt_scaledIntegral_zero (hom : ∀ z τ (r : ℝ), 0 < r → f z (r • τ) = f (r * z) τ)
    (hg : Integrable g) (hb : ∀ z ∈ rotRect h, ∀ τ, ‖f z τ‖ ≤ g τ)
    (hd : ∀ τ, ∀ z ∈ rotRect h, DifferentiableAt ℂ (fun w => f w τ) z)
    (hm : ∀ z ∈ rotRect h, AEStronglyMeasurable (f z) volume) {u : ℝ} (hu : 0 < u)
    (huh : u < h) : HasDerivAt (scaledIntegral f) 0 (1 + u * I) := by
  set z₀ : ℂ := 1 + u * I with hz₀
  set δ : ℝ := min (min u (h - u)) (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hu (by linarith)) (by norm_num)
  have hδu : δ ≤ u := (min_le_left _ _).trans (min_le_left _ _)
  have hδh : δ ≤ h - u := (min_le_left _ _).trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hball : closedBall z₀ δ ⊆ rotRect h := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hre := (abs_re_le_norm (w - z₀)).trans hw
    have him := (abs_im_le_norm (w - z₀)).trans hw
    simp only [hz₀, sub_re, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, sub_im, add_im, one_im, mul_im, zero_add] at hre him
    rw [abs_le] at hre him
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hD := (hasDerivAt_pow n z₀).mul (hasDerivAt_integral_of_rect hg hb hd hm hδ hball)
  set D := (n : ℂ) * z₀ ^ (n - 1) * (∫ τ, f z₀ τ) + z₀ ^ n * ∫ τ, deriv (fun w => f w τ) z₀
  have hD' : HasDerivAt (scaledIntegral f) D z₀ := hD
  have h1 : HasDerivAt (fun ζ : ℂ => ζ * z₀) z₀ (1 : ℂ) := by
    simpa using (hasDerivAt_id (1 : ℂ)).mul_const z₀
  have h2 : HasDerivAt (scaledIntegral f) D ((1 : ℂ) * z₀) := by rwa [one_mul]
  have h3 : HasDerivAt (fun ζ : ℂ => scaledIntegral f (ζ * z₀)) (D * z₀) ((1 : ℝ) : ℂ) := by
    rw [ofReal_one]
    exact h2.comp (1 : ℂ) h1
  have h4 : HasDerivAt (fun r : ℝ => scaledIntegral f (r * z₀)) (D * z₀) 1 := h3.comp_ofReal
  have h5 : HasDerivAt (fun r : ℝ => scaledIntegral f (r * z₀)) 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (scaledIntegral f z₀)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (by norm_num : (0 : ℝ) < 1)] with r hr
    exact scaledIntegral_mul_ofReal hom z₀ hr
  have hz₀ne : z₀ ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hz₀] at this
  have hDz : D * z₀ = 0 := h4.unique h5
  have hD0 : D = 0 := by
    rcases mul_eq_zero.mp hDz with h | h
    · exact h
    · exact absurd h hz₀ne
  rwa [hD0] at hD'

end Deriv

/-- **The rotation of all loop energies by a common factor** `1 + s i`: under homogeneity,
complex differentiability on the rectangle `rotRect h` and an integrable bound there,
`∫ f 1 τ dτ = (1 + s i)ⁿ ∫ f (1 + s i) τ dτ` for `0 < s < h`. -/
theorem integral_eq_rotate (hom : ∀ z τ (r : ℝ), 0 < r → f z (r • τ) = f (r * z) τ)
    {h : ℝ} (hh : 0 < h) {g : (Fin n → ℝ) → ℝ} (hg : Integrable g)
    (hb : ∀ z ∈ rotRect h, ∀ τ, ‖f z τ‖ ≤ g τ)
    (hd : ∀ τ, ∀ z ∈ rotRect h, DifferentiableAt ℂ (fun w => f w τ) z)
    (hm : ∀ z ∈ rotRect h, AEStronglyMeasurable (f z) volume) {s : ℝ} (hs : 0 < s)
    (hsh : s < h) :
    ∫ τ, f 1 τ = (1 + s * I) ^ n * ∫ τ, f (1 + s * I) τ := by
  set ψ : ℝ → ℂ := fun u => scaledIntegral f (1 + u * I) with hψdef
  have hψ : ∀ u ∈ Ioo 0 h, HasDerivAt ψ 0 u := by
    intro u hu
    have h1 := hasDerivAt_scaledIntegral_zero hom hg hb hd hm hu.1 hu.2
    have h2 : HasDerivAt (fun ζ : ℂ => 1 + ζ * I) I (u : ℂ) := by
      simpa using ((hasDerivAt_id (u : ℂ)).mul_const I).const_add 1
    have h3 := h1.comp (u : ℂ) h2
    rw [zero_mul] at h3
    exact h3.comp_ofReal
  have hconst : ∀ u ∈ Ioo 0 h, ψ u = ψ s := fun u hu =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun x hx => (hψ x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hψ x hx).deriv) hu ⟨hs, hsh⟩
  have hlim : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (scaledIntegral f 1)) := by
    have hc : Tendsto (fun u : ℝ => (1 : ℂ) + u * I) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have : Continuous fun u : ℝ => (1 : ℂ) + u * I := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), (1 + (u : ℂ) * I) ∈ rotRect h := by
      filter_upwards [Ioo_mem_nhdsGT hh] with u hu
      exact one_add_mem_rotRect hu.1.le hu.2.le
    have hint : Tendsto (fun u : ℝ => ∫ τ, f (1 + u * I) τ) (𝓝[>] (0 : ℝ)) (𝓝 (∫ τ, f 1 τ)) := by
      refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hg ?_
      · filter_upwards [hev] with u hu
        exact hm _ hu
      · filter_upwards [hev] with u hu
        exact ae_of_all _ (hb _ hu)
      · exact ae_of_all _ fun τ =>
          ((hd τ 1 (one_mem_rotRect hh.le)).continuousAt.tendsto).comp hc
    exact ((hc.pow n).mul hint)
  have hlim' : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (ψ s)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hh] with u hu
    exact (hconst u hu).symm
  have := tendsto_nhds_unique hlim hlim'
  simpa [scaledIntegral, hψdef] using this

end QED.Integration.ThreeLoop

end
