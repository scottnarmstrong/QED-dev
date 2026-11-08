/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Compactness.Compact

/-!
# Smoothness of parametric integrals over a compact set

Let `μ` be a finite measure carried by a compact set `K`, and let `g(s, z)` be `C^∞` on an open
set `W ⊆ ℝ × E` containing `U ×ˢ K`, with `U ⊆ ℝ` open. Then `s ↦ ∫ g(s, z) dμ(z)` is `C^∞`
on `U`.

The proof is by induction on the order. The `s`-derivative of the integral is the integral of
the partial derivative `fderiv ℝ g (s, z) (1, 0)`, which is again `C^∞` on `W`. Differentiation
under the integral sign is justified by a constant bound: by the tube lemma a set
`closedBall s₀ ε ×ˢ K` lies in `W`, and it is compact, so the partial derivative is bounded on it.

## Main statements

* `QED.Integration.hasDerivAt_integral_restrict_of_contDiffOn`: differentiation under the
  integral sign.
* `QED.Integration.contDiffOn_integral_of_contDiffOn_prod`: the `C^∞` statement.
-/

public section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace QED.Integration

/-- A tube lemma: if `{s₀} ×ˢ K ⊆ W` with `K` compact and `W` open, then some closed ball
around `s₀` times `K` still lies in `W`. -/
theorem exists_closedBall_prod_subset {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {W : Set (ℝ × X)}
    (hW : IsOpen W) {s₀ : ℝ} (hs₀ : {s₀} ×ˢ K ⊆ W) :
    ∃ ε > 0, closedBall s₀ ε ×ˢ K ⊆ W := by
  obtain ⟨u, v, hu, -, hsu, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hW hs₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu s₀ (hsu rfl)
  exact ⟨ε / 2, half_pos hε,
    (prod_mono ((closedBall_subset_ball (half_lt_self hε)).trans hball) hKv).trans huv⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

/-- **Differentiation under the integral sign** over a compact set. If `g` is `C¹` on an open
set `W` containing `{s₀} ×ˢ K`, then `s ↦ ∫_K g(s, z) dμ` has derivative
`∫_K ∂ₛg(s₀, z) dμ` at `s₀`, where `∂ₛg(p) = fderiv ℝ g p (1, 0)`. -/
theorem hasDerivAt_integral_restrict_of_contDiffOn {μ : Measure E} [IsFiniteMeasure μ]
    {K : Set E} (hK : IsCompact K) {W : Set (ℝ × E)} (hW : IsOpen W) {g : ℝ × E → ℝ}
    (hg : ContDiffOn ℝ 1 g W) {s₀ : ℝ} (hs₀ : {s₀} ×ˢ K ⊆ W) :
    HasDerivAt (fun s => ∫ z, g (s, z) ∂μ.restrict K)
      (∫ z, fderiv ℝ g (s₀, z) (1, 0) ∂μ.restrict K) s₀ := by
  obtain ⟨ε, hε, hεW⟩ := exists_closedBall_prod_subset hK hW hs₀
  have hKm : MeasurableSet K := hK.measurableSet
  have hmem : ∀ x ∈ closedBall s₀ ε, ∀ z ∈ K, (x, z) ∈ W := fun x hx z hz => hεW ⟨hx, hz⟩
  have hslice : ∀ {f : ℝ × E → ℝ}, ContinuousOn f W → ∀ x ∈ closedBall s₀ ε,
      ContinuousOn (fun z => f (x, z)) K := fun hf x hx =>
    hf.comp (by fun_prop : Continuous fun z : E => (x, z)).continuousOn
      fun z hz => hmem x hx z hz
  have hg'c : ContinuousOn (fun p => fderiv ℝ g p (1, 0)) W :=
    (hg.continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply continuousOn_const
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall s₀ ε).prod hK).exists_bound_of_continuousOn (hg'c.mono hεW)
  have hball : ball s₀ ε ∈ 𝓝 s₀ := ball_mem_nhds s₀ hε
  have hsub : ball s₀ ε ⊆ closedBall s₀ ε := ball_subset_closedBall
  have hs₀ε : s₀ ∈ closedBall s₀ ε := mem_closedBall_self hε.le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x z => g (x, z))
    (F' := fun x z => fderiv ℝ g (x, z) (1, 0)) (bound := fun _ => C) hball ?_ ?_ ?_ ?_
    (integrable_const C) ?_).2
  · filter_upwards [hball] with x hx
    exact (hslice hg.continuousOn x (hsub hx)).aestronglyMeasurable hKm
  · exact (hslice hg.continuousOn s₀ hs₀ε).integrableOn_compact hK
  · exact (hslice hg'c s₀ hs₀ε).aestronglyMeasurable hKm
  · exact ae_restrict_of_forall_mem hKm fun z hz x hx => hC (x, z) ⟨hsub hx, hz⟩
  · refine ae_restrict_of_forall_mem hKm fun z hz x hx => ?_
    have hxz := hmem x (hsub hx) z hz
    have hd : DifferentiableAt ℝ g (x, z) :=
      (hg.differentiableOn one_ne_zero (x, z) hxz).differentiableAt (hW.mem_nhds hxz)
    exact HasFDerivAt.comp_hasDerivAt x hd.hasFDerivAt
      ((hasDerivAt_id' x).prodMk (hasDerivAt_const x z))

/-- Finite-order smoothness of `s ↦ ∫_K g(s, z) dμ`, by induction on the order. -/
theorem contDiffOn_integral_restrict_of_contDiffOn {μ : Measure E} [IsFiniteMeasure μ]
    {K : Set E} (hK : IsCompact K) {U : Set ℝ} (hU : IsOpen U) {W : Set (ℝ × E)}
    (hW : IsOpen W) (hUW : U ×ˢ K ⊆ W) {g : ℝ × E → ℝ} (hg : ContDiffOn ℝ ∞ g W) (n : ℕ) :
    ContDiffOn ℝ n (fun s => ∫ z, g (s, z) ∂μ.restrict K) U := by
  have hderiv : ∀ g : ℝ × E → ℝ, ContDiffOn ℝ ∞ g W → ∀ s₀ ∈ U,
      HasDerivAt (fun s => ∫ z, g (s, z) ∂μ.restrict K)
        (∫ z, fderiv ℝ g (s₀, z) (1, 0) ∂μ.restrict K) s₀ := fun g hg s₀ hs₀ =>
    hasDerivAt_integral_restrict_of_contDiffOn hK hW (hg.of_le (by simp))
      ((prod_mono (singleton_subset_iff.mpr hs₀) subset_rfl).trans hUW)
  induction n generalizing g with
  | zero =>
    exact contDiffOn_zero.mpr fun s hs => (hderiv g hg s hs).continuousAt.continuousWithinAt
  | succ n ih =>
    have hg' : ContDiffOn ℝ ∞ (fun p => fderiv ℝ g p (1, 0)) W :=
      (hg.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨fun s hs => (hderiv g hg s hs).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact (ih hg').congr fun s hs => (hderiv g hg s hs).deriv

/-- **Smoothness of a parametric integral.** Let `μ` be a finite measure carried by a compact
set `K`, and let `g` be `C^∞` on an open set `W ⊆ ℝ × E` containing `U ×ˢ K`, where `U ⊆ ℝ` is
open. Then `s ↦ ∫ g(s, z) dμ(z)` is `C^∞` on `U`. -/
theorem contDiffOn_integral_of_contDiffOn_prod {μ : Measure E} [IsFiniteMeasure μ]
    {K : Set E} (hK : IsCompact K) (hμK : ∀ᵐ z ∂μ, z ∈ K) {U : Set ℝ} (hU : IsOpen U)
    {W : Set (ℝ × E)} (hW : IsOpen W) (hUW : U ×ˢ K ⊆ W) {g : ℝ × E → ℝ}
    (hg : ContDiffOn ℝ ∞ g W) :
    ContDiffOn ℝ ∞ (fun s => ∫ z, g (s, z) ∂μ) U := by
  rw [← Measure.restrict_eq_self_of_ae_mem hμK]
  exact contDiffOn_infty.mpr fun n => contDiffOn_integral_restrict_of_contDiffOn hK hU hW hUW hg n

end QED.Integration

end
