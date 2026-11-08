/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.FormFactorPair
import QED.Algebra.Spinor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Facts for the charge renormalization of the one-loop vertex

On shell, the `γ^μ` coefficient `A = formFactorA` of the one-loop vertex depends on the momenta
only through `q²`. This module proves the facts needed to impose the charge condition (63.1):

* `sandwich_vertexOneLoop_self`: at `p' = p` the sandwich of the one-loop vertex is
  `e A(0) ū γ^μ u`, with `A(0)` independent of `p`;
* `exists_sandwich_gamma_zero_ne_zero`: some on-shell sandwich `ū γ⁰ u` is nonzero;
* `exists_abs_integral_formIntegrandAq_sub_lt`: `A(q²)` is continuous at `q² = 0⁺` at fixed
  regulators.

These are internal helpers.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-- The on-shell Feynman mass term as a function of `q² = s`. -/
noncomputable def massDq (m M s : ℝ) (z : ℝ × ℝ) : ℝ :=
  (1 - z.2) * M ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s)

/-- The integrand of `A` as a function of `q² = s`. -/
noncomputable def formIntegrandAq (m mγ Λ s : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 * (Real.log (massDq m Λ s z / massDq m mγ s z)
    + 1 / 2 * ((massDq m mγ s z)⁻¹ - (massDq m Λ s z)⁻¹)
      * (2 * ((1 - 4 * (1 - z.2) + (1 - z.2) ^ 2) * m ^ 2
        - ((1 - z.2) + (z.2 * z.1) * (z.2 * (1 - z.1))) * s)))

theorem formIntegrandA_eq_q {m mγ Λ : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (z : ℝ × ℝ) :
    formIntegrandA m mγ Λ p' p z
      = formIntegrandAq m mγ Λ (Minkowski.dot (p' - p) (p' - p)) z := by
  simp only [formIntegrandA, formIntegrandAq, massDq, feynmanMass_onShell hp' hp]

theorem formFactorA_eq_q {e m mγ Λ : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) :
    formFactorA e m mγ Λ p' p = e ^ 2 / (16 * π ^ 2) *
      ∫ z, formIntegrandAq m mγ Λ (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure := by
  simp only [formFactorA, formIntegrandA_eq_q hp' hp]

theorem massDq_pos {m M s : ℝ} (hm : 0 < m) (hM : 0 < M) (hs : 0 ≤ s) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) : 0 < massDq m M s z := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
  have hxx : 0 ≤ z.1 * (1 - z.1) * s := mul_nonneg (mul_nonneg hx0 (by linarith)) hs
  have h1 : 0 ≤ (1 - z.2) * M ^ 2 := mul_nonneg (by linarith) (sq_nonneg M)
  unfold massDq
  rcases eq_or_lt_of_le hy0 with h0 | hpos
  · rw [← h0]; simp; positivity
  · have : 0 < z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s) := by positivity
    linarith

/-! ### Continuity of `A(q²)` at `q² = 0⁺` -/

section Continuity

variable {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
include hm hmγ hΛ

theorem continuousOn_formIntegrandAq :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => formIntegrandAq m mγ Λ q.1 q.2)
      (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  have hD : ∀ M : ℝ, Continuous fun q : ℝ × (ℝ × ℝ) => massDq m M q.1 q.2 := fun M => by
    unfold massDq; fun_prop
  have hpos : ∀ M : ℝ, 0 < M → ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      massDq m M q.1 q.2 ≠ 0 := fun M hM q hq => (massDq_pos hm hM hq.1.1 hq.2).ne'
  have hlog : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Real.log (massDq m Λ q.1 q.2 / massDq m mγ q.1 q.2))
      (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    ((hD Λ).continuousOn.div (hD mγ).continuousOn (hpos mγ hmγ)).log fun q hq =>
      (div_pos (massDq_pos hm hΛ hq.1.1 hq.2) (massDq_pos hm hmγ hq.1.1 hq.2)).ne'
  have hinv : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      (massDq m mγ q.1 q.2)⁻¹ - (massDq m Λ q.1 q.2)⁻¹)
      (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    ((hD mγ).continuousOn.inv₀ (hpos mγ hmγ)).sub ((hD Λ).continuousOn.inv₀ (hpos Λ hΛ))
  unfold formIntegrandAq
  exact (by fun_prop : Continuous fun q : ℝ × (ℝ × ℝ) => 2 * q.2.2).continuousOn.mul
    (hlog.add ((continuousOn_const.mul hinv).mul (by fun_prop)))

theorem continuousAt_formIntegrandAq {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ContinuousAt (fun s => formIntegrandAq m mγ Λ s z) 0 := by
  have hD : ∀ M : ℝ, Continuous fun s : ℝ => massDq m M s z := fun M => by
    unfold massDq; fun_prop
  have h0 : ∀ M : ℝ, 0 < M → massDq m M 0 z ≠ 0 := fun M hM =>
    (massDq_pos hm hM le_rfl hz).ne'
  unfold formIntegrandAq
  refine ContinuousAt.mul (by fun_prop) (ContinuousAt.add ?_ ?_)
  · exact ((hD Λ).continuousAt.div (hD mγ).continuousAt (h0 mγ hmγ)).log
      (div_pos (massDq_pos hm hΛ le_rfl hz) (massDq_pos hm hmγ le_rfl hz)).ne'
  · exact (continuousAt_const.mul (((hD mγ).continuousAt.inv₀ (h0 mγ hmγ)).sub
      ((hD Λ).continuousAt.inv₀ (h0 Λ hΛ)))).mul (by fun_prop)

/-- `A(q²)` is continuous at `q² = 0⁺`, at fixed regulators. -/
theorem tendsto_integral_formIntegrandAq :
    Tendsto (fun s => ∫ z, formIntegrandAq m mγ Λ s z ∂feynmanMeasure) (𝓝[>] 0)
      (𝓝 (∫ z, formIntegrandAq m mγ Λ 0 z ∂feynmanMeasure)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    (continuousOn_formIntegrandAq hm hmγ hΛ)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
    (integrable_const _) (ae_feynmanMeasure.mono fun z hz =>
      tendsto_nhdsWithin_of_tendsto_nhds
        (continuousAt_formIntegrandAq hm hmγ hΛ (Ioc_prod_subset hz)).tendsto)
  · have hs : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    refine hs.mono fun s hs => ?_
    have hcont : ContinuousOn (fun z => formIntegrandAq m mγ Λ s z)
        (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :=
      ((continuousOn_formIntegrandAq hm hmγ hΛ).comp
        (continuous_const.prodMk continuous_id : Continuous fun z : ℝ × ℝ => (s, z)).continuousOn
        fun z hz => ⟨⟨hs.1.le, hs.2.le⟩, Ioc_prod_subset hz⟩)
    rw [feynmanMeasure_eq]
    exact hcont.aestronglyMeasurable (measurableSet_Ioc.prod measurableSet_Ioc)
  · have hs : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    refine hs.mono fun s hs => ae_feynmanMeasure.mono fun z hz => ?_
    exact hC (s, z) ⟨⟨hs.1.le, hs.2.le⟩, Ioc_prod_subset hz⟩

theorem exists_abs_integral_formIntegrandAq_sub_lt {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      |∫ z, formIntegrandAq m mγ Λ s z ∂feynmanMeasure
        - ∫ z, formIntegrandAq m mγ Λ 0 z ∂feynmanMeasure| < η := by
  have h := (tendsto_integral_formIntegrandAq hm hmγ hΛ).eventually (Metric.ball_mem_nhds _ hη)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h)
  refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
  have := hδ' (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; exact hsδ) hs
  simpa [Metric.mem_ball, Real.dist_eq] using this

end Continuity

/-! ### The sandwich at `p' = p` -/

/-- At `p' = p` the sandwich of the one-loop vertex is `e A(0) ū γ^μ u`, with `A(0)` independent
of the on-shell momentum. -/
theorem sandwich_vertexOneLoop_self {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (μ : Fin 4)
    {u w : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p = -((m : ℂ) • w)) :
    w ⬝ᵥ (vertexOneLoop e m mγ Λ hm hmγ hΛ p p hp hp hp0 hp0 μ *ᵥ u)
      = (e : ℂ) * ((e ^ 2 / (16 * π ^ 2) * ∫ z, formIntegrandAq m mγ Λ 0 z ∂feynmanMeasure : ℝ)
          : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) := by
  rw [vertexOneLoop_eq_limit hm hmγ hΛ hp hp hp0 hp0 μ,
    sandwich_vertexLimit hm hmγ hΛ hp hp hp0 hp0 μ hu hw, formFactorA_eq_q hp hp]
  have hl : ∀ ν, Minkowski.lower (p - p) ν = 0 := fun ν => by
    simp [Minkowski.lower]
  have hd : Minkowski.dot (p - p) (p - p) = 0 := by simp [Minkowski.dot]
  simp only [hl, hd, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, smul_zero, sub_zero,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-- Some on-shell sandwich `ū γ⁰ u` is nonzero (it is `2p⁰` for the spinor `u_0(p)`). -/
theorem exists_sandwich_gamma_zero_ne_zero {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) :
    ∃ u w : Fin 4 → ℂ, Dirac.slash p *ᵥ u = -((m : ℂ) • u) ∧
      w ᵥ* Dirac.slash p = -((m : ℂ) • w) ∧ w ⬝ᵥ (Dirac.gamma 0 *ᵥ u) ≠ 0 := by
  set u := Dirac.spinor m p 0
  have hu := Dirac.slash_mulVec_spinor m p hp 0
  have hw := Dirac.bar_vecMul_slash m p u hu
  refine ⟨u, Dirac.bar u, hu, hw, ?_⟩
  have hg := Dirac.gordon m p p u (Dirac.bar u) hu hw 0
  have hn : Dirac.bar u ⬝ᵥ u = (2 * m : ℂ) := by
    simpa using Dirac.bar_spinor_dotProduct_spinor m hm p hp hp0 0 0
  simp only [sub_self, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, smul_zero,
    sub_zero, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hg
  rw [hn] at hg
  intro h0
  rw [h0, mul_zero] at hg
  have : ((p 0 + p 0 : ℝ) : ℂ) * (2 * m) ≠ 0 := by
    have : (0 : ℝ) < (p 0 + p 0) * (2 * m) := by positivity
    exact_mod_cast this.ne'
  exact this hg.symm

end QED.OneLoop.VertexLimit

end
