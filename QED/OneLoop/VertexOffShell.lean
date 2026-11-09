/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexOffShellBound
import QED.OneLoop.VertexClosedForm
import QED.OneLoop.VertexSpatial
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The one-loop vertex limit off the mass shell

The frozen theorem (E), `QED.OneLoop.vertexLimit_existsUnique`, gives the limit `ε → 0⁺` of the
energy-first integral of the regulated one-loop vertex at on-shell positive-energy momenta
`(p', p)`. This module extends the existence of the limit to all momenta `(r', r)` in a
neighbourhood of such an on-shell point, and proves that the limit is continuous at `(p', p)`.

The on-shell premises enter the proof of (E) only through the lower bound
`3/4 min(M², m²) ≤ D_M` on the Feynman mass term over the unit square (`feynmanMass_pos`).
The mass term is jointly continuous in the momenta and the Feynman parameters, so by compactness
of the unit square the bound `c₀ ≤ D_M`, with `c₀ = 3/8 min(m_γ², Λ², m²)`, persists for
momenta near `(p', p)` (`eventually_offShell_good`). The estimates of
`QED.OneLoop.VertexOffShellBound`, uniform under that bound, then give:

* the limit at every nearby `(r', r)`, equal to the closed form `∫ v, spatialG 0 r' r v`
  (`eventually_tendsto_energyFirstIntegral`), with both energy-first stages integrable at every
  `ε > 0` (`eventually_integrable_energyFirst`);
* the continuity of that closed form at `(p', p)` (`continuousAt_integral_spatialG_zero`), by
  dominated convergence twice: over the Feynman parameters, where at `ε = 0` the integrand is a
  real power of the positive mass term `massW`, and over the spatial loop momentum, with the
  uniform `(1 + ‖v‖)⁻⁵` bound.

## Main statements

* `exists_tendsto_vertexIntegral_offShell`: there are `δ > 0` and `V` such that for all
  `(r', r)` within `δ` of `(p', p)` the energy-first integral converges to `V r' r` as `ε → 0⁺`,
  and `V` is continuous at `(p', p)`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexOffShell

open QED.OneLoop.VertexLimit

/-! ### Continuity in the momenta -/

section Continuity

variable {X : Type*} [TopologicalSpace X]

theorem continuous_shiftK_comp {f g : X → Fin 4 → ℝ} {w : X → ℝ × ℝ} (hf : Continuous f)
    (hg : Continuous g) (hw : Continuous w) : Continuous fun a => shiftK (f a) (g a) (w a) := by
  unfold shiftK; fun_prop

theorem continuous_feynmanMass_comp (m M : ℝ) {f g : X → Fin 4 → ℝ} {w : X → ℝ × ℝ}
    (hf : Continuous f) (hg : Continuous g) (hw : Continuous w) :
    Continuous fun a => feynmanMass m M (w a).1 (w a).2 (f a) (g a) := by
  have h1 := continuous_dot_comp hf hf
  have h2 := continuous_dot_comp hg hg
  have hK := continuous_shiftK_comp hf hg hw
  have h3 := continuous_dot_comp hK hK
  unfold shiftK at h3
  unfold feynmanMass
  fun_prop

theorem continuous_massW_comp (m M : ℝ) {f g : X → Fin 4 → ℝ} {w : X → ℝ × ℝ}
    {u : X → Fin 3 → ℝ} (hf : Continuous f) (hg : Continuous g) (hw : Continuous w)
    (hu : Continuous u) : Continuous fun a => massW m M (f a) (g a) (w a) (u a) := by
  unfold massW
  refine continuous_finsetSum _ (fun k _ => ?_) |>.add (continuous_feynmanMass_comp m M hf hg hw)
  exact (((continuous_apply k).comp hu).add
    ((continuous_apply k.succ).comp (continuous_shiftK_comp hf hg hw))).pow 2

/-- The numerator is jointly continuous in the external momenta and the loop momentum. -/
theorem continuous_vertexNumerator_comp (m : ℝ) (μ i j : Fin 4) {f g h : X → Fin 4 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun a => vertexNumerator m (f a) (g a) μ (h a) i j := by
  have hslash : Continuous Dirac.slash := by
    unfold Dirac.slash Minkowski.lower
    fun_prop
  have hs : ∀ k : X → Fin 4 → ℝ, Continuous k → Continuous fun a =>
      (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (k a + h a) := fun k hk =>
    continuous_const.sub (hslash.comp (hk.add hh))
  unfold vertexNumerator
  refine continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun ρ _ =>
    continuous_const.mul ?_
  exact ((((continuous_const.matrix_mul (hs f hf)).matrix_mul continuous_const).matrix_mul
    (hs g hg)).matrix_mul continuous_const).matrix_elem i j

end Continuity

/-- At `ε = 0` the closed-form energy integral is continuous in the momenta at any point where
the mass term `massW` is positive: there it is a real power of `massW`. -/
theorem continuousAt_timeT_zero {m M : ℝ} {p' p : Fin 4 → ℝ} (μ i j : Fin 4) {z : ℝ × ℝ}
    {v : Fin 3 → ℝ} (hW : 0 < massW m M p' p z v) :
    ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => timeT m M 0 x.1 x.2 μ i j z v)
      (p', p) := by
  have hWc : Continuous fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => massW m M x.1 x.2 z v :=
    continuous_massW_comp m M continuous_fst continuous_snd continuous_const continuous_const
  have ha : Continuous fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => -shiftK x.1 x.2 z 0 :=
    ((continuous_apply 0).comp
      (continuous_shiftK_comp continuous_fst continuous_snd continuous_const)).neg
  have hNc : Continuous fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      vertexNumerator m x.1 x.2 μ (Fin.cons (-shiftK x.1 x.2 z 0) v : Fin 4 → ℝ) i j :=
    continuous_vertexNumerator_comp m μ i j continuous_fst continuous_snd
      (Continuous.finCons (A := fun _ : Fin 4 => ℝ) ha continuous_const)
  have h32 : ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      ((massW m M x.1 x.2 z v ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) (p', p) :=
    Complex.continuous_ofReal.continuousAt.comp
      (hWc.continuousAt.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hW.ne'))
  have h52 : ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      ((massW m M x.1 x.2 z v ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) (p', p) :=
    Complex.continuous_ofReal.continuousAt.comp
      (hWc.continuousAt.rpow_const (p := -(5 / 2 : ℝ)) (Or.inl hW.ne'))
  have hg : ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      -(I * (π / 8 : ℂ)) * vertexForm μ (Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ))
          (Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ)) i j
          * ((massW m M x.1 x.2 z v ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
        + I * (3 * π / 8 : ℂ)
          * vertexNumerator m x.1 x.2 μ (Fin.cons (-shiftK x.1 x.2 z 0) v : Fin 4 → ℝ) i j
          * ((massW m M x.1 x.2 z v ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) (p', p) :=
    (continuousAt_const.mul h32).add ((continuousAt_const.mul hNc.continuousAt).mul h52)
  refine hg.congr ?_
  have hev : ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p), 0 < massW m M x.1 x.2 z v :=
    hWc.continuousAt.eventually (lt_mem_nhds hW)
  filter_upwards [hev] with x hx
  rw [timeT_zero_eq μ i j hx, alphaN_eq]

/-- `spatialG` is strongly measurable in the spatial loop momentum, for all parameters. -/
theorem stronglyMeasurable_spatialG (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    StronglyMeasurable (spatialG e m mγ Λ ε p' p μ i j) := by
  have h2 : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => (2 * (q.2.2 : ℂ)) :=
    measurable_const.mul (Complex.measurable_ofReal.comp measurable_snd.snd)
  have hf : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => kappa e * (2 * (q.2.2 : ℂ)) *
      (timeT m mγ ε p' p μ i j q.2 q.1 - timeT m Λ ε p' p μ i j q.2 q.1) :=
    (measurable_const.mul h2).mul
      ((measurable_timeT m mγ ε p' p μ i j).sub (measurable_timeT m Λ ε p' p μ i j))
  exact hf.stronglyMeasurable.integral_prod_right' (ν := feynmanMeasure)

/-! ### A neighbourhood of an on-shell point -/

/-- Near on-shell positive-energy momenta, the Feynman mass term stays above any constant below
its on-shell lower bound `3/4 min(M², m²)`, uniformly on the unit square. -/
theorem eventually_feynmanMass_ge {m M c : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hc : c < 3 / 4 * min (M ^ 2) (m ^ 2)) :
    ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p), ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      c ≤ feynmanMass m M z.1 z.2 x.1 x.2 := by
  refine (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    fun z hz => ?_
  have hcont : Continuous fun q : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × (ℝ × ℝ) =>
      feynmanMass m M q.2.1 q.2.2 q.1.1 q.1.2 :=
    continuous_feynmanMass_comp m M continuous_fst.fst continuous_fst.snd continuous_snd
  have hlt : c < feynmanMass m M z.1 z.2 p' p :=
    hc.trans_le (feynmanMass_pos hp' hp hp0' hp0 hz.1 hz.2)
  exact (hcont.continuousAt.eventually (lt_mem_nhds hlt)).mono fun q hq => hq.le

/-- The uniform lower bound on the Feynman mass used near an on-shell point. -/
noncomputable def offShellMass (m mγ Λ : ℝ) : ℝ :=
  3 / 8 * min (min (mγ ^ 2) (Λ ^ 2)) (m ^ 2)

theorem offShellMass_pos {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    0 < offShellMass m mγ Λ := by
  unfold offShellMass; positivity

/-- Near on-shell positive-energy momenta `(p', p)`, the momenta stay in the ball of radius
`‖p'‖ + ‖p‖ + 1` and both Feynman mass terms stay above `offShellMass` on the unit square. -/
theorem eventually_offShell_good {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) :
    ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p),
      ‖x.1‖ ≤ ‖p'‖ + ‖p‖ + 1 ∧ ‖x.2‖ ≤ ‖p'‖ + ‖p‖ + 1 ∧
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        offShellMass m mγ Λ ≤ feynmanMass m mγ z.1 z.2 x.1 x.2) ∧
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        offShellMass m mγ Λ ≤ feynmanMass m Λ z.1 z.2 x.1 x.2) := by
  have hlt : ∀ M : ℝ, 0 < M → min (mγ ^ 2) (Λ ^ 2) ≤ M ^ 2 →
      offShellMass m mγ Λ < 3 / 4 * min (M ^ 2) (m ^ 2) := by
    intro M hM hle
    have h1 : min (min (mγ ^ 2) (Λ ^ 2)) (m ^ 2) ≤ min (M ^ 2) (m ^ 2) :=
      min_le_min_right _ hle
    have h2 : 0 < min (M ^ 2) (m ^ 2) := by positivity
    unfold offShellMass
    linarith
  have h1 : ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p), ‖x.1‖ < ‖p'‖ + ‖p‖ + 1 :=
    continuous_fst.norm.continuousAt.eventually (gt_mem_nhds (by linarith [norm_nonneg p]))
  have h2 : ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p), ‖x.2‖ < ‖p'‖ + ‖p‖ + 1 :=
    continuous_snd.norm.continuousAt.eventually (gt_mem_nhds (by linarith [norm_nonneg p']))
  have h3 := eventually_feynmanMass_ge (M := mγ) hp' hp hp0' hp0
    (hlt mγ hmγ (min_le_left _ _))
  have h4 := eventually_feynmanMass_ge (M := Λ) hp' hp hp0' hp0
    (hlt Λ hΛ (min_le_right _ _))
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  exact ⟨hx1.le, hx2.le, hx3, hx4⟩

/-! ### The limit near an on-shell point -/

section NearShell

variable {e m mγ Λ : ℝ} {p' p : Fin 4 → ℝ}

/-- Near an on-shell point, the energy-first integral converges as `ε → 0⁺` to the closed form
`∫ v, spatialG 0 r' r v`. -/
theorem eventually_tendsto_energyFirstIntegral (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p),
      Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ =>
          vertexIntegrand e m mγ Λ ε x.1 x.2 μ ℓ i j)
        (𝓝[>] 0) (𝓝 (∫ v, spatialG e m mγ Λ 0 x.1 x.2 μ i j v)) :=
  (eventually_offShell_good hm hmγ hΛ hp' hp hp0' hp0).mono fun _ hx =>
    tendsto_energyFirstIntegral_of_feynmanMass_ge (offShellMass_pos hm hmγ hΛ) hx.2.2.1
      hx.2.2.2 μ i j

/-- Near an on-shell point, both stages of the energy-first integral are integrable at every
`ε > 0`. (The inner stage is integrable at all momenta, by
`QED.OneLoop.VertexLimit.integrable_time_vertexIntegrand`.) -/
theorem eventually_integrable_energyFirst (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p), ∀ ε > 0,
      (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
        vertexIntegrand e m mγ Λ ε x.1 x.2 μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
      Integrable fun v : Fin 3 → ℝ =>
        ∫ t : ℝ, vertexIntegrand e m mγ Λ ε x.1 x.2 μ (Fin.cons t v : Fin 4 → ℝ) i j :=
  (eventually_offShell_good hm hmγ hΛ hp' hp hp0' hp0).mono fun x hx _ hε =>
    ⟨fun v => integrable_time_vertexIntegrand hε e m mγ Λ x.1 x.2 μ i j v,
      (integrable_spatialG_of_feynmanMass_ge (offShellMass_pos hm hmγ hΛ) hx.2.2.1 hx.2.2.2
        μ i j hε).congr (Eventually.of_forall fun v =>
          (integral_vertexIntegrand_time hε e m mγ Λ x.1 x.2 μ i j v).symm)⟩

/-- At `ε = 0`, the energy integral `spatialG 0 r' r v` is continuous in the momenta at an
on-shell point, for each spatial loop momentum `v`. -/
theorem continuousAt_spatialG_zero (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (μ i j : Fin 4) (v : Fin 3 → ℝ) :
    ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => spatialG e m mγ Λ 0 x.1 x.2 μ i j v)
      (p', p) := by
  obtain ⟨Cb, hCb⟩ := exists_norm_timeT_sub_le_uniform m mγ Λ μ i j
    (offShellMass_pos hm hmγ hΛ) (‖p'‖ + ‖p‖ + 1)
  have hgood := eventually_offShell_good hm hmγ hΛ hp' hp hp0' hp0
  have hz0 : ((0 : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    simp
  have hCb0 : 0 ≤ Cb := by
    obtain ⟨x, hx⟩ := hgood.exists
    have h := hCb x.1 x.2 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 0 le_rfl _ hz0 v
    have hu : 0 < (1 + ‖v‖) ^ (-(5 : ℝ)) := by positivity
    by_contra hC
    nlinarith [norm_nonneg (timeT m mγ 0 x.1 x.2 μ i j (0, 0) v
      - timeT m Λ 0 x.1 x.2 μ i j (0, 0) v), not_le.mp hC]
  refine continuousAt_of_dominated (bound := fun _ => ‖kappa e‖ * 2 * Cb) ?_ ?_
    (integrable_const _) ?_
  · refine Eventually.of_forall fun x => ?_
    have h2 : Measurable fun z : ℝ × ℝ => (2 * (z.2 : ℂ)) :=
      measurable_const.mul (Complex.measurable_ofReal.comp measurable_snd)
    have hT : ∀ M : ℝ, Measurable fun z : ℝ × ℝ => timeT m M 0 x.1 x.2 μ i j z v := by
      intro M
      have h := (measurable_timeT m M 0 x.1 x.2 μ i j).comp (measurable_prodMk_left (x := v))
      exact h
    have h3 : Measurable fun z : ℝ × ℝ => kappa e * (2 * (z.2 : ℂ)) := measurable_const.mul h2
    have h4 : Measurable fun z : ℝ × ℝ => kappa e * (2 * (z.2 : ℂ)) *
        (timeT m mγ 0 x.1 x.2 μ i j z v - timeT m Λ 0 x.1 x.2 μ i j z v) :=
      h3.mul ((hT mγ).sub (hT Λ))
    exact h4.aestronglyMeasurable
  · refine hgood.mono fun x hx => ae_feynmanMeasure.mono fun z hz => ?_
    have hzI := Ioc_prod_subset hz
    have hb := hCb x.1 x.2 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 0 le_rfl z hzI v
    have hu : (1 + ‖v‖) ^ (-(5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg v]) (by norm_num)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hz.2.1]
    calc ‖kappa e‖ * (2 * z.2) *
          ‖timeT m mγ 0 x.1 x.2 μ i j z v - timeT m Λ 0 x.1 x.2 μ i j z v‖
        ≤ ‖kappa e‖ * (2 * 1) * (Cb * 1) := by
          gcongr
          · exact hz.2.2
          · exact hb.trans (mul_le_mul_of_nonneg_left hu hCb0)
      _ = ‖kappa e‖ * 2 * Cb := by ring
  · refine ae_feynmanMeasure.mono fun z hz => ?_
    have hzI := Ioc_prod_subset hz
    exact continuousAt_const.mul
      ((continuousAt_timeT_zero μ i j (massW_pos hm hmγ hp' hp hp0' hp0 hzI v)).sub
        (continuousAt_timeT_zero μ i j (massW_pos hm hΛ hp' hp hp0' hp0 hzI v)))

/-- The closed form `∫ v, spatialG 0 r' r v` of the limit is continuous in the momenta at an
on-shell point. -/
theorem continuousAt_integral_spatialG_zero (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ContinuousAt
      (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => ∫ v, spatialG e m mγ Λ 0 x.1 x.2 μ i j v)
      (p', p) := by
  obtain ⟨C, hC⟩ := exists_norm_spatialG_le_uniform e m mγ Λ μ i j
    (offShellMass_pos hm hmγ hΛ) (‖p'‖ + ‖p‖ + 1)
  refine continuousAt_of_dominated (bound := fun v => C * (1 + ‖v‖) ^ (-(5 : ℝ)))
    (Eventually.of_forall fun x =>
      (stronglyMeasurable_spatialG e m mγ Λ 0 x.1 x.2 μ i j).aestronglyMeasurable)
    ((eventually_offShell_good hm hmγ hΛ hp' hp hp0' hp0).mono fun x hx =>
      Eventually.of_forall fun v => hC x.1 x.2 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 0 le_rfl v)
    ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
      (by simp; norm_num)).const_mul C)
    (Eventually.of_forall fun v => continuousAt_spatialG_zero hm hmγ hΛ hp' hp hp0' hp0 μ i j v)

end NearShell

/-! ### The main statement -/

/-- **The one-loop vertex limit off the mass shell.** Near on-shell positive-energy momenta
`(p', p)`, the energy-first integral of each entry of the regulated one-loop vertex integrand
has a limit `V r' r` as `ε → 0⁺` at every pair of momenta `(r', r)` within `δ` of `(p', p)`
(on shell or not), and `V` is continuous at `(p', p)`. Here `V r' r = ∫ v, spatialG 0 r' r v`. -/
theorem exists_tendsto_vertexIntegral_offShell {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ∃ δ > 0, ∃ V : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℂ,
      (∀ r' r : Fin 4 → ℝ, dist r' p' < δ → dist r p < δ →
        Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun ℓ =>
            QED.OneLoop.vertexIntegrand e m mγ Λ ε r' r μ ℓ i j) (𝓝[>] 0) (𝓝 (V r' r))) ∧
      ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => V x.1 x.2) (p', p) := by
  have hlim := eventually_tendsto_energyFirstIntegral (e := e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hlim
  have hcont := continuousAt_integral_spatialG_zero (e := e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  refine ⟨δ, hδ, fun r' r => ∫ v, spatialG e m mγ Λ 0 r' r μ i j v, ?_, ?_⟩
  · intro r' r hr' hr
    have hd : dist (r', r) (p', p) < δ := by
      rw [Prod.dist_eq]
      exact max_lt hr' hr
    have h := hball hd
    exact h
  · exact hcont

end QED.OneLoop.VertexOffShell

end
