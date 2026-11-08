/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexIntegrand
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import QED.OneLoop.VertexAlgebra
public import QED.Integration.FeynmanParameter
public import QED.Integration.ShiftedEnergyIntegral
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.Basic
import QED.Integration.LoopBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The energy-first integral of the one-loop vertex

Analytic machinery for the frozen integrand `QED.OneLoop.vertexIntegrand` of the primary source's
(62.40) under prescription M1 (decision D-5). It proves the facts behind the frozen theorem (E),
`QED.OneLoop.vertexLimit_existsUnique`, and exposes the limit in a form used to evaluate the
one-loop vertex in closed form.

Fix the parameters and one matrix entry. For `ε > 0` and spatial loop momentum `v`:

1. The integrand factors as `κ N(ℓ) [(A B C_γ)⁻¹ - (A B C_Λ)⁻¹]`, where `N` is the Dirac
   numerator and `A, B, C_M` are the propagator denominators (`vertexIntegrand_apply`). Each
   triple product is a Feynman-parameter integral over the unit square
   (`inv_mul_mul_eq_integral_feynmanMeasure`), whose combined denominator is
   `-(t + a)² + W - iε` after completing the square (`combDen_cons`).
2. The integrand is jointly integrable on `ℝ × [0,1]²` (`integrable_jointF`), so the energy
   integral and the Feynman integral can be swapped. The energy integral is then evaluated in
   closed form (`integral_quadratic_mul_shifted`), giving `spatialG ε v`
   (`integral_vertexIntegrand_time`).
3. The Pauli–Villars difference is bounded by `C (1 + ‖v‖)⁻⁵` uniformly in `ε > 0`
   (`norm_timeT_sub_le`). This bound uses the positivity of the Feynman mass term, which
   needs `m_γ > 0` and the on-shell premises.
4. Dominated convergence, first over the Feynman parameters and then over `v`, gives the limit
   `ε → 0⁺` of the energy-first integral: `∫ v, spatialG 0 v`
   (`tendsto_energyFirstIntegral_vertexIntegrand`).

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-! ### Notation for the proof -/

/-- The overall constant of the (62.40) integrand. -/
noncomputable def kappa (e : ℝ) : ℂ :=
  (I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

/-- The Feynman shift `K = y (x p' + (1 - x) p)` at parameters `z = (x, y)`. -/
noncomputable def shiftK (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) : Fin 4 → ℝ :=
  z.2 • (z.1 • p' + (1 - z.1) • p)

/-- The spatial mass term `W = Σₖ (vₖ + K_{k+1})² + D` after completing the square. -/
noncomputable def massW (m M : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ k : Fin 3, (v k + shiftK p' p z k.succ) ^ 2 + feynmanMass m M z.1 z.2 p' p

/-- The Feynman-combined denominator of one Pauli–Villars term. -/
noncomputable def combDen (m M ε : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  (z.2 : ℂ) * ((z.1 : ℂ) * denom m ε (p' + ℓ) + (1 - z.1) * denom m ε (p + ℓ))
    + (1 - z.2) * denom M ε ℓ

/-- The leading coefficient of the numerator in the loop energy. -/
noncomputable def alphaN (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) : ℂ :=
  Classical.choose (exists_vertexNumerator_quadratic m p' p μ i j)

theorem vertexNumerator_cons (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (v : Fin 3 → ℝ) :
    ∃ β γ : ℂ, ∀ t : ℝ, vertexNumerator m p' p μ (Fin.cons t v : Fin 4 → ℝ) i j
      = alphaN m p' p μ i j * (t : ℂ) ^ 2 + β * t + γ :=
  Classical.choose_spec (exists_vertexNumerator_quadratic m p' p μ i j) v

/-- The closed-form energy integral of one Pauli–Villars term. -/
noncomputable def timeT (m M ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (z : ℝ × ℝ)
    (v : Fin 3 → ℝ) : ℂ :=
  -((π / 8 : ℂ) * alphaN m p' p μ i j * (-(massW m M p' p z v : ℂ) + ε * I) ^ (-(3 / 2 : ℂ)))
    - (3 * π / 8 : ℂ) * vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j
      * (-(massW m M p' p z v : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))

/-- The energy integral of the integrand, after the Feynman-parameter integral. -/
noncomputable def spatialG (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (v : Fin 3 → ℝ) : ℂ :=
  ∫ z, kappa e * (2 * (z.2 : ℂ)) *
    (timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v) ∂feynmanMeasure

/-- The integrand on `ℝ × [0,1]²` at fixed `ε` and spatial momentum `v`. -/
noncomputable def jointF (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (v : Fin 3 → ℝ)
    (q : ℝ × (ℝ × ℝ)) : ℂ :=
  kappa e * vertexNumerator m p' p μ (Fin.cons q.1 v : Fin 4 → ℝ) i j *
    (2 * (q.2.2 : ℂ) * combDen m mγ ε p' p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) ^ (-3 : ℤ)
      - 2 * (q.2.2 : ℂ) * combDen m Λ ε p' p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) ^ (-3 : ℤ))

/-! ### Elementary facts -/

theorem im_ofReal_sub_mul_I (r ε : ℝ) : ((r : ℂ) - (ε : ℂ) * I).im = -ε := by
  simp only [Complex.sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
  ring

theorem neg_sq_add_eq (t a W ε : ℝ) :
    -((t : ℂ) + a) ^ 2 + ((W : ℂ) - (ε : ℂ) * I) = ((-(t + a) ^ 2 + W : ℝ) : ℂ) - (ε : ℂ) * I := by
  push_cast; ring

theorem continuous_dot_comp {X : Type*} [TopologicalSpace X] {f g : X → Fin 4 → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => Minkowski.dot (f x) (g x) := by
  unfold Minkowski.dot
  refine continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun ν _ => ?_
  exact (continuous_const.mul ((continuous_apply μ).comp hf)).mul ((continuous_apply ν).comp hg)

theorem continuous_shiftK (p' p : Fin 4 → ℝ) : Continuous (shiftK p' p) := by
  unfold shiftK; fun_prop

theorem continuous_feynmanMass (m M : ℝ) (p' p : Fin 4 → ℝ) :
    Continuous fun z : ℝ × ℝ => feynmanMass m M z.1 z.2 p' p := by
  have h := continuous_dot_comp (continuous_shiftK p' p) (continuous_shiftK p' p)
  unfold shiftK at h
  unfold feynmanMass
  fun_prop

theorem continuous_massW (m M : ℝ) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Continuous fun z => massW m M p' p z v := by
  unfold massW
  refine continuous_finsetSum _ (fun k _ => ?_) |>.add (continuous_feynmanMass m M p' p)
  exact (continuous_const.add ((continuous_apply k.succ).comp (continuous_shiftK p' p))).pow 2

theorem norm_shiftK_le (p' p : Fin 4 → ℝ) {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ‖shiftK p' p z‖ ≤ ‖p'‖ + ‖p‖ := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
  unfold shiftK
  calc ‖z.2 • (z.1 • p' + (1 - z.1) • p)‖ = |z.2| * ‖z.1 • p' + (1 - z.1) • p‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * (|z.1| * ‖p'‖ + |1 - z.1| * ‖p‖) := by
        gcongr
        · rw [abs_of_nonneg hy0]; exact hy1
        · refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖p'‖ + ‖p‖ := by
        rw [abs_of_nonneg hx0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.1), one_mul]
        nlinarith [norm_nonneg p', norm_nonneg p]

theorem feynmanMass_sub (m M₁ M₂ x y : ℝ) (p' p : Fin 4 → ℝ) :
    feynmanMass m M₁ x y p' p - feynmanMass m M₂ x y p' p = (1 - y) * (M₁ ^ 2 - M₂ ^ 2) := by
  unfold feynmanMass; ring

/-- Completing the square in the Feynman-combined denominator. -/
theorem combDen_cons (m M ε : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    combDen m M ε p' p z (Fin.cons t v : Fin 4 → ℝ) =
      -((t : ℂ) + shiftK p' p z 0) ^ 2 + ((massW m M p' p z v : ℂ) - (ε : ℂ) * I) := by
  rw [combDen, feynman_combination, dot_cons_add, neg_sq_add_eq]
  congr 2
  simp only [massW, shiftK]
  ring

theorem combDen_cons_im (m M ε : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    (combDen m M ε p' p z (Fin.cons t v : Fin 4 → ℝ)).im = -ε := by
  rw [combDen_cons, neg_sq_add_eq, im_ofReal_sub_mul_I]

theorem combDen_cons_ne_zero {ε : ℝ} (hε : ε ≠ 0) (m M : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ)
    (t : ℝ) (v : Fin 3 → ℝ) : combDen m M ε p' p z (Fin.cons t v : Fin 4 → ℝ) ≠ 0 := by
  intro h
  have := combDen_cons_im m M ε p' p z t v
  rw [h, zero_im] at this
  exact hε (by linarith)

theorem mem_slitPlane_neg_add_mul_I {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    -(W : ℂ) + ε * I ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simp [hε.ne']

theorem continuous_combDen_cons {ε : ℝ} (m M : ℝ) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Continuous fun q : ℝ × (ℝ × ℝ) => combDen m M ε p' p q.2 (Fin.cons q.1 v : Fin 4 → ℝ) := by
  simp_rw [combDen_cons]
  have h1 := (continuous_apply 0).comp ((continuous_shiftK p' p).comp
    (continuous_snd : Continuous fun q : ℝ × (ℝ × ℝ) => q.2))
  have h2 := (continuous_massW m M p' p v).comp
    (continuous_snd : Continuous fun q : ℝ × (ℝ × ℝ) => q.2)
  simp only [Function.comp_def] at h1 h2
  fun_prop

theorem continuous_vertexNumerator_cons (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (v : Fin 3 → ℝ) {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    Continuous fun x => vertexNumerator m p' p μ (Fin.cons (f x) v : Fin 4 → ℝ) i j :=
  (continuous_vertexNumerator m p' p μ i j).comp (hf.finCons continuous_const)

/-! ### Step 1: Feynman parameters -/

theorem vertexIntegrand_eq_integral_jointF {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (t : ℝ) (v : Fin 3 → ℝ) :
    vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j =
      ∫ z, jointF e m mγ Λ ε p' p μ i j v (t, z) ∂feynmanMeasure := by
  set ℓ : Fin 4 → ℝ := Fin.cons t v
  have hA : (denom m ε (p' + ℓ)).im < 0 := by rw [denom_im]; linarith
  have hB : (denom m ε (p + ℓ)).im < 0 := by rw [denom_im]; linarith
  have hγ : (denom mγ ε ℓ).im < 0 := by rw [denom_im]; linarith
  have hΛ : (denom Λ ε ℓ).im < 0 := by rw [denom_im]; linarith
  have key : ((denom mγ ε ℓ)⁻¹ - (denom Λ ε ℓ)⁻¹) * (denom m ε (p' + ℓ))⁻¹
        * (denom m ε (p + ℓ))⁻¹
      = (denom m ε (p' + ℓ) * denom m ε (p + ℓ) * denom mγ ε ℓ)⁻¹
        - (denom m ε (p' + ℓ) * denom m ε (p + ℓ) * denom Λ ε ℓ)⁻¹ := by
    simp only [mul_inv]; ring
  rw [vertexIntegrand_apply, key, inv_mul_mul_eq_integral_feynmanMeasure hA hB hγ,
    inv_mul_mul_eq_integral_feynmanMeasure hA hB hΛ,
    ← integral_sub (integrable_feynmanMeasure_three hA hB hγ)
      (integrable_feynmanMeasure_three hA hB hΛ),
    ← integral_const_mul, ← integral_mul_const]
  congr 1
  ext z
  simp only [jointF, combDen, kappa, ℓ]
  ring

/-! ### Step 2: joint integrability and the closed-form energy integral -/

theorem volume_prod_feynmanMeasure :
    (volume : Measure ℝ).prod feynmanMeasure
      = ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))).restrict
          (univ ×ˢ (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)) := by
  rw [feynmanMeasure_eq, ← Measure.prod_restrict, Measure.restrict_univ]

theorem ae_volume_prod_feynmanMeasure :
    ∀ᵐ q ∂(volume : Measure ℝ).prod feynmanMeasure, q.2 ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
  rw [volume_prod_feynmanMeasure]
  exact ae_restrict_of_forall_mem
    (MeasurableSet.univ.prod (measurableSet_Ioc.prod measurableSet_Ioc)) fun q hq => hq.2

theorem ae_feynmanMeasure :
    ∀ᵐ z ∂feynmanMeasure, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
  rw [feynmanMeasure_eq]
  exact ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun z hz => hz

theorem Ioc_prod_subset :
    Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
  prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self

/-- Norm bound for one Feynman-weighted denominator. -/
theorem norm_two_mul_zpow_le {y c s : ℝ} {Z : ℂ} (hy : y ∈ Ioc (0 : ℝ) 1) (hc : 0 < c)
    (hs : 0 ≤ s) (hZ : c * (1 + s) ≤ ‖Z‖) :
    ‖2 * (y : ℂ) * Z ^ (-3 : ℤ)‖ ≤ 2 * (c ^ 3)⁻¹ * ((1 + s) ^ 2)⁻¹ := by
  have h1 : 0 < c * (1 + s) := by positivity
  have hZ0 : 0 < ‖Z‖ := h1.trans_le hZ
  rw [norm_mul, norm_mul, norm_zpow, zpow_neg, zpow_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hy.1, Complex.norm_ofNat]
  have h3 : ((c * (1 + s)) ^ 3)⁻¹ ≥ (‖Z‖ ^ 3)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le hZ 3)
  have h4 : ((c * (1 + s)) ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ * ((1 + s) ^ 2)⁻¹ := by
    rw [mul_pow, mul_inv]
    have h5 : ((1 + s) ^ 3)⁻¹ ≤ ((1 + s) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
    exact mul_le_mul_of_nonneg_left h5 (by positivity)
  calc 2 * y * (‖Z‖ ^ 3)⁻¹ ≤ 2 * 1 * ((c * (1 + s)) ^ 3)⁻¹ := by
        gcongr
        · exact hy.2
    _ ≤ 2 * (c ^ 3)⁻¹ * ((1 + s) ^ 2)⁻¹ := by rw [mul_one, mul_assoc]; gcongr

theorem continuous_jointF {ε : ℝ} (hε : ε ≠ 0) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (v : Fin 3 → ℝ) : Continuous (jointF e m mγ Λ ε p' p μ i j v) := by
  unfold jointF
  have hN := continuous_vertexNumerator_cons m p' p μ i j v
    (continuous_fst : Continuous fun q : ℝ × (ℝ × ℝ) => q.1)
  have hγ := (continuous_combDen_cons (ε := ε) m mγ p' p v).zpow₀ (-3)
    fun q => Or.inl (combDen_cons_ne_zero hε m mγ p' p q.2 q.1 v)
  have hΛ := (continuous_combDen_cons (ε := ε) m Λ p' p v).zpow₀ (-3)
    fun q => Or.inl (combDen_cons_ne_zero hε m Λ p' p q.2 q.1 v)
  fun_prop

theorem integrable_jointF {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (v : Fin 3 → ℝ) :
    Integrable (jointF e m mγ Λ ε p' p μ i j v) ((volume : Measure ℝ).prod feynmanMeasure) := by
  obtain ⟨CN, hCN⟩ := exists_norm_vertexNumerator_le m p' p μ i j
  have hCN0 : 0 ≤ CN := by
    have := hCN 0
    have h1 : 0 < (1 + ‖(0 : Fin 4 → ℝ)‖) ^ 2 := by positivity
    by_contra h
    nlinarith [norm_nonneg (vertexNumerator m p' p μ 0 i j), not_le.mp h]
  obtain ⟨Cγ, hCγ⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuous_massW m mγ p' p v).continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  obtain ⟨CΛ, hCΛ⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuous_massW m Λ p' p v).continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε (‖p'‖ + ‖p‖) (max Cγ CΛ)
  set G : ℝ := ‖kappa e‖ * (CN * (2 * (1 + ‖v‖) ^ 2)) * (2 * (2 * (c ^ 3)⁻¹))
  refine Integrable.mono' (g := fun q : ℝ × (ℝ × ℝ) => G * (1 + q.1 ^ 2)⁻¹ * 1) ?_
    (continuous_jointF hε.ne' e m mγ Λ p' p μ i j v).aestronglyMeasurable
    (ae_volume_prod_feynmanMeasure.mono fun q hq => ?_)
  · exact (integrable_inv_one_add_sq.const_mul G).mul_prod (integrable_const (1 : ℝ))
  obtain ⟨t, z⟩ := q
  simp only at hq ⊢
  have hzI : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := Ioc_prod_subset hq
  have ha : |shiftK p' p z 0| ≤ ‖p'‖ + ‖p‖ :=
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm (shiftK p' p z) 0).trans (norm_shiftK_le p' p hzI)
  have hZ : ∀ M, massW m M p' p z v ≤ max Cγ CΛ →
      c * (1 + t ^ 2) ≤ ‖combDen m M ε p' p z (Fin.cons t v : Fin 4 → ℝ)‖ := by
    intro M hM
    rw [combDen_cons, ← add_sub_assoc]
    exact hcb t _ _ ha hM
  have hWγ : massW m mγ p' p z v ≤ max Cγ CΛ :=
    ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hCγ z hzI)).trans (le_max_left _ _)
  have hWΛ : massW m Λ p' p z v ≤ max Cγ CΛ :=
    ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hCΛ z hzI)).trans (le_max_right _ _)
  have hy : z.2 ∈ Ioc (0 : ℝ) 1 := hq.2
  have hb1 := norm_two_mul_zpow_le hy hc (sq_nonneg t) (hZ mγ hWγ)
  have hb2 := norm_two_mul_zpow_le hy hc (sq_nonneg t) (hZ Λ hWΛ)
  have hN : ‖vertexNumerator m p' p μ (Fin.cons t v : Fin 4 → ℝ) i j‖
      ≤ CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2) := by
    refine (hCN _).trans ?_
    have h1 := norm_finCons_le t v
    have h2 : (1 + ‖(Fin.cons t v : Fin 4 → ℝ)‖) ^ 2 ≤ 2 * (1 + ‖v‖) ^ 2 * (1 + t ^ 2) := by
      have h3 : (1 + ‖(Fin.cons t v : Fin 4 → ℝ)‖) ^ 2 ≤ (1 + (|t| + ‖v‖)) ^ 2 := by
        gcongr
      have h4 : |t| ^ 2 = t ^ 2 := sq_abs t
      have h5 : 1 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg v]
      nlinarith [norm_nonneg v, abs_nonneg t, sq_nonneg (1 + ‖v‖ - |t|),
        mul_nonneg (sq_nonneg t) (sub_nonneg.2 h5)]
    calc CN * (1 + ‖(Fin.cons t v : Fin 4 → ℝ)‖) ^ 2
        ≤ CN * (2 * (1 + ‖v‖) ^ 2 * (1 + t ^ 2)) := by gcongr
      _ = CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2) := by ring
  have h1t : 0 < 1 + t ^ 2 := by positivity
  rw [jointF, norm_mul, norm_mul, mul_one]
  calc ‖kappa e‖ * ‖vertexNumerator m p' p μ (Fin.cons t v : Fin 4 → ℝ) i j‖ *
        ‖2 * (z.2 : ℂ) * combDen m mγ ε p' p z (Fin.cons t v : Fin 4 → ℝ) ^ (-3 : ℤ)
          - 2 * (z.2 : ℂ) * combDen m Λ ε p' p z (Fin.cons t v : Fin 4 → ℝ) ^ (-3 : ℤ)‖
      ≤ ‖kappa e‖ * (CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2)) *
        (2 * (c ^ 3)⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹ + 2 * (c ^ 3)⁻¹ * ((1 + t ^ 2) ^ 2)⁻¹) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)
    _ = G * (1 + t ^ 2)⁻¹ := by
        simp only [G]; field_simp; ring

theorem integrable_numerator_mul_combDen {ε : ℝ} (hε : 0 < ε) (m M : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (z : ℝ × ℝ) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => vertexNumerator m p' p μ (Fin.cons t v : Fin 4 → ℝ) i j *
      combDen m M ε p' p z (Fin.cons t v : Fin 4 → ℝ) ^ (-3 : ℤ) := by
  obtain ⟨β, γ, h⟩ := vertexNumerator_cons m p' p μ i j v
  have hw : -((massW m M p' p z v : ℂ) - (ε : ℂ) * I) ∈ slitPlane := by
    rw [neg_sub', sub_neg_eq_add]
    exact mem_slitPlane_neg_add_mul_I hε _
  simp_rw [h, combDen_cons]
  exact integrable_quadratic_mul_shifted hw _ _ _ _

theorem integral_numerator_mul_combDen {ε : ℝ} (hε : 0 < ε) (m M : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (z : ℝ × ℝ) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, vertexNumerator m p' p μ (Fin.cons t v : Fin 4 → ℝ) i j *
      combDen m M ε p' p z (Fin.cons t v : Fin 4 → ℝ) ^ (-3 : ℤ) = timeT m M ε p' p μ i j z v := by
  obtain ⟨β, γ, h⟩ := vertexNumerator_cons m p' p μ i j v
  have hw : -((massW m M p' p z v : ℂ) - (ε : ℂ) * I) ∈ slitPlane := by
    rw [neg_sub', sub_neg_eq_add]
    exact mem_slitPlane_neg_add_mul_I hε _
  simp_rw [h, combDen_cons]
  rw [integral_quadratic_mul_shifted hw, timeT, h]
  have hneg : -((massW m M p' p z v : ℂ) - (ε : ℂ) * I) = -(massW m M p' p z v : ℂ) + ε * I := by
    ring
  rw [hneg]
  push_cast
  ring

/-- The energy integral of the integrand equals `spatialG`. -/
theorem integral_vertexIntegrand_time {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j
      = spatialG e m mγ Λ ε p' p μ i j v := by
  simp_rw [vertexIntegrand_eq_integral_jointF hε]
  rw [integral_integral_swap (f := fun t z => jointF e m mγ Λ ε p' p μ i j v (t, z))
    (integrable_jointF hε e m mγ Λ p' p μ i j v)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  have hpt : ∀ t : ℝ, jointF e m mγ Λ ε p' p μ i j v (t, z) =
      kappa e * (2 * (z.2 : ℂ)) *
        (vertexNumerator m p' p μ (Fin.cons t v : Fin 4 → ℝ) i j *
            combDen m mγ ε p' p z (Fin.cons t v : Fin 4 → ℝ) ^ (-3 : ℤ)
          - vertexNumerator m p' p μ (Fin.cons t v : Fin 4 → ℝ) i j *
            combDen m Λ ε p' p z (Fin.cons t v : Fin 4 → ℝ) ^ (-3 : ℤ)) := by
    intro t; simp only [jointF]; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub (integrable_numerator_mul_combDen hε m mγ p' p μ i j z v)
    (integrable_numerator_mul_combDen hε m Λ p' p μ i j z v),
    integral_numerator_mul_combDen hε, integral_numerator_mul_combDen hε]

/-! ### Step 3: the uniform Pauli–Villars bound -/

theorem norm_ofReal_div_eight_pi : ‖(π / 8 : ℂ)‖ = π / 8 := by
  rw [show (π / 8 : ℂ) = ((π / 8 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem norm_ofReal_three_div_eight_pi : ‖(3 * π / 8 : ℂ)‖ = 3 * π / 8 := by
  rw [show (3 * π / 8 : ℂ) = ((3 * π / 8 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem nonneg_of_norm_le_mul_sq {f : (Fin 4 → ℝ) → ℂ} {C : ℝ}
    (h : ∀ ℓ, ‖f ℓ‖ ≤ C * (1 + ‖ℓ‖) ^ 2) : 0 ≤ C := by
  have h0 := h 0
  have h1 : 0 < (1 + ‖(0 : Fin 4 → ℝ)‖) ^ 2 := by positivity
  by_contra hC
  nlinarith [norm_nonneg (f 0), not_le.mp hC]

/-- `(c u²)^{-(s + 1)} = c^{-(s+1)} u^{-(2s + 2)}`, in the form used below. -/
theorem rpow_mul_sq_neg {c u r : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) :
    (c * u ^ 2) ^ (-r) = c ^ (-r) * u ^ (-(2 * r)) := by
  rw [Real.mul_rpow hc (by positivity), ← Real.rpow_natCast u 2, ← Real.rpow_mul hu]
  congr 2
  push_cast; ring

/-- The Pauli–Villars difference of the closed-form energy integrals decays like `‖v‖⁻⁵`,
uniformly in `ε > 0` and in the Feynman parameters. -/
theorem norm_timeT_sub_le {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ∃ Cb : ℝ, ∀ ε > 0, ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
        ≤ Cb * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  obtain ⟨CN, hCN⟩ := exists_norm_vertexNumerator_le m p' p μ i j
  have hCN0 : 0 ≤ CN := nonneg_of_norm_le_mul_sq hCN
  set c0 : ℝ := 3 / 4 * min (min (mγ ^ 2) (Λ ^ 2)) (m ^ 2) with hc0_def
  have hc0 : 0 < c0 := by positivity
  set A0 : ℝ := ‖p'‖ + ‖p‖ with hA0_def
  have hA0 : 0 ≤ A0 := by positivity
  obtain ⟨c1, hc1, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) A0 hc0
  set α : ℂ := alphaN m p' p μ i j
  set L : ℝ := mγ ^ 2 + Λ ^ 2
  refine ⟨π / 8 * ‖α‖ * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ)))
      + 3 * π / 8 * (CN * (1 + A0) ^ 2) * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ))),
    fun ε hε z hz v => ?_⟩
  set u : ℝ := 1 + ‖v‖ with hu_def
  have hu1 : 1 ≤ u := by simp only [u]; linarith [norm_nonneg v]
  have hu0 : 0 ≤ u := by linarith
  set Wγ : ℝ := massW m mγ p' p z v
  set WΛ : ℝ := massW m Λ p' p z v
  have hDγ : c0 ≤ feynmanMass m mγ z.1 z.2 p' p := by
    refine le_trans ?_ (feynmanMass_pos hp' hp hp0' hp0 hz.1 hz.2)
    simp only [c0]
    gcongr
    exact min_le_left _ _
  have hDΛ : c0 ≤ feynmanMass m Λ z.1 z.2 p' p := by
    refine le_trans ?_ (feynmanMass_pos hp' hp hp0' hp0 hz.1 hz.2)
    simp only [c0]
    gcongr
    exact min_le_right _ _
  have hb : ‖(fun k : Fin 3 => shiftK p' p z k.succ)‖ ≤ A0 :=
    (pi_norm_le_iff_of_nonneg hA0).2 fun k =>
      (norm_le_pi_norm (shiftK p' p z) k.succ).trans (norm_shiftK_le p' p hz)
  have hWγ : c1 * u ^ 2 ≤ Wγ := hcoer v _ _ hb hDγ
  have hWΛ : c1 * u ^ 2 ≤ WΛ := hcoer v _ _ hb hDΛ
  have hpos : 0 < c1 * u ^ 2 := by positivity
  have hWγ0 : 0 < Wγ := hpos.trans_le hWγ
  have hWΛ0 : 0 < WΛ := hpos.trans_le hWΛ
  have hmin : c1 * u ^ 2 ≤ min Wγ WΛ := le_min hWγ hWΛ
  have hΔ : |Wγ - WΛ| ≤ L := by
    have h : Wγ - WΛ = (1 - z.2) * (mγ ^ 2 - Λ ^ 2) := by
      simp only [Wγ, WΛ, massW]
      rw [← feynmanMass_sub m mγ Λ z.1 z.2 p' p]
      ring
    have hy0 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
    have hy1 : 1 - z.2 ≤ 1 := by linarith [hz.2.1]
    rw [h, abs_mul, abs_of_nonneg hy0]
    have : |mγ ^ 2 - Λ ^ 2| ≤ L := by
      simp only [L]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg mγ, sq_nonneg Λ]
    nlinarith [abs_nonneg (mγ ^ 2 - Λ ^ 2)]
  have hs32 : (-(((3 / 2 : ℝ)) : ℂ)) = -(3 / 2 : ℂ) := by push_cast; ring
  have hs52 : (-(((5 / 2 : ℝ)) : ℂ)) = -(5 / 2 : ℂ) := by push_cast; ring
  have l1 := norm_cpow_sub_cpow_le (s := 3 / 2) hWγ0 hWΛ0 hε (by norm_num)
  have l2 := norm_cpow_sub_cpow_le (s := 5 / 2) hWγ0 hWΛ0 hε (by norm_num)
  rw [hs32] at l1
  rw [hs52] at l2
  have r1 : (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ)) ≤ c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by
    calc (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ)) ≤ (c1 * u ^ 2) ^ (-(3 / 2 + 1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hmin (by norm_num)
      _ = c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by
          rw [rpow_mul_sq_neg hc1.le hu0]; norm_num
  have r2 : (min Wγ WΛ) ^ (-(5 / 2 + 1 : ℝ)) ≤ c1 ^ (-(5 / 2 + 1 : ℝ)) * u ^ (-(7 : ℝ)) := by
    calc (min Wγ WΛ) ^ (-(5 / 2 + 1 : ℝ)) ≤ (c1 * u ^ 2) ^ (-(5 / 2 + 1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hmin (by norm_num)
      _ = c1 ^ (-(5 / 2 + 1 : ℝ)) * u ^ (-(7 : ℝ)) := by
          rw [rpow_mul_sq_neg hc1.le hu0]; norm_num
  have hNt : ‖vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j‖
      ≤ CN * (1 + A0) ^ 2 * u ^ 2 := by
    refine (hCN _).trans ?_
    have ha : |-shiftK p' p z 0| ≤ A0 := by
      rw [abs_neg]
      exact (Real.norm_eq_abs _ ▸ norm_le_pi_norm (shiftK p' p z) 0).trans
        (norm_shiftK_le p' p hz)
    have h1 := norm_finCons_le (-shiftK p' p z 0) v
    have h2 : 1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ ≤ (1 + A0) * u := by
      simp only [u]; nlinarith [norm_nonneg v]
    calc CN * (1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖) ^ 2
        ≤ CN * ((1 + A0) * u) ^ 2 := by gcongr
      _ = CN * (1 + A0) ^ 2 * u ^ 2 := by ring
  have hu5 : u ^ 2 * u ^ (-(7 : ℝ)) = u ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_add (by linarith)]
    norm_num
  have hsplit : timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v
      = -((π / 8 : ℂ) * α * ((-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
          - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))))
        - (3 * π / 8 : ℂ)
          * vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j
          * ((-(Wγ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))) := by
    simp only [timeT, Wγ, WΛ, α]
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_mul, norm_ofReal_div_eight_pi,
    norm_ofReal_three_div_eight_pi]
  have t1 : π / 8 * ‖α‖ * ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
        - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
      ≤ π / 8 * ‖α‖ * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ)) := by
    calc π / 8 * ‖α‖ * ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
          - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
        ≤ π / 8 * ‖α‖ * (3 / 2 * |Wγ - WΛ| * (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ))) := by
          gcongr
      _ ≤ π / 8 * ‖α‖ * (3 / 2 * L * (c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)))) := by
          gcongr
      _ = π / 8 * ‖α‖ * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ)) := by ring
  have t2 : 3 * π / 8
        * ‖vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j‖
        * ‖(-(Wγ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))‖
      ≤ 3 * π / 8 * (CN * (1 + A0) ^ 2) * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ)))
        * u ^ (-(5 : ℝ)) := by
    calc 3 * π / 8
          * ‖vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j‖
          * ‖(-(Wγ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))‖
        ≤ 3 * π / 8 * (CN * (1 + A0) ^ 2 * u ^ 2)
          * (5 / 2 * |Wγ - WΛ| * (min Wγ WΛ) ^ (-(5 / 2 + 1 : ℝ))) := by
          gcongr
      _ ≤ 3 * π / 8 * (CN * (1 + A0) ^ 2 * u ^ 2)
          * (5 / 2 * L * (c1 ^ (-(5 / 2 + 1 : ℝ)) * u ^ (-(7 : ℝ)))) := by
          gcongr
      _ = 3 * π / 8 * (CN * (1 + A0) ^ 2) * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ)))
          * (u ^ 2 * u ^ (-(7 : ℝ))) := by ring
      _ = 3 * π / 8 * (CN * (1 + A0) ^ 2) * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ)))
          * u ^ (-(5 : ℝ)) := by rw [hu5]
  calc π / 8 * ‖α‖ * ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
          - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
        + 3 * π / 8
          * ‖vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j‖
          * ‖(-(Wγ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))‖
      ≤ π / 8 * ‖α‖ * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ))
        + 3 * π / 8 * (CN * (1 + A0) ^ 2) * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ)))
          * u ^ (-(5 : ℝ)) := add_le_add t1 t2
    _ = _ := by ring

/-! ### Step 4: dominated convergence -/

theorem massW_pos {m M : ℝ} (hm : 0 < m) (hM : 0 < M) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (v : Fin 3 → ℝ) :
    0 < massW m M p' p z v := by
  have h1 := feynmanMass_pos (M := M) hp' hp hp0' hp0 hz.1 hz.2
  have h2 : 0 < 3 / 4 * min (M ^ 2) (m ^ 2) := by positivity
  have h3 : 0 ≤ ∑ k : Fin 3, (v k + shiftK p' p z k.succ) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  simp only [massW]
  linarith

theorem continuous_timeT {ε : ℝ} (hε : 0 < ε) (m M : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (v : Fin 3 → ℝ) : Continuous fun z => timeT m M ε p' p μ i j z v := by
  unfold timeT
  have hW := continuous_massW m M p' p v
  have hX : Continuous fun z => (-(massW m M p' p z v : ℂ) + ε * I) := by fun_prop
  have h32 := hX.cpow (continuous_const (y := -(3 / 2 : ℂ)))
    (fun z => mem_slitPlane_neg_add_mul_I hε _)
  have h52 := hX.cpow (continuous_const (y := -(5 / 2 : ℂ)))
    (fun z => mem_slitPlane_neg_add_mul_I hε _)
  have ha : Continuous fun z : ℝ × ℝ => -shiftK p' p z 0 :=
    ((continuous_apply 0).comp (continuous_shiftK p' p)).neg
  have hN := continuous_vertexNumerator_cons m p' p μ i j v ha
  fun_prop

theorem tendsto_timeT {m M : ℝ} {p' p : Fin 4 → ℝ} (μ i j : Fin 4) {z : ℝ × ℝ}
    {v : Fin 3 → ℝ} (hW : 0 < massW m M p' p z v) :
    Tendsto (fun ε : ℝ => timeT m M ε p' p μ i j z v) (𝓝[>] 0)
      (𝓝 (timeT m M 0 p' p μ i j z v)) := by
  have h0 : timeT m M 0 p' p μ i j z v =
      -((π / 8 : ℂ) * alphaN m p' p μ i j * (-(massW m M p' p z v : ℂ)) ^ (-(3 / 2 : ℂ)))
        - (3 * π / 8 : ℂ)
          * vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j
          * (-(massW m M p' p z v : ℂ)) ^ (-(5 / 2 : ℂ)) := by
    simp only [timeT, ofReal_zero, zero_mul, add_zero]
  rw [h0]
  unfold timeT
  exact (((tendsto_cpow_neg_add_mul_I hW _).const_mul _).neg).sub
    ((tendsto_cpow_neg_add_mul_I hW _).const_mul _)

theorem tendsto_spatialG {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) (v : Fin 3 → ℝ) :
    Tendsto (fun ε : ℝ => spatialG e m mγ Λ ε p' p μ i j v) (𝓝[>] 0)
      (𝓝 (spatialG e m mγ Λ 0 p' p μ i j v)) := by
  obtain ⟨Cb, hCb⟩ := norm_timeT_sub_le hm hmγ hΛ hp' hp hp0' hp0 μ i j
  have hz0 : ((0 : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    simp
  have hCb0 : 0 ≤ Cb := by
    have h := hCb 1 one_pos _ hz0 v
    have hu : 0 < (1 + ‖v‖) ^ (-(5 : ℝ)) := by positivity
    by_contra hC
    nlinarith [norm_nonneg (timeT m mγ 1 p' p μ i j (0, 0) v - timeT m Λ 1 p' p μ i j (0, 0) v),
      not_le.mp hC]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖kappa e‖ * 2 * Cb) ?_ ?_
    (integrable_const _) ?_
  · refine eventually_nhdsWithin_of_forall fun ε hε => ?_
    have h1 := continuous_timeT hε m mγ p' p μ i j v
    have h2 := continuous_timeT hε m Λ p' p μ i j v
    exact (by fun_prop : Continuous fun z : ℝ × ℝ => kappa e * (2 * (z.2 : ℂ)) *
      (timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v)).aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall fun ε hε => ae_feynmanMeasure.mono fun z hz => ?_
    have hzI := Ioc_prod_subset hz
    have hb := hCb ε hε z hzI v
    have hu : (1 + ‖v‖) ^ (-(5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg v]) (by norm_num)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hz.2.1]
    calc ‖kappa e‖ * (2 * z.2) *
          ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
        ≤ ‖kappa e‖ * (2 * 1) * (Cb * 1) := by
          gcongr
          · exact hz.2.2
          · exact hb.trans (mul_le_mul_of_nonneg_left hu hCb0)
      _ = ‖kappa e‖ * 2 * Cb := by ring
  · refine ae_feynmanMeasure.mono fun z hz => ?_
    have hzI := Ioc_prod_subset hz
    exact ((tendsto_timeT μ i j (massW_pos hm hmγ hp' hp hp0' hp0 hzI v)).sub
      (tendsto_timeT μ i j (massW_pos hm hΛ hp' hp hp0' hp0 hzI v))).const_mul _

theorem continuous_vertexIntegrand_cons {ε : ℝ} (hε : ε ≠ 0) (e m mγ Λ : ℝ)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    Continuous fun q : (Fin 3 → ℝ) × ℝ =>
      vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons q.2 q.1 : Fin 4 → ℝ) i j := by
  simp_rw [vertexIntegrand_apply]
  have hℓ : Continuous fun q : (Fin 3 → ℝ) × ℝ => (Fin.cons q.2 q.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd continuous_fst
  have hd : ∀ (M : ℝ) (k : (Fin 3 → ℝ) × ℝ → Fin 4 → ℝ), Continuous k →
      Continuous fun q => (denom M ε (k q))⁻¹ := by
    intro M k hk
    refine Continuous.inv₀ ?_ fun q h => ?_
    · unfold denom
      have := continuous_dot_comp hk hk
      fun_prop
    · have := denom_im M ε (k q)
      rw [h, zero_im] at this
      exact hε (by linarith)
  have h1 := hd mγ _ hℓ
  have h2 := hd Λ _ hℓ
  have h3 := hd m _ (continuous_const (y := p').add hℓ)
  have h4 := hd m _ (continuous_const (y := p).add hℓ)
  have hN := (continuous_vertexNumerator m p' p μ i j).comp hℓ
  simp only [Function.comp_def] at hN
  fun_prop

/-! ### The energy-first integral and its limit -/

theorem integrable_time_vertexIntegrand {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j :=
  (integrable_jointF hε e m mγ Λ p' p μ i j v).integral_prod_left.congr
    (Eventually.of_forall fun t =>
      (vertexIntegrand_eq_integral_jointF hε e m mγ Λ p' p μ i j t v).symm)

theorem energyFirstIntegral_eq_integral_spatialG {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    (energyFirstIntegral fun ℓ => vertexIntegrand e m mγ Λ ε p' p μ ℓ i j)
      = ∫ v, spatialG e m mγ Λ ε p' p μ i j v := by
  simp only [energyFirstIntegral]
  exact integral_congr_ae (Eventually.of_forall fun v =>
    integral_vertexIntegrand_time hε e m mγ Λ p' p μ i j v)

theorem aestronglyMeasurable_spatialG {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) : AEStronglyMeasurable (spatialG e m mγ Λ ε p' p μ i j) volume := by
  have h := (continuous_vertexIntegrand_cons hε.ne' e m mγ Λ p' p μ i j).stronglyMeasurable
    |>.integral_prod_right' (ν := (volume : Measure ℝ))
  exact h.aestronglyMeasurable.congr
    (Eventually.of_forall fun v => integral_vertexIntegrand_time hε e m mγ Λ p' p μ i j v)

/-- The uniform `(1 + ‖v‖)⁻⁵` bound on the energy integral. -/
theorem exists_norm_spatialG_le {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ ε > 0, ∀ v : Fin 3 → ℝ,
      ‖spatialG e m mγ Λ ε p' p μ i j v‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  obtain ⟨Cb, hCb⟩ := norm_timeT_sub_le hm hmγ hΛ hp' hp hp0' hp0 μ i j
  refine ⟨‖kappa e‖ * 2 * Cb * feynmanMeasure.real univ, fun ε hε v => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := feynmanMeasure)
    (f := fun z => kappa e * (2 * (z.2 : ℂ)) *
      (timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v))
    (C := ‖kappa e‖ * 2 * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))))
    (ae_feynmanMeasure.mono fun z hz => by
      have hzI := Ioc_prod_subset hz
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hz.2.1]
      calc ‖kappa e‖ * (2 * z.2) *
            ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
          ≤ ‖kappa e‖ * (2 * 1) * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))) := by
            gcongr
            · exact hz.2.2
            · exact hCb ε hε z hzI v
        _ = ‖kappa e‖ * 2 * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))) := by ring)
  refine h.trans (le_of_eq ?_)
  ring

theorem integrable_spatialG {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    Integrable (spatialG e m mγ Λ ε p' p μ i j) := by
  obtain ⟨C, hC⟩ := exists_norm_spatialG_le (e := e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  have h := integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5) (by simp; norm_num)
  exact (h.const_mul C).mono' (aestronglyMeasurable_spatialG hε e m mγ Λ p' p μ i j)
    (Eventually.of_forall fun v => hC ε hε v)

/-- The energy-first integral of each entry of the integrand converges, as `ε → 0⁺`, to the
integral over `v` of the closed form `spatialG 0 v`. -/
theorem tendsto_energyFirstIntegral_vertexIntegrand {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ => vertexIntegrand e m mγ Λ ε p' p μ ℓ i j)
      (𝓝[>] 0) (𝓝 (∫ v, spatialG e m mγ Λ 0 p' p μ i j v)) := by
  obtain ⟨C, hC⟩ := exists_norm_spatialG_le (e := e) hm hmγ hΛ hp' hp hp0' hp0 μ i j
  have hbnd := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul C
  have hlim : Tendsto (fun ε : ℝ => ∫ v, spatialG e m mγ Λ ε p' p μ i j v) (𝓝[>] 0)
      (𝓝 (∫ v, spatialG e m mγ Λ 0 p' p μ i j v)) :=
    tendsto_integral_filter_of_dominated_convergence _
      (eventually_nhdsWithin_of_forall fun ε hε =>
        aestronglyMeasurable_spatialG hε e m mγ Λ p' p μ i j)
      (eventually_nhdsWithin_of_forall fun ε hε => Eventually.of_forall (hC ε hε))
      hbnd
      (Eventually.of_forall fun v => tendsto_spatialG hm hmγ hΛ hp' hp hp0' hp0 μ i j v)
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  exact (energyFirstIntegral_eq_integral_spatialG hε e m mγ Λ p' p μ i j).symm

/-! ### The boundary value at `ε = 0` -/

theorem exp_pi_mul_I_mul_neg_three_halves :
    Complex.exp (π * I * (-(3 / 2 : ℂ))) = I := by
  have h : (π : ℂ) * I * (-(3 / 2 : ℂ)) = (-1 : ℤ) * (2 * π * I) + (π / 2 : ℂ) * I := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_mul_I,
    show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem exp_pi_mul_I_mul_neg_five_halves :
    Complex.exp (π * I * (-(5 / 2 : ℂ))) = -I := by
  have h : (π : ℂ) * I * (-(5 / 2 : ℂ)) = (-1 : ℤ) * (2 * π * I) + (-(π / 2) : ℂ) * I := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_mul_I,
    show (-((π : ℂ) / 2)) = ((-(π / 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `(-W)^{-3/2} = i W^{-3/2}` for `W > 0`: the boundary value from the upper half plane. -/
theorem neg_ofReal_cpow_neg_three_halves {W : ℝ} (hW : 0 < W) :
    (-(W : ℂ)) ^ (-(3 / 2 : ℂ)) = I * ((W ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
  have h := Complex.ofReal_cpow_of_nonpos (x := -W) (by linarith) (-(3 / 2 : ℂ))
  push_cast at h
  rw [h, exp_pi_mul_I_mul_neg_three_halves, Complex.ofReal_cpow hW.le]
  push_cast
  ring_nf

/-- `(-W)^{-5/2} = -i W^{-5/2}` for `W > 0`: the boundary value from the upper half plane. -/
theorem neg_ofReal_cpow_neg_five_halves {W : ℝ} (hW : 0 < W) :
    (-(W : ℂ)) ^ (-(5 / 2 : ℂ)) = -I * ((W ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
  have h := Complex.ofReal_cpow_of_nonpos (x := -W) (by linarith) (-(5 / 2 : ℂ))
  push_cast at h
  rw [h, exp_pi_mul_I_mul_neg_five_halves, Complex.ofReal_cpow hW.le]
  push_cast
  ring_nf

/-- The closed-form energy integral at `ε = 0`, with the phases made explicit. -/
theorem timeT_zero_eq {m M : ℝ} {p' p : Fin 4 → ℝ} (μ i j : Fin 4) {z : ℝ × ℝ}
    {v : Fin 3 → ℝ} (hW : 0 < massW m M p' p z v) :
    timeT m M 0 p' p μ i j z v =
      -(I * (π / 8 : ℂ)) * alphaN m p' p μ i j * ((massW m M p' p z v ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
        + I * (3 * π / 8 : ℂ)
          * vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j
          * ((massW m M p' p z v ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
  simp only [timeT, ofReal_zero, zero_mul, add_zero]
  rw [neg_ofReal_cpow_neg_three_halves hW, neg_ofReal_cpow_neg_five_halves hW]
  ring

/-- The uniform Pauli–Villars bound persists at `ε = 0`. -/
theorem norm_timeT_zero_sub_le {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ∃ Cb : ℝ, ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeT m mγ 0 p' p μ i j z v - timeT m Λ 0 p' p μ i j z v‖
        ≤ Cb * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  obtain ⟨Cb, hCb⟩ := norm_timeT_sub_le hm hmγ hΛ hp' hp hp0' hp0 μ i j
  refine ⟨Cb, fun z hz v => ?_⟩
  have hlim := ((tendsto_timeT μ i j (massW_pos hm hmγ hp' hp hp0' hp0 hz v)).sub
    (tendsto_timeT μ i j (massW_pos hm hΛ hp' hp hp0' hp0 hz v))).norm
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hCb ε hε z hz v)

end QED.OneLoop.VertexLimit

end
