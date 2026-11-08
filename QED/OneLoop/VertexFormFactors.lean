/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexClosedForm
public import QED.OneLoop.VertexSpatial
public import QED.OneLoop.NumeratorReduction
public import QED.Algebra.FormFactorIndependence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Form factors of the one-loop vertex

The `ε → 0⁺` limit of the energy-first integral of the one-loop vertex integrand, divided by
`i`, is evaluated in closed form and sandwiched between on-shell Dirac solutions. The result is
the decomposition (63.18) with explicit Feynman-parameter integrals for the two coefficients
(`formFactorA`, `formFactorB`). With `x₁ = y x`, `x₂ = y (1 - x)`, `x₃ = 1 - y` and
`D_M = (1 - y) M² + y² (m² + x (1 - x) q²)`, the Pauli coefficient is
`B = (e²/8π²) ∫ dF₃ (x₃ - x₃²) m² (1/D_{m_γ} - 1/D_Λ)`, the Pauli–Villars form of (63.20).

These declarations are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-! ### Kinematics of the Feynman mass term -/

theorem dot_sub_self (p' p : Fin 4 → ℝ) :
    Minkowski.dot (p' - p) (p' - p)
      = Minkowski.dot p' p' - 2 * Minkowski.dot p' p + Minkowski.dot p p := by
  simp only [Minkowski.dot_eq, Pi.sub_apply]; ring

/-- On shell, `D_M = (1 - y) M² + y² (m² + x (1 - x) q²)`, the primary source's (63.15). -/
theorem feynmanMass_onShell {m M x y : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) :
    feynmanMass m M x y p' p
      = (1 - y) * M ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * Minkowski.dot (p' - p) (p' - p)) := by
  rw [feynmanMass, dot_smul_add_smul_self, dot_sub_self, hp', hp]; ring

theorem feynmanMass_reflect {m M x y : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) :
    feynmanMass m M (1 - x) y p' p = feynmanMass m M x y p' p := by
  rw [feynmanMass_onShell hp' hp, feynmanMass_onShell hp' hp]; ring

/-! ### Integrability against `feynmanMeasure` -/

theorem integrable_feynmanMeasure_of_continuousOn {E : Type*} [NormedAddCommGroup E]
    {f : ℝ × ℝ → E} (hf : ContinuousOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    Integrable f feynmanMeasure := by
  rw [feynmanMeasure_eq]
  exact (hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-! ### The closed form, entrywise -/

theorem kappa_eq (e : ℝ) : kappa e = ((e ^ 3 / (16 * π ^ 4) : ℝ) : ℂ) := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have h1 : (I * e) ^ 3 * (1 / I) ^ 3 = (e : ℂ) ^ 3 := by
    rw [← mul_pow]; congr 1; field_simp
  unfold kappa
  rw [h1]
  push_cast
  ring

/-- The integrand of the closed form of `V^μ`, as a matrix at Feynman parameters `z`. -/
noncomputable def closedFormMatrix (m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (z : ℝ × ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (2 * (z.2 : ℂ)) •
    (((Real.log (feynmanMass m Λ z.1 z.2 p' p / feynmanMass m mγ z.1 z.2 p' p) : ℝ) : ℂ) •
        Dirac.gamma μ
      + ((1 / 2 * ((feynmanMass m mγ z.1 z.2 p' p)⁻¹ - (feynmanMass m Λ z.1 z.2 p' p)⁻¹) : ℝ)
          : ℂ) • vertexNumeratorMatrix m p' p μ (-shiftK p' p z))

/-- `V^μ_{ij} = (1/i) lim = (e³/16π²) ∫ dF₃ [log(D_Λ/D_γ) γ^μ + Ñ/(2D_γ) - Ñ/(2D_Λ)]_{ij}`. -/
theorem vertexLimit_entry_eq {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    (1 / I) * ∫ v, spatialG e m mγ Λ 0 p' p μ i j v
      = ((e ^ 3 / (16 * π ^ 2) : ℝ) : ℂ) *
          ∫ z, closedFormMatrix m mγ Λ p' p μ z i j ∂feynmanMeasure := by
  rw [integral_spatialG_zero_eq hm hmγ hΛ hp' hp hp0' hp0]
  have hcongr : (fun z : ℝ × ℝ => kappa e * (2 * (z.2 : ℂ)) *
      ∫ v, (timeT m mγ 0 p' p μ i j z v - timeT m Λ 0 p' p μ i j z v))
      =ᵐ[feynmanMeasure] fun z => (kappa e * I * (π : ℂ) ^ 2) *
        closedFormMatrix m mγ Λ p' p μ z i j := by
    refine ae_feynmanMeasure.mono fun z hz => ?_
    dsimp only
    rw [integral_timeT_zero_sub hm hmγ hΛ hp' hp hp0' hp0 μ i j (Ioc_prod_subset hz)]
    simp only [closedFormMatrix, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      ← vertexNumerator_eq_vertexNumeratorMatrix_apply]
    push_cast
    ring
  rw [integral_congr_ae hcongr, integral_const_mul, kappa_eq]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-! ### The explicit coefficients -/

/-- The integrand of the `γ^μ` coefficient. -/
noncomputable def formIntegrandA (m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 * (Real.log (feynmanMass m Λ z.1 z.2 p' p / feynmanMass m mγ z.1 z.2 p' p)
    + 1 / 2 * ((feynmanMass m mγ z.1 z.2 p' p)⁻¹ - (feynmanMass m Λ z.1 z.2 p' p)⁻¹)
      * (2 * ((1 - 4 * (1 - z.2) + (1 - z.2) ^ 2) * m ^ 2
        - ((1 - z.2) + (z.2 * z.1) * (z.2 * (1 - z.1))) * Minkowski.dot (p' - p) (p' - p))))

/-- The integrand of the Pauli coefficient: `2y (x₃ - x₃²) m² (1/D_γ - 1/D_Λ)`. -/
noncomputable def formIntegrandB (m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2
    * ((feynmanMass m mγ z.1 z.2 p' p)⁻¹ - (feynmanMass m Λ z.1 z.2 p' p)⁻¹)

/-- The integrand of the `(p' - p)^μ` term, which is odd under `x ↦ 1 - x`. -/
noncomputable def oddIntegrand (m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 * (1 / 2 * ((feynmanMass m mγ z.1 z.2 p' p)⁻¹ - (feynmanMass m Λ z.1 z.2 p' p)⁻¹))
    * (numeratorAsym m z.1 z.2 * (p' μ - p μ))

/-- The `γ^μ` coefficient `A` of the one-loop vertex (counterterm not included). -/
noncomputable def formFactorA (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) : ℝ :=
  e ^ 2 / (16 * π ^ 2) * ∫ z, formIntegrandA m mγ Λ p' p z ∂feynmanMeasure

/-- The Pauli coefficient `B = (e²/8π²) ∫ dF₃ (x₃ - x₃²) m² (1/D_γ - 1/D_Λ)`. -/
noncomputable def formFactorB (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) : ℝ :=
  e ^ 2 / (8 * π ^ 2) * ∫ z, formIntegrandB m mγ Λ p' p z ∂feynmanMeasure

/-! ### Continuity and integrability on the unit square -/

theorem feynmanMass_pos_of_mem {m M : ℝ} (hm : 0 < m) (hM : 0 < M) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    0 < feynmanMass m M z.1 z.2 p' p :=
  lt_of_lt_of_le (by positivity) (feynmanMass_pos (M := M) hp' hp hp0' hp0 hz.1 hz.2)

section Continuity

variable {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) {p' p : Fin 4 → ℝ}
  (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
  (hp0 : 0 < p 0)
include hm hmγ hΛ hp' hp hp0' hp0

theorem continuousOn_inv_feynmanMass_sub :
    ContinuousOn (fun z : ℝ × ℝ =>
      (feynmanMass m mγ z.1 z.2 p' p)⁻¹ - (feynmanMass m Λ z.1 z.2 p' p)⁻¹)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
  ((continuous_feynmanMass m mγ p' p).continuousOn.inv₀ fun _ hz =>
      (feynmanMass_pos_of_mem hm hmγ hp' hp hp0' hp0 hz).ne').sub
    ((continuous_feynmanMass m Λ p' p).continuousOn.inv₀ fun _ hz =>
      (feynmanMass_pos_of_mem hm hΛ hp' hp hp0' hp0 hz).ne')

theorem continuousOn_log_feynmanMass :
    ContinuousOn (fun z : ℝ × ℝ =>
      Real.log (feynmanMass m Λ z.1 z.2 p' p / feynmanMass m mγ z.1 z.2 p' p))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
  ((continuous_feynmanMass m Λ p' p).continuousOn.div
      (continuous_feynmanMass m mγ p' p).continuousOn fun _ hz =>
        (feynmanMass_pos_of_mem hm hmγ hp' hp hp0' hp0 hz).ne').log fun _ hz =>
    (div_pos (feynmanMass_pos_of_mem hm hΛ hp' hp hp0' hp0 hz)
      (feynmanMass_pos_of_mem hm hmγ hp' hp hp0' hp0 hz)).ne'

theorem integrable_formIntegrandA :
    Integrable (formIntegrandA m mγ Λ p' p) feynmanMeasure := by
  refine integrable_feynmanMeasure_of_continuousOn ?_
  have h1 := continuousOn_log_feynmanMass hm hmγ hΛ hp' hp hp0' hp0
  have h2 := continuousOn_inv_feynmanMass_sub hm hmγ hΛ hp' hp hp0' hp0
  have h3 : Continuous fun z : ℝ × ℝ => Minkowski.dot (p' - p) (p' - p) := continuous_const
  unfold formIntegrandA
  exact (continuous_const.mul continuous_snd).continuousOn.mul
    (h1.add ((continuousOn_const.mul h2).mul (by fun_prop)))

theorem integrable_formIntegrandB :
    Integrable (formIntegrandB m mγ Λ p' p) feynmanMeasure := by
  refine integrable_feynmanMeasure_of_continuousOn ?_
  have h2 := continuousOn_inv_feynmanMass_sub hm hmγ hΛ hp' hp hp0' hp0
  unfold formIntegrandB
  exact (by fun_prop : Continuous fun z : ℝ × ℝ =>
    2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2).continuousOn.mul h2

theorem integrable_oddIntegrand (μ : Fin 4) :
    Integrable (oddIntegrand m mγ Λ p' p μ) feynmanMeasure := by
  refine integrable_feynmanMeasure_of_continuousOn ?_
  have h2 := continuousOn_inv_feynmanMass_sub hm hmγ hΛ hp' hp hp0' hp0
  unfold oddIntegrand numeratorAsym
  exact ((continuous_const.mul continuous_snd).continuousOn.mul (continuousOn_const.mul h2)).mul
    (by fun_prop)

theorem integrable_closedFormMatrix (μ i j : Fin 4) :
    Integrable (fun z => closedFormMatrix m mγ Λ p' p μ z i j) feynmanMeasure := by
  refine integrable_feynmanMeasure_of_continuousOn ?_
  have h1 := continuousOn_log_feynmanMass hm hmγ hΛ hp' hp hp0' hp0
  have h2 := continuousOn_inv_feynmanMass_sub hm hmγ hΛ hp' hp hp0' hp0
  have hN : Continuous fun z : ℝ × ℝ => vertexNumeratorMatrix m p' p μ (-shiftK p' p z) i j := by
    simp_rw [← vertexNumerator_eq_vertexNumeratorMatrix_apply]
    exact (continuous_vertexNumerator m p' p μ i j).comp (continuous_shiftK p' p).neg
  simp only [closedFormMatrix, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  refine (by fun_prop : Continuous fun z : ℝ × ℝ => 2 * (z.2 : ℂ)).continuousOn.mul
    ((Complex.continuous_ofReal.comp_continuousOn h1).mul continuousOn_const |>.add
      ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul h2)).mul
        hN.continuousOn))

end Continuity

/-! ### Sandwiching -/

/-- The sandwich of an entrywise integral is the integral of the sandwiches. -/
theorem dotProduct_mulVec_of_integral {ν : Measure (ℝ × ℝ)}
    (f : ℝ × ℝ → Matrix (Fin 4) (Fin 4) ℂ) (hf : ∀ i j, Integrable (fun z => f z i j) ν)
    (c : ℂ) (u w : Fin 4 → ℂ) :
    w ⬝ᵥ (Matrix.of (fun i j => c * ∫ z, f z i j ∂ν) *ᵥ u) = c * ∫ z, w ⬝ᵥ (f z *ᵥ u) ∂ν := by
  simp only [dotProduct, mulVec, Matrix.of_apply]
  have h1 : ∀ i, Integrable (fun z => w i * ∑ j, f z i j * u j) ν := fun i =>
    (integrable_finsetSum _ fun j _ => (hf i j).mul_const _).const_mul _
  rw [integral_finsetSum _ fun i _ => h1 i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hf i j).mul_const _, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]
  ring

/-- The sandwich of the closed-form integrand, reduced on shell. -/
theorem sandwich_closedFormMatrix {m mγ Λ : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    {u w : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u))
    (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) (μ : Fin 4) (z : ℝ × ℝ) :
    w ⬝ᵥ (closedFormMatrix m mγ Λ p' p μ z *ᵥ u) =
      (formIntegrandA m mγ Λ p' p z : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))
        - (2 * I / (m : ℂ)) * (formIntegrandB m mγ Λ p' p z : ℂ)
          * (w ⬝ᵥ ((∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u))
        + (oddIntegrand m mγ Λ p' p μ z : ℂ) * (w ⬝ᵥ u) := by
  have hN := sandwich_vertexNumeratorMatrix_neg_shift hp' hp hu hw z.1 z.2 μ
  have hK : -shiftK p' p z = -(z.2 • (z.1 • p' + (1 - z.1) • p)) := rfl
  simp only [closedFormMatrix, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul,
    dotProduct_add, smul_eq_mul, hK, hN, formIntegrandA, formIntegrandB, oddIntegrand]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp
  ring

theorem oddIntegrand_reflect {m mγ Λ : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (μ : Fin 4)
    (z : ℝ × ℝ) :
    oddIntegrand m mγ Λ p' p μ (1 - z.1, z.2) = -oddIntegrand m mγ Λ p' p μ z := by
  simp only [oddIntegrand, feynmanMass_reflect hp' hp, numeratorAsym_one_sub]
  ring

/-- **The decomposition of the one-loop vertex limit.** For on-shell positive-energy momenta,
`(1/i) lim_{ε→0⁺}` of the energy-first integral, sandwiched between on-shell Dirac solutions,
equals `e ū' [A γ^μ - (i/m) B S^{μν} q_ν] u` with `A = formFactorA` and `B = formFactorB`. -/
theorem sandwich_vertexLimit {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) {u w : Fin 4 → ℂ}
    (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u)) (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) :
    w ⬝ᵥ (Matrix.of (fun i j => (1 / I) * ∫ v, spatialG e m mγ Λ 0 p' p μ i j v) *ᵥ u) =
      (e : ℂ) * (w ⬝ᵥ ((((formFactorA e m mγ Λ p' p : ℝ) : ℂ) • Dirac.gamma μ
        - (I / (m : ℂ) * ((formFactorB e m mγ Λ p' p : ℝ) : ℂ)) •
          ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u)) := by
  have hentry : Matrix.of (fun i j => (1 / I) * ∫ v, spatialG e m mγ Λ 0 p' p μ i j v)
      = Matrix.of (fun i j => ((e ^ 3 / (16 * π ^ 2) : ℝ) : ℂ) *
          ∫ z, closedFormMatrix m mγ Λ p' p μ z i j ∂feynmanMeasure) := by
    ext i j
    simp only [Matrix.of_apply]
    exact vertexLimit_entry_eq hm hmγ hΛ hp' hp hp0' hp0 μ i j
  rw [hentry, dotProduct_mulVec_of_integral _
    (integrable_closedFormMatrix hm hmγ hΛ hp' hp hp0' hp0 μ)]
  simp_rw [sandwich_closedFormMatrix hm.ne' hp' hp hu hw μ]
  set X := w ⬝ᵥ (Dirac.gamma μ *ᵥ u)
  set Y := w ⬝ᵥ ((∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u)
  set Z := w ⬝ᵥ u
  set c : ℂ := 2 * I / (m : ℂ)
  have iA := (integrable_formIntegrandA hm hmγ hΛ hp' hp hp0' hp0).ofReal (𝕜 := ℂ)
  have iB := (integrable_formIntegrandB hm hmγ hΛ hp' hp hp0' hp0).ofReal (𝕜 := ℂ)
  have iO := (integrable_oddIntegrand hm hmγ hΛ hp' hp hp0' hp0 μ).ofReal (𝕜 := ℂ)
  have i1 : Integrable (fun z => (formIntegrandA m mγ Λ p' p z : ℂ) * X) feynmanMeasure :=
    iA.mul_const X
  have i2 : Integrable (fun z => c * (formIntegrandB m mγ Λ p' p z : ℂ) * Y) feynmanMeasure :=
    (iB.const_mul c).mul_const Y
  have i3 : Integrable (fun z => (formIntegrandA m mγ Λ p' p z : ℂ) * X
      - c * (formIntegrandB m mγ Λ p' p z : ℂ) * Y) feynmanMeasure := i1.sub i2
  have i4 : Integrable (fun z => (oddIntegrand m mγ Λ p' p μ z : ℂ) * Z) feynmanMeasure :=
    iO.mul_const Z
  have hodd : ∫ z, oddIntegrand m mγ Λ p' p μ z ∂feynmanMeasure = 0 :=
    integral_feynman_eq_zero_of_odd (oddIntegrand_reflect hp' hp μ)
  have hsplit : ∫ z, ((formIntegrandA m mγ Λ p' p z : ℂ) * X
        - c * (formIntegrandB m mγ Λ p' p z : ℂ) * Y
        + (oddIntegrand m mγ Λ p' p μ z : ℂ) * Z) ∂feynmanMeasure
      = ((∫ z, formIntegrandA m mγ Λ p' p z ∂feynmanMeasure : ℝ) : ℂ) * X
        - c * ((∫ z, formIntegrandB m mγ Λ p' p z ∂feynmanMeasure : ℝ) : ℂ) * Y := by
    rw [integral_add i3 i4, integral_sub i1 i2, integral_mul_const, integral_mul_const,
      integral_mul_const, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      integral_complex_ofReal, hodd]
    simp
  rw [hsplit]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    formFactorA, formFactorB, c]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

end QED.OneLoop.VertexLimit

end
