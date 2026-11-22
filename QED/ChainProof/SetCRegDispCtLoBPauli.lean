/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBValue
import QED.OneLoop.NumeratorReduction
import QED.Algebra.FormFactorProjector
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Pauli projection of the doubled vertex with one photon denominator

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 5 of the
plan (the value of the doubled vertex). The Feynman-parameter form
`QED.ChainProof.CtLoB.dblOneLimit_vChain` of the doubled vertex is projected on the Pauli form
factor with the frozen projector (`QED.OneLoop.formFactorProj_eq_of_sandwich`): the `γ^μ` term
drops out and the on-shell reduction `QED.OneLoop.sandwich_vertexNumeratorMatrix_neg_shift` of the
numerator at `-K` leaves its `S^{μν} q_ν` coefficient only.

* `pauliNum_eq_of_sandwich`: the Pauli numerator of a vertex that, between on-shell spinors, is
  `a γ^μ + b (p' + p)^μ + c q^μ + d S^{μν} q_ν` is `q² (4m² + q²)² (i m d - 2 m b)/m`;
* `pauliNum_gamma`, `pauliNum_vertexNumeratorMatrix_neg_shift`: hence `0` for `γ^μ` and
  `4 m (x₃ - x₃²) q² (4m² + q²)²` for the one-loop numerator at `-K`, `x₃ = 1 - y`;
* `vChain_pauliWt`, `sum_pauliWt_gamma`: the Pauli weights turn vertex chains into Pauli numerators;
* `alpha_eq_of_quadratic`: the energy-quadratic coefficient of a vertex chain is unique;
* **`dblOneLimit_pauliChain`**: for on-shell positive-energy momenta with `q² > 0` and any
  admissible energy coefficient `α`,
  `dblOneLimit α (pauliChain e) = i (π²/6) κ_e 4 m q² (4m² + q²)² ∫ 6 x_d y² (x₃ - x₃²)/Δ²`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Matrix
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.Dirac QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.VPUnitNested

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The Pauli numerator from an on-shell decomposition -/

/-- **The Pauli numerator of a decomposed vertex**: if, between on-shell spinors,
`V^μ = a γ^μ + b (p' + p)^μ + c q^μ + d S^{μν} q_ν`, then
`pauliNum V = q² (4m² + q²)² (i m d - 2 m b)/m`. -/
theorem pauliNum_eq_of_sandwich {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {a b c d : ℂ}
    (h : ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* slash p' = -((m : ℂ) • w) →
      w ⬝ᵥ (V μ *ᵥ u) = w ⬝ᵥ ((a • gamma μ + (b * ((p' μ + p μ : ℝ) : ℂ) +
        c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙 +
          d • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u)) :
    pauliNum m p' p V =
      (Minkowski.dot (p' - p) (p' - p) : ℂ) *
        (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 *
          (I * m * d - 2 * m * b) / m := by
  obtain ⟨-, h2, -⟩ := formFactorProj_eq_of_sandwich one_ne_zero hm hp' hp hq h
  rw [formFactorProj₂_eq_pauliNum] at h2
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hq' : (Minkowski.dot (p' - p) (p' - p) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hD : 4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 4 * m ^ 2 + Minkowski.dot (p' - p) (p' - p) := by positivity
    exact_mod_cast this.ne'
  simp only [Complex.ofReal_one, one_mul, div_one] at h2
  rw [div_eq_iff (mul_ne_zero hq' (pow_ne_zero 2 hD))] at h2
  rw [eq_div_iff hm']
  linear_combination h2

/-- The Pauli numerator of `γ^μ` vanishes. -/
theorem pauliNum_gamma {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) : pauliNum m p' p (fun μ => gamma μ) = 0 := by
  rw [pauliNum_eq_of_sandwich (a := 1) (b := 0) (c := 0) (d := 0) hm hp' hp hq]
  · ring
  · intro μ u w _ _
    simp

/-- The Pauli numerator of the one-loop numerator at `-K`: `4 m (x₃ - x₃²) q² (4m² + q²)²`. -/
theorem pauliNum_vertexNumeratorMatrix_neg_shift {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (z : ℝ × ℝ) :
    pauliNum m p' p (fun μ => vertexNumeratorMatrix m p' p μ (-shiftK p' p z)) =
      4 * (m : ℂ) * (((1 - z.2) - (1 - z.2) ^ 2 : ℝ) : ℂ) *
        ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [pauliNum_eq_of_sandwich (a := ((2 * ((1 - 4 * (1 - z.2) + (1 - z.2) ^ 2) * m ^ 2
      - ((1 - z.2) + (z.2 * z.1) * (z.2 * (1 - z.1))) * Minkowski.dot (p' - p) (p' - p)) : ℝ) : ℂ))
    (b := 0) (c := (numeratorAsym m z.1 z.2 : ℂ))
    (d := -(4 * I * m * ((1 - z.2) - (1 - z.2) ^ 2))) hm hp' hp hq]
  · rw [div_eq_iff hm']
    push_cast
    linear_combination (-(4 : ℂ) * (m : ℂ) ^ 2 * ((1 - (z.2 : ℂ)) - (1 - (z.2 : ℂ)) ^ 2) *
      ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
        (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)) * I_sq
  · intro μ u w hu hw
    rw [show -shiftK p' p z = -(z.2 • (z.1 • p' + (1 - z.1) • p)) from rfl,
      sandwich_vertexNumeratorMatrix_neg_shift hp' hp hu hw z.1 z.2 μ]
    simp only [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
    push_cast
    ring

/-! ### Pauli weights and vertex chains -/

theorem vChain_pauliWt (m : ℝ) (p' p : Fin 4 → ℝ) (k : ℂ) (ℓ : Fin 4 → ℝ) :
    vChain m p' p (fun x => pauliWt m p' p x.1 x.2.1 x.2.2 * k) ℓ =
      k * pauliNum m p' p (fun μ => vertexNumeratorMatrix m p' p μ ℓ) := by
  rw [vChain, pauliNum_eq_sum, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [vertexNumerator_eq_vertexNumeratorMatrix_apply]
  ring

theorem sum_pauliWt_gamma (m : ℝ) (p' p : Fin 4 → ℝ) (k : ℂ) :
    ∑ x : VIdx, pauliWt m p' p x.1 x.2.1 x.2.2 * k * gamma x.1 x.2.1 x.2.2 =
      k * pauliNum m p' p (fun μ => gamma μ) := by
  rw [pauliNum_eq_sum, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The energy-quadratic coefficient -/

/-- A quadratic polynomial in a real variable determines its leading coefficient. -/
theorem lead_eq_of_quadratic {a b c a' b' c' : ℂ}
    (h : ∀ t : ℝ, a * (t : ℂ) ^ 2 + b * t + c = a' * (t : ℂ) ^ 2 + b' * t + c') : a = a' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  push_cast at h0 h1 h2
  linear_combination (h1 + h2 - 2 * h0) / 2

theorem vChain_cons (m : ℝ) (p' p : Fin 4 → ℝ) (c : VIdx → ℂ) (v : Fin 3 → ℝ) :
    ∃ β γ : ℂ, ∀ t : ℝ, vChain m p' p c (Fin.cons t v : Fin 4 → ℝ) =
      (∑ x, c x * alphaN m p' p x.1 x.2.1 x.2.2) * (t : ℂ) ^ 2 + β * t + γ := by
  choose β γ hβ using fun x : VIdx => vertexNumerator_cons m p' p x.1 x.2.1 x.2.2 v
  refine ⟨∑ x, c x * β x, ∑ x, c x * γ x, fun t => ?_⟩
  simp only [vChain, hβ, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **The energy-quadratic coefficient of a vertex chain is unique.** -/
theorem alpha_eq_of_quadratic (m : ℝ) (p' p : Fin 4 → ℝ) (c : VIdx → ℂ) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      vChain m p' p c (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    α = ∑ x, c x * alphaN m p' p x.1 x.2.1 x.2.2 := by
  obtain ⟨β, γ, h⟩ := hα 0
  obtain ⟨β', γ', h'⟩ := vChain_cons m p' p c 0
  exact lead_eq_of_quadratic fun t => (h t).symm.trans (h' t)

/-! ### The Pauli projection of the doubled vertex -/

/-- **The Pauli-projected doubled vertex with one photon denominator.** For on-shell
positive-energy momenta with `q² > 0` and any energy-quadratic coefficient `α` of the
Pauli-projected chain, `dblOneLimit α (pauliChain e)` is
`i (π²/6) κ_e 4 m q² (4m² + q²)² ∫ 6 x_d y² (x₃ - x₃²) / Δ²`. -/
theorem dblOneLimit_pauliChain (e : ℝ) {m M : ℝ} (hm : 0 < m) (hM : 0 < M) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (d : Fin 2) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    dblOneLimit α (pauliChain e m p' p) m M d p' p =
      I * ((π ^ 2 / 6 : ℝ) : ℂ) * kappa e *
        (4 * (m : ℂ) * ((Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)) *
        ∫ z, dblWt d 0 z * (((1 - z.2) - (1 - z.2) ^ 2 : ℝ) : ℂ) /
          (feynmanMass m M z.1 z.2 p' p : ℂ) ^ 2 ∂feynmanMeasure := by
  set c : VIdx → ℂ := fun x => pauliWt m p' p x.1 x.2.1 x.2.2 * kappa e
  have hN : pauliChain e m p' p = vChain m p' p c := pauliChain_eq_vChain e m p' p
  rw [hN] at hα ⊢
  rw [alpha_eq_of_quadratic m p' p c hα, dblOneLimit_vChain hm hM hp' hp hp0' hp0 c d,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  have hg : ∑ x : VIdx, c x * gamma x.1 x.2.1 x.2.2 = 0 := by
    simp only [c]
    rw [sum_pauliWt_gamma, pauliNum_gamma hm.ne' hp' hp hq, mul_zero]
  rw [hg, vChain_pauliWt, pauliNum_vertexNumeratorMatrix_neg_shift hm.ne' hp' hp hq]
  ring

end QED.ChainProof.CtLoB

end
