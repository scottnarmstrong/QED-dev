/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexEnergyFirst
public import QED.Algebra.Contraction
public import QED.Integration.SpatialIntegral
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The spatial integral of the one-loop vertex

Fix Feynman parameters `z = (x, y)` in the unit square and one matrix entry. This module
evaluates in closed form the integral over the spatial loop momentum `v⃗ ∈ ℝ³` of the
Pauli–Villars difference `timeT m m_γ 0 … z v - timeT m Λ 0 … z v` of the energy integrals of
`QED.OneLoop.VertexLimit.timeT` at `ε = 0`.

Write `D_M = feynmanMass m M x y p' p` (positive on the mass shell), `K = shiftK p' p z`,
`a = K⁰` and `b⃗ = (K¹, K², K³)`. The computation has four steps.

1. Translating `v⃗ ↦ v⃗ - b⃗` turns the mass term into `|v⃗|² + D_M` and the numerator argument
   `(-a, v⃗)` into `(0, v⃗) - K` (`timeT_zero_sub_eq`).
2. The numerator `N((0, v⃗) - K)` is a quadratic polynomial in `v⃗` whose coefficients are values
   of the bilinear form `vertexForm` (`vertexNumerator_cons_zero_sub`).
3. Odd and mixed moments of radial functions vanish and the diagonal second moments are a third
   of the radial one. Together with the radial integrals of `QED.Integration.SpatialIntegral`
   this evaluates the integral of the resulting quadratic radial integrand
   (`integral_spatialQuadratic`). The radial second moment of the paired `-5/2` profile equals
   the paired logarithmic integral `2π log(D₂/D₁)`.
4. The leading energy coefficient `alphaN` is `vertexForm` at the unit time slash
   (`alphaN_eq`), and the covariant contraction
   `-vF(E₀, E₀) + Σₖ vF(Eₖ, Eₖ) = 4 γ^μ` (`neg_vertexForm_time_add_sum_vertexForm_space`)
   combines the two logarithmic terms.

## Main statements

* `QED.OneLoop.VertexLimit.alphaN_eq`: the leading energy coefficient of the numerator.
* `QED.OneLoop.VertexLimit.neg_vertexForm_time_add_sum_vertexForm_space`: the covariant
  contraction of the quadratic numerator terms.
* `QED.OneLoop.VertexLimit.integrable_timeT_zero_sub`: the Pauli–Villars difference is
  integrable over `ℝ³`.
* `QED.OneLoop.VertexLimit.integral_timeT_zero_sub`: its integral is
  `iπ² log(D_Λ/D_γ) γ^μ + (iπ²/2) (1/D_γ - 1/D_Λ) N(-K)`.

The remaining declarations are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter MeasureTheory
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-! ### Gamma-matrix algebra -/

/-- The slash of the `β`-th unit vector is `g_{ββ} γ^β`. -/
theorem slash_single (β : Fin 4) :
    Dirac.slash (Pi.single β 1) = ((Minkowski.metric β β : ℝ) : ℂ) • Dirac.gamma β := by
  fin_cases β <;> simp [Dirac.slash, Minkowski.lower_eq, Fin.sum_univ_four, Minkowski.metric]

/-- `γ_β = g_{ββ} γ^β`. -/
theorem gammaLower_eq_smul (β : Fin 4) :
    Dirac.gammaLower β = ((Minkowski.metric β β : ℝ) : ℂ) • Dirac.gamma β := by
  fin_cases β <;> simp [Dirac.gammaLower, Minkowski.metric]

theorem metric_mul_self (β : Fin 4) : Minkowski.metric β β * Minkowski.metric β β = 1 := by
  fin_cases β <;> simp [Minkowski.metric]

theorem cons_one_zero_eq_single : (Fin.cons 1 0 : Fin 4 → ℝ) = Pi.single 0 1 := by
  funext q
  refine Fin.cases ?_ (fun k => ?_) q <;> simp

/-- `(0, v⃗)̸ = Σₖ vₖ Eₖ`, with `Eₖ` the slash of the `(k + 1)`-th unit vector. -/
theorem slash_cons_zero (v : Fin 3 → ℝ) :
    Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ) =
      ∑ k : Fin 3, (v k : ℂ) • Dirac.slash (Pi.single k.succ 1) := by
  have h2 : (Fin.cons 0 v : Fin 4 → ℝ) 2 = v 1 := rfl
  have h3 : (Fin.cons 0 v : Fin 4 → ℝ) 3 = v 2 := rfl
  simp only [slash_single, Fin.sum_univ_three]
  simp [Dirac.slash, Minkowski.lower_eq, Fin.sum_univ_four, Minkowski.metric, h2, h3]

/-! ### The bilinear form -/

/-- `vertexForm μ X Y = (γ^ν X γ^μ Y γ_ν)_{ij}`. -/
theorem vertexForm_eq_sum (μ : Fin 4) (X Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ X Y i j =
      (∑ ν, Dirac.gamma ν * (X * Dirac.gamma μ * Y) * Dirac.gammaLower ν) i j := by
  rw [vertexForm, Finset.sum_comm, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [Dirac.gammaLower, Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc, Minkowski.metric_symm ν]

theorem vertexForm_add_left (μ : Fin 4) (X X' Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ (X + X') Y i j = vertexForm μ X Y i j + vertexForm μ X' Y i j := by
  simp only [vertexForm, Matrix.add_mul, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem vertexForm_add_right (μ : Fin 4) (X Y Y' : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ X (Y + Y') i j = vertexForm μ X Y i j + vertexForm μ X Y' i j := by
  simp only [vertexForm, Matrix.add_mul, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem vertexForm_zero_left (μ : Fin 4) (Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ 0 Y i j = 0 := by
  simp [vertexForm]

theorem vertexForm_zero_right (μ : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ X 0 i j = 0 := by
  simp [vertexForm]

theorem vertexForm_sum_smul_left {ι : Type*} (μ : Fin 4) (s : Finset ι) (c : ι → ℂ)
    (A : ι → Matrix (Fin 4) (Fin 4) ℂ) (Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ (∑ k ∈ s, c k • A k) Y i j = ∑ k ∈ s, c k * vertexForm μ (A k) Y i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, vertexForm_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, vertexForm_add_left, vertexForm_smul_left, ih]

theorem vertexForm_sum_smul_right {ι : Type*} (μ : Fin 4) (s : Finset ι) (c : ι → ℂ)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (A : ι → Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ X (∑ k ∈ s, c k • A k) i j = ∑ k ∈ s, c k * vertexForm μ X (A k) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, vertexForm_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, vertexForm_add_right, vertexForm_smul_right,
      ih]

/-! ### The leading energy coefficient -/

/-- The leading energy coefficient is the `vertexForm` of the unit time slash. -/
theorem alphaN_eq (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    alphaN m p' p μ i j =
      vertexForm μ (Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ))
        (Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ)) i j := by
  obtain ⟨β, γ, h⟩ := vertexNumerator_cons m p' p μ i j 0
  set E := Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ)
  set X := (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p' + (Fin.cons 0 0 : Fin 4 → ℝ))
  set Y := (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p + (Fin.cons 0 0 : Fin 4 → ℝ))
  have h' : ∀ t : ℝ, vertexNumerator m p' p μ (Fin.cons t 0 : Fin 4 → ℝ) i j =
      vertexForm μ E E i j * (t : ℂ) ^ 2 + -(vertexForm μ X E i j + vertexForm μ E Y i j) * t
        + vertexForm μ X Y i j := fun t => by
    rw [vertexNumerator_eq_vertexForm, slash_add_cons p', slash_add_cons p, ← sub_sub,
      ← sub_sub, vertexForm_sub_smul_sub_smul]
  have e0 := (h 0).symm.trans (h' 0)
  have e1 := (h 1).symm.trans (h' 1)
  have e2 := (h (-1)).symm.trans (h' (-1))
  push_cast at e0 e1 e2
  linear_combination (e1 + e2 - 2 * e0) / 2

/-! ### The covariant contraction -/

theorem vertexForm_slash_single (μ β : Fin 4) (i j : Fin 4) :
    vertexForm μ (Dirac.slash (Pi.single β 1)) (Dirac.slash (Pi.single β 1)) i j =
      vertexForm μ (Dirac.gamma β) (Dirac.gamma β) i j := by
  rw [slash_single, vertexForm_smul_left, vertexForm_smul_right, ← mul_assoc,
    ← Complex.ofReal_mul, metric_mul_self, Complex.ofReal_one, one_mul]

/-- `γ^β γ^μ γ_β = 2 γ^μ`. -/
theorem sum_gamma_mul_gamma_mul_gammaLower (μ : Fin 4) :
    ∑ β, Dirac.gamma β * Dirac.gamma μ * Dirac.gammaLower β = (2 : ℂ) • Dirac.gamma μ := by
  have h : Dirac.slash (Minkowski.metric μ μ • Pi.single μ 1) = Dirac.gamma μ := by
    rw [Dirac.slash_smul, slash_single, smul_smul, ← Complex.ofReal_mul, metric_mul_self,
      Complex.ofReal_one, one_smul]
  have := Dirac.contract_slash (Minkowski.metric μ μ • Pi.single μ 1)
  rwa [h] at this

/-- Pulling the sum over `β` inside the outer contraction. -/
theorem sum_metric_smul_sum_gamma (μ : Fin 4) :
    ∑ β, ((Minkowski.metric β β : ℝ) : ℂ) •
        ∑ ν, Dirac.gamma ν * (Dirac.gamma β * Dirac.gamma μ * Dirac.gamma β) * Dirac.gammaLower ν
      = ∑ ν, Dirac.gamma ν *
          (∑ β, Dirac.gamma β * Dirac.gamma μ * Dirac.gammaLower β) * Dirac.gammaLower ν := by
  simp only [gammaLower_eq_smul _, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
    Finset.sum_mul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun β _ => ?_
  rw [smul_comm]

/-- Covariant contraction of the quadratic numerator terms:
`-vF(E₀, E₀) + Σₖ vF(Eₖ, Eₖ) = 4 γ^μ`, with `E_β` the slash of the `β`-th unit vector. -/
theorem neg_vertexForm_time_add_sum_vertexForm_space (μ i j : Fin 4) :
    -vertexForm μ (Dirac.slash (Pi.single 0 1)) (Dirac.slash (Pi.single 0 1)) i j
      + ∑ k : Fin 3, vertexForm μ (Dirac.slash (Pi.single k.succ 1))
          (Dirac.slash (Pi.single k.succ 1)) i j
      = 4 * Dirac.gamma μ i j := by
  have hsum : -vertexForm μ (Dirac.slash (Pi.single 0 1)) (Dirac.slash (Pi.single 0 1)) i j
      + ∑ k : Fin 3, vertexForm μ (Dirac.slash (Pi.single k.succ 1))
          (Dirac.slash (Pi.single k.succ 1)) i j
      = ∑ β, ((Minkowski.metric β β : ℝ) : ℂ) *
          vertexForm μ (Dirac.gamma β) (Dirac.gamma β) i j := by
    conv_rhs => rw [Fin.sum_univ_succ]
    simp [vertexForm_slash_single, Minkowski.metric]
  rw [hsum]
  simp only [vertexForm_eq_sum]
  rw [← Finset.sum_congr rfl fun β _ => (Matrix.smul_apply _ _ i j).trans (smul_eq_mul _ _),
    ← Matrix.sum_apply, sum_metric_smul_sum_gamma, sum_gamma_mul_gamma_mul_gammaLower]
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
  rw [sum_gamma_mul_gamma_mul_gammaLower, smul_smul, Matrix.smul_apply, smul_eq_mul]
  norm_num

/-! ### The numerator at a shifted spatial loop momentum -/

/-- Expansion of `vertexForm` at `(X' - L, X - L)` with `L = Σₖ cₖ Eₖ`. -/
theorem vertexForm_sub_sum_smul (μ : Fin 4) (X' X : Matrix (Fin 4) (Fin 4) ℂ) (c : Fin 3 → ℂ)
    (E : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ (X' - ∑ k, c k • E k) (X - ∑ k, c k • E k) i j =
      vertexForm μ X' X i j - ∑ k, c k * (vertexForm μ X' (E k) i j + vertexForm μ (E k) X i j)
        + ∑ k, ∑ l, c k * c l * vertexForm μ (E k) (E l) i j := by
  rw [vertexForm_sub_left, vertexForm_sub_right, vertexForm_sub_right, vertexForm_sum_smul_left,
    vertexForm_sum_smul_left, vertexForm_sum_smul_right]
  simp only [vertexForm_sum_smul_right, Finset.mul_sum, mul_add, Finset.sum_add_distrib,
    ← mul_assoc]
  ring

/-- With `ℓ = (0, v⃗) - K`, the numerator is quadratic in `v⃗`. -/
theorem vertexNumerator_cons_zero_sub (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (K : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    vertexNumerator m p' p μ ((Fin.cons 0 v : Fin 4 → ℝ) - K) i j =
      vertexNumerator m p' p μ (-K) i j
        - ∑ k : Fin 3, (v k : ℂ) *
            (vertexForm μ ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p' - K))
                (Dirac.slash (Pi.single k.succ 1)) i j
              + vertexForm μ (Dirac.slash (Pi.single k.succ 1))
                ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p - K)) i j)
        + ∑ k : Fin 3, ∑ l : Fin 3, ((v k * v l : ℝ) : ℂ) *
            vertexForm μ (Dirac.slash (Pi.single k.succ 1)) (Dirac.slash (Pi.single l.succ 1))
              i j := by
  set E : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ := fun k => Dirac.slash (Pi.single k.succ 1)
  set X' := (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p' - K)
  set X := (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p - K)
  have hq : ∀ q : Fin 4 → ℝ, q + ((Fin.cons 0 v : Fin 4 → ℝ) - K) = (q - K) + Fin.cons 0 v :=
    fun q => by abel
  have hL := slash_cons_zero v
  rw [vertexNumerator_eq_vertexForm, vertexNumerator_eq_vertexForm, hq, hq, Dirac.slash_add,
    Dirac.slash_add, ← sub_sub, ← sub_sub, hL, ← sub_eq_add_neg, ← sub_eq_add_neg]
  change vertexForm μ (X' - ∑ k, (v k : ℂ) • E k) (X - ∑ k, (v k : ℂ) • E k) i j = _
  rw [vertexForm_sub_sum_smul]
  simp only [Complex.ofReal_mul]
  rfl


/-! ### Radial integrals -/

/-- The Pauli–Villars-paired radial profile `(r + D₁)^{-3/2} - (r + D₂)^{-3/2}`. -/
noncomputable def pairedRpow32 (D₁ D₂ r : ℝ) : ℝ :=
  (r + D₁) ^ (-(3 / 2 : ℝ)) - (r + D₂) ^ (-(3 / 2 : ℝ))

/-- The Pauli–Villars-paired radial profile `(r + D₁)^{-5/2} - (r + D₂)^{-5/2}`. -/
noncomputable def pairedRpow52 (D₁ D₂ r : ℝ) : ℝ :=
  (r + D₁) ^ (-(5 / 2 : ℝ)) - (r + D₂) ^ (-(5 / 2 : ℝ))

theorem sum_sq_nonneg (v : Fin 3 → ℝ) : 0 ≤ ∑ j, v j ^ 2 :=
  Finset.sum_nonneg fun j _ => sq_nonneg (v j)

theorem sq_le_sum_sq (v : Fin 3 → ℝ) (k : Fin 3) : v k ^ 2 ≤ ∑ j, v j ^ 2 :=
  Finset.single_le_sum (f := fun j => v j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)

theorem integrable_pairedRpow32 {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    Integrable fun v : Fin 3 → ℝ => pairedRpow32 D₁ D₂ (∑ j, v j ^ 2) :=
  integrable_sum_sq_add_rpow_neg_three_halves_sub h₁ h₂

theorem integral_pairedRpow32 {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    ∫ v : Fin 3 → ℝ, pairedRpow32 D₁ D₂ (∑ j, v j ^ 2) = 2 * π * Real.log (D₂ / D₁) :=
  integral_sum_sq_add_rpow_neg_three_halves_sub h₁ h₂

theorem integrable_pairedRpow52 {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    Integrable fun v : Fin 3 → ℝ => pairedRpow52 D₁ D₂ (∑ j, v j ^ 2) :=
  (integrable_sum_sq_add_rpow h₁ (by norm_num)).sub (integrable_sum_sq_add_rpow h₂ (by norm_num))

theorem integral_pairedRpow52 {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    ∫ v : Fin 3 → ℝ, pairedRpow52 D₁ D₂ (∑ j, v j ^ 2) = 4 * π / (3 * D₁) - 4 * π / (3 * D₂) := by
  unfold pairedRpow52
  rw [integral_sub (integrable_sum_sq_add_rpow h₁ (by norm_num))
    (integrable_sum_sq_add_rpow h₂ (by norm_num)), integral_sum_sq_add_rpow_neg_five_halves h₁,
    integral_sum_sq_add_rpow_neg_five_halves h₂]

/-- `r (r + D)^{-5/2} = (r + D)^{-3/2} - D (r + D)^{-5/2}`. -/
theorem mul_add_rpow_neg_five_halves {r D : ℝ} (h : 0 < r + D) :
    r * (r + D) ^ (-(5 / 2 : ℝ)) = (r + D) ^ (-(3 / 2 : ℝ)) - D * (r + D) ^ (-(5 / 2 : ℝ)) := by
  have e := Real.rpow_add_one h.ne' (-(5 / 2 : ℝ))
  rw [show -(5 / 2 : ℝ) + 1 = -(3 / 2) by norm_num] at e
  rw [e]
  ring

/-- The radial second moment of the paired `-5/2` profile, rewritten as a combination of
integrable profiles. -/
theorem sum_sq_mul_pairedRpow52 {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) (v : Fin 3 → ℝ) :
    (∑ j, v j ^ 2) * pairedRpow52 D₁ D₂ (∑ j, v j ^ 2) =
      pairedRpow32 D₁ D₂ (∑ j, v j ^ 2) - (D₁ * (∑ j, v j ^ 2 + D₁) ^ (-(5 / 2 : ℝ))
        - D₂ * (∑ j, v j ^ 2 + D₂) ^ (-(5 / 2 : ℝ))) := by
  have hr := sum_sq_nonneg v
  unfold pairedRpow52 pairedRpow32
  rw [mul_sub, mul_add_rpow_neg_five_halves (by positivity),
    mul_add_rpow_neg_five_halves (by positivity)]
  ring

theorem integrable_mul_sub_mul_rpow {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    Integrable fun v : Fin 3 → ℝ => D₁ * (∑ j, v j ^ 2 + D₁) ^ (-(5 / 2 : ℝ))
      - D₂ * (∑ j, v j ^ 2 + D₂) ^ (-(5 / 2 : ℝ)) :=
  ((integrable_sum_sq_add_rpow h₁ (by norm_num)).const_mul D₁).sub
    ((integrable_sum_sq_add_rpow h₂ (by norm_num)).const_mul D₂)

theorem integrable_sum_sq_mul_pairedRpow52 {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    Integrable fun v : Fin 3 → ℝ => (∑ j, v j ^ 2) * pairedRpow52 D₁ D₂ (∑ j, v j ^ 2) := by
  rw [funext (sum_sq_mul_pairedRpow52 h₁ h₂)]
  exact (integrable_pairedRpow32 h₁ h₂).sub (integrable_mul_sub_mul_rpow h₁ h₂)

/-- `∫ |v|² [(|v|² + D₁)^{-5/2} - (|v|² + D₂)^{-5/2}] d³v = 2π log(D₂/D₁)`. -/
theorem integral_sum_sq_mul_pairedRpow52 {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    ∫ v : Fin 3 → ℝ, (∑ j, v j ^ 2) * pairedRpow52 D₁ D₂ (∑ j, v j ^ 2) =
      2 * π * Real.log (D₂ / D₁) := by
  rw [funext (sum_sq_mul_pairedRpow52 h₁ h₂),
    integral_sub (integrable_pairedRpow32 h₁ h₂) (integrable_mul_sub_mul_rpow h₁ h₂),
    integral_sub ((integrable_sum_sq_add_rpow h₁ (by norm_num)).const_mul D₁)
      ((integrable_sum_sq_add_rpow h₂ (by norm_num)).const_mul D₂),
    integral_const_mul, integral_const_mul, integral_sum_sq_add_rpow_neg_five_halves h₁,
    integral_sum_sq_add_rpow_neg_five_halves h₂, integral_pairedRpow32 h₁ h₂]
  field_simp
  ring

/-! ### Moments of radial functions -/

/-- First moments are integrable when `g(|v|²)` and `|v|² g(|v|²)` are, since
`|vₖ| ≤ 1 + |v|²`. -/
theorem integrable_coord_mul_radial {g : ℝ → ℝ}
    (hg : Integrable fun v : Fin 3 → ℝ => g (∑ j, v j ^ 2))
    (hg2 : Integrable fun v : Fin 3 → ℝ => (∑ j, v j ^ 2) * g (∑ j, v j ^ 2)) (k : Fin 3) :
    Integrable fun v : Fin 3 → ℝ => v k * g (∑ j, v j ^ 2) := by
  refine (hg.norm.add hg2.norm).mono'
    ((continuous_apply k).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  have hr := sum_sq_nonneg v
  have hk := sq_le_sum_sq v k
  have hab : |v k| ≤ 1 + ∑ j, v j ^ 2 := by
    nlinarith [sq_abs (v k), sq_nonneg (|v k| - 1), abs_nonneg (v k)]
  simp only [Pi.add_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg hr]
  calc |v k| * |g (∑ j, v j ^ 2)| ≤ (1 + ∑ j, v j ^ 2) * |g (∑ j, v j ^ 2)| :=
        mul_le_mul_of_nonneg_right hab (abs_nonneg _)
    _ = _ := by ring

/-- Second moments are integrable when `|v|² g(|v|²)` is, since `|vₖ vₗ| ≤ |v|²`. -/
theorem integrable_coord_mul_coord_mul_radial {g : ℝ → ℝ}
    (hg : Integrable fun v : Fin 3 → ℝ => g (∑ j, v j ^ 2))
    (hg2 : Integrable fun v : Fin 3 → ℝ => (∑ j, v j ^ 2) * g (∑ j, v j ^ 2)) (k l : Fin 3) :
    Integrable fun v : Fin 3 → ℝ => v k * v l * g (∑ j, v j ^ 2) := by
  refine hg2.norm.mono'
    ((((continuous_apply k).mul (continuous_apply l)).aestronglyMeasurable).mul
      hg.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  have hr := sum_sq_nonneg v
  have hk := sq_le_sum_sq v k
  have hl := sq_le_sum_sq v l
  have hab : |v k| * |v l| ≤ ∑ j, v j ^ 2 := by
    nlinarith [sq_abs (v k), sq_abs (v l), sq_nonneg (|v k| - |v l|)]
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right hab (abs_nonneg _)

theorem integral_coord_mul_pairedRpow52 (D₁ D₂ : ℝ) (k : Fin 3) :
    ∫ v : Fin 3 → ℝ, v k * pairedRpow52 D₁ D₂ (∑ j, v j ^ 2) = 0 :=
  integral_coord_smul_radial (pairedRpow52 D₁ D₂) k

theorem integral_coord_mul_coord_mul_pairedRpow52 (D₁ D₂ : ℝ) {k l : Fin 3} (hkl : k ≠ l) :
    ∫ v : Fin 3 → ℝ, v k * v l * pairedRpow52 D₁ D₂ (∑ j, v j ^ 2) = 0 :=
  integral_coord_mul_coord_smul_radial (pairedRpow52 D₁ D₂) hkl

theorem integral_coord_mul_self_mul_pairedRpow52 {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂)
    (k : Fin 3) :
    ∫ v : Fin 3 → ℝ, v k * v k * pairedRpow52 D₁ D₂ (∑ j, v j ^ 2) =
      2 * π * Real.log (D₂ / D₁) / 3 := by
  have h := integral_coord_sq_smul_radial (pairedRpow52 D₁ D₂)
    (integrable_sum_sq_mul_pairedRpow52 h₁ h₂) k
  simp only [smul_eq_mul] at h
  simp only [← sq]
  rw [h, integral_sum_sq_mul_pairedRpow52 h₁ h₂]
  ring


/-! ### The quadratic radial integrand -/

/-- `A h(|w|²) + B (N₀ - Σₖ wₖ cₖ + Σₖₗ wₖ wₗ Qₖₗ) g(|w|²)`, with `h` and `g` the paired
radial profiles of exponents `-3/2` and `-5/2`. -/
noncomputable def spatialQuadratic (D₁ D₂ : ℝ) (A B N₀ : ℂ) (c : Fin 3 → ℂ)
    (Q : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℝ) : ℂ :=
  A * (pairedRpow32 D₁ D₂ (∑ j, w j ^ 2) : ℂ)
    + B * (N₀ - ∑ k, (w k : ℂ) * c k + ∑ k, ∑ l, ((w k * w l : ℝ) : ℂ) * Q k l)
      * (pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℂ)

theorem spatialQuadratic_eq (D₁ D₂ : ℝ) (A B N₀ : ℂ) (c : Fin 3 → ℂ)
    (Q : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℝ) :
    spatialQuadratic D₁ D₂ A B N₀ c Q w =
      A * (pairedRpow32 D₁ D₂ (∑ j, w j ^ 2) : ℂ)
        + B * N₀ * (pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℂ)
        - ∑ k, B * c k * ((w k * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ)
        + ∑ k, ∑ l, B * Q k l * ((w k * w l * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) := by
  have h1 : ∑ k, B * c k * ((w k * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) =
      B * (∑ k, (w k : ℂ) * c k) * (pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℂ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  have h2 : ∑ k, ∑ l, B * Q k l * ((w k * w l * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) =
      B * (∑ k, ∑ l, ((w k * w l : ℝ) : ℂ) * Q k l) * (pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℂ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by push_cast; ring
  rw [spatialQuadratic, h1, h2]
  ring

theorem integrable_spatialQuadratic {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) (A B N₀ : ℂ)
    (c : Fin 3 → ℂ) (Q : Fin 3 → Fin 3 → ℂ) :
    Integrable (spatialQuadratic D₁ D₂ A B N₀ c Q) := by
  have hg := integrable_pairedRpow52 h₁ h₂
  have hg2 := integrable_sum_sq_mul_pairedRpow52 h₁ h₂
  rw [funext (spatialQuadratic_eq D₁ D₂ A B N₀ c Q)]
  refine ((((integrable_pairedRpow32 h₁ h₂).ofReal.const_mul A).add
    (hg.ofReal.const_mul (B * N₀))).sub (integrable_finsetSum _ fun k _ => ?_)).add
    (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_)
  · exact (integrable_coord_mul_radial hg hg2 k).ofReal.const_mul _
  · exact (integrable_coord_mul_coord_mul_radial hg hg2 k l).ofReal.const_mul _

/-- The integral of the quadratic radial integrand: the linear and mixed terms drop out and each
diagonal term contributes a third of the radial second moment. -/
theorem integral_spatialQuadratic {D₁ D₂ : ℝ} (h₁ : 0 < D₁) (h₂ : 0 < D₂) (A B N₀ : ℂ)
    (c : Fin 3 → ℂ) (Q : Fin 3 → Fin 3 → ℂ) :
    ∫ w, spatialQuadratic D₁ D₂ A B N₀ c Q w =
      A * ((2 * π * Real.log (D₂ / D₁) : ℝ) : ℂ)
        + B * (N₀ * ((4 * π / (3 * D₁) - 4 * π / (3 * D₂) : ℝ) : ℂ)
          + (∑ k, Q k k) * ((2 * π * Real.log (D₂ / D₁) / 3 : ℝ) : ℂ)) := by
  have hg := integrable_pairedRpow52 h₁ h₂
  have hg2 := integrable_sum_sq_mul_pairedRpow52 h₁ h₂
  have iH : Integrable fun w : Fin 3 → ℝ => A * (pairedRpow32 D₁ D₂ (∑ j, w j ^ 2) : ℂ) :=
    (integrable_pairedRpow32 h₁ h₂).ofReal.const_mul A
  have iG : Integrable fun w : Fin 3 → ℝ => B * N₀ * (pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℂ) :=
    hg.ofReal.const_mul _
  have iL : ∀ k ∈ (Finset.univ : Finset (Fin 3)), Integrable fun w : Fin 3 → ℝ =>
      B * c k * ((w k * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) := fun k _ =>
    (integrable_coord_mul_radial hg hg2 k).ofReal.const_mul _
  have iQ : ∀ k l, Integrable fun w : Fin 3 → ℝ =>
      B * Q k l * ((w k * w l * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) := fun k l =>
    (integrable_coord_mul_coord_mul_radial hg hg2 k l).ofReal.const_mul _
  have iQ' : ∀ k ∈ (Finset.univ : Finset (Fin 3)), Integrable fun w : Fin 3 → ℝ =>
      ∑ l, B * Q k l * ((w k * w l * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) := fun k _ =>
    integrable_finsetSum _ fun l _ => iQ k l
  have iHG : Integrable fun w : Fin 3 → ℝ => A * (pairedRpow32 D₁ D₂ (∑ j, w j ^ 2) : ℂ)
      + B * N₀ * (pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℂ) := iH.add iG
  have iS : Integrable fun w : Fin 3 → ℝ =>
      ∑ k, B * c k * ((w k * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) :=
    integrable_finsetSum _ iL
  have iHGS : Integrable fun w : Fin 3 → ℝ => A * (pairedRpow32 D₁ D₂ (∑ j, w j ^ 2) : ℂ)
      + B * N₀ * (pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℂ)
      - ∑ k, B * c k * ((w k * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) := iHG.sub iS
  have iSS : Integrable fun w : Fin 3 → ℝ =>
      ∑ k, ∑ l, B * Q k l * ((w k * w l * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) :=
    integrable_finsetSum _ iQ'
  simp_rw [spatialQuadratic_eq]
  rw [integral_add iHGS iSS, integral_sub iHG iS, integral_add iH iG,
    integral_finsetSum _ iL, integral_finsetSum _ iQ']
  rw [Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => iQ k l]
  simp_rw [integral_const_mul, integral_complex_ofReal,
    integral_pairedRpow32 h₁ h₂, integral_pairedRpow52 h₁ h₂,
    integral_coord_mul_pairedRpow52]
  have hdiag : ∀ k : Fin 3, ∑ l, B * Q k l *
      ((∫ w : Fin 3 → ℝ, w k * w l * pairedRpow52 D₁ D₂ (∑ j, w j ^ 2) : ℝ) : ℂ) =
      B * Q k k * ((2 * π * Real.log (D₂ / D₁) / 3 : ℝ) : ℂ) := fun k => by
    rw [Finset.sum_eq_single k (fun l _ hl => by
      rw [integral_coord_mul_coord_mul_pairedRpow52 D₁ D₂ (Ne.symm hl), ofReal_zero, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), integral_coord_mul_self_mul_pairedRpow52 h₁ h₂]
  simp only [hdiag, ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring


/-! ### The spatial integral of the paired energy integral -/

/-- `(-a, v⃗) = (0, v⃗ + b⃗) - K` for `K = (a, b⃗)`. -/
theorem cons_neg_eq_cons_zero_sub (K : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    (Fin.cons (-K 0) v : Fin 4 → ℝ) = Fin.cons 0 (v + fun k => K k.succ) - K := by
  funext q
  refine Fin.cases ?_ (fun k => ?_) q <;> simp

/-- At `ε = 0`, the Pauli–Villars difference of the energy integrals is the quadratic radial
integrand evaluated at the translated spatial momentum `v⃗ + b⃗`. -/
theorem timeT_zero_sub_eq {m mγ Λ : ℝ} {p' p : Fin 4 → ℝ} (μ i j : Fin 4) {z : ℝ × ℝ}
    (hγ : 0 < feynmanMass m mγ z.1 z.2 p' p) (hΛ : 0 < feynmanMass m Λ z.1 z.2 p' p)
    (v : Fin 3 → ℝ) :
    timeT m mγ 0 p' p μ i j z v - timeT m Λ 0 p' p μ i j z v =
      spatialQuadratic (feynmanMass m mγ z.1 z.2 p' p) (feynmanMass m Λ z.1 z.2 p' p)
        (-(I * (π / 8 : ℂ)) * alphaN m p' p μ i j) (I * (3 * π / 8 : ℂ))
        (vertexNumerator m p' p μ (-shiftK p' p z) i j)
        (fun k => vertexForm μ
            ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p' - shiftK p' p z))
            (Dirac.slash (Pi.single k.succ 1)) i j
          + vertexForm μ (Dirac.slash (Pi.single k.succ 1))
            ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p - shiftK p' p z)) i j)
        (fun k l => vertexForm μ (Dirac.slash (Pi.single k.succ 1))
          (Dirac.slash (Pi.single l.succ 1)) i j)
        (v + fun k => shiftK p' p z k.succ) := by
  set b : Fin 3 → ℝ := fun k => shiftK p' p z k.succ
  have hb : ∀ M, massW m M p' p z v = ∑ j, (v + b) j ^ 2 + feynmanMass m M z.1 z.2 p' p :=
    fun M => rfl
  have hW : ∀ M, 0 < feynmanMass m M z.1 z.2 p' p → 0 < massW m M p' p z v := fun M hM => by
    rw [hb]
    have := sum_sq_nonneg (v + b)
    positivity
  rw [timeT_zero_eq μ i j (hW _ hγ), timeT_zero_eq μ i j (hW _ hΛ),
    cons_neg_eq_cons_zero_sub, vertexNumerator_cons_zero_sub, hb, hb]
  simp only [spatialQuadratic, pairedRpow32, pairedRpow52]
  push_cast
  ring

/-- On the mass shell, the Feynman mass term is positive. -/
theorem feynmanMass_pos_of_pos {m M : ℝ} (hm : 0 < m) (hM : 0 < M) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) {z : ℝ × ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    0 < feynmanMass m M z.1 z.2 p' p :=
  lt_of_lt_of_le (by positivity) (feynmanMass_pos hp' hp hp0' hp0 hz.1 hz.2)

/-- The Pauli–Villars difference of the energy integrals at `ε = 0` is integrable in `v⃗`. -/
theorem integrable_timeT_zero_sub {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) {z : ℝ × ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    Integrable fun v : Fin 3 → ℝ =>
      timeT m mγ 0 p' p μ i j z v - timeT m Λ 0 p' p μ i j z v := by
  have hγ := feynmanMass_pos_of_pos hm hmγ hp' hp hp0' hp0 hz
  have hΛ' := feynmanMass_pos_of_pos hm hΛ hp' hp hp0' hp0 hz
  exact ((integrable_spatialQuadratic hγ hΛ' _ _ _ _ _).comp_add_right _).congr
    (Eventually.of_forall fun v => (timeT_zero_sub_eq μ i j hγ hΛ' v).symm)

/-- The spatial integral at fixed Feynman parameters. -/
theorem integral_timeT_zero_sub {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) {z : ℝ × ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    ∫ v : Fin 3 → ℝ, (timeT m mγ 0 p' p μ i j z v - timeT m Λ 0 p' p μ i j z v) =
      I * ((π ^ 2 * Real.log (feynmanMass m Λ z.1 z.2 p' p / feynmanMass m mγ z.1 z.2 p' p)
          : ℝ) : ℂ) * Dirac.gamma μ i j
        + I * ((π ^ 2 / 2 * ((feynmanMass m mγ z.1 z.2 p' p)⁻¹
            - (feynmanMass m Λ z.1 z.2 p' p)⁻¹) : ℝ) : ℂ)
          * vertexNumerator m p' p μ (-shiftK p' p z) i j := by
  have hγ := feynmanMass_pos_of_pos hm hmγ hp' hp hp0' hp0 hz
  have hΛ' := feynmanMass_pos_of_pos hm hΛ hp' hp hp0' hp0 hz
  rw [funext (timeT_zero_sub_eq μ i j hγ hΛ'), integral_add_right_eq_self
    (spatialQuadratic _ _ _ _ _ _ _), integral_spatialQuadratic hγ hΛ']
  have hQ : ∑ k : Fin 3, vertexForm μ (Dirac.slash (Pi.single k.succ 1))
      (Dirac.slash (Pi.single k.succ 1)) i j = 4 * Dirac.gamma μ i j + alphaN m p' p μ i j := by
    rw [alphaN_eq, cons_one_zero_eq_single]
    linear_combination neg_vertexForm_time_add_sum_vertexForm_space μ i j
  simp only [hQ]
  push_cast
  ring

end QED.OneLoop.VertexLimit

end
