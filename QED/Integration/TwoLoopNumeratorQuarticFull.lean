/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopNumeratorQuartic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The two-loop parametric representation with numerators of degree at most four

Completion of the parametric representation with numerators of degree at most four in the loop
momenta (obligations O2-10 and O2-11, `docs/TWO-LOOP-DERIVATION.md`, section 4.4). The energy
integral is `integral_loopQuartic_mul_prod_lineDenom_eq` (`TwoLoopNumeratorQuartic.lean`); this
file does the spatial integral, Fubini on simplex × space, and the final finite identity.

For `N = m + 1 ≥ 7` propagators `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε` (mostly-plus metric,
`kᵢ = ∑ₛ αᵢₛ ℓₛ + pᵢ`) and a numerator `P` of degree at most four (`LoopQuartic`):
`J[P] = -π⁴ ∫_Δ U⁻² [(N-5)! W^{4-N} P(-S) + (N-6)!/2 W^{5-N} ∑ₐ_b Hₐ_b(-S) Gₐ_b +
(N-7)!/4 W^{6-N} ∑ₐ_bcd Rₐ_bcd Πₐ_bcd(G)]`,
with `W = V - iε`, `S = loopShift α p z` the shift of the completed square,
`G_{(s,μ),(r,ν)} = g_{μν} (A⁻¹)ₛᵣ` (`loopMetricInv`, `g = diag(-1, 1, 1, 1)`), `Hₐ_b(X)` the
coefficients of the part of `P(X + δ)` quadratic in `δ` (`LoopQuartic.hess`), `R` the quartic
coefficients and `Πₐ_bcd(G) = Gₐ_b G_cd + Gₐ_c G_bd + Gₐ_d G_bc` (`matPair`). In terms of `ℓ`:
relative to the scalar normalization `-π⁴ (N-5)! U⁻² W^{4-N}`, `ℓ` is replaced by `-S`, each pair
of loop momenta by `G W/(2(N-5))`, and each quadruple by the three pairings
`Π(G) W²/(4(N-5)(N-6))`.

## Proof

At an interior point of the simplex, the energy-integrated integrand `numEnergyValueQuartic`
(three terms, with kernels `w^{1-N}`, `w^{2-N}`, `w^{3-N}`, `w = (v+σ)ᵀA(v+σ) + W`) is integrated
over the spatial momenta with the even-part lemmas
`integral_mul_inv_quadForm_add_pow_of_even_quartic` (first term),
`integral_mul_inv_quadForm_add_pow_of_even` (second term, whose coefficients `Hₐ_b` are quadratic
in the shift) and `integral_inv_quadForm_shifted_add_pow` (third term). The
results are combined by the finite identities `LoopQuartic.contractTwo_eq` (energy and spatial
parts of `∑ H G`) and `LoopQuartic.contractFour_eq` (energy, mixed and spatial parts of
`∑ R Π(G)`), the latter from the quadratic expansion `sum_mul_matPair_add` of the pairing sum.

For Fubini, each term is bounded at interior points by `C (U⁻² + tr² A · U⁻⁴)` with `C`
independent of the point (`integrable_eval_mul_energyValue_quartic`,
`integrable_energyContractTwo_mul_energyValueTwo`,
`integrable_energyContractFour_mul_energyValueFour`), through the weight comparison
`1 + |v|² ≤ (1 + 2|σ|² + 2 tr A/U)(1 + (v+σ)ᵀA(v+σ))`, the bounds `|(A⁻¹)ₛᵣ| ≤ tr A/U` and
`tr A · U⁻³ ≤ U⁻² + tr² A · U⁻⁴`.

## Hypotheses

* `N ≥ 7` (`6 ≤ m`): the spatial fourth moment against `w^{-m}` needs `m ≥ 6`; for a quartic
  numerator this is overall power counting, `8 + 4 - 2N < 0`.
* Two of the `αᵢ` are linearly independent, `U⁻²` and `tr² A · U⁻⁴` are integrable on the
  simplex. Under `NoSubdivergenceQuartic` (the complement of every direction class has at least
  five lines) both hold (`..._of_criterion`).

The formula was checked numerically before formalization against the spatial moment formulas
applied to a fit of the integrand's polynomial coefficients (relative error below `1e-13`,
`N = 7, 8, 10`).

## Main statements

* `loopMetricInv`, `LoopQuartic.contractTwo`, `LoopQuartic.contractFour`: the contractions.
* `LoopQuartic.contractTwo_eq`, `LoopQuartic.contractFour_eq`: their energy/spatial splittings.
* `integrable_numEnergyValueQuartic`: integrability on simplex × space.
* `factorial_mul_integral_numEnergyValueQuartic`: the spatial integral at an interior point.
* `jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom`: the full representation, with
  the integrability of both stages; `..._of_criterion`: the same under `NoSubdivergenceQuartic`;
  `..._of_integrable`: the same with the two integrabilities on simplex × energies and
  simplex × space as hypotheses.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter Function
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint simplexComb)
open QED.Integration.Spatial (quadForm)

/-! ### The metric contraction -/

/-- `G_{(s,μ),(r,ν)} = g_{μν} (A⁻¹)ₛᵣ`, with `g = diag(-1, 1, 1, 1)`. -/
noncomputable def loopMetricInv (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix LoopIndex LoopIndex ℝ :=
  fun a b => Minkowski.metric a.2 b.2 * A⁻¹ a.1 b.1

/-- The energy block of `loopMetricInv`: `-(A⁻¹)ₛᵣ` on energy pairs, `0` otherwise. -/
noncomputable def energyMetricInv (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix LoopIndex LoopIndex ℝ :=
  fun a b => if a.2 = 0 ∧ b.2 = 0 then -A⁻¹ a.1 b.1 else 0

/-- The spatial block of `loopMetricInv`: `δ_{cd} (A⁻¹)ₛᵣ` on spatial pairs, `0` otherwise. -/
noncomputable def spatialMetricInv (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix LoopIndex LoopIndex ℝ :=
  fun a b => if a.2 ≠ 0 ∧ a.2 = b.2 then A⁻¹ a.1 b.1 else 0

theorem loopMetricInv_eq_add (A : Matrix (Fin 2) (Fin 2) ℝ) :
    loopMetricInv A = energyMetricInv A + spatialMetricInv A := by
  funext a b
  obtain ⟨s, μ⟩ := a
  obtain ⟨r, ν⟩ := b
  simp only [loopMetricInv, energyMetricInv, spatialMetricInv, Matrix.add_apply,
    Minkowski.metric]
  fin_cases μ <;> fin_cases ν <;> simp

section Eval

variable (A : Matrix (Fin 2) (Fin 2) ℝ) (s r : Fin 2)

theorem loopMetricInv_zero_zero : loopMetricInv A (s, 0) (r, 0) = -A⁻¹ s r := by
  simp [loopMetricInv, Minkowski.metric]

theorem loopMetricInv_zero_succ (d : Fin 3) : loopMetricInv A (s, 0) (r, d.succ) = 0 := by
  simp [loopMetricInv, Minkowski.metric, (Fin.succ_ne_zero d).symm]

theorem loopMetricInv_succ_zero (c : Fin 3) : loopMetricInv A (s, c.succ) (r, 0) = 0 := by
  simp [loopMetricInv, Minkowski.metric, Fin.succ_ne_zero c]

theorem ofReal_loopMetricInv_succ_succ (c d : Fin 3) :
    ((loopMetricInv A (s, c.succ) (r, d.succ) : ℝ) : ℂ) = if c = d then (A⁻¹ s r : ℂ) else 0 := by
  by_cases h : c = d
  · subst h
    simp [loopMetricInv, Minkowski.metric, Fin.succ_ne_zero c]
  · simp [loopMetricInv, Minkowski.metric, h]

theorem energyMetricInv_zero_zero : energyMetricInv A (s, 0) (r, 0) = -A⁻¹ s r := by
  simp [energyMetricInv]

theorem energyMetricInv_succ_left (c : Fin 3) (ν : Fin 4) :
    energyMetricInv A (s, c.succ) (r, ν) = 0 := by
  simp [energyMetricInv, Fin.succ_ne_zero c]

theorem energyMetricInv_succ_right (μ : Fin 4) (d : Fin 3) :
    energyMetricInv A (s, μ) (r, d.succ) = 0 := by
  simp [energyMetricInv, Fin.succ_ne_zero d]

theorem spatialMetricInv_zero_left (ν : Fin 4) : spatialMetricInv A (s, 0) (r, ν) = 0 := by
  simp [spatialMetricInv]

theorem spatialMetricInv_zero_right (μ : Fin 4) : spatialMetricInv A (s, μ) (r, 0) = 0 := by
  simp only [spatialMetricInv]
  split_ifs with h
  · exact absurd h.2 h.1
  · rfl

theorem spatialMetricInv_succ_succ (c d : Fin 3) :
    spatialMetricInv A (s, c.succ) (r, d.succ) = if c = d then A⁻¹ s r else 0 := by
  simp [spatialMetricInv, Fin.succ_ne_zero c]

end Eval

/-- A sum over the eight loop components splits into energy and spatial components. -/
theorem sum_loopIndex (f : LoopIndex → ℂ) :
    ∑ a, f a = ∑ s, f (s, 0) + ∑ s, ∑ c : Fin 3, f (s, c.succ) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => Fin.sum_univ_succ _

/-- The pairing sum is quadratic: the contraction of `R` with `Π(B₁ + B₂)` is the sum of the
contractions with `Π(B₁)` and `Π(B₂)` and of the cross term
`∑ (Rₐ_bcd + Rₐ_cbd + Rₐ_cdb + R_cabd + R_cadb + R_cdab) B₁ₐ_b B₂_cd`. -/
theorem sum_mul_matPair_add {ι : Type*} [Fintype ι] (R : ι → ι → ι → ι → ℂ)
    (B₁ B₂ : Matrix ι ι ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (matPair (B₁ + B₂) a b c d : ℂ) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (matPair B₁ a b c d : ℂ) +
      ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (matPair B₂ a b c d : ℂ) +
      ∑ a, ∑ b, ∑ c, ∑ d, (R a b c d + R a c b d + R a c d b + R c a b d + R c a d b +
        R c d a b) * ((B₁ a b * B₂ c d : ℝ) : ℂ) := by
  have p13 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((B₁ a c * B₂ b d : ℝ) : ℂ) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a c b d * ((B₁ a b * B₂ c d : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  have p14 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((B₁ a d * B₂ b c : ℝ) : ℂ) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a c d b * ((B₁ a b * B₂ c d : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  have p23 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((B₁ b c * B₂ a d : ℝ) : ℂ) =
      ∑ a, ∑ b, ∑ c, ∑ d, R c a b d * ((B₁ a b * B₂ c d : ℝ) : ℂ) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  have p24 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((B₁ b d * B₂ a c : ℝ) : ℂ) =
      ∑ a, ∑ b, ∑ c, ∑ d, R c a d b * ((B₁ a b * B₂ c d : ℝ) : ℂ) := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  have p34 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((B₁ c d * B₂ a b : ℝ) : ℂ) =
      ∑ a, ∑ b, ∑ c, ∑ d, R c d a b * ((B₁ a b * B₂ c d : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  have hR : ∑ a, ∑ b, ∑ c, ∑ d, (R a b c d + R a c b d + R a c d b + R c a b d + R c a d b +
        R c d a b) * ((B₁ a b * B₂ c d : ℝ) : ℂ) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((B₁ a b * B₂ c d : ℝ) : ℂ) +
        ∑ a, ∑ b, ∑ c, ∑ d, R a c b d * ((B₁ a b * B₂ c d : ℝ) : ℂ) +
        ∑ a, ∑ b, ∑ c, ∑ d, R a c d b * ((B₁ a b * B₂ c d : ℝ) : ℂ) +
        ∑ a, ∑ b, ∑ c, ∑ d, R c a b d * ((B₁ a b * B₂ c d : ℝ) : ℂ) +
        ∑ a, ∑ b, ∑ c, ∑ d, R c a d b * ((B₁ a b * B₂ c d : ℝ) : ℂ) +
        ∑ a, ∑ b, ∑ c, ∑ d, R c d a b * ((B₁ a b * B₂ c d : ℝ) : ℂ) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hR, ← p13, ← p14, ← p23, ← p24, ← p34]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [matPair, Matrix.add_apply]
  push_cast
  ring

/-! ### The contractions of a numerator of degree at most four -/

namespace LoopQuartic

variable (P : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)

/-- The contraction `∑ₐ_b Hₐ_b(X) Gₐ_b` of the quadratic coefficients with
`G = loopMetricInv A`. -/
noncomputable def contractTwo (X : LoopIndex → ℂ) : ℂ :=
  ∑ a, ∑ b, P.hess X a b * (loopMetricInv A a b : ℂ)

/-- The contraction `∑ Rₐ_bcd Πₐ_bcd(G)` of the quartic coefficients with the pairing sum of
`G = loopMetricInv A`. -/
noncomputable def contractFour : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, P.quart a b c d * (matPair (loopMetricInv A) a b c d : ℂ)

/-- The spatial contraction of the quadratic coefficients, `∑ₛᵣ ∑_c H_{(s,c),(r,c)}(X) (A⁻¹)ₛᵣ`. -/
noncomputable def spatialContractTwo (X : LoopIndex → ℂ) : ℂ :=
  ∑ s, ∑ c : Fin 3, ∑ r, P.hess X (s, c.succ) (r, c.succ) * ((A⁻¹ s r : ℝ) : ℂ)

/-- The mixed contraction of the quartic coefficients: two energy and two spatial indices,
`∑ₜₑq (∑ₛᵣ R^{sym}_{(s,0),(r,0),(t,e),(q,e)} (A⁻¹)ₛᵣ) (A⁻¹)ₜq`. -/
noncomputable def mixedContractFour : ℂ :=
  ∑ t, ∑ e : Fin 3, ∑ q, (∑ s, ∑ r, P.quartSym (s, 0) (r, 0) (t, e.succ) (q, e.succ) *
    ((A⁻¹ s r : ℝ) : ℂ)) * ((A⁻¹ t q : ℝ) : ℂ)

/-- The spatial contraction of the quartic coefficients, `∑ R_{(s,c),(r,d),(t,e),(q,f)} Π`, with
`Π = spatialPair A`. -/
noncomputable def spatialContractFour : ℂ :=
  ∑ s, ∑ c : Fin 3, ∑ r, ∑ d : Fin 3, ∑ t, ∑ e : Fin 3, ∑ q, ∑ f : Fin 3,
    P.quart (s, c.succ) (r, d.succ) (t, e.succ) (q, f.succ) *
      (spatialPair A s c r d t e q f : ℂ)

/-- The metric contraction splits into energy and spatial parts. -/
theorem contractTwo_eq (X : LoopIndex → ℂ) :
    P.contractTwo A X = -P.energyContractTwo A X + P.spatialContractTwo A X := by
  simp only [contractTwo, energyContractTwo, spatialContractTwo, sum_loopIndex,
    loopMetricInv_zero_zero, loopMetricInv_zero_succ, loopMetricInv_succ_zero,
    ofReal_loopMetricInv_succ_succ, ofReal_zero, mul_zero, Finset.sum_const_zero, add_zero,
    zero_add, mul_ite, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ofReal_neg, mul_neg,
    Finset.sum_neg_distrib]

theorem sum_mul_matPair_energyMetricInv :
    ∑ a, ∑ b, ∑ c, ∑ d, P.quart a b c d * (matPair (energyMetricInv A) a b c d : ℂ) =
      P.energyContractFour A := by
  simp only [sum_loopIndex, matPair, energyMetricInv_succ_left, energyMetricInv_succ_right,
    mul_zero, zero_mul, add_zero, ofReal_zero, Finset.sum_const_zero, energyMetricInv_zero_zero,
    neg_mul_neg]
  rfl

theorem sum_mul_matPair_spatialMetricInv :
    ∑ a, ∑ b, ∑ c, ∑ d, P.quart a b c d * (matPair (spatialMetricInv A) a b c d : ℂ) =
      P.spatialContractFour A := by
  simp only [sum_loopIndex, matPair, spatialMetricInv_zero_left, spatialMetricInv_zero_right,
    mul_zero, zero_mul, add_zero, ofReal_zero, Finset.sum_const_zero, zero_add,
    spatialMetricInv_succ_succ]
  rfl

theorem sum_comm_five (F : Fin 2 → Fin 2 → Fin 2 → Fin 3 → Fin 2 → ℂ) :
    ∑ s, ∑ r, ∑ t, ∑ e, ∑ q, F s r t e q = ∑ t, ∑ e, ∑ q, ∑ s, ∑ r, F s r t e q := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  ring

theorem sum_mul_energyMetricInv_mul_spatialMetricInv :
    ∑ a, ∑ b, ∑ c, ∑ d, P.quartSym a b c d *
      ((energyMetricInv A a b * spatialMetricInv A c d : ℝ) : ℂ) = -P.mixedContractFour A := by
  simp only [sum_loopIndex, ofReal_mul, energyMetricInv_succ_left, energyMetricInv_succ_right,
    spatialMetricInv_zero_left, spatialMetricInv_zero_right, mul_zero, zero_mul, add_zero,
    zero_add, ofReal_zero, Finset.sum_const_zero, energyMetricInv_zero_zero,
    spatialMetricInv_succ_succ]
  have hite : ∀ (e f : Fin 3) (t q : Fin 2),
      ((if e = f then A⁻¹ t q else 0 : ℝ) : ℂ) = if e = f then ((A⁻¹ t q : ℝ) : ℂ) else 0 :=
    fun e f t q => by split_ifs <;> simp
  simp only [hite, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [sum_comm_five]
  simp only [mixedContractFour, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun r _ => ?_
  push_cast
  ring

/-- **The pairing contraction splits into energy, mixed and spatial parts.** -/
theorem contractFour_eq :
    P.contractFour A =
      P.energyContractFour A - P.mixedContractFour A + P.spatialContractFour A := by
  rw [contractFour, loopMetricInv_eq_add, sum_mul_matPair_add, sum_mul_matPair_energyMetricInv,
    sum_mul_matPair_spatialMetricInv]
  have := P.sum_mul_energyMetricInv_mul_spatialMetricInv A
  simp only [quartSym] at this
  rw [this]
  ring

end LoopQuartic

/-! ### Spatial components and bounds on the coefficients -/

theorem quartPart_loopComp_spatial (P : LoopQuartic) (y : Fin 2 → Fin 3 → ℝ) :
    P.quartPart (loopComp (loopMomenta 0 y)) =
      ∑ s, ∑ c : Fin 3, ∑ r, ∑ d : Fin 3, ∑ t, ∑ e : Fin 3, ∑ q, ∑ f : Fin 3,
        P.quart (s, c.succ) (r, d.succ) (t, e.succ) (q, f.succ) *
          ((y s c * y r d * y t e * y q f : ℝ) : ℂ) := by
  simp only [LoopQuartic.quartPart, sum_loopIndex, loopComp_loopMomenta_spatial, Fin.cases_zero,
    Fin.cases_succ, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  push_cast
  rfl

theorem norm_loopComp_le (ℓ : Fin 2 → Fin 4 → ℝ) (a : LoopIndex) :
    ‖loopComp ℓ a‖ ≤ 1 + ∑ s, ∑ μ, ℓ s μ ^ 2 := by
  have hle : ∀ s μ, ℓ s μ ^ 2 ≤ ∑ s, ∑ μ, ℓ s μ ^ 2 := fun s μ =>
    (Finset.single_le_sum (fun μ _ => sq_nonneg (ℓ s μ)) (Finset.mem_univ μ)).trans
      (Finset.single_le_sum (f := fun s => ∑ μ, ℓ s μ ^ 2)
        (fun s _ => Finset.sum_nonneg fun μ _ => sq_nonneg (ℓ s μ)) (Finset.mem_univ s))
  rw [loopComp, norm_real, Real.norm_eq_abs]
  nlinarith [hle a.1 a.2, abs_nonneg (ℓ a.1 a.2), sq_abs (ℓ a.1 a.2),
    sq_nonneg (|ℓ a.1 a.2| - 1)]

theorem norm_loopComp_mul_le (ℓ : Fin 2 → Fin 4 → ℝ) (a b : LoopIndex) :
    ‖loopComp ℓ a * loopComp ℓ b‖ ≤ ∑ s, ∑ μ, ℓ s μ ^ 2 := by
  have hle : ∀ s μ, ℓ s μ ^ 2 ≤ ∑ s, ∑ μ, ℓ s μ ^ 2 := fun s μ =>
    (Finset.single_le_sum (fun μ _ => sq_nonneg (ℓ s μ)) (Finset.mem_univ μ)).trans
      (Finset.single_le_sum (f := fun s => ∑ μ, ℓ s μ ^ 2)
        (fun s _ => Finset.sum_nonneg fun μ _ => sq_nonneg (ℓ s μ)) (Finset.mem_univ s))
  rw [loopComp, loopComp, ← ofReal_mul, norm_real, Real.norm_eq_abs, abs_mul]
  nlinarith [hle a.1 a.2, hle b.1 b.2, abs_nonneg (ℓ a.1 a.2), abs_nonneg (ℓ b.1 b.2),
    sq_abs (ℓ a.1 a.2), sq_abs (ℓ b.1 b.2), sq_nonneg (|ℓ a.1 a.2| - |ℓ b.1 b.2|)]

namespace LoopQuartic

variable (P : LoopQuartic)

/-- A bound for the coefficients `Hₐ_b`:
`‖Qₐ_b‖ + ∑_c ‖Kₐ_bc + Kₐ_cb + K_cab‖ + ∑_cd ‖R^{sym}ₐ_bcd‖`. -/
noncomputable def hessBound (a b : LoopIndex) : ℝ :=
  ‖P.quad a b‖ + ∑ c, ‖P.cub a b c + P.cub a c b + P.cub c a b‖ +
    ∑ c, ∑ d, ‖P.quartSym a b c d‖

theorem hessBound_nonneg (a b : LoopIndex) : 0 ≤ P.hessBound a b := by
  unfold hessBound
  positivity

theorem norm_hess_le (X : LoopIndex → ℂ) {S : ℝ} (h1 : ∀ a, ‖X a‖ ≤ 1 + S)
    (h2 : ∀ a b, ‖X a * X b‖ ≤ S) (hS : 0 ≤ S) (a b : LoopIndex) :
    ‖P.hess X a b‖ ≤ P.hessBound a b * (1 + S) := by
  have hq : ‖P.quad a b‖ ≤ ‖P.quad a b‖ * (1 + S) :=
    le_mul_of_one_le_right (norm_nonneg _) (by linarith)
  have hk : ‖∑ c, (P.cub a b c + P.cub a c b + P.cub c a b) * X c‖ ≤
      (∑ c, ‖P.cub a b c + P.cub a c b + P.cub c a b‖) * (1 + S) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h1 c) (norm_nonneg _)
  have hr : ‖∑ c, ∑ d, P.quartSym a b c d * (X c * X d)‖ ≤
      (∑ c, ∑ d, ‖P.quartSym a b c d‖) * (1 + S) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((h2 c d).trans (by linarith)) (norm_nonneg _)
  unfold hess hessBound
  calc _ ≤ ‖P.quad a b‖ + ‖∑ c, (P.cub a b c + P.cub a c b + P.cub c a b) * X c‖ +
        ‖∑ c, ∑ d, P.quartSym a b c d * (X c * X d)‖ := norm_add₃_le
    _ ≤ _ := by
        rw [add_mul, add_mul]
        linarith

/-- `‖∑ₛᵣ H_{(s,0),(r,0)}(X) (A⁻¹)ₛᵣ‖ ≤ (∑ₛᵣ hessBound) (1 + S) tr A / det A`. -/
theorem norm_energyContractTwo_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (X : LoopIndex → ℂ) {S : ℝ} (h1 : ∀ a, ‖X a‖ ≤ 1 + S) (h2 : ∀ a b, ‖X a * X b‖ ≤ S)
    (hS : 0 ≤ S) :
    ‖P.energyContractTwo A X‖ ≤
      (∑ s, ∑ r, P.hessBound (s, 0) (r, 0)) * (1 + S) * (A.trace / A.det) := by
  unfold energyContractTwo
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul (P.norm_hess_le X h1 h2 hS _ _) (abs_inv_apply_le hA s r) (abs_nonneg _)
    (mul_nonneg (P.hessBound_nonneg _ _) (by linarith))

/-- `‖∑ R_{(s,0),(r,0),(t,0),(q,0)} Πₛᵣₜq(A⁻¹)‖ ≤ 3 (∑ ‖R‖) (tr A / det A)²`. -/
theorem norm_energyContractFour_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) :
    ‖P.energyContractFour A‖ ≤
      (∑ s, ∑ r, ∑ t, ∑ q, ‖P.quart (s, 0) (r, 0) (t, 0) (q, 0)‖) *
        (3 * (A.trace / A.det) ^ 2) := by
  have hpair : ∀ s r t q, |matPair A⁻¹ s r t q| ≤ 3 * (A.trace / A.det) ^ 2 := fun s r t q => by
    have h := fun a b => abs_inv_apply_le hA a b
    have h0 := trace_div_det_nonneg hA
    have hp : ∀ a b c d, |A⁻¹ a b * A⁻¹ c d| ≤ (A.trace / A.det) ^ 2 := fun a b c d => by
      rw [abs_mul, sq]
      exact mul_le_mul (h a b) (h c d) (abs_nonneg _) h0
    unfold matPair
    calc _ ≤ |A⁻¹ s r * A⁻¹ t q| + |A⁻¹ s t * A⁻¹ r q| + |A⁻¹ s q * A⁻¹ r t| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ _ := by linarith [hp s r t q, hp s t r q, hp s q r t]
  unfold energyContractFour
  simp only [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hpair s r t q) (norm_nonneg _)

theorem continuous_hess (a b : LoopIndex) : Continuous fun X : LoopIndex → ℂ => P.hess X a b := by
  unfold hess
  fun_prop

theorem continuous_energyContractTwo (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun X : LoopIndex → ℂ => P.energyContractTwo A X := by
  unfold energyContractTwo
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun r _ =>
    (P.continuous_hess _ _).mul continuous_const

/-- The even part of the energy contraction:
`C₂(X + D) + C₂(X - D) = 2 (C₂(X) + ∑ₛᵣ (∑_cd R^{sym}_{(s,0),(r,0),c,d} D_c D_d) (A⁻¹)ₛᵣ)`. -/
theorem energyContractTwo_add_add_sub (A : Matrix (Fin 2) (Fin 2) ℝ) (X D : LoopIndex → ℂ) :
    P.energyContractTwo A (X + D) + P.energyContractTwo A (X - D) =
      2 * (P.energyContractTwo A X + ∑ s, ∑ r,
        (∑ c, ∑ d, P.quartSym (s, 0) (r, 0) c d * (D c * D d)) * ((A⁻¹ s r : ℝ) : ℂ)) := by
  simp only [energyContractTwo]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← add_mul, P.hess_add_add_hess_sub]
  ring

end LoopQuartic

theorem sum_comm_six (F : Fin 2 → Fin 2 → Fin 2 → Fin 3 → Fin 2 → Fin 3 → ℂ) :
    ∑ s, ∑ r, ∑ t, ∑ e, ∑ q, ∑ f, F s r t e q f =
      ∑ t, ∑ e, ∑ q, ∑ f, ∑ s, ∑ r, F s r t e q f := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  ring

/-! ### Real inequalities for the bounds on the simplex -/

theorem inv_sqrt_mul_inv_sqrt_pow_three {U : ℝ} (hU : 0 < U) :
    (Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹ = (U ^ 2)⁻¹ := by
  rw [← mul_inv, ← pow_succ', show 3 + 1 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hU.le]

theorem inv_sqrt_mul_sq_mul_le {U t b : ℝ} (hU : 0 < U) (ht : 0 ≤ t) :
    (Real.sqrt U)⁻¹ * (b + 2 * (t / U)) ^ 2 * (Real.sqrt U ^ 3)⁻¹ ≤
      (2 * b ^ 2 + 8) * ((U ^ 2)⁻¹ + t ^ 2 * (U ^ 4)⁻¹) := by
  have e : (Real.sqrt U)⁻¹ * (b + 2 * (t / U)) ^ 2 * (Real.sqrt U ^ 3)⁻¹ =
      (b + 2 * (t / U)) ^ 2 * (U ^ 2)⁻¹ := by
    rw [← inv_sqrt_mul_inv_sqrt_pow_three hU]
    ring
  have e2 : t ^ 2 * (U ^ 4)⁻¹ = (t / U) ^ 2 * (U ^ 2)⁻¹ := by
    field_simp
  rw [e, e2]
  have ha : 0 ≤ t / U := div_nonneg ht hU.le
  have hi : 0 < (U ^ 2)⁻¹ := by positivity
  set a := t / U
  set i := (U ^ 2)⁻¹
  have : (b + 2 * a) ^ 2 ≤ (2 * b ^ 2 + 8) * (1 + a ^ 2) := by
    nlinarith [sq_nonneg (b - 2 * a), mul_nonneg (sq_nonneg b) (sq_nonneg a)]
  nlinarith [mul_le_mul_of_nonneg_right this hi.le]

theorem inv_sqrt_mul_mul_mul_le {U t b : ℝ} (hU : 0 < U) (ht : 0 ≤ t) (hb : 0 ≤ b) :
    (Real.sqrt U)⁻¹ * (t / U * (b + 2 * (t / U))) * (Real.sqrt U ^ 3)⁻¹ ≤
      (b + 2) * ((U ^ 2)⁻¹ + t ^ 2 * (U ^ 4)⁻¹) := by
  have e : (Real.sqrt U)⁻¹ * (t / U * (b + 2 * (t / U))) * (Real.sqrt U ^ 3)⁻¹ =
      (t / U * (b + 2 * (t / U))) * (U ^ 2)⁻¹ := by
    rw [← inv_sqrt_mul_inv_sqrt_pow_three hU]
    ring
  have e2 : t ^ 2 * (U ^ 4)⁻¹ = (t / U) ^ 2 * (U ^ 2)⁻¹ := by
    field_simp
  rw [e, e2]
  have ha : 0 ≤ t / U := div_nonneg ht hU.le
  have hi : 0 < (U ^ 2)⁻¹ := by positivity
  set a := t / U
  set i := (U ^ 2)⁻¹
  have : a * (b + 2 * a) ≤ (b + 2) * (1 + a ^ 2) := by
    nlinarith [mul_nonneg hb (sq_nonneg (a - 1)), sq_nonneg a]
  nlinarith [mul_le_mul_of_nonneg_right this hi.le]

theorem inv_sqrt_mul_sq_div_mul_le {U t : ℝ} (hU : 0 < U) :
    (Real.sqrt U)⁻¹ * (t / U) ^ 2 * (Real.sqrt U ^ 3)⁻¹ ≤ (U ^ 2)⁻¹ + t ^ 2 * (U ^ 4)⁻¹ := by
  have e : (Real.sqrt U)⁻¹ * (t / U) ^ 2 * (Real.sqrt U ^ 3)⁻¹ = t ^ 2 * (U ^ 4)⁻¹ := by
    rw [mul_right_comm, inv_sqrt_mul_inv_sqrt_pow_three hU]
    field_simp
  rw [e]
  have : 0 ≤ (U ^ 2)⁻¹ := by positivity
  linarith

theorem spatialNormConst_nonneg {k : ℕ} (hk : 4 ≤ k) : 0 ≤ spatialNormConst k := by
  have h4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have a1 : 0 < (k : ℝ) - 1 := by linarith
  have a2 : 0 < (k : ℝ) - 2 := by linarith
  have a3 : 0 < (k : ℝ) - 3 := by linarith
  unfold spatialNormConst
  positivity

/-! ### The spatial integral against a weight of polynomial growth -/

/-- A weight bounded by `C (1 + (v+σ)ᵀA(v+σ))^j` is integrable against
`((v+σ)ᵀA(v+σ) + V - iε)^{-k}` for `k ≥ j + 4`, with the uniform bound on the absolute integral. -/
theorem integrable_mul_inv_quadForm_shifted_and_le {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {V K ε δ : ℝ} (hε : 0 < ε) (hV : |V| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {j k : ℕ} (hjk : j + 4 ≤ k)
    (σ : Fin 2 → Fin 3 → ℝ) {f : (Fin 2 → Fin 3 → ℝ) → ℂ} (hf : Continuous f) {C : ℝ}
    (hb : ∀ v, ‖f v‖ ≤ C * (1 + quadForm A (v + σ)) ^ j) :
    Integrable (fun v => f v *
        ((((quadForm A (v + σ) : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ k)⁻¹) ∧
      ∫ v, ‖f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ k)⁻¹‖ ≤
        C * ((Real.sqrt δ ^ k)⁻¹ * (spatialNormConst (k - j) * (Real.sqrt A.det ^ 3)⁻¹)) := by
  set W : ℂ := (V : ℂ) - (ε : ℂ) * I with hW
  have hw : W.im < 0 := by simp [hW]; linarith
  have hC : 0 ≤ C := by
    have h0 := (norm_nonneg (f 0)).trans (hb 0)
    have hp : 0 < (1 + quadForm A (0 + σ)) ^ j :=
      pow_pos (by linarith [quadForm_nonneg hA (0 + σ)]) j
    exact nonneg_of_mul_nonneg_left h0 hp
  have hint := (integrable_one_add_quadForm_pow_mul_norm hA hw hjk).comp_add_right σ
  have hmeas : AEStronglyMeasurable
      (fun v => f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ k)⁻¹) volume :=
    (hf.mul ((continuous_inv_add_pow hw k).comp
      ((continuous_quadForm A).comp (continuous_id.add continuous_const)))).aestronglyMeasurable
  have hpt : ∀ v, ‖f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ k)⁻¹‖ ≤
      C * ((1 + quadForm A (v + σ)) ^ j * ‖((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ k)⁻¹‖) :=
    fun v => by
      rw [norm_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hb v) (norm_nonneg _)
  refine ⟨(hint.const_mul C).mono' hmeas (Eventually.of_forall hpt), ?_⟩
  calc ∫ v, ‖f v * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ k)⁻¹‖
      ≤ ∫ v, C * ((1 + quadForm A (v + σ)) ^ j *
          ‖((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ k)⁻¹‖) :=
        integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _) (hint.const_mul C)
          (Eventually.of_forall hpt)
    _ = C * ∫ v, (1 + quadForm A v) ^ j * ‖((((quadForm A v : ℝ) : ℂ) + W) ^ k)⁻¹‖ := by
        rw [integral_const_mul, integral_add_right_eq_self (fun v =>
          (1 + quadForm A v) ^ j * ‖((((quadForm A v : ℝ) : ℂ) + W) ^ k)⁻¹‖) σ]
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (integral_one_add_quadForm_pow_mul_norm_le hA hV hδ0 hδ hδε hjk) hC

/-! ### The spatial integrals at a fixed interior point -/

theorem continuous_loopComp : Continuous loopComp :=
  continuous_pi fun a => continuous_ofReal.comp ((continuous_apply a.2).comp (continuous_apply a.1))

section StageB

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

theorem energyValueFour_eq (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    energyValueFour α p M ε x v = -(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2)))) *
      ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
      ((((quadForm (symanzikMatrix α (simplexPoint x))
        (v + spatialShift α p (simplexPoint x)) : ℝ) : ℂ) +
        (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 2))⁻¹ := by
  simp only [energyValueFour, shiftedConst]

/-- The pointwise bound on the first spatial weight. -/
theorem norm_eval_loopMomenta_neg_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (τ : Fin 2 → ℝ) (σ v : Fin 2 → Fin 3 → ℝ) :
    ‖P.eval (loopMomenta (-τ) v)‖ ≤
      P.coeffBound * (1 + ∑ s, τ s ^ 2) ^ 2 *
        (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) ^ 2 *
          (1 + quadForm A (v + σ)) ^ 2 := by
  have h1 := (P.norm_eval_le (loopMomenta (-τ) v)).trans_eq (by
    rw [sum_sq_loopMomenta, sum_sq_neg])
  have h2 := one_add_sum_sum_sq_le hA v σ
  have hτ : 0 ≤ ∑ s, τ s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have hv : 0 ≤ ∑ s, ∑ c, v s c ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  have h3 : 1 + (∑ s, τ s ^ 2 + ∑ s, ∑ c, v s c ^ 2) ≤ (1 + ∑ s, τ s ^ 2) *
      ((1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) * (1 + quadForm A (v + σ))) :=
    calc 1 + (∑ s, τ s ^ 2 + ∑ s, ∑ c, v s c ^ 2)
        ≤ (1 + ∑ s, τ s ^ 2) * (1 + ∑ s, ∑ c, v s c ^ 2) := by nlinarith [mul_nonneg hτ hv]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h4 := pow_le_pow_left₀ (by positivity) h3 2
  calc ‖P.eval (loopMomenta (-τ) v)‖
      ≤ P.coeffBound * (1 + (∑ s, τ s ^ 2 + ∑ s, ∑ c, v s c ^ 2)) ^ 2 := h1
    _ ≤ P.coeffBound * ((1 + ∑ s, τ s ^ 2) *
          ((1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) *
            (1 + quadForm A (v + σ)))) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 P.coeffBound_nonneg
    _ = _ := by ring

/-- The pointwise bound on the second spatial weight. -/
theorem norm_energyContractTwo_loopMomenta_neg_le {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) (τ : Fin 2 → ℝ) (σ v : Fin 2 → Fin 3 → ℝ) :
    ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v))‖ ≤
      (∑ s, ∑ r, P.hessBound (s, 0) (r, 0)) * (A.trace / A.det) * (1 + ∑ s, τ s ^ 2) *
        (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) *
          (1 + quadForm A (v + σ)) ^ 1 := by
  set ℓ := loopMomenta (-τ) v with hℓ
  have hS0 : 0 ≤ ∑ s, ∑ μ, ℓ s μ ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun μ _ => sq_nonneg _
  have h1 := P.norm_energyContractTwo_le hA (loopComp ℓ) (norm_loopComp_le ℓ)
    (norm_loopComp_mul_le ℓ) hS0
  have hS : ∑ s, ∑ μ, ℓ s μ ^ 2 = ∑ s, τ s ^ 2 + ∑ s, ∑ c, v s c ^ 2 := by
    rw [hℓ, sum_sq_loopMomenta, sum_sq_neg]
  rw [hS] at h1
  have h2 := one_add_sum_sum_sq_le hA v σ
  have hτ : 0 ≤ ∑ s, τ s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have hv : 0 ≤ ∑ s, ∑ c, v s c ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  have h3 : 1 + (∑ s, τ s ^ 2 + ∑ s, ∑ c, v s c ^ 2) ≤ (1 + ∑ s, τ s ^ 2) *
      ((1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) * (1 + quadForm A (v + σ))) :=
    calc 1 + (∑ s, τ s ^ 2 + ∑ s, ∑ c, v s c ^ 2)
        ≤ (1 + ∑ s, τ s ^ 2) * (1 + ∑ s, ∑ c, v s c ^ 2) := by nlinarith [mul_nonneg hτ hv]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)
  have hH : 0 ≤ ∑ s, ∑ r, P.hessBound (s, 0) (r, 0) :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun r _ => P.hessBound_nonneg _ _
  have htd := trace_div_det_nonneg hA
  calc _ ≤ (∑ s, ∑ r, P.hessBound (s, 0) (r, 0)) * (1 + (∑ s, τ s ^ 2 + ∑ s, ∑ c, v s c ^ 2)) *
        (A.trace / A.det) := h1
    _ ≤ (∑ s, ∑ r, P.hessBound (s, 0) (r, 0)) * ((1 + ∑ s, τ s ^ 2) *
          ((1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) *
            (1 + quadForm A (v + σ)))) * (A.trace / A.det) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hH) htd
    _ = _ := by ring

theorem trace_nonneg_of_posDef {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) : 0 ≤ A.trace := by
  have h0 : 0 < A 0 0 := hA.diag_pos
  have h1 : 0 < A 1 1 := hA.diag_pos
  rw [trace_fin_two]
  linarith

/-- The first part of `numEnergyValueQuartic` is integrable in the spatial momenta, with a
uniform bound by `U⁻² + tr² A · U⁻⁴`. -/
theorem integrable_eval_mul_energyValue_quartic (hm : 6 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) {K δ : ℝ}
    (hV : |symanzikV α p M (simplexPoint x)| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {Kτ Kσ : ℝ}
    (hτ : ∑ s, energyShift α p (simplexPoint x) s ^ 2 ≤ Kτ)
    (hσ : ∑ s, ∑ c, spatialShift α p (simplexPoint x) s c ^ 2 ≤ Kσ) :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
        P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ,
          ‖P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v‖ ≤
        ‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * P.coeffBound * (1 + Kτ) ^ 2 *
          ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2)) * (2 * (1 + 2 * Kσ) ^ 2 + 8) *
          ((symanzikU α (simplexPoint x) ^ 2)⁻¹ + (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
            (symanzikU α (simplexPoint x) ^ 4)⁻¹) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set U := symanzikU α (simplexPoint x) with hUdef
  have hUpos : 0 < U := hPD.det_pos
  have hAdet : A.det = U := rfl
  set c₀ : ℂ := -(π / (((m + 1 : ℕ) : ℂ) - 1)) with hc₀
  have hfun : ∀ v, P.eval (loopMomenta (-τ) v) * energyValue α p M ε x v =
      c₀ * ((Real.sqrt U : ℝ) : ℂ)⁻¹ * (P.eval (loopMomenta (-τ) v) *
        ((((quadForm A (v + σ) : ℝ) : ℂ) +
          (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹) := fun v => by
    rw [energyValue_eq]
    ring
  have hG := integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 2) (k := m)
    (by omega) σ (P.continuous_eval.comp
      (continuous_loopMomenta.comp (continuous_const.prodMk continuous_id)))
    (fun v => norm_eval_loopMomenta_neg_le P hPD τ σ v)
  refine ⟨?_, ?_⟩
  · simp only [hfun]
    exact hG.1.const_mul _
  · have hn : ∀ v, ‖P.eval (loopMomenta (-τ) v) * energyValue α p M ε x v‖ =
        ‖c₀ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ‖P.eval (loopMomenta (-τ) v) *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹‖ := fun v => by
      rw [hfun, norm_mul]
    simp only [hn]
    rw [integral_const_mul]
    have hsNC := spatialNormConst_nonneg (by omega : 4 ≤ m - 2)
    have htr0 := trace_nonneg_of_posDef hPD
    have hτ0 : 0 ≤ ∑ s, τ s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
    have hσ0 : 0 ≤ ∑ s, ∑ c, σ s c ^ 2 :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
    have hB0 : 0 ≤ 1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / U) := by
      have := div_nonneg htr0 hUpos.le
      linarith
    have hfac : (1 + ∑ s, τ s ^ 2) ^ 2 * (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / U)) ^ 2 ≤
        (1 + Kτ) ^ 2 * (1 + 2 * Kσ + 2 * (A.trace / U)) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 2)
        (pow_le_pow_left₀ hB0 (by linarith) 2) (by positivity) (by positivity)
    have hX : 0 ≤ ‖c₀‖ * P.coeffBound * ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2)) := by
      have := P.coeffBound_nonneg
      positivity
    have hY : 0 ≤ (Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹ := by positivity
    calc ‖c₀ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ∫ v, ‖P.eval (loopMomenta (-τ) v) *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ m)⁻¹‖
        ≤ ‖c₀ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * (P.coeffBound * (1 + ∑ s, τ s ^ 2) ^ 2 *
            (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) ^ 2 *
            ((Real.sqrt δ ^ m)⁻¹ * (spatialNormConst (m - 2) * (Real.sqrt A.det ^ 3)⁻¹))) :=
          mul_le_mul_of_nonneg_left hG.2 (norm_nonneg _)
      _ = (‖c₀‖ * P.coeffBound * ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2))) *
            ((1 + ∑ s, τ s ^ 2) ^ 2 * (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / U)) ^ 2) *
            ((Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹) := by
          rw [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hAdet]
          ring
      _ ≤ (‖c₀‖ * P.coeffBound * ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2))) *
            ((1 + Kτ) ^ 2 * (1 + 2 * Kσ + 2 * (A.trace / U)) ^ 2) *
            ((Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hX) hY
      _ = (‖c₀‖ * P.coeffBound * (1 + Kτ) ^ 2 *
            ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2))) *
            ((Real.sqrt U)⁻¹ * (1 + 2 * Kσ + 2 * (A.trace / U)) ^ 2 * (Real.sqrt U ^ 3)⁻¹) := by
          ring
      _ ≤ (‖c₀‖ * P.coeffBound * (1 + Kτ) ^ 2 *
            ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2))) *
            ((2 * (1 + 2 * Kσ) ^ 2 + 8) * ((U ^ 2)⁻¹ + A.trace ^ 2 * (U ^ 4)⁻¹)) := by
          refine mul_le_mul_of_nonneg_left (inv_sqrt_mul_sq_mul_le hUpos htr0) ?_
          have := P.coeffBound_nonneg
          positivity
      _ = _ := by ring

/-- The second part of `numEnergyValueQuartic` is integrable in the spatial momenta, with a
uniform bound by `U⁻² + tr² A · U⁻⁴`. -/
theorem integrable_energyContractTwo_mul_energyValueTwo (hm : 6 ≤ m) (hε : 0 < ε)
    {x : Fin m → ℝ} (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) {K δ : ℝ}
    (hV : |symanzikV α p M (simplexPoint x)| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {Kτ Kσ : ℝ}
    (hτ : ∑ s, energyShift α p (simplexPoint x) s ^ 2 ≤ Kτ)
    (hσ : ∑ s, ∑ c, spatialShift α p (simplexPoint x) s c ^ 2 ≤ Kσ) :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
        P.energyContractTwo (symanzikMatrix α (simplexPoint x))
          (loopComp (loopMomenta (-energyShift α p (simplexPoint x)) v)) *
        energyValueTwo α p M ε x v) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ,
          ‖P.energyContractTwo (symanzikMatrix α (simplexPoint x))
            (loopComp (loopMomenta (-energyShift α p (simplexPoint x)) v)) *
          energyValueTwo α p M ε x v‖ ≤
        ‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ * (∑ s, ∑ r, P.hessBound (s, 0) (r, 0)) *
          (1 + Kτ) * ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1)) *
          (1 + 2 * Kσ + 2) *
          ((symanzikU α (simplexPoint x) ^ 2)⁻¹ + (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
            (symanzikU α (simplexPoint x) ^ 4)⁻¹) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set U := symanzikU α (simplexPoint x) with hUdef
  have hUpos : 0 < U := hPD.det_pos
  have hAdet : A.det = U := rfl
  set c₂ : ℂ := (π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1))) with hc₂
  set Hb := ∑ s, ∑ r, P.hessBound (s, 0) (r, 0) with hHb
  have hH : 0 ≤ Hb := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun r _ =>
    P.hessBound_nonneg _ _
  have hfun : ∀ v, P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
      energyValueTwo α p M ε x v = c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹ *
        (P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 1))⁻¹) :=
    fun v => by
      rw [energyValueTwo_eq]
      ring
  have hG := integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 1)
    (k := m - 1) (by omega) σ ((P.continuous_energyContractTwo A).comp (continuous_loopComp.comp
      (continuous_loopMomenta.comp (continuous_const.prodMk continuous_id))))
    (fun v => norm_energyContractTwo_loopMomenta_neg_le P hPD τ σ v)
  refine ⟨?_, ?_⟩
  · simp only [hfun]
    exact hG.1.const_mul _
  · have hn : ∀ v, ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
        energyValueTwo α p M ε x v‖ = ‖c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ *
          ‖P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
            ((((quadForm A (v + σ) : ℝ) : ℂ) +
              (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 1))⁻¹‖ :=
      fun v => by rw [hfun, norm_mul]
    simp only [hn]
    rw [integral_const_mul]
    have hsNC := spatialNormConst_nonneg (by omega : 4 ≤ m - 1 - 1)
    have htr0 := trace_nonneg_of_posDef hPD
    have htU : 0 ≤ A.trace / U := div_nonneg htr0 hUpos.le
    have hτ0 : 0 ≤ ∑ s, τ s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
    have hσ0 : 0 ≤ ∑ s, ∑ c, σ s c ^ 2 :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
    have hB0 : 0 ≤ 1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / U) := by linarith
    have hfac : (1 + ∑ s, τ s ^ 2) * (A.trace / U * (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 +
          2 * (A.trace / U))) ≤
        (1 + Kτ) * (A.trace / U * (1 + 2 * Kσ + 2 * (A.trace / U))) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) htU) (by positivity)
        (by linarith)
    have hX : 0 ≤ ‖c₂‖ * Hb * ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1)) := by
      positivity
    have hY : 0 ≤ (Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹ := by positivity
    calc ‖c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ∫ v, ‖P.energyContractTwo A
          (loopComp (loopMomenta (-τ) v)) * ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 1))⁻¹‖
        ≤ ‖c₂ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * (Hb * (A.trace / A.det) * (1 + ∑ s, τ s ^ 2) *
            (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) *
            ((Real.sqrt δ ^ (m - 1))⁻¹ *
              (spatialNormConst (m - 1 - 1) * (Real.sqrt A.det ^ 3)⁻¹))) :=
          mul_le_mul_of_nonneg_left hG.2 (norm_nonneg _)
      _ = (‖c₂‖ * Hb * ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1))) *
            ((1 + ∑ s, τ s ^ 2) * (A.trace / U * (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 +
              2 * (A.trace / U)))) * ((Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹) := by
          rw [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hAdet]
          ring
      _ ≤ (‖c₂‖ * Hb * ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1))) *
            ((1 + Kτ) * (A.trace / U * (1 + 2 * Kσ + 2 * (A.trace / U)))) *
            ((Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hX) hY
      _ = (‖c₂‖ * Hb * (1 + Kτ) * ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1))) *
            ((Real.sqrt U)⁻¹ * (A.trace / U * (1 + 2 * Kσ + 2 * (A.trace / U))) *
              (Real.sqrt U ^ 3)⁻¹) := by
          ring
      _ ≤ (‖c₂‖ * Hb * (1 + Kτ) * ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1))) *
            ((1 + 2 * Kσ + 2) * ((U ^ 2)⁻¹ + A.trace ^ 2 * (U ^ 4)⁻¹)) := by
          have hKσ : 0 ≤ 1 + 2 * Kσ := by linarith
          refine mul_le_mul_of_nonneg_left (inv_sqrt_mul_mul_mul_le hUpos htr0 hKσ) ?_
          have : 0 ≤ 1 + Kτ := by linarith
          positivity
      _ = _ := by ring

/-- The third part of `numEnergyValueQuartic` is integrable in the spatial momenta, with a
uniform bound by `U⁻² + tr² A · U⁻⁴`. -/
theorem integrable_energyContractFour_mul_energyValueFour (hm : 6 ≤ m) (hε : 0 < ε)
    {x : Fin m → ℝ} (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) {K δ : ℝ}
    (hV : |symanzikV α p M (simplexPoint x)| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) :
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
        P.energyContractFour (symanzikMatrix α (simplexPoint x)) * energyValueFour α p M ε x v) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ,
          ‖P.energyContractFour (symanzikMatrix α (simplexPoint x)) *
            energyValueFour α p M ε x v‖ ≤
        ‖-(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2))))‖ *
          ((∑ s, ∑ r, ∑ t, ∑ q, ‖P.quart (s, 0) (r, 0) (t, 0) (q, 0)‖) * 3) *
          ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0)) *
          ((symanzikU α (simplexPoint x) ^ 2)⁻¹ + (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
            (symanzikU α (simplexPoint x) ^ 4)⁻¹) := by
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set U := symanzikU α (simplexPoint x) with hUdef
  have hUpos : 0 < U := hPD.det_pos
  have hAdet : A.det = U := rfl
  set c₄ : ℂ := -(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2)))) with hc₄
  set Rb := ∑ s, ∑ r, ∑ t, ∑ q, ‖P.quart (s, 0) (r, 0) (t, 0) (q, 0)‖ with hRb
  have hR : 0 ≤ Rb := by positivity
  have hfun : ∀ v, P.energyContractFour A * energyValueFour α p M ε x v =
      c₄ * ((Real.sqrt U : ℝ) : ℂ)⁻¹ * (P.energyContractFour A *
        ((((quadForm A (v + σ) : ℝ) : ℂ) +
          (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 2))⁻¹) :=
    fun v => by
      rw [energyValueFour_eq]
      ring
  have hG := integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 0)
    (k := m - 2) (by omega) σ (continuous_const (y := P.energyContractFour A))
    (C := ‖P.energyContractFour A‖) (fun v => by rw [pow_zero, mul_one])
  refine ⟨?_, ?_⟩
  · simp only [hfun]
    exact hG.1.const_mul _
  · have hn : ∀ v, ‖P.energyContractFour A * energyValueFour α p M ε x v‖ =
        ‖c₄ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ‖P.energyContractFour A *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 2))⁻¹‖ :=
      fun v => by rw [hfun, norm_mul]
    simp only [hn]
    rw [integral_const_mul]
    have hsNC := spatialNormConst_nonneg (by omega : 4 ≤ m - 2 - 0)
    have hC4 := P.norm_energyContractFour_le hPD
    rw [hAdet] at hC4
    have hX : 0 ≤ ‖c₄‖ * ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0)) := by
      positivity
    have hY : 0 ≤ (Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹ := by positivity
    calc ‖c₄ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * ∫ v, ‖P.energyContractFour A *
          ((((quadForm A (v + σ) : ℝ) : ℂ) +
            (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) ^ (m - 2))⁻¹‖
        ≤ ‖c₄ * ((Real.sqrt U : ℝ) : ℂ)⁻¹‖ * (‖P.energyContractFour A‖ *
            ((Real.sqrt δ ^ (m - 2))⁻¹ *
              (spatialNormConst (m - 2 - 0) * (Real.sqrt A.det ^ 3)⁻¹))) :=
          mul_le_mul_of_nonneg_left hG.2 (norm_nonneg _)
      _ = (‖c₄‖ * ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0))) *
            ‖P.energyContractFour A‖ * ((Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹) := by
          rw [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hAdet]
          ring
      _ ≤ (‖c₄‖ * ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0))) *
            (Rb * (3 * (A.trace / U) ^ 2)) * ((Real.sqrt U)⁻¹ * (Real.sqrt U ^ 3)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC4 hX) hY
      _ = (‖c₄‖ * (Rb * 3) * ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0))) *
            ((Real.sqrt U)⁻¹ * (A.trace / U) ^ 2 * (Real.sqrt U ^ 3)⁻¹) := by ring
      _ ≤ (‖c₄‖ * (Rb * 3) * ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0))) *
            ((U ^ 2)⁻¹ + A.trace ^ 2 * (U ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left (inv_sqrt_mul_sq_div_mul_le hUpos) (by positivity)
      _ = _ := by ring

end StageB

/-! ### The three spatial integrals at an interior point -/

section StageBIntegrals

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- The spatial integral of the first part of `numEnergyValueQuartic` at an interior point. -/
theorem integral_eval_mul_energyValue_quartic (hm : 6 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) :
    ∫ v : Fin 2 → Fin 3 → ℝ,
        P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v =
      -(π / (((m + 1 : ℕ) : ℂ) - 1)) * ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        (P.eval (loopMomenta (-energyShift α p (simplexPoint x))
            (-spatialShift α p (simplexPoint x))) *
          ((π : ℂ) ^ 3 * (((m : ℂ) - 1) * ((m : ℂ) - 2) * ((m : ℂ) - 3))⁻¹ *
            ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹) +
        P.spatialContractTwo (symanzikMatrix α (simplexPoint x))
            (loopComp (loopMomenta (-energyShift α p (simplexPoint x))
              (-spatialShift α p (simplexPoint x)))) *
          ((π : ℂ) ^ 3 *
            (2 * (((m : ℂ) - 1) * ((m : ℂ) - 2) * ((m : ℂ) - 3) * ((m : ℂ) - 4)))⁻¹ *
            ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹) +
        P.spatialContractFour (symanzikMatrix α (simplexPoint x)) *
          ((π : ℂ) ^ 3 * (4 * (((m : ℂ) - 1) * ((m : ℂ) - 2) * ((m : ℂ) - 3) * ((m : ℂ) - 4) *
            ((m : ℂ) - 5)))⁻¹ *
            ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹)) := by
  obtain ⟨K, hV⟩ : ∃ K, |symanzikV α p M (simplexPoint x)| ≤ K := ⟨_, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans hV
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  have hg := (integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 2) (k := m)
    (by omega) (spatialShift α p (simplexPoint x)) (P.continuous_eval.comp
      (continuous_loopMomenta.comp (continuous_const.prodMk continuous_id)))
    (fun v => norm_eval_loopMomenta_neg_le P hPD (energyShift α p (simplexPoint x))
      (spatialShift α p (simplexPoint x)) v)).1
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set W : ℂ := ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I with hWdef
  have hw : W.im < 0 := by simp [hWdef]; linarith
  have hfun : (fun v : Fin 2 → Fin 3 → ℝ => P.eval (loopMomenta (-τ) v) *
      energyValue α p M ε x v) = fun v => -(π / (((m + 1 : ℕ) : ℂ) - 1)) *
        ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        (P.eval (loopMomenta (-τ) v) * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m)⁻¹) := by
    funext v
    rw [energyValue_eq]
    ring
  rw [hfun, integral_const_mul]
  congr 1
  have hshift := integral_add_right_eq_self (μ := volume) (fun y : Fin 2 → Fin 3 → ℝ =>
    P.eval (loopMomenta (-τ) (y - σ)) * ((((quadForm A y : ℝ) : ℂ) + W) ^ m)⁻¹) σ
  simp only [add_sub_cancel_right] at hshift
  rw [hshift]
  have hg' : Integrable fun v : Fin 2 → Fin 3 → ℝ =>
      P.eval (loopMomenta (-τ) v) * ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ m)⁻¹ := hg
  have hint' : Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      P.eval (loopMomenta (-τ) (y - σ)) * ((((quadForm A y : ℝ) : ℂ) + W) ^ m)⁻¹ := by
    have := hg'.comp_sub_right σ
    simpa only [sub_add_cancel] using this
  set X := loopComp (loopMomenta (-τ) (-σ)) with hX
  have heven : ∀ y : Fin 2 → Fin 3 → ℝ, P.eval (loopMomenta (-τ) (y - σ)) +
      P.eval (loopMomenta (-τ) (-y - σ)) =
      2 * (P.eval (loopMomenta (-τ) (-σ)) + ∑ s, ∑ c : Fin 3, ∑ r, ∑ d : Fin 3,
        P.hess X (s, c.succ) (r, d.succ) * ((y s c * y r d : ℝ) : ℂ) +
        ∑ s, ∑ c : Fin 3, ∑ r, ∑ d : Fin 3, ∑ t, ∑ e : Fin 3, ∑ q, ∑ f : Fin 3,
          P.quart (s, c.succ) (r, d.succ) (t, e.succ) (q, f.succ) *
            ((y s c * y r d * y t e * y q f : ℝ) : ℂ)) := fun y => by
    have e1 : loopMomenta (-τ) (y - σ) = loopMomenta (-τ) (-σ) + loopMomenta 0 y := by
      rw [← loopMomenta_add, add_zero, neg_add_eq_sub]
    have e2 : loopMomenta (-τ) (-y - σ) = loopMomenta (-τ) (-σ) - loopMomenta 0 y := by
      rw [← loopMomenta_sub, sub_zero]
      congr 1
      abel
    rw [e1, e2, LoopQuartic.eval_add_add_eval_sub, sum_sum_mul_loopComp_spatial,
      quartPart_loopComp_spatial]
  rw [integral_mul_inv_quadForm_add_pow_of_even_quartic hPD hw hm hint'
    (P.eval (loopMomenta (-τ) (-σ))) (fun s c r d => P.hess X (s, c.succ) (r, d.succ))
    (fun s c r d t e q f => P.quart (s, c.succ) (r, d.succ) (t, e.succ) (q, f.succ)) heven]
  rfl

/-- The spatial integral of the second part of `numEnergyValueQuartic` at an interior point. -/
theorem integral_energyContractTwo_mul_energyValueTwo (hm : 6 ≤ m) (hε : 0 < ε)
    {x : Fin m → ℝ} (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) :
    ∫ v : Fin 2 → Fin 3 → ℝ,
        P.energyContractTwo (symanzikMatrix α (simplexPoint x))
          (loopComp (loopMomenta (-energyShift α p (simplexPoint x)) v)) *
        energyValueTwo α p M ε x v =
      (π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1))) *
        ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        (P.energyContractTwo (symanzikMatrix α (simplexPoint x))
            (loopComp (loopMomenta (-energyShift α p (simplexPoint x))
              (-spatialShift α p (simplexPoint x)))) *
          ((π : ℂ) ^ 3 * ((((m - 1 : ℕ) : ℂ) - 1) * (((m - 1 : ℕ) : ℂ) - 2) *
            (((m - 1 : ℕ) : ℂ) - 3))⁻¹ *
            ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 1 - 3))⁻¹) +
        P.mixedContractFour (symanzikMatrix α (simplexPoint x)) *
          ((π : ℂ) ^ 3 * (2 * ((((m - 1 : ℕ) : ℂ) - 1) * (((m - 1 : ℕ) : ℂ) - 2) *
            (((m - 1 : ℕ) : ℂ) - 3) * (((m - 1 : ℕ) : ℂ) - 4)))⁻¹ *
            ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 1 - 4))⁻¹)) := by
  obtain ⟨K, hV⟩ : ∃ K, |symanzikV α p M (simplexPoint x)| ≤ K := ⟨_, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans hV
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  have hg := (integrable_mul_inv_quadForm_shifted_and_le hPD hε hV hδ0 hδ hδε (j := 1)
    (k := m - 1) (by omega) (spatialShift α p (simplexPoint x))
    ((P.continuous_energyContractTwo (symanzikMatrix α (simplexPoint x))).comp
      (continuous_loopComp.comp
        (continuous_loopMomenta.comp (continuous_const.prodMk continuous_id))))
    (fun v => norm_energyContractTwo_loopMomenta_neg_le P hPD (energyShift α p (simplexPoint x))
      (spatialShift α p (simplexPoint x)) v)).1
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set σ := spatialShift α p (simplexPoint x) with hσdef
  set W : ℂ := ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I with hWdef
  have hw : W.im < 0 := by simp [hWdef]; linarith
  have hfun : (fun v : Fin 2 → Fin 3 → ℝ => P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
      energyValueTwo α p M ε x v) = fun v => (π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1))) *
        ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        (P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
          ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ (m - 1))⁻¹) := by
    funext v
    rw [energyValueTwo_eq]
    ring
  rw [hfun, integral_const_mul]
  congr 1
  have hshift := integral_add_right_eq_self (μ := volume) (fun y : Fin 2 → Fin 3 → ℝ =>
    P.energyContractTwo A (loopComp (loopMomenta (-τ) (y - σ))) *
      ((((quadForm A y : ℝ) : ℂ) + W) ^ (m - 1))⁻¹) σ
  simp only [add_sub_cancel_right] at hshift
  rw [hshift]
  have hg' : Integrable fun v : Fin 2 → Fin 3 → ℝ =>
      P.energyContractTwo A (loopComp (loopMomenta (-τ) v)) *
        ((((quadForm A (v + σ) : ℝ) : ℂ) + W) ^ (m - 1))⁻¹ := hg
  have hint' : Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      P.energyContractTwo A (loopComp (loopMomenta (-τ) (y - σ))) *
        ((((quadForm A y : ℝ) : ℂ) + W) ^ (m - 1))⁻¹ := by
    have := hg'.comp_sub_right σ
    simpa only [sub_add_cancel] using this
  set X := loopComp (loopMomenta (-τ) (-σ)) with hX
  have heven : ∀ y : Fin 2 → Fin 3 → ℝ,
      P.energyContractTwo A (loopComp (loopMomenta (-τ) (y - σ))) +
        P.energyContractTwo A (loopComp (loopMomenta (-τ) (-y - σ))) =
      2 * (P.energyContractTwo A X + ∑ t, ∑ e : Fin 3, ∑ q, ∑ f : Fin 3,
        (∑ s, ∑ r, P.quartSym (s, 0) (r, 0) (t, e.succ) (q, f.succ) * ((A⁻¹ s r : ℝ) : ℂ)) *
          ((y t e * y q f : ℝ) : ℂ)) := fun y => by
    have e1 : loopMomenta (-τ) (y - σ) = loopMomenta (-τ) (-σ) + loopMomenta 0 y := by
      rw [← loopMomenta_add, add_zero, neg_add_eq_sub]
    have e2 : loopMomenta (-τ) (-y - σ) = loopMomenta (-τ) (-σ) - loopMomenta 0 y := by
      rw [← loopMomenta_sub, sub_zero]
      congr 1
      abel
    rw [e1, e2, loopComp_add, loopComp_sub, P.energyContractTwo_add_add_sub]
    congr 2
    simp only [sum_sum_mul_loopComp_spatial, Finset.sum_mul]
    rw [sum_comm_six]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun f _ =>
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [integral_mul_inv_quadForm_add_pow_of_even hPD hw (by omega) hint'
    (P.energyContractTwo A X) (fun t e q f => ∑ s, ∑ r,
      P.quartSym (s, 0) (r, 0) (t, e.succ) (q, f.succ) * ((A⁻¹ s r : ℝ) : ℂ)) heven]
  rfl

/-- The spatial integral of the third part of `numEnergyValueQuartic` at an interior point. -/
theorem integral_energyContractFour_mul_energyValueFour (hm : 6 ≤ m) (hε : 0 < ε)
    {x : Fin m → ℝ} (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) :
    ∫ v : Fin 2 → Fin 3 → ℝ,
        P.energyContractFour (symanzikMatrix α (simplexPoint x)) * energyValueFour α p M ε x v =
      P.energyContractFour (symanzikMatrix α (simplexPoint x)) *
        -(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2)))) *
        ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
        ((π : ℂ) ^ 3 * ((((m - 2 : ℕ) : ℂ) - 1) * (((m - 2 : ℕ) : ℂ) - 2) *
          (((m - 2 : ℕ) : ℂ) - 3))⁻¹ *
          ((Real.sqrt (symanzikMatrix α (simplexPoint x)).det ^ 3 : ℝ) : ℂ)⁻¹ *
          ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 2 - 3))⁻¹) := by
  have hw : (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I).im < 0 := by
    simp; linarith
  simp only [energyValueFour_eq]
  simp only [← mul_assoc]
  rw [integral_const_mul, integral_inv_quadForm_shifted_add_pow hPD hw (by omega)]
  ring

end StageBIntegrals

/-! ### Fubini on simplex × space and the representation -/

section Main

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

theorem measurable_energyValueFour (hε : ε ≠ 0) :
    Measurable fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) => energyValueFour α p M ε q.1 q.2 := by
  have hZ := (continuous_simplexPoint' (m := m)).measurable
  have hA : Measurable fun x : Fin m → ℝ => symanzikMatrix α (simplexPoint x) :=
    (continuous_symanzikMatrix α).measurable.comp hZ
  have hσ := (measurable_spatialShift α p).comp hZ
  have hV := (measurable_symanzikV α p M).comp hZ
  have hΨ := (continuous_quadForm_inv (m := m - 2) hε).measurable.comp
    ((hA.comp measurable_fst).prodMk (((measurable_snd).add (hσ.comp measurable_fst)).prodMk
      (hV.comp measurable_fst)))
  have hU : Measurable fun x : Fin m → ℝ =>
      ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ :=
    (continuous_ofReal.comp (continuous_symanzikU_simplexPoint α).sqrt).measurable.inv
  exact (measurable_const.mul (hU.comp measurable_fst)).mul hΨ

theorem measurable_energyContractFour :
    Measurable fun x : Fin m → ℝ => P.energyContractFour (symanzikMatrix α (simplexPoint x)) := by
  have hZ := (continuous_simplexPoint' (m := m)).measurable
  have hinv := (measurable_symanzikMatrix_inv α).comp hZ
  have he : ∀ a b : Fin 2, Measurable fun x : Fin m → ℝ =>
      (symanzikMatrix α (simplexPoint x))⁻¹ a b := fun a b => hinv.eval_matrix
  unfold LoopQuartic.energyContractFour matPair
  exact Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun r _ =>
    Finset.measurable_sum _ fun t _ => Finset.measurable_sum _ fun q _ =>
      measurable_const.mul (Complex.measurable_ofReal.comp
        ((((he s r).mul (he t q)).add ((he s t).mul (he r q))).add ((he s q).mul (he r t))))

theorem measurable_energyContractTwo_loopMomenta :
    Measurable fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.energyContractTwo (symanzikMatrix α (simplexPoint q.1))
        (loopComp (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2)) := by
  have hZ := (continuous_simplexPoint' (m := m)).measurable
  have hinv := (measurable_symanzikMatrix_inv α).comp hZ
  have hτ := (measurable_energyShift α p).comp hZ
  have hX : Measurable fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      loopComp (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2) :=
    continuous_loopComp.measurable.comp (continuous_loopMomenta.measurable.comp
      ((hτ.neg.comp measurable_fst).prodMk measurable_snd))
  unfold LoopQuartic.energyContractTwo
  exact Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun r _ =>
    ((P.continuous_hess _ _).measurable.comp hX).mul
      (Complex.measurable_ofReal.comp (hinv.eval_matrix.comp measurable_fst))

theorem measurable_eval_loopMomenta_quartic :
    Measurable fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.eval (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2) := by
  have hZ := (continuous_simplexPoint' (m := m)).measurable
  have hτ := (measurable_energyShift α p).comp hZ
  exact P.continuous_eval.measurable.comp (continuous_loopMomenta.measurable.comp
    ((hτ.neg.comp measurable_fst).prodMk measurable_snd))

/-- The energy-integrated integrand with a numerator of degree at most four is integrable on
simplex × space (`N ≥ 7`). -/
theorem integrable_numEnergyValueQuartic (hm : 6 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (hA : IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
      (symanzikU α (simplexPoint x) ^ 4)⁻¹) (simplexSet m)) :
    Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
        numEnergyValueQuartic P α p M ε q.1 q.2)
      ((volume.restrict (simplexSet m)).prod volume) := by
  have hm0 : 0 < m := by omega
  set K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  obtain ⟨Kτ, hKτ⟩ := exists_sum_sq_energyShift_le α p
  obtain ⟨Kσ, hKσ⟩ := exists_sum_sq_spatialShift_le α p
  have hUA := hU.add hA
  -- the first part
  have h1 : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.eval (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2) *
        energyValue α p M ε q.1 q.2) ((volume.restrict (simplexSet m)).prod volume) := by
    have hmeas := ((measurable_eval_loopMomenta_quartic P α p).mul
      (measurable_energyValue α p M hε.ne')).aestronglyMeasurable
      (μ := (volume.restrict (simplexSet m)).prod volume)
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      exact (integrable_eval_mul_energyValue_quartic P α p M hm hε hPD
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).1
    · refine (hUA.const_mul (‖-(π / (((m + 1 : ℕ) : ℂ) - 1))‖ * P.coeffBound * (1 + Kτ) ^ 2 *
        ((Real.sqrt δ ^ m)⁻¹ * spatialNormConst (m - 2)) * (2 * (1 + 2 * Kσ) ^ 2 + 8))).mono'
        hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_eval_mul_energyValue_quartic P α p M hm hε hPD
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).2
  -- the second part
  have h2 : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.energyContractTwo (symanzikMatrix α (simplexPoint q.1))
          (loopComp (loopMomenta (-energyShift α p (simplexPoint q.1)) q.2)) *
        energyValueTwo α p M ε q.1 q.2) ((volume.restrict (simplexSet m)).prod volume) := by
    have hmeas := ((measurable_energyContractTwo_loopMomenta P α p).mul
      (measurable_energyValueTwo α p M hε.ne')).aestronglyMeasurable
      (μ := (volume.restrict (simplexSet m)).prod volume)
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      exact (integrable_energyContractTwo_mul_energyValueTwo P α p M hm hε hPD
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).1
    · refine (hUA.const_mul (‖(π : ℂ) / (2 * ((m : ℂ) * ((m : ℂ) - 1)))‖ *
        (∑ s, ∑ r, P.hessBound (s, 0) (r, 0)) * (1 + Kτ) *
        ((Real.sqrt δ ^ (m - 1))⁻¹ * spatialNormConst (m - 1 - 1)) * (1 + 2 * Kσ + 2))).mono'
        hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_energyContractTwo_mul_energyValueTwo P α p M hm hε hPD
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε (hKτ _ hz.1 hdet)
        (hKσ _ hz.1 hdet)).2
  -- the third part
  have h3 : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      P.energyContractFour (symanzikMatrix α (simplexPoint q.1)) *
        energyValueFour α p M ε q.1 q.2) ((volume.restrict (simplexSet m)).prod volume) := by
    have hmeas := (((measurable_energyContractFour P α).comp measurable_fst).mul
      (measurable_energyValueFour α p M hε.ne')).aestronglyMeasurable
      (μ := (volume.restrict (simplexSet m)).prod volume)
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      exact (integrable_energyContractFour_mul_energyValueFour P α p M hm hε hPD
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε).1
    · refine (hUA.const_mul (‖-(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2))))‖ *
        ((∑ s, ∑ r, ∑ t, ∑ q, ‖P.quart (s, 0) (r, 0) (t, 0) (q, 0)‖) * 3) *
        ((Real.sqrt δ ^ (m - 2))⁻¹ * spatialNormConst (m - 2 - 0)))).mono'
        hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      have hz := Feynman.simplexPoint_mem_stdSimplex hxS
      have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact (integrable_energyContractFour_mul_energyValueFour P α p M hm hε hPD
        (abs_symanzikV_le α p M hz.1 hz.2 hdet) hδ0 hδ hδε).2
  exact (h1.add h2).add h3

end Main

/-! ### The representation -/

section Representation

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- At an interior point, `m!` times the spatial integral of `numEnergyValueQuartic` is the
integrand of the representation. -/
theorem factorial_mul_integral_numEnergyValueQuartic (hm : 6 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) :
    (m.factorial : ℂ) * ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValueQuartic P α p M ε x v =
      -((π : ℂ) ^ 4) * (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            P.eval (-loopShift α p (simplexPoint x)) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            P.contractTwo (symanzikMatrix α (simplexPoint x))
              (loopComp (-loopShift α p (simplexPoint x))) +
          ((m - 6).factorial : ℂ) / 4 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹ *
            P.contractFour (symanzikMatrix α (simplexPoint x)))) := by
  have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
  obtain ⟨K, hV⟩ : ∃ K, |symanzikV α p M (simplexPoint x)| ≤ K := ⟨_, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans hV
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  have i1 := (integrable_eval_mul_energyValue_quartic P α p M hm hε hPD hV hδ0 hδ hδε le_rfl
    le_rfl).1
  have i2 := (integrable_energyContractTwo_mul_energyValueTwo P α p M hm hε hPD hV hδ0 hδ hδε
    le_rfl le_rfl).1
  have i3 := (integrable_energyContractFour_mul_energyValueFour P α p M hm hε hPD hV hδ0 hδ
    hδε).1
  have hsplit : ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValueQuartic P α p M ε x v =
      (∫ v : Fin 2 → Fin 3 → ℝ, P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) *
        energyValue α p M ε x v) +
      (∫ v : Fin 2 → Fin 3 → ℝ, P.energyContractTwo (symanzikMatrix α (simplexPoint x))
          (loopComp (loopMomenta (-energyShift α p (simplexPoint x)) v)) *
        energyValueTwo α p M ε x v) +
      ∫ v : Fin 2 → Fin 3 → ℝ, P.energyContractFour (symanzikMatrix α (simplexPoint x)) *
        energyValueFour α p M ε x v := by
    rw [← integral_add i1 i2]
    exact integral_add (i1.add i2) i3
  rw [hsplit, integral_eval_mul_energyValue_quartic P α p M hm hε hPD,
    integral_energyContractTwo_mul_energyValueTwo P α p M hm hε hPD,
    integral_energyContractFour_mul_energyValueFour P α p M hm hε hPD,
    LoopQuartic.contractTwo_eq, LoopQuartic.contractFour_eq]
  have hneg : -loopShift α p (simplexPoint x) =
      loopMomenta (-energyShift α p (simplexPoint x)) (-spatialShift α p (simplexPoint x)) := by
    rw [loopShift, loopMomenta_neg]
  rw [hneg]
  have hAdet : (symanzikMatrix α (simplexPoint x)).det = symanzikU α (simplexPoint x) := rfl
  rw [hAdet]
  set a := P.eval (loopMomenta (-energyShift α p (simplexPoint x))
    (-spatialShift α p (simplexPoint x)))
  set e2 := P.energyContractTwo (symanzikMatrix α (simplexPoint x))
    (loopComp (loopMomenta (-energyShift α p (simplexPoint x))
      (-spatialShift α p (simplexPoint x))))
  set s2 := P.spatialContractTwo (symanzikMatrix α (simplexPoint x))
    (loopComp (loopMomenta (-energyShift α p (simplexPoint x))
      (-spatialShift α p (simplexPoint x))))
  set e4 := P.energyContractFour (symanzikMatrix α (simplexPoint x))
  set x4 := P.mixedContractFour (symanzikMatrix α (simplexPoint x))
  set s4 := P.spatialContractFour (symanzikMatrix α (simplexPoint x))
  set W : ℂ := ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I with hW
  have hW0 : W ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hW] at this
    linarith
  set sU := Real.sqrt (symanzikU α (simplexPoint x)) with hsU
  have hsU0 : (sU : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hUpos).ne'
  have hUs : symanzikU α (simplexPoint x) = sU ^ 2 := (Real.sq_sqrt hUpos.le).symm
  rw [hUs]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  rw [show k + 6 - 1 - 3 = k + 2 by omega, show k + 6 - 1 - 4 = k + 1 by omega,
    show k + 6 - 2 - 3 = k + 1 by omega, show k + 6 - 3 = k + 3 by omega,
    show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega,
    show k + 6 - 6 = k by omega,
    show ((k + 6 - 1 : ℕ) : ℂ) = (k : ℂ) + 5 by push_cast [show k + 6 - 1 = k + 5 by omega]; ring,
    show ((k + 6 - 2 : ℕ) : ℂ) = (k : ℂ) + 4 by push_cast [show k + 6 - 2 = k + 4 by omega]; ring,
    show (k + 6).factorial =
      (k + 6) * (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) * k.factorial by
      simp only [Nat.factorial_succ]; ring,
    show (k + 2).factorial = (k + 2) * (k + 1) * k.factorial by
      simp only [Nat.factorial_succ]; ring,
    show (k + 1).factorial = (k + 1) * k.factorial by simp only [Nat.factorial_succ]]
  push_cast
  have e1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  have e2' : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : k + 2 ≠ 0)
  have e3 : (k : ℂ) + 3 ≠ 0 := by exact_mod_cast (by omega : k + 3 ≠ 0)
  have e4' : (k : ℂ) + 4 ≠ 0 := by exact_mod_cast (by omega : k + 4 ≠ 0)
  have e5 : (k : ℂ) + 5 ≠ 0 := by exact_mod_cast (by omega : k + 5 ≠ 0)
  have e6 : (k : ℂ) + 6 ≠ 0 := by exact_mod_cast (by omega : k + 6 ≠ 0)
  have r0 : (k : ℂ) + 6 + 1 - 1 = (k : ℂ) + 6 := by ring
  have r1 : (k : ℂ) + 6 - 1 = (k : ℂ) + 5 := by ring
  have r2 : (k : ℂ) + 6 - 2 = (k : ℂ) + 4 := by ring
  have r3 : (k : ℂ) + 6 - 3 = (k : ℂ) + 3 := by ring
  have r4 : (k : ℂ) + 6 - 4 = (k : ℂ) + 2 := by ring
  have r5 : (k : ℂ) + 6 - 5 = (k : ℂ) + 1 := by ring
  have r6 : (k : ℂ) + 5 - 1 = (k : ℂ) + 4 := by ring
  have r7 : (k : ℂ) + 5 - 2 = (k : ℂ) + 3 := by ring
  have r8 : (k : ℂ) + 5 - 3 = (k : ℂ) + 2 := by ring
  have r9 : (k : ℂ) + 5 - 4 = (k : ℂ) + 1 := by ring
  have r10 : (k : ℂ) + 4 - 1 = (k : ℂ) + 3 := by ring
  have r11 : (k : ℂ) + 4 - 2 = (k : ℂ) + 2 := by ring
  have r12 : (k : ℂ) + 4 - 3 = (k : ℂ) + 1 := by ring
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  field_simp
  ring

/-- **The two-loop parametric representation with a numerator of degree at most four**
(O2-10/O2-11 infrastructure). For `N = m + 1 ≥ 7` propagators with line momenta
`kᵢ(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ`, masses `Mᵢ`, `ε > 0`, two linearly independent `αᵢ`, `U⁻²` and
`tr² A · U⁻⁴` integrable on the simplex, and a numerator `P` of degree at most four
(`LoopQuartic`): both stages of the joint energy-first integral of `P ∏ᵢ Dᵢ⁻¹`,
`Dᵢ = kᵢ·kᵢ + Mᵢ² - iε`, are integrable, and
`jointEnergyFirstIntegral 2 (P ∏ᵢ Dᵢ⁻¹) = -π⁴ ∫_Δ U⁻² ((N-5)! W^{4-N} P(-S) +
(N-6)!/2 W^{5-N} ∑ₐ_b Hₐ_b(-S) Gₐ_b + (N-7)!/4 W^{6-N} ∑ Rₐ_bcd Πₐ_bcd(G)) dx`,
with `W = V - iε`, `S = loopShift α p z`, `G_{(s,μ),(r,ν)} = g_{μν} (A⁻¹)ₛᵣ` (`loopMetricInv`),
`Hₐ_b` the coefficients of the part of `P(-S + δ)` quadratic in `δ` (`LoopQuartic.hess`), and
`Π(G)` the pairing sum (`matPair`). -/
theorem jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom (hm : 6 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (hA : IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
      (symanzikU α (simplexPoint x) ^ 4)⁻¹) (simplexSet m)) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ =>
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            P.eval (-loopShift α p (simplexPoint x)) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            P.contractTwo (symanzikMatrix α (simplexPoint x))
              (loopComp (-loopShift α p (simplexPoint x))) +
          ((m - 6).factorial : ℂ) / 4 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹ *
            P.contractFour (symanzikMatrix α (simplexPoint x))) := by
  have hm0 : 0 < m := by omega
  have hA' := integral_loopQuartic_mul_prod_lineDenom_eq P α p M (by omega) hε hspan hU hA
  have hH := integrable_numEnergyValueQuartic P α p M hm hε hspan hU hA
  refine ⟨fun v => (hA' v).1, ?_, ?_⟩
  · have : (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) =
        fun v => (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic P α p M ε x v :=
      funext fun v => (hA' v).2
    rw [this]
    exact hH.integral_prod_right.const_mul _
  · have hA2 : ∀ v : Fin 2 → Fin 3 → ℝ, ∫ t : Fin 2 → ℝ,
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
          (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic P α p M ε x v :=
      fun v => (hA' v).2
    have hspat : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
        (m.factorial : ℂ) * ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValueQuartic P α p M ε x v =
          -((π : ℂ) ^ 4) * (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
            (((m - 4).factorial : ℂ) *
                ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
                P.eval (-loopShift α p (simplexPoint x)) +
              ((m - 5).factorial : ℂ) / 2 *
                ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
                P.contractTwo (symanzikMatrix α (simplexPoint x))
                  (loopComp (-loopShift α p (simplexPoint x))) +
              ((m - 6).factorial : ℂ) / 4 *
                ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹ *
                P.contractFour (symanzikMatrix α (simplexPoint x)))) := by
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      exact factorial_mul_integral_numEnergyValueQuartic P α p M hm hε hPD
    show ∫ v : Fin 2 → Fin 3 → ℝ, ∫ t : Fin 2 → ℝ,
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ = _
    simp only [hA2]
    rw [integral_const_mul, ← integral_integral_swap
      (f := fun x v => numEnergyValueQuartic P α p M ε x v) hH, ← integral_const_mul,
      integral_congr_ae hspat, integral_const_mul]

/-- **The representation with numerators of degree at most four under the graph criterion.**
`jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom` with `hspan`, `hU` and the
integrability of `tr² A · U⁻⁴` replaced by `NoSubdivergenceQuartic α` (the complement of every
direction class has at least five lines). -/
theorem jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_criterion (hm : 6 ≤ m)
    (hε : 0 < ε) (hcrit : NoSubdivergenceQuartic α) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ =>
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            P.eval (-loopShift α p (simplexPoint x)) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            P.contractTwo (symanzikMatrix α (simplexPoint x))
              (loopComp (-loopShift α p (simplexPoint x))) +
          ((m - 6).factorial : ℂ) / 4 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹ *
            P.contractFour (symanzikMatrix α (simplexPoint x))) := by
  have h3 : NoSubdivergence α := hcrit.noSubdivergenceQuadratic.noSubdivergence
  exact jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom P α p M hm hε h3.span
    (integrableOn_inv_sq_symanzikU_of_criterion α h3)
    (integrableOn_trace_sq_mul_inv_pow_four_symanzikU α hcrit)

end Representation

/-! ### The representation under integrability hypotheses

The integrability on simplex × energies and on simplex × space is the only place where `hU` and
the integrability of `tr² A · U⁻⁴` enter. The forms below take those two integrabilities as
hypotheses, for use with sharper bounds on the numerator (for instance the numerator-aware
weights of `QED/Integration/SymanzikIntegrabilityRefined.lean`). -/

section OfIntegrable

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- The energy integral at fixed spatial momenta, with the integrability on simplex × energies as
a hypothesis. -/
theorem integral_loopQuartic_mul_prod_lineDenom_eq_of_integrable (hm : 3 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) (v : Fin 2 → Fin 3 → ℝ)
    (hint : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) =>
        P.eval (loopMomenta q.2 v) * (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume)) :
    Integrable (fun t : Fin 2 → ℝ =>
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) ∧
      ∫ t : Fin 2 → ℝ, P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic P α p M ε x v := by
  have hm0 : 0 < m := by omega
  have hfey : ∀ t : Fin 2 → ℝ,
      P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m,
          P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
    intro t
    have h : ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
      refine Feynman.prod_inv_eq_factorial_mul_integral_simplex fun i => ?_
      simp only [lineDenom, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub]
      linarith
    rw [h, integral_const_mul]
    ring
  refine ⟨?_, ?_⟩
  · simp only [hfey]
    exact hint.integral_prod_right.const_mul _
  · simp only [hfey]
    rw [integral_const_mul]
    congr 1
    rw [← integral_integral_swap (f := fun x t =>
      P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹) hint]
    refine integral_congr_ae ?_
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    exact integral_eval_mul_paramDenom_quartic P α p M hm hε hPD v

/-- **The representation with a numerator of degree at most four, under integrability
hypotheses.** The conclusion of `jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom`,
with `hU` and the integrability of `tr² A · U⁻⁴` replaced by the integrability of the
parametrized integrand on simplex × energies (for every spatial momentum) and of the
energy-integrated integrand `numEnergyValueQuartic` on simplex × space. -/
theorem jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_integrable (hm : 6 ≤ m)
    (hε : 0 < ε) (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hE : ∀ v : Fin 2 → Fin 3 → ℝ, Integrable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) =>
        P.eval (loopMomenta q.2 v) * (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume))
    (hS : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
        numEnergyValueQuartic P α p M ε q.1 q.2)
      ((volume.restrict (simplexSet m)).prod volume)) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ =>
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            P.eval (-loopShift α p (simplexPoint x)) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            P.contractTwo (symanzikMatrix α (simplexPoint x))
              (loopComp (-loopShift α p (simplexPoint x))) +
          ((m - 6).factorial : ℂ) / 4 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹ *
            P.contractFour (symanzikMatrix α (simplexPoint x))) := by
  have hm0 : 0 < m := by omega
  have hA' := fun v => integral_loopQuartic_mul_prod_lineDenom_eq_of_integrable P α p M (by omega)
    hε hspan v (hE v)
  refine ⟨fun v => (hA' v).1, ?_, ?_⟩
  · have : (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) =
        fun v => (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic P α p M ε x v :=
      funext fun v => (hA' v).2
    rw [this]
    exact hS.integral_prod_right.const_mul _
  · have hA2 : ∀ v : Fin 2 → Fin 3 → ℝ, ∫ t : Fin 2 → ℝ,
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
          (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic P α p M ε x v :=
      fun v => (hA' v).2
    have hspat : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
        (m.factorial : ℂ) * ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValueQuartic P α p M ε x v =
          -((π : ℂ) ^ 4) * (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
            (((m - 4).factorial : ℂ) *
                ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
                P.eval (-loopShift α p (simplexPoint x)) +
              ((m - 5).factorial : ℂ) / 2 *
                ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
                P.contractTwo (symanzikMatrix α (simplexPoint x))
                  (loopComp (-loopShift α p (simplexPoint x))) +
              ((m - 6).factorial : ℂ) / 4 *
                ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹ *
                P.contractFour (symanzikMatrix α (simplexPoint x)))) := by
      filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
      exact factorial_mul_integral_numEnergyValueQuartic P α p M hm hε hPD
    show ∫ v : Fin 2 → Fin 3 → ℝ, ∫ t : Fin 2 → ℝ,
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ = _
    simp only [hA2]
    rw [integral_const_mul, ← integral_integral_swap
      (f := fun x v => numEnergyValueQuartic P α p M ε x v) hS, ← integral_const_mul,
      integral_congr_ae hspat, integral_const_mul]

end OfIntegrable

end QED.Integration.TwoLoop

end
