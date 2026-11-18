/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopMomentsQuartic
public import QED.Integration.TwoLoopParametricNumerator
public import QED.Integration.SymanzikIntegrabilityQuadratic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Numerators of degree at most four: the energy integral

First half of the parametric representation with numerators of degree at most four in the loop
momenta (obligations O2-10 and O2-11, `docs/TWO-LOOP-DERIVATION.md`, section 4.4), extending
`QED/Integration/TwoLoopParametricNumerator.lean` (degree at most two).

A numerator is `P(ℓ) = c + ∑ Lₐ ℓₐ + ∑ Qₐ_b ℓₐ ℓ_b + ∑ Kₐ_bc ℓₐ ℓ_b ℓ_c + ∑ Rₐ_bcd ℓₐ ℓ_b ℓ_c ℓ_d`
(`LoopQuartic`), with indices `a = (s, μ)` running over the eight components `ℓₛ^μ` of the two
loop momenta (`LoopIndex`). Its even part about a point `ℓ₀` is
`P(ℓ₀ + δ) + P(ℓ₀ - δ) = 2 (P(ℓ₀) + ∑ Hₐ_b(ℓ₀) δₐ δ_b + ∑ Rₐ_bcd δₐ δ_b δ_c δ_d)`
(`LoopQuartic.eval_add_add_eval_sub`), with the coefficients
`Hₐ_b(ℓ₀) = Qₐ_b + ∑_c (Kₐ_bc + Kₐ_cb + K_cab) ℓ₀_c + ∑_cd R^{sym}ₐ_bcd ℓ₀_c ℓ₀_d` (`LoopQuartic.hess`),
`R^{sym}ₐ_bcd = Rₐ_bcd + Rₐ_cbd + Rₐ_cdb + R_cabd + R_cadb + R_cdab` (the six placements of the two
`δ`s among the four factors).

**The energy integral at fixed spatial momenta** (`integral_loopQuartic_mul_prod_lineDenom_eq`):
for `N = m + 1 ≥ 4` propagators, `ε > 0`, two independent `αᵢ`, `U⁻²` and `tr² A · U⁻⁴`
integrable on the simplex,
`∫_{ℝ²} P ∏ᵢ Dᵢ⁻¹ dt = m! ∫_Δ (P(-τ, v) E₀ + C₂ E₂ + C₄ E₄) dx`, with
`E₀ = -(π/(N-1)) U^{-1/2} w^{1-N}`, `E₂ = π/(2(N-1)(N-2)) U^{-1/2} w^{2-N}`,
`E₄ = -π/(4(N-1)(N-2)(N-3)) U^{-1/2} w^{3-N}`, `C₂ = ∑ₛᵣ H_{(s,0),(r,0)}(-τ, v) (A⁻¹)ₛᵣ`,
`C₄ = ∑ R_{(s,0),(r,0),(t,0),(q,0)} Πₛᵣₜq(A⁻¹)` and `w = (v+σ)ᵀA(v+σ) + V - iε`. The integrability
of `tr² A · U⁻⁴` enters through `B² U^{-1/2}`, `B = 1 + 2|τ|² + 2 tr A / U`, the weight comparison
of the quartic numerator with the kernel; under `NoSubdivergenceQuartic` it holds
(`QED/Integration/SymanzikIntegrabilityQuadratic.lean`).

The formula was checked numerically against direct 2D quadrature with random complex
coefficients (relative error `5e-12`).

## Main statements

* `LoopQuartic`, `LoopQuartic.eval`, `LoopQuartic.hess`: numerators of degree at most four.
* `LoopQuartic.eval_add_add_eval_sub`: the even part.
* `integral_eval_mul_paramDenom_quartic`: the energy integral at an interior point.
* `integral_loopQuartic_mul_prod_lineDenom_eq`: the energy integral at fixed spatial momenta;
  `integral_loopQuartic_mul_prod_lineDenom_eq_of_criterion`: the same under
  `NoSubdivergenceQuartic`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter Function
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint simplexComb)
open QED.Integration.Spatial (quadForm)

/-! ### Even parts of multilinear sums -/

section EvenSums

variable {ι : Type*} [Fintype ι]

theorem sum_lin_even (L : ι → ℂ) (X D : ι → ℂ) :
    ∑ a, L a * (X a + D a) + ∑ a, L a * (X a - D a) = 2 * ∑ a, L a * X a := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem sum_quad_even (Q : ι → ι → ℂ) (X D : ι → ℂ) :
    ∑ a, ∑ b, Q a b * ((X a + D a) * (X b + D b)) +
        ∑ a, ∑ b, Q a b * ((X a - D a) * (X b - D b)) =
      2 * (∑ a, ∑ b, Q a b * (X a * X b) + ∑ a, ∑ b, Q a b * (D a * D b)) := by
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem sum_cub_even (K : ι → ι → ι → ℂ) (X D : ι → ℂ) :
    ∑ a, ∑ b, ∑ c, K a b c * ((X a + D a) * (X b + D b) * (X c + D c)) +
        ∑ a, ∑ b, ∑ c, K a b c * ((X a - D a) * (X b - D b) * (X c - D c)) =
      2 * (∑ a, ∑ b, ∑ c, K a b c * (X a * X b * X c) +
        ∑ a, ∑ b, (∑ c, (K a b c + K a c b + K c a b) * X c) * (D a * D b)) := by
  have e3 : ∑ a, ∑ b, ∑ c, K a c b * X c * (D a * D b) =
      ∑ a, ∑ b, ∑ c, K a b c * (D a * X b * D c) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e4 : ∑ a, ∑ b, ∑ c, K c a b * X c * (D a * D b) =
      ∑ a, ∑ b, ∑ c, K a b c * (X a * D b * D c) := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have hR : ∑ a, ∑ b, (∑ c, (K a b c + K a c b + K c a b) * X c) * (D a * D b) =
      ∑ a, ∑ b, ∑ c, K a b c * (D a * D b * X c) + ∑ a, ∑ b, ∑ c, K a c b * X c * (D a * D b) +
        ∑ a, ∑ b, ∑ c, K c a b * X c * (D a * D b) := by
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by ring
  rw [hR, e3, e4]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => by ring

theorem sum_quart_even (R : ι → ι → ι → ι → ℂ) (X D : ι → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((X a + D a) * (X b + D b) * (X c + D c) * (X d + D d)) +
        ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ((X a - D a) * (X b - D b) * (X c - D c) * (X d - D d)) =
      2 * (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (X a * X b * X c * X d) +
        ∑ a, ∑ b, (∑ c, ∑ d, (R a b c d + R a c b d + R a c d b + R c a b d + R c a d b +
          R c d a b) * (X c * X d)) * (D a * D b) +
        ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (D a * D b * D c * D d)) := by
  have p13 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (D a * X b * D c * X d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a c b d * (X c * X d) * (D a * D b) := by
    rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have p14 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (D a * X b * X c * D d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a c d b * (X c * X d) * (D a * D b) := by
    rw [Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have p23 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (X a * D b * D c * X d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R c a b d * (X c * X d) * (D a * D b) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have p24 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (X a * D b * X c * D d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R c a d b * (X c * X d) * (D a * D b) := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have p34 : ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (X a * X b * D c * D d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R c d a b * (X c * X d) * (D a * D b) := by
    rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm,
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hR : ∑ a, ∑ b, (∑ c, ∑ d, (R a b c d + R a c b d + R a c d b + R c a b d + R c a d b +
          R c d a b) * (X c * X d)) * (D a * D b) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * (D a * D b * X c * X d) +
        ∑ a, ∑ b, ∑ c, ∑ d, R a c b d * (X c * X d) * (D a * D b) +
        ∑ a, ∑ b, ∑ c, ∑ d, R a c d b * (X c * X d) * (D a * D b) +
        ∑ a, ∑ b, ∑ c, ∑ d, R c a b d * (X c * X d) * (D a * D b) +
        ∑ a, ∑ b, ∑ c, ∑ d, R c a d b * (X c * X d) * (D a * D b) +
        ∑ a, ∑ b, ∑ c, ∑ d, R c d a b * (X c * X d) * (D a * D b) := by
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hR, ← p13, ← p14, ← p23, ← p24, ← p34]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end EvenSums

/-! ### Numerators of degree at most four -/

/-- The indices `(s, μ)` of the eight components `ℓₛ^μ` of the two loop momenta. -/
abbrev LoopIndex := Fin 2 × Fin 4

/-- The components of the loop momenta as complex numbers, indexed by `LoopIndex`. -/
def loopComp (ℓ : Fin 2 → Fin 4 → ℝ) (a : LoopIndex) : ℂ := ((ℓ a.1 a.2 : ℝ) : ℂ)

theorem loopComp_add (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    loopComp (ℓ + δ) = loopComp ℓ + loopComp δ := by
  funext a
  simp [loopComp]

theorem loopComp_sub (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    loopComp (ℓ - δ) = loopComp ℓ - loopComp δ := by
  funext a
  simp [loopComp]

/-- A polynomial of degree at most four in the two loop momenta,
`P(ℓ) = c + ∑ Lₐ ℓₐ + ∑ Qₐ_b ℓₐ ℓ_b + ∑ Kₐ_bc ℓₐ ℓ_b ℓ_c + ∑ Rₐ_bcd ℓₐ ℓ_b ℓ_c ℓ_d`, indices in
`LoopIndex`, with complex coefficients. -/
structure LoopQuartic where
  /-- The constant term `c`. -/
  const : ℂ
  /-- The linear coefficients `Lₐ`. -/
  lin : LoopIndex → ℂ
  /-- The quadratic coefficients `Qₐ_b`. -/
  quad : LoopIndex → LoopIndex → ℂ
  /-- The cubic coefficients `Kₐ_bc`. -/
  cub : LoopIndex → LoopIndex → LoopIndex → ℂ
  /-- The quartic coefficients `Rₐ_bcd`. -/
  quart : LoopIndex → LoopIndex → LoopIndex → LoopIndex → ℂ

namespace LoopQuartic

variable (P : LoopQuartic)

/-- The value of the polynomial at complex components `X`. -/
def evalC (X : LoopIndex → ℂ) : ℂ :=
  P.const + ∑ a, P.lin a * X a + ∑ a, ∑ b, P.quad a b * (X a * X b) +
    ∑ a, ∑ b, ∑ c, P.cub a b c * (X a * X b * X c) +
    ∑ a, ∑ b, ∑ c, ∑ d, P.quart a b c d * (X a * X b * X c * X d)

/-- The value `P(ℓ)`. -/
def eval (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ := P.evalC (loopComp ℓ)

/-- The quartic part `∑ Rₐ_bcd Xₐ X_b X_c X_d`. -/
def quartPart (X : LoopIndex → ℂ) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, P.quart a b c d * (X a * X b * X c * X d)

/-- The sum of the quartic coefficients over the six placements of two indices `a, b` among four
slots: `Rₐ_bcd + Rₐ_cbd + Rₐ_cdb + R_cabd + R_cadb + R_cdab`. -/
def quartSym (a b c d : LoopIndex) : ℂ :=
  P.quart a b c d + P.quart a c b d + P.quart a c d b + P.quart c a b d + P.quart c a d b +
    P.quart c d a b

/-- The coefficients of the part of `P(X + D)` quadratic in `D`:
`Hₐ_b(X) = Qₐ_b + ∑_c (Kₐ_bc + Kₐ_cb + K_cab) X_c + ∑_cd R^{sym}ₐ_bcd X_c X_d`. -/
def hess (X : LoopIndex → ℂ) (a b : LoopIndex) : ℂ :=
  P.quad a b + ∑ c, (P.cub a b c + P.cub a c b + P.cub c a b) * X c +
    ∑ c, ∑ d, P.quartSym a b c d * (X c * X d)

/-- **The even part of a numerator of degree at most four.** -/
theorem evalC_add_add_evalC_sub (X D : LoopIndex → ℂ) :
    P.evalC (X + D) + P.evalC (X - D) =
      2 * (P.evalC X + ∑ a, ∑ b, P.hess X a b * (D a * D b) + P.quartPart D) := by
  have h1 := sum_lin_even P.lin X D
  have h2 := sum_quad_even P.quad X D
  have h3 := sum_cub_even P.cub X D
  have h4 := sum_quart_even P.quart X D
  have hH : ∑ a, ∑ b, P.hess X a b * (D a * D b) =
      ∑ a, ∑ b, P.quad a b * (D a * D b) +
        ∑ a, ∑ b, (∑ c, (P.cub a b c + P.cub a c b + P.cub c a b) * X c) * (D a * D b) +
        ∑ a, ∑ b, (∑ c, ∑ d, (P.quart a b c d + P.quart a c b d + P.quart a c d b +
          P.quart c a b d + P.quart c a d b + P.quart c d a b) * (X c * X d)) * (D a * D b) := by
    simp only [hess, quartSym, add_mul, Finset.sum_add_distrib]
  simp only [evalC, quartPart, Pi.add_apply, Pi.sub_apply]
  rw [hH]
  linear_combination h1 + h2 + h3 + h4

theorem eval_add_add_eval_sub (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    P.eval (ℓ + δ) + P.eval (ℓ - δ) =
      2 * (P.eval ℓ + ∑ a, ∑ b, P.hess (loopComp ℓ) a b * (loopComp δ a * loopComp δ b) +
        P.quartPart (loopComp δ)) := by
  simp only [eval, loopComp_add, loopComp_sub]
  exact P.evalC_add_add_evalC_sub _ _

/-- The sum of the norms of the coefficients. -/
noncomputable def coeffBound : ℝ :=
  ‖P.const‖ + ∑ a, ‖P.lin a‖ + ∑ a, ∑ b, ‖P.quad a b‖ + ∑ a, ∑ b, ∑ c, ‖P.cub a b c‖ +
    ∑ a, ∑ b, ∑ c, ∑ d, ‖P.quart a b c d‖

theorem coeffBound_nonneg : 0 ≤ P.coeffBound := by
  unfold coeffBound
  positivity

theorem norm_evalC_le (X : LoopIndex → ℂ) {S : ℝ} (h1 : ∀ a, ‖X a‖ ≤ 1 + S)
    (h2 : ∀ a b, ‖X a * X b‖ ≤ S) (hS : 0 ≤ S) :
    ‖P.evalC X‖ ≤ P.coeffBound * (1 + S) ^ 2 := by
  have hT : 1 ≤ (1 + S) ^ 2 := by nlinarith
  have b1 : ∀ a, ‖X a‖ ≤ (1 + S) ^ 2 := fun a => (h1 a).trans (by nlinarith)
  have b2 : ∀ a b, ‖X a * X b‖ ≤ (1 + S) ^ 2 := fun a b => (h2 a b).trans (by nlinarith)
  have b3 : ∀ a b c, ‖X a * X b * X c‖ ≤ (1 + S) ^ 2 := fun a b c => by
    rw [norm_mul, sq]
    exact mul_le_mul ((h2 a b).trans (by linarith)) (h1 c) (norm_nonneg _) (by linarith)
  have b4 : ∀ a b c d, ‖X a * X b * X c * X d‖ ≤ (1 + S) ^ 2 := fun a b c d => by
    rw [mul_assoc, norm_mul, sq]
    exact mul_le_mul ((h2 a b).trans (by linarith)) ((h2 c d).trans (by linarith))
      (norm_nonneg _) (by linarith)
  have hL : ‖∑ a, P.lin a * X a‖ ≤ (∑ a, ‖P.lin a‖) * (1 + S) ^ 2 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (b1 a) (norm_nonneg _)
  have hQ : ‖∑ a, ∑ b, P.quad a b * (X a * X b)‖ ≤ (∑ a, ∑ b, ‖P.quad a b‖) * (1 + S) ^ 2 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (b2 a b) (norm_nonneg _)
  have hK : ‖∑ a, ∑ b, ∑ c, P.cub a b c * (X a * X b * X c)‖ ≤
      (∑ a, ∑ b, ∑ c, ‖P.cub a b c‖) * (1 + S) ^ 2 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (b3 a b c) (norm_nonneg _)
  have hR : ‖∑ a, ∑ b, ∑ c, ∑ d, P.quart a b c d * (X a * X b * X c * X d)‖ ≤
      (∑ a, ∑ b, ∑ c, ∑ d, ‖P.quart a b c d‖) * (1 + S) ^ 2 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (b4 a b c d) (norm_nonneg _)
  have hc : ‖P.const‖ ≤ ‖P.const‖ * (1 + S) ^ 2 := le_mul_of_one_le_right (norm_nonneg _) hT
  unfold evalC coeffBound
  calc _ ≤ ‖P.const‖ + ‖∑ a, P.lin a * X a‖ + ‖∑ a, ∑ b, P.quad a b * (X a * X b)‖ +
        ‖∑ a, ∑ b, ∑ c, P.cub a b c * (X a * X b * X c)‖ +
        ‖∑ a, ∑ b, ∑ c, ∑ d, P.quart a b c d * (X a * X b * X c * X d)‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add₃_le
    _ ≤ _ := by
        have := add_le_add (add_le_add (add_le_add (add_le_add hc hL) hQ) hK) hR
        linarith

/-- `‖P(ℓ)‖ ≤ coeffBound · (1 + |ℓ|²)²`. -/
theorem norm_eval_le (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖P.eval ℓ‖ ≤ P.coeffBound * (1 + ∑ s, ∑ μ, ℓ s μ ^ 2) ^ 2 := by
  set S := ∑ s, ∑ μ, ℓ s μ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun μ _ => sq_nonneg _
  have hle : ∀ s μ, ℓ s μ ^ 2 ≤ S := fun s μ =>
    (Finset.single_le_sum (fun μ _ => sq_nonneg (ℓ s μ)) (Finset.mem_univ μ)).trans
      (Finset.single_le_sum (f := fun s => ∑ μ, ℓ s μ ^ 2)
        (fun s _ => Finset.sum_nonneg fun μ _ => sq_nonneg (ℓ s μ)) (Finset.mem_univ s))
  refine P.norm_evalC_le _ (fun a => ?_) (fun a b => ?_) hS
  · rw [loopComp, norm_real, Real.norm_eq_abs]
    nlinarith [hle a.1 a.2, abs_nonneg (ℓ a.1 a.2), sq_abs (ℓ a.1 a.2),
      sq_nonneg (|ℓ a.1 a.2| - 1)]
  · rw [loopComp, loopComp, ← ofReal_mul, norm_real, Real.norm_eq_abs, abs_mul]
    nlinarith [hle a.1 a.2, hle b.1 b.2, abs_nonneg (ℓ a.1 a.2), abs_nonneg (ℓ b.1 b.2),
      sq_abs (ℓ a.1 a.2), sq_abs (ℓ b.1 b.2), sq_nonneg (|ℓ a.1 a.2| - |ℓ b.1 b.2|)]

theorem continuous_eval : Continuous P.eval := by
  unfold eval evalC loopComp
  fun_prop

end LoopQuartic

/-! ### Energy components -/

theorem loopComp_loopMomenta_energy (u : Fin 2 → ℝ) (a : LoopIndex) :
    loopComp (loopMomenta u 0) a = if a.2 = 0 then ((u a.1 : ℝ) : ℂ) else 0 := by
  obtain ⟨s, μ⟩ := a
  refine Fin.cases ?_ (fun c => ?_) μ
  · simp [loopComp, loopMomenta]
  · simp [loopComp, loopMomenta, Fin.succ_ne_zero]

theorem sum_mul_loopComp_energy (f : LoopIndex → ℂ) (u : Fin 2 → ℝ) :
    ∑ a, f a * loopComp (loopMomenta u 0) a = ∑ s, f (s, 0) * ((u s : ℝ) : ℂ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fin.sum_univ_succ]
  simp [loopComp_loopMomenta_energy, Fin.succ_ne_zero]

theorem sum_sum_hess_loopComp_energy (H : LoopIndex → LoopIndex → ℂ) (u : Fin 2 → ℝ) :
    ∑ a, ∑ b, H a b * (loopComp (loopMomenta u 0) a * loopComp (loopMomenta u 0) b) =
      ∑ s, ∑ r, H (s, 0) (r, 0) * ((u s * u r : ℝ) : ℂ) := by
  have h1 : ∀ a, ∑ b, H a b * (loopComp (loopMomenta u 0) a * loopComp (loopMomenta u 0) b) =
      (∑ r, H a (r, 0) * ((u r : ℝ) : ℂ)) * loopComp (loopMomenta u 0) a := fun a => by
    rw [← sum_mul_loopComp_energy (fun b => H a b) u, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [h1]
  rw [sum_mul_loopComp_energy (fun a => ∑ r, H a (r, 0) * ((u r : ℝ) : ℂ)) u, Finset.sum_congr rfl
    fun s _ => Finset.sum_mul _ _ _]
  push_cast
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => by ring

theorem quartPart_loopComp_energy (P : LoopQuartic) (u : Fin 2 → ℝ) :
    P.quartPart (loopComp (loopMomenta u 0)) =
      ∑ s, ∑ r, ∑ t, ∑ q, P.quart (s, 0) (r, 0) (t, 0) (q, 0) *
        ((u s * u r * u t * u q : ℝ) : ℂ) := by
  set Y := loopComp (loopMomenta u 0) with hY
  have e1 : ∀ a b c, ∑ d, P.quart a b c d * (Y a * Y b * Y c * Y d) =
      (∑ q, P.quart a b c (q, 0) * ((u q : ℝ) : ℂ)) * (Y a * Y b * Y c) := fun a b c => by
    rw [hY, ← sum_mul_loopComp_energy (fun d => P.quart a b c d) u, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  have e2 : ∀ a b, ∑ c, (∑ q, P.quart a b c (q, 0) * ((u q : ℝ) : ℂ)) * (Y a * Y b * Y c) =
      (∑ t, ∑ q, P.quart a b (t, 0) (q, 0) * ((u t : ℝ) : ℂ) * ((u q : ℝ) : ℂ)) * (Y a * Y b) :=
    fun a b => by
      have := sum_mul_loopComp_energy
        (fun c => (∑ q, P.quart a b c (q, 0) * ((u q : ℝ) : ℂ)) * (Y a * Y b)) u
      rw [Finset.sum_mul]
      refine (Finset.sum_congr rfl fun c _ => by rw [hY]; ring).trans (this.trans ?_)
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by ring
  have e3 : ∀ a, ∑ b, (∑ t, ∑ q, P.quart a b (t, 0) (q, 0) * ((u t : ℝ) : ℂ) *
      ((u q : ℝ) : ℂ)) * (Y a * Y b) = (∑ r, ∑ t, ∑ q, P.quart a (r, 0) (t, 0) (q, 0) *
        ((u r : ℝ) : ℂ) * ((u t : ℝ) : ℂ) * ((u q : ℝ) : ℂ)) * Y a := fun a => by
    have := sum_mul_loopComp_energy (fun b => (∑ t, ∑ q, P.quart a b (t, 0) (q, 0) *
      ((u t : ℝ) : ℂ) * ((u q : ℝ) : ℂ)) * Y a) u
    rw [Finset.sum_mul]
    refine (Finset.sum_congr rfl fun b _ => by rw [hY]; ring).trans (this.trans ?_)
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => by ring
  unfold LoopQuartic.quartPart
  simp only [e1, e2, e3]
  rw [hY, sum_mul_loopComp_energy]
  simp only [Finset.sum_mul]
  push_cast
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => by ring

/-! ### The energy integral at fixed spatial momenta -/

/-- The energy contraction of the quadratic coefficients, `∑ₛᵣ H_{(s,0),(r,0)}(X) (A⁻¹)ₛᵣ`. -/
noncomputable def LoopQuartic.energyContractTwo (P : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) : ℂ :=
  ∑ s, ∑ r, P.hess X (s, 0) (r, 0) * ((A⁻¹ s r : ℝ) : ℂ)

/-- The energy contraction of the quartic coefficients,
`∑ R_{(s,0),(r,0),(t,0),(q,0)} Πₛᵣₜq(A⁻¹)`. -/
noncomputable def LoopQuartic.energyContractFour (P : LoopQuartic)
    (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∑ s, ∑ r, ∑ t, ∑ q, P.quart (s, 0) (r, 0) (t, 0) (q, 0) * ((matPair A⁻¹ s r t q : ℝ) : ℂ)

/-- `(U⁻²)(U^{-1/2}) ≤ 1 + U⁻⁴`. -/
theorem inv_sq_mul_inv_sqrt_le (r : ℝ) : (r ^ 2)⁻¹ * (Real.sqrt r)⁻¹ ≤ 1 + (r ^ 4)⁻¹ := by
  rcases le_or_gt r 0 with h | h
  · rw [Real.sqrt_eq_zero'.mpr h, _root_.inv_zero, mul_zero]
    positivity
  rcases le_or_gt r 1 with h1 | h1
  · have hs : r ≤ Real.sqrt r := by
      rw [Real.le_sqrt h.le h.le]
      nlinarith
    have e1 : (Real.sqrt r)⁻¹ ≤ r⁻¹ := inv_anti₀ h hs
    have e2 : (r ^ 2)⁻¹ * r⁻¹ ≤ (r ^ 4)⁻¹ := by
      rw [← mul_inv, ← pow_succ]
      exact inv_anti₀ (by positivity) (pow_le_pow_of_le_one h.le h1 (by norm_num))
    have : (r ^ 2)⁻¹ * (Real.sqrt r)⁻¹ ≤ (r ^ 2)⁻¹ * r⁻¹ :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    linarith
  · have a1 : (r ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    have a2 : (Real.sqrt r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by rw [Real.one_le_sqrt]; exact h1.le)
    have a3 : 0 ≤ (Real.sqrt r)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have : (r ^ 2)⁻¹ * (Real.sqrt r)⁻¹ ≤ 1 := by nlinarith
    have : 0 ≤ (r ^ 4)⁻¹ := by positivity
    linarith

section StageA

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- The energy-integrated parametrized integrand of the fourth energy moment,
`-π/(4 N'(N'-1)(N'-2)) U^{-1/2} w^{3-N}`, `N' = N - 1 = m`. -/
noncomputable def energyValueFour (ε : ℝ) (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) : ℂ :=
  -(π / (4 * ((m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2)))) *
    ((Real.sqrt (symanzikU α (simplexPoint x)) : ℝ) : ℂ)⁻¹ *
    (shiftedConst α p M ε x v ^ (m - 2))⁻¹

/-- The energy-integrated parametrized integrand with the numerator `P` of degree at most four:
`P(-τ, v) E₀ + C₂(-τ, v) E₂ + C₄ E₄`. -/
noncomputable def numEnergyValueQuartic (ε : ℝ) (x : Fin m → ℝ) (v : Fin 2 → Fin 3 → ℝ) : ℂ :=
  P.eval (loopMomenta (-energyShift α p (simplexPoint x)) v) * energyValue α p M ε x v +
    P.energyContractTwo (symanzikMatrix α (simplexPoint x))
        (loopComp (loopMomenta (-energyShift α p (simplexPoint x)) v)) *
      energyValueTwo α p M ε x v +
    P.energyContractFour (symanzikMatrix α (simplexPoint x)) * energyValueFour α p M ε x v

theorem continuous_eval_loopMomenta_left_quartic (v : Fin 2 → Fin 3 → ℝ) :
    Continuous fun t : Fin 2 → ℝ => P.eval (loopMomenta t v) :=
  P.continuous_eval.comp (continuous_loopMomenta.comp (continuous_id.prodMk continuous_const))

theorem continuous_eval_loopMomenta_right_quartic (t : Fin 2 → ℝ) :
    Continuous fun v : Fin 2 → Fin 3 → ℝ => P.eval (loopMomenta t v) :=
  P.continuous_eval.comp (continuous_loopMomenta.comp (continuous_const.prodMk continuous_id))

theorem norm_eval_loopMomenta_le_quartic (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    ‖P.eval (loopMomenta t v)‖ ≤
      P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) ^ 2 * (1 + ∑ s, t s ^ 2) ^ 2 := by
  refine (P.norm_eval_le _).trans ?_
  rw [sum_sq_loopMomenta, mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ P.coeffBound_nonneg
  have h1 : 0 ≤ ∑ s, t s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have h2 : 0 ≤ ∑ s, ∑ c, v s c ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg h1 h2]) 2

/-- The pointwise bound on the energy integrand at an interior point of the simplex. -/
theorem norm_eval_mul_inv_le_quartic {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (τ t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) (F : ℂ) :
    ‖P.eval (loopMomenta t v) * F‖ ≤
      P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) ^ 2 *
        (1 + 2 * ∑ i, τ i ^ 2 + 2 * (A.trace / A.det)) ^ 2 *
          ((1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 2 * ‖F‖) := by
  have hK : 0 ≤ P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) ^ 2 :=
    mul_nonneg P.coeffBound_nonneg (by positivity)
  have h1 := norm_eval_loopMomenta_le_quartic P t v
  have h2 := one_add_sum_sq_le hA t τ
  have h2' : (1 + ∑ s, t s ^ 2) ^ 2 ≤ ((1 + 2 * ∑ i, τ i ^ 2 + 2 * (A.trace / A.det)) *
      (1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  rw [norm_mul]
  calc ‖P.eval (loopMomenta t v)‖ * ‖F‖
      ≤ (P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) ^ 2 * (1 + ∑ s, t s ^ 2) ^ 2) * ‖F‖ := by
        gcongr
    _ ≤ (P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) ^ 2 *
          ((1 + 2 * ∑ i, τ i ^ 2 + 2 * (A.trace / A.det)) * (1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ))) ^ 2) *
          ‖F‖ := by gcongr
    _ = _ := by ring

/-- At an interior point of the simplex, the parametrized energy integrand with the numerator is
integrable in the energies (`N ≥ 4`). -/
theorem integrable_eval_mul_paramDenom_quartic (hm : 3 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) (v : Fin 2 → Fin 3 → ℝ) :
    Integrable fun t : Fin 2 → ℝ =>
      P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
  have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
  simp only [paramDenom_eq α p M hdet]
  have hw : (shiftedConst α p M ε x v).im < 0 := by rw [shiftedConst_im]; linarith
  have hb := ((integrable_one_add_quadratic_pow_mul_norm hPD hw (j := 2)
    (by omega : 2 + 2 ≤ m + 1)).comp_add_right (energyShift α p (simplexPoint x))).const_mul
    (P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) ^ 2 *
      (1 + 2 * ∑ i, energyShift α p (simplexPoint x) i ^ 2 +
        2 * ((symanzikMatrix α (simplexPoint x)).trace /
          (symanzikMatrix α (simplexPoint x)).det)) ^ 2)
  refine hb.mono' ?_ (Eventually.of_forall fun t => ?_)
  · refine ((continuous_eval_loopMomenta_left_quartic P v).mul ?_).aestronglyMeasurable
    exact (continuous_inv_neg_add_pow hw (m + 1)).comp
      ((continuous_quadratic _).comp (continuous_id.add continuous_const))
  · exact norm_eval_mul_inv_le_quartic P hPD _ t v _

/-- **The energy integral at an interior point** with a numerator of degree at most four
(`N ≥ 4`): `∫ P(t, v) (∑ᵢ zᵢ Dᵢ)^{-N} dt = numEnergyValueQuartic`. -/
theorem integral_eval_mul_paramDenom_quartic (hm : 3 ≤ m) (hε : 0 < ε) {x : Fin m → ℝ}
    (hPD : (symanzikMatrix α (simplexPoint x)).PosDef) (v : Fin 2 → Fin 3 → ℝ) :
    ∫ t : Fin 2 → ℝ, P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹ =
      numEnergyValueQuartic P α p M ε x v := by
  have hint := integrable_eval_mul_paramDenom_quartic P α p M hm hε hPD v
  have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
  simp only [paramDenom_eq α p M hdet] at hint ⊢
  set A := symanzikMatrix α (simplexPoint x) with hAdef
  set τ := energyShift α p (simplexPoint x) with hτdef
  set w := shiftedConst α p M ε x v with hwdef
  have hw : w.im < 0 := by rw [hwdef, shiftedConst_im]; linarith
  have hshift := integral_add_right_eq_self (μ := volume) (fun u : Fin 2 → ℝ =>
    P.eval (loopMomenta (u - τ) v) * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹) τ
  simp only [add_sub_cancel_right] at hshift
  rw [hshift]
  have hint' : Integrable fun u : Fin 2 → ℝ =>
      P.eval (loopMomenta (u - τ) v) * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹ := by
    have := hint.comp_sub_right τ
    simpa only [sub_add_cancel] using this
  set X := loopComp (loopMomenta (-τ) v) with hX
  have heven : ∀ u : Fin 2 → ℝ, P.eval (loopMomenta (u - τ) v) +
      P.eval (loopMomenta (-u - τ) v) =
      2 * (P.eval (loopMomenta (-τ) v) +
        ∑ s, ∑ r, P.hess X (s, 0) (r, 0) * ((u s * u r : ℝ) : ℂ) +
        ∑ s, ∑ r, ∑ t, ∑ q, P.quart (s, 0) (r, 0) (t, 0) (q, 0) *
          ((u s * u r * u t * u q : ℝ) : ℂ)) := fun u => by
    have e1 : loopMomenta (u - τ) v = loopMomenta (-τ) v + loopMomenta u 0 := by
      rw [← loopMomenta_add, add_zero, neg_add_eq_sub]
    have e2 : loopMomenta (-u - τ) v = loopMomenta (-τ) v - loopMomenta u 0 := by
      rw [← loopMomenta_sub, sub_zero]
      congr 1
      abel
    rw [e1, e2, LoopQuartic.eval_add_add_eval_sub, sum_sum_hess_loopComp_energy,
      quartPart_loopComp_energy]
  rw [integral_mul_inv_neg_quadratic_add_pow_of_even_quartic hPD hw (by omega) hint'
    (P.eval (loopMomenta (-τ) v)) (fun s r => P.hess X (s, 0) (r, 0))
    (fun s r t q => P.quart (s, 0) (r, 0) (t, 0) (q, 0)) heven]
  simp only [numEnergyValueQuartic, energyValue, energyValueTwo, energyValueFour,
    LoopQuartic.energyContractTwo, LoopQuartic.energyContractFour]
  rw [show m + 1 - 2 = m - 1 by omega, show m + 1 - 3 = m - 2 by omega]
  have hAU : A.det = symanzikU α (simplexPoint x) := rfl
  rw [hAU]
  push_cast
  ring

theorem integrable_eval_mul_paramDenom_prod_quartic (hm : 3 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (hA : IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
      (symanzikU α (simplexPoint x) ^ 4)⁻¹) (simplexSet m))
    (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) =>
        P.eval (loopMomenta q.2 v) * (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume) := by
  have hm0 : 0 < m := by omega
  have hmeas : AEStronglyMeasurable (fun q : (Fin m → ℝ) × (Fin 2 → ℝ) =>
      P.eval (loopMomenta q.2 v) * (paramDenom α p M ε q.1 q.2 v ^ (m + 1))⁻¹)
      ((volume.restrict (simplexSet m)).prod volume) :=
    (((continuous_eval_loopMomenta_left_quartic P v).comp continuous_snd).mul
      (continuous_paramDenom α p M hε.ne' v)).aestronglyMeasurable
  obtain ⟨Kτ, hKτ⟩ := exists_sum_sq_energyShift_le α p
  have hK : 0 ≤ energyBound α p M v := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta hK hε
  set Kv := P.coeffBound * (1 + ∑ s, ∑ c, v s c ^ 2) ^ 2 with hKv
  have hKv0 : 0 ≤ Kv := mul_nonneg P.coeffBound_nonneg (by positivity)
  set KA := ∑ i, (α i 0 ^ 2 + α i 1 ^ 2) with hKA
  set C := Kv * ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 2 * energyNormConst (m - 1)) with hC
  have : IsFiniteMeasure (volume.restrict (simplexSet m)) :=
    isFiniteMeasure_restrict.mpr (Feynman.isCompact_simplexSet m).measure_lt_top.ne
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    exact integrable_eval_mul_paramDenom_quartic P α p M hm hε hPD v
  · have hb : IntegrableOn (fun x => C * (2 * (1 + 2 * Kτ) ^ 2 *
        (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹ + 8 * (KA ^ 2 +
          (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
            (symanzikU α (simplexPoint x) ^ 4)⁻¹))) (simplexSet m) :=
      (((integrableOn_inv_sqrt_symanzikU α hU).const_mul _).add
        (((integrable_const _).add hA).const_mul _)).const_mul _
    refine hb.mono' hmeas.norm.integral_prod_right' ?_
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hdet : symanzikU α (simplexPoint x) ≠ 0 := hPD.det_pos.ne'
    have hUpos : 0 < symanzikU α (simplexPoint x) := hPD.det_pos
    have hz := Feynman.simplexPoint_mem_stdSimplex hxS
    have hτ := hKτ _ hz.1 hdet
    have htr := trace_symanzikMatrix_le α hz.1 hz.2
    have htr0 : 0 ≤ (symanzikMatrix α (simplexPoint x)).trace := by
      have h0 : 0 < symanzikMatrix α (simplexPoint x) 0 0 := hPD.diag_pos
      have h1 : 0 < symanzikMatrix α (simplexPoint x) 1 1 := hPD.diag_pos
      rw [trace_fin_two]
      linarith
    have hre : |(shiftedConst α p M ε x v).re| ≤ energyBound α p M v := by
      rw [shiftedConst_re]
      exact abs_re_shifted_le α p M hz.1 hz.2 hdet v
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [paramDenom_eq α p M hdet]
    set A := symanzikMatrix α (simplexPoint x) with hAdef
    set τ := energyShift α p (simplexPoint x) with hτdef
    set w := shiftedConst α p M ε x v with hwdef
    set U := symanzikU α (simplexPoint x) with hUdef
    have hw : w.im < 0 := by rw [hwdef, shiftedConst_im]; linarith
    have hAdet : A.det = U := rfl
    set B := 1 + 2 * ∑ i, τ i ^ 2 + 2 * (A.trace / A.det) with hB
    have hB0 : 0 ≤ B := by
      have := trace_div_det_nonneg hPD
      have : 0 ≤ ∑ i, τ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      linarith
    have hBsq : B ^ 2 ≤ 2 * (1 + 2 * Kτ) ^ 2 + 8 * (A.trace ^ 2 * (U ^ 2)⁻¹) := by
      have hτ0 : 0 ≤ ∑ i, τ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hle : B ≤ (1 + 2 * Kτ) + 2 * (A.trace / U) := by rw [hB, hAdet]; linarith
      have h0 : 0 ≤ A.trace / U := div_nonneg htr0 hUpos.le
      have e : A.trace ^ 2 * (U ^ 2)⁻¹ = (A.trace / U) ^ 2 := by rw [div_pow, div_eq_mul_inv]
      rw [e]
      calc B ^ 2 ≤ ((1 + 2 * Kτ) + 2 * (A.trace / U)) ^ 2 := pow_le_pow_left₀ hB0 hle 2
        _ ≤ _ := by nlinarith [sq_nonneg ((1 + 2 * Kτ) - 2 * (A.trace / U))]
    have hint2 := (integrable_one_add_quadratic_pow_mul_norm hPD hw (j := 2)
      (by omega : 2 + 2 ≤ m + 1)).comp_add_right τ
    have hI := integral_one_add_quadratic_pow_mul_norm_le hPD hre (shiftedConst_im α p M x v)
      hδ0 hδ hδε (j := 2) (by omega : 2 + 2 ≤ m + 1)
    rw [show m + 1 - 2 = m - 1 by omega] at hI
    have hI0 : 0 ≤ ∫ u : Fin 2 → ℝ, (1 + u ⬝ᵥ A *ᵥ u) ^ 2 *
        ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖ :=
      integral_nonneg fun u => by
        have := dotProduct_mulVec_self_nonneg hPD u
        positivity
    have hR0 : 0 ≤ (Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 2 *
        ((Real.sqrt A.det)⁻¹ * energyNormConst (m - 1)) := hI0.trans hI
    have hE0 : 0 ≤ energyNormConst (m - 1) := integral_nonneg fun _ => norm_nonneg _
    have hfin : A.trace ^ 2 * (U ^ 2)⁻¹ * (Real.sqrt U)⁻¹ ≤ KA ^ 2 + A.trace ^ 2 * (U ^ 4)⁻¹ := by
      have h1 := inv_sq_mul_inv_sqrt_le U
      have h2 : A.trace ^ 2 ≤ KA ^ 2 := pow_le_pow_left₀ htr0 htr 2
      have h3 : 0 ≤ A.trace ^ 2 := sq_nonneg _
      calc A.trace ^ 2 * (U ^ 2)⁻¹ * (Real.sqrt U)⁻¹
          = A.trace ^ 2 * ((U ^ 2)⁻¹ * (Real.sqrt U)⁻¹) := by ring
        _ ≤ A.trace ^ 2 * (1 + (U ^ 4)⁻¹) := mul_le_mul_of_nonneg_left h1 h3
        _ ≤ _ := by nlinarith
    calc ∫ t, ‖P.eval (loopMomenta t v) *
          ((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖
        ≤ ∫ t, Kv * B ^ 2 * ((1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) ^ 2 *
            ‖((-(((t + τ) ⬝ᵥ A *ᵥ (t + τ) : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖) :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            (hint2.const_mul _) (Eventually.of_forall fun t =>
              norm_eval_mul_inv_le_quartic P hPD τ t v _)
      _ = Kv * B ^ 2 * ∫ u : Fin 2 → ℝ, (1 + u ⬝ᵥ A *ᵥ u) ^ 2 *
            ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖ := by
          rw [integral_const_mul, integral_add_right_eq_self (fun u : Fin 2 → ℝ =>
            (1 + u ⬝ᵥ A *ᵥ u) ^ 2 * ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (m + 1))⁻¹‖) τ]
      _ ≤ Kv * B ^ 2 * ((Real.sqrt δ ^ (m + 1))⁻¹ * 2 ^ 2 *
            ((Real.sqrt A.det)⁻¹ * energyNormConst (m - 1))) :=
          mul_le_mul_of_nonneg_left hI (mul_nonneg hKv0 (sq_nonneg _))
      _ = C * (B ^ 2 * (Real.sqrt U)⁻¹) := by rw [hC, hAdet]; ring
      _ ≤ C * ((2 * (1 + 2 * Kτ) ^ 2 + 8 * (A.trace ^ 2 * (U ^ 2)⁻¹)) * (Real.sqrt U)⁻¹) := by
          have hC0 : 0 ≤ C := by rw [hC]; positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBsq
            (inv_nonneg.mpr (Real.sqrt_nonneg _))) hC0
      _ ≤ C * (2 * (1 + 2 * Kτ) ^ 2 * (Real.sqrt U)⁻¹ + 8 * (KA ^ 2 + A.trace ^ 2 * (U ^ 4)⁻¹)) := by
          have hC0 : 0 ≤ C := by rw [hC]; positivity
          refine mul_le_mul_of_nonneg_left ?_ hC0
          nlinarith [hfin]

/-- **The energy integral at fixed spatial momenta, numerators of degree at most four.** For
`N = m + 1 ≥ 4` propagators, `ε > 0`, two independent `αᵢ`, `U⁻²` and `tr² A · U⁻⁴` integrable on
the simplex, the energy integrand `P(ℓ) ∏ᵢ Dᵢ(t, v)⁻¹` is integrable and
`∫_{ℝ²} P ∏ᵢ Dᵢ⁻¹ dt = m! ∫_Δ (P(-τ, v) E₀ + C₂ E₂ + C₄ E₄) dx` (`numEnergyValueQuartic`). -/
theorem integral_loopQuartic_mul_prod_lineDenom_eq (hm : 3 ≤ m) (hε : 0 < ε)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hU : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m))
    (hA : IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
      (symanzikU α (simplexPoint x) ^ 4)⁻¹) (simplexSet m))
    (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun t : Fin 2 → ℝ =>
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) ∧
      ∫ t : Fin 2 → ℝ, P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic P α p M ε x v := by
  have hm0 : 0 < m := by omega
  have hint := integrable_eval_mul_paramDenom_prod_quartic P α p M hm hε hspan hU hA v
  have hfey : ∀ t : Fin 2 → ℝ,
      P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m,
          P.eval (loopMomenta t v) * (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
    intro t
    have h : ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, (paramDenom α p M ε x t v ^ (m + 1))⁻¹ := by
      refine Feynman.prod_inv_eq_factorial_mul_integral_simplex fun i => ?_
      simp only [lineDenom, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
        add_zero, zero_sub]
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

/-- **The energy integral at fixed spatial momenta under the graph criterion.**
`integral_loopQuartic_mul_prod_lineDenom_eq` with `hspan`, `hU` and the integrability of
`tr² A · U⁻⁴` replaced by `NoSubdivergenceQuartic α` (the complement of every direction class has
at least five lines). -/
theorem integral_loopQuartic_mul_prod_lineDenom_eq_of_criterion (hε : 0 < ε)
    (hcrit : NoSubdivergenceQuartic α) (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun t : Fin 2 → ℝ =>
        P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) ∧
      ∫ t : Fin 2 → ℝ, P.eval (loopMomenta t v) * ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹ =
        (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic P α p M ε x v := by
  have hm : 5 ≤ m := NoSubdivergenceOfOrder.le hcrit
  have h3 : NoSubdivergence α := hcrit.noSubdivergenceQuadratic.noSubdivergence
  exact integral_loopQuartic_mul_prod_lineDenom_eq P α p M (by omega) hε h3.span
    (integrableOn_inv_sq_symanzikU_of_criterion α h3)
    (integrableOn_trace_sq_mul_inv_pow_four_symanzikU α hcrit) v

end StageA

/-! ### Toward the spatial integral: even parts of the coefficients -/

/-- The even part of the quadratic coefficients: the terms linear in `D` cancel,
`H(X + D) + H(X - D) = 2 (H(X) + ∑_cd R^{sym}ₐ_bcd D_c D_d)`. -/
theorem LoopQuartic.hess_add_add_hess_sub (P : LoopQuartic) (X D : LoopIndex → ℂ)
    (a b : LoopIndex) :
    P.hess (X + D) a b + P.hess (X - D) a b =
      2 * (P.hess X a b + ∑ c, ∑ d, P.quartSym a b c d * (D c * D d)) := by
  have h1 := sum_lin_even (fun c => P.cub a b c + P.cub a c b + P.cub c a b) X D
  have h2 := sum_quad_even (fun c d => P.quartSym a b c d) X D
  simp only [LoopQuartic.hess, Pi.add_apply, Pi.sub_apply]
  linear_combination h1 + h2

theorem loopComp_loopMomenta_spatial (y : Fin 2 → Fin 3 → ℝ) (s : Fin 2) (μ : Fin 4) :
    loopComp (loopMomenta 0 y) (s, μ) = Fin.cases 0 (fun c => ((y s c : ℝ) : ℂ)) μ := by
  refine Fin.cases ?_ (fun c => ?_) μ <;> simp [loopComp, loopMomenta]

theorem sum_mul_loopComp_spatial (f : LoopIndex → ℂ) (y : Fin 2 → Fin 3 → ℝ) :
    ∑ a, f a * loopComp (loopMomenta 0 y) a = ∑ s, ∑ c : Fin 3, f (s, c.succ) * ((y s c : ℝ) : ℂ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fin.sum_univ_succ]
  simp [loopComp_loopMomenta_spatial]

theorem sum_sum_mul_loopComp_spatial (H : LoopIndex → LoopIndex → ℂ) (y : Fin 2 → Fin 3 → ℝ) :
    ∑ a, ∑ b, H a b * (loopComp (loopMomenta 0 y) a * loopComp (loopMomenta 0 y) b) =
      ∑ s, ∑ c : Fin 3, ∑ r, ∑ d : Fin 3, H (s, c.succ) (r, d.succ) * ((y s c * y r d : ℝ) : ℂ) := by
  have h1 : ∀ a, ∑ b, H a b * (loopComp (loopMomenta 0 y) a * loopComp (loopMomenta 0 y) b) =
      (∑ r, ∑ d : Fin 3, H a (r, d.succ) * ((y r d : ℝ) : ℂ)) * loopComp (loopMomenta 0 y) a :=
    fun a => by
      rw [← sum_mul_loopComp_spatial (fun b => H a b) y, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
  simp only [h1]
  rw [sum_mul_loopComp_spatial (fun a => ∑ r, ∑ d : Fin 3, H a (r, d.succ) * ((y r d : ℝ) : ℂ)) y]
  simp only [Finset.sum_mul]
  push_cast
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun d _ => by ring

end QED.Integration.TwoLoop

end
