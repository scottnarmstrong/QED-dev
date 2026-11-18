/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.FormFactorProjector
import QED.Algebra.Spinor
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Covariant vertices have the on-shell form `a γ^μ + b (p' + p)^μ + c q^μ`

The algebraic half of obligation O2-20 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). Let
`V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ` be a vertex and `(p', p)` an on-shell pair with
`q = p' - p`, `q² > 0`. Call `V` **little-group covariant** at `(p', p)` if
`S V^μ S⁻¹ = L^μ_ν V^ν` for every real matrix `L` fixing `p` and `p'` and every invertible
`S` with `S γ^μ S⁻¹ = L^μ_ν γ^ν` (`QED.Dirac.IsLittleGroupCovariant`). No condition on `L`
beyond these is imposed (the Clifford relation forces `L` to be a Lorentz transformation).
A vertex built from the gamma matrices, the momenta `p, p'` and the metric is covariant in this
sense; so is a parametric integral of such vertices whose integrand is covariant.

**Theorem** (`QED.Dirac.hasOnShellForm_of_isLittleGroupCovariant`). For `m ≠ 0`, on-shell
`p, p'` (`p·p = p'·p' = -m²`, mostly-plus metric) and `q² > 0`, a little-group covariant
vertex satisfies, for some `α, β, c ∈ ℂ` and every `μ`,

`(m - p̸') V^μ (m - p̸) = (m - p̸') (α γ^μ + β (p' + p)^μ + c q^μ) (m - p̸)`,

the hypothesis of `QED.OneLoop.formFactorProj_eq_of_mul_mul_eq`. Consequently
(`QED.OneLoop.exists_isFormFactorPair_iff_of_isLittleGroupCovariant`) such a vertex has a
form-factor pair (G₀) if and only if its `q^μ` projector `formFactorProjQ` vanishes, and then
the pair is unique. A further symmetry, charge conjugation combined with the reflection in
`p + p'`, forces the `q^μ` projector to vanish (`QED.OneLoop.formFactorProjQ_eq_zero_of_mirror`
in `QED/Algebra/SandwichReductionMirror.lean`).

## Proof

* **Reflections.** For `a·a ≠ 0` the reflection `R_a v = v - 2 (a·v)/(a·a) a` is represented on
  spinors by `S_a = a̸ Γ` with `Γ` the chirality matrix: `S_a γ^μ S_a⁻¹ = (R_a)^μ_ν γ^ν`, with
  `S_a⁻¹ = S_a/(a·a)` (`QED.Dirac.isCovariantUnder_reflect_gamma`). If `a·p = a·p' = 0`, then
  `S_a` commutes with `p̸` and `p̸'`.
* **Transport.** Conjugating by `S_a` and acting with `R_a` on the vector index carries a
  little-group covariant vertex at `(p', p)` to one at `(R_a p', R_a p)`, and the on-shell form
  back (`QED.Dirac.hasOnShellForm_of_reflect`). Two reflections bring any on-shell pair to one
  with vanishing components `2, 3` (first `p` to rest, then `p'` into the `x` direction).
* **Canonical pair.** If `p, p'` have vanishing components `2, 3`, the reflections in `e₂`,
  `e₃` and `e₂ + e₃` fix them. With `X^μ = (m - p̸') V^μ (m - p̸)`, covariance gives that `X⁰`,
  `X¹` commute with `γ²Γ` and `γ³Γ`, that `X² γ²` and `X³ γ³` do too, and that
  `S X² S⁻¹ = -X³` for `S = (γ² + γ³)Γ`. Matrices commuting with `γ²Γ` and `γ³Γ` are the span
  of `1, γ⁰, γ¹, γ⁰γ¹` (`QED.Dirac.eq_of_commute_gamma_two_three`, a direct computation), and
  between `m - p̸'` and `m - p̸` these reduce to multiples of `(m - p̸')(m - p̸)` (resp. of
  `(m - p̸') γ^k (m - p̸)`, `k = 2, 3`), by the Dirac equation; this uses
  `D = p⁰p'¹ - p¹p'⁰ ≠ 0`, which holds since `D² = q² (4m² + q²)/4`.

## Main definitions

* `QED.Dirac.vecAct`, `QED.Dirac.IsCovariantUnder`, `QED.Dirac.IsLittleGroupCovariant`.
* `QED.Dirac.HasOnShellForm`: the on-shell form above.
* `QED.Dirac.reflect`, `QED.Dirac.reflectMatrix`, `QED.Dirac.reflSpin`.

## Main statements

* `QED.Dirac.hasOnShellForm_of_isLittleGroupCovariant`: covariance gives the on-shell form.
* `QED.OneLoop.exists_isFormFactorPair_iff_of_isLittleGroupCovariant`: existence of a
  form-factor pair is equivalent to the vanishing of the `q^μ` projector.
* `QED.OneLoop.existsUnique_isFormFactorPair_of_isLittleGroupCovariant`: then it is unique.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The chirality matrix `diag(-1, -1, 1, 1)` of the Weyl representation. -/
local notation "Γ" => Matrix.diagonal ![(-1 : ℂ), -1, 1, 1]

/-! ### The action on the vector index and covariance -/

/-- The action of a real `4 × 4` matrix on the vector index of a vertex:
`(L V)^μ = L^μ_ν V^ν`. -/
noncomputable def vecAct (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => ∑ ν, ((L μ ν : ℝ) : ℂ) • V ν

/-- `V` is covariant under `(L, S, T)`: `S V^μ T = L^μ_ν V^ν` for every `μ` (with `T = S⁻¹` in
the intended use). -/
def IsCovariantUnder (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ, S * V μ * T = vecAct L V μ

/-- **Little-group covariance** at `(p', p)`: `V` is covariant under every `(L, S, S⁻¹)` with
`L p = p`, `L p' = p'` and `S γ^μ S⁻¹ = L^μ_ν γ^ν`. -/
def IsLittleGroupCovariant (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), S * T = 1 →
    IsCovariantUnder L S T gamma → L *ᵥ p = p → L *ᵥ p' = p' → IsCovariantUnder L S T V

/-- The on-shell form of a vertex at `(p', p)`:
`(m - p̸') V^μ (m - p̸) = (m - p̸') (α γ^μ + β (p' + p)^μ + c (p' - p)^μ) (m - p̸)`. -/
def HasOnShellForm (m : ℝ) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ α β c : ℂ, ∀ μ, ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
    ((m : ℂ) • 𝟙 - slash p') *
      (α • gamma μ + (β * ((p' μ + p μ : ℝ) : ℂ) + c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙) *
        ((m : ℂ) • 𝟙 - slash p)

theorem vecAct_vecAct (L M : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    vecAct L (vecAct M V) = vecAct (L * M) V := by
  funext μ
  simp only [vecAct, Finset.smul_sum, smul_smul, Matrix.mul_apply, ofReal_sum, ofReal_mul,
    Finset.sum_smul]
  rw [Finset.sum_comm]

theorem vecAct_one (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : vecAct 1 V = V := by
  funext μ
  simp [vecAct, Matrix.one_apply, apply_ite (fun x : ℝ => (x : ℂ)), ite_smul]

theorem mul_vecAct_mul (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    S * vecAct L V μ * T = vecAct L (fun ν => S * V ν * T) μ := by
  simp only [vecAct, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem vecAct_add (L : Matrix (Fin 4) (Fin 4) ℝ) (A B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : vecAct L (fun ν => A ν + B ν) μ = vecAct L A μ + vecAct L B μ := by
  simp only [vecAct, smul_add, Finset.sum_add_distrib]

theorem vecAct_smul (L : Matrix (Fin 4) (Fin 4) ℝ) (α : ℂ) (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : vecAct L (fun ν => α • A ν) μ = α • vecAct L A μ := by
  simp only [vecAct, Finset.smul_sum, smul_comm _ α]

theorem vecAct_apply_smul_one (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℂ) (μ : Fin 4) :
    vecAct L (fun ν => v ν • 𝟙) μ = (∑ ν, ((L μ ν : ℝ) : ℂ) * v ν) • 𝟙 := by
  simp only [vecAct, smul_smul, Finset.sum_smul]

/-! ### Reflections and their spinor representatives -/

/-- The reflection `R_a v = v - 2 (a·v)/(a·a) a` in the hyperplane orthogonal to `a`. -/
noncomputable def reflect (a v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  v - (2 * Minkowski.dot a v / Minkowski.dot a a) • a

/-- The matrix of `R_a`: `(R_a)^μ_ν = δ^μ_ν - 2 a^μ a_ν/(a·a)`. -/
noncomputable def reflectMatrix (a : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν =>
    (if μ = ν then 1 else 0) - 2 * a μ * Minkowski.lower a ν / Minkowski.dot a a

/-- The spinor representative `S_a = a̸ Γ` of the reflection `R_a`. -/
noncomputable def reflSpin (a : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ := slash a * Γ

theorem dot_sub_smul_left (v w a : Fin 4 → ℝ) (c : ℝ) :
    Minkowski.dot (v - c • a) w = Minkowski.dot v w - c * Minkowski.dot a w := by
  simp only [Minkowski.dot_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem dot_sub_smul_right (v w a : Fin 4 → ℝ) (c : ℝ) :
    Minkowski.dot v (w - c • a) = Minkowski.dot v w - c * Minkowski.dot v a := by
  simp only [Minkowski.dot_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem reflectMatrix_mulVec (a v : Fin 4 → ℝ) : reflectMatrix a *ᵥ v = reflect a v := by
  funext μ
  have h : ∑ ν, 2 * a μ * Minkowski.lower a ν / Minkowski.dot a a * v ν =
      2 * Minkowski.dot a v / Minkowski.dot a a * a μ := by
    rw [Minkowski.dot_eq_sum_lower a v, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun ν _ => by ring
  simp only [reflectMatrix, mulVec, dotProduct, of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, h, reflect,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem dot_reflect {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (v w : Fin 4 → ℝ) :
    Minkowski.dot (reflect a v) (reflect a w) = Minkowski.dot v w := by
  unfold reflect
  rw [dot_sub_smul_left, dot_sub_smul_right, dot_sub_smul_right, Minkowski.dot_comm v a]
  field_simp
  ring

theorem reflect_reflect {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (v : Fin 4 → ℝ) :
    reflect a (reflect a v) = v := by
  have h : Minkowski.dot a (reflect a v) = -Minkowski.dot a v := by
    unfold reflect
    rw [dot_sub_smul_right]
    field_simp
    ring
  unfold reflect at h ⊢
  rw [h]
  funext μ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem reflect_of_dot_eq_zero {a v : Fin 4 → ℝ} (h : Minkowski.dot a v = 0) :
    reflect a v = v := by
  simp [reflect, h]

theorem reflect_add (a v w : Fin 4 → ℝ) : reflect a (v + w) = reflect a v + reflect a w := by
  have h : Minkowski.dot a (v + w) = Minkowski.dot a v + Minkowski.dot a w := by
    simp only [Minkowski.dot_eq, Pi.add_apply]; ring
  funext μ
  simp only [reflect, h, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem reflect_sub (a v w : Fin 4 → ℝ) : reflect a (v - w) = reflect a v - reflect a w := by
  have h : Minkowski.dot a (v - w) = Minkowski.dot a v - Minkowski.dot a w := by
    simp only [Minkowski.dot_eq, Pi.sub_apply]; ring
  funext μ
  simp only [reflect, h, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem reflectMatrix_mul_self {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) :
    reflectMatrix a * reflectMatrix a = 1 := by
  ext μ ν
  have h := congrFun (reflect_reflect ha (Pi.single ν 1)) μ
  rw [← reflectMatrix_mulVec, ← reflectMatrix_mulVec, mulVec_mulVec, mulVec_single_one] at h
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h

/-- `L_a V^μ = V^μ - (2 a^μ/(a·a)) a_ν V^ν`. -/
theorem vecAct_reflectMatrix (a : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) :
    vecAct (reflectMatrix a) V μ =
      V μ - ((2 * a μ / Minkowski.dot a a : ℝ) : ℂ) •
        ∑ ν, ((Minkowski.lower a ν : ℝ) : ℂ) • V ν := by
  simp only [vecAct, reflectMatrix, of_apply, ofReal_sub, sub_smul, Finset.sum_sub_distrib,
    apply_ite (fun x : ℝ => (x : ℂ)), ofReal_one, ofReal_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.smul_sum, smul_smul]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  push_cast
  ring

theorem chirality_mul_gamma_mul (μ : Fin 4) (Y : Matrix (Fin 4) (Fin 4) ℂ) :
    Γ * (gamma μ * Y) = -(gamma μ * (Γ * Y)) := by
  rw [← Matrix.mul_assoc, chirality_mul_gamma, Matrix.neg_mul, Matrix.mul_assoc]

theorem chirality_mul_slash_mul (a : Fin 4 → ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ) :
    Γ * (slash a * Y) = -(slash a * (Γ * Y)) := by
  rw [← Matrix.mul_assoc, chirality_mul_slash, Matrix.neg_mul, Matrix.mul_assoc]

theorem chirality_mul_chirality_mul (Y : Matrix (Fin 4) (Fin 4) ℂ) : Γ * (Γ * Y) = Y := by
  rw [← Matrix.mul_assoc, chirality_mul_chirality, Matrix.one_mul]

/-- `(v - w)̸ = v̸ - w̸`. -/
theorem slash_sub (v w : Fin 4 → ℝ) : slash (v - w) = slash v - slash w := by
  simp only [slash, Minkowski.lower, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    Complex.ofReal_sub, sub_smul]

theorem reflSpin_mul_reflSpin (a : Fin 4 → ℝ) :
    reflSpin a * reflSpin a = ((Minkowski.dot a a : ℝ) : ℂ) • 𝟙 := by
  unfold reflSpin
  simp only [Matrix.mul_assoc, chirality_mul_slash_mul, chirality_mul_chirality, Matrix.mul_neg,
    Matrix.mul_one]
  rw [slash_mul_slash]
  push_cast
  module

theorem reflSpin_mul_inv {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) :
    reflSpin a * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) = 1 := by
  rw [Matrix.mul_smul, reflSpin_mul_reflSpin, smul_smul, inv_mul_cancel₀ (by exact_mod_cast ha),
    one_smul]

theorem inv_mul_reflSpin {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) :
    (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) * reflSpin a = 1 := by
  rw [Matrix.smul_mul, reflSpin_mul_reflSpin, smul_smul, inv_mul_cancel₀ (by exact_mod_cast ha),
    one_smul]

/-- `S_a` commutes with `v̸` if `a·v = 0`. -/
theorem reflSpin_mul_slash {a v : Fin 4 → ℝ} (h : Minkowski.dot a v = 0) :
    reflSpin a * slash v = slash v * reflSpin a := by
  have hc := slash_anticomm a v
  rw [h, mul_zero, ofReal_zero, zero_smul] at hc
  unfold reflSpin
  rw [Matrix.mul_assoc, chirality_mul_slash, Matrix.mul_neg, ← Matrix.mul_assoc,
    eq_neg_of_add_eq_zero_left hc, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

/-- `S_a` commutes with `m - v̸` if `a·v = 0`. -/
theorem reflSpin_mul_mass_sub_slash {a v : Fin 4 → ℝ} (h : Minkowski.dot a v = 0) (m : ℝ) :
    reflSpin a * ((m : ℂ) • 𝟙 - slash v) = ((m : ℂ) • 𝟙 - slash v) * reflSpin a := by
  rw [Matrix.mul_sub, Matrix.sub_mul, reflSpin_mul_slash h, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- `S_a γ^μ S_a = (a·a) γ^μ - 2 a^μ a̸`. -/
theorem reflSpin_mul_gamma_mul_reflSpin (a : Fin 4 → ℝ) (μ : Fin 4) :
    reflSpin a * gamma μ * reflSpin a =
      ((Minkowski.dot a a : ℝ) : ℂ) • gamma μ - ((2 * a μ : ℝ) : ℂ) • slash a := by
  have hc := gamma_slash_anticomm μ a
  have e : slash a * gamma μ = ((-2 * a μ : ℝ) : ℂ) • 𝟙 - gamma μ * slash a :=
    eq_sub_of_add_eq' hc
  unfold reflSpin
  simp only [Matrix.mul_assoc, chirality_mul_gamma_mul, chirality_mul_slash_mul,
    chirality_mul_chirality, Matrix.mul_neg, neg_neg, Matrix.mul_one]
  rw [← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc, slash_mul_slash]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  push_cast
  module

/-- `S_a v̸ S_a = (a·a) v̸ - 2 (a·v) a̸`. -/
theorem reflSpin_mul_slash_mul_reflSpin (a v : Fin 4 → ℝ) :
    reflSpin a * slash v * reflSpin a =
      ((Minkowski.dot a a : ℝ) : ℂ) • slash v -
        ((2 * Minkowski.dot a v : ℝ) : ℂ) • slash a := by
  have hc := slash_anticomm a v
  have e : slash a * slash v = ((-2 * Minkowski.dot a v : ℝ) : ℂ) • 𝟙 - slash v * slash a :=
    eq_sub_of_add_eq hc
  unfold reflSpin
  simp only [Matrix.mul_assoc, chirality_mul_slash_mul, chirality_mul_chirality, Matrix.mul_neg,
    neg_neg, Matrix.mul_one]
  rw [← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc, slash_mul_slash]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  push_cast
  module

/-- `S_a v̸ S_a⁻¹ = (R_a v)̸`. -/
theorem reflSpin_mul_slash_mul_inv {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (v : Fin 4 → ℝ) :
    reflSpin a * slash v * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) =
      slash (reflect a v) := by
  have ha' : ((Minkowski.dot a a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [Matrix.mul_smul, reflSpin_mul_slash_mul_reflSpin, reflect, slash_sub, slash_smul,
    smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ ha', one_smul]
  congr 2
  push_cast
  field_simp

/-- **The spinor representative of a reflection**:
`S_a γ^μ S_a⁻¹ = (R_a)^μ_ν γ^ν` with `S_a = a̸ Γ`, `S_a⁻¹ = S_a/(a·a)`. -/
theorem isCovariantUnder_reflect_gamma {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) :
    IsCovariantUnder (reflectMatrix a) (reflSpin a)
      (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) gamma := by
  intro μ
  have ha' : ((Minkowski.dot a a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [Matrix.mul_smul, reflSpin_mul_gamma_mul_reflSpin, vecAct_reflectMatrix]
  rw [show ∑ ν, ((Minkowski.lower a ν : ℝ) : ℂ) • gamma ν = slash a from rfl, smul_sub, smul_smul,
    smul_smul, inv_mul_cancel₀ ha', one_smul]
  congr 2
  push_cast
  field_simp

/-! ### Transport along a reflection -/

theorem isCovariantUnder_iff (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    IsCovariantUnder L S T V ↔ (fun μ => S * V μ * T) = vecAct L V :=
  ⟨fun h => funext h, fun h μ => congrFun h μ⟩

theorem vecAct_mulVec_apply (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ν, ((L μ ν : ℝ) : ℂ) * ((v ν : ℝ) : ℂ) = (((L *ᵥ v) μ : ℝ) : ℂ) := by
  simp only [mulVec, dotProduct, ofReal_sum, ofReal_mul]

/-- The vertex transported along the reflection `R_a`: `(R_a)^μ_ν S_a V^ν S_a⁻¹`. -/
noncomputable def reflectVertex (a : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  vecAct (reflectMatrix a)
    (fun ν => reflSpin a * V ν * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a))

section Transport

variable {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
include ha

/-- `S_a⁻¹ γ^μ S_a = (R_a)^μ_ν γ^ν` as well. -/
theorem inv_mul_gamma_mul_reflSpin (μ : Fin 4) :
    (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) * gamma μ * reflSpin a =
      vecAct (reflectMatrix a) gamma μ := by
  rw [← isCovariantUnder_reflect_gamma ha μ, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]

/-- **Little-group covariance is transported along a reflection.** -/
theorem isLittleGroupCovariant_reflectVertex {p' p : Fin 4 → ℝ}
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsLittleGroupCovariant p' p V) :
    IsLittleGroupCovariant (reflect a p') (reflect a p) (reflectVertex a V) := by
  intro L S T hST hSγ hLp hLp'
  set Sa := reflSpin a with hSa
  set Ta := (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) with hTa
  set La := reflectMatrix a with hLa
  have hSaTa : Sa * Ta = 1 := reflSpin_mul_inv ha
  have hTaSa : Ta * Sa = 1 := inv_mul_reflSpin ha
  have hLaLa : La * La = 1 := reflectMatrix_mul_self ha
  have hγ : (fun μ => Sa * gamma μ * Ta) = vecAct La gamma :=
    (isCovariantUnder_iff _ _ _ _).1 (isCovariantUnder_reflect_gamma ha)
  have hγ' : (fun μ => Ta * gamma μ * Sa) = vecAct La gamma :=
    funext (inv_mul_gamma_mul_reflSpin ha)
  have hSγ' : (fun μ => S * gamma μ * T) = vecAct L gamma :=
    (isCovariantUnder_iff _ _ _ _).1 hSγ
  have hmv : ∀ v, (La * L * La) *ᵥ (La *ᵥ v) = La *ᵥ (L *ᵥ v) := fun v => by
    rw [mulVec_mulVec, show La * L * La * La = La * L by
      rw [Matrix.mul_assoc (La * L), hLaLa, Matrix.mul_one], ← mulVec_mulVec]
  have hSaTa' : ∀ X, Sa * (Ta * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hSaTa, Matrix.one_mul]
  -- The conjugated triple fixes `p` and `p'`.
  have h0 := hV (La * L * La) (Ta * S * Sa) (Ta * T * Sa)
    (by
      calc Ta * S * Sa * (Ta * T * Sa) = Ta * (S * (Sa * Ta) * T) * Sa := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hSaTa, Matrix.mul_one, hST, Matrix.mul_one, hTaSa])
    (by
      rw [isCovariantUnder_iff]
      calc (fun μ => Ta * S * Sa * gamma μ * (Ta * T * Sa))
          = (fun μ => Ta * (S * (Sa * gamma μ * Ta) * T) * Sa) := by
            funext μ; simp only [Matrix.mul_assoc]
        _ = (fun μ => Ta * (S * vecAct La gamma μ * T) * Sa) := by
            funext μ; rw [← congrFun hγ μ]
        _ = vecAct La (fun ν => Ta * (S * gamma ν * T) * Sa) := by
            funext μ; rw [mul_vecAct_mul, mul_vecAct_mul]
        _ = vecAct La (fun ν => Ta * vecAct L gamma ν * Sa) := by
            rw [← hSγ']
        _ = vecAct La (vecAct L (vecAct La gamma)) := by
            congr 1; funext ν; rw [mul_vecAct_mul, hγ']
        _ = vecAct (La * L * La) gamma := by
            rw [vecAct_vecAct, vecAct_vecAct, Matrix.mul_assoc])
    (by
      rw [show p = La *ᵥ reflect a p by rw [hLa, reflectMatrix_mulVec, reflect_reflect ha]]
      rw [hmv, hLp])
    (by
      rw [show p' = La *ᵥ reflect a p' by rw [hLa, reflectMatrix_mulVec, reflect_reflect ha]]
      rw [hmv, hLp'])
  rw [isCovariantUnder_iff] at h0 ⊢
  set W := fun ρ => Sa * V ρ * Ta with hW
  have hR : reflectVertex a V = vecAct La W := rfl
  rw [hR]
  calc (fun μ => S * vecAct La W μ * T)
      = vecAct La (fun ν => Sa * (Ta * S * Sa * V ν * (Ta * T * Sa)) * Ta) := by
        funext μ
        rw [mul_vecAct_mul]
        congr 1
        funext ν
        simp only [hW, Matrix.mul_assoc, hSaTa', hSaTa, Matrix.mul_one]
    _ = vecAct La (fun ν => Sa * vecAct (La * L * La) V ν * Ta) := by
        rw [← h0]
    _ = vecAct La (vecAct (La * L * La) W) := by
        congr 1; funext ν; rw [mul_vecAct_mul]
    _ = vecAct L (vecAct La W) := by
        rw [vecAct_vecAct, vecAct_vecAct, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLaLa,
          Matrix.one_mul]

/-- `S_a (m - v̸) S_a⁻¹ = m - (R_a v)̸`. -/
theorem reflSpin_mul_mass_sub_slash_mul_inv (m : ℝ) (v : Fin 4 → ℝ) :
    reflSpin a * ((m : ℂ) • 𝟙 - slash v) * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) =
      (m : ℂ) • 𝟙 - slash (reflect a v) := by
  have e : reflSpin a * ((m : ℂ) • 𝟙) * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) =
      (m : ℂ) • (reflSpin a * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_comm]
  rw [Matrix.mul_sub, Matrix.sub_mul, reflSpin_mul_slash_mul_inv ha, e, reflSpin_mul_inv ha]

/-- **The on-shell form is pulled back along a reflection.** -/
theorem hasOnShellForm_of_reflectVertex {m : ℝ} {p' p : Fin 4 → ℝ}
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hF : HasOnShellForm m (reflect a p') (reflect a p) (reflectVertex a V)) :
    HasOnShellForm m p' p V := by
  obtain ⟨α, β, c, hF⟩ := hF
  refine ⟨α, β, c, fun μ => ?_⟩
  set Sa := reflSpin a with hSa
  set Ta := (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) with hTa
  set La := reflectMatrix a with hLa
  have hSaTa : Sa * Ta = 1 := reflSpin_mul_inv ha
  have hTaSa : Ta * Sa = 1 := inv_mul_reflSpin ha
  have hLaLa : La * La = 1 := reflectMatrix_mul_self ha
  have hγ' : (fun μ => Ta * gamma μ * Sa) = vecAct La gamma :=
    funext (inv_mul_gamma_mul_reflSpin ha)
  set P := (m : ℂ) • 𝟙 - slash p with hP
  set P' := (m : ℂ) • 𝟙 - slash p' with hP'
  have hPr : (m : ℂ) • 𝟙 - slash (reflect a p) = Sa * P * Ta :=
    (reflSpin_mul_mass_sub_slash_mul_inv ha m p).symm
  have hPr' : (m : ℂ) • 𝟙 - slash (reflect a p') = Sa * P' * Ta :=
    (reflSpin_mul_mass_sub_slash_mul_inv ha m p').symm
  rw [hPr, hPr'] at hF
  have hTaSa' : ∀ X, Ta * (Sa * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hTaSa, Matrix.one_mul]
  -- `V` is the transport back of `reflectVertex a V`.
  have hVback : V = vecAct La (fun ν => Ta * reflectVertex a V ν * Sa) := by
    have : (fun ν => Ta * reflectVertex a V ν * Sa) = vecAct La V := by
      funext ν
      rw [show reflectVertex a V = vecAct La (fun ν => Sa * V ν * Ta) from rfl, mul_vecAct_mul]
      congr 1
      funext ρ
      simp only [Matrix.mul_assoc, hTaSa', hTaSa, Matrix.mul_one]
    rw [this, vecAct_vecAct, hLaLa, vecAct_one]
  -- Each term.
  have key : ∀ ν, P' * (Ta * reflectVertex a V ν * Sa) * P =
      Ta * (Sa * P' * Ta * reflectVertex a V ν * (Sa * P * Ta)) * Sa := fun ν => by
    simp only [Matrix.mul_assoc, hTaSa', hTaSa, Matrix.mul_one]
  set F : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun ν =>
    α • gamma ν + (β * ((reflect a p' ν + reflect a p ν : ℝ) : ℂ) +
      c * ((reflect a p' ν - reflect a p ν : ℝ) : ℂ)) • 𝟙 with hFdef
  have key2 : ∀ ν, Ta * (Sa * P' * Ta * F ν * (Sa * P * Ta)) * Sa = P' * (Ta * F ν * Sa) * P :=
    fun ν => by
      simp only [Matrix.mul_assoc, hTaSa', hTaSa, Matrix.mul_one]
  have hback : vecAct La (fun ν => Ta * F ν * Sa) μ =
      α • gamma μ + (β * ((p' μ + p μ : ℝ) : ℂ) + c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙 := by
    have e1 : (fun ν => Ta * F ν * Sa) = fun ν => α • (Ta * gamma ν * Sa) +
        (β * ((reflect a (p' + p) ν : ℝ) : ℂ) + c * ((reflect a (p' - p) ν : ℝ) : ℂ)) • 𝟙 := by
      funext ν
      rw [reflect_add, reflect_sub]
      simp only [hFdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hTaSa, Pi.add_apply, Pi.sub_apply]
    have hs : ∀ v : Fin 4 → ℝ, ∑ ν, ((La μ ν : ℝ) : ℂ) * ((reflect a v ν : ℝ) : ℂ) =
        ((v μ : ℝ) : ℂ) := fun v => by
      rw [vecAct_mulVec_apply, hLa, reflectMatrix_mulVec, reflect_reflect ha]
    have hsc : ∑ ν, ((La μ ν : ℝ) : ℂ) * (β * ((reflect a (p' + p) ν : ℝ) : ℂ) +
        c * ((reflect a (p' - p) ν : ℝ) : ℂ)) =
        β * ((p' μ + p μ : ℝ) : ℂ) + c * ((p' μ - p μ : ℝ) : ℂ) := by
      have h1 := hs (p' + p)
      have h2 := hs (p' - p)
      simp only [Pi.add_apply, Pi.sub_apply] at h1 h2
      rw [← h1, ← h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ν _ => by ring
    rw [e1, vecAct_add, vecAct_smul, vecAct_apply_smul_one, hsc, hγ', vecAct_vecAct,
      hLaLa, vecAct_one]
  calc P' * V μ * P
      = vecAct La (fun ν => P' * (Ta * reflectVertex a V ν * Sa) * P) μ := by
        conv_lhs => rw [hVback]
        rw [mul_vecAct_mul]
    _ = vecAct La (fun ν => P' * (Ta * F ν * Sa) * P) μ := by
        congr 1
        funext ν
        rw [key, hF ν, key2]
    _ = P' * vecAct La (fun ν => Ta * F ν * Sa) μ * P := by
        rw [mul_vecAct_mul]
    _ = _ := by rw [hback]

end Transport

/-! ### The canonical pair: momenta in the `(t, x)` plane -/

theorem gamma_two_mul_chirality :
    gamma 2 * Γ = !![0, 0, 0, -I; 0, 0, I, 0; 0, -I, 0, 0; I, 0, 0, 0] := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [gamma]

theorem gamma_three_mul_chirality :
    gamma 3 * Γ = !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0] := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [gamma]

theorem gamma_zero_mul_gamma_one :
    gamma 0 * gamma 1 = !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The commutant of `γ²Γ` and `γ³Γ`** is spanned by `1, γ⁰, γ¹, γ⁰γ¹`. -/
theorem eq_of_commute_gamma_two_three (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (h₂ : gamma 2 * Γ * Y = Y * (gamma 2 * Γ)) (h₃ : gamma 3 * Γ * Y = Y * (gamma 3 * Γ)) :
    Y = Y 3 3 • 𝟙 + Y 3 1 • gamma 0 + (-Y 3 0) • gamma 1 + Y 3 2 • (gamma 0 * gamma 1) := by
  rw [gamma_two_mul_chirality] at h₂
  rw [gamma_three_mul_chirality] at h₃
  have a := fun i j => congrFun (congrFun h₂ i) j
  have b := fun i j => congrFun (congrFun h₃ i) j
  have a00 := a 0 0; have a01 := a 0 1; have a02 := a 0 2; have a03 := a 0 3
  have b00 := b 0 0; have b01 := b 0 1; have b02 := b 0 2; have b03 := b 0 3
  have b30 := b 3 0; have b31 := b 3 1; have b32 := b 3 2; have b33 := b 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at a00 a01 a02 a03 b00 b01 b02 b03 b30 b31 b32 b33
  have k : ∀ x y : ℂ, I * x = y * I → y = x := fun x y h => by
    rw [mul_comm y] at h; exact (mul_left_cancel₀ I_ne_zero h).symm
  have c00 : Y 0 0 = Y 3 3 := k _ _ a03
  have c02 : Y 0 2 = Y 3 1 := k _ _ a01
  have c01 : Y 0 1 = -Y 3 2 := k _ _ (by rw [mul_neg]; exact a02)
  have c03 : Y 0 3 = -Y 3 0 := k _ _ (by rw [mul_neg]; exact a00)
  have c10 : Y 1 0 = -Y 3 2 := by rw [← b30, neg_neg]
  have c12 : Y 1 2 = -Y 3 0 := by rw [← b32, neg_neg]
  have c20 : Y 2 0 = Y 3 1 := b00.trans c02
  have c21 : Y 2 1 = Y 3 0 := by rw [b01, c03, neg_neg]
  have c22 : Y 2 2 = Y 3 3 := b02.trans c00
  have c23 : Y 2 3 = Y 3 2 := by rw [b03, c01, neg_neg]
  rw [gamma_zero_mul_gamma_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, c00, c01, c02, c03, c10, b31, c12, b33, c20, c21, c22, c23]

theorem gamma_zero_mul_gamma_zero : gamma 0 * gamma 0 = 𝟙 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem gamma_one_mul_gamma_one : gamma 1 * gamma 1 = -𝟙 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem gamma_one_mul_gamma_zero : gamma 1 * gamma 0 = -(gamma 0 * gamma 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

/-- The slash of a vector in the `(t, x)` plane. -/
theorem slash_of_two_three {p : Fin 4 → ℝ} (h2 : p 2 = 0) (h3 : p 3 = 0) :
    slash p = ((-p 0 : ℝ) : ℂ) • gamma 0 + ((p 1 : ℝ) : ℂ) • gamma 1 := by
  simp [slash, Minkowski.lower_eq, Fin.sum_univ_four, h2, h3]

theorem slash_mul_slash_of_two_three {p' p : Fin 4 → ℝ} (h2 : p 2 = 0) (h3 : p 3 = 0)
    (h2' : p' 2 = 0) (h3' : p' 3 = 0) :
    slash p * slash p' = ((p 0 * p' 0 - p 1 * p' 1 : ℝ) : ℂ) • 𝟙 -
      ((p 0 * p' 1 - p 1 * p' 0 : ℝ) : ℂ) • (gamma 0 * gamma 1) := by
  rw [slash_of_two_three h2 h3, slash_of_two_three h2' h3']
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    gamma_zero_mul_gamma_zero, gamma_one_mul_gamma_one, gamma_one_mul_gamma_zero]
  push_cast
  module

/-- **Reduction between the on-shell projectors** for momenta in the `(t, x)` plane. Let `G` be a
matrix and suppose that, between `m - p̸'` and `G (m - p̸)`, the matrices `p̸`, `p̸'`, `p̸p̸'`
reduce to multiples of the identity. If `D = p⁰p'¹ - p¹p'⁰ ≠ 0`, then every matrix commuting with
`γ²Γ` and `γ³Γ` reduces likewise. -/
theorem exists_mul_mul_eq_smul_of_commute {p' p : Fin 4 → ℝ} (h2 : p 2 = 0) (h3 : p 3 = 0)
    (h2' : p' 2 = 0) (h3' : p' 3 = 0) (hD : p 0 * p' 1 - p 1 * p' 0 ≠ 0)
    (A B G : Matrix (Fin 4) (Fin 4) ℂ) {κ₁ κ₂ κ₃ : ℂ}
    (h₁ : A * slash p * G * B = κ₁ • (A * G * B))
    (h₂ : A * slash p' * G * B = κ₂ • (A * G * B))
    (h₃ : A * (slash p * slash p') * G * B = κ₃ • (A * G * B))
    (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (hY₂ : gamma 2 * Γ * Y = Y * (gamma 2 * Γ)) (hY₃ : gamma 3 * Γ * Y = Y * (gamma 3 * Γ)) :
    ∃ s : ℂ, A * Y * G * B = s • (A * G * B) := by
  set D : ℂ := ((p 0 * p' 1 - p 1 * p' 0 : ℝ) : ℂ) with hDdef
  have hD' : D ≠ 0 := by rw [hDdef]; exact_mod_cast hD
  set A0 := A * gamma 0 * G * B
  set A1 := A * gamma 1 * G * B
  set A01 := A * (gamma 0 * gamma 1) * G * B
  set Bm := A * G * B
  have lin : ∀ (x y : ℂ) (X Z : Matrix (Fin 4) (Fin 4) ℂ),
      A * (x • X + y • Z) * G * B = x • (A * X * G * B) + y • (A * Z * G * B) := by
    intro x y X Z
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e₁ : ((-p 0 : ℝ) : ℂ) • A0 + ((p 1 : ℝ) : ℂ) • A1 = κ₁ • Bm := by
    rw [← h₁, slash_of_two_three h2 h3, lin]
  have e₂ : ((-p' 0 : ℝ) : ℂ) • A0 + ((p' 1 : ℝ) : ℂ) • A1 = κ₂ • Bm := by
    rw [← h₂, slash_of_two_three h2' h3', lin]
  have e₃ : ((p 0 * p' 0 - p 1 * p' 1 : ℝ) : ℂ) • Bm - D • A01 = κ₃ • Bm := by
    rw [← h₃, slash_mul_slash_of_two_three h2 h3 h2' h3']
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Bm, A01, hDdef]
  have f₀ : D • A0 = (((p 1 : ℝ) : ℂ) * κ₂ - ((p' 1 : ℝ) : ℂ) * κ₁) • Bm := by
    rw [hDdef]
    linear_combination (norm := skip) (-((p' 1 : ℝ) : ℂ)) • e₁ + ((p 1 : ℝ) : ℂ) • e₂
    push_cast
    module
  have f₁ : D • A1 = (((p 0 : ℝ) : ℂ) * κ₂ - ((p' 0 : ℝ) : ℂ) * κ₁) • Bm := by
    rw [hDdef]
    linear_combination (norm := skip) (-((p' 0 : ℝ) : ℂ)) • e₁ + ((p 0 : ℝ) : ℂ) • e₂
    push_cast
    module
  have f₀₁ : D • A01 = (((p 0 * p' 0 - p 1 * p' 1 : ℝ) : ℂ) - κ₃) • Bm := by
    linear_combination (norm := module) (-1 : ℂ) • e₃
  have hYe := eq_of_commute_gamma_two_three Y hY₂ hY₃
  refine ⟨D⁻¹ * (Y 3 3 * D + Y 3 1 * (((p 1 : ℝ) : ℂ) * κ₂ - ((p' 1 : ℝ) : ℂ) * κ₁) +
    (-Y 3 0) * (((p 0 : ℝ) : ℂ) * κ₂ - ((p' 0 : ℝ) : ℂ) * κ₁) +
    Y 3 2 * (((p 0 * p' 0 - p 1 * p' 1 : ℝ) : ℂ) - κ₃)), ?_⟩
  have hsum : D • (A * Y * G * B) = (Y 3 3 * D + Y 3 1 * (((p 1 : ℝ) : ℂ) * κ₂ -
      ((p' 1 : ℝ) : ℂ) * κ₁) + (-Y 3 0) * (((p 0 : ℝ) : ℂ) * κ₂ - ((p' 0 : ℝ) : ℂ) * κ₁) +
      Y 3 2 * (((p 0 * p' 0 - p 1 * p' 1 : ℝ) : ℂ) - κ₃)) • Bm := by
    conv_lhs => rw [hYe]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [smul_add, smul_add, smul_add, smul_comm D (Y 3 1), smul_comm D (-Y 3 0),
      smul_comm D (Y 3 2), f₀, f₁, f₀₁]
    module
  rw [← smul_smul, ← hsum, smul_smul, inv_mul_cancel₀ hD', one_smul]

section Canonical

/-! The reflections in `e₂`, `e₃`, `e₂ + e₃` and the gamma-matrix identities they need. -/

theorem slash_e₂ : slash ![0, 0, 1, 0] = gamma 2 := by
  simp [slash, Minkowski.lower_eq, Fin.sum_univ_four]

theorem slash_e₃ : slash ![0, 0, 0, 1] = gamma 3 := by
  simp [slash, Minkowski.lower_eq, Fin.sum_univ_four]

theorem slash_e₂₃ : slash ![0, 0, 1, 1] = gamma 2 + gamma 3 := by
  simp [slash, Minkowski.lower_eq, Fin.sum_univ_four]

theorem vecAct_reflectMatrix_e₂ (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    vecAct (reflectMatrix ![0, 0, 1, 0]) X = ![X 0, X 1, -X 2, X 3] := by
  funext μ
  rw [vecAct_reflectMatrix]
  fin_cases μ <;> simp [Minkowski.lower_eq, Minkowski.dot_eq, Fin.sum_univ_four]
  module

theorem vecAct_reflectMatrix_e₃ (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    vecAct (reflectMatrix ![0, 0, 0, 1]) X = ![X 0, X 1, X 2, -X 3] := by
  funext μ
  rw [vecAct_reflectMatrix]
  fin_cases μ <;> simp [Minkowski.lower_eq, Minkowski.dot_eq, Fin.sum_univ_four]
  module

theorem vecAct_reflectMatrix_e₂₃ (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    vecAct (reflectMatrix ![0, 0, 1, 1]) X = ![X 0, X 1, -X 3, -X 2] := by
  funext μ
  rw [vecAct_reflectMatrix]
  fin_cases μ <;> simp [Minkowski.lower_eq, Minkowski.dot_eq, Fin.sum_univ_four] <;>
    ring_nf <;> module

theorem gamma_two_mul_gamma_two : gamma 2 * gamma 2 = -𝟙 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem gamma_three_mul_gamma_three : gamma 3 * gamma 3 = -𝟙 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

/-- How `γ⁰, γ¹, γ², γ³` pass `γ²Γ` and `γ³Γ`. -/
theorem gamma_mul_chirality_comm :
    gamma 2 * Γ * gamma 0 = gamma 0 * (gamma 2 * Γ) ∧
    gamma 3 * Γ * gamma 0 = gamma 0 * (gamma 3 * Γ) ∧
    gamma 2 * Γ * gamma 1 = gamma 1 * (gamma 2 * Γ) ∧
    gamma 3 * Γ * gamma 1 = gamma 1 * (gamma 3 * Γ) ∧
    gamma 2 * Γ * gamma 2 = -(gamma 2 * (gamma 2 * Γ)) ∧
    gamma 3 * Γ * gamma 2 = gamma 2 * (gamma 3 * Γ) ∧
    gamma 2 * Γ * gamma 3 = gamma 3 * (gamma 2 * Γ) ∧
    gamma 3 * Γ * gamma 3 = -(gamma 3 * (gamma 3 * Γ)) := by
  rw [gamma_two_mul_chirality, gamma_three_mul_chirality]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four])

variable {m : ℝ} {p' p : Fin 4 → ℝ}

/-- Covariance under a reflection fixing `p, p'`, for the on-shell part
`X^μ = (m - p̸') V^μ (m - p̸)`: `S_n X^μ = (R_n X)^μ S_n`. -/
theorem reflSpin_mul_onShell {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsLittleGroupCovariant p' p V) {n : Fin 4 → ℝ} (hn : Minkowski.dot n n ≠ 0)
    (hnp : Minkowski.dot n p = 0) (hnp' : Minkowski.dot n p' = 0) (μ : Fin 4) :
    reflSpin n * (((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p)) =
      vecAct (reflectMatrix n)
        (fun ν => ((m : ℂ) • 𝟙 - slash p') * V ν * ((m : ℂ) • 𝟙 - slash p)) μ * reflSpin n := by
  set Sn := reflSpin n
  set Tn := (((Minkowski.dot n n : ℝ) : ℂ)⁻¹ • reflSpin n)
  set P := (m : ℂ) • 𝟙 - slash p
  set P' := (m : ℂ) • 𝟙 - slash p'
  have h := hV (reflectMatrix n) Sn Tn (reflSpin_mul_inv hn) (isCovariantUnder_reflect_gamma hn)
    (by rw [reflectMatrix_mulVec, reflect_of_dot_eq_zero hnp])
    (by rw [reflectMatrix_mulVec, reflect_of_dot_eq_zero hnp']) μ
  have hc1 : Sn * P' = P' * Sn := reflSpin_mul_mass_sub_slash hnp' m
  have hc2 : Sn * P = P * Sn := reflSpin_mul_mass_sub_slash hnp m
  have hTS : Tn * Sn = 1 := inv_mul_reflSpin hn
  rw [← mul_vecAct_mul, ← h]
  calc Sn * (P' * V μ * P) = P' * (Sn * V μ) * P := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc1, Matrix.mul_assoc P' Sn]
    _ = P' * (Sn * V μ * (Tn * Sn)) * P := by rw [hTS, Matrix.mul_one]
    _ = P' * (Sn * V μ * Tn) * (Sn * P) := by simp only [Matrix.mul_assoc]
    _ = P' * (Sn * V μ * Tn) * P * Sn := by rw [hc2]; simp only [Matrix.mul_assoc]

/-- The three reductions between the on-shell projectors, for `G` anticommuting with `p̸` and
`p̸'` (only `p̸` is used): `p̸ ↦ m`, `p̸' ↦ -m`, `p̸ p̸' ↦ m² - 2 p·p'`. -/
theorem onShell_reductions_anticomm (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) {G : Matrix (Fin 4) (Fin 4) ℂ}
    (hG : G * slash p = -(slash p * G)) :
    ((m : ℂ) • 𝟙 - slash p') * slash p * G * ((m : ℂ) • 𝟙 - slash p) =
        (m : ℂ) • (((m : ℂ) • 𝟙 - slash p') * G * ((m : ℂ) • 𝟙 - slash p)) ∧
      ((m : ℂ) • 𝟙 - slash p') * slash p' * G * ((m : ℂ) • 𝟙 - slash p) =
        (-(m : ℂ)) • (((m : ℂ) • 𝟙 - slash p') * G * ((m : ℂ) • 𝟙 - slash p)) ∧
      ((m : ℂ) • 𝟙 - slash p') * (slash p * slash p') * G * ((m : ℂ) • 𝟙 - slash p) =
        ((m : ℂ) ^ 2 - 2 * (Minkowski.dot p p' : ℂ)) •
          (((m : ℂ) • 𝟙 - slash p') * G * ((m : ℂ) • 𝟙 - slash p)) := by
  set P := (m : ℂ) • 𝟙 - slash p
  set P' := (m : ℂ) • 𝟙 - slash p'
  have hsP : slash p * P = (-(m : ℂ)) • P := slash_mul_mass_sub_slash m p hp
  have hP's : ∀ X, P' * (slash p' * X) = (-(m : ℂ)) • (P' * X) := fun X => by
    rw [← Matrix.mul_assoc, mass_sub_slash_mul_slash m p' hp', Matrix.smul_mul]
  have r1 : ∀ X, slash p * (slash p' * X) =
      ((-2 * Minkowski.dot p p' : ℝ) : ℂ) • X - slash p' * (slash p * X) := fun X => by
    rw [← Matrix.mul_assoc, eq_sub_of_add_eq (slash_anticomm p p'), Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
  have r2 : ∀ X, slash p * (G * X) = -(G * (slash p * X)) := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG, Matrix.neg_mul, neg_neg]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_assoc, r1, r2, hsP, hP's, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul] <;> push_cast <;> module

/-- The three reductions for `G = 1`: `p̸ ↦ -m`, `p̸' ↦ -m`, `p̸ p̸' ↦ -m² - 2 p·p'`. -/
theorem onShell_reductions_one (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) :
    ((m : ℂ) • 𝟙 - slash p') * slash p * 1 * ((m : ℂ) • 𝟙 - slash p) =
        (-(m : ℂ)) • (((m : ℂ) • 𝟙 - slash p') * 1 * ((m : ℂ) • 𝟙 - slash p)) ∧
      ((m : ℂ) • 𝟙 - slash p') * slash p' * 1 * ((m : ℂ) • 𝟙 - slash p) =
        (-(m : ℂ)) • (((m : ℂ) • 𝟙 - slash p') * 1 * ((m : ℂ) • 𝟙 - slash p)) ∧
      ((m : ℂ) • 𝟙 - slash p') * (slash p * slash p') * 1 * ((m : ℂ) • 𝟙 - slash p) =
        (-(m : ℂ) ^ 2 - 2 * (Minkowski.dot p p' : ℂ)) •
          (((m : ℂ) • 𝟙 - slash p') * 1 * ((m : ℂ) • 𝟙 - slash p)) := by
  set P := (m : ℂ) • 𝟙 - slash p
  set P' := (m : ℂ) • 𝟙 - slash p'
  have hsP : slash p * P = (-(m : ℂ)) • P := slash_mul_mass_sub_slash m p hp
  have hP's : ∀ X, P' * (slash p' * X) = (-(m : ℂ)) • (P' * X) := fun X => by
    rw [← Matrix.mul_assoc, mass_sub_slash_mul_slash m p' hp', Matrix.smul_mul]
  have r1 : ∀ X, slash p * (slash p' * X) =
      ((-2 * Minkowski.dot p p' : ℝ) : ℂ) • X - slash p' * (slash p * X) := fun X => by
    rw [← Matrix.mul_assoc, eq_sub_of_add_eq (slash_anticomm p p'), Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_assoc, Matrix.one_mul, r1, hsP, hP's, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul]
  push_cast
  module

/-- Cramer's rule for the coefficients of `(p' + p)^μ` and `(p' - p)^μ`. -/
theorem solve_two {K₀ K₁ q₀ q₁ r₀ r₁ : ℂ} (h : K₀ * q₁ - K₁ * q₀ ≠ 0) :
    (r₀ * q₁ - r₁ * q₀) / (K₀ * q₁ - K₁ * q₀) * K₀ +
        (r₁ * K₀ - r₀ * K₁) / (K₀ * q₁ - K₁ * q₀) * q₀ = r₀ ∧
      (r₀ * q₁ - r₁ * q₀) / (K₀ * q₁ - K₁ * q₀) * K₁ +
        (r₁ * K₀ - r₀ * K₁) / (K₀ * q₁ - K₁ * q₀) * q₁ = r₁ := by
  constructor <;>
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff h]
    ring

/-- **The canonical case.** For momenta in the `(t, x)` plane, on shell with `q² > 0`, a
little-group covariant vertex has the on-shell form. -/
theorem hasOnShellForm_of_two_three (hm : m ≠ 0) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (h2 : p 2 = 0) (h3 : p 3 = 0) (h2' : p' 2 = 0) (h3' : p' 3 = 0)
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsLittleGroupCovariant p' p V) :
    HasOnShellForm m p' p V := by
  -- `D = p⁰p'¹ - p¹p'⁰ ≠ 0`, from `4 D² = q² (4m² + q²)`.
  have hD : p 0 * p' 1 - p 1 * p' 0 ≠ 0 := by
    have e1 := hp
    have e2 := hp'
    rw [Minkowski.dot_eq, h2, h3] at e1
    rw [Minkowski.dot_eq, h2', h3'] at e2
    have key : 4 * (p 0 * p' 1 - p 1 * p' 0) ^ 2 = Minkowski.dot (p' - p) (p' - p) *
        (4 * m ^ 2 + Minkowski.dot (p' - p) (p' - p)) := by
      rw [Minkowski.dot_eq]
      simp only [Pi.sub_apply, h2, h3, h2', h3']
      linear_combination (-3 * m ^ 2 + p 0 ^ 2 - 4 * p 0 * p' 0 - p 1 ^ 2 + 4 * p 1 * p' 1 +
        6 * p' 0 ^ 2 - 6 * p' 1 ^ 2) * e1 +
        (3 * m ^ 2 - 4 * p 0 * p' 0 + 4 * p 1 * p' 1 + p' 0 ^ 2 - p' 1 ^ 2) * e2
    intro h0
    rw [h0] at key
    have : 0 < Minkowski.dot (p' - p) (p' - p) * (4 * m ^ 2 + Minkowski.dot (p' - p) (p' - p)) :=
      mul_pos hq (by positivity)
    linarith
  set P := (m : ℂ) • 𝟙 - slash p with hP
  set P' := (m : ℂ) • 𝟙 - slash p' with hP'
  obtain ⟨X, hX⟩ : ∃ X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ, X = fun ν => P' * V ν * P :=
    ⟨_, rfl⟩
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have h4m : (4 * (m : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hm')
  -- `P' X P = 4m² X`.
  have hXX : ∀ ν, P' * X ν * P = (4 * (m : ℂ) ^ 2) • X ν := fun ν => by
    have hPP : P * P = (2 * m : ℂ) • P := mass_sub_slash_sq m p hp
    have hPP' : P' * P' = (2 * m : ℂ) • P' := mass_sub_slash_sq m p' hp'
    calc P' * X ν * P = P' * P' * V ν * (P * P) := by simp only [hX, Matrix.mul_assoc]
      _ = (4 * (m : ℂ) ^ 2) • X ν := by
        rw [hPP, hPP']
        simp only [hX, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        congr 1
        ring
  have hXeq : ∀ ν (s : ℂ) (Z : Matrix (Fin 4) (Fin 4) ℂ), P' * X ν * P = s • Z →
      X ν = (s / (4 * (m : ℂ) ^ 2)) • Z := fun ν s Z h => by
    rw [hXX] at h
    rw [div_eq_inv_mul, ← smul_smul, ← h, smul_smul, inv_mul_cancel₀ h4m, one_smul]
  -- Reductions.
  obtain ⟨r1₁, r1₂, r1₃⟩ := onShell_reductions_one hp' hp
  have hcomm := gamma_mul_chirality_comm
  obtain ⟨c20, c30, c21, c31, c22, c32, c23, c33⟩ := hcomm
  have red1 := exists_mul_mul_eq_smul_of_commute h2 h3 h2' h3' hD P' P 1 r1₁ r1₂ r1₃
  have hG2 : ∀ v : Fin 4 → ℝ, v 2 = 0 → gamma 2 * slash v = -(slash v * gamma 2) := fun v hv => by
    rw [eq_neg_iff_add_eq_zero, gamma_slash_anticomm, hv, mul_zero, ofReal_zero, zero_smul]
  have hG3 : ∀ v : Fin 4 → ℝ, v 3 = 0 → gamma 3 * slash v = -(slash v * gamma 3) := fun v hv => by
    rw [eq_neg_iff_add_eq_zero, gamma_slash_anticomm, hv, mul_zero, ofReal_zero, zero_smul]
  obtain ⟨r2₁, r2₂, r2₃⟩ := onShell_reductions_anticomm hp' hp (hG2 p h2)
  obtain ⟨r3₁, r3₂, r3₃⟩ := onShell_reductions_anticomm hp' hp (hG3 p h3)
  have red2 := exists_mul_mul_eq_smul_of_commute h2 h3 h2' h3' hD P' P (gamma 2) r2₁ r2₂ r2₃
  have red3 := exists_mul_mul_eq_smul_of_commute h2 h3 h2' h3' hD P' P (gamma 3) r3₁ r3₂ r3₃
  -- Covariance under the three reflections.
  have dot_e : ∀ v : Fin 4 → ℝ, v 2 = 0 → v 3 = 0 →
      Minkowski.dot ![0, 0, 1, 0] v = 0 ∧ Minkowski.dot ![0, 0, 0, 1] v = 0 ∧
        Minkowski.dot ![0, 0, 1, 1] v = 0 := fun v hv2 hv3 => by
    simp [Minkowski.dot_eq, hv2, hv3]
  obtain ⟨e₂p, e₃p, e₂₃p⟩ := dot_e p h2 h3
  obtain ⟨e₂p', e₃p', e₂₃p'⟩ := dot_e p' h2' h3'
  have n₂ : Minkowski.dot ![0, 0, 1, 0] ![0, 0, 1, 0] ≠ 0 := by simp [Minkowski.dot_eq]
  have n₃ : Minkowski.dot ![0, 0, 0, 1] ![0, 0, 0, 1] ≠ 0 := by simp [Minkowski.dot_eq]
  have n₂₃ : Minkowski.dot ![0, 0, 1, 1] ![0, 0, 1, 1] ≠ 0 := by simp [Minkowski.dot_eq]
  have cov₂ := reflSpin_mul_onShell (m := m) hV n₂ e₂p e₂p'
  have cov₃ := reflSpin_mul_onShell (m := m) hV n₃ e₃p e₃p'
  have cov₂₃ := reflSpin_mul_onShell (m := m) hV n₂₃ e₂₃p e₂₃p'
  simp only [← hP, ← hP', vecAct_reflectMatrix_e₂, vecAct_reflectMatrix_e₃,
    vecAct_reflectMatrix_e₂₃, reflSpin, slash_e₂, slash_e₃, slash_e₂₃] at cov₂ cov₃ cov₂₃
  have hXμ : ∀ μ, P' * V μ * P = X μ := fun μ => by rw [hX]
  simp only [hXμ] at cov₂ cov₃ cov₂₃
  set A₂ := gamma 2 * Γ with hA₂
  set A₃ := gamma 3 * Γ with hA₃
  -- `X⁰` and `X¹` are multiples of `P' P`.
  obtain ⟨s₀, hs₀⟩ := red1 (X 0) (by simpa using cov₂ 0) (by simpa using cov₃ 0)
  obtain ⟨s₁, hs₁⟩ := red1 (X 1) (by simpa using cov₂ 1) (by simpa using cov₃ 1)
  obtain ⟨t₀, ht₀⟩ := red1 (gamma 0) c20 c30
  obtain ⟨t₁, ht₁⟩ := red1 (gamma 1) c21 c31
  simp only [Matrix.mul_one] at hs₀ hs₁ ht₀ ht₁
  -- `X²` and `X³` are multiples of `P' γ² P` and `P' γ³ P`.
  have hX2a : A₂ * X 2 = -(X 2 * A₂) := by
    have := cov₂ 2; simpa [Matrix.neg_mul] using this
  have hX2b : A₃ * X 2 = X 2 * A₃ := by simpa using cov₃ 2
  have hX3a : A₂ * X 3 = X 3 * A₂ := by simpa using cov₂ 3
  have hX3b : A₃ * X 3 = -(X 3 * A₃) := by
    have := cov₃ 3; simpa [Matrix.neg_mul] using this
  obtain ⟨u₂, hu₂⟩ := red2 (X 2 * gamma 2)
    (by rw [← Matrix.mul_assoc, hX2a, Matrix.neg_mul, Matrix.mul_assoc, c22, Matrix.mul_neg,
      neg_neg, Matrix.mul_assoc])
    (by rw [← Matrix.mul_assoc, hX2b, Matrix.mul_assoc, c32, Matrix.mul_assoc])
  obtain ⟨u₃, hu₃⟩ := red3 (X 3 * gamma 3)
    (by rw [← Matrix.mul_assoc, hX3a, Matrix.mul_assoc, c23, Matrix.mul_assoc])
    (by rw [← Matrix.mul_assoc, hX3b, Matrix.neg_mul, Matrix.mul_assoc, c33, Matrix.mul_neg,
      neg_neg, Matrix.mul_assoc])
  have hsq : ∀ (A Y G B : Matrix (Fin 4) (Fin 4) ℂ), G * G = -𝟙 →
      A * (Y * G) * G * B = -(A * Y * B) := fun A Y G B h => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G G B, h, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg,
      Matrix.mul_neg]
  rw [hsq _ _ _ _ gamma_two_mul_gamma_two, neg_eq_iff_eq_neg, ← neg_smul] at hu₂
  rw [hsq _ _ _ _ gamma_three_mul_gamma_three, neg_eq_iff_eq_neg, ← neg_smul] at hu₃
  set B := P' * P with hB
  set B₂ := P' * gamma 2 * P with hB₂
  set B₃ := P' * gamma 3 * P with hB₃
  have hX0 := hXeq 0 _ _ hs₀
  have hX1 := hXeq 1 _ _ hs₁
  have hX2 := hXeq 2 _ _ hu₂
  have hX3 := hXeq 3 _ _ hu₃
  set σ₀ := s₀ / (4 * (m : ℂ) ^ 2)
  set σ₁ := s₁ / (4 * (m : ℂ) ^ 2)
  set β₂ := -u₂ / (4 * (m : ℂ) ^ 2)
  set β₃ := -u₃ / (4 * (m : ℂ) ^ 2)
  -- The reflection in `e₂ + e₃` gives `β₂ = β₃` on `B₃`.
  set A₂₃ := (gamma 2 + gamma 3) * Γ with hA₂₃
  have hcP : A₂₃ * P = P * A₂₃ := by
    have := reflSpin_mul_mass_sub_slash e₂₃p m
    simpa [reflSpin, slash_e₂₃] using this
  have hcP' : A₂₃ * P' = P' * A₂₃ := by
    have := reflSpin_mul_mass_sub_slash e₂₃p' m
    simpa [reflSpin, slash_e₂₃] using this
  have hAA : A₂₃ * A₂₃ = (2 : ℂ) • 𝟙 := by
    have := reflSpin_mul_reflSpin (![0, 0, 1, 1] : Fin 4 → ℝ)
    rw [reflSpin, slash_e₂₃] at this
    rw [this]
    norm_num [Minkowski.dot_eq]
  have hAγ : A₂₃ * gamma 2 = -(gamma 3 * A₂₃) := by
    rw [hA₂₃]
    ext i j
    rw [Matrix.neg_apply]
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;> simp [gamma]
  have hdiag : A₂₃ * X 2 = -X 3 * A₂₃ := by simpa using cov₂₃ 2
  have hβ : β₂ • B₃ = β₃ • B₃ := by
    have e1 : A₂₃ * X 2 = (-β₂) • (B₃ * A₂₃) := by
      rw [hX2, Matrix.mul_smul, hB₂, hB₃]
      calc β₂ • (A₂₃ * (P' * gamma 2 * P)) = β₂ • (P' * (A₂₃ * gamma 2) * P) := by
            simp only [← Matrix.mul_assoc, hcP']
        _ = (-β₂) • (P' * gamma 3 * P * A₂₃) := by
            rw [hAγ, Matrix.mul_neg, Matrix.neg_mul, smul_neg, neg_smul]
            simp only [Matrix.mul_assoc, hcP]
    have e2 : -X 3 * A₂₃ = (-β₃) • (B₃ * A₂₃) := by
      rw [hX3, Matrix.neg_mul, Matrix.smul_mul, neg_smul]
    have e3 : β₂ • (B₃ * A₂₃) = β₃ • (B₃ * A₂₃) := by
      have := hdiag
      rw [e1, e2, neg_smul, neg_smul, neg_inj] at this
      exact this
    have e4 := congrArg (· * A₂₃) e3
    simp only [Matrix.smul_mul, Matrix.mul_assoc, hAA, Matrix.mul_smul, Matrix.mul_one,
      smul_smul] at e4
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have := congrArg (fun Z => (2 : ℂ)⁻¹ • Z) e4
    simp only [smul_smul] at this
    rwa [mul_comm β₂, mul_comm β₃, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ h2, one_mul,
      one_mul] at this
  -- Solve for the coefficients of `(p' + p)^μ` and `(p' - p)^μ`.
  set K₀ : ℂ := ((p' 0 + p 0 : ℝ) : ℂ)
  set K₁ : ℂ := ((p' 1 + p 1 : ℝ) : ℂ)
  set q₀ : ℂ := ((p' 0 - p 0 : ℝ) : ℂ)
  set q₁ : ℂ := ((p' 1 - p 1 : ℝ) : ℂ)
  have hdet : K₀ * q₁ - K₁ * q₀ ≠ 0 := by
    have : K₀ * q₁ - K₁ * q₀ = ((2 * (p 0 * p' 1 - p 1 * p' 0) : ℝ) : ℂ) := by
      simp only [K₀, K₁, q₀, q₁]; push_cast; ring
    rw [this]
    exact_mod_cast mul_ne_zero two_ne_zero hD
  set r₀ := σ₀ - β₂ * t₀
  set r₁ := σ₁ - β₂ * t₁
  have key₀ : σ₀ = β₂ * t₀ + ((r₀ * q₁ - r₁ * q₀) / (K₀ * q₁ - K₁ * q₀) * K₀ +
      (r₁ * K₀ - r₀ * K₁) / (K₀ * q₁ - K₁ * q₀) * q₀) := by
    rw [(solve_two hdet).1]
    simp only [r₀]
    ring
  have key₁ : σ₁ = β₂ * t₁ + ((r₀ * q₁ - r₁ * q₀) / (K₀ * q₁ - K₁ * q₀) * K₁ +
      (r₁ * K₀ - r₀ * K₁) / (K₀ * q₁ - K₁ * q₀) * q₁) := by
    rw [(solve_two hdet).2]
    simp only [r₁]
    ring
  refine ⟨β₂, (r₀ * q₁ - r₁ * q₀) / (K₀ * q₁ - K₁ * q₀),
    (r₁ * K₀ - r₀ * K₁) / (K₀ * q₁ - K₁ * q₀), fun μ => ?_⟩
  have hdist : ∀ (x y : ℂ) (Z : Matrix (Fin 4) (Fin 4) ℂ),
      P' * (x • Z + y • 𝟙) * P = x • (P' * Z * P) + y • B := fun x y Z => by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hB]
  rw [hXμ, hdist]
  fin_cases μ
  · simp only [Fin.zero_eta]
    rw [hX0, ht₀, smul_smul, ← add_smul]
    congr 1
  · simp only [Fin.mk_one]
    rw [hX1, ht₁, smul_smul, ← add_smul]
    congr 1
  · simp only [Fin.reduceFinMk]
    rw [hX2, h2, h2']
    simp [hB₂]
  · simp only [Fin.reduceFinMk]
    rw [hX3, h3, h3', ← hβ]
    simp [hB₃]

end Canonical

/-! ### The general pair -/

section General

variable {m : ℝ} {p' p : Fin 4 → ℝ}

theorem hasOnShellForm_of_reflect {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (h : ∀ W, IsLittleGroupCovariant (reflect a p') (reflect a p) W →
      HasOnShellForm m (reflect a p') (reflect a p) W)
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsLittleGroupCovariant p' p V) :
    HasOnShellForm m p' p V :=
  hasOnShellForm_of_reflectVertex ha (h _ (isLittleGroupCovariant_reflectVertex ha hV))

/-- The kinematic hypotheses are preserved by a reflection. -/
theorem onShell_reflect {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    Minkowski.dot (reflect a p') (reflect a p') = -m ^ 2 ∧
      Minkowski.dot (reflect a p) (reflect a p) = -m ^ 2 ∧
      0 < Minkowski.dot (reflect a p' - reflect a p) (reflect a p' - reflect a p) := by
  rw [dot_reflect ha, dot_reflect ha, ← reflect_sub, dot_reflect ha]
  exact ⟨hp', hp, hq⟩

/-- The case `p⃗ = 0`: one reflection puts `p'` in the `(t, x)` plane. -/
theorem hasOnShellForm_of_rest (hm : m ≠ 0) (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (h1 : p 1 = 0) (h2 : p 2 = 0) (h3 : p 3 = 0)
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsLittleGroupCovariant p' p V) :
    HasOnShellForm m p' p V := by
  set k := Real.sqrt (p' 1 ^ 2 + p' 2 ^ 2 + p' 3 ^ 2) with hk
  have hk2 : k ^ 2 = p' 1 ^ 2 + p' 2 ^ 2 + p' 3 ^ 2 := Real.sq_sqrt (by positivity)
  set b : Fin 4 → ℝ := ![0, p' 1 - k, p' 2, p' 3] with hb
  have hbb : Minkowski.dot b b = (p' 1 - k) ^ 2 + p' 2 ^ 2 + p' 3 ^ 2 := by
    simp [hb, Minkowski.dot_eq]; ring
  by_cases h0 : Minkowski.dot b b = 0
  · have e2 : p' 2 = 0 := by nlinarith [sq_nonneg (p' 1 - k), sq_nonneg (p' 2), sq_nonneg (p' 3)]
    have e3 : p' 3 = 0 := by nlinarith [sq_nonneg (p' 1 - k), sq_nonneg (p' 2), sq_nonneg (p' 3)]
    exact hasOnShellForm_of_two_three hm hp' hp hq h2 h3 e2 e3 hV
  · refine hasOnShellForm_of_reflect h0 (fun W hW => ?_) hV
    obtain ⟨hp'r, hpr, hqr⟩ := onShell_reflect h0 hp' hp hq
    have hbp : Minkowski.dot b p = 0 := by simp [hb, Minkowski.dot_eq, h1, h2, h3]
    have hbp' : 2 * Minkowski.dot b p' / Minkowski.dot b b = 1 := by
      rw [div_eq_one_iff_eq h0, hbb]
      simp only [hb, Minkowski.dot_eq]
      simp
      nlinarith [hk2]
    have hrp : reflect b p = p := reflect_of_dot_eq_zero hbp
    have hrp' : reflect b p' = p' - b := by simp [reflect, hbp']
    refine hasOnShellForm_of_two_three hm hp'r hpr hqr ?_ ?_ ?_ ?_ hW
    · rw [hrp, h2]
    · rw [hrp, h3]
    · rw [hrp']; simp [hb]
    · rw [hrp']; simp [hb]

/-- **Covariance gives the on-shell form (O2-20, algebraic half).** For `m ≠ 0`, on-shell `p`,
`p'` with `q² > 0`, every little-group covariant vertex `V` satisfies
`(m - p̸') V^μ (m - p̸) = (m - p̸') (α γ^μ + β (p' + p)^μ + c (p' - p)^μ) (m - p̸)` for some
`α, β, c ∈ ℂ` and all `μ`. -/
theorem hasOnShellForm_of_isLittleGroupCovariant (hm : m ≠ 0)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsLittleGroupCovariant p' p V) : HasOnShellForm m p' p V := by
  set a : Fin 4 → ℝ := p - ![m, 0, 0, 0] with ha
  have hp_c : -(p 0 * p 0) + p 1 * p 1 + p 2 * p 2 + p 3 * p 3 = -m ^ 2 := by
    rw [← Minkowski.dot_eq]; exact hp
  have haa : Minkowski.dot a a = 2 * m * (p 0 - m) := by
    simp only [ha, Minkowski.dot_eq, Pi.sub_apply]
    simp
    linear_combination hp_c
  by_cases h0 : Minkowski.dot a a = 0
  · have e0 : p 0 = m := by
      rw [haa] at h0
      have : p 0 - m = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exact absurd (by linarith : m = 0) hm
        · exact h
      linarith
    have hs : p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 0 := by rw [e0] at hp_c; linear_combination hp_c
    have e1 : p 1 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
    have e2 : p 2 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
    have e3 : p 3 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
    exact hasOnShellForm_of_rest hm hp' hp hq e1 e2 e3 hV
  · refine hasOnShellForm_of_reflect h0 (fun W hW => ?_) hV
    obtain ⟨hp'r, hpr, hqr⟩ := onShell_reflect h0 hp' hp hq
    have hap : 2 * Minkowski.dot a p / Minkowski.dot a a = 1 := by
      rw [div_eq_one_iff_eq h0, haa]
      simp only [ha, Minkowski.dot_eq, Pi.sub_apply]
      simp
      linear_combination 2 * hp_c
    have hrp : reflect a p = p - a := by simp [reflect, hap]
    refine hasOnShellForm_of_rest hm hp'r hpr hqr ?_ ?_ ?_ hW <;>
      rw [hrp, ha] <;> simp only [Pi.sub_apply, sub_sub_cancel] <;> rfl

end General

end QED.Dirac

namespace QED.OneLoop

open QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- Between on-shell spinors, `X` and `Y` agree if `(m - p̸') X (m - p̸) = (m - p̸') Y (m - p̸)`. -/
theorem sandwich_eq_of_mul_mul_eq {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    {X Y : Matrix (Fin 4) (Fin 4) ℂ}
    (h : ((m : ℂ) • 𝟙 - slash p') * X * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') * Y * ((m : ℂ) • 𝟙 - slash p))
    {u w : Fin 4 → ℂ} (hu : slash p *ᵥ u = -((m : ℂ) • u)) (hw : w ᵥ* slash p' = -((m : ℂ) • w)) :
    w ⬝ᵥ (X *ᵥ u) = w ⬝ᵥ (Y *ᵥ u) := by
  have hPu : ((m : ℂ) • 𝟙 - slash p) *ᵥ u = (2 * (m : ℂ)) • u := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, hu]; module
  have hwP : w ᵥ* ((m : ℂ) • 𝟙 - slash p') = (2 * (m : ℂ)) • w := by
    rw [vecMul_sub, vecMul_smul, vecMul_one, hw]; module
  have key : ∀ Z : Matrix (Fin 4) (Fin 4) ℂ, w ⬝ᵥ ((((m : ℂ) • 𝟙 - slash p') * Z *
      ((m : ℂ) • 𝟙 - slash p)) *ᵥ u) = (4 * (m : ℂ) ^ 2) * (w ⬝ᵥ (Z *ᵥ u)) := fun Z => by
    rw [← mulVec_mulVec, hPu, ← mulVec_mulVec, dotProduct_mulVec, hwP, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have h4 : (4 * (m : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (by exact_mod_cast hm))
  have := key X
  rw [h, key Y] at this
  exact (mul_left_cancel₀ h4 this).symm

/-- **Form factors of a covariant vertex (O2-21 reduced to the `q^μ` projector).** For
`e, m ≠ 0`, on-shell `p, p'` with `q² > 0`, a little-group covariant vertex has a form-factor
pair (G₀) if and only if its `q^μ` projector `formFactorProjQ` vanishes. -/
theorem exists_isFormFactorPair_iff_of_isLittleGroupCovariant {e m : ℝ} (he : e ≠ 0)
    (hm : m ≠ 0) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsLittleGroupCovariant p' p V) :
    (∃ F, IsFormFactorPair e m p' p V F) ↔ formFactorProjQ m p' p V = 0 := by
  obtain ⟨α, β, c, h⟩ := hasOnShellForm_of_isLittleGroupCovariant hm hp' hp hq hV
  rw [(formFactorProj_eq_of_mul_mul_eq he hp' hp hq h).2.2]
  refine exists_isFormFactorPair_iff he hm hp' hp hq (a := α) (b := β) (c := c) (d := 0)
    fun μ u w hu hw => ?_
  rw [sandwich_eq_of_mul_mul_eq hm (h μ) hu hw, zero_smul, add_zero]

/-- **Existence and uniqueness of the form factors of a covariant vertex without `q^μ`
term.** -/
theorem existsUnique_isFormFactorPair_of_isLittleGroupCovariant {e m : ℝ} (he : e ≠ 0)
    (hm : m ≠ 0) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hV : IsLittleGroupCovariant p' p V)
    (hQ : formFactorProjQ m p' p V = 0) : ∃! F, IsFormFactorPair e m p' p V F := by
  obtain ⟨F, hF⟩ := (exists_isFormFactorPair_iff_of_isLittleGroupCovariant he hm hp' hp hq hV).2 hQ
  exact ⟨F, hF, fun G hG => (eq_formFactorProj_of_isFormFactorPair he hm hp' hp hq hG).trans
    (eq_formFactorProj_of_isFormFactorPair he hm hp' hp hq hF).symm⟩

end QED.OneLoop

end
