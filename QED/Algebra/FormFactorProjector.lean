/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.FormFactorIndependence
public import QED.Frozen.OneLoop.IsFormFactorPair
import QED.Algebra.Spinor
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Trace projectors onto the form factors

Explicit linear functionals `P₁`, `P₂` of a vertex `V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ` that
return the form factors of the on-shell decomposition (G₀) `QED.OneLoop.IsFormFactorPair`
(obligations O2-11 and O2-21 of `docs/TWO-LOOP-DERIVATION.md`).

Write `P = m - p̸`, `P' = m - p̸'`, `K = p' + p`, `q = p' - p`, `Q = q·q` (mostly-plus metric,
so `Q > 0` for the spacelike momentum transfer) and `D = 4m² + Q`. On shell, `P` maps onto
the solutions of `(p̸ + m) u = 0` and `P'` onto the row solutions of `ū' (p̸' + m) = 0`, so the
on-shell part of `V` is the matrix family `P' V^μ P`. The three traces
* `T₁ V = Σ_μ tr[P' V^μ P γ_μ]` (`QED.Dirac.traceGammaProj`),
* `T₂ V = Σ_μ K_μ tr[P' V^μ P]` and `T₃ V = Σ_μ q_μ tr[P' V^μ P]` (`QED.Dirac.traceVecProj`)
of `P' V^μ P = P' (α γ^μ + β K^μ + c q^μ) P` are `T₁ = (4Q - 8m²) α - 4mD β`,
`T₂ = -4mD α - 2D² β` and `T₃ = 2DQ c`. Inverting,
`P₁ V = (D T₁ - 6m T₂) / (4 e D²)` and `P₂ V = m (mD T₁ + (Q - 2m²) T₂) / (e Q D²)`, and
`T₃ V / (2DQ)` detects a `q^μ` term.

## Main statements

* `QED.OneLoop.eq_formFactorProj_of_isFormFactorPair`: a form-factor pair is
  `(P₁ V, P₂ V)`; this is uniqueness, constructively.
* `QED.OneLoop.formFactorProjQ_eq_zero_of_isFormFactorPair`: a vertex with a form-factor pair
  has no `q^μ` term, `Σ_μ q_μ tr[P' V^μ P] = 0`.
* `QED.OneLoop.isFormFactorPair_formFactorProj`: if, between on-shell spinors, `V^μ` equals
  `a γ^μ + b (p' + p)^μ + d S^{μν} q_ν`, then `(P₁ V, P₂ V)` is a form-factor pair, with
  `P₁ V = (a + 2mb)/e` and `P₂ V = (imd - 2mb)/e`.
* `QED.OneLoop.exists_isFormFactorPair_iff`: if, between on-shell spinors,
  `V^μ = a γ^μ + b (p' + p)^μ + c q^μ + d S^{μν} q_ν`, a form-factor pair exists iff `c = 0`.

The formulas were checked numerically on random on-shell kinematics before the proofs.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- `T₁ V = Σ_μ tr[(m - p̸') V^μ (m - p̸) γ_μ]`. -/
noncomputable def traceGammaProj (m : ℝ) (p' p : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ μ, trace (((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) * gammaLower μ)

/-- `Σ_μ a_μ tr[(m - p̸') V^μ (m - p̸)]`, with `a_μ` the covariant components of `a`. -/
noncomputable def traceVecProj (m : ℝ) (p' p a : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ μ, ((Minkowski.lower a μ : ℝ) : ℂ) *
    trace (((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p))

/-- `tr[(m - p̸')(m - p̸)] = 4m² - 4 p'·p`. -/
theorem trace_mass_sub_slash_mul_mass_sub_slash (m : ℝ) (p' p : Fin 4 → ℝ) :
    trace (((m : ℂ) • 𝟙 - slash p') * ((m : ℂ) • 𝟙 - slash p)) =
      4 * (m : ℂ) ^ 2 - 4 * (Minkowski.dot p' p : ℂ) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, trace_sub, trace_smul, trace_one, Fintype.card_fin, trace_slash,
    trace_slash_mul_slash, smul_eq_mul]
  push_cast
  ring

/-- `tr[(m - p̸') a̸ (m - p̸)] = 4m (p'·a + a·p)`. -/
theorem trace_mass_sub_slash_mul_slash_mul_mass_sub_slash (m : ℝ) (p' p a : Fin 4 → ℝ) :
    trace (((m : ℂ) • 𝟙 - slash p') * slash a * ((m : ℂ) • 𝟙 - slash p)) =
      4 * (m : ℂ) * ((Minkowski.dot p' a : ℂ) + (Minkowski.dot a p : ℂ)) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, trace_sub, trace_smul, trace_slash, trace_slash_mul_slash,
    trace_slash_mul_slash_mul_slash, smul_eq_mul]
  ring

/-- `tr[(m - p̸')(m - p̸) a̸] = 4m (p'·a + p·a)`. -/
theorem trace_mass_sub_slash_mul_mass_sub_slash_mul_slash (m : ℝ) (p' p a : Fin 4 → ℝ) :
    trace (((m : ℂ) • 𝟙 - slash p') * ((m : ℂ) • 𝟙 - slash p) * slash a) =
      4 * (m : ℂ) * ((Minkowski.dot p' a : ℂ) + (Minkowski.dot p a : ℂ)) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, trace_sub, trace_smul, trace_slash, trace_slash_mul_slash,
    trace_slash_mul_slash_mul_slash, smul_eq_mul]
  ring

/-- `γ^μ (m - p̸) γ_μ = -4m - 2 p̸`. -/
theorem sum_gamma_mul_mass_sub_slash_mul_gammaLower (m : ℝ) (p : Fin 4 → ℝ) :
    ∑ μ, gamma μ * ((m : ℂ) • 𝟙 - slash p) * gammaLower μ =
      (m : ℂ) • ((-4 : ℂ) • 𝟙) - (2 : ℂ) • slash p := by
  rw [← contract_one, ← contract_slash, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-- `T₁` of a vertex whose on-shell part is `α γ^μ + (β k^μ + c l^μ)`. No on-shell condition
is needed. -/
theorem traceGammaProj_eq_of_mul_mul_eq {m : ℝ} {p' p k l : Fin 4 → ℝ}
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {α β c : ℂ}
    (h : ∀ μ, ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') * (α • gamma μ + (β * (k μ : ℂ) + c * (l μ : ℂ)) • 𝟙) *
        ((m : ℂ) • 𝟙 - slash p)) :
    traceGammaProj m p' p V =
      α * (-16 * (m : ℂ) ^ 2 - 8 * (Minkowski.dot p' p : ℂ)) +
        4 * (m : ℂ) * (β * ((Minkowski.dot p' k : ℂ) + (Minkowski.dot p k : ℂ)) +
          c * ((Minkowski.dot p' l : ℂ) + (Minkowski.dot p l : ℂ))) := by
  set P : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p with hP
  set P' : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p' with hP'
  have hμ : ∀ μ, trace (P' * V μ * P * gammaLower μ) =
      α * trace (P' * (gamma μ * P * gammaLower μ)) +
        (β * trace (P' * P * ((k μ : ℂ) • gammaLower μ)) +
          c * trace (P' * P * ((l μ : ℂ) • gammaLower μ))) := by
    intro μ
    rw [h μ]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      trace_add, trace_smul, smul_eq_mul, add_smul, Matrix.mul_assoc, mul_smul]
  unfold traceGammaProj
  rw [Finset.sum_congr rfl fun μ _ => hμ μ, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← trace_sum, ← trace_sum, ← trace_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, sum_smul_gammaLower,
    sum_smul_gammaLower, sum_gamma_mul_mass_sub_slash_mul_gammaLower,
    trace_mass_sub_slash_mul_mass_sub_slash_mul_slash,
    trace_mass_sub_slash_mul_mass_sub_slash_mul_slash]
  simp only [hP', Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, trace_sub, trace_smul, trace_one, Fintype.card_fin,
    trace_slash, trace_slash_mul_slash, smul_eq_mul]
  push_cast
  ring

/-- `Σ_μ a_μ tr[P' V^μ P]` of a vertex whose on-shell part is `α γ^μ + (β k^μ + c l^μ)`. No
on-shell condition is needed. -/
theorem traceVecProj_eq_of_mul_mul_eq {m : ℝ} {p' p k l : Fin 4 → ℝ} (a : Fin 4 → ℝ)
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {α β c : ℂ}
    (h : ∀ μ, ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') * (α • gamma μ + (β * (k μ : ℂ) + c * (l μ : ℂ)) • 𝟙) *
        ((m : ℂ) • 𝟙 - slash p)) :
    traceVecProj m p' p a V =
      α * (4 * (m : ℂ) * ((Minkowski.dot p' a : ℂ) + (Minkowski.dot a p : ℂ))) +
        (β * (Minkowski.dot a k : ℂ) + c * (Minkowski.dot a l : ℂ)) *
          (4 * (m : ℂ) ^ 2 - 4 * (Minkowski.dot p' p : ℂ)) := by
  set P : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p with hP
  set P' : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p' with hP'
  have hμ : ∀ μ, ((Minkowski.lower a μ : ℝ) : ℂ) * trace (P' * V μ * P) =
      α * trace (P' * (((Minkowski.lower a μ : ℝ) : ℂ) • gamma μ) * P) +
        (β * (((Minkowski.lower a μ : ℝ) : ℂ) * (k μ : ℂ)) +
          c * (((Minkowski.lower a μ : ℝ) : ℂ) * (l μ : ℂ))) * trace (P' * P) := by
    intro μ
    rw [h μ]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      trace_add, trace_smul, smul_eq_mul]
    ring
  have hdot : ∀ b : Fin 4 → ℝ,
      ∑ μ, ((Minkowski.lower a μ : ℝ) : ℂ) * (b μ : ℂ) = (Minkowski.dot a b : ℂ) := by
    intro b
    rw [Minkowski.dot_eq_sum_lower]
    push_cast
    rfl
  unfold traceVecProj
  rw [Finset.sum_congr rfl fun μ _ => hμ μ, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hdot, hdot]
  rw [show P' * ∑ μ, ((Minkowski.lower a μ : ℝ) : ℂ) • gamma μ = P' * slash a from rfl,
    trace_mass_sub_slash_mul_slash_mul_mass_sub_slash, trace_mass_sub_slash_mul_mass_sub_slash]

/-- If `w X u = w Y u` for every on-shell column `u` (`(p̸ + m) u = 0`) and row `w`
(`w (p̸' + m) = 0`), then `(m - p̸') X (m - p̸) = (m - p̸') Y (m - p̸)`. -/
theorem mass_sub_slash_mul_mul_eq_of_sandwich {m : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    {X Y : Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ u w : Fin 4 → ℂ, slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* slash p' = -((m : ℂ) • w) → w ⬝ᵥ (X *ᵥ u) = w ⬝ᵥ (Y *ᵥ u)) :
    ((m : ℂ) • 𝟙 - slash p') * X * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') * Y * ((m : ℂ) • 𝟙 - slash p) := by
  set P : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p with hP
  set P' : Matrix (Fin 4) (Fin 4) ℂ := (m : ℂ) • 𝟙 - slash p' with hP'
  have hPs : slash p * P = (-(m : ℂ)) • P := slash_mul_mass_sub_slash m p hp
  have hP's : P' * slash p' = (-(m : ℂ)) • P' := mass_sub_slash_mul_slash m p' hp'
  clear_value P P'
  have hu : ∀ x, slash p *ᵥ (P *ᵥ x) = -((m : ℂ) • (P *ᵥ x)) := fun x => by
    rw [mulVec_mulVec, hPs, smul_mulVec, neg_smul]
  have hw : ∀ y, (y ᵥ* P') ᵥ* slash p' = -((m : ℂ) • (y ᵥ* P')) := fun y => by
    rw [vecMul_vecMul, hP's, vecMul_smul, neg_smul]
  rw [← sub_eq_zero, show P' * X * P - P' * Y * P = P' * (X - Y) * P by
    rw [Matrix.mul_sub, Matrix.sub_mul]]
  refine mul_mul_eq_zero_of_sandwich fun x y => ?_
  rw [sub_mulVec, dotProduct_sub, h _ _ (hu x) (hw y), sub_self]

end QED.Dirac

namespace QED.OneLoop

open QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The projector onto `F₁`: `P₁ V = (D T₁ - 6m T₂) / (4 e D²)` with `D = 4m² + q²`,
`T₁ V = Σ_μ tr[(m - p̸') V^μ (m - p̸) γ_μ]` and `T₂ V = Σ_μ (p' + p)_μ tr[(m - p̸') V^μ (m - p̸)]`. -/
noncomputable def formFactorProj₁ (e m : ℝ) (p' p : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ((4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) * traceGammaProj m p' p V -
      6 * (m : ℂ) * traceVecProj m p' p (p' + p) V) /
    (4 * (e : ℂ) * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)

/-- The projector onto `F₂`: `P₂ V = m (m D T₁ + (q² - 2m²) T₂) / (e q² D²)` with `D`, `T₁`,
`T₂` as for `formFactorProj₁`. -/
noncomputable def formFactorProj₂ (e m : ℝ) (p' p : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  (m : ℂ) * ((m : ℂ) * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) *
        traceGammaProj m p' p V +
      ((Minkowski.dot (p' - p) (p' - p) : ℂ) - 2 * (m : ℂ) ^ 2) * traceVecProj m p' p (p' + p) V) /
    ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
      (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2)

/-- The projector onto a `q^μ` term: `T₃ V / (2 D q²)` with
`T₃ V = Σ_μ q_μ tr[(m - p̸') V^μ (m - p̸)]`. -/
noncomputable def formFactorProjQ (m : ℝ) (p' p : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  traceVecProj m p' p (p' - p) V /
    (2 * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) *
      (Minkowski.dot (p' - p) (p' - p) : ℂ))

/-- The three projectors of a vertex whose on-shell part is
`α γ^μ + β (p' + p)^μ + c (p' - p)^μ`: `P₁ V = (α + 2mβ)/e`, `P₂ V = -2mβ/e` and the `q^μ`
projector returns `c`. -/
theorem formFactorProj_eq_of_mul_mul_eq {e m : ℝ} (he : e ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {α β c : ℂ}
    (h : ∀ μ, ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') *
        (α • gamma μ + (β * ((p' μ + p μ : ℝ) : ℂ) + c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙) *
          ((m : ℂ) • 𝟙 - slash p)) :
    formFactorProj₁ e m p' p V = (α + 2 * m * β) / e ∧
      formFactorProj₂ e m p' p V = -(2 * m * β) / e ∧ formFactorProjQ m p' p V = c := by
  have h' : ∀ μ, ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') *
        (α • gamma μ + (β * ((p' + p) μ : ℂ) + c * ((p' - p) μ : ℂ)) • 𝟙) *
          ((m : ℂ) • 𝟙 - slash p) := fun μ => by
    rw [h μ, Pi.add_apply, Pi.sub_apply]
  have T1 := traceGammaProj_eq_of_mul_mul_eq h'
  have T2 := traceVecProj_eq_of_mul_mul_eq (p' + p) h'
  have T3 := traceVecProj_eq_of_mul_mul_eq (p' - p) h'
  -- On-shell kinematics in terms of `d = p'·p`.
  set d := Minkowski.dot p' p with hd
  have k1 : Minkowski.dot p' (p' + p) + Minkowski.dot p (p' + p) = -2 * m ^ 2 + 2 * d := by
    have e : Minkowski.dot p' (p' + p) + Minkowski.dot p (p' + p) =
        Minkowski.dot p' p' + 2 * Minkowski.dot p' p + Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.add_apply]; ring
    rw [e, hp, hp']; ring
  have k2 : Minkowski.dot p' (p' - p) + Minkowski.dot p (p' - p) = 0 := by
    have e : Minkowski.dot p' (p' - p) + Minkowski.dot p (p' - p) =
        Minkowski.dot p' p' - Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.sub_apply]; ring
    rw [e, hp, hp']; ring
  have k3 : Minkowski.dot p' (p' + p) + Minkowski.dot (p' + p) p = -2 * m ^ 2 + 2 * d := by
    rw [Minkowski.dot_comm (p' + p) p, k1]
  have k4 : Minkowski.dot p' (p' - p) + Minkowski.dot (p' - p) p = 0 := by
    rw [Minkowski.dot_comm (p' - p) p, k2]
  have k5 : Minkowski.dot (p' + p) (p' + p) = -2 * m ^ 2 + 2 * d := by
    have e : Minkowski.dot (p' + p) (p' + p) =
        Minkowski.dot p' p' + 2 * Minkowski.dot p' p + Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.add_apply]; ring
    rw [e, hp, hp']; ring
  have k6 : Minkowski.dot (p' + p) (p' - p) = 0 := by
    have e : Minkowski.dot (p' + p) (p' - p) = Minkowski.dot p' p' - Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.add_apply, Pi.sub_apply]; ring
    rw [e, hp, hp']; ring
  have k7 : Minkowski.dot (p' - p) (p' + p) = 0 := by
    rw [Minkowski.dot_comm, k6]
  have hQ : Minkowski.dot (p' - p) (p' - p) = -2 * m ^ 2 - 2 * d := by
    have e : Minkowski.dot (p' - p) (p' - p) =
        Minkowski.dot p' p' - 2 * Minkowski.dot p' p + Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.sub_apply]; ring
    rw [e, hp, hp']; ring
  have kc : ∀ x y : ℝ, (x : ℂ) + (y : ℂ) = ((x + y : ℝ) : ℂ) := fun _ _ => by push_cast; ring
  rw [kc, k1, kc, k2] at T1
  rw [kc, k3, k5, k6] at T2
  rw [kc, k4, k7, hQ] at T3
  have hQpos : 0 < -2 * m ^ 2 - 2 * d := hQ ▸ hq
  have hm1 : (m : ℂ) ^ 2 - (d : ℂ) ≠ 0 := by
    have : (m ^ 2 - d : ℝ) ≠ 0 := by nlinarith [sq_nonneg m]
    exact_mod_cast this
  have hm2 : (m : ℂ) ^ 2 + (d : ℂ) ≠ 0 := by
    have : (m ^ 2 + d : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
  have hD : 4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ) =
      2 * ((m : ℂ) ^ 2 - (d : ℂ)) := by
    rw [hQ]; push_cast; ring
  have hQc : (Minkowski.dot (p' - p) (p' - p) : ℂ) = -2 * ((m : ℂ) ^ 2 + (d : ℂ)) := by
    rw [hQ]; push_cast; ring
  unfold formFactorProj₁ formFactorProj₂ formFactorProjQ
  rw [hD, hQc, T1, T2, T3]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

/-- A form-factor pair `F` puts the on-shell part of `V` in the form
`e (F₁ + F₂) γ^μ - (e F₂ / 2m) (p' + p)^μ` (Gordon identity), with no `q^μ` term. -/
theorem mul_mul_eq_of_isFormFactorPair {e m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {F : ℂ × ℂ} (hF : IsFormFactorPair e m p' p V F)
    (μ : Fin 4) :
    ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') *
        (((e : ℂ) * (F.1 + F.2)) • gamma μ + (-((e : ℂ) * F.2 / (2 * m)) *
          ((p' μ + p μ : ℝ) : ℂ) + 0 * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙) *
          ((m : ℂ) • 𝟙 - slash p) := by
  refine mass_sub_slash_mul_mul_eq_of_sandwich hp' hp fun u w hu hw => ?_
  rw [hF μ u w hu hw, sandwich_formFactor_eq hm hu hw]
  simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  ring

/-- **The projectors return the form factors.** If `F` is a form-factor pair (G₀) of `V` at
on-shell `(p', p)` with `q² > 0`, then `F = (P₁ V, P₂ V)`. In particular the pair is unique. -/
theorem eq_formFactorProj_of_isFormFactorPair {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {F : ℂ × ℂ} (hF : IsFormFactorPair e m p' p V F) :
    F = (formFactorProj₁ e m p' p V, formFactorProj₂ e m p' p V) := by
  obtain ⟨h1, h2, -⟩ := formFactorProj_eq_of_mul_mul_eq he hp' hp hq
    (mul_mul_eq_of_isFormFactorPair hm hp' hp hF)
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [h1, h2]
  refine Prod.ext ?_ ?_
  · dsimp only
    field_simp
    ring
  · dsimp only
    field_simp

/-- A vertex with a form-factor pair has no `q^μ` term: the `q^μ` projector vanishes. -/
theorem formFactorProjQ_eq_zero_of_isFormFactorPair {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {F : ℂ × ℂ} (hF : IsFormFactorPair e m p' p V F) : formFactorProjQ m p' p V = 0 :=
  (formFactorProj_eq_of_mul_mul_eq he hp' hp hq (mul_mul_eq_of_isFormFactorPair hm hp' hp hF)).2.2

/-- The Gordon identity on a general covariant decomposition between on-shell spinors:
`w [a γ^μ + b K^μ + c q^μ + d S^{μν} q_ν] u = w [(a + imd) γ^μ + (b - id/2) K^μ + c q^μ] u`
with `K = p' + p` and `q = p' - p`. -/
theorem sandwich_decomp_eq {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ} {u w : Fin 4 → ℂ}
    (hu : slash p *ᵥ u = -((m : ℂ) • u)) (hw : w ᵥ* slash p' = -((m : ℂ) • w)) (a b c d : ℂ)
    (μ : Fin 4) :
    w ⬝ᵥ ((a • gamma μ + (b * ((p' μ + p μ : ℝ) : ℂ) + c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙 +
        d • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u) =
      w ⬝ᵥ (((a + I * m * d) • gamma μ + ((b - I * d / 2) * ((p' μ + p μ : ℝ) : ℂ) +
        c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙) *ᵥ u) := by
  have hg := sandwich_formFactor_eq hm hu hw 0 (I * m * d) μ
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have c1 : I / (m : ℂ) * (I * m * d) = -d := by
    field_simp
    rw [I_sq]
    ring
  have c2 : I * m * d / (2 * m) = I * d / 2 := by
    field_simp
  rw [c1, c2] at hg
  simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at hg ⊢
  linear_combination hg

/-- The projectors of a vertex that, between on-shell spinors, equals
`a γ^μ + b (p' + p)^μ + c q^μ + d S^{μν} q_ν`: `P₁ V = (a + 2mb)/e`, `P₂ V = (imd - 2mb)/e`,
and the `q^μ` projector returns `c`. -/
theorem formFactorProj_eq_of_sandwich {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {a b c d : ℂ}
    (h : ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* slash p' = -((m : ℂ) • w) →
      w ⬝ᵥ (V μ *ᵥ u) = w ⬝ᵥ ((a • gamma μ + (b * ((p' μ + p μ : ℝ) : ℂ) +
        c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙 +
          d • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u)) :
    formFactorProj₁ e m p' p V = (a + 2 * m * b) / e ∧
      formFactorProj₂ e m p' p V = (I * m * d - 2 * m * b) / e ∧
        formFactorProjQ m p' p V = c := by
  obtain ⟨h1, h2, h3⟩ := formFactorProj_eq_of_mul_mul_eq (α := a + I * m * d)
    (β := b - I * d / 2) (c := c) he hp' hp hq fun μ =>
      mass_sub_slash_mul_mul_eq_of_sandwich hp' hp fun u w hu hw =>
        (h μ u w hu hw).trans (sandwich_decomp_eq hm hu hw a b c d μ)
  refine ⟨h1.trans ?_, h2.trans ?_, h3⟩ <;> congr 1 <;> ring

/-- **Existence from a decomposition without `q^μ` term.** If, between on-shell spinors,
`V^μ = a γ^μ + b (p' + p)^μ + d S^{μν} q_ν`, then `(P₁ V, P₂ V)` is a form-factor pair (G₀)
of `V`. -/
theorem isFormFactorPair_formFactorProj {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {a b d : ℂ}
    (h : ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* slash p' = -((m : ℂ) • w) →
      w ⬝ᵥ (V μ *ᵥ u) = w ⬝ᵥ ((a • gamma μ + (b * ((p' μ + p μ : ℝ) : ℂ)) • 𝟙 +
          d • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u)) :
    IsFormFactorPair e m p' p V (formFactorProj₁ e m p' p V, formFactorProj₂ e m p' p V) := by
  have h' : ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* slash p' = -((m : ℂ) • w) →
      w ⬝ᵥ (V μ *ᵥ u) = w ⬝ᵥ ((a • gamma μ + (b * ((p' μ + p μ : ℝ) : ℂ) +
        0 * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙 +
          d • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u) :=
    fun μ u w hu hw => by rw [h μ u w hu hw, zero_mul, add_zero]
  obtain ⟨h1, h2, -⟩ := formFactorProj_eq_of_sandwich he hm hp' hp hq h'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  intro μ u w hu hw
  rw [h' μ u w hu hw, sandwich_decomp_eq hm hu hw, sandwich_formFactor_eq hm hu hw, h1, h2]
  simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  field_simp
  ring

/-- **The `q^μ` term decides existence (O2-21).** If, between on-shell spinors,
`V^μ = a γ^μ + b (p' + p)^μ + c q^μ + d S^{μν} q_ν`, then `V` has a form-factor pair (G₀) iff
`c = 0`. -/
theorem exists_isFormFactorPair_iff {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {a b c d : ℂ}
    (h : ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* slash p' = -((m : ℂ) • w) →
      w ⬝ᵥ (V μ *ᵥ u) = w ⬝ᵥ ((a • gamma μ + (b * ((p' μ + p μ : ℝ) : ℂ) +
        c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙 +
          d • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u)) :
    (∃ F, IsFormFactorPair e m p' p V F) ↔ c = 0 := by
  constructor
  · rintro ⟨F, hF⟩
    rw [← (formFactorProj_eq_of_sandwich he hm hp' hp hq h).2.2]
    exact formFactorProjQ_eq_zero_of_isFormFactorPair he hm hp' hp hq hF
  · rintro rfl
    exact ⟨_, isFormFactorPair_formFactorProj he hm hp' hp hq fun μ u w hu hw => by
      rw [h μ u w hu hw, zero_mul, add_zero]⟩

/-- **Existence and uniqueness without `q^μ` term.** If, between on-shell spinors,
`V^μ = a γ^μ + b (p' + p)^μ + d S^{μν} q_ν`, then `V` has exactly one form-factor pair (G₀),
namely `(P₁ V, P₂ V) = ((a + 2mb)/e, (imd - 2mb)/e)`. -/
theorem existsUnique_isFormFactorPair_of_sandwich {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {a b d : ℂ}
    (h : ∀ (μ : Fin 4) (u w : Fin 4 → ℂ), slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* slash p' = -((m : ℂ) • w) →
      w ⬝ᵥ (V μ *ᵥ u) = w ⬝ᵥ ((a • gamma μ + (b * ((p' μ + p μ : ℝ) : ℂ)) • 𝟙 +
          d • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • lorentzGen μ ν) *ᵥ u)) :
    ∃! F, IsFormFactorPair e m p' p V F :=
  ⟨_, isFormFactorPair_formFactorProj he hm hp' hp hq h,
    fun _ hF => eq_formFactorProj_of_isFormFactorPair he hm hp' hp hq hF⟩

end QED.OneLoop

end
