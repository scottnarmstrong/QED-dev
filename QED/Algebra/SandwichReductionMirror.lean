/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.SandwichReduction
public import QED.Algebra.ChargeConjugation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The mirror symmetry forbids the `q^μ` term

The algebraic half of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), by charge
conjugation. Let `K = p' + p`, `q = p' - p` for on-shell `p, p'` with `q² > 0`, so that
`K·K = -4m² - q² ≠ 0`. The reflection `R_K` in `K` maps `p ↦ -p'` and `p' ↦ -p` and fixes `q`;
`S_K = K̸ Γ` represents it on spinors (`QED.Dirac.isCovariantUnder_reflect_gamma`). With the
charge-conjugation matrix `C` (`C γ^μ C = -(γ^μ)ᵀ`, `C² = 1`), the **mirror** of a vertex is
`𝓜(V)^μ = S_K C (V^μ)ᵀ C S_K⁻¹`.

For the full QED vertex, charge conjugation gives `C V^μ(p', p)ᵀ C = -V^μ(-p, -p')`, and
covariance under the reflection `R_K` turns the right side into `-(R_K)^μ_ν V^ν(p', p)`; the
order-`e⁵` classes are exchanged in mirror pairs (`C₊ ↔ C₋`, `S₊ ↔ S₋`) or are self-mirror.
The vertex then satisfies the **mirror identity** `𝓜(V)^μ = -(R_K)^μ_ν V^ν`.

**Theorem** (`QED.OneLoop.formFactorProjQ_eq_zero_of_mirror`). A vertex with the on-shell form
`(m - p̸') V^μ (m - p̸) = (m - p̸') (α γ^μ + β K^μ + c q^μ) (m - p̸)` that satisfies the mirror
identity has `c = 0`; hence its `q^μ` projector vanishes, and a little-group covariant vertex
satisfying the mirror identity has exactly one form-factor pair
(`QED.OneLoop.existsUnique_isFormFactorPair_of_mirror`).

## Proof

`𝓜` is linear, fixes multiples of the identity, sends `γ^μ` to `-(R_K)^μ_ν γ^ν` and commutes
with the on-shell projection `Z ↦ (m - p̸') Z (m - p̸)`, because
`C (m - p̸)ᵀ C = m + p̸` and `S_K (m + p̸) S_K⁻¹ = m + (R_K p)̸ = m - p̸'`. Applying `𝓜` to the
on-shell form and comparing with `-(R_K)^μ_ν` of it, where `R_K K = -K` and `R_K q = q`, gives
`2 c q^μ (m - p̸')(m - p̸) = 0`. The trace of `(m - p̸')(m - p̸)` is `8m² + 2q² ≠ 0`, so
`c q^μ = 0` for all `μ`, and `c = 0` since `q ≠ 0`.
-/

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

open QED.Dirac

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The mirror identity `S_K C (V^μ)ᵀ C S_K⁻¹ = -(R_K)^μ_ν V^ν`, `K = p' + p`. -/
def IsMirrorSymmetric (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ, reflSpin (p' + p) * (chargeConj * (V μ)ᵀ * chargeConj) *
      (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p)) =
    -vecAct (reflectMatrix (p' + p)) V μ

/-- `C (γ^μ)ᵀ C = -γ^μ`. -/
theorem chargeConj_mul_transpose_gamma_mul_chargeConj (μ : Fin 4) :
    chargeConj * (gamma μ)ᵀ * chargeConj = -gamma μ := by
  have h' : (gamma μ)ᵀ = -(chargeConj * gamma μ * chargeConj) := by
    rw [chargeConj_mul_gamma_mul_chargeConj, neg_neg]
  rw [h', Matrix.mul_neg, Matrix.neg_mul]
  congr 1
  simp only [← Matrix.mul_assoc, chargeConj_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, chargeConj_mul_self, Matrix.mul_one]

/-- `C (v̸)ᵀ C = -v̸`. -/
theorem chargeConj_mul_transpose_slash_mul_chargeConj (v : Fin 4 → ℝ) :
    chargeConj * (slash v)ᵀ * chargeConj = -slash v := by
  simp only [slash, Matrix.transpose_sum, Matrix.transpose_smul, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, chargeConj_mul_transpose_gamma_mul_chargeConj, smul_neg,
    Finset.sum_neg_distrib]

/-- `C (m - v̸)ᵀ C = m + v̸`. -/
theorem chargeConj_mul_transpose_mass_sub_slash_mul_chargeConj (m : ℝ) (v : Fin 4 → ℝ) :
    chargeConj * ((m : ℂ) • 𝟙 - slash v)ᵀ * chargeConj = (m : ℂ) • 𝟙 + slash v := by
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_sub,
    Matrix.sub_mul, chargeConj_mul_transpose_slash_mul_chargeConj, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, chargeConj_mul_self, sub_neg_eq_add]

section Mirror

variable {m : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
  (hp : Minkowski.dot p p = -m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
include hp' hp hq

theorem dot_add_self_ne_zero : Minkowski.dot (p' + p) (p' + p) ≠ 0 := by
  have e : Minkowski.dot (p' + p) (p' + p) = -4 * m ^ 2 - Minkowski.dot (p' - p) (p' - p) := by
    have h1 : Minkowski.dot (p' + p) (p' + p) =
        Minkowski.dot p' p' + 2 * Minkowski.dot p' p + Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.add_apply]; ring
    have h2 : Minkowski.dot (p' - p) (p' - p) =
        Minkowski.dot p' p' - 2 * Minkowski.dot p' p + Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.sub_apply]; ring
    rw [h1, h2, hp, hp']; ring
  rw [e]
  have := sq_nonneg m
  linarith

/-- The reflection in `K = p' + p` maps `p ↦ -p'`, `p' ↦ -p`, and fixes `q = p' - p`. -/
theorem reflect_add_self :
    reflect (p' + p) p = -p' ∧ reflect (p' + p) p' = -p ∧ reflect (p' + p) (p' - p) = p' - p := by
  have hK := dot_add_self_ne_zero hp' hp hq
  have hKK : Minkowski.dot (p' + p) (p' + p) =
      Minkowski.dot p' p' + 2 * Minkowski.dot p' p + Minkowski.dot p p := by
    simp only [Minkowski.dot_eq, Pi.add_apply]; ring
  have hKp : Minkowski.dot (p' + p) p = Minkowski.dot p' p + Minkowski.dot p p := by
    simp only [Minkowski.dot_eq, Pi.add_apply]; ring
  have hKp' : Minkowski.dot (p' + p) p' = Minkowski.dot p' p' + Minkowski.dot p' p := by
    simp only [Minkowski.dot_eq, Pi.add_apply]; ring
  have hKq : Minkowski.dot (p' + p) (p' - p) = 0 := by
    have : Minkowski.dot (p' + p) (p' - p) = Minkowski.dot p' p' - Minkowski.dot p p := by
      simp only [Minkowski.dot_eq, Pi.add_apply, Pi.sub_apply]; ring
    rw [this, hp, hp', sub_self]
  have c1 : 2 * Minkowski.dot (p' + p) p / Minkowski.dot (p' + p) (p' + p) = 1 := by
    rw [div_eq_one_iff_eq hK, hKp, hKK, hp, hp']; ring
  have c2 : 2 * Minkowski.dot (p' + p) p' / Minkowski.dot (p' + p) (p' + p) = 1 := by
    rw [div_eq_one_iff_eq hK, hKp', hKK, hp, hp']; ring
  refine ⟨?_, ?_, reflect_of_dot_eq_zero hKq⟩
  · simp only [reflect, c1, one_smul]; abel
  · simp only [reflect, c2, one_smul]; abel

/-- **The mirror symmetry kills the `q^μ` term.** -/
theorem eq_zero_of_mirror {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {α β c : ℂ}
    (hF : ∀ μ, ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') *
        (α • gamma μ + (β * ((p' μ + p μ : ℝ) : ℂ) + c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙) *
          ((m : ℂ) • 𝟙 - slash p))
    (hM : IsMirrorSymmetric p' p V) : c = 0 := by
  have hK := dot_add_self_ne_zero hp' hp hq
  obtain ⟨hRp, hRp', hRq⟩ := reflect_add_self hp' hp hq
  set S := reflSpin (p' + p) with hS
  set T := (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p)) with hT
  set L := reflectMatrix (p' + p) with hL
  set C := chargeConj with hC
  set P := (m : ℂ) • 𝟙 - slash p with hP
  set P' := (m : ℂ) • 𝟙 - slash p' with hP'
  have hST : S * T = 1 := reflSpin_mul_inv hK
  have hTS : T * S = 1 := inv_mul_reflSpin hK
  have hCC : C * C = 1 := chargeConj_mul_self
  -- The mirror map and its properties.
  set M : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ := fun Z => S * (C * Zᵀ * C) * T
    with hM_def
  have hSvT : ∀ v, S * ((m : ℂ) • 𝟙 + slash v) * T = (m : ℂ) • 𝟙 + slash (reflect (p' + p) v) :=
    fun v => by
      rw [Matrix.mul_add, Matrix.add_mul, reflSpin_mul_slash_mul_inv hK, Matrix.mul_smul S,
        Matrix.mul_one, Matrix.smul_mul, hST]
  have hMP : ∀ Z, M (P' * Z * P) = P' * M Z * P := fun Z => by
    simp only [hM_def, Matrix.transpose_mul]
    have e1 : C * (Pᵀ * (Zᵀ * P'ᵀ)) * C = (C * Pᵀ * C) * (C * Zᵀ * C) * (C * P'ᵀ * C) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C C, hCC, Matrix.one_mul, ← Matrix.mul_assoc C C, hCC,
        Matrix.one_mul]
    rw [e1, hP, hP', chargeConj_mul_transpose_mass_sub_slash_mul_chargeConj,
      chargeConj_mul_transpose_mass_sub_slash_mul_chargeConj]
    have e2 : S * (((m : ℂ) • 𝟙 + slash p) * (C * Zᵀ * C) * ((m : ℂ) • 𝟙 + slash p')) * T =
        (S * ((m : ℂ) • 𝟙 + slash p) * T) * (S * (C * Zᵀ * C) * T) *
          (S * ((m : ℂ) • 𝟙 + slash p') * T) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc T S, hTS, Matrix.one_mul, ← Matrix.mul_assoc T S, hTS,
        Matrix.one_mul]
    rw [e2, hSvT, hSvT, hRp, hRp', slash_neg, slash_neg, ← sub_eq_add_neg, ← sub_eq_add_neg]
  have hMγ : ∀ μ, M (gamma μ) = -vecAct L gamma μ := fun μ => by
    simp only [hM_def]
    rw [chargeConj_mul_transpose_gamma_mul_chargeConj, Matrix.mul_neg, Matrix.neg_mul,
      isCovariantUnder_reflect_gamma hK μ]
  have hM1 : ∀ x : ℂ, M (x • 𝟙) = x • 𝟙 := fun x => by
    simp only [hM_def, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hCC, hST]
  have hMlin : ∀ (x : ℂ) (A B : Matrix (Fin 4) (Fin 4) ℂ), M (x • A + B) = x • M A + M B :=
    fun x A B => by
      simp only [hM_def, Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  -- Compare the two expressions for `P' 𝓜(V^μ) P`.
  set F : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun ν =>
    α • gamma ν + (β * ((p' ν + p ν : ℝ) : ℂ) + c * ((p' ν - p ν : ℝ) : ℂ)) • 𝟙 with hFdef
  have hLv : ∀ (v : Fin 4 → ℝ) (μ : Fin 4),
      ∑ ν, ((L μ ν : ℝ) : ℂ) * ((v ν : ℝ) : ℂ) = ((reflect (p' + p) v μ : ℝ) : ℂ) :=
    fun v μ => by rw [vecAct_mulVec_apply, hL, reflectMatrix_mulVec]
  have hLF : ∀ μ, vecAct L F μ = α • vecAct L gamma μ +
      (-(β * ((p' μ + p μ : ℝ) : ℂ)) + c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙 := fun μ => by
    have e : F = fun ν => α • gamma ν + (β * (((p' + p) ν : ℝ) : ℂ) +
        c * (((p' - p) ν : ℝ) : ℂ)) • 𝟙 := by
      funext ν; simp only [hFdef, Pi.add_apply, Pi.sub_apply]
    rw [e, vecAct_add, vecAct_smul, vecAct_apply_smul_one]
    congr 2
    have hRK : reflect (p' + p) (p' + p) = -(p' + p) := by
      rw [reflect_add, hRp, hRp']; abel
    simp only [mul_add, Finset.sum_add_distrib]
    rw [show ∑ ν, ((L μ ν : ℝ) : ℂ) * (β * (((p' + p) ν : ℝ) : ℂ)) =
        β * ∑ ν, ((L μ ν : ℝ) : ℂ) * (((p' + p) ν : ℝ) : ℂ) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ν _ => by ring,
      show ∑ ν, ((L μ ν : ℝ) : ℂ) * (c * (((p' - p) ν : ℝ) : ℂ)) =
        c * ∑ ν, ((L μ ν : ℝ) : ℂ) * (((p' - p) ν : ℝ) : ℂ) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ν _ => by ring,
      hLv, hLv, hRK, hRq]
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, ofReal_neg]
    ring
  have key : ∀ μ, ((2 * c * ((p' μ - p μ : ℝ) : ℂ)) • (P' * P)) = 0 := fun μ => by
    have e1 : P' * M (V μ) * P = P' * (-(α • vecAct L gamma μ) +
        (β * ((p' μ + p μ : ℝ) : ℂ) + c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙) * P := by
      rw [← hMP, hF μ, hMP, hMlin, hMγ, hM1, smul_neg]
    have e2 : P' * M (V μ) * P = P' * (-(α • vecAct L gamma μ) +
        (β * ((p' μ + p μ : ℝ) : ℂ) - c * ((p' μ - p μ : ℝ) : ℂ)) • 𝟙) * P := by
      have h := hM μ
      simp only [← hS, ← hL, ← hC] at h
      rw [show M (V μ) = S * (C * (V μ)ᵀ * C) * T from rfl, h, Matrix.mul_neg, Matrix.neg_mul,
        mul_vecAct_mul]
      have : (fun ν => P' * V ν * P) = fun ν => P' * F ν * P := funext hF
      rw [this, ← mul_vecAct_mul, hLF, ← Matrix.neg_mul, ← Matrix.mul_neg]
      congr 2
      rw [neg_add]
      congr 1
      rw [← neg_smul]
      congr 1
      ring
    have h0 := sub_eq_zero.mpr (e1.symm.trans e2)
    refine Eq.trans ?_ h0
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    module
  -- Take the trace.
  have htr : trace (P' * P) ≠ 0 := by
    rw [hP, hP', trace_mass_sub_slash_mul_mass_sub_slash]
    have e : Minkowski.dot (p' - p) (p' - p) = -2 * m ^ 2 - 2 * Minkowski.dot p' p := by
      have h2 : Minkowski.dot (p' - p) (p' - p) =
          Minkowski.dot p' p' - 2 * Minkowski.dot p' p + Minkowski.dot p p := by
        simp only [Minkowski.dot_eq, Pi.sub_apply]; ring
      rw [h2, hp, hp']; ring
    have : (4 * m ^ 2 - 4 * Minkowski.dot p' p : ℝ) ≠ 0 := by
      have := sq_nonneg m
      nlinarith
    exact_mod_cast this
  have hcq : ∀ μ, c * ((p' μ - p μ : ℝ) : ℂ) = 0 := fun μ => by
    have := congrArg trace (key μ)
    rw [trace_smul, trace_zero, smul_eq_mul, mul_eq_zero] at this
    rcases this with h | h
    · linear_combination h / 2
    · exact absurd h htr
  by_contra hc
  have hz : ∀ μ, p' μ - p μ = 0 := fun μ => by
    have := hcq μ
    rw [mul_eq_zero] at this
    exact_mod_cast this.resolve_left hc
  have : Minkowski.dot (p' - p) (p' - p) = 0 := by
    simp [Minkowski.dot_eq, Pi.sub_apply, hz]
  linarith

end Mirror

/-- **The `q^μ` projector of a covariant, mirror-symmetric vertex vanishes.** -/
theorem formFactorProjQ_eq_zero_of_mirror {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsLittleGroupCovariant p' p V) (hM : IsMirrorSymmetric p' p V) :
    formFactorProjQ m p' p V = 0 := by
  obtain ⟨α, β, c, h⟩ := hasOnShellForm_of_isLittleGroupCovariant hm hp' hp hq hV
  rw [(formFactorProj_eq_of_mul_mul_eq he hp' hp hq h).2.2]
  exact eq_zero_of_mirror hp' hp hq h hM

/-- **A covariant, mirror-symmetric vertex has exactly one form-factor pair (G₀)**, for
`e, m ≠ 0`, on-shell `p, p'` and `q² > 0`. -/
theorem existsUnique_isFormFactorPair_of_mirror {e m : ℝ} (he : e ≠ 0) (hm : m ≠ 0)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsLittleGroupCovariant p' p V) (hM : IsMirrorSymmetric p' p V) :
    ∃! F, IsFormFactorPair e m p' p V F :=
  existsUnique_isFormFactorPair_of_isLittleGroupCovariant he hm hp' hp hq hV
    (formFactorProjQ_eq_zero_of_mirror he hm hp' hp hq hV hM)

end QED.OneLoop

end
