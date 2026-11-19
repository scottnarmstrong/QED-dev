/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.SandwichReduction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# A reflection-covariant vertex at `p' = p` in the rest frame

Helper level for the reality and the form of the order-`e⁵` vertex at `q = 0`
(`QED.GradedProof.GEx2.VertexZeroInput`). Let `p₀ = (m, 0, 0, 0)` (`restVec`), so that
`p̸₀ = -m γ⁰` and the on-shell spinors `p̸₀ u = -m u`, `w p̸₀ = -m w` are those with `γ⁰ u = u`,
`w γ⁰ = w`. Let `V^μ` be covariant under the reflections `R_n` in the spatial vectors `n`
(`S_n V^μ S_n⁻¹ = (R_n)^μ_ν V^ν`, `S_n = n̸ Γ`). Then between on-shell spinors at `p₀`,
`w V^μ u = c · w γ^μ u` with `c = V⁰₃₃ + V⁰₃₁` (`sandwichEq_restVec`):

* `V⁰` commutes with `S_{e₂}`, `S_{e₃}`, hence lies in the span of `1, γ⁰, γ¹, γ⁰γ¹`
  (`QED.Dirac.eq_of_commute_gamma_two_three`), and `γ¹`, `γ⁰γ¹` vanish between rest spinors;
* `V¹` has the same form, and `S_{e₁}` flips its sign, so it vanishes between rest spinors;
* the reflections in `e₁ - e₂`, `e₁ - e₃` carry `V¹` to `V²`, `V³`.

`SandwichEq m p X c G` records `w X u = c · w G u` for all on-shell `u, w` at `p`.
-/

@[expose] public section

open Matrix Complex

namespace QED.GradedProof.V5Zero.Dirac

open QED.Dirac

/-- `w X u = c · w G u` for every pair of on-shell spinors `p̸ u = -m u`, `w p̸ = -m w`. -/
def SandwichEq (m : ℝ) (p : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ)
    (G : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ u w : Fin 4 → ℂ, slash p *ᵥ u = -((m : ℂ) • u) → w ᵥ* slash p = -((m : ℂ) • w) →
    w ⬝ᵥ (X *ᵥ u) = c * (w ⬝ᵥ (G *ᵥ u))

/-- The rest momentum `p₀ = (m, 0, 0, 0)`. -/
def restVec (m : ℝ) : Fin 4 → ℝ := ![m, 0, 0, 0]

theorem slash_restVec (m : ℝ) : slash (restVec m) = (-(m : ℂ)) • gamma 0 := by
  simp [slash, Minkowski.lower_eq, Fin.sum_univ_four, restVec]

theorem dot_restVec (m : ℝ) : Minkowski.dot (restVec m) (restVec m) = -m ^ 2 := by
  simp [Minkowski.dot_eq, restVec]
  ring

/-! ### Moving on-shell spinors -/

/-- If `Q A = A P`, then `A` maps on-shell spinors of `P` to on-shell spinors of `Q`. -/
theorem onShell_mulVec {Q A P : Matrix (Fin 4) (Fin 4) ℂ} (hA : Q * A = A * P) {m : ℂ}
    {u : Fin 4 → ℂ} (hu : P *ᵥ u = -(m • u)) : Q *ᵥ (A *ᵥ u) = -(m • (A *ᵥ u)) := by
  rw [mulVec_mulVec, hA, ← mulVec_mulVec, hu, mulVec_neg, mulVec_smul]

/-- If `B Q = P B`, then `B` maps on-shell row spinors of `P` to on-shell row spinors of `Q`. -/
theorem onShell_vecMul {Q B P : Matrix (Fin 4) (Fin 4) ℂ} (hB : B * Q = P * B) {m : ℂ}
    {w : Fin 4 → ℂ} (hw : w ᵥ* P = -(m • w)) : (w ᵥ* B) ᵥ* Q = -(m • (w ᵥ* B)) := by
  rw [vecMul_vecMul, hB, ← vecMul_vecMul, hw, neg_vecMul, smul_vecMul]

/-- `(w B) X (A u) = w (B X A) u`. -/
theorem dotProduct_conj (w u : Fin 4 → ℂ) (A B X : Matrix (Fin 4) (Fin 4) ℂ) :
    (w ᵥ* B) ⬝ᵥ (X *ᵥ (A *ᵥ u)) = w ⬝ᵥ ((B * X * A) *ᵥ u) := by
  rw [← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-! ### Rest-frame spinors -/

theorem gamma_zero_mulVec_of_rest {m : ℝ} (hm : m ≠ 0) {u : Fin 4 → ℂ}
    (hu : slash (restVec m) *ᵥ u = -((m : ℂ) • u)) : gamma 0 *ᵥ u = u := by
  rw [slash_restVec, smul_mulVec, neg_smul, neg_inj] at hu
  exact smul_right_injective _ (by exact_mod_cast hm) hu

theorem vecMul_gamma_zero_of_rest {m : ℝ} (hm : m ≠ 0) {w : Fin 4 → ℂ}
    (hw : w ᵥ* slash (restVec m) = -((m : ℂ) • w)) : w ᵥ* gamma 0 = w := by
  rw [slash_restVec, vecMul_smul, neg_smul, neg_inj] at hw
  exact smul_right_injective _ (by exact_mod_cast hm) hw

theorem gamma_zero_mul_gamma_mul_gamma_zero {i : Fin 4} (hi : i ≠ 0) :
    gamma 0 * gamma i * gamma 0 = -gamma i := by
  fin_cases i
  · exact absurd rfl hi
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gamma, Matrix.mul_apply, Fin.sum_univ_four]

/-- Between rest spinors the spatial `γ^i` vanish. -/
theorem dotProduct_gamma_eq_zero {u w : Fin 4 → ℂ} (hu : gamma 0 *ᵥ u = u)
    (hw : w ᵥ* gamma 0 = w) {i : Fin 4} (hi : i ≠ 0) : w ⬝ᵥ (gamma i *ᵥ u) = 0 := by
  have h : w ⬝ᵥ (gamma i *ᵥ u) = -(w ⬝ᵥ (gamma i *ᵥ u)) := by
    conv_lhs => rw [← hu, ← hw, dotProduct_conj, gamma_zero_mul_gamma_mul_gamma_zero hi]
    rw [neg_mulVec, dotProduct_neg]
  linear_combination h / 2

/-- **The `S_{e₂}`, `S_{e₃}` commutant between rest spinors**: `w Y u = (Y₃₃ + Y₃₁) w γ⁰ u`. -/
theorem sandwichEq_of_commute {m : ℝ} (hm : m ≠ 0) {Y : Matrix (Fin 4) (Fin 4) ℂ}
    (h₂ : reflSpin ![0, 0, 1, 0] * Y = Y * reflSpin ![0, 0, 1, 0])
    (h₃ : reflSpin ![0, 0, 0, 1] * Y = Y * reflSpin ![0, 0, 0, 1]) :
    SandwichEq m (restVec m) Y (Y 3 3 + Y 3 1) (gamma 0) := by
  intro u w hu hw
  have hu0 := gamma_zero_mulVec_of_rest hm hu
  have hw0 := vecMul_gamma_zero_of_rest hm hw
  rw [reflSpin, slash_e₂] at h₂
  rw [reflSpin, slash_e₃] at h₃
  have hY := congrArg (fun Z => w ⬝ᵥ (Z *ᵥ u)) (eq_of_commute_gamma_two_three Y h₂ h₃)
  rw [hY]
  simp only [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  have h1 := dotProduct_gamma_eq_zero hu0 hw0 (by decide : (1 : Fin 4) ≠ 0)
  have h01 : w ⬝ᵥ ((gamma 0 * gamma 1) *ᵥ u) = 0 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, hw0, h1]
  rw [h01, h1, hu0]
  ring

/-! ### Reflections in spatial vectors -/

theorem vecAct_reflectMatrix_e₁ (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    vecAct (reflectMatrix ![0, 1, 0, 0]) X = ![X 0, -X 1, X 2, X 3] := by
  funext μ
  rw [vecAct_reflectMatrix]
  fin_cases μ <;> simp [Minkowski.lower_eq, Minkowski.dot_eq, Fin.sum_univ_four]
  module

theorem vecAct_reflectMatrix_e₁₂ (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    vecAct (reflectMatrix ![0, 1, -1, 0]) X 1 = X 2 := by
  rw [vecAct_reflectMatrix]
  simp [Minkowski.lower_eq, Minkowski.dot_eq, Fin.sum_univ_four]
  module

theorem vecAct_reflectMatrix_e₁₃ (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    vecAct (reflectMatrix ![0, 1, 0, -1]) X 1 = X 3 := by
  rw [vecAct_reflectMatrix]
  simp [Minkowski.lower_eq, Minkowski.dot_eq, Fin.sum_univ_four]
  module

/-- Covariance under a reflection gives commutation with `S_n`. -/
theorem reflSpin_mul_comm {n : Fin 4 → ℝ} (hn : Minkowski.dot n n ≠ 0)
    {Y : Matrix (Fin 4) (Fin 4) ℂ}
    (h : reflSpin n * Y * (((Minkowski.dot n n : ℝ) : ℂ)⁻¹ • reflSpin n) = Y) :
    reflSpin n * Y = Y * reflSpin n := by
  calc reflSpin n * Y
      = reflSpin n * Y * ((((Minkowski.dot n n : ℝ) : ℂ)⁻¹ • reflSpin n) * reflSpin n) := by
        rw [inv_mul_reflSpin hn, Matrix.mul_one]
    _ = Y * reflSpin n := by rw [← Matrix.mul_assoc, h]

/-- A reflection in a spatial vector maps rest spinors to rest spinors, and transports a
sandwich identity at `p₀`: `w (S X T) u` is a sandwich of `X` between on-shell spinors. -/
theorem sandwich_reflSpin {m : ℝ} {n : Fin 4 → ℝ} (hn0 : n 0 = 0)
    {X : Matrix (Fin 4) (Fin 4) ℂ} {c : ℂ} {G : Matrix (Fin 4) (Fin 4) ℂ}
    (hX : SandwichEq m (restVec m) X c G) {u w : Fin 4 → ℂ}
    (hu : slash (restVec m) *ᵥ u = -((m : ℂ) • u))
    (hw : w ᵥ* slash (restVec m) = -((m : ℂ) • w)) :
    w ⬝ᵥ ((reflSpin n * X * (((Minkowski.dot n n : ℝ) : ℂ)⁻¹ • reflSpin n)) *ᵥ u) =
      c * (w ⬝ᵥ ((reflSpin n * G * (((Minkowski.dot n n : ℝ) : ℂ)⁻¹ • reflSpin n)) *ᵥ u)) := by
  have hnp : Minkowski.dot n (restVec m) = 0 := by simp [Minkowski.dot_eq, restVec, hn0]
  have hc := reflSpin_mul_slash hnp
  have hcT : (((Minkowski.dot n n : ℝ) : ℂ)⁻¹ • reflSpin n) * slash (restVec m) =
      slash (restVec m) * (((Minkowski.dot n n : ℝ) : ℂ)⁻¹ • reflSpin n) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hc]
  have hu' := onShell_mulVec hcT.symm hu
  have hw' := onShell_vecMul hc hw
  rw [← dotProduct_conj, ← dotProduct_conj]
  exact hX _ _ hu' hw'

/-- **The rest-frame theorem.** If the vertex `V` at `p₀ = (m, 0, 0, 0)` is covariant under the
reflections in the spatial vectors `n` (those with `n⁰ = 0`), then between on-shell spinors at
`p₀`, `w V^μ u = (V⁰₃₃ + V⁰₃₁) · w γ^μ u` for every `μ`. -/
theorem sandwichEq_restVec {m : ℝ} (hm : m ≠ 0) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : ∀ n : Fin 4 → ℝ, Minkowski.dot n n ≠ 0 → n 0 = 0 → ∀ μ,
      reflSpin n * V μ * (((Minkowski.dot n n : ℝ) : ℂ)⁻¹ • reflSpin n) =
        vecAct (reflectMatrix n) V μ) (μ : Fin 4) :
    SandwichEq m (restVec m) (V μ) (V 0 3 3 + V 0 3 1) (gamma μ) := by
  have d₂ : Minkowski.dot ![0, 0, 1, 0] ![0, 0, 1, 0] ≠ 0 := by simp [Minkowski.dot_eq]
  have d₃ : Minkowski.dot ![0, 0, 0, 1] ![0, 0, 0, 1] ≠ 0 := by simp [Minkowski.dot_eq]
  have d₁ : Minkowski.dot ![0, 1, 0, 0] ![0, 1, 0, 0] ≠ 0 := by simp [Minkowski.dot_eq]
  have d₁₂ : Minkowski.dot ![0, 1, -1, 0] ![0, 1, -1, 0] ≠ 0 := by
    simp [Minkowski.dot_eq]
  have d₁₃ : Minkowski.dot ![0, 1, 0, -1] ![0, 1, 0, -1] ≠ 0 := by
    simp [Minkowski.dot_eq]
  have comm : ∀ ν : Fin 4, ν = 0 ∨ ν = 1 →
      SandwichEq m (restVec m) (V ν) (V ν 3 3 + V ν 3 1) (gamma 0) := by
    intro ν hν
    refine sandwichEq_of_commute hm (reflSpin_mul_comm d₂ ?_) (reflSpin_mul_comm d₃ ?_)
    · rw [hV _ d₂ rfl, vecAct_reflectMatrix_e₂]
      rcases hν with rfl | rfl <;> rfl
    · rw [hV _ d₃ rfl, vecAct_reflectMatrix_e₃]
      rcases hν with rfl | rfl <;> rfl
  -- the spatial component `V¹` vanishes between rest spinors
  have h₁ : SandwichEq m (restVec m) (V 1) 0 (gamma 1) := by
    intro u w hu hw
    have e := sandwich_reflSpin (n := ![0, 1, 0, 0]) rfl (comm 1 (Or.inr rfl)) hu hw
    rw [hV _ d₁ rfl, isCovariantUnder_reflect_gamma d₁, vecAct_reflectMatrix_e₁,
      vecAct_reflectMatrix_e₁] at e
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, neg_mulVec, dotProduct_neg] at e
    rw [← comm 1 (Or.inr rfl) u w hu hw] at e
    rw [zero_mul]
    linear_combination -e / 2
  have hspat : ∀ (n : Fin 4 → ℝ), Minkowski.dot n n ≠ 0 → n 0 = 0 → ∀ ν : Fin 4,
      vecAct (reflectMatrix n) V 1 = V ν → SandwichEq m (restVec m) (V ν) 0 (gamma ν) := by
    intro n hn hn0 ν hν u w hu hw
    have e := sandwich_reflSpin hn0 h₁ hu hw
    rw [hV _ hn hn0, hν] at e
    rw [e, zero_mul, zero_mul]
  intro u w hu hw
  have hu0 := gamma_zero_mulVec_of_rest hm hu
  have hw0 := vecMul_gamma_zero_of_rest hm hw
  obtain rfl | rfl | rfl | rfl : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 := by fin_cases μ <;> simp
  · exact comm 0 (Or.inl rfl) u w hu hw
  · rw [h₁ u w hu hw, dotProduct_gamma_eq_zero hu0 hw0 (by decide)]
    simp
  · rw [hspat _ d₁₂ rfl 2 (vecAct_reflectMatrix_e₁₂ V) u w hu hw,
      dotProduct_gamma_eq_zero hu0 hw0 (by decide)]
    simp
  · rw [hspat _ d₁₃ rfl 3 (vecAct_reflectMatrix_e₁₃ V) u w hu hw,
      dotProduct_gamma_eq_zero hu0 hw0 (by decide)]
    simp

end QED.GradedProof.V5Zero.Dirac

end
