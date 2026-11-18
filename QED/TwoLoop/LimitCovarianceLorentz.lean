/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.SandwichReduction
public import QED.TwoLoop.ParametricBridge
public import QED.TwoLoop.CountertermInsertionAlgebra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Spinor lifts of Lorentz maps

Part of obligation O2-20 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). A **spinor lift** of a
real `4 × 4` matrix `L` is a pair `(S, T)` with `S T = 1` and `S γ^μ T = L^μ_ν γ^ν` for every
`μ` (the data quantified over in `QED.Dirac.IsLittleGroupCovariant`). This file derives what the
covariance arguments for the order-`e⁵` vertex need from such a pair:

* `T S = 1`, and the Clifford relation forces `L` to preserve the Minkowski form in both senses,
  `L g Lᵀ = g` and `Lᵀ g L = g` (`IsSpinLift.lorentz_left`, `IsSpinLift.lorentz_right`);
* `S (Lu)̸ T = u̸`, hence `S (m - (Lu)̸) T = m - u̸` (`IsSpinLift.mul_slash_mul`,
  `IsSpinLift.mul_electronNumerator_mul`), and `(Lu)·(Lv) = u·v` (`IsSpinLift.dot_mulVec`);
* **the vertex-chain rule** (`IsSpinLift.mul_chain_mul`): for a photon tensor `D` and matrices
  `A, B`, `S (∑ D_{νρ} γ^ρ A γ^μ B γ^ν) T = L^μ_κ ∑ D'_{νρ} γ^ρ (S A T) γ^κ (S B T) γ^ν` with
  `D'_{ν'ρ'} = ∑ D_{νρ} L^ν_{ν'} L^ρ_{ρ'}`.
-/

@[expose] public section

open Matrix Complex

namespace QED.TwoLoop.LimitCovariance

open QED.Dirac

section SumComm

variable {ι R : Type*} [Fintype ι] [AddCommMonoid R]

theorem sum3_rev (g : ι → ι → ι → R) :
    ∑ x, ∑ y, ∑ z, g x y z = ∑ z, ∑ y, ∑ x, g x y z := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun y _ => Finset.sum_comm]
  rw [Finset.sum_comm]

theorem sum4_swap (f : ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := Finset.sum_congr rfl fun a _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum_move3 (g : ι → ι → ι → ι → R) :
    ∑ a, ∑ c, ∑ d, ∑ e, g a c d e = ∑ c, ∑ d, ∑ e, ∑ a, g a c d e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_comm

theorem sum5_perm (f : ι → ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ d, ∑ e, ∑ c, ∑ a, ∑ b, f a b c d e := by
  calc _ = ∑ a, ∑ c, ∑ d, ∑ e, ∑ b, f a b c d e :=
        Finset.sum_congr rfl fun a _ => sum_move3 (fun b c d e => f a b c d e)
    _ = ∑ c, ∑ d, ∑ e, ∑ a, ∑ b, f a b c d e := sum_move3 (fun a c d e => ∑ b, f a b c d e)
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d _ => Finset.sum_comm

end SumComm

/-- `L` applied to each loop momentum. -/
def loopAct (L : Matrix (Fin 4) (Fin 4) ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  fun s => L *ᵥ ℓ s

/-- A spinor lift `(S, T)` of `L`: `S T = 1` and `S γ^μ T = L^μ_ν γ^ν`. -/
structure IsSpinLift (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ) : Prop where
  mul_eq_one : S * T = 1
  cov : IsCovariantUnder L S T gamma

namespace IsSpinLift

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem mul_eq_one' (h : IsSpinLift L S T) : T * S = 1 :=
  mul_eq_one_comm.mp h.mul_eq_one

theorem mul_mul_mul (h : IsSpinLift L S T) (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    S * (A * B) * T = (S * A * T) * (S * B * T) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc T S, h.mul_eq_one', Matrix.one_mul]

theorem mul_gamma_mul (h : IsSpinLift L S T) (μ : Fin 4) :
    S * gamma μ * T = ∑ ν, ((L μ ν : ℝ) : ℂ) • gamma ν :=
  h.cov μ

/-- The Minkowski form as a real matrix. -/
def metricM : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun μ ν => Minkowski.metric μ ν

theorem metricM_mul_self : metricM * metricM = 1 := by
  ext μ ρ
  simp only [Matrix.mul_apply, metricM, Matrix.of_apply, Minkowski.metric_mul_metric,
    Matrix.one_apply]

/-- **The Clifford relation forces `L g Lᵀ = g`.** -/
theorem lorentz_left (h : IsSpinLift L S T) (μ ν : Fin 4) :
    ∑ a, ∑ b, L μ a * L ν b * Minkowski.metric a b = Minkowski.metric μ ν := by
  have hC := gamma_anticomm μ ν
  have hS : S * (gamma μ * gamma ν + gamma ν * gamma μ) * T =
      ((-2 * Minkowski.metric μ ν : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    rw [hC, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h.mul_eq_one]
  rw [mul_add, add_mul, h.mul_mul_mul, h.mul_mul_mul, h.mul_gamma_mul, h.mul_gamma_mul] at hS
  have hexp : (∑ a, ((L μ a : ℝ) : ℂ) • gamma a) * (∑ b, ((L ν b : ℝ) : ℂ) • gamma b) +
      (∑ b, ((L ν b : ℝ) : ℂ) • gamma b) * (∑ a, ((L μ a : ℝ) : ℂ) • gamma a) =
      ∑ a, ∑ b, ((L μ a * L ν b : ℝ) : ℂ) • (gamma a * gamma b + gamma b * gamma a) := by
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [ofReal_mul]; congr 1; ring
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [ofReal_mul]
  rw [hexp] at hS
  simp only [gamma_anticomm, smul_smul, ← Finset.sum_smul] at hS
  have h00 := congrFun (congrFun hS 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  have h00' : ((∑ a, ∑ b, L μ a * L ν b * (-2 * Minkowski.metric a b) : ℝ) : ℂ) =
      ((-2 * Minkowski.metric μ ν : ℝ) : ℂ) := by
    rw [← h00]
    push_cast
    rfl
  have hr := Complex.ofReal_injective h00'
  have e : ∑ a, ∑ b, L μ a * L ν b * (-2 * Minkowski.metric a b) =
      -2 * ∑ a, ∑ b, L μ a * L ν b * Minkowski.metric a b := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  linarith

theorem mul_metricM_mul_transpose (h : IsSpinLift L S T) : L * metricM * Lᵀ = metricM := by
  ext μ ν
  rw [metricM, Matrix.of_apply, ← h.lorentz_left μ ν]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem transpose_mul_metricM_mul (h : IsSpinLift L S T) : Lᵀ * metricM * L = metricM := by
  have h1 : (metricM * L * metricM) * Lᵀ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc L, h.mul_metricM_mul_transpose,
      metricM_mul_self]
  have h2 : Lᵀ * (metricM * L * metricM) = 1 := mul_eq_one_comm.mp h1
  calc Lᵀ * metricM * L = Lᵀ * (metricM * L * metricM) * metricM := by
        simp only [Matrix.mul_assoc, metricM_mul_self, Matrix.mul_one]
    _ = metricM := by rw [h2, Matrix.one_mul]

/-- **`Lᵀ g L = g`.** -/
theorem lorentz_right (h : IsSpinLift L S T) (μ ν : Fin 4) :
    ∑ a, ∑ b, L a μ * L b ν * Minkowski.metric a b = Minkowski.metric μ ν := by
  have := congrFun (congrFun h.transpose_mul_metricM_mul μ) ν
  rw [metricM, Matrix.of_apply] at this
  rw [← this]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem lower_mulVec_contract (h : IsSpinLift L S T) (u : Fin 4 → ℝ) (ν : Fin 4) :
    ∑ μ, Minkowski.lower (L *ᵥ u) μ * L μ ν = Minkowski.lower u ν := by
  simp only [Minkowski.lower, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  have e : ∀ b, ∑ μ, ∑ a, Minkowski.metric μ a * (L a b * u b) * L μ ν =
      (∑ μ, ∑ a, L μ ν * L a b * Minkowski.metric μ a) * u b := fun b => by
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
  simp only [e, h.lorentz_right]

/-- **`S (Lu)̸ T = u̸`.** -/
theorem mul_slash_mul (h : IsSpinLift L S T) (u : Fin 4 → ℝ) :
    S * slash (L *ᵥ u) * T = slash u := by
  simp only [slash, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    h.mul_gamma_mul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_smul, ← h.lower_mulVec_contract u ν]
  push_cast
  rfl

theorem slash_mulVec (h : IsSpinLift L S T) (u : Fin 4 → ℝ) :
    slash (L *ᵥ u) = T * slash u * S := by
  rw [← h.mul_slash_mul u]
  simp only [← Matrix.mul_assoc]
  rw [h.mul_eq_one', Matrix.one_mul, Matrix.mul_assoc, h.mul_eq_one', Matrix.mul_one]

/-- **`S (m - (Lu)̸) T = m - u̸`.** -/
theorem mul_electronNumerator_mul (h : IsSpinLift L S T) (m : ℝ) (u : Fin 4 → ℝ) :
    S * Bridge.electronNumerator m (L *ᵥ u) * T = Bridge.electronNumerator m u := by
  simp only [Bridge.electronNumerator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, h.mul_eq_one, h.mul_slash_mul]

theorem dot_mulVec (h : IsSpinLift L S T) (u v : Fin 4 → ℝ) :
    Minkowski.dot (L *ᵥ u) (L *ᵥ v) = Minkowski.dot u v := by
  simp only [Minkowski.dot, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [sum4_swap]
  have e : ∀ c b, ∑ μ, ∑ ν, Minkowski.metric μ ν * (L μ b * u b) * (L ν c * v c) =
      Minkowski.metric b c * u b * v c := fun c b => by
    rw [← h.lorentz_right b c, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [e]
  exact Finset.sum_comm

/-! ### The vertex chain -/

/-- The chain `∑_{ν ρ} D_{νρ} γ^ρ A γ^μ B γ^ν`. -/
noncomputable def chain (D : Fin 4 → Fin 4 → ℂ) (A B : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ ν, ∑ ρ, D ν ρ • (gamma ρ * A * gamma μ * B * gamma ν)

/-- The transform `D'_{ν'ρ'} = ∑ D_{νρ} L^ν_{ν'} L^ρ_{ρ'}` of a photon tensor. -/
noncomputable def tensorAct (L : Matrix (Fin 4) (Fin 4) ℝ) (D : Fin 4 → Fin 4 → ℂ)
    (ν' ρ' : Fin 4) : ℂ :=
  ∑ ν, ∑ ρ, D ν ρ * ((L ν ν' : ℝ) : ℂ) * ((L ρ ρ' : ℝ) : ℂ)

theorem mul_five_mul (h : IsSpinLift L S T) (A₁ A₂ A₃ A₄ A₅ : Matrix (Fin 4) (Fin 4) ℂ) :
    S * (A₁ * A₂ * A₃ * A₄ * A₅) * T =
      (S * A₁ * T) * (S * A₂ * T) * (S * A₃ * T) * (S * A₄ * T) * (S * A₅ * T) := by
  rw [h.mul_mul_mul, h.mul_mul_mul, h.mul_mul_mul, h.mul_mul_mul]

theorem trilinear_expand (a b c : Fin 4 → ℂ) (X Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    (∑ ρ, a ρ • X ρ) * A * (∑ κ, b κ • Y κ) * B * (∑ ν, c ν • Z ν) =
      ∑ ρ, ∑ κ, ∑ ν, (a ρ * b κ * c ν) • (X ρ * A * Y κ * B * Z ν) := by
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [sum3_rev]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun κ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  ring

/-- **The vertex-chain rule.** -/
theorem mul_chain_mul (h : IsSpinLift L S T) (D : Fin 4 → Fin 4 → ℂ)
    (A B : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    S * chain D A B μ * T = vecAct L (chain (tensorAct L D) (S * A * T) (S * B * T)) μ := by
  simp only [chain, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    h.mul_five_mul]
  simp only [h.mul_gamma_mul, trilinear_expand, Finset.smul_sum, smul_smul]
  rw [sum5_perm]
  simp only [vecAct, chain, tensorAct, Finset.smul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun ν' _ =>
    Finset.sum_congr rfl fun ρ' _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  ring

end IsSpinLift

end QED.TwoLoop.LimitCovariance

end
