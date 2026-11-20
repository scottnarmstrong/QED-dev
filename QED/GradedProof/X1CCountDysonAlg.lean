/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum

/-!
# (X₁) piece C: unwinding the three peels at order `5` (algebra)

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (assembly). Pure algebra in `4 × 4` complex matrices, with no
reference to contractions.

**`countDyson_unwind`**: let `G H J V : ℕ → Fin 4 → Matrix` (order, external photon index),
`X Y : ℕ → Matrix` (the in- and out-leg insertions, `S̃ Σ` and `Σ S̃`) and
`Q : ℕ → Fin 4 → Fin 4 → ℂ` (the photon-leg insertion `Δ̃ Π`), with `X K = Y K = Q K = 0` for
`K ∈ {0, 1, 3, 5}`. If at the odd orders `K ∈ {1, 3, 5}`

`G_K = H_K + ∑_{K₁+K₂=K} G_{K₁} X_{K₂}`, `H_K = J_K + ∑ Y_{K₂} H_{K₁}`,
`J_K(μ) = V_K(μ) + ∑ ∑_ν Q_{K₂}(ν, μ) • J_{K₁}(ν)`,

then `G_5(μ)` is the sum over `a + b + c + d = 2` (each `< 3`) and `ν` of
`Qleg_d(ν, μ) • (Yleg_a · V_{2b+1}(ν) · Xleg_c)`, with the chains `countDysonLeg` (`1`, `X₂`,
`X₄ + X₂ X₂`) and `countDysonPLeg` (`δ`, `Q₂`, `Q₄ + Q₂ Q₂`): the shape of `dysonFive`. The
even orders never enter.

`countDysonAct R W μ = ∑_ν R(ν, μ) • W(ν)` and its lemmas organize the photon sums.
-/

@[expose] public section

open Finset

namespace QED.GradedProof.X1C

/-- The photon kernel `R` acting on a family of matrices indexed by the vertex index. -/
def countDysonAct (R : Fin 4 → Fin 4 → ℂ) (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ ν, R ν μ • W ν

/-- The fermion-leg chain of order `2n` built from the pieces `X 2`, `X 4`. -/
def countDysonLeg (X : ℕ → Matrix (Fin 4) (Fin 4) ℂ) : ℕ → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => 1
  | 1 => X 2
  | 2 => X 4 + X 2 * X 2
  | _ => 0

/-- The photon-leg chain of order `2n` built from the pieces `Q 2`, `Q 4`. -/
def countDysonPLeg (Q : ℕ → Fin 4 → Fin 4 → ℂ) : ℕ → Fin 4 → Fin 4 → ℂ
  | 0 => fun ν μ => if ν = μ then 1 else 0
  | 1 => Q 2
  | 2 => fun ν μ => Q 4 ν μ + ∑ l, Q 2 ν l * Q 2 l μ
  | _ => fun _ _ => 0

section Act

variable (R R' : Fin 4 → Fin 4 → ℂ) (W W' : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4)
  (A : Matrix (Fin 4) (Fin 4) ℂ)

theorem countDysonAct_delta : countDysonAct (fun ν μ => if ν = μ then 1 else 0) W μ = W μ := by
  simp [countDysonAct, ite_smul]

theorem countDysonAct_add_left : countDysonAct (fun ν μ => R ν μ + R' ν μ) W μ =
    countDysonAct R W μ + countDysonAct R' W μ := by
  simp [countDysonAct, add_smul, sum_add_distrib]

theorem countDysonAct_add_right : countDysonAct R (fun ν => W ν + W' ν) μ =
    countDysonAct R W μ + countDysonAct R W' μ := by
  simp [countDysonAct, smul_add, sum_add_distrib]

theorem countDysonAct_comp : countDysonAct (fun ν μ => ∑ l, R ν l * R' l μ) W μ =
    countDysonAct R' (fun l => countDysonAct R W l) μ := by
  simp only [countDysonAct, sum_smul, smul_sum, smul_smul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by rw [mul_comm]

theorem mul_countDysonAct : A * countDysonAct R W μ = countDysonAct R (fun ν => A * W ν) μ := by
  simp [countDysonAct, mul_sum, mul_smul_comm]

theorem countDysonAct_mul : countDysonAct R W μ * A = countDysonAct R (fun ν => W ν * A) μ := by
  simp [countDysonAct, sum_mul, smul_mul_assoc]

end Act

theorem countDyson_sum_antidiagonal_five {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) :
    ∑ p ∈ antidiagonal 5, f p =
      f (0, 5) + f (1, 4) + f (2, 3) + f (3, 2) + f (4, 1) + f (5, 0) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sum_range_succ]

theorem countDyson_sum_antidiagonal_three {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) :
    ∑ p ∈ antidiagonal 3, f p = f (0, 3) + f (1, 2) + f (2, 1) + f (3, 0) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sum_range_succ]

theorem countDyson_sum_antidiagonal_one {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) :
    ∑ p ∈ antidiagonal 1, f p = f (0, 1) + f (1, 0) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sum_range_succ]

/-- **Unwinding the three peels at order `5`.** -/
theorem countDyson_unwind (G H J V : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (X Y : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (Q : ℕ → Fin 4 → Fin 4 → ℂ)
    (hX : ∀ K ≤ 5, K ≠ 2 → K ≠ 4 → X K = 0) (hY : ∀ K ≤ 5, K ≠ 2 → K ≠ 4 → Y K = 0)
    (hQ : ∀ K ≤ 5, K ≠ 2 → K ≠ 4 → Q K = 0)
    (hG : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ μ,
      G K μ = H K μ + ∑ p ∈ antidiagonal K, G p.1 μ * X p.2)
    (hH : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ μ,
      H K μ = J K μ + ∑ p ∈ antidiagonal K, Y p.2 * H p.1 μ)
    (hJ : ∀ K ∈ ({1, 3, 5} : Finset ℕ), ∀ μ,
      J K μ = V K μ + ∑ p ∈ antidiagonal K, ∑ ν, Q p.2 ν μ • J p.1 ν) (μ : Fin 4) :
    G 5 μ = ∑ a ∈ range 3, ∑ b ∈ range 3, ∑ c ∈ range 3, ∑ d ∈ range 3,
      if a + b + c + d = 2 then
        ∑ ν, countDysonPLeg Q d ν μ •
          (countDysonLeg Y a * V (2 * b + 1) ν * countDysonLeg X c)
      else 0 := by
  have X0 := hX 0 (by norm_num) (by norm_num) (by norm_num)
  have X1 := hX 1 (by norm_num) (by norm_num) (by norm_num)
  have X3 := hX 3 (by norm_num) (by norm_num) (by norm_num)
  have X5 := hX 5 (by norm_num) (by norm_num) (by norm_num)
  have Y0 := hY 0 (by norm_num) (by norm_num) (by norm_num)
  have Y1 := hY 1 (by norm_num) (by norm_num) (by norm_num)
  have Y3 := hY 3 (by norm_num) (by norm_num) (by norm_num)
  have Y5 := hY 5 (by norm_num) (by norm_num) (by norm_num)
  have Q0 := hQ 0 (by norm_num) (by norm_num) (by norm_num)
  have Q1 := hQ 1 (by norm_num) (by norm_num) (by norm_num)
  have Q3 := hQ 3 (by norm_num) (by norm_num) (by norm_num)
  have Q5 := hQ 5 (by norm_num) (by norm_num) (by norm_num)
  have J1 : ∀ μ, J 1 μ = V 1 μ := fun μ => by
    rw [hJ 1 (by simp) μ, countDyson_sum_antidiagonal_one]
    simp [Q0, Q1]
  have J3 : ∀ μ, J 3 μ = V 3 μ + countDysonAct (Q 2) (V 1) μ := fun μ => by
    rw [hJ 3 (by simp) μ, countDyson_sum_antidiagonal_three]
    simp [Q0, Q1, Q3, J1, countDysonAct]
  have J5 : J 5 μ = V 5 μ + countDysonAct (Q 2) (V 3) μ +
      countDysonAct (Q 2) (fun l => countDysonAct (Q 2) (V 1) l) μ +
      countDysonAct (Q 4) (V 1) μ := by
    rw [hJ 5 (by simp) μ, countDyson_sum_antidiagonal_five]
    have : ∑ ν, Q 2 ν μ • J 3 ν = countDysonAct (Q 2) (V 3) μ +
        countDysonAct (Q 2) (fun l => countDysonAct (Q 2) (V 1) l) μ := by
      rw [← countDysonAct_add_right]
      exact sum_congr rfl fun ν _ => by rw [J3]
    simp only [Q0, Q1, Q3, Q5, Pi.zero_apply, zero_smul, sum_const_zero, add_zero, zero_add,
      this, J1]
    simp only [countDysonAct]
    abel
  have H1 : ∀ μ, H 1 μ = J 1 μ := fun μ => by
    rw [hH 1 (by simp) μ, countDyson_sum_antidiagonal_one]
    simp [Y0, Y1]
  have H3 : ∀ μ, H 3 μ = J 3 μ + Y 2 * J 1 μ := fun μ => by
    rw [hH 3 (by simp) μ, countDyson_sum_antidiagonal_three]
    simp [Y0, Y1, Y3, H1]
  have H5 : H 5 μ = J 5 μ + Y 2 * H 3 μ + Y 4 * H 1 μ := by
    rw [hH 5 (by simp) μ, countDyson_sum_antidiagonal_five]
    simp [Y0, Y1, Y3, Y5]
    abel
  have G1 : G 1 μ = H 1 μ := by
    rw [hG 1 (by simp) μ, countDyson_sum_antidiagonal_one]
    simp [X0, X1]
  have G3 : G 3 μ = H 3 μ + G 1 μ * X 2 := by
    rw [hG 3 (by simp) μ, countDyson_sum_antidiagonal_three]
    simp [X0, X1, X3]
  have G5 : G 5 μ = H 5 μ + G 3 μ * X 2 + G 1 μ * X 4 := by
    rw [hG 5 (by simp) μ, countDyson_sum_antidiagonal_five]
    simp [X0, X1, X3, X5]
    abel
  show _ = ∑ a ∈ range 3, ∑ b ∈ range 3, ∑ c ∈ range 3, ∑ d ∈ range 3,
      if a + b + c + d = 2 then countDysonAct (countDysonPLeg Q d)
        (fun ν => countDysonLeg Y a * V (2 * b + 1) ν * countDysonLeg X c) μ else 0
  simp only [G5, G3, G1, H5, H3, H1, J5, J3, J1]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  norm_num [countDysonLeg, countDysonPLeg, countDysonAct_delta, countDysonAct_add_left,
    countDysonAct_comp, mul_countDysonAct, countDysonAct_mul, mul_add, add_mul, mul_assoc]
  abel
end QED.GradedProof.X1C

end
