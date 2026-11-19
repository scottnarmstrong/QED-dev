/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Grad
public import QED.TwoLoop.LimitCovarianceQuartic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Stein identity for a numerator times an affine form

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A1. For a numerator `P` of degree at most three (`P.quart = 0`), an affine form
`c + l·ℓ`, a symmetric matrix `A` and `G l = Y` (`G = loopMetricInv A`):

* `gradEval_eq`, `dirDeriv_evalC`: the directional derivative `∇P(X)·D` is `∑ₐ gₐ(X) Dₐ` with
  the gradient `gvec`, and the value of `∂_Y P` at `X` is `∇P(X)·Y`;
* `evalC_sub_evalC`: the odd part `P(X + D) - P(X - D) = 2 (∇P(X)·D + K(D))`;
* `evalC_mulLin`: `(P·(c + l·ℓ))(X) = P(X) (c + l·X)`;
* `contractTwo_mulLin`: `∑ H[P·(c + l·ℓ)](X) G = (c + l·X) ∑ H[P](X) G + ∇P(X)·Y` (from the even
  part and polarization);
* `ehat_mulLin` (**Stein**): `Ê_{n+7}[P·(c + l·ℓ)] = (c + l·X) Ê_{n+7}[P] + ½ Ê_{n+6}[∂_Y P]`;
* `gradPart_eq`: the gradient part of `hasDerivAt_ehat_path` is `Ê_{n+6}[∂_Y P]`.
-/

@[expose] public section

open Complex
open scoped Matrix

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop

open Cubic

/-- The gradient `∂ₐP(X)` of a numerator of degree at most three. -/
def gvec (P : LoopQuartic) (X : LoopIndex → ℂ) (a : LoopIndex) : ℂ :=
  P.lin a + ∑ b, (P.quad a b + P.quad b a) * X b +
    ∑ b, ∑ e, (P.cub a b e + P.cub b a e + P.cub b e a) * (X b * X e)

/-- The cubic part `∑ K_abc Dₐ D_b D_c`. -/
def cubPart (P : LoopQuartic) (D : LoopIndex → ℂ) : ℂ :=
  ∑ a, ∑ b, ∑ c, P.cub a b c * (D a * D b * D c)

/-- The linear form `l·X`. -/
def linF (l X : LoopIndex → ℂ) : ℂ := ∑ a, l a * X a

section Moment

variable (P : LoopQuartic) (hq : P.quart = 0)
include hq

theorem gradEval_eq (X D : LoopIndex → ℂ) : gradEval P X D = ∑ a, gvec P X a * D a := by
  have q1 : ∑ a, ∑ b, P.quad a b * (X a * D b) = ∑ a, ∑ b, P.quad b a * X b * D a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have c2 : ∑ a, ∑ b, ∑ c, P.cub a b c * (X a * D b * X c) =
      ∑ a, ∑ b, ∑ e, P.cub b a e * (X b * X e) * D a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have c3 : ∑ a, ∑ b, ∑ c, P.cub a b c * (X a * X b * D c) =
      ∑ a, ∑ b, ∑ e, P.cub b e a * (X b * X e) * D a := by
    calc _ = ∑ a, ∑ c, ∑ b, P.cub a b c * (X a * X b * D c) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, P.cub a b c * (X a * X b * D c) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
  have hL : gradEval P X D = ∑ a, P.lin a * D a + (∑ a, ∑ b, P.quad a b * X b * D a +
      ∑ a, ∑ b, P.quad a b * (X a * D b)) + (∑ a, ∑ b, ∑ e, P.cub a b e * (X b * X e) * D a +
      ∑ a, ∑ b, ∑ c, P.cub a b c * (X a * D b * X c) +
      ∑ a, ∑ b, ∑ c, P.cub a b c * (X a * X b * D c)) := by
    simp only [gradEval, hq, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    congr 1
    · congr 1
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
    · simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
  rw [hL, q1, c2, c3]
  simp only [gvec, add_mul, Finset.sum_mul, Finset.sum_add_distrib]

omit hq in
theorem dirDeriv_evalC (X Y : LoopIndex → ℂ) :
    (dirDeriv P Y).evalC X = ∑ a, gvec P X a * Y a := by
  have h1 : ∑ b, (∑ a, (P.quad a b + P.quad b a) * Y a) * X b =
      ∑ a, ∑ b, (P.quad a b + P.quad b a) * X b * Y a := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ b, ∑ e, (∑ a, (P.cub a b e + P.cub b a e + P.cub b e a) * Y a) * (X b * X e) =
      ∑ a, ∑ b, ∑ e, (P.cub a b e + P.cub b a e + P.cub b e a) * (X b * X e) * Y a := by
    simp only [Finset.sum_mul]
    calc _ = ∑ b, ∑ a, ∑ e, (P.cub a b e + P.cub b a e + P.cub b e a) * Y a * (X b * X e) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
  have h3 : (dirDeriv P Y).evalC X = ∑ a, P.lin a * Y a +
      ∑ b, (∑ a, (P.quad a b + P.quad b a) * Y a) * X b +
      ∑ b, ∑ e, (∑ a, (P.cub a b e + P.cub b a e + P.cub b e a) * Y a) * (X b * X e) := by
    simp [LoopQuartic.evalC, dirDeriv]
  rw [h3, h1, h2]
  simp only [gvec, add_mul, Finset.sum_mul, Finset.sum_add_distrib]

theorem gradTwo_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (X Y : LoopIndex → ℂ) :
    gradTwo P A X Y = (dirDeriv P Y).contractTwo A X := by
  have hs : ∀ a b c d, P.quartSym a b c d = 0 := fun a b c d => by
    simp [LoopQuartic.quartSym, hq]
  simp only [gradTwo, hessGrad, hs, zero_mul, Finset.sum_const_zero, add_zero,
    LoopQuartic.contractTwo, hess_dirDeriv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => by ring

theorem contractFour_eq_zero (A : Matrix (Fin 2) (Fin 2) ℝ) : P.contractFour A = 0 := by
  simp [LoopQuartic.contractFour, hq]

omit hq in
theorem contractFour_dirDeriv (Y : LoopIndex → ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (dirDeriv P Y).contractFour A = 0 := by
  simp [LoopQuartic.contractFour, dirDeriv]

/-- **The odd part** of a numerator of degree at most three. -/
theorem evalC_sub_evalC (X D : LoopIndex → ℂ) :
    P.evalC (X + D) - P.evalC (X - D) = 2 * (gradEval P X D + cubPart P D) := by
  have s1 : ∑ a, P.lin a * (X + D) a - ∑ a, P.lin a * (X - D) a = 2 * ∑ a, P.lin a * D a := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring
  have s2 : ∑ a, ∑ b, P.quad a b * ((X + D) a * (X + D) b) -
      ∑ a, ∑ b, P.quad a b * ((X - D) a * (X - D) b) =
      2 * ∑ a, ∑ b, P.quad a b * (D a * X b + X a * D b) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring
  have s3 : ∑ a, ∑ b, ∑ c, P.cub a b c * ((X + D) a * (X + D) b * (X + D) c) -
      ∑ a, ∑ b, ∑ c, P.cub a b c * ((X - D) a * (X - D) b * (X - D) c) =
      2 * (∑ a, ∑ b, ∑ c, P.cub a b c * ((D a * X b + X a * D b) * X c + X a * X b * D c) +
        cubPart P D) := by
    rw [cubPart, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [LoopQuartic.evalC, gradEval, hq, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero]
  linear_combination s1 + s2 + s3

theorem evalC_mulLin (c : ℂ) (l X : LoopIndex → ℂ) :
    (mulLin P c l).evalC X = P.evalC X * (c + linF l X) := by
  have t1 : ∑ a, P.const * l a * X a = P.const * linF l X := by
    rw [linF, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have t2 : ∑ a, ∑ b, P.lin a * l b * (X a * X b) = (∑ a, P.lin a * X a) * linF l X := by
    rw [linF, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have t3 : ∑ a, ∑ b, ∑ e, P.quad a b * l e * (X a * X b * X e) =
      (∑ a, ∑ b, P.quad a b * (X a * X b)) * linF l X := by
    rw [linF]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have t4 : ∑ a, ∑ b, ∑ e, ∑ d, P.cub a b e * l d * (X a * X b * X e * X d) =
      (∑ a, ∑ b, ∑ e, P.cub a b e * (X a * X b * X e)) * linF l X := by
    rw [linF]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have u1 : ∑ a, P.lin a * c * X a = c * ∑ a, P.lin a * X a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have u2 : ∑ a, ∑ b, P.quad a b * c * (X a * X b) = c * ∑ a, ∑ b, P.quad a b * (X a * X b) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have u3 : ∑ a, ∑ b, ∑ e, P.cub a b e * c * (X a * X b * X e) =
      c * ∑ a, ∑ b, ∑ e, P.cub a b e * (X a * X b * X e) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  simp only [LoopQuartic.evalC, mulLin, hq, Pi.zero_apply, zero_mul, zero_add,
    Finset.sum_const_zero, add_zero, add_mul, Finset.sum_add_distrib]
  linear_combination t1 + t2 + t3 + t4 + u1 + u2 + u3

theorem quartPart_mulLin (c : ℂ) (l D : LoopIndex → ℂ) :
    (mulLin P c l).quartPart D = cubPart P D * linF l D := by
  simp only [LoopQuartic.quartPart, mulLin, hq, cubPart, linF, Pi.zero_apply, zero_mul,
    zero_add]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem quartPart_eq_zero (D : LoopIndex → ℂ) : P.quartPart D = 0 := by
  simp [LoopQuartic.quartPart, hq]

omit hq in
theorem linF_add (l X D : LoopIndex → ℂ) : linF l (X + D) = linF l X + linF l D := by
  simp only [linF, Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit hq in
theorem linF_sub (l X D : LoopIndex → ℂ) : linF l (X - D) = linF l X - linF l D := by
  simp only [linF, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The quadratic part of `P·(c + l·ℓ)` at `X`. -/
theorem hessForm_mulLin (c : ℂ) (l X D : LoopIndex → ℂ) :
    ∑ a, ∑ b, (mulLin P c l).hess X a b * (D a * D b) =
      (c + linF l X) * ∑ a, ∑ b, P.hess X a b * (D a * D b) + gradEval P X D * linF l D := by
  have eQ := (mulLin P c l).evalC_add_add_evalC_sub X D
  have eP := P.evalC_add_add_evalC_sub X D
  have eO := evalC_sub_evalC P hq X D
  rw [evalC_mulLin P hq, evalC_mulLin P hq, evalC_mulLin P hq, quartPart_mulLin P hq,
    linF_add, linF_sub] at eQ
  rw [quartPart_eq_zero P hq] at eP
  linear_combination (-1 / 2 : ℂ) * eQ + ((c + linF l X) / 2) * eP + (linF l D / 2) * eO

/-- **The second-moment contraction of `P·(c + l·ℓ)`**, for `A` symmetric and `G l = Y`. -/
theorem contractTwo_mulLin (c : ℂ) (l Y : LoopIndex → ℂ) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : Aᵀ = A) (hY : ∀ a, ∑ d, ((loopMetricInv A a d : ℝ) : ℂ) * l d = Y a)
    (X : LoopIndex → ℂ) :
    (mulLin P c l).contractTwo A X =
      (c + linF l X) * P.contractTwo A X + ∑ a, gvec P X a * Y a := by
  have hqf : ∀ D : LoopIndex → ℂ, ∑ a, ∑ b, (mulLin P c l).hess X a b * (D a * D b) =
      ∑ a, ∑ b, ((c + linF l X) * P.hess X a b + gvec P X a * l b) * (D a * D b) := by
    intro D
    rw [hessForm_mulLin P hq, gradEval_eq P hq]
    set k := c + linF l X
    rw [linF, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hpol := QED.TwoLoop.LimitCovariance.sum_mul_symm_eq_of_quadForm_eq _ _ hqf
    (fun a b => ((loopMetricInv A a b : ℝ) : ℂ))
    fun a b => by rw [QED.TwoLoop.LimitCovariance.loopMetricInv_symm hA]
  unfold LoopQuartic.contractTwo
  rw [hpol]
  set k := c + linF l X
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hY a, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Stein**: `Ê_{n+7}[P·(c + l·ℓ)] = (c + l·X) Ê_{n+7}[P] + ½ Ê_{n+6}[∂_Y P]` for `G l = Y`. -/
theorem ehat_mulLin (n : ℕ) (c : ℂ) (l Y : LoopIndex → ℂ) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : Aᵀ = A) (hY : ∀ a, ∑ d, ((loopMetricInv A a d : ℝ) : ℂ) * l d = Y a)
    (X : LoopIndex → ℂ) (W : ℂ) :
    ehat (n + 7) (mulLin P c l) A X W =
      (c + linF l X) * ehat (n + 7) P A X W + 1 / 2 * ehat (n + 6) (dirDeriv P Y) A X W := by
  simp only [ehat_add_six, evalC_mulLin P hq, contractTwo_mulLin P hq c l Y hA hY,
    contractFour_mulLin P hq c l Y A hY X, contractFour_eq_zero P hq,
    contractFour_dirDeriv, dirDeriv_evalC]
  simp only [show n + 1 + 2 = n + 3 by omega, show n + 1 + 3 = n + 4 by omega,
    show n + 1 + 1 = n + 2 by omega, Nat.factorial_succ (n + 2), Nat.factorial_succ (n + 1),
    Nat.factorial_succ n]
  push_cast
  ring

/-- The gradient part of `hasDerivAt_ehat_path` is the moment functional of `∂_Y P`. -/
theorem gradPart_eq (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (X Y : LoopIndex → ℂ) (W : ℂ) :
    ((n + 2).factorial : ℂ) * (W ^ (n + 3))⁻¹ * gradEval P X Y +
        ((n + 1).factorial : ℂ) / 2 * (W ^ (n + 2))⁻¹ * gradTwo P A X Y =
      ehat (n + 6) (dirDeriv P Y) A X W := by
  rw [ehat_add_six, gradEval_eq P hq, gradTwo_eq P hq, dirDeriv_evalC, contractFour_dirDeriv]
  ring

theorem ehat_dirDeriv_smul (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (X Y : LoopIndex → ℂ) (r : ℂ)
    (W : ℂ) :
    ehat (n + 6) (dirDeriv P fun a => r * Y a) A X W = r * ehat (n + 6) (dirDeriv P Y) A X W := by
  have h1 : gradEval P X (fun a => r * Y a) = r * gradEval P X Y := by
    rw [gradEval_eq P hq, gradEval_eq P hq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : gradTwo P A X (fun a => r * Y a) = r * gradTwo P A X Y := by
    rw [gradTwo_eq P hq, gradTwo_eq P hq]
    simp only [LoopQuartic.contractTwo, hess_dirDeriv, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  rw [← gradPart_eq P hq, ← gradPart_eq P hq, h1, h2]
  ring

end Moment

end QED.GradedProof.WI2

end
