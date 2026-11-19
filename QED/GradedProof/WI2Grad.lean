/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Stein
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring

/-!
# Derivatives of the moment functional along a path

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A1. Along a path `s ↦ (P s, X s, W s)` of numerators (coefficientwise differentiable,
`HasQDerivAt`), shifts and denominators, the moment functional `Ê_{n+6}` of `WI2Gauss` has the
derivative (`hasDerivAt_ehat_path`)

`Ê_{n+6}[P'] + (n+2)! W^{-(n+3)} ∇P(X)·Y + (n+1)!/2 W^{-(n+2)} ∑ (∇_Y H)(X) G - W' Ê_{n+7}[P]`,

with `Y = X'` and the directional derivatives `gradEval`, `gradTwo` of the value and of the
second-moment contraction (the fourth-moment contraction does not depend on `X`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop

/-- Coefficientwise derivative of a path of numerators. -/
def HasQDerivAt (P : ℝ → LoopQuartic) (P' : LoopQuartic) (t : ℝ) : Prop :=
  HasDerivAt (fun s => (P s).const) P'.const t ∧
    (∀ a, HasDerivAt (fun s => (P s).lin a) (P'.lin a) t) ∧
    (∀ a b, HasDerivAt (fun s => (P s).quad a b) (P'.quad a b) t) ∧
    (∀ a b c, HasDerivAt (fun s => (P s).cub a b c) (P'.cub a b c) t) ∧
    (∀ a b c d, HasDerivAt (fun s => (P s).quart a b c d) (P'.quart a b c d) t)

/-- The directional derivative `∇P(X)·Y` of the value of a numerator. -/
def gradEval (P : LoopQuartic) (X Y : LoopIndex → ℂ) : ℂ :=
  ∑ a, P.lin a * Y a + ∑ a, ∑ b, P.quad a b * (Y a * X b + X a * Y b) +
    ∑ a, ∑ b, ∑ c, P.cub a b c * ((Y a * X b + X a * Y b) * X c + X a * X b * Y c) +
    ∑ a, ∑ b, ∑ c, ∑ d, P.quart a b c d *
      (((Y a * X b + X a * Y b) * X c + X a * X b * Y c) * X d + X a * X b * X c * Y d)

/-- The directional derivative of the coefficients `H(X)` of the quadratic part. -/
def hessGrad (P : LoopQuartic) (X Y : LoopIndex → ℂ) (a b : LoopIndex) : ℂ :=
  ∑ c, (P.cub a b c + P.cub a c b + P.cub c a b) * Y c +
    ∑ c, ∑ d, P.quartSym a b c d * (Y c * X d + X c * Y d)

/-- The directional derivative of the second-moment contraction `∑ H(X) G`. -/
noncomputable def gradTwo (P : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X Y : LoopIndex → ℂ) : ℂ :=
  ∑ a, ∑ b, hessGrad P X Y a b * (loopMetricInv A a b : ℂ)

section Path

variable {P : ℝ → LoopQuartic} {P' : LoopQuartic} {t : ℝ} {X : ℝ → LoopIndex → ℂ}
  {Y : LoopIndex → ℂ}

theorem HasQDerivAt.quartSym (hP : HasQDerivAt P P' t) (a b c d : LoopIndex) :
    HasDerivAt (fun s => (P s).quartSym a b c d) (P'.quartSym a b c d) t := by
  have h := hP.2.2.2.2
  exact (((((h a b c d).add (h a c b d)).add (h a c d b)).add (h c a b d)).add
    (h c a d b)).add (h c d a b)

theorem hasDerivAt_evalC (hP : HasQDerivAt P P' t)
    (hX : ∀ a, HasDerivAt (fun s => X s a) (Y a) t) :
    HasDerivAt (fun s => (P s).evalC (X s)) (P'.evalC (X t) + gradEval (P t) (X t) Y) t := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hP
  have d1 := HasDerivAt.fun_sum (u := Finset.univ) fun a _ => (h1 a).mul (hX a)
  have d2 := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun b _ => (h2 a b).mul ((hX a).mul (hX b))
  have d3 := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun b _ => HasDerivAt.fun_sum (u := Finset.univ)
      fun c _ => (h3 a b c).mul (((hX a).mul (hX b)).mul (hX c))
  have d4 := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun b _ => HasDerivAt.fun_sum (u := Finset.univ)
      fun c _ => HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
        (h4 a b c d).mul ((((hX a).mul (hX b)).mul (hX c)).mul (hX d))
  have h := (((h0.add d1).add d2).add d3).add d4
  convert h using 1
  · funext s
    simp only [LoopQuartic.evalC, Pi.add_apply, Pi.mul_apply]
  · simp only [LoopQuartic.evalC, gradEval, Finset.sum_add_distrib, Pi.mul_apply]
    ring

theorem hasDerivAt_hess (hP : HasQDerivAt P P' t)
    (hX : ∀ a, HasDerivAt (fun s => X s a) (Y a) t) (a b : LoopIndex) :
    HasDerivAt (fun s => (P s).hess (X s) a b)
      (P'.hess (X t) a b + hessGrad (P t) (X t) Y a b) t := by
  have h2 := hP.2.2.1
  have h3 := hP.2.2.2.1
  have d1 := HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
    (((h3 a b c).add (h3 a c b)).add (h3 c a b)).mul (hX c)
  have d2 := HasDerivAt.fun_sum (u := Finset.univ) fun c _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
      (hP.quartSym a b c d).mul ((hX c).mul (hX d))
  have h := ((h2 a b).add d1).add d2
  convert h using 1
  · funext s
    simp only [LoopQuartic.hess, Pi.add_apply, Pi.mul_apply]
  · simp only [LoopQuartic.hess, hessGrad, Finset.sum_add_distrib, add_mul, mul_add,
      Pi.mul_apply, Pi.add_apply]
    ring

theorem hasDerivAt_contractTwo (hP : HasQDerivAt P P' t)
    (hX : ∀ a, HasDerivAt (fun s => X s a) (Y a) t) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun s => (P s).contractTwo A (X s))
      (P'.contractTwo A (X t) + gradTwo (P t) A (X t) Y) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
      (hasDerivAt_hess hP hX a b).mul_const ((loopMetricInv A a b : ℝ) : ℂ)
  convert h using 1
  · funext s
    simp only [LoopQuartic.contractTwo]
  · simp only [LoopQuartic.contractTwo, gradTwo, add_mul, Finset.sum_add_distrib]

theorem hasDerivAt_contractFour (hP : HasQDerivAt P P' t) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun s => (P s).contractFour A) (P'.contractFour A) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun b _ => HasDerivAt.fun_sum (u := Finset.univ)
      fun c _ => HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
        (hP.2.2.2.2 a b c d).mul_const ((matPair (loopMetricInv A) a b c d : ℝ) : ℂ)
  exact h

end Path

/-- `Ê_{n+6}` with the factorials and powers written out. -/
theorem ehat_add_six (n : ℕ) (P : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) (W : ℂ) :
    ehat (n + 6) P A X W =
      ((n + 2).factorial : ℂ) * (W ^ (n + 3))⁻¹ * P.evalC X +
        ((n + 1).factorial : ℂ) / 2 * (W ^ (n + 2))⁻¹ * P.contractTwo A X +
        (n.factorial : ℂ) / 4 * (W ^ (n + 1))⁻¹ * P.contractFour A := by
  simp only [ehat, show n + 6 - 4 = n + 2 by omega, show n + 6 - 3 = n + 3 by omega,
    show n + 6 - 5 = n + 1 by omega, show n + 6 - 6 = n by omega]

theorem hasDerivAt_inv_pow_comp {k : ℕ} {W : ℝ → ℂ} {W' : ℂ} {t : ℝ} (hW : HasDerivAt W W' t)
    (h0 : W t ≠ 0) :
    HasDerivAt (fun s => (W s ^ k)⁻¹) (-((k : ℂ) * (W t ^ (k + 1))⁻¹) * W') t :=
  (hasDerivAt_inv_pow (k := k) h0).comp t hW

/-- **The derivative of the moment functional along a path.** -/
theorem hasDerivAt_ehat_path (n : ℕ) {P : ℝ → LoopQuartic} {P' : LoopQuartic} {t : ℝ}
    (hP : HasQDerivAt P P' t) (A : Matrix (Fin 2) (Fin 2) ℝ) {X : ℝ → LoopIndex → ℂ}
    {Y : LoopIndex → ℂ} (hX : ∀ a, HasDerivAt (fun s => X s a) (Y a) t) {W : ℝ → ℂ} {W' : ℂ}
    (hW : HasDerivAt W W' t) (h0 : W t ≠ 0) :
    HasDerivAt (fun s => ehat (n + 6) (P s) A (X s) (W s))
      (ehat (n + 6) P' A (X t) (W t) +
        (((n + 2).factorial : ℂ) * (W t ^ (n + 3))⁻¹ * gradEval (P t) (X t) Y +
          ((n + 1).factorial : ℂ) / 2 * (W t ^ (n + 2))⁻¹ * gradTwo (P t) A (X t) Y) -
        W' * ehat (n + 7) (P t) A (X t) (W t)) t := by
  simp only [ehat_add_six]
  have h := ((((hasDerivAt_inv_pow_comp (k := n + 3) hW h0).const_mul
      ((n + 2).factorial : ℂ)).mul (hasDerivAt_evalC hP hX)).add
    (((hasDerivAt_inv_pow_comp (k := n + 2) hW h0).const_mul
      (((n + 1).factorial : ℂ) / 2)).mul (hasDerivAt_contractTwo hP hX A))).add
    (((hasDerivAt_inv_pow_comp (k := n + 1) hW h0).const_mul
      ((n.factorial : ℂ) / 4)).mul (hasDerivAt_contractFour hP A))
  convert h using 1
  simp only [show n + 1 + 2 = n + 3 by omega, show n + 1 + 3 = n + 4 by omega,
    show n + 1 + 1 = n + 2 by omega, Nat.factorial_succ (n + 2), Nat.factorial_succ (n + 1),
    Nat.factorial_succ n]
  push_cast
  ring

end QED.GradedProof.WI2

end
