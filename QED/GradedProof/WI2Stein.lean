/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Gauss
import Mathlib.Tactic.Ring

/-!
# Products with a linear form and directional derivatives of cubic numerators

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A1. For a numerator `P` of degree at most three (`P.quart = 0`):

* `LoopQuartic.mulLin P c l`: the quartic `P(ℓ) (c + ∑ₐ lₐ ℓₐ)`;
* `LoopQuartic.dirDeriv P Y`: the quadratic `∑ₐ Yₐ ∂ₐ P`.

The Stein-type identity behind the parametric derivative identity: integrating
`P(ℓ) l·(ℓ - X)` against `w^{-(n+1)}` is integrating `½ ∂_Y P` against `w^{-n}`, where `G l = Y`.
This file proves its fourth-moment part (`contractFour_mulLin`):
`∑ R[P·l] Π(G) = ∑ H[∂_Y P] G`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop

namespace Cubic

/-- The product `P(ℓ) (c + ∑ₐ lₐ ℓₐ)` of a numerator of degree at most three with an affine form
(the quintic part, which vanishes for `P.quart = 0`, is dropped). -/
def mulLin (P : LoopQuartic) (c : ℂ) (l : LoopIndex → ℂ) : LoopQuartic where
  const := P.const * c
  lin a := P.lin a * c + P.const * l a
  quad a b := P.quad a b * c + P.lin a * l b
  cub a b e := P.cub a b e * c + P.quad a b * l e
  quart a b e d := P.quart a b e d * c + P.cub a b e * l d

/-- The directional derivative `∑ₐ Yₐ ∂ₐ P` of a numerator of degree at most three. -/
def dirDeriv (P : LoopQuartic) (Y : LoopIndex → ℂ) : LoopQuartic where
  const := ∑ a, P.lin a * Y a
  lin b := ∑ a, (P.quad a b + P.quad b a) * Y a
  quad b e := ∑ a, (P.cub a b e + P.cub b a e + P.cub b e a) * Y a
  cub _ _ _ := 0
  quart _ _ _ _ := 0

theorem hess_dirDeriv (P : LoopQuartic) (Y X : LoopIndex → ℂ) (b e : LoopIndex) :
    (dirDeriv P Y).hess X b e = ∑ a, (P.cub a b e + P.cub b a e + P.cub b e a) * Y a := by
  simp [LoopQuartic.hess, LoopQuartic.quartSym, dirDeriv]

/-- **Stein, fourth moment**: for `P.quart = 0` and `G l = Y` (`G = loopMetricInv A`),
`∑ R[P·l] Π(G) = ∑ H[∂_Y P] G`. -/
theorem contractFour_mulLin (P : LoopQuartic) (hq : P.quart = 0) (c : ℂ) (l Y : LoopIndex → ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hY : ∀ a, ∑ d, ((loopMetricInv A a d : ℝ) : ℂ) * l d = Y a) (X : LoopIndex → ℂ) :
    (mulLin P c l).contractFour A = (dirDeriv P Y).contractTwo A X := by
  set G : LoopIndex → LoopIndex → ℂ := fun a b => ((loopMetricInv A a b : ℝ) : ℂ) with hG
  have hL : (mulLin P c l).contractFour A =
      ∑ a, ∑ b, ∑ e, P.cub a b e * (G a b * Y e + G a e * Y b + Y a * G b e) := by
    simp only [LoopQuartic.contractFour, mulLin, hq, Pi.zero_apply, zero_mul, zero_add,
      matPair]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => ?_
    rw [← hY e, ← hY b, ← hY a]
    simp only [hG, mul_add, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    ring
  have hR : (dirDeriv P Y).contractTwo A X =
      ∑ b, ∑ e, ∑ a, (P.cub a b e + P.cub b a e + P.cub b e a) * Y a * G b e := by
    simp only [LoopQuartic.contractTwo, hess_dirDeriv, Finset.sum_mul, hG]
  rw [hL, hR]
  -- reindex the three terms of the right side to the form of the left side
  have t1 : ∑ b, ∑ e, ∑ a, P.cub a b e * Y a * G b e =
      ∑ a, ∑ b, ∑ e, P.cub a b e * (Y a * G b e) := by
    calc _ = ∑ b, ∑ a, ∑ e, P.cub a b e * Y a * G b e :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ e, P.cub a b e * Y a * G b e := Finset.sum_comm
      _ = _ := by simp only [mul_assoc]
  have t2 : ∑ b, ∑ e, ∑ a, P.cub b a e * Y a * G b e =
      ∑ a, ∑ b, ∑ e, P.cub a b e * (G a e * Y b) := by
    calc _ = ∑ b, ∑ a, ∑ e, P.cub b a e * Y a * G b e :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun e _ => by ring
  have t3 : ∑ b, ∑ e, ∑ a, P.cub b e a * Y a * G b e =
      ∑ a, ∑ b, ∑ e, P.cub a b e * (G a b * Y e) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => ?_
    ring
  have split : ∑ b, ∑ e, ∑ a, (P.cub a b e + P.cub b a e + P.cub b e a) * Y a * G b e =
      ∑ b, ∑ e, ∑ a, P.cub a b e * Y a * G b e + ∑ b, ∑ e, ∑ a, P.cub b a e * Y a * G b e +
        ∑ b, ∑ e, ∑ a, P.cub b e a * Y a * G b e := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [split, t1, t2, t3]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end Cubic

end QED.GradedProof.WI2

end
