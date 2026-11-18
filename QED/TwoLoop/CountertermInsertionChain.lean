/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Index sums of an open fermion chain

Finite-sum lemmas for the explicit evaluation of the amplitude (T₇) of the one-loop
counterterm classes (obligation O2-13, `docs/TWO-LOOP-DERIVATION.md`, section 5.1). The
amplitude sums over the spinor indices `α, β` of the fermion fields and the Lorentz indices of
the photon fields of all vertices. For an open fermion line through `n` vertices `x₁, …, xₙ`
(the outgoing vertex first), with the outer indices fixed, the spinor sum is the entry of the
matrix product `A₁ S₁ A₂ ⋯ Sₙ₋₁ Aₙ`.

* `QED.TwoLoop.Insertion.sum_pi_three`, `sum_pi_four`, `sum_pi_five`: a sum over the functions
  on a type covered by `3`, `4`, `5` distinct elements is an iterated sum over their values.
* `QED.TwoLoop.Insertion.sum_spinor_chain3`, `sum_spinor_chain4`: the spinor sums of an open
  chain through three and four vertices.

These are statements about finite sums only.
-/

@[expose] public section

namespace QED.TwoLoop.Insertion

open Finset

/-! ### Sums over functions on a small finite type -/

section Pi

variable {X R M : Type*} [Fintype X] [DecidableEq X] [Fintype R] [AddCommMonoid M]

/-- A sum over the functions on a type covered by three distinct elements. -/
theorem sum_pi_three {x₁ x₂ x₃ : X} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃) (g : (X → R) → M) :
    ∑ f, g f = ∑ a, ∑ b, ∑ c,
      g (fun t => if t = x₁ then a else if t = x₂ then b else c) := by
  let e : (X → R) ≃ R × R × R :=
    { toFun := fun f => (f x₁, f x₂, f x₃)
      invFun := fun q t => if t = x₁ then q.1 else if t = x₂ then q.2.1 else q.2.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl | rfl <;> simp [h12.symm, h13.symm, h23.symm]
      right_inv := fun q => by simp [h12.symm, h13.symm, h23.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

/-- A sum over the functions on a type covered by four distinct elements. -/
theorem sum_pi_four {x₁ x₂ x₃ x₄ : X} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄)
    (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x = x₄) (g : (X → R) → M) :
    ∑ f, g f = ∑ a, ∑ b, ∑ c, ∑ d,
      g (fun t => if t = x₁ then a else if t = x₂ then b else if t = x₃ then c else d) := by
  let e : (X → R) ≃ R × R × R × R :=
    { toFun := fun f => (f x₁, f x₂, f x₃, f x₄)
      invFun := fun q t =>
        if t = x₁ then q.1 else if t = x₂ then q.2.1 else if t = x₃ then q.2.2.1 else q.2.2.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl | rfl | rfl <;>
          simp [h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm]
      right_inv := fun q => by simp [h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

/-- A sum over the functions on a type covered by five distinct elements. -/
theorem sum_pi_five {x₁ x₂ x₃ x₄ x₅ : X} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄)
    (h15 : x₁ ≠ x₅) (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h25 : x₂ ≠ x₅) (h34 : x₃ ≠ x₄)
    (h35 : x₃ ≠ x₅) (h45 : x₄ ≠ x₅)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x = x₄ ∨ x = x₅) (g : (X → R) → M) :
    ∑ f, g f = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      g (fun t => if t = x₁ then a else if t = x₂ then b else if t = x₃ then c else
        if t = x₄ then d else e) := by
  let E : (X → R) ≃ R × R × R × R × R :=
    { toFun := fun f => (f x₁, f x₂, f x₃, f x₄, f x₅)
      invFun := fun q t =>
        if t = x₁ then q.1 else if t = x₂ then q.2.1 else if t = x₃ then q.2.2.1 else
          if t = x₄ then q.2.2.2.1 else q.2.2.2.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl | rfl | rfl | rfl <;>
          simp [h12.symm, h13.symm, h14.symm, h15.symm, h23.symm, h24.symm, h25.symm, h34.symm,
            h35.symm, h45.symm]
      right_inv := fun q => by
        simp [h12.symm, h13.symm, h14.symm, h15.symm, h23.symm, h24.symm, h25.symm, h34.symm,
          h35.symm, h45.symm] }
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

end Pi

/-! ### Spinor sums of an open chain -/

/-- The entry of a product of five matrices as an iterated sum over the internal indices. -/
theorem mul_apply_five (A B D E G : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (A * B * D * E * G) i j =
      ∑ w, ∑ z, ∑ y, ∑ x, A i x * B x y * D y z * E z w * G w j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]

/-- The entry of a product of seven matrices as an iterated sum over the internal indices. -/
theorem mul_apply_seven (A B D E G H K : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (A * B * D * E * G * H * K) i j =
      ∑ v, ∑ u, ∑ w, ∑ z, ∑ y, ∑ x,
        A i x * B x y * D y z * E z w * G w u * H u v * K v j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]

section Chain

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The spinor sum of an open chain through three vertices** `x₁, x₂, x₃` (outgoing vertex
first): with `α x₁` and `β x₃` fixed, the sum of `c · A₁ S₁ A₂ S₂ A₃` over the spinor indices is
`c` times the entry of the matrix product. -/
theorem sum_spinor_chain3 {x₁ x₂ x₃ : X} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃) (c : ℂ) (A₁ A₂ A₃ S₁ S₂ : Matrix (Fin 4) (Fin 4) ℂ)
    (a b : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      (if α x₁ = a ∧ β x₃ = b then (1 : ℂ) else 0) *
        (c * (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃))) =
      c * (A₁ * S₁ * A₂ * S₂ * A₃) a b := by
  have hs := fun (g : (X → Fin 4) → ℂ) => sum_pi_three h12 h13 h23 hX g
  simp only [hs, h12.symm, h13.symm, h23.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_apply_five]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, w, 2, y]; rw [Finset.sum_comm]
  conv_lhs => enter [2, w]; rw [Finset.sum_comm]


/-- **The spinor sum of an open chain through four vertices** `x₁, …, x₄` (outgoing vertex
first). -/
theorem sum_spinor_chain4 {x₁ x₂ x₃ x₄ : X} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄)
    (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x = x₄) (c : ℂ)
    (A₁ A₂ A₃ A₄ S₁ S₂ S₃ : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      (if α x₁ = a ∧ β x₄ = b then (1 : ℂ) else 0) *
        (c * (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃) * S₃ (β x₃) (α x₄) * A₄ (α x₄) (β x₄))) =
      c * (A₁ * S₁ * A₂ * S₂ * A₃ * S₃ * A₄) a b := by
  have hs := fun (g : (X → Fin 4) → ℂ) => sum_pi_four h12 h13 h14 h23 h24 h34 hX g
  simp only [hs, h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_apply_seven]
  simp only [Finset.mul_sum]
  -- reorder `α x₂, α x₃, α x₄, β x₁, β x₂, β x₃` to `α x₄, β x₃, α x₃, β x₂, α x₂, β x₁`
  conv_lhs => enter [2, a2]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a4, 2, a2, 2, a3, 2, b1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a4, 2, a2, 2, a3]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a4, 2, a2]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a4]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a4, 2, b3]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a4, 2, b3, 2, a3, 2, a2]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a4, 2, b3, 2, a3]; rw [Finset.sum_comm]


end Chain

end QED.TwoLoop.Insertion

end
