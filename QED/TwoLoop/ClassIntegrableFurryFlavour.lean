/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassIntegrableFurryEven
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# The regulator-fermion sum of the triangle in divided-difference form

Part of obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3) for the class `Fp`, the
three-line analogue of `QED.TwoLoop.Bridge.flavourSum_bubble`. For one loop flavour the triangle
of `F₊` (three propagators, a numerator of degree three in the loop momentum) is linearly
divergent; under the two Pauli–Villars conditions the flavour sum is a sum of terms with five,
or four, triangle denominators, each ultraviolet convergent.

With `a_f = (A + x_f)⁻¹`, `b_f = (B + x_f)⁻¹`, `d_f = (C + x_f)⁻¹` for the three loop lines,
`x_f = M_f²`, `c₀ = 1`, the conditions `1 + c₁ + c₂ = 0`, `x₀ + c₁ x₁ + c₂ x₂ = 0`, and a numerator
`E₀ + x_f E₂` affine in `x_f` (`QED.TwoLoop.FurryIntegrable.furryNum_eq`):

`∑_f c_f (E₀ + x_f E₂) a_f b_f d_f = (x₁ - x₀)(x₂ - x₀) [(E₀ + x₀ E₂)(a₀b₀d₀d₁d₂ + a₀b₀b₁d₁d₂
  + a₀b₀b₁b₂d₂ + a₀a₁b₁d₁d₂ + a₀a₁b₁b₂d₂ + a₀a₁a₂b₂d₂) - E₂ (a₁b₁d₁d₂ + a₁b₁b₂d₂ + a₁a₂b₂d₂)]`

(`flavourSum_triangle`). This is the Leibniz rule for the second divided difference of
`x ↦ (E₀ + x E₂) a(x) b(x) d(x)` at `x₀, x₁, x₂`, with `a[xᵢ, xⱼ] = -aᵢaⱼ`,
`a[x₀, x₁, x₂] = a₀a₁a₂`. As for the bubble, the conditions enter only through
`c₁ (x₁ - x₂) = x₂ - x₀`, so no distinctness of the masses is needed: the identity is a field
identity, checked by `field_simp; ring` after a `linear_combination` of the two conditions with
the coefficients `G(x₁) - x₁ Y₁₂` and `Y₁₂`, `Y₁₂ = G[x₁, x₂]`.
-/

@[expose] public section

namespace QED.TwoLoop.FurryIntegrable

open Complex QED.WickModel
open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero)

/-- **The regulator-fermion sum of the triangle as a second divided difference** (scalar
form). -/
theorem flavourSum_triangle {A B C x0 x1 x2 c1 c2 E0 E2 : ℂ} (h1 : 1 + c1 + c2 = 0)
    (h2 : x0 + c1 * x1 + c2 * x2 = 0) (hA0 : A + x0 ≠ 0) (hA1 : A + x1 ≠ 0) (hA2 : A + x2 ≠ 0)
    (hB0 : B + x0 ≠ 0) (hB1 : B + x1 ≠ 0) (hB2 : B + x2 ≠ 0)
    (hC0 : C + x0 ≠ 0) (hC1 : C + x1 ≠ 0) (hC2 : C + x2 ≠ 0) :
    (E0 + x0 * E2) * ((A + x0)⁻¹ * (B + x0)⁻¹ * (C + x0)⁻¹) +
        c1 * ((E0 + x1 * E2) * ((A + x1)⁻¹ * (B + x1)⁻¹ * (C + x1)⁻¹)) +
        c2 * ((E0 + x2 * E2) * ((A + x2)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹)) =
      (x1 - x0) * (x2 - x0) *
        ((E0 + x0 * E2) *
            ((A + x0)⁻¹ * (B + x0)⁻¹ * (C + x0)⁻¹ * (C + x1)⁻¹ * (C + x2)⁻¹ +
              (A + x0)⁻¹ * (B + x0)⁻¹ * (B + x1)⁻¹ * (C + x1)⁻¹ * (C + x2)⁻¹ +
              (A + x0)⁻¹ * (B + x0)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹ +
              (A + x0)⁻¹ * (A + x1)⁻¹ * (B + x1)⁻¹ * (C + x1)⁻¹ * (C + x2)⁻¹ +
              (A + x0)⁻¹ * (A + x1)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹ +
              (A + x0)⁻¹ * (A + x1)⁻¹ * (A + x2)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹) -
          E2 * ((A + x1)⁻¹ * (B + x1)⁻¹ * (C + x1)⁻¹ * (C + x2)⁻¹ +
              (A + x1)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹ +
              (A + x1)⁻¹ * (A + x2)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹)) := by
  -- `Y₁₂ = G[x₁, x₂]`, the first divided difference of `G(x) = (E₀ + x E₂) a(x) b(x) d(x)`
  linear_combination (norm := skip)
    ((E0 + x1 * E2) * ((A + x1)⁻¹ * (B + x1)⁻¹ * (C + x1)⁻¹) -
        x1 * (E2 * ((A + x2)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹) - (E0 + x1 * E2) *
          ((A + x1)⁻¹ * (A + x2)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹ +
            (A + x1)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹ +
            (A + x1)⁻¹ * (B + x1)⁻¹ * (C + x1)⁻¹ * (C + x2)⁻¹))) * h1 +
      (E2 * ((A + x2)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹) - (E0 + x1 * E2) *
          ((A + x1)⁻¹ * (A + x2)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹ +
            (A + x1)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ * (C + x2)⁻¹ +
            (A + x1)⁻¹ * (B + x1)⁻¹ * (C + x1)⁻¹ * (C + x2)⁻¹)) * h2
  field_simp
  ring

/-- **The regulator-fermion sum of the triangle in divided-difference form** (propagator
denominators). For `ε ≠ 0`, any momenta `u`, `v`, `w` of the three loop lines and the
Pauli–Villars conditions `1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0`, the flavour sum
`∑_f c_f (E₀ + M_f² E₂) D_f(u)⁻¹ D_f(v)⁻¹ D_f(w)⁻¹` is `(M₁² - m²)(M₂² - m²)` times a sum of terms
with five (coefficient `E₀ + m² E₂`) or four (coefficient `-E₂`) loop denominators. -/
theorem flavourSum_triangle_propDenom {ε : ℝ} (hε : ε ≠ 0) (u v w : Fin 4 → ℝ)
    {m M₁ M₂ c₁ c₂ : ℝ} (h1 : 1 + c₁ + c₂ = 0) (h2 : m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0)
    (E0 E2 : ℂ) :
    (E0 + ((m ^ 2 : ℝ) : ℂ) * E2) *
          ((propDenom m ε u)⁻¹ * (propDenom m ε v)⁻¹ * (propDenom m ε w)⁻¹) +
        (c₁ : ℂ) * ((E0 + ((M₁ ^ 2 : ℝ) : ℂ) * E2) *
          ((propDenom M₁ ε u)⁻¹ * (propDenom M₁ ε v)⁻¹ * (propDenom M₁ ε w)⁻¹)) +
        (c₂ : ℂ) * ((E0 + ((M₂ ^ 2 : ℝ) : ℂ) * E2) *
          ((propDenom M₂ ε u)⁻¹ * (propDenom M₂ ε v)⁻¹ * (propDenom M₂ ε w)⁻¹)) =
      ((((M₁ ^ 2 - m ^ 2) * (M₂ ^ 2 - m ^ 2)) : ℝ) : ℂ) *
        ((E0 + ((m ^ 2 : ℝ) : ℂ) * E2) *
            ((propDenom m ε u)⁻¹ * (propDenom m ε v)⁻¹ * (propDenom m ε w)⁻¹ *
                (propDenom M₁ ε w)⁻¹ * (propDenom M₂ ε w)⁻¹ +
              (propDenom m ε u)⁻¹ * (propDenom m ε v)⁻¹ * (propDenom M₁ ε v)⁻¹ *
                (propDenom M₁ ε w)⁻¹ * (propDenom M₂ ε w)⁻¹ +
              (propDenom m ε u)⁻¹ * (propDenom m ε v)⁻¹ * (propDenom M₁ ε v)⁻¹ *
                (propDenom M₂ ε v)⁻¹ * (propDenom M₂ ε w)⁻¹ +
              (propDenom m ε u)⁻¹ * (propDenom M₁ ε u)⁻¹ * (propDenom M₁ ε v)⁻¹ *
                (propDenom M₁ ε w)⁻¹ * (propDenom M₂ ε w)⁻¹ +
              (propDenom m ε u)⁻¹ * (propDenom M₁ ε u)⁻¹ * (propDenom M₁ ε v)⁻¹ *
                (propDenom M₂ ε v)⁻¹ * (propDenom M₂ ε w)⁻¹ +
              (propDenom m ε u)⁻¹ * (propDenom M₁ ε u)⁻¹ * (propDenom M₂ ε u)⁻¹ *
                (propDenom M₂ ε v)⁻¹ * (propDenom M₂ ε w)⁻¹) -
          E2 * ((propDenom M₁ ε u)⁻¹ * (propDenom M₁ ε v)⁻¹ * (propDenom M₁ ε w)⁻¹ *
                (propDenom M₂ ε w)⁻¹ +
              (propDenom M₁ ε u)⁻¹ * (propDenom M₁ ε v)⁻¹ * (propDenom M₂ ε v)⁻¹ *
                (propDenom M₂ ε w)⁻¹ +
              (propDenom M₁ ε u)⁻¹ * (propDenom M₂ ε u)⁻¹ * (propDenom M₂ ε v)⁻¹ *
                (propDenom M₂ ε w)⁻¹)) := by
  have hd : ∀ (M : ℝ) (z : Fin 4 → ℝ),
      propDenom M ε z = (((Minkowski.dot z z : ℝ) : ℂ) - (ε : ℂ) * I) + ((M ^ 2 : ℝ) : ℂ) := by
    intro M z
    simp only [propDenom]
    push_cast
    ring
  have hne : ∀ (M : ℝ) (z : Fin 4 → ℝ),
      (((Minkowski.dot z z : ℝ) : ℂ) - (ε : ℂ) * I) + ((M ^ 2 : ℝ) : ℂ) ≠ 0 := fun M z =>
    hd M z ▸ propDenom_ne_zero hε z
  have h1' : (1 : ℂ) + c₁ + c₂ = 0 := by exact_mod_cast h1
  have h2' : ((m ^ 2 : ℝ) : ℂ) + c₁ * ((M₁ ^ 2 : ℝ) : ℂ) + c₂ * ((M₂ ^ 2 : ℝ) : ℂ) = 0 := by
    exact_mod_cast h2
  have key := flavourSum_triangle (E0 := E0) (E2 := E2) h1' h2' (hne m u) (hne M₁ u) (hne M₂ u)
    (hne m v) (hne M₁ v) (hne M₂ v) (hne m w) (hne M₁ w) (hne M₂ w)
  simp only [hd]
  rw [key]
  push_cast
  ring

end QED.TwoLoop.FurryIntegrable

end
