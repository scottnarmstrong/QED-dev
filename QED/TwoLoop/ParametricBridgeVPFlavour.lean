/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridgeVP
public import QED.Integration.SymanzikIntegrabilityClasses
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# The vacuum-polarization class: the regulator-fermion sum in divided-difference form

Part of obligations O2-7 and O2-10 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.1–4.4), continuing
`QED/TwoLoop/ParametricBridgeVP.lean`. There the value of `VP` is a joint integral of
`(2π)⁻⁸ ∑_f c_f N_f ∏ᵢ D_{f,i}⁻¹`, a sum over the loop flavour `f` with weights
`c₀ = 1`, `c₁`, `c₂` and loop masses `m`, `M₁`, `M₂`. For one flavour the bubble has two lines and
the loop matrix violates the no-subdivergence criterion. This file proves, at fixed `ε ≠ 0`, that
under the two Pauli–Villars conditions `1 + c₁ + c₂ = 0` and `m² + c₁ M₁² + c₂ M₂² = 0` the flavour
sum is a sum of four terms, each with **four** bubble denominators, and each of a loop matrix that
satisfies the criterion.

## What is true

Write `a_f = (u² + M_f² - iε)⁻¹`, `b_f = (v² + M_f² - iε)⁻¹` for the two bubble lines
(`u = λ₀ - λ₁`, `v = λ₀`) and `x_f = M_f²`.

* **The numerator is even in the loop mass** (`loopTrace_eq`, `vpNumer_eq`): the loop trace is
  `Tr[γ^σ (M - q̸) γ^τ (M - (q+k)̸)] = Tr[γ^σ q̸ γ^τ (q+k)̸] + M² Tr[γ^σ γ^τ]`, because the
  traces of three gamma matrices vanish (`trace_gamma_gamma_slash`, `trace_gamma_slash_gamma`, by
  `γ⁵ = diag(-1, -1, 1, 1)` in the Weyl representation). So `N_f = E₀ + x_f E₂` with `E₀`, `E₂`
  independent of the flavour. **This is needed beyond the Pauli–Villars conditions**: the
  products of the two fermion propagators themselves, `(M_f - q̸)(M_f - (q+k)̸) a_f b_f`, contain a
  part odd in `M_f`, and `∑_f c_f M_f a_f b_f` is not cancelled by the two conditions (it decays
  only like the single-flavour bubble). Only after the trace with the two loop vertices does the
  odd part vanish, term by term.
* **The divided difference** (`flavourSum_bubble`, `flavourSum_propDenom`): with
  `K = (M₁² - m²)(M₂² - m²)`,
  `∑_f c_f (E₀ + x_f E₂) a_f b_f = K [(E₀ + m² E₂)(a₀b₀b₁b₂ + a₀a₁b₁b₂ + a₀a₁a₂b₂)
    - E₂ (a₂⁻¹ + b₁⁻¹) a₁a₂b₁b₂]`.
  This is the Leibniz rule for the second divided difference of `x ↦ (E₀ + x E₂)/((A+x)(B+x))` at
  `m², M₁², M₂²`; the conditions enter only through `c₁ (M₁² - M₂²) = M₂² - m²`, so no distinctness
  of the masses is needed. The identity is a field identity checked by `field_simp; ring` after a
  `linear_combination` of the two conditions.
* **The shapes.** The four terms have the bubble shapes `(a; b b b)`, `(a a; b b)`, `(a a a; b)`,
  `(a a; b b)` (`vpShapeLines`). Only the second and fourth are the doubled bubble
  `loopMatrixVPBubble`. The first and third cannot be brought to that shape with numerators of
  the same degree: `∑_f c_f a_f b_f` decays only like `|u|⁻²` at fixed `v` (and `|v|⁻²` at fixed
  `u`), while a doubled-bubble term with a numerator of degree `0` in `u` decays like `|u|⁻⁴`.
  Multiplying by `(A + x₁) a₁ = 1` does give the doubled shape
  (`K a₀b₀b₁b₂ = (x₁ - x₀)(A + x₁)(a₀a₁b₀b₁ - a₀a₁b₁b₂)`), but raises the bubble degree of the
  numerator by two, which makes those terms logarithmically divergent in the bubble one by one.
  In the form used here every term has numerator degree at most `2` in the bubble momentum over
  four bubble denominators. All four loop matrices (photons doubled, four bubble lines) satisfy
  the no-subdivergence criterion (`intNoSubdivergence_vpShapeMatrix`), also in the frozen line
  order (`intNoSubdivergence_frozen_vpShape`), and all four have the uniform positivity bound of
  `V` (`symanzikV_vpShape_ge`).

## Main statement

`parametricForm_VP`: for `ε ≠ 0`, under momentum conservation and the two Pauli–Villars
conditions, the value (T₁₀) of `VP` is the joint energy-first integral of
`(2π)⁻⁸ ∑ₜ₌₀³ Nₜ(λ) ∏ᵢ₌₀⁹ D_{t,i}(λ)⁻¹`, with `D_{t,i} = vpDenom P t …` the line denominators of
the loop matrix `vpShapeMatrix t` (masses `vpShapeMasses P t`), and `Nₜ = vpTermNumer … t` of total
degree at most `4` in the class loop momenta (and in the frozen ones,
`isLoopPoly_vpTermNumer_frozen`); every `vpShapeMatrix t` satisfies the criterion.
-/

@[expose] public section

namespace QED.TwoLoop.Bridge

open Complex QED.WickModel QED.TwoLoop.Enumeration
open QED.TwoLoop.NestedVP (cV flavV nestedMom)
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  class5LoopMatrixPV classVPMomenta classVPPVMasses classVPMasses classVPBubbleMasses
  loopMatrixVP loopMatrixVPBubble pvLines IntNoSubdivergence NoSubdivergence symanzikU symanzikV)

/-! ### `γ⁵` and the traces of three gamma matrices -/

/-- `γ⁵ = diag(-1, -1, 1, 1)`, in the Weyl representation of `QED.Dirac.gamma`. -/
def gamma5 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![-1, -1, 1, 1]

theorem gamma5_mul_gamma5 : gamma5 * gamma5 = 1 := by
  rw [gamma5, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem gamma5_conj_gamma (μ : Fin 4) : gamma5 * Dirac.gamma μ * gamma5 = -Dirac.gamma μ := by
  ext i j
  rw [gamma5, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases μ <;> fin_cases i <;> fin_cases j <;> simp [Dirac.gamma]

theorem gamma5_conj_mul (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    gamma5 * (X * Y) * gamma5 = (gamma5 * X * gamma5) * (gamma5 * Y * gamma5) := by
  calc gamma5 * (X * Y) * gamma5 = gamma5 * X * (gamma5 * gamma5) * Y * gamma5 := by
        rw [gamma5_mul_gamma5, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem gamma5_conj_slash (p : Fin 4 → ℝ) : gamma5 * Dirac.slash p * gamma5 = -Dirac.slash p := by
  simp only [Dirac.slash, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    gamma5_conj_gamma, smul_neg, Finset.sum_neg_distrib]

theorem trace_eq_zero_of_gamma5_conj {X : Matrix (Fin 4) (Fin 4) ℂ}
    (h : gamma5 * X * gamma5 = -X) : X.trace = 0 := by
  have h1 : (gamma5 * X * gamma5).trace = X.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, gamma5_mul_gamma5, Matrix.one_mul]
  rw [h, Matrix.trace_neg] at h1
  linear_combination (-1 / 2 : ℂ) * h1

/-- `Tr[γ^a γ^b r̸] = 0`. -/
theorem trace_gamma_gamma_slash (a b : Fin 4) (r : Fin 4 → ℝ) :
    (Dirac.gamma a * Dirac.gamma b * Dirac.slash r).trace = 0 :=
  trace_eq_zero_of_gamma5_conj (by
    rw [gamma5_conj_mul, gamma5_conj_mul, gamma5_conj_gamma, gamma5_conj_gamma, gamma5_conj_slash]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg])

/-- `Tr[γ^a q̸ γ^b] = 0`. -/
theorem trace_gamma_slash_gamma (a b : Fin 4) (q : Fin 4 → ℝ) :
    (Dirac.gamma a * Dirac.slash q * Dirac.gamma b).trace = 0 :=
  trace_eq_zero_of_gamma5_conj (by
    rw [gamma5_conj_mul, gamma5_conj_mul, gamma5_conj_gamma, gamma5_conj_gamma, gamma5_conj_slash]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg])

/-! ### The numerator is even in the loop mass -/

/-- **The loop trace is even in the loop mass**:
`Tr[γ^σ (M - q̸) γ^τ (M - (q+k)̸)] = Tr[γ^σ (-q̸) γ^τ (-(q+k)̸)] + M² Tr[γ^σ γ^τ]`. -/
theorem loopTrace_eq (M : ℝ) (q k : Fin 4 → ℝ) (σ τ : Fin 4) :
    loopTrace M q k σ τ =
      loopTrace 0 q k σ τ + ((M ^ 2 : ℝ) : ℂ) * (Dirac.gamma σ * Dirac.gamma τ).trace := by
  simp only [loopTrace, electronNumerator, Complex.ofReal_zero, zero_smul, zero_sub,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    trace_gamma_gamma_slash, trace_gamma_slash_gamma]
  push_cast
  ring

/-- The `M²` part of the numerator of `VP`: the loop trace replaced by `Tr[γ^σ γ^τ]`. -/
noncomputable def vpNumer2 (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ) :
    ℂ :=
  (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4,
    outerNum P p kext k μ l0 l2 α β *
      ((Minkowski.metric l0 l3 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
      ((Minkowski.metric l2 l4 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
      (Dirac.gamma l3 * Dirac.gamma l4).trace

/-- **The numerator of `VP` is affine in `M²`**: `N(M) = N(0) + M² N₂`. -/
theorem vpNumer_eq (P : Params) (M : ℝ) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (q k : Fin 4 → ℝ) :
    vpNumer P M p kext α β μ q k =
      vpNumer P 0 p kext α β μ q k + ((M ^ 2 : ℝ) : ℂ) * vpNumer2 P p kext α β μ k := by
  rw [vpNumer, vpNumer, vpNumer2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [loopTrace_eq M]
  ring

/-- The flavour-independent part `E₀` of the numerator, in the class loop momenta. -/
noncomputable def vpE0 (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vpNumerator P 0 pIn kIn αOut βIn μ ℓ

/-- The coefficient `E₂` of `M_f²` in the numerator, in the class loop momenta. -/
noncomputable def vpE2 (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vpNumer2 P (pIn 0) (kIn 0) (αOut 0) (βIn 0) (μ 0) (-ℓ 1)

theorem vpNumerator_eq (P : Params) (M : ℝ) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpNumerator P M pIn kIn αOut βIn μ ℓ =
      vpE0 P pIn kIn αOut βIn μ ℓ + ((M ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ :=
  vpNumer_eq _ _ _ _ _ _ _ _ _

/-! ### The divided difference -/

/-- **The regulator-fermion sum as a second divided difference** (scalar form). With
`a_f = (A + x_f)⁻¹`, `b_f = (B + x_f)⁻¹` and the conditions `1 + c₁ + c₂ = 0`,
`x₀ + c₁ x₁ + c₂ x₂ = 0`:
`∑_f c_f (E₀ + x_f E₂) a_f b_f = (x₁ - x₀)(x₂ - x₀) [(E₀ + x₀E₂)(a₀b₀b₁b₂ + a₀a₁b₁b₂ + a₀a₁a₂b₂)
  - E₂ ((A + x₂) + (B + x₁)) a₁a₂b₁b₂]`. -/
theorem flavourSum_bubble {A B x0 x1 x2 c1 c2 E0 E2 : ℂ} (h1 : 1 + c1 + c2 = 0)
    (h2 : x0 + c1 * x1 + c2 * x2 = 0) (hA0 : A + x0 ≠ 0) (hA1 : A + x1 ≠ 0) (hA2 : A + x2 ≠ 0)
    (hB0 : B + x0 ≠ 0) (hB1 : B + x1 ≠ 0) (hB2 : B + x2 ≠ 0) :
    (E0 + x0 * E2) * ((A + x0)⁻¹ * (B + x0)⁻¹) +
        c1 * ((E0 + x1 * E2) * ((A + x1)⁻¹ * (B + x1)⁻¹)) +
        c2 * ((E0 + x2 * E2) * ((A + x2)⁻¹ * (B + x2)⁻¹)) =
      (x1 - x0) * (x2 - x0) *
        ((E0 + x0 * E2) * ((A + x0)⁻¹ * (B + x0)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ +
            (A + x0)⁻¹ * (A + x1)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ +
            (A + x0)⁻¹ * (A + x1)⁻¹ * (A + x2)⁻¹ * (B + x2)⁻¹) -
          E2 * ((A + x2) + (B + x1)) * ((A + x1)⁻¹ * (A + x2)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹)) := by
  -- `Y₁₂ = G[x₁, x₂]`, the first divided difference of `G(x) = (E₀ + x E₂) a(x) b(x)`
  linear_combination (norm := skip)
    ((E0 + x1 * E2) * ((A + x1)⁻¹ * (B + x1)⁻¹) -
        x1 * (E2 * ((A + x2)⁻¹ * (B + x2)⁻¹) - (E0 + x1 * E2) *
          ((A + x1)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ + (A + x1)⁻¹ * (A + x2)⁻¹ * (B + x2)⁻¹))) * h1 +
      (E2 * ((A + x2)⁻¹ * (B + x2)⁻¹) - (E0 + x1 * E2) *
          ((A + x1)⁻¹ * (B + x1)⁻¹ * (B + x2)⁻¹ + (A + x1)⁻¹ * (A + x2)⁻¹ * (B + x2)⁻¹)) * h2
  field_simp
  ring

/-- **The regulator-fermion sum in divided-difference form** (propagator denominators). For
`ε ≠ 0`, any momenta `u`, `v` of the two bubble lines and the Pauli–Villars conditions
`1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0`, the flavour sum
`∑_f c_f (E₀ + M_f² E₂) D_f(u)⁻¹ D_f(v)⁻¹` is `(M₁² - m²)(M₂² - m²)` times a sum of terms with four
bubble denominators. -/
theorem flavourSum_propDenom {ε : ℝ} (hε : ε ≠ 0) (u v : Fin 4 → ℝ) {m M₁ M₂ c₁ c₂ : ℝ}
    (h1 : 1 + c₁ + c₂ = 0) (h2 : m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (E0 E2 : ℂ) :
    (E0 + ((m ^ 2 : ℝ) : ℂ) * E2) * ((propDenom m ε u)⁻¹ * (propDenom m ε v)⁻¹) +
        (c₁ : ℂ) * ((E0 + ((M₁ ^ 2 : ℝ) : ℂ) * E2) *
          ((propDenom M₁ ε u)⁻¹ * (propDenom M₁ ε v)⁻¹)) +
        (c₂ : ℂ) * ((E0 + ((M₂ ^ 2 : ℝ) : ℂ) * E2) *
          ((propDenom M₂ ε u)⁻¹ * (propDenom M₂ ε v)⁻¹)) =
      ((((M₁ ^ 2 - m ^ 2) * (M₂ ^ 2 - m ^ 2)) : ℝ) : ℂ) *
        ((E0 + ((m ^ 2 : ℝ) : ℂ) * E2) *
            ((propDenom m ε u)⁻¹ * (propDenom m ε v)⁻¹ * (propDenom M₁ ε v)⁻¹ *
                (propDenom M₂ ε v)⁻¹ +
              (propDenom m ε u)⁻¹ * (propDenom M₁ ε u)⁻¹ * (propDenom M₁ ε v)⁻¹ *
                (propDenom M₂ ε v)⁻¹ +
              (propDenom m ε u)⁻¹ * (propDenom M₁ ε u)⁻¹ * (propDenom M₂ ε u)⁻¹ *
                (propDenom M₂ ε v)⁻¹) -
          E2 * (propDenom M₂ ε u + propDenom M₁ ε v) *
            ((propDenom M₁ ε u)⁻¹ * (propDenom M₂ ε u)⁻¹ * (propDenom M₁ ε v)⁻¹ *
              (propDenom M₂ ε v)⁻¹)) := by
  have hd : ∀ (M : ℝ) (w : Fin 4 → ℝ),
      propDenom M ε w = (((Minkowski.dot w w : ℝ) : ℂ) - (ε : ℂ) * I) + ((M ^ 2 : ℝ) : ℂ) := by
    intro M w
    simp only [propDenom]
    push_cast
    ring
  have hne : ∀ (M : ℝ) (w : Fin 4 → ℝ),
      (((Minkowski.dot w w : ℝ) : ℂ) - (ε : ℂ) * I) + ((M ^ 2 : ℝ) : ℂ) ≠ 0 := fun M w =>
    hd M w ▸ propDenom_ne_zero hε w
  have h1' : (1 : ℂ) + c₁ + c₂ = 0 := by exact_mod_cast h1
  have h2' : ((m ^ 2 : ℝ) : ℂ) + c₁ * ((M₁ ^ 2 : ℝ) : ℂ) + c₂ * ((M₂ ^ 2 : ℝ) : ℂ) = 0 := by
    exact_mod_cast h2
  have key := flavourSum_bubble (E0 := E0) (E2 := E2) h1' h2' (hne m u) (hne M₁ u) (hne M₂ u)
    (hne m v) (hne M₁ v) (hne M₂ v)
  simp only [hd]
  rw [key]
  push_cast
  ring

/-! ### The four shapes -/

/-- The line maps of the four terms: lines `0 … 7` as in `class5LoopMatrixPV .VP` (open line,
bubble lines `2` (`v₃v₄`, momentum `u`) and `3` (`v₄v₃`, momentum `v`), photons doubled), and the
extra bubble lines `8`, `9`: shapes `(u; v v v)`, `(u u; v v)`, `(u u u; v)`, `(u u; v v)`. -/
def vpShapeLines : Fin 4 → Fin 10 → Fin 6
  | 0 => ![0, 1, 2, 3, 4, 5, 4, 5, 3, 3]
  | 1 => ![0, 1, 2, 3, 4, 5, 4, 5, 2, 3]
  | 2 => ![0, 1, 2, 3, 4, 5, 4, 5, 2, 2]
  | 3 => ![0, 1, 2, 3, 4, 5, 4, 5, 2, 3]

/-- The loop matrix of term `t`: the rows of `class5LoopMatrix .VP` along `vpShapeLines t`. -/
def vpShapeMatrix (t : Fin 4) : Fin 10 → Fin 2 → ℤ :=
  fun i => class5LoopMatrix .VP (vpShapeLines t i)

/-- Terms `1` and `3` have the doubled-bubble loop matrix. -/
theorem vpShapeMatrix_bubble :
    vpShapeMatrix 1 = loopMatrixVPBubble ∧ vpShapeMatrix 3 = loopMatrixVPBubble :=
  ⟨rfl, rfl⟩

/-- **All four loop matrices satisfy the no-subdivergence criterion.** -/
theorem intNoSubdivergence_vpShapeMatrix : ∀ t, IntNoSubdivergence (vpShapeMatrix t) := by
  decide

theorem noSubdivergence_vpShapeMatrix (t : Fin 4) :
    NoSubdivergence (castLoopMatrix (vpShapeMatrix t)) :=
  (QED.Integration.TwoLoop.noSubdivergence_castLoopMatrix_iff _).mpr
    (intNoSubdivergence_vpShapeMatrix t)

/-- The same in the frozen routing (frozen loop matrix along the same line maps). -/
theorem intNoSubdivergence_frozen_vpShape :
    ∀ t, IntNoSubdivergence fun i => frozenLoopMatrixVP (vpShapeLines t i) := by
  decide

/-- The masses of term `t`: open line `m`, photons `m_γ` (lines `4, 5`) and `Λ` (lines `6, 7`),
bubble lines `2, 3, 8, 9`: `(m, m, M₁, M₂)`, `(m, M₁, M₁, M₂)`, `(m, M₂, M₁, M₂)`,
`(M₁, M₁, M₂, M₂)`. -/
def vpShapeMasses (P : Params) : Fin 4 → Fin 10 → ℝ
  | 0 => ![P.m, P.m, P.m, P.m, P.mγ, P.mγ, P.Λ, P.Λ, P.M₁, P.M₂]
  | 1 => ![P.m, P.m, P.m, P.M₁, P.mγ, P.mγ, P.Λ, P.Λ, P.M₁, P.M₂]
  | 2 => ![P.m, P.m, P.m, P.M₂, P.mγ, P.mγ, P.Λ, P.Λ, P.M₁, P.M₂]
  | 3 => ![P.m, P.m, P.M₁, P.M₁, P.mγ, P.mγ, P.Λ, P.Λ, P.M₂, P.M₂]

theorem vpShapeMasses_bubble (P : Params) :
    vpShapeMasses P 1 = classVPBubbleMasses P.m P.m P.M₁ P.M₁ P.M₂ P.mγ P.mγ P.Λ P.Λ ∧
      vpShapeMasses P 3 = classVPBubbleMasses P.m P.M₁ P.M₁ P.M₂ P.M₂ P.mγ P.mγ P.Λ P.Λ :=
  ⟨rfl, rfl⟩

/-- The external momenta of the lines of term `t`. -/
def vpShapeMomenta (t : Fin 4) (p p' : Fin 4 → ℝ) : Fin 10 → Fin 4 → ℝ :=
  fun i => classVPMomenta p p' (vpShapeLines t i)

/-- The line denominator `D_{t,i}(λ)` of term `t`. -/
noncomputable def vpDenom (P : Params) (t : Fin 4) (p p' : Fin 4 → ℝ) (i : Fin 10)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  lineDenom (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') (vpShapeMasses P t) P.ε i ℓ

/-- **Positivity of `V` for the four shapes**: for masses at least those of `VP` with all loop
masses `m` and photon masses `m_γ`, `V ≥ (3/4) min(m², m_γ²)` wherever `U ≠ 0` on the simplex. -/
theorem symanzikV_vpShape_ge (t : Fin 4) {mass mγ : ℝ} {M' : Fin 10 → ℝ}
    (hM' : ∀ i, classVPMasses mass mass mγ mγ (vpShapeLines t i) ^ 2 ≤ M' i ^ 2)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {z : Fin 10 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1) (hU : symanzikU (castLoopMatrix (vpShapeMatrix t)) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') M' z :=
  QED.Integration.TwoLoop.le_symanzikV_comp_of (σ := vpShapeLines t) (α := loopMatrixVP)
    (fun _ hw hw1 hU' =>
      QED.Integration.TwoLoop.symanzikV_classVP_ge le_rfl hp hp' hq le_rfl le_rfl hw hw1 hU')
    hM' hz hz1 hU

/-- The mass condition of `symanzikV_vpShape_ge` for the masses of the model. -/
theorem classVPMasses_vpShapeLines_le (P : Params) (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2)
    (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) (t : Fin 4) (i : Fin 10) :
    classVPMasses P.m P.m P.mγ P.mγ (vpShapeLines t i) ^ 2 ≤ vpShapeMasses P t i ^ 2 := by
  fin_cases t <;> fin_cases i <;>
    simp [classVPMasses, vpShapeLines, vpShapeMasses, h₁, h₂, hΛ]

/-! ### The numerators of the four terms -/

/-- `K = (M₁² - m²)(M₂² - m²)`, the coefficient of the second divided difference. -/
noncomputable def vpBubbleCoeff (P : Params) : ℂ :=
  (((P.M₁ ^ 2 - P.m ^ 2) * (P.M₂ ^ 2 - P.m ^ 2) : ℝ) : ℂ)

/-- The numerator of term `t`: `K (E₀ + m² E₂)` for `t = 0, 1, 2`, and
`-K E₂ (D_{3,8} + D_{3,3})` for `t = 3`. -/
noncomputable def vpTermNumer (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (t : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  if t = 3 then
    -(vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ *
      (vpDenom P 3 (pIn 0) (pOut 0) 8 ℓ + vpDenom P 3 (pIn 0) (pOut 0) 3 ℓ))
  else
    vpBubbleCoeff P * (vpE0 P pIn kIn αOut βIn μ ℓ +
      ((P.m ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ)

/-! ### The integrand in divided-difference form -/

theorem prod_univ_ten {M : Type*} [CommMonoid M] (f : Fin 10 → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.prod_univ_eight]
  rfl

/-- The line momenta of the class routing of `VP`. -/
def classLineVP (p p' : Fin 4 → ℝ) (j : Fin 6) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix (class5LoopMatrix .VP)) (classVPMomenta p p') j ℓ

theorem vpDenom_eq (P : Params) (t : Fin 4) (p p' : Fin 4 → ℝ) (i : Fin 10)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpDenom P t p p' i ℓ =
      propDenom (vpShapeMasses P t i) P.ε (classLineVP p p' (vpShapeLines t i) ℓ) :=
  rfl

theorem pvDenomVP_eq (P : Params) (f : Fin 3) (p p' : Fin 4 → ℝ) (i : Fin 8)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    pvDenomVP P f p p' i ℓ =
      propDenom (classVPPVMasses P.m (P.mass f) P.mγ P.mγ P.Λ P.Λ i) P.ε
        (classLineVP p p' (pvLines i) ℓ) :=
  rfl

/-- **The integrand of `VP` in divided-difference form.** For `ε ≠ 0`, under momentum
conservation and the two Pauli–Villars conditions, the regulated amplitude (T₈) in the class
routing is `∑ₜ Nₜ ∏ᵢ₌₀⁹ D_{t,i}⁻¹`. -/
theorem regulatedAmplitude₂_classMomVP_shapes (P : Params) (hε : P.ε ≠ 0)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cV pIn kIn (classMomVP (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
        ∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹ := by
  rw [regulatedAmplitude₂_classMomVP P hε hmom]
  simp only [vpNumerator_eq, Fin.sum_univ_three, Fin.sum_univ_four, Fin.prod_univ_eight,
    prod_univ_ten, vpDenom_eq, pvDenomVP_eq, vpTermNumer]
  simp only [Params.loopCoeff, Params.mass, vpShapeMasses, vpShapeLines, classVPPVMasses, pvLines,
    Matrix.cons_val, Fin.isValue, Fin.reduceEq, ↓reduceIte, Complex.ofReal_one, vpBubbleCoeff]
  have key := flavourSum_propDenom hε (classLineVP (pIn 0) (pOut 0) 2 ℓ)
    (classLineVP (pIn 0) (pOut 0) 3 ℓ) hc₁ hc₂ (vpE0 P pIn kIn αOut βIn μ ℓ)
    (vpE2 P pIn kIn αOut βIn μ ℓ)
  linear_combination
    ((propDenom P.m P.ε (classLineVP (pIn 0) (pOut 0) 0 ℓ))⁻¹ *
      (propDenom P.m P.ε (classLineVP (pIn 0) (pOut 0) 1 ℓ))⁻¹ *
      (propDenom P.mγ P.ε (classLineVP (pIn 0) (pOut 0) 4 ℓ))⁻¹ *
      (propDenom P.mγ P.ε (classLineVP (pIn 0) (pOut 0) 5 ℓ))⁻¹ *
      (propDenom P.Λ P.ε (classLineVP (pIn 0) (pOut 0) 4 ℓ))⁻¹ *
      (propDenom P.Λ P.ε (classLineVP (pIn 0) (pOut 0) 5 ℓ))⁻¹) * key

/-! ### Degree bounds -/

/-- The entries of a matrix-valued function are polynomials of total degree at most `n` in the
loop momenta. -/
def IsLoopPolyMat (L n : ℕ) (A : (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ i j, IsLoopPoly L n fun ℓ => A ℓ i j

namespace IsLoopPolyMat

variable {L n n' : ℕ} {A B : (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}

theorem const (C : Matrix (Fin 4) (Fin 4) ℂ) : IsLoopPolyMat L 0 fun _ => C :=
  fun _ _ => IsLoopPoly.const _

theorem mul (hA : IsLoopPolyMat L n A) (hB : IsLoopPolyMat L n' B) :
    IsLoopPolyMat L (n + n') fun ℓ => A ℓ * B ℓ := fun i j => by
  simp only [Matrix.mul_apply]
  exact IsLoopPoly.sum _ fun k _ => (hA i k).mul (hB k j)

theorem trace (hA : IsLoopPolyMat L n A) : IsLoopPoly L n fun ℓ => (A ℓ).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact IsLoopPoly.sum _ fun i _ => hA i i

end IsLoopPolyMat

theorem IsLoopAffine.isLoopPolyMat_electronNumerator {L : ℕ}
    {F : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ} (hF : IsLoopAffine F) (m : ℝ) :
    IsLoopPolyMat L 1 fun ℓ => electronNumerator m (F ℓ) :=
  fun a b => hF.isLoopPoly_electronNumerator m a b

/-- The denominator `k² + M² - iε` at a momentum affine in the loop momenta has degree at most
two. -/
theorem IsLoopAffine.isLoopPoly_propDenom {L : ℕ} {F : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : IsLoopAffine F) (M ε : ℝ) : IsLoopPoly L 2 fun ℓ => propDenom M ε (F ℓ) := by
  have h : (fun ℓ => propDenom M ε (F ℓ)) = fun ℓ =>
      (∑ μ ∈ Finset.univ, ∑ ν ∈ Finset.univ, ((Minkowski.metric μ ν : ℝ) : ℂ) *
        (((F ℓ μ : ℝ) : ℂ) * ((F ℓ ν : ℝ) : ℂ))) + (((M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) := by
    funext ℓ
    simp only [propDenom, Minkowski.dot]
    push_cast
    simp only [mul_assoc]
    ring
  rw [h]
  exact (IsLoopPoly.sum _ fun μ _ => IsLoopPoly.sum _ fun ν _ =>
    ((hF.isLoopPoly_coord μ).mul (hF.isLoopPoly_coord ν)).const_mul _).add (IsLoopPoly.const _)

theorem isLoopAffine_affine (a : Fin 2 → ℝ) (b : Fin 4 → ℝ) :
    IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => a 0 • ℓ 0 + a 1 • ℓ 1 + b :=
  ⟨a, b, fun ℓ => by simp [Fin.sum_univ_two]⟩

theorem isLoopAffine_vpLines (p kext : Fin 4 → ℝ) :
    IsLoopAffine (fun ℓ : Fin 2 → Fin 4 → ℝ => ℓ 0) ∧
      IsLoopAffine (fun ℓ : Fin 2 → Fin 4 → ℝ => ℓ 0 + -ℓ 1) ∧
      IsLoopAffine (fun ℓ : Fin 2 → Fin 4 → ℝ => p + kext - -ℓ 1) ∧
      IsLoopAffine (fun ℓ : Fin 2 → Fin 4 → ℝ => p - -ℓ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (congrArg IsLoopAffine (funext fun ℓ => ?_)).mp (isLoopAffine_affine ![1, 0] 0)
    simp
  · refine (congrArg IsLoopAffine (funext fun ℓ => ?_)).mp (isLoopAffine_affine ![1, -1] 0)
    simp
  · refine (congrArg IsLoopAffine (funext fun ℓ => ?_)).mp
      (isLoopAffine_affine ![0, 1] (p + kext))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_smul,
      one_smul, zero_add]
    abel
  · refine (congrArg IsLoopAffine (funext fun ℓ => ?_)).mp (isLoopAffine_affine ![0, 1] p)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_smul,
      one_smul, zero_add]
    abel

theorem isLoopPolyMat_outerNum (P : Params) (p kext : Fin 4 → ℝ) (μ ρ ν : Fin 4) :
    IsLoopPolyMat 2 2 fun ℓ => outerNum P p kext (-ℓ 1) μ ρ ν := by
  obtain ⟨-, -, h12, h01⟩ := isLoopAffine_vpLines p kext
  have h := ((((IsLoopPolyMat.const (L := 2) (Dirac.gamma ν)).mul
    (h12.isLoopPolyMat_electronNumerator P.m)).mul (IsLoopPolyMat.const (Dirac.gamma μ))).mul
      (h01.isLoopPolyMat_electronNumerator P.m)).mul (IsLoopPolyMat.const (Dirac.gamma ρ))
  exact h

/-- `E₀` has total degree at most `4` in the class loop momenta. -/
theorem isLoopPoly_vpE0 (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) : IsLoopPoly 2 4 (vpE0 P pIn kIn αOut βIn μ) := by
  obtain ⟨hq, hqk, -, -⟩ := isLoopAffine_vpLines (pIn 0) (kIn 0)
  unfold vpE0 vpNumerator vpNumer
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l2 _ =>
    IsLoopPoly.sum _ fun l3 _ => IsLoopPoly.sum _ fun l4 _ => ?_)
  have ht : IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ => loopTrace 0 (ℓ 0) (-ℓ 1) l3 l4 :=
    ((((IsLoopPolyMat.const (L := 2) (Dirac.gamma l3)).mul
      (hq.isLoopPolyMat_electronNumerator 0)).mul (IsLoopPolyMat.const (Dirac.gamma l4))).mul
        (hqk.isLoopPolyMat_electronNumerator 0)).trace
  exact ((((isLoopPolyMat_outerNum P (pIn 0) (kIn 0) (μ 0) l0 l2) (αOut 0) (βIn 0)).mul
    (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)).mul ht

/-- `E₂` has total degree at most `2` in the class loop momenta. -/
theorem isLoopPoly_vpE2 (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) : IsLoopPoly 2 2 (vpE2 P pIn kIn αOut βIn μ) := by
  unfold vpE2 vpNumer2
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l2 _ =>
    IsLoopPoly.sum _ fun l3 _ => IsLoopPoly.sum _ fun l4 _ => ?_)
  exact ((((isLoopPolyMat_outerNum P (pIn 0) (kIn 0) (μ 0) l0 l2) (αOut 0) (βIn 0)).mul
    (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)).mul
      (IsLoopPoly.const (n := 0) _)

theorem isLoopPoly_vpDenom (P : Params) (t : Fin 4) (p p' : Fin 4 → ℝ) (i : Fin 10) :
    IsLoopPoly 2 2 (vpDenom P t p p' i) :=
  (isLoopAffine_lineMomentum (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') i
    ).isLoopPoly_propDenom _ _

/-- **The numerators of the four terms have total degree at most `4`** in the class loop
momenta. -/
theorem isLoopPoly_vpTermNumer (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (t : Fin 4) :
    IsLoopPoly 2 4 (vpTermNumer P pOut pIn kIn αOut βIn μ t) := by
  unfold vpTermNumer
  split_ifs
  · have h := (((isLoopPoly_vpE2 P pIn kIn αOut βIn μ).const_mul (vpBubbleCoeff P)).mul
      ((isLoopPoly_vpDenom P 3 (pIn 0) (pOut 0) 8).add
        (isLoopPoly_vpDenom P 3 (pIn 0) (pOut 0) 3))).const_mul (-1)
    simpa [mul_assoc] using h
  · exact ((isLoopPoly_vpE0 P pIn kIn αOut βIn μ).add
      (((isLoopPoly_vpE2 P pIn kIn αOut βIn μ).const_mul _).mono (by norm_num))).const_mul _

/-- The numerators in the frozen loop momenta also have total degree at most `4`. -/
theorem isLoopPoly_vpTermNumer_frozen (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (t : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => vpTermNumer P pOut pIn kIn αOut βIn μ t (chgVP (pIn 0) ℓ) :=
  (isLoopPoly_vpTermNumer P pOut pIn kIn αOut βIn μ t).comp_intAffine matVP _

/-! ### The value -/

/-- **Parametric form of `VP`.** For `ε ≠ 0`, under momentum conservation and the two
Pauli–Villars conditions `1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0`, the value (T₁₀) of the
vacuum-polarization class is the joint energy-first integral of
`(2π)⁻⁸ ∑ₜ₌₀³ Nₜ(λ) ∏ᵢ₌₀⁹ D_{t,i}(λ)⁻¹` in the class loop momenta, with `Nₜ` polynomials of total
degree at most `4` and `D_{t,i}` the line denominators of the loop matrices `vpShapeMatrix t`,
each of which satisfies the no-subdivergence criterion. -/
theorem parametricForm_VP (P : Params) (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
            ∑ t : Fin 4, vpTermNumer P pOut pIn kIn αOut βIn μ t ℓ *
              ∏ i : Fin 10, (vpDenom P t (pIn 0) (pOut 0) i ℓ)⁻¹) ∧
      (∀ t, IsLoopPoly 2 4 (vpTermNumer P pOut pIn kIn αOut βIn μ t)) ∧
      (∀ t, NoSubdivergence (castLoopMatrix (vpShapeMatrix t))) := by
  refine ⟨?_, isLoopPoly_vpTermNumer P pOut pIn kIn αOut βIn μ, noSubdivergence_vpShapeMatrix⟩
  rw [contractionValue₂_VP_eq_flavourSum P hε hmom]
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [← regulatedAmplitude₂_classMomVP P hε hmom,
    regulatedAmplitude₂_classMomVP_shapes P hε hc₁ hc₂ hmom]

end QED.TwoLoop.Bridge

end
