/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphTraceMain
public import QED.TwoLoop.UnitLGraph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The `d`-dimensional scheme of the crossed-ladder (X) numerator

Entries of the trace scheme of `QED/DimReg/TwoLoopBridgeTrace.lean` for the crossed ladder,
with the same convention: **scheme definitions, not theorems**. Each entry is a named, exposed
definition whose docstring states the `d`-dimensional object, with a proved `d = 4` check
against the model's four-dimensional trace (`QED/TwoLoop/UnitXGraphTraceMain.lean`).

## The `d`-dimensional Pauli projector

Conventions of the model: metric `(-, +, +, +)`, `{γ^μ, γ^ν} = -2 g^{μν}`, `N(k) = m - k̸`,
`tr 1 = 4`, and in `d` dimensions `g^μ_μ = d`, so `γ^μ γ_μ = -d`. The model's Pauli matrix
(`QED.TwoLoop.UnitLGraph.pauliMat`) is
`P_μ = m(4m² + q²) N(p) γ_μ N(p') + (q² - 2m²)(p' + p)_μ N(p) N(p')`.
Contracted with `d`-dimensional indices it does **not** annihilate the Dirac structure `γ^μ`
of `F₁`: `tr(P_μ γ^μ) = 2 m q² (q² + 4m²)(d - 4)`, which at second order along the on-shell
curve gives `F₂ ↦ F₂ + c (d - 4) F₁`; on a graph whose `F₁` has a pole at `d = 4` (the crossed
ladder: the overall vertex divergence) this leaves a finite spurious term. The scheme
therefore uses the `d`-dimensional projector
`P^d_μ = A_d N(p) γ_μ N(p') + B_d (p' + p)_μ N(p) N(p')`,
`A_d = 2m(4m² + q²)/(d - 2)` (`pauliProjA`), `B_d = q² - 4m²/(d - 2)` (`pauliProjB`),
the unique coefficients with `tr(P^d_μ γ^μ) = 0` and `tr(P^d_μ (p' + p)^μ)` equal to the model's
value for every `d` (`pauliProj_annihilates_F₁`, `pauliProj_normalization`). At `d = 4` it is
the model's matrix (`pauliMat_eq_pauliProj`). On the one-loop vertex it reproduces the Pauli
numerator `QED.DimReg.OneLoopBridge.pauliNum` (restated in
`QED/DimReg/TwoLoopBridgeTrace.lean`) exactly, after integration over the split of the electron
weight `w`.

## The crossed-ladder numerator

With the slot momenta `qₖ = aₖ p + bₖ p'` of the chain, the slot data `αₖ = aₖ + bₖ`,
`βₖ = bₖ`, the contraction coefficients `C_{kl}` and the crossed contraction
`xw(P; Y) = tr(γ^ν P_μ γ^σ Y₀ γ_ν Y₁ γ^μ Y₂ γ_σ Y₃)`
(`QED.TwoLoop.UnitXGraph.xw`), the projected numerator is `N = T₁ + T₂ V + T₃ V²` with
`T₁ ∝ xw(P; Ē)`, `T₂ ∝ Σ_{k<l} C_{kl} xw(P; Ē with slots k, l contracted)` and `T₃` the three
double contractions. In `d` dimensions (all of `γ^ν, γ^σ, γ^μ` and the contraction index
`d`-dimensional, projector `P^d`), the second-order coefficients along the on-shell curve are,
at `m = 1`,
`c₂[xw(P^d; Ē)] = 512 Ψ₁ᵈ(α, β, 1)`, `c₂[Σ C_{kl} xw(P^d; …)] = -1024 Ψ₂ᵈ(α, β, C, 1)`,
`c₂[T₃ᵈ] = 0`
(the same normalizations as `QED.TwoLoop.UnitXGraph.xT1_slot`, `xT2_slot`), with `Ψ₁ᵈ`
(`psiT1d`) and `Ψ₂ᵈ` (`psiT2d`) polynomials in `ε = (4 - d)/2`, homogeneous of degrees `4` and
`3` in the slot data and `u = U`, as the model's `psiT1h`, `psiT2h`. `T₃ᵈ` vanishes identically
because the double contractions leave only the structure `γ^μ`, which `P^d` annihilates; with
the model's projector it would be a nonzero multiple of `d - 4`. The `d = 4` checks
`psiT1d_four`, `psiT2d_four` are `ring`.

The polynomials are the output of the conventional `d`-dimensional trace algebra applied to the
chains above: the contraction rule `γ^ν S x̸ γ_ν = -2 x̸ S - (γ^ν S γ_ν) x̸`, `γ^ν γ_ν = -d`,
then the trace recursion with `p·p = p'·p' = -m²`, and `c₂[f] = -2m² ∂f/∂(p·p')` at
`p·p' = -m²` (along `p'(u)`, `p·p' = -m²(1 + 2u² + O(u⁴))`); the trace values were also
compared with explicit Clifford matrices in `D = 6` and `D = 8`.
-/

@[expose] public section

namespace QED.DimReg.TwoLoopBridgeTrace

open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitLGraph QED.TwoLoop.Bridge

/-! ### The projector -/

/-- **Scheme (the `d`-dimensional Pauli projector, first coefficient).**
`A_d = 2m(4m² + q²)/(d - 2)`, the coefficient of `N(p) γ_μ N(p')`. -/
noncomputable def pauliProjA (d m Q : ℂ) : ℂ := 2 * m * (4 * m ^ 2 + Q) / (d - 2)

/-- **Scheme (the `d`-dimensional Pauli projector, second coefficient).**
`B_d = q² - 4m²/(d - 2)`, the coefficient of `(p' + p)_μ N(p) N(p')`. -/
noncomputable def pauliProjB (d m Q : ℂ) : ℂ := Q - 4 * m ^ 2 / (d - 2)

theorem pauliProjA_four (m Q : ℂ) : pauliProjA 4 m Q = m * (4 * m ^ 2 + Q) := by
  rw [pauliProjA, show (4 : ℂ) - 2 = 2 by norm_num]
  ring

theorem pauliProjB_four (m Q : ℂ) : pauliProjB 4 m Q = Q - 2 * m ^ 2 := by
  rw [pauliProjB, show (4 : ℂ) - 2 = 2 by norm_num]
  ring

/-- **The `d = 4` check (projector).** At `d = 4` the scheme projector is the model's Pauli
matrix `QED.TwoLoop.UnitLGraph.pauliMat`. -/
theorem pauliMat_eq_pauliProj (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    pauliMat m p' p μ =
      pauliProjA 4 m (QED.Minkowski.dot (p' - p) (p' - p)) •
          (electronNumerator m p * QED.Dirac.gammaLower μ * electronNumerator m p') +
        (pauliProjB 4 m (QED.Minkowski.dot (p' - p) (p' - p)) *
          ((QED.Minkowski.lower (p' + p) μ : ℝ) : ℂ)) •
          (electronNumerator m p * electronNumerator m p') := by
  rw [pauliProjA_four, pauliProjB_four, pauliMat]

/-- **Why `P^d` (`F₁` is annihilated in every dimension).** With the `d`-dimensional traces
`tr(N(p) γ_μ N(p') γ^μ) = 2((d - 2) q² - 4m²)` and `tr(N(p) N(p') (p̸ + p̸')) = -4m(q² + 4m²)`,
`tr(P^d_μ γ^μ) = 0` for `d ≠ 2`. -/
theorem pauliProj_annihilates_F₁ {d : ℂ} (hd : d ≠ 2) (m Q : ℂ) :
    pauliProjA d m Q * (2 * ((d - 2) * Q - 4 * m ^ 2)) +
      pauliProjB d m Q * (-4 * m * (Q + 4 * m ^ 2)) = 0 := by
  have : d - 2 ≠ 0 := sub_ne_zero.mpr hd
  simp only [pauliProjA, pauliProjB]
  field_simp
  ring

/-- **The normalization of `P^d`.** With `tr(N(p) (p̸ + p̸') N(p')) = -4m(q² + 4m²)` and
`(p + p')² tr(N(p) N(p')) = -2(q² + 4m²)²`, `tr(P^d_μ (p' + p)^μ)` is the model's value
`-2 q² (q² + 4m²)²` for every `d ≠ 2`: the `F₂` normalization does not depend on `d`. -/
theorem pauliProj_normalization {d : ℂ} (hd : d ≠ 2) (m Q : ℂ) :
    pauliProjA d m Q * (-4 * m * (Q + 4 * m ^ 2)) +
      pauliProjB d m Q * (-2 * (Q + 4 * m ^ 2) ^ 2) = -2 * Q * (Q + 4 * m ^ 2) ^ 2 := by
  have : d - 2 ≠ 0 := sub_ne_zero.mpr hd
  simp only [pauliProjA, pauliProjB]
  field_simp
  ring

/-! ### The crossed-ladder polynomials -/

/-- **Scheme (crossed ladder, `c₂[T₁]`).** The `d`-dimensional quartic `Ψ₁ᵈ`:
`c₂[xw(P^d; Ē)] = 512 Ψ₁ᵈ(α, β, 1)` at `m = 1`, as a polynomial in `ε = (4 - d)/2`,
homogeneous of degree `4` in the slot data `aₖ = αₖ`, `bₖ = βₖ` and `u = U`. Its `ε⁰` part is
the model's `QED.TwoLoop.UnitXGraph.psiT1h`. -/
noncomputable def psiT1d (d a0 a1 a2 a3 b0 b1 b2 b3 u : ℂ) : ℂ :=
  (2 * a0 * a1 * a2 * a3 - a0 * a1 * a2 * u - 2 * a0 * a1 * a3 * b2 + a0 * a1 * b2 * u -
    a0 * a1 * b3 * u - a0 * a1 * u ^ 2 + 2 * a0 * a2 * a3 * b1 - a0 * a2 * a3 * u -
    a0 * a2 * b1 * u + a0 * a2 * b3 * u + a0 * a3 * b1 * u - a0 * a3 * b2 * u - a0 * b1 * u ^ 2 +
    a0 * b2 * u ^ 2 + a1 * a2 * b0 * u - a1 * a2 * b3 * u - a1 * a2 * u ^ 2 - a1 * a3 * b0 * u +
    a1 * a3 * b2 * u + a1 * b0 * u ^ 2 - a1 * b2 * u ^ 2 + a1 * b3 * u ^ 2 + a2 * a3 * b0 * u -
    a2 * a3 * b1 * u - a2 * a3 * u ^ 2 - a2 * b0 * u ^ 2 + a2 * b1 * u ^ 2 - a2 * b3 * u ^ 2 +
    2 * a2 * u ^ 3 - a3 * b1 * u ^ 2 + a3 * b2 * u ^ 2 - a3 * u ^ 3 - b0 * u ^ 3 + 2 * b1 * u ^ 3 -
    2 * b2 * u ^ 3 + b3 * u ^ 3) + (4 - d) / 2 * (-2 * a0 * a1 * a2 * a3 - a0 * a1 * a2 * b3 +
    a0 * a1 * a2 * u + a0 * a1 * a3 * b2 - 2 * a0 * a1 * b2 * u + a0 * a1 * b3 * u +
    a0 * a1 * u ^ 2 - a0 * a2 * a3 * b1 - a0 * a2 * a3 * u + 2 * a0 * a2 * b1 * u -
    a0 * a2 * b3 * u + a0 * a2 * u ^ 2 - 3 * a0 * a3 * b1 * u + 3 * a0 * a3 * b2 * u -
    a0 * a3 * u ^ 2 + 2 * a0 * b1 * u ^ 2 - 2 * a0 * b2 * u ^ 2 + a0 * b3 * u ^ 2 + a0 * u ^ 3 +
    a1 * a2 * a3 * b0 + a1 * a2 * a3 * u - a1 * a2 * u ^ 2 + a1 * a3 * b0 * u -
    2 * a1 * a3 * b2 * u + a1 * a3 * u ^ 2 - 2 * a1 * b0 * u ^ 2 + 3 * a1 * b2 * u ^ 2 -
    2 * a1 * b3 * u ^ 2 - a1 * u ^ 3 - a2 * a3 * b0 * u + 2 * a2 * a3 * b1 * u + a2 * a3 * u ^ 2 +
    2 * a2 * b0 * u ^ 2 - 3 * a2 * b1 * u ^ 2 + 2 * a2 * b3 * u ^ 2 - 2 * a2 * u ^ 3 -
    a3 * b0 * u ^ 2 + 2 * a3 * b1 * u ^ 2 - 2 * a3 * b2 * u ^ 2 + a3 * u ^ 3 - b1 * u ^ 3 +
    b2 * u ^ 3) + ((4 - d) / 2) ^ 2 * (-a0 * a1 * a2 * b3 + a0 * a1 * a3 * b2 - a0 * a1 * b2 * u +
    a0 * a1 * b3 * u - a0 * a2 * a3 * b1 + a0 * a2 * a3 * u + a0 * a2 * b1 * u - a0 * a2 * b3 * u -
    a0 * a2 * u ^ 2 - a0 * a3 * b1 * u + a0 * a3 * b2 * u + a0 * a3 * u ^ 2 + a0 * b1 * u ^ 2 -
    a0 * b2 * u ^ 2 + a0 * b3 * u ^ 2 - a0 * u ^ 3 + a1 * a2 * a3 * b0 - a1 * a2 * a3 * u -
    a1 * a2 * b0 * u + a1 * a2 * b3 * u + a1 * a2 * u ^ 2 + a1 * a3 * b0 * u - a1 * a3 * b2 * u -
    a1 * a3 * u ^ 2 - a1 * b0 * u ^ 2 + a1 * b2 * u ^ 2 - a1 * b3 * u ^ 2 + a1 * u ^ 3 -
    a2 * a3 * b0 * u + a2 * a3 * b1 * u + a2 * b0 * u ^ 2 - a2 * b1 * u ^ 2 + a2 * b3 * u ^ 2 -
    a3 * b0 * u ^ 2 + a3 * b1 * u ^ 2 - a3 * b2 * u ^ 2 + b0 * u ^ 3 - b1 * u ^ 3 + b2 * u ^ 3 -
    b3 * u ^ 3)

/-- **Scheme (crossed ladder, `c₂[T₂]`).** The `d`-dimensional cubic `Ψ₂ᵈ`:
`c₂[Σ_{k<l} C_{kl} xw(P^d; Ē, slots k, l contracted)] = -1024 Ψ₂ᵈ(α, β, C, 1)` at `m = 1`, a
polynomial in `ε = (4 - d)/2`, linear in the contraction coefficients `C_{kl}` (`c01, …, c23`)
and homogeneous of degree `3` in the slot data, the `C_{kl}` and `u = U`. Its `ε⁰` part is the
model's `QED.TwoLoop.UnitXGraph.psiT2h`. -/
noncomputable def psiT2d (d a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u : ℂ) : ℂ :=
  c01 * ((a2 * a3 + a2 * b3 - 2 * a2 * u - a3 * b2 + a3 * u + 2 * b2 * u - b3 * u) + (4 - d) / 2 *
      (-2 * a2 * a3 - 3 * a2 * b3 + 4 * a2 * u + 3 * a3 * b2 - 2 * a3 * u - 3 * b2 * u + b3 * u) +
      ((4 - d) / 2) ^ 2 * (a2 * a3 + a2 * b3 - 2 * a2 * u - a3 * b2 + a3 * u + b3 * u) +
      ((4 - d) / 2) ^ 3 * (a2 * b3 - a3 * b2 + b2 * u - b3 * u)) +
    c02 * ((a1 * a3 - a1 * b3 - a1 * u + a3 * b1 - 2 * a3 * u + 2 * b3 * u) + (4 - d) / 2 *
      (-a1 * a3 + a1 * b3 + a1 * u - a3 * b1 + 2 * a3 * u + 3 * b1 * u - 2 * b3 * u) +
      ((4 - d) / 2) ^ 2 * (a1 * a3 - 3 * a1 * b3 - a1 * u + 3 * a3 * b1 - a3 * u - 2 * b1 * u) +
      ((4 - d) / 2) ^ 3 * (-a1 * a3 - a1 * b3 + a1 * u + a3 * b1 - b1 * u + b3 * u)) +
    c03 * ((4 * a1 * a2 - 4 * a1 * b2 - a1 * u + 4 * a2 * b1 - a2 * u) + (4 - d) / 2 *
      (-5 * a1 * a2 + a1 * b2 + 2 * a1 * u - a2 * b1 - 3 * a2 * u - 5 * b1 * u + 5 * b2 * u) +
      ((4 - d) / 2) ^ 2 * (6 * a1 * b2 - 6 * a2 * b1 + 3 * a2 * u + 3 * b1 * u - 3 * b2 * u) +
      ((4 - d) / 2) ^ 3 * (a1 * a2 + a1 * b2 - a1 * u - a2 * b1 + b1 * u - b2 * u)) +
    c12 * ((a3 * u + b0 * u - b3 * u) + (4 - d) / 2 * (a0 * a3 - a0 * b3 - a0 * u + a3 * b0 -
      2 * a3 * u - b0 * u + b3 * u) + ((4 - d) / 2) ^ 2 * (-2 * a0 * a3 + 2 * a0 * u + a3 * u -
      b0 * u + b3 * u) + ((4 - d) / 2) ^ 3 * (a0 * a3 + a0 * b3 - a0 * u - a3 * b0 + b0 * u -
      b3 * u)) +
    c13 * ((a0 * a2 - a0 * b2 + a2 * b0 - a2 * u - 2 * b0 * u) + (4 - d) / 2 * (-a0 * a2 + a0 * b2 -
      a2 * b0 + 4 * a2 * u + 2 * b0 * u - 3 * b2 * u) + ((4 - d) / 2) ^ 2 * (a0 * a2 - 3 * a0 * b2 -
      a0 * u + 3 * a2 * b0 - 3 * a2 * u + 2 * b2 * u) + ((4 - d) / 2) ^ 3 * (-a0 * a2 - a0 * b2 +
      a0 * u + a2 * b0 - b0 * u + b2 * u)) +
    c23 * ((a0 * a1 + a0 * b1 - a1 * b0 + b0 * u - 2 * b1 * u) + (4 - d) / 2 * (-2 * a0 * a1 -
      3 * a0 * b1 - a0 * u + 3 * a1 * b0 + a1 * u - b0 * u + 3 * b1 * u) + ((4 - d) / 2) ^ 2 *
      (a0 * a1 + a0 * b1 + 2 * a0 * u - a1 * b0 - 2 * a1 * u - b0 * u) + ((4 - d) / 2) ^ 3 *
      (a0 * b1 - a0 * u - a1 * b0 + a1 * u + b0 * u - b1 * u))

/-- **The `d = 4` check (`Ψ₁`).** At `d = 4` the scheme quartic is the model's
`QED.TwoLoop.UnitXGraph.psiT1h`. -/
theorem psiT1d_four (a0 a1 a2 a3 b0 b1 b2 b3 u : ℝ) :
    psiT1d 4 a0 a1 a2 a3 b0 b1 b2 b3 u = (psiT1h a0 a1 a2 a3 b0 b1 b2 b3 u : ℂ) := by
  simp only [psiT1d, psiT1h]
  push_cast
  ring

/-- **The `d = 4` check (`Ψ₂`).** At `d = 4` the scheme cubic is the model's
`QED.TwoLoop.UnitXGraph.psiT2h`. -/
theorem psiT2d_four (a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u : ℝ) :
    psiT2d 4 a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u =
      (psiT2h a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u : ℂ) := by
  simp only [psiT2d, psiT2h]
  push_cast
  ring

end QED.DimReg.TwoLoopBridgeTrace
