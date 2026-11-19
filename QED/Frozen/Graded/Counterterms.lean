/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace QED.Graded

/-- (G₀) **Graded counterterm coefficients** (rulings S2′ (D-55 revised) and S3 of the Stage 2 memo,
provisional; successor of D-37.3 for the graded model; plan Q5 (ii)). Srednicki's counterterms
(62.2)–(62.3), expanded in the charge: `Z₁ - 1 = ∑_{k ≥ 0} e^{2(k+1)} d₁ f k`, and likewise `Z₂ - 1`
with `d₂`, `Z_m - 1` with `dm`, and `Z₃ - 1 = ∑_k e^{2(k+1)} d₃ k`. Level `k` is the coefficient of
`e^{2(k+1)}`, so level `0` is the one-loop (order `e²`) counterterm and level `1` the two-loop
(order `e⁴`) one. The coefficients `d` do not contain `e` (ruling S3): the order of a term is read
off its vertices, and the separation by order is definitional. The fermion counterterms are given
per flavour `f` (the counterterm Lagrangian has `Ψ̄_f ⋯ Ψ_f` terms for every flavour; B4 check); the
photon counterterm is flavour-independent. These are data: the conditions fixing them are
(G₉)–(G₁₂). The per-flavour storage is constrained by the scheme map `rep` of (G₁₂): under S2′
(`leptonRep`, (G₁₂′)) a regulator fermion carries its lepton's `d₁, d₂, d_m`, and its mass
counterterm vertex reads `d_m · M_f` with its own mass `M_f` (G₃). -/
structure Counterterms (F : Type) where
  /-- The vertex counterterm `Z₁ - 1` of flavour `f`, coefficient of `e^{2(k+1)}`. -/
  d₁ : F → ℕ → ℝ
  /-- The field counterterm `Z₂ - 1` of flavour `f`, coefficient of `e^{2(k+1)}`. -/
  d₂ : F → ℕ → ℝ
  /-- The mass counterterm `Z_m - 1` of flavour `f`, coefficient of `e^{2(k+1)}`; the vertex
  factor (V₁₉) multiplies it by the mass of flavour `f`. -/
  dm : F → ℕ → ℝ
  /-- The photon counterterm `Z₃ - 1`, coefficient of `e^{2(k+1)}`. -/
  d₃ : ℕ → ℝ

end QED.Graded

end
