-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVertexChainLimit
public import QED.Frozen.VPChain.A1SixSetB
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Provider.VPChain.VertexChainTwoPauliLimit

@[expose] public section

open QED.WickModel (Params IsElectronOnShell IsPhotonOnShell)

namespace QED.VPChain

/-- (HC₃) **The sixth-order set (b) coefficient of the electron's anomalous magnetic moment, from
the chain vertex (Stage 1a headline goal; decisions D-37, D-49).** Fix the model data `P₀` with
`e ≠ 0` and `m > 0`. The model is packet T1's, with its electron and its two regulator fermions:
the flavours `![m, M₁, M₂]` with loop coefficients `![1, c₁, c₂]` and open line `0` are (X₀′),
(X₀″) (theorem (M₃): the values are T1's (T₁₀)). Its regulators `M₁, M₂, c₁, c₂, m_γ, Λ` and its
counterterms are replaced; its `ε` plays no role. The limits are taken in the order of D-37.4
and D-49.2: `ε → 0⁺` first; then `q² → 0⁺` at fixed regulators and counterterms, uniformly over
the on-shell pairs; then jointly `m_γ → 0⁺` and `Λ → ∞`; then `M₁, M₂ → ∞`, with `c₁, c₂` fixed
by the Pauli–Villars conditions and no constraint on `M₂ / M₁`. In quantifier form, as in (HV₃):
for every `η > 0` there is `R_M` such that for all regulator fermions heavier than the electron and
than `R_M` and satisfying the Pauli–Villars conditions there are `δ > 0` and `R`, which may depend
on them, such that for `0 < m_γ < δ` and `Λ > R` counterterms with the three conditions below
exist, and for every choice of counterterms with
* the electron on shell (Z₅),
* the charge condition (K₀) for the one-loop vertex function (J) with `Z₁ = 1 + δ₁`,
* the photon on shell (Z₈),

there is `q₀ > 0` such that at every on-shell positive-energy pair `(p', p)` with `0 < q² < q₀`:
* the chain vertex (C₃) with two insertions has an `ε → 0⁺` limit (C₄);
* every such limit has a form-factor pair (G₀), with the charge `e` factored out, and every such
  pair has its Pauli component within `η` of `A₁⁽⁶⁾(b) (α/π)³`, `α = e²/(4π)`:
  `|64 π⁶ F₂ / e⁶ - A₁⁽⁶⁾(b)| < η`, with `A₁⁽⁶⁾(b)` the constant (C₅).

The conditions are (HV₃)'s, unchanged: the counterterms are single real numbers of order `e²`
(D-37.3). The chain vertex reads only `δ₃` among them, which (Z₈) determines (Z₉); (Z₅) and (K₀)
are kept so that the statement has (HV₃)'s hypotheses and can be added to it. By homogeneity
(obligation O3-7; `δ₃` is `e²` times a number independent of `e` when `e ≠ 0`) the vertex is `e⁷`
times a matrix independent of `e`, so `F₂ / e⁶` is the coefficient `[e⁶] F₂`. The headline concerns
one gauge-invariant set of the 72 sixth-order diagrams (Q8), on the 1PI vertex (D-37.6). The chain
family is infrared finite; the order of limits is kept for uniformity with (HV₃) and (HM₂). -/
theorem isFormFactorPair_vertexChain_two_pauli_limit (P₀ : Params) (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂), RM < M₁ → RM < M₂ →
      ∀ (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0),
      ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
        (∃ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ ∧
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ ∧
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂) ∧
        ∀ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ →
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ →
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂ →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V) ∧
            ∀ V, IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetB : ℂ)‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.VPChain

end
-- FROZEN_ANCHOR_SUFFIX_END
