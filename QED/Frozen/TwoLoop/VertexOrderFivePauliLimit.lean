-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.IsVertexOrderFiveLimit
public import QED.Frozen.TwoLoop.A1Four
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Provider.TwoLoop.VertexOrderFivePauliLimit

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params onePIFunction₂ IsElectronOnShell IsPhotonOnShell)

namespace QED.TwoLoop

/-- (HV₃) **The fourth-order mass-independent coefficient of the electron's anomalous magnetic
moment, from the order-`e⁵` 1PI vertex (packet T3 headline goal; decisions D-36.2, D-37.1,
D-37.3, D-37.4, D-37.6).** Fix the model data `P₀` with `e ≠ 0` and `m > 0`. Its regulators
`M₁, M₂, c₁, c₂, m_γ, Λ` and its counterterms `δ₁, δ₂, δ_m, δ₃` are replaced; its `ε` plays no
role: the vertex (HV₁) enters only through its limit (HV₂), and the conditions (Z₅), (Z₈) do not
depend on it. The limits are taken in the order
of decision D-37.4, which refines D-5: `ε → 0⁺` first, at fixed everything else; then `q² → 0⁺`
at fixed regulators and counterterms, uniformly over the on-shell pairs; then jointly `m_γ → 0⁺`
and `Λ → ∞` at fixed regulator-fermion masses; then `M₁, M₂ → ∞`, with `c₁, c₂` fixed by the
Pauli–Villars conditions and no constraint on `M₂ / M₁`. In quantifier form (D-37.1 read with
D-37.4; `docs/TWO-LOOP-DERIVATION.md`, section 5.6): for every
`η > 0` there is `R_M` such that for all regulator fermions heavier than the electron and than
`R_M` and satisfying the Pauli–Villars conditions there are `δ > 0` and `R`, which may depend on
them, such that for `0 < m_γ < δ` and `Λ > R` counterterms (single real numbers, D-37.3) with the
three conditions below exist, and for every choice of counterterms with
* the electron on shell (Z₅),
* the charge condition (K₀) for the one-loop vertex function (J) with `Z₁ = 1 + δ₁`, as in (L₄′),
* the photon on shell (Z₈),

there is `q₀ > 0`, which may depend on all of these, such that at every on-shell positive-energy
pair `(p', p)` with `0 < q² < q₀`, `q = p' - p`:
* the order-`e⁵` vertex (HV₁) has an `ε → 0⁺` limit (HV₂);
* every such limit has a form-factor pair (G₀), with the charge `e` factored out, and every such
  pair has its Pauli component within `η` of `A₁⁽⁴⁾ (α/π)²`, `α = e²/(4π)`:
  `|16 π⁴ F₂ / e⁴ - A₁⁽⁴⁾| < η`, with `A₁⁽⁴⁾` the constant (U₁).

The conditions (Z₅), (K₀), (Z₈) are the order-`e²` conditions of the frozen one-loop model,
unchanged (the counterterms are single real numbers and the expansion is truncated, D-37.3). They
determine the counterterms uniquely ((K), (Z₉), (Z₆)). By homogeneity in `e` (obligation O2-27,
items 1–2, proved in `QED/TwoLoop/CountertermScaling.lean`; it uses `e ≠ 0`) they are `e²` times
numbers independent of `e`, so the vertex (HV₁) is `e⁵` times a matrix independent of `e` and
`F₂ / e⁴` is the coefficient `[e⁴] F₂`, not a limit in `e`. The headline is stated on the 1PI
vertex (D-37.6); an LSZ restatement can follow. The joint limit in `q²` and `m_γ` of the one-loop
headlines (I) and (H) does not exist at this order: for `q² ≠ 0` the order-`e⁴` Pauli form factor
carries an infrared logarithm `∼ q² ln m_γ` (BMR-I p. 834; `docs/TWO-LOOP-DERIVATION.md`,
section 5.6), so `q₀` depends on the regulators. -/
theorem isFormFactorPair_vertexOrderFive_pauli_limit (P₀ : Params) (he : P₀.e ≠ 0)
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
            (∃ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ } p' p V) ∧
            ∀ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ } p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 - (a1Four : ℂ)‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.TwoLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
