-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsLSZFormFactorPair
public import QED.Frozen.WickModel.LszAmplitude
public import QED.Frozen.WickModel.IsLSZChargeNormalized
public import QED.Frozen.WickModel.IsLSZResponseMagneticMoment
public import QED.Frozen.WickModel.LszSourceMagneticMoment
public import QED.Frozen.Algebra.LorentzGen
public import QED.Frozen.Algebra.Lower
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
public import QED.Provider.WickModel.LszAmplitudePauliLandeFactorLimit

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- (H) **The one-loop anomalous magnetic moment of the electron, from the model's own LSZ
amplitude (headline theorem; decisions D-21, D-32).** Fix the model data `P₀` with `e ≠ 0`,
`m > 0`, and regulator fermions heavier than the electron satisfying the Pauli–Villars
conditions. The photon regulators `m_γ`, `Λ` and the counterterms `δ₁`, `δ₂`, `δ_m` of `P₀` are
replaced; its `ε` plays no role, and its `δ₃` is arbitrary: no photon on-shell condition (Z₈) is
assumed. Fix a wave-packet profile `φ` as in (W₄) and (L₇′). Then, jointly as `m_γ → 0⁺` and
`Λ → ∞`:
* counterterms exist with the electron on shell (Z₅), the LSZ charge condition (L₄) holding, and
  an LSZ response magnetic moment (L₅);
* for every such choice of counterterms: at on-shell positive-energy pairs with small `q² > 0`,
  the LSZ amplitude has a form-factor pair (H₀), and every such pair has its Pauli component
  within `η` of `e²/(8π²) = α/(2π)` ((63.22), (64.2)); every LSZ response magnetic moment gives
  a Landé factor `g = 4 m μ / e` within `η` of `2 (1 + α/(2π))` (64.16)–(64.17); and the LSZ
  source magnetic moment (L₇) of every sufficiently narrow packet does too.
The model is truncated at order `e³`, so the limits are exact for it, with no `O(α²)` term. As in
(I), `q² → 0⁺` is taken jointly with the regulator limit and uniformly over the pairs (one `δ`
bounds both `q²` and `m_γ`); this implies the iterated order of decision D-5. As in (R′), the
response definition (L₅) takes `q → 0⁺` at fixed regulators. As in (W₅), the packet limit
`λ → 0⁺` is taken first, at fixed regulators and counterterms (decision D-17). -/
theorem lszAmplitude_pauli_landeFactor_limit (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hM₁ : P₀.m < P₀.M₁) (hM₂ : P₀.m < P₀.M₂) (hPV₁ : 1 + P₀.c₁ + P₀.c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + P₀.c₁ * P₀.M₁ ^ 2 + P₀.c₂ * P₀.M₂ ^ 2 = 0)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      (∃ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
        IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon ∧
        ∃ μ : ℝ, IsLSZResponseMagneticMoment
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ) ∧
      ∀ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
        IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon →
        (∀ (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
            (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
          0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
          (∃ F : ℂ × ℂ, IsLSZFormFactorPair
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F) ∧
          ∀ F : ℂ × ℂ, IsLSZFormFactorPair
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F →
            ‖F.2 - ((P₀.e ^ 2 / (8 * Real.pi ^ 2) : ℝ) : ℂ)‖ < η) ∧
        (∀ μ : ℝ, IsLSZResponseMagneticMoment
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ →
          |4 * P₀.m * μ / P₀.e - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))| < η) ∧
        ∃ lam₀ > 0, ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ‖4 * (P₀.m : ℂ) * lszSourceMagneticMoment
              { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
              hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam / P₀.e
            - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.lszAmplitude_pauli_landeFactor_limit
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
