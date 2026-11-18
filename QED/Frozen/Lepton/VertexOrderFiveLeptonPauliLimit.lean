-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.IsVertexOrderFiveLimit
public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.Lepton.A2Four
public import QED.Frozen.TwoLoop.A1Four
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Provider.Lepton.VertexOrderFiveLeptonPauliLimit

@[expose] public section

open QED.WickModel (Params IsElectronOnShell)

namespace QED.Lepton

/-- (HM₂) **The fourth-order coefficient of the electron's anomalous magnetic moment with heavy
leptons, from the order-`e⁵` 1PI vertex (Stage 0 headline goal; decisions D-36.2, D-37, D-49).**
Fix the model data `P₀` with `e ≠ 0` and electron mass `m = P₀.m > 0`, and `n` heavy leptons with
masses `m_ℓ > m` (`mH`). Each lepton, the electron included, has its own pair of regulator
fermions satisfying the Pauli–Villars conditions with that lepton's mass (D-49.4): the
electron's are T1's fields `M₁, M₂, c₁, c₂` of `Params`, the heavy lepton `ℓ`'s are
`MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ`; the model is the flavoured Wick model (F₈) with the flavours
(L₁). The regulators, the photon regulators `m_γ, Λ` and the counterterms of `P₀` are replaced;
its `ε` plays no role. The limits are taken in the order of D-37.4 and D-49.2: `ε → 0⁺` first;
then `q² → 0⁺` at fixed regulators and counterterms, uniformly over the on-shell pairs; then
jointly `m_γ → 0⁺` and `Λ → ∞`; then all regulator-fermion masses `→ ∞`, with a single threshold
`R_M` for the regulator pairs of every lepton, no constraint on the ratios of the regulator
masses, and the coefficients fixed by the Pauli–Villars conditions. In quantifier form, as in
(HV₃): for every `η > 0` there is `R_M` such that for all regulator fermions of the electron and of
every heavy lepton that are heavier than their lepton and than `R_M` and satisfy the
Pauli–Villars conditions, there are `δ > 0` and `R`, which may depend on them, such that for
`0 < m_γ < δ` and `Λ > R` counterterms with the three conditions below exist, and for every choice
of counterterms with
* the electron on shell (Z₅) (T1's; it does not see the flavours, (E₅)),
* the charge condition (K₀) for the one-loop vertex function (J) with `Z₁ = 1 + δ₁`,
* the photon on shell (F₁₁), `Π(0) = 0` for the vacuum polarization summed over all flavours,
there is `q₀ > 0` such that at every on-shell positive-energy pair `(p', p)` with
`0 < q² < q₀`:
* the order-`e⁵` vertex (F₉) has an `ε → 0⁺` limit (F₁₀);
* every such limit has a form-factor pair (G₀), and every such pair has
  `|16 π⁴ F₂ / e⁴ - (A₁⁽⁴⁾ + ∑_ℓ A₂⁽⁴⁾(m/m_ℓ))| < η`, with `A₁⁽⁴⁾` the constant (U₁) and `A₂⁽⁴⁾`
  the function (U₃). With the muon and the tau this is Passera (13),
  `C_e⁽⁴⁾ = A₁⁽⁴⁾ + A₂⁽⁴⁾(m_e/m_μ) + A₂⁽⁴⁾(m_e/m_τ)`.
With `n = 0` the statement is (HV₃), by (E₃′), (E₄) and `∑_∅ = 0`. As in (HV₃), the counterterms
are single real numbers (D-37.3) and `F₂ / e⁴` is the coefficient `[e⁴] F₂` by homogeneity
(O2-27, which carries over since (Z₅), (K₀) are T1's and (F₁₁) is affine in `δ₃`). -/
theorem isFormFactorPair_vertexOrderFive_lepton_pauli_limit {n : ℕ} (P₀ : Params)
    (mH : Fin n → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ) (η : ℝ)
    (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
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
              δm := dm, δ₃ := d₃ }
            (leptonFlavors
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩)) ∧
        ∀ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ →
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ →
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ }
            (leptonFlavors
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              (leptonFlavors
                { P₀ with
                  M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                  δm := dm, δ₃ := d₃ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) p' p V) ∧
            ∀ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              (leptonFlavors
                { P₀ with
                  M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                  δm := dm, δ₃ := d₃ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 -
                  ((QED.TwoLoop.a1Four + ∑ ℓ, a2Four (P₀.m / mH ℓ) : ℝ) : ℂ)‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
