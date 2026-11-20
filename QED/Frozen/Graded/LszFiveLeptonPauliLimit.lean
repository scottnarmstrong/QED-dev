-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.IsLSZAmplitudePart
public import QED.Frozen.Graded.IsSpinFormFactorPair
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.TwoLoop.A1Four
public import QED.Frozen.Lepton.A2Four
public import QED.Provider.Graded.LszFiveLeptonPauliLimit

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (X₂) **Exit test, magnetic moment: the two-loop LSZ lift of (HV₃) and (HM₂)** (ruling S8;
decision D-44.1; Passera (13)). (HM₂)'s binders, quantifier order and target, with the 1PI
vertex replaced by the order-`e⁵` LSZ amplitude (G-L₁) of the graded model, and the conditions
(Z₅), (K₀), (F₁₁) replaced by "renormalized through order `e⁴`" (G₁₂) in the per-lepton scheme
`leptonRep`: for every `η > 0` there is `R_M` such that for all regulator fermions of the electron
and of every heavy lepton that are heavier than their lepton and than `R_M` and satisfy the
Pauli–Villars conditions, there are `δ > 0` and `R` such that for `0 < m_γ < δ` and `Λ > R`
renormalized counterterms exist, and for every choice of them there is `q₀ > 0` such that at
every on-shell positive-energy pair with `0 < q² < q₀` the order-`5` LSZ amplitude exists, has a
form-factor pair (G-L₂), and every such pair has
`|16 π⁴ F₂ / e⁴ - (A₁⁽⁴⁾ + ∑_ℓ A₂⁽⁴⁾(m/m_ℓ))| < η`. The photon-leg terms carry the factor
`q² D(q²)` of the free photon propagator times the inserted bubble; at fixed regulators
(`m_γ > 0`) `q² D(q²) → 0` as `q² → 0`, which is taken first, so they do not reach `F₂` in the
limit (the pure tree-times-bubble terms are proportional to `γ^μ` and shift only `F₁` anyway); the
leg corrections vanish by the on-shell conditions through order `e⁴`. -/
theorem isSpinFormFactorPair_lszFive_lepton_pauli_limit {n : ℕ} (P₀ : Params)
    (mH : Fin n → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ) (η : ℝ)
    (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
          IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2) ∧
        ∀ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
          IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2 →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ M, IsLSZAmplitudePart
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 5 p' p M) ∧
            ∀ M, IsLSZAmplitudePart
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 5 p' p M →
              (∃ F : ℂ × ℂ, IsSpinFormFactorPair P₀.e P₀.m p' p M F) ∧
              ∀ F : ℂ × ℂ, IsSpinFormFactorPair P₀.e P₀.m p' p M F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 -
                  ((QED.TwoLoop.a1Four + ∑ ℓ, Lepton.a2Four (P₀.m / mH ℓ) : ℝ) : ℂ)‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
