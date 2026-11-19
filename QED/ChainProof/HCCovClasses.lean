/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCCovConj

/-!
# The set (b) headline with the mirror obligation discharged

Helper level, Phase 5 Stage 1a. With the mirror link proved from existence and covariance
(`QED.ChainProof.Conj.chainMirrorLink_of_exists_cov`, `QED/ChainProof/HCCovConj.lean`), the
reduction of (HC₃) in `QED/ChainProof/HCClasses.lean` needs one obligation fewer.

* `isFormFactorPair_vertexChain_two_pauli_limit_of_classes_cov`: (HC₃) from any class
  decomposition `X` (O3-4), the per-class limits (O3-5/O3-6) and their covariance (O3-8), and the
  Pauli link (O3-9).
* `chainClassX`: the nine class vertices of the landed enumeration (`QED/ChainProof/Enum*.lean`),
  `(1/i)` times the signed value (F₇) of each representative, at T1's flavours;
  `chainClassDecomposition`: they decompose the chain vertex at every `ε` and all momenta
  (`QED.ChainProof.Enum.vertexChain_two_eq_classes_flavors`).
* `isFormFactorPair_vertexChain_two_pauli_limit_of_classLinks`: (HC₃) from
  `ClassLimitLink chainClassX`, `ClassCovLink chainClassX` and `ChainPauliAtLink`.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction IsElectronOnShell IsPhotonOnShell)

namespace QED.ChainProof

open QED.ChainProof.Enum

section Classes

variable {ι : Type*} [Fintype ι]
  {X : ι → Params → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}

/-- **The set (b) headline (HC₃) from a class decomposition, the per-class limits and their
covariance, and the Pauli link.** The conclusion is, verbatim, the proposition of the frozen
`QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`. -/
theorem isFormFactorPair_vertexChain_two_pauli_limit_of_classes_cov
    (hD : ChainClassDecomposition X) (hL : ClassLimitLink X) (hC : ClassCovLink X)
    (hPA : ChainPauliAtLink)
    (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
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
            (∃ V, QED.VPChain.IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V) ∧
            ∀ V, QED.VPChain.IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (QED.VPChain.a1SixSetB : ℂ)‖ < η :=
  isFormFactorPair_vertexChain_two_pauli_limit_of_classes hD hL hC
    (Conj.chainMirrorLink_of_exists_cov (chainExistsLink_of_classes hD hL)
      (chainCovLink_of_classes hD hL hC)) hPA P₀ he hm η hη

end Classes

/-- **The class vertices of set (b)** (the landed enumeration O3-4): `(1/i)` times the value (F₇)
at T1's flavours of the representative of class `r`, with its fermionic sign, in the order
`BB, BD₀, BD₁, DB₀, DB₁, DD₀₀, DD₀₁, DD₁₀, DD₁₁` of
`QED.ChainProof.Enum.vertexChain_two_eq_classes_flavors`. -/
noncomputable def chainClassX (r : Fin 9) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β =>
    let V := fun {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) =>
      QED.Lepton.contractionValue₂ P (chainFlavors P) C (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)
    (1 / I) * ![V repBB, -V (repBD 0), -V (repBD 1), -V (repDB 0), -V (repDB 1), V (repDD 0 0),
      V (repDD 0 1), V (repDD 1 0), V (repDD 1 1)] r

/-- The chain vertex is the sum of the nine class vertices, at every parameter set and all
momenta. -/
theorem vertexChain_two_eq_sum_chainClassX (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    QED.VPChain.vertexChain 2 P (chainFlavors P) p' p μ = ∑ r, chainClassX r P p' p μ := by
  rw [vertexChain_two_eq_classes_flavors]
  ext α β
  simp only [Matrix.of_apply, Matrix.sum_apply, chainClassX, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

/-- **The class decomposition** `ChainClassDecomposition chainClassX`. -/
theorem chainClassDecomposition : ChainClassDecomposition chainClassX :=
  fun P _ ε _ p' p _ μ => vertexChain_two_eq_sum_chainClassX { P with ε := ε } p' p μ

/-- **The set (b) headline (HC₃) from the per-class limits and covariance of the nine landed
classes, and the Pauli link.** The conclusion is, verbatim, the proposition of the frozen
`QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`. -/
theorem isFormFactorPair_vertexChain_two_pauli_limit_of_classLinks
    (hL : ClassLimitLink chainClassX) (hC : ClassCovLink chainClassX) (hPA : ChainPauliAtLink)
    (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
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
            (∃ V, QED.VPChain.IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V) ∧
            ∀ V, QED.VPChain.IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (QED.VPChain.a1SixSetB : ℂ)‖ < η :=
  isFormFactorPair_vertexChain_two_pauli_limit_of_classes_cov chainClassDecomposition hL hC hPA
    P₀ he hm η hη

end QED.ChainProof

end
