/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCLinks

/-!
# Existence and covariance of the chain limits from a class decomposition

Helper level, Phase 5 Stage 1a. This file is the place where the class decomposition of set (b)
(obligation O3-4, owned elsewhere: `QED/ChainProof/Enum*`, not imported) enters the proof of the
headline, as an explicit hypothesis.

* `ChainClassDecomposition X`: at admissible parameters, every `ε > 0` and every pair, the chain
  vertex with two insertions is the finite sum `∑_r X r` of class vertices. The intended `X r` is
  `(1/i)` times the fermionic sign times the value (T₁₀) of the representative of class `r` (the
  nine classes of set (b) with its `δ₃` partners, coefficient one each), but nothing here depends
  on that choice.
* `ClassLimitLink X` (O3-6 per class): each class vertex has an `ε → 0⁺` limit at every
  admissible pair.
* `ClassCovLink X` (O3-8 per class): the class limits are covariant under every spinor-lifted `L`
  that keeps positive energies.

Proved: `chainExistsLink_of_classes` and `chainCovLink_of_classes`, the links `ChainExistsLink`
and `ChainCovLink` of `QED/ChainProof/HCLinks.lean`; the limit of the chain vertex is the sum of
the class limits (`chainLim_eq_sum`); and the exact proposition of (HC₃) from the decomposition,
the two per-class links, the mirror link and the Pauli link
(`isFormFactorPair_vertexChain_two_pauli_limit_of_classes`).
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real
open QED.WickModel (Params IsElectronOnShell IsPhotonOnShell)

namespace QED.ChainProof

open QED.TwoLoop.LimitCovariance

variable {ι : Type*} [Fintype ι]
  (X : ι → Params → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

/-- **The class decomposition** (the form in which O3-4 is used): at admissible parameters, for
every `ε > 0` and every pair, the chain vertex is the sum of the class vertices. -/
def ChainClassDecomposition : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ ε : ℝ, 0 < ε → ∀ p' p, IsPairQ P.m p' p → ∀ μ,
    QED.VPChain.vertexChain 2 { P with ε := ε } (chainFlavors P) p' p μ =
      ∑ r, X r { P with ε := ε } p' p μ

/-- `Y` is the `ε → 0⁺` limit of the class vertex `X r`, entrywise. -/
def IsClassLimit (r : ι) (P : Params) (p' p : Fin 4 → ℝ) (Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    Prop :=
  ∀ μ i j, Tendsto (fun ε => X r { P with ε := ε } p' p μ i j) (𝓝[>] 0) (𝓝 (Y μ i j))

/-- **O3-6 per class**: every class vertex has an `ε → 0⁺` limit at every admissible pair. -/
def ClassLimitLink : Prop :=
  ∀ r P, ChainAdmissible P → ∀ p' p, IsPairQ P.m p' p → ∃ Y, IsClassLimit X r P p' p Y

/-- **O3-8 per class**: the class limits are covariant under every spinor-lifted `L` that keeps
positive energies. -/
def ClassCovLink : Prop :=
  ∀ r P, ChainAdmissible P →
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ P.m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ Y Z, IsClassLimit X r P p' p Y → IsClassLimit X r P (L *ᵥ p') (L *ᵥ p) Z →
      ∀ μ, S * Z μ * T = QED.Dirac.vecAct L Y μ

variable {X}

/-- With the decomposition, the sum of class limits is a limit of the chain vertex. -/
theorem chainLim_sum (hD : ChainClassDecomposition X) {P : Params} (hA : ChainAdmissible P)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p) {Y : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ r, IsClassLimit X r P p' p (Y r)) : chainLim P p' p (∑ r, Y r) := by
  intro μ i j
  have hsum : Tendsto (fun ε => ∑ r, X r { P with ε := ε } p' p μ i j) (𝓝[>] 0)
      (𝓝 (∑ r, Y r μ i j)) := tendsto_finsetSum _ fun r _ => hY r μ i j
  have hev : (fun ε => ∑ r, X r { P with ε := ε } p' p μ i j) =ᶠ[𝓝[>] 0]
      fun ε => QED.VPChain.vertexChain 2 { P with ε := ε } (chainFlavors P) p' p μ i j := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hD P hA ε hε p' p hpq μ, Matrix.sum_apply]
  have hgoal := hsum.congr' hev
  simpa [Finset.sum_apply, Matrix.sum_apply] using hgoal

/-- **The limit of the chain vertex is the sum of the class limits.** -/
theorem chainLim_eq_sum (hD : ChainClassDecomposition X) {P : Params} (hA : ChainAdmissible P)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p) {Y : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ r, IsClassLimit X r P p' p (Y r)) {V} (hV : chainLim P p' p V) : V = ∑ r, Y r :=
  isVertexChainLimit_unique hV (chainLim_sum hD hA hpq hY)

/-- **Existence of the chain limits from the classes.** -/
theorem chainExistsLink_of_classes (hD : ChainClassDecomposition X) (hL : ClassLimitLink X) :
    ChainExistsLink := by
  intro P hA p' p hpq
  choose Y hY using fun r => hL r P hA p' p hpq
  exact ⟨∑ r, Y r, chainLim_sum hD hA hpq hY⟩

/-- A spinor-lifted map keeps the pairs with `q² > 0` when it keeps positive energies. -/
theorem isPairQ_map {m : ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) {p' p : Fin 4 → ℝ} (hpq : IsPairQ m p' p) (h0 : 0 < (L *ᵥ p') 0)
    (h1 : 0 < (L *ᵥ p) 0) : IsPairQ m (L *ᵥ p') (L *ᵥ p) := by
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  refine ⟨by rw [h.dot_mulVec]; exact hp', by rw [h.dot_mulVec]; exact hp, h0, h1, ?_⟩
  rw [← Matrix.mulVec_sub, h.dot_mulVec]
  exact hq

/-- `vecAct L` commutes with finite sums. -/
theorem vecAct_sum (L : Matrix (Fin 4) (Fin 4) ℝ) (Y : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : QED.Dirac.vecAct L (∑ r, Y r) μ = ∑ r, QED.Dirac.vecAct L (Y r) μ := by
  simp only [QED.Dirac.vecAct, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

/-- **Covariance of the chain limits from the classes.** -/
theorem chainCovLink_of_classes (hD : ChainClassDecomposition X) (hL : ClassLimitLink X)
    (hC : ClassCovLink X) : ChainCovLink := by
  intro P hA L S T h p' p hpq h0 h1 V W hV hW μ
  have hpq' := isPairQ_map h hpq h0 h1
  choose Y hY using fun r => hL r P hA p' p hpq
  choose Z hZ using fun r => hL r P hA _ _ hpq'
  rw [chainLim_eq_sum hD hA hpq hY hV, chainLim_eq_sum hD hA hpq' hZ hW, vecAct_sum,
    Finset.sum_apply, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun r _ =>
    hC r P hA L S T h p' p hpq h0 h1 (Y r) (Z r) (hY r) (hZ r) μ

/-- **The set (b) headline (HC₃) from the class decomposition (O3-4) and the per-class and
whole-vertex obligations.** The conclusion is, verbatim, the proposition of the frozen
`QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`. -/
theorem isFormFactorPair_vertexChain_two_pauli_limit_of_classes (hD : ChainClassDecomposition X)
    (hL : ClassLimitLink X) (hC : ClassCovLink X) (hM : ChainMirrorLink) (hPA : ChainPauliAtLink)
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
  isFormFactorPair_vertexChain_two_pauli_limit_of_obligations (chainExistsLink_of_classes hD hL)
    (chainCovLink_of_classes hD hL hC) hM hPA P₀ he hm η hη

end QED.ChainProof

end
