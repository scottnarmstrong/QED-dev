/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCAssembly
public import QED.ChainProof.HCKinematics
import Mathlib.Tactic.Linarith

/-!
# The set (b) headline from four fixed-regulator obligations

Helper level, Phase 5 Stage 1a. The fixed link `QED.ChainProof.ChainFixedLink` of
`QED/ChainProof/HCLink.lean` is split into four statements about the `ε → 0⁺` limits of the chain
vertex with two insertions at T1's flavours (`chainLim P`), at admissible parameters
(`ChainAdmissible`) and on-shell positive-energy pairs with `q² > 0` (`IsPairQ`):

* `ChainExistsLink` (O3-5, O3-6 at `ε → 0⁺`): the limit exists;
* `ChainCovLink` (O3-8, covariance): `S W^μ T = L^μ_ν V^ν` for every spinor-lifted `L` that keeps
  positive energies;
* `ChainMirrorLink` (O3-8, no `q^μ` term): every limit is mirror symmetric;
* `ChainPauliAtLink` (O3-9 with O3-6, O3-7, O3-10): the Pauli projection at the canonical pair
  with `q² = Q` tends to `e⁶ chainRegMass/(64π⁶)` as `Q → 0⁺`.

Proved here:
* `isVertexChainLimit_unique`: limits are unique (the filter `𝓝[>] 0` is nontrivial);
* `covFamily_chainLim`: with the first two links, the limits form a covariant family
  (`QED/ChainProof/HCKinematics.lean`), so the Pauli projection depends only on `q²` and the
  uniform `q² → 0⁺` statement is equivalent to the one-variable limit;
* `chainLimitLink_of`, `chainPauliLink_of`: the two links of `QED/ChainProof/HCLink.lean`;
* `chainPauliAtLink_of_chainPauliLink`: the one-variable limit is also necessary;
* **`isFormFactorPair_vertexChain_two_pauli_limit_of_obligations`**: the exact proposition of
  (HC₃) from the four links.

The four links are **not** proved. The class decomposition (O3-4) and the three-loop
integrability (HC₀) enter only through them.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real
open QED.WickModel (Params IsElectronOnShell IsPhotonOnShell)

namespace QED.ChainProof

open QED.TwoLoop.LimitCovariance

/-- The `ε → 0⁺` limits of the chain vertex with two insertions at T1's flavours. -/
def chainLim (P : Params) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  QED.VPChain.IsVertexChainLimit 2 P (chainFlavors P) p' p V

/-- **Limits are unique.** -/
theorem isVertexChainLimit_unique {n : ℕ} {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : QED.Lepton.Flavors F} {p' p : Fin 4 → ℝ} {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : QED.VPChain.IsVertexChainLimit n P Φ p' p V)
    (hW : QED.VPChain.IsVertexChainLimit n P Φ p' p W) : V = W := by
  funext μ
  ext i j
  exact tendsto_nhds_unique (hV μ i j) (hW μ i j)

/-- **O3-5, O3-6 at the `ε → 0⁺` level**: the limit exists. -/
def ChainExistsLink : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ p' p, IsPairQ P.m p' p → ∃ V, chainLim P p' p V

/-- **O3-8, covariance**: for every real `L` with a spinor lift `(S, T)` that keeps positive
energies, the limits `V` at `(p', p)` and `W` at `(L p', L p)` satisfy `S W^μ T = L^μ_ν V^ν`. -/
def ChainCovLink : Prop :=
  ∀ P : Params, ChainAdmissible P →
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ P.m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ V W, chainLim P p' p V → chainLim P (L *ᵥ p') (L *ᵥ p) W →
      ∀ μ, S * W μ * T = QED.Dirac.vecAct L V μ

/-- **O3-8, no `q^μ` term**: every limit is mirror symmetric (charge conjugation). -/
def ChainMirrorLink : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ p' p, IsPairQ P.m p' p →
    ∀ V, chainLim P p' p V → QED.OneLoop.IsMirrorSymmetric p' p V

/-- **O3-9 with the value (O3-6, O3-7, O3-10)**: the Pauli projection of the limit at the
canonical pair with `q² = Q` tends to `e⁶ chainRegMass m m_γ Λ M₁ M₂/(64π⁶)` as `Q → 0⁺`. -/
def ChainPauliAtLink : Prop :=
  ∀ P : Params, ChainAdmissible P →
    Tendsto (CovFamily.pauliAtCanonical (chainLim P) P.e P.m) (𝓝[>] 0)
      (𝓝 ((P.e : ℂ) ^ 6 * (chainRegMass P.m P.mγ P.Λ P.M₁ P.M₂ : ℂ) / (64 * (π : ℂ) ^ 6)))

/-- With existence and covariance, the chain limits form a covariant family. -/
theorem covFamily_chainLim (hE : ChainExistsLink) (hC : ChainCovLink) {P : Params}
    (hA : ChainAdmissible P) : CovFamily P.m (chainLim P) where
  pos := hA.hm
  exists' := hE P hA
  unique := fun _ _ _ _ _ hV hW => isVertexChainLimit_unique hV hW
  cov := hC P hA

/-- **The limit link** from existence, covariance and mirror symmetry. -/
theorem chainLimitLink_of (hE : ChainExistsLink) (hC : ChainCovLink) (hM : ChainMirrorLink) :
    ChainLimitLink := by
  intro P hA p' p hp' hp hp0' hp0 hq
  have hpq : IsPairQ P.m p' p := ⟨hp', hp, hp0', hp0, hq⟩
  exact ⟨hE P hA p' p hpq, fun V hV =>
    ⟨(covFamily_chainLim hE hC hA).isLittleGroupCovariant hpq hV, hM P hA p' p hpq V hV⟩⟩

/-- **The Pauli link** from existence, covariance and the one-variable limit. -/
theorem chainPauliLink_of (hE : ChainExistsLink) (hC : ChainCovLink) (hPA : ChainPauliAtLink) :
    ChainPauliLink := by
  intro P hA η hη
  obtain ⟨q₀, hq₀, h⟩ := (covFamily_chainLim hE hC hA).uniform_of_tendsto P.e (hPA P hA) η hη
  exact ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq V hV =>
    h p' p ⟨hp', hp, hp0', hp0, hq⟩ hqq V hV⟩

/-- The one-variable limit is also necessary: the Pauli link (with existence and covariance)
gives it. -/
theorem chainPauliAtLink_of_chainPauliLink (hE : ChainExistsLink) (hC : ChainCovLink)
    (hP : ChainPauliLink) : ChainPauliAtLink := by
  intro P hA
  refine (covFamily_chainLim hE hC hA).tendsto_of_uniform P.e fun η hη => ?_
  obtain ⟨q₀, hq₀, h⟩ := hP P hA η hη
  exact ⟨q₀, hq₀, fun p' p hpq hqq V hV =>
    h p' p hpq.1 hpq.2.1 hpq.2.2.1 hpq.2.2.2.1 hpq.2.2.2.2 hqq V hV⟩

/-- **The set (b) headline (HC₃) from the four fixed-regulator obligations.** The conclusion is,
verbatim, the proposition of the frozen `QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`.
-/
theorem isFormFactorPair_vertexChain_two_pauli_limit_of_obligations (hE : ChainExistsLink)
    (hC : ChainCovLink) (hM : ChainMirrorLink) (hPA : ChainPauliAtLink)
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
  isFormFactorPair_vertexChain_two_pauli_limit_of_fixedLink
    (chainFixedLink_of_links (chainLimitLink_of hE hC hM) (chainPauliLink_of hE hC hPA))
    P₀ he hm η hη

end QED.ChainProof

end
