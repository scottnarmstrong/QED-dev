/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAPauliLinkGen
public import QED.ChainProof.SetCPauliCond

/-!
# The set (c) Pauli link from covariance, a fixed-`ε` mirror identity and a canonical limit

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The Pauli link
`QED.ChainProof.SetCPauli.SetCPauliLink P₀ a` of `QED/ChainProof/SetCPauliCond.lean` is reduced,
by the abstract argument of `QED/ChainProof/SetAPauliLinkGen.lean` (the set (b) route, written
for any covariant family of limits), to the limit link `SetCLimitLink P₀` (existence) and three
named statements about the set (c) limits `setCLim` at fixed admissible regulators and VP share
(`SetCAdm`: `m < M₁, M₂`, Pauli–Villars conditions, `0 < m_γ < Λ`, `m_γ < 2m`, `D`
renormalized through order `e⁴`, `s` a VP share of `D`):

* `SetCCovLink P₀` (covariance, open): for every real `L` with a spinor lift `(S, T)` that keeps
  positive energies, the limits `V` at `(p', p)` and `W` at `(L p', L p)` satisfy
  `S W^μ T = L^μ_ν V^ν`;
* `SetCMirrorAt P₀` (charge conjugation with inversion, at fixed `ε ∈ (0, 1]`):
  `C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ`; **proved** in `QED/ChainProof/SetCMirror.lean`;
* `SetCPauliAt P₀ b` (the canonical Pauli limit, open): as `Q → 0⁺`, the Pauli projection of
  every limit at the canonical pair `(boostMomentum m Q, restMomentum m)` tends to the real
  number `b m_γ Λ M₁ M₂`. Unlike set (a) (`QED.ChainProof.SetAPauli.SetANestedAt`, a one-loop
  outer vertex `outerAt` with a dressed photon), the set (c) outer vertex is two-loop, so no
  `outerAt` form is assumed; `b` is expected to be the dispersion integral over the bubble's
  spectral mass of the twelve two-loop placements with their counterterms, at fixed regulators.

Proved here:
* `covFamily_setCLim`: with the limit link and covariance, the limits form a
  `QED.ChainProof.CovFamily`;
* `isMirrorRel_setCLim`: the fixed-`ε` mirror identity passes to the limits;
* `tendsto_pauliAtCanonical_setCLim`: the canonical Pauli projection tends to `b`;
* **`setCPauliLink_of_pauliAt`**: `SetCPauliLink P₀ (setCPauliValue P₀ b)`, with the
  fixed-regulator value `a = 64π⁶ b / e⁶`;
* `setCFixedLink_of_pauliAt`: the fixed link of (HS₆), whose consumer is
  `QED.ChainProof.SetCPauli.isFormFactorPair_vertexSetC_pauli_limit_of_links`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCPauli

open QED.TwoLoop.LimitCovariance QED.Dirac QED.TwoLoop.PauliZero QED.ChainProof.CovFamily
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-- The fixed admissible regulators of (HS₆), a counterterm set renormalized through `e⁴` and a
VP share of it. -/
def SetCAdm (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ) : Prop :=
  P₀.m < M₁ ∧ P₀.m < M₂ ∧ 1 + c₁ + c₂ = 0 ∧ P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 ∧
    0 < mγ ∧ 0 < Λ ∧ mγ < Λ ∧ mγ < 2 * P₀.m ∧
    Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2 ∧
    ThreeLoop.IsVPShareOnShell (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D s

/-- The `ε → 0⁺` limits of the set (c) family vertex at fixed regulators and VP share. -/
abbrev setCLim (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ)
    (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (shareCt D s) (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V

/-- **Covariance of the set (c) limits** (open). -/
def SetCCovLink (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ P₀.m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ V W, setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s p' p V →
      setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s (L *ᵥ p') (L *ᵥ p) W →
      ∀ μ, S * W μ * T = vecAct L V μ

/-- **The mirror identity of the set (c) family vertex at fixed `ε ∈ (0, 1]`**:
`C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ` (proved: `QED.ChainProof.SetCMirror.setCMirrorAt`). -/
def SetCMirrorAt (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ p' p, IsPairQ P₀.m p' p → ∀ μ,
      chargeConj * (Graded.familyVertex { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s)
          (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p μ)ᵀ * chargeConj =
        chir * Graded.familyVertex { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s)
          (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p p' μ * chir

/-- **The canonical Pauli limit of the set (c) limits** (open), for a value `b m_γ Λ M₁ M₂`: as
`Q → 0⁺`, the Pauli projection of every limit at the canonical pair tends to `b`. -/
def SetCPauliAt (P₀ : Params) (b : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ η : ℝ, 0 < η → ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ V,
      setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s (boostMomentum P₀.m Q) (restMomentum P₀.m) V →
      ‖QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q) (restMomentum P₀.m) V -
        ((b mγ Λ M₁ M₂ : ℝ) : ℂ)‖ < η

/-- **The fixed-regulator value** of (HS₆) for the canonical Pauli limit `b`:
`a = 64π⁶ b / e⁶`. -/
noncomputable def setCPauliValue (P₀ : Params) (b : ℝ → ℝ → ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun mγ Λ M₁ M₂ => 64 * π ^ 6 * b mγ Λ M₁ M₂ / P₀.e ^ 6

/-- **With the limit link and covariance, the set (c) limits form a covariant family.** -/
theorem covFamily_setCLim {P₀ : Params} (hm : 0 < P₀.m) (hL : SetCLimitLink P₀)
    (hC : SetCCovLink P₀) {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    CovFamily P₀.m (setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s) where
  pos := hm
  exists' := by
    intro p' p hpq
    obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, hm2, hD, hs⟩ := hA
    obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
    exact hL M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs p' p hp' hp hp0' hp0 hq
  unique := by
    intro p' p _ V W hV hW
    funext μ
    ext i j
    exact tendsto_nhds_unique (hV μ i j) (hW μ i j)
  cov := hC M₁ M₂ c₁ c₂ mγ Λ D s hA

/-- **The fixed-`ε` mirror identity passes to the set (c) limits.** -/
theorem isMirrorRel_setCLim {P₀ : Params} (hMA : SetCMirrorAt P₀) {M₁ M₂ c₁ c₂ mγ Λ : ℝ}
    {D : RegCt} {s : ℝ × ℝ × ℝ} (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    IsMirrorRel P₀.m (setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s) := by
  intro p' p hpq V W hV hW μ
  refine chargeConj_lim_eq_of_eventually (hV μ) (hW μ) ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  exact hMA M₁ M₂ c₁ c₂ mγ Λ D s hA ε hε.1 hε.2 p' p hpq μ

/-- **The canonical Pauli projection of the set (c) limits tends to `b`.** -/
theorem tendsto_pauliAtCanonical_setCLim {P₀ : Params} {b : ℝ → ℝ → ℝ → ℝ → ℝ}
    {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (H : CovFamily P₀.m (setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s)) (hB : SetCPauliAt P₀ b)
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    Tendsto (pauliAtCanonical (setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s) P₀.e P₀.m) (𝓝[>] 0)
      (𝓝 ((b mγ Λ M₁ M₂ : ℝ) : ℂ)) := by
  refine Metric.tendsto_nhds.2 fun η hη => ?_
  filter_upwards [hB M₁ M₂ c₁ c₂ mγ Λ D s hA η hη, self_mem_nhdsWithin] with Q hQ
    (hQ0 : 0 < Q)
  rw [dist_eq_norm]
  exact hQ _ (H.lim_canonicalLimit hQ0)

/-- **The set (c) Pauli link** from the limit link, covariance, the fixed-`ε` mirror identity
and the canonical Pauli limit, at the fixed-regulator value `setCPauliValue P₀ b`. -/
theorem setCPauliLink_of_pauliAt {P₀ : Params} {b : ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hL : SetCLimitLink P₀) (hC : SetCCovLink P₀) (hMA : SetCMirrorAt P₀)
    (hB : SetCPauliAt P₀ b) :
    SetCPauliLink P₀ (setCPauliValue P₀ b) := by
  intro M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs η hη
  have hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s :=
    ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, hm2, hD, hs⟩
  have H := covFamily_setCLim hm hL hC hA
  have hMir := fun p' p hpq V hV =>
    H.isMirrorSymmetric_of_mirrorRel (isMirrorRel_setCLim hMA hA) (p' := p') (p := p) hpq
      (V := V) hV
  obtain ⟨q₀, hq₀, hall⟩ :=
    H.formFactor_pauli_of_tendsto hMir he (tendsto_pauliAtCanonical_setCLim H hB hA) η hη
  refine ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq V hV => ?_⟩
  obtain ⟨hex, hbd⟩ := hall p' p ⟨hp', hp, hp0', hp0, hq⟩ hqq V hV
  refine ⟨hex, fun F hF => ?_⟩
  have e1 : ((setCPauliValue P₀ b mγ Λ M₁ M₂ : ℝ) : ℂ) =
      64 * (π : ℂ) ^ 6 * ((b mγ Λ M₁ M₂ : ℝ) : ℂ) / (P₀.e : ℂ) ^ 6 := by
    unfold setCPauliValue
    push_cast
    ring
  rw [e1]
  exact hbd F hF

/-- **The fixed link of (HS₆)** from the limit link and the obligations of the Pauli link. -/
theorem setCFixedLink_of_pauliAt {P₀ : Params} {b : ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hL : SetCLimitLink P₀) (hC : SetCCovLink P₀) (hMA : SetCMirrorAt P₀)
    (hB : SetCPauliAt P₀ b) :
    SetCFixedLink P₀ (setCPauliValue P₀ b) :=
  setCFixedLink_of_links hL (setCPauliLink_of_pauliAt he hm hL hC hMA hB)

end QED.ChainProof.SetCPauli

end
