/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAPauliLinkGen
public import QED.ChainProof.SetAPauliCond

/-!
# The set (a) Pauli link from covariance, a fixed-`ε` mirror identity and a nested value

Helper level for (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`. The Pauli link
`QED.ChainProof.SetAPauli.SetAPauliLink P₀ a` of `QED/ChainProof/SetAPauliCond.lean` is reduced,
by the abstract argument of `QED/ChainProof/SetAPauliLinkGen.lean` (the set (b) route, written
for any covariant family of limits), to the limit link `SetALimitLink P₀` (existence; owned
elsewhere) and three named statements about the set (a) limits `setALim` at fixed admissible
regulators (`SetAAdm`: `m < M₁, M₂`, Pauli–Villars conditions, `0 < m_γ < Λ`, `m_γ < 2m`, `D`
renormalized through order `e⁴`), none of which is proved here:

* `SetACovLink P₀` (covariance): for every real `L` with a spinor lift `(S, T)` that keeps
  positive energies, the limits `V` at `(p', p)` and `W` at `(L p', L p)` satisfy
  `S W^μ T = L^μ_ν V^ν`;
* `SetAMirrorAt P₀` (charge conjugation with inversion, at fixed `ε ∈ (0, 1]`): the family vertex
  satisfies `C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ`, the set (a) analogue of
  `QED.ChainProof.ChainMirrorAt`;
* `SetANestedAt P₀ R` (the nested value at fixed `q`): for small `Q > 0`, every limit at the
  canonical pair `(boostMomentum m Q, restMomentum m)` has Pauli projection
  `e² outerAt m Q (R m_γ Λ M₁ M₂)`, for a photon function `R` (for set (a), the dressed photon
  `Π⁽⁴⁾(s) s D(s)²` at fixed regulators; nothing here depends on that choice), with
  `SetAPhotonReg P₀ R` (measurable, continuous on `(0, ∞)`, bounded on `[0, ∞)`).

Proved here:
* `covFamily_setALim`: with the limit link and covariance, the limits form a
  `QED.ChainProof.CovFamily`;
* `isMirrorRel_setALim`: the fixed-`ε` mirror identity passes to the limits;
* **`setAPauliLink_of_nested`**: `SetAPauliLink P₀ (setAPauliValue P₀ R)`, with the
  fixed-regulator value `a = 64π⁶ e² outerAt m 0 R / e⁶`;
* `setAFixedLink_of_nested`: the fixed link of (HA₆), whose consumer is
  `QED.ChainProof.SetAPauli.isFormFactorPair_vertexSetA_pauli_limit_of_links`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetAPauli

open QED.TwoLoop.LimitCovariance QED.Dirac QED.TwoLoop.PauliZero QED.ChainProof.CovFamily

/-- The counterterm data of (HA₆). -/
abbrev RegCt : Type := Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3)

/-- The fixed admissible regulators of (HA₆) and a counterterm set renormalized through `e⁴`. -/
def SetAAdm (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) : Prop :=
  P₀.m < M₁ ∧ P₀.m < M₂ ∧ 1 + c₁ + c₂ = 0 ∧ P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 ∧
    0 < mγ ∧ 0 < Λ ∧ mγ < Λ ∧ mγ < 2 * P₀.m ∧
    Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2

/-- The `ε → 0⁺` limits of the set (a) family vertex at fixed regulators. -/
abbrev setALim (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (p' p : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
    (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V

/-- **Covariance of the set (a) limits** (open). -/
def SetACovLink (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D, SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D →
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ P₀.m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ V W, setALim P₀ M₁ M₂ c₁ c₂ mγ Λ D p' p V →
      setALim P₀ M₁ M₂ c₁ c₂ mγ Λ D (L *ᵥ p') (L *ᵥ p) W →
      ∀ μ, S * W μ * T = vecAct L V μ

/-- **The mirror identity of the set (a) family vertex at fixed `ε ∈ (0, 1]`** (open):
`C V_ε(p', p)^μᵀ C = Γ V_ε(p, p')^μ Γ`. -/
def SetAMirrorAt (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D, SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ p' p, IsPairQ P₀.m p' p → ∀ μ,
      chargeConj * (Graded.familyVertex { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7
          p' p μ)ᵀ * chargeConj =
        chir * Graded.familyVertex { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7
          p p' μ * chir

/-- **The nested value of the set (a) limits at fixed `q² = Q`** (open), for a photon function
`R m_γ Λ M₁ M₂`: for small `Q > 0`, every limit at the canonical pair has Pauli projection
`e² outerAt m Q R`. -/
def SetANestedAt (P₀ : Params) (R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D, SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D →
    ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ V,
      setALim P₀ M₁ M₂ c₁ c₂ mγ Λ D (boostMomentum P₀.m Q) (restMomentum P₀.m) V →
      QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q) (restMomentum P₀.m) V =
        ((P₀.e ^ 2 * QED.ChainProof.HCValue.outerAt P₀.m Q (R mγ Λ M₁ M₂) : ℝ) : ℂ)

/-- **Regularity of the photon function** (open): at admissible regulator masses, `R m_γ Λ M₁ M₂`
is measurable, continuous on `(0, ∞)` and bounded on `[0, ∞)`. -/
def SetAPhotonReg (P₀ : Params) (R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ M₁ M₂ mγ Λ : ℝ, P₀.m < M₁ → P₀.m < M₂ → 0 < mγ → mγ < Λ →
    Measurable (R mγ Λ M₁ M₂) ∧ ContinuousOn (R mγ Λ M₁ M₂) (Ioi 0) ∧
      ∃ C : ℝ, ∀ t, 0 ≤ t → |R mγ Λ M₁ M₂ t| ≤ C

/-- **The fixed-regulator value** of (HA₆) for the photon function `R`:
`a = 64π⁶ e² outerAt m 0 R / e⁶`. -/
noncomputable def setAPauliValue (P₀ : Params) (R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun mγ Λ M₁ M₂ =>
    64 * π ^ 6 * (P₀.e ^ 2 * QED.ChainProof.HCValue.outerAt P₀.m 0 (R mγ Λ M₁ M₂)) / P₀.e ^ 6

/-- **With the limit link and covariance, the set (a) limits form a covariant family.** -/
theorem covFamily_setALim {P₀ : Params} (hm : 0 < P₀.m) (hL : SetALimitLink P₀)
    (hC : SetACovLink P₀) {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) :
    CovFamily P₀.m (setALim P₀ M₁ M₂ c₁ c₂ mγ Λ D) where
  pos := hm
  exists' := by
    intro p' p hpq
    obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, hm2, hD⟩ := hA
    obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
    exact SetASpec.isFamilyVertexLimit_of_outerSpec _ _ D _ 7 hm hp' hp hp0' hp0
      (hL M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD p' p hp' hp hp0' hp0 hq)
  unique := by
    intro p' p _ V W hV hW
    funext μ
    ext i j
    exact tendsto_nhds_unique (hV μ i j) (hW μ i j)
  cov := hC M₁ M₂ c₁ c₂ mγ Λ D hA

/-- **The fixed-`ε` mirror identity passes to the set (a) limits.** -/
theorem isMirrorRel_setALim {P₀ : Params} (hMA : SetAMirrorAt P₀) {M₁ M₂ c₁ c₂ mγ Λ : ℝ}
    {D : RegCt} (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) :
    IsMirrorRel P₀.m (setALim P₀ M₁ M₂ c₁ c₂ mγ Λ D) := by
  intro p' p hpq V W hV hW μ
  refine chargeConj_lim_eq_of_eventually (hV μ) (hW μ) ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  exact hMA M₁ M₂ c₁ c₂ mγ Λ D hA ε hε.1 hε.2 p' p hpq μ

/-- **The set (a) Pauli link** from the limit link, covariance, the fixed-`ε` mirror identity,
the nested value and the regularity of the photon function, at the fixed-regulator value
`setAPauliValue P₀ R`. -/
theorem setAPauliLink_of_nested {P₀ : Params} {R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hL : SetALimitLink P₀) (hC : SetACovLink P₀) (hMA : SetAMirrorAt P₀)
    (hN : SetANestedAt P₀ R) (hR : SetAPhotonReg P₀ R) :
    SetAPauliLink P₀ (setAPauliValue P₀ R) := by
  intro M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD η hη
  have hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D := ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, hm2, hD⟩
  have H := covFamily_setALim hm hL hC hA
  have hMir := fun p' p hpq V hV =>
    H.isMirrorSymmetric_of_mirrorRel (isMirrorRel_setALim hMA hA) (p' := p') (p := p) hpq
      (V := V) hV
  obtain ⟨hRm, hRc, C, hRb⟩ := hR M₁ M₂ mγ Λ hM₁ hM₂ hmγ hmΛ
  have hb := H.tendsto_pauliAtCanonical_of_nested P₀.e (P₀.e ^ 2) hRm hRc hRb
    (hN M₁ M₂ c₁ c₂ mγ Λ D hA)
  obtain ⟨q₀, hq₀, hall⟩ := H.formFactor_pauli_of_tendsto hMir he hb η hη
  refine ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq V hV => ?_⟩
  obtain ⟨hex, hbd⟩ := hall p' p ⟨hp', hp, hp0', hp0, hq⟩ hqq V hV
  refine ⟨hex, fun F hF => ?_⟩
  have e1 : ((setAPauliValue P₀ R mγ Λ M₁ M₂ : ℝ) : ℂ) = 64 * (π : ℂ) ^ 6 *
      ((P₀.e ^ 2 * QED.ChainProof.HCValue.outerAt P₀.m 0 (R mγ Λ M₁ M₂) : ℝ) : ℂ) /
        (P₀.e : ℂ) ^ 6 := by
    unfold setAPauliValue
    push_cast
    ring
  rw [e1]
  exact hbd F hF

/-- **The fixed link of (HA₆)** from the limit link and the obligations of the Pauli link. -/
theorem setAFixedLink_of_nested {P₀ : Params} {R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hL : SetALimitLink P₀) (hC : SetACovLink P₀) (hMA : SetAMirrorAt P₀)
    (hN : SetANestedAt P₀ R) (hR : SetAPhotonReg P₀ R) :
    SetAFixedLink P₀ (setAPauliValue P₀ R) :=
  setAFixedLink_of_links hm hL (setAPauliLink_of_nested he hm hL hC hMA hN hR)

end QED.ChainProof.SetAPauli

end
