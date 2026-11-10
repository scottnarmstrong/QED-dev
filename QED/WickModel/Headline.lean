/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszAmplitude
public import QED.Frozen.WickModel.IsLSZChargeNormalized
public import QED.Frozen.WickModel.IsLSZResponseMagneticMoment
public import QED.Frozen.WickModel.LszSourceMagneticMoment
public import QED.Frozen.Algebra.LorentzGen
public import QED.Frozen.Algebra.Lower
public import QED.WickModel.HeadlinePair
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
import QED.Frozen.WickModel.IsLSZChargeNormalizedIff
import QED.Frozen.WickModel.IsLSZResponseMagneticMomentIff
import QED.Frozen.WickModel.ElectronCountertermsExistsUnique
import QED.Frozen.OneLoop.ChargeConditionExistsUnique
import QED.Frozen.OneLoop.ResponseMagneticMomentExistsUnique
import QED.Frozen.OneLoop.PauliFormFactorLimit
import QED.Frozen.OneLoop.LandeFactorLimit
import QED.Frozen.OneLoop.SourceLandeFactorLimit
import QED.WickModel.LszPacketMoment
import Mathlib.Tactic.Ring

/-!
# The one-loop anomalous magnetic moment from the LSZ amplitude

The headline limit, from the model's own LSZ amplitude, with the internal copy
`QED.WickModel.Headline.LszPair` of the LSZ form-factor decomposition. The model data `P₀` has
its photon regulators `m_γ`, `Λ` and counterterms `δ₁`, `δ₂`, `δ_m` replaced.

* **Counterterms.** `Z₁` comes from the sealed (K) and `δ₁ = Z₁ - 1`; `(δ₂, δ_m)` from the sealed
  (Z₆) at that `δ₁`; the LSZ charge condition (L₄) is (K₀) by (L₄′); a response magnetic moment
  exists by (R), and is an LSZ one by (L₅′).
* **Pauli form factor.** The LSZ pairs are the one-loop pairs, shifted in the first component
  (`QED.WickModel.Headline.lszPair_iff_isFormFactorPair_vertexOneLoop`); so the sealed (I)
  applies. This needs no charge condition.
* **Response Landé factor.** By (L₄′), (L₅′) and the sealed (R′).
* **Source Landé factor.** The LSZ source magnetic moment (L₇) equals the packet-4b one (W₃) at
  `Z₁ = 1 + δ₁` for every packet width (`QED.WickModel.LszPacket.lszSourceMagneticMoment_eq`);
  so (L₄′) and the sealed (W₅) apply.

The headline takes `δ` the least and `R` the largest of the three limits' thresholds.

## Main statements

* `QED.WickModel.Headline.exists_onShell_counterterms`: on-shell counterterms exist.
* `QED.WickModel.Headline.lszPair_pauli_limit`: the Pauli component of the LSZ pairs.
* `QED.WickModel.Headline.lszResponse_landeFactor_limit`: the response Landé factor.
* `QED.WickModel.Headline.lszSource_landeFactor_limit`: the source Landé factor.
* `QED.WickModel.Headline.landeFactor_limit_of_lsz`: the headline limit.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.WickModel

/-- **On-shell counterterms exist.** For `e ≠ 0` and regulators `m_γ, Λ > 0` there are
counterterms `δ₁`, `δ₂`, `δ_m` with the electron on shell (Z₅), the LSZ charge condition (L₄)
holding, and an LSZ response magnetic moment (L₅). -/
theorem Headline.exists_onShell_counterterms (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hM₁ : P₀.m < P₀.M₁) (hM₂ : P₀.m < P₀.M₂) (hPV₁ : 1 + P₀.c₁ + P₀.c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + P₀.c₁ * P₀.M₁ ^ 2 + P₀.c₂ * P₀.M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) :
    ∃ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
        { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
      IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
        hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon ∧
      ∃ μ : ℝ, IsLSZResponseMagneticMoment
        { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
        hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ := by
  obtain ⟨Z₁, hZ₁, -⟩ := QED.OneLoop.existsUnique_isChargeNormalized P₀.e P₀.m mγ Λ he hm hmγ hΛ
  obtain ⟨d, hd, -⟩ :=
    electronCounterterms_existsUnique { P₀ with mγ := mγ, Λ := Λ, δ₁ := Z₁ - 1 } hm hmγ hΛ
  refine ⟨Z₁ - 1, d.1, d.2, hd, ?_, ?_⟩
  · rw [isLSZChargeNormalized_iff_isChargeNormalized]
    show QED.OneLoop.IsChargeNormalized P₀.e (1 + (Z₁ - 1)) P₀.m mγ Λ hm hmγ hΛ
    rwa [add_sub_cancel]
  · obtain ⟨μ, hμ, -⟩ :=
      QED.OneLoop.existsUnique_isResponseMagneticMoment P₀.e (1 + (Z₁ - 1)) P₀.m mγ Λ hm hmγ hΛ
    refine ⟨μ, ?_⟩
    rw [isLSZResponseMagneticMoment_iff_isResponseMagneticMoment]
    exact hμ

/-- **The Pauli component of the LSZ form-factor pairs** tends to `e²/(8π²)` jointly as
`q² → 0⁺`, `m_γ → 0⁺` and `Λ → ∞`, uniformly in the counterterms: near the limit an LSZ pair
exists, and every LSZ pair has its second component within `η` of `e²/(8π²)`. By the sealed (I)
and `QED.WickModel.Headline.lszPair_iff_isFormFactorPair_vertexOneLoop`. -/
theorem Headline.lszPair_pauli_limit (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hM₁ : P₀.m < P₀.M₁) (hM₂ : P₀.m < P₀.M₂) (hPV₁ : 1 + P₀.c₁ + P₀.c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + P₀.c₁ * P₀.M₁ ^ 2 + P₀.c₂ * P₀.M₂ ^ 2 = 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      ∀ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ)
        (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
        (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
        0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
        (∃ F : ℂ × ℂ, Headline.LszPair
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F) ∧
        ∀ F : ℂ × ℂ, Headline.LszPair
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F →
          ‖F.2 - ((P₀.e ^ 2 / (8 * Real.pi ^ 2) : ℝ) : ℂ)‖ < η := by
  obtain ⟨δ, hδ, R, hI⟩ :=
    QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_limit P₀.e P₀.m he hm η hη
  refine ⟨δ, hδ, R, fun mγ Λ hmγ hΛ hmγδ hRΛ d₁ d₂ dm hon p' p hp' hp hp0' hp0 hq hqδ => ?_⟩
  obtain ⟨⟨G, hG⟩, hall⟩ := hI mγ Λ hmγ hΛ p' p hp' hp hp0' hp0 hq hqδ hmγδ hRΛ
  set P : Params := { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } with hP
  set κ := Headline.photonLegCoeff P hm hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0 with hκ
  refine ⟨⟨(G.1 + κ + ((1 + P.δ₁ : ℝ) : ℂ), G.2), ?_⟩, fun F hF => ?_⟩
  · rw [Headline.lszPair_iff_isFormFactorPair_vertexOneLoop, ← hκ]
    have h : G.1 + κ + ((1 + P.δ₁ : ℝ) : ℂ) - κ - ((1 + P.δ₁ : ℝ) : ℂ) = G.1 := by ring
    rw [h]
    exact hG
  · exact hall (F.1 - κ - ((1 + P.δ₁ : ℝ) : ℂ), F.2)
      ((Headline.lszPair_iff_isFormFactorPair_vertexOneLoop P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p'
        p hp' hp hp0' hp0 F).1 hF)

/-- **The response Landé factor from the LSZ amplitude** tends to `2 (1 + e²/(8π²))` jointly as
`m_γ → 0⁺` and `Λ → ∞`: for counterterms satisfying the LSZ charge condition (L₄), every LSZ
response magnetic moment (L₅) gives `g = 4 m μ / e` within `η`. By (L₄′), (L₅′) and the sealed
(R′). -/
theorem Headline.lszResponse_landeFactor_limit (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hM₁ : P₀.m < P₀.M₁) (hM₂ : P₀.m < P₀.M₂) (hPV₁ : 1 + P₀.c₁ + P₀.c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + P₀.c₁ * P₀.M₁ ^ 2 + P₀.c₂ * P₀.M₂ ^ 2 = 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      ∀ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
        IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon →
        ∀ μ : ℝ, IsLSZResponseMagneticMoment
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ →
          |4 * P₀.m * μ / P₀.e - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))| < η := by
  obtain ⟨δ, hδ, R, hR⟩ :=
    QED.OneLoop.landeFactor_isResponseMagneticMoment_limit P₀.e P₀.m he hm η hη
  refine ⟨δ, hδ, R, fun mγ Λ hmγ hΛ hmγδ hRΛ d₁ d₂ dm hon hL4 μ hμ => ?_⟩
  set P : Params := { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } with hP
  exact (hR mγ Λ hmγ hΛ hmγδ hRΛ).2 (1 + d₁) μ
    ((isLSZChargeNormalized_iff_isChargeNormalized P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon).1 hL4)
    ((isLSZResponseMagneticMoment_iff_isResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂
      hon μ).1 hμ)

/-- **The source Landé factor from the LSZ amplitude** tends to `2 (1 + e²/(8π²))`: for a
profile `φ` as in (W₄) and counterterms satisfying the LSZ charge condition (L₄), the Landé
factor of the LSZ source magnetic moment (L₇) of every sufficiently narrow packet is within `η`
of the limit, jointly as `m_γ → 0⁺` and `Λ → ∞`. By (L₄′), the equality of (L₇) with the
packet-4b source magnetic moment (W₃) at `Z₁ = 1 + δ₁`, and the sealed (W₅). -/
theorem Headline.lszSource_landeFactor_limit (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hM₁ : P₀.m < P₀.M₁) (hM₂ : P₀.m < P₀.M₂) (hPV₁ : 1 + P₀.c₁ + P₀.c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + P₀.c₁ * P₀.M₁ ^ 2 + P₀.c₂ * P₀.M₂ ^ 2 = 0)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      ∀ (d₁ d₂ dm : ℝ) (hon : IsElectronOnShell
          { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } hm hmγ hΛ),
        IsLSZChargeNormalized { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
          hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon →
        ∃ lam₀ > 0, ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ‖4 * (P₀.m : ℂ) * lszSourceMagneticMoment
              { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
              hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon φ lam / P₀.e
            - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))‖ < η := by
  obtain ⟨δ, hδ, R, hW⟩ :=
    QED.OneLoop.landeFactor_sourceMagneticMoment_limit P₀.e P₀.m he hm φ hφ hφc hφ0 η hη
  refine ⟨δ, hδ, R, fun mγ Λ hmγ hΛ hmγδ hRΛ d₁ d₂ dm hon hL4 => ?_⟩
  set P : Params := { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm } with hP
  obtain ⟨lam₀, hlam₀, hW'⟩ := (hW mγ Λ hmγ hΛ hmγδ hRΛ).2 (1 + d₁)
    ((isLSZChargeNormalized_iff_isChargeNormalized P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon).1 hL4)
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  rw [LszPacket.lszSourceMagneticMoment_eq P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hφ hφc lam hlam]
  exact hW' lam hlam hlt

/-- **The one-loop anomalous magnetic moment of the electron, from the model's own LSZ
amplitude** (the headline limit, with the internal copy `QED.WickModel.Headline.LszPair` of the
LSZ form-factor decomposition). Jointly as `m_γ → 0⁺` and `Λ → ∞`: on-shell counterterms with
the LSZ charge condition and an LSZ response magnetic moment exist; and for every such choice,
as `q² → 0⁺` the LSZ amplitude has a form-factor pair, every such pair has its Pauli component
within `η` of `e²/(8π²)`, every LSZ response magnetic moment gives a Landé factor within `η` of
`2 (1 + e²/(8π²))`, and so does the LSZ source magnetic moment of every sufficiently narrow
packet. -/
theorem Headline.landeFactor_limit_of_lsz (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
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
          (∃ F : ℂ × ℂ, Headline.LszPair
            { P₀ with mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂, δm := dm }
            hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F) ∧
          ∀ F : ℂ × ℂ, Headline.LszPair
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
            - 2 * (1 + P₀.e ^ 2 / (8 * Real.pi ^ 2))‖ < η := by
  obtain ⟨δI, hδI, RI, hI⟩ := Headline.lszPair_pauli_limit P₀ he hm hM₁ hM₂ hPV₁ hPV₂ η hη
  obtain ⟨δR, hδR, RR, hR⟩ :=
    Headline.lszResponse_landeFactor_limit P₀ he hm hM₁ hM₂ hPV₁ hPV₂ η hη
  obtain ⟨δW, hδW, RW, hW⟩ :=
    Headline.lszSource_landeFactor_limit P₀ he hm hM₁ hM₂ hPV₁ hPV₂ φ hφ hφc hφ0 η hη
  refine ⟨min δI (min δR δW), lt_min hδI (lt_min hδR hδW), max RI (max RR RW),
    fun mγ Λ hmγ hΛ hmγδ hRΛ => ⟨Headline.exists_onShell_counterterms P₀ he hm hM₁ hM₂ hPV₁ hPV₂
      mγ Λ hmγ hΛ, fun d₁ d₂ dm hon hL4 => ⟨fun p' p hp' hp hp0' hp0 hq hqδ => ?_, ?_, ?_⟩⟩⟩
  · exact hI mγ Λ hmγ hΛ (lt_of_lt_of_le hmγδ (min_le_left _ _))
      (lt_of_le_of_lt (le_max_left _ _) hRΛ) d₁ d₂ dm hon p' p hp' hp hp0' hp0 hq
      (lt_of_lt_of_le hqδ (min_le_left _ _))
  · exact hR mγ Λ hmγ hΛ
      (lt_of_lt_of_le hmγδ ((min_le_right _ _).trans (min_le_left _ _)))
      (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hRΛ) d₁ d₂ dm hon hL4
  · exact hW mγ Λ hmγ hΛ
      (lt_of_lt_of_le hmγδ ((min_le_right _ _).trans (min_le_right _ _)))
      (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hRΛ) d₁ d₂ dm hon hL4

end QED.WickModel

end
