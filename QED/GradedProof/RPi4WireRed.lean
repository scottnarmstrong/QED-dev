/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Wire
public import QED.GradedProof.RPi4MajLClass
public import QED.GradedProof.RPi4MajTiltM
public import QED.GradedProof.RPi4FaceIdDone

/-!
# (R-Π₄) end-to-end wiring with the proved inputs discharged

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57). The wiring theorem
`QED.GradedProof.RPi4.vacuumPolarizationPart_two_lepton_limit_of_open` with every input that is
now proved discharged:

* `DecFaceGen` (`QED.GradedProof.RPi4.faceId_decFaceGen_all`);
* `MajLRay` of the three class entries, at `decCfg 1 4` and at every frozen-flavour
  configuration (`QED.GradedProof.RPi4.majL_vVal_VA`, `…VB`, `…VC`);
* the single-flavour one-loop blocks along the ray at the frozen flavours, masses at least `m`
  (`QED.GradedProof.RPi4.maj_tiltRay_fLim_pos`).

What remains open is exactly: the bounded class densities `MajDRay` (packaged as `WireDRay`),
the face rate `MajFaceRate`, both at `decCfg 1 4` and at the frozen flavours, and the
scale-Lipschitz bound `MajLimLip4` of the photon limit.

* `WireDRay Φ e m₀`: `MajDRay` of the three class densities;
* `WireFixDens P₀ mH`: `WireDRay` and `MajFaceRate` at every frozen-flavour configuration;
* `wire_majFixRay_of_dens`: `MajFixRay` from `WireFixDens`;
* **`vacuumPolarizationPart_two_lepton_limit_of_dens`**: the frozen conclusion from
  `WireDRay` and `MajFaceRate` at `decCfg 1 4`, `MajLimLip4` and `WireFixDens`;
* `WireDRayGen e`, `WireFaceRateGen e`: the same inputs for every flavour set closed under the
  Pauli–Villars conditions, and **`vacuumPolarizationPart_two_lepton_limit_of_gen`**, the frozen
  conclusion from `WireDRayGen`, `WireFaceRateGen` and `MajLimLip4`.
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **The bounded class densities along the ray**: `MajDRay` of the three class densities
`vDens` (entry `2 3`) of a flavour set `Φ` with threshold `m₀`. -/
def WireDRay {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e m₀ : ℝ) : Prop :=
  (MajDRay fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3) ∧
    (MajDRay fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3) ∧
    (MajDRay fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3)

/-- **`WireDRay` for every Pauli–Villars-closed flavour set** with masses at least `m₀ > 0`. -/
def WireDRayGen (e : ℝ) : Prop :=
  ∀ (F : Type) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ),
    0 < m₀ → (∀ g, m₀ ≤ Φ.mass g) → (∀ f, rep (rep f) = rep f) →
    (∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0) →
    (∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) →
    WireDRay Φ e m₀

/-- **`MajFaceRate` for every Pauli–Villars-closed flavour set** with masses at least `m₀ > 0`
(the export requested from the face identification). -/
def WireFaceRateGen (e : ℝ) : Prop :=
  ∀ (F : Type) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ),
    0 < m₀ → (∀ g, m₀ ≤ Φ.mass g) → (∀ f, rep (rep f) = rep f) →
    (∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0) →
    (∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) →
    MajFaceRate Φ rep e m₀

section Frozen

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **The open per-class inputs at every frozen-flavour configuration** (`m₀ = m`, the
representative map `leptonRep`): the bounded class densities and the face rate. -/
def WireFixDens : Prop :=
  ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ →
    1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
    ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
      (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
      (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      WireDRay (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) P₀.e P₀.m ∧
        MajFaceRate (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e P₀.m

/-- **`MajFixRay` from the open per-class inputs at the frozen flavours**: `MajLRay` of the
classes (`majL_vVal_*`) and the one-loop blocks (`maj_tiltRay_fLim_pos`, masses at least `m`)
are proved; `DecFaceGen` is `faceId_decFaceGen_all`. -/
theorem wire_majFixRay_of_dens (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (h : WireFixDens P₀ mH) : MajFixRay P₀ mH := by
  refine wire_majFixRay_of_ins P₀ mH he hm hmH (faceId_decFaceGen_all P₀.e) ?_
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂
  obtain ⟨⟨hDA, hDB, hDC⟩, hR⟩ :=
    h M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂
  have hmass := le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hM₁ hM₂ hmH hMH₁ hMH₂
  have hpv₁ := leptonFlavors_blockPV₁ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₁ hcH₁
  have hpv₂ := leptonFlavors_blockPV₂ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₂ hcH₂
  exact ⟨⟨majL_vVal_VA _ hm hmass P₀.e 2 3, majL_vVal_VB _ hm hmass P₀.e 2 3,
      majL_vVal_VC _ hm hmass P₀.e 2 3⟩, ⟨hDA, hDB, hDC⟩, hR,
    fun g => maj_tiltRay_fLim_pos P₀ _ leptonRep leptonRep_idem hpv₁ hpv₂ hm hmass he _⟩

/-- **`WireFixDens` from the generic inputs.** -/
theorem wire_fixDens_of_gen (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hD : WireDRayGen P₀.e) (hR : WireFaceRateGen P₀.e) : WireFixDens P₀ mH := by
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂
  have hmass := le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hM₁ hM₂ hmH hMH₁ hMH₂
  have hpv₁ := leptonFlavors_blockPV₁ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₁ hcH₁
  have hpv₂ := leptonFlavors_blockPV₂ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₂ hcH₂
  exact ⟨hD _ _ leptonRep P₀.m hm hmass leptonRep_idem hpv₁ hpv₂,
    hR _ _ leptonRep P₀.m hm hmass leptonRep_idem hpv₁ hpv₂⟩

/-- **(R-Π₄), conditional on the remaining open inputs**: the frozen conclusion of
`QED.Graded.vacuumPolarizationPart_two_lepton_limit`, with its binders, from the bounded class
densities (`WireDRay`) and the face rate (`MajFaceRate`) at `decCfg 1 4`, the scale-Lipschitz
bound `MajLimLip4` of the photon limit, and the same density and rate inputs at the frozen
flavours (`WireFixDens`). Everything else is proved. -/
theorem vacuumPolarizationPart_two_lepton_limit_of_dens {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hD4 : WireDRay (decCfg 1 4) P₀.e 1)
    (hR4 : MajFaceRate (decCfg 1 4) (fun _ => 0) P₀.e 1) (hL4 : MajLimLip4 P₀.e)
    (hFix : WireFixDens P₀ mH) :
    ∃ (Pinf : ℝ → ℂ) (C : ℝ), ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
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
            (∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) ∧
            ∀ Pol : ℝ → ℂ, (∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
              (∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖Pol s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
              ∀ s : ℝ, 0 ≤ s →
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  obtain ⟨hDA, hDB, hDC⟩ := hD4
  exact vacuumPolarizationPart_two_lepton_limit_of_open P₀ mH he hm hmH
    (faceId_decFaceGen_all P₀.e)
    (majL_vVal_VA _ one_pos hmass P₀.e 2 3) (majL_vVal_VB _ one_pos hmass P₀.e 2 3)
    (majL_vVal_VC _ one_pos hmass P₀.e 2 3) hDA hDB hDC hR4 hL4
    (wire_majFixRay_of_dens P₀ mH he hm hmH hFix)

end Frozen

/-- **(R-Π₄), conditional on the generic open inputs**: the frozen conclusion from the bounded
class densities and the face rate for every Pauli–Villars-closed flavour set (`WireDRayGen`,
`WireFaceRateGen`) and the scale-Lipschitz bound `MajLimLip4` of the photon limit. -/
theorem vacuumPolarizationPart_two_lepton_limit_of_gen {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hD : WireDRayGen P₀.e) (hR : WireFaceRateGen P₀.e) (hL4 : MajLimLip4 P₀.e) :
    ∃ (Pinf : ℝ → ℂ) (C : ℝ), ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
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
            (∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) ∧
            ∀ Pol : ℝ → ℂ, (∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
              (∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖Pol s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
              ∀ s : ℝ, 0 ≤ s →
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  exact vacuumPolarizationPart_two_lepton_limit_of_dens P₀ mH he hm hmH
    (hD _ _ (fun _ => 0) 1 one_pos hmass hrep hpv.1 hpv.2)
    (hR _ _ (fun _ => 0) 1 one_pos hmass hrep hpv.1 hpv.2) hL4
    (wire_fixDens_of_gen P₀ mH hm hmH hD hR)

end QED.GradedProof.RPi4

end
