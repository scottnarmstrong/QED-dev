/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4AsmCore
public import QED.GradedProof.RPi4MajGlue
public import QED.GradedProof.RPi4MajUV
public import QED.GradedProof.RPi4MajGrowD
public import QED.GradedProof.RPi4DecClass
public import QED.GradedProof.RPi4DecContF
public import QED.GradedProof.RPi4DecLipF
public import QED.GradedProof.RPi4DecContT

/-!
# (R-Π₄) end-to-end wiring, conditional on the open inputs

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57). This file chains the
proved steps L8–L11 with the decoupling (L9, modulo `DecFaceGen`) and the majorant (L10) into a
single statement whose conclusion is the frozen conclusion, with the frozen binders, and whose
extra hypotheses are exactly the inputs that are still open:

* `DecFaceGen P₀.e`, the generic face-limit identity (counterterm matching);
* at the configuration `decCfg 1 4` (flavour map `fun _ => 0`, `m₀ = 1`): `MajLRay` of the three
  class entries, `MajDRay` of the three class densities, `MajFaceRate`, and `MajLimLip4`;
* at the flavours of the frozen statement: `MajFixRay`.

Main results:

* `wire_lipT48_of_faceGen`: `DecLipT48` from `DecFaceGen` (second differences of the classes at
  `decCfg 1 4`, `decCfg 1 8`, then the heavy and light Lipschitz bounds);
* `wire_rayVal4_of_inputs`: `MajRayVal` at `decCfg 1 4` from its per-class inputs;
* `wire_asmMajorant_of_inputs`: `AsmMajorant` from the open majorant inputs;
* **`vacuumPolarizationPart_two_lepton_limit_of_open`**: the frozen conclusion of (R-Π₄);
* `WireFixIns`, `wire_majFixRay_of_ins`: `MajFixRay` from the per-class inputs at every
  frozen-flavour configuration (including the one-loop blocks along the ray, proved only for
  masses at least `1`), and the variant `vacuumPolarizationPart_two_lepton_limit_of_open_cls`.
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **`DecLipT48` from `DecFaceGen`**: the class bounds `dec_pieceTwo_vDens_*` at
`decCfg 1 4`, `decCfg 1 8` give the second-difference bound, hence the heavy and light
Lipschitz bounds, hence `DecLipT48` by `dec_lipT48_of`. -/
theorem wire_lipT48_of_faceGen (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e) :
    DecLipT48 P.e := by
  have key : ∀ x : ℝ, x = 4 ∨ x = 8 →
      DecLipHeavy (decCfg 1 x) (fun _ => 0) P.e ∧ DecLipLight (decCfg 1 x) (fun _ => 0) P.e := by
    intro x hx
    have hx0 : 0 < x := by rcases hx with rfl | rfl <;> norm_num
    have hx1 : (1 : ℝ) ≤ x := by rcases hx with rfl | rfl <;> norm_num
    have hm₀ : (0 : ℝ) < 1 := one_pos
    have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 x).mass g := dec_cfg_mass_ge le_rfl hm₀
      (by rw [one_pow]; exact hx1)
    have hpv := dec_cfg_pv (μ := 1) one_ne_zero hx0.le
    have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
      fun _ => rfl
    have hthr : -(2 * (1 : ℝ)) ^ 2 < -3 := by norm_num
    have hδ : (0 : ℝ) < 1 / 100 := by norm_num
    have hδ21 : (1 / 100 : ℝ) * 21 ≤ 1 / 4 := by norm_num
    have h2 : DecTwoDiff (decCfg 1 x) (fun _ => 0) P.e :=
      dec_twoDiff_of_vTwo (decCfg 1 x) (fun _ => 0) hm₀ hmass hrep hpv.1 hpv.2 P he one_pos hδ
        (by norm_num) (by norm_num)
        (dec_vTwo_of_pieceTwo
          (dec_pieceTwo_vDens_VA (decCfg 1 x) one_pos hmass P.e hthr hδ hδ21 2 3))
        (dec_vTwo_of_pieceTwo
          (dec_pieceTwo_vDens_VB (decCfg 1 x) one_pos hmass P.e hthr hδ hδ21 2 3))
        (dec_vTwo_of_pieceTwo
          (dec_pieceTwo_vDens_VC (decCfg 1 x) one_pos hmass P.e hthr hδ hδ21 2 3))
    exact ⟨dec_lipHeavy_of_twoDiff (decCfg 1 x) (fun _ => 0) hm₀ hmass hrep hpv.1 hpv.2 P he
      (fun s h₀ h₁ => hF (Fin 3) (decCfg 1 x) (fun _ => 0) 1 hm₀ hmass hrep hpv.1
        hpv.2 _ s (by positivity) ((lt_min (by norm_num) (by norm_num)).trans_le h₀)
        (h₁.trans_lt (asm_max_lt_two_mul_sq _))) h2,
      dec_lipLight_of_twoDiff (decCfg 1 x) (fun _ => 0) hm₀ hmass hrep hpv.1 hpv.2 P he h2⟩
  exact dec_lipT48_of P hF (fun x hx => (key x hx).1) (fun x hx => (key x hx).2)

/-- **`MajRayVal` at `decCfg 1 4` from its per-class inputs**: the single-flavour one-loop
blocks along the ray are proved (`maj_tiltRay_fLim_gen`, masses at least `1`). -/
theorem wire_rayVal4_of_inputs (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA (decCfg 1 4) P.e 1 a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB (decCfg 1 4) P.e 1 a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC (decCfg 1 4) P.e 1 a b k 2 3)
    (hDA : MajDRay fun u k => vDens aVA baseVA cVA (decCfg 1 4) P.e 1 u k 2 3)
    (hDB : MajDRay fun u k => vDens aVB baseVB cVB (decCfg 1 4) P.e 1 u k 2 3)
    (hDC : MajDRay fun u k => vDens aVC baseVC cVC (decCfg 1 4) P.e 1 u k 2 3)
    (hR : MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1) :
    MajRayVal (decCfg 1 4) (fun _ => 0) P.e := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  exact maj_rayVal_of_inputs (decCfg 1 4) (fun _ => 0) one_pos hmass hrep hpv.1 hpv.2 P he hF
    hA hB hC hDA hDB hDC hR
    (fun g => maj_tiltRay_fLim_gen P (decCfg 1 4) (fun _ => 0) hrep hpv.1 hpv.2 hmass he _)

section Frozen

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **`AsmMajorant` from the open majorant inputs**: the continuity and Lipschitz inputs at
`s = 0` and `MajGrowD` are proved (`dec_contD`, `dec_lipD48`, `dec_contT`,
`wire_lipT48_of_faceGen`, `maj_growD`). -/
theorem wire_asmMajorant_of_inputs (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hDA : MajDRay fun u k => vDens aVA baseVA cVA (decCfg 1 4) P₀.e 1 u k 2 3)
    (hDB : MajDRay fun u k => vDens aVB baseVB cVB (decCfg 1 4) P₀.e 1 u k 2 3)
    (hDC : MajDRay fun u k => vDens aVC baseVC cVC (decCfg 1 4) P₀.e 1 u k 2 3)
    (hR : MajFaceRate (decCfg 1 4) (fun _ => 0) P₀.e 1) (hL4 : MajLimLip4 P₀.e)
    (hFix : MajFixRay P₀ mH) : AsmMajorant P₀ mH :=
  maj_asmMajorant_of_lim P₀ mH he hm hmH hF (dec_contD P₀) (dec_lipD48 P₀) (dec_contT P₀ hF)
    (wire_lipT48_of_faceGen P₀ he hF) (maj_growD P₀ he)
    (wire_rayVal4_of_inputs P₀ he hF hA hB hC hDA hDB hDC hR) hL4 hFix

/-- **(R-Π₄), conditional on the open inputs**: the frozen conclusion of
`QED.Graded.vacuumPolarizationPart_two_lepton_limit`, with its binders, from the generic
face-limit identity `DecFaceGen` and the open majorant inputs (at `decCfg 1 4`: `MajLRay` and
`MajDRay` of the three classes, `MajFaceRate`, `MajLimLip4`; at the frozen flavours:
`MajFixRay`). The face-limit identities (`maj_asmFaceIds_of_decFaceGen`) and the decoupling
(`dec_asmDecoupling_of_faceGen`) follow from `DecFaceGen`. -/
theorem vacuumPolarizationPart_two_lepton_limit_of_open {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hDA : MajDRay fun u k => vDens aVA baseVA cVA (decCfg 1 4) P₀.e 1 u k 2 3)
    (hDB : MajDRay fun u k => vDens aVB baseVB cVB (decCfg 1 4) P₀.e 1 u k 2 3)
    (hDC : MajDRay fun u k => vDens aVC baseVC cVC (decCfg 1 4) P₀.e 1 u k 2 3)
    (hR : MajFaceRate (decCfg 1 4) (fun _ => 0) P₀.e 1) (hL4 : MajLimLip4 P₀.e)
    (hFix : MajFixRay P₀ mH) :
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
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 :=
  asm_two_lepton_limit_of_decoupling_majorant P₀ mH he hm hmH
    (maj_asmFaceIds_of_decFaceGen P₀ mH hm hmH hF) (dec_asmDecoupling_of_faceGen P₀ mH he hm hmH hF)
    (wire_asmMajorant_of_inputs P₀ mH he hm hmH hF hA hB hC hDA hDB hDC hR hL4 hFix)

/-- **The per-class majorant inputs at every frozen-flavour configuration** (`m₀ = m`, the
representative map `leptonRep`): `MajLRay` of the three class entries, `MajDRay` of the three
class densities, `MajFaceRate`, and the single-flavour one-loop blocks along the ray (proved by
`maj_tiltRay_fLim_gen` only when all masses are at least `1`). -/
def WireFixIns : Prop :=
  ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ →
    1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
    ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
      (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
      (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ((MajLRay fun a b k =>
          vVal aVA baseVA cVA (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) P₀.e P₀.m a b k 2 3) ∧
        (MajLRay fun a b k =>
          vVal aVB baseVB cVB (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) P₀.e P₀.m a b k 2 3) ∧
        (MajLRay fun a b k =>
          vVal aVC baseVC cVC (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) P₀.e P₀.m a b k 2 3)) ∧
      ((MajDRay fun u k =>
          vDens aVA baseVA cVA (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) P₀.e P₀.m u k 2 3) ∧
        (MajDRay fun u k =>
          vDens aVB baseVB cVB (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) P₀.e P₀.m u k 2 3) ∧
        (MajDRay fun u k =>
          vDens aVC baseVC cVC (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) P₀.e P₀.m u k 2 3)) ∧
      MajFaceRate (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e P₀.m ∧
      ∀ g, MajTiltRay (fLim (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e
        (Pi.single g 1))

/-- **`MajFixRay` from the per-class inputs** at every frozen-flavour configuration
(`maj_rayVal_of_inputs`). -/
theorem wire_majFixRay_of_ins (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) (h : WireFixIns P₀ mH) : MajFixRay P₀ mH := by
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂
  obtain ⟨⟨hA, hB, hC⟩, ⟨hDA, hDB, hDC⟩, hR, hFl⟩ :=
    h M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂
  exact maj_rayVal_of_inputs (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep hm
    (le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hM₁ hM₂
      hmH hMH₁ hMH₂)
    leptonRep_idem
    (leptonFlavors_blockPV₁ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₁
      hcH₁)
    (leptonFlavors_blockPV₂ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₂
      hcH₂)
    P₀ he hF hA hB hC hDA hDB hDC hR hFl

/-- **(R-Π₄), conditional on the open inputs, per class at the frozen flavours**: as
`vacuumPolarizationPart_two_lepton_limit_of_open`, with `MajFixRay` replaced by its per-class
inputs `WireFixIns`. -/
theorem vacuumPolarizationPart_two_lepton_limit_of_open_cls {n : ℕ} (P₀ : Params)
    (mH : Fin n → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC (decCfg 1 4) P₀.e 1 a b k 2 3)
    (hDA : MajDRay fun u k => vDens aVA baseVA cVA (decCfg 1 4) P₀.e 1 u k 2 3)
    (hDB : MajDRay fun u k => vDens aVB baseVB cVB (decCfg 1 4) P₀.e 1 u k 2 3)
    (hDC : MajDRay fun u k => vDens aVC baseVC cVC (decCfg 1 4) P₀.e 1 u k 2 3)
    (hR : MajFaceRate (decCfg 1 4) (fun _ => 0) P₀.e 1) (hL4 : MajLimLip4 P₀.e)
    (hFixI : WireFixIns P₀ mH) :
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
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 :=
  vacuumPolarizationPart_two_lepton_limit_of_open P₀ mH he hm hmH hF hA hB hC hDA hDB hDC hR hL4
    (wire_majFixRay_of_ins P₀ mH he hm hmH hF hFixI)

end Frozen

end QED.GradedProof.RPi4

end
