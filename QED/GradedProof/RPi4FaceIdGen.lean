/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecLin
public import QED.GradedProof.RPi4FaceIdClass

/-!
# (R-Π₄) step L6d3: the generic face identity and `DecFaceGen`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.
`FaceClassGen e` is the class-level face identity `FaceClassId` for **every** flavour set with
masses `≥ m₀ > 0`, an idempotent `rep` and the Pauli–Villars sums (zero coefficients and the
three-flavour configurations of the decoupling step included), at every tilted momentum below
threshold. It implies the decoupling worker's hypothesis `DecFaceGen e`
(**`faceId_decFaceGen`**): the mass hypothesis `Φ.mass g ≠ 0` of `faceId_faceLimitId` follows
from `0 < m₀ ≤ Φ.mass g`, and `s = 0` lies in the admissible range.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

/-- **The generic class-level face identity** at coupling `e`. -/
def FaceClassGen (e : ℝ) : Prop :=
  ∀ (F : Type) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ),
    0 < m₀ → (∀ g, m₀ ≤ Φ.mass g) → (∀ f, rep (rep f) = rep f) →
    (∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0) →
    (∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) →
    ∀ c s : ℝ, 0 < c → -(4 * m₀ ^ 2) < s → s < 2 * c ^ 2 →
      FaceClassId Φ rep e m₀ (tiltVec c s)

/-- **`DecFaceGen` from the generic class-level face identity.** -/
theorem faceId_decFaceGen {e : ℝ} (h : FaceClassGen e) : DecFaceGen e := by
  intro F _ _ Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ c s hc hs₁ hs₂
  have hne : ∀ g, Φ.mass g ≠ 0 := fun g => (hm₀.trans_le (hmass g)).ne'
  have h0₁ : -(4 * m₀ ^ 2) < 0 := by nlinarith
  have h0₂ : (0 : ℝ) < 2 * c ^ 2 := by positivity
  exact faceId_faceLimitId Φ rep hne
    (h F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ c s hc hs₁ hs₂)
    (h F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ c 0 hc h0₁ h0₂)

end QED.GradedProof.RPi4

end
