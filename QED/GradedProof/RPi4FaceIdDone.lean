/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdOneLoop
public import QED.GradedProof.RPi4FaceIdGen

/-!
# (R-Π₄) step L6d3: the face-limit identity

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. From
`faceId_faceClassGen` and `faceId_decFaceGen`:

* **`faceId_decFaceGen_all`**: `DecFaceGen e` for every `e`;
* **`faceId_faceLimitId_all`**: the face-limit identity `FaceLimitId` at every admissible point.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

/-- **`DecFaceGen e`** for every `e`. -/
theorem faceId_decFaceGen_all (e : ℝ) : DecFaceGen e :=
  faceId_decFaceGen (faceId_faceClassGen e)

/-- **The face-limit identity** at every admissible point. -/
theorem faceId_faceLimitId_all {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (rep : F → F) (e : ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    {c s : ℝ} (hc : 0 < c) (hs₁ : -(4 * m₀ ^ 2) < s) (hs₂ : s < 2 * c ^ 2) :
    FaceLimitId Φ rep e m₀ c s :=
  faceId_decFaceGen_all e F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ c s hc hs₁ hs₂

end QED.GradedProof.RPi4

end
