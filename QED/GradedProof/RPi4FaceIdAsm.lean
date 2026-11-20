/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdVDens
public import QED.GradedProof.RPi4FaceIdGen

/-!
# (R-Π₄) step L6d3: `FaceClassGen` from a one-loop limit

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The sum of the
three class densities satisfies `FaceIdPL` with `Ψ = faceIdClassPsi` (entry `(2, 3)`), the sum
of the face integrals of all pieces and flavours (`faceId_classPL`). Hence the generic
class-level face identity `FaceClassGen e` follows from the **one-loop limit**
`FaceIdOneLoopLim e`: `Ψ(ε) → (iπ²)⁻¹ · 3e²/(16π²) · ∑_g fLim(single g 1)` as `ε → 0⁺`, at
every tilted momentum below threshold (`faceId_faceClassGen_of_oneLoop`). What remains is the
one-loop algebra of `Ψ` (Dirac identities, partial fractions, Pauli–Villars cancellation,
identification with the counterterm bubbles and the Ward step).

* `faceIdClassPsi`, **`faceId_classPL`**, `FaceIdOneLoopLim`,
  **`faceId_faceClassGen_of_oneLoop`**.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2

/-- **The face integrals of the three classes** at entry `(2, 3)` (`β = 0, 0, 1` for
`VA`, `VB`, `VC`). -/
noncomputable def faceIdClassPsi {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e m₀ : ℝ)
    (k : Fin 4 → ℝ) (ε : ℝ) : ℂ :=
  faceIdBlockPsi baseVA cVA (vNum e 0 1 aVA baseVA cVA) (vNumE4 e 0 1 aVA) Φ m₀ 0 k 2 3 ε +
    faceIdBlockPsi baseVB cVB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) Φ m₀ 0 k 2 3 ε +
    faceIdBlockPsi baseVC cVC (vNum e 0 1 aVC baseVC cVC) (vNumE4 e 0 1 aVC) Φ m₀ 1 k 2 3 ε

/-- **The three classes as one-loop limits** at one momentum below threshold. -/
theorem faceId_classPL {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ}
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) :
    FaceIdPL (fun t => vDens aVA baseVA cVA Φ e m₀ t k 2 3 + vDens aVB baseVB cVB Φ e m₀ t k 2 3 +
      vDens aVC baseVC cVC Φ e m₀ t k 2 3) (faceIdClassPsi Φ e m₀ k) :=
  ((faceId_vDens_PL_VA Φ hm₀ hmass e hk 2 3).add (faceId_vDens_PL_VB Φ hm₀ hmass e hk 2 3)).add
    (faceId_vDens_PL_VC Φ hm₀ hmass e hk 2 3)

/-- **The one-loop limit** behind the class-level face identity: at every tilted momentum below
threshold, `faceIdClassPsi → (iπ²)⁻¹ · 3e²/(16π²) · ∑_g fLim(single g 1)` as `ε → 0⁺`. -/
def FaceIdOneLoopLim (e : ℝ) : Prop :=
  ∀ (F : Type) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ),
    0 < m₀ → (∀ g, m₀ ≤ Φ.mass g) → (∀ f, rep (rep f) = rep f) →
    (∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0) →
    (∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) →
    ∀ c s : ℝ, 0 < c → -(4 * m₀ ^ 2) < s → s < 2 * c ^ 2 →
      Tendsto (faceIdClassPsi Φ e m₀ (tiltVec c s)) (𝓝[>] 0)
        (𝓝 ((I * (π : ℂ) ^ 2)⁻¹ * (((3 * e ^ 2 / (16 * π ^ 2) : ℝ) : ℂ) *
          ∑ g, fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3)))

/-- **`FaceClassGen` from the one-loop limit.** -/
theorem faceId_faceClassGen_of_oneLoop {e : ℝ} (h : FaceIdOneLoopLim e) : FaceClassGen e := by
  intro F _ _ Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ c s hc hs₁ hs₂
  have hk : -(2 * m₀) ^ 2 < Minkowski.dot (tiltVec c s) (tiltVec c s) := by
    rw [dot_tiltVec hs₂.le]; linarith
  have hT := (faceId_classPL Φ hm₀ hmass e hk).tendsto
    (h F Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ c s hc hs₁ hs₂)
  have hne : I * (π : ℂ) ^ 2 ≠ 0 :=
    mul_ne_zero I_ne_zero (pow_ne_zero 2 (ofReal_ne_zero.2 Real.pi_ne_zero))
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at hT
  exact hT

end QED.GradedProof.RPi4

end
