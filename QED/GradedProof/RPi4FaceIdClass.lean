/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DensBound
public import QED.GradedProof.RPi4FaceIdLim

/-!
# (R-Π₄) step L6d3: the face-limit identity from the class-level identity

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The density
bound `norm_qDens_sub_le` asks `FaceLimitId` (`t · (qDens(s, t) - qDens(0, t)) → 0`). Since
`t σ(t) → -3e²/(16π²)` (`abs_mul_sigma_add_le`), this follows from the **class-level face
identity** `FaceClassId` at the two tilted momenta: the limit of `t` times the sum of the three
class densities is `3e²/(16π²)` times the unit mass insertion `∑_g fLim(single g 1)`. In
counterterm language: the vertex faces of `VB` are the gauge counterterm classes at `d₁ = κ`,
the self-energy faces of `VA`, `VC` the fermion counterterm classes at `(d₂, d_m) = (κ, 4κ)`,
`κ = 1/(16π²)`; by the Ward step (`tendsto_gauge_add_d₂`) these add up to the mass insertion
`fLim(3e²κ)`, which the mass face `-3e²κ fLim` cancels. Then `t · qDens(s, t) → 0` for every
`s`, which is more than `FaceLimitId` needs.

* `FaceClassId`, `faceId_tendsto_mul_sigma`, **`faceId_tendsto_mul_qDens_zero`**,
  **`faceId_faceLimitId`**.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2

section Class

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The class-level face identity at the momentum `k`** (entry `(2, 3)`): `t` times the sum of
the photon-mass densities of `VA`, `VB`, `VC` tends to `3e²/(16π²)` times the unit mass
insertion `∑_g fLim(single g 1)`. -/
def FaceClassId (e m₀ : ℝ) (k : Fin 4 → ℝ) : Prop :=
  Tendsto (fun t : ℝ => (t : ℂ) * (vDens aVA baseVA cVA Φ e m₀ t k 2 3 +
      vDens aVB baseVB cVB Φ e m₀ t k 2 3 + vDens aVC baseVC cVC Φ e m₀ t k 2 3)) atTop
    (𝓝 (((3 * e ^ 2 / (16 * π ^ 2) : ℝ) : ℂ) *
      ∑ g, fLim Φ rep e (Pi.single g 1) k 2 3))

/-- **The mass face**: `t σ(e, m, t) → -3e²/(16π²)`. -/
theorem faceId_tendsto_mul_sigma (e : ℝ) {m : ℝ} (hm : m ≠ 0) :
    Tendsto (fun t : ℝ => (t : ℂ) * (sigma e m t : ℂ)) atTop
      (𝓝 ((-(3 * e ^ 2 / (16 * π ^ 2)) : ℝ) : ℂ)) := by
  refine faceId_tendsto_of_rate (C := e ^ 2 * |m| / (2 * π ^ 2)) fun t ht => ?_
  have h := abs_mul_sigma_add_le e hm (lt_of_lt_of_le one_pos ht)
  have hc : (t : ℂ) * (sigma e m t : ℂ) - ((-(3 * e ^ 2 / (16 * π ^ 2)) : ℝ) : ℂ) =
      ((t * sigma e m t + 3 * e ^ 2 / (16 * π ^ 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- **`t · qDens(s, t) → 0`** when the class-level face identity holds at the tilted momentum
`k'(s)` (the flavour masses nonzero, for the mass face). -/
theorem faceId_tendsto_mul_qDens_zero (hmass : ∀ g, Φ.mass g ≠ 0) {e m₀ c s : ℝ}
    (h : FaceClassId Φ rep e m₀ (tiltVec c s)) :
    Tendsto (fun t : ℝ => (t : ℂ) * qDens Φ rep e m₀ c s t) atTop (𝓝 0) := by
  set K : ℂ := ((3 * e ^ 2 / (16 * π ^ 2) : ℝ) : ℂ)
  have hσ : Tendsto (fun t : ℝ => ∑ g, (t : ℂ) * (sigma e (Φ.mass g) t : ℂ) *
      fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3) atTop
      (𝓝 (∑ g, ((-(3 * e ^ 2 / (16 * π ^ 2)) : ℝ) : ℂ) *
        fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3)) :=
    tendsto_finsetSum _ fun g _ => (faceId_tendsto_mul_sigma e (hmass g)).mul_const _
  have hsum := ((h.add hσ).const_mul (-I / ((c ^ 2 : ℝ) : ℂ)))
  have h0 : -I / ((c ^ 2 : ℝ) : ℂ) * (K * ∑ g, fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3 +
      ∑ g, ((-(3 * e ^ 2 / (16 * π ^ 2)) : ℝ) : ℂ) *
        fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3) = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [K]
    push_cast
    simp
  rw [h0] at hsum
  refine hsum.congr fun t => ?_
  have hd : ∑ g, (t : ℂ) * (sigma e (Φ.mass g) t : ℂ) *
      fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3 =
      (t : ℂ) * ∑ g, (sigma e (Φ.mass g) t : ℂ) *
        fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [qDens]
  rw [hd]
  ring

/-- **The face-limit identity `FaceLimitId` from the class-level identity** at `k'(s)` and at
`k'(0)`: both limits of `t · qDens` are `0`. -/
theorem faceId_faceLimitId (hmass : ∀ g, Φ.mass g ≠ 0) {e m₀ c s : ℝ}
    (hs : FaceClassId Φ rep e m₀ (tiltVec c s)) (h0 : FaceClassId Φ rep e m₀ (tiltVec c 0)) :
    FaceLimitId Φ rep e m₀ c s :=
  faceLimitId_of_tendsto Φ rep (faceId_tendsto_mul_qDens_zero Φ rep hmass hs)
    (faceId_tendsto_mul_qDens_zero Φ rep hmass h0)

end Class

end QED.GradedProof.RPi4

end
