/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegLongShare

/-!
# Set (c): the cancellation of the longitudinal parts in the Pauli-limit normalization

Helper level for the cancellation `QED.ChainProof.SetCRegDisp.IsKKCancel`
(`QED/ChainProof/SetCRegLongShare.lean`). The longitudinal kernel of a main placement is an
explicit constant times the Pauli limit `kkLimP` at `x = 1/2`
(`QED/ChainProof/SetCRegMainBDKDesc.lean`), so the cancellation is a statement about the sum
over the twelve placements of these Pauli limits alone:

`Re ∑ᵢ kkLimP(i, √(m² T)/2, 1/2) = -4 e⁵ m⁵/(π⁴ (Λ² - m_γ²)²) · ∫₀^∞ R_T · ΔF₂`.

By the Ward identity at the ends of the element line (`QED.ChainProof.SetCMain.dKUnit_int`,
`QED.ChainProof.SetCMain.dKUnit_ext`) the twelve longitudinal integrands telescope. After a
second Ward step at the other end, what survives is the integral of the longitudinal photon
function times the one-loop vertex, plus terms proportional to `γ^μ` (no Pauli part), terms
odd in the element momentum, and terms that vanish on shell.

* `uBDK_eq`: `uBDK = i e (Λ² - m_γ²)²/(1024 π² m⁵) · kkLimP(i, √(m² T)/2, 1/2)`;
* `kkSumP`, `IsKKSum`: the sum of the twelve Pauli limits and its expected value;
* **`isKKCancel_iff`**: `IsKKCancel P₀ ↔ IsKKSum P₀`.
-/

@[expose] public section

open Complex Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain
open QED.TwoLoop.UnitLLink (oneLoopF2)

/-- **The longitudinal kernel of a main placement**:
`uBDK = i e (Λ² - m_γ²)²/(1024 π² m⁵) · kkLimP(i, √(m² T)/2, 1/2)`. -/
theorem uBDK_eq (P₀ : Params) (he : P₀.e ≠ 0) (hm : P₀.m ≠ 0) (i : Fin 12) (mγ Λ T : ℝ) :
    uBDK P₀ i mγ Λ T = I * ((P₀.e * (Λ ^ 2 - mγ ^ 2) ^ 2 / (1024 * π ^ 2 * P₀.m ^ 5) : ℝ) : ℂ) *
      kkLimP { P₀ with mγ := mγ, Λ := Λ } i (√(P₀.m ^ 2 * T) / 2) (1 / 2) := by
  have he' : (P₀.e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 he
  have hm' : (P₀.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [uBDK, kerK, vpCst, wKD]
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

/-- The sum over the twelve main placements of the Pauli limits at `x = 1/2` with the spectral
mass `√(m² T)/2`. -/
noncomputable def kkSumP (P₀ : Params) (mγ Λ T : ℝ) : ℂ :=
  ∑ i, kkLimP { P₀ with mγ := mγ, Λ := Λ } i (√(P₀.m ^ 2 * T) / 2) (1 / 2)

/-- **The expected value of the sum of the longitudinal Pauli limits** at every regulator and
every spectral mass: `Re kkSumP = -4 e⁵ m⁵/(π⁴ (Λ² - m_γ²)²) · ∫₀^∞ R_T · ΔF₂`. -/
def IsKKSum (P₀ : Params) : Prop :=
  ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ →
    (kkSumP P₀ mγ Λ T).re = -(4 * P₀.e ^ 5 * P₀.m ^ 5 / (π ^ 4 * (Λ ^ 2 - mγ ^ 2) ^ 2) *
      photonTail (vpPhotonT P₀.m mγ Λ T) 0 * (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ))

theorem kkCancel_lhs_eq (P₀ : Params) (he : P₀.e ≠ 0) (hm : P₀.m ≠ 0) (mγ Λ T : ℝ) :
    64 * π ^ 6 / P₀.e ^ 6 * ((1 / I) * ∑ i, uBDK P₀ i mγ Λ T).re =
      π ^ 4 * (Λ ^ 2 - mγ ^ 2) ^ 2 / (16 * P₀.e ^ 5 * P₀.m ^ 5) * (kkSumP P₀ mγ Λ T).re := by
  simp only [uBDK_eq P₀ he hm, ← Finset.mul_sum]
  rw [← mul_assoc, ← mul_assoc, one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_mul,
    Complex.re_ofReal_mul, kkSumP]
  field_simp
  ring

/-- **The cancellation of the longitudinal parts is the value of the sum of the twelve
longitudinal Pauli limits.** -/
theorem isKKCancel_iff (P₀ : Params) (he : P₀.e ≠ 0) (hm : P₀.m ≠ 0) :
    IsKKCancel P₀ ↔ IsKKSum P₀ := by
  have key : ∀ mγ Λ : ℝ, 0 < mγ → mγ < Λ → ∀ T : ℝ,
      (64 * π ^ 6 / P₀.e ^ 6 * ((1 / I) * ∑ i, uBDK P₀ i mγ Λ T).re =
        -(photonTail (vpPhotonT P₀.m mγ Λ T) 0 / 4 *
          (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ))) ↔
      ((kkSumP P₀ mγ Λ T).re = -(4 * P₀.e ^ 5 * P₀.m ^ 5 / (π ^ 4 * (Λ ^ 2 - mγ ^ 2) ^ 2) *
        photonTail (vpPhotonT P₀.m mγ Λ T) 0 * (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ))) := by
    intro mγ Λ hmγ hΛ T
    have hd : Λ ^ 2 - mγ ^ 2 ≠ 0 := by nlinarith
    have hc : π ^ 4 * (Λ ^ 2 - mγ ^ 2) ^ 2 / (16 * P₀.e ^ 5 * P₀.m ^ 5) ≠ 0 := by positivity
    rw [kkCancel_lhs_eq P₀ he hm]
    constructor
    · intro h
      apply mul_left_cancel₀ hc
      rw [h]
      field_simp
      ring
    · intro h
      rw [h]
      field_simp
      ring
  exact ⟨fun h mγ Λ T h0 h1 => (key mγ Λ h0 h1 T).1 (h mγ Λ T h0 h1),
    fun h mγ Λ T h0 h1 => (key mγ Λ h0 h1 T).2 (h mγ Λ T h0 h1)⟩

end QED.ChainProof.SetCRegDisp

end
