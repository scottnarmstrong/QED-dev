/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKNorm

/-!
# Set (c): the cancellation of the longitudinal parts above threshold

Successor target for `QED.ChainProof.SetCRegDisp.IsKKCancel`
(`QED/ChainProof/SetCRegLongShare.lean`) and `QED.ChainProof.SetCRegDisp.IsKKSum`
(`QED/ChainProof/SetCRegKKNorm.lean`). Those quantify over every real spectral mass `T` and are
false: `kkSumP` depends on `T` only through `√(m² T)/2`, so it is constant for `T ≤ 0`, while the
right side vanishes for `T < 0` (the tail of the photon function `R_T`, which has a non-integrable
pole at `s = -T m²`, takes the value `0`) and is nonzero at `T = 0`. The dispersion integral only
uses spectral masses `T ≥ 4` (threshold `4 m²`), so the successors are restricted to `4 ≤ T`.

* `IsKKCancelGe`, `IsKKSumGe`: the cancellation and its Pauli-limit form for `4 ≤ T`;
* **`isKKCancelGe_iff`**: `IsKKCancelGe P₀ ↔ IsKKSumGe P₀`;
* **`setCKerRe_eq_feyn_ge`**: under `IsKKCancelGe` the total kernel is the Feynman kernel for
  `4 ≤ T`.
-/

@[expose] public section

open Complex Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitLLink (oneLoopF2)

/-- **The cancellation of the longitudinal parts above threshold**: the longitudinal kernels of
the twelve main classes cancel the longitudinal share part at every regulator and every spectral
mass `T ≥ 4`. -/
def IsKKCancelGe (P₀ : Params) : Prop :=
  ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ → 4 ≤ T →
    64 * π ^ 6 / P₀.e ^ 6 * ((1 / I) * ∑ i, uBDK P₀ i mγ Λ T).re =
      -(photonTail (vpPhotonT P₀.m mγ Λ T) 0 / 4 * (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ))

/-- **The value of the sum of the longitudinal Pauli limits above threshold**:
`Re kkSumP = -4 e⁵ m⁵/(π⁴ (Λ² - m_γ²)²) · ∫₀^∞ R_T · ΔF₂` for `T ≥ 4`. -/
def IsKKSumGe (P₀ : Params) : Prop :=
  ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ → 4 ≤ T →
    (kkSumP P₀ mγ Λ T).re = -(4 * P₀.e ^ 5 * P₀.m ^ 5 / (π ^ 4 * (Λ ^ 2 - mγ ^ 2) ^ 2) *
      photonTail (vpPhotonT P₀.m mγ Λ T) 0 * (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ))

/-- **The cancellation above threshold is the value of the sum of the twelve longitudinal Pauli
limits.** -/
theorem isKKCancelGe_iff (P₀ : Params) (he : P₀.e ≠ 0) (hm : P₀.m ≠ 0) :
    IsKKCancelGe P₀ ↔ IsKKSumGe P₀ := by
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
  exact ⟨fun h mγ Λ T h0 h1 hT => (key mγ Λ h0 h1 T).1 (h mγ Λ T h0 h1 hT),
    fun h mγ Λ T h0 h1 hT => (key mγ Λ h0 h1 T).2 (h mγ Λ T h0 h1 hT)⟩

/-- **Under the cancellation above threshold the total kernel is the Feynman kernel** at every
spectral mass `T ≥ 4`: transverse main kernels `uBDT`, the fixed counterterm kernels and the
Feynman shares `uSF`. -/
theorem setCKerRe_eq_feyn_ge {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hK : IsKKCancelGe P₀) {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ) {T : ℝ} (hT : 4 ≤ T) :
    setCKerRe P₀ (uBD P₀) mγ Λ T = kerRe P₀ (uBDT P₀) (uCBC P₀) (uSF P₀) mγ Λ T := by
  rw [setCKerRe_eq_add_long P₀ he hm _ hmγ (hmγ.trans hΛ) T, ← neg_neg (photonTail _ 0 / 4 * _),
    ← hK mγ Λ T hmγ hΛ hT]
  simp only [kerRe, uBD, Finset.sum_add_distrib]
  rw [show ∀ a b c d : ℂ, a + b + c + d = (a + c + d) + b from fun _ _ _ _ => by ring,
    mul_add, Complex.add_re]
  ring

end QED.ChainProof.SetCRegDisp

end
