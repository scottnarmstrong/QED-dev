/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegFront
public import QED.ChainProof.SetCRegMainBDK

/-!
# Set (c): the longitudinal part of the VP-share kernels

Helper level for the regulator limit `hReg` of
`QED.ChainProof.SetCRegDisp.setCRegLimitB_of_leaves`. The share kernels `uSC` carry the shell
slope `shellKer₁C = shellKer₁ + (e⁴/64π⁴) ∫₀^∞ R_T`, whose longitudinal part grows like
`log Λ`. Here the longitudinal part of the five share classes is collapsed. The two line classes
carry `2 (ΔV_k + ΔV_m) = -2 ΔF₂` (the identity `V_k + V_m + F₂ = 0`), the three vertex classes
`(3/2) B(0) = 3 ΔF₂`. So in total it is `¼ ∫₀^∞ R_T · ΔF₂`, with
`ΔF₂ = F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ)`: exactly the value of the middle vertex class alone.

By the Ward identity for the longitudinal part of the dressed photon, the longitudinal kernels
`uBDK` of the twelve main classes should cancel it exactly, at every regulator and every `T`
(`IsKKCancel`; not proved here). Under that input the total kernel is the Feynman kernel
(`setCKerRe_eq_feyn`).

* `oneLoopF2_eq_one_div`, `dVk_add_dVm`: the outer line factors;
* `uSF`: the Feynman share kernels (shell slope `shellKer₁`);
* **`sum_uSC_eq`**: `∑ uSC = ∑ uSF + i (e⁶/256π⁶) ∫₀^∞ R_T · ΔF₂`;
* **`setCKerRe_eq_add_long`**: the real total kernel is the one with the Feynman shares plus
  `¼ ∫₀^∞ R_T · ΔF₂`;
* `IsKKCancel`, **`setCKerRe_eq_feyn`**: under the cancellation of the longitudinal parts the
  total kernel uses only the transverse main kernels and the Feynman shares.
-/

@[expose] public section

open Complex Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitLLink (oneLoopF2)
open QED.TwoLoop.UnitSCClose (selfVk selfVm)

/-- `F₂⁽²⁾` depends on the masses only through `μ/m`. -/
theorem oneLoopF2_eq_one_div {m μ : ℝ} (hm : 0 < m) : oneLoopF2 m μ = oneLoopF2 1 (μ / m) := by
  unfold oneLoopF2
  refine intervalIntegral.integral_congr fun Y _ => ?_
  simp only [QED.TwoLoop.UnitLLink.ladderInnerMass]
  have hm' : m ≠ 0 := hm.ne'
  by_cases h : Y ^ 2 * m ^ 2 + (1 - Y) * μ ^ 2 = 0
  · have h' : Y ^ 2 * 1 ^ 2 + (1 - Y) * (μ / m) ^ 2 = 0 := by
      rw [div_pow, one_pow, mul_one]
      field_simp
      linear_combination h
    rw [h, h']
    simp
  · have h' : Y ^ 2 * 1 ^ 2 + (1 - Y) * (μ / m) ^ 2 ≠ 0 := by
      intro h''
      apply h
      rw [div_pow, one_pow, mul_one] at h''
      field_simp at h''
      linear_combination h''
    field_simp

/-- **The line factors of the share**: `ΔV_k + ΔV_m = -ΔF₂`. -/
theorem dVk_add_dVm {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    dVk m mγ Λ + dVm m mγ Λ = -(oneLoopF2 m mγ - oneLoopF2 m Λ) := by
  have h1 := QED.TwoLoop.UnitSCClose.selfVk_add_selfVm_add_oneLoopF2 (div_pos hmγ hm)
  have h2 := QED.TwoLoop.UnitSCClose.selfVk_add_selfVm_add_oneLoopF2 (div_pos hΛ hm)
  rw [oneLoopF2_eq_one_div hm, oneLoopF2_eq_one_div (μ := Λ) hm, dVk, dVm]
  linear_combination h1 - h2

/-- The Pauli factor of the share vertex classes: `B(0) = 2 ΔF₂`. -/
theorem sPauliB0_eq_two_mul {P₀ : Params} {mγ Λ : ℝ} (hm : 0 < P₀.m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) : sPauliB0 P₀ mγ Λ = 2 * (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) :=
  QED.TwoLoop.UnitLLink.oneLoopPauliZero_eq { P₀ with mγ := mγ, Λ := Λ } hm hmγ hΛ

/-- The share kernels with the Feynman shell slope `shellKer₁` (no longitudinal part). -/
noncomputable abbrev uSF (P₀ : Params) : Fin 5 → ℝ → ℝ → ℝ → ℂ :=
  uShare P₀ (shellKer₁ P₀) (massKer P₀ (shellKer₀ P₀) (shellKer₁ P₀))

theorem sum_uShare (P₀ : Params) (w₂ wm : ℝ → ℝ → ℝ → ℂ) (mγ Λ T : ℝ) :
    ∑ k, uShare P₀ w₂ wm k mγ Λ T =
      2 * (sCoefLine P₀ * ((dVk P₀.m mγ Λ : ℂ) * w₂ mγ Λ T + (dVm P₀.m mγ Λ : ℂ) * wm mγ Λ T)) +
        3 * (sCoefVtx P₀ mγ Λ * w₂ mγ Λ T) := by
  simp only [Fin.sum_univ_five, uShare]
  norm_num
  ring

/-- **The longitudinal part of the share classes collapses**:
`∑ uSC = ∑ uSF + i (e⁶/256π⁶) ∫₀^∞ R_T · (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`. -/
theorem sum_uSC_eq (P₀ : Params) (hm : 0 < P₀.m) {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (T : ℝ) :
    ∑ k, uSC P₀ k mγ Λ T = ∑ k, uSF P₀ k mγ Λ T +
      I * ((P₀.e ^ 6 / (256 * π ^ 6) * photonTail (vpPhotonT P₀.m mγ Λ T) 0 *
        (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) : ℝ) : ℂ) := by
  rw [sum_uShare, sum_uShare]
  simp only [massKer, shellKer₁C_eq, sCoefLine, sCoefVtx,
    sPauliB0_eq_two_mul hm hmγ hΛ]
  have h := dVk_add_dVm hm hmγ hΛ
  have hc : ((dVk P₀.m mγ Λ : ℝ) : ℂ) + ((dVm P₀.m mγ Λ : ℝ) : ℂ) =
      -(((oneLoopF2 P₀.m mγ : ℝ) : ℂ) - ((oneLoopF2 P₀.m Λ : ℝ) : ℂ)) := by
    exact_mod_cast h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp
  linear_combination (4096 * (P₀.e : ℂ) ^ 6 * (photonTail (vpPhotonT P₀.m mγ Λ T) 0 : ℂ)) * hc

/-- **The real total kernel with the longitudinal share part split off**. -/
theorem setCKerRe_eq_add_long (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ) {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) (T : ℝ) :
    setCKerRe P₀ uBD mγ Λ T = kerRe P₀ uBD (uCBC P₀) (uSF P₀) mγ Λ T +
      photonTail (vpPhotonT P₀.m mγ Λ T) 0 / 4 * (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) := by
  simp only [setCKerRe, kerRe]
  rw [sum_uSC_eq P₀ hm hmγ hΛ T]
  have e : ∀ z w : ℂ, (1 / I * (z + w)).re = (1 / I * z).re + (1 / I * w).re := fun z w => by
    rw [mul_add, Complex.add_re]
  rw [show ∀ a b c d : ℂ, a + b + (c + d) = (a + b + c) + d from fun _ _ _ _ => by ring, e,
    mul_add]
  congr 1
  have hI : (1 / I * (I * (((P₀.e ^ 6 / (256 * π ^ 6) * photonTail (vpPhotonT P₀.m mγ Λ T) 0 *
      (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) : ℝ) : ℂ)))).re =
      P₀.e ^ 6 / (256 * π ^ 6) * photonTail (vpPhotonT P₀.m mγ Λ T) 0 *
        (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_mul, Complex.ofReal_re]
  rw [hI]
  field_simp
  ring

/-- **The cancellation of the longitudinal parts** (expected from the Ward identity, not proved):
the longitudinal kernels of the twelve main classes cancel the longitudinal share part at every
regulator and every spectral mass. -/
def IsKKCancel (P₀ : Params) : Prop :=
  ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ →
    64 * π ^ 6 / P₀.e ^ 6 * ((1 / I) * ∑ i, uBDK P₀ i mγ Λ T).re =
      -(photonTail (vpPhotonT P₀.m mγ Λ T) 0 / 4 * (oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ))

/-- **Under the cancellation the total kernel is the Feynman kernel**: transverse main kernels
`uBDT`, the fixed counterterm kernels and the Feynman shares `uSF`. -/
theorem setCKerRe_eq_feyn {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hK : IsKKCancel P₀)
    {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ) (T : ℝ) :
    setCKerRe P₀ (uBD P₀) mγ Λ T = kerRe P₀ (uBDT P₀) (uCBC P₀) (uSF P₀) mγ Λ T := by
  rw [setCKerRe_eq_add_long P₀ he hm _ hmγ (hmγ.trans hΛ) T, ← neg_neg (photonTail _ 0 / 4 * _),
    ← hK mγ Λ T hmγ hΛ]
  simp only [kerRe, uBD, Finset.sum_add_distrib]
  rw [show ∀ a b c d : ℂ, a + b + c + d = (a + c + d) + b from fun _ _ _ _ => by ring,
    mul_add, Complex.add_re]
  ring

end QED.ChainProof.SetCRegDisp

end
