/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LightClass
public import QED.GradedProof.RPi4UnifF
public import QED.GradedProof.RPi4Dyadic

/-!
# (R-Π₄) step L7: the class sum at a light photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7. The class sum
`QED.GradedProof.RPi4.qPair` at the photon pair `(a, b)` is `O(√b)` for `0 < a ≤ b ≤ 1`,
uniformly for `s` in a compact interval below threshold `-4m₀²`.

* `exists_norm_qPair_comparable_le`: comparable pairs `b ≤ 2a`, from the tilted representation
  `QED.GradedProof.RPi4.qPair_eq_tilt`, the class values (`lightBdd_vVal_VA` etc., `O(b)`) and
  the mass part `QED.GradedProof.RPi4.exists_norm_fLim_ctPair_tilt_le` (`O(√b)`);
* `exists_norm_qPair_light_le`: all light pairs, by the dyadic lemma
  `QED.GradedProof.RPi4.norm_le_of_comparable_rpow` and additivity `qPair_add`;
* `exists_norm_qPair_sub_light_le`: the subtracted form `‖Q(a, b; s) - Q(a, b; 0)‖ ≤ C √b`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

section L7

variable (P : QED.WickModel.Params) {F : Type} [Fintype F] [DecidableEq F]
  (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The class sum at light comparable photon pairs**: `‖Q(a, b; s)‖ ≤ C √b` for
`0 < a ≤ b ≤ min(2a, 1)`, uniformly for `s ∈ [S₀, S]`. -/
theorem exists_norm_qPair_comparable_le (he : P.e ≠ 0) {S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b s : ℝ, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 → S₀ ≤ s → s ≤ S →
      ‖qPair Φ rep P.e a b s‖ ≤ C * Real.sqrt b := by
  set c : ℝ := 1 + |S| with hc_def
  have hc : 0 < c := by positivity
  have hS : S < 2 * c ^ 2 := by nlinarith [le_abs_self S, abs_nonneg S]
  have hS₀' : -(2 * m₀) ^ 2 < S₀ := by linarith [show (2 * m₀) ^ 2 = 4 * m₀ ^ 2 by ring]
  have hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot
      (lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u) (lineK (tiltBase c S₀ S) (tiltDir c S₀ S) u) :=
    fun u hu => (dot_lineK_tilt_mem hS hS₀S hu).1
  obtain ⟨CA, hCA⟩ := lightBdd_vVal_VA Φ hm₀ hmass P.e hS₀' hseg 2 3
  obtain ⟨CB, hCB⟩ := lightBdd_vVal_VB Φ hm₀ hmass P.e hS₀' hseg 2 3
  obtain ⟨CC, hCC⟩ := lightBdd_vVal_VC Φ hm₀ hmass P.e hS₀' hseg 2 3
  obtain ⟨CF, hCF⟩ := exists_norm_fLim_ctPair_tilt_le P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he
    hS₀ hS₀S hS 2 3
  refine ⟨(|CA| + |CB| + |CC| + |CF|) / c ^ 2, by positivity,
    fun a b s ha hab hb2 hb1 h₀ h₁ => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hs : -(4 * m₀ ^ 2) < s := by linarith
  have hs2 : s < 2 * c ^ 2 := by linarith
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot (tiltVec c s) (tiltVec c s) := by
    rw [dot_tiltVec hs2.le]; exact hs
  obtain ⟨u, hu, hue⟩ := exists_tiltVec_eq_lineK (c := c) h₀ h₁
  rw [qPair_eq_tilt Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hc hs hs2,
    wV_eq_vVal_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    wV_eq_vVal_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    wV_eq_vVal_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk]
  have hA := hCA u hu a b ha hab hb2 hb1
  have hB := hCB u hu a b ha hab hb2 hb1
  have hC := hCC u hu a b ha hab hb2 hb1
  have hF := hCF a b s ha hab h₀ h₁
  rw [← hue] at hA hB hC
  have hsq : b ≤ Real.sqrt b := by
    have h := Real.sqrt_le_sqrt hb1
    rw [Real.sqrt_one] at h
    calc b = Real.sqrt b * Real.sqrt b := (Real.mul_self_sqrt hb.le).symm
      _ ≤ Real.sqrt b * 1 := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg b)
      _ = Real.sqrt b := mul_one _
  have hsb := Real.sqrt_nonneg b
  have hX : ∀ (C : ℝ) (z : ℂ), ‖z‖ ≤ C * b → ‖z‖ ≤ |C| * Real.sqrt b := fun C z h =>
    h.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) hb.le).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg C)))
  have hF' : ‖fLim Φ rep P.e (fun g => ctPair P.e (Φ.mass g) a b) (tiltVec c s) 2 3‖ ≤
      |CF| * Real.sqrt b := hF.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hsb)
  rw [norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add (hX _ _ hA) (hX _ _ hB))) (hX _ _ hC))) hF')
  calc 1 / c ^ 2 * ‖vVal aVA baseVA cVA Φ P.e m₀ a b (tiltVec c s) 2 3 +
        vVal aVB baseVB cVB Φ P.e m₀ a b (tiltVec c s) 2 3 +
        vVal aVC baseVC cVC Φ P.e m₀ a b (tiltVec c s) 2 3 +
        fLim Φ rep P.e (fun g => ctPair P.e (Φ.mass g) a b) (tiltVec c s) 2 3‖
      ≤ 1 / c ^ 2 * (|CA| * Real.sqrt b + |CB| * Real.sqrt b + |CC| * Real.sqrt b +
          |CF| * Real.sqrt b) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- **L7 (light photon pair).** `‖Q(a, b; s)‖ ≤ C √b` for `0 < a ≤ b ≤ 1`, uniformly for
`s ∈ [S₀, S]`, `S₀ > -4m₀²`. -/
theorem exists_norm_qPair_light_le (he : P.e ≠ 0) {S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ ≤ S) :
    ∃ C : ℝ, ∀ a b s : ℝ, 0 < a → a ≤ b → b ≤ 1 → S₀ ≤ s → s ≤ S →
      ‖qPair Φ rep P.e a b s‖ ≤ C * Real.sqrt b := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_qPair_comparable_le P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he
    hS₀ hS₀S
  refine ⟨C / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))), fun a b s ha hab hb1 h₀ h₁ => ?_⟩
  have hs : -(4 * m₀ ^ 2) < s := by linarith
  have h := norm_le_of_comparable_rpow (Q := fun a b => qPair Φ rep P.e a b s) (r₀ := 1)
    hC0 (by norm_num : (0 : ℝ) < 1 / 2)
    (fun a b d ha hab hbd _ => qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha
      (ha.trans_le hab) ((ha.trans_le hab).trans_le hbd) hs)
    (fun a b ha hab hb2 hb1 => by
      rw [← Real.sqrt_eq_rpow]
      exact hC a b s ha hab hb2 hb1 h₀ h₁) a b ha hab hb1
  rw [← Real.sqrt_eq_rpow] at h
  calc ‖qPair Φ rep P.e a b s‖ ≤ C * Real.sqrt b / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := h
    _ = _ := by ring

/-- **L7 for the subtracted class sum**: `‖Q(a, b; s) - Q(a, b; 0)‖ ≤ C √b` for
`0 < a ≤ b ≤ 1`, uniformly for `s ∈ [S₀, S]`, `S₀ > -4m₀²`. -/
theorem exists_norm_qPair_sub_light_le (he : P.e ≠ 0) {S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ ≤ S) :
    ∃ C : ℝ, ∀ a b s : ℝ, 0 < a → a ≤ b → b ≤ 1 → S₀ ≤ s → s ≤ S →
      ‖qPair Φ rep P.e a b s - qPair Φ rep P.e a b 0‖ ≤ C * Real.sqrt b := by
  have hm : -(4 * m₀ ^ 2) < min S₀ 0 := lt_min hS₀ (by nlinarith)
  obtain ⟨C, hC⟩ := exists_norm_qPair_light_le P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he hm
    (min_le_left _ _ |>.trans (hS₀S.trans (le_max_left S 0)))
  refine ⟨2 * C, fun a b s ha hab hb1 h₀ h₁ => ?_⟩
  have h1 := hC a b s ha hab hb1 ((min_le_left _ _).trans h₀) (h₁.trans (le_max_left _ _))
  have h2 := hC a b 0 ha hab hb1 (min_le_right _ _) (le_max_right _ _)
  calc _ ≤ ‖qPair Φ rep P.e a b s‖ + ‖qPair Φ rep P.e a b 0‖ := norm_sub_le _ _
    _ ≤ C * Real.sqrt b + C * Real.sqrt b := add_le_add h1 h2
    _ = 2 * C * Real.sqrt b := by ring

end L7

end QED.GradedProof.RPi4

end
