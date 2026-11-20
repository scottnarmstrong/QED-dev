/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecContF
public import QED.GradedProof.RPi4DecContV

/-!
# (R-Π₄) step L9: the per-flavour function is continuous at `s = 0` (`DecContT`)

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
regularity input `DecContT` of `QED.GradedProof.RPi4.dec_scalAff_of_weak`.

* `dec_continuousAt_qPair`: at a fixed photon pair `0 < a ≤ b` the projected class sum
  `qPair(a, b; ·)` is continuous at every `s` of the region (the tilted representation
  `QED.GradedProof.RPi4.qPair_eq_tilt`, the class values `vVal` and the mass part, each continuous
  along the tilt segment);
* `dec_continuousAt_asmPolLim`: the photon-regulator limit `asmPolLim` is continuous at `s = 0`,
  given the face-limit identity: the L8 rate `QED.GradedProof.RPi4.asm_exists_norm_sub_polLim_le`
  is uniform for `s` in a neighbourhood of `0`;
* **`dec_contT : DecFaceGen P.e → DecContT P.e`**;
* `dec_scalAff_of_lip48`: `DecScalAff` modulo `DecFaceGen`, `DecLipD48` and `DecLipT48`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.WickModel (Params)

section QPair

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The projected class sum at a fixed photon pair is continuous in `s`** on the region. -/
theorem dec_continuousAt_qPair (P : Params) (he : P.e ≠ 0) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s) :
    ContinuousAt (qPair Φ rep P.e a b) s := by
  have hb : 0 < b := ha.trans_le hab
  set c : ℝ := 1 + |s|
  have hc : 0 < c := by positivity
  have hsc : s + 1 < 2 * c ^ 2 := by
    have := le_abs_self s
    nlinarith [abs_nonneg s]
  set S₀ : ℝ := (s - 4 * m₀ ^ 2) / 2
  have hS₀ : -(4 * m₀ ^ 2) < S₀ := by simp only [S₀]; linarith
  have hS₀' : -(2 * m₀) ^ 2 < S₀ := by nlinarith
  have hS₀s : S₀ < s := by simp only [S₀]; nlinarith
  have hS₀S : S₀ < s + 1 := hS₀s.trans (lt_add_one s)
  have hmem : Icc S₀ (s + 1) ∈ 𝓝 s := Icc_mem_nhds hS₀s (lt_add_one s)
  have hseg := fun u (hu : |u| ≤ 1 / 2) => (dot_lineK_tilt_mem (c := c) hsc hS₀S.le hu).1
  have hA := dec_continuousOn_tilt hS₀S hsc
    (dec_segCont_vVal_VA Φ hm₀ hmass P.e hS₀' hseg ha hab 2 3)
  have hB := dec_continuousOn_tilt hS₀S hsc
    (dec_segCont_vVal_VB Φ hm₀ hmass P.e hS₀' hseg ha hab 2 3)
  have hC := dec_continuousOn_tilt hS₀S hsc
    (dec_segCont_vVal_VC Φ hm₀ hmass P.e hS₀' hseg ha hab 2 3)
  have hF := dec_continuousOn_fLim_tilt P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he
    (fun g => ctPair P.e (Φ.mass g) a b) hS₀ hS₀S hsc 2 3
  have hsum := (((hA.add hB).add hC).add hF).const_mul (-I / ((c ^ 2 : ℝ) : ℂ))
  refine (hsum.continuousAt hmem).congr ?_
  filter_upwards [hmem] with t ht
  have ht0 : -(4 * m₀ ^ 2) < t := hS₀.trans_le ht.1
  have ht2 : t < 2 * c ^ 2 := by linarith [ht.2]
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot (tiltVec c t) (tiltVec c t) := by
    rw [dot_tiltVec ht2.le]
    exact ht0
  rw [qPair_eq_tilt Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hc ht0 ht2,
    wV_eq_vVal_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    wV_eq_vVal_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    wV_eq_vVal_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk]
  simp only [Pi.add_apply]

/-- **The photon-regulator limit is continuous at `s = 0`**, given the face-limit identity on a
neighbourhood: the L8 rate is uniform in `s` there. -/
theorem dec_tendsto_asmPolLim_zero (P : Params) (he : P.e ≠ 0)
    (hId : ∀ s : ℝ, min (-(2 * m₀ ^ 2)) 0 ≤ s → s ≤ max (m₀ ^ 2) 0 →
      FaceLimitId Φ rep P.e m₀ (1 + |max (m₀ ^ 2) 0|) s) :
    Tendsto (asmPolLim Φ rep P.e) (𝓝 0) (𝓝 0) := by
  have hS₀ : -(4 * m₀ ^ 2) < -(2 * m₀ ^ 2) := by nlinarith
  obtain ⟨C, hC⟩ := asm_exists_norm_sub_polLim_le Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he
    (S₀ := -(2 * m₀ ^ 2)) (S := m₀ ^ 2) hS₀ hId
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hr := (dec_tendsto_rate C).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨Λ, hΛ⟩ := (hr.and (eventually_ge_atTop 1)).exists
  have hΛ0 : 0 < Λ := one_pos.trans_le hΛ.2
  have hab : Λ⁻¹ ≤ Λ := (inv_le_one_of_one_le₀ hΛ.2).trans hΛ.2
  have hQ := dec_continuousAt_qPair Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he (inv_pos.2 hΛ0) hab
    (s := 0) (by nlinarith)
  have hQt : Tendsto (fun s => qPair Φ rep P.e Λ⁻¹ Λ s - qPair Φ rep P.e Λ⁻¹ Λ 0) (𝓝 0)
      (𝓝 0) := by
    have := hQ.tendsto.sub_const (qPair Φ rep P.e Λ⁻¹ Λ 0)
    rwa [sub_self] at this
  have hev := (Metric.tendsto_nhds.mp hQt) (ε / 2) (half_pos hε)
  have hI : Icc (-(2 * m₀ ^ 2)) (m₀ ^ 2) ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by nlinarith) (by positivity)
  filter_upwards [hev, hI] with s hs hsI
  rw [dist_zero_right]
  rw [dist_zero_right] at hs
  have h1 := hC s hsI.1 hsI.2 Λ⁻¹ Λ (inv_pos.2 hΛ0) (inv_le_one_of_one_le₀ hΛ.2) hΛ.2
  have h2 := norm_sub_le (qPair Φ rep P.e Λ⁻¹ Λ s - qPair Φ rep P.e Λ⁻¹ Λ 0)
    (qPair Φ rep P.e Λ⁻¹ Λ s - qPair Φ rep P.e Λ⁻¹ Λ 0 - asmPolLim Φ rep P.e s)
  rw [sub_sub_cancel] at h2
  have h3 := hΛ.1
  linarith

end QPair

/-- **`DecContT`: the per-flavour function is continuous at `s = 0`**, given the generic
face-limit identity. -/
theorem dec_contT (P : Params) (hF : DecFaceGen P.e) : DecContT P.e := by
  intro x hx
  by_cases he : P.e = 0
  · have e0 : decT₀ P.e 1 x = fun _ => 0 := funext fun s => by simp [decT₀, he]
    rw [e0]
    exact tendsto_const_nhds
  set m₀ : ℝ := min 1 x with hm₀d
  have hm₀ : 0 < m₀ := dec_min_one_pos hx
  have hmass : ∀ g, m₀ ≤ (decCfg 1 x).mass g := dec_cfg_mass_ge (min_le_left _ _) hm₀
    (dec_min_one_sq_le hx)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero hx.le
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  have h := dec_tendsto_asmPolLim_zero (decCfg 1 x) (fun _ => 0) hm₀ hmass hrep hpv.1 hpv.2 P
    he fun s h₀ h₁ => hF (Fin 3) (decCfg 1 x) (fun _ => 0) m₀ hm₀ hmass hrep hpv.1 hpv.2 _ s
      (by positivity) ((lt_min (by nlinarith) (by nlinarith)).trans_le h₀)
      (h₁.trans_lt (asm_max_lt_two_mul_sq _))
  have h' := h.div_const ((P.e : ℂ) ^ 4)
  rw [zero_div] at h'
  exact h'

/-- **`DecScalAff` modulo `DecFaceGen` and the two Lipschitz bounds at `x = 4, 8`** (the
continuity inputs `DecContD`, `DecContT` are now proved). -/
theorem dec_scalAff_of_lip48 (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hD48 : DecLipD48 P.e) (hT48 : DecLipT48 P.e) : DecScalAff P.e :=
  dec_scalAff_of_weak P he hF (dec_contD P) hD48 (dec_contT P hF) hT48

end QED.GradedProof.RPi4

end
