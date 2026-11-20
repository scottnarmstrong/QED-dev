/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajOne
public import QED.GradedProof.RPi4DecLipF

/-!
# (R-Π₄) step L10, one loop: `MajGrowD` from a bound along one spacelike ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, input
`MajGrowD`. The tilted vector of `s` at `c = √s` is `majRayVec s = √s (1, 0, 1, 1)`, so for
`s ≥ 1` the projection of a covariant tensor is `-W(√s v)²³ / s`
(`QED.GradedProof.RPi4.projS_eq_tilt`). Near `s = 0` the projection of the limit of the weighted
block is Lipschitz (`QED.GradedProof.RPi4.dec_lip_projS_fLim`). So `MajGrowD` needs only one entry
along one ray: `O(s)`, with increments `O(s - s')`. This replaces `MajOneIns` (no statement at
small `s`, no projection of single flavours).

* `majRayVec s`: the ray vector; `MajTiltRay W`: the entry `W(majRayVec s)²³` is `O(s)` with
  increments `O(s - s')` for `s ≥ s' ≥ 1`; closed under sums, constants and agreement on the ray;
* `maj_sRay_of_parts`: Lipschitz on `[0, 2]` and the bounds for `t ≥ 1` give `MajSRay`;
* `maj_projS_rayVec`: `projS W s = -W(majRayVec s)²³ / s` for covariant `W`, `s > 0`;
* `maj_symanzikV_ray`: along the ray `V = V₀ + s R(c)` (the input `V₀ + s B` of the tool
  `QED.GradedProof.RPi4.maj_integral_phi`);
* **`maj_growD_of_tiltRay`**: `MajTiltRay (fLim (decCfg 1 4) …) → MajGrowD`.
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-! ### The ray -/

/-- **The ray vector** `√s (1, 0, 1, 1)`, the tilted vector of `s` at `c = √s`. -/
noncomputable def majRayVec (s : ℝ) : Fin 4 → ℝ := tiltVec (Real.sqrt s) s

/-- **One entry along the ray**: `W(majRayVec s)²³` is `O(s)` for `s ≥ 1`, with increments
`O(s - s')`. -/
def MajTiltRay (W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ‖W (majRayVec s) 2 3‖ ≤ C * s ∧
    ∀ s' : ℝ, 1 ≤ s' → s' ≤ s → ‖W (majRayVec s) 2 3 - W (majRayVec s') 2 3‖ ≤ C * (s - s')

namespace MajTiltRay

variable {W W' : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem zero : MajTiltRay fun _ _ _ => 0 := ⟨0, fun s _ => ⟨by simp, fun s' _ _ => by simp⟩⟩

theorem add (hW : MajTiltRay W) (hW' : MajTiltRay W') :
    MajTiltRay fun k μ ν => W k μ ν + W' k μ ν := by
  obtain ⟨C, hC⟩ := hW
  obtain ⟨D, hD⟩ := hW'
  refine ⟨C + D, fun s hs => ⟨?_, fun s' hs' hss => ?_⟩⟩
  · calc _ ≤ ‖W (majRayVec s) 2 3‖ + ‖W' (majRayVec s) 2 3‖ := norm_add_le _ _
      _ ≤ C * s + D * s := add_le_add (hC s hs).1 (hD s hs).1
      _ = _ := by ring
  · calc _ = ‖(W (majRayVec s) 2 3 - W (majRayVec s') 2 3) +
          (W' (majRayVec s) 2 3 - W' (majRayVec s') 2 3)‖ := by ring_nf
      _ ≤ ‖W (majRayVec s) 2 3 - W (majRayVec s') 2 3‖ +
          ‖W' (majRayVec s) 2 3 - W' (majRayVec s') 2 3‖ := norm_add_le _ _
      _ ≤ C * (s - s') + D * (s - s') :=
          add_le_add ((hC s hs).2 s' hs' hss) ((hD s hs).2 s' hs' hss)
      _ = _ := by ring

theorem const_mul (hW : MajTiltRay W) (a : ℂ) : MajTiltRay fun k μ ν => a * W k μ ν := by
  obtain ⟨C, hC⟩ := hW
  refine ⟨‖a‖ * C, fun s hs => ⟨?_, fun s' hs' hss => ?_⟩⟩
  · rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC s hs).1 (norm_nonneg a)
  · rw [← mul_sub, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hC s hs).2 s' hs' hss) (norm_nonneg a)

theorem sum {ι : Type*} (s : Finset ι) {W : ι → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ s, MajTiltRay (W i)) : MajTiltRay fun k μ ν => ∑ i ∈ s, W i k μ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : MajTiltRay fun _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Agreement of the entry on the ray. -/
theorem congr (hW : MajTiltRay W)
    (e : ∀ s : ℝ, 1 ≤ s → W (majRayVec s) 2 3 = W' (majRayVec s) 2 3) :
    MajTiltRay W' := by
  obtain ⟨C, hC⟩ := hW
  refine ⟨C, fun s hs => ⟨?_, fun s' hs' hss => ?_⟩⟩
  · rw [← e s hs]
    exact (hC s hs).1
  · rw [← e s hs, ← e s' hs']
    exact (hC s hs).2 s' hs' hss

end MajTiltRay

theorem dot_majRayVec {s : ℝ} (hs : 0 ≤ s) :
    Minkowski.dot (majRayVec s) (majRayVec s) = s := by
  unfold majRayVec
  exact dot_tiltVec (by rw [Real.sq_sqrt hs]; linarith)

/-- **The projection along the ray**: `projS W s = -W(majRayVec s)²³ / s` for `s > 0`. -/
theorem maj_projS_rayVec {T : ℝ} {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hcov : TCov T W)
    {s : ℝ} (hs : 0 < s) : projS W s = -W (majRayVec s) 2 3 / (s : ℂ) := by
  have hc : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  rw [projS_eq_tilt hcov hc (by nlinarith [sq_nonneg T]) (by rw [h2]; linarith), h2]
  rfl

/-- **The second Symanzik remainder along the ray**: for line momenta `cᵢ √s v`,
`V = ∑ᵢ zᵢ Mᵢ² + s R(c)`, with `R(c) ≥ 0` the remainder of the coefficient column
(`QED.Integration.TwoLoop.remainder_nonneg`). -/
theorem maj_symanzikV_ray {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (M : Fin (m + 1) → ℝ)
    (z : Fin (m + 1) → ℝ) (cs : Fin (m + 1) → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    QED.Integration.TwoLoop.symanzikV α (fun i => cs i • majRayVec s) M z =
      ∑ i, z i * M i ^ 2 + s * QED.Integration.TwoLoop.remainder α z cs := by
  have h := QED.Integration.TwoLoop.symanzikV_smul_add_smul α M z cs 0
    (P := majRayVec s) (K := 0) (by simp [Minkowski.dot_eq])
  simp only [zero_smul, add_zero, Pi.zero_apply] at h
  rw [h, dot_majRayVec hs]
  simp [Minkowski.dot_eq]

/-! ### From the parts to `MajSRay` -/

/-- **Lipschitz on `[0, 2]` and the bounds for `t ≥ 1` give `MajSRay`.** -/
theorem maj_sRay_of_parts {g : ℝ → ℂ} {L C : ℝ}
    (hL : ∀ s s' : ℝ, s ∈ Icc (0 : ℝ) 2 → s' ∈ Icc (0 : ℝ) 2 → ‖g s - g s'‖ ≤ L * |s - s'|)
    (hC : ∀ t : ℝ, 1 ≤ t → ‖g t‖ ≤ C ∧
      ∀ t' : ℝ, 1 ≤ t' → t' ≤ t → ‖g t - g t'‖ ≤ C * ((t - t') / t')) : MajSRay g := by
  have hL0 : 0 ≤ L := by
    have h := hL 0 2 ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
    have h' : 0 ≤ L * 2 := (norm_nonneg _).trans (by simpa using h)
    linarith
  set K₁ : ℝ := 2 * L + C + ‖g 0‖ with hK₁
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 le_rfl).1
  have hval : ∀ t : ℝ, 0 ≤ t → ‖g t - g 0‖ ≤ K₁ := by
    intro t ht
    rcases le_or_gt t 2 with h2 | h2
    · have h := hL t 0 ⟨ht, h2⟩ ⟨le_rfl, by norm_num⟩
      rw [sub_zero, abs_of_nonneg ht] at h
      have : L * t ≤ L * 2 := mul_le_mul_of_nonneg_left h2 hL0
      linarith [norm_nonneg (g 0)]
    · calc ‖g t - g 0‖ ≤ ‖g t‖ + ‖g 0‖ := norm_sub_le _ _
        _ ≤ C + ‖g 0‖ := add_le_add (hC t (by linarith)).1 le_rfl
        _ ≤ K₁ := by linarith
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hval 0 le_rfl)
  refine ⟨2 * L + C + 2 * K₁, fun t ht => ⟨(hval t ht).trans (by linarith), fun t' ht' htt => ?_⟩⟩
  have hr : 0 ≤ (t - t') / t' := div_nonneg (by linarith) ht'.le
  rcases le_or_gt t 2 with h2 | h2
  · have h := hL t t' ⟨ht, h2⟩ ⟨ht'.le, htt.trans h2⟩
    rw [abs_of_nonneg (by linarith)] at h
    have e : t - t' = t' * ((t - t') / t') := by field_simp
    have h3 : L * (t' * ((t - t') / t')) ≤ L * (2 * ((t - t') / t')) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (htt.trans h2) hr) hL0
    calc ‖g t - g t'‖ ≤ L * (t - t') := h
      _ = L * (t' * ((t - t') / t')) := by rw [← e]
      _ ≤ L * (2 * ((t - t') / t')) := h3
      _ ≤ (2 * L + C + 2 * K₁) * ((t - t') / t') := by nlinarith
  rcases le_or_gt 1 t' with h1 | h1
  · calc ‖g t - g t'‖ ≤ C * ((t - t') / t') := (hC t (h1.trans htt)).2 t' h1 htt
      _ ≤ (2 * L + C + 2 * K₁) * ((t - t') / t') := by nlinarith
  · have hr1 : 1 ≤ (t - t') / t' := by rw [le_div_iff₀ ht']; linarith
    calc ‖g t - g t'‖ = ‖(g t - g 0) - (g t' - g 0)‖ := by ring_nf
      _ ≤ ‖g t - g 0‖ + ‖g t' - g 0‖ := norm_sub_le _ _
      _ ≤ K₁ + K₁ := add_le_add (hval t ht) (hval t' ht'.le)
      _ ≤ 2 * K₁ * ((t - t') / t') := by nlinarith
      _ ≤ (2 * L + C + 2 * K₁) * ((t - t') / t') := by nlinarith

/-- The bounds for `t ≥ 1` of `-W(majRayVec t)²³ / t` from `MajTiltRay`. -/
theorem maj_ray_div_bounds {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (h : MajTiltRay W) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖-W (majRayVec t) 2 3 / (t : ℂ)‖ ≤ C ∧
      ∀ t' : ℝ, 1 ≤ t' → t' ≤ t →
        ‖-W (majRayVec t) 2 3 / (t : ℂ) - -W (majRayVec t') 2 3 / (t' : ℂ)‖ ≤
          C * ((t - t') / t') := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1 le_rfl).1
    linarith
  refine ⟨2 * C, fun t ht => ⟨?_, fun t' ht' htt => ?_⟩⟩
  · have ht0 : 0 < t := by linarith
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0,
      div_le_iff₀ ht0]
    nlinarith [(hC t ht).1]
  · have ht0 : 0 < t := by linarith
    have ht0' : 0 < t' := by linarith
    set a := W (majRayVec t) 2 3
    set b := W (majRayVec t') 2 3
    have e : -a / (t : ℂ) - -b / (t' : ℂ) =
        -((a - b) / (t : ℂ)) - b * (((t' - t : ℝ) : ℂ) / ((t * t' : ℝ) : ℂ)) := by
      have : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
      have : (t' : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0'.ne'
      push_cast
      field_simp
      ring
    have hab := (hC t ht).2 t' ht' htt
    have hb := (hC t' ht').1
    have hr : 0 ≤ (t - t') / t' := div_nonneg (by linarith) ht0'.le
    have h1 : ‖(a - b) / (t : ℂ)‖ ≤ C * ((t - t') / t') := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, div_le_iff₀ ht0]
      calc ‖a - b‖ ≤ C * (t - t') := hab
        _ = C * ((t - t') / t') * t' := by field_simp
        _ ≤ C * ((t - t') / t') * t := mul_le_mul_of_nonneg_left htt (by positivity)
    have h2 : ‖b * (((t' - t : ℝ) : ℂ) / ((t * t' : ℝ) : ℂ))‖ ≤ C * ((t - t') / t') := by
      rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (by positivity : 0 < t * t'), abs_sub_comm,
        abs_of_nonneg (by linarith : 0 ≤ t - t')]
      calc ‖b‖ * ((t - t') / (t * t')) ≤ C * t' * ((t - t') / (t * t')) :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = C * ((t - t') / t') * (t' / t) := by field_simp
        _ ≤ C * ((t - t') / t') * 1 :=
            mul_le_mul_of_nonneg_left ((div_le_one ht0).mpr htt) (by positivity)
        _ = _ := mul_one _
    rw [e]
    calc _ ≤ ‖(a - b) / (t : ℂ)‖ + ‖b * (((t' - t : ℝ) : ℂ) / ((t * t' : ℝ) : ℂ))‖ := by
          rw [← norm_neg ((a - b) / (t : ℂ))]
          exact norm_sub_le _ _
      _ ≤ C * ((t - t') / t') + C * ((t - t') / t') := add_le_add h1 h2
      _ = _ := by ring

/-! ### `MajGrowD` -/

/-- **(L10) `MajGrowD` from one entry along the ray.** -/
theorem maj_growD_of_tiltRay (P : Params) (he : P.e ≠ 0)
    (h : MajTiltRay (fLim (decCfg 1 4) (fun _ => 0) P.e fun _ => 1)) : MajGrowD P.e := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  set W := fLim (decCfg 1 4) (fun _ => 0) P.e fun _ => 1 with hW
  have hT : TCov (2 * 1) W :=
    tcov_fLim (decCfg 1 4) (fun _ => 0) one_pos hmass (fun _ => rfl) hpv.1 hpv.2 P he _
  obtain ⟨L, hL⟩ := dec_lip_projS_fLim P (decCfg 1 4) (fun _ => 0) one_pos hmass (fun _ => rfl)
    hpv.1 hpv.2 he (fun _ => 1) (S₀ := -1) (S := 2) (by norm_num) (by norm_num)
  obtain ⟨C, hC⟩ := maj_ray_div_bounds h
  have hg : MajSRay (projS W) := by
    refine maj_sRay_of_parts (L := L) (C := C) (fun s s' hs hs' => hL s s'
      ⟨by linarith [hs.1], hs.2⟩ ⟨by linarith [hs'.1], hs'.2⟩) fun t ht => ?_
    rw [maj_projS_rayVec hT (by linarith)]
    refine ⟨(hC t ht).1, fun t' ht' htt => ?_⟩
    rw [maj_projS_rayVec hT (by linarith)]
    exact (hC t ht).2 t' ht' htt
  refine maj_growD_of_sRay ((hg.affine (I / (P.e : ℂ) ^ 2) (projS W 0)).congr fun t _ => ?_)
  simp only [decD₀, hW]
  ring

end QED.GradedProof.RPi4

end
