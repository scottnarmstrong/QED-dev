/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmBNode

/-!
# Set (a), stage D: the dispersion of the `VB` finite part at a fixed node

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. At unit
mass and a node `(ρ, β, w)` of the open cube with `w(1-w) ≠ β(1-β)` (the thresholds of `A_w`
and `A_β` differ), the finite part of the `VB` class has a once-subtracted dispersive form with
the density `ksWnB` and no threshold term:

  `ksUb0 1 s ρ β w - ksUb0 1 0 ρ β w = ∫_{T > 4} ksWnB ρ β w T · s/(T(s + T)) dT`,

for `s > -4`. Off the thresholds the density is a combination of the interval densities of the
`G₀ log(1 + z)/A_β` and `K(z)` nodes (`ksWB_T1_node`, `ksWB_K_node`) and the half-line
densities of `log(1 + s/x)` and `log²(1 + s/x)` (`ksWB_ksWnB_eq`).

Main result:

* **`ksWB_node_disp`**: the integrability and the dispersion at a node.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

theorem ksWB_ae_ne (c x : ℝ) : ∀ᵐ T ∂(volume.restrict (Ioi c)), T ≠ x :=
  ae_restrict_of_ae (by rw [ae_iff]; simp)

section Disp

variable {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
  (hab : w * (1 - w) ≠ β * (1 - β))
include hρ hβ hw hab

omit hρ hβ hw in
theorem ksWB_q_ne_r : ksWBq w ≠ ksWBr β := by
  intro h
  exact hab (inv_injective h)

theorem ksWB_four_le_p : 4 ≤ ksWBp ρ β w := by
  obtain ⟨-, hq4, -, hr4, hl0, -⟩ := ksWB_basic hρ hβ hw
  have h := (ksWB_mem_uIcc (ksWB_q_ne_r hab) hl0
    (left_mem_uIcc : ksWBp ρ β w ∈ uIcc (ksWBp ρ β w) (ksWBq w))).2
  exact le_trans (le_min hq4 hr4) h

/-- **The dispersion of the `VB` finite part at a node** (unit mass, `s > -4`): the density
times the kernel is integrable on `T > 4`, and it gives the subtracted finite part. -/
theorem ksWB_node_disp {s : ℝ} (hs : -4 < s) :
    IntegrableOn (fun T => ksWnB ρ β w T * (s / (T * (s + T)))) (Ioi 4) ∧
      ksUb0 1 s ρ β w - ksUb0 1 0 ρ β w =
        ∫ T in Ioi 4, ksWnB ρ β w T * (s / (T * (s + T))) := by
  obtain ⟨hq0, hq4, hr0, hr4, hl0, hY, hY1, hD0⟩ := ksWB_basic hρ hβ hw
  have hqr := ksWB_q_ne_r hab
  have hp4 := ksWB_four_le_p hρ hβ hw hab
  have hp0 : 0 < ksWBp ρ β w := by linarith
  have hpdef : ksWBp ρ β w = (ksWBl ρ β w * ksWBr β + ksWBq w) / (1 + ksWBl ρ β w) := rfl
  have hsq : -ksWBq w < s := by linarith
  have hsr : -ksWBr β < s := by linarith
  have hsp : -ksWBp ρ β w < s := by linarith
  -- the two interval nodes
  have N1 := ksWB_T1_node hq0 hr0 hqr hl0 (ksWBg0 ρ β w / ρ) (ksWBg1 ρ β w / ρ) hsq hsr
  have NK := ksWB_K_node hq0 hr0 hqr hl0 hsq hsr
  rw [← hpdef] at N1 NK
  have i1 := ksWB_intervalIntegrable_T1 hq0 hr0 hqr hl0 (ksWBg0 ρ β w / ρ) (ksWBg1 ρ β w / ρ)
    hsq hsr
  have iK := ksWB_intervalIntegrable_K hq0 hr0 hqr hl0 hsq hsr
  rw [← hpdef] at i1 iK
  -- the half-line nodes
  have Lp := ksD_log_eq_integral hp0 hsp
  have Lq := ksD_log_eq_integral hq0 hsq
  have Lr := ksD_log_eq_integral hr0 hsr
  have Sq := ksW_logSq_eq_integral hq0 hsq
  have Sr := ksW_logSq_eq_integral hr0 hsr
  have ikp := ksD_integrableOn_logNodeKer hp0 hsp
  have ikq := ksD_integrableOn_logNodeKer hq0 hsq
  have ikr := ksD_integrableOn_logNodeKer hr0 hsr
  have isq := ksW_integrableOn_logSq hq0 hsq
  have isr := ksW_integrableOn_logSq hr0 hsr
  -- the decomposition of the density
  set Q1 : ℝ → ℝ := fun T => ((ksWBg0 ρ β w / ρ - ksWBg1 ρ β w / ρ * T) *
      (ksWBr β / (ksWBr β - T)) * (s / (T * (s + T))) - ρ * ksUcB w *
        ((log (ksWBl ρ β w * (ksWBr β - T)) - log (T - ksWBq w)) * (s / (T * (s + T))))) *
      ((if ksWBp ρ β w < T then 1 else 0) - (if ksWBq w < T then 1 else 0)) with hQ1
  set Qp : ℝ → ℝ := fun T => s / (T * (s + T)) * (if ksWBp ρ β w < T then 1 else 0) with hQp
  set Qq : ℝ → ℝ := fun T => s / (T * (s + T)) * (if ksWBq w < T then 1 else 0) with hQq
  set Qr : ℝ → ℝ := fun T => s / (T * (s + T)) * (if ksWBr β < T then 1 else 0) with hQr
  set Sqq : ℝ → ℝ := fun T => 2 * log ((T - ksWBq w) / ksWBq w) * (s / (T * (s + T))) *
    (if ksWBq w < T then 1 else 0) with hSqq
  set Srr : ℝ → ℝ := fun T => 2 * log ((T - ksWBr β) / ksWBr β) * (s / (T * (s + T))) *
    (if ksWBr β < T then 1 else 0) with hSrr
  set c₁ := ksUq ρ β w * ksDYmax β w / 2 + (1 - ρ)⁻¹ * ksUf0 β w with hc₁
  set c₂ := (1 - ρ)⁻¹ * ksUf0 β w with hc₂
  set c₃ := ρ * ksUcB w * log (ksDYmax β w / ρ) with hc₃
  set c₄ := ρ * ksUcB w / 2 with hc₄
  set c₅ := ksUf0 β w / 2 with hc₅
  have hae : ∀ᵐ T ∂(volume.restrict (Ioi (4 : ℝ))), ksWnB ρ β w T * (s / (T * (s + T))) =
      Q1 T - c₁ * Qp T + c₂ * Qr T - c₃ * Qq T + c₄ * Sqq T + c₅ * Srr T := by
    filter_upwards [ksWB_ae_ne 4 (ksWBp ρ β w), ksWB_ae_ne 4 (ksWBq w),
      ksWB_ae_ne 4 (ksWBr β)] with T h1 h2 h3
    rw [ksWB_ksWnB_eq hρ hβ hw h1 h2 h3]
    simp only [hQ1, hQp, hQq, hQr, hSqq, hSrr, hc₁, hc₂, hc₃, hc₄, hc₅]
    ring
  have iQ1 : IntegrableOn Q1 (Ioi 4) := ksWB_integrableOn_ind_sub (i1.sub (iK.const_mul _))
  have iQp : IntegrableOn Qp (Ioi 4) := ksWB_integrableOn_ind ikp
  have iQq : IntegrableOn Qq (Ioi 4) := ksWB_integrableOn_ind ikq
  have iQr : IntegrableOn Qr (Ioi 4) := ksWB_integrableOn_ind ikr
  have iSq : IntegrableOn Sqq (Ioi 4) := ksWB_integrableOn_ind isq
  have iSr : IntegrableOn Srr (Ioi 4) := ksWB_integrableOn_ind isr
  have iall := ((((iQ1.sub (iQp.const_mul c₁)).add (iQr.const_mul c₂)).sub
    (iQq.const_mul c₃)).add (iSq.const_mul c₄)).add (iSr.const_mul c₅)
  refine ⟨iall.congr_fun_ae (EventuallyEq.symm hae), ?_⟩
  rw [integral_congr_ae hae]
  have h1 : IntegrableOn (fun T => Q1 T - c₁ * Qp T) (Ioi 4) := iQ1.sub (iQp.const_mul c₁)
  have h2 : IntegrableOn (fun T => Q1 T - c₁ * Qp T + c₂ * Qr T) (Ioi 4) :=
    h1.add (iQr.const_mul c₂)
  have h3 : IntegrableOn (fun T => Q1 T - c₁ * Qp T + c₂ * Qr T - c₃ * Qq T) (Ioi 4) :=
    h2.sub (iQq.const_mul c₃)
  have h4 : IntegrableOn (fun T => Q1 T - c₁ * Qp T + c₂ * Qr T - c₃ * Qq T + c₄ * Sqq T)
      (Ioi 4) := h3.add (iSq.const_mul c₄)
  rw [integral_add h4 (iSr.const_mul c₅), integral_add h3 (iSq.const_mul c₄),
    integral_sub h2 (iQq.const_mul c₃), integral_add h1 (iQr.const_mul c₂),
    integral_sub iQ1 (iQp.const_mul c₁), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have hQ1v : ∫ T in Ioi 4, Q1 T = (∫ t in ksWBp ρ β w..ksWBq w,
      (ksWBg0 ρ β w / ρ - ksWBg1 ρ β w / ρ * t) * (ksWBr β / (ksWBr β - t)) *
        (s / (t * (s + t)))) - ρ * ksUcB w * ∫ t in ksWBp ρ β w..ksWBq w,
      (log (ksWBl ρ β w * (ksWBr β - t)) - log (t - ksWBq w)) * (s / (t * (s + t))) := by
    have := ksWB_integral_ind_sub hp4 hq4 (i1.sub (iK.const_mul (ρ * ksUcB w)))
    rw [intervalIntegral.integral_sub i1 (iK.const_mul _),
      intervalIntegral.integral_const_mul] at this
    exact this
  have hQpv : ∫ T in Ioi 4, Qp T = ∫ t in Ioi (ksWBp ρ β w), s / (t * (s + t)) :=
    ksWB_integral_ind hp4
  have hQqv : ∫ T in Ioi 4, Qq T = ∫ t in Ioi (ksWBq w), s / (t * (s + t)) :=
    ksWB_integral_ind hq4
  have hQrv : ∫ T in Ioi 4, Qr T = ∫ t in Ioi (ksWBr β), s / (t * (s + t)) :=
    ksWB_integral_ind hr4
  have hSqv : ∫ T in Ioi 4, Sqq T =
      ∫ t in Ioi (ksWBq w), 2 * log ((t - ksWBq w) / ksWBq w) * (s / (t * (s + t))) :=
    ksWB_integral_ind hq4
  have hSrv : ∫ T in Ioi 4, Srr T =
      ∫ t in Ioi (ksWBr β), 2 * log ((t - ksWBr β) / ksWBr β) * (s / (t * (s + t))) :=
    ksWB_integral_ind hr4
  rw [hQ1v, hQpv, hQqv, hQrv, hSqv, hSrv, ← N1, ← NK, ← Lp, ← Lq, ← Lr, ← Sq, ← Sr,
    ksWB_ksUb0_eq hρ hβ hw hs, ksWB_ksUb0_eq hρ hβ hw (σ := 0) (by norm_num)]
  simp only [hc₁, hc₂, hc₃, hc₄, hc₅, mul_zero, add_zero, zero_div, log_one, sub_zero,
    div_self hr0.ne', mul_one]
  ring

end Disp

end QED.ChainProof.SetAKS

end
