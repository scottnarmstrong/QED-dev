/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKAsmLam
public import QED.ChainProof.SetCKFormOS
public import QED.ChainProof.SetCKFormXE
public import QED.ChainProof.SetCKFormXFub

/-!
# Set (c), Stage K, assembly: the Stieltjes identity from the outer-corner density

Helper level (no frozen statement). The value theorem consumes `H_tot = H_λ` almost everywhere
on `(0, 1)` (`isSetCKStieltjes_of_hTot_ae`), where `H_tot = setCKHTot` is the sum of the six
group weights and `H_λ = ∫₀^X λ⁽⁴⁾ Q`. Five of the six weights are known as `H_ρ` of a closed-form
density: `ρ_L`, `ρ_S` by definition, `ρ_C` (`setCKRhoH_rhoCornIn_eq`), `ρ_X`
(`crossTH_ae_eq_rhoCrossX`), `ρ_oS` (`scOutSH_ae_eq_setCKRhoH`). This file proves:

* the interval integrability of `ρ Q` on `[0, X]` for each of the six densities (for `ρ_X` at
  almost every `X`; for `ρ_oC` from the sum identity `setCKRhoSum_eq_setCLambda`);
* **`setCKHTot_ae_eq_of_scOutCH`**: if the outer-massive corner weight is `H_ρ` of `ρ_oC`
  (`scOutCH = setCKRhoH rhoScOutC` a.e.), then `H_tot = H_λ` a.e.;
* **`isSetCKStieltjes_of_scOutCH`** and **`setCKDisp_eq_aSetC_of_scOutCH`**: the Stieltjes
  identity (S) and the set (c) value `∫₀¹ ρ(v) A_(c)(4/(1 - v²)) dv = aSetC` under the same
  single hypothesis.
-/

@[expose] public section

open Real Set Filter MeasureTheory QED.Polylog

namespace QED.ChainProof.SetCK

open QED.Chain QED.TwoLoop.UnitLLink

variable {X : ℝ}

theorem setCKAsm_continuousOn_Q (hX : X < 1) : ContinuousOn setCKQ (Icc 0 X) := by
  unfold setCKQ
  exact continuousOn_id.pow 2 |>.div (continuousOn_const.sub continuousOn_id)
    fun x hx => by linarith [hx.2]

/-- `ρ Q` is interval integrable on `[0, X]` if `ρ Q/(Q + 1)` is integrable on `(0, 1)`. -/
theorem setCKAsm_intervalIntegrable_of_div {ρ : ℝ → ℝ}
    (hρ : IntegrableOn (fun x => ρ x * (setCKQ x / (setCKQ x + 1))) (Ioo 0 1))
    (hX : X ∈ Ioo (0 : ℝ) 1) : IntervalIntegrable (fun x => ρ x * setCKQ x) volume 0 X := by
  have hi : IntegrableOn (fun x => ρ x * (setCKQ x / (setCKQ x + 1))) (Icc 0 X) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hρ.mono_set (Ioo_subset_Ioo_right hX.2.le)
  have hc : ContinuousOn (fun x => setCKQ x + 1) (Icc 0 X) :=
    (setCKAsm_continuousOn_Q hX.2).add continuousOn_const
  have hm := hi.mul_continuousOn hc isCompact_Icc
  refine (IntegrableOn.intervalIntegrable (by rwa [uIcc_of_le hX.1.le])).congr_uIoo ?_
  intro x hx
  rw [uIoo_of_le hX.1.le] at hx
  have hQ := setCKQ_nonneg ⟨hx.1.le, (hx.2.trans hX.2).le⟩
  have : setCKQ x + 1 ≠ 0 := by linarith
  simp only
  field_simp

theorem setCKAsm_ii_rhoL (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => rhoL x * setCKQ x) volume 0 X :=
  setCKAsm_intervalIntegrable_of_div (integrableOn_rhoL_mul one_pos) hX

theorem setCKAsm_ii_rhoSelfIn (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => rhoSelfIn x * setCKQ x) volume 0 X :=
  setCKAsm_intervalIntegrable_of_div (integrableOn_rhoSelfIn_mul one_pos) hX

theorem setCKAsm_ii_rhoCornC (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => rhoCornC x * setCKQ x) volume 0 X := by
  refine setCKAsm_intervalIntegrable_of_div ?_ hX
  exact (integrableOn_rhoCornIn_mul one_pos).congr
    (rhoCornIn_ae_eq.mono fun x hx => by simp only [hx])

theorem setCKAsm_ii_setCLambda (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => setCLambda x * setCKQ x) volume 0 X :=
  setCKAsm_intervalIntegrable_of_div (integrableOn_setCLambda_mul one_pos) hX

theorem setCKAsm_ii_rhoScOutS (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => rhoScOutS x * setCKQ x) volume 0 X := by
  refine ((continuousOn_rhoScOutSQ hX.2).intervalIntegrable_of_Icc hX.1.le).congr_uIoo ?_
  intro x hx
  rw [uIoo_of_le hX.1.le] at hx
  exact (rhoScOutS_mul_setCKQ ⟨hx.1, hx.2.trans hX.2⟩).symm

/-- `ρ_X Q` is interval integrable on `[0, X]` for almost every `X ∈ (0, 1)`. -/
theorem setCKAsm_ae_ii_rhoCrossX :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntervalIntegrable (fun x => rhoCrossX x * setCKQ x) volume 0 X := by
  have h' : ∀ᵐ x ∂volume, x ∈ Ioo (0 : ℝ) 1 → formXI x = formXIT x :=
    (ae_restrict_iff' measurableSet_Ioo).1 formXI_ae_eq_formXIT
  filter_upwards [crossTH_ae_eq_formXI, ae_restrict_mem measurableSet_Ioo] with X hI hX
  have hT : IntegrableOn (fun x => setCKdQ x * formXIT x) (Ioo 0 X) := by
    refine hI.1.congr_fun_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    filter_upwards [h'] with x hx hxX
    rw [hx ⟨hxX.1, hxX.2.trans hX.2⟩]
  have hc : ContinuousOn (fun x => formXe1M x / (1 - x)) (Icc 0 X) := by
    unfold formXe1M
    refine ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) (by fun_prop) ?_
    · intro x hx; have := hx.2; have := hX.2; intro h; linarith [show x = 1 by linarith]
    · intro x hx; have := hx.2; have := hX.2; intro h; linarith [show x = 1 by linarith]
  have hE : IntegrableOn (fun x => formXe1M x / (1 - x)) (Ioo 0 X) :=
    (hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hS : IntegrableOn (fun x => rhoCrossX x * setCKQ x) (Ioo 0 X) := by
    refine (hE.add hT).congr_fun (fun x hx => ?_) measurableSet_Ioo
    exact formXIT_eq ⟨hx.1, hx.2.trans hX.2⟩
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hX.1.le).2 hS

theorem setCKAsm_ii_rhoScOutC (hX : X ∈ Ioo (0 : ℝ) 1)
    (hXc : IntervalIntegrable (fun x => rhoCrossX x * setCKQ x) volume 0 X) :
    IntervalIntegrable (fun x => rhoScOutC x * setCKQ x) volume 0 X := by
  refine ((setCKAsm_ii_setCLambda hX).sub (((((setCKAsm_ii_rhoL hX).add
    (setCKAsm_ii_rhoSelfIn hX)).add (setCKAsm_ii_rhoCornC hX)).add (hXc.const_mul 2)).add
    (setCKAsm_ii_rhoScOutS hX))).congr_uIoo ?_
  intro x hx
  rw [uIoo_of_le hX.1.le] at hx
  have h := setCKRhoSum_eq_setCLambda ⟨hx.1, hx.2.trans hX.2⟩
  beta_reduce
  rw [← h]
  ring

/-- **`H_tot = H_λ` from the outer-corner density.** -/
theorem setCKHTot_ae_eq_of_scOutCH
    (h : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), scOutCH X = setCKRhoH rhoScOutC X) :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), setCKHTot X = setCKRhoH setCLambda X := by
  filter_upwards [crossTH_ae_eq_rhoCrossX, scOutSH_ae_eq_setCKRhoH, h, setCKAsm_ae_ii_rhoCrossX,
    ae_restrict_mem measurableSet_Ioo] with X hXc hoS hoC iX hX
  have iL := setCKAsm_ii_rhoL hX
  have iS := setCKAsm_ii_rhoSelfIn hX
  have iC := setCKAsm_ii_rhoCornC hX
  have iO := setCKAsm_ii_rhoScOutS hX
  have iD := setCKAsm_ii_rhoScOutC hX iX
  have e : ∫ x in (0 : ℝ)..X, setCLambda x * setCKQ x =
      ∫ x in (0 : ℝ)..X, (rhoL x * setCKQ x + rhoSelfIn x * setCKQ x + rhoCornC x * setCKQ x +
        2 * (rhoCrossX x * setCKQ x) + rhoScOutS x * setCKQ x + rhoScOutC x * setCKQ x) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hX.1.le fun x hx => ?_
    rw [← setCKRhoSum_eq_setCLambda ⟨hx.1, hx.2.trans hX.2⟩]
    ring
  rw [setCKHTot, setCKRhoH_rhoCornIn_eq hX, hXc, hoS, hoC]
  simp only [setCKRhoH]
  rw [e,
    intervalIntegral.integral_add ((((iL.add iS).add iC).add (iX.const_mul 2)).add iO) iD,
    intervalIntegral.integral_add (((iL.add iS).add iC).add (iX.const_mul 2)) iO,
    intervalIntegral.integral_add ((iL.add iS).add iC) (iX.const_mul 2),
    intervalIntegral.integral_add (iL.add iS) iC, intervalIntegral.integral_add iL iS,
    intervalIntegral.integral_const_mul]

/-- **The Stieltjes identity (S) from the outer-corner density.** -/
theorem isSetCKStieltjes_of_scOutCH
    (h : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), scOutCH X = setCKRhoH rhoScOutC X) :
    IsSetCKStieltjes :=
  isSetCKStieltjes_of_hTot_ae (setCKHTot_ae_eq_of_scOutCH h)

/-- **The set (c) value from the outer-corner density**: `setCKDisp = aSetC`. -/
theorem setCKDisp_eq_aSetC_of_scOutCH
    (h : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), scOutCH X = setCKRhoH rhoScOutC X) :
    setCKDisp = aSetC :=
  setCKDisp_eq_aSetC (isSetCKStieltjes_of_scOutCH h)

end QED.ChainProof.SetCK

end
