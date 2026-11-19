/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInBd
public import QED.ChainProof.SetCKCornInCV

/-!
# Set (c), Stage K, group G2: integrability of the dominating function, measurability

Helper level (no frozen statement). The dominating function `cornInDom` of `SetCKCornInBd` is a
sum of `-log y₃`, `-log(1-Y)`, `-log x`, constants and the product `(√(1-Y))⁻¹ (√x)⁻¹`, each
integrable on `(0, 1)` in its variables, so it is integrable on the cube `(0, 1)³` for the
product measure `μ₁ ⊗ (μ₁ ⊗ μ₁)`, `μ₁ = volume|(0,1)` (**`integrable_cornInDom`**). Also: the
total weight `K_tot` is jointly measurable (`measurable_cornInKt`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

theorem cornIn_integrableOn_one_sub {f : ℝ → ℝ} (h : IntegrableOn f (Ioo 0 1)) :
    IntegrableOn (fun x => f (1 - x)) (Ioo 0 1) := by
  have h1 : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 h
  have h2 := h1.comp_sub_left 1
  norm_num at h2
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h2.symm

theorem integrableOn_neg_log_Ioo : IntegrableOn (fun x => -log x) (Ioo 0 1) :=
  ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
    intervalIntegral.intervalIntegrable_log').neg

theorem integrableOn_inv_sqrt_Ioo : IntegrableOn (fun x => (√x)⁻¹) (Ioo 0 1) := by
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2
    (by norm_num : (-1 : ℝ) < -(1 / 2))
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
  simp only
  rw [rpow_neg hx.1.le, sqrt_eq_rpow]

/-- **The dominating function is integrable on the cube.** -/
theorem integrable_cornInDom {t : ℝ} (C₁ C₂ : ℝ) :
    Integrable (fun p : ℝ × ℝ × ℝ => cornInDom t C₁ C₂ p.1 p.2.1 p.2.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have iL : Integrable (fun x => -log x) μ := integrableOn_neg_log_Ioo
  have iL1 : Integrable (fun x => -log (1 - x)) μ :=
    cornIn_integrableOn_one_sub integrableOn_neg_log_Ioo
  have iS : Integrable (fun x => (√x)⁻¹) μ := integrableOn_inv_sqrt_Ioo
  have iS1 : Integrable (fun x => (√(1 - x))⁻¹) μ :=
    cornIn_integrableOn_one_sub integrableOn_inv_sqrt_Ioo
  have a : Integrable (fun p : ℝ × ℝ × ℝ => -log p.2.1) (μ.prod (μ.prod μ)) :=
    (iL.comp_fst μ).comp_snd μ
  have b : Integrable (fun p : ℝ × ℝ × ℝ => -log (1 - p.1)) (μ.prod (μ.prod μ)) :=
    iL1.comp_fst (μ.prod μ)
  have c : Integrable (fun p : ℝ × ℝ × ℝ => -log p.2.2) (μ.prod (μ.prod μ)) :=
    (iL.comp_snd μ).comp_snd μ
  have d : Integrable (fun p : ℝ × ℝ × ℝ => (√(1 - p.1))⁻¹ * (√p.2.2)⁻¹) (μ.prod (μ.prod μ)) :=
    iS1.mul_prod (iS.comp_snd μ)
  set m := cornInM0 t
  have hs := ((((a.add b).add c).const_mul (C₁ / m)).add (d.const_mul (C₂ / m))).add
    (integrable_const (C₁ + 1 / (2 * m)))
  refine hs.congr (Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, cornInDom]
  ring

theorem measurable_cornInKt :
    Measurable fun p : ℝ × ℝ × ℝ × ℝ => cornInKt p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hW0 : Measurable fun p : ℝ × ℝ × ℝ × ℝ => cornInW0 p.1 p.2.1 p.2.2.1 := by
    unfold cornInW0 betaG cornerG
    fun_prop
  have hOm : Measurable fun p : ℝ × ℝ × ℝ × ℝ =>
      cornInOm (cornerA1 p.2.2.1 p.2.1 (p.1 - p.2.1)) (cornerA2 p.2.2.1 p.2.1 (p.1 - p.2.1))
        (cornerC1 p.2.2.1 p.2.1 (p.1 - p.2.1)) (cornerC2 p.2.2.1 p.2.1 (p.1 - p.2.1))
        (cornerC3 p.2.2.1 p.2.1 (p.1 - p.2.1)) p.2.2.1 p.2.2.2 := by
    unfold cornInOm cornerA1 cornerA2 cornerC1 cornerC2 cornerC3 cornerG cornerQ cornerR
      QED.TwoLoop.UnitSCReduce.cornerP1 QED.TwoLoop.UnitSCReduce.cornerP2
    fun_prop
  have hC0 : Measurable fun p : ℝ × ℝ × ℝ × ℝ => -(cornerC0 p.2.2.1 / p.2.2.1) := by
    unfold cornerC0
    fun_prop
  have hD : Measurable fun p : ℝ × ℝ × ℝ × ℝ => cornInDPhi p.1 p.2.1 p.2.2.1 := by
    simp only [cornInDPhi, hpoly, cornInNl]
    fun_prop
  have hXs : Measurable fun p : ℝ × ℝ × ℝ × ℝ => cornInXs p.1 p.2.1 := by
    unfold cornInXs
    fun_prop
  have hx : Measurable fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1 := by fun_prop
  have hw : Measurable fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2 := by fun_prop
  unfold cornInKt cornInKw cornInK cornInDPhiC
  exact (Measurable.ite (measurableSet_lt hW0 hw) hOm hC0).sub
    ((Measurable.ite (measurableSet_lt hXs hx) hD measurable_const).mul
      (Measurable.ite (measurableSet_le hw hW0) measurable_const measurable_const))

end QED.ChainProof.SetCK

end
