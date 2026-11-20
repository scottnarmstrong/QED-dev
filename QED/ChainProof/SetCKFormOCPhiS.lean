/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCF0
public import QED.ChainProof.SetCKFormOCNode

/-!
# Set (c), Stage K, closed forms: `∫ φ_X` per `a`

Helper level (no frozen statement). Step 4 of the `ρ_oC` route (Stage K notes, Session 30+).
On `x ∈ (0, X)`, `log v(x, X) = log(X - x) + log(X + x - X x) - log(1 - X) - log(1 - x)`
(**`formOC_logv_eq`**), so `x ↦ β_c(a, x) log v(x, X)` is integrable on `(0, X)`
(**`formOC_integrableOn_beta_logv`**). Hence, whenever `φ_X` (`formOCPhi`) is integrable
(**`formOC_integral_phi`**):

`∫ φ_X = ∫_{a ∈ (0,1)} (∫_{(0,X)} f(a, x) dx - ∫_{(0,X)} β_c(a, x) log v(x, X) dx)`,

with `f = formOCf`. The inner `β_c log v` integral is `𝓛(a, X)`; its `X`-derivative `ℓ_a` is
the next step.
-/

@[expose] public section

open Real Set Filter MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {a x X : ℝ}

theorem formOCD0_pos_of_le (ha : a ∈ Ioo (0 : ℝ) 1) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 < formOCD0 a x := by
  have h1 : 0 < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
  have := setCKQ_nonneg ⟨hx0, hx1.le⟩
  unfold formOCD0
  positivity

theorem formOC_logv_eq (hX : X < 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    log (scOutVX x X) =
      log (X - x) + log (X + x - X * x) - log (1 - X) - log (1 - x) := by
  have h1X : 0 < 1 - X := by linarith
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hXx : 0 < X - x := by linarith [hx.2]
  have hS : 0 < X + x - X * x := by nlinarith [hx.1, hx.2]
  have e : scOutVX x X = (X - x) * (X + x - X * x) / ((1 - X) * (1 - x)) := by
    unfold scOutVX setCKQ
    field_simp
    ring
  rw [e, log_div (by positivity) (by positivity), log_mul hXx.ne' hS.ne',
    log_mul h1X.ne' h1x.ne']
  ring

theorem formOC_integrableOn_logv (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => log (scOutVX x X)) (Ioo 0 X) := by
  have h1 : IntegrableOn (fun x => log (X - x)) (Ioo 0 X) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := X) (b := 0)).comp_sub_left X
    simp only [sub_self, sub_zero] at h
    exact (h.1).mono_set Ioo_subset_Ioc_self
  have hc : ContinuousOn (fun x => log (X + x - X * x) - log (1 - X) - log (1 - x))
      (Icc 0 X) := by
    refine ((continuousOn_log.comp (by fun_prop) fun x hx => ?_).sub continuousOn_const).sub
      (continuousOn_log.comp (by fun_prop) fun x hx => ?_)
    · simp only [mem_compl_iff, mem_singleton_iff]
      nlinarith [hx.1, hx.2, hX.1, hX.2]
    · simp only [mem_compl_iff, mem_singleton_iff]
      linarith [hx.2, hX.2]
  have h2 : IntegrableOn (fun x => log (X + x - X * x) - log (1 - X) - log (1 - x))
      (Ioo 0 X) :=
    (hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  refine (h1.add h2).congr_fun (fun x hx => ?_) measurableSet_Ioo
  simp only [Pi.add_apply, formOC_logv_eq hX.2 hx]
  ring

theorem formOC_continuousOn_beta (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X < 1) :
    ContinuousOn (fun x => formOCbeta a x) (Icc 0 X) := by
  unfold formOCbeta formOCD0 setCKQ
  refine ContinuousOn.div (by fun_prop) ?_ fun x hx => ?_
  · refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) (by fun_prop)
    exact continuousOn_const.add (continuousOn_const.mul
      (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => by linarith [hx.2]))
  · have hD := formOCD0_pos_of_le ha hx.1 (by linarith [hx.2])
    unfold formOCD0 setCKQ at hD
    have : x - 1 ≠ 0 := by linarith [hx.2]
    positivity

theorem formOC_integrableOn_beta_logv (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => formOCbeta a x * log (scOutVX x X)) (Ioo 0 X) :=
  (formOC_integrableOn_logv hX).continuousOn_mul_of_subset (formOC_continuousOn_beta ha hX.2)
    isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self

/-- The section of `φ_X` at `a`, restricted to `x ∈ (0, X)`. -/
theorem formOC_phi_section :
    EqOn (fun x => formOCPhi X (a, x))
      (fun x => formOCf a x - formOCbeta a x * log (scOutVX x X)) (Ioo 0 X) := by
  intro x hx
  simp only [formOCPhi, hx.2, ↓reduceIte, formOCf]

/-- **`∫ φ_X` per `a`.** -/
theorem formOC_integral_phi (hX : X ∈ Ioo (0 : ℝ) 1)
    (hint : Integrable (formOCPhi X) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)))) :
    ∫ q, formOCPhi X q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ a in Ioo (0 : ℝ) 1, ((∫ x in Ioo (0 : ℝ) X, formOCf a x) -
        ∫ x in Ioo (0 : ℝ) X, formOCbeta a x * log (scOutVX x X)) := by
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hint.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with a hsec ha
  have hset : Ioo (0 : ℝ) 1 ∩ Iio X = Ioo 0 X := by
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨⟨h0, _⟩, h⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨h0, h.trans hX.2⟩, h⟩
  have hind : (fun x => formOCPhi X (a, x)) = Set.indicator (Iio X)
      (fun x => formOCf a x - formOCbeta a x * log (scOutVX x X)) := by
    funext x
    by_cases h : x < X
    · simp only [formOCPhi, h, ↓reduceIte, formOCf, indicator_of_mem (mem_Iio.2 h)]
    · simp only [formOCPhi, h, ↓reduceIte, indicator_of_notMem (fun h' => h (mem_Iio.1 h'))]
  have hsec0 : IntegrableOn (fun y => formOCPhi X (a, y)) (Ioo 0 1) volume := hsec
  have hsec' : IntegrableOn (fun x => formOCPhi X (a, x)) (Ioo 0 X) :=
    hsec0.mono_set fun x hx => ⟨hx.1, hx.2.trans hX.2⟩
  have hb := formOC_integrableOn_beta_logv ha hX
  have hf : IntegrableOn (fun x => formOCf a x) (Ioo 0 X) :=
    ((hsec'.congr_fun formOC_phi_section measurableSet_Ioo).add hb).congr_fun
      (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioo
  show ∫ x in Ioo (0 : ℝ) 1, formOCPhi X (a, x) = _
  rw [hind, setIntegral_indicator measurableSet_Iio, hset, integral_sub hf hb]

end

end QED.ChainProof.SetCK

end
