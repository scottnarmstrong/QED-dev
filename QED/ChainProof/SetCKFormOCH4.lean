/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCH3
public import QED.ChainProof.SetCKAsmLam
import QED.Polylog.Reflection
import QED.Polylog.Landen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp

/-!
# Set (c), Stage K, closed forms: the `a`-integral of `G`

Helper level (no frozen statement). Item 5 of the `ρ_oC` route (Stage K notes), the last input
of set (c)'s value. For `X ∈ (0, 1)`:

* **`formOCG_intervalIntegrable`**: `G(·, X)` is integrable on `(0, 1)`
  (`G = formOCGr0 + c_A log a` with `formOCGr0`, `c_A` continuous on `[0, 1]`);
* **`integral_formOCG`**: `∫₀¹ G(a, X) da = 𝒢(1, X) - 𝒢(0, X)` (regular form `formOCHr`, the
  fundamental theorem of calculus with `∂_a 𝒢 = G`);
* **`formOCHr_one_sub_zero`**: `𝒢(1, X) - 𝒢(0, X) = ρ_oC(X) Q(X)/2`, from the reflection
  formula at `X` and at `1/(2 - X)` and Landen's identity at `1/(2 - X)`;
* **`integral_formOCG_eq`**: `∫₀¹ G(a, X) da = ρ_oC(X) Q(X)/2`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ChainProof.SetCK

section

variable {X : ℝ}

theorem formOCG_eq_r_of_mem (hX : X ∈ Ioo (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    formOCG a X = formOCGr0 a X + formOCGcA a X * log a := by
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨ha0, ha1⟩ := ha
  exact formOCG_eq_r ha0.ne' (by linarith) (by linarith) (by nlinarith) (by nlinarith)

/-- **`G(·, X)` is integrable on `(0, 1)`.** -/
theorem formOCG_intervalIntegrable (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun a => formOCG a X) volume 0 1 := by
  have hc : ContinuousOn (fun a => formOCGr0 a X) (Icc 0 1) := fun a ha =>
    (continuousAt_formOCGr0 hX ha).continuousWithinAt
  have hA : ContinuousOn (fun a => formOCGcA a X) (Icc 0 1) := fun a ha =>
    (continuousAt_formOCGcA hX ha).continuousWithinAt
  have hlog : IntegrableOn log (Icc (0 : ℝ) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      intervalIntegral.intervalIntegrable_log'
  have h := hc.integrableOn_Icc.add (hlog.continuousOn_mul hA isCompact_Icc)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact (h.mono_set Ioc_subset_Icc_self).congr_fun
    (fun a ha => (formOCG_eq_r_of_mem hX ha).symm) measurableSet_Ioc

/-- **The fundamental theorem of calculus for `𝒢`.** -/
theorem integral_formOCG (hX : X ∈ Ioo (0 : ℝ) 1) :
    ∫ a in Ioo (0 : ℝ) 1, formOCG a X = formOCHr 1 X - formOCHr 0 X := by
  obtain ⟨hX0, hX1⟩ := hX
  have hderiv : ∀ a ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun b => formOCHr b X) (formOCG a X) a := by
    intro a ha
    refine (hasDerivAt_formOCH ha ⟨hX0, hX1⟩).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with b hb
    obtain ⟨hb0, hb1⟩ := hb
    exact (formOCH_eq_r hb0.ne' (by linarith) (by linarith) (by nlinarith)).symm
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hderiv
    (formOCG_intervalIntegrable ⟨hX0, hX1⟩)
    ((continuousAt_formOCHr ⟨hX0, hX1⟩ ⟨le_rfl, zero_le_one⟩).tendsto.mono_left
      nhdsWithin_le_nhds)
    ((continuousAt_formOCHr ⟨hX0, hX1⟩ ⟨zero_le_one, le_rfl⟩).tendsto.mono_left
      nhdsWithin_le_nhds)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
  exact h

/-- **The endpoint identity** `𝒢(1, X) - 𝒢(0, X) = ρ_oC(X) Q(X)/2`. -/
theorem formOCHr_one_sub_zero (hX : X ∈ Ioo (0 : ℝ) 1) :
    formOCHr 1 X - formOCHr 0 X = rhoScOutC X * setCKQ X / 2 := by
  obtain ⟨hX0, hX1⟩ := hX
  have h1 : 0 < 1 - X := by linarith
  have h2 : 0 < 2 - X := by linarith
  have hv0 : 0 ≤ 1 / (2 - X) := by positivity
  have hv1 : 1 / (2 - X) ≤ 1 := by rw [div_le_one h2]; linarith
  have hv2 : 1 / 2 ≤ 1 / (2 - X) := one_div_le_one_div_of_le h2 (by linarith)
  have r1 := Li₂_add_Li₂_one_sub hX0.le hX1.le
  have r2 := Li₂_add_Li₂_one_sub hv0 hv1
  have r3 := Li₂_one_sub_inv_add_Li₂_one_sub hv2 hv1
  have e1 : 1 - 1 / (2 - X) = (1 - X) / (2 - X) := by field_simp; ring
  have e2 : 1 - (1 / (2 - X))⁻¹ = X - 1 := by rw [one_div, inv_inv]; ring
  have e3 : log (1 / (2 - X)) = -log (2 - X) := by rw [one_div, log_inv]
  have e4 : log ((1 - X) / (2 - X)) = log (1 - X) - log (2 - X) := log_div h1.ne' h2.ne'
  rw [e1, e3, e4] at r2
  rw [e2, e1, e3] at r3
  simp only [formOCHr, formOCHphi, one_mul, zero_mul, mul_zero, sub_zero, sub_add_cancel,
    log_one, Li₂_zero, one_pow, div_one, zero_add, add_zero]
  have l1 : Li₂ X = π ^ 2 / 6 - Li₂ (1 - X) - log X * log (1 - X) := by linarith
  have l3 : Li₂ ((1 - X) / (2 - X)) = -Li₂ (X - 1) - log (2 - X) ^ 2 / 2 := by
    rw [neg_sq] at r3; linarith
  have l2 : Li₂ (1 / (2 - X)) = π ^ 2 / 6 + Li₂ (X - 1) + log (2 - X) ^ 2 / 2 +
      log (2 - X) * (log (1 - X) - log (2 - X)) := by linarith
  rw [l1, l2, l3]
  simp only [rhoScOutC, formXW, setCKQ, formOCHhRat, formOCHhS, formOCHhcR, formOCHcM,
    formOCHcx, formOCHcT, formOCHK, formOCHq]
  have hXm : X - 1 ≠ 0 := by linarith
  have hXt : X - 2 ≠ 0 := by linarith
  generalize log X = lX
  generalize log (1 - X) = lo
  generalize log (2 - X) = T
  generalize Li₂ (1 - X) = A
  generalize Li₂ (X - 1) = B
  generalize hOg : 1 - X = Og at *
  generalize hXg : X - 1 = Xm at *
  generalize hTg : X - 2 = Xt at *
  generalize hT2 : 2 - X = Tg at *
  field_simp
  subst hOg hXg hTg hT2
  ring

/-- **`∫₀¹ G(a, X) da = ρ_oC(X) Q(X)/2`** on `(0, 1)` (the input `hGi` of set (c)). -/
theorem integral_formOCG_eq (hX : X ∈ Ioo (0 : ℝ) 1) :
    ∫ a in Ioo (0 : ℝ) 1, formOCG a X = rhoScOutC X * setCKQ X / 2 := by
  rw [integral_formOCG hX, formOCHr_one_sub_zero hX]

end

end QED.ChainProof.SetCK

end
