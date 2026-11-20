/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCH
public import QED.ChainProof.SetCKFormCGD
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the `u`-antiderivative of `J` and the fundamental theorem

Helper level (no frozen statement). The `u`-antiderivative of `J = formCJ X` (task 3 of the `ρ_C`
closed form, scratch `stageK/fce/`) is

`G(u) = F_U log(1 - u) + F_V log(X - u) + G_m (log P - log(X + u - Xu)) + F_M log M`
`  + (F_X + (log P - log Q)/6) log(1 - X) + H + h_U log(1 - u) + h_M log M + h_P log P`
`  + h_A log(X + u - Xu) + D₁ + … + D₇`

(`formCG`), with the rational parts of `SetCKFormCG` and the dilogarithm blocks of
`SetCKFormCGD`.

* **`hasDerivAt_formCG`**: `G' = J` on `0 < u < X < 1`;
* **`continuousOn_formCG`**: `G` is continuous on `[0, X]` (at `u = X`: `F_V = (X - u) F_h` and
  `t log t → 0`; the argument `M` of `D₃` reaches `1`, where `Li₂` is still continuous);
* **`integral_formCJ_eq`**: if `J` is integrable on `(0, X)`, then `∫_{(0, X)} J = G(X) - G(0)`.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog

namespace QED.ChainProof.SetCK

/-- **The `u`-antiderivative of `J`**. -/
noncomputable def formCG (X u : ℝ) : ℝ :=
  formCFU X u * log (1 - u) + formCFV X u * log (X - u) +
    formCGm X u * (log (formCP X u) - log (X + u - X * u)) + formCFM X u * log (coordM X u) +
    (formCFX X u + (log (formCP X u) - log (formCQ X u)) / 6) * log (1 - X) + formCHr X u +
    formChU X * log (1 - u) + formChM X * log (coordM X u) + formChP X * log (formCP X u) +
    formChA X * log (X + u - X * u) + formCD1 X u + formCD2 X u + formCD3 X u + formCD4 X u +
    formCD5 X u + formCD6 X u + formCD7 X u

/-- **`G' = J`** on `0 < u < X < 1`. -/
theorem hasDerivAt_formCG {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    HasDerivAt (formCG X) (formCJ X u) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1⟩ := formCD_facts hX hu
  have dU := ((hasDerivAt_id u).const_sub 1).log h1u.ne'
  have dV := ((hasDerivAt_id u).const_sub X).log hXu.ne'
  have dA0 : HasDerivAt (fun v => X + v - X * v) (1 - X) u := by
    have := (((hasDerivAt_id u).const_add X).sub ((hasDerivAt_id u).const_mul X))
    exact this.congr_deriv (by simp)
  have dA := dA0.log hA.ne'
  have dP := (formC_hasDerivAt_P X u).log hP.ne'
  have dQ := (formC_hasDerivAt_Q X u).log hQ.ne'
  have dM := (formC_hasDerivAt_M X u).log hM.ne'
  have h := (((hasDerivAt_formCFU hX hu).mul dU).add ((hasDerivAt_formCFV hX hu).mul dV)).add
    ((hasDerivAt_formCGm hX hu).mul (dP.sub dA))
  have h := ((h.add ((hasDerivAt_formCFM hX hu).mul dM)).add
    (((hasDerivAt_formCFX hX hu).add ((dP.sub dQ).div_const 6)).mul_const (log (1 - X)))).add
    (hasDerivAt_formCHr hX hu)
  have h := (((h.add (dU.const_mul (formChU X))).add (dM.const_mul (formChM X))).add
    (dP.const_mul (formChP X))).add (dA.const_mul (formChA X))
  have h := ((((((h.add (hasDerivAt_formCD1 hX hu)).add (hasDerivAt_formCD2 hX hu)).add
    (hasDerivAt_formCD3 hX hu)).add (hasDerivAt_formCD4 hX hu)).add
    (hasDerivAt_formCD5 hX hu)).add (hasDerivAt_formCD6 hX hu)).add (hasDerivAt_formCD7 hX hu)
  refine h.congr_deriv ?_
  rw [← formCS1_eq hX hu, ← formCS2_eq hX hu, ← formCS3_eq hX hu, ← formCS4_eq hX hu,
    ← formCS5_eq hX hu]
  unfold formCJ
  simp only [id, Pi.sub_apply]
  ring

section cont

variable {X u : ℝ}

@[fun_prop]
theorem formC_continuous_P (X : ℝ) : Continuous fun u => formCP X u := by unfold formCP; fun_prop

@[fun_prop]
theorem formC_continuous_Q (X : ℝ) : Continuous fun u => formCQ X u := by unfold formCQ; fun_prop

@[fun_prop]
theorem formC_continuous_M (X : ℝ) : Continuous fun u => coordM X u := by unfold coordM; fun_prop

theorem formCD_facts_Icc (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Icc 0 X) :
    0 < formCP X u ∧ 0 < formCQ X u ∧ 0 < coordM X u ∧ 0 < 1 - X ∧ 0 < 1 - u ∧ 0 ≤ X - u ∧
      0 < X + u - X * u ∧ 0 < formCK X ∧ formCQ X u < formCK X ∧ coordM X u < formCK X ∧
      coordM X u ≤ 1 ∧ (1 - X) ^ 2 < coordM X u ∧ 1 - X < coordM X u := by
  obtain ⟨h0, h1⟩ := hX
  obtain ⟨hu0, huX⟩ := hu
  have h1X : 0 < 1 - X := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hXu : 0 ≤ X - u := by linarith
  have hA : 0 < X + u - X * u := by nlinarith
  have hP : 0 < formCP X u := by unfold formCP; nlinarith
  refine ⟨hP, by unfold formCQ; nlinarith, by unfold coordM; nlinarith, h1X, h1u, hXu, hA,
    by unfold formCK; nlinarith, ?_, ?_, ?_, ?_, ?_⟩
  · have : formCK X - formCQ X u = 2 * (1 - X) * (1 - u) := by unfold formCK formCQ; ring
    nlinarith [mul_pos h1X h1u]
  · have : formCK X - coordM X u = (1 - X) * (1 - u) := by unfold formCK coordM; ring
    nlinarith [mul_pos h1X h1u]
  · have : 1 - coordM X u = (1 - X) * (X - u) := by unfold coordM; ring
    nlinarith [mul_nonneg h1X.le hXu]
  · have : coordM X u - (1 - X) ^ 2 = X + u - X * u := by unfold coordM; ring
    linarith
  · have : coordM X u - (1 - X) = formCP X u := by unfold coordM formCP; ring
    linarith

theorem formC_contAt_Li2 {z : ℝ} (h1 : -1 < z) (h2 : z < 1) : ContinuousAt Li₂ z :=
  continuousOn_Li₂.continuousAt (Icc_mem_nhds h1 h2)

/-- The part of `G` that is continuous at every point of `[0, X]`. -/
theorem formCG_contAt (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Icc 0 X) :
    ContinuousAt (fun v => formCFU X v * log (1 - v) +
      formCGm X v * (log (formCP X v) - log (X + v - X * v)) + formCFM X v * log (coordM X v) +
      (formCFX X v + (log (formCP X v) - log (formCQ X v)) / 6) * log (1 - X) + formCHr X v +
      formChU X * log (1 - v) + formChM X * log (coordM X v) + formChP X * log (formCP X v) +
      formChA X * log (X + v - X * v) + formCD1 X v + formCD2 X v + formCD4 X v +
      formCD5 X v + formCD6 X v + formCD7 X v) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1, hM2, hM3⟩ := formCD_facts_Icc hX hu
  have hX0 : X ≠ 0 := hX.1.ne'
  have hX1 : X - 1 ≠ 0 := by linarith
  have hX2 : X - 2 ≠ 0 := by linarith [hX.2]
  have cP := formC_continuous_P X
  have cQ := formC_continuous_Q X
  have cM := formC_continuous_M X
  have l1 : ContinuousAt Li₂ (formCQ X u / formCK X) :=
    formC_contAt_Li2 (by have := div_pos hQ hK; linarith) ((div_lt_one hK).2 hQK)
  have l2 : ContinuousAt Li₂ (coordM X u / formCK X) :=
    formC_contAt_Li2 (by have := div_pos hM hK; linarith) ((div_lt_one hK).2 hMK)
  have l4 : ContinuousAt Li₂ (1 / (coordM X u / (1 - X) ^ 2)) := by
    rw [one_div_div]
    exact formC_contAt_Li2 (by have := div_pos (pow_pos h1X 2) hM; linarith)
      ((div_lt_one hM).2 hM2)
  have l5 : ContinuousAt Li₂ (1 / (coordM X u / (1 - X))) := by
    rw [one_div_div]
    exact formC_contAt_Li2 (by have := div_pos h1X hM; linarith) ((div_lt_one hM).2 hM3)
  have l6 : ContinuousAt Li₂ (-formCP X u / (1 - X) / (-formCP X u / (1 - X) - 1)) := by
    have hd : -formCP X u / (1 - X) - 1 = -coordM X u / (1 - X) := by
      field_simp; unfold coordM formCP; ring
    have hPM : formCP X u < coordM X u := by
      have : coordM X u - formCP X u = 1 - X := by unfold coordM formCP; ring
      linarith
    have e : -formCP X u / (1 - X) / (-coordM X u / (1 - X)) = formCP X u / coordM X u := by
      field_simp
    rw [hd, e]
    exact formC_contAt_Li2 (by have := div_pos hP hM; linarith) ((div_lt_one hM).2 hPM)
  have l7 : ContinuousAt Li₂ (-formCQ X u / formCK X) :=
    formC_contAt_Li2 (by rw [neg_div, neg_lt_neg_iff, div_lt_one hK]; exact hQK)
      (by have := div_pos hQ hK; rw [neg_div]; linarith)
  have hd6 : -formCP X u / (1 - X) - 1 ≠ 0 := by
    have : -formCP X u / (1 - X) < 0 := div_neg_of_neg_of_pos (by linarith) h1X
    linarith
  have hd6' : 1 - -formCP X u / (1 - X) ≠ 0 := by
    have : -formCP X u / (1 - X) < 0 := div_neg_of_neg_of_pos (by linarith) h1X
    linarith
  unfold formCFU formCFM formCFX formCHr formCD1 formCD2 formCD4 formCD5 formCD6 formCD7
  unfold formCGm formCGq formCc formCGp
  fun_prop (disch := (first | assumption | positivity | linarith))

/-- **`G` is continuous on `[0, X]`**. -/
theorem continuousOn_formCG (hX : X ∈ Ioo (0 : ℝ) 1) : ContinuousOn (formCG X) (Icc 0 X) := by
  have hs : ContinuousOn (fun v => formCFU X v * log (1 - v) +
      formCGm X v * (log (formCP X v) - log (X + v - X * v)) + formCFM X v * log (coordM X v) +
      (formCFX X v + (log (formCP X v) - log (formCQ X v)) / 6) * log (1 - X) + formCHr X v +
      formChU X * log (1 - v) + formChM X * log (coordM X v) + formChP X * log (formCP X v) +
      formChA X * log (X + v - X * v) + formCD1 X v + formCD2 X v + formCD4 X v +
      formCD5 X v + formCD6 X v + formCD7 X v) (Icc 0 X) :=
    fun v hv => (formCG_contAt hX hv).continuousWithinAt
  have hh : ContinuousOn (formCFh X) (Icc 0 X) := fun v hv => by
    have hM := (formCD_facts_Icc hX hv).2.2.1
    have cM := formC_continuous_M X
    unfold formCFh
    exact (by fun_prop (disch := positivity) :
      ContinuousAt (fun v => (1 - X) * (-X ^ 4 + X ^ 3 * v + 3 * X ^ 3 - 3 * X ^ 2 * v - 5 * X ^ 2 +
        2 * X * v + 6 * X - 2) / (12 * coordM X v ^ 2)) v).continuousWithinAt
  have hV : ContinuousOn (fun v => formCFV X v * log (X - v)) (Icc 0 X) := by
    refine (hh.mul (continuous_mul_log.comp (continuous_sub_left X)).continuousOn).congr
      fun v hv => ?_
    rw [formCFV_eq (formCD_facts_Icc hX hv).2.2.1.ne']
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  have h3 : ContinuousOn (formCD3 X) (Icc 0 X) := by
    have cM := formC_continuous_M X
    have hL : ContinuousOn (fun v => Li₂ (coordM X v)) (Icc 0 X) :=
      continuousOn_Li₂.comp cM.continuousOn fun v hv => by
        obtain ⟨-, -, hM, -, -, -, -, -, -, -, hM1, -, -⟩ := formCD_facts_Icc hX hv
        exact ⟨by linarith, hM1⟩
    have hl : ContinuousOn (fun v => log (coordM X v)) (Icc 0 X) := fun v hv =>
      ((continuousAt_log (formCD_facts_Icc hX hv).2.2.1.ne').comp
        cM.continuousAt).continuousWithinAt
    unfold formCD3
    exact continuousOn_const.mul ((continuousOn_const.mul hl).add hL.neg)
  refine ((hs.add hV).add h3).congr fun v _ => ?_
  simp only [Pi.add_apply]
  unfold formCG
  ring

/-- **The fundamental theorem for `J`**: `∫_{(0, X)} J = G(X) - G(0)`. -/
theorem integral_formCJ_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1)
    (hI : IntegrableOn (formCJ X) (Ioo 0 X)) :
    ∫ u in Ioo 0 X, formCJ X u = formCG X X - formCG X 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hX.1.le]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX.1.le (continuousOn_formCG hX)
    (fun u hu => hasDerivAt_formCG hX hu)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hX.1.le).2 hI)

end cont

end QED.ChainProof.SetCK

end
