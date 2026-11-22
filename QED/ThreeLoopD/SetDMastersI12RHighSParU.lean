/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ParamHPLLog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import QED.Polylog.HPLLowWeight

/-!
# Set (d), master `I₁₂`: the parametric integral `U` of the bad part, orders 0 and 1

The piece `Qreg` of the bad part of the bulk term `S` of `I₁₂` contains the parametric integral
(with `z = w (1 + w)`)

  `U(w) = (1 + w)⁻¹ ∫₀¹ (1 + w v)^{2ε-2} (1 - v)^{-ε} (1 + w v/(1 + w))^{-ε} dv`,

whose `εⁿ` coefficient is `U_n(w) = (1 + w)⁻¹ ∫₀¹ (1 + w v)⁻² Lⁿ/n! dv` with
`L(w, v) = 2 log (1 + w v) - log (1 - v) - log (1 + w + w v) + log (1 + w)`.

This file proves the integration-by-parts reduction (`i12HSU_succ`, for every `n`)

  `U_{n+1}(w) = (1 + w)⁻² ∫₀¹ M(w, v) Lⁿ/n! dv`,
  `M = (2w(1 - v)/(1 + w v) + 1 - w(1 - v)/(1 + w + w v))/(1 + w v)`,

(the primitive `(v - 1)/((1 + w)(1 + w v))` of `(1 + w v)⁻²` vanishes at `v = 1`, and
`L(w, 0) = 0`), and the closed forms

  `U₀(w) = (1 + w)⁻²`,
  `U₁(w) = (1 + w)⁻² (2 + (1 + 2w)/w² (log (1 + 2w) - 2 log (1 + w)))`,

also in the variable `x = 1/(1 + 2w) = 1/√(1 + 4z)` as harmonic polylogarithms
(`i12HSU_one_hpl`): `U₁ = 4x²/(1 + x)² (2 + 4x/(1 - x)² (2 log 2 + H(0; x) - 2 H(-1; x)))`.

## Main definitions

* `QED.ThreeLoopD.i12HSUL`: the logarithm `L(w, v)`.
* `QED.ThreeLoopD.i12HSU`: the coefficient `U_n(w)`.
* `QED.ThreeLoopD.i12HSUM`: the reduced kernel `M(w, v)`; `i12HSUMPrim`: its primitive in `v`.
* `QED.ThreeLoopD.i12HSWofX`: `w = (1 - x)/(2x)`, so that `x = 1/(1 + 2w) = 1/√(1 + 4z)`
  (`QED.ThreeLoopD.eq_inv_sqrt_i12HSWofX`).

## Main results

* `QED.ThreeLoopD.i12HSU_succ`, `QED.ThreeLoopD.i12HSU_zero`, `QED.ThreeLoopD.i12HSU_one`,
  `QED.ThreeLoopD.i12HSU_one_hpl`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ThreeLoopD

open QED.Polylog.ParamHPL QED.Polylog.HPL

/-- The logarithm `L(w, v) = 2 log (1 + w v) - log (1 - v) - log (1 + w + w v) + log (1 + w)`
of the integrand of `U`. -/
noncomputable def i12HSUL (w v : ℝ) : ℝ :=
  2 * log (1 + w * v) - log (1 - v) - log (1 + w + w * v) + log (1 + w)

/-- The coefficient `U_n(w) = (1 + w)⁻¹ ∫₀¹ (1 + w v)⁻² Lⁿ/n! dv`. -/
noncomputable def i12HSU (n : ℕ) (w : ℝ) : ℝ :=
  (1 + w)⁻¹ * ∫ v in Ioo (0 : ℝ) 1, ((1 + w * v) ^ 2)⁻¹ * (i12HSUL w v ^ n / n.factorial)

/-- The reduced kernel `M(w, v)` of `U_{n+1}`. -/
noncomputable def i12HSUM (w v : ℝ) : ℝ :=
  (2 * w * (1 - v) / (1 + w * v) + 1 - w * (1 - v) / (1 + w + w * v)) / (1 + w * v)

/-- `L(w, 0) = 0`. -/
theorem i12HSUL_zero (w : ℝ) : i12HSUL w 0 = 0 := by
  simp [i12HSUL]

/-- `∂ᵥ L = 2w/(1 + w v) + 1/(1 - v) - w/(1 + w + w v)`. -/
theorem hasDerivAt_i12HSUL {w v : ℝ} (hw : 0 ≤ w) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    HasDerivAt (i12HSUL w)
      (2 * w / (1 + w * v) + 1 / (1 - v) - w / (1 + w + w * v)) v := by
  have h1 : 0 < 1 + w * v := by positivity
  have h2 : 0 < 1 - v := by linarith
  have h3 : 0 < 1 + w + w * v := by positivity
  have da : HasDerivAt (fun v => 1 + w * v) w v := by
    simpa using ((hasDerivAt_id v).const_mul w).const_add 1
  have db : HasDerivAt (fun v => 1 - v) (-1) v := by
    simpa using (hasDerivAt_id v).const_sub 1
  have dc : HasDerivAt (fun v => 1 + w + w * v) w v := by
    simpa using ((hasDerivAt_id v).const_mul w).const_add (1 + w)
  have h := ((((da.log h1.ne').const_mul 2).sub (db.log h2.ne')).sub (dc.log h3.ne')).add_const
    (log (1 + w))
  exact h.congr_deriv (by ring)

/-- `L` is continuous at every `v ∈ [0, 1)`. -/
theorem continuousAt_i12HSUL {w v : ℝ} (hw : 0 ≤ w) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ContinuousAt (i12HSUL w) v :=
  (hasDerivAt_i12HSUL hw hv0 hv1).continuousAt

/-- The log-power bound `|L| ≤ C_w + |log v| + |log (1 - v)|`,
`C_w = 2 log (1 + w) + log (1 + 2w)`. -/
theorem abs_i12HSUL_le {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |i12HSUL w v| ≤ 2 * log (1 + w) + log (1 + 2 * w) + |log v| + |log (1 - v)| := by
  have hwv : 0 ≤ w * v := mul_nonneg hw hv.1.le
  have hwv1 : w * v ≤ w := by nlinarith [hv.2]
  have a0 : 0 ≤ log (1 + w * v) := log_nonneg (by linarith)
  have a1 : log (1 + w * v) ≤ log (1 + w) := log_le_log (by linarith) (by linarith)
  have b0 : log (1 + w) ≤ log (1 + w + w * v) := log_le_log (by linarith) (by linarith)
  have b1 : log (1 + w + w * v) ≤ log (1 + 2 * w) := log_le_log (by linarith) (by linarith)
  have c0 : 0 ≤ log (1 + w) := log_nonneg (by linarith)
  have hl := neg_abs_le (log (1 - v))
  have hl' := le_abs_self (log (1 - v))
  have hlv := abs_nonneg (log v)
  rw [abs_le]
  unfold i12HSUL
  constructor <;> linarith

/-- The log-power bound for `Lⁿ`. -/
theorem abs_i12HSUL_pow_le {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    |i12HSUL w v ^ n| ≤ (2 * log (1 + w) + log (1 + 2 * w) + |log v| + |log (1 - v)|) ^ n := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_i12HSUL_le hw hv) n

theorem i12HSU_C_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ 2 * log (1 + w) + log (1 + 2 * w) := by
  have := log_nonneg (show (1 : ℝ) ≤ 1 + w by linarith)
  have := log_nonneg (show (1 : ℝ) ≤ 1 + 2 * w by linarith)
  linarith

/-- `|M(w, v)| ≤ 1 + 3w` on `(0, 1)`. -/
theorem abs_i12HSUM_le {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |i12HSUM w v| ≤ 1 + 3 * w := by
  have h1 : 1 ≤ 1 + w * v := by nlinarith [hv.1]
  have h3 : 1 ≤ 1 + w + w * v := by nlinarith [hv.1]
  have hv1 : 0 ≤ 1 - v := by linarith [hv.2]
  have e1 : 0 ≤ 2 * w * (1 - v) / (1 + w * v) := by positivity
  have e1' : 2 * w * (1 - v) / (1 + w * v) ≤ 2 * w := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hv.1, mul_nonneg hw hv1]
  have e2 : 0 ≤ w * (1 - v) / (1 + w + w * v) := by positivity
  have e2' : w * (1 - v) / (1 + w + w * v) ≤ w := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hv.1, mul_nonneg hw hv1, mul_nonneg hw hv.1.le]
  unfold i12HSUM
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + w * v), div_le_iff₀ (by linarith)]
  rw [abs_le]
  constructor <;> nlinarith

/-- `d/dv L^{n+1}/(n+1)! = Lⁿ/n! ∂ᵥ L`. -/
theorem hasDerivAt_i12HSUL_pow_div {w v : ℝ} (hw : 0 ≤ w) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ) :
    HasDerivAt (fun v => i12HSUL w v ^ (n + 1) / ((n + 1).factorial : ℝ))
      (i12HSUL w v ^ n / n.factorial *
        (2 * w / (1 + w * v) + 1 / (1 - v) - w / (1 + w + w * v))) v := by
  have h := ((hasDerivAt_i12HSUL hw hv0 hv1).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- `d/dv (v - 1)/((1 + w)(1 + w v)) = (1 + w v)⁻²`. -/
theorem hasDerivAt_i12HSU_prim {w v : ℝ} (hw : 0 ≤ w) (hv0 : 0 ≤ v) :
    HasDerivAt (fun v => (v - 1) / ((1 + w) * (1 + w * v))) (((1 + w * v) ^ 2)⁻¹) v := by
  have h1 : 0 < 1 + w * v := by positivity
  have h2 : 0 < 1 + w := by linarith
  have dd : HasDerivAt (fun v => (1 + w) * (1 + w * v)) ((1 + w) * w) v := by
    simpa using (((hasDerivAt_id v).const_mul w).const_add 1).const_mul (1 + w)
  have h := ((hasDerivAt_id v).sub_const 1).div dd (by positivity)
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- The reduction identity `(v - 1)/((1 + w)(1 + w v)) ∂ᵥ L = -(1 + w)⁻¹ M`. -/
theorem i12HSU_prim_mul_deriv {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    (v - 1) / ((1 + w) * (1 + w * v)) *
      (2 * w / (1 + w * v) + 1 / (1 - v) - w / (1 + w + w * v)) =
      -((1 + w)⁻¹ * i12HSUM w v) := by
  have h1 : 0 < 1 + w * v := by nlinarith [hv.1]
  have h2 : 0 < 1 + w := by linarith
  have h3 : 0 < 1 + w + w * v := by nlinarith [hv.1]
  have h4 : 1 - v ≠ 0 := by linarith [hv.2]
  unfold i12HSUM
  field_simp
  ring

theorem continuousAt_i12HSUM {w v : ℝ} (hw : 0 ≤ w) (hv0 : 0 ≤ v) :
    ContinuousAt (i12HSUM w) v := by
  have h1 : 1 + w * v ≠ 0 := by positivity
  have h3 : 1 + w + w * v ≠ 0 := by positivity
  unfold i12HSUM
  fun_prop (disch := assumption)

/-- **Integration by parts:** `U_{n+1}(w) = (1 + w)⁻² ∫₀¹ M(w, v) Lⁿ/n! dv`. -/
theorem i12HSU_succ {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    i12HSU (n + 1) w =
      ((1 + w) ^ 2)⁻¹ * ∫ v in Ioo (0 : ℝ) 1, i12HSUM w v * (i12HSUL w v ^ n / n.factorial) := by
  set C := 2 * log (1 + w) + log (1 + 2 * w) with hCdef
  have hC : 0 ≤ C := i12HSU_C_nonneg hw
  set f : ℝ → ℝ := fun v =>
    ((1 + w * v) ^ 2)⁻¹ * (i12HSUL w v ^ (n + 1) / ((n + 1).factorial : ℝ)) with hf
  set k : ℝ → ℝ := fun v => (1 + w)⁻¹ * (i12HSUM w v * (i12HSUL w v ^ n / n.factorial))
    with hk
  set h : ℝ → ℝ := fun v =>
    (v - 1) / ((1 + w) * (1 + w * v)) * (i12HSUL w v ^ (n + 1) / ((n + 1).factorial : ℝ))
    with hh
  have hfac : ∀ m : ℕ, (1 : ℝ) ≤ m.factorial := fun m => by exact_mod_cast m.factorial_pos
  -- measurability
  have hcf : ContinuousOn f (Ioo 0 1) := continuousOn_of_forall_continuousAt fun v hv => by
    have h1 : (1 + w * v) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (by nlinarith [hv.1, mul_nonneg hw hv.1.le] : (0 : ℝ) < 1 + w * v).ne'
    exact (ContinuousAt.inv₀ (f := fun v => (1 + w * v) ^ 2) (by fun_prop) h1).mul
      (((continuousAt_i12HSUL hw hv.1.le hv.2).pow _).div_const _)
  have hck : ContinuousOn k (Ioo 0 1) := continuousOn_of_forall_continuousAt fun v hv =>
    continuousAt_const.mul ((continuousAt_i12HSUM hw hv.1.le).mul
      (((continuousAt_i12HSUL hw hv.1.le hv.2).pow _).div_const _))
  -- integrability
  have hfi : IntegrableOn f (Ioo 0 1) := by
    refine integrableOn_Ioo_of_abs_le_logs hC zero_le_one (n + 1)
      (hcf.aestronglyMeasurable measurableSet_Ioo) fun v hv => ?_
    have h1 : 1 ≤ (1 + w * v) ^ 2 := one_le_pow₀ (by nlinarith [hv.1])
    have hb := abs_i12HSUL_pow_le hw hv (n + 1)
    rw [hf, abs_mul, abs_div, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (1 + w * v) ^ 2),
      abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ)), one_mul]
    calc ((1 + w * v) ^ 2)⁻¹ * (|i12HSUL w v ^ (n + 1)| / ((n + 1).factorial : ℝ))
        ≤ 1 * (|i12HSUL w v ^ (n + 1)| / 1) := by
          gcongr
          · exact inv_le_one_of_one_le₀ h1
          · exact hfac _
      _ ≤ _ := by simpa using hb
  have hki : IntegrableOn k (Ioo 0 1) := by
    refine integrableOn_Ioo_of_abs_le_logs hC (by linarith : (0 : ℝ) ≤ 1 + 3 * w) n
      (hck.aestronglyMeasurable measurableSet_Ioo) fun v hv => ?_
    have hb := abs_i12HSUL_pow_le hw hv n
    have hM := abs_i12HSUM_le hw hv
    rw [hk, abs_mul, abs_mul, abs_div, abs_inv, abs_of_pos (by linarith : (0 : ℝ) < 1 + w),
      abs_of_pos (by positivity : (0 : ℝ) < (n.factorial : ℝ))]
    have hi1 : (1 + w)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hd1 : |i12HSUL w v ^ n| / (n.factorial : ℝ) ≤ |i12HSUL w v ^ n| :=
      div_le_self (abs_nonneg _) (hfac n)
    calc (1 + w)⁻¹ * (|i12HSUM w v| * (|i12HSUL w v ^ n| / (n.factorial : ℝ)))
        ≤ 1 * ((1 + 3 * w) * |i12HSUL w v ^ n|) := by
          gcongr
      _ ≤ _ := by rw [one_mul]; gcongr
  -- derivative of the boundary term
  have hd : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt h (f v - k v) v := fun v hv => by
    have h := (hasDerivAt_i12HSU_prim hw hv.1.le).mul
      (hasDerivAt_i12HSUL_pow_div hw hv.1.le hv.2 n)
    refine h.congr_deriv ?_
    have key := i12HSU_prim_mul_deriv hw hv
    rw [hf, hk]
    simp only
    linear_combination (i12HSUL w v ^ n / n.factorial) * key
  -- boundary limits
  have hla : Tendsto h (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt h 0 := by
      have h1 : (1 + w) * (1 + w * 0) ≠ 0 := by simp; linarith
      exact (ContinuousAt.div (f := fun v : ℝ => v - 1)
        (g := fun v => (1 + w) * (1 + w * v)) (by fun_prop) (by fun_prop) h1).mul
        (((continuousAt_i12HSUL hw le_rfl zero_lt_one).pow _).div_const _)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [hh, i12HSUL_zero] using this
  have hlb : Tendsto h (𝓝[<] 1) (𝓝 0) := by
    have := tendsto_one_sub_mul_of_abs_le_logs (n := n + 1) (D := 1) hC zero_le_one
      (f := fun v => -(((1 + w) * (1 + w * v))⁻¹ *
        (i12HSUL w v ^ (n + 1) / ((n + 1).factorial : ℝ)))) fun v hv => by
      have h1 : 1 ≤ (1 + w) * (1 + w * v) := by
        nlinarith [mul_nonneg hw hv.1.le, mul_nonneg (mul_nonneg hw hw) hv.1.le]
      have hb := abs_i12HSUL_pow_le hw hv (n + 1)
      rw [abs_neg, abs_mul, abs_div, abs_inv, abs_of_pos (by positivity : (0 : ℝ) <
        (1 + w) * (1 + w * v)), abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ)),
        one_mul]
      calc ((1 + w) * (1 + w * v))⁻¹ * (|i12HSUL w v ^ (n + 1)| / ((n + 1).factorial : ℝ))
          ≤ 1 * (|i12HSUL w v ^ (n + 1)| / 1) := by
            gcongr
            · exact inv_le_one_of_one_le₀ h1
            · exact hfac _
        _ ≤ _ := by simpa using hb
    refine this.congr fun v => ?_
    rw [hh]
    simp only
    rw [div_eq_mul_inv]
    ring
  have key := setIntegral_Ioo_eq_add_of_eq_add_deriv (f := f) (k := k) (h := h)
    (h' := fun v => f v - k v) zero_lt_one (fun v _ => by ring) hki hd (hfi.sub hki) hla hlb
  unfold i12HSU
  rw [show (fun v => ((1 + w * v) ^ 2)⁻¹ * (i12HSUL w v ^ (n + 1) /
      ((n + 1).factorial : ℝ))) = f from rfl, key, hk, integral_const_mul, sub_self, add_zero,
    ← mul_assoc, ← mul_inv, ← sq]

/-- `U₀(w) = (1 + w)⁻²`. -/
theorem i12HSU_zero {w : ℝ} (hw : 0 ≤ w) : i12HSU 0 w = ((1 + w) ^ 2)⁻¹ := by
  unfold i12HSU
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v => v / (1 + w * v))
      (((1 + w * v) ^ 2)⁻¹) v := fun v hv => by
    rw [uIcc_of_le zero_le_one] at hv
    have h1 : 0 < 1 + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1]
    have h := (hasDerivAt_id v).div (((hasDerivAt_id v).const_mul w).const_add 1) h1.ne'
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hc : ContinuousOn (fun v : ℝ => ((1 + w * v) ^ 2)⁻¹) (uIcc 0 1) := fun v hv => by
    rw [uIcc_of_le zero_le_one] at hv
    have h1 : (1 + w * v) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (by nlinarith [hv.1, mul_nonneg hw hv.1] : (0 : ℝ) < 1 + w * v).ne'
    exact (ContinuousAt.inv₀ (f := fun v => (1 + w * v) ^ 2) (by fun_prop)
      h1).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  have h2 : (1 + w) ≠ 0 := by linarith
  field_simp
  ring

/-- The primitive of `M` in `v`:
`-2(1 + w)/(w(1 + w v)) + (1 + 2w)/w² (log (1 + w + w v) - log (1 + w v))`. -/
noncomputable def i12HSUMPrim (w v : ℝ) : ℝ :=
  -2 * (1 + w) / (w * (1 + w * v)) + (1 + 2 * w) / w ^ 2 * (log (1 + w + w * v) - log (1 + w * v))

theorem hasDerivAt_i12HSUMPrim {w v : ℝ} (hw : 0 < w) (hv : 0 ≤ v) :
    HasDerivAt (i12HSUMPrim w) (i12HSUM w v) v := by
  have h1 : 0 < 1 + w * v := by positivity
  have h3 : 0 < 1 + w + w * v := by positivity
  have da : HasDerivAt (fun v => 1 + w * v) w v := by
    simpa using ((hasDerivAt_id v).const_mul w).const_add 1
  have dc : HasDerivAt (fun v => 1 + w + w * v) w v := by
    simpa using ((hasDerivAt_id v).const_mul w).const_add (1 + w)
  have de : HasDerivAt (fun v => w * (1 + w * v)) (w * w) v := da.const_mul w
  have h := ((hasDerivAt_const v (-2 * (1 + w))).div de (by positivity)).add
    (((dc.log h3.ne').sub (da.log h1.ne')).const_mul ((1 + 2 * w) / w ^ 2))
  refine h.congr_deriv ?_
  unfold i12HSUM
  field_simp
  ring

/-- `U₁(w) = (1 + w)⁻² (2 + (1 + 2w)/w² (log (1 + 2w) - 2 log (1 + w)))` for `w > 0`. -/
theorem i12HSU_one {w : ℝ} (hw : 0 < w) :
    i12HSU 1 w =
      ((1 + w) ^ 2)⁻¹ * (2 + (1 + 2 * w) / w ^ 2 * (log (1 + 2 * w) - 2 * log (1 + w))) := by
  rw [i12HSU_succ hw.le 0]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (i12HSUMPrim w) (i12HSUM w v) v := fun v hv => by
    rw [uIcc_of_le zero_le_one] at hv
    exact hasDerivAt_i12HSUMPrim hw hv.1
  have hc : ContinuousOn (i12HSUM w) (uIcc 0 1) := fun v hv => by
    rw [uIcc_of_le zero_le_one] at hv
    exact (continuousAt_i12HSUM hw.le hv.1).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  congr 1
  unfold i12HSUMPrim
  simp only [mul_zero, add_zero, mul_one, log_one, sub_zero]
  have h2 : (1 + w) ≠ 0 := by linarith
  have e : 1 + w + w = 1 + 2 * w := by ring
  rw [e]
  field_simp
  ring

/-! ### The variable `x = 1/(1 + 2w) = 1/√(1 + 4z)` -/

/-- The parameter `w = (1 - x)/(2x)` of `x ∈ (0, 1)`. -/
noncomputable def i12HSWofX (x : ℝ) : ℝ := (1 - x) / (2 * x)

theorem i12HSWofX_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < i12HSWofX x := by
  unfold i12HSWofX
  have := hx.1; have := hx.2
  apply div_pos <;> linarith

theorem one_add_two_mul_i12HSWofX {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 + 2 * i12HSWofX x = x⁻¹ := by
  unfold i12HSWofX
  have := hx.1.ne'
  field_simp
  ring

theorem one_add_i12HSWofX {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 + i12HSWofX x = (1 + x) / (2 * x) := by
  unfold i12HSWofX
  have := hx.1.ne'
  field_simp
  ring

/-- `z = w (1 + w) = (1 - x²)/(4x²)`. -/
theorem i12HSWofX_mul_one_add {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i12HSWofX x * (1 + i12HSWofX x) = (1 - x ^ 2) / (4 * x ^ 2) := by
  rw [one_add_i12HSWofX hx]
  unfold i12HSWofX
  have := hx.1.ne'
  field_simp
  ring

/-- `x = 1/√(1 + 4z)` for `z = w (1 + w)`, `w = i12HSWofX x`. -/
theorem eq_inv_sqrt_i12HSWofX {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x = (√(1 + 4 * (i12HSWofX x * (1 + i12HSWofX x))))⁻¹ := by
  rw [i12HSWofX_mul_one_add hx]
  have hx0 := hx.1
  have e : 1 + 4 * ((1 - x ^ 2) / (4 * x ^ 2)) = (x⁻¹) ^ 2 := by
    field_simp
    ring
  rw [e, sqrt_sq (by positivity), inv_inv]

/-- `U₁` as harmonic polylogarithms of `x = 1/(1 + 2w)`:
`U₁ = 4x²/(1 + x)² (2 + 4x/(1 - x)² (2 log 2 + H(0; x) - 2 H(-1; x)))`. -/
theorem i12HSU_one_hpl {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i12HSU 1 (i12HSWofX x) = 4 * x ^ 2 / (1 + x) ^ 2 *
      (2 + 4 * x / (1 - x) ^ 2 *
        (2 * log 2 + hpl [.zero] x - 2 * hpl [.negOne] x)) := by
  rw [i12HSU_one (i12HSWofX_pos hx), one_add_two_mul_i12HSWofX hx, one_add_i12HSWofX hx,
    hpl_zero, hpl_negOne hx]
  have hx0 := hx.1
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hx2 : 0 < 1 + x := by linarith
  rw [log_inv, log_div hx2.ne' (by positivity), log_mul two_ne_zero hx0.ne']
  unfold i12HSWofX
  field_simp
  ring

end QED.ThreeLoopD
