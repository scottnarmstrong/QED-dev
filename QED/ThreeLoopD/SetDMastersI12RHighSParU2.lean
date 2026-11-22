/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSParU
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import QED.Polylog.HPLLowWeight

/-!
# Set (d), master `I₁₂`: the parametric integral `U` at order 2

With `L(w, v)` and `U_n(w)` as in `QED.ThreeLoopD.SetDMastersI12RHighSParU`, the order-2
coefficient reduces (`i12HSU_two_eq`) to

  `U₂(w) = 2 U₁(w) + (1 + 2w)/(w²(1 + w)²) J(w)`,
  `J(w) = ∫₀¹ (w/(1 + w + w v) - w/(1 + w v)) L(w, v) dv`,

and `J` is a weight-2 combination of harmonic polylogarithms of `y = w/(1 + w)`
(`i12HSUJ_hpl`):

  `J = 2 (H(0,-1) - H(0,1) + H(1,-1) - H(1,1) - H(-1,-1) + H(-1,1))(y)`.

The proof is the differential-equation method of `QED.Polylog.ParamHPL` in the parameter `w`:
differentiation under the integral sign, an integration by parts in `v` that removes `L` from
the derivative, `∂_w J = 2(2w² + 2w + 1)/(w(1 + w)(1 + 2w)) log ((1 + 2w)/(1 + w)²)`, and the limit
`J → 0` as `w → 0⁺`. The variable `y = w/(1 + w)` is the Möbius image `(1 - x)/(1 + x)` of
`x = 1/(1 + 2w) = 1/√(1 + 4z)`; in it the alphabet is again `{0, 1, -1}` and the boundary point
`w = 0` is `y = 0`.

## Main definitions

* `QED.ThreeLoopD.i12HSUR`, `QED.ThreeLoopD.i12HSUJ`: the kernel and the integral `J`.
* `QED.ThreeLoopD.i12HSUJw`: the word combination of `J` (`hplSum` form).

## Main results

* `QED.ThreeLoopD.i12HSU_two_eq`, `QED.ThreeLoopD.i12HSUJ_hpl`,
  `QED.ThreeLoopD.i12HSUJ_eq_hplSum`, `QED.ThreeLoopD.integral_i12HSUJd`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ThreeLoopD

open QED.Polylog.ParamHPL QED.Polylog.HPL

/-- The kernel `w/(1 + w + w v) - w/(1 + w v)` of `J`. -/
noncomputable def i12HSUR (w v : ℝ) : ℝ := w / (1 + w + w * v) - w / (1 + w * v)

/-- `J(w) = ∫₀¹ (w/(1 + w + w v) - w/(1 + w v)) L(w, v) dv`. -/
noncomputable def i12HSUJ (w : ℝ) : ℝ := ∫ v in Ioo (0 : ℝ) 1, i12HSUR w v * i12HSUL w v

/-- `∂_w L = 2v/(1 + w v) - (1 + v)/(1 + w + w v) + 1/(1 + w)`. -/
noncomputable def i12HSULw (w v : ℝ) : ℝ :=
  2 * v / (1 + w * v) - (1 + v) / (1 + w + w * v) + 1 / (1 + w)

/-- The `w`-derivative of the integrand of `J`. -/
noncomputable def i12HSUJd (w v : ℝ) : ℝ :=
  (((1 + w + w * v) ^ 2)⁻¹ - ((1 + w * v) ^ 2)⁻¹) * i12HSUL w v + i12HSUR w v * i12HSULw w v

theorem hasDerivAt_i12HSUL_w {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => i12HSUL w v) (i12HSULw w v) w := by
  have h1 : 0 < 1 + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have h3 : 0 < 1 + w + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have h2 : 0 < 1 + w := by linarith
  have da : HasDerivAt (fun w => 1 + w * v) v w := by
    simpa using ((hasDerivAt_id w).mul_const v).const_add 1
  have dc : HasDerivAt (fun w => 1 + w + w * v) (1 + v) w := by
    exact (((hasDerivAt_id' w).const_add 1).add ((hasDerivAt_id' w).mul_const v)).congr_deriv
      (by ring)
  have dd : HasDerivAt (fun w => 1 + w) 1 w := by simpa using (hasDerivAt_id w).const_add 1
  have h := ((((da.log h1.ne').const_mul 2).sub_const (log (1 - v))).sub
    (dc.log h3.ne')).add (dd.log h2.ne')
  exact h.congr_deriv (by unfold i12HSULw; ring)

theorem hasDerivAt_i12HSUR_w {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => i12HSUR w v) (((1 + w + w * v) ^ 2)⁻¹ - ((1 + w * v) ^ 2)⁻¹) w := by
  have h1 : 0 < 1 + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have h3 : 0 < 1 + w + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have da : HasDerivAt (fun w => 1 + w * v) v w := by
    simpa using ((hasDerivAt_id w).mul_const v).const_add 1
  have dc : HasDerivAt (fun w => 1 + w + w * v) (1 + v) w := by
    exact (((hasDerivAt_id' w).const_add 1).add ((hasDerivAt_id' w).mul_const v)).congr_deriv
      (by ring)
  have h := ((hasDerivAt_id w).div dc h3.ne').sub ((hasDerivAt_id w).div da h1.ne')
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem hasDerivAt_i12HSUJ_integrand {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => i12HSUR w v * i12HSUL w v) (i12HSUJd w v) w := by
  have h := (hasDerivAt_i12HSUR_w hw hv).mul (hasDerivAt_i12HSUL_w hw hv)
  exact h.congr_deriv (by unfold i12HSUJd; ring)

theorem abs_i12HSUR_le {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |i12HSUR w v| ≤ 2 * w := by
  have h1 : 1 ≤ 1 + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have h3 : 1 ≤ 1 + w + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have e1 : 0 ≤ w / (1 + w + w * v) := by positivity
  have e1' : w / (1 + w + w * v) ≤ w := div_le_self hw h3
  have e2 : 0 ≤ w / (1 + w * v) := by positivity
  have e2' : w / (1 + w * v) ≤ w := div_le_self hw h1
  unfold i12HSUR
  rw [abs_le]
  constructor <;> linarith

theorem abs_i12HSULw_le {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |i12HSULw w v| ≤ 5 := by
  have h1 : 1 ≤ 1 + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have h3 : 1 ≤ 1 + w + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have e1 : 0 ≤ 2 * v / (1 + w * v) := by have := hv.1; positivity
  have e1' : 2 * v / (1 + w * v) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hv.2, mul_nonneg hw hv.1.le]
  have e2 : 0 ≤ (1 + v) / (1 + w + w * v) := by have := hv.1; positivity
  have e2' : (1 + v) / (1 + w + w * v) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hv.2, mul_nonneg hw hv.1.le]
  have e3 : 0 ≤ 1 / (1 + w) := by positivity
  have e3' : 1 / (1 + w) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  unfold i12HSULw
  rw [abs_le]
  constructor <;> linarith

/-- `|L(w, v)|` is bounded uniformly for `0 ≤ w ≤ T`. -/
theorem abs_i12HSUL_le_T {w v T : ℝ} (hw : 0 ≤ w) (hT : w ≤ T) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |i12HSUL w v| ≤ 2 * log (1 + T) + log (1 + 2 * T) + |log v| + |log (1 - v)| := by
  have h := abs_i12HSUL_le hw hv
  have a : log (1 + w) ≤ log (1 + T) := log_le_log (by linarith) (by linarith)
  have b : log (1 + 2 * w) ≤ log (1 + 2 * T) := log_le_log (by linarith) (by linarith)
  linarith

theorem abs_i12HSUJd_le {w v T : ℝ} (hw : 0 ≤ w) (hT : w ≤ T) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |i12HSUJd w v| ≤
      2 * (2 * log (1 + T) + log (1 + 2 * T) + 5 * T + |log v| + |log (1 - v)|) ^ 1 := by
  have h1 : 1 ≤ 1 + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have h3 : 1 ≤ 1 + w + w * v := by nlinarith [hv.1, mul_nonneg hw hv.1.le]
  have q1 : 0 ≤ ((1 + w + w * v) ^ 2)⁻¹ := by positivity
  have q1' : ((1 + w + w * v) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h3)
  have q2 : 0 ≤ ((1 + w * v) ^ 2)⁻¹ := by positivity
  have q2' : ((1 + w * v) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  have hq : |((1 + w + w * v) ^ 2)⁻¹ - ((1 + w * v) ^ 2)⁻¹| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hL := abs_i12HSUL_le_T hw hT hv
  have hR := abs_i12HSUR_le hw hv
  have hLw := abs_i12HSULw_le hw hv
  unfold i12HSUJd
  calc |(((1 + w + w * v) ^ 2)⁻¹ - ((1 + w * v) ^ 2)⁻¹) * i12HSUL w v +
        i12HSUR w v * i12HSULw w v|
      ≤ 2 * |i12HSUL w v| + 2 * w * 5 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        gcongr
    _ ≤ _ := by
        rw [pow_one]
        nlinarith [abs_nonneg (log v), abs_nonneg (log (1 - v))]

/-- The boundary factor `ρ = 1/((1 + w v)(1 + w)) - 1/((1 + w + w v)(1 + 2w))`, with
`(1 - v) ρ = ∂_w log((1 + w + w v)/(1 + w v)) - (its value at v = 1)`. -/
noncomputable def i12HSUrho (w v : ℝ) : ℝ :=
  1 / ((1 + w * v) * (1 + w)) - 1 / ((1 + w + w * v) * (1 + 2 * w))

/-- The coefficient `κ = 2(2w² + 2w + 1)/((1 + w)(1 + 2w))` of the reduced derivative. -/
noncomputable def i12HSUkappa (w : ℝ) : ℝ := 2 * (2 * w ^ 2 + 2 * w + 1) / ((1 + w) * (1 + 2 * w))

theorem abs_i12HSUrho_le {w v : ℝ} (hw : 0 ≤ w) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |i12HSUrho w v| ≤ 1 := by
  have h1 : 1 ≤ (1 + w * v) * (1 + w) := by
    nlinarith [mul_nonneg hw hv.1.le, mul_nonneg (mul_nonneg hw hw) hv.1.le]
  have h3 : 1 ≤ (1 + w + w * v) * (1 + 2 * w) := by
    nlinarith [mul_nonneg hw hv.1.le, mul_nonneg (mul_nonneg hw hw) hv.1.le]
  have e1 : 0 ≤ 1 / ((1 + w * v) * (1 + w)) := by positivity
  have e1' : 1 / ((1 + w * v) * (1 + w)) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
  have e2 : 0 ≤ 1 / ((1 + w + w * v) * (1 + 2 * w)) := by positivity
  have e2' : 1 / ((1 + w + w * v) * (1 + 2 * w)) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact h3
  unfold i12HSUrho
  rw [abs_le]; constructor <;> linarith

/-- The integration-by-parts identity: `∂_w(R L) = ∂_v((1 - v) ρ L) + κ (1/(1 + w + w v) -
1/(1 + w v))`. -/
theorem hasDerivAt_i12HSU_bdry {w v : ℝ} (hw : 0 ≤ w) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    HasDerivAt (fun v => (1 - v) * i12HSUrho w v * i12HSUL w v)
      (i12HSUJd w v - i12HSUkappa w * (1 / (1 + w + w * v) - 1 / (1 + w * v))) v := by
  have h1 : 0 < 1 + w * v := by positivity
  have h3 : 0 < 1 + w + w * v := by positivity
  have h2 : 0 < 1 + w := by linarith
  have h4 : 0 < 1 + 2 * w := by linarith
  have h5 : 1 - v ≠ 0 := by linarith
  have da : HasDerivAt (fun v => (1 + w * v) * (1 + w)) (w * (1 + w)) v := by
    exact ((((hasDerivAt_id' v).const_mul w).const_add 1).mul_const (1 + w)).congr_deriv
      (by ring)
  have dc : HasDerivAt (fun v => (1 + w + w * v) * (1 + 2 * w)) (w * (1 + 2 * w)) v := by
    exact ((((hasDerivAt_id' v).const_mul w).const_add (1 + w)).mul_const
      (1 + 2 * w)).congr_deriv (by ring)
  have dr : HasDerivAt (i12HSUrho w)
      (-(w * (1 + w)) / ((1 + w * v) * (1 + w)) ^ 2 +
        w * (1 + 2 * w) / ((1 + w + w * v) * (1 + 2 * w)) ^ 2) v := by
    have := ((hasDerivAt_const v (1 : ℝ)).div da (by positivity)).sub
      ((hasDerivAt_const v (1 : ℝ)).div dc (by positivity))
    exact this.congr_deriv (by ring)
  have h := ((((hasDerivAt_id' v).const_sub 1).mul dr).mul (hasDerivAt_i12HSUL hw hv0 hv1))
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold i12HSUJd i12HSUR i12HSULw i12HSUkappa i12HSUrho
  field_simp
  ring

/-- The primitive of `κ (1/(1 + w + w v) - 1/(1 + w v))` in `v`. -/
theorem hasDerivAt_i12HSU_kprim {w v : ℝ} (hw : 0 < w) (hv0 : 0 ≤ v) :
    HasDerivAt (fun v => i12HSUkappa w / w * (log (1 + w + w * v) - log (1 + w * v)))
      (i12HSUkappa w * (1 / (1 + w + w * v) - 1 / (1 + w * v))) v := by
  have h1 : 0 < 1 + w * v := by positivity
  have h3 : 0 < 1 + w + w * v := by positivity
  have da : HasDerivAt (fun v => 1 + w * v) w v := by
    simpa using ((hasDerivAt_id v).const_mul w).const_add 1
  have dc : HasDerivAt (fun v => 1 + w + w * v) w v := by
    simpa using ((hasDerivAt_id v).const_mul w).const_add (1 + w)
  have h := ((dc.log h3.ne').sub (da.log h1.ne')).const_mul (i12HSUkappa w / w)
  refine h.congr_deriv ?_
  field_simp

theorem continuousAt_i12HSUJd {w v : ℝ} (hw : 0 ≤ w) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ContinuousAt (i12HSUJd w) v := by
  have h1 : 1 + w * v ≠ 0 := by positivity
  have h3 : 1 + w + w * v ≠ 0 := by positivity
  have h2 : 1 + w ≠ 0 := by positivity
  have hL := continuousAt_i12HSUL hw hv0 hv1
  unfold i12HSUJd i12HSUR i12HSULw
  fun_prop (disch := first | assumption | exact pow_ne_zero 2 h1 | exact pow_ne_zero 2 h3)

theorem continuousAt_i12HSUJ_integrand {w v : ℝ} (hw : 0 ≤ w) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ContinuousAt (fun v => i12HSUR w v * i12HSUL w v) v := by
  have h1 : 1 + w * v ≠ 0 := by positivity
  have h3 : 1 + w + w * v ≠ 0 := by positivity
  have hL := continuousAt_i12HSUL hw hv0 hv1
  unfold i12HSUR
  fun_prop (disch := assumption)

/-- **The reduced derivative:** `∫₀¹ ∂_w(R L) dv = κ/w (log (1 + 2w) - 2 log (1 + w))`. -/
theorem integral_i12HSUJd {w : ℝ} (hw : 0 < w) :
    ∫ v in Ioo (0 : ℝ) 1, i12HSUJd w v =
      i12HSUkappa w / w * (log (1 + 2 * w) - 2 * log (1 + w)) := by
  set k : ℝ → ℝ := fun v => i12HSUkappa w * (1 / (1 + w + w * v) - 1 / (1 + w * v)) with hk
  have hkc : ContinuousOn k (Icc 0 1) := fun v hv => by
    have h1 : 1 + w * v ≠ 0 := by have := hv.1; positivity
    have h3 : 1 + w + w * v ≠ 0 := by have := hv.1; positivity
    exact ContinuousAt.continuousWithinAt (by rw [hk]; fun_prop (disch := assumption))
  have hki : IntegrableOn k (Ioo 0 1) :=
    (hkc.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self
  have hJi : IntegrableOn (i12HSUJd w) (Ioo 0 1) := by
    refine integrableOn_Ioo_of_abs_le_logs (C := 2 * log (1 + w) + log (1 + 2 * w) + 5 * w)
      (by have := i12HSU_C_nonneg hw.le; linarith) zero_le_two 1
      ((continuousOn_of_forall_continuousAt fun v hv => continuousAt_i12HSUJd hw.le hv.1.le
        hv.2).aestronglyMeasurable measurableSet_Ioo) fun v hv => ?_
    exact abs_i12HSUJd_le hw.le le_rfl hv
  have hla : Tendsto (fun v => (1 - v) * i12HSUrho w v * i12HSUL w v) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun v => (1 - v) * i12HSUrho w v * i12HSUL w v) 0 :=
      (hasDerivAt_i12HSU_bdry hw.le le_rfl zero_lt_one).continuousAt
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [i12HSUL_zero] using this
  have hlb : Tendsto (fun v => (1 - v) * i12HSUrho w v * i12HSUL w v) (𝓝[<] 1) (𝓝 0) := by
    have := tendsto_one_sub_mul_of_abs_le_logs (n := 1) (D := 1)
      (i12HSU_C_nonneg hw.le) zero_le_one (f := fun v => i12HSUrho w v * i12HSUL w v)
      fun v hv => by
        rw [abs_mul, pow_one, one_mul]
        have := abs_i12HSUL_le hw.le hv
        have := abs_i12HSUrho_le hw.le hv
        calc |i12HSUrho w v| * |i12HSUL w v| ≤ 1 * |i12HSUL w v| := by gcongr
          _ ≤ _ := by linarith
    exact this.congr fun v => by ring
  have key := setIntegral_Ioo_eq_add_of_eq_add_deriv (f := i12HSUJd w) (k := k)
    (h := fun v => (1 - v) * i12HSUrho w v * i12HSUL w v)
    (h' := fun v => i12HSUJd w v - k v) zero_lt_one (fun v _ => by ring) hki
    (fun v hv => hasDerivAt_i12HSU_bdry hw.le hv.1.le hv.2) (hJi.sub hki) hla hlb
  have hkc' : ContinuousOn k (uIcc 0 1) := by rw [uIcc_of_le zero_le_one]; exact hkc
  rw [key, sub_self, add_zero, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v hv => by
      rw [uIcc_of_le zero_le_one] at hv
      exact hasDerivAt_i12HSU_kprim hw hv.1) hkc'.intervalIntegrable]
  simp only [mul_zero, add_zero, mul_one, log_one, sub_zero]
  rw [show 1 + w + w = 1 + 2 * w by ring]
  ring

/-! ### `J` as harmonic polylogarithms of `y = w/(1 + w)` -/

/-- The weight-1 word combination `H(-1; y) - H(1; y) = log (1 + y) + log (1 - y)`. -/
def i12HSUJc : List (ℝ × List Letter) := [(1, [.negOne]), (-1, [.one])]

/-- Its negative. -/
def i12HSUJc' : List (ℝ × List Letter) := [(-1, [.negOne]), (1, [.one])]

/-- The weight-2 combination `H(0,-1) - H(0,1) + H(1,-1) - H(1,1) - H(-1,-1) + H(-1,1)`. -/
def i12HSUJw : List (ℝ × List Letter) :=
  (0, []) :: (prepend .zero i12HSUJc ++ prepend .one i12HSUJc ++ prepend .negOne i12HSUJc')

theorem hplSum_i12HSUJc {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    hplSum i12HSUJc y = log (1 + y) + log (1 - y) := by
  simp [i12HSUJc, hpl_negOne hy, hpl_one hy]

theorem hplSum_i12HSUJc' {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    hplSum i12HSUJc' y = -(log (1 + y) + log (1 - y)) := by
  simp [i12HSUJc', hpl_negOne hy, hpl_one hy]
  ring

theorem i12HSU_y_mem {w : ℝ} (hw : 0 < w) : w / (1 + w) ∈ Ioo (0 : ℝ) 1 :=
  ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩

theorem i12HSU_log_one_add_y_add_log_one_sub_y {w : ℝ} (hw : 0 < w) :
    log (1 + w / (1 + w)) + log (1 - w / (1 + w)) = log (1 + 2 * w) - 2 * log (1 + w) := by
  have h2 : (0 : ℝ) < 1 + w := by linarith
  have e1 : 1 + w / (1 + w) = (1 + 2 * w) / (1 + w) := by field_simp; ring
  have e2 : 1 - w / (1 + w) = (1 + w)⁻¹ := by field_simp; ring
  rw [e1, e2, log_div (by linarith) h2.ne', log_inv]
  ring

theorem hasDerivAt_i12HSU_y {w : ℝ} (hw : 0 ≤ w) :
    HasDerivAt (fun w => w / (1 + w)) (((1 + w) ^ 2)⁻¹) w := by
  have h := (hasDerivAt_id' w).div ((hasDerivAt_id' w).const_add 1) (by positivity)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The target `G(w) = 2 hplSum i12HSUJw (w/(1 + w))` has the derivative of `J`. -/
theorem hasDerivAt_i12HSUJ_target {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w => 2 * hplSum i12HSUJw (w / (1 + w)))
      (∫ v in Ioo (0 : ℝ) 1, i12HSUJd w v) w := by
  have hy := i12HSU_y_mem hw
  have h := ((hasDerivAt_hplSum_letters_comp 0 i12HSUJc i12HSUJc i12HSUJc'
    (hasDerivAt_i12HSU_y hw.le) hy).const_mul 2)
  refine h.congr_deriv ?_
  rw [integral_i12HSUJd hw, hplSum_i12HSUJc hy, hplSum_i12HSUJc' hy,
    i12HSU_log_one_add_y_add_log_one_sub_y hw]
  have h2 : (0 : ℝ) < 1 + w := by linarith
  have h4 : (0 : ℝ) < 1 + 2 * w := by linarith
  have e1 : 1 - w / (1 + w) = (1 + w)⁻¹ := by field_simp; ring
  have e2 : 1 + w / (1 + w) = (1 + 2 * w) / (1 + w) := by field_simp; ring
  rw [e1, e2]
  unfold i12HSUkappa
  field_simp
  ring

/-- The bound `|R L| ≤ 2w (C + |log v| + |log (1 - v)|)` for `w ≤ T`. -/
theorem abs_i12HSUJ_integrand_le {w v T : ℝ} (hw : 0 ≤ w) (hT : w ≤ T) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |i12HSUR w v * i12HSUL w v| ≤
      2 * w * (2 * log (1 + T) + log (1 + 2 * T) + |log v| + |log (1 - v)|) ^ 1 := by
  rw [abs_mul, pow_one]
  exact mul_le_mul (abs_i12HSUR_le hw hv) (abs_i12HSUL_le_T hw hT hv) (abs_nonneg _)
    (by positivity)

theorem i12HSU_continuousOn_logs (c : ℝ) :
    ContinuousOn (fun v : ℝ => 2 * (c + |log v| + |log (1 - v)|) ^ 1) (Ioo 0 1) :=
  continuousOn_of_forall_continuousAt fun v hv => by
    have h0 : v ≠ 0 := hv.1.ne'
    have h1 : 1 - v ≠ 0 := by linarith [hv.2]
    fun_prop (disch := assumption)

theorem i12HSU_integrableOn_logs {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun v : ℝ => 2 * (c + |log v| + |log (1 - v)|) ^ 1) (Ioo 0 1) :=
  integrableOn_Ioo_of_abs_le_logs hc zero_le_two 1
    ((i12HSU_continuousOn_logs c).aestronglyMeasurable measurableSet_Ioo) fun v _ =>
    (abs_of_nonneg (by positivity)).le

/-- `J(w) → 0` as `w → 0⁺`. -/
theorem tendsto_i12HSUJ_zero : Tendsto i12HSUJ (𝓝[>] 0) (𝓝 0) := by
  have hC : 0 ≤ 2 * log (1 + 1) + log (1 + 2 * 1) := i12HSU_C_nonneg zero_le_one
  have h := tendsto_setIntegral_param (g := fun v w => i12HSUR w v * i12HSUL w v)
    (g₀ := fun _ => 0) measurableSet_Ioo (l := 𝓝[>] (0 : ℝ))
    (B := fun v => 2 * (2 * log (1 + 1) + log (1 + 2 * 1) + |log v| + |log (1 - v)|) ^ 1)
    ?_ ?_ (i12HSU_integrableOn_logs hC) ?_
  · have e : i12HSUJ = fun y => ∫ v in Ioo (0 : ℝ) 1, i12HSUR y v * i12HSUL y v := rfl
    rw [e]
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (continuousOn_of_forall_continuousAt fun v hv =>
      continuousAt_i12HSUJ_integrand (le_of_lt hy) hv.1.le hv.2).aestronglyMeasurable
      measurableSet_Ioo
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy v hv
    refine (abs_i12HSUJ_integrand_le hy.1.le hy.2.le hv).trans ?_
    have : 0 ≤ (2 * log (1 + 1) + log (1 + 2 * 1) + |log v| + |log (1 - v)|) ^ 1 := by
      rw [pow_one]; positivity
    nlinarith [hy.2]
  · intro v hv
    have hc := (hasDerivAt_i12HSUJ_integrand (w := 0) le_rfl hv).continuousAt
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [i12HSUR] using this

/-- `G(w) = 2 hplSum i12HSUJw (w/(1 + w)) → 0` as `w → 0⁺`. -/
theorem tendsto_i12HSUJ_target_zero :
    Tendsto (fun w => 2 * hplSum i12HSUJw (w / (1 + w))) (𝓝[>] 0) (𝓝 0) := by
  have hy : Tendsto (fun w : ℝ => w / (1 + w)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : ContinuousAt (fun w : ℝ => w / (1 + w)) 0 :=
        (hasDerivAt_i12HSU_y le_rfl).continuousAt
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact (i12HSU_y_mem hw).1
  have hrest : Tendsto (hplSum (prepend .zero i12HSUJc ++ prepend .one i12HSUJc ++
      prepend .negOne i12HSUJc')) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_hplSum_zero fun e he => ?_
    simp only [i12HSUJc, i12HSUJc', prepend, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [AllZero]
  have := (hrest.comp hy).const_mul 2
  simp only [mul_zero] at this
  refine this.congr fun w => ?_
  simp [i12HSUJw]

/-- **`J` as harmonic polylogarithms:** for `w > 0` and `y = w/(1 + w)`,
`J(w) = 2 hplSum i12HSUJw y`. -/
theorem i12HSUJ_eq_hplSum {w : ℝ} (hw : 0 < w) :
    i12HSUJ w = 2 * hplSum i12HSUJw (w / (1 + w)) := by
  set T := w + 1
  have hCT : 0 ≤ 2 * log (1 + T) + log (1 + 2 * T) + 5 * T := by
    have := i12HSU_C_nonneg (w := T) (by positivity); positivity
  refine eqOn_setIntegral_of_hasDerivAt_left (g := fun v w => i12HSUR w v * i12HSUL w v)
    (g' := fun v w => i12HSUJd w v) measurableSet_Ioo (p := 0) (q := T) (c := 0)
    (by positivity) ?_ ?_ ?_ ?_ ?_ ?_ tendsto_i12HSUJ_zero tendsto_i12HSUJ_target_zero w
    ⟨hw, by linarith⟩
  · intro y hy
    exact (continuousOn_of_forall_continuousAt fun v hv =>
      continuousAt_i12HSUJ_integrand hy.1.le hv.1.le hv.2).aestronglyMeasurable
      measurableSet_Ioo
  · intro y hy
    exact integrableOn_Ioo_of_abs_le_logs (i12HSU_C_nonneg hy.1.le) (by linarith [hy.1]) 1
      ((continuousOn_of_forall_continuousAt fun v hv =>
        continuousAt_i12HSUJ_integrand hy.1.le hv.1.le hv.2).aestronglyMeasurable
        measurableSet_Ioo) fun v hv => abs_i12HSUJ_integrand_le hy.1.le le_rfl hv
  · intro y hy
    exact (continuousOn_of_forall_continuousAt fun v hv =>
      continuousAt_i12HSUJd hy.1.le hv.1.le hv.2).aestronglyMeasurable measurableSet_Ioo
  · intro x _
    refine ⟨1, one_pos, _, i12HSU_integrableOn_logs hCT, fun v hv y hy _ => ?_⟩
    exact abs_i12HSUJd_le hy.1.le hy.2.le hv
  · intro v hv y hy
    exact hasDerivAt_i12HSUJ_integrand hy.1.le hv
  · intro x hx
    exact hasDerivAt_i12HSUJ_target hx.1

/-- **`J` as harmonic polylogarithms of `y = w/(1 + w)`:**
`J = 2 (H(0,-1) - H(0,1) + H(1,-1) - H(1,1) - H(-1,-1) + H(-1,1))(y)`. -/
theorem i12HSUJ_hpl {w : ℝ} (hw : 0 < w) :
    i12HSUJ w = 2 * (hpl [.zero, .negOne] (w / (1 + w)) - hpl [.zero, .one] (w / (1 + w)) +
      hpl [.one, .negOne] (w / (1 + w)) - hpl [.one, .one] (w / (1 + w)) -
      hpl [.negOne, .negOne] (w / (1 + w)) + hpl [.negOne, .one] (w / (1 + w))) := by
  rw [i12HSUJ_eq_hplSum hw]
  simp [i12HSUJw, i12HSUJc, i12HSUJc']
  ring

/-! ### `U₂` -/

/-- **`U₂` in terms of `U₁` and `J`:** `U₂ = 2 U₁ + (1 + 2w)/(w²(1 + w)²) J` for `w > 0`. -/
theorem i12HSU_two_eq {w : ℝ} (hw : 0 < w) :
    i12HSU 2 w = 2 * i12HSU 1 w + (1 + 2 * w) / (w ^ 2 * (1 + w) ^ 2) * i12HSUJ w := by
  have hC := i12HSU_C_nonneg hw.le
  set f1 : ℝ → ℝ := fun v => ((1 + w * v) ^ 2)⁻¹ * (i12HSUL w v ^ 1 / (Nat.factorial 1 : ℝ))
    with hf1
  have hf1i : IntegrableOn f1 (Ioo 0 1) := by
    refine integrableOn_Ioo_of_abs_le_logs hC zero_le_one 1
      ((continuousOn_of_forall_continuousAt fun v hv => ?_).aestronglyMeasurable
        measurableSet_Ioo) fun v hv => ?_
    · have h1 : (1 + w * v) ^ 2 ≠ 0 := pow_ne_zero 2 (by have := hv.1; positivity)
      exact (ContinuousAt.inv₀ (f := fun v => (1 + w * v) ^ 2) (by fun_prop) h1).mul
        (((continuousAt_i12HSUL hw.le hv.1.le hv.2).pow _).div_const _)
    · have h1 : 1 ≤ (1 + w * v) ^ 2 := one_le_pow₀ (by nlinarith [hv.1])
      have hb := abs_i12HSUL_le hw.le hv
      rw [hf1]
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, one_mul]
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (1 + w * v) ^ 2)]
      calc ((1 + w * v) ^ 2)⁻¹ * |i12HSUL w v| ≤ 1 * |i12HSUL w v| := by
            gcongr; exact inv_le_one_of_one_le₀ h1
        _ ≤ _ := by linarith
  have hf2i : IntegrableOn (fun v => i12HSUR w v * i12HSUL w v) (Ioo 0 1) :=
    integrableOn_Ioo_of_abs_le_logs hC (by linarith) 1
      ((continuousOn_of_forall_continuousAt fun v hv =>
        continuousAt_i12HSUJ_integrand hw.le hv.1.le hv.2).aestronglyMeasurable
        measurableSet_Ioo) fun v hv => abs_i12HSUJ_integrand_le hw.le le_rfl hv
  have hM : ∀ v ∈ Ioo (0 : ℝ) 1, i12HSUM w v * (i12HSUL w v ^ 1 / (Nat.factorial 1 : ℝ)) =
      2 * (1 + w) * f1 v + (1 + 2 * w) / w ^ 2 * (i12HSUR w v * i12HSUL w v) := by
    intro v hv
    have h1 : 0 < 1 + w * v := by have := hv.1; positivity
    have h3 : 0 < 1 + w + w * v := by have := hv.1; positivity
    rw [hf1]
    unfold i12HSUM i12HSUR
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    field_simp
    ring
  rw [i12HSU_succ hw.le 1, setIntegral_congr_fun measurableSet_Ioo hM,
    integral_add (hf1i.const_mul _) (hf2i.const_mul _), integral_const_mul, integral_const_mul]
  unfold i12HSU i12HSUJ
  rw [← hf1]
  have h2 : (1 + w) ≠ 0 := by linarith
  field_simp

end QED.ThreeLoopD
