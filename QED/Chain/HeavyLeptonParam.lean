/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.VPChainPiHat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The heavy-lepton bubble: `Π̂` in the threshold variable, and the rationalizing map

Helper analysis for obligation O3-M3 of `docs/HIGHER-LOOP-PLAN.md` (heavy-lepton VP insertion,
Passera (10)). It is **not** frozen.

For a loop lepton of mass `M = 1/y` (`0 < y < 1`, open-line mass `1`), the insertion integrand is
`(1-x) Π̂(y² x²/(1-x))`, with `Π̂ = QED.Chain.piHat`. Its closed form in `x` involves
`√(y²x² - 4x + 4)`; this file rationalizes it.

* `piHatP p`: for `p > 0`, `Π̂(1/(p(1+p))) = piHatP p =
  ⅓[-5/3 + 4p(1+p) + (1 - 2p(1+p))(2p+1)(log(1+p) - log p)]` (`piHat_inv_mul_one_add`). This is
  the plan's Landau form with `a = 4p(1+p)`, `β = 2p+1`.
* The map `w ↦ x = phi y w = (1-w²)/(1+yw)` sends `(0,1)` onto `(0,1)`, decreasing, with
  derivative `-jac y w`. Its inverse is `omega y x = (√(y²x² - 4x + 4) - yx)/2`.
* On this curve `y² x²/(1-x) = 1/(p(1+p))` with `p = pOf y w = w(1+yw)/(y(1-w²))`, and
  `log(1+p) - log p = ell y w = log(y+w) - log w - log(1+yw)`.

## Main statements

* `piHat_inv_mul_one_add`: the closed form of `Π̂` in the variable `p`.
* `phi_omega`, `omega_mem_Ioo`, `hasDerivAt_omega`: the inverse map and its derivative.
* `tendsto_omega_zero`, `tendsto_omega_one`: `omega → 1⁻` as `x → 0⁺`, `omega → 0⁺` as `x → 1⁻`.
* `heavy_integrand_eq`: `(1-x) Π̂(y² x²/(1-x)) = (1 - phi y w) piHatP (pOf y w)` at `w = omega y x`.
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.Chain.HeavyLepton

/-! ### `Π̂` in the variable `p` -/

/-- `Π̂(1/(p(1+p)))` in closed form, `p > 0`. -/
noncomputable def piHatP (p : ℝ) : ℝ :=
  (-5 / 3 + 4 * p * (1 + p) + (1 - 2 * p * (1 + p)) * (2 * p + 1) * (log (1 + p) - log p)) / 3

/-- A `t`-antiderivative of `t(1-t)(log(p+t) + log(1+p-t) - log p - log(1+p))`. -/
noncomputable def tPrimP (p t : ℝ) : ℝ :=
  2 * p ^ 2 * t / 3 + 2 * p * t / 3 + 2 * t ^ 3 / 9 - t ^ 2 / 3 - t / 6 +
    (-p ^ 3 / 3 - p ^ 2 / 2 - t ^ 3 / 3 + t ^ 2 / 2) * log (p + t) +
    (p ^ 3 / 3 + p ^ 2 / 2 - 1 / 6 - t ^ 3 / 3 + t ^ 2 / 2) * log (1 + p - t) +
    (t ^ 3 / 3 - t ^ 2 / 2) * (log p + log (1 + p))

theorem hasDerivAt_tPrimP {p t : ℝ} (ha : 0 < p + t) (hb : 0 < 1 + p - t) :
    HasDerivAt (tPrimP p)
      (t * (1 - t) * (log (p + t) + log (1 + p - t) - log p - log (1 + p))) t := by
  have h1 : HasDerivAt (fun t => p + t) 1 t := by simpa using (hasDerivAt_id' t).const_add p
  have h2 : HasDerivAt (fun t => 1 + p - t) (-1) t := by
    simpa using (hasDerivAt_id' t).const_sub (1 + p)
  have hc : HasDerivAt (fun t : ℝ => -1 / 3 * t ^ 3 + 1 / 2 * t ^ 2) (-t ^ 2 + t) t := by
    have := ((hasDerivAt_pow 3 t).const_mul (-1 / 3)).add ((hasDerivAt_pow 2 t).const_mul (1 / 2))
    refine this.congr_deriv ?_
    push_cast
    ring
  have hP : HasDerivAt (fun t : ℝ => 2 * p ^ 2 * t / 3 + 2 * p * t / 3 + 2 * t ^ 3 / 9 -
      t ^ 2 / 3 - t / 6) (2 * p ^ 2 / 3 + 2 * p / 3 + 2 * t ^ 2 / 3 - 2 * t / 3 - 1 / 6) t := by
    have := (((((hasDerivAt_id' t).const_mul (2 * p ^ 2 / 3)).add
      ((hasDerivAt_id' t).const_mul (2 * p / 3))).add
      ((hasDerivAt_pow 3 t).const_mul (2 / 9))).sub
      ((hasDerivAt_pow 2 t).const_mul (1 / 3))).sub ((hasDerivAt_id' t).const_mul (1 / 6))
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    · push_cast
      ring
    · simp only [Pi.add_apply, Pi.sub_apply]
      ring
  have h := ((hP.add (((hc.const_add (-p ^ 3 / 3 - p ^ 2 / 2))).mul (h1.log ha.ne'))).add
    ((hc.const_add (p ^ 3 / 3 + p ^ 2 / 2 - 1 / 6)).mul (h2.log hb.ne'))).sub
    (hc.mul_const (log p + log (1 + p)))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · field_simp
    ring
  · simp only [tPrimP, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring

/-- For `p > 0`, `1 + t(1-t)/(p(1+p)) = (p+t)(1+p-t)/(p(1+p))`. -/
theorem one_add_inv_mul_eq {p t : ℝ} (hp : 0 < p) :
    1 + t * (1 - t) * (1 / (p * (1 + p))) = (p + t) * (1 + p - t) / (p * (1 + p)) := by
  have : p * (1 + p) ≠ 0 := by positivity
  field_simp
  ring

/-- **`Π̂` in the variable `p`.** For `p > 0`, `Π̂(1/(p(1+p))) = piHatP p`. -/
theorem piHat_inv_mul_one_add {p : ℝ} (hp : 0 < p) :
    piHat (1 / (p * (1 + p))) = piHatP p := by
  have hab : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < p + t ∧ 0 < 1 + p - t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
      t * (1 - t) * log (1 + t * (1 - t) * (1 / (p * (1 + p)))) =
        t * (1 - t) * (log (p + t) + log (1 + p - t) - log p - log (1 + p)) := by
    intro t ht
    obtain ⟨ha, hb⟩ := hab t ht
    rw [one_add_inv_mul_eq hp, log_div (mul_pos ha hb).ne' (by positivity), log_mul ha.ne' hb.ne',
      log_mul hp.ne' (by positivity)]
    ring
  have hcont : ContinuousOn
      (fun t => t * (1 - t) * (log (p + t) + log (1 + p - t) - log p - log (1 + p)))
      (uIcc 0 1) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.sub (ContinuousOn.sub
      (ContinuousOn.add ?_ ?_) continuousOn_const) continuousOn_const)
    · exact ContinuousOn.log (by fun_prop) fun t ht => (hab t ht).1.ne'
    · exact ContinuousOn.log (by fun_prop) fun t ht => (hab t ht).2.ne'
  unfold piHat
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_tPrimP (hab t ht).1 (hab t ht).2) hcont.intervalIntegrable]
  simp only [tPrimP, piHatP, add_zero, sub_zero]
  ring_nf

/-! ### The rationalizing map -/

/-- The map `w ↦ x = (1-w²)/(1+yw)`. -/
noncomputable def phi (y w : ℝ) : ℝ := (1 - w ^ 2) / (1 + y * w)

/-- `-phi'`: `(yw² + 2w + y)/(1+yw)²`. -/
noncomputable def jac (y w : ℝ) : ℝ := (y * w ^ 2 + 2 * w + y) / (1 + y * w) ^ 2

/-- The threshold variable `p = w(1+yw)/(y(1-w²))`. -/
noncomputable def pOf (y w : ℝ) : ℝ := w * (1 + y * w) / (y * (1 - w ^ 2))

/-- The inverse of `phi y`: `(√(y²x² - 4x + 4) - yx)/2`. -/
noncomputable def omega (y x : ℝ) : ℝ := (√(y ^ 2 * x ^ 2 - 4 * x + 4) - y * x) / 2

/-- `log(1+p) - log p` in the variable `w`: `log(y+w) - log w - log(1+yw)`. -/
noncomputable def ell (y w : ℝ) : ℝ := log (y + w) - log w - log (1 + y * w)

theorem hasDerivAt_phi {y w : ℝ} (h : 1 + y * w ≠ 0) : HasDerivAt (phi y) (-jac y w) w := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + y * w) y w := by
    simpa using ((hasDerivAt_id' w).const_mul y).const_add 1
  have h2 : HasDerivAt (fun w : ℝ => 1 - w ^ 2) (-(2 * w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_sub 1
  refine ((h2.div h1 h).congr_deriv ?_)
  unfold jac
  field_simp
  ring

theorem jac_pos {y w : ℝ} (hy : 0 < y) (hw : 0 ≤ w) : 0 < jac y w := by
  unfold jac
  positivity

theorem pOf_pos {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) : 0 < pOf y w := by
  obtain ⟨h0, h1⟩ := hw
  unfold pOf
  have : 0 < 1 - w ^ 2 := by nlinarith
  positivity

theorem sqrt_arg_pos {y x : ℝ} (hx : x < 1) : 0 < y ^ 2 * x ^ 2 - 4 * x + 4 := by
  nlinarith [sq_nonneg (y * x)]

theorem omega_quadratic {y x : ℝ} (hx : x < 1) :
    omega y x ^ 2 + x * y * omega y x + x - 1 = 0 := by
  have hs := Real.sq_sqrt (sqrt_arg_pos (y := y) hx).le
  unfold omega
  linear_combination hs / 4

theorem omega_mem_Ioo {y x : ℝ} (hy : 0 < y) (hx : x ∈ Ioo (0 : ℝ) 1) :
    omega y x ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hpos := sqrt_arg_pos (y := y) hx1
  have hs := Real.sq_sqrt hpos.le
  have hr := Real.sqrt_nonneg (y ^ 2 * x ^ 2 - 4 * x + 4)
  set r := √(y ^ 2 * x ^ 2 - 4 * x + 4)
  unfold omega
  constructor
  · nlinarith [mul_pos hy hx0]
  · nlinarith [mul_pos hy hx0]

theorem one_add_mul_omega_pos {y x : ℝ} (hy : 0 < y) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < 1 + y * omega y x := by
  have := (omega_mem_Ioo hy hx).1
  positivity

/-- `phi y (omega y x) = x` for `x < 1` (with `1 + y omega ≠ 0`). -/
theorem phi_omega {y x : ℝ} (hx : x < 1) (h : 1 + y * omega y x ≠ 0) :
    phi y (omega y x) = x := by
  have hq := omega_quadratic (y := y) hx
  unfold phi
  rw [div_eq_iff h]
  linear_combination -hq

theorem continuous_omega (y : ℝ) : Continuous (omega y) := by
  unfold omega
  fun_prop

theorem hasDerivAt_omega {y x : ℝ} (hy : 0 < y) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (omega y) (-jac y (omega y x))⁻¹ x := by
  refine HasDerivAt.of_local_left_inverse (continuous_omega y).continuousAt
    (hasDerivAt_phi (one_add_mul_omega_pos hy hx).ne') ?_ ?_
  · exact neg_ne_zero.2 (jac_pos hy (omega_mem_Ioo hy hx).1.le).ne'
  · filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    exact phi_omega hz.2 (one_add_mul_omega_pos hy hz).ne'

theorem omega_zero (y : ℝ) : omega y 0 = 1 := by
  unfold omega
  rw [show y ^ 2 * 0 ^ 2 - 4 * 0 + 4 = (2 : ℝ) ^ 2 by ring, Real.sqrt_sq (by norm_num)]
  ring

theorem omega_one {y : ℝ} (hy : 0 ≤ y) : omega y 1 = 0 := by
  unfold omega
  rw [show y ^ 2 * 1 ^ 2 - 4 * 1 + 4 = y ^ 2 by ring, Real.sqrt_sq hy]
  ring

/-- `omega y x → 1⁻` as `x → 0⁺`. -/
theorem tendsto_omega_zero {y : ℝ} (hy : 0 < y) :
    Tendsto (omega y) (𝓝[>] 0) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((continuous_omega y).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [omega_zero] at this
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with x hx
    exact (omega_mem_Ioo hy hx).2

/-- `omega y x → 0⁺` as `x → 1⁻`. -/
theorem tendsto_omega_one {y : ℝ} (hy : 0 < y) :
    Tendsto (omega y) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((continuous_omega y).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    rwa [omega_one hy.le] at this
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with x hx
    exact (omega_mem_Ioo hy hx).1

/-- On the curve `x = phi y w`, `y² x²/(1-x) = 1/(p(1+p))` with `p = pOf y w`. -/
theorem photonVar_phi {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) :
    y ^ 2 * (phi y w ^ 2 / (1 - phi y w)) = 1 / (pOf y w * (1 + pOf y w)) := by
  obtain ⟨h0, h1⟩ := hw
  have hd : 0 < 1 + y * w := by positivity
  have hs : 0 < 1 - w ^ 2 := by nlinarith
  have hq : 1 - phi y w = w * (y + w) / (1 + y * w) := by
    unfold phi
    field_simp
    ring
  have hq' : 1 + pOf y w = (y + w) / (y * (1 - w ^ 2)) := by
    unfold pOf
    field_simp
    ring
  rw [hq, hq']
  unfold phi pOf
  field_simp

/-- `log(1+p) - log p = ell y w` for `p = pOf y w`. -/
theorem log_one_add_pOf_sub {y w : ℝ} (hy : 0 < y) (hw : w ∈ Ioo (0 : ℝ) 1) :
    log (1 + pOf y w) - log (pOf y w) = ell y w := by
  obtain ⟨h0, h1⟩ := hw
  have hd : 0 < 1 + y * w := by positivity
  have hs : 0 < 1 - w ^ 2 := by nlinarith
  have hp := pOf_pos hy ⟨h0, h1⟩
  rw [← log_div (by positivity) hp.ne']
  have : (1 + pOf y w) / pOf y w = (y + w) / (w * (1 + y * w)) := by
    unfold pOf
    field_simp
    ring
  rw [this, log_div (by positivity) (by positivity), log_mul h0.ne' hd.ne']
  unfold ell
  ring

/-- **The integrand in the variable `w`.** For `x ∈ (0,1)` and `w = omega y x`,
`(1-x) Π̂(y² x²/(1-x)) = (1 - phi y w) piHatP (pOf y w)`. -/
theorem heavy_integrand_eq {y x : ℝ} (hy : 0 < y) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x))) =
      (1 - phi y (omega y x)) * piHatP (pOf y (omega y x)) := by
  have hw := omega_mem_Ioo hy hx
  have hphi := phi_omega hx.2 (one_add_mul_omega_pos hy hx).ne'
  conv_lhs => rw [← hphi]
  rw [photonVar_phi hy hw, piHat_inv_mul_one_add (pOf_pos hy hw)]

end QED.Chain.HeavyLepton
