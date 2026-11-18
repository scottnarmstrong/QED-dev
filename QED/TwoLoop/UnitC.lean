/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitX
public import QED.TwoLoop.UnitLS
import QED.Polylog.ExtraIntegralsC
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The one-dimensional integral of the corner unit (helper level, O2-25)

Section 6.6 of `docs/TWO-LOOP-UNITS.md` reduces the finite part of the corner unit C,
`b_C = 2 ∫_{Δ₂} ∫₀¹ G_C - 3/2` (eq. (6.5)), to `b_C = 2 ∫₀¹ K_C - 3/2` (eq. (6.9)) with an
explicit kernel `K_C` (eq. (6.10), `cornerKernel`) in the functions `Li₂ Y`,
`D(Y) = Li₂ (1 - 2Y) - Li₂ (2Y - 1)` (`crossedD`), `log Y` and `log (1 - Y)`. Integration by
parts gives `K_C = G_C' + K_m` on `(0, 1) \ {1/2}` (eq. (6.11)), with an explicit boundary
function `G_C` (`cornerBoundary`) and a combination `K_m` (`cornerMasterKernel`) of the master
integrals `M₁, …, M₈` of the crossed-ladder unit (section 4.5.4; `QED.TwoLoop.UnitX`). No new
master integral occurs.

## Main statements

* `QED.TwoLoop.Units.intervalIntegrable_cornerKernel`: `K_C` is integrable on `[0, 1]`.
* `QED.TwoLoop.Units.hasDerivAt_cornerBoundary`: `G_C' = K_C - K_m` on `(0, 1) \ {1/2}`.
* `QED.TwoLoop.Units.tendsto_cornerBoundary_zero`, `…_one`: `G_C(0⁺) = -1/3`,
  `G_C(1⁻) = -47/48 - ζ(2)/2`.
* `QED.TwoLoop.Units.intervalIntegrable_and_integral_cornerKernel`:
  `∫₀¹ K_C = -31/48 + ζ(2)/6 + ζ(2) log 2 - ζ(3)/4`.
* `QED.TwoLoop.Units.cornerUnit_finitePart_value`:
  `2 ∫₀¹ K_C - 3/2 = -67/24 + 2 ζ(2) log 2 + ζ(2)/3 - ζ(3)/2`, BMR-I's finite part of C.
* `QED.TwoLoop.Units.selfEnergyCornerUnit_value`: with `b_S = 2 ∫₀¹ K_S`
  (`QED.TwoLoop.UnitLS`), `b_S + b_C = -7/3 + 2 ζ(2) log 2 - ζ(3)/2`, BMR-I's value of S + C.
* `QED.TwoLoop.Units.cornerUnit_assembly`: the arithmetic of the assembly (6.13) from the master
  integrals, in the form of `crossedUnit_assembly`.

Here `ζ(2) = π²/6` and `ζ(3) = zeta3`.

**Scope.** Helper level: this file evaluates the explicit one-dimensional integral `∫₀¹ K_C`.
Not proved here: the representation (6.5) of C and its link to the model (section 8 of the
document), the `x`-integration giving `Φ_C` (6.7) and the `ξ`-integration giving `K_C` (6.10).
Those steps are derived in exact rational arithmetic and checked numerically (mode
`cornerexact` of `scripts/numerics/two_loop_unit_integrals.py`), not proved.

## Integrability

On `(0, 1)`, `K_C` is a combination, with polynomial coefficients, of `Li₂`, `D`, the integrands
of the masters, and the three functions `(Li₂ Y + log (1 - Y))/Y²`, `(log (1 - Y) + Y)/Y²` and
`log Y (log (1 - Y) + Y)/Y²` (`cornerKernel_eq_decomp`), which carry the cancellation of the
double poles at `Y = 0`. Each is integrable on `[0, 1]`.
-/

public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.TwoLoop.Units

/-! ### The kernel, the boundary function and the master combination -/

/-- The corner kernel `K_C` of eq. (6.10) of `docs/TWO-LOOP-UNITS.md`. -/
noncomputable def cornerKernel (Y : ℝ) : ℝ :=
  (Y - 1 / 2 - 1 / (3 * (Y - 1)) - 1 / (6 * Y) + 1 / (2 * Y ^ 2)) * Li₂ Y +
    (2 * Y / 3 - 1 / 3 - 1 / (6 * (Y - 1)) - 1 / (6 * Y)) * crossedD Y +
    (Y / 6 - 1 / 12 - 1 / (12 * (Y - 1))) * log Y ^ 2 +
    (Y / 3 - 1 / 6 - 1 / (6 * Y) + 1 / (2 * Y ^ 2)) * (log Y * log (1 - Y)) +
    (Y / 6 - 1 / 4 - 5 / (12 * (Y - 1)) + 1 / (2 * Y)) * log Y +
    (-2 * Y / 3 + 4 / 3 - 5 / (6 * Y) + 1 / (6 * Y ^ 2)) * log (1 - Y) +
    (-2 * Y / 3 + 1 / 3 + 1 / (12 * (Y - 1)) + 1 / (4 * Y)) * (π ^ 2 / 6) +
    (31 * Y / 24 - 7 / 6 - 1 / (3 * Y))

/-- The boundary function `G_C` of eq. (6.11). -/
noncomputable def cornerBoundary (Y : ℝ) : ℝ :=
  (Y ^ 2 / 2 - Y / 2 - 1 / (2 * Y)) * Li₂ Y + (Y ^ 2 - Y) / 3 * crossedD Y +
    (Y ^ 2 - Y) / 12 * log Y ^ 2 + (Y ^ 2 / 6 - Y / 6 - 1 / (2 * Y)) * (log Y * log (1 - Y)) +
    (Y ^ 2 / 12 - Y / 4 - 1 / 2) * log Y +
    (-Y ^ 2 / 3 + 7 * Y / 6 - 2 / 3 - 1 / (6 * Y)) * log (1 - Y) -
    π ^ 2 / 6 * (Y ^ 2 - Y) / 3 + 37 * Y ^ 2 / 48 - 7 * Y / 4

/-- The combination `K_m` of master integrands in eq. (6.11). -/
noncomputable def cornerMasterKernel (Y : ℝ) : ℝ :=
  -(1 / 6) * (Li₂ Y / Y + log Y * log (1 - Y) / Y + (crossedD Y - π ^ 2 / 4) / Y +
      2 * ((Li₂ Y - π ^ 2 / 6) / (Y - 1)) + (crossedD Y + π ^ 2 / 4) / (Y - 1)) -
    1 / 12 * (log Y ^ 2 / (Y - 1) - log Y / (Y - 1)) - 5 / 6 * (log (1 - Y) / Y) -
    1 / 6 * ((log Y - log (1 - Y)) / (2 * Y - 1))

/-! ### Integrability of `K_C` -/

/-- On `(0, 1)`, `K_C` is a combination of integrable functions with polynomial coefficients. -/
theorem cornerKernel_eq_decomp {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    cornerKernel Y =
      (Y - 1 / 2) * Li₂ Y + (2 * Y / 3 - 1 / 3) * crossedD Y +
        ((Y / 6 - 1 / 12) * (Y - 1) - 1 / 12) * (log Y ^ 2 / (Y - 1)) +
        ((Y / 3 - 1 / 6) * Y - 1 / 6) * (log Y * log (1 - Y) / Y) +
        ((Y / 6 - 1 / 4) * (Y - 1) - 5 / 12) * (log Y / (Y - 1)) +
        ((-2 * Y / 3 + 4 / 3) * Y - 5 / 6) * (log (1 - Y) / Y) +
        (π ^ 2 / 6 * (-2 * Y / 3 + 1 / 3) + (31 * Y / 24 - 7 / 6)) -
        1 / 3 * ((Li₂ Y - π ^ 2 / 6) / (Y - 1)) - 1 / 6 * ((crossedD Y + π ^ 2 / 4) / (Y - 1)) -
        1 / 6 * (Li₂ Y / Y) - 1 / 6 * ((crossedD Y - π ^ 2 / 4) / Y) +
        1 / 2 * ((Li₂ Y + log (1 - Y)) / Y ^ 2) - 1 / 3 * ((log (1 - Y) + Y) / Y ^ 2) +
        1 / 2 * (log Y * (log (1 - Y) + Y) / Y ^ 2) := by
  obtain ⟨hY0, hY1⟩ := hY
  have h0 : Y ≠ 0 := hY0.ne'
  have h1 : Y - 1 ≠ 0 := by linarith
  unfold cornerKernel
  field_simp
  ring

/-- A continuous function times a function integrable on `[0, 1]` is integrable on `[0, 1]`. -/
theorem intervalIntegrable_mul_unit {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    {g : ℝ → ℝ} (hg : Continuous g) : IntervalIntegrable (fun x => g x * f x) volume 0 1 :=
  hf.continuousOn_mul hg.continuousOn

theorem intervalIntegrable_Li₂_unit : IntervalIntegrable Li₂ volume 0 1 :=
  (continuousOn_Li₂.mono (by rw [uIcc_of_le zero_le_one]; exact Icc_subset_Icc (by norm_num) le_rfl)
    ).intervalIntegrable

theorem intervalIntegrable_crossedD_unit : IntervalIntegrable crossedD volume 0 1 :=
  (continuousOn_crossedD.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable

/-- `K_C` is integrable on `[0, 1]`. -/
theorem intervalIntegrable_cornerKernel : IntervalIntegrable cornerKernel volume 0 1 := by
  have i1 := intervalIntegrable_mul_unit intervalIntegrable_Li₂_unit
    (g := fun Y => Y - 1 / 2) (by fun_prop)
  have i2 := intervalIntegrable_mul_unit intervalIntegrable_crossedD_unit
    (g := fun Y => 2 * Y / 3 - 1 / 3) (by fun_prop)
  have i3 := intervalIntegrable_mul_unit intervalIntegrable_and_integral_log_sq_div_sub_one.1
    (g := fun Y => (Y / 6 - 1 / 12) * (Y - 1) - 1 / 12) (by fun_prop)
  have i4 := intervalIntegrable_mul_unit
    intervalIntegrable_and_integral_log_mul_log_one_sub_div.1
    (g := fun Y => (Y / 3 - 1 / 6) * Y - 1 / 6) (by fun_prop)
  have i5 := intervalIntegrable_mul_unit intervalIntegrable_and_integral_log_div_sub_one.1
    (g := fun Y => (Y / 6 - 1 / 4) * (Y - 1) - 5 / 12) (by fun_prop)
  have i6 := intervalIntegrable_mul_unit intervalIntegrable_and_integral_log_one_sub_div.1
    (g := fun Y => (-2 * Y / 3 + 4 / 3) * Y - 5 / 6) (by fun_prop)
  have i7 : IntervalIntegrable
      (fun Y : ℝ => π ^ 2 / 6 * (-2 * Y / 3 + 1 / 3) + (31 * Y / 24 - 7 / 6)) volume 0 1 :=
    (by fun_prop : Continuous fun Y : ℝ =>
      π ^ 2 / 6 * (-2 * Y / 3 + 1 / 3) + (31 * Y / 24 - 7 / 6)).intervalIntegrable 0 1
  have i8 := intervalIntegrable_and_integral_Li₂_sub_div_sub_one.1.const_mul (1 / 3)
  have i9 := intervalIntegrable_and_integral_crossedD_add_div_sub_one.1.const_mul (1 / 6)
  have i10 := intervalIntegrable_and_integral_Li₂_div.1.const_mul (1 / 6)
  have i11 := intervalIntegrable_and_integral_crossedD_sub_div.1.const_mul (1 / 6)
  have i12 := intervalIntegrable_and_integral_Li₂_add_log_one_sub_div_sq.1.const_mul (1 / 2)
  have i13 := intervalIntegrable_and_integral_log_one_sub_add_div_sq.1.const_mul (1 / 3)
  have i14 := intervalIntegrable_log_mul_log_one_sub_add_div_sq.const_mul (1 / 2)
  have hsum := ((((((((((((i1.add i2).add i3).add i4).add i5).add i6).add i7).sub i8).sub i9).sub
    i10).sub i11).add i12).sub i13).add i14
  refine hsum.congr_uIoo fun Y hY => ?_
  rw [uIoo_of_le zero_le_one] at hY
  exact (cornerKernel_eq_decomp hY).symm

/-! ### The master combination -/

theorem unitIntegral_add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = a)
    (hg : IntervalIntegrable g volume 0 1 ∧ ∫ x in (0 : ℝ)..1, g x = b) :
    IntervalIntegrable (fun x => f x + g x) volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x + g x = a + b :=
  ⟨hf.1.add hg.1, by rw [intervalIntegral.integral_add hf.1 hg.1, hf.2, hg.2]⟩

theorem unitIntegral_sub {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = a)
    (hg : IntervalIntegrable g volume 0 1 ∧ ∫ x in (0 : ℝ)..1, g x = b) :
    IntervalIntegrable (fun x => f x - g x) volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x - g x = a - b :=
  ⟨hf.1.sub hg.1, by rw [intervalIntegral.integral_sub hf.1 hg.1, hf.2, hg.2]⟩

/-- `∫₀¹ K_m`, from the eight masters of `QED.TwoLoop.UnitX`. -/
theorem intervalIntegrable_and_integral_cornerMasterKernel :
    IntervalIntegrable cornerMasterKernel volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, cornerMasterKernel Y =
        -(1 / 6) * (zeta3 + zeta3 + (-(π ^ 2 / 2) * log 2 - 7 / 4 * zeta3) + 2 * (2 * zeta3) +
            (-(π ^ 2 / 2) * log 2 - 7 / 4 * zeta3)) -
          1 / 12 * (-2 * zeta3 - π ^ 2 / 6) - 5 / 6 * (-(π ^ 2 / 6)) - 1 / 6 * (π ^ 2 / 4) := by
  have m1 := intervalIntegrable_and_integral_Li₂_div
  have m2 := intervalIntegrable_and_integral_log_mul_log_one_sub_div
  have m3 := intervalIntegrable_and_integral_crossedD_sub_div
  have m4 := unitIntegral_const_mul intervalIntegrable_and_integral_Li₂_sub_div_sub_one 2
  have m3' := intervalIntegrable_and_integral_crossedD_add_div_sub_one
  have m56 := unitIntegral_const_mul
    (unitIntegral_sub intervalIntegrable_and_integral_log_sq_div_sub_one
      intervalIntegrable_and_integral_log_div_sub_one) (1 / 12)
  have m7 := unitIntegral_const_mul intervalIntegrable_and_integral_log_one_sub_div (5 / 6)
  have m8 := unitIntegral_const_mul intervalIntegrable_and_integral_log_sub_log_div (1 / 6)
  exact unitIntegral_congr (unitIntegral_sub (unitIntegral_sub (unitIntegral_sub
    (unitIntegral_const_mul (unitIntegral_add (unitIntegral_add (unitIntegral_add
      (unitIntegral_add m1 m2) m3) m4) m3') (-(1 / 6))) m56) m7) m8) (fun Y _ => rfl) rfl

/-! ### The boundary function: derivative -/

/-- The derivative of `a y² + b y + c + d/y`. -/
theorem hasDerivAt_quadInv (a b c d : ℝ) {Y : ℝ} (hY : Y ≠ 0) :
    HasDerivAt (fun y => a * y ^ 2 + b * y + c + d / y) (2 * a * Y + b - d / Y ^ 2) Y := by
  have h := ((((hasDerivAt_pow 2 Y).const_mul a).add ((hasDerivAt_id' Y).const_mul b)).add_const
    c).add ((hasDerivAt_inv hY).const_mul d)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · push_cast
    field_simp
    ring
  · filter_upwards with y
    simp [div_eq_mul_inv]

theorem cornerBoundary_eq_quad (Y : ℝ) :
    cornerBoundary Y =
      (1 / 2 * Y ^ 2 + -(1 / 2) * Y + 0 + -(1 / 2) / Y) * Li₂ Y +
        (1 / 3 * Y ^ 2 + -(1 / 3) * Y + 0 + 0 / Y) * crossedD Y +
        (1 / 12 * Y ^ 2 + -(1 / 12) * Y + 0 + 0 / Y) * log Y ^ 2 +
        (1 / 6 * Y ^ 2 + -(1 / 6) * Y + 0 + -(1 / 2) / Y) * (log Y * log (1 - Y)) +
        (1 / 12 * Y ^ 2 + -(1 / 4) * Y + -(1 / 2) + 0 / Y) * log Y +
        (-(1 / 3) * Y ^ 2 + 7 / 6 * Y + -(2 / 3) + -(1 / 6) / Y) * log (1 - Y) +
        ((37 / 48 - π ^ 2 / 18) * Y ^ 2 + (π ^ 2 / 18 - 7 / 4) * Y + 0 + 0 / Y) := by
  unfold cornerBoundary
  ring

/-- **`G_C' = K_C - K_m`** on `(0, 1) \ {1/2}` (eq. (6.11)). -/
theorem hasDerivAt_cornerBoundary {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hh : Y ≠ 1 / 2) :
    HasDerivAt cornerBoundary (cornerKernel Y - cornerMasterKernel Y) Y := by
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hY1' : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
  have hY2 : (1 : ℝ) - 2 * Y ≠ 0 := fun h => hh (by linarith)
  have hY2' : (2 : ℝ) * Y - 1 ≠ 0 := fun h => hh (by linarith)
  have hL := hasDerivAt_Li₂' hY
  have hD := hasDerivAt_crossedD hY hh
  have ha := hasDerivAt_log hY0
  have hb := hasDerivAt_log_one_sub hY.2
  have q := fun a b c d => hasDerivAt_quadInv a b c d hY0
  have h := (((((((q (1 / 2) (-(1 / 2)) 0 (-(1 / 2))).mul hL).add
    ((q (1 / 3) (-(1 / 3)) 0 0).mul hD)).add ((q (1 / 12) (-(1 / 12)) 0 0).mul (ha.pow 2))).add
    ((q (1 / 6) (-(1 / 6)) 0 (-(1 / 2))).mul (ha.mul hb))).add
    ((q (1 / 12) (-(1 / 4)) (-(1 / 2)) 0).mul ha)).add
    ((q (-(1 / 3)) (7 / 6) (-(2 / 3)) (-(1 / 6))).mul hb)).add
    (q (37 / 48 - π ^ 2 / 18) (π ^ 2 / 18 - 7 / 4) 0 0)
  have hfun : cornerBoundary = fun y =>
      (1 / 2 * y ^ 2 + -(1 / 2) * y + 0 + -(1 / 2) / y) * Li₂ y +
        (1 / 3 * y ^ 2 + -(1 / 3) * y + 0 + 0 / y) * crossedD y +
        (1 / 12 * y ^ 2 + -(1 / 12) * y + 0 + 0 / y) * log y ^ 2 +
        (1 / 6 * y ^ 2 + -(1 / 6) * y + 0 + -(1 / 2) / y) * (log y * log (1 - y)) +
        (1 / 12 * y ^ 2 + -(1 / 4) * y + -(1 / 2) + 0 / y) * log y +
        (-(1 / 3) * y ^ 2 + 7 / 6 * y + -(2 / 3) + -(1 / 6) / y) * log (1 - y) +
        ((37 / 48 - π ^ 2 / 18) * y ^ 2 + (π ^ 2 / 18 - 7 / 4) * y + 0 + 0 / y) :=
    funext cornerBoundary_eq_quad
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold cornerKernel cornerMasterKernel
  field_simp
  ring

/-! ### The boundary function: endpoint values -/

theorem tendsto_crossedD_zero : Tendsto crossedD (𝓝[>] 0) (𝓝 (π ^ 2 / 4)) := by
  rw [← crossedD_zero]
  exact (continuousOn_crossedD 0 (by norm_num)).tendsto.mono_left (nhdsWithin_le_of_mem
    (mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) Ioo_subset_Icc_self))

theorem tendsto_crossedD_one : Tendsto crossedD (𝓝[<] 1) (𝓝 (-(π ^ 2 / 4))) := by
  rw [← crossedD_one]
  exact (continuousOn_crossedD 1 (by norm_num)).tendsto.mono_left (nhdsWithin_le_of_mem
    (mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) Ioo_subset_Icc_self))

/-- A continuous function tends to its value along `𝓝[>] p` and `𝓝[<] p`. -/
theorem tendsto_nhdsWithin_of_continuous {g : ℝ → ℝ} (hg : Continuous g) (p : ℝ) (S : Set ℝ) :
    Tendsto g (𝓝[S] p) (𝓝 (g p)) :=
  (hg.tendsto p).mono_left nhdsWithin_le_nhds

/-- **`G_C(0⁺) = -1/3`.** -/
theorem tendsto_cornerBoundary_zero : Tendsto cornerBoundary (𝓝[>] 0) (𝓝 (-(1 / 3))) := by
  have c := fun g (hg : Continuous g) => tendsto_nhdsWithin_of_continuous hg 0 (Ioi 0)
  have h := ((((((((((c (fun Y : ℝ => Y ^ 2 / 2 - Y / 2) (by fun_prop)).mul
    tendsto_Li₂_zero_right).sub (tendsto_Li₂_div_zero.const_mul (1 / 2))).add
    ((c (fun Y : ℝ => (Y ^ 2 - Y) / 3) (by fun_prop)).mul tendsto_crossedD_zero)).add
    ((c (fun Y : ℝ => (Y - 1) / 12) (by fun_prop)).mul tendsto_mul_log_sq_zero)).add
    ((c (fun Y : ℝ => Y ^ 2 / 6 - Y / 6) (by fun_prop)).mul tendsto_log_mul_log_one_sub_zero)).sub
    (tendsto_log_mul_log_one_sub_add_div_zero.const_mul (1 / 2))).add
    ((c (fun Y : ℝ => Y / 12 - 1 / 4) (by fun_prop)).mul tendsto_mul_log_zero)).add
    ((c (fun Y : ℝ => -Y ^ 2 / 3 + 7 * Y / 6 - 2 / 3) (by fun_prop)).mul
      tendsto_log_one_sub_zero)).sub (tendsto_log_one_sub_div_zero'.const_mul (1 / 6))).add
    (c (fun Y : ℝ => -(π ^ 2 / 6 * (Y ^ 2 - Y) / 3) + 37 * Y ^ 2 / 48 - 7 * Y / 4) (by fun_prop))
  refine (h.congr' ?_).trans ?_
  · filter_upwards [self_mem_nhdsWithin] with Y (hY : 0 < Y)
    have h0 : Y ≠ 0 := hY.ne'
    unfold cornerBoundary
    field_simp
    ring
  · norm_num

/-- **`G_C(1⁻) = -47/48 - ζ(2)/2`.** -/
theorem tendsto_cornerBoundary_one :
    Tendsto cornerBoundary (𝓝[<] 1) (𝓝 (-(47 / 48) - π ^ 2 / 12)) := by
  have c : ∀ g : ℝ → ℝ, ContinuousAt g 1 → Tendsto g (𝓝[<] 1) (𝓝 (g 1)) :=
    fun g hg => hg.tendsto.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto log (𝓝[<] 1) (𝓝 0) := by
    simpa using c log (continuousAt_log one_ne_zero)
  have hml : Tendsto (fun Y : ℝ => (1 - Y) * log (1 - Y)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have t1 := (c (fun Y : ℝ => Y ^ 2 / 2 - Y / 2 - 1 / (2 * Y))
    (by fun_prop (disch := norm_num))).mul tendsto_Li₂_one_left
  have t2 := (c (fun Y : ℝ => (Y ^ 2 - Y) / 3) (by fun_prop)).mul tendsto_crossedD_one
  have t3 := (c (fun Y : ℝ => (Y ^ 2 - Y) / 12) (by fun_prop)).mul (hlog.pow 2)
  have t4 := (c (fun Y : ℝ => Y ^ 2 / 6 - Y / 6 - 1 / (2 * Y))
    (by fun_prop (disch := norm_num))).mul tendsto_log_mul_log_one_sub_one
  have t5 := (c (fun Y : ℝ => Y ^ 2 / 12 - Y / 4 - 1 / 2) (by fun_prop)).mul hlog
  have t6 := (c (fun Y : ℝ => (2 * Y ^ 2 - 5 * Y - 1) / (6 * Y))
    (by fun_prop (disch := norm_num))).mul hml
  have h := ((((t1.add t2).add t3).add t4).add t5).add t6
  have h' := h.add (c (fun Y : ℝ => -(π ^ 2 / 6 * (Y ^ 2 - Y) / 3) + 37 * Y ^ 2 / 48 - 7 * Y / 4)
    (by fun_prop))
  refine (h'.congr' ?_).trans ?_
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with Y hY
    have h0 : Y ≠ 0 := hY.1.ne'
    unfold cornerBoundary
    field_simp
    ring
  · norm_num
    ring

theorem continuousAt_cornerBoundary_half : ContinuousAt cornerBoundary (1 / 2) := by
  have hL : ContinuousAt Li₂ (1 / 2) :=
    continuousOn_Li₂.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have hD : ContinuousAt crossedD (1 / 2) :=
    continuousOn_crossedD.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have ha : ContinuousAt log (1 / 2) := continuousAt_log (by norm_num)
  have hb : ContinuousAt (fun Y : ℝ => log (1 - Y)) (1 / 2) :=
    (continuousAt_log (by norm_num)).comp (by fun_prop)
  unfold cornerBoundary
  fun_prop (disch := norm_num)

/-! ### The value -/

/-- **`∫₀¹ K_C = -31/48 + ζ(2)/6 + ζ(2) log 2 - ζ(3)/4`**, with integrability. -/
theorem intervalIntegrable_and_integral_cornerKernel :
    IntervalIntegrable cornerKernel volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, cornerKernel Y =
        -(31 / 48) + π ^ 2 / 36 + π ^ 2 / 6 * log 2 - zeta3 / 4 := by
  have hKm := intervalIntegrable_and_integral_cornerMasterKernel
  have hdiff : IntervalIntegrable (fun Y => cornerKernel Y - cornerMasterKernel Y) volume 0 1 :=
    intervalIntegrable_cornerKernel.sub hKm.1
  have hsub : ∀ c d : ℝ, c ∈ Icc (0 : ℝ) 1 → d ∈ Icc (0 : ℝ) 1 →
      IntervalIntegrable (fun Y => cornerKernel Y - cornerMasterKernel Y) volume c d :=
    fun c d hc hd => hdiff.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le zero_le_one])
      (by rwa [uIcc_of_le zero_le_one]))
  have hhalf := continuousAt_cornerBoundary_half
  have e₁ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun Y hY => hasDerivAt_cornerBoundary ⟨hY.1, by linarith [hY.2]⟩ hY.2.ne)
    (hsub 0 (1 / 2) (by norm_num) (by norm_num)) tendsto_cornerBoundary_zero
    (hhalf.tendsto.mono_left nhdsWithin_le_nhds)
  have e₂ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (1 / 2 : ℝ) < 1)
    (fun Y hY => hasDerivAt_cornerBoundary ⟨by linarith [hY.1], hY.2⟩ hY.1.ne')
    (hsub (1 / 2) 1 (by norm_num) (by norm_num)) (hhalf.tendsto.mono_left nhdsWithin_le_nhds)
    tendsto_cornerBoundary_one
  have hD : IntervalIntegrable (fun Y => cornerKernel Y - cornerMasterKernel Y) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, cornerKernel Y - cornerMasterKernel Y =
        -(47 / 48) - π ^ 2 / 12 - -(1 / 3) := by
    refine ⟨hdiff, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hsub 0 (1 / 2) (by norm_num)
      (by norm_num)) (hsub (1 / 2) 1 (by norm_num) (by norm_num)), e₁, e₂]
    ring
  exact unitIntegral_congr (unitIntegral_add hD hKm) (fun Y _ => by ring) (by ring)

/-- **The finite part of the corner unit.** `b_C = 2 ∫₀¹ K_C - 3/2 = -67/24 + 2 ζ(2) log 2 +
ζ(2)/3 - ζ(3)/2`, BMR-I p. 852 row c) (eq. (6.5) of the document). -/
theorem cornerUnit_finitePart_value :
    2 * (∫ Y in (0 : ℝ)..1, cornerKernel Y) - 3 / 2 =
      -(67 / 24) + 2 * (π ^ 2 / 6) * log 2 + π ^ 2 / 6 / 3 - zeta3 / 2 := by
  rw [intervalIntegrable_and_integral_cornerKernel.2]
  ring

/-- **S + C.** `b_S + b_C = 2 ∫₀¹ K_S + (2 ∫₀¹ K_C - 3/2) = -7/3 + 2 ζ(2) log 2 - ζ(3)/2`,
BMR-I's value of the infrared-finite grouping S + C (eq. (7.1) of the document). -/
theorem selfEnergyCornerUnit_value :
    2 * (∫ Y in (0 : ℝ)..1, selfEnergyKernel Y) +
        (2 * (∫ Y in (0 : ℝ)..1, cornerKernel Y) - 3 / 2) =
      -(7 / 3) + 2 * (π ^ 2 / 6) * log 2 - zeta3 / 2 := by
  rw [cornerUnit_finitePart_value, integral_selfEnergyKernel]
  ring

/-! ### The assembly from the masters -/

/-- **Arithmetic of the assembly (6.13).** With the boundary values `G_C(1⁻) = -47/48 - ζ(2)/2`
and `G_C(0⁺) = -1/3`, the combination of the master integrals in (6.13), doubled and shifted by
`-3/2`, is BMR's finite part of C, `-67/24 + 2 ζ(2) log 2 + ζ(2)/3 - ζ(3)/2`. -/
theorem cornerUnit_assembly :
    2 * ((-(47 / 48) - π ^ 2 / 12) - -(1 / 3) +
        -(1 / 6) * ((∫ Y in (0 : ℝ)..1, Li₂ Y / Y) + (∫ Y in (0 : ℝ)..1, log Y * log (1 - Y) / Y) +
          (∫ Y in (0 : ℝ)..1, (crossedD Y - π ^ 2 / 4) / Y) +
          2 * (∫ Y in (0 : ℝ)..1, (Li₂ Y - π ^ 2 / 6) / (Y - 1)) +
          (∫ Y in (0 : ℝ)..1, (crossedD Y + π ^ 2 / 4) / (Y - 1))) -
        1 / 12 * ((∫ Y in (0 : ℝ)..1, log Y ^ 2 / (Y - 1)) - (∫ Y in (0 : ℝ)..1, log Y / (Y - 1))) -
        5 / 6 * (∫ Y in (0 : ℝ)..1, log (1 - Y) / Y) -
        1 / 6 * (∫ Y in (0 : ℝ)..1, (log Y - log (1 - Y)) / (2 * Y - 1))) - 3 / 2 =
      -(67 / 24) + 2 * (π ^ 2 / 6) * log 2 + π ^ 2 / 6 / 3 - zeta3 / 2 := by
  rw [integral_Li₂_div, integral_log_mul_log_one_sub_div,
    intervalIntegrable_and_integral_crossedD_sub_div.2,
    intervalIntegrable_and_integral_Li₂_sub_div_sub_one.2,
    intervalIntegrable_and_integral_crossedD_add_div_sub_one.2,
    intervalIntegrable_and_integral_log_sq_div_sub_one.2,
    intervalIntegrable_and_integral_log_div_sub_one.2,
    intervalIntegrable_and_integral_log_one_sub_div.2,
    intervalIntegrable_and_integral_log_sub_log_div.2]
  ring

end QED.TwoLoop.Units
