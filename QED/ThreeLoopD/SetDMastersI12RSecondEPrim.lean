/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondEx
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus
import QED.Polylog.Reflection

/-!
# Set (d), master `I₁₂`: an antiderivative of the `x`-integrand of `E(c)`

For `c = y (1 - y)` with `0 < y < 1`, write `P = (1 - y)x + y`, `Q = yx + 1 - y` (so
`PQ = c(1 - x)² + x`) and `z = c(1 - x)²/(PQ)`. The integrand `QED.ThreeLoopD.i12REx c x` is

  `(1/c)(-(3/2) ℓ² + (9/2) ℓ + (3N(N + 4x)/(2x²)) log z - 3 Li₂ z) + 3(1 - x)²/(2x)`,

`ℓ = log x - log P - log Q = log (1 - z)`, `N = c(1 - x)²` (`QED.ThreeLoopD.i12REx_eq_letters`),
and `QED.ThreeLoopD.i12REF y c` is an antiderivative on `(0, 1)` in the letters `x`, `1 - x`, `P`,
`Q`, whose dilogarithms all have arguments in `(0, 1)`. Its limits at `0⁺` and `1⁻` contain
`Li₂ y + Li₂ (1 - y)` only, and Euler's reflection formula then gives the closed form of
`E(c) = ∫₀¹ i12REx c x dx` (the integrand is `≤ 0`, so it is integrable).

## Main results

* `QED.ThreeLoopD.i12REx_eq_letters`, `QED.ThreeLoopD.hasDerivAt_i12REF`.
* `QED.ThreeLoopD.tendsto_i12REF_zero`, `QED.ThreeLoopD.tendsto_i12REF_one`.
* `QED.ThreeLoopD.integral_i12REx_eq`: `∫₀¹ i12REx (y (1 - y)) x dx = E_cl(y)` for `0 < y < 1`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- An antiderivative in `x` of `i12REx c x`, `c = y (1 - y)`. -/
noncomputable def i12REF (y c x : ℝ) : ℝ :=
  -(3 * x / (2 * c)) * (log x - log ((1 - y) * x + y) - log (y * x + 1 - y)) ^ 2 -
    3 * (1 - c) * (log ((1 - y) * x + y) ^ 2 + log (y * x + 1 - y) ^ 2) +
    6 * (1 - c) * (log ((1 - y) * x + y) * log y + log (y * x + 1 - y) * log (1 - y)) +
    6 * (c - 1) * (Li₂ ((1 - y) * x / ((1 - y) * x + y)) + Li₂ (y * x / (y * x + 1 - y))) -
    6 / c * (Li₂ ((1 - y) * (1 - x)) + Li₂ (y * (1 - x))) +
    6 * (2 * c ^ 2 - 2 * c - 1) / c * Li₂ x -
    3 * x / c * Li₂ (c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y))) -
    6 / c * (log x * log (1 - x)) + 3 * x / (2 * c) * log x -
    3 * c / (2 * x) * (log y + log (1 - y) + 2 * log (1 - x) - log ((1 - y) * x + y) -
      log (y * x + 1 - y)) +
    (c * x ^ 3 + (6 - 6 * c) * x ^ 2 + (18 * c - 24) * x + (18 - 10 * c)) * log (1 - x) +
    (c / 2 * x ^ 3 + (3 - 3 * c) * x ^ 2 + (9 * c - 12) * x + 0) * (log y + log (1 - y)) +
    (-(c / 2) * x ^ 3 + -(3 * (1 - c)) * x ^ 2 + -(3 * (6 * c ^ 2 - 8 * c + 1) / (2 * c)) * x +
      0) * (log ((1 - y) * x + y) + log (y * x + 1 - y)) +
    -(y * (5 * y ^ 3 - 9 * y ^ 2 + 9 * y - 6) / (1 - y) ^ 2) * log ((1 - y) * x + y) +
    -((1 - y) * (5 * (1 - y) ^ 3 - 9 * (1 - y) ^ 2 + 9 * (1 - y) - 6) / y ^ 2) *
      log (y * x + 1 - y) +
    (0 * x ^ 3 + 1 / 2 * x ^ 2 + -((2 * c + 1) / c) * x + 0)

theorem i12R_PQ_pos {y x : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < (1 - y) * x + y ∧ 0 < y * x + 1 - y := by
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hx0, hx1⟩ := hx
  constructor
  · nlinarith
  · nlinarith

/-- **The letter form** of `i12REx (y (1 - y)) x`. -/
theorem i12REx_eq_letters {y x : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    i12REx (y * (1 - y)) x =
      (-(3 / 2) * (log x - log ((1 - y) * x + y) - log (y * x + 1 - y)) ^ 2 +
        9 / 2 * (log x - log ((1 - y) * x + y) - log (y * x + 1 - y)) +
        3 * (y * (1 - y) * (1 - x) ^ 2) * (y * (1 - y) * (1 - x) ^ 2 + 4 * x) / (2 * x ^ 2) *
          (log y + log (1 - y) + 2 * log (1 - x) - log ((1 - y) * x + y) -
            log (y * x + 1 - y)) -
        3 * Li₂ (y * (1 - y) * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y)))) /
        (y * (1 - y)) + 3 * (1 - x) ^ 2 / (2 * x) := by
  obtain ⟨hP, hQ⟩ := i12R_PQ_pos hy hx
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hx0, hx1⟩ := hx
  have h1y : 0 < 1 - y := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hc : 0 < y * (1 - y) := mul_pos hy0 h1y
  have hwc : 0 < (1 - x) * (y * (1 - y)) := mul_pos h1x hc
  set k := x / ((1 - x) * (y * (1 - y))) with hk
  have hk0 : 0 < k := div_pos hx0 hwc
  have hwk' : 1 - x + k = ((1 - y) * x + y) * (y * x + 1 - y) / ((1 - x) * (y * (1 - y))) := by
    rw [hk]
    field_simp
    ring
  have hlk : log k = log x - (log (1 - x) + (log y + log (1 - y))) := by
    rw [hk, Real.log_div hx0.ne' hwc.ne', Real.log_mul h1x.ne' hc.ne',
      Real.log_mul hy0.ne' h1y.ne']
  have hlwk : log (1 - x + k) = log ((1 - y) * x + y) + log (y * x + 1 - y) -
      (log (1 - x) + (log y + log (1 - y))) := by
    rw [hwk', Real.log_div (mul_pos hP hQ).ne' hwc.ne', Real.log_mul hP.ne' hQ.ne',
      Real.log_mul h1x.ne' hc.ne', Real.log_mul hy0.ne' h1y.ne']
  have hz : (1 - x) / (1 - x + k) =
      y * (1 - y) * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y)) := by
    rw [hwk']
    field_simp
  simp only [i12REx, i12RA, i12RA0]
  rw [hlk, hlwk, hz]
  generalize Li₂ (y * (1 - y) * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y))) = L
  generalize log ((1 - y) * x + y) = lP
  generalize log (y * x + 1 - y) = lQ
  generalize log x = lx
  generalize log (1 - x) = lw
  generalize log y = ly
  generalize log (1 - y) = lv
  have := hx0.ne'
  have := h1x.ne'
  have := hy0.ne'
  have := h1y.ne'
  field_simp
  ring

/-- **The derivative of `i12REF`**: `∂ₓ i12REF y (y (1 - y)) x = i12REx (y (1 - y)) x`. -/
theorem hasDerivAt_i12REF {y x : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12REF y (y * (1 - y))) (i12REx (y * (1 - y)) x) x := by
  rw [i12REx_eq_letters hy hx]
  obtain ⟨hP, hQ⟩ := i12R_PQ_pos hy hx
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hx0, hx1⟩ := hx
  have h1y : 0 < 1 - y := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hc : 0 < y * (1 - y) := mul_pos hy0 h1y
  set c := y * (1 - y) with hcdef
  have hPQ : ((1 - y) * x + y) * (y * x + 1 - y) = c * (1 - x) ^ 2 + x := by
    rw [hcdef]; ring
  have hi := hasDerivAt_id' x
  have hcub : ∀ a b d e : ℝ, HasDerivAt (fun x => a * x ^ 3 + b * x ^ 2 + d * x + e)
      (3 * a * x ^ 2 + 2 * b * x + d) x := fun a b d e => by
    have := ((((hi.pow 3).const_mul a).add ((hi.pow 2).const_mul b)).add
      (hi.const_mul d)).add_const e
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have dP : HasDerivAt (fun x => (1 - y) * x + y) (1 - y) x := by
    simpa using (hi.const_mul (1 - y)).add_const y
  have dQ : HasDerivAt (fun x => y * x + 1 - y) y x := by
    simpa using ((hi.const_mul y).add_const 1).sub_const y
  have dw : HasDerivAt (fun x => 1 - x) (-1) x := by simpa using hi.const_sub 1
  have lx := Real.hasDerivAt_log hx0.ne'
  have lw := dw.log h1x.ne'
  have lP := dP.log hP.ne'
  have lQ := dQ.log hQ.ne'
  -- the dilogarithms
  have m2 : (1 - y) * x / ((1 - y) * x + y) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (mul_pos h1y hx0) hP, (div_lt_one hP).2 (by linarith)⟩
  have m3 : y * x / (y * x + 1 - y) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (mul_pos hy0 hx0) hQ, (div_lt_one hQ).2 (by linarith)⟩
  have m4 : (1 - y) * (1 - x) ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos h1y h1x, by nlinarith⟩
  have m5 : y * (1 - x) ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hy0 h1x, by nlinarith⟩
  have mz : c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (mul_pos hc (pow_pos h1x 2)) (mul_pos hP hQ),
      (div_lt_one (mul_pos hP hQ)).2 (by rw [hPQ]; linarith)⟩
  have L1 := hasDerivAt_Li₂' ⟨hx0, hx1⟩
  have L2 := (hasDerivAt_Li₂' m2).comp x ((hi.const_mul (1 - y)).div dP hP.ne')
  have L3 := (hasDerivAt_Li₂' m3).comp x ((hi.const_mul y).div dQ hQ.ne')
  have L4 := (hasDerivAt_Li₂' m4).comp x (dw.const_mul (1 - y))
  have L5 := (hasDerivAt_Li₂' m5).comp x (dw.const_mul y)
  have Lz := (hasDerivAt_Li₂' mz).comp x (((dw.pow 2).const_mul c).div (dP.mul dQ)
    (mul_pos hP hQ).ne')
  have T10 : HasDerivAt (fun x => 3 * c / (2 * x)) (-(3 * c * 2) / (2 * x) ^ 2) x := by
    have := (hasDerivAt_const x (3 * c)).div (hi.const_mul 2) (by positivity)
    refine this.congr_deriv ?_
    ring
  have hA := ((((((((hi.const_mul 3).div_const (2 * c)).neg.mul
    (((lx.sub lP).sub lQ).pow 2)).sub (((lP.pow 2).add (lQ.pow 2)).const_mul (3 * (1 - c)))).add
    (((lP.mul_const (log y)).add (lQ.mul_const (log (1 - y)))).const_mul (6 * (1 - c)))).add
    ((L2.add L3).const_mul (6 * (c - 1)))).sub ((L4.add L5).const_mul (6 / c))).add
    (L1.const_mul (6 * (2 * c ^ 2 - 2 * c - 1) / c))).sub
    (((hi.const_mul 3).div_const c).mul Lz)
  have hB := ((hA.sub ((lx.mul lw).const_mul (6 / c))).add
    (((hi.const_mul 3).div_const (2 * c)).mul lx)).sub
    (T10.mul ((((lw.const_mul 2).const_add (log y + log (1 - y))).sub lP).sub lQ))
  have hC := ((hB.add ((hcub c (6 - 6 * c) (18 * c - 24) (18 - 10 * c)).mul lw)).add
    ((hcub (c / 2) (3 - 3 * c) (9 * c - 12) 0).mul_const (log y + log (1 - y)))).add
    ((hcub (-(c / 2)) (-(3 * (1 - c))) (-(3 * (6 * c ^ 2 - 8 * c + 1) / (2 * c))) 0).mul
      (lP.add lQ))
  have h := ((hC.add (lP.const_mul (-(y * (5 * y ^ 3 - 9 * y ^ 2 + 9 * y - 6) / (1 - y) ^ 2)))).add
    (lQ.const_mul (-((1 - y) * (5 * (1 - y) ^ 3 - 9 * (1 - y) ^ 2 + 9 * (1 - y) - 6) /
      y ^ 2)))).add (hcub 0 (1 / 2) (-((2 * c + 1) / c)) 0)
  convert h using 1
  · funext t
    simp only [i12REF, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.neg_apply, Pi.pow_apply, Pi.div_apply]
  have e2 : 1 - (1 - y) * x / ((1 - y) * x + y) = y / ((1 - y) * x + y) := by
    field_simp; ring
  have e3 : 1 - y * x / (y * x + 1 - y) = (1 - y) / (y * x + 1 - y) := by
    field_simp; ring
  have e4 : 1 - (1 - y) * (1 - x) = (1 - y) * x + y := by ring
  have e5 : 1 - y * (1 - x) = y * x + 1 - y := by ring
  have ez : 1 - c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y)) =
      x / ((1 - y) * x + y) / (y * x + 1 - y) := by
    rw [div_div, eq_div_iff (mul_pos hP hQ).ne', sub_mul, div_mul_cancel₀ _ (mul_pos hP hQ).ne',
      hPQ]
    ring
  simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
    Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one, e2, e3, e4, e5, ez]
  rw [Real.log_div hy0.ne' hP.ne', Real.log_div h1y.ne' hQ.ne',
    Real.log_div (div_pos hx0 hP).ne' hQ.ne', Real.log_div hx0.ne' hP.ne']
  generalize Li₂ (c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y))) = L
  generalize log ((1 - y) * x + y) = a
  generalize log (y * x + 1 - y) = b
  generalize log x = u
  generalize log (1 - x) = v
  generalize log y = ly
  generalize log (1 - y) = lv
  clear_value c
  clear hA hB hC h L1 L2 L3 L4 L5 Lz T10 lx lw lP lQ dP dQ dw hcub hi m2 m3 m4 m5 mz e2 e3 e4 e5 ez
  have hP' := hP.ne'
  have hQ' := hQ.ne'
  have hc' := hc.ne'
  have hx' := hx0.ne'
  have hy' := hy0.ne'
  have hw' := h1x.ne'
  have ht' := h1y.ne'
  generalize hp : (1 - y) * x + y = p at *
  generalize hq : y * x + 1 - y = q at *
  generalize hw : 1 - x = w at *
  generalize ht : 1 - y = t at *
  field_simp
  subst hp hq hw ht hcdef
  ring

theorem i12R_continuousAt_Li₂ {t : ℝ} (ht : |t| < 1) : ContinuousAt Li₂ t :=
  (hasDerivAt_Li₂_tsum ht).continuousAt

/-- **The limit at `0⁺`**. -/
theorem tendsto_i12REF_zero {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i12REF y (y * (1 - y))) (𝓝[>] 0) (𝓝 (-(6 / (y * (1 - y))) * (Li₂ y + Li₂ (1 - y)) +
      3 * (1 - y * (1 - y)) * (log y ^ 2 + log (1 - y) ^ 2) -
      y * (5 * y ^ 3 - 9 * y ^ 2 + 9 * y - 6) / (1 - y) ^ 2 * log y -
      (1 - y) * (5 * (1 - y) ^ 3 - 9 * (1 - y) ^ 2 + 9 * (1 - y) - 6) / y ^ 2 * log (1 - y) +
      3 / 2)) := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1y : 0 < 1 - y := by linarith
  have hc : 0 < y * (1 - y) := mul_pos hy0 h1y
  set c := y * (1 - y) with hcdef
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  -- the continuous part
  have hlP : ContinuousAt (fun x : ℝ => log ((1 - y) * x + y)) 0 :=
    ((by fun_prop : Continuous fun x : ℝ => (1 - y) * x + y).continuousAt).log
      (by simpa using hy0.ne')
  have hlQ : ContinuousAt (fun x : ℝ => log (y * x + 1 - y)) 0 :=
    ((by fun_prop : Continuous fun x : ℝ => y * x + 1 - y).continuousAt).log
      (by simpa using h1y.ne')
  have hlw : ContinuousAt (fun x : ℝ => log (1 - x)) 0 :=
    ((by fun_prop : Continuous fun x : ℝ => 1 - x).continuousAt).log (by norm_num)
  have hL1 : ContinuousAt Li₂ 0 := i12R_continuousAt_Li₂ (by norm_num)
  have hL2 : ContinuousAt (fun x : ℝ => Li₂ ((1 - y) * x / ((1 - y) * x + y))) 0 :=
    ContinuousAt.comp (f := fun x : ℝ => (1 - y) * x / ((1 - y) * x + y))
      (i12R_continuousAt_Li₂ (by simp))
      (((by fun_prop : Continuous fun x : ℝ => (1 - y) * x).continuousAt).div
        ((by fun_prop : Continuous fun x : ℝ => (1 - y) * x + y).continuousAt)
        (by simpa using hy0.ne'))
  have hL3 : ContinuousAt (fun x : ℝ => Li₂ (y * x / (y * x + 1 - y))) 0 :=
    ContinuousAt.comp (f := fun x : ℝ => y * x / (y * x + 1 - y))
      (i12R_continuousAt_Li₂ (by simp))
      (((by fun_prop : Continuous fun x : ℝ => y * x).continuousAt).div
        ((by fun_prop : Continuous fun x : ℝ => y * x + 1 - y).continuousAt)
        (by simpa using h1y.ne'))
  have hL4 : ContinuousAt (fun x : ℝ => Li₂ ((1 - y) * (1 - x))) 0 :=
    ContinuousAt.comp (f := fun x : ℝ => (1 - y) * (1 - x))
      (i12R_continuousAt_Li₂ (by rw [sub_zero, mul_one, abs_of_pos h1y]; linarith))
      (by fun_prop)
  have hL5 : ContinuousAt (fun x : ℝ => Li₂ (y * (1 - x))) 0 :=
    ContinuousAt.comp (f := fun x : ℝ => y * (1 - x))
      (i12R_continuousAt_Li₂ (by rw [sub_zero, mul_one, abs_of_pos hy0]; linarith))
      (by fun_prop)
  have hm : ContinuousAt i12ml 0 := continuous_i12ml.continuousAt
  set H : ℝ → ℝ := fun x => 3 / c * i12ml x * (log ((1 - y) * x + y) + log (y * x + 1 - y)) -
    3 / (2 * c) * x * (log ((1 - y) * x + y) + log (y * x + 1 - y)) ^ 2 -
    3 * (1 - c) * (log ((1 - y) * x + y) ^ 2 + log (y * x + 1 - y) ^ 2) +
    6 * (1 - c) * (log ((1 - y) * x + y) * log y + log (y * x + 1 - y) * log (1 - y)) +
    6 * (c - 1) * (Li₂ ((1 - y) * x / ((1 - y) * x + y)) + Li₂ (y * x / (y * x + 1 - y))) -
    6 / c * (Li₂ ((1 - y) * (1 - x)) + Li₂ (y * (1 - x))) +
    6 * (2 * c ^ 2 - 2 * c - 1) / c * Li₂ x + 3 / (2 * c) * i12ml x +
    (c * x ^ 3 + (6 - 6 * c) * x ^ 2 + (18 * c - 24) * x + (18 - 10 * c)) * log (1 - x) +
    (c / 2 * x ^ 3 + (3 - 3 * c) * x ^ 2 + (9 * c - 12) * x + 0) * (log y + log (1 - y)) +
    (-(c / 2) * x ^ 3 + -(3 * (1 - c)) * x ^ 2 + -(3 * (6 * c ^ 2 - 8 * c + 1) / (2 * c)) * x +
      0) * (log ((1 - y) * x + y) + log (y * x + 1 - y)) +
    -(y * (5 * y ^ 3 - 9 * y ^ 2 + 9 * y - 6) / (1 - y) ^ 2) * log ((1 - y) * x + y) +
    -((1 - y) * (5 * (1 - y) ^ 3 - 9 * (1 - y) ^ 2 + 9 * (1 - y) - 6) / y ^ 2) *
      log (y * x + 1 - y) +
    (0 * x ^ 3 + 1 / 2 * x ^ 2 + -((2 * c + 1) / c) * x + 0) with hH
  have hHc : ContinuousAt H 0 := by
    rw [hH]
    fun_prop
  -- the singular part
  set φ : ℝ → ℝ := fun x => log y + log (1 - y) + 2 * log (1 - x) - log ((1 - y) * x + y) -
    log (y * x + 1 - y) with hφ
  have hφd : HasDerivAt φ (2 * (-1 / (1 - 0)) - (1 - y) / ((1 - y) * 0 + y) -
      y / (y * 0 + 1 - y)) 0 := by
    have hi := hasDerivAt_id' (0 : ℝ)
    have dP : HasDerivAt (fun x : ℝ => (1 - y) * x + y) (1 - y) 0 := by
      simpa using (hi.const_mul (1 - y)).add_const y
    have dQ : HasDerivAt (fun x : ℝ => y * x + 1 - y) y 0 := by
      simpa using ((hi.const_mul y).add_const 1).sub_const y
    have dw : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by simpa using hi.const_sub 1
    exact (((dw.log (by norm_num)).const_mul 2).const_add (log y + log (1 - y))).sub
      (dP.log (by simpa using hy0.ne'))|>.sub (dQ.log (by simpa using h1y.ne'))
  have hφ0 : φ 0 = 0 := by simp [hφ]
  have t3 : Tendsto (fun x => φ x / x) (𝓝[>] 0) (𝓝 (2 * (-1 / (1 - 0)) -
      (1 - y) / ((1 - y) * 0 + y) - y / (y * 0 + 1 - y))) := by
    refine hφd.tendsto_slope_zero_right.congr fun t => ?_
    rw [zero_add, hφ0, sub_zero, smul_eq_mul]
    ring
  have hz : Tendsto (fun x : ℝ => c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y)))
      (𝓝[>] 0) (𝓝 1) := by
    have : ContinuousAt (fun x : ℝ => c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y)))
        0 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simpa using ⟨hy0.ne', h1y.ne'⟩
    have h := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    convert h using 2
    simp [hcdef]
    field_simp
  have t4 : Tendsto (fun x : ℝ => x * Li₂ (c * (1 - x) ^ 2 / (((1 - y) * x + y) *
      (y * x + 1 - y)))) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).mul
      (tendsto_Li₂_comp (by norm_num) hz ?_)
    · simpa using h
    filter_upwards [hev] with x hx
    obtain ⟨hP, hQ⟩ := i12R_PQ_pos ⟨hy0, hy1⟩ hx
    have hPQ : ((1 - y) * x + y) * (y * x + 1 - y) = c * (1 - x) ^ 2 + x := by
      rw [hcdef]; ring
    refine ⟨by linarith [div_pos (mul_pos hc (pow_pos (sub_pos.2 hx.2) 2)) (mul_pos hP hQ)],
      (div_le_one (mul_pos hP hQ)).2 (by rw [hPQ]; linarith [hx.1])⟩
  have h := (((hHc.tendsto.mono_left nhdsWithin_le_nhds).add
    (tendsto_mul_log_sq_zero.const_mul (-(3 / (2 * c))))).add
    (tendsto_log_mul_log_one_sub_zero.const_mul (-(6 / c)))).add (t3.const_mul (-(3 * c / 2)))
    |>.add (t4.const_mul (-(3 / c)))
  have e : i12REF y c =ᶠ[𝓝[>] 0] fun x => H x + -(3 / (2 * c)) * (x * log x ^ 2) +
      -(6 / c) * (log x * log (1 - x)) + -(3 * c / 2) * (φ x / x) +
      -(3 / c) * (x * Li₂ (c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y)))) := by
    filter_upwards [hev] with x hx
    have := hx.1.ne'
    simp only [i12REF, hH, hφ, i12ml]
    field_simp
    ring
  refine Tendsto.congr' e.symm ?_
  convert h using 2
  simp only [hH, i12ml, mul_zero, zero_add, sub_zero, mul_one, zero_div, Li₂_zero, log_one,
    zero_mul, add_zero, zero_pow two_ne_zero, Real.log_zero, div_one]
  have := hy0.ne'
  have := h1y.ne'
  field_simp
  ring

/-- **The limit at `1⁻`**. -/
theorem tendsto_i12REF_one {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i12REF y (y * (1 - y))) (𝓝[<] 1) (𝓝 (-(6 * (1 - y * (1 - y))) * (Li₂ (1 - y) + Li₂ y) -
      (9 - 5 * (y * (1 - y))) * (log y + log (1 - y)) -
      π ^ 2 * (2 * (1 - y * (1 - y)) + 1 / (y * (1 - y))) - 3 / 2 - 1 / (y * (1 - y)))) := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1y : 0 < 1 - y := by linarith
  have hc : 0 < y * (1 - y) := mul_pos hy0 h1y
  set c := y * (1 - y) with hcdef
  have hev : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hlP : ContinuousAt (fun x : ℝ => log ((1 - y) * x + y)) 1 :=
    ((by fun_prop : Continuous fun x : ℝ => (1 - y) * x + y).continuousAt).log (by simp)
  have hlQ : ContinuousAt (fun x : ℝ => log (y * x + 1 - y)) 1 :=
    ((by fun_prop : Continuous fun x : ℝ => y * x + 1 - y).continuousAt).log (by simp)
  have hlx : ContinuousAt (fun x : ℝ => log x) 1 :=
    continuousAt_id.log (by norm_num)
  have hL2 : ContinuousAt (fun x : ℝ => Li₂ ((1 - y) * x / ((1 - y) * x + y))) 1 :=
    ContinuousAt.comp (f := fun x : ℝ => (1 - y) * x / ((1 - y) * x + y))
      (i12R_continuousAt_Li₂ (by simp; rw [abs_of_pos h1y]; linarith))
      (((by fun_prop : Continuous fun x : ℝ => (1 - y) * x).continuousAt).div
        ((by fun_prop : Continuous fun x : ℝ => (1 - y) * x + y).continuousAt) (by simp))
  have hL3 : ContinuousAt (fun x : ℝ => Li₂ (y * x / (y * x + 1 - y))) 1 :=
    ContinuousAt.comp (f := fun x : ℝ => y * x / (y * x + 1 - y))
      (i12R_continuousAt_Li₂ (by simp; rw [abs_of_pos hy0]; linarith))
      (((by fun_prop : Continuous fun x : ℝ => y * x).continuousAt).div
        ((by fun_prop : Continuous fun x : ℝ => y * x + 1 - y).continuousAt) (by simp))
  have hL4 : ContinuousAt (fun x : ℝ => Li₂ ((1 - y) * (1 - x))) 1 :=
    ContinuousAt.comp (f := fun x : ℝ => (1 - y) * (1 - x))
      (i12R_continuousAt_Li₂ (by simp)) (by fun_prop)
  have hL5 : ContinuousAt (fun x : ℝ => Li₂ (y * (1 - x))) 1 :=
    ContinuousAt.comp (f := fun x : ℝ => y * (1 - x))
      (i12R_continuousAt_Li₂ (by simp)) (by fun_prop)
  have hLz : ContinuousAt (fun x : ℝ => Li₂ (c * (1 - x) ^ 2 /
      (((1 - y) * x + y) * (y * x + 1 - y)))) 1 :=
    ContinuousAt.comp (f := fun x : ℝ => c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y)))
      (i12R_continuousAt_Li₂ (by simp))
      (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp))
  have hm : ContinuousAt (fun x : ℝ => i12ml (1 - x)) 1 := by fun_prop
  set H : ℝ → ℝ := fun x =>
    -(3 * x / (2 * c)) * (log x - log ((1 - y) * x + y) - log (y * x + 1 - y)) ^ 2 -
    3 * (1 - c) * (log ((1 - y) * x + y) ^ 2 + log (y * x + 1 - y) ^ 2) +
    6 * (1 - c) * (log ((1 - y) * x + y) * log y + log (y * x + 1 - y) * log (1 - y)) +
    6 * (c - 1) * (Li₂ ((1 - y) * x / ((1 - y) * x + y)) + Li₂ (y * x / (y * x + 1 - y))) -
    6 / c * (Li₂ ((1 - y) * (1 - x)) + Li₂ (y * (1 - x))) -
    3 * x / c * Li₂ (c * (1 - x) ^ 2 / (((1 - y) * x + y) * (y * x + 1 - y))) +
    3 * x / (2 * c) * log x -
    3 * c / (2 * x) * (log y + log (1 - y) - log ((1 - y) * x + y) - log (y * x + 1 - y)) -
    (c * x ^ 3 - 5 * c * x ^ 2 + 6 * x ^ 2 + 13 * c * x - 18 * x + 3 * c) / x * i12ml (1 - x) +
    (c / 2 * x ^ 3 + (3 - 3 * c) * x ^ 2 + (9 * c - 12) * x + 0) * (log y + log (1 - y)) +
    (-(c / 2) * x ^ 3 + -(3 * (1 - c)) * x ^ 2 + -(3 * (6 * c ^ 2 - 8 * c + 1) / (2 * c)) * x +
      0) * (log ((1 - y) * x + y) + log (y * x + 1 - y)) +
    -(y * (5 * y ^ 3 - 9 * y ^ 2 + 9 * y - 6) / (1 - y) ^ 2) * log ((1 - y) * x + y) +
    -((1 - y) * (5 * (1 - y) ^ 3 - 9 * (1 - y) ^ 2 + 9 * (1 - y) - 6) / y ^ 2) *
      log (y * x + 1 - y) +
    (0 * x ^ 3 + 1 / 2 * x ^ 2 + -((2 * c + 1) / c) * x + 0) with hH
  have hHc : ContinuousAt H 1 := by
    rw [hH]
    fun_prop (disch := norm_num)
  have h := ((hHc.tendsto.mono_left nhdsWithin_le_nhds).add
    (tendsto_log_mul_log_one_sub_one.const_mul (-(6 / c)))).add
    (tendsto_Li₂_one_left.const_mul (6 * (2 * c ^ 2 - 2 * c - 1) / c))
  have e : i12REF y c =ᶠ[𝓝[<] 1] fun x => H x + -(6 / c) * (log x * log (1 - x)) +
      6 * (2 * c ^ 2 - 2 * c - 1) / c * Li₂ x := by
    filter_upwards [hev] with x hx
    have := hx.1.ne'
    simp only [i12REF, hH, i12ml]
    field_simp
    ring
  refine Tendsto.congr' e.symm ?_
  convert h using 2
  have e1 : 1 - y + y = 1 := by ring
  have e2 : y + 1 - y = 1 := by ring
  simp only [hH, i12ml, mul_one, e1, e2, div_one, sub_self, log_one, sub_zero, zero_mul,
    mul_zero, Li₂_zero, zero_pow two_ne_zero, add_zero, Real.log_zero]
  have := hy0.ne'
  have := h1y.ne'
  clear_value c
  subst hcdef
  field_simp
  ring

theorem i12REx_nonpos {c x : ℝ} (hc : 0 < c) (hx : x ∈ Ioo (0 : ℝ) 1) : i12REx c x ≤ 0 := by
  have hk : 0 < x / ((1 - x) * c) := div_pos hx.1 (mul_pos (sub_pos.2 hx.2) hc)
  obtain ⟨-, hv⟩ := integrableOn_and_integral_i12Rg_inner hk hx
  have h0 : ∫ θ in Ioo x 1, i12Rg (x / ((1 - x) * c) / (1 - θ)) ≤ 0 :=
    setIntegral_nonpos measurableSet_Ioo fun θ hθ => i12Rg_nonpos (div_pos hk (sub_pos.2 hθ.2))
  rw [hv] at h0
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (sub_pos.2 hx.2).le hx.1.le) (by linarith)

/-- **The closed form of `E`**: `∫₀¹ i12REx (y (1 - y)) x dx`, `0 < y < 1`. -/
theorem integral_i12REx_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in Ioo (0 : ℝ) 1, i12REx (y * (1 - y)) x =
      -1 / (y * (1 - y)) - 3 + (6 * y ^ 3 - 15 * y ^ 2 + 17 * y - 9) / (1 - y) ^ 2 * log y +
        (6 * (1 - y) ^ 3 - 15 * (1 - y) ^ 2 + 17 * (1 - y) - 9) / y ^ 2 * log (1 - y) -
        3 * (1 - y * (1 - y)) * (log y ^ 2 + log (1 - y) ^ 2 + π ^ 2) -
        6 * ((1 - y * (1 - y) + (y * (1 - y)) ^ 2) / (y * (1 - y))) * log y * log (1 - y) := by
  have hc : 0 < y * (1 - y) := mul_pos hy.1 (by linarith [hy.2])
  obtain ⟨-, hv⟩ := intervalIntegrable_and_integral_eq_of_nonpos' zero_lt_one
    (fun x hx => hasDerivAt_i12REF hy hx) (fun x hx => i12REx_nonpos hc hx)
    (tendsto_i12REF_zero hy) (tendsto_i12REF_one hy)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hv
  rw [hv]
  have hM : Li₂ (1 - y) = π ^ 2 / 6 - log y * log (1 - y) - Li₂ y := by
    linarith [Li₂_add_Li₂_one_sub hy.1.le hy.2.le]
  rw [hM]
  have := hy.1.ne'
  have : 1 - y ≠ 0 := by linarith [hy.2]
  field_simp
  ring

end QED.ThreeLoopD
