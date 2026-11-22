/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondRA
import QED.Polylog.LiCalculus
import QED.Polylog.ExtraIntegrals
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set (d), master `I₁₂`: reduction of `R₁'(0)` to one dimension

By `QED.ThreeLoopD.hasDerivAt_i12R1_zero`, `R₁'(0)` is the integral over `(y, t, u) ∈ (0, 1)³`
of `i12R1d c t u`, `c = y(1 - y)`. With `X = ut`, `Y = (1 - u)c` and `g` = `i12Rg`,
the integrand splits pointwise (`QED.ThreeLoopD.i12R1d_eq`) as

  `i12R1el c t u + ((1 - X) g(X / ((1 - X) Y)) / t - g(X / Y) / t) / c`,

where `i12R1el` is elementary (logarithms and `h(X) = ((1 - X)² log (1 - X) + X) / X²`).

**`t` first.** The elementary part and `g(κt)/t` (`κ = u / ((1 - u)c)`, `∫₀¹ g(κt)/t = Φ(κ)`)
are integrated by one antiderivative; the remaining part defines `E(c)` (`QED.ThreeLoopD.i12RE`).
**`u` second.** The elementary `u`-integrand `i12R1U` integrates to
`-(1/6) log c + 329/36 - π² + (3 log c + π² - 15/2) / c`, and `∫₀¹ Φ(κ) du = K(1/c)`.

Integrability of the pieces comes from sign-definiteness (`g ≤ 0`, `h ≥ 0`) and from the
integrability of the whole integrand.

## Main results

* `QED.ThreeLoopD.integral_i12R1_t`, `QED.ThreeLoopD.intervalIntegrable_and_integral_i12R1U`.
* `QED.ThreeLoopD.integral_i12R1_section`: the `(t, u)`-integral at fixed `c`.
* `QED.ThreeLoopD.deriv_i12R1_zero_eq`: `R₁'(0) = ∫₀¹ i12R1F y dy`.
* `QED.ThreeLoopD.i12R1F_eq`: `i12R1F` with `K(1/c)` paired into `K(c)`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

theorem i12Rg_nonpos {r : ℝ} (hr : 0 < r) : i12Rg r ≤ 0 := by
  have h1 : 0 < 1 + r := by linarith
  have hL := one_sub_inv_le_log_of_pos h1
  have hM := one_sub_inv_le_log_of_pos (div_pos h1 hr)
  rw [Real.log_div h1.ne' hr.ne', inv_div] at hM
  have key : r ≤ (1 + r) ^ 2 * log (1 + r) - r ^ 2 * log r := by
    have e1 : 1 - (1 + r)⁻¹ = r / (1 + r) := by field_simp; ring
    have e2 : 1 - r / (1 + r) = 1 / (1 + r) := by field_simp; ring
    rw [e1] at hL
    rw [e2] at hM
    have hA : (2 * r + 1) * (r / (1 + r)) ≤ (2 * r + 1) * log (1 + r) :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    have hB : r ^ 2 * (1 / (1 + r)) ≤ r ^ 2 * (log (1 + r) - log r) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have hC : r ≤ (2 * r + 1) * (r / (1 + r)) + r ^ 2 * (1 / (1 + r)) := by
      rw [show (2 * r + 1) * (r / (1 + r)) + r ^ 2 * (1 / (1 + r)) = (3 * r ^ 2 + r) / (1 + r) by
        field_simp; ring, le_div_iff₀ h1]
      nlinarith [sq_nonneg r]
    nlinarith
  unfold i12Rg
  have : 1 ≤ ((1 + r) ^ 2 * log (1 + r) - r ^ 2 * log r) / r := by
    rw [le_div_iff₀ hr]; linarith
  rw [mul_div_assoc]
  linarith

/-- `h(X) = ((1 - X)² log (1 - X) + X) / X²`. -/
noncomputable def i12Rh (X : ℝ) : ℝ := ((1 - X) ^ 2 * log (1 - X) + X) / X ^ 2

theorem i12Rh_nonneg {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) : 0 ≤ i12Rh X := by
  have h1 : 0 < 1 - X := by linarith [hX.2]
  have hL := one_sub_inv_le_log_of_pos h1
  have e : 1 - (1 - X)⁻¹ = -X / (1 - X) := by field_simp; ring
  rw [e, div_le_iff₀ h1] at hL
  unfold i12Rh
  apply div_nonneg _ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hL h1.le, hX.1]

/-- The antiderivative `H` of `h` (`H(0⁺) = 1`). -/
noncomputable def i12RHh (X : ℝ) : ℝ := -log (1 - X) / X + X * log (1 - X) + 2 * Li₂ X - X

theorem hasDerivAt_i12RHh {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12RHh (i12Rh X) X := by
  have h1 : 0 < 1 - X := by linarith [hX.2]
  have hl : HasDerivAt (fun x => log (1 - x)) (-1 / (1 - X)) X := by
    have := ((hasDerivAt_id X).const_sub 1).log h1.ne'
    simpa using this
  have h := ((((hl.neg).div (hasDerivAt_id X) hX.1.ne').add ((hasDerivAt_id X).mul hl)).add
    ((hasDerivAt_Li₂' hX).const_mul 2)).sub (hasDerivAt_id X)
  refine h.congr_deriv ?_
  have hX0 := hX.1.ne'
  have h10 := h1.ne'
  simp only [i12Rh, id, Pi.neg_apply]
  field_simp
  ring

theorem tendsto_i12RHh_zero : Tendsto i12RHh (𝓝[>] 0) (𝓝 1) := by
  have hl : HasDerivAt (fun x => log (1 - x)) (-1) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num)
    simpa using this
  have hs := hl.tendsto_slope_zero_right
  simp only [zero_add, sub_zero, Real.log_one, smul_eq_mul] at hs
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlog : Tendsto (fun x : ℝ => log (1 - x)) (𝓝[>] 0) (𝓝 0) := by
    have : ContinuousAt (fun x : ℝ => log (1 - x)) 0 :=
      (continuousAt_const.sub continuousAt_id).log (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hLi : Tendsto (fun x : ℝ => Li₂ x) (𝓝[>] 0) (𝓝 (Li₂ 0)) := by
    refine tendsto_Li₂_comp (by norm_num) hid ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.1], hx.2.le⟩
  have h := (((hs.neg).add (hid.mul hlog)).add (hLi.const_mul 2)).sub hid
  simp only [Li₂_zero] at h
  convert h using 2
  · simp only [i12RHh]; ring
  · norm_num

/-- The elementary part of the integrand of `R₁'(0)`. -/
noncomputable def i12R1el (c t u : ℝ) : ℝ :=
  u * (1 - u) * (2 * log c + 2 * log t - log (1 - t) + log u + log (1 - u)) -
    3 * u * (1 - u) * i12Rh (u * t) - 3 * u * (1 - u) * (log (1 - u) + log c) +
    (6 * u * log (1 - u) + 6 * u * log c - 6 * ((1 - u * t) * log (1 - u * t)) / t -
      6 * u * log u - 6 * u * log t) / c

/-- The part of the integrand of `R₁'(0)` giving `E(c)`. -/
noncomputable def i12R1Ee (c t u : ℝ) : ℝ :=
  (1 - u * t) * i12Rg (u * t / ((1 - u * t) * (1 - u) * c)) / t

theorem i12R1d_eq {c t u : ℝ} (hc : 0 < c) (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i12R1d c t u = i12R1el c t u +
      (i12R1Ee c t u - i12Rg (1 / c * u / (1 - u) * t) / t) / c := by
  have ht0 := ht.1.ne'
  have hu0 := hu.1.ne'
  have hc0 := hc.ne'
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have hut : u * t < 1 := by nlinarith [hu.1, hu.2, ht.1, ht.2]
  have hut1 : 0 < 1 - u * t := by linarith
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hX := mul_pos hu.1 ht.1
  have hY := mul_pos hu1 hc
  have hN : 0 < u * t + (1 - u) * c - u * t * ((1 - u) * c) := by nlinarith [mul_pos hY hut1]
  have hS : 0 < u * t + (1 - u) * c := by linarith
  have hD : 0 < (1 - u * t) * (1 - u) * c := by positivity
  have e1 : 1 + u * t / ((1 - u * t) * (1 - u) * c) =
      (u * t + (1 - u) * c - u * t * ((1 - u) * c)) / ((1 - u * t) * (1 - u) * c) := by
    field_simp; ring
  have e2 : 1 + u * t / ((1 - u) * c) = (u * t + (1 - u) * c) / ((1 - u) * c) := by
    field_simp; ring
  have e3 : 1 / c * u / (1 - u) * t = u * t / ((1 - u) * c) := by field_simp
  simp only [i12R1d, i12Phi1d, i12R1el, i12R1Ee, i12Rg, i12Rh, e1, e2, e3]
  rw [Real.log_div hN.ne' hD.ne', Real.log_div hS.ne' hY.ne', Real.log_div hX.ne' hD.ne',
    Real.log_div hX.ne' hY.ne', Real.log_mul (mul_pos hut1 hu1).ne' hc0,
    Real.log_mul hut1.ne' hu1.ne', Real.log_mul hu1.ne' hc0, Real.log_mul hu0 ht0,
    Real.log_mul hc0 ht0, Real.log_mul hu0 hu1.ne']
  generalize log (u * t + (1 - u) * c - u * t * ((1 - u) * c)) = LN
  generalize log (u * t + (1 - u) * c) = LS
  generalize log (1 - u * t) = LX
  generalize log (1 - u) = LU
  generalize log u = Lu
  generalize log t = Lt
  generalize log c = Lc
  generalize log (1 - t) = LT
  field_simp
  ring

/-! ### The `t`-integral -/

/-- `x log x`. -/
noncomputable def i12ml (x : ℝ) : ℝ := x * log x

@[fun_prop] theorem continuous_i12ml : Continuous i12ml := Real.continuous_mul_log

theorem hasDerivAt_i12ml {x : ℝ} (hx : 0 < x) : HasDerivAt i12ml (log x + 1) x := by
  have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')
  refine h.congr_deriv ?_
  simp only [id]
  field_simp

theorem i12_continuousOn_Li₂_mul {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun t => Li₂ (u * t)) (Icc 0 1) :=
  continuousOn_Li₂.comp (continuous_const.mul continuous_id).continuousOn fun t ht =>
    ⟨by nlinarith [hu.1, ht.1], by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩

theorem i12_tendsto_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto f (𝓝[>] 0) (𝓝 (f 0)) ∧ Tendsto f (𝓝[<] 1) (𝓝 (f 1)) :=
  ⟨((hf 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT one_pos)).tendsto,
    ((hf 1 ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT one_pos)).tendsto⟩

/-- The part of the `t`-antiderivative continuous on `[0, 1]`. -/
noncomputable def i12R1Pc (c u t : ℝ) : ℝ :=
  u * (1 - u) * ((2 * log c + log u + log (1 - u)) * t + 2 * i12ml t - 2 * t + i12ml (1 - t) + t) -
    3 * u * (1 - u) * (log (1 - u) + log c) * t +
    ((6 * u * log (1 - u) + 6 * u * log c - 6 * u * log u) * t - 6 * u * (i12ml t - t) -
      6 * (i12ml (1 - u * t) + u * t)) / c + 6 * Li₂ (u * t) / c

/-- The `t`-antiderivative of `i12R1el - g(κt)/(ct)`. -/
noncomputable def i12R1Prim (c u t : ℝ) : ℝ :=
  i12R1Pc c u t - 3 * (1 - u) * i12RHh (u * t) - i12RPhi (1 / c * u / (1 - u) * t) / c

theorem continuousOn_i12R1Pc (c : ℝ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (i12R1Pc c u) (Icc 0 1) := by
  have h : Continuous fun t => u * (1 - u) * ((2 * log c + log u + log (1 - u)) * t +
      2 * i12ml t - 2 * t + i12ml (1 - t) + t) - 3 * u * (1 - u) * (log (1 - u) + log c) * t +
      ((6 * u * log (1 - u) + 6 * u * log c - 6 * u * log u) * t - 6 * u * (i12ml t - t) -
        6 * (i12ml (1 - u * t) + u * t)) / c := by fun_prop
  exact h.continuousOn.add ((i12_continuousOn_Li₂_mul hu).const_mul 6 |>.div_const c)

theorem hasDerivAt_i12R1Prim {c u t : ℝ} (hc : 0 < c) (hu : u ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12R1Prim c u) (i12R1el c t u - i12Rg (1 / c * u / (1 - u) * t) / t / c) t := by
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hX : u * t ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hu.1 ht.1, by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩
  have hX1 : 0 < 1 - u * t := by linarith [hX.2]
  have hk : 0 < 1 / c * u / (1 - u) := div_pos (mul_pos (by positivity) hu.1) hu1
  have hmt := hasDerivAt_i12ml ht.1
  have hm1 := (hasDerivAt_i12ml ht1).comp t ((hasDerivAt_id t).const_sub 1)
  have hmX := (hasDerivAt_i12ml hX1).comp t (((hasDerivAt_id t).const_mul u).const_sub 1)
  have hL := (hasDerivAt_Li₂' hX).comp t ((hasDerivAt_id t).const_mul u)
  have hH := (hasDerivAt_i12RHh hX).comp t ((hasDerivAt_id t).const_mul u)
  have hP := (hasDerivAt_i12RPhi (mul_pos hk ht.1)).comp t ((hasDerivAt_id t).const_mul _)
  have hlin : ∀ a : ℝ, HasDerivAt (fun t : ℝ => a * t) a t := fun a => by
    simpa using (hasDerivAt_id t).const_mul a
  have hA := (((((hlin (2 * log c + log u + log (1 - u))).add (hmt.const_mul 2)).sub
    (hlin 2)).add hm1).add (hasDerivAt_id t)).const_mul (u * (1 - u))
  have hB := ((((hlin (6 * u * log (1 - u) + 6 * u * log c - 6 * u * log u)).sub
      ((hmt.sub (hasDerivAt_id t)).const_mul (6 * u))).sub
      ((hmX.add (hlin u)).const_mul 6)).div_const c)
  have h := ((hA.sub (hlin (3 * u * (1 - u) * (log (1 - u) + log c)))).add hB).add
    ((hL.const_mul 6).div_const c)
  have h2 := (h.sub (hH.const_mul (3 * (1 - u)))).sub (hP.div_const c)
  have e : i12R1Prim c u = fun t => (u * (1 - u) * ((2 * log c + log u + log (1 - u)) * t +
      2 * i12ml t - 2 * t + i12ml (1 - t) + id t) - 3 * u * (1 - u) * (log (1 - u) + log c) * t +
      ((6 * u * log (1 - u) + 6 * u * log c - 6 * u * log u) * t - 6 * u * (i12ml t - id t) -
        6 * (i12ml (1 - u * t) + u * t)) / c + 6 * Li₂ (u * t) / c) -
      3 * (1 - u) * i12RHh (u * t) - i12RPhi (1 / c * u / (1 - u) * t) / c := by
    funext t; simp [i12R1Prim, i12R1Pc]
  rw [e]
  refine h2.congr_deriv ?_
  have ht0 := ht.1.ne'
  have hX0 := hX.1.ne'
  have hk0 := hk.ne'
  have hu0 := hu.1.ne'
  have hc0 := hc.ne'
  have hu10 := hu1.ne'
  simp only [i12R1el]
  generalize i12Rg (1 / c * u / (1 - u) * t) = G
  generalize i12Rh (u * t) = Hh
  field_simp
  ring

/-- The elementary `u`-integrand left after the `t`-integration. -/
noncomputable def i12R1U (c u : ℝ) : ℝ :=
  u * (1 - u) * (2 * log c + log u + log (1 - u) - 1) - 3 * u * (1 - u) * (log (1 - u) + log c) +
    3 * (1 - u) - 3 * (1 - u) * i12RHh u +
    (6 * u * log (1 - u) + 6 * u * log c - 6 * u * log u + 6 * Li₂ u -
      6 * ((1 - u) * log (1 - u))) / c

theorem i12_intervalIntegrable_log_one_sub :
    IntervalIntegrable (fun t : ℝ => log (1 - t)) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).comp_sub_left 1
  simpa using h.symm

/-- `∫₀¹ g(κt)/t dt = Φ(κ)`. -/
theorem intervalIntegrable_and_integral_i12Rg_div {k : ℝ} (hk : 0 < k) :
    IntervalIntegrable (fun t => i12Rg (k * t) / t) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, i12Rg (k * t) / t = i12RPhi k := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos' (F := fun t => i12RPhi (k * t))
    (f := fun t => i12Rg (k * t) / t)
    (A := 0) (B := i12RPhi (k * 1)) zero_lt_one (fun t ht => ?_) (fun t ht => ?_)
    (tendsto_i12RPhi_zero.comp (i12_tendsto_mul_nhdsGT hk)) ?_
  · simpa using h
  · have := (hasDerivAt_i12RPhi (mul_pos hk ht.1)).comp t ((hasDerivAt_id t).const_mul k)
    refine this.congr_deriv ?_
    have := ht.1.ne'
    have := hk.ne'
    field_simp
  · exact div_nonpos_of_nonpos_of_nonneg (i12Rg_nonpos (mul_pos hk ht.1)) ht.1.le
  · have hc : ContinuousAt (fun t => i12RPhi (k * t)) 1 :=
      (hasDerivAt_i12RPhi (by simpa using hk)).continuousAt.comp (by fun_prop)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem intervalIntegrable_i12Rh_mul {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun t => i12Rh (u * t)) volume 0 1 := by
  have hc : ContinuousAt (fun t => i12RHh (u * t) / u) 1 :=
    ((hasDerivAt_i12RHh (by simpa using hu)).continuousAt.comp (by fun_prop)).div_const u
  refine (intervalIntegrable_and_integral_eq_of_nonneg' (F := fun t => i12RHh (u * t) / u)
    zero_lt_one (fun t ht => ?_) (fun t ht => i12Rh_nonneg ?_)
    ((tendsto_i12RHh_zero.comp (i12_tendsto_mul_nhdsGT hu.1)).div_const u)
    (hc.tendsto.mono_left nhdsWithin_le_nhds)).1
  · have hX : u * t ∈ Ioo (0 : ℝ) 1 :=
      ⟨mul_pos hu.1 ht.1, by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩
    have := ((hasDerivAt_i12RHh hX).comp t ((hasDerivAt_id t).const_mul u)).div_const u
    refine this.congr_deriv ?_
    have := hu.1.ne'
    field_simp
  · exact ⟨mul_pos hu.1 ht.1, by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩

theorem intervalIntegrable_i12_log_one_sub_mul {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun t => (1 - u * t) * log (1 - u * t) / t) volume 0 1 := by
  have hcont : ContinuousOn (fun t => -Li₂ (u * t) + i12ml (1 - u * t) + u * t) (Icc 0 1) :=
    ((i12_continuousOn_Li₂_mul ⟨hu.1.le, hu.2.le⟩).neg.add (by fun_prop)).add (by fun_prop)
  obtain ⟨h0, h1⟩ := i12_tendsto_Icc hcont
  refine (intervalIntegrable_and_integral_eq_of_nonpos' zero_lt_one (fun t ht => ?_)
    (fun t ht => ?_) h0 h1).1
  · have hX : u * t ∈ Ioo (0 : ℝ) 1 :=
      ⟨mul_pos hu.1 ht.1, by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩
    have hX1 : 0 < 1 - u * t := by linarith [hX.2]
    have h := ((((hasDerivAt_Li₂' hX).comp t ((hasDerivAt_id t).const_mul u)).neg).add
      ((hasDerivAt_i12ml hX1).comp t (((hasDerivAt_id t).const_mul u).const_sub 1))).add
      ((hasDerivAt_id t).const_mul u)
    refine h.congr_deriv ?_
    have := hu.1.ne'
    have := ht.1.ne'
    field_simp
    ring
  · have hX : u * t < 1 := by nlinarith [hu.1, hu.2, ht.1, ht.2]
    have hl : log (1 - u * t) ≤ 0 := Real.log_nonpos (by linarith) (by nlinarith [hu.1, ht.1])
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hl)
      ht.1.le

/-- **The `t`-integral** of the integrand of `R₁'(0)`, given its integrability. -/
theorem integral_i12R1_t {c u : ℝ} (hc : 0 < c) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hint : IntervalIntegrable (fun t => i12R1d c t u) volume 0 1) :
    IntervalIntegrable (fun t => i12R1Ee c t u) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, i12R1d c t u = i12R1U c u - i12RPhi (1 / c * u / (1 - u)) / c +
        (∫ t in (0 : ℝ)..1, i12R1Ee c t u) / c := by
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have hk : 0 < 1 / c * u / (1 - u) := div_pos (mul_pos (by positivity) hu.1) hu1
  obtain ⟨hgi, hgv⟩ := intervalIntegrable_and_integral_i12Rg_div hk
  have hel : IntervalIntegrable (fun t => i12R1el c t u) volume 0 1 := by
    have h := ((((intervalIntegrable_const (c := u * (1 - u) * (2 * log c + log u + log (1 - u)) -
      3 * u * (1 - u) * (log (1 - u) + log c) +
      (6 * u * log (1 - u) + 6 * u * log c - 6 * u * log u) / c)).add
      ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).const_mul
        (2 * u * (1 - u) - 6 * u / c))).sub
      (i12_intervalIntegrable_log_one_sub.const_mul (u * (1 - u)))).sub
      ((intervalIntegrable_i12Rh_mul hu).const_mul (3 * u * (1 - u)))).sub
      ((intervalIntegrable_i12_log_one_sub_mul hu).const_mul (6 / c))
    refine h.congr fun t _ => ?_
    simp only [i12R1el]
    ring
  have hpi : IntervalIntegrable (fun t => i12R1el c t u -
      i12Rg (1 / c * u / (1 - u) * t) / t / c) volume 0 1 := hel.sub (hgi.div_const c)
  have hPc := continuousOn_i12R1Pc c (u := u) ⟨hu.1.le, hu.2.le⟩
  obtain ⟨hP0, hP1⟩ := i12_tendsto_Icc hPc
  have h0 : Tendsto (i12R1Prim c u) (𝓝[>] 0) (𝓝 (i12R1Pc c u 0 - 3 * (1 - u) * 1 - 0 / c)) :=
    (hP0.sub ((tendsto_i12RHh_zero.comp (i12_tendsto_mul_nhdsGT hu.1)).const_mul _)).sub
      ((tendsto_i12RPhi_zero.comp (i12_tendsto_mul_nhdsGT hk)).div_const c)
  have hHc : ContinuousAt (fun t => i12RHh (u * t)) 1 :=
    (hasDerivAt_i12RHh (by simpa using hu)).continuousAt.comp (by fun_prop)
  have hΦc : ContinuousAt (fun t => i12RPhi (1 / c * u / (1 - u) * t)) 1 :=
    (hasDerivAt_i12RPhi (by simpa using hk)).continuousAt.comp (by fun_prop)
  have h1 : Tendsto (i12R1Prim c u) (𝓝[<] 1) (𝓝 (i12R1Prim c u 1)) :=
    (hP1.sub ((hHc.tendsto.mono_left nhdsWithin_le_nhds).const_mul _)).sub
      ((hΦc.tendsto.mono_left nhdsWithin_le_nhds).div_const c)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun t ht => hasDerivAt_i12R1Prim hc hu ht) hpi h0 h1
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, i12R1Ee c t u = c * (i12R1d c t u -
      (i12R1el c t u - i12Rg (1 / c * u / (1 - u) * t) / t / c)) := by
    intro t ht
    rw [i12R1d_eq hc ht hu]
    field_simp
    ring
  have hEi : IntervalIntegrable (fun t => i12R1Ee c t u) volume 0 1 :=
    i12_intervalIntegrable_congr_Ioo (fun t ht => (hpt t ht).symm)
      ((hint.sub hpi).const_mul c)
  refine ⟨hEi, ?_⟩
  have hsplit : ∫ t in (0 : ℝ)..1, i12R1d c t u = ∫ t in (0 : ℝ)..1,
      ((i12R1el c t u - i12Rg (1 / c * u / (1 - u) * t) / t / c) + i12R1Ee c t u / c) :=
    i12_integral_congr_Ioo fun t ht => by
      rw [i12R1d_eq hc ht hu]
      ring
  rw [hsplit, intervalIntegral.integral_add hpi (hEi.div_const c), hftc,
    intervalIntegral.integral_div]
  simp only [i12R1Prim, i12R1Pc, i12R1U, i12ml, mul_one, mul_zero, sub_zero, sub_self,
    Real.log_one, Real.log_zero, Li₂_zero, zero_div, add_zero]
  ring

/-! ### The `u`-integral of the elementary part -/

theorem i12_hasDerivAt_cubic (a₀ a₁ a₂ a₃ u : ℝ) :
    HasDerivAt (fun u => a₀ + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3)
      (a₁ + 2 * a₂ * u + 3 * a₃ * u ^ 2) u := by
  have hi := hasDerivAt_id u
  have h := ((((hasDerivAt_const u a₀).add (hi.const_mul a₁)).add
    ((hi.pow 2).const_mul a₂)).add ((hi.pow 3).const_mul a₃))
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- The `u`-antiderivative of `i12R1U`. -/
noncomputable def i12R1V (c u : ℝ) : ℝ :=
  (-40 / 9 + 3 / c + (34 / 3 - 6 / c) * u + (-log c / 2 + 3 * log c / c - 13 / 12 - 3 / (2 * c)) *
      u ^ 2 + (log c / 3 - 10 / 9) * u ^ 3) +
    (0 + (1 / 2 - 3 / c) * u + (-1 / 3) * u ^ 2 + 0 * u ^ 3) * i12ml u +
    (25 / 3 - 6 / c + (-2 / 3 - 6 / c) * u + (-5 / 3) * u ^ 2 + 0 * u ^ 3) * i12ml (1 - u) +
    (-3 + (-6 + 6 / c) * u + 3 * u ^ 2 + 0 * u ^ 3) * Li₂ u

theorem hasDerivAt_i12R1V {c u : ℝ} (hc : 0 < c) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12R1V c) (i12R1U c u) u := by
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have hm := hasDerivAt_i12ml hu.1
  have hm1 := (hasDerivAt_i12ml hu1).comp u ((hasDerivAt_id u).const_sub 1)
  have hL := hasDerivAt_Li₂' hu
  have hP := i12_hasDerivAt_cubic (-40 / 9 + 3 / c) (34 / 3 - 6 / c)
    (-log c / 2 + 3 * log c / c - 13 / 12 - 3 / (2 * c)) (log c / 3 - 10 / 9) u
  have hA := i12_hasDerivAt_cubic 0 (1 / 2 - 3 / c) (-1 / 3) 0 u
  have hB := i12_hasDerivAt_cubic (25 / 3 - 6 / c) (-2 / 3 - 6 / c) (-5 / 3) 0 u
  have hC := i12_hasDerivAt_cubic (-3) (-6 + 6 / c) 3 0 u
  have h := ((hP.add (hA.mul hm)).add (hB.mul hm1)).add (hC.mul hL)
  have e : i12R1V c = ((fun u => (-40 / 9 + 3 / c) + (34 / 3 - 6 / c) * u +
      (-log c / 2 + 3 * log c / c - 13 / 12 - 3 / (2 * c)) * u ^ 2 +
      (log c / 3 - 10 / 9) * u ^ 3) +
    (fun u => 0 + (1 / 2 - 3 / c) * u + (-1 / 3) * u ^ 2 + 0 * u ^ 3) * i12ml) +
    (fun u => (25 / 3 - 6 / c) + (-2 / 3 - 6 / c) * u + (-5 / 3) * u ^ 2 + 0 * u ^ 3) *
      (i12ml ∘ HSub.hSub 1) +
    (fun u => (-3) + (-6 + 6 / c) * u + 3 * u ^ 2 + 0 * u ^ 3) * Li₂ := by
    funext u; simp [i12R1V]
  rw [e]
  refine h.congr_deriv ?_
  have hu0 := hu.1.ne'
  have hc0 := hc.ne'
  simp only [i12R1U, i12RHh, i12ml, Function.comp_apply]
  field_simp
  ring

theorem continuousOn_i12R1V (c : ℝ) : ContinuousOn (i12R1V c) (Icc 0 1) := by
  have h2 : ContinuousOn Li₂ (Icc 0 1) :=
    continuousOn_Li₂.mono (Icc_subset_Icc (by norm_num) le_rfl)
  unfold i12R1V
  exact (by fun_prop : Continuous fun u : ℝ => (-40 / 9 + 3 / c + (34 / 3 - 6 / c) * u +
    (-log c / 2 + 3 * log c / c - 13 / 12 - 3 / (2 * c)) * u ^ 2 + (log c / 3 - 10 / 9) * u ^ 3) +
    (0 + (1 / 2 - 3 / c) * u + (-1 / 3) * u ^ 2 + 0 * u ^ 3) * i12ml u +
    (25 / 3 - 6 / c + (-2 / 3 - 6 / c) * u + (-5 / 3) * u ^ 2 + 0 * u ^ 3) *
      i12ml (1 - u)).continuousOn.add ((by fun_prop : Continuous fun u : ℝ =>
    -3 + (-6 + 6 / c) * u + 3 * u ^ 2 + 0 * u ^ 3).continuousOn.mul h2)

theorem intervalIntegrable_i12_log_one_sub_div :
    IntervalIntegrable (fun u : ℝ => -log (1 - u) / u) volume 0 1 := by
  have h2 : ContinuousOn Li₂ (Icc 0 1) :=
    continuousOn_Li₂.mono (Icc_subset_Icc (by norm_num) le_rfl)
  obtain ⟨h0, h1⟩ := i12_tendsto_Icc h2
  refine (intervalIntegrable_and_integral_eq_of_nonneg' zero_lt_one
    (fun u hu => hasDerivAt_Li₂' hu) (fun u hu => ?_) h0 h1).1
  have : log (1 - u) ≤ 0 := Real.log_nonpos (by linarith [hu.2]) (by linarith [hu.1])
  exact div_nonneg (by linarith) hu.1.le

/-- **The `u`-integral of the elementary part.** -/
theorem intervalIntegrable_and_integral_i12R1U {c : ℝ} (hc : 0 < c) :
    IntervalIntegrable (i12R1U c) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, i12R1U c u =
        -(1 / 6) * log c + 329 / 36 - π ^ 2 + (3 * log c + π ^ 2 - 15 / 2) / c := by
  have hI : ∀ {f : ℝ → ℝ}, Continuous f → ContinuousOn f (uIcc 0 1) :=
    fun hf => hf.continuousOn
  have hLi : IntervalIntegrable Li₂ volume 0 1 :=
    (continuousOn_Li₂.mono (by
      rw [uIcc_of_le zero_le_one]; exact Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable
  have hlog := intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)
  have h := ((((intervalIntegrable_const (c := 0)).add
    ((hI (by fun_prop : Continuous fun u : ℝ => u * (1 - u) * (2 * log c - 1) -
      3 * u * (1 - u) * log c + 3 * (1 - u) + 3 * u * (1 - u) +
        6 * u * log c / c)).intervalIntegrable)).add
    (hlog.continuousOn_mul
      (hI (by fun_prop : Continuous fun u : ℝ => u * (1 - u) - 6 * u / c)))).add
    (i12_intervalIntegrable_log_one_sub.continuousOn_mul
      (hI (by fun_prop : Continuous fun u : ℝ => -5 * u * (1 - u) + (12 * u - 6) / c)))).add
    (intervalIntegrable_i12_log_one_sub_div.continuousOn_mul
      (hI (by fun_prop : Continuous fun u : ℝ => -3 * (1 - u))))
  have hU : IntervalIntegrable (i12R1U c) volume 0 1 := by
    refine (h.add (hLi.continuousOn_mul (hI (by fun_prop : Continuous fun u : ℝ =>
      6 / c - 6 * (1 - u))))).congr fun u _ => ?_
    simp only [i12R1U, i12RHh]
    ring
  obtain ⟨h0, h1⟩ := i12_tendsto_Icc (continuousOn_i12R1V c)
  refine ⟨hU, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u hu => hasDerivAt_i12R1V hc hu) hU h0 h1]
  simp only [i12R1V, i12ml, Li₂_one, Li₂_zero, sub_zero, sub_self, Real.log_one,
    Real.log_zero, mul_zero, zero_mul, one_pow, zero_pow two_ne_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  ring

/-! ### `R₁'(0)` as a one-dimensional integral -/

/-- `E(c) = ∫₀¹ du ∫₀¹ dt (1 - ut) g(ut / ((1 - ut)(1 - u)c)) / t`. -/
noncomputable def i12RE (c : ℝ) : ℝ := ∫ u in Ioo (0 : ℝ) 1, ∫ t in Ioo (0 : ℝ) 1, i12R1Ee c t u

/-- The `y`-integrand of `R₁'(0)`, `c = y(1 - y)`. -/
noncomputable def i12R1F (y : ℝ) : ℝ :=
  -(1 / 6) * log (y * (1 - y)) + 329 / 36 - π ^ 2 + (3 * log (y * (1 - y)) + π ^ 2 - 15 / 2 -
    i12RK (1 / (y * (1 - y))) + i12RE (y * (1 - y))) / (y * (1 - y))

/-- **The `(t, u)`-integral at fixed `c`.** -/
theorem integral_i12R1_section {c : ℝ} (hc : 0 < c)
    (hi : Integrable (fun p : ℝ × ℝ => i12R1d c p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    ∫ p, i12R1d c p.1 p.2 ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) =
      -(1 / 6) * log c + 329 / 36 - π ^ 2 +
        (3 * log c + π ^ 2 - 15 / 2 - i12RK (1 / c) + i12RE c) / c := by
  have hm : 0 < 1 / c := by positivity
  obtain ⟨hUi, hUv⟩ := intervalIntegrable_and_integral_i12R1U hc
  have hUo : IntegrableOn (i12R1U c) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hUi
  have hK := integrableOn_i12RK hm
  have hsec : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ t in Ioo (0 : ℝ) 1, i12R1d c t u = i12R1U c u - i12RPhi (1 / c * u / (1 - u)) / c +
        (∫ t in Ioo (0 : ℝ) 1, i12R1Ee c t u) / c := by
    filter_upwards [hi.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with u hu hu'
    have hint : IntervalIntegrable (fun t => i12R1d c t u) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hu
    have h := (integral_i12R1_t hc hu' hint).2
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
    exact h
  have hEi : IntegrableOn (fun u => (∫ t in Ioo (0 : ℝ) 1, i12R1Ee c t u) / c) (Ioo 0 1) := by
    have h := ((hi.integral_prod_right.sub hUo).add (hK.div_const c))
    refine h.congr ?_
    filter_upwards [hsec] with u hu
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hu]
    ring
  have hUK : IntegrableOn (fun u => i12R1U c u - i12RPhi (1 / c * u / (1 - u)) / c) (Ioo 0 1) :=
    hUo.sub (hK.div_const c)
  rw [integral_prod_symm _ hi, integral_congr_ae hsec, integral_add hUK hEi,
    integral_sub hUo (hK.div_const c), integral_div, integral_div]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hUv]
  have hKv : ∫ u in Ioo (0 : ℝ) 1, i12RPhi (1 / c * u / (1 - u)) = i12RK (1 / c) := by
    rw [i12RK, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hKv, ← i12RE]
  ring

/-- **`R₁'(0)` in one dimension**: `R₁'(0) = ∫₀¹ i12R1F y dy`, with
`i12R1F y = -(1/6) log c + 329/36 - π² + (3 log c + π² - 15/2 - K(1/c) + E(c)) / c`,
`c = y(1 - y)`; the integrand is integrable. -/
theorem deriv_i12R1_zero_eq :
    IntegrableOn i12R1F (Ioo 0 1) ∧
      deriv i12R1 0 = ((∫ y in Ioo (0 : ℝ) 1, i12R1F y : ℝ) : ℂ) := by
  obtain ⟨hi, hd⟩ := hasDerivAt_i12R1_zero
  have hiR : Integrable (fun z : ℝ × ℝ × ℝ => i12R1d (z.1 * (1 - z.1)) z.2.1 z.2.2)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
    hi.re.congr (ae_of_all _ fun z => Complex.ofReal_re _)
  rw [volume_restrict_prod3] at hiR
  have hae : ∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ w, i12R1d (y * (1 - y)) w.1 w.2 ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) = i12R1F y := by
    filter_upwards [hiR.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with y hy hy'
    exact integral_i12R1_section (mul_pos hy'.1 (sub_pos.2 hy'.2)) hy
  refine ⟨hiR.integral_prod_left.congr hae, ?_⟩
  rw [hd.deriv, integral_complex_ofReal]
  congr 1
  change ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
    i12R1d (z.1 * (1 - z.1)) z.2.1 z.2.2 = _
  rw [volume_restrict_prod3, integral_prod _ hiR]
  exact integral_congr_ae hae

/-- `i12R1F` with the pairing `K(c) + K(1/c) = -6 - 2π² - 3 log² c` applied. -/
theorem i12R1F_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    i12R1F y = i12RK (y * (1 - y)) / (y * (1 - y)) + (-(1 / 6) * log (y * (1 - y)) + 329 / 36 -
      π ^ 2 + (3 * log (y * (1 - y)) + 3 * π ^ 2 - 3 / 2 + 3 * log (y * (1 - y)) ^ 2 +
        i12RE (y * (1 - y))) / (y * (1 - y))) := by
  have hc : 0 < y * (1 - y) := mul_pos hy.1 (sub_pos.2 hy.2)
  have h := i12RK_add_i12RK_inv hc
  rw [i12R1F, show i12RK (1 / (y * (1 - y))) = -6 - 2 * π ^ 2 - 3 * log (y * (1 - y)) ^ 2 -
    i12RK (y * (1 - y)) by linarith]
  field_simp
  ring

end QED.ThreeLoopD
