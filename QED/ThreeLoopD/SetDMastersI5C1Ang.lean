/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C0Ang
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₅`: the angular integrals at order `ε`

Every angular denominator of the kernel is a positive multiple of
`D_k(z) = 1 - k² - 2 i k z` (`QED.ThreeLoopD.i5Dk`) with `0 < k < 1`. By
`QED.ThreeLoopD.i5_integral_ang`, `∫₋₁¹ √(1 - z²) / D_k(z) dz = π/2` for every such `k`. At
order `ε` two more angular integrals occur:

  `∫₋₁¹ √(1 - z²) log D_k(z) / D_k(z) dz = π/2 · (-1 + (1 + k²)/k² · log (1 + k²))`,
  `∫₋₁¹ √(1 - z²) log (1 - z²) / D_k(z) dz = π/2 · (-2 log 2 + (1 + k²)/k² · log (1 + k²))`

(`QED.ThreeLoopD.i5_integral_angLogD`, `QED.ThreeLoopD.i5_integral_angLogW`). More generally
`∫₋₁¹ √(1 - z²) log D_{k'}(z) / D_k(z) dz = π/2 · (-k'/k + (1 + k²)/k² · log (1 + k k'))`
(`QED.ThreeLoopD.i5_integral_angLogDD`).

**The first.** Along `j ∈ [0, k']` the real part `1 - j²` of `D_j(z)` stays positive, so
`log D_{k'}(z) = ∫₀^{k'} (-2j - 2iz)/D_j(z) dj`. By the partial fractions
`(-2j - 2iz)/(D_j D_k) = (1/j)(1/D_k - (1 + j²)(k/D_k - j/D_j)/((k - j)(1 + jk)))`, `j ≠ k`, the
angular integral of the integrand is `π/2 · (k - j)/(1 + jk)`, whose integral over `(0, k')` is
the right side. The integrand is continuous on the compact rectangle, so Fubini applies.

**The second.** Its integrand is `√(1 - z²) log (1 - z²)` times the even part
`(1 - k²)/((1 - k²)² + 4k² z²)` of `1/D_k`. Now `log (1 - z²) = -∫₀¹ 2r z²/(1 - (1 - r²) z²) dr`,
and the integrand of the double integral is bounded. The angular integrals are of the type
`∫₋₁¹ √(1 - z²)/(p² + (q² - p²) z²) dz = π/(p (p + q))` (`QED.ThreeLoopD.i5_integral_asF`, from
the primitive `QED.ThreeLoopD.i5AsF`); after them the `r`-integrand is
`π r (1 - k²)/((1 + r)(1 + k² + r (1 - k²)))`.

## Main results

* `QED.ThreeLoopD.i5_integral_asF`, `QED.ThreeLoopD.i5_integral_angD`.
* `QED.ThreeLoopD.i5_integral_angLogDD`, `QED.ThreeLoopD.i5_integral_angLogD`,
  `QED.ThreeLoopD.i5_integral_angLogW`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-! ### The angular integral of `√(1 - z²)/(p² + (q² - p²) z²)` -/

/-- The primitive `((q/p) arcsin (z q/√(p² + (q² - p²) z²)) - arcsin z)/(q² - p²)` of
`√(1 - z²)/(p² + (q² - p²) z²)`. -/
noncomputable def i5AsF (p q z : ℝ) : ℝ :=
  (q / p * Real.arcsin (z * q / √(p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2)) - Real.arcsin z) /
    (q ^ 2 - p ^ 2)

theorem i5_asF_den_pos {p q z : ℝ} (hp : 0 < p) (hq : 0 < q) (hz : z ∈ Icc (-1 : ℝ) 1) :
    0 < p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2 := by
  have h : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  rcases h.lt_or_eq with h | h
  · nlinarith [sq_nonneg (q * z), mul_pos (pow_pos hp 2) h]
  · have hz2 : z ^ 2 = 1 := by linarith
    rw [hz2]
    nlinarith [pow_pos hq 2]

theorem hasDerivAt_i5AsF {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hb : q ^ 2 - p ^ 2 ≠ 0) {z : ℝ}
    (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (i5AsF p q) (√(1 - z ^ 2) / (p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2)) z := by
  have hw : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hd := i5_asF_den_pos hp hq (Ioo_subset_Icc_self hz)
  set B := √(p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2) with hB
  set W := √(1 - z ^ 2) with hW
  have hB0 : 0 < B := Real.sqrt_pos.mpr hd
  have hW0 : 0 < W := Real.sqrt_pos.mpr hw
  have hB2 : B ^ 2 = p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2 := Real.sq_sqrt hd.le
  have hW2 : W ^ 2 = 1 - z ^ 2 := Real.sq_sqrt hw.le
  have hdB : HasDerivAt (fun z : ℝ => √(p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2))
      ((q ^ 2 - p ^ 2) * z / B) z := by
    have h := ((hasDerivAt_pow 2 z).const_mul (q ^ 2 - p ^ 2)).const_add (p ^ 2)
    refine (h.sqrt hd.ne').congr_deriv ?_
    rw [← hB]; field_simp; ring
  have hdg : HasDerivAt (fun z : ℝ => z * q / √(p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2))
      (q * p ^ 2 / (B ^ 2 * B)) z := by
    refine (((hasDerivAt_id z).mul_const q).div hdB hB0.ne').congr_deriv ?_
    rw [← hB]; field_simp; rw [hB2]; simp only [id]; ring
  set g := z * q / B with hg
  have hg2 : 1 - g ^ 2 = (p * W / B) ^ 2 := by
    rw [hg]; field_simp; rw [hB2, hW2]; ring
  have hg1 : g < 1 := by
    have : 0 < 1 - g ^ 2 := by rw [hg2]; positivity
    nlinarith
  have hgm : -1 < g := by
    have : 0 < 1 - g ^ 2 := by rw [hg2]; positivity
    nlinarith
  have hsq : √(1 - g ^ 2) = p * W / B := by
    rw [hg2, Real.sqrt_sq (by positivity)]
  have h1 := (Real.hasDerivAt_arcsin hgm.ne' hg1.ne).comp z hdg
  have h2 := Real.hasDerivAt_arcsin (x := z) (by linarith [hz.1]) (by linarith [hz.2])
  rw [← hW] at h2
  unfold i5AsF
  refine (((h1.const_mul (q / p)).sub h2).div_const (q ^ 2 - p ^ 2)).congr_deriv ?_
  rw [hsq, ← hB2]
  have key : q ^ 2 - B ^ 2 = (q ^ 2 - p ^ 2) * W ^ 2 := by rw [hB2, hW2]; ring
  calc (q / p * (1 / (p * W / B) * (q * p ^ 2 / (B ^ 2 * B))) - 1 / W) / (q ^ 2 - p ^ 2)
      = (q ^ 2 - B ^ 2) / (W * B ^ 2 * (q ^ 2 - p ^ 2)) := by field_simp
    _ = W / B ^ 2 := by rw [key]; field_simp

theorem continuousOn_i5AsF {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ContinuousOn (i5AsF p q) (Icc (-1) 1) := by
  unfold i5AsF
  refine ((continuousOn_const.mul (Real.continuous_arcsin.comp_continuousOn ?_)).sub
    Real.continuous_arcsin.continuousOn).div_const _
  exact (continuousOn_id.mul continuousOn_const).div (by fun_prop) fun z hz =>
    (Real.sqrt_pos.mpr (i5_asF_den_pos hp hq hz)).ne'

theorem i5AsF_one {p q : ℝ} (hq : 0 < q) :
    i5AsF p q 1 = (q / p * (Real.pi / 2) - Real.pi / 2) / (q ^ 2 - p ^ 2) := by
  unfold i5AsF
  rw [show p ^ 2 + (q ^ 2 - p ^ 2) * 1 ^ 2 = q ^ 2 by ring, Real.sqrt_sq hq.le, one_mul,
    div_self hq.ne', Real.arcsin_one]

theorem i5AsF_neg_one {p q : ℝ} (hq : 0 < q) :
    i5AsF p q (-1) = (q / p * (-(Real.pi / 2)) + Real.pi / 2) / (q ^ 2 - p ^ 2) := by
  unfold i5AsF
  rw [show p ^ 2 + (q ^ 2 - p ^ 2) * (-1) ^ 2 = q ^ 2 by ring, Real.sqrt_sq hq.le, neg_one_mul,
    neg_div, div_self hq.ne', Real.arcsin_neg, Real.arcsin_one]
  ring

/-- **The angular integral** `∫₋₁¹ √(1 - z²)/(p² + (q² - p²) z²) dz = π/(p (p + q))`. -/
theorem i5_integral_asF {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hb : q ^ 2 - p ^ 2 ≠ 0) :
    ∫ z in (-1 : ℝ)..1, √(1 - z ^ 2) / (p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2) =
      Real.pi / (p * (p + q)) := by
  have hc : ContinuousOn (fun z : ℝ => √(1 - z ^ 2) / (p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2))
      (Icc (-1) 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => (i5_asF_den_pos hp hq hz).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) (continuousOn_i5AsF hp hq)
    (fun z hz => hasDerivAt_i5AsF hp hq hb hz) (hc.intervalIntegrable_of_Icc (by norm_num)),
    i5AsF_one hq, i5AsF_neg_one hq]
  have hqp : q - p ≠ 0 := fun h => hb (by
    rw [show q ^ 2 - p ^ 2 = (q - p) * (q + p) by ring, h, zero_mul])
  rw [show q ^ 2 - p ^ 2 = (q - p) * (q + p) by ring]
  have : q + p ≠ 0 := by positivity
  field_simp
  ring

/-! ### The denominators `D_k` -/

/-- `D_k(z) = 1 - k² - 2 i k z`. -/
noncomputable def i5Dk (k z : ℝ) : ℂ := ((1 - k ^ 2 : ℝ) : ℂ) - ((2 * k * z : ℝ) : ℂ) * I

theorem re_i5Dk (k z : ℝ) : (i5Dk k z).re = 1 - k ^ 2 := by
  unfold i5Dk
  simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_zero]

theorem i5Dk_ne_zero {k : ℝ} (hk : k ^ 2 < 1) (z : ℝ) : i5Dk k z ≠ 0 := fun h => by
  have := re_i5Dk k z
  rw [h, zero_re] at this
  linarith

theorem i5Ang_Dk (k : ℝ) : i5Ang (1 - k ^ 2) (2 * k) = 1 / 2 := by
  unfold i5Ang
  rw [show (1 - k ^ 2) ^ 2 + (2 * k) ^ 2 = (1 + k ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  ring

/-- `∫₋₁¹ √(1 - z²)/D_k(z) dz = π/2`. -/
theorem i5_integral_angD {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z = (Real.pi : ℂ) / 2 := by
  have h := i5_integral_ang (P := 1 - k ^ 2) (Q := 2 * k) (by nlinarith [hk.1, hk.2])
    (by linarith [hk.1])
  rw [i5Ang_Dk k] at h
  unfold i5Dk
  rw [h]
  push_cast
  ring

theorem i5_integrableOn_angD {k : ℝ} (hk : k ^ 2 < 1) :
    IntegrableOn (fun z : ℝ => ((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z) (Ioo (-1 : ℝ) 1) := by
  have hc : Continuous fun z : ℝ => ((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z :=
    Continuous.div (by fun_prop) (by unfold i5Dk; fun_prop) fun z => i5Dk_ne_zero hk z
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-! ### `∫ √(1 - z²) log D_k / D_k` -/

theorem hasDerivAt_i5Dk (j z : ℝ) :
    HasDerivAt (fun j : ℝ => i5Dk j z) (-2 * (j : ℂ) - 2 * ((z : ℂ) * I)) j := by
  have e : (fun j : ℝ => i5Dk j z) =
      fun j : ℝ => (fun w : ℂ => 1 - w ^ 2 - 2 * w * ((z : ℂ) * I)) (j : ℂ) := by
    funext j; unfold i5Dk; push_cast; ring
  rw [e]
  refine HasDerivAt.comp_ofReal (e := fun w : ℂ => 1 - w ^ 2 - 2 * w * ((z : ℂ) * I)) ?_
  have h := ((hasDerivAt_pow 2 (j : ℂ)).const_sub 1).sub
    (((hasDerivAt_id (j : ℂ)).const_mul 2).mul_const ((z : ℂ) * I))
  refine h.congr_deriv ?_
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  push_cast
  ring

/-- `log D_k(z) = ∫₀ᵏ (-2j - 2iz)/D_j(z) dj`. -/
theorem i5_log_Dk_eq {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) (z : ℝ) :
    log (i5Dk k z) = ∫ j in (0 : ℝ)..k, (-2 * (j : ℂ) - 2 * ((z : ℂ) * I)) / i5Dk j z := by
  have hj : ∀ j ∈ uIcc 0 k, j ^ 2 < 1 := fun j hj => by
    rw [uIcc_of_le hk.1.le] at hj
    nlinarith [hj.1, hj.2, hk.2]
  have hd : ∀ j ∈ uIcc 0 k, HasDerivAt (fun j : ℝ => log (i5Dk j z))
      ((-2 * (j : ℂ) - 2 * ((z : ℂ) * I)) / i5Dk j z) j := fun j h =>
    HasDerivAt.clog_real (hasDerivAt_i5Dk j z) (mem_slitPlane_iff.mpr (Or.inl (by
      rw [re_i5Dk]; linarith [hj j h])))
  have hc : ContinuousOn (fun j : ℝ => (-2 * (j : ℂ) - 2 * ((z : ℂ) * I)) / i5Dk j z)
      (uIcc 0 k) :=
    ContinuousOn.div (by fun_prop) (by unfold i5Dk; fun_prop) fun j h => i5Dk_ne_zero (hj j h) z
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have h0 : i5Dk 0 z = 1 := by unfold i5Dk; simp
  rw [h0, log_one, sub_zero]

/-- The partial fractions of `(-2j - 2u)/(D_j D_k)`, `D_j = 1 - j² - 2ju`. -/
theorem i5_pf_Dk {j k u : ℂ} (hj : j ≠ 0) (hkj : k - j ≠ 0) (h1 : 1 + j * k ≠ 0)
    (hDj : 1 - j ^ 2 - 2 * j * u ≠ 0) (hDk : 1 - k ^ 2 - 2 * k * u ≠ 0) :
    (-2 * j - 2 * u) / (1 - j ^ 2 - 2 * j * u) / (1 - k ^ 2 - 2 * k * u) =
      1 / j * (1 / (1 - k ^ 2 - 2 * k * u)) -
        (1 + j ^ 2) * k / (j * (k - j) * (1 + j * k)) * (1 / (1 - k ^ 2 - 2 * k * u)) +
        (1 + j ^ 2) / ((k - j) * (1 + j * k)) * (1 / (1 - j ^ 2 - 2 * j * u)) := by
  have key : (-2 * j - 2 * u) * (j * (k - j) * (1 + j * k)) =
      ((k - j) * (1 + j * k) - (1 + j ^ 2) * k) * (1 - j ^ 2 - 2 * j * u) +
        (1 + j ^ 2) * j * (1 - k ^ 2 - 2 * k * u) := by ring
  generalize 1 - j ^ 2 - 2 * j * u = Dj at hDj key ⊢
  generalize 1 - k ^ 2 - 2 * k * u = Dk at hDk key ⊢
  field_simp
  linear_combination key

theorem i5Dk_eq (k z : ℝ) : i5Dk k z = 1 - (k : ℂ) ^ 2 - 2 * (k : ℂ) * ((z : ℂ) * I) := by
  unfold i5Dk; push_cast; ring

/-- The inner angular integral: `∫₋₁¹ √(1 - z²) (-2j - 2iz)/(D_j D_k) dz = π/2 (k-j)/(1+jk)`. -/
theorem i5_integral_angD_pf {j k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) (hj : j ∈ Ioo (0 : ℝ) 1)
    (hjk : j ≠ k) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) : ℝ) : ℂ) *
        ((-2 * (j : ℂ) - 2 * ((z : ℂ) * I)) / i5Dk j z) / i5Dk k z =
      ((Real.pi / 2 * ((k - j) / (1 + j * k)) : ℝ) : ℂ) := by
  have hj0 : 0 < j := hj.1
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hj2 : j ^ 2 < 1 := by nlinarith [hj.1, hj.2]
  have hjc : (j : ℂ) ≠ 0 := ofReal_ne_zero.mpr hj0.ne'
  have hkjc : (k : ℂ) - j ≠ 0 := by
    rw [← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hjk.symm)
  have h1c : 1 + (j : ℂ) * k ≠ 0 := by
    rw [show 1 + (j : ℂ) * k = ((1 + j * k : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr (ne_of_gt (by nlinarith [hk.1]))
  have hpt : ∀ z ∈ Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) : ℝ) : ℂ) *
      ((-2 * (j : ℂ) - 2 * ((z : ℂ) * I)) / i5Dk j z) / i5Dk k z =
        1 / j * (((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z) -
        (1 + j ^ 2) * k / (j * (k - j) * (1 + j * k)) * (((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z) +
        (1 + j ^ 2) / ((k - j) * (1 + j * k)) * (((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk j z) :=
    fun z _ => by
      have hDj := i5Dk_ne_zero hj2 z
      have hDk := i5Dk_ne_zero hk2 z
      rw [i5Dk_eq] at hDj hDk ⊢
      rw [i5Dk_eq]
      have h := i5_pf_Dk hjc hkjc h1c hDj hDk
      rw [mul_div_assoc, h]
      ring
  have hI := i5_integrableOn_angD hk2
  have hIj := i5_integrableOn_angD hj2
  have hAB : IntegrableOn (fun z : ℝ => 1 / (j : ℂ) * (((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z) -
      (1 + (j : ℂ) ^ 2) * k / (j * (k - j) * (1 + j * k)) *
        (((√(1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z)) (Ioo (-1 : ℝ) 1) :=
    (hI.const_mul _).sub (hI.const_mul _)
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_add hAB (hIj.const_mul _),
    integral_sub (hI.const_mul _) (hI.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, i5_integral_angD hk, i5_integral_angD hj]
  push_cast
  field_simp
  ring

/-- `∫₀^{k'} (k - j)/(1 + jk) dj = -k'/k + (1 + k²)/k² log (1 + k k')`. -/
theorem i5_integral_pf_j {k k' : ℝ} (hk : 0 < k) (hk' : 0 < k') :
    ∫ j in Ioo 0 k', Real.pi / 2 * ((k - j) / (1 + j * k)) =
      Real.pi / 2 * (-k' / k + (1 + k ^ 2) / k ^ 2 * Real.log (1 + k * k')) := by
  have hpos : ∀ j ∈ Icc 0 k', 0 < 1 + j * k := fun j hj => by nlinarith [hj.1]
  have hd : ∀ j ∈ Ioo 0 k', HasDerivAt
      (fun j => Real.pi / 2 * (-j / k + (1 + k ^ 2) / k ^ 2 * Real.log (1 + j * k)))
      (Real.pi / 2 * ((k - j) / (1 + j * k))) j := fun j hj => by
    have h1 := hpos j (Ioo_subset_Icc_self hj)
    have hl : HasDerivAt (fun j => 1 + j * k) k j := by
      simpa using ((hasDerivAt_id j).mul_const k).const_add 1
    refine ((((hasDerivAt_id j).neg.div_const k).add
      ((hl.log h1.ne').const_mul ((1 + k ^ 2) / k ^ 2))).const_mul (Real.pi / 2)).congr_deriv ?_
    have h1' : 1 + k * j ≠ 0 := by rw [mul_comm]; exact h1.ne'
    field_simp
    ring
  have hc : ContinuousOn
      (fun j => Real.pi / 2 * (-j / k + (1 + k ^ 2) / k ^ 2 * Real.log (1 + j * k))) (Icc 0 k') :=
    continuousOn_const.mul ((continuousOn_id.neg.div_const k).add (continuousOn_const.mul
      (ContinuousOn.log (by fun_prop) fun j hj => (hpos j hj).ne')))
  have hi : IntervalIntegrable (fun j => Real.pi / 2 * ((k - j) / (1 + j * k))) volume 0 k' :=
    ContinuousOn.intervalIntegrable_of_Icc hk'.le (continuousOn_const.mul
      (ContinuousOn.div (by fun_prop) (by fun_prop) fun j hj => (hpos j hj).ne'))
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hk'.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hk'.le hc hd hi]
  simp only [zero_mul, add_zero, Real.log_one, mul_zero, neg_zero, zero_div]
  rw [show 1 + k' * k = 1 + k * k' by ring]
  ring

/-- **The mixed angular integral**
`∫₋₁¹ √(1 - z²) log D_{k'}(z) / D_k(z) dz = π/2 · (-k'/k + (1 + k²)/k² · log (1 + k k'))`. -/
theorem i5_integral_angLogDD {k k' : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) (hk' : k' ∈ Ioo (0 : ℝ) 1) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5Dk k' z) / i5Dk k z =
      ((Real.pi / 2 * (-k' / k + (1 + k ^ 2) / k ^ 2 * Real.log (1 + k * k')) : ℝ) : ℂ) := by
  set F : ℝ → ℝ → ℂ := fun z j => ((√(1 - z ^ 2) : ℝ) : ℂ) *
    ((-2 * (j : ℂ) - 2 * ((z : ℂ) * I)) / i5Dk j z) / i5Dk k z with hF
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hin : ∀ z : ℝ, ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5Dk k' z) / i5Dk k z =
      ∫ j in Ioo 0 k', F z j := fun z => by
    rw [i5_log_Dk_eq hk' z, intervalIntegral.integral_of_le hk'.1.le,
      integral_Ioc_eq_integral_Ioo, ← integral_const_mul, ← integral_div]
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo 0 k'))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc : ContinuousOn (Function.uncurry F) (Icc (-1 : ℝ) 1 ×ˢ Icc 0 k') := by
      have hj : ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 k', p.2 ^ 2 < 1 := fun p hp => by
        nlinarith [hp.2.1, hp.2.2, hk'.2]
      refine ContinuousOn.div (ContinuousOn.mul (by fun_prop) (ContinuousOn.div (by fun_prop)
        (by unfold i5Dk; fun_prop) fun p hp => i5Dk_ne_zero (hj p hp) p.1))
        (by unfold i5Dk; fun_prop) fun p _ => i5Dk_ne_zero hk2 p.1
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hne : ∀ᵐ j ∂(volume : Measure ℝ), j ∉ ({k} : Set ℝ) :=
    (countable_singleton k).ae_notMem volume
  simp_rw [hin]
  rw [integral_integral_swap hint, setIntegral_congr_ae measurableSet_Ioo (by
      filter_upwards [hne] with j hj hj'
      exact i5_integral_angD_pf hk ⟨hj'.1, hj'.2.trans hk'.2⟩ hj),
    integral_complex_ofReal, i5_integral_pf_j hk.1 hk'.1]

/-- **The angular integral** `∫₋₁¹ √(1 - z²) log D_k(z) / D_k(z) dz`. -/
theorem i5_integral_angLogD {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) : ℝ) : ℂ) * log (i5Dk k z) / i5Dk k z =
      ((Real.pi / 2 * (-1 + (1 + k ^ 2) / k ^ 2 * Real.log (1 + k ^ 2)) : ℝ) : ℂ) := by
  rw [i5_integral_angLogDD hk hk, neg_div, div_self hk.1.ne', sq]

/-! ### `∫ √(1 - z²) log (1 - z²) / D_k` -/

theorem i5_sqrt_log_eq (z : ℝ) :
    √(1 - z ^ 2) * Real.log (1 - z ^ 2) = 2 * (√(1 - z ^ 2) * Real.log √(1 - z ^ 2)) := by
  rcases le_or_gt 0 (1 - z ^ 2) with h | h
  · rw [Real.log_sqrt h]; ring
  · rw [Real.sqrt_eq_zero'.mpr h.le]; simp

/-- `√(1 - z²) log (1 - z²)` is continuous on `ℝ` (it vanishes at `z = ±1`). -/
theorem continuous_i5SqLog : Continuous fun z : ℝ => √(1 - z ^ 2) * Real.log (1 - z ^ 2) := by
  rw [show (fun z : ℝ => √(1 - z ^ 2) * Real.log (1 - z ^ 2)) =
    fun z => 2 * ((fun u => u * Real.log u) (√(1 - z ^ 2))) from funext i5_sqrt_log_eq]
  exact continuous_const.mul (Real.continuous_mul_log.comp (by fun_prop))

/-- `log (1 - z²) = -∫₀¹ 2r z²/(1 - (1 - r²) z²) dr`. -/
theorem i5_log_one_sub_sq_eq {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    Real.log (1 - z ^ 2) = -∫ r in Ioo (0 : ℝ) 1, 2 * r * z ^ 2 / (1 - (1 - r ^ 2) * z ^ 2) := by
  have hw : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hpos : ∀ r : ℝ, 0 < 1 - (1 - r ^ 2) * z ^ 2 := fun r => by
    nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg z)]
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun r => Real.log (1 - (1 - r ^ 2) * z ^ 2))
      (2 * r * z ^ 2 / (1 - (1 - r ^ 2) * z ^ 2)) r := fun r _ => by
    have h := (((hasDerivAt_pow 2 r).const_sub 1).mul_const (z ^ 2)).const_sub 1
    refine (h.log (hpos r).ne').congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have hc : ContinuousOn (fun r => Real.log (1 - (1 - r ^ 2) * z ^ 2)) (Icc 0 1) :=
    ContinuousOn.log (by fun_prop) fun r _ => (hpos r).ne'
  have hi : IntervalIntegrable (fun r => 2 * r * z ^ 2 / (1 - (1 - r ^ 2) * z ^ 2)) volume 0 1 :=
    (Continuous.div (by fun_prop) (by fun_prop) fun r => (hpos r).ne').intervalIntegrable _ _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hi]
  simp

/-- The integrand of the double integral for `∫ √(1 - z²) log (1 - z²) / D_k`. -/
noncomputable def i5GW (k z r : ℝ) : ℝ :=
  √(1 - z ^ 2) * ((1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2)) *
    (2 * r * z ^ 2 / (1 - (1 - r ^ 2) * z ^ 2))

theorem norm_i5GW_le {k z r : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) : ‖i5GW k z r‖ ≤ 1 / (1 - k ^ 2) := by
  have hd : 0 < 1 - k ^ 2 := by nlinarith [hk.1, hk.2]
  have hw : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hz1 : z ^ 2 ≤ 1 := by linarith
  have hr0 := hr.1
  set W := √(1 - z ^ 2) with hW
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hW2 : W ^ 2 = 1 - z ^ 2 := Real.sq_sqrt hw.le
  have hq : 0 < 1 - (1 - r ^ 2) * z ^ 2 := by nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg z)]
  have hc0 : 0 ≤ (1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2) := by positivity
  have hc1 : (1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2) ≤ 1 / (1 - k ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hd]
    nlinarith [mul_nonneg (sq_nonneg (2 * k)) (sq_nonneg z)]
  have hh0 : 0 ≤ W * (2 * r * z ^ 2 / (1 - (1 - r ^ 2) * z ^ 2)) := by positivity
  have hh1 : W * (2 * r * z ^ 2 / (1 - (1 - r ^ 2) * z ^ 2)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hq]
    nlinarith [sq_nonneg (W - r * z ^ 2), mul_le_mul_of_nonneg_left hz1
      (mul_nonneg (sq_nonneg r) (sq_nonneg z))]
  have he : i5GW k z r = (1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2) *
      (W * (2 * r * z ^ 2 / (1 - (1 - r ^ 2) * z ^ 2))) := by unfold i5GW; ring
  rw [he, Real.norm_of_nonneg (mul_nonneg hc0 hh0)]
  calc _ ≤ (1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hh1 hc0
    _ ≤ _ := by rw [mul_one]; exact hc1

/-- The inner angular integral of `i5GW`. -/
theorem i5_integral_i5GW {k r : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∫ z in Ioo (-1 : ℝ) 1, i5GW k z r =
      Real.pi * (r * (1 - k ^ 2) / ((1 + r) * (1 + k ^ 2 + r * (1 - k ^ 2)))) := by
  obtain ⟨k0, k1⟩ := hk
  obtain ⟨r0, r1⟩ := hr
  have hd : 0 < 1 - k ^ 2 := by nlinarith
  have hb1 : r ^ 2 - 1 ^ 2 ≠ 0 := by nlinarith
  have hb2 : (1 + k ^ 2) ^ 2 - (1 - k ^ 2) ^ 2 ≠ 0 := by nlinarith [pow_pos k0 2]
  have hA : 0 < (1 - r ^ 2) * (1 - k ^ 2) ^ 2 + (2 * k) ^ 2 := by
    have : 0 < 1 - r ^ 2 := by nlinarith
    positivity
  set C₁ := 2 * r * (1 - k ^ 2) / ((1 - r ^ 2) * (1 - k ^ 2) ^ 2 + (2 * k) ^ 2) with hC₁
  have hpt : ∀ z ∈ uIcc (-1 : ℝ) 1, i5GW k z r =
      C₁ * (√(1 - z ^ 2) / (1 ^ 2 + (r ^ 2 - 1 ^ 2) * z ^ 2)) -
        C₁ * (1 - k ^ 2) ^ 2 * (√(1 - z ^ 2) /
          ((1 - k ^ 2) ^ 2 + ((1 + k ^ 2) ^ 2 - (1 - k ^ 2) ^ 2) * z ^ 2)) := fun z hz => by
    rw [uIcc_of_le (by norm_num)] at hz
    have h1 := i5_asF_den_pos (p := 1) (q := r) one_pos r0 hz
    have h2 := i5_asF_den_pos (p := 1 - k ^ 2) (q := 1 + k ^ 2) hd (by positivity) hz
    have h3 : 1 - (1 - r ^ 2) * z ^ 2 = 1 ^ 2 + (r ^ 2 - 1 ^ 2) * z ^ 2 := by ring
    have h4 : (1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2 =
        (1 - k ^ 2) ^ 2 + ((1 + k ^ 2) ^ 2 - (1 - k ^ 2) ^ 2) * z ^ 2 := by ring
    unfold i5GW
    rw [hC₁, h3, h4]
    set E₁ := 1 ^ 2 + (r ^ 2 - 1 ^ 2) * z ^ 2 with hE₁
    set E₂ := (1 - k ^ 2) ^ 2 + ((1 + k ^ 2) ^ 2 - (1 - k ^ 2) ^ 2) * z ^ 2 with hE₂
    set E₃ := (1 - r ^ 2) * (1 - k ^ 2) ^ 2 + (2 * k) ^ 2 with hE₃
    have n1 := h1.ne'
    have n2 := h2.ne'
    have n3 := hA.ne'
    clear_value E₁ E₂ E₃
    field_simp
    subst hE₁ hE₂ hE₃
    ring
  have hi : ∀ p q : ℝ, 0 < p → 0 < q → IntervalIntegrable
      (fun z : ℝ => √(1 - z ^ 2) / (p ^ 2 + (q ^ 2 - p ^ 2) * z ^ 2)) volume (-1) 1 :=
    fun p q hp hq => ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => (i5_asF_den_pos hp hq hz).ne')
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub ((hi 1 r one_pos r0).const_mul _)
      ((hi _ _ hd (by positivity)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    i5_integral_asF one_pos r0 hb1, i5_integral_asF hd (by positivity) hb2, hC₁]
  have hB : 0 < 1 + k ^ 2 + r * (1 - k ^ 2) := by positivity
  set E₃ := (1 - r ^ 2) * (1 - k ^ 2) ^ 2 + (2 * k) ^ 2 with hE₃
  set B := 1 + k ^ 2 + r * (1 - k ^ 2) with hB'
  set D := 1 - k ^ 2 with hD
  have n1 := hA.ne'
  have n2 := hB.ne'
  have n3 := hd.ne'
  have n4 : (1 : ℝ) + r ≠ 0 := by positivity
  have n5 : D + (1 + k ^ 2) ≠ 0 := by rw [hD]; ring_nf; norm_num
  clear_value E₃ B D
  field_simp
  subst hE₃ hB' hD
  ring

/-- `∫₀¹ r (1 - k²)/((1 + r)(1 + k² + r (1 - k²))) dr = log 2 - (1 + k²)/(2k²) log (1 + k²)`. -/
theorem i5_integral_GW_r {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) :
    ∫ r in Ioo (0 : ℝ) 1, Real.pi * (r * (1 - k ^ 2) / ((1 + r) * (1 + k ^ 2 + r * (1 - k ^ 2)))) =
      Real.pi * (Real.log 2 - (1 + k ^ 2) / (2 * k ^ 2) * Real.log (1 + k ^ 2)) := by
  obtain ⟨k0, k1⟩ := hk
  have hd : 0 < 1 - k ^ 2 := by nlinarith
  have hpos : ∀ r ∈ Icc (0 : ℝ) 1, 0 < 1 + r ∧ 0 < 1 + k ^ 2 + r * (1 - k ^ 2) :=
    fun r hr => ⟨by linarith [hr.1], by nlinarith [hr.1]⟩
  set H : ℝ → ℝ := fun r => Real.pi * ((-(1 - k ^ 2) * Real.log (1 + r) +
    (1 + k ^ 2) * Real.log (1 + k ^ 2 + r * (1 - k ^ 2))) / (2 * k ^ 2)) with hH
  have hdH : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt H
      (Real.pi * (r * (1 - k ^ 2) / ((1 + r) * (1 + k ^ 2 + r * (1 - k ^ 2))))) r := fun r hr => by
    obtain ⟨p1, p2⟩ := hpos r (Ioo_subset_Icc_self hr)
    have d1 : HasDerivAt (fun r : ℝ => 1 + r) 1 r := by
      simpa using (hasDerivAt_id r).const_add 1
    have d2 : HasDerivAt (fun r : ℝ => 1 + k ^ 2 + r * (1 - k ^ 2)) (1 - k ^ 2) r := by
      simpa using ((hasDerivAt_id r).mul_const (1 - k ^ 2)).const_add (1 + k ^ 2)
    refine ((((d1.log p1.ne').const_mul (-(1 - k ^ 2))).add
      ((d2.log p2.ne').const_mul (1 + k ^ 2))).div_const (2 * k ^ 2) |>.const_mul
        Real.pi).congr_deriv ?_
    have : k ^ 2 ≠ 0 := by positivity
    set B := 1 + k ^ 2 + r * (1 - k ^ 2) with hB
    have n1 := p1.ne'
    have n2 := p2.ne'
    clear_value B
    field_simp
    subst hB
    ring
  have hc : ContinuousOn H (Icc 0 1) :=
    continuousOn_const.mul (((continuousOn_const.mul (ContinuousOn.log (by fun_prop)
      fun r hr => (hpos r hr).1.ne')).add (continuousOn_const.mul (ContinuousOn.log
        (by fun_prop) fun r hr => (hpos r hr).2.ne'))).div_const _)
  have hi : IntervalIntegrable (fun r => Real.pi *
      (r * (1 - k ^ 2) / ((1 + r) * (1 + k ^ 2 + r * (1 - k ^ 2))))) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_const.mul
      (ContinuousOn.div (by fun_prop) (by fun_prop) fun r hr =>
        (mul_pos (hpos r hr).1 (hpos r hr).2).ne'))
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hdH hi, hH]
  simp only [add_zero, zero_mul, Real.log_one, mul_zero, one_mul]
  rw [show 1 + k ^ 2 + (1 - k ^ 2) = 2 by ring, show (1 : ℝ) + 1 = 2 by norm_num]
  have : k ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The real form: `∫₋₁¹ √(1 - z²) log (1 - z²) (1 - k²)/((1 - k²)² + 4k² z²) dz`. -/
theorem i5_integral_angLogW_re {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) :
    ∫ z in Ioo (-1 : ℝ) 1, √(1 - z ^ 2) * Real.log (1 - z ^ 2) *
        ((1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2)) =
      Real.pi / 2 * (-2 * Real.log 2 + (1 + k ^ 2) / k ^ 2 * Real.log (1 + k ^ 2)) := by
  have hin : ∀ z ∈ Ioo (-1 : ℝ) 1, √(1 - z ^ 2) * Real.log (1 - z ^ 2) *
      ((1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2)) =
        -∫ r in Ioo (0 : ℝ) 1, i5GW k z r := fun z hz => by
    unfold i5GW
    rw [integral_const_mul, i5_log_one_sub_sq_eq hz]
    ring
  have hint : Integrable (Function.uncurry (i5GW k))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo 0 1))) := by
    refine Integrable.mono' (integrable_const (1 / (1 - k ^ 2)))
      (show Measurable (Function.uncurry (i5GW k)) by
        unfold i5GW Function.uncurry; fun_prop).aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact norm_i5GW_le hk hp.1 hp.2
  rw [setIntegral_congr_fun measurableSet_Ioo hin, integral_neg, integral_integral_swap hint,
    setIntegral_congr_fun measurableSet_Ioo fun r hr => i5_integral_i5GW hk hr,
    i5_integral_GW_r hk]
  have : k ^ 2 ≠ 0 := by have := hk.1; positivity
  field_simp
  ring

theorem i5_angLogW_even {k z : ℝ} (hk : k ^ 2 < 1) (e : ℝ) :
    (e : ℂ) / i5Dk k z + (e : ℂ) / i5Dk k (-z) =
      ((2 * (e * ((1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2)))) : ℝ) := by
  have hP : 0 < 1 - k ^ 2 := by linarith
  have h1 := i5_ang_ne (Q := 2 * k) (z := z) hP
  have h2 := i5_ang_ne (Q := 2 * k) (z := -z) hP
  have hm := i5_ang_mul (1 - k ^ 2) (2 * k) z
  have hd : (0 : ℝ) < (1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2 := by positivity
  unfold i5Dk
  rw [div_add_div _ _ h1 h2, hm]
  push_cast
  field_simp
  ring

/-- **The angular integral** `∫₋₁¹ √(1 - z²) log (1 - z²) / D_k(z) dz`. -/
theorem i5_integral_angLogW {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z =
      ((Real.pi / 2 * (-2 * Real.log 2 + (1 + k ^ 2) / k ^ 2 * Real.log (1 + k ^ 2)) : ℝ) :
        ℂ) := by
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  set f := fun z : ℝ => ((√(1 - z ^ 2) * Real.log (1 - z ^ 2) : ℝ) : ℂ) / i5Dk k z with hf
  have hfc : Continuous f := Continuous.div (continuous_ofReal.comp continuous_i5SqLog)
    (by unfold i5Dk; fun_prop) fun z => i5Dk_ne_zero hk2 z
  have hneg : ∫ z in (-1 : ℝ)..1, f (-z) = ∫ z in (-1 : ℝ)..1, f z := by
    rw [intervalIntegral.integral_comp_neg]; norm_num
  set R := Real.pi / 2 * (-2 * Real.log 2 + (1 + k ^ 2) / k ^ 2 * Real.log (1 + k ^ 2))
  have hsum : (∫ z in (-1 : ℝ)..1, f z) + ∫ z in (-1 : ℝ)..1, f (-z) = ((2 * R : ℝ) : ℂ) := by
    have hi2 : IntervalIntegrable (fun z => f (-z)) volume (-1) 1 :=
      (hfc.comp continuous_neg).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add (hfc.intervalIntegrable _ _) hi2]
    simp only [hf, neg_sq]
    rw [intervalIntegral.integral_congr (g := fun z : ℝ => ((2 * (√(1 - z ^ 2) *
      Real.log (1 - z ^ 2) * ((1 - k ^ 2) / ((1 - k ^ 2) ^ 2 + (2 * k) ^ 2 * z ^ 2))) : ℝ) :
        ℂ)) fun z _ => i5_angLogW_even hk2 _, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo, i5_integral_angLogW_re hk]
  rw [hneg] at hsum
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  have h2 : (2 : ℂ) * ∫ z in (-1 : ℝ)..1, f z = 2 * ((R : ℝ) : ℂ) := by
    rw [two_mul, hsum]; push_cast; ring
  exact mul_left_cancel₀ two_ne_zero h2

end QED.ThreeLoopD
