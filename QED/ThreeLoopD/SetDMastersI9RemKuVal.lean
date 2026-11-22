/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemKuPsi
public import QED.ThreeLoopD.SetDMastersI9RemA2Asm
public import QED.Polylog.HPLValues
public import QED.Polylog.HPLValues3
public import QED.Polylog.HPLValuesAlt4
public import QED.Polylog.HPLValuesTrailing

/-!
# Set (d), master `I₉`: the value of `K_u` and the expansion of `Rem`

With the antiderivative `Ψ` of `QED.ThreeLoopD.hasDerivAt_i9KuPsi`, `K_u = Ψ(1⁻) - Ψ(0⁺)`.

* At `w → 0⁺` every term `ρ(w) H(v; w)` tends to `0`: either `ρ` has no pole and `H(v; w) → 0`
  (or `v = 0` and `ρ(w) = O(w)`), or the word is `a · v'` with `a ≠ 0` and `v'` not all zeros,
  so `|H(a · v'; w)| ≤ C w^(3/2)`.
* At `w → 1⁻` the words starting with `1` carry a coefficient vanishing at `1`, and
  `(1 - w) H(v; w) → 0`; the other words are continuous at `1`, and their values are the
  alternating multiple zeta values of weight at most four.

The result is `K_u = (9π² + 12 ζ(3) + 17π⁴/20 - 24π² log 2)/4`, the last input of
`QED.ThreeLoopD.hasTruncLaurent_i9Rem_of_Ku`.

## Main results

* `QED.ThreeLoopD.integral_log_one_sub_mul_i9A1Dens_val`: the value of `K_u`.
* `QED.ThreeLoopD.hasTruncLaurent_i9Rem`: `HasTruncLaurent i9Rem i9RemLaurent 3`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The value `(9π² + 12 ζ(3) + 17π⁴/20 - 24π² log 2)/4` of `K_u`. -/
noncomputable def i9KuVal : ℝ :=
  (9 * π ^ 2 + 12 * zeta3 + 17 / 20 * π ^ 4 - 24 * π ^ 2 * Real.log 2) / 4

/-! ### The terms at `0⁺` -/

theorem i9KuBnd_cons {l : Letter} (hl : l ≠ zero) {v : List Letter} {r : ℝ}
    (hv : I9A2Bnd (hpl v) r) (hr : -1 < r) : I9A2Bnd (hpl (l :: v)) (r + 1) := by
  obtain ⟨C, hC⟩ := hv
  refine ⟨2 * |C| / (r + 1), fun x hx => ?_⟩
  rw [hpl_cons_of_ne_zero hl]
  have h := abs_integral_le_of_le_rpow (g := fun t => l.kernel t * hpl v t) (K := 2 * |C|)
    (r := r) hx.1.le hr fun t ht => by
      have ht1 : t ∈ Ioc (0 : ℝ) (1 / 2) := ⟨ht.1, ht.2.trans hx.2⟩
      have hk := abs_kernel_le hl (b := 1 / 2) (by norm_num) ht.1.le ht1.2
      rw [abs_mul]
      calc |l.kernel t| * |hpl v t| ≤ 2 * (|C| * t ^ r) := by
            refine mul_le_mul (hk.trans (by norm_num)) ((hC t ht1).trans
              (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity [ht.1])))
              (abs_nonneg _) (by norm_num)
        _ = 2 * |C| * t ^ r := by ring
  calc _ ≤ 2 * |C| * (x ^ (r + 1) / (r + 1)) := h
    _ = 2 * |C| / (r + 1) * x ^ (r + 1) := by ring

theorem i9Ku_tendsto_poly (b c d : ℝ) {s : Set ℝ} (y : ℝ) :
    Tendsto (fun x : ℝ => b + c * x + d * x ^ 2) (𝓝[s] y) (𝓝 (b + c * y + d * y ^ 2)) :=
  ((by fun_prop : Continuous fun x : ℝ => b + c * x + d * x ^ 2).tendsto y).mono_left
    nhdsWithin_le_nhds

theorem tendsto_i9KuRat_zero (c d : ℝ) : Tendsto (i9KuRat 0 0 c d) (𝓝[>] 0) (𝓝 0) := by
  have h := i9Ku_tendsto_poly 0 c d (s := Ioi 0) 0
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp [i9KuRat]

theorem tendsto_i9KuRat_mul_hpl_zero (b c d : ℝ) {v : List Letter} (hv : ¬AllZero v) :
    Tendsto (fun x => i9KuRat 0 b c d x * hpl v x) (𝓝[>] 0) (𝓝 0) := by
  have h := (i9Ku_tendsto_poly b c d (s := Ioi 0) 0).mul (tendsto_hpl_zero hv)
  rw [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp [i9KuRat]

theorem tendsto_i9KuRat_mul_hpl_zero_zero (c d : ℝ) :
    Tendsto (fun x => i9KuRat 0 0 c d x * hpl [zero] x) (𝓝[>] 0) (𝓝 0) := by
  have h := (i9Ku_tendsto_poly c d 0 (s := Ioi 0) 0).mul tendsto_mul_log_zero
  rw [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [i9KuRat, hpl_zero]
  ring

theorem tendsto_i9KuRat_mul_hpl_zero_cons (a b c d : ℝ) {l : Letter} {v : List Letter}
    (hl : l ≠ zero) (hv : ¬AllZero v) :
    Tendsto (fun x => i9KuRat a b c d x * hpl (l :: v) x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := abs_hpl_le_sqrt hv (b := 1 / 2) (by norm_num)
  have hB : I9A2Bnd (hpl (l :: v)) (1 / 2 + 1) :=
    i9KuBnd_cons hl ⟨C, fun t ht => hC t ht⟩ (by norm_num)
  have hq := tendsto_div_pow_of_i9A2Bnd hB 1 (by norm_num)
  have hp : Tendsto (fun x : ℝ => a + b * x + c * x ^ 2 + d * x ^ 3) (𝓝[>] 0)
      (𝓝 (a + b * 0 + c * 0 ^ 2 + d * 0 ^ 3)) :=
    ((by fun_prop : Continuous fun x : ℝ => a + b * x + c * x ^ 2 + d * x ^ 3).tendsto
      0).mono_left nhdsWithin_le_nhds
  have h := hp.mul hq
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  simp only [i9KuRat, pow_one]
  field_simp

/-! ### The terms at `1⁻` -/

theorem i9Ku_continuousAt_rat (a b c d : ℝ) : ContinuousAt (i9KuRat a b c d) 1 := by
  unfold i9KuRat
  exact ((((continuousAt_const.div continuousAt_id one_ne_zero).add continuousAt_const).add
    (continuousAt_const.mul continuousAt_id)).add (continuousAt_const.mul
    (continuousAt_id.pow 2)))

theorem tendsto_i9KuRat_one (a b c d : ℝ) :
    Tendsto (i9KuRat a b c d) (𝓝[<] 1) (𝓝 (i9KuRat a b c d 1)) :=
  (i9Ku_continuousAt_rat a b c d).tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_i9KuRat_mul_hpl_one (a b c d : ℝ) {l : Letter} {v : List Letter}
    (hl : l ≠ one) :
    Tendsto (fun x => i9KuRat a b c d x * hpl (l :: v) x) (𝓝[<] 1)
      (𝓝 (i9KuRat a b c d 1 * hpl (l :: v) 1)) :=
  (tendsto_i9KuRat_one a b c d).mul (tendsto_hpl_one hl v)

theorem tendsto_i9KuRat_mul_hpl_one_of (a b c d : ℝ) (v : List Letter)
    (h : a + b + c + d = 0) :
    Tendsto (fun x => i9KuRat a b c d x * hpl v x) (𝓝[<] 1) (𝓝 0) := by
  have hQ : Tendsto (fun x : ℝ => a / x - c - d * (1 + x)) (𝓝[<] 1)
      (𝓝 (a / 1 - c - d * (1 + 1))) :=
    (((continuousAt_const.div continuousAt_id one_ne_zero).sub continuousAt_const).sub
      (continuousAt_const.mul (continuousAt_const.add continuousAt_id))).tendsto.mono_left
      nhdsWithin_le_nhds
  have h2 := hQ.mul (i9A2_tendsto_one_sub_mul_hpl v)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx0 : x ≠ 0 := hx.1.ne'
  have hb : b = -a - c - d := by linarith
  simp only [i9KuRat, hb]
  field_simp
  ring

/-! ### The limits of `Ψ` -/

theorem tendsto_i9KuPsi_zero : Tendsto i9KuPsi (𝓝[>] 0) (𝓝 0) := by
  have e0 := (tendsto_i9KuRat_zero (9 * (π ^ 2 / 6)) (9 / 2 * (π ^ 2 / 6)))
  have e1 := e0.add
      (tendsto_i9KuRat_mul_hpl_zero_zero (21) (0))
  have e2 := e1.add
      (tendsto_i9KuRat_mul_hpl_zero (-21 + -3 * (π ^ 2 / 6)) (21) (3 * (π ^ 2 / 6))
        (v := [one]) (by decide))
  have e3 := e2.add
      (tendsto_i9KuRat_mul_hpl_zero (-33 / 2) (-21) (-9 / 2)
        (v := [negOne, zero]) (by decide))
  have e4 := e3.add
      (tendsto_i9KuRat_mul_hpl_zero (-6 * (π ^ 2 / 6)) (-12) (-9)
        (v := [zero, one]) (by decide))
  have e5 := e4.add
      (tendsto_i9KuRat_mul_hpl_zero (-9 / 2) (9) (-9 / 2)
        (v := [one, zero]) (by decide))
  have e6 := e5.add
      (tendsto_i9KuRat_mul_hpl_zero (-9) (18) (-9)
        (v := [one, one]) (by decide))
  have e7 := e6.add
      (tendsto_i9KuRat_mul_hpl_zero_cons (-6) (-9) (-6) (-3)
        (l := negOne) (v := [zero, one]) (by decide) (by decide))
  have e8 := e7.add
      (tendsto_i9KuRat_mul_hpl_zero_cons (-6) (-9) (-6) (-3)
        (l := negOne) (v := [one, zero]) (by decide) (by decide))
  have e9 := e8.add
      (tendsto_i9KuRat_mul_hpl_zero (-24) (0) (-12)
        (v := [zero, one, one]) (by decide))
  have e10 := e9.add
      (tendsto_i9KuRat_mul_hpl_zero_cons (-6) (15) (-6) (-3)
        (l := one) (v := [negOne, zero]) (by decide) (by decide))
  have e11 := e10.add
      (tendsto_i9KuRat_mul_hpl_zero_cons (6) (-3) (6) (-9)
        (l := one) (v := [zero, one]) (by decide) (by decide))
  have e12 := e11.add
      (tendsto_i9KuRat_mul_hpl_zero_cons (12) (-18) (12) (-6)
        (l := one) (v := [one, zero]) (by decide) (by decide))
  have e13 := e12.add
      (tendsto_i9KuRat_mul_hpl_zero_cons (36) (-54) (36) (-18)
        (l := one) (v := [one, one]) (by decide) (by decide))
  have e14 := e13.add
      (tendsto_i9KuRat_mul_hpl_zero (6) (0) (0)
        (v := [zero, negOne, zero, one]) (by decide))
  have e15 := e14.add
      (tendsto_i9KuRat_mul_hpl_zero (6) (0) (0)
        (v := [zero, negOne, one, zero]) (by decide))
  have e16 := e15.add
      (tendsto_i9KuRat_mul_hpl_zero (24) (0) (0)
        (v := [zero, zero, one, one]) (by decide))
  have e17 := e16.add
      (tendsto_i9KuRat_mul_hpl_zero (6) (0) (0)
        (v := [zero, one, negOne, zero]) (by decide))
  have e18 := e17.add
      (tendsto_i9KuRat_mul_hpl_zero (18) (0) (0)
        (v := [zero, one, zero, one]) (by decide))
  have e19 := e18.add
      (tendsto_i9KuRat_mul_hpl_zero (12) (0) (0)
        (v := [zero, one, one, zero]) (by decide))
  have e20 := e19.add
      (tendsto_i9KuRat_mul_hpl_zero (36) (0) (0)
        (v := [zero, one, one, one]) (by decide))
  exact (e20.congr fun x => rfl).mono_right (le_of_eq (congrArg 𝓝 (by norm_num)))

theorem tendsto_i9KuPsi_one : Tendsto i9KuPsi (𝓝[<] 1) (𝓝 i9KuVal) := by
  have e0 := (tendsto_i9KuRat_one (0) (0) (9 * (π ^ 2 / 6)) (9 / 2 * (π ^ 2 / 6)))
  have e1 := e0.add
      (tendsto_i9KuRat_mul_hpl_one (0) (0) (21) (0)
        (l := zero) (v := []) (by decide))
  have e2 := e1.add
      (tendsto_i9KuRat_mul_hpl_one_of (0) (-21 + -3 * (π ^ 2 / 6)) (21) (3 * (π ^ 2 / 6))
        [one] (by norm_num))
  have e3 := e2.add
      (tendsto_i9KuRat_mul_hpl_one (0) (-33 / 2) (-21) (-9 / 2)
        (l := negOne) (v := [zero]) (by decide))
  have e4 := e3.add
      (tendsto_i9KuRat_mul_hpl_one (0) (-6 * (π ^ 2 / 6)) (-12) (-9)
        (l := zero) (v := [one]) (by decide))
  have e5 := e4.add
      (tendsto_i9KuRat_mul_hpl_one_of (0) (-9 / 2) (9) (-9 / 2) [one, zero] (by norm_num))
  have e6 := e5.add
      (tendsto_i9KuRat_mul_hpl_one_of (0) (-9) (18) (-9) [one, one] (by norm_num))
  have e7 := e6.add
      (tendsto_i9KuRat_mul_hpl_one (-6) (-9) (-6) (-3)
        (l := negOne) (v := [zero, one]) (by decide))
  have e8 := e7.add
      (tendsto_i9KuRat_mul_hpl_one (-6) (-9) (-6) (-3)
        (l := negOne) (v := [one, zero]) (by decide))
  have e9 := e8.add
      (tendsto_i9KuRat_mul_hpl_one (0) (-24) (0) (-12)
        (l := zero) (v := [one, one]) (by decide))
  have e10 := e9.add
      (tendsto_i9KuRat_mul_hpl_one_of (-6) (15) (-6) (-3) [one, negOne, zero] (by norm_num))
  have e11 := e10.add
      (tendsto_i9KuRat_mul_hpl_one_of (6) (-3) (6) (-9) [one, zero, one] (by norm_num))
  have e12 := e11.add
      (tendsto_i9KuRat_mul_hpl_one_of (12) (-18) (12) (-6) [one, one, zero] (by norm_num))
  have e13 := e12.add
      (tendsto_i9KuRat_mul_hpl_one_of (36) (-54) (36) (-18) [one, one, one] (by norm_num))
  have e14 := e13.add
      (tendsto_i9KuRat_mul_hpl_one (0) (6) (0) (0)
        (l := zero) (v := [negOne, zero, one]) (by decide))
  have e15 := e14.add
      (tendsto_i9KuRat_mul_hpl_one (0) (6) (0) (0)
        (l := zero) (v := [negOne, one, zero]) (by decide))
  have e16 := e15.add
      (tendsto_i9KuRat_mul_hpl_one (0) (24) (0) (0)
        (l := zero) (v := [zero, one, one]) (by decide))
  have e17 := e16.add
      (tendsto_i9KuRat_mul_hpl_one (0) (6) (0) (0)
        (l := zero) (v := [one, negOne, zero]) (by decide))
  have e18 := e17.add
      (tendsto_i9KuRat_mul_hpl_one (0) (18) (0) (0)
        (l := zero) (v := [one, zero, one]) (by decide))
  have e19 := e18.add
      (tendsto_i9KuRat_mul_hpl_one (0) (12) (0) (0)
        (l := zero) (v := [one, one, zero]) (by decide))
  have e20 := e19.add
      (tendsto_i9KuRat_mul_hpl_one (0) (36) (0) (0)
        (l := zero) (v := [one, one, one]) (by decide))
  refine (e20.congr fun x => rfl).mono_right (le_of_eq (congrArg 𝓝 ?_))
  simp only [i9KuRat, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_one_at_one,
    hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one, hpl_zero_one_one_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_one_one_one_at_one]
  unfold i9KuVal
  ring

/-! ### The value of `K_u` -/

theorem integrableOn_i9KuI : IntegrableOn i9KuI (Ioo 0 1) := by
  have hB := integrableOn_i9KuFD
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hB
  refine Integrable.congr hB.integral_prod_right ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun w hw => ?_)
  simp only [i9KuD', i9KuI]
  rw [← integral_log_i9KuP_sq hw, ← integral_const_mul]
  congr 1
  funext x
  ring

theorem integral_i9KuI : ∫ w in Ioo (0 : ℝ) 1, i9KuI w = i9KuVal := by
  have hint : IntervalIntegrable i9KuI volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 integrableOn_i9KuI
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun w hw => hasDerivAt_i9KuPsi hw) hint tendsto_i9KuPsi_zero tendsto_i9KuPsi_one
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, sub_zero] at h
  exact h

/-- **The `K_u` integral**: `∫∫ log (1 - w) · i9A1Dens = (9π² + 12 ζ(3) + 17π⁴/20 - 24π² log 2)/4`.
-/
theorem integral_log_one_sub_mul_i9A1Dens_val :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, Real.log (1 - z.2) * i9A1Dens z =
      (9 * π ^ 2 + 12 * zeta3 + 17 / 20 * π ^ 4 - 24 * π ^ 2 * Real.log 2) / 4 := by
  rw [integral_log_one_sub_mul_i9A1Dens_eq, ← i9KuVal, ← integral_i9KuI]
  refine setIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
  rw [integral_log_i9KuP_sq hw]
  rfl

/-- **The expansion of `Rem`**, unconditionally. -/
theorem hasTruncLaurent_i9Rem : HasTruncLaurent i9Rem i9RemLaurent 3 :=
  hasTruncLaurent_i9Rem_of_Ku integral_log_one_sub_mul_i9A1Dens_val

end QED.ThreeLoopD
