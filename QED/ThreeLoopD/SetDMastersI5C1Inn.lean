/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Rep
public import QED.ThreeLoopD.SetDMastersI5C0Val
public import QED.ThreeLoopD.SetDMastersI5C1Lim

/-!
# Set (d), master `I₅`: the inner integral of `t K₁(t)` over `c`

For `0 < x` and `x + t < q`, with `U = (c + x)(q - c)/t`, the function
(`QED.ThreeLoopD.i5C1HP`, `ρ = (c + x)/(q - c)` in the comments)

  `G(c) = log² ρ/2 - 3 Li₂((c + x)/(q + x)) - 3/2 (log (q + x) - log (q - c))²`
    `- Li₂(x (q - c)/(q (c + x))) + (4 log (q + x) - 2 log t - log q) log ρ`

satisfies `G' = (q + x)(2 log U - log c)/((c + x)(q - c))` on `(0, q)`; every dilogarithm
argument lies in `[0, 1]` on `[0, q - x - t]` (the term `3 Li₂((c + x)/(q + x))` is the Landen
form of `-3 Li₂(-ρ)`, whose argument leaves `[-1, 1]` near `x = 0`). The `log c` singularity at
`c = 0` is integrable, so (`QED.ThreeLoopD.i5_integral_cIn`)

  `∫₀^{q-x-t} (α + β (2 log U - log c))/((c + x)(q - c)) dc = i5C1In t x q α β`.

With `t = (1 - ξ)²/ξ`, `x = v (1 - ξ)`, `q = t/x` this evaluates the inner integral of
`QED.ThreeLoopD.i5KerC_one_eq_rep` (`QED.ThreeLoopD.i5_integral_i5K1F`), so
`t K₁(t) = ∫₀¹ i5K1G ξ v dv` (`QED.ThreeLoopD.i5KerC_one_eq_repv`), and the hypothesis of
`QED.ThreeLoopD.i5RemCoeff_one_of_kerC` reduces to the one-variable identity
`∫₀¹ i5K1G ξ v dv = K(ξ)` (`QED.ThreeLoopD.i5RemCoeff_one_of_intG`).

With `y = 1 - ξ`, `x = v y`, every logarithm and dilogarithm argument factors over the letters
`x, 1 - x, ξ x + y, ξ x + y², ξ x² + y², ξ, y, 1 + ξ`; the constant `log 2` cancels and
`i5K1G ξ v = y I(v y)` with `I = QED.ThreeLoopD.i5K1I` (`QED.ThreeLoopD.i5K1G_eq`):

  `I = ξ/(ξ x + y) · (H + log (ρ₁/ρ₀) · br)`, `ρ₀ = ξ x²/y²`, `ρ₁ = y² (1 - x)/(x (ξ x + y²))`,

so `t K₁(t) = ∫₀^y I(x) dx` (`QED.ThreeLoopD.integral_i5K1G`), and `c₁` follows from
`∫₀^y I = K(ξ)` (`QED.ThreeLoopD.i5RemCoeff_one_of_intI`).

## Main results

* `QED.ThreeLoopD.i5_integral_cLog`, `QED.ThreeLoopD.i5_integral_cIn`.
* `QED.ThreeLoopD.i5_integral_i5K1F`, `QED.ThreeLoopD.i5KerC_one_eq_repv`.
* `QED.ThreeLoopD.i5RemCoeff_one_of_intG`.
* `QED.ThreeLoopD.i5K1G_eq`, `QED.ThreeLoopD.integral_i5K1G`,
  `QED.ThreeLoopD.i5RemCoeff_one_of_intI`.
-/

@[expose] public section

open MeasureTheory Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- The primitive in `c` of `(q + x)(2 log U - log c)/((c + x)(q - c))`, `U = (c + x)(q - c)/t`. -/
noncomputable def i5C1HP (t x q c : ℝ) : ℝ :=
  (log (c + x) - log (q - c)) ^ 2 / 2 - 3 * Li₂ ((c + x) / (q + x)) -
    3 / 2 * (log (q + x) - log (q - c)) ^ 2 - Li₂ (x * (q - c) / (q * (c + x))) +
    (4 * log (q + x) - 2 * log t - log q) * (log (c + x) - log (q - c))

theorem hasDerivAt_i5C1HP {t x q c : ℝ} (ht : 0 < t) (hx : 0 < x) (hc : 0 < c)
    (hcq : c < q) :
    HasDerivAt (i5C1HP t x q) ((q + x) * ((2 * log ((c + x) * (q - c) / t) - log c) /
      ((c + x) * (q - c)))) c := by
  have h1 : 0 < c + x := by linarith
  have h2 : 0 < q - c := by linarith
  have hq : 0 < q := by linarith
  have hqx : 0 < q + x := by linarith
  have da : HasDerivAt (fun c => c + x) 1 c := (hasDerivAt_id' c).add_const x
  have db : HasDerivAt (fun c => q - c) (-1) c := by
    simpa using (hasDerivAt_id' c).const_sub q
  have la := da.log h1.ne'
  have lb := db.log h2.ne'
  have hw1 : (c + x) / (q + x) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one hqx).mpr (by linarith)⟩
  have hw2 : x * (q - c) / (q * (c + x)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one (by positivity)).mpr (by nlinarith)⟩
  have L1 := (hasDerivAt_Li₂' hw1).comp c (da.div_const (q + x))
  have dw2 : HasDerivAt (fun c => x * (q - c) / (q * (c + x)))
      (-(x * (q + x)) / (q * (c + x) ^ 2)) c := by
    have := (db.const_mul x).div (da.const_mul q) (by positivity)
    convert this using 1
    field_simp
    ring
  have L2 := (hasDerivAt_Li₂' hw2).comp c dw2
  have e := (((((la.sub lb).pow 2).div_const 2).sub (L1.const_mul 3)).sub
    ((((hasDerivAt_const c (log (q + x))).sub lb).pow 2).const_mul (3 / 2))).sub L2 |>.add
    ((la.sub lb).const_mul (4 * log (q + x) - 2 * log t - log q))
  convert e using 1
  · funext c
    simp only [i5C1HP, Function.comp_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
  rw [show 1 - (c + x) / (q + x) = (q - c) / (q + x) by field_simp; ring,
    show 1 - x * (q - c) / (q * (c + x)) = c * (q + x) / (q * (c + x)) by field_simp; ring,
    Real.log_div h2.ne' hqx.ne',
    Real.log_div (mul_pos hc hqx).ne' (mul_pos hq h1).ne',
    Real.log_mul hc.ne' hqx.ne', Real.log_mul hq.ne' h1.ne',
    Real.log_div (mul_pos h1 h2).ne' ht.ne', Real.log_mul h1.ne' h2.ne']
  simp only [Pi.sub_apply, Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]
  field_simp
  ring

theorem continuousOn_i5C1HP {t x q : ℝ} (hx : 0 < x) (hu : x + t < q) (ht : 0 < t) :
    ContinuousOn (i5C1HP t x q) (Icc 0 (q - x - t)) := by
  have hq : 0 < q := by linarith
  have hqx : 0 < q + x := by linarith
  have h1 : ∀ c ∈ Icc 0 (q - x - t), 0 < c + x := fun c hc => by linarith [hc.1]
  have h2 : ∀ c ∈ Icc 0 (q - x - t), 0 < q - c := fun c hc => by linarith [hc.2]
  have la : ContinuousOn (fun c => log (c + x)) (Icc 0 (q - x - t)) :=
    ContinuousOn.log (by fun_prop) fun c hc => (h1 c hc).ne'
  have lb : ContinuousOn (fun c => log (q - c)) (Icc 0 (q - x - t)) :=
    ContinuousOn.log (by fun_prop) fun c hc => (h2 c hc).ne'
  have c1 : ContinuousOn (fun c => Li₂ ((c + x) / (q + x))) (Icc 0 (q - x - t)) :=
    continuousOn_Li₂.comp (by fun_prop) fun c hc => by
      have := h1 c hc
      exact ⟨by linarith [div_pos this hqx], (div_le_one hqx).mpr (by linarith [hc.2])⟩
  have c2 : ContinuousOn (fun c => Li₂ (x * (q - c) / (q * (c + x)))) (Icc 0 (q - x - t)) := by
    refine continuousOn_Li₂.comp (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun c hc => (mul_pos hq (h1 c hc)).ne') fun c hc => ?_
    have a1 := h1 c hc
    have a2 := h2 c hc
    have : 0 < x * (q - c) / (q * (c + x)) := by positivity
    exact ⟨by linarith, (div_le_one (by positivity)).mpr (by nlinarith [hc.1])⟩
  have e : i5C1HP t x q = fun c => (log (c + x) - log (q - c)) ^ 2 / 2 -
      3 * Li₂ ((c + x) / (q + x)) - 3 / 2 * (log (q + x) - log (q - c)) ^ 2 -
      Li₂ (x * (q - c) / (q * (c + x))) +
      (4 * log (q + x) - 2 * log t - log q) * (log (c + x) - log (q - c)) := rfl
  rw [e]
  exact (((((la.sub lb).pow 2).div_const 2).sub (continuousOn_const.mul c1)).sub
    (continuousOn_const.mul ((continuousOn_const.sub lb).pow 2))).sub c2 |>.add
    (continuousOn_const.mul (la.sub lb))

theorem intervalIntegrable_i5C1H {t x q : ℝ} (hx : 0 < x) (hu : x + t < q) (ht : 0 < t) :
    IntervalIntegrable (fun c => (2 * log ((c + x) * (q - c) / t) - log c) /
      ((c + x) * (q - c))) volume 0 (q - x - t) := by
  have h1 : ∀ c ∈ uIcc 0 (q - x - t), 0 < c + x := fun c hc => by
    rw [uIcc_of_le (by linarith)] at hc; linarith [hc.1]
  have h2 : ∀ c ∈ uIcc 0 (q - x - t), 0 < q - c := fun c hc => by
    rw [uIcc_of_le (by linarith)] at hc; linarith [hc.2]
  have hd : ContinuousOn (fun c => 1 / ((c + x) * (q - c))) (uIcc 0 (q - x - t)) :=
    continuousOn_const.div (by fun_prop) fun c hc => (mul_pos (h1 c hc) (h2 c hc)).ne'
  have hg : ContinuousOn (fun c => 2 * log ((c + x) * (q - c) / t) / ((c + x) * (q - c)))
      (uIcc 0 (q - x - t)) :=
    (continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun c hc =>
      (div_pos (mul_pos (h1 c hc) (h2 c hc)) ht).ne')).div (by fun_prop)
      fun c hc => (mul_pos (h1 c hc) (h2 c hc)).ne'
  have := hg.intervalIntegrable.sub
    ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := q - x - t)).mul_continuousOn hd)
  refine this.congr fun c _ => ?_
  ring

/-- **The `c`-integral of the logarithmic part**: for `0 < x`, `x + t < q`,
`∫₀^{q-x-t} (2 log U - log c)/((c + x)(q - c)) dc = (G(q - x - t) - G(0))/(q + x)`. -/
theorem i5_integral_cLog {t x q : ℝ} (ht : 0 < t) (hx : 0 < x) (hu : x + t < q) :
    ∫ c in Ioo 0 (q - x - t), (2 * log ((c + x) * (q - c) / t) - log c) /
      ((c + x) * (q - c)) = (i5C1HP t x q (q - x - t) - i5C1HP t x q 0) / (q + x) := by
  have hu0 : 0 ≤ q - x - t := by linarith
  have hqx : 0 < q + x := by linarith
  have hd : ∀ c ∈ Ioo 0 (q - x - t), HasDerivAt (fun c => i5C1HP t x q c / (q + x))
      ((2 * log ((c + x) * (q - c) / t) - log c) / ((c + x) * (q - c))) c := fun c hc => by
    have := (hasDerivAt_i5C1HP ht hx hc.1 (by linarith [hc.2])).div_const (q + x)
    convert this using 1
    field_simp
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu0,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu0
      ((continuousOn_i5C1HP hx hu ht).div_const _) hd (intervalIntegrable_i5C1H hx hu ht)]
  ring

/-- The closed form of `∫₀^{q-x-t} (α + β (2 log U - log c))/((c + x)(q - c)) dc`. -/
noncomputable def i5C1In (t x q α β : ℝ) : ℝ :=
  (α * (log (q - t) - log (x + t) - log x + log q) +
    β * (i5C1HP t x q (q - x - t) - i5C1HP t x q 0)) / (q + x)

theorem i5_integral_cIn {t x q : ℝ} (ht : 0 < t) (hx : 0 < x) (hu : x + t < q) (α β : ℝ) :
    ∫ c in Ioo 0 (q - x - t), (α + β * (2 * log ((c + x) * (q - c) / t) - log c)) /
      ((c + x) * (q - c)) = i5C1In t x q α β := by
  have hu0 : 0 ≤ q - x - t := by linarith
  have hqx : 0 < q + x := by linarith
  have h1 : ∀ c ∈ Icc 0 (q - x - t), 0 < c + x := fun c hc => by linarith [hc.1]
  have h2 : ∀ c ∈ Icc 0 (q - x - t), 0 < q - c := fun c hc => by linarith [hc.2]
  have hd : ∀ c ∈ Ioo 0 (q - x - t), HasDerivAt
      (fun c => (α * (log (c + x) - log (q - c)) + β * i5C1HP t x q c) / (q + x))
      ((α + β * (2 * log ((c + x) * (q - c) / t) - log c)) / ((c + x) * (q - c))) c :=
    fun c hc => by
      have a1 := h1 c (Ioo_subset_Icc_self hc)
      have a2 := h2 c (Ioo_subset_Icc_self hc)
      have da : HasDerivAt (fun c => c + x) 1 c := (hasDerivAt_id' c).add_const x
      have db : HasDerivAt (fun c => q - c) (-1) c := by
        simpa using (hasDerivAt_id' c).const_sub q
      have := ((((da.log a1.ne').sub (db.log a2.ne')).const_mul α).add
        ((hasDerivAt_i5C1HP (q := q) ht hx hc.1 (by linarith [hc.2])).const_mul β)).div_const
          (q + x)
      convert this using 1
      field_simp
      ring
  have hc : ContinuousOn (fun c => (α * (log (c + x) - log (q - c)) + β * i5C1HP t x q c) /
      (q + x)) (Icc 0 (q - x - t)) :=
    ((continuousOn_const.mul ((ContinuousOn.log (by fun_prop) fun c hc => (h1 c hc).ne').sub
      (ContinuousOn.log (by fun_prop) fun c hc => (h2 c hc).ne'))).add
      (continuousOn_const.mul (continuousOn_i5C1HP hx hu ht))).div_const _
  have hi0 : IntervalIntegrable (fun c => 1 / ((c + x) * (q - c))) volume 0 (q - x - t) :=
    ContinuousOn.intervalIntegrable_of_Icc hu0 (continuousOn_const.div (by fun_prop)
      fun c hc => (mul_pos (h1 c hc) (h2 c hc)).ne')
  have hi : IntervalIntegrable (fun c => (α + β * (2 * log ((c + x) * (q - c) / t) - log c)) /
      ((c + x) * (q - c))) volume 0 (q - x - t) := by
    refine ((hi0.const_mul α).add ((intervalIntegrable_i5C1H hx hu ht).const_mul β)).congr
      fun c _ => ?_
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu0,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu0 hc hd hi]
  have e1 : q - x - t + x = q - t := by ring
  have e2 : q - (q - x - t) = x + t := by ring
  rw [e1, e2, zero_add, sub_zero, i5C1In]
  ring

/-- The `c`-independent part `(y Λ(y, x) - x Λ(x, x)) + (y M(y) - x M(x))` of `i5K1F`. -/
noncomputable def i5C1B0 (ξ v : ℝ) : ℝ :=
  ((1 - ξ) * i5Lx ((1 - ξ) ^ 2 / ξ) (1 - ξ) (v * (1 - ξ)) -
    v * (1 - ξ) * i5Lx ((1 - ξ) ^ 2 / ξ) (v * (1 - ξ)) (v * (1 - ξ))) +
  ((1 - ξ) * i5Mx ((1 - ξ) ^ 2 / ξ) (1 - ξ) - v * (1 - ξ) * i5Mx ((1 - ξ) ^ 2 / ξ) (v * (1 - ξ)))

/-- The inner integral `∫₀^{u(v)} i5K1F ξ v c dc` in closed form. -/
noncomputable def i5K1G (ξ v : ℝ) : ℝ :=
  (1 - ξ) / ξ * (1 / v ^ 2 + ξ) / i5U ξ v *
    i5C1In ((1 - ξ) ^ 2 / ξ) (v * (1 - ξ)) ((1 - ξ) ^ 2 / ξ / (v * (1 - ξ)))
      ((1 - 2 * log 2) * ((1 - ξ) - v * (1 - ξ)) - i5C1B0 ξ v) ((1 - ξ) - v * (1 - ξ))

/-- **The inner integral over `c`.** -/
theorem i5_integral_i5K1F {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    ∫ c in Ioo 0 (i5U ξ v), i5K1F ξ v c = i5K1G ξ v := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  have ht : 0 < (1 - ξ) ^ 2 / ξ := by positivity
  have hx : 0 < v * (1 - ξ) := mul_pos hv.1 hy
  have hU := i5U_pos hξ hv
  have hUe := i5U_eq hξ hv.1
  have hu : v * (1 - ξ) + (1 - ξ) ^ 2 / ξ < (1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) := by
    linarith
  have key := i5_integral_cIn ht hx hu ((1 - 2 * log 2) * ((1 - ξ) - v * (1 - ξ)) - i5C1B0 ξ v)
    ((1 - ξ) - v * (1 - ξ))
  rw [show (1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) - v * (1 - ξ) - (1 - ξ) ^ 2 / ξ = i5U ξ v from
    hUe.symm] at key
  unfold i5K1G
  rw [← key, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun c _ => ?_
  unfold i5K1F i5C1B0
  rw [mul_assoc (i5U ξ v)]
  generalize (c + v * (1 - ξ)) * ((1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) - c) = D
  generalize i5Lx ((1 - ξ) ^ 2 / ξ) (1 - ξ) (v * (1 - ξ)) = a1
  generalize i5Lx ((1 - ξ) ^ 2 / ξ) (v * (1 - ξ)) (v * (1 - ξ)) = a2
  generalize i5Mx ((1 - ξ) ^ 2 / ξ) (1 - ξ) = a3
  generalize i5Mx ((1 - ξ) ^ 2 / ξ) (v * (1 - ξ)) = a4
  ring

/-- **`t K₁(t)` as a single integral over `v`.** -/
theorem i5KerC_one_eq_repv {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    (((1 - ξ) ^ 2 / ξ : ℝ) : ℂ) * i5KerC ((1 - ξ) ^ 2 / ξ) 1 =
      ((∫ v in Ioo (0 : ℝ) 1, i5K1G ξ v : ℝ) : ℂ) := by
  rw [i5KerC_one_eq_rep hξ]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioo fun v hv => i5_integral_i5K1F hξ hv

/-- **`c₁` from the `v`-integral**: if `∫₀¹ i5K1G ξ v dv = K(ξ)` for `0 < ξ < 1`, then
`c₁ = -4π⁴/45 - 5π²/3 - 5ζ(3) + 25`. -/
theorem i5RemCoeff_one_of_intG
    (hG : ∀ ξ ∈ Ioo (0 : ℝ) 1, ∫ v in Ioo (0 : ℝ) 1, i5K1G ξ v = i5K1x ξ) :
    i5RemCoeff 1 = -4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ) + 25 := by
  refine i5RemCoeff_one_of_kerC fun t ht => ?_
  have hξ : i13Xi t ∈ Ioo (0 : ℝ) 1 := ⟨i13Xi_pos ht.le, i13Xi_lt_one ht⟩
  have h := i5KerC_one_eq_repv hξ
  rw [← i13Xi_t ht.le] at h
  rw [h, hG _ hξ]

/-- `i5C1In` with the endpoint values of the primitive substituted. -/
theorem i5C1In_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) (α β : ℝ) :
    i5C1In t x q α β = (α * (log (q - t) - log (x + t) - log x + log q) +
      β * ((log (q - t) - log (x + t)) ^ 2 / 2 - 3 * Li₂ ((q - t) / (q + x)) -
        3 / 2 * (log (q + x) - log (x + t)) ^ 2 - Li₂ (x * (x + t) / (q * (q - t))) +
        (4 * log (q + x) - 2 * log t - log q) * (log (q - t) - log (x + t)) -
        ((log x - log q) ^ 2 / 2 - 3 * Li₂ (x / (q + x)) - 3 / 2 * (log (q + x) - log q) ^ 2 -
          π ^ 2 / 6 + (4 * log (q + x) - 2 * log t - log q) * (log x - log q)))) / (q + x) := by
  unfold i5C1In i5C1HP
  rw [show q - x - t + x = q - t by ring, show q - (q - x - t) = x + t by ring, zero_add,
    sub_zero, show x * q / (q * x) = 1 by field_simp, Li₂_one]

/-! ### The integrand in `x = v (1 - ξ)` in letter form -/

/-- `log ρ₀ = log (ξ x²/y²)`, `y = 1 - ξ`. -/
noncomputable def i5C1r0 (ξ x : ℝ) : ℝ := log ξ + 2 * log x - 2 * log (1 - ξ)

/-- `log ρ₁ = log (y² (1 - x)/(x (ξ x + y²)))`, `y = 1 - ξ`. -/
noncomputable def i5C1r1 (ξ x : ℝ) : ℝ :=
  2 * log (1 - ξ) + log (1 - x) - log x - log (ξ * x + (1 - ξ) ^ 2)

/-- `(q + x) H` in letter form (`H` the `c`-integral of `(2 log U - log c)/((c + x)(q - c))`). -/
noncomputable def i5C1Hx (ξ x : ℝ) : ℝ :=
  (i5C1r1 ξ x ^ 2 - i5C1r0 ξ x ^ 2) / 2 -
    Li₂ (ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x))) + π ^ 2 / 6 -
    3 * (Li₂ ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) - log x - log (ξ * x + (1 - ξ) ^ 2)) ^ 2 / 2 -
      Li₂ (ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)) -
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) - 2 * log (1 - ξ)) ^ 2 / 2) +
    (i5C1r1 ξ x - i5C1r0 ξ x) *
      (-3 * log x + 4 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) - log ξ - 6 * log (1 - ξ))

/-- The bracket multiplying `log (ρ₁/ρ₀)` in the integrand `I(x)`. -/
noncomputable def i5C1br (ξ x : ℝ) : ℝ :=
  1 + log x - 2 * log (1 - ξ) + log ξ +
    ((1 - ξ) * (1 + ξ) / ξ * (log (1 - ξ) + log (1 + ξ) - log (ξ * x + (1 - ξ))) +
      2 * ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x) * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) -
        2 * log (1 - ξ)) - (1 - ξ) * (1 + ξ) / ξ * log (1 + ξ))) / ((1 - ξ) - x)

/-- **The integrand `I(x)` of `t K₁(t) = ∫₀^{1-ξ} I(x) dx`**, with the letters
`x, 1 - x, ξ x + y, ξ x + y², ξ x² + y², ξ, y = 1 - ξ, 1 + ξ`. -/
noncomputable def i5K1I (ξ x : ℝ) : ℝ :=
  ξ / (ξ * x + (1 - ξ)) * (i5C1Hx ξ x + (i5C1r1 ξ x - i5C1r0 ξ x) * i5C1br ξ x)


theorem i5C1_logE2 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x)
    (hx1 : x < 1) : log ((1 - ξ) ^ 2 / ξ / x - (1 - ξ) ^ 2 / ξ) =
    2 * log (1 - ξ) - log ξ + log (1 - x) - log x := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  have h1 : 0 < 1 - x := by linarith
  rw [show (1 - ξ) ^ 2 / ξ / x - (1 - ξ) ^ 2 / ξ = (1 - ξ) ^ 2 * (1 - x) / (ξ * x) by
    field_simp, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
    h1.ne', Real.log_mul h0.ne' hx.ne', Real.log_pow]
  push_cast; ring

theorem i5C1_logE1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    log ((1 - ξ) ^ 2 / ξ) = 2 * log (1 - ξ) - log ξ := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  rw [Real.log_div (by positivity) h0.ne', Real.log_pow]
  push_cast; ring

theorem i5C1_logE3 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    log (x + (1 - ξ) ^ 2 / ξ) = log (ξ * x + (1 - ξ) ^ 2) - log ξ := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  rw [show x + (1 - ξ) ^ 2 / ξ = (ξ * x + (1 - ξ) ^ 2) / ξ by field_simp,
    Real.log_div (by positivity) h0.ne']

theorem i5C1_logE4 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    log ((1 - ξ) ^ 2 / ξ / x) = 2 * log (1 - ξ) - log ξ - log x := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  rw [Real.log_div (by positivity) hx.ne', Real.log_div (by positivity) h0.ne', Real.log_pow]
  push_cast; ring

theorem i5C1_logE5 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) : log ((1 - ξ) ^ 2 / ξ / x + x) =
    log (ξ * x ^ 2 + (1 - ξ) ^ 2) - log ξ - log x := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  rw [show (1 - ξ) ^ 2 / ξ / x + x = (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x) by field_simp; ring,
    Real.log_div (by positivity) (by positivity), Real.log_mul h0.ne' hx.ne']
  ring

theorem i5C1_logE6 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    log (1 + (1 - ξ) * x / ((1 - ξ) ^ 2 / ξ)) =
    log (ξ * x + (1 - ξ)) - log (1 - ξ) := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  rw [show 1 + (1 - ξ) * x / ((1 - ξ) ^ 2 / ξ) = (ξ * x + (1 - ξ)) / (1 - ξ) by
    field_simp; ring, Real.log_div (by positivity) hy.ne']

theorem i5C1_logE7 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    log (1 + x * x / ((1 - ξ) ^ 2 / ξ)) =
    log (ξ * x ^ 2 + (1 - ξ) ^ 2) - 2 * log (1 - ξ) := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  rw [show 1 + x * x / ((1 - ξ) ^ 2 / ξ) = (ξ * x ^ 2 + (1 - ξ) ^ 2) / (1 - ξ) ^ 2 by
    field_simp; ring, Real.log_div (by positivity) (by positivity), Real.log_pow]
  push_cast; ring

theorem i5C1_logE9 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    log (1 + x ^ 2 / ((1 - ξ) ^ 2 / ξ)) =
    log (ξ * x ^ 2 + (1 - ξ) ^ 2) - 2 * log (1 - ξ) := by
  rw [← i5C1_logE7 hξ hx, sq]

theorem i5C1_argA1 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    ((1 - ξ) ^ 2 / ξ / x - (1 - ξ) ^ 2 / ξ) / ((1 - ξ) ^ 2 / ξ / x + x) =
    (1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  have : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  field_simp
  ring

theorem i5C1_argA2 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    x / ((1 - ξ) ^ 2 / ξ / x + x) = ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  have : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  field_simp
  ring

theorem i5C1_argA3 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x)
    (hx1 : x < 1) : x * (x + (1 - ξ) ^ 2 / ξ) /
      ((1 - ξ) ^ 2 / ξ / x * ((1 - ξ) ^ 2 / ξ / x - (1 - ξ) ^ 2 / ξ)) =
    ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x)) := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  have h1 : 0 < 1 - x := by linarith
  rw [show (1 - ξ) ^ 2 / ξ / x - (1 - ξ) ^ 2 / ξ = (1 - ξ) ^ 2 * (1 - x) / (ξ * x) by
    field_simp]
  field_simp

theorem i5C1_logE8 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    log (1 + (1 - ξ) ^ 2 / ((1 - ξ) ^ 2 / ξ)) = log (1 + ξ) := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  rw [show 1 + (1 - ξ) ^ 2 / ((1 - ξ) ^ 2 / ξ) = 1 + ξ by field_simp]

/-- **The integrand in `x = v (1 - ξ)` in letter form**: `i5K1G ξ v = (1 - ξ) I(v (1 - ξ))`. -/
theorem i5K1G_eq {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    i5K1G ξ v = (1 - ξ) * i5K1I ξ (v * (1 - ξ)) := by
  have h0 := hξ.1
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  have hv0 := hv.1
  have hv1 : 0 < 1 - v := by linarith [hv.2]
  have hx : 0 < v * (1 - ξ) := mul_pos hv0 hy
  have hx1 : v * (1 - ξ) < 1 := by nlinarith [hv.2, hξ.2]
  have hq : 0 < (1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) := by positivity
  unfold i5K1G
  rw [i5C1In_eq hx hq, i5C1_argA1 hξ hx, i5C1_argA2 hξ hx, i5C1_argA3 hξ hx hx1,
    i5C1_logE2 hξ hx hx1, i5C1_logE3 hξ hx, i5C1_logE5 hξ hx, i5C1_logE4 hξ hx,
    i5C1_logE1 hξ]
  unfold i5C1B0 i5Lx i5Mx
  rw [i5C1_logE4 hξ hx, i5C1_logE6 hξ hx,
    i5C1_logE7 hξ hx, i5C1_logE8 hξ, i5C1_logE9 hξ hx]
  unfold i5K1I i5C1Hx i5C1br i5C1r0 i5C1r1 i5U
  have hl : 0 < 1 - v * (1 - ξ) := by linarith
  have h2 : 0 < ξ * (v * (1 - ξ)) + (1 - ξ) := by positivity
  have h3 : 0 < 1 - ξ - v * (1 - ξ) := by nlinarith
  have h4 : 0 < ξ * (v * (1 - ξ)) ^ 2 + (1 - ξ) ^ 2 := by positivity
  have h5 : 0 < 1 + v * ξ := by positivity
  generalize log ξ = a
  generalize log (1 - ξ) = b
  generalize log (v * (1 - ξ)) = c
  generalize log (1 - v * (1 - ξ)) = d
  generalize log (ξ * (v * (1 - ξ)) + (1 - ξ) ^ 2) = e
  generalize log (ξ * (v * (1 - ξ)) ^ 2 + (1 - ξ) ^ 2) = f
  generalize log (ξ * (v * (1 - ξ)) + (1 - ξ)) = g
  generalize log (1 + ξ) = h
  generalize Li₂ ((1 - ξ) ^ 2 * (1 - v * (1 - ξ)) / (ξ * (v * (1 - ξ)) ^ 2 + (1 - ξ) ^ 2)) = L1
  generalize Li₂ (ξ * (v * (1 - ξ)) ^ 2 / (ξ * (v * (1 - ξ)) ^ 2 + (1 - ξ) ^ 2)) = L2
  generalize Li₂ (ξ * (v * (1 - ξ)) ^ 3 * (ξ * (v * (1 - ξ)) + (1 - ξ) ^ 2) /
    ((1 - ξ) ^ 4 * (1 - v * (1 - ξ)))) = L3
  generalize log 2 = k
  field_simp
  ring

/-- **`t K₁(t)` as an integral over `x ∈ (0, 1 - ξ)`.** -/
theorem integral_i5K1G {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ∫ v in Ioo (0 : ℝ) 1, i5K1G ξ v = ∫ x in Ioo 0 (1 - ξ), i5K1I ξ x := by
  have hy : 0 < 1 - ξ := by linarith [hξ.2]
  rw [setIntegral_congr_fun measurableSet_Ioo fun v hv => i5K1G_eq hξ hv, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le hy.le,
    intervalIntegral.integral_comp_mul_right _ hy.ne', zero_mul, one_mul, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul]

/-- **`c₁` from the `x`-integral**: if `∫₀^{1-ξ} I(x) dx = K(ξ)` for `0 < ξ < 1`, then
`c₁ = -4π⁴/45 - 5π²/3 - 5ζ(3) + 25`. -/
theorem i5RemCoeff_one_of_intI
    (hI : ∀ ξ ∈ Ioo (0 : ℝ) 1, ∫ x in Ioo 0 (1 - ξ), i5K1I ξ x = i5K1x ξ) :
    i5RemCoeff 1 = -4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ) + 25 :=
  i5RemCoeff_one_of_intG fun ξ hξ => by rw [integral_i5K1G hξ, hI ξ hξ]

end QED.ThreeLoopD
