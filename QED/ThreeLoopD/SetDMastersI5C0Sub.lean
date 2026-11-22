/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C0Ang

/-!
# Set (d), master `I₅`: the kernel at `ε = 0` as a single integral

With `A(T) = 1 / (T + √(T² + 4t))` (`QED.ThreeLoopD.i5A`), the integrand of
`QED.ThreeLoopD.i5Ker_zero` is `2 (A(t) - A(t + X₁/c)) / (U X₁)` (`QED.ThreeLoopD.i5Phi0_eq`),
which is nonnegative since `A` decreases. Three substitutions reduce the double integral:

* at fixed `c`, `a = c (u - c)/t`: then `X₁ = c u`, `t U = t + t c + c u - c²`, and the
  integrand becomes `2 (A(t) - A(t + u)) / (u (t + t c + c u - c²))` on `u > c`
  (`QED.ThreeLoopD.i5Psi1`);
* Tonelli, to integrate first over `c ∈ (0, u)`;
* `u = t/x - x - t`, `x = v y`, with `y = 1 - ξ`, `t = y²/ξ`: then `A(t + u) = x/(2t)`,
  `A(t) = y/(2t)`, and `t + t c + c u - c² = (c + x)(t/x - c)`, so the `c`-integral is
  `(log ((u + x)/(t/x - u)) - log (x²/t)) / (t/x + x)`.

The result (`QED.ThreeLoopD.lintegral_i5Phi0`) is

  `t K₀(t) = ∫₀¹ ξ/(1 + vξ) (log (1 - v + vξ) - log ξ - 3 log v - log (1 - ξ + vξ)) dv`

(the integrand is `QED.ThreeLoopD.i5Psi`), as a lower Lebesgue integral.

## Main results

* `QED.ThreeLoopD.i5Phi0_eq`, `QED.ThreeLoopD.i5Phi0_nonneg`.
* `QED.ThreeLoopD.lintegral_i5Phi0`.
-/

@[expose] public section

open MeasureTheory Set Real

namespace QED.ThreeLoopD

/-- `A(T) = 1 / (T + √(T² + 4t))`. -/
noncomputable def i5A (t T : ℝ) : ℝ := 1 / (T + √(T ^ 2 + 4 * t))

/-- The integrand after `a = c (u - c)/t`. -/
noncomputable def i5Psi1 (t u c : ℝ) : ℝ :=
  2 * (i5A t t - i5A t (t + u)) / (u * (t + t * c + c * u - c ^ 2))

/-- The final integrand `ξ/(1 + vξ) (log (1 - v + vξ) - log ξ - 3 log v - log (1 - ξ + vξ))`. -/
noncomputable def i5Psi (ξ v : ℝ) : ℝ :=
  ξ / (1 + v * ξ) * (log (1 - v + v * ξ) - log ξ - 3 * log v - log (1 - ξ + v * ξ))

theorem i5Ang_two_sqrt {t : ℝ} (ht : 0 ≤ t) (T : ℝ) : i5Ang T (2 * √t) = i5A t T := by
  unfold i5Ang i5A
  rw [mul_pow, Real.sq_sqrt ht]
  ring_nf

theorem i5Ang_scale {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (T : ℝ) :
    c * i5Ang (c * T) (2 * c * √t) = i5A t T := by
  unfold i5Ang i5A
  have h : (c * T) ^ 2 + (2 * c * √t) ^ 2 = c ^ 2 * (T ^ 2 + 4 * t) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht]; ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have hc' : c ≠ 0 := hc.ne'
  by_cases h0 : T + √(T ^ 2 + 4 * t) = 0
  · rw [show c * T + c * √(T ^ 2 + 4 * t) = c * (T + √(T ^ 2 + 4 * t)) by ring, h0]
    simp
  · field_simp

theorem i5Phi0_eq {t : ℝ} (ht : 0 ≤ t) {a c : ℝ} (hc : 0 < c) :
    i5Phi0 t (a, c) = 2 * (i5A t t - i5A t (t + (c ^ 2 + a * t) / c)) /
      ((1 + a + c) * (c ^ 2 + a * t)) := by
  unfold i5Phi0
  have h := i5Ang_scale ht hc (t + (c ^ 2 + a * t) / c)
  rw [show c * (t + (c ^ 2 + a * t) / c) = c ^ 2 + a * t + c * t by field_simp; ring] at h
  simp only
  rw [h, i5Ang_two_sqrt ht]
  ring

theorem i5A_anti {t : ℝ} (ht : 0 ≤ t) {T T' : ℝ} (hT : 0 < T) (hTT : T ≤ T') :
    i5A t T' ≤ i5A t T := by
  unfold i5A
  have h1 : √(T ^ 2 + 4 * t) ≤ √(T' ^ 2 + 4 * t) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : 0 < T + √(T ^ 2 + 4 * t) := by positivity
  exact one_div_le_one_div_of_le h2 (by linarith)

theorem i5Phi0_nonneg {t : ℝ} (ht : 0 < t) {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    0 ≤ i5Phi0 t q := by
  obtain ⟨a, c⟩ := q
  have ha : 0 < a := hq.1
  have hc : 0 < c := hq.2
  rw [i5Phi0_eq ht.le hc]
  have : i5A t (t + (c ^ 2 + a * t) / c) ≤ i5A t t :=
    i5A_anti ht.le ht (by
      have h0 : 0 ≤ (c ^ 2 + a * t) / c := (by positivity)
      linarith)
  have : 0 < (1 + a + c) * (c ^ 2 + a * t) := by positivity
  exact div_nonneg (by linarith) this.le

/-! ### The substitution `a = c (u - c)/t` -/

theorem i5_image_affine {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    (fun u => c * (u - c) / t) '' Ioi c = Ioi 0 := by
  ext a
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : 0 < u - c := by linarith
    positivity
  · intro ha
    have h0 : 0 < t * a / c := by positivity
    refine ⟨c + t * a / c, by linarith, ?_⟩
    field_simp
    ring_nf

theorem i5Phi0_affine {t c u : ℝ} (ht : 0 < t) (hc : 0 < c) (hu : c < u) :
    ENNReal.ofReal |c / t| * ENNReal.ofReal (i5Phi0 t (c * (u - c) / t, c)) =
      ENNReal.ofReal (i5Psi1 t u c) := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (div_pos hc ht)]
  congr 1
  rw [i5Phi0_eq ht.le hc, i5Psi1]
  have hu0 : 0 < u := hc.trans hu
  have h1 : (c ^ 2 + c * (u - c) / t * t) / c = u := by field_simp; ring
  rw [h1]
  have h2 : 0 < t + t * c + c * u - c ^ 2 := by nlinarith
  have hD : (1 + c * (u - c) / t + c) * (c ^ 2 + c * (u - c) / t * t) =
      (t + t * c + c * u - c ^ 2) * u * c / t := by field_simp; ring
  rw [hD]
  generalize i5A t t - i5A t (t + u) = N
  field_simp

theorem lintegral_i5Phi0_inner {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (i5Phi0 t (a, c)) =
      ∫⁻ u in Ioi c, ENNReal.ofReal (i5Psi1 t u c) := by
  rw [← i5_image_affine ht hc, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f' := fun _ => c / t) (fun u _ => by
      have h := ((hasDerivAt_id u).sub_const c).const_mul c |>.div_const t
      simp only [id, mul_one] at h
      exact h.hasDerivWithinAt)
    (fun u _ v _ h => by field_simp at h; linarith)]
  exact setLIntegral_congr_fun measurableSet_Ioi fun u hu => i5Phi0_affine ht hc hu

/-! ### Tonelli -/

/-- `i5Psi1` on `{c < u}`, extended by zero. -/
noncomputable def i5F1 (t : ℝ) (p : ℝ × ℝ) : ENNReal :=
  if p.1 < p.2 then ENNReal.ofReal (i5Psi1 t p.2 p.1) else 0

theorem measurable_i5F1 (t : ℝ) : Measurable (i5F1 t) := by
  unfold i5F1 i5Psi1 i5A
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) (by fun_prop)
    measurable_const

theorem i5_swap (t : ℝ) :
    ∫⁻ c in Ioi (0 : ℝ), ∫⁻ u in Ioi c, ENNReal.ofReal (i5Psi1 t u c) =
      ∫⁻ u in Ioi (0 : ℝ), ∫⁻ c in Ioo 0 u, ENNReal.ofReal (i5Psi1 t u c) := by
  have h1 : ∀ c ∈ Ioi (0 : ℝ), ∫⁻ u in Ioi c, ENNReal.ofReal (i5Psi1 t u c) =
      ∫⁻ u in Ioi (0 : ℝ), i5F1 t (c, u) := fun c hc => by
    have : (fun u => i5F1 t (c, u)) =
        (Ioi c).indicator (fun u => ENNReal.ofReal (i5Psi1 t u c)) := by
      funext u; simp [i5F1, indicator, mem_Ioi]
    rw [this, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_left (le_of_lt hc)]
  have h2 : ∀ u ∈ Ioi (0 : ℝ), ∫⁻ c in Ioi (0 : ℝ), i5F1 t (c, u) =
      ∫⁻ c in Ioo 0 u, ENNReal.ofReal (i5Psi1 t u c) := fun u hu => by
    have : (fun c => i5F1 t (c, u)) =
        (Iio u).indicator (fun c => ENNReal.ofReal (i5Psi1 t u c)) := by
      funext c; simp [i5F1, indicator, mem_Iio]
    rw [this, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Iio_inter_Ioi]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1,
    lintegral_lintegral_swap (f := fun c u => i5F1 t (c, u)) (measurable_i5F1 t).aemeasurable]
  exact setLIntegral_congr_fun measurableSet_Ioi h2

/-! ### The integral over `c` -/

theorem i5_quad_eq (t x c : ℝ) (hx : x ≠ 0) :
    (c + x) * (t / x - c) = t + t * c + c * (t / x - x - t) - c ^ 2 := by
  field_simp
  ring

theorem i5_integral_c {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (hu : 0 < t / x - x - t) :
    ∫ c in Ioo 0 (t / x - x - t), 1 / (t + t * c + c * (t / x - x - t) - c ^ 2) =
      (log (t / x - t) - log (x + t) - log x + log (t / x)) / (t / x + x) := by
  set u := t / x - x - t with hud
  have hpos : ∀ c ∈ Icc 0 u, 0 < c + x ∧ 0 < t / x - c := fun c hc =>
    ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hD : 0 < t / x + x := by positivity
  have hd : ∀ c ∈ Ioo 0 u, HasDerivAt (fun c => (log (c + x) - log (t / x - c)) / (t / x + x))
      (1 / (t + t * c + c * u - c ^ 2)) c := fun c hc => by
    obtain ⟨h1, h2⟩ := hpos c (Ioo_subset_Icc_self hc)
    have da : HasDerivAt (fun c => c + x) 1 c := (hasDerivAt_id' c).add_const x
    have db : HasDerivAt (fun c => t / x - c) (-1) c := by
      simpa using (hasDerivAt_id' c).const_sub (t / x)
    have h := ((da.log h1.ne').sub (db.log h2.ne')).div_const (t / x + x)
    refine h.congr_deriv ?_
    rw [hud, ← i5_quad_eq t x c hx.ne', show t / x + x = (c + x) + (t / x - c) by ring]
    generalize c + x = A at h1 ⊢
    generalize t / x - c = B at h2 ⊢
    field_simp
    ring
  have hc : ContinuousOn (fun c => (log (c + x) - log (t / x - c)) / (t / x + x)) (Icc 0 u) :=
    ((ContinuousOn.log (by fun_prop) fun c hc => (hpos c hc).1.ne').sub
      (ContinuousOn.log (by fun_prop) fun c hc => (hpos c hc).2.ne')).div_const _
  have hi : IntervalIntegrable (fun c => 1 / (t + t * c + c * u - c ^ 2)) volume 0 u := by
    refine ContinuousOn.intervalIntegrable_of_Icc hu.le ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun c hc => ?_
    rw [hud, ← i5_quad_eq t x c hx.ne']
    exact (mul_pos (hpos c hc).1 (hpos c hc).2).ne'
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.le hc hd hi]
  have e1 : u + x = t / x - t := by rw [hud]; ring
  have e2 : t / x - u = x + t := by rw [hud]; ring
  rw [e1, e2, zero_add, sub_zero]
  ring

/-! ### The substitution `u = t/x - x - t`, `x = v y` -/

/-- `u(v) = y (1 - v)(1 + vξ)/(vξ) = t/(v y) - v y - t`, with `y = 1 - ξ`, `t = y²/ξ`. -/
noncomputable def i5U (ξ v : ℝ) : ℝ := (1 - ξ) * (1 - v) * (1 + v * ξ) / (v * ξ)

/-- The weight `2 (A(t) - A(t + u)) / u` in front of the `c`-integral. -/
noncomputable def i5Kw (t u : ℝ) : ℝ := 2 * (i5A t t - i5A t (t + u)) / u

theorem i5A_inv {t x : ℝ} (ht : 0 < t) (hx : 0 < x) : i5A t (t / x - x) = x / (2 * t) := by
  unfold i5A
  have hx' := hx.ne'
  rw [show (t / x - x) ^ 2 + 4 * t = (t / x + x) ^ 2 by field_simp; ring,
    Real.sqrt_sq (by positivity), show t / x - x + (t / x + x) = 2 * t / x by ring]
  have ht' := ht.ne'
  field_simp

theorem i5U_eq {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    i5U ξ v = (1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) - v * (1 - ξ) - (1 - ξ) ^ 2 / ξ := by
  have h0 : ξ ≠ 0 := hξ.1.ne'
  have h1 : 1 - ξ ≠ 0 := by linarith [hξ.2]
  unfold i5U
  field_simp
  ring

theorem i5U_pos {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) : 0 < i5U ξ v := by
  have := hξ.1; have := hξ.2; have := hv.1; have := hv.2
  unfold i5U
  have : 0 < 1 - ξ := by linarith
  have : 0 < 1 - v := by linarith
  positivity

theorem i5U_image {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : i5U ξ '' Ioo 0 1 = Ioi 0 := by
  obtain ⟨h0, h1⟩ := hξ
  ext U
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact i5U_pos ⟨h0, h1⟩ hv
  · intro hU
    set y := 1 - ξ with hy
    have hy0 : 0 < y := by linarith
    set t := y ^ 2 / ξ with ht
    have ht0 : 0 < t := by positivity
    have hty : y ^ 2 + t * y = t := by rw [ht, hy]; field_simp; ring
    set S := √((t + U) ^ 2 + 4 * t) with hS
    have hS2 : S ^ 2 = (t + U) ^ 2 + 4 * t := Real.sq_sqrt (by positivity)
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hSt : t + U < S := by nlinarith
    set x := (S - (t + U)) / 2 with hx
    have hx0 : 0 < x := by rw [hx]; linarith
    have hxq : x ^ 2 + (t + U) * x = t := by rw [hx]; nlinarith
    have hxy : x < y := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul hc hc hy0.le hx0.le]
    refine ⟨x / y, ⟨by positivity, (div_lt_one hy0).mpr hxy⟩, ?_⟩
    rw [i5U_eq ⟨h0, h1⟩ (by positivity), ← hy, ← ht, div_mul_cancel₀ _ hy0.ne']
    field_simp
    linarith

theorem i5U_injOn {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : InjOn (i5U ξ) (Ioo 0 1) := by
  intro v₁ h₁ v₂ h₂ h
  have := hξ.1; have := hξ.2; have := h₁.1; have := h₂.1
  have hy : 0 < 1 - ξ := by linarith
  unfold i5U at h
  have key : (v₂ - v₁) * (1 + v₁ * v₂ * ξ) = 0 := by
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp key with h' | h'
  · linarith
  · exfalso; have : 0 < 1 + v₁ * v₂ * ξ := by positivity
    linarith

theorem hasDerivAt_i5U {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    HasDerivAt (i5U ξ) (-((1 - ξ) / ξ * (1 / v ^ 2 + ξ))) v := by
  have h0 : ξ ≠ 0 := hξ.1.ne'
  have e : (fun v => (1 - ξ) / ξ * (v⁻¹ + (ξ - 1) - v * ξ)) =ᶠ[nhds v] i5U ξ := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    have hw' : w ≠ 0 := (mem_Ioi.mp hw).ne'
    unfold i5U
    field_simp
    ring
  have h := (((hasDerivAt_inv hv.ne').add_const (ξ - 1)).sub
    ((hasDerivAt_id v).mul_const ξ)).const_mul ((1 - ξ) / ξ)
  refine (h.congr_of_eventuallyEq e.symm).congr_deriv ?_
  field_simp
  ring

/-! ### Assembly -/

theorem i5_log_id {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    log ((1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) - (1 - ξ) ^ 2 / ξ) -
        log (v * (1 - ξ) + (1 - ξ) ^ 2 / ξ) - log (v * (1 - ξ)) +
        log ((1 - ξ) ^ 2 / ξ / (v * (1 - ξ))) =
      log (1 - v + v * ξ) - log ξ - 3 * log v - log (1 - ξ + v * ξ) := by
  obtain ⟨h0, h1⟩ := hξ
  obtain ⟨v0, v1⟩ := hv
  have hy : 0 < 1 - ξ := by linarith
  have ha : 0 < 1 - v + v * ξ := by nlinarith
  have hb : 0 < 1 - ξ + v * ξ := by nlinarith
  rw [show (1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) - (1 - ξ) ^ 2 / ξ =
      (1 - ξ) * (1 - v + v * ξ) / (ξ * v) by field_simp; ring,
    show v * (1 - ξ) + (1 - ξ) ^ 2 / ξ = (1 - ξ) * (1 - ξ + v * ξ) / ξ by field_simp; ring,
    show (1 - ξ) ^ 2 / ξ / (v * (1 - ξ)) = (1 - ξ) / (ξ * v) by field_simp]
  rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

theorem i5_point {ξ v : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal |-((1 - ξ) / ξ * (1 / v ^ 2 + ξ))| *
        ENNReal.ofReal (i5Kw ((1 - ξ) ^ 2 / ξ) (i5U ξ v) *
          ∫ c in Ioo 0 (i5U ξ v), 1 / ((1 - ξ) ^ 2 / ξ + (1 - ξ) ^ 2 / ξ * c +
            c * i5U ξ v - c ^ 2)) =
      ENNReal.ofReal (i5Psi ξ v / ((1 - ξ) ^ 2 / ξ)) := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  obtain ⟨h0, h1⟩ := hξ
  obtain ⟨v0, v1⟩ := hv
  have hy : 0 < 1 - ξ := by linarith
  have hv' : 0 < 1 - v := by linarith
  set t := (1 - ξ) ^ 2 / ξ with ht
  have ht0 : 0 < t := by positivity
  have hx : 0 < v * (1 - ξ) := by positivity
  have hU := i5U_eq ⟨h0, h1⟩ v0
  rw [← ht] at hU
  have hUp := i5U_pos ⟨h0, h1⟩ ⟨v0, v1⟩
  have hK : i5Kw t (i5U ξ v) = 2 * ((1 - ξ) / (2 * t) - v * (1 - ξ) / (2 * t)) / i5U ξ v := by
    unfold i5Kw
    rw [show t + i5U ξ v = t / (v * (1 - ξ)) - v * (1 - ξ) by rw [hU]; ring, i5A_inv ht0 hx]
    have e : t = t / (1 - ξ) - (1 - ξ) := by rw [ht]; field_simp
    have h := i5A_inv ht0 hy
    rw [← e] at h
    rw [h]
  rw [hK]
  conv_lhs => rw [hU]
  rw [i5_integral_c ht0 hx (hU ▸ hUp), ht, i5_log_id ⟨h0, h1⟩ ⟨v0, v1⟩, ← ht]
  rw [abs_neg, abs_of_pos (by positivity), show t / (v * (1 - ξ)) - v * (1 - ξ) - t =
      (1 - ξ) * (1 - v) * (1 + v * ξ) / (v * ξ) by rw [← hU]; rfl, i5Psi,
    show t / (v * (1 - ξ)) + v * (1 - ξ) = (1 - ξ) * (1 + v ^ 2 * ξ) / (v * ξ) by
      rw [ht]; field_simp]
  generalize log (1 - v + v * ξ) - log ξ - 3 * log v - log (1 - ξ + v * ξ) = L
  rw [ht]
  have hvx : 0 < 1 + v * ξ := by positivity
  have hvx2 : 0 < 1 + v ^ 2 * ξ := by positivity
  field_simp

theorem i5_inner_c {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    ∫⁻ c in Ioo 0 u, ENNReal.ofReal (i5Psi1 t u c) =
      ENNReal.ofReal (i5Kw t u * ∫ c in Ioo 0 u, 1 / (t + t * c + c * u - c ^ 2)) := by
  have hD : ∀ c ∈ Icc 0 u, 0 < t + t * c + c * u - c ^ 2 := fun c hc => by
    nlinarith [hc.1, hc.2]
  have hK : 0 ≤ i5Kw t u := by
    unfold i5Kw
    have := i5A_anti ht.le ht (by linarith : t ≤ t + u)
    exact div_nonneg (by linarith) hu.le
  have hcont : ContinuousOn (fun c => i5Kw t u * (1 / (t + t * c + c * u - c ^ 2))) (Icc 0 u) :=
    continuousOn_const.mul (ContinuousOn.div continuousOn_const (by fun_prop)
      fun c hc => (hD c hc).ne')
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
    (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun c hc =>
      mul_nonneg hK (one_div_nonneg.mpr (hD c (Ioo_subset_Icc_self hc)).le))]
  refine setLIntegral_congr_fun measurableSet_Ioo fun c _ => ?_
  unfold i5Psi1 i5Kw
  rw [mul_one_div, div_div]

theorem measurable_i5Phi0 (t : ℝ) : Measurable (i5Phi0 t) := by
  unfold i5Phi0 i5Ang
  fun_prop

/-- **The kernel at `ε = 0` as a single integral**: with `t = (1 - ξ)²/ξ`,
`∫∫ i5Phi0 t = ∫₀¹ i5Psi ξ v dv / t`, as lower integrals. -/
theorem lintegral_i5Phi0 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ENNReal.ofReal (i5Phi0 ((1 - ξ) ^ 2 / ξ) q) =
      ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal (i5Psi ξ v / ((1 - ξ) ^ 2 / ξ)) := by
  have ht : 0 < (1 - ξ) ^ 2 / ξ := by
    have := hξ.1; have : 0 < 1 - ξ := by linarith [hξ.2]
    positivity
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_symm _ (measurable_i5Phi0 _).ennreal_ofReal.aemeasurable,
    setLIntegral_congr_fun measurableSet_Ioi fun c hc => lintegral_i5Phi0_inner ht hc, i5_swap,
    setLIntegral_congr_fun measurableSet_Ioi fun u hu => i5_inner_c ht hu, ← i5U_image hξ,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun v hv => (hasDerivAt_i5U hξ hv.1).hasDerivWithinAt) (i5U_injOn hξ)]
  exact setLIntegral_congr_fun measurableSet_Ioo fun v hv => i5_point hξ hv

end QED.ThreeLoopD
