/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Small

/-!
# Set (d), master `I₅`: first bounds at large `t`

For `‖ε‖ ≤ 1/10` and `t ≥ 1` the triangle is `O(t ^ (-9/10))`
(`QED.ThreeLoopD.norm_i5Tri_le_large`): with `X₀ ≥ (c²) ^ (1/8) (a t) ^ (7/8)` and `X₀ ≥ a t`
the two terms of `QED.ThreeLoopD.i5TriDomS` are at most `t ^ (-77/80)` and `t ^ (-9/10)` times
`t`-independent integrable products (`QED.ThreeLoopD.i5TriDomS_le_large`). On shell
`‖1/w - 1/t‖ ≤ 2 t ^ (-3/2)` (`QED.ThreeLoopD.norm_inv_i5W_sub_le`).

The dependence on `w`: along the vertical segment from `X(t)` to `X(w) = X(t) + c (w - t)` the
real part stays `X₀`, so the mean-value bound `QED.ThreeLoopD.i5_norm_cpow_sub_le` gives
`‖X(w) ^ s - X(t) ^ s‖ ≤ ‖s‖ c ‖w - t‖ X₀ ^ (re s - 1) e ^ (π |im s| / 2)`. With
`X₀ ≥ (c²) ^ (1/10) (a t) ^ (9/20) (c t) ^ (9/20)` and `X₀ ≥ (a t) ^ (1/2) (c t) ^ (1/2)`
(`QED.ThreeLoopD.i5TriDomD_le`),

  `‖i5Tri ε t w - i5Tri ε t t‖ ≤ C ‖w - t‖ t ^ (-189/100)`, `t ≥ 1`
  (`QED.ThreeLoopD.norm_i5Tri_sub_le`),

so on shell (`‖w - t‖ ≤ 2 √t`) the triangle is `i5Tri ε t t + O(t ^ (-139/100))`.

These are two of the inputs of the bound on `(1, ∞)`.

## Main results

* `QED.ThreeLoopD.norm_i5Tri_le_large`, `QED.ThreeLoopD.norm_inv_i5W_sub_le`.
* `QED.ThreeLoopD.i5_norm_cpow_sub_le`, `QED.ThreeLoopD.norm_i5Tri_sub_le`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

/-- The first `t`-independent product at large `t`. -/
noncomputable def i5P3 (q : ℝ × ℝ) : ℝ :=
  i5Dom 0 (-(77 / 80)) (-(41 / 40)) q.1 * i5Dom 0 (-(11 / 40)) (-(81 / 80)) q.2

/-- The second `t`-independent product at large `t`. -/
noncomputable def i5P4 (q : ℝ × ℝ) : ℝ :=
  i5Dom 0 (-(9 / 10)) (-(21 / 20)) q.1 * i5Dom 0 0 (-(21 / 20)) q.2

theorem i5TriDomS_le_large {t : ℝ} (ht : 0 < t) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    i5TriDomS t (a, c) ≤ Real.exp (-(77 / 80) * Real.log t) * i5P3 (a, c) +
      Real.exp (-(9 / 10) * Real.log t) * i5P4 (a, c) := by
  obtain ⟨f1, f2, f3, -, -, -⟩ := i5_log_facts ht ha hc
  have hU : 0 < 1 + a + c := by linarith
  have hX : 0 < i5X0 t (a, c) := i5X0_pos ht ⟨ha, hc⟩
  have g1 : 2 * Real.log c ≤ Real.log (i5X0 t (a, c)) := by
    rw [← Real.log_rpow hc, Real.rpow_two]
    exact Real.log_le_log (by positivity) (by unfold i5X0; simp only; nlinarith)
  have g2 : Real.log a + Real.log t ≤ Real.log (i5X0 t (a, c)) := by
    rw [← Real.log_mul ha.ne' ht.ne']
    exact Real.log_le_log (by positivity) (by unfold i5X0; simp only; nlinarith)
  unfold i5TriDomS i5P3 i5P4 i5Dom
  simp only [Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hX, ← Real.exp_add]
  refine add_le_add (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_) <;>
    apply i5_le_add_min_add_min <;> linarith

theorem integrableOn_i5P3 : IntegrableOn i5P3 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  integrableOn_i5Dom_prod (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem integrableOn_i5P4 : IntegrableOn i5P4 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  integrableOn_i5Dom_prod (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The constant of the large-`t` bound on the triangle. -/
noncomputable def i5CTL : ℝ :=
  Real.exp (Real.pi / 20) * ((∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P3 q) +
    ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P4 q)

/-- **The triangle at large `t`**: `‖i5Tri ε t w‖ ≤ C t ^ (-9/10)` for `t ≥ 1`. -/
theorem norm_i5Tri_le_large {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht1 : 1 ≤ t)
    {w : ℂ} (hw : w.re = t) : ‖i5Tri ε t w‖ ≤ i5CTL * t ^ (-(9 / 10 : ℝ)) := by
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hp : t ^ (-(77 / 80 : ℝ)) ≤ t ^ (-(9 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have e1 : Real.exp (-(77 / 80) * Real.log t) = t ^ (-(77 / 80 : ℝ)) := by
    rw [Real.rpow_def_of_pos ht, mul_comm]
  have e2 : Real.exp (-(9 / 10) * Real.log t) = t ^ (-(9 / 10 : ℝ)) := by
    rw [Real.rpow_def_of_pos ht, mul_comm]
  have hB : IntegrableOn (fun q => t ^ (-(77 / 80 : ℝ)) * i5P3 q +
      t ^ (-(9 / 10 : ℝ)) * i5P4 q) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    (integrableOn_i5P3.const_mul _).add (integrableOn_i5P4.const_mul _)
  have hP3 : 0 ≤ ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P3 q :=
    setIntegral_nonneg hS fun q _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc ‖i5Tri ε t w‖ ≤ ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), Real.exp (Real.pi / 20) *
        (t ^ (-(77 / 80 : ℝ)) * i5P3 q + t ^ (-(9 / 10 : ℝ)) * i5P4 q) := by
        refine norm_integral_le_of_norm_le (hB.const_mul _)
          (ae_restrict_of_forall_mem hS fun q hq => ?_)
        refine (norm_i5TriF_le_domS hε ht hw hq).trans ?_
        gcongr
        obtain ⟨a, c⟩ := q
        rw [← e1, ← e2]
        exact i5TriDomS_le_large ht hq.1 hq.2
    _ = Real.exp (Real.pi / 20) * (t ^ (-(77 / 80 : ℝ)) *
          (∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P3 q) + t ^ (-(9 / 10 : ℝ)) *
          ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P4 q) := by
        rw [integral_const_mul, integral_add (integrableOn_i5P3.const_mul _)
          (integrableOn_i5P4.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ Real.exp (Real.pi / 20) * (t ^ (-(9 / 10 : ℝ)) *
          (∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P3 q) + t ^ (-(9 / 10 : ℝ)) *
          ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P4 q) := by gcongr
    _ = i5CTL * t ^ (-(9 / 10 : ℝ)) := by unfold i5CTL; ring

/-- **The on-shell propagator at large `t`**: `‖1/w - 1/t‖ ≤ 2 t ^ (-3/2)`. -/
theorem norm_inv_i5W_sub_le {t : ℝ} (ht : 0 < t) {z : ℝ} (hz : |z| ≤ 1) :
    ‖(i5W t z)⁻¹ - (t : ℂ)⁻¹‖ ≤ 2 * t ^ (-(3 / 2 : ℝ)) := by
  have hw := i5W_ne_zero ht z
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hnt : ‖(t : ℂ)‖ = t := by rw [norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have e : (i5W t z)⁻¹ - (t : ℂ)⁻¹ = ((t : ℂ) - i5W t z) / (i5W t z * t) := by
    field_simp
  have hd : ‖(t : ℂ) - i5W t z‖ ≤ 2 * Real.sqrt t := by
    have : (t : ℂ) - i5W t z = 2 * ((Real.sqrt t * z : ℝ) : ℂ) * I := by unfold i5W; ring
    rw [this, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_ofNat, norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
    nlinarith [Real.sqrt_nonneg t, abs_nonneg z]
  have hs : Real.sqrt t * (t * t)⁻¹ = t ^ (-(3 / 2 : ℝ)) := by
    have h2 : t * t = t ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
    rw [Real.sqrt_eq_rpow, h2, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    norm_num
  rw [e, norm_div, norm_mul, hnt]
  calc ‖(t : ℂ) - i5W t z‖ / (‖i5W t z‖ * t) ≤ 2 * Real.sqrt t / (t * t) := by
        gcongr
        exact le_norm_i5W t z
    _ = 2 * (Real.sqrt t * (t * t)⁻¹) := by ring
    _ = _ := by rw [hs]

/-! ### The dependence on `w` -/

/-- **A mean-value bound for `ξ ^ s`** along a vertical segment in `re ξ = x₀ > 0`. -/
theorem i5_norm_cpow_sub_le {X d : ℂ} {x0 : ℝ} (hx0 : 0 < x0) (hX : X.re = x0) (hd : d.re = 0)
    {s : ℂ} (hs : s.re - 1 ≤ 0) :
    ‖(X + d) ^ s - X ^ s‖ ≤
      ‖s‖ * ‖d‖ * (x0 ^ (s.re - 1) * Real.exp (Real.pi / 2 * |s.im|)) := by
  set f : ℝ → ℂ := fun τ => (X + (τ : ℂ) * d) ^ s with hf
  have hre : ∀ τ : ℝ, (X + (τ : ℂ) * d).re = x0 := fun τ => by simp [hX, hd]
  have hslit : ∀ τ : ℝ, X + (τ : ℂ) * d ∈ slitPlane := fun τ =>
    Or.inl (by rw [hre τ]; exact hx0)
  have hder : ∀ τ : ℝ, HasDerivAt f (s * (X + (τ : ℂ) * d) ^ (s - 1) * (1 * d)) τ := fun τ => by
    have hl : HasDerivAt (fun τ : ℝ => X + (τ : ℂ) * d) (1 * d) τ :=
      (((hasDerivAt_id τ).ofReal_comp).mul_const d).const_add X
    exact (Complex.hasStrictDerivAt_cpow_const (hslit τ)).hasDerivAt.comp τ hl
  have hb : ∀ τ ∈ Ico (0 : ℝ) 1, ‖s * (X + (τ : ℂ) * d) ^ (s - 1) * (1 * d)‖ ≤
      ‖s‖ * ‖d‖ * (x0 ^ (s.re - 1) * Real.exp (Real.pi / 2 * |s.im|)) := fun τ _ => by
    have hne : X + (τ : ℂ) * d ≠ 0 := slitPlane_ne_zero (hslit τ)
    have harg : |arg (X + (τ : ℂ) * d)| ≤ Real.pi / 2 :=
      abs_arg_le_pi_div_two_iff.mpr (by rw [hre τ]; exact hx0.le)
    have hn : x0 ≤ ‖X + (τ : ℂ) * d‖ := by rw [← hre τ]; exact re_le_norm _
    rw [one_mul, norm_mul, norm_mul, norm_cpow_of_ne_zero hne, div_eq_mul_inv, ← Real.exp_neg]
    have e1 : (s - 1).re = s.re - 1 := by simp
    have e2 : (s - 1).im = s.im := by simp
    rw [e1, e2]
    have h1 : ‖X + (τ : ℂ) * d‖ ^ (s.re - 1) ≤ x0 ^ (s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos hx0 hn hs
    have h2 : Real.exp (-(arg (X + (τ : ℂ) * d) * s.im)) ≤ Real.exp (Real.pi / 2 * |s.im|) := by
      refine Real.exp_le_exp.mpr ?_
      have := neg_abs_le (arg (X + (τ : ℂ) * d) * s.im)
      rw [abs_mul] at this
      nlinarith [abs_nonneg (arg (X + (τ : ℂ) * d)), abs_nonneg s.im]
    calc ‖s‖ * (‖X + (τ : ℂ) * d‖ ^ (s.re - 1) * Real.exp (-(arg (X + (τ : ℂ) * d) * s.im))) *
          ‖d‖ ≤ ‖s‖ * (x0 ^ (s.re - 1) * Real.exp (Real.pi / 2 * |s.im|)) * ‖d‖ := by gcongr
      _ = _ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun τ _ => (hder τ).hasDerivWithinAt) hb
  simpa [hf] using this

/-- The dominating function of the `w`-derivative of the integrand of the triangle. -/
noncomputable def i5TriDomD (t : ℝ) (q : ℝ × ℝ) : ℝ := q.2 * (i5X0 t q)⁻¹ * i5TriDomS t q

/-- The first product for the `w`-derivative. -/
noncomputable def i5P5 (q : ℝ × ℝ) : ℝ :=
  i5Dom 0 (-(189 / 200)) (-(209 / 200)) q.1 * i5Dom 0 (-(73 / 200)) (-(213 / 200)) q.2

/-- The second product for the `w`-derivative. -/
noncomputable def i5P6 (q : ℝ × ℝ) : ℝ :=
  i5Dom 0 (-(19 / 20)) (-(21 / 20)) q.1 * i5Dom 0 (1 / 20) (-(21 / 20)) q.2

theorem i5TriDomD_le {t : ℝ} (ht : 0 < t) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    i5TriDomD t (a, c) ≤ Real.exp (-(189 / 100) * Real.log t) * i5P5 (a, c) +
      Real.exp (-(19 / 10) * Real.log t) * i5P6 (a, c) := by
  obtain ⟨f1, f2, f3, -, -, -⟩ := i5_log_facts ht ha hc
  have hU : 0 < 1 + a + c := by linarith
  have hX : 0 < i5X0 t (a, c) := i5X0_pos ht ⟨ha, hc⟩
  have g1 : 2 * Real.log c ≤ Real.log (i5X0 t (a, c)) := by
    rw [← Real.log_rpow hc, Real.rpow_two]
    exact Real.log_le_log (by positivity) (by unfold i5X0; simp only; nlinarith)
  have g2 : Real.log a + Real.log t ≤ Real.log (i5X0 t (a, c)) := by
    rw [← Real.log_mul ha.ne' ht.ne']
    exact Real.log_le_log (by positivity) (by unfold i5X0; simp only; nlinarith)
  have g3 : Real.log c + Real.log t ≤ Real.log (i5X0 t (a, c)) := by
    rw [← Real.log_mul hc.ne' ht.ne']
    exact Real.log_le_log (by positivity) (by unfold i5X0; simp only; nlinarith)
  have e : c * (i5X0 t (a, c))⁻¹ = Real.exp (Real.log c + -Real.log (i5X0 t (a, c))) := by
    rw [Real.exp_add, Real.exp_log hc, Real.exp_neg, Real.exp_log hX]
  unfold i5TriDomD i5TriDomS i5P5 i5P6 i5Dom
  simp only
  rw [e]
  simp only [Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hX, ← Real.exp_add, mul_add]
  refine add_le_add (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_) <;>
    apply i5_le_add_min_add_min <;> linarith

theorem integrableOn_i5P5 : IntegrableOn i5P5 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  integrableOn_i5Dom_prod (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem integrableOn_i5P6 : IntegrableOn i5P6 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
  integrableOn_i5Dom_prod (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The pointwise `w`-difference of the integrand of the triangle. -/
theorem norm_i5TriF_sub_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hw : w.re = t) {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    ‖i5TriF ε t w q - i5TriF ε t (t : ℂ) q‖ ≤
      11 / 10 * Real.exp (Real.pi / 20) * ‖w - t‖ * i5TriDomD t q := by
  have hσ : |ε.re| ≤ 1 / 10 := (abs_re_le_norm ε).trans hε
  have hc : 0 < q.2 := hq.2
  have hU : 0 < 1 + q.1 + q.2 := by
    have := hq.1
    simp only [mem_Ioi] at this
    linarith
  have hX0 := i5X0_pos ht hq
  have hre : (i5X t (t : ℂ) q).re = i5X0 t q := re_i5X (ofReal_re t) q
  have hd : ((q.2 : ℂ) * (w - t)).re = 0 := by simp [hw]
  have hsplit : i5X t w q = i5X t (t : ℂ) q + (q.2 : ℂ) * (w - t) := by unfold i5X; ring
  have hs : (-1 - ε).re - 1 ≤ 0 := by simp; linarith [neg_abs_le ε.re]
  have hM := i5_norm_cpow_sub_le hX0 hre hd hs
  have hsn : ‖-1 - ε‖ ≤ 11 / 10 := by
    have := norm_sub_le (-1 : ℂ) ε
    rw [norm_neg, norm_one] at this
    linarith
  have him : Real.exp (Real.pi / 2 * |(-1 - ε).im|) ≤ Real.exp (Real.pi / 20) := by
    refine Real.exp_le_exp.mpr ?_
    have : |(-1 - ε).im| ≤ 1 / 10 := by
      simp only [sub_im, neg_im, one_im, neg_zero, zero_sub, abs_neg]
      exact (abs_im_le_norm ε).trans hε
    nlinarith [Real.pi_pos]
  have hpow : i5X0 t q ^ ((-1 - ε).re - 1) =
      i5X0 t q ^ (-1 - ε.re) * (i5X0 t q)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hX0]
    congr 1
  have hpair := i5_rpow_pair_le' hU hX0 hσ
  have hdn : ‖(q.2 : ℂ) * (w - t)‖ = q.2 * ‖w - t‖ := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hc]
  unfold i5TriF
  rw [← mul_sub, hsplit, norm_mul, norm_cpow_eq_rpow_re_of_pos hU]
  have e1 : (-1 + 2 * ε).re = -1 + 2 * ε.re := by simp
  rw [e1]
  have hUp : 0 ≤ (1 + q.1 + q.2) ^ (-1 + 2 * ε.re) := Real.rpow_nonneg hU.le _
  calc (1 + q.1 + q.2) ^ (-1 + 2 * ε.re) *
        ‖(i5X t (t : ℂ) q + (q.2 : ℂ) * (w - t)) ^ (-1 - ε) - i5X t (t : ℂ) q ^ (-1 - ε)‖ ≤
      (1 + q.1 + q.2) ^ (-1 + 2 * ε.re) * (‖-1 - ε‖ * ‖(q.2 : ℂ) * (w - t)‖ *
        (i5X0 t q ^ ((-1 - ε).re - 1) * Real.exp (Real.pi / 2 * |(-1 - ε).im|))) := by gcongr
    _ = ‖-1 - ε‖ * Real.exp (Real.pi / 2 * |(-1 - ε).im|) * ‖w - t‖ *
        (q.2 * (i5X0 t q)⁻¹ * ((1 + q.1 + q.2) ^ (-1 + 2 * ε.re) * i5X0 t q ^ (-1 - ε.re))) := by
        rw [hdn, hpow]; ring
    _ ≤ 11 / 10 * Real.exp (Real.pi / 20) * ‖w - t‖ *
        (q.2 * (i5X0 t q)⁻¹ * i5TriDomS t q) := by
        gcongr
        unfold i5TriDomS
        convert hpair using 2
    _ = _ := by unfold i5TriDomD; ring

/-- The constant of the bound on the `w`-difference of the triangle. -/
noncomputable def i5CTD : ℝ :=
  11 / 10 * Real.exp (Real.pi / 20) * ((∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P5 q) +
    ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P6 q)

/-- **The `w`-dependence of the triangle at large `t`**:
`‖i5Tri ε t w - i5Tri ε t t‖ ≤ C ‖w - t‖ t ^ (-189/100)` for `t ≥ 1`, `re w = t`. -/
theorem norm_i5Tri_sub_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {t : ℝ} (ht1 : 1 ≤ t) {w : ℂ}
    (hw : w.re = t) :
    ‖i5Tri ε t w - i5Tri ε t (t : ℂ)‖ ≤ i5CTD * ‖w - t‖ * t ^ (-(189 / 100 : ℝ)) := by
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hε4 : ‖ε‖ ≤ 1 / 4 := by linarith
  have hint : ∀ w' : ℂ, w'.re = t →
      IntegrableOn (i5TriF ε t w') (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := fun w' hw' =>
    ((integrableOn_i5TriDom ht).const_mul (Real.exp (Real.pi / 8))).mono'
      (measurable_i5TriF ε t w').aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem hS fun q hq => norm_i5TriF_le_dom hε4 ht hw' hq)
  have hp : t ^ (-(19 / 10 : ℝ)) ≤ t ^ (-(189 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have e1 : Real.exp (-(189 / 100) * Real.log t) = t ^ (-(189 / 100 : ℝ)) := by
    rw [Real.rpow_def_of_pos ht, mul_comm]
  have e2 : Real.exp (-(19 / 10) * Real.log t) = t ^ (-(19 / 10 : ℝ)) := by
    rw [Real.rpow_def_of_pos ht, mul_comm]
  have hB : IntegrableOn (fun q => t ^ (-(189 / 100 : ℝ)) * i5P5 q +
      t ^ (-(19 / 10 : ℝ)) * i5P6 q) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    (integrableOn_i5P5.const_mul _).add (integrableOn_i5P6.const_mul _)
  have hP5 : 0 ≤ ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P5 q :=
    setIntegral_nonneg hS fun q _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hP6 : 0 ≤ ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P6 q :=
    setIntegral_nonneg hS fun q _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  set K := 11 / 10 * Real.exp (Real.pi / 20) * ‖w - t‖ with hK
  have hK0 : 0 ≤ K := by positivity
  rw [i5Tri_eq, i5Tri_eq, ← integral_sub (hint w hw) (hint (t : ℂ) (ofReal_re t))]
  calc ‖∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), (i5TriF ε t w q - i5TriF ε t (t : ℂ) q)‖ ≤
        ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
          K * (t ^ (-(189 / 100 : ℝ)) * i5P5 q + t ^ (-(19 / 10 : ℝ)) * i5P6 q) := by
        refine norm_integral_le_of_norm_le (hB.const_mul _)
          (ae_restrict_of_forall_mem hS fun q hq => ?_)
        refine (norm_i5TriF_sub_le hε ht hw hq).trans ?_
        rw [← hK]
        gcongr
        obtain ⟨a, c⟩ := q
        rw [← e1, ← e2]
        exact i5TriDomD_le ht hq.1 hq.2
    _ = K * (t ^ (-(189 / 100 : ℝ)) * (∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P5 q) +
          t ^ (-(19 / 10 : ℝ)) * ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P6 q) := by
        rw [integral_const_mul, integral_add (integrableOn_i5P5.const_mul _)
          (integrableOn_i5P6.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ K * (t ^ (-(189 / 100 : ℝ)) * (∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P5 q) +
          t ^ (-(189 / 100 : ℝ)) * ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5P6 q) := by gcongr
    _ = i5CTD * ‖w - t‖ * t ^ (-(189 / 100 : ℝ)) := by rw [hK]; unfold i5CTD; ring

end QED.ThreeLoopD
