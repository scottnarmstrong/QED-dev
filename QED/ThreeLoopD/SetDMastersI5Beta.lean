/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Large
public import QED.DimReg.BetaPrime

/-!
# Set (d), master `I₅`: the hard-region constant of the triangle

The hard region of the triangle at large `t` produces the subtracted integral

  `H = ∫₀¹ h + ∫₁^∞ (h - s ^ (-1 + ε))`, `h(s) = (1 + s) ^ (-1 + 2ε) s ^ (-ε)`
  (`QED.ThreeLoopD.i5Hc`),

and `ε H = 1 - G`, `G = Γ(1 - ε)² / Γ(1 - 2ε)` (`QED.ThreeLoopD.i5Hc_eq`), for `0 < ‖ε‖ ≤ 1/10`,
with no analytic continuation: `F(s) = s ^ (1 - ε) (1 + s) ^ (-1 + 2ε)` has
`F' = ε h + (1 - 2ε) β`, `β(s) = s ^ (-ε) (1 + s) ^ (-2 + 2ε)`, and `F(s) - s ^ ε → 0` at
infinity, so `ε H + (1 - 2ε) ∫₀^∞ β = 1`, while `∫₀^∞ β = Γ(1 - ε)² / Γ(2 - 2ε)` is a convergent
Beta integral (`QED.DimReg.integral_betaPrime`).

Two general tools: the derivative of `x ↦ (a + b x) ^ c` and the mean-value bound
`‖y₁ ^ c - y₀ ^ c‖ ≤ ‖c‖ (y₁ - y₀) y₀ ^ (re c - 1)` for `0 < y₀ ≤ y₁`, `re c ≤ 1`
(`QED.ThreeLoopD.i5_norm_ofReal_cpow_sub_le`).

## Main results

* `QED.ThreeLoopD.i5_norm_ofReal_cpow_sub_le`, `QED.ThreeLoopD.norm_i5Dh_le`.
* `QED.ThreeLoopD.i5Hc_eq`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.ThreeLoopD

/-! ### Tools -/

theorem i5_cpow_add_one {x : ℂ} (hx : x ≠ 0) (c : ℂ) : x ^ (c + 1) = x ^ c * x := by
  rw [cpow_add _ _ hx, cpow_one]

theorem i5_hasDerivAt_cpow_affine (a b : ℝ) (c : ℂ) {s : ℝ} (h : 0 < a + b * s) :
    HasDerivAt (fun x : ℝ => ((a + b * x : ℝ) : ℂ) ^ c)
      (c * ((a + b * s : ℝ) : ℂ) ^ (c - 1) * b) s := by
  have hl : HasDerivAt (fun x : ℝ => ((a + b * x : ℝ) : ℂ)) (b : ℂ) s := by
    have := (((hasDerivAt_id s).const_mul b).const_add a).ofReal_comp
    simpa using this
  exact (Complex.hasStrictDerivAt_cpow_const (ofReal_mem_slitPlane.mpr h)).hasDerivAt.comp s hl

/-- **The mean-value bound for real powers with complex exponent.** -/
theorem i5_norm_ofReal_cpow_sub_le {y₀ y₁ : ℝ} (h0 : 0 < y₀) (h01 : y₀ ≤ y₁) {c : ℂ}
    (hc : c.re ≤ 1) :
    ‖(y₁ : ℂ) ^ c - (y₀ : ℂ) ^ c‖ ≤ ‖c‖ * (y₁ - y₀) * y₀ ^ (c.re - 1) := by
  have hpos : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < y₀ + (y₁ - y₀) * τ := fun τ hτ => by
    nlinarith [hτ.1]
  have hb : ∀ τ ∈ Ico (0 : ℝ) 1,
      ‖c * ((y₀ + (y₁ - y₀) * τ : ℝ) : ℂ) ^ (c - 1) * ((y₁ - y₀ : ℝ) : ℂ)‖ ≤
        ‖c‖ * (y₁ - y₀) * y₀ ^ (c.re - 1) := fun τ hτ => by
    have hp := hpos τ (Ico_subset_Icc_self hτ)
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hp, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    have e : (c - 1).re = c.re - 1 := by simp
    rw [e]
    have h1 : (y₀ + (y₁ - y₀) * τ) ^ (c.re - 1) ≤ y₀ ^ (c.re - 1) :=
      Real.rpow_le_rpow_of_nonpos h0 (by nlinarith [hτ.1]) (by linarith)
    have h2 : 0 ≤ y₁ - y₀ := by linarith
    calc ‖c‖ * (y₀ + (y₁ - y₀) * τ) ^ (c.re - 1) * (y₁ - y₀) ≤
          ‖c‖ * y₀ ^ (c.re - 1) * (y₁ - y₀) := by gcongr
      _ = _ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun τ : ℝ => ((y₀ + (y₁ - y₀) * τ : ℝ) : ℂ) ^ c)
    (fun τ hτ => (i5_hasDerivAt_cpow_affine y₀ (y₁ - y₀) c (hpos τ hτ)).hasDerivWithinAt) hb
  simpa using this

theorem i5_measurable_cpow (c : ℂ) : Measurable fun s : ℝ => (s : ℂ) ^ c :=
  measurable_ofReal.pow_const c

theorem i5_measurable_cpow_affine (a b : ℝ) (c : ℂ) :
    Measurable fun s : ℝ => ((a + b * s : ℝ) : ℂ) ^ c :=
  (measurable_ofReal.comp (measurable_const.add (measurable_const.mul measurable_id))).pow_const c

/-! ### The functions -/

/-- The hard-region integrand `h(s) = (1 + s) ^ (-1 + 2ε) s ^ (-ε)`. -/
noncomputable def i5h (ε : ℂ) (s : ℝ) : ℂ := ((1 + s : ℝ) : ℂ) ^ (-1 + 2 * ε) * (s : ℂ) ^ (-ε)

/-- `(1 + s) ^ (-1 + 2ε) - s ^ (-1 + 2ε)`. -/
noncomputable def i5Dh (ε : ℂ) (s : ℝ) : ℂ :=
  ((1 + s : ℝ) : ℂ) ^ (-1 + 2 * ε) - (s : ℂ) ^ (-1 + 2 * ε)

/-- The subtracted integrand `h(s) - s ^ (-1 + ε) = (i5Dh) s ^ (-ε)`. -/
noncomputable def i5h1 (ε : ℂ) (s : ℝ) : ℂ := i5Dh ε s * (s : ℂ) ^ (-ε)

/-- **The hard-region constant** `H = ∫₀¹ h + ∫₁^∞ (h - s ^ (-1 + ε))`. -/
noncomputable def i5Hc (ε : ℂ) : ℂ := (∫ s in Ioo (0 : ℝ) 1, i5h ε s) + ∫ s in Ioi (1 : ℝ), i5h1 ε s

/-- The Beta integrand `β(s) = s ^ (-ε) (1 + s) ^ (-2 + 2ε)`. -/
noncomputable def i5Be (ε : ℂ) (s : ℝ) : ℂ := (s : ℂ) ^ (-ε) * ((1 + s : ℝ) : ℂ) ^ (-2 + 2 * ε)

/-- The antiderivative `F(s) = s ^ (1 - ε) (1 + s) ^ (-1 + 2ε)`. -/
noncomputable def i5F (ε : ℂ) (s : ℝ) : ℂ := (s : ℂ) ^ (1 - ε) * ((1 + s : ℝ) : ℂ) ^ (-1 + 2 * ε)

theorem i5_re_facts {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) : |ε.re| ≤ 1 / 10 ∧ -(1 / 10) ≤ ε.re ∧
    ε.re ≤ 1 / 10 := by
  have h := (abs_re_le_norm ε).trans hε
  exact ⟨h, by linarith [neg_abs_le ε.re], by linarith [le_abs_self ε.re]⟩

theorem i5h_eq_h1_add {ε : ℂ} {s : ℝ} (hs : 0 < s) :
    i5h ε s = i5h1 ε s + (s : ℂ) ^ (-1 + ε) := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have e : (s : ℂ) ^ (-1 + ε) = (s : ℂ) ^ (-1 + 2 * ε) * (s : ℂ) ^ (-ε) := by
    rw [← cpow_add _ _ hs0]; ring_nf
  rw [e, i5h1, i5Dh, i5h]; ring

/-- `‖(1 + s) ^ (-1 + 2ε) - s ^ (-1 + 2ε)‖ ≤ (6/5) s ^ (-9/5)` for `s ≥ 1`. -/
theorem norm_i5Dh_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {s : ℝ} (hs : 1 ≤ s) :
    ‖i5Dh ε s‖ ≤ 6 / 5 * s ^ (-(9 / 5 : ℝ)) := by
  obtain ⟨-, h1, h2⟩ := i5_re_facts hε
  have hs0 : 0 < s := by linarith
  have hre : (-1 + 2 * ε).re = -1 + 2 * ε.re := by simp
  have hM := i5_norm_ofReal_cpow_sub_le hs0 (by linarith : s ≤ 1 + s) (c := -1 + 2 * ε)
    (by rw [hre]; linarith)
  rw [hre] at hM
  have hn : ‖-1 + 2 * ε‖ ≤ 6 / 5 := by
    have := norm_add_le (-1 : ℂ) (2 * ε)
    rw [norm_neg, norm_one, norm_mul, Complex.norm_ofNat] at this
    linarith
  have hp : s ^ (-1 + 2 * ε.re - 1) ≤ s ^ (-(9 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  unfold i5Dh
  calc _ ≤ ‖-1 + 2 * ε‖ * (1 + s - s) * s ^ (-1 + 2 * ε.re - 1) := hM
    _ ≤ 6 / 5 * 1 * s ^ (-(9 / 5 : ℝ)) := by
        rw [show 1 + s - s = 1 by ring]
        gcongr
    _ = _ := by ring

theorem norm_i5h1_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {s : ℝ} (hs : 1 ≤ s) :
    ‖i5h1 ε s‖ ≤ 6 / 5 * s ^ (-(17 / 10 : ℝ)) := by
  obtain ⟨-, h1, -⟩ := i5_re_facts hε
  have hs0 : 0 < s := by linarith
  rw [i5h1, norm_mul, norm_cpow_eq_rpow_re_of_pos hs0]
  have hp : s ^ (-ε).re ≤ s ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow_of_exponent_le hs (by simp; linarith)
  calc ‖i5Dh ε s‖ * s ^ (-ε).re ≤ 6 / 5 * s ^ (-(9 / 5 : ℝ)) * s ^ ((1 : ℝ) / 10) :=
        mul_le_mul (norm_i5Dh_le hε hs) hp (Real.rpow_nonneg hs0.le _) (by positivity)
    _ = 6 / 5 * s ^ (-(17 / 10 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hs0]; norm_num

theorem norm_i5h_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖i5h ε s‖ ≤ s ^ (-(1 / 10 : ℝ)) := by
  obtain ⟨-, h1, h2⟩ := i5_re_facts hε
  have h1s : 0 < 1 + s := by linarith [hs.1]
  rw [i5h, norm_mul, norm_cpow_eq_rpow_re_of_pos h1s, norm_cpow_eq_rpow_re_of_pos hs.1]
  have hA : (1 + s) ^ (-1 + 2 * ε).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hs.1]) (by simp; linarith)
  have hB : s ^ (-ε).re ≤ s ^ (-(1 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by simp; linarith)
  calc (1 + s) ^ (-1 + 2 * ε).re * s ^ (-ε).re ≤ 1 * s ^ (-(1 / 10 : ℝ)) :=
        mul_le_mul hA hB (Real.rpow_nonneg hs.1.le _) zero_le_one
    _ = _ := one_mul _

theorem norm_i5Be_eq (ε : ℂ) {s : ℝ} (hs : 0 < s) :
    ‖i5Be ε s‖ = s ^ (-ε.re) * (1 + s) ^ (-2 + 2 * ε.re) := by
  have h1s : 0 < 1 + s := by linarith
  rw [i5Be, norm_mul, norm_cpow_eq_rpow_re_of_pos h1s, norm_cpow_eq_rpow_re_of_pos hs]
  simp

theorem i5_measurable_cpow_one_add (c : ℂ) :
    Measurable fun s : ℝ => ((1 + s : ℝ) : ℂ) ^ c :=
  (measurable_ofReal.comp (measurable_const.add measurable_id)).pow_const c

theorem measurable_i5h (ε : ℂ) : Measurable (i5h ε) :=
  (i5_measurable_cpow_one_add _).mul (i5_measurable_cpow _)

theorem measurable_i5h1 (ε : ℂ) : Measurable (i5h1 ε) :=
  ((i5_measurable_cpow_one_add _).sub (i5_measurable_cpow _)).mul (i5_measurable_cpow _)

theorem i5Be_eq_betaPrime (ε : ℂ) (s : ℝ) :
    i5Be ε s = QED.DimReg.betaPrimeIntegrand (1 - ε) (1 - ε) 1 s := by
  unfold i5Be QED.DimReg.betaPrimeIntegrand
  rw [one_mul]
  congr 2 <;> ring

theorem integrableOn_i5Be {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) : IntegrableOn (i5Be ε) (Ioi 0) := by
  obtain ⟨-, -, h2⟩ := i5_re_facts hε
  have hr : 0 < (1 - ε).re := by simp; linarith
  have := QED.DimReg.integrableOn_betaPrime hr hr one_pos
  exact this.congr_fun (fun s _ => (i5Be_eq_betaPrime ε s).symm) measurableSet_Ioi

theorem integral_i5Be {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) :
    (1 - 2 * ε) * ∫ s in Ioi (0 : ℝ), i5Be ε s = i13G ε := by
  obtain ⟨-, -, h2⟩ := i5_re_facts hε
  have hr : 0 < (1 - ε).re := by simp; linarith
  have h12 : (1 : ℂ) - 2 * ε ≠ 0 := (i13_eps_facts (by linarith)).2.2.2.1
  have := QED.DimReg.integral_betaPrime hr hr one_pos
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => i5Be_eq_betaPrime ε s), this,
    ofReal_one, one_cpow, one_mul, show (1 : ℂ) - ε + (1 - ε) = (1 - 2 * ε) + 1 by ring,
    Gamma_add_one _ h12, i13G]
  rw [← sq, mul_div_assoc', mul_div_mul_left _ _ h12]

/-! ### The derivative of `F` -/

theorem hasDerivAt_i5F {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (i5F ε) (ε * i5h ε s + (1 - 2 * ε) * i5Be ε s) s := by
  obtain ⟨-, -, h2⟩ := i5_re_facts hε
  have h1e : (1 : ℂ) - ε ≠ 0 := fun h => by
    have := congr_arg re h; simp at this; linarith
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have h1s : (0 : ℝ) < 1 + 1 * s := by linarith
  have hA := hasDerivAt_ofReal_cpow_const hs.ne' h1e
  have hB := i5_hasDerivAt_cpow_affine 1 1 (-1 + 2 * ε) h1s
  simp only [one_mul, ofReal_one, mul_one] at hB
  have h1s' : ((1 + s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  refine (hA.mul hB).congr_deriv ?_
  have e1 : (s : ℂ) ^ (1 - ε - 1) = (s : ℂ) ^ (-ε) := by ring_nf
  have e2 : (-1 + 2 * ε - 1) = -2 + 2 * ε := by ring
  have e3 : (s : ℂ) ^ (1 - ε) = (s : ℂ) ^ (-ε) * s := by
    rw [← i5_cpow_add_one hs0]; ring_nf
  have e4 : ((1 + s : ℝ) : ℂ) ^ (-1 + 2 * ε) = ((1 + s : ℝ) : ℂ) ^ (-2 + 2 * ε) * (1 + s) := by
    rw [show (-1 : ℂ) + 2 * ε = -2 + 2 * ε + 1 by ring, i5_cpow_add_one h1s']; push_cast; ring
  rw [e1, e2, e3, e4, i5h, i5Be, e4]
  ring

theorem continuousAt_i5F {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousAt (i5F ε) s := by
  obtain ⟨-, -, h2⟩ := i5_re_facts hε
  have hA := continuousAt_ofReal_cpow_const s (1 - ε) (Or.inl (by simp; linarith))
  have hB : ContinuousAt (fun x : ℝ => ((1 + x : ℝ) : ℂ) ^ (-1 + 2 * ε)) s :=
    (continuousAt_ofReal_cpow_const (1 + s) _ (Or.inr (by linarith))).comp
      (continuous_const.add continuous_id).continuousAt
  exact hA.mul hB

theorem i5F_zero {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) : i5F ε 0 = 0 := by
  obtain ⟨-, -, h2⟩ := i5_re_facts hε
  have h1e : (1 : ℂ) - ε ≠ 0 := fun h => by
    have := congr_arg re h; simp at this; linarith
  simp [i5F, zero_cpow h1e]

theorem i5F_one (ε : ℂ) : i5F ε 1 = (2 : ℂ) ^ (-1 + 2 * ε) := by
  simp [i5F]; norm_num

/-! ### The identity -/

theorem integrableOn_i5h {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) : IntegrableOn (i5h ε) (Ioo 0 1) := by
  refine ((integrableOn_rpow_Ioo (by norm_num : (-1 : ℝ) < -(1 / 10))).mono'
    (measurable_i5h ε).aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => norm_i5h_le hε hs))

theorem integrableOn_i5h1 {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) : IntegrableOn (i5h1 ε) (Ioi 1) :=
  ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(17 / 10 : ℝ) < -1) one_pos).const_mul
    (6 / 5)).mono' (measurable_i5h1 ε).aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => norm_i5h1_le hε (le_of_lt hs))

/-- `∫₀¹ (ε h + (1 - 2ε) β) = F(1)`. -/
theorem integral_i5_Ioo {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) :
    ε * (∫ s in Ioo (0 : ℝ) 1, i5h ε s) + (1 - 2 * ε) * ∫ s in Ioo (0 : ℝ) 1, i5Be ε s =
      (2 : ℂ) ^ (-1 + 2 * ε) := by
  have hI1 := (integrableOn_i5h hε).const_mul ε
  have hI2 := ((integrableOn_i5Be hε).mono_set
    (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0)).const_mul (1 - 2 * ε)
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (fun s hs => (continuousAt_i5F hε hs.1).continuousWithinAt)
    (fun s hs => hasDerivAt_i5F hε hs.1)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr (hI1.add hI2))
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_add hI1 hI2, integral_const_mul, integral_const_mul, i5F_zero hε, i5F_one,
    sub_zero] at hF
  exact hF

/-- `F(s) - s ^ ε = s ^ (1 - ε) (i5Dh)`. -/
theorem i5F_sub_eq {ε : ℂ} {s : ℝ} (hs : 0 < s) :
    i5F ε s - (s : ℂ) ^ ε = (s : ℂ) ^ (1 - ε) * i5Dh ε s := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have e : (s : ℂ) ^ ε = (s : ℂ) ^ (1 - ε) * (s : ℂ) ^ (-1 + 2 * ε) := by
    rw [← cpow_add _ _ hs0]; ring_nf
  rw [e, i5F, i5Dh]; ring

theorem tendsto_i5F_sub {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) :
    Tendsto (fun s : ℝ => i5F ε s - (s : ℂ) ^ ε) atTop (𝓝 0) := by
  obtain ⟨-, -, h2⟩ := i5_re_facts hε
  have hT : Tendsto (fun s : ℝ => 6 / 5 * s ^ (-(7 / 10 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 10)).const_mul (6 / 5)
  refine squeeze_zero_norm' ?_ hT
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hs0 : 0 < s := by linarith
  rw [i5F_sub_eq hs0, norm_mul, norm_cpow_eq_rpow_re_of_pos hs0]
  have hp : s ^ (1 - ε).re ≤ s ^ ((11 : ℝ) / 10) :=
    Real.rpow_le_rpow_of_exponent_le hs (by simp; linarith [(i5_re_facts hε).2.1])
  calc s ^ (1 - ε).re * ‖i5Dh ε s‖ ≤ s ^ ((11 : ℝ) / 10) * (6 / 5 * s ^ (-(9 / 5 : ℝ))) :=
        mul_le_mul hp (norm_i5Dh_le hε hs) (norm_nonneg _) (by positivity)
    _ = 6 / 5 * s ^ (-(7 / 10 : ℝ)) := by
        rw [mul_left_comm, ← Real.rpow_add hs0]; norm_num

/-- `∫₁^∞ (ε (h - s ^ (-1 + ε)) + (1 - 2ε) β) = 1 - F(1)`. -/
theorem integral_i5_Ioi {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) (h0 : ε ≠ 0) :
    ε * (∫ s in Ioi (1 : ℝ), i5h1 ε s) + (1 - 2 * ε) * ∫ s in Ioi (1 : ℝ), i5Be ε s =
      1 - (2 : ℂ) ^ (-1 + 2 * ε) := by
  have hI1 := (integrableOn_i5h1 hε).const_mul ε
  have hI2 := ((integrableOn_i5Be hε).mono_set (Ioi_subset_Ioi zero_le_one)).const_mul
    (1 - 2 * ε)
  have hd : ∀ s ∈ Ioi (1 : ℝ), HasDerivAt (fun s : ℝ => i5F ε s - (s : ℂ) ^ ε)
      (ε * i5h1 ε s + (1 - 2 * ε) * i5Be ε s) s := fun s hs => by
    have hs0 : 0 < s := zero_lt_one.trans hs
    refine ((hasDerivAt_i5F hε hs0).sub (hasDerivAt_ofReal_cpow_const hs0.ne' h0)).congr_deriv ?_
    rw [i5h_eq_h1_add hs0, show ε - 1 = -1 + ε by ring]
    ring
  have hc : ContinuousWithinAt (fun s : ℝ => i5F ε s - (s : ℂ) ^ ε) (Ici 1) 1 :=
    ((continuousAt_i5F hε zero_le_one).sub
      (continuousAt_ofReal_cpow_const 1 ε (Or.inr one_ne_zero))).continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc hd (hI1.add hI2) (tendsto_i5F_sub hε)
  rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, i5F_one] at h
  rw [h]; simp

/-- **The hard-region constant**: `ε H = 1 - G`. -/
theorem i5Hc_eq {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) (h0 : ε ≠ 0) : ε * i5Hc ε = 1 - i13G ε := by
  have hB := integral_i5Be hε
  have hI := integrableOn_i5Be hε
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi (hI.mono_set Ioc_subset_Ioi_self)
    (hI.mono_set (Ioi_subset_Ioi zero_le_one)), integral_Ioc_eq_integral_Ioo] at hB
  have h1 := integral_i5_Ioo hε
  have h2 := integral_i5_Ioi hε h0
  rw [i5Hc, ← hB]
  linear_combination h1 + h2

end QED.ThreeLoopD
