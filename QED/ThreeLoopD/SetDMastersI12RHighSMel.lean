/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12Def
public import QED.DimReg.BetaPrimeNested

/-!
# Set (d), master `I₁₂`: the Mellin transform of the kernel of the bulk remainder

After the reflection of the sectors (`QED.ThreeLoopD.SetDMastersI12RHighSCov`) the main term of
the bulk part `S` of the remainder of `I₁₂` is, at fixed `(x, u)`, an integral over
`s ∈ (0, ∞)` of `s ^ (2ε - 1) φ(s c)`, with `φ(r) = Φ₀(r, 1) = ((1 + r) ^ a - r ^ a - 1) / r`,
`a = 2 - 3ε` and a scale `c > 0`. Its "good" part (`s` over all of `(0, ∞)`, with the face
subtractions `a` at `s < 1` and `a (sc) ^ (-3ε)` at `s ≥ 1`) is evaluated here in closed form for
`0 < re ε < 1/3`, where every piece converges absolutely; no analytic continuation is used.

**`φ` as a double integral.** For `r > 0`,
`φ(r) = a (a - 1) ∫_{(0,1)²} (t + r σ) ^ (-3ε) d(t, σ)` (two elementary integrations).

**Mellin transform.** For fixed `(t, σ)`, `r ^ (2ε - 1) (t + r σ) ^ (-3ε)` is
`t ^ (-3ε)` times the Beta integrand of the second kind with scale `σ / t`, so by the iterated
Beta lemma `QED.DimReg.integral_prod_betaPrime` and Fubini,

  `M_φ = ∫₀^∞ r ^ (2ε - 1) φ(r) dr = a (a - 1) / ((1 - ε)(1 - 2ε)) · Γ(2ε) Γ(ε) / Γ(3ε)`

(`= Γ(2ε - 1) Γ(ε - 1) / Γ(3ε - 2)`).

**The subtracted integral.** Scaling `r = sc` and `∫₀¹ s ^ (2ε - 1) = 1/(2ε)`,
`∫₁^∞ s ^ (-ε - 1) = 1/ε` give

  `∫₀^∞ s ^ (2ε - 1) (φ(sc) - a 1_{s < 1} - a (sc) ^ (-3ε) 1_{s ≥ 1}) ds
    = c ^ (-2ε) M_φ - a / (2ε) - a c ^ (-3ε) / ε`.

## Main results

* `QED.ThreeLoopD.i12HS_phi_eq_integral`: the double-integral representation of `φ`.
* `QED.ThreeLoopD.i12HS_mellin`: the Mellin transform `M_φ` (`QED.ThreeLoopD.i12HSMphi`).
* `QED.ThreeLoopD.i12HS_psi`: the subtracted `s`-integral at scale `c`
  (`QED.ThreeLoopD.i12HSD`, `QED.ThreeLoopD.i12HSPsi`).
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- The derivative of `x ↦ (p + q x) ^ c` where `p + q x > 0`. -/
theorem i12HS_hasDerivAt_cpow_affine (p q : ℝ) (c : ℂ) {x : ℝ} (h : 0 < p + q * x) :
    HasDerivAt (fun y : ℝ => ((p + q * y : ℝ) : ℂ) ^ c)
      (c * ((p + q * x : ℝ) : ℂ) ^ (c - 1) * q) x := by
  have hl : HasDerivAt (fun y : ℝ => ((p + q * y : ℝ) : ℂ)) (q : ℂ) x := by
    have := (((hasDerivAt_id x).const_mul q).const_add p).ofReal_comp
    simpa using this
  exact (Complex.hasStrictDerivAt_cpow_const (ofReal_mem_slitPlane.mpr h)).hasDerivAt.comp x hl


/-- The inner integral:
`∫₀¹ (t + r σ) ^ (-3ε) dσ = ((t + r) ^ (1 - 3ε) - t ^ (1 - 3ε)) / ((1 - 3ε) r)`. -/
theorem i12HS_integral_sigma (ε : ℂ) (hb : 1 - 3 * ε ≠ 0) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    ∫ σ in Ioo (0 : ℝ) 1, ((t + r * σ : ℝ) : ℂ) ^ (-3 * ε) =
      ((((t + r : ℝ) : ℂ) ^ (1 - 3 * ε) - (t : ℂ) ^ (1 - 3 * ε)) / ((1 - 3 * ε) * r)) := by
  have hpos : ∀ x ∈ uIcc (0 : ℝ) 1, 0 < t + r * x := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx
    nlinarith [hx.1]
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun y : ℝ => ((t + r * y : ℝ) : ℂ) ^ (1 - 3 * ε) / ((1 - 3 * ε) * r))
      (((t + r * x : ℝ) : ℂ) ^ (-3 * ε)) x := fun x hx => by
    have h := (i12HS_hasDerivAt_cpow_affine t r (1 - 3 * ε) (hpos x hx)).div_const
      ((1 - 3 * ε) * r)
    convert h using 1
    have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    rw [show 1 - 3 * ε - 1 = -3 * ε by ring]
    field_simp
  have hc : ContinuousOn (fun x : ℝ => ((t + r * x : ℝ) : ℂ) ^ (-3 * ε)) (uIcc 0 1) :=
    fun x hx => (i12HS_hasDerivAt_cpow_affine t r (-3 * ε) (hpos x hx)).continuousAt
      |>.continuousWithinAt
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp only [mul_zero, add_zero, mul_one]
  ring


/-- The outer integral: `∫₀¹ ((t + r) ^ (1 - 3ε) - t ^ (1 - 3ε)) dt`
`= ((1 + r) ^ (2 - 3ε) - r ^ (2 - 3ε) - 1) / (2 - 3ε)`. -/
theorem i12HS_integral_t {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioo (0 : ℝ) 1, (((t + r : ℝ) : ℂ) ^ (1 - 3 * ε) - (t : ℂ) ^ (1 - 3 * ε)) =
      (((1 + r : ℝ) : ℂ) ^ (2 - 3 * ε) - (r : ℂ) ^ (2 - 3 * ε) - 1) / (2 - 3 * ε) := by
  have ha : (2 - 3 * ε) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hare : 0 < (2 - 3 * ε).re := by simp; linarith
  have hbre : 0 < (1 - 3 * ε).re := by simp; linarith
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < r + 1 * x := fun x hx => by linarith [hx.1]
  set F : ℝ → ℂ := fun x => (((r + x : ℝ) : ℂ) ^ (2 - 3 * ε) - (x : ℂ) ^ (2 - 3 * ε)) /
    (2 - 3 * ε) with hF
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F
      (((x + r : ℝ) : ℂ) ^ (1 - 3 * ε) - (x : ℂ) ^ (1 - 3 * ε)) x := fun x hx => by
    have h1' := i12HS_hasDerivAt_cpow_affine r 1 (2 - 3 * ε) (hpos x (Ioo_subset_Icc_self hx))
    have h2' := i12HS_hasDerivAt_cpow_affine 0 1 (2 - 3 * ε) (x := x) (by linarith [hx.1])
    have h3 := (h1'.sub h2').div_const (2 - 3 * ε)
    simp only [zero_add, one_mul, ofReal_one, mul_one] at h3
    convert h3 using 1
    rw [show 2 - 3 * ε - 1 = 1 - 3 * ε by ring, add_comm x r]
    field_simp
  have hc : ContinuousOn F (Icc 0 1) := fun x hx => by
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) _
    · have := (i12HS_hasDerivAt_cpow_affine r 1 (2 - 3 * ε) (hpos x hx)).continuousAt
      simpa only [one_mul] using this
    · exact continuousAt_ofReal_cpow_const x _ (Or.inl hare)
  have hi : IntervalIntegrable
      (fun x : ℝ => ((x + r : ℝ) : ℂ) ^ (1 - 3 * ε) - (x : ℂ) ^ (1 - 3 * ε)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable fun x hx => ContinuousAt.continuousWithinAt ?_
    rw [uIcc_of_le zero_le_one] at hx
    refine ContinuousAt.sub ?_ (continuousAt_ofReal_cpow_const x _ (Or.inl hbre))
    have := (i12HS_hasDerivAt_cpow_affine r 1 (1 - 3 * ε) (hpos x hx)).continuousAt
    simpa only [one_mul, add_comm r] using this
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hi]
  simp only [hF, add_zero, ofReal_one, one_cpow, ofReal_zero,
    zero_cpow (fun h => ha h), sub_zero, add_comm r 1]
  ring

/-- **`φ` as a double integral**: for `r > 0` and `0 < re ε < 1/3`,
`Φ₀(r, 1) = (2 - 3ε)(1 - 3ε) ∫_{(0,1)²} (t + r σ) ^ (-3ε) d(t, σ)`, absolutely convergent. -/
theorem i12HS_phi_eq_integral {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3) {r : ℝ}
    (hr : 0 < r) :
    IntegrableOn (fun w : ℝ × ℝ => ((w.1 + r * w.2 : ℝ) : ℂ) ^ (-3 * ε))
        (Ioo 0 1 ×ˢ Ioo 0 1) ∧
      i12Phi0 ε r 1 = (2 - 3 * ε) * (1 - 3 * ε) *
        ∫ w in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ((w.1 + r * w.2 : ℝ) : ℂ) ^ (-3 * ε) := by
  have hb : (1 - 3 * ε) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h1d : IntegrableOn (fun t : ℝ => t ^ (-3 * ε.re)) (Ioo 0 1) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -3 * ε.re)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.mono_set Ioo_subset_Ioc_self
  have hg : IntegrableOn (fun w : ℝ × ℝ => w.1 ^ (-3 * ε.re) * (1 : ℝ))
      (Ioo 0 1 ×ˢ Ioo 0 1) := by
    unfold IntegrableOn
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact h1d.mul_prod (integrableOn_const (by simp))
  have hI : IntegrableOn (fun w : ℝ × ℝ => ((w.1 + r * w.2 : ℝ) : ℂ) ^ (-3 * ε))
      (Ioo 0 1 ×ˢ Ioo 0 1) := by
    refine hg.mono' ?_ ?_
    · exact (by fun_prop : Measurable fun w : ℝ × ℝ => ((w.1 + r * w.2 : ℝ) : ℂ) ^ (-3 * ε))
        |>.aestronglyMeasurable
    · refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 ?_
      refine Filter.Eventually.of_forall fun w hw => ?_
      obtain ⟨⟨ht0, -⟩, ⟨hs0, -⟩⟩ := hw
      rw [norm_cpow_eq_rpow_re_of_pos (by positivity), mul_one]
      simp only [neg_mul, mul_re, neg_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      rw [← neg_mul]
      exact Real.rpow_le_rpow_of_nonpos ht0 (by nlinarith) (by linarith)
  refine ⟨hI, ?_⟩
  rw [Measure.volume_eq_prod] at hI
  rw [Measure.volume_eq_prod, setIntegral_prod _ hI, setIntegral_congr_fun measurableSet_Ioo
    (fun t ht => i12HS_integral_sigma ε hb hr ht.1), integral_div, i12HS_integral_t h0 h1 hr]
  have ha : (2 - 3 * ε) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  simp only [i12Phi0, mul_one, ofReal_one, one_cpow, add_comm r 1]
  field_simp

/-- `∫₀¹ x ^ r dx = 1 / (r + 1)` and the integrand is integrable on `(0, 1)`, for `-1 < re r`. -/
theorem i12HS_cpow_unit {r : ℂ} (hr : -1 < r.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ r) (Ioo 0 1) ∧
      ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ r = 1 / (r + 1) := by
  have hi := intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hr
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hi
  refine ⟨hi.mono_set Ioo_subset_Ioc_self, ?_⟩
  have hr1 : r + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl hr), ofReal_one, one_cpow, ofReal_zero, zero_cpow hr1, sub_zero]

/-- **The Mellin transform of `φ = Φ₀(·, 1)` at `2ε`**: for `0 < re ε < 1/3`,
`∫₀^∞ r ^ (2ε - 1) Φ₀(r, 1) dr = (2 - 3ε)(1 - 3ε) / ((1 - ε)(1 - 2ε)) · Γ(2ε) Γ(ε) / Γ(3ε)`,
absolutely convergent. -/
theorem i12HS_mellin {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ (2 * ε - 1) * i12Phi0 ε r 1) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (2 * ε - 1) * i12Phi0 ε r 1 =
        (2 - 3 * ε) * (1 - 3 * ε) / ((1 - ε) * (1 - 2 * ε)) *
          (Gamma (2 * ε) * Gamma ε / Gamma (2 * ε + ε)) := by
  set S : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1 with hSd
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  set F : ℝ × (ℝ × ℝ) → ℂ := fun z =>
    (z.1 : ℂ) ^ (2 * ε - 1) * ((z.2.1 + z.1 * z.2.2 : ℝ) : ℂ) ^ (-3 * ε) with hFd
  have hFm : Measurable F := by rw [hFd]; fun_prop
  have ha : 0 < (2 * ε).re := by simp; linarith
  have hF : ∀ t : ℝ, 0 < t → ∀ w ∈ S, F (t, w) = (w.1 : ℂ) ^ (-3 * ε) *
      DimReg.betaPrimeIntegrand (2 * ε) ε (w.2 * w.1⁻¹) t := by
    intro t ht w hw
    obtain ⟨⟨hw1, -⟩, ⟨hw2, -⟩⟩ := hw
    simp only [hFd, DimReg.betaPrimeIntegrand]
    have e : w.1 + t * w.2 = w.1 * (1 + w.2 * w.1⁻¹ * t) := by field_simp
    rw [e, DimReg.cpow_ofReal_mul hw1.le (by positivity),
      show -(2 * ε + ε) = -3 * ε by ring]
    ring
  have hAe : ∀ w ∈ S, (w.1 : ℂ) ^ (-3 * ε) * ((w.2 * w.1⁻¹ : ℝ) : ℂ) ^ (-(2 * ε)) =
      (w.1 : ℂ) ^ (-ε) * (w.2 : ℂ) ^ (-(2 * ε)) := by
    intro w hw
    obtain ⟨⟨hw1, -⟩, ⟨hw2, -⟩⟩ := hw
    rw [DimReg.ofReal_mul_inv_cpow hw2.le hw1, neg_neg]
    have h1' : (w.1 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw1.ne'
    rw [mul_left_comm, ← cpow_add _ _ h1', show -3 * ε + 2 * ε = -ε by ring, mul_comm]
  obtain ⟨it, vt⟩ := i12HS_cpow_unit (r := -ε) (by simp; linarith)
  obtain ⟨is, vs⟩ := i12HS_cpow_unit (r := -(2 * ε)) (by simp; linarith)
  have hP : IntegrableOn (fun w : ℝ × ℝ => (w.1 : ℂ) ^ (-ε) * (w.2 : ℂ) ^ (-(2 * ε))) S := by
    unfold IntegrableOn
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact it.mul_prod is
  have hA : IntegrableOn (fun w : ℝ × ℝ =>
      (w.1 : ℂ) ^ (-3 * ε) * ((w.2 * w.1⁻¹ : ℝ) : ℂ) ^ (-(2 * ε))) S :=
    hP.congr_fun (fun w hw => (hAe w hw).symm) hS
  have hc : ∀ w ∈ S, 0 < w.2 * w.1⁻¹ := fun w hw => by
    obtain ⟨⟨hw1, -⟩, ⟨hw2, -⟩⟩ := hw
    positivity
  have hI := DimReg.integrableOn_prod_betaPrime (μ := volume) hS ha h0
    hFm.aestronglyMeasurable hc hF hA
  have hV := DimReg.integral_prod_betaPrime (μ := volume) hS ha h0
    hFm.aestronglyMeasurable hc hF hA
  have hVS : ∫ w in S, (w.1 : ℂ) ^ (-3 * ε) * ((w.2 * w.1⁻¹ : ℝ) : ℂ) ^ (-(2 * ε)) =
      1 / (-ε + 1) * (1 / (-(2 * ε) + 1)) := by
    rw [setIntegral_congr_fun hS hAe, hSd, Measure.volume_eq_prod,
      setIntegral_prod_mul (fun x : ℝ => (x : ℂ) ^ (-ε)) (fun x : ℝ => (x : ℂ) ^ (-(2 * ε))),
      vt, vs]
  rw [hVS] at hV
  -- the fibre integrals
  have hfib : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ^ (2 * ε - 1) * i12Phi0 ε r 1 =
      (2 - 3 * ε) * (1 - 3 * ε) * ∫ w in S, F (r, w) := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    simp only [hFd]
    rw [integral_const_mul, (i12HS_phi_eq_integral h0 h1 hr).2]
    simp only [mul_comm r]
    ring
  unfold IntegrableOn at hI
  rw [← Measure.prod_restrict] at hI
  have hint := hI.integral_prod_left
  have hint' : IntegrableOn (fun r : ℝ => (2 - 3 * ε) * (1 - 3 * ε) * ∫ w in S, F (r, w))
      (Ioi 0) := hint.const_mul ((2 - 3 * ε) * (1 - 3 * ε))
  refine ⟨hint'.congr_fun
    (fun r hr => (hfib r hr).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hfib, integral_const_mul]
  have e2 : ∫ r in Ioi (0 : ℝ), ∫ w in S, F (r, w) =
      ∫ z in Ioi 0 ×ˢ S, F z ∂((volume : Measure ℝ).prod volume) := by
    rw [← Measure.prod_restrict, integral_prod _ hI]
  rw [e2, hV]
  have h1e : (1 - ε) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h2e : (1 - 2 * ε) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [show -ε + 1 = 1 - ε by ring, show -(2 * ε) + 1 = 1 - 2 * ε by ring]
  field_simp

/-- The regularized Mellin transform of `φ` at `2ε`,
`(2 - 3ε)(1 - 3ε) / ((1 - ε)(1 - 2ε)) · Γ(2ε) Γ(ε) / Γ(3ε)` (`= Γ(2ε - 1) Γ(ε - 1) / Γ(3ε - 2)`). -/
noncomputable def i12HSMphi (ε : ℂ) : ℂ :=
  (2 - 3 * ε) * (1 - 3 * ε) / ((1 - ε) * (1 - 2 * ε)) *
    (Gamma (2 * ε) * Gamma ε / Gamma (2 * ε + ε))

/-- The subtracted kernel `φ(sc) - a 1_{s < 1} - a (sc) ^ (-3ε) 1_{s ≥ 1}` (`a = 2 - 3ε`,
`φ = Φ₀(·, 1)`): the face subtractions of the bulk remainder at `s → 0` and `s → ∞`. -/
noncomputable def i12HSD (ε : ℂ) (s c : ℝ) : ℂ :=
  i12Phi0 ε (s * c) 1 - if s < 1 then 2 - 3 * ε else (2 - 3 * ε) * ((s * c : ℝ) : ℂ) ^ (-3 * ε)

/-- The value of the subtracted `s`-integral at scale `c`:
`Ψ(ε, c) = c ^ (-2ε) M_φ - a / (2ε) - a c ^ (-3ε) / ε`. -/
noncomputable def i12HSPsi (ε : ℂ) (c : ℝ) : ℂ :=
  (c : ℂ) ^ (-2 * ε) * i12HSMphi ε - (2 - 3 * ε) / (2 * ε) - (2 - 3 * ε) * (c : ℂ) ^ (-3 * ε) / ε

/-- **The subtracted `s`-integral at scale `c`**: for `0 < re ε < 1/3` and `c > 0`,
`∫₀^∞ s ^ (2ε - 1) (φ(sc) - a 1_{s < 1} - a (sc) ^ (-3ε) 1_{s ≥ 1}) ds = Ψ(ε, c)`,
absolutely convergent. -/
theorem i12HS_psi {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (2 * ε - 1) * i12HSD ε s c) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (2 * ε - 1) * i12HSD ε s c = i12HSPsi ε c := by
  simp only [i12HSD, i12HSPsi]
  obtain ⟨hMi, hMv⟩ := i12HS_mellin h0 h1
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hε : ε ≠ 0 := fun h => by rw [h] at h0; simp at h0
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (2 * ε - 1) * i12Phi0 ε x 1 with hgd
  have hgs : ∀ s ∈ Ioi (0 : ℝ), (s : ℂ) ^ (2 * ε - 1) * i12Phi0 ε (s * c) 1 =
      (c : ℂ) ^ (1 - 2 * ε) * g (s * c) := by
    intro s hs
    have hs : (0 : ℝ) < s := hs
    simp only [hgd]
    rw [DimReg.cpow_ofReal_mul hs.le hc.le]
    have e : (c : ℂ) ^ (1 - 2 * ε) * (c : ℂ) ^ (2 * ε - 1) = 1 := by
      rw [← cpow_add _ _ hc', show 1 - 2 * ε + (2 * ε - 1) = 0 by ring, cpow_zero]
    linear_combination (-((s : ℂ) ^ (2 * ε - 1) * i12Phi0 ε (s * c) 1)) * e
  have hgi : IntegrableOn (fun s => g (s * c)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_right_iff g 0 hc).2 (by simpa using hMi)
  have hgv : ∫ s in Ioi (0 : ℝ), g (s * c) = (c : ℂ)⁻¹ * i12HSMphi ε := by
    rw [integral_comp_mul_right_Ioi g 0 hc, zero_mul, hMv, i12HSMphi, Complex.real_smul,
      ofReal_inv]
  set sub : ℝ → ℂ := fun s => if s < 1 then (2 - 3 * ε) * (s : ℂ) ^ (2 * ε - 1) else
    (2 - 3 * ε) * (c : ℂ) ^ (-3 * ε) * (s : ℂ) ^ (-ε - 1) with hsubd
  have hsub : ∀ s ∈ Ioi (0 : ℝ), (s : ℂ) ^ (2 * ε - 1) *
      (if s < 1 then 2 - 3 * ε else (2 - 3 * ε) * ((s * c : ℝ) : ℂ) ^ (-3 * ε)) = sub s := by
    intro s hs
    have hs : (0 : ℝ) < s := hs
    have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    simp only [hsubd]
    split_ifs
    · ring
    · rw [DimReg.cpow_ofReal_mul hs.le hc.le, show -ε - 1 = (2 * ε - 1) + -3 * ε by ring,
        cpow_add _ _ hs']
      ring
  obtain ⟨i1, v1⟩ := i12HS_cpow_unit (r := 2 * ε - 1) (by simp; linarith)
  have i2 : IntegrableOn (fun s : ℝ => (s : ℂ) ^ (-ε - 1)) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos)
  have v2 : ∫ s in Ici (1 : ℝ), (s : ℂ) ^ (-ε - 1) = 1 / ε := by
    rw [integral_Ici_eq_integral_Ioi, integral_Ioi_cpow_of_lt (by simp; linarith) one_pos,
      ofReal_one, one_cpow, show -ε - 1 + 1 = -ε by ring]
    field_simp
  have hdis : Disjoint (Ioo (0 : ℝ) 1) (Ici 1) :=
    Set.disjoint_left.2 fun x hx hx' => (not_lt.2 (mem_Ici.1 hx')) hx.2
  have e1 : EqOn sub (fun s => (2 - 3 * ε) * (s : ℂ) ^ (2 * ε - 1)) (Ioo 0 1) :=
    fun s hs => by simp only [hsubd, hs.2, ↓reduceIte]
  have e2 : EqOn sub (fun s => (2 - 3 * ε) * (c : ℂ) ^ (-3 * ε) * (s : ℂ) ^ (-ε - 1)) (Ici 1) :=
    fun s hs => by simp only [hsubd, not_lt.2 (mem_Ici.1 hs), ↓reduceIte]
  have i1' : IntegrableOn (fun s : ℝ => (2 - 3 * ε) * (s : ℂ) ^ (2 * ε - 1)) (Ioo 0 1) :=
    i1.const_mul _
  have i2' : IntegrableOn (fun s : ℝ => (2 - 3 * ε) * (c : ℂ) ^ (-3 * ε) * (s : ℂ) ^ (-ε - 1))
      (Ici 1) := i2.const_mul _
  have j1 : IntegrableOn sub (Ioo 0 1) := i1'.congr_fun e1.symm measurableSet_Ioo
  have j2 : IntegrableOn sub (Ici 1) := i2'.congr_fun e2.symm measurableSet_Ici
  have hsubI : IntegrableOn sub (Ioi 0) := by
    rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]; exact j1.union j2
  have hsubV : ∫ s in Ioi (0 : ℝ), sub s =
      (2 - 3 * ε) / (2 * ε) + (2 - 3 * ε) * (c : ℂ) ^ (-3 * ε) / ε := by
    rw [← Ioo_union_Ici_eq_Ioi zero_lt_one, setIntegral_union hdis measurableSet_Ici j1 j2,
      setIntegral_congr_fun measurableSet_Ioo e1, setIntegral_congr_fun measurableSet_Ici e2,
      integral_const_mul, integral_const_mul, v1, v2, show 2 * ε - 1 + 1 = 2 * ε by ring]
    field_simp
  have heq : EqOn (fun s : ℝ => (s : ℂ) ^ (2 * ε - 1) * (i12Phi0 ε (s * c) 1 -
      if s < 1 then 2 - 3 * ε else (2 - 3 * ε) * ((s * c : ℝ) : ℂ) ^ (-3 * ε)))
      (fun s => (c : ℂ) ^ (1 - 2 * ε) * g (s * c) - sub s) (Ioi 0) := fun s hs => by
    simp only [mul_sub]
    rw [hgs s hs, hsub s hs]
  have hgi' : IntegrableOn (fun s => (c : ℂ) ^ (1 - 2 * ε) * g (s * c) - sub s) (Ioi 0) :=
    (hgi.const_mul _).sub hsubI
  refine ⟨hgi'.congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_sub (hgi.const_mul _) hsubI,
    integral_const_mul, hgv, hsubV]
  have e3 : (c : ℂ) ^ (1 - 2 * ε) * (c : ℂ)⁻¹ = (c : ℂ) ^ (-2 * ε) := by
    rw [show 1 - 2 * ε = 1 + -2 * ε by ring, cpow_add _ _ hc', cpow_one]
    field_simp
  rw [← mul_assoc, e3]
  ring
