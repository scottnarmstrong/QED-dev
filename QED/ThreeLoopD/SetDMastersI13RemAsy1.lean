/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RemFP

/-!
# Set (d), master `I₁₃`: the pieces of the large-`t` expansion of the bubble

With `δ = 4/t`, `b_ε(t) = (t/4) ^ (-ε) ∫₀¹ (δ + w) ^ (-ε) φ(w) dw`. Split `φ = P + w³ ψ`:

* **The polynomial part** has the exact primitive `(δ + w) ^ (-ε) Q(δ + w)` with
  `Q(v) = p₀ v/(1 - ε) + p₁ v²/(2 - ε) + p₂ v³/(3 - ε)`, `P(w) = p₀ + p₁ (δ + w) + p₂ (δ + w)²`
  (`QED.ThreeLoopD.i13_integral_PhiP`).
* **The remainder part**: `(δ + w) ^ (-ε) = w ^ (-ε) (1 + δ/w) ^ (-ε)` and the binomial expansion
  with integral remainder (`QED.ThreeLoopD.i13_cpow_taylor3`) give
  `∫ (δ + w) ^ (-ε) w³ ψ = Ψ₀ - ε δ Ψ₁ + ε(ε + 1)/2 δ² Ψ₂ + O(δ³)`, `Ψⱼ = ∫ w ^ (3 - j - ε) ψ`,
  uniformly in `‖ε‖ ≤ 1/10` (`QED.ThreeLoopD.norm_i13_integral_Psi_sub_le`).

## Main results

* `QED.ThreeLoopD.i13_cpow_taylor3`, `QED.ThreeLoopD.norm_i13Bin3_le`.
* `QED.ThreeLoopD.i13_integral_PhiP`, `QED.ThreeLoopD.norm_i13_integral_Psi_sub_le`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-! ### The binomial series to third order -/

theorem i13_hasDerivAt_cpow_affine (a : ℂ) {α β y : ℝ} (h : 0 < α + β * y) :
    HasDerivAt (fun y : ℝ => ((α + β * y : ℝ) : ℂ) ^ a)
      (a * β * ((α + β * y : ℝ) : ℂ) ^ (a - 1)) y := by
  have hs : ((α : ℂ) + (β : ℂ) * (y : ℂ)) ∈ slitPlane := by
    have : ((α : ℂ) + (β : ℂ) * (y : ℂ)) = ((α + β * y : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact ofReal_mem_slitPlane.mpr h
  have hl : HasDerivAt (fun z : ℂ => (α : ℂ) + (β : ℂ) * z) (β : ℂ) (y : ℂ) := by
    simpa using ((hasDerivAt_id (y : ℂ)).const_mul (β : ℂ)).const_add (α : ℂ)
  have := (hl.cpow_const (c := a) hs).comp_ofReal
  convert this using 1
  · ext y; push_cast; ring_nf
  · push_cast; ring

/-- The remainder `∫₀¹ (1 - σ)² (1 + u σ) ^ (c - 3) dσ` of the binomial series. -/
noncomputable def i13Bin3 (c : ℂ) (u : ℝ) : ℂ :=
  ∫ σ in Ioo (0 : ℝ) 1, (((1 - σ) ^ 2 : ℝ) : ℂ) * ((1 + u * σ : ℝ) : ℂ) ^ (c - 3)

/-- **The binomial series with integral remainder**:
`(1 + u) ^ c = 1 + c u + c(c - 1)/2 u² + c(c - 1)(c - 2)/2 u³ B₃(c, u)` for `u ≥ 0`. -/
theorem i13_cpow_taylor3 (c : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ((1 + u : ℝ) : ℂ) ^ c = 1 + c * u + c * (c - 1) / 2 * u ^ 2 +
      c * (c - 1) * (c - 2) / 2 * u ^ 3 * i13Bin3 c u := by
  set X : ℂ → ℝ → ℂ := fun a σ => ((1 + u * σ : ℝ) : ℂ) ^ a with hX
  have hpos : ∀ σ ∈ uIcc (0 : ℝ) 1, 0 < 1 + u * σ := fun σ hσ => by
    rw [uIcc_of_le zero_le_one] at hσ
    nlinarith [hσ.1]
  have hG : ∀ σ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun σ : ℝ => X c σ +
      ((1 - σ : ℝ) : ℂ) * u * c * X (c - 1) σ +
      ((1 - σ : ℝ) : ℂ) ^ 2 * u ^ 2 * (c * (c - 1) / 2) * X (c - 2) σ)
      (c * (c - 1) * (c - 2) / 2 * u ^ 3 * ((((1 - σ) ^ 2 : ℝ) : ℂ) * X (c - 3) σ)) σ := by
    intro σ hσ
    have h0 := i13_hasDerivAt_cpow_affine c (hpos σ hσ)
    have h1 := i13_hasDerivAt_cpow_affine (c - 1) (hpos σ hσ)
    have h2 := i13_hasDerivAt_cpow_affine (c - 2) (hpos σ hσ)
    rw [show c - 1 - 1 = c - 2 by ring] at h1
    rw [show c - 2 - 1 = c - 3 by ring] at h2
    have l1 : HasDerivAt (fun σ : ℝ => ((1 - σ : ℝ) : ℂ)) (-1) σ := by
      simpa using ((hasDerivAt_id σ).const_sub 1).ofReal_comp
    have l2 : HasDerivAt (fun σ : ℝ => ((1 - σ : ℝ) : ℂ) ^ 2) (-2 * ((1 - σ : ℝ) : ℂ)) σ := by
      convert l1.pow 2 using 1; push_cast; ring
    have := (h0.add (((l1.mul_const (u : ℂ)).mul_const c).mul h1)).add
      (((l2.mul_const ((u : ℂ) ^ 2)).mul_const (c * (c - 1) / 2)).mul h2)
    convert this using 1
    simp only [hX]
    push_cast
    ring
  have hcont : ContinuousOn (fun σ : ℝ =>
      c * (c - 1) * (c - 2) / 2 * u ^ 3 * ((((1 - σ) ^ 2 : ℝ) : ℂ) * X (c - 3) σ))
      (uIcc 0 1) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul (by fun_prop) ?_)
    exact ContinuousOn.cpow_const (by fun_prop) fun σ hσ =>
      ofReal_mem_slitPlane.mpr (hpos σ hσ)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hG (hcont.intervalIntegrable)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] at hint
  simp only [hX, mul_one, mul_zero, add_zero, ofReal_one, one_cpow, sub_self, ofReal_zero,
    zero_mul, sub_zero, one_pow] at hint
  unfold i13Bin3
  rw [hint]
  ring

/-- `‖B₃(c, u)‖ ≤ 1` for `re c ≤ 3`, `u ≥ 0`. -/
theorem norm_i13Bin3_le {c : ℂ} (hc : c.re ≤ 3) {u : ℝ} (hu : 0 ≤ u) : ‖i13Bin3 c u‖ ≤ 1 := by
  unfold i13Bin3
  have := norm_setIntegral_le_of_norm_le_const (s := Ioo (0 : ℝ) 1)
    (measure_Ioo_lt_top (μ := volume) (a := (0 : ℝ)) (b := 1)) (C := 1)
    (f := fun σ : ℝ => (((1 - σ) ^ 2 : ℝ) : ℂ) * ((1 + u * σ : ℝ) : ℂ) ^ (c - 3))
    (fun σ hσ => by
      have hb : 0 < 1 + u * σ := by nlinarith [hσ.1]
      rw [norm_mul, norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hb]
      have h1 : |(1 - σ) ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [hσ.1, hσ.2]
      have h2 : (1 + u * σ) ^ (c - 3).re ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [hσ.1]) (by simp; linarith)
      calc |(1 - σ) ^ 2| * (1 + u * σ) ^ (c - 3).re ≤ 1 * 1 :=
            mul_le_mul h1 h2 (Real.rpow_nonneg hb.le _) zero_le_one
        _ = 1 := one_mul 1)
  simpa [Real.volume_real_Ioo_of_le zero_le_one] using this

/-! ### The polynomial part -/

/-- `Q(v) = p₀ v/(1 - ε) + p₁ v²/(2 - ε) + p₂ v³/(3 - ε)`, where
`P(w) = p₀ + p₁ (δ + w) + p₂ (δ + w)²`:
`p₂ = 3/16`, `p₁ = 1/4 - 3δ/8`, `p₀ = 1/2 - δ/4 + 3δ²/16`. -/
noncomputable def i13Qp (ε : ℂ) (δ v : ℝ) : ℂ :=
  (1 / 2 - δ / 4 + 3 / 16 * δ ^ 2 : ℝ) * v / (1 - ε) + (1 / 4 - 3 / 8 * δ : ℝ) * v ^ 2 / (2 - ε) +
    3 / 16 * (v : ℂ) ^ 3 / (3 - ε)

/-- **The polynomial part**:
`∫₀¹ (δ + w) ^ (-ε) P(w) dw = (1 + δ) ^ (-ε) Q(1 + δ) - δ ^ (-ε) Q(δ)`. -/
theorem i13_integral_PhiP {ε : ℂ} (hε : ‖ε‖ < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w in Ioo (0 : ℝ) 1, ((δ + w : ℝ) : ℂ) ^ (-ε) * (i13PhiP w : ℂ) =
      ((1 + δ : ℝ) : ℂ) ^ (-ε) * i13Qp ε δ (1 + δ) - (δ : ℂ) ^ (-ε) * i13Qp ε δ δ := by
  obtain ⟨h1, h2, h3, -⟩ := i13_eps_facts hε
  have hpos : ∀ w ∈ uIcc (0 : ℝ) 1, 0 < δ + 1 * w := fun w hw => by
    rw [uIcc_of_le zero_le_one] at hw; linarith [hw.1]
  have hF : ∀ w ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun w : ℝ =>
      ((δ + 1 * w : ℝ) : ℂ) ^ (-ε) * i13Qp ε δ (δ + 1 * w))
      (((δ + 1 * w : ℝ) : ℂ) ^ (-ε) * (i13PhiP w : ℂ)) w := by
    intro w hw
    have hv := hpos w hw
    have hX := i13_hasDerivAt_cpow_affine (-ε) hv
    have hQ : HasDerivAt (fun w : ℝ => i13Qp ε δ (δ + 1 * w))
        ((1 / 2 - δ / 4 + 3 / 16 * δ ^ 2 : ℝ) / (1 - ε) +
          (1 / 4 - 3 / 8 * δ : ℝ) * (2 * ((δ + 1 * w : ℝ) : ℂ)) / (2 - ε) +
          3 / 16 * (3 * ((δ + 1 * w : ℝ) : ℂ) ^ 2) / (3 - ε)) w := by
      unfold i13Qp
      have hv' : HasDerivAt (fun w : ℝ => ((δ + 1 * w : ℝ) : ℂ)) 1 w := by
        simpa using ((hasDerivAt_id w).const_add δ).ofReal_comp
      have := (((hv'.const_mul ((1 / 2 - δ / 4 + 3 / 16 * δ ^ 2 : ℝ) : ℂ)).div_const (1 - ε)).add
        (((hv'.pow 2).const_mul ((1 / 4 - 3 / 8 * δ : ℝ) : ℂ)).div_const (2 - ε))).add
        (((hv'.pow 3).const_mul (3 / 16 : ℂ)).div_const (3 - ε))
      convert this using 1
      push_cast; ring
    convert hX.mul hQ using 1
    have hv0 : ((δ + 1 * w : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv.ne'
    rw [show -ε - 1 = -ε - 1 by rfl, cpow_sub _ _ hv0, cpow_one]
    unfold i13Qp i13PhiP
    push_cast at hv0 ⊢
    simp only [one_mul] at hv0 ⊢
    field_simp
    ring
  have hcont : ContinuousOn (fun w : ℝ => ((δ + 1 * w : ℝ) : ℂ) ^ (-ε) * (i13PhiP w : ℂ))
      (uIcc 0 1) := by
    refine ContinuousOn.mul (ContinuousOn.cpow_const (by fun_prop) fun w hw =>
      ofReal_mem_slitPlane.mpr (hpos w hw)) ?_
    unfold i13PhiP; fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hint
  simp only [one_mul, mul_one, mul_zero, add_zero] at hint
  rw [hint, add_comm δ 1]

/-! ### The remainder part -/

theorem i13_cpow_shift {ε : ℂ} {δ w : ℝ} (hδ : 0 ≤ δ) (hw : 0 < w) :
    ((δ + w : ℝ) : ℂ) ^ (-ε) = (w : ℂ) ^ (-ε) * ((1 + δ / w : ℝ) : ℂ) ^ (-ε) := by
  have h : δ + w = w * (1 + δ / w) := by field_simp; ring
  rw [h, ofReal_mul, mul_cpow_ofReal_nonneg hw.le (by positivity)]

theorem i13_cpow_psi_exp {w : ℝ} (hw : 0 < w) (ε : ℂ) (j : ℕ) (hj : j ≤ 3) :
    (w : ℂ) ^ (1 - ε - j + 2) = (w : ℂ) ^ (-ε) * (w : ℂ) ^ (3 - j) := by
  have hw0 : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  rw [show 1 - ε - j + 2 = -ε + ((3 - j : ℕ) : ℂ) by push_cast [Nat.cast_sub hj]; ring,
    cpow_add _ _ hw0, cpow_natCast]

theorem i13_norm_cpow_neg_le {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 2) :
    ‖(w : ℂ) ^ (-ε)‖ ≤ w ^ ((1 : ℝ) / 2 - 1) :=
  i13_norm_cpow_le hw (by
    rw [neg_re]; norm_num; linarith [(abs_re_le_norm ε), le_abs_self ε.re, neg_abs_le ε.re])

theorem integrableOn_i13_psi_pow {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 2) (k : ℕ) :
    IntegrableOn (fun w : ℝ => (w : ℂ) ^ (-ε) * (w : ℂ) ^ k * (i13Psi w : ℂ)) (Ioo 0 1) := by
  refine Integrable.mono' (integrableOn_rpow_mul_phi (r := 1 / 2) (by norm_num) le_rfl)
    (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioo fun w hw => ?_)
  rw [norm_mul, norm_mul, norm_pow, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hw.1, abs_of_nonneg (i13Psi_nonneg hw)]
  have hk : w ^ k ≤ 1 := pow_le_one₀ hw.1.le hw.2.le
  have hr0 : 0 ≤ w ^ ((1 : ℝ) / 2 - 1) := Real.rpow_nonneg hw.1.le _
  calc ‖(w : ℂ) ^ (-ε)‖ * w ^ k * i13Psi w ≤ w ^ ((1 : ℝ) / 2 - 1) * 1 * i13Phi w :=
        mul_le_mul (mul_le_mul (i13_norm_cpow_neg_le hw hε) hk (pow_nonneg hw.1.le _) hr0)
          (i13Psi_le hw) (i13Psi_nonneg hw) (by positivity)
    _ = _ := by ring

/-- `(δ + w) ^ (-ε) g(w)` is integrable on `(0, 1)` when `|g| ≤ φ`. -/
theorem integrableOn_i13_shift_mul {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 2) {δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ}
    (hg : Measurable g) (hgb : ∀ w ∈ Ioo (0 : ℝ) 1, |g w| ≤ i13Phi w) :
    IntegrableOn (fun w : ℝ => ((δ + w : ℝ) : ℂ) ^ (-ε) * (g w : ℂ)) (Ioo 0 1) := by
  refine Integrable.mono' ((integrableOn_i13Phi).const_mul
    (δ ^ (-(1 / 2) : ℝ) + (1 + δ) ^ (1 / 2 : ℝ)))
    (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioo fun w hw => ?_)
  have hb : 0 < δ + w := by linarith [hw.1]
  rw [norm_mul, norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hb]
  have hA : 0 ≤ δ ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hδ.le _
  have hB : 0 ≤ (1 + δ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have h1 : (δ + w) ^ (-ε).re ≤ δ ^ (-(1 / 2) : ℝ) + (1 + δ) ^ (1 / 2 : ℝ) := by
    rcases le_or_gt 1 (δ + w) with h | h
    · have : (δ + w) ^ (-ε).re ≤ (1 + δ) ^ (1 / 2 : ℝ) :=
        (Real.rpow_le_rpow_of_exponent_le h (by
          rw [neg_re]; linarith [abs_re_le_norm ε, neg_abs_le ε.re])).trans
        (Real.rpow_le_rpow hb.le (by linarith [hw.2]) (by norm_num))
      linarith
    · have : (δ + w) ^ (-ε).re ≤ δ ^ (-(1 / 2) : ℝ) :=
        (Real.rpow_le_rpow_of_exponent_ge hb h.le (by
          rw [neg_re]; linarith [abs_re_le_norm ε, le_abs_self ε.re])).trans
        (Real.rpow_le_rpow_of_nonpos hδ (by linarith [hw.1]) (by norm_num))
      linarith
  exact mul_le_mul h1 (hgb w hw) (abs_nonneg _) (by positivity)

/-- The constant `∫₀¹ w ^ (-1/2) φ(w) dw`. -/
noncomputable def i13CPhi : ℝ := ∫ w in Ioo (0 : ℝ) 1, w ^ ((1 : ℝ) / 2 - 1) * i13Phi w

/-- `‖ε(ε + 1)(ε + 2)/2‖ ≤ 1` for `‖ε‖ ≤ 1/10`. -/
theorem i13_norm_K_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) :
    ‖(-ε) * (-ε - 1) * (-ε - 2) / 2‖ ≤ 1 := by
  have h1 : ‖-ε - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; linarith)
  have h2 : ‖-ε - 2‖ ≤ 3 := (norm_sub_le _ _).trans (by simp; linarith)
  rw [norm_div, norm_mul, norm_mul, norm_neg]
  simp only [Complex.norm_ofNat]
  have := mul_le_mul (mul_le_mul hε h1 (norm_nonneg _) (by norm_num)) h2 (norm_nonneg _)
    (by norm_num)
  linarith

/-- **The remainder part**: `∫ (δ + w) ^ (-ε) w³ ψ = Ψ₀ - ε δ Ψ₁ + ε(ε + 1)/2 δ² Ψ₂ + O(δ³)`. -/
theorem norm_i13_integral_Psi_sub_le {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 10) {δ : ℝ} (hδ : 0 < δ) :
    ‖(∫ w in Ioo (0 : ℝ) 1, ((δ + w : ℝ) : ℂ) ^ (-ε) * ((w ^ 3 * i13Psi w : ℝ) : ℂ)) -
        (i13PsiInt (1 - ε - 0) - ε * δ * i13PsiInt (1 - ε - 1) +
          ε * (ε + 1) / 2 * δ ^ 2 * i13PsiInt (1 - ε - 2))‖ ≤ δ ^ 3 * i13CPhi := by
  have hε2 : ‖ε‖ ≤ 1 / 2 := by linarith
  have hPsi : ∀ j : ℕ, j ≤ 3 → i13PsiInt (1 - ε - j) =
      ∫ w in Ioo (0 : ℝ) 1, (w : ℂ) ^ (-ε) * (w : ℂ) ^ (3 - j) * (i13Psi w : ℂ) := by
    intro j hj
    unfold i13PsiInt
    exact setIntegral_congr_fun measurableSet_Ioo fun w hw => by
      rw [i13_cpow_psi_exp hw.1 ε j hj]
  have e0 := hPsi 0 (by norm_num)
  have e1 := hPsi 1 (by norm_num)
  have e2 := hPsi 2 (by norm_num)
  simp only [Nat.cast_zero, Nat.sub_zero] at e0
  simp only [Nat.cast_one, show 3 - 1 = 2 from rfl] at e1
  simp only [Nat.cast_ofNat, show 3 - 2 = 1 from rfl, pow_one] at e2
  rw [e0, e1, e2]
  -- the pointwise remainder
  set K : ℂ := (-ε) * (-ε - 1) * (-ε - 2) / 2 with hK
  have hpt : ∀ w ∈ Ioo (0 : ℝ) 1,
      ((δ + w : ℝ) : ℂ) ^ (-ε) * ((w ^ 3 * i13Psi w : ℝ) : ℂ) -
        ((w : ℂ) ^ (-ε) * (w : ℂ) ^ 3 * (i13Psi w : ℂ) -
          ε * δ * ((w : ℂ) ^ (-ε) * (w : ℂ) ^ 2 * (i13Psi w : ℂ)) +
          ε * (ε + 1) / 2 * δ ^ 2 * ((w : ℂ) ^ (-ε) * (w : ℂ) * (i13Psi w : ℂ))) =
      (w : ℂ) ^ (-ε) * (i13Psi w : ℂ) * (δ ^ 3 * K * i13Bin3 (-ε) (δ / w)) := by
    intro w hw
    have hw0 : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.1.ne'
    rw [i13_cpow_shift hδ.le hw.1, i13_cpow_taylor3 (-ε) (div_nonneg hδ.le hw.1.le)]
    push_cast
    field_simp
    ring
  have hfull := integrableOn_i13_shift_mul hε2 hδ (g := fun w => w ^ 3 * i13Psi w)
    (by fun_prop) fun w hw => by
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg hw.1.le 3) (i13Psi_nonneg hw))]
      have : w ^ 3 ≤ 1 := pow_le_one₀ hw.1.le hw.2.le
      nlinarith [i13Psi_nonneg hw, i13Psi_le hw]
  have i3 := integrableOn_i13_psi_pow hε2 3
  have i2 := integrableOn_i13_psi_pow hε2 2
  have i1 := integrableOn_i13_psi_pow hε2 1
  simp only [pow_one] at i1
  have hI : ∫ w in Ioo (0 : ℝ) 1, (((δ + w : ℝ) : ℂ) ^ (-ε) * ((w ^ 3 * i13Psi w : ℝ) : ℂ) -
        ((w : ℂ) ^ (-ε) * (w : ℂ) ^ 3 * (i13Psi w : ℂ) -
          ε * δ * ((w : ℂ) ^ (-ε) * (w : ℂ) ^ 2 * (i13Psi w : ℂ)) +
          ε * (ε + 1) / 2 * δ ^ 2 * ((w : ℂ) ^ (-ε) * (w : ℂ) * (i13Psi w : ℂ)))) =
      (∫ w in Ioo (0 : ℝ) 1, ((δ + w : ℝ) : ℂ) ^ (-ε) * ((w ^ 3 * i13Psi w : ℝ) : ℂ)) -
        ((∫ w in Ioo (0 : ℝ) 1, (w : ℂ) ^ (-ε) * (w : ℂ) ^ 3 * (i13Psi w : ℂ)) -
          ε * δ * (∫ w in Ioo (0 : ℝ) 1, (w : ℂ) ^ (-ε) * (w : ℂ) ^ 2 * (i13Psi w : ℂ)) +
          ε * (ε + 1) / 2 * δ ^ 2 *
            ∫ w in Ioo (0 : ℝ) 1, (w : ℂ) ^ (-ε) * (w : ℂ) * (i13Psi w : ℂ)) := by
    have j2 : IntegrableOn (fun w : ℝ => ε * δ * ((w : ℂ) ^ (-ε) * (w : ℂ) ^ 2 *
        (i13Psi w : ℂ))) (Ioo 0 1) := i2.const_mul _
    have j1 : IntegrableOn (fun w : ℝ => ε * (ε + 1) / 2 * δ ^ 2 * ((w : ℂ) ^ (-ε) * (w : ℂ) *
        (i13Psi w : ℂ))) (Ioo 0 1) := i1.const_mul _
    have j32 : IntegrableOn (fun w : ℝ => (w : ℂ) ^ (-ε) * (w : ℂ) ^ 3 * (i13Psi w : ℂ) -
        ε * δ * ((w : ℂ) ^ (-ε) * (w : ℂ) ^ 2 * (i13Psi w : ℂ))) (Ioo 0 1) := i3.sub j2
    have j321 : IntegrableOn (fun w : ℝ => (w : ℂ) ^ (-ε) * (w : ℂ) ^ 3 * (i13Psi w : ℂ) -
        ε * δ * ((w : ℂ) ^ (-ε) * (w : ℂ) ^ 2 * (i13Psi w : ℂ)) +
        ε * (ε + 1) / 2 * δ ^ 2 * ((w : ℂ) ^ (-ε) * (w : ℂ) * (i13Psi w : ℂ))) (Ioo 0 1) :=
      j32.add j1
    rw [integral_sub hfull j321, integral_add j32 j1, integral_sub i3 j2, integral_const_mul,
      integral_const_mul]
  rw [← hI, setIntegral_congr_fun measurableSet_Ioo hpt]
  have hmaj := (integrableOn_rpow_mul_phi (r := 1 / 2) (by norm_num) le_rfl).const_mul (δ ^ 3)
  refine (norm_integral_le_of_norm_le hmaj (ae_restrict_of_forall_mem measurableSet_Ioo
    fun w hw => ?_)).trans (le_of_eq ?_)
  · have hB := norm_i13Bin3_le (c := -ε) (u := δ / w) (by
      rw [neg_re]; linarith [abs_re_le_norm ε, neg_abs_le ε.re]) (by
      exact div_nonneg hδ.le hw.1.le)
    have hKb := i13_norm_K_le hε
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (i13Psi_nonneg hw), norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    have hw1 := i13_norm_cpow_neg_le hw hε2
    have hp := i13Psi_le hw
    have hp0 := i13Psi_nonneg hw
    have hr0 : 0 ≤ w ^ ((1 : ℝ) / 2 - 1) := Real.rpow_nonneg hw.1.le _
    have hφ := (i13Phi_pos hw.2).le
    calc ‖(w : ℂ) ^ (-ε)‖ * i13Psi w * (δ ^ 3 * ‖K‖ * ‖i13Bin3 (-ε) (δ / w)‖) ≤
        w ^ ((1 : ℝ) / 2 - 1) * i13Phi w * (δ ^ 3 * 1 * 1) :=
          mul_le_mul (mul_le_mul hw1 hp hp0 hr0) (mul_le_mul (mul_le_mul le_rfl hKb
            (norm_nonneg _) (by positivity)) hB (norm_nonneg _) (by positivity))
            (by positivity) (mul_nonneg hr0 hφ)
      _ = _ := by ring
  · unfold i13CPhi
    rw [integral_const_mul]

end QED.ThreeLoopD
