/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSBadPt

/-!
# Set (d), master `I₁₂`: the reflected-face term of the bad part

The integrand `QED.ThreeLoopD.i12HSBadW` of the bad part contains, on `i12HSDom`
(`s > 1`), the term `SecWt(x, s) (h(x)^{2ε-1} - h₀^{2ε-1}) F(s, u)` which does not carry the
factor `(1 - xs)^{-ε} - 1`. It factorizes as `A(x) B(s) C(u)`
(`QED.ThreeLoopD.i12HS_domTerm_eq`), and by Fubini on `i12HSDom = {0 < x < 1, 1 < s < x⁻¹}`
(`QED.ThreeLoopD.i12HS_dom_prod`) and `∫₁^{1/x} s^{-ε-1} ds = (1 - x^ε)/ε`, for `0 < re ε < 1/3`

  `∫_{Dom} SecWt (h^{2ε-1} - h₀^{2ε-1}) F`
    `= (∫₀¹ x^{ε-1} (h^{2ε-1} - h₀^{2ε-1}) (1 - x^ε)/ε dx) · a Γ(1 - 2ε) Γ(1 + ε)/Γ(2 - ε)`

(`QED.ThreeLoopD.integral_i12HS_domTerm`), i.e. `a B_w (P(2ε - 1, ε) - P(2ε - 1, 2ε))/ε`: the
first part of the piece `(iii)` of the decomposition of the bad part.

## Main results

* `QED.ThreeLoopD.i12HS_dom_prod`: Fubini on `i12HSDom` for product integrands.
* `QED.ThreeLoopD.integral_i12HS_domTerm`.
-/

@[expose] public section

open Complex Set MeasureTheory Metric

namespace QED.ThreeLoopD

/-- `i12HSDom` as `{0 < x < 1, 1 < s < x⁻¹, 0 < u < 1}`. -/
theorem i12HSDom_eq : i12HSDom =
    {z : ℝ × ℝ × ℝ | z.1 ∈ Ioo 0 1 ∧ z.2.1 ∈ Ioo 1 z.1⁻¹ ∧ z.2.2 ∈ Ioo 0 1} := by
  ext ⟨x, s, u⟩
  simp only [i12HSDom, mem_ofPred_eq, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨hs, ⟨hx0, hx1⟩, hu⟩
    have hs0 : 0 < s := zero_lt_one.trans hs
    refine ⟨⟨hx0, hx1.trans (inv_lt_one_of_one_lt₀ hs)⟩, ⟨hs, ?_⟩, hu⟩
    rw [lt_inv_comm₀ hs0 hx0]; exact hx1
  · rintro ⟨⟨hx0, -⟩, ⟨hs, hs1⟩, hu⟩
    have hs0 : 0 < s := zero_lt_one.trans hs
    exact ⟨hs, ⟨hx0, by rw [lt_inv_comm₀ hx0 hs0]; exact hs1⟩, hu⟩

/-- **Fubini on `i12HSDom` for a product integrand** `A(x) B(s) C(u)`, with `B` integrable on
`(1, x⁻¹)` with a uniform bound. -/
theorem i12HS_dom_prod {A B C : ℝ → ℂ} (mA : Measurable A) (mB : Measurable B)
    (mC : Measurable C) (hA : IntegrableOn A (Ioo 0 1)) (hB : ∀ b, IntegrableOn B (Ioo 1 b))
    {M : ℝ} (hM : ∀ b, ∫ s in Ioo 1 b, ‖B s‖ ≤ M) (hC : IntegrableOn C (Ioo 0 1)) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => A z.1 * B z.2.1 * C z.2.2) i12HSDom ∧
      ∫ z in i12HSDom, A z.1 * B z.2.1 * C z.2.2 =
        (∫ x in Ioo (0 : ℝ) 1, A x * ∫ s in Ioo 1 x⁻¹, B s) * ∫ u in Ioo (0 : ℝ) 1, C u := by
  set F := i12HSDom.indicator (fun z : ℝ × ℝ × ℝ => A z.1 * B z.2.1 * C z.2.2) with hFd
  have hF : ∀ x s u, F (x, s, u) = (Ioo 0 1).indicator A x *
      ((Ioo 1 x⁻¹).indicator B s * (Ioo 0 1).indicator C u) := by
    intro x s u
    simp only [hFd, i12HSDom_eq, indicator_apply, mem_ofPred_eq]
    by_cases hx : x ∈ Ioo (0 : ℝ) 1 <;> by_cases hs : s ∈ Ioo 1 x⁻¹ <;>
      by_cases hu : u ∈ Ioo (0 : ℝ) 1 <;> simp [hx, hs, hu, mul_assoc]
  have mF : Measurable F := (((mA.comp measurable_fst).mul (mB.comp measurable_snd.fst)).mul
    (mC.comp measurable_snd.snd)).indicator measurableSet_i12HSDom
  have hBi : ∀ x, Integrable ((Ioo 1 x⁻¹).indicator B) :=
    fun x => (integrable_indicator_iff measurableSet_Ioo).2 (hB _)
  have hCi : Integrable ((Ioo 0 1).indicator C) := (integrable_indicator_iff measurableSet_Ioo).2 hC
  have hAi : Integrable ((Ioo 0 1).indicator A) := (integrable_indicator_iff measurableSet_Ioo).2 hA
  have hsec : ∀ x, (fun y : ℝ × ℝ => F (x, y)) = fun y => (Ioo 0 1).indicator A x *
      ((Ioo 1 x⁻¹).indicator B y.1 * (Ioo 0 1).indicator C y.2) := fun x => by
    funext y; exact hF x y.1 y.2
  have hnorm : ∀ x, ∫ y : ℝ × ℝ, ‖F (x, y)‖ ∂(volume.prod volume) =
      ‖(Ioo 0 1).indicator A x‖ * ((∫ s, ‖(Ioo 1 x⁻¹).indicator B s‖) *
        ∫ u, ‖(Ioo 0 1).indicator C u‖) := fun x => by
    have e : (fun y : ℝ × ℝ => ‖F (x, y)‖) = fun y => ‖(Ioo 0 1).indicator A x‖ *
        (‖(Ioo 1 x⁻¹).indicator B y.1‖ * ‖(Ioo 0 1).indicator C y.2‖) := by
      funext y; rw [hF x y.1 y.2, norm_mul, norm_mul]
    rw [show (∫ y : ℝ × ℝ, ‖F (x, y)‖ ∂(volume.prod volume)) =
        ∫ y : ℝ × ℝ, ‖(Ioo 0 1).indicator A x‖ *
        (‖(Ioo 1 x⁻¹).indicator B y.1‖ * ‖(Ioo 0 1).indicator C y.2‖) ∂(volume.prod volume)
        from by rw [← e],
      integral_const_mul]
    congr 1
    exact integral_prod_mul (fun s => ‖(Ioo 1 x⁻¹).indicator B s‖)
      (fun u => ‖(Ioo 0 1).indicator C u‖)
  have hFi : Integrable F (volume.prod (volume.prod volume)) := by
    refine (integrable_prod_iff mF.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall
      fun x => ?_, ?_⟩
    · rw [hsec x]; exact ((hBi x).mul_prod hCi).const_mul _
    · refine Integrable.mono' (hAi.norm.mul_const (M * ∫ u, ‖(Ioo 0 1).indicator C u‖)) ?_
        (Filter.Eventually.of_forall fun x => ?_)
      · exact (mF.norm.stronglyMeasurable.integral_prod_right' (f := fun z => ‖F z‖)
          ).aestronglyMeasurable
      · rw [hnorm x, norm_mul, norm_mul, Real.norm_of_nonneg (norm_nonneg _),
          Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
          Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_
          (integral_nonneg fun _ => norm_nonneg _)) (norm_nonneg _)
        rw [show (fun s => ‖(Ioo 1 x⁻¹).indicator B s‖) =
          (Ioo 1 x⁻¹).indicator (fun s => ‖B s‖) from by
            funext s; simp only [indicator_apply]; split_ifs <;> simp,
          integral_indicator measurableSet_Ioo]
        exact hM _
  refine ⟨(integrable_indicator_iff measurableSet_i12HSDom).1 hFi, ?_⟩
  rw [← integral_indicator measurableSet_i12HSDom, ← hFd,
    show (∫ z, F z) = ∫ z, F z ∂(volume.prod (volume.prod volume)) from rfl, integral_prod _ hFi]
  simp only [hsec, integral_const_mul]
  have hI : ∀ x, ∫ y : ℝ × ℝ, (Ioo 1 x⁻¹).indicator B y.1 * (Ioo 0 1).indicator C y.2
      ∂(volume.prod volume) =
      (∫ s in Ioo 1 x⁻¹, B s) * ∫ u in Ioo (0 : ℝ) 1, C u := fun x => by
    rw [integral_prod_mul, integral_indicator measurableSet_Ioo,
      integral_indicator measurableSet_Ioo]
  simp only [hI]
  have hm := integral_mul_const (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (∫ u in Ioo (0 : ℝ) 1, C u) (fun x => A x * ∫ s in Ioo 1 x⁻¹, B s)
  have hL : (fun x => (Ioo 0 1).indicator A x *
      ((∫ s in Ioo 1 x⁻¹, B s) * ∫ u in Ioo (0 : ℝ) 1, C u)) =
      (Ioo 0 1).indicator (fun x => A x * (∫ s in Ioo 1 x⁻¹, B s) * ∫ u in Ioo (0 : ℝ) 1, C u) := by
    funext x; simp only [indicator_apply]; split_ifs <;> simp [mul_assoc]
  rw [hL, integral_indicator measurableSet_Ioo, hm]


/-- The reflected-face term factorizes:
`SecWt (h^{2ε-1} - h₀^{2ε-1}) F = x^{ε-1} (h^{2ε-1} - h₀^{2ε-1}) s^{-ε-1} a u^{-2ε} (1 - u)^ε`. -/
theorem i12HS_domTerm_eq (ε : ℂ) {x s u : ℝ} (hs : 0 < s) (hu0 : 0 < u)
    (hu1 : u < 1) :
    i12SecWt ε x s * ((((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) *
      i12HSFt ε s u) =
    (x : ℂ) ^ (ε - 1) * (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) *
      (s : ℂ) ^ (-ε - 1) * ((2 - 3 * ε) * ((u : ℂ) ^ (-2 * ε) * ((1 - u : ℝ) : ℂ) ^ ε)) := by
  have h1 : 0 < 1 - u := by linarith
  have hk : 0 < s * i12HSk u := mul_pos hs (div_pos hu0 h1)
  have e : (s : ℂ) ^ (2 * ε - 1) * (i12HSw ε u * ((s * i12HSk u : ℝ) : ℂ) ^ (-3 * ε)) =
      (s : ℂ) ^ (-ε - 1) * ((u : ℂ) ^ (-2 * ε) * ((1 - u : ℝ) : ℂ) ^ ε) := by
    simp only [i12HSw]
    rw [i12_cpow_lin hs, i12_cpow_lin hu0, i12_cpow_lin h1, i12_cpow_lin hk, i12_cpow_lin hs,
      i12_cpow_lin hu0, i12_cpow_lin h1, i12HSk, Real.log_mul hs.ne' (div_pos hu0 h1).ne',
      Real.log_div hu0.ne' h1.ne']
    simp only [← exp_add]
    congr 1; push_cast; ring
  simp only [i12SecWt, i12HSFt]
  linear_combination ((x : ℂ) ^ (ε - 1) *
    (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) * (2 - 3 * ε)) * e

/-- `∫₁^{1/x} s^{-ε-1} ds = (1 - x^ε)/ε`. -/
theorem i12HS_integral_Ioo_one_cpow {ε : ℂ} (hε : ε ≠ 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ s in Ioo 1 x⁻¹, (s : ℂ) ^ (-ε - 1) = (1 - (x : ℂ) ^ ε) / ε := by
  have hle : (1 : ℝ) ≤ x⁻¹ := (one_le_inv₀ hx0).2 hx1.le
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
    integral_cpow (Or.inr ⟨fun h => hε (by linear_combination -h), by
      rw [uIcc_of_le hle]; intro h; linarith [h.1]⟩)]
  rw [show -ε - 1 + 1 = -ε by ring, ofReal_one, one_cpow, ofReal_inv,
    inv_cpow _ _ (by simp [arg_ofReal_of_nonneg hx0.le, Real.pi_ne_zero.symm]), ← cpow_neg,
    neg_neg]
  field_simp
  ring

/-- `∫₁^b |s^{-ε-1}| ds ≤ 1/re ε`. -/
theorem i12HS_norm_cpow_Ioo_le {ε : ℂ} (h0 : 0 < ε.re) (b : ℝ) :
    ∫ s in Ioo 1 b, ‖(s : ℂ) ^ (-ε - 1)‖ ≤ 1 / ε.re := by
  have hI : IntegrableOn (fun s : ℝ => s ^ (-ε.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have heq : EqOn (fun s : ℝ => ‖(s : ℂ) ^ (-ε - 1)‖) (fun s => s ^ (-ε.re - 1)) (Ioi 1) :=
    fun s hs => by
      dsimp only
      rw [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hs)]; simp
  have hI' : IntegrableOn (fun s : ℝ => ‖(s : ℂ) ^ (-ε - 1)‖) (Ioi 1) :=
    hI.congr_fun heq.symm measurableSet_Ioi
  calc ∫ s in Ioo 1 b, ‖((s : ℝ) : ℂ) ^ (-ε - 1)‖
      ≤ ∫ s in Ioi (1 : ℝ), ‖((s : ℝ) : ℂ) ^ (-ε - 1)‖ :=
        setIntegral_mono_set hI' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (Filter.Eventually.of_forall fun s hs => (hs : s ∈ Ioo 1 b).1)
    _ = 1 / ε.re := by
      rw [setIntegral_congr_fun measurableSet_Ioi heq,
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
      rw [Real.one_rpow, show -ε.re - 1 + 1 = -ε.re by ring]
      field_simp

/-- **The reflected-face term of the bad part** on `i12HSDom`, in closed form up to one
logarithmic `x`-integral: for `0 < re ε < 1/3`,
`∫_{Dom} SecWt (h^{2ε-1} - h₀^{2ε-1}) F = (∫₀¹ x^{ε-1} (h^{2ε-1} - h₀^{2ε-1}) (1 - x^ε)/ε dx)
· a Γ(1 - 2ε) Γ(1 + ε)/Γ(2 - ε)`. -/
theorem integral_i12HS_domTerm {ε : ℂ} (h0 : 0 < ε.re) (h1 : ε.re < 1 / 3) :
    IntegrableOn (fun z : ℝ × ℝ × ℝ => i12SecWt ε z.1 z.2.1 *
      ((((i12H z.1 : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) *
        i12HSFt ε z.2.1 z.2.2)) i12HSDom ∧
    ∫ z in i12HSDom, i12SecWt ε z.1 z.2.1 *
      ((((i12H z.1 : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) *
        i12HSFt ε z.2.1 z.2.2) =
      (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (ε - 1) *
        (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) *
          ((1 - (x : ℂ) ^ ε) / ε)) *
        ((2 - 3 * ε) * (Gamma (1 - 2 * ε) * Gamma (1 + ε) / Gamma (2 - ε))) := by
  set A : ℝ → ℂ := fun x => (x : ℂ) ^ (ε - 1) *
    (((i12H x : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) with hAd
  set B : ℝ → ℂ := fun s => (s : ℂ) ^ (-ε - 1) with hBd
  set C : ℝ → ℂ := fun u => (2 - 3 * ε) * ((u : ℂ) ^ (-2 * ε) * ((1 - u : ℝ) : ℂ) ^ ε)
    with hCd
  have mA : Measurable A := by rw [hAd]; unfold i12H; fun_prop
  have mB : Measurable B := by rw [hBd]; fun_prop
  have mC : Measurable C := by rw [hCd]; fun_prop
  have hA : IntegrableOn A (Ioo 0 1) := i12HS_integrableOn_P (2 * ε - 1) h0
  have hB : ∀ b, IntegrableOn B (Ioo 1 b) := fun b => by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
    refine ContinuousOn.cpow_const (continuous_ofReal.continuousOn) fun s hs => ?_
    exact ofReal_mem_slitPlane.2 (zero_lt_one.trans_le hs.1)
  obtain ⟨iC, vC⟩ := i12HS_beta_unit (p := -2 * ε) (q := ε) (by simp; linarith)
    (by linarith)
  have hC : IntegrableOn C (Ioo 0 1) := iC.const_mul _
  obtain ⟨hI, hE⟩ := i12HS_dom_prod mA mB mC hA hB (i12HS_norm_cpow_Ioo_le h0) hC
  have heq : EqOn (fun z : ℝ × ℝ × ℝ => A z.1 * B z.2.1 * C z.2.2)
      (fun z : ℝ × ℝ × ℝ => i12SecWt ε z.1 z.2.1 *
        ((((i12H z.1 : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)) *
          i12HSFt ε z.2.1 z.2.2)) i12HSDom := fun z hz => by
    obtain ⟨hs, -, hu⟩ := hz
    simp only [hAd, hBd, hCd]
    exact (i12HS_domTerm_eq ε (zero_lt_one.trans hs) hu.1 hu.2).symm
  refine ⟨hI.congr_fun heq measurableSet_i12HSDom, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_i12HSDom heq, hE]
  have hε : ε ≠ 0 := fun h => by rw [h] at h0; simp at h0
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [hBd, hAd]
    rw [i12HS_integral_Ioo_one_cpow hε hx.1 hx.2]
  · rw [hCd, integral_const_mul, vC]
    congr 2
    · ring_nf
    · ring_nf

end QED.ThreeLoopD
