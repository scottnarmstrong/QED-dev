/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Jet
public import QED.ThreeLoopD.SetDMastersI5C0Ang
public import QED.ThreeLoopD.SetDMastersI8R1Jet

/-!
# Set (d), master `I₅`: the first Taylor coefficient of the kernel as an integral

On `U = 1 + a + c > 0` and `X = c² + a t + c w` with `re X > 0` (`re w = t > 0`), the triangle
integrand is `U ^ (-1 + 2ε) X ^ (-1 - ε) = U⁻¹ X⁻¹ exp ((2 log U - log X) ε)`
(`QED.ThreeLoopD.i5TriF_eq_exp`), and the angular weight is
`(1 - z²) ^ (1/2 - ε) = √(1 - z²) exp (-log (1 - z²) ε)` (`QED.ThreeLoopD.i5Wt_eq_exp`). With the
uniform bounds of `QED.ThreeLoopD.norm_i5TriF_le_dom` and `QED.ThreeLoopD.norm_i5KerF_le`, the
Taylor coefficients of the parametric integrals are the integrals of the pointwise coefficients
(`QED.ThreeLoopD.i5Jet_integral`, over any measurable set of any measure space). Hence, with
`Tₖ(t, w) = ∫∫ U⁻¹ X⁻¹ (2 log U - log X)ᵏ / k!` (`QED.ThreeLoopD.i5TriC`) and
`N_ε = N₀ (1 + (1 - 2 log 2) ε + …)`, `N₀ = 2/π`,

  `K₁(t) = (1 - 2 log 2) K₀(t)`
    `+ (2/π) ∫₋₁¹ √(1 - z²) (T₁(t, w) - log (1 - z²) T₀(t, w)) / w dz`, `w = t - 2i√t z`

(`QED.ThreeLoopD.i5KerC_one_eq`, `QED.ThreeLoopD.i5KerFC_one`), and `T₀(t, w) = i5Tri 0 t w`
(`QED.ThreeLoopD.i5TriC_zero`).

## Main results

* `QED.ThreeLoopD.i5Jet_integral`, `QED.ThreeLoopD.i13Jet_i5Tri`, `QED.ThreeLoopD.i13Jet_i5KerI`.
* `QED.ThreeLoopD.i5KerC_one_eq`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric
open scoped Nat

namespace QED.ThreeLoopD

/-! ### Jets of parametric integrals over a general measure space -/

/-- **The jet of a parametric integral** over a measurable set of a general measure space: the
coefficients are the integrals of the pointwise coefficients. -/
theorem i5Jet_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {g : α → ℂ → ℂ} {c : α → ℕ → ℂ} {R ρ : ℝ} {M : α → ℝ}
    (hs : MeasurableSet s) (hρ : 0 < ρ) (hρR : ρ < R) (hMi : IntegrableOn M s μ)
    (hd : ∀ x ∈ s, DifferentiableOn ℂ (g x) (ball 0 R))
    (hm : ∀ ε ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun x => g x ε) (μ.restrict s))
    (hb : ∀ x ∈ s, ∀ ε : ℂ, ‖ε‖ = ρ → ‖g x ε‖ ≤ M x)
    (hc : ∀ x ∈ s, ∀ k, i13Dsl (g x) k 0 = c x k) :
    I13Jet (fun ε => ∫ x in s, g x ε ∂μ) fun k => ∫ x in s, c x k ∂μ := by
  have hd' : ∀ᵐ x ∂(μ.restrict s), DifferentiableOn ℂ (g x) (ball 0 R) :=
    ae_restrict_of_forall_mem hs hd
  have hb' : ∀ᵐ x ∂(μ.restrict s), ∀ ε : ℂ, ‖ε‖ = ρ → ‖g x ε‖ ≤ M x :=
    ae_restrict_of_forall_mem hs hb
  have hball : ∀ ε : ℂ, ‖ε‖ ≤ ρ → ε ∈ ball (0 : ℂ) R := fun ε hε => by
    rw [mem_ball, dist_zero_right]; linarith
  have hdiff : DifferentiableOn ℂ (fun ε => ∫ x in s, g x ε ∂μ) (ball 0 (ρ / 2)) := by
    intro ε₀ h0
    have hsub : ∀ ε ∈ ball ε₀ (ρ / 2), ‖ε‖ ≤ ρ := fun ε hε => by
      rw [mem_ball, dist_eq_norm] at hε
      rw [mem_ball, dist_zero_right] at h0
      linarith [norm_sub_norm_le ε ε₀]
    refine (QED.DimReg.differentiableAt_integral_of_holomorphic (F := fun ε x => g x ε)
      (half_pos hρ) hMi (fun ε hε => hm ε (hball ε (hsub ε hε))) ?_ ?_).differentiableWithinAt
    · filter_upwards [hd', hb'] with x hx hxb ε hε
      simpa using norm_i13Dsl_le hρ hρR hx hxb 0 ε (hsub ε hε)
    · filter_upwards [hd'] with x hx
      exact hx.mono fun ε hε => hball ε (hsub ε hε)
  refine ⟨ρ / 2, half_pos hρ, hdiff, fun k => ?_⟩
  have H := hasTruncLaurent_integral_i13Dsl hρ hρR hMi hd' hm hb' (k + 1)
  rw [i13Dsl_zero_eq_of_hasTruncLaurent (half_pos hρ) hdiff H k (Nat.lt_succ_self k)]
  exact setIntegral_congr_fun hs fun x hx => hc x hx k

/-! ### The triangle -/

/-- `2 log U - log X`, the exponent rate of the triangle integrand. -/
noncomputable def i5TriL (t : ℝ) (w : ℂ) (q : ℝ × ℝ) : ℂ :=
  2 * ((Real.log (1 + q.1 + q.2) : ℝ) : ℂ) - log (i5X t w q)

/-- The Taylor coefficients `U⁻¹ X⁻¹ (2 log U - log X)ᵏ / k!` of the triangle integrand. -/
noncomputable def i5TriFC (t : ℝ) (w : ℂ) (q : ℝ × ℝ) (k : ℕ) : ℂ :=
  ((1 + q.1 + q.2 : ℝ) : ℂ)⁻¹ * (i5X t w q)⁻¹ * (i5TriL t w q ^ k / (k ! : ℂ))

/-- The Taylor coefficients `Tₖ(t, w)` of the triangle. -/
noncomputable def i5TriC (t : ℝ) (w : ℂ) (k : ℕ) : ℂ :=
  ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5TriFC t w q k

theorem i5_U_pos {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) : 0 < 1 + q.1 + q.2 := by
  obtain ⟨h1, h2⟩ := hq
  simp only [mem_Ioi] at h1 h2
  linarith

theorem i5TriF_eq_exp {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (ε : ℂ) :
    i5TriF ε t w q =
      ((1 + q.1 + q.2 : ℝ) : ℂ)⁻¹ * (i5X t w q)⁻¹ * exp (i5TriL t w q * ε) := by
  have hU0 := i5_U_pos hq
  have hU : ((1 + q.1 + q.2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hU0.ne'
  have hX := i5X_ne_zero ht hw hq
  have e1 : ((1 + q.1 + q.2 : ℝ) : ℂ)⁻¹ = exp (-log ((1 + q.1 + q.2 : ℝ) : ℂ)) := by
    rw [exp_neg, exp_log hU]
  have e2 : (i5X t w q)⁻¹ = exp (-log (i5X t w q)) := by rw [exp_neg, exp_log hX]
  unfold i5TriF i5TriL
  rw [cpow_def_of_ne_zero hU, cpow_def_of_ne_zero hX, e1, e2, ← exp_add, ← exp_add,
    ← exp_add, ofReal_log hU0.le]
  congr 1
  ring

theorem i5Dsl_TriF {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (k : ℕ) :
    i13Dsl (fun ε => i5TriF ε t w q) k 0 = i5TriFC t w q k :=
  (((i13Jet_exp (i5TriL t w q)).const_mul
    (((1 + q.1 + q.2 : ℝ) : ℂ)⁻¹ * (i5X t w q)⁻¹)).congr
      (funext fun ε => (i5TriF_eq_exp ht hw hq ε).symm)).dsl_eq k

theorem differentiableOn_i5TriF {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (s : Set ℂ) :
    DifferentiableOn ℂ (fun ε => i5TriF ε t w q) s := by
  have hU : ((1 + q.1 + q.2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (i5_U_pos hq).ne'
  have hX := i5X_ne_zero ht hw hq
  intro ε _
  unfold i5TriF
  exact ((DifferentiableAt.const_cpow (by fun_prop) (Or.inl hU)).mul
    (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hX))).differentiableWithinAt

/-- **The jet of the triangle** in `ε`, at `re w = t > 0`. -/
theorem i13Jet_i5Tri {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w.re = t) :
    I13Jet (fun ε => i5Tri ε t w) (i5TriC t w) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  exact (i5Jet_integral (μ := volume) (g := fun q ε => i5TriF ε t w q) (c := i5TriFC t w)
    (R := 1 / 4) (ρ := 1 / 8) (M := fun q => Real.exp (Real.pi / 8) * i5TriDom t q) hS
    (by norm_num) (by norm_num) ((integrableOn_i5TriDom ht).const_mul _)
    (fun q hq => differentiableOn_i5TriF ht hw hq _)
    (fun ε _ => (measurable_i5TriF ε t w).aestronglyMeasurable)
    (fun q hq ε hε => norm_i5TriF_le_dom (by rw [hε]; norm_num) ht hw hq)
    (fun q hq k => i5Dsl_TriF ht hw hq k)).congr (funext fun ε => (i5Tri_eq ε t w).symm)

theorem i5TriC_zero (t : ℝ) (w : ℂ) : i5TriC t w 0 = i5Tri 0 t w := by
  rw [i5Tri_eq]
  unfold i5TriC i5TriFC
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp [i5TriF_zero]

theorem i5TriFC_one (t : ℝ) (w : ℂ) (q : ℝ × ℝ) :
    i5TriFC t w q 1 = ((1 + q.1 + q.2 : ℝ) : ℂ)⁻¹ * (i5X t w q)⁻¹ * i5TriL t w q := by
  simp [i5TriFC]

/-! ### The kernel -/

theorem i5Wt_eq_exp {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) (ε : ℂ) :
    ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) =
      ((√(1 - z ^ 2) : ℝ) : ℂ) * exp (((-Real.log (1 - z ^ 2) : ℝ) : ℂ) * ε) := by
  have hr := i5_one_sub_sq_pos hz
  rw [← i13_cpow_neg_eq_exp hr, ← i5_wt_zero hz, ← cpow_add _ _ (ofReal_ne_zero.mpr hr.ne')]
  congr 1
  ring

/-- The Taylor coefficients `√(1 - z²) (-log (1 - z²))ᵏ / k!` of the angular weight. -/
noncomputable def i5WtC (z : ℝ) (k : ℕ) : ℂ :=
  ((√(1 - z ^ 2) : ℝ) : ℂ) * (((-Real.log (1 - z ^ 2) : ℝ) : ℂ) ^ k / (k ! : ℂ))

/-- The Taylor coefficients of the integrand `QED.ThreeLoopD.i5KerF` of the kernel. -/
noncomputable def i5KerFC (t z : ℝ) (k : ℕ) : ℂ :=
  (i5W t z)⁻¹ * i13Cauchy (i5WtC z) (i5TriC t (i5W t z)) k

/-- The Taylor coefficients of the angular integral `∫₋₁¹ i5KerF ε t z dz`. -/
noncomputable def i5KerIC (t : ℝ) (k : ℕ) : ℂ := ∫ z in Ioo (-1 : ℝ) 1, i5KerFC t z k

theorem i13Jet_i5KerF {t : ℝ} (ht : 0 < t) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    I13Jet (fun ε => i5KerF ε t z) (i5KerFC t z) :=
  ((((i13Jet_exp ((-Real.log (1 - z ^ 2) : ℝ) : ℂ)).const_mul
    ((√(1 - z ^ 2) : ℝ) : ℂ)).mul' (i13Jet_i5Tri ht (re_i5W t z))).const_mul
      (i5W t z)⁻¹).congr (funext fun ε => by
        unfold i5KerF
        rw [i5Wt_eq_exp hz]
        field_simp) |>.congr_coeff fun k => by
          unfold i5KerFC i5WtC
          simp only [i13Cauchy]

theorem differentiableOn_i5KerF {t : ℝ} (ht : 0 < t) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableOn ℂ (fun ε => i5KerF ε t z) (ball 0 (1 / 4)) := by
  have hT := differentiableOn_i5Tri ht (re_i5W t z)
  intro ε hε
  have hTa := (hT ε hε).differentiableAt (isOpen_ball.mem_nhds hε)
  unfold i5KerF
  exact (((DifferentiableAt.const_cpow (by fun_prop)
    (Or.inl (ofReal_ne_zero.mpr (i5_one_sub_sq_pos hz).ne'))).mul hTa).div_const
      _).differentiableWithinAt

/-- **The jet of the angular integral** of the kernel. -/
theorem i13Jet_i5KerI {t : ℝ} (ht : 0 < t) :
    I13Jet (fun ε => ∫ z in Ioo (-1 : ℝ) 1, i5KerF ε t z) (i5KerIC t) :=
  i8Jet_integral (g := fun z ε => i5KerF ε t z) (c := i5KerFC t) (R := 1 / 4) (ρ := 1 / 8)
    (M := fun _ => i5TriB t / t) measurableSet_Ioo (by norm_num) (by norm_num)
    (integrableOn_const (by simp))
    (fun z hz => differentiableOn_i5KerF ht hz)
    (fun ε _ => ((measurable_i5KerF_uncurry ε).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (fun z hz ε hε => norm_i5KerF_le (by rw [hε]; norm_num) ht hz)
    (fun z hz k => (i13Jet_i5KerF ht hz).dsl_eq k)

theorem i5Nrm_eq_half (ε : ℂ) : i5Nrm ε = 1 / 2 * i8Nrm ε := by
  unfold i5Nrm i8Nrm
  ring

/-- **The jet of the kernel**. -/
theorem i13Jet_i5Ker' {t : ℝ} (ht : 0 < t) :
    I13Jet (fun ε => i5Ker ε t) (i13Cauchy (fun k => 1 / 2 * i8NC k) (i5KerIC t)) :=
  (((i8Jet_Nrm.const_mul (1 / 2)).congr (funext fun ε => (i5Nrm_eq_half ε).symm)).mul'
    (i13Jet_i5KerI ht)).congr (funext fun ε => (i5Ker_eq ε t).symm)

theorem i5KerC_eq {t : ℝ} (ht : 0 < t) (k : ℕ) :
    i5KerC t k = i13Cauchy (fun k => 1 / 2 * i8NC k) (i5KerIC t) k :=
  (i13Jet_i5Ker' ht).dsl_eq k

theorem i5Ker_zero_eq_KerIC {t : ℝ} (ht : 0 < t) :
    i5Ker 0 t = 2 / (Real.pi : ℂ) * i5KerIC t 0 := by
  rw [← i5KerC_zero, i5KerC_eq ht]
  simp only [i13Cauchy, Finset.sum_range_succ, Finset.sum_range_zero, i8NC_zero]
  ring

/-- **The first Taylor coefficient of the kernel**:
`K₁(t) = (1 - 2 log 2) K₀(t) + (2/π) ∫₋₁¹ (Taylor coefficient 1 of i5KerF) dz`. -/
theorem i5KerC_one_eq {t : ℝ} (ht : 0 < t) :
    i5KerC t 1 = (1 - 2 * (Real.log 2 : ℂ)) * i5Ker 0 t + 2 / (Real.pi : ℂ) * i5KerIC t 1 := by
  rw [i5KerC_eq ht, i5Ker_zero_eq_KerIC ht]
  simp only [i13Cauchy, Finset.sum_range_succ, Finset.sum_range_zero, i8NC_zero, i8NC_one]
  ring

/-- The first coefficient of the integrand: `(√(1 - z²) T₁ - √(1 - z²) log (1 - z²) T₀) / w`. -/
theorem i5KerFC_one (t z : ℝ) :
    i5KerFC t z 1 = (i5W t z)⁻¹ * (((√(1 - z ^ 2) : ℝ) : ℂ) * i5TriC t (i5W t z) 1 -
      ((√(1 - z ^ 2) : ℝ) : ℂ) * ((Real.log (1 - z ^ 2) : ℝ) : ℂ) * i5Tri 0 t (i5W t z)) := by
  simp only [i5KerFC, i13Cauchy, i5WtC, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  rw [i5TriC_zero]
  ring

end QED.ThreeLoopD
