/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9KOne

/-!
# Set (d), master `I₉`: the auxiliary integrals `M` and `B` of `K`

The coefficients `K₂`, `K₃` of `K = QED.ThreeLoopD.i9K` are reduced (in
`QED.ThreeLoopD.SetDMastersI9KValId`) to those of two simpler integrals:

  `M(ε) = ∫∫ (1 - w²) w ^ (2ε - 1) (c ^ (2ε) P ^ (-3ε) - c ^ (-ε)) dx dw`,
  `B(ε) = ∫ c ^ (-ε) dx = B(1 - ε, 1 - ε)`

(`c = x (1 - x)`, `P = c (1 - w)² + w`). In the notation of `QED.ThreeLoopD.SetDMastersI9KTaylor`
the integrand of `M` is `e ^ a (e ^ (ε b₁) - e ^ (ε b₃))` with `e ^ a = (1 - w²) / w`; it is
dominated on `‖ε‖ < 1/20` by `w ^ (-3/5) c ^ (-7/10)`, because `0 ≤ log (P / c) ≤ √(w / c)`.
Both integrals are analytic near `0`, with the Taylor coefficients

  `Mₖ = (1/k!) ∫∫ (1 - w²) (b₁ᵏ - b₃ᵏ) / w`,  `Bₖ = (1/k!) ∫ (-log c)ᵏ`.

## Main results

* `QED.ThreeLoopD.analyticOnNhd_integral_of_chain`: a parametric integral along a dominated chain
  of derivatives is analytic.
* `QED.ThreeLoopD.hasTruncLaurent_i9M_coeff`, `QED.ThreeLoopD.hasTruncLaurent_i9B_coeff`: the
  Taylor expansions of `M` and `B`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-! ### Analyticity along a dominated chain -/

/-- **A parametric integral along a dominated chain of derivatives is analytic** on
`‖ε‖ < R - ρ` (hypotheses of `QED.ThreeLoopD.iteratedDeriv_integral_of_chain`). -/
theorem analyticOnNhd_integral_of_chain {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {D : ℕ → ℂ → α → ℂ} {b : α → ℝ} {R ρ : ℝ} (hρ : 0 < ρ)
    (hD : ∀ᵐ z ∂μ, ∀ k ε, HasDerivAt (fun e => D k e z) (D (k + 1) ε z) ε)
    (hb : ∀ᵐ z ∂μ, ∀ ε : ℂ, ‖ε‖ < R → ‖D 0 ε z‖ ≤ b z) (hbi : Integrable b μ)
    (hm : ∀ k ε, AEStronglyMeasurable (D k ε) μ) :
    AnalyticOnNhd ℂ (fun e => ∫ z, D 0 e z ∂μ) (ball 0 (R - ρ)) := by
  have hbd : ∀ᵐ z ∂μ, ∀ ε : ℂ, ‖ε‖ < R - (1 : ℕ) * ρ → ‖D 1 ε z‖ ≤ b z / ρ ^ 1 := by
    filter_upwards [hD, hb] with z hz hbz
    exact norm_le_of_hasDerivAt_chain (D := fun k e => D k e z) hρ hz hbz 1
  have hd : ∀ ε : ℂ, ‖ε‖ < R - ρ → DifferentiableAt ℂ (fun e => ∫ z, D 0 e z ∂μ) ε := by
    intro ε hε
    have hδ : 0 < R - ρ - ‖ε‖ := by linarith
    have hint : Integrable (D 0 ε) μ := hbi.mono' (hm 0 ε) (by
      filter_upwards [hb] with z hz using hz ε (by linarith))
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds ε hδ)
      (Eventually.of_forall fun e => hm 0 e) hint (hm 1 ε) ?_
      (hbi.div_const (ρ ^ 1)) ?_).2.differentiableAt
    · filter_upwards [hbd] with z hz e he
      refine hz e ?_
      rw [mem_ball, dist_eq_norm] at he
      have := norm_sub_norm_le e ε
      push_cast
      linarith
    · filter_upwards [hD] with z hz e _ using hz 0 e
  intro ε hε
  exact DifferentiableOn.analyticAt (fun e he => (hd e (by simpa using he)).differentiableWithinAt)
    (isOpen_ball.mem_nhds hε)

/-- `QED.ThreeLoopD.hasTruncLaurent_integral_of_chain` with the analyticity derived. -/
theorem hasTruncLaurent_integral_of_chain' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {D : ℕ → ℂ → α → ℂ} {b : α → ℝ} {R ρ : ℝ} (hρ : 0 < ρ)
    (hD : ∀ᵐ z ∂μ, ∀ k ε, HasDerivAt (fun e => D k e z) (D (k + 1) ε z) ε)
    (hb : ∀ᵐ z ∂μ, ∀ ε : ℂ, ‖ε‖ < R → ‖D 0 ε z‖ ≤ b z) (hbi : Integrable b μ)
    (hm : ∀ k ε, AEStronglyMeasurable (D k ε) μ) (hρR : ρ < R) {n : ℕ} (hn : n * ρ < R) :
    HasTruncLaurent (fun e => ∫ z, D 0 e z ∂μ)
      (fun ε => ∑ k ∈ Finset.range n, (∫ z, D k 0 z ∂μ) / k.factorial * ε ^ k) n :=
  hasTruncLaurent_integral_of_chain hρ hD hb hbi hm
    (analyticOnNhd_integral_of_chain hρ hD hb hbi hm 0 (by simpa using hρR)) hn

/-! ### The integral `M` -/

/-- `a = log ((1 - w²) / w)`. -/
noncomputable def i9MA (w : ℝ) : ℝ := Real.log ((1 - w ^ 2) / w)

/-- **The `k`-th `ε`-derivative of the integrand of `M`**:
`e ^ a (b₁ᵏ e ^ (ε b₁) - b₃ᵏ e ^ (ε b₃))`. -/
noncomputable def i9MD (k : ℕ) (ε : ℂ) (z : ℝ × ℝ) : ℂ :=
  i9KExp k (i9MA z.2) (i9KB1 z.1 z.2) ε - i9KExp k (i9MA z.2) (i9KB3 z.1 z.2) ε

/-- **The integral `M(ε) = ∫∫ (1 - w²) w ^ (2ε - 1) (c ^ (2ε) P ^ (-3ε) - c ^ (-ε))`**. -/
noncomputable def i9M (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9MD 0 ε z

/-- The integrand of the Taylor coefficient `Mₖ`: `(1 - w²) (b₁ᵏ - b₃ᵏ) / (k! w)`. -/
noncomputable def i9MCoeffFun (k : ℕ) (x w : ℝ) : ℝ :=
  (1 - w ^ 2) * (i9KB1 x w ^ k - i9KB3 x w ^ k) / (k.factorial * w)

/-- **The Taylor coefficient `Mₖ`** of `M` at `ε = 0`. -/
noncomputable def i9MCoeff (k : ℕ) : ℝ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9MCoeffFun k z.1 z.2

theorem hasDerivAt_i9MD (k : ℕ) (ε : ℂ) (z : ℝ × ℝ) :
    HasDerivAt (fun e => i9MD k e z) (i9MD (k + 1) ε z) ε :=
  (hasDerivAt_i9KExp k _ _ ε).sub (hasDerivAt_i9KExp k _ _ ε)

theorem measurable_i9MD (k : ℕ) (ε : ℂ) : Measurable (i9MD k ε) := by
  unfold i9MD i9KExp i9MA i9KB1 i9KB3 i9Poly
  fun_prop

theorem exp_i9MA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) : Real.exp (i9MA w) = (1 - w ^ 2) / w := by
  have : 0 < 1 - w ^ 2 := by nlinarith [hw.1, hw.2]
  exact Real.exp_log (div_pos this hw.1)

theorem i9MD_at_zero {x w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    i9MD k 0 (x, w) / k.factorial = (i9MCoeffFun k x w : ℂ) := by
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw.1.ne'
  unfold i9MD i9KExp i9MCoeffFun
  simp only [zero_mul, add_zero, ← ofReal_exp, exp_i9MA hw]
  push_cast
  field_simp

/-- `1 + t² ≤ eᵗ` for `t ≥ 0`, i.e. `log (1 + t²) ≤ t`. -/
theorem i9_one_add_sq_le_exp {t : ℝ} (ht : 0 ≤ t) : 1 + t ^ 2 ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [sq_nonneg (t - 3 / 2), mul_nonneg ht (sq_nonneg (t - 3 / 2))]

/-- **The bound on the integrand of `M`**: `‖·‖ ≤ w ^ (-3/5) c ^ (-7/10)` on `‖ε‖ < 1/20`. -/
theorem norm_i9MD_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    ‖i9MD 0 ε (x, w)‖ ≤ w ^ (-(3 / 5) : ℝ) * (x * (1 - x)) ^ (-(7 / 10) : ℝ) := by
  have hc := i9_c_pos hx
  have hP := i9Poly_one_pos hx hw
  have hcP := i9_c_le_poly hx hw
  have hP1 := i9_poly_le_one hx hw
  have hw0 := hw.1
  have hw1 := hw.2
  set c := x * (1 - x) with hcdef
  set P := i9Poly x w 1 with hPdef
  have hc1 : c ≤ 1 := by nlinarith [hx.1, hx.2]
  have hPc : P - c ≤ w := by
    have : P - c = w * (1 - c * (2 - w)) := by rw [hPdef, i9Poly]; ring
    rw [this]
    have : 0 ≤ c * (2 - w) := mul_nonneg hc.le (by linarith)
    nlinarith
  set Lc := Real.log c
  set Lw := Real.log w
  set LP := Real.log P
  have hLc : Lc ≤ 0 := Real.log_nonpos hc.le hc1
  have hLw : Lw ≤ 0 := Real.log_nonpos hw0.le hw1.le
  have hLP : LP ≤ 0 := Real.log_nonpos hP.le hP1
  have hL0 : 0 ≤ LP - Lc := sub_nonneg.mpr (Real.log_le_log hc hcP)
  -- `L = log (P / c) ≤ t = √(w / c)`
  set t := Real.exp ((Lw - Lc) / 2) with ht
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have ht2 : t ^ 2 = w / c := by
    rw [ht, sq, ← Real.exp_add, show (Lw - Lc) / 2 + (Lw - Lc) / 2 = Lw - Lc by ring,
      Real.exp_sub, Real.exp_log hw0, Real.exp_log hc]
  have hLt : LP - Lc ≤ t := by
    have h1 : P / c ≤ 1 + t ^ 2 := by
      rw [ht2, div_le_iff₀ hc, add_mul, div_mul_cancel₀ _ hc.ne']
      linarith
    have h2 := (h1.trans (i9_one_add_sq_le_exp ht0))
    have h3 := Real.log_le_log (div_pos hP hc) h2
    rwa [Real.log_exp, Real.log_div hP.ne' hc.ne'] at h3
  -- the splitting `e ^ a (e ^ (ε b₁) - e ^ (ε b₃)) = e ^ (a + ε b₃) (e ^ (-3 ε L) - 1)`
  have hsplit : i9MD 0 ε (x, w) = exp (i9MA w + ε * i9KB3 x w) *
      (exp (ε * (-3 * ((LP - Lc : ℝ) : ℂ))) - 1) := by
    unfold i9MD i9KExp
    simp only [pow_zero, one_mul]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    unfold i9KB1 i9KB3
    push_cast
    ring
  have hre : |ε.re| ≤ 1 / 20 := (abs_re_le_norm ε).trans hε.le
  have hb3 : |i9KB3 x w| ≤ -2 * Lw - Lc := by
    unfold i9KB3
    rw [abs_le]
    constructor <;> linarith
  have hA : ‖exp (i9MA w + ε * i9KB3 x w)‖ ≤ Real.exp (-Lw) *
      Real.exp (-(1 / 10) * Lw - (1 / 20) * Lc) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e1 : (↑(i9MA w) + ε * ↑(i9KB3 x w)).re = i9MA w + ε.re * i9KB3 x w := by simp
    rw [e1]
    have h1 : i9MA w ≤ -Lw := by
      unfold i9MA
      rw [Real.log_div (by nlinarith) hw0.ne']
      have : Real.log (1 - w ^ 2) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
      linarith
    have h2 : ε.re * i9KB3 x w ≤ (1 / 20) * (-2 * Lw - Lc) := by
      calc ε.re * i9KB3 x w ≤ |ε.re * i9KB3 x w| := le_abs_self _
        _ = |ε.re| * |i9KB3 x w| := abs_mul _ _
        _ ≤ (1 / 20) * (-2 * Lw - Lc) :=
          mul_le_mul hre hb3 (abs_nonneg _) (by norm_num)
    linarith
  have hB : ‖exp (ε * (-3 * ((LP - Lc : ℝ) : ℂ))) - 1‖ ≤
      (3 / 20) * t * Real.exp (-(3 / 20) * Lc) := by
    have hn : ‖ε * (-3 * ((LP - Lc : ℝ) : ℂ))‖ ≤ (3 / 20) * (LP - Lc) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hL0]
      have : ‖(3 : ℂ)‖ = 3 := by simp
      rw [this]
      nlinarith [norm_nonneg ε]
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (ε * (-3 * ((LP - Lc : ℝ) : ℂ))) 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      pow_one] at h
    refine h.trans (mul_le_mul (hn.trans (by nlinarith)) (Real.exp_le_exp.mpr
      (hn.trans (by nlinarith))) (Real.exp_pos _).le (by positivity))
  rw [hsplit, norm_mul]
  calc _ ≤ (Real.exp (-Lw) * Real.exp (-(1 / 10) * Lw - (1 / 20) * Lc)) *
        ((3 / 20) * t * Real.exp (-(3 / 20) * Lc)) :=
        mul_le_mul hA hB (norm_nonneg _) (by positivity)
    _ ≤ Real.exp (Lw * (-(3 / 5))) * Real.exp (Lc * (-(7 / 10))) := by
        rw [ht]
        have e : Real.exp (-Lw) * Real.exp (-(1 / 10) * Lw - (1 / 20) * Lc) *
            (3 / 20 * Real.exp ((Lw - Lc) / 2) * Real.exp (-(3 / 20) * Lc)) =
            (3 / 20) * (Real.exp (Lw * (-(3 / 5))) * Real.exp (Lc * (-(7 / 10)))) := by
          simp only [mul_assoc, mul_left_comm _ (3 / 20 : ℝ)]
          congr 1
          simp only [← Real.exp_add]
          congr 1
          ring
        rw [e]
        have : 0 < Real.exp (Lw * (-(3 / 5))) * Real.exp (Lc * (-(7 / 10))) := by positivity
        linarith
    _ = _ := by rw [Real.rpow_def_of_pos hw0, Real.rpow_def_of_pos hc]

theorem integrable_i9M_bound :
    Integrable (fun z : ℝ × ℝ => z.2 ^ (-(3 / 5) : ℝ) * (z.1 * (1 - z.1)) ^ (-(7 / 10) : ℝ))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  rw [volume_restrict_prod2]
  have h := (integrableOn_mul_one_sub_rpow_Ioo (a := -(7 / 10)) (by norm_num)).mul_prod
    (integrableOn_rpow_Ioo (a := -(3 / 5)) (by norm_num))
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only
  ring

/-- **`M` to all orders**: `M(ε) = ∑_{k < n} Mₖ εᵏ + O(εⁿ)`. -/
theorem hasTruncLaurent_i9M_coeff (n : ℕ) :
    HasTruncLaurent i9M (fun ε => ∑ k ∈ Finset.range n, (i9MCoeff k : ℂ) * ε ^ k) n := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hρ : (0 : ℝ) < 1 / (20 * (n + 2)) := by positivity
  have hn : (n : ℝ) * (1 / (20 * (n + 2))) < 1 / 20 := by
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hρR : (1 : ℝ) / (20 * (n + 2)) < 1 / 20 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith
  have hb : ∀ᵐ z ∂μ, ∀ ε : ℂ, ‖ε‖ < 1 / 20 → ‖i9MD 0 ε z‖ ≤
      z.2 ^ (-(3 / 5) : ℝ) * (z.1 * (1 - z.1)) ^ (-(7 / 10) : ℝ) :=
    ae_restrict_of_forall_mem hS fun z hz ε hε => norm_i9MD_le hε hz.1 hz.2
  change HasTruncLaurent (fun e => ∫ z, i9MD 0 e z ∂μ) _ n
  have h := hasTruncLaurent_integral_of_chain' hρ
    (Eventually.of_forall fun z k ε => hasDerivAt_i9MD k ε z) hb integrable_i9M_bound
    (fun k ε => (measurable_i9MD k ε).aestronglyMeasurable) hρR hn
  convert h using 3 with ε k hk
  rw [← integral_div, i9MCoeff, ← integral_complex_ofReal]
  congr 1
  refine (setIntegral_congr_fun hS fun z hz => ?_).symm
  exact i9MD_at_zero hz.2 k

/-- **`M` is analytic** on `‖ε‖ < 1/40`. -/
theorem analyticOnNhd_i9M : AnalyticOnNhd ℂ i9M (ball 0 (1 / 40)) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have h := analyticOnNhd_integral_of_chain (R := 1 / 20) (ρ := 1 / 40) (by norm_num)
    (μ := volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
    (Eventually.of_forall fun z k ε => hasDerivAt_i9MD k ε z)
    (ae_restrict_of_forall_mem hS fun z hz ε hε => norm_i9MD_le hε hz.1 hz.2)
    integrable_i9M_bound (fun k ε => (measurable_i9MD k ε).aestronglyMeasurable)
  norm_num at h
  exact h

/-! ### The integral `B = B(1 - ε, 1 - ε)` -/

/-- **The `k`-th `ε`-derivative of `c ^ (-ε)`**: `(-log c)ᵏ e ^ (-ε log c)`. -/
noncomputable def i9BD (k : ℕ) (ε : ℂ) (x : ℝ) : ℂ :=
  i9KExp k 0 (-Real.log (x * (1 - x))) ε

/-- **The integral `B(ε) = ∫ c ^ (-ε) dx = B(1 - ε, 1 - ε)`**. -/
noncomputable def i9B (ε : ℂ) : ℂ := ∫ x in Ioo (0 : ℝ) 1, i9BD 0 ε x

/-- **The Taylor coefficient `Bₖ = (1/k!) ∫ (-log c)ᵏ`** of `B` at `ε = 0`. -/
noncomputable def i9BCoeff (k : ℕ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, (-Real.log (x * (1 - x))) ^ k / k.factorial

theorem measurable_i9BD (k : ℕ) (ε : ℂ) : Measurable (i9BD k ε) := by
  unfold i9BD i9KExp
  fun_prop

theorem norm_i9BD_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖i9BD 0 ε x‖ ≤ (x * (1 - x)) ^ (-(1 / 20) : ℝ) := by
  have hc := i9_c_pos hx
  have hc1 : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
  have hL : Real.log (x * (1 - x)) ≤ 0 := Real.log_nonpos hc.le hc1
  have hre : |ε.re| ≤ 1 / 20 := (abs_re_le_norm ε).trans hε.le
  unfold i9BD i9KExp
  rw [pow_zero, one_mul, Complex.norm_exp, Real.rpow_def_of_pos hc]
  apply Real.exp_le_exp.mpr
  have e1 : ((0 : ℝ) + ε * ((-Real.log (x * (1 - x)) : ℝ) : ℂ)).re =
      ε.re * (-Real.log (x * (1 - x))) := by simp
  rw [e1]
  have := abs_le.mp hre
  nlinarith

/-- **`B` to all orders**: `B(ε) = ∑_{k < n} Bₖ εᵏ + O(εⁿ)`, and `B` is analytic on
`‖ε‖ < 1/40`. -/
theorem hasTruncLaurent_i9B_coeff (n : ℕ) :
    HasTruncLaurent i9B (fun ε => ∑ k ∈ Finset.range n, (i9BCoeff k : ℂ) * ε ^ k) n := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hρ : (0 : ℝ) < 1 / (20 * (n + 2)) := by positivity
  have hn : (n : ℝ) * (1 / (20 * (n + 2))) < 1 / 20 := by
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hρR : (1 : ℝ) / (20 * (n + 2)) < 1 / 20 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith
  have hb : ∀ᵐ x ∂μ, ∀ ε : ℂ, ‖ε‖ < 1 / 20 → ‖i9BD 0 ε x‖ ≤ (x * (1 - x)) ^ (-(1 / 20) : ℝ) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ε hε => norm_i9BD_le hε hx
  change HasTruncLaurent (fun e => ∫ x, i9BD 0 e x ∂μ) _ n
  have h := hasTruncLaurent_integral_of_chain' (D := i9BD) hρ
    (Eventually.of_forall fun x k ε => hasDerivAt_i9KExp k _ _ ε) hb
    (integrableOn_mul_one_sub_rpow_Ioo (by norm_num))
    (fun k ε => (measurable_i9BD k ε).aestronglyMeasurable)
    hρR hn
  convert h using 3 with ε k hk
  rw [← integral_div, i9BCoeff, ← integral_complex_ofReal]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  unfold i9BD i9KExp
  simp

theorem analyticOnNhd_i9B : AnalyticOnNhd ℂ i9B (ball 0 (1 / 40)) := by
  have h := analyticOnNhd_integral_of_chain (R := 1 / 20) (ρ := 1 / 40) (by norm_num)
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (D := i9BD)
    (Eventually.of_forall fun x k ε => hasDerivAt_i9KExp k _ _ ε)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ε hε => norm_i9BD_le hε hx)
    (integrableOn_mul_one_sub_rpow_Ioo (by norm_num))
    (fun k ε => (measurable_i9BD k ε).aestronglyMeasurable)
  norm_num at h
  exact h

end QED.ThreeLoopD
