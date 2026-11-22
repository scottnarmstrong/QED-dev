/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Analytic
public import QED.ThreeLoopD.SetDMastersLaurent
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Set (d), master `I₉`: the Taylor coefficients of `K` are integrals

The integrand of `QED.ThreeLoopD.i9K` is, on the open square, the exponential sum
`c ^ (2ε - 1) w ^ (2ε - 1) (P ^ s - w ^ s - c ^ s) = ∑ⱼ ± exp (aⱼ + ε bⱼ)` (`s = 1 - 3ε`,
`P = c (1 - w)² + w`), with
`a₁ = L_P - L_c - L_w`, `b₁ = 2L_c + 2L_w - 3L_P`, `a₂ = -L_c`, `b₂ = 2L_c - L_w`, `a₃ = -L_w`,
`b₃ = 2L_w - L_c` (`L_t = log t`). Its `k`-th `ε`-derivative is `∑ⱼ ± bⱼ ^ k exp (aⱼ + ε bⱼ)`
(`QED.ThreeLoopD.i9KD`). The derivatives are dominated by the Cauchy estimates
`‖∂ᵏ F‖ ≤ b / ρ ^ k` on `‖ε‖ < 1/20 - kρ`, from the bound `b` of
`QED.ThreeLoopD.norm_i9K_integrand_le`; so the iterated derivatives of `K` are the integrals of
the iterated derivatives of the integrand. With Taylor's theorem for analytic functions this
gives, for every `n`,

  `K(ε) = ∑_{k < n} Kₖ εᵏ + O(εⁿ)`,
  `Kₖ = (1/k!) ∫∫ (b₁ᵏ P - b₂ᵏ w - b₃ᵏ c) / (c w) dx dw` (`QED.ThreeLoopD.i9KCoeff`).

## Main results

* `QED.ThreeLoopD.norm_le_of_hasDerivAt_chain`: Cauchy estimates along a chain of derivatives.
* `QED.ThreeLoopD.iteratedDeriv_integral_of_chain`: iterated differentiation under the integral.
* `QED.ThreeLoopD.hasTruncLaurent_integral_of_chain`: the truncated Taylor expansion.
* `QED.ThreeLoopD.hasTruncLaurent_i9K_coeff`:
  `HasTruncLaurent i9K (fun ε => ∑ k ∈ range n, Kₖ εᵏ) n`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-! ### Iterated derivatives under the integral sign -/

/-- **Cauchy estimates along a chain of derivatives**: if `D (k + 1)` is the derivative of
`D k` everywhere and `‖D 0‖ ≤ C` on `‖ε‖ < R`, then `‖D k‖ ≤ C / ρ ^ k` on `‖ε‖ < R - kρ`. -/
theorem norm_le_of_hasDerivAt_chain {D : ℕ → ℂ → ℂ} {R ρ C : ℝ} (hρ : 0 < ρ)
    (hD : ∀ k ε, HasDerivAt (D k) (D (k + 1) ε) ε)
    (hb : ∀ ε : ℂ, ‖ε‖ < R → ‖D 0 ε‖ ≤ C) :
    ∀ k : ℕ, ∀ ε : ℂ, ‖ε‖ < R - k * ρ → ‖D k ε‖ ≤ C / ρ ^ k := by
  intro k
  induction k with
  | zero => intro ε hε; simpa using hb ε (by simpa using hε)
  | succ k ih =>
    intro ε hε
    have hk : (((k + 1 : ℕ) : ℝ)) * ρ = k * ρ + ρ := by push_cast; ring
    rw [hk] at hε
    have hdiff : Differentiable ℂ (D k) := fun e => (hD k e).differentiableAt
    have h := norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdiff.diffContOnCl
      (C := C / ρ ^ k) fun z hz => ih z (by
        have := norm_sub_norm_le z ε
        rw [mem_sphere, dist_eq_norm] at hz
        linarith)
    rw [(hD k ε).deriv] at h
    rwa [pow_succ, ← div_div]

/-- **Iterated differentiation under the integral sign**, for a chain of derivatives `D k`
dominated at order `0` by an integrable function on `‖ε‖ < R`. -/
theorem iteratedDeriv_integral_of_chain {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {D : ℕ → ℂ → α → ℂ} {b : α → ℝ} {R ρ : ℝ} (hρ : 0 < ρ)
    (hD : ∀ᵐ z ∂μ, ∀ k ε, HasDerivAt (fun e => D k e z) (D (k + 1) ε z) ε)
    (hb : ∀ᵐ z ∂μ, ∀ ε : ℂ, ‖ε‖ < R → ‖D 0 ε z‖ ≤ b z) (hbi : Integrable b μ)
    (hm : ∀ k ε, AEStronglyMeasurable (D k ε) μ) :
    ∀ k : ℕ, ∀ ε : ℂ, ‖ε‖ < R - k * ρ →
      iteratedDeriv k (fun e => ∫ z, D 0 e z ∂μ) ε = ∫ z, D k ε z ∂μ := by
  have hbd : ∀ k : ℕ, ∀ᵐ z ∂μ, ∀ ε : ℂ, ‖ε‖ < R - k * ρ → ‖D k ε z‖ ≤ b z / ρ ^ k :=
    fun k => by
      filter_upwards [hD, hb] with z hz hbz
      exact norm_le_of_hasDerivAt_chain (D := fun k e => D k e z) hρ hz hbz k
  have hint : ∀ (k : ℕ) ε, ‖ε‖ < R - k * ρ → Integrable (D k ε) μ := fun k ε hε =>
    (hbi.div_const (ρ ^ k)).mono' (hm k ε) (by filter_upwards [hbd k] with z hz using hz ε hε)
  intro k
  induction k with
  | zero => intro ε _; simp
  | succ k ih =>
    intro ε hε
    have hk : (((k + 1 : ℕ) : ℝ)) * ρ = k * ρ + ρ := by push_cast; ring
    rw [hk] at hε
    have hk' : ‖ε‖ < R - k * ρ := by linarith
    have hδ : 0 < R - (k * ρ + ρ) - ‖ε‖ := by linarith
    have heq : iteratedDeriv k (fun e => ∫ z, D 0 e z ∂μ) =ᶠ[𝓝 ε]
        fun e => ∫ z, D k e z ∂μ := by
      have hO : IsOpen {e : ℂ | ‖e‖ < R - k * ρ} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hO.mem_nhds hk'] with e he using ih e he
    rw [iteratedDeriv_succ, heq.deriv_eq]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds ε hδ)
      (Eventually.of_forall fun e => hm k e) (hint k ε hk') (hm (k + 1) ε) ?_
      (hbi.div_const (ρ ^ (k + 1))) ?_).2.deriv
    · filter_upwards [hbd (k + 1)] with z hz e he
      refine hz e ?_
      rw [mem_ball, dist_eq_norm] at he
      have := norm_sub_norm_le e ε
      rw [hk]
      linarith
    · filter_upwards [hD] with z hz e _ using hz k e

/-- **The truncated Taylor expansion of a parametric integral**: under the hypotheses of
`iteratedDeriv_integral_of_chain`, if the integral is analytic at `0` and `nρ < R`, its
expansion to `O(εⁿ)` has the coefficients `(1/k!) ∫ D k 0`. -/
theorem hasTruncLaurent_integral_of_chain {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {D : ℕ → ℂ → α → ℂ} {b : α → ℝ} {R ρ : ℝ} (hρ : 0 < ρ)
    (hD : ∀ᵐ z ∂μ, ∀ k ε, HasDerivAt (fun e => D k e z) (D (k + 1) ε z) ε)
    (hb : ∀ᵐ z ∂μ, ∀ ε : ℂ, ‖ε‖ < R → ‖D 0 ε z‖ ≤ b z) (hbi : Integrable b μ)
    (hm : ∀ k ε, AEStronglyMeasurable (D k ε) μ)
    (han : AnalyticAt ℂ (fun e => ∫ z, D 0 e z ∂μ) 0) {n : ℕ} (hn : n * ρ < R) :
    HasTruncLaurent (fun e => ∫ z, D 0 e z ∂μ)
      (fun ε => ∑ k ∈ Finset.range n, (∫ z, D k 0 z ∂μ) / k.factorial * ε ^ k) n := by
  obtain ⟨F, hF, hev⟩ := han.exists_eventuallyEq_sum_add_pow_mul n
  refine ⟨F, hF, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hev] with ε hε
  rw [hε, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : (k : ℝ) * ρ < R := by
    have : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
    nlinarith
  rw [iteratedDeriv_integral_of_chain hρ hD hb hbi hm k 0 (by simpa using hkn), smul_eq_mul]
  ring

/-! ### The integrand of `K` as an exponential sum -/

/-- `b₁ = 2 L_c + 2 L_w - 3 L_P`. -/
noncomputable def i9KB1 (x w : ℝ) : ℝ :=
  2 * Real.log (x * (1 - x)) + 2 * Real.log w - 3 * Real.log (i9Poly x w 1)

/-- `b₂ = 2 L_c - L_w`. -/
noncomputable def i9KB2 (x w : ℝ) : ℝ := 2 * Real.log (x * (1 - x)) - Real.log w

/-- `b₃ = 2 L_w - L_c`. -/
noncomputable def i9KB3 (x w : ℝ) : ℝ := 2 * Real.log w - Real.log (x * (1 - x))

/-- `a₁ = L_P - L_c - L_w`. -/
noncomputable def i9KA1 (x w : ℝ) : ℝ :=
  Real.log (i9Poly x w 1) - Real.log (x * (1 - x)) - Real.log w

/-- `bᵏ exp (a + ε b)`. -/
noncomputable def i9KExp (k : ℕ) (a b : ℝ) (ε : ℂ) : ℂ := (b : ℂ) ^ k * exp (a + ε * b)

/-- **The `k`-th `ε`-derivative of the integrand of `K`**. -/
noncomputable def i9KD (k : ℕ) (ε : ℂ) (z : ℝ × ℝ) : ℂ :=
  i9KExp k (i9KA1 z.1 z.2) (i9KB1 z.1 z.2) ε -
    i9KExp k (-Real.log (z.1 * (1 - z.1))) (i9KB2 z.1 z.2) ε -
    i9KExp k (-Real.log z.2) (i9KB3 z.1 z.2) ε

/-- The integrand of the Taylor coefficient `Kₖ`:
`(b₁ᵏ P - b₂ᵏ w - b₃ᵏ c) / (k! c w)`. -/
noncomputable def i9KCoeffFun (k : ℕ) (x w : ℝ) : ℝ :=
  (i9KB1 x w ^ k * i9Poly x w 1 - i9KB2 x w ^ k * w - i9KB3 x w ^ k * (x * (1 - x))) /
    (k.factorial * (x * (1 - x) * w))

/-- **The Taylor coefficient `Kₖ`** of `K` at `ε = 0`. -/
noncomputable def i9KCoeff (k : ℕ) : ℝ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9KCoeffFun k z.1 z.2

theorem hasDerivAt_i9KExp (k : ℕ) (a b : ℝ) (ε : ℂ) :
    HasDerivAt (i9KExp k a b) (i9KExp (k + 1) a b ε) ε := by
  have h := ((((hasDerivAt_id' ε).mul_const (b : ℂ)).const_add (a : ℂ)).cexp).const_mul
    ((b : ℂ) ^ k)
  unfold i9KExp
  convert h using 1
  ring

theorem hasDerivAt_i9KD (k : ℕ) (ε : ℂ) (z : ℝ × ℝ) :
    HasDerivAt (fun e => i9KD k e z) (i9KD (k + 1) ε z) ε :=
  ((hasDerivAt_i9KExp k _ _ ε).sub (hasDerivAt_i9KExp k _ _ ε)).sub (hasDerivAt_i9KExp k _ _ ε)

theorem measurable_i9KD (k : ℕ) (ε : ℂ) : Measurable (i9KD k ε) := by
  unfold i9KD i9KExp i9KA1 i9KB1 i9KB2 i9KB3 i9Poly
  fun_prop

theorem i9_cpow_eq_exp {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ((t : ℝ) : ℂ) ^ z = exp ((Real.log t : ℂ) * z) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'), ofReal_log ht.le]

theorem i9Poly_one_pos {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 < i9Poly x w 1 := by
  unfold i9Poly
  have := i9_c_pos hx
  have := hw.1
  positivity

/-- On the open square the integrand of `K` is `i9KD 0`. -/
theorem i9KD_zero_eq {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) (ε : ℂ) :
    i9KD 0 ε (x, w) = i9Wt ε x w * i9Psi ε x w 1 := by
  have hc := i9_c_pos hx
  have hP := i9Poly_one_pos hx hw
  unfold i9KD i9KExp i9Wt i9Psi
  rw [mul_one, i9_cpow_eq_exp hc, i9_cpow_eq_exp hw.1, i9_cpow_eq_exp hP, i9_cpow_eq_exp hw.1,
    i9_cpow_eq_exp hc]
  simp only [pow_zero, one_mul, mul_sub, ← exp_add]
  unfold i9KA1 i9KB1 i9KB2 i9KB3
  push_cast
  congr 1
  · congr 1
    · congr 1; ring_nf
    · congr 1; ring_nf
  · congr 1; ring_nf

/-- At `ε = 0`, `i9KD k 0 / k!` is the integrand of `Kₖ`. -/
theorem i9KD_at_zero {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    i9KD k 0 (x, w) / k.factorial = (i9KCoeffFun k x w : ℂ) := by
  have hc := i9_c_pos hx
  have hP := i9Poly_one_pos hx hw
  have hw0 := hw.1
  have e1 : Real.exp (i9KA1 x w) = i9Poly x w 1 / (x * (1 - x) * w) := by
    rw [i9KA1, Real.exp_sub, Real.exp_sub, Real.exp_log hP, Real.exp_log hc, Real.exp_log hw0,
      div_div]
  have e2 : Real.exp (-Real.log (x * (1 - x))) = 1 / (x * (1 - x)) := by
    rw [Real.exp_neg, Real.exp_log hc, one_div]
  have e3 : Real.exp (-Real.log w) = 1 / w := by rw [Real.exp_neg, Real.exp_log hw0, one_div]
  have hR : i9KB1 x w ^ k * (i9Poly x w 1 / (x * (1 - x) * w)) - i9KB2 x w ^ k * (1 / (x * (1 - x)))
      - i9KB3 x w ^ k * (1 / w) = i9KCoeffFun k x w * k.factorial := by
    unfold i9KCoeffFun
    have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    generalize x * (1 - x) = c at hc ⊢
    field_simp
  unfold i9KD i9KExp
  simp only [zero_mul, add_zero, ← ofReal_exp, e1, e2, e3, ← ofReal_pow, ← ofReal_mul,
    ← ofReal_sub, hR]
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  push_cast
  field_simp

/-! ### The expansion of `K` -/

theorem i9K_eq_integral_i9KD : i9K = fun ε =>
    ∫ z, i9KD 0 ε z ∂(volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  funext ε
  refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun z hz => ?_
  exact (i9KD_zero_eq hz.1 hz.2 ε).symm

/-- **`K` to all orders**: `K(ε) = ∑_{k < n} Kₖ εᵏ + O(εⁿ)`, with `Kₖ = QED.ThreeLoopD.i9KCoeff k`
the integral of the `k`-th `ε`-derivative of the integrand at `0`, divided by `k!`. -/
theorem hasTruncLaurent_i9K_coeff (n : ℕ) :
    HasTruncLaurent i9K (fun ε => ∑ k ∈ Finset.range n, (i9KCoeff k : ℂ) * ε ^ k) n := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hρ : (0 : ℝ) < 1 / (20 * (n + 1)) := by positivity
  have hn : (n : ℝ) * (1 / (20 * (n + 1))) < 1 / 20 := by
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb : ∀ᵐ z ∂μ, ∀ ε : ℂ, ‖ε‖ < 1 / 20 → ‖i9KD 0 ε z‖ ≤
      17 * ((z.1 * (1 - z.1)) ^ (-(17 / 20) : ℝ) * z.2 ^ (-(17 / 20) : ℝ)) :=
    ae_restrict_of_forall_mem hS fun z hz ε hε => by
      rw [show z = (z.1, z.2) from rfl, i9KD_zero_eq hz.1 hz.2]
      exact norm_i9K_integrand_le hε hz.1 hz.2
  have hbi : Integrable (fun z : ℝ × ℝ =>
      17 * ((z.1 * (1 - z.1)) ^ (-(17 / 20) : ℝ) * z.2 ^ (-(17 / 20) : ℝ))) μ := by
    simp only [μ]
    rw [volume_restrict_prod2]
    exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_rpow_Ioo (by norm_num))).const_mul 17
  have han : AnalyticAt ℂ (fun e => ∫ z, i9KD 0 e z ∂μ) 0 := by
    rw [← i9K_eq_integral_i9KD]
    exact analyticOnNhd_i9K 0 (by simp)
  have h := hasTruncLaurent_integral_of_chain hρ
    (Eventually.of_forall fun z k ε => hasDerivAt_i9KD k ε z) hb hbi
    (fun k ε => (measurable_i9KD k ε).aestronglyMeasurable) han hn
  rw [← i9K_eq_integral_i9KD] at h
  convert h using 3 with ε k hk
  rw [← integral_div, i9KCoeff, ← integral_complex_ofReal]
  congr 1
  refine (setIntegral_congr_fun hS fun z hz => ?_).symm
  exact i9KD_at_zero hz.1 hz.2 k

/-! ### The coefficient `K₀` and the target expansion -/

/-- `K₀ = -3/2`: at order `0` the integrand is `(P - w - c) / (c w) = w - 2`. -/
theorem i9KCoeff_zero : i9KCoeff 0 = -3 / 2 := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have h : EqOn (fun z : ℝ × ℝ => i9KCoeffFun 0 z.1 z.2) (fun z => 1 * (z.2 - 2))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := fun z hz => by
    have hc := (i9_c_pos hz.1).ne'
    have hw := hz.2.1.ne'
    simp only [i9KCoeffFun, i9Poly, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one]
    generalize z.1 * (1 - z.1) = c at hc ⊢
    field_simp
    ring
  rw [i9KCoeff, setIntegral_congr_fun hS h, volume_restrict_prod2,
    integral_prod_mul (fun _ : ℝ => (1 : ℝ)) (fun w : ℝ => w - 2),
    ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const]
  norm_num [integral_id]

/-- **The target expansion of `K`** through `ε³` (`ζ(3) = QED.Polylog.zeta3`). -/
noncomputable def i9KTarget (ε : ℂ) : ℂ :=
  -3 / 2 - 10 * ε + (-47 + 31 * (Real.pi : ℂ) ^ 2 / 4 + 3 * (QED.Polylog.zeta3 : ℂ)) * ε ^ 2 +
    (-197 + 265 * (Real.pi : ℂ) ^ 2 / 6 + 144 * (QED.Polylog.zeta3 : ℂ) - (Real.pi : ℂ) ^ 4 / 12 -
      72 * (Real.pi : ℂ) ^ 2 * (Real.log 2 : ℂ)) * ε ^ 3

/-- **`K` through `ε³`, given the coefficients `K₁, K₂, K₃`** (`K₀` is
`QED.ThreeLoopD.i9KCoeff_zero`). -/
theorem hasTruncLaurent_i9K_of_coeff (h1 : i9KCoeff 1 = -10)
    (h2 : i9KCoeff 2 = -47 + 31 * Real.pi ^ 2 / 4 + 3 * QED.Polylog.zeta3)
    (h3 : i9KCoeff 3 = -197 + 265 * Real.pi ^ 2 / 6 + 144 * QED.Polylog.zeta3 - Real.pi ^ 4 / 12 -
      72 * Real.pi ^ 2 * Real.log 2) :
    HasTruncLaurent i9K i9KTarget 4 := by
  obtain ⟨R, hR, hev⟩ := hasTruncLaurent_i9K_coeff 4
  refine ⟨R, hR, hev.mono fun ε hε => ?_⟩
  rw [hε]
  dsimp only
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, i9KCoeff_zero, h1, h2, h3, i9KTarget]
  push_cast
  ring

end QED.ThreeLoopD
