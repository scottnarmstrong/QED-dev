/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Continuation
public import QED.DimReg.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Analyticity of parametric integrals inside their strips of convergence

Analytic regularization rests on one fact: an integral `∫ f(x) exp(s φ(x)) dμ` is holomorphic in
`s` on the open strip between two real abscissae `a < b` at which it converges absolutely
(`QED.DimReg.differentiableOn_integral_mul_exp`). The dependence of a Lee–Pomeransky integral on
the dimension is of this form, `G ^ (-d / 2) = exp(d · (-(1/2) log G))`, and so is the dependence
on one exponent, `xᵢ ^ (νᵢ - 1) = exp(νᵢ log xᵢ) / xᵢ`. Hence:

* `QED.DimReg.analyticOnNhd_lpIntegral_dim`: `d ↦ lpIntegral G ν d` is analytic on
  `{a < re d < b}` when the integral converges at `d = a` and `d = b`;
* `QED.DimReg.analyticOnNhd_lpIntegral_exp`: `νᵢ ↦ lpIntegral G ν d` is analytic on
  `{a < re νᵢ < b}` when it converges at `re νᵢ = a` and `re νᵢ = b`.

A linear relation between such integrals, proved where they all converge, then extends to their
meromorphic continuations (`QED.DimReg.relation_eventuallyEq_of_eqOn`): this is the lifting
step for the integration-by-parts and dimension-shift identities.
-/

public section

open MeasureTheory Set Complex Filter Topology Metric

namespace QED.DimReg

/-- `exp (c φ) ≤ exp (a φ) + exp (b φ)` for `c ∈ [a, b]`. -/
theorem exp_mul_le_add {a b c y : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    Real.exp (c * y) ≤ Real.exp (a * y) + Real.exp (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcb hy)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hac hy)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

/-- `ε |y| exp(t y) ≤ exp((t + ε) y) + exp((t - ε) y)`. -/
theorem mul_abs_mul_exp_le {ε t y : ℝ} :
    ε * |y| * Real.exp (t * y) ≤ Real.exp ((t + ε) * y) + Real.exp ((t - ε) * y) := by
  have hA : ε * |y| ≤ |ε * y| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (le_abs_self ε) (abs_nonneg y)
  have hB : |ε * y| ≤ Real.exp (ε * y) + Real.exp (-(ε * y)) := by
    have e1 := Real.add_one_le_exp (ε * y)
    have e2 := Real.add_one_le_exp (-(ε * y))
    have e3 := Real.exp_pos (ε * y)
    have e4 := Real.exp_pos (-(ε * y))
    rcases abs_cases (ε * y) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have h2 : ε * |y| * Real.exp (t * y) ≤
      (Real.exp (ε * y) + Real.exp (-(ε * y))) * Real.exp (t * y) :=
    mul_le_mul_of_nonneg_right (hA.trans hB) (Real.exp_pos (t * y)).le
  refine h2.trans_eq ?_
  rw [add_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2 <;> ring

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Holomorphy inside the strip of absolute convergence.** If `‖f‖ exp(a φ)` and
`‖f‖ exp(b φ)` are integrable, then `s ↦ ∫ f · exp(s φ)` is complex differentiable on
`{a < re s < b}`. -/
theorem differentiableOn_integral_mul_exp {f : α → ℂ} {φ : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hφ : AEStronglyMeasurable φ μ) {a b : ℝ}
    (ha : Integrable (fun x => ‖f x‖ * Real.exp (a * φ x)) μ)
    (hb : Integrable (fun x => ‖f x‖ * Real.exp (b * φ x)) μ) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x, f x * exp (s * φ x) ∂μ) {s | a < s.re ∧ s.re < b} := by
  intro s₀ hs₀
  obtain ⟨h1, h2⟩ := hs₀
  set ε : ℝ := min (s₀.re - a) (b - s₀.re) / 3 with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hεa : a ≤ s₀.re - 2 * ε := by
    have := min_le_left (s₀.re - a) (b - s₀.re); rw [hεdef]; linarith
  have hεb : s₀.re + 2 * ε ≤ b := by
    have := min_le_right (s₀.re - a) (b - s₀.re); rw [hεdef]; linarith
  have hφc : AEStronglyMeasurable (fun x => (φ x : ℂ)) μ :=
    (continuous_ofReal.comp_aestronglyMeasurable hφ)
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => f x * exp (s * φ x)) μ := fun s =>
    hf.mul (continuous_exp.comp_aestronglyMeasurable (hφc.const_mul s))
  have hnorm : ∀ s : ℂ, ∀ x, ‖f x * exp (s * φ x)‖ = ‖f x‖ * Real.exp (s.re * φ x) := by
    intro s x
    rw [norm_mul, norm_exp]
    simp
  have hsum : Integrable (fun x => ‖f x‖ * Real.exp (a * φ x) + ‖f x‖ * Real.exp (b * φ x)) μ :=
    ha.add hb
  have hint : ∀ c : ℝ, a ≤ c → c ≤ b → Integrable (fun x => f x * exp (c * φ x)) μ := by
    intro c hac hcb
    refine hsum.mono' (by simpa using hmeas c) (Eventually.of_forall fun x => ?_)
    rw [hnorm]
    simp only [ofReal_re]
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (exp_mul_le_add hac hcb) (norm_nonneg _)
  have hint₀ : Integrable (fun x => f x * exp (s₀ * φ x)) μ := by
    refine (hint s₀.re h1.le h2.le).mono (hmeas s₀) ?_
    refine Eventually.of_forall fun x => ?_
    rw [hnorm, hnorm]
    simp
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s₀)
    (F := fun s x => f x * exp (s * φ x)) (F' := fun s x => f x * ((φ x : ℂ) * exp (s * φ x)))
    (bound := fun x => ε⁻¹ * (‖f x‖ * Real.exp (a * φ x) + ‖f x‖ * Real.exp (b * φ x)) * 2)
    (s := ball s₀ ε) (ball_mem_nhds s₀ hε) (Eventually.of_forall hmeas) hint₀
    (hf.mul (hφc.mul (continuous_exp.comp_aestronglyMeasurable (hφc.const_mul s₀))))
    (Eventually.of_forall fun x s hs => ?_) ((hsum.const_mul ε⁻¹).mul_const 2)
    (Eventually.of_forall fun x s _ => ?_)
  · exact (hd.2.differentiableAt).differentiableWithinAt
  · have hre : |s.re - s₀.re| < ε := by
      have := mem_ball.mp hs
      rw [dist_eq_norm] at this
      exact (abs_re_le_norm _).trans_lt (by simpa using this)
    rw [abs_lt] at hre
    rw [norm_mul, norm_mul, norm_exp, norm_real, Real.norm_eq_abs]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    have key := mul_abs_mul_exp_le (ε := ε) (t := s.re) (y := φ x)
    have e1 := exp_mul_le_add (a := a) (b := b) (c := s.re + ε) (y := φ x) (by linarith)
      (by linarith)
    have e2 := exp_mul_le_add (a := a) (b := b) (c := s.re - ε) (y := φ x) (by linarith)
      (by linarith)
    have hb' : |φ x| * Real.exp (s.re * φ x) ≤
        ε⁻¹ * (Real.exp (a * φ x) + Real.exp (b * φ x)) * 2 := by
      have : ε * (|φ x| * Real.exp (s.re * φ x)) ≤
          (Real.exp (a * φ x) + Real.exp (b * φ x)) * 2 := by nlinarith
      rw [show ε⁻¹ * (Real.exp (a * φ x) + Real.exp (b * φ x)) * 2 =
        ε⁻¹ * ((Real.exp (a * φ x) + Real.exp (b * φ x)) * 2) by ring, le_inv_mul_iff₀ hε]
      exact this
    calc ‖f x‖ * (|φ x| * Real.exp (s.re * φ x)) ≤
          ‖f x‖ * (ε⁻¹ * (Real.exp (a * φ x) + Real.exp (b * φ x)) * 2) :=
          mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
      _ = _ := by ring
  · have := ((hasDerivAt_id s).mul_const (φ x : ℂ)).cexp.const_mul (f x)
    simpa [mul_comm] using this

variable {N : ℕ}

/-- On the orthant, `G ^ (-d / 2) = exp (d · (-(1/2) log G))`. -/
theorem ofReal_cpow_neg_half {y : ℝ} (hy : 0 < y) (d : ℂ) :
    (y : ℂ) ^ (-(d / 2)) = exp (d * ((-(Real.log y / 2) : ℝ) : ℂ)) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hy.ne'), ← ofReal_log hy.le]
  congr 1
  push_cast
  ring

/-- **Analyticity in the dimension.** If `G > 0` on the orthant and the Lee–Pomeransky integral
converges absolutely at the real dimensions `a < b`, then `d ↦ lpIntegral G ν d` is analytic on
the strip `a < re d < b`. -/
theorem analyticOnNhd_lpIntegral_dim {G : (Fin N → ℝ) → ℝ} (hG : Measurable G)
    (hpos : ∀ x ∈ posOrthant N, 0 < G x) (ν : Fin N → ℂ) {a b : ℝ}
    (ha : LPConvergent G ν a) (hb : LPConvergent G ν b) :
    AnalyticOnNhd ℂ (fun d => lpIntegral G ν d) {d | a < d.re ∧ d.re < b} := by
  have hopen : IsOpen {d : ℂ | a < d.re ∧ d.re < b} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  set μ := volume.restrict (posOrthant N)
  set f : (Fin N → ℝ) → ℂ := fun x => ∏ i, (x i : ℂ) ^ (ν i - 1)
  set φ : (Fin N → ℝ) → ℝ := fun x => -(Real.log (G x) / 2)
  have hrep : ∀ d : ℂ, lpIntegral G ν d = ∫ x, f x * exp (d * φ x) ∂μ := fun d =>
    setIntegral_congr_fun (measurableSet_posOrthant N) fun x hx => by
      simp only [lpIntegrand, f, φ, ofReal_cpow_neg_half (hpos x hx)]
  have hf : AEStronglyMeasurable f μ := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact Finset.measurable_prod _ fun i _ =>
      (measurable_ofReal.comp (measurable_pi_apply i)).pow_const _
  have hφ : AEStronglyMeasurable φ μ :=
    ((Real.measurable_log.comp hG).div_const 2).neg.aestronglyMeasurable
  have hconv : ∀ c : ℝ, LPConvergent G ν c →
      Integrable (fun x => ‖f x‖ * Real.exp (c * φ x)) μ := by
    intro c hc
    refine hc.norm.congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_posOrthant N)] with x hx
    rw [lpIntegrand, ofReal_cpow_neg_half (hpos x hx), norm_mul, norm_exp]
    simp [f, φ]
  have h := differentiableOn_integral_mul_exp hf hφ (hconv a ha) (hconv b hb)
  exact h.congr fun d _ => hrep d

/-- **Lifting a relation to the continuation.** If finitely many functions `F k`, meromorphic
on `ℂ`, satisfy `∑ c k · F k = 0` on a nonempty open set (where the `F k` are, for example,
convergent parametric integrals), with meromorphic coefficients, then the relation holds in a
punctured neighbourhood of every point of `ℂ`. -/
theorem relation_eventuallyEq_of_eqOn {ι : Type*} (s : Finset ι) {c F : ι → ℂ → ℂ}
    (hc : ∀ k ∈ s, Meromorphic (c k)) (hF : ∀ k ∈ s, Meromorphic (F k)) {V : Set ℂ}
    (hV : IsOpen V) (hne : V.Nonempty) (h : ∀ z ∈ V, ∑ k ∈ s, c k z * F k z = 0) (y : ℂ) :
    ∀ᶠ z in 𝓝[≠] y, ∑ k ∈ s, c k z * F k z = 0 := by
  have hm : Meromorphic fun z => ∑ k ∈ s, c k z * F k z := by
    intro z
    have := MeromorphicAt.sum (s := s) (G := fun k z => c k z * F k z) (x := z)
      fun k hk => (hc k hk z).mul (hF k hk z)
    convert this using 1
    funext w
    simp [Finset.sum_apply]
  have := Meromorphic.eventuallyEq_nhdsNE_of_eqOn hm (fun z => MeromorphicAt.const 0 z) hV hne
    (fun z hz => h z hz) y
  exact this

end QED.DimReg
