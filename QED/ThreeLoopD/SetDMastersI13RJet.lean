/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RemTaylor
public import QED.DimReg.GammaTaylor

/-!
# Set (d), master `I₁₃`: calculus of Taylor coefficients

`QED.ThreeLoopD.i13Dsl f k 0` is the `k`-th Taylor coefficient of `f` at `0`. This file gives the
rules to compute it: `QED.ThreeLoopD.I13Jet f a` says that `f` is holomorphic near `0` with
`Dᵏ f (0) = aₖ` for all `k`. Jets add, scale and multiply (Cauchy product, from the Leibniz rule
`QED.ThreeLoopD.i13Dsl_mul_apply`); the basic ones are the constants, `exp (c ε)`
(`QED.ThreeLoopD.i13Jet_exp`) and `1 / (1 - c ε)` (`QED.ThreeLoopD.i13Jet_geom`). A truncated
expansion `f = ∑_{k < n} aₖ εᵏ + εⁿ R`, `R` analytic at `0`, identifies the first `n` coefficients
(`QED.ThreeLoopD.i13Dsl_zero_eq_of_hasTruncLaurent`).

## Main results

* `QED.ThreeLoopD.I13Jet`, `QED.ThreeLoopD.I13Jet.mul`, `QED.ThreeLoopD.I13Jet.add`.
* `QED.ThreeLoopD.i13Jet_exp`, `QED.ThreeLoopD.i13Jet_geom`.
* `QED.ThreeLoopD.i13Dsl_zero_eq_of_hasTruncLaurent`.
-/

@[expose] public section

open Complex Metric Filter Topology Set
open scoped Nat

namespace QED.ThreeLoopD

/-! ### Uniqueness at `0` -/

theorem i13_eq_zero_of_punct {F H : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hF : ContinuousAt F 0)
    (hH : ContinuousAt H 0) (h : ∀ ε ∈ ball (0 : ℂ) R, ε ≠ 0 → F ε = H ε) : F 0 = H 0 := by
  have hev : F =ᶠ[𝓝[≠] 0] H := eventually_nhdsWithin_iff.mpr
    (eventually_of_mem (ball_mem_nhds 0 hR) fun z hz hz0 => h z hz hz0)
  exact tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
    ((hH.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)

theorem i13_eqOn_of_mul {F H : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hF : ContinuousOn F (ball 0 R))
    (hH : ContinuousOn H (ball 0 R)) (h : ∀ ε ∈ ball (0 : ℂ) R, ε * F ε = ε * H ε) :
    ∀ ε ∈ ball (0 : ℂ) R, F ε = H ε := by
  have hne : ∀ ε ∈ ball (0 : ℂ) R, ε ≠ 0 → F ε = H ε := fun ε hε h0 =>
    mul_left_cancel₀ h0 (h ε hε)
  intro ε hε
  by_cases h0 : ε = 0
  · subst h0
    exact i13_eq_zero_of_punct hR (hF.continuousAt (ball_mem_nhds 0 hR))
      (hH.continuousAt (ball_mem_nhds 0 hR)) hne
  · exact hne ε hε h0

/-! ### Linearity and the Leibniz rule -/

theorem i13Dsl_lin_apply {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R)) (a b : ℂ) (k : ℕ) : ∀ ε ∈ ball (0 : ℂ) R,
    i13Dsl (fun ε => a * f ε + b * g ε) k ε = a * i13Dsl f k ε + b * i13Dsl g k ε := by
  induction k with
  | zero => intro ε _; rfl
  | succ k ih =>
    have hfg : DifferentiableOn ℂ (fun ε => a * f ε + b * g ε) (ball 0 R) :=
      (hf.const_mul a).add (hg.const_mul b)
    refine i13_eqOn_of_mul hR (differentiableOn_i13Dsl hR hfg (k + 1)).continuousOn
      ((((differentiableOn_i13Dsl hR hf (k + 1)).const_mul a).add
        ((differentiableOn_i13Dsl hR hg (k + 1)).const_mul b)).continuousOn) fun ε hε => ?_
    have e1 := i13Dsl_step (fun ε => a * f ε + b * g ε) k ε
    have e2 := i13Dsl_step f k ε
    have e3 := i13Dsl_step g k ε
    rw [ih ε hε, ih 0 (mem_ball_self hR)] at e1
    linear_combination -e1 + a * e2 + b * e3

theorem i13Dsl_mul_apply {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R)) (k : ℕ) : ∀ ε ∈ ball (0 : ℂ) R,
    i13Dsl (fun ε => f ε * g ε) k ε = i13Dsl f k ε * g ε +
      ∑ i ∈ Finset.range k, i13Dsl f i 0 * i13Dsl g (k - i) ε := by
  induction k with
  | zero => intro ε _; simp
  | succ k ih =>
    have hfg : DifferentiableOn ℂ (fun ε => f ε * g ε) (ball 0 R) := hf.mul hg
    have hc : ∀ j, ContinuousOn (i13Dsl g j) (ball 0 R) := fun j =>
      (differentiableOn_i13Dsl hR hg j).continuousOn
    refine i13_eqOn_of_mul hR (differentiableOn_i13Dsl hR hfg (k + 1)).continuousOn
      (((differentiableOn_i13Dsl hR hf (k + 1)).continuousOn.mul hg.continuousOn).add
        (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hc _))) fun ε hε => ?_
    have e1 := i13Dsl_step (fun ε => f ε * g ε) k ε
    rw [ih ε hε, ih 0 (mem_ball_self hR)] at e1
    have e2 := i13Dsl_step f k ε
    have e3 := i13Dsl_step g 0 ε
    simp only [i13Dsl_zero, zero_add] at e3
    have hs : ∑ i ∈ Finset.range k, i13Dsl f i 0 * i13Dsl g (k - i) ε =
        ∑ i ∈ Finset.range k, i13Dsl f i 0 * i13Dsl g (k - i) 0 +
          ε * ∑ i ∈ Finset.range k, i13Dsl f i 0 * i13Dsl g (k + 1 - i) ε := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : k + 1 - i = (k - i) + 1 := by
        have := Finset.mem_range.mp hi; omega
      rw [hik, i13Dsl_step g (k - i) ε]
      ring
    rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega]
    rw [hs] at e1
    linear_combination -e1 + g ε * e2 + i13Dsl f k 0 * e3

theorem i13Dsl_mul_zero {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R)) (k : ℕ) :
    i13Dsl (fun ε => f ε * g ε) k 0 =
      ∑ i ∈ Finset.range (k + 1), i13Dsl f i 0 * i13Dsl g (k - i) 0 := by
  rw [i13Dsl_mul_apply hR hf hg k 0 (mem_ball_self hR), Finset.sum_range_succ, Nat.sub_self]
  simp only [i13Dsl_zero]
  ring

/-! ### Jets -/

/-- `f` is holomorphic near `0` with Taylor coefficients `Dᵏ f (0) = aₖ`. -/
def I13Jet (f : ℂ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∃ R > 0, DifferentiableOn ℂ f (ball 0 R) ∧ ∀ k, i13Dsl f k 0 = a k

theorem I13Jet.of_differentiableOn {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) : I13Jet f fun k => i13Dsl f k 0 :=
  ⟨R, hR, hf, fun _ => rfl⟩

theorem I13Jet.restrict {f : ℂ → ℂ} {a : ℕ → ℂ} (hf : I13Jet f a) {r : ℝ} (hr : 0 < r) :
    ∃ R > 0, R ≤ r ∧ DifferentiableOn ℂ f (ball 0 R) ∧ ∀ k, i13Dsl f k 0 = a k := by
  obtain ⟨R, hR, hd, hk⟩ := hf
  exact ⟨min R r, lt_min hR hr, min_le_right _ _, hd.mono (ball_subset_ball (min_le_left _ _)),
    hk⟩

theorem I13Jet.congr_coeff {f : ℂ → ℂ} {a b : ℕ → ℂ} (hf : I13Jet f a) (h : ∀ k, a k = b k) :
    I13Jet f b := by
  obtain ⟨R, hR, hd, hk⟩ := hf
  exact ⟨R, hR, hd, fun k => (hk k).trans (h k)⟩

theorem I13Jet.lin {f g : ℂ → ℂ} {a b : ℕ → ℂ} (hf : I13Jet f a) (hg : I13Jet g b) (c d : ℂ) :
    I13Jet (fun ε => c * f ε + d * g ε) fun k => c * a k + d * b k := by
  obtain ⟨R, hR, hd, hk⟩ := hf
  obtain ⟨S, hS, hSR, hdg, hkg⟩ := hg.restrict hR
  have hdf := hd.mono (ball_subset_ball hSR)
  refine ⟨S, hS, (hdf.const_mul c).add (hdg.const_mul d), fun k => ?_⟩
  rw [i13Dsl_lin_apply hS hdf hdg c d k 0 (mem_ball_self hS), hk, hkg]

theorem I13Jet.add {f g : ℂ → ℂ} {a b : ℕ → ℂ} (hf : I13Jet f a) (hg : I13Jet g b) :
    I13Jet (fun ε => f ε + g ε) fun k => a k + b k := by
  simpa using hf.lin hg 1 1

theorem I13Jet.sub {f g : ℂ → ℂ} {a b : ℕ → ℂ} (hf : I13Jet f a) (hg : I13Jet g b) :
    I13Jet (fun ε => f ε - g ε) fun k => a k - b k := by
  have h := hf.lin hg 1 (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at h
  exact h

theorem I13Jet.const_mul {f : ℂ → ℂ} {a : ℕ → ℂ} (hf : I13Jet f a) (c : ℂ) :
    I13Jet (fun ε => c * f ε) fun k => c * a k := by
  simpa using hf.lin hf c 0

theorem I13Jet.mul {f g : ℂ → ℂ} {a b : ℕ → ℂ} (hf : I13Jet f a) (hg : I13Jet g b) :
    I13Jet (fun ε => f ε * g ε) fun k => ∑ i ∈ Finset.range (k + 1), a i * b (k - i) := by
  obtain ⟨R, hR, hd, hk⟩ := hf
  obtain ⟨S, hS, hSR, hdg, hkg⟩ := hg.restrict hR
  have hdf := hd.mono (ball_subset_ball hSR)
  refine ⟨S, hS, hdf.mul hdg, fun k => ?_⟩
  rw [i13Dsl_mul_zero hS hdf hdg k]
  simp only [hk, hkg]

theorem I13Jet.congr {f g : ℂ → ℂ} {a : ℕ → ℂ} (hf : I13Jet f a) (h : f = g) : I13Jet g a :=
  h ▸ hf

/-- **Identification from a truncated expansion.** -/
theorem i13Dsl_zero_eq_of_hasTruncLaurent {f : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) {n : ℕ}
    (h : HasTruncLaurent f (fun ε => ∑ k ∈ Finset.range n, a k * ε ^ k) n) :
    ∀ k < n, i13Dsl f k 0 = a k := by
  obtain ⟨Q, hQ, hev⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · intro k hk; omega
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hev)
  set r' := min r R
  have hr' : 0 < r' := lt_min hr hR
  have hfr : DifferentiableOn ℂ f (ball 0 r') := hf.mono (ball_subset_ball (min_le_right _ _))
  have hP : Continuous fun ε : ℂ => ∑ k ∈ Finset.range n, a k * ε ^ k := by fun_prop
  have h0 : f 0 = ∑ k ∈ Finset.range n, a k * (0 : ℂ) ^ k + (0 : ℂ) ^ n * Q 0 :=
    i13_eq_zero_of_punct (F := f)
      (H := fun ε => ∑ k ∈ Finset.range n, a k * ε ^ k + ε ^ n * Q ε) hr'
      (hfr.continuousOn.continuousAt (ball_mem_nhds 0 hr'))
      (hP.continuousAt.add ((continuous_pow n).continuousAt.mul hQ.continuousAt))
      fun ε hε h0 => hball ε (ball_subset_ball (min_le_left _ _) hε) h0
  refine i13Dsl_zero_eq_of_expansion hr' hfr hQ.continuousAt fun ε hε => ?_
  by_cases hε0 : ε = 0
  · subst hε0; exact h0
  · exact hball ε (ball_subset_ball (min_le_left _ _) hε) hε0

/-! ### Basic jets -/

theorem i13Jet_const (c : ℂ) : I13Jet (fun _ => c) fun k => if k = 0 then c else 0 := by
  refine ⟨1, one_pos, differentiableOn_const c, fun k => ?_⟩
  have := i13Dsl_zero_eq_of_expansion (f := fun _ => c) (g := fun _ => 0)
    (a := fun k => if k = 0 then c else 0) one_pos (differentiableOn_const c)
    continuousAt_const (n := k + 1) fun ε _ => by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_one_ne_zero, ite_false, zero_mul, Finset.sum_const_zero, mul_zero,
        add_zero, ite_true, pow_zero, mul_one, zero_add]
  exact this k (Nat.lt_succ_self k)

/-- The remainder of `exp` after `wⁿ⁻¹`, divided by `wⁿ`. -/
noncomputable def i13ExpRem (n : ℕ) (w : ℂ) : ℂ := ∑' m : ℕ, 1 / ((m + n)! : ℂ) * w ^ m

theorem analyticAt_i13ExpRem (n : ℕ) : AnalyticAt ℂ (i13ExpRem n) 0 := by
  refine QED.DimReg.analyticAt_tsum_mul_pow (C := 1) fun m => ?_
  rw [norm_div, norm_one, Complex.norm_natCast]
  exact div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    (by positivity)

theorem exp_eq_i13ExpRem (n : ℕ) (w : ℂ) :
    exp w = ∑ k ∈ Finset.range n, w ^ k / (k ! : ℂ) + w ^ n * i13ExpRem n w := by
  have h : HasSum (fun n => w ^ n / (n ! : ℂ)) (exp w) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp w
  rw [← h.tsum_eq, ← h.summable.sum_add_tsum_nat_add n, i13ExpRem, ← tsum_mul_left]
  congr 1
  congr 1
  funext m
  rw [pow_add]
  ring

theorem i13Jet_exp (c : ℂ) : I13Jet (fun ε => exp (c * ε)) fun k => c ^ k / (k ! : ℂ) := by
  refine ⟨1, one_pos, (by fun_prop : Differentiable ℂ fun ε => exp (c * ε)).differentiableOn,
    fun k => ?_⟩
  have hg : ContinuousAt (fun ε => c ^ (k + 1) * i13ExpRem (k + 1) (c * ε)) 0 :=
    continuousAt_const.mul ((analyticAt_i13ExpRem (k + 1)).continuousAt.comp_of_eq
      (by fun_prop) (by simp))
  refine i13Dsl_zero_eq_of_expansion (n := k + 1) (a := fun k => c ^ k / (k ! : ℂ)) one_pos
    (by fun_prop : Differentiable ℂ fun ε => exp (c * ε)).differentiableOn hg (fun ε _ => ?_) k
    (Nat.lt_succ_self k)
  rw [exp_eq_i13ExpRem (k + 1)]
  simp only [mul_pow]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · ring

theorem i13Jet_geom (c : ℂ) : I13Jet (fun ε => 1 / (1 - c * ε)) fun k => c ^ k := by
  set R := 1 / (‖c‖ + 1)
  have hR : 0 < R := by positivity
  have hne : ∀ ε ∈ ball (0 : ℂ) R, 1 - c * ε ≠ 0 := by
    intro ε hε h
    rw [mem_ball, dist_zero_right] at hε
    have h1 : c * ε = 1 := by linear_combination -h
    have h2 : ‖c‖ * ‖ε‖ < 1 := by
      calc ‖c‖ * ‖ε‖ ≤ ‖c‖ * R := mul_le_mul_of_nonneg_left hε.le (norm_nonneg _)
        _ < 1 := by
          rw [show R = 1 / (‖c‖ + 1) from rfl, mul_one_div, div_lt_one (by positivity)]
          linarith
    rw [← norm_mul, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hd : DifferentiableOn ℂ (fun ε => 1 / (1 - c * ε)) (ball 0 R) := fun ε hε =>
    (DifferentiableAt.div (differentiableAt_const (1 : ℂ))
      (by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => 1 - c * ε) ε)
      (hne ε hε)).differentiableWithinAt
  refine ⟨R, hR, hd, fun k => ?_⟩
  have hg : ContinuousAt (fun ε => c ^ (k + 1) / (1 - c * ε)) 0 :=
    continuousAt_const.div (by fun_prop) (by simp)
  refine i13Dsl_zero_eq_of_expansion (n := k + 1) hR hd hg (fun ε hε => ?_) k
    (Nat.lt_succ_self k)
  have h := hne ε hε
  have hg := geom_sum_mul (c * ε) (k + 1)
  field_simp
  simp only [mul_pow] at hg ⊢
  linear_combination hg

end QED.ThreeLoopD
