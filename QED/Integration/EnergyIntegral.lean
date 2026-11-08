/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Energy integrals by analytic continuation (obligation O-7)

Under the energy-first prescription M1 for Minkowski loop integrals
(`docs/REGULARIZATION.md`, section 4), the inner integral over the loop energy
`t = ℓ̃⁰` at fixed spatial momentum has the form `∫ (-t² + w)^{-n} dt`, with
`w = |ℓ̃|² + D - iε`. Since `Re w > 0` and `Im w < 0`, `-w` lies in the slit plane.
The textbook evaluates these integrals by rotating the contour
(`srednicki-draft` (14.16)); this module evaluates them without contour
deformation. It computes the real case explicitly, then extends it to the slit
plane by holomorphy in the parameter and the identity theorem.

## Main statements

* `QED.Integration.integral_inv_one_add_sq_sq` and
  `QED.Integration.integral_inv_one_add_sq_cube`: `∫ (1 + t²)⁻² = π/2` and
  `∫ (1 + t²)⁻³ = 3π/8`.
* `QED.Integration.exists_lower_bound_add_of_mem_slitPlane`: a locally uniform
  bound `‖s + z‖ ≥ c (1 + s)` for `s ≥ 0` near any point of the slit plane.
* `QED.Integration.integral_sq_add_zpow_of_real`: the continuation principle. If
  `∫ (t² + a)^{-n} = C a^{1/2 - n}` for all real `a > 0`, then the same formula
  holds on the whole slit plane, with the principal branch.
* `QED.Integration.integral_sq_add_zpow_two`, `integral_sq_add_zpow_three`,
  `integral_sq_mul_sq_add_zpow_three`: `∫ (t² + z)⁻² = (π/2) z^{-3/2}`,
  `∫ (t² + z)⁻³ = (3π/8) z^{-5/2}`, and `∫ t² (t² + z)⁻³ = (π/8) z^{-3/2}`.
* `QED.Integration.integral_neg_sq_add_zpow_three` and
  `QED.Integration.integral_sq_mul_neg_sq_add_zpow_three`: obligation O-7 of
  `docs/ONE-LOOP-DERIVATION.md` in the mostly-plus form:
  `∫ (-t² + w)⁻³ = -(3π/8)(-w)^{-5/2}` and `∫ t² (-t² + w)⁻³ = -(π/8)(-w)^{-3/2}`.
-/

public section

open Complex Metric Filter Topology MeasureTheory
open scoped ComplexOrder
open Real (arctan tendsto_arctan_atTop tendsto_arctan_atBot)
open scoped Real

namespace QED.Integration

/-- `t / (1 + t²) → 0` as `t → ∞`. -/
lemma tendsto_div_one_add_sq_atTop : Tendsto (fun t : ℝ => t / (1 + t ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (1 + t ^ 2) / t) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [id, le_div_iff₀ ht]; nlinarith
  refine h1.inv_tendsto_atTop.congr' ?_
  filter_upwards with t
  simp [inv_div]

/-- `t / (1 + t²) → 0` as `t → -∞`. -/
lemma tendsto_div_one_add_sq_atBot : Tendsto (fun t : ℝ => t / (1 + t ^ 2)) atBot (𝓝 0) := by
  have h := (tendsto_div_one_add_sq_atTop.comp tendsto_neg_atBot_atTop).neg
  rw [neg_zero] at h
  refine h.congr fun t => ?_
  simp [neg_div]

/-- `(1 + t²)⁻¹ → 0` as `t → ∞`. -/
lemma tendsto_inv_one_add_sq_atTop : Tendsto (fun t : ℝ => (1 + t ^ 2)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))

/-- `(1 + t²)⁻¹ → 0` as `t → -∞`. -/
lemma tendsto_inv_one_add_sq_atBot : Tendsto (fun t : ℝ => (1 + t ^ 2)⁻¹) atBot (𝓝 0) := by
  have h := tendsto_inv_one_add_sq_atTop.comp tendsto_neg_atBot_atTop
  refine h.congr fun t => ?_
  simp

/-- `((1 + t²)^n)⁻¹` is integrable on `ℝ` for `n ≥ 1`. -/
lemma integrable_inv_one_add_sq_pow (n : ℕ) (hn : 1 ≤ n) :
    Integrable fun t : ℝ => ((1 + t ^ 2) ^ n)⁻¹ := by
  refine integrable_inv_one_add_sq.mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  have h1 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact inv_anti₀ (by positivity) (le_self_pow₀ h1 (by omega))

/-- `∫ (1 + t²)⁻² dt = π/2`. -/
theorem integral_inv_one_add_sq_sq : ∫ t : ℝ, ((1 + t ^ 2) ^ 2)⁻¹ = π / 2 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t => t / (2 * (1 + t ^ 2)) + arctan t / 2)
      (((1 + t ^ 2) ^ 2)⁻¹) t := by
    intro t
    have h1 : 0 < 1 + t ^ 2 := by positivity
    have h2 : HasDerivAt (fun t : ℝ => 2 * (1 + t ^ 2)) (2 * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1).const_mul 2
    have hq : HasDerivAt (fun t : ℝ => t / (2 * (1 + t ^ 2)))
        ((1 * (2 * (1 + t ^ 2)) - t * (2 * (2 * t))) / (2 * (1 + t ^ 2)) ^ 2) t :=
      (hasDerivAt_id' t).div h2 (by positivity)
    refine (hq.add ((Real.hasDerivAt_arctan t).div_const 2)).congr_deriv ?_
    field_simp
    ring
  have hbot : Tendsto (fun t : ℝ => t / (2 * (1 + t ^ 2)) + arctan t / 2) atBot (𝓝 (0 + (-(π / 2)) / 2)) := by
    refine Tendsto.add ?_ ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot).div_const 2)
    have := tendsto_div_one_add_sq_atBot.div_const 2
    simpa [div_div, mul_comm] using this
  have htop : Tendsto (fun t : ℝ => t / (2 * (1 + t ^ 2)) + arctan t / 2) atTop (𝓝 (0 + (π / 2) / 2)) := by
    refine Tendsto.add ?_ ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).div_const 2)
    have := tendsto_div_one_add_sq_atTop.div_const 2
    simpa [div_div, mul_comm] using this
  rw [integral_of_hasDerivAt_of_tendsto hderiv (integrable_inv_one_add_sq_pow 2 (by norm_num)) hbot htop]
  ring

/-- `∫ (1 + t²)⁻³ dt = 3π/8`. -/
theorem integral_inv_one_add_sq_cube : ∫ t : ℝ, ((1 + t ^ 2) ^ 3)⁻¹ = 3 * π / 8 := by
  set F : ℝ → ℝ := fun t => t / (4 * (1 + t ^ 2) ^ 2) + 3 * t / (8 * (1 + t ^ 2)) + 3 / 8 * arctan t
    with hF
  have hderiv : ∀ t : ℝ, HasDerivAt F (((1 + t ^ 2) ^ 3)⁻¹) t := by
    intro t
    have h1 : 0 < 1 + t ^ 2 := by positivity
    have hA : HasDerivAt (fun t : ℝ => 4 * (1 + t ^ 2) ^ 2) (4 * (2 * (1 + t ^ 2) * (2 * t))) t := by
      have := (((hasDerivAt_pow 2 t).const_add 1).pow 2).const_mul 4
      simpa using this
    have hB : HasDerivAt (fun t : ℝ => 8 * (1 + t ^ 2)) (8 * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1).const_mul 8
    have hq1 : HasDerivAt (fun t : ℝ => t / (4 * (1 + t ^ 2) ^ 2))
        ((1 * (4 * (1 + t ^ 2) ^ 2) - t * (4 * (2 * (1 + t ^ 2) * (2 * t)))) /
          (4 * (1 + t ^ 2) ^ 2) ^ 2) t :=
      (hasDerivAt_id' t).div hA (by positivity)
    have hq2 : HasDerivAt (fun t : ℝ => 3 * t / (8 * (1 + t ^ 2)))
        ((3 * (8 * (1 + t ^ 2)) - 3 * t * (8 * (2 * t))) / (8 * (1 + t ^ 2)) ^ 2) t := by
      have h3 : HasDerivAt (fun t : ℝ => 3 * t) 3 t := by
        simpa using (hasDerivAt_id' t).const_mul 3
      exact h3.div hB (by positivity)
    refine ((hq1.add hq2).add ((Real.hasDerivAt_arctan t).const_mul (3 / 8))).congr_deriv ?_
    field_simp
    ring
  have hlim : ∀ {l : Filter ℝ} {L : ℝ}, Tendsto (fun t : ℝ => t / (1 + t ^ 2)) l (𝓝 0) →
      Tendsto (fun t : ℝ => (1 + t ^ 2)⁻¹) l (𝓝 0) → Tendsto arctan l (𝓝 L) →
      Tendsto F l (𝓝 (3 / 8 * L)) := by
    intro l L h1 h2 h3
    have e : F = fun t => (t / (1 + t ^ 2)) * (1 + t ^ 2)⁻¹ / 4 + 3 / 8 * (t / (1 + t ^ 2))
        + 3 / 8 * arctan t := by
      funext t
      have : (1 + t ^ 2) ≠ 0 := by positivity
      simp only [hF]
      field_simp
    rw [e]
    have := ((h1.mul h2).div_const 4).add (h1.const_mul (3 / 8)) |>.add (h3.const_mul (3 / 8))
    simpa using this
  have hbot := hlim tendsto_div_one_add_sq_atBot tendsto_inv_one_add_sq_atBot
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
  have htop := hlim tendsto_div_one_add_sq_atTop tendsto_inv_one_add_sq_atTop
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)
  rw [integral_of_hasDerivAt_of_tendsto hderiv (integrable_inv_one_add_sq_pow 3 (by norm_num)) hbot htop]
  ring


/-- Near any point of the slit plane, `‖s + z‖ ≥ c (1 + s)` uniformly for `s ≥ 0`. -/
theorem exists_lower_bound_add_of_mem_slitPlane {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    ∃ δ > 0, ∃ c > 0, ∀ z ∈ ball z₀ δ, ∀ s : ℝ, 0 ≤ s → c * (1 + s) ≤ ‖(s : ℂ) + z‖ := by
  rcases hz₀ with hre | him
  · refine ⟨z₀.re / 2, by positivity, min 1 (z₀.re / 2), by positivity, fun z hz s hs => ?_⟩
    have hzre : z₀.re / 2 ≤ z.re := by
      have := abs_re_le_norm (z - z₀)
      rw [mem_ball, dist_eq] at hz
      have h2 := (abs_le.mp (this.trans hz.le)).1
      simp only [sub_re] at h2
      linarith
    have h1 : ((s : ℂ) + z).re ≤ ‖(s : ℂ) + z‖ := re_le_norm _
    simp only [add_re, ofReal_re] at h1
    have hm1 : min 1 (z₀.re / 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (z₀.re / 2) ≤ z₀.re / 2 := min_le_right _ _
    nlinarith
  · set η := |z₀.im| / 2 with hη
    have hηpos : 0 < η := by positivity
    set R := ‖z₀‖ + η with hR
    have hRnn : 0 ≤ R := by positivity
    refine ⟨η, hηpos, η / (1 + R + η), by positivity, fun z hz s hs => ?_⟩
    rw [mem_ball, dist_eq] at hz
    have him' : η ≤ |z.im| := by
      have := abs_im_le_norm (z - z₀)
      have h3 : |z₀.im| - |z.im| ≤ |z.im - z₀.im| := by
        have := abs_sub_abs_le_abs_sub z₀.im z.im
        rw [abs_sub_comm] at this; linarith [abs_sub_comm z.im z₀.im]
      simp only [sub_im] at this
      linarith
    have hre' : -R ≤ z.re := by
      have h4 : ‖z‖ ≤ ‖z₀‖ + η := by
        have := norm_le_norm_add_norm_sub' z z₀
        linarith [norm_sub_rev z z₀]
      have := neg_abs_le z.re
      linarith [abs_re_le_norm z]
    have hA : η ≤ ‖(s : ℂ) + z‖ := by
      have := abs_im_le_norm ((s : ℂ) + z)
      simp only [add_im, ofReal_im, zero_add] at this
      linarith
    have hB : s - R ≤ ‖(s : ℂ) + z‖ := by
      have := re_le_norm ((s : ℂ) + z)
      simp only [add_re, ofReal_re] at this
      linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    by_cases hsR : s ≤ R + η
    · nlinarith
    · have hsR' := not_le.mp hsR
      nlinarith

/-- The lower bound forces `t² + z ≠ 0`. -/
theorem sq_add_ne_zero_of_lower_bound {z : ℂ} {c : ℝ} (hc : 0 < c)
    (h : ∀ s : ℝ, 0 ≤ s → c * (1 + s) ≤ ‖(s : ℂ) + z‖) (t : ℝ) : (t : ℂ) ^ 2 + z ≠ 0 := by
  intro h0
  have := h (t ^ 2) (sq_nonneg t)
  rw [ofReal_pow, h0, norm_zero] at this
  nlinarith [sq_nonneg t]

/-- Norm bound `‖(t² + z)^{-m}‖ ≤ c^{-m} (1 + t²)^{-1}` from the lower bound, for `m ≥ 1`. -/
theorem norm_sq_add_zpow_le {z : ℂ} {c : ℝ} (hc : 0 < c)
    (h : ∀ s : ℝ, 0 ≤ s → c * (1 + s) ≤ ‖(s : ℂ) + z‖) (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    ‖((t : ℂ) ^ 2 + z) ^ (-(m : ℤ))‖ ≤ (c ^ m)⁻¹ * (1 + t ^ 2)⁻¹ := by
  have hb := h (t ^ 2) (sq_nonneg t)
  rw [ofReal_pow] at hb
  have h1 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hpos : 0 < c * (1 + t ^ 2) := by positivity
  rw [zpow_neg, zpow_natCast, norm_inv, norm_pow]
  calc (‖(t : ℂ) ^ 2 + z‖ ^ m)⁻¹ ≤ ((c * (1 + t ^ 2)) ^ m)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hb m)
    _ = (c ^ m)⁻¹ * ((1 + t ^ 2) ^ m)⁻¹ := by rw [mul_pow, mul_inv]
    _ ≤ (c ^ m)⁻¹ * (1 + t ^ 2)⁻¹ := by
        gcongr
        exact le_self_pow₀ h1 (by omega)

/-- **Continuation to the slit plane.** If `∫ (t² + a)^{-n} dt = C a^{1/2 - n}` for all real
`a > 0`, then `∫ (t² + z)^{-n} dt = C z^{1/2 - n}` for every `z` in the slit plane, with the
principal branch. This replaces contour rotation (Wick rotation) of the energy integral. -/
theorem integral_sq_add_zpow_of_real (n : ℕ) (hn : 1 ≤ n) (C : ℂ)
    (hreal : ∀ a : ℝ, 0 < a →
      ∫ t : ℝ, ((t : ℂ) ^ 2 + a) ^ (-(n : ℤ)) = C * (a : ℂ) ^ ((1 / 2 : ℂ) - n))
    {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t : ℝ, ((t : ℂ) ^ 2 + z) ^ (-(n : ℤ)) = C * z ^ ((1 / 2 : ℂ) - n) := by
  set G : ℂ → ℂ := fun z => ∫ t : ℝ, ((t : ℂ) ^ 2 + z) ^ (-(n : ℤ)) with hG
  set H : ℂ → ℂ := fun z => C * z ^ ((1 / 2 : ℂ) - n) with hH
  -- `G` is complex differentiable on the slit plane
  have hGd : DifferentiableOn ℂ G slitPlane := by
    intro z₀ hz₀
    obtain ⟨δ, hδ, c, hc, hbd⟩ := exists_lower_bound_add_of_mem_slitPlane hz₀
    have hne : ∀ z ∈ ball z₀ δ, ∀ t : ℝ, (t : ℂ) ^ 2 + z ≠ 0 := fun z hz' t =>
      sq_add_ne_zero_of_lower_bound hc (hbd z hz') t
    have hcont : ∀ z ∈ ball z₀ δ, ∀ m : ℤ, Continuous fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ m :=
      fun z hz' m => Continuous.zpow₀ (by fun_prop) m fun t => Or.inl (hne z hz' t)
    set F' : ℂ → ℝ → ℂ := fun z t => ((-(n : ℤ) : ℤ) : ℂ) * ((t : ℂ) ^ 2 + z) ^ (-((n + 1 : ℕ) : ℤ))
    have hmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ (-(n : ℤ))) :=
      by filter_upwards [ball_mem_nhds z₀ hδ] with z hz' using (hcont z hz' _).aestronglyMeasurable
    have hint : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + z₀) ^ (-(n : ℤ)) :=
      (integrable_inv_one_add_sq.const_mul (c ^ n)⁻¹).mono' (hcont z₀ (mem_ball_self hδ) _).aestronglyMeasurable
        (Eventually.of_forall fun t => norm_sq_add_zpow_le hc (hbd z₀ (mem_ball_self hδ)) n hn t)
    have hF'meas : AEStronglyMeasurable (F' z₀) :=
      ((hcont z₀ (mem_ball_self hδ) _).const_smul ((-(n : ℤ) : ℤ) : ℂ)).aestronglyMeasurable
    have hbound : ∀ᵐ t : ℝ, ∀ z ∈ ball z₀ δ, ‖F' z t‖ ≤ n * (c ^ (n + 1))⁻¹ * (1 + t ^ 2)⁻¹ := by
      refine Eventually.of_forall fun t z hz' => ?_
      simp only [F', norm_mul, Int.cast_neg, Int.cast_natCast, norm_neg, Complex.norm_natCast]
      rw [mul_assoc]
      gcongr
      exact norm_sq_add_zpow_le hc (hbd z hz') (n + 1) (by omega) t
    have hdiff : ∀ᵐ t : ℝ, ∀ z ∈ ball z₀ δ,
        HasDerivAt (fun z => ((t : ℂ) ^ 2 + z) ^ (-(n : ℤ))) (F' z t) z := by
      refine Eventually.of_forall fun t z hz' => ?_
      have h1 := (hasDerivAt_zpow (-(n : ℤ)) ((t : ℂ) ^ 2 + z) (Or.inl (hne z hz' t))).comp z
        ((hasDerivAt_id' z).const_add ((t : ℂ) ^ 2))
      refine h1.congr_deriv ?_
      simp only [F', mul_one]
      congr 2
      push_cast; ring
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z₀ hδ) hmeas hint hF'meas
      hbound ((integrable_inv_one_add_sq.const_mul _)) hdiff
    exact this.2.differentiableAt.differentiableWithinAt
  have hHd : DifferentiableOn ℂ H slitPlane := fun z hz =>
    ((differentiableAt_id.cpow_const hz).const_mul C).differentiableWithinAt
  have hGa := hGd.analyticOnNhd isOpen_slitPlane
  have hHa := hHd.analyticOnNhd isOpen_slitPlane
  have hpre : IsPreconnected slitPlane :=
    ((starConvex_slitPlane (by norm_num : (0 : ℂ) < 1)).isPathConnected (by simp [mem_slitPlane_iff])).isConnected.isPreconnected
  -- agreement on real points accumulating at `1`
  set u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hu
  have hupos : ∀ k : ℕ, 0 < 1 + 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hutend : Tendsto u atTop (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h1 : Tendsto (fun k : ℕ => (1 : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_add 1
      rw [add_zero] at h1
      have h2 := (continuous_ofReal.tendsto 1).comp h1
      rw [ofReal_one] at h2
      exact h2
    · simp only [u, Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg re h
      simp only [ofReal_re, one_re] at this
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), G w = H w :=
    hutend.frequently (Eventually.frequently (Eventually.of_forall fun k => hreal _ (hupos k)))
  exact hGa.eqOn_of_preconnected_of_frequently_eq hHa hpre (by simp [mem_slitPlane_iff]) hfreq hz

/-- Scaling: `∫ ((t² + a)^n)⁻¹ dt = a^{1/2 - n} ∫ ((1 + s²)^n)⁻¹ ds` for `a > 0`. -/
theorem integral_inv_sq_add_pow_real (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ, ((t ^ 2 + a) ^ n)⁻¹ = a ^ ((1 / 2 : ℝ) - n) * ∫ s : ℝ, ((1 + s ^ 2) ^ n)⁻¹ := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hscale := Measure.integral_comp_mul_left (fun t : ℝ => ((t ^ 2 + a) ^ n)⁻¹) (Real.sqrt a)
  have hpt : ∀ x : ℝ, (((Real.sqrt a * x) ^ 2 + a) ^ n)⁻¹ = (a ^ n)⁻¹ * ((1 + x ^ 2) ^ n)⁻¹ := by
    intro x
    rw [mul_pow, Real.sq_sqrt ha.le, show a * x ^ 2 + a = a * (1 + x ^ 2) by ring, mul_pow, mul_inv]
  simp only [hpt, integral_const_mul] at hscale
  rw [abs_of_pos (inv_pos.mpr hsa), smul_eq_mul] at hscale
  have : ∫ t : ℝ, ((t ^ 2 + a) ^ n)⁻¹ = Real.sqrt a * ((a ^ n)⁻¹ * ∫ s : ℝ, ((1 + s ^ 2) ^ n)⁻¹) := by
    rw [hscale, ← mul_assoc, mul_inv_cancel₀ hsa.ne', one_mul]
  rw [this, ← mul_assoc]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_sub ha, Real.rpow_natCast]
  ring

/-- The complex integrand at a real point: `∫ (t² + a)^{-n} = C a^{1/2 - n}` from the real value
`∫ (1 + s²)^{-n} = K`. -/
theorem integral_sq_add_zpow_ofReal (n : ℕ) {a : ℝ} (ha : 0 < a) {K : ℝ}
    (hK : ∫ s : ℝ, ((1 + s ^ 2) ^ n)⁻¹ = K) :
    ∫ t : ℝ, ((t : ℂ) ^ 2 + a) ^ (-(n : ℤ)) = (K : ℂ) * (a : ℂ) ^ ((1 / 2 : ℂ) - n) := by
  have h1 : ∀ t : ℝ, ((t : ℂ) ^ 2 + a) ^ (-(n : ℤ)) = (((((t ^ 2 + a) ^ n)⁻¹ : ℝ)) : ℂ) := by
    intro t; push_cast; rw [zpow_neg, zpow_natCast]
  simp_rw [h1]
  rw [integral_complex_ofReal, integral_inv_sq_add_pow_real n ha, hK, mul_comm, Complex.ofReal_mul,
    Complex.ofReal_cpow ha.le]
  push_cast; ring_nf

/-- `∫ (t² + z)⁻² dt = (π/2) z^{-3/2}` on the slit plane. -/
theorem integral_sq_add_zpow_two {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t : ℝ, ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) = (π / 2 : ℂ) * z ^ (-(3 / 2 : ℂ)) := by
  have := integral_sq_add_zpow_of_real 2 (by norm_num) ((π / 2 : ℝ) : ℂ)
    (fun a ha => integral_sq_add_zpow_ofReal 2 ha integral_inv_one_add_sq_sq) hz
  push_cast at this
  rw [this]; norm_num

/-- `∫ (t² + z)⁻³ dt = (3π/8) z^{-5/2}` on the slit plane. -/
theorem integral_sq_add_zpow_three {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t : ℝ, ((t : ℂ) ^ 2 + z) ^ (-3 : ℤ) = (3 * π / 8 : ℂ) * z ^ (-(5 / 2 : ℂ)) := by
  have := integral_sq_add_zpow_of_real 3 (by norm_num) ((3 * π / 8 : ℝ) : ℂ)
    (fun a ha => integral_sq_add_zpow_ofReal 3 ha integral_inv_one_add_sq_cube) hz
  push_cast at this
  rw [this]; norm_num

/-- The integrand `(t² + z)^{-m}` is integrable for `z` in the slit plane and `m ≥ 1`. -/
theorem integrable_sq_add_zpow {z : ℂ} (hz : z ∈ slitPlane) (m : ℕ) (hm : 1 ≤ m) :
    Integrable fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ (-(m : ℤ)) := by
  obtain ⟨δ, hδ, c, hc, hbd⟩ := exists_lower_bound_add_of_mem_slitPlane hz
  have hb := hbd z (mem_ball_self hδ)
  refine (integrable_inv_one_add_sq.const_mul (c ^ m)⁻¹).mono'
    (Continuous.zpow₀ (by fun_prop) _ fun t => Or.inl (sq_add_ne_zero_of_lower_bound hc hb t)).aestronglyMeasurable
    (Eventually.of_forall fun t => norm_sq_add_zpow_le hc hb m hm t)

/-- `∫ t² (t² + z)⁻³ dt = (π/8) z^{-3/2}` on the slit plane. -/
theorem integral_sq_mul_sq_add_zpow_three {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t : ℝ, (t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-3 : ℤ) = (π / 8 : ℂ) * z ^ (-(3 / 2 : ℂ)) := by
  obtain ⟨δ, hδ, c, hc, hbd⟩ := exists_lower_bound_add_of_mem_slitPlane hz
  have hne := sq_add_ne_zero_of_lower_bound hc (hbd z (mem_ball_self hδ))
  have hpt : ∀ t : ℝ, (t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-3 : ℤ)
      = ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) - z * ((t : ℂ) ^ 2 + z) ^ (-3 : ℤ) := by
    intro t
    have h := hne t
    rw [show (-2 : ℤ) = 1 + (-3) by norm_num, zpow_add₀ h, zpow_one]
    ring
  have i2 : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ (-2 : ℤ) := by
    simpa using integrable_sq_add_zpow hz 2 (by norm_num)
  have i3 : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + z) ^ (-3 : ℤ) := by
    simpa using integrable_sq_add_zpow hz 3 (by norm_num)
  simp_rw [hpt]
  rw [integral_sub i2 (i3.const_mul z), integral_const_mul]
  have h2 := integral_sq_add_zpow_two hz
  have h3 := integral_sq_add_zpow_three hz
  rw [h2, h3]
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have : z ^ (-(3 / 2 : ℂ)) = z * z ^ (-(5 / 2 : ℂ)) := by
    rw [show -(3 / 2 : ℂ) = 1 + (-(5 / 2)) by norm_num, Complex.cpow_add _ _ hz0, Complex.cpow_one]
  rw [this]
  ring

/-- **Obligation O-7 (first form)**, in the mostly-plus metric: for `-w` in the slit plane
(equivalently `w ∉ [0, ∞)`), `∫ (-t² + w)⁻³ dt = -(3π/8) (-w)^{-5/2}`. -/
theorem integral_neg_sq_add_zpow_three {w : ℂ} (hw : -w ∈ slitPlane) :
    ∫ t : ℝ, (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ) = -((3 * π / 8 : ℂ) * (-w) ^ (-(5 / 2 : ℂ))) := by
  have hpt : ∀ t : ℝ, (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ) = -(((t : ℂ) ^ 2 + -w) ^ (-3 : ℤ)) := by
    intro t
    rw [show -(t : ℂ) ^ 2 + w = -((t : ℂ) ^ 2 + -w) by ring, Odd.neg_zpow (by decide)]
  simp_rw [hpt]
  rw [integral_neg, integral_sq_add_zpow_three hw]

/-- **Obligation O-7 (second form)**: `∫ t² (-t² + w)⁻³ dt = -(π/8) (-w)^{-3/2}` for `-w` in
the slit plane. -/
theorem integral_sq_mul_neg_sq_add_zpow_three {w : ℂ} (hw : -w ∈ slitPlane) :
    ∫ t : ℝ, (t : ℂ) ^ 2 * (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ) = -((π / 8 : ℂ) * (-w) ^ (-(3 / 2 : ℂ))) := by
  have hpt : ∀ t : ℝ, (t : ℂ) ^ 2 * (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ)
      = -((t : ℂ) ^ 2 * ((t : ℂ) ^ 2 + -w) ^ (-3 : ℤ)) := by
    intro t
    rw [show -(t : ℂ) ^ 2 + w = -((t : ℂ) ^ 2 + -w) by ring, Odd.neg_zpow (by decide)]
    ring
  simp_rw [hpt]
  rw [integral_neg, integral_sq_mul_sq_add_zpow_three hw]

end QED.Integration

end
