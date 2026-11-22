/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValFour
public import QED.Polylog.HPLShuffle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Set (d), master `I₁₅`: integration in the ratio coordinate at weight four

The ratio-coordinate kernels for the `u`-slice are `1/u`, `1/(u+r)` and `1/(u+1/r)`.
The integration-by-parts primitive of a word with first offset `a` is
`(u+a) G(a::w;u) - P(w;u)`. The all-zero words use the logarithmic convention.

Differentiation in `r` gives the upper and lower boundary terms and the contributions
of adjacent offsets. At `u = 1` their coefficients use the harmonic kernels in `r`.
As `r` tends to one, the two positive offsets coalesce, giving ordinary HPL values.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog.HPL
open scoped Interval

namespace QED.ThreeLoopD

/-- Words with kernels `1/(u+a b)`, using the HPL convention for pure zero words. -/
noncomputable def i15FourWord (a : Letter → ℝ) : List Letter → ℝ → ℝ
  | [], _ => 1
  | b :: w, u =>
    if AllZero (b :: w) then log u ^ (w.length + 1) / ((w.length + 1).factorial : ℝ)
    else ∫ t in (0 : ℝ)..u, (t + a b)⁻¹ * i15FourWord a w t

/-- Integration by parts reduces the primitive of a word to that of its tail. -/
noncomputable def i15FourWordPrim (a : Letter → ℝ) : List Letter → ℝ → ℝ
  | [], u => u
  | b :: w, u => (u + a b) * i15FourWord a (b :: w) u - i15FourWordPrim a w u

section PositiveOffsets

variable {a : Letter → ℝ} (ha0 : a .zero = 0)
  (ha : ∀ b ≠ Letter.zero, 0 < a b)

private theorem i15FourWord_allZero {w : List Letter} (hw : AllZero w) (u : ℝ) :
    i15FourWord a w u = log u ^ w.length / (w.length.factorial : ℝ) := by
  cases w with
  | nil => simp [i15FourWord]
  | cons b w => simp only [i15FourWord, hw, ↓reduceIte, List.length_cons]

private theorem i15FourWord_cons_integral {b : Letter} {w : List Letter}
    (hw : ¬AllZero (b :: w)) :
    i15FourWord a (b :: w) = fun u => ∫ t in (0 : ℝ)..u, (t + a b)⁻¹ * i15FourWord a w t := by
  funext u
  simp only [i15FourWord, hw, ↓reduceIte]

include ha0 ha in
private theorem i15FourWord_denom (b : Letter) {u : ℝ} (hu : 0 < u) : 0 < u + a b := by
  by_cases hb : b = .zero
  · simpa [hb, ha0] using hu
  · exact add_pos hu (ha b hb)

private theorem i15FourWord_log_bound {w : List Letter} (hw : AllZero w)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, |i15FourWord a w t| ≤ C * t ^ (-δ) := by
  obtain ⟨C, hC, h⟩ := abs_log_pow_le w.length hδ
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [i15FourWord_allZero hw, abs_div, abs_pow, Nat.abs_cast]
  exact (div_le_self (by positivity) (Nat.one_le_cast.2 (Nat.factorial_pos _))).trans (h t ht)

private theorem i15FourWord_integrand_bound {b : Letter} {w : List Letter}
    {m : ℝ} (hm : 0 < m)
    (hw : ¬AllZero w → ∃ C, 0 ≤ C ∧ ∀ a : Letter → ℝ,
      a .zero = 0 → (∀ k ≠ Letter.zero, m ≤ a k) → ∀ t ∈ Ioc (0 : ℝ) 1,
        |i15FourWord a w t| ≤ C * t ^ (1 / 2 : ℝ))
    (hbw : ¬AllZero (b :: w)) :
    ∃ K, 0 ≤ K ∧ ∀ a : Letter → ℝ,
      a .zero = 0 → (∀ k ≠ Letter.zero, m ≤ a k) → ∀ t ∈ Ioc (0 : ℝ) 1,
        |(t + a b)⁻¹ * i15FourWord a w t| ≤ K * t ^ (-(1 / 2) : ℝ) := by
  by_cases hb : b = .zero
  · subst b
    have hn : ¬AllZero w := fun h => hbw (allZero_cons.2 ⟨rfl, h⟩)
    obtain ⟨C, hC, h⟩ := hw hn
    refine ⟨C, hC, fun a h0 ha t ht => ?_⟩
    rw [h0, add_zero, abs_mul, abs_of_pos (inv_pos.2 ht.1)]
    calc t⁻¹ * |i15FourWord a w t| ≤ t⁻¹ * (C * t ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (h a h0 ha t ht) (inv_nonneg.2 ht.1.le)
      _ = C * t ^ (-(1 / 2) : ℝ) := by
        rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, rpow_sub_one ht.1.ne']
        field_simp
  · have hbound : ∃ C, 0 ≤ C ∧ ∀ a : Letter → ℝ,
        a .zero = 0 → (∀ k ≠ Letter.zero, m ≤ a k) → ∀ t ∈ Ioc (0 : ℝ) 1,
          |i15FourWord a w t| ≤ C * t ^ (-(1 / 2) : ℝ) := by
      by_cases hz : AllZero w
      · obtain ⟨C, hC, h⟩ := abs_log_pow_le w.length (δ := 1 / 2) (by norm_num)
        refine ⟨C, hC, fun a _ _ t ht => ?_⟩
        rw [i15FourWord_allZero hz, abs_div, abs_pow, Nat.abs_cast]
        exact (div_le_self (by positivity) (Nat.one_le_cast.2 (Nat.factorial_pos _))).trans (h t ht)
      · obtain ⟨C, hC, h⟩ := hw hz
        refine ⟨C, hC, fun a h0 ha t ht => (h a h0 ha t ht).trans
          (mul_le_mul_of_nonneg_left ?_ hC)⟩
        exact rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by norm_num)
    obtain ⟨C, hC, h⟩ := hbound
    refine ⟨m⁻¹ * C, by positivity, fun a h0 ha t ht => ?_⟩
    have ht0 := ht.1
    have hab := ha b hb
    rw [abs_mul, abs_of_pos (inv_pos.2 (by linarith : 0 < t + a b)), mul_assoc]
    exact mul_le_mul (inv_anti₀ hm (by linarith)) (h a h0 ha t ht) (abs_nonneg _) (by positivity)

private theorem i15FourWord_bound_uniform {m : ℝ} (hm : 0 < m) (w : List Letter)
    (hw : ¬AllZero w) :
    ∃ C, 0 ≤ C ∧ ∀ a : Letter → ℝ,
      a .zero = 0 → (∀ k ≠ Letter.zero, m ≤ a k) → ∀ t ∈ Ioc (0 : ℝ) 1,
        |i15FourWord a w t| ≤ C * t ^ (1 / 2 : ℝ) := by
  induction w with
  | nil => exact (hw allZero_nil).elim
  | cons b w ih =>
    obtain ⟨K, hK, hk⟩ := i15FourWord_integrand_bound hm ih hw
    refine ⟨2 * K, by positivity, fun a h0 ha t ht => ?_⟩
    rw [i15FourWord_cons_integral hw]
    have hI := abs_integral_le_of_le_rpow ht.1.le (by norm_num : (-1 : ℝ) < -(1 / 2))
      (K := K) fun s hs => hk a h0 ha s ⟨hs.1, hs.2.trans ht.2⟩
    convert hI using 1
    norm_num
    ring

include ha in
private theorem i15FourWord_pos_lower : ∃ m > 0, ∀ b ≠ Letter.zero, m ≤ a b := by
  refine ⟨min (a .one) (a .negOne), lt_min (ha .one (by decide)) (ha .negOne (by decide)), ?_⟩
  intro b hb
  cases b with
  | zero => exact (hb rfl).elim
  | one => exact min_le_left _ _
  | negOne => exact min_le_right _ _

include ha0 ha in
private theorem i15FourWord_integrand_continuous {b : Letter} {w : List Letter}
    (hw : ContinuousOn (i15FourWord a w) (Ioi 0)) :
    ContinuousOn (fun t => (t + a b)⁻¹ * i15FourWord a w t) (Ioi 0) :=
  ((continuousOn_id.add continuousOn_const).inv₀
    (fun _ ht => (i15FourWord_denom ha0 ha b ht).ne')).mul hw

private theorem i15FourWord_intervalIntegrable_of_bound {f : ℝ → ℝ} {K u : ℝ}
    (hu : 0 ≤ u) (hc : ContinuousOn f (Ioi 0))
    (hK : ∀ t ∈ Ioc (0 : ℝ) 1, |f t| ≤ K * t ^ (-(1 / 2) : ℝ)) :
    IntervalIntegrable f volume 0 u := by
  have h : ∀ v ∈ Icc (0 : ℝ) 1, IntervalIntegrable f volume 0 v := by
    intro v hv
    have hh : IntervalIntegrable (fun t => K * t ^ (-(1 / 2) : ℝ)) volume 0 v :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hv.1] at hh ⊢
    have hcont : ContinuousOn f (Ioc 0 v) := hc.mono fun _ ht => ht.1
    refine hh.mono' (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
    apply (ae_restrict_iff' measurableSet_Ioc).2
    exact ae_of_all _ fun t ht => by rw [Real.norm_eq_abs]; exact hK t ⟨ht.1, ht.2.trans hv.2⟩
  by_cases hu1 : u ≤ 1
  · exact h u ⟨hu, hu1⟩
  · refine (h 1 ⟨zero_le_one, le_rfl⟩).trans (hc.mono ?_).intervalIntegrable
    rw [uIcc_of_le (le_of_not_ge hu1)]
    exact fun _ ht => zero_lt_one.trans_le ht.1

include ha0 ha in
private theorem i15FourWord_deriv_of_good {b : Letter} {w : List Letter}
    (hw : ContinuousOn (i15FourWord a w) (Ioi 0)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (i15FourWord a (b :: w)) ((u + a b)⁻¹ * i15FourWord a w u) u := by
  by_cases h : AllZero (b :: w)
  · obtain ⟨rfl, hz⟩ := allZero_cons.1 h
    rw [show i15FourWord a (.zero :: w) = fun x =>
          log x ^ (w.length + 1) / ((w.length + 1).factorial : ℝ) from
        funext (i15FourWord_allZero h), ha0, add_zero, i15FourWord_allZero hz]
    exact hasDerivAt_log_pow_div hu
  · obtain ⟨m, hm, hma⟩ := i15FourWord_pos_lower ha
    obtain ⟨K, -, hK⟩ := i15FourWord_integrand_bound hm
      (i15FourWord_bound_uniform hm w) h
    have hc := i15FourWord_integrand_continuous (b := b) ha0 ha hw
    rw [i15FourWord_cons_integral h]
    exact intervalIntegral.integral_hasDerivAt_right
      (i15FourWord_intervalIntegrable_of_bound hu.le hc (hK a ha0 hma))
      (hc.stronglyMeasurableAtFilter isOpen_Ioi u hu) (hc.continuousAt (Ioi_mem_nhds hu))

include ha0 ha in
private theorem continuousOn_i15FourWord (w : List Letter) :
    ContinuousOn (i15FourWord a w) (Ioi 0) := by
  induction w with
  | nil => exact continuousOn_const
  | cons b w ih =>
    exact fun u hu => (i15FourWord_deriv_of_good ha0 ha ih hu).continuousAt.continuousWithinAt

include ha0 ha in
private theorem i15FourWord_bound {w : List Letter} (hw : ¬AllZero w) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1,
      |i15FourWord a w t| ≤ C * t ^ (1 / 2 : ℝ) := by
  obtain ⟨m, hm, hma⟩ := i15FourWord_pos_lower ha
  obtain ⟨C, hC, hb⟩ := i15FourWord_bound_uniform hm w hw
  exact ⟨C, hC, hb a ha0 hma⟩

include ha0 ha in
/-- Differentiate a word by removing its first letter and multiplying by its kernel. -/
theorem hasDerivAt_i15FourWord_cons (b : Letter) (w : List Letter) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (i15FourWord a (b :: w)) ((u + a b)⁻¹ * i15FourWord a w u) u :=
  i15FourWord_deriv_of_good ha0 ha (continuousOn_i15FourWord ha0 ha w) hu

include ha0 ha in
private theorem tendsto_i15FourWord_zero {w : List Letter} (hw : ¬AllZero w) :
    Tendsto (i15FourWord a w) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := i15FourWord_bound ha0 ha hw
  exact tendsto_zero_of_abs_le_rpow (C := C) (by norm_num : (0 : ℝ) < 1 / 2) zero_lt_one hC

include ha0 ha in
/-- The derivative of the integration-by-parts primitive is the original word. -/
theorem hasDerivAt_i15FourWordPrim (w : List Letter) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (i15FourWordPrim a w) (i15FourWord a w u) u := by
  induction w with
  | nil => exact hasDerivAt_id u
  | cons b w ih =>
    have h := (((hasDerivAt_id' u).add_const (a b)).mul
      (hasDerivAt_i15FourWord_cons ha0 ha b w hu)).sub ih
    refine h.congr_deriv ?_
    rw [← mul_assoc, mul_inv_cancel₀ (i15FourWord_denom ha0 ha b hu).ne']
    ring

include ha0 ha in
/-- The primitive vanishes at the left endpoint, including for pure zero words. -/
theorem tendsto_i15FourWordPrim_zero (w : List Letter) :
    Tendsto (i15FourWordPrim a w) (𝓝[>] 0) (𝓝 0) := by
  induction w with
  | nil => exact continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  | cons b w ih =>
    have hi : Tendsto (fun t : ℝ => t + a b) (𝓝[>] 0) (𝓝 (a b)) := by
      simpa using
        (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds :
          Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)).add_const (a b)
    by_cases hw : AllZero (b :: w)
    · have hb := (allZero_cons.1 hw).1
      subst b
      obtain ⟨C, -, hC⟩ := i15FourWord_log_bound (a := a) hw (δ := 1 / 2) (by norm_num)
      have hP : Tendsto (fun t => (t + a .zero) * i15FourWord a (.zero :: w) t)
          (𝓝[>] 0) (𝓝 0) := by
        refine tendsto_zero_of_abs_le_rpow (C := C) (by norm_num : (0 : ℝ) < 1 / 2)
          zero_lt_one (fun t ht => ?_)
        rw [ha0, add_zero, abs_mul, abs_of_pos ht.1]
        calc t * |i15FourWord a (.zero :: w) t| ≤ t * (C * t ^ (-(1 / 2) : ℝ)) :=
              mul_le_mul_of_nonneg_left (hC t ht) ht.1.le
          _ = C * t ^ (1 / 2 : ℝ) := by
            rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, rpow_sub_one ht.1.ne']
            field_simp [ht.1.ne']
      simpa only [i15FourWordPrim, sub_zero] using hP.sub ih
    · simpa only [i15FourWordPrim, mul_zero, sub_zero] using
        (hi.mul (tendsto_i15FourWord_zero ha0 ha hw)).sub ih

include ha0 ha in
private theorem hasDerivAt_sum_i15FourWord (b : Letter) (L : List (List Letter))
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t => ((L.map (b :: ·)).map fun w => i15FourWord a w t).sum)
      ((u + a b)⁻¹ * (L.map fun w => i15FourWord a w u).sum) u := by
  induction L with
  | nil => simpa using hasDerivAt_const u (0 : ℝ)
  | cons w L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hasDerivAt_i15FourWord_cons ha0 ha b w hu).add ih).congr_deriv (by ring)

include ha0 ha in
private theorem tendsto_i15FourWord_mul_zero {v w : List Letter}
    (h : ¬ (AllZero v ∧ AllZero w)) :
    Tendsto (fun t => i15FourWord a v t * i15FourWord a w t) (𝓝[>] 0) (𝓝 0) := by
  have aux (p q : List Letter) (hp : ¬AllZero p) :
      Tendsto (fun t => i15FourWord a p t * i15FourWord a q t) (𝓝[>] 0) (𝓝 0) := by
    by_cases hq : AllZero q
    · obtain ⟨C, hC, hc⟩ := i15FourWord_bound ha0 ha hp
      obtain ⟨D, hD, hd⟩ := i15FourWord_log_bound (a := a) hq (δ := 1 / 4) (by norm_num)
      refine tendsto_zero_of_abs_le_rpow (C := C * D) (by norm_num : (0 : ℝ) < 1 / 4)
        zero_lt_one fun t ht => ?_
      rw [abs_mul]
      calc |i15FourWord a p t| * |i15FourWord a q t|
          ≤ (C * t ^ (1 / 2 : ℝ)) * (D * t ^ (-(1 / 4) : ℝ)) :=
            mul_le_mul (hc t ht) (hd t ht) (abs_nonneg _)
              (mul_nonneg hC (rpow_nonneg ht.1.le _))
        _ = C * D * t ^ (1 / 4 : ℝ) := by
          rw [show C * t ^ (1 / 2 : ℝ) * (D * t ^ (-(1 / 4) : ℝ)) =
            C * D * (t ^ (1 / 2 : ℝ) * t ^ (-(1 / 4) : ℝ)) by ring,
            ← rpow_add ht.1]
          norm_num
    · simpa only [zero_mul] using
        (tendsto_i15FourWord_zero ha0 ha hp).mul (tendsto_i15FourWord_zero ha0 ha hq)
  by_cases hv : AllZero v
  · simpa only [mul_comm] using aux w v (fun hw => h ⟨hv, hw⟩)
  · exact aux v w hv

include ha0 ha in
private theorem i15FourWord_mul (v w : List Letter) (u : ℝ) (hu : 0 < u) :
    i15FourWord a v u * i15FourWord a w u =
      ((shuffle v w).map fun s => i15FourWord a s u).sum := by
  match v, w with
  | [], w => simp [i15FourWord]
  | b :: v, [] => simp [i15FourWord]
  | b :: v, c :: w =>
    let S : ℝ → ℝ := fun t => ((shuffle (b :: v) (c :: w)).map fun s => i15FourWord a s t).sum
    let F : ℝ → ℝ := fun t => i15FourWord a (b :: v) t * i15FourWord a (c :: w) t - S t
    have hS : S = fun t => (((shuffle v (c :: w)).map (b :: ·)).map
          fun s => i15FourWord a s t).sum +
        (((shuffle (b :: v) w).map (c :: ·)).map fun s => i15FourWord a s t).sum := by
      funext t
      simp only [S, shuffle_cons_cons, List.map_append, List.sum_append]
    have hd : ∀ t > 0, HasDerivAt F 0 t := by
      intro t ht
      have h1 := (hasDerivAt_i15FourWord_cons ha0 ha b v ht).mul
        (hasDerivAt_i15FourWord_cons ha0 ha c w ht)
      have h2 := (hasDerivAt_sum_i15FourWord ha0 ha b (shuffle v (c :: w)) ht).add
        (hasDerivAt_sum_i15FourWord ha0 ha c (shuffle (b :: v) w) ht)
      unfold F
      rw [hS]
      refine (h1.sub h2).congr_deriv ?_
      rw [← i15FourWord_mul v (c :: w) t ht, ← i15FourWord_mul (b :: v) w t ht]
      ring
    have hmem (s : List Letter) (hs : s ∈ shuffle (b :: v) (c :: w)) :
        AllZero s ↔ AllZero (b :: v) ∧ AllZero (c :: w) := allZero_of_mem_shuffle_iff hs
    change _ = S u
    apply sub_eq_zero.mp
    change F u = 0
    by_cases hz : AllZero (b :: v) ∧ AllZero (c :: w)
    · have allzero_at_one (s : List Letter) (hs : AllZero s) (hne : s ≠ []) :
          i15FourWord a s 1 = 0 := by
        rw [i15FourWord_allZero hs, log_one, zero_pow (List.length_pos_iff.2 hne).ne', zero_div]
      have hS1 : S 1 = 0 := by
        change ((shuffle (b :: v) (c :: w)).map fun s => i15FourWord a s 1).sum = 0
        refine List.sum_eq_zero fun t ht => ?_
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
        refine allzero_at_one s ((hmem s hs).2 hz) ?_
        intro h
        have := length_of_mem_shuffle hs
        simp [h] at this
      have hF1 : F 1 = 0 := by
        simp only [F, allzero_at_one _ hz.1 (List.cons_ne_nil _ _),
          allzero_at_one _ hz.2 (List.cons_ne_nil _ _), hS1, zero_mul, sub_zero]
      rw [← hF1]
      exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun _ ht => (hd _ ht).differentiableAt.differentiableWithinAt)
        (fun _ ht => by simpa using (hd _ ht).deriv)
        hu zero_lt_one
    · have hL : Tendsto F (𝓝[>] 0) (𝓝 0) := by
        have h1 := tendsto_i15FourWord_mul_zero ha0 ha hz
        have h2 : Tendsto S (𝓝[>] 0) (𝓝 0) := by
          have hsum := tendsto_list_sum (l := shuffle (b :: v) (c :: w))
            (f := fun w t => i15FourWord a w t) (a := fun _ => (0 : ℝ)) (x := 𝓝[>] 0)
            fun s hs => tendsto_i15FourWord_zero ha0 ha (fun h => hz ((hmem s hs).1 h))
          simpa [S] using hsum
        simpa only [F, sub_zero] using h1.sub h2
      exact eq_of_hasDerivAt_zero_of_tendsto_right (b := u + 1) (by linarith)
        (fun t ht => hd t ht.1) hL u ⟨hu, by linarith⟩
termination_by v.length + w.length

end PositiveOffsets

/-- Evaluate a linear combination of words, or evaluate their primitives. -/
noncomputable def i15FourEval (F : List Letter → ℝ → ℝ)
    (L : List (ℝ × List Letter)) (u : ℝ) : ℝ :=
  (L.map fun cw => cw.1 * F cw.2 u).sum

/-- Multiply two linear combinations of words by shuffling each pair of words. -/
noncomputable def i15FourProduct (L M : List (ℝ × List Letter)) :
    List (ℝ × List Letter) :=
  L.flatMap fun (a, v) => M.flatMap fun (b, w) => (shuffle v w).map fun s => (a * b, s)

/-- The shuffle power of a linear combination of words. -/
noncomputable def i15FourPower (L : List (ℝ × List Letter)) :
    ℕ → List (ℝ × List Letter)
  | 0 => [(1, [])]
  | n + 1 => i15FourProduct L (i15FourPower L n)

private theorem i15FourEval_cons (F : List Letter → ℝ → ℝ)
    (c : ℝ) (w : List Letter) (L : List (ℝ × List Letter)) (u : ℝ) :
    i15FourEval F ((c, w) :: L) u = c * F w u + i15FourEval F L u := rfl

private theorem i15FourEval_nil (F : List Letter → ℝ → ℝ) (u : ℝ) :
    i15FourEval F [] u = 0 := rfl

private theorem i15FourEval_append (F : List Letter → ℝ → ℝ)
    (L M : List (ℝ × List Letter)) (u : ℝ) :
    i15FourEval F (L ++ M) u = i15FourEval F L u + i15FourEval F M u := by
  simp only [i15FourEval, List.map_append, List.sum_append]

private theorem i15FourEval_shuffle {a : Letter → ℝ} (ha0 : a .zero = 0)
    (ha : ∀ b ≠ Letter.zero, 0 < a b) {u : ℝ} (hu : 0 < u)
    (c d : ℝ) (v w : List Letter) :
    i15FourEval (i15FourWord a) ((shuffle v w).map fun s => (c * d, s)) u =
      (c * i15FourWord a v u) * (d * i15FourWord a w u) := by
  rw [show (c * i15FourWord a v u) * (d * i15FourWord a w u) =
      (c * d) * (i15FourWord a v u * i15FourWord a w u) by ring, i15FourWord_mul ha0 ha v w u hu]
  generalize shuffle v w = L
  induction L with
  | nil => simp [i15FourEval]
  | cons s L ih =>
    simp only [List.map_cons, i15FourEval_cons, List.sum_cons, mul_add, ih]

private theorem i15FourEval_product {a : Letter → ℝ} (ha0 : a .zero = 0)
    (ha : ∀ b ≠ Letter.zero, 0 < a b) {u : ℝ} (hu : 0 < u)
    (L M : List (ℝ × List Letter)) :
    i15FourEval (i15FourWord a) (i15FourProduct L M) u =
      i15FourEval (i15FourWord a) L u * i15FourEval (i15FourWord a) M u := by
  have h (c : ℝ) (v : List Letter) : ∀ N : List (ℝ × List Letter),
      i15FourEval (i15FourWord a)
        (N.flatMap fun (d, w) => (shuffle v w).map fun s => (c * d, s)) u =
      c * i15FourWord a v u * i15FourEval (i15FourWord a) N u := by
    intro N
    induction N with
    | nil => simp [i15FourEval]
    | cons hd N ih =>
      obtain ⟨d, w⟩ := hd
      simp only [List.flatMap_cons, i15FourEval_cons, i15FourEval_append, ih,
        i15FourEval_shuffle ha0 ha hu, mul_add]
  induction L with
  | nil => simp [i15FourProduct, i15FourEval]
  | cons hd L ih =>
    obtain ⟨c, v⟩ := hd
    rw [show i15FourProduct ((c, v) :: L) M =
        (M.flatMap fun (d, w) => (shuffle v w).map fun s => (c * d, s)) ++
          i15FourProduct L M from rfl]
    rw [i15FourEval_append, h, ih, i15FourEval_cons, add_mul]

private theorem i15FourEval_power {a : Letter → ℝ} (ha0 : a .zero = 0)
    (ha : ∀ b ≠ Letter.zero, 0 < a b) {u : ℝ} (hu : 0 < u)
    (L : List (ℝ × List Letter)) (n : ℕ) :
    i15FourEval (i15FourWord a) (i15FourPower L n) u = i15FourEval (i15FourWord a) L u ^ n := by
  induction n with
  | zero => simp [i15FourPower, i15FourEval, i15FourWord]
  | succ n ih => rw [i15FourPower, i15FourEval_product ha0 ha hu, ih, pow_succ']

private theorem hasDerivAt_i15FourEval_prim {a : Letter → ℝ} (ha0 : a .zero = 0)
    (ha : ∀ b ≠ Letter.zero, 0 < a b) {u : ℝ} (hu : 0 < u)
    (L : List (ℝ × List Letter)) :
    HasDerivAt (i15FourEval (i15FourWordPrim a) L) (i15FourEval (i15FourWord a) L u) u := by
  induction L with
  | nil => exact hasDerivAt_const u (0 : ℝ)
  | cons hd L ih =>
    obtain ⟨c, w⟩ := hd
    exact ((hasDerivAt_i15FourWordPrim ha0 ha w hu).const_mul c).add ih

private theorem tendsto_i15FourEval_prim_zero {a : Letter → ℝ} (ha0 : a .zero = 0)
    (ha : ∀ b ≠ Letter.zero, 0 < a b) (L : List (ℝ × List Letter)) :
    Tendsto (i15FourEval (i15FourWordPrim a) L) (𝓝[>] 0) (𝓝 0) := by
  induction L with
  | nil => exact tendsto_const_nhds
  | cons hd L ih =>
    obtain ⟨c, w⟩ := hd
    have h := ((tendsto_i15FourWordPrim_zero ha0 ha w).const_mul c).add ih
    change Tendsto (fun t => c * i15FourWordPrim a w t +
      i15FourEval (i15FourWordPrim a) L t) (𝓝[>] 0) (𝓝 0)
    simpa only [mul_zero, add_zero] using h

/-! ### The two fourth powers -/

open QED.Polylog

/-- Offsets of `log u`, `log (1+u/r)`, and `log (1+ru)` in the ratio coordinate. -/
noncomputable def i15WuOffsets (r : ℝ) : Letter → ℝ
  | .zero => 0
  | .one => r
  | .negOne => r⁻¹

private theorem i15WuOffsets_pos {r : ℝ} (hr : 0 < r) :
    ∀ b ≠ Letter.zero, 0 < i15WuOffsets r b := by
  intro b hb
  cases b with
  | zero => exact (hb rfl).elim
  | one => exact hr
  | negOne => exact inv_pos.2 hr

/-- The linear combination for the first logarithm in the ratio coordinate. -/
noncomputable def i15WuLeft (r : ℝ) : List (ℝ × List Letter) :=
  [(-log r + 2 * log (1 + r), []), (1, [.zero]), (-2, [.one]), (-2, [.negOne])]

/-- The linear combination for the negative of the second logarithm. -/
noncomputable def i15WuRight (r : ℝ) : List (ℝ × List Letter) :=
  [(-log r + 2 * log (1 + r), []), (1, [.zero])]

/-- The integrand `b₁⁴ - b₂⁴` in the ratio coordinate `r = x/(1-x)`. -/
noncomputable def i15WuF4 (r u : ℝ) : ℝ :=
  (-log r + log u + 2 * log (1 + r) - 2 * i15WuA r u - 2 * i15WuB r u) ^ 4 -
    (log r - 2 * log (1 + r) - log u) ^ 4

/-- The integration-by-parts primitive of the fourth-power difference. -/
noncomputable def i15WuPhi4 (r u : ℝ) : ℝ :=
  i15FourEval (i15FourWordPrim (i15WuOffsets r)) (i15FourPower (i15WuLeft r) 4) u -
    i15FourEval (i15FourWordPrim (i15WuOffsets r)) (i15FourPower (i15WuRight r) 4) u

private theorem i15FourWord_single {a : Letter → ℝ} {b : Letter} (hb : b ≠ .zero)
    (ha : 0 < a b) {u : ℝ} (hu : 0 < u) :
    i15FourWord a [b] u = log (1 + u / a b) := by
  rw [i15FourWord_cons_integral (by simpa using hb)]
  simp only [i15FourWord, mul_one]
  rw [intervalIntegral.integral_comp_add_right (fun t : ℝ => t⁻¹)]
  rw [zero_add, integral_inv_of_pos ha (add_pos hu ha)]
  congr 1
  field_simp
  ring

/-- The ratio-coordinate primitive differentiates to the fourth-power difference. -/
theorem hasDerivAt_i15WuPhi4 {r u : ℝ} (hr : 0 < r) (hu : 0 < u) :
    HasDerivAt (i15WuPhi4 r) (i15WuF4 r u) u := by
  have ha0 : i15WuOffsets r .zero = 0 := rfl
  have ha := i15WuOffsets_pos hr
  have h := (hasDerivAt_i15FourEval_prim ha0 ha hu (i15FourPower (i15WuLeft r) 4)).sub
    (hasDerivAt_i15FourEval_prim ha0 ha hu (i15FourPower (i15WuRight r) 4))
  refine h.congr_deriv ?_
  rw [i15FourEval_power ha0 ha hu, i15FourEval_power ha0 ha hu]
  have h0 : i15FourWord (i15WuOffsets r) [.zero] u = log u := by
    rw [i15FourWord_allZero (by simp)]
    norm_num
  have h1 : i15FourWord (i15WuOffsets r) [.one] u = i15WuA r u :=
    i15FourWord_single (by decide) hr hu
  have h2 : i15FourWord (i15WuOffsets r) [.negOne] u = i15WuB r u := by
    rw [i15FourWord_single (by decide) (inv_pos.2 hr) hu]
    simp only [i15WuOffsets, i15WuB, div_inv_eq_mul]
    rw [mul_comm u r]
  simp only [i15WuF4, i15WuLeft, i15WuRight, i15FourEval_cons,
    show i15FourWord (i15WuOffsets r) [] u = 1 from rfl, mul_one,
    show ∀ F : List Letter → ℝ → ℝ, i15FourEval F [] u = 0 from fun _ => rfl,
    h0, h1, h2]
  ring

/-- The lower endpoint of the ratio-coordinate primitive is zero. -/
theorem tendsto_i15WuPhi4_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (i15WuPhi4 r) (𝓝[>] 0) (𝓝 0) := by
  have ha0 : i15WuOffsets r .zero = 0 := rfl
  have ha := i15WuOffsets_pos hr
  change Tendsto (fun u =>
    i15FourEval (i15FourWordPrim (i15WuOffsets r)) (i15FourPower (i15WuLeft r) 4) u -
    i15FourEval (i15FourWordPrim (i15WuOffsets r)) (i15FourPower (i15WuRight r) 4) u)
    (𝓝[>] 0) (𝓝 0)
  simpa only [sub_zero] using
    (tendsto_i15FourEval_prim_zero ha0 ha (i15FourPower (i15WuLeft r) 4)).sub
      (tendsto_i15FourEval_prim_zero ha0 ha (i15FourPower (i15WuRight r) 4))

/-- Relate the original slice to the fourth-power difference in the ratio coordinate. -/
theorem i15A1k_four_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15A1k 4 (x, u) = i15WuF4 (x / (1 - x)) u / (24 * (x * (1 - x))) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have hx1' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, by linarith⟩
  have hm : 0 < 1 - x := by linarith
  set r := x / (1 - x) with hr
  have hpr : 1 + r = 1 / (1 - x) := by rw [hr]; field_simp; ring
  have lp : log (1 + r) = -log (1 - x) := by rw [hpr, one_div, log_inv]
  have lr : log r = log x - log (1 - x) := log_div hx0.ne' hm.ne'
  have hA : 0 < u + (1 - u) * x := by nlinarith
  have hB : 0 < 1 - (1 - u) * x := by nlinarith
  have la : i15WuA r u = log (u + (1 - u) * x) - log x := by
    unfold i15WuA
    rw [← log_div hA.ne' hx0.ne']
    congr 1
    rw [hr]; field_simp; ring
  have lb : i15WuB r u = log (1 - (1 - u) * x) - log (1 - x) := by
    unfold i15WuB
    rw [← log_div hB.ne' hm.ne']
    congr 1
    rw [hr]; field_simp; ring
  have e1 : i15B1 x u = -log r + log u + 2 * log (1 + r) - 2 * i15WuA r u - 2 * i15WuB r u := by
    rw [i15B1_eq hx1' ⟨hu0, hu1⟩, la, lb, lp, lr]; ring
  have e2 : i15B2 x u = log r - 2 * log (1 + r) - log u := by
    rw [i15B2_eq hx1', lp, lr]; ring
  unfold i15A1k i15WuF4
  simp only [e1, e2, Nat.factorial]
  norm_num

/-- The ratio-coordinate fourth-power difference is nonnegative on the slice. -/
theorem i15WuF4_nonneg {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 ≤ i15WuF4 r u := by
  let x := r / (1 + r)
  have hr0 := hr.1
  have hx0 : 0 < x := by unfold x; positivity
  have hp : 0 < 1 + r := by positivity
  have hx : x ∈ Ioo (0 : ℝ) (1 / 2) := ⟨hx0, (div_lt_iff₀ hp).2 (by linarith [hr.2])⟩
  have hratio : x / (1 - x) = r := by
    have he : 1 - x = 1 / (1 + r) := by unfold x; field_simp; ring
    rw [he]
    unfold x
    field_simp
  have h := i15A1k_four_nonneg (z := (x, u)) ⟨⟨hx0, by linarith [hx.2]⟩, hu⟩
  rw [i15A1k_four_eq hx hu, hratio] at h
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  exact le_of_not_gt fun hn => (not_lt_of_ge h) (div_neg_of_neg_of_pos hn (by positivity))

/-- Evaluate the ratio-coordinate integral at the upper endpoint of its primitive. -/
theorem integral_i15WuF4 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (i15WuF4 r) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, i15WuF4 r u = i15WuPhi4 r 1 := by
  simpa only [sub_zero] using i15Q_ftc_nonneg zero_lt_one
    (fun _ hu => hasDerivAt_i15WuPhi4 hr.1 hu.1) (fun _ hu => i15WuF4_nonneg hr hu)
    (tendsto_i15WuPhi4_zero hr.1)
    ((hasDerivAt_i15WuPhi4 hr.1 one_pos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- The weight-four A₁ slice is integrable, with value given by the word primitive. -/
theorem integrableOn_and_integral_i15A1k_four_primitive {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    IntegrableOn (fun u => i15A1k 4 (x, u)) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i15A1k 4 (x, u) =
        i15WuPhi4 (x / (1 - x)) 1 / (24 * (x * (1 - x))) := by
  obtain ⟨hI, hv⟩ := integral_i15WuF4 (i15Q_ratio_mem hx)
  have hcongr (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) := i15A1k_four_eq hx hu
  have hIo := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hI
  refine ⟨IntegrableOn.congr_fun (hIo.div_const _) (fun u hu => (hcongr u hu).symm)
    measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_div,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hv]

/-! ### The coincident offsets at `r = 1` -/

/-- The two positive offsets both tend to the same HPL letter as the ratio tends to one. -/
def i15WuCollapse : Letter → Letter
  | .zero => .zero
  | .one => .negOne
  | .negOne => .negOne

private theorem i15WuCollapse_allZero (w : List Letter) :
    AllZero (w.map i15WuCollapse) ↔ AllZero w := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [i15WuCollapse, ih]

/-- At the coalescence point the ratio-coordinate words are ordinary HPLs. -/
theorem i15FourWord_i15WuOffsets_one (w : List Letter) :
    i15FourWord (i15WuOffsets 1) w = hpl (w.map i15WuCollapse) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    by_cases hz : AllZero (b :: w)
    · funext t
      rw [i15FourWord_allZero hz, hpl_of_allZero ((i15WuCollapse_allZero _).2 hz),
        List.length_map]
    · rw [i15FourWord_cons_integral hz, ih]
      change _ = hpl (i15WuCollapse b :: w.map i15WuCollapse)
      rw [hpl_cons_of_not_allZero (fun h => hz ((i15WuCollapse_allZero _).1 h))]
      cases b <;> simp [i15WuOffsets, i15WuCollapse, add_comm]

/-! ### Differentiation in the ratio -/

/-- Derivatives of the three offsets with respect to the ratio. -/
noncomputable def i15WuOffsetsD (r : ℝ) : Letter → ℝ
  | .zero => 0
  | .one => 1
  | .negOne => -(r⁻¹) ^ 2

private theorem hasDerivAt_i15WuOffsets (b : Letter) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun q => i15WuOffsets q b) (i15WuOffsetsD r b) r := by
  cases b with
  | zero => exact hasDerivAt_const r 0
  | one => exact hasDerivAt_id r
  | negOne =>
    refine ((hasDerivAt_id' r).inv hr.ne').congr_deriv ?_
    simp [i15WuOffsetsD, inv_pow, div_eq_mul_inv]

/-- The differentiated integrand in the word recursion, evaluated on the tail and its rate. -/
noncomputable def i15WuRateStep (r : ℝ) (b : Letter) (t v d : ℝ) : ℝ :=
  -(i15WuOffsetsD r b) * ((t + i15WuOffsets r b)⁻¹) ^ 2 * v +
    (t + i15WuOffsets r b)⁻¹ * d

/-- The recursive integral of the ratio derivative, with rate zero for pure zero words. -/
noncomputable def i15WuWordRate (r : ℝ) : List Letter → ℝ → ℝ
  | [], _ => 0
  | b :: w, u =>
    if AllZero (b :: w) then 0
    else ∫ t in (0 : ℝ)..u,
      i15WuRateStep r b t (i15FourWord (i15WuOffsets r) w t) (i15WuWordRate r w t)

private theorem i15WuWordRate_zero {r u : ℝ} {w : List Letter} (h : AllZero w) :
    i15WuWordRate r w u = 0 := by
  cases w with
  | nil => rfl
  | cons b w => simp [i15WuWordRate, h]

private theorem i15WuRateStep_bound {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (b : Letter) (w : List Letter) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ r ∈ Icc p q, ∀ t ∈ Ioc (0 : ℝ) 1, |i15WuWordRate r w t| ≤ C * t ^ (1 / 2 : ℝ)) :
    ∃ K, 0 ≤ K ∧ ∀ r ∈ Icc p q, ∀ t ∈ Ioc (0 : ℝ) 1,
      |i15WuRateStep r b t (i15FourWord (i15WuOffsets r) w t) (i15WuWordRate r w t)| ≤
        K * t ^ (-(1 / 2) : ℝ) := by
  by_cases hzero : b = .zero
  · subst b
    refine ⟨C, hC, fun r hr t ht => ?_⟩
    simp only [i15WuRateStep, i15WuOffsets, i15WuOffsetsD, neg_zero, zero_mul, zero_add, add_zero]
    rw [abs_mul, abs_of_pos (inv_pos.2 ht.1)]
    calc t⁻¹ * |i15WuWordRate r w t| ≤ t⁻¹ * (C * t ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hD r hr t ht) (inv_nonneg.2 ht.1.le)
      _ = C * t ^ (-(1 / 2) : ℝ) := by
        rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, rpow_sub_one ht.1.ne']
        field_simp
  · let m := min p q⁻¹
    have hq := hp.trans_le hpq
    have hm : 0 < m := lt_min hp (inv_pos.2 hq)
    have hmlower (r : ℝ) (hr : r ∈ Icc p q) :
        ∀ k ≠ Letter.zero, m ≤ i15WuOffsets r k := by
      intro k hk
      cases k with
      | zero => exact (hk rfl).elim
      | one => exact (min_le_left _ _).trans hr.1
      | negOne => exact (min_le_right _ _).trans (inv_anti₀ (hp.trans_le hr.1) hr.2)
    have hW : ∃ D, 0 ≤ D ∧ ∀ r ∈ Icc p q, ∀ t ∈ Ioc (0 : ℝ) 1,
        |i15FourWord (i15WuOffsets r) w t| ≤ D * t ^ (-(1 / 2) : ℝ) := by
      by_cases hw : AllZero w
      · obtain ⟨D, hD, hb⟩ := i15FourWord_log_bound (a := i15WuOffsets p) hw
          (δ := 1 / 2) (by norm_num)
        refine ⟨D, hD, fun r _ t ht => ?_⟩
        simpa only [i15FourWord_allZero hw] using hb t ht
      · obtain ⟨D, hD, hb⟩ := i15FourWord_bound_uniform hm w hw
        refine ⟨D, hD, fun r hr t ht => (hb _ rfl (hmlower r hr) t ht).trans
          (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by norm_num)) hD)⟩
    obtain ⟨D, hD0, hW⟩ := hW
    let M := 1 + (p⁻¹) ^ 2
    have hM : 0 ≤ M := by unfold M; positivity
    refine ⟨M * (m⁻¹) ^ 2 * D + m⁻¹ * C, by positivity, fun r hr t ht => ?_⟩
    have t0 := ht.1
    have r0 := hp.trans_le hr.1

    have hb := hmlower r hr b hzero
    have hk : |(t + i15WuOffsets r b)⁻¹| ≤ m⁻¹ := by
      rw [abs_of_pos (inv_pos.2 (by linarith))]
      exact inv_anti₀ hm (by linarith)
    have hd : |-(i15WuOffsetsD r b)| ≤ M := by
      cases b with
      | zero => exact (hzero rfl).elim
      | one =>
        simp only [i15WuOffsetsD, abs_neg, abs_one]
        exact le_add_of_nonneg_right (sq_nonneg _)
      | negOne =>
        simp only [i15WuOffsetsD, neg_neg, abs_of_nonneg (sq_nonneg (r⁻¹))]
        exact (pow_le_pow_left₀ (inv_nonneg.2 r0.le) (inv_anti₀ hp hr.1) 2).trans
          (le_add_of_nonneg_left zero_le_one)
    unfold i15WuRateStep
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_pow, abs_mul]
    have P := mul_le_mul (mul_le_mul hd (pow_le_pow_left₀ (abs_nonneg _) hk 2)
      (by positivity) hM) (hW r hr t ht) (abs_nonneg _) (by positivity)
    have Q := mul_le_mul hk (hD r hr t ht) (abs_nonneg _) (inv_nonneg.2 hm.le)
    have ht' : t ^ (1 / 2 : ℝ) ≤ t ^ (-(1 / 2) : ℝ) :=
      rpow_le_rpow_of_exponent_ge t0 ht.2 (by norm_num)
    have Q' := Q.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ht' hC) (inv_nonneg.2 hm.le))
    exact (add_le_add P Q').trans (le_of_eq (by ring))

private theorem i15WuWordRate_bound {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (w : List Letter) :
    ∃ C, 0 ≤ C ∧ ∀ r ∈ Icc p q, ∀ t ∈ Ioc (0 : ℝ) 1,
      |i15WuWordRate r w t| ≤ C * t ^ (1 / 2 : ℝ) := by
  induction w with
  | nil => exact ⟨0, le_rfl, fun _ _ _ _ => by simp [i15WuWordRate]⟩
  | cons b w ih =>
    by_cases hz : AllZero (b :: w)
    · exact ⟨0, le_rfl, fun _ _ _ _ => by simp [i15WuWordRate_zero hz]⟩
    · obtain ⟨C, hC, hD⟩ := ih
      obtain ⟨K, hK, hb⟩ := i15WuRateStep_bound hp hpq b w hC hD
      refine ⟨2 * K, by positivity, fun r hr t ht => ?_⟩
      simp only [i15WuWordRate, hz, ↓reduceIte]
      have hI := abs_integral_le_of_le_rpow ht.1.le (by norm_num : (-1 : ℝ) < -(1 / 2))
        (K := K) fun s hs => hb r hr s ⟨hs.1, hs.2.trans ht.2⟩
      convert hI using 1
      norm_num
      ring

private theorem continuousOn_i15WuRateStep {r : ℝ} (hr : 0 < r) (b : Letter) (w : List Letter)
    (hD : ContinuousOn (i15WuWordRate r w) (Ioc 0 1)) :
    ContinuousOn (fun t => i15WuRateStep r b t (i15FourWord (i15WuOffsets r) w t)
      (i15WuWordRate r w t)) (Ioc 0 1) := by
  have hN : ContinuousOn (fun t => (t + i15WuOffsets r b)⁻¹) (Ioc 0 1) :=
    (continuousOn_id.add continuousOn_const).inv₀
      fun _ ht => (i15FourWord_denom rfl (i15WuOffsets_pos hr) b ht.1).ne'
  have hW : ContinuousOn (i15FourWord (i15WuOffsets r) w) (Ioc 0 1) :=
    (continuousOn_i15FourWord rfl (i15WuOffsets_pos hr) w).mono fun _ ht => ht.1
  exact ((continuousOn_const.mul (hN.pow 2)).mul hW).add (hN.mul hD)

private theorem intervalIntegrable_i15WuRateStep {r : ℝ} (hr : 0 < r) (b : Letter) (w : List Letter)
    (hD : ContinuousOn (i15WuWordRate r w) (Ioc 0 1)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => i15WuRateStep r b t (i15FourWord (i15WuOffsets r) w t)
      (i15WuWordRate r w t)) volume 0 u := by
  obtain ⟨C, hC, hb⟩ := i15WuWordRate_bound hr le_rfl w
  obtain ⟨K, -, hK⟩ := i15WuRateStep_bound hr le_rfl b w hC hb
  have hI : IntervalIntegrable (fun t => K * t ^ (-(1 / 2) : ℝ)) volume 0 u :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu.1] at hI ⊢
  have hc := (continuousOn_i15WuRateStep hr b w hD).mono (Ioc_subset_Ioc_right hu.2)
  refine hI.mono' (hc.aestronglyMeasurable measurableSet_Ioc) ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => by
    rw [Real.norm_eq_abs]
    exact hK r ⟨le_rfl, le_rfl⟩ t ⟨ht.1, ht.2.trans hu.2⟩)

private theorem continuousOn_i15WuWordRate {r : ℝ} (hr : 0 < r) (w : List Letter) :
    ContinuousOn (i15WuWordRate r w) (Ioc 0 1) := by
  induction w with
  | nil => exact continuousOn_const
  | cons b w ih =>
    by_cases hz : AllZero (b :: w)
    · simp only [show i15WuWordRate r (b :: w) = fun _ => 0 from
        funext (fun _ => i15WuWordRate_zero hz)]
      exact continuousOn_const
    · have hI := intervalIntegrable_i15WuRateStep hr b w ih ⟨zero_le_one, le_rfl⟩
      have h := intervalIntegral.continuousOn_primitive_interval' hI left_mem_uIcc
      rw [uIcc_of_le zero_le_one] at h
      refine (h.mono Ioc_subset_Icc_self).congr fun u _ => ?_
      simp only [i15WuWordRate, hz, ↓reduceIte]

private theorem intervalIntegrable_i15FourWord_kernel {b : Letter} {w : List Letter}
    (hz : ¬AllZero (b :: w)) {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable (fun t => (t + i15WuOffsets r b)⁻¹ * i15FourWord (i15WuOffsets r) w t)
      volume 0 u := by
  obtain ⟨m, hm, hma⟩ := i15FourWord_pos_lower (i15WuOffsets_pos hr)
  obtain ⟨K, -, hK⟩ := i15FourWord_integrand_bound hm (i15FourWord_bound_uniform hm w) hz
  exact i15FourWord_intervalIntegrable_of_bound hu
    (i15FourWord_integrand_continuous rfl (i15WuOffsets_pos hr)
      (continuousOn_i15FourWord rfl (i15WuOffsets_pos hr) w)) (hK _ rfl hma)

/-- Differentiate the moving-offset word by differentiating its recursive integral. -/
theorem hasDerivAt_i15WuWord (w : List Letter) {r u : ℝ}
    (hr : 0 < r) (hu : u ∈ Ioc (0 : ℝ) 1) :
    HasDerivAt (fun q => i15FourWord (i15WuOffsets q) w u) (i15WuWordRate r w u) r := by
  induction w generalizing r u with
  | nil => exact hasDerivAt_const r (1 : ℝ)
  | cons b w ih =>
    by_cases hz : AllZero (b :: w)
    · simp only [i15FourWord_allZero hz, i15WuWordRate_zero hz]
      exact hasDerivAt_const _ _
    · have hp : 0 < r / 2 := by positivity
      have hpq : r / 2 ≤ r + 1 := by linarith
      have hlocal : Ioo (r / 2) (r + 1) ∈ 𝓝 r :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
      obtain ⟨C, hC, hb⟩ := i15WuWordRate_bound hp hpq w
      obtain ⟨K, -, hK⟩ := i15WuRateStep_bound hp hpq b w hC hb
      have hset : Ι (0 : ℝ) u ⊆ Ioc 0 1 := by
        rw [uIoc_of_le hu.1.le]
        exact Ioc_subset_Ioc_right hu.2
      have hm : ∀ᶠ q in 𝓝 r, AEStronglyMeasurable
          (fun t => (t + i15WuOffsets q b)⁻¹ * i15FourWord (i15WuOffsets q) w t)
          (volume.restrict (Ι 0 u)) := by
        filter_upwards [hlocal] with q hq
        have hq0 := hp.trans hq.1
        have hc := i15FourWord_integrand_continuous (b := b) rfl (i15WuOffsets_pos hq0)
          (continuousOn_i15FourWord rfl (i15WuOffsets_pos hq0) w)
        exact (hc.mono (hset.trans fun _ ht => ht.1)).aestronglyMeasurable measurableSet_uIoc
      have hm' := ((continuousOn_i15WuRateStep hr b w (continuousOn_i15WuWordRate hr w)).mono
        hset).aestronglyMeasurable (μ := volume) measurableSet_uIoc
      rw [show (fun q => i15FourWord (i15WuOffsets q) (b :: w) u) = fun q =>
        ∫ t in (0 : ℝ)..u, (t + i15WuOffsets q b)⁻¹ * i15FourWord (i15WuOffsets q) w t from
          funext (fun q => congrFun (i15FourWord_cons_integral (a := i15WuOffsets q) hz) u)]
      simp only [i15WuWordRate, hz, ↓reduceIte]
      refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F' := fun q t => i15WuRateStep q b t (i15FourWord (i15WuOffsets q) w t)
          (i15WuWordRate q w t))
        (bound := fun t => K * t ^ (-(1 / 2) : ℝ)) hlocal hm
        (intervalIntegrable_i15FourWord_kernel hz hr hu.1.le) hm' ?_
        ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K) ?_).2
      · exact ae_of_all _ fun t ht q hq => by
          rw [Real.norm_eq_abs]
          exact hK q ⟨hq.1.le, hq.2.le⟩ t (hset ht)
      · refine ae_of_all _ fun t ht q hq => ?_
        have hq0 := hp.trans hq.1
        have ht' := hset ht
        have hden := i15FourWord_denom rfl (i15WuOffsets_pos hq0) b ht'.1
        have hd := (((hasDerivAt_i15WuOffsets b hq0).const_add t).inv hden.ne').mul (ih hq0 ht')
        convert hd using 1
        simp only [i15WuRateStep, div_eq_mul_inv, inv_pow, Pi.inv_apply]

/-- The word is continuous in the ratio, including at the coalescence of the offsets. -/
theorem continuousAt_i15WuWord (w : List Letter) {r u : ℝ} (hr : 0 < r)
    (hu : u ∈ Ioc (0 : ℝ) 1) :
    ContinuousAt (fun q => i15FourWord (i15WuOffsets q) w u) r :=
  (hasDerivAt_i15WuWord w hr hu).continuousAt

/-- The left limit of an endpoint word at `r = 1` is its collapsed HPL value. -/
theorem tendsto_i15WuWord_one (w : List Letter) :
    Tendsto (fun q => i15FourWord (i15WuOffsets q) w 1) (𝓝[<] 1)
      (𝓝 (hpl (w.map i15WuCollapse) 1)) := by
  rw [← i15FourWord_i15WuOffsets_one]
  exact (continuousAt_i15WuWord w one_pos ⟨one_pos, le_rfl⟩).tendsto.mono_left nhdsWithin_le_nhds

/-! ### The boundary terms from varying the offsets -/

/-- Logarithmic derivative of the difference of two offsets. -/
noncomputable def i15WuContact (r : ℝ) (b c : Letter) : ℝ :=
  (i15WuOffsetsD r c - i15WuOffsetsD r b) / (i15WuOffsets r c - i15WuOffsets r b)

/-- The contact and lower boundary terms, written as linear combinations of shorter words. -/
noncomputable def i15WuBoundary (r : ℝ) : List Letter → List (ℝ × List Letter)
  | [] => []
  | [b] => [(-(i15WuOffsetsD r b / i15WuOffsets r b), [])]
  | b :: c :: w =>
    (i15WuBoundary r (c :: w)).map (fun (p, v) => (p, b :: v)) ++
      [(i15WuContact r b c, b :: w), (-i15WuContact r b c, c :: w)]

/-- The upper boundary term and the remaining terms of the moving-offset derivative. -/
noncomputable def i15WuTransport (r : ℝ) : List Letter → ℝ → ℝ
  | [], _ => 0
  | b :: w, t =>
    i15WuOffsetsD r b * (t + i15WuOffsets r b)⁻¹ * i15FourWord (i15WuOffsets r) w t +
      i15FourEval (i15FourWord (i15WuOffsets r)) (i15WuBoundary r (b :: w)) t

private theorem i15WuOffsets_ne {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    {b c : Letter} (hbc : b ≠ c) :
    i15WuOffsets r b ≠ i15WuOffsets r c := by
  have h0 := hr.1
  have h1 := hr.2
  have hi := inv_pos.2 h0
  have h : r < r⁻¹ := calc
    r = r / 1 := (div_one r).symm
    _ < 1 / r := (div_lt_div_iff₀ one_pos h0).2 (by nlinarith [mul_lt_mul_of_pos_left h1 h0])
    _ = r⁻¹ := one_div r
  cases b <;> cases c <;> simp_all [i15WuOffsets] <;> linarith

private theorem i15WuContact_kernel {r t : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (ht : 0 < t)
    (b c : Letter) :
    let k (a : Letter) := (t + i15WuOffsets r a)⁻¹
    i15WuOffsetsD r b * k b * k c + i15WuContact r b c * (k b - k c) =
      k b * (i15WuOffsetsD r c * k c) := by
  dsimp only
  by_cases hbc : b = c
  · subst c
    simp only [sub_self, mul_zero, add_zero]
    ring
  · have hb := (i15FourWord_denom rfl (i15WuOffsets_pos hr.1) b ht).ne'
    have hc := (i15FourWord_denom rfl (i15WuOffsets_pos hr.1) c ht).ne'
    have hdiff := sub_ne_zero.mpr (i15WuOffsets_ne hr (Ne.symm hbc))
    unfold i15WuContact
    field_simp
    ring

private theorem hasDerivAt_i15WuPrefixed {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (b : Letter) (L : List (ℝ × List Letter)) :
    HasDerivAt (i15FourEval (i15FourWord (i15WuOffsets r))
      (L.map fun (c, w) => (c, b :: w)))
      ((t + i15WuOffsets r b)⁻¹ * i15FourEval (i15FourWord (i15WuOffsets r)) L t) t := by
  induction L with
  | nil =>
    change HasDerivAt (fun _ => (0 : ℝ)) (_ * 0) t
    rw [mul_zero]
    exact hasDerivAt_const t 0
  | cons p L ih =>
    obtain ⟨c, w⟩ := p
    have h := ((hasDerivAt_i15FourWord_cons rfl (i15WuOffsets_pos hr) b w ht).const_mul c).add ih
    refine h.congr_deriv ?_
    simp only [i15FourEval_cons]
    ring

private theorem hasDerivAt_i15WuUpper {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (b : Letter) :
    HasDerivAt (fun s => i15WuOffsetsD r b * (s + i15WuOffsets r b)⁻¹)
      (-(i15WuOffsetsD r b) * ((t + i15WuOffsets r b)⁻¹) ^ 2) t := by
  have hden := (i15FourWord_denom rfl (i15WuOffsets_pos hr) b ht).ne'
  have h := (((hasDerivAt_id' t).add_const (i15WuOffsets r b)).inv hden).const_mul
    (i15WuOffsetsD r b)
  refine h.congr_deriv ?_
  simp only [div_eq_mul_inv, inv_pow]
  ring

private theorem hasDerivAt_i15WuTransport_cons {r t : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) (b : Letter) (w : List Letter) :
    HasDerivAt (i15WuTransport r (b :: w))
      (i15WuRateStep r b t (i15FourWord (i15WuOffsets r) w t) (i15WuTransport r w t)) t := by
  cases w with
  | nil =>
    have h := (hasDerivAt_i15WuUpper hr.1 ht b).add
      (hasDerivAt_const t (-(i15WuOffsetsD r b / i15WuOffsets r b)))
    have hfun : i15WuTransport r [b] = fun s =>
        i15WuOffsetsD r b * (s + i15WuOffsets r b)⁻¹ - i15WuOffsetsD r b / i15WuOffsets r b := by
      funext s
      simp [i15WuTransport, i15WuBoundary, i15FourEval_cons, i15FourEval_nil, i15FourWord,
        sub_eq_add_neg]
    rw [hfun]
    convert h using 1
    simp [i15WuRateStep, i15WuTransport, i15FourWord]
  | cons c w =>
    let V := i15FourWord (i15WuOffsets r)
    have hc := hasDerivAt_i15FourWord_cons rfl (i15WuOffsets_pos hr.1) c w ht
    have hb := hasDerivAt_i15FourWord_cons rfl (i15WuOffsets_pos hr.1) b w ht
    have h := (((hasDerivAt_i15WuUpper hr.1 ht b).mul hc).add
      (hasDerivAt_i15WuPrefixed hr.1 ht b (i15WuBoundary r (c :: w)))).add
      ((hb.const_mul (i15WuContact r b c)).add (hc.const_mul (-i15WuContact r b c)))
    have hval : i15WuTransport r (b :: c :: w) = fun s =>
        (i15WuOffsetsD r b * (s + i15WuOffsets r b)⁻¹ * V (c :: w) s +
          i15FourEval V ((i15WuBoundary r (c :: w)).map fun (p, v) => (p, b :: v)) s) +
            (i15WuContact r b c * V (b :: w) s + (-i15WuContact r b c) * V (c :: w) s) := by
      funext s
      simp only [V, i15WuTransport, i15WuBoundary, i15FourEval_append, i15FourEval_cons,
        i15FourEval_nil, add_zero]
      ring
    rw [hval]
    refine h.congr_deriv ?_
    simp only [i15WuRateStep, i15WuTransport]
    have he := i15WuContact_kernel hr ht b c
    dsimp only at he
    linear_combination i15FourWord (i15WuOffsets r) w t * he

private theorem i15WuContact_zero_left (r : ℝ) (b : Letter) :
    i15WuContact r .zero b = i15WuOffsetsD r b / i15WuOffsets r b := by
  simp [i15WuContact, i15WuOffsets, i15WuOffsetsD]

private theorem i15WuContact_zero_right (r : ℝ) (b : Letter) :
    i15WuContact r b .zero = i15WuOffsetsD r b / i15WuOffsets r b := by
  simp [i15WuContact, i15WuOffsets, i15WuOffsetsD]

private def i15WuZeros (f : ℕ → ℝ) (w : List Letter) (_ : ℝ) : ℝ :=
  if AllZero w then f w.length else 0

private theorem i15WuBoundary_zeros (r : ℝ) (w : List Letter) (b : Letter)
    (f : ℕ → ℝ) (t : ℝ) :
    i15FourEval (i15WuZeros f) (i15WuBoundary r (b :: w)) t =
      if AllZero w then -(i15WuOffsetsD r b / i15WuOffsets r b) * f w.length else 0 := by
  induction w generalizing f b with
  | nil => simp [i15WuBoundary, i15FourEval_cons, i15FourEval_nil, i15WuZeros]
  | cons c w ih =>
    have hprefix : i15FourEval (i15WuZeros f)
        ((i15WuBoundary r (c :: w)).map fun (p, v) => (p, b :: v)) t =
        if b = .zero then
          i15FourEval (i15WuZeros fun k => f (k + 1)) (i15WuBoundary r (c :: w)) t else 0 := by
      by_cases hb : b = .zero
      · subst b
        simp [i15FourEval, i15WuZeros, Function.comp_def]
      · simp [i15FourEval, i15WuZeros, Function.comp_def, hb]
    simp only [i15WuBoundary, i15FourEval_append, i15FourEval_cons, i15FourEval_nil,
      hprefix, ih, i15WuZeros]
    by_cases hb : b = .zero
    · subst b
      simp only [i15WuOffsets, i15WuOffsetsD, zero_div, neg_zero, zero_mul, add_zero,
        ↓reduceIte, allZero_cons, true_and, List.length_cons, i15WuContact_zero_left]
      by_cases hc : c = .zero
      · subst c
        simp
      · by_cases h : AllZero w <;> simp [h, hc]
    · by_cases hc : c = .zero
      · subst c
        simp [hb, i15WuContact_zero_right, mul_ite]
      · simp [hb, hc]

private noncomputable def i15WuNonzero (r : ℝ) (w : List Letter) (t : ℝ) : ℝ :=
  if AllZero w then 0 else i15FourWord (i15WuOffsets r) w t

private theorem i15WuEval_split (r t : ℝ) (L : List (ℝ × List Letter)) :
    i15FourEval (i15FourWord (i15WuOffsets r)) L t =
      i15FourEval (i15WuZeros fun n => log t ^ n / (n.factorial : ℝ)) L t +
        i15FourEval (i15WuNonzero r) L t := by
  induction L with
  | nil => simp only [i15FourEval_nil, add_zero]
  | cons h L ih =>
    obtain ⟨c, w⟩ := h
    simp only [i15FourEval_cons, ih, i15WuZeros, i15WuNonzero]
    by_cases hw : AllZero w
    · simp only [hw, ↓reduceIte, i15FourWord_allZero hw, mul_zero, zero_add]
      ring
    · simp only [hw, ↓reduceIte, mul_zero, zero_add]
      ring

private theorem tendsto_i15WuNonzero_eval_zero {r : ℝ} (hr : 0 < r)
    (L : List (ℝ × List Letter)) :
    Tendsto (i15FourEval (i15WuNonzero r) L) (𝓝[>] 0) (𝓝 0) := by
  induction L with
  | nil => exact tendsto_const_nhds
  | cons h L ih =>
    obtain ⟨c, w⟩ := h
    have hw : Tendsto (i15WuNonzero r w) (𝓝[>] 0) (𝓝 0) := by
      by_cases h : AllZero w
      · exact tendsto_const_nhds.congr' (Eventually.of_forall fun _ => by simp [i15WuNonzero, h])
      · exact (tendsto_i15FourWord_zero rfl (i15WuOffsets_pos hr) h).congr'
          (Eventually.of_forall fun _ => by simp [i15WuNonzero, h])
    change Tendsto (fun t => c * i15WuNonzero r w t + i15FourEval (i15WuNonzero r) L t)
      (𝓝[>] 0) (𝓝 0)
    simpa only [mul_zero, add_zero] using (hw.const_mul c).add ih

private theorem tendsto_mul_i15WuWord_allZero_zero {r : ℝ} (hr : 0 < r)
    (w : List Letter) (hw : AllZero w) :
    Tendsto (fun t => t * i15FourWord (i15WuOffsets r) w t) (𝓝[>] 0) (𝓝 0) := by
  rcases w with _ | ⟨b, w⟩
  · simp only [i15FourWord, mul_one]
    exact (hasDerivAt_id' (0 : ℝ)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨rfl, _⟩ := allZero_cons.1 hw
  have h := (tendsto_i15FourWordPrim_zero rfl (i15WuOffsets_pos hr) (.zero :: w)).add
    (tendsto_i15FourWordPrim_zero rfl (i15WuOffsets_pos hr) w)
  exact (by simpa only [add_zero] using h : Tendsto _ _ (𝓝 (0 : ℝ))).congr'
    (Eventually.of_forall fun _ => by simp [i15FourWordPrim, i15WuOffsets])

private theorem tendsto_i15WuTransport_zero {r : ℝ} (hr : 0 < r) (w : List Letter) :
    Tendsto (i15WuTransport r w) (𝓝[>] 0) (𝓝 0) := by
  cases w with
  | nil => exact tendsto_const_nhds
  | cons b w =>
    let a := i15WuOffsets r b
    let d := i15WuOffsetsD r b
    have e (t : ℝ) : i15WuTransport r (b :: w) t =
        (if AllZero w then (d * (t + a)⁻¹ - d / a) else d * (t + a)⁻¹) *
          i15FourWord (i15WuOffsets r) w t +
        i15FourEval (i15WuNonzero r) (i15WuBoundary r (b :: w)) t := by
      simp only [i15WuTransport, i15WuEval_split, i15WuBoundary_zeros, a, d]
      by_cases hz : AllZero w
      · simp only [hz, ↓reduceIte, i15FourWord_allZero hz]; ring
      · simp [hz]
    have hup : Tendsto (fun t => (if AllZero w then (d * (t + a)⁻¹ - d / a)
        else d * (t + a)⁻¹) * i15FourWord (i15WuOffsets r) w t) (𝓝[>] 0) (𝓝 0) := by
      by_cases hb : b = .zero
      · subst b
        simpa only [a, d, i15WuOffsets, i15WuOffsetsD, zero_mul, zero_div, sub_zero, ite_self] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
      · have ha : 0 < a := i15WuOffsets_pos hr b hb
        by_cases hz : AllZero w
        · simp only [hz, ↓reduceIte]
          have hc : ContinuousAt (fun t => -d / (a * (t + a))) 0 :=
            continuousAt_const.div (continuousAt_const.mul (continuousAt_id.add continuousAt_const))
              (by simpa using (mul_pos ha ha).ne')
          have h := (hc.tendsto.mono_left nhdsWithin_le_nhds).mul
            (tendsto_mul_i15WuWord_allZero_zero hr w hz)
          refine (by simpa only [mul_zero] using h : Tendsto _ _ (𝓝 (0 : ℝ))).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
          field_simp [ha.ne', (add_pos ht ha).ne']
          ring
        · simp only [hz, ↓reduceIte]
          have hc : ContinuousAt (fun t => d * (t + a)⁻¹) 0 :=
            continuousAt_const.mul ((continuousAt_id.add continuousAt_const).inv₀ (by simpa using
              ha.ne'))
          simpa only [mul_zero] using (hc.tendsto.mono_left nhdsWithin_le_nhds).mul
            (tendsto_i15FourWord_zero rfl (i15WuOffsets_pos hr) hz)
    have h := hup.add (tendsto_i15WuNonzero_eval_zero hr (i15WuBoundary r (b :: w)))
    rw [funext e]
    simpa only [add_zero] using h

/-- Integration by parts reduces the derivative to the upper, lower and contact terms. -/
theorem i15WuWordRate_eq_transport {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioc (0 : ℝ) 1) (w : List Letter) :
    i15WuWordRate r w u = i15WuTransport r w u := by
  induction w generalizing u with
  | nil => rfl
  | cons b w ih =>
    have hd (t : ℝ) (ht : t ∈ Ioo 0 u) :
        HasDerivAt (i15WuTransport r (b :: w))
          (i15WuRateStep r b t (i15FourWord (i15WuOffsets r) w t) (i15WuWordRate r w t)) t := by
      rw [ih ⟨ht.1, ht.2.le.trans hu.2⟩]
      exact hasDerivAt_i15WuTransport_cons hr ht.1 b w
    have hInt := intervalIntegrable_i15WuRateStep hr.1 b w (continuousOn_i15WuWordRate hr.1 w)
      ⟨hu.1.le, hu.2⟩
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hu.1 hd hInt
      (tendsto_i15WuTransport_zero hr.1 (b :: w))
      ((hasDerivAt_i15WuTransport_cons hr hu.1 b w).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
    by_cases hzero : AllZero (b :: w)
    · obtain ⟨rfl, hw⟩ := allZero_cons.1 hzero
      simp [i15WuRateStep, i15WuOffsetsD, i15WuWordRate_zero hw] at h
      rw [i15WuWordRate_zero hzero, ← h]
    · simpa only [i15WuWordRate, hzero, ↓reduceIte, sub_zero] using h

/-- The ratio derivative of an endpoint word is a linear combination of shortened words. -/
theorem hasDerivAt_i15WuWord_transport {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioc (0 : ℝ) 1) (w : List Letter) :
    HasDerivAt (fun q => i15FourWord (i15WuOffsets q) w u) (i15WuTransport r w u) r := by
  rw [← i15WuWordRate_eq_transport hr hu w]
  exact hasDerivAt_i15WuWord w hr.1 hu

/-! ### The endpoint derivative uses the harmonic alphabet -/

/-- The upper boundary coefficients at `u = 1`, in the kernels of the ratio. -/
theorem i15WuUpper_at_one {r : ℝ} (hr : 0 < r) (b : Letter) :
    i15WuOffsetsD r b * (1 + i15WuOffsets r b)⁻¹ =
      match b with
      | .zero => 0
      | .one => Letter.negOne.kernel r
      | .negOne => -Letter.zero.kernel r + Letter.negOne.kernel r := by
  have hp : 1 + r ≠ 0 := by positivity
  have hi : 0 < r⁻¹ := inv_pos.2 hr
  have hp' : 1 + r⁻¹ ≠ 0 := by positivity
  cases b <;> simp only [i15WuOffsetsD, i15WuOffsets, Letter.kernel_zero, Letter.kernel_negOne]
  · ring
  · ring
  · field_simp [hr.ne', hp, hp']
    ring

/-- The lower boundary coefficients in the kernels of the ratio. -/
theorem i15WuLower_kernel {r : ℝ} (hr : 0 < r) (b : Letter) :
    -(i15WuOffsetsD r b / i15WuOffsets r b) =
      match b with
      | .zero => 0
      | .one => -Letter.zero.kernel r
      | .negOne => Letter.zero.kernel r := by
  cases b <;> simp [i15WuOffsetsD, i15WuOffsets, hr.ne', pow_two, div_eq_mul_inv]

/-- The contact coefficients in the harmonic alphabet of the ratio. -/
theorem i15WuContact_kernel_at_one {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (b c : Letter) :
    i15WuContact r b c =
      match b, c with
      | .zero, .one | .one, .zero => Letter.zero.kernel r
      | .zero, .negOne | .negOne, .zero => -Letter.zero.kernel r
      | .one, .negOne | .negOne, .one =>
        -Letter.zero.kernel r - Letter.one.kernel r + Letter.negOne.kernel r
      | _, _ => 0 := by
  have hr0 := hr.1.ne'
  have hp : 1 + r ≠ 0 := by have := hr.1; positivity
  have hm : 1 - r ≠ 0 := (sub_pos.2 hr.2).ne'
  have hsq : r ^ 2 ≠ 1 := by
    have := mul_lt_mul_of_pos_left hr.2 hr.1
    nlinarith [hr.2]
  cases b <;> cases c <;>
    simp [i15WuContact, i15WuOffsetsD, i15WuOffsets, hr0, pow_two, div_eq_mul_inv]
  all_goals (field_simp [hr0, hp, hm, hsq]; ring)

/-- Matching the ratio endpoint with `W₄` gives the required A₁ inner slice. -/
theorem integrableOn_and_integral_i15A1k_four_of_endpoint
    (hW : ∀ r ∈ Ioo (0 : ℝ) 1, i15WuPhi4 r 1 = i15W4 r)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    IntegrableOn (fun u => i15A1k 4 (x, u)) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i15A1k 4 (x, u) = i15W4G x := by
  obtain ⟨hI, hv⟩ := integrableOn_and_integral_i15A1k_four_primitive hx
  exact ⟨hI, by rw [hv, hW _ (i15Q_ratio_mem hx), i15W4G]⟩

end QED.ThreeLoopD
