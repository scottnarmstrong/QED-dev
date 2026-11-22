/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWLogSq
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Set (a), stage D: two dispersive tools for the `VB` nodes

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route.

* An indicator difference `[p < t] - [q < t]` on `t > c` integrates like the oriented
  interval `p..q` (`ksWB_integral_ind_sub`).
* **The derivative criterion** (`ksWB_sub_eq_of_deriv`): if
  `F'(σ) = ∫_p^q m(t)/(t + σ)² dt` between `0` and `s`, then
  `F(s) - F(0) = ∫_p^q m(t) s/(t(s + t)) dt`. This is Fubini on the rectangle, with
  `∫_0^s (t + σ)⁻² dσ = s/(t(s + t))`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology
open scoped Interval

namespace QED.ChainProof.SetAKS

theorem ksWB_mul_ind_sub_eq (f : ℝ → ℝ) (p q t : ℝ) :
    f t * ((if p < t then (1 : ℝ) else 0) - (if q < t then 1 else 0)) =
      (Ioc p q).indicator f t - (Ioc q p).indicator f t := by
  by_cases h1 : p < t <;> by_cases h2 : q < t
  · simp [h1, h2, indicator, not_le.2 h1, not_le.2 h2]
  · simp [h1, h2, indicator, not_le.2 h1, le_of_not_gt h2]
  · simp [h1, h2, indicator, le_of_not_gt h1, not_le.2 h2]
  · simp [h1, h2, indicator]

theorem ksWB_mul_ind_eq (f : ℝ → ℝ) (x t : ℝ) :
    f t * (if x < t then (1 : ℝ) else 0) = (Ioi x).indicator f t := by
  by_cases h : x < t <;> simp [h, indicator]

/-- **An indicator difference integrates over an oriented interval.** -/
theorem ksWB_integral_ind_sub {f : ℝ → ℝ} {c p q : ℝ} (hp : c ≤ p) (hq : c ≤ q)
    (hf : IntervalIntegrable f volume p q) :
    ∫ t in Ioi c, f t * ((if p < t then 1 else 0) - (if q < t then 1 else 0)) =
      ∫ t in p..q, f t := by
  simp_rw [ksWB_mul_ind_sub_eq f p q]
  have i1 : Integrable ((Ioc p q).indicator f) (volume.restrict (Ioi c)) :=
    (hf.1.integrable_indicator measurableSet_Ioc).restrict
  have i2 : Integrable ((Ioc q p).indicator f) (volume.restrict (Ioi c)) :=
    (hf.2.integrable_indicator measurableSet_Ioc).restrict
  rw [integral_sub i1 i2, setIntegral_indicator measurableSet_Ioc,
    setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 (show Ioc p q ⊆ Ioi c from fun t ht => lt_of_le_of_lt hp ht.1),
    inter_eq_right.2 (show Ioc q p ⊆ Ioi c from fun t ht => lt_of_le_of_lt hq ht.1)]
  rfl

theorem ksWB_integrableOn_ind_sub {f : ℝ → ℝ} {c p q : ℝ}
    (hf : IntervalIntegrable f volume p q) :
    IntegrableOn (fun t => f t * ((if p < t then 1 else 0) - (if q < t then 1 else 0)))
      (Ioi c) := by
  simp_rw [ksWB_mul_ind_sub_eq f p q]
  exact ((hf.1.integrable_indicator measurableSet_Ioc).sub
    (hf.2.integrable_indicator measurableSet_Ioc)).integrableOn

theorem ksWB_integral_ind {f : ℝ → ℝ} {c x : ℝ} (hx : c ≤ x) :
    ∫ t in Ioi c, f t * (if x < t then 1 else 0) = ∫ t in Ioi x, f t := by
  simp_rw [ksWB_mul_ind_eq f x]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.2 hx]

theorem ksWB_integrableOn_ind {f : ℝ → ℝ} {c x : ℝ} (hf : IntegrableOn f (Ioi x)) :
    IntegrableOn (fun t => f t * (if x < t then 1 else 0)) (Ioi c) := by
  simp_rw [ksWB_mul_ind_eq f x]
  exact (hf.integrable_indicator measurableSet_Ioi).integrableOn

/-- The `σ`-integral of the Cauchy kernel: `∫_0^s (t + σ)⁻² dσ = s/(t(s + t))`. -/
theorem ksWB_integral_inv_sq {t s : ℝ} (ht : 0 < t) (hst : 0 < s + t) :
    ∫ σ in (0 : ℝ)..s, ((t + σ) ^ 2)⁻¹ = s / (t * (s + t)) := by
  have hpos : ∀ σ ∈ uIcc 0 s, 0 < t + σ := fun σ hσ => by
    rcases le_total 0 s with h | h
    · rw [uIcc_of_le h] at hσ; linarith [hσ.1]
    · rw [uIcc_of_ge h] at hσ; linarith [hσ.1]
  have hd : ∀ σ ∈ uIcc 0 s, HasDerivAt (fun σ => -(t + σ)⁻¹) ((t + σ) ^ 2)⁻¹ σ :=
    fun σ hσ => by
      have h := (((hasDerivAt_id σ).const_add t).inv (hpos σ hσ).ne').neg
      refine h.congr_deriv ?_
      have := (pow_pos (hpos σ hσ) 2).ne'
      simp only [id]
      field_simp
  have hc : ContinuousOn (fun σ => ((t + σ) ^ 2)⁻¹) (uIcc 0 s) :=
    ContinuousOn.inv₀ (by fun_prop) fun σ hσ => (pow_pos (hpos σ hσ) 2).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  have : s + t ≠ 0 := hst.ne'
  have : t + s ≠ 0 := by linarith
  field_simp
  ring

/-- **The derivative criterion for a once-subtracted dispersion over an interval.** -/
theorem ksWB_sub_eq_of_deriv {p q s : ℝ} {m F : ℝ → ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsp : -p < s) (hsq : -q < s) (hm : IntervalIntegrable m volume p q)
    (hF : ∀ σ ∈ uIcc 0 s, HasDerivAt F (∫ t in p..q, m t / (t + σ) ^ 2) σ) :
    F s - F 0 = ∫ t in p..q, m t * (s / (t * (s + t))) := by
  set δ := min p q + min 0 s with hδ
  have hδ0 : 0 < δ := by
    rcases le_total p q with h | h <;> rcases le_total 0 s with h' | h' <;>
      simp only [hδ, min_eq_left, min_eq_right, h, h'] <;> linarith
  have hbd : ∀ σ ∈ Ι (0 : ℝ) s, ∀ t ∈ Ι p q, δ ≤ t + σ := fun σ hσ t ht => by
    have h1 : min 0 s < σ := hσ.1
    have h2 : min p q < t := ht.1
    linarith
  set κ : ℝ → ℝ → ℝ := fun σ t => m t / (t + σ) ^ 2 with hκ
  have hm' : Integrable m (volume.restrict (Ι p q)) := hm.def'
  have : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hmeas : AEStronglyMeasurable (Function.uncurry κ)
      ((volume.restrict (Ι (0 : ℝ) s)).prod (volume.restrict (Ι p q))) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => m z.2)
        ((volume.restrict (Ι (0 : ℝ) s)).prod (volume.restrict (Ι p q))) := (hm'.comp_snd _).1
    have h2 : AEStronglyMeasurable (fun z : ℝ × ℝ => ((z.2 + z.1) ^ 2)⁻¹)
        ((volume.restrict (Ι (0 : ℝ) s)).prod (volume.restrict (Ι p q))) :=
      (by fun_prop : Measurable fun z : ℝ × ℝ => ((z.2 + z.1) ^ 2)⁻¹).aestronglyMeasurable
    exact (h1.mul h2).congr (Eventually.of_forall fun z => by simp [κ, div_eq_mul_inv]; rfl)
  have hint : Integrable (Function.uncurry κ)
      ((volume.restrict (Ι (0 : ℝ) s)).prod (volume.restrict (Ι p q))) := by
    have hc : Integrable (fun _ : ℝ => (δ ^ 2)⁻¹) (volume.restrict (Ι (0 : ℝ) s)) :=
      (intervalIntegrable_const (a := 0) (b := s)).def'
    refine Integrable.mono' (Integrable.mul_prod hc hm'.norm) hmeas ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_uIoc)] with z hz
    have hz' := hbd z.1 hz.1 z.2 hz.2
    have hz0 : 0 < z.2 + z.1 := by linarith
    simp only [Function.uncurry, κ, norm_div, norm_pow, Real.norm_eq_abs, abs_of_pos hz0]
    rw [div_eq_mul_inv, mul_comm]
    gcongr
  have hsgn : ∀ (f : ℝ → ℝ) (a b : ℝ),
      ∫ x in a..b, f x = (if a ≤ b then 1 else -1) * ∫ x in Ι a b, f x := fun f a b => by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul]
  have hFint : IntervalIntegrable (fun σ => ∫ t in p..q, κ σ t) volume 0 s := by
    rw [intervalIntegrable_iff]
    refine (hint.integral_prod_left.const_mul (if p ≤ q then 1 else -1)).congr
      (Eventually.of_forall fun σ => ?_)
    simp only [hsgn _ p q]
    rfl
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hF hFint]
  have hin : ∀ t ∈ Ι p q, ∫ σ in (0 : ℝ)..s, κ σ t = m t * (s / (t * (s + t))) := fun t ht => by
    have h2 : min p q < t := ht.1
    have ht0 : 0 < t := lt_of_le_of_lt (le_min hp.le hq.le) h2
    have hst : 0 < s + t := by
      rcases le_total p q with h | h
      · rw [min_eq_left h] at h2; linarith
      · rw [min_eq_right h] at h2; linarith
    simp only [κ, div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, ksWB_integral_inv_sq ht0 hst, div_eq_mul_inv]
  calc ∫ σ in (0 : ℝ)..s, ∫ t in p..q, κ σ t
      = (if (0 : ℝ) ≤ s then 1 else -1) * ∫ σ in Ι (0 : ℝ) s,
          (if p ≤ q then 1 else -1) * ∫ t in Ι p q, κ σ t := by
        rw [hsgn _ 0 s]
        simp only [hsgn _ p q]
    _ = (if (0 : ℝ) ≤ s then 1 else -1) * (if p ≤ q then 1 else -1) *
          ∫ t in Ι p q, ∫ σ in Ι (0 : ℝ) s, κ σ t := by
        rw [integral_const_mul, integral_integral_swap hint]
        ring
    _ = (if p ≤ q then 1 else -1) * ∫ t in Ι p q, ∫ σ in (0 : ℝ)..s, κ σ t := by
        simp only [hsgn _ 0 s]
        rw [integral_const_mul]
        ring
    _ = ∫ t in p..q, m t * (s / (t * (s + t))) := by
        rw [setIntegral_congr_fun measurableSet_uIoc hin, ← hsgn]

/-! ### The interval nodes

Parameters `q, r > 0`, `q ≠ r`, `l > 0`, and `p = (l r + q)/(1 + l)`, which lies strictly
between `q` and `r`. In the `VB` class `q = T_w`, `r = T_β`, `p = T_D`. -/

section Nodes

variable {q r l : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (hl : 0 < l)
include hq hr hqr hl

omit hq hr in
/-- The interval `[[p, q]]` stays on the side of `q` away from `r`, and above `min q r`. -/
theorem ksWB_mem_uIcc {t : ℝ} (ht : t ∈ uIcc ((l * r + q) / (1 + l)) q) :
    0 < (t - r) * (q - r) ∧ min q r ≤ t := by
  have hl1 : 0 < 1 + l := by linarith
  have e1 : (l * r + q) / (1 + l) - r = (q - r) / (1 + l) := by field_simp; ring
  have e2 : (l * r + q) / (1 + l) - q = l * (r - q) / (1 + l) := by field_simp; ring
  rcases lt_or_gt_of_ne hqr with h | h
  · have hp1 : (l * r + q) / (1 + l) < r := by
      have : (q - r) / (1 + l) < 0 := div_neg_of_neg_of_pos (by linarith) hl1
      linarith
    have hp2 : q < (l * r + q) / (1 + l) := by
      have : 0 < l * (r - q) / (1 + l) := div_pos (mul_pos hl (by linarith)) hl1
      linarith
    rw [uIcc_of_ge hp2.le] at ht
    refine ⟨mul_pos_of_neg_of_neg (by linarith [ht.2]) (by linarith), ?_⟩
    rw [min_eq_left h.le]
    exact ht.1
  · have hp1 : r < (l * r + q) / (1 + l) := by
      have : 0 < (q - r) / (1 + l) := div_pos (by linarith) hl1
      linarith
    have hp2 : (l * r + q) / (1 + l) < q := by
      have : l * (r - q) / (1 + l) < 0 := div_neg_of_neg_of_pos (by nlinarith) hl1
      linarith
    rw [uIcc_of_le hp2.le] at ht
    refine ⟨mul_pos (by linarith [ht.1]) (by linarith), ?_⟩
    rw [min_eq_right h.le]
    linarith [ht.1]

omit hq hr in
/-- The logarithm of `1 + z(σ)`, `z(σ) = l(r + σ)/(q + σ)`, from the endpoint values. -/
theorem ksWB_log_one_add {σ : ℝ} (hσq : -q < σ) (hσr : -r < σ) :
    log ((q - r) / ((l * r + q) / (1 + l) - r)) -
        log ((q + σ) / ((l * r + q) / (1 + l) + σ)) =
      log (1 + l * (r + σ) / (q + σ)) := by
  have hl1 : 0 < 1 + l := by linarith
  have hqσ : 0 < q + σ := by linarith
  have hrσ : 0 < r + σ := by linarith
  have hqr' : q - r ≠ 0 := sub_ne_zero.2 hqr
  have e1 : (q - r) / ((l * r + q) / (1 + l) - r) = 1 + l := by
    rw [show (l * r + q) / (1 + l) - r = (q - r) / (1 + l) by field_simp; ring]
    field_simp
  have hpσ : 0 < (l * r + q) / (1 + l) + σ := by
    rw [show (l * r + q) / (1 + l) + σ = (l * (r + σ) + (q + σ)) / (1 + l) by field_simp; ring]
    positivity
  rw [e1, ← log_div hl1.ne' (div_pos hqσ hpσ).ne']
  congr 1
  field_simp
  ring

omit hq hr in
/-- **The `log(1 + z)` node as an interval integral**:
`∫_p^q (1/(t - r) - 1/(t + σ)) dt = log(1 + l(r + σ)/(q + σ))`. -/
theorem ksWB_integral_phi {σ : ℝ} (hσq : -q < σ) (hσr : -r < σ) :
    ∫ t in (l * r + q) / (1 + l)..q, (1 / (t - r) - 1 / (t + σ)) =
      log (1 + l * (r + σ) / (q + σ)) := by
  set p := (l * r + q) / (1 + l) with hp
  have hmem := fun t (ht : t ∈ uIcc p q) => ksWB_mem_uIcc hqr hl ht
  have h1 : IntervalIntegrable (fun t => 1 / (t - r)) volume p q :=
    (continuousOn_const.div (by fun_prop) fun t ht => by
      have := (hmem t ht).1
      intro h; rw [h, zero_mul] at this; exact lt_irrefl _ this).intervalIntegrable
  have hpos : ∀ t ∈ uIcc p q, 0 < t + σ := fun t ht => by
    have := (hmem t ht).2
    rcases le_total q r with h | h
    · rw [min_eq_left h] at this; linarith
    · rw [min_eq_right h] at this; linarith
  have h2 : IntervalIntegrable (fun t => 1 / (t + σ)) volume p q :=
    (continuousOn_const.div (by fun_prop) fun t ht => (hpos t ht).ne').intervalIntegrable
  rw [intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_comp_sub_right (fun x => 1 / x) r,
    intervalIntegral.integral_comp_add_right (fun x => 1 / x) σ,
    integral_one_div, integral_one_div, ksWB_log_one_add hqr hl hσq hσr]
  · have hp0 := hpos p left_mem_uIcc
    have hq0 := hpos q right_mem_uIcc
    exact notMem_uIcc_of_lt (by linarith) (by linarith)
  · have hp0 := (hmem p left_mem_uIcc).1
    rcases lt_or_gt_of_ne hqr with h | h
    · exact notMem_uIcc_of_gt (by nlinarith) (by linarith)
    · exact notMem_uIcc_of_lt (by nlinarith) (by linarith)

/-- On `[[p, q]]`: `t > 0`, `t + σ > 0` (`σ > -q, -r`) and `t ≠ r`. -/
theorem ksWB_uIcc_facts {σ t : ℝ} (hσq : -q < σ) (hσr : -r < σ)
    (ht : t ∈ uIcc ((l * r + q) / (1 + l)) q) : 0 < t ∧ 0 < t + σ ∧ t - r ≠ 0 := by
  obtain ⟨h1, h2⟩ := ksWB_mem_uIcc hqr hl ht
  refine ⟨?_, ?_, fun h => by rw [h, zero_mul] at h1; exact lt_irrefl _ h1⟩
  · rcases le_total q r with h | h
    · rw [min_eq_left h] at h2; linarith
    · rw [min_eq_right h] at h2; linarith
  · rcases le_total q r with h | h
    · rw [min_eq_left h] at h2; linarith
    · rw [min_eq_right h] at h2; linarith

/-- **The `G₀ log(1 + z)/A_β` node**: for an affine coefficient `g₀ + g₁σ` and
`H(σ) = (g₀ + g₁σ) r/(r + σ) log(1 + l(r + σ)/(q + σ))`,
`H(s) - H(0) = ∫_p^q (g₀ - g₁t) r/(r - t) s/(t(s + t)) dt`. -/
theorem ksWB_T1_node (g₀ g₁ : ℝ) {s : ℝ} (hsq : -q < s) (hsr : -r < s) :
    (g₀ + g₁ * s) * (r / (r + s)) * log (1 + l * (r + s) / (q + s)) -
        g₀ * log (1 + l * r / q) =
      ∫ t in (l * r + q) / (1 + l)..q,
        (g₀ - g₁ * t) * (r / (r - t)) * (s / (t * (s + t))) := by
  set p := (l * r + q) / (1 + l) with hp
  have hrs : r + s ≠ 0 := by linarith
  have e : EqOn (fun t => (g₀ - g₁ * t) * (r / (r - t)) * (s / (t * (s + t))))
      (fun t => (g₀ + g₁ * s) * (r / (r + s)) * (1 / (t - r) - 1 / (t + s)) -
        g₀ * (1 / (t - r) - 1 / (t + 0))) (uIcc p q) := fun t ht => by
    obtain ⟨h0, h1, h2⟩ := ksWB_uIcc_facts hq hr hqr hl hsq hsr ht
    have h3 : r - t ≠ 0 := fun h => h2 (by linarith)
    have h4 : s + t ≠ 0 := by linarith
    simp only [add_zero]
    field_simp
    ring
  have hi : ∀ σ, -q < σ → -r < σ →
      IntervalIntegrable (fun t => 1 / (t - r) - 1 / (t + σ)) volume p q := fun σ h1 h2 => by
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_const.div (by fun_prop) fun t ht => ?_).sub
      (continuousOn_const.div (by fun_prop) fun t ht => ?_)
    · exact (ksWB_uIcc_facts hq hr hqr hl h1 h2 ht).2.2
    · exact (ksWB_uIcc_facts hq hr hqr hl h1 h2 ht).2.1.ne'
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub
      ((hi s hsq hsr).const_mul _) ((hi 0 (by linarith) (by linarith)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ksWB_integral_phi hqr hl hsq hsr,
    ksWB_integral_phi hqr hl (by linarith) (by linarith)]
  simp

/-- The `t`-integral behind the derivative of the `K` node:
`∫_p^q (log(l(r - t)) - log(t - q))/(t + σ)² dt = K'(z(σ)) z'(σ)`. -/
theorem ksWB_integral_K_deriv {σ : ℝ} (hσq : -q < σ) (hσr : -r < σ) :
    ∫ t in (l * r + q) / (1 + l)..q, (log (l * (r - t)) - log (t - q)) / (t + σ) ^ 2 =
      ksUKer (l * (r + σ) / (q + σ)) * (l * (q - r) / (q + σ) ^ 2) := by
  set p := (l * r + q) / (1 + l) with hp
  have hqσ : 0 < q + σ := by linarith
  have hrσ : 0 < r + σ := by linarith
  set C := (r - q) / ((q + σ) * (r + σ)) with hC
  set G : ℝ → ℝ := fun t => (log (l * (r - t)) * (t - q) - (t - q) * log (t - q)) /
      ((q + σ) * (t + σ)) - C * (log (t - r) - log (t + σ)) with hG
  have hfacts := fun t (ht : t ∈ uIcc p q) => ksWB_uIcc_facts hq hr hqr hl hσq hσr ht
  have hlr : ∀ t ∈ uIcc p q, l * (r - t) ≠ 0 := fun t ht =>
    mul_ne_zero hl.ne' fun h => (hfacts t ht).2.2 (by linarith)
  have hcont : ContinuousOn G (uIcc p q) := by
    have hml : Continuous fun t : ℝ => (t - q) * log (t - q) :=
      continuous_mul_log.comp (continuous_id.sub continuous_const)
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    have h1 := (hfacts t ht).2.1
    have h2 := (hfacts t ht).2.2
    refine ContinuousAt.sub (ContinuousAt.div (ContinuousAt.sub (ContinuousAt.mul ?_
      (by fun_prop)) hml.continuousAt) (by fun_prop) (mul_pos hqσ h1).ne') ?_
    · exact (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).log (hlr t ht)
    · exact continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).log h2).sub
        ((continuousAt_id.add continuousAt_const).log h1.ne'))
  have hderiv : ∀ t ∈ Ioo (min p q) (max p q), HasDerivWithinAt G
      ((log (l * (r - t)) - log (t - q)) / (t + σ) ^ 2) (Ioi t) t := fun t ht => by
    have htI : t ∈ uIcc p q := Ioo_subset_Icc_self ht
    obtain ⟨h0, h1, h2⟩ := hfacts t htI
    have h3 := hlr t htI
    have htq : t - q ≠ 0 := by
      intro h
      rcases le_total p q with hpq | hpq
      · rw [max_eq_right hpq] at ht; linarith [ht.2]
      · rw [min_eq_right hpq] at ht; linarith [ht.1]
    have d1 := ((hasDerivAt_id t).const_sub r).const_mul l |>.log h3
    have d2 := (hasDerivAt_id t).sub_const q
    have d3 := ((hasDerivAt_id t).sub_const q).log htq
    have d4 := ((hasDerivAt_id t).sub_const r).log h2
    have d5 := ((hasDerivAt_id t).add_const σ).log h1.ne'
    have d6 := ((hasDerivAt_id t).add_const σ).const_mul (q + σ)
    have dG := (((d1.mul d2).sub (d2.mul d3)).div d6 (mul_pos hqσ h1).ne').sub
      ((d4.sub d5).const_mul C)
    refine HasDerivAt.hasDerivWithinAt ?_
    have h3' : r - t ≠ 0 := fun h => h2 (by linarith)
    convert dG using 1
    · funext x
      simp only [hG, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id]
    · simp only [id, hC, Pi.mul_apply, Pi.sub_apply]
      generalize log (l * (r - t)) = L1
      generalize log (t - q) = L2
      generalize log (t - r) = L3
      generalize log (t + σ) = L4
      have hl0 : l ≠ 0 := hl.ne'
      have e1 : q + σ ≠ 0 := hqσ.ne'
      have e2 : r + σ ≠ 0 := hrσ.ne'
      have e3 : t + σ ≠ 0 := h1.ne'
      field_simp
      ring
  have hint : IntervalIntegrable (fun t => (log (l * (r - t)) - log (t - q)) / (t + σ) ^ 2)
      volume p q := by
    have hl1 : IntervalIntegrable (fun t => log (l * (r - t))) volume p q :=
      (ContinuousOn.log (by fun_prop) hlr).intervalIntegrable
    have hl2 : IntervalIntegrable (fun t => log (t - q)) volume p q := by
      have := (intervalIntegral.intervalIntegrable_log' (a := p - q) (b := q - q)).comp_sub_right q
      simpa using this
    have hk : ContinuousOn (fun t => ((t + σ) ^ 2)⁻¹) (uIcc p q) :=
      ContinuousOn.inv₀ (by fun_prop) fun t ht => (pow_pos (hfacts t ht).2.1 2).ne'
    simpa only [div_eq_mul_inv] using (hl1.sub hl2).mul_continuousOn hk
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint]
  have hpq : l * (r - p) = p - q := by rw [hp]; field_simp; ring
  have hp0 := hfacts p left_mem_uIcc
  have hpr : p - r ≠ 0 := hp0.2.2
  have hqr' : q - r ≠ 0 := sub_ne_zero.2 hqr
  have hL := ksWB_log_one_add hqr hl hσq hσr
  rw [log_div hqr' hpr, log_div hqσ.ne' hp0.2.1.ne'] at hL
  simp only [hG, sub_self, mul_zero, zero_mul, zero_div, zero_sub, hpq]
  simp only [ksUKer]
  have hz : l * (r + σ) / (q + σ) ≠ 0 := by positivity
  rw [← hL, hC]
  field_simp
  ring


/-- **The dispersion of the `K` node** `K(z(s))`, `z(s) = l(r + s)/(q + s)`: its density is
`log(-z(-t)) = log(l(r - t)) - log(t - q)` on the oriented interval `p..q`. -/
theorem ksWB_K_node {s : ℝ} (hsq : -q < s) (hsr : -r < s) :
    ksUK (l * (r + s) / (q + s)) - ksUK (l * r / q) =
      ∫ t in (l * r + q) / (1 + l)..q, (log (l * (r - t)) - log (t - q)) * (s / (t * (s + t))) := by
  set p := (l * r + q) / (1 + l) with hp
  have hp0 := ksWB_uIcc_facts hq hr hqr hl hsq hsr (left_mem_uIcc : p ∈ uIcc p q)
  have hlr : ∀ t ∈ uIcc p q, l * (r - t) ≠ 0 := fun t ht =>
    mul_ne_zero hl.ne' fun h =>
      (ksWB_uIcc_facts hq hr hqr hl hsq hsr ht).2.2 (by linarith)
  have hm : IntervalIntegrable (fun t => log (l * (r - t)) - log (t - q)) volume p q := by
    have hl1 : IntervalIntegrable (fun t => log (l * (r - t))) volume p q :=
      (ContinuousOn.log (by fun_prop) hlr).intervalIntegrable
    have hl2 : IntervalIntegrable (fun t => log (t - q)) volume p q := by
      have := (intervalIntegral.intervalIntegrable_log' (a := p - q) (b := q - q)).comp_sub_right q
      simpa using this
    exact hl1.sub hl2
  have hF : ∀ σ ∈ uIcc 0 s, HasDerivAt (fun σ => ksUK (l * (r + σ) / (q + σ)))
      (∫ t in p..q, (log (l * (r - t)) - log (t - q)) / (t + σ) ^ 2) σ := fun σ hσ => by
    have hσ0 : min 0 s ≤ σ := hσ.1
    have hσq : -q < σ := by
      rcases le_total 0 s with h | h
      · rw [min_eq_left h] at hσ0; linarith
      · rw [min_eq_right h] at hσ0; linarith
    have hσr : -r < σ := by
      rcases le_total 0 s with h | h
      · rw [min_eq_left h] at hσ0; linarith
      · rw [min_eq_right h] at hσ0; linarith
    have hqσ : q + σ ≠ 0 := by linarith
    rw [ksWB_integral_K_deriv hq hr hqr hl hσq hσr]
    have hz : HasDerivAt (fun σ => l * (r + σ) / (q + σ)) (l * (q - r) / (q + σ) ^ 2) σ := by
      have h := (((hasDerivAt_id σ).const_add r).const_mul l).div
        ((hasDerivAt_id σ).const_add q) hqσ
      refine h.congr_deriv ?_
      simp only [id]
      ring
    have hz0 : 0 < l * (r + σ) / (q + σ) :=
      div_pos (mul_pos hl (by linarith)) (by linarith)
    exact (ksU_hasDerivAt_ksUK hz0).comp σ hz
  have h := ksWB_sub_eq_of_deriv hp0.1 hq (by linarith [hp0.2.1]) hsq hm hF
  simpa using h

/-- The integrand of the `G₀ log(1 + z)/A_β` node is interval integrable. -/
theorem ksWB_intervalIntegrable_T1 (g₀ g₁ : ℝ) {s : ℝ} (hsq : -q < s) (hsr : -r < s) :
    IntervalIntegrable (fun t => (g₀ - g₁ * t) * (r / (r - t)) * (s / (t * (s + t))))
      volume ((l * r + q) / (1 + l)) q := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  obtain ⟨h0, h1, h2⟩ := ksWB_uIcc_facts hq hr hqr hl hsq hsr ht
  have h3 : r - t ≠ 0 := fun h => h2 (by linarith)
  have h4 : t * (s + t) ≠ 0 := mul_ne_zero h0.ne' (by linarith)
  exact (ContinuousAt.mul (ContinuousAt.mul (by fun_prop)
    (continuousAt_const.div (by fun_prop) h3)) (continuousAt_const.div (by fun_prop) h4)
    ).continuousWithinAt

/-- The integrand of the `K` node is interval integrable. -/
theorem ksWB_intervalIntegrable_K {s : ℝ} (hsq : -q < s) (hsr : -r < s) :
    IntervalIntegrable (fun t => (log (l * (r - t)) - log (t - q)) * (s / (t * (s + t))))
      volume ((l * r + q) / (1 + l)) q := by
  set p := (l * r + q) / (1 + l) with hp
  have hlr : ∀ t ∈ uIcc p q, l * (r - t) ≠ 0 := fun t ht =>
    mul_ne_zero hl.ne' fun h => (ksWB_uIcc_facts hq hr hqr hl hsq hsr ht).2.2 (by linarith)
  have hl1 : IntervalIntegrable (fun t => log (l * (r - t))) volume p q :=
    (ContinuousOn.log (by fun_prop) hlr).intervalIntegrable
  have hl2 : IntervalIntegrable (fun t => log (t - q)) volume p q := by
    have := (intervalIntegral.intervalIntegrable_log' (a := p - q) (b := q - q)).comp_sub_right q
    simpa using this
  have hk : ContinuousOn (fun t => s / (t * (s + t))) (uIcc p q) := by
    refine continuousOn_const.div (by fun_prop) fun t ht => ?_
    obtain ⟨h0, h1, -⟩ := ksWB_uIcc_facts hq hr hqr hl hsq hsr ht
    exact mul_ne_zero h0.ne' (by linarith)
  exact (hl1.sub hl2).mul_continuousOn hk

omit hq hr in
/-- The density of the `K` node is positive strictly between `p` and `q`. -/
theorem ksWB_K_density_pos {t : ℝ}
    (ht : t ∈ Ioo (min ((l * r + q) / (1 + l)) q) (max ((l * r + q) / (1 + l)) q)) :
    0 < log (l * (r - t)) - log (t - q) := by
  set p := (l * r + q) / (1 + l) with hp
  have hl1 : 0 < 1 + l := by linarith
  have e1 : p - r = (q - r) / (1 + l) := by rw [hp]; field_simp; ring
  have e2 : p - q = l * (r - q) / (1 + l) := by rw [hp]; field_simp; ring
  have htq : t ≠ q := by
    intro h; rw [h] at ht
    rcases le_total p q with h' | h'
    · rw [max_eq_right h'] at ht; exact lt_irrefl _ ht.2
    · rw [min_eq_right h'] at ht; exact lt_irrefl _ ht.1
  -- `l(r - t) - (t - q) = (1 + l)(p - t)` has the sign of `t - q`
  have key : l * (r - t) - (t - q) = (1 + l) * (p - t) := by rw [hp]; field_simp; ring
  rcases lt_or_gt_of_ne hqr with h | h
  · -- `q < p < r`
    have hpq : q < p := by
      have : 0 < l * (r - q) / (1 + l) := div_pos (mul_pos hl (by linarith)) hl1
      linarith
    rw [min_eq_right hpq.le, max_eq_left hpq.le] at ht
    have h1 : 0 < t - q := by linarith [ht.1]
    have h2 : t - q < l * (r - t) := by nlinarith [ht.2]
    rw [sub_pos]
    exact log_lt_log h1 h2
  · -- `r < p < q`
    have hpq : p < q := by
      have : l * (r - q) / (1 + l) < 0 := div_neg_of_neg_of_pos (by nlinarith) hl1
      linarith
    rw [min_eq_left hpq.le, max_eq_right hpq.le] at ht
    have h1 : 0 < q - t := by linarith [ht.2]
    have h2 : q - t < l * (t - r) := by nlinarith [ht.1]
    rw [sub_pos, ← log_neg_eq_log (t - q), ← log_neg_eq_log (l * (r - t)),
      show -(t - q) = q - t by ring, show -(l * (r - t)) = l * (t - r) by ring]
    exact log_lt_log h1 h2

end Nodes

end QED.ChainProof.SetAKS

end
