/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndShell
public import QED.ChainProof.SetCRegPieceE
import QED.ChainProof.SetCKRegCt
import QED.TwoLoop.CountertermScaling

/-!
# Set (c): a coincidence obstruction to the pointwise dispersion bound

The fixed counterterm kernel in `QED/ChainProof/SetCRegFront.lean` uses
the partial fractions of `QED/TwoLoop/VacuumPolarizationUnitLimit.lean`.
At coincident spectral and heavy regulator masses the actual value
satisfies a scalar inverse-mass bound, but differs from the dressed-photon
integral. One copy of the resulting jump survives in the fixed
counterterm sum, multiplied by the infrared-divergent charge coefficient.

The transverse main kernels and Feynman shares are continuous in the
positive spectral mass. In particular they cannot cancel the jump.
Consequently the Feynman kernel fails the pointwise bound at unit electron
mass and nonzero charge. The same follows for the total kernel under the
longitudinal cancellation of `QED/ChainProof/SetCRegLongShare.lean`.
-/

public section

open Complex Real MeasureTheory Filter Set
open scoped Topology
open QED.TwoLoop.VPUnit
open QED.WickModel (Params)
open QED.OneLoop.VertexLimit (chargeA0 chargeZ isChargeNormalized_chargeZ)
open QED.TwoLoop.UnitLLink (ladderCtBracket ladderDeltaOne_eq four_pi_sq_mul_eq_ladderDeltaOne)

namespace QED.ChainProof.SetCRegDisp

/-! ### The pointwise value of the fixed counterterms -/

/-- The partial-fraction definition evaluated at the coincident heavy mass. -/
theorem vpInsert_diag {a c : ℝ} (hac : a ≠ c) :
    vpInsert c a c = (c / (c - a)) ^ 2 * f2 c -
      (2 * (a / (c - a)) + 3 * (a / (c - a)) ^ 2) * f2 a -
      a ^ 2 / (c - a) * df2 a := by
  have hca := sub_ne_zero.mpr hac.symm
  have hac' := sub_ne_zero.mpr hac
  unfold vpInsert
  simp only [sub_self, div_zero, sub_zero, zero_sub, zero_mul]
  field_simp
  ring

private theorem f2_le_one {a : ℝ} (ha : 0 < a) : f2 a ≤ 1 := by
  unfold f2
  have h := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_f2Kernel ha) (intervalIntegrable_const (c := (1 : ℝ))) ?_
  · simpa using h
  intro x hx
  rw [f2Kernel, div_le_one (den_pos ha hx)]
  have h₁ : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have h₂ : 1 - x ≤ 1 := by linarith [hx.1]
  exact (mul_le_of_le_one_right (sq_nonneg x) h₂).trans
    (le_add_of_nonneg_right (mul_nonneg h₁ ha.le))

private theorem df2_bounds {a : ℝ} (ha : 0 < a) : 0 ≤ -df2 a ∧ -df2 a ≤ 1 / a := by
  rw [df2, neg_neg]
  refine ⟨intervalIntegral.integral_nonneg zero_le_one fun x _ =>
    div_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg _)) (sq_nonneg _), ?_⟩
  have h := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_df2Kernel ha) (intervalIntegrable_const (c := 1 / a)) ?_
  · simpa using h
  intro x hx
  have hs : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  set d := x ^ 2 + (1 - x) * a
  have hd : 0 < d := den_pos ha hx
  have hxd : x ^ 2 ≤ d := le_add_of_nonneg_right (mul_nonneg hs ha.le)
  have hsd : a * (1 - x) ≤ d := by dsimp [d]; linarith [sq_nonneg x]
  rw [df2Kernel, div_le_div_iff₀ (sq_pos_of_pos hd) ha]
  calc
    _ = (x ^ 2 * (1 - x)) * (a * (1 - x)) := by ring
    _ ≤ d * d := mul_le_mul
      ((mul_le_of_le_one_right (sq_nonneg x) (by linarith [hx.1])).trans hxd)
      hsd (mul_nonneg ha.le hs) hd.le
    _ = _ := by ring

private theorem vpInsert_diag_bounds {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hac : a ≤ c / 2) :
    f2 c - 10 * a / c ≤ vpInsert c a c ∧ vpInsert c a c ≤ 4 / (3 * c) + 2 * a / c := by
  have hd : 0 < c - a := by linarith
  set r := a / (c - a) with hr
  have hr0 : 0 ≤ r := div_nonneg ha.le hd.le
  have hr1 : r ≤ 1 := (div_le_one hd).2 (by linarith)
  have hr2 : r ≤ 2 * a / c := by
    rw [hr, div_le_div_iff₀ hd hc]
    nlinarith only [mul_nonneg ha.le (show 0 ≤ c - 2 * a by linarith)]
  have hsum : c / (c - a) = 1 + r := by
    rw [hr]
    field_simp
    ring
  have hh : 0 ≤ 2 * r + 3 * r ^ 2 := by positivity
  have hcoef : 2 * r + 3 * r ^ 2 ≤ 10 * a / c := by
    have hsq : r ^ 2 ≤ r := by nlinarith only [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
    calc
      2 * r + 3 * r ^ 2 ≤ 5 * r := by linarith only [hsq]
      _ ≤ 5 * (2 * a / c) := mul_le_mul_of_nonneg_left hr2 (by norm_num)
      _ = _ := by ring
  have hneg : (2 * r + 3 * r ^ 2) * f2 a ≤ 10 * a / c :=
    (mul_le_of_le_one_right hh (f2_le_one ha)).trans hcoef
  have hneg₀ : 0 ≤ (2 * r + 3 * r ^ 2) * f2 a := mul_nonneg hh (f2_nonneg ha)
  have hdf := df2_bounds ha
  have hpos : 0 ≤ (a * r) * -df2 a := mul_nonneg (mul_nonneg ha.le hr0) hdf.1
  have hpos' : (a * r) * -df2 a ≤ 2 * a / c := by
    calc
      _ ≤ (a * r) * (1 / a) := mul_le_mul_of_nonneg_left hdf.2 (by positivity)
      _ = r := by field_simp
      _ ≤ _ := hr2
  have hmain : f2 c ≤ (1 + r) ^ 2 * f2 c := by
    conv_lhs => rw [← one_mul (f2 c)]
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hr0, sq_nonneg r]) (f2_nonneg hc)
  have hmain' : (1 + r) ^ 2 * f2 c ≤ 4 / (3 * c) := by
    have hsq : (1 + r) ^ 2 ≤ 4 := by
      exact (pow_le_pow_left₀ (show 0 ≤ 1 + r by positivity)
        (show 1 + r ≤ 2 by linarith) 2).trans_eq (by norm_num)
    calc
      _ ≤ 4 * (1 / (3 * c)) :=
        mul_le_mul hsq (f2_le hc) (f2_nonneg hc) (by norm_num)
      _ = _ := by ring
  have hlt : a < c := by linarith
  rw [vpInsert_diag hlt.ne, hsum, ← hr]
  rw [show a ^ 2 / (c - a) = a * r by rw [hr]; ring]
  constructor <;> linarith only [hneg, hneg₀, hpos, hpos', hmain, hmain']

/-- A bound for the actual partial-fraction value, including its coincident heavy mass. -/
theorem abs_vpInsert_le {a b c : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (hab : a < b) (hc : 4 ≤ c) :
    |vpInsert c a b| ≤ 20 / c := by
  have hc₀ : 0 < c := by linarith
  have hac : a < c := by linarith
  by_cases hbc : c = b
  · subst b
    have h := vpInsert_diag_bounds ha hc₀ (by linarith)
    rw [abs_le]
    have h1 : 10 * a / c ≤ 10 / c := div_le_div_of_nonneg_right (by linarith) hc₀.le
    have h2 : 2 * a / c ≤ 2 / c := div_le_div_of_nonneg_right (by linarith) hc₀.le
    have he : 4 / (3 * c) = (4 / 3) * (1 / c) := by ring
    have hf : 0 ≤ 1 / c := by positivity
    rw [show 20 / c = 20 * (1 / c) by ring]
    rw [show 10 / c = 10 * (1 / c) by ring] at h1
    rw [show 2 / c = 2 * (1 / c) by ring] at h2
    constructor <;> linarith only [h.1, h.2, f2_nonneg hc₀, h1, h2, he, hf]
  · rw [vpInsert_eq_integral ha (ha.trans hab) hc₀ hac.ne' hbc hab.ne]
    obtain ⟨h₀, h₁⟩ := integral_regKernel_le hc₀ ha.le hab.le
    rw [abs_of_nonneg h₀]
    exact h₁.trans (by rw [div_le_div_iff₀ (by positivity) hc₀]; linarith)

-- The bounding integrand at zero light mass, extended continuously at x = 0.
private theorem integral_gap {c : ℝ} (hc : 0 < c) :
    (∫ x in (0 : ℝ)..1, f2Kernel c x *
      (1 - x ^ 2 / (x ^ 2 + (1 - x) * c)) ^ 2) < f2 c := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2 / (x ^ 2 + (1 - x) * c)) (Icc 0 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun _ hx => (den_pos hc hx).ne')
  unfold f2
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
    ((continuousOn_f2Kernel hc).mul ((continuousOn_const.sub hcont).pow 2))
    (continuousOn_f2Kernel hc) ?_ ?_
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hu0 : 0 ≤ x ^ 2 / (x ^ 2 + (1 - x) * c) :=
      div_nonneg (sq_nonneg _) (den_pos hc hx').le
    have hu1 : x ^ 2 / (x ^ 2 + (1 - x) * c) ≤ 1 :=
      (div_le_one (den_pos hc hx')).2
        (le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hx.2) hc.le))
    apply mul_le_of_le_one_right (f2Kernel_nonneg hc hx')
    nlinarith only [hu0, hu1, mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  · refine ⟨1 / 2, by norm_num, ?_⟩
    have hd : 0 < (1 / 2 : ℝ) ^ 2 + (1 - 1 / 2) * c := by positivity
    have hu0 : 0 < (1 / 2 : ℝ) ^ 2 / ((1 / 2) ^ 2 + (1 - 1 / 2) * c) := by positivity
    have hu1 : (1 / 2 : ℝ) ^ 2 / ((1 / 2) ^ 2 + (1 - 1 / 2) * c) < 1 := by
      rw [div_lt_one hd]; linarith
    have hf : 0 < f2Kernel c (1 / 2) := by unfold f2Kernel; positivity
    apply mul_lt_of_lt_one_right hf
    simpa using pow_lt_pow_left₀ (sub_lt_self 1 hu0) (sub_nonneg.mpr hu1.le) two_ne_zero

private theorem integral_regKernel_diag_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hac : a ≤ c) :
    (∫ x in (0 : ℝ)..1, regKernel c a c x) ≤
      ∫ x in (0 : ℝ)..1, f2Kernel c x * (1 - x ^ 2 / (x ^ 2 + (1 - x) * c)) ^ 2 := by
  have hcont (d : ℝ) (hd : 0 < d) :
      ContinuousOn (fun x : ℝ => x ^ 2 / (x ^ 2 + (1 - x) * d)) (Icc 0 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun _ hx => (den_pos hd hx).ne')
  have hreg : ContinuousOn (regKernel c a c) (Icc 0 1) :=
    (continuousOn_f2Kernel hc).mul (((hcont a ha).sub (hcont c hc)).pow 2)
  have hupper : ContinuousOn (fun x : ℝ =>
      f2Kernel c x * (1 - x ^ 2 / (x ^ 2 + (1 - x) * c)) ^ 2) (Icc 0 1) :=
    (continuousOn_f2Kernel hc).mul ((continuousOn_const.sub (hcont c hc)).pow 2)
  refine intervalIntegral.integral_mono_on zero_le_one (hreg.intervalIntegrable_of_Icc zero_le_one)
    (hupper.intervalIntegrable_of_Icc zero_le_one) fun x hx => ?_
  have hs : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hdiff : 0 ≤ x ^ 2 / (x ^ 2 + (1 - x) * a) - x ^ 2 / (x ^ 2 + (1 - x) * c) := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (sq_nonneg x) (den_pos ha hx)
      (add_le_add_right (mul_le_mul_of_nonneg_left hac hs) _)
  have hx1 : x ^ 2 / (x ^ 2 + (1 - x) * a) ≤ 1 :=
    (div_le_one (den_pos ha hx)).2 (le_add_of_nonneg_right (mul_nonneg hs ha.le))
  unfold regKernel
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdiff (sub_le_sub_right hx1 _) 2)
    (f2Kernel_nonneg hc hx)

/-- At any fixed heavy mass, the partial-fraction value at coincidence exceeds the
dressed-photon integral by a positive gap for sufficiently small light regulator. -/
theorem exists_pos_le_vpInsert_diag_sub_integral {c : ℝ} (hc : 0 < c) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ a, 0 < a → a < δ →
      ε ≤ vpInsert c a c - ∫ x in (0 : ℝ)..1, regKernel c a c x := by
  set U := ∫ x in (0 : ℝ)..1, f2Kernel c x * (1 - x ^ 2 / (x ^ 2 + (1 - x) * c)) ^ 2
  have hU : U < f2 c := integral_gap hc
  set ε := (f2 c - U) / 2 with hε
  have hε₀ : 0 < ε := by linarith
  refine ⟨ε, min (c / 2) (ε * c / 10), hε₀, lt_min (by positivity) (by positivity),
    fun a ha hδ => ?_⟩
  have hac := hδ.le.trans (min_le_left _ _)
  have hb := (vpInsert_diag_bounds ha hc hac).1
  have hI := integral_regKernel_diag_le ha hc (by linarith)
  have hδ' := hδ.trans_le (min_le_right _ _)
  have hε' : 10 * a / c < ε := by
    rw [div_lt_iff₀ hc]
    linarith only [hδ']
  linarith only [hI, hb, hε', hε]

/-- Only one copy of the fixed vertex-counterterm factor survives the signed sum. -/
theorem sum_uCBC_eq (P₀ : Params) (mγ Λ T : ℝ) :
    (∑ k, uCBC P₀ k mγ Λ T) =
      cbVPKer P₀ mγ Λ T -
        2 * I * ((P₀.e ^ 4 / (16 * π ^ 4) * cb01B P₀ mγ Λ *
          vpInsertW T ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2) : ℝ) : ℂ) := by
  norm_num [Fin.sum_univ_succ, uCBOf, cb01KerC, cb01Ker]
  ring

/-- The fixed counterterms have a pointwise inverse-spectral-mass bound with their
explicit regulator coefficients. -/
theorem norm_sum_uCBC_le (P₀ : Params) {mγ Λ T : ℝ}
    (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hmγm : mγ ≤ P₀.m) (hΛ : mγ < Λ)
    (hT : 4 ≤ T) :
    ‖∑ k, uCBC P₀ k mγ Λ T‖ ≤
      (P₀.e ^ 4 / (16 * π ^ 4)) *
        ((20 * |chargeA0 P₀.e P₀.m mγ Λ| + 12 * |cb01B P₀ mγ Λ|) / T) := by
  have ha : 0 < (mγ / P₀.m) ^ 2 := by positivity
  have ha1 : (mγ / P₀.m) ^ 2 ≤ 1 :=
    (pow_le_pow_left₀ (div_nonneg hmγ.le hm.le) ((div_le_one hm).2 hmγm) 2).trans_eq
      (by norm_num)
  have hab := pow_lt_pow_left₀ (div_lt_div_of_pos_right hΛ hm)
    (div_nonneg hmγ.le hm.le) two_ne_zero
  have hT₀ : 0 < T := by linarith
  have hF := abs_vpInsert_le ha ha1 hab hT
  have hW := abs_vpInsertW_le ha hab.le hT₀
  have hn : 0 ≤ P₀.e ^ 4 / (16 * π ^ 4) := by positivity
  rw [sum_uCBC_eq, cbVPKer]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
    Complex.norm_ofNat, abs_of_nonneg hn]
  calc
    _ ≤ |chargeA0 P₀.e P₀.m mγ Λ| * (P₀.e ^ 4 / (16 * π ^ 4) * (20 / T)) +
        2 * (P₀.e ^ 4 / (16 * π ^ 4) * |cb01B P₀ mγ Λ| * (6 / T)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF hn) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hW (mul_nonneg hn (abs_nonneg _))) (by norm_num))
    _ = _ := by ring

/-- At fixed positive heavy regulator, the unit-mass charge coefficient
diverges to negative infinity as the light regulator tends to zero. -/
theorem tendsto_chargeA0_unit_atBot {e Λ : ℝ} (he : e ≠ 0) (hΛ : 0 < Λ) :
    Tendsto (fun mγ => chargeA0 e 1 mγ Λ) (𝓝[>] 0) atBot := by
  have hsub := QED.ChainProof.SetCK.tendsto_integral_ladderCtBracket_sub_log
  have hct : Tendsto (fun mγ => ∫ Y in (0 : ℝ)..1, ladderCtBracket mγ Y)
      (𝓝[>] 0) atBot := by
    refine (Tendsto.atBot_add Real.tendsto_log_nhdsGT_zero hsub).congr fun mγ => ?_
    ring
  have hf : 0 < e ^ 2 / (4 * π ^ 2) := by positivity
  have hscaled := (tendsto_atBot_add_const_right _ (-(∫ Y in (0 : ℝ)..1, ladderCtBracket Λ Y))
    hct).const_mul_atBot hf
  refine hscaled.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with mγ (hγ : 0 < mγ)
  have hch : QED.OneLoop.IsChargeNormalized 1 (1 + -chargeA0 1 1 mγ Λ)
      1 mγ Λ one_pos hγ hΛ := by
    simpa only [chargeZ, sub_eq_add_neg] using
      (isChargeNormalized_chargeZ (e := 1) one_pos hγ hΛ)
  have hδ := four_pi_sq_mul_eq_ladderDeltaOne one_pos hγ hΛ hch
  rw [ladderDeltaOne_eq hγ hΛ] at hδ
  rw [QED.TwoLoop.Scaling.chargeA0_eq e]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  linear_combination hδ

theorem continuousAt_integral_regKernel {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) :
    ContinuousAt (fun t => ∫ x in (0 : ℝ)..1, regKernel t a b x) c := by
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => 2 / c) ?_ ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun t => Measurable.aestronglyMeasurable ?_
    unfold regKernel f2Kernel
    fun_prop
  · filter_upwards [Ioi_mem_nhds (show c / 2 < c by linarith)] with t ht
    refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have ht₀ : 0 < t := (half_pos hc).trans (show c / 2 < t from ht)
    rw [Real.norm_of_nonneg (regKernel_nonneg ht₀ hx')]
    calc
      _ ≤ f2Kernel t x := regKernel_le ht₀ ha.le hab hx'
      _ ≤ x ^ 2 / t := f2Kernel_le ht₀ hx'
      _ ≤ 1 / t := div_le_div_of_nonneg_right
        (by simpa using pow_le_pow_left₀ hx'.1 hx'.2 2) ht₀.le
      _ ≤ 2 / c := by rw [div_le_div_iff₀ ht₀ hc]; linarith [show c / 2 < t from ht]
  · refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hpos := den_pos hc ⟨hx.1.le, hx.2⟩
    unfold regKernel f2Kernel
    apply ContinuousAt.mul
    · exact continuousAt_const.div (by fun_prop) hpos.ne'
    · exact continuousAt_const

theorem continuousAt_vpInsertW {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) :
    ContinuousAt (fun t => vpInsertW t a b) c := by
  unfold vpInsertW
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => 12 / c) ?_ ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun t => Measurable.aestronglyMeasurable ?_
    unfold wKer wKerK
    fun_prop
  · filter_upwards [Ioi_mem_nhds (show c / 2 < c by linarith)] with t ht
    refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have ht₀ : 0 < t := (half_pos hc).trans (show c / 2 < t from ht)
    exact (abs_wKer_le ha hab ht₀ ⟨hx.1.le, hx.2⟩).trans
      (by rw [div_le_div_iff₀ ht₀ hc]; linarith [show c / 2 < t from ht])
  · refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hK : 0 ≤ x ^ 2 / (1 - x) := div_nonneg (sq_nonneg _) (sub_nonneg.mpr hx.2)
    have hden : x ^ 2 / (1 - x) + c ≠ 0 := (add_pos_of_nonneg_of_pos hK hc).ne'
    unfold wKer wKerK
    exact continuousAt_const.mul ((continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hden).sub
      (continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2)
        (pow_ne_zero 2 hden)))

/-! ### The obstruction under a continuous remainder -/

/-- Any summand continuous in the spectral variable at the coincident heavy mass
preserves the obstruction to a pointwise uniform estimate for the fixed counterterms. -/
theorem not_uniform_uCBC_add_continuous_at_diag (P₀ : Params)
    (hm : P₀.m = 1) (he : P₀.e ≠ 0) (F : ℝ → ℝ → ℝ → ℂ)
    (hF : ∀ a b : ℝ, 0 < a → a < b → 4 < b ^ 2 → ContinuousAt (F a b) (b ^ 2)) :
    ¬ ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ a b, 0 < a → a < δ → Λ₀ < b → ∀ t, 4 ≤ t →
      ‖F a b t + ∑ k, uCBC P₀ k a b t‖ ≤ C / Real.sqrt t := by
  rintro ⟨C, δ, Λ₀, hδ, hbd⟩
  let b := max (Λ₀ + 1) 3
  have hb₃ : 3 ≤ b := le_max_right _ _
  have hb : 0 < b := by linarith
  have hbΛ : Λ₀ < b := (lt_add_one _).trans_le (le_max_left _ _)
  have hb₄ : 4 < b ^ 2 := by nlinarith only [hb₃, sq_nonneg (b - 3)]
  let K := P₀.e ^ 4 / (16 * π ^ 4)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨ε, η, hε, hη, hgap⟩ := exists_pos_le_vpInsert_diag_sub_integral (sq_pos_of_pos hb)
  let M := 2 * (C / √(b ^ 2))
  have hev : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      chargeA0 P₀.e 1 a b < -(M / (K * ε)) :=
    (tendsto_chargeA0_unit_atBot he hb).eventually (eventually_lt_atBot _)
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), a ∈ Ioo 0 (min δ (min b (√η))) :=
    Ioo_mem_nhdsGT (lt_min hδ (lt_min hb (Real.sqrt_pos.2 hη)))
  obtain ⟨a, hq, ha, hsmall⟩ := (hev.and hsmall).exists
  have haδ : a < δ := hsmall.trans_le (min_le_left _ _)
  have hab : a < b := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have haη : a ^ 2 < η := by
    rw [← Real.sq_sqrt hη.le]
    exact pow_lt_pow_left₀
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))) ha.le two_ne_zero
  have ha₂ : 0 < a ^ 2 := sq_pos_of_pos ha
  have hab₂ : a ^ 2 < b ^ 2 := pow_lt_pow_left₀ hab ha.le two_ne_zero
  let G := fun t => ∫ x in (0 : ℝ)..1, regKernel t (a ^ 2) (b ^ 2) x
  let W := fun t => vpInsertW t (a ^ 2) (b ^ 2)
  let Q := chargeA0 P₀.e 1 a b
  let H := fun t => F a b t - (Q : ℂ) * I * ((K * G t : ℝ) : ℂ) -
    2 * I * ((K * cb01B P₀ a b * W t : ℝ) : ℂ)
  have hG : ContinuousAt G (b ^ 2) := continuousAt_integral_regKernel ha₂ hab₂.le
    (sq_pos_of_pos hb)
  have hW : ContinuousAt W (b ^ 2) := continuousAt_vpInsertW ha₂ hab₂.le (sq_pos_of_pos hb)
  have hH : ContinuousAt H (b ^ 2) :=
    ((hF a b ha hab hb₄).sub (continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul hG)))).sub
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul hW)))
  have hp (t : ℝ) (ht : b ^ 2 < t) : H t = F a b t + ∑ k, uCBC P₀ k a b t := by
    rw [sum_uCBC_eq, cbVPKer, hm, div_one, div_one]
    rw [vpInsert_eq_integral ha₂ (sq_pos_of_pos hb) (by linarith) (hab₂.trans ht).ne'
      ht.ne' hab₂.ne]
    simp only [H, Q, K, G, W]
    ring
  have hlimit : ‖H (b ^ 2)‖ ≤ C / √(b ^ 2) := by
    have hL := hH.norm.continuousWithinAt (s := Ioi (b ^ 2))
    have hR : ContinuousAt (fun t : ℝ => C / √t) (b ^ 2) :=
      continuousAt_const.div Real.continuous_sqrt.continuousAt
        (Real.sqrt_pos.2 (sq_pos_of_pos hb)).ne'
    apply le_of_tendsto_of_tendsto hL hR.continuousWithinAt
    filter_upwards [self_mem_nhdsWithin] with t (ht : b ^ 2 < t)
    rw [hp t ht]
    exact hbd a b ha haδ hbΛ t (hb₄.trans ht).le
  have hdiag := hbd a b ha haδ hbΛ (b ^ 2) hb₄.le
  have hpos := hgap (a ^ 2) ha₂ haη
  have hjump : (F a b (b ^ 2) + ∑ k, uCBC P₀ k a b (b ^ 2)) - H (b ^ 2) =
      -(Q : ℂ) * I * ((K * (vpInsert (b ^ 2) (a ^ 2) (b ^ 2) - G (b ^ 2)) : ℝ) : ℂ) := by
    rw [sum_uCBC_eq, cbVPKer, hm, div_one, div_one]
    simp only [H, Q, K, G, W]
    push_cast
    ring
  have hj := (norm_sub_le (F a b (b ^ 2) + ∑ k, uCBC P₀ k a b (b ^ 2)) (H (b ^ 2))).trans
    (add_le_add hdiag hlimit)
  rw [hjump] at hj
  have hnonneg : 0 ≤ vpInsert (b ^ 2) (a ^ 2) (b ^ 2) - G (b ^ 2) :=
    hε.le.trans hpos
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
    abs_of_pos hK, abs_of_nonneg hnonneg] at hj
  have hle : (K * ε) * |Q| ≤ M := by
    calc
      _ ≤ |Q| * (K * (vpInsert (b ^ 2) (a ^ 2) (b ^ 2) - G (b ^ 2))) := by
        rw [mul_comm (K * ε)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpos hK.le) (abs_nonneg _)
      _ ≤ M := hj.trans_eq (by dsimp [M]; ring)
  have hlt : M < (K * ε) * |Q| := by
    have hh : M / (K * ε) < -Q := by linarith only [hq]
    rw [div_lt_iff₀ (mul_pos hK hε)] at hh
    exact hh.trans_le (mul_le_mul_of_nonneg_right (neg_le_abs Q) (mul_pos hK hε).le)
      |>.trans_eq (mul_comm _ _)
  exact (not_lt_of_ge hle) hlt

-- Multiplication by the imaginary unit embeds the real part after division by it.
private theorem I_mul_re_div_I (x : ℝ) :
    ((1 / I) * (I * (x : ℂ))).re = x := by
  rw [← mul_assoc, div_mul_cancel₀ _ I_ne_zero, one_mul, ofReal_re]

private theorem sum_uCBC_eq_I_mul (P₀ : Params) (a b t : ℝ) :
    ∃ x : ℝ, (∑ k, uCBC P₀ k a b t) = I * (x : ℂ) := by
  set K := P₀.e ^ 4 / (16 * π ^ 4)
  refine ⟨-chargeA0 P₀.e P₀.m a b * (K *
    vpInsert t ((a / P₀.m) ^ 2) ((b / P₀.m) ^ 2)) -
      2 * (K * cb01B P₀ a b * vpInsertW t ((a / P₀.m) ^ 2) ((b / P₀.m) ^ 2)), ?_⟩
  rw [sum_uCBC_eq, cbVPKer]
  change -(chargeA0 P₀.e P₀.m a b : ℂ) * I *
      ((K * vpInsert t ((a / P₀.m) ^ 2) ((b / P₀.m) ^ 2) : ℝ) : ℂ) - _ = _
  dsimp only [K]
  push_cast
  ring

/-- The coincidence obstruction in the real kernel normalization, conditional on
continuity of the real main/share sum at the coincident heavy mass. -/
theorem not_uniform_kerRe_of_continuous_at_diag (P₀ : Params)
    (hm : P₀.m = 1) (he : P₀.e ≠ 0)
    (U : Fin 12 → ℝ → ℝ → ℝ → ℂ) (S : Fin 5 → ℝ → ℝ → ℝ → ℂ)
    (hcont : ∀ a b : ℝ, 0 < a → a < b → 4 < b ^ 2 →
      ContinuousAt (fun t => ((1 / I) * ((∑ i, U i a b t) + ∑ k, S k a b t)).re)
        (b ^ 2)) :
    ¬ ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ a b, 0 < a → a < δ → Λ₀ < b → ∀ t, 4 ≤ t →
      |kerRe P₀ U (uCBC P₀) S a b t| ≤ C / Real.sqrt t := by
  rintro ⟨C, δ, Λ₀, hδ, hbd⟩
  let R := fun a b t => ((1 / I) * ((∑ i, U i a b t) + ∑ k, S k a b t)).re
  let F := fun a b t => I * (R a b t : ℂ)
  have hF (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : 4 < b ^ 2) :
      ContinuousAt (F a b) (b ^ 2) :=
    continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp (hcont a b ha hab hb))
  let K := 64 * π ^ 6 / P₀.e ^ 6
  have hK : 0 < K := by dsimp [K]; positivity
  apply not_uniform_uCBC_add_continuous_at_diag P₀ hm he F hF
  refine ⟨C / K, δ, Λ₀, hδ, fun a b ha haδ hb t ht => ?_⟩
  obtain ⟨x, hx⟩ := sum_uCBC_eq_I_mul P₀ a b t
  rw [hx, show F a b t + I * (x : ℂ) = I * ((R a b t + x : ℝ) : ℂ) by
    simp only [F, ofReal_add, mul_add]]
  rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hs : ((1 / I) * ((∑ i, U i a b t) + (∑ k, uCBC P₀ k a b t) + ∑ k, S k a b t)).re =
      R a b t + x := by
    rw [add_right_comm (∑ i, U i a b t), mul_add, add_re, hx, I_mul_re_div_I]
  have h := hbd a b ha haδ hb t ht
  rw [kerRe, hs] at h
  change |K * (R a b t + x)| ≤ C / √t at h
  rw [abs_mul, abs_of_pos hK, mul_comm] at h
  rw [div_right_comm, le_div_iff₀ hK]
  exact h

end QED.ChainProof.SetCRegDisp

end

public section

open Complex Real Set Filter
open scoped Topology
open QED.WickModel (Params)
open QED.ChainProof.SetCUnit QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration
open QED.TwoLoop.ClassIntegrable (openClasses)

namespace QED.ChainProof.SetCRegDisp

/-! ### Continuity of the transverse main kernels -/

private theorem extra_mass_sub {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ a b z w : ℝ}
    (hμ : 0 < μ) (ha : μ ≤ a) (hb : μ ≤ b) (hz : μ ≤ z) (hw : μ ≤ w) :
    unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, z]) 2 -
      unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, w]) 2 =
      ((w ^ 2 - z ^ 2 : ℝ) : ℂ) *
        unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, z, w]) 2 := by
  have hg : MassesGe μ a b a b := ⟨ha, hb, ha, hb⟩
  have hκ : TrailOne 3 (fun _ : Fin 4 => (1 : ℝ)) := fun _ _ => rfl
  have hX (u v : ℝ) (hu : μ ≤ u) (hv : μ ≤ v) :
      ExtraGe μ (fun _ => 1) ![a, b, u, v] := by
    intro j
    refine ⟨one_pos, le_rfl, ?_⟩
    fin_cases j
    · exact ha
    · exact hb
    · exact hu
    · exact hv
  have h1 := unitMPauliZeroPow_succ hc P hm hs hμ hg (n := 2) (r := 3)
    (by decide) hκ (hX z w hz hw)
  have h2 := unitMPauliZeroPow_succ hc P hm hs hμ hg (n := 2) (r := 3)
    (by decide) hκ (hX w z hw hz)
  have hi (u v : ℝ) : Fin.init (![a, b, u, v] : Fin 4 → ℝ) = ![a, b, u] := by
    funext j
    fin_cases j <;> rfl
  rw [hi] at h1 h2
  have hp (n : ℕ) :
      unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, w, z]) n =
        unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, z, w]) n := by
    let σ := Equiv.swap (2 : Fin 4) 3
    have hσ : (![a, b, z, w] : Fin 4 → ℝ) ∘ σ = ![a, b, w, z] := by
      funext j
      fin_cases j <;> rfl
    simpa only [hσ, Function.comp_def] using
      unitMPauliZeroPow_perm c P s σ (fun _ => 1) P.m a b a b ![a, b, z, w] n
  rw [hp 3, hp 2] at h2
  change unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, z, w]) 3 =
    unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, z]) 2 -
      ((w ^ 2 : ℝ) : ℂ) *
        unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, z, w]) 2 at h1
  change unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, z, w]) 3 =
    unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, w]) 2 -
      ((z ^ 2 : ℝ) : ℂ) *
        unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m a b a b ![a, b, z, w]) 2 at h2
  push_cast at h1 h2 ⊢
  linear_combination h2 - h1

/-- The transverse Pauli kernel is continuous at every positive spectral mass,
including coincidence with a regulator mass. -/
theorem continuousAt_kerT {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {mγ Λ T : ℝ}
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) :
    ContinuousAt (kerT c P s mγ Λ) T := by
  let z := fun t : ℝ => √(P.m ^ 2 * t)
  let μ := min mγ (min Λ (z (T / 2)))
  have hμ : 0 < μ := lt_min hmγ (lt_min hΛ (Real.sqrt_pos.2 (by positivity)))
  have hμa : μ ≤ mγ := min_le_left _ _
  have hμb : μ ≤ Λ := (min_le_right _ _).trans (min_le_left _ _)
  have hμz (t : ℝ) (ht : T / 2 ≤ t) : μ ≤ z t :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ht (sq_nonneg _)))
  have hμT := hμz T (by linarith)
  have hzsq (t : ℝ) (ht : 0 ≤ t) : z t ^ 2 = P.m ^ 2 * t :=
    Real.sq_sqrt (mul_nonneg (sq_nonneg _) ht)
  have hrot (t : ℝ) : kerT c P s mγ Λ t =
      unitMPauliZeroPow c P s (fun _ => 1) (unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ, z t]) 2 := by
    rw [kerT, unitMPauliZeroPow_repBExtra_rot]
  obtain ⟨C, hC⟩ := norm_unitMPauliZeroPow_le hc P hm hs hμ 2 (r := 4)
    (κ := fun _ => 1) (by decide) (fun _ _ => rfl) (fun _ => ⟨one_pos, le_rfl⟩)
  let D := 1 + (∑ i, unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ] i ^ 2) + 2 * (P.m ^ 2 * (T + 1))
  let B := |C| * D ^ 4
  have hB (t : ℝ) (ht : t ∈ Ioo (T / 2) (T + 1)) :
      ‖unitMPauliZeroPow c P s (fun _ => 1)
          (unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ, z t, z T]) 2‖ ≤ B := by
    have hμs : ∀ j : Fin 4, μ ≤ (![mγ, Λ, z t, z T] : Fin 4 → ℝ) j := by
      intro j
      fin_cases j
      · exact hμa
      · exact hμb
      · exact hμz t ht.1.le
      · exact hμT
    have he : ∑ i, unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ, z t, z T] i ^ 2 =
        (∑ i, unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ] i ^ 2) + z t ^ 2 + z T ^ 2 := by
      rw [sum_sq_unitMMasses_succ]
      change (∑ i, unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ, z t] i ^ 2) + z T ^ 2 = _
      rw [sum_sq_unitMMasses_succ]
      rfl
    have hS : 1 + (∑ i, unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ, z t, z T] i ^ 2) ≤ D := by
      rw [he, hzsq t (by linarith [ht.1]), hzsq T hT.le]
      dsimp only [D]
      linarith only [mul_le_mul_of_nonneg_left ht.2.le (sq_nonneg P.m),
        mul_le_mul_of_nonneg_left (show T ≤ T + 1 by linarith) (sq_nonneg P.m)]
    have hCS := hC mγ Λ mγ Λ ![mγ, Λ, z t, z T] ⟨hμa, hμb, hμa, hμb⟩ hμs
    refine hCS.trans ?_
    have hs₀ : 0 ≤ 1 + ∑ i, unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ, z t, z T] i ^ 2 :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => sq_nonneg _)
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ hs₀ hS 4) (pow_nonneg hs₀ _) (abs_nonneg _)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (g := fun t : ℝ => |T - t| * (P.m ^ 2 * B))
  · have hcont : ContinuousAt (fun t : ℝ => |T - t| * (P.m ^ 2 * B)) T := by fun_prop
    simpa only [sub_self, abs_zero, zero_mul] using hcont.tendsto
  · have hnear : Ioo (T / 2) (T + 1) ∈ 𝓝 T := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hnear] with t ht
    rw [hrot t, hrot T, extra_mass_sub hc P hm hs hμ hμa hμb (hμz t ht.1.le) hμT, norm_mul,
      norm_real, Real.norm_eq_abs, hzsq T hT.le, hzsq t (by linarith [ht.1]),
      ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg P.m)]
    rw [mul_comm (P.m ^ 2), ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB t ht) (mul_nonneg (abs_nonneg _) (sq_nonneg _))

open QED.ChainProof.SetCMainB

/-- Each transverse main placement is continuous at every positive spectral mass. -/
theorem continuousAt_uBDT (P₀ : Params) (i : Fin 12) {mγ Λ T : ℝ}
    (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) :
    ContinuousAt (uBDT P₀ i mγ Λ) T := by
  let P : Params := { P₀ with mγ := mγ, Λ := Λ }
  have hk := continuousAt_kerT (repBClass_mem i) P hm (four_le_repBSlot i) hmγ hΛ hT
  unfold uBDT
  exact continuousAt_const.mul hk

end QED.ChainProof.SetCRegDisp

end

public section

open Complex Real MeasureTheory Set Filter
open scoped Topology
open QED.WickModel (Params)
open QED.TwoLoop.UnitLLink

namespace QED.ChainProof.SetCRegDisp

/-! ### The Feynman shares -/

/-- In the normalization of the real Feynman kernel, the centered share
estimate has constant 56. -/
theorem abs_kerRe_uSF_add_tail_le (P₀ : Params) {mγ Λ T : ℝ}
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmγ : 0 < mγ)
    (hreg : mγ ≤ Λ) (hT : 1 ≤ T) :
    |kerRe P₀ (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (uSF P₀) mγ Λ T +
      ((oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) / 4 +
        3 * dVm P₀.m mγ Λ / 2) * photonTail (vpPhotonT P₀.m mγ Λ T) 0|
      ≤ 56 / Real.sqrt T := by
  set K : ℝ := 64 * π ^ 6 / P₀.e ^ 6 with hK
  set A : ℝ := P₀.e ^ 6 / (128 * π ^ 6) with hA
  set L : ℝ := ((oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) / 2 + 3 * dVm P₀.m mγ Λ) *
    photonTail (vpPhotonT P₀.m mγ Λ T) 0 with hL
  have hKA : K * A = 1 / 2 := by
    rw [hK, hA]
    field_simp [he, Real.pi_ne_zero]
    ring
  have hA₀ : 0 ≤ A := by positivity
  have hK₀ : 0 ≤ K := by positivity
  have hpre : sCoefLine P₀ * (P₀.e ^ 4 / (32 * π ^ 4) : ℝ) = I * (A : ℂ) := by
    rw [sCoefLine, hA]
    push_cast
    field_simp [show (π : ℂ) ≠ 0 from ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
  have hbound := norm_sum_uSF_add_tail_le P₀ hm hmγ hreg hT
  rw [hpre, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hA₀] at hbound
  change ‖(∑ k, uSF P₀ k mγ Λ T) + I * (A : ℂ) * (L : ℂ)‖ ≤
    A * (112 / √T) at hbound
  have hproj := Complex.abs_re_le_norm
    ((1 / I) * ((∑ k, uSF P₀ k mγ Λ T) + I * (A : ℂ) * (L : ℂ)))
  rw [norm_mul, Complex.norm_div, norm_one, norm_I, div_one, one_mul] at hproj
  have hcancel : (1 / I : ℂ) * I = 1 := div_mul_cancel₀ _ I_ne_zero
  have hI : (1 / I : ℂ) * (I * (A : ℂ) * (L : ℂ)) = ((A * L : ℝ) : ℂ) := by
    calc
      _ = ((1 / I : ℂ) * I) * ((A : ℂ) * (L : ℂ)) := by ring
      _ = _ := by rw [hcancel, one_mul]; exact (Complex.ofReal_mul A L).symm
  rw [mul_add, add_re, hI, ofReal_re] at hproj
  have h := mul_le_mul_of_nonneg_left (hproj.trans hbound) hK₀
  rw [← abs_of_nonneg hK₀, ← abs_mul, mul_add, ← mul_assoc K, hKA] at h
  have hright : K * (A * (112 / √T)) = 56 / √T := by rw [← mul_assoc, hKA]; ring
  have hleft : 1 / 2 * L =
      ((oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) / 4 + 3 * dVm P₀.m mγ Λ / 2) *
        photonTail (vpPhotonT P₀.m mγ Λ T) 0 := by rw [hL]; ring
  rw [abs_of_nonneg hK₀, hright, hleft] at h
  simpa only [kerRe, Finset.sum_const_zero, zero_add, hK] using h

private theorem continuousAt_vpPhotonT_spectral {m mγ Λ T s : ℝ} (hm : 0 < m)
    (hT : 0 < T) (hs : 0 ≤ s) :
    ContinuousAt (fun t => vpPhotonT m mγ Λ t s) T := by
  unfold vpPhotonT
  have hcont : ContinuousAt (fun t : ℝ => s + t * m ^ 2) T := by fun_prop
  exact (continuousAt_const.div hcont (show s + T * m ^ 2 ≠ 0 by positivity)).mul
    continuousAt_const

private theorem vpPhotonT_anti {m mγ Λ t T s : ℝ} (hm : 0 < m)
    (ht : 0 < t) (htT : t ≤ T) (hs : 0 ≤ s) :
    vpPhotonT m mγ Λ T s ≤ vpPhotonT m mγ Λ t s := by
  unfold vpPhotonT
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (add_le_add_right (mul_le_mul_of_nonneg_right htT (sq_nonneg _)) s))
    (sq_nonneg _)

/-- The dressed-photon tail is continuous in the positive spectral mass. -/
theorem continuousAt_photonTail_vp {m mγ Λ T a : ℝ} (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (ha : 0 ≤ a) :
    ContinuousAt (fun t => photonTail (vpPhotonT m mγ Λ t) a) T := by
  unfold photonTail
  refine continuousAt_of_dominated
    (bound := fun u => vpPhotonT m mγ Λ (T / 2) (a + u)) ?_ ?_
    (integrableOn_vpPhotonT_shift hmγ hΛ (half_pos hT) hm ha) ?_
  · refine Eventually.of_forall fun t => Measurable.aestronglyMeasurable ?_
    exact (measurable_vpPhotonT m mγ Λ).comp
      (measurable_const.prodMk (measurable_const.add measurable_id))
  · filter_upwards [Ioi_mem_nhds (show T / 2 < T by linarith)] with t (ht : T / 2 < t)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    have hs : 0 ≤ a + u := add_nonneg ha (le_of_lt hu)
    rw [Real.norm_of_nonneg (vpPhotonT_nonneg hmγ hΛ ((half_pos hT).trans ht) hm hs)]
    exact vpPhotonT_anti hm (half_pos hT) ht.le hs
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    exact continuousAt_vpPhotonT_spectral hm hT (add_nonneg ha (le_of_lt hu))

private theorem continuousAt_weighted_shell_integral {m mγ Λ T : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T)
    {w v : ℝ → ℝ} (hw : Continuous w) (hv : Continuous v) :
    ContinuousAt (fun t => ∫ x in (0 : ℝ)..1,
      w x * vpPhotonT m mγ Λ t (shellArg m x) -
        v x * photonTail (vpPhotonT m mγ Λ t) (shellArg m x)) T := by
  let B := photonK mγ Λ / (T / 2 * m ^ 2)
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun x => ‖w x‖ * B + ‖v x‖ * (B * π)) ?_ ?_
    (((hw.norm.mul continuous_const).add (hv.norm.mul continuous_const)).intervalIntegrable
      0 1) ?_
  · refine Eventually.of_forall fun t => Measurable.aestronglyMeasurable ?_
    exact (hw.measurable.mul ((measurable_vpPhotonT m mγ Λ).comp
      (measurable_const.prodMk (measurable_shellArg m)))).sub
        (hv.measurable.mul ((measurable_photonTail_vp m mγ Λ).comp
          (measurable_const.prodMk (measurable_shellArg m))))
  · filter_upwards [Ioi_mem_nhds (show T / 2 < T by linarith)] with t (ht : T / 2 < t)
    refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hs := shellArg_nonneg m (Ioc_subset_Icc_self hx)
    have ht₀ := (half_pos hT).trans ht
    have hden : photonK mγ Λ / (t * m ^ 2) ≤ B :=
      div_le_div_of_nonneg_left (photonK_nonneg _ _) (by positivity)
        (mul_le_mul_of_nonneg_right ht.le (sq_nonneg _))
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, Real.norm_of_nonneg (vpPhotonT_nonneg hmγ hΛ ht₀ hm hs),
      Real.norm_of_nonneg (photonTail_nonneg hmγ hΛ ht₀ hm hs)]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    · refine (vpPhotonT_le hmγ hΛ ht₀ hm hs).trans ?_
      have hbase : 0 ≤ photonK mγ Λ / (t * m ^ 2) :=
        div_nonneg (photonK_nonneg _ _) (by positivity)
      have hunit : (1 + shellArg m x ^ 2)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _))
      exact (mul_le_of_le_one_right hbase hunit).trans hden
    · exact (photonTail_le hmγ hΛ ht₀ hm hs).trans
        (mul_le_mul_of_nonneg_right hden Real.pi_pos.le)
  · refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hs := shellArg_nonneg m (Ioc_subset_Icc_self hx)
    exact (continuousAt_const.mul (continuousAt_vpPhotonT_spectral hm hT hs)).sub
      (continuousAt_const.mul (continuousAt_photonTail_vp hm hmγ hΛ hT hs))

/-- The Feynman share sum is continuous at positive spectral mass with fixed regulators. -/
theorem continuousAt_sum_uSF (P₀ : Params) {mγ Λ T : ℝ}
    (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) :
    ContinuousAt (fun t => ∑ k, uSF P₀ k mγ Λ t) T := by
  have hV : ContinuousAt (shellKer₀ P₀ mγ Λ) T := by
    have h := continuousAt_weighted_shell_integral hm hmγ hΛ hT
      (w := fun _ => 0) (v := fun x => -(1 + x)) continuous_const (by fun_prop)
    simp only [zero_mul, neg_mul, sub_neg_eq_add, zero_add] at h
    exact Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul h)
  have hS : ContinuousAt (shellKer₁ P₀ mγ Λ) T :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul
      (continuousAt_weighted_shell_integral hm hmγ hΛ hT
        (w := fun x => 2 * P₀.m ^ 2 * x * (1 + x)) (v := fun x => 1 - x)
        (by fun_prop) (by fun_prop)))
  simp only [sum_uShare, massKer]
  fun_prop

end QED.ChainProof.SetCRegDisp

end

public section

open Complex Real Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

/-! ### Failure of the uniform bound -/

/-- The current Feynman kernel admits no pointwise uniform dispersion bound at unit mass. -/
theorem not_uniform_feyn_kerRe (P₀ : Params) (hm : P₀.m = 1) (he : P₀.e ≠ 0) :
    ¬ ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ a b, 0 < a → a < δ → Λ₀ < b → ∀ t, 4 ≤ t →
      |kerRe P₀ (uBDT P₀) (uCBC P₀) (uSF P₀) a b t| ≤ C / Real.sqrt t := by
  have hm₀ : 0 < P₀.m := hm ▸ one_pos
  apply not_uniform_kerRe_of_continuous_at_diag P₀ hm he
  intro a b ha hab hb
  have ht : 0 < b ^ 2 := by linarith
  have hmain : ContinuousAt (fun t => ∑ i, uBDT P₀ i a b t) (b ^ 2) := by
    exact tendsto_finsetSum _ fun i _ =>
      (continuousAt_uBDT P₀ i hm₀ ha (ha.trans hab) ht).tendsto
  have hshare := continuousAt_sum_uSF P₀ hm₀ ha (ha.trans hab) ht
  exact Complex.continuous_re.continuousAt.comp
    (continuousAt_const.mul (hmain.add hshare))

/-- With longitudinal cancellation, the regulator-limit bound for the current total
kernel would imply the impossible Feynman bound at unit mass. -/
theorem not_uniform_setCKerRe_of_isKKCancel (P₀ : Params) (hm : P₀.m = 1)
    (he : P₀.e ≠ 0) (hKK : IsKKCancel P₀) :
    ¬ ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ a b, 0 < a → a < δ → Λ₀ < b → ∀ t, 4 ≤ t →
      |setCKerRe P₀ (uBD P₀) a b t| ≤ C / Real.sqrt t := by
  rintro ⟨C, δ, Λ₀, hδ, hbd⟩
  apply not_uniform_feyn_kerRe P₀ hm he
  refine ⟨C, min δ 1, max Λ₀ 1, lt_min hδ one_pos, fun a b ha haδ hb t ht => ?_⟩
  have hab : a < b := (haδ.trans_le (min_le_right _ _)).trans
    ((le_max_right _ _).trans_lt hb)
  rw [← setCKerRe_eq_feyn he (hm ▸ one_pos) hKK ha hab t]
  exact hbd a b ha (haδ.trans_le (min_le_left _ _)) ((le_max_left _ _).trans_lt hb) t ht

/-- The bound field rules out the current predicate under longitudinal cancellation. -/
theorem not_isRegPieceE_of_isKKCancel (P₀ : Params) (hm : P₀.m = 1) (he : P₀.e ≠ 0)
    (hKK : IsKKCancel P₀) (A : ℝ → ℝ) :
    ¬ IsRegPieceE (setCKerRe P₀ (uBD P₀)) A := by
  intro h
  exact not_uniform_setCKerRe_of_isKKCancel P₀ hm he hKK h.bound

end QED.ChainProof.SetCRegDisp

end
