/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLRegular
import QED.Polylog.ExtraIntegrals
import QED.Polylog.HPLLowWeight
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₅`: endpoint constants of HPL combinations

A finite linear combination of HPLs which has a finite limit at `1⁻) has that
limit equal to the sum of its shuffle-regularized constants. This allows a
moving-offset word to be compared with a candidate HPL expression by
differentiation, including when the candidate contains leading-one words.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL
open Polynomial

namespace QED.ThreeLoopD

/-- A finite HPL value is approached with an error of order `√(1-x)`. -/
theorem i15WV_abs_hpl_sub_one_le {w : List Letter} (hw : w.head? ≠ some .one) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ Ico (1 / 2 : ℝ) 1,
      |hpl w x - hpl w 1| ≤ K * (1 - x) ^ (1 / 2 : ℝ) := by
  cases w with
  | nil => exact ⟨0, le_rfl, fun _ _ => by simp⟩
  | cons a w =>
    have ha : a ≠ .one := by simpa using hw
    obtain ⟨C, hC, hc⟩ := abs_hpl_le_one_sub_rpow w (by norm_num : (0 : ℝ) < 1 / 2)
    refine ⟨4 * C, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith [hx.1]
    let g := fun t => a.kernel t * hpl w t
    have hbound (t : ℝ) (ht : t ∈ Ico (1 / 2 : ℝ) 1) :
        |g t| ≤ (2 * C) * (1 - t) ^ (-(1 / 2) : ℝ) := by
      unfold g
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (abs_kernel_le_two ha ht) (hc t ht) (abs_nonneg _) (by norm_num)
    have hy (y : ℝ) (hy : y ∈ Ioo x 1) : |hpl (a :: w) x - hpl (a :: w) y| ≤
        (4 * C) * (1 - x) ^ (1 / 2 : ℝ) := by
      have hsub (t : ℝ) (ht : t ∈ uIcc x y) : t ∈ Ioo (0 : ℝ) 1 := by
        rw [uIcc_of_le hy.1.le] at ht
        exact ⟨hx0.trans_le ht.1, ht.2.trans_lt hy.2⟩
      have hFTC : ∫ t in x..y, g t = hpl (a :: w) y - hpl (a :: w) x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_hpl_cons a w
          (hsub t ht)) (((continuousOn_kernel a).mul (continuousOn_hpl w)).mono
            hsub).intervalIntegrable
      have hpow : ContinuousOn (fun t => (1 - t) ^ (-(1 / 2) : ℝ)) (uIcc x y) :=
        (continuousOn_const.sub continuousOn_id).rpow_const
          (fun t ht => Or.inl (sub_pos.2 (hsub t ht).2).ne')
      have hMaj : IntervalIntegrable (fun t => (2 * C) * (1 - t) ^ (-(1 / 2) : ℝ)) volume x y :=
        (continuousOn_const.mul hpow).intervalIntegrable
      have hI := intervalIntegral.norm_integral_le_of_norm_le hy.1.le
        (ae_of_all _ fun t ht => by
          rw [Real.norm_eq_abs]
          exact hbound t ⟨hx.1.trans ht.1.le, ht.2.trans_lt hy.2⟩) hMaj
      rw [Real.norm_eq_abs, hFTC, abs_sub_comm (hpl (a :: w) y) (hpl (a :: w) x),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun t => t ^ (-(1 / 2) : ℝ)) 1,
        integral_rpow (Or.inl (by norm_num))] at hI
      refine hI.trans ?_
      have hpos : 0 ≤ (1 - y) ^ (1 / 2 : ℝ) := rpow_nonneg (sub_pos.2 hy.2).le _
      norm_num at *
      nlinarith [mul_nonneg hC hpos]
    exact le_of_tendsto ((tendsto_hpl_one ha w).const_sub (hpl (a :: w) x)).abs (by
      filter_upwards [Ioo_mem_nhdsLT hx.2] with y hy' using hy y hy')

private theorem tendsto_i15WV_log_pow_mul_error {w : List Letter} (hw : w.head? ≠ some .one)
    (n : ℕ) :
    Tendsto (fun x => hpl [Letter.one] x ^ n * (hpl w x - hpl w 1)) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := i15WV_abs_hpl_sub_one_le hw
  obtain ⟨C, hC, hlog⟩ := abs_log_pow_le n (δ := 1 / 4) (by norm_num)
  have hbound : ∀ᶠ x in 𝓝[<] (1 : ℝ), |hpl [Letter.one] x ^ n * (hpl w x - hpl w 1)| ≤
      (C * K) * (1 - x) ^ (1 / 4 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with x hx
    have hpos := sub_pos.2 hx.2
    have h1 := hlog (1 - x) ⟨hpos, by linarith [hx.1]⟩
    rw [hpl_one ⟨by linarith [hx.1], hx.2⟩, abs_mul, abs_pow, abs_neg]
    calc |log (1 - x)| ^ n * |hpl w x - hpl w 1|
        ≤ (C * (1 - x) ^ (-(1 / 4) : ℝ)) * (K * (1 - x) ^ (1 / 2 : ℝ)) :=
          mul_le_mul h1 (hb x ⟨hx.1.le, hx.2⟩) (abs_nonneg _) (by positivity)
      _ = (C * K) * (1 - x) ^ (1 / 4 : ℝ) := by
        rw [show C * (1 - x) ^ (-(1 / 4) : ℝ) * (K * (1 - x) ^ (1 / 2 : ℝ)) =
          C * K * ((1 - x) ^ (-(1 / 4) : ℝ) * (1 - x) ^ (1 / 2 : ℝ)) by ring,
          ← rpow_add hpos]
        norm_num
  have hl := ((continuousAt_const.sub continuousAt_id :
    ContinuousAt (fun x : ℝ => 1 - x) 1).rpow_const
      (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  have hr : Tendsto (fun x => C * K * (1 - x) ^ (1 / 4 : ℝ)) (𝓝[<] 1) (𝓝 0) := by
    simpa using hl.const_mul (C * K)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hr

private noncomputable def i15WVRegPoly (L : List (ℚ × ℕ × List Letter)) : Polynomial ℝ :=
  (L.map fun t => monomial t.2.1 ((t.1 : ℝ) * hpl t.2.2 1)).sum

private theorem i15WV_eval_regPoly (L : List (ℚ × ℕ × List Letter)) (x : ℝ) :
    (i15WVRegPoly L).eval x = evalExp x (hpl · 1) L := by
  induction L with
  | nil => simp [i15WVRegPoly, evalExp]
  | cons t L ih =>
    simp only [i15WVRegPoly, evalExp, List.map_cons, List.sum_cons, eval_add, eval_monomial] at *
    rw [ih]
    ring

private theorem tendsto_i15WV_reg_error (w : List Letter) :
    Tendsto (fun x => hpl w x - (i15WVRegPoly (regExpandWord w)).eval (hpl [.one] x))
      (𝓝[<] 1) (𝓝 0) := by
  let L := regExpandWord w
  have he : ∀ᶠ x in 𝓝[<] (1 : ℝ),
      hpl w x - (i15WVRegPoly L).eval (hpl [.one] x) =
        (L.map fun t => (t.1 : ℝ) *
          (hpl [.one] x ^ t.2.1 * (hpl t.2.2 x - hpl t.2.2 1))).sum := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    rw [hpl_eq_regExpand w hx, i15WV_eval_regPoly, show regExpandWord w = L from rfl]
    induction L with
    | nil => simp [evalExp]
    | cons t L ih =>
      simp only [evalExp, List.map_cons, List.sum_cons] at ih ⊢
      linarith only [ih, show (t.1 : ℝ) * hpl [Letter.one] x ^ t.2.1 * hpl t.2.2 x -
        (t.1 : ℝ) * hpl [Letter.one] x ^ t.2.1 * hpl t.2.2 1 =
          (t.1 : ℝ) * (hpl [Letter.one] x ^ t.2.1 * (hpl t.2.2 x - hpl t.2.2 1)) by ring]
  have hs := tendsto_list_sum (l := L) (x := 𝓝[<] (1 : ℝ))
    (f := fun t x => (t.1 : ℝ) * (hpl [.one] x ^ t.2.1 * (hpl t.2.2 x - hpl t.2.2 1)))
    (a := fun _ => (0 : ℝ)) fun t ht => by
      simpa only [mul_zero] using
        (tendsto_i15WV_log_pow_mul_error (head_ne_one_of_mem_regExpandWord w ht) t.2.1).const_mul
          (t.1 : ℝ)
  exact (by simpa using hs : Tendsto _ _ (𝓝 (0 : ℝ))).congr' (he.mono fun _ hx => hx.symm)

/-- A finite limit of a linear combination of HPLs equals its shuffle-regularized value. -/
theorem i15WV_eq_reg_of_tendsto (L : List (ℝ × List Letter)) {c : ℝ}
    (h : Tendsto (fun x => (L.map fun t => t.1 * hpl t.2 x).sum) (𝓝[<] 1) (𝓝 c)) :
    c = (L.map fun t => t.1 * hplReg t.2).sum := by
  let P := (L.map fun t => C t.1 * i15WVRegPoly (regExpandWord t.2)).sum
  have hP (z : ℝ) : P.eval z =
      (L.map fun t => t.1 * (i15WVRegPoly (regExpandWord t.2)).eval z).sum := by
    clear h
    induction L with
    | nil => simp [P]
    | cons t L ih => simp only [P, List.map_cons, List.sum_cons, eval_add, eval_mul, eval_C, ih]
  have he (x : ℝ) : (L.map fun t => t.1 * hpl t.2 x).sum - P.eval (hpl [.one] x) =
      (L.map fun t => t.1 *
        (hpl t.2 x - (i15WVRegPoly (regExpandWord t.2)).eval (hpl [.one] x))).sum := by
    rw [hP]
    clear h hP P
    induction L with
    | nil => simp
    | cons t L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring
  have herr : Tendsto (fun x => (L.map fun t => t.1 * hpl t.2 x).sum - P.eval (hpl [.one] x))
      (𝓝[<] 1) (𝓝 0) := by
    simp_rw [he]
    simpa using tendsto_list_sum (l := L) (x := 𝓝[<] (1 : ℝ))
      (a := fun _ => (0 : ℝ)) fun t _ => by
        simpa only [mul_zero] using (tendsto_i15WV_reg_error t.2).const_mul t.1
  have hlim : Tendsto (fun x => P.eval (hpl [.one] x)) (𝓝[<] 1) (𝓝 c) := by
    simpa using h.sub herr
  have hlog : Tendsto (hpl [Letter.one]) (𝓝[<] 1) atTop := by
    refine (tendsto_neg_atBot_atTop.comp
      (tendsto_log_nhdsGT_zero.comp tendsto_one_sub_nhdsLT_one)).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    exact (hpl_one hx).symm
  have hdeg : P.degree ≤ 0 := by
    by_contra! hn
    have hinf := (Polynomial.abs_tendsto_atTop P hn).comp hlog
    exact not_tendsto_nhds_of_tendsto_atTop hinf _ hlim.abs
  have hconst := Polynomial.eq_C_of_degree_le_zero hdeg
  have hlim' : Tendsto (fun _ : ℝ => P.eval 0) (𝓝[<] 1) (𝓝 c) := by
    refine hlim.congr' (Eventually.of_forall fun x => ?_)
    have hv (z : ℝ) : P.eval z = P.coeff 0 := by
      simpa only [eval_C] using congrArg (fun Q : Polynomial ℝ => Q.eval z) hconst
    rw [hv, hv]
  calc c = P.eval 0 := tendsto_nhds_unique hlim' tendsto_const_nhds
    _ = _ := by simp only [hP, i15WV_eval_regPoly, hplReg]

/-- Match a moving-offset word to an HPL primitive of its ratio derivative.
The derivative match implies the candidate has a finite limit, which fixes the constant. -/
theorem i15WV_eq_of_hasDerivAt_of_tendsto {F D : ℝ → ℝ} {c : ℝ}
    (L : List (ℝ × List Letter))
    (hF : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt F (D r) r)
    (hL : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => (L.map fun t => t.1 * hpl t.2 x).sum)
      (D r) r)
    (h0 : Tendsto F (𝓝[<] 1) (𝓝 c)) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    F r = c - (L.map fun t => t.1 * hplReg t.2).sum + (L.map fun t => t.1 * hpl t.2 r).sum := by
  let G : ℝ → ℝ := fun x => (L.map fun t => t.1 * hpl t.2 x).sum
  have hD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun y => G y - F y) 0 x := by
    change HasDerivAt (G - F) 0 x
    have h := (hL x hx).sub (hF x hx)
    rw [sub_self] at h
    exact h
  have hconst (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : G x - F x = G r - F r :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun x hx => (hD x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => by simpa using (hD x hx).deriv) hx hr
  have hlim : Tendsto G (𝓝[<] 1) (𝓝 (c + (G r - F r))) := by
    refine (h0.add_const (G r - F r)).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    linarith only [hconst x hx]
  linarith only [i15WV_eq_reg_of_tendsto L hlim]

/-- Prefixing the words of an HPL sum integrates the sum against the prefixed kernel. -/
theorem hasDerivAt_i15WV_hpl_prepend (L : List (ℝ × List Letter)) (b : Letter)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => (L.map fun t => t.1 * hpl (b :: t.2) x).sum)
      (b.kernel r * (L.map fun t => t.1 * hpl t.2 r).sum) r := by
  induction L with
  | nil => simpa using hasDerivAt_const r (0 : ℝ)
  | cons t L ih =>
    have h := ((hasDerivAt_hpl_cons b t.2 hr).const_mul t.1).add ih
    simp only [List.map_cons, List.sum_cons]
    refine h.congr_deriv ?_
    ring

end QED.ThreeLoopD
