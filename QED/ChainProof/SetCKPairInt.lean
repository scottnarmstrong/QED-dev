/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKPairFub
public import QED.ChainProof.SetCKPairBd
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Set (c), Stage K: integrability of the pair kernel, and the L pair density

Helper level (no frozen statement). From the pointwise bound on `σ_x(v)` (`abs_dispSig_le`), for
`0 < x < X < 1` and `t > 0` (`abs_pairKer_le`),

`|pairKer t x X| ≤ (15/c) (1 - x)^(-3/4) D(v) Q'(X)`, `v = Q(X) - Q(x)`, `c = (3/4) min(1, t)`,

`D(v) = 1/((1 + v)^(3/2)) + 1/(√v (1 + v))`. The dominating function has the explicit
antiderivative `2 arctan √v - 2/√(1 + v)` in `X`, so its `X`-integral over `(x, 1)` is `π + 2`, and
`(1 - x)^(-3/4)` is integrable. Hence the pair kernel is absolutely integrable on the node
triangle (`pairKerIntegrable`), and **`ρ_L` is the density of the L pair**
(`rhoL_isLPairDensity`).
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology MeasureTheory Function

/-- The `v`-profile of the dominating function. -/
noncomputable def pairDomV (v : ℝ) : ℝ := 1 / ((1 + v) * √(1 + v)) + 1 / (√v * (1 + v))

/-- Its antiderivative. -/
noncomputable def pairPhiV (v : ℝ) : ℝ := 2 * arctan √v - 2 / √(1 + v)

/-- The dominating function on the node triangle, without its `x`-weight. -/
noncomputable def pairDom (x X : ℝ) : ℝ := pairDomV (setCKQ X - setCKQ x) * setCKdQ X

/-- The `x`-weight `(1 - x)^(-3/4)` of the dominating function. -/
noncomputable def pairW (x : ℝ) : ℝ := (1 - x) ^ (-(3 / 4 : ℝ))

section

variable {t x X v : ℝ}

theorem hasDerivAt_pairPhiV (hv : 0 < v) : HasDerivAt pairPhiV (pairDomV v) v := by
  have hs : 0 < √v := sqrt_pos.2 hv
  have hw : 0 < √(1 + v) := sqrt_pos.2 (by linarith)
  have h1 := ((hasDerivAt_arctan (√v)).comp v (hasDerivAt_sqrt hv.ne')).const_mul 2
  have h2 := (((hasDerivAt_sqrt (by linarith : (1 + v) ≠ 0)).comp v
    ((hasDerivAt_id v).const_add 1)).inv hw.ne').const_mul 2
  refine (h1.sub h2).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · have e1 : √v ^ 2 = v := sq_sqrt hv.le
    have e2 : √(1 + v) ^ 2 = 1 + v := sq_sqrt (by linarith)
    simp only [Function.comp_def]
    unfold pairDomV
    rw [e1, e2]
    field_simp
    ring
  · exact Eventually.of_forall fun w => by simp only [pairPhiV, div_eq_mul_inv]; rfl

theorem tendsto_pairPhiV_zero : Tendsto pairPhiV (𝓝[>] 0) (𝓝 (-2)) := by
  have hc : ContinuousAt pairPhiV 0 := by
    unfold pairPhiV
    refine ((continuous_arctan.comp continuous_sqrt).const_mul 2).continuousAt.sub
      (continuousAt_const.div
        (continuous_sqrt.comp (continuous_const.add continuous_id)).continuousAt (by simp))
  have h0 : pairPhiV 0 = -2 := by simp [pairPhiV]
  rw [← h0]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_pairPhiV_atTop : Tendsto pairPhiV atTop (𝓝 π) := by
  have h1 : Tendsto (fun v => 2 * arctan √v) atTop (𝓝 (2 * (π / 2))) :=
    ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp tendsto_sqrt_atTop).const_mul 2
  have h2 : Tendsto (fun v : ℝ => 2 / √(1 + v)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left _ 1
      tendsto_id))
  have := h1.sub h2
  rw [show 2 * (π / 2) - 0 = π by ring] at this
  exact this

theorem pairDomV_pos (hv : 0 < v) : 0 < pairDomV v := by
  unfold pairDomV
  have : 0 < √v := sqrt_pos.2 hv
  have : 0 < √(1 + v) := sqrt_pos.2 (by linarith)
  positivity

theorem setCKdQ_pos (hX : X ∈ Ioo (0 : ℝ) 1) : 0 < setCKdQ X := by
  unfold setCKdQ
  have : 0 < 2 - X := by linarith [hX.2]
  have : 0 < 1 - X := by linarith [hX.2]
  have := hX.1
  positivity

/-- Integrability of a nonnegative derivative from the limits of a primitive at both ends. -/
theorem intervalIntegrable_deriv_of_nonneg_of_tendsto {f f' : ℝ → ℝ} {a b fa fb : ℝ}
    (hab : a < b) (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ f' x) (ha : Tendsto f (𝓝[>] a) (𝓝 fa))
    (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) : IntervalIntegrable f' volume a b := by
  set F : ℝ → ℝ := update (update f a fa) b fb
  have Fderiv : ∀ x ∈ Ioo a b, HasDerivAt F (f' x) x := by
    refine fun x hx => (hderiv x hx).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with _ hy
    unfold F
    rw [update_of_ne hy.2.ne, update_of_ne hy.1.ne']
  have hcont : ContinuousOn F (Icc a b) := by
    rw [continuousOn_update_iff, continuousOn_update_iff, Icc_sdiff_right, Ico_sdiff_left]
    refine ⟨⟨fun z hz => (hderiv z hz).continuousAt.continuousWithinAt, ?_⟩, ?_⟩
    · exact fun _ => ha.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
    · rintro -
      refine (hb.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhdsLT hab] with _ hz using (update_of_ne hz.1.ne' _ _).symm
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := F) ?_ ?_ ?_
  · rwa [uIcc_of_le hab.le]
  · rw [min_eq_left hab.le, max_eq_right hab.le]; exact Fderiv
  · rw [min_eq_left hab.le, max_eq_right hab.le]; exact hpos

/-- The `X`-integral of the dominating function over `(x, 1)`. -/
theorem pairDom_integral (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (pairDom x) volume x 1 ∧ ∫ X in x..1, pairDom x X = π + 2 := by
  have hv : ∀ X ∈ Ioo x 1, 0 < setCKQ X - setCKQ x := fun X hX =>
    sub_pos.2 (setCKQ_lt hx.1.le hX.1 hX.2)
  have hd : ∀ X ∈ Ioo x 1, HasDerivAt (fun X => pairPhiV (setCKQ X - setCKQ x)) (pairDom x X) X :=
    fun X hX => by
      have := (hasDerivAt_pairPhiV (hv X hX)).comp X
        ((hasDerivAt_setCKQ hX.2).sub_const (setCKQ x))
      exact this
  have hp : ∀ X ∈ Ioo x 1, 0 ≤ pairDom x X := fun X hX =>
    (mul_pos (pairDomV_pos (hv X hX)) (setCKdQ_pos ⟨hx.1.trans hX.1, hX.2⟩)).le
  have ha := tendsto_pairPhiV_zero.comp (tendsto_setCKQ_sub_right hx)
  have hb := tendsto_pairPhiV_atTop.comp (tendsto_setCKQ_sub_atTop x)
  have hI := intervalIntegrable_deriv_of_nonneg_of_tendsto hx.2 hd hp ha hb
  refine ⟨hI, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx.2 hd hI ha hb]
  ring

theorem integrableOn_pairW : IntegrableOn pairW (Ioo 0 1) := by
  show IntegrableOn (fun x : ℝ => (1 - x) ^ (-(3 / 4 : ℝ))) (Ioo 0 1)
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0)
    (r := -(3 / 4 : ℝ)) (by norm_num)).comp_sub_left 1
  simp only [sub_self, sub_zero] at h
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h

theorem pairW_eq (hx : x < 1) : pairW x = (1 - x)⁻¹ ^ ((1 : ℝ) / 4) * (√(1 - x))⁻¹ := by
  have h1 : 0 < 1 - x := by linarith
  unfold pairW
  rw [show -(3 / 4 : ℝ) = -(1 / 4) + -(1 / 2) by norm_num, rpow_add h1, rpow_neg h1.le,
    rpow_neg h1.le, ← sqrt_eq_rpow, ← inv_rpow h1.le]

/-- **The pointwise bound on the pair kernel.** -/
theorem abs_pairKer_le (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) (hxX : x < X) (hX : X < 1) :
    |pairKer t x X| ≤ 15 / (3 / 4 * min 1 t) * (pairW x * pairDom x X) := by
  set c := 3 / 4 * min 1 t with hc
  have hm0 : 0 < min 1 t := lt_min one_pos ht
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by have := min_le_left 1 t; rw [hc]; linarith
  clear_value c
  have h1 : 0 < 1 - x := by linarith [hx.2]
  set v := setCKQ X - setCKQ x with hvdef
  have hv : 0 < v := sub_pos.2 (setCKQ_lt hx.1.le hxX hX)
  set u := setCKQ x + t with hudef
  have hQX : setCKQ X + t = v + u := by rw [hvdef, hudef]; ring
  have hU : c ≤ (1 - x) * u := by
    have e : (1 - x) * u = x ^ 2 + (1 - x) * t := by
      rw [hudef]; unfold setCKQ; field_simp
    rw [e]
    have hm1 : min 1 t ≤ 1 := min_le_left _ _
    have hmt : min 1 t ≤ t := min_le_right _ _
    have : (1 - x) * min 1 t ≤ (1 - x) * t := mul_le_mul_of_nonneg_left hmt h1.le
    have : x ^ 2 * min 1 t ≤ x ^ 2 := by nlinarith
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hu0 : 0 ≤ u := by have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩; rw [hudef]; linarith
  have hu : c ≤ u := by nlinarith [hx.1]
  have hdQ : 0 < setCKdQ X := setCKdQ_pos ⟨hx.1.trans hxX, hX⟩
  -- the bound on `σ`
  have hσ := abs_dispSig_le hx hv
  set L := log (1 + x / (1 - x) / v) with hL
  set z := (1 - x)⁻¹ ^ ((1 : ℝ) / 4) with hz
  set q := √v with hq
  have hq0 : 0 < q := sqrt_pos.2 hv
  have hz1 : 1 ≤ z := one_le_rpow (by rw [← one_div, le_div_iff₀ h1]; linarith [hx.1])
    (by norm_num)
  clear_value z q
  have hLb : 1 + L ≤ 5 * z * (1 + 1 / q) := by
    have e1 : 1 + x / (1 - x) / v ≤ (1 + 1 / v) * (1 - x)⁻¹ := by
      have : (1 + 1 / v) * (1 - x)⁻¹ - (1 + x / (1 - x) / v) =
          (x * v + (1 - x)) / ((1 - x) * v) := by field_simp; ring
      have : 0 ≤ (x * v + (1 - x)) / ((1 - x) * v) :=
        div_nonneg (by nlinarith [hx.1]) (mul_pos h1 hv).le
      linarith
    have e2 : L ≤ log (1 + 1 / v) + log (1 - x)⁻¹ := by
      have : 0 < x / (1 - x) / v := div_pos (div_pos hx.1 h1) hv
      rw [← log_mul (by positivity) (inv_pos.2 h1).ne']
      exact log_le_log (by linarith) e1
    have e3 : log (1 + 1 / v) ≤ 2 * (1 / q) := by
      have : 1 + 1 / v = 1 + (1 / q) ^ 2 := by rw [div_pow, one_pow, hq, sq_sqrt hv.le]
      rw [this]
      have hq' : 0 ≤ 1 / q := by positivity
      calc log (1 + (1 / q) ^ 2) ≤ log ((1 + 1 / q) ^ 2) :=
            log_le_log (by positivity) (by nlinarith [hq'])
        _ = 2 * log (1 + 1 / q) := by rw [log_pow]; norm_num
        _ ≤ 2 * (1 / q) := by
            have := log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / q); linarith
    have e4 : log (1 - x)⁻¹ ≤ 4 * z := by
      have := log_le_rpow_div (by positivity : (0 : ℝ) ≤ (1 - x)⁻¹)
        (by norm_num : (0 : ℝ) < 1 / 4)
      rw [hz]; linarith
    have : 0 ≤ 1 / q := by positivity
    nlinarith
  set s := √(1 - x) with hs
  set w := √(1 + v) with hw
  have hs0 : 0 < s := sqrt_pos.2 h1
  have hw0 : 0 < w := sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = 1 - x := sq_sqrt h1.le
  have hw2 : w ^ 2 = 1 + v := sq_sqrt (by linarith)
  have hw1 : 1 ≤ w := by rw [hw]; exact one_le_sqrt.2 (by linarith)
  clear_value s w
  have hvu : c * w ≤ s * (v + u) := by
    have key : c ^ 2 * (1 + v) ≤ (1 - x) * (v + u) ^ 2 := by
      have a1 : (1 - x) * (v + u) ^ 2 ≥ (1 - x) * u * (u + v) := by
        have : 0 ≤ (1 - x) * v * (u + v) := mul_nonneg (mul_nonneg h1.le hv.le) (by linarith)
        have e : (1 - x) * (v + u) ^ 2 - (1 - x) * u * (u + v) = (1 - x) * v * (u + v) := by
          ring
        linarith
      have a2 : (1 - x) * u * (u + v) ≥ c * (u + v) :=
        mul_le_mul_of_nonneg_right hU (by linarith)
      have a3 : c * (u + v) ≥ c ^ 2 * (1 + v) := by
        have b1 := mul_nonneg hc0.le (sub_nonneg.2 hu)
        have b2 := mul_nonneg (mul_nonneg hc0.le hv.le) (sub_nonneg.2 hc1)
        have e : c * (u + v) - c ^ 2 * (1 + v) = c * (u - c) + c * v * (1 - c) := by ring
        linarith
      linarith
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
    have k1 : (c * w) ^ 2 = c ^ 2 * (1 + v) := by rw [mul_pow, hw2]
    have k2 : (s * (v + u)) ^ 2 = (1 - x) * (v + u) ^ 2 := by rw [mul_pow, hs2]
    rw [k1, k2]
    exact key
  have hσ' : |dispSig x v| ≤ 15 * z * (1 + 1 / q) / (s ^ 2 * (1 + v)) := by
    rw [le_div_iff₀ (by positivity), hs2]
    linarith
  have hinv : 1 / (v + u) ≤ s / (c * w) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    linarith
  have hD : (1 + 1 / q) / ((1 + v) * w) ≤ pairDomV v := by
    unfold pairDomV
    rw [← hq, ← hw]
    have : 1 / q / ((1 + v) * w) ≤ 1 / (q * (1 + v)) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hq0 (by linarith : (0 : ℝ) < 1 + v)]
    calc (1 + 1 / q) / ((1 + v) * w) = 1 / ((1 + v) * w) + 1 / q / ((1 + v) * w) := by ring
      _ ≤ _ := by linarith
  have hW : pairW x = z / s := by rw [pairW_eq hx.2, ← hz, ← hs, div_eq_mul_inv]
  unfold pairKer
  rw [hQX, abs_mul, abs_of_pos (by positivity : 0 < setCKdQ X / (v + u))]
  unfold pairDom
  rw [← hvdef, hW]
  calc |dispSig x v| * (setCKdQ X / (v + u)) = |dispSig x v| * (1 / (v + u)) * setCKdQ X := by
        ring
    _ ≤ 15 * z * (1 + 1 / q) / (s ^ 2 * (1 + v)) * (s / (c * w)) * setCKdQ X := by gcongr
    _ = 15 / c * (z / s * ((1 + 1 / q) / ((1 + v) * w))) * setCKdQ X := by
        field_simp
    _ ≤ 15 / c * (z / s * pairDomV v) * setCKdQ X := by gcongr
    _ = 15 / c * (z / s * (pairDomV v * setCKdQ X)) := by ring


theorem measurable_setCKQ : Measurable setCKQ := by unfold setCKQ; fun_prop

section

variable {f g : ℝ × ℝ → ℝ}

theorem measurable_pairAl_comp (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => pairAl (f p) (-(g p)) := by
  unfold pairAl; fun_prop

theorem measurable_pairBe_comp (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => pairBe (f p) (-(g p)) := by
  unfold pairBe; fun_prop

theorem measurable_pairGa_comp (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => pairGa (f p) (-(g p)) := by
  unfold pairGa; fun_prop

theorem measurable_dispSig_comp (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => dispSig (f p) (g p) := by
  have hB : Measurable fun p => if f p < g p then pairBe (f p) (-(g p)) else 0 :=
    Measurable.ite (measurableSet_lt hf hg) (measurable_pairBe_comp hf hg) measurable_const
  have hL : Measurable fun p => log (1 + f p / (1 - f p) / g p) := by fun_prop
  unfold dispSig
  exact (((measurable_pairAl_comp hf hg).add hB).add ((measurable_pairGa_comp hf hg).mul hL)).neg

end

theorem measurable_pairKerT (t : ℝ) : Measurable (pairKerT t) := by
  have hQ := measurable_setCKQ
  have h1 : Measurable fun p : ℝ × ℝ => dispSig p.1 (setCKQ p.2 - setCKQ p.1) :=
    measurable_dispSig_comp measurable_fst ((hQ.comp measurable_snd).sub (hQ.comp measurable_fst))
  have h2 : Measurable fun p : ℝ × ℝ => setCKdQ p.2 / (setCKQ p.2 + t) := by
    unfold setCKdQ; fun_prop
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) (h1.mul h2)
    measurable_const

/-- The dominating function on the node triangle. -/
noncomputable def pairDomT (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then 15 / (3 / 4 * min 1 t) * (pairW p.1 * pairDom p.1 p.2) else 0

theorem measurable_pairDomT (t : ℝ) : Measurable (pairDomT t) := by
  have hQ := measurable_setCKQ
  have hk : Measurable fun p : ℝ × ℝ =>
      15 / (3 / 4 * min 1 t) * (pairW p.1 * pairDom p.1 p.2) := by
    unfold pairW pairDom pairDomV setCKdQ
    have hv : Measurable fun p : ℝ × ℝ => setCKQ p.2 - setCKQ p.1 :=
      (hQ.comp measurable_snd).sub (hQ.comp measurable_fst)
    fun_prop
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) hk measurable_const

theorem integrable_pairDomT (ht : 0 < t) :
    Integrable (pairDomT t)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set K := 15 / (3 / 4 * min 1 t)
  have hsec : ∀ x, (fun X => pairDomT t (x, X)) =
      (Ioi x).indicator (fun X => K * (pairW x * pairDom x X)) := fun x => by
    funext X; simp only [pairDomT, indicator, mem_Ioi]; rfl
  rw [integrable_prod_iff (measurable_pairDomT t).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hsec, integrable_indicator_iff measurableSet_Ioi, IntegrableOn, restrict_Ioi_Ioo hx]
    have := (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).1 (pairDom_integral hx).1
    exact (this.const_mul (pairW x)).const_mul K
  · have hW : Integrable (fun x => K * pairW x * (π + 2)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
      (integrableOn_pairW.const_mul K).mul_const _
    refine hW.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hn : ∀ X, ‖pairDomT t (x, X)‖ =
        (Ioi x).indicator (fun X => ‖K * (pairW x * pairDom x X)‖) X := fun X => by
      rw [congrFun (hsec x) X, norm_indicator_eq_indicator_norm]
    simp only [hn]
    rw [integral_indicator measurableSet_Ioi, restrict_Ioi_Ioo hx]
    have hK : 0 ≤ K := by have := lt_min one_pos ht; positivity
    have hWx : 0 ≤ pairW x := rpow_nonneg (by linarith [hx.2]) _
    have e : ∫ X in Ioo x 1, ‖K * (pairW x * pairDom x X)‖ =
        ∫ X in Ioo x 1, K * pairW x * pairDom x X := by
      refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
      have hv : 0 < setCKQ X - setCKQ x := sub_pos.2 (setCKQ_lt hx.1.le hX.1 hX.2)
      have : 0 ≤ pairDom x X :=
        (mul_pos (pairDomV_pos hv) (setCKdQ_pos ⟨hx.1.trans hX.1, hX.2⟩)).le
      rw [Real.norm_of_nonneg (by positivity)]
      ring
    rw [e, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hx.2.le, (pairDom_integral hx).2]

/-- **The Fubini hypothesis holds**: the pair kernel is absolutely integrable on the triangle. -/
theorem pairKerIntegrable (ht : 0 < t) : PairKerIntegrable t := by
  refine Integrable.mono' (integrable_pairDomT ht) (measurable_pairKerT t).aestronglyMeasurable ?_
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
  refine Eventually.of_forall fun p hp => ?_
  rw [Real.norm_eq_abs]
  unfold pairKerT pairDomT
  split_ifs with h
  · exact abs_pairKer_le ht hp.1 h hp.2.2
  · simp

/-- **The pilot (S_L)**: `ρ_L` is the fibre density of the L pair. -/
theorem rhoL_isLPairDensity : IsLPairDensity rhoL :=
  isLPairDensity_rhoL_of_pairKerIntegrable fun _ ht => pairKerIntegrable ht

end

end QED.ChainProof.SetCK
