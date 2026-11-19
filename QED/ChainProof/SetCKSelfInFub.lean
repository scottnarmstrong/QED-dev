/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKSelfInRho
public import QED.ChainProof.SetCKPairInt

/-!
# Set (c), Stage K, group G1: the Stieltjes identity for `S(t, 0)`

Helper level (no frozen statement). The discontinuity of the G1 per-node function is bounded,
`|σ_x(v)| ≤ 3/(1 + v)` for `0 < x < 1`, `v > 0` (`abs_selfInSig_le`). Since
`Q(X) + t ≥ min(1, t) (1 + v)` for `v = Q(X) - Q(x)`, the G1 kernel is dominated on the node
triangle `0 < x < X < 1` by `(3/min(1, t)) Q'(X)/(1 + Q(X) - Q(x))²`, whose `X`-integral over
`(x, 1)` is `1` (`abs_selfInKer_le`, `selfInDom_integral`). Fubini's theorem on the triangle,
the per-node dispersion relation (`integral_selfInKer`), the inner node integral
(`integral_selfInSig_X`) and the density identity (`rhoSelfIn_mul_setCKQ`) give

**`rhoSelfIn_isSelfInDensity`**: `S(t, 0) = ∫₀¹ ρ_S(X) Q(X)/(Q(X) + t) dX` for every `t > 0`.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology MeasureTheory Function QED.TwoLoop.UnitLLink

/-- The G1 kernel on the node triangle `0 < x < X < 1`, extended by zero. -/
noncomputable def selfInKerT (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then selfInKer t p.1 p.2 else 0

/-- The dominating function `Q'(X)/(1 + Q(X) - Q(x))²` of the G1 kernel. -/
noncomputable def selfInDom (x X : ℝ) : ℝ := setCKdQ X / (1 + (setCKQ X - setCKQ x)) ^ 2

section

variable {t x X v : ℝ}

theorem abs_selfInSigA_le (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) (hvx : v ≤ x) :
    |selfInSigA x v| ≤ 13 / 12 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hxx : 0 < 12 * x ^ 2 := by positivity
  unfold selfInSigA
  rw [abs_div, abs_neg, abs_of_pos hxx, div_le_iff₀ hxx, abs_le]
  constructor <;> nlinarith [mul_pos hv hx0, mul_le_mul_of_nonneg_left hvx hv.le,
    mul_pos (mul_pos hv hv) (sub_pos.2 hx1), mul_le_mul_of_nonneg_left hvx (sq_nonneg x),
    mul_pos hx0 hx0, pow_pos hx0 3]

theorem abs_selfInSigB_mul_le (hx : x ∈ Ioo (0 : ℝ) 1) (hxv : x < v) :
    |selfInSigB x v| * (1 + v) ≤ 3 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hv : 0 < v := hx0.trans hxv
  have hv2 : 0 < 12 * v ^ 2 := by positivity
  have e : selfInSigB x v = (x ^ 2 * (x + 1) - 2 * x * (2 * x + 1) * v) / (12 * v ^ 2) := by
    unfold selfInSigB
    field_simp
    ring
  have h1 : 0 ≤ 1 + v := by linarith
  rw [e, abs_div, abs_of_pos hv2, div_mul_eq_mul_div, div_le_iff₀ hv2]
  have hxv' : x ^ 2 ≤ v ^ 2 := by nlinarith
  have hb : |x ^ 2 * (x + 1) - 2 * x * (2 * x + 1) * v| ≤
      x ^ 2 * (x + 1) + 2 * x * (2 * x + 1) * v := by
    rw [abs_le]
    constructor <;> nlinarith [mul_pos (mul_pos hx0 hx0) hv, mul_pos hx0 hv, pow_pos hx0 3]
  calc |x ^ 2 * (x + 1) - 2 * x * (2 * x + 1) * v| * (1 + v)
      ≤ (x ^ 2 * (x + 1) + 2 * x * (2 * x + 1) * v) * (1 + v) := by gcongr
    _ ≤ 3 * (12 * v ^ 2) := by
      nlinarith [mul_pos hx0 hv, mul_pos (mul_pos hx0 hv) hv, mul_pos (mul_pos hx0 hx0) hv,
        mul_lt_mul_of_pos_right hxv hv, mul_lt_mul_of_pos_right hx1 hv,
        mul_lt_mul_of_pos_right hx1 (mul_pos hv hv), mul_lt_mul_of_pos_right hxv (mul_pos hv hv),
        mul_lt_mul_of_pos_right hx1 hx0]

/-- **The bound on the discontinuity**: `|σ_x(v)| ≤ 3/(1 + v)`. -/
theorem abs_selfInSig_le (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    |selfInSig x v| ≤ 3 / (1 + v) := by
  have h1 : 0 < 1 + v := by linarith
  rw [le_div_iff₀ h1]
  unfold selfInSig
  split_ifs with h
  · exact abs_selfInSigB_mul_le hx h
  · have hA := abs_selfInSigA_le hx hv (not_lt.1 h)
    have : 1 + v ≤ 2 := by linarith [hx.2, not_lt.1 h]
    nlinarith [abs_nonneg (selfInSigA x v)]

/-- **The pointwise bound on the G1 kernel.** -/
theorem abs_selfInKer_le (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) (hxX : x < X) (hX : X < 1) :
    |selfInKer t x X| ≤ 3 / min 1 t * selfInDom x X := by
  set m := min 1 t with hm
  have hm0 : 0 < m := lt_min one_pos ht
  have hm1 : m ≤ 1 := min_le_left 1 t
  have hmt : m ≤ t := min_le_right 1 t
  clear_value m
  set v := setCKQ X - setCKQ x with hvdef
  have hv : 0 < v := sub_pos.2 (setCKQ_lt hx.1.le hxX hX)
  have hQx : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hd : 0 < setCKdQ X := setCKdQ_pos ⟨hx.1.trans hxX, hX⟩
  have hQX : setCKQ X + t = v + setCKQ x + t := by rw [hvdef]; ring
  have hlow : m * (1 + v) ≤ setCKQ X + t := by
    rw [hQX]; nlinarith
  have hpos : 0 < m * (1 + v) := by positivity
  have hS := abs_selfInSig_le hx hv
  unfold selfInKer selfInDom
  rw [← hvdef, abs_mul, abs_of_pos (div_pos hd (by linarith))]
  have hnn : 0 ≤ setCKdQ X / (setCKQ X + t) := (div_pos hd (by linarith)).le
  calc |selfInSig x v| * (setCKdQ X / (setCKQ X + t))
      ≤ 3 / (1 + v) * (setCKdQ X / (m * (1 + v))) :=
        mul_le_mul hS (div_le_div_of_nonneg_left hd.le hpos hlow) hnn (by positivity)
    _ = 3 / m * (setCKdQ X / (1 + v) ^ 2) := by
        field_simp

/-- The `X`-integral of the dominating function over `(x, 1)` is `1`. -/
theorem selfInDom_integral (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (selfInDom x) volume x 1 ∧ ∫ X in x..1, selfInDom x X = 1 := by
  have hv : ∀ X ∈ Ioo x 1, 0 < setCKQ X - setCKQ x := fun X hX =>
    sub_pos.2 (setCKQ_lt hx.1.le hX.1 hX.2)
  have hd : ∀ X ∈ Ioo x 1,
      HasDerivAt (fun X => -(1 + (setCKQ X - setCKQ x))⁻¹) (selfInDom x X) X := fun X hX => by
    have h1 : 1 + (setCKQ X - setCKQ x) ≠ 0 := by linarith [hv X hX]
    have := (((hasDerivAt_setCKQ hX.2).sub_const (setCKQ x)).const_add 1).inv h1
    convert this.neg using 1
    unfold selfInDom
    ring
  have hp : ∀ X ∈ Ioo x 1, 0 ≤ selfInDom x X := fun X hX =>
    div_nonneg (setCKdQ_pos ⟨hx.1.trans hX.1, hX.2⟩).le (sq_nonneg _)
  have hc : ContinuousAt (fun v : ℝ => -(1 + v)⁻¹) 0 := by
    have : (1 + (0 : ℝ)) ≠ 0 := by norm_num
    exact ((continuousAt_const.add continuousAt_id).inv₀ this).neg
  have ha : Tendsto (fun X => -(1 + (setCKQ X - setCKQ x))⁻¹) (𝓝[>] x) (𝓝 (-(1 + 0)⁻¹)) :=
    (hc.tendsto.mono_left nhdsWithin_le_nhds).comp (tendsto_setCKQ_sub_right hx)
  have hb : Tendsto (fun X => -(1 + (setCKQ X - setCKQ x))⁻¹) (𝓝[<] 1) (𝓝 (-0)) :=
    (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1
      (tendsto_setCKQ_sub_atTop x))).neg
  have hI := intervalIntegrable_deriv_of_nonneg_of_tendsto hx.2 hd hp ha hb
  refine ⟨hI, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx.2 hd hI ha hb]
  norm_num

theorem measurable_selfInSig_comp {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => selfInSig (f p) (g p) := by
  unfold selfInSig selfInSigA selfInSigB
  exact Measurable.ite (measurableSet_lt hf hg) (by fun_prop) (by fun_prop)

theorem measurable_selfInKerT (t : ℝ) : Measurable (selfInKerT t) := by
  have hQ := measurable_setCKQ
  have h1 : Measurable fun p : ℝ × ℝ => selfInSig p.1 (setCKQ p.2 - setCKQ p.1) :=
    measurable_selfInSig_comp measurable_fst
      ((hQ.comp measurable_snd).sub (hQ.comp measurable_fst))
  have h2 : Measurable fun p : ℝ × ℝ => setCKdQ p.2 / (setCKQ p.2 + t) := by
    unfold setCKdQ; fun_prop
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) (h1.mul h2)
    measurable_const

/-- The dominating function on the node triangle. -/
noncomputable def selfInDomT (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then 3 / min 1 t * selfInDom p.1 p.2 else 0

theorem measurable_selfInDomT (t : ℝ) : Measurable (selfInDomT t) := by
  have hQ := measurable_setCKQ
  have hk : Measurable fun p : ℝ × ℝ => 3 / min 1 t * selfInDom p.1 p.2 := by
    unfold selfInDom setCKdQ
    have hv : Measurable fun p : ℝ × ℝ => setCKQ p.2 - setCKQ p.1 :=
      (hQ.comp measurable_snd).sub (hQ.comp measurable_fst)
    fun_prop
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) hk measurable_const

theorem integrable_selfInDomT (ht : 0 < t) :
    Integrable (selfInDomT t)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set K := 3 / min 1 t
  have hK : 0 ≤ K := by have := lt_min one_pos ht; positivity
  have hsec : ∀ x, (fun X => selfInDomT t (x, X)) =
      (Ioi x).indicator (fun X => K * selfInDom x X) := fun x => by
    funext X; simp only [selfInDomT, indicator, mem_Ioi]; rfl
  rw [integrable_prod_iff (measurable_selfInDomT t).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hsec, integrable_indicator_iff measurableSet_Ioi, IntegrableOn, restrict_Ioi_Ioo hx]
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).1
      (selfInDom_integral hx).1).const_mul K
  · have hW : Integrable (fun _ : ℝ => K) (volume.restrict (Ioo (0 : ℝ) 1)) :=
      integrable_const K
    refine hW.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hn : ∀ X, ‖selfInDomT t (x, X)‖ =
        (Ioi x).indicator (fun X => ‖K * selfInDom x X‖) X := fun X => by
      rw [congrFun (hsec x) X, norm_indicator_eq_indicator_norm]
    simp only [hn]
    rw [integral_indicator measurableSet_Ioi, restrict_Ioi_Ioo hx]
    have e : ∫ X in Ioo x 1, ‖K * selfInDom x X‖ = ∫ X in Ioo x 1, K * selfInDom x X := by
      refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
      have : 0 ≤ selfInDom x X :=
        div_nonneg (setCKdQ_pos ⟨hx.1.trans hX.1, hX.2⟩).le (sq_nonneg _)
      rw [Real.norm_of_nonneg (by positivity)]
    rw [e, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hx.2.le, (selfInDom_integral hx).2, mul_one]

/-- **The Fubini hypothesis for G1**: the kernel is absolutely integrable on the triangle. -/
theorem integrable_selfInKerT (ht : 0 < t) :
    Integrable (selfInKerT t)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  refine Integrable.mono' (integrable_selfInDomT ht) (measurable_selfInKerT t).aestronglyMeasurable
    ?_
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
  refine Eventually.of_forall fun p hp => ?_
  rw [Real.norm_eq_abs]
  unfold selfInKerT selfInDomT
  split_ifs with h
  · exact abs_selfInKer_le ht hp.1 h hp.2.2
  · simp

/-- An `x`-section of the triangle kernel: the per-node dispersion integral. -/
theorem integral_selfInKerT_x (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hint : Integrable (fun X => selfInKerT t (x, X)) (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∫ X, selfInKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
      selfInF x (setCKQ x + t) - selfInE1 x / (setCKQ x + t) := by
  have he : (fun X => selfInKerT t (x, X)) = (Ioi x).indicator (selfInKer t x) := by
    funext X; simp only [selfInKerT, indicator, mem_Ioi]
  rw [he] at hint ⊢
  rw [integral_indicator measurableSet_Ioi, restrict_Ioi_Ioo hx]
  rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn, restrict_Ioi_Ioo hx] at hint
  have hii : IntervalIntegrable (selfInKer t x) volume x 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).2 hint
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.2.le,
    integral_selfInKer hx ht hii]

/-- The inner node integral `S(X)` in closed form. -/
noncomputable def selfInS (X : ℝ) : ℝ :=
  (selfInIB X (pairY1 X) - selfInIB X 0) + (selfInIA X X - selfInIA X (pairY1 X))

/-- An `X`-section of the triangle kernel: the inner node integral. -/
theorem integral_selfInKerT_X (ht : 0 < t) (hX : X ∈ Ioo (0 : ℝ) 1)
    (hint : Integrable (fun x => selfInKerT t (x, X)) (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∫ x, selfInKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
      selfInS X * (setCKdQ X / (setCKQ X + t)) := by
  have he : (fun x => selfInKerT t (x, X)) = (Iio X).indicator (fun x => selfInKer t x X) := by
    funext x; simp only [selfInKerT, indicator, mem_Iio]
  rw [he] at hint ⊢
  rw [integral_indicator measurableSet_Iio, restrict_Iio_Ioo hX]
  rw [integrable_indicator_iff measurableSet_Iio, IntegrableOn, restrict_Iio_Ioo hX] at hint
  have hQ : 0 ≤ setCKQ X := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
  have hc : setCKdQ X / (setCKQ X + t) ≠ 0 :=
    (div_pos (setCKdQ_pos hX) (by linarith)).ne'
  simp only [selfInKer] at hint ⊢
  have hs : IntegrableOn (fun x => selfInSig x (setCKQ X - setCKQ x)) (Ioo 0 X) := by
    have := hint.mul_const (setCKdQ X / (setCKQ X + t))⁻¹
    have e : (fun x => selfInSig x (setCKQ X - setCKQ x) * (setCKdQ X / (setCKQ X + t)) *
        (setCKdQ X / (setCKQ X + t))⁻¹) = fun x => selfInSig x (setCKQ X - setCKQ x) := by
      funext x; rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
    rw [e] at this
    exact this
  have hii : IntervalIntegrable (fun x => selfInSig x (setCKQ X - setCKQ x)) volume 0 X :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hX.1.le).2 hs
  rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hX.1.le, integral_selfInSig_X hX hii]
  rfl

theorem integrableOn_selfInE1 (ht : 0 < t) :
    IntegrableOn (fun x => selfInE1 x / (setCKQ x + t)) (Ioo 0 1) := by
  have hc : ContinuousOn (fun x : ℝ => -(x * (x + 1)) / 2 * (1 - x) / (x ^ 2 + (1 - x) * t))
      (Icc 0 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (pos_denom ht hx).ne'
  refine (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun (fun x hx => ?_)
    measurableSet_Ioo
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hd := (pos_denom ht (Ioo_subset_Icc_self hx)).ne'
  unfold selfInE1
  rw [show setCKQ x + t = (x ^ 2 + (1 - x) * t) / (1 - x) by unfold setCKQ; field_simp]
  field_simp

/-- The node integral of the per-node function, by Fubini on the node triangle. -/
theorem integral_selfInF (ht : 0 < t) :
    2 * ∫ x in Ioo (0 : ℝ) 1, selfInF x (setCKQ x + t) =
      ∫ X in Ioo (0 : ℝ) 1, rhoSelfIn X * (setCKQ X / (setCKQ X + t)) := by
  have H := integrable_selfInKerT ht
  have hg := H.integral_prod_left
  have hh := H.integral_prod_right
  have hE := integrableOn_selfInE1 ht
  have e1 : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), selfInF x (setCKQ x + t) =
      selfInE1 x / (setCKQ x + t) +
        ∫ X, selfInKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, H.prod_right_ae] with x hx hs
    rw [integral_selfInKerT_x ht hx hs]
    ring
  have e2 : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ x, selfInKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
        selfInS X * (setCKdQ X / (setCKQ X + t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, H.prod_left_ae] with X hX hs
    exact integral_selfInKerT_X ht hX hs
  have hswap := integral_integral_swap (f := fun x X => selfInKerT t (x, X)) H
  rw [integral_congr_ae e1, integral_add hE hg, hswap, integral_congr_ae e2,
    ← integral_add hE (hh.congr e2), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun X hX => ?_
  have h := rhoSelfIn_mul_setCKQ hX
  have hu : setCKQ X + t ≠ 0 := by
    have := setCKQ_nonneg (Ioo_subset_Icc_self hX); linarith
  unfold selfInS
  field_simp
  linear_combination -h

/-- **G1 (Stage K)**: `ρ_S` is the Stieltjes density of the inner-massive self-energy unit,
`S(t, 0) = ∫₀¹ ρ_S(X) Q(X)/(Q(X) + t) dX` for every `t > 0`. -/
theorem rhoSelfIn_isSelfInDensity : IsSelfInDensity rhoSelfIn := fun t ht => by
  rw [selfIn_eq ht, ← setIntegral_Ioo_eq_intervalIntegral, integral_selfInF ht,
    setIntegral_Ioo_eq_intervalIntegral]
  rfl

end

end QED.ChainProof.SetCK

end
