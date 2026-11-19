/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKSelfIn

/-!
# Set (c), Stage K, group G1: the per-node dispersion relation

Helper level (no frozen statement). For `x ∈ (0, 1)` the per-node function `F(x, u)` of the
inner-massive self-energy unit (`selfInF`) is analytic in `u` off `(-∞, 0]` with a simple pole at
`u = 0` and decays like `log u/u`; its discontinuity is **rational**:

`F(x, u) = e₁(x)/u + ∫₀^∞ σ_x(v)/(v + u) dv`, `e₁(x) = -x(x+1)/2`,

`σ_x(v) = -(v²(x-1) - 4 v x² + 2 v x + 6 x³)/(12 x²)` for `v ≤ x` (from `log u`) and
`σ_x(v) = x²(x+1)/(12 v²) - x(2x+1)/(6 v)` for `v > x` (from `log u` and `log(u + x)`).

This file proves it in the outer node variable `X`, `v = Q(X) - Q(x)`, `v + u = Q(X) + t` for
`u = Q(x) + t` (`integral_selfInKer`), with the explicit `v`-antiderivatives `selfInPsiA`
(`v < x`) and `selfInPsiB` (`v > x`, vanishing at `v = ∞`), split at the node `ξ(x)` of
`SetCKPairX` (`Q(ξ) - Q(x) = x`).
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology MeasureTheory

/-- `σ_x(v)` for `v ≤ x`. -/
noncomputable def selfInSigA (x v : ℝ) : ℝ :=
  -(v ^ 2 * (x - 1) - 4 * v * x ^ 2 + 2 * v * x + 6 * x ^ 3) / (12 * x ^ 2)

/-- `σ_x(v)` for `v > x`. -/
noncomputable def selfInSigB (x v : ℝ) : ℝ :=
  x ^ 2 * (x + 1) / (12 * v ^ 2) - x * (2 * x + 1) / (6 * v)

/-- **The discontinuity** `σ_x(v)` of the per-node function. -/
noncomputable def selfInSig (x v : ℝ) : ℝ := if x < v then selfInSigB x v else selfInSigA x v

/-- The residue `e₁(x) = -x(x+1)/2` of the per-node function at `u = 0`. -/
noncomputable def selfInE1 (x : ℝ) : ℝ := -(x * (x + 1)) / 2

/-- **The G1 kernel** in the node variables: `σ_x(Q(X) - Q(x)) Q'(X)/(Q(X) + t)`. -/
noncomputable def selfInKer (t x X : ℝ) : ℝ :=
  selfInSig x (setCKQ X - setCKQ x) * (setCKdQ X / (setCKQ X + t))

/-- The `v`-antiderivative of `σ_x(v)/(v + u)` for `v ≤ x`. -/
noncomputable def selfInPsiA (x u v : ℝ) : ℝ :=
  (1 - x) / (12 * x ^ 2) * v ^ 2 / 2 + ((2 * x - 1) / (6 * x) - (1 - x) / (12 * x ^ 2) * u) * v +
    (-x / 2 - (2 * x - 1) / (6 * x) * u + (1 - x) / (12 * x ^ 2) * u ^ 2) * log (v + u)

/-- The `v`-antiderivative of `σ_x(v)/(v + u)` for `v > x`, vanishing at `v = ∞`. -/
noncomputable def selfInPsiB (x u v : ℝ) : ℝ :=
  (-(x * (2 * x + 1)) / 6 / u - x ^ 2 * (x + 1) / 12 / u ^ 2) * (log v - log (v + u)) -
    x ^ 2 * (x + 1) / 12 / (u * v)

section

variable {x t u v X : ℝ}

theorem hasDerivAt_selfInPsiA (hx : x ≠ 0) (hvu : 0 < v + u) :
    HasDerivAt (selfInPsiA x u) (selfInSigA x v / (v + u)) v := by
  have hl : HasDerivAt (fun v => log (v + u)) (1 / (v + u)) v := by
    simpa using ((hasDerivAt_id' v).add_const u).log hvu.ne'
  have h := ((((hasDerivAt_pow 2 v).const_mul ((1 - x) / (12 * x ^ 2))).div_const 2).add
    ((hasDerivAt_id' v).const_mul ((2 * x - 1) / (6 * x) - (1 - x) / (12 * x ^ 2) * u))).add
    (hl.const_mul (-x / 2 - (2 * x - 1) / (6 * x) * u + (1 - x) / (12 * x ^ 2) * u ^ 2))
  convert h using 1
  · funext w
    rfl
  · unfold selfInSigA
    have := hvu.ne'
    field_simp
    ring

theorem hasDerivAt_selfInPsiB (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (selfInPsiB x u) (selfInSigB x v / (v + u)) v := by
  have hvu : 0 < v + u := by linarith
  have hl1 : HasDerivAt (fun v => log v) (1 / v) v := by
    simpa using (hasDerivAt_id' v).log hv.ne'
  have hl2 : HasDerivAt (fun v => log (v + u)) (1 / (v + u)) v := by
    simpa using ((hasDerivAt_id' v).add_const u).log hvu.ne'
  have hinv : HasDerivAt (fun v => x ^ 2 * (x + 1) / 12 / (u * v))
      ((0 * (u * v) - x ^ 2 * (x + 1) / 12 * (u * 1)) / (u * v) ^ 2) v :=
    (hasDerivAt_const v _).div ((hasDerivAt_id' v).const_mul u) (mul_pos hu hv).ne'
  have h := ((hl1.sub hl2).const_mul
    (-(x * (2 * x + 1)) / 6 / u - x ^ 2 * (x + 1) / 12 / u ^ 2)).sub hinv
  convert h using 1
  · funext w
    rfl
  unfold selfInSigB
  have := hu.ne'
  have := hv.ne'
  have := hvu.ne'
  field_simp
  ring

theorem tendsto_selfInPsiB_atTop (hu : 0 < u) :
    Tendsto (selfInPsiB x u) atTop (𝓝 0) := by
  have h1 : Tendsto (fun v : ℝ => u / v) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun v : ℝ => -log (1 + u / v)) atTop (𝓝 (-log (1 + 0))) :=
    (((continuousAt_log (by norm_num : (1 + 0 : ℝ) ≠ 0)).tendsto.comp
      (tendsto_const_nhds.add h1))).neg
  have h3 : Tendsto (fun v : ℝ => x ^ 2 * (x + 1) / 12 / u * v⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.const_mul (x ^ 2 * (x + 1) / 12 / u)
    rwa [mul_zero] at this
  rw [add_zero, log_one, neg_zero] at h2
  have h := (h2.const_mul (-(x * (2 * x + 1)) / 6 / u - x ^ 2 * (x + 1) / 12 / u ^ 2)).sub h3
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with v hv
  have e : log v - log (v + u) = -log (1 + u / v) := by
    rw [show 1 + u / v = (v + u) / v by field_simp, log_div (by linarith) hv.ne']
    ring
  unfold selfInPsiB
  rw [e]
  field_simp

/-- **The evaluation**: `Ψ_A(x) - Ψ_A(0) - Ψ_B(x) = F(x, u) - e₁(x)/u`. -/
theorem selfIn_disp_value (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    selfInPsiA x u x - selfInPsiA x u 0 - selfInPsiB x u x =
      selfInF x u - selfInE1 x / u := by
  have hx0 := hx.1.ne'
  have := hu.ne'
  have hxu : x + u = u + x := add_comm x u
  unfold selfInPsiA selfInPsiB selfInF selfInA selfInB selfInCY selfInR selfInE1
  rw [zero_add, hxu]
  field_simp
  ring

theorem continuousAt_selfInPsiA (hvu : 0 < v + u) : ContinuousAt (selfInPsiA x u) v := by
  have : ContinuousAt (fun v => log (v + u)) v :=
    (continuousAt_id.add continuousAt_const).log hvu.ne'
  unfold selfInPsiA
  fun_prop

/-- **The per-node dispersion relation** in the outer node variable `X`. -/
theorem integral_selfInKer (hx : x ∈ Ioo (0 : ℝ) 1) (ht : 0 < t)
    (hint : IntervalIntegrable (selfInKer t x) volume x 1) :
    ∫ X in x..1, selfInKer t x X = selfInF x (setCKQ x + t) - selfInE1 x / (setCKQ x + t) := by
  have hQx : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hu : 0 < setCKQ x + t := by linarith
  obtain ⟨hξ, hQξ⟩ := pairXi_spec hx
  set u := setCKQ x + t with hu_def
  set ξ := pairXi x with hξdef
  have hvξ : setCKQ ξ - setCKQ x = x := by
    rw [hQξ, ← setCKQ_add_self hx.2]; ring
  have hv1 : ∀ X ∈ Ioo x ξ, 0 < setCKQ X - setCKQ x ∧ setCKQ X - setCKQ x < x := by
    intro X hX
    have h1 := setCKQ_lt hx.1.le hX.1 (hX.2.trans hξ.2)
    have h2 := setCKQ_lt (hx.1.le.trans hX.1.le) hX.2 hξ.2
    constructor <;> linarith
  have hv2 : ∀ X ∈ Ioo ξ 1, x < setCKQ X - setCKQ x := by
    intro X hX
    have := setCKQ_lt (hx.1.le.trans hξ.1.le) hX.1 hX.2
    linarith
  have he : ∀ X, setCKQ X - setCKQ x + u = setCKQ X + t := fun X => by rw [hu_def]; ring
  have hd1 : ∀ X ∈ Ioo x ξ,
      HasDerivAt (fun X => selfInPsiA x u (setCKQ X - setCKQ x)) (selfInKer t x X) X := by
    intro X hX
    have hX1 : X < 1 := hX.2.trans hξ.2
    obtain ⟨hv0, hvx⟩ := hv1 X hX
    have := (hasDerivAt_selfInPsiA hx.1.ne' (by linarith : 0 < setCKQ X - setCKQ x + u)).comp X
      ((hasDerivAt_setCKQ hX1).sub_const (setCKQ x))
    refine this.congr_deriv ?_
    unfold selfInKer selfInSig
    simp only [not_lt.2 hvx.le, ↓reduceIte]
    rw [he]
    ring
  have hd2 : ∀ X ∈ Ioo ξ 1,
      HasDerivAt (fun X => selfInPsiB x u (setCKQ X - setCKQ x)) (selfInKer t x X) X := by
    intro X hX
    have hv := hv2 X hX
    have hv0 : 0 < setCKQ X - setCKQ x := hx.1.trans hv
    have := (hasDerivAt_selfInPsiB (x := x) hu hv0).comp X
      ((hasDerivAt_setCKQ hX.2).sub_const (setCKQ x))
    refine this.congr_deriv ?_
    unfold selfInKer selfInSig
    simp only [hv, ↓reduceIte]
    rw [he]
    ring
  have hcA0 : ContinuousAt (selfInPsiA x u) 0 := continuousAt_selfInPsiA (by linarith)
  have hcA : ContinuousAt (selfInPsiA x u) x := continuousAt_selfInPsiA (by linarith [hx.1])
  have hcB : ContinuousAt (selfInPsiB x u) x :=
    (hasDerivAt_selfInPsiB (x := x) hu hx.1).continuousAt
  have hvc : Tendsto (fun X => setCKQ X - setCKQ x) (𝓝 ξ) (𝓝 x) := by
    have hc : ContinuousAt (fun X => setCKQ X - setCKQ x) ξ :=
      (continuousAt_setCKQ hξ.2).sub continuousAt_const
    have : Tendsto (fun X => setCKQ X - setCKQ x) (𝓝 ξ) (𝓝 (setCKQ ξ - setCKQ x)) := hc.tendsto
    rwa [hvξ] at this
  have hsub : ∀ c d : ℝ, x ≤ c → d ≤ 1 → c ≤ d → IntervalIntegrable (selfInKer t x) volume c d :=
    fun c d hc hd hcd => hint.mono_set (by
      rw [uIcc_of_le hcd, uIcc_of_le (hx.2.le)]
      exact Icc_subset_Icc hc hd)
  have I1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hξ.1 hd1
    (hsub x ξ le_rfl hξ.2.le hξ.1.le)
    ((hcA0.tendsto.mono_left nhdsWithin_le_nhds).comp (tendsto_setCKQ_sub_right hx))
    ((hcA.tendsto.comp hvc).mono_left nhdsWithin_le_nhds)
  have I2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hξ.2 hd2
    (hsub ξ 1 hξ.1.le le_rfl hξ.2.le)
    ((hcB.tendsto.comp hvc).mono_left nhdsWithin_le_nhds)
    ((tendsto_selfInPsiB_atTop hu).comp (tendsto_setCKQ_sub_atTop x))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hsub x ξ le_rfl hξ.2.le hξ.1.le)
    (hsub ξ 1 hξ.1.le le_rfl hξ.2.le), I1, I2]
  have hv := selfIn_disp_value hx hu
  linear_combination hv

end

end QED.ChainProof.SetCK

end
