/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKPairDisp

/-!
# Set (c), Stage K: the per-node dispersion relation in the outer node variable

Helper level (no frozen statement). Substituting `v = Q(X) - Q(x)` (`Q(X) = X²/(1-X)`, so
`v + u = Q(X) + t` for `u = Q(x) + t`) in the per-node dispersion relation of `SetCKPairDisp`
gives, for `x ∈ (0, 1)`, `t > 0`, `t ≠ x`, the identity (`integral_pairKer`)

`∫_x^1 σ_x(Q(X) - Q(x)) Q'(X)/(Q(X) + t) dX = F(x, Q(x) + t) - e₁(x)/(Q(x) + t)`,

given the integrability of the left side. The `β` threshold `v = x` sits at `X = ξ(x)`, the
root of `Q(ξ) = x/(1-x)` (`pairXi`); the integral is split there.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology MeasureTheory

/-- `Q'(X) = X(2 - X)/(1 - X)²`. -/
noncomputable def setCKdQ (X : ℝ) : ℝ := X * (2 - X) / (1 - X) ^ 2

/-- **The pair kernel** in the node variables: `σ_x(Q(X) - Q(x)) Q'(X)/(Q(X) + t)`. -/
noncomputable def pairKer (t x X : ℝ) : ℝ :=
  dispSig x (setCKQ X - setCKQ x) * (setCKdQ X / (setCKQ X + t))

/-- The node `ξ(x)` with `Q(ξ) = x/(1-x)`, i.e. `Q(ξ) - Q(x) = x`. -/
noncomputable def pairXi (x : ℝ) : ℝ :=
  (√((x / (1 - x)) ^ 2 + 4 * (x / (1 - x))) - x / (1 - x)) / 2

section

variable {x t X : ℝ}

theorem hasDerivAt_setCKQ (hX : X < 1) : HasDerivAt setCKQ (setCKdQ X) X := by
  have h1 : 1 - X ≠ 0 := by linarith
  have := ((hasDerivAt_id' X).pow 2).div ((hasDerivAt_id' X).const_sub 1) h1
  convert this using 1
  · funext y; simp only [setCKQ, Pi.div_apply, Pi.pow_apply]
  · simp only [Pi.pow_apply]
    unfold setCKdQ
    field_simp
    ring

theorem continuousAt_setCKQ (hX : X < 1) : ContinuousAt setCKQ X :=
  (hasDerivAt_setCKQ hX).continuousAt

theorem setCKQ_sub {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    setCKQ b - setCKQ a = (b - a) * (a + b - a * b) / ((1 - a) * (1 - b)) := by
  have h1 : 1 - a ≠ 0 := by linarith
  have h2 : 1 - b ≠ 0 := by linarith
  unfold setCKQ
  field_simp
  ring

theorem setCKQ_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) : setCKQ a < setCKQ b := by
  have h := setCKQ_sub (hab.trans hb) hb
  have hpos : 0 < (b - a) * (a + b - a * b) / ((1 - a) * (1 - b)) := by
    have h1 : 0 < 1 - a := by linarith
    have h2 : 0 < 1 - b := by linarith
    have h3 : 0 < a + b - a * b := by nlinarith
    exact div_pos (mul_pos (by linarith) h3) (mul_pos h1 h2)
  linarith

theorem setCKQ_add_self (hx : x < 1) : setCKQ x + x = x / (1 - x) := by
  have h1 : 1 - x ≠ 0 := by linarith
  unfold setCKQ
  field_simp
  ring

theorem pairXi_spec (hx : x ∈ Ioo (0 : ℝ) 1) :
    pairXi x ∈ Ioo x 1 ∧ setCKQ (pairXi x) = x / (1 - x) := by
  have hp : 0 < x / (1 - x) := div_pos hx.1 (by linarith [hx.2])
  set p := x / (1 - x) with hpdef
  set s := √(p ^ 2 + 4 * p) with hsdef
  have hs2 : s ^ 2 = p ^ 2 + 4 * p := sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hsp : p < s := by nlinarith
  have hs1 : s < p + 2 := by nlinarith
  have hξ : pairXi x = (s - p) / 2 := rfl
  have hξ0 : 0 < pairXi x := by rw [hξ]; linarith
  have hξ1 : pairXi x < 1 := by rw [hξ]; linarith
  have hQ : setCKQ (pairXi x) = p := by
    have h1 : 1 - pairXi x ≠ 0 := by linarith
    unfold setCKQ
    rw [div_eq_iff h1, hξ]
    linear_combination hs2 / 4
  refine ⟨⟨?_, hξ1⟩, hQ⟩
  by_contra hle
  push Not at hle
  have hQx : setCKQ x + x = p := setCKQ_add_self hx.2
  rcases eq_or_lt_of_le hle with h | h
  · rw [h] at hQ; linarith [hx.1]
  · have := setCKQ_lt hξ0.le h hx.2
    linarith [hx.1]

theorem tendsto_setCKQ_sub_right (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun X => setCKQ X - setCKQ x) (𝓝[>] x) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun X => setCKQ X - setCKQ x) x :=
      (continuousAt_setCKQ hx.2).sub continuousAt_const
    have : Tendsto (fun X => setCKQ X - setCKQ x) (𝓝 x) (𝓝 (setCKQ x - setCKQ x)) := hc.tendsto
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT hx.2] with X hX
    exact sub_pos.2 (setCKQ_lt hx.1.le hX.1 hX.2)

theorem tendsto_setCKQ_sub_atTop (x : ℝ) :
    Tendsto (fun X => setCKQ X - setCKQ x) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun X : ℝ => 1 - X) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun X : ℝ => 1 - X) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with X hX
      exact sub_pos.2 hX
  have h2 := tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun X : ℝ => X ^ 2) (𝓝[<] 1) (𝓝 1) := by
    have := ((continuous_pow 2).tendsto (1 : ℝ))
    rw [one_pow] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h4 := tendsto_atTop_add_const_right _ (-setCKQ x) (h3.pos_mul_atTop one_pos h2)
  refine h4.congr fun X => ?_
  simp only [Function.comp, setCKQ]
  ring

/-- **The per-node dispersion relation** in the outer node variable `X`. -/
theorem integral_pairKer (hx : x ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) (hxt : x ≠ t)
    (hint : IntervalIntegrable (pairKer t x) volume x 1) :
    ∫ X in x..1, pairKer t x X = pairFe x (setCKQ x + t) - dispE1 x / (setCKQ x + t) := by
  have hQx : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hu : 0 < setCKQ x + t := by linarith
  have hup : setCKQ x + t ≠ x / (1 - x) := by
    rw [← setCKQ_add_self hx.2]; intro h; exact hxt (by linarith)
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
      HasDerivAt (fun X => dispPsi1 x u (setCKQ X - setCKQ x)) (pairKer t x X) X := by
    intro X hX
    have hX1 : X < 1 := hX.2.trans hξ.2
    obtain ⟨hv0, hvx⟩ := hv1 X hX
    have := (hasDerivAt_dispPsi1 hx hu hup hv0).comp X ((hasDerivAt_setCKQ hX1).sub_const _)
    refine this.congr_deriv ?_
    unfold pairKer dispSig
    simp only [not_lt.2 hvx.le, ↓reduceIte]
    rw [he]
    ring
  have hd2 : ∀ X ∈ Ioo ξ 1, HasDerivAt (fun X => dispPsi1 x u (setCKQ X - setCKQ x) +
      dispJump x u (setCKQ X - setCKQ x)) (pairKer t x X) X := by
    intro X hX
    have hv := hv2 X hX
    have hv0 : 0 < setCKQ X - setCKQ x := hx.1.trans hv
    have hQ := (hasDerivAt_setCKQ hX.2).sub_const (setCKQ x)
    have := ((hasDerivAt_dispPsi1 hx hu hup hv0).comp X hQ).add
      ((hasDerivAt_dispJump hx hu hv0).comp X hQ)
    refine this.congr_deriv ?_
    unfold pairKer dispSig
    simp only [hv, ↓reduceIte]
    rw [he]
    ring
  have hcont1 : ContinuousAt (dispPsi1 x u) x := (hasDerivAt_dispPsi1 hx hu hup hx.1).continuousAt
  have hcontJ : ContinuousAt (dispJump x u) x := (hasDerivAt_dispJump hx hu hx.1).continuousAt
  have hvc : Tendsto (fun X => setCKQ X - setCKQ x) (𝓝 ξ) (𝓝 x) := by
    have hc : ContinuousAt (fun X => setCKQ X - setCKQ x) ξ :=
      (continuousAt_setCKQ hξ.2).sub continuousAt_const
    have : Tendsto (fun X => setCKQ X - setCKQ x) (𝓝 ξ) (𝓝 (setCKQ ξ - setCKQ x)) := hc.tendsto
    rwa [hvξ] at this
  have hsub : ∀ c d : ℝ, x ≤ c → d ≤ 1 → c ≤ d → IntervalIntegrable (pairKer t x) volume c d :=
    fun c d hc hd hcd => hint.mono_set (by
      rw [uIcc_of_le hcd, uIcc_of_le (hx.2.le)]
      exact Icc_subset_Icc hc hd)
  have I1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hξ.1 hd1
    (hsub x ξ le_rfl hξ.2.le hξ.1.le)
    ((tendsto_dispPsi1_zero hx hu).comp (tendsto_setCKQ_sub_right hx))
    ((hcont1.tendsto.comp hvc).mono_left nhdsWithin_le_nhds)
  have I2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hξ.2 hd2
    (hsub ξ 1 hξ.1.le le_rfl hξ.2.le)
    (((hcont1.tendsto.comp hvc).add (hcontJ.tendsto.comp hvc)).mono_left nhdsWithin_le_nhds)
    ((tendsto_dispPsi2_atTop hx hu hup).comp (tendsto_setCKQ_sub_atTop x))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hsub x ξ le_rfl hξ.2.le hξ.1.le)
    (hsub ξ 1 hξ.1.le le_rfl hξ.2.le), I1, I2]
  have hv := disp_value hx hu hup
  linear_combination hv

end

end QED.ChainProof.SetCK
