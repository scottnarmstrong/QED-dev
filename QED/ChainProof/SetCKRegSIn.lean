/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegSInBd
public import QED.ChainProof.SetCKSelfIn
public import QED.TwoLoop.UnitSCCloseIR
public import QED.TwoLoop.UnitSCLimitSLimit

/-!
# Set (c), Stage K: the regulator link of the self-energy unit with a massive inner photon

Helper level (no frozen statement). The self-energy unit `S(t, 0)` at outer photon mass `λ` and
`Λ = ∞` is eq. (5.3) of `docs/TWO-LOOP-UNITS.md` with the two photon masses separated (inner
mass² `t`, `M = M_t(Y)`, outer mass `λ`):

`selfInRep t λ = 2 ∫₀¹ dY [∫₀¹ dx G_S(λ; Y, x) + d̄₂(Y, M) V_k(λ) + (d̄₂ - σ)(Y, M) V_m(λ)]`,

`G_S = selfGm λ √t + k₂/h²` (`selfInS`, the engine's `E - e₀`), with the counterterm insertions
`d̄₂`, `σ` of `QED.ChainProof.SetCK.selfIn` and the one-loop insertion values `V_k`, `V_m`
(`QED.TwoLoop.UnitSCClose.selfVk`, `selfVm`). The unit is infrared finite.

* **`tendsto_selfInRep`**: `selfInRep t λ → selfIn t` as `λ → 0⁺`, for every `t > 0`
  (dominated convergence with `abs_selfInS_le`, `G_S(0) = selfGm 0 √t - D` (`selfInS_zero`),
  `V_k(λ) → -1`, `V_m(λ) → 1/2`).

Numerically (scratch `stageK/m5/snum2.py`) `selfInRep 1 λ = -0.590483` (`λ = 10⁻²`) and
`-0.599005` (`λ = 10⁻³`), against `selfIn 1 = -0.599985`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitSCClose

/-- **The self-energy unit with a massive inner photon at outer photon mass `λ`**: the two-mass
form of eq. (5.3). -/
noncomputable def selfInRep (t lam : ℝ) : ℝ :=
  2 * ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, selfInS t lam Y x) +
    selfInD2 Y (massIn t Y) * selfVk lam +
      (selfInD2 Y (massIn t Y) - selfInSigma Y (massIn t Y)) * selfVm lam)

theorem measurable_selfInS_uncurry (t lam : ℝ) :
    Measurable (uncurry fun Y x => selfInS t lam Y x) := by
  have h1 := measurable_selfGm_uncurry lam (√t)
  have h2 : Measurable (uncurry fun Y x => selfK2 Y x / (ladderInnerMass 1 lam x / x) ^ 2) := by
    change Measurable fun p : ℝ × ℝ => selfK2 p.1 p.2 / (ladderInnerMass 1 lam p.2 / p.2) ^ 2
    unfold selfK2 ladderInnerMass
    fun_prop
  exact h1.add h2

/-- `G_S` is continuous in the outer mass `λ`. -/
theorem continuous_selfInS {t Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : Continuous fun lam => selfInS t lam Y x := by
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have hM := massIn_pos ht (Ioo_subset_Icc_self hY)
  have hMx : ∀ lam, 0 < ladderInnerMass 1 lam x := fun lam =>
    ladderInnerMass_pos_of_pos hx.1 hx.2.le
  have hh : ∀ lam, 0 < ladderInnerMass 1 lam x / x := fun lam => div_pos (hMx lam) hx.1
  have hMc : Continuous fun lam => ladderInnerMass 1 lam x := by unfold ladderInnerMass; fun_prop
  simp only [selfInS, selfGm, sForm]
  have hMs : ladderInnerMass 1 (√t) Y = massIn t Y := rfl
  rw [hMs]
  have h1 : ∀ lam, ladderInnerMass 1 lam x / x ≠ 0 := fun lam => (hh lam).ne'
  have h2 : ∀ lam, ladderInnerMass 1 lam x / x *
      (massIn t Y + Y * (1 - Y) * (ladderInnerMass 1 lam x / x)) ≠ 0 := fun lam => by
    have := hh lam; positivity
  have h3 : ∀ lam, massIn t Y + Y * (1 - Y) * (ladderInnerMass 1 lam x / x) ≠ 0 := fun lam => by
    have := hh lam; positivity
  have h4 : ∀ lam, 1 + massIn t Y / (Y * (1 - Y) * (ladderInnerMass 1 lam x / x)) ≠ 0 :=
    fun lam => by have := hh lam; positivity
  have h5 : ∀ lam, massIn t Y * (massIn t Y + Y * (1 - Y) * (ladderInnerMass 1 lam x / x)) ≠ 0 :=
    fun lam => by have := hh lam; positivity
  have h6 : massIn t Y ^ 2 ≠ 0 := pow_ne_zero 2 hM.ne'
  have h7 : massIn t Y ≠ 0 := hM.ne'
  have h8 : ∀ _ : ℝ, x ≠ 0 := fun _ => hx.1.ne'
  have h9 : ∀ lam, Y * (1 - Y) * (ladderInnerMass 1 lam x / x) ≠ 0 := fun lam =>
    mul_ne_zero hc.ne' (hh lam).ne'
  have h10 : ∀ lam, (ladderInnerMass 1 lam x / x) ^ 2 ≠ 0 := fun lam => pow_ne_zero 2 (h1 lam)
  have h12 : massIn t Y * (Y * (1 - Y)) ≠ 0 := mul_ne_zero hM.ne' hc.ne'
  fun_prop (disch := assumption)

/-- At `λ = 0`, `G_S` is the Stage K integrand `selfGm 0 √t - D`. -/
theorem selfInS_zero {t Y x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    selfInS t 0 Y x = selfGm 0 (√t) Y x - selfInSub Y x := by
  have hx0 := hx.1.ne'
  have e : ladderInnerMass 1 0 x / x = x := by
    unfold ladderInnerMass
    rw [show x ^ 2 * 1 ^ 2 + (1 - x) * 0 ^ 2 = x * x by ring]
    field_simp
  unfold selfInS
  rw [e]
  unfold selfInSub selfK2
  field_simp
  ring

theorem intervalIntegrable_selfInS {t lam Y : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => selfInS t lam Y x) volume 0 1 ∧
      |∫ x in (0 : ℝ)..1, selfInS t lam Y x| ≤
        selfInSBd t * (2 + log 2 - log Y - log (1 - Y)) := by
  have hm : Measurable fun x => selfInS t lam Y x :=
    (measurable_selfGm lam (√t) Y).add (by unfold selfK2 ladderInnerMass; fun_prop)
  obtain ⟨hi, hb⟩ := intervalIntegrable_of_abs_le hm
    ((intervalIntegrable_add_ladderEll 1 Y).const_mul (selfInSBd t))
    fun x hx => abs_selfInS_le ht hY hx
  refine ⟨hi, hb.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_const_mul, integral_add_ladderEll]
  ring

theorem intervalIntegrable_integral_selfInS {t lam : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, selfInS t lam Y x) volume 0 1 :=
  (intervalIntegrable_of_abs_le (measurable_intervalIntegral_of_uncurry
    (measurable_selfInS_uncurry t lam))
    ((intervalIntegrable_ellY (2 + log 2)).const_mul (selfInSBd t))
    fun _ hY => (intervalIntegrable_selfInS ht hY).2.trans (le_of_eq (by ring))).1

/-- **`∬ G_S(λ) → ∬ G_S(0)` as `λ → 0⁺`.** -/
theorem tendsto_integral_selfInS {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfInS t lam Y x) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfInS t 0 Y x)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => selfInSBd t * (2 + log 2 - log Y - log (1 - Y)))
    (Eventually.of_forall fun lam => (measurable_intervalIntegral_of_uncurry
      (measurable_selfInS_uncurry t lam)).aestronglyMeasurable) ?_
    ((intervalIntegrable_ellY (2 + log 2)).const_mul (selfInSBd t)) ?_
  · refine Eventually.of_forall fun lam => ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]
    exact (intervalIntegrable_selfInS ht ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩).2
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hYo : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => selfInSBd t * (1 + ladderEll Y x))
      (Eventually.of_forall fun lam => ((measurable_selfGm lam (√t) Y).add
        (by unfold selfK2 ladderInnerMass; fun_prop)).aestronglyMeasurable) ?_
      ((intervalIntegrable_add_ladderEll 1 Y).const_mul (selfInSBd t)) ?_
    · refine Eventually.of_forall fun lam => ?_
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      rw [Real.norm_eq_abs]
      exact abs_selfInS_le ht hYo ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      exact ((continuous_selfInS ht hYo ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).tendsto 0).mono_left
        nhdsWithin_le_nhds

theorem intervalIntegrable_selfInD2 {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun Y => selfInD2 Y (massIn t Y)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  have hM : ∀ Y ∈ uIcc (0 : ℝ) 1, massIn t Y ≠ 0 := fun Y hY => by
    rw [uIcc_of_le zero_le_one] at hY; exact (massIn_pos ht hY).ne'
  have hc : ContinuousOn (fun Y => massIn t Y) (uIcc 0 1) := by
    unfold massIn ladderInnerMass; fun_prop
  unfold selfInD2
  exact (((continuousOn_const.sub continuousOn_id).mul (hc.log hM)).div_const 2).add
    (ContinuousOn.div (by fun_prop) hc hM)

theorem intervalIntegrable_selfInSigma {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun Y => selfInSigma Y (massIn t Y)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  have hM : ∀ Y ∈ uIcc (0 : ℝ) 1, massIn t Y ≠ 0 := fun Y hY => by
    rw [uIcc_of_le zero_le_one] at hY; exact (massIn_pos ht hY).ne'
  have hc : ContinuousOn (fun Y => massIn t Y) (uIcc 0 1) := by
    unfold massIn ladderInnerMass; fun_prop
  unfold selfInSigma
  exact ((ContinuousOn.div_const (continuousOn_const.add continuousOn_id) 2).mul
    (hc.log hM)).neg

theorem selfInRep_split {t lam : ℝ} (ht : 0 < t) :
    selfInRep t lam = 2 * ((∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfInS t lam Y x) +
      selfVk lam * (∫ Y in (0 : ℝ)..1, selfInD2 Y (massIn t Y)) +
        selfVm lam * ((∫ Y in (0 : ℝ)..1, selfInD2 Y (massIn t Y)) -
          ∫ Y in (0 : ℝ)..1, selfInSigma Y (massIn t Y))) := by
  have iS := intervalIntegrable_integral_selfInS (lam := lam) ht
  have iD := intervalIntegrable_selfInD2 ht
  have iσ := intervalIntegrable_selfInSigma ht
  unfold selfInRep
  rw [intervalIntegral.integral_add (iS.add (iD.mul_const _)) ((iD.sub iσ).mul_const _),
    intervalIntegral.integral_add iS (iD.mul_const _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_sub iD iσ]
  ring

theorem selfIn_split {t : ℝ} (ht : 0 < t) :
    selfIn t = 2 * ((∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfInS t 0 Y x) +
      (-1) * (∫ Y in (0 : ℝ)..1, selfInD2 Y (massIn t Y)) +
        1 / 2 * ((∫ Y in (0 : ℝ)..1, selfInD2 Y (massIn t Y)) -
          ∫ Y in (0 : ℝ)..1, selfInSigma Y (massIn t Y))) := by
  have iS := intervalIntegrable_integral_selfInS (lam := 0) ht
  have iD := intervalIntegrable_selfInD2 ht
  have iσ := intervalIntegrable_selfInSigma ht
  have e : selfIn t = 2 * ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, selfInS t 0 Y x) +
      selfInD2 Y (massIn t Y) * (-1) +
        (selfInD2 Y (massIn t Y) - selfInSigma Y (massIn t Y)) * (1 / 2)) := by
    unfold selfIn
    congr 1
    refine intervalIntegral.integral_congr fun Y _ => ?_
    have hx : ∫ x in (0 : ℝ)..1, (selfGm 0 (√t) Y x - selfInSub Y x) =
        ∫ x in (0 : ℝ)..1, selfInS t 0 Y x := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      exact (selfInS_zero ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).symm
    simp only [selfInIntegrand]
    rw [hx]
    ring
  rw [e, intervalIntegral.integral_add (iS.add (iD.mul_const _)) ((iD.sub iσ).mul_const _),
    intervalIntegral.integral_add iS (iD.mul_const _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_sub iD iσ]
  ring

/-- **The regulator link of the inner-massive self-energy unit**: for `t > 0`,
`selfInRep t λ → selfIn t` as `λ → 0⁺`. -/
theorem tendsto_selfInRep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => selfInRep t lam) (𝓝[>] 0) (𝓝 (selfIn t)) := by
  have h := (((tendsto_integral_selfInS ht).add
    (tendsto_selfVk.mul_const (∫ Y in (0 : ℝ)..1, selfInD2 Y (massIn t Y)))).add
    (tendsto_selfVm.mul_const ((∫ Y in (0 : ℝ)..1, selfInD2 Y (massIn t Y)) -
      ∫ Y in (0 : ℝ)..1, selfInSigma Y (massIn t Y)))).const_mul 2
  rw [selfIn_split ht]
  exact h.congr fun lam => (selfInRep_split ht).symm

end QED.ChainProof.SetCK
