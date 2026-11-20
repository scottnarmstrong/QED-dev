/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegLInBd

/-!
# Set (c), Stage K: the regulator link of the ladder pair

Helper level (no frozen statement). The inner ladder placement at outer photon mass `λ` and
`Λ = ∞` is the representation (3.4) of `docs/TWO-LOOP-UNITS.md` with the two photon masses
separated (inner mass² `t`, outer mass `λ`):

`lInRep t λ = ∫₀¹ dY [∫₀¹ dx G(λ, √t; Y, x) - F₂(λ) CT(√t; Y)]` (`lInRep`).

With `G = R + T₁` (`QED.ChainProof.SetCK.lInR`, `lT1`) and `∫₀¹ T₁ dx = -(Y c/M) J(λ)`,
`∫₀¹ Y c/M dY = F₂(t)`:

`lInRep t λ = ∬ R(λ) - F₂(t) J(λ) - F₂(λ) ∫₀¹ CT(√t)` (`lInRep_split`),

and `lInner t = ∬ R(0) + (11/6) F₂(t) - (1/2) ∫₀¹ CT(√t)` (`lInner_split`). Dominated convergence
with `K(t)(1 + ℓ)` (`abs_lInR_le`), `J(λ) + log λ → -11/6` and `F₂(λ) → 1/2` give

* **`tendsto_lInRep`**: `lInRep t λ - F₂(t) log λ → lInner t` as `λ → 0⁺`;
* **`tendsto_lPairRep`**: `lInRep t λ + lOutRep t λ → lPair t` as `λ → 0⁺`, for every `t > 0`:
  the infrared logarithms `±F₂(t) log λ` of the two placements cancel, and the λ-regulated ladder
  pair at `Λ = ∞` tends to the Stage K pair `lPair` (`QED.ChainProof.SetCK.tendsto_lOutRep`).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- **The inner ladder placement at outer photon mass `λ`**: the two-mass representation (3.4). -/
noncomputable def lInRep (t lam : ℝ) : ℝ :=
  ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, ladderGm lam (√t) Y x) -
    oneLoopF2 1 lam * ladderCtBracket (√t) Y)

theorem measurable_lInR_uncurry (t lam : ℝ) : Measurable (uncurry fun Y x => lInR t lam Y x) := by
  have h1 := measurable_ladderGm_uncurry lam (√t)
  have h2 : Measurable (uncurry fun Y x => lT1 t lam Y x) := by
    change Measurable fun p : ℝ × ℝ => lT1 t lam p.1 p.2
    unfold lT1 massIn ladderInnerMass
    fun_prop
  exact h1.sub h2

theorem intervalIntegrable_lInR {t lam Y : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => lInR t lam Y x) volume 0 1 ∧
      |∫ x in (0 : ℝ)..1, lInR t lam Y x| ≤
        lInBd t * (2 + log 2 - log Y - log (1 - Y)) := by
  have hm : Measurable fun x => lInR t lam Y x :=
    (measurable_lInR_uncurry t lam).comp (measurable_const.prodMk measurable_id)
  obtain ⟨hi, hb⟩ := intervalIntegrable_of_abs_le hm
    ((intervalIntegrable_add_ladderEll 1 Y).const_mul (lInBd t))
    fun x hx => abs_lInR_le ht hY hx
  refine ⟨hi, hb.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_const_mul, integral_add_ladderEll]
  ring

theorem intervalIntegrable_integral_lInR {t lam : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, lInR t lam Y x) volume 0 1 :=
  (intervalIntegrable_of_abs_le (measurable_intervalIntegral_of_uncurry
    (measurable_lInR_uncurry t lam)) ((intervalIntegrable_ellY (2 + log 2)).const_mul (lInBd t))
    fun _ hY => (intervalIntegrable_lInR ht hY).2.trans (le_of_eq (by ring))).1

/-- **`∬ R(λ) → ∬ R(0)` as `λ → 0⁺`.** -/
theorem tendsto_integral_lInR {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, lInR t lam Y x) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, lInR t 0 Y x)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => lInBd t * (2 + log 2 - log Y - log (1 - Y)))
    (Eventually.of_forall fun lam => (measurable_intervalIntegral_of_uncurry
      (measurable_lInR_uncurry t lam)).aestronglyMeasurable) ?_
    ((intervalIntegrable_ellY (2 + log 2)).const_mul (lInBd t)) ?_
  · refine Eventually.of_forall fun lam => ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]
    exact (intervalIntegrable_lInR ht ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩).2
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hYo : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => lInBd t * (1 + ladderEll Y x))
      (Eventually.of_forall fun lam => ((measurable_lInR_uncurry t lam).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_
      ((intervalIntegrable_add_ladderEll 1 Y).const_mul (lInBd t)) ?_
    · refine Eventually.of_forall fun lam => ?_
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      rw [Real.norm_eq_abs]
      exact abs_lInR_le ht hYo ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      exact ((continuous_lInR ht hYo ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).tendsto 0).mono_left
        nhdsWithin_le_nhds

theorem continuousOn_div_massIn {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun Y => Y * (Y * (1 - Y)) / massIn t Y) (uIcc 0 1) := by
  refine ContinuousOn.div (by fun_prop) (by unfold massIn ladderInnerMass; fun_prop) fun Y hY => ?_
  rw [uIcc_of_le zero_le_one] at hY
  exact (massIn_pos ht hY).ne'

theorem integral_div_massIn_eq {t : ℝ} :
    ∫ Y in (0 : ℝ)..1, Y * (Y * (1 - Y)) / massIn t Y = oneLoopF2 1 (√t) := by
  unfold oneLoopF2
  refine intervalIntegral.integral_congr fun Y _ => ?_
  simp only [massIn]
  ring

/-- `∫₀¹ T₁ dx = -(Y c/M) J(λ)`. -/
theorem integral_lT1 (t lam Y : ℝ) :
    ∫ x in (0 : ℝ)..1, lT1 t lam Y x = -(Y * (Y * (1 - Y)) / massIn t Y) * outerSoftJ lam := by
  unfold outerSoftJ
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [lT1]
  ring

theorem intervalIntegrable_lT1 {t lam : ℝ} (ht : 0 < t) (hlam : 0 < lam) {Y : ℝ}
    (hY : Y ∈ Icc (0 : ℝ) 1) : IntervalIntegrable (fun x => lT1 t lam Y x) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  unfold lT1
  refine (ContinuousOn.div (by fun_prop) ((continuousOn_const).mul
    (by unfold ladderInnerMass; fun_prop)) fun x hx => ?_).neg
  rw [uIcc_of_le zero_le_one] at hx
  exact mul_ne_zero (massIn_pos ht hY).ne' (ladderInnerMass_pos one_pos hlam hx).ne'

theorem lInRep_split {t lam : ℝ} (ht : 0 < t) (hlam : 0 < lam) :
    lInRep t lam = (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, lInR t lam Y x) -
      oneLoopF2 1 (√t) * outerSoftJ lam -
        oneLoopF2 1 lam * ∫ Y in (0 : ℝ)..1, ladderCtBracket (√t) Y := by
  have iR := intervalIntegrable_integral_lInR (lam := lam) ht
  have iD := (continuousOn_div_massIn ht).intervalIntegrable (μ := volume)
  have iC := intervalIntegrable_ladderCtBracket (sqrt_pos.2 ht)
  have e : lInRep t lam = ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, lInR t lam Y x) -
      outerSoftJ lam * (Y * (Y * (1 - Y)) / massIn t Y) -
        oneLoopF2 1 lam * ladderCtBracket (√t) Y) := by
    unfold lInRep
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hYo : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
    have hG : (fun x => ladderGm lam (√t) Y x) = fun x => lInR t lam Y x + lT1 t lam Y x := by
      funext x; simp only [lInR]; ring
    rw [hG, intervalIntegral.integral_add (intervalIntegrable_lInR ht hYo).1
      (intervalIntegrable_lT1 ht hlam (Ioo_subset_Icc_self hYo)), integral_lT1]
    ring
  rw [e, intervalIntegral.integral_sub (iR.sub (iD.const_mul _)) (iC.const_mul _),
    intervalIntegral.integral_sub iR (iD.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_div_massIn_eq]
  ring

theorem lInner_split {t : ℝ} (ht : 0 < t) :
    lInner t = (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, lInR t 0 Y x) +
      11 / 6 * oneLoopF2 1 (√t) - 1 / 2 * ∫ Y in (0 : ℝ)..1, ladderCtBracket (√t) Y := by
  have iR := intervalIntegrable_integral_lInR (lam := 0) ht
  have iD := (continuousOn_div_massIn ht).intervalIntegrable (μ := volume)
  have iC := intervalIntegrable_ladderCtBracket (sqrt_pos.2 ht)
  have e : lInner t = ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, lInR t 0 Y x) +
      11 / 6 * (Y * (Y * (1 - Y)) / massIn t Y) - 1 / 2 * ladderCtBracket (√t) Y) := by
    unfold lInner
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hYo : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
    have hx : ∫ x in (0 : ℝ)..1, (ladderGm 0 (√t) Y x +
        Y * (Y * (1 - Y)) * (1 - x) ^ 3 / (x * massIn t Y)) =
        ∫ x in (0 : ℝ)..1, lInR t 0 Y x := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le zero_le_one] at hx
      exact (lInR_zero ht hYo ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).symm
    simp only [lInnerIntegrand]
    rw [hx]
    ring
  rw [e, intervalIntegral.integral_sub (iR.add (iD.const_mul _)) (iC.const_mul _),
    intervalIntegral.integral_add iR (iD.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_div_massIn_eq]

/-- **The regulator link of the inner ladder placement**: for `t > 0`,
`lInRep t λ - F₂(t) log λ → lInner t` as `λ → 0⁺`. -/
theorem tendsto_lInRep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => lInRep t lam - oneLoopF2 1 (√t) * log lam) (𝓝[>] 0)
      (𝓝 (lInner t)) := by
  have h := ((tendsto_integral_lInR ht).sub
    (tendsto_outerSoftJ_add_log.const_mul (oneLoopF2 1 (√t)))).sub
    (tendsto_oneLoopF2_one.mul_const (∫ Y in (0 : ℝ)..1, ladderCtBracket (√t) Y))
  rw [lInner_split ht]
  refine (h.congr' ?_).trans (le_of_eq (congrArg 𝓝 (by ring)))
  filter_upwards [self_mem_nhdsWithin] with lam (hl : 0 < lam)
  rw [lInRep_split ht hl]
  ring

/-- **The regulator link of the ladder pair**: for `t > 0`, the λ-regulated ladder pair at
`Λ = ∞` tends to the Stage K pair, `lInRep t λ + lOutRep t λ → lPair t` as `λ → 0⁺`. -/
theorem tendsto_lPairRep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun lam => lInRep t lam + lOutRep t lam) (𝓝[>] 0) (𝓝 (lPair t)) := by
  have := (tendsto_lInRep ht).add (tendsto_lOutRep ht)
  rw [lPair]
  refine this.congr fun lam => ?_
  ring

end QED.ChainProof.SetCK
