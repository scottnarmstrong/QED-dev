/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegSOut
public import QED.ChainProof.SetCKLamOutCDecay

/-!
# Set (c), Stage K: the outer-massive self-energy unit at finite Pauli–Villars mass

Helper level (no frozen statement). In `S(0, t)` (outer photon of mass² `t > 0`) the massless
line is the inner photon. With the Pauli–Villars pair `(λ, Λ)` on it, and the counterterms
`δ₂, δ_m` (inserted in the outer one-loop vertex, coefficients `V_k(√t)`, `V_m(√t)`) and the
corner counterterm `δ₁` (coefficient `F₂(√t)`) as Pauli–Villars differences of their
inner-parameter integrands `d̄₂`, `d̄₂ - σ`, `CT` (`selfInD2`, `selfInSigma`, `ladderCtBracket`),
the unit is (layer R2 of the M5 plan)

`scOutSReg t λ Λ = 2 ∫₀¹ dY [∫₀¹ dx (G(√t, λ) - G(√t, Λ)) + Δd̄₂ V_k + Δ(d̄₂ - σ) V_m
  - F₂ ΔCT]`, `G = selfGm`, `Δf = f(M_λ) - f(M_Λ)`.

* **`scOutSReg_eq`**: `scOutSReg t λ Λ = scOutSRep t λ - scOutSRep t Λ` (`λ² ≤ 1 ≤ Λ`; the
  large-`M` constant `k₂/h_t²` cancels in the difference);
* **`lamOutS_scOutSRep_eq`**: at the large mass, with `G(√t, Λ) + k₂/h_t² = e₁ - ℓ log M_Λ`
  (`selfE1`) and `∫₀¹ ℓ dx = (1-Y)/2 V_k + V_m` (`integral_selfEll`), the logarithms of the
  self-energy subdivergence cancel against `δ₂, δ_m` by `V_k + V_m + F₂ = 0`:
  `scOutSRep t Λ = 2 ∬ e₁ - 2 F₂ ∫ Y²(2 - Y)/(2 M_Λ) + F₂ ∫ Y log M_Λ`;
* `lamOutS_E1_bound` (`|∬ e₁| ≤ (20 + 9 log Λ + 5 log 2)/Λ²`), `tendsto_lamOutS_rat`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitSCClose

/-- **The outer-massive self-energy unit with the corner counterterm at finite Pauli–Villars
mass** (pair `(λ, Λ)` on the inner line; counterterms `δ₂, δ_m, δ₁` as Pauli–Villars
differences of their inner-parameter integrands). -/
noncomputable def scOutSReg (t lam Lam : ℝ) : ℝ :=
  2 * ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, (selfGm (√t) lam Y x - selfGm (√t) Lam Y x)) +
    (selfInD2 Y (ladderInnerMass 1 lam Y) - selfInD2 Y (ladderInnerMass 1 Lam Y)) * selfVk (√t) +
    ((selfInD2 Y (ladderInnerMass 1 lam Y) - selfInSigma Y (ladderInnerMass 1 lam Y)) -
      (selfInD2 Y (ladderInnerMass 1 Lam Y) - selfInSigma Y (ladderInnerMass 1 Lam Y))) *
      selfVm (√t) -
    oneLoopF2 1 (√t) * (ladderCtBracket lam Y - ladderCtBracket Lam Y))

/-- The `Y`-integrand of `scOutSRep`. -/
noncomputable def lamOutSInt (t lam Y : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, (selfGm (√t) lam Y x + selfK2 Y x / hOut t x ^ 2)) +
    selfInD2 Y (ladderInnerMass 1 lam Y) * selfVk (√t) +
      (selfInD2 Y (ladderInnerMass 1 lam Y) - selfInSigma Y (ladderInnerMass 1 lam Y)) *
        selfVm (√t) -
      oneLoopF2 1 (√t) * (Y * ((Y ^ 2 + 2 * Y - 2) / (2 * ladderInnerMass 1 lam Y) -
        log (ladderInnerMass 1 lam Y) / 2))

theorem scOutSRep_eq_lamOutSInt (t lam : ℝ) :
    scOutSRep t lam = 2 * ∫ Y in (0 : ℝ)..1, lamOutSInt t lam Y := rfl

/-- `G(√t, Λ) + k₂/h_t² = e₁ - ℓ log M_Λ`. -/
theorem lamOutS_integrand_eq (t Lam Y : ℝ) :
    (fun x => selfGm (√t) Lam Y x + selfK2 Y x / hOut t x ^ 2) =
      fun x => selfE1 (√t) Lam Y x - selfEll (√t) Y x * log (ladderInnerMass 1 Lam Y) := by
  funext x
  unfold selfE1 hOut
  ring

theorem lamOutS_intervalIntegrable_Lam {t Lam Y : ℝ} (ht : 0 < t) (hLam : 1 ≤ Lam)
    (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => selfGm (√t) Lam Y x + selfK2 Y x / hOut t x ^ 2) volume 0 1 := by
  rw [lamOutS_integrand_eq]
  exact (selfE1_x_bound hLam hY).1.sub
    ((integral_selfEll (sqrt_pos.2 ht) Y).1.mul_const _)

/-- **The `Y`-integrand at the large mass**: the logarithms of the self-energy subdivergence
cancel against `δ₂, δ_m` (`V_k + V_m + F₂ = 0`); the corner counterterm's `(Y/2) log M_Λ` is
left. -/
theorem lamOutSInt_eq {t Lam Y : ℝ} (ht : 0 < t) (hLam : 1 ≤ Lam) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    lamOutSInt t Lam Y = (∫ x in (0 : ℝ)..1, selfE1 (√t) Lam Y x) -
      oneLoopF2 1 (√t) * (Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y)) +
      oneLoopF2 1 (√t) * (Y / 2 * log (ladderInnerMass 1 Lam Y)) := by
  have hs : 0 < √t := sqrt_pos.2 ht
  have hM : 0 < ladderInnerMass 1 Lam Y :=
    ladderInnerMass_pos one_pos (by linarith) ⟨hY.1.le, hY.2.le⟩
  have hsum := selfVk_add_selfVm_add_oneLoopF2 hs
  obtain ⟨hiE, -⟩ := selfE1_x_bound (lam := √t) hLam hY
  obtain ⟨hiL, hL⟩ := integral_selfEll hs Y
  unfold lamOutSInt
  rw [lamOutS_integrand_eq, intervalIntegral.integral_sub hiE (hiL.mul_const _),
    intervalIntegral.integral_mul_const, hL]
  have hf : oneLoopF2 1 (√t) = -selfVk (√t) - selfVm (√t) := by linarith
  rw [hf]
  unfold selfInD2 selfInSigma
  field_simp
  ring

/-! ### Integrability in `Y` -/

theorem lamOutSInt_intervalIntegrable_lam {t lam : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1) :
    IntervalIntegrable (lamOutSInt t lam) volume 0 1 := by
  have hid := selfVk_add_selfVm_add_oneLoopF2 (sqrt_pos.2 ht)
  have iS := intervalIntegrable_integral_scOutRegS ht hl
  have iC : IntervalIntegrable
      (fun Y => regOutCtF (selfVk (√t)) (selfVm (√t)) (ladderInnerMass 1 lam Y) Y) volume 0 1 :=
    (intervalIntegrable_of_abs_le (measurable_regOutCtF _ _ lam) (regIntervalIntegrable_logY _ 1)
      fun Y hY => abs_regOutCtF_le hl hY).1
  refine (iS.add iC).congr_uIoo fun Y hY => ?_
  rw [uIoo_of_le zero_le_one] at hY
  have hM : ladderInnerMass 1 lam Y ≠ 0 :=
    ((pow_pos hY.1 2).trans_le (regMassOut_bounds hl hY).1).ne'
  simp only
  rw [← regOutCt_eq hid hM]
  unfold lamOutSInt
  simp only [scOutRegS]
  ring

/-- `∫₀¹ dY ∫₀¹ dx e₁(√t, Λ)`: integrability and the Phase 4 bound. -/
theorem lamOutS_E1_bound {t Lam : ℝ} (hLam : 1 ≤ Lam) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, selfE1 (√t) Lam Y x) volume 0 1 ∧
      |∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfE1 (√t) Lam Y x| ≤
        (20 + 9 * log Lam + 5 * log 2) / Lam ^ 2 := by
  have hg : IntervalIntegrable
      (fun Y => 5 * ((10 + 9 * log Lam + 5 * log 2) / 5 - log Y - log (1 - Y)) / Lam ^ 2)
      volume 0 1 := ((intervalIntegrable_ellY _).const_mul 5).div_const _
  obtain ⟨h1, h2⟩ := intervalIntegrable_of_abs_le
    (measurable_intervalIntegral_of_uncurry (measurable_selfE1_uncurry (√t) Lam)) hg
    fun Y hY => (selfE1_x_bound hLam hY).2.trans (le_of_eq (by ring))
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_ellY]
  ring

theorem lamOutS_rat_continuousOn {Lam : ℝ} (hLam : 0 < Lam) :
    ContinuousOn (fun Y => Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y)) (Icc 0 1) := by
  refine ContinuousOn.div (by fun_prop) (by unfold ladderInnerMass; fun_prop) fun Y hY => ?_
  have := ladderInnerMass_pos one_pos hLam hY
  positivity

theorem lamOutSInt_intervalIntegrable_Lam {t Lam : ℝ} (ht : 0 < t) (hLam : 1 ≤ Lam) :
    IntervalIntegrable (lamOutSInt t Lam) volume 0 1 := by
  have hL0 : 0 < Lam := by linarith
  have i1 := (lamOutS_E1_bound (t := t) hLam).1
  have i2 : IntervalIntegrable (fun Y => Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact lamOutS_rat_continuousOn hL0
  have i3 := intervalIntegrable_half_log hL0
  refine ((i1.sub (i2.const_mul (oneLoopF2 1 (√t)))).add
    (i3.const_mul (oneLoopF2 1 (√t)))).congr_uIoo fun Y hY => ?_
  rw [uIoo_of_le zero_le_one] at hY
  exact (lamOutSInt_eq ht hLam hY).symm

/-- **The self-energy part at finite `Λ` is the difference of the two inner masses.** -/
theorem scOutSReg_eq {t lam Lam : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1) (hLam : 1 ≤ Lam) :
    scOutSReg t lam Lam = scOutSRep t lam - scOutSRep t Lam := by
  rw [scOutSRep_eq_lamOutSInt, scOutSRep_eq_lamOutSInt, ← mul_sub,
    ← intervalIntegral.integral_sub (lamOutSInt_intervalIntegrable_lam ht hl)
      (lamOutSInt_intervalIntegrable_Lam ht hLam)]
  unfold scOutSReg
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
  rw [uIoc_of_le zero_le_one] at hY
  have hYo : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
  have il : IntervalIntegrable (fun x => selfGm (√t) lam Y x + selfK2 Y x / hOut t x ^ 2)
      volume 0 1 := (intervalIntegrable_scOutRegS ht hl hYo).1
  have iL := lamOutS_intervalIntegrable_Lam ht hLam hYo
  have e : (∫ x in (0 : ℝ)..1, (selfGm (√t) lam Y x - selfGm (√t) Lam Y x)) =
      ∫ x in (0 : ℝ)..1, ((selfGm (√t) lam Y x + selfK2 Y x / hOut t x ^ 2) -
        (selfGm (√t) Lam Y x + selfK2 Y x / hOut t x ^ 2)) := by
    congr 1
    funext x
    ring
  rw [e, intervalIntegral.integral_sub il iL]
  unfold lamOutSInt ladderCtBracket
  ring

/-! ### The self-energy part at the large mass -/

/-- **The self-energy part at inner mass `Λ`**: `scOutSRep t Λ = 2 ∬ e₁(√t, Λ)
- 2 F₂(√t) ∫ Y²(2 - Y)/(2 M_Λ) + F₂(√t) ∫ Y log M_Λ`; the last term is the corner counterterm's
inner logarithm. -/
theorem lamOutS_scOutSRep_eq {t Lam : ℝ} (ht : 0 < t) (hLam : 1 ≤ Lam) :
    scOutSRep t Lam = 2 * (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfE1 (√t) Lam Y x) -
      2 * oneLoopF2 1 (√t) *
        (∫ Y in (0 : ℝ)..1, Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y)) +
      oneLoopF2 1 (√t) * ∫ Y in (0 : ℝ)..1, Y * log (ladderInnerMass 1 Lam Y) := by
  have hL0 : 0 < Lam := by linarith
  set F := oneLoopF2 1 (√t)
  have i1 := (lamOutS_E1_bound (t := t) hLam).1
  have i2 : IntervalIntegrable (fun Y => Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact lamOutS_rat_continuousOn hL0
  have i3 := intervalIntegrable_half_log hL0
  rw [scOutSRep_eq_lamOutSInt]
  rw [intervalIntegral.integral_congr_ae (g := fun Y =>
      (∫ x in (0 : ℝ)..1, selfE1 (√t) Lam Y x) -
        F * (Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y)) +
        F * (Y / 2 * log (ladderInnerMass 1 Lam Y))) ?_,
    intervalIntegral.integral_add (i1.sub (i2.const_mul F)) (i3.const_mul F),
    intervalIntegral.integral_sub i1 (i2.const_mul F), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  · have e : ∫ Y in (0 : ℝ)..1, Y / 2 * log (ladderInnerMass 1 Lam Y) =
        1 / 2 * ∫ Y in (0 : ℝ)..1, Y * log (ladderInnerMass 1 Lam Y) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext Y
      ring
    rw [e]
    ring
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact lamOutSInt_eq ht hLam ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩

/-- `∫₀¹ Y²(2 - Y)/(2 M_Λ) dY → 0` as `Λ → ∞`. -/
theorem tendsto_lamOutS_rat :
    Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1, Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y))
      atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ))
    (F := fun Lam Y => Y ^ 2 * (2 - Y) / (2 * ladderInnerMass 1 Lam Y))
    (f := fun _ => (0 : ℝ)) (a := 0) (b := 1) (μ := volume) (fun _ => 1) ?_ ?_
    intervalIntegrable_const ?_
  · simp only [intervalIntegral.integral_zero] at h
    exact h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Lam hLam
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine (lamOutS_rat_continuousOn (by linarith)).mono ?_
    rw [uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  · refine Eventually.of_forall fun Lam => ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hM := ladderInnerMass_one_ge (lam := Lam) hY.2
    have hY2 : 0 < Y ^ 2 := pow_pos hY.1 2
    have h2Y : 0 ≤ 2 - Y := by linarith [hY.2]
    have hM0 : 0 < 2 * ladderInnerMass 1 Lam Y := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hY2.le h2Y) hM0.le),
      div_le_one hM0]
    nlinarith [hY.1, hY.2]
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hδ := lamOut_tendsto_sq_mul (lt_of_le_of_ne hY.2 hY1)
    have hM : Tendsto (fun Lam => 2 * ladderInnerMass 1 Lam Y) atTop atTop := by
      have := ((lamOut_tendsto_add_atTop (Y ^ 2 * 1 ^ 2) 0).comp hδ).const_mul_atTop
        (show (0 : ℝ) < 2 by norm_num)
      refine this.congr fun Lam => ?_
      simp only [Function.comp]
      unfold ladderInnerMass
      ring
    exact tendsto_const_nhds.div_atTop hM

end QED.ChainProof.SetCK
