/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.ChainBOuter
public import QED.Chain.ChainBValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (b): the `(m_γ, Λ)` limit, regulator decoupling in the product, and the value (O3-11–O3-13)

Helper-level analysis for obligations O3-11, O3-12 and the limit side of O3-13 of
`docs/HIGHER-LOOP-PLAN.md`, for the two-bubble functional `chainReg` of
`QED/Chain/ChainBOuter.lean`. It is **not** frozen and does not depend on any three-loop model.

## Objects

* `chainLim M₁ M₂ = ∫₀¹ (1-x) jSum(M₁, M₂, s)² dx`, `s = x²/(1-x)`: the `(m_γ, Λ)` limit of
  `chainReg` at fixed regulator masses.
* With `jSum = Π̂ + Δ_M` (`jSum_eq_piHat_add`), the cross terms
  `crossX1 M₁ M₂ = ∫₀¹ (1-x) 2Π̂(s) Δ_M(s) dx` and `crossX2 M₁ M₂ = ∫₀¹ (1-x) Δ_M(s)² dx`.

## Main statements

* `tendsto_chainReg` (**O3-11**): for `M₁, M₂ ≥ 1`, as `(m_γ, Λ) → (0⁺, ∞)` jointly,
  `chainReg m_γ Λ M₁ M₂ → chainLim M₁ M₂`. Dominated convergence: `x² s² D³ = (1-x)(sD)³` and
  `0 ≤ sD ≤ 1`, so the limit integrand itself dominates; it is integrable since `|jSum| ≤ 3Π̂`.
* `chainLim_eq_add_cross`: `chainLim = aSetB + crossX1 + crossX2`.
* `crossX1_bounds`, `crossX2_bounds` (**O3-12, cross terms**): for `M₁, M₂ ≥ 1`, with no
  constraint on `M₂/M₁`, `-K(M₁⁻² + M₂⁻²) ≤ crossX1 ≤ 0` and `0 ≤ crossX2 ≤ K(M₁⁻² + M₂⁻²)` with
  `K = (41 - 4π²)/135 = (2/15)∫₀¹ x²Π̂ ≈ 0.0112710`.
* `chainLim_sub_bounds`, `abs_chainLim_sub_le` (**O3-12, decoupling with a rate**): for
  `M₁, M₂ ≥ 1`, `-K(M₁⁻² + M₂⁻²) ≤ chainLim M₁ M₂ - aSetB ≤ 0`. The constant is the leading
  offset `κ = -K` of task T1 (section C.5 of `scripts/numerics/phase5_chains.py`), so the bound is
  asymptotically sharp; it has no logarithm.
* `tendsto_chainLim`, `tendsto_crossX1`, `tendsto_crossX2`: the limits as `M₁, M₂ → ∞` jointly
  along `atTop ×ˢ atTop`.
* `integral_chainFree` (**O3-13 side**): the regulator-free functional
  `∫₀¹ (1-x) specJ(1, s)² dx = ∫₀¹ (1-x) Π̂(x²/(1-x))² dx = aSetB`.
* `chainReg_iterated_limit` (**the D-37 order, regulators last**): for every `η > 0` there is `R`
  such that for all `M₁, M₂ > R` there are `δ > 0` and `Λ₀` with
  `|chainReg m_γ Λ M₁ M₂ - aSetB| < η` for `m_γ ∈ (0, δ)` and `Λ > Λ₀`.
* `chainOuter_iterated_limit`: the same for the outer functional
  `64π⁶ outerF2 (s ↦ (Π_e(s) - Π_e(0))² s² D³)` at unit charge, for every coefficient pair that
  satisfies the two Pauli–Villars conditions (the shape of
  `QED.Chain.HeavyVP.heavyOuter_iterated_limit`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.Chain.ChainB

open QED.TwoLoop.VPUnit QED.TwoLoop.UnitVPLink QED.Chain.HeavyVP QED.Chain

/-! ### Definitions -/

/-- **The `(m_γ, Λ)` limit of the two-bubble functional** at fixed regulator masses:
`∫₀¹ (1-x) jSum(M₁, M₂, s)² dx`, `s = x²/(1-x)`. -/
noncomputable def chainLim (M₁ M₂ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - x) * jSum M₁ M₂ (photonVar x) ^ 2

/-- The cross term `∫₀¹ (1-x) 2Π̂(s) Δ_M(s) dx`. -/
noncomputable def crossX1 (M₁ M₂ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - x) * (2 * piHat (photonVar x) * deltaM M₁ M₂ (photonVar x))

/-- The cross term `∫₀¹ (1-x) Δ_M(s)² dx`. -/
noncomputable def crossX2 (M₁ M₂ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - x) * deltaM M₁ M₂ (photonVar x) ^ 2

/-! ### Elementary facts on the photon curve -/

theorem one_sub_mul_photonVar {x : ℝ} (hx : x ≠ 1) : (1 - x) * photonVar x = x ^ 2 := by
  have h : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  unfold photonVar
  field_simp

theorem photonVar_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < photonVar x :=
  div_pos (pow_pos hx.1 2) (by linarith [hx.2])

theorem measurable_piHat : Measurable piHat := by
  have hF : Measurable
      (Function.uncurry fun (s t : ℝ) => t * (1 - t) * log (1 + t * (1 - t) * s)) := by
    change Measurable fun q : ℝ × ℝ => q.2 * (1 - q.2) * log (1 + q.2 * (1 - q.2) * q.1)
    fun_prop
  have h := (stronglyMeasurable_intervalIntegral hF).measurable.const_mul 2
  exact h

/-- The bound `(2/15)(M₁⁻² + M₂⁻²) x² Π̂(s)` of the cross-term integrands. -/
theorem cross_pointwise {M₁ M₂ x : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deltaM M₁ M₂ (photonVar x) ≤ 0 ∧
      -(2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) * (x ^ 2 * piHat (photonVar x))) ≤
        (1 - x) * (2 * piHat (photonVar x) * deltaM M₁ M₂ (photonVar x)) ∧
      (1 - x) * deltaM M₁ M₂ (photonVar x) ^ 2 ≤
        2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) * (x ^ 2 * piHat (photonVar x)) ∧
      -(2 * piHat (photonVar x)) ≤ deltaM M₁ M₂ (photonVar x) := by
  set s := photonVar x with hs
  have hs0 : 0 ≤ s := (photonVar_pos hx).le
  have h1x : 0 ≤ 1 - x := by linarith [hx.2]
  have hxs : (1 - x) * s = x ^ 2 := one_sub_mul_photonVar hx.2.ne
  obtain ⟨-, b2⟩ := deltaM_bounds h1 h2 hs0
  have ha := abs_deltaM_le h1 h2 hs0
  have hl := neg_two_piHat_le_deltaM h1 h2 hs0
  have hP := piHat_nonneg hs0
  set S := 1 / M₁ ^ 2 + 1 / M₂ ^ 2 with hS
  set d := deltaM M₁ M₂ s with hd
  rw [abs_of_nonpos b2] at ha
  -- `-d ≤ (s/15) S`
  have k1 : (1 - x) * (-d) ≤ (1 - x) * (s / 15 * S) := mul_le_mul_of_nonneg_left ha h1x
  have e1 : (1 - x) * (s / 15 * S) = x ^ 2 * S / 15 := by
    rw [← hxs]
    ring
  refine ⟨b2, ?_, ?_, hl⟩
  · have : (1 - x) * (2 * piHat s * d) = 2 * piHat s * ((1 - x) * d) := by ring
    rw [this]
    have k2 : 2 * piHat s * ((1 - x) * (-d)) ≤ 2 * piHat s * (x ^ 2 * S / 15) := by
      rw [← e1]
      exact mul_le_mul_of_nonneg_left k1 (by positivity)
    nlinarith
  · have hdd : d ^ 2 ≤ (-d) * (2 * piHat s) := by nlinarith
    have k3 : (1 - x) * d ^ 2 ≤ (1 - x) * (-d) * (2 * piHat s) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hdd h1x
    have k4 : (1 - x) * (-d) * (2 * piHat s) ≤ x ^ 2 * S / 15 * (2 * piHat s) := by
      rw [← e1]
      exact mul_le_mul_of_nonneg_right k1 (by positivity)
    have : x ^ 2 * S / 15 * (2 * piHat s) = 2 / 15 * S * (x ^ 2 * piHat s) := by ring
    linarith

/-! ### Integrability -/

theorem ae_mem_Ioo_Icc : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact ae_restrict_mem measurableSet_Ioo

theorem intervalIntegrable_piHat_sq :
    IntervalIntegrable (fun x => (1 - x) * piHat (photonVar x) ^ 2) volume 0 1 :=
  intervalIntegrable_setB

theorem intervalIntegrable_moment :
    IntervalIntegrable (fun x => x ^ 2 * piHat (photonVar x)) volume 0 1 :=
  intervalIntegrable_piHatMoment

/-- A function that is measurable and bounded a.e. on `(0,1)` by an interval-integrable
function is interval integrable. -/
theorem intervalIntegrable_of_bound {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : IntervalIntegrable g volume 0 1) (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ g x) :
    IntervalIntegrable f volume 0 1 := by
  refine hg.mono_fun hf.aestronglyMeasurable ?_
  rw [uIoc_of_le zero_le_one]
  filter_upwards [ae_mem_Ioo] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hb x hx).trans (le_abs_self _)

theorem measurable_comp_photonVar {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun x => f (photonVar x) := hf.comp measurable_photonVar

theorem intervalIntegrable_chainLim {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    IntervalIntegrable (fun x => (1 - x) * jSum M₁ M₂ (photonVar x) ^ 2) volume 0 1 := by
  refine intervalIntegrable_of_bound ?_ (intervalIntegrable_piHat_sq.const_mul 9) fun x hx => ?_
  · exact (measurable_const.sub measurable_id).mul
      ((measurable_comp_photonVar (measurable_jSum M₁ M₂)).pow_const 2)
  · have hs := (photonVar_pos hx).le
    have hj := abs_jSum_le h1 h2 hs
    have h1x : 0 ≤ 1 - x := by linarith [hx.2]
    have hP := piHat_nonneg hs
    have hsq : jSum M₁ M₂ (photonVar x) ^ 2 ≤ 9 * piHat (photonVar x) ^ 2 := by
      have := sq_le_sq' (neg_le_of_abs_le hj) (le_of_abs_le hj)
      nlinarith
    rw [abs_of_nonneg (mul_nonneg h1x (sq_nonneg _))]
    nlinarith

theorem intervalIntegrable_crossX1 {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    IntervalIntegrable (fun x => (1 - x) * (2 * piHat (photonVar x) *
      deltaM M₁ M₂ (photonVar x))) volume 0 1 := by
  refine intervalIntegrable_of_bound ?_
    (intervalIntegrable_moment.const_mul (2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2)))
    fun x hx => ?_
  · exact (measurable_const.sub measurable_id).mul
      ((measurable_const.mul (measurable_comp_photonVar measurable_piHat)).mul
        (measurable_comp_photonVar (measurable_deltaM M₁ M₂)))
  · obtain ⟨b, l, -, -⟩ := cross_pointwise h1 h2 hx
    have hs := (photonVar_pos hx).le
    have hP := piHat_nonneg hs
    have h1x : 0 ≤ 1 - x := by linarith [hx.2]
    have hn : (1 - x) * (2 * piHat (photonVar x) * deltaM M₁ M₂ (photonVar x)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1x (mul_nonpos_of_nonneg_of_nonpos (by positivity) b)
    rw [abs_of_nonpos hn]
    linarith

theorem intervalIntegrable_crossX2 {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    IntervalIntegrable (fun x => (1 - x) * deltaM M₁ M₂ (photonVar x) ^ 2) volume 0 1 := by
  refine intervalIntegrable_of_bound ?_
    (intervalIntegrable_moment.const_mul (2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2)))
    fun x hx => ?_
  · exact (measurable_const.sub measurable_id).mul
      ((measurable_comp_photonVar (measurable_deltaM M₁ M₂)).pow_const 2)
  · obtain ⟨-, -, u, -⟩ := cross_pointwise h1 h2 hx
    have h1x : 0 ≤ 1 - x := by linarith [hx.2]
    rw [abs_of_nonneg (mul_nonneg h1x (sq_nonneg _))]
    exact u

/-! ### The regulator-free functional and the split into cross terms -/

/-- **The regulator-free functional is set (b)** (O3-13 side):
`∫₀¹ (1-x) specJ(1, s)² dx = ∫₀¹ (1-x) Π̂(x²/(1-x))² dx = aSetB`. -/
theorem integral_chainFree :
    ∫ x in (0 : ℝ)..1, (1 - x) * specJ 1 (photonVar x) ^ 2 = aSetB := by
  rw [← integral_setB]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  rw [specJ_one_eq_piHat (by linarith [photonVar_nonneg hx])]
  rfl

/-- **The split.** For `M₁, M₂ ≥ 1`, `chainLim M₁ M₂ = aSetB + crossX1 M₁ M₂ + crossX2 M₁ M₂`. -/
theorem chainLim_eq_add_cross {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    chainLim M₁ M₂ = aSetB + crossX1 M₁ M₂ + crossX2 M₁ M₂ := by
  have hpt : ∀ x ∈ uIcc (0 : ℝ) 1, (1 - x) * jSum M₁ M₂ (photonVar x) ^ 2 =
      (1 - x) * piHat (photonVar x) ^ 2 +
        (1 - x) * (2 * piHat (photonVar x) * deltaM M₁ M₂ (photonVar x)) +
        (1 - x) * deltaM M₁ M₂ (photonVar x) ^ 2 := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    rw [jSum_eq_piHat_add (photonVar_nonneg hx)]
    ring
  unfold chainLim crossX1 crossX2
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add
    (intervalIntegrable_piHat_sq.add (intervalIntegrable_crossX1 h1 h2))
    (intervalIntegrable_crossX2 h1 h2), intervalIntegral.integral_add intervalIntegrable_piHat_sq
    (intervalIntegrable_crossX1 h1 h2)]
  congr 2
  exact integral_setB

/-! ### Decoupling of the regulator fermions in the product (O3-12) -/

theorem integral_moment_bound (M₁ M₂ : ℝ) :
    ∫ x in (0 : ℝ)..1, 2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) * (x ^ 2 * piHat (photonVar x)) =
      (41 - 4 * π ^ 2) / 135 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) := by
  rw [intervalIntegral.integral_const_mul]
  change 2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) * ∫ x in (0 : ℝ)..1, x ^ 2 * piHat (x ^ 2 / (1 - x)) = _
  rw [integral_piHatMoment]
  ring

/-- **The first cross term.** For `M₁, M₂ ≥ 1` (no constraint on `M₂/M₁`),
`-K(M₁⁻² + M₂⁻²) ≤ ∫₀¹ (1-x) 2Π̂ Δ_M ≤ 0` with `K = (41 - 4π²)/135`. -/
theorem crossX1_bounds {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    -((41 - 4 * π ^ 2) / 135 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2)) ≤ crossX1 M₁ M₂ ∧
      crossX1 M₁ M₂ ≤ 0 := by
  have hI := intervalIntegrable_crossX1 h1 h2
  have hB := intervalIntegrable_moment.const_mul (2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2))
  constructor
  · rw [← integral_moment_bound, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one hB.neg hI ?_
    filter_upwards [ae_mem_Ioo_Icc] with x hx
    exact (cross_pointwise h1 h2 hx).2.1
  · refine le_of_le_of_eq (intervalIntegral.integral_mono_ae_restrict zero_le_one hI
      (intervalIntegrable_const (c := (0 : ℝ))) ?_) (by simp)
    filter_upwards [ae_mem_Ioo_Icc] with x hx
    have b := (cross_pointwise h1 h2 hx).1
    have hP := piHat_nonneg (photonVar_pos hx).le
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.2])
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) b)

/-- **The second cross term.** For `M₁, M₂ ≥ 1` (no constraint on `M₂/M₁`),
`0 ≤ ∫₀¹ (1-x) Δ_M² ≤ K(M₁⁻² + M₂⁻²)` with `K = (41 - 4π²)/135`. -/
theorem crossX2_bounds {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    0 ≤ crossX2 M₁ M₂ ∧
      crossX2 M₁ M₂ ≤ (41 - 4 * π ^ 2) / 135 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) := by
  have hI := intervalIntegrable_crossX2 h1 h2
  have hB := intervalIntegrable_moment.const_mul (2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2))
  constructor
  · exact intervalIntegral.integral_nonneg zero_le_one fun x hx =>
      mul_nonneg (by linarith [hx.2]) (sq_nonneg _)
  · rw [← integral_moment_bound]
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one hI hB ?_
    filter_upwards [ae_mem_Ioo_Icc] with x hx
    exact (cross_pointwise h1 h2 hx).2.2.1

/-- **Decoupling of the regulator fermions in the product, with a rate.** For `M₁, M₂ ≥ 1`
(no constraint on `M₂/M₁`): `-K(M₁⁻² + M₂⁻²) ≤ chainLim M₁ M₂ - aSetB ≤ 0` with
`K = (41 - 4π²)/135 = (2/15)∫₀¹ x²Π̂`, the leading offset of task T1 (asymptotically sharp). -/
theorem chainLim_sub_bounds {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    -((41 - 4 * π ^ 2) / 135 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2)) ≤ chainLim M₁ M₂ - aSetB ∧
      chainLim M₁ M₂ - aSetB ≤ 0 := by
  have hI := (intervalIntegrable_crossX1 h1 h2).add (intervalIntegrable_crossX2 h1 h2)
  have hB := intervalIntegrable_moment.const_mul (2 / 15 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2))
  have hsum : chainLim M₁ M₂ - aSetB = ∫ x in (0 : ℝ)..1,
      ((1 - x) * (2 * piHat (photonVar x) * deltaM M₁ M₂ (photonVar x)) +
        (1 - x) * deltaM M₁ M₂ (photonVar x) ^ 2) := by
    rw [chainLim_eq_add_cross h1 h2, intervalIntegral.integral_add
      (intervalIntegrable_crossX1 h1 h2) (intervalIntegrable_crossX2 h1 h2)]
    unfold crossX1 crossX2
    ring
  rw [hsum]
  constructor
  · rw [← integral_moment_bound, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one hB.neg hI ?_
    filter_upwards [ae_mem_Ioo_Icc] with x hx
    obtain ⟨b, -, -, l⟩ := cross_pointwise h1 h2 hx
    have hs := (photonVar_pos hx).le
    have h1x : 0 ≤ 1 - x := by linarith [hx.2]
    have ha := abs_deltaM_le h1 h2 hs
    rw [abs_of_nonpos b] at ha
    have hxs : (1 - x) * photonVar x = x ^ 2 := one_sub_mul_photonVar hx.2.ne
    have hP := piHat_nonneg hs
    set d := deltaM M₁ M₂ (photonVar x)
    set P := piHat (photonVar x)
    set S := 1 / M₁ ^ 2 + 1 / M₂ ^ 2
    -- `(1-x) d (2P + d) ≥ (1-x) d · 2P ≥ -(1-x)(s/15)S · 2P`
    have k1 : (1 - x) * (-d) ≤ (1 - x) * (photonVar x / 15 * S) :=
      mul_le_mul_of_nonneg_left ha h1x
    have e1 : (1 - x) * (photonVar x / 15 * S) = x ^ 2 * S / 15 := by
      rw [← hxs]
      ring
    have k2 : (1 - x) * (-d) * (2 * P) ≤ x ^ 2 * S / 15 * (2 * P) := by
      rw [← e1]
      exact mul_le_mul_of_nonneg_right k1 (by positivity)
    have k3 : 0 ≤ (1 - x) * d ^ 2 := mul_nonneg h1x (sq_nonneg _)
    show -(2 / 15 * S * (x ^ 2 * P)) ≤ (1 - x) * (2 * P * d) + (1 - x) * d ^ 2
    nlinarith
  · refine le_of_le_of_eq (intervalIntegral.integral_mono_ae_restrict zero_le_one hI
      (intervalIntegrable_const (c := (0 : ℝ))) ?_) (by simp)
    filter_upwards [ae_mem_Ioo_Icc] with x hx
    obtain ⟨b, -, -, l⟩ := cross_pointwise h1 h2 hx
    have h1x : 0 ≤ 1 - x := by linarith [hx.2]
    have e : (1 - x) * (2 * piHat (photonVar x) * deltaM M₁ M₂ (photonVar x)) +
        (1 - x) * deltaM M₁ M₂ (photonVar x) ^ 2 =
        (1 - x) * (deltaM M₁ M₂ (photonVar x) *
          (2 * piHat (photonVar x) + deltaM M₁ M₂ (photonVar x))) := by ring
    show _ ≤ (0 : ℝ)
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos h1x (mul_nonpos_of_nonpos_of_nonneg b (by linarith))

/-- **Decoupling, absolute form.** For `M₁, M₂ ≥ 1`,
`|chainLim M₁ M₂ - aSetB| ≤ (41 - 4π²)/135 · (1/M₁² + 1/M₂²)`. -/
theorem abs_chainLim_sub_le {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    |chainLim M₁ M₂ - aSetB| ≤ (41 - 4 * π ^ 2) / 135 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) := by
  obtain ⟨b1, b2⟩ := chainLim_sub_bounds h1 h2
  rw [abs_of_nonpos b2]
  linarith

theorem tendsto_inv_sq_add :
    Tendsto (fun p : ℝ × ℝ => 1 / p.1 ^ 2 + 1 / p.2 ^ 2) (atTop ×ˢ atTop) (𝓝 0) := by
  have t1 : Tendsto (fun p : ℝ × ℝ => 1 / p.1 ^ 2) (atTop ×ˢ atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_fst)
  have t2 : Tendsto (fun p : ℝ × ℝ => 1 / p.2 ^ 2) (atTop ×ˢ atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_snd)
  simpa using t1.add t2

/-- A quantity bounded by `C(1/M₁² + 1/M₂²)` once `M₁, M₂ ≥ 1` tends to `0` jointly. -/
theorem tendsto_of_abs_le_inv_sq {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : ∀ M₁ M₂ : ℝ, 1 ≤ M₁ → 1 ≤ M₂ → |F M₁ M₂| ≤ C * (1 / M₁ ^ 2 + 1 / M₂ ^ 2)) :
    Tendsto (fun p : ℝ × ℝ => F p.1 p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have t := tendsto_inv_sq_add.const_mul C
  rw [mul_zero] at t
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ t
  filter_upwards [(eventually_ge_atTop 1).prod_inl atTop,
    (eventually_ge_atTop 1).prod_inr atTop] with p hp1 hp2
  rw [Real.norm_eq_abs]
  exact hF p.1 p.2 hp1 hp2

/-- **The first cross term tends to `0`** as `M₁, M₂ → ∞` jointly (no constraint on `M₂/M₁`). -/
theorem tendsto_crossX1 :
    Tendsto (fun p : ℝ × ℝ => crossX1 p.1 p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  refine tendsto_of_abs_le_inv_sq (C := (41 - 4 * π ^ 2) / 135) fun M₁ M₂ h1 h2 => ?_
  obtain ⟨b1, b2⟩ := crossX1_bounds h1 h2
  rw [abs_of_nonpos b2]
  linarith

/-- **The second cross term tends to `0`** as `M₁, M₂ → ∞` jointly. -/
theorem tendsto_crossX2 :
    Tendsto (fun p : ℝ × ℝ => crossX2 p.1 p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  refine tendsto_of_abs_le_inv_sq (C := (41 - 4 * π ^ 2) / 135) fun M₁ M₂ h1 h2 => ?_
  obtain ⟨b1, b2⟩ := crossX2_bounds h1 h2
  rw [abs_of_nonneg b1]
  exact b2

/-- **Decoupling, joint limit.** `chainLim M₁ M₂ → aSetB` as `M₁, M₂ → ∞` jointly. -/
theorem tendsto_chainLim :
    Tendsto (fun p : ℝ × ℝ => chainLim p.1 p.2) (atTop ×ˢ atTop) (𝓝 aSetB) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := tendsto_of_abs_le_inv_sq (F := fun M₁ M₂ => chainLim M₁ M₂ - aSetB)
    (C := (41 - 4 * π ^ 2) / 135) fun M₁ M₂ h1 h2 => abs_chainLim_sub_le h1 h2
  simpa [Real.norm_eq_abs] using h.abs

/-! ### The `(m_γ, Λ)` limit at fixed regulator masses (O3-11) -/

/-- `s D(s) → 1` as `(m_γ, Λ) → (0⁺, ∞)`, for `s > 0`. -/
theorem tendsto_mul_photonD {s : ℝ} (hs : 0 < s) :
    Tendsto (fun p : ℝ × ℝ => s * photonD p.1 p.2 s) (𝓝[>] 0 ×ˢ atTop) (𝓝 1) := by
  have ha : Tendsto (fun m : ℝ => s * (1 / (s + m ^ 2))) (𝓝 0) (𝓝 (s * (1 / (s + 0 ^ 2)))) := by
    have : ContinuousAt (fun m : ℝ => s * (1 / (s + m ^ 2))) 0 := by
      refine continuousAt_const.mul (continuousAt_const.div (by fun_prop) ?_)
      simp [hs.ne']
    exact this.tendsto
  have ha' := ha.comp ((tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := (atTop : Filter ℝ))).mono_right
    nhdsWithin_le_nhds)
  have hb : Tendsto (fun p : ℝ × ℝ => s * (1 / (s + p.2 ^ 2))) (𝓝[>] 0 ×ˢ atTop) (𝓝 (s * 0)) :=
    (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ s
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_snd))).const_mul s
  have h := ha'.sub hb
  have hv : s * (1 / (s + 0 ^ 2)) - s * 0 = 1 := by
    field_simp
    simp
  rw [hv] at h
  refine h.congr fun p => ?_
  simp only [Function.comp_apply, photonD]
  ring

/-- **O3-11: the joint `(m_γ, Λ)` limit at fixed regulator masses.** For `M₁, M₂ ≥ 1`, as
`(m_γ, Λ) → (0⁺, ∞)` jointly, `chainReg m_γ Λ M₁ M₂ → chainLim M₁ M₂`. -/
theorem tendsto_chainReg {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    Tendsto (fun p : ℝ × ℝ => chainReg p.1 p.2 M₁ M₂) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (chainLim M₁ M₂)) := by
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, 0 < p.1 ∧ p.1 ≤ p.2 := by
    have e1 : ∀ᶠ m in 𝓝[>] (0 : ℝ), m ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
    filter_upwards [e1.prod_inl atTop, (eventually_ge_atTop 1).prod_inr (𝓝[>] (0 : ℝ))]
      with p hp1 hp2
    exact ⟨hp1.1, hp1.2.le.trans hp2⟩
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by simp [ae_iff, measure_singleton]
  have hform : ∀ (p : ℝ × ℝ) {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 →
      x ^ 2 * (photonVar x ^ 2 * photonD p.1 p.2 (photonVar x) ^ 3 *
        jSum M₁ M₂ (photonVar x) ^ 2) =
      (1 - x) * (photonVar x * photonD p.1 p.2 (photonVar x)) ^ 3 *
        jSum M₁ M₂ (photonVar x) ^ 2 := by
    intro p x hx
    rw [← one_sub_mul_photonVar hx.2.ne]
    ring
  unfold chainReg chainLim
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => (1 - x) * jSum M₁ M₂ (photonVar x) ^ 2) ?_ ?_ (intervalIntegrable_chainLim h1 h2) ?_
  · refine Eventually.of_forall fun p => ?_
    exact ((measurable_id.pow_const 2).mul (((measurable_photonVar.pow_const 2).mul
      ((measurable_comp_photonVar (measurable_photonD p.1 p.2)).pow_const 3)).mul
      ((measurable_comp_photonVar (measurable_jSum M₁ M₂)).pow_const 2))).aestronglyMeasurable
  · filter_upwards [hev] with p hp
    filter_upwards [hne] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    obtain ⟨d0, d1⟩ := photonD_bounds hp.1 hp.2 (photonVar_pos hx').le
    have h1x : 0 ≤ 1 - x := by linarith [hx'.2]
    rw [hform p hx', Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hc : (photonVar x * photonD p.1 p.2 (photonVar x)) ^ 3 ≤ 1 := pow_le_one₀ d0 d1
    have := mul_le_mul_of_nonneg_left hc h1x
    have hJ := sq_nonneg (jSum M₁ M₂ (photonVar x))
    nlinarith
  · filter_upwards [hne] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have t := (((tendsto_mul_photonD (photonVar_pos hx')).pow 3).const_mul (1 - x)).mul_const
      (jSum M₁ M₂ (photonVar x) ^ 2)
    rw [one_pow, mul_one] at t
    exact t.congr fun p => (hform p hx').symm

/-! ### The iterated limit in the D-37 order -/

/-- **The iterated limit in the order of D-37.4 (regulator masses last).** For every `η > 0`
there is `R` such that for all `M₁, M₂ > R` there are `δ > 0` and `Λ₀` (depending on
`M₁, M₂`) with `|chainReg m_γ Λ M₁ M₂ - aSetB| < η` for all `m_γ ∈ (0, δ)` and `Λ > Λ₀`. -/
theorem chainReg_iterated_limit :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → |chainReg mγ Λ M₁ M₂ - aSetB| < η := by
  intro η hη
  refine ⟨1 + 4 / η, fun M₁ M₂ h1 h2 => ?_⟩
  have hη' : 0 < 4 / η := by positivity
  have small : ∀ M : ℝ, 1 + 4 / η < M → 1 / M ^ 2 < η / 4 := by
    intro M hM
    have hM0 : 0 < M := by linarith
    have hle : 1 / M ^ 2 ≤ 1 / M := one_div_le_one_div_of_le hM0 (by nlinarith)
    have hlt : 1 / M < η / 4 := by
      rw [div_lt_iff₀ hM0]
      have := (div_lt_iff₀ hη).1 (show 4 / η < M by linarith)
      linarith
    linarith
  have hK0 : 0 ≤ π ^ 2 := sq_nonneg π
  have hK : (41 - 4 * π ^ 2) / 135 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    linarith
  have s1 := small M₁ h1
  have s2 := small M₂ h2
  have hpos : 0 ≤ 1 / M₁ ^ 2 + 1 / M₂ ^ 2 := by positivity
  have key := abs_chainLim_sub_le (M₁ := M₁) (M₂ := M₂) (by linarith) (by linarith)
  have hL : |chainLim M₁ M₂ - aSetB| < η / 2 := by
    have : (41 - 4 * π ^ 2) / 135 * (1 / M₁ ^ 2 + 1 / M₂ ^ 2) ≤ 1 / M₁ ^ 2 + 1 / M₂ ^ 2 := by
      nlinarith
    linarith
  have hT := (Metric.tendsto_nhds.1 (tendsto_chainReg (M₁ := M₁) (M₂ := M₂) (by linarith)
    (by linarith))) (η / 2) (by positivity)
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := eventually_prod_iff.1 hT
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hpa
  obtain ⟨Λ₀, hΛ₀⟩ := eventually_atTop.1 hpb
  refine ⟨u, hu, Λ₀, fun mγ Λ hm0 hm1 hΛ => ?_⟩
  have hd := hall (hsub ⟨hm0, hm1⟩) (hΛ₀ Λ hΛ.le)
  rw [Real.dist_eq] at hd
  have := abs_sub_le (chainReg mγ Λ M₁ M₂) (chainLim M₁ M₂) aSetB
  linarith

/-- **The set (b) outer functional tends to `aSetB` in the order of D-37.4.** At unit charge,
for every `η > 0` there is `R` such that for all `M₁, M₂ > R` there are `δ > 0` and `Λ₀` such
that for all `m_γ ∈ (0, δ)`, `Λ > Λ₀` and every pair `c₁, c₂` satisfying the Pauli–Villars
conditions of loop mass `1`,
`|64π⁶ outerF2 (s ↦ (Π_e(s) - Π_e(0))² s² D(s)³) - aSetB| < η`. -/
theorem chainOuter_iterated_limit :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ c₁ c₂ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → 1 + c₁ + c₂ = 0 →
        1 ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
        |64 * π ^ 6 * outerF2 (fun s =>
            (heavyPi 1 1 M₁ M₂ c₁ c₂ s - heavyPi 1 1 M₁ M₂ c₁ c₂ 0) ^ 2 * s ^ 2 *
              photonD mγ Λ s ^ 3) - aSetB| < η := by
  intro η hη
  obtain ⟨R, hR⟩ := chainReg_iterated_limit η hη
  refine ⟨max R 1, fun M₁ M₂ h1 h2 => ?_⟩
  have hM₁ : 1 < M₁ := lt_of_le_of_lt (le_max_right _ _) h1
  have hM₂ : 1 < M₂ := lt_of_le_of_lt (le_max_right _ _) h2
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hR M₁ M₂ (lt_of_le_of_lt (le_max_left _ _) h1)
    (lt_of_le_of_lt (le_max_left _ _) h2)
  refine ⟨δ, hδ, Λ₀, fun mγ Λ c₁ c₂ hm0 hm1 hΛ hPV₁ hPV₂ => ?_⟩
  rw [chainOuter_eq_chainReg hM₁ hM₂ hPV₁ hPV₂, one_pow, one_mul]
  exact hΛ₀ mγ Λ hm0 hm1 hΛ

end QED.Chain.ChainB
