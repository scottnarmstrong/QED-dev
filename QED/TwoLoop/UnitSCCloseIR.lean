/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLLinkLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The infrared cancellation of the `S + C` counterterms at every photon mass

Sections 5.2 and 7 of `docs/TWO-LOOP-UNITS.md`. The `δ₂`, `δ_m` insertions on an internal electron
line of the one-loop vertex contribute, per unit `d₂` and `d_m`, the Pauli coefficients
(eq. of section 5.2, at `m = 1`, photon mass `μ`, `M = x² + (1-x) μ²`)

`V_k(μ) = ∫₀¹ x²(x-1)(3x³ + 3x² + μ²(2 + 2x - 4x²))/(2M²) dx`,
`V_m(μ) = ∫₀¹ x²(1-x)(2x² + 3μ²(1-x))/(2M²) dx`

(`selfVk`, `selfVm`), and `F₂⁽²⁾(μ) = ∫₀¹ x²(1-x)/M dx` (`QED.TwoLoop.UnitLLink.oneLoopF2`). With
the Ward identity `δ₁ = δ₂` the counterterms of `S + C` are `2δ₂ [V_k + V_m + F₂⁽²⁾] - 2σ V_m`
(section 7), each bracket a Pauli–Villars difference over `μ ∈ {m_γ, Λ}`. This file proves:

* `selfVk_add_selfVm_add_oneLoopF2`: **`V_k(μ) + V_m(μ) + F₂⁽²⁾(μ) = 0` for every `μ > 0`**, not
  only as `μ → 0`: the combined integrand is the derivative of `x³(1-x)²/(2M)`, which vanishes at
  both ends (`hasDerivAt_irPrim`). So the infrared-divergent constant `δ₂` multiplies exactly zero
  at both photon masses, and the `S + C` counterterms reduce to `-2σ (V_m(m_γ) - V_m(Λ))` with
  `σ = δ₂ - δ_m` infrared finite. This is the mechanism by which `S + C` carries no
  `(m²/Λ²) log m_γ` remainder (section 8, item 11, of the document; section 11.3 of
  `docs/TWO-LOOP-DERIVATION.md` observed it numerically): the obstruction to the joint limit for
  `S` and `C` separately cancels identically in the sum.
* `tendsto_selfVm`: `V_m(λ) → 1/2` as `λ → 0⁺` (dominated convergence, `|integrand| ≤ 3(1-x)`);
  hence `tendsto_selfVk`: `V_k(λ) → -1`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitSCClose

open QED.TwoLoop.UnitLLink

/-- The integrand of `V_k(μ)`: `x²(x-1)(3x³ + 3x² + μ²(2 + 2x - 4x²))/(2M²)`. -/
noncomputable def vkIntegrand (μ x : ℝ) : ℝ :=
  x ^ 2 * (x - 1) * (3 * x ^ 3 + 3 * x ^ 2 + μ ^ 2 * (2 + 2 * x - 4 * x ^ 2)) /
    (2 * ladderInnerMass 1 μ x ^ 2)

/-- The integrand of `V_m(μ)`: `x²(1-x)(2x² + 3μ²(1-x))/(2M²)`. -/
noncomputable def vmIntegrand (μ x : ℝ) : ℝ :=
  x ^ 2 * (1 - x) * (2 * x ^ 2 + 3 * μ ^ 2 * (1 - x)) / (2 * ladderInnerMass 1 μ x ^ 2)

/-- **The `δ₂` insertion per unit `d₂`** (`k̸` part, section 5.2 of the document). -/
noncomputable def selfVk (μ : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, vkIntegrand μ x

/-- **The `δ_m` insertion per unit `d_m`** (section 5.2 of the document). -/
noncomputable def selfVm (μ : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, vmIntegrand μ x

/-- The primitive `x³(1-x)²/(2M)` of the combined integrand. -/
noncomputable def irPrim (μ x : ℝ) : ℝ := x ^ 3 * (1 - x) ^ 2 / (2 * ladderInnerMass 1 μ x)

theorem continuousOn_div_mass {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ContinuousOn (fun x => f x / (2 * ladderInnerMass 1 μ x ^ n)) (Icc 0 1) := by
  refine ContinuousOn.div hf.continuousOn (by unfold ladderInnerMass; fun_prop) fun x hx => ?_
  have := ladderInnerMass_pos one_pos hμ hx
  positivity

theorem intervalIntegrable_vkIntegrand {μ : ℝ} (hμ : 0 < μ) :
    IntervalIntegrable (vkIntegrand μ) volume 0 1 :=
  (continuousOn_div_mass hμ (by fun_prop) 2).intervalIntegrable_of_Icc zero_le_one

theorem intervalIntegrable_vmIntegrand {μ : ℝ} (hμ : 0 < μ) :
    IntervalIntegrable (vmIntegrand μ) volume 0 1 :=
  (continuousOn_div_mass hμ (by fun_prop) 2).intervalIntegrable_of_Icc zero_le_one

/-- **The combined integrand is a derivative**:
`d/dx [x³(1-x)²/(2M)] = V_k-integrand + V_m-integrand + x²(1-x)/M`. -/
theorem hasDerivAt_irPrim {μ x : ℝ} (hM : 0 < ladderInnerMass 1 μ x) :
    HasDerivAt (irPrim μ) (vkIntegrand μ x + vmIntegrand μ x +
      x ^ 2 * (1 - x) * 1 ^ 2 / ladderInnerMass 1 μ x) x := by
  have hMd : HasDerivAt (fun x => 2 * ladderInnerMass 1 μ x) (2 * (2 * x - μ ^ 2)) x := by
    unfold ladderInnerMass
    have := (((hasDerivAt_pow 2 x).mul_const ((1 : ℝ) ^ 2)).add
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul_const (μ ^ 2))).const_mul 2
    refine this.congr_deriv ?_
    simp
    ring
  have hN : HasDerivAt (fun x : ℝ => x ^ 3 * (1 - x) ^ 2)
      (3 * x ^ 2 * (1 - x) ^ 2 - 2 * x ^ 3 * (1 - x)) x := by
    have := (hasDerivAt_pow 3 x).mul (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow 2)
    refine this.congr_deriv ?_
    simp
    ring
  have h := hN.div hMd (by positivity)
  refine h.congr_deriv ?_
  unfold vkIntegrand vmIntegrand
  have hM0 := hM.ne'
  unfold ladderInnerMass at hM0 ⊢
  field_simp
  ring

/-- **The infrared cancellation at every photon mass**: `V_k(μ) + V_m(μ) + F₂⁽²⁾(μ) = 0`. -/
theorem selfVk_add_selfVm_add_oneLoopF2 {μ : ℝ} (hμ : 0 < μ) :
    selfVk μ + selfVm μ + oneLoopF2 1 μ = 0 := by
  have hM : ∀ x ∈ Icc (0 : ℝ) 1, 0 < ladderInnerMass 1 μ x := fun x hx =>
    ladderInnerMass_pos one_pos hμ hx
  have hi := ((intervalIntegrable_vkIntegrand hμ).add (intervalIntegrable_vmIntegrand hμ)).add
    (intervalIntegrable_oneLoopF2_integrand one_pos hμ)
  have hc : ContinuousOn (irPrim μ) (Icc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by unfold ladderInnerMass; fun_prop) fun x hx => ?_
    have := hM x hx
    positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc
    (fun x hx => hasDerivAt_irPrim (hM x ⟨hx.1.le, hx.2.le⟩)) hi
  rw [selfVk, selfVm, oneLoopF2, ← intervalIntegral.integral_add
    (intervalIntegrable_vkIntegrand hμ) (intervalIntegrable_vmIntegrand hμ),
    ← intervalIntegral.integral_add ((intervalIntegrable_vkIntegrand hμ).add
      (intervalIntegrable_vmIntegrand hμ)) (intervalIntegrable_oneLoopF2_integrand one_pos hμ)]
  rw [hFTC]
  simp [irPrim]

/-! ### The limits `λ → 0⁺` -/

theorem abs_vmIntegrand_le {μ x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    |vmIntegrand μ x| ≤ 3 * (1 - x) := by
  have hx0 := hx.1
  have h1x : 0 ≤ 1 - x := by linarith [hx.2]
  have hge : x ^ 2 ≤ ladderInnerMass 1 μ x := ladderInnerMass_one_ge hx.2
  have hge' : (1 - x) * μ ^ 2 ≤ ladderInnerMass 1 μ x := by
    unfold ladderInnerMass; nlinarith [sq_nonneg x]
  have hM : 0 < ladderInnerMass 1 μ x := lt_of_lt_of_le (by positivity) hge
  unfold vmIntegrand
  rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have e1 : x ^ 2 * (1 - x) * (2 * x ^ 2) ≤ 2 * (1 - x) * ladderInnerMass 1 μ x ^ 2 := by
    have : x ^ 2 * x ^ 2 ≤ ladderInnerMass 1 μ x * ladderInnerMass 1 μ x :=
      mul_le_mul hge hge (by positivity) hM.le
    nlinarith
  have e2 : x ^ 2 * (1 - x) * (3 * μ ^ 2 * (1 - x)) ≤
      3 * (1 - x) * ladderInnerMass 1 μ x ^ 2 := by
    have : x ^ 2 * ((1 - x) * μ ^ 2) ≤ ladderInnerMass 1 μ x * ladderInnerMass 1 μ x :=
      mul_le_mul hge hge' (by positivity) hM.le
    nlinarith
  nlinarith

theorem tendsto_vmIntegrand {x : ℝ} (hx : 0 < x) :
    Tendsto (fun lam => vmIntegrand lam x) (𝓝 0) (𝓝 (1 - x)) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hc : ContinuousAt (fun lam => vmIntegrand lam x) 0 := by
    unfold vmIntegrand ladderInnerMass
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hx0])
  convert hc.tendsto using 2
  simp only [vmIntegrand, ladderInnerMass]
  field_simp
  ring

/-- **`V_m(λ) → 1/2` as `λ → 0⁺`.** -/
theorem tendsto_selfVm : Tendsto selfVm (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hlim : ∫ x in (0 : ℝ)..1, (1 - x) = 1 / 2 := by
    simp only [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id, integral_id, intervalIntegral.integral_const]
    norm_num
  rw [← hlim]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun x => 3 * (1 - x))
    ?_ ?_ ((intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_id).const_mul 3) ?_
  · refine Eventually.of_forall fun lam => ?_
    exact (by unfold vmIntegrand ladderInnerMass; fun_prop :
      Measurable fun x : ℝ => vmIntegrand lam x).aestronglyMeasurable
  · refine Eventually.of_forall fun lam => ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs]
    exact abs_vmIntegrand_le hx
  · refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    exact (tendsto_vmIntegrand hx.1).mono_left nhdsWithin_le_nhds

/-- **`V_k(λ) → -1` as `λ → 0⁺`**, from the cancellation identity. -/
theorem tendsto_selfVk : Tendsto selfVk (𝓝[>] 0) (𝓝 (-1)) := by
  have h := (tendsto_selfVm.add tendsto_oneLoopF2_one).neg
  have e : -(1 / 2 + 1 / 2 : ℝ) = -1 := by norm_num
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam (hlam : 0 < lam)
  have := selfVk_add_selfVm_add_oneLoopF2 hlam
  linarith

end QED.TwoLoop.UnitSCClose

end
