/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitSMasters
public import QED.TwoLoop.UnitSCLimitCMasters
public import QED.TwoLoop.UnitSCCloseIR
public import QED.TwoLoop.WardIdentity
public import QED.TwoLoop.HeadlineAssemblyUnits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The unit `S + C` at finite regulators, and the link given the `δ₂, δ_m` half

Section 7 of `docs/TWO-LOOP-UNITS.md`. With the graph halves after the integration over the outer
electron parameter (`QED.TwoLoop.UnitSCLimit.sixteen_pi_pow_four_mul_unitF2_S_eq_gsum`,
`QED.TwoLoop.UnitSCLimit.sixteen_pi_pow_four_mul_unitF2_C_eq_gsum`) and the counterterm halves,
`S + C` is a real function of the two regulator masses alone:

`SC(λ, Λ) = 2 ∫∫ G_Σ^S + 2 ∫_{y₃,y₄} ∫ G_Σ^C - Σ(λ, Λ) (V_m(λ) - V_m(Λ))` (`scTotal`),
`Σ(λ, Λ) = ∫₀¹ (1 + x) log(M_Λ(x)/M_λ(x)) dx` (`scMassCt`), `M_μ = x² + (1-x) μ²`.

The counterterms combine as in section 7 of the document: with the `δ₂, δ_m` half
`8π² (d₂ ΔV_k + d_m ΔV_m)` (the formula `SCtHalfFormula`, evaluated by a parallel worker), the
`δ₁` half `2δ₁ ΔF₂⁽²⁾ = 8π² d₁ ΔF₂⁽²⁾`, the Ward identity `d₁ = d₂` and
`V_k + V_m + F₂⁽²⁾ = 0` at both photon masses, only `8π² (d_m - d₂) ΔV_m` survives, and on shell
`8π² (d_m - d₂) = -Σ(λ, Λ)` (`eight_pi_sq_mul_dm_sub_d₂`), which is infrared finite. This file
proves:

* `sixteen_pi_pow_four_mul_unitF2_SC_eq`: given `SCtHalfFormula`, for `m = 1`,
  `0 < m_γ < Λ`, `m_γ ≤ 1`, the electron on shell and the charge condition,
  `16π⁴ (unitF2 S P₁ + unitF2 C P₁) = SC(m_γ, Λ)`;
* `scUnitLimitOne_of_sCtHalf`: **the `S + C` link** `SCUnitLimitOne`, given `SCtHalfFormula` and
  the joint limit `SC(λ, Λ) → -7/3 + 2 ζ(2) log 2 - ζ(3)/2` (`SCTotalLimit`).

`SCTotalLimit` is a statement about explicit real integrals; it is the remaining analytic part of
the link (stages 2–4 of the plan: the `log M_Λ` cancellation, the bounds uniform in the regulators
and the joint limit, and the `x`- and `ξ`-integrations down to `selfEnergyKernel` and
`cornerKernel`).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.TwoLoop.UnitSCLimit

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCReduce QED.WickModel QED.TwoLoop.UnitsRegulated
open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitSCClose QED.TwoLoop.HeadlineAssembly

/-! ### The real function `SC(λ, Λ)` -/

/-- **The mass-counterterm integral** `Σ(λ, Λ) = ∫₀¹ (1 + x) log(M_Λ(x)/M_λ(x)) dx`
(`= 2σ` of section 7 of the document). -/
noncomputable def scMassCt (mγ Λ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 + x) * log (ladderInnerMass 1 Λ x / ladderInnerMass 1 mγ x)

/-- **The unit `S + C` at finite regulators** as a real function of the photon masses:
`2 ∫∫ G_Σ^S + 2 ∫_{y₃,y₄} ∫ G_Σ^C - Σ(λ, Λ) (V_m(λ) - V_m(Λ))`. -/
noncomputable def scTotal (mγ Λ : ℝ) : ℝ :=
  2 * (∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, selfGSum mγ Λ Y x) +
    2 * (∫ p in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGSum mγ Λ p.1 p.2 x) -
    scMassCt mγ Λ * (selfVm mγ - selfVm Λ)

/-! ### The counterterms -/

/-- **The pinned `δ₂, δ_m` half of the unit `S`** (hypothesis; evaluated by a parallel worker): at
`m = 1`, `0 < m_γ < Λ`, `16π⁴ sCtHalf P₁ = 8π² (d₂ (V_k(m_γ) - V_k(Λ)) + d_m (V_m(m_γ) - V_m(Λ)))`,
`P₁ = atUnitCharge P d₁ d₂ d_m d₃`. -/
def SCtHalfFormula : Prop :=
  ∀ (P : Params), P.m = 1 → 0 < P.mγ → P.mγ < P.Λ → ∀ d₁ d₂ dm d₃ : ℝ,
    16 * (π : ℂ) ^ 4 * sCtHalf (atUnitCharge P d₁ d₂ dm d₃) =
      ((8 * π ^ 2 * (d₂ * (selfVk P.mγ - selfVk P.Λ) + dm * (selfVm P.mγ - selfVm P.Λ)) : ℝ) : ℂ)

theorem selfEnergyFeynmanMass_one {μ x : ℝ} :
    selfEnergyFeynmanMass 1 μ (-1 ^ 2) x = ladderInnerMass 1 μ x := by
  unfold selfEnergyFeynmanMass ladderInnerMass; ring

theorem intervalIntegrable_logMassRatio {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) (w : ℝ → ℝ)
    (hw : Continuous w) :
    IntervalIntegrable (fun x => w x * log (ladderInnerMass 1 Λ x / ladderInnerMass 1 mγ x))
      volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
  have h1 : ContinuousOn (fun x => ladderInnerMass 1 Λ x) (Icc 0 1) := by
    unfold ladderInnerMass; fun_prop
  have h2 : ContinuousOn (fun x => ladderInnerMass 1 mγ x) (Icc 0 1) := by
    unfold ladderInnerMass; fun_prop
  refine hw.continuousOn.mul ((h1.div h2 fun x hx => (ladderInnerMass_pos one_pos hmγ hx).ne').log
    fun x hx => ?_)
  exact (div_pos (ladderInnerMass_pos one_pos hΛ hx) (ladderInnerMass_pos one_pos hmγ hx)).ne'

/-- **On shell, `8π² (d_m - d₂) = -Σ(m_γ, Λ)`** (`m = e = 1`): the mass counterterm minus the
wave-function counterterm, `B(-m²) - A(-m²)`, in the variables of section 5.2 of the document. -/
theorem eight_pi_sq_mul_dm_sub_d₂ (P : Params) (hm0 : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hm : P.m = 1) {d₁ d₂ dm d₃ : ℝ}
    (hel : IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm0 hmγ hΛ) :
    8 * π ^ 2 * (dm - d₂) = -scMassCt P.mγ P.Λ := by
  obtain ⟨h2, hmm⟩ := (QED.TwoLoop.Ward.isElectronOnShell_iff (atUnitCharge P d₁ d₂ dm d₃) hm0 hmγ hΛ).1 hel
  have hdiff : dm - d₂ = (selfEnergyLoopB (atUnitCharge P d₁ d₂ dm d₃)
      (-(atUnitCharge P d₁ d₂ dm d₃).m ^ 2)).re - (selfEnergyLoopA (atUnitCharge P d₁ d₂ dm d₃)
      (-(atUnitCharge P d₁ d₂ dm d₃).m ^ 2)).re := by
    have e0 : dm - d₂ = onShellδm (atUnitCharge P d₁ d₂ dm d₃) -
        onShellδ₂ (atUnitCharge P d₁ d₂ dm d₃) := congrArg₂ (· - ·) hmm h2
    rw [e0]
    unfold onShellδm onShellδ₂
    ring
  rw [hdiff]
  simp only [selfEnergyLoopA, selfEnergyLoopB, Complex.ofReal_re, atUnitCharge]
  rw [hm]
  simp only [selfEnergyFeynmanMass_one]
  have hI1 := intervalIntegrable_logMassRatio hmγ hΛ (fun _ => 1) continuous_const
  have hIx := intervalIntegrable_logMassRatio hmγ hΛ (fun x => x) continuous_id
  have e1 : ∫ x in (0 : ℝ)..1, (1 - x) * log (ladderInnerMass 1 P.Λ x / ladderInnerMass 1 P.mγ x) =
      (∫ x in (0 : ℝ)..1, 1 * log (ladderInnerMass 1 P.Λ x / ladderInnerMass 1 P.mγ x)) -
        ∫ x in (0 : ℝ)..1, x * log (ladderInnerMass 1 P.Λ x / ladderInnerMass 1 P.mγ x) := by
    rw [← intervalIntegral.integral_sub hI1 hIx]
    congr 1; funext x; ring
  have e2 : scMassCt P.mγ P.Λ =
      (∫ x in (0 : ℝ)..1, 1 * log (ladderInnerMass 1 P.Λ x / ladderInnerMass 1 P.mγ x)) +
        ∫ x in (0 : ℝ)..1, x * log (ladderInnerMass 1 P.Λ x / ladderInnerMass 1 P.mγ x) := by
    rw [scMassCt, ← intervalIntegral.integral_add hI1 hIx]
    congr 1; funext x; ring
  have e3 : ∫ x in (0 : ℝ)..1, log (ladderInnerMass 1 P.Λ x / ladderInnerMass 1 P.mγ x) =
      ∫ x in (0 : ℝ)..1, 1 * log (ladderInnerMass 1 P.Λ x / ladderInnerMass 1 P.mγ x) := by
    simp only [one_mul]
  rw [e1, e2, e3]
  have hπ : π ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The unit `S + C` at finite regulators** (`m = 1`, `0 < m_γ < Λ`, `m_γ ≤ 1`, the electron on
shell and the charge condition at charge `1`), given the `δ₂, δ_m` half:
`16π⁴ (unitF2 S P₁ + unitF2 C P₁) = SC(m_γ, Λ)`. -/
theorem sixteen_pi_pow_four_mul_unitF2_SC_eq (hct : SCtHalfFormula) (P : Params) (hm0 : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ0 : 0 < P.Λ) (hm : P.m = 1) (hlt : P.mγ < P.Λ) (hmγ1 : P.mγ ≤ 1)
    {d₁ d₂ dm d₃ : ℝ} (hel : IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm0 hmγ hΛ0)
    (hch : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm0 hmγ hΛ0) :
    16 * (π : ℂ) ^ 4 * (unitF2 .S (atUnitCharge P d₁ d₂ dm d₃) +
        unitF2 .C (atUnitCharge P d₁ d₂ dm d₃)) = ((scTotal P.mγ P.Λ : ℝ) : ℂ) := by
  have hS := sixteen_pi_pow_four_mul_unitF2_S_eq_gsum P hm hmγ hlt d₁ d₂ dm d₃
  have hC := sixteen_pi_pow_four_mul_unitF2_C_eq_gsum P hm hm0 hmγ hΛ0 hlt hmγ1 (d₂ := d₂)
    (dm := dm) (d₃ := d₃) hch
  have hct' := hct P hm hmγ hlt d₁ d₂ dm d₃
  have hδ := four_pi_sq_mul_eq_ladderDeltaOne hm0 hmγ hΛ0 hch
  have hd : d₁ = d₂ := QED.TwoLoop.Ward.δ₁_eq_δ₂_of_isChargeNormalized
    (atUnitCharge P d₁ d₂ dm d₃) one_ne_zero hm0 hmγ hΛ0 hel hch
  have hdm := eight_pi_sq_mul_dm_sub_d₂ P hm0 hmγ hΛ0 hm hel
  have hIRa := selfVk_add_selfVm_add_oneLoopF2 hmγ
  have hIRb := selfVk_add_selfVm_add_oneLoopF2 hΛ0
  rw [mul_add, hS, hC, hct', hm]
  rw [hm] at hδ
  have key : 2 * (∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, selfGSum P.mγ P.Λ Y x) +
      8 * π ^ 2 * (d₂ * (selfVk P.mγ - selfVk P.Λ) + dm * (selfVm P.mγ - selfVm P.Λ)) +
      (2 * (∫ p in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGSum P.mγ P.Λ p.1 p.2 x) +
        2 * (ladderDeltaOne 1 P.mγ P.Λ * (oneLoopF2 1 P.mγ - oneLoopF2 1 P.Λ))) =
      scTotal P.mγ P.Λ := by
    rw [scTotal, ← hδ, hd, show selfVk P.mγ = -selfVm P.mγ - oneLoopF2 1 P.mγ by linarith,
      show selfVk P.Λ = -selfVm P.Λ - oneLoopF2 1 P.Λ by linarith,
      show scMassCt P.mγ P.Λ = -(8 * π ^ 2 * (dm - d₂)) by linarith]
    ring
  rw [← key]
  push_cast
  ring

/-! ### The link -/

/-- **The joint limit of `SC(λ, Λ)`** (the remaining analytic statement):
`SC(λ, Λ) → -7/3 + 2 ζ(2) log 2 - ζ(3)/2` as `(λ, Λ) → (0⁺, ∞)`. -/
def SCTotalLimit : Prop :=
  Tendsto (fun p : ℝ × ℝ => scTotal p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
    (𝓝 (-(7 / 3) + 2 * (π ^ 2 / 6) * Real.log 2 - QED.Polylog.zeta3 / 2))

/-- **The `S + C` link at `m = 1`, given the `δ₂, δ_m` half and the joint limit of `SC(λ, Λ)`.** -/
theorem scUnitLimitOne_of_sCtHalf (hct : SCtHalfFormula) (hlim : SCTotalLimit) :
    SCUnitLimitOne := by
  intro η hη
  have hT := Metric.tendsto_nhds.mp hlim η hη
  obtain ⟨pa, hpa, pb, hpb, hp⟩ := eventually_prod_iff.mp hT
  obtain ⟨ε, hε, hεa⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpa)
  obtain ⟨a, ha⟩ := eventually_atTop.mp hpb
  refine ⟨min ε 1, lt_min hε one_pos, max a 1,
    fun P hm hmγ hΛ hm1 hδ hR d₁ d₂ dm d₃ hel hch => ?_⟩
  have hlt : P.mγ < P.Λ := by
    have := min_le_right ε 1
    have := le_max_right a 1
    linarith
  have hmγ1 : P.mγ ≤ 1 := (lt_of_lt_of_le hδ (min_le_right ε 1)).le
  rw [sixteen_pi_pow_four_mul_unitF2_SC_eq hct P hm hmγ hΛ hm1 hlt hmγ1 hel hch,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← Real.dist_eq]
  refine hp (hεa ?_ hmγ) (ha _ ((le_max_left a 1).trans hR.le))
  rw [Real.dist_eq, sub_zero, abs_of_pos hmγ]
  exact lt_of_lt_of_le hδ (min_le_left ε 1)

/-- **The `S + C` link at every mass**, given the `δ₂, δ_m` half and the joint limit. -/
theorem scUnitLimit_of_sCtHalf (hct : SCtHalfFormula) (hlim : SCTotalLimit) : SCUnitLimit :=
  SCUnitLimit.of_one (scUnitLimitOne_of_sCtHalf hct hlim)

end QED.TwoLoop.UnitSCLimit

end
