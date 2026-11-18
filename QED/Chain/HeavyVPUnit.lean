/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VacuumPolarizationUnitLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The heavy-flavour VP unit at finite regulators: limits and decoupling (O3-M2)

Helper-level analysis for obligation O3-M2 of `docs/HIGHER-LOOP-PLAN.md` (Stage 0). It is
**not** frozen and does not depend on any multi-lepton model.

The open line has mass `1`. The closed loop is a lepton of mass `M_L > 0` with its **own**
Pauli–Villars pair `(M₁, M₂)` and coefficients `c₁, c₂`, fixed by the two conditions with the loop
mass, `1 + c₁ + c₂ = 0` and `M_L² + c₁ M₁² + c₂ M₂² = 0` (plan section 6, Q5 (i)). The one-flavour
value `QED.TwoLoop.VPUnit.vpFlavour M m_γ Λ` is already a function of the loop mass `M` (through the
spectral mass `4M²/(1-v²)`), with the open-line mass `1`; the only places where the existing VP
pipeline fixes the loop mass to `1` are the Pauli–Villars coefficients (`pvC1`, `pvC2`), the sum
`vpUnitReg`, and the decoupling bound `abs_vpLimSum_sub_le`. This file generalizes those.

## Objects

* `pvC1L M_L M₁ M₂ = (M₂² - M_L²)/(M₁² - M₂²)`, `pvC2L M_L M₁ M₂ = (M₁² - M_L²)/(M₂² - M₁²)`: the
  unique solution of the two conditions with loop mass `M_L` (`pvL_conditions`, `pvL_unique`).
  They are scale invariant (`pvC1L_smul`), equal `pvC1 (M₁/M_L) (M₂/M_L)` (`pvC1L_eq_pvC1_div`) and
  reduce to `pvC1`, `pvC2` at `M_L = 1` (`pvC1L_one`, `pvC2L_one`).
* `heavyUnitReg M_L m_γ Λ M₁ M₂`: the flavours with masses `M_L, M₁, M₂` and coefficients
  `1, c₁, c₂`; `heavyUnitReg 1 = vpUnitReg` (`heavyUnitReg_one`).
* `heavyLimSum M_L M₁ M₂ = vpLim M_L + c₁ vpLim M₁ + c₂ vpLim M₂`, its `(m_γ, Λ)` limit.

## Main statements

* `tendsto_heavyUnitReg`: the joint limit `(m_γ, Λ) → (0⁺, ∞)` at fixed nonzero masses.
* `heavyLimSum_bounds`: for `0 < M_L ≤ M₁, M₂` (no constraint on `M₂/M₁`),
  `-(vpLim M₁ + vpLim M₂) ≤ c₁ vpLim M₁ + c₂ vpLim M₂ ≤ 0`. The pointwise divided-difference bound
  `QED.TwoLoop.VPUnit.pv_f2_bound` is reused at the rescaled point `w = 4M_L²/(1-v²)`,
  `μ_f = (M_f/M_L)²`.
* `abs_heavyLimSum_sub_le` (**decoupling with a rate**): for `0 < M_L ≤ M₁, M₂`,
  `|heavyLimSum M_L M₁ M₂ - vpLim M_L| ≤ (1/M₁² + 1/M₂²)/45`, the constant of
  `abs_vpLimSum_sub_le`, uniform in `M_L` and in `M₂/M₁`. In units of the loop mass it reads
  `((M_L/M₁)² + (M_L/M₂)²) · 1/(45 M_L²)`, and `1/(45 M_L²)` is the leading size of `vpLim M_L`
  itself, so the regulators must sit far above `M_L` for a small *relative* error (at
  `M = (2,3) M_L` the bound allows `36%`; numerically the shift is `-33%`).
* `tendsto_heavyLimSum`: `heavyLimSum M_L M₁ M₂ → vpLim M_L` as `M₁, M₂ → ∞` jointly.
* `heavyUnitReg_iterated_limit`: the D-37.4 quantifier form, masses first, to `vpLim M_L`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.Chain.HeavyVP

open QED.TwoLoop.VPUnit

/-! ### The Pauli–Villars coefficients with loop mass `M_L` -/

/-- The Pauli–Villars coefficient `c₁ = (M₂² - M_L²)/(M₁² - M₂²)` for loop mass `M_L`. -/
noncomputable def pvC1L (ML M₁ M₂ : ℝ) : ℝ := (M₂ ^ 2 - ML ^ 2) / (M₁ ^ 2 - M₂ ^ 2)

/-- The Pauli–Villars coefficient `c₂ = (M₁² - M_L²)/(M₂² - M₁²)` for loop mass `M_L`. -/
noncomputable def pvC2L (ML M₁ M₂ : ℝ) : ℝ := (M₁ ^ 2 - ML ^ 2) / (M₂ ^ 2 - M₁ ^ 2)

theorem pvC1L_one (M₁ M₂ : ℝ) : pvC1L 1 M₁ M₂ = pvC1 M₁ M₂ := by
  simp [pvC1L, pvC1]

theorem pvC2L_one (M₁ M₂ : ℝ) : pvC2L 1 M₁ M₂ = pvC2 M₁ M₂ := by
  simp [pvC2L, pvC2]

/-- The coefficients are invariant under a common rescaling of the three masses. -/
theorem pvC1L_smul {t : ℝ} (ht : t ≠ 0) (ML M₁ M₂ : ℝ) :
    pvC1L (t * ML) (t * M₁) (t * M₂) = pvC1L ML M₁ M₂ := by
  unfold pvC1L
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  rw [show (t * M₂) ^ 2 - (t * ML) ^ 2 = t ^ 2 * (M₂ ^ 2 - ML ^ 2) by ring,
    show (t * M₁) ^ 2 - (t * M₂) ^ 2 = t ^ 2 * (M₁ ^ 2 - M₂ ^ 2) by ring,
    mul_div_mul_left _ _ ht2]

theorem pvC2L_smul {t : ℝ} (ht : t ≠ 0) (ML M₁ M₂ : ℝ) :
    pvC2L (t * ML) (t * M₁) (t * M₂) = pvC2L ML M₁ M₂ := by
  unfold pvC2L
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  rw [show (t * M₁) ^ 2 - (t * ML) ^ 2 = t ^ 2 * (M₁ ^ 2 - ML ^ 2) by ring,
    show (t * M₂) ^ 2 - (t * M₁) ^ 2 = t ^ 2 * (M₂ ^ 2 - M₁ ^ 2) by ring,
    mul_div_mul_left _ _ ht2]

/-- In units of the loop mass the coefficients are those of `QED.TwoLoop.VPUnit`. -/
theorem pvC1L_eq_pvC1_div {ML : ℝ} (hML : ML ≠ 0) (M₁ M₂ : ℝ) :
    pvC1L ML M₁ M₂ = pvC1 (M₁ / ML) (M₂ / ML) := by
  rw [← pvC1L_one, ← pvC1L_smul (inv_ne_zero hML) ML M₁ M₂]
  simp [div_eq_inv_mul, inv_mul_cancel₀ hML]

theorem pvC2L_eq_pvC2_div {ML : ℝ} (hML : ML ≠ 0) (M₁ M₂ : ℝ) :
    pvC2L ML M₁ M₂ = pvC2 (M₁ / ML) (M₂ / ML) := by
  rw [← pvC2L_one, ← pvC2L_smul (inv_ne_zero hML) ML M₁ M₂]
  simp [div_eq_inv_mul, inv_mul_cancel₀ hML]

/-- The coefficients satisfy the Pauli–Villars conditions with loop mass `M_L`. -/
theorem pvL_conditions {ML M₁ M₂ : ℝ} (h : M₁ ^ 2 ≠ M₂ ^ 2) :
    1 + pvC1L ML M₁ M₂ + pvC2L ML M₁ M₂ = 0 ∧
      ML ^ 2 + pvC1L ML M₁ M₂ * M₁ ^ 2 + pvC2L ML M₁ M₂ * M₂ ^ 2 = 0 := by
  have h1 : M₁ ^ 2 - M₂ ^ 2 ≠ 0 := sub_ne_zero.2 h
  have h2 : M₂ ^ 2 - M₁ ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  unfold pvC1L pvC2L
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The Pauli–Villars conditions with loop mass `M_L` determine the coefficients. -/
theorem pvL_unique {ML M₁ M₂ c₁ c₂ : ℝ} (h : M₁ ^ 2 ≠ M₂ ^ 2) (h1 : 1 + c₁ + c₂ = 0)
    (h2 : ML ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) :
    c₁ = pvC1L ML M₁ M₂ ∧ c₂ = pvC2L ML M₁ M₂ := by
  have h1' : M₁ ^ 2 - M₂ ^ 2 ≠ 0 := sub_ne_zero.2 h
  have h2' : M₂ ^ 2 - M₁ ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  unfold pvC1L pvC2L
  constructor
  · rw [eq_div_iff h1']
    linear_combination h2 - M₂ ^ 2 * h1
  · rw [eq_div_iff h2']
    linear_combination h2 - M₁ ^ 2 * h1

/-- The two conditions with `0 < M_L < M₂` force `M₁² ≠ M₂²`. -/
theorem sq_ne_sq_of_pvL {ML M₁ M₂ c₁ c₂ : ℝ} (hML : 0 < ML) (hM₂ : ML < M₂)
    (h1 : 1 + c₁ + c₂ = 0) (h2 : ML ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) : M₁ ^ 2 ≠ M₂ ^ 2 := by
  intro h
  rw [h] at h2
  have : ML ^ 2 - M₂ ^ 2 = 0 := by linear_combination h2 - M₂ ^ 2 * h1
  nlinarith

/-! ### The heavy-flavour VP unit at finite regulators -/

/-- **The heavy-flavour VP unit at finite regulators** (open-line mass `1`): the flavours with
masses `M_L, M₁, M₂` and coefficients `1, c₁, c₂` of the loop mass `M_L`. -/
noncomputable def heavyUnitReg (ML mγ Λ M₁ M₂ : ℝ) : ℝ :=
  vpFlavour ML mγ Λ + pvC1L ML M₁ M₂ * vpFlavour M₁ mγ Λ + pvC2L ML M₁ M₂ * vpFlavour M₂ mγ Λ

/-- The `(m_γ, Λ)` limit of `heavyUnitReg`: `vpLim M_L + c₁ vpLim M₁ + c₂ vpLim M₂`. -/
noncomputable def heavyLimSum (ML M₁ M₂ : ℝ) : ℝ :=
  vpLim ML + pvC1L ML M₁ M₂ * vpLim M₁ + pvC2L ML M₁ M₂ * vpLim M₂

/-- At loop mass `1` the heavy unit is the electron unit `vpUnitReg`. -/
theorem heavyUnitReg_one (mγ Λ M₁ M₂ : ℝ) : heavyUnitReg 1 mγ Λ M₁ M₂ = vpUnitReg mγ Λ M₁ M₂ := by
  simp only [heavyUnitReg, vpUnitReg, pvC1L_one, pvC2L_one]

theorem heavyLimSum_one (M₁ M₂ : ℝ) :
    heavyLimSum 1 M₁ M₂ = vpLim 1 + pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂ := by
  simp only [heavyLimSum, pvC1L_one, pvC2L_one]

/-- **Joint limit at fixed masses.** For `M_L, M₁, M₂ ≠ 0`, as `(m_γ, Λ) → (0⁺, ∞)` jointly,
`heavyUnitReg M_L m_γ Λ M₁ M₂ → heavyLimSum M_L M₁ M₂`. -/
theorem tendsto_heavyUnitReg {ML M₁ M₂ : ℝ} (hML : ML ≠ 0) (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) :
    Tendsto (fun p : ℝ × ℝ => heavyUnitReg ML p.1 p.2 M₁ M₂) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (heavyLimSum ML M₁ M₂)) :=
  ((tendsto_vpFlavour hML).add ((tendsto_vpFlavour hM₁).const_mul _)).add
    ((tendsto_vpFlavour hM₂).const_mul _)

/-! ### Decoupling of the heavy lepton's regulators -/

/-- **The divided-difference bound with loop mass `M_L`.** For `0 < M_L ≤ M₁, M₂`, with no
constraint on `M₂/M₁`: `-(vpLim M₁ + vpLim M₂) ≤ c₁ vpLim M₁ + c₂ vpLim M₂ ≤ 0`. (When
`M₁² = M₂²` the coefficients are `0` by Lean's division convention.) -/
theorem heavyLimSum_bounds {ML M₁ M₂ : ℝ} (hML : 0 < ML) (h1 : ML ≤ M₁) (h2 : ML ≤ M₂) :
    -(vpLim M₁ + vpLim M₂) ≤ pvC1L ML M₁ M₂ * vpLim M₁ + pvC2L ML M₁ M₂ * vpLim M₂ ∧
      pvC1L ML M₁ M₂ * vpLim M₁ + pvC2L ML M₁ M₂ * vpLim M₂ ≤ 0 := by
  have hM₁ : M₁ ≠ 0 := (hML.trans_le h1).ne'
  have hM₂ : M₂ ≠ 0 := (hML.trans_le h2).ne'
  have n1 := vpLim_nonneg hM₁
  have n2 := vpLim_nonneg hM₂
  by_cases h : M₁ ^ 2 = M₂ ^ 2
  · simp only [pvC1L, pvC2L, h, sub_self, div_zero, zero_mul, add_zero]
    constructor <;> linarith
  set μ₁ := (M₁ / ML) ^ 2 with hμ₁def
  set μ₂ := (M₂ / ML) ^ 2 with hμ₂def
  have hμ₁ : 1 ≤ μ₁ := one_le_pow₀ ((one_le_div hML).2 h1)
  have hμ₂ : 1 ≤ μ₂ := one_le_pow₀ ((one_le_div hML).2 h2)
  have hμ : μ₁ ≠ μ₂ := by
    intro e
    apply h
    have hML2 : ML ^ 2 ≠ 0 := pow_ne_zero 2 hML.ne'
    have e' := e
    simp only [hμ₁def, hμ₂def, div_pow] at e'
    exact (div_left_inj' hML2).1 e'
  have hc₁ : pvC1L ML M₁ M₂ = (μ₂ - 1) / (μ₁ - μ₂) := by
    rw [pvC1L_eq_pvC1_div hML.ne']
    rfl
  have hc₂ : pvC2L ML M₁ M₂ = (μ₁ - 1) / (μ₂ - μ₁) := by
    rw [pvC2L_eq_pvC2_div hML.ne']
    rfl
  have I1 := intervalIntegrable_vpLim hM₁
  have I2 := intervalIntegrable_vpLim hM₂
  have hpt : ∀ v ∈ Icc (0 : ℝ) 1,
      -(rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2)) + rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2))) ≤
          pvC1L ML M₁ M₂ * (rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2))) +
            pvC2L ML M₁ M₂ * (rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2))) ∧
        pvC1L ML M₁ M₂ * (rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2))) +
            pvC2L ML M₁ M₂ * (rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2))) ≤ 0 := by
    intro v hv
    rcases hv.2.lt_or_eq with hv1 | rfl
    · have hs : 0 < 1 - v ^ 2 := by nlinarith [hv.1]
      have hw : 0 < 4 * ML ^ 2 / (1 - v ^ 2) := by positivity
      have hr : 0 ≤ rho v := div_nonneg (mul_nonneg (sq_nonneg v) (by nlinarith [hv.1])) hs.le
      have e1 : 4 * M₁ ^ 2 / (1 - v ^ 2) = 4 * ML ^ 2 / (1 - v ^ 2) * μ₁ := by
        simp only [hμ₁def]
        field_simp
      have e2 : 4 * M₂ ^ 2 / (1 - v ^ 2) = 4 * ML ^ 2 / (1 - v ^ 2) * μ₂ := by
        simp only [hμ₂def]
        field_simp
      obtain ⟨b1, b2⟩ := pv_f2_bound hw hμ₁ hμ₂ hμ
      rw [e1, e2, hc₁, hc₂]
      have m1 := mul_le_mul_of_nonneg_left b1 hr
      have m2 := mul_le_mul_of_nonneg_left b2 hr
      constructor <;> nlinarith
    · simp [rho]
  have hsum : pvC1L ML M₁ M₂ * vpLim M₁ + pvC2L ML M₁ M₂ * vpLim M₂ =
      ∫ v in (0 : ℝ)..1, (pvC1L ML M₁ M₂ * (rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2))) +
        pvC2L ML M₁ M₂ * (rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2)))) := by
    rw [intervalIntegral.integral_add (I1.const_mul _) (I2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  have hneg : -(vpLim M₁ + vpLim M₂) =
      ∫ v in (0 : ℝ)..1, -(rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2)) +
        rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2))) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_add I1 I2]
    rfl
  rw [hsum, hneg]
  constructor
  · exact intervalIntegral.integral_mono_on zero_le_one (I1.add I2).neg
      ((I1.const_mul _).add (I2.const_mul _)) fun v hv => (hpt v hv).1
  · have := intervalIntegral.integral_mono_on zero_le_one
      ((I1.const_mul _).add (I2.const_mul _)) (intervalIntegrable_const (c := (0 : ℝ)))
      fun v hv => (hpt v hv).2
    simpa using this

/-- **Decoupling of the heavy lepton's regulators, with a rate.** For `0 < M_L ≤ M₁, M₂` (no
constraint on `M₂/M₁`), `|heavyLimSum M_L M₁ M₂ - vpLim M_L| ≤ (1/M₁² + 1/M₂²)/45`. -/
theorem abs_heavyLimSum_sub_le {ML M₁ M₂ : ℝ} (hML : 0 < ML) (h1 : ML ≤ M₁) (h2 : ML ≤ M₂) :
    |heavyLimSum ML M₁ M₂ - vpLim ML| ≤ (1 / M₁ ^ 2 + 1 / M₂ ^ 2) / 45 := by
  have hM₁ : M₁ ≠ 0 := (hML.trans_le h1).ne'
  have hM₂ : M₂ ≠ 0 := (hML.trans_le h2).ne'
  obtain ⟨b1, b2⟩ := heavyLimSum_bounds hML h1 h2
  have l1 := vpLim_le hM₁
  have l2 := vpLim_le hM₂
  have e1 : 1 / (45 * M₁ ^ 2) = 1 / M₁ ^ 2 / 45 := by ring
  have e2 : 1 / (45 * M₂ ^ 2) = 1 / M₂ ^ 2 / 45 := by ring
  unfold heavyLimSum
  rw [abs_le]
  constructor <;> linarith

/-- The same bound in units of the loop mass:
`|heavyLimSum M_L M₁ M₂ - vpLim M_L| ≤ ((M_L/M₁)² + (M_L/M₂)²) / (45 M_L²)`. -/
theorem abs_heavyLimSum_sub_le' {ML M₁ M₂ : ℝ} (hML : 0 < ML) (h1 : ML ≤ M₁) (h2 : ML ≤ M₂) :
    |heavyLimSum ML M₁ M₂ - vpLim ML| ≤ ((ML / M₁) ^ 2 + (ML / M₂) ^ 2) / (45 * ML ^ 2) := by
  have e : ((ML / M₁) ^ 2 + (ML / M₂) ^ 2) / (45 * ML ^ 2) = (1 / M₁ ^ 2 + 1 / M₂ ^ 2) / 45 := by
    field_simp
  rw [e]
  exact abs_heavyLimSum_sub_le hML h1 h2

/-- At loop mass `1` the decoupling bound is `QED.TwoLoop.VPUnit.abs_vpLimSum_sub_le`. -/
theorem abs_heavyLimSum_sub_le_one {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    |vpLim 1 + pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂ - (119 / 36 - π ^ 2 / 3)| ≤
      (1 / M₁ ^ 2 + 1 / M₂ ^ 2) / 45 := by
  have h := abs_heavyLimSum_sub_le one_pos h1 h2
  rw [heavyLimSum_one] at h
  rwa [← vpLim_one]

/-- **Decoupling, joint limit.** As `M₁, M₂ → ∞` jointly (along `atTop ×ˢ atTop`, no constraint on
`M₂/M₁`), `heavyLimSum M_L M₁ M₂ → vpLim M_L`, for every `M_L > 0`. -/
theorem tendsto_heavyLimSum {ML : ℝ} (hML : 0 < ML) :
    Tendsto (fun p : ℝ × ℝ => heavyLimSum ML p.1 p.2) (atTop ×ˢ atTop) (𝓝 (vpLim ML)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have t1 : Tendsto (fun p : ℝ × ℝ => 1 / p.1 ^ 2) (atTop ×ˢ atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_fst)
  have t2 : Tendsto (fun p : ℝ × ℝ => 1 / p.2 ^ 2) (atTop ×ˢ atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_snd)
  have t := (t1.add t2).div_const 45
  rw [zero_add, zero_div] at t
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ t
  filter_upwards [(eventually_ge_atTop ML).prod_inl atTop,
    (eventually_ge_atTop ML).prod_inr atTop] with p hp1 hp2
  rw [Real.norm_eq_abs]
  exact abs_heavyLimSum_sub_le hML hp1 hp2

/-- **The iterated limit in the order of D-37.4.** For `M_L > 0` and every `η > 0` there is `R`
such that for all `M₁, M₂ > R` there are `δ > 0` and `Λ₀` (depending on `M₁, M₂`) with
`|heavyUnitReg M_L m_γ Λ M₁ M₂ - vpLim M_L| < η` for all `m_γ ∈ (0, δ)` and `Λ > Λ₀`. -/
theorem heavyUnitReg_iterated_limit {ML : ℝ} (hML : 0 < ML) :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ →
        |heavyUnitReg ML mγ Λ M₁ M₂ - vpLim ML| < η := by
  intro η hη
  refine ⟨max ML 1 + 1 / η, fun M₁ M₂ h1 h2 => ?_⟩
  have hη' : 0 < 1 / η := by positivity
  have hL1 := le_max_left ML 1
  have hR1 := le_max_right ML 1
  have small : ∀ M : ℝ, max ML 1 + 1 / η < M → 1 / M ^ 2 < η := by
    intro M hM
    have hM0 : 0 < M := by linarith
    have hle : 1 / M ^ 2 ≤ 1 / M := one_div_le_one_div_of_le hM0 (by nlinarith)
    have hlt : 1 / M < η := by
      rw [div_lt_iff₀ hM0]
      have := (div_lt_iff₀ hη).1 (show 1 / η < M by linarith)
      linarith
    linarith
  have key := abs_heavyLimSum_sub_le hML (by linarith : ML ≤ M₁) (by linarith : ML ≤ M₂)
  have s1 := small M₁ h1
  have s2 := small M₂ h2
  have hL : |heavyLimSum ML M₁ M₂ - vpLim ML| < η / 2 := by linarith
  have hT := (Metric.tendsto_nhds.1 (tendsto_heavyUnitReg (M₁ := M₁) (M₂ := M₂) hML.ne'
    (by linarith : (0 : ℝ) < M₁).ne' (by linarith : (0 : ℝ) < M₂).ne')) (η / 2) (by positivity)
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := eventually_prod_iff.1 hT
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hpa
  obtain ⟨Λ₀, hΛ₀⟩ := eventually_atTop.1 hpb
  refine ⟨u, hu, Λ₀, fun mγ Λ hm0 hm1 hΛ => ?_⟩
  have hd := hall (hsub ⟨hm0, hm1⟩) (hΛ₀ Λ hΛ.le)
  rw [Real.dist_eq] at hd
  have := abs_sub_le (heavyUnitReg ML mγ Λ M₁ M₂) (heavyLimSum ML M₁ M₂) (vpLim ML)
  linarith

end QED.Chain.HeavyVP
