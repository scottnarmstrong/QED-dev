/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VacuumPolarizationUnit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The vacuum-polarization unit at finite regulators and its limits (O2-18, O2-19)

Helper analysis of explicit integrals, mirroring the numerical model of
`scripts/numerics/two_loop_units.py` (functions `f2`, `df2`, `vp_insert`, `vp_flavour`,
`vp_unit`). It is **not** frozen.

**Scope.** This module is about explicit integrals only. Whether `vpUnitReg` equals the model's
VP unit (the frozen order-5 vertex restricted to the VP contractions) is a separate obligation
(O2-8, O2-10, O2-13 of `docs/TWO-LOOP-DERIVATION.md`) and is not addressed here.

## Objects (electron mass `m = 1`)

* `f2 c = ∫₀¹ dx x²(1-x)/(x² + (1-x)c)`: the one-loop `F₂/r` with a photon of squared mass `c`;
  `df2 c = -∫₀¹ dx x²(1-x)²/(x² + (1-x)c)²`, its derivative in `c` (as in the script).
* `vpInsert c a b`: the exact partial-fraction value (script `vp_insert`) of `F₂/r` for the photon
  function `R(k²) = k⁴/(k² + c) · (1/(k² + a) - 1/(k² + b))²`, written through `f2` and `df2`
  at `c`, `a` and `b`; here `a = m_γ²`, `b = Λ²`, `c = 4M²/(1-v²)`.
* `vpFlavour M m_γ Λ = ∫₀¹ dv ρ(v) vpInsert(4M²/(1-v²), m_γ², Λ²)`, `ρ(v) = v²(1-v²/3)/(1-v²)`.
* `pvC1`, `pvC2`: the Pauli–Villars coefficients, the unique solution of
  `1 + c₁ + c₂ = 0`, `1 + c₁M₁² + c₂M₂² = 0` when `M₁² ≠ M₂²` (`pv_conditions`, `pv_unique`).
* `vpUnitReg m_γ Λ M₁ M₂`: the sum over the flavours `f = 0, 1, 2` with masses `1, M₁, M₂` and
  coefficients `1, c₁, c₂` (script `vp_unit`).
* `vpLim M = ∫₀¹ dv ρ(v) f2(4M²/(1-v²))`, with `vpLim 1 = 119/36 - π²/3` (`vpLim_one`).

## Route

* `vpInsert_eq_integral`: for distinct positive `a, b, c` the partial-fraction value is the
  integral of the kernel `regKernel c a b x = k_c(x) · (x²/(x²+(1-x)a) - x²/(x²+(1-x)b))²`, where
  `k_c` is the integrand of `f2 c`. With `0 ≤ a ≤ b` the bracket lies in `[0,1]`, so
  `0 ≤ regKernel ≤ k_c`, and it tends to `1` as `a → 0`, `b → ∞`. The exceptional point
  `4M²/(1-v²) = Λ²` of the partial fractions is a null set in `v`.
* Item 1 is then dominated convergence twice, as a **joint** limit along
  `𝓝[>] 0 ×ˢ atTop` in `(m_γ, Λ)` at fixed `M₁, M₂ ≠ 0`.
* Item 2 (O2-19) needs no derivative bound: pointwise in `(v, x)`, with `P = x²`,
  `Q = (1-x)·4/(1-v²)`, `μ_f = M_f²`, the Pauli–Villars sum of `1/(P + Qμ)` is a second divided
  difference, `Σ_f c_f/(P + Qμ_f) = Q²(μ₁-1)(μ₂-1)/((P+Q)(P+Qμ₁)(P+Qμ₂))`. Hence
  `-(vpLim M₁ + vpLim M₂) ≤ c₁ vpLim M₁ + c₂ vpLim M₂ ≤ 0` for all `M₁, M₂ ≥ 1`, with no constraint
  on `M₂/M₁` (also when `M₁ - M₂ → 0`), and `0 ≤ vpLim M ≤ 1/(45M²)`.

## Main statements

* `QED.TwoLoop.VPUnit.tendsto_vpUnitReg` (item 1): joint limit `(m_γ, Λ) → (0⁺, ∞)` at fixed
  `M₁, M₂ ≠ 0`, to `vpLim 1 + c₁ vpLim M₁ + c₂ vpLim M₂`.
* `QED.TwoLoop.VPUnit.abs_vpLimSum_sub_le` (item 2, rate): for `M₁, M₂ ≥ 1`,
  `|vpLim 1 + c₁ vpLim M₁ + c₂ vpLim M₂ - (119/36 - π²/3)| ≤ (1/M₁² + 1/M₂²)/45`.
* `QED.TwoLoop.VPUnit.tendsto_vpLimSum` (item 2): the joint limit `M₁, M₂ → ∞` along
  `atTop ×ˢ atTop` is `119/36 - π²/3`.
* `QED.TwoLoop.VPUnit.vpUnitReg_iterated_limit`: the D-37.4 / D-41 quantifier form, masses first.
* `QED.TwoLoop.VPUnit.hasDerivAt_f2`: `df2` is the derivative of `f2` on `(0, ∞)`;
  `vpInsert_eq_integral`: the partial-fraction value is the kernel integral.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.TwoLoop.VPUnit

/-! ### Definitions -/

/-- The integrand of `f2`: `x²(1-x)/(x² + (1-x)c)`. -/
noncomputable def f2Kernel (c x : ℝ) : ℝ := x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * c)

/-- The integrand of `-df2`: `x²(1-x)²/(x² + (1-x)c)²`. -/
noncomputable def df2Kernel (c x : ℝ) : ℝ := x ^ 2 * (1 - x) ^ 2 / (x ^ 2 + (1 - x) * c) ^ 2

/-- The one-loop `F₂/r` with a photon of squared mass `c` (script `f2`). -/
noncomputable def f2 (c : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, f2Kernel c x

/-- The derivative of `f2` in the squared photon mass, as an explicit integral (script `df2`). -/
noncomputable def df2 (c : ℝ) : ℝ := -∫ x in (0 : ℝ)..1, df2Kernel c x

/-- The spectral weight `ρ(v) = v²(1 - v²/3)/(1 - v²)`. -/
noncomputable def rho (v : ℝ) : ℝ := v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2)

/-- The exact partial-fraction value of `F₂/r` for the photon function
`R(k²) = k⁴/(k² + c) · (1/(k² + a) - 1/(k² + b))²` (script `vp_insert`, finite `b`). The
coefficients are those of `R = A/(k²+c) + Σ_{e=a,b} (B_e/(k²+e) + E_e/(k²+e)²)`, with
`A = c²(1/(a-c) - 1/(b-c))²`, `E_e = h_e(-e)` and `B_e = h_e'(-e)` for `h_e = R·(k²+e)²`; a double
pole contributes `-E_e · df2 e`. -/
noncomputable def vpInsert (c a b : ℝ) : ℝ :=
  c ^ 2 * (1 / (a - c) - 1 / (b - c)) ^ 2 * f2 c +
    ((-2 * a / (c - a) - a ^ 2 / (c - a) ^ 2 - 2 * a ^ 2 / ((c - a) * (b - a))) * f2 a -
      a ^ 2 / (c - a) * df2 a) +
    ((-2 * b / (c - b) - b ^ 2 / (c - b) ^ 2 - 2 * b ^ 2 / ((c - b) * (a - b))) * f2 b -
      b ^ 2 / (c - b) * df2 b)

/-- One flavour of mass `M` at finite regulators (script `vp_flavour`):
`∫₀¹ dv ρ(v) vpInsert(4M²/(1-v²), m_γ², Λ²)`. -/
noncomputable def vpFlavour (M mγ Λ : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, rho v * vpInsert (4 * M ^ 2 / (1 - v ^ 2)) (mγ ^ 2) (Λ ^ 2)

/-- The Pauli–Villars coefficient `c₁ = (M₂² - 1)/(M₁² - M₂²)`. -/
noncomputable def pvC1 (M₁ M₂ : ℝ) : ℝ := (M₂ ^ 2 - 1) / (M₁ ^ 2 - M₂ ^ 2)

/-- The Pauli–Villars coefficient `c₂ = (M₁² - 1)/(M₂² - M₁²)`. -/
noncomputable def pvC2 (M₁ M₂ : ℝ) : ℝ := (M₁ ^ 2 - 1) / (M₂ ^ 2 - M₁ ^ 2)

/-- The VP unit at finite regulators (script `vp_unit`): the flavours `f = 0, 1, 2` with masses
`1, M₁, M₂` and coefficients `1, c₁, c₂`. -/
noncomputable def vpUnitReg (mγ Λ M₁ M₂ : ℝ) : ℝ :=
  vpFlavour 1 mγ Λ + pvC1 M₁ M₂ * vpFlavour M₁ mγ Λ + pvC2 M₁ M₂ * vpFlavour M₂ mγ Λ

/-- The limited one-flavour VP function `V(M) = ∫₀¹ dv ρ(v) f2(4M²/(1-v²))`. -/
noncomputable def vpLim (M : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, rho v * f2 (4 * M ^ 2 / (1 - v ^ 2))

/-- The kernel of `vpInsert`: `x² R(x²/(1-x))` in the variable `x` of `f2`. -/
noncomputable def regKernel (c a b x : ℝ) : ℝ :=
  f2Kernel c x * (x ^ 2 / (x ^ 2 + (1 - x) * a) - x ^ 2 / (x ^ 2 + (1 - x) * b)) ^ 2

/-! ### The Pauli–Villars coefficients -/

/-- The coefficients satisfy the Pauli–Villars conditions. -/
theorem pv_conditions {M₁ M₂ : ℝ} (h : M₁ ^ 2 ≠ M₂ ^ 2) :
    1 + pvC1 M₁ M₂ + pvC2 M₁ M₂ = 0 ∧ 1 + pvC1 M₁ M₂ * M₁ ^ 2 + pvC2 M₁ M₂ * M₂ ^ 2 = 0 := by
  have h1 : M₁ ^ 2 - M₂ ^ 2 ≠ 0 := sub_ne_zero.2 h
  have h2 : M₂ ^ 2 - M₁ ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  unfold pvC1 pvC2
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The Pauli–Villars conditions determine the coefficients. -/
theorem pv_unique {M₁ M₂ c₁ c₂ : ℝ} (h : M₁ ^ 2 ≠ M₂ ^ 2) (h1 : 1 + c₁ + c₂ = 0)
    (h2 : 1 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) : c₁ = pvC1 M₁ M₂ ∧ c₂ = pvC2 M₁ M₂ := by
  have h1' : M₁ ^ 2 - M₂ ^ 2 ≠ 0 := sub_ne_zero.2 h
  have h2' : M₂ ^ 2 - M₁ ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  unfold pvC1 pvC2
  constructor
  · rw [eq_div_iff h1']
    linear_combination h2 - M₂ ^ 2 * h1
  · rw [eq_div_iff h2']
    linear_combination h2 - M₁ ^ 2 * h1

/-! ### The one-loop kernel -/

theorem den_pos {e x : ℝ} (he : 0 < e) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < x ^ 2 + (1 - x) * e := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases hx1.lt_or_eq with h | rfl
  · have : 0 < (1 - x) * e := mul_pos (by linarith) he
    positivity
  · norm_num

theorem continuousOn_f2Kernel {e : ℝ} (he : 0 < e) : ContinuousOn (f2Kernel e) (Icc 0 1) :=
  ContinuousOn.div (by fun_prop) (by fun_prop) fun _ hx => (den_pos he hx).ne'

theorem continuousOn_df2Kernel {e : ℝ} (he : 0 < e) : ContinuousOn (df2Kernel e) (Icc 0 1) :=
  ContinuousOn.div (by fun_prop) (by fun_prop) fun _ hx => pow_ne_zero 2 (den_pos he hx).ne'

theorem intervalIntegrable_f2Kernel {e : ℝ} (he : 0 < e) :
    IntervalIntegrable (f2Kernel e) volume 0 1 :=
  (continuousOn_f2Kernel he).intervalIntegrable_of_Icc zero_le_one

theorem intervalIntegrable_df2Kernel {e : ℝ} (he : 0 < e) :
    IntervalIntegrable (df2Kernel e) volume 0 1 :=
  (continuousOn_df2Kernel he).intervalIntegrable_of_Icc zero_le_one

theorem f2Kernel_nonneg {c x : ℝ} (hc : 0 < c) (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ f2Kernel c x :=
  div_nonneg (mul_nonneg (sq_nonneg x) (by linarith [hx.2])) (den_pos hc hx).le

theorem f2Kernel_le {c x : ℝ} (hc : 0 < c) (hx : x ∈ Icc (0 : ℝ) 1) :
    f2Kernel c x ≤ x ^ 2 / c := by
  unfold f2Kernel
  rw [div_le_div_iff₀ (den_pos hc hx) hc]
  nlinarith [sq_nonneg (x ^ 2)]

theorem integral_sq_div (c : ℝ) : ∫ x in (0 : ℝ)..1, x ^ 2 / c = 1 / (3 * c) := by
  rw [intervalIntegral.integral_div, integral_pow]
  norm_num
  ring

theorem f2_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ f2 c :=
  intervalIntegral.integral_nonneg zero_le_one fun _ hx => f2Kernel_nonneg hc hx

theorem f2_le {c : ℝ} (hc : 0 < c) : f2 c ≤ 1 / (3 * c) := by
  rw [← integral_sq_div c]
  exact intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_f2Kernel hc)
    ((by fun_prop : Continuous fun x : ℝ => x ^ 2 / c).intervalIntegrable 0 1)
    fun x hx => f2Kernel_le hc hx

/-- `df2` is the derivative of `f2` on `(0, ∞)`. -/
theorem hasDerivAt_f2 {c₀ : ℝ} (hc₀ : 0 < c₀) : HasDerivAt f2 (df2 c₀) c₀ := by
  have hc2 : 0 < c₀ / 2 := by positivity
  have hs : Ioi (c₀ / 2) ∈ 𝓝 c₀ := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ c : ℝ, Measurable (f2Kernel c) := fun c => by unfold f2Kernel; fun_prop
  have hmeas' : Measurable fun x => -df2Kernel c₀ x := by unfold df2Kernel; fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f2Kernel) (F' := fun c x => -df2Kernel c x) (bound := df2Kernel (c₀ / 2))
    (μ := volume) (a := 0) (b := 1) hs
    (Eventually.of_forall fun c => (hmeas c).aestronglyMeasurable)
    (intervalIntegrable_f2Kernel hc₀) hmeas'.aestronglyMeasurable ?_
    (intervalIntegrable_df2Kernel hc2) ?_
  · have := key.2
    unfold df2
    rw [← intervalIntegral.integral_neg]
    exact this
  · refine Eventually.of_forall fun x hx c hc => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    have hc' : c₀ / 2 < c := hc
    have hd0 := den_pos hc2 hx'
    have hle : x ^ 2 + (1 - x) * (c₀ / 2) ≤ x ^ 2 + (1 - x) * c := by
      nlinarith [mul_le_mul_of_nonneg_left hc'.le (by linarith [hx'.2] : (0 : ℝ) ≤ 1 - x)]
    unfold df2Kernel
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg _)) (sq_nonneg _))]
    exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg x) (sq_nonneg _)) (pow_pos hd0 2)
      (pow_le_pow_left₀ hd0.le hle 2)
  · refine Eventually.of_forall fun x hx c hc => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    have hc' : 0 < c := hc2.trans hc
    have hd := (den_pos hc' hx').ne'
    have h := (hasDerivAt_const c (x ^ 2 * (1 - x))).div
      (((hasDerivAt_id c).const_mul (1 - x)).const_add (x ^ 2)) (by simpa using hd)
    refine h.congr_deriv ?_
    simp only [df2Kernel, id]
    ring

/-! ### The finite-regulator kernel -/

theorem ratio_mem {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ x ^ 2 / (x ^ 2 + (1 - x) * a) - x ^ 2 / (x ^ 2 + (1 - x) * b) ∧
      x ^ 2 / (x ^ 2 + (1 - x) * a) - x ^ 2 / (x ^ 2 + (1 - x) * b) ≤ 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases hx0.lt_or_eq with h | rfl
  · have h1x : 0 ≤ 1 - x := by linarith
    have hda : x ^ 2 ≤ x ^ 2 + (1 - x) * a := by nlinarith [mul_nonneg h1x ha]
    have hdb : x ^ 2 + (1 - x) * a ≤ x ^ 2 + (1 - x) * b := by
      nlinarith [mul_le_mul_of_nonneg_left hab h1x]
    have hx2 : 0 < x ^ 2 := by positivity
    have hpa : 0 < x ^ 2 + (1 - x) * a := lt_of_lt_of_le hx2 hda
    constructor
    · rw [sub_nonneg]
      exact div_le_div_of_nonneg_left hx2.le hpa hdb
    · have h1 : x ^ 2 / (x ^ 2 + (1 - x) * a) ≤ 1 := (div_le_one hpa).2 hda
      have h2 : 0 ≤ x ^ 2 / (x ^ 2 + (1 - x) * b) := div_nonneg hx2.le (by linarith)
      linarith
  · simp

theorem regKernel_nonneg {c a b x : ℝ} (hc : 0 < c) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ regKernel c a b x :=
  mul_nonneg (f2Kernel_nonneg hc hx) (sq_nonneg _)

theorem regKernel_le {c a b x : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hab : a ≤ b)
    (hx : x ∈ Icc (0 : ℝ) 1) : regKernel c a b x ≤ f2Kernel c x := by
  obtain ⟨h0, h1⟩ := ratio_mem ha hab hx
  exact mul_le_of_le_one_right (f2Kernel_nonneg hc hx) (pow_le_one₀ h0 h1)

/-- The partial-fraction identity, pointwise in `x`. -/
theorem regKernel_eq {x a b c : ℝ} (hda : x ^ 2 + (1 - x) * a ≠ 0)
    (hdb : x ^ 2 + (1 - x) * b ≠ 0) (hdc : x ^ 2 + (1 - x) * c ≠ 0)
    (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    regKernel c a b x =
      c ^ 2 * (1 / (a - c) - 1 / (b - c)) ^ 2 * f2Kernel c x +
      ((-2 * a / (c - a) - a ^ 2 / (c - a) ^ 2 - 2 * a ^ 2 / ((c - a) * (b - a))) *
          f2Kernel a x + a ^ 2 / (c - a) * df2Kernel a x) +
      ((-2 * b / (c - b) - b ^ 2 / (c - b) ^ 2 - 2 * b ^ 2 / ((c - b) * (a - b))) *
          f2Kernel b x + b ^ 2 / (c - b) * df2Kernel b x) := by
  have h1 : c - a ≠ 0 := sub_ne_zero.2 hca
  have h2 : c - b ≠ 0 := sub_ne_zero.2 hcb
  have h3 : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have h4 : a - c ≠ 0 := sub_ne_zero.2 (Ne.symm hca)
  have h5 : b - c ≠ 0 := sub_ne_zero.2 (Ne.symm hcb)
  have h6 : a - b ≠ 0 := sub_ne_zero.2 hab
  unfold regKernel f2Kernel df2Kernel
  field_simp
  ring

/-- For distinct positive `a, b, c`, the partial-fraction value is the integral of the kernel. -/
theorem vpInsert_eq_integral {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hca : c ≠ a)
    (hcb : c ≠ b) (hab : a ≠ b) : vpInsert c a b = ∫ x in (0 : ℝ)..1, regKernel c a b x := by
  set A := c ^ 2 * (1 / (a - c) - 1 / (b - c)) ^ 2
  set Ba := -2 * a / (c - a) - a ^ 2 / (c - a) ^ 2 - 2 * a ^ 2 / ((c - a) * (b - a))
  set Ea := a ^ 2 / (c - a)
  set Bb := -2 * b / (c - b) - b ^ 2 / (c - b) ^ 2 - 2 * b ^ 2 / ((c - b) * (a - b))
  set Eb := b ^ 2 / (c - b)
  have key : ∀ x ∈ uIcc (0 : ℝ) 1, regKernel c a b x =
      A * f2Kernel c x + (Ba * f2Kernel a x + Ea * df2Kernel a x) +
        (Bb * f2Kernel b x + Eb * df2Kernel b x) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    exact regKernel_eq (den_pos ha hx).ne' (den_pos hb hx).ne' (den_pos hc hx).ne' hca hcb hab
  have ic := (intervalIntegrable_f2Kernel hc).const_mul A
  have ia := (intervalIntegrable_f2Kernel ha).const_mul Ba
  have ia2 := (intervalIntegrable_df2Kernel ha).const_mul Ea
  have ib := (intervalIntegrable_f2Kernel hb).const_mul Bb
  have ib2 := (intervalIntegrable_df2Kernel hb).const_mul Eb
  rw [intervalIntegral.integral_congr key,
    intervalIntegral.integral_add (ic.add (ia.add ia2)) (ib.add ib2),
    intervalIntegral.integral_add ic (ia.add ia2), intervalIntegral.integral_add ia ia2,
    intervalIntegral.integral_add ib ib2]
  simp only [intervalIntegral.integral_const_mul]
  unfold vpInsert f2 df2
  ring

/-! ### Item 1: the joint limit `(m_γ, Λ) → (0⁺, ∞)` at fixed `M_f` -/

theorem measurable_regKernel (a b : ℝ) :
    Measurable (Function.uncurry fun (c x : ℝ) => regKernel c a b x) := by
  change Measurable fun q : ℝ × ℝ => regKernel q.1 a b q.2
  unfold regKernel f2Kernel
  fun_prop

/-- A parametric interval integral of a jointly measurable function is strongly measurable. -/
theorem stronglyMeasurable_intervalIntegral {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    StronglyMeasurable fun v => ∫ x in (0 : ℝ)..1, F v x := by
  have : (fun v => ∫ x in (0 : ℝ)..1, F v x) =
      fun v => ∫ x, F v x ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    funext v
    exact intervalIntegral.integral_of_le zero_le_one
  rw [this]
  exact hF.stronglyMeasurable.integral_prod_right

/-- The bracket of `regKernel` tends to `1` for `0 < x < 1`. -/
theorem tendsto_regKernel {c x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun p : ℝ × ℝ => regKernel c (p.1 ^ 2) (p.2 ^ 2) x) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (f2Kernel c x)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hx2 : 0 < x ^ 2 := by positivity
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] (0 : ℝ) ×ˢ atTop) (𝓝 0) :=
    (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := (atTop : Filter ℝ))).mono_right nhdsWithin_le_nhds
  have h1 : Tendsto (fun p : ℝ × ℝ => x ^ 2 / (x ^ 2 + (1 - x) * p.1 ^ 2))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 1) := by
    have hden : Tendsto (fun p : ℝ × ℝ => x ^ 2 + (1 - x) * p.1 ^ 2) (𝓝[>] 0 ×ˢ atTop)
        (𝓝 (x ^ 2 + (1 - x) * 0 ^ 2)) :=
      tendsto_const_nhds.add ((tendsto_const_nhds (x := 1 - x)).mul (hfst.pow 2))
    have := (tendsto_const_nhds (x := x ^ 2)).div hden (by simp; exact hx0.ne')
    rw [show x ^ 2 / (x ^ 2 + (1 - x) * 0 ^ 2) = 1 by simp [hx2.ne']] at this
    exact this
  have hsnd : Tendsto (fun p : ℝ × ℝ => (1 - x) * p.2 ^ 2) (𝓝[>] (0 : ℝ) ×ˢ atTop) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp
      (tendsto_snd (f := 𝓝[>] (0 : ℝ)) (g := (atTop : Filter ℝ)))).const_mul_atTop
      (by linarith)
  have h2 : Tendsto (fun p : ℝ × ℝ => x ^ 2 / (x ^ 2 + (1 - x) * p.2 ^ 2))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ hsnd)
  have := (tendsto_const_nhds (x := f2Kernel c x)).mul ((h1.sub h2).pow 2)
  simpa [regKernel] using this

/-- The inner integral converges to `f2 c`. -/
theorem tendsto_integral_regKernel {c : ℝ} (hc : 0 < c) :
    Tendsto (fun p : ℝ × ℝ => ∫ x in (0 : ℝ)..1, regKernel c (p.1 ^ 2) (p.2 ^ 2) x)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (f2 c)) := by
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, p.1 ^ 2 ≤ p.2 ^ 2 := by
    have h1 : ∀ᶠ m in 𝓝[>] (0 : ℝ), m ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [h1.prod_inl atTop, (eventually_gt_atTop (1 : ℝ)).prod_inr (𝓝[>] (0 : ℝ))]
      with p hp1 hp2
    nlinarith [hp1.1, hp1.2]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (f2Kernel c) ?_ ?_
    (intervalIntegrable_f2Kernel hc) ?_
  · refine Eventually.of_forall fun p => ?_
    have : Measurable fun x => regKernel c (p.1 ^ 2) (p.2 ^ 2) x := by
      unfold regKernel f2Kernel
      fun_prop
    exact this.aestronglyMeasurable
  · filter_upwards [hev] with p hp
    refine Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    rw [Real.norm_eq_abs, abs_of_nonneg (regKernel_nonneg hc hx')]
    exact regKernel_le hc (sq_nonneg _) hp hx'
  · have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    exact tendsto_regKernel ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

/-- The spectral mass is at least `4M²` on `[0,1)`. -/
theorem le_specMass {M v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    4 * M ^ 2 ≤ 4 * M ^ 2 / (1 - v ^ 2) := by
  have hs : 0 < 1 - v ^ 2 := by nlinarith
  have hs1 : 1 - v ^ 2 ≤ 1 := by nlinarith
  exact le_div_self (by positivity) hs hs1

theorem specMass_pos {M v : ℝ} (hM : M ≠ 0) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    0 < 4 * M ^ 2 / (1 - v ^ 2) :=
  lt_of_lt_of_le (by positivity) (le_specMass hv0 hv1)

/-- `ρ(v) y ≤ v²(1 - v²/3)/(12M²)` when `0 ≤ y ≤ 1/(3c_v)`. -/
theorem rho_mul_bound {M v y : ℝ} (hM : M ≠ 0) (hv0 : 0 ≤ v) (hv1 : v < 1) (hy0 : 0 ≤ y)
    (hy : y ≤ 1 / (3 * (4 * M ^ 2 / (1 - v ^ 2)))) :
    0 ≤ rho v * y ∧ rho v * y ≤ v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2) := by
  have hs : 0 < 1 - v ^ 2 := by nlinarith
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  have hr : 0 ≤ rho v := div_nonneg (mul_nonneg (sq_nonneg v) (by linarith)) hs.le
  refine ⟨mul_nonneg hr hy0, ?_⟩
  calc rho v * y ≤ rho v * (1 / (3 * (4 * M ^ 2 / (1 - v ^ 2)))) :=
        mul_le_mul_of_nonneg_left hy hr
    _ = v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2) := by
        unfold rho
        field_simp
        ring

theorem integral_regKernel_le {c a b : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ ∫ x in (0 : ℝ)..1, regKernel c a b x ∧
      ∫ x in (0 : ℝ)..1, regKernel c a b x ≤ 1 / (3 * c) := by
  refine ⟨intervalIntegral.integral_nonneg zero_le_one fun x hx => regKernel_nonneg hc hx, ?_⟩
  refine le_trans ?_ (f2_le hc)
  have hm : Measurable fun x => regKernel c a b x := by
    unfold regKernel f2Kernel
    fun_prop
  refine intervalIntegral.integral_mono_on zero_le_one ?_ (intervalIntegrable_f2Kernel hc)
    fun x hx => regKernel_le hc ha hab hx
  refine (intervalIntegrable_f2Kernel hc).mono_fun hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_)
  rw [uIoc_of_le zero_le_one] at hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
  dsimp only
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (regKernel_nonneg hc hx'),
    abs_of_nonneg (f2Kernel_nonneg hc hx')]
  exact regKernel_le hc ha hab hx'

/-- Off a finite set of `v`, `vpInsert` at the spectral mass is the kernel integral. -/
theorem vpFlavour_eq {M a b : ℝ} (hM : M ≠ 0) (ha : 0 < a) (hab : a < b) (haM : a < 4 * M ^ 2) :
    vpFlavour M (√a) (√b) =
      ∫ v in (0 : ℝ)..1, rho v * ∫ x in (0 : ℝ)..1, regKernel (4 * M ^ 2 / (1 - v ^ 2)) a b x := by
  have hb : 0 < b := ha.trans hab
  unfold vpFlavour
  rw [sq_sqrt ha.le, sq_sqrt hb.le]
  refine intervalIntegral.integral_congr_ae ?_
  set S : Set ℝ := {1, √(1 - 4 * M ^ 2 / b)}
  have hS : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ S :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite S).measure_zero volume)
  filter_upwards [hS] with v hvS hv
  rw [uIoc_of_le zero_le_one] at hv
  have hv1 : v < 1 := lt_of_le_of_ne hv.2 fun h => hvS (by simp [S, h])
  have hc := specMass_pos (M := M) hM hv.1.le hv1
  have hca : 4 * M ^ 2 / (1 - v ^ 2) ≠ a := (lt_of_lt_of_le haM (le_specMass hv.1.le hv1)).ne'
  have hcb : 4 * M ^ 2 / (1 - v ^ 2) ≠ b := by
    intro h
    have hs : 0 < 1 - v ^ 2 := by nlinarith [hv.1]
    have : v ^ 2 = 1 - 4 * M ^ 2 / b := by
      field_simp
      field_simp at h
      linarith
    apply hvS
    have : v = √(1 - 4 * M ^ 2 / b) := by rw [← this, sqrt_sq hv.1.le]
    simp [S, this]
  rw [vpInsert_eq_integral ha hb hc hca hcb hab.ne]

/-- **One flavour, joint limit.** For `M ≠ 0`, as `(m_γ, Λ) → (0⁺, ∞)` jointly,
`vpFlavour M m_γ Λ → vpLim M`. -/
theorem tendsto_vpFlavour {M : ℝ} (hM : M ≠ 0) :
    Tendsto (fun p : ℝ × ℝ => vpFlavour M p.1 p.2) (𝓝[>] 0 ×ˢ atTop) (𝓝 (vpLim M)) := by
  set G : ℝ × ℝ → ℝ → ℝ := fun p v =>
    rho v * ∫ x in (0 : ℝ)..1, regKernel (4 * M ^ 2 / (1 - v ^ 2)) (p.1 ^ 2) (p.2 ^ 2) x
  have hMp : 0 < |M| := abs_pos.2 hM
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, 0 < p.1 ∧ p.1 < |M| ∧ |M| < p.2 := by
    have h1 : ∀ᶠ m in 𝓝[>] (0 : ℝ), m ∈ Ioo 0 |M| := Ioo_mem_nhdsGT hMp
    filter_upwards [h1.prod_inl atTop, (eventually_gt_atTop |M|).prod_inr (𝓝[>] (0 : ℝ))]
      with p hp1 hp2
    exact ⟨hp1.1, hp1.2, hp2⟩
  have hlim : Tendsto (fun p => ∫ v in (0 : ℝ)..1, G p v) (𝓝[>] 0 ×ˢ atTop) (𝓝 (vpLim M)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun v => v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2)) ?_ ?_
      ((by fun_prop : Continuous fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2)
        ).intervalIntegrable 0 1) ?_
    · refine Eventually.of_forall fun p => ?_
      have hm : Measurable rho := by unfold rho; fun_prop
      refine hm.aestronglyMeasurable.mul
        (stronglyMeasurable_intervalIntegral (F := fun v x =>
          regKernel (4 * M ^ 2 / (1 - v ^ 2)) (p.1 ^ 2) (p.2 ^ 2) x) ?_).aestronglyMeasurable
      have := (measurable_regKernel (p.1 ^ 2) (p.2 ^ 2)).comp
        ((by fun_prop : Measurable fun v : ℝ => 4 * M ^ 2 / (1 - v ^ 2)).prodMap measurable_id)
      exact this
    · filter_upwards [hev] with p hp
      have hab : p.1 ^ 2 ≤ p.2 ^ 2 := by nlinarith [hp.1, hp.2.1, hp.2.2]
      have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with v hv1 hv
      rw [uIoc_of_le zero_le_one] at hv
      have hv1' : v < 1 := lt_of_le_of_ne hv.2 hv1
      have hc := specMass_pos (M := M) hM hv.1.le hv1'
      obtain ⟨h0, h1⟩ := integral_regKernel_le hc (sq_nonneg p.1) hab
      obtain ⟨g0, g1⟩ := rho_mul_bound hM hv.1.le hv1' h0 h1
      simp only [G]
      rw [Real.norm_eq_abs, abs_of_nonneg g0]
      exact g1
    · have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with v hv1 hv
      rw [uIoc_of_le zero_le_one] at hv
      have hc := specMass_pos (M := M) hM hv.1.le (lt_of_le_of_ne hv.2 hv1)
      exact (tendsto_integral_regKernel hc).const_mul (rho v)
  refine hlim.congr' ?_
  filter_upwards [hev] with p hp
  have ha : 0 < p.1 ^ 2 := pow_pos hp.1 2
  have hab : p.1 ^ 2 < p.2 ^ 2 := by nlinarith [hp.1, hp.2.1, hp.2.2]
  have haM : p.1 ^ 2 < 4 * M ^ 2 := by
    have : p.1 ^ 2 < |M| ^ 2 := by nlinarith [hp.1, hp.2.1]
    rw [sq_abs] at this
    nlinarith [sq_nonneg M]
  have h := vpFlavour_eq hM ha hab haM
  rw [sqrt_sq hp.1.le, sqrt_sq (hp.1.trans (hp.2.1.trans hp.2.2)).le] at h
  exact h.symm

/-- **Item 1 (joint limit).** At fixed `M₁, M₂ ≠ 0`, as `(m_γ, Λ) → (0⁺, ∞)` jointly,
`vpUnitReg m_γ Λ M₁ M₂ → vpLim 1 + c₁ vpLim M₁ + c₂ vpLim M₂`. -/
theorem tendsto_vpUnitReg {M₁ M₂ : ℝ} (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) :
    Tendsto (fun p : ℝ × ℝ => vpUnitReg p.1 p.2 M₁ M₂) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (vpLim 1 + pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂)) :=
  ((tendsto_vpFlavour one_ne_zero).add ((tendsto_vpFlavour hM₁).const_mul _)).add
    ((tendsto_vpFlavour hM₂).const_mul _)

/-! ### The limited one-flavour function -/

/-- The electron flavour: `vpLim 1 = 119/36 - π²/3` (from `integral_vpUnit`). -/
theorem vpLim_one : vpLim 1 = 119 / 36 - π ^ 2 / 3 := by
  rw [← integral_vpUnit]
  simp only [vpLim, rho, f2, f2Kernel, one_pow, mul_one]

theorem intervalIntegrable_vpLim {M : ℝ} (hM : M ≠ 0) :
    IntervalIntegrable (fun v => rho v * f2 (4 * M ^ 2 / (1 - v ^ 2))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hm : Measurable rho := by unfold rho; fun_prop
  have hF : Measurable
      (Function.uncurry fun (v x : ℝ) => f2Kernel (4 * M ^ 2 / (1 - v ^ 2)) x) := by
    change Measurable fun q : ℝ × ℝ => f2Kernel (4 * M ^ 2 / (1 - q.1 ^ 2)) q.2
    unfold f2Kernel
    fun_prop
  refine Integrable.mono' (g := fun v => v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2)) ?_
    (hm.aestronglyMeasurable.mul (stronglyMeasurable_intervalIntegral hF).aestronglyMeasurable) ?_
  · exact ((by fun_prop : Continuous fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2)
      ).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_mem_Ioo] with v hv
    have hc := specMass_pos (M := M) hM hv.1.le hv.2
    obtain ⟨g0, g1⟩ := rho_mul_bound hM hv.1.le hv.2 (f2_nonneg hc) (f2_le hc)
    rw [Real.norm_eq_abs, abs_of_nonneg g0]
    exact g1

theorem vpLim_integrand_bound {M v : ℝ} (hM : M ≠ 0) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ rho v * f2 (4 * M ^ 2 / (1 - v ^ 2)) ∧
      rho v * f2 (4 * M ^ 2 / (1 - v ^ 2)) ≤ v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2) := by
  rcases hv.2.lt_or_eq with h | rfl
  · have hc := specMass_pos (M := M) hM hv.1 h
    exact rho_mul_bound hM hv.1 h (f2_nonneg hc) (f2_le hc)
  · simp only [rho]
    norm_num
    positivity

theorem vpLim_nonneg {M : ℝ} (hM : M ≠ 0) : 0 ≤ vpLim M :=
  intervalIntegral.integral_nonneg zero_le_one fun _ hv => (vpLim_integrand_bound hM hv).1

/-- **Decay.** `vpLim M ≤ 1/(45M²)`; the constant `1/45` is the leading heavy-flavour
coefficient. -/
theorem vpLim_le {M : ℝ} (hM : M ≠ 0) : vpLim M ≤ 1 / (45 * M ^ 2) := by
  have hint : ∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2) = 1 / (45 * M ^ 2) := by
    have : (fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2)) =
        fun v => (v ^ 2 - v ^ 4 / 3) / (12 * M ^ 2) := by
      funext v
      ring
    rw [this, intervalIntegral.integral_div, intervalIntegral.integral_sub
      ((continuous_pow 2).intervalIntegrable 0 1)
      (((continuous_pow 4).div_const 3).intervalIntegrable 0 1),
      intervalIntegral.integral_div, integral_pow, integral_pow]
    field_simp
    norm_num
  rw [← hint]
  exact intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_vpLim hM)
    ((by fun_prop : Continuous fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) / (12 * M ^ 2)
      ).intervalIntegrable 0 1) fun _ hv => (vpLim_integrand_bound hM hv).2

/-! ### Item 2: regulator-fermion decoupling (O2-19) -/

/-- The pointwise divided-difference bound: for `1/(P + Qμ)` the Pauli–Villars sum over the
flavours `1, 2` lies between `-(1/(P+Qμ₁) + 1/(P+Qμ₂))` and `0` (times `N ≥ 0`). -/
theorem pv_pointwise {N P Q μ₁ μ₂ : ℝ} (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hPQ : 0 < P + Q)
    (h1 : 1 ≤ μ₁) (h2 : 1 ≤ μ₂) (h12 : μ₁ ≠ μ₂) :
    -(N / (P + Q * μ₁) + N / (P + Q * μ₂)) ≤
        (μ₂ - 1) / (μ₁ - μ₂) * (N / (P + Q * μ₁)) + (μ₁ - 1) / (μ₂ - μ₁) * (N / (P + Q * μ₂)) ∧
      (μ₂ - 1) / (μ₁ - μ₂) * (N / (P + Q * μ₁)) + (μ₁ - 1) / (μ₂ - μ₁) * (N / (P + Q * μ₂)) ≤
        0 := by
  have hq1 : 0 ≤ Q * (μ₁ - 1) := mul_nonneg hQ (by linarith)
  have hq2 : 0 ≤ Q * (μ₂ - 1) := mul_nonneg hQ (by linarith)
  have hd1 : 0 < P + Q * μ₁ := by nlinarith
  have hd2 : 0 < P + Q * μ₂ := by nlinarith
  have h12' : μ₁ - μ₂ ≠ 0 := sub_ne_zero.2 h12
  have h21' : μ₂ - μ₁ ≠ 0 := sub_ne_zero.2 (Ne.symm h12)
  set K := N / (P + Q)
  set a₁ := Q * (μ₁ - 1) / (P + Q * μ₁)
  set a₂ := Q * (μ₂ - 1) / (P + Q * μ₂)
  have hK : 0 ≤ K := div_nonneg hN hPQ.le
  have ha₁ : 0 ≤ a₁ ∧ a₁ ≤ 1 :=
    ⟨div_nonneg hq1 hd1.le, (div_le_one hd1).2 (by nlinarith)⟩
  have ha₂ : 0 ≤ a₂ ∧ a₂ ≤ 1 :=
    ⟨div_nonneg hq2 hd2.le, (div_le_one hd2).2 (by nlinarith)⟩
  have hT : (μ₂ - 1) / (μ₁ - μ₂) * (N / (P + Q * μ₁)) + (μ₁ - 1) / (μ₂ - μ₁) * (N / (P + Q * μ₂)) =
      K * (a₁ * a₂ - 1) := by
    simp only [K, a₁, a₂]
    rw [div_mul_div_comm, div_mul_div_comm,
      div_add_div _ _ (mul_ne_zero h12' hd1.ne') (mul_ne_zero h21' hd2.ne'),
      div_mul_div_comm, div_sub_one (mul_ne_zero hd1.ne' hd2.ne'), div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero h12' hd1.ne') (mul_ne_zero h21' hd2.ne'))
        (mul_ne_zero hPQ.ne' (mul_ne_zero hd1.ne' hd2.ne'))]
    have e : μ₂ - μ₁ = -(μ₁ - μ₂) := by ring
    rw [e]
    ring
  have hN1 : N / (P + Q * μ₁) = K * (1 - a₁) := by
    simp only [K, a₁]
    field_simp [hd1.ne', hPQ.ne']
    ring
  have hN2 : N / (P + Q * μ₂) = K * (1 - a₂) := by
    simp only [K, a₂]
    field_simp [hd2.ne', hPQ.ne']
    ring
  rw [hT, hN1, hN2]
  have e : K * (a₁ * a₂ - 1) + (K * (1 - a₁) + K * (1 - a₂)) = K * ((1 - a₁) * (1 - a₂)) := by
    ring
  have p1 : 0 ≤ K * ((1 - a₁) * (1 - a₂)) :=
    mul_nonneg hK (mul_nonneg (by linarith) (by linarith))
  have p2 : K * (a₁ * a₂ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hK (by linarith [mul_le_of_le_one_left ha₂.1 ha₁.2, ha₂.2])
  constructor <;> linarith

/-- The same bound for `f2`, at fixed `v`. -/
theorem pv_f2_bound {w μ₁ μ₂ : ℝ} (hw : 0 < w) (h1 : 1 ≤ μ₁) (h2 : 1 ≤ μ₂) (h12 : μ₁ ≠ μ₂) :
    -(f2 (w * μ₁) + f2 (w * μ₂)) ≤
        (μ₂ - 1) / (μ₁ - μ₂) * f2 (w * μ₁) + (μ₁ - 1) / (μ₂ - μ₁) * f2 (w * μ₂) ∧
      (μ₂ - 1) / (μ₁ - μ₂) * f2 (w * μ₁) + (μ₁ - 1) / (μ₂ - μ₁) * f2 (w * μ₂) ≤ 0 := by
  have hw1 : 0 < w * μ₁ := by positivity
  have hw2 : 0 < w * μ₂ := by positivity
  have i1 := intervalIntegrable_f2Kernel hw1
  have i2 := intervalIntegrable_f2Kernel hw2
  have hpt : ∀ x ∈ Icc (0 : ℝ) 1,
      -(f2Kernel (w * μ₁) x + f2Kernel (w * μ₂) x) ≤
          (μ₂ - 1) / (μ₁ - μ₂) * f2Kernel (w * μ₁) x + (μ₁ - 1) / (μ₂ - μ₁) * f2Kernel (w * μ₂) x ∧
        (μ₂ - 1) / (μ₁ - μ₂) * f2Kernel (w * μ₁) x + (μ₁ - 1) / (μ₂ - μ₁) * f2Kernel (w * μ₂) x ≤
          0 := by
    intro x hx
    have hPQ : 0 < x ^ 2 + (1 - x) * w := den_pos hw hx
    have := pv_pointwise (N := x ^ 2 * (1 - x)) (P := x ^ 2) (Q := (1 - x) * w)
      (mul_nonneg (sq_nonneg x) (by linarith [hx.2]))
      (mul_nonneg (by linarith [hx.2]) hw.le) hPQ h1 h2 h12
    simpa only [f2Kernel, mul_assoc] using this
  have hsum : (μ₂ - 1) / (μ₁ - μ₂) * f2 (w * μ₁) + (μ₁ - 1) / (μ₂ - μ₁) * f2 (w * μ₂) =
      ∫ x in (0 : ℝ)..1,
        ((μ₂ - 1) / (μ₁ - μ₂) * f2Kernel (w * μ₁) x +
          (μ₁ - 1) / (μ₂ - μ₁) * f2Kernel (w * μ₂) x) := by
    rw [intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  have hneg : -(f2 (w * μ₁) + f2 (w * μ₂)) =
      ∫ x in (0 : ℝ)..1, -(f2Kernel (w * μ₁) x + f2Kernel (w * μ₂) x) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_add i1 i2]
    rfl
  rw [hsum, hneg]
  constructor
  · exact intervalIntegral.integral_mono_on zero_le_one (i1.add i2).neg
      ((i1.const_mul _).add (i2.const_mul _)) fun x hx => (hpt x hx).1
  · have := intervalIntegral.integral_mono_on zero_le_one
      ((i1.const_mul _).add (i2.const_mul _)) (intervalIntegrable_const (c := (0 : ℝ)))
      fun x hx => (hpt x hx).2
    simpa using this

/-- **The divided-difference bound (O2-19).** For all `M₁, M₂ ≥ 1`, with no constraint on
`M₂/M₁`: `-(vpLim M₁ + vpLim M₂) ≤ c₁ vpLim M₁ + c₂ vpLim M₂ ≤ 0`. (When `M₁² = M₂²` the
coefficients are `0` by Lean's division convention.) -/
theorem vpLimSum_bounds {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    -(vpLim M₁ + vpLim M₂) ≤ pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂ ∧
      pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂ ≤ 0 := by
  have hM₁ : M₁ ≠ 0 := by positivity
  have hM₂ : M₂ ≠ 0 := by positivity
  have n1 := vpLim_nonneg hM₁
  have n2 := vpLim_nonneg hM₂
  by_cases h : M₁ ^ 2 = M₂ ^ 2
  · simp only [pvC1, pvC2, h, sub_self, div_zero, zero_mul, add_zero]
    constructor <;> linarith
  have hμ₁ : 1 ≤ M₁ ^ 2 := by nlinarith
  have hμ₂ : 1 ≤ M₂ ^ 2 := by nlinarith
  have I1 := intervalIntegrable_vpLim hM₁
  have I2 := intervalIntegrable_vpLim hM₂
  have hpt : ∀ v ∈ Icc (0 : ℝ) 1,
      -(rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2)) + rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2))) ≤
          pvC1 M₁ M₂ * (rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2))) +
            pvC2 M₁ M₂ * (rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2))) ∧
        pvC1 M₁ M₂ * (rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2))) +
            pvC2 M₁ M₂ * (rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2))) ≤ 0 := by
    intro v hv
    rcases hv.2.lt_or_eq with hv1 | rfl
    · have hs : 0 < 1 - v ^ 2 := by nlinarith [hv.1]
      have hw : 0 < 4 / (1 - v ^ 2) := by positivity
      have hr : 0 ≤ rho v := div_nonneg (mul_nonneg (sq_nonneg v) (by nlinarith [hv.1])) hs.le
      have e1 : 4 * M₁ ^ 2 / (1 - v ^ 2) = 4 / (1 - v ^ 2) * M₁ ^ 2 := by ring
      have e2 : 4 * M₂ ^ 2 / (1 - v ^ 2) = 4 / (1 - v ^ 2) * M₂ ^ 2 := by ring
      obtain ⟨b1, b2⟩ := pv_f2_bound hw hμ₁ hμ₂ h
      rw [e1, e2]
      simp only [pvC1, pvC2]
      have m1 := mul_le_mul_of_nonneg_left b1 hr
      have m2 := mul_le_mul_of_nonneg_left b2 hr
      constructor <;> nlinarith
    · simp [rho]
  have hsum : pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂ =
      ∫ v in (0 : ℝ)..1, (pvC1 M₁ M₂ * (rho v * f2 (4 * M₁ ^ 2 / (1 - v ^ 2))) +
        pvC2 M₁ M₂ * (rho v * f2 (4 * M₂ ^ 2 / (1 - v ^ 2)))) := by
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

/-- **Item 2 with a rate.** For all `M₁, M₂ ≥ 1` (no constraint on `M₂/M₁`),
`|vpLim 1 + c₁ vpLim M₁ + c₂ vpLim M₂ - (119/36 - π²/3)| ≤ (1/M₁² + 1/M₂²)/45`. -/
theorem abs_vpLimSum_sub_le {M₁ M₂ : ℝ} (h1 : 1 ≤ M₁) (h2 : 1 ≤ M₂) :
    |vpLim 1 + pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂ - (119 / 36 - π ^ 2 / 3)| ≤
      (1 / M₁ ^ 2 + 1 / M₂ ^ 2) / 45 := by
  have hM₁ : M₁ ≠ 0 := by positivity
  have hM₂ : M₂ ≠ 0 := by positivity
  obtain ⟨b1, b2⟩ := vpLimSum_bounds h1 h2
  have l1 := vpLim_le hM₁
  have l2 := vpLim_le hM₂
  have e1 : 1 / (45 * M₁ ^ 2) = 1 / M₁ ^ 2 / 45 := by ring
  have e2 : 1 / (45 * M₂ ^ 2) = 1 / M₂ ^ 2 / 45 := by ring
  rw [← vpLim_one, abs_le]
  constructor <;> linarith

/-- **Item 2 (O2-19), joint limit.** As `M₁, M₂ → ∞` jointly (along `atTop ×ˢ atTop`, with no
constraint on `M₂/M₁`), `vpLim 1 + c₁ vpLim M₁ + c₂ vpLim M₂ → 119/36 - π²/3`. -/
theorem tendsto_vpLimSum :
    Tendsto (fun p : ℝ × ℝ => vpLim 1 + pvC1 p.1 p.2 * vpLim p.1 + pvC2 p.1 p.2 * vpLim p.2)
      (atTop ×ˢ atTop) (𝓝 (119 / 36 - π ^ 2 / 3)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have t1 : Tendsto (fun p : ℝ × ℝ => 1 / p.1 ^ 2) (atTop ×ˢ atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_fst)
  have t2 : Tendsto (fun p : ℝ × ℝ => 1 / p.2 ^ 2) (atTop ×ˢ atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_snd)
  have t := (t1.add t2).div_const 45
  rw [zero_add, zero_div] at t
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ t
  filter_upwards [(eventually_ge_atTop (1 : ℝ)).prod_inl atTop,
    (eventually_ge_atTop (1 : ℝ)).prod_inr atTop] with p hp1 hp2
  rw [Real.norm_eq_abs]
  exact abs_vpLimSum_sub_le hp1 hp2

/-- **The iterated limit in the order of D-37.4 (the quantifier shape of D-41).** For every
`η > 0` there is `R` such that for all `M₁, M₂ > R` there are `δ > 0` and `Λ₀` (depending on
`M₁, M₂`) with `|vpUnitReg m_γ Λ M₁ M₂ - (119/36 - π²/3)| < η` for all `m_γ ∈ (0, δ)` and
`Λ > Λ₀`. -/
theorem vpUnitReg_iterated_limit :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ →
        |vpUnitReg mγ Λ M₁ M₂ - (119 / 36 - π ^ 2 / 3)| < η := by
  intro η hη
  refine ⟨1 + 1 / η, fun M₁ M₂ h1 h2 => ?_⟩
  have hη' : 0 < 1 / η := by positivity
  have hM₁ : 1 < M₁ := by linarith
  have hM₂ : 1 < M₂ := by linarith
  have small : ∀ M : ℝ, 1 + 1 / η < M → 1 / M ^ 2 < η := by
    intro M hM
    have hM0 : 0 < M := by linarith
    have hle : 1 / M ^ 2 ≤ 1 / M := one_div_le_one_div_of_le hM0 (by nlinarith)
    have hlt : 1 / M < η := by
      rw [div_lt_iff₀ hM0]
      have := (div_lt_iff₀ hη).1 (show 1 / η < M by linarith)
      linarith
    linarith
  have key := abs_vpLimSum_sub_le hM₁.le hM₂.le
  have s1 := small M₁ h1
  have s2 := small M₂ h2
  have hL : |vpLim 1 + pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂ - (119 / 36 - π ^ 2 / 3)| <
      η / 2 := by linarith
  have hT := (Metric.tendsto_nhds.1 (tendsto_vpUnitReg (M₁ := M₁) (M₂ := M₂)
    (by positivity) (by positivity)))
    (η / 2) (by positivity)
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := eventually_prod_iff.1 hT
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hpa
  obtain ⟨Λ₀, hΛ₀⟩ := eventually_atTop.1 hpb
  refine ⟨u, hu, Λ₀, fun mγ Λ hm0 hm1 hΛ => ?_⟩
  have hd := hall (hsub ⟨hm0, hm1⟩) (hΛ₀ Λ hΛ.le)
  rw [Real.dist_eq] at hd
  have := abs_sub_le (vpUnitReg mγ Λ M₁ M₂)
    (vpLim 1 + pvC1 M₁ M₂ * vpLim M₁ + pvC2 M₁ M₂ * vpLim M₂) (119 / 36 - π ^ 2 / 3)
  linarith

end QED.TwoLoop.VPUnit
