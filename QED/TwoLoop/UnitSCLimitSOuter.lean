/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitSMasters
public import QED.TwoLoop.UnitLLinkOuter
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The self-energy unit S: the `x`-integration at `λ = 0`

Sections 5.4 and 5.5 of `docs/TWO-LOOP-UNITS.md`, stage (4) of the `S + C` link for the
self-energy pair (the analogue of `QED/TwoLoop/UnitLLinkOuter.lean`). At photon mass `λ` the
`x`-integrand of eq. (5.3) is `G_S(λ) = E_S - e₀ = selfGm λ λ + k₂/h²` (`selfR`: the `a`-integral
at `M = M_λ`, with the large-`M` constant `e₀ = -k₂/h²` of section 2.3 removed). At `λ = 0`
(`M = Y²`, `h = x`, `W = Y + (1-Y) x`) it is (`selfR_zero_eq`)

`G_S(0) = r + c_W log W + c_x (log x + log(1-Y)) + c_Y log Y`

with `r = x(Y-1)(x-1)(5Yx + Y - 5x + 7)/(4Y)`, `c_Y = (x-1)(3Yx + 3Y - 3x + 1)/4` and quartic
`c_W`, `c_x` over `Y²` (`selfR0`). This file proves that its `x`-integral is the kernel of eq. (5.5):

`∫₀¹ G_S(0; Y, x) dx = K_S(Y)` for `0 < Y < 1` (`integral_selfR_zero`, with
`K_S = QED.TwoLoop.Units.selfEnergyKernel`),

by an explicit antiderivative `A(x) log x + B(x) log W + C(x)` with quintic `A, B, C`
(`selfR0Anti`; `A(0) = 0`, and `B` vanishes at the root of `W`). Generated with sympy and checked
there in exact arithmetic.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitSCLimit

open QED.TwoLoop.UnitLLink QED.TwoLoop.Units

/-! ### Quintic polynomials -/

/-- The quintic `c₀ + c₁ x + c₂ x² + c₃ x³ + c₄ x⁴ + c₅ x⁵`. -/
def quint (c₀ c₁ c₂ c₃ c₄ c₅ x : ℝ) : ℝ :=
  c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4 + c₅ * x ^ 5

/-- The derivative of `quint c₀ c₁ c₂ c₃ c₄ c₅`. -/
def dquint (c₁ c₂ c₃ c₄ c₅ x : ℝ) : ℝ :=
  c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 + 4 * c₄ * x ^ 3 + 5 * c₅ * x ^ 4

theorem hasDerivAt_quint (c₀ c₁ c₂ c₃ c₄ c₅ x : ℝ) :
    HasDerivAt (quint c₀ c₁ c₂ c₃ c₄ c₅) (dquint c₁ c₂ c₃ c₄ c₅ x) x := by
  have h := ((((((hasDerivAt_const x c₀).add ((hasDerivAt_id x).const_mul c₁)).add
    ((hasDerivAt_pow 2 x).const_mul c₂)).add ((hasDerivAt_pow 3 x).const_mul c₃)).add
    ((hasDerivAt_pow 4 x).const_mul c₄)).add ((hasDerivAt_pow 5 x).const_mul c₅))
  convert h using 1
  · funext y; simp [quint]
  · simp [dquint]; ring

theorem continuous_quint (c₀ c₁ c₂ c₃ c₄ c₅ : ℝ) : Continuous (quint c₀ c₁ c₂ c₃ c₄ c₅) := by
  unfold quint; fun_prop

/-! ### The integrand at `λ = 0` -/

/-- **The `x`-integrand of eq. (5.3)** at photon mass `λ`: `G_S = selfGm λ λ + k₂/h²`
(the large-`M` constant `e₀ = -k₂/h²` removed). -/
noncomputable def selfR (lam Y x : ℝ) : ℝ :=
  selfGm lam lam Y x + selfK2 Y x / (ladderInnerMass 1 lam x / x) ^ 2

/-- The coefficient `c_W` of `log W` in `G_S(0)`. -/
noncomputable def selfCW (Y x : ℝ) : ℝ :=
  -((x - 1) * ladderW Y x * (5 * Y ^ 2 * x ^ 2 - 2 * Y ^ 2 * x - 3 * Y ^ 2 - 10 * Y * x ^ 2 +
    9 * Y * x - Y + 5 * x ^ 2 - 7 * x)) / (4 * Y ^ 2)

/-- The coefficient `c_x` of `log x + log(1 - Y)` in `G_S(0)`. -/
noncomputable def selfCX (Y x : ℝ) : ℝ :=
  -(x * (Y - 1) * (x - 1) * (5 * Y ^ 2 * x ^ 2 - 7 * Y ^ 2 * x - 4 * Y ^ 2 - 10 * Y * x ^ 2 +
    14 * Y * x - 8 * Y + 5 * x ^ 2 - 7 * x)) / (4 * Y ^ 2)

/-- **`G_S` at `λ = 0`, explicitly**:
`r + c_W log W + c_x (log x + log(1-Y)) + c_Y log Y`. -/
noncomputable def selfR0 (Y x : ℝ) : ℝ :=
  x * (Y - 1) * (x - 1) * (5 * Y * x + Y - 5 * x + 7) / (4 * Y) +
    selfCW Y x * log (ladderW Y x) + selfCX Y x * (log x + log (1 - Y)) +
    (x - 1) * (3 * Y * x + 3 * Y - 3 * x + 1) / 4 * log Y

/-- **At `λ = 0` the integrand is `selfR0`.** -/
theorem selfR_zero_eq {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    selfR 0 Y x = selfR0 Y x := by
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hx0 : x ≠ 0 := hx.1.ne'
  have hW := ladderW_pos hY hx.1.le
  have hM : ladderInnerMass 1 0 Y = Y ^ 2 := by unfold ladderInnerMass; ring
  have hh : ladderInnerMass 1 0 x / x = x := by
    unfold ladderInnerMass; rw [div_eq_iff hx0]; ring
  have e1 : Y ^ 2 + Y * (1 - Y) * x = Y * ladderW Y x := by unfold ladderW; ring
  have e2 : 1 + Y ^ 2 / (Y * (1 - Y) * x) = ladderW Y x / ((1 - Y) * x) := by
    unfold ladderW; field_simp; ring
  have hl1 : log (Y ^ 2 + Y * (1 - Y) * x) = log Y + log (ladderW Y x) := by
    rw [e1, log_mul hY0 hW.ne']
  have hl2 : log (1 + Y ^ 2 / (Y * (1 - Y) * x)) = log (ladderW Y x) - log (1 - Y) - log x := by
    rw [e2, log_div hW.ne' (by positivity), log_mul hY1.ne' hx0]
    ring
  unfold selfR selfGm
  rw [hM, hh, hl1, hl2]
  have hY1' : (1 : ℝ) - Y ≠ 0 := hY1.ne'
  have hWne : ladderW Y x ≠ 0 := hW.ne'
  have eW : Y ^ 2 + Y * (1 - Y) * x = Y * ladderW Y x := e1
  have hD : Y ^ 2 + Y * (1 - Y) * x ≠ 0 := by rw [eW]; exact mul_ne_zero hY0 hWne
  simp only [sForm, selfK1, selfK2, selfR0, selfCW, selfCX]
  generalize log x = lx
  generalize log (ladderW Y x) = lW
  generalize log Y = a
  generalize log (1 - Y) = b
  unfold ladderW
  have hWne' : x - x * Y + Y ≠ 0 := by
    have := hWne; unfold ladderW at this
    rw [show x - x * Y + Y = Y + (1 - Y) * x by ring]; exact this
  have hWne'' : Y + x * (1 - Y) ≠ 0 := by
    have := hWne; unfold ladderW at this
    rw [show Y + x * (1 - Y) = Y + (1 - Y) * x by ring]; exact this
  field_simp
  ring

/-! ### The antiderivative -/

/-- The coefficient of `log x` in the antiderivative. -/
noncomputable def sAntiA (Y x : ℝ) : ℝ :=
  quint 0 0 (-(Y - 1) * (Y + 2) / (2 * Y)) (-(Y - 7) * (Y - 1) * (3 * Y - 1) / (12 * Y ^ 2))
    (3 * (Y - 1) ^ 3 / (4 * Y ^ 2)) (-(Y - 1) ^ 3 / (4 * Y ^ 2)) x

/-- The coefficient of `log W` in the antiderivative. -/
noncomputable def sAntiB (Y x : ℝ) : ℝ :=
  quint (Y * (3 * Y - 2) / (12 * (Y - 1))) (-(3 * Y + 1) / 4) ((Y ^ 2 + 2 * Y - 2) / (2 * Y))
    ((Y - 1) * (6 * Y ^ 2 - 22 * Y + 7) / (12 * Y ^ 2)) (-3 * (Y - 1) ^ 3 / (4 * Y ^ 2))
    ((Y - 1) ^ 3 / (4 * Y ^ 2)) x

/-- The remaining part of the antiderivative (`a = log Y`, `b = log(1 - Y)`). -/
noncomputable def sAntiC (Y x : ℝ) : ℝ :=
  quint 0 (-(9 * Y * log Y - 3 * Y + 3 * log Y + 2) / 12)
    ((-12 * Y ^ 2 * log (1 - Y) - 3 * Y ^ 2 + 12 * Y * log Y - 12 * Y * log (1 - Y) - 11 * Y +
      24 * log (1 - Y) + 14) / (24 * Y))
    ((Y - 1) * (3 * Y ^ 2 * log Y - 3 * Y ^ 2 * log (1 - Y) - 3 * Y ^ 2 + 22 * Y * log (1 - Y) +
      9 * Y - 7 * log (1 - Y)) / (12 * Y ^ 2))
    ((Y - 1) ^ 2 * (3 * Y * log (1 - Y) + Y - 3 * log (1 - Y)) / (4 * Y ^ 2))
    (-(log (1 - Y)) * (Y - 1) ^ 3 / (4 * Y ^ 2)) x

/-- `B(x) (1 - Y)/W`, a polynomial in `x` since `B` vanishes at the root of `W`. -/
noncomputable def sAntiQ (Y x : ℝ) : ℝ :=
  quint (-(3 * Y - 2) / 12) ((Y - 1) * (6 * Y + 5) / (12 * Y)) (-(Y - 1) * (13 * Y - 7) / (12 * Y ^ 2))
    (-(Y - 1) ^ 2 * (2 * Y - 3) / (4 * Y ^ 2)) ((Y - 1) ^ 3 / (4 * Y ^ 2)) 0 x

theorem sAntiB_mul_div {Y x : ℝ} (hY0 : Y ≠ 0) (hY1 : Y - 1 ≠ 0) (hW0 : Y + (1 - Y) * x ≠ 0) :
    sAntiB Y x * ((1 - Y) / (Y + (1 - Y) * x)) = sAntiQ Y x := by
  rw [mul_div_assoc', div_eq_iff hW0]
  simp only [sAntiB, sAntiQ, quint]
  field_simp
  ring

/-- **The antiderivative of `G_S(0)` in `x`**: `A(x) log x + B(x) log W + C(x)`. -/
noncomputable def selfR0Anti (Y x : ℝ) : ℝ :=
  sAntiA Y x * log x + sAntiB Y x * log (ladderW Y x) + sAntiC Y x

theorem hasDerivAt_selfR0Anti {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    HasDerivAt (selfR0Anti Y) (selfR0 Y x) x := by
  have hW := ladderW_pos hY hx.le
  have hWd : HasDerivAt (ladderW Y) (1 - Y) x := by
    have h := ((hasDerivAt_id x).const_mul (1 - Y)).const_add Y
    convert h using 1
    · funext y; simp [ladderW]
    · ring
  have hA : HasDerivAt (sAntiA Y) (dquint 0 (-(Y - 1) * (Y + 2) / (2 * Y))
      (-(Y - 7) * (Y - 1) * (3 * Y - 1) / (12 * Y ^ 2))
      (3 * (Y - 1) ^ 3 / (4 * Y ^ 2)) (-(Y - 1) ^ 3 / (4 * Y ^ 2)) x) x := by
    unfold sAntiA; exact hasDerivAt_quint _ _ _ _ _ _ x
  have hB : HasDerivAt (sAntiB Y) (dquint (-(3 * Y + 1) / 4) ((Y ^ 2 + 2 * Y - 2) / (2 * Y))
      ((Y - 1) * (6 * Y ^ 2 - 22 * Y + 7) / (12 * Y ^ 2)) (-3 * (Y - 1) ^ 3 / (4 * Y ^ 2))
      ((Y - 1) ^ 3 / (4 * Y ^ 2)) x) x := by
    unfold sAntiB; exact hasDerivAt_quint _ _ _ _ _ _ x
  have hC : HasDerivAt (sAntiC Y) (dquint (-(9 * Y * log Y - 3 * Y + 3 * log Y + 2) / 12)
      ((-12 * Y ^ 2 * log (1 - Y) - 3 * Y ^ 2 + 12 * Y * log Y - 12 * Y * log (1 - Y) - 11 * Y +
        24 * log (1 - Y) + 14) / (24 * Y))
      ((Y - 1) * (3 * Y ^ 2 * log Y - 3 * Y ^ 2 * log (1 - Y) - 3 * Y ^ 2 + 22 * Y * log (1 - Y) +
        9 * Y - 7 * log (1 - Y)) / (12 * Y ^ 2))
      ((Y - 1) ^ 2 * (3 * Y * log (1 - Y) + Y - 3 * log (1 - Y)) / (4 * Y ^ 2))
      (-(log (1 - Y)) * (Y - 1) ^ 3 / (4 * Y ^ 2)) x) x := by
    unfold sAntiC; exact hasDerivAt_quint _ _ _ _ _ _ x
  have h := ((hA.mul (hasDerivAt_log hx.ne')).add (hB.mul (hWd.log hW.ne'))).add hC
  refine h.congr_deriv ?_
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hx0 : x ≠ 0 := hx.ne'
  have hW0 : Y + (1 - Y) * x ≠ 0 := hW.ne'
  have hq := sAntiB_mul_div hY0 hY1 hW0
  simp only [selfR0, selfCW, selfCX, ladderW] at hq ⊢
  rw [hq]
  generalize log x = lx
  generalize log (Y + (1 - Y) * x) = lW
  generalize log Y = a
  generalize log (1 - Y) = b
  simp only [sAntiA, sAntiQ, quint, dquint]
  field_simp
  ring

theorem continuousOn_selfR0Anti {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (selfR0Anti Y) (Icc 0 1) := by
  have e1 : (fun x => sAntiA Y x * log x) = fun x =>
      quint 0 (-(Y - 1) * (Y + 2) / (2 * Y)) (-(Y - 7) * (Y - 1) * (3 * Y - 1) / (12 * Y ^ 2))
        (3 * (Y - 1) ^ 3 / (4 * Y ^ 2)) (-(Y - 1) ^ 3 / (4 * Y ^ 2)) 0 x * (x * log x) := by
    funext x; simp only [sAntiA, quint]; ring
  have hA : Continuous fun x => sAntiA Y x * log x := by
    rw [e1]; exact (continuous_quint _ _ _ _ _ _).mul continuous_mul_log
  have hB : ContinuousOn (fun x => sAntiB Y x * log (ladderW Y x)) (Icc 0 1) := by
    refine ContinuousOn.mul (continuous_quint _ _ _ _ _ _).continuousOn ?_
    refine ContinuousOn.log (by unfold ladderW; fun_prop) fun x hx => (ladderW_pos hY hx.1).ne'
  have hC : Continuous (sAntiC Y) := continuous_quint _ _ _ _ _ _
  exact (hA.continuousOn.add hB).add hC.continuousOn

theorem intervalIntegrable_selfR0 {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (selfR0 Y) volume 0 1 := by
  set g₂ : ℝ → ℝ := fun x => x * (Y - 1) * (x - 1) * (5 * Y * x + Y - 5 * x + 7) / (4 * Y) +
    selfCW Y x * log (ladderW Y x) + selfCX Y x * log (1 - Y) +
    (x - 1) * (3 * Y * x + 3 * Y - 3 * x + 1) / 4 * log Y with hg₂
  have e : selfR0 Y = fun x => selfCX Y x * log x + g₂ x := by
    funext x; simp only [selfR0, hg₂]; ring
  have hlogW : ContinuousOn (fun x => log (ladderW Y x)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ContinuousOn.log (by unfold ladderW; fun_prop) fun x hx => (ladderW_pos hY hx.1).ne'
  have h₁ : ContinuousOn (selfCX Y) (uIcc 0 1) := by
    unfold selfCX; fun_prop
  have h₂ : ContinuousOn g₂ (uIcc 0 1) := by
    simp only [hg₂]
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (by fun_prop)
      ((by unfold selfCW ladderW; fun_prop : ContinuousOn (selfCW Y) (uIcc 0 1)).mul hlogW))
      (by unfold selfCX; fun_prop)) (by fun_prop)
  rw [e]
  exact (intervalIntegral.intervalIntegrable_log'.continuousOn_mul h₁).add h₂.intervalIntegrable

/-- **The `x`-integral of `G_S(0)` is the kernel of eq. (5.5)**:
`∫₀¹ G_S(0; Y, x) dx = K_S(Y)` for `0 < Y < 1`. -/
theorem integral_selfR0 {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, selfR0 Y x = selfEnergyKernel Y := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_selfR0Anti hY) (fun x hx => hasDerivAt_selfR0Anti hY hx.1)
    (intervalIntegrable_selfR0 hY)]
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hY1' : 1 - Y ≠ 0 := by linarith [hY.2]
  have hW1 : ladderW Y 1 = 1 := by unfold ladderW; ring
  have hW0 : ladderW Y 0 = Y := by unfold ladderW; ring
  rw [selfEnergyKernel_eq hY, sub_sub_cancel]
  simp only [selfR0Anti, hW1, hW0, log_one, log_zero, mul_zero, add_zero, sAntiA, sAntiB, sAntiC,
    quint]
  generalize log Y = a
  generalize log (1 - Y) = b
  field_simp
  ring

/-- **The `x`-integral of the integrand at `λ = 0`** is `K_S(Y)`, for `0 < Y < 1`. -/
theorem integral_selfR_zero {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, selfR 0 Y x = selfEnergyKernel Y := by
  rw [← integral_selfR0 hY]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
  rw [uIoc_of_le zero_le_one] at hx
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · -- the endpoint `x = 1`: both sides vanish there
    subst h1
    have hY0 : Y ≠ 0 := hY.1.ne'
    have hY1 : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
    simp only [selfR, selfGm, sForm, selfK1, selfK2, selfR0, selfCW, selfCX, ladderInnerMass,
      ladderW]
    norm_num
  · exact selfR_zero_eq hY ⟨hx.1, h1⟩

end QED.TwoLoop.UnitSCLimit

end
