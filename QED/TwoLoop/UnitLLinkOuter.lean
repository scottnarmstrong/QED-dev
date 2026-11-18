/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLS
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder unit L: the `x`-integration of the limit remainder

Section 3.4 of `docs/TWO-LOOP-UNITS.md`, one step of stage (3) of the L link (the limit
`λ → 0`). In the finite-`λ` representation (3.4) the remainder `R = G - T₁` (the `x`-integrand
minus the term carrying the soft outer photon) has the `λ`-independent limit

`R₀(Y, x) = (1-x)/2 · [-Y log Y - Y log W + (1-Y) P/Y² · (log x + log(1-Y) - log W)
  + (10Y²x - Y² - 10Yx + 4Y - 2)/Y]`,

with `W = Y + (1-Y)x` and `P = 12Y²x² - 13Y²x + 2Y² - 12Yx² + 8Yx - 2Y - 2x` (`ladderR0`;
derived from (3.4) at `λ = 0`, see `QED/TwoLoop/UnitLLinkLimit.lean` for the pointwise limit).
This file proves that its `x`-integral is the kernel of eq. (3.6):

`∫₀¹ R₀(Y, x) dx = K_L(Y)` for `0 < Y < 1` (`integral_ladderR0`),

by an explicit antiderivative `a(x) log x + b(x) log W + c(x)` with quartic `a, b, c`
(`ladderR0Anti`), continuous on `[0, 1]` (`a(0) = 0`, and `b` vanishes at the root of `W`, so that
`b(x)(1-Y)/W` is polynomial).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.TwoLoop.UnitLLink

open QED.TwoLoop.Units

/-! ### Quartic polynomials -/

/-- The quartic `c₀ + c₁ x + c₂ x² + c₃ x³ + c₄ x⁴`. -/
def quart (c₀ c₁ c₂ c₃ c₄ x : ℝ) : ℝ := c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4

/-- The derivative `c₁ + 2 c₂ x + 3 c₃ x² + 4 c₄ x³` of `quart c₀ c₁ c₂ c₃ c₄`. -/
def dquart (c₁ c₂ c₃ c₄ x : ℝ) : ℝ := c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 + 4 * c₄ * x ^ 3

theorem hasDerivAt_quart (c₀ c₁ c₂ c₃ c₄ x : ℝ) :
    HasDerivAt (quart c₀ c₁ c₂ c₃ c₄) (dquart c₁ c₂ c₃ c₄ x) x := by
  have h := (((((hasDerivAt_const x c₀).add ((hasDerivAt_id x).const_mul c₁)).add
    ((hasDerivAt_pow 2 x).const_mul c₂)).add ((hasDerivAt_pow 3 x).const_mul c₃)).add
    ((hasDerivAt_pow 4 x).const_mul c₄))
  convert h using 1
  · funext y; simp [quart]
  · simp [dquart]; ring

theorem continuous_quart (c₀ c₁ c₂ c₃ c₄ : ℝ) : Continuous (quart c₀ c₁ c₂ c₃ c₄) := by
  unfold quart; fun_prop

/-! ### The remainder at `λ = 0` -/

/-- `W = Y + (1 - Y) x`, the argument of the logarithm `log(M + c h)` at `λ = 0`, divided by `Y`. -/
def ladderW (Y x : ℝ) : ℝ := Y + (1 - Y) * x

/-- The polynomial `P` of the coefficient `(1 - Y) P / Y²` of `R₀`. -/
def ladderP (Y x : ℝ) : ℝ :=
  12 * Y ^ 2 * x ^ 2 - 13 * Y ^ 2 * x + 2 * Y ^ 2 - 12 * Y * x ^ 2 + 8 * Y * x - 2 * Y - 2 * x

/-- **The limit remainder** `R₀(Y, x)` of section 3.4 of the document. -/
noncomputable def ladderR0 (Y x : ℝ) : ℝ :=
  (1 - x) / 2 * (-Y * log Y - Y * log (ladderW Y x) +
    (1 - Y) * ladderP Y x / Y ^ 2 * (log x + log (1 - Y) - log (ladderW Y x)) +
    (10 * Y ^ 2 * x - Y ^ 2 - 10 * Y * x + 4 * Y - 2) / Y)

/-! ### The antiderivative -/

/-- The coefficient of `log x` in the antiderivative. -/
noncomputable def antiA (Y x : ℝ) : ℝ :=
  quart 0 (-(Y - 1) ^ 2 / Y) ((Y - 1) * (15 * Y ^ 2 - 10 * Y + 2) / (4 * Y ^ 2))
    (-(Y - 1) * (25 * Y ^ 2 - 20 * Y + 2) / (6 * Y ^ 2)) (3 * (Y - 1) ^ 2 / (2 * Y)) x

/-- The coefficient of `log W` in the antiderivative. -/
noncomputable def antiB (Y x : ℝ) : ℝ :=
  quart ((4 * Y ^ 3 - 5 * Y ^ 2 - 4 * Y + 6) / (12 * (Y - 1) ^ 2)) ((Y ^ 2 - 4 * Y + 2) / (2 * Y))
    (-(14 * Y ^ 3 - 25 * Y ^ 2 + 12 * Y - 2) / (4 * Y ^ 2))
    ((Y - 1) * (25 * Y ^ 2 - 20 * Y + 2) / (6 * Y ^ 2)) (-3 * (Y - 1) ^ 2 / (2 * Y)) x

/-- The remaining part of the antiderivative (`a = log Y`, `b = log(1 - Y)`). -/
noncomputable def antiC (Y x : ℝ) : ℝ :=
  quart 0
    (-(12 * log (1 - Y) * Y ^ 3 - 36 * log (1 - Y) * Y ^ 2 + 36 * log (1 - Y) * Y -
      12 * log (1 - Y) + 6 * log Y * Y ^ 3 - 6 * log Y * Y ^ 2 - 10 * Y ^ 3 + 11 * Y ^ 2 + 4 * Y -
      6) / (12 * Y * (Y - 1)))
    ((90 * log (1 - Y) * Y ^ 3 - 150 * log (1 - Y) * Y ^ 2 + 72 * log (1 - Y) * Y -
      12 * log (1 - Y) + 6 * log Y * Y ^ 3 + 31 * Y ^ 3 - 44 * Y ^ 2 + 8 * Y) / (24 * Y ^ 2))
    (-(Y - 1) * (25 * log (1 - Y) * Y ^ 2 - 20 * log (1 - Y) * Y + 2 * log (1 - Y) + 7 * Y ^ 2) /
      (6 * Y ^ 2))
    (3 * log (1 - Y) * (Y - 1) ^ 2 / (2 * Y)) x

/-- `b(x) (1 - Y) / W`, a polynomial in `x` since `b` vanishes at the root of `W`. -/
noncomputable def antiQ (Y x : ℝ) : ℝ :=
  quart (-(4 * Y ^ 3 - 5 * Y ^ 2 - 4 * Y + 6) / (12 * Y * (Y - 1)))
    (-(10 * Y ^ 3 - 35 * Y ^ 2 + 32 * Y - 6) / (12 * Y ^ 2))
    ((Y - 1) * (8 * Y ^ 2 - 10 * Y + 1) / (3 * Y ^ 2)) (-3 * (Y - 1) ^ 2 / (2 * Y)) 0 x

theorem antiB_mul_div {Y x : ℝ} (hY0 : Y ≠ 0) (hY1 : Y - 1 ≠ 0) (hW0 : Y + (1 - Y) * x ≠ 0) :
    antiB Y x * ((1 - Y) / (Y + (1 - Y) * x)) = antiQ Y x := by
  rw [mul_div_assoc', div_eq_iff hW0]
  simp only [antiB, antiQ, quart]
  field_simp
  ring

/-- **The antiderivative of `R₀` in `x`**: `a(x) log x + b(x) log W + c(x)`. -/
noncomputable def ladderR0Anti (Y x : ℝ) : ℝ :=
  antiA Y x * log x + antiB Y x * log (ladderW Y x) + antiC Y x

theorem ladderW_pos {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : 0 ≤ x) : 0 < ladderW Y x := by
  unfold ladderW
  have : 0 ≤ (1 - Y) * x := mul_nonneg (by linarith [hY.2]) hx
  linarith [hY.1]

theorem hasDerivAt_ladderR0Anti {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    HasDerivAt (ladderR0Anti Y) (ladderR0 Y x) x := by
  have hW := ladderW_pos hY hx.le
  have hWd : HasDerivAt (ladderW Y) (1 - Y) x := by
    have h := ((hasDerivAt_id x).const_mul (1 - Y)).const_add Y
    convert h using 1
    · funext y; simp [ladderW]
    · ring
  have hA : HasDerivAt (antiA Y) (dquart (-(Y - 1) ^ 2 / Y)
      ((Y - 1) * (15 * Y ^ 2 - 10 * Y + 2) / (4 * Y ^ 2))
      (-(Y - 1) * (25 * Y ^ 2 - 20 * Y + 2) / (6 * Y ^ 2)) (3 * (Y - 1) ^ 2 / (2 * Y)) x) x := by
    unfold antiA; exact hasDerivAt_quart _ _ _ _ _ x
  have hB : HasDerivAt (antiB Y) (dquart ((Y ^ 2 - 4 * Y + 2) / (2 * Y))
      (-(14 * Y ^ 3 - 25 * Y ^ 2 + 12 * Y - 2) / (4 * Y ^ 2))
      ((Y - 1) * (25 * Y ^ 2 - 20 * Y + 2) / (6 * Y ^ 2)) (-3 * (Y - 1) ^ 2 / (2 * Y)) x) x := by
    unfold antiB; exact hasDerivAt_quart _ _ _ _ _ x
  have hC : HasDerivAt (antiC Y) (dquart
      (-(12 * log (1 - Y) * Y ^ 3 - 36 * log (1 - Y) * Y ^ 2 + 36 * log (1 - Y) * Y -
        12 * log (1 - Y) + 6 * log Y * Y ^ 3 - 6 * log Y * Y ^ 2 - 10 * Y ^ 3 + 11 * Y ^ 2 +
        4 * Y - 6) / (12 * Y * (Y - 1)))
      ((90 * log (1 - Y) * Y ^ 3 - 150 * log (1 - Y) * Y ^ 2 + 72 * log (1 - Y) * Y -
        12 * log (1 - Y) + 6 * log Y * Y ^ 3 + 31 * Y ^ 3 - 44 * Y ^ 2 + 8 * Y) / (24 * Y ^ 2))
      (-(Y - 1) * (25 * log (1 - Y) * Y ^ 2 - 20 * log (1 - Y) * Y + 2 * log (1 - Y) +
        7 * Y ^ 2) / (6 * Y ^ 2))
      (3 * log (1 - Y) * (Y - 1) ^ 2 / (2 * Y)) x) x := by
    unfold antiC; exact hasDerivAt_quart _ _ _ _ _ x
  have h := ((hA.mul (hasDerivAt_log hx.ne')).add (hB.mul (hWd.log hW.ne'))).add hC
  refine h.congr_deriv ?_
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hx0 : x ≠ 0 := hx.ne'
  have hW0 : Y + (1 - Y) * x ≠ 0 := hW.ne'
  have hq := antiB_mul_div hY0 hY1 hW0
  simp only [ladderR0, ladderP, ladderW] at hq ⊢
  rw [hq]
  generalize log x = lx
  generalize log (Y + (1 - Y) * x) = lW
  generalize log Y = a
  generalize log (1 - Y) = b
  simp only [antiA, antiQ, quart, dquart]
  field_simp
  ring

theorem continuousOn_ladderR0Anti {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (ladderR0Anti Y) (Icc 0 1) := by
  have e1 : (fun x => antiA Y x * log x) = fun x =>
      quart (-(Y - 1) ^ 2 / Y) ((Y - 1) * (15 * Y ^ 2 - 10 * Y + 2) / (4 * Y ^ 2))
        (-(Y - 1) * (25 * Y ^ 2 - 20 * Y + 2) / (6 * Y ^ 2)) (3 * (Y - 1) ^ 2 / (2 * Y)) 0 x *
        (x * log x) := by
    funext x; simp only [antiA, quart]; ring
  have hA : Continuous fun x => antiA Y x * log x := by
    rw [e1]; exact (continuous_quart _ _ _ _ _).mul continuous_mul_log
  have hB : ContinuousOn (fun x => antiB Y x * log (ladderW Y x)) (Icc 0 1) := by
    refine ContinuousOn.mul (continuous_quart _ _ _ _ _).continuousOn ?_
    refine ContinuousOn.log (by unfold ladderW; fun_prop) fun x hx => (ladderW_pos hY hx.1).ne'
  have hC : Continuous (antiC Y) := continuous_quart _ _ _ _ _
  exact (hA.continuousOn.add hB).add hC.continuousOn

theorem intervalIntegrable_ladderR0 {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (ladderR0 Y) volume 0 1 := by
  set g₁ : ℝ → ℝ := fun x => (1 - x) / 2 * ((1 - Y) * ladderP Y x / Y ^ 2) with hg₁
  set g₂ : ℝ → ℝ := fun x => (1 - x) / 2 * (-Y * log Y - Y * log (ladderW Y x) +
    (1 - Y) * ladderP Y x / Y ^ 2 * (log (1 - Y) - log (ladderW Y x)) +
    (10 * Y ^ 2 * x - Y ^ 2 - 10 * Y * x + 4 * Y - 2) / Y) with hg₂
  have e : ladderR0 Y = fun x => g₁ x * log x + g₂ x := by
    funext x; simp only [ladderR0, hg₁, hg₂]; ring
  have hlogW : ContinuousOn (fun x => log (ladderW Y x)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ContinuousOn.log (by unfold ladderW; fun_prop) fun x hx => (ladderW_pos hY hx.1).ne'
  have h₁ : ContinuousOn g₁ (uIcc 0 1) := by
    simp only [hg₁, ladderP]; fun_prop
  have h₂ : ContinuousOn g₂ (uIcc 0 1) := by
    simp only [hg₂, ladderP]
    exact ContinuousOn.mul (by fun_prop) ((((continuousOn_const.sub
      (continuousOn_const.mul hlogW))).add ((by fun_prop : ContinuousOn
        (fun x => (1 - Y) * (12 * Y ^ 2 * x ^ 2 - 13 * Y ^ 2 * x + 2 * Y ^ 2 - 12 * Y * x ^ 2 +
          8 * Y * x - 2 * Y - 2 * x) / Y ^ 2) (uIcc 0 1)).mul
        (continuousOn_const.sub hlogW))).add (by fun_prop))
  rw [e]
  exact (intervalIntegral.intervalIntegrable_log'.continuousOn_mul h₁).add
    (h₂.intervalIntegrable)

/-- `K_L` written out on `(0, 1)` (its definition, through `ladderKernel_eq`). -/
theorem ladderKernel_eq' {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ladderKernel Y =
      (Y ^ 3 + 3 * Y ^ 2 - 2 * Y - 2) * log (1 - Y) / (12 * Y ^ 2) +
        (-7 * Y ^ 3 + 11 * Y ^ 2 + Y - 6) * log Y / (12 * (1 - Y) ^ 2) -
        (23 * Y ^ 3 - 41 * Y ^ 2 + 16 * Y + 4) / (24 * Y * (1 - Y)) := by
  rw [ladderKernel_eq hY, sub_sub_cancel]
  have h1 : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
  have h0 : Y ≠ 0 := hY.1.ne'
  generalize log Y = a
  generalize log (1 - Y) = b
  field_simp
  ring

/-- **The `x`-integral of the limit remainder is the kernel of eq. (3.6)**:
`∫₀¹ R₀(Y, x) dx = K_L(Y)` for `0 < Y < 1`. -/
theorem integral_ladderR0 {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, ladderR0 Y x = ladderKernel Y := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_ladderR0Anti hY) (fun x hx => hasDerivAt_ladderR0Anti hY hx.1)
    (intervalIntegrable_ladderR0 hY)]
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hY1' : 1 - Y ≠ 0 := by linarith [hY.2]
  have hW1 : ladderW Y 1 = 1 := by unfold ladderW; ring
  have hW0 : ladderW Y 0 = Y := by unfold ladderW; ring
  rw [ladderKernel_eq' hY]
  simp only [ladderR0Anti, hW1, hW0, log_one, log_zero, mul_zero, add_zero, antiA, antiB, antiC,
    quart]
  generalize log Y = a
  generalize log (1 - Y) = b
  field_simp
  ring

end QED.TwoLoop.UnitLLink

end
