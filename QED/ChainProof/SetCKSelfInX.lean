/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitSMasters
public import QED.ChainProof.SetCKPairS
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G1: the inner-massive self-energy unit, integrated over `x`

Helper level (no frozen statement). In the **inner-massive** placement of the self-energy unit
`S` (the photon of mass² `t` inside the self-energy subgraph, the outer photon massless) the
`x`-integrand of eq. (5.3) of `docs/TWO-LOOP-UNITS.md` is `selfGm 0 (√t) Y x`, with `h = x`.
At infinite Pauli–Villars mass its regulator partner leaves the `M`-independent polynomial
`D(Y, x) = (1-x)(Y x - Y - x + 3)/4 = -k₂/x²` (`selfInSub`), so the `x`-integrand of the unit is
`selfGm 0 (√t) Y x - D(Y, x)`. This file integrates it over `x` in closed form, for arbitrary
`c, M > 0` (in the unit `c = Y(1-Y)` and `M = M_t(Y)`):

* `selfInG Y c M x`: the shape `sForm` of eq. (5.3) at `h = x`, minus `D`;
* `selfGm_zero_sub_eq_selfInG`: in the unit, `selfGm 0 (√t) Y x - D = selfInG Y (Y(1-Y)) M_t x`;
* **`integral_selfInG`**: `∫₀¹ selfInG Y c M x dx = Φ_S(Y, c, M)` (`selfInPhi`), a combination of
  `log(M + c)`, `log M`, `log c` with rational coefficients. The integrand is a quartic in `x`
  times `log(M + c x)` or `log(c x)`, plus a cubic: there is no dilogarithm.

The proof is the fundamental theorem of calculus with the antiderivative
`P₁ log(M + c x) - T₁ + P₃ log c + S₃ · x log x - T₃ + P₀` (`selfInXF`), whose polynomials
(Horner lists, `hpoly`) were generated in exact arithmetic (sympy, scratch `g1/genX.py`).
-/

@[expose] public section

open MeasureTheory Set Real

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit

/-- `D(Y, x) = (1-x)(Y x - Y - x + 3)/4 = -k₂/x²`, the infinite-regulator remainder. -/
noncomputable def selfInSub (Y x : ℝ) : ℝ := (1 - x) * (Y * x - Y - x + 3) / 4

/-- **The inner-massive self-energy integrand** at `h = x`, minus `D`. -/
noncomputable def selfInG (Y c M x : ℝ) : ℝ :=
  sForm (selfK1 Y x) (selfK2 Y x) c x M (log (M + c * x)) (log (1 + M / (c * x))) -
    selfInSub Y x

/-- The coefficient of `log(M + c x)` in `selfInG` (coefficients in `x`). -/
noncomputable def selfInXp1 (Y c M : ℝ) : List ℝ :=
  [-(3*Y + 1)/4, -(-M + Y*c + 2*c)/M, -(-3*M ^ 2*Y + 3*M ^ 2 + 4*M*Y*c - 16*M*c + Y*c ^ 2 +
    7*c ^ 2)/(4*M ^ 2), -c*(-2*M*Y + 2*M + Y*c - 3*c)/M ^ 2, 5*c ^ 2*(Y - 1)/(4*M ^ 2)]

/-- The coefficient of `log c + log x` in `selfInG` (coefficients in `x`). -/
noncomputable def selfInXp3 (Y c M : ℝ) : List ℝ :=
  [0, c*(Y + 2)/M, c*(4*M*Y - 16*M + Y*c + 7*c)/(4*M ^ 2), c*(-2*M*Y + 2*M + Y*c - 3*c)/M ^ 2,
    -5*c ^ 2*(Y - 1)/(4*M ^ 2)]

/-- The rational part of `selfInG` (coefficients in `x`). -/
noncomputable def selfInXp0 (Y c M : ℝ) : List ℝ :=
  [0, c*(Y + 7)/(4*M), c*(Y - 3)/M, -5*c*(Y - 1)/(4*M)]

/-- `P₁`, the antiderivative of `p₁` vanishing at `x = -M/c` (coefficients in `x`). -/
noncomputable def selfInXP1 (Y c M : ℝ) : List ℝ :=
  [-M*(M*Y - M + 4*Y*c - 2*c)/(12*c ^ 2), -(3*Y + 1)/4, -(-M + Y*c + 2*c)/(2*M), -(-3*M ^ 2*Y +
    3*M ^ 2 + 4*M*Y*c - 16*M*c + Y*c ^ 2 + 7*c ^ 2)/(12*M ^ 2), -c*(-2*M*Y + 2*M + Y*c -
    3*c)/(4*M ^ 2), c ^ 2*(Y - 1)/(4*M ^ 2)]

/-- `T₁`, the antiderivative of `P₁ c/(M + c x)` vanishing at `0` (coefficients in `x`). -/
noncomputable def selfInXT1 (Y c M : ℝ) : List ℝ :=
  [0, -(M*Y - M + 4*Y*c - 2*c)/(12*c), -(-M*Y + M + 5*Y*c + 5*c)/(24*M), -c*(M*Y - 7*M + Y*c +
    7*c)/(36*M ^ 2), -c*(-M*Y + M + Y*c - 3*c)/(16*M ^ 2), c ^ 2*(Y - 1)/(20*M ^ 2)]

/-- `P₃`, the antiderivative of `p₃` vanishing at `0` (coefficients in `x`). -/
noncomputable def selfInXP3 (Y c M : ℝ) : List ℝ :=
  [0, 0, c*(Y + 2)/(2*M), c*(4*M*Y - 16*M + Y*c + 7*c)/(12*M ^ 2), c*(-2*M*Y + 2*M + Y*c -
    3*c)/(4*M ^ 2), -c ^ 2*(Y - 1)/(4*M ^ 2)]

/-- `S₃ = P₃/x` (coefficients in `x`). -/
noncomputable def selfInXS3 (Y c M : ℝ) : List ℝ :=
  [0, c*(Y + 2)/(2*M), c*(4*M*Y - 16*M + Y*c + 7*c)/(12*M ^ 2), c*(-2*M*Y + 2*M + Y*c -
    3*c)/(4*M ^ 2), -c ^ 2*(Y - 1)/(4*M ^ 2)]

/-- `T₃`, the antiderivative of `S₃` vanishing at `0` (coefficients in `x`). -/
noncomputable def selfInXT3 (Y c M : ℝ) : List ℝ :=
  [0, 0, c*(Y + 2)/(4*M), c*(4*M*Y - 16*M + Y*c + 7*c)/(36*M ^ 2), c*(-2*M*Y + 2*M + Y*c -
    3*c)/(16*M ^ 2), -c ^ 2*(Y - 1)/(20*M ^ 2)]

/-- `P₀`, the antiderivative of `p₀` vanishing at `0` (coefficients in `x`). -/
noncomputable def selfInXP0 (Y c M : ℝ) : List ℝ :=
  [0, 0, c*(Y + 7)/(8*M), c*(Y - 3)/(3*M), -5*c*(Y - 1)/(16*M)]

/-- **The closed form** `Φ_S(Y, c, M) = ∫₀¹ selfInG Y c M x dx`. -/
noncomputable def selfInPhi (Y c M : ℝ) : ℝ :=
  (-(M + c) ^ 3*(M*Y - M + Y*c + c)/(12*M ^ 2*c ^ 2)) * log (M + c) +
    (M*(M*Y - M + 4*Y*c - 2*c)/(12*c ^ 2)) * log M +
    (c*(4*M*Y + 2*M + Y*c + c)/(12*M ^ 2)) * log c +
    ((2*M ^ 2*Y - 2*M ^ 2 + 7*M*Y*c - 3*M*c + 2*Y*c ^ 2 + 2*c ^ 2)/(24*M*c))

theorem selfInG_eq {Y c M x : ℝ} (hc : 0 < c) (hM : 0 < M) (hx : 0 < x) :
    selfInG Y c M x = hpoly (selfInXp1 Y c M) x * log (M + c * x) +
      hpoly (selfInXp3 Y c M) x * (log c + log x) + hpoly (selfInXp0 Y c M) x := by
  have hMx : 0 < M + c * x := by positivity
  have e : log (1 + M / (c * x)) = log (M + c * x) - log c - log x := by
    rw [show 1 + M / (c * x) = (M + c * x) / (c * x) by field_simp; ring,
      log_div hMx.ne' (by positivity), log_mul hc.ne' hx.ne']
    ring
  have := hM.ne'
  have := hc.ne'
  have := hx.ne'
  unfold selfInG sForm selfInSub selfK1 selfK2 selfInXp1 selfInXp3 selfInXp0
  rw [e]
  simp only [hpoly]
  field_simp
  ring

/-- The antiderivative of `selfInG` in `x`. -/
noncomputable def selfInXF (Y c M x : ℝ) : ℝ :=
  hpoly (selfInXP1 Y c M) x * log (M + c * x) - hpoly (selfInXT1 Y c M) x +
    hpoly (selfInXP3 Y c M) x * log c + hpoly (selfInXS3 Y c M) x * (x * log x) -
    hpoly (selfInXT3 Y c M) x + hpoly (selfInXP0 Y c M) x

theorem hasDerivAt_selfInXF {Y c M x : ℝ} (hc : 0 < c) (hM : 0 < M) (hx : 0 < x) :
    HasDerivAt (selfInXF Y c M) (selfInG Y c M x) x := by
  have hMx : 0 < M + c * x := by positivity
  have hlog : HasDerivAt (fun x => log (M + c * x)) (c / (M + c * x)) x := by
    simpa using (((hasDerivAt_id' x).const_mul c).const_add M).log hMx.ne'
  have h := (((((hasDerivAt_hpoly (selfInXP1 Y c M) x).mul hlog).sub
    (hasDerivAt_hpoly (selfInXT1 Y c M) x)).add
    ((hasDerivAt_hpoly (selfInXP3 Y c M) x).mul_const (log c))).add
    ((hasDerivAt_hpoly (selfInXS3 Y c M) x).mul (hasDerivAt_mul_log hx.ne'))).sub
    (hasDerivAt_hpoly (selfInXT3 Y c M) x) |>.add (hasDerivAt_hpoly (selfInXP0 Y c M) x)
  convert h using 1
  · funext y
    rfl
  rw [selfInG_eq hc hM hx]
  have := hM.ne'
  have := hc.ne'
  have := hMx.ne'
  simp only [selfInXP1, selfInXT1, selfInXP3, selfInXS3, selfInXT3, selfInXP0, selfInXp1,
    selfInXp3, selfInXp0, hpoly, hpolyD]
  field_simp
  ring

theorem continuousOn_selfInXF {Y c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ContinuousOn (selfInXF Y c M) (Icc 0 1) := by
  have hlog : ContinuousOn (fun x => log (M + c * x)) (Icc 0 1) := by
    refine ContinuousOn.log (by fun_prop) fun x hx => ?_
    have : 0 ≤ c * x := mul_nonneg hc.le hx.1
    positivity
  unfold selfInXF
  have := continuous_mul_log.continuousOn (s := Icc (0 : ℝ) 1)
  fun_prop

theorem intervalIntegrable_selfInG {Y c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    IntervalIntegrable (selfInG Y c M) volume 0 1 := by
  have hlog : ContinuousOn (fun x => log (M + c * x)) (uIcc 0 1) := by
    refine ContinuousOn.log (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    have : 0 ≤ c * x := mul_nonneg hc.le hx.1
    positivity
  have hint : IntervalIntegrable (fun x => hpoly (selfInXp1 Y c M) x * log (M + c * x) +
      hpoly (selfInXp3 Y c M) x * (log c + log x) + hpoly (selfInXp0 Y c M) x) volume 0 1 := by
    refine ((((continuous_hpoly _).continuousOn.mul hlog).intervalIntegrable).add ?_).add
      (continuous_hpoly _).continuousOn.intervalIntegrable
    exact (intervalIntegrable_const.add intervalIntegral.intervalIntegrable_log').continuousOn_mul
      (continuous_hpoly _).continuousOn
  refine hint.congr ?_
  rw [uIoc_of_le zero_le_one]
  exact fun x hx => (selfInG_eq hc hM hx.1).symm

/-- `selfInXF 1 - selfInXF 0 = Φ_S`. -/
theorem selfInXF_one_sub_zero {Y c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    selfInXF Y c M 1 - selfInXF Y c M 0 = selfInPhi Y c M := by
  unfold selfInXF selfInPhi
  simp only [selfInXP1, selfInXT1, selfInXP3, selfInXS3, selfInXT3, selfInXP0, hpoly, mul_one,
    mul_zero, add_zero, log_one, zero_mul, zero_add, sub_zero]
  have := hM.ne'
  have := hc.ne'
  field_simp
  ring

/-- **The `x`-integration of the inner-massive self-energy integrand**:
`∫₀¹ selfInG Y c M x dx = Φ_S(Y, c, M)` for `c, M > 0`. -/
theorem integral_selfInG {Y c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∫ x in (0 : ℝ)..1, selfInG Y c M x = selfInPhi Y c M := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_selfInXF hc hM) (fun x hx => hasDerivAt_selfInXF hc hM hx.1)
    (intervalIntegrable_selfInG hc hM), selfInXF_one_sub_zero hc hM]

/-- **The unit's inner-massive integrand**: `selfGm 0 (√t) Y x - D(Y, x)` is
`selfInG Y (Y(1-Y)) M_t x`, `M_t = Y² + (1-Y) t`. -/
theorem selfGm_zero_sub_eq_selfInG {t Y x : ℝ} (hx : x ≠ 0) :
    selfGm 0 (√t) Y x - selfInSub Y x =
      selfInG Y (Y * (1 - Y)) (ladderInnerMass 1 (√t) Y) x := by
  rw [selfGm, ladderInnerMass_zero_div hx]
  rfl

end QED.ChainProof.SetCK

end
