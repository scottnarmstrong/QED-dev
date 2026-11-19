/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLCloseMasters
public import QED.ChainProof.SetCKOneLoop
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K: the inner-massive ladder, integrated over the outer parameter

Helper level (no frozen statement). In the **inner-massive** placement of the ladder unit (the
photon of mass² `t` inside the vertex subgraph, the outer photon massless) the representation
(3.4) of `docs/TWO-LOOP-UNITS.md` has `h = x`, and the soft-outer-photon logarithm is isolated by
the term `T₁` of section 3.4 at `λ = 0`. This file integrates the subtracted integrand over the
outer Feynman parameter `x` in closed form, for an arbitrary inner mass `M > 0` and an arbitrary
`c > 0` (in the unit, `c = Y(1-Y)` and `M = M_t(Y) = Y² + (1-Y) t`):

* `innerG Y c M x = gForm(Y x(1-x)/2, c, x q₀, x, M, log(M + c x), log(1 + M/(c x)))
    + Y c (1-x)³/(x M)`: the shape `gForm` of eq. (3.4) (`QED.TwoLoop.UnitLLink.gForm`) at
  `h = x`, plus `-T₁`;
* `ladderGm_zero_add_eq_innerG`: in the unit, `ladderGm 0 (√t) Y x + Y c(1-x)³/(x M_t)` is
  `innerG Y (Y(1-Y)) M_t x`;
* **`integral_innerG`**: `∫₀¹ innerG Y c M x dx = Φ_in(Y, c, M)` (`phiIn`), an explicit
  combination of `log(M + c)`, `log M`, `log c` with rational coefficients. There is no
  dilogarithm: after the subtraction of `T₁` the integrand is a cubic in `x` times
  `log(M + c x)` or `log(c x)`, plus a quadratic.

The proof is the fundamental theorem of calculus with the explicit antiderivative
`P₁ log(M + c x) - T₁ + P₃ log c + S₃ · x log x - T₃ + P₀` (`innerXF`), whose polynomials were
generated in exact arithmetic (sympy) and are checked here by `field_simp; ring`.

`Φ_in` is the input of the inner placement's Stieltjes density: its singularities in `M`
(the cut of `log M` and `log(M + c)` and the poles at `M = 0`) give the fibre density.
-/

@[expose] public section

open MeasureTheory Set Real

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- A polynomial of degree at most four, `a₀ + a₁ x + a₂ x² + a₃ x³ + a₄ x⁴`. -/
def poly4 (a₀ a₁ a₂ a₃ a₄ x : ℝ) : ℝ := a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4

theorem hasDerivAt_poly4 (a₀ a₁ a₂ a₃ a₄ x : ℝ) :
    HasDerivAt (poly4 a₀ a₁ a₂ a₃ a₄)
      (a₁ + 2 * a₂ * x + 3 * a₃ * x ^ 2 + 4 * a₄ * x ^ 3) x := by
  have h := (((((hasDerivAt_id' x).const_mul a₁).const_add a₀).add
    ((hasDerivAt_pow 2 x).const_mul a₂)).add ((hasDerivAt_pow 3 x).const_mul a₃)).add
    ((hasDerivAt_pow 4 x).const_mul a₄)
  convert h using 1
  · funext y
    simp only [poly4, Pi.add_apply]
  · norm_num
    ring

theorem continuous_poly4 (a₀ a₁ a₂ a₃ a₄ : ℝ) : Continuous (poly4 a₀ a₁ a₂ a₃ a₄) := by
  unfold poly4
  fun_prop

/-- `x q₀ = x (3Y - 2) + (4Y - Y² - 2)(1 - x) - 2c(1-x)²/x`, the numerator `q` of `gForm` at
`h = x`. -/
noncomputable def innerXq (Y c x : ℝ) : ℝ :=
  x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) - 2 * c * ((1 - x) / x) ^ 2)

/-- **The inner-massive ladder integrand** at `h = x`, with the soft-outer-photon term `T₁`
(section 3.4 of `docs/TWO-LOOP-UNITS.md`, at `λ = 0`) subtracted. -/
noncomputable def innerG (Y c M x : ℝ) : ℝ :=
  gForm (Y * x * (1 - x) / 2) c (innerXq Y c x) x M (log (M + c * x)) (log (1 + M / (c * x))) +
    Y * c * (1 - x) ^ 3 / (x * M)

/-- The coefficient of `log(M + c x)` in `innerG`. -/
noncomputable def innerXp1 (Y c M x : ℝ) : ℝ :=
  poly4
    (Y*(-M ^ 2 + 2*c ^ 2)/(2*M ^ 2))
    (-Y*(-M ^ 2 - 8*M*c - Y ^ 2*c + 4*Y*c + 6*c ^ 2 - 2*c)/(2*M ^ 2))
    (Y*c*(-8*M - 2*Y ^ 2 + 5*Y + 15*c - 2)/(2*M ^ 2))
    (-Y*c*(-Y ^ 2 + Y + 11*c)/(2*M ^ 2))
    (0) x

/-- The coefficient of `log(c x)` in `innerG`. -/
noncomputable def innerXp3 (Y c M x : ℝ) : ℝ :=
  poly4
    (-Y*c ^ 2/M ^ 2)
    (Y*c*(-8*M - Y ^ 2 + 4*Y + 6*c - 2)/(2*M ^ 2))
    (-Y*c*(-8*M - 2*Y ^ 2 + 5*Y + 15*c - 2)/(2*M ^ 2))
    (Y*c*(-Y ^ 2 + Y + 11*c)/(2*M ^ 2))
    (0) x

/-- The rational part of `innerG`. -/
noncomputable def innerXp0 (Y c M x : ℝ) : ℝ :=
  poly4
    (-Y*(Y ^ 2 - 4*Y + 2)/(2*M))
    (-Y*(-2*Y ^ 2 + 5*Y + 9*c - 2)/(2*M))
    (Y*(-Y ^ 2 + Y + 9*c)/(2*M))
    (0)
    (0) x

/-- `P₁`, the antiderivative of the `log(M + c x)` coefficient vanishing at `x = -M/c`. -/
noncomputable def innerXP1 (Y c M x : ℝ) : ℝ :=
  poly4
    (Y*(-3*M ^ 3*Y ^ 2 + 3*M ^ 3*Y - 5*M ^ 3*c - 8*M ^ 2*Y ^ 2*c + 20*M ^ 2*Y*c - 8*M ^ 2*c -
      6*M*Y ^ 2*c ^ 2 + 24*M*Y*c ^ 2 + 36*M*c ^ 3 - 12*M*c ^ 2 + 24*c ^ 4)/(24*M*c ^ 3))
    (Y*(-M ^ 2 + 2*c ^ 2)/(2*M ^ 2))
    (-Y*(-M ^ 2 - 8*M*c - Y ^ 2*c + 4*Y*c + 6*c ^ 2 - 2*c)/(4*M ^ 2))
    (Y*c*(-8*M - 2*Y ^ 2 + 5*Y + 15*c - 2)/(6*M ^ 2))
    (-Y*c*(-Y ^ 2 + Y + 11*c)/(8*M ^ 2)) x

/-- `T₁`, an antiderivative of `P₁ c/(M + c x)` (a polynomial). -/
noncomputable def innerXT1 (Y c M x : ℝ) : ℝ :=
  poly4
    (0)
    (Y*(-3*M ^ 3*Y ^ 2 + 3*M ^ 3*Y - 5*M ^ 3*c - 8*M ^ 2*Y ^ 2*c + 20*M ^ 2*Y*c - 8*M ^ 2*c -
      6*M*Y ^ 2*c ^ 2 + 24*M*Y*c ^ 2 + 36*M*c ^ 3 - 12*M*c ^ 2 + 24*c ^ 4)/(24*M ^ 2*c ^ 2))
    (-Y*(-3*M ^ 2*Y ^ 2 + 3*M ^ 2*Y - 5*M ^ 2*c - 8*M*Y ^ 2*c + 20*M*Y*c + 12*M*c ^ 2 - 8*M*c -
      6*Y ^ 2*c ^ 2 + 24*Y*c ^ 2 + 36*c ^ 3 - 12*c ^ 2)/(48*M ^ 2*c))
    (Y*(-3*M*Y ^ 2 + 3*M*Y + M*c - 8*Y ^ 2*c + 20*Y*c + 60*c ^ 2 - 8*c)/(72*M ^ 2))
    (-Y*c*(-Y ^ 2 + Y + 11*c)/(32*M ^ 2)) x

/-- `P₃`, the antiderivative of the `log(c x)` coefficient vanishing at `0`. -/
noncomputable def innerXP3 (Y c M x : ℝ) : ℝ :=
  poly4
    (0)
    (-Y*c ^ 2/M ^ 2)
    (Y*c*(-8*M - Y ^ 2 + 4*Y + 6*c - 2)/(4*M ^ 2))
    (-Y*c*(-8*M - 2*Y ^ 2 + 5*Y + 15*c - 2)/(6*M ^ 2))
    (Y*c*(-Y ^ 2 + Y + 11*c)/(8*M ^ 2)) x

/-- `S₃ = P₃/x`. -/
noncomputable def innerXS3 (Y c M x : ℝ) : ℝ :=
  poly4
    (-Y*c ^ 2/M ^ 2)
    (Y*c*(-8*M - Y ^ 2 + 4*Y + 6*c - 2)/(4*M ^ 2))
    (-Y*c*(-8*M - 2*Y ^ 2 + 5*Y + 15*c - 2)/(6*M ^ 2))
    (Y*c*(-Y ^ 2 + Y + 11*c)/(8*M ^ 2))
    (0) x

/-- `T₃`, an antiderivative of `S₃`. -/
noncomputable def innerXT3 (Y c M x : ℝ) : ℝ :=
  poly4
    (0)
    (-Y*c ^ 2/M ^ 2)
    (Y*c*(-8*M - Y ^ 2 + 4*Y + 6*c - 2)/(8*M ^ 2))
    (-Y*c*(-8*M - 2*Y ^ 2 + 5*Y + 15*c - 2)/(18*M ^ 2))
    (Y*c*(-Y ^ 2 + Y + 11*c)/(32*M ^ 2)) x

/-- `P₀`, an antiderivative of the rational part. -/
noncomputable def innerXP0 (Y c M x : ℝ) : ℝ :=
  poly4
    (0)
    (-Y*(Y ^ 2 - 4*Y + 2)/(2*M))
    (-Y*(-2*Y ^ 2 + 5*Y + 9*c - 2)/(4*M))
    (Y*(-Y ^ 2 + Y + 9*c)/(6*M))
    (0) x

/-- **The closed form** `Φ_in(Y, c, M) = ∫₀¹ G_in dx`. -/
noncomputable def phiIn (Y c M : ℝ) : ℝ :=
  (Y*(M + c) ^ 2*(-3*M ^ 2*Y ^ 2 + 3*M ^ 2*Y - 5*M ^ 2*c - 2*M*Y ^ 2*c + 14*M*Y*c + 10*M*c ^ 2
      - 8*M*c + Y ^ 2*c ^ 2 - 7*Y*c ^ 2 + 15*c ^ 3 + 4*c ^ 2)/(24*M ^ 2*c ^ 3)) * log (M + c) +
    (-Y*(-3*M ^ 3*Y ^ 2 + 3*M ^ 3*Y - 5*M ^ 3*c - 8*M ^ 2*Y ^ 2*c + 20*M ^ 2*Y*c - 8*M ^ 2*c -
      6*M*Y ^ 2*c ^ 2 + 24*M*Y*c ^ 2 + 36*M*c ^ 3 - 12*M*c ^ 2 + 24*c ^ 4)/(24*M*c ^ 3)) * log M +
    (-Y*c*(16*M + Y ^ 2 - 7*Y + 15*c + 4)/(24*M ^ 2)) * log c +
    (-Y*(-6*M ^ 2*Y ^ 2 + 6*M ^ 2*Y - 10*M ^ 2*c - 13*M*Y ^ 2*c + 37*M*Y*c + 5*M*c ^ 2 - 16*M*c
      + 2*Y ^ 2*c ^ 2 - 14*Y*c ^ 2 + 70*c ^ 3 + 8*c ^ 2)/(48*M*c ^ 2))
/-- `innerG` as a cubic times `log(M + c x)`, a cubic times `log c + log x`, plus a quadratic. -/
theorem innerG_eq {Y c M x : ℝ} (hc : 0 < c) (hM : 0 < M) (hx : 0 < x) :
    innerG Y c M x = innerXp1 Y c M x * log (M + c * x) +
      innerXp3 Y c M x * (log c + log x) + innerXp0 Y c M x := by
  have hMx : 0 < M + c * x := by positivity
  have e : log (1 + M / (c * x)) = log (M + c * x) - log c - log x := by
    rw [show 1 + M / (c * x) = (M + c * x) / (c * x) by field_simp; ring,
      log_div hMx.ne' (by positivity), log_mul hc.ne' hx.ne']
    ring
  unfold innerG gForm innerXq innerXp1 innerXp3 innerXp0 poly4
  rw [e]
  field_simp
  ring

/-- The antiderivative of `innerG` in `x`:
`P₁ log(M + c x) - T₁ + P₃ log c + S₃ · x log x - T₃ + P₀`. -/
noncomputable def innerXF (Y c M x : ℝ) : ℝ :=
  innerXP1 Y c M x * log (M + c * x) - innerXT1 Y c M x + innerXP3 Y c M x * log c +
    innerXS3 Y c M x * (x * log x) - innerXT3 Y c M x + innerXP0 Y c M x

theorem hasDerivAt_innerXF {Y c M x : ℝ} (hc : 0 < c) (hM : 0 < M) (hx : 0 < x) :
    HasDerivAt (innerXF Y c M) (innerG Y c M x) x := by
  have hMx : 0 < M + c * x := by positivity
  have hlog : HasDerivAt (fun x => log (M + c * x)) (c / (M + c * x)) x := by
    simpa using (((hasDerivAt_id' x).const_mul c).const_add M).log hMx.ne'
  have dP1 : HasDerivAt (innerXP1 Y c M) _ x := hasDerivAt_poly4 _ _ _ _ _ x
  have dT1 : HasDerivAt (innerXT1 Y c M) _ x := hasDerivAt_poly4 _ _ _ _ _ x
  have dP3 : HasDerivAt (innerXP3 Y c M) _ x := hasDerivAt_poly4 _ _ _ _ _ x
  have dS3 : HasDerivAt (innerXS3 Y c M) _ x := hasDerivAt_poly4 _ _ _ _ _ x
  have dT3 : HasDerivAt (innerXT3 Y c M) _ x := hasDerivAt_poly4 _ _ _ _ _ x
  have dP0 : HasDerivAt (innerXP0 Y c M) _ x := hasDerivAt_poly4 _ _ _ _ _ x
  have h := (((((dP1.mul hlog).sub dT1).add (dP3.mul_const (log c))).add
    (dS3.mul (hasDerivAt_mul_log hx.ne'))).sub dT3).add dP0
  convert h using 1
  · funext y
    rfl
  · rw [innerG_eq hc hM hx]
    simp only [innerXP1, innerXS3, innerXp1, innerXp3, innerXp0, poly4]
    field_simp
    ring

theorem continuousOn_innerXF {Y c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ContinuousOn (innerXF Y c M) (Icc 0 1) := by
  have hlog : ContinuousOn (fun x => log (M + c * x)) (Icc 0 1) := by
    refine ContinuousOn.log (by fun_prop) fun x hx => ?_
    have : 0 ≤ c * x := mul_nonneg hc.le hx.1
    positivity
  unfold innerXF innerXP1 innerXT1 innerXP3 innerXS3 innerXT3 innerXP0
  exact ((((((continuous_poly4 _ _ _ _ _).continuousOn.mul hlog).sub
    (continuous_poly4 _ _ _ _ _).continuousOn).add
    ((continuous_poly4 _ _ _ _ _).continuousOn.mul continuousOn_const)).add
    ((continuous_poly4 _ _ _ _ _).continuousOn.mul continuous_mul_log.continuousOn)).sub
    (continuous_poly4 _ _ _ _ _).continuousOn).add (continuous_poly4 _ _ _ _ _).continuousOn

theorem intervalIntegrable_innerG {Y c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    IntervalIntegrable (innerG Y c M) volume 0 1 := by
  have hlog : ContinuousOn (fun x => log (M + c * x)) (uIcc 0 1) := by
    refine ContinuousOn.log (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    have : 0 ≤ c * x := mul_nonneg hc.le hx.1
    positivity
  have hint : IntervalIntegrable (fun x => innerXp1 Y c M x * log (M + c * x) +
      innerXp3 Y c M x * (log c + log x) + innerXp0 Y c M x) volume 0 1 := by
    refine (((((continuous_poly4 _ _ _ _ _).continuousOn.mul hlog).intervalIntegrable).add ?_).add
      (continuous_poly4 _ _ _ _ _).continuousOn.intervalIntegrable)
    exact (intervalIntegrable_const.add intervalIntegral.intervalIntegrable_log').continuousOn_mul
      (continuous_poly4 _ _ _ _ _).continuousOn
  refine hint.congr ?_
  rw [uIoc_of_le zero_le_one]
  exact fun x hx => (innerG_eq hc hM hx.1).symm

/-- `innerXF 1 - innerXF 0 = Φ_in`. -/
theorem innerXF_one_sub_zero {Y c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    innerXF Y c M 1 - innerXF Y c M 0 = phiIn Y c M := by
  unfold innerXF innerXP1 innerXT1 innerXP3 innerXS3 innerXT3 innerXP0 phiIn poly4
  simp only [mul_one, mul_zero, add_zero, log_one, one_pow, zero_mul, zero_add, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  have := hM.ne'
  have := hc.ne'
  field_simp
  ring

/-- **The `x`-integration of the inner-massive ladder** (soft-outer term subtracted):
`∫₀¹ innerG Y c M x dx = Φ_in(Y, c, M)` for `c, M > 0`. -/
theorem integral_innerG {Y c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∫ x in (0 : ℝ)..1, innerG Y c M x = phiIn Y c M := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_innerXF hc hM) (fun x hx => hasDerivAt_innerXF hc hM hx.1)
    (intervalIntegrable_innerG hc hM), innerXF_one_sub_zero hc hM]

/-! ### The unit's inner-massive integrand -/

/-- At zero outer photon mass, `h = x`. -/
theorem ladderInnerMass_zero_div {x : ℝ} (hx : x ≠ 0) : ladderInnerMass 1 0 x / x = x := by
  unfold ladderInnerMass
  field_simp
  ring

/-- **The inner-massive ladder integrand**: `ladderGm 0 (√t) Y x + Y c (1-x)³/(x M_t)` is
`innerG Y (Y(1-Y)) M_t x`, `M_t = Y² + (1-Y) t`. -/
theorem ladderGm_zero_add_eq_innerG {t Y x : ℝ} (hx : x ≠ 0) :
    ladderGm 0 (√t) Y x + Y * (Y * (1 - Y)) * (1 - x) ^ 3 / (x * ladderInnerMass 1 (√t) Y) =
      innerG Y (Y * (1 - Y)) (ladderInnerMass 1 (√t) Y) x := by
  rw [ladderGm_eq_form, ladderInnerMass_zero_div hx]
  rfl

end QED.ChainProof.SetCK

end
