/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.HeavyLeptonLimits
public import QED.Chain.VPChainSetB
public import QED.Polylog.Landen
public import QED.Polylog.Reflection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The heavy-lepton VP insertion in closed form (O3-M3)

Helper-level result for obligation O3-M3 of `docs/HIGHER-LOOP-PLAN.md` (section 3 (c)). It is
**not** frozen; `QED.Chain.HeavyLepton.a2Heavy` is a plain definition.

For a vacuum-polarization loop of mass `M = 1/y` (`0 < y < 1`) inserted in the one-loop vertex
of a lepton of mass `1`, with `Π̂_M(s) = Π̂(s/M²) = QED.Chain.piHat (y² s)`, the coefficient is

`A(y) = ∫₀¹ (1-x) Π̂_{1/y}(x²/(1-x)) dx = ∫₀¹ (1-x) Π̂(y² x²/(1-x)) dx`.

## The closed form (Passera (10))

Passera (2007), eq. (10), with `x = m_j/m_l` (here `x = M = 1/y > 1`, real parts understood):

`A₂⁽⁴⁾(1/x) = -25/36 - (ln x)/3 + x²(4 + 3 ln x) + (x/2)(1 - 5x²)[π²/2 - ln x ln((1-x)/(1+x))
  - Li₂(x) + Li₂(-x)] + x⁴[π²/3 - 2 ln x ln(1/x - x) - Li₂(x²)]`.

With `x = 1/y`, `Re Li₂(1/y) = π²/3 - ln²y/2 - Li₂(y)` and `Li₂(-1/y) = -π²/6 - ln²y/2 - Li₂(-y)`
(inversion), the bracket becomes `ln y ln((1-y)/(1+y)) + Li₂(y) - Li₂(-y)` and the last term
`y⁻⁴[2 ln y ln(1-y²) + Li₂(y²)]`, giving `a2Heavy`:

`A(y) = -25/36 + (ln y)/3 + (4 - 3 ln y)/y² + (y² - 5)/(2y³) · [ln y ln((1-y)/(1+y)) + Li₂(y)
  - Li₂(-y)] + [2 ln y ln(1-y²) + Li₂(y²)]/y⁴`.

Every function here is real on `0 < y < 1`, and `Li₂ = QED.Polylog.Li₂` (the power series) is
evaluated only at `y, -y, y² ∈ (-1, 1)`. The agreement of this form with Passera (10) at `x = 1/y`
is checked numerically in `scripts/numerics/phase5_chains.py`, section B (to `10⁻²⁹`), and
`scripts/numerics/chain/heavy_lepton.py`, step 5 (to `10⁻³⁵`); the
inversion step itself is not formalized (Passera's `Li₂` at `x > 1` is outside the domain of
`QED.Polylog.Li₂`).

## Route

The substitution `x = (1-w²)/(1+yw)` (`QED/Chain/HeavyLeptonParam.lean`) rationalizes the
integrand, an explicit antiderivative in `w` (`QED/Chain/HeavyLeptonPrim.lean`) has one-sided
limits at both ends (`QED/Chain/HeavyLeptonLimits.lean`), and the dilogarithm identities
(reflection, Landen, `Li₂(y) + Li₂(-y) = Li₂(y²)/2`) bring the difference of the limits to the
form above. In the variable `x` the antiderivative is `-hlPrim y (omega y x)`.

## Main statements

* `intervalIntegrable_heavy`, `integral_heavy`: integrability, and `A(y) = a2Heavy y`.
* `heavyIntegral_nonneg`, `heavyIntegral_le`: `0 ≤ A(y) ≤ y²/45`; `tendsto_heavyIntegral_zero`:
  `A(y) → 0` as `y → 0⁺`.
* `heavyIntegral_mono`: `A` is monotone on `(0,1)`.
* `tendsto_a2Heavy_one`: `a2Heavy y → 119/36 - π²/3 = ∫₀¹ (1-x) Π̂(x²/(1-x)) dx` (the electron
  value, `QED.Chain.integral_oneBubble`) as `y → 1⁻`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.Chain.HeavyLepton

/-- The heavy-lepton insertion `A(y) = ∫₀¹ (1-x) Π̂(y² x²/(1-x)) dx` (loop mass `1/y`). -/
noncomputable def heavyIntegral (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x)))

/-- **The closed form of Passera (10)** at `x = 1/y`, written with `log` and `Li₂` at `y`, `-y`,
`y²` (not frozen). -/
noncomputable def a2Heavy (y : ℝ) : ℝ :=
  -25 / 36 + log y / 3 + (4 - 3 * log y) / y ^ 2 +
    (y ^ 2 - 5) / (2 * y ^ 3) * (log y * log ((1 - y) / (1 + y)) + Li₂ y - Li₂ (-y)) +
    (2 * log y * log (1 - y ^ 2) + Li₂ (y ^ 2)) / y ^ 4

/-! ### The antiderivative in `x` -/

/-- The antiderivative in `x`: `-hlPrim y (omega y x)`. -/
noncomputable def heavyPrimX (y x : ℝ) : ℝ := -hlPrim y (omega y x)

theorem hasDerivAt_heavyPrimX {y x : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (heavyPrimX y) ((1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x)))) x := by
  have hw := omega_mem_Ioo hy.1 hx
  have hj := jac_pos hy.1 hw.1.le
  have h := ((hasDerivAt_hlPrim hy hw).comp x (hasDerivAt_omega hy.1 hx)).neg
  refine h.congr_deriv ?_
  rw [← integrandW_eq hy.1 hw, heavy_integrand_eq hy.1 hx]
  field_simp

theorem tendsto_heavyPrimX_zero {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (heavyPrimX y) (𝓝[>] 0) (𝓝 (-hlPrimOne y)) :=
  ((tendsto_hlPrim_one hy).comp (tendsto_omega_zero hy.1)).neg

theorem tendsto_heavyPrimX_one {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (heavyPrimX y) (𝓝[<] 1) (𝓝 (-hlPrimZero y)) :=
  ((tendsto_hlPrim_zero hy).comp (tendsto_omega_one hy.1)).neg

theorem heavy_integrand_nonneg {y x : ℝ} (hx : x < 1) :
    0 ≤ (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x))) :=
  mul_nonneg (by linarith)
    (piHat_nonneg (mul_nonneg (sq_nonneg y) (div_nonneg (sq_nonneg x) (by linarith))))

theorem intervalIntegrable_and_integral_heavy {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x)))) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x))) =
        hlPrimOne y - hlPrimZero y := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (fun x hx => hasDerivAt_heavyPrimX hy hx)
    (fun x hx => heavy_integrand_nonneg hx.2) (tendsto_heavyPrimX_zero hy)
    (tendsto_heavyPrimX_one hy)
  exact ⟨h.1, by rw [h.2]; ring⟩

/-! ### The dilogarithm identities -/

/-- **The endpoint difference is the closed form.** -/
theorem hlPrimOne_sub_hlPrimZero {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    hlPrimOne y - hlPrimZero y = a2Heavy y := by
  obtain ⟨hy0, hy1⟩ := hy
  have hyp : 0 < 1 + y := by linarith
  have hym : 0 < 1 - y := by linarith
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have l1 : log (1 - y ^ 2) = log (1 - y) + log (1 + y) := by
    rw [show 1 - y ^ 2 = (1 - y) * (1 + y) by ring, log_mul hym.ne' hyp.ne']
  have l2 : log ((1 - y) / (1 + y)) = log (1 - y) - log (1 + y) := log_div hym.ne' hyp.ne'
  -- reflection at `y` and at `y²`
  have hR1 := Li₂_add_Li₂_one_sub hy0.le hy1.le
  have hR2 := Li₂_add_Li₂_one_sub (x := y ^ 2) (by positivity) (by nlinarith)
  rw [log_pow, l1] at hR2
  push_cast at hR2
  -- reflection at `1/(1+y)`
  have hx1 : 1 / 2 ≤ 1 / (1 + y) := by rw [div_le_div_iff₀ (by norm_num) hyp]; linarith
  have hx2 : 1 / (1 + y) ≤ 1 := by rw [div_le_one hyp]; linarith
  have e1 : 1 - 1 / (1 + y) = y / (1 + y) := by field_simp; ring
  have e2 : 1 - (1 / (1 + y))⁻¹ = -y := by field_simp; ring
  have ll : log (1 / (1 + y)) = -log (1 + y) := by rw [one_div, log_inv]
  have ll2 : log (y / (1 + y)) = log y - log (1 + y) := log_div hy0.ne' hyp.ne'
  have hR3 := Li₂_add_Li₂_one_sub (x := 1 / (1 + y)) (by positivity) hx2
  rw [e1, ll, ll2] at hR3
  -- Landen at `1/(1+y)`
  have hLa := Li₂_one_sub_inv_add_Li₂_one_sub hx1 hx2
  rw [e2, e1, ll] at hLa
  -- `Li₂(y) + Li₂(-y) = Li₂(y²)/2`
  have hS := Li₂_add_Li₂_neg (x := y) (by rw [abs_of_pos hy0]; exact hy1.le)
  unfold hlPrimOne hlPrimZero a2Heavy
  rw [l1, l2]
  linear_combination (norm := skip) (-y ^ 3 + 5 * y + 4) / (2 * y ^ 4) * hR1 - 2 / y ^ 4 * hR2 +
    (5 - y ^ 2) / (2 * y ^ 3) * hR3 + (y ^ 2 - 5) / y ^ 3 * hLa - 2 / y ^ 4 * hS
  field_simp
  ring

/-! ### The main result -/

/-- The heavy-lepton integrand `(1-x) Π̂(y² x²/(1-x))` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_heavy {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x)))) volume 0 1 :=
  (intervalIntegrable_and_integral_heavy hy).1

/-- **O3-M3 (helper level).** For `0 < y < 1`,
`∫₀¹ (1-x) Π̂(y² x²/(1-x)) dx = a2Heavy y`, the closed form of Passera (10) at `x = 1/y`. -/
theorem integral_heavy {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x))) = a2Heavy y := by
  rw [(intervalIntegrable_and_integral_heavy hy).2, hlPrimOne_sub_hlPrimZero hy]

theorem heavyIntegral_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : heavyIntegral y = a2Heavy y :=
  integral_heavy hy

/-! ### Bounds and monotonicity -/

theorem heavy_integrand_nonneg' {y x : ℝ} (hx : x ≤ 1) :
    0 ≤ (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x))) :=
  mul_nonneg (by linarith)
    (piHat_nonneg (mul_nonneg (sq_nonneg y) (div_nonneg (sq_nonneg x) (by linarith))))

theorem continuousOn_piHat_integrand {S : ℝ} (hS : 0 ≤ S) :
    ContinuousOn (fun t => t * (1 - t) * log (1 + t * (1 - t) * S)) (uIcc 0 1) := by
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.log (by fun_prop) fun t ht => ?_)
  rw [uIcc_of_le zero_le_one] at ht
  have : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
  have : 0 ≤ t * (1 - t) * S := mul_nonneg this hS
  linarith

/-- `Π̂` is monotone on `[0, ∞)`. -/
theorem piHat_mono {S S' : ℝ} (hS : 0 ≤ S) (h : S ≤ S') : piHat S ≤ piHat S' := by
  unfold piHat
  refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on zero_le_one
    (continuousOn_piHat_integrand hS).intervalIntegrable
    (continuousOn_piHat_integrand (hS.trans h)).intervalIntegrable fun t ht => ?_) zero_le_two
  have h0 : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
  refine mul_le_mul_of_nonneg_left (log_le_log (by nlinarith [mul_nonneg h0 hS]) ?_) h0
  nlinarith [mul_le_mul_of_nonneg_left h h0]

/-- `Π̂(S) ≤ S/15` for `S ≥ 0`. -/
theorem piHat_le {S : ℝ} (hS : 0 ≤ S) : piHat S ≤ S / 15 := by
  have hc : Continuous fun t : ℝ => t * (1 - t) * (t * (1 - t) * S) := by fun_prop
  have hint : ∫ t in (0 : ℝ)..1, t * (1 - t) * (t * (1 - t) * S) = S / 30 := by
    have h := fun t (_ : t ∈ uIcc (0 : ℝ) 1) =>
      ((hasDerivAt_poly12 0 0 0 (S / 3) (-S / 2) (S / 5) 0 0 0 0 0 0 0 t).congr_deriv
        (by ring : _ = t * (1 - t) * (t * (1 - t) * S)))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (hc.intervalIntegrable 0 1)]
    ring
  unfold piHat
  have hle : ∫ t in (0 : ℝ)..1, t * (1 - t) * log (1 + t * (1 - t) * S) ≤
      ∫ t in (0 : ℝ)..1, t * (1 - t) * (t * (1 - t) * S) := by
    refine intervalIntegral.integral_mono_on zero_le_one
      (continuousOn_piHat_integrand hS).intervalIntegrable
      (hc.intervalIntegrable 0 1)
      fun t ht => ?_
    have h0 : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
    refine mul_le_mul_of_nonneg_left ?_ h0
    have := log_le_sub_one_of_pos (by nlinarith [mul_nonneg h0 hS] : 0 < 1 + t * (1 - t) * S)
    linarith
  rw [hint] at hle
  linarith

/-- `A(y) ≥ 0`. -/
theorem heavyIntegral_nonneg (y : ℝ) : 0 ≤ heavyIntegral y :=
  intervalIntegral.integral_nonneg zero_le_one fun _ hx => heavy_integrand_nonneg' hx.2

/-- `A(y) ≤ y²/45` for `0 < y < 1`. -/
theorem heavyIntegral_le {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : heavyIntegral y ≤ y ^ 2 / 45 := by
  have hc : Continuous fun x : ℝ => y ^ 2 * x ^ 2 / 15 := by fun_prop
  have hint : ∫ x in (0 : ℝ)..1, y ^ 2 * x ^ 2 / 15 = y ^ 2 / 45 := by
    have h := fun x (_ : x ∈ uIcc (0 : ℝ) 1) =>
      ((hasDerivAt_poly12 0 0 0 (y ^ 2 / 45) 0 0 0 0 0 0 0 0 0 x).congr_deriv
        (by ring : _ = y ^ 2 * x ^ 2 / 15))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (hc.intervalIntegrable 0 1)]
    ring
  unfold heavyIntegral
  rw [← hint]
  refine intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_heavy hy)
    (hc.intervalIntegrable 0 1) fun x hx => ?_
  rcases hx.2.lt_or_eq with hx1 | rfl
  · have hs : 0 < 1 - x := by linarith
    have hS : 0 ≤ y ^ 2 * (x ^ 2 / (1 - x)) := by positivity
    calc (1 - x) * piHat (y ^ 2 * (x ^ 2 / (1 - x)))
        ≤ (1 - x) * (y ^ 2 * (x ^ 2 / (1 - x)) / 15) :=
          mul_le_mul_of_nonneg_left (piHat_le hS) hs.le
      _ = y ^ 2 * x ^ 2 / 15 := by field_simp
  · simp only [sub_self, zero_mul]
    positivity

/-- **The limit `y → 0⁺`.** `A(y) → 0`. -/
theorem tendsto_heavyIntegral_zero : Tendsto heavyIntegral (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => y ^ 2 / 45) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => y ^ 2 / 45) (𝓝 0) (𝓝 (0 ^ 2 / 45)) :=
      ((continuous_pow 2).div_const 45).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall heavyIntegral_nonneg) ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
  exact heavyIntegral_le hy

/-- **Monotonicity.** `A` is monotone on `(0,1)`. -/
theorem heavyIntegral_mono {y₁ y₂ : ℝ} (h1 : 0 < y₁) (h12 : y₁ ≤ y₂) (h2 : y₂ < 1) :
    heavyIntegral y₁ ≤ heavyIntegral y₂ := by
  refine intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_heavy ⟨h1, by linarith⟩)
    (intervalIntegrable_heavy ⟨by linarith, h2⟩) fun x hx => ?_
  have hs : 0 ≤ 1 - x := by linarith [hx.2]
  have hq : 0 ≤ x ^ 2 / (1 - x) := div_nonneg (sq_nonneg x) hs
  refine mul_le_mul_of_nonneg_left (piHat_mono (mul_nonneg (sq_nonneg y₁) hq) ?_) hs
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h1.le h12 2) hq

/-- `a2Heavy` is monotone on `(0,1)`. -/
theorem a2Heavy_mono {y₁ y₂ : ℝ} (h1 : 0 < y₁) (h12 : y₁ ≤ y₂) (h2 : y₂ < 1) :
    a2Heavy y₁ ≤ a2Heavy y₂ := by
  rw [← heavyIntegral_eq ⟨h1, by linarith⟩, ← heavyIntegral_eq ⟨by linarith, h2⟩]
  exact heavyIntegral_mono h1 h12 h2

/-! ### The limit `y → 1⁻`: the electron value -/

/-- **The limit `y → 1⁻`.** `a2Heavy y → 119/36 - π²/3`, the one-bubble electron value. -/
theorem tendsto_a2Heavy_one : Tendsto a2Heavy (𝓝[<] 1) (𝓝 (119 / 36 - π ^ 2 / 3)) := by
  have hl : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have hy : Tendsto (fun y : ℝ => y) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left hl
  have hL : Tendsto (fun y => log y) (𝓝[<] 1) (𝓝 (log 1)) :=
    (continuousAt_log one_ne_zero).tendsto.mono_left hl
  rw [log_one] at hL
  have hL2 : Tendsto (fun y => log y * log (1 + y)) (𝓝[<] 1) (𝓝 (0 * log (1 + 1))) :=
    hL.mul ((ContinuousAt.log (by fun_prop) (by norm_num)).tendsto.mono_left hl)
  have hLm : Tendsto (fun y : ℝ => Li₂ (-y)) (𝓝[<] 1) (𝓝 (Li₂ (-1))) := by
    refine tendsto_Li₂_comp_of_continuousAt hl (by fun_prop) ⟨by norm_num, by norm_num⟩ ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with y hy
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hL22 := tendsto_Li₂_one_left.comp tendsto_sq_nhdsLT_one
  have hc : ∀ c : ℝ, Tendsto (fun _ : ℝ => c) (𝓝[<] 1) (𝓝 c) := fun c => tendsto_const_nhds
  have hC : Tendsto (fun y => (4 - 3 * log y) / y ^ 2) (𝓝[<] 1) (𝓝 ((4 - 3 * 0) / 1 ^ 2)) :=
    ((hc 4).sub (hL.const_mul 3)).div (hy.pow 2) (by norm_num)
  have hD : Tendsto (fun y => (y ^ 2 - 5) / (2 * y ^ 3) *
      (log y * log (1 - y) - log y * log (1 + y) + Li₂ y - Li₂ (-y))) (𝓝[<] 1)
      (𝓝 ((1 ^ 2 - 5) / (2 * 1 ^ 3) * (0 - 0 * log (1 + 1) + π ^ 2 / 6 - Li₂ (-1)))) :=
    (((hy.pow 2).sub (hc 5)).div ((hy.pow 3).const_mul 2) (by norm_num)).mul
      (((tendsto_log_mul_log_one_sub_one.sub hL2).add tendsto_Li₂_one_left).sub hLm)
  have hE : Tendsto (fun y => (2 * (log y * log (1 - y) + log y * log (1 + y)) + Li₂ (y ^ 2)) /
      y ^ 4) (𝓝[<] 1) (𝓝 ((2 * (0 + 0 * log (1 + 1)) + π ^ 2 / 6) / 1 ^ 4)) :=
    (((tendsto_log_mul_log_one_sub_one.add hL2).const_mul 2).add hL22).div (hy.pow 4)
      (by norm_num)
  have h := ((((hc (-25 / 36)).add (hL.div_const 3)).add hC).add hD).add hE
  have h2 : Tendsto a2Heavy (𝓝[<] 1) _ := h.congr' (by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with y hy
    have hyp : 0 < 1 + y := by linarith [hy.1]
    have hym : 0 < 1 - y := by linarith [hy.2]
    simp only [a2Heavy]
    rw [show 1 - y ^ 2 = (1 - y) * (1 + y) by ring, log_mul hym.ne' hyp.ne',
      log_div hym.ne' hyp.ne']
    ring)
  convert h2 using 2
  rw [Li₂_neg_one]
  ring

/-- `A(1)` is the electron one-bubble integral `∫₀¹ (1-x) Π̂(x²/(1-x)) dx = 119/36 - π²/3`. -/
theorem heavyIntegral_one : heavyIntegral 1 = 119 / 36 - π ^ 2 / 3 := by
  unfold heavyIntegral
  simp only [one_pow, one_mul]
  exact integral_oneBubble

/-- **Continuity at `y = 1`.** `A(y) → A(1) = 119/36 - π²/3` as `y → 1⁻`. -/
theorem tendsto_heavyIntegral_one : Tendsto heavyIntegral (𝓝[<] 1) (𝓝 (heavyIntegral 1)) := by
  rw [heavyIntegral_one]
  refine tendsto_a2Heavy_one.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with y hy
  exact (heavyIntegral_eq hy).symm

end QED.Chain.HeavyLepton
