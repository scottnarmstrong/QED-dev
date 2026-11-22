/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4P1Red
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Set (e), master I₄: the photon parameter `y₄` of the `F`-part

In the gauge of I₂ (`QED.ThreeLoopE.SetEMastersI4P1Red`) the parameter `y₄` (the photon line
`D₇`, from A to E) enters both Symanzik polynomials linearly. With the lines
`A = y₇ + α₁ α₂`, `B = y₈ + α₂ α₃` of I₂, `C₀ = α₁ α₃` and

  `K = A + B`, `Q = A B + C₀ K`, `S = α₁ + α₂ + y₈`,

one has `U = K y₄ + Q` and `F = (S K - Q) y₄ + S Q` (`QED.ThreeLoopE.i4P1FY4_U`,
`QED.ThreeLoopE.i4P1FY4_F`), with `0 < Q < S K` on the domain. This is the form
`F = m (S U₁ - U₂) + S U₂` of `F` along the line `D₇` parallel to the external momentum, with
`S` the sum of the electron parameters. Hence the `y₄`-integral of `log (F / U) / U²` is
elementary: with `α = S K - Q`, `N = α y + S Q`, `D = K y + Q`, so that `N K = α D + Q²`,

  `P(y) = -(log N - log D) (1 / (K D) + α / (K Q²)) + 1 / (K D)`

has derivative `log (N / D) / D²`, and

  `∫_{y > 0} log (N / D) / D² dy = (S log S - (α / K) log (α / K)) / Q² - 1 / (K Q)`
  (`QED.ThreeLoopE.i4P1FY4_integral`).

## Main definitions

* `QED.ThreeLoopE.i4P1FY4Val`: the value of the `y₄`-integral.

## Main results

* `QED.ThreeLoopE.i4P1FY4_U`, `QED.ThreeLoopE.i4P1FY4_F`, `QED.ThreeLoopE.i4P1FY4_pos`.
* `QED.ThreeLoopE.i4P1FY4_integral`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- `K = A + B`. -/
def i4P1FY4K (x w y₇ y₈ : ℝ) : ℝ := i2LineA x w y₇ + i2LineB x w y₈

/-- `Q = A B + α₁ α₃ (A + B)`. -/
def i4P1FY4Q (x w y₇ y₈ : ℝ) : ℝ :=
  i2LineA x w y₇ * i2LineB x w y₈ + (1 - w) ^ 2 * x * (1 - x) * i4P1FY4K x w y₇ y₈

/-- `S = α₁ + α₂ + y₈`, the sum of the electron parameters. -/
def i4P1FY4S (x w y₈ : ℝ) : ℝ := (1 - w) * x + w + y₈

theorem i4P1FY4_U (x w y₄ y₇ y₈ : ℝ) :
    i2U x w y₄ y₇ y₈ = i4P1FY4K x w y₇ y₈ * y₄ + i4P1FY4Q x w y₇ y₈ := by
  unfold i2U i4P1FY4Q i4P1FY4K i2LineC
  ring

theorem i4P1FY4_F (x w y₄ y₇ y₈ : ℝ) :
    i4CWF x w y₄ y₇ y₈ = (i4P1FY4S x w y₈ * i4P1FY4K x w y₇ y₈ - i4P1FY4Q x w y₇ y₈) * y₄ +
      i4P1FY4S x w y₈ * i4P1FY4Q x w y₇ y₈ := by
  unfold i4CWF i4F i4P1FY4S i4P1FY4Q i4P1FY4K i2LineA i2LineB
  ring

/-- On the domain, `K > 0`, `Q > 0` and `S K > Q`. -/
theorem i4P1FY4_pos {x w y₇ y₈ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
    (h₇ : 0 < y₇) (h₈ : 0 < y₈) :
    0 < i4P1FY4K x w y₇ y₈ ∧ 0 < i4P1FY4Q x w y₇ y₈ ∧
      i4P1FY4Q x w y₇ y₈ < i4P1FY4S x w y₈ * i4P1FY4K x w y₇ y₈ := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hw0, hw1⟩ := hw
  have h1x : 0 < 1 - x := by linarith
  have h1w : 0 < 1 - w := by linarith
  have hA : 0 < i2LineA x w y₇ := by unfold i2LineA; positivity
  have hB : 0 < i2LineB x w y₈ := by unfold i2LineB; positivity
  have hK : 0 < i4P1FY4K x w y₇ y₈ := by unfold i4P1FY4K; positivity
  refine ⟨hK, by unfold i4P1FY4Q; positivity, ?_⟩
  -- `S K - Q = K (S - C₀ - B) + B²` with `S - C₀ - B = (w + (1 - w) x)(1 - (1 - w)(1 - x))`.
  have e : i4P1FY4S x w y₈ * i4P1FY4K x w y₇ y₈ - i4P1FY4Q x w y₇ y₈ =
      i4P1FY4K x w y₇ y₈ * ((w + (1 - w) * x) * (1 - (1 - w) * (1 - x))) +
        i2LineB x w y₈ ^ 2 := by
    unfold i4P1FY4S i4P1FY4Q i4P1FY4K i2LineA i2LineB
    ring
  have h3 : 0 < 1 - (1 - w) * (1 - x) := by nlinarith
  have : 0 < i4P1FY4K x w y₇ y₈ * ((w + (1 - w) * x) * (1 - (1 - w) * (1 - x))) +
      i2LineB x w y₈ ^ 2 := by positivity
  linarith

/-- The value of the `y₄`-integral of `log (F / U) / U²`. -/
noncomputable def i4P1FY4Val (S K Q : ℝ) : ℝ :=
  (S * log S - (S - Q / K) * log (S - Q / K)) / Q ^ 2 - 1 / (K * Q)

private noncomputable def i4P1FY4Prim (S K Q y : ℝ) : ℝ :=
  -(log ((S * K - Q) * y + S * Q) - log (K * y + Q)) *
      (1 / (K * (K * y + Q)) + (S * K - Q) / (K * Q ^ 2)) + 1 / (K * (K * y + Q))

private theorem hasDerivAt_i4P1FY4Prim {S K Q y : ℝ} (hK : 0 < K) (hQ : 0 < Q)
    (hα : Q < S * K) (hy : 0 ≤ y) :
    HasDerivAt (i4P1FY4Prim S K Q)
      (log (((S * K - Q) * y + S * Q) / (K * y + Q)) / (K * y + Q) ^ 2) y := by
  have hS : 0 < S := by
    by_contra h; push Not at h; nlinarith
  have hα' : 0 < S * K - Q := by linarith
  have hN : 0 < (S * K - Q) * y + S * Q := by positivity
  have hD : 0 < K * y + Q := by positivity
  have hN' : HasDerivAt (fun y => (S * K - Q) * y + S * Q) (S * K - Q) y := by
    simpa using ((hasDerivAt_id y).const_mul (S * K - Q)).add_const (S * Q)
  have hD' : HasDerivAt (fun y => K * y + Q) K y := by
    simpa using ((hasDerivAt_id y).const_mul K).add_const Q
  have hL := ((hN'.log hN.ne').sub (hD'.log hD.ne'))
  have hI := (hD'.const_mul K).inv (by positivity)
  have h := ((hL.neg).mul ((hI.add_const ((S * K - Q) / (K * Q ^ 2))))).add hI
  unfold i4P1FY4Prim
  convert h using 1
  · funext y; simp [one_div]
  · simp only [Pi.neg_apply, Pi.sub_apply, Pi.inv_apply]
    rw [log_div hN.ne' hD.ne']
    field_simp
    ring

private theorem tendsto_i4P1FY4Prim {S K Q : ℝ} (hK : 0 < K) (hQ : 0 < Q) (hα : Q < S * K) :
    Tendsto (i4P1FY4Prim S K Q) atTop
      (𝓝 (-log ((S * K - Q) / K) * ((S * K - Q) / (K * Q ^ 2)))) := by
  have hα' : 0 < S * K - Q := by linarith
  have hD : Tendsto (fun y : ℝ => K * y + Q) atTop atTop :=
    tendsto_atTop_add_const_right _ Q (tendsto_id.const_mul_atTop hK)
  have hinv : Tendsto (fun y : ℝ => 1 / (K * (K * y + Q))) atTop (𝓝 0) :=
    (hD.const_mul_atTop hK).inv_tendsto_atTop.congr fun y => by simp [one_div]
  have hinv1 : Tendsto (fun y : ℝ => 1 / (K * y + Q)) atTop (𝓝 0) :=
    hD.inv_tendsto_atTop.congr fun y => by simp [one_div]
  -- `N / D = α / K + (S Q - α Q / K) / D`
  have hratio : Tendsto (fun y : ℝ => ((S * K - Q) * y + S * Q) / (K * y + Q)) atTop
      (𝓝 ((S * K - Q) / K)) := by
    have h1 : Tendsto (fun y : ℝ => (S * K - Q) / K + (S * Q - (S * K - Q) * Q / K) *
        (1 / (K * y + Q))) atTop (𝓝 ((S * K - Q) / K + (S * Q - (S * K - Q) * Q / K) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hinv1)
    rw [mul_zero, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with y hy
    have : 0 < K * y + Q := by positivity
    field_simp
    ring
  have hlog := (continuousAt_log (by positivity : (S * K - Q) / K ≠ 0)).tendsto.comp hratio
  have hL : Tendsto (fun y : ℝ => log ((S * K - Q) * y + S * Q) - log (K * y + Q)) atTop
      (𝓝 (log ((S * K - Q) / K))) := by
    refine hlog.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with y hy
    have hS : 0 < S := by
      by_contra h; push Not at h; nlinarith
    rw [Function.comp_apply, log_div (by positivity) (by positivity)]
  have h := ((hL.neg).mul (hinv.add (tendsto_const_nhds (x := (S * K - Q) / (K * Q ^ 2))))).add
    hinv
  simp only [zero_add, add_zero] at h
  exact h

/-- **The `y₄`-integral**: for `0 < Q < S K`,
`∫_{y > 0} log (((S K - Q) y + S Q) / (K y + Q)) / (K y + Q)²
  = (S log S - (S - Q / K) log (S - Q / K)) / Q² - 1 / (K Q)`, with the integrand integrable. -/
theorem i4P1FY4_integral {S K Q : ℝ} (hK : 0 < K) (hQ : 0 < Q) (hα : Q < S * K) :
    IntegrableOn (fun y => log (((S * K - Q) * y + S * Q) / (K * y + Q)) / (K * y + Q) ^ 2)
        (Ioi 0) ∧
      ∫ y in Ioi 0, log (((S * K - Q) * y + S * Q) / (K * y + Q)) / (K * y + Q) ^ 2 =
        i4P1FY4Val S K Q := by
  have hS : 0 < S := by
    by_contra h; push Not at h; nlinarith
  have hα' : 0 < S * K - Q := by linarith
  -- domination by `M / (K y + Q)²`
  set M : ℝ := |log S| + |log ((S * K - Q) / K)|
  have hint2 : IntegrableOn (fun y : ℝ => 1 / (K * y + Q) ^ 2) (Ioi 0) := by
    refine integrableOn_Ioi_deriv_of_nonneg (g := fun y => -(1 / (K * (K * y + Q))))
      (l := 0) ?_ (fun y hy => ?_) (fun y _ => by positivity) ?_
    · exact (by fun_prop : Continuous fun y : ℝ => K * y + Q).continuousAt.continuousWithinAt
        |>.const_mul K |>.inv₀ (by positivity) |>.const_mul 1 |>.neg
    · have hy' : 0 < K * y + Q := by have : (0 : ℝ) < y := hy; positivity
      have hD' : HasDerivAt (fun y => K * (K * y + Q)) (K * K) y := by
        simpa using (((hasDerivAt_id y).const_mul K).add_const Q).const_mul K
      convert ((hD'.inv (by positivity)).const_mul 1).neg using 1
      · funext y; simp [one_div]
      · field_simp
    · have hD : Tendsto (fun y : ℝ => K * y + Q) atTop atTop :=
        tendsto_atTop_add_const_right _ Q (tendsto_id.const_mul_atTop hK)
      simpa [one_div] using ((hD.const_mul_atTop hK).inv_tendsto_atTop).neg
  have hint : IntegrableOn (fun y => log (((S * K - Q) * y + S * Q) / (K * y + Q)) /
      (K * y + Q) ^ 2) (Ioi 0) := by
    refine Integrable.mono' (hint2.const_mul M) ?_ (ae_restrict_of_forall_mem measurableSet_Ioi
      fun y hy => ?_)
    · exact (by fun_prop : Measurable fun y : ℝ =>
        log (((S * K - Q) * y + S * Q) / (K * y + Q)) / (K * y + Q) ^ 2).aestronglyMeasurable
    · have hy0 : (0 : ℝ) < y := hy
      have hD : 0 < K * y + Q := by positivity
      have hN : 0 < (S * K - Q) * y + S * Q := by positivity
      -- `α / K ≤ N / D ≤ S`
      have hlo : (S * K - Q) / K ≤ ((S * K - Q) * y + S * Q) / (K * y + Q) := by
        rw [div_le_div_iff₀ hK hD]; nlinarith
      have hhi : ((S * K - Q) * y + S * Q) / (K * y + Q) ≤ S := by
        rw [div_le_iff₀ hD]; nlinarith
      have hlog : |log (((S * K - Q) * y + S * Q) / (K * y + Q))| ≤ M := by
        have h1 := log_le_log (by positivity) hlo
        have h2 := log_le_log (by positivity) hhi
        rw [abs_le]
        constructor <;> linarith [abs_nonneg (log S), le_abs_self (log S),
          neg_abs_le (log ((S * K - Q) / K)), abs_nonneg (log ((S * K - Q) / K))]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (K * y + Q) ^ 2),
        mul_one_div]
      exact div_le_div_of_nonneg_right hlog (by positivity)
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := i4P1FY4Prim S K Q) ?_
    (fun y hy => hasDerivAt_i4P1FY4Prim hK hQ hα (le_of_lt hy)) hint
    (tendsto_i4P1FY4Prim hK hQ hα)]
  · unfold i4P1FY4Prim i4P1FY4Val
    have e1 : S - Q / K = (S * K - Q) / K := by field_simp
    rw [e1]
    simp only [mul_zero, zero_add, mul_comm S Q, log_mul hQ.ne' hS.ne']
    field_simp
    ring
  · exact (hasDerivAt_i4P1FY4Prim hK hQ hα le_rfl).continuousAt.continuousWithinAt

end QED.ThreeLoopE

end
