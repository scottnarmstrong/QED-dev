/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.GammaTaylor
import Mathlib.Analysis.Analytic.Order

/-!
# Fourth-order jets of holomorphic functions at `0`

`QED.ThreeLoopD.i12HSJ f a₀ a₁ a₂ a₃ a₄`: near `0`,
`f(ε) = a₀ + a₁ ε + a₂ ε² + a₃ ε³ + a₄ ε⁴ + ε⁵ g(ε)` with `g` analytic at `0`. Jets add and
multiply (truncated Cauchy product), every function analytic at `0` has the jet of its Taylor
coefficients, and a jet determines the iterated derivatives at `0` through order `4`
(`QED.ThreeLoopD.i12HSJ.iteratedDeriv_three`, `QED.ThreeLoopD.i12HSJ.iteratedDeriv_four`).
For the `Γ`-ratios with `γ`-free exponent `ε² X(ε)`, `exp (ε² X)` has the jet
`(1, 0, X₀, X₁, X₂ + X₀²/2)` (`QED.ThreeLoopD.i12HSJ_exp_sq`).

## Main results

* `QED.ThreeLoopD.i12HSJ.mul`, `QED.ThreeLoopD.i12HSJ.sub`, `QED.ThreeLoopD.i12HSJ.const_mul`.
* `QED.ThreeLoopD.i12HSJ_of_analyticAt`.
* `QED.ThreeLoopD.i12HSJ.iteratedDeriv_three`, `QED.ThreeLoopD.i12HSJ.iteratedDeriv_four`.
* `QED.ThreeLoopD.i12HSJ_exp_sq`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.ThreeLoopD

/-- `f` has the jet `(a₀, …, a₄)` at `0`: `f = a₀ + a₁ ε + ⋯ + a₄ ε⁴ + ε⁵ g` near `0`, `g`
analytic at `0`. -/
def i12HSJ (f : ℂ → ℂ) (a0 a1 a2 a3 a4 : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
    f =ᶠ[𝓝 0] fun ε => a0 + a1 * ε + a2 * ε ^ 2 + a3 * ε ^ 3 + a4 * ε ^ 4 + ε ^ 5 * g ε

namespace i12HSJ

variable {f g : ℂ → ℂ} {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℂ}

theorem congr (h : i12HSJ f a0 a1 a2 a3 a4) {c0 c1 c2 c3 c4 : ℂ} (e0 : a0 = c0)
    (e1 : a1 = c1) (e2 : a2 = c2) (e3 : a3 = c3) (e4 : a4 = c4) : i12HSJ f c0 c1 c2 c3 c4 := by
  subst e0 e1 e2 e3 e4; exact h

theorem congr_fun (h : i12HSJ f a0 a1 a2 a3 a4) (hfg : f =ᶠ[𝓝 0] g) :
    i12HSJ g a0 a1 a2 a3 a4 := by
  obtain ⟨G, hG, hf⟩ := h
  exact ⟨G, hG, hfg.symm.trans hf⟩

theorem mul (hf : i12HSJ f a0 a1 a2 a3 a4) (hg : i12HSJ g b0 b1 b2 b3 b4) :
    i12HSJ (fun ε => f ε * g ε) (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1 + a2 * b0)
      (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
      (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  refine ⟨fun ε => (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) +
      (a2 * b4 + a3 * b3 + a4 * b2) * ε + (a3 * b4 + a4 * b3) * ε ^ 2 + a4 * b4 * ε ^ 3 +
      F ε * (b0 + b1 * ε + b2 * ε ^ 2 + b3 * ε ^ 3 + b4 * ε ^ 4) +
      (a0 + a1 * ε + a2 * ε ^ 2 + a3 * ε ^ 3 + a4 * ε ^ 4) * G ε + ε ^ 5 * F ε * G ε,
    by fun_prop, ?_⟩
  filter_upwards [hf, hg] with ε h1 h2
  rw [h1, h2]
  ring

theorem add (hf : i12HSJ f a0 a1 a2 a3 a4) (hg : i12HSJ g b0 b1 b2 b3 b4) :
    i12HSJ (fun ε => f ε + g ε) (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  refine ⟨fun ε => F ε + G ε, by fun_prop, ?_⟩
  filter_upwards [hf, hg] with ε h1 h2
  rw [h1, h2]
  ring

theorem sub (hf : i12HSJ f a0 a1 a2 a3 a4) (hg : i12HSJ g b0 b1 b2 b3 b4) :
    i12HSJ (fun ε => f ε - g ε) (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3) (a4 - b4) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  refine ⟨fun ε => F ε - G ε, by fun_prop, ?_⟩
  filter_upwards [hf, hg] with ε h1 h2
  rw [h1, h2]
  ring

theorem const_mul (hf : i12HSJ f a0 a1 a2 a3 a4) (c : ℂ) :
    i12HSJ (fun ε => c * f ε) (c * a0) (c * a1) (c * a2) (c * a3) (c * a4) := by
  obtain ⟨F, hF, hf⟩ := hf
  refine ⟨fun ε => c * F ε, by fun_prop, ?_⟩
  filter_upwards [hf] with ε h1
  rw [h1]
  ring

theorem analyticAt (hf : i12HSJ f a0 a1 a2 a3 a4) : AnalyticAt ℂ f 0 := by
  obtain ⟨F, hF, hf⟩ := hf
  have : AnalyticAt ℂ (fun ε => a0 + a1 * ε + a2 * ε ^ 2 + a3 * ε ^ 3 + a4 * ε ^ 4 +
      ε ^ 5 * F ε) 0 := by fun_prop
  exact this.congr hf.symm

theorem iteratedDeriv_poly {k : ℕ} (hk : k < 5) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    iteratedDeriv k (fun ε => a0 + a1 * ε + a2 * ε ^ 2 + a3 * ε ^ 3 + a4 * ε ^ 4 +
      ε ^ 5 * F ε) 0 =
      iteratedDeriv k (fun ε => a0 + a1 * ε ^ 1 + a2 * ε ^ 2 + a3 * ε ^ 3 + a4 * ε ^ 4) 0 := by
  have hF' : ContDiffAt ℂ k F 0 := hF.contDiffAt
  have e : (fun ε => a0 + a1 * ε + a2 * ε ^ 2 + a3 * ε ^ 3 + a4 * ε ^ 4 + ε ^ 5 * F ε) =
      fun ε => (a0 + a1 * ε ^ 1 + a2 * ε ^ 2 + a3 * ε ^ 3 + a4 * ε ^ 4) + ε ^ 5 * F ε := by
    funext ε; ring
  rw [e, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_mul (by fun_prop) hF']
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [iteratedDeriv_pow, zero_pow (show 5 - i ≠ 0 by omega),
    mul_zero, zero_mul]

theorem iteratedDeriv_three (hf : i12HSJ f a0 a1 a2 a3 a4) :
    iteratedDeriv 3 f 0 = 6 * a3 := by
  obtain ⟨F, hF, hf⟩ := hf
  rw [hf.iteratedDeriv_eq, iteratedDeriv_poly (by norm_num) hF]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero, iteratedDeriv_const]
  norm_num
  ring

theorem iteratedDeriv_four (hf : i12HSJ f a0 a1 a2 a3 a4) :
    iteratedDeriv 4 f 0 = 24 * a4 := by
  obtain ⟨F, hF, hf⟩ := hf
  rw [hf.iteratedDeriv_eq, iteratedDeriv_poly (by norm_num) hF]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero, iteratedDeriv_const]
  norm_num [Nat.factorial]
  ring

end i12HSJ

/-- **A function analytic at `0` has the jet of its Taylor coefficients.** -/
theorem i12HSJ_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    i12HSJ f (iteratedDeriv 0 f 0) (iteratedDeriv 1 f 0) (iteratedDeriv 2 f 0 / 2)
      (iteratedDeriv 3 f 0 / 6) (iteratedDeriv 4 f 0 / 24) := by
  obtain ⟨F, hF, hev⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 5
  refine ⟨F, hF, ?_⟩
  filter_upwards [hev] with ε h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_eq_mul, Nat.factorial]
  push_cast
  ring

/-- **The jet of `exp (ε² X(ε))`** for `X = X₀ + X₁ ε + X₂ ε² + ε³ Y`, `Y` analytic at `0`. -/
theorem i12HSJ_exp_sq {X Y : ℂ → ℂ} {X0 X1 X2 : ℂ} (hY : AnalyticAt ℂ Y 0)
    (hX : ∀ ε, X ε = X0 + X1 * ε + X2 * ε ^ 2 + ε ^ 3 * Y ε) :
    i12HSJ (fun ε => exp (ε ^ 2 * X ε)) 1 0 X0 X1 (X2 + X0 ^ 2 / 2) := by
  have hXe : X = fun ε => X0 + X1 * ε + X2 * ε ^ 2 + ε ^ 3 * Y ε := funext hX
  have hXa : AnalyticAt ℂ X 0 := by rw [hXe]; fun_prop
  have hE : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * X ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  refine ⟨fun ε => Y ε + (X1 + X2 * ε + ε ^ 2 * Y ε) * (X ε + X0) / 2 +
      ε * X ε ^ 3 * QED.DimReg.expRem3 (ε ^ 2 * X ε), by fun_prop, ?_⟩
  refine Eventually.of_forall fun ε => ?_
  simp only
  rw [QED.DimReg.exp_eq_expRem3]
  generalize QED.DimReg.expRem3 (ε ^ 2 * X ε) = E
  rw [hX ε]
  ring

end QED.ThreeLoopD
