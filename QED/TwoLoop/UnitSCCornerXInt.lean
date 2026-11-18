/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerXBranch
public import QED.TwoLoop.UnitSCCornerXEnds
public import QED.TwoLoop.UnitSCCornerXRat
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The corner unit C: the integration over `x` at `λ = 0`

Section 6.6.1 of `docs/TWO-LOOP-UNITS.md`: for `Y, ξ ∈ (0, 1)`, `ξ ≠ 1/2`,

`∫₀¹ G_C(Y ξ, Y (1 - ξ), x) dx = Φ_C(Y, ξ)` (`integral_cornerGm_zero`),

with `G_C = cornerGm 0 0` and `Φ_C = cornerPhi` (eq. (6.7)), and the integrand is integrable on
`(0, 1)`. On each branch of `β` an explicit antiderivative (`cornerF1` on `[0, x*]`, `cornerF2` on
`[x*, 1]`) has derivative the letter form of `QED.TwoLoop.UnitSCCorner.cornerGm_zero_branch1`,
`…_branch2` (`hasDerivAt_cornerF1`, `hasDerivAt_cornerF2`, each derivative identity checked by
`field_simp` and `ring`); the letter forms are continuous on the closed branches (the logarithms of
`x` and `1 - x` occur only as `x log x` and `(1 - x) log (1 - x)`), so the fundamental theorem of
calculus applies; the endpoint values combine to `Φ_C` (`cornerF_ends`, by the coefficient
identities
of `QED.TwoLoop.UnitSCCornerXEnds`). No dilogarithm arises.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The antiderivative on `[0, x*]`.** -/
noncomputable def cornerF1 (Y ξ x : ℝ) : ℝ :=
  cA1 Y ξ x + (x ^ 2 / 4 - x / 2) * log Y + x * cQ1x Y ξ x * (log ξ + log (1 - Y)) +
    cQ1x Y ξ x * (x * log x) + cC1 Y ξ x * log (Y + ξ * (1 - Y) * x)

/-- **The antiderivative on `[x*, 1]`.** -/
noncomputable def cornerF2 (Y ξ x : ℝ) : ℝ :=
  cA2 Y ξ x + (x ^ 2 / 2 - x) * log Y - (1 - x) / 4 * ((1 - x) * log (1 - x)) +
    x * cQ1x Y ξ x * (log ξ + log (1 - ξ)) + 2 * (x * cQ1x Y ξ x) * log x +
    cC2a Y ξ x * log (1 - ξ * x) + cC2b Y ξ x * log (1 - (1 - ξ) * x)

/-- **`Φ_C(Y, ξ)`** (eq. (6.7)). -/
noncomputable def cornerPhi (Y ξ : ℝ) : ℝ :=
  cφ1 Y ξ + cφY Y ξ * log Y + cφx Y ξ * log ξ + cφA Y ξ * log (1 - Y * ξ) +
    cφB Y ξ * log (ξ + Y - 2 * Y * ξ)

section Deriv

variable {Y ξ x : ℝ}

theorem hasDerivAt_mul_log' {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => x * log x) (log x + 1) x := by
  have h := (hasDerivAt_id' x).mul (hasDerivAt_log hx)
  convert h using 1
  field_simp

theorem hasDerivAt_one_sub_mul_log {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt (fun x => (1 - x) * log (1 - x)) (-log (1 - x) - 1) x := by
  have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hs : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  have h := hs.mul (hs.log h1)
  convert h using 1
  field_simp
  ring

theorem hasDerivAt_log_affine {a b x : ℝ} (h : a + b * x ≠ 0) :
    HasDerivAt (fun x => log (a + b * x)) (b / (a + b * x)) x := by
  have hs : HasDerivAt (fun x : ℝ => a + b * x) b x := by
    simpa using ((hasDerivAt_id' x).const_mul b).const_add a
  exact hs.log h

theorem hasDerivAt_cornerF1 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    HasDerivAt (cornerF1 Y ξ) (cornerG1 Y ξ x) x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hW : 0 < Y + ξ * (1 - Y) * x := by
    have : 0 < 1 - Y := by linarith
    positivity
  have hlW := hasDerivAt_log_affine (a := Y) (b := ξ * (1 - Y)) (x := x) hW.ne'
  have hB : HasDerivAt (fun x : ℝ => x ^ 2 / 4 - x / 2) (x / 2 - 1 / 2) x := by
    have := ((hasDerivAt_pow 2 x).div_const 4).sub ((hasDerivAt_id' x).div_const 2)
    convert this using 1
    push_cast
    ring
  have hQ : HasDerivAt (fun x => x * cQ1x Y ξ x) (cQ1x Y ξ x + x * cQ1xD Y ξ x) x := by
    have := (hasDerivAt_id' x).mul (hasDerivAt_cQ1x Y ξ x)
    convert this using 1
    ring
  have h := (((((hasDerivAt_cA1 Y ξ x).add (hB.mul_const (log Y))).add
    (hQ.mul_const (log ξ + log (1 - Y)))).add
    ((hasDerivAt_cQ1x Y ξ x).mul (hasDerivAt_mul_log' hx.ne'))).add
    ((hasDerivAt_cC1 Y ξ x).mul hlW))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · have d1 := cQ1x_deriv (Y := Y) (ξ := ξ) (x := x) hY0.ne'
    have d2 := cC1_deriv (Y := Y) (ξ := ξ) (x := x) hY0.ne'
    have d3 := cA1_deriv (Y := Y) (ξ := ξ) (x := x) hY0 hY1 hξ0 hx
    unfold cornerG1
    linear_combination (log x + (log ξ + log (1 - Y))) * d1 +
      log (Y + ξ * (1 - Y) * x) * d2 + d3
  · simp only [cornerF1, Pi.add_apply, Pi.mul_apply]

theorem hasDerivAt_cornerF2 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hξ2 : ξ ≠ 1 / 2) :
    HasDerivAt (cornerF2 Y ξ) (cornerG2 Y ξ x) x := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨hx0, hx1⟩ := hx
  have hA : 0 < 1 + -ξ * x := by nlinarith
  have hB : 0 < 1 + -(1 - ξ) * x := by nlinarith
  have hlA := hasDerivAt_log_affine (a := 1) (b := -ξ) (x := x) hA.ne'
  have hlB := hasDerivAt_log_affine (a := 1) (b := -(1 - ξ)) (x := x) hB.ne'
  have hB2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2 - x) (x - 1) x := by
    have := ((hasDerivAt_pow 2 x).div_const 2).sub (hasDerivAt_id' x)
    convert this using 1
    push_cast
    ring
  have hU : HasDerivAt (fun x : ℝ => (1 - x) / 4) (-(1 / 4)) x := by
    have := ((hasDerivAt_id' x).const_sub 1).div_const 4
    convert this using 1
    ring
  have hQ : HasDerivAt (fun x => x * cQ1x Y ξ x) (cQ1x Y ξ x + x * cQ1xD Y ξ x) x := by
    have := (hasDerivAt_id' x).mul (hasDerivAt_cQ1x Y ξ x)
    convert this using 1
    ring
  have h := ((((((hasDerivAt_cA2 Y ξ x).add (hB2.mul_const (log Y))).sub
    (hU.mul (hasDerivAt_one_sub_mul_log (x := x) hx1.ne))).add
    (hQ.mul_const (log ξ + log (1 - ξ)))).add
    ((hQ.const_mul 2).mul (hasDerivAt_log hx0.ne'))).add
    ((hasDerivAt_cC2a Y ξ x).mul hlA)).add ((hasDerivAt_cC2b Y ξ x).mul hlB)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · have d1 := cQ1x_deriv (Y := Y) (ξ := ξ) (x := x) hY0.ne'
    have d2 := cC2a_deriv (Y := Y) (ξ := ξ) (x := x) hY0.ne'
    have d3 := cC2b_deriv (Y := Y) (ξ := ξ) (x := x) hY0.ne'
    have d4 := cA2_deriv (Y := Y) (ξ := ξ) (x := x) hY0 hξ0 hξ1 hx0 hx1 hξ2
    have e1 : (1 : ℝ) + -ξ * x = 1 - ξ * x := by ring
    have e2 : (1 : ℝ) + -(1 - ξ) * x = 1 - (1 - ξ) * x := by ring
    rw [e1, e2]
    unfold cornerG2
    have hx0' := hx0.ne'
    have hA' : 1 - ξ * x ≠ 0 := by rw [← e1]; exact hA.ne'
    have hB' : 1 - (1 - ξ) * x ≠ 0 := by rw [← e2]; exact hB.ne'
    have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0'
    linear_combination (log ξ + log (1 - ξ) + 2 * log x) * d1 +
      log (1 - ξ * x) * d2 + log (1 - (1 - ξ) * x) * d3 + d4 + 2 * cQ1x Y ξ x * hxinv
  · simp only [cornerF2, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring_nf

end Deriv

/-! ### Continuity on the closed branches -/

section Cont

variable {Y ξ : ℝ}

theorem xStar_mem (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    xStar Y ξ ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 0 < 1 - Y * ξ := by nlinarith
  unfold xStar
  constructor
  · exact div_pos (by linarith) hA
  · rw [div_lt_one hA]; nlinarith

theorem continuous_cR1 (Y ξ : ℝ) : Continuous (cR1 Y ξ) := by
  unfold cR1
  fun_prop

theorem continuous_mul_log' : Continuous fun x : ℝ => x * log x := Real.continuous_mul_log

theorem continuous_one_sub_mul_log : Continuous fun x : ℝ => (1 - x) * log (1 - x) :=
  Real.continuous_mul_log.comp (continuous_const.sub continuous_id)

theorem continuousOn_log_affine {a b : ℝ} {s : Set ℝ} (h : ∀ x ∈ s, 0 < a + b * x) :
    ContinuousOn (fun x => log (a + b * x)) s :=
  (by fun_prop : Continuous fun x : ℝ => a + b * x).continuousOn.log fun x hx => (h x hx).ne'

theorem continuousOn_cornerG1 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (cornerG1 Y ξ) (Icc 0 (xStar Y ξ)) := by
  have hW : ∀ x ∈ Icc (0 : ℝ) (xStar Y ξ), 0 < Y + ξ * (1 - Y) * x := fun x hx => by
    have : 0 < 1 - Y := by linarith [hY.2]
    have := hY.1; have := hξ.1; have := hx.1
    positivity
  have hl := continuousOn_log_affine (a := Y) (b := ξ * (1 - Y)) hW
  unfold cornerG1
  have hK : Continuous (cKx Y ξ) := by unfold cKx; fun_prop
  exact ((((continuous_cR1 Y ξ).continuousOn.sub (by fun_prop)).sub (by fun_prop)).sub
    ((hK.mul continuous_mul_log').continuousOn)).add (((by fun_prop :
      Continuous fun x => x * cKx Y ξ x - (1 - x) / 2)).continuousOn.mul hl)

theorem continuousOn_cornerF1 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (cornerF1 Y ξ) (Icc 0 (xStar Y ξ)) := by
  have hW : ∀ x ∈ Icc (0 : ℝ) (xStar Y ξ), 0 < Y + ξ * (1 - Y) * x := fun x hx => by
    have : 0 < 1 - Y := by linarith [hY.2]
    have := hY.1; have := hξ.1; have := hx.1
    positivity
  have hl := continuousOn_log_affine (a := Y) (b := ξ * (1 - Y)) hW
  unfold cornerF1
  refine (((((by unfold cA1; exact continuous_px _ _ _ _ _ _ _ :
    Continuous (cA1 Y ξ)).add (by fun_prop)).add ?_).add ?_).continuousOn).add ?_
  · exact ((continuous_id.mul (by unfold cQ1x; exact continuous_px _ _ _ _ _ _ _)).mul
      continuous_const)
  · exact (by unfold cQ1x; exact continuous_px _ _ _ _ _ _ _ : Continuous (cQ1x Y ξ)).mul
      continuous_mul_log'
  · exact (by unfold cC1; exact continuous_px _ _ _ _ _ _ _ :
      Continuous (cC1 Y ξ)).continuousOn.mul hl

theorem continuousOn_cR2 (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (cR2 Y ξ) (Icc (xStar Y ξ) 1) := by
  have hN : Continuous (cR2N Y ξ) := by unfold cR2N; exact continuous_px _ _ _ _ _ _ _
  unfold cR2
  refine hN.continuousOn.div (by fun_prop) fun x hx => mul_ne_zero ?_ ?_
  · nlinarith [hx.2, hξ.1, hξ.2]
  · nlinarith [hx.2, hξ.1, hξ.2]

theorem continuousOn_cornerG2 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (cornerG2 Y ξ) (Icc (xStar Y ξ) 1) := by
  have h0 := (xStar_mem hY hξ).1
  have hA : ∀ x ∈ Icc (xStar Y ξ) 1, 0 < 1 + -ξ * x := fun x hx => by
    nlinarith [hx.2, hξ.2, hξ.1]
  have hB : ∀ x ∈ Icc (xStar Y ξ) 1, 0 < 1 + -(1 - ξ) * x := fun x hx => by
    nlinarith [hx.2, hξ.2, hξ.1]
  have hlA := continuousOn_log_affine hA
  have hlB := continuousOn_log_affine hB
  have hlx : ContinuousOn (fun x => log x) (Icc (xStar Y ξ) 1) :=
    continuousOn_log.mono fun x hx => (h0.trans_le hx.1).ne'
  have hK : Continuous (cKx Y ξ) := by unfold cKx; fun_prop
  have e : cornerG2 Y ξ = fun x => cR2 Y ξ x - (1 - x) * log Y +
      1 / 2 * ((1 - x) * log (1 - x)) +
      (x * cKx Y ξ x - (1 - x) / 2) * (log (1 + -ξ * x) + log (1 + -(1 - ξ) * x)) -
      x * cKx Y ξ x * (log ξ + log (1 - ξ) + 2 * log x) := by
    funext x
    unfold cornerG2
    ring_nf
  rw [e]
  exact (((((continuousOn_cR2 hξ).sub (by fun_prop)).add
    (continuous_one_sub_mul_log.const_smul (1 / 2 : ℝ)).continuousOn).add
    ((by fun_prop : Continuous fun x => x * cKx Y ξ x - (1 - x) / 2).continuousOn.mul
      (hlA.add hlB))).sub ((by fun_prop : Continuous fun x => x * cKx Y ξ x).continuousOn.mul
      ((continuousOn_const.add continuousOn_const).add (hlx.const_smul (2 : ℝ)))))

theorem continuousOn_cornerF2 (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (cornerF2 Y ξ) (Icc (xStar Y ξ) 1) := by
  have h0 := (xStar_mem hY hξ).1
  have hA : ∀ x ∈ Icc (xStar Y ξ) 1, 0 < 1 + -ξ * x := fun x hx => by
    nlinarith [hx.2, hξ.2, hξ.1]
  have hB : ∀ x ∈ Icc (xStar Y ξ) 1, 0 < 1 + -(1 - ξ) * x := fun x hx => by
    nlinarith [hx.2, hξ.2, hξ.1]
  have hlA := continuousOn_log_affine hA
  have hlB := continuousOn_log_affine hB
  have hlx : ContinuousOn (fun x => log x) (Icc (xStar Y ξ) 1) :=
    continuousOn_log.mono fun x hx => (h0.trans_le hx.1).ne'
  have cA : Continuous (cA2 Y ξ) := by unfold cA2; exact continuous_px _ _ _ _ _ _ _
  have cQ : Continuous (cQ1x Y ξ) := by unfold cQ1x; exact continuous_px _ _ _ _ _ _ _
  have ca : Continuous (cC2a Y ξ) := by unfold cC2a; exact continuous_px _ _ _ _ _ _ _
  have cb : Continuous (cC2b Y ξ) := by unfold cC2b; exact continuous_px _ _ _ _ _ _ _
  have e : cornerF2 Y ξ = fun x => cA2 Y ξ x + (x ^ 2 / 2 - x) * log Y -
      (1 - x) / 4 * ((1 - x) * log (1 - x)) + x * cQ1x Y ξ x * (log ξ + log (1 - ξ)) +
      2 * (x * cQ1x Y ξ x) * log x + cC2a Y ξ x * log (1 + -ξ * x) +
      cC2b Y ξ x * log (1 + -(1 - ξ) * x) := by
    funext x
    unfold cornerF2
    ring_nf
  rw [e]
  have hc1 : Continuous fun x => cA2 Y ξ x + (x ^ 2 / 2 - x) * log Y -
      (1 - x) / 4 * ((1 - x) * log (1 - x)) + x * cQ1x Y ξ x * (log ξ + log (1 - ξ)) :=
    ((cA.add (by fun_prop)).sub ((by fun_prop : Continuous fun x : ℝ => (1 - x) / 4).mul
      continuous_one_sub_mul_log)).add ((continuous_id.mul cQ).mul continuous_const)
  exact ((hc1.continuousOn.add ((continuous_const.mul (continuous_id.mul cQ)).continuousOn.mul
    hlx)).add (ca.continuousOn.mul hlA)).add (cb.continuousOn.mul hlB)

end Cont

/-! ### The endpoint values -/

section Ends

variable {Y ξ : ℝ}

theorem log_xStar (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    log (xStar Y ξ) = log (1 - Y) - log (1 - Y * ξ) := by
  have hA : 0 < 1 - Y * ξ := by nlinarith [hY.1, hY.2, hξ.1, hξ.2]
  unfold xStar
  rw [log_div (by linarith [hY.2]) hA.ne']

theorem log_W_xStar (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    log (Y + ξ * (1 - Y) * xStar Y ξ) = log (ξ + Y - 2 * Y * ξ) - log (1 - Y * ξ) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith
  have hA' : 1 - ξ * Y ≠ 0 := by nlinarith
  rw [← log_div hB.ne' hA.ne']
  congr 1
  unfold xStar
  field_simp
  ring

theorem log_one_sub_xStar (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    log (1 - xStar Y ξ) = log Y + log (1 - ξ) - log (1 - Y * ξ) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have h1 : 0 < 1 - ξ := by linarith
  have hA' : 1 - ξ * Y ≠ 0 := by nlinarith
  rw [← log_mul hY0.ne' h1.ne', ← log_div (by positivity) hA.ne']
  congr 1
  unfold xStar
  field_simp
  ring

theorem log_A_xStar (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    log (1 - ξ * xStar Y ξ) = log (1 - ξ) - log (1 - Y * ξ) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have h1 : 0 < 1 - ξ := by linarith
  have hA' : 1 - ξ * Y ≠ 0 := by nlinarith
  rw [← log_div h1.ne' hA.ne']
  congr 1
  unfold xStar
  field_simp
  ring

theorem log_B_xStar (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    log (1 - (1 - ξ) * xStar Y ξ) = log (ξ + Y - 2 * Y * ξ) - log (1 - Y * ξ) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith
  have hA' : 1 - ξ * Y ≠ 0 := by nlinarith
  rw [← log_div hB.ne' hA.ne']
  congr 1
  unfold xStar
  field_simp
  ring

/-- **The endpoint values combine to `Φ_C`.** -/
theorem cornerF_ends (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hξ2 : ξ ≠ 1 / 2) :
    cornerF1 Y ξ (xStar Y ξ) - cornerF1 Y ξ 0 + (cornerF2 Y ξ 1 - cornerF2 Y ξ (xStar Y ξ)) =
      cornerPhi Y ξ := by
  unfold cornerF1 cornerF2 cornerPhi
  rw [log_xStar hY hξ, log_W_xStar hY hξ, log_one_sub_xStar hY hξ, log_A_xStar hY hξ,
    log_B_xStar hY hξ]
  simp only [mul_zero, zero_mul, add_zero, mul_one, sub_sub_cancel, sub_self, log_one, log_zero]
  linear_combination (log Y) * cornerF_coeff_LY hY hξ hξ2 +
    (log ξ) * cornerF_coeff_Lxi hY hξ hξ2 +
    (log (1 - ξ)) * cornerF_coeff_L1xi hY hξ hξ2 +
    (log (1 - Y * ξ)) * cornerF_coeff_LA hY hξ hξ2 +
    (log (ξ + Y - 2 * Y * ξ)) * cornerF_coeff_LB hY hξ hξ2 +
    cornerF_coeff_1 hY hξ hξ2

end Ends

/-! ### The integral over `x` -/

/-- **The `x`-integration of section 6.6.1**: for `Y, ξ ∈ (0, 1)`, `ξ ≠ 1/2`, the corner integrand
at `λ = 0` is integrable on `(0, 1)` and `∫₀¹ G_C(Y ξ, Y (1 - ξ), x) dx = Φ_C(Y, ξ)`. -/
theorem integral_cornerGm_zero {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hξ2 : ξ ≠ 1 / 2) :
    IntegrableOn (fun x => cornerGm 0 0 (Y * ξ) (Y * (1 - ξ)) x) (Ioo 0 1) ∧
      ∫ x in Ioo (0 : ℝ) 1, cornerGm 0 0 (Y * ξ) (Y * (1 - ξ)) x = cornerPhi Y ξ := by
  obtain ⟨hs0, hs1⟩ := xStar_mem hY hξ
  set f := fun x => cornerGm 0 0 (Y * ξ) (Y * (1 - ξ)) x with hf
  have i1 : IntervalIntegrable (cornerG1 Y ξ) volume 0 (xStar Y ξ) :=
    (continuousOn_cornerG1 hY hξ).intervalIntegrable_of_Icc hs0.le
  have i2 : IntervalIntegrable (cornerG2 Y ξ) volume (xStar Y ξ) 1 :=
    (continuousOn_cornerG2 hY hξ).intervalIntegrable_of_Icc hs1.le
  have q1 : EqOn (cornerG1 Y ξ) f (uIoo 0 (xStar Y ξ)) := fun x hx => by
    rw [uIoo_of_le hs0.le] at hx
    exact (cornerGm_zero_branch1 hY hξ hx.1 hx.2.le).symm
  have q2 : EqOn (cornerG2 Y ξ) f (uIoo (xStar Y ξ) 1) := fun x hx => by
    rw [uIoo_of_le hs1.le] at hx
    exact (cornerGm_zero_branch2 hY hξ ⟨hs0.trans hx.1, hx.2⟩ hx.1.le).symm
  have j1 := i1.congr_uIoo q1
  have j2 := i2.congr_uIoo q2
  have j := j1.trans j2
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp j, ?_⟩
  have e1 : ∫ x in (0 : ℝ)..(xStar Y ξ), f x = cornerF1 Y ξ (xStar Y ξ) - cornerF1 Y ξ 0 := by
    rw [← intervalIntegral.integral_congr_uIoo q1]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs0.le
      (continuousOn_cornerF1 hY hξ) (fun x hx => hasDerivAt_cornerF1 hY hξ hx.1) i1
  have e2 : ∫ x in (xStar Y ξ)..1, f x = cornerF2 Y ξ 1 - cornerF2 Y ξ (xStar Y ξ) := by
    rw [← intervalIntegral.integral_congr_uIoo q2]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs1.le
      (continuousOn_cornerF2 hY hξ)
      (fun x hx => hasDerivAt_cornerF2 hY hξ ⟨hs0.trans hx.1, hx.2⟩ hξ2) i2
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals j1 j2, e1, e2]
  exact cornerF_ends hY hξ hξ2

end QED.TwoLoop.UnitSCCorner

end
