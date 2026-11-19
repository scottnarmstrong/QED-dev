/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInPhi
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G2: the boundary term integrated by parts in `x`

Helper level (no frozen statement). For `0 < y₃ < Y < 1` and `M > 0`, the boundary term of
`cornerGm_add_log_eq` integrates over `x` to (**`integral_cornInDel`**)

`∫₀¹ δ/(M + w₀) dx = -∫_{x*}^1 φ'(x) log(1 + w₀(x)/M) dx`.

It vanishes for `x < x*` (`cornInDel_of_branch1`); on `(x*, 1)` it is `φ w₀'/(M + w₀)`
(`cornInDel_of_branch2`) and `φ(x*) = φ(1) = 0`. The antiderivative `φ log(1 + w₀/M)` is written
as `(1-x) R(x) ℓ(x)` with `φ = (x-1)² R` and the continuous function
`ℓ = (1-x) log(M(1-x) + e x²) - (1-x) log(1-x) - (1-x) log M` (`cornInEll`,
`= (1-x) log(1 + w₀/M)` for `x < 1`), so it is continuous on `[x*, 1]`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `R` with `φ = (x-1)² R`. -/
noncomputable def cornInR (Y y3 x : ℝ) : ℝ :=
  (1 - Y - x * (1 - y3)) * hpoly (cornInPl Y y3) x / (4 * x ^ 2 * y3 * (y3 - Y) ^ 3 * (x - 2))

/-- `S` with `φ' = (x-1) S`. -/
noncomputable def cornInS (Y y3 x : ℝ) : ℝ :=
  hpoly (cornInNl Y y3) x / (2 * x ^ 3 * y3 * (y3 - Y) ^ 3 * (x - 2) ^ 2)

/-- `ℓ = (1-x) log(M(1-x) + e x²) - (1-x) log(1-x) - (1-x) log M`. -/
noncomputable def cornInEll (M Y y3 x : ℝ) : ℝ :=
  (1 - x) * log (M * (1 - x) + y3 * (Y - y3) * x ^ 2) - (1 - x) * log (1 - x) -
    (1 - x) * log M

theorem cornInXs_mem {Y y3 : ℝ} (_h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) :
    cornInXs Y y3 ∈ Ioo (0 : ℝ) 1 := by
  have h1 : 0 < 1 - y3 := by linarith
  unfold cornInXs
  exact ⟨div_pos (by linarith) h1, (div_lt_one h1).2 (by linarith)⟩

theorem cornIn_branch2_of_xs {Y y3 x : ℝ} (_h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hx : cornInXs Y y3 ≤ x) : 1 - Y ≤ x * (1 - y3) := by
  have h1 : 0 < 1 - y3 := by linarith
  unfold cornInXs at hx
  rwa [div_le_iff₀ h1] at hx

theorem cornIn_branch1_of_xs {Y y3 x : ℝ} (_h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hx : x ≤ cornInXs Y y3) : x * (1 - y3) ≤ 1 - Y := by
  have h1 : 0 < 1 - y3 := by linarith
  unfold cornInXs at hx
  rwa [le_div_iff₀ h1] at hx

theorem cornIn_den_pos {M Y y3 x : ℝ} (hM : 0 < M) (h3 : 0 < y3) (h34 : y3 < Y) (hx0 : 0 < x)
    (hx1 : x ≤ 1) : 0 < M * (1 - x) + y3 * (Y - y3) * x ^ 2 := by
  have : 0 < y3 * (Y - y3) * x ^ 2 := by
    have : 0 < Y - y3 := by linarith
    positivity
  nlinarith [mul_nonneg hM.le (by linarith : (0 : ℝ) ≤ 1 - x)]

theorem cornInEll_eq {M Y y3 x : ℝ} (hM : 0 < M) (h3 : 0 < y3) (h34 : y3 < Y) (hx0 : 0 < x)
    (hx1 : x < 1) :
    (1 - x) * log (1 + y3 * (Y - y3) * x ^ 2 / (1 - x) / M) = cornInEll M Y y3 x := by
  have h1 : 0 < 1 - x := by linarith
  have hD := cornIn_den_pos hM h3 h34 hx0 hx1.le
  have e : 1 + y3 * (Y - y3) * x ^ 2 / (1 - x) / M =
      (M * (1 - x) + y3 * (Y - y3) * x ^ 2) / ((1 - x) * M) := by
    field_simp
  rw [e, log_div hD.ne' (by positivity), log_mul h1.ne' hM.ne']
  unfold cornInEll
  ring

theorem continuousOn_cornInR {Y y3 a : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (ha : 0 < a) :
    ContinuousOn (cornInR Y y3) (Icc a 1) := by
  unfold cornInR
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
  have hx0 : 0 < x := ha.trans_le hx.1
  have : x - 2 ≠ 0 := by linarith [hx.2]
  have : y3 - Y ≠ 0 := by linarith
  have := h3.ne'
  positivity

theorem continuousOn_cornInS {Y y3 a : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (ha : 0 < a) :
    ContinuousOn (cornInS Y y3) (Icc a 1) := by
  unfold cornInS
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
  have hx0 : 0 < x := ha.trans_le hx.1
  have : x - 2 ≠ 0 := by linarith [hx.2]
  have : y3 - Y ≠ 0 := by linarith
  have := h3.ne'
  positivity

theorem continuousOn_cornInEll {M Y y3 a : ℝ} (hM : 0 < M) (h3 : 0 < y3) (h34 : y3 < Y)
    (ha : 0 < a) : ContinuousOn (cornInEll M Y y3) (Icc a 1) := by
  unfold cornInEll
  have hl : ContinuousOn (fun x => log (M * (1 - x) + y3 * (Y - y3) * x ^ 2)) (Icc a 1) :=
    ContinuousOn.log (by fun_prop) fun x hx =>
      (cornIn_den_pos hM h3 h34 (ha.trans_le hx.1) hx.2).ne'
  have hm : Continuous fun x : ℝ => (1 - x) * log (1 - x) :=
    continuous_mul_log.comp (continuous_const.sub continuous_id)
  exact ((continuousOn_const.sub continuousOn_id).mul hl).sub hm.continuousOn |>.sub
    (by fun_prop)

theorem cornInPhi_eq (Y y3 x : ℝ) : cornInPhi Y y3 x = (x - 1) ^ 2 * cornInR Y y3 x := by
  unfold cornInPhi cornInR
  ring

theorem cornInDPhi_eq (Y y3 x : ℝ) : cornInDPhi Y y3 x = (x - 1) * cornInS Y y3 x := by
  unfold cornInDPhi cornInS
  ring

/-- **The boundary term integrated by parts.** -/
theorem integral_cornInDel {M Y y3 : ℝ} (hM : 0 < M) (h3 : 0 < y3) (h34 : y3 < Y)
    (hY : Y < 1) :
    IntervalIntegrable (fun x => cornInDel Y y3 x / (M + cornInW0 Y y3 x)) volume 0 1 ∧
      IntervalIntegrable (fun x => cornInDPhi Y y3 x * log (1 + cornInW0 Y y3 x / M)) volume
        (cornInXs Y y3) 1 ∧
      ∫ x in (0 : ℝ)..1, cornInDel Y y3 x / (M + cornInW0 Y y3 x) =
        -∫ x in cornInXs Y y3..1, cornInDPhi Y y3 x * log (1 + cornInW0 Y y3 x / M) := by
  set xs := cornInXs Y y3 with hxsdef
  have hxs := cornInXs_mem h3 h34 hY
  set e := y3 * (Y - y3) with he
  have he0 : 0 < e := mul_pos h3 (by linarith)
  -- continuous versions on `[x*, 1]`
  set g1 : ℝ → ℝ := fun x => -(cornInS Y y3 x * cornInEll M Y y3 x) with hg1
  set g2 : ℝ → ℝ := fun x => cornInR Y y3 x * (e * x * (2 - x) * (1 - x)) /
    (M * (1 - x) + e * x ^ 2) with hg2
  set F : ℝ → ℝ := fun x => (1 - x) * cornInR Y y3 x * cornInEll M Y y3 x with hF
  have cR := continuousOn_cornInR h3 h34 hxs.1
  have cS := continuousOn_cornInS h3 h34 hxs.1
  have cL := continuousOn_cornInEll hM h3 h34 hxs.1
  have cg1 : ContinuousOn g1 (Icc xs 1) := (cS.mul cL).neg
  have cg2 : ContinuousOn g2 (Icc xs 1) := by
    refine ContinuousOn.div (cR.mul (by fun_prop)) (by fun_prop) fun x hx => ?_
    exact (cornIn_den_pos hM h3 h34 (hxs.1.trans_le hx.1) hx.2).ne'
  have cF : ContinuousOn F (Icc xs 1) := ((continuousOn_const.sub continuousOn_id).mul cR).mul cL
  -- agreement on `(x*, 1)`
  have hw0 : ∀ x ∈ Ioo xs 1, cornInW0 Y y3 x = e * x ^ 2 / (1 - x) := fun x hx =>
    cornInW0_of_branch2 h3 hx.2 (cornIn_branch2_of_xs h3 h34 hY hx.1.le)
  have eq1 : EqOn (fun x => cornInDPhi Y y3 x * log (1 + cornInW0 Y y3 x / M)) g1
      (uIoo xs 1) := by
    intro x hx
    rw [uIoo_of_le hxs.2.le] at hx
    have hx0 : 0 < x := hxs.1.trans hx.1
    simp only [hg1]
    rw [hw0 x hx, cornInDPhi_eq, ← cornInEll_eq hM h3 h34 hx0 hx.2]
    ring
  have eq2 : EqOn (fun x => cornInDel Y y3 x / (M + cornInW0 Y y3 x)) g2 (uIoo xs 1) := by
    intro x hx
    rw [uIoo_of_le hxs.2.le] at hx
    have hx0 : 0 < x := hxs.1.trans hx.1
    have h1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hD := cornIn_den_pos hM h3 h34 hx0 hx.2.le
    simp only [hg2]
    rw [hw0 x hx, cornInDel_of_branch2 h3 h34 ⟨hx0, hx.2⟩ (cornIn_branch2_of_xs h3 h34 hY hx.1.le),
      cornInPhi_eq]
    have : M + e * x ^ 2 / (1 - x) = (M * (1 - x) + e * x ^ 2) / (1 - x) := by field_simp
    rw [this]
    field_simp
    ring
  have i1 : IntervalIntegrable (fun x => cornInDPhi Y y3 x * log (1 + cornInW0 Y y3 x / M))
      volume xs 1 :=
    ((cg1.mono (by rw [uIcc_of_le hxs.2.le])).intervalIntegrable).congr_uIoo
      (fun x hx => (eq1 hx).symm)
  have i2 : IntervalIntegrable (fun x => cornInDel Y y3 x / (M + cornInW0 Y y3 x)) volume xs 1 :=
    ((cg2.mono (by rw [uIcc_of_le hxs.2.le])).intervalIntegrable).congr_uIoo
      (fun x hx => (eq2 hx).symm)
  -- the first branch contributes nothing
  have eq0 : EqOn (fun x => cornInDel Y y3 x / (M + cornInW0 Y y3 x)) (fun _ => 0)
      (uIoo 0 xs) := by
    intro x hx
    rw [uIoo_of_le hxs.1.le] at hx
    simp only
    rw [cornInDel_of_branch1 hY h3 hx.1
      (betaG_of_branch1 h3 (by linarith [hx.2, hxs.2])
        (cornIn_branch1_of_xs h3 h34 hY hx.2.le)), zero_div]
  have i0 : IntervalIntegrable (fun x => cornInDel Y y3 x / (M + cornInW0 Y y3 x)) volume 0 xs :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo (fun x hx => (eq0 hx).symm)
  refine ⟨i0.trans i2, i1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals i0 i2,
    intervalIntegral.integral_congr_uIoo eq0, intervalIntegral.integral_const, smul_zero,
    zero_add]
  -- the fundamental theorem of calculus for `F`
  have hderiv : ∀ x ∈ Ioo xs 1, HasDerivAt F
      (cornInDPhi Y y3 x * log (1 + cornInW0 Y y3 x / M) +
        cornInDel Y y3 x / (M + cornInW0 Y y3 x)) x := by
    intro x hx
    have hx0 : 0 < x := hxs.1.trans hx.1
    have h1 : 0 < 1 - x := by linarith [hx.2]
    have hx2 : x ≠ 2 := by linarith [hx.2]
    have hy : y3 - Y ≠ 0 := by linarith
    have hw : HasDerivAt (fun x => e * x ^ 2 / (1 - x)) (e * x * (2 - x) / (1 - x) ^ 2) x := by
      have := ((hasDerivAt_pow 2 x).const_mul e).div ((hasDerivAt_const x 1).sub
        (hasDerivAt_id' x)) h1.ne'
      refine this.congr_deriv ?_
      simp only [Pi.sub_apply]
      field_simp
      push_cast
      ring
    have hpos : 0 < 1 + e * x ^ 2 / (1 - x) / M := by positivity
    have hL : HasDerivAt (fun x => log (1 + e * x ^ 2 / (1 - x) / M))
        (e * x * (2 - x) / (1 - x) ^ 2 / M / (1 + e * x ^ 2 / (1 - x) / M)) x :=
      (((hw.div_const M).const_add 1).log hpos.ne')
    have hP := (hasDerivAt_cornInPhi hx0.ne' hx2 h3.ne' hy).mul hL
    have hev : (fun x => cornInPhi Y y3 x * log (1 + e * x ^ 2 / (1 - x) / M)) =ᶠ[𝓝 x] F := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
      have hz0 : 0 < z := hxs.1.trans hz.1
      simp only [hF]
      rw [← cornInEll_eq hM h3 h34 hz0 hz.2, cornInPhi_eq]
      ring
    refine (hP.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    rw [hw0 x hx, cornInDel_of_branch2 h3 h34 ⟨hx0, hx.2⟩
      (cornIn_branch2_of_xs h3 h34 hY hx.1.le)]
    have hD := cornIn_den_pos hM h3 h34 hx0 hx.2.le
    have : 1 + e * x ^ 2 / (1 - x) / M = (M * (1 - x) + e * x ^ 2) / ((1 - x) * M) := by
      field_simp
    rw [this]
    have : M + e * x ^ 2 / (1 - x) = (M * (1 - x) + e * x ^ 2) / (1 - x) := by field_simp
    rw [this]
    field_simp
    rw [he]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxs.2.le cF hderiv
    (i1.add i2)
  rw [intervalIntegral.integral_add i1 i2] at hFTC
  have hF1 : F 1 = 0 := by simp [hF]
  have hFxs : F xs = 0 := by
    have : cornInR Y y3 xs = 0 := by
      have h1 : 1 - y3 ≠ 0 := by linarith
      have : 1 - Y - xs * (1 - y3) = 0 := by
        rw [hxsdef]; unfold cornInXs; field_simp; ring
      simp [cornInR, this]
    simp [hF, this]
  rw [hF1, hFxs, sub_zero] at hFTC
  linarith

end QED.ChainProof.SetCK

end
