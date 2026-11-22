/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLBasic
public import QED.Polylog.Basic
import QED.Polylog.HPLCalculus
import QED.Polylog.HPLLowWeight
import QED.Polylog.ExtraIntegrals
import QED.Polylog.Reflection
import QED.Polylog.DilogPM
import QED.Polylog.LiN
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Set (d), master `I₁₅`: a mixed weight-three combination of harmonic polylogarithms

The inner integral `W₃` of `QED.ThreeLoopD.SetDMastersI15KValThreeW` contains the words
`H(1, 0, -1)`, `H(1, -1, 0)`, `H(-1, 1, 0)` (mixing the letters `1` and `-1`) only through

  `K = 2 H(1, 0, -1) - H(1, -1, 0) - H(-1, 1, 0)`,

which is classical:

  `K = -3/2 Li₃ (1 - r²) + 3 Li₃ (1 - r) + 3 Li₃ (1/(1 + r)) - 2 log (1 + r) Li₂ r`
    `- 2 log r log (1 - r) log (1 + r) - log³ (1 + r)/2 - π²/4 log (1 - r)`
    `+ 3π²/4 log (1 + r) - 9/2 ζ(3)`

(found by a numerical fit). The proof compares derivatives (weight two, by reflection,
duplication and `Li₂ (1/(1 + r))`) and the limits at `0⁺`.

## Main results

* `QED.ThreeLoopD.i15K_mixed`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The classical form of `K`. -/
noncomputable def i15KR (r : ℝ) : ℝ :=
  -(3 / 2) * Li₃ (1 - r ^ 2) + 3 * Li₃ (1 - r) + 3 * Li₃ (1 / (1 + r)) -
    2 * log (1 + r) * Li₂ r - 2 * log r * log (1 - r) * log (1 + r) - log (1 + r) ^ 3 / 2 -
    π ^ 2 / 4 * log (1 - r) + 3 * π ^ 2 / 4 * log (1 + r) - 9 / 2 * zeta3

theorem hasDerivAt_i15KR {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i15KR
      (2 * hpl [zero, negOne] x / (1 - x) - hpl [negOne, zero] x / (1 - x) -
        hpl [one, zero] x / (1 + x)) x := by
  obtain ⟨h0, h1⟩ := hx
  have hm1 : 1 - x ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hm2 : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hm3 : 1 / (1 + x) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩
  have hxm : x ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have d1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_sub 1
  have d2 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have d3 : HasDerivAt (fun y : ℝ => 1 / (1 + y)) (-1 / (1 + x) ^ 2) x := by
    have := (hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id' x).const_add 1)
      (by linarith : (1 : ℝ) + x ≠ 0)
    refine HasDerivAt.congr_deriv (f := fun y : ℝ => 1 / (1 + y)) this ?_
    ring
  have hp : HasDerivAt (fun y : ℝ => log (1 + y)) (1 / (1 + x)) x := by
    simpa using ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
  have hl : HasDerivAt (fun y : ℝ => log (1 - y)) (-1 / (1 - x)) x := d2.log (by linarith)
  have h := (((((((((((hasDerivAt_Li₃' hm1).comp x d1).const_mul (-(3 / 2))).add
    (((hasDerivAt_Li₃' hm2).comp x d2).const_mul 3)).add
    (((hasDerivAt_Li₃' hm3).comp x d3).const_mul 3)).sub
    ((hp.const_mul 2).mul (hasDerivAt_Li₂' hxm))).sub
    ((((hasDerivAt_log h0.ne').const_mul 2).mul hl).mul hp)).sub
    ((hp.pow 3).div_const 2)).sub (hl.const_mul (π ^ 2 / 4))).add
    (hp.const_mul (3 * π ^ 2 / 4))).sub (hasDerivAt_const x (9 / 2 * zeta3)))
  refine h.congr_deriv ?_
  have r1 := Li₂_add_Li₂_one_sub (x := x ^ 2) (by positivity) (by nlinarith)
  have r2 := Li₂_add_Li₂_neg (x := x) (by rw [abs_of_pos h0]; exact h1.le)
  have r3 := Li₂_add_Li₂_one_sub (x := x) h0.le h1.le
  have r4 := Li_two_inv_one_add hxm
  have l1 : log (x ^ 2) = 2 * log x := by rw [log_pow]; push_cast; ring
  have l2 : log (1 - x ^ 2) = log (1 - x) + log (1 + x) := by
    rw [← log_mul (by linarith) (by linarith)]; ring_nf
  rw [Li_two] at r4
  simp only [hpl_zero_negOne hxm, hpl_negOne_zero hxm, hpl_one_zero hxm, Li_two, Pi.mul_apply]
  rw [l1, l2] at r1
  have e1 : Li₂ (1 - x ^ 2) = π ^ 2 / 6 - 2 * log x * (log (1 - x) + log (1 + x)) -
      2 * (Li₂ x + Li₂ (-x)) := by linarith
  have e2 : Li₂ (1 - x) = π ^ 2 / 6 - log x * log (1 - x) - Li₂ x := by linarith
  rw [e1, e2, r4]
  have hx1 : 1 - x ≠ 0 := by linarith
  have hx2 : 1 + x ≠ 0 := by linarith
  have hx3 : 1 - x ^ 2 ≠ 0 := hm1.1.ne'
  have hx4 : 1 / (1 + x) ≠ 0 := hm3.1.ne'
  field_simp
  ring

theorem tendsto_i15KR_zero : Tendsto i15KR (𝓝[>] 0) (𝓝 0) := by
  have hI : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have t1 : Tendsto (fun x : ℝ => Li₃ (1 - x ^ 2)) (𝓝[>] 0) (𝓝 zeta3) := by
    have h := tendsto_Li₃_comp (l := 𝓝[>] (0 : ℝ)) (a := 1) (g := fun x : ℝ => 1 - x ^ 2)
      (by norm_num) (by
        have : Tendsto (fun x : ℝ => 1 - x ^ 2) (𝓝 0) (𝓝 (1 - 0 ^ 2)) :=
          (continuous_const.sub (continuous_pow 2)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds) (by
        filter_upwards [hI] with x hx
        exact ⟨by nlinarith [hx.1, hx.2], by nlinarith [hx.1]⟩)
    rwa [Li₃_one] at h
  have t2 : Tendsto (fun x : ℝ => Li₃ (1 - x)) (𝓝[>] 0) (𝓝 zeta3) := by
    have h := tendsto_Li₃_comp (l := 𝓝[>] (0 : ℝ)) (a := 1) (g := fun x : ℝ => 1 - x)
      (by norm_num) (by
        have : Tendsto (fun x : ℝ => 1 - x) (𝓝 0) (𝓝 (1 - 0)) :=
          (continuous_const.sub continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds) (by
        filter_upwards [hI] with x hx
        exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    rwa [Li₃_one] at h
  have t3 : Tendsto (fun x : ℝ => Li₃ (1 / (1 + x))) (𝓝[>] 0) (𝓝 zeta3) := by
    have h := tendsto_Li₃_comp (l := 𝓝[>] (0 : ℝ)) (a := 1) (g := fun x : ℝ => 1 / (1 + x))
      (by norm_num) (by
        have : Tendsto (fun x : ℝ => 1 / (1 + x)) (𝓝 0) (𝓝 (1 / (1 + 0))) :=
          (continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)).tendsto
        simpa using this.mono_left nhdsWithin_le_nhds) (by
        filter_upwards [hI] with x hx
        refine ⟨by have := hx.1; rw [le_div_iff₀ (by linarith [hx.1])]; nlinarith, ?_⟩
        rw [div_le_one (by linarith [hx.1])]; linarith [hx.1])
    rwa [Li₃_one] at h
  have hp : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => log (1 + x)) (𝓝 0) (𝓝 (log (1 + 0))) :=
      ((continuousAt_log (by norm_num)).comp (continuous_const.add continuous_id).continuousAt)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hm : Tendsto (fun x : ℝ => log (1 - x)) (𝓝[>] 0) (𝓝 0) := tendsto_log_one_sub_zero
  have h := ((((((((t1.const_mul (-(3 / 2))).add (t2.const_mul 3)).add (t3.const_mul 3)).sub
    ((hp.const_mul 2).mul tendsto_Li₂_zero_right)).sub
    ((tendsto_log_mul_log_one_sub_zero.const_mul 2).mul hp)).sub ((hp.pow 3).div_const 2)).sub
    (hm.const_mul (π ^ 2 / 4))).add (hp.const_mul (3 * π ^ 2 / 4))).sub
    (tendsto_const_nhds (x := 9 / 2 * zeta3))
  convert h using 2 with x
  all_goals (try simp only [i15KR])
  all_goals ring

/-- **`K = 2 H(1, 0, -1) - H(1, -1, 0) - H(-1, 1, 0)` in classical polylogarithms.** -/
theorem i15K_mixed {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    2 * hpl [one, zero, negOne] r - hpl [one, negOne, zero] r - hpl [negOne, one, zero] r =
      i15KR r := by
  have h := eq_of_hasDerivAt_zero_of_tendsto_right (c := 0)
    (F := fun x => 2 * hpl [one, zero, negOne] x - hpl [one, negOne, zero] x -
      hpl [negOne, one, zero] x - i15KR x) zero_lt_one (fun x hx => by
      have h := ((((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul 2).sub
        (hasDerivAt_hpl_cons one [negOne, zero] hx)).sub
        (hasDerivAt_hpl_cons negOne [one, zero] hx)).sub (hasDerivAt_i15KR hx)
      refine h.congr_deriv ?_
      simp only [kernel_one, kernel_negOne]
      field_simp
      ring) (by
      have h := ((((tendsto_hpl_zero (w := [one, zero, negOne]) (by simp [AllZero])).const_mul
        2).sub (tendsto_hpl_zero (w := [one, negOne, zero]) (by simp [AllZero]))).sub
        (tendsto_hpl_zero (w := [negOne, one, zero]) (by simp [AllZero]))).sub tendsto_i15KR_zero
      simpa using h) r hr
  linarith

end QED.ThreeLoopD
