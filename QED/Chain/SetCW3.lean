/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
import QED.Polylog.AlphabetPM
import QED.Polylog.DilogPM
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus
import QED.Polylog.LiHalf
import QED.Polylog.LiLimits
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (c): the weight-three part

Helper analysis for the sixth-order set (c) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

Integration by parts reduces the set (c) integrand `QED.Chain.setCJ` to the derivative of a
rational-coefficient part (`QED.Chain.SetCW1`), the weight-four term `(5/3) log s Φ(s)/s`
(`QED.Polylog.integral_log_mul_setCPhi_div`) and the simple-pole remainder `g₃ = setCg3` of
weight at most three, with poles at `s = 0, 1, -1`. It has a classical antiderivative `G₃` built
from `P(f) = Li 3 f - log f · Li 2 f` at `s/(1+s), t, (1+s)/2, (1-s)/2, 2s/(1+s), 1 - s²`
(`t = (1-s)/(1+s)`), `Li 3 (±s)`, `Li 2 (±s)` times a logarithm, and a cubic polynomial in
logarithms. Its only mixed-alphabet input is `∫₀¹ log s log (1+s)/(1-s) = 3/2 ζ(2) log 2 - ζ(3)`,
the source of the `-8 ζ(2) log 2` of the set (c) value.

## Main statements

* `QED.Chain.hasDerivAt_setCG3`: `G₃' = g₃` on `(0, 1)`.
* `QED.Chain.tendsto_setCG3_zero`: `G₃(0⁺) = ζ(3)/3 - 8/9 log³ 2`.
* `QED.Chain.tendsto_setCG3_one`:
  `G₃(1⁻) = -97/24 ζ(3) - 8/9 log³ 2 - 4/3 π² log 2 + 31/54 π² + 8/9 log 2`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.Chain

/-- The weight-at-most-three simple-pole part `g₃` of the set (c) integrand. -/
noncomputable def setCg3 (u : ℝ) : ℝ :=
  -(92 / 9) * Li 2 (-u) / u - 46 / 9 * Li 2 u / u - 16 / 3 * log u * log (1 + u) / (u - 1) +
    8 / 3 * log u * log (1 + u) / u + 1 / 2 * log u * log (1 - u) / u -
    8 / 3 * log u * log (1 - u) / (u - 1) - 193 / 36 * log u ^ 2 / (u + 1) +
    97 / 36 * log u ^ 2 / (u - 1) - 125 / 27 * log (1 + u) / u - 55 / 12 * log (1 - u) / u -
    131 / 54 * log u / (u + 1) - 1 / 27 * log u / (u - 1) + 8 / 9 / (u + 1)

/-- The weight-three antiderivative `G₃` (with `t = (1-u)/(1+u)`). -/
noncomputable def setCG3 (u : ℝ) : ℝ :=
  8 / 3 * (Li 3 (u / (1 + u)) - log (u / (1 + u)) * Li 2 (u / (1 + u))) -
    4 / 3 * (Li 3 ((1 - u) / (1 + u)) - log ((1 - u) / (1 + u)) * Li 2 ((1 - u) / (1 + u))) +
    4 * (Li 3 ((1 + u) / 2) - log ((1 + u) / 2) * Li 2 ((1 + u) / 2)) -
    4 / 3 * (Li 3 ((1 - u) / 2) - log ((1 - u) / 2) * Li 2 ((1 - u) / 2)) -
    16 / 3 * (Li 3 (2 * u / (1 + u)) - log (2 * u / (1 + u)) * Li 2 (2 * u / (1 + u))) -
    2 / 3 * (Li 3 (1 - u ^ 2) - log (1 - u ^ 2) * Li 2 (1 - u ^ 2)) -
    14 / 3 * Li 3 u + 1 / 2 * Li 3 (-u) +
    Li 2 u * (-(4 / 9) * log u - 16 / 3 * log 2 + 491 / 108) +
    Li 2 (-u) * (-(193 / 18) * log u + 16 / 3 * log 2 + 119 / 54) +
    (8 / 9 * log (1 + u) - 1 / 27 * log u * log (1 - u) - 131 / 54 * log u * log (1 + u) +
      97 / 36 * log u ^ 2 * log (1 - u) - 193 / 36 * log u ^ 2 * log (1 + u) -
      16 / 3 * log u * log (1 - u) * log (1 + u) + 8 / 3 * log u * log (1 + u) ^ 2 +
      4 / 3 * (log (1 + u) - log 2) ^ 2 * log (1 - u) - 4 / 3 * log (1 + u) ^ 3 +
      16 / 3 * log (1 + u) ^ 2 * log 2 - 4 * log (1 + u) * log 2 ^ 2)

/-- **The weight-three antiderivative**: `G₃' = g₃` on `(0, 1)`. -/
theorem hasDerivAt_setCG3 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt setCG3 (setCg3 u) u := by
  obtain ⟨h0, h1⟩ := hu
  obtain ⟨dD, aD, nD, lD, gD, gD1⟩ := PM.data_divOneAdd h0 h1
  obtain ⟨dT, aT, nT, lT, gT, gT1⟩ := PM.data_ksT h0 h1
  obtain ⟨dF, aF, nF, lF, gF, gF1⟩ := PM.data_halfOneAdd h0 h1
  obtain ⟨dK, aK, nK, lK, gK, gK1⟩ := PM.data_halfOneSub h0 h1
  obtain ⟨dG, aG, nG, lG, gG, gG1⟩ := PM.data_twoMulDiv h0 h1
  obtain ⟨dI, aI, nI, lI, gI, gI1⟩ := PM.data_oneSubSq h0 h1
  obtain ⟨di, ai, ni, li, -, gi1⟩ := PM.data_id h0 h1
  obtain ⟨dA, aA, nA, lA, -, gA1⟩ := PM.data_neg h0 h1
  obtain ⟨dB, -, nB, lB, -, -⟩ := PM.data_oneSub h0 h1
  have pD := hasDerivAt_Li_three_sub_of dD aD nD lD gD gD1
  have pT := hasDerivAt_Li_three_sub_of dT aT nT lT gT gT1
  have pF := hasDerivAt_Li_three_sub_of dF aF nF lF gF gF1
  have pK := hasDerivAt_Li_three_sub_of dK aK nK lK gK gK1
  have pG := hasDerivAt_Li_three_sub_of dG aG nG lG gG gG1
  have pI := hasDerivAt_Li_three_sub_of dI aI nI lI gI gI1
  have t1 := hasDerivAt_Li_three_of di ai ni li rfl
  have t2 := hasDerivAt_Li_three_of dA aA nA lA rfl
  have qP := hasDerivAt_Li_two_of di ai ni li gi1
  have qM := hasDerivAt_Li_two_of dA aA nA lA gA1
  have e0 := hasDerivAt_log_of di ni li
  have e1 := hasDerivAt_log_of dB nB lB
  have em : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + u)) u := by
    have := ((hasDerivAt_id' u).const_add 1).log (by linarith)
    simpa [one_div] using this
  have r1 := qP.mul (((e0.const_mul (-(4 / 9))).sub_const (16 / 3 * log 2)).add_const
    (491 / 108))
  have r2 := qM.mul (((e0.const_mul (-(193 / 18))).add_const (16 / 3 * log 2)).add_const
    (119 / 54))
  have s1 := em.const_mul (8 / 9)
  have s2 := (e0.mul e1).const_mul (1 / 27)
  have s3 := (e0.mul em).const_mul (131 / 54)
  have s4 := ((e0.pow 2).mul e1).const_mul (97 / 36)
  have s5 := ((e0.pow 2).mul em).const_mul (193 / 36)
  have s6 := ((e0.mul e1).mul em).const_mul (16 / 3)
  have s7 := (e0.mul (em.pow 2)).const_mul (8 / 3)
  have s8 := (((em.sub_const (log 2)).pow 2).mul e1).const_mul (4 / 3)
  have s9 := (em.pow 3).const_mul (4 / 3)
  have s10 := ((em.pow 2).mul_const (log 2)).const_mul (16 / 3)
  have s11 := (em.mul_const (log 2 ^ 2)).const_mul 4
  have S := (((((((((s1.sub s2).sub s3).add s4).sub s5).sub s6).add s7).add s8).sub s9).add
    s10).sub s11
  have P := ((((((((pD.const_mul (8 / 3)).sub (pT.const_mul (4 / 3))).add (pF.const_mul 4)).sub
    (pK.const_mul (4 / 3))).sub (pG.const_mul (16 / 3))).sub (pI.const_mul (2 / 3))).sub
    (t1.const_mul (14 / 3))).add (t2.const_mul (1 / 2)))
  have h := ((P.add r1).add r2).add S
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  swap
  · simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    unfold setCG3
    ring
  simp only [Pi.pow_apply, Pi.mul_apply]
  unfold setCg3
  have hm : 1 - u ≠ 0 := by linarith
  have hm' : u - 1 ≠ 0 := by linarith
  have hp : 1 + u ≠ 0 := by linarith
  have hp' : u + 1 ≠ 0 := by linarith
  have hz : u ≠ 0 := h0.ne'
  field_simp
  ring

private theorem tlim {l : Filter ℝ} {x₀ : ℝ} (hl : l ≤ 𝓝 x₀) {g : ℝ → ℝ} {a : ℝ}
    (hg : ContinuousAt g x₀) (h : g x₀ = a) : Tendsto g l (𝓝 a) :=
  h ▸ hg.tendsto.mono_left hl

private theorem mem_Icc_of_abs {x : ℝ} (h : |x| < 1) : x ∈ Icc (-1 : ℝ) 1 :=
  mem_Icc.2 (abs_le.1 h.le)

private theorem log_half : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]

/-- `G₃(0⁺) = ζ(3)/3 - 8/9 log³ 2`. -/
theorem tendsto_setCG3_zero :
    Tendsto setCG3 (𝓝[>] 0) (𝓝 (zeta3 / 3 - 8 / 9 * log 2 ^ 3)) := by
  have ev : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have m1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have mh : (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have m0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sA := ev.mono fun u hu => mem_Icc_of_abs (PM.data_neg hu.1 hu.2).2.1
  have sD := ev.mono fun u hu => mem_Icc_of_abs (PM.data_divOneAdd hu.1 hu.2).2.1
  have sT := ev.mono fun u hu => mem_Icc_of_abs (PM.data_ksT hu.1 hu.2).2.1
  have sF := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneAdd hu.1 hu.2).2.1
  have sG := ev.mono fun u hu => mem_Icc_of_abs (PM.data_twoMulDiv hu.1 hu.2).2.1
  have sI := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSubSq hu.1 hu.2).2.1
  have sK := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneSub hu.1 hu.2).2.1
  have si := ev.mono fun u hu => mem_Icc_of_abs (PM.data_id hu.1 hu.2).2.1
  have gi : Tendsto (fun u : ℝ => u) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gA : Tendsto (fun u : ℝ => -u) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gD : Tendsto (fun u : ℝ => u / (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gT : Tendsto (fun u : ℝ => (1 - u) / (1 + u)) _ (𝓝 1) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gF : Tendsto (fun u : ℝ => (1 + u) / 2) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop) (by norm_num)
  have gG : Tendsto (fun u : ℝ => 2 * u / (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gI : Tendsto (fun u : ℝ => 1 - u ^ 2) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gK : Tendsto (fun u : ℝ => (1 - u) / 2) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop) (by norm_num)
  have T1 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gD sD
  have T2 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) m1
    one_ne_zero gT sT
  have T3 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) mh
    (by norm_num) gF sF
  have T4 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) mh
    (by norm_num) gK sK
  have T5 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gG sG
  have T6 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) m1
    one_ne_zero gI sI
  have T7 := tendsto_Li_comp (k := 3) (by norm_num) m0 gi si
  have T8 := tendsto_Li_comp (k := 3) (by norm_num) m0 gA sA
  have lb : Tendsto (fun u : ℝ => log (1 - u)) (𝓝[>] 0) (𝓝 0) := tendsto_log_one_sub_zero
  have lm : Tendsto (fun u : ℝ => log (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have qi := tendsto_Li_comp (k := 2) (by norm_num) m0 gi si
  have qA := tendsto_Li_comp (k := 2) (by norm_num) m0 gA sA
  have vi := tendsto_log_mul_Li_comp (k := 2) (by norm_num) gi (si.mono fun _ h => abs_le.2 h)
  have vA := tendsto_log_mul_Li_comp (k := 2) (by norm_num) gA (sA.mono fun _ h => abs_le.2 h)
  have R1 := (vi.const_mul (-(4 / 9))).add (qi.mul_const (-(16 / 3) * log 2 + 491 / 108))
  have R2 := (vA.const_mul (-(193 / 18))).add (qA.mul_const (16 / 3 * log 2 + 119 / 54))
  have X1 := tendsto_log_mul_log_one_sub_zero
  have X2 := tendsto_log_mul_log_one_add_zero
  have X3 := tendsto_log_one_sub_mul_log_sq
  have X4 := tendsto_log_one_add_mul_log_sq
  have X5 := ((((((((lm.const_mul (8 / 9)).sub (X1.const_mul (1 / 27))).sub
    (X2.const_mul (131 / 54))).add (X3.const_mul (97 / 36))).sub (X4.const_mul (193 / 36))).sub
    ((X1.mul lm).const_mul (16 / 3))).add ((X2.mul lm).const_mul (8 / 3))).add
    ((((lm.sub_const (log 2)).pow 2).mul lb).const_mul (4 / 3)))
  have X6 := (((lm.pow 3).const_mul (4 / 3)).sub ((lm.pow 2).const_mul (16 / 3 * log 2))).add
    (lm.const_mul (4 * log 2 ^ 2))
  have P := ((((((((T1.const_mul (8 / 3)).sub (T2.const_mul (4 / 3))).add (T3.const_mul 4)).sub
    (T4.const_mul (4 / 3))).sub (T5.const_mul (16 / 3))).sub (T6.const_mul (2 / 3))).sub
    (T7.const_mul (14 / 3))).add (T8.const_mul (1 / 2)))
  have H := (((P.add R1).add R2).add X5).sub X6
  have H2 : Tendsto setCG3 (𝓝[>] 0) (𝓝 _) := H.congr' <| by
    filter_upwards [ev] with u hu
    unfold setCG3
    rw [Real.log_neg_eq_log]
    ring
  convert H2 using 2
  simp only [Li_zero, log_one, log_half, Li_three_one, Li_two_one_half,
    Li_three_one_half, mul_zero, zero_mul, sub_zero]
  ring

/-- `G₃(1⁻) = -97/24 ζ(3) - 8/9 log³ 2 - 4/3 π² log 2 + 31/54 π² + 8/9 log 2`. -/
theorem tendsto_setCG3_one :
    Tendsto setCG3 (𝓝[<] 1) (𝓝 (-(97 / 24) * zeta3 - 8 / 9 * log 2 ^ 3 -
      4 / 3 * π ^ 2 * log 2 + 31 / 54 * π ^ 2 + 8 / 9 * log 2)) := by
  have ev : ∀ᶠ u in 𝓝[<] (1 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
  have hl : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have m1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have mm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have mh : (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sA := ev.mono fun u hu => mem_Icc_of_abs (PM.data_neg hu.1 hu.2).2.1
  have sD := ev.mono fun u hu => mem_Icc_of_abs (PM.data_divOneAdd hu.1 hu.2).2.1
  have sT := ev.mono fun u hu => mem_Icc_of_abs (PM.data_ksT hu.1 hu.2).2.1
  have sF := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneAdd hu.1 hu.2).2.1
  have sG := ev.mono fun u hu => mem_Icc_of_abs (PM.data_twoMulDiv hu.1 hu.2).2.1
  have sI := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSubSq hu.1 hu.2).2.1
  have sK := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneSub hu.1 hu.2).2.1
  have si := ev.mono fun u hu => mem_Icc_of_abs (PM.data_id hu.1 hu.2).2.1
  have gi : Tendsto (fun u : ℝ => u) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gA : Tendsto (fun u : ℝ => -u) _ (𝓝 (-1)) := tlim hl (by fun_prop) (by norm_num)
  have gD : Tendsto (fun u : ℝ => u / (1 + u)) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gT : Tendsto (fun u : ℝ => (1 - u) / (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gF : Tendsto (fun u : ℝ => (1 + u) / 2) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gG : Tendsto (fun u : ℝ => 2 * u / (1 + u)) _ (𝓝 1) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gI : Tendsto (fun u : ℝ => 1 - u ^ 2) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gK : Tendsto (fun u : ℝ => (1 - u) / 2) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have T1 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) mh
    (by norm_num) gD sD
  have T2 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gT sT
  have T3 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) m1
    one_ne_zero gF sF
  have T4 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gK sK
  have T5 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) m1
    one_ne_zero gG sG
  have T6 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gI sI
  have T7 := tendsto_Li_comp (k := 3) (by norm_num) m1 gi si
  have T8 := tendsto_Li_comp (k := 3) (by norm_num) mm gA sA
  have l0 : Tendsto (fun u : ℝ => log u) _ (𝓝 0) :=
    tlim hl (continuousAt_log one_ne_zero) (by norm_num)
  have lm : Tendsto (fun u : ℝ => log (1 + u)) _ (𝓝 (log 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have qi := tendsto_Li_comp (k := 2) (by norm_num) m1 gi si
  have qA := tendsto_Li_comp (k := 2) (by norm_num) mm gA sA
  have R1 := qi.mul (((l0.const_mul (-(4 / 9))).sub_const (16 / 3 * log 2)).add_const
    (491 / 108))
  have R2 := qA.mul (((l0.const_mul (-(193 / 18))).add_const (16 / 3 * log 2)).add_const
    (119 / 54))
  have Y1 := tendsto_log_mul_log_one_sub_one
  have Y2 : Tendsto (fun x : ℝ => 4 / 3 * (log (1 + x) - log 2) ^ 2 * log (1 - x)) (𝓝[<] 1)
      (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 2) ?_
    filter_upwards [ev] with x hx
    obtain ⟨h0, h1⟩ := hx
    have hB := abs_log_one_add_div_two_le h0.le h1.le
    rw [log_div (by linarith) two_ne_zero] at hB
    rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    have : |log (1 + x) - log 2| ^ 2 ≤ (1 - x) * 1 := by
      rw [sq]
      exact mul_le_mul hB (hB.trans (by linarith)) (abs_nonneg _) (by linarith)
    nlinarith
  have Y3 := (((((((lm.const_mul (8 / 9)).sub (Y1.const_mul (1 / 27))).sub
    ((l0.mul lm).const_mul (131 / 54))).add ((l0.mul Y1).const_mul (97 / 36))).sub
    (((l0.pow 2).mul lm).const_mul (193 / 36))).sub ((Y1.mul lm).const_mul (16 / 3))).add
    ((l0.mul (lm.pow 2)).const_mul (8 / 3)))
  have Y4 := (((lm.pow 3).const_mul (4 / 3)).sub ((lm.pow 2).const_mul (16 / 3 * log 2))).add
    (lm.const_mul (4 * log 2 ^ 2))
  have P := ((((((((T1.const_mul (8 / 3)).sub (T2.const_mul (4 / 3))).add (T3.const_mul 4)).sub
    (T4.const_mul (4 / 3))).sub (T5.const_mul (16 / 3))).sub (T6.const_mul (2 / 3))).sub
    (T7.const_mul (14 / 3))).add (T8.const_mul (1 / 2)))
  have H := ((((P.add R1).add R2).add Y3).add Y2).sub Y4
  have H2 : Tendsto setCG3 (𝓝[<] 1) (𝓝 _) := H.congr fun u => by
    unfold setCG3
    ring
  convert H2 using 2
  simp only [log_one, log_half, Li_three_one, Li_two_one_half,
    Li_three_one_half, mul_zero, zero_mul, sub_zero,
    show Li 3 (-1) = -(3 / 4) * zeta3 from Li₃_neg_one,
    show Li 2 1 = π ^ 2 / 6 from Li₂_one, show Li 2 (-1) = -π ^ 2 / 12 from Li₂_neg_one]
  ring

end QED.Chain
