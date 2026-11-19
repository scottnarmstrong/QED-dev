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
# Set (a): the weight-three part

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

The weight-three part of the set (a) integrand `QED.Chain.setAJ` is `QED.Chain.setAg3`. It has a
classical antiderivative `G₃` built from the combinations `P(f) = Li 3 f - log f · Li 2 f` at
`u/(1+u), (1+u)/2, 2u/(1+u), 1 - u², t², (1-u)/2` (`t = (1-u)/(1+u)`), `Li 3 (±u)`, dilogarithms
times one logarithm, and a cubic polynomial in logarithms. Its derivative is checked with the
dilogarithm identities of `QED.Polylog.DilogPM`.

## Main statements

* `QED.Chain.hasDerivAt_setAG3`: `G₃' = g₃` on `(0, 1)`.
* `QED.Chain.tendsto_setAG3_zero`, `QED.Chain.tendsto_setAG3_one`:
  `G₃(0⁺) = -209/18 ζ(3) + 124/27 log³ 2 - 10/9 π² log 2` and
  `G₃(1⁻) = -98/9 ζ(3) + 124/27 log³ 2 - 17/9 π² log 2`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.Chain

/-- The weight-three part `g₃` of the set (a) integrand. -/
noncomputable def setAg3 (u : ℝ) : ℝ :=
  4 / 9 * log u ^ 2 / (1 + u) - 100 / 9 * log u * log (1 - u) / u -
    20 / 3 * log u * log (1 - u) / (1 + u) - 6 * log u * log (1 + u) / u -
    8 / 3 * log u * log (1 + u) / (1 + u) + 28 / 3 * log (1 - u) * log (1 + u) / u +
    4 * log (1 + u) ^ 2 / u + 176 / 9 * (Li 2 u + Li 2 (-u) / 2) * (1 / u - 1 / (1 + u))

/-- The weight-three antiderivative `G₃` (with `t = (1-u)/(1+u)`). -/
noncomputable def setAG3 (u : ℝ) : ℝ :=
  -(140 / 9) * (Li 3 (u / (1 + u)) - log (u / (1 + u)) * Li 2 (u / (1 + u))) -
    92 / 9 * (Li 3 ((1 + u) / 2) - log ((1 + u) / 2) * Li 2 ((1 + u) / 2)) +
    20 / 3 * (Li 3 (2 * u / (1 + u)) - log (2 * u / (1 + u)) * Li 2 (2 * u / (1 + u))) +
    8 / 9 * (Li 3 (1 - u ^ 2) - log (1 - u ^ 2) * Li 2 (1 - u ^ 2)) -
    4 / 9 * (Li 3 (((1 - u) / (1 + u)) ^ 2) -
      log (((1 - u) / (1 + u)) ^ 2) * Li 2 (((1 - u) / (1 + u)) ^ 2)) -
    32 / 9 * (Li 3 ((1 - u) / 2) - log ((1 - u) / 2) * Li 2 ((1 - u) / 2)) +
    16 / 9 * Li 3 u - 6 * Li 3 (-u) +
    Li 2 (u / (1 + u)) * (-(142 / 9) * log u + 88 / 9 * log (1 + u) + 20 / 3 * log 2) +
    Li 2 (1 - u) * (-(160 / 9) * log u + 176 / 9 * log (1 + u) - 20 / 3 * log 2) +
    (-(160 / 9) * log u ^ 2 * log (1 - u) + 4 / 9 * log u ^ 2 * log (1 + u) +
      16 * log u * log (1 - u) * log (1 + u) - 20 / 3 * log u * log (1 - u) * log 2 -
      43 / 9 * log u * log (1 + u) ^ 2 + 32 / 9 * log (1 - u) * log (1 + u) ^ 2 -
      64 / 9 * log (1 - u) * log (1 + u) * log 2 + 32 / 9 * log (1 - u) * log 2 ^ 2 +
      20 / 27 * log (1 + u) ^ 3 - 10 / 3 * log (1 + u) ^ 2 * log 2 +
      92 / 9 * log (1 + u) * log 2 ^ 2 + 160 / 9 * (π ^ 2 / 6) * log u -
      176 / 9 * (π ^ 2 / 6) * log (1 + u))

/-- **The weight-three antiderivative**: `G₃' = g₃` on `(0, 1)`. -/
theorem hasDerivAt_setAG3 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt setAG3 (setAg3 u) u := by
  obtain ⟨h0, h1⟩ := hu
  have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  obtain ⟨dB, aB, nB, lB, gB, gB1⟩ := PM.data_oneSub h0 h1
  obtain ⟨dD, aD, nD, lD, gD, gD1⟩ := PM.data_divOneAdd h0 h1
  obtain ⟨dF, aF, nF, lF, gF, gF1⟩ := PM.data_halfOneAdd h0 h1
  obtain ⟨dG, aG, nG, lG, gG, gG1⟩ := PM.data_twoMulDiv h0 h1
  obtain ⟨dI, aI, nI, lI, gI, gI1⟩ := PM.data_oneSubSq h0 h1
  obtain ⟨dJ, aJ, nJ, lJ, gJ, gJ1⟩ := PM.data_ksTSq h0 h1
  obtain ⟨dK, aK, nK, lK, gK, gK1⟩ := PM.data_halfOneSub h0 h1
  obtain ⟨di, ai, ni, li, -, -⟩ := PM.data_id h0 h1
  obtain ⟨dA, aA, nA, lA, -, -⟩ := PM.data_neg h0 h1
  have pD := hasDerivAt_Li_three_sub_of dD aD nD lD gD gD1
  have pF := hasDerivAt_Li_three_sub_of dF aF nF lF gF gF1
  have pG := hasDerivAt_Li_three_sub_of dG aG nG lG gG gG1
  have pI := hasDerivAt_Li_three_sub_of dI aI nI lI gI gI1
  have pJ := hasDerivAt_Li_three_sub_of dJ aJ nJ lJ gJ gJ1
  have pK := hasDerivAt_Li_three_sub_of dK aK nK lK gK gK1
  have t1 := hasDerivAt_Li_three_of di ai ni li rfl
  have t2 := hasDerivAt_Li_three_of dA aA nA lA rfl
  have qD := hasDerivAt_Li_two_of dD aD nD lD gD1
  have qB := hasDerivAt_Li_two_of dB aB nB lB gB1
  have e0 := hasDerivAt_log_of di ni li
  have e1 := hasDerivAt_log_of dB nB lB
  have em : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + u)) u := by
    have := ((hasDerivAt_id' u).const_add 1).log (by linarith)
    simpa [one_div] using this
  have r1 := qD.mul (((e0.const_mul (-(142 / 9))).add (em.const_mul (88 / 9))).add_const
    (20 / 3 * log 2))
  have r2 := qB.mul (((e0.const_mul (-(160 / 9))).add (em.const_mul (176 / 9))).sub_const
    (20 / 3 * log 2))
  have s1 := ((e0.pow 2).const_mul (-(160 / 9))).mul e1
  have s2 := ((e0.pow 2).const_mul (4 / 9)).mul em
  have s3 := ((e0.const_mul 16).mul e1).mul em
  have s4 := ((e0.const_mul (20 / 3)).mul e1).mul_const (log 2)
  have s5 := (e0.const_mul (43 / 9)).mul (em.pow 2)
  have s6 := (e1.const_mul (32 / 9)).mul (em.pow 2)
  have s7 := ((e1.const_mul (64 / 9)).mul em).mul_const (log 2)
  have s8 := (e1.const_mul (32 / 9)).mul_const (log 2 ^ 2)
  have s9 := (em.pow 3).const_mul (20 / 27)
  have s10 := ((em.pow 2).const_mul (10 / 3)).mul_const (log 2)
  have s11 := (em.const_mul (92 / 9)).mul_const (log 2 ^ 2)
  have s12 := e0.const_mul (160 / 9 * (π ^ 2 / 6))
  have s13 := em.const_mul (176 / 9 * (π ^ 2 / 6))
  have S := (((((((((((s1.add s2).add s3).sub s4).sub s5).add s6).sub s7).add s8).add s9).sub
    s10).add s11).add s12).sub s13
  have P := ((((((((pD.const_mul (-(140 / 9))).sub (pF.const_mul (92 / 9))).add
    (pG.const_mul (20 / 3))).add (pI.const_mul (8 / 9))).sub (pJ.const_mul (4 / 9))).sub
    (pK.const_mul (32 / 9))).add (t1.const_mul (16 / 9))).sub (t2.const_mul 6))
  have h := ((P.add r1).add r2).add S
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  rw [Li_two_div_one_add hu, Li_two_one_sub' hu]
  unfold setAg3
  have hm : 1 - u ≠ 0 := by linarith
  have hp : 1 + u ≠ 0 := by linarith
  field_simp
  ring

private theorem tlim {l : Filter ℝ} {x₀ : ℝ} (hl : l ≤ 𝓝 x₀) {g : ℝ → ℝ} {a : ℝ}
    (hg : ContinuousAt g x₀) (h : g x₀ = a) : Tendsto g l (𝓝 a) :=
  h ▸ hg.tendsto.mono_left hl

private theorem mem_Icc_of_abs {x : ℝ} (h : |x| < 1) : x ∈ Icc (-1 : ℝ) 1 :=
  mem_Icc.2 (abs_le.1 h.le)

private theorem log_half : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]

/-- `G₃(0⁺) = -209/18 ζ(3) + 124/27 log³ 2 - 10/9 π² log 2`. -/
theorem tendsto_setAG3_zero :
    Tendsto setAG3 (𝓝[>] 0)
      (𝓝 (-(209 / 18) * zeta3 + 124 / 27 * log 2 ^ 3 - 10 / 9 * π ^ 2 * log 2)) := by
  have ev : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have m1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have mh : (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have m0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sA := ev.mono fun u hu => mem_Icc_of_abs (PM.data_neg hu.1 hu.2).2.1
  have sB := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSub hu.1 hu.2).2.1
  have sD := ev.mono fun u hu => mem_Icc_of_abs (PM.data_divOneAdd hu.1 hu.2).2.1
  have sF := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneAdd hu.1 hu.2).2.1
  have sG := ev.mono fun u hu => mem_Icc_of_abs (PM.data_twoMulDiv hu.1 hu.2).2.1
  have sI := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSubSq hu.1 hu.2).2.1
  have sJ := ev.mono fun u hu => mem_Icc_of_abs (PM.data_ksTSq hu.1 hu.2).2.1
  have sK := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneSub hu.1 hu.2).2.1
  have si := ev.mono fun u hu => mem_Icc_of_abs (PM.data_id hu.1 hu.2).2.1
  have gi : Tendsto (fun u : ℝ => u) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gA : Tendsto (fun u : ℝ => -u) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gB : Tendsto (fun u : ℝ => 1 - u) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gD : Tendsto (fun u : ℝ => u / (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gF : Tendsto (fun u : ℝ => (1 + u) / 2) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop) (by norm_num)
  have gG : Tendsto (fun u : ℝ => 2 * u / (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gI : Tendsto (fun u : ℝ => 1 - u ^ 2) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gJ : Tendsto (fun u : ℝ => ((1 - u) / (1 + u)) ^ 2) _ (𝓝 1) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gK : Tendsto (fun u : ℝ => (1 - u) / 2) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop) (by norm_num)
  have T1 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gD sD
  have T2 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) mh
    (by norm_num) gF sF
  have T3 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gG sG
  have T4 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) m1
    one_ne_zero gI sI
  have T5 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) m1
    one_ne_zero gJ sJ
  have T6 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) mh
    (by norm_num) gK sK
  have T7 := tendsto_Li_comp (k := 3) (by norm_num) m0 gi si
  have T8 := tendsto_Li_comp (k := 3) (by norm_num) m0 gA sA
  have lb : Tendsto (fun u : ℝ => log (1 - u)) (𝓝[>] 0) (𝓝 0) := tendsto_log_one_sub_zero
  have lm : Tendsto (fun u : ℝ => log (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have qD := tendsto_Li_comp (k := 2) (by norm_num) m0 gD sD
  have qB := tendsto_Li_comp (k := 2) (by norm_num) m1 gB sB
  have vD := tendsto_log_mul_Li_comp (k := 2) (by norm_num) gD (sD.mono fun _ h => abs_le.2 h)
  have vi := tendsto_log_mul_Li_comp (k := 2) (by norm_num) gi (si.mono fun _ h => abs_le.2 h)
  have R1 := (vD.const_mul (-(142 / 9))).add (qD.mul ((lm.const_mul (-(54 / 9))).add_const
    (20 / 3 * log 2)))
  have R2 := (vi.const_mul (160 / 9)).add (((lm.const_mul (176 / 9)).sub_const
    (20 / 3 * log 2)).mul qB)
  have X1 := (tendsto_log_one_add_mul_log_sq.const_mul (4 / 9)).add
    (tendsto_log_mul_log_one_sub_zero.mul ((lm.const_mul 16).sub_const (20 / 3 * log 2)))
  have X2 := (tendsto_log_mul_log_one_add_zero.mul lm).const_mul (43 / 9)
  have X3 := (((((((((lb.mul (lm.pow 2)).const_mul (32 / 9)).sub
    (((lb.mul lm).const_mul (64 / 9)).mul_const (log 2))).add
    (lb.const_mul (32 / 9 * log 2 ^ 2))).add ((lm.pow 3).const_mul (20 / 27))).sub
    ((lm.pow 2).const_mul (10 / 3 * log 2))).add (lm.const_mul (92 / 9 * log 2 ^ 2))).sub
    (lm.const_mul (176 / 9 * (π ^ 2 / 6)))))
  have P := ((((((((T1.const_mul (-(140 / 9))).sub (T2.const_mul (92 / 9))).add
    (T3.const_mul (20 / 3))).add (T4.const_mul (8 / 9))).sub (T5.const_mul (4 / 9))).sub
    (T6.const_mul (32 / 9))).add (T7.const_mul (16 / 9))).sub (T8.const_mul 6))
  have H := ((((P.add R1).add R2).add X1).sub X2).add X3
  have H2 : Tendsto setAG3 (𝓝[>] 0) (𝓝 _) := H.congr' <| by
    filter_upwards [ev] with u hu
    unfold setAG3
    rw [Li_two_one_sub' hu, (PM.data_divOneAdd hu.1 hu.2).2.2.2.2.1]
    ring
  convert H2 using 2
  simp only [Li_zero, log_one, log_half, Li_three_one, Li_two_one_half,
    Li_three_one_half, mul_zero, zero_mul, sub_zero, show Li 2 1 = π ^ 2 / 6 from Li₂_one]
  ring

/-- `G₃(1⁻) = -98/9 ζ(3) + 124/27 log³ 2 - 17/9 π² log 2`. -/
theorem tendsto_setAG3_one :
    Tendsto setAG3 (𝓝[<] 1)
      (𝓝 (-(98 / 9) * zeta3 + 124 / 27 * log 2 ^ 3 - 17 / 9 * π ^ 2 * log 2)) := by
  have ev : ∀ᶠ u in 𝓝[<] (1 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
  have hl : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have m1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have mm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have mh : (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have m0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sA := ev.mono fun u hu => mem_Icc_of_abs (PM.data_neg hu.1 hu.2).2.1
  have sB := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSub hu.1 hu.2).2.1
  have sD := ev.mono fun u hu => mem_Icc_of_abs (PM.data_divOneAdd hu.1 hu.2).2.1
  have sF := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneAdd hu.1 hu.2).2.1
  have sG := ev.mono fun u hu => mem_Icc_of_abs (PM.data_twoMulDiv hu.1 hu.2).2.1
  have sI := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSubSq hu.1 hu.2).2.1
  have sJ := ev.mono fun u hu => mem_Icc_of_abs (PM.data_ksTSq hu.1 hu.2).2.1
  have sK := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneSub hu.1 hu.2).2.1
  have si := ev.mono fun u hu => mem_Icc_of_abs (PM.data_id hu.1 hu.2).2.1
  have gi : Tendsto (fun u : ℝ => u) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gA : Tendsto (fun u : ℝ => -u) _ (𝓝 (-1)) := tlim hl (by fun_prop) (by norm_num)
  have gB : Tendsto (fun u : ℝ => 1 - u) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gD : Tendsto (fun u : ℝ => u / (1 + u)) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gF : Tendsto (fun u : ℝ => (1 + u) / 2) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gG : Tendsto (fun u : ℝ => 2 * u / (1 + u)) _ (𝓝 1) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gI : Tendsto (fun u : ℝ => 1 - u ^ 2) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gJ : Tendsto (fun u : ℝ => ((1 - u) / (1 + u)) ^ 2) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gK : Tendsto (fun u : ℝ => (1 - u) / 2) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have T1 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) mh
    (by norm_num) gD sD
  have T2 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) m1
    one_ne_zero gF sF
  have T3 := tendsto_Li_sub_log_mul_Li_comp (k := 3) (j := 2) (by norm_num) (by norm_num) m1
    one_ne_zero gG sG
  have T4 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gI sI
  have T5 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gJ sJ
  have T6 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 3) (j := 2) (by norm_num) (by norm_num)
    gK sK
  have T7 := tendsto_Li_comp (k := 3) (by norm_num) m1 gi si
  have T8 := tendsto_Li_comp (k := 3) (by norm_num) mm gA sA
  have l0 : Tendsto (fun u : ℝ => log u) _ (𝓝 0) :=
    tlim hl (continuousAt_log one_ne_zero) (by norm_num)
  have lm : Tendsto (fun u : ℝ => log (1 + u)) _ (𝓝 (log 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have qD := tendsto_Li_comp (k := 2) (by norm_num) mh gD sD
  have qB := tendsto_Li_comp (k := 2) (by norm_num) m0 gB sB
  have R1 := qD.mul (((l0.const_mul (-(142 / 9))).add (lm.const_mul (88 / 9))).add_const
    (20 / 3 * log 2))
  have R2 := qB.mul (((l0.const_mul (-(160 / 9))).add (lm.const_mul (176 / 9))).sub_const
    (20 / 3 * log 2))
  have Y1 := tendsto_log_mul_log_one_sub_one.mul (((l0.const_mul (-(160 / 9))).add
    (lm.const_mul 16)).sub_const (20 / 3 * log 2))
  have Y2 : Tendsto (fun x : ℝ => 32 / 9 * (log (1 + x) - log 2) ^ 2 * log (1 - x)) (𝓝[<] 1)
      (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 4) ?_
    filter_upwards [ev] with x hx
    obtain ⟨h0, h1⟩ := hx
    have hB := abs_log_one_add_div_two_le h0.le h1.le
    rw [log_div (by linarith) two_ne_zero] at hB
    rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 32 / 9)]
    have : |log (1 + x) - log 2| ^ 2 ≤ (1 - x) * 1 := by
      rw [sq]
      exact mul_le_mul hB (hB.trans (by linarith)) (abs_nonneg _) (by linarith)
    nlinarith
  have Y3 := ((((((((l0.pow 2).mul lm).const_mul (4 / 9)).sub
    ((l0.mul (lm.pow 2)).const_mul (43 / 9))).add ((lm.pow 3).const_mul (20 / 27))).sub
    ((lm.pow 2).const_mul (10 / 3 * log 2))).add (lm.const_mul (92 / 9 * log 2 ^ 2))).add
    (l0.const_mul (160 / 9 * (π ^ 2 / 6)))).sub (lm.const_mul (176 / 9 * (π ^ 2 / 6)))
  have P := ((((((((T1.const_mul (-(140 / 9))).sub (T2.const_mul (92 / 9))).add
    (T3.const_mul (20 / 3))).add (T4.const_mul (8 / 9))).sub (T5.const_mul (4 / 9))).sub
    (T6.const_mul (32 / 9))).add (T7.const_mul (16 / 9))).sub (T8.const_mul 6))
  have H := ((((P.add R1).add R2).add Y1).add Y2).add Y3
  have H2 : Tendsto setAG3 (𝓝[<] 1) (𝓝 _) := H.congr fun u => by
    unfold setAG3
    ring
  convert H2 using 2
  simp only [Li_zero, log_one, log_half, Li_three_one, Li_two_one_half,
    Li_three_one_half, mul_zero, zero_mul, sub_zero,
    show Li 3 (-1) = -(3 / 4) * zeta3 from Li₃_neg_one]
  ring

end QED.Chain
