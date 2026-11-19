/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
import QED.Polylog.AlphabetPM
import QED.Polylog.DilogPM
import QED.Polylog.LiCalculus
import QED.Polylog.LiLimits
import QED.Polylog.ExtraIntegrals
import QED.Polylog.Reflection
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (a): the weight-four part

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

The weight-four part of the set (a) integrand `QED.Chain.setAJ` is `-(8/3) Φ ψ'`, with
`Φ = log u (2 log (1 - u) + log (1 + u)) + 4 Li 2 u + 2 Li 2 (-u)` and
`ψ' = log u/(1 + u) + log (1 + u)/u - 2 log (1 + u)/(1 + u)` (the derivative of
`ψ = log (1 + u) (log u - log (1 + u))`). Up to the remainder
`R = (log u log² (1 - u²) - log u log² (1 - u))/u`, whose integral is `-(3/4) ∫₀¹ log y log²(1-y)/y`
(`QED.Polylog.intervalIntegrable_and_integral_log_mul_log_one_sub_sq_div`), it has a classical
antiderivative `G₄` built from the `Li₃`-free combinations `P(f) = Li 4 f - log f · Li 3 f` at the
arguments `-u, 1 - u, 1/(1+u), u/(1+u), -t, (1+u)/2, 2u/(1+u), u², 1 - u², t²` (`t = (1-u)/(1+u)`),
two `log 2 · Li 3` terms, dilogarithms times two logarithms, and a quartic polynomial in
logarithms. Its derivative is checked with the dilogarithm identities of `QED.Polylog.DilogPM`.

## Main statements

* `QED.Chain.setAG4`: the antiderivative, written so that every group has a limit at `0⁺` and
  at `1⁻`.
* `QED.Chain.hasDerivAt_setAG4`: `G₄' = Φ ψ' - R` on `(0, 1)`.
* `QED.Chain.tendsto_setAG4_zero`, `QED.Chain.tendsto_setAG4_one`: `G₄(0⁺) = 7π⁴/120 + 4 Li 4 (1/2)`
  and `G₄(1⁻) = 23π⁴/360 + π² log² 2/6 - log⁴ 2/6`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.Chain

/-- `Φ(u) = log u (2 log (1 - u) + log (1 + u)) + 4 Li 2 u + 2 Li 2 (-u)`. -/
noncomputable def setAPhi (u : ℝ) : ℝ :=
  log u * (2 * log (1 - u) + log (1 + u)) + 4 * Li 2 u + 2 * Li 2 (-u)

/-- `ψ'(u) = log u/(1 + u) + log (1 + u)/u - 2 log (1 + u)/(1 + u)`. -/
noncomputable def setAPsiD (u : ℝ) : ℝ :=
  log u / (1 + u) + log (1 + u) / u - 2 * log (1 + u) / (1 + u)

/-- The non-classical remainder `R(u) = log u log² (1 - u²)/u - log u log² (1 - u)/u`. -/
noncomputable def setARem (u : ℝ) : ℝ :=
  log u * (log (1 - u) + log (1 + u)) ^ 2 / u - log u * log (1 - u) ^ 2 / u

/-- The weight-four antiderivative `G₄` (with `t = (1-u)/(1+u)`). -/
noncomputable def setAG4 (u : ℝ) : ℝ :=
  2 * (Li 4 (-u) - log (-u) * Li 3 (-u)) +
    4 * (Li 4 (1 - u) - log (1 - u) * Li 3 (1 - u)) +
    6 * (Li 4 (1 / (1 + u)) - log (1 / (1 + u)) * Li 3 (1 / (1 + u))) -
    6 * (Li 4 (u / (1 + u)) - log (u / (1 + u)) * Li 3 (u / (1 + u))) +
    4 * (Li 4 (-((1 - u) / (1 + u))) -
      log (-((1 - u) / (1 + u))) * Li 3 (-((1 - u) / (1 + u)))) +
    4 * (Li 4 ((1 + u) / 2) - log ((1 + u) / 2) * Li 3 ((1 + u) / 2)) -
    4 * log 2 * Li 3 ((1 + u) / 2) +
    4 * (Li 4 (2 * u / (1 + u)) - log (2 * u / (1 + u)) * Li 3 (2 * u / (1 + u))) +
    4 * log 2 * Li 3 (2 * u / (1 + u)) -
    (Li 4 (u ^ 2) - log (u ^ 2) * Li 3 (u ^ 2)) / 2 -
    (Li 4 (1 - u ^ 2) - log (1 - u ^ 2) * Li 3 (1 - u ^ 2)) -
    (Li 4 (((1 - u) / (1 + u)) ^ 2) -
      log (((1 - u) / (1 + u)) ^ 2) * Li 3 (((1 - u) / (1 + u)) ^ 2)) / 4 +
    log (1 - u) * log (1 + u) *
      (-4 * (Li 2 (u / (1 + u)) - Li 2 (1 / 2)) - 2 * (log (1 + u) ^ 2 - log 2 ^ 2)) -
    2 * Li 2 (u / (1 + u)) * log (1 + u) ^ 2 +
    2 * log u ^ 2 * (Li 2 ((1 - u) / 2) - Li 2 (1 / 2)) -
    4 * Li 2 ((1 - u) / 2) * log u * log (1 + u) +
    (2 * log u ^ 2 * log (1 - u) * log (1 + u) - 2 * log u ^ 2 * log (1 - u) * log 2 +
      log u ^ 2 * log (1 + u) ^ 2 / 2 + 4 * log u * log (1 - u) * log (1 + u) * log 2 +
      log u * log (1 + u) ^ 3 - 2 * log u * log (1 + u) * log 2 ^ 2 -
      3 / 2 * log (1 + u) ^ 4 + 4 / 3 * log (1 + u) ^ 3 * log 2 -
      log (1 + u) ^ 2 * log 2 ^ 2 + π ^ 2 / 3 * log u * log (1 + u) +
      π ^ 2 / 3 * log (1 + u) ^ 2)

/-- **The weight-four antiderivative**: `G₄' = Φ ψ' - R` on `(0, 1)`. -/
theorem hasDerivAt_setAG4 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt setAG4 (setAPhi u * setAPsiD u - setARem u) u := by
  obtain ⟨h0, h1⟩ := hu
  have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  obtain ⟨dA, aA, nA, lA, gA, -⟩ := PM.data_neg h0 h1
  obtain ⟨dB, aB, nB, lB, gB, -⟩ := PM.data_oneSub h0 h1
  obtain ⟨dC, aC, nC, lC, gC, -⟩ := PM.data_invOneAdd h0 h1
  obtain ⟨dD, aD, nD, lD, gD, gD1⟩ := PM.data_divOneAdd h0 h1
  obtain ⟨dE, aE, nE, lE, gE, -⟩ := PM.data_negKsT h0 h1
  obtain ⟨dF, aF, nF, lF, gF, -⟩ := PM.data_halfOneAdd h0 h1
  obtain ⟨dG, aG, nG, lG, gG, -⟩ := PM.data_twoMulDiv h0 h1
  obtain ⟨dH, aH, nH, lH, gH, -⟩ := PM.data_sq h0 h1
  obtain ⟨dI, aI, nI, lI, gI, -⟩ := PM.data_oneSubSq h0 h1
  obtain ⟨dJ, aJ, nJ, lJ, gJ, -⟩ := PM.data_ksTSq h0 h1
  obtain ⟨dK, aK, nK, lK, gK, gK1⟩ := PM.data_halfOneSub h0 h1
  obtain ⟨di, -, ni, li, -, -⟩ := PM.data_id h0 h1
  have pA := hasDerivAt_Li_four_sub_of dA aA nA lA gA rfl
  have pB := hasDerivAt_Li_four_sub_of dB aB nB lB gB (Li_two_one_sub' hu)
  have pC := hasDerivAt_Li_four_sub_of dC aC nC lC gC (Li_two_inv_one_add hu)
  have pD := hasDerivAt_Li_four_sub_of dD aD nD lD gD (Li_two_div_one_add hu)
  have pE := hasDerivAt_Li_four_sub_of dE aE nE lE gE (Li_two_neg_ksT hu)
  have pF := hasDerivAt_Li_four_sub_of dF aF nF lF gF (Li_two_one_add_div_two hu)
  have tF := hasDerivAt_Li_three_of dF aF nF lF (Li_two_one_add_div_two hu)
  have pG := hasDerivAt_Li_four_sub_of dG aG nG lG gG (Li_two_two_mul_div hu)
  have tG := hasDerivAt_Li_three_of dG aG nG lG (Li_two_two_mul_div hu)
  have pH := hasDerivAt_Li_four_sub_of dH aH nH lH gH (Li_two_sq' hu)
  have pI := hasDerivAt_Li_four_sub_of dI aI nI lI gI (Li_two_one_sub_sq hu)
  have pJ := hasDerivAt_Li_four_sub_of dJ aJ nJ lJ gJ (Li_two_ksT_sq hu)
  have qD := hasDerivAt_Li_two_of dD aD nD lD gD1
  have qK := hasDerivAt_Li_two_of dK aK nK lK gK1
  have e0 := hasDerivAt_log_of di ni li
  have e1 := hasDerivAt_log_of dB nB lB
  have em : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + u)) u := by
    have := ((hasDerivAt_id' u).const_add 1).log (by linarith)
    simpa [one_div] using this
  have r1 := (e1.mul em).mul (((qD.sub_const (Li 2 (1 / 2))).const_mul (-4)).sub
    (((em.pow 2).sub_const (log 2 ^ 2)).const_mul 2))
  have r2 := ((qD.const_mul 2).mul (em.pow 2))
  have r3 := ((e0.pow 2).const_mul 2).mul (qK.sub_const (Li 2 (1 / 2)))
  have r4 := ((qK.const_mul 4).mul e0).mul em
  have s1 := (((e0.pow 2).const_mul 2).mul e1).mul em
  have s2 := (((e0.pow 2).const_mul 2).mul e1).mul_const (log 2)
  have s3 := ((e0.pow 2).mul (em.pow 2)).div_const 2
  have s4 := (((e0.const_mul 4).mul e1).mul em).mul_const (log 2)
  have s5 := e0.mul (em.pow 3)
  have s6 := ((e0.const_mul 2).mul em).mul_const (log 2 ^ 2)
  have s7 := (em.pow 4).const_mul (3 / 2)
  have s8 := ((em.pow 3).const_mul (4 / 3)).mul_const (log 2)
  have s9 := (em.pow 2).mul_const (log 2 ^ 2)
  have s10 := (e0.const_mul (π ^ 2 / 3)).mul em
  have s11 := (em.pow 2).const_mul (π ^ 2 / 3)
  have S := (((((((((s1.sub s2).add s3).add s4).add s5).sub s6).sub s7).add s8).sub s9).add
    s10).add s11
  have P := ((((((((pA.const_mul 2).add (pB.const_mul 4)).add (pC.const_mul 6)).sub
    (pD.const_mul 6)).add (pE.const_mul 4)).add (pF.const_mul 4)).sub
    (tF.const_mul (4 * log 2))).add (pG.const_mul 4)).add (tG.const_mul (4 * log 2))
  have P' := ((P.sub (pH.div_const 2)).sub pI).sub (pJ.div_const 4)
  have h := ((((P'.add r1).sub r2).add r3).sub r4).add S
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
  rw [Li_two_div_one_add hu, show Li 2 (1 / 2) = π ^ 2 / 12 - log 2 ^ 2 / 2 from Li₂_one_half]
  unfold setAPhi setAPsiD setARem
  have hm : 1 - u ≠ 0 := by linarith
  have hp : 1 + u ≠ 0 := by linarith
  field_simp
  ring

private theorem tlim {l : Filter ℝ} {x₀ : ℝ} (hl : l ≤ 𝓝 x₀) {g : ℝ → ℝ} {a : ℝ}
    (hg : ContinuousAt g x₀) (h : g x₀ = a) : Tendsto g l (𝓝 a) :=
  h ▸ hg.tendsto.mono_left hl

private theorem mem_Icc_of_abs {x : ℝ} (h : |x| < 1) : x ∈ Icc (-1 : ℝ) 1 :=
  mem_Icc.2 (abs_le.1 h.le)

/-- `G₄(0⁺) = 7π⁴/120 + 4 Li 4 (1/2)`. -/
theorem tendsto_setAG4_zero :
    Tendsto setAG4 (𝓝[>] 0) (𝓝 (7 * π ^ 4 / 120 + 4 * Li 4 (1 / 2))) := by
  have ev : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have m1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have mm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have mh : (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have m0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sA := ev.mono fun u hu => mem_Icc_of_abs (PM.data_neg hu.1 hu.2).2.1
  have sB := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSub hu.1 hu.2).2.1
  have sC := ev.mono fun u hu => mem_Icc_of_abs (PM.data_invOneAdd hu.1 hu.2).2.1
  have sD := ev.mono fun u hu => mem_Icc_of_abs (PM.data_divOneAdd hu.1 hu.2).2.1
  have sE := ev.mono fun u hu => mem_Icc_of_abs (PM.data_negKsT hu.1 hu.2).2.1
  have sF := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneAdd hu.1 hu.2).2.1
  have sG := ev.mono fun u hu => mem_Icc_of_abs (PM.data_twoMulDiv hu.1 hu.2).2.1
  have sH := ev.mono fun u hu => mem_Icc_of_abs (PM.data_sq hu.1 hu.2).2.1
  have sI := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSubSq hu.1 hu.2).2.1
  have sJ := ev.mono fun u hu => mem_Icc_of_abs (PM.data_ksTSq hu.1 hu.2).2.1
  have sK := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneSub hu.1 hu.2).2.1
  have gA : Tendsto (fun u : ℝ => -u) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gB : Tendsto (fun u : ℝ => 1 - u) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gC : Tendsto (fun u : ℝ => 1 / (1 + u)) _ (𝓝 1) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gD : Tendsto (fun u : ℝ => u / (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gE : Tendsto (fun u : ℝ => -((1 - u) / (1 + u))) _ (𝓝 (-1)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gF : Tendsto (fun u : ℝ => (1 + u) / 2) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop) (by norm_num)
  have gG : Tendsto (fun u : ℝ => 2 * u / (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gH : Tendsto (fun u : ℝ => u ^ 2) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gI : Tendsto (fun u : ℝ => 1 - u ^ 2) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gJ : Tendsto (fun u : ℝ => ((1 - u) / (1 + u)) ^ 2) _ (𝓝 1) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gK : Tendsto (fun u : ℝ => (1 - u) / 2) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop) (by norm_num)
  have T1 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
    gA sA
  have T2 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) m1
    one_ne_zero gB sB
  have T3 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) m1
    one_ne_zero gC sC
  have T4 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
    gD sD
  have T5 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) mm
    (by norm_num) gE sE
  have T6 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) mh
    (by norm_num) gF sF
  have T7 := tendsto_Li_comp (k := 3) (by norm_num) mh gF sF
  have T8 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
    gG sG
  have T9 := tendsto_Li_comp (k := 3) (by norm_num) m0 gG sG
  have T10 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
    gH sH
  have T11 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) m1
    one_ne_zero gI sI
  have T12 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) m1
    one_ne_zero gJ sJ
  have lb : Tendsto (fun u : ℝ => log (1 - u)) (𝓝[>] 0) (𝓝 0) := tendsto_log_one_sub_zero
  have lm : Tendsto (fun u : ℝ => log (1 + u)) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have qD := tendsto_Li_comp (k := 2) (by norm_num) m0 gD sD
  have qK := tendsto_Li_comp (k := 2) (by norm_num) mh gK sK
  have R1 := (lb.mul lm).mul (((qD.sub_const (Li 2 (1 / 2))).const_mul (-4)).sub
    (((lm.pow 2).sub_const (log 2 ^ 2)).const_mul 2))
  have R2 := (qD.const_mul 2).mul (lm.pow 2)
  have R3 : Tendsto (fun u : ℝ => 2 * (Li 2 ((1 - u) / 2) - Li 2 (1 / 2)) * log u ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_mul_log_sq_of_abs_le (C := 2) ?_
    filter_upwards [ev] with u hu
    obtain ⟨h0, h1⟩ := hu
    have := abs_Li_sub_le (k := 2) (by norm_num) (x := (1 - u) / 2) (y := 1 / 2)
      (by rw [abs_le]; constructor <;> linarith) (by norm_num [abs_of_pos])
    rw [show (1 - u) / 2 - 1 / 2 = -(u / 2) by ring, abs_neg,
      abs_of_pos (show 0 < u / 2 by linarith)] at this
    rw [abs_mul, abs_two]
    linarith
  have R4 := (qK.const_mul 4).mul tendsto_log_mul_log_one_add_zero
  have X1 := tendsto_log_one_sub_mul_log_sq.mul ((lm.const_mul 2).sub_const (2 * log 2))
  have X2 := tendsto_log_one_add_mul_log_sq.mul (lm.div_const 2)
  have X3 := tendsto_log_mul_log_one_add_zero.mul ((((lb.const_mul (4 * log 2)).add
    (lm.pow 2)).sub_const (2 * log 2 ^ 2)).add_const (π ^ 2 / 3))
  have X4 := ((((lm.pow 4).const_mul (-(3 / 2))).add ((lm.pow 3).const_mul (4 / 3 * log 2))).sub
    ((lm.pow 2).mul_const (log 2 ^ 2))).add ((lm.pow 2).const_mul (π ^ 2 / 3))
  have P := ((((((T1.const_mul 2).add (T2.const_mul 4)).add (T3.const_mul 6)).sub
    (T4.const_mul 6)).add (T5.const_mul 4)).add (T6.const_mul 4)).sub (T7.const_mul (4 * log 2))
  have P' := ((((P.add (T8.const_mul 4)).add (T9.const_mul (4 * log 2))).sub
    (T10.div_const 2)).sub T11).sub (T12.div_const 4)
  have H := (((((((P'.add R1).sub R2).add R3).sub R4).add X1).add X2).add X3).add X4
  have H2 : Tendsto setAG4 (𝓝[>] 0) (𝓝 _) := H.congr fun u => by
    unfold setAG4
    ring
  convert H2 using 2
  simp only [Li_four_one, Li_four_neg_one, Li_zero, log_one, Real.log_neg_eq_log, one_div,
    Real.log_inv]
  ring

/-- `G₄(1⁻) = 23π⁴/360 + π² log² 2/6 - log⁴ 2/6`. -/
theorem tendsto_setAG4_one :
    Tendsto setAG4 (𝓝[<] 1)
      (𝓝 (23 * π ^ 4 / 360 + π ^ 2 * log 2 ^ 2 / 6 - log 2 ^ 4 / 6)) := by
  have ev : ∀ᶠ u in 𝓝[<] (1 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
  have hl : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have m1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have mm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have mh : (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have m0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have sA := ev.mono fun u hu => mem_Icc_of_abs (PM.data_neg hu.1 hu.2).2.1
  have sB := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSub hu.1 hu.2).2.1
  have sC := ev.mono fun u hu => mem_Icc_of_abs (PM.data_invOneAdd hu.1 hu.2).2.1
  have sD := ev.mono fun u hu => mem_Icc_of_abs (PM.data_divOneAdd hu.1 hu.2).2.1
  have sE := ev.mono fun u hu => mem_Icc_of_abs (PM.data_negKsT hu.1 hu.2).2.1
  have sF := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneAdd hu.1 hu.2).2.1
  have sG := ev.mono fun u hu => mem_Icc_of_abs (PM.data_twoMulDiv hu.1 hu.2).2.1
  have sH := ev.mono fun u hu => mem_Icc_of_abs (PM.data_sq hu.1 hu.2).2.1
  have sI := ev.mono fun u hu => mem_Icc_of_abs (PM.data_oneSubSq hu.1 hu.2).2.1
  have sJ := ev.mono fun u hu => mem_Icc_of_abs (PM.data_ksTSq hu.1 hu.2).2.1
  have sK := ev.mono fun u hu => mem_Icc_of_abs (PM.data_halfOneSub hu.1 hu.2).2.1
  have gA : Tendsto (fun u : ℝ => -u) _ (𝓝 (-1)) := tlim hl (by fun_prop) (by norm_num)
  have gB : Tendsto (fun u : ℝ => 1 - u) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gC : Tendsto (fun u : ℝ => 1 / (1 + u)) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gD : Tendsto (fun u : ℝ => u / (1 + u)) _ (𝓝 (1 / 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gE : Tendsto (fun u : ℝ => -((1 - u) / (1 + u))) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gF : Tendsto (fun u : ℝ => (1 + u) / 2) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gG : Tendsto (fun u : ℝ => 2 * u / (1 + u)) _ (𝓝 1) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gH : Tendsto (fun u : ℝ => u ^ 2) _ (𝓝 1) := tlim hl (by fun_prop) (by norm_num)
  have gI : Tendsto (fun u : ℝ => 1 - u ^ 2) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have gJ : Tendsto (fun u : ℝ => ((1 - u) / (1 + u)) ^ 2) _ (𝓝 0) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have gK : Tendsto (fun u : ℝ => (1 - u) / 2) _ (𝓝 0) := tlim hl (by fun_prop) (by norm_num)
  have T1 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) mm
    (by norm_num) gA sA
  have T2 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
    gB sB
  have T3 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) mh
    (by norm_num) gC sC
  have T4 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) mh
    (by norm_num) gD sD
  have T5 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
    gE sE
  have T6 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) m1
    one_ne_zero gF sF
  have T7 := tendsto_Li_comp (k := 3) (by norm_num) m1 gF sF
  have T8 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) m1
    one_ne_zero gG sG
  have T9 := tendsto_Li_comp (k := 3) (by norm_num) m1 gG sG
  have T10 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) m1
    one_ne_zero gH sH
  have T11 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
    gI sI
  have T12 := tendsto_Li_sub_log_mul_Li_comp_zero (k := 4) (j := 3) (by norm_num) (by norm_num)
    gJ sJ
  have l0 : Tendsto (fun u : ℝ => log u) _ (𝓝 0) :=
    tlim hl (continuousAt_log one_ne_zero) (by norm_num)
  have lm : Tendsto (fun u : ℝ => log (1 + u)) _ (𝓝 (log 2)) :=
    tlim hl (by fun_prop (disch := norm_num)) (by norm_num)
  have qD := tendsto_Li_comp (k := 2) (by norm_num) mh gD sD
  have qK := tendsto_Li_comp (k := 2) (by norm_num) m0 gK sK
  have R1 : Tendsto (fun x : ℝ => log (1 + x) * (-4 * (Li 2 (x / (1 + x)) - Li 2 (1 / 2)) -
      2 * (log (1 + x) ^ 2 - log 2 ^ 2)) * log (1 - x)) (𝓝[<] 1) (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 8) ?_
    filter_upwards [ev] with x hx
    obtain ⟨h0, h1⟩ := hx
    have hA := abs_Li_sub_le (k := 2) (by norm_num) (x := x / (1 + x)) (y := 1 / 2)
      (by
        rw [abs_le]
        constructor
        · have : 0 ≤ x / (1 + x) := by positivity
          linarith
        · rw [div_le_iff₀ (by linarith)]
          linarith) (by norm_num [abs_of_pos])
    rw [show x / (1 + x) - 1 / 2 = -((1 - x) / (2 * (1 + x))) by field_simp; ring, abs_neg,
      abs_of_nonneg (show 0 ≤ (1 - x) / (2 * (1 + x)) by apply div_nonneg <;> linarith)] at hA
    have hq : (1 - x) / (2 * (1 + x)) ≤ (1 - x) / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    have hB := abs_log_one_add_div_two_le h0.le h1.le
    rw [log_div (by linarith) two_ne_zero] at hB
    have hL0 : 0 ≤ log (1 + x) := log_nonneg (by linarith)
    have hL1 : log (1 + x) ≤ log 2 := log_le_log (by linarith) (by linarith)
    have hl2 : log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos two_pos (by norm_num); linarith
    set A := Li 2 (x / (1 + x)) - Li 2 (1 / 2)
    set L := log (1 + x)
    rw [abs_le] at hA hB
    have hS : 0 ≤ L + log 2 := by linarith
    have hI1 : -4 * A - 2 * (L ^ 2 - log 2 ^ 2) ≤ 8 * (1 - x) := by
      nlinarith [mul_le_mul_of_nonneg_right (show -(L - log 2) ≤ 1 - x by linarith) hS]
    have hI2 : -4 * (1 - x) ≤ -4 * A - 2 * (L ^ 2 - log 2 ^ 2) := by
      nlinarith [mul_nonneg (show 0 ≤ -(L - log 2) by linarith) hS]
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hI2 hL0, mul_nonneg (show 0 ≤ 1 - L by linarith)
        (show 0 ≤ 1 - x by linarith)]
    · nlinarith [mul_le_mul_of_nonneg_left hI1 hL0, mul_nonneg (show 0 ≤ 1 - L by linarith)
        (show 0 ≤ 1 - x by linarith)]
  have R2 := (qD.const_mul 2).mul (lm.pow 2)
  have R3 := ((l0.pow 2).const_mul 2).mul (qK.sub_const (Li 2 (1 / 2)))
  have R4 := ((qK.const_mul 4).mul l0).mul lm
  have Y1 := tendsto_log_mul_log_one_sub_one.mul ((((l0.const_mul 2).mul lm).sub
    (l0.const_mul (2 * log 2))).add (lm.const_mul (4 * log 2)))
  have Y2 := ((((((((((l0.pow 2).mul (lm.pow 2)).div_const 2).add (l0.mul (lm.pow 3))).sub
    ((l0.mul lm).const_mul (2 * log 2 ^ 2))).add ((lm.pow 4).const_mul (-(3 / 2)))).add
    ((lm.pow 3).const_mul (4 / 3 * log 2))).sub ((lm.pow 2).const_mul (log 2 ^ 2))).add
    ((l0.mul lm).const_mul (π ^ 2 / 3))).add ((lm.pow 2).const_mul (π ^ 2 / 3)))
  have P := ((((((T1.const_mul 2).add (T2.const_mul 4)).add (T3.const_mul 6)).sub
    (T4.const_mul 6)).add (T5.const_mul 4)).add (T6.const_mul 4)).sub (T7.const_mul (4 * log 2))
  have P' := ((((P.add (T8.const_mul 4)).add (T9.const_mul (4 * log 2))).sub
    (T10.div_const 2)).sub T11).sub (T12.div_const 4)
  have H := ((((((P'.add R1).sub R2).add R3).sub R4).add Y1).add Y2)
  have H2 : Tendsto setAG4 (𝓝[<] 1) (𝓝 _) := H.congr fun u => by
    unfold setAG4
    ring
  convert H2 using 2
  simp only [Li_four_one, Li_four_neg_one, Li_zero, log_one, Real.log_neg_eq_log,
    show Li 2 (1 / 2) = π ^ 2 / 12 - log 2 ^ 2 / 2 from Li₂_one_half]
  ring

end QED.Chain
