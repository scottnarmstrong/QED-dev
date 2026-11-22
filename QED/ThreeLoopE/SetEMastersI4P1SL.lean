/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4P1SSwap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (e), master I₄: the elementary `l`-integral at fixed `t`

In the variables `(t, l)` of `QED.ThreeLoopE.SetEMastersI4P1SSwap` the density is
`i4STDens l t = P (C + 2 log N - log (l - t)) / N²` (`QED.ThreeLoopE.i4STDens_eq`), with
`N = λ c + k l` and `P`, `C` depending on `t` only:

  `P = λ² / ((λ + t)(λ c + t))`,
  `C = log (λ c + t) - 2 log λ + 4 + 3 λ² log (λ² / (λ + t)) / (λ c + t)`.

With `x = l - t` and `N_t = λ c + k t = N - k x`, a primitive in `l` is

  `F = P (-C / (k N) - 2 (log N + 1) / (k N) - x log x / (N_t N) + log N / (k N_t))`

(`QED.ThreeLoopE.i4SLF`, `QED.ThreeLoopE.i4SLF_hasDerivAt`); it is continuous at `x = 0` and
tends to `P log k / (k N_t)` as `l → ∞` (`QED.ThreeLoopE.i4SLF_tendsto`).

The section condition `i4STmin l < t` is linear in `l`: it reads `α l < β` with
`α = k (λ (a - c) - k t)` and `β = k λ (a + c) t + λ² c²` (`QED.ThreeLoopE.mem_i4SLSec`).
Hence the section is empty for `β ≤ 0`, the interval `(max 0 t, β / α)` for `α > 0 < β`, and
the half-line `(max 0 t, ∞)` for `α ≤ 0`, and the `l`-integral is `QED.ThreeLoopE.i4SB`
(`QED.ThreeLoopE.i4SL_integral`).

## Main definitions

* `QED.ThreeLoopE.i4SP`, `QED.ThreeLoopE.i4SC`, `QED.ThreeLoopE.i4SNt`,
  `QED.ThreeLoopE.i4SAl`, `QED.ThreeLoopE.i4SBe`, `QED.ThreeLoopE.i4SLF`,
  `QED.ThreeLoopE.i4SB`.

## Main results

* `QED.ThreeLoopE.i4SL_integral`.
* `QED.ThreeLoopE.i4P1_B`: `P'(0)` as an integral of `i4SB`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopE

/-- The prefactor `P = λ² / ((λ + t)(λ c + t))`. -/
noncomputable def i4SP (a b c t : ℝ) : ℝ := (a + b) ^ 2 / ((a + b + t) * ((a + b) * c + t))

/-- The `l`-independent part `C` of the bracket. -/
noncomputable def i4SC (a b c t : ℝ) : ℝ :=
  log ((a + b) * c + t) - 2 * log (a + b) + 4 +
    3 * (a + b) ^ 2 * log ((a + b) ^ 2 / (a + b + t)) / ((a + b) * c + t)

/-- `N_t = λ c + k t`, the value of `N` at `l = t`. -/
def i4SNt (a b c t : ℝ) : ℝ := (a + b) * c + (b + c) * t

/-- `α = k (λ (a - c) - k t)`. -/
def i4SAl (a b c t : ℝ) : ℝ := (b + c) * ((a + b) * (a - c) - (b + c) * t)

/-- `β = k λ (a + c) t + λ² c²`. -/
def i4SBe (a b c t : ℝ) : ℝ := (b + c) * (a + b) * (a + c) * t + (a + b) ^ 2 * c ^ 2

/-- The primitive `F` in `l` of `i4STDens · t`. -/
noncomputable def i4SLF (a b c t l : ℝ) : ℝ :=
  i4SP a b c t * (-(i4SC a b c t / ((b + c) * i4SN a b c l)) -
    2 * (log (i4SN a b c l) + 1) / ((b + c) * i4SN a b c l) -
    (l - t) * log (l - t) / (i4SNt a b c t * i4SN a b c l) +
    log (i4SN a b c l) / ((b + c) * i4SNt a b c t))

/-- The value of the `l`-integral over the section `i4SLSec t`. -/
noncomputable def i4SB (a b c t : ℝ) : ℝ :=
  if i4SBe a b c t ≤ 0 then 0 else
    (if 0 < i4SAl a b c t then i4SLF a b c t (i4SBe a b c t / i4SAl a b c t)
      else i4SP a b c t * log (b + c) / ((b + c) * i4SNt a b c t)) -
    i4SLF a b c t (max 0 t)

theorem i4STDens_eq (a b c l t : ℝ) :
    i4STDens a b c l t =
      i4SP a b c t * (i4SC a b c t + 2 * log (i4SN a b c l) - log (l - t)) /
        i4SN a b c l ^ 2 := by
  unfold i4STDens i4SP i4SC
  rw [show i4SN a b c l ^ 2 * (a + b + t) * ((a + b) * c + t) =
    ((a + b + t) * ((a + b) * c + t)) * i4SN a b c l ^ 2 by ring, ← div_div]
  ring

theorem i4SN_pos_of_nonneg {a b c l : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hl : 0 ≤ l) : 0 < i4SN a b c l := by
  unfold i4SN; positivity

/-- `α ≤ 0` forces `β > 0`. -/
theorem i4SBe_pos_of_Al {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : i4SAl a b c t ≤ 0) : 0 < i4SBe a b c t := by
  unfold i4SAl at h
  have h1 : (a + b) * (a - c) ≤ (b + c) * t := by
    by_contra h'
    push Not at h'
    have : 0 < (b + c) * ((a + b) * (a - c) - (b + c) * t) := mul_pos (by positivity) (by linarith)
    linarith
  have e : i4SBe a b c t = (a + b) * (a + c) * ((b + c) * t - (a + b) * (a - c)) +
      (a + b) ^ 2 * a ^ 2 := by unfold i4SBe; ring
  rw [e]
  have : 0 ≤ (a + b) * (a + c) * ((b + c) * t - (a + b) * (a - c)) :=
    mul_nonneg (by positivity) (by linarith)
  have : 0 < (a + b) ^ 2 * a ^ 2 := by positivity
  linarith

/-- `β > 0` forces `N_t > 0`. -/
theorem i4SNt_pos {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 0 < i4SBe a b c t) : 0 < i4SNt a b c t := by
  have e : (a + b) * (a + c) * i4SNt a b c t = i4SBe a b c t + (a + b) ^ 2 * a * c := by
    unfold i4SNt i4SBe; ring
  have : 0 < (a + b) * (a + c) * i4SNt a b c t := by
    rw [e]; have : 0 < (a + b) ^ 2 * a * c := by positivity
    linarith
  exact pos_of_mul_pos_right this (by positivity)

/-- **The section is linear**: `l ∈ i4SLSec t ↔ 0 < l ∧ t < l ∧ α l < β`. -/
theorem mem_i4SLSec {a b c t l : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c = 1) :
    l ∈ i4SLSec a b c t ↔ 0 < l ∧ t < l ∧ i4SAl a b c t * l < i4SBe a b c t := by
  have key : i4SD a b c l * (l - t) - i4SN a b c l ^ 2 =
      i4SAl a b c t * l - i4SBe a b c t := by
    obtain rfl : c = 1 - a - b := by linarith
    unfold i4SD i4SN i4SAl i4SBe; ring
  simp only [i4SLSec, mem_ofPred_eq]
  constructor
  · rintro ⟨hl, h1, h2⟩
    have hD := i4SD_pos ha hb hc hl
    refine ⟨hl, h2, ?_⟩
    have : l - t < i4SN a b c l ^ 2 / i4SD a b c l := by unfold i4STmin at h1; linarith
    rw [lt_div_iff₀ hD] at this
    linarith
  · rintro ⟨hl, h2, h1⟩
    have hD := i4SD_pos ha hb hc hl
    refine ⟨hl, ?_, h2⟩
    have : l - t < i4SN a b c l ^ 2 / i4SD a b c l := by
      rw [lt_div_iff₀ hD]; linarith
    unfold i4STmin; linarith

theorem i4SLF_hasDerivAt {a b c t l : ℝ} (hk : 0 < b + c) (hN : 0 < i4SN a b c l)
    (hNt : i4SNt a b c t ≠ 0) (hx : t < l) :
    HasDerivAt (i4SLF a b c t) (i4STDens a b c l t) l := by
  have hx0 : l - t ≠ 0 := (sub_pos.2 hx).ne'
  have hkN : (b + c) * i4SN a b c l ≠ 0 := mul_ne_zero hk.ne' hN.ne'
  have hNtN : i4SNt a b c t * i4SN a b c l ≠ 0 := mul_ne_zero hNt hN.ne'
  have hNd : HasDerivAt (fun l => i4SN a b c l) (b + c) l := by
    unfold i4SN
    simpa using ((hasDerivAt_id l).const_mul (b + c)).const_add ((a + b) * c)
  have hkNd : HasDerivAt (fun l => (b + c) * i4SN a b c l) ((b + c) * (b + c)) l :=
    hNd.const_mul (b + c)
  have hNtNd : HasDerivAt (fun l => i4SNt a b c t * i4SN a b c l)
      (i4SNt a b c t * (b + c)) l := hNd.const_mul _
  have hlogN := hNd.log hN.ne'
  have hxd : HasDerivAt (fun l => l - t) 1 l := (hasDerivAt_id l).sub_const t
  have hxl := hxd.mul (hxd.log hx0)
  have T1 := (hasDerivAt_const l (i4SC a b c t)).div hkNd hkN
  have T2 := ((hlogN.add_const 1).const_mul 2).div hkNd hkN
  have T3 := hxl.div hNtNd hNtN
  have T4 := hlogN.div_const ((b + c) * i4SNt a b c t)
  have h := (((T1.neg.sub T2).sub T3).add T4).const_mul (i4SP a b c t)
  convert h using 1
  · funext y
    simp only [i4SLF, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, Pi.mul_apply]
  · rw [i4STDens_eq]
    simp only [Pi.mul_apply]
    field_simp
    unfold i4SN i4SNt
    ring

theorem i4SLF_continuousAt {a b c t l : ℝ} (hN : 0 < i4SN a b c l) :
    ContinuousAt (i4SLF a b c t) l := by
  have hxl : Continuous fun l : ℝ => (l - t) * log (l - t) :=
    continuous_mul_log.comp (by fun_prop)
  have hNc : Continuous fun l => i4SN a b c l := by unfold i4SN; fun_prop
  have hlog : ContinuousAt (fun l => log (i4SN a b c l)) l :=
    hNc.continuousAt.log hN.ne'
  unfold i4SLF
  by_cases hk : b + c = 0
  · simp only [hk, zero_mul, div_zero, neg_zero, zero_sub]
    by_cases hNt : i4SNt a b c t = 0
    · simp only [hNt, zero_mul, div_zero, add_zero]
      exact continuousAt_const.mul continuousAt_const
    · exact continuousAt_const.mul (((hxl.continuousAt.div
        (continuousAt_const.mul hNc.continuousAt) (mul_ne_zero hNt hN.ne')).neg).add
        continuousAt_const)
  by_cases hNt : i4SNt a b c t = 0
  · simp only [hNt, zero_mul, div_zero, sub_zero, add_zero, mul_zero]
    exact continuousAt_const.mul
      ((continuousAt_const.div (continuousAt_const.mul hNc.continuousAt)
        (mul_ne_zero hk hN.ne')).neg.sub
        ((continuousAt_const.mul (hlog.add continuousAt_const)).div
          (continuousAt_const.mul hNc.continuousAt) (mul_ne_zero hk hN.ne')))
  exact continuousAt_const.mul
    ((((continuousAt_const.div (continuousAt_const.mul hNc.continuousAt)
      (mul_ne_zero hk hN.ne')).neg.sub
      ((continuousAt_const.mul (hlog.add continuousAt_const)).div
        (continuousAt_const.mul hNc.continuousAt) (mul_ne_zero hk hN.ne'))).sub
      (hxl.continuousAt.div (continuousAt_const.mul hNc.continuousAt)
        (mul_ne_zero hNt hN.ne'))).add (hlog.div_const _))

/-- The primitive tends to `P log k / (k N_t)` as `l → ∞`. -/
theorem i4SLF_tendsto {a b c t : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hNt : 0 < i4SNt a b c t) :
    Tendsto (i4SLF a b c t) atTop
      (𝓝 (i4SP a b c t * log (b + c) / ((b + c) * i4SNt a b c t))) := by
  set k := b + c with hk_def
  have hk : 0 < k := by positivity
  set Nt := i4SNt a b c t with hNt_def
  have hNlin : ∀ l, i4SN a b c l = k * (l - t) + Nt := fun l => by
    simp only [hk_def, hNt_def, i4SN, i4SNt]; ring
  have hNat : Tendsto (fun l => i4SN a b c l) atTop atTop := by
    simp only [i4SN]
    exact tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hk)
  have hxat : Tendsto (fun l : ℝ => l - t) atTop atTop := tendsto_atTop_add_const_right _ _
    tendsto_id
  have hinv : Tendsto (fun l => (i4SN a b c l)⁻¹) atTop (𝓝 0) := hNat.inv_tendsto_atTop
  have hlogdiv : Tendsto (fun l => log (i4SN a b c l) / i4SN a b c l) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hNat
    simpa [Function.comp_def] using this
  have hxN : Tendsto (fun l => (l - t) / i4SN a b c l) atTop (𝓝 (1 / k)) := by
    have h : Tendsto (fun l => 1 / k - Nt / k * (i4SN a b c l)⁻¹) atTop
        (𝓝 (1 / k - Nt / k * 0)) := tendsto_const_nhds.sub (hinv.const_mul _)
    rw [mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [hNat.eventually_gt_atTop 0] with l hl
    rw [hNlin] at hl ⊢
    field_simp
    ring
  have hNx : Tendsto (fun l => i4SN a b c l / (l - t)) atTop (𝓝 k) := by
    have h : Tendsto (fun l => k + Nt * (l - t)⁻¹) atTop (𝓝 (k + Nt * 0)) :=
      tendsto_const_nhds.add (hxat.inv_tendsto_atTop.const_mul _)
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [hxat.eventually_gt_atTop 0] with l hl
    rw [hNlin]
    field_simp
  have hlogk : Tendsto (fun l => log (i4SN a b c l / (l - t))) atTop (𝓝 (log k)) :=
    ((continuousAt_log hk.ne').tendsto).comp hNx
  have hlim := (((((tendsto_const_nhds (x := -(i4SC a b c t) / k)).mul hinv).sub
    ((tendsto_const_nhds (x := 2 / k)).mul (hlogdiv.add hinv))).add
    ((hxN.mul hlogk).div_const Nt)).add ((tendsto_const_nhds (x := 1 / k)).mul hlogdiv)).const_mul
    (i4SP a b c t)
  convert hlim.congr' ?_ using 2
  · field_simp
    ring
  · filter_upwards [hxat.eventually_gt_atTop 0, hNat.eventually_gt_atTop 0] with l hx hN
    rw [log_div hN.ne' hx.ne']
    unfold i4SLF
    rw [← hk_def, ← hNt_def]
    have e := hNlin l
    field_simp
    rw [e]
    ring

/-- **The `l`-integral at fixed `t`.** -/
theorem i4SL_integral {a b c t : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c = 1)
    (hint : IntegrableOn (fun l => i4STDens a b c l t) (i4SLSec a b c t)) :
    ∫ l in i4SLSec a b c t, i4STDens a b c l t = i4SB a b c t := by
  have hk : 0 < b + c := by positivity
  unfold i4SB
  by_cases hβ : i4SBe a b c t ≤ 0
  · simp only [hβ, ↓reduceIte]
    have : i4SLSec a b c t = ∅ := by
      ext l
      simp only [mem_empty_iff_false, iff_false]
      rw [mem_i4SLSec ha hb hc habc]
      rintro ⟨hl, -, h⟩
      by_cases hα : i4SAl a b c t ≤ 0
      · linarith [i4SBe_pos_of_Al ha hb hc hα]
      · push Not at hα
        nlinarith [mul_pos hα hl]
    rw [this, Measure.restrict_empty, integral_zero_measure]
  simp only [hβ, ↓reduceIte]
  push Not at hβ
  have hNt := i4SNt_pos ha hb hc hβ
  have hd : ∀ l, max 0 t < l → HasDerivAt (i4SLF a b c t) (i4STDens a b c l t) l :=
    fun l hl => i4SLF_hasDerivAt hk
      (i4SN_pos_of_nonneg ha hb hc (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hl)))
      hNt.ne' (lt_of_le_of_lt (le_max_right _ _) hl)
  have hcont : ∀ l, max 0 t ≤ l → ContinuousAt (i4SLF a b c t) l := fun l hl =>
    i4SLF_continuousAt (i4SN_pos_of_nonneg ha hb hc ((le_max_left _ _).trans hl))
  by_cases hα : 0 < i4SAl a b c t
  · simp only [hα, ↓reduceIte]
    have hsec : i4SLSec a b c t = Ioo (max 0 t) (i4SBe a b c t / i4SAl a b c t) := by
      ext l
      rw [mem_i4SLSec ha hb hc habc, mem_Ioo, max_lt_iff, lt_div_iff₀ hα, mul_comm l]
      tauto
    have hlt : max 0 t < i4SBe a b c t / i4SAl a b c t := by
      rw [max_lt_iff, lt_div_iff₀ hα, lt_div_iff₀ hα]
      refine ⟨by simpa using hβ, ?_⟩
      have e : i4SBe a b c t - t * i4SAl a b c t = i4SNt a b c t ^ 2 := by
        unfold i4SBe i4SAl i4SNt; ring
      nlinarith [pow_pos hNt 2]
    rw [hsec] at hint ⊢
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlt.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le
      (fun l hl => (hcont l hl.1).continuousWithinAt) (fun l hl => hd l hl.1)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlt.le).2 hint)
  · simp only [hα, ↓reduceIte]
    push Not at hα
    have hsec : i4SLSec a b c t = Ioi (max 0 t) := by
      ext l
      rw [mem_i4SLSec ha hb hc habc, mem_Ioi, max_lt_iff]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2, by nlinarith [mul_nonpos_of_nonpos_of_nonneg hα h1.le]⟩
    rw [hsec] at hint ⊢
    exact integral_Ioi_of_hasDerivAt_of_tendsto (hcont _ le_rfl).continuousWithinAt
      (fun l hl => hd l hl) hint (i4SLF_tendsto hb hc hNt)

/-- **`P'(0)` as an integral of `i4SB` over `t` and the triangle**, with the integrability of
`i4SB` in `t` for almost every `(a, b)`. -/
theorem i4P1_B :
    (∀ᵐ q ∂(volume.restrict i4STri), Integrable (i4SB q.1 q.2 (1 - q.1 - q.2))) ∧
      IntegrableOn (fun q : ℝ × ℝ => ∫ t, i4SB q.1 q.2 (1 - q.1 - q.2) t) i4STri ∧
      iteratedDeriv 1 i4PInt 0 =
        ((∫ q in i4STri, ∫ t, i4SB q.1 q.2 (1 - q.1 - q.2) t : ℝ) : ℂ) := by
  obtain ⟨-, hae, hI, hE⟩ := i4P1_Omega
  have key : ∀ᵐ q ∂(volume.restrict i4STri), Integrable (i4SB q.1 q.2 (1 - q.1 - q.2)) ∧
      i4SOmega q.1 q.2 (1 - q.1 - q.2) = ∫ t, i4SB q.1 q.2 (1 - q.1 - q.2) t := by
    filter_upwards [hae, ae_restrict_mem measurableSet_i4STri] with q hq hT
    obtain ⟨h1, h2, h3⟩ := hT
    have hc : 0 < 1 - q.1 - q.2 := by linarith
    have habc : q.1 + q.2 + (1 - q.1 - q.2) = 1 := by ring
    have heq : ∀ᵐ t, ∫ l in i4SLSec q.1 q.2 (1 - q.1 - q.2) t,
        i4STDens q.1 q.2 (1 - q.1 - q.2) l t = i4SB q.1 q.2 (1 - q.1 - q.2) t :=
      hq.1.mono fun t ht => i4SL_integral h1 h2 hc habc ht
    exact ⟨hq.2.congr heq, by unfold i4SOmega; exact integral_congr_ae heq⟩
  refine ⟨key.mono fun q hq => hq.1, hI.congr_fun_ae (key.mono fun q hq => hq.2), ?_⟩
  rw [hE, integral_congr_ae (key.mono fun q hq => hq.2)]

end QED.ThreeLoopE

end
