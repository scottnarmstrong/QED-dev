/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValTwoB
public import QED.ThreeLoopD.SetDMastersI15KOne
import QED.Polylog.LiLimits
import QED.Polylog.ExtraIntegralsC
import QED.Polylog.DilogPM
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₁₅`: the second Taylor coefficient of `K`

`∫∫ F₂ = 35 π²/12 + 4 ζ(3) - 251/8`.

With `F₂ = A₁ + A₂₃` (`QED.ThreeLoopD.i15F_two_eq`), `∫∫ A₂₃ = π²/4 + 4 ζ(3) - 59/8`
(`QED.ThreeLoopD.SetDMastersI15KValTwoA`) and `∫∫ A₁ = 8 π²/3 - 24` here. For `A₁ ≥ 0` the
inner integral over `u` at `0 < x < 1/2` is `2 W(r) / (x (1 - x))`, `r = x / (1 - x)`
(`QED.ThreeLoopD.SetDMastersI15KValTwoB`); since `dx / (x (1 - x)) = dr / r`, the outer
integral over `(0, 1/2)` is half of `∫₀¹ 4 W(r) / r dr`, whose primitive
`QED.ThreeLoopD.i15QPhi` (dilogarithms of `± r`) runs from `24` at `0⁺` to `8 π²/3` at `1⁻`.
The half `(1/2, 1)` is the mirror image (`A₁` is symmetric under `x ↦ 1 - x`). The
primitives also give the integrability of `A₁` (Tonelli, as `A₁ ≥ 0`), and then that of
`A₂₃ = F₂ - A₁`.

## Main results

* `QED.ThreeLoopD.integral_i15A1`: `∫∫ A₁ = 8 π²/3 - 24`.
* `QED.ThreeLoopD.integral_i15F_two`: `∫∫ F₂ = 35 π²/12 + 4 ζ(3) - 251/8`.
* `QED.ThreeLoopD.hasTruncLaurent_i15K_of_coeffs_three`: the target expansion of `K` from
  `∫ F₃`, `∫ F₄`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### The outer primitive in `r` -/

/-- `Q(r) = 3 Li₂(-r) + 2 Li₂ r + log r (log (1 + r) + 2 log (1 - r))`. -/
noncomputable def i15QQ (r : ℝ) : ℝ :=
  3 * Li₂ (-r) + 2 * Li₂ r + log r * (log (1 + r) + 2 * log (1 - r))

/-- A primitive of `4 W(r) / r`. -/
noncomputable def i15QPhi (r : ℝ) : ℝ :=
  -4 * (1 / r + r) * i15QQ r - 8 * (Li₂ (-r) + log r * log (1 + r)) +
    16 * (Li₂ r + log r * log (1 - r)) + 8 * Li₂ (-r) + 2 * (r * log r ^ 2) +
    20 * (r * log r) - 4 * log r + 20 * (log (1 + r) / r) - 20 * (r * log (1 + r)) +
    2 * π ^ 2 * r / 3

theorem hasDerivAt_i15QPhi {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i15QPhi (4 * i15QWr r / r) r := by
  obtain ⟨hr0, hr1⟩ := hr
  have hn : |-r| < 1 := by rw [abs_neg, abs_of_pos hr0]; exact hr1
  have hp : |r| < 1 := by rw [abs_of_pos hr0]; exact hr1
  have l2n := (hasDerivAt_Li₂ hn (by linarith)).comp r (hasDerivAt_neg r)
  have l2 := hasDerivAt_Li₂ hp hr0.ne'
  have hl := Real.hasDerivAt_log hr0.ne'
  have hlp : HasDerivAt (fun r : ℝ => log (1 + r)) (1 / (1 + r)) r := by
    have := ((hasDerivAt_id' r).const_add 1).log (by linarith : (0 : ℝ) < 1 + r).ne'
    simpa using this
  have hlm : HasDerivAt (fun r : ℝ => log (1 - r)) (-1 / (1 - r)) r := by
    have := ((hasDerivAt_id' r).const_sub 1).log (by linarith : (0 : ℝ) < 1 - r).ne'
    simpa [neg_div] using this
  have hinv : HasDerivAt (fun r : ℝ => 1 / r) ((0 * r - 1 * 1) / r ^ 2) r :=
    (hasDerivAt_const r 1).div (hasDerivAt_id' r) hr0.ne'
  have dQ : HasDerivAt i15QQ (3 * (-log (1 - -r) / -r * -1) + 2 * (-log (1 - r) / r) +
      (r⁻¹ * (log (1 + r) + 2 * log (1 - r)) + log r * (1 / (1 + r) + 2 * (-1 / (1 - r))))) r := by
    have := ((l2n.const_mul 3).add (l2.const_mul 2)).add (hl.mul (hlp.add (hlm.const_mul 2)))
    convert this using 1
    funext y; simp [i15QQ]
  have g1 := ((hinv.add (hasDerivAt_id' r)).const_mul (-4)).mul dQ
  have g2 := (l2n.add (hl.mul hlp)).const_mul 8
  have g3 := (l2.add (hl.mul hlm)).const_mul 16
  have g4 := l2n.const_mul 8
  have g5 := ((hasDerivAt_id' r).mul (hl.pow 2)).const_mul 2
  have g6 := ((hasDerivAt_id' r).mul hl).const_mul 20
  have g7 := hl.const_mul 4
  have g8 := (hlp.div (hasDerivAt_id' r) hr0.ne').const_mul 20
  have g9 := ((hasDerivAt_id' r).mul hlp).const_mul 20
  have g10 := ((hasDerivAt_id' r).const_mul (2 * π ^ 2)).div_const 3
  have h := ((((((((g1.sub g2).add g3).add g4).add g5).add g6).sub g7).add g8).sub g9).add g10
  convert h using 1
  · funext y
    simp only [i15QPhi, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply,
      Pi.pow_apply, Pi.div_apply]
  · have h1 : 1 - r ≠ 0 := by linarith
    have h2 : 1 + r ≠ 0 := by linarith
    simp only [sub_neg_eq_add, Pi.pow_apply, Pi.add_apply]
    unfold i15QWr i15QQ
    field_simp
    ring

/-! ### The limits of the outer primitive -/

theorem i15Q_abs_log_comb_le {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 2) :
    |log (1 + r) + 2 * log (1 - r) + r| ≤ 6 * r ^ 2 := by
  have ha : |r| < 1 := by rw [abs_of_pos h0]; linarith
  have hb : |-r| < 1 := by rw [abs_neg]; exact ha
  have e1 := Real.abs_log_sub_add_sum_range_le ha 1
  have e2 := Real.abs_log_sub_add_sum_range_le hb 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_neg, sub_neg_eq_add, abs_of_pos h0] at e1 e2
  have hd : r ^ 2 / (1 - r) ≤ 2 * r ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg r]
  have e1' := e1.trans hd
  have e2' := e2.trans hd
  have hsum : log (1 + r) + 2 * log (1 - r) + r =
      (-r + log (1 + r)) + 2 * (r + log (1 - r)) := by ring
  rw [hsum]
  calc |(-r + log (1 + r)) + 2 * (r + log (1 - r))|
      ≤ |-r + log (1 + r)| + |2 * (r + log (1 - r))| := abs_add_le _ _
    _ = |-r + log (1 + r)| + 2 * |r + log (1 - r)| := by rw [abs_mul]; norm_num
    _ ≤ 6 * r ^ 2 := by linarith

theorem tendsto_Li₂_neg_div_zero : Tendsto (fun r => Li₂ (-r) / r) (𝓝[>] 0) (𝓝 (-1)) := by
  have hd : HasDerivAt (fun r : ℝ => Li₂ (-r)) (1 * -1) 0 := by
    have h0 : HasDerivAt Li₂ 1 (-0) := by rw [neg_zero]; exact hasDerivAt_Li₂_zero
    have := h0.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  refine (hd.tendsto_slope_zero_right.congr fun t => ?_).trans (by norm_num)
  simp only [zero_add, neg_zero, Li₂_zero, sub_zero, smul_eq_mul]
  ring

theorem tendsto_i15QPhi_zero : Tendsto i15QPhi (𝓝[>] 0) (𝓝 24) := by
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun x : ℝ => -x) (𝓝[>] 0) (𝓝 0) := by simpa using hx0.neg
  have hnI : ∀ᶠ x in 𝓝[>] (0 : ℝ), -x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have l2n : Tendsto (fun x => Li₂ (-x)) (𝓝[>] 0) (𝓝 0) := by
    simpa [Li₂_zero] using tendsto_Li₂_comp (by norm_num) hn hnI
  have hlp : Tendsto (fun x => log x * log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_mul_log_zero.mul tendsto_log_one_add_div_zero
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    field_simp
  have hlm := tendsto_log_mul_log_one_sub_zero
  have hlp1 : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => log (1 + x)) 0 :=
      (continuousAt_const.add continuousAt_id).log (by norm_num)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hQ : Tendsto i15QQ (𝓝[>] 0) (𝓝 0) := by
    have := ((l2n.const_mul 3).add (tendsto_Li₂_zero_right.const_mul 2)).add
      (hlp.add (hlm.const_mul 2))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun x => ?_
    simp only [i15QQ]; ring
  have hcomb : Tendsto (fun x => log x * ((log (1 + x) + 2 * log (1 - x) + x) / x)) (𝓝[>] 0)
      (𝓝 0) := by
    refine i15V_tendsto_log_mul_of_abs_le (C := 6) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    rw [abs_div, abs_of_pos hx.1, div_le_iff₀ hx.1]
    have := i15Q_abs_log_comb_le hx.1 hx.2.le
    nlinarith
  have hN := ((((tendsto_Li₂_neg_div_zero.const_mul (-12)).sub
    (tendsto_Li₂_div_zero.const_mul 8)).add (tendsto_log_one_add_div_zero.const_mul 20)).sub
    (hcomb.const_mul 4))
  have hR := (((((((((hx0.mul hQ).const_mul (-4)).sub ((l2n.add hlp).const_mul 8)).add
    ((tendsto_Li₂_zero_right.add hlm).const_mul 16)).add (l2n.const_mul 8)).add
    (tendsto_mul_log_sq_zero.const_mul 2)).add (tendsto_mul_log_zero.const_mul 20)).sub
    ((hx0.mul hlp1).const_mul 20)).add ((hx0.const_mul (2 * π ^ 2)).div_const 3))
  have h := hN.add hR
  have e : (-12 * -1 - 8 * 1 + 20 * 1 - 4 * 0 + (-4 * (0 * 0) - 8 * (0 + 0) + 16 * (0 + 0) +
      8 * 0 + 2 * 0 + 20 * 0 - 20 * (0 * 0) + 2 * π ^ 2 * 0 / 3) : ℝ) = 24 := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  simp only [i15QPhi, i15QQ]
  field_simp
  ring

theorem tendsto_i15QPhi_one : Tendsto i15QPhi (𝓝[<] 1) (𝓝 (8 * π ^ 2 / 3)) := by
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun x : ℝ => -x) (𝓝[<] 1) (𝓝 (-1)) := hx1.neg
  have hnI : ∀ᶠ x in 𝓝[<] (1 : ℝ), -x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have l2n : Tendsto (fun x => Li₂ (-x)) (𝓝[<] 1) (𝓝 (Li₂ (-1))) :=
    tendsto_Li₂_comp (by norm_num) hn hnI
  have hlog : Tendsto (fun x : ℝ => log x) (𝓝[<] 1) (𝓝 0) := by
    have := (Real.continuousAt_log (one_ne_zero (α := ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hlp : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[<] 1) (𝓝 (log (1 + 1))) :=
    ((Real.continuousAt_log (by norm_num : (1 : ℝ) + 1 ≠ 0)).tendsto.comp (hx1.const_add 1))
  have hlm := tendsto_log_mul_log_one_sub_one
  have hinv : Tendsto (fun x : ℝ => 1 / x) (𝓝[<] 1) (𝓝 (1 / 1)) :=
    tendsto_const_nhds.div hx1 one_ne_zero
  have hQ : Tendsto i15QQ (𝓝[<] 1) (𝓝 (3 * Li₂ (-1) + 2 * (π ^ 2 / 6) + (0 * log (1 + 1) +
      2 * 0))) := by
    have := ((l2n.const_mul 3).add (tendsto_Li₂_one_left.const_mul 2)).add
      ((hlog.mul hlp).add (hlm.const_mul 2))
    refine this.congr fun x => ?_
    simp only [i15QQ]; ring
  have g1 := ((hinv.add hx1).const_mul (-4)).mul hQ
  have g2 := (l2n.add (hlog.mul hlp)).const_mul 8
  have g3 := (tendsto_Li₂_one_left.add hlm).const_mul 16
  have g4 := l2n.const_mul 8
  have g5 := (hx1.mul (hlog.pow 2)).const_mul 2
  have g6 := (hx1.mul hlog).const_mul 20
  have g7 := hlog.const_mul 4
  have g8 := (hlp.div hx1 one_ne_zero).const_mul 20
  have g9 := (hx1.mul hlp).const_mul 20
  have g10 := (hx1.const_mul (2 * π ^ 2)).div_const 3
  have h := ((((((((g1.sub g2).add g3).add g4).add g5).add g6).sub g7).add g8).sub g9).add g10
  rw [Li₂_neg_one] at h
  convert h using 1
  · funext y
    simp only [i15QPhi, Pi.div_apply]
  · ring_nf

/-! ### The outer primitive in `x` -/

/-- The inner integral of `A₁` at `0 < x < 1/2`. -/
noncomputable def i15QG (x : ℝ) : ℝ := 2 * i15QWr (x / (1 - x)) / (x * (1 - x))

/-- `Ψ(x) = Φ(x / (1 - x)) / 2`. -/
noncomputable def i15QPsi (x : ℝ) : ℝ := i15QPhi (x / (1 - x)) / 2

theorem i15Q_ratio_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : x / (1 - x) ∈ Ioo (0 : ℝ) 1 := by
  have : 0 < 1 - x := by linarith [hx.2]
  exact ⟨div_pos hx.1 this, by rw [div_lt_one this]; linarith [hx.2]⟩

theorem hasDerivAt_i15QPsi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt i15QPsi (i15QG x) x := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have hd : HasDerivAt (fun x => x / (1 - x)) ((1 * (1 - x) - x * (-1)) / (1 - x) ^ 2) x := by
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub 1
    exact (hasDerivAt_id' x).div h2 h1.ne'
  have h := ((hasDerivAt_i15QPhi (i15Q_ratio_mem hx)).comp x hd).div_const 2
  convert h using 1
  · funext y; rfl
  unfold i15QG
  have h0 : x ≠ 0 := hx.1.ne'
  field_simp
  ring

theorem i15Q_continuousAt_ratio {x : ℝ} (hx : x ≠ 1) :
    ContinuousAt (fun x : ℝ => x / (1 - x)) x :=
  continuousAt_id.div (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 (Ne.symm hx))

theorem i15Q_tendsto_ratio_zero :
    Tendsto (fun x : ℝ => x / (1 - x)) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((i15Q_continuousAt_ratio (x := 0) (by norm_num)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    exact (i15Q_ratio_mem hx).1

theorem i15Q_tendsto_ratio_half :
    Tendsto (fun x : ℝ => x / (1 - x)) (𝓝[<] (1 / 2)) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((i15Q_continuousAt_ratio (x := 1 / 2) (by norm_num)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2)))
    convert this using 2
    norm_num
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    exact (i15Q_ratio_mem hx).2

theorem tendsto_i15QPsi_zero : Tendsto i15QPsi (𝓝[>] 0) (𝓝 12) := by
  have := (tendsto_i15QPhi_zero.comp i15Q_tendsto_ratio_zero).div_const 2
  rw [show (24 : ℝ) / 2 = 12 by norm_num] at this
  exact this

theorem tendsto_i15QPsi_half : Tendsto i15QPsi (𝓝[<] (1 / 2)) (𝓝 (4 * π ^ 2 / 3)) := by
  have := (tendsto_i15QPhi_one.comp i15Q_tendsto_ratio_half).div_const 2
  rw [show 8 * π ^ 2 / 3 / 2 = 4 * π ^ 2 / 3 by ring] at this
  exact this

/-! ### The symmetry `x ↦ 1 - x` and the slices -/

theorem i15A1_one_sub (x u : ℝ) : i15A1 (1 - x, u) = i15A1 (x, u) := by
  have hc : (1 - x) * (1 - (1 - x)) = x * (1 - x) := by ring
  have hP : i15P (1 - x) u = i15P x u := by unfold i15P i9Poly; ring
  unfold i15A1 i15B1 i15B2
  simp only [hc, hP]

/-- The slice integral `g(x) = ∫₀¹ A₁(x, u) du`. -/
noncomputable def i15Qg (x : ℝ) : ℝ := ∫ u in Ioo (0 : ℝ) 1, i15A1 (x, u)

theorem i15Qg_one_sub (x : ℝ) : i15Qg (1 - x) = i15Qg x := by
  unfold i15Qg
  simp only [i15A1_one_sub]

theorem i15Qg_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : i15Qg x = i15QG x :=
  (integrableOn_and_integral_i15A1_inner hx).2

theorem i15A1_nonneg {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) : 0 ≤ i15A1 z := by
  obtain ⟨hx, hu⟩ := hz
  have := i15A1_eq hx hu
  simp only [Prod.mk.eta] at this
  rw [this]
  have hc : 0 < z.1 * (1 - z.1) := mul_pos hx.1 (by linarith [hx.2])
  exact div_nonneg (mul_nonneg (by norm_num) (i15Qf_nonneg hx hu)) hc.le

theorem i15QG_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : 0 ≤ i15QG x := by
  rw [← i15Qg_eq hx]
  refine setIntegral_nonneg measurableSet_Ioo fun u hu => ?_
  exact i15A1_nonneg (z := (x, u)) ⟨⟨hx.1, by linarith [hx.2]⟩, hu⟩

/-! ### The outer integral -/

theorem i15Qg_left :
    IntervalIntegrable i15Qg volume 0 (1 / 2) ∧
      ∫ x in (0 : ℝ)..(1 / 2), i15Qg x = 4 * π ^ 2 / 3 - 12 := by
  have h := i15Q_ftc_nonneg (F := i15QPsi) (f := i15Qg) (by norm_num)
    (fun x hx => by rw [i15Qg_eq hx]; exact hasDerivAt_i15QPsi hx)
    (fun x hx => by rw [i15Qg_eq hx]; exact i15QG_nonneg hx) tendsto_i15QPsi_zero
    tendsto_i15QPsi_half
  exact h

theorem i15Qg_right :
    IntervalIntegrable i15Qg volume (1 / 2) 1 ∧
      ∫ x in (1 / 2 : ℝ)..1, i15Qg x = 4 * π ^ 2 / 3 - 12 := by
  have hs : ∀ x ∈ Ioo (1 / 2 : ℝ) 1, 1 - x ∈ Ioo (0 : ℝ) (1 / 2) := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hd : ∀ x ∈ Ioo (1 / 2 : ℝ) 1, HasDerivAt (fun x => -i15QPsi (1 - x)) (i15Qg x) x := by
    intro x hx
    have := ((hasDerivAt_i15QPsi (hs x hx)).comp x ((hasDerivAt_id' x).const_sub 1)).neg
    rw [← i15Qg_one_sub, i15Qg_eq (hs x hx)]
    convert this using 1
    · funext y; rfl
    · ring
  have h0 : Tendsto (fun x => -i15QPsi (1 - x)) (𝓝[>] (1 / 2)) (𝓝 (-(4 * π ^ 2 / 3))) := by
    refine (tendsto_i15QPsi_half.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)).neg
    · have := ((continuous_sub_left (1 : ℝ)).tendsto (1 / 2)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (1 / 2)))
      convert this using 2; norm_num
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 / 2 < x)
      show 1 - x < 1 / 2
      linarith
  have h1 : Tendsto (fun x => -i15QPsi (1 - x)) (𝓝[<] 1) (𝓝 (-12)) :=
    (tendsto_i15QPsi_zero.comp tendsto_one_sub_nhdsLT_one).neg
  have h := i15Q_ftc_nonneg (F := fun x => -i15QPsi (1 - x)) (f := i15Qg) (by norm_num) hd
    (fun x hx => by rw [← i15Qg_one_sub, i15Qg_eq (hs x hx)]; exact i15QG_nonneg (hs x hx)) h0 h1
  refine ⟨h.1, ?_⟩
  rw [h.2]
  ring

/-! ### Integrability and the value of `∫∫ A₁` -/

theorem measurable_i15A1 : Measurable i15A1 := by
  unfold i15A1 i15B1 i15B2 i15P i9Poly
  fun_prop

theorem integrableOn_i15A1_slice {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hx2 : x ≠ 1 / 2) :
    IntegrableOn (fun u => i15A1 (x, u)) (Ioo 0 1) := by
  rcases lt_or_gt_of_ne hx2 with h | h
  · exact (integrableOn_and_integral_i15A1_inner ⟨hx.1, h⟩).1
  · have := (integrableOn_and_integral_i15A1_inner (x := 1 - x)
      ⟨by linarith [hx.2], by linarith⟩).1
    simpa only [i15A1_one_sub] using this

theorem integrable_i15A1 : IntegrableOn i15A1 (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rw [IntegrableOn, volume_restrict_prod2,
    integrable_prod_iff measurable_i15A1.aestronglyMeasurable]
  have hne : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), x ∈ ({1 / 2} : Set ℝ)ᶜ :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton _))
  have hgI : IntegrableOn i15Qg (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (i15Qg_left.1.trans i15Qg_right.1)
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with x hx hx2
    exact integrableOn_i15A1_slice hx hx2
  · refine hgI.congr_fun (fun x hx => ?_) measurableSet_Ioo
    unfold i15Qg
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (i15A1_nonneg (z := (x, u)) ⟨hx, hu⟩)]

/-- **`∫∫ A₁ = 8 π²/3 - 24`.** -/
theorem integral_i15A1 :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15A1 z = 8 * π ^ 2 / 3 - 24 := by
  have hF : Integrable i15A1 ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [← volume_restrict_prod2]; exact integrable_i15A1
  rw [volume_restrict_prod2, integral_prod _ hF]
  change ∫ x in Ioo (0 : ℝ) 1, i15Qg x = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals i15Qg_left.1 i15Qg_right.1,
    i15Qg_left.2, i15Qg_right.2]
  ring

/-! ### The second Taylor coefficient -/

/-- **`∫∫ F₂ = 35 π²/12 + 4 ζ(3) - 251/8`.** -/
theorem integral_i15F_two :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 2 z =
      35 / 12 * Real.pi ^ 2 + 4 * QED.Polylog.zeta3 - 251 / 8 := by
  have hS := i15_S_meas
  have hF := integrable_i15F_real (k := 2) (by norm_num)
  have h23 : IntegrableOn i15A23 (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    IntegrableOn.congr_fun (hF.sub integrable_i15A1) (fun z hz => by
      simp only [Pi.sub_apply]; rw [i15F_two_eq hz]; ring) hS
  rw [setIntegral_congr_fun hS fun z hz => i15F_two_eq hz,
    integral_add integrable_i15A1 h23, integral_i15A1, integral_i15A23 h23]
  ring

/-- **The target expansion of `K` from `∫ F₃`, `∫ F₄`** (`∫ F₀`, `∫ F₁`, `∫ F₂` are proved). -/
theorem hasTruncLaurent_i15K_of_coeffs_three
    (h3 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 3 z =
      -16 * Real.pi ^ 2 * Real.log 2 + 107 / 8 * Real.pi ^ 2 + 61 * QED.Polylog.zeta3 - 1665 / 16)
    (h4 : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15F 4 z =
      384 * QED.Polylog.Li 4 (1 / 2) + 16 * Real.log 2 ^ 4
        + 32 * Real.pi ^ 2 * Real.log 2 ^ 2 - 72 * Real.pi ^ 2 * Real.log 2
        - 253 / 80 * Real.pi ^ 4 - 2 / 3 * Real.pi ^ 2 * QED.Polylog.zeta3
        + 2267 / 48 * Real.pi ^ 2 + 503 / 2 * QED.Polylog.zeta3 + 12 * QED.Polylog.zeta5
        - 10403 / 32) :
    HasTruncLaurent i15K i15KLaurent 5 :=
  hasTruncLaurent_i15K_of_coeffs_two integral_i15F_two h3 h4

end QED.ThreeLoopD
