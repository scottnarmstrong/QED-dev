/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondT2G
import QED.Polylog.ExtraIntegrals
import QED.Polylog.Landen
import QED.Polylog.Reflection

/-!
# Set (d), master `I₁₂`: the endpoint values of the antiderivative `G`

With `ℓ = log 2`, the antiderivative `QED.ThreeLoopD.i12T2G` has the one-sided limits

  `G(0⁺) = -ℓ³ - 9ℓ²/4 - π²ℓ/2 + 27π²/8 - 21 ζ(3)/4`,
  `G(1⁻) = 9ℓ²/4 + π²ℓ + 3ℓ + 21π²/4 + 69 ζ(3)/4 - 18`.

At `u → 0⁺` every monomial containing `a = log u` also contains `u`, `log (1 + u)` or
`log (1 - u)`, and `u aᵏ`, `a log (1 ± u) → 0`. At `u → 1⁻`, with `v = 1 - u` and
`e = log (1 + u) - ℓ`, every monomial containing `b = log (1 - u)` also contains `v`, `e` or
`log u`, and `v bᵏ`, `b e`, `b log u → 0` (`|e| ≤ v`). The values use `Li₂ (1/2)` and
`Li₃ (1/2)`.

## Main results

* `QED.ThreeLoopD.tendsto_i12T2G_zero`, `QED.ThreeLoopD.tendsto_i12T2G_one`.
-/

@[expose] public section

open Real Filter Topology Set QED.Polylog

namespace QED.ThreeLoopD

theorem i12_tendsto_mul_log_cube_zero :
    Tendsto (fun x : ℝ => x * log x ^ 3) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 3)).pow 3
  rw [zero_pow three_ne_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [mul_pow, ← rpow_natCast (x ^ (1 / 3 : ℝ)), ← rpow_mul hx.le]
  norm_num
  ring

theorem i12_tendsto_nhdsGT_zero_of_continuousAt {f : ℝ → ℝ} (hf : ContinuousAt f 0) :
    Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
  hf.tendsto.mono_left nhdsWithin_le_nhds

theorem i12_tendsto_nhdsLT_one_of_continuousAt {f : ℝ → ℝ} (hf : ContinuousAt f 1) :
    Tendsto f (𝓝[<] 1) (𝓝 (f 1)) :=
  hf.tendsto.mono_left nhdsWithin_le_nhds

theorem i12_T2_args_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    2 * x / (1 + x) ∈ Icc (-1 : ℝ) 1 ∧ (1 - x) / (1 + x) ∈ Icc (-1 : ℝ) 1 ∧
      1 / (1 + x) ∈ Icc (-1 : ℝ) 1 ∧ (1 + x) / 2 ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hp : (0 : ℝ) < 1 + x := by linarith
  have h1 : 0 < 2 * x / (1 + x) := by positivity
  have h2 : 0 < (1 - x) / (1 + x) := div_pos (by linarith) hp
  have h3 : 0 < 1 / (1 + x) := by positivity
  refine ⟨⟨by linarith, (div_le_one hp).2 (by linarith)⟩, ⟨by linarith, (div_le_one hp).2
    (by linarith)⟩, ⟨by linarith, (div_le_one hp).2 (by linarith)⟩, ⟨by linarith, by linarith⟩⟩

theorem tendsto_i12T2G_zero : Tendsto i12T2G (𝓝[>] 0)
    (𝓝 (-log 2 ^ 3 - 9 * log 2 ^ 2 / 4 - log 2 * π ^ 2 / 2 + 27 * π ^ 2 / 8 - 21 * zeta3 / 4)) := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have tu : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    i12_tendsto_nhdsGT_zero_of_continuousAt continuous_id.continuousAt
  have tb : Tendsto (fun x : ℝ => log (1 - x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using i12_tendsto_nhdsGT_zero_of_continuousAt (f := fun x : ℝ => log (1 - x))
      (by fun_prop (disch := norm_num))
  have tc : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using i12_tendsto_nhdsGT_zero_of_continuousAt (f := fun x : ℝ => log (1 + x))
      (by fun_prop (disch := norm_num))
  have aF : Tendsto (fun x : ℝ => 2 * x / (1 + x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using i12_tendsto_nhdsGT_zero_of_continuousAt (f := fun x : ℝ => 2 * x / (1 + x))
      (by fun_prop (disch := norm_num))
  have aG : Tendsto (fun x : ℝ => (1 - x) / (1 + x)) (𝓝[>] 0) (𝓝 1) := by
    simpa using i12_tendsto_nhdsGT_zero_of_continuousAt (f := fun x : ℝ => (1 - x) / (1 + x))
      (by fun_prop (disch := norm_num))
  have aI : Tendsto (fun x : ℝ => 1 / (1 + x)) (𝓝[>] 0) (𝓝 1) := by
    simpa using i12_tendsto_nhdsGT_zero_of_continuousAt (f := fun x : ℝ => 1 / (1 + x))
      (by fun_prop (disch := norm_num))
  have aP : Tendsto (fun x : ℝ => (1 + x) / 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    simpa using i12_tendsto_nhdsGT_zero_of_continuousAt (f := fun x : ℝ => (1 + x) / 2)
      (by fun_prop (disch := norm_num))
  have iF : ∀ᶠ x in 𝓝[>] (0 : ℝ), 2 * x / (1 + x) ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun x hx => (i12_T2_args_mem hx).1
  have iG : ∀ᶠ x in 𝓝[>] (0 : ℝ), (1 - x) / (1 + x) ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun x hx => (i12_T2_args_mem hx).2.1
  have iI : ∀ᶠ x in 𝓝[>] (0 : ℝ), 1 / (1 + x) ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun x hx => (i12_T2_args_mem hx).2.2.1
  have iP : ∀ᶠ x in 𝓝[>] (0 : ℝ), (1 + x) / 2 ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun x hx => (i12_T2_args_mem hx).2.2.2
  have tF2 := tendsto_Li₂_comp (by norm_num) aF iF
  have tG2 := tendsto_Li₂_comp (by norm_num) aG iG
  have tI2 := tendsto_Li₂_comp (by norm_num) aI iI
  have tP2 := tendsto_Li₂_comp (by norm_num) aP iP
  have tF3 := tendsto_Li₃_comp (by norm_num) aF iF
  have tG3 := tendsto_Li₃_comp (by norm_num) aG iG
  have tI3 := tendsto_Li₃_comp (by norm_num) aI iI
  have tP3 := tendsto_Li₃_comp (by norm_num) aP iP
  have tua := tendsto_mul_log_zero
  have tua2 := tendsto_mul_log_sq_zero
  have tua3 := i12_tendsto_mul_log_cube_zero
  have tab := tendsto_log_mul_log_one_sub_zero
  have tac : Tendsto (fun x : ℝ => log x * log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using tua.abs)
    filter_upwards [hev] with x hx
    have h0 : 0 ≤ log (1 + x) := log_nonneg (by linarith [hx.1])
    have h1 : log (1 + x) ≤ x := by
      have := log_le_sub_one_of_pos (by linarith [hx.1] : 0 < 1 + x)
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_pos hx.1, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have h := (((((((((((((((((((((((((((((((((((((((((((((((tu.mul tb).mul tb).mul tb).add
      (((tu.mul tb).mul tb).const_mul (3/2))).add
      ((((tu.mul tb).mul tc).mul tc).const_mul (-3))).add
      (((tu.mul tb).mul tc).const_mul (6*log 2 - 9))).add
      ((tu.mul tb).const_mul (-6*log 2 ^ 2 + 6*log 2 + 3/2))).add
      ((((tu.mul tc).mul tc).mul tc).const_mul (4))).add
      (((tu.mul tc).mul tc).const_mul (9 - 9*log 2))).add
      (((tu.mul tc).mul tF2).const_mul (6))).add
      (((tu.mul tc).mul tG2).const_mul (6))).add
      ((tu.mul tc).const_mul (6*log 2 ^ 2 - 9*log 2 - 3/2))).add
      ((tu.mul tF2).const_mul (9 - 6*log 2))).add
      ((tu.mul tG2).const_mul (9 - 6*log 2))).add
      ((tu.mul tF3).const_mul (6))).add
      ((tu.mul tG3).const_mul (6))).add
      (tu.const_mul (log 2 ^ 3 + 3*log 2 ^ 2/2 + log 2*π ^ 2 + 6*log 2 - π ^ 2 + 12*zeta3 -
        18))).add
      (((tb.mul tb).mul tb).const_mul (-1))).add
      ((tb.mul tb).const_mul (-3/2))).add
      (((tb.mul tc).mul tc).const_mul (3))).add
      (((tb.mul tc).mul tua).const_mul (6))).add
      ((tb.mul tc).const_mul (6*log 2 - 15))).add
      ((tb.mul tua).const_mul (6 - 12*log 2))).add
      ((tb.mul tua2).const_mul (-6))).add
      (tb.const_mul (-6*log 2 ^ 2 + 18*log 2 - 3/2))).add
      (((tc.mul tc).mul tua).const_mul (-9))).add
      ((tc.mul tc).const_mul (75/4 - 6*log 2))).add
      ((tc.mul tG2).const_mul (-6))).add
      ((tc.mul tI2).const_mul (6))).add
      ((tc.mul tP2).const_mul (6))).add
      ((tc.mul tua).const_mul (12*log 2 - 9))).add
      ((tc.mul tua2).const_mul (6))).add
      (tc.const_mul (6*log 2 ^ 2 - 27*log 2/2 - 3/2))).add
      ((tF2.mul tua).const_mul (-6))).add
      (tF2.const_mul (39/2 - 6*log 2))).add
      ((tG2.mul tua).const_mul (-6))).add
      (tG2.const_mul (9 - 6*log 2))).add
      (tI2.const_mul (9))).add
      (tP2.const_mul (9/2))).add
      (tG3.const_mul (-6))).add
      (tI3.const_mul (6))).add
      (tP3.const_mul (-6))).add
      (tua.const_mul (3*log 2 ^ 2 + 3*log 2 + π ^ 2 + 6))).add
      (tua2.const_mul (3*log 2 + 3/2))).add
      tua3).add
      (tab.const_mul (18 - 6*log 2))).add
      (tac.const_mul (6*log 2 - 18)))
  have key := h.congr' (f₂ := i12T2G) (by
    filter_upwards [hev] with x hx
    simp only [i12T2G]
    ring)
  convert key using 2
  simp only [Li₂_zero, Li₃_zero, Li₂_one, Li₃_one, Li₂_one_half, Li₃_one_half]
  ring

theorem tendsto_i12T2G_one : Tendsto i12T2G (𝓝[<] 1)
    (𝓝 (9 * log 2 ^ 2 / 4 + log 2 * π ^ 2 + 3 * log 2 + 21 * π ^ 2 / 4 + 69 * zeta3 / 4 - 18)) := by
  have hev : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have tv : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) := by
    simpa using i12_tendsto_nhdsLT_one_of_continuousAt (f := fun x : ℝ => 1 - x)
      (by fun_prop)
  have ta : Tendsto (fun x : ℝ => log x) (𝓝[<] 1) (𝓝 0) := by
    simpa using i12_tendsto_nhdsLT_one_of_continuousAt (f := fun x : ℝ => log x)
      (by fun_prop (disch := norm_num))
  have te : Tendsto (fun x : ℝ => log (1 + x) - log 2) (𝓝[<] 1) (𝓝 0) := by
    have := i12_tendsto_nhdsLT_one_of_continuousAt (f := fun x : ℝ => log (1 + x) - log 2)
      (by fun_prop (disch := norm_num))
    norm_num at this
    exact this
  have aF : Tendsto (fun x : ℝ => 2 * x / (1 + x)) (𝓝[<] 1) (𝓝 1) := by
    have := i12_tendsto_nhdsLT_one_of_continuousAt (f := fun x : ℝ => 2 * x / (1 + x))
      (by fun_prop (disch := norm_num))
    norm_num at this
    exact this
  have aG : Tendsto (fun x : ℝ => (1 - x) / (1 + x)) (𝓝[<] 1) (𝓝 0) := by
    simpa using i12_tendsto_nhdsLT_one_of_continuousAt (f := fun x : ℝ => (1 - x) / (1 + x))
      (by fun_prop (disch := norm_num))
  have aI : Tendsto (fun x : ℝ => 1 / (1 + x)) (𝓝[<] 1) (𝓝 (1 / 2)) := by
    have := i12_tendsto_nhdsLT_one_of_continuousAt (f := fun x : ℝ => 1 / (1 + x))
      (by fun_prop (disch := norm_num))
    convert this using 2
    norm_num
  have aP : Tendsto (fun x : ℝ => (1 + x) / 2) (𝓝[<] 1) (𝓝 1) := by
    simpa using i12_tendsto_nhdsLT_one_of_continuousAt (f := fun x : ℝ => (1 + x) / 2)
      (by fun_prop (disch := norm_num))
  have iF : ∀ᶠ x in 𝓝[<] (1 : ℝ), 2 * x / (1 + x) ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun x hx => (i12_T2_args_mem hx).1
  have iG : ∀ᶠ x in 𝓝[<] (1 : ℝ), (1 - x) / (1 + x) ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun x hx => (i12_T2_args_mem hx).2.1
  have iI : ∀ᶠ x in 𝓝[<] (1 : ℝ), 1 / (1 + x) ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun x hx => (i12_T2_args_mem hx).2.2.1
  have iP : ∀ᶠ x in 𝓝[<] (1 : ℝ), (1 + x) / 2 ∈ Icc (-1 : ℝ) 1 :=
    hev.mono fun x hx => (i12_T2_args_mem hx).2.2.2
  have tF2 := tendsto_Li₂_comp (by norm_num) aF iF
  have tG2 := tendsto_Li₂_comp (by norm_num) aG iG
  have tI2 := tendsto_Li₂_comp (by norm_num) aI iI
  have tP2 := tendsto_Li₂_comp (by norm_num) aP iP
  have tF3 := tendsto_Li₃_comp (by norm_num) aF iF
  have tG3 := tendsto_Li₃_comp (by norm_num) aG iG
  have tI3 := tendsto_Li₃_comp (by norm_num) aI iI
  have tP3 := tendsto_Li₃_comp (by norm_num) aP iP
  have tab := tendsto_log_mul_log_one_sub_one
  have tbv : Tendsto (fun x : ℝ => (1 - x) * log (1 - x)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have tbv2 : Tendsto (fun x : ℝ => (1 - x) * log (1 - x) ^ 2) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one
  have tbv3 : Tendsto (fun x : ℝ => (1 - x) * log (1 - x) ^ 3) (𝓝[<] 1) (𝓝 0) :=
    i12_tendsto_mul_log_cube_zero.comp tendsto_one_sub_nhdsLT_one
  have tbe : Tendsto (fun x : ℝ => log (1 - x) * (log (1 + x) - log 2)) (𝓝[<] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using tbv.abs)
    filter_upwards [hev] with x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hy : 0 < (1 + x) / 2 := by linarith
    have hl := log_div (by linarith : (1 + x) ≠ 0) (two_ne_zero (α := ℝ))
    have hup : log ((1 + x) / 2) ≤ 0 := log_nonpos hy.le (by linarith)
    have hlo := one_sub_inv_le_log_of_pos hy
    have hlo' : x - 1 ≤ 1 - ((1 + x) / 2)⁻¹ := by
      rw [inv_div, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, ← hl, abs_of_nonpos hup,
      abs_of_pos (by linarith : (0 : ℝ) < 1 - x), mul_comm (1 - x)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h := ((((((((((((((((((((((((((((((((((((((((((((((((((((((
      (tv.mul ta).mul ta).mul ta).const_mul (-1)).add
      ((((tv.mul ta).mul ta).mul te).const_mul (-6))).add
      (((tv.mul ta).mul ta).const_mul (-9*log 2 - 3/2))).add
      ((((tv.mul ta).mul te).mul te).const_mul (9))).add
      (((tv.mul ta).mul te).const_mul (6*log 2 + 9))).add
      (((tv.mul ta).mul tF2).const_mul (6))).add
      (((tv.mul ta).mul tG2).const_mul (6))).add
      (((tv.mul ta).mul tab).const_mul (6))).add
      ((tv.mul ta).const_mul (-6*log 2 ^ 2 + 6*log 2 - π ^ 2 - 6))).add
      ((((tv.mul te).mul te).mul te).const_mul (-4))).add
      (((tv.mul te).mul te).const_mul (-3*log 2 - 9))).add
      (((tv.mul te).mul tF2).const_mul (-6))).add
      (((tv.mul te).mul tG2).const_mul (-6))).add
      (((tv.mul te).mul tab).const_mul (-6))).add
      ((tv.mul te).const_mul (3/2 - 9*log 2))).add
      ((tv.mul tF2).const_mul (-9))).add
      ((tv.mul tG2).const_mul (-9))).add
      ((tv.mul tF3).const_mul (-6))).add
      ((tv.mul tG3).const_mul (-6))).add
      ((tv.mul tab).const_mul (6*log 2 - 6))).add
      (tv.const_mul (-2*log 2 ^ 3 - 3*log 2 ^ 2/2 - log 2*π ^ 2 - 9*log 2/2 + π ^ 2 -
        12*zeta3 + 18))).add
      ((ta.mul ta).mul ta)).add
      (((ta.mul ta).mul te).const_mul (6))).add
      ((ta.mul ta).const_mul (9*log 2 + 3/2))).add
      (((ta.mul te).mul te).const_mul (-9))).add
      ((ta.mul te).const_mul (-27))).add
      ((ta.mul tF2).const_mul (-6))).add
      ((ta.mul tG2).const_mul (-6))).add
      ((ta.mul tab).const_mul (-6))).add
      (ta.const_mul (12*log 2 ^ 2 - 24*log 2 + π ^ 2 + 6))).add
      (((te.mul te).mul te).const_mul (4))).add
      (((te.mul te).mul tbv).const_mul (3))).add
      ((te.mul te).const_mul (111/4 - 3*log 2))).add
      ((te.mul tF2).const_mul (6))).add
      ((te.mul tI2).const_mul (6))).add
      ((te.mul tP2).const_mul (6))).add
      ((te.mul tab).const_mul (6))).add
      ((te.mul tbv).const_mul (9))).add
      (te.const_mul (-6*log 2 ^ 2 + 33*log 2 - 3))).add
      (tF2.const_mul (57/2 - 6*log 2))).add
      (tG2.const_mul (18 - 12*log 2))).add
      (tI2.const_mul (6*log 2 + 9))).add
      (tP2.const_mul (6*log 2 + 9/2))).add
      (tF3.const_mul (6))).add
      (tI3.const_mul (6))).add
      (tP3.const_mul (-6))).add
      (tab.const_mul (24 - 12*log 2))).add
      (tbv.const_mul (3*log 2 ^ 2 + 3*log 2 - 3/2))).add
      (tbv2.const_mul (-3/2))).add
      (tbv3.const_mul (-1))).add
      (tbe.const_mul (12*log 2 -
        24))).add_const (2*log 2 ^ 3 + 27*log 2 ^ 2/4 + log 2*π ^ 2 + 3*log 2 - π ^ 2 +
        12*zeta3 - 18))
  have key := h.congr' (f₂ := i12T2G) (by
    filter_upwards [hev] with x hx
    simp only [i12T2G]
    ring)
  convert key using 2
  simp only [Li₂_zero, Li₃_zero, Li₂_one, Li₃_one, Li₂_one_half, Li₃_one_half]
  ring

end QED.ThreeLoopD
