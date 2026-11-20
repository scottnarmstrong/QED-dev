/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCJ
public import QED.Polylog.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Set (c), Stage K, closed forms: the dilogarithm identity of `ρ_C`

Helper level (no frozen statement). With `K = X² - 2X + 2` (`formCK`), `T = X² - X + 1`
(`formCT`) and `W = 4 Li₂(X - 1) + 2 Li₂(1 - X) + 2 log(1 - X) log(2 - X) + log X log(1 - X)`
(`formCW`, the weight-two function of the `λ⁽⁴⁾` alphabet), the weight-two part of the
endpoint value `G(X; X) - G(0; X)` of the `u`-antiderivative of `σ_C` reduces to `-W/6` by

**`formCDel_eq_zero`**: for `0 < X < 1`, `formCDel X = 0`, where `formCDel` is the signed sum of
thirteen `Li₂` values with arguments in `(-1, 1)`, `π²/6`, `log² T/2 - log(1 - X) log T -
log K log T` and `W`.

Proof: every term has an explicit derivative (`Li₂' = -log(1 - z)/z`, the logarithms of
`1 - z` factor over the letters `2, X, 1 - X, 2 - X, K, T`), the derivatives cancel
(`hasDerivAt_formCDel`), so `formCDel` is constant on `(0, 1)`; its limit at `0⁺` is `0`
(`tendsto_formCDel`: `Li₂` is continuous on `[-1, 1]`, `log X log(1 - X) → 0`,
`Li₂ 1 = π²/6`, `Li₂ (-1) = -π²/12`).
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.ChainProof.SetCK

/-- `T = X² - X + 1`, the value of `M` at `u = 0`. -/
def formCT (X : ℝ) : ℝ := X ^ 2 - X + 1

/-- The weight-two function `W` of the `λ⁽⁴⁾` alphabet. -/
noncomputable def formCW (X : ℝ) : ℝ :=
  4 * Li₂ (X - 1) + 2 * Li₂ (1 - X) + 2 * log (1 - X) * log (2 - X) + log X * log (1 - X)

/-- The thirteen `Li₂` values of the endpoint value of the `u`-antiderivative. -/
noncomputable def formCLi (X : ℝ) : ℝ :=
  -Li₂ X - Li₂ (1 / formCK X) - Li₂ (X ^ 2 / formCK X) - Li₂ ((1 - X) / formCT X) -
    Li₂ (-(X * (2 - X)) / formCK X) - Li₂ (formCT X) - Li₂ ((1 - X) ^ 2) +
    Li₂ (X ^ 2 / formCT X) + Li₂ (-X ^ 2 / formCK X) + Li₂ (1 - X) +
    Li₂ (X * (2 - X) / formCK X) + Li₂ ((1 - X) ^ 2 / formCT X) + Li₂ (formCT X / formCK X)

/-- **The dilogarithm identity**, as a function that vanishes on `(0, 1)`. -/
noncomputable def formCDel (X : ℝ) : ℝ :=
  formCLi X + π ^ 2 / 6 + log (formCT X) ^ 2 / 2 - log (1 - X) * log (formCT X) -
    log (formCK X) * log (formCT X) + formCW X

theorem formC_hasDerivAt_K (X : ℝ) : HasDerivAt formCK (2 * X - 2) X :=
  (((hasDerivAt_pow 2 X).sub ((hasDerivAt_id X).const_mul 2)).add_const 2).congr_deriv
    (by norm_num)

theorem formC_hasDerivAt_T (X : ℝ) : HasDerivAt formCT (2 * X - 1) X :=
  (((hasDerivAt_pow 2 X).sub (hasDerivAt_id X)).add_const 1).congr_deriv (by norm_num)

theorem formCK_pos (X : ℝ) : 0 < formCK X := by
  unfold formCK
  nlinarith [sq_nonneg (X - 1)]

theorem formCT_pos (X : ℝ) : 0 < formCT X := by
  unfold formCT
  nlinarith [sq_nonneg (X - 1 / 2)]

/-- The chain rule for `Li₂ ∘ f` with the factored logarithm `L = log(1 - f)` and the
logarithmic derivative `r = f'/f`. -/
theorem formC_li2_comp {f : ℝ → ℝ} {f' x L r : ℝ} (hf : HasDerivAt f f' x) (h1 : |f x| < 1)
    (h0 : f x ≠ 0) (hL : log (1 - f x) = L) (hr : f' = r * f x) :
    HasDerivAt (fun y => Li₂ (f y)) (-(L * r)) x := by
  refine ((hasDerivAt_Li₂ h1 h0).comp x hf).congr_deriv ?_
  rw [hL, hr]
  field_simp

section terms

variable {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1)
include hX

theorem formC_dLi1 : HasDerivAt (fun y => Li₂ y) (-(log (1 - X) * (1 / X))) X := by
  obtain ⟨h0, h1⟩ := hX
  refine formC_li2_comp (hasDerivAt_id X) ?_ h0.ne' rfl ?_
  · show |X| < 1
    rw [abs_lt]; constructor <;> linarith
  · show (1 : ℝ) = 1 / X * X
    field_simp

theorem formC_dLi2 : HasDerivAt (fun y => Li₂ (1 / formCK y))
    (-((2 * log (1 - X) - log (formCK X)) * (-(2 * X - 2) / formCK X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hK := formCK_pos X
  have hK1 : 1 < formCK X := by unfold formCK; nlinarith
  refine formC_li2_comp ((hasDerivAt_const X (1 : ℝ)).div (formC_hasDerivAt_K X) hK.ne')
    ?_ (by positivity) ?_ ?_
  · rw [abs_of_pos (by positivity), div_lt_one hK]; exact hK1
  · have e : 1 - 1 / formCK X = (1 - X) ^ 2 / formCK X := by
      field_simp; unfold formCK; ring
    rw [e, log_div (by positivity) hK.ne', log_pow]; push_cast; ring
  · field_simp; ring

theorem formC_dLi3 : HasDerivAt (fun y => Li₂ (y ^ 2 / formCK y))
    (-((log 2 + log (1 - X) - log (formCK X)) * (2 / X - (2 * X - 2) / formCK X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hK := formCK_pos X
  refine formC_li2_comp ((hasDerivAt_pow 2 X).div (formC_hasDerivAt_K X) hK.ne')
    ?_ (by positivity) ?_ ?_
  · rw [abs_of_pos (by positivity), div_lt_one hK]; unfold formCK; nlinarith
  · have e : 1 - X ^ 2 / formCK X = 2 * (1 - X) / formCK X := by
      field_simp; unfold formCK; ring
    rw [e, log_div (by nlinarith) hK.ne', log_mul (by norm_num) (by linarith)]
  · field_simp; ring

theorem formC_dLi4 : HasDerivAt (fun y => Li₂ ((1 - y) / formCT y))
    (-((2 * log X - log (formCT X)) * (-1 / (1 - X) - (2 * X - 1) / formCT X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hT := formCT_pos X
  have h1X : (1 - X) ≠ 0 := by linarith
  refine formC_li2_comp (((hasDerivAt_id X).const_sub 1).div (formC_hasDerivAt_T X) hT.ne')
    ?_ (div_pos (by linarith) hT).ne' ?_ ?_
  · rw [abs_of_pos (div_pos (by linarith) hT), div_lt_one hT]; unfold formCT; nlinarith
  · have e : 1 - (1 - X) / formCT X = X ^ 2 / formCT X := by
      field_simp; unfold formCT; ring
    rw [e, log_div (by positivity) hT.ne', log_pow]; push_cast; ring
  · simp only [id]; field_simp

theorem formC_dLi5 : HasDerivAt (fun y => Li₂ (-(y * (2 - y)) / formCK y))
    (-((log 2 - log (formCK X)) * (1 / X - 1 / (2 - X) - (2 * X - 2) / formCK X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hK := formCK_pos X
  have h2X : (2 - X) ≠ 0 := by linarith
  have hd : HasDerivAt (fun y => -(y * (2 - y))) (-(1 * (2 - X) + X * (-1))) X :=
    ((hasDerivAt_id X).mul ((hasDerivAt_id X).const_sub 2)).neg
  refine formC_li2_comp (hd.div (formC_hasDerivAt_K X) hK.ne') ?_ ?_ ?_ ?_
  · rw [abs_lt, lt_div_iff₀ hK, div_lt_iff₀ hK]; unfold formCK
    constructor <;> nlinarith
  · exact div_ne_zero (neg_ne_zero.2 (mul_pos h0 (by linarith)).ne') hK.ne'
  · have e : 1 - -(X * (2 - X)) / formCK X = 2 / formCK X := by
      field_simp; unfold formCK; ring
    rw [e, log_div (by norm_num) hK.ne']
  · field_simp; ring

theorem formC_dLi6 : HasDerivAt (fun y => Li₂ (formCT y))
    (-((log X + log (1 - X)) * ((2 * X - 1) / formCT X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hT := formCT_pos X
  refine formC_li2_comp (formC_hasDerivAt_T X) ?_ hT.ne' ?_ ?_
  · rw [abs_of_pos hT]; unfold formCT; nlinarith
  · have e : 1 - formCT X = X * (1 - X) := by unfold formCT; ring
    rw [e, log_mul h0.ne' (by linarith)]
  · field_simp

theorem formC_dLi7 : HasDerivAt (fun y => Li₂ ((1 - y) ^ 2))
    (-((log X + log (2 - X)) * (-2 / (1 - X)))) X := by
  obtain ⟨h0, h1⟩ := hX
  have h1X : (1 - X) ≠ 0 := by linarith
  refine formC_li2_comp (((hasDerivAt_id X).const_sub 1).pow 2) ?_ (by positivity) ?_ ?_
  · rw [abs_of_pos (by positivity)]; nlinarith
  · have e : 1 - (1 - X) ^ 2 = X * (2 - X) := by ring
    rw [e, log_mul h0.ne' (by linarith)]
  · simp only [id]; field_simp; ring

theorem formC_dLi8 : HasDerivAt (fun y => Li₂ (y ^ 2 / formCT y))
    (-((log (1 - X) - log (formCT X)) * (2 / X - (2 * X - 1) / formCT X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hT := formCT_pos X
  refine formC_li2_comp ((hasDerivAt_pow 2 X).div (formC_hasDerivAt_T X) hT.ne')
    ?_ (by positivity) ?_ ?_
  · rw [abs_of_pos (by positivity), div_lt_one hT]; unfold formCT; nlinarith
  · have e : 1 - X ^ 2 / formCT X = (1 - X) / formCT X := by
      field_simp; unfold formCT; ring
    rw [e, log_div (by linarith) hT.ne']
  · field_simp; ring

theorem formC_dLi9 : HasDerivAt (fun y => Li₂ (-y ^ 2 / formCK y))
    (-((log 2 + log (formCT X) - log (formCK X)) * (2 / X - (2 * X - 2) / formCK X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hK := formCK_pos X
  have hT := formCT_pos X
  refine formC_li2_comp ((hasDerivAt_pow 2 X).neg.div (formC_hasDerivAt_K X) hK.ne')
    ?_ ?_ ?_ ?_
  · rw [abs_lt, lt_div_iff₀ hK, div_lt_iff₀ hK]; unfold formCK
    constructor <;> nlinarith
  · exact div_ne_zero (neg_ne_zero.2 (by positivity)) hK.ne'
  · have e : 1 - -X ^ 2 / formCK X = 2 * formCT X / formCK X := by
      field_simp; unfold formCK formCT; ring
    rw [e, log_div (by positivity) hK.ne', log_mul (by norm_num) hT.ne']
  · simp only [Pi.neg_apply]; field_simp; ring

theorem formC_dLi10 : HasDerivAt (fun y => Li₂ (1 - y)) (-(log X * (-1 / (1 - X)))) X := by
  obtain ⟨h0, h1⟩ := hX
  have h1X : (1 - X) ≠ 0 := by linarith
  refine formC_li2_comp ((hasDerivAt_id X).const_sub 1) ?_ h1X ?_ ?_
  · rw [abs_lt]; constructor <;> linarith
  · ring_nf
  · show -1 = -1 / (1 - X) * (1 - X)
    field_simp

theorem formC_dLi11 : HasDerivAt (fun y => Li₂ (y * (2 - y) / formCK y))
    (-((log 2 + 2 * log (1 - X) - log (formCK X)) *
      (1 / X - 1 / (2 - X) - (2 * X - 2) / formCK X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hK := formCK_pos X
  have h2X : (2 - X) ≠ 0 := by linarith
  have hd : HasDerivAt (fun y => y * (2 - y)) (1 * (2 - X) + X * (-1)) X :=
    (hasDerivAt_id X).mul ((hasDerivAt_id X).const_sub 2)
  have hp : 0 < X * (2 - X) := mul_pos h0 (by linarith)
  refine formC_li2_comp (hd.div (formC_hasDerivAt_K X) hK.ne') ?_ (by positivity) ?_ ?_
  · rw [abs_of_pos (by positivity), div_lt_one hK]; unfold formCK; nlinarith
  · have e : 1 - X * (2 - X) / formCK X = 2 * (1 - X) ^ 2 / formCK X := by
      field_simp; unfold formCK; ring
    rw [e, log_div (by nlinarith) hK.ne', log_mul (by norm_num) (by nlinarith), log_pow]
    push_cast; ring
  · field_simp; ring

theorem formC_dLi12 : HasDerivAt (fun y => Li₂ ((1 - y) ^ 2 / formCT y))
    (-((log X - log (formCT X)) * (-2 / (1 - X) - (2 * X - 1) / formCT X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hT := formCT_pos X
  have h1X : (1 - X) ≠ 0 := by linarith
  refine formC_li2_comp ((((hasDerivAt_id X).const_sub 1).pow 2).div (formC_hasDerivAt_T X)
    hT.ne') ?_ (by positivity) ?_ ?_
  · rw [abs_of_pos (by positivity), div_lt_one hT]; unfold formCT; nlinarith
  · have e : 1 - (1 - X) ^ 2 / formCT X = X / formCT X := by
      field_simp; unfold formCT; ring
    rw [e, log_div h0.ne' hT.ne']
  · simp only [Pi.pow_apply, id]; field_simp; ring

theorem formC_dLi13 : HasDerivAt (fun y => Li₂ (formCT y / formCK y))
    (-((log (1 - X) - log (formCK X)) * ((2 * X - 1) / formCT X - (2 * X - 2) / formCK X))) X := by
  obtain ⟨h0, h1⟩ := hX
  have hK := formCK_pos X
  have hT := formCT_pos X
  refine formC_li2_comp ((formC_hasDerivAt_T X).div (formC_hasDerivAt_K X) hK.ne')
    ?_ (by positivity) ?_ ?_
  · rw [abs_of_pos (by positivity), div_lt_one hK]; unfold formCK formCT; nlinarith
  · have e : 1 - formCT X / formCK X = (1 - X) / formCK X := by
      field_simp; unfold formCK formCT; ring
    rw [e, log_div (by linarith) hK.ne']
  · field_simp

theorem formC_dLiW : HasDerivAt (fun y => Li₂ (y - 1)) (-(log (2 - X) * (1 / (X - 1)))) X := by
  obtain ⟨h0, h1⟩ := hX
  have h1X : (X - 1) ≠ 0 := by linarith
  refine formC_li2_comp ((hasDerivAt_id X).sub_const 1) ?_ h1X ?_ ?_
  · show |X - 1| < 1
    rw [abs_lt]; constructor <;> linarith
  · show log (1 - (X - 1)) = log (2 - X)
    ring_nf
  · show (1 : ℝ) = 1 / (X - 1) * (X - 1)
    field_simp

end terms

/-- **The derivative of `formCDel` vanishes** on `(0, 1)`. -/
theorem hasDerivAt_formCDel {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) : HasDerivAt formCDel 0 X := by
  obtain ⟨h0, h1⟩ := hX
  have hK := formCK_pos X
  have hT := formCT_pos X
  have h1X : 0 < 1 - X := by linarith
  have h2X : 0 < 2 - X := by linarith
  have lT := (formC_hasDerivAt_T X).log hT.ne'
  have lK := (formC_hasDerivAt_K X).log hK.ne'
  have l1 := ((hasDerivAt_id X).const_sub 1).log h1X.ne'
  have l2 := ((hasDerivAt_id X).const_sub 2).log h2X.ne'
  have lX := (hasDerivAt_id X).log h0.ne'
  have hX : X ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have h := (formC_dLi1 hX).neg.sub (formC_dLi2 hX)
  have h := ((((h.sub (formC_dLi3 hX)).sub (formC_dLi4 hX)).sub (formC_dLi5 hX)).sub
    (formC_dLi6 hX)).sub (formC_dLi7 hX)
  have h := ((((h.add (formC_dLi8 hX)).add (formC_dLi9 hX)).add (formC_dLi10 hX)).add
    (formC_dLi11 hX)).add (formC_dLi12 hX)
  have h := (h.add (formC_dLi13 hX)).add_const (π ^ 2 / 6)
  have hW := ((((formC_dLiW hX).const_mul 4).add
    ((formC_dLi10 hX).const_mul 2)).add ((l1.const_mul 2).mul l2)).add (lX.mul l1)
  have hD := (((h.add ((lT.pow 2).div_const 2)).sub (l1.mul lT)).sub (lK.mul lT)).add hW
  have e : formCDel = fun y => -Li₂ y - Li₂ (1 / formCK y) - Li₂ (y ^ 2 / formCK y) -
      Li₂ ((1 - y) / formCT y) - Li₂ (-(y * (2 - y)) / formCK y) - Li₂ (formCT y) -
      Li₂ ((1 - y) ^ 2) + Li₂ (y ^ 2 / formCT y) + Li₂ (-y ^ 2 / formCK y) + Li₂ (1 - y) +
      Li₂ (y * (2 - y) / formCK y) + Li₂ ((1 - y) ^ 2 / formCT y) +
      Li₂ (formCT y / formCK y) + π ^ 2 / 6 + log (formCT y) ^ 2 / 2 -
      log (1 - y) * log (formCT y) - log (formCK y) * log (formCT y) +
      (4 * Li₂ (y - 1) + 2 * Li₂ (1 - y) + 2 * log (1 - y) * log (2 - y) +
        log (id y) * log (1 - id y)) := by
    funext y
    simp only [formCDel, formCLi, formCW, id]
  rw [e]
  refine hD.congr_deriv ?_
  have hX1 : X - 1 ≠ 0 := by linarith
  have hX0 := h0.ne'
  have h1X' := h1X.ne'
  have h2X' := h2X.ne'
  have hK' := hK.ne'
  have hT' := hT.ne'
  simp only [id]
  field_simp
  ring

/-- `Li₂ ∘ g → Li₂ (g 0)` at `0⁺` for `g` continuous at `0` with values in `[-1, 1]` on `(0, 1)`. -/
theorem formC_tendsto_Li2 {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    (hs : ∀ X ∈ Ioo (0 : ℝ) 1, g X ∈ Icc (-1 : ℝ) 1) (h0 : g 0 ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun X => Li₂ (g X)) (𝓝[>] 0) (𝓝 (Li₂ (g 0))) :=
  tendsto_Li₂_comp h0 (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_of_mem (Ioo_mem_nhdsGT one_pos) hs)

theorem formC_mem_Icc {a b : ℝ} (hb : 0 < b) (h1 : -b ≤ a) (h2 : a ≤ b) :
    a / b ∈ Icc (-1 : ℝ) 1 :=
  ⟨by rw [le_div_iff₀ hb]; linarith, by rw [div_le_iff₀ hb]; linarith⟩

/-- **The limit at `0⁺`**: `formCDel → 0`. -/
theorem tendsto_formCDel : Tendsto formCDel (𝓝[>] 0) (𝓝 0) := by
  have cK : Continuous formCK := by unfold formCK; fun_prop
  have cT : Continuous formCT := by unfold formCT; fun_prop
  have K0 : formCK 0 = 2 := by norm_num [formCK]
  have T0 : formCT 0 = 1 := by norm_num [formCT]
  have hK0 : formCK 0 ≠ 0 := by rw [K0]; norm_num
  have hT0 : formCT 0 ≠ 0 := by rw [T0]; norm_num
  have cl : ∀ {g : ℝ → ℝ}, Continuous g → 0 < g 0 →
      Tendsto (fun X => log (g X)) (𝓝[>] 0) (𝓝 (log (g 0))) := fun hg h =>
    ((continuousAt_log h.ne').tendsto.comp (hg.tendsto 0)).mono_left nhdsWithin_le_nhds
  have bK : ∀ X ∈ Ioo (0 : ℝ) 1, 1 < formCK X ∧ formCK X < 2 := fun X hX => by
    obtain ⟨h0, h1⟩ := hX; unfold formCK; constructor <;> nlinarith
  have bT : ∀ X ∈ Ioo (0 : ℝ) 1, 3 / 4 ≤ formCT X ∧ formCT X < 1 := fun X hX => by
    obtain ⟨h0, h1⟩ := hX; unfold formCT; constructor <;> nlinarith [sq_nonneg (X - 1 / 2)]
  have t1 := formC_tendsto_Li2 (g := fun X => X) continuousAt_id
    (fun X hX => ⟨by linarith [hX.1], hX.2.le⟩) (by norm_num)
  have t2 := formC_tendsto_Li2 (g := fun X => 1 / formCK X)
    ((continuous_const.div cK fun X => (formCK_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCK_pos X) (by linarith [bK X hX]) (by linarith [bK X hX]))
    (formC_mem_Icc (formCK_pos 0) (by rw [K0]; norm_num) (by rw [K0]; norm_num))
  have t3 := formC_tendsto_Li2 (g := fun X => X ^ 2 / formCK X)
    (((continuous_pow 2).div cK fun X => (formCK_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCK_pos X) (by nlinarith [bK X hX])
      (by obtain ⟨h0, h1⟩ := hX; nlinarith [bK X ⟨h0, h1⟩]))
    (formC_mem_Icc (formCK_pos 0) (by rw [K0]; norm_num) (by rw [K0]; norm_num))
  have t4 := formC_tendsto_Li2 (g := fun X => (1 - X) / formCT X)
    (((continuous_const.sub continuous_id).div cT fun X => (formCT_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCT_pos X) (by linarith [hX.2, bT X hX])
      (by obtain ⟨h0, h1⟩ := hX; unfold formCT; nlinarith))
    (formC_mem_Icc (formCT_pos 0) (by rw [T0]; norm_num) (by rw [T0]; norm_num))
  have t5 := formC_tendsto_Li2 (g := fun X => -(X * (2 - X)) / formCK X)
    (((continuous_id.mul (continuous_const.sub continuous_id)).neg.div cK
      fun X => (formCK_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCK_pos X)
      (by obtain ⟨h0, h1⟩ := hX; unfold formCK; nlinarith)
      (by obtain ⟨h0, h1⟩ := hX; nlinarith [bK X ⟨h0, h1⟩]))
    (formC_mem_Icc (formCK_pos 0) (by rw [K0]; norm_num) (by rw [K0]; norm_num))
  have t6 := formC_tendsto_Li2 (g := formCT) cT.continuousAt
    (fun X hX => ⟨by linarith [bT X hX], (bT X hX).2.le⟩) (by rw [T0]; norm_num)
  have t7 := formC_tendsto_Li2 (g := fun X => (1 - X) ^ 2)
    ((continuous_const.sub continuous_id).pow 2).continuousAt
    (fun X hX => ⟨by nlinarith, by obtain ⟨h0, h1⟩ := hX; nlinarith⟩) (by norm_num)
  have t8 := formC_tendsto_Li2 (g := fun X => X ^ 2 / formCT X)
    (((continuous_pow 2).div cT fun X => (formCT_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCT_pos X) (by nlinarith [bT X hX])
      (by obtain ⟨h0, h1⟩ := hX; unfold formCT; nlinarith))
    (formC_mem_Icc (formCT_pos 0) (by rw [T0]; norm_num) (by rw [T0]; norm_num))
  have t9 := formC_tendsto_Li2 (g := fun X => -X ^ 2 / formCK X)
    (((continuous_pow 2).neg.div cK fun X => (formCK_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCK_pos X)
      (by obtain ⟨h0, h1⟩ := hX; nlinarith [bK X ⟨h0, h1⟩])
      (by nlinarith [bK X hX]))
    (formC_mem_Icc (formCK_pos 0) (by rw [K0]; norm_num) (by rw [K0]; norm_num))
  have t10 := formC_tendsto_Li2 (g := fun X => 1 - X)
    (continuous_const.sub continuous_id).continuousAt
    (fun X hX => ⟨by linarith [hX.2], by linarith [hX.1]⟩) (by norm_num)
  have t11 := formC_tendsto_Li2 (g := fun X => X * (2 - X) / formCK X)
    (((continuous_id.mul (continuous_const.sub continuous_id)).div cK
      fun X => (formCK_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCK_pos X)
      (by obtain ⟨h0, h1⟩ := hX; nlinarith [bK X ⟨h0, h1⟩])
      (by obtain ⟨h0, h1⟩ := hX; unfold formCK; nlinarith))
    (formC_mem_Icc (formCK_pos 0) (by rw [K0]; norm_num) (by rw [K0]; norm_num))
  have t12 := formC_tendsto_Li2 (g := fun X => (1 - X) ^ 2 / formCT X)
    ((((continuous_const.sub continuous_id).pow 2).div cT
      fun X => (formCT_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCT_pos X) (by nlinarith [bT X hX])
      (by obtain ⟨h0, h1⟩ := hX; unfold formCT; nlinarith))
    (formC_mem_Icc (formCT_pos 0) (by rw [T0]; norm_num) (by rw [T0]; norm_num))
  have t13 := formC_tendsto_Li2 (g := fun X => formCT X / formCK X)
    ((cT.div cK fun X => (formCK_pos X).ne').continuousAt)
    (fun X hX => formC_mem_Icc (formCK_pos X) (by linarith [bT X hX, bK X hX])
      (by obtain ⟨h0, h1⟩ := hX; unfold formCT formCK; nlinarith))
    (formC_mem_Icc (formCK_pos 0) (by rw [K0, T0]; norm_num) (by rw [K0, T0]; norm_num))
  have tW := formC_tendsto_Li2 (g := fun X => X - 1)
    (continuous_id.sub continuous_const).continuousAt
    (fun X hX => ⟨by linarith [hX.1], by linarith [hX.2]⟩) (by norm_num)
  have lT := cl cT (formCT_pos 0)
  have lK := cl cK (formCK_pos 0)
  have l1 := cl (g := fun X => 1 - X) (continuous_const.sub continuous_id) (by norm_num)
  have l2 := cl (g := fun X => 2 - X) (continuous_const.sub continuous_id) (by norm_num)
  have h := (((((t1.neg.sub t2).sub t3).sub t4).sub t5).sub t6).sub t7
  have h := (((((h.add t8).add t9).add t10).add t11).add t12).add t13
  have h := (((h.add_const (π ^ 2 / 6)).add ((lT.pow 2).div_const 2)).sub (l1.mul lT)).sub
    (lK.mul lT)
  have h := h.add ((((tW.const_mul 4).add (t10.const_mul 2)).add ((l1.const_mul 2).mul l2)).add
    tendsto_log_mul_log_one_sub_zero)
  convert h using 2
  · simp only [formCDel, formCLi, formCW]
  · norm_num [K0, T0]
    rw [Li₂_one, Li₂_neg_one]
    ring

/-- **The dilogarithm identity**: `formCDel = 0` on `(0, 1)`. -/
theorem formCDel_eq_zero {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) : formCDel X = 0 := by
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx => (hasDerivAt_formCDel hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hasDerivAt_formCDel hx).deriv)
  have hc' : Tendsto formCDel (𝓝[>] 0) (𝓝 c) :=
    tendsto_const_nhds.congr' (eventually_of_mem (Ioo_mem_nhdsGT one_pos)
      fun x hx => (hc x hx).symm)
  rw [hc X hX, tendsto_nhds_unique hc' tendsto_formCDel]

end QED.ChainProof.SetCK

end
