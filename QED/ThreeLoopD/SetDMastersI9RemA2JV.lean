/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA2JD
public import QED.Polylog.HPLValues4

/-!
# Set (d), master `I₉`: the value of the one-dimensional `A₂'` integral

With the antiderivative `Ψ = A + B/x + C/x²` of `x ↦ j(1 - x)`
(`QED.ThreeLoopD.hasDerivAt_i9A2Psi`), `∫₀¹ j = Ψ(1⁻) - Ψ(0⁺)`.

* At `x → 0⁺` the words of `C` contain three letters `1` and those of `B` (apart from
  `H(1)`, `H(0, 1)`, `H(1, 0)`) two, so `|H(w; x)| ≤ c x^(5/2)`, resp. `c x^(3/2)`
  (`QED.ThreeLoopD.I9A2Bnd`, built letter by letter); the rest of `A` tends to `0`, and the
  singular part `-π² log x + (2π² H(1) + 3π² H(0, 1) + π² H(1, 0))/x` tends to `4π²`.
* At `x → 1⁻`, `Ψ = c₀ + H(1) c₁ + H(1)² c₂ + (1 - x)(…)` with `c₀, c₁, c₂` combinations of
  words starting with `0` (shuffle algebra), `c₁(1) = c₂(1) = 0`, `|c_k(x) - c_k(1)| ≤
  K (1 - x)^(1/2)` (`QED.ThreeLoopD.I9A2Rate`), and `c₀(1) = 9π²/2 + 45 ζ(3) - 11π⁴/30` from the
  multiple zeta values of weight at most four.

## Main results

* `QED.ThreeLoopD.tendsto_i9A2Psi_zero`, `QED.ThreeLoopD.tendsto_i9A2Psi_one`: the limits.
* `QED.ThreeLoopD.integral_i9A2j`: `∫₀¹ j = π²/2 + 45 ζ(3) - 11π⁴/30`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### Power bounds at `0` -/

/-- `|f x| ≤ C x ^ r` on `(0, 1/2]`. -/
def I9A2Bnd (f : ℝ → ℝ) (r : ℝ) : Prop := ∃ C, ∀ x ∈ Ioc (0 : ℝ) (1 / 2), |f x| ≤ C * x ^ r

theorem I9A2Bnd.add {f g : ℝ → ℝ} {r : ℝ} (hf : I9A2Bnd f r) (hg : I9A2Bnd g r) :
    I9A2Bnd (fun x => f x + g x) r := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun x hx => ?_⟩
  have := hC x hx
  have := hD x hx
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ (C + D) * x ^ r := by linarith

theorem I9A2Bnd.const_mul {f : ℝ → ℝ} {r : ℝ} (hf : I9A2Bnd f r) (c : ℝ) :
    I9A2Bnd (fun x => c * f x) r := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨|c| * C, fun x hx => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x hx) (abs_nonneg c)

theorem i9A2Bnd_mono {f : ℝ → ℝ} {r s : ℝ} (hf : I9A2Bnd f r) (hrs : s ≤ r) : I9A2Bnd f s := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨|C|, fun x hx => ?_⟩
  have h1 : x ^ r ≤ x ^ s := rpow_le_rpow_of_exponent_ge hx.1 (by linarith [hx.2]) hrs
  calc |f x| ≤ C * x ^ r := hC x hx
    _ ≤ |C| * x ^ r := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity [hx.1])
    _ ≤ |C| * x ^ s := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)

theorem i9A2Bnd_nil : I9A2Bnd (hpl []) 0 :=
  ⟨1, fun x _ => by simp⟩

theorem i9A2Bnd_zero : I9A2Bnd (hpl [zero]) (-1 / 8) := by
  obtain ⟨C, -, hC⟩ := abs_log_pow_le 1 (δ := 1 / 8) (by norm_num)
  refine ⟨C, fun x hx => ?_⟩
  rw [hpl_zero]
  have := hC x ⟨hx.1, by linarith [hx.2]⟩
  rw [pow_one] at this
  convert this using 2
  norm_num

theorem i9A2Bnd_cons_zero {w : List Letter} {r : ℝ} (hw : I9A2Bnd (hpl w) r) (hr : 0 < r)
    (hnz : ¬AllZero (zero :: w)) : I9A2Bnd (hpl (zero :: w)) r := by
  obtain ⟨C, hC⟩ := hw
  refine ⟨|C| / r, fun x hx => ?_⟩
  rw [hpl_cons_of_not_allZero hnz]
  have h := abs_integral_le_of_le_rpow (g := fun t => zero.kernel t * hpl w t) (K := |C|)
    (r := r - 1) hx.1.le (by linarith) fun t ht => by
      have ht1 : t ∈ Ioc (0 : ℝ) (1 / 2) := ⟨ht.1, ht.2.trans hx.2⟩
      rw [kernel_zero, abs_mul, abs_inv, abs_of_pos ht.1, rpow_sub ht.1, rpow_one]
      calc t⁻¹ * |hpl w t| ≤ t⁻¹ * (|C| * t ^ r) :=
            mul_le_mul_of_nonneg_left ((hC t ht1).trans (mul_le_mul_of_nonneg_right
              (le_abs_self C) (by positivity [ht.1]))) (by positivity [ht.1])
        _ = |C| * (t ^ r / t) := by field_simp
  simp only [sub_add_cancel] at h
  calc _ ≤ |C| * (x ^ r / r) := h
    _ = |C| / r * x ^ r := by ring

theorem i9A2Bnd_cons_one {w : List Letter} {r : ℝ} (hw : I9A2Bnd (hpl w) r) (hr : -1 < r) :
    I9A2Bnd (hpl (one :: w)) (r + 1) := by
  obtain ⟨C, hC⟩ := hw
  refine ⟨2 * |C| / (r + 1), fun x hx => ?_⟩
  rw [hpl_cons_of_ne_zero (by decide)]
  have h := abs_integral_le_of_le_rpow (g := fun t => one.kernel t * hpl w t) (K := 2 * |C|)
    (r := r) hx.1.le hr fun t ht => by
      have ht1 : t ∈ Ioc (0 : ℝ) (1 / 2) := ⟨ht.1, ht.2.trans hx.2⟩
      have hq : 0 < 1 - t := by linarith [ht1.2]
      have hk : (1 - t)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hq (by norm_num)]; linarith [ht1.2]
      rw [kernel_one, abs_mul, abs_inv, abs_of_pos hq]
      calc (1 - t)⁻¹ * |hpl w t| ≤ 2 * (|C| * t ^ r) :=
            mul_le_mul hk ((hC t ht1).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
              (by positivity [ht.1]))) (abs_nonneg _) (by norm_num)
        _ = 2 * |C| * t ^ r := by ring
  calc _ ≤ 2 * |C| * (x ^ (r + 1) / (r + 1)) := h
    _ = 2 * |C| / (r + 1) * x ^ (r + 1) := by ring

theorem tendsto_div_pow_of_i9A2Bnd {f : ℝ → ℝ} {r : ℝ} (hf : I9A2Bnd f r) (n : ℕ)
    (hr : (n : ℝ) < r) : Tendsto (fun x => f x / x ^ n) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf
  refine tendsto_zero_of_abs_le_rpow (C := C) (r := r - n) (b := 1 / 2) (by linarith)
    (by norm_num) fun x hx => ?_
  rw [abs_div, abs_of_pos (pow_pos hx.1 n), rpow_sub hx.1, rpow_natCast, div_le_iff₀
    (pow_pos hx.1 n)]
  calc |f x| ≤ C * x ^ r := hC x hx
    _ = C * (x ^ r / x ^ n) * x ^ n := by rw [mul_assoc C, div_mul_cancel₀ _ (pow_pos hx.1 n).ne']

/-! ### Behaviour at `1` -/

theorem i9A2_tendsto_one_sub_rpow :
    Tendsto (fun x : ℝ => (1 - x) ^ (1 / 2 : ℝ)) (𝓝[<] 1) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (1 - x) ^ (1 / 2 : ℝ)) (𝓝 1) (𝓝 ((1 - 1) ^ (1 / 2 : ℝ))) :=
    ((continuous_const.sub continuous_id).rpow_const fun _ => Or.inr (by norm_num)).tendsto 1
  rw [sub_self, zero_rpow (by norm_num)] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem i9A2_tendsto_one_sub_mul_hpl (w : List Letter) :
    Tendsto (fun x => (1 - x) * hpl w x) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := abs_hpl_le_one_sub_rpow w (ε := 1 / 2) (by norm_num)
  have hl := i9A2_tendsto_one_sub_rpow.const_mul C
  rw [mul_zero] at hl
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with x hx
  have hq : 0 < 1 - x := by linarith [hx.2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hq]
  calc (1 - x) * |hpl w x| ≤ (1 - x) * (C * (1 - x) ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hC x hx) hq.le
    _ = C * (1 - x) ^ (1 / 2 : ℝ) := by
        rw [mul_left_comm, ← rpow_one_add' hq.le (by norm_num)]
        congr 2
        norm_num

/-- `A` without its `log x` term. -/
noncomputable def i9A2PsiAr (x : ℝ) : ℝ :=
  (-π ^ 2) * hpl [one] x +
    (27 - 2 * π ^ 2) * hpl [zero, one] x +
    (27 - 2 * π ^ 2) * hpl [one, one] x +
    (-12) * hpl [zero, zero, one] x +
    (-18) * hpl [zero, one, zero] x +
    (21) * hpl [zero, one, one] x +
    (-12) * hpl [one, zero, one] x +
    (-18) * hpl [one, one, zero] x +
    (21) * hpl [one, one, one] x +
    (12) * hpl [zero, zero, one, one] x +
    (-6) * hpl [zero, one, zero, one] x +
    (-18) * hpl [zero, one, one, zero] x +
    (12) * hpl [zero, one, one, one] x +
    (12) * hpl [one, zero, one, one] x +
    (-6) * hpl [one, one, zero, one] x +
    (-18) * hpl [one, one, one, zero] x +
    (12) * hpl [one, one, one, one] x

/-- `B` without its terms of weight at most two that are singular in `B/x`. -/
noncomputable def i9A2PsiBr (x : ℝ) : ℝ :=
  (-27 + 4 * π ^ 2) * hpl [one, one] x +
    (-12) * hpl [zero, one, one] x +
    (6) * hpl [one, zero, one] x +
    (18) * hpl [one, one, zero] x +
    (-12) * hpl [one, one, one] x +
    (-24) * hpl [zero, zero, one, one] x +
    (24) * hpl [zero, one, one, zero] x +
    (-36) * hpl [zero, one, one, one] x +
    (12) * hpl [one, zero, zero, one] x +
    (12) * hpl [one, zero, one, zero] x +
    (-12) * hpl [one, zero, one, one] x +
    (12) * hpl [one, one, zero, one] x +
    (36) * hpl [one, one, one, zero] x +
    (-24) * hpl [one, one, one, one] x

theorem i9A2Bnd_i9A2PsiBr : I9A2Bnd i9A2PsiBr (3 / 2) := by
  unfold i9A2PsiBr
  have b0 : I9A2Bnd (fun x => (-27 + 4 * π ^ 2) * hpl [one, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num))
        (by norm_num)).const_mul (-27 + 4 * π ^ 2)
  have b1 : I9A2Bnd (fun x => (-12) * hpl [zero, one, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_zero (i9A2Bnd_cons_one (i9A2Bnd_cons_one i9A2Bnd_nil
        (by norm_num)) (by norm_num)) (by norm_num) (by decide)) (by norm_num)).const_mul (-12)
  have b2 : I9A2Bnd (fun x => (6) * hpl [one, zero, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_zero (i9A2Bnd_cons_one i9A2Bnd_nil
        (by norm_num)) (by norm_num) (by decide)) (by norm_num)) (by norm_num)).const_mul (6)
  have b3 : I9A2Bnd (fun x => (18) * hpl [one, one, zero] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one i9A2Bnd_zero (by norm_num)) (by norm_num))
        (by norm_num)).const_mul (18)
  have b4 : I9A2Bnd (fun x => (-12) * hpl [one, one, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num))
        (by norm_num)) (by norm_num)) (by norm_num)).const_mul (-12)
  have b5 : I9A2Bnd (fun x => (-24) * hpl [zero, zero, one, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_zero (i9A2Bnd_cons_zero (i9A2Bnd_cons_one
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num)) (by norm_num) (by decide))
        (by norm_num) (by decide)) (by norm_num)).const_mul (-24)
  have b6 : I9A2Bnd (fun x => (24) * hpl [zero, one, one, zero] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_zero (i9A2Bnd_cons_one (i9A2Bnd_cons_one i9A2Bnd_zero
        (by norm_num)) (by norm_num)) (by norm_num) (by decide)) (by norm_num)).const_mul (24)
  have b7 : I9A2Bnd (fun x => (-36) * hpl [zero, one, one, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_zero (i9A2Bnd_cons_one (i9A2Bnd_cons_one
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)
        (by decide)) (by norm_num)).const_mul (-36)
  have b8 : I9A2Bnd (fun x => (12) * hpl [one, zero, zero, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_zero (i9A2Bnd_cons_zero
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num) (by decide)) (by norm_num)
        (by decide)) (by norm_num)) (by norm_num)).const_mul (12)
  have b9 : I9A2Bnd (fun x => (12) * hpl [one, zero, one, zero] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_zero (i9A2Bnd_cons_one i9A2Bnd_zero
        (by norm_num)) (by norm_num) (by decide)) (by norm_num)) (by norm_num)).const_mul (12)
  have b10 : I9A2Bnd (fun x => (-12) * hpl [one, zero, one, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_zero (i9A2Bnd_cons_one
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num)) (by norm_num) (by decide))
        (by norm_num)) (by norm_num)).const_mul (-12)
  have b11 : I9A2Bnd (fun x => (12) * hpl [one, one, zero, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one (i9A2Bnd_cons_zero
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num) (by decide)) (by norm_num))
        (by norm_num)) (by norm_num)).const_mul (12)
  have b12 : I9A2Bnd (fun x => (36) * hpl [one, one, one, zero] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one (i9A2Bnd_cons_one i9A2Bnd_zero
        (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)).const_mul (36)
  have b13 : I9A2Bnd (fun x => (-24) * hpl [one, one, one, one] x) (3 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one (i9A2Bnd_cons_one
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
        (by norm_num)).const_mul (-24)
  exact (((((((((((((b0.add b1).add b2).add b3).add b4).add b5).add b6).add b7).add b8).add b9).add
      b10).add b11).add b12).add b13)

theorem i9A2Bnd_i9A2PsiC : I9A2Bnd i9A2PsiC (5 / 2) := by
  unfold i9A2PsiC
  have b0 : I9A2Bnd (fun x => (-9) * hpl [one, one, one] x) (5 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num))
        (by norm_num)) (by norm_num)) (by norm_num)).const_mul (-9)
  have b1 : I9A2Bnd (fun x => (-12) * hpl [one, zero, one, one] x) (5 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_zero (i9A2Bnd_cons_one
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num)) (by norm_num) (by decide))
        (by norm_num)) (by norm_num)).const_mul (-12)
  have b2 : I9A2Bnd (fun x => (-18) * hpl [one, one, zero, one] x) (5 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one (i9A2Bnd_cons_zero
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num) (by decide)) (by norm_num))
        (by norm_num)) (by norm_num)).const_mul (-18)
  have b3 : I9A2Bnd (fun x => (-18) * hpl [one, one, one, zero] x) (5 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one (i9A2Bnd_cons_one i9A2Bnd_zero
        (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)).const_mul (-18)
  have b4 : I9A2Bnd (fun x => (12) * hpl [one, one, one, one] x) (5 / 2) :=
    (i9A2Bnd_mono (i9A2Bnd_cons_one (i9A2Bnd_cons_one (i9A2Bnd_cons_one
        (i9A2Bnd_cons_one i9A2Bnd_nil (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
        (by norm_num)).const_mul (12)
  exact ((((b0.add b1).add b2).add b3).add b4)

theorem tendsto_i9A2PsiAr_zero : Tendsto i9A2PsiAr (𝓝[>] 0) (𝓝 0) := by
  unfold i9A2PsiAr
  simpa using (((((((((((((((((tendsto_hpl_zero (w := [one]) (by decide)).const_mul (-π ^ 2)).add
    ((tendsto_hpl_zero (w := [zero, one]) (by decide)).const_mul (27 - 2 * π ^ 2))).add
    ((tendsto_hpl_zero (w := [one, one]) (by decide)).const_mul (27 - 2 * π ^ 2))).add
    ((tendsto_hpl_zero (w := [zero, zero, one]) (by decide)).const_mul (-12))).add
    ((tendsto_hpl_zero (w := [zero, one, zero]) (by decide)).const_mul (-18))).add
    ((tendsto_hpl_zero (w := [zero, one, one]) (by decide)).const_mul (21))).add
    ((tendsto_hpl_zero (w := [one, zero, one]) (by decide)).const_mul (-12))).add
    ((tendsto_hpl_zero (w := [one, one, zero]) (by decide)).const_mul (-18))).add
    ((tendsto_hpl_zero (w := [one, one, one]) (by decide)).const_mul (21))).add
    ((tendsto_hpl_zero (w := [zero, zero, one, one]) (by decide)).const_mul (12))).add
    ((tendsto_hpl_zero (w := [zero, one, zero, one]) (by decide)).const_mul (-6))).add
    ((tendsto_hpl_zero (w := [zero, one, one, zero]) (by decide)).const_mul (-18))).add
    ((tendsto_hpl_zero (w := [zero, one, one, one]) (by decide)).const_mul (12))).add
    ((tendsto_hpl_zero (w := [one, zero, one, one]) (by decide)).const_mul (12))).add
    ((tendsto_hpl_zero (w := [one, one, zero, one]) (by decide)).const_mul (-6))).add
    ((tendsto_hpl_zero (w := [one, one, one, zero]) (by decide)).const_mul (-18))).add
    ((tendsto_hpl_zero (w := [one, one, one, one]) (by decide)).const_mul (12))

theorem tendsto_one_sub_mul_i9A2PsiB :
    Tendsto (fun x => (1 - x) * i9A2PsiB x) (𝓝[<] 1) (𝓝 0) := by
  have h := (((((((((((((((((i9A2_tendsto_one_sub_mul_hpl [one]).const_mul (2 * π ^ 2)).add
    ((i9A2_tendsto_one_sub_mul_hpl [zero, one]).const_mul (3 * π ^ 2))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, zero]).const_mul (π ^ 2))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one]).const_mul (-27 + 4 * π ^ 2))).add
    ((i9A2_tendsto_one_sub_mul_hpl [zero, one, one]).const_mul (-12))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, zero, one]).const_mul (6))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one, zero]).const_mul (18))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one, one]).const_mul (-12))).add
    ((i9A2_tendsto_one_sub_mul_hpl [zero, zero, one, one]).const_mul (-24))).add
    ((i9A2_tendsto_one_sub_mul_hpl [zero, one, one, zero]).const_mul (24))).add
    ((i9A2_tendsto_one_sub_mul_hpl [zero, one, one, one]).const_mul (-36))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, zero, zero, one]).const_mul (12))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, zero, one, zero]).const_mul (12))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, zero, one, one]).const_mul (-12))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one, zero, one]).const_mul (12))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one, one, zero]).const_mul (36))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one, one, one]).const_mul (-24))
  simp only [mul_zero, add_zero] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [i9A2PsiB]
  ring

theorem tendsto_one_sub_mul_i9A2PsiC :
    Tendsto (fun x => (1 - x) * i9A2PsiC x) (𝓝[<] 1) (𝓝 0) := by
  have h := (((((i9A2_tendsto_one_sub_mul_hpl [one, one, one]).const_mul (-9)).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, zero, one, one]).const_mul (-12))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one, zero, one]).const_mul (-18))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one, one, zero]).const_mul (-18))).add
    ((i9A2_tendsto_one_sub_mul_hpl [one, one, one, one]).const_mul (12))
  simp only [mul_zero, add_zero] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [i9A2PsiC]
  ring

/-! ### The limit at `0` -/

theorem i9A2_tendsto_log_one_sub_div :
    Tendsto (fun x => Real.log (1 - x) / x) (𝓝[>] 0) (𝓝 (-1)) := by
  have hd : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num)
    simpa using this
  refine hd.tendsto_slope_zero_right.congr' (Eventually.of_forall fun t => ?_)
  simp [div_eq_inv_mul]

theorem i9A2_tendsto_Li₂_div : Tendsto (fun x => Li₂ x / x) (𝓝[>] 0) (𝓝 1) := by
  have hd := hasDerivAt_Li_tsum (k := 2) (by norm_num) (x := 0) (by norm_num)
  have h1 : (∑' n : ℕ, (0 : ℝ) ^ n / ((n : ℝ) + 1) ^ (2 - 1)) = 1 := by
    rw [tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
    simp
  rw [h1] at hd
  refine hd.tendsto_slope_zero_right.congr' (Eventually.of_forall fun t => ?_)
  simp [div_eq_inv_mul, Li_two]

theorem i9A2_tendsto_log_mul :
    Tendsto (fun x => Real.log x * (Real.log (1 - x) / x + 1)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := abs_log_pow_le 1 (δ := 1 / 2) (by norm_num)
  refine tendsto_zero_of_abs_le_rpow (C := 4 * C) (r := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) fun x hx => ?_
  have hx1 : |x| < 1 := by rw [abs_of_pos hx.1]; linarith [hx.2]
  have hlog := abs_log_sub_add_sum_range_le hx1 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_of_pos hx.1] at hlog
  have hq : 1 / 2 ≤ 1 - x := by linarith [hx.2]
  have h2 : |Real.log (1 - x) / x + 1| ≤ 4 * x := by
    have e : Real.log (1 - x) / x + 1 = (x + Real.log (1 - x)) / x := by
      field_simp [hx.1.ne']; ring
    rw [e, abs_div, abs_of_pos hx.1, div_le_iff₀ hx.1]
    calc |x + Real.log (1 - x)| ≤ x ^ 2 / (1 - x) := hlog
      _ ≤ x ^ 2 / (1 / 2) := div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) hq
      _ ≤ 4 * x * x := by nlinarith [hx.1]
  have hl := hC x ⟨hx.1, by linarith [hx.2]⟩
  rw [pow_one] at hl
  rw [abs_mul]
  have hxr : x * x ^ (-(1 / 2) : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← rpow_one_add' hx.1.le (by norm_num)]; norm_num
  calc |Real.log x| * |Real.log (1 - x) / x + 1| ≤ C * x ^ (-(1 / 2) : ℝ) * (4 * x) :=
        mul_le_mul hl h2 (abs_nonneg _) (by positivity [hx.1])
    _ = 4 * C * (x * x ^ (-(1 / 2) : ℝ)) := by ring
    _ = 4 * C * x ^ (1 / 2 : ℝ) := by rw [hxr]

/-- The part of `Ψ` that is singular at `0`. -/
noncomputable def i9A2PsiSing (x : ℝ) : ℝ :=
  -π ^ 2 * hpl [zero] x +
    (2 * π ^ 2 * hpl [one] x + 3 * π ^ 2 * hpl [zero, one] x + π ^ 2 * hpl [one, zero] x) / x

theorem tendsto_i9A2PsiSing : Tendsto i9A2PsiSing (𝓝[>] 0) (𝓝 (4 * π ^ 2)) := by
  have h := ((i9A2_tendsto_log_mul.const_mul (-π ^ 2)).add
    (i9A2_tendsto_log_one_sub_div.const_mul (-2 * π ^ 2))).add
    (i9A2_tendsto_Li₂_div.const_mul (2 * π ^ 2))
  have e : -π ^ 2 * 0 + -2 * π ^ 2 * -1 + 2 * π ^ 2 * 1 = 4 * π ^ 2 := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  simp only [i9A2PsiSing, hpl_zero, hpl_one hx, hpl_zero_one hx, hpl_one_zero hx, Li_two]
  field_simp [hx.1.ne']
  ring

theorem i9A2Psi_eq_zero_split (x : ℝ) :
    i9A2Psi x = i9A2PsiSing x + i9A2PsiAr x + i9A2PsiBr x / x ^ 1 + i9A2PsiC x / x ^ 2 := by
  simp only [i9A2Psi, i9A2PsiSing, i9A2PsiA, i9A2PsiAr, i9A2PsiB, i9A2PsiBr, pow_one]
  ring

/-- **`Ψ(x) → 4π²` as `x → 0⁺`.** -/
theorem tendsto_i9A2Psi_zero : Tendsto i9A2Psi (𝓝[>] 0) (𝓝 (4 * π ^ 2)) := by
  have h := ((tendsto_i9A2PsiSing.add tendsto_i9A2PsiAr_zero).add
    (tendsto_div_pow_of_i9A2Bnd i9A2Bnd_i9A2PsiBr 1 (by norm_num))).add
    (tendsto_div_pow_of_i9A2Bnd i9A2Bnd_i9A2PsiC 2 (by norm_num))
  simp only [add_zero] at h
  exact h.congr fun x => (i9A2Psi_eq_zero_split x).symm

/-! ### The limit at `1` -/

/-- `|f x - L| ≤ K (1 - x)^(1/2)` on `[1/2, 1)`. -/
def I9A2Rate (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∃ K, ∀ x ∈ Ico (1 / 2 : ℝ) 1, |f x - L| ≤ K * (1 - x) ^ (1 / 2 : ℝ)

theorem I9A2Rate.add {f g : ℝ → ℝ} {a b : ℝ} (hf : I9A2Rate f a) (hg : I9A2Rate g b) :
    I9A2Rate (fun x => f x + g x) (a + b) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨M, hM⟩ := hg
  refine ⟨K + M, fun x hx => ?_⟩
  have := hK x hx
  have := hM x hx
  calc |f x + g x - (a + b)| = |(f x - a) + (g x - b)| := by ring_nf
    _ ≤ |f x - a| + |g x - b| := abs_add_le _ _
    _ ≤ (K + M) * (1 - x) ^ (1 / 2 : ℝ) := by linarith

theorem I9A2Rate.const_mul {f : ℝ → ℝ} {a : ℝ} (hf : I9A2Rate f a) (c : ℝ) :
    I9A2Rate (fun x => c * f x) (c * a) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨|c| * K, fun x hx => ?_⟩
  rw [← mul_sub, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK x hx) (abs_nonneg c)

theorem i9A2Rate_const (c : ℝ) : I9A2Rate (fun _ => c) c :=
  ⟨0, fun x _ => by simp⟩

theorem i9A2Rate_zero : I9A2Rate (hpl [zero]) 0 := by
  refine ⟨2, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith [hx.1]
  have hq : 0 < 1 - x := by linarith [hx.2]
  rw [hpl_zero, sub_zero, abs_of_nonpos (Real.log_nonpos hx0.le hx.2.le)]
  have h1 := Real.one_sub_inv_le_log_of_pos hx0
  have h2 : 1 - x ≤ (1 - x) ^ (1 / 2 : ℝ) := by
    have := rpow_le_rpow_of_exponent_ge hq (by linarith [hx.1]) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    rwa [rpow_one] at this
  have h3 : x⁻¹ - 1 ≤ 2 * (1 - x) := by
    rw [inv_eq_one_div, div_sub_one hx0.ne', div_le_iff₀ hx0]; nlinarith [hx.1]
  nlinarith

theorem i9A2_integral_one_sub_rpow (x : ℝ) :
    ∫ t in x..1, (1 - t) ^ (-(1 / 2) : ℝ) = 2 * (1 - x) ^ (1 / 2 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) 1, sub_self,
    integral_rpow (Or.inl (by norm_num))]
  norm_num [zero_rpow]
  ring_nf

theorem i9A2Rate_hpl_zero_cons (u : List Letter) (hnz : ¬AllZero (zero :: u)) :
    I9A2Rate (hpl (zero :: u)) (hpl (zero :: u) 1) := by
  obtain ⟨C, hC0, hC⟩ := abs_hpl_le_one_sub_rpow u (ε := 1 / 2) (by norm_num)
  refine ⟨4 * C, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith [hx.1]
  set g : ℝ → ℝ := fun t => zero.kernel t * hpl u t with hg
  have hI := intervalIntegrable_kernel_mul_hpl_one (a := zero) (by decide) hnz
  have hIx := intervalIntegrable_kernel_mul_hpl hnz hx0 hx.2
  have e : hpl (zero :: u) x - hpl (zero :: u) 1 = -∫ t in x..1, g t := by
    rw [hpl_cons_of_not_allZero hnz]
    simp only
    rw [intervalIntegral.integral_interval_sub_left hIx hI, intervalIntegral.integral_symm]
  have hB : IntervalIntegrable (fun t => 2 * C * (1 - t) ^ (-(1 / 2) : ℝ)) volume x 1 := by
    have := ((intervalIntegral.intervalIntegrable_rpow' (a := 1 - x) (b := 0)
      (r := -(1 / 2)) (by norm_num)).comp_sub_left 1).const_mul (2 * C)
    simpa using this
  have hbd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc x 1 →
      ‖g t‖ ≤ 2 * C * (1 - t) ^ (-(1 / 2) : ℝ) := by
    have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
      rw [ae_iff]; simp
    filter_upwards [h1] with t ht1 ht
    have ht' : t ∈ Ico (1 / 2 : ℝ) 1 := ⟨by linarith [hx.1, ht.1], lt_of_le_of_ne ht.2 ht1⟩
    have ht0 : 0 < t := by linarith [ht'.1]
    have hk : t⁻¹ ≤ 2 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht'.1]
    rw [Real.norm_eq_abs]
    simp only [hg, kernel_zero]
    rw [abs_mul, abs_inv, abs_of_pos ht0]
    calc t⁻¹ * |hpl u t| ≤ 2 * (C * (1 - t) ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul hk (hC t ht') (abs_nonneg _) (by norm_num)
      _ = 2 * C * (1 - t) ^ (-(1 / 2) : ℝ) := by ring
  have hn := intervalIntegral.norm_integral_le_of_norm_le hx.2.le hbd hB
  rw [intervalIntegral.integral_const_mul, i9A2_integral_one_sub_rpow x] at hn
  rw [e, abs_neg, ← Real.norm_eq_abs]
  linarith

theorem i9A2_tendsto_one_sub_rpow' {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => (1 - x) ^ r) (𝓝[<] 1) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (1 - x) ^ r) (𝓝 1) (𝓝 ((1 - 1) ^ r)) :=
    ((continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hr.le).tendsto 1
  rw [sub_self, zero_rpow hr.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_hpl_one_pow_mul_of_rate {f : ℝ → ℝ} (hf : I9A2Rate f 0) (k : ℕ) :
    Tendsto (fun x => hpl [one] x ^ k * f x) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨C, hC0, hC⟩ := abs_log_pow_le k (δ := 1 / 4) (by norm_num)
  have hl := (i9A2_tendsto_one_sub_rpow' (r := 1 / 4) (by norm_num)).const_mul (C * K)
  rw [mul_zero] at hl
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with x hx
  have hq : 0 < 1 - x := by linarith [hx.2]
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have h1 := hK x ⟨hx.1.le, hx.2⟩
  rw [sub_zero] at h1
  have h2 := hC (1 - x) ⟨hq, by linarith [hx.1]⟩
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans h1
    exact nonneg_of_mul_nonneg_left this (by positivity)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, hpl_one hx', abs_neg]
  calc |Real.log (1 - x)| ^ k * |f x| ≤ C * (1 - x) ^ (-(1 / 4) : ℝ) *
        (K * (1 - x) ^ (1 / 2 : ℝ)) := mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    _ = C * K * ((1 - x) ^ (-(1 / 4) : ℝ) * (1 - x) ^ (1 / 2 : ℝ)) := by ring
    _ = C * K * (1 - x) ^ (1 / 4 : ℝ) := by
        rw [← rpow_add hq]; norm_num

/-- The `H(1)⁰` coefficient of `A + B + C`. -/
noncomputable def i9A2c0 (x : ℝ) : ℝ :=
  -π ^ 2 * hpl [zero] x + 27 * hpl [zero, one] x - 12 * hpl [zero, zero, one] x -
    18 * hpl [zero, one, zero] x + 21 * hpl [zero, one, one] x -
    36 * hpl [zero, zero, one, one] x - 30 * hpl [zero, one, zero, one] x -
    18 * hpl [zero, one, one, zero] x - 24 * hpl [zero, one, one, one] x

/-- The `H(1)¹` coefficient of `A + B + C`. -/
noncomputable def i9A2c1 (x : ℝ) : ℝ :=
  π ^ 2 + π ^ 2 * hpl [zero] x - 6 * hpl [zero, one] x + 12 * hpl [zero, zero, one] x +
    12 * hpl [zero, one, zero] x + 12 * hpl [zero, one, one] x

/-- The `H(1)²` coefficient of `A + B + C`. -/
noncomputable def i9A2c2 (x : ℝ) : ℝ := π ^ 2 - 6 * hpl [zero, one] x

theorem i9A2PsiS_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i9A2PsiA x + i9A2PsiB x + i9A2PsiC x =
      i9A2c0 x + hpl [one] x * i9A2c1 x + hpl [one] x ^ 2 * i9A2c2 x := by
  simp only [i9A2PsiA, i9A2PsiB, i9A2PsiC, i9A2c0, i9A2c1, i9A2c2, hpl_w0101 hx, hpl_w0110 hx,
    hpl_w1001 hx, hpl_w1010 hx, hpl_w1011 hx, hpl_w1101 hx, hpl_w1110 hx, hpl_w1111 hx]
  simp only [hpl_one_zero_zero hx, hpl_one_zero_one hx, hpl_one_one_zero hx,
    hpl_one_one_one hx, hpl_zero_one_zero hx, hpl_zero_zero_one hx]
  simp only [hpl_one_zero hx, hpl_one_one hx, hpl_zero_one hx, hpl_one hx, hpl_zero]
  ring

theorem i9A2Psi_eq_one_split {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i9A2Psi x = i9A2c0 x + hpl [one] x * i9A2c1 x + hpl [one] x ^ 2 * i9A2c2 x +
      ((1 - x) * i9A2PsiB x * (1 / x) + (1 - x) * i9A2PsiC x * ((1 + x) / x ^ 2)) := by
  rw [← i9A2PsiS_eq hx, i9A2Psi]
  field_simp [hx.1.ne']
  ring

theorem i9A2Rate_c1 : I9A2Rate i9A2c1 0 := by
  have h := (((((i9A2Rate_const (π ^ 2)).add (i9A2Rate_zero.const_mul (π ^ 2))).add
    ((i9A2Rate_hpl_zero_cons [one] (by decide)).const_mul (-6))).add
    ((i9A2Rate_hpl_zero_cons [zero, one] (by decide)).const_mul 12)).add
    ((i9A2Rate_hpl_zero_cons [one, zero] (by decide)).const_mul 12)).add
    ((i9A2Rate_hpl_zero_cons [one, one] (by decide)).const_mul 12)
  rw [hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one] at h
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun x hx => ?_⟩
  convert hK x hx using 3
  · simp only [i9A2c1]; ring
  · ring

theorem i9A2Rate_c2 : I9A2Rate i9A2c2 0 := by
  have h := (i9A2Rate_const (π ^ 2)).add
    ((i9A2Rate_hpl_zero_cons [one] (by decide)).const_mul (-6))
  rw [hpl_zero_one_at_one] at h
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun x hx => ?_⟩
  convert hK x hx using 3
  · simp only [i9A2c2]; ring
  · ring

theorem tendsto_i9A2c0 :
    Tendsto i9A2c0 (𝓝[<] 1) (𝓝 (9 / 2 * π ^ 2 + 45 * zeta3 - 11 / 30 * π ^ 4)) := by
  have t : ∀ u : List Letter, Tendsto (hpl (zero :: u)) (𝓝[<] 1) (𝓝 (hpl (zero :: u) 1)) :=
    fun u => tendsto_hpl_one (by decide) u
  have h1 := ((t []).const_mul (-π ^ 2)).add ((t [one]).const_mul 27)
  have h2 := ((h1.sub ((t [zero, one]).const_mul 12)).sub ((t [one, zero]).const_mul 18)).add
    ((t [one, one]).const_mul 21)
  have h := (((h2.sub ((t [zero, one, one]).const_mul 36)).sub
    ((t [one, zero, one]).const_mul 30)).sub ((t [one, one, zero]).const_mul 18)).sub
    ((t [one, one, one]).const_mul 24)
  rw [hpl_zero_at_one, hpl_zero_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_one_one_one_at_one] at h
  have e : -π ^ 2 * 0 + 27 * (π ^ 2 / 6) - 12 * zeta3 - 18 * (-2 * zeta3) + 21 * zeta3 -
      36 * (π ^ 4 / 360) - 30 * (π ^ 4 / 120) - 18 * (-π ^ 4 / 72) - 24 * (π ^ 4 / 90) =
      9 / 2 * π ^ 2 + 45 * zeta3 - 11 / 30 * π ^ 4 := by ring
  rw [e] at h
  exact h

/-- **`Ψ(x) → 9π²/2 + 45 ζ(3) - 11π⁴/30` as `x → 1⁻`.** -/
theorem tendsto_i9A2Psi_one :
    Tendsto i9A2Psi (𝓝[<] 1) (𝓝 (9 / 2 * π ^ 2 + 45 * zeta3 - 11 / 30 * π ^ 4)) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) (𝓝[<] 1) (𝓝 (1 / 1)) :=
    ((continuousAt_const.div continuousAt_id (by norm_num)).tendsto).mono_left
      nhdsWithin_le_nhds
  have hinv2 : Tendsto (fun x : ℝ => (1 + x) / x ^ 2) (𝓝[<] 1) (𝓝 ((1 + 1) / 1 ^ 2)) :=
    (((continuousAt_const.add continuousAt_id).div (continuousAt_id.pow 2)
      (by norm_num)).tendsto).mono_left nhdsWithin_le_nhds
  have h := ((tendsto_i9A2c0.add (tendsto_hpl_one_pow_mul_of_rate i9A2Rate_c1 1)).add
    (tendsto_hpl_one_pow_mul_of_rate i9A2Rate_c2 2)).add
    ((tendsto_one_sub_mul_i9A2PsiB.mul hinv).add (tendsto_one_sub_mul_i9A2PsiC.mul hinv2))
  simp only [zero_mul, add_zero, pow_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
  exact (i9A2Psi_eq_one_split hx).symm

/-! ### The value -/

/-- **`∫₀¹ j = π²/2 + 45 ζ(3) - 11π⁴/30`.** -/
theorem integral_i9A2j :
    ∫ p in Ioo (0 : ℝ) 1, i9A2j p = π ^ 2 / 2 + 45 * zeta3 - 11 / 30 * π ^ 4 := by
  have hj := integrableOn_and_integral_i9A2j.1
  have hji : IntervalIntegrable i9A2j volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hj
  have hint : IntervalIntegrable (fun x => i9A2j (1 - x)) volume 0 1 := by
    have := hji.comp_sub_left 1
    simpa using this.symm
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have e := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1) (fun p => i9A2j p) 1
  simp only [sub_self, sub_zero] at e
  rw [← e, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun x hx => hasDerivAt_i9A2Psi hx) hint tendsto_i9A2Psi_zero tendsto_i9A2Psi_one]
  ring

end QED.ThreeLoopD
