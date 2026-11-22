/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeW
import QED.Polylog.HPLCalculus
import QED.Polylog.HPLLowWeight
public import QED.Polylog.LiN

/-!
# Set (d), master `I₁₅`: the primitive of `W₃ / r` at `0⁺`

The primitive `Φ = Σ qₜ(r) H(wₜ; r)` of `QED.ThreeLoopD.SetDMastersI15KValThreeW` has terms
`a H(w; r) / r` and `log r`, `log² r` that diverge separately at `0⁺`. Splitting off the part
`Σ (b + c r + d r²) H(w; r)` that tends to `0` (`QED.ThreeLoopD.tendsto_i15T3Sum_zero`), the rest
is, by the closed forms of the words of weight `≤ 3` that start with `0^j a 0^k`,

  `300 + Σᵢ pᵢ(log r) Eᵢ(r) + Σ a H(a, w'; r) / r`,

with `Eᵢ = Li_k(±r)/(±r) - 1 = O(r)` (`k = 1, 2, 3`), `pᵢ` polynomials of degree `≤ 2`, and the
last sum over words `a w'` (`a = ±1`, `w'` not all zeros) with `H = O(r^{3/2})`. Hence `Φ → 300`.

## Main results

* `QED.ThreeLoopD.i15W3Phi_eq`: the splitting.
* `QED.ThreeLoopD.tendsto_i15W3Phi_zero`: `Φ → 300` at `0⁺`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- `|Li_k x / x - 1| ≤ 2 |x|` for `0 < |x| ≤ 1/2`, `k ≥ 1`. -/
theorem i15W0_abs_Li_div_sub_le {k : ℕ} {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 2) :
    |Li k x / x - 1| ≤ 2 * |x| := by
  have hx1 : |x| < 1 := by linarith
  have hs := hasSum_Li_of_abs_lt_one k hx1
  have h1 := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    one_pow, div_one] at h1
  have hg : HasSum (fun n : ℕ => |x| ^ 2 * (1 / 2) ^ n) (|x| ^ 2 * 2) := by
    have := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left (|x| ^ 2)
    convert this using 2; norm_num
  have hb := h1.norm_le_of_bounded hg fun n => by
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_pow]
    have hd : (1 : ℝ) ≤ |((n + 1 : ℕ) : ℝ) + 1| ^ k := by
      apply one_le_pow₀; rw [abs_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1)]
      push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc |x| ^ (n + 1 + 1) / |((n + 1 : ℕ) : ℝ) + 1| ^ k ≤ |x| ^ (n + 1 + 1) :=
          div_le_self (by positivity) hd
      _ = |x| ^ 2 * |x| ^ n := by ring
      _ ≤ |x| ^ 2 * (1 / 2) ^ n := by gcongr
  rw [Real.norm_eq_abs] at hb
  have hxp : 0 < |x| := abs_pos.2 hx0
  rw [show Li k x / x - 1 = (Li k x - x) / x by field_simp, abs_div]
  rw [div_le_iff₀ hxp]
  nlinarith

/-- `log r ^ j · (Li_k (s r)/(s r) - 1) → 0` at `0⁺`, `|s| = 1`. -/
theorem i15W0_tendsto_log_pow_mul (j k : ℕ) {s : ℝ} (hs : |s| = 1) :
    Tendsto (fun r => log r ^ j * (Li k (s * r) / (s * r) - 1)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := abs_log_pow_le j (by norm_num : (0 : ℝ) < 1 / 2)
  refine tendsto_zero_of_abs_le_rpow (C := 2 * K) (r := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) fun t ht => ?_
  have ht0 := ht.1
  have hst : |s * t| = t := by rw [abs_mul, hs, one_mul, abs_of_pos ht0]
  have h1 := i15W0_abs_Li_div_sub_le (k := k) (x := s * t)
    (by rw [← abs_ne_zero, hst]; exact ht0.ne') (by rw [hst]; exact ht.2)
  rw [hst] at h1
  have h2 := hK t ⟨ht0, by linarith [ht.2]⟩
  have hrp : t * t ^ (-(1 / 2 : ℝ)) = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' ht0.le (by norm_num)]; norm_num
  rw [abs_mul, abs_pow]
  calc |log t| ^ j * |Li k (s * t) / (s * t) - 1| ≤ (K * t ^ (-(1 / 2 : ℝ))) * (2 * t) :=
        mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    _ = 2 * K * (t * t ^ (-(1 / 2 : ℝ))) := by ring
    _ = 2 * K * t ^ (1 / 2 : ℝ) := by rw [hrp]

/-- `H(a w'; r) / r → 0` at `0⁺` for `a ≠ 0` and `w'` not all zeros. -/
theorem i15W0_tendsto_hpl_div {a : Letter} (ha : a ≠ zero) {w : List Letter} (hw : ¬AllZero w) :
    Tendsto (fun r => hpl (a :: w) r / r) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := abs_hpl_le_sqrt hw (b := 1 / 2) (by norm_num)
  refine tendsto_zero_of_abs_le_rpow (C := 2 * C / (3 / 2)) (r := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) fun t ht => ?_
  have ht0 := ht.1
  have hb : |hpl (a :: w) t| ≤ 2 * C * (t ^ ((1 / 2 : ℝ) + 1) / ((1 / 2 : ℝ) + 1)) := by
    rw [hpl_cons_of_ne_zero ha]
    refine abs_integral_le_of_le_rpow ht0.le (by norm_num) fun y hy => ?_
    rw [abs_mul]
    have hk := abs_kernel_le ha (b := 1 / 2) (by norm_num) hy.1.le (hy.2.trans ht.2)
    have hh := hC y ⟨hy.1, hy.2.trans ht.2⟩
    calc |a.kernel y| * |hpl w y| ≤ (1 - 1 / 2)⁻¹ * (C * y ^ (1 / 2 : ℝ)) :=
          mul_le_mul hk hh (abs_nonneg _) (by norm_num)
      _ = 2 * C * y ^ (1 / 2 : ℝ) := by norm_num; ring
  have he : t ^ ((1 / 2 : ℝ) + 1) = t * t ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_add ht0, Real.rpow_one]; ring
  rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  rw [he] at hb
  calc |hpl (a :: w) t| ≤ 2 * C * (t * t ^ (1 / 2 : ℝ) / (1 / 2 + 1)) := hb
    _ = 2 * C / (3 / 2) * t ^ (1 / 2 : ℝ) * t := by ring

/-- `(a + b log r + c log² r) (Li_k (s r)/(s r) - 1) → 0` at `0⁺`, `|s| = 1`. -/
theorem i15W0_tendsto_quad (a b c : ℝ) (k : ℕ) {s : ℝ} (hs : |s| = 1) :
    Tendsto (fun r => (a + b * log r + c * log r ^ 2) * (Li k (s * r) / (s * r) - 1))
      (𝓝[>] 0) (𝓝 0) := by
  have h := (((i15W0_tendsto_log_pow_mul 0 k hs).const_mul a).add
    ((i15W0_tendsto_log_pow_mul 1 k hs).const_mul b)).add
    ((i15W0_tendsto_log_pow_mul 2 k hs).const_mul c)
  simp only [mul_zero, add_zero] at h
  refine h.congr fun r => ?_
  ring

/-- The terms of the primitive that tend to `0` on their own. -/
noncomputable def i15W0L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter) :=
  [((0, 0, 10 * π ^ 2 - 24 * zeta3, 0), []),
   ((0, 0, 228, 0), [zero]),
   ((0, -8 * π ^ 2, 4 * π ^ 2, 0), [one]),
   ((0, -4 * π ^ 2, -228, 0), [negOne]),
   ((0, 0, 60, 0), [zero, zero]),
   ((0, -96, 120, 0), [zero, negOne]),
   ((0, -240, 120, 0), [one, zero]),
   ((0, -120, -60, 0), [negOne, zero]),
   ((0, 0, 12, 0), [zero, zero, zero]),
   ((0, -48, 72, 0), [zero, zero, negOne]),
   ((0, -48, 96, 0), [zero, one, zero]),
   ((0, 24, -72, 0), [zero, negOne, zero]),
   ((0, 0, 48, 0), [zero, negOne, negOne]),
   ((0, -48, 24, 0), [one, zero, zero]),
   ((0, -192, 96, 0), [one, zero, negOne]),
   ((0, -192, 96, 0), [one, one, zero]),
   ((0, 96, -48, 0), [one, negOne, zero]),
   ((0, -24, -12, 0), [negOne, zero, zero]),
   ((0, -96, -24, 0), [negOne, zero, negOne]),
   ((0, -96, -48, 0), [negOne, one, zero]),
   ((0, 48, 48, 0), [negOne, negOne, zero]),
   ((0, 0, -48, 0), [negOne, negOne, negOne])]

theorem tendsto_i15W0L : Tendsto (i15T3Sum i15W0L) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_i15T3Sum_zero fun t ht => ?_
  simp only [i15W0L, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [AllZero]

/-- The splitting of the primitive near `0`. -/
theorem i15W3Phi_eq {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    i15W3Phi r = 300 +
      ((12 * log r ^ 2 + 120 * log r + 4 * π ^ 2) * (Li 1 (1 * r) / (1 * r) - 1) +
      (-6 * log r ^ 2 - 60 * log r + (228 - 4 * π ^ 2)) * (Li 1 (-1 * r) / (-1 * r) - 1) +
      (24 * log r - 120) * (Li 2 (1 * r) / (1 * r) - 1) +
      (180 - 12 * log r) * (Li 2 (-1 * r) / (-1 * r) - 1) -
      72 * (Li 3 (1 * r) / (1 * r) - 1) + 84 * (Li 3 (-1 * r) / (-1 * r) - 1)) +
      (96 * (hpl [one, zero, negOne] r / r) + 96 * (hpl [one, one, zero] r / r) -
        48 * (hpl [one, negOne, zero] r / r) - 72 * (hpl [negOne, zero, negOne] r / r) -
        48 * (hpl [negOne, one, zero] r / r) + 48 * (hpl [negOne, negOne, negOne] r / r)) +
      i15T3Sum i15W0L r := by
  obtain ⟨h0, h1⟩ := hr
  have hr' : r ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have a1 : |r| < 1 := by rw [abs_of_pos h0]; exact h1
  have a2 : |-r| < 1 := by rw [abs_neg, abs_of_pos h0]; exact h1
  simp only [one_mul, neg_one_mul]
  unfold i15W3Phi i15T3Sum
  simp only [i15W3L, i15W0L, i15T3q, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hpl_zero, hpl_zero_zero, hpl_one hr', hpl_negOne hr', hpl_zero_negOne hr', hpl_one_zero hr',
    hpl_negOne_zero hr', hpl_zero_zero_negOne hr', hpl_zero_one_zero hr',
    hpl_zero_negOne_zero hr', hpl_one_zero_zero hr', hpl_negOne_zero_zero hr', Li_one a1,
    Li_one a2, sub_neg_eq_add]
  field_simp
  ring

/-- **`Φ → 300` at `0⁺`.** -/
theorem tendsto_i15W3Phi_zero : Tendsto i15W3Phi (𝓝[>] 0) (𝓝 300) := by
  have p1 : |(1 : ℝ)| = 1 := abs_one
  have p2 : |(-1 : ℝ)| = 1 := by simp
  have hE := (((((i15W0_tendsto_quad (4 * π ^ 2) 120 12 1 p1).add
    (i15W0_tendsto_quad (228 - 4 * π ^ 2) (-60) (-6) 1 p2)).add
    (i15W0_tendsto_quad (-120) 24 0 2 p1)).add (i15W0_tendsto_quad 180 (-12) 0 2 p2)).sub
    ((i15W0_tendsto_quad 1 0 0 3 p1).const_mul 72)).add
    ((i15W0_tendsto_quad 1 0 0 3 p2).const_mul 84)
  have hn : ∀ {a : Letter} {w : List Letter}, a ≠ zero → ¬AllZero w →
      Tendsto (fun r => hpl (a :: w) r / r) (𝓝[>] 0) (𝓝 0) := fun ha hw =>
    i15W0_tendsto_hpl_div ha hw
  have hH := (((((((hn (a := one) (w := [zero, negOne]) (by simp) (by simp [AllZero])).const_mul
    96).add ((hn (a := one) (w := [one, zero]) (by simp) (by simp [AllZero])).const_mul 96)).sub
    ((hn (a := one) (w := [negOne, zero]) (by simp) (by simp [AllZero])).const_mul 48)).sub
    ((hn (a := negOne) (w := [zero, negOne]) (by simp) (by simp [AllZero])).const_mul 72)).sub
    ((hn (a := negOne) (w := [one, zero]) (by simp) (by simp [AllZero])).const_mul 48)).add
    ((hn (a := negOne) (w := [negOne, negOne]) (by simp) (by simp [AllZero])).const_mul 48))
  have h := ((tendsto_const_nhds (x := (300 : ℝ))).add hE).add hH |>.add tendsto_i15W0L
  simp only [mul_zero, add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
  rw [i15W3Phi_eq hr]
  ring

end QED.ThreeLoopD
