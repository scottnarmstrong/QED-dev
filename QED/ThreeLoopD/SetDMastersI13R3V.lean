/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R3P
public import QED.Polylog.HPLValues3
public import QED.Polylog.HPLValues4
public import QED.Polylog.HPLValuesAlt4
public import QED.Polylog.HPLValuesTrailing

/-!
# Set (d), master `I₁₃`: `Ψ₃` at `ξ = 1`

Every word of `Ψ₃` beginning with the letter `1` carries the factor `1 - ξ`
(`QED.ThreeLoopD.i13Psi3S`), and `(1 - ξ) H(1 · w; ξ) → 0` as `ξ → 1⁻`
(`QED.ThreeLoopD.i13_contOn_one_sub_mul_hpl`). So `Ψ₃` is continuous on `(0, 1]`, `F₃` is
continuous on `[0, ∞)`, and `F₃(0) = Ψ₃(1) = π⁴/90 - 26ζ(3) - 33/8`, from the values `H(w; 1)` of
the words of weight at most four.

## Main results

* `QED.ThreeLoopD.continuousOn_i13F3`, `QED.ThreeLoopD.i13F3_zero`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i13_cont_coef {p : ℝ → ℝ} (hp : Continuous p) :
    ContinuousOn (fun x => p x / x ^ 2) (Ioc 0 1) :=
  hp.continuousOn.div (continuous_pow 2).continuousOn fun _ hx => pow_ne_zero 2 hx.1.ne'

theorem i13_contOn_of_Ioo {f : ℝ → ℝ} (h : ContinuousOn f (Ioo 0 1))
    (h1 : ContinuousWithinAt f (Ioc 0 1) 1) : ContinuousOn f (Ioc 0 1) := by
  intro x hx
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact ((h x ⟨hx.1, hlt⟩).continuousAt (Ioo_mem_nhds hx.1 hlt)).continuousWithinAt
  · exact h1

theorem i13_contOn_hpl {a : Letter} (ha : a ≠ one) (w : List Letter) :
    ContinuousOn (hpl (a :: w)) (Ioc 0 1) :=
  i13_contOn_of_Ioo (continuousOn_hpl _)
    ((continuousWithinAt_hpl_one ha w).mono Ioc_subset_Icc_self)

theorem i13_contOn_one_sub_mul_hpl (w : List Letter) :
    ContinuousOn (fun x => (1 - x) * hpl w x) (Ioc 0 1) := by
  refine i13_contOn_of_Ioo ((continuousOn_const.sub continuousOn_id).mul (continuousOn_hpl w)) ?_
  obtain ⟨C, hC, hb⟩ := abs_hpl_le_one_sub_rpow w (ε := 1 / 2) (by norm_num)
  have hlim : Tendsto (fun x : ℝ => C * (1 - x) ^ (1 / 2 : ℝ)) (𝓝 1) (𝓝 0) := by
    have : ContinuousAt (fun x : ℝ => C * (1 - x) ^ (1 / 2 : ℝ)) 1 :=
      continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inr (by norm_num)))
    simpa using this.tendsto
  show Tendsto (fun x => (1 - x) * hpl w x) (𝓝[Ioc 0 1] 1) (𝓝 ((1 - 1) * hpl w 1))
  rw [sub_self, zero_mul]
  refine squeeze_zero_norm' ?_ (hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [inter_mem_nhdsWithin (Ioc (0 : ℝ) 1) (Ioi_mem_nhds (by norm_num :
    (1 / 2 : ℝ) < 1)), self_mem_nhdsWithin] with x hx hx'
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hx'.2] : (0 : ℝ) ≤ 1 - x)]
  rcases hx'.2.lt_or_eq with hlt | rfl
  · have h := hb x ⟨hx.2.le, hlt⟩
    have hp : 0 < 1 - x := by linarith
    calc (1 - x) * |hpl w x| ≤ (1 - x) * (C * (1 - x) ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left h hp.le
      _ = C * ((1 - x) ^ (1 : ℝ) * (1 - x) ^ (-(1 / 2) : ℝ)) := by rw [rpow_one]; ring
      _ = C * (1 - x) ^ (1 / 2 : ℝ) := by rw [← rpow_add hp]; norm_num
  · simp

/-- `Ψ₃` as a sum over words, with the factor `1 - ξ` of the words beginning with `1` shown. -/
noncomputable def i13Psi3S (x : ℝ) : ℝ :=
    (499 / 16 - 2 * zeta3 - 133 / 4 * x - 133 / 4 * x ^ 3 - 11 / 12 * π ^ 2 + 499 / 16 * x ^ 4 +
      2 * zeta3 * x ^ 4 - 2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3 +
      11 / 12 * π ^ 2 * x ^ 4) / x ^ 2 +
    (π ^ 2 / 3 - π ^ 2 * x ^ 4 / 3) / x ^ 2 * hpl [negOne] x +
    (243 / 8 - 115 / 2 * x ^ 3 - 81 / 8 * x ^ 4 - π ^ 2 / 2 + 21 / 2 * x + 107 / 4 * x ^ 2 -
      8 * zeta3 * x ^ 2 - 2 * π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 3 +
      π ^ 2 * x ^ 4 / 6) / x ^ 2 * hpl [zero] x +
    (81 / 4 - 107 / 4 * x - 81 / 4 * x ^ 3 - π ^ 2 / 3 + 107 / 4 * x ^ 2 - π ^ 2 * x / 3 -
      π ^ 2 * x ^ 2 / 3 - π ^ 2 * x ^ 3 / 3) / x ^ 2 * ((1 - x) * hpl [one] x) +
    (-11 - 8 * x + 8 * x ^ 3 + 11 * x ^ 4) / x ^ 2 * hpl [negOne, zero] x +
    (4 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (99 / 4 + 5 * x ^ 3 + 29 * x - 33 / 4 * x ^ 4 + 77 / 2 * x ^ 2 -
      4 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, zero] x +
    (33 / 2 - 26 * x ^ 3 - 10 * x + 25 * x ^ 2 - 11 / 2 * x ^ 4 -
      4 / 3 * π ^ 2 * x ^ 2) / x ^ 2 * hpl [zero, one] x +
    (33 / 2 + 11 / 2 * x ^ 3 + 13 / 2 * x + 63 / 2 * x ^ 2) / x ^ 2 * ((1 -
      x) * hpl [one, zero] x) +
    (11 - 25 * x - 11 * x ^ 3 + 25 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one] x) +
    (4 - 4 * x ^ 4) / x ^ 2 * hpl [negOne, negOne, zero] x +
    (-10 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 + 2 * x ^ 4) / x ^ 2 * hpl [negOne, zero, zero] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, zero, one] x +
    (-4 + 4 * x ^ 4) / x ^ 2 * hpl [negOne, one, zero] x +
    (-6 - 24 * x ^ 2 - 8 * x - 8 * x ^ 3 + 2 * x ^ 4) / x ^ 2 * hpl [zero, negOne, zero] x +
    (27 / 2 + 22 * x + 22 * x ^ 3 + 41 * x ^ 2 - x ^ 4 / 2) / x ^ 2 * hpl [zero, zero, zero] x +
    (9 - 3 * x ^ 4 + 4 * x + 4 * x ^ 3 + 30 * x ^ 2) / x ^ 2 * hpl [zero, zero, one] x +
    (9 - 3 * x ^ 4 + 4 * x + 4 * x ^ 3 + 30 * x ^ 2) / x ^ 2 * hpl [zero, one, zero] x +
    (6 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4 + 12 * x ^ 2) / x ^ 2 * hpl [zero, one, one] x +
    (-4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) / x ^ 2 * ((1 - x) * hpl [one, negOne, zero] x) +
    (9 - x ^ 2 + 3 * x ^ 3 + 13 * x) / x ^ 2 * ((1 - x) * hpl [one, zero, zero] x) +
    (6 - 2 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, zero, one] x) +
    (6 - 2 * x + 2 * x ^ 3 + 10 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, zero] x) +
    (4 - 12 * x - 4 * x ^ 3 + 12 * x ^ 2) / x ^ 2 * ((1 - x) * hpl [one, one, one] x) +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (-24) * hpl [zero, negOne, zero, zero] x +
    (-16) * hpl [zero, negOne, zero, one] x +
    (-16) * hpl [zero, negOne, one, zero] x +
    (-16) * hpl [zero, zero, negOne, zero] x +
    (28) * hpl [zero, zero, zero, zero] x +
    (24) * hpl [zero, zero, zero, one] x +
    (24) * hpl [zero, zero, one, zero] x +
    (16) * hpl [zero, zero, one, one] x +
    (-16) * hpl [zero, one, negOne, zero] x +
    (24) * hpl [zero, one, zero, zero] x +
    (16) * hpl [zero, one, zero, one] x +
    (16) * hpl [zero, one, one, zero] x

theorem continuousOn_i13Psi3S : ContinuousOn i13Psi3S (Ioc 0 1) := by
  unfold i13Psi3S
  exact (((((((((((((((((((((((((((((((((((((i13_cont_coef (p := fun x => 499 / 16 - 2 * zeta3 -
    133 / 4 * x - 133 / 4 * x ^ 3 - 11 / 12 * π ^ 2 + 499 / 16 * x ^ 4 + 2 * zeta3 * x ^ 4 -
    2 / 3 * π ^ 2 * x + 2 / 3 * π ^ 2 * x ^ 3 + 11 / 12 * π ^ 2 * x ^ 4) (by fun_prop)).add
      ((i13_cont_coef (p := fun x => π ^ 2 / 3 - π ^ 2 * x ^ 4 / 3) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 243 / 8 - 115 / 2 * x ^ 3 - 81 / 8 * x ^ 4 - π ^ 2 / 2 +
        21 / 2 * x + 107 / 4 * x ^ 2 - 8 * zeta3 * x ^ 2 - 2 * π ^ 2 * x ^ 2 - 2 / 3 * π ^ 2 * x -
        2 / 3 * π ^ 2 * x ^ 3 + π ^ 2 * x ^ 4 / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i13_cont_coef (p := fun x => 81 / 4 - 107 / 4 * x - 81 / 4 * x ^ 3 - π ^ 2 / 3 +
        107 / 4 * x ^ 2 - π ^ 2 * x / 3 - π ^ 2 * x ^ 2 / 3 - π ^ 2 * x ^ 3 / 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i13_cont_coef (p := fun x => -11 - 8 * x + 8 * x ^ 3 + 11 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i13_cont_coef (p := fun x => 99 / 4 + 5 * x ^ 3 + 29 * x - 33 / 4 * x ^ 4 +
        77 / 2 * x ^ 2 - 4 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i13_cont_coef (p := fun x => 33 / 2 - 26 * x ^ 3 - 10 * x + 25 * x ^ 2 - 11 / 2 * x ^ 4 -
        4 / 3 * π ^ 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i13_cont_coef (p := fun x => 33 / 2 + 11 / 2 * x ^ 3 + 13 / 2 * x +
        63 / 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i13_cont_coef (p := fun x => 11 - 25 * x - 11 * x ^ 3 + 25 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i13_cont_coef (p := fun x => 4 - 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => -10 - 24 * x ^ 2 - 16 * x - 16 * x ^ 3 +
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => -4 + 4 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => -6 - 24 * x ^ 2 - 8 * x - 8 * x ^ 3 +
        2 * x ^ 4) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 27 / 2 + 22 * x + 22 * x ^ 3 + 41 * x ^ 2 -
        x ^ 4 / 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i13_cont_coef (p := fun x => 9 - 3 * x ^ 4 + 4 * x + 4 * x ^ 3 +
        30 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i13_cont_coef (p := fun x => 9 - 3 * x ^ 4 + 4 * x + 4 * x ^ 3 +
        30 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i13_cont_coef (p := fun x => 6 - 8 * x - 8 * x ^ 3 - 2 * x ^ 4 +
        12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i13_cont_coef (p := fun x => -4 - 4 * x - 4 * x ^ 2 - 4 * x ^ 3) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne, zero]))).add
      ((i13_cont_coef (p := fun x => 9 - x ^ 2 + 3 * x ^ 3 + 13 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i13_cont_coef (p := fun x => 6 - 2 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, one]))).add
      ((i13_cont_coef (p := fun x => 6 - 2 * x + 2 * x ^ 3 + 10 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i13_cont_coef (p := fun x => 4 - 12 * x - 4 * x ^ 3 + 12 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, one]))).add
      (continuousOn_const.mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one, zero])))

theorem i13Psi3_eq_S (x : ℝ) : i13Psi3 x = i13Psi3S x := by
  unfold i13Psi3 i13Psi3S i13Psi3N0 i13Psi3N1 i13Psi3N2 i13Psi3N3 i13Psi3N4 i13Psi3W
  ring

theorem continuousOn_i13Psi3 : ContinuousOn i13Psi3 (Ioc 0 1) := by
  rw [show i13Psi3 = i13Psi3S from funext i13Psi3_eq_S]
  exact continuousOn_i13Psi3S

theorem continuousOn_i13F3 : ContinuousOn i13F3 (Ici 0) :=
  continuousOn_i13Psi3.comp continuous_i13Xi.continuousOn fun _ ht =>
    ⟨i13Xi_pos ht, i13Xi_le_one ht⟩

/-- **`Ψ₃(1) = π⁴/90 - 26ζ(3) - 33/8`.** -/
theorem i13Psi3_one : i13Psi3 1 = π ^ 4 / 90 - 26 * zeta3 - 33 / 8 := by
  rw [i13Psi3_eq_S]
  unfold i13Psi3S
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_zero_at_one, hpl_zero_one_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_zero_zero_at_one, hpl_negOne_zero_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_zero_one_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_one_one_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_one_negOne_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_one_zero_one_at_one, hpl_zero_one_one_zero_at_one]
  norm_num
  ring

theorem i13F3_zero : i13F3 0 = π ^ 4 / 90 - 26 * zeta3 - 33 / 8 := by
  unfold i13F3
  rw [i13Xi_zero, i13Psi3_one]

end QED.ThreeLoopD
