/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10G0An
public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Set (e), master `I₁₀`: `K_ab = ε² h(ε)` with `h` analytic near `ε = 0`

Write `A(x) - 1 = ε D(ε, x)` with `D(ε, x) = dslope (e ↦ (1 - x) ^ (-e)) 0 ε`
(`QED.ThreeLoopE.i10D`; entire in `ε`, `D(0, x) = -log (1 - x)`). Then the integrand of
`K_ab` (`QED.ThreeLoopE.i10Kab`) is `ε²` times

  `H = D(ε, ρ) D(ε, σ) (z(1 - z)) ^ (ε - 1) (τ ^ (ε - 1) - (1 - z) σ ^ (ε - 1) - z ρ ^ (ε - 1))`

(`QED.ThreeLoopE.i10KabH`), so `K_ab = ε² h`, `h = ∫ H` (`QED.ThreeLoopE.i10Kab_eq`). On
`‖ε‖ < 1/20`:

* `‖D(ε, x)‖ ≤ -log (1 - x) (1 - x) ^ (-1/20) ≤ 2 x (1 - x) ^ (-11/20)`
  (`QED.ThreeLoopE.norm_i10D_le`, from `-log (1 - x) ≤ 2 x (1 - x) ^ (-1/2)`);
* for `z ≤ 1/2` the bracket is `(τ ^ a - σ ^ a) + z (σ ^ a - ρ ^ a)` (`a = ε - 1`); as
  `τ ≥ σ/2`, `‖τ ^ a - σ ^ a‖` is at most `5 σ ^ (-21/20)` and, by the mean value theorem, at
  most `16 z σ ^ (-41/20)`, hence at most their geometric mean `9 √z σ ^ (-31/20)`; with the
  symmetry `(z, ρ, σ) ↦ (1 - z, σ, ρ)`, `‖bracket‖ ≤ 16 (z(1 - z)) ^ (1/2) (ρσ) ^ (-31/20)`
  (`QED.ThreeLoopE.norm_i10Br_le`).

So `‖H‖ ≤ 64 (z(1 - z)) ^ (-11/20) (ρ(1 - ρ)) ^ (-11/20) (σ(1 - σ)) ^ (-11/20)`, integrable, and
`h` is analytic on `‖ε‖ < 1/40` (`QED.ThreeLoopE.analyticOnNhd_i10KabH`).

## Main results

* `QED.ThreeLoopE.i10Kab_eq`, `QED.ThreeLoopE.norm_i10KabH_le`,
  `QED.ThreeLoopE.analyticOnNhd_i10KabH`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology QED.DimReg QED.ThreeLoopD

namespace QED.ThreeLoopE

/-! ### The difference quotient `D` -/

/-- `D(ε, x) = ((1 - x) ^ (-ε) - 1) / ε`, continued to `ε = 0` by `-log (1 - x)`. -/
noncomputable def i10D (ε : ℂ) (x : ℝ) : ℂ := dslope (fun e : ℂ => ((1 - x : ℝ) : ℂ) ^ (-e)) 0 ε

theorem i10A_sub_one (ε : ℂ) (x : ℝ) : i10A ε x - 1 = ε * i10D ε x := by
  have h := sub_smul_dslope (fun e : ℂ => ((1 - x : ℝ) : ℂ) ^ (-e)) 0 ε
  simp only [sub_zero, neg_zero, cpow_zero, smul_eq_mul] at h
  rw [i10A, i10D, h]

theorem i10D_of_ne {ε : ℂ} (h : ε ≠ 0) (x : ℝ) :
    i10D ε x = (((1 - x : ℝ) : ℂ) ^ (-ε) - 1) / ε := by
  rw [eq_div_iff h, mul_comm, ← i10A_sub_one, i10A]

theorem hasDerivAt_i10A_zero {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt (fun e : ℂ => ((1 - x : ℝ) : ℂ) ^ (-e)) (-Complex.log ((1 - x : ℝ) : ℂ)) 0 := by
  have hc : ((1 - x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hx))
  have h := (hasDerivAt_neg (0 : ℂ)).const_cpow (c := ((1 - x : ℝ) : ℂ)) (Or.inl hc)
  rw [neg_zero, cpow_zero] at h
  convert h using 1
  ring

theorem i10D_zero' {x : ℝ} (hx : x ≠ 1) : i10D 0 x = -Complex.log ((1 - x : ℝ) : ℂ) := by
  rw [i10D, dslope_same, (hasDerivAt_i10A_zero hx).deriv]

theorem i10D_zero {x : ℝ} (hx : x < 1) : i10D 0 x = -(Real.log (1 - x) : ℂ) := by
  rw [i10D_zero' hx.ne, ofReal_log (by linarith)]

theorem differentiable_i10D {x : ℝ} (hx : x < 1) : Differentiable ℂ fun ε => i10D ε x := by
  have h0 : ((1 - x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hf : DifferentiableOn ℂ (fun e : ℂ => ((1 - x : ℝ) : ℂ) ^ (-e)) univ := fun e _ =>
    (differentiableAt_id.neg.const_cpow (Or.inl h0)).differentiableWithinAt
  have := (differentiableOn_dslope (c := (0 : ℂ)) (s := univ) univ_mem).2 hf
  exact fun ε => (this ε (mem_univ _)).differentiableAt univ_mem

theorem measurable_i10D (ε : ℂ) : Measurable fun x : ℝ => i10D ε x := by
  by_cases h : ε = 0
  · subst h
    have e : (fun x : ℝ => i10D 0 x) = fun x =>
        if x = 1 then i10D 0 1 else -Complex.log ((1 - x : ℝ) : ℂ) := by
      funext x
      by_cases hx : x = 1
      · subst hx; simp
      · simp only [hx, ↓reduceIte, i10D_zero' hx]
    rw [e]
    exact Measurable.ite (measurableSet_singleton 1) measurable_const (by fun_prop)
  · simp only [i10D_of_ne h]
    fun_prop

/-! ### Bounds on `D` -/

/-- `-log (1 - x) ≤ 2 x (1 - x) ^ (-1/2)` on `(0, 1)`. -/
theorem neg_log_one_sub_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    -Real.log (1 - x) ≤ 2 * x * (1 - x) ^ (-(1 / 2) : ℝ) := by
  have hc : 0 < 1 - x := by linarith [hx.2]
  set s := (1 - x) ^ (1 / 2 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hc _
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hs0)
  rw [Real.log_inv, hs, Real.log_rpow hc] at hl
  have hge : 1 - x ≤ s := by
    rw [hs]
    calc 1 - x = (1 - x) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 - x) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hc (by linarith [hx.1]) (by norm_num)
  have hinv : (1 - x) ^ (-(1 / 2) : ℝ) = s⁻¹ := by rw [hs, Real.rpow_neg hc.le]
  rw [hinv]
  have : s⁻¹ - 1 ≤ x * s⁻¹ := by
    rw [show s⁻¹ - 1 = (1 - s) * s⁻¹ by field_simp]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hs0.le)
  linarith

theorem norm_i10D_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖i10D ε x‖ ≤ 2 * x * (1 - x) ^ (-(11 / 20) : ℝ) := by
  have hc : 0 < 1 - x := by linarith [hx.2]
  have hc1 : 1 - x ≤ 1 := by linarith [hx.1]
  set L := -Real.log (1 - x) with hL
  have hL0 : 0 ≤ L := by rw [hL, neg_nonneg]; exact Real.log_nonpos hc.le hc1
  have hE : (1 - x) ^ (-(1 / 20) : ℝ) = Real.exp (L / 20) := by
    rw [Real.rpow_def_of_pos hc, hL]; congr 1; ring
  have hE1 : 1 ≤ Real.exp (L / 20) := Real.one_le_exp (by positivity)
  have hmain : ‖i10D ε x‖ ≤ L * (1 - x) ^ (-(1 / 20) : ℝ) := by
    by_cases h0 : ε = 0
    · subst h0
      rw [i10D_zero hx.2, norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonpos
        (Real.log_nonpos hc.le hc1), hE]
      exact le_mul_of_one_le_right hL0 hE1
    · rw [i10D_of_ne h0, norm_div]
      have hw : ((1 - x : ℝ) : ℂ) ^ (-ε) = cexp ((Real.log (1 - x) : ℂ) * (-ε)) := by
        rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hc.ne'), ofReal_log hc.le]
      have hb := Complex.norm_exp_sub_sum_le_norm_mul_exp ((Real.log (1 - x) : ℂ) * (-ε)) 1
      simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, pow_one] at hb
      have hn : ‖(Real.log (1 - x) : ℂ) * (-ε)‖ = L * ‖ε‖ := by
        rw [norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonpos
          (Real.log_nonpos hc.le hc1)]
      rw [hw, div_le_iff₀ (norm_pos_iff.mpr h0)]
      calc _ ≤ L * ‖ε‖ * Real.exp (L * ‖ε‖) := by rw [← hn]; exact hb
        _ ≤ L * ‖ε‖ * Real.exp (L / 20) := by
            gcongr
            nlinarith
        _ = _ := by rw [hE]; ring
  have hlog := neg_log_one_sub_le hx
  calc _ ≤ L * (1 - x) ^ (-(1 / 20) : ℝ) := hmain
    _ ≤ 2 * x * (1 - x) ^ (-(1 / 2) : ℝ) * (1 - x) ^ (-(1 / 20) : ℝ) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hc.le _)
    _ = _ := by rw [mul_assoc, rpow_mul_rpow_eq (c := -(11 / 20)) hc (by norm_num)]

/-! ### The bracket -/

/-- The bracket of `K_ab`: `τ ^ (ε - 1) - (1 - z) σ ^ (ε - 1) - z ρ ^ (ε - 1)`. -/
noncomputable def i10Br (ε : ℂ) (z ρ σ : ℝ) : ℂ :=
  ((i10Tau z ρ σ : ℝ) : ℂ) ^ (ε - 1) - (1 - z : ℂ) * (σ : ℂ) ^ (ε - 1) - (z : ℂ) * (ρ : ℂ) ^ (ε - 1)

theorem i10Br_symm (ε : ℂ) (z ρ σ : ℝ) : i10Br ε (1 - z) σ ρ = i10Br ε z ρ σ := by
  have : i10Tau (1 - z) σ ρ = i10Tau z ρ σ := by unfold i10Tau; ring
  rw [i10Br, i10Br, this]
  push_cast
  ring

/-- Mean value bound for `t ↦ t ^ a` on `[σ/2, 1]`. -/
theorem norm_cpow_sub_cpow_mvt {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {σ t : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Icc (σ / 2) 1) :
    ‖(t : ℂ) ^ (ε - 1) - (σ : ℂ) ^ (ε - 1)‖ ≤ 16 * σ ^ (-(41 / 20) : ℝ) * |t - σ| := by
  have hr := i10_re_le hε
  have hr' := (i9_eps_facts hε).2.2.1
  have hσ2 : 0 < σ / 2 := by linarith [hσ.1]
  have ha : ε - 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hd : ∀ y ∈ Icc (σ / 2) 1, HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (ε - 1))
      ((ε - 1) * (y : ℂ) ^ (ε - 1 - 1)) (Icc (σ / 2) 1) y := fun y hy =>
    (hasDerivAt_ofReal_cpow_const (by linarith [hy.1]) ha).hasDerivWithinAt
  have hb : ∀ y ∈ Icc (σ / 2) 1, ‖(ε - 1) * (y : ℂ) ^ (ε - 1 - 1)‖ ≤ 16 * σ ^ (-(41 / 20) : ℝ) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hn : ‖ε - 1‖ ≤ 2 := by
      calc ‖ε - 1‖ ≤ ‖ε‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hp : ‖(y : ℂ) ^ (ε - 1 - 1)‖ ≤ y ^ (-(41 / 20) : ℝ) :=
      norm_cpow_le_rpow_of_le hy0 hy.2 (by simp; linarith)
    have hm : y ^ (-(41 / 20) : ℝ) ≤ (σ / 2) ^ (-(41 / 20) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hσ2 hy.1 (by norm_num)
    have h2 : (σ / 2) ^ (-(41 / 20) : ℝ) ≤ 8 * σ ^ (-(41 / 20) : ℝ) := by
      rw [Real.div_rpow hσ.1.le (by norm_num), div_eq_mul_inv, mul_comm,
        ← Real.rpow_neg (by norm_num), neg_neg]
      have : (2 : ℝ) ^ (41 / 20 : ℝ) ≤ 2 ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hσ.1.le _)
    rw [norm_mul]
    calc _ ≤ 2 * (8 * σ ^ (-(41 / 20) : ℝ)) :=
          mul_le_mul hn (hp.trans (hm.trans h2)) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hσm : σ ∈ Icc (σ / 2) 1 := ⟨by linarith [hσ.1], hσ.2.le⟩
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _) hσm ht
  rwa [Real.norm_eq_abs] at this

/-- The bracket bound for `z ≤ 1/2`. -/
theorem norm_i10Br_le_half {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z ρ σ : ℝ} (hz : z ∈ Ioc (0 : ℝ) (1 / 2))
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ‖i10Br ε z ρ σ‖ ≤ 11 * (z ^ (1 / 2 : ℝ) * (ρ * σ) ^ (-(31 / 20) : ℝ)) := by
  have hr := i10_re_le hε
  have hr' := (i9_eps_facts hε).2.2.1
  obtain ⟨hz0, hz1⟩ := hz
  have hτ0 : σ / 2 ≤ i10Tau z ρ σ := by unfold i10Tau; nlinarith [hρ.1, hσ.1]
  have hτ1 : i10Tau z ρ σ ≤ 1 := by unfold i10Tau; nlinarith [hρ.2, hσ.2]
  have hτp : 0 < i10Tau z ρ σ := by linarith [hσ.1]
  have hd : |i10Tau z ρ σ - σ| ≤ z := by
    rw [show i10Tau z ρ σ - σ = z * (ρ - σ) by unfold i10Tau; ring, abs_mul, abs_of_pos hz0]
    exact mul_le_of_le_one_right hz0.le (abs_le.mpr ⟨by linarith [hρ.1, hσ.2],
      by linarith [hρ.2, hσ.1]⟩)
  set X := ((i10Tau z ρ σ : ℝ) : ℂ) ^ (ε - 1) - (σ : ℂ) ^ (ε - 1) with hX
  -- the two bounds on `X`
  have hσr : ‖(σ : ℂ) ^ (ε - 1)‖ ≤ σ ^ (-(21 / 20) : ℝ) :=
    norm_cpow_le_rpow_of_le hσ.1 hσ.2.le (by simp; linarith)
  have hρr : ‖(ρ : ℂ) ^ (ε - 1)‖ ≤ ρ ^ (-(21 / 20) : ℝ) :=
    norm_cpow_le_rpow_of_le hρ.1 hρ.2.le (by simp; linarith)
  have hτr : ‖((i10Tau z ρ σ : ℝ) : ℂ) ^ (ε - 1)‖ ≤ 4 * σ ^ (-(21 / 20) : ℝ) := by
    have h1 : ‖((i10Tau z ρ σ : ℝ) : ℂ) ^ (ε - 1)‖ ≤ (i10Tau z ρ σ) ^ (-(21 / 20) : ℝ) :=
      norm_cpow_le_rpow_of_le hτp hτ1 (by simp; linarith)
    have h2 := Real.rpow_le_rpow_of_nonpos (by linarith [hσ.1]) hτ0
      (by norm_num : -(21 / 20 : ℝ) ≤ 0)
    have h3 : (σ / 2) ^ (-(21 / 20) : ℝ) ≤ 4 * σ ^ (-(21 / 20) : ℝ) := by
      rw [Real.div_rpow hσ.1.le (by norm_num), div_eq_mul_inv, mul_comm,
        ← Real.rpow_neg (by norm_num), neg_neg]
      have : (2 : ℝ) ^ (21 / 20 : ℝ) ≤ 2 ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hσ.1.le _)
    linarith
  have hM1 : ‖X‖ ≤ 5 * σ ^ (-(21 / 20) : ℝ) := by
    calc ‖X‖ ≤ _ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hM2 : ‖X‖ ≤ 16 * σ ^ (-(41 / 20) : ℝ) * z :=
    (norm_cpow_sub_cpow_mvt hε hσ ⟨hτ0, hτ1⟩).trans
      (mul_le_mul_of_nonneg_left hd
        (by have := Real.rpow_nonneg hσ.1.le (-(41 / 20) : ℝ); positivity))
  -- the geometric mean
  have hS : ‖X‖ ≤ 9 * (z ^ (1 / 2 : ℝ) * σ ^ (-(31 / 20) : ℝ)) := by
    have hsqr : (σ ^ (-(31 / 20) : ℝ)) ^ 2 = σ ^ (-(21 / 20) : ℝ) * σ ^ (-(41 / 20) : ℝ) := by
      rw [sq, rpow_mul_rpow_eq (c := -(31 / 10)) hσ.1 (by norm_num),
        rpow_mul_rpow_eq (c := -(31 / 10)) hσ.1 (by norm_num)]
    have hz2 : (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]; norm_num
    have hs0 := Real.rpow_nonneg hσ.1.le (-(41 / 20) : ℝ)
    have hs1 := Real.rpow_nonneg hσ.1.le (-(31 / 20) : ℝ)
    have hz0' := Real.rpow_nonneg hz0.le (1 / 2 : ℝ)
    have hsq : ‖X‖ ^ 2 ≤ 80 * z * (σ ^ (-(31 / 20) : ℝ)) ^ 2 := by
      rw [hsqr, sq]
      calc ‖X‖ * ‖X‖ ≤ (5 * σ ^ (-(21 / 20) : ℝ)) * (16 * σ ^ (-(41 / 20) : ℝ) * z) :=
            mul_le_mul hM1 hM2 (norm_nonneg _) (by linarith [norm_nonneg X])
        _ = _ := by ring
    have h81 : 80 * z * (σ ^ (-(31 / 20) : ℝ)) ^ 2 ≤
        (9 * (z ^ (1 / 2 : ℝ) * σ ^ (-(31 / 20) : ℝ))) ^ 2 := by
      have : (9 * (z ^ (1 / 2 : ℝ) * σ ^ (-(31 / 20) : ℝ))) ^ 2 =
          81 * (z ^ (1 / 2 : ℝ)) ^ 2 * (σ ^ (-(31 / 20) : ℝ)) ^ 2 := by ring
      rw [this, hz2]
      nlinarith [sq_nonneg (σ ^ (-(31 / 20) : ℝ)), hz0]
    exact (pow_le_pow_iff_left₀ (norm_nonneg X) (by positivity) two_ne_zero).1 (hsq.trans h81)
  -- assembling
  have hρ1 : ρ ^ (-(31 / 20) : ℝ) ≥ 1 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ.1
    hρ.2.le (by norm_num)
  have hσ1 : σ ^ (-(31 / 20) : ℝ) ≥ 1 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hσ.1
    hσ.2.le (by norm_num)
  have hρσ : (ρ * σ) ^ (-(31 / 20) : ℝ) = ρ ^ (-(31 / 20) : ℝ) * σ ^ (-(31 / 20) : ℝ) :=
    Real.mul_rpow hρ.1.le hσ.1.le
  have hσa : σ ^ (-(21 / 20) : ℝ) ≤ σ ^ (-(31 / 20) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hσ.1 hσ.2.le (by norm_num)
  have hρa : ρ ^ (-(21 / 20) : ℝ) ≤ ρ ^ (-(31 / 20) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ.1 hρ.2.le (by norm_num)
  have hzs : z ≤ z ^ (1 / 2 : ℝ) := by
    calc z = z ^ (1 : ℝ) := (Real.rpow_one z).symm
      _ ≤ z ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hz0 (by linarith) (by norm_num)
  have hzs0 : 0 ≤ z ^ (1 / 2 : ℝ) := Real.rpow_nonneg hz0.le _
  have e : i10Br ε z ρ σ = X + (z : ℂ) * ((σ : ℂ) ^ (ε - 1) - (ρ : ℂ) ^ (ε - 1)) := by
    rw [i10Br, hX]; ring
  have hzn : ‖(z : ℂ)‖ = z := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hz0]
  rw [e, hρσ]
  calc _ ≤ ‖X‖ + z * (‖(σ : ℂ) ^ (ε - 1)‖ + ‖(ρ : ℂ) ^ (ε - 1)‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, hzn]
        gcongr
        exact norm_sub_le _ _
    _ ≤ 9 * (z ^ (1 / 2 : ℝ) * σ ^ (-(31 / 20) : ℝ)) +
        z ^ (1 / 2 : ℝ) * (ρ ^ (-(31 / 20) : ℝ) * σ ^ (-(31 / 20) : ℝ) +
          ρ ^ (-(31 / 20) : ℝ) * σ ^ (-(31 / 20) : ℝ)) := by
        gcongr
        · nlinarith
        · nlinarith
    _ ≤ _ := by nlinarith [mul_nonneg hzs0 (Real.rpow_nonneg hσ.1.le (-(31 / 20) : ℝ))]

theorem i10_half_le {t : ℝ} (ht : 0 < t) (h : t ≤ 2 * (t * (1 - t))) (ht1 : t < 1) :
    t ^ (1 / 2 : ℝ) ≤ 3 / 2 * (t * (1 - t)) ^ (1 / 2 : ℝ) := by
  have hc : 0 ≤ t * (1 - t) := mul_nonneg ht.le (by linarith)
  calc t ^ (1 / 2 : ℝ) ≤ (2 * (t * (1 - t))) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow ht.le h (by norm_num)
    _ = (2 : ℝ) ^ (1 / 2 : ℝ) * (t * (1 - t)) ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) hc
    _ ≤ _ := by
        gcongr
        rw [← Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = √((3 / 2) ^ 2) from
          (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num)

/-- **The bracket bound** `‖bracket‖ ≤ 17 (z(1 - z)) ^ (1/2) (ρσ) ^ (-31/20)`. -/
theorem norm_i10Br_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z ρ σ : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ‖i10Br ε z ρ σ‖ ≤ 17 * ((z * (1 - z)) ^ (1 / 2 : ℝ) * (ρ * σ) ^ (-(31 / 20) : ℝ)) := by
  have hP := Real.rpow_nonneg (mul_pos hρ.1 hσ.1).le (-(31 / 20) : ℝ)
  rcases le_or_gt z (1 / 2) with h | h
  · have hb := norm_i10Br_le_half hε ⟨hz.1, h⟩ hρ hσ
    have hh := i10_half_le hz.1 (by nlinarith [hz.1]) hz.2
    calc _ ≤ 11 * (z ^ (1 / 2 : ℝ) * (ρ * σ) ^ (-(31 / 20) : ℝ)) := hb
      _ ≤ 11 * (3 / 2 * (z * (1 - z)) ^ (1 / 2 : ℝ) * (ρ * σ) ^ (-(31 / 20) : ℝ)) := by gcongr
      _ ≤ _ := by
          have := Real.rpow_nonneg (mul_nonneg hz.1.le (by linarith [hz.2]) : 0 ≤ z * (1 - z))
            (1 / 2 : ℝ)
          nlinarith [mul_nonneg this hP]
  · have hb := norm_i10Br_le_half hε (z := 1 - z) ⟨by linarith [hz.2], by linarith⟩ hσ hρ
    rw [i10Br_symm, mul_comm σ ρ] at hb
    have hh := i10_half_le (t := 1 - z) (by linarith [hz.2]) (by nlinarith [hz.2])
      (by linarith [hz.1])
    rw [show (1 - z) * (1 - (1 - z)) = z * (1 - z) by ring] at hh
    calc _ ≤ 11 * ((1 - z) ^ (1 / 2 : ℝ) * (ρ * σ) ^ (-(31 / 20) : ℝ)) := hb
      _ ≤ 11 * (3 / 2 * (z * (1 - z)) ^ (1 / 2 : ℝ) * (ρ * σ) ^ (-(31 / 20) : ℝ)) := by gcongr
      _ ≤ _ := by
          have := Real.rpow_nonneg (mul_nonneg hz.1.le (by linarith [hz.2]) : 0 ≤ z * (1 - z))
            (1 / 2 : ℝ)
          nlinarith [mul_nonneg this hP]

/-! ### The integrand `H` and the domination -/

/-- `H = D(ε, ρ) D(ε, σ) (z(1 - z)) ^ (ε - 1) · bracket` on `(z, ρ, σ)`. -/
noncomputable def i10KabH (ε : ℂ) (q : ℝ × ℝ × ℝ) : ℂ :=
  i10D ε q.2.1 * i10D ε q.2.2 * i10W ε q.1 * i10Br ε q.1 q.2.1 q.2.2

/-- **`K_ab = ε² ∫ H`.** -/
theorem i10Kab_eq (ε : ℂ) :
    i10Kab ε = ε ^ 2 * ∫ q in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i10KabH ε q := by
  rw [i10Kab, ← integral_const_mul]
  congr 1
  funext q
  rw [i10A_sub_one, i10A_sub_one, i10KabH]
  simp only [i10Br]
  ring

theorem norm_i10W_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    ‖i10W ε z‖ ≤ (z * (1 - z)) ^ (-(21 / 20) : ℝ) := by
  have hr' := (i9_eps_facts hε).2.2.1
  exact norm_cpow_le_rpow_of_le (i9_c_pos hz) ((i9_c_le z).trans (by norm_num))
    (by simp; linarith)

/-- **The dominating bound** for `H`. -/
theorem norm_i10KabH_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    ‖i10KabH ε q‖ ≤ 68 * ((q.1 * (1 - q.1)) ^ (-(11 / 20) : ℝ) *
      ((q.2.1 * (1 - q.2.1)) ^ (-(11 / 20) : ℝ) * (q.2.2 * (1 - q.2.2)) ^ (-(11 / 20) : ℝ))) := by
  obtain ⟨hz, hρ, hσ⟩ := hq
  set z := q.1
  set ρ := q.2.1
  set σ := q.2.2
  have hc := i9_c_pos hz
  have hρ1 : 0 < 1 - ρ := by linarith [hρ.2]
  have hσ1 : 0 < 1 - σ := by linarith [hσ.2]
  have h1 := norm_i10D_le hε hρ
  have h2 := norm_i10D_le hε hσ
  have h3 := norm_i10W_le hε hz
  have h4 := norm_i10Br_le hε hz hρ hσ
  have p1 := Real.rpow_nonneg hρ1.le (-(11 / 20) : ℝ)
  have p2 := Real.rpow_nonneg hσ1.le (-(11 / 20) : ℝ)
  have p3 := Real.rpow_nonneg hc.le (-(21 / 20) : ℝ)
  rw [i10KabH, norm_mul, norm_mul, norm_mul]
  calc _ ≤ (2 * ρ * (1 - ρ) ^ (-(11 / 20) : ℝ)) * (2 * σ * (1 - σ) ^ (-(11 / 20) : ℝ)) *
        (z * (1 - z)) ^ (-(21 / 20) : ℝ) *
        (17 * ((z * (1 - z)) ^ (1 / 2 : ℝ) * (ρ * σ) ^ (-(31 / 20) : ℝ))) := by
        have n1 : 0 ≤ 2 * ρ * (1 - ρ) ^ (-(11 / 20) : ℝ) :=
          mul_nonneg (mul_nonneg (by norm_num) hρ.1.le) p1
        have n2 : 0 ≤ 2 * σ * (1 - σ) ^ (-(11 / 20) : ℝ) :=
          mul_nonneg (mul_nonneg (by norm_num) hσ.1.le) p2
        exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) n1) h3 (norm_nonneg _)
          (mul_nonneg n1 n2)) h4 (norm_nonneg _) (mul_nonneg (mul_nonneg n1 n2) p3)
    _ = 68 * (((z * (1 - z)) ^ (-(21 / 20) : ℝ) * (z * (1 - z)) ^ (1 / 2 : ℝ)) *
        ((ρ ^ (1 : ℝ) * ρ ^ (-(31 / 20) : ℝ)) * (1 - ρ) ^ (-(11 / 20) : ℝ)) *
        ((σ ^ (1 : ℝ) * σ ^ (-(31 / 20) : ℝ)) * (1 - σ) ^ (-(11 / 20) : ℝ))) := by
        rw [Real.rpow_one, Real.rpow_one, Real.mul_rpow hρ.1.le hσ.1.le]; ring
    _ = _ := by
        rw [rpow_mul_rpow_eq (c := -(11 / 20)) hc (by norm_num),
          rpow_mul_rpow_eq (c := -(11 / 20)) hρ.1 (by norm_num),
          rpow_mul_rpow_eq (c := -(11 / 20)) hσ.1 (by norm_num),
          Real.mul_rpow hρ.1.le hρ1.le, Real.mul_rpow hσ.1.le hσ1.le]
        ring

theorem integrable_i10KabBound :
    IntegrableOn (fun q : ℝ × ℝ × ℝ => 68 * ((q.1 * (1 - q.1)) ^ (-(11 / 20) : ℝ) *
      ((q.2.1 * (1 - q.2.1)) ^ (-(11 / 20) : ℝ) * (q.2.2 * (1 - q.2.2)) ^ (-(11 / 20) : ℝ))))
      (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  rw [IntegrableOn, volume_restrict_prod3]
  exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      (integrableOn_mul_one_sub_rpow_Ioo (by norm_num)))).const_mul 68

theorem measurable_i10KabH (ε : ℂ) : Measurable (i10KabH ε) := by
  have hD := measurable_i10D ε
  have h1 : Measurable fun q : ℝ × ℝ × ℝ => i10D ε q.2.1 := hD.comp (by fun_prop)
  have h2 : Measurable fun q : ℝ × ℝ × ℝ => i10D ε q.2.2 := hD.comp (by fun_prop)
  have h3 : Measurable fun q : ℝ × ℝ × ℝ => i10W ε q.1 * i10Br ε q.1 q.2.1 q.2.2 := by
    unfold i10W i10Br i10Tau; fun_prop
  have : i10KabH ε = fun q => i10D ε q.2.1 * i10D ε q.2.2 * (i10W ε q.1 *
      i10Br ε q.1 q.2.1 q.2.2) := by funext q; rw [i10KabH]; ring
  rw [this]
  exact (h1.mul h2).mul h3

theorem integrableOn_i10KabH {ε : ℂ} (hε : ‖ε‖ < 1 / 20) :
    IntegrableOn (i10KabH ε) (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
  integrable_i10KabBound.mono' (measurable_i10KabH ε).aestronglyMeasurable
    (ae_restrict_of_forall_mem (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo))
      fun _ hq => norm_i10KabH_le hε hq)

/-! ### Analyticity -/

theorem differentiableAt_i10KabH {q : ℝ × ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) (ε : ℂ) :
    DifferentiableAt ℂ (fun ε => i10KabH ε q) ε := by
  obtain ⟨hz, hρ, hσ⟩ := hq
  have hτ : 0 < i10Tau q.1 q.2.1 q.2.2 := by
    unfold i10Tau; nlinarith [hz.1, hz.2, hρ.1, hσ.1]
  have e1 : ∀ r : ℝ, (fun ε : ℂ => (r : ℂ) ^ (ε - 1)) =
      fun ε => (r : ℂ) ^ ((1 : ℂ) * ε + -1) := fun r => by funext ε; ring_nf
  have dc : ∀ r : ℝ, 0 < r → DifferentiableAt ℂ (fun ε : ℂ => (r : ℂ) ^ (ε - 1)) ε :=
    fun r hr => by
      rw [e1]; exact differentiableAt_cpow_lin _ _ _ (Or.inl (ofReal_ne_zero.mpr hr.ne'))
  have hW : DifferentiableAt ℂ (fun ε => i10W ε q.1) ε := dc _ (i9_c_pos hz)
  have hB : DifferentiableAt ℂ (fun ε => i10Br ε q.1 q.2.1 q.2.2) ε := by
    unfold i10Br
    exact ((dc _ hτ).sub ((dc _ hσ.1).const_mul _)).sub ((dc _ hρ.1).const_mul _)
  unfold i10KabH
  exact (((differentiable_i10D hρ.2 ε).mul (differentiable_i10D hσ.2 ε)).mul hW).mul hB

theorem differentiableAt_i10KabInt {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 40) :
    DifferentiableAt ℂ (fun ε => ∫ q in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
      i10KabH ε q) ε₀ := by
  have hball : ∀ ε ∈ ball ε₀ (1 / 40), ‖ε‖ < 1 / 20 := fun ε hε => by
    have := norm_sub_norm_le ε ε₀
    rw [mem_ball, dist_eq_norm] at hε
    linarith
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
    integrable_i10KabBound (fun ε _ => (measurable_i10KabH ε).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem hS fun q hq ε hε => norm_i10KabH_le (hball ε hε) hq
  · exact ae_restrict_of_forall_mem hS fun q hq ε _ =>
      (differentiableAt_i10KabH hq ε).differentiableWithinAt

/-- **`h = ∫ H` is analytic near `0`.** -/
theorem analyticOnNhd_i10KabH : AnalyticOnNhd ℂ (fun ε => ∫ q in Ioo (0 : ℝ) 1 ×ˢ
    (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i10KabH ε q) (ball 0 (1 / 40)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_i10KabInt
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

end QED.ThreeLoopE
