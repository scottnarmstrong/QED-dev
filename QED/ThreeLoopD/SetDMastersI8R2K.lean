/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R2A

/-!
# Set (d), master `I₈`: the coefficients of the angular average in closed form

The coefficients `Aₖ(t) = ∑ᵢ Nᵢ Jₖ₋ᵢ(t)` of the angular average `A_ε = N_ε J_ε`
(`QED.ThreeLoopD.i8AC`) obey, since `∑ᵢ Nᵢ mₖ₋ᵢ = δₖ₀`,

  `t (t + 4) Aₖ₊₁' = -2 Aₖ₊₁ - t Aₖ + δₖ₀` (`QED.ThreeLoopD.hasDerivAt_i8AC`),

and `|Aₖ(t)| ≤ c/t`. In `ξ` (`t = (1 - ξ)²/ξ`, `r = (1 + ξ)/(1 - ξ)`) this reads
`(Aₖ₊₁/r)' = (t Aₖ - δₖ₀)/(1 + ξ)²`, and `Aₖ₊₁/r → 0` as `ξ → 0` fixes the constant
(`QED.ThreeLoopD.i8AC_succ_of`). Hence, with harmonic polylogarithms `H(w) = H(w; ξ)`,

  `A₀ = ξ/(1 - ξ)`, `A₁ = r (ξ/(1 + ξ) - H(-1))`,
  `A₂ = r (2ξ/(1 + ξ) - H(-1) - H(0, -1) + 2 H(-1, -1))`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8AC`, `QED.ThreeLoopD.i8AC_succ_of`.
* `QED.ThreeLoopD.i8AC_zero`, `QED.ThreeLoopD.i8AC_one`, `QED.ThreeLoopD.i8AC_two`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The coefficients `Aₖ(t) = ∑ᵢ Nᵢ Jₖ₋ᵢ(t)` of the angular average. -/
noncomputable def i8AC (t : ℝ) (k : ℕ) : ℂ := i13Cauchy i8NC (i8JC t) k

theorem i8_sum_prev {a f fp : ℕ → ℂ} (h0 : fp 0 = 0) (hs : ∀ j, fp (j + 1) = f j) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), a i * fp (k + 1 - i) =
      ∑ i ∈ Finset.range (k + 1), a i * f (k - i) := by
  rw [Finset.sum_range_succ, Nat.sub_self, h0, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show k + 1 - i = k - i + 1 by omega, hs]

/-- **The differential equation** `t (t + 4) Aₖ₊₁' = -2 Aₖ₊₁ - t Aₖ + δₖ₀`. -/
theorem hasDerivAt_i8AC (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => i8AC s (k + 1))
      ((-2 * i8AC t (k + 1) - t * i8AC t k + (if k = 0 then 1 else 0)) / (t * (t + 4))) t := by
  have hd : ∀ i ∈ Finset.range (k + 2), HasDerivAt (fun s => i8NC i * (i8Jr (k + 1 - i) s : ℂ))
      (i8NC i * (((-2 * i8Jr (k + 1 - i) t - t * i8Jpr (k + 1 - i) t -
        (i8M0r (k + 1 - i) - i8M0pr (k + 1 - i))) / (t * (t + 4)) : ℝ) : ℂ)) t :=
    fun i _ => ((hasDerivAt_i8Jr (k + 1 - i) ht).ofReal_comp).const_mul _
  have h := HasDerivAt.fun_sum hd
  have e : (fun s => i8AC s (k + 1)) =
      fun s => ∑ i ∈ Finset.range (k + 2), i8NC i * (i8Jr (k + 1 - i) s : ℂ) := by
    funext s
    simp only [i8AC, i13Cauchy, i8JC_eq]
  rw [e]
  refine h.congr_deriv ?_
  have hJp := i8_sum_prev (a := i8NC) (f := fun j => (i8Jr j t : ℂ))
    (fp := fun j => (i8Jpr j t : ℂ)) (by simp [i8Jpr]) (fun j => rfl) k
  have hMp := i8_sum_prev (a := i8NC) (f := fun j => (i8M0r j : ℂ))
    (fp := fun j => (i8M0pr j : ℂ)) (by simp [i8M0pr]) (fun j => rfl) k
  have hM1 := i8_cauchy_Mom0 (k + 1)
  have hM0 := i8_cauchy_Mom0 k
  simp only [i13Cauchy, i8M0C_eq] at hM1 hM0
  rw [hM0] at hMp
  rw [show k + 1 + 1 = k + 2 from rfl] at hM1
  have hA1 : i8AC t (k + 1) = ∑ i ∈ Finset.range (k + 2), i8NC i * (i8Jr (k + 1 - i) t : ℂ) := by
    simp only [i8AC, i13Cauchy, i8JC_eq]
  have hA0 : i8AC t k = ∑ i ∈ Finset.range (k + 1), i8NC i * (i8Jr (k - i) t : ℂ) := by
    simp only [i8AC, i13Cauchy, i8JC_eq]
  rw [hA1, hA0, ← hJp]
  have ht4 : ((t * (t + 4) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat] at ht4 ⊢
  simp only [mul_div_assoc', ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib]
  rw [hMp]
  have q1 : ∑ x ∈ Finset.range (k + 2), i8NC x * (-2 * (i8Jr (k + 1 - x) t : ℂ)) =
      -2 * ∑ i ∈ Finset.range (k + 2), i8NC i * (i8Jr (k + 1 - i) t : ℂ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have q2 : ∑ x ∈ Finset.range (k + 2), i8NC x * ((t : ℂ) * (i8Jpr (k + 1 - x) t : ℂ)) =
      t * ∑ i ∈ Finset.range (k + 2), i8NC i * (i8Jpr (k + 1 - i) t : ℂ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hk : (if k + 1 = 0 then (1 : ℂ) else 0) = 0 := by simp
  rw [q1, q2, hM1, hk]
  push_cast
  ring

/-- The constant of the bound `|Aₖ(t)| ≤ c/t`. -/
noncomputable def i8ACb (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), ‖i8NC i‖ * 2 ^ (k - i)

theorem norm_i8AC_le (k : ℕ) {t : ℝ} (ht : 0 < t) : ‖i8AC t k‖ ≤ i8ACb k / t := by
  unfold i8AC i13Cauchy i8ACb
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, i8JC_eq, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (abs_i8Jr_le _ ht) (norm_nonneg _)

theorem i8_T_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < (1 - x) ^ 2 / x :=
  div_pos (by nlinarith [hx.2]) hx.1

theorem i8_hasDerivAt_T {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => (1 - y) ^ 2 / y) (-(1 - x) * (1 + x) / x ^ 2) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have := (((hasDerivAt_id' x).const_sub 1).pow 2).div (hasDerivAt_id' x) h0
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- **The closed form of `Aₖ₊₁` from that of `Aₖ`**: if `Aₖ(t(x)) = Aₚ(x)`,
`C' = (t Aₚ - δₖ₀)/(1 + x)²` and `C → 0` at `0`, then `Aₖ₊₁(t(x)) = r(x) C(x)`. -/
theorem i8AC_succ_of {k : ℕ} {Ap Cx : ℝ → ℝ}
    (hAp : ∀ x ∈ Ioo (0 : ℝ) 1, i8AC ((1 - x) ^ 2 / x) k = (Ap x : ℂ))
    (hC : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Cx
      (((1 - x) ^ 2 / x * Ap x - (if k = 0 then 1 else 0)) / (1 + x) ^ 2) x)
    (hC0 : Tendsto Cx (𝓝[>] 0) (𝓝 0)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8AC ((1 - x) ^ 2 / x) (k + 1) = (((1 + x) / (1 - x) * Cx x : ℝ) : ℂ) := by
  set G : ℝ → ℂ := fun y => i8AC ((1 - y) ^ 2 / y) (k + 1) * (((1 - y) / (1 + y) : ℝ) : ℂ) -
    (Cx y : ℂ) with hG
  have hGd : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt G 0 y := by
    intro y hy
    have h0 : y ≠ 0 := hy.1.ne'
    have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    have h2 : 1 + y ≠ 0 := by linarith [hy.1]
    have hA := HasDerivAt.scomp (h := fun y : ℝ => (1 - y) ^ 2 / y) y
      (hasDerivAt_i8AC k (i8_T_pos hy)) (i8_hasDerivAt_T hy)
    have hq : HasDerivAt (fun y : ℝ => (1 - y) / (1 + y)) (-2 / (1 + y) ^ 2) y := by
      have := ((hasDerivAt_id' y).const_sub 1).div ((hasDerivAt_id' y).const_add 1) h2
      refine this.congr_deriv ?_
      field_simp
      ring
    have e := (hA.mul hq.ofReal_comp).sub (hC y hy).ofReal_comp
    refine e.congr_deriv ?_
    have h0' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
    have h1' : (1 - y : ℂ) ≠ 0 := by exact_mod_cast h1
    have h2' : (1 + y : ℂ) ≠ 0 := by exact_mod_cast h2
    simp only [Function.comp_apply, Complex.real_smul]
    rw [hAp y hy]
    generalize i8AC ((1 - y) ^ 2 / y) (k + 1) = A
    have h4 : ((1 - y) ^ 2 / y + 4 : ℂ) = (1 + y) ^ 2 / y := by
      field_simp; ring
    push_cast
    rw [h4]
    split_ifs <;> simp only [Complex.ofReal_one, Complex.ofReal_zero] <;> field_simp <;> ring
  have hlim : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    have hB : Tendsto (fun y : ℝ => i8ACb (k + 1) * y / (1 - y) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : ContinuousAt (fun y : ℝ => i8ACb (k + 1) * y / (1 - y) ^ 2) 0 :=
        (continuousAt_const.mul continuousAt_id).div (by fun_prop) (by norm_num)
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    have hP : Tendsto (fun y => i8AC ((1 - y) ^ 2 / y) (k + 1) *
        (((1 - y) / (1 + y) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hB
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
      have hq : ‖(((1 - y) / (1 + y) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor
        · have : 0 ≤ (1 - y) / (1 + y) := div_nonneg (by linarith [hy.2]) (by linarith [hy.1])
          linarith
        · rw [div_le_one (by linarith [hy.1])]; linarith [hy.1]
      rw [norm_mul]
      calc ‖i8AC ((1 - y) ^ 2 / y) (k + 1)‖ * ‖(((1 - y) / (1 + y) : ℝ) : ℂ)‖
          ≤ i8ACb (k + 1) / ((1 - y) ^ 2 / y) * 1 :=
            mul_le_mul (norm_i8AC_le _ (i8_T_pos hy)) hq (norm_nonneg _)
              (div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (i8_T_pos hy).le)
        _ = i8ACb (k + 1) * y / (1 - y) ^ 2 := by
            have : (1 - y) ^ 2 ≠ 0 := by have := hy.2; positivity
            field_simp [hy.1.ne']
    simpa [hG] using hP.sub (Complex.continuous_ofReal.tendsto 0 |>.comp hC0)
  have hconst : ∀ y ∈ Ioo (0 : ℝ) 1, G y = G x := fun y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hGd z hz).deriv) hy hx
  have hGx : G x = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
    exact (hconst y hy).symm
  simp only [hG, sub_eq_zero] at hGx
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have hq : (((1 - x) / (1 + x) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero h1 h2)
  rw [eq_div_of_mul_eq hq hGx]
  push_cast
  have h1' : (1 - x : ℂ) ≠ 0 := by exact_mod_cast h1
  have h2' : (1 + x : ℂ) ≠ 0 := by exact_mod_cast h2
  field_simp

/-! ### `A₀`, `A₁`, `A₂` -/

/-- `A₀(t(x)) = x/(1 - x)`. -/
theorem i8AC_zero_x {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8AC ((1 - x) ^ 2 / x) 0 = ((x / (1 - x) : ℝ) : ℂ) := by
  have hT := i8_T_pos hx
  have h := i8_t_NC_JC_zero hT
  rw [i13Xi_of_xi hx.1 hx.2.le, mul_comm] at h
  have e : i8AC ((1 - x) ^ 2 / x) 0 = i8NC 0 * i8JC ((1 - x) ^ 2 / x) 0 := by
    simp [i8AC, i13Cauchy]
  have hT' : (((1 - x) ^ 2 / x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  rw [e, eq_div_of_mul_eq hT' h]
  have h0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  have h1 : (1 - x : ℂ) ≠ 0 := by exact_mod_cast (by linarith [hx.2] : (1 : ℝ) - x ≠ 0)
  push_cast
  field_simp

/-- `A₁` in the variable `ξ`: `r (ξ/(1 + ξ) - H(-1))`. -/
noncomputable def i8A1x (x : ℝ) : ℝ := (1 + x) / (1 - x) * (x / (1 + x) - hpl [negOne] x)

/-- `A₂` in the variable `ξ`: `r (2ξ/(1 + ξ) - H(-1) - H(0, -1) + 2 H(-1, -1))`. -/
noncomputable def i8A2x (x : ℝ) : ℝ :=
  (1 + x) / (1 - x) * (2 * x / (1 + x) - hpl [negOne] x - hpl [zero, negOne] x +
    2 * hpl [negOne, negOne] x)

theorem i8_tendsto_rat_zero {c : ℝ} :
    Tendsto (fun x : ℝ => c * x / (1 + x)) (𝓝[>] 0) (𝓝 0) := by
  have : ContinuousAt (fun x : ℝ => c * x / (1 + x)) 0 :=
    (continuousAt_const.mul continuousAt_id).div (by fun_prop) (by norm_num)
  simpa using this.tendsto.mono_left nhdsWithin_le_nhds

theorem i8AC_one_x {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8AC ((1 - x) ^ 2 / x) 1 = (i8A1x x : ℂ) := by
  have hlim : Tendsto (fun x : ℝ => 1 * x / (1 + x) - hpl [negOne] x) (𝓝[>] 0) (𝓝 0) := by
    have := (i8_tendsto_rat_zero (c := 1)).sub (tendsto_hpl_zero (w := [negOne]) (by simp))
    simpa using this
  refine i8AC_succ_of (k := 0) (Ap := fun x => x / (1 - x))
    (Cx := fun x => 1 * x / (1 + x) - hpl [negOne] x) (fun y hy => i8AC_zero_x hy)
    (fun y hy => ?_) hlim hx |>.trans ?_
  · have h0 : y ≠ 0 := hy.1.ne'
    have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    have h2 : 1 + y ≠ 0 := by linarith [hy.1]
    have e := (((hasDerivAt_id' y).const_mul 1).div ((hasDerivAt_id' y).const_add 1) h2).sub
      (hasDerivAt_hpl_cons negOne [] hy)
    refine e.congr_deriv ?_
    simp only [kernel_negOne, hpl_nil, ↓reduceIte]
    field_simp
    ring
  · unfold i8A1x; simp

theorem i8AC_two_x {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8AC ((1 - x) ^ 2 / x) 2 = (i8A2x x : ℂ) := by
  refine i8AC_succ_of (k := 1) (Ap := i8A1x)
    (Cx := fun x => 2 * x / (1 + x) - hpl [negOne] x - hpl [zero, negOne] x +
      2 * hpl [negOne, negOne] x) (fun y hy => i8AC_one_x hy) (fun y hy => ?_) ?_ hx |>.trans ?_
  · have h0 : y ≠ 0 := hy.1.ne'
    have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    have h2 : 1 + y ≠ 0 := by linarith [hy.1]
    have e := (((((hasDerivAt_id' y).const_mul 2).div ((hasDerivAt_id' y).const_add 1) h2).sub
      (hasDerivAt_hpl_cons negOne [] hy)).sub (hasDerivAt_hpl_cons zero [negOne] hy)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hy).const_mul 2)
    refine e.congr_deriv ?_
    unfold i8A1x
    simp only [kernel_negOne, kernel_zero, hpl_nil, one_ne_zero, ↓reduceIte]
    field_simp
    ring
  · have := (((i8_tendsto_rat_zero (c := 2)).sub (tendsto_hpl_zero (w := [negOne]) (by simp))).sub
      (tendsto_hpl_zero (w := [zero, negOne]) (by simp))).add
      ((tendsto_hpl_zero (w := [negOne, negOne]) (by simp)).const_mul 2)
    simpa using this
  · unfold i8A2x; simp

theorem i8_xi_mem {t : ℝ} (ht : 0 < t) : i13Xi t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i13Xi_pos ht.le, i13Xi_lt_one ht⟩

theorem i8AC_one {t : ℝ} (ht : 0 < t) : i8AC t 1 = (i8A1x (i13Xi t) : ℂ) := by
  conv_lhs => rw [i13Xi_t ht.le]
  exact i8AC_one_x (i8_xi_mem ht)

theorem i8AC_two {t : ℝ} (ht : 0 < t) : i8AC t 2 = (i8A2x (i13Xi t) : ℂ) := by
  conv_lhs => rw [i13Xi_t ht.le]
  exact i8AC_two_x (i8_xi_mem ht)

theorem i8AC_zero {t : ℝ} (ht : 0 < t) :
    i8AC t 0 = ((i13Xi t / (1 - i13Xi t) : ℝ) : ℂ) := by
  conv_lhs => rw [i13Xi_t ht.le]
  exact i8AC_zero_x (i8_xi_mem ht)

end QED.ThreeLoopD
