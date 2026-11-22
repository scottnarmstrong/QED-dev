/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Prim
public import QED.ThreeLoopD.SetDMastersI5C1Bas
public import QED.Polylog.HPLLowWeight
public import QED.Polylog.HPLLyndon3
public import QED.Polylog.DilogPM

/-!
# Set (d), master `I₅`: the kernel `K(ξ)` in trilogarithms

For `0 < ξ < 1` the harmonic-polylogarithm form of `K(ξ)` (`QED.ThreeLoopD.i5K1x`) equals an
explicit combination of `Li₃` at `ξ, -ξ, 1 - ξ, ξ/(1+ξ), 1/(1+ξ), 1 - ξ², ξ²`, of `Li₂ (±ξ)`
and of logarithms (`QED.ThreeLoopD.i5K1x_eq_li`). The only non-elementary step is the sum
`H(0,1,-1; ξ) + H(0,-1,1; ξ)` (`QED.ThreeLoopD.i5C1_hplX_eq`): its derivative is
`H(1; ξ) H(-1; ξ) / ξ` by the shuffle product, and both sides vanish at `0⁺`.

## Main results

* `QED.ThreeLoopD.i5C1_tendsto_log_pow_mul`: `log t ^ k · A(t) → 0` at `0⁺` when `A` is
  differentiable at `0` with `A 0 = 0`.
* `QED.ThreeLoopD.i5C1_hplX_eq`: `H(0,1,-1; ξ) + H(0,-1,1; ξ) = X(ξ)`.
* `QED.ThreeLoopD.i5K1x_eq_li`: the trilogarithm form of `K(ξ)`.
-/

@[expose] public section

open Set Real Filter Topology QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- `log t ^ k · t → 0` at `0⁺`. -/
theorem i5C1_tendsto_log_pow_mul_self (k : ℕ) :
    Tendsto (fun t : ℝ => log t ^ k * t) (𝓝[>] 0) (𝓝 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_mul]
    exact tendsto_id.mono_right nhdsWithin_le_nhds
  have hkr : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  have h := (tendsto_log_mul_rpow_nhdsGT_zero hkr).pow k
  rw [zero_pow hk.ne'] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [mul_pow, ← Real.rpow_natCast (t ^ (1 / (k : ℝ))), ← Real.rpow_mul ht.le,
    one_div_mul_cancel (by positivity), Real.rpow_one]

/-- `log t ^ k · A(t) → 0` at `0⁺` when `A` is differentiable at `0` with `A 0 = 0`. -/
theorem i5C1_tendsto_log_pow_mul (k : ℕ) {A : ℝ → ℝ} (hA : DifferentiableAt ℝ A 0)
    (h0 : A 0 = 0) : Tendsto (fun t : ℝ => log t ^ k * A t) (𝓝[>] 0) (𝓝 0) := by
  have hs := hA.hasDerivAt.tendsto_slope_zero_right
  have h := (i5C1_tendsto_log_pow_mul_self k).mul hs
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  field_simp

/-- A trilogarithm with derivative `V · D`, from `Li₂ (f x) = V` and `f'/f x = D`. -/
theorem i5C1_hasDerivAt_Li₃ {f : ℝ → ℝ} {f' x V D : ℝ} (hf : HasDerivAt f f' x)
    (h0 : f x ≠ 0) (h1 : |f x| < 1) (hV : Li₂ (f x) = V) (hD : f' / f x = D) :
    HasDerivAt (fun x => Li₃ (f x)) (V * D) x := by
  refine ((hasDerivAt_Li₃ h1 h0).comp x hf).congr_deriv ?_
  rw [← hV, ← hD]
  ring

/-- The closed form `X(ξ)` of `H(0,1,-1; ξ) + H(0,-1,1; ξ)`. -/
noncomputable def i5C1Xf (t : ℝ) : ℝ :=
  Li₂ (-t) * log (1 - t) + Li₂ t * log (1 + t) + 5 / 4 * Li₃ (t / (1 + t)) +
    1 / 4 * Li₃ (1 / (1 + t)) + 13 / 4 * Li₃ (-t) + (-1) * Li₃ (1 - t) +
    1 / 2 * Li₃ (1 - t ^ 2) + 2 * Li₃ t + (-1 / 2) * Li₃ (t ^ 2) +
    (-(π ^ 2 / 24)) * log (1 + t) + π ^ 2 / 12 * log (1 - t) + zeta3 / 4 +
    (-1 / 4) * log (1 + t) ^ 3 + 5 / 8 * (log (1 + t) ^ 2 * log t) +
    log (1 + t) * log t * log (1 - t)

theorem hasDerivAt_i5C1Xf {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i5C1Xf (-log (1 - t) * log (1 + t) / t) t := by
  obtain ⟨h0, h1⟩ := ht
  have hm : 0 < 1 - t := by linarith
  have hp : 0 < 1 + t := by linarith
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have hid : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id' t
  have dn : HasDerivAt (fun y : ℝ => -y) (-1) t := hasDerivAt_neg' t
  have dm : HasDerivAt (fun y : ℝ => 1 - y) (-1) t := by simpa using hid.const_sub 1
  have dp : HasDerivAt (fun y : ℝ => 1 + y) 1 t := by simpa using hid.const_add 1
  have dsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have dq : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * t)) t := dsq.const_sub 1
  have ddiv : HasDerivAt (fun y : ℝ => y / (1 + y)) ((1 * (1 + t) - t * 1) / (1 + t) ^ 2) t :=
    hid.div dp hp.ne'
  have dinv : HasDerivAt (fun y : ℝ => 1 / (1 + y)) ((0 * (1 + t) - 1 * 1) / (1 + t) ^ 2) t :=
    (hasDerivAt_const t (1 : ℝ)).div dp hp.ne'
  have lx : HasDerivAt (fun y : ℝ => log y) (1 / t) t := by
    simpa [one_div] using hasDerivAt_log h0.ne'
  have lm : HasDerivAt (fun y : ℝ => log (1 - y)) (-1 / (1 - t)) t := dm.log hm.ne'
  have lp : HasDerivAt (fun y : ℝ => log (1 + y)) (1 / (1 + t)) t := dp.log hp.ne'
  have l2p : HasDerivAt (fun y : ℝ => Li₂ y) (-log (1 - t) * (1 / t)) t :=
    i5C1_hasDerivAt_Li₂ hid h0.ne' (by rw [abs_of_pos h0]; exact h1) rfl (by ring)
  have l2m : HasDerivAt (fun y : ℝ => Li₂ (-y)) (-log (1 + t) * (1 / t)) t :=
    i5C1_hasDerivAt_Li₂ dn (by simpa using h0.ne') (by rw [abs_neg, abs_of_pos h0]; exact h1)
      (by rw [sub_neg_eq_add]) (by field_simp)
  -- the dilogarithm values at the trilogarithm arguments
  have vdiv : Li₂ (t / (1 + t)) = -Li₂ (-t) - log (1 + t) ^ 2 / 2 := by
    simpa only [Li_two] using Li_two_div_one_add ⟨h0, h1⟩
  have vinv : Li₂ (1 / (1 + t)) =
      π ^ 2 / 6 + log t * log (1 + t) - log (1 + t) ^ 2 / 2 + Li₂ (-t) := by
    simpa only [Li_two] using Li_two_inv_one_add ⟨h0, h1⟩
  have vsub : Li₂ (1 - t) = π ^ 2 / 6 - log t * log (1 - t) - Li₂ t := by
    simpa only [Li_two] using Li_two_one_sub' ⟨h0, h1⟩
  have vsq : Li₂ (t ^ 2) = 2 * (Li₂ t + Li₂ (-t)) := by
    have := Li₂_add_Li₂_neg (x := t) (by rw [abs_of_pos h0]; exact h1.le)
    linarith
  have vsubsq : Li₂ (1 - t ^ 2) =
      π ^ 2 / 6 - 2 * log t * (log (1 - t) + log (1 + t)) - 2 * (Li₂ t + Li₂ (-t)) := by
    have h := Li_two_one_sub' (u := t ^ 2) ⟨by positivity, by nlinarith⟩
    simp only [Li_two] at h
    rw [h, vsq, Real.log_pow, show 1 - t ^ 2 = (1 - t) * (1 + t) by ring,
      Real.log_mul hm.ne' hp.ne']
    push_cast
    ring
  have t3div : HasDerivAt (fun y : ℝ => Li₃ (y / (1 + y)))
      ((-Li₂ (-t) - log (1 + t) ^ 2 / 2) * (1 / (t * (1 + t)))) t :=
    i5C1_hasDerivAt_Li₃ ddiv (by positivity)
      (by rw [abs_of_pos (by positivity), div_lt_one hp]; linarith) vdiv (by field_simp; ring)
  have t3inv : HasDerivAt (fun y : ℝ => Li₃ (1 / (1 + y)))
      ((π ^ 2 / 6 + log t * log (1 + t) - log (1 + t) ^ 2 / 2 + Li₂ (-t)) * (-1 / (1 + t))) t :=
    i5C1_hasDerivAt_Li₃ dinv (by positivity)
      (by rw [abs_of_pos (by positivity), div_lt_one hp]; linarith) vinv (by field_simp; ring)
  have t3m : HasDerivAt (fun y : ℝ => Li₃ (-y)) (Li₂ (-t) * (1 / t)) t :=
    i5C1_hasDerivAt_Li₃ dn (by simpa using h0.ne') (by rw [abs_neg, abs_of_pos h0]; exact h1)
      rfl (by field_simp)
  have t3sub : HasDerivAt (fun y : ℝ => Li₃ (1 - y))
      ((π ^ 2 / 6 - log t * log (1 - t) - Li₂ t) * (-1 / (1 - t))) t :=
    i5C1_hasDerivAt_Li₃ dm hm.ne' (by rw [abs_of_pos hm]; linarith) vsub rfl
  have t3q : HasDerivAt (fun y : ℝ => Li₃ (1 - y ^ 2))
      ((π ^ 2 / 6 - 2 * log t * (log (1 - t) + log (1 + t)) - 2 * (Li₂ t + Li₂ (-t))) *
        (-(2 * t) / (1 - t ^ 2))) t :=
    i5C1_hasDerivAt_Li₃ dq hq.ne' (by rw [abs_of_pos hq]; nlinarith) vsubsq rfl
  have t3p : HasDerivAt (fun y : ℝ => Li₃ y) (Li₂ t * (1 / t)) t :=
    i5C1_hasDerivAt_Li₃ hid h0.ne' (by rw [abs_of_pos h0]; exact h1) rfl (by ring)
  have t3sq : HasDerivAt (fun y : ℝ => Li₃ (y ^ 2)) (2 * (Li₂ t + Li₂ (-t)) * (2 / t)) t :=
    i5C1_hasDerivAt_Li₃ dsq (by positivity) (by rw [abs_of_pos (by positivity)]; nlinarith)
      vsq (by field_simp)
  refine HasDerivAt.congr_deriv (f := i5C1Xf)
    (((((((((((((((l2m.mul lm).add (l2p.mul lp)).add (t3div.const_mul (5 / 4))).add
      (t3inv.const_mul (1 / 4))).add (t3m.const_mul (13 / 4))).add (t3sub.const_mul (-1))).add
      (t3q.const_mul (1 / 2))).add (t3p.const_mul 2)).add (t3sq.const_mul (-1 / 2))).add
      (lp.const_mul (-(π ^ 2 / 24)))).add (lm.const_mul (π ^ 2 / 12))).add
      (hasDerivAt_const t (zeta3 / 4))).add ((lp.pow 3).const_mul (-1 / 4))).add
      (((lp.pow 2).mul lx).const_mul (5 / 8))).add ((lp.mul lx).mul lm)) ?_
  simp only [Pi.mul_apply, Pi.pow_apply]
  field_simp
  ring

/-- `X(ξ) → 0` at `0⁺`. -/
theorem tendsto_i5C1Xf_zero : Tendsto i5C1Xf (𝓝[>] 0) (𝓝 0) := by
  have hL2 : DifferentiableAt ℝ Li₂ 0 := hasDerivAt_Li₂_zero.differentiableAt
  have hL2m : DifferentiableAt ℝ (fun t : ℝ => Li₂ (-t)) 0 :=
    DifferentiableAt.comp (g := Li₂) (f := fun t : ℝ => -t) 0 (by simpa using hL2)
      differentiableAt_id.neg
  have hA0 := i5C1_tendsto_log_pow_mul 0
    (A := fun t => Li₂ (-t) * log (1 - t) + Li₂ t * log (1 + t) -
      π ^ 2 / 24 * log (1 + t) + π ^ 2 / 12 * log (1 - t) - log (1 + t) ^ 3 / 4)
    (by fun_prop (disch := norm_num)) (by simp)
  have hA1 := i5C1_tendsto_log_pow_mul 1
    (A := fun t => 5 / 8 * log (1 + t) ^ 2 + log (1 + t) * log (1 - t))
    (by fun_prop (disch := norm_num)) (by simp)
  have hIcc : ∀ {g : ℝ → ℝ}, (∀ x ∈ Ioo (0 : ℝ) 1, -1 ≤ g x ∧ g x ≤ 1) →
      ∀ x ∈ Ioo (0 : ℝ) 1, g x ∈ Icc (-1 : ℝ) 1 := fun h x hx => h x hx
  have c1 := tendsto_Li_comp_zero (k := 3) (by norm_num) (g := fun t : ℝ => t / (1 + t))
    (by fun_prop (disch := norm_num)) (by norm_num) (hIcc fun x hx => by
      obtain ⟨a, b⟩ := hx
      exact ⟨by have : 0 ≤ x / (1 + x) := by positivity
                linarith, by rw [div_le_one (by linarith)]; linarith⟩)
  have c2 := tendsto_Li_comp_zero (k := 3) (by norm_num) (g := fun t : ℝ => 1 / (1 + t))
    (by fun_prop (disch := norm_num)) (by norm_num) (hIcc fun x hx => by
      obtain ⟨a, b⟩ := hx
      exact ⟨by have : 0 ≤ 1 / (1 + x) := by positivity
                linarith, by rw [div_le_one (by linarith)]; linarith⟩)
  have c3 := tendsto_Li_comp_zero (k := 3) (by norm_num) (g := fun t : ℝ => -t)
    (by fun_prop) (by norm_num) (hIcc fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have c4 := tendsto_Li_comp_zero (k := 3) (by norm_num) (g := fun t : ℝ => 1 - t)
    (by fun_prop) (by norm_num) (hIcc fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have c5 := tendsto_Li_comp_zero (k := 3) (by norm_num) (g := fun t : ℝ => 1 - t ^ 2)
    (by fun_prop) (by norm_num) (hIcc fun x hx => ⟨by nlinarith [hx.2, hx.1],
      by nlinarith [hx.1]⟩)
  have c6 := tendsto_Li_comp_zero (k := 3) (by norm_num) (g := fun t : ℝ => t)
    (by fun_prop) (by norm_num) (hIcc fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have c7 := tendsto_Li_comp_zero (k := 3) (by norm_num) (g := fun t : ℝ => t ^ 2)
    (by fun_prop) (by norm_num) (hIcc fun x hx => ⟨by nlinarith [hx.1],
      by nlinarith [hx.1, hx.2]⟩)
  have h := ((((((((c1.const_mul (5 / 4)).add (c2.const_mul (1 / 4))).add
    (c3.const_mul (13 / 4))).add (c4.const_mul (-1))).add (c5.const_mul (1 / 2))).add
    (c6.const_mul 2)).add (c7.const_mul (-1 / 2))).add
    (tendsto_const_nhds (x := zeta3 / 4))).add (hA0.add hA1)
  simp only [Li_three] at h
  convert h using 1
  · funext t
    simp only [i5C1Xf, pow_zero, pow_one]
    ring
  · norm_num [Li₃_one]
    ring

/-- `H(0,1,-1; ξ) + H(0,-1,1; ξ) = X(ξ)` on `(0, 1)`. -/
theorem i5C1_hplX_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, negOne] t + hpl [zero, negOne, one] t = i5C1Xf t := by
  have key := eq_of_hasDerivAt_zero_of_tendsto_right
    (F := fun x => hpl [zero, one, negOne] x + hpl [zero, negOne, one] x - i5C1Xf x)
    (c := 0) zero_lt_one (fun x hx => ?_) ?_ t ht
  · linarith
  · have h := ((hasDerivAt_hpl_cons zero [one, negOne] hx).add
      (hasDerivAt_hpl_cons zero [negOne, one] hx)).sub (hasDerivAt_i5C1Xf hx)
    have hs := hpl_mul_hpl [one] [negOne] hx
    simp [shuffle, shuffleAux, hpl_one hx, hpl_negOne hx] at hs
    refine h.congr_deriv ?_
    simp only [kernel_zero]
    linear_combination (-x⁻¹) * hs
  · simpa using ((tendsto_hpl_zero (w := [zero, one, negOne]) (by simp [AllZero])).add
      (tendsto_hpl_zero (w := [zero, negOne, one]) (by simp [AllZero]))).sub tendsto_i5C1Xf_zero

/-- The trilogarithm form of `K(ξ)` on `(0, 1)`. -/
theorem i5K1x_eq_li {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    i5K1x ξ = Li₂ (-ξ) * log ξ - 2 * Li₂ (-ξ) * log (1 - ξ) - 8 * Li₂ ξ * log (1 + ξ) +
      2 * Li₂ ξ * log ξ - 2 * Li₂ ξ * log (1 - ξ) + 2 * Li₂ ξ - 10 * Li₃ (ξ / (1 + ξ)) -
      2 * Li₃ (1 / (1 + ξ)) - 30 * Li₃ (-ξ) + 6 * Li₃ (1 - ξ) - 4 * Li₃ (1 - ξ ^ 2) -
      18 * Li₃ ξ + 4 * Li₃ (ξ ^ 2) + π ^ 2 * log (1 + ξ) / 3 - π ^ 2 * log (1 - ξ) / 2 +
      2 * log (1 + ξ) ^ 3 - 5 * log (1 + ξ) ^ 2 * log ξ - 8 * log (1 + ξ) * log ξ * log (1 - ξ) +
      log ξ ^ 2 * log (1 - ξ) / 2 - log ξ * log (1 - ξ) ^ 2 + log ξ * log (1 - ξ) := by
  have hX := i5C1_hplX_eq hξ
  have hr : Li₂ (1 - ξ) = π ^ 2 / 6 - log ξ * log (1 - ξ) - Li₂ ξ := by
    simpa only [Li_two] using Li_two_one_sub' hξ
  unfold i5K1x
  rw [hpl_one hξ, hpl_zero_one hξ, hpl_one_zero hξ, hpl_zero_zero_negOne hξ,
    hpl_zero_zero_one hξ, hpl_zero_negOne_zero hξ, hpl_zero_one_zero hξ, hpl_zero_one_one hξ,
    hpl_one_zero_zero hξ, hpl_one_zero_negOne hξ]
  simp only [Li_two, Li_three]
  unfold i5C1Xf at hX
  linear_combination (2 * log (1 - ξ)) * hr - 8 * hX

end QED.ThreeLoopD
