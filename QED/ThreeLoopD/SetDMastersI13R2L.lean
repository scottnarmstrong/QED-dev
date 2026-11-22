/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R2F
public import QED.Polylog.ExtraIntegrals

/-!
# Set (d), master `I₁₃`: the limit of `F₂ - A₂` at infinity

As `t → ∞`, `ξ(t) → 0⁺`. In terms of `ξ` and the normalized remainders

  `a = (log (1 - ξ) + ξ + ξ²/2)/ξ²`, `b = (log (1 + ξ) - ξ + ξ²/2)/ξ²`,
  `d = (Li₂ (-ξ) + ξ - ξ²/4)/ξ²`,

all `O(ξ)`, the difference of the primitives `F₂ - A₂` is (`QED.ThreeLoopD.i13F2_sub_prim2`)

  `-8 - π²/3 + ξ Q₁ + ξ log ξ Q₂ + ξ log² ξ Q₃ + 11a + 6a log ξ - 2b log ξ - 2d
    + 8 log ξ Li₂ ξ - 8 Li₃ ξ - 16 Li₃ (-ξ)`

with polynomials `Qᵢ` in `ξ, a, b, d`. Every term but the first tends to `0`, so
`F₂ - A₂ → -8 - π²/3` (`QED.ThreeLoopD.tendsto_i13F2_sub_prim2`).

## Main results

* `QED.ThreeLoopD.i13_abs_Li₂_sub_le`.
* `QED.ThreeLoopD.tendsto_i13F2_sub_prim2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### Remainder bounds -/

/-- `|Li₂ y - y - y²/4| ≤ 2 |y|³` for `|y| ≤ 1/2`. -/
theorem i13_abs_Li₂_sub_le {y : ℝ} (hy : |y| ≤ 1 / 2) : |Li₂ y - y - y ^ 2 / 4| ≤ 2 * |y| ^ 3 := by
  have hs := hasSum_Li₂ (hy.trans (by norm_num))
  have ht := (hasSum_nat_add_iff' 2).mpr hs
  have hg : HasSum (fun n : ℕ => |y| ^ 3 * (1 / 2 : ℝ) ^ n) (|y| ^ 3 * 2) := by
    have := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at this
    simpa using this.mul_left (|y| ^ 3)
  have hle := ht.norm_le_of_bounded hg fun n => by
    have h1 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) + 1 := by
      have := (n + 2 : ℕ).cast_nonneg (α := ℝ)
      linarith
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < (((n + 2 : ℕ) : ℝ) + 1) ^ 2)]
    calc |y| ^ (n + 2 + 1) / (((n + 2 : ℕ) : ℝ) + 1) ^ 2 ≤ |y| ^ (n + 2 + 1) :=
          div_le_self (by positivity) (one_le_pow₀ h1)
      _ = |y| ^ 3 * |y| ^ n := by ring
      _ ≤ |y| ^ 3 * (1 / 2) ^ n := by
          gcongr
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Real.norm_eq_abs] at hle
  norm_num at hle
  calc |Li₂ y - y - y ^ 2 / 4| = |Li₂ y - (y + y ^ 2 / 4)| := by ring_nf
    _ ≤ 2 * |y| ^ 3 := by linarith

/-- `a(ξ) = (log (1 - ξ) + ξ + ξ²/2)/ξ²`. -/
noncomputable def i13Ra (ξ : ℝ) : ℝ := (Real.log (1 - ξ) + ξ + ξ ^ 2 / 2) / ξ ^ 2

/-- `b(ξ) = (log (1 + ξ) - ξ + ξ²/2)/ξ²`. -/
noncomputable def i13Rb (ξ : ℝ) : ℝ := (Real.log (1 + ξ) - ξ + ξ ^ 2 / 2) / ξ ^ 2

/-- `d(ξ) = (Li₂ (-ξ) + ξ - ξ²/4)/ξ²`. -/
noncomputable def i13Rd (ξ : ℝ) : ℝ := (Li₂ (-ξ) + ξ - ξ ^ 2 / 4) / ξ ^ 2

theorem i13_abs_div_sq_le {r ξ : ℝ} (hξ : 0 < ξ) (h : |r| ≤ 2 * ξ ^ 3) :
    |r / ξ ^ 2| ≤ 2 * ξ := by
  rw [abs_div, abs_of_pos (pow_pos hξ 2), div_le_iff₀ (pow_pos hξ 2)]
  calc |r| ≤ 2 * ξ ^ 3 := h
    _ = 2 * ξ * ξ ^ 2 := by ring

theorem i13_abs_cube_div_le {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) (1 / 2)) :
    ξ ^ 3 / (1 - ξ) ≤ 2 * ξ ^ 3 := by
  rw [div_le_iff₀ (by linarith [hξ.2])]
  nlinarith [hξ.1, hξ.2, pow_pos hξ.1 3]

theorem abs_i13Ra_le {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) (1 / 2)) : |i13Ra ξ| ≤ 2 * ξ := by
  have ha : |ξ| < 1 := by rw [abs_of_pos hξ.1]; linarith [hξ.2]
  have h := Real.abs_log_sub_add_sum_range_le ha 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos hξ.1] at h
  norm_num at h
  refine i13_abs_div_sq_le hξ.1 ?_
  calc |Real.log (1 - ξ) + ξ + ξ ^ 2 / 2| = |ξ + ξ ^ 2 / 2 + Real.log (1 - ξ)| := by ring_nf
    _ ≤ 2 * ξ ^ 3 := h.trans (i13_abs_cube_div_le hξ)

theorem abs_i13Rb_le {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) (1 / 2)) : |i13Rb ξ| ≤ 2 * ξ := by
  have ha : |-ξ| < 1 := by rw [abs_neg, abs_of_pos hξ.1]; linarith [hξ.2]
  have h := Real.abs_log_sub_add_sum_range_le ha 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos hξ.1,
    sub_neg_eq_add] at h
  norm_num at h
  refine i13_abs_div_sq_le hξ.1 ?_
  calc |Real.log (1 + ξ) - ξ + ξ ^ 2 / 2| = |-ξ + ξ ^ 2 / 2 + Real.log (1 + ξ)| := by ring_nf
    _ ≤ 2 * ξ ^ 3 := h.trans (i13_abs_cube_div_le hξ)

theorem abs_i13Rd_le {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) (1 / 2)) : |i13Rd ξ| ≤ 2 * ξ := by
  have hy : |-ξ| ≤ 1 / 2 := by rw [abs_neg, abs_of_pos hξ.1]; exact hξ.2.le
  have h := i13_abs_Li₂_sub_le hy
  rw [abs_neg, abs_of_pos hξ.1] at h
  refine i13_abs_div_sq_le hξ.1 ?_
  calc |Li₂ (-ξ) + ξ - ξ ^ 2 / 4| = |Li₂ (-ξ) - -ξ - (-ξ) ^ 2 / 4| := by ring_nf
    _ ≤ 2 * ξ ^ 3 := h

theorem i13_tendsto_of_abs_le {R : ℝ → ℝ} (hb : ∀ ξ ∈ Ioo (0 : ℝ) (1 / 2), |R ξ| ≤ 2 * ξ) :
    Tendsto R (𝓝[>] 0) (𝓝 0) ∧ Tendsto (fun ξ => R ξ * Real.log ξ) (𝓝[>] 0) (𝓝 0) := by
  have hI : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hx : Tendsto (fun ξ : ℝ => 2 * ξ) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ξ : ℝ => 2 * ξ) (𝓝 0) (𝓝 (2 * 0)) := (continuous_const_mul 2).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hxl : Tendsto (fun ξ : ℝ => 2 * |ξ * Real.log ξ|) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_mul_log.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))).abs.const_mul 2
    simpa using this
  refine ⟨squeeze_zero_norm' ?_ hx, squeeze_zero_norm' ?_ hxl⟩
  · filter_upwards [hI] with ξ hξ using hb ξ hξ
  · filter_upwards [hI] with ξ hξ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hξ.1]
    calc |R ξ| * |Real.log ξ| ≤ 2 * ξ * |Real.log ξ| :=
          mul_le_mul_of_nonneg_right (hb ξ hξ) (abs_nonneg _)
      _ = 2 * (ξ * |Real.log ξ|) := by ring

/-! ### The difference of the primitives -/

/-- The polynomial `Q₁`. -/
noncomputable def i13LimQ1 (ξ a _b d : ℝ) : ℝ :=
  16 * a ^ 3 * ξ ^ 5 - 32 * a ^ 2 * ξ ^ 5 - 56 * a ^ 2 * ξ ^ 4 - 24 * a ^ 2 * ξ ^ 3 -
    8 * a ^ 2 * ξ ^ 2 - 8 * a ^ 2 * ξ - 4 * a * π ^ 2 * ξ / 3 + 20 * a * ξ ^ 5 + 72 * a * ξ ^ 4 +
    99 * a * ξ ^ 3 + 48 * a * ξ ^ 2 + 4 * a * ξ + 8 * a + 2 * d * ξ ^ 3 + π ^ 2 * ξ +
    4 * π ^ 2 / 3 - 4 * ξ ^ 5 - 22 * ξ ^ 4 - 51 * ξ ^ 3 - 59 * ξ ^ 2 - 16 * ξ + 17

/-- The polynomial `Q₂`. -/
noncomputable def i13LimQ2 (ξ a b d : ℝ) : ℝ :=
  -24 * a ^ 2 * ξ ^ 3 + 34 * a * ξ ^ 3 + 56 * a * ξ ^ 2 + 24 * a * ξ + 8 * a + 2 * b * ξ ^ 3 +
    8 * d * ξ - 12 * ξ ^ 3 - 36 * ξ ^ 2 - 53 * ξ - 36

/-- The polynomial `Q₃`. -/
noncomputable def i13LimQ3 (ξ a _b _d : ℝ) : ℝ := 12 * a * ξ - 9 * ξ - 12

/-- `F₂ - A₂` in terms of `ξ`. -/
noncomputable def i13Dif2 (ξ : ℝ) : ℝ :=
  -8 - π ^ 2 / 3 + (ξ * i13LimQ1 ξ (i13Ra ξ) (i13Rb ξ) (i13Rd ξ) +
    ξ * Real.log ξ * i13LimQ2 ξ (i13Ra ξ) (i13Rb ξ) (i13Rd ξ) +
    ξ * Real.log ξ ^ 2 * i13LimQ3 ξ (i13Ra ξ) (i13Rb ξ) (i13Rd ξ) + 11 * i13Ra ξ +
    6 * (i13Ra ξ * Real.log ξ) - 2 * (i13Rb ξ * Real.log ξ) - 2 * i13Rd ξ +
    8 * (Real.log ξ * Li₂ ξ) - 8 * Li₃ ξ - 16 * Li₃ (-ξ))

theorem i13F2_sub_prim2 {t : ℝ} (ht : 0 < t) : i13F2 t - i13Prim2 t = i13Dif2 (i13Xi t) := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have hlog := i13_log_eq_xi ht
  unfold i13F2 i13Prim2
  rw [hlog]
  set ξ := i13Xi t
  have h0 : ξ ≠ 0 := hx0.ne'
  have h1 : 1 - ξ ≠ 0 := by linarith
  rw [hT]
  unfold i13Dif2 i13Psi2 i13LimQ1 i13LimQ2 i13LimQ3 i13Ra i13Rb i13Rd Real.negMulLog
  field_simp
  ring

theorem tendsto_i13Dif2 : Tendsto i13Dif2 (𝓝[>] 0) (𝓝 (-8 - π ^ 2 / 3)) := by
  have hx : Tendsto (fun ξ : ℝ => ξ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hxl : Tendsto (fun ξ : ℝ => ξ * Real.log ξ) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hxl2 : Tendsto (fun ξ : ℝ => ξ * Real.log ξ ^ 2) (𝓝[>] 0) (𝓝 0) :=
    tendsto_mul_log_sq_zero
  obtain ⟨ha, hal⟩ := i13_tendsto_of_abs_le fun ξ hξ => abs_i13Ra_le hξ
  obtain ⟨hb, hbl⟩ := i13_tendsto_of_abs_le fun ξ hξ => abs_i13Rb_le hξ
  obtain ⟨hd, -⟩ := i13_tendsto_of_abs_le fun ξ hξ => abs_i13Rd_le hξ
  have hs : ∀ᶠ ξ in 𝓝[>] (0 : ℝ), |ξ| ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ξ hξ
    rw [abs_of_pos hξ.1]; exact hξ.2.le
  have hLP : Tendsto (fun ξ : ℝ => Real.log ξ * Li₂ ξ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_Li_comp (k := 2) le_rfl hx hs
  have hP3 : Tendsto (fun ξ : ℝ => Li₃ ξ) (𝓝[>] 0) (𝓝 0) := by
    have := hasDerivAt_Li₃_zero.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hD3 : Tendsto (fun ξ : ℝ => Li₃ (-ξ)) (𝓝[>] 0) (𝓝 0) := by
    have hn : Tendsto (fun ξ : ℝ => -ξ) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_neg (0 : ℝ))
    have := (hasDerivAt_Li₃_zero.continuousAt.tendsto.comp hn).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [Function.comp_def] using this
  have hv := hx.prodMk_nhds (ha.prodMk_nhds (hb.prodMk_nhds hd))
  have hQ : ∀ Q : ℝ → ℝ → ℝ → ℝ → ℝ, Continuous (fun p : ℝ × ℝ × ℝ × ℝ =>
      Q p.1 p.2.1 p.2.2.1 p.2.2.2) → Tendsto (fun ξ => Q ξ (i13Ra ξ) (i13Rb ξ) (i13Rd ξ))
      (𝓝[>] 0) (𝓝 (Q 0 0 0 0)) := fun Q hc => (hc.tendsto _).comp hv
  have hQ1 := hQ i13LimQ1 (by unfold i13LimQ1; fun_prop)
  have hQ2 := hQ i13LimQ2 (by unfold i13LimQ2; fun_prop)
  have hQ3 := hQ i13LimQ3 (by unfold i13LimQ3; fun_prop)
  have H := ((((((((((hx.mul hQ1).add (hxl.mul hQ2)).add (hxl2.mul hQ3)).add
    (ha.const_mul 11)).add (hal.const_mul 6)).sub (hbl.const_mul 2)).sub (hd.const_mul 2)).add
    (hLP.const_mul 8)).sub (hP3.const_mul 8)).sub (hD3.const_mul 16)).const_add (-8 - π ^ 2 / 3)
  have H' : Tendsto i13Dif2 (𝓝[>] 0) _ := H.congr fun ξ => by unfold i13Dif2; ring
  convert H' using 2
  ring

theorem tendsto_i13F2_sub_prim2 :
    Tendsto (fun t => i13F2 t - i13Prim2 t) atTop (𝓝 (-8 - π ^ 2 / 3)) :=
  (tendsto_i13Dif2.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i13F2_sub_prim2 (by linarith)).symm⟩)

end QED.ThreeLoopD
