/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajLGen
public import QED.GradedProof.RPi4MajFlow

/-!
# (R-Π₄) step L10, two loops: the top monomial of an eight-line piece along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.IR). The top
monomial `s² T₁(Q₂)/V⁴` of an eight-line piece along the ray (`V = V₀ + s B`) is at most
`s (G + H/b)` with integrable `G`, `H` as soon as `‖T₁(Q₂)‖ · 2 √(zᵢ zⱼ) ≤ K U⁻² B` for two
fermion lines `i ≠ j` (the AM–GM bound of two flows, `QED.GradedProof.RPi4.maj_abs_flow_mul_le`):
by `QED.GradedProof.RPi4.maj_ray_four_le` it is at most `s K U⁻² (zᵢ zⱼ)^{-1/2} / (2 V₀³)`;
where the fermion parameters sum to `y ≥ 1/2`, `V₀ ≥ c₀/2` and the weight is integrable
(`QED.GradedProof.RPi4.maj_integrableOn_weight`); where `y < 1/2`, `U ≥ y/2`, `V₀ ≥ c₀ y` and
`V₀ ≥ b²/8` give `y^{-9/2} (zᵢ zⱼ)^{-1/2} / b`, below the integrable product
`∏_{k < 6} x_k^{-19/20}` (`QED.GradedProof.RPi4.maj_corner_weight_le`).

* **`maj_top_of_flow`**: the hypothesis `hTop` of `QED.GradedProof.RPi4.maj_pvOf_lray` for
  `m = 7`.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- **The top monomial of an eight-line piece** from the AM–GM bound of two fermion flows. -/
theorem maj_top_of_flow (α : Fin 8 → Fin 2 → ℝ) (cs : Fin 8 → ℝ) (Ms : ℝ → ℝ → Fin 8 → ℝ)
    (Q₄ : LoopQuartic) {i j : Fin 7} (hi : (i : ℕ) < 6) (hj : (j : ℕ) < 6) (hij : i ≠ j)
    (hW : IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹ *
      (Real.sqrt (simplexPoint x i.castSucc * simplexPoint x j.castSucc))⁻¹) (simplexSet 7))
    (hU : ∀ x ∈ simplexSet 7, (1 - headSum 6 x) * headSum 6 x ≤ symanzikU α (simplexPoint x))
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hV : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ simplexSet 7,
      c₀ * headSum 6 x + (1 - headSum 6 x) * a ^ 2 ≤ ∑ l, simplexPoint x l * Ms a b l ^ 2)
    {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ x ∈ simplexSet 7, 0 < symanzikU α (simplexPoint x) →
      ‖coeffOne Q₄ α (fun l => cs l • majRayVec 1) x‖ *
          (2 * Real.sqrt (simplexPoint x i.castSucc * simplexPoint x j.castSucc)) ≤
        K * (symanzikU α (simplexPoint x) ^ 2)⁻¹ * remainder α (simplexPoint x) cs) :
    ∃ G H : (Fin 7 → ℝ) → ℝ, IntegrableOn G (simplexSet 7) ∧ IntegrableOn H (simplexSet 7) ∧
      ∀ᵐ x ∂(volume.restrict (simplexSet 7)),
        ∀ s : ℝ, 1 ≤ s → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
          ‖coeffOne Q₄ α (fun l => cs l • majRayVec 1) x‖ * s ^ 2 /
            (∑ l, simplexPoint x l * Ms a b l ^ 2 +
              s * remainder α (simplexPoint x) cs) ^ (7 - 3) ≤ s * (G x + H x / b) := by
  set w : (Fin 7 → ℝ) → ℝ := fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹ *
    (Real.sqrt (simplexPoint x i.castSucc * simplexPoint x j.castSucc))⁻¹ with hw
  set κ : ℝ := 2 * K * Real.sqrt 8 / (c₀ ^ 2 * Real.sqrt c₀) with hκ
  refine ⟨fun x => K / 2 * (2 / c₀) ^ 3 * w x, fun x => κ * headProd 6 (19 / 20) x,
    hW.const_mul _, maj_integrableOn_headProd.const_mul _, ?_⟩
  have hae0 : ∀ᵐ x ∂(volume.restrict (simplexSet 7)), ∀ k : Fin 7, x k ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_all_iff]
    exact fun k => Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) k 0
  filter_upwards [hae0, ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet 7)]
    with x hx0 hxS
  intro s hs a b ha hab hb2
  have hb : 0 < b := ha.trans_le hab
  have hs0 : 0 ≤ s := by linarith
  have hxle := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le (by norm_num) x).mp hxS
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  have hxpos : ∀ k, 0 < x k := fun k => lt_of_le_of_ne (hxle.1 k) (hx0 k).symm
  have hy0 : 0 < headSum 6 x := (hxpos i).trans_le (le_headSum hxle.1 hi)
  set y := headSum 6 x with hy_def
  have hy1 : y ≤ 1 := headSum_le_one hxle.1 hxle.2
  have hUy := hU x hxS
  have hy7 : y < 1 := by
    have e : y = x 0 + x 1 + x 2 + x 3 + x 4 + x 5 := by
      simp [hy_def, headSum, Fin.sum_univ_seven]
    have e2 := hxle.2
    rw [Fin.sum_univ_seven] at e2
    have := hxpos 6
    linarith
  have hU0 : 0 < symanzikU α (simplexPoint x) :=
    lt_of_lt_of_le (mul_pos (by linarith) hy0) hUy
  set U := symanzikU α (simplexPoint x) with hU_def
  set B := remainder α (simplexPoint x) cs with hB_def
  have hB0 : 0 ≤ B := remainder_nonneg α hz.1 hU0.ne' cs
  set P := ‖coeffOne Q₄ α (fun l => cs l • majRayVec 1) x‖ with hP_def
  have hsq : 0 < Real.sqrt (x i * x j) := Real.sqrt_pos.mpr (mul_pos (hxpos i) (hxpos j))
  set W' := K * (U ^ 2)⁻¹ / (2 * Real.sqrt (x i * x j)) with hW'
  have hW'0 : 0 ≤ W' := by positivity
  have hPB : |P| ≤ B * W' := by
    rw [abs_of_nonneg (norm_nonneg _), hW', mul_div_assoc', le_div_iff₀ (by positivity)]
    have := hF x hxS hU0
    rw [simplexPoint_castSucc, simplexPoint_castSucc] at this
    linarith
  set V₀ := ∑ l, simplexPoint x l * Ms a b l ^ 2 with hV₀
  have hVx : c₀ * y + (1 - y) * a ^ 2 ≤ V₀ := hV a b ha hab x hxS
  have ha2 : 0 ≤ (1 - y) * a ^ 2 := mul_nonneg (by linarith) (sq_nonneg a)
  have hV0 : 0 < V₀ := by nlinarith
  have hfour := maj_ray_four_le (n := 4) hV0 hB0 hs0 (by norm_num) hW'0 hPB
  rw [abs_of_nonneg (norm_nonneg _)] at hfour
  have hG0 : 0 ≤ K / 2 * (2 / c₀) ^ 3 * w x := by simp only [hw]; positivity
  have hH0 : 0 ≤ κ * headProd 6 (19 / 20) x / b := by
    refine div_nonneg (mul_nonneg (by positivity) ?_) hb.le
    exact Finset.prod_nonneg fun k _ => by split_ifs <;> [exact Real.rpow_nonneg (hxle.1 k) _;
      exact zero_le_one]
  suffices h : W' / V₀ ^ 3 ≤ K / 2 * (2 / c₀) ^ 3 * w x + κ * headProd 6 (19 / 20) x / b by
    calc P * s ^ 2 / (V₀ + s * B) ^ (7 - 3) = s ^ 2 * P / (V₀ + s * B) ^ 4 := by ring
      _ ≤ s * W' / V₀ ^ (4 - 1) := hfour
      _ = s * (W' / V₀ ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hs0
  by_cases hyc : 1 / 2 ≤ y
  · have hVc : c₀ / 2 ≤ V₀ := by nlinarith
    have hc2 : 0 < c₀ / 2 := by positivity
    refine le_trans ?_ (le_add_of_nonneg_right hH0)
    have h1 : W' / V₀ ^ 3 ≤ W' / (c₀ / 2) ^ 3 :=
      div_le_div_of_nonneg_left hW'0 (by positivity) (pow_le_pow_left₀ hc2.le hVc 3)
    refine h1.trans (le_of_eq ?_)
    simp only [hW', hw, simplexPoint_castSucc, ← hU_def]
    field_simp
  · replace hyc := not_le.mp hyc
    refine le_trans ?_ (le_add_of_nonneg_left hG0)
    have hUy2 : y / 2 ≤ U := by nlinarith
    have hUi : (U ^ 2)⁻¹ ≤ 4 / y ^ 2 := by
      rw [show 4 / y ^ 2 = ((y / 2) ^ 2)⁻¹ by field_simp; ring]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hUy2 2)
    have hcy : c₀ * y ≤ V₀ := by linarith
    have hb8 : c₀ * y * (b ^ 2 / 8) ≤ V₀ ^ 2 := by
      have hb8' : b ^ 2 / 8 ≤ V₀ := by nlinarith
      nlinarith
    have hsc := Real.sqrt_pos.mpr hc₀
    have hsy := Real.sqrt_pos.mpr hy0
    have hs8 : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
    have hX : b * Real.sqrt c₀ * Real.sqrt y / Real.sqrt 8 ≤ V₀ := by
      have h := Real.sqrt_le_sqrt hb8
      rw [Real.sqrt_sq hV0.le] at h
      refine le_trans (le_of_eq ?_) h
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc₀.le, Real.sqrt_div' _ (by norm_num),
        Real.sqrt_sq hb.le]
      ring
    have hV3 : (c₀ * y) ^ 2 * (b * Real.sqrt c₀ * Real.sqrt y / Real.sqrt 8) ≤ V₀ ^ 3 := by
      rw [pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hcy 2) hX (by positivity)
        (pow_pos hV0 2).le
    have hnum : W' ≤ K * (4 / y ^ 2) / (2 * Real.sqrt (x i * x j)) := by
      simp only [hW']
      gcongr
    have hcw := maj_corner_weight_le hxpos hxle.2 hi hj hij
    calc W' / V₀ ^ 3 ≤ K * (4 / y ^ 2) / (2 * Real.sqrt (x i * x j)) /
          ((c₀ * y) ^ 2 * (b * Real.sqrt c₀ * Real.sqrt y / Real.sqrt 8)) :=
          div_le_div₀ (by positivity) hnum (by positivity) hV3
      _ = κ * (1 / (y ^ 4 * Real.sqrt y * Real.sqrt (x i * x j))) / b := by
          simp only [hκ]
          field_simp
          ring
      _ ≤ κ * headProd 6 (19 / 20) x / b := by
          gcongr

end QED.GradedProof.RPi4

end
