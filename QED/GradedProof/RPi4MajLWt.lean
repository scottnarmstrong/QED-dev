/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LightInt
public import QED.Integration.SymanzikIntegrabilityQuadratic

/-!
# (R-Π₄) step L10, two loops: the weights of the top monomial along the ray

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2, light
photon pairs along the ray). By AM–GM on two flows
(`QED.GradedProof.RPi4.maj_abs_flow_mul_le`) the top monomial of a piece along the ray carries
the weight `U⁻² (zᵢ zⱼ)^{-1/2}` instead of `1/B`. This file proves the two integrability
statements it needs.

* `maj_integrableOn_weight`: `U⁻² (zᵢ zⱼ)^{-1/2}` is integrable on the simplex if every line `l`
  has three lines `t ∉ {i, j}` with `det(α_l, α_t) ≠ 0` (the no-subdivergence criterion with the
  lines `i`, `j` removed): at a point with `z_l ≥ 1/N`, `U⁻² ≤ C ∏_{t ∈ T} z_t^{-2/3}` and
  `(zᵢ zⱼ)^{-1/2} ≤ (zᵢ zⱼ)^{-2/3}`;
* `maj_corner_weight_le`, `maj_integrableOn_headProd`: near the soft-photon corner, with
  `y` the sum of the six fermion parameters of an eight-line piece,
  `y^{-9/2} (xᵢ xⱼ)^{-1/2} ≤ ∏_{k < 6} x_k^{-19/20}`, which is integrable.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- `(√(x y))⁻¹ ≤ x^{-2/3} y^{-2/3}` for `0 < x, y ≤ 1`. -/
theorem maj_inv_sqrt_mul_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    (Real.sqrt (x * y))⁻¹ ≤ x ^ (-(2 / 3 : ℝ)) * y ^ (-(2 / 3 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hx.le hy.le, mul_inv, ← Real.rpow_neg hx.le,
    ← Real.rpow_neg hy.le]
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num))
    (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by norm_num)) (by positivity) (by positivity)

/-- **The bulk weight of the top monomial**: `U⁻² (zᵢ zⱼ)^{-1/2}` is integrable on the simplex
if every line has three lines outside `{i, j}` not parallel to it. -/
theorem maj_integrableOn_weight {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) {i j : Fin (m + 1)}
    (hij : i ≠ j)
    (hT : ∀ l, ∃ T : Finset (Fin (m + 1)), T.card = 3 ∧ i ∉ T ∧ j ∉ T ∧
      ∀ t ∈ T, pairDet α l t ≠ 0) :
    IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹ *
      (Real.sqrt (simplexPoint x i * simplexPoint x j))⁻¹) (simplexSet m) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
    · exact h
  choose T hTcard hTi hTj hTd using hT
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_pairDet_sq α
  set κ : ℝ := 3 * c / (2 * ((m : ℝ) + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hint : IntegrableOn (fun x => (κ ^ 2)⁻¹ * ∑ l, ∏ t ∈ insert i (insert j (T l)),
      simplexPoint x t ^ (-(2 / 3 : ℝ))) (simplexSet m) :=
    (integrable_finsetSum _ fun l _ =>
      integrableOn_prod_simplexPoint_rpow _ (by norm_num) (by norm_num)).const_mul _
  have hmeas : Measurable fun x : Fin m → ℝ => (symanzikU α (simplexPoint x) ^ 2)⁻¹ *
      (Real.sqrt (simplexPoint x i * simplexPoint x j))⁻¹ :=
    ((continuous_symanzikU_comp_simplexPoint α).pow 2).measurable.inv.mul
      ((((continuous_apply i).comp continuous_simplexPoint').mul
        ((continuous_apply j).comp continuous_simplexPoint')).measurable.sqrt.inv)
  refine hint.mono' hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (QED.Integration.Feynman.measurableSet_simplexSet m)]
  filter_upwards [ae_simplexPoint_ne_zero hm] with x hx0 hxS
  obtain ⟨hz0, hz1⟩ := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  set z := simplexPoint x with hzdef
  have hzpos : ∀ i, 0 < z i := fun i => lt_of_le_of_ne (hz0 i) (hx0 i).symm
  have hzle : ∀ i, z i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun j _ => hz0 j) (Finset.mem_univ i)).trans hz1.le
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
    (f := fun _ => ((m : ℝ) + 1)⁻¹) (g := z) (by
      rw [hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [mul_inv_cancel₀ hm1.ne'])
  set P : ℝ := ∏ t ∈ T l, z t ^ (1 / ((2 : ℕ) + 1 : ℝ)) with hP
  have hP0 : 0 < P := Finset.prod_pos fun t _ => Real.rpow_pos_of_pos (hzpos t) _
  have hrow := mul_sum_pairDet_sq_le_two_mul_symanzikU α hz0 l
  have hsub : ∑ t ∈ T l, z t * c ≤ ∑ t, z t * pairDet α l t ^ 2 :=
    (Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hc l t (hTd l t ht)) (hz0 t)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (T l))
        fun t _ _ => mul_nonneg (hz0 t) (sq_nonneg _))
  have hamgm := card_mul_prod_rpow_le_sum (T l) (by norm_num : 0 < 3) (hTcard l) hz0
  have hP' : P = ∏ t ∈ T l, z t ^ (1 / ((3 : ℕ) : ℝ)) := by
    rw [hP]; norm_num
  have hUl : κ * P ≤ symanzikU α z := by
    rw [← Finset.sum_mul] at hsub
    rw [← hP'] at hamgm
    push_cast at hamgm
    have h2 : c * (3 * P) ≤ ∑ t, z t * pairDet α l t ^ 2 := by
      have := mul_le_mul_of_nonneg_left hamgm hc0.le
      nlinarith
    have h1 : ((m : ℝ) + 1)⁻¹ * (c * (3 * P)) ≤ z l * ∑ t, z t * pairDet α l t ^ 2 :=
      mul_le_mul hl h2 (by positivity) (hz0 l)
    have e : κ * P = ((m : ℝ) + 1)⁻¹ * (c * (3 * P)) / 2 := by
      rw [hκ]; field_simp
    rw [e]
    linarith
  have hκP : 0 < κ * P := mul_pos hκ0 hP0
  have hUi : (symanzikU α z ^ 2)⁻¹ ≤ (κ ^ 2)⁻¹ * ∏ t ∈ T l, z t ^ (-(2 / 3 : ℝ)) := by
    have e := prod_rpow_neg_div (T l) hz0 2
    have e2 : -(((2 : ℕ) : ℝ) / ((2 : ℕ) + 1 : ℝ)) = -(2 / 3 : ℝ) := by norm_num
    rw [e2] at e
    rw [e, ← hP, ← mul_inv, ← mul_pow]
    exact inv_anti₀ (pow_pos hκP 2) (pow_le_pow_left₀ hκP.le hUl 2)
  have hsq := maj_inv_sqrt_mul_le (hzpos i) (hzpos j) (hzle i) (hzle j)
  have hjT : i ∉ insert j (T l) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hij, hTi l⟩
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity))
    (inv_nonneg.mpr (Real.sqrt_nonneg _)))]
  calc (symanzikU α z ^ 2)⁻¹ * (Real.sqrt (z i * z j))⁻¹
      ≤ ((κ ^ 2)⁻¹ * ∏ t ∈ T l, z t ^ (-(2 / 3 : ℝ))) *
          (z i ^ (-(2 / 3 : ℝ)) * z j ^ (-(2 / 3 : ℝ))) :=
        mul_le_mul hUi hsq (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (mul_nonneg (by positivity) (Finset.prod_nonneg fun t _ => Real.rpow_nonneg (hz0 t) _))
    _ = (κ ^ 2)⁻¹ * ∏ t ∈ insert i (insert j (T l)), z t ^ (-(2 / 3 : ℝ)) := by
        rw [Finset.prod_insert hjT, Finset.prod_insert (hTj l)]
        ring
    _ ≤ (κ ^ 2)⁻¹ * ∑ l, ∏ t ∈ insert i (insert j (T l)), z t ^ (-(2 / 3 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.single_le_sum (f := fun l => ∏ t ∈ insert i (insert j (T l)),
          z t ^ (-(2 / 3 : ℝ))) (fun l _ => Finset.prod_nonneg fun t _ =>
            Real.rpow_nonneg (hz0 t) _) (Finset.mem_univ l)

/-! ### The corner weight -/

/-- The product majorant `∏_{k < 6} x_k^{-19/20}` is integrable on the simplex. -/
theorem maj_integrableOn_headProd :
    IntegrableOn (headProd (m := 7) 6 (19 / 20)) (simplexSet 7) := by
  have hsub : simplexSet 7 ⊆ Set.univ.pi fun _ => Icc (0 : ℝ) 1 := fun x hx' i _ => by
    have hx := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le (by norm_num) x).mp hx'
    refine ⟨hx.1 i, ?_⟩
    calc x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
      _ ≤ 1 := hx.2
  exact (integrableOn_headProd (m := 7) 6 (by norm_num)).mono_set hsub

/-- **The corner weight**: `y^{-9/2} (xᵢ xⱼ)^{-1/2} ≤ ∏_{k < 6} x_k^{-19/20}` for the sum `y`
of the first six coordinates, `i ≠ j` among them. -/
theorem maj_corner_weight_le {x : Fin 7 → ℝ} (hx : ∀ k, 0 < x k) (hx1 : ∑ k, x k ≤ 1)
    {i j : Fin 7} (hi : (i : ℕ) < 6) (hj : (j : ℕ) < 6) (hij : i ≠ j) :
    1 / (headSum 6 x ^ 4 * Real.sqrt (headSum 6 x) * Real.sqrt (x i * x j)) ≤
      headProd 6 (19 / 20) x := by
  have hx0 : ∀ k, 0 ≤ x k := fun k => (hx k).le
  set y := headSum 6 x with hy
  have hyi : x i ≤ y := le_headSum hx0 hi
  have hyj : x j ≤ y := le_headSum hx0 hj
  have hy0 : 0 < y := (hx i).trans_le hyi
  have hy1 : y ≤ 1 :=
    (Finset.sum_le_sum fun k _ => by split_ifs <;> simp [hx0 k]).trans hx1
  set S := Finset.univ.filter fun k : Fin 7 => (k : ℕ) < 6 with hS
  have hiS : i ∈ S := by simp [hS, hi]
  have hjS : j ∈ S.erase i := by simp [hS, hj, Ne.symm hij]
  have hcard : ((S.erase i).erase j).card = 4 := by
    rw [Finset.card_erase_of_mem hjS, Finset.card_erase_of_mem hiS, hS, Fin.card_filter_val_lt]
    rfl
  have e : headProd 6 (19 / 20) x = x i ^ (-(19 / 20 : ℝ)) * (x j ^ (-(19 / 20 : ℝ)) *
      ∏ k ∈ (S.erase i).erase j, x k ^ (-(19 / 20 : ℝ))) := by
    rw [Finset.mul_prod_erase (S.erase i) (fun k => x k ^ (-(19 / 20 : ℝ))) hjS,
      Finset.mul_prod_erase S (fun k => x k ^ (-(19 / 20 : ℝ))) hiS, headProd, Finset.prod_ite,
      Finset.prod_const_one, mul_one]
  -- the rest: each factor is at least `y^{-19/20}`
  have hrest : (y ^ (-(19 / 20 : ℝ))) ^ 4 ≤ ∏ k ∈ (S.erase i).erase j, x k ^ (-(19 / 20 : ℝ)) := by
    rw [← hcard, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k hk => ?_
    have hk6 : (k : ℕ) < 6 := by
      simp only [hS, Finset.mem_erase, Finset.mem_filter] at hk
      exact hk.2.2.2
    exact Real.rpow_le_rpow_of_nonpos (hx k) (le_headSum hx0 hk6) (by norm_num)
  -- the factors `i`, `j`
  have hfac : ∀ k, x k ≤ y → (x k ^ (-(1 / 2 : ℝ))) * y ^ (-(9 / 20 : ℝ)) ≤
      x k ^ (-(19 / 20 : ℝ)) := fun k hk => by
    have h1 : y ^ (-(9 / 20 : ℝ)) ≤ x k ^ (-(9 / 20 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (hx k) hk (by norm_num)
    calc x k ^ (-(1 / 2 : ℝ)) * y ^ (-(9 / 20 : ℝ))
        ≤ x k ^ (-(1 / 2 : ℝ)) * x k ^ (-(9 / 20 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (hx0 k) _)
      _ = x k ^ (-(19 / 20 : ℝ)) := by
          rw [← Real.rpow_add (hx k)]; norm_num
  -- the left side in powers
  have hL : 1 / (y ^ 4 * Real.sqrt y * Real.sqrt (x i * x j)) =
      x i ^ (-(1 / 2 : ℝ)) * x j ^ (-(1 / 2 : ℝ)) * y ^ (-(9 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.mul_rpow (hx0 i) (hx0 j),
      Real.rpow_neg (hx0 i), Real.rpow_neg (hx0 j), Real.rpow_neg hy0.le,
      show (9 / 2 : ℝ) = (4 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_natCast]
    field_simp
  have hy47 : y ^ (-(9 / 2 : ℝ)) ≤ (y ^ (-(9 / 20 : ℝ))) ^ 2 * (y ^ (-(19 / 20 : ℝ))) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le,
      ← Real.rpow_mul hy0.le, ← Real.rpow_add hy0]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by norm_num)
  rw [hL, e]
  have hi' := hfac i hyi
  have hj' := hfac j hyj
  have hp : 0 ≤ y ^ (-(9 / 20 : ℝ)) := Real.rpow_nonneg hy0.le _
  have hq : 0 ≤ y ^ (-(19 / 20 : ℝ)) := Real.rpow_nonneg hy0.le _
  have hxi := Real.rpow_nonneg (hx0 i) (-(1 / 2 : ℝ))
  have hxj := Real.rpow_nonneg (hx0 j) (-(1 / 2 : ℝ))
  calc x i ^ (-(1 / 2 : ℝ)) * x j ^ (-(1 / 2 : ℝ)) * y ^ (-(9 / 2 : ℝ))
      ≤ x i ^ (-(1 / 2 : ℝ)) * x j ^ (-(1 / 2 : ℝ)) *
          ((y ^ (-(9 / 20 : ℝ))) ^ 2 * (y ^ (-(19 / 20 : ℝ))) ^ 4) :=
        mul_le_mul_of_nonneg_left hy47 (mul_nonneg hxi hxj)
    _ = (x i ^ (-(1 / 2 : ℝ)) * y ^ (-(9 / 20 : ℝ))) *
          ((x j ^ (-(1 / 2 : ℝ)) * y ^ (-(9 / 20 : ℝ))) * (y ^ (-(19 / 20 : ℝ))) ^ 4) := by ring
    _ ≤ x i ^ (-(19 / 20 : ℝ)) * (x j ^ (-(19 / 20 : ℝ)) *
          ∏ k ∈ (S.erase i).erase j, x k ^ (-(19 / 20 : ℝ))) :=
        mul_le_mul hi' (mul_le_mul hj' hrest (pow_nonneg hq 4) (Real.rpow_nonneg (hx0 j) _))
          (mul_nonneg (mul_nonneg hxj hp) (pow_nonneg hq 4)) (Real.rpow_nonneg (hx0 i) _)

end QED.GradedProof.RPi4

end
