/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrabilityQuadratic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# A numerator-aware integrability criterion on the simplex

The representation with numerators of degree at most four
(`QED/Integration/TwoLoopNumeratorQuarticFull.lean`) assumes that `tr² A · U⁻⁴` is integrable on
the simplex. That weight comes from bounding the numerator by `(1 + |ℓ|²)²`, as if all four
powers of the loop momenta could fall in every one-loop subgraph. Under the criterion of order
five (`NoSubdivergenceQuartic`) it holds only for `X` with doubled photons. This file gives a
criterion that counts, for each one-loop subgraph, only the numerator factors carried by its
lines.

For `N = m + 1` lines with loop coefficients `αᵢ ∈ ℝ²`, `A(z) = ∑ᵢ zᵢ αᵢ αᵢᵀ`, `U = det A` and
`dᵢⱼ = det(αᵢ, αⱼ)`, let `Q_e = ∑ⱼ zⱼ d_ej²` (`lineQuad`), so that `Q_e/U = α_eᵀ A⁻¹ α_e`
(`lineQuad_div_symanzikU`). For a numerator `∏_{e ∈ E} k_e^{μ_e}`, one component of the momentum
`k_e = α_e·ℓ + p_e` of each line `e ∈ E`, the factor `k_e` grows like `(α_eᵀ A⁻¹ α_e)^{1/2} |u|`
in the variables `u` that diagonalize the completed square, so after the energy and spatial
integrals the absolute integrand is bounded by a multiple of
`U⁻² ∏_{e ∈ E} (1 + Q_e/U)^{1/2}` (`refinedWeight 2 E`). That bound is the motivation and is not
formalized here.

**The criterion** (`NoSubdivergenceRefined k E α`): for every line `i`,
`2k + #{e ∈ E : dᵢₑ ≠ 0} < 2 #{j : dᵢⱼ ≠ 0}`. For the direction class `D` of `i` and its
complement `S` (the one-loop subgraph whose loop momentum avoids `D`), `|E ∩ S|` is the degree of
the numerator in that loop momentum, and for `k = 2` the condition `2|S| > 4 + |E ∩ S|` is the
ultraviolet power counting of the subgraph. With `E = ∅` it is the criterion of order `k + 1`
(`noSubdivergenceRefined_empty_iff`).

**The theorem** (`integrableOn_refinedWeight_of_criterion`): under the criterion,
`U⁻ᵏ ∏_{e ∈ E} (1 + Q_e/U)^{1/2}` is integrable on the simplex. The proof refines that of
`integrableOn_inv_pow_symanzikU_of_criterion`: at a point with `z_l ≥ 1/N`, with `S` the lines
not parallel to `l` and `σ = ∑_{j ∈ S} zⱼ`, `U ≥ κσ`; for `e ∥ l` the lines with `d_ej ≠ 0` lie
in `S`, so `Q_e ≤ Cσ` and `Q_e/U` is bounded; otherwise `Q_e/U ≤ C/(κσ)`. The weight is then at
most a constant times `σ^{-(k + |E ∩ S|/2)}`, and the arithmetic–geometric mean inequality
bounds this by `∏_{j ∈ S} zⱼ^{-s}` with `s = (k + |E ∩ S|/2)/|S| < 1`.

## Numerical check

Not part of the formal statement. On the loop matrices of the nine classes, with
`E` the four fermion lines (`QED/Integration/SymanzikIntegrabilityRefinedClasses.lean`), the
criterion agrees with the Newton-polytope test of `U⁻² ∏_{e ∈ E} (1 + Q_e/U)^{1/2}` over integer
weight vectors (entries up to `4`, up to `3` for ten lines) on all twenty-one forms. Monte Carlo
truncated means `E[min(f, T)]` (`4·10⁶` points) level off for the forms satisfying it (`L`, `X`,
`C±`, `S±` with doubled photons, the doubled-bubble `VP`; slowly for `X` with single lines, whose
margin is smallest) and grow with `T` for the others.

## Main statements

* `lineQuad`, `lineQuad_eq_adjugate`, `lineQuad_div_symanzikU`: the line weights.
* `NoSubdivergenceRefined`, `refinedWeight`: the criterion and the weight.
* `integrableOn_refinedWeight_of_criterion`: integrability under the criterion.
-/

@[expose] public section

open MeasureTheory Set Matrix Finset
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-! ### The line weights -/

/-- `Q_e(z) = ∑ⱼ zⱼ det(α_e, αⱼ)²`, so that `Q_e / U = α_eᵀ A⁻¹ α_e` (`lineQuad_eq_adjugate`). -/
def lineQuad (α : Fin (m + 1) → Fin 2 → ℝ) (e : Fin (m + 1)) (z : Fin (m + 1) → ℝ) : ℝ :=
  ∑ j, z j * pairDet α e j ^ 2

theorem lineQuad_eq_adjugate (α : Fin (m + 1) → Fin 2 → ℝ) (e : Fin (m + 1))
    (z : Fin (m + 1) → ℝ) :
    lineQuad α e z = α e ⬝ᵥ (adjugate (symanzikMatrix α z) *ᵥ α e) := by
  simp only [lineQuad, pairDet, adjugate_fin_two, dotProduct, mulVec, Fin.sum_univ_two,
    of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    symanzikMatrix]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Q_e / U = α_eᵀ A⁻¹ α_e`. -/
theorem lineQuad_div_symanzikU (α : Fin (m + 1) → Fin 2 → ℝ) (e : Fin (m + 1))
    (z : Fin (m + 1) → ℝ) :
    lineQuad α e z / symanzikU α z = α e ⬝ᵥ ((symanzikMatrix α z)⁻¹ *ᵥ α e) := by
  rw [lineQuad_eq_adjugate, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, div_eq_inv_mul]
  rfl

theorem lineQuad_nonneg (α : Fin (m + 1) → Fin 2 → ℝ) (e : Fin (m + 1)) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) : 0 ≤ lineQuad α e z :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (sq_nonneg _)

/-! ### The criterion -/

/-- **The numerator-aware criterion** of order `k` with numerator lines `E`: for every line `i`,
`2k + #{e ∈ E : det(αᵢ, α_e) ≠ 0} < 2 #{j : det(αᵢ, αⱼ) ≠ 0}`. For a direction class `D` (the
lines parallel to `αᵢ`) and its complement `S`, the one-loop subgraph whose loop momentum avoids
`D`: `2|S| > 2k + |E ∩ S|`, with `|E ∩ S|` the degree of the numerator in that loop momentum
when each line of `E` carries one factor of its momentum. -/
def NoSubdivergenceRefined (k : ℕ) (E : Finset (Fin (m + 1))) (α : Fin (m + 1) → Fin 2 → ℝ) :
    Prop :=
  ∀ i, 2 * k + (E.filter fun e => pairDet α i e ≠ 0).card <
    2 * (Finset.univ.filter fun j => pairDet α i j ≠ 0).card

theorem NoSubdivergenceRefined.noSubdivergenceOfOrder {k : ℕ} {E : Finset (Fin (m + 1))}
    {α : Fin (m + 1) → Fin 2 → ℝ} (h : NoSubdivergenceRefined k E α) :
    NoSubdivergenceOfOrder (k + 1) α := fun i => by
  have := h i
  omega

/-- With no numerator lines the criterion is that of order `k + 1`. -/
theorem noSubdivergenceRefined_empty_iff (k : ℕ) (α : Fin (m + 1) → Fin 2 → ℝ) :
    NoSubdivergenceRefined k ∅ α ↔ NoSubdivergenceOfOrder (k + 1) α := by
  refine ⟨NoSubdivergenceRefined.noSubdivergenceOfOrder, fun h i => ?_⟩
  have := h i
  simp only [Finset.filter_empty, Finset.card_empty, add_zero]
  omega

/-- The weight `U⁻ᵏ ∏_{e ∈ E} (1 + Q_e/U)^{1/2}`. -/
noncomputable def refinedWeight (k : ℕ) (E : Finset (Fin (m + 1)))
    (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  (symanzikU α z ^ k)⁻¹ * ∏ e ∈ E, Real.sqrt (1 + lineQuad α e z / symanzikU α z)

/-! ### Parallel lines -/

/-- If `α_e ∥ α_l ≠ 0`, the lines not parallel to `α_e` are not parallel to `α_l`. -/
theorem pairDet_ne_zero_of_pairDet_eq_zero (α : Fin (m + 1) → Fin 2 → ℝ) {l e j j₀ : Fin (m + 1)}
    (hj₀ : pairDet α l j₀ ≠ 0) (hle : pairDet α l e = 0) (hej : pairDet α e j ≠ 0) :
    pairDet α l j ≠ 0 := by
  intro hlj
  have h0 : pairDet α e j * α l 0 = 0 := by
    have : pairDet α e j * α l 0 = α e 0 * pairDet α l j - α j 0 * pairDet α l e := by
      simp only [pairDet]; ring
    rw [this, hlj, hle]; ring
  have h1 : pairDet α e j * α l 1 = 0 := by
    have : pairDet α e j * α l 1 = α e 1 * pairDet α l j - α j 1 * pairDet α l e := by
      simp only [pairDet]; ring
    rw [this, hlj, hle]; ring
  have hl0 : α l 0 = 0 := (mul_eq_zero.mp h0).resolve_left hej
  have hl1 : α l 1 = 0 := (mul_eq_zero.mp h1).resolve_left hej
  exact hj₀ (by simp only [pairDet, hl0, hl1]; ring)

/-! ### Real-power algebra -/

theorem inv_rpow_le_of_amgm {n : ℕ} (hn : 0 < n) {T : Finset (Fin (m + 1))} (hT : T.card = n)
    {z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 < z i) {p : ℝ} (hp : 0 ≤ p) :
    ((∑ j ∈ T, z j) ^ p)⁻¹ ≤ ((n : ℝ) ^ p)⁻¹ * ∏ j ∈ T, z j ^ (-(p / n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hamgm := card_mul_prod_rpow_le_sum T hn hT fun i => (hz i).le
  set P := ∏ i ∈ T, z i ^ (1 / (n : ℝ)) with hP
  have hP0 : 0 < P := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hz i) _
  have hprod : ∏ j ∈ T, z j ^ (-(p / n)) = (P ^ p)⁻¹ := by
    rw [hP, ← Real.finsetProd_rpow _ _ (fun i _ => (Real.rpow_pos_of_pos (hz i) _).le),
      ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_mul (hz i).le, Real.rpow_neg (hz i).le]
    congr 2
    field_simp
  rw [hprod, ← mul_inv, ← Real.mul_rpow hn'.le hP0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_le_rpow (by positivity) hamgm hp)

/-! ### Integrability -/

/-- **The numerator-aware integrability criterion.** Under `NoSubdivergenceRefined k E α`, the
weight `U⁻ᵏ ∏_{e ∈ E} (1 + Q_e/U)^{1/2}` is integrable on the simplex. Proof: at a point with
`z_l ≥ 1/N`, with `S` the lines not parallel to `l` and `σ = ∑_{j ∈ S} zⱼ`, `U ≥ κσ`;
`Q_e ≤ Cσ` for `e ∥ l`, `Q_e ≤ C` otherwise; so the weight is `≲ σ^{-(k + |E ∩ S|/2)}`, and the
arithmetic–geometric mean inequality bounds this by `∏_{j ∈ S} zⱼ^{-s}`, `s < 1`. -/
theorem integrableOn_refinedWeight_of_criterion (α : Fin (m + 1) → Fin 2 → ℝ) (k : ℕ)
    (E : Finset (Fin (m + 1))) (hcrit : NoSubdivergenceRefined k E α) :
    IntegrableOn (fun x => refinedWeight k E α (simplexPoint x)) (simplexSet m) := by
  have hm : 0 < m := by have := hcrit.noSubdivergenceOfOrder.le; omega
  set T : Fin (m + 1) → Finset (Fin (m + 1)) := fun l =>
    Finset.univ.filter fun j => pairDet α l j ≠ 0 with hTdef
  set n : Fin (m + 1) → ℕ := fun l => (T l).card with hndef
  set J : Fin (m + 1) → ℕ := fun l => (E.filter fun e => pairDet α l e ≠ 0).card with hJdef
  have hcr : ∀ l, 2 * k + J l < 2 * n l := hcrit
  have hn0 : ∀ l, 0 < n l := fun l => by have := hcr l; omega
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_pairDet_sq α
  set Cm : ℝ := ∑ e, ∑ j, pairDet α e j ^ 2 with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hle_Cm : ∀ e j, pairDet α e j ^ 2 ≤ Cm := fun e j =>
    (Finset.single_le_sum (f := fun j => pairDet α e j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun e => ∑ j, pairDet α e j ^ 2)
        (fun e _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ e))
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set κ : ℝ := c / (2 * ((m : ℝ) + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  set B : ℝ := 1 + Cm / κ with hB
  have hB1 : 1 ≤ B := by have : 0 ≤ Cm / κ := by positivity
                         linarith
  set p : Fin (m + 1) → ℝ := fun l => (k : ℝ) + (J l : ℝ) / 2 with hpdef
  have hp0 : ∀ l, 0 ≤ p l := fun l => by positivity
  have hs1 : ∀ l, p l / (n l : ℝ) < 1 := fun l => by
    have hn' : (0 : ℝ) < n l := by exact_mod_cast hn0 l
    rw [div_lt_one hn']
    have : ((2 * k + J l : ℕ) : ℝ) < ((2 * n l : ℕ) : ℝ) := by exact_mod_cast hcr l
    push_cast at this
    simp only [hpdef]
    linarith
  set D : Fin (m + 1) → ℝ := fun l =>
    (κ ^ k)⁻¹ * Real.sqrt B ^ E.card * (((n l : ℝ) ^ p l)⁻¹) with hDdef
  have hint : IntegrableOn (fun x => ∑ l, D l * ∏ j ∈ T l, simplexPoint x j ^ (-(p l / n l)))
      (simplexSet m) :=
    integrable_finsetSum _ fun l _ =>
      (integrableOn_prod_simplexPoint_rpow (T l) (div_nonneg (hp0 l) (by positivity))
        (hs1 l)).const_mul _
  have hmeasU := (continuous_symanzikU_comp_simplexPoint α).measurable
  have hmeasQ : ∀ e, Measurable fun x : Fin m → ℝ => lineQuad α e (simplexPoint x) := fun e => by
    unfold lineQuad
    exact Finset.measurable_sum _ fun j _ =>
      ((continuous_simplexPoint (m := m) j).measurable).mul measurable_const
  refine hint.mono' ?_ ?_
  · refine (((hmeasU.pow_const k).inv).mul ?_).aestronglyMeasurable
    exact Finset.measurable_prod _ fun e _ =>
      (measurable_const.add ((hmeasQ e).div hmeasU)).sqrt
  rw [ae_restrict_iff' (Feynman.measurableSet_simplexSet m)]
  filter_upwards [ae_simplexPoint_ne_zero hm] with x hx0 hxS
  obtain ⟨hz0, hz1⟩ := Feynman.simplexPoint_mem_stdSimplex hxS
  set z := simplexPoint x with hzdef
  have hzpos : ∀ i, 0 < z i := fun i => lt_of_le_of_ne (hz0 i) (hx0 i).symm
  obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
    (f := fun _ => ((m : ℝ) + 1)⁻¹) (g := z) (by
      rw [hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [mul_inv_cancel₀ hm1.ne'])
  -- the partial sum `σ` over the lines not parallel to `l`
  set σ := ∑ j ∈ T l, z j with hσ
  obtain ⟨j₀, hj₀⟩ : (T l).Nonempty := Finset.card_pos.mp (hn0 l)
  have hj₀' : pairDet α l j₀ ≠ 0 := (Finset.mem_filter.mp hj₀).2
  have hσ0 : 0 < σ := Finset.sum_pos (fun j _ => hzpos j) ⟨j₀, hj₀⟩
  have hσ1 : σ ≤ 1 := by
    rw [← hz1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hz0 j
  -- `U ≥ κ σ`
  have hrow := mul_sum_pairDet_sq_le_two_mul_symanzikU α hz0 l
  have hsub : c * σ ≤ ∑ j, z j * pairDet α l j ^ 2 := by
    rw [hσ, Finset.mul_sum]
    refine (Finset.sum_le_sum fun j hj => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (T l)) fun j _ _ => mul_nonneg (hz0 j) (sq_nonneg _))
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hc l j (Finset.mem_filter.mp hj).2) (hz0 j)
  have hUσ : κ * σ ≤ symanzikU α z := by
    have h1 : ((m : ℝ) + 1)⁻¹ * (c * σ) ≤ z l * ∑ j, z j * pairDet α l j ^ 2 :=
      mul_le_mul hl hsub (by positivity) (hz0 l)
    have : κ * σ = ((m : ℝ) + 1)⁻¹ * (c * σ) / 2 := by rw [hκ]; field_simp
    rw [this]
    linarith
  have hU0 : 0 < symanzikU α z := lt_of_lt_of_le (by positivity) hUσ
  -- the factors of the product
  have hfac : ∀ e ∈ E, Real.sqrt (1 + lineQuad α e z / symanzikU α z) ≤
      Real.sqrt B * (if pairDet α l e ≠ 0 then (Real.sqrt σ)⁻¹ else 1) := by
    intro e _
    by_cases hle : pairDet α l e = 0
    · -- `e` is parallel to `l`: `Q_e ≤ Cm σ`
      have hQ : lineQuad α e z ≤ Cm * σ := by
        unfold lineQuad
        rw [hσ, Finset.mul_sum]
        calc ∑ j, z j * pairDet α e j ^ 2 = ∑ j ∈ T l, z j * pairDet α e j ^ 2 := by
              refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
              have : pairDet α e j = 0 := by
                by_contra hej
                exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j,
                  pairDet_ne_zero_of_pairDet_eq_zero α hj₀' hle hej⟩)
              rw [this]; ring
          _ ≤ ∑ j ∈ T l, Cm * z j := Finset.sum_le_sum fun j _ => by
              rw [mul_comm Cm]
              exact mul_le_mul_of_nonneg_left (hle_Cm e j) (hz0 j)
      have hQU : lineQuad α e z / symanzikU α z ≤ Cm / κ := by
        rw [div_le_div_iff₀ hU0 hκ0]
        calc lineQuad α e z * κ ≤ Cm * σ * κ :=
              mul_le_mul_of_nonneg_right hQ hκ0.le
          _ = Cm * (κ * σ) := by ring
          _ ≤ Cm * symanzikU α z := mul_le_mul_of_nonneg_left hUσ hCm0
      simp only [hle, ne_eq, not_true_eq_false, ite_false, mul_one]
      exact Real.sqrt_le_sqrt (by linarith)
    · -- otherwise `Q_e ≤ Cm`
      have hQ : lineQuad α e z ≤ Cm := by
        unfold lineQuad
        calc ∑ j, z j * pairDet α e j ^ 2 ≤ ∑ j, z j * Cm :=
              Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle_Cm e j) (hz0 j)
          _ = Cm := by rw [← Finset.sum_mul, hz1, one_mul]
      have hQU : 1 + lineQuad α e z / symanzikU α z ≤ B / σ := by
        have h1 : lineQuad α e z / symanzikU α z ≤ Cm / (κ * σ) :=
          div_le_div₀ hCm0 hQ (by positivity) hUσ
        have h2 : 1 ≤ 1 / σ := by rw [le_div_iff₀ hσ0]; linarith
        have h3 : B / σ = 1 / σ + Cm / (κ * σ) := by rw [hB]; field_simp
        rw [h3]
        linarith
      simp only [hle, ne_eq, not_false_eq_true, ite_true]
      calc Real.sqrt (1 + lineQuad α e z / symanzikU α z) ≤ Real.sqrt (B / σ) :=
            Real.sqrt_le_sqrt hQU
        _ = Real.sqrt B * (Real.sqrt σ)⁻¹ := by
            rw [Real.sqrt_div' B hσ0.le, div_eq_mul_inv]
  have hprod : ∏ e ∈ E, Real.sqrt (1 + lineQuad α e z / symanzikU α z) ≤
      Real.sqrt B ^ E.card * ((Real.sqrt σ)⁻¹) ^ J l := by
    calc ∏ e ∈ E, Real.sqrt (1 + lineQuad α e z / symanzikU α z)
        ≤ ∏ e ∈ E, (Real.sqrt B * (if pairDet α l e ≠ 0 then (Real.sqrt σ)⁻¹ else 1)) :=
          Finset.prod_le_prod₀ (fun e _ => Real.sqrt_nonneg _) hfac
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite, Finset.prod_const,
            Finset.prod_const_one, mul_one]
  -- combine
  have hUk : (symanzikU α z ^ k)⁻¹ ≤ (κ ^ k)⁻¹ * (σ ^ k)⁻¹ := by
    rw [← mul_inv, ← mul_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hUσ k)
  have hσp : (σ ^ k)⁻¹ * ((Real.sqrt σ)⁻¹) ^ J l = (σ ^ p l)⁻¹ := by
    rw [inv_pow, ← mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_natCast (σ ^ (1 / (2 : ℝ))),
      ← Real.rpow_mul hσ0.le, ← Real.rpow_natCast σ k, ← Real.rpow_add hσ0]
    congr 2
    simp only [hpdef]
    ring
  have hamgm := inv_rpow_le_of_amgm (hn0 l) rfl hzpos (hp0 l)
  have hw0 : 0 ≤ refinedWeight k E α z := by
    unfold refinedWeight
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hU0.le _))
      (Finset.prod_nonneg fun e _ => Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg hw0]
  have hsqB : 0 ≤ Real.sqrt B ^ E.card := pow_nonneg (Real.sqrt_nonneg _) _
  calc refinedWeight k E α z
      ≤ ((κ ^ k)⁻¹ * (σ ^ k)⁻¹) * (Real.sqrt B ^ E.card * ((Real.sqrt σ)⁻¹) ^ J l) :=
        mul_le_mul hUk hprod (Finset.prod_nonneg fun e _ => Real.sqrt_nonneg _) (by positivity)
    _ = (κ ^ k)⁻¹ * Real.sqrt B ^ E.card * ((σ ^ k)⁻¹ * ((Real.sqrt σ)⁻¹) ^ J l) := by ring
    _ = (κ ^ k)⁻¹ * Real.sqrt B ^ E.card * ((∑ j ∈ T l, z j) ^ p l)⁻¹ := by rw [hσp]
    _ ≤ (κ ^ k)⁻¹ * Real.sqrt B ^ E.card *
          (((n l : ℝ) ^ p l)⁻¹ * ∏ j ∈ T l, z j ^ (-(p l / n l))) :=
        mul_le_mul_of_nonneg_left hamgm (by positivity)
    _ = D l * ∏ j ∈ T l, z j ^ (-(p l / n l)) := by rw [hDdef]; ring
    _ ≤ ∑ l, D l * ∏ j ∈ T l, z j ^ (-(p l / n l)) :=
        Finset.single_le_sum (f := fun l => D l * ∏ j ∈ T l, z j ^ (-(p l / n l)))
          (fun l _ => mul_nonneg (by positivity)
            (Finset.prod_nonneg fun j _ => (Real.rpow_pos_of_pos (hzpos j) _).le))
          (Finset.mem_univ l)

end QED.Integration.TwoLoop

end
