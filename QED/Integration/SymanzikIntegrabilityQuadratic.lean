/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopParametricNumerator
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Graph criteria for the integrability of `trᵃ A · U⁻ᵏ` on the simplex

The parametric representation with numerators of degree at most two
(`jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom`) assumes that `tr A · U⁻³` is
integrable on the simplex (`hA`), besides `U⁻²` (`hU`). This file gives a graph criterion for
it, and for the powers needed by numerators of higher degree.

For `N = m + 1` lines with loop coefficients `αᵢ ∈ ℝ²`, `A(z) = ∑ᵢ zᵢ αᵢ αᵢᵀ`, `U = det A`,
`dᵢⱼ = det(αᵢ, αⱼ)` (`pairDet`), the **criterion of order `n`** (`NoSubdivergenceOfOrder n`) asks
that every line `i` have at least `n` lines `j` with `dᵢⱼ ≠ 0`; for nonzero `αᵢ`, that the
complement of every direction class (the lines parallel to `αᵢ`) have at least `n` lines,
counted with multiplicity. Order `3` is `NoSubdivergence`
(`QED/Integration/SymanzikIntegrability.lean`); order `4` is `NoSubdivergenceQuadratic`, the
criterion for numerators of degree two; order `5` is `NoSubdivergenceQuartic`, for degree four.

* Under the criterion of order `k + 1`, `U⁻ᵏ` is integrable on the simplex
  (`integrableOn_inv_pow_symanzikU_of_criterion`). The proof is that of the case `k = 2`: some
  `zₗ ≥ 1/N`, so `2U ≥ zₗ ∑ⱼ zⱼ dₗⱼ² ≥ (c/N) ∑_{j ∈ T} zⱼ` for a set `T` of `k + 1` lines not
  parallel to `l`, and by the arithmetic–geometric mean inequality
  `(∑_{T} zⱼ)⁻ᵏ ≤ (k+1)⁻ᵏ ∏_{T} zⱼ^{-k/(k+1)}`, integrable since `k/(k+1) < 1`.
* `tr A = ∑ᵢ zᵢ |αᵢ|²` is bounded on the simplex (`trace_symanzikMatrix_le`), so the same
  criterion makes `trʲ A · U⁻ᵏ` integrable (`integrableOn_trace_pow_mul_inv_pow_symanzikU`). In
  particular `NoSubdivergenceQuadratic` gives `hA` (`integrableOn_trace_mul_inv_cube_symanzikU`),
  and `NoSubdivergenceQuartic` gives `tr² A · U⁻⁴`.

## Power counting

The criterion is the right one (not proved here; checked numerically, see below). On the face
where the coordinates of a set `S` of lines vanish like `λ`, the measure contributes `λ^{|S|}`,
`U` vanishes like `λ^{ω(S)}` with `ω(S)` the least number of lines of `S` in a non-parallel pair,
and `tr A` does not vanish unless every nonzero line is in `S`. For `S` the complement of a
direction class, `ω(S) = 1`, so `trʲ A · U⁻ᵏ` needs `|S| > k`: this is the criterion of order
`k + 1`. The other faces give weaker conditions. Bounding `tr A` loses nothing: the condition for
`trʲ A · U⁻ᵏ` is that for `U⁻ᵏ`. For `k = 3` it says that every one-loop subgraph has at least
four lines, the power counting of a one-loop subintegration with a numerator of degree two.

## Numerical check

Not part of the formal statement: on the loop matrices of
`QED/Integration/SymanzikIntegrabilityClasses.lean`, with and without the Pauli–Villars doubling,
the criterion of order `4` (resp. `5`) agrees with the Newton-polytope face test for `tr A · U⁻³`
(resp. `tr² A · U⁻⁴`) on every class, and Monte Carlo truncated means `E[min(f, T)]`,
`T = 10², …, 10⁸`, stay bounded for the classes satisfying it and grow with `T` otherwise.

## Main statements

* `NoSubdivergenceOfOrder`, `NoSubdivergenceQuadratic`, `NoSubdivergenceQuartic`.
* `integrableOn_inv_pow_symanzikU_of_criterion`: `U⁻ᵏ` under the criterion of order `k + 1`.
* `integrableOn_trace_pow_mul_inv_pow_symanzikU`: `trʲ A · U⁻ᵏ` under the same criterion.
* `integrableOn_trace_mul_inv_cube_symanzikU`: `hA` under `NoSubdivergenceQuadratic`.
* `jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom_of_criterion` and the monomial
  forms `..._degree_one_of_criterion`, `..._degree_two_of_criterion`: the representation with
  numerators of degree at most two, with `hspan`, `hU`, `hA` replaced by
  `NoSubdivergenceQuadratic α`.
-/

@[expose] public section

open MeasureTheory Set Matrix Finset Complex
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-! ### The criterion of order `n` -/

/-- The criterion of order `n`: every line `i` has at least `n` lines `j` with
`det(αᵢ, αⱼ) ≠ 0`, that is (for nonzero `αᵢ`) the complement of every direction class has at
least `n` lines, counted with multiplicity. -/
def NoSubdivergenceOfOrder (n : ℕ) (α : Fin (m + 1) → Fin 2 → ℝ) : Prop :=
  ∀ i, n ≤ (Finset.univ.filter fun j => pairDet α i j ≠ 0).card

/-- The criterion for numerators of degree two: the complement of every direction class has at
least four lines. -/
def NoSubdivergenceQuadratic (α : Fin (m + 1) → Fin 2 → ℝ) : Prop :=
  NoSubdivergenceOfOrder 4 α

/-- The criterion for numerators of degree four: the complement of every direction class has at
least five lines. -/
def NoSubdivergenceQuartic (α : Fin (m + 1) → Fin 2 → ℝ) : Prop :=
  NoSubdivergenceOfOrder 5 α

theorem noSubdivergence_iff_ofOrder_three (α : Fin (m + 1) → Fin 2 → ℝ) :
    NoSubdivergence α ↔ NoSubdivergenceOfOrder 3 α :=
  Iff.rfl

theorem NoSubdivergenceOfOrder.mono {n n' : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}
    (h : NoSubdivergenceOfOrder n' α) (hn : n ≤ n') : NoSubdivergenceOfOrder n α :=
  fun i => hn.trans (h i)

theorem NoSubdivergenceQuadratic.noSubdivergence {α : Fin (m + 1) → Fin 2 → ℝ}
    (h : NoSubdivergenceQuadratic α) : NoSubdivergence α :=
  NoSubdivergenceOfOrder.mono h (by norm_num)

theorem NoSubdivergenceQuartic.noSubdivergenceQuadratic {α : Fin (m + 1) → Fin 2 → ℝ}
    (h : NoSubdivergenceQuartic α) : NoSubdivergenceQuadratic α :=
  NoSubdivergenceOfOrder.mono h (by norm_num)

theorem NoSubdivergenceOfOrder.le {n : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}
    (h : NoSubdivergenceOfOrder n α) : n ≤ m := by
  have h0 := h 0
  have hsub : (Finset.univ.filter fun j => pairDet α 0 j ≠ 0) ⊆ Finset.univ.erase 0 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    refine Finset.mem_erase.mpr ⟨fun h => hj.2 ?_, Finset.mem_univ j⟩
    rw [h, pairDet_self]
  have := (Finset.card_le_card hsub).trans_eq' rfl
  rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin] at this
  omega

/-! ### The arithmetic–geometric mean step with `n` terms -/

theorem card_mul_prod_rpow_le_sum {ι : Type*} (T : Finset ι) {n : ℕ} (hn : 0 < n)
    (hT : T.card = n) {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    (n : ℝ) * ∏ i ∈ T, z i ^ (1 / (n : ℝ)) ≤ ∑ i ∈ T, z i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean_weighted T (fun _ => (1 / (n : ℝ))) z
    (fun _ _ => by positivity) (by rw [Finset.sum_const, hT, nsmul_eq_mul]; field_simp)
    (fun i _ => hz i)
  rw [← Finset.mul_sum] at h
  have := mul_le_mul_of_nonneg_left h hn'.le
  rwa [← mul_assoc, mul_one_div_cancel hn'.ne', one_mul] at this

theorem prod_rpow_neg_div {ι : Type*} (T : Finset ι) {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i)
    (k : ℕ) :
    ∏ i ∈ T, z i ^ (-((k : ℝ) / ((k : ℝ) + 1))) =
      ((∏ i ∈ T, z i ^ (1 / ((k : ℝ) + 1))) ^ k)⁻¹ := by
  rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i), Real.rpow_neg (hz i)]
  congr 2
  field_simp

/-! ### `U⁻ᵏ` under the criterion of order `k + 1` -/

/-- **`U⁻ᵏ` is integrable** on the simplex under the criterion of order `k + 1`: for every line
`i`, at least `k + 1` lines `j` have `det(αᵢ, αⱼ) ≠ 0`. -/
theorem integrableOn_inv_pow_symanzikU_of_criterion (α : Fin (m + 1) → Fin 2 → ℝ) (k : ℕ)
    (hcrit : NoSubdivergenceOfOrder (k + 1) α) :
    IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ k)⁻¹) (simplexSet m) := by
  have hm : 0 < m := by have := hcrit.le; omega
  choose T hTsub hTcard using fun l => Finset.exists_subset_card_eq (hcrit l)
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_pairDet_sq α
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set κ : ℝ := ((k : ℝ) + 1) * c / (2 * ((m : ℝ) + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  set s : ℝ := (k : ℝ) / ((k : ℝ) + 1) with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s < 1 := by rw [hs, div_lt_one hk1]; linarith
  have hint : IntegrableOn (fun x => (κ ^ k)⁻¹ * ∑ l, ∏ j ∈ T l,
      simplexPoint x j ^ (-s)) (simplexSet m) :=
    (integrable_finsetSum _ fun l _ =>
      integrableOn_prod_simplexPoint_rpow (T l) hs0 hs1).const_mul _
  refine hint.mono'
    ((continuous_symanzikU_comp_simplexPoint α).pow k).measurable.inv.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (Feynman.measurableSet_simplexSet m)]
  filter_upwards [ae_simplexPoint_ne_zero hm] with x hx0 hxS
  obtain ⟨hz0, hz1⟩ := Feynman.simplexPoint_mem_stdSimplex hxS
  set z := simplexPoint x with hzdef
  have hzpos : ∀ i, 0 < z i := fun i => lt_of_le_of_ne (hz0 i) (hx0 i).symm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  -- a coordinate of size at least `1/N`
  obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
    (f := fun _ => ((m : ℝ) + 1)⁻¹) (g := z) (by
      rw [hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [mul_inv_cancel₀ hm1.ne'])
  set P : ℝ := ∏ j ∈ T l, z j ^ (1 / ((k : ℝ) + 1)) with hP
  have hP0 : 0 < P := Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hzpos j) _
  -- the row bound
  have hrow := mul_sum_pairDet_sq_le_two_mul_symanzikU α hz0 l
  have hsub : ∑ j ∈ T l, z j * c ≤ ∑ j, z j * pairDet α l j ^ 2 := by
    refine (Finset.sum_le_sum fun j hj => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (T l)) fun j _ _ => mul_nonneg (hz0 j) (sq_nonneg _))
    exact mul_le_mul_of_nonneg_left (hc l j (Finset.mem_filter.mp (hTsub l hj)).2) (hz0 j)
  have hamgm := card_mul_prod_rpow_le_sum (T l) (Nat.succ_pos k) (hTcard l) hz0
  push_cast at hamgm
  have hUl : κ * P ≤ symanzikU α z := by
    rw [← Finset.sum_mul] at hsub
    have h1 : ((m : ℝ) + 1)⁻¹ * (c * (((k : ℝ) + 1) * P)) ≤
        z l * ∑ j, z j * pairDet α l j ^ 2 := by
      have h2 : c * (((k : ℝ) + 1) * P) ≤ ∑ j, z j * pairDet α l j ^ 2 := by
        have := mul_le_mul_of_nonneg_left hamgm hc0.le
        nlinarith
      exact mul_le_mul hl h2 (by positivity) (hz0 l)
    rw [hκ]
    have : ((k : ℝ) + 1) * c / (2 * ((m : ℝ) + 1)) * P =
        ((m : ℝ) + 1)⁻¹ * (c * (((k : ℝ) + 1) * P)) / 2 := by
      field_simp
    rw [this]
    linarith
  have hκP : 0 < κ * P := mul_pos hκ0 hP0
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (symanzikU_nonneg α hz0) _))]
  calc (symanzikU α z ^ k)⁻¹ ≤ ((κ * P) ^ k)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hκP.le hUl k)
    _ = (κ ^ k)⁻¹ * ∏ j ∈ T l, z j ^ (-s) := by
        rw [hs, prod_rpow_neg_div _ hz0, ← hP, mul_pow, mul_inv]
    _ ≤ (κ ^ k)⁻¹ * ∑ l, ∏ j ∈ T l, z j ^ (-s) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.single_le_sum (f := fun l => ∏ j ∈ T l, z j ^ (-s))
          (fun l _ => Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hz0 j) _)
          (Finset.mem_univ l)

/-! ### Powers of the trace -/

theorem continuous_trace_symanzikMatrix_comp_simplexPoint (α : Fin (m + 1) → Fin 2 → ℝ) :
    Continuous fun x : Fin m → ℝ => (symanzikMatrix α (simplexPoint x)).trace := by
  simp only [trace_fin_two, symanzikMatrix, of_apply]
  have := fun i => continuous_simplexPoint (m := m) i
  fun_prop

theorem trace_symanzikMatrix_nonneg (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) : 0 ≤ (symanzikMatrix α z).trace := by
  rw [trace_fin_two]
  simp only [symanzikMatrix, of_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_nonneg fun i _ => by
    nlinarith [hz i, mul_nonneg (hz i) (mul_self_nonneg (α i 0)),
      mul_nonneg (hz i) (mul_self_nonneg (α i 1))]

/-- **`trʲ A · U⁻ᵏ` is integrable** on the simplex under the criterion of order `k + 1`, since
`tr A` is bounded there. -/
theorem integrableOn_trace_pow_mul_inv_pow_symanzikU (α : Fin (m + 1) → Fin 2 → ℝ) (j k : ℕ)
    (hcrit : NoSubdivergenceOfOrder (k + 1) α) :
    IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace ^ j *
      (symanzikU α (simplexPoint x) ^ k)⁻¹) (simplexSet m) := by
  set C : ℝ := ∑ i, (α i 0 ^ 2 + α i 1 ^ 2)
  refine ((integrableOn_inv_pow_symanzikU_of_criterion α k hcrit).const_mul (C ^ j)).mono'
    (((continuous_trace_symanzikMatrix_comp_simplexPoint α).pow j).measurable.mul
      ((continuous_symanzikU_comp_simplexPoint α).pow k).measurable.inv).aestronglyMeasurable ?_
  rw [ae_restrict_iff' (Feynman.measurableSet_simplexSet m)]
  refine Filter.Eventually.of_forall fun x hxS => ?_
  obtain ⟨hz0, hz1⟩ := Feynman.simplexPoint_mem_stdSimplex hxS
  have ht0 := trace_symanzikMatrix_nonneg α hz0
  have htC := trace_symanzikMatrix_le α hz0 hz1
  have hUk : 0 ≤ (symanzikU α (simplexPoint x) ^ k)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (symanzikU_nonneg α hz0) _)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht0 _) hUk)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 htC j) hUk

/-- **The hypothesis `hA`** of the representation with numerators of degree two:
`tr A · U⁻³` is integrable on the simplex under `NoSubdivergenceQuadratic`. -/
theorem integrableOn_trace_mul_inv_cube_symanzikU (α : Fin (m + 1) → Fin 2 → ℝ)
    (hcrit : NoSubdivergenceQuadratic α) :
    IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace *
      (symanzikU α (simplexPoint x) ^ 3)⁻¹) (simplexSet m) := by
  simpa using integrableOn_trace_pow_mul_inv_pow_symanzikU α 1 3 hcrit

/-- `tr² A · U⁻⁴` is integrable on the simplex under `NoSubdivergenceQuartic`. -/
theorem integrableOn_trace_sq_mul_inv_pow_four_symanzikU (α : Fin (m + 1) → Fin 2 → ℝ)
    (hcrit : NoSubdivergenceQuartic α) :
    IntegrableOn (fun x => (symanzikMatrix α (simplexPoint x)).trace ^ 2 *
      (symanzikU α (simplexPoint x) ^ 4)⁻¹) (simplexSet m) :=
  integrableOn_trace_pow_mul_inv_pow_symanzikU α 2 4 hcrit

/-! ### The representation with numerators of degree at most two under the criterion -/

section Representation

variable (P : LoopQuadratic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) {ε : ℝ}

/-- **The representation with numerators of degree at most two under the graph criterion.**
`jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom`, with `hspan`, `hU`, `hA`
replaced by `NoSubdivergenceQuadratic α` (the complement of every direction class has at least
four lines). -/
theorem jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom_of_criterion
    (hm : 5 ≤ m) (hε : 0 < ε) (hcrit : NoSubdivergenceQuadratic α) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ =>
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ,
        P.eval (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) *
          ∏ i, (lineDenom α p M ε i fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))⁻¹) ∧
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            P.eval (-loopShift α p (simplexPoint x)) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            P.contract (symanzikMatrix α (simplexPoint x))) :=
  jointEnergyFirstIntegral_loopQuadratic_mul_prod_inv_lineDenom P α p M hm hε
    hcrit.noSubdivergence.span
    (integrableOn_inv_sq_symanzikU_of_criterion α hcrit.noSubdivergence)
    (integrableOn_trace_mul_inv_cube_symanzikU α hcrit)

/-- **Degree one under the graph criterion.** -/
theorem jointEnergyFirstIntegral_mul_prod_inv_lineDenom_degree_one_of_criterion
    (hm : 5 ≤ m) (hε : 0 < ε) (hcrit : NoSubdivergenceQuadratic α) (s : Fin 2) (μ : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => ((ℓ s μ : ℝ) : ℂ) * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ((m - 4).factorial : ℂ) *
        ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
          ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
          ((-loopShift α p (simplexPoint x) s μ : ℝ) : ℂ) :=
  jointEnergyFirstIntegral_mul_prod_inv_lineDenom_degree_one α p M hm hε
    hcrit.noSubdivergence.span
    (integrableOn_inv_sq_symanzikU_of_criterion α hcrit.noSubdivergence)
    (integrableOn_trace_mul_inv_cube_symanzikU α hcrit) s μ

/-- **Degree two under the graph criterion.** -/
theorem jointEnergyFirstIntegral_mul_prod_inv_lineDenom_degree_two_of_criterion
    (hm : 5 ≤ m) (hε : 0 < ε) (hcrit : NoSubdivergenceQuadratic α) (s : Fin 2) (μ : Fin 4)
    (r : Fin 2) (ν : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => ((ℓ s μ * ℓ r ν : ℝ) : ℂ) * ∏ i, (lineDenom α p M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
            ((loopShift α p (simplexPoint x) s μ * loopShift α p (simplexPoint x) r ν : ℝ) : ℂ) +
          ((m - 5).factorial : ℂ) / 2 *
            ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
            (((Minkowski.metric μ ν : ℝ) : ℂ) *
              (((symanzikMatrix α (simplexPoint x))⁻¹ s r : ℝ) : ℂ))) :=
  jointEnergyFirstIntegral_mul_prod_inv_lineDenom_degree_two α p M hm hε
    hcrit.noSubdivergence.span
    (integrableOn_inv_sq_symanzikU_of_criterion α hcrit.noSubdivergence)
    (integrableOn_trace_mul_inv_cube_symanzikU α hcrit) s μ r ν

end Representation

end QED.Integration.TwoLoop

end
