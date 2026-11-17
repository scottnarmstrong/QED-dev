/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopParametricAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Integrability of the first Symanzik polynomial on the simplex

For `N = m + 1` lines with loop coefficients `αᵢ ∈ ℝ²` (`α : Fin (m + 1) → Fin 2 → ℝ`), the first
Symanzik polynomial `U(z) = det A(z)`, `A(z) = ∑ᵢ zᵢ αᵢ αᵢᵀ` (`symanzikU`), is a sum of squares
(the Cauchy–Binet formula for `2 × 2` determinants):
`U(z) = ∑_{i<j} zᵢ zⱼ dᵢⱼ²`, `dᵢⱼ = det(αᵢ, αⱼ) = αᵢ₀ αⱼ₁ - αᵢ₁ αⱼ₀` (`pairDet`).

This file discharges the integrability hypotheses of the scalar two-loop parametric
representation (`QED/Integration/TwoLoopParametric.lean`) on the simplex
`simplexSet m` (Lebesgue measure on the first `m` barycentric coordinates):

* `U^{-1/2}` is integrable as soon as two of the `αᵢ` are independent (`hspan`), because
  `U ≥ zᵢ zⱼ dᵢⱼ²` and `(zᵢ zⱼ)^{-1/2}` is integrable.
* `U⁻²` is integrable under the **no-subdivergence criterion**: for every line `i`, at least three
  lines `j` have `dᵢⱼ ≠ 0`. For nonzero `αᵢ` the lines with `dᵢⱼ = 0` are the direction class of
  `i` (the lines parallel to it), so the criterion says that the complement of every direction
  class has at least three lines. The bound is elementary: some `zₖ ≥ 1/N`, so
  `2U ≥ zₖ ∑ⱼ zⱼ dₖⱼ² ≥ (c/N) (z_a + z_b + z_c)` for three lines `a, b, c` not parallel to `k`,
  and by the arithmetic–geometric mean inequality `(z_a + z_b + z_c)⁻² ≤ (z_a z_b z_c)^{-2/3}/9`.

Both rest on one integrability statement: `∏_{i ∈ T} zᵢ^{-s}` is integrable on the simplex for
every set `T` of barycentric coordinates and `0 ≤ s < 1`
(`integrableOn_prod_simplexPoint_rpow`). It is proved on the cube when `T` avoids the last
coordinate (a product of one-variable integrals), transported by the measure-preserving
affine involution `simplexSwap` that exchanges a coordinate with the last one, and for `T` the
set of all coordinates by bounding the largest coordinate below by `1/N`.

The criterion is also necessary (the classical power counting of the faces where `U → 0`;
not proved here): if a direction class `D` has at most two lines outside it, `U` vanishes to
first order at the face where the coordinates outside `D` vanish, and `U⁻²` is not integrable.

## Main statements

* `two_mul_symanzikU`, `symanzikU_eq_sum_Ioi`: the Cauchy–Binet formula.
* `integrableOn_prod_simplexPoint_rpow`: products of `zᵢ^{-s}`, `s < 1`, are integrable.
* `integrableOn_inv_sqrt_symanzikU_of_span`: `U^{-1/2}` is integrable under `hspan`.
* `integrableOn_inv_sq_symanzikU_of_criterion`: `U⁻²` is integrable under the criterion.
-/

@[expose] public section

open MeasureTheory Set Matrix Finset

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-! ### The Cauchy–Binet formula -/

/-- The determinant `det(αᵢ, αⱼ) = αᵢ₀ αⱼ₁ - αᵢ₁ αⱼ₀` of two loop-coefficient vectors. -/
def pairDet (α : Fin (m + 1) → Fin 2 → ℝ) (i j : Fin (m + 1)) : ℝ :=
  α i 0 * α j 1 - α i 1 * α j 0

theorem pairDet_self (α : Fin (m + 1) → Fin 2 → ℝ) (i : Fin (m + 1)) : pairDet α i i = 0 := by
  unfold pairDet; ring

theorem pairDet_sq_comm (α : Fin (m + 1) → Fin 2 → ℝ) (i j : Fin (m + 1)) :
    pairDet α j i ^ 2 = pairDet α i j ^ 2 := by
  unfold pairDet; ring

/-- **Cauchy–Binet (`2 × 2`), symmetric form:** `2 U(z) = ∑ᵢ ∑ⱼ zᵢ zⱼ dᵢⱼ²`. -/
theorem two_mul_symanzikU (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) :
    2 * symanzikU α z = ∑ i, ∑ j, z i * z j * pairDet α i j ^ 2 := by
  set P : Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun i j => z i * α i 0 * α i 0 * (z j * α j 1 * α j 1) with hP
  set Q : Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun i j => z i * α i 0 * α i 1 * (z j * α j 1 * α j 0) with hQ
  have h1 : ∑ i, ∑ j, z i * z j * pairDet α i j ^ 2 =
      ∑ i, ∑ j, P i j + ∑ i, ∑ j, P j i - 2 * ∑ i, ∑ j, Q i j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hP, hQ, pairDet]
    ring
  have h2 : ∑ i, ∑ j, P j i = ∑ i, ∑ j, P i j := Finset.sum_comm
  rw [h1, h2, symanzikU, Matrix.det_fin_two]
  simp only [symanzikMatrix, Matrix.of_apply, Finset.sum_mul_sum, hP, hQ]
  ring

/-- **Cauchy–Binet (`2 × 2`):** `U(z) = ∑_{i<j} zᵢ zⱼ dᵢⱼ²`, with an `if` over all pairs. -/
theorem symanzikU_eq_sum_ite (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) :
    symanzikU α z = ∑ i, ∑ j, if i < j then z i * z j * pairDet α i j ^ 2 else 0 := by
  have hpt : ∀ i j, z i * z j * pairDet α i j ^ 2 =
      (if i < j then z i * z j * pairDet α i j ^ 2 else 0) +
        (if j < i then z j * z i * pairDet α j i ^ 2 else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt]
    · simp [pairDet_self]
    · simp only [h.not_gt, h, ↓reduceIte, pairDet_sq_comm]
      ring
  have h2 : 2 * symanzikU α z = ∑ i, ∑ j, ((if i < j then z i * z j * pairDet α i j ^ 2 else 0) +
      (if j < i then z j * z i * pairDet α j i ^ 2 else 0)) := by
    rw [two_mul_symanzikU]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
  have hc : ∑ i, ∑ j, (if j < i then z j * z i * pairDet α j i ^ 2 else 0) =
      ∑ i, ∑ j, (if i < j then z i * z j * pairDet α i j ^ 2 else 0) := Finset.sum_comm
  simp only [Finset.sum_add_distrib] at h2
  linarith

/-- **Cauchy–Binet (`2 × 2`):** `U(z) = ∑ᵢ ∑_{j > i} zᵢ zⱼ dᵢⱼ²`. -/
theorem symanzikU_eq_sum_Ioi (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) :
    symanzikU α z = ∑ i, ∑ j ∈ Finset.Ioi i, z i * z j * pairDet α i j ^ 2 := by
  rw [symanzikU_eq_sum_ite]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

theorem symanzikU_nonneg (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) : 0 ≤ symanzikU α z := by
  have h := two_mul_symanzikU α z
  have : 0 ≤ ∑ i, ∑ j, z i * z j * pairDet α i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      have := hz i; have := hz j; positivity
  linarith

theorem le_sum_sum {g : Fin (m + 1) → Fin (m + 1) → ℝ} (hg : ∀ a b, 0 ≤ g a b)
    (a b : Fin (m + 1)) : g a b ≤ ∑ a, ∑ b, g a b :=
  (Finset.single_le_sum (fun b _ => hg a b) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, g a b)
      (fun a _ => Finset.sum_nonneg fun b _ => hg a b) (Finset.mem_univ a))

/-- One term of Cauchy–Binet: `zᵢ zⱼ dᵢⱼ² ≤ U(z)` for `z ≥ 0`. -/
theorem mul_mul_pairDet_sq_le_symanzikU (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (i j : Fin (m + 1)) :
    z i * z j * pairDet α i j ^ 2 ≤ symanzikU α z := by
  have hg : ∀ a b : Fin (m + 1),
      0 ≤ if a < b then z a * z b * pairDet α a b ^ 2 else 0 := by
    intro a b
    split_ifs
    · have := hz a; have := hz b; positivity
    · exact le_rfl
  rw [symanzikU_eq_sum_ite]
  rcases lt_trichotomy i j with h | rfl | h
  · simpa [h] using le_sum_sum hg i j
  · rw [pairDet_self]
    simpa using (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hg a b)
  · have := le_sum_sum hg j i
    simp only [h, ↓reduceIte, pairDet_sq_comm] at this
    linarith

/-- One row of Cauchy–Binet: `zₖ ∑ⱼ zⱼ dₖⱼ² ≤ 2 U(z)` for `z ≥ 0`. -/
theorem mul_sum_pairDet_sq_le_two_mul_symanzikU (α : Fin (m + 1) → Fin 2 → ℝ)
    {z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (k : Fin (m + 1)) :
    z k * ∑ j, z j * pairDet α k j ^ 2 ≤ 2 * symanzikU α z := by
  rw [two_mul_symanzikU, Finset.mul_sum]
  have h := Finset.single_le_sum (f := fun i => ∑ j, z i * z j * pairDet α i j ^ 2)
    (fun i _ => Finset.sum_nonneg fun j _ => by have := hz i; have := hz j; positivity)
    (Finset.mem_univ k)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) h
  ring

/-! ### The simplex: membership and the exchange of a coordinate with the last one -/

theorem mem_simplexSet_iff (hm : 0 < m) (x : Fin m → ℝ) :
    x ∈ simplexSet m ↔ ∀ i, 0 ≤ simplexPoint x i := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  constructor
  · exact fun hx => (Feynman.simplexPoint_mem_stdSimplex hx).1
  · intro h
    rw [← Fin.snoc_init_self x, Feynman.snoc_mem_simplexSet_iff]
    have hl := h (Fin.last (n + 1))
    rw [simplexPoint_last, Fin.sum_univ_castSucc] at hl
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have := h i.castSucc.castSucc
      rwa [simplexPoint_castSucc] at this
    · have := h (Fin.last n).castSucc
      rwa [simplexPoint_castSucc] at this
    · simp only [Fin.init]
      linarith

theorem sum_update_eq (x : Fin m → ℝ) (j : Fin m) (v : ℝ) :
    ∑ i, Function.update x j v i = v + ∑ i, x i - x j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase Finset.univ x (Finset.mem_univ j)
  linarith

/-- The affine involution of `ℝᵐ` exchanging the barycentric coordinates `j` and `m`:
`xⱼ` is replaced by `1 - ∑ᵢ xᵢ`. -/
def simplexSwap (j : Fin m) (x : Fin m → ℝ) : Fin m → ℝ :=
  Function.update x j (1 - ∑ i, x i)

theorem sum_simplexSwap (j : Fin m) (x : Fin m → ℝ) : ∑ i, simplexSwap j x i = 1 - x j := by
  rw [simplexSwap, sum_update_eq]
  ring

theorem simplexPoint_simplexSwap (j : Fin m) (x : Fin m → ℝ) (i : Fin (m + 1)) :
    simplexPoint (simplexSwap j x) i = simplexPoint x (Equiv.swap j.castSucc (Fin.last m) i) := by
  induction i using Fin.lastCases with
  | last =>
    rw [Equiv.swap_apply_right, simplexPoint_last, sum_simplexSwap, simplexPoint_castSucc]
    ring
  | cast k =>
    rw [simplexPoint_castSucc]
    by_cases hk : k = j
    · subst hk
      rw [Equiv.swap_apply_left, simplexPoint_last, simplexSwap, Function.update_self]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h => hk (Fin.castSucc_injective _ h))
        (Fin.castSucc_ne_last k), simplexPoint_castSucc, simplexSwap, Function.update_of_ne hk]

theorem simplexSwap_simplexSwap (j : Fin m) (x : Fin m → ℝ) :
    simplexSwap j (simplexSwap j x) = x := by
  have h1 : 1 - ∑ i, simplexSwap j x i = x j := by rw [sum_simplexSwap]; ring
  show Function.update (simplexSwap j x) j (1 - ∑ i, simplexSwap j x i) = x
  rw [h1, simplexSwap, Function.update_idem, Function.update_eq_self]

theorem simplexSwap_mem_iff (j : Fin m) (x : Fin m → ℝ) :
    simplexSwap j x ∈ simplexSet m ↔ x ∈ simplexSet m := by
  rw [mem_simplexSet_iff j.pos, mem_simplexSet_iff j.pos]
  simp only [simplexPoint_simplexSwap]
  constructor
  · intro h i
    simpa using h (Equiv.swap j.castSucc (Fin.last m) i)
  · exact fun h i => h _

theorem preimage_simplexSwap (j : Fin m) : simplexSwap j ⁻¹' simplexSet m = simplexSet m :=
  Set.ext fun x => simplexSwap_mem_iff j x

/-- The linear part of `simplexSwap j`: row `j` replaced by `(-1, …, -1)`. -/
def swapMatrix (j : Fin m) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.updateRow 1 j fun _ => -1

theorem swapMatrix_mulVec (j : Fin m) (x : Fin m → ℝ) :
    swapMatrix j *ᵥ x = Function.update x j (-∑ i, x i) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp [swapMatrix, Matrix.mulVec, dotProduct]
  · simp [swapMatrix, Matrix.mulVec, dotProduct, hi, Matrix.one_apply]

theorem simplexSwap_eq (j : Fin m) :
    simplexSwap j = fun x => swapMatrix j *ᵥ x + Pi.single j 1 := by
  funext x i
  rw [swapMatrix_mulVec, simplexSwap]
  by_cases hi : i = j
  · subst hi
    simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same]
    ring
  · simp [hi]

theorem swapMatrix_mul_self (j : Fin m) : swapMatrix j * swapMatrix j = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_one, LinearMap.id_apply,
    Matrix.toLin'_apply, Matrix.toLin'_apply, swapMatrix_mulVec, swapMatrix_mulVec, sum_update_eq,
    Function.update_idem]
  have : -(-∑ i, x i + ∑ i, x i - x j) = x j := by ring
  rw [this, Function.update_eq_self]

theorem abs_det_swapMatrix (j : Fin m) : |(swapMatrix j).det| = 1 := by
  have h : (swapMatrix j).det * (swapMatrix j).det = 1 := by
    rw [← Matrix.det_mul, swapMatrix_mul_self, Matrix.det_one]
  rcases mul_self_eq_one_iff.mp h with h1 | h1 <;> simp [h1]

theorem measurePreserving_simplexSwap (j : Fin m) :
    MeasurePreserving (simplexSwap j) volume volume := by
  have hdet : (swapMatrix j).det ≠ 0 := by
    intro h
    have := abs_det_swapMatrix j
    rw [h, abs_zero] at this
    exact zero_ne_one this
  have hL : MeasurePreserving (Matrix.toLin' (swapMatrix j)) volume volume := by
    refine ⟨(Matrix.toLin' (swapMatrix j)).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, abs_inv, abs_det_swapMatrix, inv_one,
      ENNReal.ofReal_one, one_smul]
  have := (measurePreserving_add_right volume (Pi.single j (1 : ℝ) : Fin m → ℝ)).comp hL
  rw [simplexSwap_eq]
  convert this using 1
  funext x
  simp [Matrix.toLin'_apply]

/-- `simplexSwap j` as a measurable equivalence (it is an involution). -/
def simplexSwapEquiv (j : Fin m) : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) where
  toFun := simplexSwap j
  invFun := simplexSwap j
  left_inv := simplexSwap_simplexSwap j
  right_inv := simplexSwap_simplexSwap j
  measurable_toFun := (measurePreserving_simplexSwap j).measurable
  measurable_invFun := (measurePreserving_simplexSwap j).measurable

theorem integrableOn_comp_simplexSwap_iff (j : Fin m) {f : (Fin m → ℝ) → ℝ} :
    IntegrableOn (f ∘ simplexSwap j) (simplexSet m) ↔ IntegrableOn f (simplexSet m) := by
  have h := (measurePreserving_simplexSwap j).integrableOn_comp_preimage
    (simplexSwapEquiv j).measurableEmbedding (f := f) (s := simplexSet m)
  rwa [preimage_simplexSwap] at h

/-! ### Products of negative powers of the barycentric coordinates -/

theorem integrableOn_Icc_rpow_neg {s : ℝ} (hs : s < 1) :
    IntegrableOn (fun t : ℝ => t ^ (-s)) (Icc 0 1) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by linarith)

/-- A product of one-variable functions, each integrable on `[0, 1]`, is integrable on the
simplex. -/
theorem integrableOn_simplexSet_of_prod {f : Fin m → ℝ → ℝ}
    (hf : ∀ i, IntegrableOn (f i) (Icc 0 1)) :
    IntegrableOn (fun x : Fin m → ℝ => ∏ i, f i (x i)) (simplexSet m) := by
  refine IntegrableOn.mono_set ?_ (Feynman.simplexSet_subset_Icc m)
  rw [← Set.pi_univ_Icc, IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod hf

theorem integrableOn_prod_simplexPoint_rpow_of_last_notMem (T : Finset (Fin (m + 1)))
    (hT : Fin.last m ∉ T) {s : ℝ} (hs : s < 1) :
    IntegrableOn (fun x => ∏ i ∈ T, simplexPoint x i ^ (-s)) (simplexSet m) := by
  have heq : (fun x : Fin m → ℝ => ∏ i ∈ T, simplexPoint x i ^ (-s)) =
      fun x => ∏ i : Fin m, (fun (i : Fin m) (t : ℝ) =>
        if i.castSucc ∈ T then t ^ (-s) else 1) i (x i) := by
    funext x
    rw [← Finset.univ_inter T, ← Finset.prod_ite_mem, Fin.prod_univ_castSucc]
    simp [hT, simplexPoint_castSucc]
  rw [heq]
  refine integrableOn_simplexSet_of_prod
    (f := fun (i : Fin m) (t : ℝ) => if i.castSucc ∈ T then t ^ (-s) else 1) fun i => ?_
  by_cases hi : i.castSucc ∈ T
  · simp only [hi, ↓reduceIte]
    exact integrableOn_Icc_rpow_neg hs
  · simp only [hi, ↓reduceIte]
    exact integrableOn_const isCompact_Icc.measure_lt_top.ne

theorem integrableOn_prod_simplexPoint_rpow_of_ne_univ (T : Finset (Fin (m + 1)))
    (hT : T ≠ Finset.univ) {s : ℝ} (hs : s < 1) :
    IntegrableOn (fun x => ∏ i ∈ T, simplexPoint x i ^ (-s)) (simplexSet m) := by
  by_cases hl : Fin.last m ∈ T
  · obtain ⟨k, hk⟩ : ∃ k, k ∉ T := by
      by_contra h
      push Not at h
      exact hT (Finset.eq_univ_of_forall h)
    obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.castSucc = k := by
      induction k using Fin.lastCases with
      | last => exact absurd hl hk
      | cast j => exact ⟨j, rfl⟩
    rw [← integrableOn_comp_simplexSwap_iff j]
    have heq : (fun x => ∏ i ∈ T, simplexPoint x i ^ (-s)) ∘ simplexSwap j =
        fun x => ∏ i ∈ T.map (Equiv.swap j.castSucc (Fin.last m)).toEmbedding,
          simplexPoint x i ^ (-s) := by
      funext x
      simp only [Function.comp, simplexPoint_simplexSwap, Finset.prod_map,
        Equiv.coe_toEmbedding]
    rw [heq]
    refine integrableOn_prod_simplexPoint_rpow_of_last_notMem _ ?_ hs
    rw [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
    exact hk
  · exact integrableOn_prod_simplexPoint_rpow_of_last_notMem T hl hs

theorem measurable_prod_simplexPoint_rpow (T : Finset (Fin (m + 1))) (r : ℝ) :
    Measurable fun x : Fin m → ℝ => ∏ i ∈ T, simplexPoint x i ^ r :=
  Finset.measurable_prod _ fun i _ => (continuous_simplexPoint i).measurable.pow_const r

/-- **Products of negative powers.** For every set `T` of barycentric coordinates and
`0 ≤ s < 1`, `∏_{i ∈ T} zᵢ^{-s}` is integrable on the simplex (`z = simplexPoint x`). -/
theorem integrableOn_prod_simplexPoint_rpow (T : Finset (Fin (m + 1))) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    IntegrableOn (fun x => ∏ i ∈ T, simplexPoint x i ^ (-s)) (simplexSet m) := by
  by_cases hT : T = Finset.univ
  · subst hT
    set c : ℝ := ((m : ℝ) + 1)⁻¹ ^ (-s)
    have hint : IntegrableOn (fun x => c * ∑ k, ∏ i ∈ Finset.univ.erase k,
        simplexPoint x i ^ (-s)) (simplexSet m) :=
      (integrable_finsetSum _ fun k _ => integrableOn_prod_simplexPoint_rpow_of_ne_univ _
        (fun h => Finset.notMem_erase k _ (h ▸ Finset.mem_univ k)) hs1).const_mul c
    refine hint.mono' (measurable_prod_simplexPoint_rpow _ _).aestronglyMeasurable
      (ae_restrict_of_forall_mem (Feynman.measurableSet_simplexSet m) fun x hx => ?_)
    obtain ⟨hz0, hz1⟩ := Feynman.simplexPoint_mem_stdSimplex hx
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
      (f := fun _ => ((m : ℝ) + 1)⁻¹) (g := simplexPoint x) (by
        rw [hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [mul_inv_cancel₀ hm1.ne'])
    have hnn : ∀ t : Finset (Fin (m + 1)), 0 ≤ ∏ i ∈ t, simplexPoint x i ^ (-s) :=
      fun t => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz0 i) _
    rw [Real.norm_of_nonneg (hnn _), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    have hck : simplexPoint x k ^ (-s) ≤ c :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hk (by linarith)
    have hsum : ∏ i ∈ Finset.univ.erase k, simplexPoint x i ^ (-s) ≤
        ∑ k, ∏ i ∈ Finset.univ.erase k, simplexPoint x i ^ (-s) :=
      Finset.single_le_sum (f := fun k => ∏ i ∈ Finset.univ.erase k, simplexPoint x i ^ (-s))
        (fun k _ => hnn _) (Finset.mem_univ k)
    exact mul_le_mul hck hsum (hnn _) ((Real.rpow_nonneg (hz0 k) _).trans hck)
  · exact integrableOn_prod_simplexPoint_rpow_of_ne_univ T hT hs1

/-! ### `U^{-1/2}` -/

theorem continuous_symanzikU (α : Fin (m + 1) → Fin 2 → ℝ) : Continuous (symanzikU α) := by
  have : Continuous fun z : Fin (m + 1) → ℝ => symanzikMatrix α z :=
    continuous_matrix fun s t => by
      simp only [symanzikMatrix, of_apply]
      fun_prop
  exact this.matrix_det

theorem continuous_symanzikU_comp_simplexPoint (α : Fin (m + 1) → Fin 2 → ℝ) :
    Continuous fun x : Fin m → ℝ => symanzikU α (simplexPoint x) :=
  (continuous_symanzikU α).comp (continuous_pi fun i => continuous_simplexPoint i)

/-- **`U^{-1/2}` is integrable** on the simplex as soon as two of the `αᵢ` are independent:
`U ≥ zᵢ zⱼ dᵢⱼ²` and `(zᵢ zⱼ)^{-1/2}` is integrable. -/
theorem integrableOn_inv_sqrt_symanzikU_of_span (α : Fin (m + 1) → Fin 2 → ℝ) (hm : 0 < m)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) :
    IntegrableOn (fun x => (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹) (simplexSet m) := by
  obtain ⟨i, j, hij⟩ := hspan
  have hd : pairDet α i j ≠ 0 := hij
  have hne : i ≠ j := by
    rintro rfl
    exact hd (pairDet_self α i)
  have hint : IntegrableOn (fun x => |pairDet α i j|⁻¹ *
      ∏ k ∈ {i, j}, simplexPoint x k ^ (-(1 / 2 : ℝ))) (simplexSet m) :=
    (integrableOn_prod_simplexPoint_rpow _ (by norm_num) (by norm_num)).const_mul _
  refine hint.mono'
    (continuous_symanzikU_comp_simplexPoint α).sqrt.measurable.inv.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (Feynman.measurableSet_simplexSet m)]
  filter_upwards [ae_simplexPoint_ne_zero hm] with x hx0 hxS
  have hz0 := (Feynman.simplexPoint_mem_stdSimplex hxS).1
  have hzi : 0 < simplexPoint x i := lt_of_le_of_ne (hz0 i) (hx0 i).symm
  have hzj : 0 < simplexPoint x j := lt_of_le_of_ne (hz0 j) (hx0 j).symm
  have hU := mul_mul_pairDet_sq_le_symanzikU α hz0 i j
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), Finset.prod_pair hne,
    Real.rpow_neg hzi.le, Real.rpow_neg hzj.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hdpos : 0 < |pairDet α i j| := abs_pos.mpr hd
  have hle : |pairDet α i j| * (Real.sqrt (simplexPoint x i) * Real.sqrt (simplexPoint x j)) ≤
      Real.sqrt (symanzikU α (simplexPoint x)) := by
    rw [← Real.sqrt_mul hzi.le, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < |pairDet α i j| * (Real.sqrt (simplexPoint x i) * Real.sqrt (simplexPoint x j)) :=
    by positivity
  calc (Real.sqrt (symanzikU α (simplexPoint x)))⁻¹
      ≤ (|pairDet α i j| * (Real.sqrt (simplexPoint x i) * Real.sqrt (simplexPoint x j)))⁻¹ :=
        inv_anti₀ hpos hle
    _ = |pairDet α i j|⁻¹ * ((Real.sqrt (simplexPoint x i))⁻¹ *
          (Real.sqrt (simplexPoint x j))⁻¹) := by
        rw [mul_inv, mul_inv]

/-! ### `U⁻²` under the no-subdivergence criterion -/

/-- The no-subdivergence criterion: every line `i` has at least three lines `j` with
`det(αᵢ, αⱼ) ≠ 0`, that is (for nonzero `αᵢ`) the complement of every direction class has at
least three lines. -/
def NoSubdivergence (α : Fin (m + 1) → Fin 2 → ℝ) : Prop :=
  ∀ i, 3 ≤ (Finset.univ.filter fun j => pairDet α i j ≠ 0).card

theorem NoSubdivergence.three_le {α : Fin (m + 1) → Fin 2 → ℝ} (h : NoSubdivergence α) :
    3 ≤ m := by
  have h0 := h 0
  have hsub : (Finset.univ.filter fun j => pairDet α 0 j ≠ 0) ⊆ Finset.univ.erase 0 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    refine Finset.mem_erase.mpr ⟨fun h => hj.2 ?_, Finset.mem_univ j⟩
    rw [h, pairDet_self]
  have := (Finset.card_le_card hsub).trans_eq' rfl
  rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin] at this
  omega

theorem NoSubdivergence.span {α : Fin (m + 1) → Fin 2 → ℝ} (h : NoSubdivergence α) :
    ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 := by
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) (h 0))
  exact ⟨0, j, (Finset.mem_filter.mp hj).2⟩

theorem exists_pos_le_pairDet_sq (α : Fin (m + 1) → Fin 2 → ℝ) :
    ∃ c > 0, ∀ i j, pairDet α i j ≠ 0 → c ≤ pairDet α i j ^ 2 := by
  by_cases hne : ((Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))).filter
      fun p => pairDet α p.1 p.2 ≠ 0).Nonempty
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ (fun p => pairDet α p.1 p.2 ^ 2) hne
    refine ⟨_, lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (Finset.mem_filter.mp hp).2)), fun i j hij => ?_⟩
    exact hmin (i, j) (by simp [hij])
  · exact ⟨1, one_pos, fun i j hij => absurd ⟨(i, j), by simp [hij]⟩ hne⟩

/-- The arithmetic–geometric mean step: for `z > 0` on a set `T` of three indices,
`(∑_{T} z)` bounds `3 ∏_{T} z^{1/3}`, and `∏_{T} z^{-2/3} = (∏_{T} z^{1/3})⁻²`. -/
theorem three_mul_prod_rpow_le_sum {ι : Type*} (T : Finset ι) (hT : T.card = 3) {z : ι → ℝ}
    (hz : ∀ i, 0 ≤ z i) : 3 * ∏ i ∈ T, z i ^ (1 / 3 : ℝ) ≤ ∑ i ∈ T, z i := by
  have h := Real.geom_mean_le_arith_mean_weighted T (fun _ => (1 / 3 : ℝ)) z
    (fun _ _ => by norm_num) (by rw [Finset.sum_const, hT]; norm_num) (fun i _ => hz i)
  rw [← Finset.mul_sum] at h
  linarith

theorem prod_rpow_neg_two_thirds {ι : Type*} (T : Finset ι) {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∏ i ∈ T, z i ^ (-(2 / 3 : ℝ)) = ((∏ i ∈ T, z i ^ (1 / 3 : ℝ)) ^ 2)⁻¹ := by
  rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i), Real.rpow_neg (hz i)]
  norm_num

/-- **`U⁻²` is integrable** on the simplex under the no-subdivergence criterion: for every line
`i`, at least three lines `j` have `det(αᵢ, αⱼ) ≠ 0`. -/
theorem integrableOn_inv_sq_symanzikU_of_criterion (α : Fin (m + 1) → Fin 2 → ℝ)
    (hcrit : NoSubdivergence α) :
    IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ 2)⁻¹) (simplexSet m) := by
  have hm : 0 < m := by have := hcrit.three_le; omega
  choose T hTsub hTcard using fun k => Finset.exists_subset_card_eq (hcrit k)
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_pairDet_sq α
  set κ : ℝ := 3 * c / (2 * ((m : ℝ) + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hint : IntegrableOn (fun x => (κ ^ 2)⁻¹ * ∑ k, ∏ j ∈ T k,
      simplexPoint x j ^ (-(2 / 3 : ℝ))) (simplexSet m) :=
    (integrable_finsetSum _ fun k _ =>
      integrableOn_prod_simplexPoint_rpow (T k) (by norm_num) (by norm_num)).const_mul _
  refine hint.mono'
    ((continuous_symanzikU_comp_simplexPoint α).pow 2).measurable.inv.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (Feynman.measurableSet_simplexSet m)]
  filter_upwards [ae_simplexPoint_ne_zero hm] with x hx0 hxS
  obtain ⟨hz0, hz1⟩ := Feynman.simplexPoint_mem_stdSimplex hxS
  set z := simplexPoint x with hzdef
  have hzpos : ∀ i, 0 < z i := fun i => lt_of_le_of_ne (hz0 i) (hx0 i).symm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  -- a coordinate of size at least `1/N`
  obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
    (f := fun _ => ((m : ℝ) + 1)⁻¹) (g := z) (by
      rw [hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [mul_inv_cancel₀ hm1.ne'])
  set P : ℝ := ∏ j ∈ T k, z j ^ (1 / 3 : ℝ) with hP
  have hP0 : 0 < P := Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hzpos j) _
  -- the row bound
  have hrow := mul_sum_pairDet_sq_le_two_mul_symanzikU α hz0 k
  have hsub : ∑ j ∈ T k, z j * c ≤ ∑ j, z j * pairDet α k j ^ 2 := by
    refine (Finset.sum_le_sum fun j hj => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (T k)) fun j _ _ => mul_nonneg (hz0 j) (sq_nonneg _))
    exact mul_le_mul_of_nonneg_left (hc k j (Finset.mem_filter.mp (hTsub k hj)).2) (hz0 j)
  have hamgm := three_mul_prod_rpow_le_sum (T k) (hTcard k) hz0
  have hUk : κ * P ≤ symanzikU α z := by
    rw [← Finset.sum_mul] at hsub
    have h1 : ((m : ℝ) + 1)⁻¹ * (c * (3 * P)) ≤ z k * ∑ j, z j * pairDet α k j ^ 2 := by
      have h2 : c * (3 * P) ≤ ∑ j, z j * pairDet α k j ^ 2 := by nlinarith
      exact mul_le_mul hk h2 (by positivity) (hz0 k)
    rw [hκ]
    have : 3 * c / (2 * ((m : ℝ) + 1)) * P = ((m : ℝ) + 1)⁻¹ * (c * (3 * P)) / 2 := by
      field_simp
    rw [this]
    linarith
  have hκP : 0 < κ * P := mul_pos hκ0 hP0
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  calc (symanzikU α z ^ 2)⁻¹ ≤ ((κ * P) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hκP.le hUk 2)
    _ = (κ ^ 2)⁻¹ * ∏ j ∈ T k, z j ^ (-(2 / 3 : ℝ)) := by
        rw [prod_rpow_neg_two_thirds _ hz0, ← hP, mul_pow, mul_inv]
    _ ≤ (κ ^ 2)⁻¹ * ∑ k, ∏ j ∈ T k, z j ^ (-(2 / 3 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.single_le_sum (f := fun k => ∏ j ∈ T k, z j ^ (-(2 / 3 : ℝ)))
          (fun k _ => Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hz0 j) _)
          (Finset.mem_univ k)

end QED.Integration.TwoLoop

end
