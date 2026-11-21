/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayAQWt
public import QED.GradedProof.RPi4FaceIdRayAPGen
public import QED.GradedProof.RPi4FaceCoeff
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# (R-Π₄) step L10, T2.UV: the coefficients of a merged piece through the adjugate

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (input (A) of
`QED.GradedProof.RPi4.faceIdRay_of_size_rate`). For data with rows `(1,0)`, `(0,1)`, `(1,-1)`
(line classes `0`, `1`, `2`, sums `Z₀`, `Z₁`, `Z₂`) the inverse Symanzik matrix is
`adj A / U`, `adj A = [[Z₁ + Z₂, Z₂], [Z₂, Z₀ + Z₂]]`. The coefficients of the merged integrand
(`QED.GradedProof.RPi4.faceIdRayAPOne`, `…Two`, `…Three`) are then bounded by
`U⁻²`, `U⁻³ Z`, `U⁻⁴ Z Z'` with sums `Z` over the classes the numerator sees:

* a numerator of degree `≤ 1` along loop `1` (classes `VA`, `VC`) does not see the entry
  `(1, 1)`: `U⁻³ (Z₁ + Z₂)`; if moreover its degree along loop `0` is `≤ 3`, the quartic
  contraction never sees `(0,0)(0,0)`: `U⁻⁴ (Z₁ + Z₂) Z₂`;
* a numerator of degrees `≤ 3` along both loops (class `VB`): `U⁻³ (Z₀ + Z₁ + Z₂)`,
  `U⁻⁴ (Z₀ + Z₂)(Z₁ + Z₂)`.

The numerators come as quartics of bounded degree along both loops at once
(`faceIdRayAQ_exists_loopQuartic`, from the uniqueness of a polynomial on real points).

* `faceIdRayAQ_mvPoly_eq`, `faceIdRayAQ_exists_loopQuartic`;
* `faceIdRayAQ_inv_entries`, `faceIdRayAQ_exists_shift_le`;
* `faceIdRayAQ_norm_one_le`, `faceIdRayAQ_norm_two_le_all`, `faceIdRayAQ_norm_two_le_deg`;
* `faceIdRayAQ_norm_contractFour_le`, `faceIdRayAQ_norm_three_le_VB`,
  `faceIdRayAQ_norm_three_le_VA`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-! ### Quartics of bounded degree along both loops -/

/-- **A polynomial in the loop momenta is determined by its values at real points.** -/
theorem faceIdRayAQ_mvPoly_eq {P Q : MvPolynomial (Fin 2 × Fin 4) ℂ}
    (h : ∀ ℓ : Fin 2 → Fin 4 → ℝ, MvPolynomial.eval (fun x => ((ℓ x.1 x.2 : ℝ) : ℂ)) P =
      MvPolynomial.eval (fun x => ((ℓ x.1 x.2 : ℝ) : ℂ)) Q) : P = Q := by
  refine MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) fun x hx => ?_
  have hx' : ∀ i, ∃ r : ℝ, (r : ℂ) = x i := fun i => hx i (Set.mem_univ i)
  choose y hy using hx'
  have e : x = fun i => ((y (i.1, i.2) : ℝ) : ℂ) := funext fun i => (hy i).symm
  rw [e]
  exact h fun s μ => y (s, μ)

theorem faceIdRayAQ_ofList_quart (l : List LoopIndex) (hl : l.length ≤ 3) :
    (LoopQuartic.ofList l).quart = 0 := by
  match l, hl with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl

/-- **A quartic of bounded degree along both loops**, without quartic part for total degree
`≤ 3`. -/
theorem faceIdRayAQ_exists_loopQuartic {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {n d₀ d₁ : ℕ}
    (hn : n ≤ 4) (hF : IsLoopPoly 2 n F) (h₀ : IsLoopPolyDeg 0 d₀ 4 F)
    (h₁ : IsLoopPolyDeg 1 d₁ 4 F) :
    ∃ P : LoopQuartic, LoopDegLe 0 d₀ P ∧ LoopDegLe 1 d₁ P ∧ (n ≤ 3 → P.quart = 0) ∧
      P.eval = F := by
  classical
  obtain ⟨Q, hQ, hFQ⟩ := hF
  obtain ⟨Q0, -, hs0, hF0⟩ := h₀
  obtain ⟨Q1, -, hs1, hF1⟩ := h₁
  have e0 : Q0 = Q := faceIdRayAQ_mvPoly_eq fun ℓ => by rw [← hF0, ← hFQ]
  have e1 : Q1 = Q := faceIdRayAQ_mvPoly_eq fun ℓ => by rw [← hF1, ← hFQ]
  rw [e0] at hs0
  rw [e1] at hs1
  have key : ∀ t : Finset (LoopIndex →₀ ℕ), t ⊆ Q.support → ∃ P : LoopQuartic,
      LoopDegLe 0 d₀ P ∧ LoopDegLe 1 d₁ P ∧ (n ≤ 3 → P.quart = 0) ∧
        ∀ X, P.evalC X = ∑ x ∈ t, Q.coeff x * ∏ i ∈ x.support, X i ^ x i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact fun _ => ⟨LoopQuartic.zero, LoopDegLe.zero, LoopDegLe.zero, fun _ => rfl,
        fun X => by simp [LoopQuartic.evalC_zero]⟩
    | insert x t hx ih =>
      intro ht
      obtain ⟨P, hP0, hP1, hPq, hP⟩ := ih ((Finset.subset_insert x t).trans ht)
      have hxQ : x ∈ Q.support := ht (Finset.mem_insert_self x t)
      have hlen : x.toMultiset.toList.length ≤ n := by
        rw [Multiset.length_toList, Finsupp.card_toMultiset]
        exact (MvPolynomial.le_totalDegree hxQ).trans hQ
      have hdeg : x.toMultiset.toList.length ≤ 4 := hlen.trans hn
      refine ⟨(LoopQuartic.smul (Q.coeff x) (LoopQuartic.ofList x.toMultiset.toList)).add P,
        ((LoopDegLe.ofList _ ?_).smul _).add hP0, ((LoopDegLe.ofList _ ?_).smul _).add hP1,
        fun h3 => ?_, fun X => ?_⟩
      · rw [sum_map_loopInd_toList]
        exact hs0 x hxQ
      · rw [sum_map_loopInd_toList]
        exact hs1 x hxQ
      · have hq := faceIdRayAQ_ofList_quart _ (hlen.trans h3)
        funext a b c d
        simp only [LoopQuartic.add, LoopQuartic.smul, hq, hPq h3, Pi.zero_apply,
          mul_zero, add_zero]
      rw [LoopQuartic.evalC_add, LoopQuartic.evalC_smul, LoopQuartic.evalC_ofList _ hdeg,
        prod_map_toList_toMultiset, hP, Finset.sum_insert hx]
  obtain ⟨P, hP0, hP1, hPq, hP⟩ := key Q.support subset_rfl
  refine ⟨P, hP0, hP1, hPq, funext fun ℓ => ?_⟩
  rw [hFQ ℓ, MvPolynomial.eval_eq, LoopQuartic.eval, hP]
  rfl

/-! ### The inverse Symanzik matrix by classes -/

section Classes

variable (α : Fin (m + 1) → Fin 2 → ℝ) (cl : Fin (m + 1) → Fin 3)
  (hα : ∀ t, α t = faceIdRayAQRow (cl t))

include hα

theorem faceIdRayAQ_rows : ∀ i, α i = ![1, 0] ∨ α i = ![0, 1] ∨ α i = ![1, -1] := fun i => by
  rw [hα i]
  generalize cl i = a
  fin_cases a <;> simp [faceIdRayAQRow]

/-- The class sums are the chain sums. -/
theorem faceIdRayAQ_chainZ (z : Fin (m + 1) → ℝ) (κ : Fin 3) :
    chainZ α z (faceIdRayAQRow κ) = ∑ t, if cl t = κ then z t else 0 := by
  refine Finset.sum_congr rfl fun t _ => ?_
  have hi : α t = faceIdRayAQRow κ ↔ cl t = κ := by
    rw [hα t]
    constructor
    · generalize cl t = b
      fin_cases b <;> fin_cases κ <;> simp [faceIdRayAQRow, funext_iff, Fin.forall_fin_two]
    · intro h; rw [h]
  by_cases h : cl t = κ
  · rw [ite_eq_left (hi.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hi.mp h')), ite_eq_right h]

/-- **The inverse Symanzik matrix by classes**: `A⁻¹ = [[Z₁ + Z₂, Z₂], [Z₂, Z₀ + Z₂]] / U`
(`Z_κ` the class sums). -/
theorem faceIdRayAQ_inv_entries (z : Fin (m + 1) → ℝ) :
    (symanzikMatrix α z)⁻¹ 0 0 = (∑ t, if cl t ≠ 0 then z t else 0) / symanzikU α z ∧
      (symanzikMatrix α z)⁻¹ 1 1 = (∑ t, if cl t ≠ 1 then z t else 0) / symanzikU α z ∧
      (symanzikMatrix α z)⁻¹ 0 1 = (∑ t, if cl t = 2 then z t else 0) / symanzikU α z ∧
      (symanzikMatrix α z)⁻¹ 1 0 = (∑ t, if cl t = 2 then z t else 0) / symanzikU α z := by
  obtain ⟨h00, h11, h01, h10⟩ := symanzikMatrix_inv_chain α z (faceIdRayAQ_rows α cl hα)
  have c0 := faceIdRayAQ_chainZ α cl hα z 0
  have c1 := faceIdRayAQ_chainZ α cl hα z 1
  have c2 := faceIdRayAQ_chainZ α cl hα z 2
  simp only [faceIdRayAQRow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at c0 c1 c2
  have s0 : (∑ t, if cl t ≠ 0 then z t else 0) =
      (∑ t, if cl t = 1 then z t else 0) + ∑ t, if cl t = 2 then z t else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    generalize cl t = b
    fin_cases b <;> simp
  have s1 : (∑ t, if cl t ≠ 1 then z t else 0) =
      (∑ t, if cl t = 0 then z t else 0) + ∑ t, if cl t = 2 then z t else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    generalize cl t = b
    fin_cases b <;> simp
  rw [h00, h11, h01, h10, c0, c1, c2, s0, s1]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Classes

/-! ### The coefficients -/

/-- The loop shift along the ray is bounded. -/
theorem faceIdRayAQ_exists_shift_le (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → symanzikU α z ≠ 0 →
      ∀ a, ‖loopComp (-loopShift α (fun i => cs i • majRayVec 1) z) a‖ ≤ K := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_loopShift_smul_le α cs
  refine ⟨C * ∑ μ, |majRayVec 1 μ|, by positivity, fun z hz hU a => ?_⟩
  rw [loopComp, Complex.norm_real, Real.norm_eq_abs, Pi.neg_apply, Pi.neg_apply, abs_neg]
  refine (hC z hz hU (majRayVec 1) a.1 a.2).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  exact Finset.single_le_sum (f := fun μ => |majRayVec 1 μ|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ a.2)

/-- **`T₁ ≲ U⁻²`.** -/
theorem faceIdRayAQ_norm_one_le (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (cs : Fin (m + 1) → ℝ) : ∃ C, 0 ≤ C ∧ ∀ x : Fin m → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) →
        ‖faceIdRayAPOne Q α (fun i => cs i • majRayVec 1) x‖ ≤
          C / symanzikU α (simplexPoint x) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := faceIdRayAQ_exists_shift_le α cs
  refine ⟨lqNorm Q * (1 + K) ^ 4, mul_nonneg (lqNorm_nonneg Q) (by positivity),
    fun x hz hU => ?_⟩
  exact norm_invU_mul_le hU (norm_evalC_le_lqNorm Q _ hK0 (hK _ hz hU.ne'))

theorem faceIdRayAQ_div_cube {L g U B : ℝ} (hU : 0 < U) (h : B ≤ L * (g / U)) :
    B / U ^ 2 ≤ L * g / U ^ 3 := by
  calc B / U ^ 2 ≤ L * (g / U) / U ^ 2 := div_le_div_of_nonneg_right h (by positivity)
    _ = L * g / U ^ 3 := by field_simp

section Two

variable (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (cl : Fin (m + 1) → Fin 3)
  (hα : ∀ t, α t = faceIdRayAQRow (cl t)) (cs : Fin (m + 1) → ℝ)

include hα

/-- **`T₂ ≲ U⁻³ ∑ₜ zₜ`** for any numerator. -/
theorem faceIdRayAQ_norm_two_le_all : ∃ C, 0 ≤ C ∧ ∀ x : Fin m → ℝ,
    (∀ i, 0 ≤ simplexPoint x i) → 0 < symanzikU α (simplexPoint x) →
      ‖faceIdRayAPTwo Q α (fun i => cs i • majRayVec 1) x‖ ≤
        C * (∑ t, simplexPoint x t) / symanzikU α (simplexPoint x) ^ 3 := by
  obtain ⟨K, hK0, hK⟩ := faceIdRayAQ_exists_shift_le α cs
  refine ⟨lqHess Q * (1 + (K + K ^ 2)), mul_nonneg (lqHess_nonneg Q) (by positivity),
    fun x hz hU => ?_⟩
  set z := simplexPoint x
  have hrows := faceIdRayAQ_rows α cl hα
  have hg := abs_inv_le_chain α hrows hz hU.ne'
  have hsum : chainZ α z ![1, 0] + chainZ α z ![0, 1] + chainZ α z ![1, -1] = ∑ t, z t := by
    simp only [chainZ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases hrows t with h | h | h <;> simp [h]
  rw [hsum] at hg
  exact (norm_invU_mul_le hU le_rfl).trans (faceIdRayAQ_div_cube hU (norm_contractTwo_le Q _ _ hK0
      (hK z hz hU.ne') hg))

/-- **`T₂ ≲ U⁻³ (Z₁ + Z₂)`** for a numerator of degree `≤ 1` along loop `1`. -/
theorem faceIdRayAQ_norm_two_le_deg (hQ : LoopDegLe 1 1 Q) : ∃ C, 0 ≤ C ∧ ∀ x : Fin m → ℝ,
    (∀ i, 0 ≤ simplexPoint x i) → 0 < symanzikU α (simplexPoint x) →
      ‖faceIdRayAPTwo Q α (fun i => cs i • majRayVec 1) x‖ ≤
        C * (∑ t, if cl t ≠ 0 then simplexPoint x t else 0) /
          symanzikU α (simplexPoint x) ^ 3 := by
  obtain ⟨K, hK0, hK⟩ := faceIdRayAQ_exists_shift_le α cs
  refine ⟨lqHess Q * (1 + (K + K ^ 2)), mul_nonneg (lqHess_nonneg Q) (by positivity),
    fun x hz hU => ?_⟩
  set z := simplexPoint x
  obtain ⟨h00, -, h01, h10⟩ := faceIdRayAQ_inv_entries α cl hα z
  have hs2 : (∑ t, if cl t = 2 then z t else 0) ≤ ∑ t, if cl t ≠ 0 then z t else 0 :=
    Finset.sum_le_sum fun t _ => by
      by_cases h : cl t = 2
      · rw [ite_eq_left h, ite_eq_left (by rw [h]; decide)]
      · rw [ite_eq_right h]; split_ifs <;> simp [hz t]
  have hs0 : 0 ≤ ∑ t, if cl t = 2 then z t else 0 :=
    Finset.sum_nonneg fun t _ => by split_ifs <;> simp [hz t]
  have hg : ∀ r t, (r, t) ≠ ((1 : Fin 2), (1 : Fin 2)) →
      |(symanzikMatrix α z)⁻¹ r t| ≤ (∑ t, if cl t ≠ 0 then z t else 0) / symanzikU α z := by
    intro r t hrt
    fin_cases r <;> fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [h00, abs_of_nonneg (div_nonneg (hs0.trans hs2) hU.le)]
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
      rw [h01, abs_of_nonneg (div_nonneg hs0 hU.le)]
      exact div_le_div_of_nonneg_right hs2 hU.le
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
      rw [h10, abs_of_nonneg (div_nonneg hs0 hU.le)]
      exact div_le_div_of_nonneg_right hs2 hU.le
    · exact absurd rfl hrt
  exact (norm_invU_mul_le hU le_rfl).trans (faceIdRayAQ_div_cube hU (norm_contractTwo_le_deg hQ _ _ hK0
      (hK z hz hU.ne') (div_nonneg (hs0.trans hs2) hU.le) hg))

end Two

/-- **The quartic contraction from the loop counts of its nonzero coefficients**: if every
product `|(A⁻¹)_{x₁y₁}| |(A⁻¹)_{z₁w₁}|` with at most `d₀` indices in loop `0` and `d₁` in
loop `1` is `≤ P`, then `‖contractFour‖ ≤ 3 lqQuart P`. -/
theorem faceIdRayAQ_norm_contractFour_le {Q : LoopQuartic} {d₀ d₁ : ℕ}
    (h₀ : LoopDegLe 0 d₀ Q) (h₁ : LoopDegLe 1 d₁ Q) (A : Matrix (Fin 2) (Fin 2) ℝ) {P : ℝ}
    (hP : ∀ x y z w : LoopIndex,
      loopInd 0 x + loopInd 0 y + loopInd 0 z + loopInd 0 w ≤ d₀ →
      loopInd 1 x + loopInd 1 y + loopInd 1 z + loopInd 1 w ≤ d₁ →
        |A⁻¹ x.1 y.1| * |A⁻¹ z.1 w.1| ≤ P) :
    ‖Q.contractFour A‖ ≤ lqQuart Q * (3 * P) := by
  have hG : ∀ x y z w : LoopIndex, |loopMetricInv A x y * loopMetricInv A z w| ≤
      |A⁻¹ x.1 y.1| * |A⁻¹ z.1 w.1| := fun x y z w => by
    rw [abs_mul]
    exact mul_le_mul (abs_loopMetricInv_le A x y le_rfl) (abs_loopMetricInv_le A z w le_rfl)
      (abs_nonneg _) (abs_nonneg _)
  refine norm_contractFour_le_of_matPair A fun a b c e hq => ?_
  have c0 : loopInd 0 a + loopInd 0 b + loopInd 0 c + loopInd 0 e ≤ d₀ := by
    by_contra h; exact hq (h₀.quart a b c e (by omega))
  have c1 : loopInd 1 a + loopInd 1 b + loopInd 1 c + loopInd 1 e ≤ d₁ := by
    by_contra h; exact hq (h₁.quart a b c e (by omega))
  exact abs_matPair_le ((hG _ _ _ _).trans (hP _ _ _ _ c0 c1))
    ((hG _ _ _ _).trans (hP a c b e (by omega) (by omega)))
    ((hG _ _ _ _).trans (hP a e b c (by omega) (by omega)))

theorem faceIdRayAQ_div_four {L P U B : ℝ} (hU : 0 < U) (h : B ≤ L * (P / U ^ 2)) :
    B / U ^ 2 ≤ L * P / U ^ 4 := by
  calc B / U ^ 2 ≤ L * (P / U ^ 2) / U ^ 2 := div_le_div_of_nonneg_right h (by positivity)
    _ = L * P / U ^ 4 := by field_simp

section Three

variable (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (cl : Fin (m + 1) → Fin 3)
  (hα : ∀ t, α t = faceIdRayAQRow (cl t))

include hα

/-- **`T₃ ≲ U⁻⁴ (Z₀ + Z₂)(Z₁ + Z₂)`** for degrees `≤ 3` along both loops. -/
theorem faceIdRayAQ_norm_three_le_VB (h₀ : LoopDegLe 0 3 Q) (h₁ : LoopDegLe 1 3 Q) :
    ∃ C, 0 ≤ C ∧ ∀ x : Fin m → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) →
        ‖faceIdRayAPThree Q α x‖ ≤ C * ((∑ t, if cl t ≠ 1 then simplexPoint x t else 0) *
          (∑ t, if cl t ≠ 0 then simplexPoint x t else 0)) /
            symanzikU α (simplexPoint x) ^ 4 := by
  refine ⟨lqQuart Q * 3, mul_nonneg (lqQuart_nonneg Q) (by norm_num), fun x hz hU => ?_⟩
  set z := simplexPoint x
  set U := symanzikU α z
  obtain ⟨h00, h11, h01, h10⟩ := faceIdRayAQ_inv_entries α cl hα z
  set Z0 := ∑ t, if cl t ≠ 0 then z t else 0
  set Z1 := ∑ t, if cl t ≠ 1 then z t else 0
  set Z2 := ∑ t, if cl t = 2 then z t else 0
  have hle : ∀ (p : Fin 3 → Prop) [DecidablePred p], (∀ b, b = 2 → p b) →
      Z2 ≤ ∑ t, if p (cl t) then z t else 0 := fun p _ hp =>
    Finset.sum_le_sum fun t _ => by
      by_cases h : cl t = 2
      · rw [ite_eq_left h, ite_eq_left (hp _ h)]
      · rw [ite_eq_right h]; split_ifs <;> simp [hz t]
  have hZ2 : 0 ≤ Z2 := Finset.sum_nonneg fun t _ => by split_ifs <;> simp [hz t]
  have hZ20 : Z2 ≤ Z0 := hle (fun b => b ≠ 0) fun b hb => by rw [hb]; decide
  have hZ21 : Z2 ≤ Z1 := hle (fun b => b ≠ 1) fun b hb => by rw [hb]; decide
  have e00 : |(symanzikMatrix α z)⁻¹ 0 0| = Z0 / U := by
    rw [h00, abs_of_nonneg (div_nonneg (hZ2.trans hZ20) hU.le)]
  have e11 : |(symanzikMatrix α z)⁻¹ 1 1| = Z1 / U := by
    rw [h11, abs_of_nonneg (div_nonneg (hZ2.trans hZ21) hU.le)]
  have e01 : |(symanzikMatrix α z)⁻¹ 0 1| = Z2 / U := by
    rw [h01, abs_of_nonneg (div_nonneg hZ2 hU.le)]
  have e10 : |(symanzikMatrix α z)⁻¹ 1 0| = Z2 / U := by
    rw [h10, abs_of_nonneg (div_nonneg hZ2 hU.le)]
  have hU2 : 0 < U ^ 2 := by positivity
  have key : ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → a ≤ Z1 → c ≤ Z0 → a / U * (c / U) ≤
      Z1 * Z0 / U ^ 2 := fun a c ha hc ha' hc' => by
    rw [div_mul_div_comm, ← sq]
    exact div_le_div_of_nonneg_right (mul_le_mul ha' hc' hc (hZ2.trans hZ21)) hU2.le
  have hZ0 := hZ2.trans hZ20
  have hZ1 := hZ2.trans hZ21
  have r0 : Z0 ≤ Z0 := le_rfl
  have r1 : Z1 ≤ Z1 := le_rfl
  have hc := faceIdRayAQ_norm_contractFour_le h₀ h₁ (symanzikMatrix α z) (P := Z1 * Z0 / U ^ 2)
    fun x y v w c0 c1 => by
      obtain ⟨r, μ⟩ := x; obtain ⟨t, ν⟩ := y; obtain ⟨r', μ'⟩ := v; obtain ⟨t', ν'⟩ := w
      fin_cases r <;> fin_cases t <;> fin_cases r' <;> fin_cases t' <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at c0 c1 ⊢ <;>
        (try simp [loopInd] at c0 c1) <;>
        simp only [e00, e11, e01, e10] <;>
        first
          | (apply key <;> assumption)
          | (rw [mul_comm]; apply key <;> assumption)
  exact (norm_invU_mul_le hU le_rfl).trans (faceIdRayAQ_div_four hU
    (hc.trans_eq (by ring)))

/-- **`T₃ ≲ U⁻⁴ (Z₁ + Z₂) Z₂`** for degree `≤ 1` along loop `1` and `≤ 3` along loop `0`. -/
theorem faceIdRayAQ_norm_three_le_VA (h₀ : LoopDegLe 0 3 Q) (h₁ : LoopDegLe 1 1 Q) :
    ∃ C, 0 ≤ C ∧ ∀ x : Fin m → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) →
        ‖faceIdRayAPThree Q α x‖ ≤ C * ((∑ t, if cl t ≠ 0 then simplexPoint x t else 0) *
          (∑ t, if cl t = 2 then simplexPoint x t else 0)) /
            symanzikU α (simplexPoint x) ^ 4 := by
  refine ⟨lqQuart Q * 3, mul_nonneg (lqQuart_nonneg Q) (by norm_num), fun x hz hU => ?_⟩
  set z := simplexPoint x
  set U := symanzikU α z
  obtain ⟨h00, -, h01, h10⟩ := faceIdRayAQ_inv_entries α cl hα z
  set Z0 := ∑ t, if cl t ≠ 0 then z t else 0
  set Z2 := ∑ t, if cl t = 2 then z t else 0
  have hZ2 : 0 ≤ Z2 := Finset.sum_nonneg fun t _ => by split_ifs <;> simp [hz t]
  have hZ20 : Z2 ≤ Z0 := Finset.sum_le_sum fun t _ => by
    by_cases h : cl t = 2
    · rw [ite_eq_left h, ite_eq_left (by rw [h]; decide)]
    · rw [ite_eq_right h]; split_ifs <;> simp [hz t]
  have e00 : |(symanzikMatrix α z)⁻¹ 0 0| = Z0 / U := by
    rw [h00, abs_of_nonneg (div_nonneg (hZ2.trans hZ20) hU.le)]
  have e01 : |(symanzikMatrix α z)⁻¹ 0 1| = Z2 / U := by
    rw [h01, abs_of_nonneg (div_nonneg hZ2 hU.le)]
  have e10 : |(symanzikMatrix α z)⁻¹ 1 0| = Z2 / U := by
    rw [h10, abs_of_nonneg (div_nonneg hZ2 hU.le)]
  have hU2 : 0 < U ^ 2 := by positivity
  have key : ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → a ≤ Z0 → c ≤ Z2 → a / U * (c / U) ≤
      Z0 * Z2 / U ^ 2 := fun a c ha hc ha' hc' => by
    rw [div_mul_div_comm, ← sq]
    exact div_le_div_of_nonneg_right (mul_le_mul ha' hc' hc (hZ2.trans hZ20)) hU2.le
  have hZ0 := hZ2.trans hZ20
  have r0 : Z0 ≤ Z0 := le_rfl
  have r2 : Z2 ≤ Z2 := le_rfl
  have hc := faceIdRayAQ_norm_contractFour_le h₀ h₁ (symanzikMatrix α z) (P := Z0 * Z2 / U ^ 2)
    fun x y v w c0 c1 => by
      obtain ⟨r, μ⟩ := x; obtain ⟨t, ν⟩ := y; obtain ⟨r', μ'⟩ := v; obtain ⟨t', ν'⟩ := w
      fin_cases r <;> fin_cases t <;> fin_cases r' <;> fin_cases t' <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at c0 c1 ⊢ <;>
        (try simp [loopInd] at c0 c1) <;>
        simp only [e00, e01, e10] <;>
        first
          | (apply key <;> assumption)
          | (rw [mul_comm]; apply key <;> assumption)
  exact (norm_invU_mul_le hU le_rfl).trans (faceIdRayAQ_div_four hU
    (hc.trans_eq (by ring)))

end Three

end QED.GradedProof.RPi4

end
