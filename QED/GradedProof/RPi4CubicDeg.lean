/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LoopDegNum
public import QED.GradedProof.SE2TwoLoopGggg

/-!
# (R-Π₄) step L6d1: cubic numerators of bounded degree along one loop

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. The merged
pieces with seven lines (six after the photon collapse) have the numerator
`C (vNum X - vNum M) = C (X² - M²) (E₂ + (X² + M²) E₄)`, a polynomial of total degree two. Their
parametric integrand has no `v^{5-n} = v⁻¹` term only if the quartic is chosen without quartic
part; this file chooses it so, keeping the degree bound along one loop:

* `exists_loopQuartic_cubic_deg`: a polynomial of total degree `≤ 3` and degree `≤ d` along loop
  `s` is a `LoopQuartic` with `quart = 0` and `LoopDegLe s d`;
* `isLoopPolyDeg_vE2`, `isLoopPolyDeg_vNumE2`: the coefficient of `m²` of a class numerator has
  degree `≤ loopDegOf base s` along loop `s` (and total degree `2`);
* **`exists_loopQuartic_vNum_sub_cubic`**: the numerator of the seven-line pieces as such a
  quartic.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- **A polynomial of total degree `≤ 3` and degree `≤ d` along loop `s`** is a `LoopQuartic`
without quartic part whose coefficients with more than `d` indices in loop `s` vanish. -/
theorem exists_loopQuartic_cubic_deg {s : Fin 2} {d : ℕ} {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : IsLoopPolyDeg s d 3 F) :
    ∃ P : LoopQuartic, P.quart = 0 ∧ LoopDegLe s d P ∧ P.eval = F := by
  classical
  obtain ⟨Q, hQ, hsQ, hF⟩ := h
  have key : ∀ t : Finset (LoopIndex →₀ ℕ), t ⊆ Q.support → ∃ P : LoopQuartic,
      P.quart = 0 ∧ LoopDegLe s d P ∧
        ∀ X, P.evalC X = ∑ x ∈ t, Q.coeff x * ∏ i ∈ x.support, X i ^ x i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact fun _ => ⟨LoopQuartic.zero, rfl, LoopDegLe.zero, fun X => by
        simp [LoopQuartic.evalC_zero]⟩
    | insert x t hx ih =>
      intro ht
      obtain ⟨P, hPq, hPd, hP⟩ := ih ((Finset.subset_insert x t).trans ht)
      have hxQ : x ∈ Q.support := ht (Finset.mem_insert_self x t)
      have hdeg : x.toMultiset.toList.length ≤ 3 := by
        rw [Multiset.length_toList, Finsupp.card_toMultiset]
        exact (MvPolynomial.le_totalDegree hxQ).trans hQ
      refine ⟨(LoopQuartic.smul (Q.coeff x) (LoopQuartic.ofList x.toMultiset.toList)).add P,
        ?_, ((LoopDegLe.ofList _ ?_).smul _).add hPd, fun X => ?_⟩
      · have h0 := LoopQuartic.quart_ofList _ hdeg
        simp only [LoopQuartic.add, LoopQuartic.smul, h0, hPq, Pi.zero_apply, mul_zero]
        funext a b c e
        simp
      · rw [sum_map_loopInd_toList]
        exact hsQ x hxQ
      rw [LoopQuartic.evalC_add, LoopQuartic.evalC_smul,
        LoopQuartic.evalC_ofList _ (by omega), prod_map_toList_toMultiset, hP,
        Finset.sum_insert hx]
  obtain ⟨P, hPq, hPd, hP⟩ := key Q.support subset_rfl
  refine ⟨P, hPq, hPd, funext fun ℓ => ?_⟩
  rw [hF ℓ, MvPolynomial.eval_eq, LoopQuartic.eval, hP]
  rfl

/-- The degree along loop `s` of the numerator factor of fermion line `l`. -/
theorem isLoopPolyDegMat_fm_zero (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ)
    (s : Fin 2) (l : Fin 4) :
    IsLoopPolyDegMat s (if base l.castSucc s = 0 then 0 else 1) 1
      fun ℓ => electronNumerator 0 (fm base pp l ℓ) := by
  simp only [fm_eq_affine]
  rw [← affDeg_castLoopMatrix]
  exact isLoopPolyDegMat_electronNumerator s _ _ 0

/-- **The coefficient of `m²` of the trace of a fermion loop** has degree at most
`loopDegOf base s` along loop `s`. -/
theorem isLoopPolyDeg_vE2 (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ) (s : Fin 2)
    (G : Fin 4 → Mat) :
    IsLoopPolyDeg s (loopDegOf base s) 3 fun ℓ => vE2 G (fun l => fm base pp l ℓ) := by
  have N := isLoopPolyDegMat_fm_zero base pp s
  have C := fun l => IsLoopPolyDegMat.const (s := s) (G l)
  have hd : ∀ l, (if base (Fin.castSucc l) s = 0 then 0 else 1) ≤ 1 := fun l => by
    split_ifs <;> simp
  have hsum : ∀ i j : Fin 4, i ≠ j →
      (if base i.castSucc s = 0 then 0 else 1) + (if base j.castSucc s = 0 then 0 else 1) ≤
        loopDegOf base s := by
    intro i j hij
    simp only [loopDegOf, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> split_ifs <;> omega
  unfold vE2
  refine (((((?_ : IsLoopPolyDeg s _ 3 _).add ?_).add ?_).add ?_).add ?_).add ?_
  · exact ((C 0).mul ((C 1).mul ((C 2).mul ((N 2).mul ((C 3).mul (N 3)))))).trace.mono
      (by simpa using hsum 2 3 (by decide)) (by norm_num)
  · exact ((C 0).mul ((C 1).mul ((N 1).mul ((C 2).mul ((C 3).mul (N 3)))))).trace.mono
      (by simpa using hsum 1 3 (by decide)) (by norm_num)
  · exact ((C 0).mul ((C 1).mul ((N 1).mul ((C 2).mul ((N 2).mul (C 3)))))).trace.mono
      (by simpa using hsum 1 2 (by decide)) (by norm_num)
  · exact ((C 0).mul ((N 0).mul ((C 1).mul ((C 2).mul ((C 3).mul (N 3)))))).trace.mono
      (by simpa using hsum 0 3 (by decide)) (by norm_num)
  · exact ((C 0).mul ((N 0).mul ((C 1).mul ((C 2).mul ((N 2).mul (C 3)))))).trace.mono
      (by simpa using hsum 0 2 (by decide)) (by norm_num)
  · exact ((C 0).mul ((N 0).mul ((C 1).mul ((N 1).mul ((C 2).mul (C 3)))))).trace.mono
      (by simpa using hsum 0 1 (by decide)) (by norm_num)

/-- The coefficient of `m²` of a class numerator has degree at most `loopDegOf base s` along
loop `s`. -/
theorem isLoopPolyDeg_vNumE2 (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (s : Fin 2) (k : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPolyDeg s (loopDegOf base s) 3 fun ℓ => vNumE2 e mγ Λ A base c k ℓ a b :=
  IsLoopPolyDeg.sum _ fun ρ _ => IsLoopPolyDeg.sum _ fun σ _ =>
    (isLoopPolyDeg_vE2 base (ppc c k) s (A a b ρ σ)).const_mul _

/-- **The numerator of the seven-line pieces as a cubic of bounded degree along loop `s`**:
`C (vNum X - vNum M)` is a `LoopQuartic` without quartic part whose coefficients with more than
`loopDegOf base s` indices in loop `s` vanish. -/
theorem exists_loopQuartic_vNum_sub_cubic (e mγ Λ : ℝ)
    {A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat} (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (s : Fin 2) (C : ℂ) (m m' : ℝ)
    (k : Fin 4 → ℝ) (a b : Fin 4) :
    ∃ Q : LoopQuartic, Q.quart = 0 ∧ LoopDegLe s (loopDegOf base s) Q ∧
      Q.eval = fun ℓ => C * (vNum e mγ Λ A base c m k ℓ a b - vNum e mγ Λ A base c m' k ℓ a b) := by
  have h : IsLoopPolyDeg s (loopDegOf base s) 3 fun ℓ =>
      C * (vNum e mγ Λ A base c m k ℓ a b - vNum e mγ Λ A base c m' k ℓ a b) := by
    have e1 : (fun ℓ => C * (vNum e mγ Λ A base c m k ℓ a b -
        vNum e mγ Λ A base c m' k ℓ a b)) = fun ℓ =>
          (C * ((m : ℂ) ^ 2 - (m' : ℂ) ^ 2)) * (vNumE2 e mγ Λ A base c k ℓ a b +
            ((m : ℂ) ^ 2 + (m' : ℂ) ^ 2) * vNumE4 e mγ Λ A k a b) := by
      funext ℓ
      rw [vNum_eq e mγ Λ A base c hA, vNum_eq e mγ Λ A base c hA]
      ring
    rw [e1]
    exact ((isLoopPolyDeg_vNumE2 e mγ Λ A base c s k a b).add
      (IsLoopPolyDeg.const _)).const_mul _
  exact exists_loopQuartic_cubic_deg h

end QED.GradedProof.RPi4

end
