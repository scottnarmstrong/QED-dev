/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealSharp
public import QED.GradedProof.SE2ParamPiece

/-!
# Reality of parametric `ε → 0⁺` limits

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`.

Where `V ≥ c > 0` on the simplex, the `ε → 0⁺` limit of a two-loop joint integral with a quartic
numerator `Q` is the parametric value `-π⁴ ∫_Δ paramIntegrand Q α q M 0`
(`QED.GradedProof.SE2.SEData.tendsto_pv`). At `ε = 0` the parametric integrand is built from the
real Symanzik data `U`, `V`, `A⁻¹` and the real shift, and is linear in the coefficients of `Q`
with real kernel. So conjugating the coefficients conjugates the value:

* `qconj`: the coefficientwise complex conjugate of a quartic, `(qconj Q)(ℓ) = conj (Q ℓ)` for
  real `ℓ` (`eval_qconj`);
* `paramIntegrand_qconj`, `pv_qconj`: `pv (qconj Q) = conj (pv Q)`;
* `pv_conj_of_eval`: any admissible quartic with the values `conj (Q ℓ)` has the value
  `conj (pv Q)` (so the limit of a real numerator is real);
* `SEPiece.sharp_W`: if the matrix numerator of a self-energy piece satisfies `N_p(ℓ)♯ = c N_p(ℓ)`
  for real `ℓ` (`QED.GradedProof.SE2Real.sharp`), its limit matrix satisfies `W(p)♯ = c W(p)` on
  the region.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Matrix
open scoped Real

namespace QED.GradedProof.SE2Real

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.GradedProof.SE2

/-- **The coefficientwise complex conjugate of a quartic.** -/
def qconj (Q : LoopQuartic) : LoopQuartic where
  const := starRingEnd ℂ Q.const
  lin a := starRingEnd ℂ (Q.lin a)
  quad a b := starRingEnd ℂ (Q.quad a b)
  cub a b c := starRingEnd ℂ (Q.cub a b c)
  quart a b c d := starRingEnd ℂ (Q.quart a b c d)

variable (Q : LoopQuartic)

theorem evalC_qconj {X : LoopIndex → ℂ} (hX : ∀ a, starRingEnd ℂ (X a) = X a) :
    (qconj Q).evalC X = starRingEnd ℂ (Q.evalC X) := by
  simp only [LoopQuartic.evalC, qconj, map_add, map_sum, map_mul, hX]

theorem conj_loopComp (ℓ : Fin 2 → Fin 4 → ℝ) (a : LoopIndex) :
    starRingEnd ℂ (loopComp ℓ a) = loopComp ℓ a := by
  simp [loopComp]

theorem eval_qconj (ℓ : Fin 2 → Fin 4 → ℝ) : (qconj Q).eval ℓ = starRingEnd ℂ (Q.eval ℓ) :=
  evalC_qconj Q (conj_loopComp ℓ)

theorem hess_qconj {X : LoopIndex → ℂ} (hX : ∀ a, starRingEnd ℂ (X a) = X a) (a b : LoopIndex) :
    (qconj Q).hess X a b = starRingEnd ℂ (Q.hess X a b) := by
  simp only [LoopQuartic.hess, LoopQuartic.quartSym, qconj, map_add, map_sum, map_mul, hX]

theorem contractTwo_qconj (A : Matrix (Fin 2) (Fin 2) ℝ) {X : LoopIndex → ℂ}
    (hX : ∀ a, starRingEnd ℂ (X a) = X a) :
    (qconj Q).contractTwo A X = starRingEnd ℂ (Q.contractTwo A X) := by
  simp only [LoopQuartic.contractTwo, hess_qconj Q hX, map_sum, map_mul, Complex.conj_ofReal]

theorem contractFour_qconj (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (qconj Q).contractFour A = starRingEnd ℂ (Q.contractFour A) := by
  simp only [LoopQuartic.contractFour, qconj, map_sum, map_mul, Complex.conj_ofReal]

/-- **At `ε = 0` the parametric integrand commutes with conjugation of the coefficients.** -/
theorem paramIntegrand_qconj {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ) :
    paramIntegrand (qconj Q) α p M 0 x = starRingEnd ℂ (paramIntegrand Q α p M 0 x) := by
  have h1 : (qconj Q).eval (-loopShift α p (simplexPoint x)) =
      starRingEnd ℂ (Q.eval (-loopShift α p (simplexPoint x))) := eval_qconj Q _
  have h2 := contractTwo_qconj Q (symanzikMatrix α (simplexPoint x))
    (conj_loopComp (-loopShift α p (simplexPoint x)))
  have h3 := contractFour_qconj Q (symanzikMatrix α (simplexPoint x))
  simp only [paramIntegrand, h1, h2, h3, map_add, map_mul, map_inv₀, map_pow,
    Complex.conj_ofReal, map_natCast, map_div₀, Complex.ofReal_zero, zero_mul, sub_zero, map_ofNat]

variable {D : SEData}

/-- **`pv (qconj Q) = conj (pv Q)`.** -/
theorem pv_qconj (Q : LoopQuartic) (q : Fin (D.m + 1) → Fin 4 → ℝ) :
    D.pv (qconj Q) q = starRingEnd ℂ (D.pv Q q) := by
  simp only [SEData.pv, paramIntegrand_qconj, integral_conj, map_mul, map_neg, map_pow,
    Complex.conj_ofReal]

theorem good_qconj {Q : LoopQuartic} (hQ : D.Good Q) : D.Good (qconj Q) := by
  refine ⟨hQ.1.imp id fun h => ?_, ?_⟩
  · funext a b c d
    simp [qconj, h]
  · obtain ⟨C, hC, hb⟩ := hQ.2
    exact ⟨C, hC, fun A hA ℓ => by rw [eval_qconj, Complex.norm_conj]; exact hb A hA ℓ⟩

/-- **The value of a quartic with conjugate values is the conjugate value.** -/
theorem pv_conj_of_eval {Q Q' : LoopQuartic} (hQ : D.Good Q) (hQ' : D.Good Q')
    (he : Q'.eval = fun ℓ => starRingEnd ℂ (Q.eval ℓ)) {q : Fin (D.m + 1) → Fin 4 → ℝ}
    (hV : D.VPos q) : D.pv Q' q = starRingEnd ℂ (D.pv Q q) := by
  rw [← pv_qconj]
  exact SE2.SEData.pv_unique hQ' (good_qconj hQ) (by rw [he]; funext ℓ; rw [eval_qconj]) hV

namespace SEPiece

variable {T : ℝ} (P : SEPiece T)

/-- **The limit matrix inherits the `♯`-symmetry of the numerator.** -/
theorem sharp_W {c : ℂ} (hN : ∀ p ℓ, sharp (P.N p ℓ) = c • P.N p ℓ) {p : Fin 4 → ℝ}
    (hp : -T ^ 2 < Minkowski.dot p p) : sharp (P.W p) = c • P.W p := by
  classical
  ext i j
  set Qc : Fin 4 × Fin 4 → LoopQuartic := fun kl => qconj (P.quartic p kl.1 kl.2)
  set w : Fin 4 × Fin 4 → ℂ := fun kl => -(cMat i kl.1 * cMat kl.2 j)
  set Qs := qsum Finset.univ w Qc
  have hI : ∀ kl ∈ (Finset.univ : Finset (Fin 4 × Fin 4)),
      IntegrableOn (paramIntegrand (Qc kl) P.D.α (P.D.mom p) P.D.M 0) (simplexSet P.D.m) :=
    fun kl _ => SEData.integrableOn_pv (good_qconj (P.good_quartic p kl.1 kl.2))
      (P.hV p hp)
  have hev : Qs.eval = fun ℓ => c * P.N p ℓ i j := by
    funext ℓ
    have h := congrFun (congrFun (hN p ℓ) i) j
    rw [Matrix.smul_apply, smul_eq_mul] at h
    rw [← h, eval_qsum]
    simp only [Qc, w, eval_qconj, P.eval_quartic, sharp, Matrix.neg_apply, Matrix.mul_apply,
      Matrix.map_apply, Finset.sum_mul, Fintype.sum_prod_type, neg_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine congrArg Neg.neg
      (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
  have hc : P.D.Good (qsum Finset.univ (fun _ : Unit => c) fun _ => P.quartic p i j) := by
    refine ⟨?_, ?_⟩
    · rcases (P.good_quartic p i j).1 with h7 | hq
      · exact Or.inl h7
      · exact Or.inr (SEData.quart_qsum _ _ _ fun _ _ => hq)
    · have hb := (P.good_quartic p i j).2.const_mul c
      have he : (qsum Finset.univ (fun _ : Unit => c) fun _ => P.quartic p i j).eval =
          fun ℓ => c * (P.quartic p i j).eval ℓ := by
        funext ℓ
        rw [eval_qsum]
        simp
      rw [he]
      exact hb
  have hgood : P.D.Good Qs := by
    refine ⟨?_, ?_⟩
    · rcases Nat.lt_or_ge P.D.m 7 with h7 | h7
      · refine Or.inr (SEData.quart_qsum _ _ _ fun kl _ => ?_)
        rcases (good_qconj (P.good_quartic p kl.1 kl.2)).1 with h' | h'
        · omega
        · exact h'
      · exact Or.inl h7
    · have he : (qsum Finset.univ (fun _ : Unit => c) fun _ => P.quartic p i j).eval =
          Qs.eval := by
        rw [hev]
        funext ℓ
        rw [eval_qsum, P.eval_quartic]
        simp
      rw [← he]
      exact hc.2
  have hcv : (qsum Finset.univ (fun _ : Unit => c) fun _ => P.quartic p i j).eval = Qs.eval := by
    rw [hev]
    funext ℓ
    rw [eval_qsum, P.eval_quartic]
    simp
  have key := SEData.pv_unique hc hgood hcv (P.hV p hp)
  have hI' : ∀ u ∈ (Finset.univ : Finset Unit), IntegrableOn
      (paramIntegrand (P.quartic p i j) P.D.α (P.D.mom p) P.D.M 0) (simplexSet P.D.m) :=
    fun _ _ => SEData.integrableOn_pv (P.good_quartic p i j) (P.hV p hp)
  rw [SEData.pv_qsum _ _ _ hI', SEData.pv_qsum _ _ _ hI] at key
  simp only [Finset.univ_unique, Finset.sum_singleton] at key
  rw [Matrix.smul_apply, smul_eq_mul]
  simp only [SEPiece.W, Matrix.of_apply] at key ⊢
  rw [key]
  simp only [sharp, Matrix.neg_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
    Finset.sum_mul, Fintype.sum_prod_type, neg_mul, Finset.sum_neg_distrib, Qc, w, pv_qconj]
  rw [Finset.sum_comm]
  refine congrArg Neg.neg
    (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)

end SEPiece

end QED.GradedProof.SE2Real

end
