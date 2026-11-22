/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceConv

/-!
# The last integration to the face: commuting derivatives and the boundary value

Two ingredients of the face theorem at `(ν₇, ν₈) = (-k₇, -k₈)`:

* the order of the derivatives does not matter: `derivStep 8` and `derivStep 7` commute up to
  evaluation (`evalEq_derivStep_comm`, from `∂₇∂₈ = ∂₈∂₇` on the exponents and the product
  rule), so `∂₈^k ∂₇ G^{-d/2} = ∂₇ ∂₈^k G^{-d/2}` (`faceDeriv_iterate_comm`);
* **the boundary value** (`integral_posOrthant_deriv_last`): if `Φ` and its derivative `Φ'` in
  the last coordinate (on `t ≥ 0`) are integrable on the open orthant, then the boundary
  value `w ↦ Φ(w, 0)` is integrable and `∫_{(0,∞)^{n+1}} Φ' = -∫_{(0,∞)^n} Φ(w, 0) dw`
  (Fubini, `∫₀^∞ f' = -f(0)` with `f → 0` at infinity since `f, f'` are integrable).
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory QED.DimReg QED.DimReg.Sector

namespace QED.DimReg.ThreeLoop

/-! ### Derivatives of polynomials up to evaluation -/

theorem eval_diff_congr {P Q : ZPoly} (h : ∀ y : Fin 9 → ℝ, ZPoly.eval P y = ZPoly.eval Q y)
    (b : Fin 9) (y : Fin 9 → ℝ) :
    ZPoly.eval (ZPoly.diff b P) y = ZPoly.eval (ZPoly.diff b Q) y := by
  have hP := ZPoly.hasDerivAt_eval_update P y b
  have hQ := ZPoly.hasDerivAt_eval_update Q y b
  simp only [h] at hP
  exact hP.unique hQ

theorem eval_diff_mul (P Q : ZPoly) (b : Fin 9) (y : Fin 9 → ℝ) :
    ZPoly.eval (ZPoly.diff b (ZPoly.mul P Q)) y =
      ZPoly.eval (ZPoly.diff b P) y * ZPoly.eval Q y +
        ZPoly.eval P y * ZPoly.eval (ZPoly.diff b Q) y := by
  have h := ZPoly.hasDerivAt_eval_update (ZPoly.mul P Q) y b
  have hP := ZPoly.hasDerivAt_eval_update P y b
  have hQ := ZPoly.hasDerivAt_eval_update Q y b
  simp only [ZPoly.eval_mul] at h
  exact h.unique ((hP.mul hQ).congr_deriv (by rw [Function.update_eq_self]))

theorem eval_diff_append (P Q : ZPoly) (b : ℕ) (y : Fin 9 → ℝ) :
    ZPoly.eval (ZPoly.diff b (P ++ Q)) y =
      ZPoly.eval (ZPoly.diff b P) y + ZPoly.eval (ZPoly.diff b Q) y := by
  rw [ZPoly.diff, List.map_append, ZPoly.eval_append]
  rfl

/-- **Second derivatives commute** on the exponents. -/
theorem eval_diff_comm (P : ZPoly) (a b : ℕ) (y : Fin 9 → ℝ) :
    ZPoly.eval (ZPoly.diff a (ZPoly.diff b P)) y =
      ZPoly.eval (ZPoly.diff b (ZPoly.diff a P)) y := by
  induction P with
  | nil => rfl
  | cons t P ih =>
    simp only [ZPoly.diff, List.map_cons, ZPoly.eval_cons] at ih ⊢
    rw [ih]
    congr 1
    have hm : mono (subExp (subExp t.1 (unitExp b)) (unitExp a)) y =
        mono (subExp (subExp t.1 (unitExp a)) (unitExp b)) y := by
      unfold mono
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [getD_subExp]
      rw [Nat.sub_right_comm]
    rw [hm]
    congr 1
    simp only [getD_subExp, ZPoly.getD_unitExp]
    by_cases hab : a = b
    · subst hab; rfl
    · simp only [hab, Ne.symm hab, ite_false, Nat.sub_zero]
      push_cast; ring

/-! ### Lists of polynomials up to evaluation -/

/-- Two lists of polynomials of the same length with the same evaluations. -/
def EvalEq (A B : List ZPoly) : Prop :=
  A.length = B.length ∧ ∀ j (y : Fin 9 → ℝ), ZPoly.eval (A.getD j []) y = ZPoly.eval (B.getD j []) y

theorem EvalEq.refl (A : List ZPoly) : EvalEq A A := ⟨rfl, fun _ _ => rfl⟩

theorem EvalEq.trans {A B C : List ZPoly} (h1 : EvalEq A B) (h2 : EvalEq B C) : EvalEq A C :=
  ⟨h1.1.trans h2.1, fun j y => (h1.2 j y).trans (h2.2 j y)⟩

theorem faceDeriv_congr {A B : List ZPoly} (h : EvalEq A B) (d : ℂ) :
    faceDeriv A d = faceDeriv B d := by
  funext y
  simp only [faceDeriv, h.1, h.2]

/-- The components of `derivStep`, up to evaluation, at every index. -/
theorem eval_getD_derivStep' (b : ℕ) (A : List ZPoly) (j : ℕ) (y : Fin 9 → ℝ) :
    ZPoly.eval ((derivStep b A).getD j []) y =
      ZPoly.eval (ZPoly.diff b (A.getD j []) ++
        if j = 0 then [] else
          ZPoly.mul (A.getD (j - 1) []) (ZPoly.diff b (ZPoly.ofN lpPoly))) y := by
  by_cases hj : j < A.length + 1
  · rw [eval_getD_derivStep b A hj, ZPoly.eval_append]
    split_ifs <;> simp [ZPoly.eval_mul]
  · have h1 : (derivStep b A).getD j [] = [] := by
      simp [List.getD_eq_getElem?_getD, length_derivStep, hj]
    have h2 : A.getD j [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h3 : A.getD (j - 1) [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [h1, h2, h3]
    split_ifs <;> rfl

theorem EvalEq.derivStep {A B : List ZPoly} (h : EvalEq A B) (b : Fin 9) :
    EvalEq (derivStep b A) (derivStep b B) := by
  refine ⟨by simp [length_derivStep, h.1], fun j y => ?_⟩
  rw [eval_getD_derivStep', eval_getD_derivStep', ZPoly.eval_append, ZPoly.eval_append,
    eval_diff_congr (h.2 j) b y]
  split_ifs
  · rfl
  · simp only [ZPoly.eval_mul, h.2 (j - 1) y]

/-- **`derivStep 8` and `derivStep 7` commute** up to evaluation. -/
theorem evalEq_derivStep_comm (A : List ZPoly) :
    EvalEq (derivStep 8 (derivStep 7 A)) (derivStep 7 (derivStep 8 A)) := by
  refine ⟨by simp [length_derivStep], fun j y => ?_⟩
  set G := ZPoly.ofN lpPoly
  have key : ∀ (a c : Fin 9), ZPoly.eval ((derivStep a (derivStep c A)).getD j []) y =
      ZPoly.eval (ZPoly.diff a (ZPoly.diff c (A.getD j []))) y +
        (if j = 0 then 0 else
          ZPoly.eval (ZPoly.diff a (A.getD (j - 1) [])) y * ZPoly.eval (ZPoly.diff c G) y +
          ZPoly.eval (A.getD (j - 1) []) y * ZPoly.eval (ZPoly.diff a (ZPoly.diff c G)) y +
          ZPoly.eval (ZPoly.diff c (A.getD (j - 1) [])) y * ZPoly.eval (ZPoly.diff a G) y +
          (if j - 1 = 0 then 0 else
            ZPoly.eval (A.getD (j - 1 - 1) []) y * ZPoly.eval (ZPoly.diff c G) y *
              ZPoly.eval (ZPoly.diff a G) y)) := by
    intro a c
    rw [eval_getD_derivStep', ZPoly.eval_append,
      eval_diff_congr (fun y => eval_getD_derivStep' c A j y) a y, eval_diff_append]
    split_ifs with h0 h1
    · simp [ZPoly.diff]
    · rw [eval_diff_mul, ZPoly.eval_mul, eval_getD_derivStep', ZPoly.eval_append]
      simp only [h1, ite_true, ZPoly.eval_nil, add_zero]
      ring
    · rw [eval_diff_mul, ZPoly.eval_mul, eval_getD_derivStep', ZPoly.eval_append]
      simp only [h1, ite_false, ZPoly.eval_mul]
      ring
  have k1 := key 8 7
  have k2 := key 7 8
  rw [show ((8 : Fin 9) : ℕ) = 8 from rfl, show ((7 : Fin 9) : ℕ) = 7 from rfl] at k1 k2
  rw [k1, k2, eval_diff_comm (A.getD j []) 8 7, eval_diff_comm G 8 7]
  split_ifs <;> ring

/-- **`∂₈^k ∂₇ = ∂₇ ∂₈^k`** on the derivative polynomials. -/
theorem evalEq_iterate_comm (A : List ZPoly) :
    ∀ k : ℕ, EvalEq ((derivStep 8)^[k] (derivStep 7 A)) (derivStep 7 ((derivStep 8)^[k] A))
  | 0 => EvalEq.refl _
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ((evalEq_iterate_comm A k).derivStep 8).trans (evalEq_derivStep_comm _)

theorem faceDeriv_iterate_comm (A : List ZPoly) (k : ℕ) (d : ℂ) :
    faceDeriv ((derivStep 8)^[k] (derivStep 7 A)) d =
      faceDeriv (derivStep 7 ((derivStep 8)^[k] A)) d :=
  faceDeriv_congr (evalEq_iterate_comm A k) d

/-! ### The boundary value in the last coordinate -/

/-- **The boundary value.** If `Φ` has derivative `Φ'` in the last coordinate at every point
`(w, t)` with `w` in the open orthant and `t ≥ 0`, and `Φ`, `Φ'` are integrable on the open
orthant, then `w ↦ Φ(w, 0)` is integrable and `∫ Φ' = -∫ Φ(w, 0) dw`. -/
theorem integral_posOrthant_deriv_last {n : ℕ} {Φ Φ' : (Fin (n + 1) → ℝ) → ℂ}
    (hd : ∀ w ∈ posOrthant n, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => Φ (Fin.snoc w s)) (Φ' (Fin.snoc w t)) t)
    (hΦ : IntegrableOn Φ (posOrthant (n + 1))) (hΦ' : IntegrableOn Φ' (posOrthant (n + 1))) :
    IntegrableOn (fun w => Φ (Fin.snoc w 0)) (posOrthant n) ∧
      ∫ x in posOrthant (n + 1), Φ' x = -∫ w in posOrthant n, Φ (Fin.snoc w 0) := by
  rw [integrableOn_posOrthant_snoc] at hΦ hΦ'
  unfold IntegrableOn at hΦ hΦ'
  rw [← Measure.prod_restrict] at hΦ hΦ'
  -- the fibrewise identity
  have hae : ∀ᵐ w ∂(volume.restrict (posOrthant n)),
      ∫ t in Ioi (0 : ℝ), Φ' (Fin.snoc w t) = -Φ (Fin.snoc w 0) := by
    filter_upwards [hΦ.prod_left_ae, hΦ'.prod_left_ae,
      ae_restrict_mem (measurableSet_posOrthant n)] with w h1 h2 hw
    have hder : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun s => Φ (Fin.snoc w s)) (Φ' (Fin.snoc w t)) t :=
      fun t ht => hd w hw t (le_of_lt ht)
    have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hder h2 h1
    rw [integral_Ioi_of_hasDerivAt_of_tendsto
      (hd w hw 0 le_rfl).continuousAt.continuousWithinAt hder h2 hlim, zero_sub]
  have hint := hΦ'.integral_prod_right
  refine ⟨?_, ?_⟩
  · refine (hint.neg.congr ?_ : Integrable _ _)
    filter_upwards [hae] with w hw
    simp only [Pi.neg_apply, hw, neg_neg]
  · rw [setIntegral_posOrthant_snoc, ← Measure.prod_restrict, integral_prod_symm _ hΦ',
      ← integral_neg]
    exact integral_congr_ae hae

end QED.DimReg.ThreeLoop
