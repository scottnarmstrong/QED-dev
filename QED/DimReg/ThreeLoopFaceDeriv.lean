/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopVal3

/-!
# The derivatives of `G^{-d/2}` in `x₇`, `x₈` and their restriction to the face `x₇ = x₈ = 0`

The polynomials `Aⱼ` of `QED.DimReg.ThreeLoop.aPolys` (built by `QED.DimReg.ThreeLoop.derivStep`)
describe the derivatives of `G^{-d/2}`, `G = QED.DimReg.ThreeLoop.lpPoly`:

* `faceDeriv A d = Σⱼ (-d/2)↓ⱼ G^{-d/2-j} Aⱼ`; `faceDeriv_init`: for `A = [1]` it is `G^{-d/2}`;
  `hasDerivAt_faceDeriv`: where `G > 0`, the derivative in `x_b` of `faceDeriv A d` is
  `faceDeriv (derivStep b A) d`. So (by induction on the steps)
  `faceDeriv (aPolys k₇ k₈) d = ∂₇^{k₇} ∂₈^{k₈} G^{-d/2}`;
* `ext7`: a point of the face (`x₇ = x₈ = 0`); `eval_ext7`, `lpPoly_eval_ext7`: on the face the
  polynomials are their face restrictions `QED.DimReg.ThreeLoop.faceZ`, and `G` is `G₇`;
* `aPolys_deg`: every term `c x^α` of `Aⱼ` with `c ≠ 0` has `|α| + k₇ + k₈ ≤ 4j`, since `G` has
  degree `≤ 4`. So the Pochhammer orders `4j - |β| - K` of `QED.DimReg.ThreeLoop.coef3` are
  honest differences.
-/

@[expose] public section

open Complex QED.DimReg QED.DimReg.Sector

namespace QED.DimReg.ThreeLoop

/-! ### The falling factorial -/

/-- The falling factorial `e (e - 1) ⋯ (e - j + 1)`. -/
noncomputable def fallC (e : ℂ) (j : ℕ) : ℂ := ∏ i ∈ Finset.range j, (e - i)

theorem fallC_zero (e : ℂ) : fallC e 0 = 1 := by simp [fallC]

theorem fallC_succ (e : ℂ) (j : ℕ) : fallC e (j + 1) = fallC e j * (e - j) :=
  Finset.prod_range_succ _ _

theorem fallC_neg (s : ℂ) (j : ℕ) : fallC (-s) j = (-1) ^ j * TwoLoopSESector.poch s j := by
  induction j with
  | zero => simp [fallC, TwoLoopSESector.poch]
  | succ j ih =>
    rw [fallC_succ, ih]
    simp only [TwoLoopSESector.poch, Finset.prod_range_succ, pow_succ]
    ring

/-! ### The derivatives of `G^{-d/2}` -/

/-- `Σⱼ (-d/2)↓ⱼ G^{-d/2-j} Aⱼ` at the point `y`. -/
noncomputable def faceDeriv (A : List ZPoly) (d : ℂ) (y : Fin 9 → ℝ) : ℂ :=
  ∑ j ∈ Finset.range A.length, fallC (-(d / 2)) j * ((lpPoly.eval y : ℝ) : ℂ) ^ (-(d / 2) - j) *
    (ZPoly.eval (A.getD j []) y : ℂ)

theorem faceDeriv_init (d : ℂ) (y : Fin 9 → ℝ) :
    faceDeriv [[([], 1)]] d y = ((lpPoly.eval y : ℝ) : ℂ) ^ (-(d / 2)) := by
  simp only [faceDeriv, List.length_singleton, Finset.range_one, Finset.sum_singleton,
    fallC_zero, List.getD_cons_zero, Nat.cast_zero, sub_zero, ZPoly.eval_cons, ZPoly.eval_nil,
    mono_nil, Int.cast_one, mul_one, add_zero, ofReal_one, one_mul]

theorem length_derivStep (b : ℕ) (A : List ZPoly) : (derivStep b A).length = A.length + 1 := by
  simp [derivStep]

theorem eval_getD_derivStep (b : ℕ) (A : List ZPoly) {j : ℕ} (hj : j < A.length + 1)
    (y : Fin 9 → ℝ) : ZPoly.eval ((derivStep b A).getD j []) y =
      ZPoly.eval (ZPoly.diff b (A.getD j [])) y +
        if j = 0 then 0 else ZPoly.eval (A.getD (j - 1) []) y *
          ZPoly.eval (ZPoly.diff b (ZPoly.ofN lpPoly)) y := by
  simp only [derivStep, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, ZPoly.eval_append]
  split_ifs <;> simp [ZPoly.eval_mul]

theorem hasDerivAt_lpPoly (y : Fin 9 → ℝ) (b : Fin 9) :
    HasDerivAt (fun t => lpPoly.eval (Function.update y b t))
      (ZPoly.eval (ZPoly.diff b (ZPoly.ofN lpPoly)) y) (y b) := by
  simpa only [ZPoly.eval_ofN] using ZPoly.hasDerivAt_eval_update (ZPoly.ofN lpPoly) y b

theorem hasDerivAt_cpow_update {Gf : (Fin 9 → ℝ) → ℝ} {g' : ℝ} {y : Fin 9 → ℝ} {b : Fin 9}
    (hd : HasDerivAt (fun t => Gf (Function.update y b t)) g' (y b)) (hy : 0 < Gf y) (c : ℂ) :
    HasDerivAt (fun t => ((Gf (Function.update y b t) : ℝ) : ℂ) ^ c)
      (c * ((Gf y : ℝ) : ℂ) ^ (c - 1) * g') (y b) := by
  have hGs : ((Gf (Function.update y b (y b)) : ℝ) : ℂ) ∈ slitPlane := by
    rw [Function.update_eq_self]; exact ofReal_mem_slitPlane.mpr hy
  have := (Complex.hasStrictDerivAt_cpow_const (c := c) hGs).hasDerivAt.comp (y b)
    (h := fun t => ((Gf (Function.update y b t) : ℝ) : ℂ)) hd.ofReal_comp
  simp only [Function.update_eq_self] at this
  exact this

/-- **One derivative of `Σⱼ (-d/2)↓ⱼ G^{-d/2-j} Aⱼ`** in `x_b`, where `G > 0`, is given by
`derivStep b`. -/
theorem hasDerivAt_faceDeriv (A : List ZPoly) (d : ℂ) {y : Fin 9 → ℝ} (hy : 0 < lpPoly.eval y)
    (b : Fin 9) :
    HasDerivAt (fun t => faceDeriv A d (Function.update y b t)) (faceDeriv (derivStep b A) d y)
      (y b) := by
  set e : ℂ := -(d / 2)
  set G : ℂ := ((lpPoly.eval y : ℝ) : ℂ)
  set g' : ℝ := ZPoly.eval (ZPoly.diff b (ZPoly.ofN lpPoly)) y
  have hGs : G ∈ slitPlane := ofReal_mem_slitPlane.mpr hy
  have hG0 : G ≠ 0 := slitPlane_ne_zero hGs
  have hterm : ∀ j ∈ Finset.range A.length, HasDerivAt (fun t => fallC e j *
      ((lpPoly.eval (Function.update y b t) : ℝ) : ℂ) ^ (e - j) *
        (ZPoly.eval (A.getD j []) (Function.update y b t) : ℂ))
      (fallC e j * ((e - j) * G ^ (e - j - 1) * g' * (ZPoly.eval (A.getD j []) y : ℂ) +
        G ^ (e - j) * (ZPoly.eval (ZPoly.diff b (A.getD j [])) y : ℂ))) (y b) := by
    intro j _
    have hB := hasDerivAt_cpow_update (Gf := fun z => lpPoly.eval z) (hasDerivAt_lpPoly y b) hy
      (e - j)
    have hA := (ZPoly.hasDerivAt_eval_update (A.getD j []) y b).ofReal_comp
    have := (hB.fun_mul hA).const_mul (fallC e j)
    convert this using 1
    · funext t; ring
    · simp only [Function.update_eq_self, G, g']
  have hsum := HasDerivAt.fun_sum hterm
  unfold faceDeriv
  convert hsum using 1
  rw [length_derivStep]
  have hA : ∀ j ∈ Finset.range (A.length + 1), fallC e j * G ^ (e - j) *
      (ZPoly.eval ((derivStep b A).getD j []) y : ℂ) =
      fallC e j * G ^ (e - j) * (ZPoly.eval (ZPoly.diff b (A.getD j [])) y : ℂ) +
        if j = 0 then 0 else fallC e j * G ^ (e - j) *
          ((ZPoly.eval (A.getD (j - 1) []) y : ℂ) * g') := by
    intro j hj
    rw [eval_getD_derivStep b A (Finset.mem_range.mp hj)]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hA, Finset.sum_add_distrib, Finset.sum_range_succ,
    Finset.sum_range_succ']
  have hlast : A.getD A.length [] = [] := by simp
  simp only [hlast, ZPoly.diff, List.map_nil, ZPoly.eval_nil, ofReal_zero, mul_zero, add_zero,
    ite_true, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpow : G ^ (e - ((j + 1 : ℕ) : ℂ)) = G ^ (e - j - 1) := by
    congr 1; push_cast; ring
  rw [fallC_succ, hpow]
  ring

/-! ### The face `x₇ = x₈ = 0` -/

/-- The point `(x, 0, 0)` of the face `x₇ = x₈ = 0`. -/
def ext7 (x : Fin 7 → ℝ) : Fin 9 → ℝ := fun i => if h : (i : ℕ) < 7 then x ⟨i, h⟩ else 0

theorem getD_take_of_lt (α : List ℕ) {k m : ℕ} (hk : k < m) :
    (α.take m).getD k 0 = α.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem mono_ext7 (α : List ℕ) (x : Fin 7 → ℝ) :
    mono α (ext7 x) =
      if α.getD 7 0 = 0 ∧ α.getD 8 0 = 0 then mono (α.take 7) x else 0 := by
  rw [mono, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [ext7, Fin.val_castSucc, Fin.val_last, Fin.is_lt, dite_eq_left, lt_self_iff_false,
    dite_eq_right, not_false_eq_true, show ¬ (8 < 7) by omega, Fin.eta]
  have hp : ∏ i : Fin 7, x i ^ α.getD i 0 = mono (α.take 7) x :=
    Finset.prod_congr rfl fun i _ => by rw [getD_take_of_lt α i.isLt]
  rw [hp]
  split_ifs with h
  · rw [h.1, h.2]; simp
  · rcases not_and_or.mp h with a | a
    · rw [zero_pow a]; simp
    · rw [zero_pow a]; simp

/-- **On the face a polynomial is its face restriction.** -/
theorem eval_ext7 (P : ZPoly) (x : Fin 7 → ℝ) :
    ZPoly.eval P (ext7 x) = ZPoly.eval (faceZ P) x := by
  induction P with
  | nil => rfl
  | cons t P ih =>
    have hf : faceZ (t :: P) = if (t.1.getD 7 0 == 0 && t.1.getD 8 0 == 0) then
        (t.1.take 7, t.2) :: faceZ P else faceZ P := by
      unfold faceZ; rw [List.filter_cons]; split <;> rfl
    rw [hf, ZPoly.eval_cons, mono_ext7, ih]
    by_cases h : t.1.getD 7 0 = 0 ∧ t.1.getD 8 0 = 0
    · have hb : (t.1.getD 7 0 == 0 && t.1.getD 8 0 == 0) = true := by simp only [h.1, h.2]; rfl
      rw [hb]
      simp only [h, and_self, ↓reduceIte, ZPoly.eval_cons]
    · have hb : (t.1.getD 7 0 == 0 && t.1.getD 8 0 == 0) = false := by simpa using h
      rw [hb]
      simp only [h, ↓reduceIte, mul_zero, zero_add, Bool.false_eq_true]

theorem faceZ_ofN (P : NPoly) : faceZ (ZPoly.ofN P) = ZPoly.ofN (faceRestrict P) := by
  simp [faceZ, faceRestrict, ZPoly.ofN, List.filter_map, Function.comp_def]

/-- **On the face `G` is `G₇`.** -/
theorem lpPoly_eval_ext7 (x : Fin 7 → ℝ) : lpPoly.eval (ext7 x) = g7.eval x := by
  rw [← ZPoly.eval_ofN, eval_ext7, ← ZPoly.eval_ofN, g7, faceZ_ofN, lpPoly_eq_lit]

/-! ### The degree bound -/

theorem sum_addExp : ∀ a b : List ℕ, (addExp a b).sum = a.sum + b.sum
  | [], b => by simp [addExp]
  | a :: as, [] => by simp [addExp]
  | a :: as, b :: bs => by simp [addExp, sum_addExp as bs]; ring

theorem subExp_nil : ∀ a : List ℕ, subExp a [] = a
  | [] => rfl
  | _ :: _ => rfl

theorem sum_subExp_unit : ∀ (b : ℕ) (a : List ℕ), 1 ≤ a.getD b 0 →
    (subExp a (unitExp b)).sum + 1 = a.sum
  | _, [], h => by simp at h
  | 0, x :: as, h => by
    simp only [unitExp, addAt, subExp, subExp_nil, List.sum_cons] at h ⊢
    simp at h; omega
  | b + 1, x :: as, h => by
    have := sum_subExp_unit b as (by simpa using h)
    simp only [unitExp, addAt] at this ⊢
    simp only [subExp, List.sum_cons]
    omega

/-- Every term `c x^α` of the `j`-th polynomial with `c ≠ 0` has `|α| + K ≤ 4j`. -/
def DegOk (K : ℕ) (A : List ZPoly) : Prop :=
  ∀ j, ∀ t ∈ A.getD j [], t.2 ≠ 0 → t.1.sum + K ≤ 4 * j

theorem lpPolyLit_deg : ∀ t ∈ lpPolyLit, t.1.sum ≤ 4 := by decide +kernel

theorem diff_deg {P : ZPoly} {b : ℕ} {B : ℕ} (hP : ∀ t ∈ P, t.2 ≠ 0 → t.1.sum ≤ B) :
    ∀ t ∈ ZPoly.diff b P, t.2 ≠ 0 → t.1.sum + 1 ≤ B := by
  intro t ht h0
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have h1 : s.2 ≠ 0 := fun h => h0 (by show s.2 * _ = 0; rw [h]; simp)
  have h2 : 1 ≤ s.1.getD b 0 := by
    by_contra hc
    have hz : s.1.getD b 0 = 0 := by omega
    exact h0 (by show s.2 * _ = 0; rw [hz]; simp)
  have := sum_subExp_unit b s.1 h2
  have := hP s hs h1
  simp only at *
  omega

theorem dG_deg {b : ℕ} : ∀ t ∈ ZPoly.diff b (ZPoly.ofN lpPoly), t.2 ≠ 0 → t.1.sum + 1 ≤ 4 := by
  refine diff_deg fun t ht _ => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact lpPolyLit_deg s (lpPoly_eq_lit ▸ hs)

theorem mul_deg {P Q : ZPoly} {B C : ℕ} (hP : ∀ t ∈ P, t.2 ≠ 0 → t.1.sum ≤ B)
    (hQ : ∀ t ∈ Q, t.2 ≠ 0 → t.1.sum ≤ C) : ∀ t ∈ ZPoly.mul P Q, t.2 ≠ 0 → t.1.sum ≤ B + C := by
  intro t ht h0
  obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  simp only [ne_eq, mul_eq_zero, not_or] at h0
  rw [sum_addExp]
  exact Nat.add_le_add (hP s hs h0.1) (hQ u hu h0.2)

theorem derivStep_deg {K : ℕ} {A : List ZPoly} (hA : DegOk K A) (b : ℕ) :
    DegOk (K + 1) (derivStep b A) := by
  intro j t ht h0
  by_cases hj : j < A.length + 1
  · simp only [derivStep, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hj, Option.map_some, Option.getD_some, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h1 : s.2 ≠ 0 := fun h => h0 (by show s.2 * _ = 0; rw [h]; simp)
      have := hA j s (by simpa [List.getD_eq_getElem?_getD] using hs) h1
      have h2 : 1 ≤ s.1.getD b 0 := by
        by_contra hc
        have hz : s.1.getD b 0 = 0 := by omega
        exact h0 (by show s.2 * _ = 0; rw [hz]; simp)
      have := sum_subExp_unit b s.1 h2
      simp only at *
      omega
    · split_ifs at ht with hj0
      · simp at ht
      · obtain ⟨s, hs, ht'⟩ := List.mem_flatMap.mp ht
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht'
        simp only [ne_eq, mul_eq_zero, not_or] at h0
        have := hA (j - 1) s (by simpa [List.getD_eq_getElem?_getD] using hs) h0.1
        have := dG_deg (b := b) u hu h0.2
        rw [sum_addExp]
        omega
  · simp [List.getD_eq_getElem?_getD, length_derivStep, hj] at ht

theorem iterate_derivStep_deg (b : ℕ) : ∀ (k K : ℕ) (A : List ZPoly), DegOk K A →
    DegOk (K + k) ((derivStep b)^[k] A)
  | 0, _, _, h => h
  | k + 1, K, A, h => by
    rw [Function.iterate_succ_apply]
    have := iterate_derivStep_deg b k (K + 1) _ (derivStep_deg h b)
    rwa [show K + 1 + k = K + (k + 1) by ring] at this

/-- **The degree bound**: every term `c x^α` of `Aⱼ` (for `aPolys k₇ k₈`) with `c ≠ 0` has
`|α| + k₇ + k₈ ≤ 4j`. -/
theorem aPolys_deg (k₇ k₈ : ℕ) : DegOk (k₇ + k₈) (aPolys k₇ k₈) := by
  have h0 : DegOk 0 [[([], 1)]] := by
    intro j t ht _
    rcases j with _ | j
    · simp at ht; simp [ht]
    · simp at ht
  have := iterate_derivStep_deg 8 k₈ _ _ (by simpa using iterate_derivStep_deg 7 k₇ 0 _ h0)
  exact this

theorem length_aPolys (k₇ k₈ : ℕ) : (aPolys k₇ k₈).length = k₇ + k₈ + 1 := by
  have h : ∀ b k (A : List ZPoly), ((derivStep b)^[k] A).length = A.length + k := by
    intro b k
    induction k with
    | zero => simp
    | succ k ih => intro A; rw [Function.iterate_succ_apply, ih, length_derivStep]; ring
  simp only [aPolys, h]
  simp; ring

end QED.DimReg.ThreeLoop
