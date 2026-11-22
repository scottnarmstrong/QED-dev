/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopAnn

/-!
# The twelve IBP templates of set (d) for convergent Lee–Pomeransky integrals

Let `J(ν, d) = ∫_{(0,∞)^9} x^{ν-1} G^{-d/2}` be the Lee–Pomeransky integral of the set (d)
family and `N(ν, d) = Γ(d/2) / (Γ(2d - |ν|) ∏_a Γ(ν_a))` its normalization (`normLP`). At a
point where all integrals involved converge, the normalized integrals `N J` satisfy every
template relation `QED.Algebra.IBPCert.Family.template i j` of
`QED.ThreeLoopD.SetDCert.lbl` (`tmpl_lp`).

The proof multiplies the annihilator relation of `QED.DimReg.lpIntegral_annihilator`, with the
data `QED.DimReg.ThreeLoop.pT`, `QED.DimReg.ThreeLoop.qT` of `QED.DimReg.ThreeLoopAnn`, by
`N(ν, d)`:

* every template term is `c ν_a I(ν + e_a - e_b)`, `c ν_a I(ν + e_a)` or `2d I(ν)`
  (`mem_template`), and `ν_a N(ν + e_a - e_b) = (ν_b - 1) N(ν)`,
  `ν_a N(ν + e_a) = (2d - |ν| - 1) N(ν)` (`normLP_raise_lower`, `normLP_raise`), so the template
  is `N(ν)/2` times a combination of the `J(ν + σ)` with coefficients affine in `(ν, d)`
  (`tmplSum_eq`);
* the annihilator relation is a combination of the same kind (`lcEval_annLC`);
* the two combinations agree term by term, which the kernel checks (`tmplCheck_all`) with the
  label merging of `QED.Algebra.IBPCert.LinComb`: the labels are the shifts `σ` preceded by the
  index of the variable (`ν_k` for `k < 9`, `d` for `9`, `1` for `10`).
-/

@[expose] public section

open Complex MeasureTheory QED.DimReg QED.DimReg.Sector QED.Algebra.IBPCert
open QED.ThreeLoopD.SetDCert
open QED.DimReg.ZPoly (annField toML annProd)

namespace QED.DimReg.ThreeLoop

/-! ### Template coefficients, shifts and the normalization -/

/-- The shift of an index list, as a complex vector. -/
def shC (σ : List ℤ) : Fin 9 → ℂ := fun i => ((σ.getD i 0 : ℤ) : ℂ)

/-- The coefficient `c₀ + c_d d + c_ν ν_idx` of a template term at complex `(d, ν)`. -/
def tcoef (t : Term) (d : ℂ) (ν : Fin 9 → ℂ) : ℂ :=
  t.c0 + t.cd * d + t.cnu * (if h : t.idx < 9 then ν ⟨t.idx, h⟩ else 0)

/-- The Lee–Pomeransky normalization `Γ(d/2) / (Γ(2d - |ν|) ∏_a Γ(ν_a))` of the set (d) family. -/
noncomputable def normLP (ν : Fin 9 → ℂ) (d : ℂ) : ℂ :=
  Gamma (d / 2) * (Gamma (2 * d - ∑ a, ν a))⁻¹ * ∏ a, (Gamma (ν a))⁻¹

theorem shC_nil : shC [] = 0 := by funext i; simp [shC]

theorem getD_range_map_int (f : ℕ → ℤ) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem shC_replicate : shC (List.replicate 9 0) = 0 := by
  funext i
  fin_cases i <;> simp [shC]

theorem shC_shiftVec (a b : ℕ) (i : Fin 9) :
    shC (Family.shiftVec 9 a b) i =
      (if (i : ℕ) = a then 1 else 0) - (if (i : ℕ) = b then 1 else 0) := by
  simp only [shC, Family.shiftVec, getD_range_map_int _ i.isLt, Bool.cond_eq_ite, Nat.beq_eq]
  split_ifs <;> simp

/-- The shape of the template terms: `2d I(ν)` (the term `i = j`), or `c ν_a I(ν + e_a - e_b)`
(`b < N`; `b = a` is no shift), or `c ν_a I(ν + e_a)` (`b = N`). -/
theorem mem_template {F : Family} {i j : ℕ} {t : Term} (h : t ∈ F.template i j) :
    t = ⟨[], 0, F.spDen, 0, 0⟩ ∨
      ∃ a < F.nProp, ∃ b ≤ F.nProp, ∃ c : ℤ, t = ⟨Family.shiftVec F.nProp a b, 0, 0, a, c⟩ := by
  have hnz : ∀ {s a c}, t ∈ Family.nzTerm s a c → t = ⟨s, 0, 0, a, c⟩ := by
    intro s a c ht
    simp only [Family.nzTerm, Bool.cond_eq_ite] at ht
    split_ifs at ht
    · simp at ht
    · simpa using ht
  unfold Family.template at h
  rw [List.mem_append] at h
  rcases h with h | h
  · left
    simp only [Bool.cond_eq_ite] at h
    split_ifs at h
    · simpa using h
    · simp at h
  · right
    obtain ⟨a, ha, h⟩ := List.mem_flatMap.mp h
    obtain ⟨w, -, h⟩ := List.mem_flatMap.mp h
    rw [List.mem_range] at ha
    simp only [Bool.cond_eq_ite] at h
    split_ifs at h
    · simp at h
    · rw [List.mem_append] at h
      rcases h with h | h
      · exact ⟨a, ha, F.nProp, le_rfl, _, hnz h⟩
      · obtain ⟨b, hb, h⟩ := List.mem_flatMap.mp h
        exact ⟨a, ha, b, (List.mem_range.mp hb).le, _, hnz h⟩

/-! ### The normalization under the template shifts -/

theorem mul_inv_Gamma_succ (s : ℂ) : s * (Gamma (s + 1))⁻¹ = (Gamma s)⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Gamma_zero]
  · rw [Gamma_add_one s hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- `ν_a N(ν + e_a - e_b) = (ν_b - 1) N(ν)` for `a ≠ b`. -/
theorem normLP_raise_lower (ν : Fin 9 → ℂ) (d : ℂ) {a b : Fin 9} (hab : a ≠ b) :
    ν a * normLP (fun i => ν i + ((if i = a then 1 else 0) - (if i = b then 1 else 0))) d =
      (ν b - 1) * normLP ν d := by
  have hs : ∑ i, (ν i + ((if i = a then (1 : ℂ) else 0) - (if i = b then 1 else 0))) =
      ∑ i, ν i := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
  have hp : ∀ g : Fin 9 → ℂ,
      ∏ i, g i = g a * (g b * ∏ i ∈ (Finset.univ.erase a).erase b, g i) := by
    intro g
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  unfold normLP
  rw [hs, hp, hp (fun i => (Gamma (ν i))⁻¹)]
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b,
      (Gamma (ν i + ((if i = a then 1 else 0) - (if i = b then 1 else 0))))⁻¹ =
      ∏ i ∈ (Finset.univ.erase a).erase b, (Gamma (ν i))⁻¹ :=
    Finset.prod_congr rfl fun i hi => by
      have h1 := Finset.ne_of_mem_erase hi
      have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      simp [h1, h2]
  rw [hrest]
  simp only [↓reduceIte, ite_eq_right hab, ite_eq_right (Ne.symm hab), sub_zero, zero_sub,
    ← sub_eq_add_neg]
  have e1 := mul_inv_Gamma_succ (ν a)
  have e2 := mul_inv_Gamma_succ (ν b - 1)
  rw [sub_add_cancel] at e2
  rw [← e2, ← e1]
  ring

/-- `ν_a N(ν + e_a) = (2d - |ν| - 1) N(ν)`. -/
theorem normLP_raise (ν : Fin 9 → ℂ) (d : ℂ) (a : Fin 9) :
    ν a * normLP (fun i => ν i + (if i = a then 1 else 0)) d =
      (2 * d - ∑ i, ν i - 1) * normLP ν d := by
  have hs : ∑ i, (ν i + (if i = a then (1 : ℂ) else 0)) = ∑ i, ν i + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hp : ∀ g : Fin 9 → ℂ, ∏ i, g i = g a * ∏ i ∈ Finset.univ.erase a, g i := fun g =>
    (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm
  unfold normLP
  rw [hs, hp, hp (fun i => (Gamma (ν i))⁻¹)]
  have hrest : ∏ i ∈ Finset.univ.erase a, (Gamma (ν i + (if i = a then 1 else 0)))⁻¹ =
      ∏ i ∈ Finset.univ.erase a, (Gamma (ν i))⁻¹ :=
    Finset.prod_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi]
  rw [hrest]
  simp only [↓reduceIte]
  have e1 := mul_inv_Gamma_succ (ν a)
  have e2 := mul_inv_Gamma_succ (2 * d - ∑ i, ν i - 1)
  rw [sub_add_cancel, show 2 * d - ∑ i, ν i - 1 = 2 * d - (∑ i, ν i + 1) by ring] at e2
  rw [← e1, ← e2]
  ring

/-! ### Linear combinations with affine coefficients -/

/-- The variable of a label head: `ν_k` for `k < 9`, `d` for `9`, `1` otherwise. -/
def varC (ν : Fin 9 → ℂ) (d : ℂ) (k : ℤ) : ℂ :=
  if h : 0 ≤ k ∧ k.toNat < 9 then ν ⟨k.toNat, h.2⟩ else if k = 9 then d else 1

theorem varC_fin (ν : Fin 9 → ℂ) (d : ℂ) (k : Fin 9) : varC ν d ((k : ℕ) : ℤ) = ν k := by
  have h : 0 ≤ ((k : ℕ) : ℤ) ∧ ((k : ℕ) : ℤ).toNat < 9 := by simp
  simp only [varC, dite_eq_left h]
  exact congrArg ν (Fin.ext (by simp))

theorem varC_nat (ν : Fin 9 → ℂ) (d : ℂ) {k : ℕ} (hk : k < 9) :
    varC ν d (k : ℤ) = ν ⟨k, hk⟩ := varC_fin ν d ⟨k, hk⟩

theorem varC_nine (ν : Fin 9 → ℂ) (d : ℂ) : varC ν d 9 = d := by simp [varC]

theorem varC_ten (ν : Fin 9 → ℂ) (d : ℂ) : varC ν d 10 = 1 := by simp [varC]

/-- The value of a label `k :: σ`: the variable `k` times `J σ`. -/
def keyVal (J : List ℤ → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) : List ℤ → ℂ
  | [] => 0
  | k :: σ => varC ν d k * J σ

@[simp] theorem keyVal_cons (J : List ℤ → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) (k : ℤ) (σ : List ℤ) :
    keyVal J ν d (k :: σ) = varC ν d k * J σ := rfl

/-- The value `Σ c · keyVal(label)` of a list of labelled integer coefficients. -/
def lcEval (J : List ℤ → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) (l : List (List ℤ × ℤ)) : ℂ :=
  (l.map fun t => (t.2 : ℂ) * keyVal J ν d t.1).sum

theorem lcEval_append (J : List ℤ → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) (l m : List (List ℤ × ℤ)) :
    lcEval J ν d (l ++ m) = lcEval J ν d l + lcEval J ν d m := by
  simp [lcEval]

theorem lcEval_flatMap {β : Type*} (J : List ℤ → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) (L : List β)
    (f : β → List (List ℤ × ℤ)) :
    lcEval J ν d (L.flatMap f) = (L.map fun x => lcEval J ν d (f x)).sum := by
  induction L with
  | nil => simp [lcEval]
  | cons x L ih => rw [List.flatMap_cons, lcEval_append, ih, List.map_cons, List.sum_cons]

/-- The kernel zero test: all coefficients cancel after merging equal labels. -/
def zeroLC (l : List (List ℤ × ℤ)) : Bool :=
  (LinComb.sumTree 64 (l.map fun t => bif intIsZero t.2 then [] else [(t.1, [t.2])])).isEmpty

theorem eval_zeroLC_aux (f : List ℤ → ℂ) (l : List (List ℤ × ℤ)) :
    LinComb.eval f 0
      (LinComb.sumTree 64 (l.map fun t => bif intIsZero t.2 then [] else [(t.1, [t.2])])) =
      (l.map fun t => (t.2 : ℂ) * f t.1).sum := by
  rw [LinComb.eval_sumTree, List.map_map]
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    cases h : intIsZero t.2
    · simp [Function.comp_apply, h]
    · simp only [Function.comp_apply, h, Bool.cond_true, LinComb.eval_nil]
      rw [eq_zero_of_intIsZero h]
      simp

theorem lcEval_eq_zero_of_zeroLC {l : List (List ℤ × ℤ)} (h : zeroLC l = true)
    (J : List ℤ → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) : lcEval J ν d l = 0 := by
  rw [lcEval, ← eval_zeroLC_aux]
  simp only [zeroLC, List.isEmpty_iff] at h
  rw [h]
  rfl

theorem lsum_map_neg {β : Type*} (L : List β) (f : β → ℂ) :
    (L.map fun x => -f x).sum = -(L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The negated combination. -/
def negLC (l : List (List ℤ × ℤ)) : List (List ℤ × ℤ) := l.map fun t => (t.1, -t.2)

theorem lcEval_eq_of_zeroLC {l m : List (List ℤ × ℤ)} (h : zeroLC (l ++ negLC m) = true)
    (J : List ℤ → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) : lcEval J ν d l = lcEval J ν d m := by
  have h0 := lcEval_eq_zero_of_zeroLC h J ν d
  rw [lcEval_append] at h0
  have hn : lcEval J ν d (negLC m) = -lcEval J ν d m := by
    simp only [lcEval, negLC, List.map_map]
    rw [← lsum_map_neg]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp
  linear_combination h0 - hn

/-! ### The template side -/

/-- The label `σ` of the term `ν_a I(ν + e_a - e_b)` with the affine coefficient
`2 (N(ν + σ)/N(ν)) ν_a`: `2(ν_b - 1)` (`b ≠ a`, `b < 9`), `2 ν_a` (`b = a`),
`2(2d - |ν| - 1)` (`b = 9`), times `c`. -/
def redAB (a b : ℕ) (c : ℤ) : List (List ℤ × ℤ) :=
  if b = 9 then
    ((9 : ℤ) :: Family.shiftVec 9 a b, 4 * c) :: ((10 : ℤ) :: Family.shiftVec 9 a b, -2 * c) ::
      (List.range 9).map fun k : ℕ => ((k : ℤ) :: Family.shiftVec 9 a b, -2 * c)
  else if b = a then [((a : ℤ) :: Family.shiftVec 9 a b, 2 * c)]
  else [((b : ℤ) :: Family.shiftVec 9 a b, 2 * c), ((10 : ℤ) :: Family.shiftVec 9 a b, -2 * c)]

/-- The index `b` of a template shift `e_a - e_b` (`9` for `e_a`). -/
def bOf (σ : List ℤ) (a : ℕ) : ℕ :=
  if σ.all (· == 0) then a else (σ.findIdx? (· == -1)).getD 9

theorem bOf_shiftVec : ∀ a < 9, ∀ b ≤ 9, bOf (Family.shiftVec 9 a b) a = b := by
  decide +kernel

/-- The affine reduction of a template term (meaningful on the shapes of `mem_template`). -/
def redTerm (t : Term) : List (List ℤ × ℤ) :=
  if t.shift = [] then [((9 : ℤ) :: List.replicate 9 0, 2 * t.cd)]
  else redAB t.idx (bOf t.shift t.idx) t.cnu

/-- The template, reduced. -/
def tmplLC (i j : ℕ) : List (List ℤ × ℤ) := (lbl.template i j).flatMap redTerm

theorem sum_fin_nine_list (f : ℕ → ℂ) :
    ((List.range 9).map f).sum = ∑ k : Fin 9, f k := by
  simp [List.sum_range_succ, Fin.sum_univ_succ]
  ring

theorem shiftVec_ne_nil (a b : ℕ) : Family.shiftVec 9 a b ≠ [] := by
  simp [Family.shiftVec]

/-- One reduced term, `ν_a N(ν + σ) J(σ) = (N(ν)/2) · (affine coefficient) J(σ)`. -/
theorem tcoef_mul_redAB (Φ : (Fin 9 → ℂ) → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) {a b : ℕ} (ha : a < 9)
    (hb : b ≤ 9) (c : ℤ) :
    tcoef ⟨Family.shiftVec 9 a b, 0, 0, a, c⟩ d ν *
        (normLP (ν + shC (Family.shiftVec 9 a b)) d * Φ (shC (Family.shiftVec 9 a b))) =
      normLP ν d / 2 * lcEval (fun σ => Φ (shC σ)) ν d (redAB a b c) := by
  set σ := Family.shiftVec 9 a b
  set A : Fin 9 := ⟨a, ha⟩
  set F := Φ (shC σ)
  have htc : tcoef ⟨σ, 0, 0, a, c⟩ d ν = c * ν A := by simp [tcoef, ha, A]
  rw [htc]
  rcases eq_or_lt_of_le hb with rfl | hb9
  · -- `b = 9`: the shift `e_a`
    have hν : ν + shC σ = fun i => ν i + (if i = A then 1 else 0) := by
      funext i
      simp only [Pi.add_apply, σ, shC_shiftVec, A, Fin.ext_iff]
      have : (i : ℕ) ≠ 9 := i.isLt.ne
      simp [this]
    have h := normLP_raise ν d A
    have hsum : ((List.range 9).map ((fun t : List ℤ × ℤ => (t.2 : ℂ) * keyVal
        (fun σ => Φ (shC σ)) ν d t.1) ∘ fun k : ℕ => ((k : ℤ) :: σ, -2 * c))).sum =
        ((-2 * c : ℤ) : ℂ) * F * ∑ k, ν k := by
      rw [sum_fin_nine_list, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Function.comp_apply, keyVal_cons, varC_fin]
      ring
    rw [hν, redAB, ite_eq_left rfl, lcEval, List.map_cons, List.map_cons, List.sum_cons,
      List.sum_cons, List.map_map, hsum, keyVal_cons, keyVal_cons, varC_nine, varC_ten]
    push_cast
    linear_combination (c : ℂ) * F * h
  · by_cases hab : b = a
    · -- no shift
      subst hab
      have hν : ν + shC σ = ν := by
        funext i
        simp [σ, shC_shiftVec]
      rw [hν, redAB, ite_eq_right hb9.ne, ite_eq_left rfl]
      simp only [lcEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, keyVal_cons,
        varC_nat ν d ha]
      push_cast
      ring
    · -- the shift `e_a - e_b`
      set B : Fin 9 := ⟨b, hb9⟩
      have hAB : A ≠ B := fun h => hab (congrArg Fin.val h).symm
      have hν : ν + shC σ =
          fun i => ν i + ((if i = A then 1 else 0) - (if i = B then 1 else 0)) := by
        funext i
        simp only [Pi.add_apply, σ, shC_shiftVec, A, B, Fin.ext_iff]
      have h := normLP_raise_lower ν d hAB
      rw [hν, redAB, ite_eq_right hb9.ne, ite_eq_right hab]
      simp only [lcEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, keyVal_cons,
        varC_nat ν d hb9, varC_ten]
      push_cast
      linear_combination (c : ℂ) * F * h

/-- **The template, reduced**: `Σ_t coeff_t N(ν + σ_t) J(σ_t) = (N(ν)/2) · lcEval (tmplLC)`. -/
theorem tmplSum_eq (Φ : (Fin 9 → ℂ) → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) (i j : ℕ) :
    ((lbl.template i j).map fun t => tcoef t d ν *
        (normLP (ν + shC t.shift) d * Φ (shC t.shift))).sum =
      normLP ν d / 2 * lcEval (fun σ => Φ (shC σ)) ν d (tmplLC i j) := by
  rw [tmplLC, lcEval_flatMap, ← list_sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  rcases mem_template ht with rfl | ⟨a, ha, b, hb, c, rfl⟩
  · rw [redTerm, ite_eq_left rfl]
    simp only [lcEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, keyVal_cons,
      varC_nine, shC_nil, shC_replicate, add_zero, tcoef, show lbl.spDen = 2 from rfl]
    push_cast
    ring_nf
  · have ha' : a < 9 := ha
    have hb' : b ≤ 9 := hb
    simp only [show lbl.nProp = 9 from rfl]
    rw [tcoef_mul_redAB Φ ν d ha' hb' c]
    simp only [redTerm, ite_eq_right (shiftVec_ne_nil a b), bOf_shiftVec a ha' b hb']

/-! ### The annihilator side -/

/-- The annihilator relation of `(p, q)` as labelled affine coefficients, times `2`. -/
def annLC (p : List ZPoly) (q : ZPoly) : List (List ℤ × ℤ) :=
  ((List.range 9).flatMap fun b => (p.getD b []).flatMap fun t =>
    [((b : ℤ) :: (List.range 9).map (fun k => (t.1.getD k 0 : ℤ) - if k = b then 1 else 0),
        2 * t.2),
      ((10 : ℤ) :: (List.range 9).map (fun k => (t.1.getD k 0 : ℤ) - if k = b then 1 else 0),
        2 * t.2 * ((t.1.getD b 0 : ℤ) - 1))]) ++
  q.map fun t => ((9 : ℤ) :: (List.range 9).map fun k => (t.1.getD k 0 : ℤ), -t.2)

theorem shC_lower (ν : Fin 9 → ℂ) (α : List ℕ) (b : Fin 9) :
    ν + shC ((List.range 9).map fun k => (α.getD k 0 : ℤ) - if k = b then 1 else 0) =
      lowerAt (natShift ν fun k => α.getD k 0) b := by
  funext k
  simp only [Pi.add_apply, shC, getD_range_map_int _ k.isLt, lowerAt, natShift, Fin.ext_iff]
  split_ifs <;> push_cast <;> ring

theorem shC_raise (ν : Fin 9 → ℂ) (α : List ℕ) :
    ν + shC ((List.range 9).map fun k => (α.getD k 0 : ℤ)) = natShift ν fun k => α.getD k 0 := by
  funext k
  simp [shC, natShift]

/-- **The annihilator side**: `lcEval (annLC p q)` is twice the relation of
`QED.DimReg.lpIntegral_annihilator` (with `r = 0`) for the values `Ψ`. -/
theorem lcEval_annLC (Ψ : (Fin 9 → ℂ) → ℂ) (ν : Fin 9 → ℂ) (d : ℂ) (p : List ZPoly)
    (q : ZPoly) :
    lcEval (fun σ => Ψ (ν + shC σ)) ν d (annLC p q) =
      2 * (∑ b, ((annField p b).map fun t => (t.1 : ℂ) * (ν b + t.2 b - 1) *
          Ψ (lowerAt (natShift ν t.2) b)).sum -
        d / 2 * ((toML q).map fun t => (t.1 : ℂ) * Ψ (natShift ν t.2)).sum) := by
  have h1 : lcEval (fun σ => Ψ (ν + shC σ)) ν d ((List.range 9).flatMap fun b =>
      (p.getD b []).flatMap fun t =>
        [((b : ℤ) :: (List.range 9).map (fun k => (t.1.getD k 0 : ℤ) - if k = b then 1 else 0),
            2 * t.2),
          ((10 : ℤ) :: (List.range 9).map (fun k => (t.1.getD k 0 : ℤ) - if k = b then 1 else 0),
            2 * t.2 * ((t.1.getD b 0 : ℤ) - 1))]) =
      2 * ∑ b, ((annField p b).map fun t => (t.1 : ℂ) * (ν b + t.2 b - 1) *
          Ψ (lowerAt (natShift ν t.2) b)).sum := by
    rw [lcEval_flatMap, sum_fin_nine_list, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [lcEval_flatMap, annField, ZPoly.toML, List.map_map, ← list_sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp only [lcEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, keyVal_cons,
      varC_fin, varC_ten, shC_lower, Function.comp_apply]
    push_cast
    ring
  have h2 : lcEval (fun σ => Ψ (ν + shC σ)) ν d (q.map fun t =>
      ((9 : ℤ) :: (List.range 9).map fun k => (t.1.getD k 0 : ℤ), -t.2)) =
      -(2 * (d / 2 * ((toML q).map fun t => (t.1 : ℂ) * Ψ (natShift ν t.2)).sum)) := by
    simp only [lcEval, ZPoly.toML, List.map_map, ← list_sum_map_mul_left]
    rw [← lsum_map_neg]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp only [Function.comp_apply, keyVal_cons, varC_nine, shC_raise]
    push_cast
    ring
  rw [annLC, lcEval_append, h1, h2]
  ring

/-! ### The kernel check and the relation -/

/-- The twelve templates agree with the twelve annihilators, term by term. -/
theorem tmplCheck_all : ∀ i < 3, ∀ j < 4,
    zeroLC (annLC (pT i j) (qT i j) ++ negLC (tmplLC i j)) = true := by
  decide +kernel

/-- Bounds on the exponents occurring in the annihilator data. -/
theorem pExp_le : ∀ i < 3, ∀ j < 4, ∀ b < 9, ∀ t ∈ (pT i j).getD b [], ∀ k < 9,
    t.1.getD k 0 ≤ 2 := by
  decide +kernel

theorem degs_le : ∀ k < 9, degs.getD k 0 ≤ 2 := by decide

theorem mulDiff_exp_le {P : ZPoly} (hP : ∀ t ∈ P, ∀ k < 9, t.1.getD k 0 ≤ 2) (b : ℕ) :
    ∀ t ∈ ZPoly.mul P (ZPoly.diff b (ZPoly.ofN lpPoly)), ∀ k < 9, t.1.getD k 0 ≤ 4 := by
  intro t ht k hk
  obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  simp only [getD_addExp, getD_subExp]
  have h1 := hP s hs k hk
  have h2 := deg_lpPoly w hw ⟨k, hk⟩
  have h3 := degs_le k hk
  simp only at h2
  omega

theorem qExp_le : ∀ i < 3, ∀ j < 4, ∀ t ∈ qT i j, ∀ k < 9, t.1.getD k 0 ≤ 2 := by
  decide +kernel

/-- The points where the template relation needs convergence: exponents `ν + α` or
`ν + α - e_b` with `α ≤ 6` entrywise, dimension `d` or `d + 2`. -/
def Shifted (ν : Fin 9 → ℂ) (d : ℂ) (μ : Fin 9 → ℂ) (e : ℂ) : Prop :=
  (∀ k, ∃ m : ℕ, m ≤ 6 ∧ (μ k = ν k + m ∨ μ k = ν k + m - 1)) ∧ (e = d ∨ e = d + 2)

/-- **The template relations at a convergent point.** If all integrals near `(ν, d)` converge,
the normalized integrals `N(ν + σ, d) J(ν + σ, d)` satisfy the template relation `(i, j)` of
`lbl`. -/
theorem tmpl_lp {i j : ℕ} (hi : i < 3) (hj : j < 4) (ν : Fin 9 → ℂ) (d : ℂ)
    (hconv : ∀ μ e, Shifted ν d μ e → LPConvergent (fun x => lpPoly.eval x) μ e) :
    ((lbl.template i j).map fun t => tcoef t d ν * (normLP (ν + shC t.shift) d *
      lpIntegral (fun x => lpPoly.eval x) (ν + shC t.shift) d)).sum = 0 := by
  have hb := pExp_le i hi j hj
  have hqb := qExp_le i hi j hj
  have hA := lpIntegral_annihilator (G := fun x => lpPoly.eval x) (fun x hx => G_pos hx)
    (fun b x _ => hasDerivAt_G b x) (annField (pT i j)) (toML (qT i j)) []
    (annProd lpPoly (pT i j)) (fun x _ => hsyz hi hj x) (fun b x _ => he i j b x) ν d
    (fun b t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      refine hconv _ _ ⟨fun k => ⟨u.1.getD k 0, (hb b b.isLt u hu k k.isLt).trans
        (by norm_num), ?_⟩, Or.inl rfl⟩
      by_cases hk : k = b
      · right; simp [lowerAt, natShift, hk]
      · left; simp [lowerAt, natShift, hk])
    (fun t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact hconv _ _ ⟨fun k => ⟨u.1.getD k 0, (hqb u hu k k.isLt).trans (by norm_num),
        Or.inl rfl⟩, Or.inl rfl⟩)
    (fun t ht => by simp at ht)
    (fun b t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact hconv _ _ ⟨fun k => ⟨u.1.getD k 0, (mulDiff_exp_le (hb b b.isLt) b u hu k
        k.isLt).trans (by norm_num), Or.inl rfl⟩, Or.inr rfl⟩)
  have hE := lcEval_eq_of_zeroLC (tmplCheck_all i hi j hj)
    (fun σ => lpIntegral (fun x => lpPoly.eval x) (ν + shC σ) d) ν d
  rw [tmplSum_eq (fun δ => lpIntegral (fun x => lpPoly.eval x) (ν + δ) d), ← hE,
    lcEval_annLC (fun μ => lpIntegral (fun x => lpPoly.eval x) μ d)]
  simp only [List.map_nil, List.sum_nil, add_zero] at hA
  rw [hA]
  ring

end QED.DimReg.ThreeLoop
