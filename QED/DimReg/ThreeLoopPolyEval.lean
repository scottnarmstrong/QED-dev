/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.SectorCert
public import QED.DimReg.LPAnnihilator
public import QED.Algebra.IBPCertPoly

/-!
# Sparse integer polynomials: evaluation, products, partial derivatives, kernel zero tests

For families with many Schwinger parameters (nine at three loops) the polynomial identities
behind the annihilator relations of `QED.DimReg.lpIntegral_annihilator` have thousands of terms,
too many for `ring`. They are checked here by the kernel instead: a sparse polynomial
`QED.DimReg.ZPoly` (exponent lists with integer coefficients) is evaluated by
`QED.DimReg.ZPoly.eval` with the monomials `QED.DimReg.Sector.mono` of the sector checker, and

* products (`QED.DimReg.ZPoly.mul`, `eval_mul`), scalar multiples and sums are computed
  exactly;
* partial derivatives are computed on exponents (`QED.DimReg.ZPoly.diff`) and are the actual
  derivatives (`QED.DimReg.ZPoly.hasDerivAt_eval_update`);
* `QED.DimReg.ZPoly.isZeroB` collects like terms with the sorted merges of the IBP checker
  (`QED.Algebra.IBPCert.LinComb.sumTree`), so that `decide +kernel` proves `P.eval = 0`
  (`QED.DimReg.ZPoly.eval_eq_zero_of_isZeroB`);
* `QED.DimReg.ZPoly.toML` converts to the monomial lists of `QED.DimReg.lpIntegral_annihilator`
  (`QED.DimReg.ZPoly.polyEval_toML`).

Nothing here depends on the number of variables.
-/

@[expose] public section

namespace QED.DimReg

open QED.Algebra.IBPCert Sector

/-- A sparse polynomial `Σ cₜ y ^ αₜ` with integer coefficients (exponent lists, missing
entries `0`). -/
abbrev ZPoly := List (List ℕ × ℤ)

namespace ZPoly

variable {N : ℕ}

/-- Evaluation of a sparse integer polynomial. -/
noncomputable def eval (P : ZPoly) (y : Fin N → ℝ) : ℝ :=
  (P.map fun t => (t.2 : ℝ) * mono t.1 y).sum

@[simp] theorem eval_nil (y : Fin N → ℝ) : eval [] y = 0 := rfl

@[simp] theorem eval_cons (t : List ℕ × ℤ) (P : ZPoly) (y : Fin N → ℝ) :
    eval (t :: P) y = (t.2 : ℝ) * mono t.1 y + eval P y := by
  simp [eval]

theorem eval_append (P Q : ZPoly) (y : Fin N → ℝ) : eval (P ++ Q) y = eval P y + eval Q y := by
  simp [eval]

/-- The natural polynomial as an integer one. -/
def ofN (P : NPoly) : ZPoly := P.map fun t => (t.1, (t.2 : ℤ))

theorem eval_ofN (P : NPoly) (y : Fin N → ℝ) : eval (ofN P) y = P.eval y := by
  simp [eval, ofN, NPoly.eval, Function.comp_def]

/-- The scalar multiple `c P`. -/
def smul (c : ℤ) (P : ZPoly) : ZPoly := P.map fun t => (t.1, c * t.2)

theorem eval_smul (c : ℤ) (P : ZPoly) (y : Fin N → ℝ) : eval (smul c P) y = c * eval P y := by
  induction P with
  | nil => simp [smul]
  | cons t P ih =>
    simp only [smul, List.map_cons, eval_cons, Int.cast_mul] at ih ⊢
    rw [ih]; ring

/-- The product of two sparse polynomials (not normalized). -/
def mul (P Q : ZPoly) : ZPoly := P.flatMap fun s => Q.map fun t => (addExp s.1 t.1, s.2 * t.2)

theorem eval_map_mul (s : List ℕ × ℤ) (Q : ZPoly) (y : Fin N → ℝ) :
    eval (Q.map fun t => (addExp s.1 t.1, s.2 * t.2)) y = (s.2 : ℝ) * mono s.1 y * eval Q y := by
  induction Q with
  | nil => simp
  | cons t Q ih =>
    simp only [List.map_cons, eval_cons, ih, mono_addExp, Int.cast_mul]
    ring

theorem eval_mul (P Q : ZPoly) (y : Fin N → ℝ) : eval (mul P Q) y = eval P y * eval Q y := by
  induction P with
  | nil => simp [mul]
  | cons s P ih =>
    simp only [mul, List.flatMap_cons, eval_append, eval_map_mul, eval_cons] at ih ⊢
    rw [ih]; ring

/-- The sum of a list of sparse polynomials. -/
def sum (Ps : List ZPoly) : ZPoly := Ps.flatten

theorem eval_sum (Ps : List ZPoly) (y : Fin N → ℝ) :
    eval (sum Ps) y = (Ps.map fun P => eval P y).sum := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih => simp only [sum, List.flatten_cons, eval_append, List.map_cons,
      List.sum_cons] at ih ⊢; rw [ih]

/-! ### Partial derivatives -/

/-- The partial derivative `∂_b P`, computed on exponents. -/
def diff (b : ℕ) (P : ZPoly) : ZPoly :=
  P.map fun t => (subExp t.1 (unitExp b), t.2 * (t.1.getD b 0 : ℤ))

theorem getD_unitExp (b k : ℕ) : (unitExp b).getD k 0 = if k = b then 1 else 0 := by
  rw [unitExp, getD_addAt]; simp

/-- `y ^ α` with `y_b` replaced by `s`: `s ^ α_b` times the other factors. -/
theorem mono_update (α : List ℕ) (y : Fin N → ℝ) (b : Fin N) (s : ℝ) :
    mono α (Function.update y b s) =
      s ^ α.getD b 0 * ∏ k ∈ Finset.univ.erase b, y k ^ α.getD k 0 := by
  rw [mono, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem mono_diffExp (α : List ℕ) (y : Fin N → ℝ) (b : Fin N) :
    mono (subExp α (unitExp b)) y =
      y b ^ (α.getD b 0 - 1) * ∏ k ∈ Finset.univ.erase b, y k ^ α.getD k 0 := by
  rw [mono, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
  simp only [getD_subExp, getD_unitExp, ite_true]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have : (k : ℕ) ≠ b := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
  simp [this]

theorem hasDerivAt_mono_update (α : List ℕ) (y : Fin N → ℝ) (b : Fin N) :
    HasDerivAt (fun s => mono α (Function.update y b s))
      ((α.getD b 0 : ℝ) * mono (subExp α (unitExp b)) y) (y b) := by
  simp only [mono_update, mono_diffExp]
  convert (hasDerivAt_pow (α.getD b 0) (y b)).mul_const
    (∏ k ∈ Finset.univ.erase b, y k ^ α.getD k 0) using 1
  ring

/-- **The computed derivative is the derivative.** -/
theorem hasDerivAt_eval_update (P : ZPoly) (y : Fin N → ℝ) (b : Fin N) :
    HasDerivAt (fun s => eval P (Function.update y b s)) (eval (diff b P) y) (y b) := by
  induction P with
  | nil => simpa [diff] using hasDerivAt_const (y b) (0 : ℝ)
  | cons t P ih =>
    simp only [diff, List.map_cons, eval_cons] at ih ⊢
    convert ((hasDerivAt_mono_update t.1 y b).const_mul (t.2 : ℝ)).add ih using 1
    push_cast; ring

/-! ### Zero tests by the kernel -/

/-- The polynomial as a sorted linear combination of the IBP checker (labels = exponents,
constant coefficients). -/
def toLC (P : ZPoly) : LinComb :=
  LinComb.sumTree 64
    (P.map fun t => bif intIsZero t.2 then [] else [(t.1.map Int.ofNat, [t.2])])

/-- All coefficients cancel after collecting like terms. -/
def isZeroB (P : ZPoly) : Bool := (toLC P).isEmpty

/-- The monomial of a label, for `LinComb.eval`. -/
noncomputable def monoZ (y : Fin N → ℝ) (l : List ℤ) : ℝ := mono (l.map Int.toNat) y

theorem eval_toLC (P : ZPoly) (y : Fin N → ℝ) : LinComb.eval (monoZ y) 0 (toLC P) = eval P y := by
  rw [toLC, LinComb.eval_sumTree, List.map_map]
  induction P with
  | nil => rfl
  | cons t P ih =>
    rw [List.map_cons, List.sum_cons, ih, eval_cons]
    cases h : intIsZero t.2
    · simp only [Function.comp_apply, h, Bool.cond_false, LinComb.eval_cons, LinComb.eval_nil,
        Poly.eval_cons, Poly.eval_nil]
      simp [monoZ, Function.comp_def]
    · rw [Function.comp_apply, h, Bool.cond_true, LinComb.eval_nil, eq_zero_of_intIsZero h]
      simp

/-- **Kernel zero test.** -/
theorem eval_eq_zero_of_isZeroB {P : ZPoly} (h : isZeroB P = true) (y : Fin N → ℝ) :
    eval P y = 0 := by
  rw [← eval_toLC]
  simp only [isZeroB, List.isEmpty_iff] at h
  rw [h]; rfl

/-- Two polynomials agree if their difference passes the zero test. -/
theorem eval_eq_of_isZeroB {P Q : ZPoly} (h : isZeroB (P ++ smul (-1) Q) = true)
    (y : Fin N → ℝ) : eval P y = eval Q y := by
  have := eval_eq_zero_of_isZeroB h y
  rw [eval_append, eval_smul] at this
  push_cast at this
  linarith

/-! ### Monomial lists -/

/-- The monomial list of `QED.DimReg.lpIntegral_annihilator`. -/
def toML (P : ZPoly) : MonoList N := P.map fun t => (t.2, fun k => t.1.getD k 0)

theorem polyEval_toML (P : ZPoly) (x : Fin N → ℝ) : polyEval (toML P) x = eval P x := by
  simp [polyEval, toML, eval, monoEval, mono, Function.comp_def]

/-! ### Annihilator checks -/

/-- The kernel check of an annihilator `Σ_b p_b ∂_b G = q G` of the natural polynomial `G`, with
`p_b` the `b`-th entry of `p`. -/
def annCheck (N : ℕ) (G : NPoly) (p : List ZPoly) (q : ZPoly) : Bool :=
  isZeroB (sum (List.ofFn (n := N) fun b => mul (p.getD b []) (diff b (ofN G))) ++
    smul (-1) (mul q (ofN G)))

/-- The products `p_b ∂_b G`, as monomial lists. -/
def annProd (G : NPoly) (p : List ZPoly) (b : Fin N) : MonoList N :=
  toML (mul (p.getD b []) (diff b (ofN G)))

/-- The vector field `p`, as monomial lists. -/
def annField (p : List ZPoly) (b : Fin N) : MonoList N := toML (p.getD b [])

/-- **The syzygy of a checked annihilator**, in the form of
`QED.DimReg.lpIntegral_annihilator`. -/
theorem annCheck_syz {G : NPoly} {p : List ZPoly} {q : ZPoly} (h : annCheck N G p q = true)
    (x : Fin N → ℝ) :
    ∑ b, polyEval (annField p b) x * eval (diff b (ofN G)) x =
      polyEval (toML q) x * G.eval x + polyEval [] x := by
  have h0 := eval_eq_of_isZeroB h x
  rw [eval_sum, List.map_ofFn, List.sum_ofFn, eval_mul, eval_ofN] at h0
  simp only [Function.comp_def, eval_mul] at h0
  simp only [annField, polyEval_toML, h0]
  simp [polyEval]

/-- The products `p_b ∂_b G` evaluate correctly. -/
theorem annProd_eval (G : NPoly) (p : List ZPoly) (b : Fin N) (x : Fin N → ℝ) :
    polyEval (annField p b) x * eval (diff b (ofN G)) x = polyEval (annProd G p b) x := by
  simp only [annField, annProd, polyEval_toML, eval_mul]

/-- A natural polynomial with a positive coefficient is positive on the open orthant. -/
theorem _root_.QED.DimReg.Sector.NPoly.eval_pos_of_mem {P : NPoly} {t : List ℕ × ℕ} (ht : t ∈ P)
    (hc : 0 < t.2) {y : Fin N → ℝ} (hy : y ∈ posOrthant N) : 0 < P.eval y := by
  have hy' := mem_posOrthant.mp hy
  have hpos : 0 < (t.2 : ℝ) * mono t.1 y :=
    mul_pos (by exact_mod_cast hc) (Finset.prod_pos fun k _ => pow_pos (hy' k) _)
  refine lt_of_lt_of_le hpos (List.single_le_sum (fun z hz => ?_) _
    (List.mem_map.mpr ⟨t, ht, rfl⟩))
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hz
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun k _ => pow_nonneg (hy' k).le _)

end ZPoly

end QED.DimReg
