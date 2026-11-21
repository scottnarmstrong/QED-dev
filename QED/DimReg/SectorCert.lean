/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.CubeSplit

/-!
# Certified sector decomposition: the checker and its soundness

A sector certificate (`QED.DimReg.Sector.SDCert`) is a splitting tree (`QED.DimReg.SplitTree`)
together with the polynomials of the integrand, as sparse polynomials with natural coefficients
(`QED.DimReg.Sector.NPoly`). The checker `QED.DimReg.Sector.SDCert.check` is a computable
`Bool`, run by `decide +kernel`. For every leaf `σ` of the tree and every polynomial `P` it pulls
`P` back along the leaf substitution `φ_σ` (exponent arithmetic only: `yᵢ ↦ yⱼ yᵢ` sends the
exponent `α` to `α + αᵢ eⱼ`), takes the componentwise minimal exponent `m` of `P ∘ φ_σ`, and checks
that some term of `P ∘ φ_σ` has exponent exactly `m`. No data per leaf are needed.

Soundness (`QED.DimReg.Sector.SDCert.sound`): if the check passes, then for an integrable `g`

  `∫_Q g = Σ_σ ∫_Q J_σ(y) · g(φ_σ(y)) dy`,

the Jacobian `J_σ` is the monomial `y ^ jacExp σ`, and every polynomial factorizes on the leaf as
`P(φ_σ(y)) = y ^ m · P̃(y)` with `P̃ ≥ 1` on the closed orthant. So `P̃ ^ c` is smooth and
bounded away from `0` on the closed cube, and the leaf integrand is a monomial times a smooth
function: the input of the one-variable continuation (`QED.DimReg.mellinCont`).

## Main definitions and results

* `QED.DimReg.Sector.mono`, `QED.DimReg.Sector.NPoly.eval`: evaluation.
* `QED.DimReg.Sector.mono_splitMap`, `QED.DimReg.Sector.mono_pullExp`,
  `QED.DimReg.Sector.leafJac_eq_mono`: the exponent arithmetic of the substitutions.
* `QED.DimReg.Sector.eval_eq_mono_mul_of_leafOk`, `QED.DimReg.Sector.one_le_eval_shift`: the leaf
  factorization.
* `QED.DimReg.Sector.SDCert.check`, `QED.DimReg.Sector.SDCert.sound`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.DimReg

namespace SplitTree

variable {N : ℕ}

/-- `Valid` as a `Bool`. -/
def validB : SplitTree N → Bool
  | leaf => true
  | node i j l r => (i != j) && l.validB && r.validB

theorem valid_of_validB : ∀ T : SplitTree N, T.validB = true → T.Valid
  | leaf, _ => trivial
  | node i j l r, h => by
    simp only [validB, Bool.and_eq_true, bne_iff_ne] at h
    exact ⟨h.1.1, valid_of_validB l h.1.2, valid_of_validB r h.2⟩

end SplitTree

namespace Sector

variable {N : ℕ}

/-! ### Exponent lists -/

/-- Add `v` to entry `n` of an exponent list, padding with zeros. -/
def addAt : ℕ → ℕ → List ℕ → List ℕ
  | 0, v, [] => [v]
  | 0, v, a :: as => (a + v) :: as
  | n + 1, v, [] => 0 :: addAt n v []
  | n + 1, v, a :: as => a :: addAt n v as

theorem getD_addAt : ∀ (n v : ℕ) (α : List ℕ) (k : ℕ),
    (addAt n v α).getD k 0 = α.getD k 0 + if k = n then v else 0
  | 0, v, [], k => by cases k <;> simp [addAt]
  | 0, v, a :: as, k => by cases k <;> simp [addAt]
  | n + 1, v, [], k => by
    cases k with
    | zero => simp [addAt]
    | succ k => simpa [addAt] using getD_addAt n v [] k
  | n + 1, v, a :: as, k => by
    cases k with
    | zero => simp [addAt]
    | succ k => simpa [addAt] using getD_addAt n v as k

/-- Entrywise sum of exponent lists, padding with zeros. -/
def addExp : List ℕ → List ℕ → List ℕ
  | [], b => b
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addExp as bs

theorem getD_addExp : ∀ (a b : List ℕ) (k : ℕ),
    (addExp a b).getD k 0 = a.getD k 0 + b.getD k 0
  | [], b, k => by simp [addExp]
  | a :: as, [], k => by simp [addExp]
  | a :: as, b :: bs, k => by
    cases k with
    | zero => simp [addExp]
    | succ k => simpa [addExp] using getD_addExp as bs k

/-- Entrywise truncated difference of exponent lists. -/
def subExp : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a - b) :: subExp as bs

theorem getD_subExp : ∀ (a b : List ℕ) (k : ℕ),
    (subExp a b).getD k 0 = a.getD k 0 - b.getD k 0
  | [], b, k => by simp [subExp]
  | a :: as, [], k => by simp [subExp]
  | a :: as, b :: bs, k => by
    cases k with
    | zero => simp [subExp]
    | succ k => simpa [subExp] using getD_subExp as bs k

/-- Entrywise `≤` of exponent lists (missing entries are `0`). -/
def leExp : List ℕ → List ℕ → Bool
  | [], _ => true
  | a :: as, [] => Nat.beq a 0 && leExp as []
  | a :: as, b :: bs => Nat.ble a b && leExp as bs

theorem getD_le_of_leExp : ∀ {a b : List ℕ}, leExp a b = true → ∀ k, a.getD k 0 ≤ b.getD k 0
  | [], b, _, k => by simp
  | a :: as, [], h, k => by
    simp only [leExp, Bool.and_eq_true] at h
    cases k with
    | zero => simp [Nat.eq_of_beq_eq_true h.1]
    | succ k => simpa using getD_le_of_leExp h.2 k
  | a :: as, b :: bs, h, k => by
    simp only [leExp, Bool.and_eq_true, Nat.ble_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k => simpa using getD_le_of_leExp h.2 k

/-- Entrywise minimum (truncation is correct: a missing entry is `0`). -/
def minExp : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs => Nat.min a b :: minExp as bs
  | _, _ => []

/-- The exponent of `yⱼ`: the unit vector `eⱼ`. -/
def unitExp (j : ℕ) : List ℕ := addAt j 1 []

/-! ### Monomials and their pull-backs -/

/-- The monomial `y ^ α = ∏ₖ yₖ ^ αₖ`. -/
def mono (α : List ℕ) (y : Fin N → ℝ) : ℝ := ∏ k : Fin N, y k ^ α.getD k 0

theorem mono_addExp (a b : List ℕ) (y : Fin N → ℝ) :
    mono (addExp a b) y = mono a y * mono b y := by
  simp only [mono, getD_addExp, pow_add, Finset.prod_mul_distrib]

theorem mono_nil (y : Fin N → ℝ) : mono [] y = 1 := by simp [mono]

theorem mono_unitExp (j : Fin N) (y : Fin N → ℝ) : mono (unitExp j) y = y j := by
  simp only [mono, unitExp, getD_addAt, List.getD_nil, zero_add, Fin.val_inj, pow_ite, pow_one,
    pow_zero]
  rw [Finset.prod_ite_eq' Finset.univ j]
  simp

theorem mono_sub_of_le {a m : List ℕ} (h : ∀ k, m.getD k 0 ≤ a.getD k 0) (y : Fin N → ℝ) :
    mono a y = mono m y * mono (subExp a m) y := by
  simp only [mono, getD_subExp, ← Finset.prod_mul_distrib, ← pow_add]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Nat.add_sub_cancel' (h k)]

/-- The pull-back of an exponent under `yᵢ ↦ yⱼ yᵢ`: `α + αᵢ eⱼ`. -/
def pullStep (i j : Fin N) (α : List ℕ) : List ℕ := addAt j (α.getD i 0) α

theorem mono_splitMap (i j : Fin N) (α : List ℕ) (y : Fin N → ℝ) :
    mono α (splitMap i j y) = mono (pullStep i j α) y := by
  have hL : mono α (splitMap i j y) = y j ^ α.getD i 0 * mono α y := by
    have e : (fun k : Fin N => splitMap i j y k ^ α.getD k 0) =
        Function.update (fun k => y k ^ α.getD k 0) i ((y j * y i) ^ α.getD i 0) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp [splitMap]
      · simp [splitMap, Function.update_of_ne hk]
    rw [mono, e, Finset.prod_update_of_mem (Finset.mem_univ i), mono,
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i), mul_pow]
    ring
  rw [hL, mono, mono, pullStep]
  simp only [getD_addAt, pow_add, Finset.prod_mul_distrib, Fin.val_inj, pow_ite, pow_zero]
  rw [Finset.prod_ite_eq' Finset.univ j]
  simp only [Finset.mem_univ, ite_true]
  ring

/-- The pull-back of an exponent along a leaf path. -/
def pullExp : List (Fin N × Fin N) → List ℕ → List ℕ
  | [], α => α
  | p :: ps, α => pullExp ps (pullStep p.1 p.2 α)

theorem mono_pullExp : ∀ (ps : List (Fin N × Fin N)) (α : List ℕ) (y : Fin N → ℝ),
    mono (pullExp ps α) y = mono α (leafMap ps y)
  | [], α, y => rfl
  | p :: ps, α, y => by
    rw [pullExp, mono_pullExp ps, leafMap, mono_splitMap]

/-- The exponent of the Jacobian monomial of a leaf. -/
def jacExp : List (Fin N × Fin N) → List ℕ
  | [] => []
  | p :: ps => addExp (jacExp ps) (pullExp ps (unitExp p.2))

theorem leafJac_eq_mono : ∀ (ps : List (Fin N × Fin N)) (y : Fin N → ℝ),
    leafJac ps y = mono (jacExp ps) y
  | [], y => (mono_nil y).symm
  | p :: ps, y => by
    rw [leafJac, jacExp, mono_addExp, leafJac_eq_mono ps, mono_pullExp, mono_unitExp]

/-! ### Sparse polynomials with natural coefficients -/

/-- A sparse polynomial `Σ cₜ y ^ αₜ` with natural coefficients. -/
abbrev NPoly := List (List ℕ × ℕ)

/-- Evaluation of a sparse polynomial. -/
def NPoly.eval (P : NPoly) (y : Fin N → ℝ) : ℝ := (P.map fun t => (t.2 : ℝ) * mono t.1 y).sum

/-- The pull-back of a polynomial along a leaf path. -/
def NPoly.pull (ps : List (Fin N × Fin N)) (P : NPoly) : NPoly :=
  P.map fun t => (pullExp ps t.1, t.2)

/-- Division by the monomial `y ^ m` (exponent subtraction). -/
def NPoly.shift (m : List ℕ) (P : NPoly) : NPoly := P.map fun t => (subExp t.1 m, t.2)

theorem NPoly.eval_pull (ps : List (Fin N × Fin N)) (P : NPoly) (y : Fin N → ℝ) :
    (P.pull ps).eval y = P.eval (leafMap ps y) := by
  simp only [NPoly.eval, NPoly.pull, List.map_map, Function.comp_def, mono_pullExp]

/-- The componentwise minimal exponent of a polynomial. -/
def NPoly.minE : NPoly → List ℕ
  | [] => []
  | [t] => t.1
  | t :: ts => minExp t.1 (NPoly.minE ts)

/-- The leaf test: every exponent is `≥ m`, and some term with nonzero coefficient has exponent
exactly `m`. -/
def leafOk (m : List ℕ) (P : NPoly) : Bool :=
  P.all (fun t => leExp m t.1) && P.any (fun t => leExp t.1 m && (t.2 != 0))

theorem eval_eq_mono_mul_of_leafOk {m : List ℕ} {P : NPoly} (h : leafOk m P = true)
    (y : Fin N → ℝ) : P.eval y = mono m y * (P.shift m).eval y := by
  simp only [leafOk, Bool.and_eq_true, List.all_eq_true] at h
  simp only [NPoly.eval, NPoly.shift, List.map_map, Function.comp_def, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  rw [mono_sub_of_le (getD_le_of_leExp (h.1 t ht)) y]
  ring

theorem eval_nonneg (P : NPoly) {y : Fin N → ℝ} (hy : ∀ k, 0 ≤ y k) : 0 ≤ P.eval y := by
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun k _ => pow_nonneg (hy k) _)

/-- On a leaf that passes the test, the cofactor `P̃ = P / y ^ m` is `≥ 1` on the closed orthant. -/
theorem one_le_eval_shift {m : List ℕ} {P : NPoly} (h : leafOk m P = true) {y : Fin N → ℝ}
    (hy : ∀ k, 0 ≤ y k) : 1 ≤ (P.shift m).eval y := by
  simp only [leafOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, bne_iff_ne] at h
  obtain ⟨⟨t, ht, hle, hc⟩, -⟩ := And.intro h.2 h.1
  have hm : ∀ k, (subExp t.1 m).getD k 0 = 0 := fun k => by
    rw [getD_subExp]; exact Nat.sub_eq_zero_of_le (getD_le_of_leExp hle k)
  have h1 : mono (subExp t.1 m) y = 1 := by
    simp only [mono, hm, pow_zero, Finset.prod_const_one]
  have hmem : ((t.2 : ℝ) * mono (subExp t.1 m) y) ∈
      ((P.shift m).map fun t => (t.2 : ℝ) * mono t.1 y) := by
    refine List.mem_map.mpr ⟨(subExp t.1 m, t.2), List.mem_map.mpr ⟨t, ht, rfl⟩, rfl⟩
  have hle1 := List.single_le_sum (fun x hx => by
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun k _ => pow_nonneg (hy k) _))
    _ hmem
  rw [h1, mul_one] at hle1
  have : (1 : ℝ) ≤ t.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
  exact this.trans hle1

/-! ### The certificate -/

/-- A sector certificate: a splitting tree and the polynomials of the integrand. -/
structure SDCert (N : ℕ) where
  /-- The splitting tree. -/
  tree : SplitTree N
  /-- The polynomials whose leaf factorization is certified. -/
  polys : List NPoly

/-- The checker: the tree is valid and every polynomial passes the leaf test on every leaf. -/
def SDCert.check (c : SDCert N) : Bool :=
  c.tree.validB && c.tree.paths.all fun ps =>
    c.polys.all fun P => leafOk (NPoly.minE (P.pull ps)) (P.pull ps)

/-- **Soundness of the sector checker.** If the check passes, then for every integrable `g` the
cube integral is the sum of the leaf integrals, every leaf integrand is integrable, the leaf
Jacobians are monomials, and every certified polynomial factorizes on every leaf as
`P(φ_σ(y)) = y ^ m · P̃(y)` with `P̃` a polynomial with natural coefficients, `P̃ ≥ 1` on the
closed orthant. -/
theorem SDCert.sound {c : SDCert N} (h : c.check = true) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : (Fin N → ℝ) → E} (hg : IntegrableOn g (unitCube N)) :
    (∀ ps ∈ c.tree.paths, IntegrableOn (leafIntegrand g ps) (unitCube N)) ∧
    (∫ y in unitCube N, g y =
      (c.tree.paths.map fun ps => ∫ y in unitCube N, leafIntegrand g ps y).sum) ∧
    ∀ ps ∈ c.tree.paths, (∀ y, leafJac ps y = mono (jacExp ps) y) ∧
      ∀ P ∈ c.polys, ∃ (m : List ℕ) (Q : NPoly),
        (∀ y, P.eval (leafMap ps y) = mono m y * Q.eval y) ∧
        ∀ y : Fin N → ℝ, (∀ k, 0 ≤ y k) → 1 ≤ Q.eval y := by
  simp only [SDCert.check, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hv, hl⟩ := h
  obtain ⟨hi, he⟩ := SplitTree.integral_eq_sum c.tree (SplitTree.valid_of_validB _ hv) hg
  refine ⟨hi, he, fun ps hps => ⟨leafJac_eq_mono ps, fun P hP => ?_⟩⟩
  have hok := hl ps hps P hP
  refine ⟨NPoly.minE (P.pull ps), (P.pull ps).shift (NPoly.minE (P.pull ps)), fun y => ?_,
    fun y hy => one_le_eval_shift hok hy⟩
  rw [← NPoly.eval_pull, eval_eq_mono_mul_of_leafOk hok]

end Sector

end QED.DimReg
