/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertLocal
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Split IBP certificates with packed labels, checked at integer points (layer L2)

A large reduction is certified as a chain of steps. Each step (`QED.Algebra.IBPCert.Step`)
proves one *relation* `P = Σ pₗ(d) [l] = 0` (its `claim`) as a combination with multipliers in
`ℤ[d]` of IBP relations at its seeds and of relations proved by earlier steps (`rels`), up to
labels it declares zero (`zeros`). Relations are polynomial identities, so no step introduces
exceptional values of `d`; only the last step, of the form `q [T] - Σ nⱼ [Mⱼ]`, is divided by
`q(d)` (`QED.Algebra.IBPCert.Step.reduction`).

The checker is designed for the kernel:

* **Packed labels.** An index vector `ν` with entries in `[-o, B - o)` is packed into the natural
  number `Σ_a (ν_a + o) Bᵃ` (`QED.Algebra.IBPCert.pack`), so that labels are compared with one
  `Nat.blt`. The checker verifies the range of every label it packs; then the packed number
  decodes back to `ν` (`QED.Algebra.IBPCert.decodeVec_pack`).
* **Evaluation at points.** Instead of multiplying polynomials, every coefficient is evaluated at
  the integer points `x = 0, …, n - 1` and the combination is checked to vanish at each point.
  All polynomials involved have fewer than `n` coefficients (checked), so the identity holds for
  every `d` (`QED.Algebra.IBPCert.PolyLt.eq_zero`, from Lagrange interpolation in Mathlib).

## Main statements

* `QED.Algebra.IBPCert.Step.sound`: if `Step.check` accepts, the IBP relations hold at the
  step's seeds, the integrals of its `zeros` vanish, and its `rels` hold, then its claim holds.
  The hypotheses are local (seeds and labels of the step only), in a field of characteristic `0`.
* `QED.Algebra.IBPCert.Step.reduction`: a claim `q [T] - Σ nⱼ [Mⱼ]` gives
  `I(T) = Σ (nⱼ(d) / q(d)) I(Mⱼ)` where `q(d) ≠ 0`.
-/

@[expose] public section

namespace QED.Algebra.IBPCert

/-! ### Polynomial functions of bounded degree -/

/-- `Φ` is a polynomial function of degree `< n`. -/
def PolyLt {K : Type*} [Field K] (n : ℕ) (Φ : K → K) : Prop :=
  ∃ Q : Polynomial K, (∀ m, n ≤ m → Q.coeff m = 0) ∧ ∀ y, Φ y = Q.eval y

namespace PolyLt

variable {K : Type*} [Field K] {n : ℕ}

theorem zero : PolyLt n (fun _ : K => 0) := ⟨0, fun _ _ => rfl, fun _ => by simp⟩

theorem add {Φ Ψ : K → K} (h : PolyLt n Φ) (h' : PolyLt n Ψ) : PolyLt n (fun y => Φ y + Ψ y) := by
  obtain ⟨Q, hQ, hΦ⟩ := h
  obtain ⟨Q', hQ', hΨ⟩ := h'
  exact ⟨Q + Q', fun m hm => by simp [hQ m hm, hQ' m hm], fun y => by simp [hΦ, hΨ]⟩

theorem mul_const {Φ : K → K} (h : PolyLt n Φ) (c : K) : PolyLt n (fun y => Φ y * c) := by
  obtain ⟨Q, hQ, hΦ⟩ := h
  exact ⟨Q * Polynomial.C c, fun m hm => by simp [hQ m hm], fun y => by simp [hΦ]⟩

theorem const_mul {Φ : K → K} (h : PolyLt n Φ) (c : K) : PolyLt n (fun y => c * Φ y) := by
  simpa [mul_comm] using h.mul_const c

theorem listSum {α : Type*} (f : α → K → K) :
    ∀ (L : List α), (∀ a ∈ L, PolyLt n (f a)) → PolyLt n (fun y => (L.map fun a => f a y).sum)
  | [], _ => by simp only [List.map_nil, List.sum_nil]; exact zero
  | a :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (listSum f L fun b hb => h b (by simp [hb]))

theorem coeff_toPolynomial : ∀ (p : Poly) (m : ℕ),
    (Poly.toPolynomial p : Polynomial K).coeff m = (p.getD m 0 : K)
  | [], m => by simp [Poly.toPolynomial]
  | a :: p, 0 => by simp [Poly.toPolynomial]
  | a :: p, m + 1 => by
    rw [Poly.toPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul,
      coeff_toPolynomial p m]
    simp

theorem ofPoly (p : Poly) (hp : p.length ≤ n) : PolyLt n (fun y : K => Poly.eval y p) := by
  refine ⟨Poly.toPolynomial p, fun m hm => ?_, fun y => (Poly.eval_toPolynomial y p).symm⟩
  rw [coeff_toPolynomial, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  simp

/-- **Interpolation.** A polynomial function of degree `< n` vanishing at `0, 1, …, n - 1`
vanishes identically (characteristic `0`). -/
theorem eq_zero [CharZero K] {Φ : K → K} (h : PolyLt n Φ) (hpts : ∀ x : ℕ, x < n → Φ x = 0)
    (y : K) : Φ y = 0 := by
  classical
  obtain ⟨Q, hQ, hΦ⟩ := h
  let s : Finset K := (Finset.range n).image (fun x : ℕ => (x : K))
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hdeg : Q.degree < s.card := by
    rw [hs, Polynomial.degree_lt_iff_coeff_zero]; exact hQ
  have h0 : Q = 0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s hdeg (by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    rw [← hΦ]; exact hpts k (Finset.mem_range.1 hk))
  rw [hΦ, h0, Polynomial.eval_zero]

end PolyLt

theorem Poly.length_add : ∀ p q : Poly, (Poly.add p q).length = max p.length q.length
  | [], q => by simp [Poly.add]
  | a :: p, [] => by simp [Poly.add]
  | a :: p, b :: q => by simp [Poly.add, Poly.length_add p q, Nat.succ_max_succ]

theorem Poly.length_smul (c : ℤ) : ∀ p : Poly, (Poly.smul c p).length = p.length
  | [] => rfl
  | a :: p => by simp [Poly.smul, Poly.length_smul c p]

theorem Poly.length_mul_le : ∀ p q : Poly, (Poly.mul p q).length ≤ p.length + q.length
  | [], q => by simp [Poly.mul]
  | a :: p, q => by
    have := Poly.length_mul_le p q
    simp only [Poly.mul, Poly.length_add, Poly.length_smul, List.length_cons]
    omega

/-! ### Packed labels -/

/-- `x + o ∈ [0, B)`. -/
def inDigit (B o : ℕ) (x : ℤ) : Bool :=
  match Int.add x (.ofNat o) with
  | .ofNat k => Nat.blt k B
  | .negSucc _ => false

/-- A label of length `n` with all entries in `[-o, B - o)`. -/
def inRange (B o n : ℕ) (l : List ℤ) : Bool := Nat.beq l.length n && l.all (inDigit B o)

/-- The packed label `Σ_a (l_a + o) Bᵃ`. -/
def pack (B o : ℕ) : List ℤ → ℕ
  | [] => 0
  | x :: l => Int.toNat (Int.add x (.ofNat o)) + B * pack B o l

/-- The `a`-th entry of a packed label. -/
def digit (B o c a : ℕ) : ℤ := ((c / B ^ a % B : ℕ) : ℤ) - o

/-- The index vector of a packed label. -/
def decodeVec (n B o c : ℕ) : Fin n → ℤ := fun a => digit B o c a

theorem inDigit_spec {B o : ℕ} {x : ℤ} (h : inDigit B o x = true) :
    ∃ k : ℕ, k < B ∧ x + o = k := by
  unfold inDigit at h
  rw [Poly.int_add_eq] at h
  revert h
  generalize hy : x + (Int.ofNat o) = y
  intro h
  cases y with
  | ofNat k =>
    simp only [Nat.blt_eq] at h
    exact ⟨k, h, rfl⟩
  | negSucc _ => simp at h

theorem digit_pack {B o : ℕ} : ∀ {l : List ℤ}, (∀ x ∈ l, inDigit B o x = true) →
    ∀ a < l.length, digit B o (pack B o l) a = l.getD a 0
  | [], _, a, ha => by simp at ha
  | x :: l, h, a, ha => by
    obtain ⟨k, hk, hx⟩ := inDigit_spec (h x (by simp))
    have hB : 0 < B := by omega
    have hpk : pack B o (x :: l) = k + B * pack B o l := by
      simp only [pack, Poly.int_add_eq]; rw [show x + Int.ofNat o = (k : ℤ) by simpa using hx]
      rfl
    cases a with
    | zero =>
      simp only [digit, hpk, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hk, List.getD_cons_zero]
      omega
    | succ a =>
      have hdiv : (k + B * pack B o l) / B ^ (a + 1) = pack B o l / B ^ a := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
          Nat.div_eq_of_lt hk, zero_add]
      simp only [List.length_cons] at ha
      rw [List.getD_cons_succ, ← digit_pack (fun y hy => h y (by simp [hy])) a (by omega)]
      simp only [digit, hpk, hdiv]

theorem decodeVec_pack {B o n : ℕ} {l : List ℤ} (h : inRange B o n l = true) :
    decodeVec n B o (pack B o l) = toVec n l := by
  simp only [inRange, Bool.and_eq_true, List.all_eq_true] at h
  have hl := Nat.eq_of_beq_eq_true h.1
  funext a
  exact digit_pack h.2 a (by omega)

/-! ### Combinations with value vectors -/

/-- A combination of packed labels whose coefficients are vectors of values at the points
`0, 1, …`. -/
abbrev VComb := List (ℕ × List ℤ)

namespace VComb

variable {K : Type*} [CommRing K] (J : ℕ → K) (x : ℕ)

/-- The value at the point `x`: `Σ vₗ[x] · J l`. -/
def evalAt : VComb → K
  | [] => 0
  | t :: ts => (t.2.getD x 0 : K) * J t.1 + evalAt ts

@[simp] theorem evalAt_nil : evalAt J x [] = 0 := rfl

@[simp] theorem evalAt_cons (t : ℕ × List ℤ) (ts : VComb) :
    evalAt J x (t :: ts) = (t.2.getD x 0 : K) * J t.1 + evalAt J x ts := rfl

theorem getD_eq_zero_of_isZero' : ∀ (y : ℕ) {v : List ℤ}, Poly.isZero v = true → v.getD y 0 = 0
  | _, [], _ => by simp
  | y, a :: v, h => by
    simp only [Poly.isZero, Bool.and_eq_true] at h
    cases y with
    | zero => simp [eq_zero_of_intIsZero h.1]
    | succ y => rw [List.getD_cons_succ]; exact getD_eq_zero_of_isZero' y h.2

theorem getD_eq_zero_of_isZero {v : List ℤ} (h : Poly.isZero v = true) : v.getD x 0 = 0 :=
  getD_eq_zero_of_isZero' x h

/-- Merge step (as `LinComb.addCons`, with packed labels). -/
def addCons (t : ℕ × List ℤ) (ts : VComb) (rec : VComb → VComb) : VComb → VComb
  | [] => t :: ts
  | u :: us =>
    match natCmp t.1 u.1 with
    | .lt => t :: rec (u :: us)
    | .gt => u :: addCons t ts rec us
    | .eq =>
      let p := Poly.add t.2 u.2
      bif Poly.isZero p then rec us else (t.1, p) :: rec us

/-- Merge of two combinations sorted by label. -/
def add : VComb → VComb → VComb
  | [], m => m
  | t :: ts, m => addCons t ts (add ts) m

theorem evalAt_addCons (t : ℕ × List ℤ) (ts : VComb) (rec : VComb → VComb)
    (hrec : ∀ m, evalAt J x (rec m) = evalAt J x ts + evalAt J x m) :
    ∀ m, evalAt J x (addCons t ts rec m) = evalAt J x (t :: ts) + evalAt J x m
  | [] => by simp [addCons]
  | u :: us => by
    unfold addCons
    cases h : natCmp t.1 u.1
    · simp only [evalAt_cons, hrec]; ring
    · have hl := eq_of_natCmp_eq h
      cases hz : Poly.isZero (Poly.add t.2 u.2)
      · simp only [hz, Bool.cond_false, evalAt_cons, hrec, getD_polyAdd, hl]; push_cast; ring
      · have h0 := getD_eq_zero_of_isZero x hz
        rw [getD_polyAdd] at h0
        have h0' : ((t.2.getD x 0 : ℤ) : K) + ((u.2.getD x 0 : ℤ) : K) = 0 := by
          rw [← Int.cast_add, h0, Int.cast_zero]
        simp only [hz, Bool.cond_true, hrec, evalAt_cons, hl]
        linear_combination (-J u.1) * h0'
    · simp only [evalAt_cons, evalAt_addCons t ts rec hrec us]; ring

theorem evalAt_add : ∀ l m : VComb, evalAt J x (add l m) = evalAt J x l + evalAt J x m
  | [], m => by simp [add]
  | t :: ts, m => evalAt_addCons J x t ts (add ts) (evalAt_add ts) m

/-- One round of pairwise merging. -/
def pairs : List VComb → List VComb
  | [] => []
  | [l] => [l]
  | l :: m :: rest => add l m :: pairs rest

/-- Balanced merging. -/
def sumTree : ℕ → List VComb → VComb
  | 0, ls => ls.foldr add []
  | k + 1, ls =>
    match ls with
    | [] => []
    | [l] => l
    | l :: m :: rest => sumTree k (pairs (l :: m :: rest))

theorem sum_pairs : ∀ ls : List VComb,
    ((pairs ls).map (evalAt J x)).sum = (ls.map (evalAt J x)).sum
  | [] => rfl
  | [_] => rfl
  | l :: m :: rest => by
    simp only [pairs, List.map_cons, List.sum_cons, evalAt_add, sum_pairs rest]; ring

theorem evalAt_foldr_add : ∀ ls : List VComb,
    evalAt J x (ls.foldr add []) = (ls.map (evalAt J x)).sum
  | [] => rfl
  | l :: ls => by simp [evalAt_add, evalAt_foldr_add ls]

theorem evalAt_sumTree : ∀ (k : ℕ) (ls : List VComb),
    evalAt J x (sumTree k ls) = (ls.map (evalAt J x)).sum
  | 0, ls => evalAt_foldr_add J x ls
  | _ + 1, [] => by simp [sumTree]
  | _ + 1, [l] => by simp [sumTree]
  | k + 1, l :: m :: rest => by
    rw [sumTree, evalAt_sumTree k, sum_pairs]

/-- Sorting (and merging) a list of terms by balanced merging of singletons. -/
def sort (l : VComb) : VComb := sumTree 64 (l.map fun t => [t])

theorem evalAt_sort (l : VComb) : evalAt J x (sort l) = evalAt J x l := by
  rw [sort, evalAt_sumTree, List.map_map]
  induction l with
  | nil => rfl
  | cons t l ih => simp [ih]

/-- Every term has a zero vector or a label declared zero by `z`. -/
def vanishes (z : ℕ → Bool) (l : VComb) : Bool := l.all fun t => z t.1 || Poly.isZero t.2

theorem evalAt_eq_zero_of_vanishes {z : ℕ → Bool} (hz : ∀ l, z l = true → J l = 0) :
    ∀ {l : VComb}, vanishes z l = true → evalAt J x l = 0
  | [], _ => rfl
  | t :: ts, h => by
    simp only [vanishes, List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at h
    rw [evalAt_cons, evalAt_eq_zero_of_vanishes hz (l := ts) h.2]
    rcases h.1 with h1 | h1
    · simp [hz _ h1]
    · rw [getD_eq_zero_of_isZero x h1]; simp

theorem evalAt_map {α : Type*} (f : α → ℕ × List ℤ) (L : List α) :
    evalAt J x (L.map f) = (L.map fun a => ((f a).2.getD x 0 : K) * J (f a).1).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

end VComb

/-! ### Integer evaluation -/

/-- `p(x)` for an integer `x`, by Horner's rule. -/
def evalZ (x : ℤ) : Poly → ℤ
  | [] => 0
  | a :: p => Int.add a (Int.mul x (evalZ x p))

theorem cast_evalZ {K : Type*} [CommRing K] (x : ℤ) : ∀ p : Poly,
    ((evalZ x p : ℤ) : K) = Poly.eval (x : K) p
  | [] => by simp [evalZ]
  | a :: p => by
    simp only [evalZ, Poly.int_add_eq, Poly.int_mul_eq, Poly.eval_cons, Int.cast_add,
      Int.cast_mul, cast_evalZ x p]

/-- The values `p(0), …, p(n - 1)`. -/
def vals (n : ℕ) (p : Poly) : List ℤ := (List.range n).map fun x => evalZ (.ofNat x) p

theorem getD_vals {n x : ℕ} (hx : x < n) (p : Poly) : (vals n p).getD x 0 = evalZ x p := by
  simp [vals, List.getD_eq_getElem?_getD, hx]

/-- Pointwise product of value vectors. -/
def vmul : List ℤ → List ℤ → List ℤ
  | a :: u, b :: v => Int.mul a b :: vmul u v
  | _, _ => []

theorem getD_vmul : ∀ (u v : List ℤ) (x : ℕ), (vmul u v).getD x 0 = u.getD x 0 * v.getD x 0
  | [], v, x => by simp [vmul]
  | a :: u, [], x => by simp [vmul]
  | a :: u, b :: v, 0 => by simp [vmul]
  | a :: u, b :: v, x + 1 => by simp only [vmul, List.getD_cons_succ]; exact getD_vmul u v x

/-- The vector `(v[x] (a + b x))ₓ`, starting at the point `x₀`. -/
def scaleAff (a b : ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | x, v :: vs => Int.mul v (Int.add a (Int.mul b (.ofNat x))) :: scaleAff a b (x + 1) vs

theorem getD_scaleAff (a b : ℤ) : ∀ (x₀ : ℕ) (v : List ℤ) (x : ℕ),
    (scaleAff a b x₀ v).getD x 0 = v.getD x 0 * (a + b * (x₀ + x : ℕ))
  | _, [], x => by simp [scaleAff]
  | x₀, c :: v, 0 => by simp [scaleAff]
  | x₀, c :: v, x + 1 => by
    simp only [scaleAff, List.getD_cons_succ, getD_scaleAff a b (x₀ + 1) v x]
    congr 3; omega

/-! ### Steps -/

/-- One step of a split certificate: the claim `Σ pₗ [l] = 0` as a combination of the IBP
relations at `seeds` (multipliers in the seeds) and of earlier relations `rels` (with
multipliers), up to the labels `zeros`; checked at the points `0, …, npts - 1`. -/
structure Step where
  /-- The relation proved by this step. -/
  claim : List (List ℤ × Poly)
  /-- The number of evaluation points. -/
  npts : ℕ
  /-- IBP seeds with multipliers. -/
  seeds : List Seed
  /-- Relations proved earlier, with multipliers. -/
  rels : List (List (List ℤ × Poly) × Poly)
  /-- Labels treated as vanishing. -/
  zeros : List (List ℤ)

namespace Step

variable (F : Family) (B o : ℕ) (c : Step)

/-- The claim, negated, as value vectors. -/
def claimVec : VComb := VComb.sort (c.claim.map fun t => (pack B o t.1, vals c.npts (Poly.neg t.2)))

/-- The coefficient `c0 + cnu ν_idx` of a template term at a seed. -/
def termConst (s : Seed) (t : Term) : ℤ := Int.add t.c0 (Int.mul t.cnu (s.nu.getD t.idx 0))

/-- A seed relation times its multiplier, given the values `mv` of the multiplier. -/
def seedVecOf (s : Seed) (mv : List ℤ) : VComb :=
  VComb.sort <| (F.tmplAt s.i s.j).map fun t =>
    (pack B o (Poly.add s.nu t.shift), scaleAff (termConst s t) t.cd 0 mv)

/-- An earlier relation times its multiplier, given the values `mv` of the multiplier. -/
def relVecOf (n : ℕ) (r : List (List ℤ × Poly)) (mv : List ℤ) : VComb :=
  VComb.sort (r.map fun t => (pack B o t.1, vmul mv (vals n t.2)))

/-- The admissibility conditions: template, seeds, ranges of all labels, degree bounds. -/
def admissible : Bool :=
  let N := F.nProp
  let n := c.npts
  F.tmplOk && c.seeds.all (Seed.ok F) &&
  c.seeds.all (fun s => Nat.ble (s.mult.length + 2) n &&
    (F.tmplAt s.i s.j).all fun t => inRange B o N (Poly.add s.nu t.shift)) &&
  c.claim.all (fun t => inRange B o N t.1 && Nat.ble t.2.length n) &&
  c.rels.all (fun r => r.1.all fun t =>
    inRange B o N t.1 && Nat.ble (t.2.length + r.2.length) n) &&
  c.zeros.all (fun l => inRange B o N l && F.zeroPred l)

/-- The step checker. -/
def check : Bool :=
  admissible F B o c &&
    VComb.vanishes (fun l => (c.zeros.map (pack B o)).any (Nat.beq l))
      (VComb.sumTree 64 (claimVec B o c ::
        (c.seeds.map fun s => seedVecOf F B o s (vals c.npts s.mult)) ++
        (c.rels.map fun r => relVecOf B o c.npts r.1 (vals c.npts r.2))))

end Step

/-! ### Soundness -/

theorem sum_map_mul_left {α K : Type*} [CommRing K] (a : K) (f : α → K) :
    ∀ L : List α, (L.map fun x => a * f x).sum = a * (L.map f).sum
  | [] => by simp
  | x :: L => by simp [sum_map_mul_left a f L, mul_add]

theorem sum_map_neg_eval {K : Type*} [CommRing K] (J : List ℤ → K) (y : K) :
    ∀ L : List (List ℤ × Poly),
      (L.map fun t => Poly.eval y (Poly.neg t.2) * J t.1).sum = -LinComb.eval J y L
  | [] => by simp
  | t :: L => by
    rw [List.map_cons, List.sum_cons, sum_map_neg_eval J y L, LinComb.eval_cons, Poly.eval_neg]
    ring

theorem cast_natCast_int {K : Type*} [CommRing K] (x : ℕ) : (((x : ℤ) : K)) = (x : K) := by
  simp

namespace Step

variable {F : Family} {B o : ℕ} {c : Step}

/-- **Soundness of a step.** If the check passes, the IBP relations hold at the step's seeds, the
integrals of its `zeros` vanish and the relations `rels` hold at `d`, then the claim holds at
`d`. -/
theorem sound {K : Type*} [Field K] [CharZero K] (h : c.check F B o = true)
    (I : (Fin F.nProp → ℤ) → K → K) (d : K)
    (hI : ∀ s ∈ c.seeds, F.IBPHoldsAt I d s.i s.j (toVec F.nProp s.nu))
    (hz : ∀ l ∈ c.zeros, I (toVec F.nProp l) d = 0)
    (hr : ∀ r ∈ c.rels, LinComb.eval (fun l => I (toVec F.nProp l) d) d r.1 = 0) :
    LinComb.eval (fun l => I (toVec F.nProp l) d) d c.claim = 0 := by
  set Jl : List ℤ → K := fun l => I (toVec F.nProp l) d with hJl
  set Jn : ℕ → K := fun l => I (decodeVec F.nProp B o l) d with hJn
  simp only [check, admissible, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨ht, hsok⟩, hseed⟩, hclaim⟩, hrel⟩, hzero⟩, hvan⟩ := h
  set n := c.npts
  have hJ : ∀ l, inRange B o F.nProp l = true → Jn (pack B o l) = Jl l := by
    intro l hl; simp only [hJn, hJl, decodeVec_pack hl]
  -- the polynomial function whose values the checker computes
  let Φ : K → K := fun y =>
    (c.claim.map fun t => Poly.eval y (Poly.neg t.2) * Jl t.1).sum +
    (c.seeds.map fun s => ((F.tmplAt s.i s.j).map fun t =>
      Poly.eval y (Poly.mul s.mult [termConst s t, t.cd]) * Jl (Poly.add s.nu t.shift)).sum).sum +
    (c.rels.map fun r => (r.1.map fun t => Poly.eval y (Poly.mul r.2 t.2) * Jl t.1).sum).sum
  have hpoly : PolyLt n Φ := by
    refine ((PolyLt.listSum _ _ fun t ht => ?_).add (PolyLt.listSum _ _ fun s hs => ?_)).add
      (PolyLt.listSum _ _ fun r hr => ?_)
    · refine (PolyLt.ofPoly _ ?_).mul_const _
      have := (hclaim t ht).2
      simp only [Nat.ble_eq] at this
      simpa [Poly.neg, Poly.length_smul] using this
    · refine PolyLt.listSum _ _ fun t _ => (PolyLt.ofPoly _ ?_).mul_const _
      have h1 := (hseed s hs).1
      simp only [Nat.ble_eq] at h1
      have := Poly.length_mul_le s.mult [termConst s t, t.cd]
      simp only [List.length_cons, List.length_nil] at this
      omega
    · refine PolyLt.listSum _ _ fun t ht => (PolyLt.ofPoly _ ?_).mul_const _
      have h1 := (hrel r hr t ht).2
      simp only [Nat.ble_eq] at h1
      have := Poly.length_mul_le r.2 t.2
      omega
  -- its values at the points are the checker's values
  have hpts : ∀ x : ℕ, x < n → Φ x = 0 := by
    intro x hx
    have hv := VComb.evalAt_eq_zero_of_vanishes Jn x (z := fun l =>
      (c.zeros.map (pack B o)).any (Nat.beq l)) (by
        intro l hl
        simp only [List.any_eq_true, List.mem_map] at hl
        obtain ⟨_, ⟨m, hm, rfl⟩, hb⟩ := hl
        rw [Nat.eq_of_beq_eq_true hb, hJ m (hzero m hm).1]; exact hz m hm) hvan
    rw [VComb.evalAt_sumTree] at hv
    simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
      add_assoc] at hv
    rw [← hv]
    simp only [Φ, add_assoc]
    congr 1
    · rw [claimVec, VComb.evalAt_sort, VComb.evalAt_map]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      rw [getD_vals hx, cast_evalZ, cast_natCast_int, hJ t.1 (hclaim t ht).1]
    congr 1
    · refine congrArg List.sum (List.map_congr_left fun s hs => ?_)
      simp only [Function.comp_apply, seedVecOf, VComb.evalAt_sort, VComb.evalAt_map]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      rw [getD_scaleAff, getD_vals hx, hJ _ ((hseed s hs).2 t ht), Poly.eval_mul]
      simp only [Int.cast_mul, Int.cast_add, cast_evalZ, cast_natCast_int, Poly.eval_cons,
        Poly.eval_nil, zero_add]
      ring
    · refine congrArg List.sum (List.map_congr_left fun r hr' => ?_)
      simp only [Function.comp_apply, relVecOf, VComb.evalAt_sort, VComb.evalAt_map]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      rw [getD_vmul, getD_vals hx, getD_vals hx, hJ _ (hrel r hr' t ht).1, Poly.eval_mul]
      simp only [Int.cast_mul, cast_evalZ, cast_natCast_int]
  have hΦ := hpoly.eq_zero hpts d
  -- at `d` the seed and relation parts vanish
  have hseeds : (c.seeds.map fun s => ((F.tmplAt s.i s.j).map fun t =>
      Poly.eval d (Poly.mul s.mult [termConst s t, t.cd]) * Jl (Poly.add s.nu t.shift)).sum).sum
      = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    have hok := hsok s hs
    simp only [Seed.ok, Bool.and_eq_true, Nat.blt_eq] at hok
    obtain ⟨⟨hi, hj⟩, hl⟩ := hok
    have hl : s.nu.length = F.nProp := Nat.eq_of_beq_eq_true hl
    have := hI s hs
    unfold Family.IBPHoldsAt at this
    rw [← F.tmplAt_eq_template ht hi hj] at this
    have e : ((F.tmplAt s.i s.j).map fun t =>
        Poly.eval d (Poly.mul s.mult [termConst s t, t.cd]) * Jl (Poly.add s.nu t.shift)) =
        (F.tmplAt s.i s.j).map fun t => Poly.eval d s.mult *
          (t.coeff d (toVec F.nProp s.nu) *
            I (toVec F.nProp s.nu + toVec F.nProp t.shift) d) := by
      refine List.map_congr_left fun t _ => ?_
      simp only [Poly.eval_mul, Poly.eval_cons, Poly.eval_nil, hJl, toVec_polyAdd, Term.coeff,
        vecGet_toVec hl, termConst, Poly.int_add_eq, Poly.int_mul_eq]
      push_cast; ring
    rw [e, sum_map_mul_left, this, mul_zero]
  have hrels : (c.rels.map fun r =>
      (r.1.map fun t => Poly.eval d (Poly.mul r.2 t.2) * Jl t.1).sum).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    have e : (r.1.map fun t => Poly.eval d (Poly.mul r.2 t.2) * Jl t.1) =
        r.1.map fun t => Poly.eval d r.2 * (Poly.eval d t.2 * Jl t.1) := by
      refine List.map_congr_left fun t _ => ?_
      rw [Poly.eval_mul]; ring
    rw [e, sum_map_mul_left, ← LinComb.eval_eq_sum, hr r hr', mul_zero]
  have hc := hΦ
  simp only [Φ] at hc
  rw [hseeds, hrels, sum_map_neg_eval] at hc
  linear_combination -hc

/-- A list of relations (with multipliers) all hold; reduces to a conjunction on literal lists,
so a chain of steps supplies it as an anonymous constructor. -/
def RelsHold {K : Type*} [CommRing K] (J : List ℤ → K) (d : K) :
    List (List (List ℤ × Poly) × Poly) → Prop
  | [] => True
  | r :: rs => LinComb.eval J d r.1 = 0 ∧ RelsHold J d rs

theorem RelsHold.forall {K : Type*} [CommRing K] {J : List ℤ → K} {d : K} :
    ∀ {rs : List (List (List ℤ × Poly) × Poly)}, RelsHold J d rs →
      ∀ r ∈ rs, LinComb.eval J d r.1 = 0
  | [], _, r, hr => by simp at hr
  | r' :: rs, h, r, hr => by
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h.1
    · exact RelsHold.forall h.2 r hr

/-- `Step.sound` with the earlier relations given as `RelsHold`. -/
theorem sound' {K : Type*} [Field K] [CharZero K] (h : c.check F B o = true)
    (I : (Fin F.nProp → ℤ) → K → K) (d : K)
    (hI : ∀ s ∈ c.seeds, F.IBPHoldsAt I d s.i s.j (toVec F.nProp s.nu))
    (hz : ∀ l ∈ c.zeros, I (toVec F.nProp l) d = 0)
    (hr : RelsHold (fun l => I (toVec F.nProp l) d) d c.rels) :
    LinComb.eval (fun l => I (toVec F.nProp l) d) d c.claim = 0 :=
  sound h I d hI hz hr.forall

/-- A claim `q [T] - Σ nⱼ [Mⱼ] = 0` gives the reduction of `T` where `q(d) ≠ 0`. -/
theorem reduction {K : Type*} [Field K] (J : List ℤ → K) (d : K) (T : List ℤ) (q : Poly)
    (ms : List (List ℤ × Poly))
    (h : LinComb.eval J d ((T, q) :: ms.map fun m => (m.1, Poly.neg m.2)) = 0)
    (hq : Poly.eval d q ≠ 0) :
    J T = (ms.map fun m => Poly.eval d m.2 / Poly.eval d q * J m.1).sum := by
  have key : ∀ L : List (List ℤ × Poly), LinComb.eval J d (L.map fun m => (m.1, Poly.neg m.2)) =
      -(Poly.eval d q * (L.map fun m => Poly.eval d m.2 / Poly.eval d q * J m.1).sum) := by
    intro L
    induction L with
    | nil => simp
    | cons m L ih =>
      simp only [List.map_cons, LinComb.eval_cons, ih, Poly.eval_neg, List.sum_cons]
      field_simp
      ring
  rw [LinComb.eval_cons, key] at h
  apply mul_left_cancel₀ hq
  linear_combination h

/-- A claim `q · Σ cⱼ [Tⱼ] - Σ nᵢ [Mᵢ] = 0` gives the reduction of the combination `Σ cⱼ [Tⱼ]`
where `q(d) ≠ 0`. -/
theorem reduction_combo {K : Type*} [Field K] (J : List ℤ → K) (d : K) (q : Poly)
    (ts ms : List (List ℤ × Poly))
    (h : LinComb.eval J d (LinComb.smul q ts ++ ms.map fun m => (m.1, Poly.neg m.2)) = 0)
    (hq : Poly.eval d q ≠ 0) :
    (ts.map fun t => Poly.eval d t.2 * J t.1).sum =
      (ms.map fun m => Poly.eval d m.2 / Poly.eval d q * J m.1).sum := by
  rw [LinComb.eval_eq_sum, List.map_append, List.sum_append, ← LinComb.eval_eq_sum,
    LinComb.eval_smul, LinComb.eval_eq_sum, List.map_map] at h
  have key : ∀ L : List (List ℤ × Poly),
      (L.map ((fun t => Poly.eval d t.2 * J t.1) ∘ fun m => (m.1, Poly.neg m.2))).sum =
        -(Poly.eval d q * (L.map fun m => Poly.eval d m.2 / Poly.eval d q * J m.1).sum) := by
    intro L
    induction L with
    | nil => simp
    | cons m L ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, Poly.eval_neg] at ih ⊢
      rw [ih]
      field_simp
      ring
  rw [key] at h
  apply mul_left_cancel₀ hq
  linear_combination h

end Step

end QED.Algebra.IBPCert
