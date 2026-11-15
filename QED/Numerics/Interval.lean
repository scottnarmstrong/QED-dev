/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer interval arithmetic checked by the kernel (milestone NUM.ARITHMETIC)

Decision D-34 asks for certified enclosures whose arithmetic is carried out by Lean's kernel,
with integer (fixed-point) intervals and outward rounding. This module provides that arithmetic.

An `Interval S` has integer endpoints `lo`, `hi` at a fixed scale `S : ℕ` and stands for the
real interval `[lo / S, hi / S]`. A flag `ok` records whether the interval carries information:
an interval with `ok = false` contains every real number. Operations that cannot produce a bound
clear the flag (the reciprocal of an interval meeting `0`), and every operation propagates it, so
each operation is sound without side conditions.

All operations use only `ℕ` and `ℤ` arithmetic, which the kernel reduces with GMP-accelerated
natural-number primitives. The hot operations (products and squares of nonnegative intervals,
reciprocals of positive intervals) pattern-match on the sign of the endpoints and then use
natural-number multiplication and division directly; the general product falls back to the
four endpoint products. Nothing here uses `Rat` arithmetic except to read off the numerator and
denominator of a rational constant.

## Main definitions

* `QED.Numerics.Interval`: scaled integer intervals, with membership `x ∈ I` for `x : ℝ`.
* Operations: `ofInt` and numerals, `point`, `ofFrac`, `ofRat`, `+`, `-` (binary and unary), `*`,
  `⁻¹`, `/`, `Interval.sq`, `Interval.npow`, `Interval.span`, `Interval.meet`.
* Comparisons: `Interval.geRat`, `Interval.leRat`, `Interval.isPos`.

## Main statements

* `QED.Numerics.Interval.mem_add`, `mem_sub`, `mem_neg`, `mem_mul`, `mem_inv`, `mem_div`,
  `mem_sq`, `mem_npow`, `mem_ofRat`, `mem_ofFrac`, ...: each operation is sound for real
  arithmetic, e.g. `x ∈ I → y ∈ J → x * y ∈ I * J`.
* `QED.Numerics.Interval.mem_span_of_monotoneOn`, `mem_span_of_antitoneOn`: enclosures of
  monotone functions from enclosures of their values at the two ends (with `point`).
* `QED.Numerics.Interval.le_of_geRat`, `le_of_leRat`, `pos_of_isPos`: the comparisons are sound.

The tactic `interval_mem` proves goals `e ∈ E` where the interval expression `E` mirrors the
real expression `e`.
-/

@[expose] public section

namespace QED.Numerics

/-! ### Rounding helpers -/

/-- `⌈m / d⌉` for natural numbers `m` and `d > 0`, as an integer. -/
def cdivNat (m d : ℕ) : ℤ := .ofNat (Nat.div (Nat.sub (Nat.add m d) 1) d)

theorem int_neg_eq (n : ℤ) : Int.neg n = -n := rfl

theorem int_sub_eq (a b : ℤ) : Int.sub a b = a - b := rfl

theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem cast_ediv_le (n d : ℤ) (hd : 0 < d) : ((n / d : ℤ) : ℝ) ≤ (n : ℝ) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast Int.ediv_mul_le n hd.ne'

theorem le_cast_neg_ediv_neg (n d : ℤ) (hd : 0 < d) :
    (n : ℝ) / d ≤ ((-((-n) / d) : ℤ) : ℝ) := by
  have h := cast_ediv_le (-n) d hd
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

theorem cast_natDiv_le (m d : ℕ) : ((Nat.div m d : ℕ) : ℝ) ≤ (m : ℝ) / d :=
  Nat.cast_div_le

theorem le_cast_cdivNat (m d : ℕ) (hd : 0 < d) : (m : ℝ) / d ≤ (cdivNat m d : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  simp only [cdivNat, Int.ofNat_eq_natCast, Int.cast_natCast, nat_div_eq, Nat.add_eq, Nat.sub_eq]
  have h := Nat.lt_mul_div_succ (m + d - 1) hd
  have h' : m ≤ d * ((m + d - 1) / d) := by
    generalize (m + d - 1) / d = q at h ⊢
    rw [Nat.mul_add, Nat.mul_one] at h
    omega
  rw [mul_comm]
  exact_mod_cast h'

/-- `a ≤ b` for integers, decided from the constructors and one natural-number comparison
(cheaper in the kernel than `Int.decLe`, which forms `b - a`). -/
def intLe : ℤ → ℤ → Bool
  | .ofNat a, .ofNat b => Nat.ble a b
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc a, .negSucc b => Nat.ble b a

theorem intLe_iff {a b : ℤ} : intLe a b = true ↔ a ≤ b := by
  cases a <;> cases b <;> simp [intLe, Int.negSucc_eq] <;> omega

/-- The minimum of two integers, by `intLe`. -/
def imin (a b : ℤ) : ℤ := bif intLe a b then a else b

/-- The maximum of two integers, by `intLe`. -/
def imax (a b : ℤ) : ℤ := bif intLe a b then b else a

theorem imin_eq (a b : ℤ) : imin a b = min a b := by
  by_cases hab : a ≤ b
  · simp [imin, intLe_iff.2 hab, min_eq_left hab]
  · have h : intLe a b = false := Bool.eq_false_iff.2 (fun h' => hab (intLe_iff.1 h'))
    simp [imin, h, min_eq_right (le_of_not_ge hab)]

theorem imax_eq (a b : ℤ) : imax a b = max a b := by
  by_cases hab : a ≤ b
  · simp [imax, intLe_iff.2 hab, max_eq_right hab]
  · have h : intLe a b = false := Bool.eq_false_iff.2 (fun h' => hab (intLe_iff.1 h'))
    simp [imax, h, max_eq_left (le_of_not_ge hab)]

/-- `⌊n / d⌋` for an integer `n` and `d > 0`, by natural-number division of the magnitude. -/
def fdivInt (n : ℤ) (d : ℕ) : ℤ :=
  match n with
  | .ofNat m => .ofNat (Nat.div m d)
  | .negSucc m => .negSucc (Nat.div m d)

/-- `⌈n / d⌉` for an integer `n` and `d > 0`, by natural-number division of the magnitude. -/
def cdivInt (n : ℤ) (d : ℕ) : ℤ :=
  match n with
  | .ofNat m => cdivNat m d
  | .negSucc m => Int.neg (.ofNat (Nat.div (m + 1) d))

theorem fdivInt_eq {d : ℕ} (hd : 0 < d) (n : ℤ) : fdivInt n d = n / (d : ℤ) := by
  cases n with
  | ofNat m => simp [fdivInt, nat_div_eq]
  | negSucc m =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    rfl

theorem cdivInt_eq {d : ℕ} (hd : 0 < d) (n : ℤ) : cdivInt n d = -((-n) / (d : ℤ)) := by
  cases n with
  | ofNat m =>
    rcases m with _ | k
    · simp [cdivInt, cdivNat, nat_div_eq, Nat.div_eq_of_lt (Nat.sub_lt hd Nat.one_pos)]
    · have e : -(Int.ofNat (k + 1)) = Int.negSucc k := rfl
      rw [e, ← fdivInt_eq hd]
      simp only [cdivInt, cdivNat, fdivInt, nat_div_eq, Nat.add_eq, Nat.sub_eq, Int.neg_negSucc]
      rw [show k + 1 + d - 1 = k + d by omega, Nat.add_div_right k hd]
      simp
  | negSucc m =>
    simp only [cdivInt, nat_div_eq, int_neg_eq, Int.neg_negSucc]
    rw [Int.ofNat_eq_natCast, Int.natCast_div]

/-! ### Intervals -/

/-- An interval with integer endpoints at the fixed scale `S`: it stands for the real interval
`[lo / S, hi / S]`. The flag `ok` records whether the interval carries information; an interval
with `ok = false` contains every real number. -/
structure Interval (S : ℕ) where
  /-- The scaled lower endpoint. -/
  lo : ℤ
  /-- The scaled upper endpoint. -/
  hi : ℤ
  /-- Whether the interval carries information. -/
  ok : Bool

namespace Interval

variable {S : ℕ}

/-- Membership of a real number in an interval. -/
protected def Mem (I : Interval S) (x : ℝ) : Prop :=
  I.ok = true → (I.lo : ℝ) / S ≤ x ∧ x ≤ (I.hi : ℝ) / S

instance : Membership ℝ (Interval S) := ⟨Interval.Mem⟩

theorem mem_iff {I : Interval S} {x : ℝ} :
    x ∈ I ↔ (I.ok = true → (I.lo : ℝ) / S ≤ x ∧ x ≤ (I.hi : ℝ) / S) := Iff.rfl

theorem mem_of_ok_false {I : Interval S} (h : I.ok = false) (x : ℝ) : x ∈ I := by
  intro h'
  simp [h] at h'

/-! #### Constants -/

/-- The point interval at the integer `n`. -/
def ofInt (n : ℤ) : Interval S := ⟨Int.mul n S, Int.mul n S, true⟩

instance : IntCast (Interval S) := ⟨ofInt⟩

instance : NatCast (Interval S) := ⟨fun n => ofInt n⟩

instance {n : ℕ} : OfNat (Interval S) n := ⟨ofInt n⟩

/-- The point interval at the scaled integer `n`, i.e. at the real number `n / S`. -/
def point (n : ℤ) : Interval S := ⟨n, n, true⟩

/-- An interval containing `n / d`, rounded outward. -/
def ofFrac (n : ℤ) (d : ℕ) : Interval S :=
  ⟨fdivInt (Int.mul n S) d, cdivInt (Int.mul n S) d, true⟩

/-- An interval containing the rational number `q`, rounded outward. -/
def ofRat (q : ℚ) : Interval S := ofFrac q.num q.den

/-! #### Arithmetic -/

/-- Sum of intervals. -/
protected def add (I J : Interval S) : Interval S :=
  ⟨Int.add I.lo J.lo, Int.add I.hi J.hi, I.ok && J.ok⟩

/-- Negation of an interval. -/
protected def neg (I : Interval S) : Interval S := ⟨Int.neg I.hi, Int.neg I.lo, I.ok⟩

/-- Difference of intervals. -/
protected def sub (I J : Interval S) : Interval S :=
  ⟨Int.sub I.lo J.hi, Int.sub I.hi J.lo, I.ok && J.ok⟩

/-- Product of intervals of any signs, from the four endpoint products. -/
def mulGen (I J : Interval S) : Interval S :=
  let a := Int.mul I.lo J.lo
  let b := Int.mul I.lo J.hi
  let c := Int.mul I.hi J.lo
  let d := Int.mul I.hi J.hi
  ⟨fdivInt (imin (imin a b) (imin c d)) S, cdivInt (imax (imax a b) (imax c d)) S, I.ok && J.ok⟩

/-- Product of intervals. When both lower endpoints are nonnegative it uses two
natural-number products; otherwise it falls back to `mulGen`. -/
protected def mul (I J : Interval S) : Interval S :=
  match I.lo, J.lo with
  | .ofNat a, .ofNat c =>
    ⟨.ofNat (Nat.div (Nat.mul a c) S), cdivNat (Nat.mul I.hi.toNat J.hi.toNat) S, I.ok && J.ok⟩
  | _, _ => mulGen I J

/-- Natural numbers `(p, q)` with `p / S ≤ |x| ≤ q / S` for every member `x`. -/
def absBounds (I : Interval S) : ℕ × ℕ :=
  match I.lo, I.hi with
  | .ofNat a, h => (a, h.toNat)
  | .negSucc m, .negSucc n => (n + 1, m + 1)
  | .negSucc m, .ofNat b => (0, max (m + 1) b)

/-- Square of an interval. -/
def sq (I : Interval S) : Interval S :=
  let p := absBounds I
  ⟨.ofNat (Nat.div (Nat.mul p.1 p.1) S), cdivNat (Nat.mul p.2 p.2) S, I.ok⟩

/-- Reciprocal of an interval. It carries information only when the interval lies in `(0, ∞)`
or in `(-∞, 0)`, detected from the signs of the scaled endpoints. -/
protected def inv (I : Interval S) : Interval S :=
  match I.lo with
  | .ofNat (a + 1) =>
    ⟨.ofNat (Nat.div (Nat.mul S S) I.hi.toNat), cdivNat (Nat.mul S S) (a + 1), I.ok⟩
  | _ =>
    match I.hi with
    | .negSucc b =>
      ⟨Int.neg (cdivNat (Nat.mul S S) (b + 1)),
        Int.neg (.ofNat (Nat.div (Nat.mul S S) I.lo.natAbs)), I.ok⟩
    | _ => ⟨0, 0, false⟩

instance : Add (Interval S) := ⟨Interval.add⟩
instance : Neg (Interval S) := ⟨Interval.neg⟩
instance : Sub (Interval S) := ⟨Interval.sub⟩
instance : Mul (Interval S) := ⟨Interval.mul⟩
instance : Inv (Interval S) := ⟨Interval.inv⟩

/-- Quotient of intervals, as the product with the reciprocal. -/
protected def div (I J : Interval S) : Interval S := I * J⁻¹

instance : Div (Interval S) := ⟨Interval.div⟩

/-- Natural power of an interval by repeated products. -/
def npow (I : Interval S) : ℕ → Interval S
  | 0 => 1
  | n + 1 => npow I n * I

/-- The interval from the lower end of `A` to the upper end of `B`. If `g` is monotone on
`[a, b]`, `g a ∈ A` and `g b ∈ B`, it contains `g x` for every `x ∈ [a, b]`. -/
def span (A B : Interval S) : Interval S := ⟨A.lo, B.hi, A.ok && B.ok⟩

/-- An interval containing every common member of `I` and `J`. -/
def meet (I J : Interval S) : Interval S :=
  bif I.ok then (bif J.ok then ⟨max I.lo J.lo, min I.hi J.hi, true⟩ else I) else J

/-! #### Comparisons -/

/-- `true` only if every member of `I` is at least `q`. -/
def geRat (I : Interval S) (q : ℚ) : Bool := I.ok && decide (q.num * S ≤ I.lo * q.den)

/-- `true` only if every member of `I` is at most `q`. -/
def leRat (I : Interval S) (q : ℚ) : Bool := I.ok && decide (I.hi * q.den ≤ q.num * S)

/-- `true` only if every member of `I` is positive. -/
def isPos (I : Interval S) : Bool := I.ok && decide (0 < I.lo)

/-! ### Soundness -/

theorem mem_add {I J : Interval S} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ I + J := by
  intro h
  change (I.ok && J.ok) = true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hx1, hx2⟩ := hx h.1
  obtain ⟨hy1, hy2⟩ := hy h.2
  change ((Int.add I.lo J.lo : ℤ) : ℝ) / S ≤ x + y ∧ x + y ≤ ((Int.add I.hi J.hi : ℤ) : ℝ) / S
  simp only [Int.add_def, Int.cast_add, add_div]
  constructor <;> linarith

theorem mem_neg {I : Interval S} {x : ℝ} (hx : x ∈ I) : -x ∈ -I := by
  intro h
  change I.ok = true at h
  obtain ⟨hx1, hx2⟩ := hx h
  change ((Int.neg I.hi : ℤ) : ℝ) / S ≤ -x ∧ -x ≤ ((Int.neg I.lo : ℤ) : ℝ) / S
  simp only [int_neg_eq, Int.cast_neg, neg_div]
  constructor <;> linarith

theorem mem_sub {I J : Interval S} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) : x - y ∈ I - J := by
  intro h
  change (I.ok && J.ok) = true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hx1, hx2⟩ := hx h.1
  obtain ⟨hy1, hy2⟩ := hy h.2
  change ((Int.sub I.lo J.hi : ℤ) : ℝ) / S ≤ x - y ∧ x - y ≤ ((Int.sub I.hi J.lo : ℤ) : ℝ) / S
  simp only [int_sub_eq, Int.cast_sub, sub_div]
  constructor <;> linarith

/-- A product `t u` with `t ∈ [p, q]` lies between `p u` and `q u`. -/
theorem min_le_mul_le_max {p q t : ℝ} (ht : p ≤ t ∧ t ≤ q) (u : ℝ) :
    min (p * u) (q * u) ≤ t * u ∧ t * u ≤ max (p * u) (q * u) := by
  rcases le_total 0 u with hu | hu
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right ht.1 hu),
      (mul_le_mul_of_nonneg_right ht.2 hu).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right ht.2 hu),
      (mul_le_mul_of_nonpos_right ht.1 hu).trans (le_max_left _ _)⟩

/-- A product of members of `[p, q]` and `[r, s]` lies between the extreme endpoint products. -/
theorem corner_bounds {p q r s x y : ℝ} (hx : p ≤ x ∧ x ≤ q) (hy : r ≤ y ∧ y ≤ s) :
    min (min (p * r) (p * s)) (min (q * r) (q * s)) ≤ x * y ∧
      x * y ≤ max (max (p * r) (p * s)) (max (q * r) (q * s)) := by
  obtain ⟨h1, h2⟩ := min_le_mul_le_max hx y
  obtain ⟨hp1, hp2⟩ := min_le_mul_le_max hy p
  obtain ⟨hq1, hq2⟩ := min_le_mul_le_max hy q
  rw [mul_comm r p, mul_comm s p, mul_comm y p] at hp1 hp2
  rw [mul_comm r q, mul_comm s q, mul_comm y q] at hq1 hq2
  exact ⟨(min_le_min hp1 hq1).trans h1, h2.trans (max_le_max hp2 hq2)⟩

theorem mem_span_of_monotoneOn {A B : Interval S} {g : ℝ → ℝ} {a b x : ℝ}
    (hg : MonotoneOn g (Set.Icc a b)) (hx : x ∈ Set.Icc a b) (ha : g a ∈ A) (hb : g b ∈ B) :
    g x ∈ span A B := by
  intro h
  change (A.ok && B.ok) = true at h
  rw [Bool.and_eq_true] at h
  have hab : a ≤ b := hx.1.trans hx.2
  exact ⟨(ha h.1).1.trans (hg ⟨le_rfl, hab⟩ hx hx.1),
    (hg hx ⟨hab, le_rfl⟩ hx.2).trans (hb h.2).2⟩

theorem mem_span_of_antitoneOn {A B : Interval S} {g : ℝ → ℝ} {a b x : ℝ}
    (hg : AntitoneOn g (Set.Icc a b)) (hx : x ∈ Set.Icc a b) (hb : g b ∈ A) (ha : g a ∈ B) :
    g x ∈ span A B := by
  intro h
  change (A.ok && B.ok) = true at h
  rw [Bool.and_eq_true] at h
  have hab : a ≤ b := hx.1.trans hx.2
  exact ⟨(hb h.1).1.trans (hg hx ⟨hab, le_rfl⟩ hx.2),
    (hg ⟨le_rfl, hab⟩ hx hx.1).trans (ha h.2).2⟩

theorem mem_meet {I J : Interval S} {x : ℝ} (hI : x ∈ I) (hJ : x ∈ J) : x ∈ meet I J := by
  unfold meet
  cases hi : I.ok <;> cases hj : J.ok
  · simpa using hJ
  · simpa using hJ
  · simpa using hI
  · intro _
    obtain ⟨h1, h2⟩ := hI hi
    obtain ⟨h3, h4⟩ := hJ hj
    simp only [Bool.cond_true, Int.cast_max, Int.cast_min]
    rw [← max_div_div_right (Nat.cast_nonneg S), ← min_div_div_right (Nat.cast_nonneg S)]
    exact ⟨max_le h1 h3, le_min h2 h4⟩

section Soundness

variable [NeZero S]

theorem scale_pos : (0 : ℝ) < S := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S)

theorem scale_pos_int : (0 : ℤ) < S := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S)

theorem mem_ofInt (n : ℤ) : (n : ℝ) ∈ (ofInt n : Interval S) := by
  intro _
  have hS := (scale_pos (S := S)).ne'
  simp only [ofInt, Int.mul_def, Int.cast_mul, Int.cast_natCast]
  constructor <;> rw [mul_div_cancel_right₀ _ hS]

theorem mem_intCast (n : ℤ) : (n : ℝ) ∈ (n : Interval S) := mem_ofInt n

theorem mem_natCast (n : ℕ) : (n : ℝ) ∈ (n : Interval S) := by
  have h := mem_ofInt (S := S) n
  rw [Int.cast_natCast] at h
  exact h

theorem mem_zero : (0 : ℝ) ∈ (0 : Interval S) := by
  have h := mem_natCast (S := S) 0
  rw [Nat.cast_zero] at h
  exact h

theorem mem_one : (1 : ℝ) ∈ (1 : Interval S) := by
  have h := mem_natCast (S := S) 1
  rw [Nat.cast_one] at h
  exact h

theorem mem_ofNat (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℝ) ∈ (OfNat.ofNat n : Interval S) :=
  mem_natCast n

omit [NeZero S] in
theorem mem_point (n : ℤ) : ((n : ℝ) / S) ∈ (point n : Interval S) := fun _ => ⟨le_rfl, le_rfl⟩

theorem mem_ofFrac (n : ℤ) (d : ℕ) : ((n : ℝ) / d) ∈ (ofFrac n d : Interval S) := by
  intro _
  have hS := scale_pos (S := S)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [ofFrac, Nat.cast_zero, div_zero]
    generalize Int.mul n S = k
    constructor
    · refine div_nonpos_of_nonpos_of_nonneg ?_ hS.le
      cases k <;> simp [fdivInt, nat_div_eq]
    · refine div_nonneg ?_ hS.le
      cases k <;> simp [cdivInt, cdivNat, nat_div_eq, int_neg_eq]
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have h1 := cast_ediv_le (n * S) d hd'
  have h2 := le_cast_neg_ediv_neg (n * S) d hd'
  simp only [ofFrac, fdivInt_eq hd, cdivInt_eq hd, Int.mul_def]
  push_cast at h1 h2 ⊢
  constructor
  · rw [div_le_iff₀ hS]
    calc _ ≤ (n : ℝ) * S / d := h1
      _ = n / d * S := by ring
  · rw [le_div_iff₀ hS]
    calc (n : ℝ) / d * S = n * S / d := by ring
      _ ≤ _ := h2

theorem mem_ofRat (q : ℚ) : (q : ℝ) ∈ (ofRat q : Interval S) := by
  have h := mem_ofFrac (S := S) q.num q.den
  rwa [← Rat.cast_def] at h

theorem mem_ofRat_of_eq {q : ℚ} {x : ℝ} (h : (q : ℝ) = x) : x ∈ (ofRat q : Interval S) :=
  h ▸ mem_ofRat q

theorem mem_mulGen {I J : Interval S} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mulGen I J := by
  intro h
  change (I.ok && J.ok) = true at h
  rw [Bool.and_eq_true] at h
  have hS := scale_pos (S := S)
  obtain ⟨h1, h2⟩ := corner_bounds (hx h.1) (hy h.2)
  have e : ∀ m n : ℤ, (m : ℝ) / S * ((n : ℝ) / S) = ((m * n : ℤ) : ℝ) / S / S := by
    intro m n; push_cast; ring
  simp only [e, min_div_div_right hS.le, max_div_div_right hS.le] at h1 h2
  simp only [← Int.cast_min, ← Int.cast_max] at h1 h2
  have hSn : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  simp only [mulGen, Int.mul_def, imin_eq, imax_eq, fdivInt_eq hSn, cdivInt_eq hSn]
  constructor
  · rw [div_le_iff₀ hS]
    refine le_trans ?_ ((div_le_iff₀ hS).1 h1)
    exact cast_ediv_le _ _ scale_pos_int
  · rw [le_div_iff₀ hS]
    refine le_trans ((le_div_iff₀ hS).1 h2) ?_
    exact le_cast_neg_ediv_neg _ _ scale_pos_int

/-- The fast path of `Interval.mul`, for intervals with nonnegative lower endpoints. -/
theorem mem_mul_nonneg {I J : Interval S} {x y : ℝ} {a c : ℕ} (ha : I.lo = .ofNat a)
    (hc : J.lo = .ofNat c) (hx : x ∈ I) (hy : y ∈ J) (h : (I.ok && J.ok) = true) :
    ((Int.ofNat (Nat.div (Nat.mul a c) S) : ℤ) : ℝ) / S ≤ x * y ∧
      x * y ≤ ((cdivNat (Nat.mul I.hi.toNat J.hi.toNat) S : ℤ) : ℝ) / S := by
  rw [Bool.and_eq_true] at h
  have hS := scale_pos (S := S)
  obtain ⟨hx1, hx2⟩ := hx h.1
  obtain ⟨hy1, hy2⟩ := hy h.2
  rw [ha] at hx1
  rw [hc] at hy1
  simp only [Int.ofNat_eq_natCast, Int.cast_natCast] at hx1 hy1 ⊢
  have hx0 : 0 ≤ x := le_trans (by positivity) hx1
  have hy0 : 0 ≤ y := le_trans (by positivity) hy1
  have hIhi : (0 : ℝ) ≤ I.hi := by
    have := hx0.trans hx2
    rwa [div_nonneg_iff, or_iff_left (fun h' => absurd h'.2 (not_le.2 hS)), and_iff_left hS.le]
      at this
  have hJhi : (0 : ℝ) ≤ J.hi := by
    have := hy0.trans hy2
    rwa [div_nonneg_iff, or_iff_left (fun h' => absurd h'.2 (not_le.2 hS)), and_iff_left hS.le]
      at this
  have eI : ((I.hi.toNat : ℕ) : ℝ) = I.hi := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by exact_mod_cast hIhi)]
  have eJ : ((J.hi.toNat : ℕ) : ℝ) = J.hi := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by exact_mod_cast hJhi)]
  constructor
  · rw [div_le_iff₀ hS]
    have k1 := cast_natDiv_le (Nat.mul a c) S
    simp only [Nat.mul_eq, Nat.cast_mul] at k1
    calc _ ≤ (a : ℝ) * c / S := k1
      _ = (a : ℝ) / S * (c / S) * S := by field_simp
      _ ≤ x * y * S := by gcongr
  · rw [le_div_iff₀ hS]
    have k2 := le_cast_cdivNat (Nat.mul I.hi.toNat J.hi.toNat) S (Nat.pos_of_ne_zero (NeZero.ne S))
    simp only [Nat.mul_eq, Nat.cast_mul, eI, eJ] at k2
    calc x * y * S ≤ (I.hi : ℝ) / S * (J.hi / S) * S := by gcongr
      _ = (I.hi : ℝ) * J.hi / S := by field_simp
      _ ≤ _ := k2

theorem mem_mul {I J : Interval S} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) : x * y ∈ I * J := by
  change x * y ∈ Interval.mul I J
  unfold Interval.mul
  split
  · rename_i a c ha hc
    intro h
    exact mem_mul_nonneg ha hc hx hy h
  · exact mem_mulGen hx hy

theorem abs_mem_absBounds {I : Interval S} {x : ℝ} (hx : x ∈ I) (h : I.ok = true) :
    ((absBounds I).1 : ℝ) / S ≤ |x| ∧ |x| ≤ ((absBounds I).2 : ℝ) / S := by
  have hS := scale_pos (S := S)
  obtain ⟨hx1, hx2⟩ := hx h
  rcases hlo : I.lo with a | m <;> rcases hhi : I.hi with b | n <;>
    rw [hlo] at hx1 <;> rw [hhi] at hx2 <;> simp only [absBounds, hlo, hhi] <;>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc] at hx1 hx2 ⊢
  · have hx0 : 0 ≤ x := le_trans (by positivity) hx1
    rw [abs_of_nonneg hx0]
    exact ⟨hx1, hx2⟩
  · have hx0 : 0 ≤ x := le_trans (by positivity) hx1
    have : x ≤ 0 := hx2.trans (by rw [neg_div]; simp only [neg_nonpos]; positivity)
    have hx00 : x = 0 := le_antisymm this hx0
    subst hx00
    have : (a : ℝ) / S ≤ 0 := hx1
    simp only [abs_zero, Int.toNat_negSucc, Nat.cast_zero, zero_div, le_refl, and_true]
    exact this
  · refine ⟨by simp [abs_nonneg], ?_⟩
    rw [abs_le]
    have hm' : ((m + 1 : ℕ) : ℝ) / S ≤ ((max (m + 1) b : ℕ) : ℝ) / S := by
      gcongr; exact_mod_cast le_max_left _ _
    have hb' : (b : ℝ) / S ≤ ((max (m + 1) b : ℕ) : ℝ) / S := by
      gcongr; exact_mod_cast le_max_right _ _
    push_cast at hm' hb' hx1
    rw [neg_div] at hx1
    constructor <;> push_cast <;> linarith
  · have hx0 : x ≤ 0 := hx2.trans (by rw [neg_div]; simp only [neg_nonpos]; positivity)
    rw [abs_of_nonpos hx0]
    push_cast at hx1 hx2 ⊢
    rw [neg_div] at hx1 hx2
    constructor <;> linarith

theorem mem_sq {I : Interval S} {x : ℝ} (hx : x ∈ I) : x ^ 2 ∈ sq I := by
  intro h
  change I.ok = true at h
  have hS := scale_pos (S := S)
  obtain ⟨h1, h2⟩ := abs_mem_absBounds hx h
  have hp0 : (0 : ℝ) ≤ ((absBounds I).1 : ℝ) / S := by positivity
  rw [← sq_abs]
  change ((Int.ofNat (Nat.div (Nat.mul (absBounds I).1 (absBounds I).1) S) : ℤ) : ℝ) / S ≤ |x| ^ 2
    ∧ |x| ^ 2 ≤ ((cdivNat (Nat.mul (absBounds I).2 (absBounds I).2) S : ℤ) : ℝ) / S
  constructor
  · rw [div_le_iff₀ hS]
    have k1 := cast_natDiv_le (Nat.mul (absBounds I).1 (absBounds I).1) S
    simp only [Nat.mul_eq, Nat.cast_mul] at k1
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    calc _ ≤ ((absBounds I).1 : ℝ) * (absBounds I).1 / S := k1
      _ = (((absBounds I).1 : ℝ) / S) ^ 2 * S := by field_simp
      _ ≤ |x| ^ 2 * S := by gcongr
  · rw [le_div_iff₀ hS]
    have k2 := le_cast_cdivNat (Nat.mul (absBounds I).2 (absBounds I).2) S
      (Nat.pos_of_ne_zero (NeZero.ne S))
    simp only [Nat.mul_eq, Nat.cast_mul] at k2
    calc |x| ^ 2 * S ≤ (((absBounds I).2 : ℝ) / S) ^ 2 * S := by gcongr
      _ = ((absBounds I).2 : ℝ) * (absBounds I).2 / S := by field_simp
      _ ≤ _ := k2

theorem mem_inv {I : Interval S} {x : ℝ} (hx : x ∈ I) : x⁻¹ ∈ I⁻¹ := by
  change x⁻¹ ∈ Interval.inv I
  have hS := scale_pos (S := S)
  have hSS : 0 < Nat.mul S S := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne S))
    (Nat.pos_of_ne_zero (NeZero.ne S))
  unfold Interval.inv
  split
  · rename_i a ha
    intro h
    change I.ok = true at h
    obtain ⟨hx1, hx2⟩ := hx h
    rw [ha] at hx1
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast] at hx1 ⊢
    have hlo : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) / S := by positivity
    have hxpos : 0 < x := hlo.trans_le hx1
    have hhi : (0 : ℝ) < I.hi := by
      have := hxpos.trans_le hx2
      rwa [div_pos_iff_of_pos_right hS] at this
    have eI : ((I.hi.toNat : ℕ) : ℝ) = I.hi := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by exact_mod_cast hhi.le)]
    constructor
    · rw [div_le_iff₀ hS]
      have k1 := cast_natDiv_le (Nat.mul S S) I.hi.toNat
      simp only [Nat.mul_eq, Nat.cast_mul, eI] at k1
      calc _ ≤ (S : ℝ) * S / I.hi := k1
        _ = ((I.hi : ℝ) / S)⁻¹ * S := by field_simp
        _ ≤ x⁻¹ * S := by gcongr
    · rw [le_div_iff₀ hS]
      have k2 := le_cast_cdivNat (Nat.mul S S) (a + 1) (Nat.succ_pos a)
      simp only [Nat.mul_eq, Nat.cast_mul] at k2
      calc x⁻¹ * S ≤ (((a + 1 : ℕ) : ℝ) / S)⁻¹ * S := by gcongr
        _ = (S : ℝ) * S / ((a + 1 : ℕ) : ℝ) := by field_simp
        _ ≤ _ := k2
  · split
    · rename_i b hb
      intro h
      change I.ok = true at h
      obtain ⟨hx1, hx2⟩ := hx h
      rw [hb] at hx2
      simp only [Int.cast_negSucc] at hx2
      push_cast at hx2
      rw [neg_div] at hx2
      have hhi : ((b : ℝ) + 1) / S > 0 := by positivity
      have hxneg : x < 0 := by linarith
      have hlo : (I.lo : ℝ) < 0 := by
        have := hx1.trans_lt hxneg
        rwa [div_neg_iff, or_iff_right (fun h' => absurd h'.2 (not_lt.2 hS.le)),
          and_iff_left hS] at this
      have eL : ((I.lo.natAbs : ℕ) : ℝ) = -I.lo := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg hlo]
      have hax : (-x) ≤ ((I.lo.natAbs : ℕ) : ℝ) / S := by rw [eL, neg_div]; linarith
      have hbx : ((b + 1 : ℕ) : ℝ) / S ≤ -x := by push_cast; linarith
      have hnx : 0 < -x := by linarith
      simp only [int_neg_eq, Int.cast_neg, Int.ofNat_eq_natCast, Int.cast_natCast, neg_div]
      constructor
      · rw [neg_le, ← inv_neg, le_div_iff₀ hS]
        have k2 := le_cast_cdivNat (Nat.mul S S) (b + 1) (Nat.succ_pos b)
        simp only [Nat.mul_eq, Nat.cast_mul] at k2
        calc (-x)⁻¹ * S ≤ (((b + 1 : ℕ) : ℝ) / S)⁻¹ * S := by gcongr
          _ = (S : ℝ) * S / ((b + 1 : ℕ) : ℝ) := by field_simp
          _ ≤ _ := k2
      · rw [le_neg, ← inv_neg, div_le_iff₀ hS]
        have hL : (0 : ℝ) < ((I.lo.natAbs : ℕ) : ℝ) := by rw [eL]; linarith
        have k1 := cast_natDiv_le (Nat.mul S S) I.lo.natAbs
        simp only [Nat.mul_eq, Nat.cast_mul] at k1
        calc _ ≤ (S : ℝ) * S / ((I.lo.natAbs : ℕ) : ℝ) := k1
          _ = (((I.lo.natAbs : ℕ) : ℝ) / S)⁻¹ * S := by field_simp
          _ ≤ (-x)⁻¹ * S := by gcongr
    · exact mem_of_ok_false rfl _

theorem mem_div {I J : Interval S} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) : x / y ∈ I / J := by
  rw [div_eq_mul_inv]
  exact mem_mul hx (mem_inv hy)

theorem mem_npow {I : Interval S} {x : ℝ} (hx : x ∈ I) (n : ℕ) : x ^ n ∈ npow I n := by
  induction n with
  | zero => simpa [npow] using mem_one
  | succ n ih => rw [pow_succ]; exact mem_mul ih hx

theorem le_of_geRat {I : Interval S} {q : ℚ} (h : I.geRat q = true) {x : ℝ} (hx : x ∈ I) :
    (q : ℝ) ≤ x := by
  unfold geRat at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  have hS := scale_pos (S := S)
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  refine le_trans ?_ (hx h.1).1
  rw [Rat.cast_def, div_le_div_iff₀ hd hS]
  exact_mod_cast h.2

theorem le_of_leRat {I : Interval S} {q : ℚ} (h : I.leRat q = true) {x : ℝ} (hx : x ∈ I) :
    x ≤ q := by
  unfold leRat at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  have hS := scale_pos (S := S)
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  refine (hx h.1).2.trans ?_
  rw [Rat.cast_def, div_le_div_iff₀ hS hd]
  exact_mod_cast h.2

theorem pos_of_isPos {I : Interval S} (h : I.isPos = true) {x : ℝ} (hx : x ∈ I) : 0 < x := by
  unfold isPos at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  refine lt_of_lt_of_le ?_ (hx h.1).1
  have : (0 : ℝ) < I.lo := by exact_mod_cast h.2
  exact div_pos this scale_pos

end Soundness

end Interval

/-- Proves a goal `e ∈ E`, where the interval expression `E` is built from `+`, `-`, `*`, `⁻¹`,
`/`, `Interval.sq`, `Interval.npow`, numerals, casts, `Interval.ofRat` and `Interval.ofFrac`
with the same shape as the real expression `e`, and the leaves are hypotheses `x ∈ X`. Side
goals `(q : ℝ) = c` for rational constants are closed by `norm_num`. The membership lemmas are
applied at reducible transparency, so the shapes must match syntactically (unfold the interval
extension and the integrand first, e.g. with `simp only`). -/
syntax "interval_mem" : tactic

macro_rules
  | `(tactic| interval_mem) => `(tactic| repeat' first
      | assumption
      | with_reducible apply QED.Numerics.Interval.mem_add
      | with_reducible apply QED.Numerics.Interval.mem_sub
      | with_reducible apply QED.Numerics.Interval.mem_mul
      | with_reducible apply QED.Numerics.Interval.mem_div
      | with_reducible apply QED.Numerics.Interval.mem_neg
      | with_reducible apply QED.Numerics.Interval.mem_inv
      | with_reducible apply QED.Numerics.Interval.mem_sq
      | with_reducible apply QED.Numerics.Interval.mem_npow
      | with_reducible apply QED.Numerics.Interval.mem_zero
      | with_reducible apply QED.Numerics.Interval.mem_one
      | with_reducible apply QED.Numerics.Interval.mem_ofNat
      | with_reducible apply QED.Numerics.Interval.mem_natCast
      | with_reducible apply QED.Numerics.Interval.mem_intCast
      | with_reducible apply QED.Numerics.Interval.mem_ofFrac
      | with_reducible apply QED.Numerics.Interval.mem_ofRat
      | ((with_reducible apply QED.Numerics.Interval.mem_ofRat_of_eq); norm_num))

end QED.Numerics

end
