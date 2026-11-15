/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.FeynmanParameter
public import QED.Numerics.Interval
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Box-partition quadrature checked by the kernel (milestone NUM.INTEGRATION)

Decision D-34 encloses two-dimensional integrals over the unit square by a box partition proposed
by an external script and checked in Lean: on each box the integrand is bounded by interval
arithmetic (`QED.Numerics.Interval`), and the checker sums `area × [lower, upper]`.

A partition is a list of vertical strips. Strip `k` covers `(x_{k-1}/S, x_k/S] × (0, 1]`, with
`x_{-1} = 0`, and is cut at the heights `y_1/S ≤ y_2/S ≤ ... ≤ y_m/S = 1` (from `y_0 = 0`).
The checker verifies that the strip ends do not decrease and end at `S`, and that the cuts in
each strip do not decrease and end at `S`; the half-open boxes then tile `(0, 1]²` exactly
(empty boxes are harmless). Coverage needs no other data: a missing box, an overlap or a box
outside the square makes the check fail.

The integrand enters as a computable interval extension `F : Box S → Interval S`. The checker
accumulates the scaled sums `Σ area · lo` and `Σ area · hi` exactly in `ℤ` (at scale `S³`), so
the only rounding is inside `F`. Running sums are forced to literals at every step, so kernel
reduction stays shallow for partitions with many boxes.

## Main definitions

* `QED.Numerics.Box`, `QED.Numerics.Strip`: boxes and strips with natural-number corners at
  scale `S`.
* `QED.Numerics.Quadrature.check`: the checker.
* `QED.Numerics.Quadrature.uniform`: the uniform `n × m` grid.

## Main statements

* `QED.Numerics.Quadrature.integral_bounds_of_check`: if `f` is integrable for
  `QED.Integration.feynmanMeasure`, `F` is sound for `f` on every box, and the checker accepts
  the partition with claimed bounds `lo`, `hi`, then `lo ≤ ∫ f ≤ hi`.
* `QED.Numerics.Quadrature.integral_bounds_of_check_of_continuousOn`: the same for `f`
  continuous on the closed unit square.

## Writing certificates

* Prove the soundness hypothesis of `F` with `QED.Numerics.Box.fst_mem_X`,
  `QED.Numerics.Box.snd_mem_Y` and the tactic `interval_mem`, after unfolding `f` and `F`.
* Check with `decide +kernel`. Declare long partition literals `noncomputable`: the kernel does
  not need compiled code, and the code generator exceeds its recursion limit on list literals
  with thousands of entries.
* Kernel cost grows linearly in the number of boxes: about 0.2 ms per box for the traversal plus
  roughly 0.1 ms per interval operation in `F` (the general product `Interval.mulGen`, used for
  factors with a negative lower endpoint, costs about 0.3 ms).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.Numerics

/-- An axis-parallel box `(x₀/S, x₁/S] × (y₀/S, y₁/S]` with natural-number corners at scale
`S`. -/
structure Box (S : ℕ) where
  /-- Scaled left edge. -/
  x₀ : ℕ
  /-- Scaled right edge. -/
  x₁ : ℕ
  /-- Scaled bottom edge. -/
  y₀ : ℕ
  /-- Scaled top edge. -/
  y₁ : ℕ

namespace Box

variable {S : ℕ}

/-- The interval of first coordinates of the box. -/
def X (B : Box S) : Interval S := ⟨.ofNat B.x₀, .ofNat B.x₁, true⟩

/-- The interval of second coordinates of the box. -/
def Y (B : Box S) : Interval S := ⟨.ofNat B.y₀, .ofNat B.y₁, true⟩

/-- The points of the box. -/
def toSet (B : Box S) : Set (ℝ × ℝ) :=
  Ioc ((B.x₀ : ℝ) / S) ((B.x₁ : ℝ) / S) ×ˢ Ioc ((B.y₀ : ℝ) / S) ((B.y₁ : ℝ) / S)

theorem fst_mem_X {B : Box S} {z : ℝ × ℝ} (hz : z ∈ B.toSet) : z.1 ∈ B.X := fun _ =>
  ⟨by simpa [X] using hz.1.1.le, by simpa [X] using hz.1.2⟩

theorem snd_mem_Y {B : Box S} {z : ℝ × ℝ} (hz : z ∈ B.toSet) : z.2 ∈ B.Y := fun _ =>
  ⟨by simpa [Y] using hz.2.1.le, by simpa [Y] using hz.2.2⟩

end Box

/-- A vertical strip of a box partition. It ends at `x / S` (it starts where the previous strip
ends) and its boxes have top edges `ys / S`, from bottom to top. -/
structure Strip where
  /-- Scaled right edge of the strip. -/
  x : ℕ
  /-- Scaled top edges of the boxes of the strip. -/
  ys : List ℕ

namespace Quadrature

variable {S : ℕ}

/-- Always `true`. Evaluating it makes the kernel reduce `n` to a literal; the checker applies it
to its running sums so that kernel reduction never builds deep unevaluated sums. -/
def force (n : ℤ) : Bool :=
  match n with
  | .ofNat m => Nat.beq m m
  | .negSucc m => Nat.beq m m

theorem force_eq_true (n : ℤ) : force n = true := by
  cases n <;> simp [force]

/-- The scaled area `(xb - xa)(y - ya)` of a box, at scale `S²`. -/
def weight (xa xb ya y : ℕ) : ℤ := .ofNat (Nat.mul (Nat.sub xb xa) (Nat.sub y ya))

/-- Sums over the boxes of the strip `(xa/S, xb/S]`, from height `ya/S` upward through the cuts
`ys`, added to the running sums `lo`, `hi`. Returns `none` if a cut decreases, the cuts do not
end at `S`, or `F` gives no information on some box. -/
def stripSum (F : Box S → Interval S) (xa xb : ℕ) : ℕ → List ℕ → ℤ → ℤ → Option (ℤ × ℤ)
  | ya, [], lo, hi => bif Nat.beq ya S then some (lo, hi) else none
  | ya, y :: ys, lo, hi =>
    let I := F ⟨xa, xb, ya, y⟩
    let w := weight xa xb ya y
    bif Nat.ble ya y && I.ok && force lo && force hi then
      stripSum F xa xb y ys (Int.add lo (Int.mul w I.lo)) (Int.add hi (Int.mul w I.hi))
    else none

/-- Sums over the strips `P`, starting at `xa/S`, added to the running sums `lo`, `hi`. Returns
`none` if a strip end decreases, the strips do not end at `S`, or a strip fails. -/
def partSum (F : Box S → Interval S) : ℕ → List Strip → ℤ → ℤ → Option (ℤ × ℤ)
  | xa, [], lo, hi => bif Nat.beq xa S then some (lo, hi) else none
  | xa, s :: P, lo, hi =>
    bif Nat.ble xa s.x then
      match stripSum F xa s.x 0 s.ys lo hi with
      | some (lo', hi') => partSum F s.x P lo' hi'
      | none => none
    else none

/-- The checker: accepts when the strips `P` tile the unit square, `F` gives information on
every box, and the resulting enclosure `[Σ area · lo, Σ area · hi]` of the integral lies in
`[lo, hi]`. -/
def check (F : Box S → Interval S) (P : List Strip) (lo hi : ℚ) : Bool :=
  match partSum F 0 P 0 0 with
  | some (L, H) =>
    Nat.blt 0 S && decide (lo.num * ((S : ℤ) * S * S) ≤ L * lo.den) &&
      decide (H * hi.den ≤ hi.num * ((S : ℤ) * S * S))
  | none => false

/-- The uniform grid of `n` strips of `m` boxes each, at scale `S`. -/
def uniform (S n m : ℕ) : List Strip :=
  (List.range n).map fun i => ⟨S * (i + 1) / n, (List.range m).map fun j => S * (j + 1) / m⟩

/-! ### Soundness -/

/-- Integral bounds on one box from pointwise bounds. -/
theorem integral_box_bounds {f : ℝ × ℝ → ℝ} {a b c d l u : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : IntegrableOn f (Ioc a b ×ˢ Ioc c d))
    (hbd : ∀ z ∈ Ioc a b ×ˢ Ioc c d, l ≤ f z ∧ f z ≤ u) :
    l * ((b - a) * (d - c)) ≤ ∫ z in Ioc a b ×ˢ Ioc c d, f z ∧
      ∫ z in Ioc a b ×ˢ Ioc c d, f z ≤ u * ((b - a) * (d - c)) := by
  have hs : MeasurableSet (Ioc a b ×ˢ Ioc c d) := measurableSet_Ioc.prod measurableSet_Ioc
  have hvol : (volume : Measure (ℝ × ℝ)).real (Ioc a b ×ˢ Ioc c d) = (b - a) * (d - c) := by
    rw [Measure.volume_eq_prod, measureReal_prod_prod, Real.volume_real_Ioc_of_le hab,
      Real.volume_real_Ioc_of_le hcd]
  have hfin : (volume : Measure (ℝ × ℝ)) (Ioc a b ×ˢ Ioc c d) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  constructor
  · have := setIntegral_ge_of_const_le_real hs hfin (fun z hz => (hbd z hz).1) hf
    rwa [hvol] at this
  · have := setIntegral_mono_on hf (integrableOn_const hfin) hs (fun z hz => (hbd z hz).2)
    rwa [setIntegral_const, hvol, smul_eq_mul, mul_comm] at this

theorem weight_div {S : ℕ} {xa xb ya y : ℕ} (hx : xa ≤ xb) (hy : ya ≤ y) (c : ℤ) :
    ((weight xa xb ya y * c : ℤ) : ℝ) / (S : ℝ) ^ 3 =
      (c : ℝ) / S * (((xb : ℝ) / S - (xa : ℝ) / S) * ((y : ℝ) / S - (ya : ℝ) / S)) := by
  have e : ((weight xa xb ya y : ℤ) : ℝ) = ((xb : ℝ) - xa) * ((y : ℝ) - ya) := by
    simp only [weight, Nat.mul_eq, Nat.sub_eq, Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [Nat.cast_mul, Nat.cast_sub hx, Nat.cast_sub hy]
  rw [Int.cast_mul, e]
  rcases Nat.eq_zero_or_pos S with h0 | hS
  · simp [h0]
  · have : (S : ℝ) ≠ 0 := by positivity
    field_simp

variable [NeZero S] {f : ℝ × ℝ → ℝ} {F : Box S → Interval S}

theorem stripSum_sound
    (hF : ∀ B : Box S, ∀ z ∈ B.toSet, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 → f z ∈ F B)
    (hf : IntegrableOn f (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)) {xa xb : ℕ} (hab : xa ≤ xb)
    (hb : xb ≤ S) (ys : List ℕ) :
    ∀ (ya : ℕ) (lo hi L H : ℤ), stripSum F xa xb ya ys lo hi = some (L, H) →
      ya ≤ S ∧
      ((L - lo : ℤ) : ℝ) / (S : ℝ) ^ 3 ≤
        ∫ z in Ioc ((xa : ℝ) / S) ((xb : ℝ) / S) ×ˢ Ioc ((ya : ℝ) / S) 1, f z ∧
      ∫ z in Ioc ((xa : ℝ) / S) ((xb : ℝ) / S) ×ˢ Ioc ((ya : ℝ) / S) 1, f z ≤
        ((H - hi : ℤ) : ℝ) / (S : ℝ) ^ 3 := by
  have hS := Interval.scale_pos (S := S)
  have hSne : (S : ℝ) ≠ 0 := hS.ne'
  induction ys with
  | nil =>
    intro ya lo hi L H h
    simp only [stripSum] at h
    cases hc : Nat.beq ya S
    · simp [hc] at h
    · simp only [hc, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hya : ya = S := Nat.eq_of_beq_eq_true hc
      subst hya
      simp [hSne]
  | cons y ys ih =>
    intro ya lo hi L H h
    simp only [stripSum] at h
    cases hc : (Nat.ble ya y && (F ⟨xa, xb, ya, y⟩).ok && force lo && force hi)
    · simp [hc] at h
    rw [hc, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨⟨⟨hy, hok⟩, -⟩, -⟩ := hc
    obtain ⟨hyS, ih1, ih2⟩ := ih y _ _ L H h
    have hyaS : ya ≤ S := hy.trans hyS
    refine ⟨hyaS, ?_⟩
    have h0 : (0 : ℝ) ≤ (xa : ℝ) / S := by positivity
    have hxab : (xa : ℝ) / S ≤ (xb : ℝ) / S := by gcongr
    have hx1 : (xb : ℝ) / S ≤ 1 := by rw [div_le_one hS]; exact_mod_cast hb
    have hyy : (ya : ℝ) / S ≤ (y : ℝ) / S := by gcongr
    have hy1 : (y : ℝ) / S ≤ 1 := by rw [div_le_one hS]; exact_mod_cast hyS
    have hya0 : (0 : ℝ) ≤ (ya : ℝ) / S := by positivity
    set A := Ioc ((xa : ℝ) / S) ((xb : ℝ) / S) with hA
    have hsub : ∀ c d : ℝ, 0 ≤ c → d ≤ 1 → A ×ˢ Ioc c d ⊆ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 :=
      fun c d hc hd => prod_mono (Ioc_subset_Ioc h0 hx1) (Ioc_subset_Ioc hc hd)
    have hunion : A ×ˢ Ioc ((ya : ℝ) / S) 1 =
        A ×ˢ Ioc ((ya : ℝ) / S) ((y : ℝ) / S) ∪ A ×ˢ Ioc ((y : ℝ) / S) 1 := by
      rw [← prod_union, Ioc_union_Ioc_eq_Ioc hyy hy1]
    have hdisj : Disjoint (A ×ˢ Ioc ((ya : ℝ) / S) ((y : ℝ) / S)) (A ×ˢ Ioc ((y : ℝ) / S) 1) :=
      disjoint_prod.2 (Or.inr (Ioc_disjoint_Ioc_of_le le_rfl))
    have hint := setIntegral_union hdisj (measurableSet_Ioc.prod measurableSet_Ioc)
      (hf.mono_set (hsub _ _ hya0 hy1)) (hf.mono_set (hsub _ _ (hya0.trans hyy) le_rfl))
    have hbox := integral_box_bounds (f := f) hxab hyy (hf.mono_set (hsub _ _ hya0 hy1))
      (l := ((F ⟨xa, xb, ya, y⟩).lo : ℝ) / S) (u := ((F ⟨xa, xb, ya, y⟩).hi : ℝ) / S)
      (fun z hz => hF ⟨xa, xb, ya, y⟩ z hz (hsub _ _ hya0 hy1 hz) hok)
    rw [← weight_div hab hy, ← weight_div hab hy] at hbox
    rw [hunion, hint]
    simp only [Int.add_def, Int.mul_def] at ih1 ih2
    push_cast at ih1 ih2 hbox ⊢
    constructor
    · calc ((L : ℝ) - lo) / S ^ 3 =
            (weight xa xb ya y : ℝ) * (F ⟨xa, xb, ya, y⟩).lo / S ^ 3 +
              (L - (lo + weight xa xb ya y * (F ⟨xa, xb, ya, y⟩).lo)) / S ^ 3 := by ring
        _ ≤ _ := add_le_add hbox.1 ih1
    · calc _ ≤ (weight xa xb ya y : ℝ) * (F ⟨xa, xb, ya, y⟩).hi / S ^ 3 +
              (H - (hi + weight xa xb ya y * (F ⟨xa, xb, ya, y⟩).hi)) / S ^ 3 :=
            add_le_add hbox.2 ih2
        _ = ((H : ℝ) - hi) / S ^ 3 := by ring

theorem partSum_sound
    (hF : ∀ B : Box S, ∀ z ∈ B.toSet, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 → f z ∈ F B)
    (hf : IntegrableOn f (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)) (P : List Strip) :
    ∀ (xa : ℕ) (lo hi L H : ℤ), partSum F xa P lo hi = some (L, H) →
      xa ≤ S ∧
      ((L - lo : ℤ) : ℝ) / (S : ℝ) ^ 3 ≤ ∫ z in Ioc ((xa : ℝ) / S) 1 ×ˢ Ioc (0 : ℝ) 1, f z ∧
      ∫ z in Ioc ((xa : ℝ) / S) 1 ×ˢ Ioc (0 : ℝ) 1, f z ≤ ((H - hi : ℤ) : ℝ) / (S : ℝ) ^ 3 := by
  have hS := Interval.scale_pos (S := S)
  have hSne : (S : ℝ) ≠ 0 := hS.ne'
  induction P with
  | nil =>
    intro xa lo hi L H h
    simp only [partSum] at h
    cases hc : Nat.beq xa S
    · simp [hc] at h
    · simp only [hc, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hxa : xa = S := Nat.eq_of_beq_eq_true hc
      subst hxa
      simp [hSne]
  | cons s P ih =>
    intro xa lo hi L H h
    simp only [partSum] at h
    cases hc : Nat.ble xa s.x
    · simp [hc] at h
    rw [hc, Bool.cond_true] at h
    rw [Nat.ble_eq] at hc
    cases hs : stripSum F xa s.x 0 s.ys lo hi with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨lo', hi'⟩ := p
      simp only [hs] at h
      obtain ⟨hxS, ih1, ih2⟩ := ih s.x lo' hi' L H h
      obtain ⟨-, hs1, hs2⟩ := stripSum_sound hF hf hc hxS s.ys 0 lo hi lo' hi' hs
      refine ⟨hc.trans hxS, ?_⟩
      have hxx : (xa : ℝ) / S ≤ (s.x : ℝ) / S := by gcongr
      have hx1 : (s.x : ℝ) / S ≤ 1 := by rw [div_le_one hS]; exact_mod_cast hxS
      have h0 : (0 : ℝ) ≤ (xa : ℝ) / S := by positivity
      have hsub : ∀ c d : ℝ, 0 ≤ c → d ≤ 1 →
          Ioc c d ×ˢ Ioc (0 : ℝ) 1 ⊆ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 :=
        fun c d hc hd => prod_mono (Ioc_subset_Ioc hc hd) subset_rfl
      have hunion : Ioc ((xa : ℝ) / S) 1 ×ˢ Ioc (0 : ℝ) 1 =
          Ioc ((xa : ℝ) / S) ((s.x : ℝ) / S) ×ˢ Ioc (0 : ℝ) 1 ∪
            Ioc ((s.x : ℝ) / S) 1 ×ˢ Ioc (0 : ℝ) 1 := by
        rw [← union_prod, Ioc_union_Ioc_eq_Ioc hxx hx1]
      have hdisj : Disjoint (Ioc ((xa : ℝ) / S) ((s.x : ℝ) / S) ×ˢ Ioc (0 : ℝ) 1)
          (Ioc ((s.x : ℝ) / S) 1 ×ˢ Ioc (0 : ℝ) 1) :=
        disjoint_prod.2 (Or.inl (Ioc_disjoint_Ioc_of_le le_rfl))
      have hint := setIntegral_union hdisj (measurableSet_Ioc.prod measurableSet_Ioc)
        (hf.mono_set (hsub _ _ h0 hx1)) (hf.mono_set (hsub _ _ (h0.trans hxx) le_rfl))
      rw [hunion, hint]
      simp only [Nat.cast_zero, zero_div] at hs1 hs2
      push_cast at ih1 ih2 hs1 hs2 ⊢
      constructor
      · calc ((L : ℝ) - lo) / S ^ 3 = (lo' - lo) / S ^ 3 + (L - lo') / S ^ 3 := by ring
          _ ≤ _ := add_le_add hs1 ih1
      · calc _ ≤ ((hi' : ℝ) - hi) / S ^ 3 + (H - hi') / S ^ 3 := add_le_add hs2 ih2
          _ = ((H : ℝ) - hi) / S ^ 3 := by ring

omit [NeZero S] in
/-- **Soundness of the box-partition checker.** If `f` is integrable on the unit square, the
interval extension `F` is sound for `f` on every box (at points of `(0, 1]²`), and the checker
accepts the partition `P` with claimed bounds `lo`, `hi`, then `lo ≤ ∫ f ≤ hi` for the measure
`QED.Integration.feynmanMeasure`. -/
theorem integral_bounds_of_check {f : ℝ × ℝ → ℝ} {F : Box S → Interval S} {P : List Strip}
    {lo hi : ℚ} (hf : Integrable f QED.Integration.feynmanMeasure)
    (hF : ∀ B : Box S, ∀ z ∈ B.toSet, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 → f z ∈ F B)
    (h : check F P lo hi = true) :
    (lo : ℝ) ≤ ∫ z, f z ∂QED.Integration.feynmanMeasure ∧
      ∫ z, f z ∂QED.Integration.feynmanMeasure ≤ hi := by
  unfold check at h
  cases hp : partSum F 0 P 0 0 with
  | none => simp [hp] at h
  | some p =>
    obtain ⟨L, H⟩ := p
    simp only [hp, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_iff] at h
    obtain ⟨⟨hS0, hlo⟩, hhi⟩ := h
    have : NeZero S := ⟨Nat.pos_iff_ne_zero.1 hS0⟩
    have hS := Interval.scale_pos (S := S)
    rw [QED.Integration.feynmanMeasure_eq] at hf ⊢
    obtain ⟨-, h1, h2⟩ := partSum_sound hF hf P 0 0 0 L H hp
    simp only [Nat.cast_zero, zero_div, sub_zero] at h1 h2
    have hS3 : (0 : ℝ) < (S : ℝ) ^ 3 := by positivity
    have hld : (0 : ℝ) < lo.den := by exact_mod_cast lo.den_pos
    have hhd : (0 : ℝ) < hi.den := by exact_mod_cast hi.den_pos
    constructor
    · refine le_trans ?_ h1
      rw [Rat.cast_def, div_le_div_iff₀ hld hS3]
      have : ((lo.num * ((S : ℤ) * S * S) : ℤ) : ℝ) ≤ ((L * lo.den : ℤ) : ℝ) := by
        exact_mod_cast hlo
      push_cast at this
      linarith
    · refine h2.trans ?_
      rw [Rat.cast_def, div_le_div_iff₀ hS3 hhd]
      have : ((H * hi.den : ℤ) : ℝ) ≤ ((hi.num * ((S : ℤ) * S * S) : ℤ) : ℝ) := by
        exact_mod_cast hhi
      push_cast at this
      linarith

omit [NeZero S] in
/-- `integral_bounds_of_check` for an integrand continuous on the closed unit square. -/
theorem integral_bounds_of_check_of_continuousOn {f : ℝ × ℝ → ℝ} {F : Box S → Interval S}
    {P : List Strip} {lo hi : ℚ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hF : ∀ B : Box S, ∀ z ∈ B.toSet, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 → f z ∈ F B)
    (h : check F P lo hi = true) :
    (lo : ℝ) ≤ ∫ z, f z ∂QED.Integration.feynmanMeasure ∧
      ∫ z, f z ∂QED.Integration.feynmanMeasure ≤ hi := by
  refine integral_bounds_of_check ?_ hF h
  rw [QED.Integration.feynmanMeasure_eq]
  exact (hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

end Quadrature

end QED.Numerics

end
