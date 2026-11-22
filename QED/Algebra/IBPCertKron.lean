/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertEval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Split IBP certificates checked at one large integer point (layer L2)

`QED.Algebra.IBPCert.Step` checks a polynomial identity in `d` at `n` points, where `n` exceeds
the degree. For three-loop reductions the multipliers have degree about `20`, and the kernel
spends nearly all its time on the `n` values of every term. This module checks the same kind of
step at a **single** integer point `x₀`, chosen larger than a bound `C` on the coefficients:

* every coefficient `pₗ` of the combination is an integer polynomial with `‖pₗ‖₁ ≤ C`, where `C`
  is computed by the checker from the data (`QED.Algebra.IBPCert.KStep.bound`), using
  `‖p q‖₁ ≤ ‖p‖₁ ‖q‖₁`;
* an integer polynomial `p` with `‖p‖₁ < x₀` and `p(x₀) = 0` is zero: its constant coefficient is
  divisible by `x₀` and smaller than `x₀` in absolute value
  (`QED.Algebra.IBPCert.Poly.eval_eq_zero_of_evalZ`).

The vanishing of each label's coefficient at `x₀` is checked on the merged list of values, so
the soundness proof separates the labels one at a time (`QED.Algebra.IBPCert.kron_sum_eq_zero`).

## Main statements

* `QED.Algebra.IBPCert.KStep.sound`: if `KStep.check` accepts, the IBP relations hold at the
  step's seeds, the integrals of its `zeros` vanish and its `rels` hold at `d`, then its claim
  holds at `d`, in any field.
-/

@[expose] public section

namespace QED.Algebra.IBPCert

namespace Poly

/-- The `ℓ¹` norm `Σ |aᵢ|` of the coefficients. -/
def norm1 : Poly → ℕ
  | [] => 0
  | a :: p => a.natAbs + norm1 p

@[simp] theorem norm1_nil : norm1 [] = 0 := rfl

@[simp] theorem norm1_cons (a : ℤ) (p : Poly) : norm1 (a :: p) = a.natAbs + norm1 p := rfl

theorem norm1_add : ∀ p q : Poly, norm1 (add p q) ≤ norm1 p + norm1 q
  | [], q => by simp [add]
  | a :: p, [] => by simp [add]
  | a :: p, b :: q => by
    simp only [add, norm1_cons, int_add_eq]
    have := norm1_add p q
    have := Int.natAbs_add_le a b
    omega

theorem norm1_smul (c : ℤ) : ∀ p : Poly, norm1 (smul c p) = c.natAbs * norm1 p
  | [] => by simp [smul]
  | a :: p => by
    simp only [smul, norm1_cons, int_mul_eq, Int.natAbs_mul, norm1_smul c p]
    ring

theorem norm1_neg (p : Poly) : norm1 (neg p) = norm1 p := by
  simp [neg, norm1_smul]

theorem norm1_mul : ∀ p q : Poly, norm1 (mul p q) ≤ norm1 p * norm1 q
  | [], q => by simp [mul]
  | a :: p, q => by
    have h1 := norm1_add (smul a q) (0 :: mul p q)
    have h2 := Nat.add_le_add_left (norm1_mul p q) (a.natAbs * norm1 q)
    simp only [norm1_smul, norm1_cons, Int.natAbs_zero, zero_add] at h1
    simp only [mul, norm1_cons, add_mul]
    exact h1.trans h2

theorem evalZ_eq_eval (x : ℤ) (p : Poly) : evalZ x p = Poly.eval x p := by
  simpa using cast_evalZ (K := ℤ) x p

/-- **Uniqueness of base-`x` expansions.** An integer polynomial with `‖p‖₁ < x` and `p(x) = 0`
vanishes everywhere. -/
theorem eval_eq_zero_of_evalZ {x : ℤ} : ∀ {p : Poly}, (norm1 p : ℤ) < x → evalZ x p = 0 →
    ∀ {K : Type*} [CommRing K] (d : K), Poly.eval d p = 0
  | [], _, _, _, _, d => by simp [Poly.eval]
  | a :: p, hb, h0, K, _, d => by
    simp only [evalZ, int_add_eq, int_mul_eq] at h0
    simp only [norm1_cons, Nat.cast_add] at hb
    have hx : 0 < x := by have := Int.natCast_nonneg (norm1 p); omega
    have hp : evalZ x p = 0 := by
      by_contra hne
      have ha : a.natAbs = x.natAbs * (evalZ x p).natAbs := by
        rw [← Int.natAbs_mul, show a = -(x * evalZ x p) by omega, Int.natAbs_neg]
      have h1 : 1 ≤ (evalZ x p).natAbs := Int.natAbs_pos.2 hne
      have h2 : x.natAbs ≤ a.natAbs := by rw [ha]; exact Nat.le_mul_of_pos_right _ h1
      have h3 : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx.le
      have := Int.natCast_nonneg (norm1 p)
      omega
    have ha : a = 0 := by rw [hp, mul_zero, add_zero] at h0; exact h0
    have hb' : (norm1 p : ℤ) < x := by
      have := Int.natCast_nonneg a.natAbs; omega
    rw [Poly.eval_cons, ha, eval_eq_zero_of_evalZ hb' hp d]
    simp

end Poly

/-! ### Separating the labels -/

section Kron

variable {K : Type*} [CommRing K]

theorem sum_map_filter_add {α R : Type*} [AddCommMonoid R] (f : α → R) (q : α → Bool) :
    ∀ T : List α, (T.map f).sum = ((T.filter q).map f).sum + ((T.filter fun t => !q t).map f).sum
  | [] => by simp
  | t :: T => by
    have := sum_map_filter_add f q T
    cases h : q t <;> simp [h, this] <;> abel

/-- The sum of the polynomials of a list. -/
def polySum (T : List Poly) : Poly := T.foldr Poly.add []

theorem eval_polySum (d : K) : ∀ T : List Poly, Poly.eval d (polySum T) = (T.map (Poly.eval d)).sum
  | [] => by simp [polySum]
  | p :: T => by simp [polySum, Poly.eval_add, ← eval_polySum d T]

theorem norm1_polySum : ∀ T : List Poly, Poly.norm1 (polySum T) ≤ (T.map Poly.norm1).sum
  | [] => by simp [polySum]
  | p :: T => by
    have := Poly.norm1_add p (polySum T)
    have := norm1_polySum T
    simp only [polySum, List.foldr_cons, List.map_cons, List.sum_cons] at *
    omega

theorem sum_map_filter_label {R : Type*} [CommRing R] (y : R) (J : ℕ → R) (l : ℕ)
    (T : List (ℕ × Poly)) :
    (((T.filter fun t => Nat.beq t.1 l).map fun t => Poly.eval y t.2 * J t.1)).sum =
      Poly.eval y (polySum ((T.filter fun t => Nat.beq t.1 l).map Prod.snd)) * J l := by
  rw [eval_polySum, List.map_map, ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have := (List.mem_filter.1 ht).2
  rw [Nat.eq_of_beq_eq_true this]; rfl

/-- **Separation of labels.** If `Σ pₜ(x) J(lₜ) = 0` for every integer weight `J` vanishing on
the labels `z`, and `x` exceeds the total `ℓ¹` norm, then `Σ pₜ(d) J(lₜ) = 0` for every `d` and
every weight `J` vanishing on `z`, in any commutative ring. -/
theorem kron_sum_eq_zero (z : ℕ → Bool) (x : ℤ) :
    ∀ (n : ℕ) (T : List (ℕ × Poly)), T.length ≤ n →
      ((T.map fun t => Poly.norm1 t.2).sum : ℤ) < x →
      (∀ J : ℕ → ℤ, (∀ l, z l = true → J l = 0) →
        (T.map fun t => evalZ x t.2 * J t.1).sum = 0) →
      ∀ (d : K) (J : ℕ → K), (∀ l, z l = true → J l = 0) →
        (T.map fun t => Poly.eval d t.2 * J t.1).sum = 0
  | _, [], _, _, _, d, J, _ => by simp
  | 0, _ :: _, hn, _, _, _, _, _ => by simp at hn
  | n + 1, t₀ :: T, hn, hb, h, d, J, hJ => by
    set l := t₀.1
    set q : ℕ × Poly → Bool := fun t => Nat.beq t.1 l
    have hq : ∀ t, q t = true ↔ t.1 = l := fun t => by simp [q, Nat.beq_eq]
    set A := (t₀ :: T).filter q
    set R := (t₀ :: T).filter fun t => !q t
    have hR : R.length ≤ n := by
      have : R = T.filter fun t => !q t := by simp [R, (hq t₀).2 rfl]
      rw [this]; simp only [List.length_cons] at hn
      exact (List.length_filter_le _ _).trans (by omega)
    have hnorm := sum_map_filter_add (fun t : ℕ × Poly => Poly.norm1 t.2) q (t₀ :: T)
    -- the part with label `l`
    have hA : (A.map fun t => Poly.eval d t.2 * J t.1).sum = 0 := by
      rw [sum_map_filter_label]
      cases hz : z l
      · have h1 := h (fun m => if m = l then 1 else 0) (fun m hm => by
          have : m ≠ l := fun h' => by rw [h'] at hm; simp [hz] at hm
          simp [this])
        rw [sum_map_filter_add _ q] at h1
        have h2 : ((((t₀ :: T).filter fun t => !q t).map fun t =>
            evalZ x t.2 * if t.1 = l then (1 : ℤ) else 0)).sum = 0 := by
          refine List.sum_eq_zero fun v hv => ?_
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
          have : t.1 ≠ l := fun h' => by
            have := (List.mem_filter.1 ht).2; simp [(hq t).2 h'] at this
          simp [this]
        have h3 := sum_map_filter_label x (fun m => if m = l then (1 : ℤ) else 0) l (t₀ :: T)
        simp only [ite_true, mul_one] at h3
        rw [h2, add_zero] at h1
        simp only [Poly.evalZ_eq_eval] at h1
        rw [h1] at h3
        have hb' : ((Poly.norm1 (polySum (A.map Prod.snd)) : ℕ) : ℤ) < x := by
          have := norm1_polySum (A.map Prod.snd)
          rw [List.map_map] at this
          have h4 : (Poly.norm1 (polySum (A.map Prod.snd))) ≤
              ((t₀ :: T).map fun t => Poly.norm1 t.2).sum := by
            rw [hnorm]; exact this.trans (Function.comp_def _ _ ▸ Nat.le_add_right _ _)
          omega
        rw [Poly.eval_eq_zero_of_evalZ hb' (by rw [Poly.evalZ_eq_eval]; exact h3.symm) d, zero_mul]
      · rw [hJ l hz, mul_zero]
    -- the rest, by induction
    have hRest : (R.map fun t => Poly.eval d t.2 * J t.1).sum = 0 := by
      refine kron_sum_eq_zero z x n R hR ?_ ?_ d J hJ
      · have : (R.map fun t => Poly.norm1 t.2).sum ≤ ((t₀ :: T).map fun t => Poly.norm1 t.2).sum :=
          by rw [hnorm]; exact Nat.le_add_left _ _
        omega
      · intro J' hJ'
        have h1 := h (fun m => if m = l then 0 else J' m) (fun m hm => by
          split_ifs <;> simp [hJ' m hm])
        rw [sum_map_filter_add _ q] at h1
        have h2 : (A.map fun t => evalZ x t.2 * if t.1 = l then 0 else J' t.1).sum = 0 := by
          refine List.sum_eq_zero fun v hv => ?_
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
          simp [(hq t).1 (List.mem_filter.1 ht).2]
        rw [h2, zero_add] at h1
        rw [← h1]
        refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
        have : t.1 ≠ l := fun h' => by
          have := (List.mem_filter.1 ht).2; simp [(hq t).2 h'] at this
        simp [this]
    rw [sum_map_filter_add _ q, hA, hRest, add_zero]

end Kron

/-! ### Steps checked at one point -/

/-- One step of a split certificate, checked at the single point `x0` (see the module
docstring). The fields are those of `QED.Algebra.IBPCert.Step`, with `x0` in place of the number
of points. -/
structure KStep where
  /-- The relation proved by this step. -/
  claim : List (List ℤ × Poly)
  /-- The evaluation point. -/
  x0 : ℕ
  /-- IBP seeds with multipliers. -/
  seeds : List Seed
  /-- Relations proved earlier, with multipliers. -/
  rels : List (List (List ℤ × Poly) × Poly)
  /-- Labels treated as vanishing. -/
  zeros : List (List ℤ)

namespace KStep

variable (F : Family) (B o : ℕ) (c : KStep)

/-- The bound on the `ℓ¹` norm of the coefficients of the combination. -/
def bound : ℕ :=
  (c.claim.map fun t => Poly.norm1 t.2).sum +
  (c.seeds.map fun s => Poly.norm1 s.mult *
    ((F.tmplAt s.i s.j).map fun t => (Step.termConst s t).natAbs + t.cd.natAbs).sum).sum +
  (c.rels.map fun r => Poly.norm1 r.2 * (r.1.map fun t => Poly.norm1 t.2).sum).sum

/-- The claim, negated, as values at `x0`. -/
def claimVec : VComb :=
  VComb.sort (c.claim.map fun t => (pack B o t.1, [evalZ (.ofNat c.x0) (Poly.neg t.2)]))

/-- A seed relation times its multiplier, given the value `m` of the multiplier at `x0`. -/
def seedVecOf (s : Seed) (m : ℤ) : VComb :=
  VComb.sort <| (F.tmplAt s.i s.j).map fun t =>
    (pack B o (Poly.add s.nu t.shift),
      [Int.mul m (Int.add (Step.termConst s t) (Int.mul t.cd (.ofNat c.x0)))])

/-- An earlier relation times its multiplier, given the value `m` of the multiplier at `x0`. -/
def relVecOf (r : List (List ℤ × Poly)) (m : ℤ) : VComb :=
  VComb.sort (r.map fun t => (pack B o t.1, [Int.mul m (evalZ (.ofNat c.x0) t.2)]))

/-- The admissibility conditions: template, seeds, label ranges, and `bound < x0`. -/
def admissible : Bool :=
  let N := F.nProp
  F.tmplOk && c.seeds.all (Seed.ok F) &&
  c.seeds.all (fun s => (F.tmplAt s.i s.j).all fun t => inRange B o N (Poly.add s.nu t.shift)) &&
  c.claim.all (fun t => inRange B o N t.1) &&
  c.rels.all (fun r => r.1.all fun t => inRange B o N t.1) &&
  c.zeros.all (fun l => inRange B o N l && F.zeroPred l) &&
  Nat.blt (bound F c) c.x0

/-- The step checker. -/
def check : Bool :=
  admissible F B o c &&
    VComb.vanishes (fun l => (c.zeros.map (pack B o)).any (Nat.beq l))
      (VComb.sumTree 64 (claimVec B o c ::
        (c.seeds.map fun s => seedVecOf F B o c s (evalZ (.ofNat c.x0) s.mult)) ++
        (c.rels.map fun r => relVecOf B o c r.1 (evalZ (.ofNat c.x0) r.2))))

/-- The terms of the combination, with packed labels and polynomial coefficients. -/
def terms : List (ℕ × Poly) :=
  c.claim.map (fun t => (pack B o t.1, Poly.neg t.2)) ++
  (c.seeds.flatMap fun s => (F.tmplAt s.i s.j).map fun t =>
    (pack B o (Poly.add s.nu t.shift), Poly.mul s.mult [Step.termConst s t, t.cd])) ++
  (c.rels.flatMap fun r => r.1.map fun t => (pack B o t.1, Poly.mul r.2 t.2))

theorem sum_flatMap {α β R : Type*} [AddCommMonoid R] (g : β → R) (f : α → List β) :
    ∀ L : List α, ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum
  | [] => by simp
  | a :: L => by simp [List.flatMap_cons, sum_flatMap g f L]

/-- The sum over `terms` splits into the claim, seed and relation parts. -/
theorem sum_terms {R : Type*} [CommRing R] (y : R) (J : ℕ → R) :
    ((terms F B o c).map fun t => Poly.eval y t.2 * J t.1).sum =
      (c.claim.map fun t => Poly.eval y (Poly.neg t.2) * J (pack B o t.1)).sum +
      (c.seeds.map fun s => ((F.tmplAt s.i s.j).map fun t =>
        Poly.eval y (Poly.mul s.mult [Step.termConst s t, t.cd]) *
          J (pack B o (Poly.add s.nu t.shift))).sum).sum +
      (c.rels.map fun r => (r.1.map fun t =>
        Poly.eval y (Poly.mul r.2 t.2) * J (pack B o t.1)).sum).sum := by
  simp only [terms, List.map_append, List.sum_append, sum_flatMap, List.map_map]
  rfl

theorem norm_terms : ((terms F B o c).map fun t => Poly.norm1 t.2).sum ≤ bound F c := by
  simp only [terms, bound, List.map_append, List.sum_append, sum_flatMap, List.map_map]
  refine Nat.add_le_add (Nat.add_le_add (le_of_eq ?_) ?_) ?_
  · exact congrArg List.sum (List.map_congr_left fun t _ => Poly.norm1_neg _)
  · refine List.sum_le_sum fun s _ => ?_
    simp only [Function.comp_def, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun t _ => ?_
    refine (Poly.norm1_mul _ _).trans (le_of_eq ?_)
    simp
  · refine List.sum_le_sum fun r _ => ?_
    simp only [Function.comp_def, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun t _ => Poly.norm1_mul _ _

end KStep

namespace KStep

variable {F : Family} {B o : ℕ} {c : KStep}

/-- **Soundness of a step.** If the check passes, the IBP relations hold at the step's seeds, the
integrals of its `zeros` vanish and the relations `rels` hold at `d`, then the claim holds at
`d`. -/
theorem sound {K : Type*} [Field K] (h : c.check F B o = true)
    (I : (Fin F.nProp → ℤ) → K → K) (d : K)
    (hI : ∀ s ∈ c.seeds, F.IBPHoldsAt I d s.i s.j (toVec F.nProp s.nu))
    (hz : ∀ l ∈ c.zeros, I (toVec F.nProp l) d = 0)
    (hr : ∀ r ∈ c.rels, LinComb.eval (fun l => I (toVec F.nProp l) d) d r.1 = 0) :
    LinComb.eval (fun l => I (toVec F.nProp l) d) d c.claim = 0 := by
  set Jl : List ℤ → K := fun l => I (toVec F.nProp l) d with hJl
  set Jn : ℕ → K := fun l => I (decodeVec F.nProp B o l) d with hJn
  simp only [check, admissible, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨ht, hsok⟩, hseed⟩, hclaim⟩, hrel⟩, hzero⟩, hbd⟩, hvan⟩ := h
  have hJ : ∀ l, inRange B o F.nProp l = true → Jn (pack B o l) = Jl l := by
    intro l hl; simp only [hJn, hJl, decodeVec_pack hl]
  set z : ℕ → Bool := fun l => (c.zeros.map (pack B o)).any (Nat.beq l) with hzdef
  have hzJ : ∀ l, z l = true → Jn l = 0 := by
    intro l hl
    simp only [hzdef, List.any_eq_true, List.mem_map] at hl
    obtain ⟨_, ⟨m, hm, rfl⟩, hb⟩ := hl
    rw [Nat.eq_of_beq_eq_true hb, hJ m (hzero m hm).1]; exact hz m hm
  -- the checker's values: the combination vanishes at `x0` for every integer weight
  have hx : ∀ J : ℕ → ℤ, (∀ l, z l = true → J l = 0) →
      ((terms F B o c).map fun t => evalZ (c.x0 : ℤ) t.2 * J t.1).sum = 0 := by
    intro J hJz
    have hv := VComb.evalAt_eq_zero_of_vanishes J 0 hJz hvan
    rw [VComb.evalAt_sumTree] at hv
    simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map]
      at hv
    simp only [Poly.evalZ_eq_eval]
    rw [sum_terms, ← hv]
    congr 1
    congr 1
    · rw [claimVec, VComb.evalAt_sort, VComb.evalAt_map]
      refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
      simp [Poly.evalZ_eq_eval]
    · refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
      simp only [Function.comp_apply, seedVecOf, VComb.evalAt_sort, VComb.evalAt_map]
      refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
      simp only [List.getD_cons_zero, Poly.int_mul_eq, Poly.int_add_eq, Poly.evalZ_eq_eval,
        Poly.eval_mul, Poly.eval_cons, Poly.eval_nil, Int.cast_id, Int.ofNat_eq_natCast]
      ring
    · refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
      simp only [Function.comp_apply, relVecOf, VComb.evalAt_sort, VComb.evalAt_map]
      refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
      simp only [List.getD_cons_zero, Poly.int_mul_eq, Poly.evalZ_eq_eval, Poly.eval_mul,
        Int.ofNat_eq_natCast, Int.cast_id]
  have hb : (((terms F B o c).map fun t => Poly.norm1 t.2).sum : ℤ) < (c.x0 : ℤ) := by
    have := norm_terms F B o c; omega
  have hd := kron_sum_eq_zero z (c.x0 : ℤ) _ _ le_rfl hb hx d Jn hzJ
  rw [sum_terms] at hd
  -- back to unpacked labels
  have e1 : (c.claim.map fun t => Poly.eval d (Poly.neg t.2) * Jn (pack B o t.1)) =
      c.claim.map fun t => Poly.eval d (Poly.neg t.2) * Jl t.1 :=
    List.map_congr_left fun t ht => by rw [hJ t.1 (hclaim t ht)]
  have hseeds : (c.seeds.map fun s => ((F.tmplAt s.i s.j).map fun t =>
      Poly.eval d (Poly.mul s.mult [Step.termConst s t, t.cd]) *
        Jn (pack B o (Poly.add s.nu t.shift))).sum).sum = 0 := by
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
        Poly.eval d (Poly.mul s.mult [Step.termConst s t, t.cd]) *
          Jn (pack B o (Poly.add s.nu t.shift))) =
        (F.tmplAt s.i s.j).map fun t => Poly.eval d s.mult *
          (t.coeff d (toVec F.nProp s.nu) *
            I (toVec F.nProp s.nu + toVec F.nProp t.shift) d) := by
      refine List.map_congr_left fun t ht' => ?_
      rw [hJ _ (hseed s hs t ht')]
      simp only [Poly.eval_mul, Poly.eval_cons, Poly.eval_nil, hJl, toVec_polyAdd, Term.coeff,
        vecGet_toVec hl, Step.termConst, Poly.int_add_eq, Poly.int_mul_eq]
      push_cast; ring
    rw [e, sum_map_mul_left, this, mul_zero]
  have hrels : (c.rels.map fun r => (r.1.map fun t =>
      Poly.eval d (Poly.mul r.2 t.2) * Jn (pack B o t.1)).sum).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    have e : (r.1.map fun t => Poly.eval d (Poly.mul r.2 t.2) * Jn (pack B o t.1)) =
        r.1.map fun t => Poly.eval d r.2 * (Poly.eval d t.2 * Jl t.1) := by
      refine List.map_congr_left fun t ht => ?_
      rw [Poly.eval_mul, hJ t.1 (hrel r hr' t ht)]; ring
    rw [e, sum_map_mul_left, ← LinComb.eval_eq_sum, hr r hr', mul_zero]
  rw [e1, hseeds, hrels, sum_map_neg_eval] at hd
  linear_combination -hd

/-- `KStep.sound` with the earlier relations given as `RelsHold`. -/
theorem sound' {K : Type*} [Field K] (h : c.check F B o = true)
    (I : (Fin F.nProp → ℤ) → K → K) (d : K)
    (hI : ∀ s ∈ c.seeds, F.IBPHoldsAt I d s.i s.j (toVec F.nProp s.nu))
    (hz : ∀ l ∈ c.zeros, I (toVec F.nProp l) d = 0)
    (hr : Step.RelsHold (fun l => I (toVec F.nProp l) d) d c.rels) :
    LinComb.eval (fun l => I (toVec F.nProp l) d) d c.claim = 0 :=
  sound h I d hI hz (Step.RelsHold.forall hr)

end KStep

end QED.Algebra.IBPCert
