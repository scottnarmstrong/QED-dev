/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBBJoint
public import QED.TwoLoop.JointIntegralInvariance

/-!
# A power-counting majorant at three loops

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58), classes `VA`, `VB`, `VC`. Lines `x : Fin m` carry the linear forms
`L_x ℓ = ∑ₛ aₓₛ ℓₛ` of three loop momenta `ℓ : Fin 3 → E` (integer rows `aₓ`) and exponents
`eₓ`. With `ν(y) = 1 + ‖y‖`, the majorant is `∏ₓ ν(L_x ℓ)^{-eₓ}` (`majF`).

* **Exchange** (`exists_min_basis`): at every `ℓ`, a basis `t` (a triple of lines with nonzero
  determinant) minimising `∑_p ‖L_{t_p} ℓ‖` satisfies `‖L_{t_p} ℓ‖ ≤ ‖L_x ℓ‖` whenever replacing
  `t_p` by `x` gives a basis (`x` is *admissible* at `p`).
* **Allocation** (`majF_le`): if the exponents are split, `eₓ = ∑_p c x p`, with `c x p ≠ 0`
  only at admissible positions and `∑ₓ c x p ≥ R`, then `majF ≤ ∏_p ν(L_{t_p} ℓ)^{-R}`.
* **Criterion** (`BasisCrit`): every basis has determinant `±1` and has such an allocation;
  `critB` is a Boolean test with the allocation `alloc` computed by a greedy rule
  (`basisCrit_of_critB`; soundness does not depend on the rule). The criterion is monotone in
  the exponents (`BasisCrit.mono_e`).
* **Integrability** (`integrable_majF`): under the criterion, if `ν^{-R}` is integrable on `E`
  and the integer unimodular matrices act on `Fin 3 → E` with determinant `±1`, the majorant is
  integrable on `Fin 3 → E` (it is at most the sum over the bases of products of `ν^{-R}` in
  unimodular coordinates). Instances: `E = ℝ` with `R = 2` (`integrable_majF_real`) and
  `E = ℝ⁴` with `R = 5` (`integrable_majF_four`).
-/

@[expose] public section

open MeasureTheory

namespace QED.ChainProof.SetALinkV

/-! ### Triples of lines -/

/-- The determinant of three integer rows. -/
def det3 (x y z : Fin 3 → ℤ) : ℤ :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) +
    x 2 * (y 0 * z 1 - y 1 * z 0)

variable {m : ℕ}

/-- A triple of lines. -/
abbrev Tri (m : ℕ) := Fin m × Fin m × Fin m

/-- The lines of a triple. -/
def triRow (t : Tri m) : Fin 3 → Fin m := ![t.1, t.2.1, t.2.2]

/-- The determinant of the rows of a triple. -/
def triDet (a : Fin m → Fin 3 → ℤ) (t : Tri m) : ℤ := det3 (a t.1) (a t.2.1) (a t.2.2)

/-- The triple with the line at position `p` replaced by `x`. -/
def triSet (t : Tri m) (x : Fin m) (p : Fin 3) : Tri m :=
  if p = 0 then (x, t.2.1, t.2.2) else if p = 1 then (t.1, x, t.2.2) else (t.1, t.2.1, x)

theorem triRow_triSet (t : Tri m) (x : Fin m) (p q : Fin 3) :
    triRow (triSet t x p) q = if q = p then x else triRow t q := by
  fin_cases p <;> fin_cases q <;> rfl

/-- The triple is strictly increasing. -/
def Sorted3 (t : Tri m) : Prop := t.1 < t.2.1 ∧ t.2.1 < t.2.2

instance (t : Tri m) : Decidable (Sorted3 t) := by unfold Sorted3; infer_instance

/-- The sorted triple. -/
def sort3 (t : Tri m) : Tri m :=
  if t.1 ≤ t.2.1 then
    (if t.2.1 ≤ t.2.2 then t else if t.1 ≤ t.2.2 then (t.1, t.2.2, t.2.1)
      else (t.2.2, t.1, t.2.1))
  else (if t.1 ≤ t.2.2 then (t.2.1, t.1, t.2.2) else if t.2.1 ≤ t.2.2 then (t.2.1, t.2.2, t.1)
      else (t.2.2, t.2.1, t.1))

theorem triDet_sort3 (a : Fin m → Fin 3 → ℤ) (t : Tri m) :
    triDet a (sort3 t) = triDet a t ∨ triDet a (sort3 t) = -triDet a t := by
  obtain ⟨i, j, k⟩ := t
  unfold sort3
  split_ifs <;> simp only [triDet, det3, true_or] <;>
    first | exact Or.inl (by ring1) | exact Or.inr (by ring1)

theorem sum_sort3 (f : Fin m → ℝ) (t : Tri m) :
    ∑ q, f (triRow (sort3 t) q) = ∑ q, f (triRow t q) := by
  obtain ⟨i, j, k⟩ := t
  unfold sort3
  split_ifs <;> simp [triRow, Fin.sum_univ_three] <;> ring

theorem sorted_sort3 (a : Fin m → Fin 3 → ℤ) {t : Tri m} (h : triDet a t ≠ 0) :
    Sorted3 (sort3 t) := by
  obtain ⟨i, j, k⟩ := t
  have hij : i ≠ j := by rintro rfl; apply h; simp only [triDet, det3]; ring
  have hik : i ≠ k := by rintro rfl; apply h; simp only [triDet, det3]; ring
  have hjk : j ≠ k := by rintro rfl; apply h; simp only [triDet, det3]; ring
  have hij' := Fin.val_ne_of_ne hij
  have hik' := Fin.val_ne_of_ne hik
  have hjk' := Fin.val_ne_of_ne hjk
  unfold sort3 Sorted3
  split_ifs <;> simp only [Fin.lt_def, Fin.le_def] at * <;> omega

/-- `x` is admissible at position `p` of `t`: replacing `t_p` by `x` gives a basis. -/
def admB (a : Fin m → Fin 3 → ℤ) (t : Tri m) (x : Fin m) (p : Fin 3) : Bool :=
  decide (triDet a (triSet t x p) ≠ 0)

/-- An allocation of the exponents to the positions of `t`; every line has an admissible
position. -/
def GoodAlloc (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (R : ℕ) (t : Tri m)
    (c : Fin m → Fin 3 → ℕ) : Prop :=
  (∀ x, ∑ p, c x p = e x) ∧ (∀ x p, c x p ≠ 0 → admB a t x p = true) ∧
    (∀ p, R ≤ ∑ x, c x p) ∧ ∀ x, ∃ p, admB a t x p = true

/-- **The basis criterion**: some triple is a basis, every basis is unimodular and carries an
allocation with threshold `R`. -/
def BasisCrit (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (R : ℕ) : Prop :=
  (∃ t, triDet a t ≠ 0) ∧ ∀ t, Sorted3 t → triDet a t ≠ 0 → |triDet a t| = 1 ∧
    ∃ c, GoodAlloc a e R t c

theorem BasisCrit.mono {a : Fin m → Fin 3 → ℤ} {e : Fin m → ℕ} {R R' : ℕ}
    (h : BasisCrit a e R) (hR : R' ≤ R) : BasisCrit a e R' := by
  refine ⟨h.1, fun t hs ht => ⟨(h.2 t hs ht).1, ?_⟩⟩
  obtain ⟨c, h1, h2, h3, h4⟩ := (h.2 t hs ht).2
  exact ⟨c, h1, h2, fun p => hR.trans (h3 p), h4⟩

/-- **The criterion is monotone in the exponents**: the excess goes to an admissible
position. -/
theorem BasisCrit.mono_e {a : Fin m → Fin 3 → ℤ} {e e' : Fin m → ℕ} {R : ℕ}
    (h : BasisCrit a e R) (he : ∀ x, e x ≤ e' x) : BasisCrit a e' R := by
  classical
  refine ⟨h.1, fun t hs ht => ⟨(h.2 t hs ht).1, ?_⟩⟩
  obtain ⟨c, h1, h2, h3, h4⟩ := (h.2 t hs ht).2
  choose q hq using h4
  refine ⟨fun x p => c x p + if p = q x then e' x - e x else 0, fun x => ?_, fun x p hp => ?_,
    fun p => (h3 p).trans (Finset.sum_le_sum fun x _ => Nat.le_add_right _ _), fun x => ⟨_, hq x⟩⟩
  · rw [Finset.sum_add_distrib, h1, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    have := he x
    omega
  · by_cases hc : c x p = 0
    · by_cases hpq : p = q x
      · exact hpq ▸ hq x
      · simp [hc, hpq] at hp
    · exact h2 x p hc

/-! ### The greedy allocation -/

/-- The admissible position of largest score (`0` if none is admissible). -/
def pick (A : Fin 3 → Bool) (sc : Fin 3 → ℤ) : Fin 3 :=
  (List.finRange 3).foldl (fun b p => if A p && (!A b || decide (sc b < sc p)) then p else b) 0

/-- One unit of exponent to the most urgent admissible position. -/
def unitStep (A : Fin 3 → Bool) (dem : ℤ) (fut : Fin 3 → ℤ)
    (s : (Fin 3 → ℕ) × (Fin 3 → ℕ)) : (Fin 3 → ℕ) × (Fin 3 → ℕ) :=
  let p := pick A fun q => dem - s.2 q - fut q
  (Function.update s.1 p (s.1 p + 1), Function.update s.2 p (s.2 p + 1))

/-- The allocation along a list of lines, with the running totals `w`, as a list of pairs. -/
def allocA (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (dem : ℤ) (t : Tri m) :
    List (Fin m) → (Fin 3 → ℕ) → List (Fin m × (Fin 3 → ℕ))
  | [], _ => []
  | x :: rest, w =>
    let fut : Fin 3 → ℤ := fun p =>
      ((rest.filter fun y => admB a t y p).map fun y => (e y : ℤ)).sum
    let r := (unitStep (admB a t x) dem fut)^[e x] (0, w)
    (x, r.1) :: allocA a e dem t rest r.2

/-- The number of admissible positions of a line. -/
def nAdm (a : Fin m → Fin 3 → ℤ) (t : Tri m) (x : Fin m) : ℕ :=
  ((List.finRange 3).filter (admB a t x)).length

/-- The lines with one, then two, then three admissible positions. -/
def ordL (a : Fin m → Fin 3 → ℤ) (t : Tri m) : List (Fin m) :=
  (List.finRange m).filter (fun x => nAdm a t x = 1) ++
    (List.finRange m).filter (fun x => nAdm a t x = 2) ++
      (List.finRange m).filter (fun x => nAdm a t x = 3)

/-- Look up the allocation of a line. -/
def lookA (l : List (Fin m × (Fin 3 → ℕ))) (x : Fin m) : Fin 3 → ℕ :=
  match l.find? (fun q => q.1 == x) with
  | some q => q.2
  | none => 0

/-- The greedy allocation. -/
def alloc (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (R : ℕ) (t : Tri m) : Fin m → Fin 3 → ℕ :=
  lookA (allocA a e R t (ordL a t) 0)

/-- `GoodAlloc` as a Boolean test. -/
def goodB (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (R : ℕ) (t : Tri m)
    (c : Fin m → Fin 3 → ℕ) : Bool :=
  (List.finRange m).all (fun x => (c x 0 + c x 1 + c x 2 == e x) &&
      (List.finRange 3).all (fun p => c x p == 0 || admB a t x p) &&
      (List.finRange 3).any (fun p => admB a t x p)) &&
    (List.finRange 3).all fun p => decide (R ≤ ((List.finRange m).map fun x => c x p).sum)

/-- **The Boolean criterion**, with the greedy allocation. -/
def critB (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (R : ℕ) : Bool :=
  (List.finRange m).any (fun i => (List.finRange m).any fun j =>
      (List.finRange m).any fun k => triDet a (i, j, k) != 0) &&
    (List.finRange m).all fun i => (List.finRange m).all fun j => (List.finRange m).all fun k =>
      !(decide (i < j) && decide (j < k)) || triDet a (i, j, k) == 0 ||
        ((triDet a (i, j, k)).natAbs == 1 && goodB a e R (i, j, k) (alloc a e R (i, j, k)))

theorem sum_finRange_map (f : Fin m → ℕ) : ((List.finRange m).map f).sum = ∑ x, f x := by
  rw [Fin.sum_univ_def]

theorem goodB_sound {a : Fin m → Fin 3 → ℤ} {e : Fin m → ℕ} {R : ℕ} {t : Tri m}
    {c : Fin m → Fin 3 → ℕ} (h : goodB a e R t c = true) : GoodAlloc a e R t c := by
  simp only [goodB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    true_and, forall_const, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
    sum_finRange_map] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x => ?_, fun x p hp => ?_, h2, fun x => (h1 x).2⟩
  · rw [Fin.sum_univ_three]
    exact (h1 x).1.1
  · rcases (h1 x).1.2 p with h | h
    · exact absurd h hp
    · exact h

/-- **Soundness of the Boolean criterion.** -/
theorem basisCrit_of_critB {a : Fin m → Fin 3 → ℤ} {e : Fin m → ℕ} {R : ℕ}
    (h : critB a e R = true) : BasisCrit a e R := by
  simp only [critB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    true_and, forall_const, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨i, j, k, h0⟩, h1⟩ := h
  refine ⟨⟨(i, j, k), h0⟩, fun ⟨i, j, k⟩ hs ht => ?_⟩
  rcases h1 i j k with (h | h) | ⟨h2, h3⟩
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    rcases h with h | h
    · exact absurd hs.1 h
    · exact absurd hs.2 h
  · exact absurd h ht
  · refine ⟨?_, _, goodB_sound h3⟩
    rw [Int.abs_eq_natAbs, h2]
    rfl

/-! ### The majorant -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear form of an integer row. -/
noncomputable def linF (r : Fin 3 → ℤ) (ℓ : Fin 3 → E) : E := ∑ s, (r s : ℝ) • ℓ s

/-- `ν(y) = 1 + ‖y‖`. -/
noncomputable def nu (y : E) : ℝ := 1 + ‖y‖

omit [NormedSpace ℝ E] in
theorem one_le_nu (y : E) : 1 ≤ nu y := by unfold nu; linarith [norm_nonneg y]

omit [NormedSpace ℝ E] in
theorem nu_pos (y : E) : 0 < nu y := lt_of_lt_of_le one_pos (one_le_nu y)

/-- **The majorant** `∏ₓ ν(L_x ℓ)^{-eₓ}`. -/
noncomputable def majF (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (ℓ : Fin 3 → E) : ℝ :=
  ∏ x, (nu (linF (a x) ℓ) ^ e x)⁻¹

theorem continuous_linF (r : Fin 3 → ℤ) : Continuous (linF (E := E) r) :=
  continuous_finsetSum _ fun s _ => (continuous_apply s).const_smul _

theorem continuous_majF (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) :
    Continuous (majF (E := E) a e) := by
  refine continuous_finsetProd _ fun x _ => ?_
  refine Continuous.inv₀ (((continuous_const.add
    ((continuous_linF (a x)).norm))).pow _) fun ℓ => (pow_pos (nu_pos _) _).ne'

theorem sum_triSet (f : Fin m → ℝ) (t : Tri m) (x : Fin m) (p : Fin 3) :
    ∑ q, f (triRow (triSet t x p) q) = ∑ q, f (triRow t q) - f (triRow t p) + f x := by
  simp only [triRow_triSet]
  fin_cases p <;> simp [Fin.sum_univ_three] <;> ring

/-- **The exchange property of a minimising basis.** -/
theorem exists_min_basis (a : Fin m → Fin 3 → ℤ) (h : ∃ t, triDet a t ≠ 0) (ℓ : Fin 3 → E) :
    ∃ t, Sorted3 t ∧ triDet a t ≠ 0 ∧ ∀ x p, admB a t x p = true →
      ‖linF (a (triRow t p)) ℓ‖ ≤ ‖linF (a x) ℓ‖ := by
  classical
  set Bs := (Finset.univ : Finset (Tri m)).filter fun t => Sorted3 t ∧ triDet a t ≠ 0
  have hS : ∀ t, triDet a t ≠ 0 → sort3 t ∈ Bs := fun t ht => by
    simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨sorted_sort3 a ht, ?_⟩
    rcases triDet_sort3 a t with h | h <;> rw [h]
    · exact ht
    · exact neg_ne_zero.mpr ht
  have hne : Bs.Nonempty := by
    obtain ⟨t, ht⟩ := h
    exact ⟨_, hS t ht⟩
  obtain ⟨t, ht, hmin⟩ := Bs.exists_min_image
    (fun t => ∑ q, ‖linF (a (triRow t q)) ℓ‖) hne
  refine ⟨t, (Finset.mem_filter.mp ht).2.1, (Finset.mem_filter.mp ht).2.2, fun x p hx => ?_⟩
  simp only [admB, decide_eq_true_eq] at hx
  have := hmin _ (hS _ hx)
  rw [sum_sort3 (fun y => ‖linF (a y) ℓ‖), sum_triSet (fun y => ‖linF (a y) ℓ‖)] at this
  linarith

/-- **The allocation bound.** -/
theorem majF_le (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (R : ℕ) (t : Tri m)
    (c : Fin m → Fin 3 → ℕ) (hc : GoodAlloc a e R t c) (ℓ : Fin 3 → E)
    (hmin : ∀ x p, admB a t x p = true → ‖linF (a (triRow t p)) ℓ‖ ≤ ‖linF (a x) ℓ‖) :
    majF a e ℓ ≤ ∏ p, (nu (linF (a (triRow t p)) ℓ) ^ R)⁻¹ := by
  obtain ⟨h1, h2, h3, -⟩ := hc
  set ν : Fin m → ℝ := fun x => nu (linF (a x) ℓ)
  set μ : Fin 3 → ℝ := fun p => nu (linF (a (triRow t p)) ℓ)
  have hν : ∀ x, 1 ≤ ν x := fun x => one_le_nu _
  have hμ : ∀ p, 1 ≤ μ p := fun p => one_le_nu _
  have e1 : majF a e ℓ = ∏ x, ∏ p, (ν x ^ c x p)⁻¹ := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← h1 x, ← Finset.prod_pow_eq_pow_sum, Finset.prod_inv_distrib]
  have e2 : ∀ x p, (ν x ^ c x p)⁻¹ ≤ (μ p ^ c x p)⁻¹ := by
    intro x p
    by_cases hz : c x p = 0
    · simp [hz]
    · have hle : μ p ≤ ν x := by
        have := hmin x p (h2 x p hz)
        simp only [μ, ν, nu]
        linarith
      exact inv_anti₀ (pow_pos (lt_of_lt_of_le one_pos (hμ p)) _)
        (pow_le_pow_left₀ (le_trans zero_le_one (hμ p)) hle _)
  calc majF a e ℓ = ∏ x, ∏ p, (ν x ^ c x p)⁻¹ := e1
    _ ≤ ∏ x, ∏ p, (μ p ^ c x p)⁻¹ :=
        Finset.prod_le_prod₀ (fun x _ => Finset.prod_nonneg fun p _ => by
            have := hν x; positivity)
          fun x _ => Finset.prod_le_prod₀ (fun p _ => by have := hν x; positivity)
            fun p _ => e2 x p
    _ = ∏ p, (μ p ^ ∑ x, c x p)⁻¹ := by
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ p, (μ p ^ R)⁻¹ :=
        Finset.prod_le_prod₀ (fun p _ => by have := hμ p; positivity)
          fun p _ => inv_anti₀ (pow_pos (lt_of_lt_of_le one_pos (hμ p)) _)
            (pow_le_pow_right₀ (hμ p) (h3 p))

/-! ### Merging parallel lines -/

/-- The exponents of merged lines. -/
def mergeE {m' : ℕ} (cls : Fin m → Fin m') (e : Fin m → ℕ) (c : Fin m') : ℕ :=
  (((List.finRange m).filter fun x => cls x = c).map e).sum

theorem mergeE_eq {m' : ℕ} (cls : Fin m → Fin m') (e : Fin m → ℕ) (c : Fin m') :
    mergeE cls e c = ∑ x ∈ Finset.univ.filter (fun x => cls x = c), e x := by
  rw [mergeE, Finset.sum_filter, Fin.sum_univ_def, List.sum_map_ite]
  simp

theorem linF_neg (r : Fin 3 → ℤ) (ℓ : Fin 3 → E) : linF (-r) ℓ = -linF r ℓ := by
  simp [linF, Finset.sum_neg_distrib]

/-- **Lines whose rows agree up to sign merge**, their exponents added. -/
theorem majF_merge {m' : ℕ} (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ)
    (a' : Fin m' → Fin 3 → ℤ) (cls : Fin m → Fin m')
    (hs : ∀ x, a x = a' (cls x) ∨ a x = -a' (cls x)) (ℓ : Fin 3 → E) :
    majF a e ℓ = majF a' (mergeE cls e) ℓ := by
  classical
  have h1 : ∀ x, nu (linF (a x) ℓ) = nu (linF (a' (cls x)) ℓ) := fun x => by
    rcases hs x with h | h <;> rw [h]
    simp [nu, linF_neg]
  unfold majF
  simp only [h1, mergeE_eq]
  rw [← Finset.prod_fiberwise (s := Finset.univ) (g := cls)
    (f := fun x => (nu (linF (a' (cls x)) ℓ) ^ e x)⁻¹)]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

/-! ### Integrability -/

/-- The matrix of the rows of a triple. -/
def triMat (a : Fin m → Fin 3 → ℤ) (t : Tri m) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun p s => a (triRow t p) s

theorem det_triMat (a : Fin m → Fin 3 → ℤ) (t : Tri m) : (triMat a t).det = triDet a t := by
  rw [Matrix.det_fin_three]
  simp only [triMat, Matrix.of_apply, triDet, det3, triRow]
  simp
  ring

theorem matrixAct_triMat (a : Fin m → Fin 3 → ℤ) (t : Tri m) (ℓ : Fin 3 → E) (p : Fin 3) :
    QED.TwoLoop.JointIntegralInvariance.matrixAct E (triMat a t) ℓ p = linF (a (triRow t p)) ℓ := by
  simp only [QED.TwoLoop.JointIntegralInvariance.matrixAct_apply, triMat, Matrix.of_apply, linF]
  exact Finset.sum_congr rfl fun s _ => (Int.cast_smul_eq_zsmul ℝ _ _).symm

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure]

/-- A unimodular basis gives an integrable product. -/
theorem integrable_basis (a : Fin m → Fin 3 → ℤ) (t : Tri m) (hdet : |triDet a t| = 1)
    (hE : ∀ M : Matrix (Fin 3) (Fin 3) ℤ, |M.det| = 1 →
      |LinearMap.det (QED.TwoLoop.JointIntegralInvariance.matrixAct E M)| = 1)
    {g : E → ℝ} (hg : Integrable g) :
    Integrable (fun ℓ : Fin 3 → E => ∏ p, g (linF (a (triRow t p)) ℓ)) := by
  have hM : |(triMat a t).det| = 1 := by rw [det_triMat, hdet]
  obtain ⟨hmp, hemb⟩ := QED.TwoLoop.NestedVP.measurePreserving_linear_add volume
    (QED.TwoLoop.JointIntegralInvariance.matrixAct E (triMat a t)) (hE _ hM) 0
  have hP : Integrable (fun ℓ' : Fin 3 → E => ∏ p, g (ℓ' p)) :=
    Integrable.fintype_prod (f := fun _ => g) fun _ => hg
  have := (hmp.integrable_comp_emb hemb).mpr hP
  refine this.congr (Filter.Eventually.of_forall fun ℓ => ?_)
  simp only [Function.comp_apply, add_zero, matrixAct_triMat]

/-- **Integrability of the majorant** under the basis criterion. -/
theorem integrable_majF (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) (R : ℕ)
    (hc : BasisCrit a e R)
    (hE : ∀ M : Matrix (Fin 3) (Fin 3) ℤ, |M.det| = 1 →
      |LinearMap.det (QED.TwoLoop.JointIntegralInvariance.matrixAct E M)| = 1)
    (hg : Integrable fun y : E => (nu y ^ R)⁻¹) : Integrable (majF (E := E) a e) := by
  classical
  set Bs := (Finset.univ : Finset (Tri m)).filter fun t => Sorted3 t ∧ triDet a t ≠ 0
  have hI : Integrable fun ℓ : Fin 3 → E =>
      ∑ t ∈ Bs, ∏ p, (nu (linF (a (triRow t p)) ℓ) ^ R)⁻¹ :=
    integrable_finsetSum _ fun t ht =>
      integrable_basis a t
        (hc.2 t (Finset.mem_filter.mp ht).2.1 (Finset.mem_filter.mp ht).2.2).1 hE hg
  refine hI.mono' (continuous_majF a e).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ℓ => ?_)
  obtain ⟨t, hs, ht, hmin⟩ := exists_min_basis a hc.1 ℓ
  obtain ⟨c, hcg⟩ := (hc.2 t hs ht).2
  have h0 : 0 ≤ majF a e ℓ := Finset.prod_nonneg fun x _ => by
    have := nu_pos (linF (a x) ℓ); positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  refine (majF_le a e R t c hcg ℓ hmin).trans ?_
  exact Finset.single_le_sum (f := fun t => ∏ p, (nu (linF (a (triRow t p)) ℓ) ^ R)⁻¹)
    (fun t _ => Finset.prod_nonneg fun p _ => by
      have := nu_pos (linF (a (triRow t p)) ℓ); positivity)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, ht⟩)

/-- The majorant on the energies, `R = 2`. -/
theorem integrable_majF_real (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ) {R : ℕ}
    (hc : BasisCrit a e R) (hR : 2 ≤ R) : Integrable (majF (E := ℝ) a e) := by
  refine integrable_majF a e 2 (hc.mono hR) (fun M hM => ?_) ?_
  · rw [QED.TwoLoop.JointIntegralInvariance.det_matrixAct_real]
    exact_mod_cast hM
  · refine (QED.ChainProof.RepsIntBB.integrable_inv_one_add_abs_pow le_rfl).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp [nu, Real.norm_eq_abs]

/-- The majorant on `(ℝ⁴)³`, `R = 5`. -/
theorem integrable_majF_four (a : Fin m → Fin 3 → ℤ) (e : Fin m → ℕ)
    (hc : BasisCrit a e 5) : Integrable (majF (E := Fin 4 → ℝ) a e) := by
  refine integrable_majF a e 5 hc (fun M hM => ?_) ?_
  · rw [QED.TwoLoop.JointIntegralInvariance.det_matrixAct_pi, abs_pow]
    have : |((M.det : ℤ) : ℝ)| = 1 := by exact_mod_cast hM
    rw [this, one_pow]
  · exact QED.ChainProof.RepsIntBB.integrable_jb le_rfl

end QED.ChainProof.SetALinkV

end
