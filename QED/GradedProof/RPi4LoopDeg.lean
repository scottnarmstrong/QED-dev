/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LightBd
public import QED.TwoLoop.ClassIntegrableLoopPoly

/-!
# (R-Π₄) step L6d1: numerators of bounded degree along one loop

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. On a face of a
logarithmic subgraph only one entry `(A⁻¹)ₛₛ` of the inverse Symanzik matrix is large. The
contractions of the parametric integrand see that entry only through the coefficients of the
numerator with two (or four) indices in loop `s`, so a numerator of degree at most one along
loop `s` (a self-energy face) does not see it at all, and one of degree at most two (a vertex
face) sees it at most once in the quartic contraction:

* `IsLoopPolyDeg s d n F`: `F` is a polynomial of total degree `≤ n` and of degree `≤ d` in the
  components of `ℓₛ`, with the closure lemmas `const`, `coord`, `add`, `sub`, `mul`,
  `const_mul`, `sum`, `prod`;
* `LoopDegLe s d Q`: the coefficients of `Q` with more than `d` indices in loop `s` vanish;
  `exists_loopQuartic_deg` converts the first into the second;
* `hess_eq_zero_of_loopDeg`, `norm_contractTwo_le_deg`, `norm_contractFour_le_deg_one`,
  `norm_contractFour_le_deg_two`: the sharp contraction bounds, with a bound `g₀` of the entries
  of `A⁻¹` other than `(s, s)`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.Bridge

/-! ### Polynomials of bounded degree along one loop -/

/-- `F` is a polynomial of total degree at most `n` in the loop momenta and of degree at most `d`
in the four components of `ℓₛ`. -/
def IsLoopPolyDeg (s : Fin 2) (d n : ℕ) (F : (Fin 2 → Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ Q : MvPolynomial (Fin 2 × Fin 4) ℂ, Q.totalDegree ≤ n ∧
    (∀ x ∈ Q.support, ∑ μ, x (s, μ) ≤ d) ∧
    ∀ ℓ, F ℓ = MvPolynomial.eval (fun x => ((ℓ x.1 x.2 : ℝ) : ℂ)) Q

namespace IsLoopPolyDeg

variable {s : Fin 2} {d d' n n' : ℕ} {F G : (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem isLoopPoly (h : IsLoopPolyDeg s d n F) : IsLoopPoly 2 n F := by
  obtain ⟨Q, hQ, -, hF⟩ := h
  exact ⟨Q, hQ, hF⟩

theorem mono (h : IsLoopPolyDeg s d n F) (hd : d ≤ d') (hn : n ≤ n') :
    IsLoopPolyDeg s d' n' F := by
  obtain ⟨Q, hQ, hs, hF⟩ := h
  exact ⟨Q, hQ.trans hn, fun x hx => (hs x hx).trans hd, hF⟩

theorem const (c : ℂ) : IsLoopPolyDeg s d n fun _ => c := by
  classical
  refine ⟨MvPolynomial.C c, by rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _,
    fun x hx => ?_, fun _ => by simp⟩
  have hx0 : x = 0 := by
    by_contra h
    exact h (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hx))
  simp [hx0]

/-- A component of a loop momentum other than `ℓₛ`. -/
theorem coord_ne {r : Fin 2} (hr : r ≠ s) (ν : Fin 4) (hn : 1 ≤ n) :
    IsLoopPolyDeg s d n fun ℓ => ((ℓ r ν : ℝ) : ℂ) := by
  classical
  refine ⟨MvPolynomial.X (r, ν), by rw [MvPolynomial.totalDegree_X]; exact hn,
    fun x hx => ?_, fun _ => by simp⟩
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hx
  subst hx
  have : ∀ μ, (Finsupp.single (r, ν) 1 : Fin 2 × Fin 4 →₀ ℕ) (s, μ) = 0 := fun μ =>
    Finsupp.single_eq_of_ne (by simp [Ne.symm hr])
  simp [this]

/-- A component of `ℓₛ`. -/
theorem coord (r : Fin 2) (ν : Fin 4) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    IsLoopPolyDeg s d n fun ℓ => ((ℓ r ν : ℝ) : ℂ) := by
  classical
  refine ⟨MvPolynomial.X (r, ν), by rw [MvPolynomial.totalDegree_X]; exact hn,
    fun x hx => ?_, fun _ => by simp⟩
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hx
  subst hx
  calc ∑ μ, (Finsupp.single (r, ν) 1 : Fin 2 × Fin 4 →₀ ℕ) (s, μ)
      ≤ ∑ μ, if μ = ν then 1 else 0 := Finset.sum_le_sum fun μ _ => by
        rw [Finsupp.single_apply]
        split_ifs with h1 h2 <;> simp_all
    _ = 1 := by simp
    _ ≤ d := hd

theorem add (hF : IsLoopPolyDeg s d n F) (hG : IsLoopPolyDeg s d n G) :
    IsLoopPolyDeg s d n fun ℓ => F ℓ + G ℓ := by
  classical
  obtain ⟨Q, hQ, hsQ, hF⟩ := hF
  obtain ⟨R, hR, hsR, hG⟩ := hG
  refine ⟨Q + R, (MvPolynomial.totalDegree_add Q R).trans (max_le hQ hR), fun x hx => ?_,
    fun ℓ => by simp [hF, hG]⟩
  rcases Finset.mem_union.mp (MvPolynomial.support_add hx) with h | h
  exacts [hsQ x h, hsR x h]

theorem const_mul (c : ℂ) (hF : IsLoopPolyDeg s d n F) :
    IsLoopPolyDeg s d n fun ℓ => c * F ℓ := by
  classical
  obtain ⟨Q, hQ, hsQ, hF⟩ := hF
  refine ⟨MvPolynomial.C c * Q, ?_, fun x hx => ?_, fun ℓ => by simp [hF]⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hQ
  · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hx)
    have ha0 : a = 0 := by
      by_contra h
      exact h (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha))
    simpa [ha0] using hsQ b hb

theorem sub (hF : IsLoopPolyDeg s d n F) (hG : IsLoopPolyDeg s d n G) :
    IsLoopPolyDeg s d n fun ℓ => F ℓ - G ℓ := by
  simpa [sub_eq_add_neg] using hF.add (hG.const_mul (-1))

theorem mul (hF : IsLoopPolyDeg s d n F) (hG : IsLoopPolyDeg s d' n' G) :
    IsLoopPolyDeg s (d + d') (n + n') fun ℓ => F ℓ * G ℓ := by
  classical
  obtain ⟨Q, hQ, hsQ, hF⟩ := hF
  obtain ⟨R, hR, hsR, hG⟩ := hG
  refine ⟨Q * R, (MvPolynomial.totalDegree_mul Q R).trans (Nat.add_le_add hQ hR),
    fun x hx => ?_, fun ℓ => by simp [hF, hG]⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hx)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  exact Nat.add_le_add (hsQ a ha) (hsR b hb)

theorem sum {ι : Type*} (t : Finset ι) {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, IsLoopPolyDeg s d n (F i)) : IsLoopPolyDeg s d n fun ℓ => ∑ i ∈ t, F i ℓ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using const (s := s) (d := d) (n := n) 0
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod {ι : Type*} (t : Finset ι) {F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ} (dd nn : ι → ℕ)
    (h : ∀ i ∈ t, IsLoopPolyDeg s (dd i) (nn i) (F i)) :
    IsLoopPolyDeg s (∑ i ∈ t, dd i) (∑ i ∈ t, nn i) fun ℓ => ∏ i ∈ t, F i ℓ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using const (s := s) (d := 0) (n := 0) 1
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end IsLoopPolyDeg

/-! ### Coefficient arrays of bounded degree along one loop -/

/-- `1` if the index `a` belongs to loop `s`, else `0`. -/
def loopInd (s : Fin 2) (a : LoopIndex) : ℕ := if a.1 = s then 1 else 0

theorem loopInd_le_one (s : Fin 2) (a : LoopIndex) : loopInd s a ≤ 1 := by
  unfold loopInd; split_ifs <;> simp

theorem loopInd_of_eq {s : Fin 2} {a : LoopIndex} (h : a.1 = s) : loopInd s a = 1 := by
  simp [loopInd, h]

/-- The coefficients of `Q` with more than `d` indices in loop `s` vanish. -/
structure LoopDegLe (s : Fin 2) (d : ℕ) (Q : LoopQuartic) : Prop where
  lin : ∀ a, d < loopInd s a → Q.lin a = 0
  quad : ∀ a b, d < loopInd s a + loopInd s b → Q.quad a b = 0
  cub : ∀ a b c, d < loopInd s a + loopInd s b + loopInd s c → Q.cub a b c = 0
  quart : ∀ a b c e, d < loopInd s a + loopInd s b + loopInd s c + loopInd s e →
    Q.quart a b c e = 0

namespace LoopDegLe

variable {s : Fin 2} {d : ℕ}

theorem add {P Q : LoopQuartic} (hP : LoopDegLe s d P) (hQ : LoopDegLe s d Q) :
    LoopDegLe s d (P.add Q) where
  lin a h := by simp [LoopQuartic.add, hP.lin a h, hQ.lin a h]
  quad a b h := by simp [LoopQuartic.add, hP.quad a b h, hQ.quad a b h]
  cub a b c h := by simp [LoopQuartic.add, hP.cub a b c h, hQ.cub a b c h]
  quart a b c e h := by simp [LoopQuartic.add, hP.quart a b c e h, hQ.quart a b c e h]

theorem smul (c : ℂ) {P : LoopQuartic} (hP : LoopDegLe s d P) :
    LoopDegLe s d (LoopQuartic.smul c P) where
  lin a h := by simp [LoopQuartic.smul, hP.lin a h]
  quad a b h := by simp [LoopQuartic.smul, hP.quad a b h]
  cub a b c h := by simp [LoopQuartic.smul, hP.cub a b c h]
  quart a b c e h := by simp [LoopQuartic.smul, hP.quart a b c e h]

theorem zero : LoopDegLe s d LoopQuartic.zero where
  lin _ _ := rfl
  quad _ _ _ := rfl
  cub _ _ _ _ := rfl
  quart _ _ _ _ _ := rfl

theorem ofList (l : List LoopIndex) (hl : (l.map (loopInd s)).sum ≤ d) :
    LoopDegLe s d (LoopQuartic.ofList l) := by
  match l, hl with
  | [], _ => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | [a], h =>
    refine ⟨fun x hx => ?_, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    simp only [LoopQuartic.ofList, ite_eq_right_iff, one_ne_zero, imp_false]
    rintro rfl; omega
  | [a, b], h =>
    refine ⟨fun _ _ => rfl, fun x y hx => ?_, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    simp only [LoopQuartic.ofList]
    split_ifs with h1 h2 <;> first | rfl | (subst h1 h2; omega)
  | [a, b, c], h =>
    refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun x y z hx => ?_, fun _ _ _ _ _ => rfl⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    simp only [LoopQuartic.ofList]
    split_ifs with h1 h2 h3 <;> first | rfl | (subst h1 h2 h3; omega)
  | [a, b, c, e], h =>
    refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun x y z w hx => ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    simp only [LoopQuartic.ofList]
    split_ifs with h1 h2 h3 h4 <;> first | rfl | (subst h1 h2 h3 h4; omega)
  | _ :: _ :: _ :: _ :: _ :: _, _ => exact zero

end LoopDegLe

/-- The number of indices in loop `s` of the list of variables of a monomial. -/
theorem sum_map_loopInd_toList (s : Fin 2) (x : LoopIndex →₀ ℕ) :
    (x.toMultiset.toList.map (loopInd s)).sum = ∑ μ, x (s, μ) := by
  classical
  rw [Multiset.sum_map_toList, Finset.sum_multiset_map_count, Finsupp.toFinset_toMultiset]
  simp only [Finsupp.count_toMultiset, smul_eq_mul]
  rw [Finset.sum_subset (Finset.subset_univ x.support) fun a _ ha => by
    simp [Finsupp.notMem_support_iff.mp ha]]
  rw [Fintype.sum_prod_type]
  simp only [loopInd, mul_ite, mul_one, mul_zero]
  fin_cases s <;> simp

/-- **A polynomial of total degree `≤ 4` and degree `≤ d` along loop `s` is a `LoopQuartic`
whose coefficients with more than `d` indices in loop `s` vanish.** -/
theorem exists_loopQuartic_deg {s : Fin 2} {d : ℕ} {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h : IsLoopPolyDeg s d 4 F) : ∃ P : LoopQuartic, LoopDegLe s d P ∧ P.eval = F := by
  classical
  obtain ⟨Q, hQ, hsQ, hF⟩ := h
  have key : ∀ t : Finset (LoopIndex →₀ ℕ), t ⊆ Q.support → ∃ P : LoopQuartic,
      LoopDegLe s d P ∧ ∀ X, P.evalC X = ∑ x ∈ t, Q.coeff x * ∏ i ∈ x.support, X i ^ x i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact fun _ => ⟨LoopQuartic.zero, LoopDegLe.zero, fun X => by
        simp [LoopQuartic.evalC_zero]⟩
    | insert x t hx ih =>
      intro ht
      obtain ⟨P, hPd, hP⟩ := ih ((Finset.subset_insert x t).trans ht)
      have hxQ : x ∈ Q.support := ht (Finset.mem_insert_self x t)
      have hdeg : x.toMultiset.toList.length ≤ 4 := by
        rw [Multiset.length_toList, Finsupp.card_toMultiset]
        exact (MvPolynomial.le_totalDegree hxQ).trans hQ
      refine ⟨(LoopQuartic.smul (Q.coeff x) (LoopQuartic.ofList x.toMultiset.toList)).add P,
        ((LoopDegLe.ofList _ ?_).smul _).add hPd, fun X => ?_⟩
      · rw [sum_map_loopInd_toList]
        exact hsQ x hxQ
      rw [LoopQuartic.evalC_add, LoopQuartic.evalC_smul, LoopQuartic.evalC_ofList _ hdeg,
        prod_map_toList_toMultiset, hP, Finset.sum_insert hx]
  obtain ⟨P, hPd, hP⟩ := key Q.support subset_rfl
  refine ⟨P, hPd, funext fun ℓ => ?_⟩
  rw [hF ℓ, MvPolynomial.eval_eq, LoopQuartic.eval, hP]
  rfl

/-! ### The sharp contraction bounds -/

section Contract

variable {s : Fin 2} {Q : LoopQuartic}

/-- **Degree at most one along loop `s`**: the coefficients `Hₐ_b(X)` with both indices in
loop `s` vanish. -/
theorem hess_eq_zero_of_loopDeg (hQ : LoopDegLe s 1 Q) (X : LoopIndex → ℂ) {a b : LoopIndex}
    (ha : a.1 = s) (hb : b.1 = s) : Q.hess X a b = 0 := by
  have ia := loopInd_of_eq ha
  have ib := loopInd_of_eq hb
  have h0 : ∀ c, Q.cub a b c + Q.cub a c b + Q.cub c a b = 0 := fun c => by
    rw [hQ.cub a b c (by omega), hQ.cub a c b (by omega), hQ.cub c a b (by omega)]
    ring
  have h1 : ∀ c e, Q.quartSym a b c e = 0 := fun c e => by
    simp only [LoopQuartic.quartSym]
    rw [hQ.quart a b c e (by omega), hQ.quart a c b e (by omega), hQ.quart a c e b (by omega),
      hQ.quart c a b e (by omega), hQ.quart c a e b (by omega), hQ.quart c e a b (by omega)]
    ring
  simp [LoopQuartic.hess, hQ.quad a b (by omega), h0, h1]

theorem abs_loopMetricInv_le (A : Matrix (Fin 2) (Fin 2) ℝ) {g : ℝ} (a b : LoopIndex)
    (h : |A⁻¹ a.1 b.1| ≤ g) : |loopMetricInv A a b| ≤ g := by
  simp only [loopMetricInv, abs_mul]
  have hm : |Minkowski.metric a.2 b.2| ≤ 1 := by
    unfold Minkowski.metric; split_ifs <;> simp
  calc |Minkowski.metric a.2 b.2| * |A⁻¹ a.1 b.1| ≤ 1 * g :=
        mul_le_mul hm h (abs_nonneg _) zero_le_one
    _ = g := one_mul g

/-- **The quadratic contraction at degree at most one along loop `s`**: only the entries of
`A⁻¹` other than `(s, s)` enter. -/
theorem norm_contractTwo_le_deg (hQ : LoopDegLe s 1 Q) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) {K g₀ : ℝ} (hK : 0 ≤ K) (hX : ∀ a, ‖X a‖ ≤ K) (hg₀ : 0 ≤ g₀)
    (hg : ∀ r t, (r, t) ≠ (s, s) → |A⁻¹ r t| ≤ g₀) :
    ‖Q.contractTwo A X‖ ≤ lqHess Q * (1 + (K + K ^ 2)) * g₀ := by
  have h1 : ∀ a, ‖X a‖ ≤ 1 + (K + K ^ 2) := fun a => by nlinarith [hX a]
  have h2 : ∀ a b, ‖X a * X b‖ ≤ K + K ^ 2 := fun a b => by
    rw [norm_mul]
    nlinarith [mul_le_mul (hX a) (hX b) (norm_nonneg _) hK]
  unfold LoopQuartic.contractTwo lqHess
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  have hB : 0 ≤ Q.hessBound a b * (1 + (K + K ^ 2)) * g₀ :=
    mul_nonneg (mul_nonneg (Q.hessBound_nonneg _ _) (by positivity)) hg₀
  by_cases hab : a.1 = s ∧ b.1 = s
  · rw [hess_eq_zero_of_loopDeg hQ X hab.1 hab.2, zero_mul, norm_zero]
    exact hB
  · rw [norm_mul, norm_real, Real.norm_eq_abs]
    refine mul_le_mul (Q.norm_hess_le X h1 h2 (by positivity) a b)
      (abs_loopMetricInv_le A a b (hg _ _ fun h => hab ?_)) (abs_nonneg _)
      (mul_nonneg (Q.hessBound_nonneg _ _) (by positivity))
    simp only [Prod.mk.injEq] at h
    exact h

theorem norm_contractFour_le_of_matPair (A : Matrix (Fin 2) (Fin 2) ℝ) {B : ℝ}
    (hp : ∀ a b c e, Q.quart a b c e ≠ 0 → |matPair (loopMetricInv A) a b c e| ≤ B) :
    ‖Q.contractFour A‖ ≤ lqQuart Q * B := by
  unfold LoopQuartic.contractFour lqQuart
  simp only [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  by_cases hq : Q.quart a b c e = 0
  · rw [hq, zero_mul, norm_zero]
    simp
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hp a b c e hq) (norm_nonneg _)

theorem abs_matPair_le {G : Matrix LoopIndex LoopIndex ℝ} {a b c e : LoopIndex} {B : ℝ}
    (h1 : |G a b * G c e| ≤ B) (h2 : |G a c * G b e| ≤ B) (h3 : |G a e * G b c| ≤ B) :
    |matPair G a b c e| ≤ 3 * B := by
  unfold matPair
  calc _ ≤ |G a b * G c e| + |G a c * G b e| + |G a e * G b c| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- **The quartic contraction at degree at most one along loop `s`.** -/
theorem norm_contractFour_le_deg_one (hQ : LoopDegLe s 1 Q) (A : Matrix (Fin 2) (Fin 2) ℝ)
    {g₀ : ℝ} (hg₀ : 0 ≤ g₀) (hg : ∀ r t, (r, t) ≠ (s, s) → |A⁻¹ r t| ≤ g₀) :
    ‖Q.contractFour A‖ ≤ lqQuart Q * (3 * g₀ ^ 2) := by
  -- an entry with indices not both in loop `s`
  have hG : ∀ x y : LoopIndex, ¬(x.1 = s ∧ y.1 = s) → |loopMetricInv A x y| ≤ g₀ :=
    fun x y hxy => abs_loopMetricInv_le A x y (hg _ _ fun h => hxy (by simpa using h))
  have hP : ∀ x y z w : LoopIndex, ¬(x.1 = s ∧ y.1 = s) → ¬(z.1 = s ∧ w.1 = s) →
      |loopMetricInv A x y * loopMetricInv A z w| ≤ g₀ ^ 2 := fun x y z w h h' => by
    rw [abs_mul, sq]
    exact mul_le_mul (hG x y h) (hG z w h') (abs_nonneg _) hg₀
  have hn : ∀ x y z w : LoopIndex, loopInd s x + loopInd s y + loopInd s z + loopInd s w ≤ 1 →
      ¬(x.1 = s ∧ y.1 = s) := fun x y z w h hxy => by
    have := loopInd_of_eq hxy.1
    have := loopInd_of_eq hxy.2
    omega
  refine norm_contractFour_le_of_matPair A fun a b c e hq => ?_
  have hc : loopInd s a + loopInd s b + loopInd s c + loopInd s e ≤ 1 := by
    by_contra h
    exact hq (hQ.quart a b c e (by omega))
  refine abs_matPair_le (hP _ _ _ _ (hn _ _ _ _ hc) (hn c e a b (by omega)))
    (hP _ _ _ _ (hn a c b e (by omega)) (hn b e a c (by omega)))
    (hP _ _ _ _ (hn a e b c (by omega)) (hn b c a e (by omega)))

/-- **The quartic contraction at degree at most two along loop `s`**: the large entry `(A⁻¹)ₛₛ`
enters at most once in each pairing. -/
theorem norm_contractFour_le_deg_two (hQ : LoopDegLe s 2 Q) (A : Matrix (Fin 2) (Fin 2) ℝ)
    {g₀ g : ℝ} (hg₀ : 0 ≤ g₀) (hgg : ∀ r t, |A⁻¹ r t| ≤ g)
    (hg : ∀ r t, (r, t) ≠ (s, s) → |A⁻¹ r t| ≤ g₀) :
    ‖Q.contractFour A‖ ≤ lqQuart Q * (3 * (g₀ * g)) := by
  have hg0 : 0 ≤ g := (abs_nonneg _).trans (hgg 0 0)
  have hG : ∀ x y : LoopIndex, ¬(x.1 = s ∧ y.1 = s) → |loopMetricInv A x y| ≤ g₀ :=
    fun x y hxy => abs_loopMetricInv_le A x y (hg _ _ fun h => hxy (by simpa using h))
  have hA : ∀ x y : LoopIndex, |loopMetricInv A x y| ≤ g := fun x y =>
    abs_loopMetricInv_le A x y (hgg _ _)
  have hP : ∀ x y z w : LoopIndex, (¬(x.1 = s ∧ y.1 = s) ∨ ¬(z.1 = s ∧ w.1 = s)) →
      |loopMetricInv A x y * loopMetricInv A z w| ≤ g₀ * g := fun x y z w h => by
    rw [abs_mul]
    rcases h with h | h
    · exact mul_le_mul (hG x y h) (hA z w) (abs_nonneg _) hg₀
    · rw [mul_comm g₀]
      exact mul_le_mul (hA x y) (hG z w h) (abs_nonneg _) hg0
  have hn : ∀ x y z w : LoopIndex, loopInd s x + loopInd s y + loopInd s z + loopInd s w ≤ 2 →
      (¬(x.1 = s ∧ y.1 = s) ∨ ¬(z.1 = s ∧ w.1 = s)) := fun x y z w h => by
    by_contra hc
    push Not at hc
    have := loopInd_of_eq hc.1.1
    have := loopInd_of_eq hc.1.2
    have := loopInd_of_eq hc.2.1
    have := loopInd_of_eq hc.2.2
    omega
  refine norm_contractFour_le_of_matPair A fun a b c e hq => ?_
  have hc : loopInd s a + loopInd s b + loopInd s c + loopInd s e ≤ 2 := by
    by_contra h
    exact hq (hQ.quart a b c e (by omega))
  exact abs_matPair_le (hP _ _ _ _ (hn _ _ _ _ hc)) (hP _ _ _ _ (hn a c b e (by omega)))
    (hP _ _ _ _ (hn a e b c (by omega)))

end Contract

end QED.GradedProof.RPi4

end
