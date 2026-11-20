/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LightPiece
public import QED.GradedProof.RPi4Pos

/-!
# (R-Π₄) step L7: the pieces of a vacuum-polarization class at a light photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7 (light photon
pair). A piece of a class `VA`, `VB`, `VC` over a shape whose last two lines are the photon
lines, with the photon factor `b² - a²` in its numerator, is `O(b)` for light comparable photon
pairs `0 < a ≤ b ≤ min(2a, 1)`, uniformly along a segment of momenta below threshold.

* `LightBdd k₀ w G`: `‖G a b (k(u))‖ ≤ C b` for such pairs and `|u| ≤ 1/2`; closed under sums
  and constants.
* `symanzikV_sub_mass`: `V` is affine in the squared masses; `pvOf_const_mul`.
* `castLoopMatrix_rows`, `chainZ_rows`, `sum_fermion_simplexPoint`: the chain sums of a
  vacuum-polarization shape are `y` (fermion lines) and `1 - y` (photon lines).
* `lightBdd_vpPiece`: the hypotheses of `QED.GradedProof.RPi4.exists_norm_pvOf_light_le` from
  the criterion, the refined bound, the chain bound `U ≥ (1 - y) y`
  (`QED.GradedProof.RPi4.symanzikU_ge_chain`) and the positivity
  `QED.GradedProof.RPi4.symanzikV_vp_ge_fermion` at zero photon masses, plus `z a² + z' b²` for
  the photon lines.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)

/-! ### Bounded by the heavier photon mass at light comparable pairs -/

/-- `G a b` is at most `C b` along the segment `lineK k₀ w`, `|u| ≤ 1/2`, for all light
comparable photon pairs `0 < a ≤ b ≤ min(2a, 1)`. -/
def LightBdd (k₀ w : Fin 4 → ℝ) (G : ℝ → ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 →
    ‖G a b (lineK k₀ w u)‖ ≤ C * b

namespace LightBdd

variable {k₀ w : Fin 4 → ℝ} {G H : ℝ → ℝ → (Fin 4 → ℝ) → ℂ}

theorem add (hG : LightBdd k₀ w G) (hH : LightBdd k₀ w H) :
    LightBdd k₀ w fun a b k => G a b k + H a b k := by
  obtain ⟨C, hC⟩ := hG
  obtain ⟨D, hD⟩ := hH
  refine ⟨C + D, fun u hu a b ha hab hb2 hb1 => ?_⟩
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add (hC u hu a b ha hab hb2 hb1) (hD u hu a b ha hab hb2 hb1)

theorem const_mul (hG : LightBdd k₀ w G) (r : ℂ) : LightBdd k₀ w fun a b k => r * G a b k := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨‖r‖ * C, fun u hu a b ha hab hb2 hb1 => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u hu a b ha hab hb2 hb1) (norm_nonneg _)

theorem zero : LightBdd k₀ w fun _ _ _ => 0 :=
  ⟨0, fun u _ a b _ _ _ _ => by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, LightBdd k₀ w (G i)) : LightBdd k₀ w fun a b k => ∑ i ∈ s, G i a b k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : LightBdd k₀ w fun _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : LightBdd k₀ w G)
    (e : ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ a b : ℝ, 0 < a → a ≤ b →
      G a b (lineK k₀ w u) = H a b (lineK k₀ w u)) : LightBdd k₀ w H := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun u hu a b ha hab hb2 hb1 => e u hu a b ha hab ▸ hC u hu a b ha hab hb2 hb1⟩

end LightBdd

/-! ### Auxiliary identities -/

/-- `V` is affine in the squared masses: `V(M) - V(M') = ∑ᵢ zᵢ (Mᵢ² - M'ᵢ²)`. -/
theorem symanzikV_sub_mass {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M M' z : Fin (m + 1) → ℝ) :
    symanzikV α p M z - symanzikV α p M' z = ∑ i, z i * (M i ^ 2 - M' i ^ 2) := by
  simp only [symanzikV]
  rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `pvOf` is homogeneous in the numerator. -/
theorem pvOf_const_mul {m : ℕ} {Q : LoopQuartic} {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hQ : Q.eval = F) (r : ℂ) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) :
    pvOf (fun ℓ => r * F ℓ) α p M = r * pvOf F α p M := by
  have hQ' : (qsum Finset.univ (fun _ : Unit => r) fun _ => Q).eval = fun ℓ => r * F ℓ := by
    funext ℓ
    rw [eval_qsum, ← hQ]
    simp
  rw [pvOf_eq hQ', pvOf_eq hQ]
  simp only [paramIntegrand_qsum, Finset.univ_unique, Finset.sum_singleton]
  rw [integral_const_mul]
  ring

/-- The loop rows of a vacuum-polarization shape: fermion rows `(1, 0)` or `(0, 1)`, photon row
`(1, -1)`. -/
theorem castLoopMatrix_rows {n : ℕ} (base : Fin 5 → Fin 2 → ℤ)
    (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
    (hrow4 : base 4 = ![1, -1]) (sh : Fin (n + 1) → Fin 5) (i : Fin (n + 1)) :
    (sh i ≠ 4 → castLoopMatrix (fun l => base (sh l)) i = ![1, 0] ∨
        castLoopMatrix (fun l => base (sh l)) i = ![0, 1]) ∧
      (sh i = 4 → castLoopMatrix (fun l => base (sh l)) i = ![1, -1]) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases hrow _ h with h' | h'
    · left; funext s; fin_cases s <;> simp [castLoopMatrix, h']
    · right; funext s; fin_cases s <;> simp [castLoopMatrix, h']
  · funext s; fin_cases s <;> simp [castLoopMatrix, h, hrow4]

theorem chainZ_rows {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (z : Fin (n + 1) → ℝ)
    (sh : Fin (n + 1) → Fin 5)
    (hα : ∀ i, (sh i ≠ 4 → α i = ![1, 0] ∨ α i = ![0, 1]) ∧ (sh i = 4 → α i = ![1, -1])) :
    chainZ α z ![1, 0] + chainZ α z ![0, 1] = ∑ i, (if sh i = 4 then 0 else z i) ∧
      chainZ α z ![1, -1] = ∑ i, (if sh i = 4 then z i else 0) := by
  have h10 : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := fun h => by
    have := congrFun h 0; simp at this
  have h1m : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 1; simp at this
  have h0m : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 0; simp at this
  refine ⟨?_, ?_⟩
  · simp only [chainZ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h4 : sh i = 4
    · have := (hα i).2 h4
      simp [this, h4, h1m.symm, h0m.symm]
    · rcases (hα i).1 h4 with h | h <;> simp [h, h4, h10, h10.symm]
  · simp only [chainZ]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h4 : sh i = 4
    · simp [(hα i).2 h4, h4]
    · rcases (hα i).1 h4 with h | h <;> simp [h, h4, h1m, h0m]

/-- The fermion parameters of a shape whose photon lines are the last two are the first `n - 1`
simplex coordinates. -/
theorem sum_fermion_simplexPoint {n : ℕ} (sh : Fin (n + 1) → Fin 5)
    (hsh : ∀ l : Fin (n + 1), sh l = 4 ↔ n - 1 ≤ (l : ℕ)) (x : Fin n → ℝ) :
    ∑ i, (if sh i = 4 then 0 else simplexPoint x i) = headSum (n - 1) x := by
  rw [Fin.sum_univ_castSucc, simplexPoint_eq_snoc]
  have hl : sh (Fin.last n) = 4 := (hsh _).mpr (by simp)
  simp only [hl, ite_true, add_zero, headSum, Fin.snoc_castSucc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hsh j.castSucc
  simp only [Fin.val_castSucc] at this
  by_cases hj : (j : ℕ) < n - 1
  · have : sh j.castSucc ≠ 4 := fun h => by have := this.mp h; omega
    simp [this, hj]
  · have : sh j.castSucc = 4 := this.mpr (by omega)
    simp [this, hj]

/-! ### A piece of a vacuum-polarization class at a light pair -/

/-- **A piece of a vacuum-polarization class at a light comparable photon pair is `O(b)`** along
a segment of momenta below threshold: the numerator carries the photon factor `b² - a²`, the
photon lines (the last two) the masses `a`, `b`. -/
theorem lightBdd_vpPiece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
    (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
      |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
    (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
    (hrow4 : base 4 = ![1, -1]) {n : ℕ} (hn : n = 6 ∨ n = 7) (sh : Fin (n + 1) → Fin 5)
    (hsh : ∀ l : Fin (n + 1), sh l = 4 ↔ n - 1 ≤ (l : ℕ)) (Ms : ℝ → ℝ → Fin (n + 1) → ℝ)
    (hMs : ∀ a b l, Ms a b l ^ 2 = Ms 0 0 l ^ 2 + (if (l : ℕ) = n - 1 then a ^ 2 else 0) +
      (if (l : ℕ) = n then b ^ 2 else 0))
    {E : Finset (Fin (n + 1))} (hcrit : IntNoSubdivergenceRefined 2 E fun i => base (sh i))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (n - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun i => base (sh i)) E 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hf : ∀ l, sh l ≠ 4 → m₀ ≤ Ms 0 0 l)
    {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(2 * m₀) ^ 2 < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u)) :
    LightBdd k₀ w fun a b k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
      (castLoopMatrix fun l => base (sh l)) (fun l => c (sh l) • k) (Ms a b) := by
  set α := castLoopMatrix fun l => base (sh l) with hα_def
  have hn6 : 6 ≤ n := by omega
  have hcrit' : NoSubdivergenceRefined 2 E α :=
    (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by
      have := hcrit'.noSubdivergenceOfOrder i; omega
  have hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ (7 ≤ n ∨ Q.quart = 0) ∧
      ∀ q, IntegrableOn (coeffOne Q α q) (simplexSet n) ∧
        IntegrableOn (coeffTwo Q α q) (simplexSet n) ∧
        IntegrableOn (coeffThree Q α) (simplexSet n) := fun k => by
    obtain ⟨Q, hq, hb, he⟩ := good_of_poly hn (hpoly k) (hB k)
    refine ⟨Q, he, hq, fun q => ?_⟩
    rcases hq with h7 | hq0
    · exact integrableOn_coeff Q α q h7 hcrit' hb
    · exact integrableOn_coeff_cubic Q α q hq0 hn6 hcrit' hb
  have hrows := castLoopMatrix_rows base hrow hrow4 sh
  have hrows3 : ∀ i, α i = ![1, 0] ∨ α i = ![0, 1] ∨ α i = ![1, -1] := fun i => by
    by_cases h4 : sh i = 4
    · exact Or.inr (Or.inr ((hrows i).2 h4))
    · rcases (hrows i).1 h4 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  -- the parameter sums of the fermion and photon lines
  have hsums : ∀ x ∈ simplexSet n,
      ∑ i, (if sh i = 4 then 0 else simplexPoint x i) = headSum (n - 1) x ∧
        ∑ i, (if sh i = 4 then simplexPoint x i else 0) = 1 - headSum (n - 1) x := by
    intro x hx
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
    have h1 := sum_fermion_simplexPoint sh hsh x
    refine ⟨h1, ?_⟩
    have h2 : ∑ i, simplexPoint x i = ∑ i, (if sh i = 4 then 0 else simplexPoint x i) +
        ∑ i, (if sh i = 4 then simplexPoint x i else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
    rw [hz.2, h1] at h2
    linarith
  have hU : ∀ x ∈ simplexSet n,
      (1 - headSum (n - 1) x) * headSum (n - 1) x ≤ symanzikU α (simplexPoint x) := by
    intro x hx
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
    obtain ⟨e1, e2⟩ := chainZ_rows α (simplexPoint x) sh hrows
    have h := symanzikU_ge_chain α hz.1 hrows3
    rw [e1, e2, (hsums x hx).1, (hsums x hx).2] at h
    exact h
  set c₀ := min 1 (1 + S₀ / (2 * m₀) ^ 2) * m₀ ^ 2
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  have hc₀ : 0 < c₀ := by
    refine mul_pos (lt_min one_pos ?_) (by positivity)
    have : -1 < S₀ / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  have hV : ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ simplexSet n,
      symanzikU α (simplexPoint x) ≠ 0 →
      c₀ * headSum (n - 1) x + (1 - headSum (n - 1) x) * a ^ 2 ≤
        symanzikV α (fun i => c (sh i) • lineK k₀ w u) (Ms a b) (simplexPoint x) := by
    intro u hu a b ha hab x hx hU0
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
    set k := lineK k₀ w u
    have hs := hseg u hu
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow sh (Ms 0 0) hm₀ hf
      (k := k) (by linarith) hz.1 hU0
    have hZ : ∑ i ∈ Finset.univ.filter (fun i => sh i ≠ 4), simplexPoint x i =
        headSum (n - 1) x := by
      rw [← (hsums x hx).1, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by by_cases h4 : sh i = 4 <;> simp [h4]
    rw [hZ] at hP0
    have hy0 : 0 ≤ headSum (n - 1) x := by
      rw [← (hsums x hx).1]
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hz.1 i]
    have hmin : c₀ ≤ min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2 := by
      refine mul_le_mul_of_nonneg_right (min_le_min le_rfl ?_) (by positivity)
      have := div_le_div_of_nonneg_right hs hT.le
      linarith
    have hdiff := symanzikV_sub_mass α (fun i => c (sh i) • k) (Ms a b) (Ms 0 0) (simplexPoint x)
    have hph : (1 - headSum (n - 1) x) * a ^ 2 ≤
        ∑ i, simplexPoint x i * (Ms a b i ^ 2 - Ms 0 0 i ^ 2) := by
      rw [← (hsums x hx).2, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hMs a b i]
      have hzi := hz.1 i
      by_cases h4 : sh i = 4
      · have hi := (hsh i).mp h4
        have hin : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
        simp only [h4, ite_true]
        rcases Nat.eq_or_lt_of_le hi with h | h
        · have h1 : (i : ℕ) = n - 1 := h.symm
          have h2 : ¬ (i : ℕ) = n := by omega
          rw [ite_eq_left h1, ite_eq_right h2]
          nlinarith
        · have h1 : ¬ (i : ℕ) = n - 1 := by omega
          have h2 : (i : ℕ) = n := by omega
          rw [ite_eq_right h1, ite_eq_left h2]
          nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab 2) hzi]
      · simp only [h4, ite_false, zero_mul]
        have h1 : 0 ≤ (if (i : ℕ) = n - 1 then a ^ 2 else 0) := by split_ifs <;> positivity
        have h2 : 0 ≤ (if (i : ℕ) = n then b ^ 2 else 0) := by split_ifs <;> positivity
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hmin hy0]
  obtain ⟨C₁, C₂, hC⟩ := exists_norm_pvOf_light_le hn α hspan (fun l => c (sh l)) Ms k₀ w N hk
    hQ hU hc₀ hV
  refine ⟨|C₁| + |C₂|, fun u hu a b ha hab hb2 hb1 => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨Q, hQe, -, -⟩ := hQ (lineK k₀ w u)
  dsimp only
  rw [pvOf_const_mul hQe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by nlinarith)]
  have h := hC u hu a b ha hab hb2
  have hpv := norm_nonneg (pvOf (N (lineK k₀ w u)) α (fun i => c (sh i) • lineK k₀ w u) (Ms a b))
  have hC' : C₁ + C₂ / b ≤ (|C₁| + |C₂|) / b := by
    rw [add_div]
    have h1 : C₁ ≤ |C₁| / b := (le_abs_self C₁).trans (le_div_self (abs_nonneg _) hb hb1)
    have h2 : C₂ / b ≤ |C₂| / b := div_le_div_of_nonneg_right (le_abs_self C₂) hb.le
    linarith
  calc (b ^ 2 - a ^ 2) * ‖pvOf (N (lineK k₀ w u)) α (fun i => c (sh i) • lineK k₀ w u) (Ms a b)‖
      ≤ b ^ 2 * ((|C₁| + |C₂|) / b) :=
        mul_le_mul (by nlinarith) (h.trans hC') hpv (sq_nonneg b)
    _ = (|C₁| + |C₂|) * b := by field_simp

end QED.GradedProof.RPi4

end
