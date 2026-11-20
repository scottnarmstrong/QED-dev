/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4CollapsePiece

/-!
# (R-Π₄) step L6b′: the pieces of a vacuum-polarization class as photon-mass integrals

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6b′ (heavy photon
pair). A piece over a shape whose last two lines are the photon lines (row `4`), with the photon
factor `b² - a²` in its numerator, is `∫_{a²}^{b²} pairDens(u) du`, for every photon pair
`0 < a < b` and every momentum below the threshold `(2 m₀)²`.

* `comp_eq_dbl`: a shape whose last two lines have the same row is a doubled shape.
* `pairDens_congr_mass`: the density does not depend on the mass of the photon line.
* `pvOf_vpShape_pair`: the photon collapse for a vacuum-polarization shape, from the criterion,
  the refined bound and the positivity `QED.GradedProof.RPi4.symanzikV_vp_ge_fermion` of the
  merged shape.
* `PairInt m₀ G D`: `G a b k = ∫_{a²}^{b²} D u k du` with `D` interval integrable; closed under
  sums and constants.
* `pairInt_pieceA`, `pairInt_pieceB`: the pieces with eight and seven lines.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.GradedProof.WI2 (dbl)
open QED.TwoLoop.Bridge (IsLoopPoly)

/-- A shape whose last two lines have the same row is the doubled shape of its first `m + 1`
lines. -/
theorem comp_eq_dbl {β : Type*} {m : ℕ} (sh : Fin (m + 2) → Fin 5)
    (h : sh (Fin.last (m + 1)) = sh (Fin.last m).castSucc) (g : Fin 5 → β) :
    (fun l => g (sh l)) = dbl (Fin.last m) fun l => g (sh l.castSucc) := by
  funext l
  induction l using Fin.lastCases with
  | last => simp [dbl, h]
  | cast l => simp [dbl]

theorem pairDens_congr_mass {m : ℕ} (F : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) {M M' : Fin (m + 1) → ℝ}
    (i : Fin (m + 1)) (h : ∀ j, j ≠ i → M j = M' j) (u : ℝ) :
    pairDens F α p M i u = pairDens F α p M' i u := by
  have e : Function.update M i 0 = Function.update M' i 0 := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [Function.update_of_ne hj, h j hj]
  simp only [pairDens, e]

section Shape

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **The photon collapse for a vacuum-polarization shape.** The last two of the `m + 2` lines
are the photon lines (masses `a = Mₘ`, `b`); the merged shape is the first `m + 1` lines. -/
theorem pvOf_vpShape_pair {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 (m + 1 - 3) F)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (M : Fin (m + 1) → ℝ) (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ M l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {a b : ℝ}
    (hMa : M (Fin.last m) = a) (ha : 0 < a) (hab : a < b) :
    IntervalIntegrable (pairDens F (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
        (fun l => c (sh l.castSucc) • k) M (Fin.last m)) volume (a ^ 2) (b ^ 2) ∧
      pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * F ℓ)
        (castLoopMatrix fun l => base (sh l)) (fun l => c (sh l) • k) (Fin.snoc M b) =
      ∫ u in a ^ 2..b ^ 2, pairDens F
        (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
        (fun l => c (sh l.castSucc) • k) M (Fin.last m) u := by
  subst hMa
  set i := Fin.last m with hi_def
  have hi4 : sh i.castSucc = 4 := (hsh _).2 (by simp [i])
  have hl : sh (Fin.last (m + 1)) = sh i.castSucc := by rw [(hsh _).2 (by simp), hi4]
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set p : Fin (m + 1) → Fin 4 → ℝ := fun l => c (sh l.castSucc) • k with hp_def
  have hα : castLoopMatrix (fun l => base (sh l)) = dbl i α :=
    comp_eq_dbl sh hl fun r s => (base r s : ℝ)
  have hp : (fun l => c (sh l) • k) = dbl i p := comp_eq_dbl sh hl fun r => c r • k
  rw [hα, hp]
  rw [hα] at hB
  have hcrit' : NoSubdivergenceRefined 2 E (dbl i α) :=
    hα ▸ (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).2 hcrit
  have hrows := castLoopMatrix_rows base hrow hrow4 fun l : Fin (m + 1) => sh l.castSucc
  have hne : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 ↔ l ≠ i := fun l => by
    rw [Ne, hsh, Ne, Fin.ext_iff]
    simp only [Fin.val_castSucc, i, Fin.val_last]
    have := l.isLt
    omega
  have hspan : ∃ j l, α j 0 * α l 1 - α j 1 * α l 0 ≠ 0 := by
    have h0 : (0 : Fin (m + 1)) ≠ i := by
      rw [Ne, Fin.ext_iff]; simp only [i, Fin.val_last, Fin.val_zero]; omega
    refine ⟨0, i, ?_⟩
    rw [show α i = ![1, -1] from (hrows i).2 hi4]
    rcases (hrows 0).1 ((hne 0).2 h0) with h | h <;> rw [show α 0 = _ from h] <;> simp
  set c₀ := min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  have hc₀ : 0 < c₀ := by
    refine mul_pos (lt_min one_pos ?_) (by positivity)
    have : -1 < Minkowski.dot k k / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  refine pvOf_dbl_pair hm i α p M hcrit' hpoly hB (by nlinarith) hspan
    (lt_min hc₀ (pow_pos ha 2)) ?_
  intro z hz0 hz1 hU u hu
  have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
    (Function.update M i 0) hm₀ (fun l hl => by
      rw [Function.update_of_ne ((hne l).1 hl)]; exact hf l hl) hk hz0 hU
  have hfil : Finset.univ.filter (fun l : Fin (m + 1) => sh l.castSucc ≠ 4) =
      Finset.univ.erase i := by
    ext l; simp [hne l]
  rw [hfil, Finset.sum_erase_eq_sub (Finset.mem_univ i), hz1] at hP0
  have hzi1 : z i ≤ 1 := by
    rw [← hz1]; exact Finset.single_le_sum (fun j _ => hz0 j) (Finset.mem_univ i)
  have h1 := mul_le_mul_of_nonneg_right (min_le_left c₀ (M i ^ 2)) (sub_nonneg.2 hzi1)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right c₀ (M i ^ 2)) (hz0 i)
  have h3 := mul_le_mul_of_nonneg_left hu.1 (hz0 i)
  nlinarith

end Shape

/-! ### Photon-mass integrals -/

/-- **`G` is the photon-mass integral of `D`**: `G a b k = ∫_{a²}^{b²} D u k du`, `D` interval
integrable, for every momentum `k` with `k² > -(2m₀)²` and every photon pair `0 < a < b`. -/
def PairInt (m₀ : ℝ) (G : ℝ → ℝ → (Fin 4 → ℝ) → ℂ) (D : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∀ k : Fin 4 → ℝ, -(2 * m₀) ^ 2 < Minkowski.dot k k → ∀ a b : ℝ, 0 < a → a < b →
    IntervalIntegrable (fun u => D u k) volume (a ^ 2) (b ^ 2) ∧
      G a b k = ∫ u in a ^ 2..b ^ 2, D u k

namespace PairInt

variable {m₀ : ℝ} {G G' : ℝ → ℝ → (Fin 4 → ℝ) → ℂ} {D D' : ℝ → (Fin 4 → ℝ) → ℂ}

theorem add (h : PairInt m₀ G D) (h' : PairInt m₀ G' D') :
    PairInt m₀ (fun a b k => G a b k + G' a b k) fun u k => D u k + D' u k := by
  intro k hk a b ha hab
  obtain ⟨i1, e1⟩ := h k hk a b ha hab
  obtain ⟨i2, e2⟩ := h' k hk a b ha hab
  exact ⟨i1.add i2, by dsimp only; rw [e1, e2, intervalIntegral.integral_add i1 i2]⟩

theorem const_mul (h : PairInt m₀ G D) (r : ℂ) :
    PairInt m₀ (fun a b k => r * G a b k) fun u k => r * D u k := by
  intro k hk a b ha hab
  obtain ⟨i1, e1⟩ := h k hk a b ha hab
  exact ⟨i1.const_mul r, by dsimp only; rw [e1, intervalIntegral.integral_const_mul]⟩

theorem zero : PairInt m₀ (fun _ _ _ => 0) fun _ _ => 0 := fun _ _ _ _ _ _ =>
  ⟨intervalIntegrable_const, by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → ℝ → (Fin 4 → ℝ) → ℂ}
    {D : ι → ℝ → (Fin 4 → ℝ) → ℂ} (h : ∀ i ∈ s, PairInt m₀ (G i) (D i)) :
    PairInt m₀ (fun a b k => ∑ i ∈ s, G i a b k) fun u k => ∑ i ∈ s, D i u k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : PairInt m₀ (fun _ _ _ => 0) fun _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem congr (h : PairInt m₀ G D)
    (e : ∀ k : Fin 4 → ℝ, -(2 * m₀) ^ 2 < Minkowski.dot k k → ∀ a b : ℝ, 0 < a → a < b →
      G a b k = G' a b k) :
    PairInt m₀ G' D := fun k hk a b ha hab =>
  ⟨(h k hk a b ha hab).1, (e k hk a b ha hab).symm.trans (h k hk a b ha hab).2⟩

theorem congr_dens (h : PairInt m₀ G D) (e : ∀ u k, D u k = D' u k) : PairInt m₀ G D' := by
  have : D = D' := funext fun u => funext (e u)
  exact this ▸ h

end PairInt

section Pieces

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1]) {m₀ : ℝ} (hm₀ : 0 < m₀)

include hflow hrow hrow4 hm₀

/-- **A piece with eight lines at a photon pair** is the photon-mass integral of its density. -/
theorem pairInt_pieceA (i j : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {X Y : ℝ} (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 4 (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4 (N k)) :
    PairInt m₀ (fun a b k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
        (castLoopMatrix fun l => base (shA i j l)) (fun l => c (shA i j l) • k)
        ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a, b])
      fun u k => pairDens (N k) (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k) ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, 0] (Fin.last 6)
        u := by
  intro k hk a b ha hab
  have hM : (![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a, b] : Fin 8 → ℝ) =
      Fin.snoc (![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a] : Fin 7 → ℝ) b := by
    funext l; fin_cases l <;> rfl
  have h := pvOf_vpShape_pair base c y₁ y₂ hflow hrow hrow4 (Or.inr rfl) (shA i j)
    (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega) hcrit (hpoly k) (hB k) hm₀
    ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a]
    (fun l hl => by
      fin_cases l
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl]) hk rfl ha hab
  have hd : pairDens (N k) (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
      (fun l => c (shA i j l.castSucc) • k) ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a] (Fin.last 6) =
      pairDens (N k) (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
      (fun l => c (shA i j l.castSucc) • k) ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, 0] (Fin.last 6) :=
    funext <| pairDens_congr_mass _ _ _ _ (fun l hl => by
      fin_cases l <;> simp [Fin.ext_iff] at hl ⊢)
  rw [hd] at h
  dsimp only
  rw [hM]
  exact h

/-- **A piece with seven lines at a photon pair** is the photon-mass integral of its density. -/
theorem pairInt_pieceB (i : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {Y : ℝ} (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 3 (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4 (N k)) :
    PairInt m₀ (fun a b k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
        (castLoopMatrix fun l => base (shB i l)) (fun l => c (shB i l) • k)
        ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a, b])
      fun u k => pairDens (N k) (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k) ![Mf 0, Mf 1, Mf 2, Mf 3, Y, 0] (Fin.last 5) u := by
  intro k hk a b ha hab
  have hM : (![Mf 0, Mf 1, Mf 2, Mf 3, Y, a, b] : Fin 7 → ℝ) =
      Fin.snoc (![Mf 0, Mf 1, Mf 2, Mf 3, Y, a] : Fin 6 → ℝ) b := by
    funext l; fin_cases l <;> rfl
  have h := pvOf_vpShape_pair base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB i)
    (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega) hcrit (hpoly k) (hB k) hm₀
    ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a]
    (fun l hl => by
      fin_cases l
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl]) hk rfl ha hab
  have hd : pairDens (N k) (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
      (fun l => c (shB i l.castSucc) • k) ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a] (Fin.last 5) =
      pairDens (N k) (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
      (fun l => c (shB i l.castSucc) • k) ![Mf 0, Mf 1, Mf 2, Mf 3, Y, 0] (Fin.last 5) :=
    funext <| pairDens_congr_mass _ _ _ _ (fun l hl => by
      fin_cases l <;> simp [Fin.ext_iff] at hl ⊢)
  rw [hd] at h
  dsimp only
  rw [hM]
  exact h

end Pieces

end QED.GradedProof.RPi4

end
