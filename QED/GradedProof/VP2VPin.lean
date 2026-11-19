/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VWardR

/-!
# The pinched loops of the two-loop Ward identity: integrability

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. Contracting a
two-loop class with `k_μ` cancels one of the two lines next to the vertex `μ`, leaving a fermion
loop with three lines (rows `r 0, r 1, r 2` of the class routing), three vertex matrices `B` and
the internal photon. For one flavour of mass `m` its numerator
`tr3 B N(y) = Tr[B₀ N(y₀) B₁ N(y₁) B₂ N(y₂)]` is `E₀ + m² E₂` (`tr3_eq`, odd traces vanish),
of degrees three and one.

* `tri3_eq`: the three-flavour Pauli–Villars combination is a sum of six products of seven
  inverse denominators and three of six (`dd2_quad_inv3`);
* `jef_piece7`: such products with a cubic numerator over seven lines are integrable in both
  stages (T₉′) under the decidable criterion;
* `jef_g3Triple`, `jef_g3Block`: the three-flavour combination and the block-summed flavour sum
  of a three-line loop are integrable, the pieces with six lines padded by a seventh.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat jointEnergyFirstIntegrable_add)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Three-line traces -/

/-- The trace of a loop with three vertex matrices `B` and three numerators `N`. -/
noncomputable def tr3 (B N : Fin 3 → Mat) : ℂ :=
  (B 0 * N 0 * B 1 * N 1 * B 2 * N 2).trace

/-- The coefficient of `m⁰` of a three-line loop. -/
noncomputable def p3E0 (B : Fin 3 → Mat) (y : Fin 3 → Fin 4 → ℝ) : ℂ :=
  (B 0 * (electronNumerator 0 (y 0) * (B 1 * (electronNumerator 0 (y 1) *
    (B 2 * electronNumerator 0 (y 2)))))).trace

/-- The coefficient of `m²` of a three-line loop. -/
noncomputable def p3E2 (B : Fin 3 → Mat) (y : Fin 3 → Fin 4 → ℝ) : ℂ :=
  (B 0 * (B 1 * (B 2 * electronNumerator 0 (y 2)))).trace +
    (B 0 * (B 1 * (electronNumerator 0 (y 1) * B 2))).trace +
    (B 0 * (electronNumerator 0 (y 0) * (B 1 * B 2))).trace

theorem tr3_eq {B : Fin 3 → Mat} (hB : ∀ l, IsOddG (B l)) (m : ℝ) (y : Fin 3 → Fin 4 → ℝ) :
    tr3 B (fun l => electronNumerator m (y l)) = p3E0 B y + (m : ℂ) ^ 2 * p3E2 B y := by
  have n := fun l => isOddG_eN0 (y l)
  unfold tr3 p3E0 p3E2
  simp only [eN_eq_add m]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_assoc, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [IsOddG.trace5 (hB 0) (n 0) (hB 1) (n 1) (hB 2),
    IsOddG.trace5 (hB 0) (n 0) (hB 1) (hB 2) (n 2),
    IsOddG.trace5 (hB 0) (hB 1) (n 1) (hB 2) (n 2), IsOddG.trace3 (hB 0) (hB 1) (hB 2)]
  ring

/-! ### The three-flavour combination of three lines -/

theorem dd2_quad_inv3 (V : Fin 3 → ℂ) (s0 s1 s2 E0 E2 E4 : ℂ) (h01 : s0 - s1 ≠ 0)
    (h02 : s0 - s2 ≠ 0) (h12 : s1 - s2 ≠ 0) (h0 : ∀ i, V i + s0 ≠ 0) (h1 : ∀ i, V i + s1 ≠ 0)
    (h2 : ∀ i, V i + s2 ≠ 0) :
    dd2 (fun s : ℂ => (E0 + s * E2 + s ^ 2 * E4) *
      ((V 0 + s)⁻¹ * (V 1 + s)⁻¹ * (V 2 + s)⁻¹)) s0 s1 s2 =
        (E0 + s0 * E2 + s0 ^ 2 * E4) *
          (∑ i : Fin 3, ∑ j : Fin 3, if i ≤ j then
            (∏ l : Fin 3, (V l + if l ≤ i then s0 else if l ≤ j then s1 else s2)⁻¹) *
              (V i + s1)⁻¹ * (V j + s2)⁻¹ else 0) -
          (E2 + (s0 + s1) * E4) *
            (∑ i : Fin 3, (∏ l : Fin 3, (V l + if l ≤ i then s1 else s2)⁻¹) * (V i + s2)⁻¹) +
          E4 * ∏ l : Fin 3, (V l + s2)⁻¹ := by
  rw [dd2_mul h01 h02 h12, dd2_mul h01 h02 h12, dd2_mul h01 h02 h12]
  simp only [dd1_mul h01, dd1_mul h12, dd2_quad _ _ _ h01 h02 h12, dd1_quad _ _ _ h01,
    dd1_inv (h0 _) (h1 _) h01, dd1_inv (h1 _) (h2 _) h12,
    dd2_inv (h0 _) (h1 _) (h2 _) h01 h02 h12]
  simp only [Fin.sum_univ_three, Fin.prod_univ_three]
  simp (config := {decide := true}) only [Fin.isValue, ite_true, ite_false]
  ring

/-- **The three-flavour combination of a three-line loop** (numerator linear in `m²`). -/
theorem tri3_eq (V : Fin 3 → ℂ) (K E0 E2 s0 s1 s2 : ℂ) (h01 : s0 - s1 ≠ 0)
    (h02 : s0 - s2 ≠ 0) (h12 : s1 - s2 ≠ 0) (h0 : ∀ i, V i + s0 ≠ 0) (h1 : ∀ i, V i + s1 ≠ 0)
    (h2 : ∀ i, V i + s2 ≠ 0) :
    K * ((E0 + s0 * E2) * ∏ l, (V l + s0)⁻¹) +
        (s2 - s0) / (s1 - s2) * (K * ((E0 + s1 * E2) * ∏ l, (V l + s1)⁻¹)) +
        (s0 - s1) / (s1 - s2) * (K * ((E0 + s2 * E2) * ∏ l, (V l + s2)⁻¹)) =
      ∑ i : Fin 3, ∑ j : Fin 3, (if i ≤ j then
          K * (s1 - s0) * (s2 - s0) * (E0 + s0 * E2) *
            ((∏ l : Fin 3, (V l + if l ≤ i then s0 else if l ≤ j then s1 else s2)⁻¹) *
              (V i + s1)⁻¹ * (V j + s2)⁻¹) else 0) +
        ∑ i : Fin 3, -(K * (s1 - s0) * (s2 - s0)) * E2 *
          ((∏ l : Fin 3, (V l + if l ≤ i then s1 else s2)⁻¹) * (V i + s2)⁻¹) := by
  set H : ℂ → ℂ := fun s => (E0 + s * E2 + s ^ 2 * 0) *
    ((V 0 + s)⁻¹ * (V 1 + s)⁻¹ * (V 2 + s)⁻¹) with hH
  have hT := tri_eq_dd2 h01 h02 h12 H
  have hL := dd2_quad_inv3 V s0 s1 s2 E0 E2 0 h01 h02 h12 h0 h1 h2
  rw [← hH] at hL
  have e : ∀ s, (E0 + s * E2) * ∏ l, (V l + s)⁻¹ = H s := fun s => by
    simp only [hH, Fin.prod_univ_three]
    ring
  rw [e, e, e]
  calc K * H s0 + (s2 - s0) / (s1 - s2) * (K * H s1) + (s0 - s1) / (s1 - s2) * (K * H s2)
      = K * (H s0 + (s2 - s0) / (s1 - s2) * H s1 + (s0 - s1) / (s1 - s2) * H s2) := by ring
    _ = K * ((s1 - s0) * (s2 - s0) * dd2 H s0 s1 s2) := by rw [hT]
    _ = _ := by
      rw [hL]
      simp only [Fin.sum_univ_three, Fin.prod_univ_three]
      simp (config := {decide := true}) only [Fin.isValue, ite_true, ite_false]
      ring

/-! ### Pieces with seven lines -/

/-- **A piece with seven lines and a cubic numerator** is integrable in both stages. -/
theorem jef_piece7 (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ) (sh : Fin 7 → Fin 5)
    {E : Finset (Fin 7)} (hcrit : IntNoSubdivergenceRefined 2 E fun n => base (sh n))
    (Ms : Fin 7 → ℝ) {ε : ℝ} (hε : 0 < ε) {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hpoly : IsLoopPoly 2 3 F) (hB : RefinedBound (castLoopMatrix fun n => base (sh n)) E 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F ℓ *
      ∏ n, (propDenom (Ms n) ε (lineMomentum (castLoopMatrix base) pp (sh n) ℓ))⁻¹ := by
  obtain ⟨Q, hq, rfl⟩ := IsLoopPoly.exists_loopQuartic_cubic hpoly
  exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic Q
    (castLoopMatrix fun n => base (sh n)) (fun n => pp (sh n)) Ms hq (le_refl 6) hε
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB

/-- The rows of a piece with seven lines of a three-line loop: the three lines, the lines `i`
and `j` again, the photon twice. -/
def shA3 (r : Fin 3 → Fin 4) (i j : Fin 3) : Fin 7 → Fin 5 :=
  ![(r 0).castSucc, (r 1).castSucc, (r 2).castSucc, (r i).castSucc, (r j).castSucc,
    Fin.last 4, Fin.last 4]

/-- The rows of a piece with six lines of a three-line loop, padded: the three lines, the line
`i` twice more, the photon twice. -/
def shB3 (r : Fin 3 → Fin 4) (i : Fin 3) : Fin 7 → Fin 5 :=
  ![(r 0).castSucc, (r 1).castSucc, (r 2).castSucc, (r i).castSucc, (r i).castSucc,
    Fin.last 4, Fin.last 4]

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ) (r : Fin 3 → Fin 4)

/-- The integrand of a three-line loop of mass `M` with numerator `Num M`, photon factor
included. -/
noncomputable def g3 (Num : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) (mγ Λ M ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vD base pp mγ Λ ε ℓ * (Num M ℓ * ∏ l : Fin 3, (propDenom M ε (fm base pp (r l) ℓ))⁻¹)

theorem jef_pieceA3 (i j : Fin 3)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => base (shA3 r i j n))
    (Mf : Fin 3 → ℝ) (X Y mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hpoly : IsLoopPoly 2 3 F)
    (hB : RefinedBound (castLoopMatrix fun n => base (shA3 r i j n)) {0, 1, 2} 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F ℓ *
      ((∏ l : Fin 3, (propDenom (Mf l) ε (fm base pp (r l) ℓ))⁻¹) *
        (propDenom X ε (fm base pp (r i) ℓ))⁻¹ * (propDenom Y ε (fm base pp (r j) ℓ))⁻¹ *
        ((propDenom mγ ε (phm base pp ℓ))⁻¹ * (propDenom Λ ε (phm base pp ℓ))⁻¹)) := by
  have h := jef_piece7 base pp (shA3 r i j) hcrit ![Mf 0, Mf 1, Mf 2, X, Y, mγ, Λ] hε hpoly hB
  refine JEF.congr h fun ℓ => ?_
  rw [Fin.prod_univ_seven]
  simp only [Fin.prod_univ_three, shA3, Matrix.cons_val, fm, phm]
  ring

theorem jef_pieceB3 (i : Fin 3)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB3 r i n))
    (Mf : Fin 3 → ℝ) (Y mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hpoly : IsLoopPoly 2 1 F)
    (hB : RefinedBound (castLoopMatrix fun n => base (shB3 r i n)) {0, 1, 2} 1 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F ℓ *
      ((∏ l : Fin 3, (propDenom (Mf l) ε (fm base pp (r l) ℓ))⁻¹) *
        (propDenom Y ε (fm base pp (r i) ℓ))⁻¹ *
        ((propDenom mγ ε (phm base pp ℓ))⁻¹ * (propDenom Λ ε (phm base pp ℓ))⁻¹)) := by
  have hpad := rb_propDenom_pad base pp (shB3 r i) 3 4 (by decide) (r i) rfl rfl Y ε
  have hB' : RefinedBound (castLoopMatrix fun n => base (shB3 r i n)) {0, 1, 2, 3, 4} 4
      fun ℓ => F ℓ * propDenom Y ε (fm base pp (r i) ℓ) :=
    (hB.mul hpad (by decide)).mono (by decide) (by norm_num)
  have hP : IsLoopPoly 2 3 fun ℓ => F ℓ * propDenom Y ε (fm base pp (r i) ℓ) :=
    hpoly.mul ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y ε)
  have h := jef_piece7 base pp (shB3 r i) hcrit ![Mf 0, Mf 1, Mf 2, Y, Y, mγ, Λ] hε hP hB'
  refine JEF.congr h fun ℓ => ?_
  have hne := propDenom_ne_zero (M := Y) hε.ne' (fm base pp (r i) ℓ)
  rw [Fin.prod_univ_seven]
  simp only [Fin.prod_univ_three, shB3, Matrix.cons_val, fm, phm]
  field_simp

/-- **The three-flavour combination of a three-line loop is integrable.** -/
theorem jef_g3Triple
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => base (shA3 r i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB3 r i n))
    (Num : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) (E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hE : ∀ m ℓ, Num m ℓ = E0 ℓ + (m : ℂ) ^ 2 * E2 ℓ) (hP : ∀ m, IsLoopPoly 2 3 (Num m))
    (hP2 : IsLoopPoly 2 1 E2)
    (hBA : ∀ m i j, RefinedBound (castLoopMatrix fun n => base (shA3 r i j n)) {0, 1, 2} 4
      (Num m))
    (hBB : ∀ i, RefinedBound (castLoopMatrix fun n => base (shB3 r i n)) {0, 1, 2} 1 E2)
    (mγ Λ M X Y : ℝ) (hMX : M ^ 2 - X ^ 2 ≠ 0) (hMY : M ^ 2 - Y ^ 2 ≠ 0)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => g3 base pp r Num mγ Λ M ε ℓ +
      (triA M X Y : ℂ) * g3 base pp r Num mγ Λ X ε ℓ +
      (triB M X Y : ℂ) * g3 base pp r Num mγ Λ Y ε ℓ := by
  have h01 : (M : ℂ) ^ 2 - (X : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hMX
  have h02 : (M : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hMY
  have h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hXY
  have hd : ∀ (m : ℝ) (l : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ),
      propDenom m ε (fm base pp l ℓ) = propDenom 0 ε (fm base pp l ℓ) + (m : ℂ) ^ 2 :=
    fun m l ℓ => propDenom_eq_add m ε _
  have nz : ∀ (m : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (l : Fin 3),
      propDenom 0 ε (fm base pp (r l) ℓ) + (m : ℂ) ^ 2 ≠ 0 := fun m ℓ l => by
    rw [← hd]
    exact propDenom_ne_zero hε.ne' _
  have PA : ∀ i j : Fin 3, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      if i ≤ j then
        vD base pp mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (E0 ℓ + (M : ℂ) ^ 2 * E2 ℓ) *
          ((∏ l : Fin 3, (propDenom 0 ε (fm base pp (r l) ℓ) + if l ≤ i then (M : ℂ) ^ 2 else
              if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)⁻¹) *
            (propDenom 0 ε (fm base pp (r i) ℓ) + (X : ℂ) ^ 2)⁻¹ *
            (propDenom 0 ε (fm base pp (r j) ℓ) + (Y : ℂ) ^ 2)⁻¹)
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      have h := jef_pieceA3 base pp r i j (hcA i j)
        (fun l => if l ≤ i then M else if l ≤ j then X else Y) X Y mγ Λ hε
        ((hP M).const_mul (((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)))
        ((hBA M i j).const_mul _)
      refine JEF.congr h fun ℓ => ?_
      have hs : ∀ l : Fin 3, propDenom (if l ≤ i then M else if l ≤ j then X else Y) ε
          (fm base pp (r l) ℓ) = propDenom 0 ε (fm base pp (r l) ℓ) +
            if l ≤ i then (M : ℂ) ^ 2 else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2 :=
        fun l => by rw [hd]; split_ifs <;> rfl
      rw [Finset.prod_congr rfl fun l _ => by rw [hs l], hd X (r i) ℓ, hd Y (r j) ℓ, hE]
      simp only [vD]
      ring
    · simp only [hij, ite_false]
      exact JEF.zero
  have PB : ∀ i : Fin 3, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      -(vD base pp mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
          E2 ℓ * ((∏ l : Fin 3, (propDenom 0 ε (fm base pp (r l) ℓ) +
            if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)⁻¹) *
          (propDenom 0 ε (fm base pp (r i) ℓ) + (Y : ℂ) ^ 2)⁻¹) := by
    intro i
    have h := jef_pieceB3 base pp r i (hcB i) (fun l => if l ≤ i then X else Y) Y mγ Λ hε
      (hP2.const_mul (-(((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))))
      ((hBB i).const_mul _)
    refine JEF.congr h fun ℓ => ?_
    have hs : ∀ l : Fin 3, propDenom (if l ≤ i then X else Y) ε (fm base pp (r l) ℓ) =
        propDenom 0 ε (fm base pp (r l) ℓ) + if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2 :=
      fun l => by rw [hd]; split_ifs <;> rfl
    rw [Finset.prod_congr rfl fun l _ => by rw [hs l], hd Y (r i) ℓ]
    simp only [vD]
    ring
  have hS := jointEnergyFirstIntegrable_add
    (JEF.sum Finset.univ fun i _ => JEF.sum Finset.univ fun j _ => PA i j)
    (JEF.sum Finset.univ fun i _ => PB i)
  refine JEF.congr hS fun ℓ => ?_
  have htA : ((triA M X Y : ℝ) : ℂ) =
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triA]; push_cast; rfl
  have htB : ((triB M X Y : ℝ) : ℂ) =
      ((M : ℂ) ^ 2 - (X : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triB]; push_cast; rfl
  rw [← tri3_eq (fun l => propDenom 0 ε (fm base pp (r l) ℓ)) (vD base pp mγ Λ ε ℓ)
    (E0 ℓ) (E2 ℓ) ((M : ℂ) ^ 2) ((X : ℂ) ^ 2) ((Y : ℂ) ^ 2) h01 h02 h12 (nz M ℓ) (nz X ℓ)
    (nz Y ℓ)]
  simp only [g3, hE, htA, htB, hd M, hd X, hd Y]

/-- **The block-summed flavour sum of a three-line loop is integrable.** -/
theorem jef_g3Block
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => base (shA3 r i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB3 r i n))
    (Num : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) (E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hE : ∀ m ℓ, Num m ℓ = E0 ℓ + (m : ℂ) ^ 2 * E2 ℓ) (hP : ∀ m, IsLoopPoly 2 3 (Num m))
    (hP2 : IsLoopPoly 2 1 E2)
    (hBA : ∀ m i j, RefinedBound (castLoopMatrix fun n => base (shA3 r i j n)) {0, 1, 2} 4
      (Num m))
    (hBB : ∀ i, RefinedBound (castLoopMatrix fun n => base (shB3 r i n)) {0, 1, 2} 1 E2)
    {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * g3 base pp r Num mγ Λ (Φ.mass f) ε ℓ := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := 1 + ∑ g, Φ.mass g with hX
  have hlt : ∀ g, Φ.mass g < X := fun g => by
    have := Finset.single_le_sum (fun g _ => (hpos g).le) (Finset.mem_univ g)
    linarith
  have hX0 : 0 < X := by
    have := Finset.sum_nonneg (s := Finset.univ) fun g _ => (hpos g).le
    linarith
  have hXY : X ^ 2 - (X + 1) ^ 2 ≠ 0 := by nlinarith
  have h1 : ∀ g, Φ.mass g ^ 2 - X ^ 2 ≠ 0 := fun g => by
    have := hlt g; have := hpos g; nlinarith
  have h2 : ∀ g, Φ.mass g ^ 2 - (X + 1) ^ 2 ≠ 0 := fun g => by
    have := hlt g; have := hpos g; nlinarith
  refine JEF.congr (JEF.sum Finset.univ fun f _ => JEF.const_mul
    (jef_g3Triple base pp r hcA hcB Num E0 E2 hE hP hP2 hBA hBB mγ Λ (Φ.mass f) X (X + 1)
      (h1 f) (h2 f) hXY hε) (Φ.coeff f : ℂ)) fun ℓ => ?_
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
    (fun _ M => g3 base pp r Num mγ Λ M ε ℓ)]

end Setting

end QED.GradedProof.VP2

end
