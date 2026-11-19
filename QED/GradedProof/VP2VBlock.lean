/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VAlg

/-!
# The two-loop classes `VA`, `VB`, `VC`: the block-summed loop is integrable

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2. For line data
(`base`, `pp`) of a class satisfying the decidable criteria of its pieces, and four odd vertex
matrices `A`:

* the numerators of the pieces have the degrees and the pointwise bounds of the refined two-loop
  theorems (`rb_vT`, `isLoopPoly_vT`, `isLoopPoly_vE2`, `rb_propDenom_pad`);
* `jef_vTriple`: the three-flavour Pauli–Villars combination of the loop integrand
  `K D_{m_γ}(q)⁻¹ D_Λ(q)⁻¹ vT(M) ∏ D_M(y_l)⁻¹` is integrable in both stages (T₉′), through
  `tri_v_eq`;
* `jef_vBlock`: so is its flavour sum under the block Pauli–Villars conditions.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.VP2

open QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat jointEnergyFirstIntegrable_add)
open QED.Integration.TwoLoop (lineMomentum lineDenom castLoopMatrix RefinedBound
  IntNoSubdivergenceRefined LoopQuartic refinedBound_lineMomentum)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Matrix bounds -/

namespace RBM

variable {m : ℕ} {al : Fin (m + 1) → Fin 2 → ℝ} {E : Finset (Fin (m + 1))} {k : ℕ}
  {A B : (Fin 2 → Fin 4 → ℝ) → Mat}

theorem mono (h : RefinedBoundMat al E k A) {E' : Finset (Fin (m + 1))} {k' : ℕ} (hE : E ⊆ E')
    (hk : k ≤ k') : RefinedBoundMat al E' k' A := fun i j => (h i j).mono hE hk

theorem mulC (h : RefinedBoundMat al E k A) (C : Mat) :
    RefinedBoundMat al E k fun ℓ => A ℓ * C :=
  mono (RefinedBoundMat.mul h (RefinedBoundMat.const C) (Finset.disjoint_empty_right E))
    (by simp) (by simp)

theorem cMul (C : Mat) (h : RefinedBoundMat al E k A) :
    RefinedBoundMat al E k fun ℓ => C * A ℓ :=
  mono (RefinedBoundMat.mul (RefinedBoundMat.const C) h (Finset.disjoint_empty_left E))
    (by simp) (by simp)

theorem mulN (h : RefinedBoundMat al E k A) {e : Fin (m + 1)} (hB : RefinedBoundMat al {e} 1 B)
    (he : e ∉ E) : RefinedBoundMat al (insert e E) (k + 1) fun ℓ => A ℓ * B ℓ :=
  mono (RefinedBoundMat.mul h hB (Finset.disjoint_singleton_right.mpr he))
    (by rw [Finset.union_comm, ← Finset.insert_eq]) le_rfl

end RBM

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ)

theorem rbm_fm {m : ℕ} (sh : Fin (m + 1) → Fin 5) (n : Fin (m + 1)) (l : Fin 4)
    (h : sh n = l.castSucc) (M : ℝ) :
    RefinedBoundMat (castLoopMatrix fun k => base (sh k)) {n} 1
      fun ℓ => electronNumerator M (fm base pp l ℓ) := by
  have := fun i j => QED.TwoLoop.ClassIntegrable.refinedBound_electronNumerator
    (castLoopMatrix fun k => base (sh k)) (fun k => pp (sh k)) n M i j
  simp only [lineMomentum_sh, h] at this
  exact this

/-- **The bound of the loop trace** on four lines carrying the four fermion momenta. -/
theorem rb_vT {m : ℕ} (sh : Fin (m + 1) → Fin 5) (e : Fin 4 → Fin (m + 1))
    (he : ∀ l, sh (e l) = l.castSucc) (h01 : e 0 ≠ e 1) (h02 : e 0 ≠ e 2) (h03 : e 0 ≠ e 3)
    (h12 : e 1 ≠ e 2) (h13 : e 1 ≠ e 3) (h23 : e 2 ≠ e 3) (A : Fin 4 → Mat) (M : ℝ) :
    RefinedBound (castLoopMatrix fun k => base (sh k)) {e 0, e 1, e 2, e 3} 4
      fun ℓ => vT A M (fun l => fm base pp l ℓ) := by
  have N := fun l => rbm_fm base pp sh (e l) l (he l) M
  have h0 : RefinedBoundMat (castLoopMatrix fun k => base (sh k)) ∅ 0 fun _ => A 0 :=
    RefinedBoundMat.const _
  have h := RefinedBoundMat.trace (RBM.mulN (RBM.mulC (RBM.mulN (RBM.mulC (RBM.mulN
    (RBM.mulC (RBM.mulN h0 (N 0) (Finset.notMem_empty _)) (A 1)) (N 1) (by simp [h01.symm]))
    (A 2)) (N 2) (by simp [h02.symm, h12.symm])) (A 3)) (N 3)
    (by simp [h03.symm, h13.symm, h23.symm]))
  refine h.mono (fun x hx => ?_) le_rfl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem isLoopPolyMat_fm (l : Fin 4) (M : ℝ) :
    IsLoopPolyMat 2 1 fun ℓ => electronNumerator M (fm base pp l ℓ) :=
  (isLoopAffine_lineMomentum _ _ _).isLoopPolyMat_electronNumerator M

theorem isLoopPoly_vT (A : Fin 4 → Mat) (M : ℝ) :
    IsLoopPoly 2 4 fun ℓ => vT A M (fun l => fm base pp l ℓ) := by
  have N := fun l => isLoopPolyMat_fm base pp l M
  have h := ((((((((IsLoopPolyMat.const (A 0)).mul (N 0)).mul (IsLoopPolyMat.const (A 1))).mul
    (N 1)).mul (IsLoopPolyMat.const (A 2))).mul (N 2)).mul (IsLoopPolyMat.const (A 3))).mul
    (N 3)).trace
  exact h.mono (by norm_num)

theorem isLoopPoly_vE2 (A : Fin 4 → Mat) :
    IsLoopPoly 2 2 fun ℓ => vE2 A (fun l => fm base pp l ℓ) := by
  have N := fun l => isLoopPolyMat_fm base pp l 0
  have C := fun l => IsLoopPolyMat.const (L := 2) (A l)
  unfold vE2
  refine ((((((?_ : IsLoopPoly 2 2 _).add ?_).add ?_).add ?_).add ?_).add ?_)
  · exact (((C 0).mul ((C 1).mul ((C 2).mul ((N 2).mul ((C 3).mul (N 3))))))).trace.mono
      (by norm_num)
  · exact (((C 0).mul ((C 1).mul ((N 1).mul ((C 2).mul ((C 3).mul (N 3))))))).trace.mono
      (by norm_num)
  · exact (((C 0).mul ((C 1).mul ((N 1).mul ((C 2).mul ((N 2).mul (C 3))))))).trace.mono
      (by norm_num)
  · exact (((C 0).mul ((N 0).mul ((C 1).mul ((C 2).mul ((C 3).mul (N 3))))))).trace.mono
      (by norm_num)
  · exact (((C 0).mul ((N 0).mul ((C 1).mul ((C 2).mul ((N 2).mul (C 3))))))).trace.mono
      (by norm_num)
  · exact (((C 0).mul ((N 0).mul ((C 1).mul ((N 1).mul ((C 2).mul (C 3))))))).trace.mono
      (by norm_num)

/-- The denominator of a line, padded by a second line with the same momentum, is bounded on the
two lines. -/
theorem rb_propDenom_pad {m : ℕ} (sh : Fin (m + 1) → Fin 5) (a b : Fin (m + 1)) (hab : a ≠ b)
    (l : Fin 4) (ha : sh a = l.castSucc) (hb : sh b = l.castSucc) (Y ε : ℝ) :
    RefinedBound (castLoopMatrix fun k => base (sh k)) {a, b} 2
      fun ℓ => propDenom Y ε (fm base pp l ℓ) := by
  have e : (fun ℓ => propDenom Y ε (fm base pp l ℓ)) = fun ℓ =>
      (∑ μ ∈ Finset.univ, ∑ ν ∈ Finset.univ, ((Minkowski.metric μ ν : ℝ) : ℂ) *
        (((fm base pp l ℓ μ : ℝ) : ℂ) * ((fm base pp l ℓ ν : ℝ) : ℂ))) +
          (((Y ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) := by
    funext ℓ
    simp only [propDenom, Minkowski.dot]
    push_cast
    simp only [mul_assoc]
    ring
  rw [e]
  have La := fun μ => refinedBound_lineMomentum (castLoopMatrix fun k => base (sh k))
    (fun k => pp (sh k)) a μ
  have Lb := fun μ => refinedBound_lineMomentum (castLoopMatrix fun k => base (sh k))
    (fun k => pp (sh k)) b μ
  simp only [lineMomentum_sh, ha, hb] at La Lb
  have hd : Disjoint ({a} : Finset (Fin (m + 1))) {b} := Finset.disjoint_singleton.mpr hab
  refine RefinedBound.add (RefinedBound.sum _ fun μ _ => RefinedBound.sum _ fun ν _ => ?_)
    ((RefinedBound.const _).mono (Finset.empty_subset _) (by norm_num))
  refine (((La μ).mul (Lb ν) hd).const_mul _).mono (fun x hx => ?_) le_rfl
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hx ⊢
  exact hx


/-! ### The three-flavour combination -/

/-- The loop integrand of one flavour of mass `M`. -/
noncomputable def vH (A : Fin 4 → Mat) (ε M : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vT A M (fun l => fm base pp l ℓ) * ∏ l : Fin 4, (propDenom M ε (fm base pp l ℓ))⁻¹

/-- The photon factor. -/
noncomputable def vD (mγ Λ ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (propDenom mγ ε (phm base pp ℓ))⁻¹ * (propDenom Λ ε (phm base pp ℓ))⁻¹

/-- The masses of the fermion lines in a piece with eight lines. -/
def mA (M X Y : ℝ) (i j l : Fin 4) : ℝ := if l ≤ i then M else if l ≤ j then X else Y

/-- The masses of the fermion lines in a piece with seven lines. -/
def mB (X Y : ℝ) (i l : Fin 4) : ℝ := if l ≤ i then X else Y

theorem sq_mA (M X Y : ℝ) (i j l : Fin 4) : ((mA M X Y i j l : ℝ) : ℂ) ^ 2 =
    if l ≤ i then (M : ℂ) ^ 2 else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2 := by
  unfold mA
  split_ifs <;> rfl

theorem sq_mB (X Y : ℝ) (i l : Fin 4) :
    ((mB X Y i l : ℝ) : ℂ) ^ 2 = if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2 := by
  unfold mB
  split_ifs <;> rfl

theorem e4_cases {m : ℕ} (sh : Fin (m + 1) → Fin 5) (e : Fin 4 → Fin (m + 1))
    (h : sh (e 0) = (0 : Fin 4).castSucc ∧ sh (e 1) = (1 : Fin 4).castSucc ∧
      sh (e 2) = (2 : Fin 4).castSucc ∧ sh (e 3) = (3 : Fin 4).castSucc) :
    ∀ l, sh (e l) = l.castSucc := by
  intro l
  fin_cases l
  exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- **The three-flavour Pauli–Villars combination of one class integrand is integrable.** -/
theorem jef_vTriple {A : Fin 4 → Mat} (hA : ∀ l, IsOddG (A l))
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (K : ℂ) (M X Y mγ Λ : ℝ) (hMX : M ^ 2 - X ^ 2 ≠ 0) (hMY : M ^ 2 - Y ^ 2 ≠ 0)
    (hXY : X ^ 2 - Y ^ 2 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      K * vD base pp mγ Λ ε ℓ * vH base pp A ε M ℓ +
        (triA M X Y : ℂ) * (K * vD base pp mγ Λ ε ℓ * vH base pp A ε X ℓ) +
        (triB M X Y : ℂ) * (K * vD base pp mγ Λ ε ℓ * vH base pp A ε Y ℓ) := by
  have hε' : ε ≠ 0 := hε.ne'
  have h01 : (M : ℂ) ^ 2 - (X : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hMX
  have h02 : (M : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hMY
  have h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hXY
  have hd : ∀ (m : ℝ) (l : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ), propDenom m ε (fm base pp l ℓ) =
      propDenom 0 ε (fm base pp l ℓ) + (m : ℂ) ^ 2 := fun m l ℓ => propDenom_eq_add m ε _
  have nz : ∀ (m : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (l : Fin 4),
      propDenom 0 ε (fm base pp l ℓ) + (m : ℂ) ^ 2 ≠ 0 := fun m ℓ l => by
    rw [← hd]
    exact propDenom_ne_zero hε' _
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      if i ≤ j then
        K * vD base pp mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (vE0 A (fun l => fm base pp l ℓ) + (M : ℂ) ^ 2 * vE2 A (fun l => fm base pp l ℓ) +
            ((M : ℂ) ^ 2) ^ 2 * vE4 A) *
          ((∏ l : Fin 4, (propDenom 0 ε (fm base pp l ℓ) + if l ≤ i then (M : ℂ) ^ 2 else
              if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)⁻¹) *
            (propDenom 0 ε (fm base pp i ℓ) + (X : ℂ) ^ 2)⁻¹ *
            (propDenom 0 ε (fm base pp j ℓ) + (Y : ℂ) ^ 2)⁻¹)
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      have hB := (rb_vT base pp (shA i j) ![0, 1, 2, 3]
        (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) A M).const_mul
          (K * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))
      have h := jef_pieceA base pp i j (hcA i j) (mA M X Y i j) X Y mγ Λ hε
        ((isLoopPoly_vT base pp A M).const_mul
          (K * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2))) hB
      refine JEF.congr h fun ℓ => ?_
      rw [vT_eq hA, Finset.prod_congr rfl fun l _ => by rw [hd, sq_mA], hd X i ℓ, hd Y j ℓ]
      simp only [vD]
      ring
    · simp only [hij, ite_false]
      exact JEF.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      -(K * vD base pp mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
          (vE2 A (fun l => fm base pp l ℓ) + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * vE4 A) *
        ((∏ l : Fin 4, (propDenom 0 ε (fm base pp l ℓ) +
            if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)⁻¹) *
          (propDenom 0 ε (fm base pp i ℓ) + (Y : ℂ) ^ 2)⁻¹) := by
    intro i
    set c : ℂ := -(K * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) with hc
    have rT := fun m => rb_vT base pp (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) A m
    have hB0 := ((rT M).sub (rT X)).const_mul (c / ((M : ℂ) ^ 2 - (X : ℂ) ^ 2))
    have hB : RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4
        fun ℓ => c * (vE2 A (fun l => fm base pp l ℓ) + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * vE4 A) := by
      refine (congrArg (RefinedBound _ _ 4) (funext fun ℓ => ?_)).mp
        (hB0.mono (by decide) le_rfl)
      rw [vT_eq hA, vT_eq hA]
      field_simp
      ring
    have hP : IsLoopPoly 2 3 fun ℓ =>
        c * (vE2 A (fun l => fm base pp l ℓ) + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * vE4 A) :=
      (((isLoopPoly_vE2 base pp A).add (IsLoopPoly.const _)).const_mul c).mono (by norm_num)
    have h := jef_pieceB base pp i (hcB i) (mB X Y i) Y mγ Λ hε hP hB
    refine JEF.congr h fun ℓ => ?_
    rw [Finset.prod_congr rfl fun l _ => by rw [hd, sq_mB], hd Y i ℓ]
    simp only [vD, hc]
    ring
  -- the padded piece
  have PC : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      K * vD base pp mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        vE4 A * ∏ l : Fin 4, (propDenom 0 ε (fm base pp l ℓ) + (Y : ℂ) ^ 2)⁻¹ := by
    set c : ℂ := K * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * vE4 A with hc
    have hB : RefinedBound (castLoopMatrix fun n => base (shB 0 n)) {0, 1, 2, 3, 4} 4
        fun ℓ => c * propDenom Y ε (fm base pp 0 ℓ) :=
      ((rb_propDenom_pad base pp (shB 0) 0 4 (by decide) 0 rfl rfl Y ε).const_mul
        c).mono (by decide) (by norm_num)
    have hP : IsLoopPoly 2 3 fun ℓ => c * propDenom Y ε (fm base pp 0 ℓ) :=
      (((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y ε).const_mul c).mono
        (by norm_num)
    have h := jef_pieceB base pp 0 (hcB 0) (fun _ => Y) Y mγ Λ hε hP hB
    refine JEF.congr h fun ℓ => ?_
    have h0 := nz Y ℓ 0
    rw [Finset.prod_congr rfl fun l _ => by rw [hd Y l ℓ], hd Y 0 ℓ]
    simp only [vD, hc]
    field_simp
  have hS := jointEnergyFirstIntegrable_add (jointEnergyFirstIntegrable_add
    (JEF.sum Finset.univ fun i _ => JEF.sum Finset.univ fun j _ => PA i j)
    (JEF.sum Finset.univ fun i _ => PB i)) PC
  refine JEF.congr hS fun ℓ => ?_
  have htA : ((triA M X Y : ℝ) : ℂ) =
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triA]; push_cast; rfl
  have htB : ((triB M X Y : ℝ) : ℂ) =
      ((M : ℂ) ^ 2 - (X : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triB]; push_cast; rfl
  rw [← tri_v_eq (fun l => propDenom 0 ε (fm base pp l ℓ)) (K * vD base pp mγ Λ ε ℓ)
    (vE0 A (fun l => fm base pp l ℓ)) (vE2 A (fun l => fm base pp l ℓ)) (vE4 A)
    ((M : ℂ) ^ 2) ((X : ℂ) ^ 2) ((Y : ℂ) ^ 2) h01 h02 h12 (nz M ℓ) (nz X ℓ) (nz Y ℓ)]
  simp only [vH, vT_eq hA, htA, htB, hd M, hd X, hd Y]

/-- **The block-summed flavour sum of one class integrand is integrable** (T₉′). -/
theorem jef_vBlock {A : Fin 4 → Mat} (hA : ∀ l, IsOddG (A l))
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (K : ℂ) (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (K * vD base pp mγ Λ ε ℓ * vH base pp A ε (Φ.mass f) ℓ) := by
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
    (jef_vTriple base pp hA hcA hcB K (Φ.mass f) X (X + 1) mγ Λ (h1 f) (h2 f) hXY hε)
    (Φ.coeff f : ℂ)) fun ℓ => ?_
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
    (fun _ M => K * vD base pp mγ Λ ε ℓ * vH base pp A ε M ℓ)]

end Setting

end QED.GradedProof.VP2

end
