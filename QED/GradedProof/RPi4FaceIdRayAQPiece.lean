/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayAQGen
public import QED.GradedProof.RPi4MajLClass
public import QED.GradedProof.RPi4InstClass

/-!
# (R-Π₄) step L10, T2.UV: (A) with a power loss for the merged pieces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (input (A) of
`QED.GradedProof.RPi4.faceIdRay_of_size_rate`). The three kinds of merged pieces of a class
numerator (`QED.GradedProof.RPi4.faceIdRayAPieceA`, `…B`, `…P`) satisfy `FaceIdRayAQPow`
(all `u ≥ 1`), given

* the line classes of the rows (`clB`, rows `(1,0)`, `(0,1)`, `(1,-1)`);
* the coefficient bounds of the class (`FaceIdRayAQBd`, from the degrees along the loops:
  `faceIdRayAQBd_VA` for degree `≤ 1` along loop `1`, `faceIdRayAQBd_VB` otherwise);
* a cut pair, the flow lines `0, j'` and the integer checks of the four monomial families.

The numerators are taken as quartics of bounded degree along both loops at once
(`QED.GradedProof.RPi4.faceIdRayAQ_exists_loopQuartic`); the top monomial of the pieces with
seven lines is bounded by the flows of the fermion lines `0`, `j'`
(`QED.GradedProof.RPi4.maj_vNumE0_flow`, as in `QED.GradedProof.RPi4.majL_pieceA`).

* `faceIdRayAQRowZ`, `faceIdRayAQ_castLoopMatrix_row`, `FaceIdRayAQBd`, `faceIdRayAQBd_VA`,
  `faceIdRayAQBd_VB`;
* **`faceIdRayAQ_pieceA`**, **`faceIdRayAQ_pieceB`**, **`faceIdRayAQ_pieceP`**.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Line classes and coefficient bounds -/

/-- The three integer rows `(1,0)`, `(0,1)`, `(1,-1)`. -/
def faceIdRayAQRowZ : Fin 3 → Fin 2 → ℤ := ![![1, 0], ![0, 1], ![1, -1]]

theorem faceIdRayAQ_castLoopMatrix_row {n : ℕ} (a : Fin (n + 1) → Fin 2 → ℤ)
    (cl : Fin (n + 1) → Fin 3) (h : ∀ t, a t = faceIdRayAQRowZ (cl t)) (t : Fin (n + 1)) :
    castLoopMatrix a t = faceIdRayAQRow (cl t) := by
  funext s
  simp only [castLoopMatrix, h t]
  generalize cl t = b
  fin_cases b <;> fin_cases s <;> simp [faceIdRayAQRowZ, faceIdRayAQRow]

/-- **The coefficient bounds of a piece**: `‖T₂‖ ≤ C U⁻³ ∑_{K₂} z`,
`‖T₃‖ ≤ C U⁻⁴ (∑_{K₁} z)(∑_{K₃} z)` (sums over the lines of the classes `K`). -/
def FaceIdRayAQBd {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (cs : Fin (n + 1) → ℝ)
    (cl : Fin (n + 1) → Fin 3) (K₂ K₁ K₃ : Fin 3 → Prop) [DecidablePred K₂] [DecidablePred K₁]
    [DecidablePred K₃] (Q : Fin 3 → LoopQuartic) : Prop :=
  (∃ C, 0 ≤ C ∧ ∀ x : Fin n → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
    0 < symanzikU α (simplexPoint x) → ∀ t,
      ‖faceIdRayAPTwo (Q t) α (fun i => cs i • majRayVec 1) x‖ ≤
        C * (∑ u, if K₂ (cl u) then simplexPoint x u else 0) /
          symanzikU α (simplexPoint x) ^ 3) ∧
  (∃ C, 0 ≤ C ∧ ∀ x : Fin n → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
    0 < symanzikU α (simplexPoint x) → ∀ t,
      ‖faceIdRayAPThree (Q t) α x‖ ≤ C * ((∑ u, if K₁ (cl u) then simplexPoint x u else 0) *
        (∑ u, if K₃ (cl u) then simplexPoint x u else 0)) / symanzikU α (simplexPoint x) ^ 4)

/-- A bound for each of three quartics with a common nonnegative right side, uniformly. -/
theorem faceIdRayAQ_unif {n : ℕ} {f : Fin 3 → (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ}
    {S : (Fin n → ℝ) → Prop}
    (h : ∀ t, ∃ C, 0 ≤ C ∧ ∀ x, S x → f t x ≤ C * g x) (hg : ∀ x, S x → 0 ≤ g x) :
    ∃ C, 0 ≤ C ∧ ∀ x, S x → ∀ t, f t x ≤ C * g x := by
  choose C hC0 hC using h
  refine ⟨∑ t, C t, Finset.sum_nonneg fun t _ => hC0 t, fun x hx t => (hC t x hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun t _ => hC0 t)
    (Finset.mem_univ t)) (hg x hx)

section Bd

variable {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (cl : Fin (n + 1) → Fin 3)
  (hα : ∀ t, α t = faceIdRayAQRow (cl t)) (cs : Fin (n + 1) → ℝ) (Q : Fin 3 → LoopQuartic)

include hα

/-- **The coefficient bounds at degree `≤ 1` along loop `1`** (classes `VA`, `VC`). -/
theorem faceIdRayAQBd_VA (hQ : ∀ t, LoopDegLe 0 3 (Q t) ∧ LoopDegLe 1 1 (Q t)) :
    FaceIdRayAQBd α cs cl (· ≠ 0) (· ≠ 0) (· = 2) Q := by
  have hz : ∀ (p : Fin 3 → Prop) [DecidablePred p] (x : Fin n → ℝ),
      (∀ i, 0 ≤ simplexPoint x i) → 0 ≤ ∑ u, if p (cl u) then simplexPoint x u else 0 :=
    fun p _ x hz => Finset.sum_nonneg fun u _ => by split_ifs <;> simp [hz u]
  constructor
  · obtain ⟨C, hC0, hC⟩ := faceIdRayAQ_unif (S := fun x : Fin n → ℝ =>
      (∀ i, 0 ≤ simplexPoint x i) ∧ 0 < symanzikU α (simplexPoint x))
      (f := fun t x => ‖faceIdRayAPTwo (Q t) α (fun i => cs i • majRayVec 1) x‖)
      (g := fun x => (∑ u, if cl u ≠ 0 then simplexPoint x u else 0) /
        symanzikU α (simplexPoint x) ^ 3) (fun t => by
          obtain ⟨C, hC0, hC⟩ := faceIdRayAQ_norm_two_le_deg (Q t) α cl hα cs (hQ t).2
          exact ⟨C, hC0, fun x hx => (hC x hx.1 hx.2).trans_eq (mul_div_assoc _ _ _)⟩)
      fun x hx => div_nonneg (hz (· ≠ 0) x hx.1) (pow_pos hx.2 3).le
    exact ⟨C, hC0, fun x hx hU t => (hC x ⟨hx, hU⟩ t).trans_eq (mul_div_assoc _ _ _).symm⟩
  · obtain ⟨C, hC0, hC⟩ := faceIdRayAQ_unif (S := fun x : Fin n → ℝ =>
      (∀ i, 0 ≤ simplexPoint x i) ∧ 0 < symanzikU α (simplexPoint x))
      (f := fun t x => ‖faceIdRayAPThree (Q t) α x‖)
      (g := fun x => ((∑ u, if cl u ≠ 0 then simplexPoint x u else 0) *
        (∑ u, if cl u = 2 then simplexPoint x u else 0)) /
          symanzikU α (simplexPoint x) ^ 4) (fun t => by
          obtain ⟨C, hC0, hC⟩ := faceIdRayAQ_norm_three_le_VA (Q t) α cl hα (hQ t).1 (hQ t).2
          exact ⟨C, hC0, fun x hx => (hC x hx.1 hx.2).trans_eq (mul_div_assoc _ _ _)⟩)
      fun x hx => div_nonneg (mul_nonneg (hz (· ≠ 0) x hx.1) (hz (· = 2) x hx.1))
        (pow_pos hx.2 4).le
    exact ⟨C, hC0, fun x hx hU t => (hC x ⟨hx, hU⟩ t).trans_eq (mul_div_assoc _ _ _).symm⟩

/-- **The coefficient bounds at degree `≤ 3` along both loops** (class `VB`). -/
theorem faceIdRayAQBd_VB (hQ : ∀ t, LoopDegLe 0 3 (Q t) ∧ LoopDegLe 1 3 (Q t)) :
    FaceIdRayAQBd α cs cl (fun _ => True) (· ≠ 1) (· ≠ 0) Q := by
  have hz : ∀ (p : Fin 3 → Prop) [DecidablePred p] (x : Fin n → ℝ),
      (∀ i, 0 ≤ simplexPoint x i) → 0 ≤ ∑ u, if p (cl u) then simplexPoint x u else 0 :=
    fun p _ x hz => Finset.sum_nonneg fun u _ => by split_ifs <;> simp [hz u]
  constructor
  · obtain ⟨C, hC0, hC⟩ := faceIdRayAQ_unif (S := fun x : Fin n → ℝ =>
      (∀ i, 0 ≤ simplexPoint x i) ∧ 0 < symanzikU α (simplexPoint x))
      (f := fun t x => ‖faceIdRayAPTwo (Q t) α (fun i => cs i • majRayVec 1) x‖)
      (g := fun x => (∑ u, if (fun _ : Fin 3 => True) (cl u) then simplexPoint x u else 0) /
        symanzikU α (simplexPoint x) ^ 3) (fun t => by
          obtain ⟨C, hC0, hC⟩ := faceIdRayAQ_norm_two_le_all (Q t) α cl hα cs
          refine ⟨C, hC0, fun x hx => (hC x hx.1 hx.2).trans_eq ?_⟩
          simp only [ite_true]
          exact mul_div_assoc _ _ _)
      fun x hx => div_nonneg (hz (fun _ => True) x hx.1) (pow_pos hx.2 3).le
    exact ⟨C, hC0, fun x hx hU t => (hC x ⟨hx, hU⟩ t).trans_eq (mul_div_assoc _ _ _).symm⟩
  · obtain ⟨C, hC0, hC⟩ := faceIdRayAQ_unif (S := fun x : Fin n → ℝ =>
      (∀ i, 0 ≤ simplexPoint x i) ∧ 0 < symanzikU α (simplexPoint x))
      (f := fun t x => ‖faceIdRayAPThree (Q t) α x‖)
      (g := fun x => ((∑ u, if cl u ≠ 1 then simplexPoint x u else 0) *
        (∑ u, if cl u ≠ 0 then simplexPoint x u else 0)) /
          symanzikU α (simplexPoint x) ^ 4) (fun t => by
          obtain ⟨C, hC0, hC⟩ := faceIdRayAQ_norm_three_le_VB (Q t) α cl hα (hQ t).1 (hQ t).2
          exact ⟨C, hC0, fun x hx => (hC x hx.1 hx.2).trans_eq (mul_div_assoc _ _ _)⟩)
      fun x hx => div_nonneg (mul_nonneg (hz (· ≠ 1) x hx.1) (hz (· ≠ 0) x hx.1))
        (pow_pos hx.2 4).le
    exact ⟨C, hC0, fun x hx hU t => (hC x ⟨hx, hU⟩ t).trans_eq (mul_div_assoc _ _ _).symm⟩

end Bd

/-! ### The pieces -/

/-- The line classes of the piece with seven lines `(i, j)`. -/
def faceIdRayAQClA (clB : Fin 5 → Fin 3) (i j : Fin 4) (t : Fin 7) : Fin 3 :=
  clB (shA i j t.castSucc)

/-- The line classes of the piece with six lines `i`. -/
def faceIdRayAQClB (clB : Fin 5 → Fin 3) (i : Fin 4) (t : Fin 6) : Fin 3 :=
  clB (shB i t.castSucc)

/-- The top-monomial bound for the zero quartic. -/
theorem faceIdRayAQ_top_zero {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (cs : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Fin n → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) →
        ‖faceIdRayAPOne majZeroQ α (fun i => cs i • majRayVec 1) x‖ *
          (2 * Real.sqrt (simplexPoint x i * simplexPoint x j)) ≤
            K * remainder α (simplexPoint x) cs / symanzikU α (simplexPoint x) ^ 2 :=
  ⟨0, le_rfl, fun x _ _ => by simp [faceIdRayAPOne]⟩

theorem faceIdRayAQ_sq_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  pow_le_pow_left₀ ha h 2

section Pieces

variable (e : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l)) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (clB : Fin 5 → Fin 3) (hclB : ∀ r, base r = faceIdRayAQRowZ (clB r)) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (μ ν : Fin 4) {d₀ d₁ : ℕ} (K₂ K₁ K₃ : Fin 3 → Prop) [DecidablePred K₂] [DecidablePred K₁]
  [DecidablePred K₃]
  (hBd : ∀ {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (cl : Fin (n + 1) → Fin 3),
    (∀ t, α t = faceIdRayAQRow (cl t)) → ∀ (cs : Fin (n + 1) → ℝ) (Q : Fin 3 → LoopQuartic),
      (∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t)) → FaceIdRayAQBd α cs cl K₂ K₁ K₃ Q)

include hclB hm₀ hBd

include hA in
/-- **A piece with seven lines `(i, j)`.** -/
theorem faceIdRayAQ_pieceA (hd₀ : loopDegOf base 0 ≤ d₀) (hd₁ : loopDegOf base 1 ≤ d₁)
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (i j : Fin 4) (t₁ t₂ : Fin 7)
    (ht : t₁ ≠ t₂) (hcl : faceIdRayAQClA clB i j t₁ = faceIdRayAQClA clB i j t₂)
    (hcs : c (shA i j t₁.castSucc) ≠ c (shA i j t₂.castSucc)) (j' : Fin 7) (hj' : j' = 1 ∨ j' = 3)
    (c₁ : FaceIdRayAQCheck (faceIdRayAQClA clB i j) (Fin.last 6) t₁ t₂ 2 0)
    (c₂ : FaceIdRayAQCheck (faceIdRayAQClA clB i j) (Fin.last 6) t₁ t₂ 2
      fun t => (if t = 0 then -1 else 0) + (if t = j' then -1 else 0))
    (c₃ : ∀ u, K₂ (faceIdRayAQClA clB i j u) →
      FaceIdRayAQCheck (faceIdRayAQClA clB i j) (Fin.last 6) t₁ t₂ 3
        fun t => if t = u then 2 else 0)
    (c₄ : ∀ u v, K₁ (faceIdRayAQClA clB i j u) → K₃ (faceIdRayAQClA clB i j v) →
      FaceIdRayAQCheck (faceIdRayAQClA clB i j) (Fin.last 6) t₁ t₂ 4
        fun t => (if t = u then 2 else 0) + (if t = v then 2 else 0)) :
    FaceIdRayAQPow (faceIdRayAPieceA base c (vNum e 0 1 A base c) M X Y μ ν i j) := by
  set α := castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc) with hαdef
  set cl := faceIdRayAQClA clB i j with hcldef
  have hα : ∀ t, α t = faceIdRayAQRow (cl t) :=
    faceIdRayAQ_castLoopMatrix_row _ cl fun t => hclB _
  set cs : Fin 7 → ℝ := fun l => c (shA i j l.castSucc) with hcsdef
  set v := majRayVec 1 with hv
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  have hE := vNum_eq e 0 1 A base c hA
  have h0 : ∀ k ℓ, vNum e 0 1 A base c 0 k ℓ μ ν = vNumE0 e 0 1 A base c k ℓ μ ν :=
    fun k ℓ => by rw [hE]; simp
  -- the quartic of `E₀`
  obtain ⟨Q2, h20, h21, -, hQ2⟩ := faceIdRayAQ_exists_loopQuartic (n := 4) le_rfl
    ((isLoopPoly_vNum e 0 1 A base c 0 v μ ν).const_mul C)
    (((isLoopPolyDeg_vNum e 0 1 A base c 0 0 v μ ν).const_mul C).mono hd₀ le_rfl)
    (((isLoopPolyDeg_vNum e 0 1 A base c 1 0 v μ ν).const_mul C).mono hd₁ le_rfl)
  -- the quartic of `M² E₂`
  have e2 : (fun ℓ => C * (M : ℂ) ^ 2 * vNumE2 e 0 1 A base c v ℓ μ ν) = fun ℓ =>
      C * (M : ℂ) ^ 2 * (vNum e 0 1 A base c 1 v ℓ μ ν - vNum e 0 1 A base c 0 v ℓ μ ν -
        vNumE4 e 0 1 A v μ ν) :=
    funext fun ℓ => by rw [maj_vNumE2_eq e A hA base c μ ν]
  have hD1 : ∀ s : Fin 2, IsLoopPolyDeg s (loopDegOf base s) 4
      fun ℓ => C * (M : ℂ) ^ 2 * vNumE2 e 0 1 A base c v ℓ μ ν := fun s => by
    rw [e2]
    exact (((isLoopPolyDeg_vNum e 0 1 A base c s 1 v μ ν).sub
      (isLoopPolyDeg_vNum e 0 1 A base c s 0 v μ ν)).sub (IsLoopPolyDeg.const _)).const_mul _
  obtain ⟨Q1, h10, h11, -, hQ1⟩ := faceIdRayAQ_exists_loopQuartic (n := 4) le_rfl
    (((isLoopPoly_vNumE2 e 0 1 A base c v μ ν).const_mul (C * (M : ℂ) ^ 2)).mono
      (by norm_num)) ((hD1 0).mono hd₀ le_rfl) ((hD1 1).mono hd₁ le_rfl)
  -- the constant quartic
  obtain ⟨Q0, h00, h01, -, hQ0⟩ := faceIdRayAQ_exists_loopQuartic (n := 0) (by norm_num)
    (IsLoopPoly.const (C * ((M : ℂ) ^ 2) ^ 2 * vNumE4 e 0 1 A v μ ν))
    (IsLoopPolyDeg.const (d := d₀) (C * ((M : ℂ) ^ 2) ^ 2 * vNumE4 e 0 1 A v μ ν))
    (IsLoopPolyDeg.const (d := d₁) (C * ((M : ℂ) ^ 2) ^ 2 * vNumE4 e 0 1 A v μ ν))
  set Q : Fin 3 → LoopQuartic := ![Q0, Q1, Q2] with hQ
  have hdeg : ∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t) := fun t => by
    fin_cases t
    exacts [⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩]
  have hBdQ := hBd α cl hα cs Q hdeg
  -- the top monomial
  have hTop : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Fin 6 → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) →
        ‖faceIdRayAPOne (Q 2) α (fun i => cs i • majRayVec 1) x‖ *
          (2 * Real.sqrt (simplexPoint x 0 * simplexPoint x j')) ≤
            K * remainder α (simplexPoint x) cs / symanzikU α (simplexPoint x) ^ 2 := by
    obtain ⟨Cτ, hCτ0, hCτ⟩ := maj_exists_abs_flow_le α cs
    set E0 : ℂ := ∑ ρ, ∑ σ, kV e 0 1 ρ σ * vE0 (A μ ν ρ σ) (fun _ => v) with hE0
    refine ⟨‖C‖ * ‖E0‖ * Cτ ^ 2, by positivity, fun x hz hUp => ?_⟩
    set z := simplexPoint x with hzd
    set τ := majFlow α z cs with hτ
    have hU0 : symanzikU α z ≠ 0 := hUp.ne'
    have hfl : ∀ l : Fin 4, fm base (ppc c v) l (-loopShift α (fun l => cs l • v) z) =
        (![τ 0, τ 1, τ 2, τ 3] l) • v := by
      intro l
      fin_cases l
      · exact maj_fm_shift base c (fun l : Fin 7 => shA i j l.castSucc) z v (l' := 0) rfl
      · exact maj_fm_shift base c (fun l : Fin 7 => shA i j l.castSucc) z v (l' := 1) rfl
      · exact maj_fm_shift base c (fun l : Fin 7 => shA i j l.castSucc) z v (l' := 2) rfl
      · exact maj_fm_shift base c (fun l : Fin 7 => shA i j l.castSucc) z v (l' := 3) rfl
    have hval : (Q 2).eval (-loopShift α (fun l => cs l • v) z) =
        C * (((τ 0 * τ 1 * τ 2 * τ 3 : ℝ)) : ℂ) * E0 := by
      show Q2.eval _ = _
      rw [hQ2]
      dsimp only
      rw [h0, maj_vNumE0_flow base c e 0 1 A v _ _ hfl μ ν]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hE0]
      push_cast
      ring
    have hprod : |τ 0 * τ 1 * τ 2 * τ 3| * (2 * Real.sqrt (z 0 * z j')) ≤
        Cτ ^ 2 * remainder α z cs := by
      have hw : 0 ≤ 2 * Real.sqrt (z 0 * z j') := by positivity
      rcases hj' with rfl | rfl
      · refine maj_abs_four_le hw hCτ0 ?_ (hCτ z hz hU0 2) (hCτ z hz hU0 3)
        exact maj_abs_flow_mul_le α hz hU0 cs (show (0 : Fin 7) ≠ 1 by decide)
      · rw [show τ 0 * τ 1 * τ 2 * τ 3 = τ 0 * τ 3 * τ 1 * τ 2 by ring]
        refine maj_abs_four_le hw hCτ0 ?_ (hCτ z hz hU0 1) (hCτ z hz hU0 2)
        exact maj_abs_flow_mul_le α hz hU0 cs (show (0 : Fin 7) ≠ 3 by decide)
    have hUp2 : 0 < symanzikU α z ^ 2 := pow_pos hUp 2
    have hone : faceIdRayAPOne (Q 2) α (fun i => cs i • majRayVec 1) x =
        ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ * (Q 2).eval (-loopShift α (fun l => cs l • v) z) :=
      rfl
    rw [hone, hval, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hUp2,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc (symanzikU α z ^ 2)⁻¹ * (‖C‖ * |τ 0 * τ 1 * τ 2 * τ 3| * ‖E0‖) *
          (2 * Real.sqrt (z 0 * z j'))
        = ‖C‖ * ‖E0‖ * (symanzikU α z ^ 2)⁻¹ * (|τ 0 * τ 1 * τ 2 * τ 3| *
          (2 * Real.sqrt (z 0 * z j'))) := by ring
      _ ≤ ‖C‖ * ‖E0‖ * (symanzikU α z ^ 2)⁻¹ * (Cτ ^ 2 * remainder α z cs) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by rw [div_eq_mul_inv]; ring
  -- the numerator along the ray
  have hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, C * vNum e 0 1 A base c M (r • majRayVec 1) ℓ μ ν =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ) := by
    intro r hr ℓ
    have hr0 : r ≠ 0 := by positivity
    rw [hE, Fin.sum_univ_three]
    simp only [hQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hQ0, hQ1, hQ2, Fin.val_zero, Fin.val_one, Fin.val_two,
      h0, maj_vNumE0_smul base c e 0 1 A (majRayVec 1) ℓ hr0,
      maj_vNumE2_smul base c e 0 1 A (majRayVec 1) ℓ hr0, vNumE4]
    ring
  have hMv : ∀ l : Fin 7, l ≠ Fin.last 6 → m₀ ^ 2 ≤
      (![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0] : Fin 7 → ℝ)
        l ^ 2 := by
    have hmA : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> assumption
    intro l hl
    fin_cases l
    · exact faceIdRayAQ_sq_le hm₀.le (hmA 0)
    · exact faceIdRayAQ_sq_le hm₀.le (hmA 1)
    · exact faceIdRayAQ_sq_le hm₀.le (hmA 2)
    · exact faceIdRayAQ_sq_le hm₀.le (hmA 3)
    · exact faceIdRayAQ_sq_le hm₀.le hX
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact absurd rfl hl
  exact faceIdRayAQ_pow_pairDens (by norm_num) α cs _ (Fin.last 6) hm₀ hMv
    (fun k ℓ => C * vNum e 0 1 A base c M k ℓ μ ν) Q hN (Or.inl le_rfl)
    (faceIdRayAQ_hMaj α cl hα cs (Fin.last 6) t₁ t₂ 0 j' ht hcl hcs Q (fun u => K₂ (cl u))
      (fun u => K₁ (cl u)) (fun u => K₃ (cl u)) hBdQ.1 hBdQ.2 hTop c₁ c₂ c₃ c₄)

include hA in
/-- **A piece with six lines `i`.** -/
theorem faceIdRayAQ_pieceB (hd₀ : loopDegOf base 0 ≤ d₀) (hd₁ : loopDegOf base 1 ≤ d₁)
    {M X Y : ℝ} (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (i : Fin 4) (t₁ t₂ : Fin 6)
    (ht : t₁ ≠ t₂) (hcl : faceIdRayAQClB clB i t₁ = faceIdRayAQClB clB i t₂)
    (hcs : c (shB i t₁.castSucc) ≠ c (shB i t₂.castSucc)) (j' : Fin 6)
    (c₁ : FaceIdRayAQCheck (faceIdRayAQClB clB i) (Fin.last 5) t₁ t₂ 2 0)
    (c₂ : FaceIdRayAQCheck (faceIdRayAQClB clB i) (Fin.last 5) t₁ t₂ 2
      fun t => (if t = 0 then -1 else 0) + (if t = j' then -1 else 0))
    (c₃ : ∀ u, K₂ (faceIdRayAQClB clB i u) →
      FaceIdRayAQCheck (faceIdRayAQClB clB i) (Fin.last 5) t₁ t₂ 3
        fun t => if t = u then 2 else 0)
    (c₄ : ∀ u v, K₁ (faceIdRayAQClB clB i u) → K₃ (faceIdRayAQClB clB i v) →
      FaceIdRayAQCheck (faceIdRayAQClB clB i) (Fin.last 5) t₁ t₂ 4
        fun t => (if t = u then 2 else 0) + (if t = v then 2 else 0)) :
    FaceIdRayAQPow (faceIdRayAPieceB base c (vNum e 0 1 A base c) M X Y μ ν i) := by
  set α := castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc) with hαdef
  set cl := faceIdRayAQClB clB i with hcldef
  have hα : ∀ t, α t = faceIdRayAQRow (cl t) :=
    faceIdRayAQ_castLoopMatrix_row _ cl fun t => hclB _
  set cs : Fin 6 → ℝ := fun l => c (shB i l.castSucc) with hcsdef
  set v := majRayVec 1 with hv
  set K' : ℂ := -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) with hK'
  have hE := vNum_eq e 0 1 A base c hA
  have e2 : (fun ℓ => K' * vNumE2 e 0 1 A base c v ℓ μ ν) = fun ℓ =>
      K' * (vNum e 0 1 A base c 1 v ℓ μ ν - vNum e 0 1 A base c 0 v ℓ μ ν -
        vNumE4 e 0 1 A v μ ν) :=
    funext fun ℓ => by rw [maj_vNumE2_eq e A hA base c μ ν]
  have hD1 : ∀ s : Fin 2, IsLoopPolyDeg s (loopDegOf base s) 4
      fun ℓ => K' * vNumE2 e 0 1 A base c v ℓ μ ν := fun s => by
    rw [e2]
    exact (((isLoopPolyDeg_vNum e 0 1 A base c s 1 v μ ν).sub
      (isLoopPolyDeg_vNum e 0 1 A base c s 0 v μ ν)).sub (IsLoopPolyDeg.const _)).const_mul _
  obtain ⟨Q1, h10, h11, hq1, hQ1⟩ := faceIdRayAQ_exists_loopQuartic (n := 2) (by norm_num)
    ((isLoopPoly_vNumE2 e 0 1 A base c v μ ν).const_mul K') ((hD1 0).mono hd₀ le_rfl)
    ((hD1 1).mono hd₁ le_rfl)
  set d : ℂ := K' * (((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * vNumE4 e 0 1 A v μ ν) with hd
  obtain ⟨Q0, h00, h01, hq0, hQ0⟩ := faceIdRayAQ_exists_loopQuartic (n := 0) (by norm_num)
    (IsLoopPoly.const d) (IsLoopPolyDeg.const (d := d₀) d) (IsLoopPolyDeg.const (d := d₁) d)
  set Q : Fin 3 → LoopQuartic := ![Q0, Q1, majZeroQ] with hQ
  have hdeg : ∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t) := fun t => by
    fin_cases t
    exacts [⟨h00, h01⟩, ⟨h10, h11⟩, ⟨LoopDegLe.zero, LoopDegLe.zero⟩]
  have hBdQ := hBd α cl hα cs Q hdeg
  have hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (vNum e 0 1 A base c X (r • majRayVec 1) ℓ μ ν -
        vNum e 0 1 A base c M (r • majRayVec 1) ℓ μ ν) =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ) := by
    intro r hr ℓ
    have hr0 : r ≠ 0 := by positivity
    rw [hE, hE, maj_vNumE2_smul base c e 0 1 A (majRayVec 1) ℓ hr0, Fin.sum_univ_three]
    simp only [hQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hQ0, hQ1, majZeroQ_eval, Fin.val_zero, Fin.val_one,
      Fin.val_two, vNumE4, hd, hK']
    ring
  have hMv : ∀ l : Fin 6, l ≠ Fin.last 5 → m₀ ^ 2 ≤
      (![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] : Fin 6 → ℝ) l ^ 2 := by
    have hmB : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> assumption
    intro l hl
    fin_cases l
    · exact faceIdRayAQ_sq_le hm₀.le (hmB 0)
    · exact faceIdRayAQ_sq_le hm₀.le (hmB 1)
    · exact faceIdRayAQ_sq_le hm₀.le (hmB 2)
    · exact faceIdRayAQ_sq_le hm₀.le (hmB 3)
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact absurd rfl hl
  exact faceIdRayAQ_pow_pairDens (by norm_num) α cs _ (Fin.last 5) hm₀ hMv
    (fun k ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (vNum e 0 1 A base c X k ℓ μ ν - vNum e 0 1 A base c M k ℓ μ ν)) Q hN
    (Or.inr fun t => by fin_cases t; exacts [hq0 (by norm_num), hq1 (by norm_num), rfl])
    (faceIdRayAQ_hMaj α cl hα cs (Fin.last 5) t₁ t₂ 0 j' ht hcl hcs Q (fun u => K₂ (cl u))
      (fun u => K₁ (cl u)) (fun u => K₃ (cl u)) hBdQ.1 hBdQ.2
      (faceIdRayAQ_top_zero α cs 0 j') c₁ c₂ c₃ c₄)

/-- **The padded piece.** -/
theorem faceIdRayAQ_pieceP (hd₀ : 2 ≤ d₀) (hb0 : base (0 : Fin 4).castSucc = ![1, 0])
    {M X Y : ℝ} (hY : m₀ ≤ Y) (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hE4 : ∀ k, E4 k μ ν = E4 (majRayVec 1) μ ν) (t₁ t₂ : Fin 6)
    (ht : t₁ ≠ t₂) (hcl : faceIdRayAQClB clB 0 t₁ = faceIdRayAQClB clB 0 t₂)
    (hcs : c (shB 0 t₁.castSucc) ≠ c (shB 0 t₂.castSucc)) (j' : Fin 6)
    (c₁ : FaceIdRayAQCheck (faceIdRayAQClB clB 0) (Fin.last 5) t₁ t₂ 2 0)
    (c₂ : FaceIdRayAQCheck (faceIdRayAQClB clB 0) (Fin.last 5) t₁ t₂ 2
      fun t => (if t = 0 then -1 else 0) + (if t = j' then -1 else 0))
    (c₃ : ∀ u, K₂ (faceIdRayAQClB clB 0 u) →
      FaceIdRayAQCheck (faceIdRayAQClB clB 0) (Fin.last 5) t₁ t₂ 3
        fun t => if t = u then 2 else 0)
    (c₄ : ∀ u v, K₁ (faceIdRayAQClB clB 0 u) → K₃ (faceIdRayAQClB clB 0 v) →
      FaceIdRayAQCheck (faceIdRayAQClB clB 0) (Fin.last 5) t₁ t₂ 4
        fun t => (if t = u then 2 else 0) + (if t = v then 2 else 0)) :
    FaceIdRayAQPow (faceIdRayAPieceP base c E4 M X Y μ ν) := by
  set α := castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc) with hαdef
  set cl := faceIdRayAQClB clB 0 with hcldef
  have hα : ∀ t, α t = faceIdRayAQRow (cl t) :=
    faceIdRayAQ_castLoopMatrix_row _ cl fun t => hclB _
  set cs : Fin 6 → ℝ := fun l => c (shB 0 l.castSucc) with hcsdef
  set v := majRayVec 1 with hv
  set D : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 v μ ν with hD
  set a := castLoopMatrix base (0 : Fin 4).castSucc with ha
  obtain ⟨ha1, ha0⟩ := affDeg_row10 base _ hb0
  have hD1 : ∀ s : Fin 2, IsLoopPolyDeg s (affDeg s a + affDeg s a) 2
      fun ℓ => D * (propDenom Y 0 (fm base (ppc c v) 0 ℓ) - (Y : ℂ) ^ 2) := fun s => by
    have e : (fun ℓ => D * (propDenom Y 0 (fm base (ppc c v) 0 ℓ) - (Y : ℂ) ^ 2)) =
        fun ℓ => D * (propDenom Y 0 (∑ r, a r • ℓ r + ppc c v (0 : Fin 4).castSucc) -
          (Y : ℂ) ^ 2) := by
      funext ℓ; rw [fm_eq_affine]
    rw [e]
    exact ((isLoopPolyDeg_propDenom_affine s a _ Y 0).sub (IsLoopPolyDeg.const _)).const_mul D
  obtain ⟨Q1, h10, h11, hq1, hQ1⟩ := faceIdRayAQ_exists_loopQuartic (n := 2) (by norm_num)
    (hD1 0).isLoopPoly ((hD1 0).mono (d' := d₀) (n' := 4) (by rw [ha0]; exact hd₀) (by norm_num))
    ((hD1 1).mono (d' := d₁) (n' := 4) (by rw [ha1]; exact Nat.zero_le _) (by norm_num))
  set d : ℂ := D * (Y : ℂ) ^ 2 with hd
  obtain ⟨Q0, h00, h01, hq0, hQ0⟩ := faceIdRayAQ_exists_loopQuartic (n := 0) (by norm_num)
    (IsLoopPoly.const d) (IsLoopPolyDeg.const (d := d₀) d) (IsLoopPolyDeg.const (d := d₁) d)
  set Q : Fin 3 → LoopQuartic := ![Q0, Q1, majZeroQ] with hQ
  have hdeg : ∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t) := fun t => by
    fin_cases t
    exacts [⟨h00, h01⟩, ⟨h10, h11⟩, ⟨LoopDegLe.zero, LoopDegLe.zero⟩]
  have hBdQ := hBd α cl hα cs Q hdeg
  have hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      E4 (r • majRayVec 1) μ ν * propDenom Y 0 (fm base (ppc c (r • majRayVec 1)) 0 ℓ) =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ) := by
    intro r hr ℓ
    have hr0 : r ≠ 0 := by positivity
    rw [maj_fm_smul base c (majRayVec 1) 0 ℓ hr0, hE4, Fin.sum_univ_three]
    simp only [hQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hQ0, hQ1, majZeroQ_eval, Fin.val_zero, Fin.val_one,
      Fin.val_two, hd, hD, propDenom, Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hMv : ∀ l : Fin 6, l ≠ Fin.last 5 → m₀ ^ 2 ≤ (![Y, Y, Y, Y, Y, 0] : Fin 6 → ℝ) l ^ 2 := by
    intro l hl
    fin_cases l
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact absurd rfl hl
  exact faceIdRayAQ_pow_pairDens (by norm_num) α cs _ (Fin.last 5) hm₀ hMv
    (fun k ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k μ ν *
      propDenom Y 0 (fm base (ppc c k) 0 ℓ)) Q hN
    (Or.inr fun t => by fin_cases t; exacts [hq0 (by norm_num), hq1 (by norm_num), rfl])
    (faceIdRayAQ_hMaj α cl hα cs (Fin.last 5) t₁ t₂ 0 j' ht hcl hcs Q (fun u => K₂ (cl u))
      (fun u => K₁ (cl u)) (fun u => K₃ (cl u)) hBdQ.1 hBdQ.2
      (faceIdRayAQ_top_zero α cs 0 j') c₁ c₂ c₃ c₄)

end Pieces

end QED.GradedProof.RPi4

end
