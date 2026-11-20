/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountDysonAlg
public import QED.GradedProof.X1CStatement
public import QED.GradedProof.X1CCountSum
public import QED.GradedProof.X1CT9Glue

/-!
# (X₁) piece C: the three peels as matrix identities

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (assembly into `DysonFive`).

* `countDyson_onePIPart_eq_zero`: a 1PI part with an even number of external photons and some
  external vanishes at odd or zero graded order (`t9_two_le_gradedOrder`).
* `countDysonSel` (selected `(1,1)` part at `(r', r, r' - r)` as a spinor matrix),
  `countDysonX` (`S̃(r) (1/i) onePIPart(1,0)_K(r)`), `countDysonY` (`(1/i) onePIPart(1,0)_K(r')
  S̃(r')`), `countDysonQ` (`∑_ρ Δ̃_{νρ}(q) (1/i) onePIPart(0,2)_K(q; μ, ρ)`); they vanish at
  `K ∈ {0, 1, 3, 5}` (`countDysonX_eq_zero`, …).
* `countDyson_inLeg`, `countDyson_outLeg`, `countDyson_photonLeg`, `countDyson_vertexPart`: the
  chains and the vertex part of `dysonFive` in these terms.
* `countDyson_matIn`, `countDyson_matOut`, `countDyson_matP`: the value-level peels
  (`selectedPart_peelIn`, `selectedPart_peelOut`, `selectedPart_peelP` at `q = r' - r`) as the
  matrix recursions consumed by `countDyson_unwind`.
* `countDyson_selectedPart_congr`: selected parts agree for selections that agree at the order.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction IsOnePI)
open QED.Graded
open Complex

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **1PI parts of odd or zero graded order vanish** (with an even number of external photons
and some external). -/
theorem countDyson_onePIPart_eq_zero {nf nA K : ℕ} (h : 2 ∣ nA) (hpos : 0 < nf ∨ 0 < nA)
    (hK : ¬ (2 ≤ K ∧ 2 ∣ K)) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    onePIPart P Φ D nf nA K pOut pIn kIn αOut βIn μ = 0 := by
  unfold onePIPart selectedPart
  refine sum_eq_zero fun N _ => mul_eq_zero_of_right _ (sum_eq_zero fun κ _ =>
    sum_eq_zero fun g hg => sum_eq_zero fun C hC => ?_)
  exfalso
  have hg' := (Finset.mem_filter.1 hg).2
  have hC' : IsOnePI C := by
    classical
    exact (Finset.mem_filter.1 hC).2
  exact hK (hg' ▸ t9_two_le_gradedOrder C h (t9_pos_of_isOnePI C hC' hpos) g)

theorem countDyson_ne {K : ℕ} (hK : K ≤ 5) (h2 : K ≠ 2) (h4 : K ≠ 4) : ¬ (2 ≤ K ∧ 2 ∣ K) := by
  rintro ⟨h, k, rfl⟩
  omega

/-- The matrix (spinor indices) of a selected `(1,1)` part at `(r', r, r' - r)`. -/
noncomputable def countDysonSel (Sel : CountSel 1 1) (r' r : Fin 4 → ℝ) (K : ℕ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => selectedPart P Φ D 1 1 Sel K ![r'] ![r] ![r' - r] ![α] ![β] ![μ]

/-- The in-leg insertion `S̃(r) · (1/i) onePIPart(1,0)_K(r)`. -/
noncomputable def countDysonX (r : Fin 4 → ℝ) (K : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  openProp P Φ r * Matrix.of fun δ β => (1 / I) * onePIPart P Φ D 1 0 K ![r] ![r] ![] ![δ] ![β] ![]

/-- The out-leg insertion `(1/i) onePIPart(1,0)_K(r') · S̃(r')`. -/
noncomputable def countDysonY (r' : Fin 4 → ℝ) (K : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Matrix.of fun α γ => (1 / I) * onePIPart P Φ D 1 0 K ![r'] ![r'] ![] ![α] ![γ] ![]) *
    openProp P Φ r'

/-- The photon-leg insertion `∑_ρ D̃_{νρ}(q) (1/i) onePIPart(0,2)_K(q; μ, ρ)`. -/
noncomputable def countDysonQ (q : Fin 4 → ℝ) (K : ℕ) (ν μ : Fin 4) : ℂ :=
  ∑ ρ, photonProp P q ν ρ * ((1 / I) * onePIPart P Φ D 0 2 K ![] ![] ![q, -q] ![] ![] ![μ, ρ])

theorem countDysonX_eq_zero (r : Fin 4 → ℝ) {K : ℕ} (hK : K ≤ 5) (h2 : K ≠ 2) (h4 : K ≠ 4) :
    countDysonX P Φ D r K = 0 := by
  have h0 : (Matrix.of fun δ β => (1 / I) * onePIPart P Φ D 1 0 K ![r] ![r] ![] ![δ] ![β] ![] :
      Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
    ext δ β
    rw [Matrix.of_apply, countDyson_onePIPart_eq_zero P Φ D (by norm_num) (.inl one_pos)
      (countDyson_ne hK h2 h4), mul_zero, Matrix.zero_apply]
  rw [countDysonX, h0, Matrix.mul_zero]

theorem countDysonY_eq_zero (r' : Fin 4 → ℝ) {K : ℕ} (hK : K ≤ 5) (h2 : K ≠ 2) (h4 : K ≠ 4) :
    countDysonY P Φ D r' K = 0 := by
  have h0 : (Matrix.of fun α γ => (1 / I) * onePIPart P Φ D 1 0 K ![r'] ![r'] ![] ![α] ![γ] ![] :
      Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
    ext δ β
    rw [Matrix.of_apply, countDyson_onePIPart_eq_zero P Φ D (by norm_num) (.inl one_pos)
      (countDyson_ne hK h2 h4), mul_zero, Matrix.zero_apply]
  rw [countDysonY, h0, Matrix.zero_mul]

theorem countDysonQ_eq_zero (q : Fin 4 → ℝ) {K : ℕ} (hK : K ≤ 5) (h2 : K ≠ 2) (h4 : K ≠ 4) :
    countDysonQ P Φ D q K = 0 := by
  funext ν μ
  refine sum_eq_zero fun ρ _ => ?_
  rw [countDyson_onePIPart_eq_zero P Φ D (by norm_num) (.inr two_pos) (countDyson_ne hK h2 h4),
    mul_zero, mul_zero]

/-! ### The chains -/

theorem countDyson_inLeg (r : Fin 4 → ℝ) (c : ℕ) :
    inLeg P Φ D c r = countDysonLeg (countDysonX P Φ D r) c := by
  rcases c with _ | _ | _ | c <;> rfl

theorem countDyson_outLeg (r' : Fin 4 → ℝ) (a : ℕ) :
    outLeg P Φ D a r' = countDysonLeg (countDysonY P Φ D r') a := by
  rcases a with _ | _ | _ | a <;> rfl

theorem countDyson_photonLeg (q : Fin 4 → ℝ) (d : ℕ) (ν μ : Fin 4) :
    photonLeg P Φ D d q ν μ = countDysonPLeg (countDysonQ P Φ D q) d ν μ := by
  rcases d with _ | _ | _ | d
  · rfl
  · rfl
  · change _ + _ = _ + _
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [countDysonQ, countDysonQ, sum_mul_sum]
    rfl
  · rfl

theorem countDyson_fun_eq {X : Type*} (x : X) : (fun _ : Fin 1 => x) = ![x] := by
  funext i
  fin_cases i
  rfl

theorem countDyson_vertexPart (r' r : Fin 4 → ℝ) (b : ℕ) (ν : Fin 4) :
    vertexPart P Φ D Φ.openLine b r' r ν =
      (1 / I) • countDysonSel P Φ D (fun C _ => IsOnePI C) r' r (2 * b + 1) ν := by
  ext α β
  simp only [vertexPart, countDysonSel, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    countDyson_fun_eq]
  rfl

theorem countDyson_matIn (SelG SelH : CountSel 1 1) (r' r : Fin 4 → ℝ) (K : ℕ)
    (hI : ∀ (αOut βIn μ : Fin 1 → Fin 4),
      selectedPart P Φ D 1 1 SelG K ![r'] ![r] ![r' - r] αOut βIn μ =
        selectedPart P Φ D 1 1 SelH K ![r'] ![r] ![r' - r] αOut βIn μ +
        ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
          selectedPart P Φ D 1 1 SelG p.1 ![r'] ![r] ![r' - r] αOut ![γ] μ *
            ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ) *
            onePIPart P Φ D 1 0 p.2 ![r] ![r] ![] ![δ] βIn ![]) (μ : Fin 4) :
    countDysonSel P Φ D SelG r' r K μ = countDysonSel P Φ D SelH r' r K μ +
      ∑ p ∈ antidiagonal K, countDysonSel P Φ D SelG r' r p.1 μ * countDysonX P Φ D r p.2 := by
  ext α β
  rw [Matrix.add_apply, Matrix.sum_apply, countDysonSel, countDysonSel, Matrix.of_apply,
    Matrix.of_apply, hI]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_apply]
  refine sum_congr rfl fun γ _ => ?_
  rw [countDysonX, Matrix.mul_apply, mul_sum, countDysonSel, Matrix.of_apply]
  refine sum_congr rfl fun δ _ => ?_
  rw [Matrix.of_apply, openProp]
  ring

theorem countDyson_matOut (SelH SelJ : CountSel 1 1) (r' r : Fin 4 → ℝ) (K : ℕ)
    (hO : ∀ (αOut βIn μ : Fin 1 → Fin 4),
      selectedPart P Φ D 1 1 SelH K ![r'] ![r] ![r' - r] αOut βIn μ =
        selectedPart P Φ D 1 1 SelJ K ![r'] ![r] ![r' - r] αOut βIn μ +
        ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
          onePIPart P Φ D 1 0 p.2 ![r'] ![r'] ![] αOut ![γ] ![] *
            ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' γ δ) *
            selectedPart P Φ D 1 1 SelH p.1 ![r'] ![r] ![r' - r] ![δ] βIn μ) (μ : Fin 4) :
    countDysonSel P Φ D SelH r' r K μ = countDysonSel P Φ D SelJ r' r K μ +
      ∑ p ∈ antidiagonal K, countDysonY P Φ D r' p.2 * countDysonSel P Φ D SelH r' r p.1 μ := by
  ext α β
  rw [Matrix.add_apply, Matrix.sum_apply, countDysonSel, countDysonSel, Matrix.of_apply,
    Matrix.of_apply, hO]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_apply, countDysonY]
  simp only [Matrix.mul_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun γ _ => sum_congr rfl fun δ _ => ?_
  rw [countDysonSel, Matrix.of_apply, Matrix.of_apply, openProp]
  ring

theorem countDyson_matP (SelJ SelV : CountSel 1 1) (r' r : Fin 4 → ℝ) (K : ℕ)
    (hP : ∀ (αOut βIn μ : Fin 1 → Fin 4),
      selectedPart P Φ D 1 1 SelJ K ![r'] ![r] ![r' - r] αOut βIn μ =
        selectedPart P Φ D 1 1 SelV K ![r'] ![r] ![r' - r] αOut βIn μ +
        ∑ p ∈ antidiagonal K, ∑ ν, ∑ ρ,
          selectedPart P Φ D 1 1 SelJ p.1 ![r'] ![r] ![r' - r] αOut βIn ![ν] *
            ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (r' - r) ν ρ) *
            onePIPart P Φ D 0 2 p.2 ![] ![] ![r' - r, -(r' - r)] ![] ![] ![μ 0, ρ])
    (μ : Fin 4) :
    countDysonSel P Φ D SelJ r' r K μ = countDysonSel P Φ D SelV r' r K μ +
      ∑ p ∈ antidiagonal K, ∑ ν, countDysonQ P Φ D (r' - r) p.2 ν μ •
        countDysonSel P Φ D SelJ r' r p.1 ν := by
  ext α β
  rw [Matrix.add_apply, Matrix.sum_apply, countDysonSel, countDysonSel, Matrix.of_apply,
    Matrix.of_apply, hP]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [Matrix.sum_apply]
  refine sum_congr rfl fun ν _ => ?_
  rw [Matrix.smul_apply, countDysonQ, smul_eq_mul, sum_mul, countDysonSel, Matrix.of_apply]
  refine sum_congr rfl fun ρ _ => ?_
  rw [photonProp]
  simp only [Matrix.cons_val_zero]
  ring


/-- Selected parts agree for selections that agree at the graded order. -/
theorem countDyson_selectedPart_congr {nf nA : ℕ} (Sel Sel' : CountSel nf nA) (K : ℕ)
    (h : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (g : Grading κ),
      gradedOrder κ g = K → (Sel C g ↔ Sel' C g))
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ =
      selectedPart P Φ D nf nA Sel' K pOut pIn kIn αOut βIn μ := by
  simp only [selectedPart_eq_countSum, countSum]
  refine sum_congr rfl fun N _ => congrArg _ (sum_congr rfl fun κ _ =>
    sum_congr rfl fun g hg => sum_congr ?_ fun _ _ => rfl)
  ext C
  rw [mem_countSel, mem_countSel]
  exact h C g (mem_countGr.1 hg)

end QED.GradedProof.X1C

end
