/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassC
public import QED.GradedProof.SE2SEChain

/-!
# The classes `P0`, `P1`: the one-loop self-energy with a `δ₃` insertion

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2. The representatives `repP0`, `repP1` of
`QED/GradedProof/SE2Classes.lean` have two `gauge` vertices `0` (incoming) and `1` (outgoing),
the `photonCt` vertex `2`, one internal electron line `0 → 1` and the photon lines `0 — 2`,
`1 — 2` (slots `2₀`, `2₁` in `P0`, swapped in `P1`). For each:

* the lines, their ends, the unique chord (T₁) and an explicit conserved routing (`decide +kernel`);
* the amplitude (T₇) at arbitrary line momenta (`p0_amplitude`, `p1_amplitude`);
* `(2π)⁻⁴` times the regulated amplitude (T₈) in the routing is `κ` times the self-energy chain
  of `S̃(p + q)` with the inserted photon factor `photonInsertion` at `q = ℓ - p`
  (`p0_integrand`, `p1_integrand`);
* the class obligation `ClassInt` (`classInt_repP0`, `classInt_repP1`), from
  `QED.GradedProof.SE2.energyFirst_seP`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel
open Complex MeasureTheory

/-- The constant `(ie)² (1/i)² (2π)⁻⁴` of a one-loop self-energy integrand. -/
noncomputable def kappaSE (e : ℝ) : ℂ :=
  (I * e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

/-! ### `P0` -/

section P0

/-- The electron line `0 → 1` of `repP0`. -/
def p0f : FermionLine repP0 := ⟨fvK k_ggp 1, by decide +kernel⟩
/-- The photon line `0 → 2₀` of `repP0`. -/
def p0gA : PhotonLine repP0 := ⟨psK k_ggp 0 0, by decide +kernel⟩
/-- The photon line `1 → 2₁` of `repP0`. -/
def p0gB : PhotonLine repP0 := ⟨psK k_ggp 1 0, by decide +kernel⟩

theorem p0_fermionLine_cases : ∀ f : FermionLine repP0, f = p0f := by decide +kernel

theorem p0_photonLine_cases : ∀ g : PhotonLine repP0, g = p0gA ∨ g = p0gB := by decide +kernel

theorem p0_line_cases : ∀ f : Line repP0, f = .inl p0f ∨ f = .inr p0gA ∨ f = .inr p0gB := by
  decide +kernel

theorem p0_isChord_iff : ∀ g : Line repP0, IsChord g ↔ g = .inl p0f := by decide +kernel

theorem p0_ends : (Line.ends (.inl p0f : Line repP0)) = (0, 1) ∧
    (Line.ends (.inr p0gA : Line repP0)) = (0, 2) ∧
    (Line.ends (.inr p0gB : Line repP0)) = (1, 2) := by
  decide +kernel

theorem p0_tails : p0f.tail = fvK k_ggp 0 ∧ p0gA.head = psK k_ggp 2 0 ∧
    p0gB.head = psK k_ggp 2 1 := by
  decide +kernel

theorem p0_ext (v : Fin 3) :
    ((∃ t : Wick.FermionVertex k_ggp, t.1 = v ∧ repP0.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ t : Wick.FermionVertex k_ggp, t.1 = v ∧ repP0.1.1 (.inl 0) = .inr t) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repP0`: `ℓ` on the electron line, `p - ℓ` on `0 → 2`, `ℓ - p` on `1 → 2`. -/
def p0Mom (p ℓ : Fin 4 → ℝ) (f : Line repP0) : Fin 4 → ℝ :=
  if f = .inl p0f then ℓ else if f = .inr p0gA then p - ℓ else ℓ - p

theorem p0Mom_apply (p ℓ : Fin 4 → ℝ) : p0Mom p ℓ (.inl p0f) = ℓ ∧
    p0Mom p ℓ (.inr p0gA) = p - ℓ ∧ p0Mom p ℓ (.inr p0gB) = ℓ - p := by
  refine ⟨ite_eq_left rfl, ?_, ?_⟩
  · rw [p0Mom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [p0Mom, ite_eq_right (by decide), ite_eq_right (by decide)]

theorem p0_isConserved (p ℓ : Fin 4 → ℝ) : IsConserved repP0 ![p] ![p] ![] (p0Mom p ℓ) := by
  obtain ⟨e1, e2, e3⟩ := p0_ends
  obtain ⟨m1, m2, m3⟩ := p0Mom_apply p ℓ
  intro v
  rw [inflow, sum_eq_of_three (by decide) (by decide) (by decide) p0_line_cases,
    externalMomentum_one_zero]
  obtain ⟨x1, x2⟩ := p0_ext v
  simp only [e1, e2, e3, x1, x2, m1, m2, m3, Matrix.cons_val_zero]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem p0_cond (α β : Wick.FermionVertex k_ggp → Fin 4) (lor : Wick.PhotonSlot k_ggp → Fin 4)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    ((∀ i t, repP0.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repP0.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repP0.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (α (fvK k_ggp 1) = αOut 0 ∧ β (fvK k_ggp 0) = βIn 0) := by
  have h1 : ∀ t, repP0.1.1 (.inl 0) = .inr t ↔ t = fvK k_ggp 1 := by decide +kernel
  have h2 : ∀ t, repP0.1.1 (.inr t) = .inl 0 ↔ t = fvK k_ggp 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, forall_eq, IsEmpty.forall_iff, and_true]

/-- The momentum entering the `photonCt` vertex through its slot `0` (T₆). -/
theorem p0_photonMomentum (kIn : Fin 0 → Fin 4 → ℝ) (k : Line repP0 → Fin 4 → ℝ) :
    photonMomentum₂ repP0 kIn k ⟨2, ⟨0, by decide⟩⟩ = k (.inr p0gA) := by
  have hA : p0gA.head = (⟨2, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_ggp) := by decide +kernel
  have hB : p0gB.head = (⟨2, ⟨1, by decide⟩⟩ : Wick.PhotonSlot k_ggp) := by decide +kernel
  have hA' : p0gA.1 = (⟨0, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_ggp) := rfl
  have hB' : p0gB.1 = (⟨1, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_ggp) := rfl
  unfold photonMomentum₂
  rw [sum_eq_of_two (by decide) p0_photonLine_cases, hA, hB, hA', hB']
  simp

/-- **The amplitude of `repP0`** at arbitrary line momenta `k`. -/
theorem p0_amplitude (P : Params) (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ)
    (k : Line repP0 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    contractionAmplitude₂ P repP0 (zeroFlavoring k_ggp) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (1 / I) ^ 2 *
        ∑ ν, ∑ ρ, ((1 / I) * ∑ a, ∑ b,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr p0gA)) ν a *
              photonCtFactor P.δ₃ (k (.inr p0gA)) a b *
              QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr p0gB)) ρ b) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl p0f)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3⟩ := p0_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_ggp → Fin 4, ∑ β : Wick.FermionVertex k_ggp → Fin 4,
      ∑ lor : Wick.PhotonSlot k_ggp → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_ggp → Fin 4,
    ((I * P.e) * (I * P.e) * (1 / I) ^ 2 *
        ((1 / I) * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr p0gA))
            (lor (psK k_ggp 0 0)) (lor (psK k_ggp 2 0)) *
          photonCtFactor P.δ₃ (k (.inr p0gA)) (lor (psK k_ggp 2 0)) (lor (psK k_ggp 2 1)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr p0gB))
            (lor (psK k_ggp 1 0)) (lor (psK k_ggp 2 1)))) *
        (Dirac.gamma (lor (psK k_ggp 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl p0f)) *
          Dirac.gamma (lor (psK k_ggp 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain2 (x₁ := fvK k_ggp 1) (x₂ := fvK k_ggp 0) (by decide)
      (by decide +kernel)]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [p0_cond, Fin.prod_univ_three, prod_eq_of_one p0_fermionLine_cases,
      prod_eq_of_two (by decide) p0_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggp 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggp 1 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show k_ggp 2 = .photonCt from rfl),
      p0_photonMomentum, t1, t2, t3]
    simp only [show p0f.1 = fvK k_ggp 1 from rfl, show p0gA.1 = psK k_ggp 0 0 from rfl,
      show p0gB.1 = psK k_ggp 1 0 from rfl, psK, fvK, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero, photonCtFactor]
    ring
  · have n10 : psK k_ggp 1 0 ≠ psK k_ggp 0 0 := by decide
    have n20 : psK k_ggp 2 0 ≠ psK k_ggp 0 0 := by decide
    have n21 : psK k_ggp 2 0 ≠ psK k_ggp 1 0 := by decide
    have m20 : psK k_ggp 2 1 ≠ psK k_ggp 0 0 := by decide
    have m21 : psK k_ggp 2 1 ≠ psK k_ggp 1 0 := by decide
    have m22 : psK k_ggp 2 1 ≠ psK k_ggp 2 0 := by decide
    rw [sum_pi_four (x₁ := psK k_ggp 0 0) (x₂ := psK k_ggp 1 0) (x₃ := psK k_ggp 2 0)
      (x₄ := psK k_ggp 2 1) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel)]
    simp only [ite_true, n10, n20, n21, m20, m21, m22, ite_false, Finset.mul_sum,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The integrand of `repP0`**: `κ` times the self-energy chain with the `δ₃` insertion. -/
theorem p0_integrand (P : Params) (p ℓ : Fin 4 → ℝ) (α β : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repP0 ![p] ![] (p0Mom p ℓ) ![α] ![β] ![] =
      kappaSE P.e * seChain (QED.OneLoop.electronPropagator P.m P.ε (p + (ℓ - p)))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε (ℓ - p)) α β := by
  obtain ⟨m1, m2, m3⟩ := p0Mom_apply p ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 3) (by decide +kernel)),
    p0_amplitude, m1, m2, m3, show p - ℓ = -(ℓ - p) by abel, show p + (ℓ - p) = ℓ by abel,
    kappaSE, seChain]
  simp only [photonPropagator_neg', photonCtFactor_neg, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, photonInsertion, Matrix.cons_val_zero]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The class obligation for `P0`.** -/
theorem classInt_repP0 : ClassInt repP0 := by
  intro Q hQ p α β
  have h := (energyFirst_seP Q hQ.hε p α β).const_mul (kappaSE Q.e)
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_one_chord Q p0_isChord_iff
    (p0Mom p) (p0_isConserved p) (fun ℓ => (p0Mom_apply p ℓ).1) ![α] ![β] ![]
    (fun q => kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m Q.ε (p + q))
      (photonInsertion Q.δ₃ Q.mγ Q.Λ Q.ε q) α β) p
    (fun ℓ => p0_integrand Q p ℓ α β) h.1 h.2

end P0

/-! ### `P1` -/

section P1

/-- The electron line `0 → 1` of `repP1`. -/
def p1f : FermionLine repP1 := ⟨fvK k_ggp 1, by decide +kernel⟩
/-- The photon line `0 → 2₁` of `repP1`. -/
def p1gA : PhotonLine repP1 := ⟨psK k_ggp 0 0, by decide +kernel⟩
/-- The photon line `1 → 2₀` of `repP1`. -/
def p1gB : PhotonLine repP1 := ⟨psK k_ggp 1 0, by decide +kernel⟩

theorem p1_fermionLine_cases : ∀ f : FermionLine repP1, f = p1f := by decide +kernel

theorem p1_photonLine_cases : ∀ g : PhotonLine repP1, g = p1gA ∨ g = p1gB := by decide +kernel

theorem p1_line_cases : ∀ f : Line repP1, f = .inl p1f ∨ f = .inr p1gA ∨ f = .inr p1gB := by
  decide +kernel

theorem p1_isChord_iff : ∀ g : Line repP1, IsChord g ↔ g = .inl p1f := by decide +kernel

theorem p1_ends : (Line.ends (.inl p1f : Line repP1)) = (0, 1) ∧
    (Line.ends (.inr p1gA : Line repP1)) = (0, 2) ∧
    (Line.ends (.inr p1gB : Line repP1)) = (1, 2) := by
  decide +kernel

theorem p1_tails : p1f.tail = fvK k_ggp 0 ∧ p1gA.head = psK k_ggp 2 1 ∧
    p1gB.head = psK k_ggp 2 0 := by
  decide +kernel

theorem p1_ext (v : Fin 3) :
    ((∃ t : Wick.FermionVertex k_ggp, t.1 = v ∧ repP1.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ t : Wick.FermionVertex k_ggp, t.1 = v ∧ repP1.1.1 (.inl 0) = .inr t) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repP1`: `ℓ` on the electron line, `p - ℓ` on `0 → 2`, `ℓ - p` on `1 → 2`. -/
def p1Mom (p ℓ : Fin 4 → ℝ) (f : Line repP1) : Fin 4 → ℝ :=
  if f = .inl p1f then ℓ else if f = .inr p1gA then p - ℓ else ℓ - p

theorem p1Mom_apply (p ℓ : Fin 4 → ℝ) : p1Mom p ℓ (.inl p1f) = ℓ ∧
    p1Mom p ℓ (.inr p1gA) = p - ℓ ∧ p1Mom p ℓ (.inr p1gB) = ℓ - p := by
  refine ⟨ite_eq_left rfl, ?_, ?_⟩
  · rw [p1Mom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [p1Mom, ite_eq_right (by decide), ite_eq_right (by decide)]

theorem p1_isConserved (p ℓ : Fin 4 → ℝ) : IsConserved repP1 ![p] ![p] ![] (p1Mom p ℓ) := by
  obtain ⟨e1, e2, e3⟩ := p1_ends
  obtain ⟨m1, m2, m3⟩ := p1Mom_apply p ℓ
  intro v
  rw [inflow, sum_eq_of_three (by decide) (by decide) (by decide) p1_line_cases,
    externalMomentum_one_zero]
  obtain ⟨x1, x2⟩ := p1_ext v
  simp only [e1, e2, e3, x1, x2, m1, m2, m3, Matrix.cons_val_zero]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem p1_cond (α β : Wick.FermionVertex k_ggp → Fin 4) (lor : Wick.PhotonSlot k_ggp → Fin 4)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    ((∀ i t, repP1.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repP1.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repP1.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (α (fvK k_ggp 1) = αOut 0 ∧ β (fvK k_ggp 0) = βIn 0) := by
  have h1 : ∀ t, repP1.1.1 (.inl 0) = .inr t ↔ t = fvK k_ggp 1 := by decide +kernel
  have h2 : ∀ t, repP1.1.1 (.inr t) = .inl 0 ↔ t = fvK k_ggp 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, forall_eq, IsEmpty.forall_iff, and_true]

/-- The momentum entering the `photonCt` vertex through its slot `0` (T₆). -/
theorem p1_photonMomentum (kIn : Fin 0 → Fin 4 → ℝ) (k : Line repP1 → Fin 4 → ℝ) :
    photonMomentum₂ repP1 kIn k ⟨2, ⟨0, by decide⟩⟩ = k (.inr p1gB) := by
  have hA : p1gA.head = (⟨2, ⟨1, by decide⟩⟩ : Wick.PhotonSlot k_ggp) := by decide +kernel
  have hB : p1gB.head = (⟨2, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_ggp) := by decide +kernel
  have hA' : p1gA.1 = (⟨0, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_ggp) := rfl
  have hB' : p1gB.1 = (⟨1, ⟨0, by decide⟩⟩ : Wick.PhotonSlot k_ggp) := rfl
  unfold photonMomentum₂
  rw [sum_eq_of_two (by decide) p1_photonLine_cases, hA, hB, hA', hB']
  simp

/-- **The amplitude of `repP1`** at arbitrary line momenta `k`. -/
theorem p1_amplitude (P : Params) (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ)
    (k : Line repP1 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    contractionAmplitude₂ P repP1 (zeroFlavoring k_ggp) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (1 / I) ^ 2 *
        ∑ ν, ∑ ρ, ((1 / I) * ∑ a, ∑ b,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr p1gA)) ν b *
              photonCtFactor P.δ₃ (k (.inr p1gB)) a b *
              QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr p1gB)) ρ a) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl p1f)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3⟩ := p1_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_ggp → Fin 4, ∑ β : Wick.FermionVertex k_ggp → Fin 4,
      ∑ lor : Wick.PhotonSlot k_ggp → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_ggp → Fin 4,
    ((I * P.e) * (I * P.e) * (1 / I) ^ 2 *
        ((1 / I) * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr p1gA))
            (lor (psK k_ggp 0 0)) (lor (psK k_ggp 2 1)) *
          photonCtFactor P.δ₃ (k (.inr p1gB)) (lor (psK k_ggp 2 0)) (lor (psK k_ggp 2 1)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr p1gB))
            (lor (psK k_ggp 1 0)) (lor (psK k_ggp 2 0)))) *
        (Dirac.gamma (lor (psK k_ggp 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl p1f)) *
          Dirac.gamma (lor (psK k_ggp 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain2 (x₁ := fvK k_ggp 1) (x₂ := fvK k_ggp 0) (by decide)
      (by decide +kernel)]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [p1_cond, Fin.prod_univ_three, prod_eq_of_one p1_fermionLine_cases,
      prod_eq_of_two (by decide) p1_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggp 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggp 1 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show k_ggp 2 = .photonCt from rfl),
      p1_photonMomentum, t1, t2, t3]
    simp only [show p1f.1 = fvK k_ggp 1 from rfl, show p1gA.1 = psK k_ggp 0 0 from rfl,
      show p1gB.1 = psK k_ggp 1 0 from rfl, psK, fvK, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero, photonCtFactor]
    ring
  · have n10 : psK k_ggp 1 0 ≠ psK k_ggp 0 0 := by decide
    have n20 : psK k_ggp 2 0 ≠ psK k_ggp 0 0 := by decide
    have n21 : psK k_ggp 2 0 ≠ psK k_ggp 1 0 := by decide
    have m20 : psK k_ggp 2 1 ≠ psK k_ggp 0 0 := by decide
    have m21 : psK k_ggp 2 1 ≠ psK k_ggp 1 0 := by decide
    have m22 : psK k_ggp 2 1 ≠ psK k_ggp 2 0 := by decide
    rw [sum_pi_four (x₁ := psK k_ggp 0 0) (x₂ := psK k_ggp 1 0) (x₃ := psK k_ggp 2 0)
      (x₄ := psK k_ggp 2 1) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel)]
    simp only [ite_true, n10, n20, n21, m20, m21, m22, ite_false, Finset.mul_sum,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The integrand of `repP1`**: `κ` times the self-energy chain with the `δ₃` insertion. -/
theorem p1_integrand (P : Params) (p ℓ : Fin 4 → ℝ) (α β : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repP1 ![p] ![] (p1Mom p ℓ) ![α] ![β] ![] =
      kappaSE P.e * seChain (QED.OneLoop.electronPropagator P.m P.ε (p + (ℓ - p)))
        (photonInsertion P.δ₃ P.mγ P.Λ P.ε (ℓ - p)) α β := by
  obtain ⟨m1, m2, m3⟩ := p1Mom_apply p ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 3) (by decide +kernel)),
    p1_amplitude, m1, m2, m3, show p - ℓ = -(ℓ - p) by abel, show p + (ℓ - p) = ℓ by abel,
    kappaSE, seChain]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, photonInsertion, Matrix.cons_val_zero]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm (f := fun x i => 1 / I *
    (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - p) _ i * photonCtFactor P.δ₃ (ℓ - p) x i *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - p) _ x))]
  simp only [photonCtFactor_comm P.δ₃ (ℓ - p) _ _]
  ring

/-- **The class obligation for `P1`.** -/
theorem classInt_repP1 : ClassInt repP1 := by
  intro Q hQ p α β
  have h := (energyFirst_seP Q hQ.hε p α β).const_mul (kappaSE Q.e)
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_one_chord Q p1_isChord_iff
    (p1Mom p) (p1_isConserved p) (fun ℓ => (p1Mom_apply p ℓ).1) ![α] ![β] ![]
    (fun q => kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m Q.ε (p + q))
      (photonInsertion Q.δ₃ Q.mγ Q.Λ Q.ε q) α β) p
    (fun ℓ => p1_integrand Q p ℓ α β) h.1 h.2

end P1

end QED.GradedProof.SE2

end
