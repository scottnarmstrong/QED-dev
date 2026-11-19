/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassP

/-!
# The class `F`: the one-loop self-energy with a `δ₂`, `δ_m` insertion

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2. The representative `repF` of `QED/GradedProof/SE2Classes.lean` has
two `gauge` vertices `0` (incoming) and `1` (outgoing), the `fermionCt` vertex `2`, the electron
lines `0 → 2 → 1` and the photon line `0 — 1`:

* the lines, their ends, the unique chord (T₁) and an explicit conserved routing (`decide +kernel`);
* the amplitude (T₇) at arbitrary line momenta (`f_amplitude`);
* `(2π)⁻⁴` times the regulated amplitude (T₈) in the routing is `κ` times the self-energy chain
  of the inserted electron line `electronInsertion` with the photon propagator at `q = ℓ - p`
  (`f_integrand`);
* the class obligation `ClassInt` (`classInt_repF`), from
  `QED.GradedProof.SE2.energyFirst_seF`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel
open Complex MeasureTheory

/-- The electron line `2 → 1` of `repF`. -/
def ff1 : FermionLine repF := ⟨fvK k_ggf 1, by decide +kernel⟩
/-- The electron line `0 → 2` of `repF`. -/
def ff2 : FermionLine repF := ⟨fvK k_ggf 2, by decide +kernel⟩
/-- The photon line `0 → 1` of `repF`. -/
def fg : PhotonLine repF := ⟨psK k_ggf 0 0, by decide +kernel⟩

theorem f_fermionLine_cases : ∀ f : FermionLine repF, f = ff1 ∨ f = ff2 := by decide +kernel

theorem f_photonLine_cases : ∀ g : PhotonLine repF, g = fg := by decide +kernel

theorem f_line_cases : ∀ f : Line repF, f = .inl ff1 ∨ f = .inl ff2 ∨ f = .inr fg := by
  decide +kernel

theorem f_isChord_iff : ∀ g : Line repF, IsChord g ↔ g = .inl ff1 := by decide +kernel

theorem f_ends : (Line.ends (.inl ff1 : Line repF)) = (2, 1) ∧
    (Line.ends (.inl ff2 : Line repF)) = (0, 2) ∧
    (Line.ends (.inr fg : Line repF)) = (0, 1) := by
  decide +kernel

theorem f_tails : ff1.tail = fvK k_ggf 2 ∧ ff2.tail = fvK k_ggf 0 ∧ fg.head = psK k_ggf 1 0 := by
  decide +kernel

theorem f_ext (v : Fin 3) :
    ((∃ t : Wick.FermionVertex k_ggf, t.1 = v ∧ repF.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ t : Wick.FermionVertex k_ggf, t.1 = v ∧ repF.1.1 (.inl 0) = .inr t) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repF`: `ℓ` on both electron lines, `p - ℓ` on the photon line. -/
def fMom (p ℓ : Fin 4 → ℝ) (f : Line repF) : Fin 4 → ℝ :=
  if f = .inl ff1 then ℓ else if f = .inl ff2 then ℓ else p - ℓ

theorem fMom_apply (p ℓ : Fin 4 → ℝ) : fMom p ℓ (.inl ff1) = ℓ ∧
    fMom p ℓ (.inl ff2) = ℓ ∧ fMom p ℓ (.inr fg) = p - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_⟩
  · rw [fMom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [fMom, ite_eq_right (by decide), ite_eq_right (by decide)]

theorem f_isConserved (p ℓ : Fin 4 → ℝ) : IsConserved repF ![p] ![p] ![] (fMom p ℓ) := by
  obtain ⟨e1, e2, e3⟩ := f_ends
  obtain ⟨m1, m2, m3⟩ := fMom_apply p ℓ
  intro v
  rw [inflow, sum_eq_of_three (by decide) (by decide) (by decide) f_line_cases,
    externalMomentum_one_zero]
  obtain ⟨x1, x2⟩ := f_ext v
  simp only [e1, e2, e3, x1, x2, m1, m2, m3, Matrix.cons_val_zero]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem f_cond (α β : Wick.FermionVertex k_ggf → Fin 4) (lor : Wick.PhotonSlot k_ggf → Fin 4)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    ((∀ i t, repF.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repF.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repF.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (α (fvK k_ggf 1) = αOut 0 ∧ β (fvK k_ggf 0) = βIn 0) := by
  have h1 : ∀ t, repF.1.1 (.inl 0) = .inr t ↔ t = fvK k_ggf 1 := by decide +kernel
  have h2 : ∀ t, repF.1.1 (.inr t) = .inl 0 ↔ t = fvK k_ggf 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, forall_eq, IsEmpty.forall_iff, and_true]

theorem f_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line repF → Fin 4 → ℝ) :
    psiMomentum₂ repF pIn k ⟨2, by decide⟩ = k (.inl ff2) :=
  psiMomentum₂_of_isRight (by decide +kernel)

/-- **The amplitude of `repF`** at arbitrary line momenta `k`. -/
theorem f_amplitude (P : Params) (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ)
    (k : Line repF → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    contractionAmplitude₂ P repF (zeroFlavoring k_ggf) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 3 *
        ∑ ν, ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr fg)) ν ρ *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl ff1)) *
            fermionCtMatrix P.δ₂ P.δm P.m (k (.inl ff2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl ff2)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3⟩ := f_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_ggf → Fin 4, ∑ β : Wick.FermionVertex k_ggf → Fin 4,
      ∑ lor : Wick.PhotonSlot k_ggf → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_ggf → Fin 4,
    ((I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 3 *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr fg)) (lor (psK k_ggf 0 0))
          (lor (psK k_ggf 1 0)) *
        (Dirac.gamma (lor (psK k_ggf 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl ff1)) *
          fermionCtMatrix P.δ₂ P.δm P.m (k (.inl ff2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl ff2)) *
          Dirac.gamma (lor (psK k_ggf 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain3 (x₁ := fvK k_ggf 1) (x₂ := fvK k_ggf 2) (x₃ := fvK k_ggf 0)
      (by decide) (by decide) (by decide) (by decide +kernel)]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [f_cond, Fin.prod_univ_three, prod_eq_of_two (by decide) f_fermionLine_cases,
      prod_eq_of_one f_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggf 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggf 1 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show k_ggf 2 = .fermionCt from rfl),
      f_psiMomentum, t1, t2, t3]
    simp only [show ff1.1 = fvK k_ggf 1 from rfl, show ff2.1 = fvK k_ggf 2 from rfl,
      show fg.1 = psK k_ggf 0 0 from rfl, psK, fvK, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero, fermionCtMatrix]
    ring
  · have n01 : psK k_ggf 0 0 ≠ psK k_ggf 1 0 := by decide
    rw [sum_pi_two (x₁ := psK k_ggf 0 0) (x₂ := psK k_ggf 1 0) n01 (by decide +kernel)]
    simp only [ite_true, n01.symm, ite_false, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The integrand of `repF`**: `κ` times the self-energy chain of the inserted electron line. -/
theorem f_integrand (P : Params) (p ℓ : Fin 4 → ℝ) (α β : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repF ![p] ![] (fMom p ℓ) ![α] ![β] ![] =
      kappaSE P.e * seChain (electronInsertion P.m P.ε P.δ₂ P.δm (p + (ℓ - p)))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - p)) α β := by
  obtain ⟨m1, m2, m3⟩ := fMom_apply p ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    f_amplitude, m1, m2, m3, show p - ℓ = -(ℓ - p) by abel, show p + (ℓ - p) = ℓ by abel,
    kappaSE, seChain, electronInsertion]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_assoc,
    Matrix.cons_val_zero]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  field_simp

/-- **The class obligation for `F`.** -/
theorem classInt_repF : ClassInt repF := by
  intro Q hQ p α β
  have h := energyFirst_seF Q hQ.hε p α β
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_one_chord Q f_isChord_iff
    (fMom p) (f_isConserved p) (fun ℓ => (fMom_apply p ℓ).1) ![α] ![β] ![]
    (fun q => kappaSE Q.e * seChain (electronInsertion Q.m Q.ε Q.δ₂ Q.δm (p + q))
      (QED.OneLoop.photonPropagator Q.mγ Q.Λ Q.ε q) α β) p
    (fun ℓ => f_integrand Q p ℓ α β) h.1 h.2

end QED.GradedProof.SE2

end
