/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkReps
public import QED.TwoLoop.CountertermInsertionD3

/-!
# Set (c): the T1 values of the classes `CD0`, `CD1`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The classes
`repCD0 s`, `repCD1 s` are the one-loop vertex with a `fermionCt` vertex on its outgoing, resp.
incoming, internal electron line and a `photonCt` vertex on the photon line (field `s` towards
the vertex `0`). Fermion flow `3 → 2 → 1 → 0`; the external photon is at `2`, resp. `1`; photon
lines `0 — 4`, `3 — 4`. For each, as for the order-`e⁵` classes of
`QED/TwoLoop/CountertermInsertionD2.lean` and `QED/TwoLoop/CountertermInsertionD3.lean`:

* the lines, ends, chord and a conserved routing (`decide +kernel`, `ring`);
* the amplitude (T₇) at arbitrary line momenta (`cd1a_amplitude`, …);
* **`contractionValue₂_repCD0a`**, `…CD0b`, **`contractionValue₂_repCD1a`**, `…CD1b` (field
  `0`, resp. `1`, towards `0`): the value (T₁₀) is the
  energy-first integral of the one-loop vertex chain with the inserted electron line
  `electronInsertion` on the outgoing, resp. incoming, side and the inserted photon line
  `photonInsertion`, at every `ε`, under momentum conservation.
-/

@[expose] public section

namespace QED.ChainProof.SetCPauli

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Relabel Complex
open QED.TwoLoop.Insertion QED.ChainProof.SetCLink
open QED.ChainProof.Enum (fv pg pc)

theorem sum_five_cd {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M]
    {a b c d e : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hX : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e) (g : X → M) :
    ∑ x, g x = g a + g b + g c + g d + g e := by
  have : (Finset.univ : Finset X) = {a, b, c, d, e} := by
    ext x
    simpa using hX x
  rw [this, Finset.sum_insert (by simp [hab, hac, had, hae]),
    Finset.sum_insert (by simp [hbc, hbd, hbe]), Finset.sum_insert (by simp [hcd, hce]),
    Finset.sum_pair hde]
  abel

theorem cd_const_aux (c e S : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    c * (I * e * (I * e) * (I * e) * -I * (1 / I) ^ 4 * (S * M i j)) =
      (I * e) ^ 3 * (1 / I) ^ 3 * c * (S * (-M) i j) := by
  change _ = _ * (S * -(M i j))
  field_simp

/-- The two orders of the photon indices of the inserted photon line agree. -/
theorem photonIns_swap (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    (∑ a, ∑ b, 1 / I * (QED.OneLoop.photonPropagator mγ Λ ε k ρ a * photonCtFactor δ₃ k a b *
      QED.OneLoop.photonPropagator mγ Λ ε k ν b)) =
    ∑ a, ∑ b, 1 / I * (QED.OneLoop.photonPropagator mγ Λ ε k ν a * photonCtFactor δ₃ k a b *
      QED.OneLoop.photonPropagator mγ Λ ε k ρ b) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [photonCtFactor_comm]
  ring

/-- The photon factor of the second slot pairing. -/
theorem photonIns_swap' (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    (∑ a, ∑ b, 1 / I * (QED.OneLoop.photonPropagator mγ Λ ε k ρ b * photonCtFactor δ₃ k a b *
      QED.OneLoop.photonPropagator mγ Λ ε k ν a)) =
    ∑ a, ∑ b, 1 / I * (QED.OneLoop.photonPropagator mγ Λ ε k ν a * photonCtFactor δ₃ k a b *
      QED.OneLoop.photonPropagator mγ Λ ε k ρ b) :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### `CD1`, field `0` towards `0`: `δ₂`, `δ_m` on the incoming line -/

section CD1a

/-- The fermion line `3 → 2`. -/
def cd1aF2 : FermionLine (repCD1 0) := ⟨fv kCD1 2, by decide +kernel⟩
/-- The fermion line `2 → 1`. -/
def cd1aF1 : FermionLine (repCD1 0) := ⟨fv kCD1 1, by decide +kernel⟩
/-- The fermion line `1 → 0` (the chord). -/
def cd1aF0 : FermionLine (repCD1 0) := ⟨fv kCD1 0, by decide +kernel⟩
/-- The photon line `0 → 4`. -/
def cd1aGA : PhotonLine (repCD1 0) := ⟨pg kCD1 0, by decide +kernel⟩
/-- The photon line `3 → 4`. -/
def cd1aGB : PhotonLine (repCD1 0) := ⟨pg kCD1 3, by decide +kernel⟩

theorem cd1a_fermionLine_cases :
    ∀ f : FermionLine (repCD1 0), f = cd1aF2 ∨ f = cd1aF1 ∨ f = cd1aF0 := by
  decide +kernel

theorem cd1a_photonLine_cases : ∀ g : PhotonLine (repCD1 0), g = cd1aGA ∨ g = cd1aGB := by
  decide +kernel

theorem cd1a_line_cases : ∀ f : Line (repCD1 0), f = .inl cd1aF2 ∨ f = .inl cd1aF1 ∨
    f = .inl cd1aF0 ∨ f = .inr cd1aGA ∨ f = .inr cd1aGB := by
  rintro (f | g)
  · rcases cd1a_fermionLine_cases f with rfl | rfl | rfl <;> simp
  · rcases cd1a_photonLine_cases g with rfl | rfl <;> simp

theorem cd1a_isChord_iff : ∀ g : Line (repCD1 0), IsChord g ↔ g = .inl cd1aF0 := by
  decide +kernel

theorem cd1a_ends : (Line.ends (.inl cd1aF2 : Line (repCD1 0))) = (3, 2) ∧
    (Line.ends (.inl cd1aF1 : Line (repCD1 0))) = (2, 1) ∧
    (Line.ends (.inl cd1aF0 : Line (repCD1 0))) = (1, 0) ∧
    (Line.ends (.inr cd1aGA : Line (repCD1 0))) = (0, 4) ∧
    (Line.ends (.inr cd1aGB : Line (repCD1 0))) = (3, 4) := by
  decide +kernel

theorem cd1a_tails : cd1aF2.tail = fv kCD1 3 ∧ cd1aF1.tail = fv kCD1 2 ∧
    cd1aF0.tail = fv kCD1 1 ∧ cd1aGA.head = pc kCD1 4 0 ∧ cd1aGB.head = pc kCD1 4 1 := by
  decide +kernel

theorem cd1a_ext (v : Fin 5) :
    ((∃ t : Wick.FermionVertex kCD1, t.1 = v ∧ (repCD1 0).1.1 (.inr t) = .inl 0) ↔ v = 3) ∧
    ((∃ a : Wick.PhotonSlot kCD1, a.1 = v ∧ (repCD1 0).1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kCD1, t.1 = v ∧ (repCD1 0).1.1 (.inl 0) = .inr t) ↔
      v = 0) := by
  revert v
  decide +kernel

/-- The routing: `ℓ` on `1 → 0`, `ℓ - k` on `2 → 1` and `3 → 2`, `ℓ - p - k` on `0 → 4` and
`p + k - ℓ` on `3 → 4`. -/
def cd1aMom (p k ℓ : Fin 4 → ℝ) (f : Line (repCD1 0)) : Fin 4 → ℝ :=
  if f = .inl cd1aF0 then ℓ else if f = .inl cd1aF1 then ℓ - k else if f = .inl cd1aF2 then ℓ - k
    else if f = .inr cd1aGA then ℓ - p - k else p + k - ℓ

theorem cd1aMom_apply (p k ℓ : Fin 4 → ℝ) : cd1aMom p k ℓ (.inl cd1aF0) = ℓ ∧
    cd1aMom p k ℓ (.inl cd1aF1) = ℓ - k ∧ cd1aMom p k ℓ (.inl cd1aF2) = ℓ - k ∧
    cd1aMom p k ℓ (.inr cd1aGA) = ℓ - p - k ∧ cd1aMom p k ℓ (.inr cd1aGB) = p + k - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_, ?_⟩
  · rw [cd1aMom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [cd1aMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [cd1aMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl]
  · rw [cd1aMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide)]

theorem cd1a_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved (repCD1 0) pOut pIn kIn (cd1aMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := cd1a_ends
  obtain ⟨m1, m2, m3, m4, m5⟩ := cd1aMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_five_cd (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) cd1a_line_cases,
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := cd1a_ext v
  simp only [e1, e2, e3, e4, e5, x1, x2, x3, m1, m2, m3, m4, m5]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem pcCD1_0 : pc kCD1 4 0 = ⟨4, ⟨0, by decide⟩⟩ := rfl

theorem pcCD1_1 : pc kCD1 4 1 = ⟨4, ⟨1, by decide⟩⟩ := rfl

theorem cd1a_cond (α β : Wick.FermionVertex kCD1 → Fin 4) (lor : Wick.PhotonSlot kCD1 → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, (repCD1 0).1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, (repCD1 0).1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, (repCD1 0).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kCD1 1) = μ 0 ∧ (α (fv kCD1 0) = αOut 0 ∧ β (fv kCD1 3) = βIn 0) := by
  have h1 : ∀ t, (repCD1 0).1.1 (.inl 0) = .inr t ↔ t = fv kCD1 0 := by decide +kernel
  have h2 : ∀ t, (repCD1 0).1.1 (.inr t) = .inl 0 ↔ t = fv kCD1 3 := by decide +kernel
  have h3 : ∀ a, (repCD1 0).1.2 (.inl 0) = .inr a ↔ a = pg kCD1 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem cd1a_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line (repCD1 0) → Fin 4 → ℝ) :
    psiMomentum₂ (repCD1 0) pIn k ⟨2, by decide⟩ = k (.inl cd1aF2) :=
  psiMomentum₂_of_isRight (by decide +kernel)

/-- The momentum entering the `photonCt` vertex through its slot `0` (T₆). -/
theorem cd1a_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (k : Line (repCD1 0) → Fin 4 → ℝ) :
    photonMomentum₂ (repCD1 0) kIn k ⟨4, ⟨0, by decide⟩⟩ = k (.inr cd1aGA) := by
  have hext : ¬ (repCD1 0).1.2 (.inl 0) = .inr ⟨4, ⟨0, by decide⟩⟩ := by decide +kernel
  have hA : cd1aGA.head = (⟨4, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD1) := by decide +kernel
  have hB : cd1aGB.head = (⟨4, ⟨1, by decide⟩⟩ : Wick.PhotonSlot kCD1) := by decide +kernel
  have hA' : cd1aGA.1 = (⟨0, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD1) := rfl
  have hB' : cd1aGB.1 = (⟨3, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD1) := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right hext, sum_eq_of_two (by decide) cd1a_photonLine_cases, hA,
    hB, hA', hB']
  simp

/-- **The amplitude of `repCD1 0`** at arbitrary line momenta `k`. -/
theorem cd1a_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line (repCD1 0) → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repCD1 0) (zeroFlavoring kCD1) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ∑ ρ, ∑ ν, ((1 / I) * ∑ a, ∑ b,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd1aGA)) ρ a *
              photonCtFactor P.δ₃ (k (.inr cd1aGA)) a b *
              QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd1aGB)) ν b) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1aF0)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1aF1)) *
            fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cd1aF2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1aF2)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := cd1a_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kCD1 → Fin 4, ∑ β : Wick.FermionVertex kCD1 → Fin 4,
      ∑ lor : Wick.PhotonSlot kCD1 → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kCD1 → Fin 4,
    (if lor (pg kCD1 1) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ((1 / I) * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd1aGA))
            (lor (pg kCD1 0)) (lor (pc kCD1 4 0)) *
          photonCtFactor P.δ₃ (k (.inr cd1aGA)) (lor (pc kCD1 4 0)) (lor (pc kCD1 4 1)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd1aGB))
            (lor (pg kCD1 3)) (lor (pc kCD1 4 1)))) *
        (Dirac.gamma (lor (pg kCD1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1aF0)) *
          Dirac.gamma (lor (pg kCD1 1)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1aF1)) *
          fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cd1aF2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1aF2)) *
          Dirac.gamma (lor (pg kCD1 3))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain4 (x₁ := fv kCD1 0) (x₂ := fv kCD1 1) (x₃ := fv kCD1 2)
      (x₄ := fv kCD1 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [cd1a_cond, Fin.prod_univ_five,
      prod_eq_of_three (by decide) (by decide) (by decide) cd1a_fermionLine_cases,
      prod_eq_of_two (by decide) cd1a_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD1 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD1 1 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show kCD1 2 = .fermionCt from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD1 3 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show kCD1 4 = .photonCt from rfl),
      cd1a_psiMomentum, cd1a_photonMomentum, t1, t2, t3, t4, t5, ite_and_eq_mul]
    simp only [show cd1aF0.1 = fv kCD1 0 from rfl, show cd1aF1.1 = fv kCD1 1 from rfl,
      show cd1aF2.1 = fv kCD1 2 from rfl, show cd1aGA.1 = pg kCD1 0 from rfl,
      show cd1aGB.1 = pg kCD1 3 from rfl, pcCD1_0, pcCD1_1, pg, fv, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero, fermionCtMatrix, photonCtFactor]
    ring
  · have n10 : pg kCD1 1 ≠ pg kCD1 0 := by decide
    have n30 : pg kCD1 3 ≠ pg kCD1 0 := by decide
    have n31 : pg kCD1 3 ≠ pg kCD1 1 := by decide
    have n40 : pc kCD1 4 0 ≠ pg kCD1 0 := by decide
    have n41 : pc kCD1 4 0 ≠ pg kCD1 1 := by decide
    have n43 : pc kCD1 4 0 ≠ pg kCD1 3 := by decide
    have m40 : pc kCD1 4 1 ≠ pg kCD1 0 := by decide
    have m41 : pc kCD1 4 1 ≠ pg kCD1 1 := by decide
    have m43 : pc kCD1 4 1 ≠ pg kCD1 3 := by decide
    have m44 : pc kCD1 4 1 ≠ pc kCD1 4 0 := by decide
    rw [sum_pi_five (x₁ := pg kCD1 0) (x₂ := pg kCD1 1) (x₃ := pg kCD1 3)
      (x₄ := pc kCD1 4 0) (x₅ := pc kCD1 4 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide +kernel)]
    simp only [ite_true, n10, n30, n31, n40, n41, n43, m40, m41, m43, m44, ite_false, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of `repCD1 0`**: under momentum conservation, the energy-first integral of the
one-loop vertex chain with the inserted electron line on the incoming side and the inserted
photon line, at every `ε`. -/
theorem contractionValue₂_repCD1a (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P (repCD1 0) pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + ℓ))
          (electronInsertion P.m P.ε P.δ₂ P.δm (pIn 0 + ℓ))
          (photonInsertion P.δ₃ P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P cd1a_isChord_iff (cd1aMom (pIn 0) (kIn 0))
    (cd1a_isConserved hmom) (fun ℓ => (cd1aMom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pOut 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4, m5⟩ := cd1aMom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 5) (by decide +kernel)),
    cd1a_amplitude, m1, m2, m3, m4, m5, vertexChain, electronInsertion, hmom,
    show pIn 0 + kIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ by abel,
    show pIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ - kIn 0 by abel,
    show ℓ - pIn 0 - kIn 0 = ℓ - (pIn 0 + kIn 0) by abel,
    show pIn 0 + kIn 0 - ℓ = -(ℓ - (pIn 0 + kIn 0)) by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_assoc,
    photonInsertion]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [photonIns_swap]
  exact cd_const_aux _ _ _ _ _ _

end CD1a

/-! ### `CD1`, field `1` towards `0`: `δ₂`, `δ_m` on the incoming line -/

section CD1b

/-- The fermion line `3 → 2`. -/
def cd1bF2 : FermionLine (repCD1 1) := ⟨fv kCD1 2, by decide +kernel⟩
/-- The fermion line `2 → 1`. -/
def cd1bF1 : FermionLine (repCD1 1) := ⟨fv kCD1 1, by decide +kernel⟩
/-- The fermion line `1 → 0` (the chord). -/
def cd1bF0 : FermionLine (repCD1 1) := ⟨fv kCD1 0, by decide +kernel⟩
/-- The photon line `0 → 4`. -/
def cd1bGA : PhotonLine (repCD1 1) := ⟨pg kCD1 0, by decide +kernel⟩
/-- The photon line `3 → 4`. -/
def cd1bGB : PhotonLine (repCD1 1) := ⟨pg kCD1 3, by decide +kernel⟩

theorem cd1b_fermionLine_cases :
    ∀ f : FermionLine (repCD1 1), f = cd1bF2 ∨ f = cd1bF1 ∨ f = cd1bF0 := by
  decide +kernel

theorem cd1b_photonLine_cases : ∀ g : PhotonLine (repCD1 1), g = cd1bGA ∨ g = cd1bGB := by
  decide +kernel

theorem cd1b_line_cases : ∀ f : Line (repCD1 1), f = .inl cd1bF2 ∨ f = .inl cd1bF1 ∨
    f = .inl cd1bF0 ∨ f = .inr cd1bGA ∨ f = .inr cd1bGB := by
  rintro (f | g)
  · rcases cd1b_fermionLine_cases f with rfl | rfl | rfl <;> simp
  · rcases cd1b_photonLine_cases g with rfl | rfl <;> simp

theorem cd1b_isChord_iff : ∀ g : Line (repCD1 1), IsChord g ↔ g = .inl cd1bF0 := by
  decide +kernel

theorem cd1b_ends : (Line.ends (.inl cd1bF2 : Line (repCD1 1))) = (3, 2) ∧
    (Line.ends (.inl cd1bF1 : Line (repCD1 1))) = (2, 1) ∧
    (Line.ends (.inl cd1bF0 : Line (repCD1 1))) = (1, 0) ∧
    (Line.ends (.inr cd1bGA : Line (repCD1 1))) = (0, 4) ∧
    (Line.ends (.inr cd1bGB : Line (repCD1 1))) = (3, 4) := by
  decide +kernel

theorem cd1b_tails : cd1bF2.tail = fv kCD1 3 ∧ cd1bF1.tail = fv kCD1 2 ∧
    cd1bF0.tail = fv kCD1 1 ∧ cd1bGA.head = pc kCD1 4 1 ∧ cd1bGB.head = pc kCD1 4 0 := by
  decide +kernel

theorem cd1b_ext (v : Fin 5) :
    ((∃ t : Wick.FermionVertex kCD1, t.1 = v ∧ (repCD1 1).1.1 (.inr t) = .inl 0) ↔ v = 3) ∧
    ((∃ a : Wick.PhotonSlot kCD1, a.1 = v ∧ (repCD1 1).1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kCD1, t.1 = v ∧ (repCD1 1).1.1 (.inl 0) = .inr t) ↔
      v = 0) := by
  revert v
  decide +kernel

/-- The routing: `ℓ` on `1 → 0`, `ℓ - k` on `2 → 1` and `3 → 2`, `ℓ - p - k` on `0 → 4` and
`p + k - ℓ` on `3 → 4`. -/
def cd1bMom (p k ℓ : Fin 4 → ℝ) (f : Line (repCD1 1)) : Fin 4 → ℝ :=
  if f = .inl cd1bF0 then ℓ else if f = .inl cd1bF1 then ℓ - k else if f = .inl cd1bF2 then ℓ - k
    else if f = .inr cd1bGA then ℓ - p - k else p + k - ℓ

theorem cd1bMom_apply (p k ℓ : Fin 4 → ℝ) : cd1bMom p k ℓ (.inl cd1bF0) = ℓ ∧
    cd1bMom p k ℓ (.inl cd1bF1) = ℓ - k ∧ cd1bMom p k ℓ (.inl cd1bF2) = ℓ - k ∧
    cd1bMom p k ℓ (.inr cd1bGA) = ℓ - p - k ∧ cd1bMom p k ℓ (.inr cd1bGB) = p + k - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_, ?_⟩
  · rw [cd1bMom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [cd1bMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [cd1bMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl]
  · rw [cd1bMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide)]

theorem cd1b_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved (repCD1 1) pOut pIn kIn (cd1bMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := cd1b_ends
  obtain ⟨m1, m2, m3, m4, m5⟩ := cd1bMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_five_cd (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) cd1b_line_cases,
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := cd1b_ext v
  simp only [e1, e2, e3, e4, e5, x1, x2, x3, m1, m2, m3, m4, m5]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem cd1b_cond (α β : Wick.FermionVertex kCD1 → Fin 4) (lor : Wick.PhotonSlot kCD1 → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, (repCD1 1).1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, (repCD1 1).1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, (repCD1 1).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kCD1 1) = μ 0 ∧ (α (fv kCD1 0) = αOut 0 ∧ β (fv kCD1 3) = βIn 0) := by
  have h1 : ∀ t, (repCD1 1).1.1 (.inl 0) = .inr t ↔ t = fv kCD1 0 := by decide +kernel
  have h2 : ∀ t, (repCD1 1).1.1 (.inr t) = .inl 0 ↔ t = fv kCD1 3 := by decide +kernel
  have h3 : ∀ a, (repCD1 1).1.2 (.inl 0) = .inr a ↔ a = pg kCD1 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem cd1b_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line (repCD1 1) → Fin 4 → ℝ) :
    psiMomentum₂ (repCD1 1) pIn k ⟨2, by decide⟩ = k (.inl cd1bF2) :=
  psiMomentum₂_of_isRight (by decide +kernel)

/-- The momentum entering the `photonCt` vertex through its slot `0` (T₆). -/
theorem cd1b_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (k : Line (repCD1 1) → Fin 4 → ℝ) :
    photonMomentum₂ (repCD1 1) kIn k ⟨4, ⟨0, by decide⟩⟩ = k (.inr cd1bGB) := by
  have hext : ¬ (repCD1 1).1.2 (.inl 0) = .inr ⟨4, ⟨0, by decide⟩⟩ := by decide +kernel
  have hA : cd1bGA.head = (⟨4, ⟨1, by decide⟩⟩ : Wick.PhotonSlot kCD1) := by decide +kernel
  have hB : cd1bGB.head = (⟨4, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD1) := by decide +kernel
  have hA' : cd1bGA.1 = (⟨0, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD1) := rfl
  have hB' : cd1bGB.1 = (⟨3, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD1) := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right hext, sum_eq_of_two (by decide) cd1b_photonLine_cases, hA,
    hB, hA', hB']
  simp

/-- **The amplitude of `repCD1 1`** at arbitrary line momenta `k`. -/
theorem cd1b_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line (repCD1 1) → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repCD1 1) (zeroFlavoring kCD1) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ∑ ρ, ∑ ν, ((1 / I) * ∑ a, ∑ b,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd1bGA)) ρ b *
              photonCtFactor P.δ₃ (k (.inr cd1bGB)) a b *
              QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd1bGB)) ν a) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1bF0)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1bF1)) *
            fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cd1bF2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1bF2)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := cd1b_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kCD1 → Fin 4, ∑ β : Wick.FermionVertex kCD1 → Fin 4,
      ∑ lor : Wick.PhotonSlot kCD1 → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kCD1 → Fin 4,
    (if lor (pg kCD1 1) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ((1 / I) * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd1bGA))
            (lor (pg kCD1 0)) (lor (pc kCD1 4 1)) *
          photonCtFactor P.δ₃ (k (.inr cd1bGB)) (lor (pc kCD1 4 0)) (lor (pc kCD1 4 1)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd1bGB))
            (lor (pg kCD1 3)) (lor (pc kCD1 4 0)))) *
        (Dirac.gamma (lor (pg kCD1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1bF0)) *
          Dirac.gamma (lor (pg kCD1 1)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1bF1)) *
          fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cd1bF2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd1bF2)) *
          Dirac.gamma (lor (pg kCD1 3))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain4 (x₁ := fv kCD1 0) (x₂ := fv kCD1 1) (x₃ := fv kCD1 2)
      (x₄ := fv kCD1 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [cd1b_cond, Fin.prod_univ_five,
      prod_eq_of_three (by decide) (by decide) (by decide) cd1b_fermionLine_cases,
      prod_eq_of_two (by decide) cd1b_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD1 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD1 1 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show kCD1 2 = .fermionCt from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD1 3 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show kCD1 4 = .photonCt from rfl),
      cd1b_psiMomentum, cd1b_photonMomentum, t1, t2, t3, t4, t5, ite_and_eq_mul]
    simp only [show cd1bF0.1 = fv kCD1 0 from rfl, show cd1bF1.1 = fv kCD1 1 from rfl,
      show cd1bF2.1 = fv kCD1 2 from rfl, show cd1bGA.1 = pg kCD1 0 from rfl,
      show cd1bGB.1 = pg kCD1 3 from rfl, pcCD1_0, pcCD1_1, pg, fv, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero, fermionCtMatrix, photonCtFactor]
    ring
  · have n10 : pg kCD1 1 ≠ pg kCD1 0 := by decide
    have n30 : pg kCD1 3 ≠ pg kCD1 0 := by decide
    have n31 : pg kCD1 3 ≠ pg kCD1 1 := by decide
    have n40 : pc kCD1 4 0 ≠ pg kCD1 0 := by decide
    have n41 : pc kCD1 4 0 ≠ pg kCD1 1 := by decide
    have n43 : pc kCD1 4 0 ≠ pg kCD1 3 := by decide
    have m40 : pc kCD1 4 1 ≠ pg kCD1 0 := by decide
    have m41 : pc kCD1 4 1 ≠ pg kCD1 1 := by decide
    have m43 : pc kCD1 4 1 ≠ pg kCD1 3 := by decide
    have m44 : pc kCD1 4 1 ≠ pc kCD1 4 0 := by decide
    rw [sum_pi_five (x₁ := pg kCD1 0) (x₂ := pg kCD1 1) (x₃ := pg kCD1 3)
      (x₄ := pc kCD1 4 0) (x₅ := pc kCD1 4 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide +kernel)]
    simp only [ite_true, n10, n30, n31, n40, n41, n43, m40, m41, m43, m44, ite_false, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of `repCD1 1`**: under momentum conservation, the energy-first integral of the
one-loop vertex chain with the inserted electron line on the incoming side and the inserted
photon line, at every `ε`. -/
theorem contractionValue₂_repCD1b (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P (repCD1 1) pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + ℓ))
          (electronInsertion P.m P.ε P.δ₂ P.δm (pIn 0 + ℓ))
          (photonInsertion P.δ₃ P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P cd1b_isChord_iff (cd1bMom (pIn 0) (kIn 0))
    (cd1b_isConserved hmom) (fun ℓ => (cd1bMom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pOut 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4, m5⟩ := cd1bMom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 5) (by decide +kernel)),
    cd1b_amplitude, m1, m2, m3, m4, m5, vertexChain, electronInsertion, hmom,
    show pIn 0 + kIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ by abel,
    show pIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ - kIn 0 by abel,
    show ℓ - pIn 0 - kIn 0 = ℓ - (pIn 0 + kIn 0) by abel,
    show pIn 0 + kIn 0 - ℓ = -(ℓ - (pIn 0 + kIn 0)) by abel]
  simp only [photonPropagator_neg', photonCtFactor_neg, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply,
    Matrix.mul_assoc, photonInsertion]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [photonIns_swap']
  exact cd_const_aux _ _ _ _ _ _

end CD1b

/-! ### `CD0`, field `0` towards `0`: `δ₂`, `δ_m` on the outgoing line -/

section CD0a

/-- The fermion line `3 → 2`. -/
def cd0aF2 : FermionLine (repCD0 0) := ⟨fv kCD0 2, by decide +kernel⟩
/-- The fermion line `2 → 1`. -/
def cd0aF1 : FermionLine (repCD0 0) := ⟨fv kCD0 1, by decide +kernel⟩
/-- The fermion line `1 → 0` (the chord). -/
def cd0aF0 : FermionLine (repCD0 0) := ⟨fv kCD0 0, by decide +kernel⟩
/-- The photon line `0 → 4`. -/
def cd0aGA : PhotonLine (repCD0 0) := ⟨pg kCD0 0, by decide +kernel⟩
/-- The photon line `3 → 4`. -/
def cd0aGB : PhotonLine (repCD0 0) := ⟨pg kCD0 3, by decide +kernel⟩

theorem cd0a_fermionLine_cases :
    ∀ f : FermionLine (repCD0 0), f = cd0aF2 ∨ f = cd0aF1 ∨ f = cd0aF0 := by
  decide +kernel

theorem cd0a_photonLine_cases : ∀ g : PhotonLine (repCD0 0), g = cd0aGA ∨ g = cd0aGB := by
  decide +kernel

theorem cd0a_line_cases : ∀ f : Line (repCD0 0), f = .inl cd0aF2 ∨ f = .inl cd0aF1 ∨
    f = .inl cd0aF0 ∨ f = .inr cd0aGA ∨ f = .inr cd0aGB := by
  rintro (f | g)
  · rcases cd0a_fermionLine_cases f with rfl | rfl | rfl <;> simp
  · rcases cd0a_photonLine_cases g with rfl | rfl <;> simp

theorem cd0a_isChord_iff : ∀ g : Line (repCD0 0), IsChord g ↔ g = .inl cd0aF0 := by
  decide +kernel

theorem cd0a_ends : (Line.ends (.inl cd0aF2 : Line (repCD0 0))) = (3, 2) ∧
    (Line.ends (.inl cd0aF1 : Line (repCD0 0))) = (2, 1) ∧
    (Line.ends (.inl cd0aF0 : Line (repCD0 0))) = (1, 0) ∧
    (Line.ends (.inr cd0aGA : Line (repCD0 0))) = (0, 4) ∧
    (Line.ends (.inr cd0aGB : Line (repCD0 0))) = (3, 4) := by
  decide +kernel

theorem cd0a_tails : cd0aF2.tail = fv kCD0 3 ∧ cd0aF1.tail = fv kCD0 2 ∧
    cd0aF0.tail = fv kCD0 1 ∧ cd0aGA.head = pc kCD0 4 0 ∧ cd0aGB.head = pc kCD0 4 1 := by
  decide +kernel

theorem cd0a_ext (v : Fin 5) :
    ((∃ t : Wick.FermionVertex kCD0, t.1 = v ∧ (repCD0 0).1.1 (.inr t) = .inl 0) ↔ v = 3) ∧
    ((∃ a : Wick.PhotonSlot kCD0, a.1 = v ∧ (repCD0 0).1.2 (.inl 0) = .inr a) ↔ v = 2) ∧
    ((∃ t : Wick.FermionVertex kCD0, t.1 = v ∧ (repCD0 0).1.1 (.inl 0) = .inr t) ↔
      v = 0) := by
  revert v
  decide +kernel

/-- The routing: `ℓ` on `1 → 0` and `2 → 1`, `ℓ - k` on `3 → 2`, `ℓ - p - k` on `0 → 4` and
`p + k - ℓ` on `3 → 4`. -/
def cd0aMom (p k ℓ : Fin 4 → ℝ) (f : Line (repCD0 0)) : Fin 4 → ℝ :=
  if f = .inl cd0aF0 then ℓ else if f = .inl cd0aF1 then ℓ else if f = .inl cd0aF2 then ℓ - k
    else if f = .inr cd0aGA then ℓ - p - k else p + k - ℓ

theorem cd0aMom_apply (p k ℓ : Fin 4 → ℝ) : cd0aMom p k ℓ (.inl cd0aF0) = ℓ ∧
    cd0aMom p k ℓ (.inl cd0aF1) = ℓ ∧ cd0aMom p k ℓ (.inl cd0aF2) = ℓ - k ∧
    cd0aMom p k ℓ (.inr cd0aGA) = ℓ - p - k ∧ cd0aMom p k ℓ (.inr cd0aGB) = p + k - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_, ?_⟩
  · rw [cd0aMom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [cd0aMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [cd0aMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl]
  · rw [cd0aMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide)]

theorem cd0a_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved (repCD0 0) pOut pIn kIn (cd0aMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := cd0a_ends
  obtain ⟨m1, m2, m3, m4, m5⟩ := cd0aMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_five_cd (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) cd0a_line_cases,
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := cd0a_ext v
  simp only [e1, e2, e3, e4, e5, x1, x2, x3, m1, m2, m3, m4, m5]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem pcCD0_0 : pc kCD0 4 0 = ⟨4, ⟨0, by decide⟩⟩ := rfl

theorem pcCD0_1 : pc kCD0 4 1 = ⟨4, ⟨1, by decide⟩⟩ := rfl

theorem cd0a_cond (α β : Wick.FermionVertex kCD0 → Fin 4) (lor : Wick.PhotonSlot kCD0 → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, (repCD0 0).1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, (repCD0 0).1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, (repCD0 0).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kCD0 2) = μ 0 ∧ (α (fv kCD0 0) = αOut 0 ∧ β (fv kCD0 3) = βIn 0) := by
  have h1 : ∀ t, (repCD0 0).1.1 (.inl 0) = .inr t ↔ t = fv kCD0 0 := by decide +kernel
  have h2 : ∀ t, (repCD0 0).1.1 (.inr t) = .inl 0 ↔ t = fv kCD0 3 := by decide +kernel
  have h3 : ∀ a, (repCD0 0).1.2 (.inl 0) = .inr a ↔ a = pg kCD0 2 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem cd0a_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line (repCD0 0) → Fin 4 → ℝ) :
    psiMomentum₂ (repCD0 0) pIn k ⟨1, by decide⟩ = k (.inl cd0aF1) :=
  psiMomentum₂_of_isRight (by decide +kernel)

/-- The momentum entering the `photonCt` vertex through its slot `0` (T₆). -/
theorem cd0a_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (k : Line (repCD0 0) → Fin 4 → ℝ) :
    photonMomentum₂ (repCD0 0) kIn k ⟨4, ⟨0, by decide⟩⟩ = k (.inr cd0aGA) := by
  have hext : ¬ (repCD0 0).1.2 (.inl 0) = .inr ⟨4, ⟨0, by decide⟩⟩ := by decide +kernel
  have hA : cd0aGA.head = (⟨4, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD0) := by decide +kernel
  have hB : cd0aGB.head = (⟨4, ⟨1, by decide⟩⟩ : Wick.PhotonSlot kCD0) := by decide +kernel
  have hA' : cd0aGA.1 = (⟨0, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD0) := rfl
  have hB' : cd0aGB.1 = (⟨3, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD0) := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right hext, sum_eq_of_two (by decide) cd0a_photonLine_cases, hA,
    hB, hA', hB']
  simp

/-- **The amplitude of `repCD0 0`** at arbitrary line momenta `k`. -/
theorem cd0a_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line (repCD0 0) → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repCD0 0) (zeroFlavoring kCD0) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ∑ ρ, ∑ ν, ((1 / I) * ∑ a, ∑ b,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd0aGA)) ρ a *
              photonCtFactor P.δ₃ (k (.inr cd0aGA)) a b *
              QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd0aGB)) ν b) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0aF0)) *
            fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cd0aF1)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0aF1)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0aF2)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := cd0a_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kCD0 → Fin 4, ∑ β : Wick.FermionVertex kCD0 → Fin 4,
      ∑ lor : Wick.PhotonSlot kCD0 → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kCD0 → Fin 4,
    (if lor (pg kCD0 2) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ((1 / I) * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd0aGA))
            (lor (pg kCD0 0)) (lor (pc kCD0 4 0)) *
          photonCtFactor P.δ₃ (k (.inr cd0aGA)) (lor (pc kCD0 4 0)) (lor (pc kCD0 4 1)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd0aGB))
            (lor (pg kCD0 3)) (lor (pc kCD0 4 1)))) *
        (Dirac.gamma (lor (pg kCD0 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0aF0)) *
          fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cd0aF1)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0aF1)) *
          Dirac.gamma (lor (pg kCD0 2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0aF2)) *
          Dirac.gamma (lor (pg kCD0 3))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain4 (x₁ := fv kCD0 0) (x₂ := fv kCD0 1) (x₃ := fv kCD0 2)
      (x₄ := fv kCD0 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [cd0a_cond, Fin.prod_univ_five,
      prod_eq_of_three (by decide) (by decide) (by decide) cd0a_fermionLine_cases,
      prod_eq_of_two (by decide) cd0a_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD0 0 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show kCD0 1 = .fermionCt from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD0 2 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD0 3 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show kCD0 4 = .photonCt from rfl),
      cd0a_psiMomentum, cd0a_photonMomentum, t1, t2, t3, t4, t5, ite_and_eq_mul]
    simp only [show cd0aF0.1 = fv kCD0 0 from rfl, show cd0aF1.1 = fv kCD0 1 from rfl,
      show cd0aF2.1 = fv kCD0 2 from rfl, show cd0aGA.1 = pg kCD0 0 from rfl,
      show cd0aGB.1 = pg kCD0 3 from rfl, pcCD0_0, pcCD0_1, pg, fv, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero, fermionCtMatrix, photonCtFactor]
    ring
  · have n10 : pg kCD0 2 ≠ pg kCD0 0 := by decide
    have n30 : pg kCD0 3 ≠ pg kCD0 0 := by decide
    have n31 : pg kCD0 3 ≠ pg kCD0 2 := by decide
    have n40 : pc kCD0 4 0 ≠ pg kCD0 0 := by decide
    have n41 : pc kCD0 4 0 ≠ pg kCD0 2 := by decide
    have n43 : pc kCD0 4 0 ≠ pg kCD0 3 := by decide
    have m40 : pc kCD0 4 1 ≠ pg kCD0 0 := by decide
    have m41 : pc kCD0 4 1 ≠ pg kCD0 2 := by decide
    have m43 : pc kCD0 4 1 ≠ pg kCD0 3 := by decide
    have m44 : pc kCD0 4 1 ≠ pc kCD0 4 0 := by decide
    rw [sum_pi_five (x₁ := pg kCD0 0) (x₂ := pg kCD0 2) (x₃ := pg kCD0 3)
      (x₄ := pc kCD0 4 0) (x₅ := pc kCD0 4 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide +kernel)]
    simp only [ite_true, n10, n30, n31, n40, n41, n43, m40, m41, m43, m44, ite_false, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of `repCD0 0`**: under momentum conservation, the energy-first integral of the
one-loop vertex chain with the inserted electron line on the outgoing side and the inserted
photon line, at every `ε`. -/
theorem contractionValue₂_repCD0a (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P (repCD0 0) pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (electronInsertion P.m P.ε P.δ₂ P.δm (pOut 0 + ℓ))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + ℓ))
          (photonInsertion P.δ₃ P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P cd0a_isChord_iff (cd0aMom (pIn 0) (kIn 0))
    (cd0a_isConserved hmom) (fun ℓ => (cd0aMom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pOut 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4, m5⟩ := cd0aMom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 5) (by decide +kernel)),
    cd0a_amplitude, m1, m2, m3, m4, m5, vertexChain, electronInsertion, hmom,
    show pIn 0 + kIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ by abel,
    show pIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ - kIn 0 by abel,
    show ℓ - pIn 0 - kIn 0 = ℓ - (pIn 0 + kIn 0) by abel,
    show pIn 0 + kIn 0 - ℓ = -(ℓ - (pIn 0 + kIn 0)) by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_assoc,
    photonInsertion]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [photonIns_swap]
  exact cd_const_aux _ _ _ _ _ _

end CD0a

/-! ### `CD0`, field `1` towards `0`: `δ₂`, `δ_m` on the outgoing line -/

section CD0b

/-- The fermion line `3 → 2`. -/
def cd0bF2 : FermionLine (repCD0 1) := ⟨fv kCD0 2, by decide +kernel⟩
/-- The fermion line `2 → 1`. -/
def cd0bF1 : FermionLine (repCD0 1) := ⟨fv kCD0 1, by decide +kernel⟩
/-- The fermion line `1 → 0` (the chord). -/
def cd0bF0 : FermionLine (repCD0 1) := ⟨fv kCD0 0, by decide +kernel⟩
/-- The photon line `0 → 4`. -/
def cd0bGA : PhotonLine (repCD0 1) := ⟨pg kCD0 0, by decide +kernel⟩
/-- The photon line `3 → 4`. -/
def cd0bGB : PhotonLine (repCD0 1) := ⟨pg kCD0 3, by decide +kernel⟩

theorem cd0b_fermionLine_cases :
    ∀ f : FermionLine (repCD0 1), f = cd0bF2 ∨ f = cd0bF1 ∨ f = cd0bF0 := by
  decide +kernel

theorem cd0b_photonLine_cases : ∀ g : PhotonLine (repCD0 1), g = cd0bGA ∨ g = cd0bGB := by
  decide +kernel

theorem cd0b_line_cases : ∀ f : Line (repCD0 1), f = .inl cd0bF2 ∨ f = .inl cd0bF1 ∨
    f = .inl cd0bF0 ∨ f = .inr cd0bGA ∨ f = .inr cd0bGB := by
  rintro (f | g)
  · rcases cd0b_fermionLine_cases f with rfl | rfl | rfl <;> simp
  · rcases cd0b_photonLine_cases g with rfl | rfl <;> simp

theorem cd0b_isChord_iff : ∀ g : Line (repCD0 1), IsChord g ↔ g = .inl cd0bF0 := by
  decide +kernel

theorem cd0b_ends : (Line.ends (.inl cd0bF2 : Line (repCD0 1))) = (3, 2) ∧
    (Line.ends (.inl cd0bF1 : Line (repCD0 1))) = (2, 1) ∧
    (Line.ends (.inl cd0bF0 : Line (repCD0 1))) = (1, 0) ∧
    (Line.ends (.inr cd0bGA : Line (repCD0 1))) = (0, 4) ∧
    (Line.ends (.inr cd0bGB : Line (repCD0 1))) = (3, 4) := by
  decide +kernel

theorem cd0b_tails : cd0bF2.tail = fv kCD0 3 ∧ cd0bF1.tail = fv kCD0 2 ∧
    cd0bF0.tail = fv kCD0 1 ∧ cd0bGA.head = pc kCD0 4 1 ∧ cd0bGB.head = pc kCD0 4 0 := by
  decide +kernel

theorem cd0b_ext (v : Fin 5) :
    ((∃ t : Wick.FermionVertex kCD0, t.1 = v ∧ (repCD0 1).1.1 (.inr t) = .inl 0) ↔ v = 3) ∧
    ((∃ a : Wick.PhotonSlot kCD0, a.1 = v ∧ (repCD0 1).1.2 (.inl 0) = .inr a) ↔ v = 2) ∧
    ((∃ t : Wick.FermionVertex kCD0, t.1 = v ∧ (repCD0 1).1.1 (.inl 0) = .inr t) ↔
      v = 0) := by
  revert v
  decide +kernel

/-- The routing: `ℓ` on `1 → 0` and `2 → 1`, `ℓ - k` on `3 → 2`, `ℓ - p - k` on `0 → 4` and
`p + k - ℓ` on `3 → 4`. -/
def cd0bMom (p k ℓ : Fin 4 → ℝ) (f : Line (repCD0 1)) : Fin 4 → ℝ :=
  if f = .inl cd0bF0 then ℓ else if f = .inl cd0bF1 then ℓ else if f = .inl cd0bF2 then ℓ - k
    else if f = .inr cd0bGA then ℓ - p - k else p + k - ℓ

theorem cd0bMom_apply (p k ℓ : Fin 4 → ℝ) : cd0bMom p k ℓ (.inl cd0bF0) = ℓ ∧
    cd0bMom p k ℓ (.inl cd0bF1) = ℓ ∧ cd0bMom p k ℓ (.inl cd0bF2) = ℓ - k ∧
    cd0bMom p k ℓ (.inr cd0bGA) = ℓ - p - k ∧ cd0bMom p k ℓ (.inr cd0bGB) = p + k - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_, ?_⟩
  · rw [cd0bMom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [cd0bMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [cd0bMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl]
  · rw [cd0bMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide)]

theorem cd0b_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved (repCD0 1) pOut pIn kIn (cd0bMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := cd0b_ends
  obtain ⟨m1, m2, m3, m4, m5⟩ := cd0bMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_five_cd (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) cd0b_line_cases,
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := cd0b_ext v
  simp only [e1, e2, e3, e4, e5, x1, x2, x3, m1, m2, m3, m4, m5]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem cd0b_cond (α β : Wick.FermionVertex kCD0 → Fin 4) (lor : Wick.PhotonSlot kCD0 → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, (repCD0 1).1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, (repCD0 1).1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, (repCD0 1).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kCD0 2) = μ 0 ∧ (α (fv kCD0 0) = αOut 0 ∧ β (fv kCD0 3) = βIn 0) := by
  have h1 : ∀ t, (repCD0 1).1.1 (.inl 0) = .inr t ↔ t = fv kCD0 0 := by decide +kernel
  have h2 : ∀ t, (repCD0 1).1.1 (.inr t) = .inl 0 ↔ t = fv kCD0 3 := by decide +kernel
  have h3 : ∀ a, (repCD0 1).1.2 (.inl 0) = .inr a ↔ a = pg kCD0 2 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem cd0b_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line (repCD0 1) → Fin 4 → ℝ) :
    psiMomentum₂ (repCD0 1) pIn k ⟨1, by decide⟩ = k (.inl cd0bF1) :=
  psiMomentum₂_of_isRight (by decide +kernel)

/-- The momentum entering the `photonCt` vertex through its slot `0` (T₆). -/
theorem cd0b_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (k : Line (repCD0 1) → Fin 4 → ℝ) :
    photonMomentum₂ (repCD0 1) kIn k ⟨4, ⟨0, by decide⟩⟩ = k (.inr cd0bGB) := by
  have hext : ¬ (repCD0 1).1.2 (.inl 0) = .inr ⟨4, ⟨0, by decide⟩⟩ := by decide +kernel
  have hA : cd0bGA.head = (⟨4, ⟨1, by decide⟩⟩ : Wick.PhotonSlot kCD0) := by decide +kernel
  have hB : cd0bGB.head = (⟨4, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD0) := by decide +kernel
  have hA' : cd0bGA.1 = (⟨0, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD0) := rfl
  have hB' : cd0bGB.1 = (⟨3, ⟨0, by decide⟩⟩ : Wick.PhotonSlot kCD0) := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right hext, sum_eq_of_two (by decide) cd0b_photonLine_cases, hA,
    hB, hA', hB']
  simp

/-- **The amplitude of `repCD0 1`** at arbitrary line momenta `k`. -/
theorem cd0b_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line (repCD0 1) → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repCD0 1) (zeroFlavoring kCD0) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ∑ ρ, ∑ ν, ((1 / I) * ∑ a, ∑ b,
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd0bGA)) ρ b *
              photonCtFactor P.δ₃ (k (.inr cd0bGB)) a b *
              QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd0bGB)) ν a) *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0bF0)) *
            fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cd0bF1)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0bF1)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0bF2)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := cd0b_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kCD0 → Fin 4, ∑ β : Wick.FermionVertex kCD0 → Fin 4,
      ∑ lor : Wick.PhotonSlot kCD0 → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kCD0 → Fin 4,
    (if lor (pg kCD0 2) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ((1 / I) * (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd0bGA))
            (lor (pg kCD0 0)) (lor (pc kCD0 4 1)) *
          photonCtFactor P.δ₃ (k (.inr cd0bGB)) (lor (pc kCD0 4 0)) (lor (pc kCD0 4 1)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr cd0bGB))
            (lor (pg kCD0 3)) (lor (pc kCD0 4 0)))) *
        (Dirac.gamma (lor (pg kCD0 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0bF0)) *
          fermionCtMatrix P.δ₂ P.δm P.m (k (.inl cd0bF1)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0bF1)) *
          Dirac.gamma (lor (pg kCD0 2)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl cd0bF2)) *
          Dirac.gamma (lor (pg kCD0 3))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain4 (x₁ := fv kCD0 0) (x₂ := fv kCD0 1) (x₃ := fv kCD0 2)
      (x₄ := fv kCD0 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [cd0b_cond, Fin.prod_univ_five,
      prod_eq_of_three (by decide) (by decide) (by decide) cd0b_fermionLine_cases,
      prod_eq_of_two (by decide) cd0b_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD0 0 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show kCD0 1 = .fermionCt from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD0 2 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show kCD0 3 = .gauge from rfl),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (show kCD0 4 = .photonCt from rfl),
      cd0b_psiMomentum, cd0b_photonMomentum, t1, t2, t3, t4, t5, ite_and_eq_mul]
    simp only [show cd0bF0.1 = fv kCD0 0 from rfl, show cd0bF1.1 = fv kCD0 1 from rfl,
      show cd0bF2.1 = fv kCD0 2 from rfl, show cd0bGA.1 = pg kCD0 0 from rfl,
      show cd0bGB.1 = pg kCD0 3 from rfl, pcCD0_0, pcCD0_1, pg, fv, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero, fermionCtMatrix, photonCtFactor]
    ring
  · have n10 : pg kCD0 2 ≠ pg kCD0 0 := by decide
    have n30 : pg kCD0 3 ≠ pg kCD0 0 := by decide
    have n31 : pg kCD0 3 ≠ pg kCD0 2 := by decide
    have n40 : pc kCD0 4 0 ≠ pg kCD0 0 := by decide
    have n41 : pc kCD0 4 0 ≠ pg kCD0 2 := by decide
    have n43 : pc kCD0 4 0 ≠ pg kCD0 3 := by decide
    have m40 : pc kCD0 4 1 ≠ pg kCD0 0 := by decide
    have m41 : pc kCD0 4 1 ≠ pg kCD0 2 := by decide
    have m43 : pc kCD0 4 1 ≠ pg kCD0 3 := by decide
    have m44 : pc kCD0 4 1 ≠ pc kCD0 4 0 := by decide
    rw [sum_pi_five (x₁ := pg kCD0 0) (x₂ := pg kCD0 2) (x₃ := pg kCD0 3)
      (x₄ := pc kCD0 4 0) (x₅ := pc kCD0 4 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide +kernel)]
    simp only [ite_true, n10, n30, n31, n40, n41, n43, m40, m41, m43, m44, ite_false, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of `repCD0 1`**: under momentum conservation, the energy-first integral of the
one-loop vertex chain with the inserted electron line on the outgoing side and the inserted
photon line, at every `ε`. -/
theorem contractionValue₂_repCD0b (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P (repCD0 1) pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (electronInsertion P.m P.ε P.δ₂ P.δm (pOut 0 + ℓ))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + ℓ))
          (photonInsertion P.δ₃ P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P cd0b_isChord_iff (cd0bMom (pIn 0) (kIn 0))
    (cd0b_isConserved hmom) (fun ℓ => (cd0bMom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pOut 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4, m5⟩ := cd0bMom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 5) (by decide +kernel)),
    cd0b_amplitude, m1, m2, m3, m4, m5, vertexChain, electronInsertion, hmom,
    show pIn 0 + kIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ by abel,
    show pIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ - kIn 0 by abel,
    show ℓ - pIn 0 - kIn 0 = ℓ - (pIn 0 + kIn 0) by abel,
    show pIn 0 + kIn 0 - ℓ = -(ℓ - (pIn 0 + kIn 0)) by abel]
  simp only [photonPropagator_neg', photonCtFactor_neg, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply,
    Matrix.mul_assoc, photonInsertion]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [photonIns_swap']
  exact cd_const_aux _ _ _ _ _ _

end CD0b

end QED.ChainProof.SetCPauli

end
