/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermInsertionD1

/-!
# The `δ₂`, `δ_m` classes: explicit values

Part of obligation O2-13 (`docs/TWO-LOOP-DERIVATION.md`, section 5.1). The two counterterm
classes with one `fermionCt` vertex (`repD2In`, `repD2Out`: the insertion on the incoming,
resp. outgoing, internal electron line) are one-loop vertex graphs with four vertices. For each:

* the lines, ends, chord and a conserved routing (`decide +kernel`, `ring`); both electron lines
  next to the `fermionCt` vertex carry the same momentum, and the vertex factor
  `-i (δ₂ k̸ + δ_m m)` is evaluated at the momentum entering through its `Ψ` (T₅);
* `d2*_amplitude`: the amplitude (T₇) at arbitrary line momenta is
  `(ie)³ (-i) (1/i)⁴ ∑_{νρ} Δ̃ (γ^ρ ⋯ S̃ (δ₂ k̸ + δ_m m) S̃ ⋯ γ^ν)`;
* `contractionValue₂_repD2In`, `contractionValue₂_repD2Out`: **the value (T₁₀) is the
  energy-first integral of the one-loop vertex chain with the inserted electron line
  `electronInsertion` in place of the incoming, resp. outgoing, propagator**, at every `ε`,
  under momentum conservation, with no integrability hypothesis.

The reduction of the inserted line (`electronInsertion_eq`) is in
`QED/TwoLoop/CountertermInsertionAlgebra.lean`, the value identities in
`QED/TwoLoop/CountertermInsertion.lean`.
-/

@[expose] public section

namespace QED.TwoLoop.Insertion

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Relabel Complex

/-! ### `δ₂`, `δ_m` on the incoming line: fermion flow `0 → 3 → 1 → 2`, external photon at `1`,
photon line `0 — 2` -/

section D2In

/-- The fermion line `0 → 3` of `repD2In`. -/
def d2if3 : FermionLine repD2In := ⟨fvK k_gggf 3, by decide +kernel⟩
/-- The fermion line `3 → 1` of `repD2In`. -/
def d2if1 : FermionLine repD2In := ⟨fvK k_gggf 1, by decide +kernel⟩
/-- The fermion line `1 → 2` of `repD2In`. -/
def d2if2 : FermionLine repD2In := ⟨fvK k_gggf 2, by decide +kernel⟩
/-- The photon line `0 → 2` of `repD2In`. -/
def d2ig : PhotonLine repD2In := ⟨psK k_gggf 0 0, by decide +kernel⟩

theorem d2i_fermionLine_cases : ∀ f : FermionLine repD2In, f = d2if3 ∨ f = d2if1 ∨ f = d2if2 := by
  decide +kernel

theorem d2i_photonLine_cases : ∀ g : PhotonLine repD2In, g = d2ig := by
  decide +kernel

theorem d2i_line_cases : ∀ f : Line repD2In,
    f = .inl d2if3 ∨ f = .inl d2if1 ∨ f = .inl d2if2 ∨ f = .inr d2ig := by
  decide +kernel

theorem d2i_isChord_iff : ∀ g : Line repD2In, IsChord g ↔ g = .inl d2if1 := by
  decide +kernel

theorem d2i_ends : (Line.ends (.inl d2if3 : Line repD2In)) = (0, 3) ∧
    (Line.ends (.inl d2if1 : Line repD2In)) = (3, 1) ∧
    (Line.ends (.inl d2if2 : Line repD2In)) = (1, 2) ∧
    (Line.ends (.inr d2ig : Line repD2In)) = (0, 2) := by
  decide +kernel

theorem d2i_tails : d2if3.tail = fvK k_gggf 0 ∧ d2if1.tail = fvK k_gggf 3 ∧
    d2if2.tail = fvK k_gggf 1 ∧ d2ig.head = psK k_gggf 2 0 := by
  decide +kernel

theorem d2i_ext (v : Fin 4) :
    ((∃ t : Wick.FermionVertex k_gggf, t.1 = v ∧ repD2In.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_gggf, a.1 = v ∧ repD2In.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex k_gggf, t.1 = v ∧ repD2In.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- The routing of `repD2In`: `ℓ` on `0 → 3` and `3 → 1`, `ℓ + k` on `1 → 2`, `p - ℓ` on the
photon. -/
def d2iMom (p k ℓ : Fin 4 → ℝ) (f : Line repD2In) : Fin 4 → ℝ :=
  if f = .inl d2if3 then ℓ else if f = .inl d2if1 then ℓ else if f = .inl d2if2 then ℓ + k
    else p - ℓ

theorem d2iMom_apply (p k ℓ : Fin 4 → ℝ) : d2iMom p k ℓ (.inl d2if3) = ℓ ∧
    d2iMom p k ℓ (.inl d2if1) = ℓ ∧ d2iMom p k ℓ (.inl d2if2) = ℓ + k ∧
    d2iMom p k ℓ (.inr d2ig) = p - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_⟩
  · rw [d2iMom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d2iMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d2iMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

theorem d2i_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved repD2In pOut pIn kIn (d2iMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4⟩ := d2i_ends
  obtain ⟨m1, m2, m3, m4⟩ := d2iMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_eq_of_four (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) d2i_line_cases, externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := d2i_ext v
  simp only [e1, e2, e3, e4, x1, x2, x3, m1, m2, m3, m4]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem d2i_cond (α β : Wick.FermionVertex k_gggf → Fin 4) (lor : Wick.PhotonSlot k_gggf → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repD2In.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repD2In.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repD2In.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (psK k_gggf 1 0) = μ 0 ∧ (α (fvK k_gggf 2) = αOut 0 ∧ β (fvK k_gggf 0) = βIn 0) := by
  have h1 : ∀ t, repD2In.1.1 (.inl 0) = .inr t ↔ t = fvK k_gggf 2 := by decide +kernel
  have h2 : ∀ t, repD2In.1.1 (.inr t) = .inl 0 ↔ t = fvK k_gggf 0 := by decide +kernel
  have h3 : ∀ a, repD2In.1.2 (.inl 0) = .inr a ↔ a = psK k_gggf 1 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem d2i_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line repD2In → Fin 4 → ℝ) :
    psiMomentum₂ repD2In pIn k ⟨3, by decide⟩ = k (.inl d2if3) :=
  psiMomentum₂_of_isRight (by decide +kernel)

/-- **The amplitude of `repD2In`** at arbitrary line momenta `k`: the chain
`γ^ρ S̃(k₁₂) γ^μ S̃(k₃₁) (δ₂ k̸₀₃ + δ_m m) S̃(k₀₃) γ^ν Δ̃_{νρ}(k_γ)` with the coupling `(ie)³ (-i)` and
`(1/i)⁴`. -/
theorem d2i_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD2In → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repD2In (zeroFlavoring k_gggf) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ∑ ν, ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d2ig)) ν ρ *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2if2)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2if1)) *
            fermionCtMatrix P.δ₂ P.δm P.m (k (.inl d2if3)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2if3)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3, t4⟩ := d2i_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_gggf → Fin 4, ∑ β : Wick.FermionVertex k_gggf → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gggf → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_gggf → Fin 4,
    (if lor (psK k_gggf 1 0) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d2ig)) (lor (psK k_gggf 0 0))
          (lor (psK k_gggf 2 0)) *
        (Dirac.gamma (lor (psK k_gggf 2 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2if2)) *
          Dirac.gamma (lor (psK k_gggf 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2if1)) *
          fermionCtMatrix P.δ₂ P.δm P.m (k (.inl d2if3)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2if3)) *
          Dirac.gamma (lor (psK k_gggf 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain4 (x₁ := fvK k_gggf 2) (x₂ := fvK k_gggf 1) (x₃ := fvK k_gggf 3)
      (x₄ := fvK k_gggf 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [d2i_cond, Fin.prod_univ_four,
      prod_eq_of_three (by decide) (by decide) (by decide) d2i_fermionLine_cases,
      prod_eq_of_one d2i_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggf 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggf 1 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggf 2 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show k_gggf 3 = .fermionCt from rfl),
      d2i_psiMomentum, t1, t2, t3, t4, ite_and_eq_mul]
    simp only [show d2if3.1 = fvK k_gggf 3 from rfl, show d2if1.1 = fvK k_gggf 1 from rfl,
      show d2if2.1 = fvK k_gggf 2 from rfl, show d2ig.1 = psK k_gggf 0 0 from rfl, psK, fvK,
      zeroFlavoring, Params.mass, Matrix.cons_val_zero, fermionCtMatrix]
    ring
  · have n10 : psK k_gggf 1 0 ≠ psK k_gggf 0 0 := by decide
    have n20 : psK k_gggf 2 0 ≠ psK k_gggf 0 0 := by decide
    have n21 : psK k_gggf 2 0 ≠ psK k_gggf 1 0 := by decide
    rw [sum_pi_three (x₁ := psK k_gggf 0 0) (x₂ := psK k_gggf 1 0) (x₃ := psK k_gggf 2 0)
      (by decide) (by decide) (by decide) (by decide +kernel)]
    simp only [ite_true, n10, n20, n21, ite_false, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of the class `δ₂`, `δ_m` on the incoming internal electron line**: under momentum
conservation, the energy-first integral of the one-loop vertex chain whose incoming electron
factor is the inserted line `-S̃(p + ℓ) (δ₂ (p̸ + ℓ̸) + δ_m m) S̃(p + ℓ)`, at every `ε`. -/
theorem contractionValue₂_repD2In (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repD2In pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + ℓ))
          (electronInsertion P.m P.ε P.δ₂ P.δm (pIn 0 + ℓ))
          (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P d2i_isChord_iff (d2iMom (pIn 0) (kIn 0))
    (d2i_isConserved hmom) (fun ℓ => (d2iMom_apply _ _ ℓ).2.1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pIn 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4⟩ := d2iMom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 5) (by decide +kernel)),
    d2i_amplitude, m1, m2, m3, m4, vertexChain, electronInsertion, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_assoc]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  field_simp

end D2In

/-! ### `δ₂`, `δ_m` on the outgoing line: fermion flow `0 → 1 → 3 → 2`, external photon at `1`,
photon line `0 — 2` -/

section D2Out

/-- The fermion line `0 → 1` of `repD2Out`. -/
def d2of1 : FermionLine repD2Out := ⟨fvK k_gggf 1, by decide +kernel⟩
/-- The fermion line `1 → 3` of `repD2Out`. -/
def d2of3 : FermionLine repD2Out := ⟨fvK k_gggf 3, by decide +kernel⟩
/-- The fermion line `3 → 2` of `repD2Out`. -/
def d2of2 : FermionLine repD2Out := ⟨fvK k_gggf 2, by decide +kernel⟩
/-- The photon line `0 → 2` of `repD2Out`. -/
def d2og : PhotonLine repD2Out := ⟨psK k_gggf 0 0, by decide +kernel⟩

theorem d2o_fermionLine_cases : ∀ f : FermionLine repD2Out, f = d2of1 ∨ f = d2of3 ∨ f = d2of2 := by
  decide +kernel

theorem d2o_photonLine_cases : ∀ g : PhotonLine repD2Out, g = d2og := by
  decide +kernel

theorem d2o_line_cases : ∀ f : Line repD2Out,
    f = .inl d2of1 ∨ f = .inl d2of3 ∨ f = .inl d2of2 ∨ f = .inr d2og := by
  decide +kernel

theorem d2o_isChord_iff : ∀ g : Line repD2Out, IsChord g ↔ g = .inl d2of1 := by
  decide +kernel

theorem d2o_ends : (Line.ends (.inl d2of1 : Line repD2Out)) = (0, 1) ∧
    (Line.ends (.inl d2of3 : Line repD2Out)) = (1, 3) ∧
    (Line.ends (.inl d2of2 : Line repD2Out)) = (3, 2) ∧
    (Line.ends (.inr d2og : Line repD2Out)) = (0, 2) := by
  decide +kernel

theorem d2o_tails : d2of1.tail = fvK k_gggf 0 ∧ d2of3.tail = fvK k_gggf 1 ∧
    d2of2.tail = fvK k_gggf 3 ∧ d2og.head = psK k_gggf 2 0 := by
  decide +kernel

theorem d2o_ext (v : Fin 4) :
    ((∃ t : Wick.FermionVertex k_gggf, t.1 = v ∧ repD2Out.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_gggf, a.1 = v ∧ repD2Out.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex k_gggf, t.1 = v ∧ repD2Out.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- The routing of `repD2Out`: `ℓ` on `0 → 1`, `ℓ + k` on `1 → 3` and `3 → 2`, `p - ℓ` on the
photon. -/
def d2oMom (p k ℓ : Fin 4 → ℝ) (f : Line repD2Out) : Fin 4 → ℝ :=
  if f = .inl d2of1 then ℓ else if f = .inl d2of3 then ℓ + k else if f = .inl d2of2 then ℓ + k
    else p - ℓ

theorem d2oMom_apply (p k ℓ : Fin 4 → ℝ) : d2oMom p k ℓ (.inl d2of1) = ℓ ∧
    d2oMom p k ℓ (.inl d2of3) = ℓ + k ∧ d2oMom p k ℓ (.inl d2of2) = ℓ + k ∧
    d2oMom p k ℓ (.inr d2og) = p - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_⟩
  · rw [d2oMom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d2oMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d2oMom, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

theorem d2o_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved repD2Out pOut pIn kIn (d2oMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4⟩ := d2o_ends
  obtain ⟨m1, m2, m3, m4⟩ := d2oMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_eq_of_four (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) d2o_line_cases, externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := d2o_ext v
  simp only [e1, e2, e3, e4, x1, x2, x3, m1, m2, m3, m4]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem d2o_cond (α β : Wick.FermionVertex k_gggf → Fin 4) (lor : Wick.PhotonSlot k_gggf → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repD2Out.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repD2Out.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repD2Out.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (psK k_gggf 1 0) = μ 0 ∧ (α (fvK k_gggf 2) = αOut 0 ∧ β (fvK k_gggf 0) = βIn 0) := by
  have h1 : ∀ t, repD2Out.1.1 (.inl 0) = .inr t ↔ t = fvK k_gggf 2 := by decide +kernel
  have h2 : ∀ t, repD2Out.1.1 (.inr t) = .inl 0 ↔ t = fvK k_gggf 0 := by decide +kernel
  have h3 : ∀ a, repD2Out.1.2 (.inl 0) = .inr a ↔ a = psK k_gggf 1 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem d2o_psiMomentum (pIn : Fin 1 → Fin 4 → ℝ) (k : Line repD2Out → Fin 4 → ℝ) :
    psiMomentum₂ repD2Out pIn k ⟨3, by decide⟩ = k (.inl d2of3) :=
  psiMomentum₂_of_isRight (by decide +kernel)

/-- **The amplitude of `repD2Out`** at arbitrary line momenta `k`: the chain
`γ^ρ S̃(k₃₂) (δ₂ k̸₁₃ + δ_m m) S̃(k₁₃) γ^μ S̃(k₀₁) γ^ν Δ̃_{νρ}(k_γ)` with the coupling `(ie)³ (-i)` and
`(1/i)⁴`. -/
theorem d2o_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD2Out → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repD2Out (zeroFlavoring k_gggf) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        ∑ ν, ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d2og)) ν ρ *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2of2)) *
            fermionCtMatrix P.δ₂ P.δm P.m (k (.inl d2of3)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2of3)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2of1)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3, t4⟩ := d2o_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_gggf → Fin 4, ∑ β : Wick.FermionVertex k_gggf → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gggf → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_gggf → Fin 4,
    (if lor (psK k_gggf 1 0) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 4 *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d2og)) (lor (psK k_gggf 0 0))
          (lor (psK k_gggf 2 0)) *
        (Dirac.gamma (lor (psK k_gggf 2 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2of2)) *
          fermionCtMatrix P.δ₂ P.δm P.m (k (.inl d2of3)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2of3)) *
          Dirac.gamma (lor (psK k_gggf 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d2of1)) *
          Dirac.gamma (lor (psK k_gggf 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain4 (x₁ := fvK k_gggf 2) (x₂ := fvK k_gggf 3) (x₃ := fvK k_gggf 1)
      (x₄ := fvK k_gggf 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [d2o_cond, Fin.prod_univ_four,
      prod_eq_of_three (by decide) (by decide) (by decide) d2o_fermionLine_cases,
      prod_eq_of_one d2o_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggf 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggf 1 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gggf 2 = .gauge from rfl),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (show k_gggf 3 = .fermionCt from rfl),
      d2o_psiMomentum, t1, t2, t3, t4, ite_and_eq_mul]
    simp only [show d2of1.1 = fvK k_gggf 1 from rfl, show d2of3.1 = fvK k_gggf 3 from rfl,
      show d2of2.1 = fvK k_gggf 2 from rfl, show d2og.1 = psK k_gggf 0 0 from rfl, psK, fvK,
      zeroFlavoring, Params.mass, Matrix.cons_val_zero, fermionCtMatrix]
    ring
  · have n10 : psK k_gggf 1 0 ≠ psK k_gggf 0 0 := by decide
    have n20 : psK k_gggf 2 0 ≠ psK k_gggf 0 0 := by decide
    have n21 : psK k_gggf 2 0 ≠ psK k_gggf 1 0 := by decide
    rw [sum_pi_three (x₁ := psK k_gggf 0 0) (x₂ := psK k_gggf 1 0) (x₃ := psK k_gggf 2 0)
      (by decide) (by decide) (by decide) (by decide +kernel)]
    simp only [ite_true, n10, n20, n21, ite_false, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of the class `δ₂`, `δ_m` on the outgoing internal electron line**: under momentum
conservation, the energy-first integral of the one-loop vertex chain whose outgoing electron
factor is the inserted line `-S̃(p' + ℓ) (δ₂ (p̸' + ℓ̸) + δ_m m) S̃(p' + ℓ)`, at every `ε`. -/
theorem contractionValue₂_repD2Out (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repD2Out pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        vertexChain P.e (μ 0) (electronInsertion P.m P.ε P.δ₂ P.δm (pOut 0 + ℓ))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + ℓ))
          (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ℓ) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P d2o_isChord_iff (d2oMom (pIn 0) (kIn 0))
    (d2o_isConserved hmom) (fun ℓ => (d2oMom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pIn 0)]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3, m4⟩ := d2oMom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 5) (by decide +kernel)),
    d2o_amplitude, m1, m2, m3, m4, vertexChain, electronInsertion, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_assoc]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  field_simp

end D2Out

end QED.TwoLoop.Insertion

end
