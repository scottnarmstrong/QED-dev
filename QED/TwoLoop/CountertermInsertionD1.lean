/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermInsertionBasic
public import QED.TwoLoop.CountertermInsertionChain
public import QED.TwoLoop.CountertermInsertionAlgebra
public import QED.Integration.EnergyFirstShift

/-!
# The `δ₁` classes: explicit values

Part of obligation O2-13 (`docs/TWO-LOOP-DERIVATION.md`, section 5.1). The three counterterm
classes with one `gaugeCt` vertex (`repD1At1`, `repD1At2`, `repD1At3` of
`QED/TwoLoop/RelabelCountertermClasses.lean`: `δ₁` at `v₁`, at the external-photon vertex `v₂`,
at `v₃`) are one-loop vertex graphs. For each:

* the lines, their ends, the unique chord (T₁) and an explicit conserved routing, all checked by
  `decide +kernel` (the momenta by `ring`);
* `d1c*_amplitude`: the amplitude (T₇) at arbitrary line momenta is
  `(ie)² (i δ₁ e) (1/i)³ ∑_{νρ} Δ̃ (γ^ρ S̃ γ^μ S̃ γ^ν)`, by the index sums of
  `QED/TwoLoop/CountertermInsertionChain.lean`;
* `contractionValue₂_repD1At*`: **the value (T₁₀) is `δ₁` times the energy-first integral of the
  frozen one-loop vertex integrand (C)**, at every `ε`, under momentum conservation. The routing
  is that of (C) after a shift of the loop momentum (by `p`, `p'` or `p`), which leaves the
  energy-first integral unchanged.

The `gaugeCt` vertex factor is `δ₁` times the `gauge` factor (V₁₉), so no integrability is needed.
-/

@[expose] public section

namespace QED.TwoLoop.Insertion

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Relabel Complex

/-! ### `δ₁` at `v₁`: fermion flow `2 → 0 → 1`, external photon at `0`, photon line `1 — 2` -/

section D1At1

/-- The fermion line `2 → 0` of `repD1At1`. -/
def d1c1f0 : FermionLine repD1At1 := ⟨fvK k_ggC 0, by decide +kernel⟩
/-- The fermion line `0 → 1` of `repD1At1`. -/
def d1c1f1 : FermionLine repD1At1 := ⟨fvK k_ggC 1, by decide +kernel⟩
/-- The photon line `1 → 2` of `repD1At1`. -/
def d1c1g : PhotonLine repD1At1 := ⟨psK k_ggC 1 0, by decide +kernel⟩

theorem d1c1_fermionLine_cases : ∀ f : FermionLine repD1At1, f = d1c1f0 ∨ f = d1c1f1 := by
  decide +kernel

theorem d1c1_photonLine_cases : ∀ g : PhotonLine repD1At1, g = d1c1g := by
  decide +kernel

theorem d1c1_line_cases : ∀ f : Line repD1At1,
    f = .inl d1c1f0 ∨ f = .inl d1c1f1 ∨ f = .inr d1c1g := by
  decide +kernel

theorem d1c1_isChord_iff : ∀ g : Line repD1At1, IsChord g ↔ g = .inl d1c1f0 := by
  decide +kernel

theorem d1c1_ends : (Line.ends (.inl d1c1f0 : Line repD1At1)) = (2, 0) ∧
    (Line.ends (.inl d1c1f1 : Line repD1At1)) = (0, 1) ∧
    (Line.ends (.inr d1c1g : Line repD1At1)) = (1, 2) := by
  decide +kernel

theorem d1c1_tails : d1c1f0.tail = fvK k_ggC 2 ∧ d1c1f1.tail = fvK k_ggC 0 ∧
    d1c1g.head = psK k_ggC 2 0 := by
  decide +kernel

theorem d1c1_ext (v : Fin 3) :
    ((∃ t : Wick.FermionVertex k_ggC, t.1 = v ∧ repD1At1.1.1 (.inr t) = .inl 0) ↔ v = 2) ∧
    ((∃ a : Wick.PhotonSlot k_ggC, a.1 = v ∧ repD1At1.1.2 (.inl 0) = .inr a) ↔ v = 0) ∧
    ((∃ t : Wick.FermionVertex k_ggC, t.1 = v ∧ repD1At1.1.1 (.inl 0) = .inr t) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repD1At1`: `ℓ` on `2 → 0`, `ℓ + k` on `0 → 1`, `ℓ - p` on the photon. -/
def d1c1Mom (p k ℓ : Fin 4 → ℝ) (f : Line repD1At1) : Fin 4 → ℝ :=
  if f = .inl d1c1f0 then ℓ else if f = .inl d1c1f1 then ℓ + k else ℓ - p

theorem d1c1Mom_apply (p k ℓ : Fin 4 → ℝ) : d1c1Mom p k ℓ (.inl d1c1f0) = ℓ ∧
    d1c1Mom p k ℓ (.inl d1c1f1) = ℓ + k ∧ d1c1Mom p k ℓ (.inr d1c1g) = ℓ - p := by
  refine ⟨ite_eq_left rfl, ?_, ?_⟩
  · rw [d1c1Mom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d1c1Mom, ite_eq_right (by decide), ite_eq_right (by decide)]

theorem d1c1_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved repD1At1 pOut pIn kIn (d1c1Mom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3⟩ := d1c1_ends
  obtain ⟨m1, m2, m3⟩ := d1c1Mom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_eq_of_three (by decide) (by decide) (by decide) d1c1_line_cases,
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := d1c1_ext v
  simp only [e1, e2, e3, x1, x2, x3, m1, m2, m3]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem d1c1_cond (α β : Wick.FermionVertex k_ggC → Fin 4) (lor : Wick.PhotonSlot k_ggC → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repD1At1.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repD1At1.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repD1At1.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (psK k_ggC 0 0) = μ 0 ∧ (α (fvK k_ggC 1) = αOut 0 ∧ β (fvK k_ggC 2) = βIn 0) := by
  have h1 : ∀ t, repD1At1.1.1 (.inl 0) = .inr t ↔ t = fvK k_ggC 1 := by decide +kernel
  have h2 : ∀ t, repD1At1.1.1 (.inr t) = .inl 0 ↔ t = fvK k_ggC 2 := by decide +kernel
  have h3 : ∀ a, repD1At1.1.2 (.inl 0) = .inr a ↔ a = psK k_ggC 0 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- **The amplitude of `repD1At1`** at arbitrary line momenta `k`: the one-loop vertex chain
`γ^ρ S̃(k₀₁) γ^μ S̃(k₂₀) γ^ν Δ̃_{ρν}(k_γ)` with the coupling `(ie)² (i δ₁ e)` and `(1/i)³`. -/
theorem d1c1_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD1At1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repD1At1 (zeroFlavoring k_ggC) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 3 *
        ∑ ν, ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d1c1g)) ρ ν *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c1f1)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c1f0)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3⟩ := d1c1_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_ggC → Fin 4, ∑ β : Wick.FermionVertex k_ggC → Fin 4,
      ∑ lor : Wick.PhotonSlot k_ggC → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_ggC → Fin 4,
    (if lor (psK k_ggC 0 0) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 3 *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d1c1g)) (lor (psK k_ggC 1 0))
          (lor (psK k_ggC 2 0)) *
        (Dirac.gamma (lor (psK k_ggC 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c1f1)) *
          Dirac.gamma (lor (psK k_ggC 0 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c1f0)) *
          Dirac.gamma (lor (psK k_ggC 2 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain3 (x₁ := fvK k_ggC 1) (x₂ := fvK k_ggC 0) (x₃ := fvK k_ggC 2)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [d1c1_cond, Fin.prod_univ_three,
      prod_eq_of_two (by decide) d1c1_fermionLine_cases, prod_eq_of_one d1c1_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 1 = .gauge from rfl),
      vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 2 = .gaugeCt from rfl),
      t1, t2, t3, ite_and_eq_mul]
    simp only [show d1c1f0.1 = fvK k_ggC 0 from rfl, show d1c1f1.1 = fvK k_ggC 1 from rfl,
      show d1c1g.1 = psK k_ggC 1 0 from rfl, psK, fvK, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero]
    ring
  · have n02 : psK k_ggC 0 0 ≠ psK k_ggC 2 0 := by decide
    have n12 : psK k_ggC 1 0 ≠ psK k_ggC 2 0 := by decide
    have n10 : psK k_ggC 1 0 ≠ psK k_ggC 0 0 := by decide
    rw [sum_pi_three (x₁ := psK k_ggC 2 0) (x₂ := psK k_ggC 0 0) (x₃ := psK k_ggC 1 0)
      (by decide) (by decide) (by decide) (by decide +kernel)]
    simp only [ite_true, n02, n12, n10, ite_false, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of the class `δ₁` at `v₁`**: under momentum conservation, `δ₁` times the
energy-first integral of the frozen one-loop vertex integrand (C), at every `ε`. -/
theorem contractionValue₂_repD1At1 (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repD1At1 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * QED.OneLoop.energyFirstIntegral fun ℓ =>
        QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0) (μ 0) ℓ (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P d1c1_isChord_iff (d1c1Mom (pIn 0) (kIn 0))
    (d1c1_isConserved hmom) (fun ℓ => (d1c1Mom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pIn 0),
    ← energyFirstIntegral_const_mul']
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3⟩ := d1c1Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d1c1_amplitude, m1, m2, m3, QED.OneLoop.vertexIntegrand, hmom,
    show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [photonPropagator_comm']
  push_cast
  ring

end D1At1

/-! ### `δ₁` at `v₂`: fermion flow `0 → 2 → 1`, external photon at `2`, photon line `0 — 1` -/

section D1At2

/-- The fermion line `2 → 1` of `repD1At2`. -/
def d1c2f1 : FermionLine repD1At2 := ⟨fvK k_ggC 1, by decide +kernel⟩
/-- The fermion line `0 → 2` of `repD1At2`. -/
def d1c2f2 : FermionLine repD1At2 := ⟨fvK k_ggC 2, by decide +kernel⟩
/-- The photon line `0 → 1` of `repD1At2`. -/
def d1c2g : PhotonLine repD1At2 := ⟨psK k_ggC 0 0, by decide +kernel⟩

theorem d1c2_fermionLine_cases : ∀ f : FermionLine repD1At2, f = d1c2f1 ∨ f = d1c2f2 := by
  decide +kernel

theorem d1c2_photonLine_cases : ∀ g : PhotonLine repD1At2, g = d1c2g := by
  decide +kernel

theorem d1c2_line_cases : ∀ f : Line repD1At2,
    f = .inl d1c2f1 ∨ f = .inl d1c2f2 ∨ f = .inr d1c2g := by
  decide +kernel

theorem d1c2_isChord_iff : ∀ g : Line repD1At2, IsChord g ↔ g = .inl d1c2f1 := by
  decide +kernel

theorem d1c2_ends : (Line.ends (.inl d1c2f1 : Line repD1At2)) = (2, 1) ∧
    (Line.ends (.inl d1c2f2 : Line repD1At2)) = (0, 2) ∧
    (Line.ends (.inr d1c2g : Line repD1At2)) = (0, 1) := by
  decide +kernel

theorem d1c2_tails : d1c2f1.tail = fvK k_ggC 2 ∧ d1c2f2.tail = fvK k_ggC 0 ∧
    d1c2g.head = psK k_ggC 1 0 := by
  decide +kernel

theorem d1c2_ext (v : Fin 3) :
    ((∃ t : Wick.FermionVertex k_ggC, t.1 = v ∧ repD1At2.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_ggC, a.1 = v ∧ repD1At2.1.2 (.inl 0) = .inr a) ↔ v = 2) ∧
    ((∃ t : Wick.FermionVertex k_ggC, t.1 = v ∧ repD1At2.1.1 (.inl 0) = .inr t) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repD1At2`: `ℓ` on `2 → 1`, `ℓ - k` on `0 → 2`, `p + k - ℓ` on the photon. -/
def d1c2Mom (p k ℓ : Fin 4 → ℝ) (f : Line repD1At2) : Fin 4 → ℝ :=
  if f = .inl d1c2f1 then ℓ else if f = .inl d1c2f2 then ℓ - k else p + k - ℓ

theorem d1c2Mom_apply (p k ℓ : Fin 4 → ℝ) : d1c2Mom p k ℓ (.inl d1c2f1) = ℓ ∧
    d1c2Mom p k ℓ (.inl d1c2f2) = ℓ - k ∧ d1c2Mom p k ℓ (.inr d1c2g) = p + k - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_⟩
  · rw [d1c2Mom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d1c2Mom, ite_eq_right (by decide), ite_eq_right (by decide)]

theorem d1c2_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved repD1At2 pOut pIn kIn (d1c2Mom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3⟩ := d1c2_ends
  obtain ⟨m1, m2, m3⟩ := d1c2Mom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_eq_of_three (by decide) (by decide) (by decide) d1c2_line_cases,
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := d1c2_ext v
  simp only [e1, e2, e3, x1, x2, x3, m1, m2, m3]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem d1c2_cond (α β : Wick.FermionVertex k_ggC → Fin 4) (lor : Wick.PhotonSlot k_ggC → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repD1At2.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repD1At2.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repD1At2.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (psK k_ggC 2 0) = μ 0 ∧ (α (fvK k_ggC 1) = αOut 0 ∧ β (fvK k_ggC 0) = βIn 0) := by
  have h1 : ∀ t, repD1At2.1.1 (.inl 0) = .inr t ↔ t = fvK k_ggC 1 := by decide +kernel
  have h2 : ∀ t, repD1At2.1.1 (.inr t) = .inl 0 ↔ t = fvK k_ggC 0 := by decide +kernel
  have h3 : ∀ a, repD1At2.1.2 (.inl 0) = .inr a ↔ a = psK k_ggC 2 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- **The amplitude of `repD1At2`** at arbitrary line momenta `k`: the one-loop vertex chain
`γ^ρ S̃(k₂₁) γ^μ S̃(k₀₂) γ^ν Δ̃_{νρ}(k_γ)` with the coupling `(ie)² (i δ₁ e)` and `(1/i)³`. -/
theorem d1c2_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD1At2 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repD1At2 (zeroFlavoring k_ggC) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 3 *
        ∑ ν, ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d1c2g)) ν ρ *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c2f1)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c2f2)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3⟩ := d1c2_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_ggC → Fin 4, ∑ β : Wick.FermionVertex k_ggC → Fin 4,
      ∑ lor : Wick.PhotonSlot k_ggC → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_ggC → Fin 4,
    (if lor (psK k_ggC 2 0) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 3 *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d1c2g)) (lor (psK k_ggC 0 0))
          (lor (psK k_ggC 1 0)) *
        (Dirac.gamma (lor (psK k_ggC 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c2f1)) *
          Dirac.gamma (lor (psK k_ggC 2 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c2f2)) *
          Dirac.gamma (lor (psK k_ggC 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain3 (x₁ := fvK k_ggC 1) (x₂ := fvK k_ggC 2) (x₃ := fvK k_ggC 0)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [d1c2_cond, Fin.prod_univ_three,
      prod_eq_of_two (by decide) d1c2_fermionLine_cases, prod_eq_of_one d1c2_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 1 = .gauge from rfl),
      vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 2 = .gaugeCt from rfl),
      t1, t2, t3, ite_and_eq_mul]
    simp only [show d1c2f1.1 = fvK k_ggC 1 from rfl, show d1c2f2.1 = fvK k_ggC 2 from rfl,
      show d1c2g.1 = psK k_ggC 0 0 from rfl, psK, fvK, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero]
    ring
  · have n20 : psK k_ggC 2 0 ≠ psK k_ggC 0 0 := by decide
    have n10 : psK k_ggC 1 0 ≠ psK k_ggC 0 0 := by decide
    have n12 : psK k_ggC 1 0 ≠ psK k_ggC 2 0 := by decide
    rw [sum_pi_three (x₁ := psK k_ggC 0 0) (x₂ := psK k_ggC 2 0) (x₃ := psK k_ggC 1 0)
      (by decide) (by decide) (by decide) (by decide +kernel)]
    simp only [ite_true, n20, n10, n12, ite_false, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of the class `δ₁` at the external-photon vertex `v₂`**: under momentum
conservation, `δ₁` times the energy-first integral of the frozen one-loop vertex integrand (C), at
every `ε`. -/
theorem contractionValue₂_repD1At2 (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repD1At2 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * QED.OneLoop.energyFirstIntegral fun ℓ =>
        QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0) (μ 0) ℓ (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P d1c2_isChord_iff (d1c2Mom (pIn 0) (kIn 0))
    (d1c2_isConserved hmom) (fun ℓ => (d1c2Mom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pIn 0 + kIn 0),
    ← energyFirstIntegral_const_mul']
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3⟩ := d1c2Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d1c2_amplitude, m1, m2, m3, QED.OneLoop.vertexIntegrand, hmom,
    show pIn 0 + kIn 0 - ℓ = -(ℓ - (pIn 0 + kIn 0)) by abel,
    show pIn 0 + kIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ by abel,
    show pIn 0 + (ℓ - (pIn 0 + kIn 0)) = ℓ - kIn 0 by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

end D1At2

/-! ### `δ₁` at `v₃`: fermion flow `0 → 1 → 2`, external photon at `1`, photon line `0 — 2` -/

section D1At3

/-- The fermion line `0 → 1` of `repD1At3`. -/
def d1c3f1 : FermionLine repD1At3 := ⟨fvK k_ggC 1, by decide +kernel⟩
/-- The fermion line `1 → 2` of `repD1At3`. -/
def d1c3f2 : FermionLine repD1At3 := ⟨fvK k_ggC 2, by decide +kernel⟩
/-- The photon line `0 → 2` of `repD1At3`. -/
def d1c3g : PhotonLine repD1At3 := ⟨psK k_ggC 0 0, by decide +kernel⟩

theorem d1c3_fermionLine_cases : ∀ f : FermionLine repD1At3, f = d1c3f1 ∨ f = d1c3f2 := by
  decide +kernel

theorem d1c3_photonLine_cases : ∀ g : PhotonLine repD1At3, g = d1c3g := by
  decide +kernel

theorem d1c3_line_cases : ∀ f : Line repD1At3,
    f = .inl d1c3f1 ∨ f = .inl d1c3f2 ∨ f = .inr d1c3g := by
  decide +kernel

theorem d1c3_isChord_iff : ∀ g : Line repD1At3, IsChord g ↔ g = .inl d1c3f1 := by
  decide +kernel

theorem d1c3_ends : (Line.ends (.inl d1c3f1 : Line repD1At3)) = (0, 1) ∧
    (Line.ends (.inl d1c3f2 : Line repD1At3)) = (1, 2) ∧
    (Line.ends (.inr d1c3g : Line repD1At3)) = (0, 2) := by
  decide +kernel

theorem d1c3_tails : d1c3f1.tail = fvK k_ggC 0 ∧ d1c3f2.tail = fvK k_ggC 1 ∧
    d1c3g.head = psK k_ggC 2 0 := by
  decide +kernel

theorem d1c3_ext (v : Fin 3) :
    ((∃ t : Wick.FermionVertex k_ggC, t.1 = v ∧ repD1At3.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_ggC, a.1 = v ∧ repD1At3.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex k_ggC, t.1 = v ∧ repD1At3.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- The routing of `repD1At3`: `ℓ` on `0 → 1`, `ℓ + k` on `1 → 2`, `p - ℓ` on the photon. -/
def d1c3Mom (p k ℓ : Fin 4 → ℝ) (f : Line repD1At3) : Fin 4 → ℝ :=
  if f = .inl d1c3f1 then ℓ else if f = .inl d1c3f2 then ℓ + k else p - ℓ

theorem d1c3Mom_apply (p k ℓ : Fin 4 → ℝ) : d1c3Mom p k ℓ (.inl d1c3f1) = ℓ ∧
    d1c3Mom p k ℓ (.inl d1c3f2) = ℓ + k ∧ d1c3Mom p k ℓ (.inr d1c3g) = p - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_⟩
  · rw [d1c3Mom, ite_eq_right (by decide), ite_eq_left rfl]
  · rw [d1c3Mom, ite_eq_right (by decide), ite_eq_right (by decide)]

theorem d1c3_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved repD1At3 pOut pIn kIn (d1c3Mom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3⟩ := d1c3_ends
  obtain ⟨m1, m2, m3⟩ := d1c3Mom_apply (pIn 0) (kIn 0) ℓ
  intro v
  rw [inflow, sum_eq_of_three (by decide) (by decide) (by decide) d1c3_line_cases,
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := d1c3_ext v
  simp only [e1, e2, e3, x1, x2, x3, m1, m2, m3]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)


theorem d1c3_cond (α β : Wick.FermionVertex k_ggC → Fin 4) (lor : Wick.PhotonSlot k_ggC → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repD1At3.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repD1At3.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repD1At3.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (psK k_ggC 1 0) = μ 0 ∧ (α (fvK k_ggC 2) = αOut 0 ∧ β (fvK k_ggC 0) = βIn 0) := by
  have h1 : ∀ t, repD1At3.1.1 (.inl 0) = .inr t ↔ t = fvK k_ggC 2 := by decide +kernel
  have h2 : ∀ t, repD1At3.1.1 (.inr t) = .inl 0 ↔ t = fvK k_ggC 0 := by decide +kernel
  have h3 : ∀ a, repD1At3.1.2 (.inl 0) = .inr a ↔ a = psK k_ggC 1 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- **The amplitude of `repD1At3`** at arbitrary line momenta `k`: the one-loop vertex chain
`γ^ρ S̃(k₁₂) γ^μ S̃(k₀₁) γ^ν Δ̃_{νρ}(k_γ)` with the coupling `(ie)² (i δ₁ e)` and `(1/i)³`. -/
theorem d1c3_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (k : Line repD1At3 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repD1At3 (zeroFlavoring k_ggC) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 3 *
        ∑ ν, ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d1c3g)) ν ρ *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c3f2)) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c3f1)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2, t3⟩ := d1c3_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_ggC → Fin 4, ∑ β : Wick.FermionVertex k_ggC → Fin 4,
      ∑ lor : Wick.PhotonSlot k_ggC → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_ggC → Fin 4,
    (if lor (psK k_ggC 1 0) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 3 *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr d1c3g)) (lor (psK k_ggC 0 0))
          (lor (psK k_ggC 2 0)) *
        (Dirac.gamma (lor (psK k_ggC 2 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c3f2)) *
          Dirac.gamma (lor (psK k_ggC 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl d1c3f1)) *
          Dirac.gamma (lor (psK k_ggC 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain3 (x₁ := fvK k_ggC 2) (x₂ := fvK k_ggC 1) (x₃ := fvK k_ggC 0)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [d1c3_cond, Fin.prod_univ_three,
      prod_eq_of_two (by decide) d1c3_fermionLine_cases, prod_eq_of_one d1c3_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 0 = .gauge from rfl),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 1 = .gauge from rfl),
      vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ (show k_ggC 2 = .gaugeCt from rfl),
      t1, t2, t3, ite_and_eq_mul]
    simp only [show d1c3f1.1 = fvK k_ggC 1 from rfl, show d1c3f2.1 = fvK k_ggC 2 from rfl,
      show d1c3g.1 = psK k_ggC 0 0 from rfl, psK, fvK, zeroFlavoring, Params.mass,
      Matrix.cons_val_zero]
    ring
  · have n10 : psK k_ggC 1 0 ≠ psK k_ggC 0 0 := by decide
    have n20 : psK k_ggC 2 0 ≠ psK k_ggC 0 0 := by decide
    have n21 : psK k_ggC 2 0 ≠ psK k_ggC 1 0 := by decide
    rw [sum_pi_three (x₁ := psK k_ggC 0 0) (x₂ := psK k_ggC 1 0) (x₃ := psK k_ggC 2 0)
      (by decide) (by decide) (by decide) (by decide +kernel)]
    simp only [ite_true, n10, n20, n21, ite_false, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The value of the class `δ₁` at `v₃`**: under momentum conservation, `δ₁` times the
energy-first integral of the frozen one-loop vertex integrand (C), at every `ε`. -/
theorem contractionValue₂_repD1At3 (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repD1At3 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * QED.OneLoop.energyFirstIntegral fun ℓ =>
        QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε (pOut 0) (pIn 0) (μ 0) ℓ (αOut 0) (βIn 0) := by
  rw [contractionValue₂_eq_energyFirstIntegral P d1c3_isChord_iff (d1c3Mom (pIn 0) (kIn 0))
    (d1c3_isConserved hmom) (fun ℓ => (d1c3Mom_apply _ _ ℓ).1)]
  conv_rhs => rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self _ (pIn 0),
    ← energyFirstIntegral_const_mul']
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  obtain ⟨m1, m2, m3⟩ := d1c3Mom_apply (pIn 0) (kIn 0) ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 4) (by decide +kernel)),
    d1c3_amplitude, m1, m2, m3, QED.OneLoop.vertexIntegrand, hmom,
    show pIn 0 - ℓ = -(ℓ - pIn 0) by abel, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [photonPropagator_neg', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

end D1At3

end QED.TwoLoop.Insertion

end
