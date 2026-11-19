/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Reduce
public import QED.TwoLoop.IntegrableOrderFiveCt
public import QED.WickModel.SelfEnergyExistsUnique

/-!
# The classes `C1`, `C2`: the one-loop self-energy with a `δ₁` vertex

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2. The representatives `repC1`, `repC2` of
`QED/GradedProof/SE2Classes.lean` have two vertices, a `gauge` and a `gaugeCt` vertex, one
internal electron line and one internal photon line. For each:

* the lines, their ends, the unique chord (T₁) and an explicit conserved routing, all checked by
  `decide +kernel`;
* the amplitude (T₇) at arbitrary line momenta (`c1_amplitude`, `c2_amplitude`);
* `(2π)⁻⁴` times the regulated amplitude (T₈) in the routing is `δ₁` times the one-loop
  self-energy integrand of (62.28) at the loop momentum `ℓ - p` (`c1_integrand`,
  `c2_integrand`);
* the class obligation `ClassInt` (`classInt_repC1`, `classInt_repC2`), from the integrability
  of the self-energy integrand at every `ε > 0` and every `p`
  (`QED.WickModel.SelfEnergyLimit.integrable_selfEnergyIntegrand_sub`).
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel
open Complex MeasureTheory

/-! ### Spinor sums of an open chain through two vertices -/

section Chain2

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A sum over the functions on a type covered by two distinct elements. -/
theorem sum_pi_two {R M : Type*} [Fintype R] [AddCommMonoid M] {x₁ x₂ : X} (h12 : x₁ ≠ x₂)
    (hX : ∀ x, x = x₁ ∨ x = x₂) (g : (X → R) → M) :
    ∑ f, g f = ∑ a, ∑ b, g (fun t => if t = x₁ then a else b) := by
  let e : (X → R) ≃ R × R :=
    { toFun := fun f => (f x₁, f x₂)
      invFun := fun q t => if t = x₁ then q.1 else q.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl <;> simp [h12.symm]
      right_inv := fun q => by simp [h12.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- **The spinor sum of an open chain through two vertices** `x₁, x₂` (outgoing vertex first). -/
theorem sum_spinor_chain2 {x₁ x₂ : X} (h12 : x₁ ≠ x₂) (hX : ∀ x, x = x₁ ∨ x = x₂) (c : ℂ)
    (A₁ A₂ S₁ : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      (if α x₁ = a ∧ β x₂ = b then (1 : ℂ) else 0) *
        (c * (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂))) =
      c * (A₁ * S₁ * A₂) a b := by
  have hs := fun (g : (X → Fin 4) → ℂ) => sum_pi_two h12 hX g
  simp only [hs, h12.symm, ite_false, ite_true]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]

end Chain2

/-- The external momenta (X₁₉) of a contraction with one external fermion pair and no external
photon. -/
theorem externalMomentum_one_zero {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 0 κ}
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ) (v : Fin N) :
    externalMomentum C pOut pIn kIn v =
      (if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl 0 then pIn 0 else 0) -
        (if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl 0) = .inr t then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

/-! ### `C1`: `δ₁` at the incoming vertex; fermion flow `1 → 0`, photon line `0 — 1` -/

section C1

/-- The electron line `1 → 0` of `repC1`. -/
def c1f : FermionLine repC1 := ⟨fvK k_gC 0, by decide +kernel⟩
/-- The photon line `0 → 1` of `repC1`. -/
def c1g : PhotonLine repC1 := ⟨psK k_gC 0 0, by decide +kernel⟩

theorem c1_fermionLine_cases : ∀ f : FermionLine repC1, f = c1f := by decide +kernel

theorem c1_photonLine_cases : ∀ g : PhotonLine repC1, g = c1g := by decide +kernel

theorem c1_line_cases : ∀ f : Line repC1, f = .inl c1f ∨ f = .inr c1g := by decide +kernel

theorem c1_isChord_iff : ∀ g : Line repC1, IsChord g ↔ g = .inl c1f := by decide +kernel

theorem c1_ends : (Line.ends (.inl c1f : Line repC1)) = (1, 0) ∧
    (Line.ends (.inr c1g : Line repC1)) = (0, 1) := by
  decide +kernel

theorem c1_tails : c1f.tail = fvK k_gC 1 ∧ c1g.head = psK k_gC 1 0 := by decide +kernel

theorem c1_ext (v : Fin 2) :
    ((∃ t : Wick.FermionVertex k_gC, t.1 = v ∧ repC1.1.1 (.inr t) = .inl 0) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex k_gC, t.1 = v ∧ repC1.1.1 (.inl 0) = .inr t) ↔ v = 0) := by
  revert v
  decide +kernel

/-- The routing of `repC1`: `ℓ` on the electron line, `ℓ - p` on the photon line. -/
def c1Mom (p ℓ : Fin 4 → ℝ) (f : Line repC1) : Fin 4 → ℝ :=
  if f = .inl c1f then ℓ else ℓ - p

theorem c1Mom_apply (p ℓ : Fin 4 → ℝ) :
    c1Mom p ℓ (.inl c1f) = ℓ ∧ c1Mom p ℓ (.inr c1g) = ℓ - p :=
  ⟨ite_eq_left rfl, ite_eq_right (by decide)⟩

theorem c1_isConserved (p ℓ : Fin 4 → ℝ) :
    IsConserved repC1 ![p] ![p] ![] (c1Mom p ℓ) := by
  obtain ⟨e1, e2⟩ := c1_ends
  obtain ⟨m1, m2⟩ := c1Mom_apply p ℓ
  intro v
  rw [inflow, sum_eq_of_two (by decide) c1_line_cases, externalMomentum_one_zero]
  obtain ⟨x1, x2⟩ := c1_ext v
  simp only [e1, e2, x1, x2, m1, m2, Matrix.cons_val_zero]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem c1_cond (α β : Wick.FermionVertex k_gC → Fin 4) (lor : Wick.PhotonSlot k_gC → Fin 4)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    ((∀ i t, repC1.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repC1.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repC1.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (α (fvK k_gC 0) = αOut 0 ∧ β (fvK k_gC 1) = βIn 0) := by
  have h1 : ∀ t, repC1.1.1 (.inl 0) = .inr t ↔ t = fvK k_gC 0 := by decide +kernel
  have h2 : ∀ t, repC1.1.1 (.inr t) = .inl 0 ↔ t = fvK k_gC 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, forall_eq, IsEmpty.forall_iff, and_true]

/-- **The amplitude of `repC1`** at arbitrary line momenta `k`. -/
theorem c1_amplitude (P : Params) (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ)
    (k : Line repC1 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    contractionAmplitude₂ P repC1 (zeroFlavoring k_gC) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 2 *
        ∑ ν, ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr c1g)) ρ ν *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl c1f)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2⟩ := c1_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_gC → Fin 4, ∑ β : Wick.FermionVertex k_gC → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gC → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_gC → Fin 4,
    ((I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 2 *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr c1g)) (lor (psK k_gC 0 0))
          (lor (psK k_gC 1 0)) *
        (Dirac.gamma (lor (psK k_gC 0 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl c1f)) *
          Dirac.gamma (lor (psK k_gC 1 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain2 (x₁ := fvK k_gC 0) (x₂ := fvK k_gC 1) (by decide)
      (by decide +kernel)]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [c1_cond, Fin.prod_univ_two, prod_eq_of_one c1_fermionLine_cases,
      prod_eq_of_one c1_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gC 0 = .gauge from rfl),
      vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ (show k_gC 1 = .gaugeCt from rfl),
      t1, t2]
    simp only [show c1f.1 = fvK k_gC 0 from rfl, show c1g.1 = psK k_gC 0 0 from rfl, psK, fvK,
      zeroFlavoring, Params.mass, Matrix.cons_val_zero]
    ring
  · have n01 : psK k_gC 0 0 ≠ psK k_gC 1 0 := by decide
    rw [sum_pi_two (x₁ := psK k_gC 0 0) (x₂ := psK k_gC 1 0) n01 (by decide +kernel)]
    simp only [ite_true, n01.symm, ite_false, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The integrand of `repC1`**: `δ₁` times the self-energy integrand at `ℓ - p`. -/
theorem c1_integrand (P : Params) (p ℓ : Fin 4 → ℝ) (α β : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repC1 ![p] ![] (c1Mom p ℓ) ![α] ![β] ![] =
      (P.δ₁ : ℂ) * selfEnergyIntegrand P P.ε p (ℓ - p) α β := by
  obtain ⟨m1, m2⟩ := c1Mom_apply p ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 3) (by decide +kernel)),
    c1_amplitude, m1, m2, selfEnergyIntegrand, show p + (ℓ - p) = ℓ by abel]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum,
    Matrix.cons_val_zero]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [photonPropagator_comm']
  push_cast
  ring

/-- **The class obligation for `C1`.** -/
theorem classInt_repC1 : ClassInt repC1 := by
  intro Q hQ p α β
  obtain ⟨h1, h2⟩ := SelfEnergyLimit.integrable_selfEnergyIntegrand_sub hQ.hε Q p 0 α β
  simp only [sub_zero] at h1 h2
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_one_chord Q c1_isChord_iff
    (c1Mom p) (c1_isConserved p) (fun ℓ => (c1Mom_apply p ℓ).1) ![α] ![β] ![]
    (fun q => (Q.δ₁ : ℂ) * selfEnergyIntegrand Q Q.ε p q α β) p
    (fun ℓ => c1_integrand Q p ℓ α β) (fun v => (h1 v).const_mul _)
    (by simpa only [integral_const_mul] using h2.const_mul (Q.δ₁ : ℂ))

end C1

/-! ### `C2`: `δ₁` at the outgoing vertex; fermion flow `0 → 1`, photon line `0 — 1` -/

section C2

/-- The electron line `0 → 1` of `repC2`. -/
def c2f : FermionLine repC2 := ⟨fvK k_gC 1, by decide +kernel⟩
/-- The photon line `0 → 1` of `repC2`. -/
def c2g : PhotonLine repC2 := ⟨psK k_gC 0 0, by decide +kernel⟩

theorem c2_fermionLine_cases : ∀ f : FermionLine repC2, f = c2f := by decide +kernel

theorem c2_photonLine_cases : ∀ g : PhotonLine repC2, g = c2g := by decide +kernel

theorem c2_line_cases : ∀ f : Line repC2, f = .inl c2f ∨ f = .inr c2g := by decide +kernel

theorem c2_isChord_iff : ∀ g : Line repC2, IsChord g ↔ g = .inl c2f := by decide +kernel

theorem c2_ends : (Line.ends (.inl c2f : Line repC2)) = (0, 1) ∧
    (Line.ends (.inr c2g : Line repC2)) = (0, 1) := by
  decide +kernel

theorem c2_tails : c2f.tail = fvK k_gC 0 ∧ c2g.head = psK k_gC 1 0 := by decide +kernel

theorem c2_ext (v : Fin 2) :
    ((∃ t : Wick.FermionVertex k_gC, t.1 = v ∧ repC2.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ t : Wick.FermionVertex k_gC, t.1 = v ∧ repC2.1.1 (.inl 0) = .inr t) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repC2`: `ℓ` on the electron line, `p - ℓ` on the photon line. -/
def c2Mom (p ℓ : Fin 4 → ℝ) (f : Line repC2) : Fin 4 → ℝ :=
  if f = .inl c2f then ℓ else p - ℓ

theorem c2Mom_apply (p ℓ : Fin 4 → ℝ) :
    c2Mom p ℓ (.inl c2f) = ℓ ∧ c2Mom p ℓ (.inr c2g) = p - ℓ :=
  ⟨ite_eq_left rfl, ite_eq_right (by decide)⟩

theorem c2_isConserved (p ℓ : Fin 4 → ℝ) :
    IsConserved repC2 ![p] ![p] ![] (c2Mom p ℓ) := by
  obtain ⟨e1, e2⟩ := c2_ends
  obtain ⟨m1, m2⟩ := c2Mom_apply p ℓ
  intro v
  rw [inflow, sum_eq_of_two (by decide) c2_line_cases, externalMomentum_one_zero]
  obtain ⟨x1, x2⟩ := c2_ext v
  simp only [e1, e2, x1, x2, m1, m2, Matrix.cons_val_zero]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem c2_cond (α β : Wick.FermionVertex k_gC → Fin 4) (lor : Wick.PhotonSlot k_gC → Fin 4)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    ((∀ i t, repC2.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repC2.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repC2.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (α (fvK k_gC 1) = αOut 0 ∧ β (fvK k_gC 0) = βIn 0) := by
  have h1 : ∀ t, repC2.1.1 (.inl 0) = .inr t ↔ t = fvK k_gC 1 := by decide +kernel
  have h2 : ∀ t, repC2.1.1 (.inr t) = .inl 0 ↔ t = fvK k_gC 0 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, forall_eq, IsEmpty.forall_iff, and_true]

/-- **The amplitude of `repC2`** at arbitrary line momenta `k`. -/
theorem c2_amplitude (P : Params) (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ)
    (k : Line repC2 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    contractionAmplitude₂ P repC2 (zeroFlavoring k_gC) pIn kIn k αOut βIn μ =
      (I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 2 *
        ∑ ν, ∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr c2g)) ν ρ *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (k (.inl c2f)) *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨t1, t2⟩ := c2_tails
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex k_gC → Fin 4, ∑ β : Wick.FermionVertex k_gC → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gC → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot k_gC → Fin 4,
    ((I * P.e) * (I * ((P.δ₁ * P.e : ℝ) : ℂ)) * (1 / I) ^ 2 *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr c2g)) (lor (psK k_gC 0 0))
          (lor (psK k_gC 1 0)) *
        (Dirac.gamma (lor (psK k_gC 1 0)) *
            QED.OneLoop.electronPropagator P.m P.ε (k (.inl c2f)) *
          Dirac.gamma (lor (psK k_gC 0 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain2 (x₁ := fvK k_gC 1) (x₂ := fvK k_gC 0) (by decide)
      (by decide +kernel)]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [c2_cond, Fin.prod_univ_two, prod_eq_of_one c2_fermionLine_cases,
      prod_eq_of_one c2_photonLine_cases,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (show k_gC 0 = .gauge from rfl),
      vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ (show k_gC 1 = .gaugeCt from rfl),
      t1, t2]
    simp only [show c2f.1 = fvK k_gC 1 from rfl, show c2g.1 = psK k_gC 0 0 from rfl, psK, fvK,
      zeroFlavoring, Params.mass, Matrix.cons_val_zero]
    ring
  · have n01 : psK k_gC 0 0 ≠ psK k_gC 1 0 := by decide
    rw [sum_pi_two (x₁ := psK k_gC 0 0) (x₂ := psK k_gC 1 0) n01 (by decide +kernel)]
    simp only [ite_true, n01.symm, ite_false, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The integrand of `repC2`**: `δ₁` times the self-energy integrand at `ℓ - p`. -/
theorem c2_integrand (P : Params) (p ℓ : Fin 4 → ℝ) (α β : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repC2 ![p] ![] (c2Mom p ℓ) ![α] ![β] ![] =
      (P.δ₁ : ℂ) * selfEnergyIntegrand P P.ε p (ℓ - p) α β := by
  obtain ⟨m1, m2⟩ := c2Mom_apply p ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (n := 3) (by decide +kernel)),
    c2_amplitude, m1, m2, selfEnergyIntegrand, show p + (ℓ - p) = ℓ by abel,
    show p - ℓ = -(ℓ - p) by abel]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum,
    Matrix.cons_val_zero]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [photonPropagator_neg']
  push_cast
  ring

/-- **The class obligation for `C2`.** -/
theorem classInt_repC2 : ClassInt repC2 := by
  intro Q hQ p α β
  obtain ⟨h1, h2⟩ := SelfEnergyLimit.integrable_selfEnergyIntegrand_sub hQ.hε Q p 0 α β
  simp only [sub_zero] at h1 h2
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_one_chord Q c2_isChord_iff
    (c2Mom p) (c2_isConserved p) (fun ℓ => (c2Mom_apply p ℓ).1) ![α] ![β] ![]
    (fun q => (Q.δ₁ : ℂ) * selfEnergyIntegrand Q Q.ε p q α β) p
    (fun ℓ => c2_integrand Q p ℓ α β) (fun v => (h1 v).const_mul _)
    (by simpa only [integral_const_mul] using h2.const_mul (Q.δ₁ : ℂ))

end C2

end QED.GradedProof.SE2

end
