/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2ClassG

/-!
# The classes `G0`, `G1`: lines, routing, amplitude and the class obligations

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2:
`classInt2_repG0`, `classInt2_repG1`. See `QED/GradedProof/VP2ClassG.lean` for the analytic part
(`energyFirst_blockBubble`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Insertion
open QED.GradedProof.SE2 (k_gC k_ggf k_gggg)
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂ Line FermionLine
  PhotonLine IsChord externalMomentum vacuumPolarizationIntegrand)

/-- The sum over the Lorentz indices of two photon slots fixed by the external photons. -/
theorem sum_lor_two {X : Type*} [Fintype X] [DecidableEq X] {x₁ x₂ : X} (h12 : x₁ ≠ x₂)
    (hX : ∀ x, x = x₁ ∨ x = x₂) (μ ν : Fin 4) (G : (X → Fin 4) → ℂ) :
    ∑ lor : X → Fin 4, (if lor x₁ = μ ∧ lor x₂ = ν then (1 : ℂ) else 0) * G lor =
      G (fun x => if x = x₁ then μ else ν) := by
  rw [SE2.sum_pi_two h12 hX]
  simp only [ite_true, h12.symm, ite_false, ite_and, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ]

/-- The trace of a product of four matrices is invariant under rotating the factors. -/
theorem trace_rotate4 (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  rw [show A * B * C * D = A * (B * C * D) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]

section OneChord

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **(T₉′) for a contraction with one chord**, for any integrand `A` of the line momenta: from a
pointwise identity in a conserved routing with a shifted one-loop integrand `G` whose two stages
are integrable. -/
theorem jointEnergyFirstIntegrable_of_one_chord' {C : Contraction nf nA κ} {c : Line C}
    (hc : ∀ g, IsChord g ↔ g = c) {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (mom : (Fin 4 → ℝ) → Line C → Fin 4 → ℝ) (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ))
    (hchord : ∀ ℓ, mom ℓ c = ℓ) (A : (Line C → Fin 4 → ℝ) → ℂ) (G : (Fin 4 → ℝ) → ℂ)
    (s : Fin 4 → ℝ) (hpt : ∀ ℓ, (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * A (mom ℓ) = G (ℓ - s))
    (h₁ : ∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => G (Fin.cons t v))
    (h₂ : Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, G (Fin.cons t v)) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ * A (lineMomentum₂ C pOut pIn kIn ℓ) := by
  rw [loopCount_eq_one_of_unique hc]
  have hfun : (fun ℓ : Fin 1 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹ *
      A (lineMomentum₂ C pOut pIn kIn ℓ)) = fun ℓ => G (ℓ 0 - s) := by
    funext ℓ
    rw [QED.TwoLoop.IntegrableOrderFive.lineMomentum₂_eq_of_unique hc mom hcons hchord, mul_one,
      hpt]
  rw [hfun]
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_one_sub h₁ h₂ s

end OneChord

/-! ### `G0`: `δ₁` at the vertex of the second external photon -/

section G0

/-- The electron line with head `0`, tail `1`. -/
def g0l0 : FermionLine repG0 := ⟨fvK k_gC 0, by decide +kernel⟩
/-- The electron line with head `1`, tail `0`. -/
def g0l1 : FermionLine repG0 := ⟨fvK k_gC 1, by decide +kernel⟩

theorem g0_line_cases : ∀ f : Line repG0, f = .inl g0l0 ∨ f = .inl g0l1 := by decide +kernel

theorem g0_fermionLine_cases : ∀ f : FermionLine repG0, f = g0l0 ∨ f = g0l1 := by decide +kernel

theorem g0_photonLine_empty : ∀ _g : PhotonLine repG0, False := by decide +kernel

theorem g0_isChord_iff : ∀ g : Line repG0, IsChord g ↔ g = .inl g0l0 := by decide +kernel

theorem g0_ends : (Line.ends (.inl g0l0 : Line repG0)) = (1, 0) ∧
    (Line.ends (.inl g0l1 : Line repG0)) = (0, 1) := by
  decide +kernel

theorem g0_tails : g0l0.tail = fvK k_gC 1 ∧ g0l1.tail = fvK k_gC 0 := by decide +kernel

theorem g0_ext (v : Fin 2) :
    ((∃ a : Wick.PhotonSlot k_gC, a.1 = v ∧ repG0.1.2 (.inl 0) = .inr a) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_gC, a.1 = v ∧ repG0.1.2 (.inl 1) = .inr a) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repG0`: `ℓ` on the chord `l0`, `ℓ + k` on `l1`. -/
def g0Mom (k ℓ : Fin 4 → ℝ) (f : Line repG0) : Fin 4 → ℝ :=
  if f = .inl g0l0 then ℓ else ℓ + k

theorem g0Mom_apply (k ℓ : Fin 4 → ℝ) :
    g0Mom k ℓ (.inl g0l0) = ℓ ∧ g0Mom k ℓ (.inl g0l1) = ℓ + k :=
  ⟨ite_eq_left rfl, ite_eq_right (by decide)⟩

theorem g0_isConserved (k ℓ : Fin 4 → ℝ) :
    IsConserved repG0 ![] ![] ![k, -k] (g0Mom k ℓ) := by
  obtain ⟨e1, e2⟩ := g0_ends
  obtain ⟨m1, m2⟩ := g0Mom_apply k ℓ
  intro v
  rw [inflow, sum_eq_of_two (by decide) g0_line_cases, externalMomentum_zero_two]
  obtain ⟨x1, x2⟩ := g0_ext v
  simp only [e1, e2, x1, x2, m1, m2, Matrix.cons_val_zero, Matrix.cons_val_one]
  funext μ
  fin_cases v <;> simp

theorem g0_cond (α β : Wick.FermionVertex k_gC → Fin 4) (lor : Wick.PhotonSlot k_gC → Fin 4)
    (μ ν : Fin 4) :
    ((∀ (i : Fin 0) t, repG0.1.1 (.inl i) = .inr t → α t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ t (i : Fin 0), repG0.1.1 (.inr t) = .inl i → β t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ j a, repG0.1.2 (.inl j) = .inr a → lor a = ![μ, ν] j)) ↔
      (lor (psK k_gC 0 0) = μ ∧ lor (psK k_gC 1 0) = ν) := by
  have h0 : ∀ a, repG0.1.2 (.inl 0) = .inr a ↔ a = psK k_gC 0 0 := by decide +kernel
  have h1 : ∀ a, repG0.1.2 (.inl 1) = .inr a ↔ a = psK k_gC 1 0 := by decide +kernel
  simp only [Fin.forall_fin_two, h0, h1, forall_eq, IsEmpty.forall_iff, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, implies_true]

open scoped Classical in
/-- **The amplitude of `repG0`** at the constant flavouring `f`, grading `0`, arbitrary line
momenta. -/
theorem g0_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
    (kIn : Fin 2 → Fin 4 → ℝ) (kk : Line repG0 → Fin 4 → ℝ) (μ ν : Fin 4) :
    contractionAmplitude P Φ D repG0 (fun _ => f) 0 ![] kIn kk ![] ![] ![μ, ν] =
      (I * P.e) * (I * ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ)) * (1 / I) ^ 2 *
        Matrix.trace (Dirac.gamma μ *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl g0l0)) * Dirac.gamma ν *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl g0l1))) := by
  obtain ⟨t0, t1⟩ := g0_tails
  have : IsEmpty (PhotonLine repG0) := ⟨g0_photonLine_empty⟩
  unfold contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex k_gC → Fin 4, ∑ β : Wick.FermionVertex k_gC → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gC → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [g0_cond, Fin.prod_univ_two, prod_eq_of_two (by decide) g0_fermionLine_cases,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one, t0, t1,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show k_gC 0 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _
      (show k_gC 1 = .gaugeCt from rfl),
    show k_gC 0 = .gauge from rfl, show k_gC 1 = .gaugeCt from rfl, dite_true, dite_false,
    reduceCtorEq, Pi.zero_apply, zero_add, mul_one]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans
    (sum_lor_two (x₁ := psK k_gC 0 0) (x₂ := psK k_gC 1 0) (by decide) (by decide +kernel) μ ν
      (fun lor => (I * P.e) * (I * ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ)) * (1 / I) ^ 2 *
        Matrix.trace (Dirac.gamma (lor (psK k_gC 0 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl g0l0)) *
          Dirac.gamma (lor (psK k_gC 1 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl g0l1))))) |>.trans ?_
  · rw [← sum_spinor_loop2 (x₁ := fvK k_gC 0) (x₂ := fvK k_gC 1) (by decide)
      (by decide +kernel), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [show g0l0.1 = fvK k_gC 0 from rfl, show g0l1.1 = fvK k_gC 1 from rfl, psK, fvK]
    push_cast
    ring
  · have n : psK k_gC 1 0 ≠ psK k_gC 0 0 := by decide
    simp only [ite_true, n, ite_false]

theorem oneLoop_repG0 : OneLoop repG0 := by
  intro t s
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 2) (by norm_num) (by decide +kernel)]
  revert t s
  decide +kernel

/-- **The integrand of `repG0`** in its routing: the block-summed bubble at `ℓ`. -/
theorem g0_integrand (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D repG0 0 ![] ![k, -k] (g0Mom k ℓ) ![] ![] ![μ, ν] =
      ∑ f, (Φ.coeff f : ℂ) * ((fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)) (rep f) *
        bubbleW P.e (Φ.mass f) P.ε k ℓ μ ν) := by
  obtain ⟨m0, m1⟩ := g0Mom_apply k ℓ
  rw [regulatedAmplitude_of_oneLoop Φ P D oneLoop_repG0 (fvK k_gC 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [g0_amplitude, m0, m1, bubbleW, hD f,
    trace_rotate4 (QED.OneLoop.electronPropagator (Φ.mass f) P.ε (ℓ + k)) _ _ _]
  push_cast
  ring

/-- **The class obligation for `G0`.** -/
theorem classInt2_repG0 : ClassInt2 repG0 := by
  intro P F _ _ Φ D rep m₀ hH ε hε k μ ν
  obtain ⟨h1, h2⟩ := energyFirst_blockBubble { P with ε := ε } Φ rep m₀ hH.hm₀ hH.hmass hH.hrep
    hH.hPV₁ hH.hPV₂ (fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)) hε k μ ν
  exact jointEnergyFirstIntegrable_of_one_chord' g0_isChord_iff (g0Mom k) (g0_isConserved k)
    (fun ℓ => (g0Mom_apply k ℓ).1)
    (fun kk => regulatedAmplitude { P with ε := ε } Φ D repG0 0 ![] ![k, -k] kk ![] ![] ![μ, ν])
    (fun q => ∑ f, (Φ.coeff f : ℂ) * (((P.e ^ 2 * D.d₁ (rep f) 0 : ℝ) : ℂ) *
      bubbleW P.e (Φ.mass f) ε k q μ ν)) 0
    (fun ℓ => (g0_integrand { P with ε := ε } Φ D rep (fun f => (hH.hD f).1) k ℓ μ ν).trans
      (by rw [sub_zero])) h1 h2

end G0

/-! ### `G1`: `δ₁` at the vertex of the first external photon -/

section G1

/-- The electron line with head `0`, tail `1`. -/
def g1l0 : FermionLine repG1 := ⟨fvK k_gC 0, by decide +kernel⟩
/-- The electron line with head `1`, tail `0`. -/
def g1l1 : FermionLine repG1 := ⟨fvK k_gC 1, by decide +kernel⟩

theorem g1_line_cases : ∀ f : Line repG1, f = .inl g1l0 ∨ f = .inl g1l1 := by decide +kernel

theorem g1_fermionLine_cases : ∀ f : FermionLine repG1, f = g1l0 ∨ f = g1l1 := by decide +kernel

theorem g1_photonLine_empty : ∀ _g : PhotonLine repG1, False := by decide +kernel

theorem g1_isChord_iff : ∀ g : Line repG1, IsChord g ↔ g = .inl g1l0 := by decide +kernel

theorem g1_ends : (Line.ends (.inl g1l0 : Line repG1)) = (1, 0) ∧
    (Line.ends (.inl g1l1 : Line repG1)) = (0, 1) := by
  decide +kernel

theorem g1_tails : g1l0.tail = fvK k_gC 1 ∧ g1l1.tail = fvK k_gC 0 := by decide +kernel

theorem g1_ext (v : Fin 2) :
    ((∃ a : Wick.PhotonSlot k_gC, a.1 = v ∧ repG1.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ a : Wick.PhotonSlot k_gC, a.1 = v ∧ repG1.1.2 (.inl 1) = .inr a) ↔ v = 0) := by
  revert v
  decide +kernel

/-- The routing of `repG1`: `ℓ` on the chord `l0`, `ℓ - k` on `l1`. -/
def g1Mom (k ℓ : Fin 4 → ℝ) (f : Line repG1) : Fin 4 → ℝ :=
  if f = .inl g1l0 then ℓ else ℓ - k

theorem g1Mom_apply (k ℓ : Fin 4 → ℝ) :
    g1Mom k ℓ (.inl g1l0) = ℓ ∧ g1Mom k ℓ (.inl g1l1) = ℓ - k :=
  ⟨ite_eq_left rfl, ite_eq_right (by decide)⟩

theorem g1_isConserved (k ℓ : Fin 4 → ℝ) :
    IsConserved repG1 ![] ![] ![k, -k] (g1Mom k ℓ) := by
  obtain ⟨e1, e2⟩ := g1_ends
  obtain ⟨m1, m2⟩ := g1Mom_apply k ℓ
  intro v
  rw [inflow, sum_eq_of_two (by decide) g1_line_cases, externalMomentum_zero_two]
  obtain ⟨x1, x2⟩ := g1_ext v
  simp only [e1, e2, x1, x2, m1, m2, Matrix.cons_val_zero, Matrix.cons_val_one]
  funext μ
  fin_cases v <;> simp
  ring

theorem g1_cond (α β : Wick.FermionVertex k_gC → Fin 4) (lor : Wick.PhotonSlot k_gC → Fin 4)
    (μ ν : Fin 4) :
    ((∀ (i : Fin 0) t, repG1.1.1 (.inl i) = .inr t → α t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ t (i : Fin 0), repG1.1.1 (.inr t) = .inl i → β t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ j a, repG1.1.2 (.inl j) = .inr a → lor a = ![μ, ν] j)) ↔
      (lor (psK k_gC 1 0) = μ ∧ lor (psK k_gC 0 0) = ν) := by
  have h0 : ∀ a, repG1.1.2 (.inl 0) = .inr a ↔ a = psK k_gC 1 0 := by decide +kernel
  have h1 : ∀ a, repG1.1.2 (.inl 1) = .inr a ↔ a = psK k_gC 0 0 := by decide +kernel
  simp only [Fin.forall_fin_two, h0, h1, forall_eq, IsEmpty.forall_iff, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, implies_true]

open scoped Classical in
/-- **The amplitude of `repG1`** at the constant flavouring `f`, grading `0`, arbitrary line
momenta. -/
theorem g1_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
    (kIn : Fin 2 → Fin 4 → ℝ) (kk : Line repG1 → Fin 4 → ℝ) (μ ν : Fin 4) :
    contractionAmplitude P Φ D repG1 (fun _ => f) 0 ![] kIn kk ![] ![] ![μ, ν] =
      (I * P.e) * (I * ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ)) * (1 / I) ^ 2 *
        Matrix.trace (Dirac.gamma ν *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl g1l0)) * Dirac.gamma μ *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl g1l1))) := by
  obtain ⟨t0, t1⟩ := g1_tails
  have : IsEmpty (PhotonLine repG1) := ⟨g1_photonLine_empty⟩
  unfold contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex k_gC → Fin 4, ∑ β : Wick.FermionVertex k_gC → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gC → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [g1_cond, Fin.prod_univ_two, prod_eq_of_two (by decide) g1_fermionLine_cases,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one, t0, t1,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
      (show k_gC 0 = .gauge from rfl),
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _
      (show k_gC 1 = .gaugeCt from rfl),
    show k_gC 0 = .gauge from rfl, show k_gC 1 = .gaugeCt from rfl, dite_true, dite_false,
    reduceCtorEq, Pi.zero_apply, zero_add, mul_one]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans
    (sum_lor_two (x₁ := psK k_gC 1 0) (x₂ := psK k_gC 0 0) (by decide) (by decide +kernel) μ ν
      (fun lor => (I * P.e) * (I * ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ)) * (1 / I) ^ 2 *
        Matrix.trace (Dirac.gamma (lor (psK k_gC 0 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl g1l0)) *
          Dirac.gamma (lor (psK k_gC 1 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl g1l1))))) |>.trans ?_
  · rw [← sum_spinor_loop2 (x₁ := fvK k_gC 0) (x₂ := fvK k_gC 1) (by decide)
      (by decide +kernel), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [show g1l0.1 = fvK k_gC 0 from rfl, show g1l1.1 = fvK k_gC 1 from rfl, psK, fvK]
    push_cast
    ring
  · have n : psK k_gC 0 0 ≠ psK k_gC 1 0 := by decide
    simp only [ite_true, n, ite_false]

theorem oneLoop_repG1 : OneLoop repG1 := by
  intro t s
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 2) (by norm_num) (by decide +kernel)]
  revert t s
  decide +kernel

/-- **The integrand of `repG1`** in its routing: the block-summed bubble at `ℓ`. -/
theorem g1_integrand (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0) (k ℓ : Fin 4 → ℝ) (μ ν : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D repG1 0 ![] ![k, -k] (g1Mom k ℓ) ![] ![] ![μ, ν] =
      ∑ f, (Φ.coeff f : ℂ) * ((fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)) (rep f) *
        bubbleW P.e (Φ.mass f) P.ε k (ℓ - k) μ ν) := by
  obtain ⟨m0, m1⟩ := g1Mom_apply k ℓ
  rw [regulatedAmplitude_of_oneLoop Φ P D oneLoop_repG1 (fvK k_gC 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [g1_amplitude, m0, m1, bubbleW, hD f,
    trace_rotate4 (Dirac.gamma ν) _ _ _, sub_add_cancel]
  push_cast
  ring

/-- **The class obligation for `G1`.** -/
theorem classInt2_repG1 : ClassInt2 repG1 := by
  intro P F _ _ Φ D rep m₀ hH ε hε k μ ν
  obtain ⟨h1, h2⟩ := energyFirst_blockBubble { P with ε := ε } Φ rep m₀ hH.hm₀ hH.hmass hH.hrep
    hH.hPV₁ hH.hPV₂ (fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)) hε k μ ν
  exact jointEnergyFirstIntegrable_of_one_chord' g1_isChord_iff (g1Mom k) (g1_isConserved k)
    (fun ℓ => (g1Mom_apply k ℓ).1)
    (fun kk => regulatedAmplitude { P with ε := ε } Φ D repG1 0 ![] ![k, -k] kk ![] ![] ![μ, ν])
    (fun q => ∑ f, (Φ.coeff f : ℂ) * (((P.e ^ 2 * D.d₁ (rep f) 0 : ℝ) : ℂ) *
      bubbleW P.e (Φ.mass f) ε k q μ ν)) k
    (fun ℓ => (g1_integrand { P with ε := ε } Φ D rep (fun f => (hH.hD f).1) k ℓ μ ν).trans
      rfl) h1 h2

end G1

end QED.GradedProof.VP2

end
