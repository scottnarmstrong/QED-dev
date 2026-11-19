/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FAlg

/-!
# The classes `F0`, `F1`: the one-loop bubble with a `δ₂, δ_m` insertion

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2:
`classInt2_repF0`, `classInt2_repF1`. The representatives have `gauge` vertices `0`, `1` (the
external photons) and the `fermionCt` vertex `2` on one closed loop of three electron lines, one
of them carrying `x` and the two through vertex `2` carrying `y`, with `x - y = ±k`.

* the lines, their ends, the unique chord and an explicit conserved routing (`decide +kernel`);
* the amplitude (G₃) at the constant flavouring `f` is `(ie)²(-i)(1/i)³` times the trace of the
  loop with the counterterm matrix (`f0_amplitude`, `f1_amplitude`), through
  `sum_spinor_loop3`;
* with the block hypotheses the integrand is the block-summed inserted bubble of
  `QED/GradedProof/VP2FAlg.lean` (`f0_integrand`, `f1_integrand`), whose two stages are
  integrable (`ef_insBubble`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Insertion
open QED.TwoLoop.Bridge
open QED.GradedProof.SE2 (k_ggf)
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂ Line FermionLine
  PhotonLine IsChord externalMomentum)

/-- **The spinor sum around a closed loop through three vertices** is a trace. -/
theorem sum_spinor_loop3 {X : Type*} [Fintype X] [DecidableEq X] {x₁ x₂ x₃ : X} (h12 : x₁ ≠ x₂)
    (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃)
    (A₁ A₂ A₃ S₁ S₂ S₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ α : X → Fin 4, ∑ β : X → Fin 4,
      A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃) * S₃ (β x₃) (α x₁) =
      Matrix.trace (A₁ * S₁ * A₂ * S₂ * A₃ * S₃) := by
  have key : ∀ α β : X → Fin 4,
      A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
          A₃ (α x₃) (β x₃) * S₃ (β x₃) (α x₁) =
        ∑ a : Fin 4, ∑ b : Fin 4, (if α x₁ = a ∧ β x₃ = b then (1 : ℂ) else 0) *
          (1 * (A₁ (α x₁) (β x₁) * S₁ (β x₁) (α x₂) * A₂ (α x₂) (β x₂) * S₂ (β x₂) (α x₃) *
            A₃ (α x₃) (β x₃))) * S₃ b a := by
    intro α β
    simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [key]
  have e : ∀ (g : (X → Fin 4) → (X → Fin 4) → Fin 4 → Fin 4 → ℂ),
      ∑ α : X → Fin 4, ∑ β : X → Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, g α β a b =
        ∑ a, ∑ b, ∑ α, ∑ β, g α β a b := fun g => by
    have h1 : ∀ α, ∑ β : X → Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, g α β a b =
        ∑ a, ∑ b, ∑ β, g α β a b := fun α => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [e]
  simp only [← Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := A₁ * S₁ * A₂ * S₂ * A₃)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simpa using sum_spinor_chain3 h12 h13 h23 hX 1 A₁ A₂ A₃ S₁ S₂ a b

theorem k_ggf_kinds : k_ggf 0 = .gauge ∧ k_ggf 1 = .gauge ∧ k_ggf 2 = .fermionCt :=
  ⟨rfl, rfl, rfl⟩

/-- The electron propagator times the counterterm matrix, in numerator form. -/
theorem trace_ins_smul (A B : Matrix (Fin 4) (Fin 4) ℂ) (d₂ dm M ε : ℝ) (x y : Fin 4 → ℝ) :
    Matrix.trace (A * QED.OneLoop.electronPropagator M ε x * B *
        QED.OneLoop.electronPropagator M ε y * fermionCtMatrix d₂ dm M y *
        QED.OneLoop.electronPropagator M ε y) =
      insG A B d₂ dm M ε x y := by
  simp only [QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, insG, insTr]
  ring

/-- The constant of the inserted bubble: `(2π)⁻⁴ (ie)² (-i) (1/i)³`. -/
noncomputable def kF (e : ℝ) : ℂ :=
  (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * ((I * e) * (I * e) * (-I) * (1 / I) ^ 3)

theorem zk_true (k q : Fin 4 → ℝ) : zk k true q = k + q := rfl

theorem zk_false (k q : Fin 4 → ℝ) : zk k false q = q := rfl

/-- The trace of a product of six matrices is invariant under rotating the factors. -/
theorem trace_rotate6 (A B C D E G : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (A * B * C * D * E * G) = Matrix.trace (E * G * A * B * C * D) := by
  rw [show A * B * C * D * E * G = (A * B * C * D) * (E * G) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-! ### `F0`: loop `0 → 1 → 2 → 0` -/

section F0

/-- The electron line `2 → 0`. -/
def f0l0 : FermionLine repF0 := ⟨fvK k_ggf 0, by decide +kernel⟩
/-- The electron line `0 → 1`. -/
def f0l1 : FermionLine repF0 := ⟨fvK k_ggf 1, by decide +kernel⟩
/-- The electron line `1 → 2`. -/
def f0l2 : FermionLine repF0 := ⟨fvK k_ggf 2, by decide +kernel⟩

theorem f0_line_cases : ∀ f : Line repF0, f = .inl f0l0 ∨ f = .inl f0l1 ∨ f = .inl f0l2 := by
  decide +kernel

theorem f0_fermionLine_cases : ∀ f : FermionLine repF0, f = f0l0 ∨ f = f0l1 ∨ f = f0l2 := by
  decide +kernel

theorem f0_photonLine_empty : ∀ _g : PhotonLine repF0, False := by decide +kernel

theorem f0_isChord_iff : ∀ g : Line repF0, IsChord g ↔ g = .inl f0l0 := by decide +kernel

theorem f0_ends : (Line.ends (.inl f0l0 : Line repF0)) = (2, 0) ∧
    (Line.ends (.inl f0l1 : Line repF0)) = (0, 1) ∧
    (Line.ends (.inl f0l2 : Line repF0)) = (1, 2) := by
  decide +kernel

theorem f0_tails : f0l0.tail = fvK k_ggf 2 ∧ f0l1.tail = fvK k_ggf 0 ∧
    f0l2.tail = fvK k_ggf 1 := by
  decide +kernel

theorem f0_ext (v : Fin 3) :
    ((∃ a : Wick.PhotonSlot k_ggf, a.1 = v ∧ repF0.1.2 (.inl 0) = .inr a) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_ggf, a.1 = v ∧ repF0.1.2 (.inl 1) = .inr a) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repF0`: `ℓ` on `l0`, `l2`, `k + ℓ` on `l1`. -/
def f0Mom (k ℓ : Fin 4 → ℝ) (f : Line repF0) : Fin 4 → ℝ :=
  if f = .inl f0l1 then k + ℓ else ℓ

theorem f0Mom_apply (k ℓ : Fin 4 → ℝ) : f0Mom k ℓ (.inl f0l0) = ℓ ∧
    f0Mom k ℓ (.inl f0l1) = k + ℓ ∧ f0Mom k ℓ (.inl f0l2) = ℓ :=
  ⟨ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide)⟩

theorem f0_isConserved (k ℓ : Fin 4 → ℝ) :
    IsConserved repF0 ![] ![] ![k, -k] (f0Mom k ℓ) := by
  obtain ⟨e1, e2, e3⟩ := f0_ends
  obtain ⟨m1, m2, m3⟩ := f0Mom_apply k ℓ
  intro v
  rw [inflow, sum_eq_of_three (by decide) (by decide) (by decide) f0_line_cases,
    externalMomentum_zero_two]
  obtain ⟨x1, x2⟩ := f0_ext v
  simp only [e1, e2, e3, x1, x2, m1, m2, m3, Matrix.cons_val_zero, Matrix.cons_val_one]
  funext μ
  fin_cases v <;> simp

theorem f0_cond (α β : Wick.FermionVertex k_ggf → Fin 4) (lor : Wick.PhotonSlot k_ggf → Fin 4)
    (μ ν : Fin 4) :
    ((∀ (i : Fin 0) t, repF0.1.1 (.inl i) = .inr t → α t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ t (i : Fin 0), repF0.1.1 (.inr t) = .inl i → β t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ j a, repF0.1.2 (.inl j) = .inr a → lor a = ![μ, ν] j)) ↔
      (lor (psK k_ggf 0 0) = μ ∧ lor (psK k_ggf 1 0) = ν) := by
  have h0 : ∀ a, repF0.1.2 (.inl 0) = .inr a ↔ a = psK k_ggf 0 0 := by decide +kernel
  have h1 : ∀ a, repF0.1.2 (.inl 1) = .inr a ↔ a = psK k_ggf 1 0 := by decide +kernel
  simp only [Fin.forall_fin_two, h0, h1, forall_eq, IsEmpty.forall_iff, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, implies_true]

open scoped Classical in
/-- **The amplitude of `repF0`** at the constant flavouring `f`, grading `0`. -/
theorem f0_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
    (kIn : Fin 2 → Fin 4 → ℝ) (kk : Line repF0 → Fin 4 → ℝ) (μ ν : Fin 4) :
    contractionAmplitude P Φ D repF0 (fun _ => f) 0 ![] kIn kk ![] ![] ![μ, ν] =
      (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 3 *
        Matrix.trace (Dirac.gamma μ *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f0l0)) *
          fermionCtMatrix (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) (Φ.mass f)
            (kk (.inl f0l2)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f0l2)) * Dirac.gamma ν *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f0l1))) := by
  obtain ⟨t0, t1, t2⟩ := f0_tails
  have : IsEmpty (PhotonLine repF0) := ⟨f0_photonLine_empty⟩
  have hpsi : QED.WickModel.psiMomentum₂ repF0 ![] kk ⟨2, by decide⟩ = kk (.inl f0l2) :=
    QED.TwoLoop.Relabel.psiMomentum₂_of_isRight (by decide +kernel)
  unfold contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex k_ggf → Fin 4, ∑ β : Wick.FermionVertex k_ggf → Fin 4,
      ∑ lor : Wick.PhotonSlot k_ggf → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [f0_cond, Fin.prod_univ_three,
    prod_eq_of_three (by decide) (by decide) (by decide) f0_fermionLine_cases,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one, t0, t1, t2,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ k_ggf_kinds.1,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ k_ggf_kinds.2.1,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ k_ggf_kinds.2.2,
    hpsi, k_ggf_kinds, dite_true, dite_false, reduceCtorEq, Pi.zero_apply, zero_add, mul_one]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans
    (sum_lor_two (x₁ := psK k_ggf 0 0) (x₂ := psK k_ggf 1 0) (by decide) (by decide +kernel) μ ν
      (fun lor => (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 3 *
        Matrix.trace (Dirac.gamma (lor (psK k_ggf 0 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f0l0)) *
          fermionCtMatrix (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) (Φ.mass f)
            (kk (.inl f0l2)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f0l2)) *
          Dirac.gamma (lor (psK k_ggf 1 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f0l1))))) |>.trans ?_
  · rw [← sum_spinor_loop3 (x₁ := fvK k_ggf 0) (x₂ := fvK k_ggf 2) (x₃ := fvK k_ggf 1)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [show f0l0.1 = fvK k_ggf 0 from rfl, show f0l1.1 = fvK k_ggf 1 from rfl,
      show f0l2.1 = fvK k_ggf 2 from rfl, psK, fvK, fermionCtMatrix]
    push_cast
    ring
  · have n : psK k_ggf 1 0 ≠ psK k_ggf 0 0 := by decide
    simp only [ite_true, n, ite_false]

theorem oneLoop_repF0 : OneLoop repF0 := by
  intro t s
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 3) (by norm_num) (by decide +kernel)]
  revert t s
  decide +kernel

/-- **The integrand of `repF0`** in its routing: the block-summed inserted bubble. -/
theorem f0_integrand (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) (k ℓ : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D repF0 0 ![] ![k, -k] (f0Mom k ℓ) ![] ![] ![μ, ν] =
      ∑ f, (Φ.coeff f : ℂ) * (kF P.e * insG (Dirac.gamma ν) (Dirac.gamma μ)
        ((fun r => P.e ^ 2 * D.d₂ r 0) (rep f)) ((fun r => P.e ^ 2 * D.dm r 0) (rep f))
        (Φ.mass f) P.ε (zk k true ℓ) (zk k false ℓ)) := by
  obtain ⟨m0, m1, m2⟩ := f0Mom_apply k ℓ
  rw [regulatedAmplitude_of_oneLoop Φ P D oneLoop_repF0 (fvK k_ggf 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [f0_amplitude, m0, m1, m2, (hD f).1, (hD f).2, trace_rotate6, zk_true, zk_false,
    trace_ins_smul, kF]
  ring

/-- **The class obligation for `F0`.** -/
theorem classInt2_repF0 : ClassInt2 repF0 := by
  intro P F _ _ Φ D rep m₀ hH ε hε k μ ν
  have hEF := ef_insBubble (isOddG_gamma ν) (isOddG_gamma μ) Φ rep m₀ hH.hm₀ hH.hmass hH.hrep
    hH.hPV₁ hH.hPV₂ (fun r => P.e ^ 2 * D.d₂ r 0) (fun r => P.e ^ 2 * D.dm r 0) hε k true false
    (kF P.e)
  exact jointEnergyFirstIntegrable_of_one_chord' f0_isChord_iff (f0Mom k) (f0_isConserved k)
    (fun ℓ => (f0Mom_apply k ℓ).1)
    (fun kk => regulatedAmplitude { P with ε := ε } Φ D repF0 0 ![] ![k, -k] kk ![] ![] ![μ, ν])
    _ 0 (fun ℓ => (f0_integrand { P with ε := ε } Φ D rep (fun f => (hH.hD f).2) k ℓ μ ν).trans
      (by rw [sub_zero])) hEF.1 hEF.2

end F0

/-! ### `F1`: loop `0 → 2 → 1 → 0` -/

section F1

/-- The electron line `1 → 0`. -/
def f1l0 : FermionLine repF1 := ⟨fvK k_ggf 0, by decide +kernel⟩
/-- The electron line `2 → 1`. -/
def f1l1 : FermionLine repF1 := ⟨fvK k_ggf 1, by decide +kernel⟩
/-- The electron line `0 → 2`. -/
def f1l2 : FermionLine repF1 := ⟨fvK k_ggf 2, by decide +kernel⟩

theorem f1_line_cases : ∀ f : Line repF1, f = .inl f1l0 ∨ f = .inl f1l1 ∨ f = .inl f1l2 := by
  decide +kernel

theorem f1_fermionLine_cases : ∀ f : FermionLine repF1, f = f1l0 ∨ f = f1l1 ∨ f = f1l2 := by
  decide +kernel

theorem f1_photonLine_empty : ∀ _g : PhotonLine repF1, False := by decide +kernel

theorem f1_isChord_iff : ∀ g : Line repF1, IsChord g ↔ g = .inl f1l0 := by decide +kernel

theorem f1_ends : (Line.ends (.inl f1l0 : Line repF1)) = (1, 0) ∧
    (Line.ends (.inl f1l1 : Line repF1)) = (2, 1) ∧
    (Line.ends (.inl f1l2 : Line repF1)) = (0, 2) := by
  decide +kernel

theorem f1_tails : f1l0.tail = fvK k_ggf 1 ∧ f1l1.tail = fvK k_ggf 2 ∧
    f1l2.tail = fvK k_ggf 0 := by
  decide +kernel

theorem f1_ext (v : Fin 3) :
    ((∃ a : Wick.PhotonSlot k_ggf, a.1 = v ∧ repF1.1.2 (.inl 0) = .inr a) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_ggf, a.1 = v ∧ repF1.1.2 (.inl 1) = .inr a) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The routing of `repF1`: `ℓ` on `l0`, `k + ℓ` on `l1`, `l2`. -/
def f1Mom (k ℓ : Fin 4 → ℝ) (f : Line repF1) : Fin 4 → ℝ :=
  if f = .inl f1l0 then ℓ else k + ℓ

theorem f1Mom_apply (k ℓ : Fin 4 → ℝ) : f1Mom k ℓ (.inl f1l0) = ℓ ∧
    f1Mom k ℓ (.inl f1l1) = k + ℓ ∧ f1Mom k ℓ (.inl f1l2) = k + ℓ :=
  ⟨ite_eq_left rfl, ite_eq_right (by decide), ite_eq_right (by decide)⟩

theorem f1_isConserved (k ℓ : Fin 4 → ℝ) :
    IsConserved repF1 ![] ![] ![k, -k] (f1Mom k ℓ) := by
  obtain ⟨e1, e2, e3⟩ := f1_ends
  obtain ⟨m1, m2, m3⟩ := f1Mom_apply k ℓ
  intro v
  rw [inflow, sum_eq_of_three (by decide) (by decide) (by decide) f1_line_cases,
    externalMomentum_zero_two]
  obtain ⟨x1, x2⟩ := f1_ext v
  simp only [e1, e2, e3, x1, x2, m1, m2, m3, Matrix.cons_val_zero, Matrix.cons_val_one]
  funext μ
  fin_cases v <;> simp

theorem f1_cond (α β : Wick.FermionVertex k_ggf → Fin 4) (lor : Wick.PhotonSlot k_ggf → Fin 4)
    (μ ν : Fin 4) :
    ((∀ (i : Fin 0) t, repF1.1.1 (.inl i) = .inr t → α t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ t (i : Fin 0), repF1.1.1 (.inr t) = .inl i → β t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ j a, repF1.1.2 (.inl j) = .inr a → lor a = ![μ, ν] j)) ↔
      (lor (psK k_ggf 0 0) = μ ∧ lor (psK k_ggf 1 0) = ν) := by
  have h0 : ∀ a, repF1.1.2 (.inl 0) = .inr a ↔ a = psK k_ggf 0 0 := by decide +kernel
  have h1 : ∀ a, repF1.1.2 (.inl 1) = .inr a ↔ a = psK k_ggf 1 0 := by decide +kernel
  simp only [Fin.forall_fin_two, h0, h1, forall_eq, IsEmpty.forall_iff, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, implies_true]

open scoped Classical in
/-- **The amplitude of `repF1`** at the constant flavouring `f`, grading `0`. -/
theorem f1_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
    (kIn : Fin 2 → Fin 4 → ℝ) (kk : Line repF1 → Fin 4 → ℝ) (μ ν : Fin 4) :
    contractionAmplitude P Φ D repF1 (fun _ => f) 0 ![] kIn kk ![] ![] ![μ, ν] =
      (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 3 *
        Matrix.trace (Dirac.gamma μ *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f1l0)) * Dirac.gamma ν *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f1l1)) *
          fermionCtMatrix (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) (Φ.mass f)
            (kk (.inl f1l2)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f1l2))) := by
  obtain ⟨t0, t1, t2⟩ := f1_tails
  have : IsEmpty (PhotonLine repF1) := ⟨f1_photonLine_empty⟩
  have hpsi : QED.WickModel.psiMomentum₂ repF1 ![] kk ⟨2, by decide⟩ = kk (.inl f1l2) :=
    QED.TwoLoop.Relabel.psiMomentum₂_of_isRight (by decide +kernel)
  unfold contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex k_ggf → Fin 4, ∑ β : Wick.FermionVertex k_ggf → Fin 4,
      ∑ lor : Wick.PhotonSlot k_ggf → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [f1_cond, Fin.prod_univ_three,
    prod_eq_of_three (by decide) (by decide) (by decide) f1_fermionLine_cases,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one, t0, t1, t2,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ k_ggf_kinds.1,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ k_ggf_kinds.2.1,
    QED.TwoLoop.Relabel.vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ k_ggf_kinds.2.2,
    hpsi, k_ggf_kinds, dite_true, dite_false, reduceCtorEq, Pi.zero_apply, zero_add, mul_one]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans
    (sum_lor_two (x₁ := psK k_ggf 0 0) (x₂ := psK k_ggf 1 0) (by decide) (by decide +kernel) μ ν
      (fun lor => (I * P.e) * (I * P.e) * (-I) * (1 / I) ^ 3 *
        Matrix.trace (Dirac.gamma (lor (psK k_ggf 0 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f1l0)) *
          Dirac.gamma (lor (psK k_ggf 1 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f1l1)) *
          fermionCtMatrix (P.e ^ 2 * D.d₂ f 0) (P.e ^ 2 * D.dm f 0) (Φ.mass f)
            (kk (.inl f1l2)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl f1l2))))) |>.trans ?_
  · rw [← sum_spinor_loop3 (x₁ := fvK k_ggf 0) (x₂ := fvK k_ggf 1) (x₃ := fvK k_ggf 2)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [show f1l0.1 = fvK k_ggf 0 from rfl, show f1l1.1 = fvK k_ggf 1 from rfl,
      show f1l2.1 = fvK k_ggf 2 from rfl, psK, fvK, fermionCtMatrix]
    push_cast
    ring
  · have n : psK k_ggf 1 0 ≠ psK k_ggf 0 0 := by decide
    simp only [ite_true, n, ite_false]

theorem oneLoop_repF1 : OneLoop repF1 := by
  intro t s
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 3) (by norm_num) (by decide +kernel)]
  revert t s
  decide +kernel

/-- **The integrand of `repF1`** in its routing: the block-summed inserted bubble. -/
theorem f1_integrand (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) (k ℓ : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D repF1 0 ![] ![k, -k] (f1Mom k ℓ) ![] ![] ![μ, ν] =
      ∑ f, (Φ.coeff f : ℂ) * (kF P.e * insG (Dirac.gamma μ) (Dirac.gamma ν)
        ((fun r => P.e ^ 2 * D.d₂ r 0) (rep f)) ((fun r => P.e ^ 2 * D.dm r 0) (rep f))
        (Φ.mass f) P.ε (zk k false ℓ) (zk k true ℓ)) := by
  obtain ⟨m0, m1, m2⟩ := f1Mom_apply k ℓ
  rw [regulatedAmplitude_of_oneLoop Φ P D oneLoop_repF1 (fvK k_ggf 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [f1_amplitude, m0, m1, m2, (hD f).1, (hD f).2, zk_true, zk_false, trace_ins_smul, kF]
  ring

/-- **The class obligation for `F1`.** -/
theorem classInt2_repF1 : ClassInt2 repF1 := by
  intro P F _ _ Φ D rep m₀ hH ε hε k μ ν
  have hEF := ef_insBubble (isOddG_gamma μ) (isOddG_gamma ν) Φ rep m₀ hH.hm₀ hH.hmass hH.hrep
    hH.hPV₁ hH.hPV₂ (fun r => P.e ^ 2 * D.d₂ r 0) (fun r => P.e ^ 2 * D.dm r 0) hε k false true
    (kF P.e)
  exact jointEnergyFirstIntegrable_of_one_chord' f1_isChord_iff (f1Mom k) (f1_isConserved k)
    (fun ℓ => (f1Mom_apply k ℓ).1)
    (fun kk => regulatedAmplitude { P with ε := ε } Φ D repF1 0 ![] ![k, -k] kk ![] ![] ![μ, ν])
    _ 0 (fun ℓ => (f1_integrand { P with ε := ε } Φ D rep (fun f => (hH.hD f).2) k ℓ μ ν).trans
      (by rw [sub_zero])) hEF.1 hEF.2

end F1

end QED.GradedProof.VP2

end
