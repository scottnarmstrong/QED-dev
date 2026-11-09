/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPointClassificationGauge2
import QED.Integration.EnergyFirstShift

/-!
# The vacuum polarization loop

The one-loop part of the vacuum polarization `onePIFunction P 0 2 2` of the general Wick model
(decisions D-22, D-23, D-24, D-25): the contractions of two gauge vertices `gauge2` with two
external photons and no external fermion.

* `isOnePI_iff_exists_isPolarizationLoop`: a contraction is 1PI exactly when it is a vacuum
  polarization loop `IsPolarizationLoop C a b`: the external photon `A(z₁)` is contracted with the
  photon field of `a`, `A(z₂)` with that of `b`, and the fermion fields of the two vertices form
  one closed loop. The other contractions with attached externals have two fermion self-loops
  and disconnected vertices.
* `IsPolarizationLoop.sum_preserves`: the flavorings preserved by the closed loop are the
  constant ones, one for each flavor `f`, of weight `c_f`; the regulated amplitude is the sum
  over the Pauli–Villars flavors inside one integrand.
* `IsPolarizationLoop.neg_contractionValue_eq`: minus the value of a loop (its fermionic sign is
  `-1`) is the energy-first integral of `vacuumPolarizationIntegrand` (62.12). For `a = 0` the
  routed integrand is the source's, by cyclicity of the trace; for `a = 1` it is the source's at
  the shifted loop momentum `ℓ - k`.
* `sum_isOnePI_polarizationLoop`: the two loops (`a = 0` and `a = 1`) have the same signed
  value, so the `1/2!` of the Wick expansion leaves one copy.
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-! ### Constant flavorings -/

/-- The flavoring in which both fermion vertices of `gauge2` have flavor `f`. -/
def constFlavoring (f : Fin 3) : Flavoring gauge2 := ⟨fun _ => f, fun _ h => absurd rfl h⟩

/-- The constant flavoring gives every vertex fermion field the flavor `f`. -/
@[simp]
theorem constFlavoring_apply (f : Fin 3) (t : Wick.FermionVertex gauge2) :
    (constFlavoring f).1 t = f := rfl

/-- The constant flavorings are distinct. -/
theorem constFlavoring_injective : Function.Injective constFlavoring := fun _ _ h =>
  congrFun (congrArg Subtype.val h) (fv2 0)

/-- The trace of a product of four matrices is invariant under rotating the factors. -/
theorem trace_mul_mul_mul_rotate (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  rw [show A * B * C * D = A * (B * C * D) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]

/-! ### Vacuum polarization loops -/

/-- If the external photons are contracted with the photon fields of `a` and `b`, there is no
internal photon line. -/
theorem isEmpty_photonLine_of_two {nf : ℕ} {C : Contraction nf 2 gauge2} {a b : Fin 2}
    (hab : a ≠ b) (h0 : C.1.2 (.inl 0) = .inr (ps2 a)) (h1 : C.1.2 (.inl 1) = .inr (ps2 b)) :
    IsEmpty (PhotonLine C) :=
  ⟨fun g => by
    obtain ⟨s, s', hs, -⟩ := g
    rcases ps2_eq_or a b hab s with rfl | rfl
    · rw [← h0, (C.2 _).1] at hs
      exact Sum.inl_ne_inr hs
    · rw [← h1, (C.2 _).1] at hs
      exact Sum.inl_ne_inr hs⟩

/-- The contraction `C` of two gauge vertices is the vacuum polarization loop in which the
external photon `A(z₁)` is contracted with the photon field of `a`, `A(z₂)` with that of `b`, and
the `Ψ` of vertex `0` with the `Ψ̄` of vertex `1` (and then the `Ψ` of `1` with the `Ψ̄` of `0`):
one closed fermion loop through both vertices. -/
def IsPolarizationLoop (C : Contraction 0 2 gauge2) (a b : Fin 2) : Prop :=
  a ≠ b ∧ C.1.2 (.inl 0) = .inr (ps2 a) ∧ C.1.2 (.inl 1) = .inr (ps2 b) ∧
    C.1.1 (.inr (fv2 0)) = .inr (fv2 1)

namespace IsPolarizationLoop

variable {C : Contraction 0 2 gauge2} {a b : Fin 2}

/-- The two external photons attach at different vertices. -/
theorem ne (hC : IsPolarizationLoop C a b) : a ≠ b := hC.1
/-- `A(z₁)` is contracted with the photon field of `a`. -/
theorem photon_zero (hC : IsPolarizationLoop C a b) : C.1.2 (.inl 0) = .inr (ps2 a) := hC.2.1
/-- `A(z₂)` is contracted with the photon field of `b`. -/
theorem photon_one (hC : IsPolarizationLoop C a b) : C.1.2 (.inl 1) = .inr (ps2 b) := hC.2.2.1
/-- The `Ψ` of vertex `0` is contracted with the `Ψ̄` of vertex `1`. -/
theorem psi_zero (hC : IsPolarizationLoop C a b) : C.1.1 (.inr (fv2 0)) = .inr (fv2 1) :=
  hC.2.2.2

/-- The `Ψ` of vertex `1` is contracted with the `Ψ̄` of vertex `0`. -/
theorem psi_one (hC : IsPolarizationLoop C a b) : C.1.1 (.inr (fv2 1)) = .inr (fv2 0) := by
  rcases h : C.1.1 (.inr (fv2 1)) with i | t
  · exact i.elim0
  · rcases fv2_eq_or 0 1 (by decide) t with rfl | rfl
    · rfl
    · have := Sum.inr_injective (C.1.1.injective (h.trans hC.psi_zero.symm))
      exact absurd (fv2_injective this) (by decide)

/-- The photon field of `a` is contracted with `A(z₁)`. -/
theorem photon_a (hC : IsPolarizationLoop C a b) : C.1.2 (.inr (ps2 a)) = .inl 0 := by
  rw [← hC.photon_zero, (C.2 _).1]

/-- The photon field of `b` is contracted with `A(z₂)`. -/
theorem photon_b (hC : IsPolarizationLoop C a b) : C.1.2 (.inr (ps2 b)) = .inl 1 := by
  rw [← hC.photon_one, (C.2 _).1]

/-- There is no internal photon line. -/
theorem isEmpty_photonLine (hC : IsPolarizationLoop C a b) : IsEmpty (PhotonLine C) :=
  isEmpty_photonLine_of_two hC.ne hC.photon_zero hC.photon_one

/-- The internal fermion line from `1` to `0`. -/
def line0 (hC : IsPolarizationLoop C a b) : FermionLine C := ⟨fv2 0, by simp [hC.psi_zero]⟩

/-- The internal fermion line from `0` to `1`. -/
def line1 (hC : IsPolarizationLoop C a b) : FermionLine C := ⟨fv2 1, by simp [hC.psi_one]⟩

/-- The line `line0` is indexed by the `Ψ` of vertex `0`. -/
@[simp]
theorem line0_val (hC : IsPolarizationLoop C a b) : hC.line0.1 = fv2 0 := rfl

/-- The line `line1` is indexed by the `Ψ` of vertex `1`. -/
@[simp]
theorem line1_val (hC : IsPolarizationLoop C a b) : hC.line1.1 = fv2 1 := rfl

/-- The line `line0` starts at vertex `1`. -/
@[simp]
theorem tail_line0 (hC : IsPolarizationLoop C a b) : hC.line0.tail = fv2 1 :=
  FermionLine.tail_eq hC.psi_zero

/-- The line `line1` starts at vertex `0`. -/
@[simp]
theorem tail_line1 (hC : IsPolarizationLoop C a b) : hC.line1.tail = fv2 0 :=
  FermionLine.tail_eq hC.psi_one

/-- The line `line0` runs from vertex `1` to vertex `0`. -/
theorem ends_line0 (hC : IsPolarizationLoop C a b) :
    Line.ends (.inl hC.line0 : Line C) = (1, 0) := by
  change (hC.line0.tail.1, hC.line0.1.1) = (1, 0)
  rw [tail_line0]
  rfl

/-- The line `line1` runs from vertex `0` to vertex `1`. -/
theorem ends_line1 (hC : IsPolarizationLoop C a b) :
    Line.ends (.inl hC.line1 : Line C) = (0, 1) := by
  change (hC.line1.tail.1, hC.line1.1.1) = (0, 1)
  rw [tail_line1]
  rfl

/-- The two fermion lines are distinct. -/
theorem line0_ne_line1 (hC : IsPolarizationLoop C a b) : hC.line0 ≠ hC.line1 := fun h =>
  (by decide : (0 : Fin 2) ≠ 1) (congrArg (fun f : FermionLine C => f.1.1) h)

/-- The internal fermion lines are the two lines of the loop. -/
theorem fermionLine_cases (hC : IsPolarizationLoop C a b) (f : FermionLine C) :
    f = hC.line0 ∨ f = hC.line1 := by
  obtain ⟨t, ht⟩ := f
  rcases fv2_eq_or 0 1 (by decide) t with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The internal lines are the two fermion lines of the loop. -/
theorem line_cases (hC : IsPolarizationLoop C a b) (g : Line C) :
    g = .inl hC.line0 ∨ g = .inl hC.line1 := by
  rcases g with f | g
  · rcases hC.fermionLine_cases f with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact (hC.isEmpty_photonLine.false g).elim

/-- A product over the internal fermion lines. -/
theorem prod_fermionLine (hC : IsPolarizationLoop C a b) {M : Type*} [CommMonoid M]
    (F : FermionLine C → M) : ∏ f, F f = F hC.line0 * F hC.line1 :=
  Fintype.prod_eq_mul _ _ hC.line0_ne_line1 fun f hf =>
    absurd (hC.fermionLine_cases f) (not_or.mpr hf)

/-- A product over the internal photon lines is empty. -/
theorem prod_photonLine (hC : IsPolarizationLoop C a b) {M : Type*} [CommMonoid M]
    (F : PhotonLine C → M) : ∏ g, F g = 1 :=
  haveI := hC.isEmpty_photonLine
  Finset.prod_of_isEmpty _

/-- A vacuum polarization loop is 1PI: its two fermion lines join the two vertices. -/
theorem isOnePI (hC : IsPolarizationLoop C a b) : IsOnePI C := by
  refine isOnePI_of_fin_two ⟨fun i => i.elim0, fun i j => ?_⟩ (f₁ := .inl hC.line0)
    (f₂ := .inl hC.line1) (fun h => hC.line0_ne_line1 (Sum.inl_injective h)) ?_ ?_
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [hC.photon_zero]
      exact Sum.inr_ne_inl
    · rw [hC.photon_one]
      exact Sum.inr_ne_inl
  · rw [hC.ends_line0]
    decide
  · rw [hC.ends_line1]
    decide

/-- The loop line is the line indexed by vertex `0`. -/
theorem isLoopLine_iff (hC : IsPolarizationLoop C a b) (g : Line C) :
    IsLoopLine g ↔ g = .inl hC.line0 := by
  rw [hC.isOnePI.isLoopLine_iff]
  constructor
  · intro h
    rcases hC.line_cases g with rfl | rfl
    · rfl
    · have := h (.inl hC.line0)
      change 1 ≤ 0 at this
      omega
  · rintro rfl g
    rcases hC.line_cases g with rfl | rfl
    · exact le_rfl
    · exact Nat.zero_le 1

/-- The external momentum at vertex `0`: the momentum of the external photon contracted with its
photon field. -/
theorem externalMomentum_zero (hC : IsPolarizationLoop C a b) (pOut pIn : Fin 0 → Fin 4 → ℝ)
    (kIn : Fin 2 → Fin 4 → ℝ) :
    externalMomentum C pOut pIn kIn 0 =
      (if a = 0 then kIn 0 else 0) + (if b = 0 then kIn 1 else 0) := by
  have h : ∀ (j : Fin 2) (c : Fin 2), C.1.2 (.inl j) = .inr (ps2 c) →
      ((∃ s : Wick.PhotonSlot gauge2, s.1 = 0 ∧ C.1.2 (.inl j) = .inr s) ↔ c = 0) :=
    fun j c hj => by
      rw [hj]
      constructor
      · rintro ⟨s, hs, h⟩
        rw [Sum.inr.injEq] at h
        rw [← h] at hs
        exact hs
      · rintro rfl
        exact ⟨ps2 0, rfl, rfl⟩
  unfold externalMomentum
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, sub_zero, Fin.sum_univ_two,
    h 0 a hC.photon_zero, h 1 b hC.photon_one]

/-- The loop line carries `ℓ`, the other line `k₀ + ℓ`, where `k₀` is the momentum of the external
photon at vertex `0`. -/
theorem lineMomentum_line1 (hC : IsPolarizationLoop C a b) (pOut pIn : Fin 0 → Fin 4 → ℝ)
    (kIn : Fin 2 → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    lineMomentum C pOut pIn kIn ℓ (.inl hC.line1) =
      (if a = 0 then kIn 0 else 0) + (if b = 0 then kIn 1 else 0) + ℓ := by
  rw [lineMomentum_of_forall_eq_or hC.isLoopLine_iff
      (fun h => hC.line0_ne_line1 (Sum.inl_injective h).symm)
      (fun g => (hC.line_cases g).symm), hC.ends_line1, hC.ends_line0,
    hC.externalMomentum_zero]
  simp

/-! ### Flavors -/

/-- **The flavorings preserved by the closed loop** are the constant ones. -/
theorem preserves_iff (hC : IsPolarizationLoop C a b) (φ : Flavoring gauge2) :
    Preserves C φ ↔ φ = constFlavoring (φ.1 (fv2 0)) := by
  constructor
  · intro hφ
    have h := hφ (.inr (fv2 0))
    rw [hC.psi_zero] at h
    apply Subtype.ext
    funext t
    rcases fv2_eq_or 0 1 (by decide) t with rfl | rfl
    · rfl
    · exact h
  · intro hφ x
    rw [hφ]
    rcases x with i | t
    · exact i.elim0
    · rcases h : C.1.1 (.inr t) with i | s
      · exact i.elim0
      · rfl

/-- The closed fermion loop through both vertices. -/
def closedLoop (_hC : IsPolarizationLoop C a b) : ClosedLoop C :=
  ⟨Quotient.mk _ (.inr (fv2 0)), fun i => i.elim0⟩

/-- The contraction has one closed fermion loop. -/
theorem eq_closedLoop (hC : IsPolarizationLoop C a b) (q : ClosedLoop C) : q = hC.closedLoop := by
  obtain ⟨q, -⟩ := q
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  apply Quotient.sound
  rcases x with i | t
  · exact i.elim0
  · rcases fv2_eq_or 0 1 (by decide) t with rfl | rfl
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨1, by simp [hC.psi_one]⟩

/-- The regulator weight of the flavor-`f` loop is `c_f`. -/
theorem loopWeight_constFlavoring (P : Params) (hC : IsPolarizationLoop C a b) (f : Fin 3) :
    loopWeight P C (constFlavoring f) = P.loopCoeff f := by
  classical
  have hfl : ∀ x : Fin 0 ⊕ Wick.FermionVertex gauge2, fermionFlavor (constFlavoring f) x = f := by
    rintro (i | t)
    · exact i.elim0
    · rfl
  rw [loopWeight]
  simp only [hfl]
  rw [Fintype.prod_eq_single hC.closedLoop fun q hq => absurd (hC.eq_closedLoop q) hq]

/-- **The sum over the preserved flavorings** is the sum over the three flavors. -/
theorem sum_preserves (hC : IsPolarizationLoop C a b) {M : Type*} [AddCommMonoid M]
    [Fintype (Flavoring gauge2)] [DecidablePred (Preserves C)] (F : Flavoring gauge2 → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring gauge2)).filter (Preserves C), F φ =
      ∑ f : Fin 3, F (constFlavoring f) := by
  refine Finset.sum_nbij' (fun φ => φ.1 (fv2 0)) constFlavoring (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hC.preserves_iff _).mpr rfl⟩)
    (fun φ hφ => ((hC.preserves_iff φ).mp (Finset.mem_filter.mp hφ).2).symm) (fun f _ => rfl)
    (fun φ hφ => by rw [← (hC.preserves_iff φ).mp (Finset.mem_filter.mp hφ).2])

/-! ### Amplitude and value -/

/-- **The amplitude of a vacuum polarization loop of flavor `f`**:
`(ie)² (1/i)² Tr[γ^{μ₀} S̃_f(ℓ) γ^{μ₁} S̃_f(k₀ + ℓ)]`, where `μ₀`, `μ₁` are the Lorentz indices at
the vertices `0`, `1` and `k₀` is the momentum of the external photon at vertex `0`. -/
theorem contractionAmplitude_eq (P : Params) (hC : IsPolarizationLoop C a b) (f : Fin 3)
    (pOut pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin 2 → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ)
    (αOut βIn : Fin 0 → Fin 4) (μ : Fin 2 → Fin 4) :
    contractionAmplitude P C (constFlavoring f) pOut pIn kIn ℓ αOut βIn μ =
      (I * P.e) ^ 2 * (1 / I) ^ 2 *
        Matrix.trace (Dirac.gamma (if a = 0 then μ 0 else μ 1) *
          QED.OneLoop.electronPropagator (P.mass f) P.ε ℓ *
          Dirac.gamma (if a = 0 then μ 1 else μ 0) *
          QED.OneLoop.electronPropagator (P.mass f) P.ε
            ((if a = 0 then kIn 0 else 0) + (if b = 0 then kIn 1 else 0) + ℓ)) := by
  have hloop : lineMomentum C pOut pIn kIn ℓ (.inl hC.line0) = ℓ :=
    lineMomentum_of_isLoopLine ((hC.isLoopLine_iff _).mpr rfl) _ _ _ _
  set lor₀ : Wick.PhotonSlot gauge2 → Fin 4 := fun s => if s = ps2 a then μ 0 else μ 1
  have hlor₀ : ∀ t : Fin 2, lor₀ (ps2 t) = if t = a then μ 0 else μ 1 := fun t => by
    simp only [lor₀, ps2_inj]
  rw [contractionAmplitude]
  simp only [IsEmpty.forall_iff, implies_true, true_and,
    lorentz_constraint_iff_of_two hC.photon_zero hC.photon_one, Fin.prod_univ_two,
    vertexFactor_gauge2, hC.prod_fermionLine, hC.prod_photonLine, mul_one, line0_val, line1_val,
    tail_line0, tail_line1, constFlavoring_apply, hloop, hC.lineMomentum_line1]
  rw [show (∑ α : Wick.FermionVertex gauge2 → Fin 4, ∑ β : Wick.FermionVertex gauge2 → Fin 4,
      ∑ lor : Wick.PhotonSlot gauge2 → Fin 4, _) =
      ∑ lor : Wick.PhotonSlot gauge2 → Fin 4, ∑ α : Wick.FermionVertex gauge2 → Fin 4,
        ∑ β : Wick.FermionVertex gauge2 → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  rw [Fintype.sum_eq_single lor₀ fun lor hlor => ?_]
  · have hcond : lor₀ (ps2 a) = μ 0 ∧ lor₀ (ps2 b) = μ 1 := by
      simp [hlor₀, hC.ne.symm]
    simp only [hcond, and_self, ite_true, one_mul, hlor₀]
    rw [sum_polarization_index (fv2_injective.ne (by decide : (0 : Fin 2) ≠ 1))
      (fv2_eq_or 0 1 (by decide))]
    have hab := hC.ne
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
    · simp
    · simp
  · have hne : ¬ (lor (ps2 a) = μ 0 ∧ lor (ps2 b) = μ 1) := fun h => hlor (funext fun s => by
      rcases ps2_eq_or a b hC.ne s with rfl | rfl
      · simp [lor₀, h.1]
      · simp [lor₀, h.2, (ps2_injective.ne hC.ne).symm])
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by
      rw [ite_eq_right hne, zero_mul]

/-- **The value of a vacuum polarization loop.** Minus its value (its fermionic sign is `-1`) is
the energy-first integral of the vacuum polarization integrand of (62.12), with the external
photons carrying `k` and `-k` and the Lorentz indices `μ`, `ν`. The Pauli–Villars flavors are
summed inside the integrand. For `a = 0` the routed trace is the source's by cyclicity; for
`a = 1` it is the source's at the shifted loop momentum `ℓ - k`. -/
theorem neg_contractionValue_eq (P : Params) (hC : IsPolarizationLoop C a b)
    (pOut pIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    -contractionValue P C pOut pIn ![k, -k] αOut βIn ![μ, ν] =
      QED.OneLoop.energyFirstIntegral fun ℓ => vacuumPolarizationIntegrand P P.ε k ℓ μ ν := by
  have hreg : ∀ ℓ, regulatedAmplitude P C pOut pIn ![k, -k] ℓ αOut βIn ![μ, ν] =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude P C (constFlavoring f) pOut pIn ![k, -k] ℓ αOut βIn ![μ, ν] :=
    fun ℓ => by
      classical
      rw [regulatedAmplitude, hC.sum_preserves]
      simp only [hC.loopWeight_constFlavoring]
  rw [contractionValue_of_isLoopLine P ((hC.isLoopLine_iff _).mpr rfl), neg_eq_neg_one_mul,
    ← QED.OneLoop.energyFirstIntegral_const_mul]
  simp only [hreg, hC.contractionAmplitude_eq]
  have hab := hC.ne
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  · congr 1
    funext ℓ
    rw [vacuumPolarizationIntegrand]
    simp only [ite_true, one_ne_zero, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one,
      add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [trace_mul_mul_mul_rotate (QED.OneLoop.electronPropagator _ _ (ℓ + k)), add_comm ℓ k]
    ring
  · rw [← QED.OneLoop.energyFirstIntegral_sub_right_eq_self
      (fun ℓ => vacuumPolarizationIntegrand P P.ε k ℓ μ ν) k]
    congr 1
    funext ℓ
    rw [vacuumPolarizationIntegrand]
    simp only [ite_true, one_ne_zero, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sub_add_cancel, trace_mul_mul_mul_rotate (Dirac.gamma ν), neg_add_eq_sub]
    ring

/-- A vacuum polarization loop is determined by the pairing of the external photons. -/
theorem ext {C' : Contraction 0 2 gauge2} (hC : IsPolarizationLoop C a b)
    (hC' : IsPolarizationLoop C' a b) : C = C' := by
  apply Subtype.ext
  apply Prod.ext
  · ext1 x
    rcases x with i | t
    · exact i.elim0
    · rcases fv2_eq_or 0 1 (by decide) t with rfl | rfl
      · rw [hC.psi_zero, hC'.psi_zero]
      · rw [hC.psi_one, hC'.psi_one]
  · ext1 x
    rcases x with i | s
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · rw [hC.photon_zero, hC'.photon_zero]
      · rw [hC.photon_one, hC'.photon_one]
    · rcases ps2_eq_or a b hC.ne s with rfl | rfl
      · rw [hC.photon_a, hC'.photon_a]
      · rw [hC.photon_b, hC'.photon_b]

end IsPolarizationLoop

/-- **The 1PI contractions of two gauge vertices with two external photons** are the vacuum
polarization loops. With the externals attached there is no internal photon line, so a 1PI
contraction has a fermion line joining the two vertices, which closes into one fermion loop. -/
theorem IsOnePI.exists_isPolarizationLoop {C : Contraction 0 2 gauge2} (hC : IsOnePI C) :
    ∃ a b, IsPolarizationLoop C a b := by
  have hext : ∀ j, ∃ a, C.1.2 (.inl j) = .inr (ps2 a) := fun j => by
    rcases h : C.1.2 (.inl j) with i | s
    · exact absurd h (hC.1.2 j i)
    · exact ⟨s.1, by rw [ps2_fst_eq]⟩
  obtain ⟨a, ha⟩ := hext 0
  obtain ⟨b, hb⟩ := hext 1
  have hab : a ≠ b := by
    rintro rfl
    exact absurd (Sum.inl_injective (C.1.2.injective (ha.trans hb.symm))) (by decide)
  have := isEmpty_photonLine_of_two hab ha hb
  obtain ⟨f₁, -, -, h₁, -⟩ := hC.exists_crosses_ne (v := 0) (w := 1) (by decide)
  rcases f₁ with ⟨t, ht⟩ | g
  swap
  · exact isEmptyElim g
  obtain ⟨s, hs⟩ : ∃ s, C.1.1 (.inr t) = .inr s := by
    rcases h : C.1.1 (.inr t) with i | s
    · exact i.elim0
    · exact ⟨s, rfl⟩
  have hst : s ≠ t := by
    intro h
    apply h₁.1
    change (FermionLine.tail ⟨t, ht⟩).1 = t.1
    rw [FermionLine.tail_eq hs, h]
  refine ⟨a, b, hab, ha, hb, ?_⟩
  rcases fv2_eq_or 0 1 (by decide) t with rfl | rfl
  · rcases fv2_eq_or 0 1 (by decide) s with rfl | rfl
    · exact absurd rfl hst
    · exact hs
  · obtain rfl : s = fv2 0 := (fv2_eq_or 0 1 (by decide) s).resolve_right hst
    rcases h : C.1.1 (.inr (fv2 0)) with i | u
    · exact i.elim0
    · rcases fv2_eq_or 0 1 (by decide) u with rfl | rfl
      · exact absurd (fv2_injective (Sum.inr_injective (C.1.1.injective (h.trans hs.symm))))
          (by decide)
      · rfl

/-- The 1PI contractions of two gauge vertices with two external photons are exactly the vacuum
polarization loops. -/
theorem isOnePI_iff_exists_isPolarizationLoop (C : Contraction 0 2 gauge2) :
    IsOnePI C ↔ ∃ a b, IsPolarizationLoop C a b :=
  ⟨IsOnePI.exists_isPolarizationLoop, fun ⟨_, _, h⟩ => h.isOnePI⟩

/-! ### The two vacuum polarization loops -/

/-- The fermion pairing of the vacuum polarization loop: one closed loop through both
vertices. -/
def polarizationFermionPairing : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex gauge2) :=
  Equiv.swap (.inr (fv2 0)) (.inr (fv2 1))

/-- The photon pairing of the vacuum polarization loop: `A(z₁)` with the photon field of `a` and
`A(z₂)` with that of `b`. -/
def polarizationPhotonPairing (a b : Fin 2) : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot gauge2) :=
  Equiv.swap (.inl 0) (.inr (ps2 a)) * Equiv.swap (.inl 1) (.inr (ps2 b))

/-- The photon pairing is a fixed-point-free involution. -/
theorem polarizationPhotonPairing_involutive : ∀ a b : Fin 2, a ≠ b →
    ∀ x, polarizationPhotonPairing a b (polarizationPhotonPairing a b x) = x ∧
      polarizationPhotonPairing a b x ≠ x := by
  decide

/-- The photon pairing sends `A(z₁)` to the photon field of `a` and `A(z₂)` to that of `b`. -/
theorem polarizationPhotonPairing_apply : ∀ a b : Fin 2, a ≠ b →
    polarizationPhotonPairing a b (.inl 0) = .inr (ps2 a) ∧
      polarizationPhotonPairing a b (.inl 1) = .inr (ps2 b) := by
  decide

/-- The vacuum polarization loop with `A(z₁)` at the vertex `a`, as a contraction. -/
def polarizationLoop (a b : Fin 2) (hab : a ≠ b) : Contraction 0 2 gauge2 :=
  ⟨(polarizationFermionPairing, polarizationPhotonPairing a b),
    polarizationPhotonPairing_involutive a b hab⟩

/-- `polarizationLoop a b` is the vacuum polarization loop with `A(z₁)` at the vertex `a`. -/
theorem isPolarizationLoop_polarizationLoop (a b : Fin 2) (hab : a ≠ b) :
    IsPolarizationLoop (polarizationLoop a b hab) a b :=
  ⟨hab, (polarizationPhotonPairing_apply a b hab).1, (polarizationPhotonPairing_apply a b hab).2,
    Equiv.swap_apply_left _ _⟩

/-- A vacuum polarization loop has fermionic sign `-1`: `(-1)²` from the vertices times the sign
`-1` of a transposition, the sign of a closed fermion loop. -/
theorem fermionSign_polarizationLoop (a b : Fin 2) (hab : a ≠ b) :
    fermionSign (polarizationLoop a b hab) = -1 := by
  have h : (Sum.inr (fv2 0) : Fin 0 ⊕ Wick.FermionVertex gauge2) ≠ .inr (fv2 1) :=
    fun h => absurd (fv2_injective (Sum.inr_injective h)) (by decide)
  rw [fermionSign, card_fermionVertex_gauge2]
  simp [polarizationLoop, polarizationFermionPairing, Equiv.Perm.sign_swap h]

/-- **The 1PI part of two gauge vertices with two external photons** of momenta `k` and `-k`: the
two vacuum polarization loops, each of sign `-1` and with minus the energy-first integral of the
vacuum polarization integrand as value. -/
theorem sum_isOnePI_polarizationLoop (P : Params) [Fintype (Contraction 0 2 gauge2)]
    [DecidablePred (IsOnePI (nf := 0) (nA := 2) (κ := gauge2))]
    (pOut pIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 0 2 gauge2)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn ![k, -k] αOut βIn ![μ, ν] =
      2 * QED.OneLoop.energyFirstIntegral fun ℓ => vacuumPolarizationIntegrand P P.ε k ℓ μ ν := by
  classical
  have h01 := isPolarizationLoop_polarizationLoop 0 1 (by decide)
  have h10 := isPolarizationLoop_polarizationLoop 1 0 (by decide)
  have hfilter : (Finset.univ : Finset (Contraction 0 2 gauge2)).filter IsOnePI =
      {polarizationLoop 0 1 (by decide), polarizationLoop 1 0 (by decide)} := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hC
      obtain ⟨a, b, h⟩ := hC.exists_isPolarizationLoop
      have hab := h.ne
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
      · exact Or.inl (h.ext h01)
      · exact Or.inr (h.ext h10)
    · rintro (rfl | rfl)
      · exact h01.isOnePI
      · exact h10.isOnePI
  have hne : polarizationLoop 0 1 (by decide) ≠ polarizationLoop 1 0 (by decide) := fun h => by
    have h' := h01.photon_zero
    rw [h, h10.photon_zero, Sum.inr.injEq, ps2_inj] at h'
    exact absurd h' (by decide)
  have e01 := h01.neg_contractionValue_eq P pOut pIn αOut βIn k μ ν
  have e10 := h10.neg_contractionValue_eq P pOut pIn αOut βIn k μ ν
  rw [hfilter, Finset.sum_pair hne, fermionSign_polarizationLoop, fermionSign_polarizationLoop]
  push_cast
  linear_combination e01 + e10

end QED.WickModel

end
