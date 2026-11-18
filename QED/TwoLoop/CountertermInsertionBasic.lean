/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RelabelCountertermClasses
public import QED.TwoLoop.EnumerationDecide
public import QED.TwoLoop.JointIntegral
public import QED.Frozen.OneLoop.PhotonPropagator
public import QED.Algebra.Minkowski

/-!
# One-loop counterterm classes: the value as one energy-first integral

Common reductions for the explicit evaluation of the seven counterterm class representatives of
the order-`e⁵` vertex (`QED/TwoLoop/RelabelCountertermClasses.lean`), each a contraction with one
loop (obligation O2-13, `docs/TWO-LOOP-DERIVATION.md`, section 5.1).

* `QED.TwoLoop.Insertion.regulatedAmplitude₂_eq_zeroFlavoring`: if every fermion field lies on the
  cycle of `σ` through the external field (no closed fermion loop), the regulated amplitude (T₈)
  is the amplitude (T₇) with every fermion an electron.
* `QED.TwoLoop.Insertion.contractionValue₂_eq_energyFirstIntegral`: for a contraction with exactly
  one chord `c` (T₁) and a momentum assignment `mom ℓ` that is conserved at every vertex and gives
  `c` the momentum `ℓ`, the value (T₁₀) is the frozen energy-first integral (D) of
  `(2π)⁻⁴` times the regulated amplitude at `mom ℓ`.
* Finite products and sums over two or three lines.
-/

@[expose] public section

namespace QED.TwoLoop.Insertion

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Products and sums over few elements -/

section Few

variable {X M : Type*} [Fintype X] [DecidableEq X]

theorem prod_eq_of_two [CommMonoid M] {a b : X} (hab : a ≠ b) (hX : ∀ x, x = a ∨ x = b)
    (g : X → M) : ∏ x, g x = g a * g b := by
  have : (Finset.univ : Finset X) = {a, b} := by
    ext x
    simpa using hX x
  rw [this, Finset.prod_pair hab]

omit [DecidableEq X] in
theorem prod_eq_of_one [CommMonoid M] {a : X} (hX : ∀ x, x = a) (g : X → M) : ∏ x, g x = g a := by
  have : (Finset.univ : Finset X) = {a} := by
    ext x
    simpa using hX x
  rw [this, Finset.prod_singleton]

theorem sum_eq_of_two [AddCommMonoid M] {a b : X} (hab : a ≠ b) (hX : ∀ x, x = a ∨ x = b)
    (g : X → M) : ∑ x, g x = g a + g b := by
  have : (Finset.univ : Finset X) = {a, b} := by
    ext x
    simpa using hX x
  rw [this, Finset.sum_pair hab]

theorem prod_eq_of_three [CommMonoid M] {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hX : ∀ x, x = a ∨ x = b ∨ x = c) (g : X → M) : ∏ x, g x = g a * g b * g c := by
  have : (Finset.univ : Finset X) = {a, b, c} := by
    ext x
    simpa using hX x
  rw [this, Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc, mul_assoc]

theorem sum_eq_of_three [AddCommMonoid M] {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hX : ∀ x, x = a ∨ x = b ∨ x = c) (g : X → M) : ∑ x, g x = g a + g b + g c := by
  have : (Finset.univ : Finset X) = {a, b, c} := by
    ext x
    simpa using hX x
  rw [this, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, add_assoc]

theorem sum_eq_of_four [AddCommMonoid M] {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hX : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d)
    (g : X → M) : ∑ x, g x = g a + g b + g c + g d := by
  have : (Finset.univ : Finset X) = {a, b, c, d} := by
    ext x
    simpa using hX x
  rw [this, Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_pair hcd, add_assoc, add_assoc]

/-- An indicator of a conjunction is the product of the indicators, for any decidability
instance of the conjunction (the frozen amplitudes decide classically). -/
theorem ite_and_eq_mul (A B : Prop) {inst : Decidable (A ∧ B)} [Decidable A] [Decidable B] :
    @ite ℂ (A ∧ B) inst 1 0 = (if A then 1 else 0) * (if B then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

end Few

/-! ### The energy-first integral and the photon propagator -/

/-- The energy-first integral commutes with a constant factor, for every integrand. -/
theorem energyFirstIntegral_const_mul' (c : ℂ) (F : (Fin 4 → ℝ) → ℂ) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => c * F ℓ) = c * QED.OneLoop.energyFirstIntegral F := by
  unfold QED.OneLoop.energyFirstIntegral
  simp only [MeasureTheory.integral_const_mul]

/-- The photon propagator is even in its momentum. -/
theorem photonPropagator_neg' (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε (-k) μ ν = QED.OneLoop.photonPropagator mγ Λ ε k μ ν := by
  simp [QED.OneLoop.photonPropagator, Minkowski.dot]

/-- The photon propagator is symmetric in its Lorentz indices. -/
theorem photonPropagator_comm' (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k μ ν = QED.OneLoop.photonPropagator mγ Λ ε k ν μ := by
  simp only [QED.OneLoop.photonPropagator, Minkowski.metric_symm μ ν]

/-! ### Flavorings -/

/-- The flavoring in which every fermion field is an electron. -/
def zeroFlavoring (κ : Fin N → Wick.VertexKind) : Flavoring κ :=
  ⟨fun _ => 0, fun _ _ => rfl⟩

theorem preserves_zeroFlavoring {nf : ℕ} (C : Contraction nf nA κ) :
    Preserves C (zeroFlavoring κ) := fun a => by
  rcases C.1.1 a with _ | _ <;> rcases a with _ | _ <;> rfl

open scoped Classical in
/-- **No closed fermion loop**: if every fermion field lies on the cycle of `σ` through the
external field, only the all-electron flavoring is preserved and its weight is `1`, so the
regulated amplitude (T₈) is the amplitude (T₇) of that flavoring. -/
theorem regulatedAmplitude₂_eq_zeroFlavoring (P : Params) {C : Contraction 1 nA κ}
    (hC : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P C pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P C (zeroFlavoring κ) pIn kIn k αOut βIn μ := by
  have hpres : ∀ φ, Preserves C φ ↔ φ = zeroFlavoring κ := fun φ =>
    ⟨fun hφ => Subtype.ext (funext fun t =>
        QED.TwoLoop.Relabel.fermionFlavor_eq_of_sameCycle hφ (hC (.inr t))),
      fun h => h ▸ preserves_zeroFlavoring C⟩
  have hfil : (Finset.univ : Finset (Flavoring κ)).filter (Preserves C) = {zeroFlavoring κ} :=
    Finset.ext fun φ => by simp [hpres]
  have hempty : IsEmpty (ClosedLoop C) := by
    refine ⟨fun ⟨q, hq⟩ => ?_⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact hq 0 (Quotient.sound (hC x).symm)
  have hw : loopWeight P C (zeroFlavoring κ) = 1 := by
    simp [loopWeight]
  rw [regulatedAmplitude₂, hfil, Finset.sum_singleton, hw, Complex.ofReal_one, one_mul]

/-- A cycle condition checkable by `decide`: every fermion field reaches the external field. -/
theorem sameCycle_of_pow {C : Contraction 1 nA κ} {n : ℕ}
    (h : ∀ x, ∃ i : Fin n, (C.1.1 ^ (i : ℕ)) x = .inl 0) (x : Fin 1 ⊕ Wick.FermionVertex κ) :
    Equiv.Perm.SameCycle C.1.1 x (.inl 0) := by
  obtain ⟨i, hi⟩ := h x
  exact ⟨(i : ℕ), by rw [zpow_natCast]; exact hi⟩

/-! ### One chord -/

open scoped Classical in
/-- With exactly one chord `c`, the loop count (T₂) is `1`. -/
theorem loopCount_eq_one_of_unique {nf : ℕ} {C : Contraction nf nA κ} {c : Line C}
    (hc : ∀ g, IsChord g ↔ g = c) : loopCount C = 1 := by
  unfold loopCount
  rw [Finset.card_eq_one]
  exact ⟨c, Finset.ext fun g => by simp [hc]⟩

open scoped Classical in
/-- With exactly one chord `c`, the chord carries the loop momentum `ℓ 0` (T₃). -/
theorem chordMomentum_of_unique {nf : ℕ} {C : Contraction nf nA κ} {c : Line C}
    (hc : ∀ g, IsChord g ↔ g = c) (ℓ : Fin 1 → Fin 4 → ℝ) : chordMomentum ℓ c = ℓ 0 := by
  have h0 : (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < c.label).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rw [(hc g).mp hg] at hl
    exact lt_irrefl _ hl
  unfold chordMomentum
  split_ifs with h
  · congr 1
    exact Fin.ext (by rw [Fin.val_zero]; convert h0)
  · exact absurd (by convert (show 0 < 1 by norm_num) using 2; convert h0) h

/-- **The value of a contraction with one chord** (T₁₀): if `c` is the only chord and `mom ℓ` is a
momentum assignment conserved at every vertex that gives `c` the momentum `ℓ`, the value is the
frozen energy-first integral of `(2π)⁻⁴` times the regulated amplitude at `mom ℓ`. -/
theorem contractionValue₂_eq_energyFirstIntegral (P : Params) {nf : ℕ} {C : Contraction nf nA κ}
    {c : Line C} (hc : ∀ g, IsChord g ↔ g = c) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (mom : (Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ)) (hchord : ∀ ℓ, mom ℓ c = ℓ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue₂ P C pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * regulatedAmplitude₂ P C pIn kIn (mom ℓ) αOut βIn μ := by
  rw [QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P (loopCount_eq_one_of_unique hc)]
  have hline : ∀ ℓ : Fin 1 → Fin 4 → ℝ, lineMomentum₂ C pOut pIn kIn ℓ = mom (ℓ 0) := by
    intro ℓ
    funext f
    refine (eq_lineMomentum₂_of_isConserved (hcons (ℓ 0)) (fun g hg => ?_) f).symm
    rw [(hc g).mp hg, hchord, chordMomentum_of_unique hc]
  simp only [hline, mul_one]
  exact jointEnergyFirstIntegral_one_eq fun ℓ =>
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * regulatedAmplitude₂ P C pIn kIn (mom ℓ) αOut βIn μ

/-- The external momenta (X₁₉) of a contraction with one external fermion pair and one external
photon. -/
theorem externalMomentum_one_one {C : Contraction 1 1 κ} (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (v : Fin N) :
    externalMomentum C pOut pIn kIn v =
      (if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl 0 then pIn 0 else 0) +
        (if ∃ a : Wick.PhotonSlot κ, a.1 = v ∧ C.1.2 (.inl 0) = .inr a then kIn 0 else 0) -
        (if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl 0) = .inr t then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one]

end QED.TwoLoop.Insertion

end
