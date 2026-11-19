/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumReps
public import QED.TwoLoop.IntegrableOrderFiveCt
public import QED.ChainProof.IntegrableChainReduction

/-!
# (T₉′) for the `δ₃`–`δ₃` representatives of set (b)

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53): the value integrand of
each of the four one-loop representatives `repDD s₀ s₁` (two `photonCt` vertices on the internal
photon line, fields `s₀`, `s₁` towards `a`) satisfies (T₉′) at `ε > 0`, for all masses, cutoffs
and counterterms, under momentum conservation (`chainValueIntegrable_repDD`). This is the `repDD`
part of `QED.ChainProof.RepsIntegrable`.

## Proof

* **Lines and routing.** `repDD s₀ s₁` has one chord, the fermion line `0 → 1`; the routing `ddMom`
  gives it `ℓ`, the line `1 → 2` the momentum `ℓ + k`, and the three photon lines `±(ℓ - p)`
  (`ddMom_isConserved`).
* **The amplitude** (`regulatedAmplitude₂_repDD`): in this routing the integrand is the one-loop
  vertex chain `vertexChain` whose photon factor is the doubly inserted photon line
  `photonDD = (1/i)² Δ̃ V Δ̃ V Δ̃`, at `q = ℓ - p` (both slot pairings at both vertices give the
  same integrand, since the propagator and the `photonCt` factor are even and symmetric).
* **The numerator is reduced to degree four.** With `V = -(i/2) δ₃ T`, `T = k² g - k k`, one has
  `T g T = k² T`, so `photonDD(k) = -(δ₃/2) k² d(k) · photonInsertion(k)` (`photonDD_eq`), with
  `d` the Pauli–Villars photon scalar; and `k² d(k) = (Λ² - m_γ²)(D_Λ⁻¹ - (m_γ² - iε) D_γ⁻¹ D_Λ⁻¹)`.
  So the integrand is a combination of the order-five `δ₃` numerator `numD3` (degree four) over
  the `δ₃` denominators times one or two further photon denominators.
* **Both pieces** satisfy the one-loop criterion through the auxiliary loop
  (`QED.TwoLoop.IntegrableOrderFive.energyFirst_of_kinds`, with ten, resp. eleven, lines; the
  refined criterion is decided).
-/

@[expose] public section

open MeasureTheory Complex

namespace QED.ChainProof.RepsInt

open QED.WickModel QED.ChainProof.Enum QED.TwoLoop.Routing QED.TwoLoop.Enumeration
  QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge

/-! ### Finite sums -/

section Few

variable {X M : Type*} [Fintype X] [DecidableEq X]

theorem sum_eq_of_five [AddCommMonoid M] {a b c d e : X} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) (hX : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e) (g : X → M) :
    ∑ x, g x = g a + g b + g c + g d + g e := by
  have : (Finset.univ : Finset X) = {a, b, c, d, e} := by
    ext x
    simpa using hX x
  rw [this, Finset.sum_insert (by simp [hab, hac, had, hae]),
    Finset.sum_insert (by simp [hbc, hbd, hbe]), Finset.sum_insert (by simp [hcd, hce]),
    Finset.sum_pair hde]
  abel

theorem prod_eq_of_three' [CommMonoid M] {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hX : ∀ x, x = a ∨ x = b ∨ x = c) (g : X → M) : ∏ x, g x = g a * g b * g c := by
  have : (Finset.univ : Finset X) = {a, b, c} := by
    ext x
    simpa using hX x
  rw [this, Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc, mul_assoc]

variable {R : Type*} [Fintype R]

/-- A sum over the functions on a type covered by seven distinct elements. -/
theorem sum_pi_seven [AddCommMonoid M] {x₁ x₂ x₃ x₄ x₅ x₆ x₇ : X}
    (hd : [x₁, x₂, x₃, x₄, x₅, x₆, x₇].Nodup)
    (hX : ∀ x, x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x = x₄ ∨ x = x₅ ∨ x = x₆ ∨ x = x₇)
    (g : (X → R) → M) :
    ∑ f, g f = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ u, ∑ w,
      g (fun t => if t = x₁ then a else if t = x₂ then b else if t = x₃ then c else
        if t = x₄ then d else if t = x₅ then e else if t = x₆ then u else w) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, not_false_eq_true, and_true] at hd
  obtain ⟨⟨h12, h13, h14, h15, h16, h17⟩, ⟨h23, h24, h25, h26, h27⟩, ⟨h34, h35, h36, h37⟩,
    ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67⟩ := hd
  let E : (X → R) ≃ R × R × R × R × R × R × R :=
    { toFun := fun f => (f x₁, f x₂, f x₃, f x₄, f x₅, f x₆, f x₇)
      invFun := fun q t =>
        if t = x₁ then q.1 else if t = x₂ then q.2.1 else if t = x₃ then q.2.2.1 else
          if t = x₄ then q.2.2.2.1 else if t = x₅ then q.2.2.2.2.1 else
            if t = x₆ then q.2.2.2.2.2.1 else q.2.2.2.2.2.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17,
            Ne.symm h23, Ne.symm h24, Ne.symm h25, Ne.symm h26, Ne.symm h27, Ne.symm h34,
            Ne.symm h35, Ne.symm h36, Ne.symm h37, Ne.symm h45, Ne.symm h46, Ne.symm h47,
            Ne.symm h56, Ne.symm h57, Ne.symm h67]
      right_inv := fun q => by
        simp [Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17,
          Ne.symm h23, Ne.symm h24, Ne.symm h25, Ne.symm h26, Ne.symm h27, Ne.symm h34,
          Ne.symm h35, Ne.symm h36, Ne.symm h37, Ne.symm h45, Ne.symm h46, Ne.symm h47,
          Ne.symm h56, Ne.symm h57, Ne.symm h67] }
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

end Few

/-! ### The lines of `repDD s₀ s₁` -/

section Lines

variable (s₀ s₁ : Fin 2)

/-- The fermion line `0 → 1`, the chord. -/
def ddF1 : FermionLine (repDD s₀ s₁) := ⟨fv kDD 1, by revert s₀ s₁; decide +kernel⟩
/-- The fermion line `1 → 2`. -/
def ddF2 : FermionLine (repDD s₀ s₁) := ⟨fv kDD 2, by revert s₀ s₁; decide +kernel⟩
/-- The photon line `2 → 3` (from `a` to the field `s₀` of the first `photonCt` vertex). -/
def ddGA : PhotonLine (repDD s₀ s₁) := ⟨pg kDD 2, by revert s₀ s₁; decide +kernel⟩
/-- The photon line `3 → 4` (between the two `photonCt` vertices). -/
def ddGB : PhotonLine (repDD s₀ s₁) := ⟨pc kDD 3 s₀.rev, by revert s₀ s₁; decide +kernel⟩
/-- The photon line `0 → 4` (from `c` to the field `s₁.rev` of the second `photonCt` vertex). -/
def ddGC : PhotonLine (repDD s₀ s₁) := ⟨pg kDD 0, by revert s₀ s₁; decide +kernel⟩

theorem dd_fermionLine_cases :
    ∀ s₀ s₁ (f : FermionLine (repDD s₀ s₁)), f = ddF1 s₀ s₁ ∨ f = ddF2 s₀ s₁ := by
  decide +kernel

theorem dd_photonLine_cases : ∀ s₀ s₁ (g : PhotonLine (repDD s₀ s₁)),
    g = ddGA s₀ s₁ ∨ g = ddGB s₀ s₁ ∨ g = ddGC s₀ s₁ := by
  decide +kernel

theorem dd_line_cases (f : Line (repDD s₀ s₁)) :
    f = .inl (ddF1 s₀ s₁) ∨ f = .inl (ddF2 s₀ s₁) ∨ f = .inr (ddGA s₀ s₁) ∨
      f = .inr (ddGB s₀ s₁) ∨ f = .inr (ddGC s₀ s₁) := by
  rcases f with f | g
  · rcases dd_fermionLine_cases s₀ s₁ f with rfl | rfl <;> simp
  · rcases dd_photonLine_cases s₀ s₁ g with rfl | rfl | rfl <;> simp

theorem dd_isChord_iff : ∀ s₀ s₁ (g : Line (repDD s₀ s₁)), IsChord g ↔ g = .inl (ddF1 s₀ s₁) := by
  decide +kernel

theorem dd_ends : ∀ s₀ s₁,
    (Line.ends (.inl (ddF1 s₀ s₁) : Line (repDD s₀ s₁))) = (0, 1) ∧
    (Line.ends (.inl (ddF2 s₀ s₁) : Line (repDD s₀ s₁))) = (1, 2) ∧
    (Line.ends (.inr (ddGA s₀ s₁) : Line (repDD s₀ s₁))) = (2, 3) ∧
    (Line.ends (.inr (ddGB s₀ s₁) : Line (repDD s₀ s₁))) = (3, 4) ∧
    (Line.ends (.inr (ddGC s₀ s₁) : Line (repDD s₀ s₁))) = (0, 4) := by
  decide +kernel

theorem dd_tails : ∀ s₀ s₁, (ddF1 s₀ s₁).tail = fv kDD 0 ∧ (ddF2 s₀ s₁).tail = fv kDD 1 ∧
    (ddGA s₀ s₁).head = pc kDD 3 s₀ ∧ (ddGB s₀ s₁).head = pc kDD 4 s₁ ∧
    (ddGC s₀ s₁).head = pc kDD 4 s₁.rev := by
  decide +kernel

theorem dd_ext : ∀ s₀ s₁ (v : Fin 5),
    ((∃ t : Wick.FermionVertex kDD, t.1 = v ∧ (repDD s₀ s₁).1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kDD, a.1 = v ∧ (repDD s₀ s₁).1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kDD, t.1 = v ∧ (repDD s₀ s₁).1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  decide +kernel

end Lines

/-! ### The routing -/

section Routing

variable (s₀ s₁ : Fin 2)

/-- The routing of `repDD s₀ s₁`: `ℓ` on `0 → 1`, `ℓ + k` on `1 → 2`, `ℓ - p` on the photon lines
`2 → 3` and `3 → 4`, and `p - ℓ` on the photon line `0 → 4`. -/
def ddMom (p k ℓ : Fin 4 → ℝ) (f : Line (repDD s₀ s₁)) : Fin 4 → ℝ :=
  if f = .inl (ddF1 s₀ s₁) then ℓ else if f = .inl (ddF2 s₀ s₁) then ℓ + k
    else if f = .inr (ddGC s₀ s₁) then p - ℓ else ℓ - p

theorem ddMom_apply (p k ℓ : Fin 4 → ℝ) : ddMom s₀ s₁ p k ℓ (.inl (ddF1 s₀ s₁)) = ℓ ∧
    ddMom s₀ s₁ p k ℓ (.inl (ddF2 s₀ s₁)) = ℓ + k ∧
    ddMom s₀ s₁ p k ℓ (.inr (ddGA s₀ s₁)) = ℓ - p ∧
    ddMom s₀ s₁ p k ℓ (.inr (ddGB s₀ s₁)) = ℓ - p ∧
    ddMom s₀ s₁ p k ℓ (.inr (ddGC s₀ s₁)) = p - ℓ := by
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_, ?_⟩
  · rw [ddMom, ite_eq_right (by simp [ddF1, ddF2, fv]), ite_eq_left rfl]
  · rw [ddMom, ite_eq_right (by simp), ite_eq_right (by simp),
      ite_eq_right (by simp [ddGA, ddGC, pg])]
  · rw [ddMom, ite_eq_right (by simp), ite_eq_right (by simp),
      ite_eq_right (by simp [ddGB, ddGC, pg, pc])]
  · rw [ddMom, ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_left rfl]

theorem ddMom_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 4 → ℝ) : IsConserved (repDD s₀ s₁) pOut pIn kIn (ddMom s₀ s₁ (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := dd_ends s₀ s₁
  obtain ⟨m1, m2, m3, m4, m5⟩ := ddMom_apply s₀ s₁ (pIn 0) (kIn 0) ℓ
  have hne : ((Sum.inl (ddF1 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inl (ddF2 s₀ s₁) ∧
      (Sum.inl (ddF1 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGA s₀ s₁) ∧
      (Sum.inl (ddF1 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGB s₀ s₁) ∧
      (Sum.inl (ddF1 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGC s₀ s₁) ∧
      (Sum.inl (ddF2 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGA s₀ s₁) ∧
      (Sum.inl (ddF2 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGB s₀ s₁) ∧
      (Sum.inl (ddF2 s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGC s₀ s₁) ∧
      (Sum.inr (ddGA s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGB s₀ s₁) ∧
      (Sum.inr (ddGA s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGC s₀ s₁) ∧
      (Sum.inr (ddGB s₀ s₁) : Line (repDD s₀ s₁)) ≠ .inr (ddGC s₀ s₁)) := by
    simp [ddF1, ddF2, ddGA, ddGB, ddGC, fv, pg, pc]
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hne
  intro v
  rw [inflow, sum_eq_of_five n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 (dd_line_cases s₀ s₁),
    externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := dd_ext s₀ s₁ v
  simp only [e1, e2, e3, e4, e5, x1, x2, x3, m1, m2, m3, m4, m5]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

end Routing

/-! ### The amplitude -/

section Amplitude

variable (s₀ s₁ : Fin 2)

theorem dd_cond (α β : Wick.FermionVertex kDD → Fin 4) (lor : Wick.PhotonSlot kDD → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, (repDD s₀ s₁).1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, (repDD s₀ s₁).1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, (repDD s₀ s₁).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kDD 1) = μ 0 ∧ (α (fv kDD 2) = αOut 0 ∧ β (fv kDD 0) = βIn 0) := by
  have h1 : ∀ s₀ s₁ t, (repDD s₀ s₁).1.1 (.inl 0) = .inr t ↔ t = fv kDD 2 := by decide +kernel
  have h2 : ∀ s₀ s₁ t, (repDD s₀ s₁).1.1 (.inr t) = .inl 0 ↔ t = fv kDD 0 := by decide +kernel
  have h3 : ∀ s₀ s₁ a, (repDD s₀ s₁).1.2 (.inl 0) = .inr a ↔ a = pg kDD 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- In the routing `ddMom`, the momentum entering a field of a `photonCt` vertex is `±(ℓ - p)`. -/
theorem dd_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (p k ℓ : Fin 4 → ℝ) :
    ∀ a : Wick.PhotonSlot kDD, (a.1 = 3 ∨ a.1 = 4) →
      photonMomentum₂ (repDD s₀ s₁) kIn (ddMom s₀ s₁ p k ℓ) a = ℓ - p ∨
        photonMomentum₂ (repDD s₀ s₁) kIn (ddMom s₀ s₁ p k ℓ) a = -(ℓ - p) := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := ddMom_apply s₀ s₁ p k ℓ
  obtain ⟨-, -, t3, t4, t5⟩ := dd_tails s₀ s₁
  have hext : ∀ s₀ s₁ (a : Wick.PhotonSlot kDD), (a.1 = 3 ∨ a.1 = 4) →
      ¬ (repDD s₀ s₁).1.2 (.inl 0) = .inr a := by decide +kernel
  have hAB : ∀ s₀ s₁, ddGA s₀ s₁ ≠ ddGB s₀ s₁ ∧ ddGA s₀ s₁ ≠ ddGC s₀ s₁ ∧
      ddGB s₀ s₁ ≠ ddGC s₀ s₁ := by decide +kernel
  obtain ⟨n1, n2, n3⟩ := hAB s₀ s₁
  intro a ha
  have hA1 : (ddGA s₀ s₁).1 = pg kDD 2 := rfl
  have hB1 : (ddGB s₀ s₁).1 = pc kDD 3 s₀.rev := rfl
  have hC1 : (ddGC s₀ s₁).1 = pg kDD 0 := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right (hext s₀ s₁ a ha),
    sum_eq_of_three n1 n2 n3 (dd_photonLine_cases s₀ s₁), t3, t4, t5, hA1, hB1, hC1, m3, m4, m5]
  obtain ⟨t, i⟩ := a
  simp only at ha
  rcases ha with rfl | rfl <;> fin_cases i <;> fin_cases s₀ <;> fin_cases s₁ <;>
    simp +decide

/-- The photon line with two `photonCt` insertions, in the normalization of the photon slot of
`vertexChain`: `(1/i)² ∑_{a b c d} Δ̃_{νa}(k) V^{ab}(k) Δ̃_{bc}(k) V^{cd}(k) Δ̃_{ρd}(k)`. -/
noncomputable def photonDD (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  (1 / I) ^ 2 * ∑ a, ∑ b, ∑ c, ∑ d,
    QED.OneLoop.photonPropagator mγ Λ ε k ν a * photonCtFactor δ₃ k a b *
      QED.OneLoop.photonPropagator mγ Λ ε k b c * photonCtFactor δ₃ k c d *
        QED.OneLoop.photonPropagator mγ Λ ε k ρ d

/-- **The amplitude of `repDD s₀ s₁` in the routing `ddMom`**: the one-loop vertex chain with the
doubly inserted photon line at `q = ℓ - p`. -/
theorem dd_amplitude (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repDD s₀ s₁) (zeroFlavoring kDD) pIn kIn
        (ddMom s₀ s₁ (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      (I * P.e) * (I * P.e) * (I * P.e) * (1 / I) ^ 3 *
        ∑ ν, ∑ ρ, photonDD P.δ₃ P.mγ P.Λ P.ε (ℓ - pIn 0) ν ρ *
          (Dirac.gamma ρ * QED.OneLoop.electronPropagator P.m P.ε (ℓ + kIn 0) *
            Dirac.gamma (μ 0) * QED.OneLoop.electronPropagator P.m P.ε ℓ *
            Dirac.gamma ν) (αOut 0) (βIn 0) := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := ddMom_apply s₀ s₁ (pIn 0) (kIn 0) ℓ
  obtain ⟨t1, t2, t3, t4, t5⟩ := dd_tails s₀ s₁
  have m5' : ddMom s₀ s₁ (pIn 0) (kIn 0) ℓ (.inr (ddGC s₀ s₁)) = -(ℓ - pIn 0) := by
    rw [m5]; abel
  have hct : ∀ (t : Fin 5) (h : kDD t = .photonCt), (t = 3 ∨ t = 4) →
      ∀ (α β : Wick.FermionVertex kDD → Fin 4) (lor : Wick.PhotonSlot kDD → Fin 4),
      Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
          (psiMomentum₂ (repDD s₀ s₁) pIn (ddMom s₀ s₁ (pIn 0) (kIn 0) ℓ))
          (photonMomentum₂ (repDD s₀ s₁) kIn (ddMom s₀ s₁ (pIn 0) (kIn 0) ℓ)) t =
        photonCtFactor P.δ₃ (ℓ - pIn 0) (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
          (lor ⟨t, ⟨1, by simp [h, Wick.VertexKind.photonSlots]⟩⟩) := by
    intro t h ht α β lor
    rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ h]
    rcases dd_photonMomentum s₀ s₁ kIn (pIn 0) (kIn 0) ℓ
        ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩ ht with e | e
    · rw [e]; rfl
    · rw [e, ← photonCtFactor_neg]; rfl
  have nf : ddF1 s₀ s₁ ≠ ddF2 s₀ s₁ := by simp [ddF1, ddF2, fv]
  have nAB : ∀ s₀ s₁, ddGA s₀ s₁ ≠ ddGB s₀ s₁ ∧ ddGA s₀ s₁ ≠ ddGC s₀ s₁ ∧
      ddGB s₀ s₁ ≠ ddGC s₀ s₁ := by decide +kernel
  obtain ⟨n1, n2, n3⟩ := nAB s₀ s₁
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kDD → Fin 4, ∑ β : Wick.FermionVertex kDD → Fin 4,
      ∑ lor : Wick.PhotonSlot kDD → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kDD → Fin 4,
    (if lor (pg kDD 1) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) * (I * P.e) * (I * P.e) * (1 / I) ^ 3 *
        ((1 / I) ^ 2 *
          (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0)
              (lor (pg kDD 0)) (lor (pc kDD 4 s₁.rev)) *
            photonCtFactor P.δ₃ (ℓ - pIn 0) (lor ⟨4, ⟨0, by decide⟩⟩) (lor ⟨4, ⟨1, by decide⟩⟩) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0)
              (lor (pc kDD 3 s₀.rev)) (lor (pc kDD 4 s₁)) *
            photonCtFactor P.δ₃ (ℓ - pIn 0) (lor ⟨3, ⟨0, by decide⟩⟩) (lor ⟨3, ⟨1, by decide⟩⟩) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (ℓ - pIn 0)
              (lor (pg kDD 2)) (lor (pc kDD 3 s₀)))) *
        (Dirac.gamma (lor (pg kDD 2)) * QED.OneLoop.electronPropagator P.m P.ε (ℓ + kIn 0) *
          Dirac.gamma (lor (pg kDD 1)) * QED.OneLoop.electronPropagator P.m P.ε ℓ *
          Dirac.gamma (lor (pg kDD 0))) (αOut 0) (βIn 0)) = _)
  · rw [← sum_spinor_chain3 (x₁ := fv kDD 2) (x₂ := fv kDD 1) (x₃ := fv kDD 0)
      (by decide) (by decide) (by decide) (by decide +kernel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [dd_cond, Fin.prod_univ_five, prod_eq_of_two nf (dd_fermionLine_cases s₀ s₁),
      prod_eq_of_three' n1 n2 n3 (dd_photonLine_cases s₀ s₁),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kDD 0 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kDD 1 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kDD 2 = .gauge from rfl),
      hct 3 rfl (Or.inl rfl), hct 4 rfl (Or.inr rfl), t1, t2, t3, t4, t5, m1, m2, m3, m4, m5',
      photonPropagator_neg', ite_and_eq_mul]
    simp only [show (ddF1 s₀ s₁).1 = fv kDD 1 from rfl, show (ddF2 s₀ s₁).1 = fv kDD 2 from rfl,
      show (ddGA s₀ s₁).1 = pg kDD 2 from rfl, show (ddGB s₀ s₁).1 = pc kDD 3 s₀.rev from rfl,
      show (ddGC s₀ s₁).1 = pg kDD 0 from rfl, fv, pg,
      QED.TwoLoop.Insertion.zeroFlavoring, Params.mass, Matrix.cons_val_zero]
    ring
  · have hd : ∀ s₀ s₁, [pg kDD 0, pg kDD 1, pg kDD 2, pc kDD 4 s₁.rev, pc kDD 4 s₁,
        pc kDD 3 s₀.rev, pc kDD 3 s₀].Nodup := by decide +kernel
    have hX : ∀ s₀ s₁ (x : Wick.PhotonSlot kDD), x = pg kDD 0 ∨ x = pg kDD 1 ∨ x = pg kDD 2 ∨
        x = pc kDD 4 s₁.rev ∨ x = pc kDD 4 s₁ ∨ x = pc kDD 3 s₀.rev ∨ x = pc kDD 3 s₀ := by
      decide +kernel
    rw [sum_pi_seven (hd s₀ s₁) (hX s₀ s₁)]
    simp only [photonDD, Finset.mul_sum, Finset.sum_mul]
    fin_cases s₀ <;> fin_cases s₁ <;>
    · simp +decide only [ite_true, ite_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
        Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      try simp only [photonCtFactor_comm P.δ₃ (ℓ - pIn 0) b a,
        photonCtFactor_comm P.δ₃ (ℓ - pIn 0) d c,
        photonPropagator_comm' P.mγ P.Λ P.ε (ℓ - pIn 0) c b]
      ring

end Amplitude

/-! ### The numerator reduction -/

section Reduction

/-- `T g T = k² T` for `T = k² g - k k`, in the form `V g V = -(i/2) δ₃ k² V`. -/
theorem photonCtFactor_metric_photonCtFactor (δ₃ : ℝ) (k : Fin 4 → ℝ) (a d : Fin 4) :
    ∑ b, ∑ c, photonCtFactor δ₃ k a b * ((Minkowski.metric b c : ℝ) : ℂ) * photonCtFactor δ₃ k c d =
      (-(I / 2) * δ₃ * ((Minkowski.dot k k : ℝ) : ℂ)) * photonCtFactor δ₃ k a d := by
  simp only [photonCtFactor, Minkowski.dot, Minkowski.metric, Fin.sum_univ_four]
  fin_cases a <;> fin_cases d <;> simp <;> ring

/-- **The doubly inserted photon line** is `-(δ₃/2) k² d(k)` times the singly inserted one. -/
theorem photonDD_eq (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    photonDD δ₃ mγ Λ ε k ν ρ = (-(δ₃ / 2 : ℂ)) *
      (((Minkowski.dot k k : ℝ) : ℂ) * photonScalar mγ Λ ε k) * photonInsertion δ₃ mγ Λ ε k ν ρ := by
  unfold photonDD photonInsertion
  simp only [photonPropagator_eq_metric_mul]
  set s := photonScalar mγ Λ ε k
  have hin : ∀ a, ∑ b, ∑ c, ∑ d,
      ((Minkowski.metric ν a : ℝ) : ℂ) * s * photonCtFactor δ₃ k a b *
        (((Minkowski.metric b c : ℝ) : ℂ) * s) * photonCtFactor δ₃ k c d *
          (((Minkowski.metric ρ d : ℝ) : ℂ) * s) =
      ∑ d, (((Minkowski.metric ν a : ℝ) : ℂ) * ((Minkowski.metric ρ d : ℝ) : ℂ) * s ^ 3) *
        ∑ b, ∑ c, photonCtFactor δ₃ k a b * ((Minkowski.metric b c : ℝ) : ℂ) *
          photonCtFactor δ₃ k c d := by
    intro a
    simp only [Finset.mul_sum]
    conv_lhs => enter [2, b]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by ring
  simp only [hin, photonCtFactor_metric_photonCtFactor, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  have hI : I * I⁻¹ = 1 := mul_inv_cancel₀ I_ne_zero
  linear_combination (-(1 / 2 : ℂ) * ((Minkowski.metric ν a : ℝ) : ℂ) *
    ((Minkowski.metric ρ d : ℝ) : ℂ) * s ^ 3 * δ₃ * ((Minkowski.dot k k : ℝ) : ℂ) *
      photonCtFactor δ₃ k a d * I⁻¹) * hI

end Reduction

/-! ### The integrand and its integrability -/

section Integrable

variable (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)

/-- The one-loop integrand of `repDD`: the vertex chain with the doubly inserted photon line. -/
noncomputable def ddIntegrand (q : Fin 4 → ℝ) : ℂ :=
  vertexChain P.e (μ 0) (QED.OneLoop.electronPropagator P.m P.ε (pOut 0 + q))
    (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + q))
    (photonDD P.δ₃ P.mγ P.Λ P.ε q) (αOut 0) (βIn 0)

/-- **The value integrand of `repDD s₀ s₁` in the routing `ddMom`** is `ddIntegrand` at
`ℓ - p`. -/
theorem integrand_repDD (s₀ s₁ : Fin 2) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 4 → ℝ) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P (repDD s₀ s₁) pIn kIn (ddMom s₀ s₁ (pIn 0) (kIn 0) ℓ) αOut βIn μ =
      ddIntegrand P pOut pIn αOut βIn μ (ℓ - pIn 0) := by
  have hcyc : ∀ s₀ s₁ x, ∃ i : Fin 4, ((repDD s₀ s₁).1.1 ^ (i : ℕ)) x = .inl 0 := by
    decide +kernel
  rw [regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_of_pow (hcyc s₀ s₁)), dd_amplitude,
    ddIntegrand, vertexChain, hmom, show pIn 0 + kIn 0 + (ℓ - pIn 0) = ℓ + kIn 0 by abel,
    show pIn 0 + (ℓ - pIn 0) = ℓ by abel]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The line kinds of the first piece: the `δ₃` lines and one more `Λ` photon line. -/
def kindsDD₁ : Fin 10 → LineKind := ![.out, .inn, .pho, .pho, .pho, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the first piece. -/
def massesDD₁ (P : Params) : Fin 10 → ℝ :=
  ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.Λ, P.m, P.m, P.m]

/-- The line kinds of the second piece: the `δ₃` lines and one more photon line of each mass. -/
def kindsDD₂ : Fin 11 → LineKind :=
  ![.out, .inn, .pho, .pho, .pho, .pho, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the second piece. -/
def massesDD₂ (P : Params) : Fin 11 → ℝ :=
  ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.m]

/-- The first piece: `numD3` over `D_e' D_e D_γ² D_Λ³`. -/
noncomputable def ddPiece₁ (q : Fin 4 → ℝ) : ℂ :=
  numD3 P (pOut 0) (pIn 0) (μ 0) q (αOut 0) (βIn 0) *
    ((propDenom P.m P.ε (pOut 0 + q))⁻¹ * (propDenom P.m P.ε (pIn 0 + q))⁻¹ *
      ((propDenom P.mγ P.ε q)⁻¹ ^ 2 * (propDenom P.Λ P.ε q)⁻¹ ^ 3))

/-- The second piece: `numD3` over `D_e' D_e D_γ³ D_Λ³`. -/
noncomputable def ddPiece₂ (q : Fin 4 → ℝ) : ℂ :=
  numD3 P (pOut 0) (pIn 0) (μ 0) q (αOut 0) (βIn 0) *
    ((propDenom P.m P.ε (pOut 0 + q))⁻¹ * (propDenom P.m P.ε (pIn 0 + q))⁻¹ *
      ((propDenom P.mγ P.ε q)⁻¹ ^ 3 * (propDenom P.Λ P.ε q)⁻¹ ^ 3))

/-- **The reduction**: the integrand is a combination of the two pieces. -/
theorem ddIntegrand_eq (hε : P.ε ≠ 0) (q : Fin 4 → ℝ) :
    ddIntegrand P pOut pIn αOut βIn μ q =
      (-(P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) * ddPiece₁ P pOut pIn αOut βIn μ q +
        ((P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I)) *
          ddPiece₂ P pOut pIn αOut βIn μ q := by
  have hDγ := propDenom_ne_zero (M := P.mγ) hε q
  have hDΛ := propDenom_ne_zero (M := P.Λ) hε q
  have hdot : ((Minkowski.dot q q : ℝ) : ℂ) =
      propDenom P.mγ P.ε q - (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I) := by
    simp only [propDenom]; push_cast; ring
  have hdiff : propDenom P.Λ P.ε q - propDenom P.mγ P.ε q = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) := by
    simp only [propDenom]; push_cast; ring
  have hscal : photonScalar P.mγ P.Λ P.ε q = (propDenom P.mγ P.ε q)⁻¹ - (propDenom P.Λ P.ε q)⁻¹ :=
    rfl
  have hphoton : photonDD P.δ₃ P.mγ P.Λ P.ε q = fun ν ρ =>
      ((-(P.δ₃ / 2 : ℂ)) * (((Minkowski.dot q q : ℝ) : ℂ) * photonScalar P.mγ P.Λ P.ε q)) *
        photonInsertion P.δ₃ P.mγ P.Λ P.ε q ν ρ := by
    funext ν ρ
    exact photonDD_eq _ _ _ _ _ _ _
  rw [ddIntegrand, hphoton, vertexChain_smul_photon, integrand_d3_eq P hε, smul_smul,
    Matrix.smul_apply, smul_eq_mul, ddPiece₁, ddPiece₂, hscal, hdot, ← hdiff]
  field_simp
  ring

/-- **Both stages of the energy-first integral of the `repDD` integrand** converge, at `ε > 0`. -/
theorem energyFirst_ddIntegrand (hε : 0 < P.ε) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => ddIntegrand P pOut pIn αOut βIn μ (Fin.cons t v)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
        ddIntegrand P pOut pIn αOut βIn μ (Fin.cons t v) := by
  have h₁ := QED.TwoLoop.IntegrableOrderFive.energyFirst_of_kinds (by norm_num) kindsDD₁
    (massesDD₁ P) P.m hε (pIn 0) (pOut 0) (by decide) (by decide) (by decide)
    (fun k => numD3 P (pOut 0) (pIn 0) (μ 0) k (αOut 0) (βIn 0))
    (isLoopPoly_numD3 P _ _ _ _ _) (ddPiece₁ P pOut pIn αOut βIn μ)
    (fun ℓ => by
      simp only [ddPiece₁, Fin.prod_univ_succ, Fin.prod_univ_zero, kindsDD₁, massesDD₁,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  have h₂ := QED.TwoLoop.IntegrableOrderFive.energyFirst_of_kinds (by norm_num) kindsDD₂
    (massesDD₂ P) P.m hε (pIn 0) (pOut 0) (by decide) (by decide) (by decide)
    (fun k => numD3 P (pOut 0) (pIn 0) (μ 0) k (αOut 0) (βIn 0))
    (isLoopPoly_numD3 P _ _ _ _ _) (ddPiece₂ P pOut pIn αOut βIn μ)
    (fun ℓ => by
      simp only [ddPiece₂, Fin.prod_univ_succ, Fin.prod_univ_zero, kindsDD₂, massesDD₂,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  have hsum := ((show EnergyFirstIntegrable (ddPiece₁ P pOut pIn αOut βIn μ) from h₁).const_mul
    (-(P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))).add
    ((show EnergyFirstIntegrable (ddPiece₂ P pOut pIn αOut βIn μ) from h₂).const_mul
      ((P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I)))
  have hfun : ddIntegrand P pOut pIn αOut βIn μ = fun q =>
      (-(P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) * ddPiece₁ P pOut pIn αOut βIn μ q +
        ((P.δ₃ / 2 : ℂ) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) * (((P.mγ ^ 2 : ℝ) : ℂ) - P.ε * I)) *
          ddPiece₂ P pOut pIn αOut βIn μ q :=
    funext (ddIntegrand_eq P pOut pIn αOut βIn μ hε.ne')
  rw [hfun]
  exact hsum

/-- **(T₉′) for the `δ₃`–`δ₃` representatives**: at `ε > 0` and under momentum conservation, the
value integrand of `repDD s₀ s₁` satisfies both stages of the joint energy-first integral, for all
masses, cutoffs and counterterms. -/
theorem chainValueIntegrable_repDD (hε : 0 < P.ε) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) (s₀ s₁ : Fin 2) :
    ChainValueIntegrable P (repDD s₀ s₁) pOut pIn kIn αOut βIn μ := by
  obtain ⟨h₁, h₂⟩ := energyFirst_ddIntegrand P pOut pIn αOut βIn μ hε
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_one_chord P
    (dd_isChord_iff s₀ s₁) (ddMom s₀ s₁ (pIn 0) (kIn 0)) (ddMom_isConserved s₀ s₁ hmom)
    (fun ℓ => (ddMom_apply s₀ s₁ _ _ ℓ).1) αOut βIn μ (ddIntegrand P pOut pIn αOut βIn μ) (pIn 0)
    (integrand_repDD P αOut βIn μ s₀ s₁ hmom) h₁ h₂

end Integrable

end QED.ChainProof.RepsInt

end
