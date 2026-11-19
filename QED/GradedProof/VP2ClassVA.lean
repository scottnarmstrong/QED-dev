/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VAmp

/-!
# The class `VA`: the loop with a self-energy insertion after the second external photon

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2: `classInt2_repVA`.
The representative has the closed electron loop `0 → 1 → 2 → 3 → 0` through the four `gauge`
vertices, the external photons at `0`, `1`, and the internal photon `2 → 3`.

* the lines, their ends, the two chords `3 → 0`, `2 → 3` and a conserved routing with line data
  `baseVA`, `ppVA` (`lineMomentum₂_repVA`);
* the amplitude at the constant flavouring `f` (`va_amplitude`): `(ie)⁴ (1/i)⁵` times the sum over
  the internal photon indices of the photon propagator and the trace of the loop;
* the integrand is the sum over `ρ, σ` of block-summed loop terms (`va_integrand`), integrable by
  `jef_vBlock` under the decidable criteria `critA_VA`, `critB_VA`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Insertion
open QED.TwoLoop.Bridge
open QED.GradedProof.SE2 (k_gggg fv4 ps4 vertexFactor_fv4)
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂ Line FermionLine
  PhotonLine IsChord externalMomentum chordMomentum)
open QED.Integration.TwoLoop (lineMomentum castLoopMatrix IntNoSubdivergenceRefined)

/-- **The chord momenta of a contraction with two chords.** -/
theorem chordMomentum_two {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    {c0 c1 : Line C} (hc : ∀ g, IsChord g ↔ g = c0 ∨ g = c1) (hl : c0.label < c1.label)
    (ℓ : Fin 2 → Fin 4 → ℝ) : chordMomentum ℓ c0 = ℓ 0 ∧ chordMomentum ℓ c1 = ℓ 1 := by
  classical
  have h0 : (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < c0.label).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hgl⟩
    rcases (hc g).mp hg with rfl | rfl
    · exact lt_irrefl _ hgl
    · exact lt_asymm hl hgl
  have h1 : (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < c1.label).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨c0, Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hgl⟩ => ?_, fun h => ?_⟩
    · rcases (hc g).mp hg with rfl | rfl
      · rfl
      · exact absurd hgl (lt_irrefl _)
    · subst h
      exact ⟨(hc _).mpr (Or.inl rfl), hl⟩
  constructor
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by rw [Fin.val_zero]; convert h0)
    · exact absurd (by convert (show 0 < 2 by norm_num) using 2; convert h0) h
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by rw [Fin.val_one]; convert h1)
    · exact absurd (by convert (show 1 < 2 by norm_num) using 2; convert h1) h

/-- The two-loop routing is determined by the chords. -/
theorem lineMomentum₂_eq_of_two {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} {c0 c1 : Line C} (hc : ∀ g, IsChord g ↔ g = c0 ∨ g = c1)
    (hl : c0.label < c1.label) {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (ℓ : Fin 2 → Fin 4 → ℝ) (mom : Line C → Fin 4 → ℝ)
    (hcons : IsConserved C pOut pIn kIn mom) (h0 : mom c0 = ℓ 0) (h1 : mom c1 = ℓ 1) :
    lineMomentum₂ C pOut pIn kIn ℓ = mom := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved hcons (fun g hg => ?_) f).symm
  obtain ⟨e0, e1⟩ := chordMomentum_two hc hl ℓ
  rcases (hc g).mp hg with rfl | rfl
  · rw [e0, h0]
  · rw [e1, h1]

section VA

/-- The electron line `3 → 0`. -/
def va0 : FermionLine repVA := ⟨fvK k_gggg 0, by decide +kernel⟩
/-- The electron line `0 → 1`. -/
def va1 : FermionLine repVA := ⟨fvK k_gggg 1, by decide +kernel⟩
/-- The electron line `1 → 2`. -/
def va2 : FermionLine repVA := ⟨fvK k_gggg 2, by decide +kernel⟩
/-- The electron line `2 → 3`. -/
def va3 : FermionLine repVA := ⟨fvK k_gggg 3, by decide +kernel⟩
/-- The photon line `2 → 3`. -/
def gA : PhotonLine repVA := ⟨psK k_gggg 2 0, by decide +kernel⟩

theorem va_fermionLine_cases :
    ∀ f : FermionLine repVA, f = va0 ∨ f = va1 ∨ f = va2 ∨ f = va3 := by
  decide +kernel

theorem va_photonLine_cases : ∀ g : PhotonLine repVA, g = gA := by decide +kernel

theorem va_isChord_iff : ∀ g : Line repVA, IsChord g ↔ g = .inl va0 ∨ g = .inl va3 := by
  decide +kernel

theorem va_label : (Line.label (.inl va0 : Line repVA)) < (Line.label (.inl va3 : Line repVA)) := by
  decide +kernel

theorem va_ends : (Line.ends (.inl va0 : Line repVA)) = (3, 0) ∧
    (Line.ends (.inl va1 : Line repVA)) = (0, 1) ∧ (Line.ends (.inl va2 : Line repVA)) = (1, 2) ∧
    (Line.ends (.inl va3 : Line repVA)) = (2, 3) ∧ (Line.ends (.inr gA : Line repVA)) = (2, 3) := by
  decide +kernel

theorem va_tails : va0.tail = fv4 3 ∧ va1.tail = fv4 0 ∧ va2.tail = fv4 1 ∧ va3.tail = fv4 2 ∧
    gA.head = ps4 3 := by
  decide +kernel

theorem va_ext (v : Fin 4) :
    ((∃ a : Wick.PhotonSlot k_gggg, a.1 = v ∧ repVA.1.2 (.inl 0) = .inr a) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_gggg, a.1 = v ∧ repVA.1.2 (.inl 1) = .inr a) ↔ v = 1) := by
  revert v
  decide +kernel

/-- The rows of the line momenta of `VA`, in the order of the trace (`va0`, `va3`, `va2`, `va1`)
and then the photon: `ℓ₀`, `ℓ₁`, `ℓ₀`, `ℓ₀ + k`, `ℓ₀ - ℓ₁`. -/
def baseVA : Fin 5 → Fin 2 → ℤ := ![![1, 0], ![0, 1], ![1, 0], ![1, 0], ![1, -1]]

/-- The shifts of the line momenta of `VA`. -/
def ppVA (k : Fin 4 → ℝ) : Fin 5 → Fin 4 → ℝ := ![0, 0, 0, k, 0]

/-- The row of each line of `VA`. -/
def idxVA (f : Line repVA) : Fin 5 :=
  if f = .inl va0 then 0 else if f = .inl va3 then 1 else if f = .inl va2 then 2 else
    if f = .inl va1 then 3 else 4

theorem idxVA_apply : idxVA (.inl va0) = 0 ∧ idxVA (.inl va1) = 3 ∧ idxVA (.inl va2) = 2 ∧
    idxVA (.inl va3) = 1 ∧ idxVA (.inr gA) = 4 := by
  decide +kernel

/-- The routing of `VA`. -/
def vaMom (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repVA) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix baseVA) (ppVA k) (idxVA f) ℓ

theorem vaMom_fm (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vaMom k ℓ (.inl va0) = fm baseVA (ppVA k) 0 ℓ ∧ vaMom k ℓ (.inl va3) = fm baseVA (ppVA k) 1 ℓ ∧
      vaMom k ℓ (.inl va2) = fm baseVA (ppVA k) 2 ℓ ∧
      vaMom k ℓ (.inl va1) = fm baseVA (ppVA k) 3 ℓ ∧
      vaMom k ℓ (.inr gA) = phm baseVA (ppVA k) ℓ := by
  obtain ⟨i0, i1, i2, i3, i4⟩ := idxVA_apply
  simp only [vaMom, i0, i1, i2, i3, i4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem vaMom_apply (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vaMom k ℓ (.inl va0) = ℓ 0 ∧ vaMom k ℓ (.inl va1) = ℓ 0 + k ∧ vaMom k ℓ (.inl va2) = ℓ 0 ∧
      vaMom k ℓ (.inl va3) = ℓ 1 ∧ vaMom k ℓ (.inr gA) = ℓ 0 - ℓ 1 := by
  obtain ⟨i0, i1, i2, i3, i4⟩ := idxVA_apply
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [vaMom, i0, i1, i2, i3, i4, lineMomentum, castLoopMatrix, baseVA, ppVA,
      Fin.sum_univ_two]
  ring

theorem va_isConserved (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved repVA ![] ![] ![k, -k] (vaMom k ℓ) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := va_ends
  obtain ⟨m0, m1, m2, m3, m4⟩ := vaMom_apply k ℓ
  intro v
  rw [inflow, Fintype.sum_sum_type, sum_eq_of_four (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) va_fermionLine_cases, sum_eq_of_one va_photonLine_cases,
    externalMomentum_zero_two]
  obtain ⟨x1, x2⟩ := va_ext v
  simp only [e0, e1, e2, e3, e4, x1, x2, m0, m1, m2, m3, m4, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  funext μ
  fin_cases v <;> simp
  ring

theorem lineMomentum₂_repVA (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ repVA ![] ![] ![k, -k] ℓ = vaMom k ℓ :=
  lineMomentum₂_eq_of_two va_isChord_iff va_label ℓ _ (va_isConserved k ℓ)
    (vaMom_apply k ℓ).1 (vaMom_apply k ℓ).2.2.2.1

theorem va_cond (α β : Wick.FermionVertex k_gggg → Fin 4) (lor : Wick.PhotonSlot k_gggg → Fin 4)
    (μ ν : Fin 4) :
    ((∀ (i : Fin 0) t, repVA.1.1 (.inl i) = .inr t → α t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ t (i : Fin 0), repVA.1.1 (.inr t) = .inl i → β t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ j a, repVA.1.2 (.inl j) = .inr a → lor a = ![μ, ν] j)) ↔
      (lor (ps4 0) = μ ∧ lor (ps4 1) = ν) := by
  have h0 : ∀ a, repVA.1.2 (.inl 0) = .inr a ↔ a = ps4 0 := by decide +kernel
  have h1 : ∀ a, repVA.1.2 (.inl 1) = .inr a ↔ a = ps4 1 := by decide +kernel
  simp only [Fin.forall_fin_two, h0, h1, forall_eq, IsEmpty.forall_iff, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, implies_true]

/-- **The amplitude of `repVA`** at the constant flavouring `f`, grading `0`. -/
theorem va_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
    (kIn : Fin 2 → Fin 4 → ℝ) (kk : Line repVA → Fin 4 → ℝ) (μ ν : Fin 4) :
    contractionAmplitude P Φ D repVA (fun _ => f) 0 ![] kIn kk ![] ![] ![μ, ν] =
      (I * P.e) ^ 4 * (1 / I) ^ 5 * ∑ ρ : Fin 4, ∑ σ : Fin 4,
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gA)) ρ σ *
          Matrix.trace (Dirac.gamma μ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va0)) * Dirac.gamma σ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va3)) * Dirac.gamma ρ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va2)) * Dirac.gamma ν *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va1))) := by
  obtain ⟨t0, t1, t2, t3, h3⟩ := va_tails
  unfold contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex k_gggg → Fin 4, ∑ β : Wick.FermionVertex k_gggg → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gggg → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [va_cond, Fin.prod_univ_four,
    prod_eq_of_four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      va_fermionLine_cases,
    prod_eq_of_one va_photonLine_cases, t0, t1, t2, t3, h3, vertexFactor_fv4,
    show va0.1 = fv4 0 from rfl, show va1.1 = fv4 1 from rfl, show va2.1 = fv4 2 from rfl,
    show va3.1 = fv4 3 from rfl, show gA.1 = ps4 2 from rfl]
  have hterm : ∀ (lor : Wick.PhotonSlot k_gggg → Fin 4)
      (α β : Wick.FermionVertex k_gggg → Fin 4),
      (if lor (ps4 0) = μ ∧ lor (ps4 1) = ν then (1 : ℂ) else 0) *
        (I * P.e * Dirac.gamma (lor (ps4 0)) (α (fv4 0)) (β (fv4 0)) *
          (I * P.e * Dirac.gamma (lor (ps4 1)) (α (fv4 1)) (β (fv4 1))) *
          (I * P.e * Dirac.gamma (lor (ps4 2)) (α (fv4 2)) (β (fv4 2))) *
          (I * P.e * Dirac.gamma (lor (ps4 3)) (α (fv4 3)) (β (fv4 3))) *
          (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va0)) (β (fv4 0))
              (α (fv4 3)) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va1)) (β (fv4 1))
              (α (fv4 0))) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va2)) (β (fv4 2))
              (α (fv4 1))) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va3)) (β (fv4 3))
              (α (fv4 2)))) *
          (1 / I * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gA)) (lor (ps4 2))
            (lor (ps4 3)))) =
      (if lor (ps4 0) = μ ∧ lor (ps4 1) = ν then (1 : ℂ) else 0) *
        ((I * P.e) ^ 4 * (1 / I) ^ 5 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gA)) (lor (ps4 2)) (lor (ps4 3))) *
        (Dirac.gamma (lor (ps4 0)) (α (fv4 0)) (β (fv4 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va0)) (β (fv4 0)) (α (fv4 3)) *
          Dirac.gamma (lor (ps4 3)) (α (fv4 3)) (β (fv4 3)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va3)) (β (fv4 3)) (α (fv4 2)) *
          Dirac.gamma (lor (ps4 2)) (α (fv4 2)) (β (fv4 2)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va2)) (β (fv4 2)) (α (fv4 1)) *
          Dirac.gamma (lor (ps4 1)) (α (fv4 1)) (β (fv4 1)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va1)) (β (fv4 1))
            (α (fv4 0))) := by
    intro lor α β
    ring
  refine (Finset.sum_congr rfl fun lor _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => hterm lor α β).trans ?_
  simp only [← Finset.mul_sum]
  simp only [sum_spinor_loop4 (x₁ := fv4 0) (x₂ := fv4 3) (x₃ := fv4 2) (x₄ := fv4 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)]
  refine (Finset.sum_congr rfl fun lor _ => mul_assoc _ _ _).trans ?_
  refine (sum_lor_ps4_1 μ ν (fun a b c d => (I * P.e) ^ 4 * (1 / I) ^ 5 *
    QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gA)) c d *
    Matrix.trace (Dirac.gamma a * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va0)) *
      Dirac.gamma d * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va3)) *
      Dirac.gamma c * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va2)) *
      Dirac.gamma b * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl va1))))).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem oneLoop_repVA : OneLoop repVA := by
  intro t s
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 4) (by norm_num) (by decide +kernel)]
  revert t s
  decide +kernel

/-- The vertex matrices of `VA` in the order of the trace. -/
noncomputable def aVA (μ ν ρ σ : Fin 4) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![Dirac.gamma μ, Dirac.gamma σ, Dirac.gamma ρ, Dirac.gamma ν]

theorem isOddG_aVA (μ ν ρ σ : Fin 4) : ∀ l, IsOddG (aVA μ ν ρ σ l) := by
  intro l
  fin_cases l <;> exact isOddG_gamma _

/-- **The integrand of `repVA`** in its routing: a sum over the internal photon indices of
flavour sums of loop terms. -/
theorem va_integrand (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (hε : P.ε ≠ 0) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D repVA 0 ![] ![k, -k] (vaMom k ℓ) ![] ![] ![μ, ν] =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ f, (Φ.coeff f : ℂ) *
        (kV P.e P.mγ P.Λ ρ σ * vD baseVA (ppVA k) P.mγ P.Λ P.ε ℓ *
          vH baseVA (ppVA k) (aVA μ ν ρ σ) P.ε (Φ.mass f) ℓ) := by
  obtain ⟨m0, m3, m2, m1, m4⟩ := vaMom_fm k ℓ
  have e : ∀ g : Fin 4 → Fin 4 → F → ℂ,
      ∑ ρ, ∑ σ, ∑ f, g ρ σ f = ∑ f, ∑ ρ, ∑ σ, g ρ σ f := fun g =>
    (Finset.sum_congr rfl fun ρ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [regulatedAmplitude_of_oneLoop Φ P D oneLoop_repVA (fv4 0), Finset.mul_sum, e]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [va_amplitude, m0, m1, m2, m3, m4]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  have h := v_term_eq baseVA (ppVA k) P.e P.mγ P.Λ (Φ.mass f) hε (aVA μ ν ρ σ) ρ σ ℓ
  have a0 : aVA μ ν ρ σ 0 = Dirac.gamma μ := rfl
  have a1 : aVA μ ν ρ σ 1 = Dirac.gamma σ := rfl
  have a2 : aVA μ ν ρ σ 2 = Dirac.gamma ρ := rfl
  have a3 : aVA μ ν ρ σ 3 = Dirac.gamma ν := rfl
  rw [a0, a1, a2, a3] at h
  rw [← h]
  ring

theorem critA_VA :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => baseVA (shA i j n) := by
  decide

theorem critB_VA :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVA (shB i n) := by
  decide

/-- **The class obligation for `VA`.** -/
theorem classInt2_repVA : ClassInt2 repVA := by
  intro P F _ _ Φ D rep m₀ hH ε hε k μ ν
  rw [loopCount_repVA]
  refine JEF.congr (JEF.sum Finset.univ fun ρ _ => JEF.sum Finset.univ fun σ _ =>
    jef_vBlock baseVA (ppVA k) (isOddG_aVA μ ν ρ σ) critA_VA critB_VA Φ rep m₀ hH.hm₀ hH.hmass
      hH.hrep hH.hPV₁ hH.hPV₂ (kV P.e P.mγ P.Λ ρ σ) P.mγ P.Λ hε) fun ℓ => ?_
  rw [lineMomentum₂_repVA, va_integrand { P with ε := ε } Φ D hε.ne' k ℓ μ ν]

end VA

end QED.GradedProof.VP2

end
