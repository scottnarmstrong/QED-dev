/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2ClassVA

/-!
# The class `VB`: the vertex-correction loop

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2: `classInt2_repVB`.
The representative has the closed electron loop `0 → 1 → 2 → 3 → 0` through the four `gauge`
vertices, the external photons at `0`, `2`, and the internal photon `1 → 3`. As for `VA`
(`QED/GradedProof/VP2ClassVA.lean`): lines, chords `3 → 0`, `1 → 2`, a conserved routing with line
data `baseVB`, `ppVB`, the amplitude at a constant flavouring, the integrand as a sum over the
internal photon indices of block-summed loop terms, and `jef_vBlock` under the decidable criteria
`critA_VB`, `critB_VB`.
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

section VB

/-- The electron line `3 → 0`. -/
def vb0 : FermionLine repVB := ⟨fvK k_gggg 0, by decide +kernel⟩
/-- The electron line `0 → 1`. -/
def vb1 : FermionLine repVB := ⟨fvK k_gggg 1, by decide +kernel⟩
/-- The electron line `1 → 2`. -/
def vb2 : FermionLine repVB := ⟨fvK k_gggg 2, by decide +kernel⟩
/-- The electron line `2 → 3`. -/
def vb3 : FermionLine repVB := ⟨fvK k_gggg 3, by decide +kernel⟩
/-- The photon line `1 → 3`. -/
def gB : PhotonLine repVB := ⟨psK k_gggg 1 0, by decide +kernel⟩

theorem vb_fermionLine_cases :
    ∀ f : FermionLine repVB, f = vb0 ∨ f = vb1 ∨ f = vb2 ∨ f = vb3 := by
  decide +kernel

theorem vb_photonLine_cases : ∀ g : PhotonLine repVB, g = gB := by decide +kernel

theorem vb_isChord_iff : ∀ g : Line repVB, IsChord g ↔ g = .inl vb0 ∨ g = .inl vb2 := by
  decide +kernel

theorem vb_label : (Line.label (.inl vb0 : Line repVB)) < (Line.label (.inl vb2 : Line repVB)) := by
  decide +kernel

theorem vb_ends : (Line.ends (.inl vb0 : Line repVB)) = (3, 0) ∧
    (Line.ends (.inl vb1 : Line repVB)) = (0, 1) ∧ (Line.ends (.inl vb2 : Line repVB)) = (1, 2) ∧
    (Line.ends (.inl vb3 : Line repVB)) = (2, 3) ∧ (Line.ends (.inr gB : Line repVB)) = (1, 3) := by
  decide +kernel

theorem vb_tails : vb0.tail = fv4 3 ∧ vb1.tail = fv4 0 ∧ vb2.tail = fv4 1 ∧ vb3.tail = fv4 2 ∧
    gB.head = ps4 3 := by
  decide +kernel

theorem vb_ext (v : Fin 4) :
    ((∃ a : Wick.PhotonSlot k_gggg, a.1 = v ∧ repVB.1.2 (.inl 0) = .inr a) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_gggg, a.1 = v ∧ repVB.1.2 (.inl 1) = .inr a) ↔ v = 2) := by
  revert v
  decide +kernel

/-- The rows of the line momenta of `VB`, in the order of the trace (`vb0`, `vb3`, `vb2`, `vb1`)
and then the photon: `ℓ₀`, `ℓ₁ - k`, `ℓ₁`, `ℓ₀ + k`, `ℓ₀ - ℓ₁ + k`. -/
def baseVB : Fin 5 → Fin 2 → ℤ := ![![1, 0], ![0, 1], ![0, 1], ![1, 0], ![1, -1]]

/-- The shifts of the line momenta of `VB`. -/
def ppVB (k : Fin 4 → ℝ) : Fin 5 → Fin 4 → ℝ := ![0, -k, 0, k, k]

/-- The row of each line of `VB`. -/
def idxVB (f : Line repVB) : Fin 5 :=
  if f = .inl vb0 then 0 else if f = .inl vb3 then 1 else if f = .inl vb2 then 2 else
    if f = .inl vb1 then 3 else 4

theorem idxVB_apply : idxVB (.inl vb0) = 0 ∧ idxVB (.inl vb1) = 3 ∧ idxVB (.inl vb2) = 2 ∧
    idxVB (.inl vb3) = 1 ∧ idxVB (.inr gB) = 4 := by
  decide +kernel

/-- The routing of `VB`. -/
def vbMom (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repVB) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix baseVB) (ppVB k) (idxVB f) ℓ

theorem vbMom_fm (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vbMom k ℓ (.inl vb0) = fm baseVB (ppVB k) 0 ℓ ∧ vbMom k ℓ (.inl vb3) = fm baseVB (ppVB k) 1 ℓ ∧
      vbMom k ℓ (.inl vb2) = fm baseVB (ppVB k) 2 ℓ ∧
      vbMom k ℓ (.inl vb1) = fm baseVB (ppVB k) 3 ℓ ∧
      vbMom k ℓ (.inr gB) = phm baseVB (ppVB k) ℓ := by
  obtain ⟨i0, i1, i2, i3, i4⟩ := idxVB_apply
  simp only [vbMom, i0, i1, i2, i3, i4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem vbMom_apply (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vbMom k ℓ (.inl vb0) = ℓ 0 ∧ vbMom k ℓ (.inl vb1) = ℓ 0 + k ∧ vbMom k ℓ (.inl vb2) = ℓ 1 ∧
      vbMom k ℓ (.inl vb3) = ℓ 1 - k ∧ vbMom k ℓ (.inr gB) = ℓ 0 - ℓ 1 + k := by
  obtain ⟨i0, i1, i2, i3, i4⟩ := idxVB_apply
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [vbMom, i0, i1, i2, i3, i4, lineMomentum, castLoopMatrix, baseVB, ppVB,
      Fin.sum_univ_two]
  all_goals ring

theorem vb_isConserved (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved repVB ![] ![] ![k, -k] (vbMom k ℓ) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := vb_ends
  obtain ⟨m0, m1, m2, m3, m4⟩ := vbMom_apply k ℓ
  intro v
  rw [inflow, Fintype.sum_sum_type, sum_eq_of_four (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) vb_fermionLine_cases, sum_eq_of_one vb_photonLine_cases,
    externalMomentum_zero_two]
  obtain ⟨x1, x2⟩ := vb_ext v
  simp only [e0, e1, e2, e3, e4, x1, x2, m0, m1, m2, m3, m4, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  funext μ
  fin_cases v <;> simp
  all_goals ring

theorem lineMomentum₂_repVB (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ repVB ![] ![] ![k, -k] ℓ = vbMom k ℓ :=
  lineMomentum₂_eq_of_two vb_isChord_iff vb_label ℓ _ (vb_isConserved k ℓ)
    (vbMom_apply k ℓ).1 (vbMom_apply k ℓ).2.2.1

theorem vb_cond (α β : Wick.FermionVertex k_gggg → Fin 4) (lor : Wick.PhotonSlot k_gggg → Fin 4)
    (μ ν : Fin 4) :
    ((∀ (i : Fin 0) t, repVB.1.1 (.inl i) = .inr t → α t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ t (i : Fin 0), repVB.1.1 (.inr t) = .inl i → β t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ j a, repVB.1.2 (.inl j) = .inr a → lor a = ![μ, ν] j)) ↔
      (lor (ps4 0) = μ ∧ lor (ps4 2) = ν) := by
  have h0 : ∀ a, repVB.1.2 (.inl 0) = .inr a ↔ a = ps4 0 := by decide +kernel
  have h1 : ∀ a, repVB.1.2 (.inl 1) = .inr a ↔ a = ps4 2 := by decide +kernel
  simp only [Fin.forall_fin_two, h0, h1, forall_eq, IsEmpty.forall_iff, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, implies_true]

/-- **The amplitude of `repVB`** at the constant flavouring `f`, grading `0`. -/
theorem vb_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
    (kIn : Fin 2 → Fin 4 → ℝ) (kk : Line repVB → Fin 4 → ℝ) (μ ν : Fin 4) :
    contractionAmplitude P Φ D repVB (fun _ => f) 0 ![] kIn kk ![] ![] ![μ, ν] =
      (I * P.e) ^ 4 * (1 / I) ^ 5 * ∑ ρ : Fin 4, ∑ σ : Fin 4,
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gB)) ρ σ *
          Matrix.trace (Dirac.gamma μ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb0)) * Dirac.gamma σ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb3)) * Dirac.gamma ν *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb2)) * Dirac.gamma ρ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb1))) := by
  obtain ⟨t0, t1, t2, t3, h3⟩ := vb_tails
  unfold contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex k_gggg → Fin 4, ∑ β : Wick.FermionVertex k_gggg → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gggg → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [vb_cond, Fin.prod_univ_four,
    prod_eq_of_four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      vb_fermionLine_cases,
    prod_eq_of_one vb_photonLine_cases, t0, t1, t2, t3, h3, vertexFactor_fv4,
    show vb0.1 = fv4 0 from rfl, show vb1.1 = fv4 1 from rfl, show vb2.1 = fv4 2 from rfl,
    show vb3.1 = fv4 3 from rfl, show gB.1 = ps4 1 from rfl]
  have hterm : ∀ (lor : Wick.PhotonSlot k_gggg → Fin 4)
      (α β : Wick.FermionVertex k_gggg → Fin 4),
      (if lor (ps4 0) = μ ∧ lor (ps4 2) = ν then (1 : ℂ) else 0) *
        (I * P.e * Dirac.gamma (lor (ps4 0)) (α (fv4 0)) (β (fv4 0)) *
          (I * P.e * Dirac.gamma (lor (ps4 1)) (α (fv4 1)) (β (fv4 1))) *
          (I * P.e * Dirac.gamma (lor (ps4 2)) (α (fv4 2)) (β (fv4 2))) *
          (I * P.e * Dirac.gamma (lor (ps4 3)) (α (fv4 3)) (β (fv4 3))) *
          (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb0)) (β (fv4 0))
              (α (fv4 3)) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb1)) (β (fv4 1))
              (α (fv4 0))) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb2)) (β (fv4 2))
              (α (fv4 1))) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb3)) (β (fv4 3))
              (α (fv4 2)))) *
          (1 / I * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gB)) (lor (ps4 1))
            (lor (ps4 3)))) =
      (if lor (ps4 0) = μ ∧ lor (ps4 2) = ν then (1 : ℂ) else 0) *
        ((I * P.e) ^ 4 * (1 / I) ^ 5 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gB)) (lor (ps4 1)) (lor (ps4 3))) *
        (Dirac.gamma (lor (ps4 0)) (α (fv4 0)) (β (fv4 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb0)) (β (fv4 0)) (α (fv4 3)) *
          Dirac.gamma (lor (ps4 3)) (α (fv4 3)) (β (fv4 3)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb3)) (β (fv4 3)) (α (fv4 2)) *
          Dirac.gamma (lor (ps4 2)) (α (fv4 2)) (β (fv4 2)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb2)) (β (fv4 2)) (α (fv4 1)) *
          Dirac.gamma (lor (ps4 1)) (α (fv4 1)) (β (fv4 1)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb1)) (β (fv4 1))
            (α (fv4 0))) := by
    intro lor α β
    ring
  refine (Finset.sum_congr rfl fun lor _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => hterm lor α β).trans ?_
  simp only [← Finset.mul_sum]
  simp only [sum_spinor_loop4 (x₁ := fv4 0) (x₂ := fv4 3) (x₃ := fv4 2) (x₄ := fv4 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)]
  refine (Finset.sum_congr rfl fun lor _ => mul_assoc _ _ _).trans ?_
  refine (sum_lor_ps4_2 μ ν (fun a b c d => (I * P.e) ^ 4 * (1 / I) ^ 5 *
    QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gB)) b d *
    Matrix.trace (Dirac.gamma a * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb0)) *
      Dirac.gamma d * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb3)) *
      Dirac.gamma c * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb2)) *
      Dirac.gamma b * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vb1))))).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem oneLoop_repVB : OneLoop repVB := by
  intro t s
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 4) (by norm_num) (by decide +kernel)]
  revert t s
  decide +kernel

/-- The vertex matrices of `VB` in the order of the trace. -/
noncomputable def aVB (μ ν ρ σ : Fin 4) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![Dirac.gamma μ, Dirac.gamma σ, Dirac.gamma ν, Dirac.gamma ρ]

theorem isOddG_aVB (μ ν ρ σ : Fin 4) : ∀ l, IsOddG (aVB μ ν ρ σ l) := by
  intro l
  fin_cases l <;> exact isOddG_gamma _

/-- **The integrand of `repVB`** in its routing: a sum over the internal photon indices of
flavour sums of loop terms. -/
theorem vb_integrand (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (hε : P.ε ≠ 0) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D repVB 0 ![] ![k, -k] (vbMom k ℓ) ![] ![] ![μ, ν] =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ f, (Φ.coeff f : ℂ) *
        (kV P.e P.mγ P.Λ ρ σ * vD baseVB (ppVB k) P.mγ P.Λ P.ε ℓ *
          vH baseVB (ppVB k) (aVB μ ν ρ σ) P.ε (Φ.mass f) ℓ) := by
  obtain ⟨m0, m3, m2, m1, m4⟩ := vbMom_fm k ℓ
  have e : ∀ g : Fin 4 → Fin 4 → F → ℂ,
      ∑ ρ, ∑ σ, ∑ f, g ρ σ f = ∑ f, ∑ ρ, ∑ σ, g ρ σ f := fun g =>
    (Finset.sum_congr rfl fun ρ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [regulatedAmplitude_of_oneLoop Φ P D oneLoop_repVB (fv4 0), Finset.mul_sum, e]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [vb_amplitude, m0, m1, m2, m3, m4]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  have h := v_term_eq baseVB (ppVB k) P.e P.mγ P.Λ (Φ.mass f) hε (aVB μ ν ρ σ) ρ σ ℓ
  have a0 : aVB μ ν ρ σ 0 = Dirac.gamma μ := rfl
  have a1 : aVB μ ν ρ σ 1 = Dirac.gamma σ := rfl
  have a2 : aVB μ ν ρ σ 2 = Dirac.gamma ν := rfl
  have a3 : aVB μ ν ρ σ 3 = Dirac.gamma ρ := rfl
  rw [a0, a1, a2, a3] at h
  rw [← h]
  ring

theorem critA_VB :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => baseVB (shA i j n) := by
  decide

theorem critB_VB :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVB (shB i n) := by
  decide

/-- **The class obligation for `VB`.** -/
theorem classInt2_repVB : ClassInt2 repVB := by
  intro P F _ _ Φ D rep m₀ hH ε hε k μ ν
  rw [loopCount_repVB]
  refine JEF.congr (JEF.sum Finset.univ fun ρ _ => JEF.sum Finset.univ fun σ _ =>
    jef_vBlock baseVB (ppVB k) (isOddG_aVB μ ν ρ σ) critA_VB critB_VB Φ rep m₀ hH.hm₀ hH.hmass
      hH.hrep hH.hPV₁ hH.hPV₂ (kV P.e P.mγ P.Λ ρ σ) P.mγ P.Λ hε) fun ℓ => ?_
  rw [lineMomentum₂_repVB, vb_integrand { P with ε := ε } Φ D hε.ne' k ℓ μ ν]

end VB

end QED.GradedProof.VP2

end
