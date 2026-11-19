/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2ClassVA

/-!
# The class `VC`: the loop with a self-energy insertion before the second external photon

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2: `classInt2_repVC`.
The representative has the closed electron loop `0 → 1 → 2 → 3 → 0` through the four `gauge`
vertices, the external photons at `0`, `3`, and the internal photon `1 → 2`. As for `VA`
(`QED/GradedProof/VP2ClassVA.lean`): lines, chords `3 → 0`, `1 → 2`, a conserved routing with line
data `baseVC`, `ppVC`, the amplitude at a constant flavouring, the integrand as a sum over the
internal photon indices of block-summed loop terms, and `jef_vBlock` under the decidable criteria
`critA_VC`, `critB_VC`.
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

section VC

/-- The electron line `3 → 0`. -/
def vc0 : FermionLine repVC := ⟨fvK k_gggg 0, by decide +kernel⟩
/-- The electron line `0 → 1`. -/
def vc1 : FermionLine repVC := ⟨fvK k_gggg 1, by decide +kernel⟩
/-- The electron line `1 → 2`. -/
def vc2 : FermionLine repVC := ⟨fvK k_gggg 2, by decide +kernel⟩
/-- The electron line `2 → 3`. -/
def vc3 : FermionLine repVC := ⟨fvK k_gggg 3, by decide +kernel⟩
/-- The photon line `1 → 2`. -/
def gC : PhotonLine repVC := ⟨psK k_gggg 1 0, by decide +kernel⟩

theorem vc_fermionLine_cases :
    ∀ f : FermionLine repVC, f = vc0 ∨ f = vc1 ∨ f = vc2 ∨ f = vc3 := by
  decide +kernel

theorem vc_photonLine_cases : ∀ g : PhotonLine repVC, g = gC := by decide +kernel

theorem vc_isChord_iff : ∀ g : Line repVC, IsChord g ↔ g = .inl vc0 ∨ g = .inl vc2 := by
  decide +kernel

theorem vc_label : (Line.label (.inl vc0 : Line repVC)) < (Line.label (.inl vc2 : Line repVC)) := by
  decide +kernel

theorem vc_ends : (Line.ends (.inl vc0 : Line repVC)) = (3, 0) ∧
    (Line.ends (.inl vc1 : Line repVC)) = (0, 1) ∧ (Line.ends (.inl vc2 : Line repVC)) = (1, 2) ∧
    (Line.ends (.inl vc3 : Line repVC)) = (2, 3) ∧ (Line.ends (.inr gC : Line repVC)) = (1, 2) := by
  decide +kernel

theorem vc_tails : vc0.tail = fv4 3 ∧ vc1.tail = fv4 0 ∧ vc2.tail = fv4 1 ∧ vc3.tail = fv4 2 ∧
    gC.head = ps4 2 := by
  decide +kernel

theorem vc_ext (v : Fin 4) :
    ((∃ a : Wick.PhotonSlot k_gggg, a.1 = v ∧ repVC.1.2 (.inl 0) = .inr a) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot k_gggg, a.1 = v ∧ repVC.1.2 (.inl 1) = .inr a) ↔ v = 3) := by
  revert v
  decide +kernel

/-- The rows of the line momenta of `VC`, in the order of the trace (`vc0`, `vc3`, `vc2`, `vc1`)
and then the photon: `ℓ₀`, `ℓ₀ + k`, `ℓ₁`, `ℓ₀ + k`, `ℓ₀ - ℓ₁ + k`. -/
def baseVC : Fin 5 → Fin 2 → ℤ := ![![1, 0], ![1, 0], ![0, 1], ![1, 0], ![1, -1]]

/-- The shifts of the line momenta of `VC`. -/
def ppVC (k : Fin 4 → ℝ) : Fin 5 → Fin 4 → ℝ := ![0, k, 0, k, k]

/-- The row of each line of `VC`. -/
def idxVC (f : Line repVC) : Fin 5 :=
  if f = .inl vc0 then 0 else if f = .inl vc3 then 1 else if f = .inl vc2 then 2 else
    if f = .inl vc1 then 3 else 4

theorem idxVC_apply : idxVC (.inl vc0) = 0 ∧ idxVC (.inl vc1) = 3 ∧ idxVC (.inl vc2) = 2 ∧
    idxVC (.inl vc3) = 1 ∧ idxVC (.inr gC) = 4 := by
  decide +kernel

/-- The routing of `VC`. -/
def vcMom (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line repVC) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix baseVC) (ppVC k) (idxVC f) ℓ

theorem vcMom_fm (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vcMom k ℓ (.inl vc0) = fm baseVC (ppVC k) 0 ℓ ∧ vcMom k ℓ (.inl vc3) = fm baseVC (ppVC k) 1 ℓ ∧
      vcMom k ℓ (.inl vc2) = fm baseVC (ppVC k) 2 ℓ ∧
      vcMom k ℓ (.inl vc1) = fm baseVC (ppVC k) 3 ℓ ∧
      vcMom k ℓ (.inr gC) = phm baseVC (ppVC k) ℓ := by
  obtain ⟨i0, i1, i2, i3, i4⟩ := idxVC_apply
  simp only [vcMom, i0, i1, i2, i3, i4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem vcMom_apply (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vcMom k ℓ (.inl vc0) = ℓ 0 ∧ vcMom k ℓ (.inl vc1) = ℓ 0 + k ∧ vcMom k ℓ (.inl vc2) = ℓ 1 ∧
      vcMom k ℓ (.inl vc3) = ℓ 0 + k ∧ vcMom k ℓ (.inr gC) = ℓ 0 - ℓ 1 + k := by
  obtain ⟨i0, i1, i2, i3, i4⟩ := idxVC_apply
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [vcMom, i0, i1, i2, i3, i4, lineMomentum, castLoopMatrix, baseVC, ppVC,
      Fin.sum_univ_two]
  all_goals ring

theorem vc_isConserved (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved repVC ![] ![] ![k, -k] (vcMom k ℓ) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := vc_ends
  obtain ⟨m0, m1, m2, m3, m4⟩ := vcMom_apply k ℓ
  intro v
  rw [inflow, Fintype.sum_sum_type, sum_eq_of_four (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) vc_fermionLine_cases, sum_eq_of_one vc_photonLine_cases,
    externalMomentum_zero_two]
  obtain ⟨x1, x2⟩ := vc_ext v
  simp only [e0, e1, e2, e3, e4, x1, x2, m0, m1, m2, m3, m4, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  funext μ
  fin_cases v <;> simp
  all_goals ring

theorem lineMomentum₂_repVC (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ repVC ![] ![] ![k, -k] ℓ = vcMom k ℓ :=
  lineMomentum₂_eq_of_two vc_isChord_iff vc_label ℓ _ (vc_isConserved k ℓ)
    (vcMom_apply k ℓ).1 (vcMom_apply k ℓ).2.2.1

theorem vc_cond (α β : Wick.FermionVertex k_gggg → Fin 4) (lor : Wick.PhotonSlot k_gggg → Fin 4)
    (μ ν : Fin 4) :
    ((∀ (i : Fin 0) t, repVC.1.1 (.inl i) = .inr t → α t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ t (i : Fin 0), repVC.1.1 (.inr t) = .inl i → β t = (![] : Fin 0 → Fin 4) i) ∧
        (∀ j a, repVC.1.2 (.inl j) = .inr a → lor a = ![μ, ν] j)) ↔
      (lor (ps4 0) = μ ∧ lor (ps4 3) = ν) := by
  have h0 : ∀ a, repVC.1.2 (.inl 0) = .inr a ↔ a = ps4 0 := by decide +kernel
  have h1 : ∀ a, repVC.1.2 (.inl 1) = .inr a ↔ a = ps4 3 := by decide +kernel
  simp only [Fin.forall_fin_two, h0, h1, forall_eq, IsEmpty.forall_iff, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, implies_true]

/-- **The amplitude of `repVC`** at the constant flavouring `f`, grading `0`. -/
theorem vc_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
    (kIn : Fin 2 → Fin 4 → ℝ) (kk : Line repVC → Fin 4 → ℝ) (μ ν : Fin 4) :
    contractionAmplitude P Φ D repVC (fun _ => f) 0 ![] kIn kk ![] ![] ![μ, ν] =
      (I * P.e) ^ 4 * (1 / I) ^ 5 * ∑ ρ : Fin 4, ∑ σ : Fin 4,
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gC)) ρ σ *
          Matrix.trace (Dirac.gamma μ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc0)) * Dirac.gamma ν *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc3)) * Dirac.gamma σ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc2)) * Dirac.gamma ρ *
            QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc1))) := by
  obtain ⟨t0, t1, t2, t3, h3⟩ := vc_tails
  unfold contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex k_gggg → Fin 4, ∑ β : Wick.FermionVertex k_gggg → Fin 4,
      ∑ lor : Wick.PhotonSlot k_gggg → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [vc_cond, Fin.prod_univ_four,
    prod_eq_of_four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      vc_fermionLine_cases,
    prod_eq_of_one vc_photonLine_cases, t0, t1, t2, t3, h3, vertexFactor_fv4,
    show vc0.1 = fv4 0 from rfl, show vc1.1 = fv4 1 from rfl, show vc2.1 = fv4 2 from rfl,
    show vc3.1 = fv4 3 from rfl, show gC.1 = ps4 1 from rfl]
  have hterm : ∀ (lor : Wick.PhotonSlot k_gggg → Fin 4)
      (α β : Wick.FermionVertex k_gggg → Fin 4),
      (if lor (ps4 0) = μ ∧ lor (ps4 3) = ν then (1 : ℂ) else 0) *
        (I * P.e * Dirac.gamma (lor (ps4 0)) (α (fv4 0)) (β (fv4 0)) *
          (I * P.e * Dirac.gamma (lor (ps4 1)) (α (fv4 1)) (β (fv4 1))) *
          (I * P.e * Dirac.gamma (lor (ps4 2)) (α (fv4 2)) (β (fv4 2))) *
          (I * P.e * Dirac.gamma (lor (ps4 3)) (α (fv4 3)) (β (fv4 3))) *
          (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc0)) (β (fv4 0))
              (α (fv4 3)) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc1)) (β (fv4 1))
              (α (fv4 0))) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc2)) (β (fv4 2))
              (α (fv4 1))) *
            (1 / I * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc3)) (β (fv4 3))
              (α (fv4 2)))) *
          (1 / I * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gC)) (lor (ps4 1))
            (lor (ps4 2)))) =
      (if lor (ps4 0) = μ ∧ lor (ps4 3) = ν then (1 : ℂ) else 0) *
        ((I * P.e) ^ 4 * (1 / I) ^ 5 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gC)) (lor (ps4 1)) (lor (ps4 2))) *
        (Dirac.gamma (lor (ps4 0)) (α (fv4 0)) (β (fv4 0)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc0)) (β (fv4 0)) (α (fv4 3)) *
          Dirac.gamma (lor (ps4 3)) (α (fv4 3)) (β (fv4 3)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc3)) (β (fv4 3)) (α (fv4 2)) *
          Dirac.gamma (lor (ps4 2)) (α (fv4 2)) (β (fv4 2)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc2)) (β (fv4 2)) (α (fv4 1)) *
          Dirac.gamma (lor (ps4 1)) (α (fv4 1)) (β (fv4 1)) *
          QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc1)) (β (fv4 1))
            (α (fv4 0))) := by
    intro lor α β
    ring
  refine (Finset.sum_congr rfl fun lor _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => hterm lor α β).trans ?_
  simp only [← Finset.mul_sum]
  simp only [sum_spinor_loop4 (x₁ := fv4 0) (x₂ := fv4 3) (x₃ := fv4 2) (x₄ := fv4 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)]
  refine (Finset.sum_congr rfl fun lor _ => mul_assoc _ _ _).trans ?_
  refine (sum_lor_ps4_3 μ ν (fun a b c d => (I * P.e) ^ 4 * (1 / I) ^ 5 *
    QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (kk (.inr gC)) b c *
    Matrix.trace (Dirac.gamma a * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc0)) *
      Dirac.gamma d * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc3)) *
      Dirac.gamma c * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc2)) *
      Dirac.gamma b * QED.OneLoop.electronPropagator (Φ.mass f) P.ε (kk (.inl vc1))))).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem oneLoop_repVC : OneLoop repVC := by
  intro t s
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 4) (by norm_num) (by decide +kernel)]
  revert t s
  decide +kernel

/-- The vertex matrices of `VC` in the order of the trace. -/
noncomputable def aVC (μ ν ρ σ : Fin 4) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![Dirac.gamma μ, Dirac.gamma ν, Dirac.gamma σ, Dirac.gamma ρ]

theorem isOddG_aVC (μ ν ρ σ : Fin 4) : ∀ l, IsOddG (aVC μ ν ρ σ l) := by
  intro l
  fin_cases l <;> exact isOddG_gamma _

/-- **The integrand of `repVC`** in its routing: a sum over the internal photon indices of
flavour sums of loop terms. -/
theorem vc_integrand (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (hε : P.ε ≠ 0) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D repVC 0 ![] ![k, -k] (vcMom k ℓ) ![] ![] ![μ, ν] =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ f, (Φ.coeff f : ℂ) *
        (kV P.e P.mγ P.Λ ρ σ * vD baseVC (ppVC k) P.mγ P.Λ P.ε ℓ *
          vH baseVC (ppVC k) (aVC μ ν ρ σ) P.ε (Φ.mass f) ℓ) := by
  obtain ⟨m0, m3, m2, m1, m4⟩ := vcMom_fm k ℓ
  have e : ∀ g : Fin 4 → Fin 4 → F → ℂ,
      ∑ ρ, ∑ σ, ∑ f, g ρ σ f = ∑ f, ∑ ρ, ∑ σ, g ρ σ f := fun g =>
    (Finset.sum_congr rfl fun ρ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [regulatedAmplitude_of_oneLoop Φ P D oneLoop_repVC (fv4 0), Finset.mul_sum, e]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [vc_amplitude, m0, m1, m2, m3, m4]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  have h := v_term_eq baseVC (ppVC k) P.e P.mγ P.Λ (Φ.mass f) hε (aVC μ ν ρ σ) ρ σ ℓ
  have a0 : aVC μ ν ρ σ 0 = Dirac.gamma μ := rfl
  have a1 : aVC μ ν ρ σ 1 = Dirac.gamma ν := rfl
  have a2 : aVC μ ν ρ σ 2 = Dirac.gamma σ := rfl
  have a3 : aVC μ ν ρ σ 3 = Dirac.gamma ρ := rfl
  rw [a0, a1, a2, a3] at h
  rw [← h]
  ring

theorem critA_VC :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => baseVC (shA i j n) := by
  decide

theorem critB_VC :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVC (shB i n) := by
  decide

/-- **The class obligation for `VC`.** -/
theorem classInt2_repVC : ClassInt2 repVC := by
  intro P F _ _ Φ D rep m₀ hH ε hε k μ ν
  rw [loopCount_repVC]
  refine JEF.congr (JEF.sum Finset.univ fun ρ _ => JEF.sum Finset.univ fun σ _ =>
    jef_vBlock baseVC (ppVC k) (isOddG_aVC μ ν ρ σ) critA_VC critB_VC Φ rep m₀ hH.hm₀ hH.hmass
      hH.hrep hH.hPV₁ hH.hPV₂ (kV P.e P.mγ P.Λ ρ σ) P.mγ P.Λ hε) fun ℓ => ?_
  rw [lineMomentum₂_repVC, vc_integrand { P with ε := ε } Φ D hε.ne' k ℓ μ ν]

end VC

end QED.GradedProof.VP2

end
