/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestVA
public import QED.ChainProof.SetALinkIntVC

/-!
# Set (a), obligation (N): the nested form of the three-loop class `VC`

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the nested form
`QED.ChainProof.SetANest.LoopNested` of `QED.ChainProof.SetALink.repVC` (the two-loop
vacuum-polarization insertion with a self-energy on the loop line `u → w`), as for `VA` in
`QED/ChainProof/SetANestVA.lean`.

* Routing: `v3cMom`, inner momenta `ℓ 0`, `ℓ 1`, outer momentum `ℓ 2 = k` (lines `0 → 1`:
  `p + k`, `1 → 2`: `p' + k`, `5 → 3`: `ℓ 0 - k`, `3 → 4`: `ℓ 0`, `6 → 5`: `ℓ 1`, `4 → 6`:
  `ℓ 0 - k`; photons `0 → 4`: `-k`, `2 → 3`: `k`, `5 → 6`: `-(ℓ 0 - ℓ 1 - k)`), with the chords
  (lines `0 → 1`, `5 → 3`, `6 → 5`) at `v3aMat ℓ + (p, 0, 0)`. The loop `4 → 6 → 5 → 3 → 4` is
  the loop `0 → 1 → 2 → 3 → 0` of the two-photon class `VC` of `Π⁽⁴⁾`
  (`QED.GradedProof.VP2.repVC`) at the photon momentum `-k`.
* **`v3c_routedIntegrand`**: the integrand of the value in the routing `v3cMom` is
  `nestG nestOuter v3cY`, `v3cY_{ab}(k, q) = (1/i) vSumF(VC)(-k, q)_{ab}`.
* **`loopNested_v3c`**: under `IntHypA` and masses bounded below by `m₀ > 0`, `VC` is in nested
  form with `X(k)^{ab} = (1/i) val0(VC)(-k)^{ab}`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.SetALink QED.ChainProof.Enum
open scoped QED.TwoLoop.Enumeration

/-! ### Lines and routing of `VC` -/

/-- The fermion lines of `repVC`, by head `1, …, 6`. -/
def v3cL : Fin 6 → FermionLine repVC :=
  ![⟨fv kV 1, by decide +kernel⟩, ⟨fv kV 2, by decide +kernel⟩, ⟨fv kV 3, by decide +kernel⟩,
    ⟨fv kV 4, by decide +kernel⟩, ⟨fv kV 5, by decide +kernel⟩, ⟨fv kV 6, by decide +kernel⟩]

/-- The photon lines `0 — 4`, `2 — 3`, `5 — 6` of `repVC`. -/
def v3cP : Fin 3 → PhotonLine repVC :=
  ![⟨pg kV 0, by decide +kernel⟩, ⟨pg kV 2, by decide +kernel⟩, ⟨pg kV 5, by decide +kernel⟩]

theorem v3cL_bijective : Function.Bijective v3cL := by decide +kernel

theorem v3cP_bijective : Function.Bijective v3cP := by decide +kernel

theorem v3c_ends : (Line.ends (.inl (v3cL 0) : Line repVC)) = (0, 1) ∧
    (Line.ends (.inl (v3cL 1) : Line repVC)) = (1, 2) ∧
    (Line.ends (.inl (v3cL 2) : Line repVC)) = (5, 3) ∧
    (Line.ends (.inl (v3cL 3) : Line repVC)) = (3, 4) ∧
    (Line.ends (.inl (v3cL 4) : Line repVC)) = (6, 5) ∧
    (Line.ends (.inl (v3cL 5) : Line repVC)) = (4, 6) ∧
    (Line.ends (.inr (v3cP 0) : Line repVC)) = (0, 4) ∧
    (Line.ends (.inr (v3cP 1) : Line repVC)) = (2, 3) ∧
    (Line.ends (.inr (v3cP 2) : Line repVC)) = (5, 6) := by decide +kernel

theorem v3c_isChord_iff : ∀ f : Line repVC,
    IsChord f ↔ f = .inl (v3cL 0) ∨ f = .inl (v3cL 2) ∨ f = .inl (v3cL 4) := by
  decide +kernel

theorem v3c_sum_line {M : Type*} [AddCommMonoid M] (g : Line repVC → M) :
    ∑ f, g f = g (.inl (v3cL 0)) + g (.inl (v3cL 1)) + g (.inl (v3cL 2)) + g (.inl (v3cL 3)) +
      g (.inl (v3cL 4)) + g (.inl (v3cL 5)) +
      (g (.inr (v3cP 0)) + g (.inr (v3cP 1)) + g (.inr (v3cP 2))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ v3cL_bijective).sum_comp,
    ← (Equiv.ofBijective _ v3cP_bijective).sum_comp, Fin.sum_univ_six, Fin.sum_univ_three]
  rfl

theorem v3c_ext (v : Fin 7) :
    ((∃ t : Wick.FermionVertex kV, t.1 = v ∧ repVC.1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kV, a.1 = v ∧ repVC.1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kV, t.1 = v ∧ repVC.1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  revert v
  decide +kernel

/-- **The nested routing of `VC`**: inner momenta `ℓ 0`, `ℓ 1`, outer momentum `ℓ 2`. -/
def v3cMom (p kext : Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) (f : Line repVC) : Fin 4 → ℝ :=
  match f.label with
  | 1 => p + ℓ 2
  | 2 => p + kext + ℓ 2
  | 3 => ℓ 0 + -ℓ 2
  | 4 => ℓ 0
  | 5 => ℓ 1
  | 6 => ℓ 0 + -ℓ 2
  | 7 => -ℓ 2
  | 11 => ℓ 2
  | _ => -(ℓ 0 - ℓ 1 + -ℓ 2)

theorem v3cMom_apply (p kext : Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) :
    v3cMom p kext ℓ (.inl (v3cL 0)) = p + ℓ 2 ∧ v3cMom p kext ℓ (.inl (v3cL 1)) = p + kext + ℓ 2 ∧
      v3cMom p kext ℓ (.inl (v3cL 2)) = ℓ 0 + -ℓ 2 ∧ v3cMom p kext ℓ (.inl (v3cL 3)) = ℓ 0 ∧
      v3cMom p kext ℓ (.inl (v3cL 4)) = ℓ 1 ∧ v3cMom p kext ℓ (.inl (v3cL 5)) = ℓ 0 + -ℓ 2 ∧
      v3cMom p kext ℓ (.inr (v3cP 0)) = -ℓ 2 ∧ v3cMom p kext ℓ (.inr (v3cP 1)) = ℓ 2 ∧
      v3cMom p kext ℓ (.inr (v3cP 2)) = -(ℓ 0 - ℓ 1 + -ℓ 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem isConserved_v3cMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 3 → Fin 4 → ℝ) : IsConserved repVC pOut pIn kIn (v3cMom (pIn 0) (kIn 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, g0, g1, g2⟩ := v3c_ends
  obtain ⟨n0, n1, n2, n3, n4, n5, m0, m1, m2⟩ := v3cMom_apply (pIn 0) (kIn 0) ℓ
  intro v
  obtain ⟨x0, x1, x2⟩ := v3c_ext v
  rw [inflow, v3c_sum_line, QED.TwoLoop.Insertion.externalMomentum_one_one, hmom]
  simp only [e0, e1, e2, e3, e4, e5, g0, g1, g2, n0, n1, n2, n3, n4, n5, m0, m1, m2, x0, x1, x2]
  fin_cases v
  all_goals simp
  all_goals abel

theorem v3c_chordMomentum (ℓ : Fin 3 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (v3cL 0) : Line repVC) = ℓ 0 ∧
      chordMomentum ℓ (.inl (v3cL 2) : Line repVC) = ℓ 1 ∧
      chordMomentum ℓ (.inl (v3cL 4) : Line repVC) = ℓ 2 :=
  ⟨chordMomentum_eq_of_card ℓ _ 0 (by decide +kernel),
    chordMomentum_eq_of_card ℓ _ 1 (by decide +kernel),
    chordMomentum_eq_of_card ℓ _ 2 (by decide +kernel)⟩

/-- The chords of `VC` carry the frozen loop momenta at `v3aMat ℓ + (p, 0, 0)`. -/
theorem v3c_hchord (p kext : Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) (f : Line repVC)
    (hf : IsChord f) : v3cMom p kext ℓ f =
      chordMomentum ((fun s => ∑ r, v3aMat s r • ℓ r) + ![p, 0, 0]) f := by
  obtain ⟨c0, c1, c2⟩ := v3c_chordMomentum ((fun s => ∑ r, v3aMat s r • ℓ r) + ![p, 0, 0])
  obtain ⟨n0, -, n2, -, n4, -⟩ := v3cMom_apply p kext ℓ
  rcases (v3c_isChord_iff f).mp hf with rfl | rfl | rfl
  · rw [c0, n0]
    simp [v3aMat, Fin.sum_univ_three]
    abel
  · rw [c1, n2]
    simp [v3aMat, Fin.sum_univ_three]
  · rw [c2, n4]
    simp [v3aMat, Fin.sum_univ_three]

/-! ### The amplitude of `VC` -/

open QED.OneLoop (photonPropagator electronPropagator)
open QED.GradedProof.X0 (closedFlavoring zOf)

theorem v3c_tails : (v3cL 0).tail = fv kV 0 ∧ (v3cL 1).tail = fv kV 1 ∧
    (v3cL 2).tail = fv kV 5 ∧ (v3cL 3).tail = fv kV 3 ∧ (v3cL 4).tail = fv kV 6 ∧
    (v3cL 5).tail = fv kV 4 := by decide +kernel

theorem v3c_heads : (v3cP 0).head = pg kV 4 ∧ (v3cP 1).head = pg kV 3 ∧
    (v3cP 2).head = pg kV 6 := by decide +kernel

theorem v3c_vals : (v3cL 0).1 = fv kV 1 ∧ (v3cL 1).1 = fv kV 2 ∧ (v3cL 2).1 = fv kV 3 ∧
    (v3cL 3).1 = fv kV 4 ∧ (v3cL 4).1 = fv kV 5 ∧ (v3cL 5).1 = fv kV 6 ∧
    (v3cP 0).1 = pg kV 0 ∧ (v3cP 1).1 = pg kV 2 ∧ (v3cP 2).1 = pg kV 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem v3c_prod_fermionLine {M : Type*} [CommMonoid M] (g : FermionLine repVC → M) :
    ∏ f, g f = g (v3cL 0) * g (v3cL 1) * g (v3cL 2) * g (v3cL 3) * g (v3cL 4) * g (v3cL 5) := by
  rw [← (Equiv.ofBijective _ v3cL_bijective).prod_comp, Fin.prod_univ_six]
  rfl

theorem v3c_prod_photonLine {M : Type*} [CommMonoid M] (g : PhotonLine repVC → M) :
    ∏ f, g f = g (v3cP 0) * g (v3cP 1) * g (v3cP 2) := by
  rw [← (Equiv.ofBijective _ v3cP_bijective).prod_comp, Fin.prod_univ_three]
  rfl

theorem v3c_cond (α β : Wick.FermionVertex kV → Fin 4) (lor : Wick.PhotonSlot kV → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repVC.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repVC.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repVC.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      (lor (pg kV 1) = μ 0 ∧ (α (fv kV 2) = αOut 0 ∧ β (fv kV 0) = βIn 0)) := by
  have h0 : ∀ t, repVC.1.1 (.inl 0) = .inr t ↔ t = fv kV 2 := by decide +kernel
  have h1 : ∀ t, repVC.1.1 (.inr t) = .inl 0 ↔ t = fv kV 0 := by decide +kernel
  have h2 : ∀ a, repVC.1.2 (.inl 0) = .inr a ↔ a = pg kV 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h0, h1, h2, forall_eq]
  tauto

theorem v3c_flav {F : Type} (Φ : Lepton.Flavors F) (f : F) :
    closedFlavoring Φ (zOf repVC) f (fv kV 0) = Φ.openLine ∧
    closedFlavoring Φ (zOf repVC) f (fv kV 1) = Φ.openLine ∧
    closedFlavoring Φ (zOf repVC) f (fv kV 2) = Φ.openLine ∧
    closedFlavoring Φ (zOf repVC) f (fv kV 3) = f ∧
    closedFlavoring Φ (zOf repVC) f (fv kV 4) = f ∧
    closedFlavoring Φ (zOf repVC) f (fv kV 5) = f ∧
    closedFlavoring Φ (zOf repVC) f (fv kV 6) = f := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold closedFlavoring <;> split_ifs with h <;>
    first | rfl | exact absurd h (by decide +kernel)

/-- The splitting of the fermion fields of `repVC` into the open line `2, 1, 0` and the loop
`4, 3, 5, 6`. -/
noncomputable def v3cSplit : Wick.FermionVertex kV ≃ Fin 3 ⊕ Fin 4 :=
  Equiv.ofBijective (fun t => (![.inl 2, .inl 1, .inl 0, .inr 1, .inr 0, .inr 2, .inr 3] :
    Fin 7 → _) t.1) (by decide +kernel)

/-- **The amplitude of `repVC`** at the flavouring with loop flavour `f`. -/
theorem v3c_amplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (f : F) (pIn kIn : Fin 1 → Fin 4 → ℝ) (kk : Line repVC → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionAmplitude P Φ D repVC (closedFlavoring Φ (zOf repVC) f) 0 pIn kIn kk
        αOut βIn μ =
      (I * P.e) ^ 7 * (1 / I) ^ 9 *
        ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l6 : Fin 4, ∑ l5 : Fin 4,
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 0))) l0 l4 *
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 1))) l2 l3 *
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 2))) l5 l6 *
          Matrix.trace (Dirac.gamma l4 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 3))) *
            Dirac.gamma l3 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 2))) *
            Dirac.gamma l5 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 4))) *
            Dirac.gamma l6 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 5)))) *
          (Dirac.gamma l2 * electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3cL 1))) *
            Dirac.gamma (μ 0) *
            electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3cL 0))) * Dirac.gamma l0)
            (αOut 0) (βIn 0) := by
  obtain ⟨t0, t1, t2, t3, t4, t5⟩ := v3c_tails
  obtain ⟨g0, g1, g2⟩ := v3c_heads
  obtain ⟨v0, v1, v2, v3, v4, v5, w0, w1, w2⟩ := v3c_vals
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := v3c_flav Φ f
  unfold Graded.contractionAmplitude
  rw [show (∑ α : Wick.FermionVertex kV → Fin 4, ∑ β : Wick.FermionVertex kV → Fin 4,
      ∑ lor : Wick.PhotonSlot kV → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [v3c_cond, Fin.prod_univ_seven, v3c_prod_fermionLine, v3c_prod_photonLine, t0, t1, t2,
    t3, t4, t5, g0, g1, g2, v0, v1, v2, v3, v4, v5, w0, w1, w2, vertexFactor_kV, f1, f2, f3, f4,
    f5, f6, ite_and_eq_mul_ite]
  set K : ℂ := (I * P.e) ^ 7 * (1 / I) ^ 9 with hK
  have hR : K * ∑ l4 : Fin 4, ∑ l3 : Fin 4, ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l6 : Fin 4,
      ∑ l5 : Fin 4,
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 0))) l0 l4 *
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 1))) l2 l3 *
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 2))) l5 l6 *
        Matrix.trace (Dirac.gamma l4 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 3))) *
          Dirac.gamma l3 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 2))) *
          Dirac.gamma l5 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 4))) *
          Dirac.gamma l6 * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 5)))) *
        (Dirac.gamma l2 * electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3cL 1))) *
          Dirac.gamma (μ 0) *
          electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3cL 0))) * Dirac.gamma l0)
          (αOut 0) (βIn 0) =
      ∑ lor : Wick.PhotonSlot kV → Fin 4, (if lor (pg kV 1) = μ 0 then (1 : ℂ) else 0) *
        (K * (photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 0))) (lor (pg kV 0)) (lor (pg kV 4)) *
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 1))) (lor (pg kV 2)) (lor (pg kV 3)) *
          photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 2))) (lor (pg kV 5)) (lor (pg kV 6)) *
          Matrix.trace (Dirac.gamma (lor (pg kV 4)) *
            electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 3))) *
            Dirac.gamma (lor (pg kV 3)) * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 2))) *
            Dirac.gamma (lor (pg kV 5)) * electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 4))) *
            Dirac.gamma (lor (pg kV 6)) *
            electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 5)))) *
          (Dirac.gamma (lor (pg kV 2)) *
            electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3cL 1))) *
            Dirac.gamma (lor (pg kV 1)) *
            electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3cL 0))) *
            Dirac.gamma (lor (pg kV 0))) (αOut 0) (βIn 0))) := by
    rw [sum_lor_kV]
    simp only [pg, Matrix.cons_val]
    symm
    rw [Finset.sum_eq_single (μ 0)
      (fun b _ hb => by simp only [hb, ite_false, zero_mul, Finset.sum_const_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [ite_true, one_mul, Finset.mul_sum]
  rw [hR]
  refine Finset.sum_congr rfl fun lor _ => ?_
  by_cases hL : lor (pg kV 1) = μ 0
  · have h := sum_spinor_chain3_loop4 v3cSplit (x₁ := fv kV 2) (x₂ := fv kV 1) (x₃ := fv kV 0)
      (y₁ := fv kV 4) (y₂ := fv kV 3) (y₃ := fv kV 5) (y₄ := fv kV 6) rfl rfl rfl rfl rfl rfl rfl
      (K * photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 0))) (lor (pg kV 0)) (lor (pg kV 4)) *
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 1))) (lor (pg kV 2)) (lor (pg kV 3)) *
        photonPropagator P.mγ P.Λ P.ε (kk (.inr (v3cP 2))) (lor (pg kV 5)) (lor (pg kV 6)))
      (Dirac.gamma (lor (pg kV 2))) (Dirac.gamma (μ 0)) (Dirac.gamma (lor (pg kV 0)))
      (electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3cL 1))))
      (electronPropagator (Φ.mass Φ.openLine) P.ε (kk (.inl (v3cL 0))))
      (Dirac.gamma (lor (pg kV 4))) (Dirac.gamma (lor (pg kV 3))) (Dirac.gamma (lor (pg kV 5)))
      (Dirac.gamma (lor (pg kV 6)))
      (electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 3))))
      (electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 2))))
      (electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 4))))
      (electronPropagator (Φ.mass f) P.ε (kk (.inl (v3cL 5)))) (αOut 0) (βIn 0)
    simp only [hL, ite_true, one_mul]
    refine Eq.trans ?_ (h.trans ?_)
    · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hK]
      by_cases ha : α (fv kV 2) = αOut 0 <;> by_cases hb : β (fv kV 0) = βIn 0 <;>
        simp only [ha, hb, and_true, and_false, ite_true, ite_false] <;> ring
    · ring
  · simp only [hL, ite_false, zero_mul, Finset.sum_const_zero]

/-! ### The inner integrand of `VC` -/

/-- The block-summed integrand of the two-photon class `VC` of `Π⁽⁴⁾` is `(2π)⁻⁸` times its
regulated amplitude in its routing. -/
theorem v3c_vSumF_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (k : Fin 4 → ℝ) (q : Fin 2 → Fin 4 → ℝ)
    (a b : Fin 4) :
    QED.GradedProof.VP2.vSumF Φ P.e QED.GradedProof.VP2.aVC QED.GradedProof.VP2.baseVC
        QED.GradedProof.VP2.cVC P.mγ P.Λ P.ε k q a b =
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D QED.GradedProof.VP2.repVC 0 ![] ![k, -k]
          (QED.GradedProof.VP2.vcMom k q) ![] ![] ![a, b] := by
  rw [QED.GradedProof.VP2.vc_integrand P Φ D hε k q a b,
    QED.GradedProof.VP2.pp_eq_ppc QED.GradedProof.VP2.ppVC_eq k]
  exact (QED.GradedProof.VP2.sum_vterm_eq Φ _ _ _ P.e P.mγ P.Λ P.ε k q a b).symm

/-- The inner integrands of `VC`: `(1/i)` times the block-summed integrand of the two-photon class
`VC` at `-k`. -/
noncomputable def v3cY (P : Params) {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (a b : Fin 4)
    (k : Fin 4 → ℝ) (q : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (1 / I) * QED.GradedProof.VP2.vSumF Φ P.e QED.GradedProof.VP2.aVC QED.GradedProof.VP2.baseVC
    QED.GradedProof.VP2.cVC P.mγ P.Λ P.ε (-k) q a b

/-- **The Wick factorization of `VC`**: in the nested routing, the integrand of the value of
`repVC` is `nestG` of the outer factor and the inner integrands `v3cY`. -/
theorem v3c_routedIntegrand (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) (ℓ : Fin 3 → Fin 4 → ℝ) :
    routedIntegrand P Φ D repVC 0 3 (fun _ => p) (fun _ => p' - p) (v3cMom p (p' - p) ℓ)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.ChainProof.SetANestV.nestG
        (QED.ChainProof.SetANestV.nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (v3cY P Φ) ℓ := by
  obtain ⟨s1, s2, s3⟩ := QED.ChainProof.SetALinkV.shapeOK_repVC
  have hC : QED.GradedProof.X0.ClosedShape repVC (zOf repVC) :=
    ⟨s1, fun t ht => s2 t ht not_false, s3⟩
  obtain ⟨n0, n1, n2, n3, n4, n5, m0, m1, m2⟩ := v3cMom_apply p (p' - p) ℓ
  obtain ⟨u0, u1, u2, u3, u4⟩ := QED.GradedProof.VP2.vcMom_apply (-ℓ 2) ![ℓ 0, ℓ 1]
  have hp : p + (p' - p) + ℓ 2 = p' + ℓ 2 := by abel
  simp only [routedIntegrand, QED.GradedProof.X0.regulatedAmplitude_eq_closed Φ P D hC,
    v3c_amplitude, QED.ChainProof.SetANestV.nestG, v3cY, v3c_vSumF_eq P Φ D hε,
    QED.GradedProof.VP2.regulatedAmplitude_of_oneLoop Φ P D QED.GradedProof.VP2.oneLoop_repVC
      (QED.GradedProof.SE2.fv4 0),
    QED.GradedProof.VP2.vc_amplitude, QED.ChainProof.SetANestV.nestOuter,
    QED.TwoLoop.Insertion.vertexChain, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    n0, n1, n2, n3, n4, n5, m0, m1, m2, u0, u1, u2, u3, u4, hp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mul_sum, Finset.sum_mul]
  rw [sum_flavor_out_four]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [sum_pair_out_three]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl
    fun f _ => Finset.sum_congr rfl fun ρ' _ => Finset.sum_congr rfl fun σ' _ => ?_
  rw [QED.TwoLoop.Insertion.photonPropagator_neg', QED.TwoLoop.Insertion.photonPropagator_neg',
    QED.TwoLoop.Insertion.photonPropagator_neg' _ _ _ (ℓ 2),
    QED.TwoLoop.Insertion.photonPropagator_comm' _ _ _ (ℓ 0 - ℓ 1 + -ℓ 2) σ' ρ']
  push_cast
  ring

/-! ### The inputs of the nested form of `VC` -/

/-- The value of `repVC` is the joint three-loop integral of `nestG nestOuter v3cY`. -/
theorem v3c_hval (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    Graded.contractionValue P Φ D repVC 0 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 3 (QED.ChainProof.SetANestV.nestG
        (QED.ChainProof.SetANestV.nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (v3cY P Φ)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcons := isConserved_v3cMom (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) hmom
  rw [contractionValue_eq_of_routing P Φ D repVC 0 loopCount_repVC (v3cMom p (p' - p))
    hcons v3aMat isUnit_det_v3aMat ![p, 0, 0] (v3c_hchord p (p' - p))]
  exact congrArg _ (funext fun ℓ => v3c_routedIntegrand P Φ D hε p' p μ i j ℓ)

/-- (HA₀) for `repVC` in the nested routing. -/
theorem v3c_hF (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (rep : F → F) (hH : QED.ChainProof.SetALink.IntHypA P Φ D rep)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3 (QED.ChainProof.SetANestV.nestG
        (QED.ChainProof.SetANestV.nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j)
        (v3cY P Φ)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hcons := isConserved_v3cMom (pOut := fun _ => p') (pIn := fun _ => p)
    (kIn := fun _ => p' - p) hmom
  have h := jointEnergyFirstIntegrable_of_routing P Φ D repVC 0 loopCount_repVC
    (v3cMom p (p' - p)) hcons v3aMat isUnit_det_v3aMat ![p, 0, 0]
    (v3c_hchord p (p' - p)) _ _ _
    (QED.ChainProof.SetALinkV.classIntA_repVC P Φ D rep hH (fun _ => p') (fun _ => p)
      (fun _ => p' - p) hmom (fun _ => i) (fun _ => j) (fun _ => μ))
  exact (congrArg _ (funext fun ℓ => v3c_routedIntegrand P Φ D hH.hε.ne' p' p μ i j ℓ)).mp h

/-- The photon tensor of `VC`: the joint integral of `v3cY` is `(1/i)` times the value of the
two-photon class `VC` at `-k`. -/
theorem v3c_efi (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) (hε : P.ε ≠ 0) (k : Fin 4 → ℝ) (a b : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (v3cY P Φ a b k) =
      (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repVC := by
  rw [show v3cY P Φ a b k = fun q => (1 / I) * QED.GradedProof.VP2.vSumF Φ P.e
      QED.GradedProof.VP2.aVC QED.GradedProof.VP2.baseVC QED.GradedProof.VP2.cVC P.mγ P.Λ P.ε
      (-k) q a b from rfl, QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  exact congrArg _ (QED.GradedProof.VP2.val0_repVC Φ D P hε (-k) a b).symm

/-- **The nested form of `VC`.** Under the hypotheses `IntHypA` of (HA₀) and masses bounded below
by `m₀ > 0`, the class `VC` is in nested form with the photon tensor
`X(k)^{ab} = (1/i) val0(VC)(-k)^{ab}` of the two-photon class `VC` of `Π⁽⁴⁾`. -/
theorem loopNested_v3c (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F)
    (hH : QED.ChainProof.SetALink.IntHypA P Φ D rep) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (p' p : Fin 4 → ℝ) :
    LoopNested P Φ D repVC
      (fun k a b => (1 / I) * QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repVC)
      p' p := by
  have hE := QED.ChainProof.SetANestV.el1_VC Φ rep hm₀ hmass hH.hrep hH.hPV₁ hH.hPV₂ P.e P.mγ P.Λ
  have h := QED.ChainProof.SetANestV.loopNested_of_nestGL1 P Φ D repVC hH.hε p' p (v3cY P Φ)
    (fun μ i j => v3c_hval P Φ D hH.hε.ne' p' p μ i j) (fun μ i j => v3c_hF P Φ D rep hH p' p μ i j)
    (fun a b k => QED.ChainProof.SetANestV.jointEnergyFirstIntegrable_vSumF_neg Φ P.e P.mγ P.Λ _ _ _
      hE hH.hε (1 / I) a b k)
    (fun a b => QED.ChainProof.SetANestV.innerBoundL1_vSumF_neg Φ P.e P.mγ P.Λ _ _ _ hE hH.hε
      (1 / I) a b)
  have e : (fun k a b => QED.TwoLoop.jointEnergyFirstIntegral 2 (v3cY P Φ a b k)) =
      fun k a b => (1 / I) *
        QED.GradedProof.VP2.val0 P Φ D (-k) a b QED.GradedProof.VP2.repVC :=
    funext fun k => funext fun a => funext fun b => v3c_efi P Φ D hH.hε.ne' k a b
  rwa [e] at h

end QED.ChainProof.SetANest

end
