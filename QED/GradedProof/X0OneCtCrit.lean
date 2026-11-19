/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0OneCt
public import QED.GradedProof.X0Assemble

/-!
# (X₀): the one-loop open-line contractions with a counterterm vertex

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the one-loop
contractions with a counterterm vertex whose fermion fields all lie on the cycle of the external
field. A Boolean test `OneCrit` on the line data (`lineData`) and the kind sequence bounds the
counts of `jointEnergyFirstIntegrable_oneCt`: `vDegE` bounds the degree `vDeg` of each vertex
factor by asking whether some loop line ends at the vertex. Under `OneCrit` the graded integrand
at the zero grading satisfies (T₉′) (`jointEnergyFirstIntegrable_openCt`): it is the T1 amplitude
at the open-line counterterm parameters (`regulatedAmplitude_zero_eq_openCt`), with one-loop line
momenta `loopCoeff · ℓ + extPart`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.WickModel
open QED.Graded (Counterterms regulatedAmplitude)
open QED.TwoLoop.Enumeration (mAny mAny_eq_true lineData mem_lineData)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The Boolean test -/

/-- An edge-level bound for the degree `vDeg` of the vertex factor of `t`. -/
def vDegE (E : Multiset (ℕ × Fin N × Fin N)) (κ : Fin N → Wick.VertexKind) (t : Fin N) : ℕ :=
  if κ t = .fermionCt then
    (if mAny E (fun x => decide (x.2.2 = t) && decide (edgeCoeff E x 0 ≠ 0)) then 1 else 0)
  else if κ t = .photonCt then
    (if mAny E (fun x => (decide (x.2.1 = t) || decide (x.2.2 = t)) &&
      decide (edgeCoeff E x 0 ≠ 0)) then 2 else 0)
  else 0

/-- **The one-loop test**: with `L_f` (`L_g`) loop fermion (photon) edges and `D = ∑ vDegE`,
`L_f + D ≤ 4` and `4 + L_f + D < 2 (L_f + 2 L_g)`. -/
def OneCrit (E : Multiset (ℕ × Fin N × Fin N)) (κ : Fin N → Wick.VertexKind) : Prop :=
  edgeCount E true (fun y => edgeCoeff E y 0 ≠ 0) + ∑ t, vDegE E κ t ≤ 4 ∧
    4 + (edgeCount E true (fun y => edgeCoeff E y 0 ≠ 0) + ∑ t, vDegE E κ t) <
      2 * (edgeCount E true (fun y => edgeCoeff E y 0 ≠ 0) +
        2 * edgeCount E false (fun y => edgeCoeff E y 0 ≠ 0))

instance (E : Multiset (ℕ × Fin N × Fin N)) (κ : Fin N → Wick.VertexKind) :
    Decidable (OneCrit E κ) := by
  unfold OneCrit; infer_instance

/-! ### Transport to the counts of `jointEnergyFirstIntegrable_oneCt` -/

variable {C : Contraction nf nA κ}

theorem exists_of_psiCoeff_ne_zero {c : Line C → ℤ} {s : Wick.FermionVertex κ}
    (h : psiCoeff c s ≠ 0) : ∃ f : FermionLine C, f.1 = s ∧ c (.inl f) ≠ 0 := by
  unfold psiCoeff at h
  split at h
  · exact absurd rfl h
  · exact ⟨_, rfl, h⟩

theorem exists_of_slotCoeff_ne_zero {c : Line C → ℤ} {a : Wick.PhotonSlot κ}
    (h : slotCoeff c a ≠ 0) : ∃ g : PhotonLine C, (g.head = a ∨ g.1 = a) ∧ c (.inr g) ≠ 0 := by
  by_contra hne
  push Not at hne
  refine h (Finset.sum_eq_zero fun g _ => ?_)
  by_cases hg : c (.inr g) = 0
  · simp [hg]
  · have h1 : g.head ≠ a := fun h' => hg (hne g (Or.inl h'))
    have h2 : g.1 ≠ a := fun h' => hg (hne g (Or.inr h'))
    simp [h1, h2]

theorem vDeg_le_vDegE (t : Fin N) :
    vDeg (fun l => loopCoeff C l 0) t ≤ vDegE (lineData C) κ t := by
  unfold vDeg vDegE
  by_cases hf : κ t = .fermionCt
  · have hm : ¬ psiCoeff (fun l => loopCoeff C l 0) ⟨t, by rw [hf]; decide⟩ = 0 →
        mAny (lineData C) (fun x => decide (x.2.2 = t) &&
          decide (edgeCoeff (lineData C) x 0 ≠ 0)) = true := fun h0 => by
      obtain ⟨f, hfs, hc⟩ := exists_of_psiCoeff_ne_zero h0
      refine (mAny_eq_true _ _).2 ⟨edgeOf (.inl f), mem_lineData.2 ⟨_, rfl⟩, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by simp [edgeOf, Line.ends, hfs], hc⟩
    simp only [hf, dite_true, ite_true]
    split_ifs <;> simp_all
  · by_cases hp : κ t = .photonCt
    · have hm : ¬ slotCoeff (fun l => loopCoeff C l 0) ⟨t, ⟨0, by rw [hp]; decide⟩⟩ = 0 →
          mAny (lineData C) (fun x => (decide (x.2.1 = t) || decide (x.2.2 = t)) &&
            decide (edgeCoeff (lineData C) x 0 ≠ 0)) = true := fun h0 => by
        obtain ⟨g, hg, hc⟩ := exists_of_slotCoeff_ne_zero h0
        refine (mAny_eq_true _ _).2 ⟨edgeOf (.inr g), mem_lineData.2 ⟨_, rfl⟩, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨?_, hc⟩
        rcases hg with hg | hg
        · right; simp [edgeOf, Line.ends, hg]
        · left; simp [edgeOf, Line.ends, hg]
      simp only [hp, dite_false, dite_true, ite_false, ite_true, reduceCtorEq]
      split_ifs <;> simp_all
    · simp [hf, hp]

/-- `OneCrit` gives the hypotheses of `jointEnergyFirstIntegrable_oneCt`. -/
theorem oneCrit_bounds (h : OneCrit (lineData C) κ) :
    oneDeg (fun l => loopCoeff C l 0) ≤ 4 ∧
      4 + oneDeg (fun l => loopCoeff C l 0) <
        2 * (loopFermionCount (fun l => loopCoeff C l 0) +
          2 * loopPhotonCount (fun l => loopCoeff C l 0)) := by
  have hF : loopFermionCount (fun l => loopCoeff C l 0) =
      edgeCount (lineData C) true (fun y => edgeCoeff (lineData C) y 0 ≠ 0) :=
    card_filter_fermion (C := C) (fun y => edgeCoeff (lineData C) y 0 ≠ 0)
  have hG : loopPhotonCount (fun l => loopCoeff C l 0) =
      edgeCount (lineData C) false (fun y => edgeCoeff (lineData C) y 0 ≠ 0) :=
    card_filter_photon (C := C) (fun y => edgeCoeff (lineData C) y 0 ≠ 0)
  have hV : ∑ t, vDeg (fun l => loopCoeff C l 0) t ≤ ∑ t, vDegE (lineData C) κ t :=
    Finset.sum_le_sum fun t _ => vDeg_le_vDegE t
  unfold oneDeg
  obtain ⟨h1, h2⟩ := h
  omega

/-! ### The graded integrand -/

/-- The parameters of the open line with its level-`0` counterterms. -/
def openCtParams (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) : Params :=
  { P with
    δ₁ := P.e ^ 2 * D.d₁ Φ.openLine 0
    δ₂ := P.e ^ 2 * D.d₂ Φ.openLine 0
    δm := P.e ^ 2 * D.dm Φ.openLine 0
    δ₃ := P.e ^ 2 * D.d₃ 0
    m := Φ.mass Φ.openLine }

open scoped Classical in
/-- **The graded integrand of an open-line contraction at the zero grading** is the T1 amplitude
at the open-line counterterm parameters (any vertex kinds). -/
theorem regulatedAmplitude_zero_eq_openCt (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (C : Contraction 1 nA κ)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0))
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C 0 pIn kIn k αOut βIn μ =
      contractionAmplitude₂ (openCtParams P Φ D) C
        (QED.TwoLoop.Insertion.zeroFlavoring κ) pIn kIn k αOut βIn μ := by
  have hct : QED.GradedProof.CtReaches C := fun t _ => ⟨0, (hcyc _).symm⟩
  rw [QED.GradedProof.regulatedAmplitude_zero_eq P (openCtParams P Φ D) Φ D C hct rfl rfl rfl
      rfl (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl),
    QED.Lepton.Proof.HM.regulatedAmplitude₂_of_not_hasLoop _ _ (isSimple_of_cycle hcyc)
      (not_hasLoop_of_cycle hcyc)]
  exact loopAmp_eq_contractionAmplitude₂ _ _ _ rfl _ _ _ _ _ _

/-- One-loop line momenta. -/
theorem lineMomentum₂_eq_oneMom (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 1 → Fin 4 → ℝ) :
    lineMomentum₂ C pOut pIn kIn ℓ =
      oneMom (fun l => loopCoeff C l 0) (extPart C pOut pIn kIn) (ℓ 0) := by
  funext f
  rw [lineMomentum₂_eq_loopCoeff, Fin.sum_univ_one]
  rfl

/-- **(X₀) for a one-loop open-line contraction passing `OneCrit`**, at the zero grading. -/
theorem jointEnergyFirstIntegrable_openCt (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (hε : 0 < P.ε) (C : Contraction 1 1 κ)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hL : loopCount C = 1)
    (hcrit : OneCrit (lineData C) κ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  unfold integrand
  rw [hL]
  simp only [regulatedAmplitude_zero_eq_openCt P Φ D C hcyc, lineMomentum₂_eq_oneMom]
  obtain ⟨hd, hn⟩ := oneCrit_bounds hcrit
  exact jointEnergyFirstIntegrable_oneCt (openCtParams P Φ D) hε C _ _ _ hd hn pIn kIn αOut βIn
    μ _

end QED.GradedProof.X0

end
