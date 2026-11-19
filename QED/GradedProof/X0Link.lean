/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.Embed
public import QED.LeptonProof.HMFlavourLoop
public import QED.TwoLoop.CountertermInsertionBasic

/-!
# (X₀): the graded integrand of an open-line gauge contraction at the zero grading

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d.8. For a
contraction of `gauge` vertices whose fermion fields all lie on the cycle of the external field
(no closed loop), the graded value (G₄) at the zero grading is the amplitude (T₇) of packet T1 at
the all-electron flavoring, with electron mass the open-line mass `M_f` of `Φ`
(`regulatedAmplitude_zero_eq_contractionAmplitude₂`). Only flavour sums and definitions are
involved; no mass condition.
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.WickModel (Params Contraction Line)
open QED.Graded
open QED.Lepton.Proof.HM (IsSimple HasLoop OnOpen loopAmp biFlavors loopFlavoring)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The parameters of the open line: electron mass `M_f`. -/
def openParams (P : Params) {F : Type} (Φ : Lepton.Flavors F) : Params :=
  { P with m := Φ.mass Φ.openLine }

theorem onOpen_of_cycle {C : Contraction 1 nA κ}
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (t : Wick.FermionVertex κ) :
    OnOpen C t :=
  ⟨0, hcyc _⟩

theorem isSimple_of_cycle {C : Contraction 1 nA κ}
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) : IsSimple C :=
  ⟨fun t h => absurd (onOpen_of_cycle hcyc t) h, fun t _ h _ => absurd (onOpen_of_cycle hcyc t) h⟩

theorem not_hasLoop_of_cycle {C : Contraction 1 nA κ}
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) : ¬ HasLoop C :=
  fun ⟨t, h⟩ => h (onOpen_of_cycle hcyc t)

/-- The amplitude with equal open-line and loop masses is the T1 amplitude at the all-electron
flavoring, when the T1 electron mass is that mass. -/
theorem loopAmp_eq_contractionAmplitude₂ (P : Params) {C : Contraction 1 nA κ}
    (hS : IsSimple C) (a : ℝ) (ha : P.m = a) (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    loopAmp P hS a a pIn kIn k αOut βIn μ =
      QED.WickModel.contractionAmplitude₂ P C (QED.TwoLoop.Insertion.zeroFlavoring κ) pIn kIn k
        αOut βIn μ := by
  unfold loopAmp Lepton.contractionAmplitude₂ QED.WickModel.contractionAmplitude₂
  have hm : ∀ x : Bool, (biFlavors a a).mass x = P.mass 0 := fun x => by
    cases x <;> simp [biFlavors, QED.WickModel.Params.mass, ha]
  simp only [hm]
  rfl

open scoped Classical in
/-- **The graded integrand at the zero grading without a closed loop.** -/
theorem regulatedAmplitude_zero_eq_contractionAmplitude₂ (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (hκ : ∀ t, κ t = .gauge)
    (C : Contraction 1 nA κ) (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0))
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C 0 pIn kIn k αOut βIn μ =
      QED.WickModel.contractionAmplitude₂ (openParams P Φ) C
        (QED.TwoLoop.Insertion.zeroFlavoring κ) pIn kIn k αOut βIn μ := by
  have hct : QED.GradedProof.CtReaches C := fun t ht => absurd (hκ t.1) ht
  rw [QED.GradedProof.regulatedAmplitude_zero_eq P (openParams P Φ) Φ D C hct rfl rfl rfl rfl
      (fun t ht => absurd ht (by rw [hκ t]; decide))
      (fun t ht => absurd ht (by rw [hκ t]; decide))
      (fun t ht => absurd ht (by rw [hκ t]; decide)),
    QED.Lepton.Proof.HM.regulatedAmplitude₂_of_not_hasLoop _ _ (isSimple_of_cycle hcyc)
      (not_hasLoop_of_cycle hcyc)]
  exact loopAmp_eq_contractionAmplitude₂ _ _ _ rfl _ _ _ _ _ _

end QED.GradedProof.X0

end
