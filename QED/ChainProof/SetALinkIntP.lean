/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkInt
public import QED.GradedProof.X0OneCtCrit
public import QED.GradedProof.VertexTwo

/-!
# The class obligation of (HA₀) for the `photonCt` classes

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58): `classIntA_repP`, the class obligation `ClassIntA (repP s) gradP` for the
one-loop representatives with the level-`1` photon counterterm.

## Proof

Every fermion field of `repP s` lies on the cycle of the external field, so the graded integrand
at the grading `gradP` is the T1 amplitude at the open-line parameters with
`δ₃ = e⁴ d₃(1)` (`QED.GradedProof.regulatedAmplitude_eq_of_grading`, then the open-line reduction
of `QED/GradedProof/X0OneCtCrit.lean`). The one-loop test `OneCrit` of its line data holds (kernel
evaluation): two loop fermion lines, two loop photon lines and a `photonCt` vertex of degree `2`,
so `d = 4` and `4 + d = 8 < 12 = 2 n`. Hence (T₉′) for `ε > 0`, any masses and any counterterm
data (`QED.GradedProof.X0.jointEnergyFirstIntegrable_oneCt`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALink

open QED.WickModel QED.ChainProof.Enum

/-- The open-line parameters with the level-`1` photon counterterm. -/
def ctParamsP (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) :
    Params :=
  { QED.GradedProof.X0.openCtParams P Φ D with δ₃ := P.e ^ 4 * D.d₃ 1 }

theorem repP_cycle (s : Fin 2) : ∀ x, Equiv.Perm.SameCycle (repP s).1.1 x (.inl 0) := by
  obtain ⟨f0, f1, f2, f3⟩ := repP_fst s
  have h2 : (repP s).1.1.SameCycle (.inr (fv kP 2)) (.inl 0) :=
    (sameCycle_of_eq f0).symm
  have h1 : (repP s).1.1.SameCycle (.inr (fv kP 1)) (.inl 0) :=
    (sameCycle_of_eq f3).symm.trans h2
  have h0 : (repP s).1.1.SameCycle (.inr (fv kP 0)) (.inl 0) :=
    (sameCycle_of_eq f2).symm.trans h1
  intro x
  rcases kP_fields x with rfl | rfl | rfl | rfl
  exacts [Equiv.Perm.SameCycle.refl _ _, h0, h1, h2]

theorem oneCrit_repP : ∀ s, QED.GradedProof.X0.OneCrit
    (QED.TwoLoop.Enumeration.lineData (repP s)) kP := by
  decide +kernel

theorem kP_ct : ∀ t : Graded.CtVertex kP, kP t.1 = .photonCt := by decide

open scoped Classical in
/-- The graded amplitude of `repP s` at `gradP` is the T1 amplitude at `ctParamsP`. -/
theorem regulatedAmplitude_repP (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (s : Fin 2)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (k : Line (repP s) → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.regulatedAmplitude P Φ D (repP s) gradP pIn kIn k αOut βIn μ =
      contractionAmplitude₂ (ctParamsP P Φ D) (repP s)
        (QED.TwoLoop.Insertion.zeroFlavoring kP) pIn kIn k αOut βIn μ := by
  have hcyc := repP_cycle s
  have hct : QED.GradedProof.CtReaches (repP s) := fun t _ => ⟨0, (hcyc _).symm⟩
  rw [QED.GradedProof.regulatedAmplitude_eq_of_grading P (ctParamsP P Φ D) Φ D (repP s) hct
      gradP rfl rfl rfl rfl (fun t h => absurd ((kP_ct t).symm.trans h) (by decide))
      (fun t h => absurd ((kP_ct t).symm.trans h) (by decide)) (fun _ _ => rfl),
    QED.Lepton.Proof.HM.regulatedAmplitude₂_of_not_hasLoop _ _
      (QED.GradedProof.X0.isSimple_of_cycle hcyc) (QED.GradedProof.X0.not_hasLoop_of_cycle hcyc)]
  exact QED.GradedProof.X0.loopAmp_eq_contractionAmplitude₂ _ _ _ rfl _ _ _ _ _ _

/-- **The class obligation for the `photonCt` classes.** -/
theorem classIntA_repP (s : Fin 2) : ClassIntA (repP s) gradP := by
  intro P F _ _ Φ D rep hH pOut pIn kIn _ αOut βIn μ
  have hL := loopCount_repP s
  obtain ⟨hd, hn⟩ := QED.GradedProof.X0.oneCrit_bounds (oneCrit_repP s)
  rw [hL]
  simp only [regulatedAmplitude_repP, QED.GradedProof.X0.lineMomentum₂_eq_oneMom]
  exact QED.GradedProof.X0.jointEnergyFirstIntegrable_oneCt (ctParamsP P Φ D) hH.hε (repP s) _ _
    _ hd hn pIn kIn αOut βIn μ _

end QED.ChainProof.SetALink

end
