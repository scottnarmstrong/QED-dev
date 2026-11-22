/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkInt
public import QED.GradedProof.X0OneCtCrit
public import QED.GradedProof.VertexTwo
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# The class obligations of (HS₀) for the one-loop classes `S0`–`S4` and `CD2`–`CD4`

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58): the class obligations `ClassIntA` for the five VP-share counterterm graphs
`repS0`, …, `repS4` (one level-`1` counterterm on the open line of the one-loop vertex) and for
the six one-loop graphs `repCD2 s`, `repCD3 s`, `repCD4 s` (a level-`0` `gaugeCt` vertex on the
open line and a level-`0` `photonCt` vertex on the photon line).

## Proof

All fermion fields lie on the cycle of the external field and the grading is constant (`n = 1`
for the `S` classes, `n = 0` for the `CD` classes), so the graded integrand is the T1 amplitude at
the open-line parameters with the level-`n` counterterms `e^{2(n+1)} d(n)`
(`QED.GradedProof.regulatedAmplitude_eq_of_grading`, then the open-line reduction of
`QED/GradedProof/X0OneCtCrit.lean`): `regulatedAmplitude_eq_ctLevel`. The one-loop test
`OneCrit` of the line data holds (kernel evaluation):

* `S0`, `S1`: three loop fermion lines, one loop photon line, a `fermionCt` vertex of degree
  `1`: `d = 4`, `4 + d = 8 < 10 = 2 n`;
* `S2`–`S4`: two loop fermion lines, one loop photon line: `d = 2`, `6 < 8`;
* `CD2`–`CD4`: two loop fermion lines, two loop photon lines, a `photonCt` vertex of degree `2`:
  `d = 4`, `8 < 12`.

Hence (T₉′) for `ε > 0`, any masses and any counterterm data
(`QED.GradedProof.X0.jointEnergyFirstIntegrable_oneCt`): `classIntA_of_openLine`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.ChainProof.SetALink
open QED.TwoLoop.Enumeration (lineData loopCount_eq_card)

/-- The open-line parameters with the level-`n` counterterms. -/
def ctParamsLevel (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Graded.Counterterms F)
    (n : ℕ) : Params :=
  { P with
    δ₁ := P.e ^ (2 * (n + 1)) * D.d₁ Φ.openLine n
    δ₂ := P.e ^ (2 * (n + 1)) * D.d₂ Φ.openLine n
    δm := P.e ^ (2 * (n + 1)) * D.dm Φ.openLine n
    δ₃ := P.e ^ (2 * (n + 1)) * D.d₃ n
    m := Φ.mass Φ.openLine }

open scoped Classical in
/-- **The graded integrand of an open-line contraction at a constant grading** `n` is the T1
amplitude at the open-line parameters with the level-`n` counterterms. -/
theorem regulatedAmplitude_eq_ctLevel (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (n : ℕ)
    (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.regulatedAmplitude P Φ D C (fun _ => n) pIn kIn k αOut βIn μ =
      contractionAmplitude₂ (ctParamsLevel P Φ D n) C
        (QED.TwoLoop.Insertion.zeroFlavoring κ) pIn kIn k αOut βIn μ := by
  have hct : QED.GradedProof.CtReaches C := fun t _ => ⟨0, (hcyc _).symm⟩
  rw [QED.GradedProof.regulatedAmplitude_eq_of_grading P (ctParamsLevel P Φ D n) Φ D C hct
      (fun _ => n) rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩)
      (fun _ _ => rfl),
    QED.Lepton.Proof.HM.regulatedAmplitude₂_of_not_hasLoop _ _
      (QED.GradedProof.X0.isSimple_of_cycle hcyc) (QED.GradedProof.X0.not_hasLoop_of_cycle hcyc)]
  exact QED.GradedProof.X0.loopAmp_eq_contractionAmplitude₂ _ _ _ rfl _ _ _ _ _ _

/-- **The class obligation for a one-loop open-line contraction passing `OneCrit`**, at a
constant grading. -/
theorem classIntA_of_openLine {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (n : ℕ) (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hL : loopCount C = 1)
    (hcrit : QED.GradedProof.X0.OneCrit (lineData C) κ) : ClassIntA C (fun _ => n) := by
  intro P F _ _ Φ D rep hH pOut pIn kIn _ αOut βIn μ
  obtain ⟨hd, hn⟩ := QED.GradedProof.X0.oneCrit_bounds hcrit
  rw [hL]
  simp only [regulatedAmplitude_eq_ctLevel P Φ D C hcyc n,
    QED.GradedProof.X0.lineMomentum₂_eq_oneMom]
  exact QED.GradedProof.X0.jointEnergyFirstIntegrable_oneCt (ctParamsLevel P Φ D n) hH.hε C _ _
    _ hd hn pIn kIn αOut βIn μ _

/-! ### The VP-share counterterm graphs `S0`–`S4` -/

theorem cycle_repS0 : ∀ x, Equiv.Perm.SameCycle repS0.1.1 x (.inl 0) := by decide +kernel

theorem cycle_repS1 : ∀ x, Equiv.Perm.SameCycle repS1.1.1 x (.inl 0) := by decide +kernel

theorem cycle_repS2 : ∀ x, Equiv.Perm.SameCycle repS2.1.1 x (.inl 0) := by decide +kernel

theorem cycle_repS3 : ∀ x, Equiv.Perm.SameCycle repS3.1.1 x (.inl 0) := by decide +kernel

theorem cycle_repS4 : ∀ x, Equiv.Perm.SameCycle repS4.1.1 x (.inl 0) := by decide +kernel

theorem loopCount_repS : loopCount repS0 = 1 ∧ loopCount repS1 = 1 ∧ loopCount repS2 = 1 ∧
    loopCount repS3 = 1 ∧ loopCount repS4 = 1 := by
  simp only [loopCount_eq_card]
  decide +kernel

theorem oneCrit_repS : QED.GradedProof.X0.OneCrit (lineData repS0) kS0 ∧
    QED.GradedProof.X0.OneCrit (lineData repS1) kS1 ∧
    QED.GradedProof.X0.OneCrit (lineData repS2) kS2 ∧
    QED.GradedProof.X0.OneCrit (lineData repS3) kS3 ∧
    QED.GradedProof.X0.OneCrit (lineData repS4) kS4 := by
  decide +kernel

/-- **The class obligation for `S0`.** -/
theorem classIntA_repS0 : ClassIntA repS0 (gOne _) :=
  classIntA_of_openLine repS0 1 cycle_repS0 loopCount_repS.1 oneCrit_repS.1

/-- **The class obligation for `S1`.** -/
theorem classIntA_repS1 : ClassIntA repS1 (gOne _) :=
  classIntA_of_openLine repS1 1 cycle_repS1 loopCount_repS.2.1 oneCrit_repS.2.1

/-- **The class obligation for `S2`.** -/
theorem classIntA_repS2 : ClassIntA repS2 (gOne _) :=
  classIntA_of_openLine repS2 1 cycle_repS2 loopCount_repS.2.2.1 oneCrit_repS.2.2.1

/-- **The class obligation for `S3`.** -/
theorem classIntA_repS3 : ClassIntA repS3 (gOne _) :=
  classIntA_of_openLine repS3 1 cycle_repS3 loopCount_repS.2.2.2.1 oneCrit_repS.2.2.2.1

/-- **The class obligation for `S4`.** -/
theorem classIntA_repS4 : ClassIntA repS4 (gOne _) :=
  classIntA_of_openLine repS4 1 cycle_repS4 loopCount_repS.2.2.2.2 oneCrit_repS.2.2.2.2

/-! ### The `gaugeCt`–`δ₃` graphs `CD2`–`CD4` -/

theorem cycle_repCD2 : ∀ s x, Equiv.Perm.SameCycle (repCD2 s).1.1 x (.inl 0) := by
  decide +kernel

theorem cycle_repCD3 : ∀ s x, Equiv.Perm.SameCycle (repCD3 s).1.1 x (.inl 0) := by
  decide +kernel

theorem cycle_repCD4 : ∀ s x, Equiv.Perm.SameCycle (repCD4 s).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_repCD : (∀ s, loopCount (repCD2 s) = 1) ∧ (∀ s, loopCount (repCD3 s) = 1) ∧
    ∀ s, loopCount (repCD4 s) = 1 := by
  simp only [loopCount_eq_card]
  decide +kernel

theorem oneCrit_repCD : (∀ s, QED.GradedProof.X0.OneCrit (lineData (repCD2 s)) kCD2) ∧
    (∀ s, QED.GradedProof.X0.OneCrit (lineData (repCD3 s)) kCD3) ∧
    ∀ s, QED.GradedProof.X0.OneCrit (lineData (repCD4 s)) kCD4 := by
  decide +kernel

/-- **The class obligation for `CD2`.** -/
theorem classIntA_repCD2 (s : Fin 2) : ClassIntA (repCD2 s) 0 :=
  classIntA_of_openLine (repCD2 s) 0 (cycle_repCD2 s) (loopCount_repCD.1 s)
    (oneCrit_repCD.1 s)

/-- **The class obligation for `CD3`.** -/
theorem classIntA_repCD3 (s : Fin 2) : ClassIntA (repCD3 s) 0 :=
  classIntA_of_openLine (repCD3 s) 0 (cycle_repCD3 s) (loopCount_repCD.2.1 s)
    (oneCrit_repCD.2.1 s)

/-- **The class obligation for `CD4`.** -/
theorem classIntA_repCD4 (s : Fin 2) : ClassIntA (repCD4 s) 0 :=
  classIntA_of_openLine (repCD4 s) 0 (cycle_repCD4 s) (loopCount_repCD.2.2 s)
    (oneCrit_repCD.2.2 s)

end QED.ChainProof.SetCLink

end
