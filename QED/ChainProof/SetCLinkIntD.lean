/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntDExt
public import QED.ChainProof.SetCLinkIntB

/-!
# Set (c), family `D`, and (HS₀)

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58). `QED.ChainProof.SetCLink.repD i s`, `i : Fin 12`, `s : Fin 2`, is a two-loop
vertex skeleton with a `photonCt` vertex on a photon line: two loops, grading `0`, no closed
fermion loop.

* `classIntA_of_data`: the class obligation of a `kD` contraction from decidable data: a
  counterterm photon line for the `k·k g` part (`GData`) and either a Ward identity at an
  internal vertex (`WardData`) or one-sided Ward identities at both ends (`ExtData`) for the
  `k_μ k_ν` part.
* **`classIntA_repD`**: the class obligations of all twenty-four orbits, the data by kernel
  evaluation.
* **`jointEnergyFirstIntegrable_setC_final`**: (HS₀), with exactly the hypotheses and
  conclusion of the frozen goal, from `RemainingC.ofB`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.GradedProof.X0 QED.Graded QED.WickModel QED.ChainProof.SetALink
open QED.ChainProof.Enum (fv pc)
open QED.TwoLoop.Enumeration (lineData loopCount_eq_card)
open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply
  photonPropagator_eq_mul)

variable {F : Type}

/-! ### The class obligations -/

/-- The data of the `k·k g` part: a counterterm photon line with its two tests. -/
def GData (C : Contraction 1 1 kD) : Prop :=
  ∃ g : PhotonLine C, (pmv C (pc kD 5 0) = mv C (.inr g) ∨ pmv C (pc kD 5 0) = -mv C (.inr g)) ∧
    PadCrit (rowOf C) (Function.update dN (.inr g) 1) dD ∧ PadCrit (rowOf C) dN dD

instance (C : Contraction 1 1 kD) : Decidable (GData C) := by unfold GData; infer_instance

/-- The data of a Ward identity at an internal vertex. -/
def WardAt (C : Contraction 1 1 kD) (fa fb : FermionLine C) (gW gK : PhotonLine C) (sW : Fin 2) :
    Prop :=
  fa.tail = fb.1 ∧ fa.1 ≠ fb.1 ∧
    fb.tail ≠ fb.1 ∧ gW ≠ gK ∧
    ((gW.1 = slD fb.1 ∧ gW.head = pc kD 5 sW) ∨ (gW.1 = pc kD 5 sW ∧ gW.head = slD fb.1)) ∧
    (∀ g : PhotonLine C, g ≠ gW → g.1 ≠ slD fb.1 ∧ g.head ≠ slD fb.1 ∧
      g.1 ≠ pc kD 5 sW ∧ g.head ≠ pc kD 5 sW) ∧
    (∀ i, C.1.1 (.inl i) ≠ .inr fb.1) ∧
    (∀ j, C.1.2 (.inl j) ≠ .inr (slD fb.1) ∧ C.1.2 (.inl j) ≠ .inr (pc kD 5 sW)) ∧
    (pmv C (pc kD 5 0) = mv C (.inl fa) - mv C (.inl fb) ∨
      pmv C (pc kD 5 0) = -(mv C (.inl fa) - mv C (.inl fb))) ∧
    (pmv C (pc kD 5 0) = mv C (.inr gK) ∨ pmv C (pc kD 5 0) = -mv C (.inr gK)) ∧
    WardCrit C fa fb gW gK

instance (C : Contraction 1 1 kD) (fa fb : FermionLine C) (gW gK : PhotonLine C) (sW : Fin 2) :
    Decidable (WardAt C fa fb gW gK sW) := by
  unfold WardAt
  repeat refine @instDecidableAnd _ _ inferInstance ?_
  infer_instance

/-- The data of a Ward identity at an internal vertex, for some lines. -/
def WardData (C : Contraction 1 1 kD) : Prop :=
  ∃ fa fb : FermionLine C, ∃ gW gK : PhotonLine C, ∃ sW : Fin 2, WardAt C fa fb gW gK sW

instance (C : Contraction 1 1 kD) : Decidable (WardData C) := by
  unfold WardData; infer_instance

/-- The data of one-sided Ward identities at both ends. -/
def ExtAt (C : Contraction 1 1 kD) (f0 f3 : FermionLine C) (gW gK : PhotonLine C) (sW : Fin 2) :
    Prop :=
  f0.1 ≠ f3.tail ∧ f0 ≠ f3 ∧
    gW ≠ gK ∧
    ((gW.1 = slD f0.1 ∧ gW.head = pc kD 5 sW) ∨ (gW.1 = pc kD 5 sW ∧ gW.head = slD f0.1)) ∧
    ((gK.1 = slD f3.tail ∧ gK.head = pc kD 5 sW.rev) ∨
      (gK.1 = pc kD 5 sW.rev ∧ gK.head = slD f3.tail)) ∧
    (∀ i, C.1.1 (.inl i) ≠ .inr f3.tail) ∧
    (ExtSlots C gW gK (slD f0.1) ∧ ExtSlots C gW gK (pc kD 5 sW) ∧
      ExtSlots C gW gK (slD f3.tail) ∧ ExtSlots C gW gK (pc kD 5 sW.rev)) ∧
    (pmv C (pc kD 5 0) = ![0, 0, 1, 1] - mv C (.inl f0) ∨
      pmv C (pc kD 5 0) = -(![0, 0, 1, 1] - mv C (.inl f0))) ∧
    (pmv C (pc kD 5 0) = mv C (.inl f3) - ![0, 0, 1, 0] ∨
      pmv C (pc kD 5 0) = -(mv C (.inl f3) - ![0, 0, 1, 0])) ∧
    ExtCrit C f0 f3 gW gK

instance (C : Contraction 1 1 kD) (f0 f3 : FermionLine C) (gW gK : PhotonLine C) (sW : Fin 2) :
    Decidable (ExtAt C f0 f3 gW gK sW) := by
  unfold ExtAt
  repeat refine @instDecidableAnd _ _ inferInstance ?_
  infer_instance

/-- The data of one-sided Ward identities at both ends, for some lines. -/
def ExtData (C : Contraction 1 1 kD) : Prop :=
  ∃ f0 f3 : FermionLine C, ∃ gW gK : PhotonLine C, ∃ sW : Fin 2, ExtAt C f0 f3 gW gK sW

instance (C : Contraction 1 1 kD) : Decidable (ExtData C) := by
  unfold ExtData; infer_instance

/-- **The class obligation of a `kD` contraction** from the data of both parts. -/
theorem classIntA_of_data (C : Contraction 1 1 kD)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hL : loopCount C = 2)
    (hG : GData C) (hK : WardData C ∨ ExtData C) : ClassIntA C 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn hmom αOut βIn μ
  rw [hL]
  refine QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul _ ?_
  obtain ⟨g, hρ, h₀, h₁⟩ := hG
  have hA := jointEnergyFirstIntegrable_ctG P Φ hH.hε (P.e ^ 2 * D.d₃ 0) C pOut pIn kIn hmom
    αOut βIn μ g hρ h₀ h₁
  have hB : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => ∑ α, ∑ β, ∑ lor,
      extI C αOut βIn μ α β lor *
        (ctKD (P.e ^ 2 * D.d₃ 0) lor
          (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
          (gV P.e α β lor *
            lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ))) := by
    rcases hK with ⟨fa, fb, gW, gK, sW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ |
      ⟨f0, f3, gW, gK, sW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · exact jointEnergyFirstIntegrable_ctK_ward P Φ hH.hε _ C pOut pIn kIn hmom αOut βIn μ fa fb
        gW gK sW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    · exact jointEnergyFirstIntegrable_ctK_ext P Φ hH.hε _ C pOut pIn kIn hmom αOut βIn μ f0 f3
        gW gK sW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  refine (congrArg _ (funext fun ℓ => ?_)).mpr
    (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add hA hB)
  rw [regulatedAmplitude_kD P Φ D hH.hε.ne' C hcyc]
  simp only [ctF_eq, add_mul, mul_add, Finset.sum_add_distrib]

/-! ### The twenty-four orbits -/

theorem cycle_repD : ∀ i s x, Equiv.Perm.SameCycle (repD i s).1.1 x (.inl 0) := by
  decide +kernel

theorem loopCount_repD (i : Fin 12) (s : Fin 2) : loopCount (repD i s) = 2 := by
  rw [loopCount_eq_card]
  revert i s
  decide +kernel

theorem data_repD : ∀ i s, GData (repD i s) ∧ (WardData (repD i s) ∨ ExtData (repD i s)) := by
  decide +kernel

/-- **The class obligations of the family `D`** (twenty-four orbits). -/
theorem classIntA_repD (i : Fin 12) (s : Fin 2) : ClassIntA (repD i s) 0 :=
  classIntA_of_data _ (cycle_repD i s) (loopCount_repD i s) (data_repD i s).1 (data_repD i s).2

/-! ### (HS₀) -/

/-- **(HS₀)**, with exactly the hypotheses and conclusion of
`QED.ThreeLoop.jointEnergyFirstIntegrable_setC`. -/
theorem jointEnergyFirstIntegrable_setC_final
    (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Graded.Grading κ)
    (hg : Graded.gradedOrder κ g = 7) (C : Contraction 1 1 κ) (hC₁ : IsOnePI C)
    (hC : QED.ThreeLoop.IsSetC C g)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ :=
  jointEnergyFirstIntegrable_setC_of_remaining
    (RemainingC.ofB classIntA_repD classIntA_repCB0 classIntA_repCB1
      SetCLinkDeg6.classIntA_repCD0 SetCLinkDeg6.classIntA_repCD1)
    P Φ D rep hε hrep hPV₁ hPV₂ hD g hg C hC₁ hC pOut pIn kIn hmom αOut βIn μ

end QED.ChainProof.SetCLink

end
