/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestP
public import QED.GradedProof.VP2Weights
public import QED.ChainProof.SetALinkVertex

/-!
# Set (a), obligation (N): the family vertex in nested form from the loop classes

Helper level for the set (a) headline (HA₆), obligation (N) of
`QED.ChainProof.SetAPauli.SetALimitLink`.

* `LoopNested P Φ D C X p' p`: the nested form of a loop class with inner photon tensor `X`
  (value = energy-first integral of `nestInt X`, integrable in both stages).
* **`familyVertex_setA_eq_nested`**: from the nested forms of the seven loop classes
  (`VA`, `VB`, `VC`, `GW`, `GU`, `FA`, `FB`, `familyVertex_setA_eq_classes`) with tensors summing
  to `-i` times the seven two-photon class values of `Π⁽⁴⁾`, every entry of the set (a) family
  vertex at `ε > 0` is `(1/i) ∫ nestInt Π⁽⁴⁾_ε`, `Π⁽⁴⁾ = vacuumPolarizationPart … 2`, and the
  integrand is integrable in both stages. The `photonCt` classes give the tree term of `Π⁽⁴⁾`
  (`contractionValue_repP_add`). With T★ᵤ the integrand is `saOuterTensor` sandwiched, the input
  of `QED.ChainProof.SetASpec.saOuterForm_list`.

The seven `LoopNested` obligations (Wick factorization, routing change and three-loop Fubini) and
the class matching `hsum` remain open.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.OneLoop QED.TwoLoop.VPUnitNested QED.TwoLoop.Insertion QED.ChainProof.SetALink
open QED.WickModel

/-- **The nested form of a loop class** at the parameters `P`: for every entry, the outer
integrand of the photon tensor `X` is integrable in both stages, and the value (G₅) of `C` at the
zero grading is its energy-first integral. For the seven loop classes of set (a), `X` is
expected to be `(1/i)` times the value of the matching two-photon class of
`QED.GradedProof.VP2.vacuumPolarizationPart_two_eq` (`sumX` below). -/
def LoopNested (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Graded.Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (X : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (p' p : Fin 4 → ℝ) : Prop :=
  ∀ μ i j : Fin 4, EFInt (nestInt P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p X μ i j) ∧
    Graded.contractionValue P Φ D C 0 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      energyFirstIntegral (nestInt P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p X μ i j)

theorem efi_sub {F G : (Fin 4 → ℝ) → ℂ} (hF : EFInt F) (hG : EFInt G) :
    energyFirstIntegral (fun ℓ => F ℓ + (-1) * G ℓ) =
      energyFirstIntegral F - energyFirstIntegral G := by
  rw [efi_add hF (hG.const_mul _), efi_const_mul]
  ring

/-- **The set (a) vertex in nested form, from the seven loop classes.** At parameters with
`ε > 0`, on-shell positive-energy momenta for the open-line mass and `0 < m_γ ≤ Λ`: if each loop
class `R` is in nested form with a photon tensor `X_R` (`LoopNested`), and the seven tensors sum
to `-i` times the seven two-photon class values of `Π⁽⁴⁾`, then every entry of the set (a) family
vertex is `(1/i)` times the energy-first integral of the outer vertex chain sandwiching
`Δ(ℓ) Π⁽⁴⁾_ε(ℓ) Δ(-ℓ)`, `Π⁽⁴⁾ = vacuumPolarizationPart … 2`, and that integrand is integrable
in both stages. The two `photonCt` classes are the tree term of `Π⁽⁴⁾`
(`contractionValue_repP_add`) with no hypothesis. -/
theorem familyVertex_setA_eq_nested (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (hε : 0 < P.ε)
    (hm : 0 < Φ.mass Φ.openLine) (hmγ : 0 < P.mγ) (hmΛ : P.mγ ≤ P.Λ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -Φ.mass Φ.openLine ^ 2)
    (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (XVA XVB XVC XGW XGU XFA XFB : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hVA : LoopNested P Φ D repVA XVA p' p) (hVB : LoopNested P Φ D repVB XVB p' p)
    (hVC : LoopNested P Φ D repVC XVC p' p) (hGW : LoopNested P Φ D repGW XGW p' p)
    (hGU : LoopNested P Φ D repGU XGU p' p) (hFA : LoopNested P Φ D repFA XFA p' p)
    (hFB : LoopNested P Φ D repFB XFB p' p)
    (hsum : ∀ ℓ a b, XVA ℓ a b + (XVB ℓ a b + (XVC ℓ a b + (XGW ℓ a b + (XGU ℓ a b +
        (XFA ℓ a b + XFB ℓ a b))))) =
      -(I * (QED.GradedProof.VP2.val0 P Φ D ℓ a b QED.GradedProof.VP2.repVA +
        QED.GradedProof.VP2.val0 P Φ D ℓ a b QED.GradedProof.VP2.repVB +
        QED.GradedProof.VP2.val0 P Φ D ℓ a b QED.GradedProof.VP2.repVC +
        QED.GradedProof.VP2.val0 P Φ D ℓ a b QED.GradedProof.VP2.repG0 +
        QED.GradedProof.VP2.val0 P Φ D ℓ a b QED.GradedProof.VP2.repG1 +
        QED.GradedProof.VP2.val0 P Φ D ℓ a b QED.GradedProof.VP2.repF0 +
        QED.GradedProof.VP2.val0 P Φ D ℓ a b QED.GradedProof.VP2.repF1)))
    (μ i j : Fin 4) :
    EFInt (nestInt P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p
        (fun ℓ a b => Graded.vacuumPolarizationPart P Φ D 2 ℓ a b) μ i j) ∧
      Graded.familyVertex P Φ D (fun C _ => IsOnePI C ∧ QED.ThreeLoop.IsSetA C) 7 p' p μ i j =
        (1 / I) * energyFirstIntegral (nestInt P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p
          (fun ℓ a b => Graded.vacuumPolarizationPart P Φ D 2 ℓ a b) μ i j) := by
  set n := nestInt P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p with hn
  set c := P.e ^ 4 * D.d₃ 1
  have hPi : (fun ℓ a b => Graded.vacuumPolarizationPart P Φ D 2 ℓ a b) =
      fun ℓ a b => nestTree c ℓ a b + (-1) * (XVA ℓ a b + (XVB ℓ a b + (XVC ℓ a b +
        (XGW ℓ a b + (XGU ℓ a b + (XFA ℓ a b + XFB ℓ a b)))))) := by
    funext ℓ a b
    rw [QED.GradedProof.VP2.vacuumPolarizationPart_two_eq, hsum ℓ a b, nestTree]
    ring
  have hfun : n (fun ℓ a b => Graded.vacuumPolarizationPart P Φ D 2 ℓ a b) μ i j = fun ℓ =>
      n (nestTree c) μ i j ℓ + (-1) * (n XVA μ i j ℓ + (n XVB μ i j ℓ + (n XVC μ i j ℓ +
        (n XGW μ i j ℓ + (n XGU μ i j ℓ + (n XFA μ i j ℓ + n XFB μ i j ℓ)))))) := by
    rw [hPi]
    funext ℓ
    simp only [hn, nestInt_add, nestInt_const_mul]
  have hT := efInt_nestInt_tree hm hmγ hmΛ hp' hp hp0' hp0 P.e c μ i j hε
  obtain ⟨iVA, vVA⟩ := hVA μ i j
  obtain ⟨iVB, vVB⟩ := hVB μ i j
  obtain ⟨iVC, vVC⟩ := hVC μ i j
  obtain ⟨iGW, vGW⟩ := hGW μ i j
  obtain ⟨iGU, vGU⟩ := hGU μ i j
  obtain ⟨iFA, vFA⟩ := hFA μ i j
  obtain ⟨iFB, vFB⟩ := hFB μ i j
  have i6 := iFA.add iFB
  have i5 := iGU.add i6
  have i4 := iGW.add i5
  have i3 := iVC.add i4
  have i2 := iVB.add i3
  have i1 := iVA.add i2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hT.add (i1.const_mul _)
  · rw [familyVertex_setA_eq_classes, Matrix.of_apply, hfun, efi_sub hT i1, efi_add iVA i2,
      efi_add iVB i3, efi_add iVC i4, efi_add iGW i5, efi_add iGU i6, efi_add iFA iFB]
    simp only
    rw [contractionValue_repP_add, vVA, vVB, vVC, vGW, vGU, vFA, vFB]
    ring

end QED.ChainProof.SetANest
