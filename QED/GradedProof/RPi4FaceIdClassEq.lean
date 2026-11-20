/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdComb
public import QED.GradedProof.RPi4FaceIdAsm

/-!
# (R-Π₄) step L6d3: the class-level face integral as one-loop classes

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. At `ε > 0`,
`faceIdClassPsi = λ ∫ (F0 + F1 + 2 G)(faceIdD₀) + iε (padded defects of VA, VC)`:

* `faceId_ef_add_right`: integrability in both stages is translation invariant;
* `faceId_combine`, **`faceId_classPsi_eq`**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

theorem faceId_ef_add_right {G : (Fin 4 → ℝ) → ℂ} (h : EF G) (c : Fin 4 → ℝ) :
    EF fun x => G (x + c) := by
  have e : ∀ (t : ℝ) (v : Fin 3 → ℝ),
      (Fin.cons t v : Fin 4 → ℝ) + c = Fin.cons (t + c 0) (v + Fin.tail c) := by
    intro t v
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
  refine ⟨fun v => ?_, ?_⟩
  · simp only [e]
    exact (h.1 _).comp_add_right (c 0)
  · simp only [e]
    have i : ∀ v : Fin 3 → ℝ, (∫ t : ℝ, G (Fin.cons (t + c 0) (v + Fin.tail c))) =
        ∫ t : ℝ, G (Fin.cons t (v + Fin.tail c)) := fun v =>
      integral_add_right_eq_self (fun t => G (Fin.cons t (v + Fin.tail c))) (c 0)
    simp only [i]
    exact h.2.comp_add_right (Fin.tail c)

/-- The combination of the class integrals, the loop-`0` face of `VB` translated by `k`. -/
theorem faceId_combine {A B₁ B₀ C S : (Fin 4 → ℝ) → ℂ} (pa pc L : ℂ) (hA : EF A) (hB₁ : EF B₁)
    (hB₀ : EF B₀) (hC : EF C) (k : Fin 4 → ℝ)
    (hS : ∀ x, A x + C x + B₁ x + B₀ (x + k) = L * S x) :
    (QED.OneLoop.energyFirstIntegral A + pa) +
        (QED.OneLoop.energyFirstIntegral B₁ + QED.OneLoop.energyFirstIntegral B₀) +
        (QED.OneLoop.energyFirstIntegral C + pc) =
      L * QED.OneLoop.energyFirstIntegral S + (pa + pc) := by
  rw [← QED.OneLoop.energyFirstIntegral_add_right_eq_self B₀ k,
    ← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul, ← funext hS,
    efi_add ((hA.add hC).add hB₁) (faceId_ef_add_right hB₀ k), efi_add (hA.add hC) hB₁,
    efi_add hA hC]
  ring

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e : ℝ) (k : Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε)
include hm₀ hmass hrep hPV₁ hPV₂ hε

/-- **The class-level face integral as one-loop classes** at `ε > 0`. -/
theorem faceId_classPsi_eq :
    faceIdClassPsi Φ e m₀ k ε =
      faceIdLam * QED.OneLoop.energyFirstIntegral (fun x =>
        fBubble (faceIdParams e) Φ (faceIdD₀ F) rep true true false ε k x 2 3 +
        fBubble (faceIdParams e) Φ (faceIdD₀ F) rep false false true ε k x 2 3 +
        2 * gBubble { faceIdParams e with ε := ε } Φ (faceIdD₀ F) rep k x 2 3) +
      ((∑ f, (Φ.coeff f : ℂ) * (ε * I * QED.OneLoop.energyFirstIntegral
        (faceIdFP (faceIdRB baseVA ![1, 0]) cVA ε k (fun _ =>
          ((blockX Φ m₀ : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) *
            (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) * vNumE4 e 0 1 aVA k 2 3)
          (blockX Φ m₀ + 1)))) +
      (∑ f, (Φ.coeff f : ℂ) * (ε * I * QED.OneLoop.energyFirstIntegral
        (faceIdFP (faceIdRB baseVC ![1, 0]) cVC ε k (fun _ =>
          ((blockX Φ m₀ : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) *
            (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) * vNumE4 e 0 1 aVC k 2 3)
          (blockX Φ m₀ + 1))))) := by
  obtain ⟨hA, eA⟩ := faceId_blockPsi_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ e k 2 3 hε
  obtain ⟨hC, eC⟩ := faceId_blockPsi_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ e k 2 3 hε
  obtain ⟨hB, eB₁, eB₀⟩ := faceId_blockPsi_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ e k 2 3 hε
  rw [faceIdClassPsi, hA, hB, hC]
  exact faceId_combine _ _ _ eA eB₁ eB₀ eC k
    (fun x => faceId_faces_eq_bubbles Φ rep e ε k x 2 3)

end QED.GradedProof.RPi4

end
