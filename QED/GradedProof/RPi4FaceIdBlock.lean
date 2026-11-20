/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdFlav

/-!
# (R-Π₄) step L6d3: the block-summed classes at the faces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. At `ε > 0` the
block-summed face integral `faceIdBlockPsi` of each class is the energy-first integral of the
flavour sum `∑_f c_f H(M_f)` of the face integrand at the physical masses (the regulator flavours
`X`, `X + 1` drop out), plus, for `VA` and `VC`, `iε` times the padded defects:

* **`faceId_blockPsi_VA`**, **`faceId_blockPsi_VC`**, **`faceId_blockPsi_VB`** (the half
  Laplacians of the `VB` numerator as bubble traces, `faceId_half_lapF_VB_one`/`_zero`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) {ε : ℝ} (hε : 0 < ε)
include hm₀ hmass hrep hPV₁ hPV₂ hε

/-- **The block-summed class `VA` at its face.** -/
theorem faceId_blockPsi_VA :
    faceIdBlockPsi baseVA cVA (vNum e 0 1 aVA baseVA cVA) (vNumE4 e 0 1 aVA) Φ m₀ 0 k μ ν ε =
      QED.OneLoop.energyFirstIntegral (fun x => ∑ f, (Φ.coeff f : ℂ) *
        (vNum e 0 1 aVA baseVA cVA (Φ.mass f) k ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)] μ ν *
          ∏ l, faceIdG (faceIdRB baseVA ![1, 0] l) (faceIdV cVA ε k x l)
            ((Φ.mass f : ℂ) ^ 2))) +
      ∑ f, (Φ.coeff f : ℂ) * (ε * I * QED.OneLoop.energyFirstIntegral
        (faceIdFP (faceIdRB baseVA ![1, 0]) cVA ε k (fun _ =>
          ((blockX Φ m₀ : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) *
            (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) * vNumE4 e 0 1 aVA k μ ν)
          (blockX Φ m₀ + 1))) ∧
    EF (fun x => ∑ f, (Φ.coeff f : ℂ) *
        (vNum e 0 1 aVA baseVA cVA (Φ.mass f) k ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)] μ ν *
          ∏ l, faceIdG (faceIdRB baseVA ![1, 0] l) (faceIdV cVA ε k x l)
            ((Φ.mass f : ℂ) ^ 2))) := by
  have hT := fun f => faceId_triPsi_VA (vNum e 0 1 aVA baseVA cVA)
    (fun ℓ => vNumE0 e 0 1 aVA baseVA cVA k ℓ μ ν) (fun ℓ => vNumE2 e 0 1 aVA baseVA cVA k ℓ μ ν)
    (vNumE4 e 0 1 aVA) k μ ν hε (fun m ℓ => faceId_lapF_vNum_VA e 0 1 m k μ ν ℓ)
    (fun m ℓ => vNum_eq e 0 1 aVA baseVA cVA (fun a b ρ σ => isOddG_aVA a b ρ σ) m k ℓ μ ν)
    (fun m => isLoopPoly_vNum e 0 1 aVA baseVA cVA m k μ ν)
    (isLoopPoly_vNumE2 e 0 1 aVA baseVA cVA k μ ν)
    (faceId_mass_sq_ne Φ hm₀ hmass f).1 (faceId_mass_sq_ne Φ hm₀ hmass f).2.1
    (faceId_mass_sq_ne Φ hm₀ hmass f).2.2
  exact faceId_sum_efi Φ
    (fun M => faceIdTriF (faceIdRB baseVA ![1, 0]) cVA ε k
      (fun m x => vNum e 0 1 aVA baseVA cVA m k ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)] μ ν) M
      (blockX Φ m₀) (blockX Φ m₀ + 1))
    (fun M x => vNum e 0 1 aVA baseVA cVA M k ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)] μ ν *
      ∏ l, faceIdG (faceIdRB baseVA ![1, 0] l) (faceIdV cVA ε k x l) ((M : ℂ) ^ 2))
    (fun M => ε * I * QED.OneLoop.energyFirstIntegral
        (faceIdFP (faceIdRB baseVA ![1, 0]) cVA ε k (fun _ =>
          ((blockX Φ m₀ : ℂ) ^ 2 - (M : ℂ) ^ 2) *
            (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (M : ℂ) ^ 2) * vNumE4 e 0 1 aVA k μ ν)
          (blockX Φ m₀ + 1)))
    (fun M => faceIdTriPsi baseVA cVA (vNum e 0 1 aVA baseVA cVA) (vNumE4 e 0 1 aVA) M
      (blockX Φ m₀) (blockX Φ m₀ + 1) 0 k μ ν ε) (fun f => (hT f).1) (fun f => (hT f).2)
    (faceId_sum_triF Φ rep hrep hPV₁ hPV₂ _ _ _ _ _ _ _)

/-- **The block-summed class `VC` at its face.** -/
theorem faceId_blockPsi_VC :
    faceIdBlockPsi baseVC cVC (vNum e 0 1 aVC baseVC cVC) (vNumE4 e 0 1 aVC) Φ m₀ 1 k μ ν ε =
      QED.OneLoop.energyFirstIntegral (fun x => ∑ f, (Φ.coeff f : ℂ) *
        (vNum e 0 1 aVC baseVC cVC (Φ.mass f) k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν *
          ∏ l, faceIdG (faceIdRB baseVC ![1, 0] l) (faceIdV cVC ε k x l)
            ((Φ.mass f : ℂ) ^ 2))) +
      ∑ f, (Φ.coeff f : ℂ) * (ε * I * QED.OneLoop.energyFirstIntegral
        (faceIdFP (faceIdRB baseVC ![1, 0]) cVC ε k (fun _ =>
          ((blockX Φ m₀ : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) *
            (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) * vNumE4 e 0 1 aVC k μ ν)
          (blockX Φ m₀ + 1))) ∧
    EF (fun x => ∑ f, (Φ.coeff f : ℂ) *
        (vNum e 0 1 aVC baseVC cVC (Φ.mass f) k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν *
          ∏ l, faceIdG (faceIdRB baseVC ![1, 0] l) (faceIdV cVC ε k x l)
            ((Φ.mass f : ℂ) ^ 2))) := by
  have hT := fun f => faceId_triPsi_VC (vNum e 0 1 aVC baseVC cVC)
    (fun ℓ => vNumE0 e 0 1 aVC baseVC cVC k ℓ μ ν) (fun ℓ => vNumE2 e 0 1 aVC baseVC cVC k ℓ μ ν)
    (vNumE4 e 0 1 aVC) k μ ν hε (fun m ℓ => faceId_lapF_vNum_VC e 0 1 m k μ ν ℓ)
    (fun m ℓ => vNum_eq e 0 1 aVC baseVC cVC (fun a b ρ σ => isOddG_aVC a b ρ σ) m k ℓ μ ν)
    (fun m => isLoopPoly_vNum e 0 1 aVC baseVC cVC m k μ ν)
    (isLoopPoly_vNumE2 e 0 1 aVC baseVC cVC k μ ν)
    (faceId_mass_sq_ne Φ hm₀ hmass f).1 (faceId_mass_sq_ne Φ hm₀ hmass f).2.1
    (faceId_mass_sq_ne Φ hm₀ hmass f).2.2
  exact faceId_sum_efi Φ
    (fun M => faceIdTriF (faceIdRB baseVC ![1, 0]) cVC ε k
      (fun m x => vNum e 0 1 aVC baseVC cVC m k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν) M
      (blockX Φ m₀) (blockX Φ m₀ + 1))
    (fun M x => vNum e 0 1 aVC baseVC cVC M k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν *
      ∏ l, faceIdG (faceIdRB baseVC ![1, 0] l) (faceIdV cVC ε k x l) ((M : ℂ) ^ 2))
    (fun M => ε * I * QED.OneLoop.energyFirstIntegral
        (faceIdFP (faceIdRB baseVC ![1, 0]) cVC ε k (fun _ =>
          ((blockX Φ m₀ : ℂ) ^ 2 - (M : ℂ) ^ 2) *
            (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (M : ℂ) ^ 2) * vNumE4 e 0 1 aVC k μ ν)
          (blockX Φ m₀ + 1)))
    (fun M => faceIdTriPsi baseVC cVC (vNum e 0 1 aVC baseVC cVC) (vNumE4 e 0 1 aVC) M
      (blockX Φ m₀) (blockX Φ m₀ + 1) 1 k μ ν ε) (fun f => (hT f).1) (fun f => (hT f).2)
    (faceId_sum_triF Φ rep hrep hPV₁ hPV₂ _ _ _ _ _ _ _)

/-- **The block-summed class `VB` at its two faces.** -/
theorem faceId_blockPsi_VB :
    faceIdBlockPsi baseVB cVB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) Φ m₀ 0 k μ ν ε =
      QED.OneLoop.energyFirstIntegral (fun x => ∑ f, (Φ.coeff f : ℂ) *
        ((faceIdKV e 0 1 * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk k false x) (zk k true x) +
            (Φ.mass f : ℂ) ^ 2 * (faceIdKV e 0 1 * (Dirac.gamma μ * Dirac.gamma ν).trace)) *
          ∏ l, faceIdG (faceIdRB baseVB ![1, 0] l) (faceIdV cVB ε k x l) ((Φ.mass f : ℂ) ^ 2))) +
      QED.OneLoop.energyFirstIntegral (fun x => ∑ f, (Φ.coeff f : ℂ) *
        ((faceIdKV e 0 1 * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk (-k) true x)
            (zk k false x) +
            (Φ.mass f : ℂ) ^ 2 * (faceIdKV e 0 1 * (Dirac.gamma μ * Dirac.gamma ν).trace)) *
          ∏ l, faceIdG (faceIdRB baseVB ![0, 1] l) (faceIdV cVB ε k x l) ((Φ.mass f : ℂ) ^ 2))) ∧
    EF (fun x => ∑ f, (Φ.coeff f : ℂ) *
        ((faceIdKV e 0 1 * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk k false x) (zk k true x) +
            (Φ.mass f : ℂ) ^ 2 * (faceIdKV e 0 1 * (Dirac.gamma μ * Dirac.gamma ν).trace)) *
          ∏ l, faceIdG (faceIdRB baseVB ![1, 0] l) (faceIdV cVB ε k x l) ((Φ.mass f : ℂ) ^ 2))) ∧
    EF (fun x => ∑ f, (Φ.coeff f : ℂ) *
        ((faceIdKV e 0 1 * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk (-k) true x)
            (zk k false x) +
            (Φ.mass f : ℂ) ^ 2 * (faceIdKV e 0 1 * (Dirac.gamma μ * Dirac.gamma ν).trace)) *
          ∏ l, faceIdG (faceIdRB baseVB ![0, 1] l) (faceIdV cVB ε k x l)
            ((Φ.mass f : ℂ) ^ 2))) := by
  set A0 : (Fin 4 → ℝ) → ℂ := fun x =>
    faceIdKV e 0 1 * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk k false x) (zk k true x)
  set B0 : (Fin 4 → ℝ) → ℂ := fun x =>
    faceIdKV e 0 1 * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk (-k) true x) (zk k false x)
  set A2 : ℂ := faceIdKV e 0 1 * (Dirac.gamma μ * Dirac.gamma ν).trace
  set X := blockX Φ m₀
  have hT := fun f => faceId_triPsi_VB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) k μ ν hε
    A0 (fun _ => A2) B0 (fun _ => A2) (fun m x => faceId_half_lapF_VB_one e 0 1 m k μ ν x)
    (fun m x => faceId_half_lapF_VB_zero e 0 1 m k μ ν x)
    ((faceId_isLoopPoly_bubTr _ _ 0 false true k k).const_mul _) (IsLoopPoly.const _)
    ((faceId_isLoopPoly_bubTr _ _ 0 true false (-k) k).const_mul _) (IsLoopPoly.const _)
    (faceId_mass_sq_ne Φ hm₀ hmass f).1 (faceId_mass_sq_ne Φ hm₀ hmass f).2.1
    (faceId_mass_sq_ne Φ hm₀ hmass f).2.2
  have h0 := faceId_sum_efi Φ
    (fun M => faceIdTriF (faceIdRB baseVB ![0, 1]) cVB ε k
        (fun m x => B0 x + (m : ℂ) ^ 2 * A2) M X (X + 1))
    (fun M x => (B0 x + (M : ℂ) ^ 2 * A2) *
        ∏ l, faceIdG (faceIdRB baseVB ![0, 1] l) (faceIdV cVB ε k x l) ((M : ℂ) ^ 2))
    (fun _ => 0)
    (fun M => QED.OneLoop.energyFirstIntegral (faceIdTriF (faceIdRB baseVB ![0, 1]) cVB ε k
        (fun m x => B0 x + (m : ℂ) ^ 2 * A2) M X (X + 1)))
    (fun f => (add_zero _).symm) (fun f => (hT f).2.2)
    (faceId_sum_triF Φ rep hrep hPV₁ hPV₂ _ _ _ _ _ _ _)
  have h1 := faceId_sum_efi Φ
    (fun M => faceIdTriF (faceIdRB baseVB ![1, 0]) cVB ε k
        (fun m x => A0 x + (m : ℂ) ^ 2 * A2) M X (X + 1))
    (fun M x => (A0 x + (M : ℂ) ^ 2 * A2) *
        ∏ l, faceIdG (faceIdRB baseVB ![1, 0] l) (faceIdV cVB ε k x l) ((M : ℂ) ^ 2))
    (fun M => QED.OneLoop.energyFirstIntegral (faceIdTriF (faceIdRB baseVB ![0, 1]) cVB ε k
        (fun m x => B0 x + (m : ℂ) ^ 2 * A2) M X (X + 1)))
    (fun M => faceIdTriPsi baseVB cVB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) M
      X (X + 1) 0 k μ ν ε)
    (fun f => (hT f).1) (fun f => (hT f).2.1)
    (faceId_sum_triF Φ rep hrep hPV₁ hPV₂ _ _ _ _ _ _ _)
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at h0
  refine ⟨?_, h1.2, h0.2⟩
  rw [← h0.1]
  exact h1.1

end QED.GradedProof.RPi4

end
