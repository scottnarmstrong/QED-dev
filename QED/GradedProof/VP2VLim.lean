/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VNum
public import QED.GradedProof.VP2WeightsZero

/-!
# The classes `VA`, `VB`, `VC`: covariant limits

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. The value of each
two-loop class (`val0`) is the joint integral of a block-summed flavour sum of loop integrands
(`val0_repVA`, `val0_repVB`, `val0_repVC`), which is `VPJ (2 m₀)` by
`QED.GradedProof.VP2.vpj_gBlock` (`vpj_VA`, `vpj_VB`, `vpj_VC`). Hence each class value, and
their sum, has a covariant, null-continuous limit below `-(2 m₀)²` (`hasVPLim_V`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2
open QED.WickModel (Params)

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ}
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e : ℝ) {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)

include hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ

/-- The block-summed integrand of a class with vertex matrices `A` and line data
(`base`, `c`). -/
noncomputable abbrev vSumF (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (mγ Λ : ℝ) (ε : ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * gH base c (vNum e mγ Λ A base c) mγ Λ (Φ.mass f) ε k ℓ a b

theorem vpj_VA : VPJ (2 * m₀) (vSumF Φ e aVA baseVA cVA mγ Λ) :=
  vpj_gBlock baseVA cVA ![0, 0] ![-1, -1] flowVA hm₀ hmγ hΛ critA_VA critB_VA _ _ _ _
    (vNum_eq e mγ Λ aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVA baseVA cVA) (isLoopPoly_vNumE2 e mγ Λ aVA baseVA cVA)
    (fun m k a b i j => rb_vNum e mγ Λ aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumA e mγ Λ baseVA cVA) (isLoopPoly_vNum_k e mγ Λ aVA baseVA cVA)
    Φ rep hmass hrep hPV₁ hPV₂

theorem vpj_VB : VPJ (2 * m₀) (vSumF Φ e aVB baseVB cVB mγ Λ) :=
  vpj_gBlock baseVB cVB ![0, 1] ![-1, 0] flowVB hm₀ hmγ hΛ critA_VB critB_VB _ _ _ _
    (vNum_eq e mγ Λ aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVB baseVB cVB) (isLoopPoly_vNumE2 e mγ Λ aVB baseVB cVB)
    (fun m k a b i j => rb_vNum e mγ Λ aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumB e mγ Λ baseVB cVB) (isLoopPoly_vNum_k e mγ Λ aVB baseVB cVB)
    Φ rep hmass hrep hPV₁ hPV₂

theorem vpj_VC : VPJ (2 * m₀) (vSumF Φ e aVC baseVC cVC mγ Λ) :=
  vpj_gBlock baseVC cVC ![0, 1] ![-1, 0] flowVC hm₀ hmγ hΛ critA_VC critB_VC _ _ _ _
    (vNum_eq e mγ Λ aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVC baseVC cVC) (isLoopPoly_vNumE2 e mγ Λ aVC baseVC cVC)
    (fun m k a b i j => rb_vNum e mγ Λ aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumC e mγ Λ baseVC cVC) (isLoopPoly_vNum_k e mγ Λ aVC baseVC cVC)
    Φ rep hmass hrep hPV₁ hPV₂

end Classes

/-! ### The class values -/

section Values

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : QED.Graded.Counterterms F)

theorem pp_eq_ppc {pp : (Fin 4 → ℝ) → Fin 5 → Fin 4 → ℝ} {c : Fin 5 → ℝ}
    (h : ∀ k j, pp k j = c j • k) (k : Fin 4 → ℝ) : pp k = ppc c k :=
  funext (h k)

omit [DecidableEq F] in
theorem sum_vterm_eq (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e mγ Λ ε : ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    ∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ f, (Φ.coeff f : ℂ) *
        (kV e mγ Λ ρ σ * vD base (ppc c k) mγ Λ ε ℓ *
          vH base (ppc c k) (A a b ρ σ) ε (Φ.mass f) ℓ) =
      vSumF Φ e A base c mγ Λ ε k ℓ a b := by
  rw [(Finset.sum_congr rfl fun ρ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [gH, vNum, vH, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem val0_repVA (P : Params) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) (a b : Fin 4) :
    val0 { P with ε := ε } Φ D k a b repVA = QED.TwoLoop.jointEnergyFirstIntegral 2
      fun ℓ => vSumF Φ P.e aVA baseVA cVA P.mγ P.Λ ε k ℓ a b := by
  unfold val0 QED.Graded.contractionValue
  rw [loopCount_repVA]
  congr 1
  funext ℓ
  rw [lineMomentum₂_repVA, va_integrand { P with ε := ε } Φ D hε k ℓ a b,
    pp_eq_ppc ppVA_eq k]
  exact sum_vterm_eq Φ aVA baseVA cVA P.e P.mγ P.Λ ε k ℓ a b

theorem val0_repVB (P : Params) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) (a b : Fin 4) :
    val0 { P with ε := ε } Φ D k a b repVB = QED.TwoLoop.jointEnergyFirstIntegral 2
      fun ℓ => vSumF Φ P.e aVB baseVB cVB P.mγ P.Λ ε k ℓ a b := by
  unfold val0 QED.Graded.contractionValue
  rw [loopCount_repVB]
  congr 1
  funext ℓ
  rw [lineMomentum₂_repVB, vb_integrand { P with ε := ε } Φ D hε k ℓ a b,
    pp_eq_ppc ppVB_eq k]
  exact sum_vterm_eq Φ aVB baseVB cVB P.e P.mγ P.Λ ε k ℓ a b

theorem val0_repVC (P : Params) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) (a b : Fin 4) :
    val0 { P with ε := ε } Φ D k a b repVC = QED.TwoLoop.jointEnergyFirstIntegral 2
      fun ℓ => vSumF Φ P.e aVC baseVC cVC P.mγ P.Λ ε k ℓ a b := by
  unfold val0 QED.Graded.contractionValue
  rw [loopCount_repVC]
  congr 1
  funext ℓ
  rw [lineMomentum₂_repVC, vc_integrand { P with ε := ε } Φ D hε k ℓ a b,
    pp_eq_ppc ppVC_eq k]
  exact sum_vterm_eq Φ aVC baseVC cVC P.e P.mγ P.Λ ε k ℓ a b

/-- **The two-loop classes have a covariant, null-continuous limit.** -/
theorem hasVPLim_V (P : Params) (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    HasVPLim (2 * m₀) fun ε k a b => val0 { P with ε := ε } Φ D k a b repVA +
      val0 { P with ε := ε } Φ D k a b repVB + val0 { P with ε := ε } Φ D k a b repVC := by
  refine (((vpj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasVPLim.add
    (vpj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasVPLim).add
    (vpj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasVPLim).congr fun k _ a b => ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [val0_repVA Φ D P hε.ne', val0_repVB Φ D P hε.ne', val0_repVC Φ D P hε.ne']

end Values

end QED.GradedProof.VP2

end
