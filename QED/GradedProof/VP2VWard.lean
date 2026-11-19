/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VWardNum

/-!
# The two-loop Ward identity for the classes `VA`, `VB`, `VC`

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. By
`QED.GradedProof.VP2.ward_gH`, the `k`-contracted block-summed integrand of each class is a
difference of two block-summed three-line loops (`pS`) plus `iε` times the contracted remainder
(`ward_sum`). The six three-line loops are integrable (`jef_pS`), and they cancel in pairs
after a unimodular change of the loop momenta (`pS_A1_eq`, `pS_A2_eq`, `pS_C1_eq`):

`A₁(ℓ₀, ℓ₁) = C₂(ℓ₀ - k, ℓ₁)`, `A₂(ℓ₀, ℓ₁) = B₁(ℓ₁, ℓ₀ + k)`, `C₁(ℓ₀, ℓ₁) = B₂(ℓ₁ - k, ℓ₀ + k)`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Class data -/

/-- The vertex matrices of `VA` after `γ^μ`. -/
noncomputable def bVA (ν ρ σ : Fin 4) : Fin 3 → Mat :=
  ![Dirac.gamma σ, Dirac.gamma ρ, Dirac.gamma ν]

/-- The vertex matrices of `VB` after `γ^μ`. -/
noncomputable def bVB (ν ρ σ : Fin 4) : Fin 3 → Mat :=
  ![Dirac.gamma σ, Dirac.gamma ν, Dirac.gamma ρ]

/-- The vertex matrices of `VC` after `γ^μ`. -/
noncomputable def bVC (ν ρ σ : Fin 4) : Fin 3 → Mat :=
  ![Dirac.gamma ν, Dirac.gamma σ, Dirac.gamma ρ]

theorem aVA_eq (μ ν ρ σ : Fin 4) :
    aVA μ ν ρ σ = ![Dirac.gamma μ, bVA ν ρ σ 0, bVA ν ρ σ 1, bVA ν ρ σ 2] := by
  funext l
  fin_cases l <;> rfl

theorem aVB_eq (μ ν ρ σ : Fin 4) :
    aVB μ ν ρ σ = ![Dirac.gamma μ, bVB ν ρ σ 0, bVB ν ρ σ 1, bVB ν ρ σ 2] := by
  funext l
  fin_cases l <;> rfl

theorem aVC_eq (μ ν ρ σ : Fin 4) :
    aVC μ ν ρ σ = ![Dirac.gamma μ, bVC ν ρ σ 0, bVC ν ρ σ 1, bVC ν ρ σ 2] := by
  funext l
  fin_cases l <;> rfl

theorem fm_VA (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (l : Fin 4) :
    fm baseVA (ppc cVA k) l ℓ = ![ℓ 0, ℓ 1, ℓ 0, k + ℓ 0] l := by
  funext μ
  fin_cases l <;> simp [lineMomentum, castLoopMatrix, baseVA, cVA, Fin.sum_univ_two, add_comm]

theorem fm_VB (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (l : Fin 4) :
    fm baseVB (ppc cVB k) l ℓ = ![ℓ 0, ℓ 1 - k, ℓ 1, k + ℓ 0] l := by
  funext μ
  fin_cases l <;> simp [lineMomentum, castLoopMatrix, baseVB, cVB, Fin.sum_univ_two] <;> ring

theorem fm_VC (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (l : Fin 4) :
    fm baseVC (ppc cVC k) l ℓ = ![ℓ 0, k + ℓ 0, ℓ 1, k + ℓ 0] l := by
  funext μ
  fin_cases l <;> simp [lineMomentum, castLoopMatrix, baseVC, cVC, Fin.sum_univ_two] <;> ring

theorem phm_VA (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    phm baseVA (ppc cVA k) ℓ = ℓ 0 - ℓ 1 := by
  funext μ
  simp [lineMomentum, castLoopMatrix, baseVA, cVA, Fin.sum_univ_two]
  ring

theorem phm_VB (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    phm baseVB (ppc cVB k) ℓ = ℓ 0 - ℓ 1 + k := by
  funext μ
  simp [lineMomentum, castLoopMatrix, baseVB, cVB, Fin.sum_univ_two]
  ring

theorem phm_VC (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    phm baseVC (ppc cVC k) ℓ = ℓ 0 - ℓ 1 + k := by
  funext μ
  simp [lineMomentum, castLoopMatrix, baseVC, cVC, Fin.sum_univ_two]
  ring

theorem hl_VA (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    fm baseVA (ppc cVA k) 3 ℓ = k + fm baseVA (ppc cVA k) 0 ℓ := by
  rw [fm_VA, fm_VA]; rfl

theorem hl_VB (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    fm baseVB (ppc cVB k) 3 ℓ = k + fm baseVB (ppc cVB k) 0 ℓ := by
  rw [fm_VB, fm_VB]; rfl

theorem hl_VC (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    fm baseVC (ppc cVC k) 3 ℓ = k + fm baseVC (ppc cVC k) 0 ℓ := by
  rw [fm_VC, fm_VC]; rfl

theorem kV_symm (e mγ Λ : ℝ) (ρ σ : Fin 4) : kV e mγ Λ ρ σ = kV e mγ Λ σ ρ := by
  simp only [kV, pvPhotonNum, Minkowski.metric_symm ρ σ]

theorem propDenom_neg' (M ε : ℝ) (p : Fin 4 → ℝ) : propDenom M ε (-p) = propDenom M ε p := by
  simp [propDenom, Minkowski.dot]

/-! ### Block-summed three-line loops -/

section PS

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e mγ Λ : ℝ)

/-- The block-summed flavour sum of a three-line loop. -/
noncomputable def pS (Bt : Fin 4 → Fin 4 → Fin 3 → Mat) (base : Fin 5 → Fin 2 → ℤ)
    (pp : Fin 5 → Fin 4 → ℝ) (r : Fin 3 → Fin 4) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * g3 base pp r (pN e mγ Λ Bt base pp r) mγ Λ (Φ.mass f) ε ℓ

theorem pN_cons (Bt : Fin 4 → Fin 4 → Fin 3 → Mat) (base : Fin 5 → Fin 2 → ℤ)
    (pp : Fin 5 → Fin 4 → ℝ) (a b d : Fin 4) (M : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    pN e mγ Λ Bt base pp ![a, b, d] M ℓ = ∑ ρ, ∑ σ, kV e mγ Λ ρ σ *
      tr3 (Bt ρ σ) ![electronNumerator M (fm base pp a ℓ), electronNumerator M (fm base pp b ℓ),
        electronNumerator M (fm base pp d ℓ)] := by
  simp only [pN]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  funext l
  fin_cases l <;> rfl

/-- **The Ward identity for a block-summed class integrand.** -/
theorem ward_sum (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (B : Fin 4 → Fin 4 → Fin 4 → Fin 3 → Mat) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (hA : ∀ μ ν ρ σ, A μ ν ρ σ = ![Dirac.gamma μ, B ν ρ σ 0, B ν ρ σ 1, B ν ρ σ 2])
    (hl : ∀ k ℓ, fm base (ppc c k) 3 ℓ = k + fm base (ppc c k) 0 ℓ) {ε : ℝ} (hε : ε ≠ 0)
    (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (ν : Fin 4) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
        ∑ f, (Φ.coeff f : ℂ) * gH base c (vNum e mγ Λ A base c) mγ Λ (Φ.mass f) ε k ℓ μ ν =
      pS Φ e mγ Λ (bt1 B ν) base (ppc c k) ![0, 1, 2] ε ℓ -
        pS Φ e mγ Λ (B ν) base (ppc c k) ![1, 2, 3] ε ℓ +
        (ε : ℂ) * I * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          ∑ f, (Φ.coeff f : ℂ) * gH base c (rNum e mγ Λ A base c) mγ Λ (Φ.mass f) ε k ℓ μ ν := by
  have h : ∀ (G : F → Fin 4 → ℂ), ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
      ∑ f, (Φ.coeff f : ℂ) * G f μ =
        ∑ f, (Φ.coeff f : ℂ) * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * G f μ := fun G => by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [h, h]
  simp only [ward_gH e mγ Λ A B base c hA hl _ hε, pS, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, Finset.mul_sum _ _ ((ε : ℂ) * I)]
  refine Finset.sum_congr rfl fun _ _ => ?_
  have hz : ∀ (C X Y a : ℂ) (Z : Fin 4 → ℂ), C * (X - Y + ∑ i, a * Z i) =
      C * X - C * Y + a * (C * ∑ i, Z i) := fun C X Y a Z => by
    rw [← Finset.mul_sum]
    ring
  exact hz _ _ _ _ _

end PS

/-! ### The cancellations -/

section Cancel

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν : Fin 4)

theorem pS_A1_eq (ℓ : Fin 2 → Fin 4 → ℝ) :
    pS Φ e mγ Λ (bt1 bVA ν) baseVA (ppc cVA k) ![0, 1, 2] ε ℓ =
      pS Φ e mγ Λ (bVC ν) baseVC (ppc cVC k) ![1, 2, 3] ε ![ℓ 0 - k, ℓ 1] := by
  have hk : k + (ℓ 0 - k) = ℓ 0 := by abel
  have hp : ℓ 0 - k - ℓ 1 + k = ℓ 0 - ℓ 1 := by abel
  simp only [pS, g3, pN_cons, vD, fm_VA, fm_VC, phm_VA, phm_VC, Fin.prod_univ_three,
    Matrix.cons_val, hk, hp, bt1, bVA, bVC]

theorem pS_A2_eq (ℓ : Fin 2 → Fin 4 → ℝ) :
    pS Φ e mγ Λ (bVA ν) baseVA (ppc cVA k) ![1, 2, 3] ε ℓ =
      pS Φ e mγ Λ (bt1 bVB ν) baseVB (ppc cVB k) ![0, 1, 2] ε ![ℓ 1, ℓ 0 + k] := by
  have hk : ℓ 0 + k - k = ℓ 0 := by abel
  have hp : ℓ 1 - (ℓ 0 + k) + k = -(ℓ 0 - ℓ 1) := by abel
  simp only [pS, g3, pN_cons, vD, fm_VA, fm_VB, phm_VA, phm_VB, Fin.prod_univ_three,
    Matrix.cons_val, hk, hp, propDenom_neg', bt1, bVA, bVB]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_comm (f := fun ρ σ => kV e mγ Λ ρ σ * _)]
  simp only [kV_symm e mγ Λ _ _, add_comm k (ℓ 0)]

theorem pS_C1_eq (ℓ : Fin 2 → Fin 4 → ℝ) :
    pS Φ e mγ Λ (bt1 bVC ν) baseVC (ppc cVC k) ![0, 1, 2] ε ℓ =
      pS Φ e mγ Λ (bVB ν) baseVB (ppc cVB k) ![1, 2, 3] ε ![ℓ 1 - k, ℓ 0 + k] := by
  have hk' : ℓ 0 + k - k = ℓ 0 := by abel
  have hp : ℓ 1 - k - (ℓ 0 + k) + k = -(ℓ 0 - ℓ 1 + k) := by abel
  simp only [pS, g3, pN_cons, vD, fm_VC, fm_VB, phm_VC, phm_VB, Fin.prod_univ_three,
    Matrix.cons_val, hk', hp, propDenom_neg', bt1, bVC, bVB]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_comm (f := fun ρ σ => kV e mγ Λ ρ σ * _)]
  simp only [kV_symm e mγ Λ _ _, add_comm k (ℓ 0)]
  ring_nf

end Cancel

end QED.GradedProof.VP2

end
