/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VWard
public import QED.TwoLoop.JointIntegralInvariance

/-!
# The two-loop Ward identity for the classes `VA`, `VB`, `VC`: the limit

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. The six
block-summed three-line loops are integrable (`jef_pS`); integrating
`QED.GradedProof.VP2.ward_sum` (`ward_int`) and cancelling the three-line loops in pairs by a
unimodular change of the loop momenta, the `k`-contraction of `VA + VB + VC` is `iε` times the
contraction of the remainders, whose integrals converge (`vpj_rVA`, ...). Hence the contraction
tends to zero (`tendsto_wardV`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2
open QED.WickModel (Params)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Integrability of the three-line loops -/

theorem crit3A_VA1 :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => baseVA (shA3 ![0, 1, 2] i j n) := by
  decide

theorem crit3B_VA1 :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVA (shB3 ![0, 1, 2] i n) := by
  decide

theorem crit3A_VA2 :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => baseVA (shA3 ![1, 2, 3] i j n) := by
  decide

theorem crit3B_VA2 :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVA (shB3 ![1, 2, 3] i n) := by
  decide

theorem crit3A_VB1 :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => baseVB (shA3 ![0, 1, 2] i j n) := by
  decide

theorem crit3B_VB1 :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVB (shB3 ![0, 1, 2] i n) := by
  decide

theorem crit3A_VB2 :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => baseVB (shA3 ![1, 2, 3] i j n) := by
  decide

theorem crit3B_VB2 :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVB (shB3 ![1, 2, 3] i n) := by
  decide

theorem crit3A_VC1 :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => baseVC (shA3 ![0, 1, 2] i j n) := by
  decide

theorem crit3B_VC1 :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVC (shB3 ![0, 1, 2] i n) := by
  decide

theorem crit3A_VC2 :
    ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => baseVC (shA3 ![1, 2, 3] i j n) := by
  decide

theorem crit3B_VC2 :
    ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => baseVC (shB3 ![1, 2, 3] i n) := by
  decide

theorem isOddG_bt1 {B : Fin 4 → Fin 4 → Fin 4 → Fin 3 → Mat}
    (hB : ∀ ν ρ σ l, IsOddG (B ν ρ σ l)) (ν ρ σ : Fin 4) : ∀ l, IsOddG (bt1 B ν ρ σ l) := by
  intro l
  fin_cases l
  · exact hB _ _ _ 2
  · exact hB _ _ _ 0
  · exact hB _ _ _ 1

theorem isOddG_bVA : ∀ ν ρ σ l, IsOddG (bVA ν ρ σ l) := by
  intro ν ρ σ l
  fin_cases l <;> exact isOddG_gamma _

theorem isOddG_bVB : ∀ ν ρ σ l, IsOddG (bVB ν ρ σ l) := by
  intro ν ρ σ l
  fin_cases l <;> exact isOddG_gamma _

theorem isOddG_bVC : ∀ ν ρ σ l, IsOddG (bVC ν ρ σ l) := by
  intro ν ρ σ l
  fin_cases l <;> exact isOddG_gamma _

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ}
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e mγ Λ : ℝ)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **A block-summed three-line loop is integrable.** -/
theorem jef_pS (Bt : Fin 4 → Fin 4 → Fin 3 → Mat) (hB : ∀ ρ σ l, IsOddG (Bt ρ σ l))
    (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ) (r : Fin 3 → Fin 4)
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2} fun n => base (shA3 r i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB3 r i n))
    {ε : ℝ} (hε : 0 < ε) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (pS Φ e mγ Λ Bt base pp r ε) :=
  jef_g3Block base pp r hcA hcB (pN e mγ Λ Bt base pp r) (pNE0 e mγ Λ Bt base pp r)
    (pNE2 e mγ Λ Bt base pp r) (pN_eq e mγ Λ Bt base pp r hB) (isLoopPoly_pN e mγ Λ Bt base pp r)
    (isLoopPoly_pNE2 e mγ Λ Bt base pp r)
    (fun m i j => (rb_pN e mγ Λ Bt base pp r (shA3 r i j) ![0, 1, 2]
      (fun l => by fin_cases l <;> rfl) (by decide) (by decide) (by decide) m).mono
        (by decide) (by norm_num))
    (fun i => (rb_pNE2 e mγ Λ Bt base pp r (shB3 r i) ![0, 1, 2]
      (fun l => by fin_cases l <;> rfl)).mono (by decide) le_rfl)
    Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ mγ Λ hε

omit [DecidableEq F] hm₀ hmass hrep hPV₁ hPV₂ in
/-- **The integrated Ward identity of a class.** -/
theorem ward_int (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (B : Fin 4 → Fin 4 → Fin 4 → Fin 3 → Mat) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (hA : ∀ μ ν ρ σ, A μ ν ρ σ = ![Dirac.gamma μ, B ν ρ σ 0, B ν ρ σ 1, B ν ρ σ 2])
    (hl : ∀ k ℓ, fm base (ppc c k) 3 ℓ = k + fm base (ppc c k) 0 ℓ) {T ε : ℝ} (hε : 0 < ε)
    (hV : VPJ T (vSumF Φ e A base c mγ Λ)) (hR : VPJ T (rSumF Φ e A base c mγ Λ))
    (k : Fin 4 → ℝ) (ν : Fin 4)
    (h1 : QED.TwoLoop.jointEnergyFirstIntegrable 2
      (pS Φ e mγ Λ (bt1 B ν) base (ppc c k) ![0, 1, 2] ε))
    (h2 : QED.TwoLoop.jointEnergyFirstIntegrable 2
      (pS Φ e mγ Λ (B ν) base (ppc c k) ![1, 2, 3] ε)) :
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => vSumF Φ e A base c mγ Λ ε k ℓ μ ν) =
      QED.TwoLoop.jointEnergyFirstIntegral 2
          (pS Φ e mγ Λ (bt1 B ν) base (ppc c k) ![0, 1, 2] ε) -
        QED.TwoLoop.jointEnergyFirstIntegral 2 (pS Φ e mγ Λ (B ν) base (ppc c k) ![1, 2, 3] ε) +
        (ε : ℂ) * I * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
          QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => rSumF Φ e A base c mγ Λ ε k ℓ μ ν) := by
  have hR' : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * rSumF Φ e A base c mγ Λ ε k ℓ μ ν :=
    JEF.sum _ fun μ _ => JEF.const_mul (hR.2 ε hε k μ ν) _
  rw [← jointEnergyFirstIntegral_sum Finset.univ (fun μ => ((Minkowski.lower k μ : ℝ) : ℂ))
      _ fun μ _ => hV.2 ε hε k μ ν,
    ← jointEnergyFirstIntegral_sum Finset.univ (fun μ => ((Minkowski.lower k μ : ℝ) : ℂ))
      _ fun μ _ => hR.2 ε hε k μ ν]
  have e1 : (fun ℓ => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * vSumF Φ e A base c mγ Λ ε k ℓ μ ν) =
      fun ℓ => pS Φ e mγ Λ (bt1 B ν) base (ppc c k) ![0, 1, 2] ε ℓ +
        ((-1 : ℂ) * pS Φ e mγ Λ (B ν) base (ppc c k) ![1, 2, 3] ε ℓ +
          (ε : ℂ) * I * ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) *
            rSumF Φ e A base c mγ Λ ε k ℓ μ ν) := by
    funext ℓ
    rw [ward_sum Φ e mγ Λ A B base c hA hl hε.ne' k ℓ ν]
    ring
  rw [e1, QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add h1
      (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add (JEF.const_mul h2 _)
        (JEF.const_mul hR' _)),
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (JEF.const_mul h2 _)
      (JEF.const_mul hR' _),
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  ring

end Classes

/-! ### The changes of variables -/

theorem shift_id (ℓ : Fin 2 → Fin 4 → ℝ) (a : Fin 2 → Fin 4 → ℝ) :
    (fun s => ∑ r, (1 : Matrix (Fin 2) (Fin 2) ℤ) s r • ℓ r) + a = ![ℓ 0 + a 0, ℓ 1 + a 1] := by
  funext s
  fin_cases s <;> simp [Fin.sum_univ_two]

theorem shift_swap (ℓ : Fin 2 → Fin 4 → ℝ) (a : Fin 2 → Fin 4 → ℝ) :
    (fun s => ∑ r, (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) s r • ℓ r) + a =
      ![ℓ 1 + a 0, ℓ 0 + a 1] := by
  funext s
  fin_cases s <;> simp [Fin.sum_univ_two]

theorem isUnit_det_swap : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  rw [Matrix.det_fin_two_of]
  norm_num

theorem integral_cov {G H : (Fin 2 → Fin 4 → ℝ) → ℂ} (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : IsUnit M.det) (a : Fin 2 → Fin 4 → ℝ)
    (h : ∀ ℓ, G ℓ = H ((fun s => ∑ r, M s r • ℓ r) + a)) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 G = QED.TwoLoop.jointEnergyFirstIntegral 2 H := by
  rw [show G = fun ℓ => H ((fun s => ∑ r, M s r • ℓ r) + a) from funext h]
  exact QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2 H M hM a

section Cancel

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν : Fin 4)

theorem int_A1 : QED.TwoLoop.jointEnergyFirstIntegral 2
      (pS Φ e mγ Λ (bt1 bVA ν) baseVA (ppc cVA k) ![0, 1, 2] ε) =
    QED.TwoLoop.jointEnergyFirstIntegral 2
      (pS Φ e mγ Λ (bVC ν) baseVC (ppc cVC k) ![1, 2, 3] ε) :=
  integral_cov 1 (by simp) ![-k, 0] fun ℓ => by
    rw [shift_id, pS_A1_eq]
    simp [sub_eq_add_neg]

theorem int_A2 : QED.TwoLoop.jointEnergyFirstIntegral 2
      (pS Φ e mγ Λ (bVA ν) baseVA (ppc cVA k) ![1, 2, 3] ε) =
    QED.TwoLoop.jointEnergyFirstIntegral 2
      (pS Φ e mγ Λ (bt1 bVB ν) baseVB (ppc cVB k) ![0, 1, 2] ε) :=
  integral_cov _ isUnit_det_swap ![0, k] fun ℓ => by
    rw [shift_swap, pS_A2_eq]
    simp

theorem int_C1 : QED.TwoLoop.jointEnergyFirstIntegral 2
      (pS Φ e mγ Λ (bt1 bVC ν) baseVC (ppc cVC k) ![0, 1, 2] ε) =
    QED.TwoLoop.jointEnergyFirstIntegral 2
      (pS Φ e mγ Λ (bVB ν) baseVB (ppc cVB k) ![1, 2, 3] ε) :=
  integral_cov _ isUnit_det_swap ![-k, k] fun ℓ => by
    rw [shift_swap, pS_C1_eq]
    simp [sub_eq_add_neg]

end Cancel

end QED.GradedProof.VP2

end
