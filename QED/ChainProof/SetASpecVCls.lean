/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecChain
public import QED.GradedProof.VP2VLim

/-!
# Set (a): the two-loop vertex-type classes `VA`, `VB`, `VC` have the spectral form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The fixed-`ε` copy of `QED.GradedProof.VP2.vpj_VA`, `vpj_VB`, `vpj_VC`: the block-summed
integrand `vSumF` of each class is `SAJ M_lo` for every `0 ≤ M_lo` below the fermion masses, the
photon mass and the regulator mass.

* `saPolyK_vNum`, `saPolyK_vNumE4`: the class numerators are polynomial along affine loop
  momenta;
* `saRow_VA`, `saRow_VB`, `saRow_VC`: a fermion row of each routing never vanishes;
* **`saj_VA`**, **`saj_VB`**, **`saj_VC`**.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2 QED.GradedProof.VP2

/-! ### Polynomiality of the class numerators -/

theorem saPolyK_vNum (e mγ Λ : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (m : ℝ) :
    SAPolyK 4 (vNum e mγ Λ A base c m) := fun lam δ a b =>
  IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.sum _ fun σ _ =>
    (isLoopPoly_vT_aff (A a b ρ σ) m _ fun l =>
      saAffine_lineMomentum base c l.castSucc lam δ).const_mul _

theorem saPolyK_vNumE4 (e mγ Λ : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    SAPolyK 2 fun k (_ : Fin 2 → Fin 4 → ℝ) a b => vNumE4 e mγ Λ A k a b :=
  fun _ _ _ _ => IsLoopPoly.const _

/-! ### The rows -/

theorem saRow_of {base : Fin 5 → Fin 2 → ℤ} {c : Fin 5 → ℝ} (h0 : base 0 = ![1, 0])
    (h3 : base 3 = ![1, 0]) (hc : c 3 = c 0 + 1) (y : Fin 2 → ℝ) :
    ∃ r : Fin 4, ∑ s, (base r.castSucc s : ℝ) * y s + c r.castSucc ≠ 0 := by
  by_cases hy : y 0 + c 0 = 0
  · refine ⟨3, ?_⟩
    have e : ((3 : Fin 4).castSucc : Fin 5) = 3 := rfl
    rw [e, h3, hc]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    intro h
    linarith
  · refine ⟨0, ?_⟩
    have e : ((0 : Fin 4).castSucc : Fin 5) = 0 := rfl
    rw [e, h0]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    simpa using hy

theorem saRow_VA (y : Fin 2 → ℝ) :
    ∃ r : Fin 4, ∑ s, (baseVA r.castSucc s : ℝ) * y s + cVA r.castSucc ≠ 0 :=
  saRow_of rfl rfl (by simp [cVA]) y

theorem saRow_VB (y : Fin 2 → ℝ) :
    ∃ r : Fin 4, ∑ s, (baseVB r.castSucc s : ℝ) * y s + cVB r.castSucc ≠ 0 :=
  saRow_of rfl rfl (by simp [cVB]) y

theorem saRow_VC (y : Fin 2 → ℝ) :
    ∃ r : Fin 4, ∑ s, (baseVC r.castSucc s : ℝ) * y s + cVC r.castSucc ≠ 0 :=
  saRow_of rfl rfl (by simp [cVC]) y

/-! ### The classes -/

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ}
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e : ℝ) {mγ Λ Mlo : ℝ} (hlo0 : 0 ≤ Mlo) (hlo : Mlo ≤ m₀) (hloγ : Mlo ≤ mγ) (hloΛ : Mlo ≤ Λ)

include hm₀ hmass hrep hPV₁ hPV₂ hlo0 hlo hloγ hloΛ

theorem saj_VA : SAJ Mlo (vSumF Φ e aVA baseVA cVA mγ Λ) :=
  saj_gBlock baseVA cVA ![0, 0] ![-1, -1] flowVA hlo0 hlo hloγ hloΛ saRow_VA critA_VA critB_VA
    _ _ _ _
    (vNum_eq e mγ Λ aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVA baseVA cVA) (isLoopPoly_vNumE2 e mγ Λ aVA baseVA cVA)
    (fun m k a b i j => rb_vNum e mγ Λ aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumA e mγ Λ baseVA cVA) (saPolyK_vNum e mγ Λ aVA baseVA cVA)
    (saPolyK_vNumE4 e mγ Λ aVA) hm₀ Φ rep hmass hrep hPV₁ hPV₂

theorem saj_VB : SAJ Mlo (vSumF Φ e aVB baseVB cVB mγ Λ) :=
  saj_gBlock baseVB cVB ![0, 1] ![-1, 0] flowVB hlo0 hlo hloγ hloΛ saRow_VB critA_VB critB_VB
    _ _ _ _
    (vNum_eq e mγ Λ aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVB baseVB cVB) (isLoopPoly_vNumE2 e mγ Λ aVB baseVB cVB)
    (fun m k a b i j => rb_vNum e mγ Λ aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumB e mγ Λ baseVB cVB) (saPolyK_vNum e mγ Λ aVB baseVB cVB)
    (saPolyK_vNumE4 e mγ Λ aVB) hm₀ Φ rep hmass hrep hPV₁ hPV₂

theorem saj_VC : SAJ Mlo (vSumF Φ e aVC baseVC cVC mγ Λ) :=
  saj_gBlock baseVC cVC ![0, 1] ![-1, 0] flowVC hlo0 hlo hloγ hloΛ saRow_VC critA_VC critB_VC
    _ _ _ _
    (vNum_eq e mγ Λ aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVC baseVC cVC) (isLoopPoly_vNumE2 e mγ Λ aVC baseVC cVC)
    (fun m k a b i j => rb_vNum e mγ Λ aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumC e mγ Λ baseVC cVC) (saPolyK_vNum e mγ Λ aVC baseVC cVC)
    (saPolyK_vNumE4 e mγ Λ aVC) hm₀ Φ rep hmass hrep hPV₁ hPV₂

end Classes

end QED.ChainProof.SetASpec

end
