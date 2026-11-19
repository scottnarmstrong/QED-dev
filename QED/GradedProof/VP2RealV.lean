/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2RealTriple
public import QED.GradedProof.VP2VLim
public import QED.GradedProof.SE2RealPiece

/-!
# The classes `VA`, `VB`, `VC`: imaginary limits

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `VPReal`; the phase counterpart of `QED/GradedProof/VP2VLim.lean`.

The numerator of one fermion loop, `vNum = ∑_{ρσ} kV_{ρσ} vT(A_{μνρσ}, m, y)`, has the constant
`kV = (2π)⁻⁸ (ie)⁴ (1/i)⁵ D_{ρσ}` with a real photon numerator `D`, so `k̄V = -kV` (`conj_kV`), and
the trace `vT` of a product of gamma matrices and electron numerators `m - y̸` at real momenta is
real (`conj_vT`, through the `♯`-symmetry of `QED/GradedProof/SE2RealSharp.lean`). Hence
`v̄Num = -vNum` (`conj_vNum`), the block-summed class integrands are `VPJC (2 m₀) (-1)`
(`vpjc_VA`, `vpjc_VB`, `vpjc_VC`), and the class values have purely imaginary limits
(`hasConjLim_VA`, `hasConjLim_VB`, `hasConjLim_VC`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2Real

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2 QED.GradedProof.VP2 QED.GradedProof.SE2Real
open QED.WickModel (Params)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### The phase of the numerators -/

theorem conj_kV (e mγ Λ : ℝ) (ρ σ : Fin 4) : starRingEnd ℂ (kV e mγ Λ ρ σ) = -kV e mγ Λ ρ σ := by
  simp only [kV, pvPhotonNum, map_mul, map_inv₀, map_pow, map_div₀, map_one, Complex.conj_I,
    Complex.conj_ofReal]
  ring

theorem conj_vT {A : Fin 4 → Mat} (hA : ∀ l, sharp (A l) = A l) (M : ℝ)
    (y : Fin 4 → Fin 4 → ℝ) : starRingEnd ℂ (vT A M y) = vT A M y :=
  conj_trace_of_sharp (by simp only [sharp_mul, hA, sharp_electronNumerator])

theorem conj_vNum (e mγ Λ : ℝ) {A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat}
    (hA : ∀ a b ρ σ l, sharp (A a b ρ σ l) = A a b ρ σ l) (base : Fin 5 → Fin 2 → ℤ)
    (c : Fin 5 → ℝ) (m : ℝ) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    starRingEnd ℂ (vNum e mγ Λ A base c m k ℓ a b) = -1 * vNum e mγ Λ A base c m k ℓ a b := by
  simp only [vNum, map_sum, map_mul, conj_kV, conj_vT (hA a b _ _), Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sharp_aVA (a b ρ σ : Fin 4) (l : Fin 4) : sharp (aVA a b ρ σ l) = aVA a b ρ σ l := by
  fin_cases l <;> simp [aVA, sharp_gamma]

theorem sharp_aVB (a b ρ σ : Fin 4) (l : Fin 4) : sharp (aVB a b ρ σ l) = aVB a b ρ σ l := by
  fin_cases l <;> simp [aVB, sharp_gamma]

theorem sharp_aVC (a b ρ σ : Fin 4) (l : Fin 4) : sharp (aVC a b ρ σ l) = aVC a b ρ σ l := by
  fin_cases l <;> simp [aVC, sharp_gamma]

/-! ### The block-summed class integrands -/

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ}
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e : ℝ) {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)

include hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ

theorem vpjc_VA : VPJC (2 * m₀) (-1) (vSumF Φ e aVA baseVA cVA mγ Λ) :=
  vpjc_gBlock baseVA cVA ![0, 0] ![-1, -1] flowVA hm₀ hmγ hΛ critA_VA critB_VA _ _ _ _
    (vNum_eq e mγ Λ aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVA baseVA cVA) (isLoopPoly_vNumE2 e mγ Λ aVA baseVA cVA)
    (fun m k a b i j => rb_vNum e mγ Λ aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumA e mγ Λ baseVA cVA) (isLoopPoly_vNum_k e mγ Λ aVA baseVA cVA)
    Φ rep hmass hrep hPV₁ hPV₂ (conj_vNum e mγ Λ sharp_aVA baseVA cVA)

theorem vpjc_VB : VPJC (2 * m₀) (-1) (vSumF Φ e aVB baseVB cVB mγ Λ) :=
  vpjc_gBlock baseVB cVB ![0, 1] ![-1, 0] flowVB hm₀ hmγ hΛ critA_VB critB_VB _ _ _ _
    (vNum_eq e mγ Λ aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVB baseVB cVB) (isLoopPoly_vNumE2 e mγ Λ aVB baseVB cVB)
    (fun m k a b i j => rb_vNum e mγ Λ aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumB e mγ Λ baseVB cVB) (isLoopPoly_vNum_k e mγ Λ aVB baseVB cVB)
    Φ rep hmass hrep hPV₁ hPV₂ (conj_vNum e mγ Λ sharp_aVB baseVB cVB)

theorem vpjc_VC : VPJC (2 * m₀) (-1) (vSumF Φ e aVC baseVC cVC mγ Λ) :=
  vpjc_gBlock baseVC cVC ![0, 1] ![-1, 0] flowVC hm₀ hmγ hΛ critA_VC critB_VC _ _ _ _
    (vNum_eq e mγ Λ aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVC baseVC cVC) (isLoopPoly_vNumE2 e mγ Λ aVC baseVC cVC)
    (fun m k a b i j => rb_vNum e mγ Λ aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumC e mγ Λ baseVC cVC) (isLoopPoly_vNum_k e mγ Λ aVC baseVC cVC)
    Φ rep hmass hrep hPV₁ hPV₂ (conj_vNum e mγ Λ sharp_aVC baseVC cVC)

end Classes

/-! ### The class values -/

section Values

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : QED.Graded.Counterterms F) (P : Params) (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)

include hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ

/-- **The class `VA` has a purely imaginary limit.** -/
theorem hasConjLim_VA :
    HasConjLim (2 * m₀) (-1) fun ε k a b => val0 { P with ε := ε } Φ D k a b repVA :=
  (vpjc_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasConjLim.congr fun k _ a b => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [val0_repVA Φ D P hε.ne']

/-- **The class `VB` has a purely imaginary limit.** -/
theorem hasConjLim_VB :
    HasConjLim (2 * m₀) (-1) fun ε k a b => val0 { P with ε := ε } Φ D k a b repVB :=
  (vpjc_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasConjLim.congr fun k _ a b => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [val0_repVB Φ D P hε.ne']

/-- **The class `VC` has a purely imaginary limit.** -/
theorem hasConjLim_VC :
    HasConjLim (2 * m₀) (-1) fun ε k a b => val0 { P with ε := ε } Φ D k a b repVC :=
  (vpjc_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasConjLim.congr fun k _ a b => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [val0_repVC Φ D P hε.ne']

end Values

end QED.GradedProof.VP2Real

end
