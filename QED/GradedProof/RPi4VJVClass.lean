/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4VJVTriple
public import QED.GradedProof.RPi4Pair

/-!
# (R-Π₄) step L6a: explicit parametric values of the classes `VA`, `VB`, `VC` at a photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6a. The named class
limit `QED.GradedProof.RPi4.wV` at the photon pair `(a, b)` is identified, on the region
`k² > -(2 m₀)²`, with an explicit finite sum of parametric integrals over simplices
(`QED.GradedProof.RPi4.blockVal`): per flavour `f`, the fifteen pieces of the three-flavour
decomposition with masses `M_f, X, X + 1`, each `-π⁴ ∫_Δ paramIntegrand` with eight or seven
lines, the two photon lines carrying the masses `a` and `b`.

* `vVal A base c Φ e m₀ a b`: the value (`blockVal` of the class numerator `vNum`);
* `vpjv_VA`, `vpjv_VB`, `vpjv_VC`: the class integrands converge to `vVal`;
* `wV_eq_vVal_VA`, `wV_eq_vVal_VB`, `wV_eq_vVal_VC`: **`wV = vVal`** on the region (by `limT_eq`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- **The explicit parametric value of a class at the photon pair `(a, b)`.** -/
noncomputable def vVal (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (e m₀ a b : ℝ) : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  blockVal base c (vNum e a b A base c) (vNumE4 e a b A) Φ m₀ a b

/-- A class with a named limit: `wV` is that limit on the region. -/
theorem wV_eq_of_vpjv {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) {T a b : ℝ}
    {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (h : VPJV T (vSumF Φ e A base c a b) W)
    {k : Fin 4 → ℝ} (hk : -T ^ 2 < Minkowski.dot k k) (μ ν : Fin 4) :
    wV Φ e A base c a b k μ ν = W k μ ν :=
  limT_eq (h.2 k hk μ ν)

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ}
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)

include hm₀ hmass hrep hPV₁ hPV₂ ha hb

theorem vpjv_VA : VPJV (2 * m₀) (vSumF Φ e aVA baseVA cVA a b) (vVal aVA baseVA cVA Φ e m₀ a b) :=
  vpjv_gBlock baseVA cVA ![0, 0] ![-1, -1] flowVA hm₀ ha hb critA_VA critB_VA _ _ _ _
    (vNum_eq e a b aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e a b aVA baseVA cVA) (isLoopPoly_vNumE2 e a b aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e a b aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e a b aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (tcov_vNumA e a b baseVA cVA) (isLoopPoly_vNum_k e a b aVA baseVA cVA)
    Φ rep hmass hrep hPV₁ hPV₂

theorem vpjv_VB : VPJV (2 * m₀) (vSumF Φ e aVB baseVB cVB a b) (vVal aVB baseVB cVB Φ e m₀ a b) :=
  vpjv_gBlock baseVB cVB ![0, 1] ![-1, 0] flowVB hm₀ ha hb critA_VB critB_VB _ _ _ _
    (vNum_eq e a b aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e a b aVB baseVB cVB) (isLoopPoly_vNumE2 e a b aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e a b aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e a b aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (tcov_vNumB e a b baseVB cVB) (isLoopPoly_vNum_k e a b aVB baseVB cVB)
    Φ rep hmass hrep hPV₁ hPV₂

theorem vpjv_VC : VPJV (2 * m₀) (vSumF Φ e aVC baseVC cVC a b) (vVal aVC baseVC cVC Φ e m₀ a b) :=
  vpjv_gBlock baseVC cVC ![0, 1] ![-1, 0] flowVC hm₀ ha hb critA_VC critB_VC _ _ _ _
    (vNum_eq e a b aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e a b aVC baseVC cVC) (isLoopPoly_vNumE2 e a b aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e a b aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e a b aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (tcov_vNumC e a b baseVC cVC) (isLoopPoly_vNum_k e a b aVC baseVC cVC)
    Φ rep hmass hrep hPV₁ hPV₂

variable {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4)

include hk

/-- **`W_VA(a, b) = vVal`** on the region. -/
theorem wV_eq_vVal_VA :
    wV Φ e aVA baseVA cVA a b k μ ν = vVal aVA baseVA cVA Φ e m₀ a b k μ ν :=
  wV_eq_of_vpjv Φ e aVA baseVA cVA (vpjv_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb)
    (by rwa [neg_sq_two_mul]) μ ν

/-- **`W_VB(a, b) = vVal`** on the region. -/
theorem wV_eq_vVal_VB :
    wV Φ e aVB baseVB cVB a b k μ ν = vVal aVB baseVB cVB Φ e m₀ a b k μ ν :=
  wV_eq_of_vpjv Φ e aVB baseVB cVB (vpjv_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb)
    (by rwa [neg_sq_two_mul]) μ ν

/-- **`W_VC(a, b) = vVal`** on the region. -/
theorem wV_eq_vVal_VC :
    wV Φ e aVC baseVC cVC a b k μ ν = vVal aVC baseVC cVC Φ e m₀ a b k μ ν :=
  wV_eq_of_vpjv Φ e aVC baseVC cVC (vpjv_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ e ha hb)
    (by rwa [neg_sq_two_mul]) μ ν

end Classes

end QED.GradedProof.RPi4

end
