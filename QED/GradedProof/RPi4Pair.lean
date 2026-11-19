/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4WLim

/-!
# (R-Π₄) step L6: the photon-pair decomposition of the two-loop classes

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6. The Pauli–Villars
photon of the model enters each two-loop class `VA`, `VB`, `VC` only through
`(Λ² - m_γ²) D_{m_γ}⁻¹ D_Λ⁻¹ = D_{m_γ}⁻¹ - D_Λ⁻¹` (`D_μ = q² + μ² - iε`). So the class integrand
at the photon pair `(a, d)` is the sum of those at `(a, b)` and `(b, d)`, exactly at every
`ε ≠ 0`, and the class limits inherit this: no differentiation in `Λ²` and no exchange of the
limit `ε → 0⁺` with a derivative is needed.

* `kV_eq_mul`, `vNum_eq_mul`: the photon constant and the class numerator are `Λ² - m_γ²` times
  their values at the pair `(0, 1)`.
* `vSumF_pair`: the class integrand at `(a, d)` is the sum of those at `(a, b)` and `(b, d)`.
* `wV Φ e A base c a b`: the named `ε → 0⁺` limit of a class at the photon pair `(a, b)`;
  `wCl_VA_eq` (and `VB`, `VC`): the class limit `wCl` of step L1 is `wV` at `(m_γ, Λ)`.
* `wV_add`: **`W(a, d) = W(a, b) + W(b, d)`** at every `k` of the region, for every class with
  `VPJ` integrands at every photon pair (`wV_VA_add`, `wV_VB_add`, `wV_VC_add`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2
open QED.TwoLoop.CountertermLimit (pvPhotonNum)
open QED.TwoLoop.Bridge (propDenom)
open QED.TwoLoop.Bridge renaming propDenom_ne_zero → pdne

namespace QED.GradedProof.RPi4

/-! ### The photon factor -/

/-- The photon constant is `Λ² - m_γ²` times its value at the pair `(0, 1)`. -/
theorem kV_eq_mul (e a b : ℝ) (ρ σ : Fin 4) :
    kV e a b ρ σ = ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * kV e 0 1 ρ σ := by
  simp only [kV, pvPhotonNum]
  push_cast
  ring

/-- The class numerator is `Λ² - m_γ²` times its value at the pair `(0, 1)`. -/
theorem vNum_eq_mul (e a b : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (m : ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    vNum e a b A base c m k ℓ μ ν = ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNum e 0 1 A base c m k ℓ μ ν := by
  simp only [vNum, kV_eq_mul e a b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Partial fractions for three denominators: `(z - u)/(u z) = (v - u)/(u v) + (z - v)/(v z)`. -/
theorem pair_inv {u v z : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (hz : z ≠ 0) :
    (z - u) * (u⁻¹ * z⁻¹) = (v - u) * (u⁻¹ * v⁻¹) + (z - v) * (v⁻¹ * z⁻¹) := by
  field_simp
  ring

/-- **The class integrand at the photon pair `(a, d)` is the sum of those at `(a, b)` and
`(b, d)`**, at every `ε ≠ 0`. -/
theorem vSumF_pair {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (a b d : ℝ) {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    vSumF Φ e A base c a d ε k ℓ μ ν =
      vSumF Φ e A base c a b ε k ℓ μ ν + vSumF Φ e A base c b d ε k ℓ μ ν := by
  simp only [vSumF, gH, vD, vNum_eq_mul e a d, vNum_eq_mul e a b, vNum_eq_mul e b d,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  set q := phm base (ppc c k) ℓ
  have h := pair_inv (pdne (M := a) hε q) (pdne (M := b) hε q) (pdne (M := d) hε q)
  have e1 : ∀ x y : ℝ, ((y ^ 2 - x ^ 2 : ℝ) : ℂ) = propDenom y ε q - propDenom x ε q := by
    intro x y
    rw [propDenom_eq_add y, propDenom_eq_add x]
    push_cast
    ring
  rw [e1 a d, e1 a b, e1 b d]
  linear_combination ((Φ.coeff f : ℂ) * vNum e 0 1 A base c (Φ.mass f) k ℓ μ ν *
    ∏ l : Fin 4, (propDenom (Φ.mass f) ε (fm base (ppc c k) l ℓ))⁻¹) * h

/-! ### The named limits at a photon pair -/

theorem limT_congr {G H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ k μ ν, ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε k μ ν = H ε k μ ν) : limT G = limT H :=
  funext fun k => funext fun μ => funext fun ν => by
    simp only [limT, limUnder]
    rw [Filter.map_congr (h k μ ν)]

section Pair

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e : ℝ)
  (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

/-- **The limit tensor of a class at the photon pair `(a, b)`.** -/
noncomputable def wV (a b : ℝ) : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  limT fun ε k μ ν =>
    QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => vSumF Φ e A base c a b ε k ℓ μ ν

/-- **`W(a, d) = W(a, b) + W(b, d)`** at every `k` of the region. -/
theorem wV_add {T : ℝ} (hV : ∀ a b : ℝ, 0 < a → 0 < b → VPJ T (vSumF Φ e A base c a b))
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) {k : Fin 4 → ℝ}
    (hk : -T ^ 2 < Minkowski.dot k k) (μ ν : Fin 4) :
    wV Φ e A base c a d k μ ν = wV Φ e A base c a b k μ ν + wV Φ e A base c b d k μ ν := by
  have h1 := tendsto_limT_of_hasVPLim (hV a b ha hb).hasVPLim hk μ ν
  have h2 := tendsto_limT_of_hasVPLim (hV b d hb hd).hasVPLim hk μ ν
  refine limT_eq ((h1.add h2).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add ((hV a b ha hb).2 ε hε k μ ν)
    ((hV b d hb hd).2 ε hε k μ ν)]
  exact congrArg _ (funext fun ℓ => (vSumF_pair Φ e A base c a b d hε.ne' k ℓ μ ν).symm)

/-- The tendsto form of `wV`. -/
theorem tendsto_wV {T : ℝ} {a b : ℝ} (hV : VPJ T (vSumF Φ e A base c a b)) {k : Fin 4 → ℝ}
    (hk : -T ^ 2 < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        fun ℓ => vSumF Φ e A base c a b ε k ℓ μ ν) (𝓝[>] 0) (𝓝 (wV Φ e A base c a b k μ ν)) :=
  tendsto_limT_of_hasVPLim hV.hasVPLim hk μ ν

end Pair

/-! ### The classes `VA`, `VB`, `VC` -/

section Classes

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

theorem wCl_VA_eq : wCl P Φ D repVA = wV Φ P.e aVA baseVA cVA P.mγ P.Λ :=
  limT_congr fun k μ ν => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact val0_repVA Φ D P hε.ne' k μ ν

theorem wCl_VB_eq : wCl P Φ D repVB = wV Φ P.e aVB baseVB cVB P.mγ P.Λ :=
  limT_congr fun k μ ν => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact val0_repVB Φ D P hε.ne' k μ ν

theorem wCl_VC_eq : wCl P Φ D repVC = wV Φ P.e aVC baseVC cVC P.mγ P.Λ :=
  limT_congr fun k μ ν => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact val0_repVC Φ D P hε.ne' k μ ν

variable (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

theorem wV_VA_add (e : ℝ) {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    wV Φ e aVA baseVA cVA a d k μ ν =
      wV Φ e aVA baseVA cVA a b k μ ν + wV Φ e aVA baseVA cVA b d k μ ν :=
  wV_add Φ e aVA baseVA cVA (fun _ _ h₁ h₂ => vpj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ e h₁ h₂)
    ha hb hd (by rwa [neg_sq_two_mul]) μ ν

theorem wV_VB_add (e : ℝ) {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    wV Φ e aVB baseVB cVB a d k μ ν =
      wV Φ e aVB baseVB cVB a b k μ ν + wV Φ e aVB baseVB cVB b d k μ ν :=
  wV_add Φ e aVB baseVB cVB (fun _ _ h₁ h₂ => vpj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ e h₁ h₂)
    ha hb hd (by rwa [neg_sq_two_mul]) μ ν

theorem wV_VC_add (e : ℝ) {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    wV Φ e aVC baseVC cVC a d k μ ν =
      wV Φ e aVC baseVC cVC a b k μ ν + wV Φ e aVC baseVC cVC b d k μ ν :=
  wV_add Φ e aVC baseVC cVC (fun _ _ h₁ h₂ => vpj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ e h₁ h₂)
    ha hb hd (by rwa [neg_sq_two_mul]) μ ν

end Classes

end QED.GradedProof.RPi4

end
