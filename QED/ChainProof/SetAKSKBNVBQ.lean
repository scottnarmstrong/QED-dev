/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNVB
public import QED.ChainProof.SetAKSKBNVA
public import QED.ChainProof.SetAKSKBNVC
public import QED.ChainProof.SetAKSKBMassVal

/-!
# Set (a), stage D: the photon-mass density `qDens` in nested one-loop form

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification). At the configuration `decCfg μ x` (no projection,
`rep = fun _ => 0`), for a photon mass `u > 0` and a momentum `s > -4μ²` read at the tilt
`k'(s) = tiltVec c s`, the density `qDens = -(i/c²)(vDens_VA + vDens_VB + vDens_VC + mass)` is
the sum of the nested forms of the three classes (stage B3; `VC` has the same nested form as
`VA`) and the mass class (stage B4):

* **`ksB_qDens`**: `qDens = -(i/c²)(-π⁴)(2 N_A + N_B) + σ(e, μ, u) ksMassF e μ x s`, with
  `N_A = ∫₀¹ x⁻¹ ∫_{Δ₂} ∑_f c_f K ksNGA`, `N_B = ∫_{Δ₂} (1 - x₃)⁻¹ ∫_{Δ₂} ∑_f c_f K ksNGB`;
* `ksN_faceIdKV`: `K = faceIdKV e 0 1 = -i e⁴/(2π)⁸`;
* **`ksB_qDens_real`**: the density is real,
  `qDens = π⁴e⁴/((2π)⁸c²) (2 ksNestA + ksNestB) + σ(e, μ, u) ksMassF e μ x s`, with the real
  nested integrals `ksNestA`, `ksNestB` of the flavour sums (each carrying the factor
  `k²k³ = c²` inside the outer integrands).

The flavour sum stays inside the integrals: only the flavour sum of the class integrands is
integrable (stage B2).
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.GradedProof.RPi4 QED.GradedProof.VP2
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- **The photon-mass density in nested one-loop form** (stage D input). -/
theorem ksB_qDens {e μ x c s u : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hc : 0 < c)
    (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) (hu : 0 < u) :
    qDens (decCfg μ x) (fun _ => 0) e μ c s u =
      -I / ((c ^ 2 : ℝ) : ℂ) * (-((π : ℂ) ^ 4) *
        (2 * (∫ x' in Ioo (0 : ℝ) 1, x'⁻¹ • ∫ y in simplexSet 2,
            ksNGAsum (decCfg μ x) e u (tiltVec c s) x' (simplexPoint y)) +
          ∫ q in simplexSet 2, (1 - simplexPoint q 2)⁻¹ • ∫ y in simplexSet 2,
            ksNGBsum (decCfg μ x) e u (tiltVec c s) (simplexPoint q) (simplexPoint y))) +
      (sigma e μ u : ℂ) * (ksMassF e μ x s : ℂ) := by
  have hk : -(2 * μ) ^ 2 < Minkowski.dot (tiltVec c s) (tiltVec c s) := by
    rw [dot_tiltVec hs2.le]
    linarith
  have hpv := ksK_pv hμ hx
  have hsum : ∑ f, (decCfg μ x).coeff f = 0 := by
    have := hpv.1 0 rfl
    rwa [Finset.filter_true_of_mem fun _ _ => rfl] at this
  have hsum2 : ∑ f, (decCfg μ x).coeff f * (decCfg μ x).mass f ^ 2 = 0 := by
    have := hpv.2 0 rfl
    rwa [Finset.filter_true_of_mem fun _ _ => rfl] at this
  have hA := (ksN_vDens_VA (decCfg μ x) hsum hsum2 hμ (ksK_mass hμ hx) e hk hu).2
  have hB := (ksN_vDens_VB (decCfg μ x) hsum hsum2 hμ (ksK_mass hμ hx) e hk hu).2
  have hC := (ksN_vDens_VC (decCfg μ x) hsum hsum2 hμ (ksK_mass hμ hx) e hk hu).2
  have hM := ksMass_qDens_mass (u := u) he hμ hx hc hs hs2
  rw [qDens, hA, hB, hC, mul_add, hM]
  ring

/-- The real nested integral of the flavour sum of the outer `VA` integrands. -/
noncomputable def ksNestA {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (u : ℝ)
    (k : Fin 4 → ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, x⁻¹ * ∫ y in simplexSet 2,
    ∑ f, Φ.coeff f * ksNGA (Φ.mass f) u x k (simplexPoint y)

/-- The real nested integral of the flavour sum of the outer `VB` integrands. -/
noncomputable def ksNestB {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (u : ℝ)
    (k : Fin 4 → ℝ) : ℝ :=
  ∫ q in simplexSet 2, (1 - simplexPoint q 2)⁻¹ * ∫ y in simplexSet 2,
    ∑ f, Φ.coeff f * ksNGB (Φ.mass f) u (simplexPoint q) k (simplexPoint y)

theorem ksN_faceIdKV (e : ℝ) : faceIdKV e 0 1 = -I * ((e ^ 4 / (2 * π) ^ 8 : ℝ) : ℂ) := by
  have hI : (1 / I) = -I := by rw [one_div, inv_I]
  simp only [faceIdKV, hI]
  push_cast
  ring_nf
  rw [show I ^ 9 = I by rw [show (9 : ℕ) = 2 * 4 + 1 from rfl, pow_succ, pow_mul, I_sq]; norm_num]

theorem ksN_smul_const (K : ℂ) (x r : ℝ) : x⁻¹ • (K * (r : ℂ)) = K * ((x⁻¹ * r : ℝ) : ℂ) := by
  rw [Complex.real_smul]
  push_cast
  ring

theorem ksN_nestA_eq {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e u : ℝ) (k : Fin 4 → ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y) =
      faceIdKV e 0 1 * (ksNestA Φ u k : ℂ) := by
  have h1 : ∀ x y, ksNGAsum Φ e u k x y = faceIdKV e 0 1 *
      ((∑ f, Φ.coeff f * ksNGA (Φ.mass f) u x k y : ℝ) : ℂ) := by
    intro x y
    simp only [ksNGAsum]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp only [h1, integral_const_mul, integral_complex_ofReal, ksN_smul_const, ksNestA]

theorem ksN_nestB_eq {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e u : ℝ) (k : Fin 4 → ℝ) :
    ∫ q in simplexSet 2, (1 - simplexPoint q 2)⁻¹ • ∫ y in simplexSet 2,
      ksNGBsum Φ e u k (simplexPoint q) (simplexPoint y) =
      faceIdKV e 0 1 * (ksNestB Φ u k : ℂ) := by
  have h1 : ∀ x y, ksNGBsum Φ e u k x y = faceIdKV e 0 1 *
      ((∑ f, Φ.coeff f * ksNGB (Φ.mass f) u x k y : ℝ) : ℂ) := by
    intro x y
    simp only [ksNGBsum]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp only [h1, integral_const_mul, integral_complex_ofReal, ksN_smul_const, ksNestB]

/-- **The photon-mass density is real**: the nested forms with the constants extracted. -/
theorem ksB_qDens_real {e μ x c s u : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hc : 0 < c) (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) (hu : 0 < u) :
    qDens (decCfg μ x) (fun _ => 0) e μ c s u =
      ((π ^ 4 * e ^ 4 / ((2 * π) ^ 8 * c ^ 2) *
          (2 * ksNestA (decCfg μ x) u (tiltVec c s) + ksNestB (decCfg μ x) u (tiltVec c s)) +
        sigma e μ u * ksMassF e μ x s : ℝ) : ℂ) := by
  rw [ksB_qDens he hμ hx hc hs hs2 hu, ksN_nestA_eq, ksN_nestB_eq, ksN_faceIdKV]
  push_cast
  linear_combination (-(π : ℂ) ^ 4 * ((e : ℂ) ^ 4 / ((2 * (π : ℂ)) ^ 8 * (c : ℂ) ^ 2)) *
    (2 * (ksNestA (decCfg μ x) u (tiltVec c s) : ℂ) + ksNestB (decCfg μ x) u (tiltVec c s))) *
    I_sq

end QED.ChainProof.SetAKS

end
