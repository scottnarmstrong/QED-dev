/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecDilG
public import QED.GradedProof.RPi4DecDil

/-!
# (R-Π₄) step L9, D3a: dimensional analysis of the two-loop classes and the mass insertions

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3a. Dilating the masses, the photon regulators and the momenta by `l` and `ε` by `l²`:

* every denominator scales by `l²` (`dec_propDenom_smul`), every numerator `M - p̸` by `l`
  (`dec_electronNumerator_smul`), the photon constant by `l²` (`dec_kV_smul`);
* hence the two-loop class integrand by `l⁻⁶` (`dec_vSumF_smul`) and the weighted
  mass-derivative block by `l⁻²` (`dec_dBlockD_smul`);
* the on-shell mass insertion is dilation invariant (`dec_ctPair_smul`).

With the integrals (`dec_jef_smul`, `dec_efi_smul`) the `ε`-families satisfy the hypothesis of
`dec_projS_smul` (`dec_jef_vSumF_smul`, `dec_efi_dBlockD_smul`).
-/

@[expose] public section

open Complex Filter Topology
open QED.GradedProof.VP2
open QED.TwoLoop.Bridge (electronNumerator propDenom)

namespace QED.GradedProof.RPi4

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

variable {l : ℝ}

/-! ### The building blocks -/

theorem dec_lineMomentum_smul {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (l : ℝ) :
    QED.Integration.TwoLoop.lineMomentum α (fun r => cs r • (l • k)) i (l • ℓ) =
      l • QED.Integration.TwoLoop.lineMomentum α (fun r => cs r • k) i ℓ := by
  funext μ
  simp only [QED.Integration.TwoLoop.lineMomentum, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · ring

theorem dec_fm_smul (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ) (j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) (l : ℝ) :
    fm base (ppc c (l • k)) j (l • ℓ) = l • fm base (ppc c k) j ℓ :=
  dec_lineMomentum_smul _ c _ k ℓ l

theorem dec_phm_smul (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (l : ℝ) :
    phm base (ppc c (l • k)) (l • ℓ) = l • phm base (ppc c k) ℓ :=
  dec_lineMomentum_smul _ c _ k ℓ l

theorem dec_propDenom_smul (M ε : ℝ) (q : Fin 4 → ℝ) (l : ℝ) :
    propDenom (l * M) (l ^ 2 * ε) (l • q) = ((l ^ 2 : ℝ) : ℂ) * propDenom M ε q := by
  simp only [propDenom, Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem dec_electronNumerator_smul (M : ℝ) (p : Fin 4 → ℝ) (l : ℝ) :
    electronNumerator (l * M) (l • p) = (l : ℂ) • electronNumerator M p := by
  simp only [electronNumerator, Dirac.slash_smul, smul_sub, smul_smul]
  push_cast
  rfl

theorem dec_vT_smul (A : Fin 4 → Mat) (M : ℝ) (y : Fin 4 → Fin 4 → ℝ) (l : ℝ) :
    vT A (l * M) (fun j => l • y j) = (l : ℂ) ^ 4 * vT A M y := by
  simp only [vT, dec_electronNumerator_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  ring

theorem dec_kV_smul (e a b : ℝ) (ρ σ : Fin 4) (l : ℝ) :
    kV e (l * a) (l * b) ρ σ = ((l ^ 2 : ℝ) : ℂ) * kV e a b ρ σ := by
  simp only [kV, QED.TwoLoop.CountertermLimit.pvPhotonNum]
  push_cast
  ring

theorem dec_vNum_smul (e a b : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (m : ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) (l : ℝ) :
    vNum e (l * a) (l * b) A base c (l * m) (l • k) (l • ℓ) μ ν =
      (l : ℂ) ^ 6 * vNum e a b A base c m k ℓ μ ν := by
  simp only [vNum, dec_fm_smul, dec_vT_smul, dec_kV_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

theorem dec_vD_smul (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ) (a b ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (hl : l ≠ 0) :
    vD base (ppc c (l • k)) (l * a) (l * b) (l ^ 2 * ε) (l • ℓ) =
      ((l : ℂ) ^ 4)⁻¹ * vD base (ppc c k) a b ε ℓ := by
  simp only [vD, dec_phm_smul, dec_propDenom_smul, mul_inv]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  push_cast
  field_simp

/-- **The two-loop class integrand scales by `l⁻⁶`.** -/
theorem dec_vSumF_smul {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat) (base : Fin 5 → Fin 2 → ℤ)
    (c : Fin 5 → ℝ) (a b ε : ℝ) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4)
    (hl : l ≠ 0) :
    vSumF (decDil l Φ) e A base c (l * a) (l * b) (l ^ 2 * ε) (l • k) (l • ℓ) μ ν =
      ((l : ℂ) ^ 6)⁻¹ * vSumF Φ e A base c a b ε k ℓ μ ν := by
  simp only [vSumF, gH, decDil, dec_vD_smul base c k a b ε ℓ hl, dec_vNum_smul, dec_fm_smul,
    dec_propDenom_smul, Finset.mul_sum, mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun _ _ => ?_
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  push_cast
  field_simp

/-- **The joint integral of the class integrand satisfies the dilation hypothesis.** -/
theorem dec_jef_vSumF_smul {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat) (base : Fin 5 → Fin 2 → ℤ)
    (c : Fin 5 → ℝ) (a b ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (hl : 0 < l) :
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => vSumF (decDil l Φ) e A base c (l * a) (l * b) (l ^ 2 * ε) (l • k) ℓ μ ν) =
      ((l ^ 2 : ℝ) : ℂ) * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => vSumF Φ e A base c a b ε k ℓ μ ν) := by
  rw [dec_jef_smul _ hl]
  simp only [dec_vSumF_smul Φ e A base c a b ε k _ μ ν hl.ne', QED.TwoLoop.jointEnergyFirstIntegral,
    MeasureTheory.integral_const_mul]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  field_simp

/-! ### The mass-derivative block -/

theorem dec_zk_smul (k q : Fin 4 → ℝ) (b : Bool) (l : ℝ) :
    zk (l • k) b (l • q) = l • zk k b q := by
  cases b <;> simp [zk, smul_add]

theorem dec_bubTr_smul (A B : Mat) (M : ℝ) (x y : Fin 4 → ℝ) (l : ℝ) :
    bubTr A B (l * M) (l • x) (l • y) = (l : ℂ) ^ 2 * bubTr A B M x y := by
  simp only [bubTr, dec_electronNumerator_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  ring

theorem dec_dBub_smul (A B : Mat) (M ε : ℝ) (x y : Fin 4 → ℝ) (hl : l ≠ 0) :
    dBub A B (l * M) (l ^ 2 * ε) (l • x) (l • y) = ((l : ℂ) ^ 3)⁻¹ * dBub A B M ε x y := by
  simp only [dBub, dec_bubTr_smul, dec_propDenom_smul, mul_inv]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  push_cast
  field_simp

theorem dec_dBubbleW_smul (e M ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) (hl : l ≠ 0) :
    dBubbleW e (l * M) (l ^ 2 * ε) (l • k) (l • q) μ ν =
      ((l : ℂ) ^ 3)⁻¹ * dBubbleW e M ε k q μ ν := by
  simp only [dBubbleW, dec_zk_smul, dec_dBub_smul _ _ _ _ _ _ hl]
  ring

/-- **The weighted mass-derivative block scales by `l⁻²`.** -/
theorem dec_dBlockD_smul {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (rep : F → F) (e : ℝ)
    (δ : F → ℝ) (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) (hl : l ≠ 0) :
    dBlockD (decDil l Φ) rep e δ (l ^ 2 * ε) (l • k) (l • q) μ ν =
      ((l : ℂ) ^ 2)⁻¹ * dBlockD Φ rep e δ ε k q μ ν := by
  simp only [dBlockD, decDil, dec_dBubbleW_smul _ _ _ _ _ _ _ hl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  push_cast
  field_simp

theorem dec_efi_dBlockD_smul {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (rep : F → F)
    (e : ℝ) (δ : F → ℝ) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (hl : 0 < l) :
    QED.OneLoop.energyFirstIntegral
        (fun q => dBlockD (decDil l Φ) rep e δ (l ^ 2 * ε) (l • k) q μ ν) =
      ((l ^ 2 : ℝ) : ℂ) * QED.OneLoop.energyFirstIntegral
        (fun q => dBlockD Φ rep e δ ε k q μ ν) := by
  rw [dec_efi_smul _ hl]
  simp only [dec_dBlockD_smul Φ rep e δ ε k _ μ ν hl.ne', QED.OneLoop.energyFirstIntegral,
    MeasureTheory.integral_const_mul]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  field_simp

/-! ### The on-shell mass insertion -/

theorem dec_onShellL_smul (m a b x : ℝ) (hl : l ≠ 0) :
    onShellL (l * m) (l * a) (l * b) x = onShellL m a b x := by
  simp only [onShellL]
  congr 1
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  rw [show x ^ 2 * (l * m) ^ 2 + (1 - x) * (l * b) ^ 2 =
      l ^ 2 * (x ^ 2 * m ^ 2 + (1 - x) * b ^ 2) by ring,
    show x ^ 2 * (l * m) ^ 2 + (1 - x) * (l * a) ^ 2 =
      l ^ 2 * (x ^ 2 * m ^ 2 + (1 - x) * a ^ 2) by ring, mul_div_mul_left _ _ hl2]

/-- **The on-shell mass insertion is dilation invariant.** -/
theorem dec_ctPair_smul (e m a b : ℝ) (hl : l ≠ 0) :
    ctPair e (l * m) (l * a) (l * b) = ctPair e m a b := by
  simp only [ctPair, dec_onShellL_smul _ _ _ _ hl]

end QED.GradedProof.RPi4

end
