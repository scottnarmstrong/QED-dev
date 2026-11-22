/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBA
public import QED.ChainProof.SetAKSKWCm
public import QED.ChainProof.SetAKSKWAsmBTot
public import QED.ChainProof.SetAKSKWAsmTot
public import QED.ChainProof.SetAKSKSSpec
public import QED.ChainProof.SetAKSKVPauli

/-!
# Set (a): the core identity `KsCoreOne` and the Pauli limit

Closes the dispersive route of Set (a) of the three-loop coefficient. For `t > -4` the four
subtracted functions of `KsCoreOne` (normalized, `ksW_ksCoreOne_iff`) are once-subtracted
dispersive integrals against the common kernel `ksSpecKer t`:

* `ΔF(t) = ∫₀¹ ksSpecKer(t, δ) ρ_A(δ) dδ` (`ksW_VA_dispersion_rhoA`);
* `ΔF_B(t) = ∫₀¹ ksSpecKer(t, δ) ρ_B(δ) dδ` (`ksWB_VB_dispersion`);
* `Π̂⁽⁴⁾(t) = ∫₀¹ ksSpecKer(t, δ) ρ⁽⁴⁾(δ) dδ`, `D(t) = ∫₀¹ ksSpecKer(t, δ) ρ_D(δ) dδ`
  (`ksS_piHat4_sub_ksDm_eq`, `ksS_ksDm_eq_spectral`).

The density identity `2ρ_A + ρ_B = 16ρ⁽⁴⁾ + 6ρ_D` on `(0, 1)` (`ksWY_density_identity`) gives
`KsCoreOne`, hence `KsCore` (`ksW_ksCore_of_one`), hence the proposition of the frozen set (a)
headline by `isFormFactorPair_vertexSetA_pauli_limit_of_ksCore`.

Main results:

* **`ksWY_ksCoreOne`**: `KsCoreOne`;
* **`ksWY_ksCore`**: `KsCore`;
* **`ksWY_isFormFactorPair_vertexSetA_pauli_limit`**: the proposition of the frozen headline
  `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`, verbatim, with no hypothesis.
-/

@[expose] public section

open Real MeasureTheory Set Complex
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetAKS

open QED.Chain
open QED.ThreeLoop (IsSetA a1SixSetA)

/-- **`KsCoreOne`**: the unit-mass core identity of Set (a). -/
theorem ksWY_ksCoreOne : KsCoreOne := by
  rw [ksW_ksCoreOne_iff]
  intro t ht
  have hA := ksW_VA_dispersion_rhoA ht
  have hB := ksWB_VB_dispersion ht
  have hP : piHat4 t = ∫ δ in (0 : ℝ)..1, ksSpecKer t δ * ksRho δ := by
    have h := ksS_piHat4_sub_ksDm_eq ht 0
    simpa only [ksSpecRho, mul_zero, zero_mul, sub_zero] using h
  have hD : ksDm t = ∫ δ in (0 : ℝ)..1, ksSpecKer t δ * ksRhoDm δ := by
    rw [ksS_ksDm_eq_spectral ht]
    refine intervalIntegral.integral_congr fun δ _ => ?_
    simp only [ksSpecKer]
    ring
  have iA : IntervalIntegrable (fun δ => ksSpecKer t δ * ksWRhoA δ) volume 0 1 := by
    have e : (fun δ => ksSpecKer t δ * ksWRhoA δ) =
        fun δ => ksSpecKer t δ * ksWRhoAn δ - ksSpecKer t δ * ksWRhoAc δ := by
      funext δ
      simp only [ksWRhoA, mul_sub]
    rw [e]
    exact (ksW_intervalIntegrable_VA_node ht).sub (ksW_intervalIntegrable_VA_thr ht)
  have iB := ksWB_intervalIntegrable_VB ht
  have iR : IntervalIntegrable (fun δ => ksSpecKer t δ * ksRho δ) volume 0 1 :=
    (ksS_intervalIntegrable_ksKer ht).congr fun δ _ => ksS_ksKer_eq t δ
  have iD := ksS_intervalIntegrable_ksDmSpec ht
  have key : ∫ δ in (0 : ℝ)..1, (2 * (ksSpecKer t δ * ksWRhoA δ) + ksSpecKer t δ * ksWRhoB δ) =
      ∫ δ in (0 : ℝ)..1, (16 * (ksSpecKer t δ * ksRho δ) + 6 * (ksSpecKer t δ * ksRhoDm δ)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun δ hδ => ?_
    linear_combination ksSpecKer t δ * ksWY_density_identity hδ
  rw [intervalIntegral.integral_add (iA.const_mul 2) iB,
    intervalIntegral.integral_add (iR.const_mul 16) (iD.const_mul 6)] at key
  simp only [intervalIntegral.integral_const_mul] at key
  rw [hA, hB, hP, hD]
  linarith

/-- **`KsCore`**: the core identity of Set (a) at every mass. -/
theorem ksWY_ksCore : KsCore :=
  ksW_ksCore_of_one ksWY_ksCoreOne

/-- **(HA₆)**: the proposition of the frozen set (a) headline
`QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`, verbatim, with no extra hypothesis. -/
theorem ksWY_isFormFactorPair_vertexSetA_pauli_limit (P₀ : Params)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ IsSetA C) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ IsSetA C) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetA : ℂ)‖ < η :=
  isFormFactorPair_vertexSetA_pauli_limit_of_ksCore ksWY_ksCore P₀ he hm η hη

end QED.ChainProof.SetAKS

end
