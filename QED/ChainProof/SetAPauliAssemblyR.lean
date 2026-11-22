/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAPauliAssembly
public import QED.ChainProof.SetAPhotonReg

/-!
# The set (a) headline (HA₆) at the photon function `setAR`

Helper level for (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetAPauliLimit.lean`, `DRAFT_SORRY`, not imported). At the photon
function `R = QED.ChainProof.SetANestedAt.setAR P₀` the nested value
(`setANestedAt_of_nestForm`) and the regularity (`setAPhotonReg`) are proved, so:

* **`isFormFactorPair_vertexSetA_pauli_limit_of_N_reg`**: the proposition of (HA₆) from
  obligation (N) `SetANestClasses P₀` and the regulator limit
  `SetARegLimitPV (setAPauliValue P₀ (setAR P₀))`, for `e ≠ 0`, `m > 0`;
* `setAPauliValue_setAR_diag`: at `M₁ = M₂` there is no admissible data, so the value is `0`;
* `a1SixSetA_eq_zero_of_setARegLimit`: hence `SetARegLimit (setAPauliValue P₀ (setAR P₀))`
  (all `M₁, M₂`, `QED/ChainProof/SetAPauliCond.lean`) would force `A₁⁽⁶⁾(a) = 0`; the regulator
  limit is to be proved in the form `SetARegLimitPV` (over `M₁ ≠ M₂`).
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetAPauliAssembly

open QED.ChainProof.SetANestedAt QED.ChainProof.SetAPauli

/-- **(HA₆) from obligation (N) and the regulator limit at `R = setAR P₀`.** The conclusion is,
verbatim, the proposition of the frozen `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
-/
theorem isFormFactorPair_vertexSetA_pauli_limit_of_N_reg (P₀ : Params)
    (hC : SetANestClasses P₀) (hreg : SetARegLimitPV (setAPauliValue P₀ (setAR P₀)))
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
              (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (ThreeLoop.a1SixSetA : ℂ)‖ < η :=
  isFormFactorPair_vertexSetA_pauli_limit_of_nestForm P₀ (setANestForm_of_classes hm hC)
    (setANestedAt_of_nestForm he hm (setANestForm_of_classes hm hC)) (setAPhotonReg hm) hreg he
    hm η hη

/-- **At `M₁ = M₂` the fixed-regulator value of `setAR` is `0`**: no Pauli–Villars data exists. -/
theorem setAPauliValue_setAR_diag {P₀ : Params} (hm : 0 < P₀.m) (mγ Λ M : ℝ) :
    setAPauliValue P₀ (setAR P₀) mγ Λ M M = 0 := by
  have hno : ¬∃ Pol, SetAPolAt P₀ M M mγ Λ Pol := by
    rintro ⟨Pol, c₁, c₂, D, hA, -⟩
    obtain ⟨hM, -, hPV₁, hPV₂, -⟩ := hA
    exact ne_of_pv hm hM hPV₁ hPV₂ rfl
  have hR : setAR P₀ mγ Λ M M = fun _ => 0 := by
    funext K
    simp [setAR, setAPol, hno]
  simp [setAPauliValue, hR, QED.ChainProof.HCValue.outerAt]

/-- **`SetARegLimit` fails at `setAR`**: it would force `A₁⁽⁶⁾(a) = 0`. -/
theorem a1SixSetA_eq_zero_of_setARegLimit {P₀ : Params} (hm : 0 < P₀.m)
    (h : SetARegLimit (setAPauliValue P₀ (setAR P₀))) : ThreeLoop.a1SixSetA = 0 := by
  by_contra hne
  obtain ⟨RM, hRM⟩ := h |ThreeLoop.a1SixSetA| (abs_pos.mpr hne)
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hRM (|RM| + 1) (|RM| + 1) (by linarith [le_abs_self RM])
    (by linarith [le_abs_self RM])
  have h1 := hΛ₀ (δ / 2) (|Λ₀| + 1) (by positivity) (by linarith)
    (by linarith [le_abs_self Λ₀])
  rw [setAPauliValue_setAR_diag hm, zero_sub, abs_neg] at h1
  exact lt_irrefl _ h1

end QED.ChainProof.SetAPauliAssembly

end
