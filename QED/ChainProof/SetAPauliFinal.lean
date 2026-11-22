/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetARegLim
public import QED.ChainProof.SetANestLGW
public import QED.ChainProof.SetANestLGU
public import QED.ChainProof.SetANestLFNested
public import QED.ChainProof.SetANestVB
public import QED.GradedProof.RPi4FaceIdDone

/-!
# The set (a) headline (HA₆), conditional only on `SetAKSScal`

Helper level for (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetAPauliLimit.lean`, `DRAFT_SORRY`, not imported).

* `intHypA_setA`: the hypotheses `IntHypA` of (HA₀) at the data of (HA₆) (admissible
  regulators, `ε > 0`, the scheme `leptonRep` and a counterterm set renormalized through `e⁴`).
* `mass_floor_setA`: every flavour mass of (HA₆) is at least the electron mass.
* **`setANestClasses`**: obligation (N) `SetANestClasses P₀`, for every `P₀` with `m > 0`, from
  the nested forms of the seven loop classes and their three group identities.
* **`isFormFactorPair_vertexSetA_pauli_limit_of_KS`**: the proposition of (HA₆), conditional
  only on the Källén–Sabry input `SetAKSScal P₀.e`; `DecFaceGen` is `faceId_decFaceGen_all`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetAPauliFinal

open QED.ChainProof.SetAPauli QED.ChainProof.SetAPauliAssembly QED.ChainProof.SetANest
open QED.ChainProof.SetALink

/-- **The hypotheses `IntHypA` at the data of (HA₆).** -/
theorem intHypA_setA {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) {ε : ℝ} (hε : 0 < ε) :
    IntHypA (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
      Graded.leptonRep := by
  obtain ⟨-, -, hPV₁, hPV₂, -, -, -, -, hD⟩ := hA
  exact ⟨hε, QED.GradedProof.RPi4.leptonRep_idem,
    QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hPV₁
      fun ℓ => ℓ.elim0,
    QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hPV₂
      fun ℓ => ℓ.elim0,
    QED.GradedProof.RPi4.hD_of_renormalized _ _ _ hD⟩

/-- **The mass floor at the data of (HA₆)**: every flavour mass is at least `m`. -/
theorem mass_floor_setA {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) (g : Fin 3 ⊕ Fin 0 × Fin 3) :
    P₀.m ≤ (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).mass g :=
  QED.GradedProof.RPi4.le_leptonFlavors_mass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hA.1 hA.2.1
    (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) g

/-- **Obligation (N) of (HA₆)**: the seven set (a) loop classes are in nested form, with the
three group identities. -/
theorem setANestClasses {P₀ : Params} (hm : 0 < P₀.m) : SetANestClasses P₀ := by
  intro M₁ M₂ c₁ c₂ mγ Λ D hA p' p _ ε hε _
  have hH := intHypA_setA hA hε
  have hmass := mass_floor_setA hA
  obtain ⟨XVA, XVB, XVC, hVA, hVB, hVC, hV⟩ :=
    loopNested_vertexType _ _ D _ hH hm hmass p' p
  exact ⟨XVA, XVB, XVC, _, _, _, _, hVA, hVB, hVC,
    loopNested_repGW _ _ D _ hH hm hmass p' p, loopNested_repGU _ _ D _ hH hm hmass p' p,
    loopNested_repFA _ _ D _ hH hm hmass p' p, loopNested_repFB _ _ D _ hH hm hmass p' p, hV,
    fun ℓ a b => gauge_group_sum _ _ D ℓ a b, fun ℓ a b => fermion_group_sum _ _ D ℓ a b⟩

/-- **(HA₆), conditional only on the Källén–Sabry input `SetAKSScal P₀.e`.** The conclusion is,
verbatim, the proposition of the frozen `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`;
obligation (N) is `setANestClasses` and `DecFaceGen` is `faceId_decFaceGen_all`. -/
theorem isFormFactorPair_vertexSetA_pauli_limit_of_KS (P₀ : Params)
    (hKS : QED.ChainProof.SetAKS.SetAKSScal P₀.e)
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
  QED.ChainProof.SetARegLim.isFormFactorPair_vertexSetA_pauli_limit_of_N_KS P₀
    (setANestClasses hm) (QED.GradedProof.RPi4.faceId_decFaceGen_all P₀.e) hKS he hm η hη

end QED.ChainProof.SetAPauliFinal

end
