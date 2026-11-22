/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.ThreeLoop.A1SixSetA
public import QED.Frozen.Graded.IsFamilyVertexLimit
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.GradedProof.RPi4Reduce
public import QED.ChainProof.SetASpecLimSum

/-!
# The set (a) headline (HA₆), conditional on a fixed link and a regulator limit

Helper level for (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetAPauliLimit.lean`, `DRAFT_SORRY`, not imported). The statement of
`isFormFactorPair_vertexSetA_pauli_limit_of_links` is, after its two hypotheses, exactly the
proposition of the frozen headline. Its hypotheses are **not** proved here:

* `SetAFixedLink P₀ a`: at fixed admissible regulators (`m < M₁, M₂`, Pauli–Villars conditions,
  `0 < m_γ < Λ`, `m_γ < 2m`) and for every `D` renormalized through order `e⁴`, for every
  `η > 0` there is `q₀ > 0` such that at every on-shell positive-energy pair with
  `0 < q² < q₀` the `ε → 0⁺` limits of the set (a) family vertex exist, every limit has a
  form-factor pair, and every such pair has `|64π⁶ F₂/e⁶ - a(m_γ, Λ, M₁, M₂)| < η`;
* `SetARegLimit P₀ a`: the iterated regulator limit of the fixed-regulator value `a` in the order
  of D-37.4 (regulator fermions first, then `m_γ → 0`, `Λ → ∞`) is `A₁⁽⁶⁾(a) = a1SixSetA`.

The fixed link splits (`setAFixedLink_of_links`) into
* `SetALimitLink P₀`: at fixed admissible regulators, every renormalized `D` and every on-shell
  positive-energy pair with `q² > 0`, the set (a) family vertex has an `ε`-uniform outer spectral
  form (`QED.ChainProof.SetASpec.SetAOuterSpec`), which gives the `ε → 0⁺` limits
  (`QED.ChainProof.SetASpec.isFamilyVertexLimit_of_outerSpec`);
* `SetAPauliLink P₀ a`: near `q² = 0⁺`, every limit has a form-factor pair and every pair has
  `|64π⁶ F₂/e⁶ - a| < η`.

The counterterm existence clause of (HA₆) is proved:
`QED.GradedProof.RPi4.exists_renormalized` at `n = 0`.

The proof is the set (b) assembly
(`QED.ChainProof.isFormFactorPair_vertexChain_two_pauli_limit_of_fixedLink`) with the graded
counterterms: tolerance `η/2` for the regulator limit and `η/2` for the fixed link,
`δ = min(δ', 2m)`, `R = max(Λ₀, δ)`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetAPauli

/-- The model data of (HA₆) at fixed regulators. -/
abbrev regParams (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) : Params :=
  { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }

/-- The flavours of (HA₆): the electron block with no heavy lepton. -/
abbrev regFlavors (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) :
    Lepton.Flavors (Fin 3 ⊕ Fin 0 × Fin 3) :=
  Lepton.leptonFlavors (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)

/-- **The fixed link of (HA₆)** (open): at fixed admissible regulators and every renormalized
`D`, the set (a) limits exist near `q² = 0⁺`, have form-factor pairs, and their Pauli form factor
is within `η` of the fixed-regulator value `a m_γ Λ M₁ M₂`. -/
def SetAFixedLink (P₀ : Params) (a : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ : ℝ, P₀.m < M₁ → P₀.m < M₂ → 1 + c₁ + c₂ = 0 →
    P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 → 0 < mγ → 0 < Λ → mγ < Λ → mγ < 2 * P₀.m →
    ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
      Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2 →
      ∀ η : ℝ, 0 < η → ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
        Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
        0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
        (∃ V, Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p
          V) ∧
        ∀ V, Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p
          V →
          (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
          ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
            ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - ((a mγ Λ M₁ M₂ : ℝ) : ℂ)‖ < η

/-- **The regulator limit of (HA₆)** (open): the fixed-regulator value `a` tends to
`A₁⁽⁶⁾(a)` in the iterated order of D-37.4. -/
def SetARegLimit (a : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ η > 0, ∃ RM : ℝ, ∀ M₁ M₂ : ℝ, RM < M₁ → RM < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
    ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → |a mγ Λ M₁ M₂ - ThreeLoop.a1SixSetA| < η

/-- **(HA₆) from the fixed link and the regulator limit.** The conclusion is, verbatim, the
proposition of the frozen `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`. -/
theorem isFormFactorPair_vertexSetA_pauli_limit_of_links {a : ℝ → ℝ → ℝ → ℝ → ℝ}
    (P₀ : Params) (hlink : SetAFixedLink P₀ a) (hreg : SetARegLimit a)
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
                  (ThreeLoop.a1SixSetA : ℂ)‖ < η := by
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨RM, hRM⟩ := hreg (η / 2) hη2
  refine ⟨RM, fun M₁ M₂ c₁ c₂ hM₁ hM₂ hRM₁ hRM₂ hPV₁ hPV₂ => ?_⟩
  obtain ⟨δ', hδ', Λ₀, hΛ₀⟩ := hRM M₁ M₂ hRM₁ hRM₂
  have h2m : 0 < 2 * P₀.m := by positivity
  refine ⟨min δ' (2 * P₀.m), lt_min hδ' h2m, max Λ₀ (min δ' (2 * P₀.m)),
    fun mγ Λ hmγ hΛ hδ hR => ?_⟩
  have hmδ' : mγ < δ' := lt_of_lt_of_le hδ (min_le_left _ _)
  have hm2 : mγ < 2 * P₀.m := lt_of_lt_of_le hδ (min_le_right _ _)
  have hΛ₀' : Λ₀ < Λ := lt_of_le_of_lt (le_max_left _ _) hR
  have hmΛ : mγ < Λ := hδ.trans (lt_of_le_of_lt (le_max_right _ _) hR)
  refine ⟨QED.GradedProof.RPi4.exists_renormalized (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) he hm hmγ hΛ hM₁ hM₂ (fun ℓ => ℓ.elim0)
    (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) hPV₁ hPV₂ (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0),
    fun D hD => ?_⟩
  obtain ⟨q₀, hq₀, hfix⟩ := hlink M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD
    (η / 2) hη2
  refine ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq => ?_⟩
  obtain ⟨hex, hall⟩ := hfix p' p hp' hp hp0' hp0 hq hqq
  refine ⟨hex, fun V hV => ⟨(hall V hV).1, fun F hF => ?_⟩⟩
  have hF2 := (hall V hV).2 F hF
  have hreg' : ‖((a mγ Λ M₁ M₂ : ℝ) : ℂ) - (ThreeLoop.a1SixSetA : ℂ)‖ < η / 2 := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs]
    exact hΛ₀ mγ Λ hmγ hmδ' hΛ₀'
  calc ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (ThreeLoop.a1SixSetA : ℂ)‖
      ≤ ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - ((a mγ Λ M₁ M₂ : ℝ) : ℂ)‖ +
        ‖((a mγ Λ M₁ M₂ : ℝ) : ℂ) - (ThreeLoop.a1SixSetA : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < η / 2 + η / 2 := add_lt_add hF2 hreg'
    _ = η := add_halves η

/-! ### The fixed link from the limit link and the Pauli link -/

/-- **The limit link of (HA₆)** (open): the `ε`-uniform outer spectral form of the set (a)
family vertex at fixed admissible regulators, every renormalized `D`, and every on-shell
positive-energy pair with `q² > 0`. -/
def SetALimitLink (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ : ℝ, P₀.m < M₁ → P₀.m < M₂ → 1 + c₁ + c₂ = 0 →
    P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 → 0 < mγ → 0 < Λ → mγ < Λ → mγ < 2 * P₀.m →
    ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
      Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2 →
      ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 → Minkowski.dot p p = -P₀.m ^ 2 →
        0 < p' 0 → 0 < p 0 → 0 < Minkowski.dot (p' - p) (p' - p) →
        SetASpec.SetAOuterSpec (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
          (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p

/-- **The Pauli link of (HA₆)** (open): near `q² = 0⁺`, every `ε → 0⁺` limit of the set (a)
family vertex has a form-factor pair, and every pair is within `η` of the fixed-regulator value
`a m_γ Λ M₁ M₂`. -/
def SetAPauliLink (P₀ : Params) (a : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ : ℝ, P₀.m < M₁ → P₀.m < M₂ → 1 + c₁ + c₂ = 0 →
    P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 → 0 < mγ → 0 < Λ → mγ < Λ → mγ < 2 * P₀.m →
    ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
      Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2 →
      ∀ η : ℝ, 0 < η → ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
        Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
        0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
        ∀ V, Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p
          V →
          (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
          ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
            ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - ((a mγ Λ M₁ M₂ : ℝ) : ℂ)‖ < η

/-- **The fixed link from the limit link and the Pauli link.** -/
theorem setAFixedLink_of_links {P₀ : Params} {a : ℝ → ℝ → ℝ → ℝ → ℝ} (hm : 0 < P₀.m)
    (hL : SetALimitLink P₀) (hP : SetAPauliLink P₀ a) : SetAFixedLink P₀ a := by
  intro M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD η hη
  obtain ⟨q₀, hq₀, hall⟩ := hP M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD η hη
  refine ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq => ⟨?_, hall p' p hp' hp hp0' hp0 hq hqq⟩⟩
  exact SetASpec.isFamilyVertexLimit_of_outerSpec _ _ D _ 7 hm hp' hp hp0' hp0
    (hL M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD p' p hp' hp hp0' hp0 hq)

end QED.ChainProof.SetAPauli

end
