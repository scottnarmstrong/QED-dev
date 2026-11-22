/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.ThreeLoop.IsVPShareOnShell
public import QED.Frozen.ThreeLoop.A1SixSetC
public import QED.Frozen.Graded.IsFamilyVertexLimit
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.GradedProof.RPi4Reduce
public import QED.ChainProof.SetAPauliCond
public import QED.ChainProof.SetCLinkFinal

/-!
# The set (c) headline (HS₆), conditional on a fixed link and a regulator limit

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetCPauliLimit.lean`, `DRAFT_SORRY`, not imported). The statement of
`isFormFactorPair_vertexSetC_pauli_limit_of_links` is, after its two hypotheses, exactly the
proposition of the frozen headline. Its hypotheses are **not** proved here:

* `SetCFixedLink P₀ a`: at fixed admissible regulators (`m < M₁, M₂`, Pauli–Villars conditions,
  `0 < m_γ < Λ`, `m_γ < 2m`), for every `D` renormalized through order `e⁴` and every VP share
  `s` of `D` (Sc₂), for every `η > 0` there is `q₀ > 0` such that at every on-shell
  positive-energy pair with `0 < q² < q₀` the `ε → 0⁺` limits of the set (c) family vertex (with
  the level-`1` fermion counterterms of `D` replaced by `s`) exist, every limit has a form-factor
  pair, and every such pair has `|64π⁶ F₂/e⁶ - a(m_γ, Λ, M₁, M₂)| < η`;
* `SetCRegLimit a`: the iterated regulator limit of the fixed-regulator value `a` in the order
  of D-37.4 (regulator fermions first, then `m_γ → 0`, `Λ → ∞`) is `A₁⁽⁶⁾(c) = a1SixSetC`.

The fixed link splits (`setCFixedLink_of_links`) into
* `SetCLimitLink P₀`: at fixed admissible regulators, every renormalized `D`, every VP share `s`
  and every on-shell positive-energy pair with `q² > 0`, the set (c) family vertex has an
  `ε → 0⁺` limit;
* `SetCPauliLink P₀ a`: near `q² = 0⁺`, every limit has a form-factor pair and every pair has
  `|64π⁶ F₂/e⁶ - a| < η`.

Two clauses of (HS₆) are proved here: the counterterm existence clause
(`QED.GradedProof.RPi4.exists_renormalized` at `n = 0`, as for (HA₆)) and the VP-share existence
clause (`QED.ChainProof.SetCLink.existsUnique_isVPShareOnShell_c`, the provider proof of (G-ex-s),
applied to `D` renormalized through order `e²`, which renormalization through `e⁴` implies).

The proof is the set (a) assembly
(`QED.ChainProof.SetAPauli.isFormFactorPair_vertexSetA_pauli_limit_of_links`): tolerance `η/2`
for the regulator limit and `η/2` for the fixed link, `δ = min(δ', 2m)`, `R = max(Λ₀, δ)`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCPauli

open QED.ChainProof.SetAPauli (regParams regFlavors)

/-- The counterterm data of (HS₆). -/
abbrev RegCt : Type := Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3)

/-- The counterterms of the set (c) vertex in (HS₆): the level-`1` fermion counterterms of `D`
replaced by the VP share `s`, the level-`1` photon counterterm kept. -/
abbrev shareCt (D : RegCt) (s : ℝ × ℝ × ℝ) : RegCt :=
  D.withLevel 1 (fun _ => s) (D.d₃ 1)

/-- **Renormalization through order `e⁴` implies renormalization through order `e²`.** -/
theorem isRenormalizedThrough_one_of_two {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Graded.Counterterms F} {rep : F → F}
    (hD : Graded.IsRenormalizedThrough P Φ D rep 2) : Graded.IsRenormalizedThrough P Φ D rep 1 :=
  ⟨fun f k hk => hD.1 f k (by omega), fun j hj hj1 => hD.2 j hj (by omega)⟩

/-- **A VP share exists** at the data of (HS₆), for every `D` renormalized through order `e⁴`:
the existence half of (G-ex-s) (`QED.ChainProof.SetCLink.existsUnique_isVPShareOnShell_c`). -/
theorem exists_isVPShareOnShell (P₀ : Params) {M₁ M₂ c₁ c₂ mγ Λ : ℝ} (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (hmγ : 0 < mγ) (hΛ : 0 < Λ) {D : RegCt}
    (hD : Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2) :
    ∃ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D s := by
  exact (SetCLink.existsUnique_isVPShareOnShell_c (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep P₀.m he hm
    (QED.GradedProof.RPi4.le_leptonFlavors_mass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hM₁ hM₂ (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0)
      (fun ℓ => ℓ.elim0))
    hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hPV₁ (fun ℓ => ℓ.elim0))
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (Fin.elim0 : Fin 0 → Lepton.HeavyLepton) hPV₂ (fun ℓ => ℓ.elim0))
    (isRenormalizedThrough_one_of_two hD)).exists

/-- **The fixed link of (HS₆)** (open): at fixed admissible regulators, every renormalized `D`
and every VP share `s`, the set (c) limits exist near `q² = 0⁺`, have form-factor pairs, and
their Pauli form factor is within `η` of the fixed-regulator value `a m_γ Λ M₁ M₂`. -/
def SetCFixedLink (P₀ : Params) (a : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ : ℝ, P₀.m < M₁ → P₀.m < M₂ → 1 + c₁ + c₂ = 0 →
    P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 → 0 < mγ → 0 < Λ → mγ < Λ → mγ < 2 * P₀.m →
    ∀ D : RegCt, Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2 →
    ∀ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D s →
      ∀ η : ℝ, 0 < η → ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
        Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
        0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
        (∃ V, Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s)
          (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V) ∧
        ∀ V, Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s)
          (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V →
          (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
          ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
            ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - ((a mγ Λ M₁ M₂ : ℝ) : ℂ)‖ < η

/-- **The regulator limit of (HS₆)** (open): the fixed-regulator value `a` tends to
`A₁⁽⁶⁾(c)` in the iterated order of D-37.4. -/
def SetCRegLimit (a : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ η > 0, ∃ RM : ℝ, ∀ M₁ M₂ : ℝ, RM < M₁ → RM < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
    ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → |a mγ Λ M₁ M₂ - ThreeLoop.a1SixSetC| < η

/-- **(HS₆) from the fixed link and the regulator limit.** The conclusion is, verbatim, the
proposition of the frozen `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_links {a : ℝ → ℝ → ℝ → ℝ → ℝ}
    (P₀ : Params) (hlink : SetCFixedLink P₀ a) (hreg : SetCRegLimit a)
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
          (∃ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (ThreeLoop.a1SixSetC : ℂ)‖ < η := by
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
    fun D hD => ⟨exists_isVPShareOnShell P₀ he hm hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hD, fun s hs => ?_⟩⟩
  obtain ⟨q₀, hq₀, hfix⟩ := hlink M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs
    (η / 2) hη2
  refine ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq => ?_⟩
  obtain ⟨hex, hall⟩ := hfix p' p hp' hp hp0' hp0 hq hqq
  refine ⟨hex, fun V hV => ⟨(hall V hV).1, fun F hF => ?_⟩⟩
  have hF2 := (hall V hV).2 F hF
  have hreg' : ‖((a mγ Λ M₁ M₂ : ℝ) : ℂ) - (ThreeLoop.a1SixSetC : ℂ)‖ < η / 2 := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs]
    exact hΛ₀ mγ Λ hmγ hmδ' hΛ₀'
  calc ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (ThreeLoop.a1SixSetC : ℂ)‖
      ≤ ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - ((a mγ Λ M₁ M₂ : ℝ) : ℂ)‖ +
        ‖((a mγ Λ M₁ M₂ : ℝ) : ℂ) - (ThreeLoop.a1SixSetC : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < η / 2 + η / 2 := add_lt_add hF2 hreg'
    _ = η := add_halves η

/-! ### The fixed link from the limit link and the Pauli link -/

/-- **The limit link of (HS₆)** (open): at fixed admissible regulators, every renormalized `D`,
every VP share `s` and every on-shell positive-energy pair with `q² > 0`, the set (c) family
vertex has an `ε → 0⁺` limit. -/
def SetCLimitLink (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ : ℝ, P₀.m < M₁ → P₀.m < M₂ → 1 + c₁ + c₂ = 0 →
    P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 → 0 < mγ → 0 < Λ → mγ < Λ → mγ < 2 * P₀.m →
    ∀ D : RegCt, Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2 →
    ∀ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D s →
      ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 → Minkowski.dot p p = -P₀.m ^ 2 →
        0 < p' 0 → 0 < p 0 → 0 < Minkowski.dot (p' - p) (p' - p) →
        ∃ V, Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s)
          (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V

/-- **The Pauli link of (HS₆)** (open): near `q² = 0⁺`, every `ε → 0⁺` limit of the set (c)
family vertex has a form-factor pair, and every pair is within `η` of the fixed-regulator value
`a m_γ Λ M₁ M₂`. -/
def SetCPauliLink (P₀ : Params) (a : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ : ℝ, P₀.m < M₁ → P₀.m < M₂ → 1 + c₁ + c₂ = 0 →
    P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 → 0 < mγ → 0 < Λ → mγ < Λ → mγ < 2 * P₀.m →
    ∀ D : RegCt, Graded.IsRenormalizedThrough (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep 2 →
    ∀ s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D s →
      ∀ η : ℝ, 0 < η → ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
        Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
        0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
        ∀ V, Graded.IsFamilyVertexLimit (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
          (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s)
          (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p V →
          (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
          ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
            ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - ((a mγ Λ M₁ M₂ : ℝ) : ℂ)‖ < η

/-- **The fixed link from the limit link and the Pauli link.** -/
theorem setCFixedLink_of_links {P₀ : Params} {a : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hL : SetCLimitLink P₀) (hP : SetCPauliLink P₀ a) : SetCFixedLink P₀ a := by
  intro M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs η hη
  obtain ⟨q₀, hq₀, hall⟩ := hP M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs η hη
  exact ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq =>
    ⟨hL M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs p' p hp' hp hp0' hp0 hq,
      hall p' p hp' hp hp0' hp0 hq hqq⟩⟩

end QED.ChainProof.SetCPauli

end
