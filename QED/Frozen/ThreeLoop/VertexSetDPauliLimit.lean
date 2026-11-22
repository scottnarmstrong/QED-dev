-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetD
public import QED.Frozen.ThreeLoop.A1SixSetD
public import QED.Frozen.Graded.IsFamilyVertexLimit
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Provider.ThreeLoop.VertexSetDPauliLimit

@[expose] public section

open QED.WickModel (Params IsOnePI)

namespace QED.ThreeLoop

/-- (HD₆) **The sixth-order set (d) coefficient of the electron's anomalous magnetic moment, from
the graded model (Stage 3d headline goal; decisions D-37, D-49, D-54, D-57).** The binders,
quantifier order and conditions of (HA₆), unchanged: for every `η > 0` there is `R_M` such that
for all regulator fermions heavier than the electron and than `R_M` and satisfying the
Pauli–Villars conditions there are `δ > 0` and `R` such that for `0 < m_γ < δ` and `Λ > R`
renormalized counterterms exist, and for every choice of them there is `q₀ > 0` such that at
every on-shell positive-energy pair `(p', p)` with `0 < q² < q₀`:
* the set (d) vertex (Gf₁) with the selection `IsOnePI ∧` (Sd₁) at order `7` has an `ε → 0⁺`
  limit (Gf₂);
* every such limit has a form-factor pair (G₀), with the charge `e` factored out, and every such
  pair has `|64 π⁶ F₂ / e⁶ - A₁⁽⁶⁾(d)| < η`, with `A₁⁽⁶⁾(d)` the constant (Sd₂).

The set (d) vertex reads no counterterm: (Sd₁) has only `gauge` vertices. The counterterm clause
is kept so that the statement has the hypotheses of the other set headlines and can be added to
them. Flavours as in (HA₆): the electron block, no heavy lepton; the loop is summed over the
electron and its two regulator fermions, whose loops vanish in the last limit. The headline
concerns one gauge-invariant set of the 72 sixth-order diagrams (D-54 P3; reported as a subset,
D-49 Q8), on the 1PI vertex (D-37.6). -/
theorem isFormFactorPair_vertexSetD_pauli_limit (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (η : ℝ) (hη : 0 < η) :
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
              (fun C _ => IsOnePI C ∧ IsSetD C) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ IsSetD C) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetD : ℂ)‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
