/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCReduceSChengWu
public import QED.TwoLoop.UnitSCReduceCChengWu
public import QED.TwoLoop.UnitLLinkCt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The units `S` and `C` at finite regulators in the hierarchical variables

Section 8 of `docs/TWO-LOOP-UNITS.md`, the `S + C` link, the reductions assembled with the
`δ₁` counterterms. With `P₁ = atUnitCharge P d₁ d₂ d_m d₃` (charge `1`, counterterms `dᵢ`), at
`m = 1`, `0 < m_γ < Λ`, normalized to the coefficient of `r² = (α/π)²`:

* `sixteen_pi_pow_four_mul_unitF2_S`: **the unit `S`**
  `16π⁴ unitF2 S P₁ = 2 ∫₀¹ dY ∫₀^∞ dz_o ∫₀^∞ dz_a selfDocSum(Y, z_o, z_a) + 16π⁴ ct_S(P₁)`,
  `ct_S = (1/(64 m⁵)) (1/i) (d2InZero + d2OutZero)` the two `δ₂, δ_m` classes (`sCtHalf`), the
  graph half being eq. (5.1) of the document (`selfDocF`, `selfDocF_subst`);
* `sixteen_pi_pow_four_mul_unitF2_C`: **the unit `C`**, for `d₁` fixed by the frozen charge
  condition (K₀) at charge `1`:
  `16π⁴ unitF2 C P₁ = 2 ∫_{y₃, y₄} ∫₀^∞ dz_o ∫₀^∞ dz_a cornerF4 + 2 δ₁ (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`,
  with `δ₁` of section 3.2 (`QED.TwoLoop.UnitLLink.ladderDeltaOne`), the graph half being eq. (6.2)
  of the document (`cornerTerm_subst`): the `2δ₁F₂⁽²⁾` of the unit table, with the outer
  Pauli–Villars subtraction still present.

What remains of the `S + C` link (section 8 of the document, items 4 and 8–11): the values of
`d2InZero`, `d2OutZero` (the `δ₂, δ_m` insertions, `-δ₂ V + (δ₂ - δ_m) m V_{S̃²}` in the limit
`ε → 0⁺`), the `b`-integrations (masters), and the joint regulator limit.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitSCReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitsRegulated
open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitLLink

/-- The `δ₂, δ_m` half of the unit `S`: `(1/(64 m⁵)) (1/i) (d2InZero + d2OutZero)`. -/
noncomputable def sCtHalf (P : Params) : ℂ :=
  1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * (d2InZero P + d2OutZero P))

theorem unitF2_S_eq (P : Params) :
    unitF2 .S P = 1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * (openZero .Sp P + openZero .Sm P)) +
      sCtHalf P := by
  simp only [unitF2, unitZero, sCtHalf]
  ring

theorem unitF2_C_eq (P : Params) :
    unitF2 .C P = 1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * (openZero .Cp P + openZero .Cm P)) +
      2 * ctHalf P := by
  simp only [unitF2, unitZero, ctHalf]
  ring

/-- **The unit `S` at finite regulators** (`m = 1`, `0 < m_γ < Λ`): the graph half in the
variables of eq. (5.1) plus the `δ₂, δ_m` classes. -/
theorem sixteen_pi_pow_four_mul_unitF2_S (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ)
    (hΛ : P.mγ < P.Λ) (d₁ d₂ dm d₃ : ℝ) :
    16 * (π : ℂ) ^ 4 * unitF2 .S (atUnitCharge P d₁ d₂ dm d₃) =
      ((2 * ∫ Y in Ioo (0 : ℝ) 1, ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
          selfDocSum P Y zo za : ℝ) : ℂ) +
        16 * (π : ℂ) ^ 4 * sCtHalf (atUnitCharge P d₁ d₂ dm d₃) := by
  have h := sixteen_pi_pow_four_mul_openZero_S_eq_doc_iterated (P := atUnitCharge P d₁ d₂ dm d₃)
    hm rfl hmγ hΛ
  rw [unitF2_S_eq, mul_add, h]
  rfl

/-- **The unit `C` at finite regulators** (`m = 1`, `0 < m_γ < Λ`, `d₁` fixed by the frozen charge
condition): the graph half in the hierarchical variables plus `2 δ₁ (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`. -/
theorem sixteen_pi_pow_four_mul_unitF2_C (P : Params) (hm : P.m = 1) (hm0 : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ0 : 0 < P.Λ) (hΛ : P.mγ < P.Λ) {d₁ d₂ dm d₃ : ℝ}
    (hch : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm0 hmγ hΛ0) :
    16 * (π : ℂ) ^ 4 * unitF2 .C (atUnitCharge P d₁ d₂ dm d₃) =
      ((2 * ∫ p in innerTriangle, ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
          cornerF4 P ![zo, p.1, p.2, za, 1 - (p.1 + p.2)] : ℝ) : ℂ) +
        ((2 * (ladderDeltaOne P.m P.mγ P.Λ * (oneLoopF2 P.m P.mγ - oneLoopF2 P.m P.Λ)) : ℝ) : ℂ) := by
  have h := sixteen_pi_pow_four_mul_openZero_C_eq_iterated (P := atUnitCharge P d₁ d₂ dm d₃)
    hm rfl hmγ hΛ
  have hct := sixteen_pi_pow_four_mul_ctHalf P hm0 hmγ hΛ0 (d₂ := d₂) (dm := dm) (d₃ := d₃) hch
  rw [unitF2_C_eq, mul_add, h, show 16 * (π : ℂ) ^ 4 * (2 * ctHalf (atUnitCharge P d₁ d₂ dm d₃)) =
    2 * (16 * (π : ℂ) ^ 4 * ctHalf (atUnitCharge P d₁ d₂ dm d₃)) by ring, hct]
  push_cast
  rfl

end QED.TwoLoop.UnitSCReduce

end
