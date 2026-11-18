/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.MassScalingClose
public import QED.Frozen.TwoLoop.A1Four
public import QED.Polylog.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The two missing unit links and the sum of the five units

Section 5.6 of `docs/TWO-LOOP-DERIVATION.md` (O2-23, O2-25), for the assembly of the headline
(HV₃). The ladder and vacuum-polarization links are proved at every mass
(`QED.TwoLoop.MassScaling.unitF2_L_limit_mass`, `unitF2_VP_iterated_limit_mass`). The links of the
units `S + C` and `X` are stated here as named propositions, in the quantifier shape of the ladder
link (thresholds `δ, R` for the joint limit `(m_γ, Λ) → (0, ∞)`, at a fixed electron mass, uniform
in the regulator fermions and in the counterterms):

* `SCUnitLimit`: `16π⁴ (unitF2 S + unitF2 C) → -7/3 + 2 ζ(2) log 2 - ζ(3)/2`;
* `XUnitLimit`: `16π⁴ unitF2 X → 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)`;

for counterterms `dᵢ` with the electron on shell (Z₅) and the charge condition (K₀) at charge `1`.
Their forms at `m = 1` (`SCUnitLimitOne`, `XUnitLimitOne`, the shape of
`QED.TwoLoop.UnitLLink.unitF2_L_limit`) imply them (`SCUnitLimit.of_one`, `XUnitLimit.of_one`),
since these units are dimensionless.

With the four limits, the sum of the units is within `4η` of `A₁⁽⁴⁾`
(`norm_sum_unitF2_sub_a1Four_lt`): the four values add up to `A₁⁽⁴⁾` (`unitValues_sum`).
-/

@[expose] public section

open Complex
open scoped Real

namespace QED.TwoLoop.HeadlineAssembly

open QED.WickModel QED.TwoLoop.UnitsRegulated QED.TwoLoop.MassScaling

/-! ### The two link propositions -/

/-- **The `S + C` unit link at a fixed mass** (hypothesis of the assembly), in the shape of
`QED.TwoLoop.MassScaling.unitF2_L_limit_mass`: for every `m₀ > 0` and `η > 0` there are `δ > 0`
and `R` such that for every parameter set with `m = m₀`, `0 < m_γ < δ`, `Λ > R` and all
counterterms `dᵢ` with the electron on shell (Z₅) and the charge condition (K₀) at charge `1`,
`‖16π⁴ (unitF2 S + unitF2 C) - (-7/3 + 2 ζ(2) log 2 - ζ(3)/2)‖ < η`. -/
def SCUnitLimit : Prop :=
  ∀ {m₀ : ℝ}, 0 < m₀ → ∀ {η : ℝ}, 0 < η →
    ∃ δ > 0, ∃ R : ℝ, ∀ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ),
      P.m = m₀ → P.mγ < δ → R < P.Λ → ∀ d₁ d₂ dm d₃ : ℝ,
        IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ →
        QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ →
        ‖16 * (π : ℂ) ^ 4 * (unitF2 .S (atUnitCharge P d₁ d₂ dm d₃) +
            unitF2 .C (atUnitCharge P d₁ d₂ dm d₃)) -
          ((-(7 / 3) + 2 * (π ^ 2 / 6) * Real.log 2 - QED.Polylog.zeta3 / 2 : ℝ) : ℂ)‖ < η

/-- **The crossed-ladder unit link at a fixed mass** (hypothesis of the assembly), in the shape of
`QED.TwoLoop.MassScaling.unitF2_L_limit_mass`: for every `m₀ > 0` and `η > 0` there are `δ > 0`
and `R` such that for every parameter set with `m = m₀`, `0 < m_γ < δ`, `Λ > R` and all
counterterms `dᵢ` with the electron on shell (Z₅) and the charge condition (K₀) at charge `1`,
`‖16π⁴ unitF2 X - (1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3))‖ < η`. (The unit `X` carries
no counterterm; the two conditions are hypotheses only so that a link proved with them applies.) -/
def XUnitLimit : Prop :=
  ∀ {m₀ : ℝ}, 0 < m₀ → ∀ {η : ℝ}, 0 < η →
    ∃ δ > 0, ∃ R : ℝ, ∀ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ),
      P.m = m₀ → P.mγ < δ → R < P.Λ → ∀ d₁ d₂ dm d₃ : ℝ,
        IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ →
        QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ →
        ‖16 * (π : ℂ) ^ 4 * unitF2 .X (atUnitCharge P d₁ d₂ dm d₃) -
          ((1 / 6 - 5 * (π ^ 2 / 6) * Real.log 2 + 13 / 6 * (π ^ 2 / 6) +
            5 / 4 * QED.Polylog.zeta3 : ℝ) : ℂ)‖ < η

/-- `SCUnitLimit` at `m = 1`, in the shape of `QED.TwoLoop.UnitLLink.unitF2_L_limit`. -/
def SCUnitLimitOne : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ > 0, ∃ R : ℝ, ∀ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ),
      P.m = 1 → P.mγ < δ → R < P.Λ → ∀ d₁ d₂ dm d₃ : ℝ,
        IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ →
        QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ →
        ‖16 * (π : ℂ) ^ 4 * (unitF2 .S (atUnitCharge P d₁ d₂ dm d₃) +
            unitF2 .C (atUnitCharge P d₁ d₂ dm d₃)) -
          ((-(7 / 3) + 2 * (π ^ 2 / 6) * Real.log 2 - QED.Polylog.zeta3 / 2 : ℝ) : ℂ)‖ < η

/-- `XUnitLimit` at `m = 1`, in the shape of `QED.TwoLoop.UnitLLink.unitF2_L_limit`. -/
def XUnitLimitOne : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ > 0, ∃ R : ℝ, ∀ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ),
      P.m = 1 → P.mγ < δ → R < P.Λ → ∀ d₁ d₂ dm d₃ : ℝ,
        IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ →
        QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ →
        ‖16 * (π : ℂ) ^ 4 * unitF2 .X (atUnitCharge P d₁ d₂ dm d₃) -
          ((1 / 6 - 5 * (π ^ 2 / 6) * Real.log 2 + 13 / 6 * (π ^ 2 / 6) +
            5 / 4 * QED.Polylog.zeta3 : ℝ) : ℂ)‖ < η

/-! ### From `m = 1` to every mass -/

/-- The data of the reduction to `m = 1`: for `m > 0`, `0 < m_γ < δ m`, `Λ > R m` and the two
conditions at charge `1`, the parameters `unitMass P` have `m = 1`, `m_γ < δ`, `Λ > R` and the
two conditions at charge `1`. -/
theorem unitMass_data (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {δ R : ℝ}
    (hmδ : P.mγ < δ * P.m) (hRΛ : R * P.m < P.Λ) {d₁ d₂ dm d₃ : ℝ}
    (hel : IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ)
    (hch : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ) :
    ∃ (hm' : 0 < (unitMass P).m) (hmγ' : 0 < (unitMass P).mγ) (hΛ' : 0 < (unitMass P).Λ),
      (unitMass P).m = 1 ∧ (unitMass P).mγ < δ ∧ R < (unitMass P).Λ ∧
      IsElectronOnShell (atUnitCharge (unitMass P) d₁ d₂ dm d₃) hm' hmγ' hΛ' ∧
      QED.OneLoop.IsChargeNormalized 1 (1 + d₁) (unitMass P).m (unitMass P).mγ (unitMass P).Λ
        hm' hmγ' hΛ' := by
  have hs : 0 < P.m⁻¹ := inv_pos.mpr hm
  have hm' : 0 < (unitMass P).m := mul_pos hs hm
  have hmγ' : 0 < (unitMass P).mγ := mul_pos hs hmγ
  have hΛ' : 0 < (unitMass P).Λ := mul_pos hs hΛ
  refine ⟨hm', hmγ', hΛ', unitMass_m hm.ne', ?_, ?_, ?_, ?_⟩
  · rw [unitMass_mγ, div_lt_iff₀ hm]
    exact hmδ
  · rw [unitMass_Λ, lt_div_iff₀ hm]
    exact hRΛ
  · exact (isElectronOnShell_massScale_iff (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hs hm' hmγ'
      hΛ').2 hel
  · exact (isChargeNormalized_mul_iff hm hmγ hΛ hs hm' hmγ' hΛ').2 hch

/-- **The `S + C` link at `m = 1` gives it at every mass** (the units are dimensionless). -/
theorem SCUnitLimit.of_one (h : SCUnitLimitOne) : SCUnitLimit := by
  intro m₀ hm₀ η hη
  obtain ⟨δ, hδ, R, hR⟩ := h hη
  refine ⟨δ * m₀, mul_pos hδ hm₀, R * m₀, fun P hm hmγ hΛ hm1 hmδ hRΛ d₁ d₂ dm d₃ hel hch => ?_⟩
  subst hm1
  obtain ⟨hm', hmγ', hΛ', h1, h2, h3, hel', hch'⟩ :=
    unitMass_data P hm hmγ hΛ hmδ hRΛ hel hch
  have key := hR (unitMass P) hm' hmγ' hΛ' h1 h2 h3 d₁ d₂ dm d₃ hel' hch'
  have hs : 0 < P.m⁻¹ := inv_pos.mpr hm
  have eS : unitF2 .S (atUnitCharge (unitMass P) d₁ d₂ dm d₃) =
      unitF2 .S (atUnitCharge P d₁ d₂ dm d₃) :=
    unitF2_massScale_of_ne_VP (by decide) (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hs
  have eC : unitF2 .C (atUnitCharge (unitMass P) d₁ d₂ dm d₃) =
      unitF2 .C (atUnitCharge P d₁ d₂ dm d₃) :=
    unitF2_massScale_of_ne_VP (by decide) (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hs
  rwa [eS, eC] at key

/-- **The `X` link at `m = 1` gives it at every mass** (the units are dimensionless). -/
theorem XUnitLimit.of_one (h : XUnitLimitOne) : XUnitLimit := by
  intro m₀ hm₀ η hη
  obtain ⟨δ, hδ, R, hR⟩ := h hη
  refine ⟨δ * m₀, mul_pos hδ hm₀, R * m₀, fun P hm hmγ hΛ hm1 hmδ hRΛ d₁ d₂ dm d₃ hel hch => ?_⟩
  subst hm1
  obtain ⟨hm', hmγ', hΛ', h1, h2, h3, hel', hch'⟩ :=
    unitMass_data P hm hmγ hΛ hmδ hRΛ hel hch
  have key := hR (unitMass P) hm' hmγ' hΛ' h1 h2 h3 d₁ d₂ dm d₃ hel' hch'
  have hs : 0 < P.m⁻¹ := inv_pos.mpr hm
  have eX : unitF2 .X (atUnitCharge (unitMass P) d₁ d₂ dm d₃) =
      unitF2 .X (atUnitCharge P d₁ d₂ dm d₃) :=
    unitF2_massScale_of_ne_VP (by decide) (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hs
  rwa [eX] at key

/-! ### The sum of the units -/

/-- **The four unit values add up to `A₁⁽⁴⁾`**:
`(11/48 + ζ(2)/3) + (119/36 - 2 ζ(2)) + (-7/3 + 2 ζ(2) log 2 - ζ(3)/2)
  + (1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)) = A₁⁽⁴⁾`, with `ζ(2) = π²/6`. -/
theorem unitValues_sum :
    (11 / 48 + π ^ 2 / 18) + (119 / 36 - π ^ 2 / 3) +
        (-(7 / 3) + 2 * (π ^ 2 / 6) * Real.log 2 - QED.Polylog.zeta3 / 2) +
        (1 / 6 - 5 * (π ^ 2 / 6) * Real.log 2 + 13 / 6 * (π ^ 2 / 6) + 5 / 4 * QED.Polylog.zeta3) =
      a1Four := by
  have hz : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) = QED.Polylog.zeta3 := rfl
  rw [a1Four, hz]
  ring

/-- The sum over the five units, written out. -/
theorem sum_unitF2 (Q : Params) :
    ∑ U, unitF2 U Q = unitF2 .VP Q + (unitF2 .S Q + unitF2 .C Q) + unitF2 .L Q + unitF2 .X Q := by
  have h : (Finset.univ : Finset TwoLoopUnit) = {.VP, .S, .C, .L, .X} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **The sum of the units is within `4ε` of `A₁⁽⁴⁾`** when each of the four links is within
`ε` of its value. -/
theorem norm_sum_unitF2_sub_a1Four_lt (Q : Params) {ε : ℝ}
    (hVP : ‖(16 * (π : ℂ) ^ 4) * unitF2 .VP Q - ((119 / 36 - π ^ 2 / 3 : ℝ) : ℂ)‖ < ε)
    (hSC : ‖16 * (π : ℂ) ^ 4 * (unitF2 .S Q + unitF2 .C Q) -
      ((-(7 / 3) + 2 * (π ^ 2 / 6) * Real.log 2 - QED.Polylog.zeta3 / 2 : ℝ) : ℂ)‖ < ε)
    (hL : ‖16 * (π : ℂ) ^ 4 * unitF2 .L Q - ((11 / 48 + π ^ 2 / 18 : ℝ) : ℂ)‖ < ε)
    (hX : ‖16 * (π : ℂ) ^ 4 * unitF2 .X Q -
      ((1 / 6 - 5 * (π ^ 2 / 6) * Real.log 2 + 13 / 6 * (π ^ 2 / 6) +
        5 / 4 * QED.Polylog.zeta3 : ℝ) : ℂ)‖ < ε) :
    ‖16 * (π : ℂ) ^ 4 * ∑ U, unitF2 U Q - (a1Four : ℂ)‖ < 4 * ε := by
  have e : 16 * (π : ℂ) ^ 4 * ∑ U, unitF2 U Q - (a1Four : ℂ) =
      ((16 * (π : ℂ) ^ 4) * unitF2 .VP Q - ((119 / 36 - π ^ 2 / 3 : ℝ) : ℂ)) +
      (16 * (π : ℂ) ^ 4 * (unitF2 .S Q + unitF2 .C Q) -
        ((-(7 / 3) + 2 * (π ^ 2 / 6) * Real.log 2 - QED.Polylog.zeta3 / 2 : ℝ) : ℂ)) +
      (16 * (π : ℂ) ^ 4 * unitF2 .L Q - ((11 / 48 + π ^ 2 / 18 : ℝ) : ℂ)) +
      (16 * (π : ℂ) ^ 4 * unitF2 .X Q -
        ((1 / 6 - 5 * (π ^ 2 / 6) * Real.log 2 + 13 / 6 * (π ^ 2 / 6) +
          5 / 4 * QED.Polylog.zeta3 : ℝ) : ℂ)) := by
    rw [sum_unitF2, ← unitValues_sum]
    push_cast
    ring
  rw [e]
  refine lt_of_le_of_lt norm_add₄_le ?_
  linarith

end QED.TwoLoop.HeadlineAssembly

end
