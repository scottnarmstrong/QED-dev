/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.HeadlineAssemblyUnits
public import QED.TwoLoop.FormFactorClause
public import QED.TwoLoop.UnitsRegulated
public import QED.Frozen.WickModel.ElectronCountertermsExistsUnique
public import QED.Frozen.WickModel.PhotonCountertermExistsUnique
public import QED.Frozen.OneLoop.ChargeConditionExistsUnique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The assembly of the two-loop headline from the unit links

Section 5.6 of `docs/TWO-LOOP-DERIVATION.md`; decisions D-37.1, D-37.4, D-41, D-43. The statement
of `pauliLimit_of_unitLimits` is, after its two hypotheses, exactly the proposition of the frozen
headline (HV₃) `QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit`
(`QED/Frozen/TwoLoop/VertexOrderFivePauliLimit.lean`, not imported here). Its hypotheses are the
two unit links not yet proved, `SCUnitLimit` and `XUnitLimit`
(`QED/TwoLoop/HeadlineAssemblyUnits.lean`); with proofs `hSC`, `hX` of them the headline is
`pauliLimit_of_unitLimits hSC hX`.

## Proof

Fix `η > 0`. Take the thresholds of the four unit links at tolerance `η/8`, at the mass `m` of
`P₀`: the ladder (`QED.TwoLoop.MassScaling.unitF2_L_limit_mass`), `S + C` and `X` (the
hypotheses) give `δ, R` independent of the regulator fermions; the vacuum polarization
(`QED.TwoLoop.MassScaling.unitF2_VP_iterated_limit_mass`) gives `R_M`, and for `M₁, M₂ > R_M`
thresholds `δ, R`. The headline's `R_M` is the latter, and its `δ, R` are the least and largest of
the four. Then, at fixed regulators beyond the thresholds:

* **counterterms exist** (`exists_counterterms`): `Z₁` from the sealed (K), `δ₁ = Z₁ - 1`;
  `(δ₂, δ_m)` from the sealed (Z₆) at that `δ₁`; `δ₃` from the sealed (Z₉) at these three; (Z₅)
  does not involve `δ₃` (`QED.TwoLoop.Scaling.isElectronOnShell_iff`);
* for admissible counterterms at charge `e`, choose admissible ones `kᵢ` at charge `1` (again
  `exists_counterterms`); then `pauliZeroLimit P e = e⁴ ∑_U unitF2 U (atUnitCharge P k)`
  (`QED.TwoLoop.UnitsRegulated.pauliZeroLimit_eq_pow_four_mul_of_conditions`,
  `pauliZeroFour_eq_sum_units`), and the four links put `16π⁴ ∑_U unitF2 U` within `η/2` of
  `A₁⁽⁴⁾` (`QED.TwoLoop.HeadlineAssembly.norm_sum_unitF2_sub_a1Four_lt`);
* the `q² → 0⁺` limit is uniform over the pairs at fixed regulators and counterterms
  (`QED.TwoLoop.PauliZero.uniform_isFormFactorPair_of_tendsto_pauliAt` with
  `QED.TwoLoop.PauliZeroLimit.tendsto_pauliZeroLimit`): there is `q₀` with
  `‖F₂ - pauliZeroLimit P e‖ < (η/2) e⁴/(16π⁴)` for every form-factor pair `F` of every vertex
  limit at every on-shell pair with `0 < q² < q₀`;
* the limit exists and has a form-factor pair
  (`QED.TwoLoop.FormFactorClause.`
  `exists_isVertexOrderFiveLimit_and_existsUnique_isFormFactorPair_headline`).
-/

@[expose] public section

open Matrix Complex Filter Topology
open scoped Real
open QED.WickModel (Params onePIFunction₂ IsElectronOnShell IsPhotonOnShell)

namespace QED.TwoLoop.HeadlineAssembly

open QED.TwoLoop.UnitsRegulated QED.TwoLoop.MassScaling

/-- **Admissible counterterms exist** (the existence clause of (HV₃)). For `e ≠ 0`, `m > 0`,
regulator fermions heavier than `m` with the Pauli–Villars conditions and `m_γ, Λ > 0`, there are
counterterms with the electron on shell (Z₅), the charge condition (K₀) with `Z₁ = 1 + δ₁`, and
the photon on shell (Z₈). From the sealed (K), (Z₆) and (Z₉). -/
theorem exists_counterterms (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (M₁ M₂ c₁ c₂ : ℝ)
    (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ∃ d₁ d₂ dm d₃ : ℝ,
      IsElectronOnShell
        { P₀ with
          M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
          δm := dm, δ₃ := d₃ } hm hmγ hΛ ∧
      QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ ∧
      IsPhotonOnShell
        { P₀ with
          M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
          δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂ := by
  obtain ⟨Z₁, hZ₁, -⟩ := QED.OneLoop.existsUnique_isChargeNormalized P₀.e P₀.m mγ Λ he hm hmγ hΛ
  obtain ⟨d, hd, -⟩ := QED.WickModel.electronCounterterms_existsUnique
    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := Z₁ - 1 } hm hmγ hΛ
  obtain ⟨d₃, hd₃, -⟩ := QED.WickModel.photonCounterterm_existsUnique
    { P₀ with
      M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := Z₁ - 1, δ₂ := d.1,
      δm := d.2 } hm hM₁ hM₂ hPV₁ hPV₂
  refine ⟨Z₁ - 1, d.1, d.2, d₃, ?_, ?_, hd₃⟩
  · have h := (QED.TwoLoop.Scaling.isElectronOnShell_iff
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := Z₁ - 1, δ₂ := d.1,
        δm := d.2 } hm hmγ hΛ).1 hd
    exact (QED.TwoLoop.Scaling.isElectronOnShell_iff
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := Z₁ - 1, δ₂ := d.1,
        δm := d.2, δ₃ := d₃ } hm hmγ hΛ).2 h
  · rw [add_sub_cancel]
    exact hZ₁

/-- **The two-loop headline (HV₃) from the two missing unit links.** The conclusion is, verbatim,
the proposition of the frozen `QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit`. -/
theorem pauliLimit_of_unitLimits (hSC : SCUnitLimit) (hX : XUnitLimit) (P₀ : Params)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ (M₁ M₂ c₁ c₂ : ℝ) (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂), RM < M₁ → RM < M₂ →
      ∀ (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0),
      ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
        (∃ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ ∧
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ ∧
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂) ∧
        ∀ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ →
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ →
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hM₁ hM₂ hPV₁ hPV₂ →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ } p' p V) ∧
            ∀ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ } p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 - (a1Four : ℂ)‖ < η := by
  have hη8 : 0 < η / 8 := by positivity
  -- the thresholds of the four unit links
  obtain ⟨δL, hδL, RL, hL⟩ := unitF2_L_limit_mass hm hη8
  obtain ⟨δS, hδS, RS, hS⟩ := hSC hm hη8
  obtain ⟨δX, hδX, RX, hXl⟩ := hX hm hη8
  obtain ⟨RV, hV⟩ := unitF2_VP_iterated_limit_mass hm (η / 8) hη8
  refine ⟨RV, fun M₁ M₂ c₁ c₂ hM₁ hM₂ hRM₁ hRM₂ hPV₁ hPV₂ => ?_⟩
  obtain ⟨δV, hδV, ΛV, hVP⟩ := hV M₁ M₂ hRM₁ hRM₂
  refine ⟨min (min δL δS) (min δX δV), lt_min (lt_min hδL hδS) (lt_min hδX hδV),
    max (max RL RS) (max RX ΛV), fun mγ Λ hmγ hΛ hδ hR => ?_⟩
  have hmL : mγ < δL := lt_of_lt_of_le hδ ((min_le_left _ _).trans (min_le_left _ _))
  have hmS : mγ < δS := lt_of_lt_of_le hδ ((min_le_left _ _).trans (min_le_right _ _))
  have hmX : mγ < δX := lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_left _ _))
  have hmV : mγ < δV := lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_right _ _))
  have hRL : RL < Λ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hR
  have hRS : RS < Λ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hR
  have hRX : RX < Λ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hR
  have hRV : ΛV < Λ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hR
  refine ⟨exists_counterterms P₀ he hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ hmγ hΛ,
    fun d₁ d₂ dm d₃ hel hch hph => ?_⟩
  -- admissible counterterms at charge `1`
  obtain ⟨k₁, k₂, km, k₃, hel₁, hch₁, hph₁⟩ :=
    exists_counterterms { P₀ with e := 1 } one_ne_zero hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ
      hmγ hΛ
  set P : Params :=
    { P₀ with
      M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
      δm := dm, δ₃ := d₃ } with hP
  set Q : Params := atUnitCharge P k₁ k₂ km k₃ with hQ
  have hel₁' : IsElectronOnShell Q hm hmγ hΛ := hel₁
  have hph₁' : IsPhotonOnShell Q hm hM₁ hM₂ hPV₁ hPV₂ := hph₁
  have hch₁' : QED.OneLoop.IsChargeNormalized 1 (1 + k₁) P.m P.mγ P.Λ hm hmγ hΛ := hch₁
  -- the regulated coefficient as the sum of the units
  have hpz : QED.TwoLoop.PauliZeroLimit.pauliZeroLimit P P.e =
      (P₀.e : ℂ) ^ 4 * ∑ U, unitF2 U Q := by
    rw [pauliZeroLimit_eq_pow_four_mul_of_conditions P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ he hel hph hch
      hel₁' hph₁' hch₁', pauliZeroFour_eq_sum_units P hm hmγ hΛ hM₁.le hM₂.le hPV₁ hPV₂]
  have hunits : ‖16 * (π : ℂ) ^ 4 * ∑ U, unitF2 U Q - (a1Four : ℂ)‖ < 4 * (η / 8) :=
    norm_sum_unitF2_sub_a1Four_lt Q
      (hVP P hm hM₁ hM₂ hPV₁ hPV₂ rfl rfl rfl hmγ hmV hRV k₁ k₂ km k₃ hph₁')
      (hS P hm hmγ hΛ rfl hmS hRS k₁ k₂ km k₃ hel₁' hch₁')
      (hL P hm hmγ hΛ rfl hmL hRL k₁ k₂ km k₃ hch₁')
      (hXl P hm hmγ hΛ rfl hmX hRX k₁ k₂ km k₃ hel₁' hch₁')
  -- the uniform `q² → 0⁺` limit over the pairs
  have he' : (P₀.e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he
  set c : ℂ := 16 * (π : ℂ) ^ 4 / (P₀.e : ℂ) ^ 4 with hc
  have hc0 : c ≠ 0 := by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [hc]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hπ)) (pow_ne_zero 4 he')
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  obtain ⟨q₀, hq₀, hunif⟩ := QED.TwoLoop.PauliZero.uniform_isFormFactorPair_of_tendsto_pauliAt P
    hm hmγ hΛ hM₁.le hM₂.le hPV₁ hPV₂ he
    (QED.TwoLoop.PauliZeroLimit.tendsto_pauliZeroLimit P hm hmγ hΛ hM₁.le hM₂.le hPV₁ hPV₂ P.e)
    (η / 2 / ‖c‖) (by positivity)
  refine ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq => ?_⟩
  obtain ⟨hex, hall⟩ :=
    FormFactorClause.exists_isVertexOrderFiveLimit_and_existsUnique_isFormFactorPair_headline
      P₀ he hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ hmγ hΛ d₁ d₂ dm d₃ p' p hp' hp hp0' hp0 hq
  refine ⟨hex, fun V hV => ⟨(hall V hV).1, fun F hF => ?_⟩⟩
  have hF2 : ‖F.2 - (P₀.e : ℂ) ^ 4 * ∑ U, unitF2 U Q‖ < η / 2 / ‖c‖ := by
    have h := hunif p' p hp hp' hp0 hp0' hq hqq V hV F hF
    rw [hpz] at h
    exact h
  have e1 : 16 * (π : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 - (a1Four : ℂ) =
      c * (F.2 - (P₀.e : ℂ) ^ 4 * ∑ U, unitF2 U Q) +
        (16 * (π : ℂ) ^ 4 * ∑ U, unitF2 U Q - (a1Four : ℂ)) := by
    simp only [hc]
    field_simp
    ring
  rw [e1]
  have h1 : ‖c * (F.2 - (P₀.e : ℂ) ^ 4 * ∑ U, unitF2 U Q)‖ < η / 2 := by
    rw [norm_mul]
    calc ‖c‖ * ‖F.2 - (P₀.e : ℂ) ^ 4 * ∑ U, unitF2 U Q‖ < ‖c‖ * (η / 2 / ‖c‖) :=
          mul_lt_mul_of_pos_left hF2 hcpos
      _ = η / 2 := by field_simp
  calc _ ≤ ‖c * (F.2 - (P₀.e : ℂ) ^ 4 * ∑ U, unitF2 U Q)‖ +
        ‖16 * (π : ℂ) ^ 4 * ∑ U, unitF2 U Q - (a1Four : ℂ)‖ := norm_add_le _ _
    _ < η := by linarith

end QED.TwoLoop.HeadlineAssembly

end
