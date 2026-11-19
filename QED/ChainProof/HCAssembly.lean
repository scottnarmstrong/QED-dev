/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCLink
public import QED.Chain.ChainBLimit
public import QED.Frozen.VPChain.A1SixSetB
public import QED.TwoLoop.HeadlineAssembly
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The assembly of the set (b) headline (O3-15), conditional on the fixed link

Helper level, Phase 5 Stage 1a (decisions D-37, D-52, D-53). The statement of
`isFormFactorPair_vertexChain_two_pauli_limit_of_fixedLink` is, after its hypothesis, exactly the
proposition of the frozen headline (HC₃) `QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`
(`QED/Frozen/VPChain/VertexChainTwoPauliLimit.lean`, `DRAFT_SORRY`, not imported). Its hypothesis
is the fixed link `QED.ChainProof.ChainFixedLink` (`QED/ChainProof/HCLink.lean`), which is **not**
proved: it carries obligations O3-5 to O3-10 at fixed regulators. The name is distinct from the
planned unconditional helper `QED.ChainProof.isFormFactorPair_vertexChain_two_pauli_limit'`.

## Proof (the order of D-37.4)

Fix `η > 0`.
* **Regulator limits** (`chainRegMass_iterated_limit`): the explicit set (b) functional in units
  of `m` has the iterated limit `aSetB = a1SixSetB` (`QED.Chain.ChainB.chainReg_iterated_limit`,
  rescaled): there is `R_M` such that for `M₁, M₂ > R_M` there are `δ', Λ₀` with
  `|chainRegMass - aSetB| < η/2` for `m_γ < δ'`, `Λ > Λ₀`. The headline's `δ` is the least of `δ'`
  and `2m`, and its `R` the largest of `Λ₀` and `δ`, so that also `m_γ < Λ` and `m_γ < 2m`.
* **Counterterms exist**: `QED.TwoLoop.HeadlineAssembly.exists_counterterms`, from the sealed (K),
  (Z₆), (Z₉); the existence clause is (HV₃)'s word for word.
* **At fixed regulators**: the parameters are admissible (`ChainAdmissible`), so the fixed link at
  tolerance `η/2` gives `q₀`, the limits, the form-factor pairs, and
  `‖64π⁶F₂/e⁶ - chainRegMass‖ < η/2`; the triangle inequality concludes.

The link itself splits into the limit link and the Pauli link (`chainFixedLink_of_links`).
-/

@[expose] public section

open Complex Filter Topology
open scoped Real
open QED.WickModel (Params IsElectronOnShell IsPhotonOnShell)

namespace QED.ChainProof

/-- `a1SixSetB` is the helper constant `aSetB` (both inline `ζ(3)` as the same series). -/
theorem a1SixSetB_eq_aSetB : QED.VPChain.a1SixSetB = QED.Chain.aSetB := rfl

/-- **The iterated regulator limit in units of the electron mass** (the D-37.4 order, regulator
fermions last): for `m > 0` and every `η > 0` there is `R_M` such that for all `M₁, M₂ > R_M`
there are `δ > 0` and `Λ₀` with `|chainRegMass m m_γ Λ M₁ M₂ - aSetB| < η` for all
`m_γ ∈ (0, δ)` and `Λ > Λ₀`. -/
theorem chainRegMass_iterated_limit {m : ℝ} (hm : 0 < m) :
    ∀ η > 0, ∃ RM : ℝ, ∀ M₁ M₂ : ℝ, RM < M₁ → RM < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ →
        |chainRegMass m mγ Λ M₁ M₂ - QED.Chain.aSetB| < η := by
  intro η hη
  obtain ⟨R, hR⟩ := QED.Chain.ChainB.chainReg_iterated_limit η hη
  refine ⟨m * R, fun M₁ M₂ h1 h2 => ?_⟩
  have h1' : R < M₁ / m := by rw [lt_div_iff₀ hm]; linarith
  have h2' : R < M₂ / m := by rw [lt_div_iff₀ hm]; linarith
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hR (M₁ / m) (M₂ / m) h1' h2'
  refine ⟨m * δ, mul_pos hm hδ, m * Λ₀, fun mγ Λ hmγ hmδ hΛ => ?_⟩
  exact hΛ₀ (mγ / m) (Λ / m) (div_pos hmγ hm) (by rw [div_lt_iff₀ hm]; linarith)
    (by rw [lt_div_iff₀ hm]; linarith)

/-- **The fixed link from the limit link and the Pauli link.** The limit link gives the limits
and, through covariance and mirror symmetry, the form-factor pairs
(`QED.OneLoop.existsUnique_isFormFactorPair_of_mirror`); every pair is the pair of projections
(`QED.OneLoop.eq_formFactorProj_of_isFormFactorPair`), so the Pauli link bounds `F₂`. -/
theorem chainFixedLink_of_links (hL : ChainLimitLink) (hP : ChainPauliLink) : ChainFixedLink := by
  intro P hA η hη
  have he' : (P.e : ℂ) ≠ 0 := ofReal_ne_zero.mpr hA.he
  set c : ℂ := 64 * (π : ℂ) ^ 6 / (P.e : ℂ) ^ 6 with hc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc0 : c ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 6 hπ))
    (pow_ne_zero 6 he')
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  obtain ⟨q₀, hq₀, hall⟩ := hP P hA (η / ‖c‖) (by positivity)
  refine ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq => ?_⟩
  obtain ⟨hex, hcov⟩ := hL P hA p' p hp' hp hp0' hp0 hq
  refine ⟨hex, fun V hV => ⟨?_, fun F hF => ?_⟩⟩
  · obtain ⟨hV₁, hV₂⟩ := hcov V hV
    obtain ⟨F, hF, -⟩ := QED.OneLoop.existsUnique_isFormFactorPair_of_mirror hA.he hA.hm.ne' hp'
      hp hq hV₁ hV₂
    exact ⟨F, hF⟩
  · have hF2 : F.2 = QED.OneLoop.formFactorProj₂ P.e P.m p' p V := by
      rw [QED.OneLoop.eq_formFactorProj_of_isFormFactorPair hA.he hA.hm.ne' hp' hp hq hF]
    have hb := hall p' p hp' hp hp0' hp0 hq hqq V hV
    rw [← hF2] at hb
    have e1 : 64 * (π : ℂ) ^ 6 * F.2 / (P.e : ℂ) ^ 6 -
        (chainRegMass P.m P.mγ P.Λ P.M₁ P.M₂ : ℂ) =
        c * (F.2 - (P.e : ℂ) ^ 6 * (chainRegMass P.m P.mγ P.Λ P.M₁ P.M₂ : ℂ) /
          (64 * (π : ℂ) ^ 6)) := by
      simp only [hc]
      field_simp
    rw [e1, norm_mul]
    calc ‖c‖ * ‖F.2 - (P.e : ℂ) ^ 6 * (chainRegMass P.m P.mγ P.Λ P.M₁ P.M₂ : ℂ) /
          (64 * (π : ℂ) ^ 6)‖ < ‖c‖ * (η / ‖c‖) := mul_lt_mul_of_pos_left hb hcpos
      _ = η := by field_simp

/-- **The set (b) headline (HC₃) from the fixed link** (O3-15). The conclusion is, verbatim, the
proposition of the frozen `QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`. -/
theorem isFormFactorPair_vertexChain_two_pauli_limit_of_fixedLink (hlink : ChainFixedLink)
    (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
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
            (∃ V, QED.VPChain.IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V) ∧
            ∀ V, QED.VPChain.IsVertexChainLimit 2
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              ⟨![P₀.m, M₁, M₂], ![1, c₁, c₂], 0⟩ p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (QED.VPChain.a1SixSetB : ℂ)‖ < η := by
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨RM, hRM⟩ := chainRegMass_iterated_limit hm (η / 2) hη2
  refine ⟨RM, fun M₁ M₂ c₁ c₂ hM₁ hM₂ hRM₁ hRM₂ hPV₁ hPV₂ => ?_⟩
  obtain ⟨δ', hδ', Λ₀, hΛ₀⟩ := hRM M₁ M₂ hRM₁ hRM₂
  have h2m : 0 < 2 * P₀.m := by positivity
  refine ⟨min δ' (2 * P₀.m), lt_min hδ' h2m, max Λ₀ (min δ' (2 * P₀.m)),
    fun mγ Λ hmγ hΛ hδ hR => ?_⟩
  have hmδ' : mγ < δ' := lt_of_lt_of_le hδ (min_le_left _ _)
  have hm2 : mγ < 2 * P₀.m := lt_of_lt_of_le hδ (min_le_right _ _)
  have hΛ₀' : Λ₀ < Λ := lt_of_le_of_lt (le_max_left _ _) hR
  have hmΛ : mγ < Λ := hδ.trans (lt_of_le_of_lt (le_max_right _ _) hR)
  refine ⟨QED.TwoLoop.HeadlineAssembly.exists_counterterms P₀ he hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁
    hPV₂ mγ Λ hmγ hΛ, fun d₁ d₂ dm d₃ _hel _hch hph => ?_⟩
  set P : Params :=
    { P₀ with
      M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
      δm := dm, δ₃ := d₃ } with hP
  have hA : ChainAdmissible P :=
    { hm := hm, hmγ := hmγ, hΛ := hΛ, hM₁ := hM₁, hM₂ := hM₂, hPV₁ := hPV₁, hPV₂ := hPV₂,
      he := he, hmγΛ := hmΛ, hmγm := hm2, photon := hph }
  obtain ⟨q₀, hq₀, hfix⟩ := hlink P hA (η / 2) hη2
  refine ⟨q₀, hq₀, fun p' p hp' hp hp0' hp0 hq hqq => ?_⟩
  obtain ⟨hex, hall⟩ := hfix p' p hp' hp hp0' hp0 hq hqq
  refine ⟨hex, fun V hV => ⟨(hall V hV).1, fun F hF => ?_⟩⟩
  have hF := (hall V hV).2 F hF
  have hreg : |chainRegMass P₀.m mγ Λ M₁ M₂ - QED.Chain.aSetB| < η / 2 :=
    hΛ₀ mγ Λ hmγ hmδ' hΛ₀'
  have hreg' : ‖((chainRegMass P₀.m mγ Λ M₁ M₂ : ℝ) : ℂ) - (QED.VPChain.a1SixSetB : ℂ)‖ <
      η / 2 := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, a1SixSetB_eq_aSetB]
    exact hreg
  calc ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (QED.VPChain.a1SixSetB : ℂ)‖
      ≤ ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
          (chainRegMass P₀.m mγ Λ M₁ M₂ : ℂ)‖ +
        ‖((chainRegMass P₀.m mγ Λ M₁ M₂ : ℝ) : ℂ) - (QED.VPChain.a1SixSetB : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < η / 2 + η / 2 := add_lt_add hF hreg'
    _ = η := add_halves η

end QED.ChainProof

end
