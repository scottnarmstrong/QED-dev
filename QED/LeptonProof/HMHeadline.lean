/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMFixed
public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.Frozen.Lepton.IsVertexOrderFiveLimit
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.Lepton.A2Four
public import QED.Frozen.TwoLoop.A1Four
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Frozen.TwoLoop.VertexOrderFivePauliLimit
import QED.TwoLoop.CountertermScaling
import QED.Chain.HeavyVPValue

/-!
# The Stage 0 headline (HM₂)

Helper-level proof of the frozen goal
`QED.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit` (Phase 5 Stage 0, decision
D-50), under the distinct name
`QED.Lepton.Proof.isFormFactorPair_vertexOrderFive_lepton_pauli_limit'`, with the exact
statement.

## Proof

The sealed two-loop headline (HV₃) `QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit` is
used as a black box at tolerance `η/2`.

* **Flavour split** (`QED/LeptonProof/HMVertex.lean`): at every `ε > 0` the multi-lepton vertex is
  T1's vertex at `P` plus `∑_ℓ ∑_j w_{ℓ j}` T1 vertices at auxiliary parameter sets, each with an
  electron, Pauli–Villars regulators `(M_j, X_ℓ)` and the same counterterms; the auxiliary loop
  measures combine into each heavy lepton's own measure.
* **Photon condition** (`QED/LeptonProof/HMPhoton.lean`): (F₁₁) holds iff T1's (Z₈) holds at the
  shifted counterterm `δ₃ - ∑_ℓ π_ℓ`. So the counterterms of (HM₂) are those of (HV₃) with
  `δ₃` shifted, and (HV₃) applies to T1's vertex at the shifted counterterm.
* **The heavy bracket** (`QED/LeptonProof/HMBracket.lean`): the rest is a finite combination of T1
  vertices whose `q² → 0⁺` value is `∑_ℓ heavyUnitReg (m_ℓ/m) (m_γ/m) (Λ/m) (M_{ℓ,1}/m) (M_{ℓ,2}/m)`
  times `e⁴/(16π⁴)`; its regulator limit is `∑_ℓ A₂⁽⁴⁾(m/m_ℓ)`
  (`QED.Chain.HeavyVP.heavyUnitReg_iterated_limit_mass`, with `a2Four = a2Heavy` by definition),
  at tolerance `η/(4(n+1))` per lepton.
* **Assembly at fixed regulators** (`QED/LeptonProof/HMFixed.lean`): `η/2 + η/4 + η/4`.

The thresholds: `R_M` is the larger of (HV₃)'s and the heavy leptons'; `δ` the least of (HV₃)'s,
the heavy leptons', `1` and `2m`; `R` above (HV₃)'s, the heavy leptons' and `1`.
-/

@[expose] public section

open QED.WickModel (Params IsElectronOnShell)

namespace QED.Lepton.Proof

/-- (HM₂), the exact statement of the frozen goal
`QED.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit`. -/
theorem isFormFactorPair_vertexOrderFive_lepton_pauli_limit' {n : ℕ} (P₀ : Params)
    (mH : Fin n → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ) (η : ℝ)
    (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
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
              δm := dm, δ₃ := d₃ }
            (leptonFlavors
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩)) ∧
        ∀ d₁ d₂ dm d₃ : ℝ,
          IsElectronOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ } hm hmγ hΛ →
          QED.OneLoop.IsChargeNormalized P₀.e (1 + d₁) P₀.m mγ Λ hm hmγ hΛ →
          IsPhotonOnShell
            { P₀ with
              M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
              δm := dm, δ₃ := d₃ }
            (leptonFlavors
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              (leptonFlavors
                { P₀ with
                  M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                  δm := dm, δ₃ := d₃ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) p' p V) ∧
            ∀ V, IsVertexOrderFiveLimit
              { P₀ with
                M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                δm := dm, δ₃ := d₃ }
              (leptonFlavors
                { P₀ with
                  M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
                  δm := dm, δ₃ := d₃ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 -
                  ((QED.TwoLoop.a1Four + ∑ ℓ, a2Four (P₀.m / mH ℓ) : ℝ) : ℂ)‖ < η :=
by
  classical
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨RM₀, hRM₀⟩ :=
    QED.TwoLoop.isFormFactorPair_vertexOrderFive_pauli_limit P₀ he hm (η / 2) hη2
  set τH : ℝ := η / 4 / (n + 1) with hτH
  have hτH0 : 0 < τH := by positivity
  have hHl := fun ℓ => QED.Chain.HeavyVP.heavyUnitReg_iterated_limit_mass hm (hmH ℓ) τH hτH0
  choose RH hRH using hHl
  refine ⟨max RM₀ (∑ ℓ, |RH ℓ|), ?_⟩
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hR₁ hR₂ hPV₁ hPV₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hRH₁ hRH₂ hPVH₁ hPVH₂
  obtain ⟨δ₀, hδ₀, R₀, hT1⟩ := hRM₀ M₁ M₂ c₁ c₂ hM₁ hM₂ ((le_max_left _ _).trans_lt hR₁)
    ((le_max_left _ _).trans_lt hR₂) hPV₁ hPV₂
  have hle₁ : ∀ ℓ, RH ℓ < MH₁ ℓ := fun ℓ =>
    ((HM.le_sum_abs RH ℓ).trans (le_max_right _ _)).trans_lt (hRH₁ ℓ)
  have hle₂ : ∀ ℓ, RH ℓ < MH₂ ℓ := fun ℓ =>
    ((HM.le_sum_abs RH ℓ).trans (le_max_right _ _)).trans_lt (hRH₂ ℓ)
  have hH2 := fun ℓ => hRH ℓ (MH₁ ℓ) (MH₂ ℓ) (hle₁ ℓ) (hle₂ ℓ)
  choose δH hδH ΛH hΛH using hH2
  obtain ⟨δH', hδH', hδH'le⟩ := HM.exists_pos_le_forall δH hδH
  refine ⟨min (min δ₀ δH') (min 1 (2 * P₀.m)), lt_min (lt_min hδ₀ hδH') (lt_min one_pos
    (by positivity)), max R₀ (∑ ℓ, |ΛH ℓ|) + 1, fun mγ Λ hmγ hΛ hδ hR => ?_⟩
  have hmγ₀ : mγ < δ₀ := hδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hmγH : ∀ ℓ, mγ < δH ℓ := fun ℓ =>
    (hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))).trans_le (hδH'le ℓ)
  have hmγ1 : mγ < 1 := hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hmγm : mγ < 2 * P₀.m := hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hΛ₀ : R₀ < Λ := by linarith [le_max_left R₀ (∑ ℓ, |ΛH ℓ|)]
  have hΛH' : ∀ ℓ, ΛH ℓ < Λ := fun ℓ => by
    linarith [HM.le_sum_abs ΛH ℓ, le_max_right R₀ (∑ ℓ, |ΛH ℓ|)]
  have hΛ1 : 1 < Λ := by
    have : 0 ≤ max R₀ (∑ ℓ, |ΛH ℓ|) :=
      (Finset.sum_nonneg fun ℓ _ => abs_nonneg (ΛH ℓ)).trans (le_max_right _ _)
    linarith
  have hmΛ : mγ < Λ := hmγ1.trans hΛ1
  obtain ⟨hex, hall⟩ := hT1 mγ Λ hmγ hΛ hmγ₀ hΛ₀
  set Hl : Fin n → HeavyLepton := fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩ with hHl
  set Xa : Fin n → ℝ := fun ℓ => HM.auxMass (Hl ℓ) with hXa
  have hok : HM.AuxOK Hl Xa P₀.m := HM.auxOK_of hm hmH hMH₁ hMH₂ hPVH₁ hPVH₂
  have hgt : HM.AuxGt Hl Xa P₀.m := HM.auxGt_of hm hmH hMH₁ hMH₂
  -- the heavy bound
  have hheavy : |∑ ℓ, QED.Chain.HeavyVP.heavyUnitReg ((Hl ℓ).m / P₀.m) (mγ / P₀.m) (Λ / P₀.m)
      ((Hl ℓ).M₁ / P₀.m) ((Hl ℓ).M₂ / P₀.m) - ∑ ℓ, a2Four (P₀.m / (Hl ℓ).m)| < η / 4 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_lt ?_
    calc ∑ ℓ, |QED.Chain.HeavyVP.heavyUnitReg ((Hl ℓ).m / P₀.m) (mγ / P₀.m) (Λ / P₀.m)
          ((Hl ℓ).M₁ / P₀.m) ((Hl ℓ).M₂ / P₀.m) - a2Four (P₀.m / (Hl ℓ).m)|
        ≤ ∑ _ℓ : Fin n, τH := Finset.sum_le_sum fun ℓ _ =>
          (hΛH ℓ mγ Λ hmγ (hmγH ℓ) (hΛH' ℓ)).le
      _ = n * τH := by simp
      _ < η / 4 := by
        rw [hτH]
        have hn : (0 : ℝ) < n + 1 := by positivity
        rw [mul_div_assoc', div_lt_iff₀ hn]
        nlinarith
  refine ⟨?_, fun d₁ d₂ dm d₃ hel hch hph => ?_⟩
  · obtain ⟨d₁, d₂, dm, d₃', hel, hch, hph⟩ := hex
    set P' : Params :=
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃' } with hP'
    set πt : ℝ := ∑ ℓ, HM.heavyPi0 P' (Hl ℓ) (Xa ℓ) with hπt
    refine ⟨d₁, d₂, dm, d₃' + πt, ?_, hch, ?_⟩
    · exact (QED.TwoLoop.Scaling.isElectronOnShell_iff
        { P₀ with
          M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
          δm := dm, δ₃ := d₃' + πt } hm hmγ hΛ).2
        ((QED.TwoLoop.Scaling.isElectronOnShell_iff P' hm hmγ hΛ).1 hel)
    · refine (HM.isPhotonOnShell_leptonFlavors_iff_t1
        { P₀ with
          M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
          δm := dm, δ₃ := d₃' + πt } hm hM₁ hM₂ hPV₁ hPV₂ hok hgt).2 ?_
      have e : d₃' + πt - ∑ ℓ, HM.heavyPi0
          { P₀ with
            M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
            δm := dm, δ₃ := d₃' + πt } (Hl ℓ) (Xa ℓ) = d₃' := by
        rw [hπt]
        exact add_sub_cancel_right d₃' _
      simp only [e]
      exact hph
  · set P : Params :=
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } with hP
    have hPa : HM.T1Adm P := ⟨hm, hmγ, hmΛ, hmγm, hM₁, hM₂, hPV₁, hPV₂⟩
    have hph' := (HM.isPhotonOnShell_leptonFlavors_iff_t1 P hm hM₁ hM₂ hPV₁ hPV₂ hok hgt).1 hph
    have hel' : IsElectronOnShell (HM.shiftP P Hl Xa) hm hmγ hΛ :=
      (QED.TwoLoop.Scaling.isElectronOnShell_iff (HM.shiftP P Hl Xa) hm hmγ hΛ).2
        ((QED.TwoLoop.Scaling.isElectronOnShell_iff P hm hmγ hΛ).1 hel)
    have hT := hall d₁ d₂ dm (d₃ - ∑ ℓ, HM.heavyPi0 P (Hl ℓ) (Xa ℓ)) hel' hch hph'
    exact HM.fixed_clause P hPa he hok hgt hMH₂ hη hT hheavy

end QED.Lepton.Proof

end
