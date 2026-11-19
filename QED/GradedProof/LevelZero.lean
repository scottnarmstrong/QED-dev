/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.CountertermsWithLevel
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.GradedProof.LevelOneElectron
public import QED.GradedProof.LevelOneCharge
public import QED.GradedProof.LevelOnePhoton
public import QED.GradedProof.LevelZeroPhoton
import QED.Frozen.WickModel.ElectronCountertermsExistsUnique
import QED.Frozen.OneLoop.ChargeConditionExistsUnique
import Mathlib.Tactic.FieldSimp

/-!
# The level-`0` counterterms of the graded model

Helper proof of the Phase 5 Stage 2 goal (G-ex₁) `QED.Graded.existsUnique_withLevel_zero`
(decision D-57), as `QED.GradedProof.existsUnique_withLevel_zero'`.

By (E-G₂ₛ), (E-G₂ₖ) and (E-G₂ₚ) (`isOnShellAt_one_iff'`, `isChargeNormalizedAt_one_iff'`,
`isPhotonOnShellAt_one_iff'`), `D.withLevel 0 x y` is renormalized through order `e²` exactly when
`x` is constant on the classes of `rep`, every flavour `f` with `rep f = f` satisfies T1's (Z₅)
and (K₀) at mass `M_f` with `δ₂ = e² d₂`, `δ_m = e² d_m`, `Z₁ = 1 + e² d₁`
(`LevelZeroCond`), and (F₁₁) holds at `δ₃ = e² y`
(`isRenormalizedThrough_withLevel_zero_iff`). The flavour conditions have exactly one solution
by the sealed (Z₆) and (K) at mass `M_f`, divided by `e²` (`existsUnique_levelZeroCond`); the
photon condition has exactly one by `QED.GradedProof.PhotonSplit.existsUnique_isPhotonOnShell`.
The solution is `x f = v (rep f)`, with `v b` the solution of flavour `b`.
-/

@[expose] public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof

variable {F : Type} [Fintype F] [DecidableEq F]

section WithLevel

variable (D : Counterterms F) (x : F → ℝ × ℝ × ℝ) (y : ℝ) (f : F)

omit [Fintype F] [DecidableEq F]

theorem withLevel_zero_d₁ : (D.withLevel 0 x y).d₁ f 0 = (x f).1 := by
  simp [Counterterms.withLevel]

theorem withLevel_zero_d₂ : (D.withLevel 0 x y).d₂ f 0 = (x f).2.1 := by
  simp [Counterterms.withLevel]

theorem withLevel_zero_dm : (D.withLevel 0 x y).dm f 0 = (x f).2.2 := by
  simp [Counterterms.withLevel]

theorem withLevel_zero_d₃ : (D.withLevel 0 x y).d₃ 0 = y := by
  simp [Counterterms.withLevel]

end WithLevel

/-- The order-`e²` conditions of a flavour of mass `M_b` on its level-`0` data
`v = (d₁, d₂, d_m)`: T1's (Z₅) with `δ₂ = e² d₂`, `δ_m = e² d_m` and (K₀) with `Z₁ = 1 + e² d₁`,
at mass `M_b`. -/
def LevelZeroCond (P : Params) (M : ℝ) (hM : 0 < M) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (v : ℝ × ℝ × ℝ) : Prop :=
  WickModel.IsElectronOnShell { P with m := M, δ₂ := P.e ^ 2 * v.2.1, δm := P.e ^ 2 * v.2.2 }
      hM hmγ hΛ ∧
    QED.OneLoop.IsChargeNormalized P.e (1 + P.e ^ 2 * v.1) M P.mγ P.Λ hM hmγ hΛ

/-- **The level-`0` conditions of one flavour have exactly one solution**: the sealed (Z₆) and (K)
at mass `M`, divided by `e²`. -/
theorem existsUnique_levelZeroCond (P : Params) (he : P.e ≠ 0) (M : ℝ) (hM : 0 < M)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) : ∃! v : ℝ × ℝ × ℝ, LevelZeroCond P M hM hmγ hΛ v := by
  have he2 : P.e ^ 2 ≠ 0 := pow_ne_zero 2 he
  obtain ⟨d, hd, hdu⟩ :=
    QED.WickModel.electronCounterterms_existsUnique { P with m := M } hM hmγ hΛ
  obtain ⟨Z, hZ, hZu⟩ := QED.OneLoop.existsUnique_isChargeNormalized P.e M P.mγ P.Λ he hM hmγ hΛ
  refine ⟨((Z - 1) / P.e ^ 2, d.1 / P.e ^ 2, d.2 / P.e ^ 2), ⟨?_, ?_⟩, ?_⟩
  · show WickModel.IsElectronOnShell
      { P with m := M, δ₂ := P.e ^ 2 * (d.1 / P.e ^ 2), δm := P.e ^ 2 * (d.2 / P.e ^ 2) } hM hmγ hΛ
    rw [mul_div_cancel₀ _ he2, mul_div_cancel₀ _ he2]
    exact hd
  · show QED.OneLoop.IsChargeNormalized P.e (1 + P.e ^ 2 * ((Z - 1) / P.e ^ 2)) M P.mγ P.Λ hM
      hmγ hΛ
    rw [mul_div_cancel₀ _ he2, add_sub_cancel]
    exact hZ
  · rintro ⟨v₁, v₂, v₃⟩ ⟨hon, hK⟩
    have h1 := hdu (P.e ^ 2 * v₂, P.e ^ 2 * v₃) hon
    have h2 := hZu _ hK
    subst h1 h2
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
    · field_simp

/-- **Renormalized through order `e²` at level `0`, unfolded** by (E-G₂ₛ), (E-G₂ₖ), (E-G₂ₚ). -/
theorem isRenormalizedThrough_withLevel_zero_iff (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hmass : ∀ f, 0 < Φ.mass f) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (x : (F → ℝ × ℝ × ℝ) × ℝ) :
    IsRenormalizedThrough P Φ (D.withLevel 0 x.1 x.2) rep 1 ↔
      (∀ f, x.1 f = x.1 (rep f)) ∧
        (∀ f, rep f = f → LevelZeroCond P (Φ.mass f) (hmass f) hmγ hΛ (x.1 f)) ∧
          Lepton.IsPhotonOnShell { P with δ₃ := P.e ^ 2 * x.2 } Φ := by
  have hflav : ∀ f, (IsOnShellAt P Φ (D.withLevel 0 x.1 x.2) f 1 ∧
      IsChargeNormalizedAt P Φ (D.withLevel 0 x.1 x.2) f 1) ↔
      LevelZeroCond P (Φ.mass f) (hmass f) hmγ hΛ (x.1 f) := fun f => by
    rw [isOnShellAt_one_iff' P Φ _ f (hmass f) hmγ hΛ,
      isChargeNormalizedAt_one_iff' P Φ _ f (hmass f) hmγ hΛ, withLevel_zero_d₁,
      withLevel_zero_d₂, withLevel_zero_dm]
    rfl
  have hph : IsPhotonOnShellAt P Φ (D.withLevel 0 x.1 x.2) 1 ↔
      Lepton.IsPhotonOnShell { P with δ₃ := P.e ^ 2 * x.2 } Φ := by
    rw [isPhotonOnShellAt_one_iff', withLevel_zero_d₃]
  unfold IsRenormalizedThrough
  refine and_congr ⟨fun h f => ?_, fun h f k hk => ?_⟩ ⟨fun h => ?_, fun h j hj1 hj2 => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h f 0 one_pos
    rw [withLevel_zero_d₁, withLevel_zero_d₁] at h1
    rw [withLevel_zero_d₂, withLevel_zero_d₂] at h2
    rw [withLevel_zero_dm, withLevel_zero_dm] at h3
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain rfl : k = 0 := by omega
    rw [withLevel_zero_d₁, withLevel_zero_d₁, withLevel_zero_d₂, withLevel_zero_d₂,
      withLevel_zero_dm, withLevel_zero_dm, ← h f]
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := h 1 le_rfl le_rfl
    exact ⟨fun f hf => (hflav f).1 (h1 f hf), hph.1 h2⟩
  · obtain rfl : j = 1 := le_antisymm hj2 hj1
    exact ⟨fun f hf => (hflav f).2 (h.1 f hf), hph.2 h.2⟩

/-- (G-ex₁) **The order-`e²` conditions fix the level-`0` counterterms.** -/
theorem existsUnique_withLevel_zero' (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (rep : F → F) (he : P.e ≠ 0) (hmass : ∀ f, 0 < Φ.mass f) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) :
    ∃! x : (F → ℝ × ℝ × ℝ) × ℝ, IsRenormalizedThrough P Φ (D.withLevel 0 x.1 x.2) rep 1 := by
  have hv := fun b => existsUnique_levelZeroCond P he (Φ.mass b) (hmass b) hmγ hΛ
  choose v hv₁ using fun b => (hv b).exists
  obtain ⟨y, hy, hyu⟩ :=
    PhotonSplit.existsUnique_isPhotonOnShell P he Φ hmass hPV₁ hPV₂
  refine ⟨(fun f => v (rep f), y), ?_, ?_⟩
  · beta_reduce
    rw [isRenormalizedThrough_withLevel_zero_iff P Φ D rep hmass hmγ hΛ]
    refine ⟨fun f => ?_, fun f hf => ?_, hy⟩
    · simp only [hrep]
    · simp only [hf]
      exact hv₁ f
  · rintro ⟨x, y'⟩ h
    rw [isRenormalizedThrough_withLevel_zero_iff P Φ D rep hmass hmγ hΛ] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine Prod.ext (funext fun f => ?_) (hyu y' h3)
    rw [h1 f]
    exact (hv (rep f)).unique (h2 (rep f) (hrep f)) (hv₁ (rep f))

end QED.GradedProof

end
