/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideDDCov
public import QED.ChainProof.HCBridge
import Mathlib.Tactic.Ring

/-!
# The three class links of (HC₃) from five representatives

Helper level, Phase 5 Stage 1a. The headline (HC₃) follows from `ClassLimitLink chainClassX`,
`ClassCovLink chainClassX` and `ChainPauliAtLink`
(`QED.ChainProof.isFormFactorPair_vertexChain_two_pauli_limit_of_classLinks`). This file reduces
all three to per-representative statements and discharges the four `δ₃`–`δ₃` representatives.

## Per-representative statements

For a representative `C` with class vertex `QED.ChainProof.HCValue.classV C`:

* `QED.ChainProof.HCLimit.RepLimit C` (existing): the `ε → 0⁺` limit exists;
* `RepNested C R`: at admissible parameters, for all small `Q > 0`, every limit `Y` of `classV C`
  at the canonical pair has Pauli projection `e² outerAt m Q (R P)`;
* `RepCov C`: the limits at `(p', p)` and `(L p', L p)` are related by every spinor-lifted `L`
  that keeps positive energies.

## Main statements

* `repNested_repDD`, `repCov_repDD`: **the four `δ₃`–`δ₃` representatives**, with the photon
  function `(δ₃²/4) s² D(s)³` (`QED.ChainProof.HCSide.formFactorProj₂_repDD`,
  `QED.ChainProof.HCSide.conj_classLimit_repDD`).
* `classNestedAtLink_enum_of_reps`, `classCovLink_chainClassX_of_reps`,
  `classLimitLink_chainClassX_of_reps`: the class links from the five remaining representatives
  (bubble–bubble, `repBD s`, `repDB s`), the signs of `enumClass` absorbed.
* **`classLinks_of_reps`**: the three links of
  `QED.ChainProof.isFormFactorPair_vertexChain_two_pauli_limit_of_classLinks` from `RepLimit`,
  `RepNested` and `RepCov` of `repBB`, `repBD s`, `repDB s`, with the photon functions
  `Π_loop(s)² s² D(s)³` (bubble–bubble) and `(δ₃/2) Π_loop(s) s² D(s)³` (each bubble–`δ₃` and
  `δ₃`–bubble representative; its class enters `enumClass` with the sign `-`).
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel (Params Contraction vacuumPolarizationLoop)
open QED.ChainProof.Enum QED.ChainProof.HCValue QED.ChainProof.HCLimit
open QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.Dirac
open QED.TwoLoop.UnitVPLink (photonD)

/-! ### Per-representative statements -/

/-- **The nested value of a representative at fixed `q`**: at admissible parameters, for all
small `Q > 0`, every `ε → 0⁺` limit of `classV C` at the canonical pair has Pauli projection
`e² outerAt m Q (R P)`. -/
def RepNested {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (R : Params → ℝ → ℝ) : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
    (∀ μ i j, Tendsto (fun ε => classV C { P with ε := ε } (boostMomentum P.m Q)
      (restMomentum P.m) μ i j) (𝓝[>] 0) (𝓝 (Y μ i j))) →
    QED.OneLoop.formFactorProj₂ P.e P.m (boostMomentum P.m Q) (restMomentum P.m) Y =
      ((P.e ^ 2 * outerAt P.m Q (R P) : ℝ) : ℂ)

/-- **Covariance of the limits of a representative**: for every spinor-lifted `L` that keeps
positive energies, the limits of `classV C` at `(p', p)` and `(L p', L p)` satisfy
`S Z^μ T = L^μ_ν Y^ν`. -/
def RepCov {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) : Prop :=
  ∀ P : Params, ChainAdmissible P →
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ P.m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ μ i j, Tendsto (fun ε => classV C { P with ε := ε } p' p μ i j) (𝓝[>] 0)
        (𝓝 (Y μ i j))) →
      (∀ μ i j, Tendsto (fun ε => classV C { P with ε := ε } (L *ᵥ p') (L *ᵥ p) μ i j)
        (𝓝[>] 0) (𝓝 (Z μ i j))) →
      ∀ μ, S * Z μ * T = vecAct L Y μ

/-! ### The `δ₃`–`δ₃` representatives -/

/-- The photon function of each `δ₃`–`δ₃` representative, `(δ₃²/4) s² D(s)³`. -/
noncomputable def ddPhoton (P : Params) (s : ℝ) : ℝ :=
  P.δ₃ ^ 2 / 4 * (s ^ 2 * photonD P.mγ P.Λ s ^ 3)

/-- **The nested value of the `δ₃`–`δ₃` representatives.** -/
theorem repNested_repDD (s₀ s₁ : Fin 2) : RepNested (repDD s₀ s₁) ddPhoton := by
  intro P hA
  filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
  intro Y hY
  have hpq := isPairQ_canonical' hA.hm hQ
  rw [formFactorProj₂_repDD s₀ s₁ hA hpq hY, dot_boostMomentum_sub_restMomentum hA.hm hQ.le]
  rfl

/-- **Covariance of the `δ₃`–`δ₃` representatives.** -/
theorem repCov_repDD (s₀ s₁ : Fin 2) : RepCov (repDD s₀ s₁) :=
  fun _ hA _ _ _ h _ _ hpq _ _ _ _ hY hZ μ => conj_classLimit_repDD s₀ s₁ hA h hpq hY hZ μ

/-! ### Signs -/

theorem formFactorProj₂_neg (e m : ℝ) (p' p : Fin 4 → ℝ) (Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    QED.OneLoop.formFactorProj₂ e m p' p (fun μ => -Y μ) =
      -QED.OneLoop.formFactorProj₂ e m p' p Y := by
  have h : (fun μ => -Y μ) = fun μ => (-1 : ℂ) • Y μ := funext fun μ => by simp
  rw [formFactorProj₂_eq_pauliNum, formFactorProj₂_eq_pauliNum, h, pauliNum_smul]
  ring

theorem outerAt_neg (m s : ℝ) (R : ℝ → ℝ) :
    outerAt m s (fun t => -R t) = -outerAt m s R := by
  have h := outerAt_const_mul m s (-1) R
  simp only [neg_one_mul] at h
  rw [h]

theorem vecAct_neg' (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : vecAct L (fun ν => -V ν) μ = -vecAct L V μ := by
  simp only [vecAct, smul_neg, Finset.sum_neg_distrib]

/-- `RepNested` for the negative class vertex `-classV C`, with the photon function negated. -/
theorem nested_neg {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}
    {R : Params → ℝ → ℝ} (h : RepNested C R) (P : Params) (hA : ChainAdmissible P) :
    ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ μ i j, Tendsto (fun ε => (-classV C { P with ε := ε } (boostMomentum P.m Q)
        (restMomentum P.m) μ) i j) (𝓝[>] 0) (𝓝 (Y μ i j))) →
      QED.OneLoop.formFactorProj₂ P.e P.m (boostMomentum P.m Q) (restMomentum P.m) Y =
        ((P.e ^ 2 * outerAt P.m Q (fun t => -R P t) : ℝ) : ℂ) := by
  filter_upwards [h P hA] with Q hQ
  intro Y hY
  have hY' : ∀ μ i j, Tendsto (fun ε => classV C { P with ε := ε } (boostMomentum P.m Q)
      (restMomentum P.m) μ i j) (𝓝[>] 0) (𝓝 ((fun ν => -Y ν) μ i j)) := fun μ i j => by
    simpa [Matrix.neg_apply] using (hY μ i j).neg
  have e := hQ _ hY'
  rw [formFactorProj₂_neg] at e
  rw [outerAt_neg, ← neg_neg (QED.OneLoop.formFactorProj₂ _ _ _ _ Y), e]
  push_cast
  ring

/-- `RepCov` for the negative class vertex `-classV C`. -/
theorem cov_neg {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ} (h : RepCov C)
    (P : Params) (hA : ChainAdmissible P) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (S T : Matrix (Fin 4) (Fin 4) ℂ) (hL : IsSpinLift L S T) (p' p : Fin 4 → ℝ)
    (hpq : IsPairQ P.m p' p) (h1 : 0 < (L *ᵥ p') 0) (h2 : 0 < (L *ᵥ p) 0)
    (Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hY : ∀ μ i j, Tendsto (fun ε => (-classV C { P with ε := ε } p' p μ) i j) (𝓝[>] 0)
      (𝓝 (Y μ i j)))
    (hZ : ∀ μ i j, Tendsto (fun ε => (-classV C { P with ε := ε } (L *ᵥ p') (L *ᵥ p) μ) i j)
      (𝓝[>] 0) (𝓝 (Z μ i j))) (μ : Fin 4) :
    S * Z μ * T = vecAct L Y μ := by
  have e := h P hA L S T hL p' p hpq h1 h2 (fun ν => -Y ν) (fun ν => -Z ν)
    (fun μ i j => by simpa [Matrix.neg_apply] using (hY μ i j).neg)
    (fun μ i j => by simpa [Matrix.neg_apply] using (hZ μ i j).neg) μ
  rw [vecAct_neg', Matrix.mul_neg, Matrix.neg_mul] at e
  exact neg_injective e

/-! ### The class links from the representatives -/

/-- The photon function of each bubble–`δ₃` and `δ₃`–bubble representative (before the sign of
its class): `(δ₃/2) Π_loop(s) s² D(s)³`. -/
noncomputable def sidePhoton (P : Params) (s : ℝ) : ℝ :=
  P.δ₃ / 2 * vacuumPolarizationLoop P s * s ^ 2 * photonD P.mγ P.Λ s ^ 3

theorem enumPhoton_side {r : Fin 9} (hr1 : 1 ≤ r.val) (hr4 : r.val ≤ 4) (P : Params) :
    enumPhoton r P = fun t => -sidePhoton P t := by
  funext t
  obtain ⟨r, hr⟩ := r
  simp only at hr1 hr4
  interval_cases r <;>
    simp [enumPhoton, enumCoeff, enumPow, sidePhoton] <;> ring

theorem enumPhoton_dd {r : Fin 9} (hr : 5 ≤ r.val) (P : Params) : enumPhoton r P = ddPhoton P := by
  funext t
  obtain ⟨r, hr'⟩ := r
  simp only at hr
  interval_cases r <;> simp [enumPhoton, enumCoeff, enumPow, ddPhoton] <;> ring

/-- The component `r` of `ClassNestedAtLink enumClass enumPhoton`. -/
def NestedAt (r : Fin 9) : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ Y,
    IsClassLimit enumClass r P (boostMomentum P.m Q) (restMomentum P.m) Y →
      QED.OneLoop.formFactorProj₂ P.e P.m (boostMomentum P.m Q) (restMomentum P.m) Y =
        ((P.e ^ 2 * outerAt P.m Q (enumPhoton r P) : ℝ) : ℂ)

theorem nestedAt_pos {r : Fin 9} {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}
    {R : Params → ℝ → ℝ} (hX : enumClass r = classV C) (hR : enumPhoton r = R)
    (hN : RepNested C R) : NestedAt r := by
  intro P hA
  rw [hR]
  refine (hN P hA).mono fun Q hQ Y hY => hQ Y fun μ i j => ?_
  have h := hY μ i j
  rw [hX] at h
  exact h

theorem nestedAt_neg {r : Fin 9} {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 1 κ}
    {R : Params → ℝ → ℝ} (hX : enumClass r = fun P p' p μ => -classV C P p' p μ)
    (hR : enumPhoton r = fun P t => -R P t) (hN : RepNested C R) : NestedAt r := by
  intro P hA
  rw [hR]
  refine (nested_neg hN P hA).mono fun Q hQ Y hY => hQ Y fun μ i j => ?_
  have h := hY μ i j
  rw [hX] at h
  exact h

theorem enumPhoton_side' {r : Fin 9} (hr1 : 1 ≤ r.val) (hr4 : r.val ≤ 4) :
    enumPhoton r = fun P t => -sidePhoton P t :=
  funext fun P => enumPhoton_side hr1 hr4 P

/-- **`ClassNestedAtLink enumClass enumPhoton` from the five remaining representatives.** -/
theorem classNestedAtLink_enum_of_reps
    (hBB : RepNested repBB (fun P => enumPhoton 0 P))
    (hBD : ∀ s, RepNested (repBD s) sidePhoton) (hDB : ∀ s, RepNested (repDB s) sidePhoton) :
    ClassNestedAtLink enumClass enumPhoton := by
  have h : ∀ r, NestedAt r := by
    intro r
    fin_cases r
    · exact nestedAt_pos (r := 0) rfl rfl hBB
    · exact nestedAt_neg (r := 1) rfl (enumPhoton_side' (by decide) (by decide)) (hBD 0)
    · exact nestedAt_neg (r := 2) rfl (enumPhoton_side' (by decide) (by decide)) (hBD 1)
    · exact nestedAt_neg (r := 3) rfl (enumPhoton_side' (by decide) (by decide)) (hDB 0)
    · exact nestedAt_neg (r := 4) rfl (enumPhoton_side' (by decide) (by decide)) (hDB 1)
    · exact nestedAt_pos (r := 5) rfl (funext fun P => enumPhoton_dd (by decide) P)
        (repNested_repDD 0 0)
    · exact nestedAt_pos (r := 6) rfl (funext fun P => enumPhoton_dd (by decide) P)
        (repNested_repDD 0 1)
    · exact nestedAt_pos (r := 7) rfl (funext fun P => enumPhoton_dd (by decide) P)
        (repNested_repDD 1 0)
    · exact nestedAt_pos (r := 8) rfl (funext fun P => enumPhoton_dd (by decide) P)
        (repNested_repDD 1 1)
  exact h

/-- **`ClassCovLink enumClass` from the five remaining representatives.** -/
theorem classCovLink_enum_of_reps (hBB : RepCov repBB) (hBD : ∀ s, RepCov (repBD s))
    (hDB : ∀ s, RepCov (repDB s)) : ClassCovLink enumClass := by
  intro r P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  fin_cases r
  · exact hBB P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  · exact cov_neg (hBD 0) P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  · exact cov_neg (hBD 1) P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  · exact cov_neg (hDB 0) P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  · exact cov_neg (hDB 1) P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  · exact repCov_repDD 0 0 P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  · exact repCov_repDD 0 1 P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  · exact repCov_repDD 1 0 P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ
  · exact repCov_repDD 1 1 P hA L S T hL p' p hpq h1 h2 Y Z hY hZ μ

/-- **`ClassCovLink chainClassX` from the five remaining representatives.** -/
theorem classCovLink_chainClassX_of_reps (hBB : RepCov repBB) (hBD : ∀ s, RepCov (repBD s))
    (hDB : ∀ s, RepCov (repDB s)) : ClassCovLink chainClassX :=
  enumClass_eq_chainClassX ▸ classCovLink_enum_of_reps hBB hBD hDB

/-- **`ClassLimitLink chainClassX` from the five remaining representatives.** -/
theorem classLimitLink_chainClassX_of_reps (hBB : RepLimit repBB) (hBD : ∀ s, RepLimit (repBD s))
    (hDB : ∀ s, RepLimit (repDB s)) : ClassLimitLink chainClassX :=
  enumClass_eq_chainClassX ▸ classLimitLink_enum_of_reps' hBB hBD hDB

/-- **The three class links of (HC₃) from the five remaining representatives**: the inputs of
`QED.ChainProof.isFormFactorPair_vertexChain_two_pauli_limit_of_classLinks`. -/
theorem classLinks_of_reps
    (hLBB : RepLimit repBB) (hLBD : ∀ s, RepLimit (repBD s)) (hLDB : ∀ s, RepLimit (repDB s))
    (hNBB : RepNested repBB (fun P => enumPhoton 0 P))
    (hNBD : ∀ s, RepNested (repBD s) sidePhoton) (hNDB : ∀ s, RepNested (repDB s) sidePhoton)
    (hCBB : RepCov repBB) (hCBD : ∀ s, RepCov (repBD s)) (hCDB : ∀ s, RepCov (repDB s)) :
    ClassLimitLink chainClassX ∧ ClassCovLink chainClassX ∧ ChainPauliAtLink :=
  ⟨classLimitLink_chainClassX_of_reps hLBB hLBD hLDB,
    classCovLink_chainClassX_of_reps hCBB hCBD hCDB,
    chainPauliAtLink_of_enum (classLimitLink_enum_of_reps' hLBB hLBD hLDB)
      (classNestedAtLink_enum_of_reps hNBB hNBD hNDB)⟩

end QED.ChainProof.HCSide

end
