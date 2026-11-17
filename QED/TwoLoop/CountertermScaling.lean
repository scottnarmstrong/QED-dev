/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.WickModel.ElectronOnShell
public import QED.WickModel.PhotonOnShell
public import QED.OneLoop.ChargeCondition
import QED.Frozen.WickModel.SelfEnergyABSpec
import QED.Frozen.WickModel.VacuumPolarizationSpec
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Homogeneity of the counterterms in the charge

Obligation O2-27, items 1 and 2 (`docs/TWO-LOOP-DERIVATION.md`, section 5.1; decision D-37.3).
At fixed regulators `m, m_γ, Λ, M₁, M₂, c₁, c₂` the frozen conditions fix the single real
counterterms, and each is `e²` times a number independent of `e`:

* the electron on-shell conditions (Z₅) `QED.WickModel.IsElectronOnShell` fix `δ₂` and `δ_m`;
* the photon on-shell condition (Z₈) `QED.WickModel.IsPhotonOnShell` fixes `δ₃`;
* the charge condition (K₀) `QED.OneLoop.IsChargeNormalized e (1 + δ₁) …` fixes `δ₁` (for
  `e ≠ 0`).

Each condition is affine in its counterterm, with a source proportional to `e²`: the loop
coefficients `A_loop`, `B_loop` of the self-energy, `Π_loop` of the vacuum polarization and the
`γ^μ` coefficient `A₀` of the one-loop vertex at `q = 0` all carry the factor `e²`, and the
charge condition reads `e (δ₁ + A₀) ū γ^μ u = 0`.

With `δᵢ = e² dᵢ`, every vertex factor (V₁₉) of kind `κ` is `e ^ κ.order` times the factor at
`e = 1` with the `dᵢ`, so the part of the two-loop 1PI function (T₁₁) of total order exactly
`K + 1` is `e ^ (K + 1)` times its value at `e = 1`.

## Main definitions

* `QED.TwoLoop.Scaling.orderPart`: the part of the 1PI function of total order exactly `j`.

## Main statements

* `QED.TwoLoop.Scaling.electronCounterterms_eq_sq_mul`,
  `QED.TwoLoop.Scaling.photonCounterterm_eq_sq_mul`,
  `QED.TwoLoop.Scaling.chargeCounterterm_eq_sq_mul`: an admissible counterterm at charge `e` is
  `e²` times an admissible counterterm at charge `1`.
* `QED.TwoLoop.Scaling.isElectronOnShell_scale`, `QED.TwoLoop.Scaling.isPhotonOnShell_scale`,
  `QED.TwoLoop.Scaling.isChargeNormalized_scale`: conversely, `e²` times an admissible
  counterterm at charge `1` is admissible at charge `e`.
* `QED.TwoLoop.Scaling.counterterms_eq_sq_mul`: the four statements together.
* `QED.TwoLoop.Scaling.vertexFactor_scale`: the per-vertex scaling.
* `QED.TwoLoop.Scaling.onePIFunction₂_succ_sub`: with `δᵢ = e² dᵢ`, the part of the 1PI
  function of total order exactly `K + 1` is `e ^ (K + 1)` times its value at `e = 1`.
* `QED.TwoLoop.Scaling.onePIFunction₂_five_sub_four_of_conditions`: the order-exactly-5 vertex
  with counterterms fixed by the frozen conditions is `e⁵` times the vertex at `e = 1` with the
  counterterms fixed by the same conditions at `e = 1`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory
open QED.WickModel
open scoped Real

namespace QED.TwoLoop.Scaling

/-! ### The electron counterterms -/

/-- The real part of the self-energy coefficient `A_loop` is `e²` times its value at `e = 1`. -/
theorem re_selfEnergyLoopA (P : Params) (d₁ d₂ dm d₃ s : ℝ) :
    (selfEnergyLoopA P s).re = P.e ^ 2 *
      (selfEnergyLoopA { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } s).re := by
  simp only [selfEnergyLoopA, ofReal_re]
  ring

/-- The real part of the self-energy coefficient `B_loop` is `e²` times its value at `e = 1`. -/
theorem re_selfEnergyLoopB (P : Params) (d₁ d₂ dm d₃ s : ℝ) :
    (selfEnergyLoopB P s).re = P.e ^ 2 *
      (selfEnergyLoopB { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } s).re := by
  simp only [selfEnergyLoopB, ofReal_re]
  ring

/-- The on-shell `δ₂` is `e²` times its value at `e = 1`. -/
theorem onShellδ₂_eq (P : Params) (d₁ d₂ dm d₃ : ℝ) :
    onShellδ₂ P = P.e ^ 2 *
      onShellδ₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } := by
  have hA : (fun s => (selfEnergyLoopA P s).re) = fun s => P.e ^ 2 *
      (selfEnergyLoopA { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } s).re :=
    funext fun s => re_selfEnergyLoopA P d₁ d₂ dm d₃ s
  have hB : (fun s => (selfEnergyLoopB P s).re) = fun s => P.e ^ 2 *
      (selfEnergyLoopB { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } s).re :=
    funext fun s => re_selfEnergyLoopB P d₁ d₂ dm d₃ s
  simp only [onShellδ₂, hB, deriv_const_mul_field', re_selfEnergyLoopA P d₁ d₂ dm d₃]
  ring

/-- The on-shell `δ_m` is `e²` times its value at `e = 1`. -/
theorem onShellδm_eq (P : Params) (d₁ d₂ dm d₃ : ℝ) :
    onShellδm P = P.e ^ 2 *
      onShellδm { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } := by
  have hA : (fun s => (selfEnergyLoopA P s).re) = fun s => P.e ^ 2 *
      (selfEnergyLoopA { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } s).re :=
    funext fun s => re_selfEnergyLoopA P d₁ d₂ dm d₃ s
  have hB : (fun s => (selfEnergyLoopB P s).re) = fun s => P.e ^ 2 *
      (selfEnergyLoopB { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } s).re :=
    funext fun s => re_selfEnergyLoopB P d₁ d₂ dm d₃ s
  simp only [onShellδm, hA, deriv_const_mul_field', re_selfEnergyLoopB P d₁ d₂ dm d₃]
  ring

/-- **The electron on-shell conditions in closed form.** For `m, m_γ, Λ > 0`, the electron is on
shell (Z₅) exactly when `δ₂ = onShellδ₂ P` and `δ_m = onShellδm P`. -/
theorem isElectronOnShell_iff (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    IsElectronOnShell P hm hmγ hΛ ↔ P.δ₂ = onShellδ₂ P ∧ P.δm = onShellδm P := by
  have hμ := lt_min hmγ hΛ
  have hab : -P.m - min P.mγ P.Λ / 2 ≤ -P.m + min P.mγ P.Λ / 2 := by linarith
  have hx : -P.m ∈ Set.Ioo (-P.m - min P.mγ P.Λ / 2) (-P.m + min P.mγ P.Λ / 2) := by
    constructor <;> linarith
  have hAB : selfEnergyAB P hm hmγ hΛ =
      fun s => (selfEnergyLoopA P s.1 - P.δ₂, selfEnergyLoopB P s.1 - P.δm) :=
    eq_selfEnergyLoop_of_tendsto P hm hmγ hΛ (selfEnergyAB_spec P hm hmγ hΛ).1
  have hslash : ∀ z hz, selfEnergySlash P hm hmγ hΛ z hz =
      (selfEnergyLoopA P (-z ^ 2) - P.δ₂) * z + (selfEnergyLoopB P (-z ^ 2) - P.δm) * P.m := by
    intro z hz
    rw [selfEnergySlash, hAB]
  refine Iff.trans ?_ (selfEnergyLoop_onShell_iff P hm hmγ hΛ P.δ₂ P.δm)
  unfold IsElectronOnShell
  simp only [hslash]
  exact and_congr Iff.rfl (hasDerivAt_comp_projIcc_iff
    (f := fun z : ℝ => (selfEnergyLoopA P (-z ^ 2) - P.δ₂) * z
      + (selfEnergyLoopB P (-z ^ 2) - P.δm) * P.m) hab hx)

/-- **Homogeneity of the electron counterterms (O2-27, item 1).** At fixed `m, m_γ, Λ > 0`, if the
electron is on shell (Z₅) at charge `e` with counterterms `(δ₂, δ_m)`, and on shell at charge `1`
with counterterms `(d₂, d_m)`, then `δ₂ = e² d₂` and `δ_m = e² d_m`. -/
theorem electronCounterterms_eq_sq_mul (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {d₁ d₂ dm d₃ : ℝ} (h : IsElectronOnShell P hm hmγ hΛ)
    (hd : IsElectronOnShell { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hmγ hΛ) :
    P.δ₂ = P.e ^ 2 * d₂ ∧ P.δm = P.e ^ 2 * dm := by
  obtain ⟨h₂, hm'⟩ := (isElectronOnShell_iff P hm hmγ hΛ).1 h
  obtain ⟨hd₂, hdm⟩ :=
    (isElectronOnShell_iff { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } hm hmγ hΛ).1 hd
  refine ⟨?_, ?_⟩
  · rw [h₂, onShellδ₂_eq P d₁ d₂ dm d₃, ← hd₂]
  · rw [hm', onShellδm_eq P d₁ d₂ dm d₃, ← hdm]

/-- **Scaling of the electron counterterms.** If the electron is on shell (Z₅) at charge `1` with
counterterms `(d₂, d_m)`, it is on shell at charge `e` with counterterms `(e² d₂, e² d_m)`. -/
theorem isElectronOnShell_scale (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {d₁ d₂ dm d₃ : ℝ}
    (hd : IsElectronOnShell { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hmγ hΛ) :
    IsElectronOnShell { P with δ₂ := P.e ^ 2 * d₂, δm := P.e ^ 2 * dm } hm hmγ hΛ := by
  obtain ⟨hd₂, hdm⟩ :=
    (isElectronOnShell_iff { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } hm hmγ hΛ).1 hd
  refine (isElectronOnShell_iff { P with δ₂ := P.e ^ 2 * d₂, δm := P.e ^ 2 * dm }
    hm hmγ hΛ).2 ⟨?_, ?_⟩
  · rw [onShellδ₂_eq { P with δ₂ := P.e ^ 2 * d₂, δm := P.e ^ 2 * dm } d₁ d₂ dm d₃]
    exact congrArg (P.e ^ 2 * ·) hd₂
  · rw [onShellδm_eq { P with δ₂ := P.e ^ 2 * d₂, δm := P.e ^ 2 * dm } d₁ d₂ dm d₃]
    exact congrArg (P.e ^ 2 * ·) hdm

/-! ### The photon counterterm -/

/-- The vacuum polarization coefficient `Π_loop` is `e²` times its value at `e = 1`. -/
theorem vacuumPolarizationLoop_eq (P : Params) (d₁ d₂ dm d₃ s : ℝ) :
    vacuumPolarizationLoop P s = P.e ^ 2 *
      vacuumPolarizationLoop { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } s := by
  simp only [vacuumPolarizationLoop, Params.loopCoeff, Params.mass]
  ring

/-- **The photon on-shell condition in closed form.** Under the conditions of (Z₂), the photon is
on shell (Z₈) exactly when `δ₃ = Π_loop(0)`. -/
theorem isPhotonOnShell_iff (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂ ↔ P.δ₃ = vacuumPolarizationLoop P 0 := by
  have hPol : vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ =
      fun s => -(P.δ₃ : ℂ) + (vacuumPolarizationLoop P s.1 : ℂ) :=
    eq_vacuumPolarizationLoop_of_tendsto P hm hM₁ hM₂ hPV₁ hPV₂
      (vacuumPolarization_spec P hm hM₁ hM₂ hPV₁ hPV₂).1
  unfold IsPhotonOnShell
  rw [hPol]
  exact vacuumPolarizationLoop_onShell_iff P P.δ₃

/-- **Homogeneity of the photon counterterm (O2-27, item 1).** Under the conditions of (Z₂), if
the photon is on shell (Z₈) at charge `e` with counterterm `δ₃` and on shell at charge `1` with
counterterm `d₃`, then `δ₃ = e² d₃`. -/
theorem photonCounterterm_eq_sq_mul (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {d₁ d₂ dm d₃ : ℝ}
    (h : IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂)
    (hd : IsPhotonOnShell { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hM₁ hM₂ hPV₁ hPV₂) :
    P.δ₃ = P.e ^ 2 * d₃ := by
  rw [(isPhotonOnShell_iff P hm hM₁ hM₂ hPV₁ hPV₂).1 h, vacuumPolarizationLoop_eq P d₁ d₂ dm d₃,
    ← (isPhotonOnShell_iff { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hM₁ hM₂ hPV₁ hPV₂).1 hd]

/-- **Scaling of the photon counterterm.** If the photon is on shell (Z₈) at charge `1` with
counterterm `d₃`, it is on shell at charge `e` with counterterm `e² d₃`. -/
theorem isPhotonOnShell_scale (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {d₁ d₂ dm d₃ : ℝ}
    (hd : IsPhotonOnShell { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hM₁ hM₂ hPV₁ hPV₂) :
    IsPhotonOnShell { P with δ₃ := P.e ^ 2 * d₃ } hm hM₁ hM₂ hPV₁ hPV₂ := by
  refine (isPhotonOnShell_iff { P with δ₃ := P.e ^ 2 * d₃ } hm hM₁ hM₂ hPV₁ hPV₂).2 ?_
  rw [vacuumPolarizationLoop_eq { P with δ₃ := P.e ^ 2 * d₃ } d₁ d₂ dm d₃]
  exact congrArg (P.e ^ 2 * ·)
    ((isPhotonOnShell_iff { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hM₁ hM₂ hPV₁ hPV₂).1 hd)

/-! ### The vertex counterterm -/

open QED.OneLoop.VertexLimit in
/-- The `γ^μ` coefficient `A₀` of the one-loop vertex at `q = 0` is `e²` times its value at
`e = 1`. -/
theorem chargeA0_eq (e m mγ Λ : ℝ) : chargeA0 e m mγ Λ = e ^ 2 * chargeA0 1 m mγ Λ := by
  simp only [chargeA0]
  ring

open QED.OneLoop.VertexLimit in
/-- **Homogeneity of the vertex counterterm (O2-27, item 1).** At fixed `m, m_γ, Λ > 0` and for
`e ≠ 0`, if the charge condition (K₀) holds at charge `e` with `Z₁ = 1 + δ₁` and at charge `1`
with `Z₁ = 1 + d₁`, then `δ₁ = e² d₁`. -/
theorem chargeCounterterm_eq_sq_mul {e δ₁ d₁ m mγ Λ : ℝ} (he : e ≠ 0) (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (h : QED.OneLoop.IsChargeNormalized e (1 + δ₁) m mγ Λ hm hmγ hΛ)
    (hd : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) m mγ Λ hm hmγ hΛ) :
    δ₁ = e ^ 2 * d₁ := by
  have h1 := eq_chargeZ_of_isChargeNormalized he hm hmγ hΛ h
  have h2 := eq_chargeZ_of_isChargeNormalized one_ne_zero hm hmγ hΛ hd
  simp only [chargeZ] at h1 h2
  rw [chargeA0_eq e] at h1
  linear_combination h1 - e ^ 2 * h2

open QED.OneLoop.VertexLimit in
/-- **Scaling of the vertex counterterm.** If the charge condition (K₀) holds at charge `1` with
`Z₁ = 1 + d₁`, it holds at every charge `e` with `Z₁ = 1 + e² d₁`. -/
theorem isChargeNormalized_scale {e d₁ m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hd : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) m mγ Λ hm hmγ hΛ) :
    QED.OneLoop.IsChargeNormalized e (1 + e ^ 2 * d₁) m mγ Λ hm hmγ hΛ := by
  have h2 := eq_chargeZ_of_isChargeNormalized one_ne_zero hm hmγ hΛ hd
  have h : 1 + e ^ 2 * d₁ = chargeZ e m mγ Λ := by
    simp only [chargeZ] at h2 ⊢
    rw [chargeA0_eq e]
    linear_combination e ^ 2 * h2
  rw [h]
  exact isChargeNormalized_chargeZ hm hmγ hΛ

/-! ### All four counterterms -/

/-- **Homogeneity of the counterterms (O2-27, item 1).** At fixed regulators, with `e ≠ 0`: if
the counterterms of `P` satisfy the frozen conditions (Z₅), (Z₈) and (K₀) at charge `e`, and
`d₁, d₂, d_m, d₃` satisfy the same conditions at charge `1`, then `δᵢ = e² dᵢ` for each `i`. -/
theorem counterterms_eq_sq_mul (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (he : P.e ≠ 0)
    (hel : IsElectronOnShell P hm hmγ hΛ) (hph : IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂)
    (hch : QED.OneLoop.IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ)
    {d₁ d₂ dm d₃ : ℝ}
    (hel₁ : IsElectronOnShell { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hmγ hΛ)
    (hph₁ : IsPhotonOnShell { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hM₁ hM₂ hPV₁ hPV₂)
    (hch₁ : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ) :
    P.δ₁ = P.e ^ 2 * d₁ ∧ P.δ₂ = P.e ^ 2 * d₂ ∧ P.δm = P.e ^ 2 * dm ∧ P.δ₃ = P.e ^ 2 * d₃ :=
  have hel' := electronCounterterms_eq_sq_mul P hm hmγ hΛ hel hel₁
  ⟨chargeCounterterm_eq_sq_mul he hm hmγ hΛ hch hch₁, hel'.1, hel'.2,
    photonCounterterm_eq_sq_mul P hm hM₁ hM₂ hPV₁ hPV₂ hph hph₁⟩

/-! ### The vertex factors and the order-graded 1PI function -/

/-- Every vertex kind has order at least `1`. -/
theorem one_le_order (k : Wick.VertexKind) : 1 ≤ k.order := by
  cases k <;> simp [Wick.VertexKind.order]

/-- A term with `N` vertices has total order at least `N`. -/
theorem le_sum_order {N : ℕ} (κ : Fin N → Wick.VertexKind) : N ≤ ∑ t, (κ t).order :=
  calc N = ∑ _t : Fin N, 1 := by simp
    _ ≤ ∑ t, (κ t).order := Finset.sum_le_sum fun t _ => one_le_order (κ t)

/-- **The per-vertex scaling.** With counterterms `δᵢ = e² dᵢ`, the vertex factor (V₁₉) of a
vertex of kind `κ t` is `e ^ (κ t).order` times the factor at `e = 1` with counterterms `dᵢ`:
`i e γ` (order `1`), `i (e² d₁) e γ` (order `3`), `-i (e² d₂ k̸ + e² d_m m)` (order `2`) and
`-(i/2) e² d₃ (k² g - k k)` (order `2`). -/
theorem vertexFactor_scale (e d₁ d₂ dm d₃ m : ℝ) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) :
    Wick.vertexFactor e (e ^ 2 * d₁) (e ^ 2 * d₂) (e ^ 2 * dm) (e ^ 2 * d₃) m α β lor kψ kA t
      = (e : ℂ) ^ (κ t).order * Wick.vertexFactor 1 d₁ d₂ dm d₃ m α β lor kψ kA t := by
  unfold Wick.vertexFactor
  split <;> rename_i h <;>
    simp only [h, Wick.VertexKind.order, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    push_cast <;> ring

/-- The product of the vertex factors is `e` to the total order times the product at `e = 1`. -/
theorem prod_vertexFactor_scale (e d₁ d₂ dm d₃ m : ℝ) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) :
    ∏ t, Wick.vertexFactor e (e ^ 2 * d₁) (e ^ 2 * d₂) (e ^ 2 * dm) (e ^ 2 * d₃) m α β lor kψ kA t
      = (e : ℂ) ^ (∑ t, (κ t).order) *
        ∏ t, Wick.vertexFactor 1 d₁ d₂ dm d₃ m α β lor kψ kA t := by
  simp_rw [vertexFactor_scale]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- With `δᵢ = e² dᵢ`, the amplitude (T₇) of a flavored contraction is `e` to the total order times
the amplitude at `e = 1` with counterterms `dᵢ`. -/
theorem contractionAmplitude₂_scale (P : Params) {d₁ d₂ dm d₃ : ℝ}
    (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
    (h₃ : P.δ₃ = P.e ^ 2 * d₃)
    {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ P C φ pIn kIn k αOut βIn μ = (P.e : ℂ) ^ (∑ t, (κ t).order) *
      contractionAmplitude₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
        C φ pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude₂
  simp only [Params.mass]
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun lor _ => ?_
  rw [h₁, h₂, hδm, h₃, prod_vertexFactor_scale]
  ring

/-- With `δᵢ = e² dᵢ`, the regulated amplitude (T₈) is `e` to the total order times the regulated
amplitude at `e = 1` with counterterms `dᵢ`; the regulator weights do not involve `e`. -/
theorem regulatedAmplitude₂_scale (P : Params) {d₁ d₂ dm d₃ : ℝ}
    (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
    (h₃ : P.δ₃ = P.e ^ 2 * d₃)
    {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P C pIn kIn k αOut βIn μ = (P.e : ℂ) ^ (∑ t, (κ t).order) *
      regulatedAmplitude₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
        C pIn kIn k αOut βIn μ := by
  unfold regulatedAmplitude₂
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun φ _ => ?_
  rw [contractionAmplitude₂_scale P h₁ h₂ hδm h₃]
  have hw : loopWeight P C φ =
      loopWeight { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } C φ := rfl
  rw [hw]
  ring

/-- With `δᵢ = e² dᵢ`, the value (T₁₀) of a contraction is `e` to the total order times its value
at `e = 1` with counterterms `dᵢ`. -/
theorem contractionValue₂_scale (P : Params) {d₁ d₂ dm d₃ : ℝ}
    (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
    (h₃ : P.δ₃ = P.e ^ 2 * d₃)
    {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue₂ P C pOut pIn kIn αOut βIn μ = (P.e : ℂ) ^ (∑ t, (κ t).order) *
      contractionValue₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
        C pOut pIn kIn αOut βIn μ := by
  unfold contractionValue₂ QED.TwoLoop.jointEnergyFirstIntegral
  simp_rw [regulatedAmplitude₂_scale P h₁ h₂ hδm h₃]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring

open scoped Classical in
/-- The part of the 1PI function (T₁₁) of total order exactly `j` in `e`: the sum over the 1PI
Wick contractions of the terms of total order exactly `j`. Every vertex has order at least `1`,
so these terms have at most `j` vertices. -/
noncomputable def orderPart (P : Params) (nf nA j : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (j + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order = j),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * contractionValue₂ P C pOut pIn kIn αOut βIn μ

/-- Splitting a sum over the terms of total order at most `K` by their order. -/
theorem sum_filter_order_le {N : ℕ} (K : ℕ) (F : (Fin N → Wick.VertexKind) → ℂ) :
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K), F κ
      = ∑ j ∈ Finset.range (K + 1), ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order = j), F κ := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun κ : Fin N → Wick.VertexKind => ∑ t, (κ t).order)
    (t := Finset.range (K + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun κ _ => ?_) fun _ _ => rfl
    rw [Finset.mem_range] at hj
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by omega, h⟩
  · intro κ hκ
    rw [Finset.mem_filter] at hκ
    rw [Finset.mem_range]
    omega

/-- **The 1PI function graded by order.** The 1PI function (T₁₁) truncated at order `K` is the sum
of its parts of total order exactly `j ≤ K`. -/
theorem onePIFunction₂_eq_sum_orderPart (P : Params) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    onePIFunction₂ P nf nA K pOut pIn kIn αOut βIn μ
      = ∑ j ∈ Finset.range (K + 1), orderPart P nf nA j pOut pIn kIn αOut βIn μ := by
  unfold onePIFunction₂ orderPart
  simp_rw [sum_filter_order_le K, Finset.mul_sum (s := Finset.range (K + 1))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun N _ hN => ?_
  rw [Finset.mem_range, not_lt] at hN
  rw [Finset.sum_eq_zero, mul_zero]
  intro κ hκ
  rw [Finset.mem_filter] at hκ
  have := le_sum_order κ
  omega

/-- With `δᵢ = e² dᵢ`, the part of total order exactly `j` is `e ^ j` times the same part at
`e = 1` with counterterms `dᵢ`. -/
theorem orderPart_scale (P : Params) {d₁ d₂ dm d₃ : ℝ}
    (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
    (h₃ : P.δ₃ = P.e ^ 2 * d₃)
    (nf nA j : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    orderPart P nf nA j pOut pIn kIn αOut βIn μ
      = (P.e : ℂ) ^ j *
        orderPart { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
          nf nA j pOut pIn kIn αOut βIn μ := by
  unfold orderPart
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun N _ => ?_
  rw [mul_left_comm ((P.e : ℂ) ^ j)]
  refine congrArg (fun x : ℂ => (N.factorial : ℂ)⁻¹ * x) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [Finset.mem_filter] at hκ
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun C _ => ?_
  rw [contractionValue₂_scale P h₁ h₂ hδm h₃, hκ.2]
  ring

/-- **The order-graded 1PI function at `δᵢ = e² dᵢ`.** The 1PI function (T₁₁) truncated at order
`K` is `∑_{j ≤ K} e ^ j W_j`, with `W_j` the part of total order exactly `j` at `e = 1` with
counterterms `dᵢ`, which does not involve `e`. -/
theorem onePIFunction₂_eq_sum_pow (P : Params) {d₁ d₂ dm d₃ : ℝ}
    (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
    (h₃ : P.δ₃ = P.e ^ 2 * d₃)
    (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    onePIFunction₂ P nf nA K pOut pIn kIn αOut βIn μ
      = ∑ j ∈ Finset.range (K + 1),
        (P.e : ℂ) ^ j *
          orderPart { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
            nf nA j pOut pIn kIn αOut βIn μ := by
  rw [onePIFunction₂_eq_sum_orderPart]
  exact Finset.sum_congr rfl fun j _ =>
    orderPart_scale P h₁ h₂ hδm h₃ nf nA j pOut pIn kIn αOut βIn μ

/-- **Extraction (O2-27, item 2).** With `δᵢ = e² dᵢ`, the part of the 1PI function (T₁₁) of total
order exactly `K + 1` is `e ^ (K + 1)` times the same part at `e = 1` with counterterms `dᵢ`. -/
theorem onePIFunction₂_succ_sub (P : Params) {d₁ d₂ dm d₃ : ℝ}
    (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
    (h₃ : P.δ₃ = P.e ^ 2 * d₃)
    (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    onePIFunction₂ P nf nA (K + 1) pOut pIn kIn αOut βIn μ
        - onePIFunction₂ P nf nA K pOut pIn kIn αOut βIn μ
      = (P.e : ℂ) ^ (K + 1) *
        (onePIFunction₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
            nf nA (K + 1) pOut pIn kIn αOut βIn μ
          - onePIFunction₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
            nf nA K pOut pIn kIn αOut βIn μ) := by
  simp only [onePIFunction₂_eq_sum_orderPart, Finset.sum_range_succ _ (K + 1), add_sub_cancel_left]
  exact orderPart_scale P h₁ h₂ hδm h₃ nf nA (K + 1) pOut pIn kIn αOut βIn μ

/-- **The order-exactly-5 vertex (O2-27, item 2).** With `δᵢ = e² dᵢ`, the order-exactly-5 part of
the 1PI vertex function (T₁₁) is `e⁵` times its value at `e = 1` with counterterms `dᵢ`. -/
theorem onePIFunction₂_five_sub_four (P : Params) {d₁ d₂ dm d₃ : ℝ}
    (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
    (h₃ : P.δ₃ = P.e ^ 2 * d₃)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin 1 → Fin 4) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ - onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ
      = (P.e : ℂ) ^ 5 *
        (onePIFunction₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
          1 1 5 pOut pIn kIn αOut βIn μ
          - onePIFunction₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
            1 1 4 pOut pIn kIn αOut βIn μ) :=
  onePIFunction₂_succ_sub P h₁ h₂ hδm h₃ 1 1 4 pOut pIn kIn αOut βIn μ

/-- **The order-exactly-5 vertex with the frozen counterterms (O2-27, items 1–2).** At fixed
regulators, with `e ≠ 0`: if the counterterms of `P` satisfy the frozen conditions (Z₅), (Z₈) and
(K₀) at charge `e`, and `d₁, d₂, d_m, d₃` satisfy them at charge `1`, then the order-exactly-5
part of the 1PI vertex function (T₁₁) is `e⁵` times the same part at `e = 1` with counterterms
`dᵢ`. -/
theorem onePIFunction₂_five_sub_four_of_conditions (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (he : P.e ≠ 0)
    (hel : IsElectronOnShell P hm hmγ hΛ) (hph : IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂)
    (hch : QED.OneLoop.IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ)
    {d₁ d₂ dm d₃ : ℝ}
    (hel₁ : IsElectronOnShell { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ } hm hmγ hΛ)
    (hph₁ : IsPhotonOnShell { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
      hm hM₁ hM₂ hPV₁ hPV₂)
    (hch₁ : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin 1 → Fin 4) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ - onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ
      = (P.e : ℂ) ^ 5 *
        (onePIFunction₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
          1 1 5 pOut pIn kIn αOut βIn μ
          - onePIFunction₂ { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }
            1 1 4 pOut pIn kIn αOut βIn μ) := by
  obtain ⟨h₁, h₂, hδm, h₃⟩ := counterterms_eq_sq_mul P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ he hel hph hch
    hel₁ hph₁ hch₁
  exact onePIFunction₂_five_sub_four P h₁ h₂ hδm h₃ pOut pIn kIn αOut βIn μ

end QED.TwoLoop.Scaling

end
