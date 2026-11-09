/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Spinor
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.WickModel.ElectronOnShell
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Instances.Matrix
import QED.Frozen.WickModel.SelfEnergyABSpec
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The electron legs of the LSZ amplitude

On an external electron leg of the order-`e³` connected function, after `ε → 0⁺` at an off-shell
momentum `r`, the self-energy insertion contributes `S̃₀(r) Σ(r)` next to the external spinor,
with `S̃₀(r) = (m - r̸) / (r² + m²)` the free propagator at `ε = 0` and
`Σ(r) = A(r²) r̸ + B(r²) m` the self-energy. This module proves that this contribution tends to
`0` as `r` approaches the mass shell through off-shell momenta, when `Σ(-m) = Σ'(-m) = 0` for
`Σ(z) = A(-z²) z + B(-z²) m`; in the Wick model these are the on-shell conditions (Z₅).

The key identity is the matrix identity `(m - r̸)(r̸ + m) = r² + m²`. It gives, for `r² ≠ -m²`,
`S̃₀(r) Σ(r) = A(r²) + m (B - A)(r²) / (r² + m²) · (m - r̸)`. The condition `Σ(-m) = 0` says
`(B - A)(-m²) = 0`, so the quotient tends to `(B - A)'(-m²)`, and on a spinor with
`(p̸ + m) u = 0` the matrix `m - r̸` tends to `m - p̸ = 2m`. The limit is
`[A(-m²) + 2m² (B' - A')(-m²)] u = Σ'(-m) u = 0`.

## Main statements

* `QED.WickModel.tendsto_electronPropagator_zero`: off shell, `S̃_ε(r) → S̃₀(r)` as `ε → 0⁺`.
* `QED.WickModel.electronPropagator_zero_mul_selfEnergyForm`,
  `QED.WickModel.selfEnergyForm_mul_electronPropagator_zero`: the identity above, for either
  order of the factors.
* `QED.WickModel.tendsto_electronLeg_in`, `QED.WickModel.tendsto_electronLeg_out`: the generic
  leg limits, for any pair `(A, B)` with `Σ(-m) = Σ'(-m) = 0`.
* `QED.WickModel.selfEnergyAB_eq_loop`: (Z₃) in closed form, `(A_loop - δ₂, B_loop - δ_m)`.
* `QED.WickModel.legConditions_of_isElectronOnShell`: the on-shell conditions (Z₅) give the
  hypotheses of the generic leg limits for `(A_loop - δ₂, B_loop - δ_m)`.
* `QED.WickModel.tendsto_electronLeg_in_spinor_of_isElectronOnShell`,
  `QED.WickModel.tendsto_electronLeg_out_spinor_of_isElectronOnShell`: the two leg limits in the
  Wick model, on the spinors (38.12).
-/

@[expose] public section

open Matrix Complex Filter Topology Set

namespace QED.WickModel

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### Continuity of the kinematic functions -/

/-- `r ↦ r²` is continuous. -/
theorem LszLegs.continuous_dot_self : Continuous fun r : Fin 4 → ℝ => Minkowski.dot r r := by
  unfold Minkowski.dot
  fun_prop

/-- `r ↦ r̸` is continuous. -/
theorem LszLegs.continuous_slash : Continuous Dirac.slash := by
  unfold Dirac.slash Minkowski.lower
  fun_prop

/-- Near an on-shell `p`, through off-shell momenta, `r²` tends to `-m²` without reaching it. -/
theorem LszLegs.tendsto_dot_self_offShell (m : ℝ) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) :
    Tendsto (fun r : Fin 4 → ℝ => Minkowski.dot r r)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝[≠] (-m ^ 2)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h := LszLegs.continuous_dot_self.tendsto p
    rw [hp] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_mem_nhdsWithin] with r hr using hr

/-! ### The propagator times the self-energy -/

/-- The free propagator at `ε = 0`: `S̃₀(r) = (m - r̸) / (r² + m²)`. -/
theorem electronPropagator_zero_eq (m : ℝ) (r : Fin 4 → ℝ) :
    QED.OneLoop.electronPropagator m 0 r =
      (((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ))⁻¹ • ((m : ℂ) • 𝟙 - Dirac.slash r) := by
  simp only [QED.OneLoop.electronPropagator, ofReal_zero, zero_mul, sub_zero]

/-- Off the mass shell, the free propagator is continuous in `ε` at `0`:
`S̃_ε(r) → S̃₀(r)` as `ε → 0⁺` for `r² ≠ -m²`. -/
theorem tendsto_electronPropagator_zero {m : ℝ} {r : Fin 4 → ℝ}
    (hr : Minkowski.dot r r ≠ -m ^ 2) :
    Tendsto (fun ε : ℝ => QED.OneLoop.electronPropagator m ε r) (𝓝[>] 0)
      (𝓝 (QED.OneLoop.electronPropagator m 0 r)) := by
  have hne : ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I ≠ 0 := by
    rw [ofReal_zero, zero_mul, sub_zero]
    exact ofReal_ne_zero.mpr fun h => hr (by linarith)
  have hc : ContinuousAt (fun ε : ℝ =>
      (((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹) 0 :=
    (continuous_const.sub (continuous_ofReal.mul continuous_const)).continuousAt.inv₀ hne
  unfold QED.OneLoop.electronPropagator
  exact (hc.smul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

/-- `(m - r̸)(a r̸ + b m) = a (r² + m²) + m (b - a) (m - r̸)`. -/
theorem LszLegs.mass_sub_slash_mul_selfEnergyForm (m : ℝ) (a b : ℂ) (r : Fin 4 → ℝ) :
    ((m : ℂ) • 𝟙 - Dirac.slash r) * (a • Dirac.slash r + (b * m) • 𝟙) =
      (a * ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ)) • 𝟙 +
        ((m : ℂ) * (b - a)) • ((m : ℂ) • 𝟙 - Dirac.slash r) := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Dirac.slash_mul_slash]
  push_cast
  module

/-- `(a r̸ + b m)(m - r̸) = a (r² + m²) + m (b - a) (m - r̸)`. -/
theorem LszLegs.selfEnergyForm_mul_mass_sub_slash (m : ℝ) (a b : ℂ) (r : Fin 4 → ℝ) :
    (a • Dirac.slash r + (b * m) • 𝟙) * ((m : ℂ) • 𝟙 - Dirac.slash r) =
      (a * ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ)) • 𝟙 +
        ((m : ℂ) * (b - a)) • ((m : ℂ) • 𝟙 - Dirac.slash r) := by
  simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Dirac.slash_mul_slash]
  push_cast
  module

/-- The scalar identity behind both orders of the factors. -/
theorem LszLegs.inv_smul_eq {m : ℝ} {r : Fin 4 → ℝ} (hr : Minkowski.dot r r ≠ -m ^ 2)
    (a b : ℂ) :
    (((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ))⁻¹ •
        ((a * ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ)) • 𝟙 +
          ((m : ℂ) * (b - a)) • ((m : ℂ) • 𝟙 - Dirac.slash r)) =
      a • 𝟙 + ((m : ℂ) * (b - a) / ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ)) •
        ((m : ℂ) • 𝟙 - Dirac.slash r) := by
  have hc : ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr fun h => hr (by linarith)
  rw [smul_add, smul_smul, smul_smul, mul_comm a, inv_mul_cancel_left₀ hc, div_eq_inv_mul]

/-- **The propagator times the self-energy.** For `r² ≠ -m²`,
`S̃₀(r) (a r̸ + b m) = a + m (b - a) / (r² + m²) · (m - r̸)`. -/
theorem electronPropagator_zero_mul_selfEnergyForm {m : ℝ} {r : Fin 4 → ℝ}
    (hr : Minkowski.dot r r ≠ -m ^ 2) (a b : ℂ) :
    QED.OneLoop.electronPropagator m 0 r * (a • Dirac.slash r + (b * m) • 𝟙) =
      a • 𝟙 + ((m : ℂ) * (b - a) / ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ)) •
        ((m : ℂ) • 𝟙 - Dirac.slash r) := by
  rw [electronPropagator_zero_eq, Matrix.smul_mul, LszLegs.mass_sub_slash_mul_selfEnergyForm,
    LszLegs.inv_smul_eq hr]

/-- **The self-energy times the propagator.** For `r² ≠ -m²`,
`(a r̸ + b m) S̃₀(r) = a + m (b - a) / (r² + m²) · (m - r̸)`. -/
theorem selfEnergyForm_mul_electronPropagator_zero {m : ℝ} {r : Fin 4 → ℝ}
    (hr : Minkowski.dot r r ≠ -m ^ 2) (a b : ℂ) :
    (a • Dirac.slash r + (b * m) • 𝟙) * QED.OneLoop.electronPropagator m 0 r =
      a • 𝟙 + ((m : ℂ) * (b - a) / ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ)) •
        ((m : ℂ) • 𝟙 - Dirac.slash r) := by
  rw [electronPropagator_zero_eq, Matrix.mul_smul, LszLegs.selfEnergyForm_mul_mass_sub_slash,
    LszLegs.inv_smul_eq hr]

/-! ### The generic leg limits -/

/-- If `A(-m²) = B(-m²)`, then `(B - A)(s) / (s + m²)` tends to `(B - A)'(-m²)` as `s → -m²`,
`s ≠ -m²`. -/
theorem LszLegs.tendsto_sub_div {m : ℝ} {A B : ℝ → ℂ} {A' B' : ℂ}
    (hA : HasDerivAt A A' (-m ^ 2)) (hB : HasDerivAt B B' (-m ^ 2))
    (hAB : A (-m ^ 2) = B (-m ^ 2)) :
    Tendsto (fun s : ℝ => (B s - A s) / ((s + m ^ 2 : ℝ) : ℂ)) (𝓝[≠] (-m ^ 2))
      (𝓝 (B' - A')) := by
  refine (hasDerivAt_iff_tendsto_slope.mp (hB.sub hA)).congr fun s => ?_
  rw [slope_def_module, Pi.sub_apply, Pi.sub_apply, hAB, sub_self, sub_zero, Complex.real_smul,
    sub_neg_eq_add, ofReal_inv, div_eq_inv_mul]

/-- `Σ(-m) = 0` gives `A(-m²) = B(-m²)`. -/
theorem LszLegs.eq_of_selfEnergy_zero {m : ℝ} (hm : m ≠ 0) {a b : ℂ}
    (h0 : -(m : ℂ) * a + m * b = 0) : a = b := by
  have h : (m : ℂ) * (b - a) = 0 := by linear_combination h0
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (ofReal_eq_zero.mp h) hm
  · exact (sub_eq_zero.mp h).symm

/-- The two scalar limits of the leg: `A(r²) → A(-m²)` and
`m (B - A)(r²) / (r² + m²) → m (B' - A')`, through off-shell momenta near an on-shell `p`. -/
theorem LszLegs.tendsto_coeffs {m : ℝ} (hm : m ≠ 0) {A B : ℝ → ℂ} {A' B' : ℂ}
    (hA : HasDerivAt A A' (-m ^ 2)) (hB : HasDerivAt B B' (-m ^ 2))
    (h0 : -(m : ℂ) * A (-m ^ 2) + m * B (-m ^ 2) = 0) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) :
    Tendsto (fun r : Fin 4 → ℝ => A (Minkowski.dot r r))
        (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 (A (-m ^ 2))) ∧
      Tendsto (fun r : Fin 4 → ℝ => (m : ℂ) * (B (Minkowski.dot r r) - A (Minkowski.dot r r)) /
          ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ))
        (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 ((m : ℂ) * (B' - A'))) := by
  have hs := LszLegs.tendsto_dot_self_offShell m hp
  refine ⟨hA.continuousAt.tendsto.comp (hs.mono_right nhdsWithin_le_nhds), ?_⟩
  have hk := ((LszLegs.tendsto_sub_div hA hB
    (LszLegs.eq_of_selfEnergy_zero hm h0)).comp hs).const_mul (m : ℂ)
  refine hk.congr fun r => ?_
  simp only [Function.comp_apply, mul_div_assoc]

/-- The final scalar identity: `A + m (B' - A') · 2m = Σ'(-m) = 0`. -/
theorem LszLegs.limit_eq_zero {m : ℝ} {a A' B' : ℂ}
    (h1 : a - 2 * m ^ 2 * A' + 2 * m ^ 2 * B' = 0) (v : Fin 4 → ℂ) :
    a • v + ((m : ℂ) * (B' - A')) • ((m : ℂ) • v - -((m : ℂ) • v)) = 0 := by
  rw [show a • v + ((m : ℂ) * (B' - A')) • ((m : ℂ) • v - -((m : ℂ) • v)) =
      (a - 2 * m ^ 2 * A' + 2 * m ^ 2 * B') • v by module, h1, zero_smul]

/-- **The incoming electron leg vanishes on shell.** Let `m ≠ 0` and `A`, `B` be differentiable
at `-m²` with `Σ(-m) = 0` and `Σ'(-m) = 0` for `Σ(z) = A(-z²) z + B(-z²) m`, that is
`-m A(-m²) + m B(-m²) = 0` and `A(-m²) - 2m² A'(-m²) + 2m² B'(-m²) = 0`. For an on-shell `p`
and a spinor with `(p̸ + m) u = 0`, `S̃₀(r) Σ(r) u → 0` as `r → p` through off-shell momenta. -/
theorem tendsto_electronLeg_in {m : ℝ} (hm : m ≠ 0) {A B : ℝ → ℂ} {A' B' : ℂ}
    (hA : HasDerivAt A A' (-m ^ 2)) (hB : HasDerivAt B B' (-m ^ 2))
    (h0 : -(m : ℂ) * A (-m ^ 2) + m * B (-m ^ 2) = 0)
    (h1 : A (-m ^ 2) - 2 * m ^ 2 * A' + 2 * m ^ 2 * B' = 0)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) {u : Fin 4 → ℂ}
    (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u)) :
    Tendsto (fun r => (QED.OneLoop.electronPropagator m 0 r *
        (A (Minkowski.dot r r) • Dirac.slash r + (B (Minkowski.dot r r) * m) • 𝟙)) *ᵥ u)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 0) := by
  obtain ⟨hA0, hk⟩ := LszLegs.tendsto_coeffs hm hA hB h0 hp
  have hv : Tendsto (fun r => ((m : ℂ) • 𝟙 - Dirac.slash r) *ᵥ u)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 (((m : ℂ) • 𝟙 - Dirac.slash p) *ᵥ u)) :=
    (((continuous_const.sub LszLegs.continuous_slash).matrix_mulVec
      continuous_const).tendsto p).mono_left nhdsWithin_le_nhds
  have hlim := (hA0.smul_const u).add (hk.smul hv)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hu,
    LszLegs.limit_eq_zero h1] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with r hr
  rw [electronPropagator_zero_mul_selfEnergyForm hr, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec]

/-- **The outgoing electron leg vanishes on shell.** Under the hypotheses of
`QED.WickModel.tendsto_electronLeg_in` on `A`, `B`, for an on-shell `p'` and a row spinor with
`w (p̸' + m) = 0`, `w Σ(r') S̃₀(r') → 0` as `r' → p'` through off-shell momenta. -/
theorem tendsto_electronLeg_out {m : ℝ} (hm : m ≠ 0) {A B : ℝ → ℂ} {A' B' : ℂ}
    (hA : HasDerivAt A A' (-m ^ 2)) (hB : HasDerivAt B B' (-m ^ 2))
    (h0 : -(m : ℂ) * A (-m ^ 2) + m * B (-m ^ 2) = 0)
    (h1 : A (-m ^ 2) - 2 * m ^ 2 * A' + 2 * m ^ 2 * B' = 0)
    {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) {w : Fin 4 → ℂ}
    (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) :
    Tendsto (fun r' => w ᵥ* ((A (Minkowski.dot r' r') • Dirac.slash r' +
        (B (Minkowski.dot r' r') * m) • 𝟙) * QED.OneLoop.electronPropagator m 0 r'))
      (𝓝[{r' | Minkowski.dot r' r' ≠ -m ^ 2}] p') (𝓝 0) := by
  obtain ⟨hA0, hk⟩ := LszLegs.tendsto_coeffs hm hA hB h0 hp'
  have hv : Tendsto (fun r' => w ᵥ* ((m : ℂ) • 𝟙 - Dirac.slash r'))
      (𝓝[{r' | Minkowski.dot r' r' ≠ -m ^ 2}] p') (𝓝 (w ᵥ* ((m : ℂ) • 𝟙 - Dirac.slash p'))) :=
    ((continuous_const.matrix_vecMul
      (continuous_const.sub LszLegs.continuous_slash)).tendsto p').mono_left nhdsWithin_le_nhds
  have hlim := (hA0.smul_const w).add (hk.smul hv)
  rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, hw,
    LszLegs.limit_eq_zero h1] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with r' hr'
  rw [selfEnergyForm_mul_electronPropagator_zero hr', Matrix.vecMul_add, Matrix.vecMul_smul,
    Matrix.vecMul_one, Matrix.vecMul_smul]

/-- The incoming leg limit on the spinor `u_s(p)` (38.12). -/
theorem tendsto_electronLeg_in_spinor {m : ℝ} (hm : m ≠ 0) {A B : ℝ → ℂ} {A' B' : ℂ}
    (hA : HasDerivAt A A' (-m ^ 2)) (hB : HasDerivAt B B' (-m ^ 2))
    (h0 : -(m : ℂ) * A (-m ^ 2) + m * B (-m ^ 2) = 0)
    (h1 : A (-m ^ 2) - 2 * m ^ 2 * A' + 2 * m ^ 2 * B' = 0)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) (s : Fin 2) :
    Tendsto (fun r => (QED.OneLoop.electronPropagator m 0 r *
        (A (Minkowski.dot r r) • Dirac.slash r + (B (Minkowski.dot r r) * m) • 𝟙)) *ᵥ
          Dirac.spinor m p s)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 0) :=
  tendsto_electronLeg_in hm hA hB h0 h1 hp (Dirac.slash_mulVec_spinor m p hp s)

/-- The outgoing leg limit on the adjoint spinor `ū_{s'}(p')` (38.7), (38.12). -/
theorem tendsto_electronLeg_out_spinor {m : ℝ} (hm : m ≠ 0) {A B : ℝ → ℂ} {A' B' : ℂ}
    (hA : HasDerivAt A A' (-m ^ 2)) (hB : HasDerivAt B B' (-m ^ 2))
    (h0 : -(m : ℂ) * A (-m ^ 2) + m * B (-m ^ 2) = 0)
    (h1 : A (-m ^ 2) - 2 * m ^ 2 * A' + 2 * m ^ 2 * B' = 0)
    {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (s' : Fin 2) :
    Tendsto (fun r' => Dirac.bar (Dirac.spinor m p' s') ᵥ* ((A (Minkowski.dot r' r') •
        Dirac.slash r' + (B (Minkowski.dot r' r') * m) • 𝟙) *
          QED.OneLoop.electronPropagator m 0 r'))
      (𝓝[{r' | Minkowski.dot r' r' ≠ -m ^ 2}] p') (𝓝 0) :=
  tendsto_electronLeg_out hm hA hB h0 h1 hp'
    (Dirac.bar_vecMul_slash m p' _ (Dirac.slash_mulVec_spinor m p' hp' s'))

/-! ### The Wick-model instance -/

/-- **(Z₃) in closed form.** The sealed form factors are `(A_loop - δ₂, B_loop - δ_m)`, with
`A_loop = selfEnergyLoopA P` and `B_loop = selfEnergyLoopB P`. -/
theorem selfEnergyAB_eq_loop (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    selfEnergyAB P hm hmγ hΛ =
      fun s => (selfEnergyLoopA P s.1 - P.δ₂, selfEnergyLoopB P s.1 - P.δm) :=
  eq_selfEnergyLoop_of_tendsto P hm hmγ hΛ (selfEnergyAB_spec P hm hmγ hΛ).1

/-- **The on-shell conditions give the leg hypotheses.** For `m, m_γ, Λ > 0` and counterterms
with the on-shell conditions (Z₅), the functions `A = A_loop - δ₂` and `B = B_loop - δ_m` are
differentiable at `-m²` (which lies below both photon thresholds), with derivatives
`A' = A_loop'(-m²)`, `B' = B_loop'(-m²)`, and satisfy `-m A(-m²) + m B(-m²) = 0` and
`A(-m²) - 2m² A' + 2m² B' = 0`. -/
theorem legConditions_of_isElectronOnShell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hon : IsElectronOnShell P hm hmγ hΛ) :
    HasDerivAt (fun s => selfEnergyLoopA P s - P.δ₂) (deriv (selfEnergyLoopA P) (-P.m ^ 2))
        (-P.m ^ 2) ∧
      HasDerivAt (fun s => selfEnergyLoopB P s - P.δm) (deriv (selfEnergyLoopB P) (-P.m ^ 2))
        (-P.m ^ 2) ∧
      -(P.m : ℂ) * (selfEnergyLoopA P (-P.m ^ 2) - P.δ₂) +
          P.m * (selfEnergyLoopB P (-P.m ^ 2) - P.δm) = 0 ∧
      (selfEnergyLoopA P (-P.m ^ 2) - P.δ₂) - 2 * P.m ^ 2 * deriv (selfEnergyLoopA P) (-P.m ^ 2)
          + 2 * P.m ^ 2 * deriv (selfEnergyLoopB P) (-P.m ^ 2) = 0 := by
  have hs := neg_sq_mem_Ioi_inter_Ioi hm hmγ hΛ
  have hA := (differentiableAt_selfEnergyLoopA hm hmγ hΛ hs).hasDerivAt
  have hB := (differentiableAt_selfEnergyLoopB hm hmγ hΛ hs).hasDerivAt
  have hμ := lt_min hmγ hΛ
  have hab : -P.m - min P.mγ P.Λ / 2 ≤ -P.m + min P.mγ P.Λ / 2 := by linarith
  have hx : -P.m ∈ Ioo (-P.m - min P.mγ P.Λ / 2) (-P.m + min P.mγ P.Λ / 2) := by
    constructor <;> linarith
  have hslash : ∀ z hz, selfEnergySlash P hm hmγ hΛ z hz =
      (selfEnergyLoopA P (-z ^ 2) - P.δ₂) * z + (selfEnergyLoopB P (-z ^ 2) - P.δm) * P.m := by
    intro z hz
    rw [selfEnergySlash, selfEnergyAB_eq_loop]
  obtain ⟨h0, h1⟩ := hon
  rw [hslash] at h0
  simp only [hslash] at h1
  have h1' := (hasDerivAt_comp_projIcc_iff
    (f := fun z : ℝ => (selfEnergyLoopA P (-z ^ 2) - P.δ₂) * z
      + (selfEnergyLoopB P (-z ^ 2) - P.δm) * P.m) hab hx).mp h1
  have hL := (hasDerivAt_selfEnergyForm hA hB P.δ₂ P.δm).unique h1'
  refine ⟨hA.sub_const _, hB.sub_const _, ?_, by linear_combination hL⟩
  rw [neg_sq] at h0
  push_cast at h0
  linear_combination h0

/-- **The incoming electron leg vanishes on shell, in the Wick model.** For `m, m_γ, Λ > 0`,
counterterms with the on-shell conditions (Z₅), an on-shell `p` and a spin `s`,
`S̃₀(r) Σ(r) u_s(p) → 0` as `r → p` through off-shell momenta, where
`Σ(r) = (A_loop(r²) - δ₂) r̸ + (B_loop(r²) - δ_m) m` is the self-energy (Z₃) in closed form
(`QED.WickModel.selfEnergyAB_eq_loop`). -/
theorem tendsto_electronLeg_in_spinor_of_isElectronOnShell (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hon : IsElectronOnShell P hm hmγ hΛ) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (s : Fin 2) :
    Tendsto (fun r => (QED.OneLoop.electronPropagator P.m 0 r *
        ((selfEnergyLoopA P (Minkowski.dot r r) - P.δ₂) • Dirac.slash r +
          ((selfEnergyLoopB P (Minkowski.dot r r) - P.δm) * P.m) • 𝟙)) *ᵥ
          Dirac.spinor P.m p s)
      (𝓝[{r | Minkowski.dot r r ≠ -P.m ^ 2}] p) (𝓝 0) := by
  obtain ⟨hA, hB, h0, h1⟩ := legConditions_of_isElectronOnShell P hm hmγ hΛ hon
  exact tendsto_electronLeg_in_spinor hm.ne' hA hB h0 h1 hp s

/-- **The outgoing electron leg vanishes on shell, in the Wick model.** For `m, m_γ, Λ > 0`,
counterterms with the on-shell conditions (Z₅), an on-shell `p'` and a spin `s'`,
`ū_{s'}(p') Σ(r') S̃₀(r') → 0` as `r' → p'` through off-shell momenta, with `Σ` as in
`QED.WickModel.tendsto_electronLeg_in_spinor_of_isElectronOnShell`. -/
theorem tendsto_electronLeg_out_spinor_of_isElectronOnShell (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hon : IsElectronOnShell P hm hmγ hΛ) {p' : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (s' : Fin 2) :
    Tendsto (fun r' => Dirac.bar (Dirac.spinor P.m p' s') ᵥ*
        (((selfEnergyLoopA P (Minkowski.dot r' r') - P.δ₂) • Dirac.slash r' +
          ((selfEnergyLoopB P (Minkowski.dot r' r') - P.δm) * P.m) • 𝟙) *
          QED.OneLoop.electronPropagator P.m 0 r'))
      (𝓝[{r' | Minkowski.dot r' r' ≠ -P.m ^ 2}] p') (𝓝 0) := by
  obtain ⟨hA, hB, h0, h1⟩ := legConditions_of_isElectronOnShell P hm hmγ hΛ hon
  exact tendsto_electronLeg_out_spinor hm.ne' hA hB h0 h1 hp' s'

end QED.WickModel

end
