/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ConnectedFunction
public import QED.Frozen.OneLoop.VertexIntegrand
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.WickModel.LszPhotonLeg
public import QED.WickModel.SelfEnergyLimit
import QED.WickModel.ThreePointClassification
import QED.WickModel.LszLegs
import QED.Frozen.WickModel.WickVertexEqOnePIFunction
import QED.Frozen.Wick.WickVertexEq
import QED.Frozen.WickModel.SelfEnergyABSpec

/-!
# The LSZ amplitude off the mass shell: the limit `ε → 0⁺`

At fixed `ε > 0`, the order-`e³` connected function with outgoing momentum `r'`, incoming momentum
`r` and photon momentum `r' - r` is the 1PI vertex plus the self-energy insertions on the two
electron legs and the vacuum polarization insertion on the photon leg
(`QED.WickModel.connectedFunction_threePoint_of_pos`). This module takes the limit `ε → 0⁺` of
each entry at off-shell momenta near the mass shell, term by term:

* the 1PI vertex is the tree term `i (1 + δ₁) e γ^μ` plus the energy-first integral of the
  one-loop vertex integrand (the sealed (Y₁) and (W₁)); the latter tends to a given limit `V`;
* on each electron leg the free propagator tends to `S̃₀` and the self-energy function tends to
  `i Σ(r)`, `Σ(r) = (A_loop(r²) - δ₂) r̸ + (B_loop(r²) - δ_m) m` (the sealed (Z₃′) in closed
  form);
* the photon leg tends to `QED.WickModel.photonLegLimit`.

## Main definitions

* `QED.WickModel.LszLimit.selfEnergyMatrix`: the self-energy `Σ(r)` in closed form.
* `QED.WickModel.LszLimit.offShellLimit`: the entries of the limit.

## Main statements

* `QED.WickModel.LszLimit.tendsto_connectedFunction_offShell`: the entrywise limit.
* `QED.WickModel.LszLimit.tendsto_sandwich_connectedFunction_offShell`: the limit of
  `(1/i) w G_ε(r', r) u`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology Set

namespace QED.WickModel

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The self-energy `Σ(r) = (A_loop(r²) - δ₂) r̸ + (B_loop(r²) - δ_m) m` in closed form
(`QED.WickModel.selfEnergyAB_eq_loop`). -/
noncomputable def LszLimit.selfEnergyMatrix (P : Params) (r : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (selfEnergyLoopA P (Minkowski.dot r r) - P.δ₂) • Dirac.slash r +
    ((selfEnergyLoopB P (Minkowski.dot r r) - P.δm) * P.m) • 𝟙

/-- The entries of the limit `ε → 0⁺` of the order-`e³` connected function at off-shell momenta
`r'`, `r`, given the limit `V` of the one-loop vertex integral: the tree vertex plus `V`, the
incoming leg `[i e γ^μ (1/i) S̃₀(r)] [i Σ(r)]`, the outgoing leg `[i Σ(r')] [(1/i) S̃₀(r') i e γ^μ]`
and the photon leg `photonLegLimit`. -/
noncomputable def LszLimit.offShellLimit (P : Params) (V : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4)
    (r' r : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  (I * (((1 + P.δ₁) * P.e : ℝ) : ℂ) * Dirac.gamma μ α β + V α β)
  + ∑ γ, ((I * P.e) • Dirac.gamma μ *
      ((1 / I) • QED.OneLoop.electronPropagator P.m 0 r)) α γ *
      (I * LszLimit.selfEnergyMatrix P r γ β)
  + ∑ γ, (I * LszLimit.selfEnergyMatrix P r' α γ) *
      (((1 / I) • QED.OneLoop.electronPropagator P.m 0 r') * (I * P.e) • Dirac.gamma μ) γ β
  + photonLegLimit P (r' - r) μ α β

/-- **The 1PI vertex.** The 1PI function with one external fermion pair and one external photon
at order `≤ 3` is the tree vertex `i (1 + δ₁) e γ^μ` plus the energy-first integral of the
one-loop vertex integrand ((Y₁) and (W₁)). -/
theorem LszLimit.onePIFunction_vertex_eq (P : Params) (r' r : Fin 4 → ℝ) (α β μ : Fin 4) :
    onePIFunction P 1 1 3 ![r'] ![r] ![r' - r] ![α] ![β] ![μ] =
      I * (((1 + P.δ₁) * P.e : ℝ) : ℂ) * Dirac.gamma μ α β +
        QED.OneLoop.energyFirstIntegral (fun ℓ =>
          QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε r' r μ ℓ α β) := by
  have h := wickVertex_eq_onePIFunction P r' r μ α β
  rw [QED.Wick.wickVertex_eq] at h
  simp only [Matrix.cons_fin_one]
  rw [← h]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

/-- **The self-energy as `ε → 0⁺`.** In the domain of (Z₃′), the self-energy function
`onePIFunction P 1 0 2` tends to `i Σ(r)`. -/
theorem LszLimit.tendsto_selfEnergy (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {r : Fin 4 → ℝ} (hrd : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot r r) (γ β : Fin 4) :
    Tendsto (fun ε : ℝ => onePIFunction { P with ε := ε } 1 0 2 ![r] ![r] ![] ![γ] ![β] ![])
      (𝓝[>] 0) (𝓝 (I * LszLimit.selfEnergyMatrix P r γ β)) := by
  have h := ((selfEnergyAB_spec P hm hmγ hΛ).1 r hrd γ β).const_mul I
  simp only [selfEnergyAB_eq_loop] at h
  refine h.congr fun ε => ?_
  rw [← mul_assoc, mul_one_div_cancel I_ne_zero, one_mul]

/-- **The incoming electron leg as `ε → 0⁺`.** -/
theorem LszLimit.tendsto_legIn (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {r : Fin 4 → ℝ} (hr : Minkowski.dot r r ≠ -P.m ^ 2)
    (hrd : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot r r) (μ α β : Fin 4) :
    Tendsto (fun ε : ℝ => ∑ γ, ((I * P.e) • Dirac.gamma μ *
        ((1 / I) • QED.OneLoop.electronPropagator P.m ε r)) α γ *
        onePIFunction { P with ε := ε } 1 0 2 ![r] ![r] ![] ![γ] ![β] ![])
      (𝓝[>] 0)
      (𝓝 (∑ γ, ((I * P.e) • Dirac.gamma μ *
        ((1 / I) • QED.OneLoop.electronPropagator P.m 0 r)) α γ *
        (I * LszLimit.selfEnergyMatrix P r γ β))) := by
  refine tendsto_finsetSum _ fun γ _ => ?_
  have hc : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ =>
      ((I * P.e) • Dirac.gamma μ * ((1 / I) • M)) α γ :=
    (continuous_const.matrix_mul (continuous_const_smul (1 / I))).matrix_elem α γ
  exact ((hc.tendsto _).comp (tendsto_electronPropagator_zero hr)).mul
    (LszLimit.tendsto_selfEnergy P hm hmγ hΛ hrd γ β)

/-- **The outgoing electron leg as `ε → 0⁺`.** -/
theorem LszLimit.tendsto_legOut (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {r' : Fin 4 → ℝ} (hr' : Minkowski.dot r' r' ≠ -P.m ^ 2)
    (hrd' : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot r' r') (μ α β : Fin 4) :
    Tendsto (fun ε : ℝ => ∑ γ, onePIFunction { P with ε := ε } 1 0 2 ![r'] ![r'] ![] ![α] ![γ] ![]
        * (((1 / I) • QED.OneLoop.electronPropagator P.m ε r') * (I * P.e) • Dirac.gamma μ) γ β)
      (𝓝[>] 0)
      (𝓝 (∑ γ, (I * LszLimit.selfEnergyMatrix P r' α γ) *
        (((1 / I) • QED.OneLoop.electronPropagator P.m 0 r') * (I * P.e) • Dirac.gamma μ) γ β))
    := by
  refine tendsto_finsetSum _ fun γ _ => ?_
  have hc : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ =>
      (((1 / I) • M) * (I * P.e) • Dirac.gamma μ) γ β :=
    ((continuous_const_smul (1 / I)).matrix_mul continuous_const).matrix_elem γ β
  exact (LszLimit.tendsto_selfEnergy P hm hmγ hΛ hrd' α γ).mul
    ((hc.tendsto _).comp (tendsto_electronPropagator_zero hr'))

/-- **The connected function as `ε → 0⁺`, entrywise.** For `m, m_γ, Λ > 0`, regulator fermions
as in (Z₂), off-shell momenta `r'`, `r` in the domain of (Z₃′), a photon momentum `r' - r` below
the pair threshold and off the photon poles, and a limit `V` of the one-loop vertex integral,
the connected function tends to `offShellLimit P V μ r' r`. -/
theorem LszLimit.tendsto_connectedFunction_offShell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {r' r : Fin 4 → ℝ}
    (hr' : Minkowski.dot r' r' ≠ -P.m ^ 2) (hr : Minkowski.dot r r ≠ -P.m ^ 2)
    (hrd' : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot r' r')
    (hrd : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot r r)
    (hq : -(4 * P.m ^ 2) < Minkowski.dot (r' - r) (r' - r))
    (hqγ : Minkowski.dot (r' - r) (r' - r) ≠ -P.mγ ^ 2)
    (hqΛ : Minkowski.dot (r' - r) (r' - r) ≠ -P.Λ ^ 2) (μ : Fin 4)
    {V : Matrix (Fin 4) (Fin 4) ℂ}
    (hV : ∀ i j : Fin 4, Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun ℓ =>
      QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ ε r' r μ ℓ i j) (𝓝[>] 0) (𝓝 (V i j)))
    (α β : Fin 4) :
    Tendsto (fun ε : ℝ =>
        connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r] ![r' - r] ![α] ![β] ![μ])
      (𝓝[>] 0) (𝓝 (LszLimit.offShellLimit P V μ r' r α β)) := by
  have h1 := (hV α β).const_add (I * (((1 + P.δ₁) * P.e : ℝ) : ℂ) * Dirac.gamma μ α β)
  have h2 := LszLimit.tendsto_legIn P hm hmγ hΛ hr hrd μ α β
  have h3 := LszLimit.tendsto_legOut P hm hmγ hΛ hr' hrd' μ α β
  have h4 := tendsto_photonLeg_photonLegLimit P hm hM₁ hM₂ hPV₁ hPV₂ hq hqγ hqΛ μ α β
  refine (((h1.add h2).add h3).add h4).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [connectedFunction_threePoint_of_pos { P with ε := ε } hε hm hM₁ hM₂ hPV₁ hPV₂,
    LszLimit.onePIFunction_vertex_eq]

/-- **The sandwiched connected function as `ε → 0⁺`.** Under the hypotheses of
`QED.WickModel.LszLimit.tendsto_connectedFunction_offShell`, for any row vector `w` and column
vector `u`, `(1/i) w G_ε(r', r) u` tends to `(1/i) w [offShellLimit P V μ r' r] u`. -/
theorem LszLimit.tendsto_sandwich_connectedFunction_offShell (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {r' r : Fin 4 → ℝ} (hr' : Minkowski.dot r' r' ≠ -P.m ^ 2)
    (hr : Minkowski.dot r r ≠ -P.m ^ 2)
    (hrd' : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot r' r')
    (hrd : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot r r)
    (hq : -(4 * P.m ^ 2) < Minkowski.dot (r' - r) (r' - r))
    (hqγ : Minkowski.dot (r' - r) (r' - r) ≠ -P.mγ ^ 2)
    (hqΛ : Minkowski.dot (r' - r) (r' - r) ≠ -P.Λ ^ 2) (μ : Fin 4)
    {V : Matrix (Fin 4) (Fin 4) ℂ}
    (hV : ∀ i j : Fin 4, Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun ℓ =>
      QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ ε r' r μ ℓ i j) (𝓝[>] 0) (𝓝 (V i j)))
    (w u : Fin 4 → ℂ) :
    Tendsto (fun ε : ℝ => (1 / I) * (w ⬝ᵥ (Matrix.of (fun α β =>
        connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r] ![r' - r] ![α] ![β] ![μ]) *ᵥ u)))
      (𝓝[>] 0) (𝓝 ((1 / I) * (w ⬝ᵥ (Matrix.of (LszLimit.offShellLimit P V μ r' r) *ᵥ u)))) :=
  tendsto_sandwich (F := fun ε α β =>
      connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r] ![r' - r] ![α] ![β] ![μ])
    (fun α β => LszLimit.tendsto_connectedFunction_offShell P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hr' hr
      hrd' hrd hq hqγ hqΛ μ hV α β) w u

end QED.WickModel

end
