-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.WickModel.RegulatedAmplitude
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.WickModel.IsLoopLine
public import QED.Frozen.Wick.VertexKindOrder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import QED.Frozen.Algebra.Slash
public import QED.Frozen.Algebra.Dot
public import QED.Frozen.Algebra.Metric
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.Complex.Basic
public import QED.Provider.WickModel.VacuumPolarizationExistsUnique

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₂) **The vacuum polarization: well-definedness and transverse form (packet 6b theorem goal;
decision D-25).** For `m > 0`, regulator fermions whose coefficients satisfy the Pauli–Villars
conditions `1 + c₁ + c₂ = 0` and `m² + c₁ M₁² + c₂ M₂² = 0` (decision D-22), and which are
heavier than the electron (`M₁, M₂ > m`, so that the pair threshold of the electron is the
lowest): first, for every `ε > 0` the regulated loop integrand of every one-loop 1PI contraction
of the two-photon function at order `e²` is integrable in both stages of M1 (this is where the
Pauli–Villars conditions act). Second, there is a unique function `Π` (`Pol`) of `s = k²` on the
region `s > -4m²` below the pair threshold such that, for every photon momentum `k` with `k²` in
that region, `Π^{μν}_ε(k) := (1/i) [i Π^{μν}_ε(k)]`, where `[i Π^{μν}_ε(k)]` is the two-photon
1PI function (X₂₈) at order `e²` with photon momentum `k` flowing in through the first external
photon and out through the second ((62.4), (62.12)), tends as `ε → 0⁺` to
`Π(k²) (k² g^{μν} - k^μ k^ν)`, the transverse form (62.6)–(62.7). The vacuum polarization has no
internal photon at this order, so it does not depend on `m_γ` or `Λ`. -/
theorem vacuumPolarization_existsUnique (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 2 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → (∃ f : Line C, IsLoopLine f) →
      ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
    ∃! Pol : {s : ℝ // -(4 * P.m ^ 2) < s} → ℂ,
      ∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
          (𝓝[>] 0)
          (𝓝 (Pol ⟨_, hk⟩ *
            ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.vacuumPolarization_existsUnique
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
