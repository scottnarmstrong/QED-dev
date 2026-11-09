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
public import QED.Provider.WickModel.SelfEnergyExistsUnique

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₁) **The electron self-energy: well-definedness and covariant form (packet 6b theorem goal;
decision D-25).** For `m, m_γ, Λ > 0`: first, for every `ε > 0` the loop integrand of every
one-loop 1PI contraction of the one-electron function at order `e²` is integrable in both stages
of the energy-first prescription M1, so its value (X₂₇) is a genuine integral. Second, there is a
unique pair of functions `A, B` of `s = p²` on the region `s > -(m + min(m_γ, Λ))²`, below the
thresholds of the electron with the photon and with the Pauli–Villars photon, such that, for
every `p` with `p²` in that region,
`Σ_ε(p) := (1/i) [i Σ_ε(p)]`, where `[i Σ_ε(p)]_{αβ}` is the one-electron 1PI function (X₂₈) at
order `e²` with the outgoing index `α` as row and the incoming index `β` as column
((62.27)–(62.28)), tends as `ε → 0⁺` to `A(p²) p̸ + B(p²) m`, entry by entry. The self-energy
has no closed fermion loop at this order, so it does not depend on the regulator fermions. -/
theorem selfEnergy_existsUnique (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 2 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → (∃ f : Line C, IsLoopLine f) →
      ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![p] ![p] ![] (Fin.cons t v) ![α] ![β] ![]) ∧
    ∃! AB : {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ,
      ∀ (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
          (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.selfEnergy_existsUnique
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
