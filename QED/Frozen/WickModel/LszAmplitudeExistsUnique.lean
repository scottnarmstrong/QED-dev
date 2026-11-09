-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ConnectedFunction
public import QED.Frozen.WickModel.RegulatedAmplitude
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected
public import QED.Frozen.WickModel.IsLoopLine
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.Wick.VertexKindOrder
public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor
public import QED.Frozen.Algebra.Dot
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic
public import QED.Provider.WickModel.LszAmplitudeExistsUnique

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (L₁) **The LSZ amplitude of the electron current exists and is unique (packet 6c theorem
goal; decisions D-23, D-29).** For `m, m_γ, Λ > 0`, regulator fermions as in (Z₂), and electron
counterterms satisfying the on-shell conditions (Z₅), two things hold. The on-shell conditions
give the exact electron propagator a pole at `p̸ = -m` with residue one, as the source says after
(62.27); this is the field normalization (41.25) under which the LSZ formula (41.17) holds.
First, for every `ε > 0` and all momenta `r'`, `r`, the loop integrand of every one-loop
connected contraction of the function with one external fermion pair and one external photon of
momentum `r' - r` at order `e³` is integrable in both stages of the energy-first prescription M1
(this is where the Pauli–Villars conditions act, on the closed fermion loops), so its value
(X₂₇) is a genuine integral. Second, for on-shell positive-energy momenta `p'`, `p`, spins `s'`,
`s` and index `μ` there is a unique number `M`, the LSZ amplitude `M^μ_{s's}(p', p)` of the
electron current, that is the following iterated limit. Let `G^μ_ε(r', r)` be the connected
function (X₂₉) at order `e³` with outgoing momentum `r'`, incoming momentum `r` and incoming
photon momentum `r' - r`, as a matrix with the outgoing spinor index as row; it is amputated by
the free external propagators, as the factors `(-i∂̸ + m)` of (41.17) do (in momentum space, the
inverse free propagators `p̸ + m`), and it keeps the corrections on the external legs. First
`ε → 0⁺` in `(1/i) ū_{s'}(p') G^μ_ε(r', r) u_s(p)` at off-shell `r'`, `r`, with the spinors
(38.7), (38.12) at the limit momenta; then `(r', r) → (p', p)` through off-shell momenta, along
every approach. The photon is the external field of (64.3)–(64.7): its leg is amputated by the
free photon propagator and keeps the vacuum-polarization insertion (D-29). -/
theorem lszAmplitude_existsUnique (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 3 →
      ∀ C : Contraction 1 1 κ, ExternalsAttached C → VerticesConnected C →
      (∃ f : Line C, IsLoopLine f) →
      ∀ (r' r : Fin 4 → ℝ) (α β μ : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] (Fin.cons t v) ![α] ![β]
            ![μ]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] (Fin.cons t v) ![α] ![β]
            ![μ]) ∧
    ∀ (p' p : Fin 4 → ℝ), Minkowski.dot p' p' = -P.m ^ 2 → Minkowski.dot p p = -P.m ^ 2 →
      0 < p' 0 → 0 < p 0 → ∀ (s' s : Fin 2) (μ : Fin 4),
      ∃! M : ℂ, ∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
        Minkowski.dot r' r' ≠ -P.m ^ 2 → Minkowski.dot r r ≠ -P.m ^ 2 →
        dist r' p' < δ → dist r p < δ →
        ∃ G : ℂ, Tendsto (fun ε : ℝ => (1 / I) *
            (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
              (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r]
                ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s)))
          (𝓝[>] 0) (𝓝 G) ∧ ‖G - M‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
