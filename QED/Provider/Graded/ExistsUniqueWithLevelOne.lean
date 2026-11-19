/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.CountertermsWithLevel
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.GradedProof.GEx2Final

/-!
# Provider for `QED.Graded.existsUnique_withLevel_one`

Proves the frozen theorem goal `QED.Graded.existsUnique_withLevel_one` (Phase 5 Stage 2 packet,
decision D-57) as `QED.Provider.Graded.existsUnique_withLevel_one`, with the binder convention of
decision D-13, from `QED.GradedProof.GEx2.existsUnique_withLevel_one'`. This module must never
import the frozen anchor.
-/

@[expose] public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- (G-ex₂), with implicit data binders and `by assumption` hypotheses (decision D-13). The
conclusion does not mention `m₀`, so the auto-parameter of `hm₀` first fixes `m₀` from the
hypothesis `∀ g, m₀ ≤ Φ.mass g` (a bare `assumption` could match `0 < P.mγ` or `0 < P.Λ`). -/
theorem existsUnique_withLevel_one {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {rep : F → F} {m₀ : ℝ}
    (he : P.e ≠ 0 := by assumption)
    (hm₀ : 0 < m₀ := by
      exact (‹∀ g, _ ≤ Φ.mass g› |> fun _ => (by assumption : 0 < m₀)))
    (hmass : ∀ g, m₀ ≤ Φ.mass g := by assumption) (hmγ : 0 < P.mγ := by assumption)
    (hΛ : 0 < P.Λ := by assumption) (hrep : ∀ f, rep (rep f) = rep f := by assumption)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0 := by
      assumption)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0 := by
      assumption)
    (hD : IsRenormalizedThrough P Φ D rep 1 := by assumption) :
    ∃! x : (F → ℝ × ℝ × ℝ) × ℝ, IsRenormalizedThrough P Φ (D.withLevel 1 x.1 x.2) rep 2 :=
  QED.GradedProof.GEx2.existsUnique_withLevel_one' P Φ D rep m₀ he hm₀ hmass hmγ hΛ hrep hPV₁
    hPV₂ hD

end QED.Provider.Graded

end
