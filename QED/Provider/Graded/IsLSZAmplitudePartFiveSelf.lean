/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.IsLSZAmplitudePart
public import QED.GradedProof.X1FAssemble
public import QED.GradedProof.X1CPeelVFinal

/-!
# Provider for `QED.Graded.isLSZAmplitudePart_five_self`

Proves the frozen theorem goal `QED.Graded.isLSZAmplitudePart_five_self` (Phase 5 Stage 2 packet,
decision D-57) as `QED.Provider.Graded.isLSZAmplitudePart_five_self`, with the binder convention
of decision D-13, from `QED.GradedProof.X1F.isLSZAmplitudePart_five_self_of_dysonFive` and the
order-`e⁵` Dyson decomposition `QED.GradedProof.X1C.peelV_dysonFive`. This module must never
import the frozen anchor.
-/

@[expose] public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- (X₁), with implicit data binders and `by assumption` hypotheses (decision D-13). The
conclusion does not mention `m₀` or `rep`, so the auto-parameter of `hm₀` first fixes `m₀` from
the hypothesis `∀ g, m₀ ≤ Φ.mass g`, as for (G-ex₂). -/
theorem isLSZAmplitudePart_five_self {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {rep : F → F} {m₀ : ℝ}
    (hm₀ : 0 < m₀ := by
      exact (‹∀ g, _ ≤ Φ.mass g› |> fun _ => (by assumption : 0 < m₀)))
    (hmass : ∀ g, m₀ ≤ Φ.mass g := by assumption) (hmγ : 0 < P.mγ := by assumption)
    (hΛ : 0 < P.Λ := by assumption) (hrep : ∀ f, rep (rep f) = rep f := by assumption)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0 := by
      assumption)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0 := by
      assumption)
    (hopen : rep Φ.openLine = Φ.openLine := by assumption)
    (hD : IsRenormalizedThrough P Φ D rep 2 := by assumption)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2 := by assumption)
    (hp0 : 0 < p 0 := by assumption) :
    (∃ M, IsLSZAmplitudePart P Φ D 5 p p M) ∧ ∀ M, IsLSZAmplitudePart P Φ D 5 p p M → M = 0 :=
  QED.GradedProof.X1F.isLSZAmplitudePart_five_self_of_dysonFive P Φ D rep m₀ hm₀ hmass hmγ hΛ
    hrep hPV₁ hPV₂ hopen hD p hp hp0
    (QED.GradedProof.X1C.peelV_dysonFive P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD)

end QED.Provider.Graded

end
