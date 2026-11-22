/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsVPShareOnShell
public import QED.Frozen.Graded.IsRenormalizedThrough
import QED.ChainProof.SetCLinkFinal

/-!
# Provider for `QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂`

Proves the frozen theorem goal (WI-s) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.isVPShareOnShell_d₁_eq_d₂`, with the binder convention of decision
D-13, from `QED.ChainProof.SetCLink.isVPShareOnShell_d₁_eq_d₂_c`
(`QED/ChainProof/SetCLinkFinal.lean`). This module must never import the frozen anchor.
-/

public section

open QED.WickModel (Params)

namespace QED.Provider.ThreeLoop

/-- (WI-s), with implicit data binders and `by assumption` hypotheses (decision D-13);
the `hm₀` default resolves `m₀` by name in the caller's context, as for (G-ex₂). -/
theorem isVPShareOnShell_d₁_eq_d₂ {P : Params} {F : Type} [Fintype F]
    [DecidableEq F] {Φ : Lepton.Flavors F} {D : Graded.Counterterms F} {rep : F → F} {m₀ : ℝ}
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
    (hD : Graded.IsRenormalizedThrough P Φ D rep 1 := by assumption) {s : ℝ × ℝ × ℝ}
    (hs : QED.ThreeLoop.IsVPShareOnShell P Φ D s := by assumption) : s.1 = s.2.1 :=
  QED.ChainProof.SetCLink.isVPShareOnShell_d₁_eq_d₂_c P Φ D rep m₀ he hm₀ hmass hmγ hΛ hrep hPV₁
    hPV₂ hD s hs

end QED.Provider.ThreeLoop

end
