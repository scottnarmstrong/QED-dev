/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealV
public import QED.GradedProof.SE2RealRX
public import QED.GradedProof.SE2RealF

/-!
# The input `SEReal` of (G-ex₂)

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57). Under the hypotheses of (G-Σ₂), the order-`4` self-energy of every flavour has
real on-shell value and derivative (`QED.GradedProof.GEx2.SEReal`): the eight reality class
obligations (`classSharp_repR`, …, `classSharp_repC2`) with `seReal_of_classes`.
-/

@[expose] public section

open QED.WickModel (Params)

namespace QED.GradedProof.SE2Real

open QED.Graded QED.GradedProof.SE2

/-- **`SEReal` under the hypotheses of (G-Σ₂).** -/
theorem seReal (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) : GEx2.SEReal P Φ D f :=
  seReal_of_classes classSharp_repR classSharp_repX classSharp_repV classSharp_repF
    classSharp_repP0 classSharp_repP1 classSharp_repC1 classSharp_repC2 P Φ D f m₀ hm₀ hmass hmγ
    hΛ hPV₁ hPV₂

end QED.GradedProof.SE2Real

end
