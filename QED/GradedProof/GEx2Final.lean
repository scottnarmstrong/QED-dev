/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.GEx2Assemble
public import QED.GradedProof.SE2RealFinal
public import QED.GradedProof.VP2RealFinal
public import QED.GradedProof.V5ZeroInput

/-!
# (G-ex₂): the order-`e⁴` conditions fix the level-`1` counterterms

Helper proof of the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), as `QED.GradedProof.GEx2.existsUnique_withLevel_one'`.

`QED.GradedProof.GEx2.existsUnique_withLevel_one_of_inputs` proves the conclusion from three
analytic inputs at `D₀ = D.withLevel 1 0 0`; they are supplied by

* `QED.GradedProof.SE2Real.seReal` (reality of the order-`4` on-shell self-energy data),
* `QED.GradedProof.VP2Real.vpReal` (reality of the order-`4` vacuum polarization at `s = 0`),
* `QED.GradedProof.V5Zero.vertexZeroInput` (the order-`5` vertex at `q = 0`),

with the total Pauli–Villars conditions from the block ones (`GEx2.sum_eq_zero_of_blocks`) and the
level-`0` scheme condition of `D₀` from that of `D`.
-/

@[expose] public section

namespace QED.GradedProof.GEx2

open QED.Graded
open QED.WickModel (Params)

/-- **(G-ex₂).** Under the hypotheses of (G-Π₂) on the scheme `rep`, with `e ≠ 0`: if `D` is
renormalized through order `e²`, exactly one choice of level-`1` data renormalizes it through
order `e⁴`. -/
theorem existsUnique_withLevel_one' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ) (he : P.e ≠ 0)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 1) :
    ∃! x : (F → ℝ × ℝ × ℝ) × ℝ, IsRenormalizedThrough P Φ (D.withLevel 1 x.1 x.2) rep 2 := by
  classical
  have hPV₁t := sum_eq_zero_of_blocks rep hrep _ hPV₁
  have hPV₂t := sum_eq_zero_of_blocks rep hrep _ hPV₂
  set D₀ := D.withLevel 1 (fun _ => (0, 0, 0)) 0 with hD₀
  have hD0 : ∀ f, D₀.d₁ f 0 = D₀.d₁ (rep f) 0 ∧ D₀.d₂ f 0 = D₀.d₂ (rep f) 0 ∧
      D₀.dm f 0 = D₀.dm (rep f) 0 := fun f => by
    simpa [hD₀, Counterterms.withLevel] using hD.1 f 0 (by norm_num)
  exact existsUnique_withLevel_one_of_inputs P Φ D rep m₀ he hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD
    (fun f => SE2Real.seReal P Φ D₀ f m₀ hm₀ hmass hmγ hΛ hPV₁t hPV₂t)
    (VP2Real.vpReal P Φ D₀ rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD0)
    (fun f => V5Zero.vertexZeroInput P Φ D₀ f m₀ hm₀ hmass hmγ hΛ hPV₁t hPV₂t)

end QED.GradedProof.GEx2

end
