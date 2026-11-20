/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajGrowD
public import QED.GradedProof.RPi4MajSplit

/-!
# (R-Π₄) step L10, one loop: the single-flavour blocks along the ray for masses at least `m₀`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The one-loop
input `∀ g, MajTiltRay (fLim Φ rep e (Pi.single g 1))` of `maj_rayVal_of_inputs` was proved
(`QED.GradedProof.RPi4.maj_tiltRay_fLim_gen`) for flavour masses at least `1`. The same proof
works for masses at least any `m₀ > 0`: the pieces `maj_tiltRay_insVal` already take a general
lower mass bound, and the auxiliary regulator mass `1 + ∑ M_g` exceeds every flavour mass.

* `maj_tiltRay_fbVal_pos`: `MajTiltRay` of the block-summed bubble at the threshold `m₀`;
* **`maj_tiltRay_fLim_pos`**: `MajTiltRay (fLim Φ rep e δ)` for masses at least `m₀ > 0`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

section Block

variable (P : Params) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)

include hm₀ hmass

/-- The auxiliary regulator mass exceeds every flavour mass by at least `1`. -/
theorem maj_mass_add_one_le_auxX (f : F) : Φ.mass f + 1 ≤ auxX Φ := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun g => Φ.mass g)
    (fun g _ => hm₀.le.trans (hmass g)) (Finset.mem_univ f)
  simp only [auxX]
  linarith

/-- **`MajTiltRay` of the block-summed bubble** at the pure mass insertion `ctδ D`, threshold
`m₀`, masses at least `m₀`. -/
theorem maj_tiltRay_fbVal_pos (sw : Bool) {bx bY : Bool} (h : bx ≠ bY) :
    MajTiltRay fun k μ ν => fbVal P Φ (ctδ D) rep m₀ sw bx bY k μ ν := by
  refine MajTiltRay.sum Finset.univ fun f _ => ?_
  have hX : m₀ ≤ auxX Φ := by
    have := maj_mass_add_one_le_auxX Φ hm₀ hmass f
    linarith [hmass f]
  refine ((maj_tiltRay_insVal sw (P.e ^ 2 * (ctδ D).dm (rep f) 0) h hm₀ (hmass f) hX
    (Y := auxX Φ + 1) (by linarith)).const_mul ((Φ.coeff f : ℂ) * kF P.e)).congr fun s _ => ?_
  simp [ctδ]

end Block

section Lim

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)

include hrep hPV₁ hPV₂ hm₀ hmass

/-- **The one-loop block along the ray, any weights, masses at least `m₀ > 0`.** -/
theorem maj_tiltRay_fLim_pos (he : P.e ≠ 0) (δ : F → ℝ) :
    MajTiltRay (fLim Φ rep P.e δ) := by
  refine ((maj_tiltRay_fbVal_pos P Φ (ctOf P.e δ) rep hm₀ hmass true
    (by decide : true ≠ false)).add (maj_tiltRay_fbVal_pos P Φ (ctOf P.e δ) rep hm₀ hmass false
      (by decide : false ≠ true))).congr fun s hs => ?_
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot (majRayVec s) (majRayVec s) := by
    rw [dot_majRayVec (by linarith)]
    nlinarith [sq_nonneg m₀]
  exact (fLim_eq_fbVal P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he δ hk 2 3).symm

end Lim

end QED.GradedProof.RPi4

end
