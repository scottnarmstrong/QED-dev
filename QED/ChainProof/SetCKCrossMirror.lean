/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseBound
public import QED.Integration.SimplexMerge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K: the crossed unit at two photon masses and its mirror symmetry

Helper level (no frozen statement). The merged integrand `crossedTerm μ_a μ_b` of
`QED/TwoLoop/UnitXGraphReduce.lean` carries the photon mass² `μ_a` on the line `z_a` and `μ_b`
on the line `z_b` (`V = E + μ_a z_a + μ_b z_b`). The crossed unit with these photon masses at
`Λ = ∞` is its integral over the 4-simplex of the merged groups `(z_A, z_M, z_c, z_a, z_b)`
(**`crossUnit μ_a μ_b`**); `crossUnit 0 0` is the massless integral of the X link
(`QED.TwoLoop.UnitXClose.xUnitLimitOne_of_dom`). In the hierarchical frame of the set (c) plan the
line `z_b` is inner and `z_a` outer, so `X(t, 0) = crossUnit 0 t` and `X(0, t) = crossUnit t 0`.

* `crossedTerm_mirror`: **the mirror symmetry of the integrand**,
  `T(μ_b, μ_a)(z_c, z_M, z_A, z_b, z_a) = T(μ_a, μ_b)(z_A, z_M, z_c, z_a, z_b)`: reversing the
  electron line exchanges the two photons, the two outer electron lines `z_A ↔ z_c`, and maps
  the merged pair to itself (split `s ↦ z_M - s`; at the midpoint `s = z_M/2` it is fixed). The
  polynomials `U`, `Ẽ`, `Ψ₁(z_M/2)`, `Ψ₂(z_M/2)` are invariant (`ring`).
* `crossUnit_mirror`: **`X(t, 0) = X(0, t)`**, i.e. `crossUnit μ_a μ_b = crossUnit μ_b μ_a`, by the
  permutation invariance of the simplex integral (`integral_simplex_comp_perm`).
* `integrableOn_crossedAt`: the integrand is integrable on `Δ₄` for all `μ_a, μ_b ≥ 0`
  (domination `crossedDom`, uniform in the masses).
* `crossUnit_eq_iterated`: the Cheng–Wu form, as for the massless integrand:
  `crossUnit μ_a μ_b = ∫_{(z₂, z₃) ∈ triangle} ∫₀^∞ dz_A ∫₀^∞ dz_a T(z_A, z₂, z₃, z_a, z_b)`,
  `z_b = 1 - z₂ - z₃`,
  with the integrand integrable on `triangle × (0, ∞)²` (`integrable_crossedH`).

Checked first with sympy (scratch `stageK/mir/m1.py`): the invariance of `U`, `Ẽ`, `Ψ₁`, `Ψ₂`
holds as a polynomial identity, also for a general split `s ↦ z_M - s`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitXClose
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The mirror symmetry of the integrand -/

theorem gXU_mirror (A M c a b : ℝ) : gXU c M A b a = gXU A M c a b := by unfold gXU; ring

theorem gXEn_mirror (A M c a b : ℝ) : gXEn c M A b a = gXEn A M c a b := by unfold gXEn; ring

theorem gXE_mirror (A M c a b : ℝ) : gXE c M A b a = gXE A M c a b := by
  unfold gXE; rw [gXU_mirror, gXEn_mirror]

theorem gPsi1_mirror (A M c a b : ℝ) : gPsi1 c (M / 2) M A b a = gPsi1 A (M / 2) M c a b := by
  simp only [gPsi1, psiT1h, gXan, gXbn, gXU, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem gPsi2_mirror (A M c a b : ℝ) : gPsi2 c (M / 2) M A b a = gPsi2 A (M / 2) M c a b := by
  simp only [gPsi2, psiT2h, gXan, gXbn, gXU, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The mirror symmetry of the crossed integrand**: exchanging the two photon lines together
with the two outer electron lines. -/
theorem crossedTerm_mirror (μa μb A M c a b : ℝ) :
    crossedTerm μb μa c M A b a = crossedTerm μa μb A M c a b := by
  unfold crossedTerm
  rw [gPsi1_mirror, gPsi2_mirror, gXU_mirror, gXE_mirror]
  ring_nf

/-! ### The unit on the simplex -/

/-- The merged integrand `T(μ_a, μ_b)` at a point `w` of `ℝ⁵`. -/
noncomputable def crossedAt (μa μb : ℝ) (w : Fin 5 → ℝ) : ℝ :=
  crossedTerm μa μb (w 0) (w 1) (w 2) (w 3) (w 4)

/-- **The crossed unit with photon masses² `μ_a` (outer line `z_a`) and `μ_b` (inner line
`z_b`)** at `Λ = ∞`: `∫_{Δ₄} T(μ_a, μ_b)`. -/
noncomputable def crossUnit (μa μb : ℝ) : ℝ :=
  ∫ y in simplexSet 4, crossedAt μa μb (simplexPoint y)

/-- The permutation `(z_A, z_M, z_c, z_a, z_b) ↦ (z_c, z_M, z_A, z_b, z_a)`. -/
def crossMirrorPerm : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 3 4

theorem crossedAt_mirror (μa μb : ℝ) (w : Fin 5 → ℝ) :
    crossedAt μb μa (w ∘ crossMirrorPerm) = crossedAt μa μb w := by
  have e0 : crossMirrorPerm 0 = 2 := by decide
  have e1 : crossMirrorPerm 1 = 1 := by decide
  have e2 : crossMirrorPerm 2 = 0 := by decide
  have e3 : crossMirrorPerm 3 = 4 := by decide
  have e4 : crossMirrorPerm 4 = 3 := by decide
  simp only [crossedAt, Function.comp_apply, e0, e1, e2, e3, e4]
  exact crossedTerm_mirror μa μb (w 0) (w 1) (w 2) (w 3) (w 4)

/-- **The mirror symmetry of the crossed unit**: `X(t, 0) = X(0, t)`. -/
theorem crossUnit_mirror (μa μb : ℝ) : crossUnit μa μb = crossUnit μb μa := by
  unfold crossUnit
  rw [← QED.Integration.SimplexMerge.integral_simplex_comp_perm crossMirrorPerm (crossedAt μb μa)]
  congr 1 with y
  exact (crossedAt_mirror μa μb _).symm

theorem measurable_crossedAt (μa μb : ℝ) : Measurable (crossedAt μa μb) :=
  measurable_crossedTerm μa μb

/-- **The crossed integrand is integrable on `Δ₄`** for all photon masses² `μ_a, μ_b ≥ 0`. -/
theorem integrableOn_crossedAt {μa μb : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) :
    IntegrableOn (fun y => crossedAt μa μb (simplexPoint y)) (simplexSet 4) := by
  obtain ⟨C, s, hs0, hs1, hC⟩ := crossedDom
  have hint : IntegrableOn (fun y => C * ∏ k ∈ Finset.univ, simplexPoint y k ^ (-s))
      (simplexSet 4) :=
    (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ hs0 hs1).const_mul _
  have hsp := QED.Integration.TwoLoop.continuous_simplexPoint' (m := 4)
  refine hint.mono' ((measurable_crossedAt μa μb).comp hsp.measurable).aestronglyMeasurable ?_
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos (by norm_num : 0 < 4)]
    with y hy
  rw [Real.norm_eq_abs]
  exact hC μa μb hμa hμb _ hy (sum_simplexPoint y)

theorem crossedAt_smul {μa μb : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) {z : Fin 5 → ℝ}
    (hz : ∀ i, 0 < z i) {t : ℝ} (ht : 0 < t) :
    crossedAt μa μb (t • z) = (t ^ 5)⁻¹ • crossedAt μa μb z := by
  simp only [crossedAt, Pi.smul_apply, smul_eq_mul]
  exact crossedTerm_smul hμa hμb (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht

/-- The integrand in the order `((z₂, z₃), (z_A, z_a))`. -/
noncomputable def crossedH (μa μb : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  crossedTerm μa μb q.2.1 q.1.1 q.1.2 q.2.2 (1 - (q.1.1 + q.1.2))

/-- **Integrability on `triangle × (0, ∞)²`** (Cheng–Wu). -/
theorem integrable_crossedH {μa μb : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) :
    Integrable (crossedH μa μb) ((volume.restrict innerTriangle).prod
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) := by
  have hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      crossedAt μa μb (t • z) = (t ^ 5)⁻¹ • crossedAt μa μb z := fun z hz t ht =>
    crossedAt_smul hμa hμb hz ht
  have hCWi := (integrableOn_simplex_chengWuSet_iff (by norm_num) innerSet (crossedAt μa μb)
    hF).mp (integrableOn_crossedAt hμa hμb)
  simp only [sum_innerSet] at hCWi
  have he := measurePreserving_splitInner.symm
  have hint := (he.integrableOn_comp_preimage splitInner.symm.measurableEmbedding).mpr hCWi
  rw [preimage_splitInner_symm] at hint
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  refine hint.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp_apply, splitInner_symm_apply]
  rfl

/-- **The crossed unit as an iterated integral in the hierarchical variables** (Cheng–Wu with
the constraint on the inner simplex `z₂ + z₃ + z_b = 1`). -/
theorem crossUnit_eq_iterated {μa μb : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) :
    crossUnit μa μb = ∫ p in innerTriangle, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
      crossedTerm μa μb zA p.1 p.2 za (1 - (p.1 + p.2)) := by
  have hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      crossedAt μa μb (t • z) = (t ^ 5)⁻¹ • crossedAt μa μb z := fun z hz t ht =>
    crossedAt_smul hμa hμb hz ht
  have hCW := integral_simplex_chengWuSet (by norm_num) innerSet (crossedAt μa μb) hF
  have hCWi := (integrableOn_simplex_chengWuSet_iff (by norm_num) innerSet (crossedAt μa μb)
    hF).mp (integrableOn_crossedAt hμa hμb)
  simp only [sum_innerSet] at hCW hCWi
  rw [crossUnit, hCW, integral_cwSet_innerSet hCWi]
  rfl

end QED.ChainProof.SetCK

end
