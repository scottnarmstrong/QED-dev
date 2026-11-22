/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4Gauge
import QED.TwoLoop.UnitXGraphChengWuSet
import QED.Integration.ChengWu

/-!
# Set (e), master I₄: the Cheng–Wu gauge on the electron lines

For the evaluation of `P'(0)` the natural Cheng–Wu gauge of I₄ fixes the sum of the three
electron parameters, `a + b + c = 1`, leaving the photon parameters `l, m, n ∈ (0, ∞)`. On shell
`F = m (S U₁ - U₂) + S U₂` with `S = a + b + c`, `U = m U₁ + U₂`, so in this gauge `F / U` is
`1` minus the effective resistance between the external vertices
(`QED.ThreeLoopE.SetEMastersI4P1SM`).

For `g` homogeneous of degree `-6` on the positive orthant,

  `∫_{i4Dom} g(a, b, c, l, m, n) = ∫_{sDom} g(a, b, 1 - a - b, l, m, n)`,

with `sDom = {a, b > 0, a + b < 1, l, n, m > 0}` in the coordinate order `(a, b, l, n, m)`
(`QED.ThreeLoopE.i4SGauge_integral`, `QED.ThreeLoopE.i4SGauge_integrableOn_iff`). The proof
relabels the simplex coordinates so that `c` is the eliminated one and applies the Cheng–Wu
theorem `QED.TwoLoop.UnitXGraph.integral_simplex_chengWuSet` with gauge set `{0, 1}`; there is no
further Jacobian. The relabelling steps are those of `QED.ThreeLoopE.SetEMastersI4Gauge`.

## Main definitions

* `QED.ThreeLoopE.i4SDom`, `QED.ThreeLoopE.i4SIntegrand`.

## Main results

* `QED.ThreeLoopE.i4SGauge_integral`, `QED.ThreeLoopE.i4SGauge_integrableOn_iff`.
-/

@[expose] public section

open MeasureTheory Set Function

namespace QED.ThreeLoopE

/-- The domain of the electron-line gauge, coordinates `(a, b, l, n, m)`. -/
def i4SDom : Set I4Coords :=
  {x | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2.1 ∧ 0 < x.2.2.2.2 ∧ x.1 + x.2.1 < 1}

/-- The integrand in the electron-line gauge: `g(a, b, 1 - a - b, l, m, n)`. -/
def i4SIntegrand (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x : I4Coords) : ℝ :=
  g x.1 x.2.1 (1 - x.1 - x.2.1) x.2.2.1 x.2.2.2.2 x.2.2.2.1

private def gaugeCoordsEquiv : (Fin 5 → ℝ) ≃ᵐ I4Coords :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
        ((MeasurableEquiv.refl ℝ).prodCongr
          ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
            ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ => ℝ)))))))

private theorem measurePreserving_gaugeCoordsEquiv : MeasurePreserving gaugeCoordsEquiv := by
  unfold gaugeCoordsEquiv
  exact ((((MeasurePreserving.id volume).prod
    ((((MeasurePreserving.id volume).prod
      ((((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ => ℝ)))).comp
        (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)))).comp
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)))).comp
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0))

private theorem gaugeCoordsEquiv_apply (x : Fin 5 → ℝ) :
    gaugeCoordsEquiv x = (x 0, x 1, x 2, x 3, x 4) := by
  rfl

private theorem preimage_gauge_i4Dom :
    gaugeCoordsEquiv ⁻¹' i4Dom = QED.Integration.ChengWu.openSimplex 5 := by
  ext x
  simp [gaugeCoordsEquiv_apply, i4Dom, QED.Integration.ChengWu.mem_openSimplex,
    Fin.forall_fin_succ, Fin.sum_univ_succ, add_assoc, and_assoc]

/-- The relabelled six-coordinate form of `g`: `(a, b, l, n, m, c)` on the simplex. -/
private def gaugeForm (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (z : Fin 6 → ℝ) : ℝ :=
  g (z 0) (z 1) (z 5) (z 2) (z 4) (z 3)

private def gaugePerm : Equiv.Perm (Fin 5) := Equiv.swap 2 3

private def gaugePermEquiv : (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 5 => ℝ) gaugePerm

private theorem gaugePermEquiv_apply (x : Fin 5 → ℝ) (i : Fin 5) :
    gaugePermEquiv x i = x (gaugePerm.symm i) := by
  simpa [gaugePermEquiv] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) gaugePerm x (gaugePerm.symm i)

private theorem measurePreserving_gaugePermEquiv : MeasurePreserving gaugePermEquiv :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin 5 => ℝ) gaugePerm

open QED.Integration Feynman TwoLoop ChengWu in
private theorem preimage_gaugePerm :
    gaugePermEquiv ⁻¹' simplexSet 5 = simplexSet 5 := by
  ext x
  simp only [mem_preimage]
  rw [mem_simplexSet_iff (by decide), mem_simplexSet_iff (by decide)]
  have hlast : simplexPoint (gaugePermEquiv x) (Fin.last 5) = simplexPoint x (Fin.last 5) := by
    simp only [simplexPoint_last, gaugePermEquiv_apply, Equiv.sum_comp]
  constructor
  · intro h i
    induction i using Fin.lastCases with
    | last => rw [← hlast]; exact h _
    | cast j =>
      simpa only [simplexPoint_castSucc, gaugePermEquiv_apply, Equiv.symm_apply_apply] using
        h (gaugePerm j).castSucc
  · intro h i
    induction i using Fin.lastCases with
    | last => rw [hlast]; exact h _
    | cast j =>
      simpa only [simplexPoint_castSucc, gaugePermEquiv_apply] using h (gaugePerm.symm j).castSucc

/-- The composite chart from the simplex to `i4Dom`. -/
private def gaugeChart (x : Fin 5 → ℝ) : I4Coords :=
  gaugeCoordsEquiv (QED.Integration.TwoLoop.simplexSwap 2 (gaugePermEquiv x))

open QED.Integration Feynman TwoLoop ChengWu in
private theorem gaugeChart_apply (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x : Fin 5 → ℝ) :
    i4SimplexIntegrand g (gaugeChart x) = gaugeForm g (simplexPoint x) := by
  have hu (z : Fin 5 → ℝ) : i4SimplexIntegrand g (gaugeCoordsEquiv z) =
      g (simplexPoint z 0) (simplexPoint z 1) (simplexPoint z 2)
        (simplexPoint z 3) (simplexPoint z 4) (simplexPoint z 5) := by
    have hsum : ∑ i, z i = z 0 + (z 1 + (z 2 + (z 3 + z 4))) := by
      simp [Fin.sum_univ_succ]
    simp only [i4SimplexIntegrand, i4Last, gaugeCoordsEquiv_apply,
      show (0 : Fin 6) = (0 : Fin 5).castSucc from rfl,
      show (1 : Fin 6) = (1 : Fin 5).castSucc from rfl,
      show (2 : Fin 6) = (2 : Fin 5).castSucc from rfl,
      show (3 : Fin 6) = (3 : Fin 5).castSucc from rfl,
      show (4 : Fin 6) = (4 : Fin 5).castSucc from rfl,
      show (5 : Fin 6) = Fin.last 5 from rfl,
      simplexPoint_castSucc, simplexPoint_last, hsum, add_assoc]
  rw [gaugeChart, hu]
  unfold gaugeForm
  simp only [simplexPoint_simplexSwap]
  have hlast : simplexPoint (gaugePermEquiv x) 5 = simplexPoint x 5 := by
    change simplexPoint (gaugePermEquiv x) (Fin.last 5) = simplexPoint x (Fin.last 5)
    simp only [simplexPoint_last, gaugePermEquiv_apply, Equiv.sum_comp]
  have shift :
      ∀ i : Fin 6, simplexPoint (gaugePermEquiv x) i =
        simplexPoint x (Equiv.swap (2 : Fin 6) 3 i) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [show Equiv.swap (2 : Fin 6) 3 (Fin.last 5) = Fin.last 5 from by decide]
      exact hlast
    | cast j =>
      have hj : Equiv.swap (2 : Fin 6) 3 j.castSucc = (gaugePerm.symm j).castSucc := by
        fin_cases j <;> decide
      rw [hj, simplexPoint_castSucc, simplexPoint_castSucc, gaugePermEquiv_apply]
  simp only [shift]
  rfl

open QED.Integration Feynman TwoLoop ChengWu in
private theorem gauge_simplex_integral (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) :
    ∫ x in i4Dom, i4SimplexIntegrand g x = ∫ x in simplexSet 5, gaugeForm g (simplexPoint x) := by
  rw [← measurePreserving_gaugeCoordsEquiv.setIntegral_preimage_emb
    gaugeCoordsEquiv.measurableEmbedding, preimage_gauge_i4Dom,
    ← setIntegral_congr_set (simplexSet_ae_eq_openSimplex (0 : Fin 5)),
    ← (measurePreserving_simplexSwap (2 : Fin 5)).setIntegral_preimage_emb
      (simplexSwapEquiv 2).measurableEmbedding, preimage_simplexSwap,
    ← measurePreserving_gaugePermEquiv.setIntegral_preimage_emb
      gaugePermEquiv.measurableEmbedding, preimage_gaugePerm]
  exact setIntegral_congr_fun (measurableSet_simplexSet _) fun x _ => gaugeChart_apply g x

open QED.Integration Feynman TwoLoop ChengWu in
private theorem gauge_simplex_integrableOn (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) :
    IntegrableOn (i4SimplexIntegrand g) i4Dom ↔
      IntegrableOn (fun x => gaugeForm g (simplexPoint x)) (simplexSet 5) := by
  rw [← measurePreserving_gaugeCoordsEquiv.integrableOn_comp_preimage
    gaugeCoordsEquiv.measurableEmbedding, preimage_gauge_i4Dom, IntegrableOn,
    ← Measure.restrict_congr_set (simplexSet_ae_eq_openSimplex (0 : Fin 5)), ← IntegrableOn,
    ← (measurePreserving_simplexSwap (2 : Fin 5)).integrableOn_comp_preimage
      (simplexSwapEquiv 2).measurableEmbedding, preimage_simplexSwap,
    ← measurePreserving_gaugePermEquiv.integrableOn_comp_preimage
      gaugePermEquiv.measurableEmbedding, preimage_gaugePerm]
  exact integrableOn_congr_fun (fun x _ => gaugeChart_apply g x) (measurableSet_simplexSet _)

private theorem preimage_i4SDom :
    gaugeCoordsEquiv ⁻¹' i4SDom = QED.TwoLoop.UnitXGraph.cwSet ({0, 1} : Finset (Fin 5)) := by
  ext z
  simp only [mem_preimage, gaugeCoordsEquiv_apply, i4SDom, mem_ofPred_eq,
    QED.TwoLoop.UnitXGraph.mem_cwSet,
    Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({1} : Finset (Fin 5))), Finset.sum_singleton,
    Fin.forall_fin_succ]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, hs⟩
    exact ⟨⟨h0, h1, h2, h3, h4, trivial⟩, hs⟩
  · rintro ⟨⟨h0, h1, h2, h3, h4, -⟩, hs⟩
    exact ⟨h0, h1, h2, h3, h4, hs⟩

private theorem gauge_cw_eq (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (w : Fin 5 → ℝ) :
    gaugeForm g (Fin.snoc w (1 - ∑ i ∈ ({0, 1} : Finset (Fin 5)), w i)) =
      i4SIntegrand g (gaugeCoordsEquiv w) := by
  have hsnoc (t : ℝ) (i : Fin 5) :
      Fin.snoc (α := fun _ : Fin 6 => ℝ) w t i.castSucc = w i :=
    Fin.snoc_castSucc (α := fun _ : Fin 6 => ℝ) t w i
  simp only [gaugeForm, i4SIntegrand, gaugeCoordsEquiv_apply,
    show (5 : Fin 6) = Fin.last 5 from rfl, Fin.snoc_last,
    show (0 : Fin 6) = (0 : Fin 5).castSucc from rfl,
    show (1 : Fin 6) = (1 : Fin 5).castSucc from rfl,
    show (2 : Fin 6) = (2 : Fin 5).castSucc from rfl,
    show (3 : Fin 6) = (3 : Fin 5).castSucc from rfl,
    show (4 : Fin 6) = (4 : Fin 5).castSucc from rfl, hsnoc,
    Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({1} : Finset (Fin 5))), Finset.sum_singleton]
  ring_nf

private theorem gaugeForm_smul {g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ∀ a b c l m n t : ℝ, 0 < a → 0 < b → 0 < c → 0 < l → 0 < m → 0 < n → 0 < t →
      g (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) = (t ^ 6)⁻¹ * g a b c l m n)
    (z : Fin 6 → ℝ) (hz : ∀ i, 0 < z i) (t : ℝ) (ht : 0 < t) :
    gaugeForm g (t • z) = (t ^ 6)⁻¹ • gaugeForm g z := by
  simp only [gaugeForm, Pi.smul_apply, smul_eq_mul]
  exact hg _ _ _ _ _ _ _ (hz 0) (hz 1) (hz 5) (hz 2) (hz 4) (hz 3) ht

private theorem measurableSet_i4SDom : MeasurableSet i4SDom := by
  unfold i4SDom
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const (by fun_prop)).inter
    ((measurableSet_lt measurable_const (by fun_prop)).inter
      ((measurableSet_lt measurable_const (by fun_prop)).inter
        ((measurableSet_lt measurable_const (by fun_prop)).inter
          ((measurableSet_lt measurable_const (by fun_prop)).inter
            (measurableSet_lt (by fun_prop) measurable_const)))))

open QED.Integration.Feynman QED.TwoLoop.UnitXGraph in
/-- **The electron-line gauge, integrals.** For `g` homogeneous of degree `-6`,
`∫_{i4Dom} g(a, b, c, l, m, n) = ∫_{sDom} g(a, b, 1 - a - b, l, m, n)`. -/
theorem i4SGauge_integral {g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ∀ a b c l m n t : ℝ, 0 < a → 0 < b → 0 < c → 0 < l → 0 < m → 0 < n → 0 < t →
      g (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) = (t ^ 6)⁻¹ * g a b c l m n) :
    ∫ x in i4Dom, i4SimplexIntegrand g x = ∫ x in i4SDom, i4SIntegrand g x := by
  rw [gauge_simplex_integral, integral_simplex_chengWuSet (by decide : 0 < 5)
    ({0, 1} : Finset (Fin 5)) (gaugeForm g) (gaugeForm_smul hg),
    ← measurePreserving_gaugeCoordsEquiv.setIntegral_preimage_emb
      gaugeCoordsEquiv.measurableEmbedding (i4SIntegrand g) i4SDom, preimage_i4SDom]
  exact setIntegral_congr_fun (measurableSet_cwSet _) fun w _ => gauge_cw_eq g w

open QED.Integration.Feynman QED.TwoLoop.UnitXGraph in
/-- **The electron-line gauge, integrability.** -/
theorem i4SGauge_integrableOn_iff {g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ∀ a b c l m n t : ℝ, 0 < a → 0 < b → 0 < c → 0 < l → 0 < m → 0 < n → 0 < t →
      g (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) = (t ^ 6)⁻¹ * g a b c l m n) :
    IntegrableOn (i4SimplexIntegrand g) i4Dom ↔ IntegrableOn (i4SIntegrand g) i4SDom := by
  rw [gauge_simplex_integrableOn, integrableOn_simplex_chengWuSet_iff (by decide : 0 < 5)
    ({0, 1} : Finset (Fin 5)) (gaugeForm g) (gaugeForm_smul hg),
    ← measurePreserving_gaugeCoordsEquiv.integrableOn_comp_preimage
      gaugeCoordsEquiv.measurableEmbedding (f := i4SIntegrand g) (s := i4SDom), preimage_i4SDom]
  exact integrableOn_congr_fun (fun w _ => gauge_cw_eq g w) (measurableSet_cwSet _)

end QED.ThreeLoopE

end
