/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCoordJac
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Set (c), Stage K, closed forms: integrals over the inner triangle in threshold coordinates

Helper level (no frozen statement). Shared layer of the closed forms of `ρ_C` and `ρ_X`. For any
`g : ℝ × ℝ → ℝ` integrable on the triangle `T = {0 < y₃ < Y < X}` (`coordT`), `0 < X < 1`,

**`coord_integral_eq`**: `u ↦ I(u)` is integrable on `(0, X)` and `∫_T g = ∫₀^X I(u) du`, with
`I(u) = ∫_{(s_lo(u), 1-u]} J₁ g(Ψ₁(u, s)) ds + ∫_{(1-u, 1)} J₂ g(Ψ₂(u, s)) ds`,

the two-dimensional change of variables (`integral_image_eq_integral_abs_det_fderiv_smul`) on
each branch of the threshold coordinates (`SetCKCoordMaps`, Jacobians from `SetCKCoordJac`)
followed by Fubini (`coord_setIntegral_prod`). The integrability of `g` on `T` is transported to
both branches (`coord_integrableOn_iff`). The square form used by the node integrals,
`∫∫_{(0,1)²} 1{y₃ < Y < X} g = ∫_T g`, is `coord_integral_square`.

For a generic integrand of the threshold, `g(Y, y₃) = f(Y, y₃, s(Y, y₃))` with
`s = formXThr Y y₃ (w_Y(X))`, **`coord_integral_thr`** gives the same with `g(Ψ_b(u, s))`
replaced by `f(Ψ_b(u, s), s)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {X : ℝ}

theorem measurable_coordSLo (X : ℝ) : Measurable (coordSLo X) := by
  unfold coordSLo; fun_prop

theorem measurableSet_coordR1 (X : ℝ) : MeasurableSet (coordR1 X) := by
  have h1 : Measurable fun p : ℝ × ℝ => coordSLo X p.1 :=
    (measurable_coordSLo X).comp measurable_fst
  exact ((measurableSet_Ioo.preimage measurable_fst).inter
    ((measurableSet_lt h1 measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))))

theorem measurableSet_coordR2 (X : ℝ) : MeasurableSet (coordR2 X) :=
  ((measurableSet_Ioo.preimage measurable_fst).inter
    ((measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)))

theorem measurableSet_coordT (X : ℝ) : MeasurableSet (coordT X) :=
  ((measurableSet_Ioo.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)))

theorem coord_hasFDerivWithin1 (hX : X ∈ Ioo (0 : ℝ) 1) :
    ∀ p ∈ coordR1 X, HasFDerivWithinAt (coordPsi1 X) (coordDer1 X p) (coordR1 X) p :=
  fun _ hp => (hasFDerivAt_coordPsi1 (coordM_pos hX hp.1.1.le).ne'
    (coordPsi1_spec hX hp).2.1.1.ne').hasFDerivWithinAt

theorem coord_hasFDerivWithin2 (hX : X ∈ Ioo (0 : ℝ) 1) :
    ∀ p ∈ coordR2 X, HasFDerivWithinAt (coordPsi2 X) (coordDer2 X p) (coordR2 X) p :=
  fun _ hp => (hasFDerivAt_coordPsi2 (coordD_pos hX hp.1.1 hp.2.2).ne'
    (coordPsi2_spec hX hp).2.1.1.ne').hasFDerivWithinAt

/-- **Integrability on the triangle** is integrability of both transported integrands. -/
theorem coord_integrableOn_iff (hX : X ∈ Ioo (0 : ℝ) 1) (g : ℝ × ℝ → ℝ) :
    IntegrableOn g (coordT X) ↔
      IntegrableOn (fun p => coordJ1 X p.1 p.2 * g (coordPsi1 X p)) (coordR1 X) ∧
        IntegrableOn (fun p => coordJ2 X p.1 p.2 * g (coordPsi2 X p)) (coordR2 X) := by
  rw [coordT_eq hX, integrableOn_union,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_coordR1 X)
      (coord_hasFDerivWithin1 hX) (coord_injOn1 hX),
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_coordR2 X)
      (coord_hasFDerivWithin2 hX) (coord_injOn2 hX)]
  refine and_congr (integrableOn_congr_fun (fun _p hp => ?_) (measurableSet_coordR1 X))
    (integrableOn_congr_fun (fun _p hp => ?_) (measurableSet_coordR2 X))
  · simp only [smul_eq_mul, abs_det_coordDer1 hX hp]
  · simp only [smul_eq_mul, abs_det_coordDer2 hX hp]

/-- **The change of variables on the triangle**, one integral per branch. -/
theorem coord_setIntegral_eq (hX : X ∈ Ioo (0 : ℝ) 1) {g : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g (coordT X)) :
    ∫ q in coordT X, g q = (∫ p in coordR1 X, coordJ1 X p.1 p.2 * g (coordPsi1 X p)) +
      ∫ p in coordR2 X, coordJ2 X p.1 p.2 * g (coordPsi2 X p) := by
  have hm2 := measurable_image_of_fderivWithin (measurableSet_coordR2 X)
    (coord_hasFDerivWithin2 hX) (coord_injOn2 hX)
  rw [coordT_eq hX] at hg ⊢
  rw [setIntegral_union (coord_disjoint hX) hm2 (hg.mono_set subset_union_left)
      (hg.mono_set subset_union_right),
    integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_coordR1 X)
      (coord_hasFDerivWithin1 hX) (coord_injOn1 hX),
    integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_coordR2 X)
      (coord_hasFDerivWithin2 hX) (coord_injOn2 hX)]
  congr 1
  · refine setIntegral_congr_fun (measurableSet_coordR1 X) fun p hp => ?_
    simp only [smul_eq_mul, abs_det_coordDer1 hX hp]
  · refine setIntegral_congr_fun (measurableSet_coordR2 X) fun p hp => ?_
    simp only [smul_eq_mul, abs_det_coordDer2 hX hp]

end

/-- **Fubini on a region `{u ∈ A, s ∈ B(u)}`** of the plane. -/
theorem coord_setIntegral_prod {A : Set ℝ} {B : ℝ → Set ℝ} (hA : MeasurableSet A)
    (hB : ∀ u, MeasurableSet (B u)) (hR : MeasurableSet {p : ℝ × ℝ | p.1 ∈ A ∧ p.2 ∈ B p.1})
    {F : ℝ × ℝ → ℝ} (hF : IntegrableOn F {p : ℝ × ℝ | p.1 ∈ A ∧ p.2 ∈ B p.1}) :
    IntegrableOn (fun u => ∫ s in B u, F (u, s)) A ∧
      ∫ p in {p : ℝ × ℝ | p.1 ∈ A ∧ p.2 ∈ B p.1}, F p = ∫ u in A, ∫ s in B u, F (u, s) := by
  set R := {p : ℝ × ℝ | p.1 ∈ A ∧ p.2 ∈ B p.1}
  have hI : Integrable (R.indicator F) ((volume : Measure ℝ).prod volume) :=
    (integrable_indicator_iff hR).2 hF
  have hfib : ∀ u, ∫ s, R.indicator F (u, s) = A.indicator (fun u => ∫ s in B u, F (u, s)) u := by
    intro u
    by_cases hu : u ∈ A
    · rw [indicator_of_mem hu, ← integral_indicator (hB u)]
      congr 1
      funext s
      by_cases hs : s ∈ B u
      · rw [indicator_of_mem (show (u, s) ∈ R from ⟨hu, hs⟩), indicator_of_mem hs]
      · rw [indicator_of_notMem (show (u, s) ∉ R from fun h => hs h.2),
          indicator_of_notMem hs]
    · rw [indicator_of_notMem hu]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      exact indicator_of_notMem (show (u, s) ∉ R from fun h => hu h.1) _
  refine ⟨(integrable_indicator_iff hA).1 (hI.integral_prod_left.congr
    (Eventually.of_forall hfib)), ?_⟩
  rw [← integral_indicator hR, Measure.volume_eq_prod, integral_prod _ hI, ← integral_indicator hA]
  exact integral_congr_ae (Eventually.of_forall hfib)

section

variable {X : ℝ}

/-- **The triangle integral as an iterated `(u, s)` integral.** -/
theorem coord_integral_eq (hX : X ∈ Ioo (0 : ℝ) 1) {g : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g (coordT X)) :
    IntegrableOn (fun u => (∫ s in Ioc (coordSLo X u) (1 - u),
        coordJ1 X u s * g (coordPsi1 X (u, s))) +
        ∫ s in Ioo (1 - u) 1, coordJ2 X u s * g (coordPsi2 X (u, s))) (Ioo 0 X) ∧
      ∫ q in coordT X, g q = ∫ u in Ioo 0 X, ((∫ s in Ioc (coordSLo X u) (1 - u),
        coordJ1 X u s * g (coordPsi1 X (u, s))) +
        ∫ s in Ioo (1 - u) 1, coordJ2 X u s * g (coordPsi2 X (u, s))) := by
  obtain ⟨h1, h2⟩ := (coord_integrableOn_iff hX g).1 hg
  obtain ⟨i1, e1⟩ := coord_setIntegral_prod (A := Ioo 0 X)
    (B := fun u => Ioc (coordSLo X u) (1 - u)) measurableSet_Ioo (fun _ => measurableSet_Ioc)
    (measurableSet_coordR1 X) h1
  obtain ⟨i2, e2⟩ := coord_setIntegral_prod (A := Ioo 0 X) (B := fun u => Ioo (1 - u) 1)
    measurableSet_Ioo (fun _ => measurableSet_Ioo) (measurableSet_coordR2 X) h2
  refine ⟨i1.add i2, ?_⟩
  rw [coord_setIntegral_eq hX hg]
  erw [e1, e2]
  rw [← integral_add i1 i2]

/-- **The square form**: `∫∫_{(0,1)²} 1{y₃ < Y < X} g = ∫_T g`, with integrability. -/
theorem coord_integral_square (hX : X ∈ Ioo (0 : ℝ) 1) (g : ℝ × ℝ → ℝ) :
    (Integrable (fun q : ℝ × ℝ => if q.2 < q.1 ∧ q.1 < X then g q else 0)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ↔
      IntegrableOn g (coordT X)) ∧
    ∫ q, (if q.2 < q.1 ∧ q.1 < X then g q else 0)
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ q in coordT X, g q := by
  set T' := {q : ℝ × ℝ | q.2 < q.1 ∧ q.1 < X}
  have hT' : MeasurableSet T' :=
    (measurableSet_lt measurable_snd measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  have he : (fun q : ℝ × ℝ => if q.2 < q.1 ∧ q.1 < X then g q else 0) = T'.indicator g := by
    funext q
    by_cases h : q.2 < q.1 ∧ q.1 < X
    · rw [ite_eq_left h, indicator_of_mem (show q ∈ T' from h)]
    · rw [ite_eq_right h, indicator_of_notMem (show q ∉ T' from h)]
  have hS : T' ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = coordT X := by
    ext ⟨Y, y3⟩
    simp only [T', coordT, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, -⟩, h5, -⟩
      exact ⟨⟨h3, h2⟩, h5, h1⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h4, h2⟩, ⟨h1, by linarith [hX.2]⟩, h3, by linarith [hX.2]⟩
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod, he]
  refine ⟨?_, ?_⟩
  · rw [integrable_indicator_iff hT', IntegrableOn, Measure.restrict_restrict hT', hS]
    rfl
  · rw [integral_indicator hT', Measure.restrict_restrict hT', hS]

/-- **The iterated form for an integrand of the threshold**:
`g(Y, y₃) = f(Y, y₃, s(Y, y₃))`, `s = formXThr Y y₃ (w_Y(X))`. -/
theorem coord_integral_thr (hX : X ∈ Ioo (0 : ℝ) 1) {f : ℝ → ℝ → ℝ → ℝ}
    (hf : IntegrableOn (fun q : ℝ × ℝ => f q.1 q.2 (formXThr q.1 q.2 (cornInWX q.1 X)))
      (coordT X)) :
    IntegrableOn (fun u => (∫ s in Ioc (coordSLo X u) (1 - u),
        coordJ1 X u s * f (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 s) +
        ∫ s in Ioo (1 - u) 1,
          coordJ2 X u s * f (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 s) (Ioo 0 X) ∧
      ∫ q in coordT X, f q.1 q.2 (formXThr q.1 q.2 (cornInWX q.1 X)) =
        ∫ u in Ioo 0 X, ((∫ s in Ioc (coordSLo X u) (1 - u),
          coordJ1 X u s * f (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 s) +
          ∫ s in Ioo (1 - u) 1,
            coordJ2 X u s * f (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 s) := by
  obtain ⟨hi, he⟩ := coord_integral_eq hX hf
  have hfib : EqOn (fun u => (∫ s in Ioc (coordSLo X u) (1 - u),
        coordJ1 X u s * f (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2
          (formXThr (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2
            (cornInWX (coordPsi1 X (u, s)).1 X))) +
        ∫ s in Ioo (1 - u) 1, coordJ2 X u s * f (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2
          (formXThr (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2
            (cornInWX (coordPsi2 X (u, s)).1 X)))
      (fun u => (∫ s in Ioc (coordSLo X u) (1 - u),
        coordJ1 X u s * f (coordPsi1 X (u, s)).1 (coordPsi1 X (u, s)).2 s) +
        ∫ s in Ioo (1 - u) 1,
          coordJ2 X u s * f (coordPsi2 X (u, s)).1 (coordPsi2 X (u, s)).2 s) (Ioo 0 X) := by
    intro u hu
    simp only
    congr 1
    · refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      simp only [coord_thr1 hX (p := (u, s)) ⟨hu, hs⟩]
    · refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
      simp only [coord_thr2 hX (p := (u, s)) ⟨hu, hs⟩]
  exact ⟨hi.congr_fun hfib measurableSet_Ioo, he.trans (setIntegral_congr_fun measurableSet_Ioo
    hfib)⟩

end

end QED.ChainProof.SetCK

end
