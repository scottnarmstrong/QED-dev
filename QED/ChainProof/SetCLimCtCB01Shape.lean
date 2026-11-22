/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassLimitVP

/-!
# Set (c), classes `CB0`, `CB1`: the bubble shapes with a doubled open line

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The classes
`CB0`, `CB1` are the vacuum-polarization vertex `VP` with a `fermionCt` vertex on one of its two
open-line lines, which therefore appears twice, `S̃ X S̃`. After the merge identity
`A X A = D Y₁ + c A + iε Y₁` the integrand is a sum of products on the bubble shapes of `VP`
(`QED.TwoLoop.Bridge.vpShapeMatrix`, ten lines) and on the same shapes with the open line `d`
repeated (eleven lines, `cbShapeMatrix d t`). This file gives the engine hypotheses of
`QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined` for these shapes:

* **`symanzikV_cbShape_ge_min`**: `V ≥ (3/4) min(m², min(m_γ, Λ)²)` off `U = 0`, by
  `QED.Integration.TwoLoop.le_symanzikV_comp_of` from the class bound `symanzikV_classVP_ge` (the
  repeated line is a further copy of a line of the class, as are the regulator photons);
* `noSubdivergenceRefined_cbShape`, `noSubdivergenceRefined_cbShape_three`: the criterion for the
  numerator line sets of `VP` (decided);
* `noSubdivergenceRefined_vpShape_erase`: the criterion on the ten-line shapes for the numerator
  line sets with the open line `d` removed (the piece `Y₁` of degree one less).
-/

@[expose] public section

open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrix classVPMomenta classVPMasses
  loopMatrixVP NoSubdivergenceRefined symanzikU symanzikV)

namespace QED.ChainProof.SetCPauli.CB01

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge

/-! ### The doubled shapes -/

/-- The line maps of the doubled shapes: those of `vpShapeLines t` and the open line `d` (`0`:
incoming, `1`: outgoing) once more, as line `10`. -/
def cbShapeLines (d : Fin 2) (t : Fin 4) : Fin 11 → Fin 6 :=
  Fin.snoc (α := fun _ => Fin 6) (vpShapeLines t) (Fin.castLE (by norm_num) d)

/-- The loop matrix of the doubled shape `(d, t)`. -/
def cbShapeMatrix (d : Fin 2) (t : Fin 4) : Fin 11 → Fin 2 → ℤ :=
  fun i => class5LoopMatrix .VP (cbShapeLines d t i)

/-- The masses of the doubled shape: those of `vpShapeMasses P t` and `m` on line `10`. -/
def cbShapeMasses (P : Params) (t : Fin 4) : Fin 11 → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (vpShapeMasses P t) P.m

/-- The external momenta of the lines of the doubled shape. -/
def cbShapeMomenta (d : Fin 2) (t : Fin 4) (p p' : Fin 4 → ℝ) : Fin 11 → Fin 4 → ℝ :=
  fun i => classVPMomenta p p' (cbShapeLines d t i)

theorem cbShapeLines_castSucc (d : Fin 2) (t : Fin 4) (i : Fin 10) :
    cbShapeLines d t i.castSucc = vpShapeLines t i := by
  simp [cbShapeLines]

theorem cbShapeLines_last (d : Fin 2) (t : Fin 4) :
    cbShapeLines d t (Fin.last 10) = Fin.castLE (by norm_num) d :=
  Fin.snoc_last (α := fun _ => Fin 6) _ _

/-- The first ten rows of a doubled shape are the rows of the bubble shape. -/
theorem cbShapeMatrix_castSucc (d : Fin 2) (t : Fin 4) (i : Fin 10) :
    cbShapeMatrix d t i.castSucc = vpShapeMatrix t i := by
  simp only [cbShapeMatrix, cbShapeLines_castSucc, vpShapeMatrix]

/-- The repeated line `10` has the row of the open line `d`. -/
theorem cbShapeMatrix_last (d : Fin 2) (t : Fin 4) :
    cbShapeMatrix d t (Fin.last 10) = vpShapeMatrix t (Fin.castLE (by norm_num) d) := by
  fin_cases d <;> fin_cases t <;> rfl

theorem cbShapeMomenta_castSucc (d : Fin 2) (t : Fin 4) (p p' : Fin 4 → ℝ) (i : Fin 10) :
    cbShapeMomenta d t p p' i.castSucc = vpShapeMomenta t p p' i := by
  simp only [cbShapeMomenta, cbShapeLines_castSucc, vpShapeMomenta]

theorem cbShapeMasses_last (P : Params) (t : Fin 4) : cbShapeMasses P t (Fin.last 10) = P.m :=
  Fin.snoc_last (α := fun _ => ℝ) _ _

theorem cbShapeMasses_castSucc (P : Params) (t : Fin 4) (i : Fin 10) :
    cbShapeMasses P t i.castSucc = vpShapeMasses P t i := by
  simp [cbShapeMasses]

/-! ### Positivity of `V` -/

/-- The mass condition of `le_symanzikV_comp_of` for the doubled shapes. -/
theorem classVPMasses_cbShapeLines_le_of (P : Params) {μ : ℝ} (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2)
    (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (hγ : μ ^ 2 ≤ P.mγ ^ 2) (hΛ : μ ^ 2 ≤ P.Λ ^ 2) (d : Fin 2)
    (t : Fin 4) (i : Fin 11) :
    classVPMasses P.m P.m μ μ (cbShapeLines d t i) ^ 2 ≤ cbShapeMasses P t i ^ 2 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [cbShapeLines_last, cbShapeMasses_last]
    fin_cases d <;> simp [classVPMasses]
  · rw [cbShapeLines_castSucc, cbShapeMasses_castSucc]
    exact QED.TwoLoop.ClassLimit.classVPMasses_vpShapeLines_le_of P h₁ h₂ hγ hΛ t j

/-- **Positivity of `V` for the doubled shapes**, with `μ = min(m_γ, Λ)`. -/
theorem symanzikV_cbShape_ge_min (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (d : Fin 2) (t : Fin 4)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {z : Fin 11 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (cbShapeMatrix d t)) z ≠ 0) :
    3 / 4 * min (P.m ^ 2) (min P.mγ P.Λ ^ 2) ≤
      symanzikV (castLoopMatrix (cbShapeMatrix d t)) (cbShapeMomenta d t p p')
        (cbShapeMasses P t) z := by
  have hμ0 : 0 < min P.mγ P.Λ := lt_min hmγ hΛ
  exact QED.Integration.TwoLoop.le_symanzikV_comp_of (σ := cbShapeLines d t)
    (α := loopMatrixVP)
    (fun _ hw hw1 hU' =>
      QED.Integration.TwoLoop.symanzikV_classVP_ge le_rfl hp hp' hq le_rfl le_rfl hw hw1 hU')
    (classVPMasses_cbShapeLines_le_of P h₁ h₂ (pow_le_pow_left₀ hμ0.le (min_le_left _ _) 2)
      (pow_le_pow_left₀ hμ0.le (min_le_right _ _) 2) d t) hz hz1 hU

/-! ### The criterion -/

/-- **The criterion on the doubled shapes** for the numerator lines `{0, 1, 2, 3}`. -/
theorem noSubdivergenceRefined_cbShape (d : Fin 2) (t : Fin 4) :
    NoSubdivergenceRefined 2 {0, 1, 2, 3} (castLoopMatrix (cbShapeMatrix d t)) :=
  (QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by
    revert d t; decide)

/-- The criterion on the doubled shapes of term `3` for the line sets of its two pieces. -/
theorem noSubdivergenceRefined_cbShape_three (d : Fin 2) :
    NoSubdivergenceRefined 2 {0, 1, 2, 8} (castLoopMatrix (cbShapeMatrix d 3)) ∧
      NoSubdivergenceRefined 2 {0, 1, 3, 9} (castLoopMatrix (cbShapeMatrix d 3)) :=
  ⟨(QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by
      revert d; decide),
    (QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by
      revert d; decide)⟩

/-- The criterion on the bubble shapes for the numerator lines without the open line `d`. -/
theorem noSubdivergenceRefined_vpShape_erase (d : Fin 2) (t : Fin 4) :
    NoSubdivergenceRefined 2 (({0, 1, 2, 3} : Finset (Fin 10)).erase (Fin.castLE (by norm_num) d))
      (castLoopMatrix (vpShapeMatrix t)) :=
  (QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by
    revert d t; decide)

/-- The criterion on the bubble shape of term `3` for the line sets of its two pieces without the
open line `d`. -/
theorem noSubdivergenceRefined_vpShape_three_erase (d : Fin 2) :
    NoSubdivergenceRefined 2 (({0, 1, 2, 8} : Finset (Fin 10)).erase (Fin.castLE (by norm_num) d))
      (castLoopMatrix (vpShapeMatrix 3)) ∧
    NoSubdivergenceRefined 2 (({0, 1, 3, 9} : Finset (Fin 10)).erase (Fin.castLE (by norm_num) d))
      (castLoopMatrix (vpShapeMatrix 3)) :=
  ⟨(QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by
      revert d; decide),
    (QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (by
      revert d; decide)⟩

end QED.ChainProof.SetCPauli.CB01

end
