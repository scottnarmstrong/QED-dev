/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCB01Num
public import QED.ChainProof.SetCUnitMLines

/-!
# Set (c): pointwise bounds for the numerators of `CB0`, `CB1`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The numerators
of `QED/ChainProof/SetCLimCtCB01Num.lean` satisfy the refined pointwise bound
(`QED.Integration.TwoLoop.RefinedBound`) on the bubble shapes `vpShapeMatrix t`:

* `refinedBound_cbNum0`, `refinedBound_cbNum2`: for open-line matrices bounded by the open lines
  `1`, `0`, the numerator at loop mass `0` is bounded by `{0, 1, 2, 3}` in degree `4`, the
  coefficient of `M²` by `{0, 1}` in degree `2`;
* the numerator pairs `cbEa0`, `cbEa2` (once merged) and `cbEv0`, `cbEv2` (bare);
* `refinedBound_cbShape`: every such bound holds on the doubled shape `cbShapeMatrix d t`, whose
  lines `0, …, 9` are those of the bubble shape.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCPauli.CB01

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.ChainProof.SetCPauli (mergeY mergeC)
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound)

/-! ### Matrix bounds -/

theorem refinedBoundMat_add {m : ℕ} {al : Fin (m + 1) → Fin 2 → ℝ} {E : Finset (Fin (m + 1))}
    {k : ℕ} {A B : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (hA : RefinedBoundMat al E k A) (hB : RefinedBoundMat al E k B) :
    RefinedBoundMat al E k fun ℓ => A ℓ + B ℓ := fun i j => by
  simp only [Matrix.add_apply]
  exact (hA i j).add (hB i j)

theorem refinedBoundMat_smul {m : ℕ} {al : Fin (m + 1) → Fin 2 → ℝ} {E : Finset (Fin (m + 1))}
    {k : ℕ} {A : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (c : ℂ)
    (hA : RefinedBoundMat al E k A) : RefinedBoundMat al E k fun ℓ => c • A ℓ := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hA i j).const_mul c

theorem refinedBoundMat_mono {m : ℕ} {al : Fin (m + 1) → Fin 2 → ℝ}
    {E E' : Finset (Fin (m + 1))} {k k' : ℕ} {A : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (hA : RefinedBoundMat al E k A) (hE : E ⊆ E') (hk : k ≤ k') : RefinedBoundMat al E' k' A :=
  fun i j => (hA i j).mono hE hk

/-- The open-line numerators `A`, `Y` of line `i` are bounded by the line `i`. -/
theorem refinedBoundMat_cbLine (t : Fin 4) (P : Params) (p' p : Fin 4 → ℝ) (i : Fin 2) :
    RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) {Fin.castLE (by norm_num) i} 1
        (fun ℓ => electronNumerator P.m (cbMom p' p ℓ i)) ∧
      RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) {Fin.castLE (by norm_num) i} 1
        (fun ℓ => mergeY P.m P.δ₂ P.δm (cbMom p' p ℓ i)) := by
  obtain ⟨⟨r00, r01⟩, ⟨r10, r11⟩, -, -⟩ := vpRows t
  have hA : RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) {Fin.castLE (by norm_num) i} 1
      (fun ℓ => electronNumerator P.m (cbMom p' p ℓ i)) := by
    fin_cases i
    · refine refinedBoundMat_electronNumerator _ 0 P.m p fun ℓ => ?_
      rw [lineMomentum_const_eq, r00, r01]
      simp [cbMom, add_comm]
    · refine refinedBoundMat_electronNumerator _ 1 P.m p' fun ℓ => ?_
      rw [lineMomentum_const_eq, r10, r11]
      simp [cbMom, add_comm]
  refine ⟨hA, ?_⟩
  unfold mergeY
  exact refinedBoundMat_add (refinedBoundMat_smul _ hA)
    (refinedBoundMat_mono (refinedBoundMat_smul _ (RefinedBoundMat.const _)) (by simp)
      (by norm_num))

/-- **The pointwise bound of `cbNum` at loop mass `0`**: by the open lines `0, 1` and the bubble
lines `2, 3`. -/
theorem refinedBound_cbNum0 (t : Fin 4) (P : Params) {X1 X0 : (Fin 2 → Fin 4 → ℝ) →
    Matrix (Fin 4) (Fin 4) ℂ} (hX1 : RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) {1} 1 X1)
    (hX0 : RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) {0} 1 X0) (α β μ : Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4
      (fun ℓ => cbNum P 0 (X1 ℓ) (X0 ℓ) α β μ ℓ) := by
  unfold cbNum loopTrace
  refine RefinedBound.const_mul _ (RefinedBound.sum _ fun l0 _ => RefinedBound.sum _ fun l3 _ =>
    RefinedBound.sum _ fun l4 _ => RefinedBound.sum _ fun l5 _ => ?_)
  have hO := (((((RefinedBoundMat.const (Dirac.gamma l0)).mul hX1 (by decide)).mul
    (RefinedBoundMat.const (Dirac.gamma μ)) (by decide)).mul hX0 (by decide)).mul
      (RefinedBoundMat.const (Dirac.gamma l3)) (by decide)) α β
  exact (((hO.mul (RefinedBound.const _) (by decide)).mul (RefinedBound.const _) (by decide)).mul
    (refinedBoundMat_loop t l5 l4).trace (by decide)).mono (by decide) (by norm_num)

/-- The pointwise bound of `cbNum2`: by the open lines `0, 1`. -/
theorem refinedBound_cbNum2 (t : Fin 4) (P : Params) {X1 X0 : (Fin 2 → Fin 4 → ℝ) →
    Matrix (Fin 4) (Fin 4) ℂ} (hX1 : RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) {1} 1 X1)
    (hX0 : RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) {0} 1 X0) (α β μ : Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1} 2
      (fun ℓ => cbNum2 P (X1 ℓ) (X0 ℓ) α β μ) := by
  unfold cbNum2
  refine RefinedBound.const_mul _ (RefinedBound.sum _ fun l0 _ => RefinedBound.sum _ fun l3 _ =>
    RefinedBound.sum _ fun l4 _ => RefinedBound.sum _ fun l5 _ => ?_)
  have hO := (((((RefinedBoundMat.const (Dirac.gamma l0)).mul hX1 (by decide)).mul
    (RefinedBoundMat.const (Dirac.gamma μ)) (by decide)).mul hX0 (by decide)).mul
      (RefinedBoundMat.const (Dirac.gamma l3)) (by decide)) α β
  exact (((hO.mul (RefinedBound.const _) (by decide)).mul (RefinedBound.const _) (by decide)).mul
    (RefinedBound.const _) (by decide)).mono (by decide) (by norm_num)

/-! ### The numerator pairs -/

theorem refinedBoundMat_cbXa (t : Fin 4) (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (i : Fin 2) :
    RefinedBoundMat (castLoopMatrix (vpShapeMatrix t)) {Fin.castLE (by norm_num) i} 1
      (fun ℓ => cbXa P d p' p ℓ i) := by
  by_cases h : i = d
  · simp only [cbXa, h, ↓reduceIte]
    exact (refinedBoundMat_cbLine t P p' p d).2
  · simp only [cbXa, h, ↓reduceIte]
    exact (refinedBoundMat_cbLine t P p' p i).1

theorem refinedBound_cbEa0 (t : Fin 4) (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4 (cbEa0 P d p' p α β μ) :=
  refinedBound_cbNum0 t P (refinedBoundMat_cbXa t P d p' p 1) (refinedBoundMat_cbXa t P d p' p 0)
    α β μ

theorem refinedBound_cbEa2 (t : Fin 4) (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1} 2 (cbEa2 P d p' p α β μ) :=
  refinedBound_cbNum2 t P (refinedBoundMat_cbXa t P d p' p 1) (refinedBoundMat_cbXa t P d p' p 0)
    α β μ

theorem refinedBound_cbEv0 (t : Fin 4) (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4 (cbEv0 P p' p α β μ) :=
  refinedBound_cbNum0 t P (refinedBoundMat_cbLine t P p' p 1).1
    (refinedBoundMat_cbLine t P p' p 0).1 α β μ

theorem refinedBound_cbEv2 (t : Fin 4) (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1} 2 (cbEv2 P p' p α β μ) :=
  refinedBound_cbNum2 t P (refinedBoundMat_cbLine t P p' p 1).1
    (refinedBoundMat_cbLine t P p' p 0).1 α β μ

/-- **Bounds on a bubble shape hold on the doubled shape** (lines `0, …, 9` unchanged). -/
theorem refinedBound_cbShape (d : Fin 2) (t : Fin 4) {E : Finset (Fin 10)} {k : ℕ}
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : RefinedBound (castLoopMatrix (vpShapeMatrix t)) E k F) :
    RefinedBound (castLoopMatrix (cbShapeMatrix d t)) (E.map Fin.castSuccEmb) k F :=
  QED.ChainProof.SetCUnitM.refinedBound_map Fin.castSuccEmb (fun e _ => by
    funext s
    simp [castLoopMatrix, cbShapeMatrix_castSucc]) h

end QED.ChainProof.SetCPauli.CB01

end
