/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliSum

/-!
# Set (c): the classes `CB0`, `CB1`, `CD0 t`, `CD1 t` split into a `δ₂` part and a mass part

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, the value
identity of `CBₖ + CDₖ,₀ + CDₖ,₁`, `k = 0, 1`. The inserted electron line carries
`Y = δ₂ A + (δ₂ - δ_m) m` and `c = 2m (δ_m - δ₂) m` (`mergeY`, `mergeC`). Both are additive in
`(δ₂, δ_m)`, so the Phase 4 values split as

* `cb01Zero P = δ₂ · vpZero P + cb01Zero (cbBParams P)`, `cbBParams P` the parameters with
  `δ₂ = 0` and `δ_m` replaced by `δ_m - δ₂` (so `Y = (δ₂ - δ_m) m`, `c` unchanged): the bare
  pieces of `CB0`, `CB1` on the ten-line shapes are literally those of `VP` (`cbFB_eq_vpF`), with
  the **same sign** (`vpZero_eq_cbFB`);
* `cdOutZero Q = -δ₂ · d3Zero Q + cdOutZero (cbBParams Q)`, and the same for `cdInZero`.

Linearity of the Phase 4 values in the numerator is not automatic (`secondCoeff` is a limit);
it follows from the explicit second-order limit (`tendsto_piece_explicit`) and the uniqueness of
limits (`projZero_add`, `pauliCurveZero_add`, `kindsZero_add`).

## Main statements

* `projZero`, **`projZero_add`**, `pauliCurveZero_add`, `kindsZero_add`: linearity;
* `cbBParams`, `cbFA_split`, `pauliCurveZero_cbFA`;
* **`vpZero_eq_cbFB`**: `∑ⱼ Z(vpCurve j, F_B j) = vpZero`;
* **`cb01Zero_split`**, **`cdOutZero_split`**, **`cdInZero_split`**.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet)
open QED.Integration.TwoLoop (LoopQuartic RefinedBound)

/-- The explicit `q → 0` value of a projected piece along a curve. -/
noncomputable def projZero (C : CurveData) {J : Type*} [Fintype J]
    (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ) (ω : ℝ → J → ℂ) : ℂ :=
  ∫ x in simplexSet C.m, secondCoeff (projNum C F ω x) / ((C.vfun x 0 : ℝ) : ℂ) ^ (C.m - 3)

/-- **The explicit `q → 0` value is linear in the numerator.** -/
theorem projZero_add (C : CurveData) {J : Type*} [Fintype J] {D n r Dω : ℕ} (a : ℂ)
    (F G : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (hGpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * G u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j)
    (hGq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = G u j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
    (hGB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (G u j))
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) :
    projZero C (fun u j ℓ => a * F u j ℓ + G u j ℓ) ω = a * projZero C F ω + projZero C G ω := by
  set v : (ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ) → ℝ → J → ℂ := fun H u j =>
    -((π : ℂ) ^ 4) * ∫ x in simplexSet C.m,
      QED.TwoLoop.ClassLimit.paramIntegrand (numQuartic (H u j)) C.α (C.mom u) C.M 0 x with hv_def
  have hv : ∀ H : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ,
      (∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = H u j) →
      (∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (H u j)) →
      ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j, IsParamValue (C.toParamData hu) (H u j) (v H u j) :=
    fun H hq hB u hu j => ⟨numQuartic (H u j), eval_numQuartic (hq u hu j), hB u hu j, rfl⟩
  have hFv := hv F hFq hFB
  have hGv := hv G hGq hGB
  have hSv : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j, IsParamValue (C.toParamData hu)
      (fun ℓ => a * F u j ℓ + G u j ℓ) (a * v F u j + v G u j) := fun u hu j => by
    have h := IsParamValue.sum (D := C.toParamData hu) (Finset.univ : Finset (Fin 2)) ![a, 1]
      (F := ![F u j, G u j]) (v := ![v F u j, v G u j])
      (fun k _ => by fin_cases k <;> simp [hFv u hu j, hGv u hu j])
    simpa [Fin.sum_univ_two] using h
  have hSpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * (a * F u j ℓ + G u j ℓ) := fun j =>
    (((hFpoly j).const_mul fun _ => a).add (hGpoly j)).congr fun ℓ u _ => by ring
  have hL1 := tendsto_piece_explicit C F hFpoly hFq hFB (v F) hFv ω hω hω0
  have hL2 := tendsto_piece_explicit C G hGpoly hGq hGB (v G) hGv ω hω hω0
  have hL3 := tendsto_piece_explicit C (fun u j ℓ => a * F u j ℓ + G u j ℓ) hSpoly
    (fun u hu j => by
      obtain ⟨Q, hQ, -, -⟩ := hSv u hu j
      exact ⟨Q, hQ⟩)
    (fun u hu j => by
      obtain ⟨Q, -, hB, -⟩ := hSv u hu j
      exact hB)
    (fun u j => a * v F u j + v G u j) hSv ω hω hω0
  have hL4 := (hL1.const_mul a).add hL2
  have e : ∀ u, ∑ j, ω u j * (a * v F u j + v G u j) =
      a * ∑ j, ω u j * v F u j + ∑ j, ω u j * v G u j := fun u => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine tendsto_nhds_unique hL3 (hL4.congr fun u => ?_)
  rw [e u, e (-u)]
  ring

/-! ### The split of `CB0`, `CB1` -/

open QED.ChainProof.SetCPauli QED.ChainProof.SetCPauli.CB01 QED.TwoLoop.Bridge
open QED.TwoLoop.PauliZero

/-- The parameters of the mass-derivative part: `δ₂ = 0` and `δ_m` replaced by `δ_m - δ₂`, so
that `Y = (δ₂ - δ_m) m` and `c` is unchanged. -/
def cbBParams (P : Params) : Params := { P with δ₂ := 0, δm := P.δm - P.δ₂ }

theorem mergeY_split (m δ₂ δm : ℝ) (k : Fin 4 → ℝ) :
    mergeY m δ₂ δm k = (δ₂ : ℂ) • electronNumerator m k + mergeY m 0 (δm - δ₂) k := by
  ext i j
  simp only [mergeY, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem mergeC_cbBParams (P : Params) :
    mergeC P.m (cbBParams P).δ₂ (cbBParams P).δm = mergeC P.m P.δ₂ P.δm := by
  simp only [mergeC, cbBParams]
  push_cast
  ring

theorem cbNum_left (P : Params) (M : ℝ) (c : ℂ) (X X' X0 : Matrix (Fin 4) (Fin 4) ℂ)
    (α β μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbNum P M (c • X + X') X0 α β μ ℓ = c * cbNum P M X X0 α β μ ℓ + cbNum P M X' X0 α β μ ℓ := by
  simp only [cbNum, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem cbNum_right (P : Params) (M : ℝ) (c : ℂ) (X1 X X' : Matrix (Fin 4) (Fin 4) ℂ)
    (α β μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbNum P M X1 (c • X + X') α β μ ℓ = c * cbNum P M X1 X α β μ ℓ + cbNum P M X1 X' α β μ ℓ := by
  simp only [cbNum, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem cbNum2_left (P : Params) (c : ℂ) (X X' X0 : Matrix (Fin 4) (Fin 4) ℂ) (α β μ : Fin 4) :
    cbNum2 P (c • X + X') X0 α β μ = c * cbNum2 P X X0 α β μ + cbNum2 P X' X0 α β μ := by
  simp only [cbNum2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem cbNum2_right (P : Params) (c : ℂ) (X1 X X' : Matrix (Fin 4) (Fin 4) ℂ) (α β μ : Fin 4) :
    cbNum2 P X1 (c • X + X') α β μ = c * cbNum2 P X1 X α β μ + cbNum2 P X1 X' α β μ := by
  simp only [cbNum2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem cbEa0_split (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbEa0 P d p' p α β μ ℓ =
      (P.δ₂ : ℂ) * cbEv0 P p' p α β μ ℓ + cbEa0 (cbBParams P) d p' p α β μ ℓ := by
  fin_cases d
  · simp only [cbEa0, cbEv0, cbXa, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    rw [mergeY_split, cbNum_right]
    rfl
  · simp only [cbEa0, cbEv0, cbXa, Fin.mk_one, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    rw [mergeY_split, cbNum_left]
    rfl

theorem cbEa2_split (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbEa2 P d p' p α β μ ℓ =
      (P.δ₂ : ℂ) * cbEv2 P p' p α β μ ℓ + cbEa2 (cbBParams P) d p' p α β μ ℓ := by
  fin_cases d
  · simp only [cbEa2, cbEv2, cbXa, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    rw [mergeY_split, cbNum2_right]
    rfl
  · simp only [cbEa2, cbEv2, cbXa, Fin.mk_one, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    rw [mergeY_split, cbNum2_left]
    rfl

theorem cbPiece_lin (P : Params) (p p' : Fin 4 → ℝ) (c : ℂ)
    (E0 E2 E0' E2' : (Fin 2 → Fin 4 → ℝ) → ℂ) (j : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbPiece P p p' (fun ℓ => c * E0 ℓ + E0' ℓ) (fun ℓ => c * E2 ℓ + E2' ℓ) j ℓ =
      c * cbPiece P p p' E0 E2 j ℓ + cbPiece P p p' E0' E2' j ℓ := by
  unfold cbPiece
  split_ifs <;> ring

/-- **The once-merged pieces split** into `δ₂` times the bare pieces and the pieces of the
mass-derivative part. -/
theorem cbFA_split (P : Params) (d : Fin 2) (j : Fin 5) (u : ℝ) (x : Idx)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbFA P d j u x ℓ = (P.δ₂ : ℂ) * cbFB P j u x ℓ + cbFA (cbBParams P) d j u x ℓ := by
  have e0 : cbEa0 P d (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1 = fun ℓ =>
      (P.δ₂ : ℂ) * cbEv0 P (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1 ℓ +
        cbEa0 (cbBParams P) d (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1 ℓ :=
    funext fun ℓ => cbEa0_split P d _ _ _ _ _ ℓ
  have e2 : cbEa2 P d (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1 = fun ℓ =>
      (P.δ₂ : ℂ) * cbEv2 P (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1 ℓ +
        cbEa2 (cbBParams P) d (curveMomentum P.m u) (restMomentum P.m) x.2.1 x.2.2 x.1 ℓ :=
    funext fun ℓ => cbEa2_split P d _ _ _ _ _ ℓ
  simp only [cbFA, cbFB]
  rw [e0, e2, cbPiece_lin]
  rfl

theorem pauliCurveZero_eq (C : CurveData) (m : ℝ) (F : ℝ → Idx → (Fin 2 → Fin 4 → ℝ) → ℂ) :
    pauliCurveZero C m F =
      projZero C F fun u j => pauliWt m (curveMomentum m u) (restMomentum m) j.1 j.2.1 j.2.2 :=
  rfl

/-- **`pauliCurveZero` is linear** in the numerator. -/
theorem pauliCurveZero_add (C : CurveData) (m : ℝ) (a : ℂ)
    (F G : ℝ → Idx → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly 8 fun ℓ u => wt u ^ 4 * F u j ℓ)
    (hGpoly : ∀ j, IsUPoly 8 fun ℓ u => wt u ^ 4 * G u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j)
    (hGq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = G u j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
    (hGB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (G u j)) :
    pauliCurveZero C m (fun u j ℓ => a * F u j ℓ + G u j ℓ) =
      a * pauliCurveZero C m F + pauliCurveZero C m G := by
  simp only [pauliCurveZero_eq]
  exact projZero_add C (r := 4) (Dω := 8) a F G hFpoly hGpoly hFq hGq hFB hGB _
    (fun j => isUPoly_pauliWt m j) (sum_pauliWt_zero m)

/-- **The once-merged pieces of `CB0`, `CB1` split** on the `VP` shapes. -/
theorem pauliCurveZero_cbFA (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (m : ℝ) (d : Fin 2) (j : Fin 5) :
    pauliCurveZero (vpCurve P hm hmγ hΛ hM₁ hM₂ j) m (cbFA P d j) =
      (P.δ₂ : ℂ) * pauliCurveZero (vpCurve P hm hmγ hΛ hM₁ hM₂ j) m (cbFB P j) +
        pauliCurveZero (vpCurve P hm hmγ hΛ hM₁ hM₂ j) m (cbFA (cbBParams P) d j) := by
  have e : cbFA P d j = fun u x ℓ => (P.δ₂ : ℂ) * cbFB P j u x ℓ +
      cbFA (cbBParams P) d j u x ℓ := funext fun u => funext fun x => funext fun ℓ =>
    cbFA_split P d j u x ℓ
  rw [e]
  exact pauliCurveZero_add _ m _ _ _ (fun x => isUPoly_cbFB P j x)
    (fun x => isUPoly_cbFA (cbBParams P) d j x)
    (fun u _ x => (isLoopPoly_cbPiece P _ _ (isLoopPoly_cbEv P _ _ _ _ _).1
      (isLoopPoly_cbEv P _ _ _ _ _).2 j).exists_loopQuartic)
    (fun u _ x => (isLoopPoly_cbPiece (cbBParams P) _ _
      (isLoopPoly_cbEa (cbBParams P) d _ _ _ _ _).1
      (isLoopPoly_cbEa (cbBParams P) d _ _ _ _ _).2 j).exists_loopQuartic)
    (fun u _ x => refinedBound_cbPiece P _ _ (fun t => refinedBound_cbEv0 t P _ _ _ _ _)
      (fun t => refinedBound_cbEv2 t P _ _ _ _ _) j)
    (fun u _ x => refinedBound_cbPiece (cbBParams P) _ _
      (fun t => refinedBound_cbEa0 t (cbBParams P) d _ _ _ _ _)
      (fun t => refinedBound_cbEa2 t (cbBParams P) d _ _ _ _ _) j)

/-! ### The bare pieces are those of `VP` -/

theorem cbEv0_eq_vpE0 (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbEv0 P p' p α β μ ℓ = QED.TwoLoop.Bridge.vpE0 P (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ) ℓ := by
  have h1 := congrArg (fun A => A α β) (cbNumM_eq P 0 (electronNumerator P.m (cbMom p' p ℓ 1))
    (electronNumerator P.m (cbMom p' p ℓ 0)) μ ℓ)
  have h2 := congrArg (fun A => A α β) (vpE0M_eq P p p' μ ℓ)
  simp only [cbNumM, vpE0M, Matrix.of_apply] at h1 h2
  have m1 : p + (p' - p) - -ℓ 1 = cbMom p' p ℓ 1 := by
    simp only [cbMom, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    abel
  have m0 : p - -ℓ 1 = cbMom p' p ℓ 0 := by
    simp only [cbMom, Matrix.cons_val_zero]
    abel
  rw [cbEv0, h1, h2, vpChainM, m1, m0]

theorem cbEv2_eq_vpE2 (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbEv2 P p' p α β μ ℓ = QED.TwoLoop.Bridge.vpE2 P (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ) ℓ := by
  have h1 := congrArg (fun A => A α β) (cbNum2M_eq P (electronNumerator P.m (cbMom p' p ℓ 1))
    (electronNumerator P.m (cbMom p' p ℓ 0)) μ)
  have h2 := congrArg (fun A => A α β) (vpE2M_eq P p p' μ ℓ)
  simp only [cbNum2M, vpE2M, Matrix.of_apply] at h1 h2
  have m1 : p + (p' - p) - -ℓ 1 = cbMom p' p ℓ 1 := by
    simp only [cbMom, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    abel
  have m0 : p - -ℓ 1 = cbMom p' p ℓ 0 := by
    simp only [cbMom, Matrix.cons_val_zero]
    abel
  rw [cbEv2, h1, h2, vpChainM, m1, m0]

theorem cbFB_eq_vpF (P : Params) (j : Fin 5) (u : ℝ) (x : Idx) :
    cbFB P j u x = vpF P (curveMomentum P.m u) j x := by
  funext ℓ
  simp only [cbFB, vpF, vpPieceM, Matrix.of_apply, QED.TwoLoop.ClassLimit.vpPieceNumer, cbPiece,
    cbEv0_eq_vpE0, cbEv2_eq_vpE2]

/-- **`VP` from the bare pieces of `CB0`, `CB1`.** -/
theorem vpZero_eq_cbFB (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) :
    ∑ j, pauliCurveZero (vpCurve P hm hmγ hΛ hM₁ hM₂ j) P.m (cbFB P j) = vpZero P := by
  have e : ∀ j, cbFB P j = fun u x => vpF P (curveMomentum P.m u) j x := fun j =>
    funext fun u => funext fun x => cbFB_eq_vpF P j u x
  simp only [e, vpZero, pauliCurveZero, vpV, CurveData.vfun, vpCurve,
    curveMomentum_zero]
  rfl

/-- **The split of `CB0`, `CB1`**: `δ₂ · VP` plus the mass-derivative part `cb01Zero` at
`cbBParams`. -/
theorem cb01Zero_split (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (d : Fin 2) :
    cb01Zero P hm hmγ hΛ hM₁ hM₂ P.m d =
      (P.δ₂ : ℂ) * vpZero P + cb01Zero (cbBParams P) hm hmγ hΛ hM₁ hM₂ P.m d := by
  have hc : mergeC P.m P.δ₂ P.δm = mergeC (cbBParams P).m (cbBParams P).δ₂ (cbBParams P).δm :=
    (mergeC_cbBParams P).symm
  unfold cb01Zero
  rw [Finset.sum_congr rfl fun j _ => pauliCurveZero_cbFA P hm hmγ hΛ hM₁ hM₂ P.m d j,
    Finset.sum_add_distrib, ← Finset.mul_sum, vpZero_eq_cbFB, hc, add_assoc]
  rfl

/-! ### The split of `CD0 t`, `CD1 t` -/

open QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit

theorem kindsZero_eq {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (P : Params) (hm : 0 < P.m) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = P.m ^ 2) (hMp : ∀ i, κ i = .pho → μ₀ ^ 2 ≤ Ms i ^ 2)
    (hcrit : QED.Integration.TwoLoop.IntNoSubdivergenceRefined 2 {0, 1, 2, 3}
      fun i => (κ i).dir)
    (num : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) :
    kindsZero κ Ms P num = projZero (kindsCurve hm7 κ Ms P hm hμ₀ hMe hMp hcrit)
      (fun u (j : Idx) ℓ => num (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2)
      (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2) /
        auxLimit P.m := by
  simp only [projZero, kindsZero, kindsV, CurveData.vfun, kindsCurve, curveMomentum_zero]
  rfl

/-- **`kindsZero` is linear** in the numerator, for numerators of the product form. -/
theorem kindsZero_add {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) (P : Params) (hm : 0 < P.m) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = P.m ^ 2) (hMp : ∀ i, κ i = .pho → μ₀ ^ 2 ≤ Ms i ^ 2)
    (hcrit : QED.Integration.TwoLoop.IntNoSubdivergenceRefined 2 {0, 1, 2, 3}
      fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux) (a : ℂ)
    (d₁ d₂ : (Fin 4 → ℝ) → ℝ → (Fin 4 → ℝ) → ℂ)
    (N₁ N₂ : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN₁ : ∀ p' μ i j, IsLoopPoly 2 4 fun ℓ => N₁ p' μ (ℓ 0) i j)
    (hN₂ : ∀ p' μ i j, IsLoopPoly 2 4 fun ℓ => N₂ p' μ (ℓ 0) i j)
    (hN₁p : ∀ μ i j k, IsLoopPoly 1 4 fun y => N₁ (y 0) μ k i j)
    (hN₂p : ∀ μ i j k, IsLoopPoly 1 4 fun y => N₂ (y 0) μ k i j)
    (hfac₁ : ∀ p' (ε : ℝ), 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      ∏ i, (propDenom (Ms i) ε ((κ i).lineMom (restMomentum P.m) p' ℓ))⁻¹ =
        d₁ p' ε (ℓ 0) * ((propDenom P.m ε (ℓ 1))⁻¹) ^ 3)
    (hfac₂ : ∀ p' (ε : ℝ), 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      ∏ i, (propDenom (Ms i) ε ((κ i).lineMom (restMomentum P.m) p' ℓ))⁻¹ =
        d₂ p' ε (ℓ 0) * ((propDenom P.m ε (ℓ 1))⁻¹) ^ 3) :
    kindsZero κ Ms P (fun p' μ k => a • N₁ p' μ k + N₂ p' μ k) =
      a * kindsZero κ Ms P N₁ + kindsZero κ Ms P N₂ := by
  have hv : ∀ (d : (Fin 4 → ℝ) → ℝ → (Fin 4 → ℝ) → ℂ)
      (N : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ),
      (∀ p' μ i j, IsLoopPoly 2 4 fun ℓ => N p' μ (ℓ 0) i j) →
      (∀ p' (ε : ℝ), 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
        ∏ i, (propDenom (Ms i) ε ((κ i).lineMom (restMomentum P.m) p' ℓ))⁻¹ =
          d p' ε (ℓ 0) * ((propDenom P.m ε (ℓ 1))⁻¹) ^ 3) →
      ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) (j : Idx), ∃ v, IsParamValue
        ((kindsCurve hm7 κ Ms P hm hμ₀ hMe hMp hcrit).toParamData hu)
        (fun ℓ => N (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2) v :=
    fun d N hN hfac u hu j => by
      obtain ⟨v, hv, -, -⟩ := pieceLim_entry hm7 κ Ms hm hμ₀ hMe hMp hcrit hcard hE
        (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
        ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu) (d (curveMomentum P.m u))
        (N (curveMomentum P.m u)) (hN _) (hfac _) j.1 j.2.1 j.2.2
      exact ⟨v, hv⟩
  have hpoly : ∀ N : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ μ i j k, IsLoopPoly 1 4 fun y => N (y 0) μ k i j) → ∀ j : Idx,
      IsUPoly 8 fun (ℓ : Fin 2 → Fin 4 → ℝ) u =>
        wt u ^ 4 * N (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2 :=
    fun N hN j => isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
      (G := fun ℓ y => N (y 0) j.1 (ℓ 0) j.2.1 j.2.2)
      (fun ℓ => hN j.1 j.2.1 j.2.2 (ℓ 0))
      (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
  have h1 := hv d₁ N₁ hN₁ hfac₁
  have h2 := hv d₂ N₂ hN₂ hfac₂
  rw [kindsZero_eq hm7 κ Ms P hm hμ₀ hMe hMp hcrit, kindsZero_eq hm7 κ Ms P hm hμ₀ hMe hMp hcrit,
    kindsZero_eq hm7 κ Ms P hm hμ₀ hMe hMp hcrit]
  have e : (fun u (j : Idx) (ℓ : Fin 2 → Fin 4 → ℝ) => (a • N₁ (curveMomentum P.m u) j.1 (ℓ 0) +
      N₂ (curveMomentum P.m u) j.1 (ℓ 0)) j.2.1 j.2.2) = fun u j ℓ =>
      a * N₁ (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2 +
        N₂ (curveMomentum P.m u) j.1 (ℓ 0) j.2.1 j.2.2 := by
    funext u j ℓ
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [e, projZero_add _ (r := 4) (Dω := 8) a _ _ (hpoly N₁ hN₁p) (hpoly N₂ hN₂p)
    (fun u hu j => by
      obtain ⟨v, Q, hQ, -, -⟩ := h1 u hu j
      exact ⟨Q, hQ⟩)
    (fun u hu j => by
      obtain ⟨v, Q, hQ, -, -⟩ := h2 u hu j
      exact ⟨Q, hQ⟩)
    (fun u hu j => by
      obtain ⟨v, Q, -, hB, -⟩ := h1 u hu j
      exact hB)
    (fun u hu j => by
      obtain ⟨v, Q, -, hB, -⟩ := h2 u hu j
      exact hB)
    _ (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m)]
  ring

theorem vertexChain_smul_add_out (e : ℝ) (μ : Fin 4) (c : ℂ) (A A' B : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ (c • A + A') B D = c • vertexChain e μ A B D + vertexChain e μ A' B D := by
  simp only [vertexChain, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [smul_comm c, smul_comm c]

theorem vertexChain_smul_add_in (e : ℝ) (μ : Fin 4) (c : ℂ) (A B B' : Matrix (Fin 4) (Fin 4) ℂ)
    (D : Fin 4 → Fin 4 → ℂ) :
    vertexChain e μ A (c • B + B') D = c • vertexChain e μ A B D + vertexChain e μ A B' D := by
  simp only [vertexChain, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [smul_comm c, smul_comm c]

theorem neg_mergeY_split (m δ₂ δm : ℝ) (k : Fin 4 → ℝ) :
    -mergeY m δ₂ δm k = (-(δ₂ : ℂ)) • electronNumerator m k + -mergeY m 0 (δm - δ₂) k := by
  rw [mergeY_split, neg_add, neg_smul]

theorem numOut₁_split (Q : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    numOut₁ Q p' p μ k = (-(Q.δ₂ : ℂ)) • numD3 Q p' p μ k + numOut₁ (cbBParams Q) p' p μ k := by
  simp only [numOut₁, numD3]
  rw [neg_mergeY_split, vertexChain_smul_add_out]
  rfl

theorem numIn₁_split (Q : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (k : Fin 4 → ℝ) :
    numIn₁ Q p' p μ k = (-(Q.δ₂ : ℂ)) • numD3 Q p' p μ k + numIn₁ (cbBParams Q) p' p μ k := by
  simp only [numIn₁, numD3]
  rw [neg_mergeY_split, vertexChain_smul_add_in]
  rfl

theorem numOut₂_cbBParams (Q : Params) :
    numOut₂ (cbBParams Q) = numOut₂ Q := by
  funext p' p μ k
  have h := mergeC_cbBParams Q
  simp only [numOut₂]
  rw [show (cbBParams Q).m = Q.m from rfl, h]
  rfl

theorem numIn₂_cbBParams (Q : Params) :
    numIn₂ (cbBParams Q) = numIn₂ Q := by
  funext p' p μ k
  have h := mergeC_cbBParams Q
  simp only [numIn₂]
  rw [show (cbBParams Q).m = Q.m from rfl, h]
  rfl

open QED.TwoLoop.ReflCovariance in
/-- **The split of `CD0 t`**: `-δ₂` times the `δ₃` class plus the mass-derivative part. -/
theorem cdOutZero_split (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) :
    cdOutZero Q = -(Q.δ₂ : ℂ) * d3Zero Q + cdOutZero (cbBParams Q) := by
  have e : (fun p' => numOut₁ Q p' (restMomentum Q.m)) = fun p' μ k =>
      (-(Q.δ₂ : ℂ)) • numD3 Q p' (restMomentum Q.m) μ k +
        numOut₁ (cbBParams Q) p' (restMomentum Q.m) μ k :=
    funext fun p' => funext fun μ => funext fun k => numOut₁_split Q _ _ μ k
  unfold cdOutZero d3Zero
  rw [e, kindsZero_add (by norm_num) kindsD3 (massesD3 Q) Q hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ) intNoSubdivergenceRefined_kindsD3
    (by decide) (by decide) _ (fun p' => den₁ Q p' (restMomentum Q.m))
    (fun p' => den₁ (cbBParams Q) p' (restMomentum Q.m)) _ _
    (fun p' μ i j => (affMat_vertexChain Q.e μ (AffMat.electronNumerator Q.m p')
      (AffMat.electronNumerator Q.m (restMomentum Q.m)) Q.δ₃ Q.mγ Q.Λ i j).isLoopPoly)
    (fun p' μ i j => (affMat_numOut₁ (cbBParams Q) p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numD3_out Q _ μ i j k)
    (fun μ i j k => isLoopPoly_numOut₁_out (cbBParams Q) _ μ i j k)
    (fun p' ε _ ℓ => den₁_fac Q _ p' ε ℓ) (fun p' ε _ ℓ => den₁_fac (cbBParams Q) _ p' ε ℓ),
    numOut₂_cbBParams, add_assoc]
  rfl

open QED.TwoLoop.ReflCovariance in
/-- **The split of `CD1 t`**: `-δ₂` times the `δ₃` class plus the mass-derivative part. -/
theorem cdInZero_split (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ) :
    cdInZero Q = -(Q.δ₂ : ℂ) * d3Zero Q + cdInZero (cbBParams Q) := by
  have e : (fun p' => numIn₁ Q p' (restMomentum Q.m)) = fun p' μ k =>
      (-(Q.δ₂ : ℂ)) • numD3 Q p' (restMomentum Q.m) μ k +
        numIn₁ (cbBParams Q) p' (restMomentum Q.m) μ k :=
    funext fun p' => funext fun μ => funext fun k => numIn₁_split Q _ _ μ k
  unfold cdInZero d3Zero
  rw [e, kindsZero_add (by norm_num) kindsD3 (massesD3 Q) Q hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho Q) (min_sq_le_massesD3_sq Q hmγ hΛ) intNoSubdivergenceRefined_kindsD3
    (by decide) (by decide) _ (fun p' => den₁ Q p' (restMomentum Q.m))
    (fun p' => den₁ (cbBParams Q) p' (restMomentum Q.m)) _ _
    (fun p' μ i j => (affMat_vertexChain Q.e μ (AffMat.electronNumerator Q.m p')
      (AffMat.electronNumerator Q.m (restMomentum Q.m)) Q.δ₃ Q.mγ Q.Λ i j).isLoopPoly)
    (fun p' μ i j => (affMat_numIn₁ (cbBParams Q) p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numD3_out Q _ μ i j k)
    (fun μ i j k => isLoopPoly_numIn₁_out (cbBParams Q) _ μ i j k)
    (fun p' ε _ ℓ => den₁_fac Q _ p' ε ℓ) (fun p' ε _ ℓ => den₁_fac (cbBParams Q) _ p' ε ℓ),
    numIn₂_cbBParams, add_assoc]
  rfl

end QED.ChainProof.SetCRegDisp

end
