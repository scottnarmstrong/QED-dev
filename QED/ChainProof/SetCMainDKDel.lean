/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDKWard
public import QED.ChainProof.SetCLimCtCB01Lim

/-!
# Set (c), the `δ₃` classes: the unit with deleted electron lines

Helper level for the open links `QED.ChainProof.SetCMain.DKLimLink`, `DKCovLink`. After a Ward
identity (`QED/ChainProof/SetCMainDKWard.lean`) a term of the longitudinal part carries the
scalar `k_j² + m² = D_j + iε` of an electron line `j` of the ten-line unit: it is the term with
line `j` deleted plus `iε` times the term on all ten lines.

* `HasLimJ.of_denom`: if both the deleted and the full term have limits, the term with the
  factor `D_j + iε` has the limit of the deleted one;
* `prod_inv_succAbove`: deleting a line from the product of the inverse denominators;
* `unitZ`, `unitMMatrix_comp_eq`: the loop matrix of the unit (unscaled extra lines) composed
  with any line map is the cast of an integer matrix, so the numerator-aware criterion on it is
  decided by kernel evaluation;
* **`dkData`**: the parametric data of the unit restricted along a line map `ι` (a deletion of
  lines), with the positivity of `V` from the unit through
  `QED.Integration.TwoLoop.le_symanzikV_comp_of`.
-/

@[expose] public section
open Complex Filter Topology

namespace QED.ChainProof.SetCMain

open QED.ChainProof.SetCPauli.CB01 (HasLimJ)
open QED.TwoLoop.LimitCovariance (ParamData)
open QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.ChainProof.SetCUnit
open QED.WickModel (Params)
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrixPV
  NoSubdivergenceRefined)

/-! ### A denominator factor `D + iε` -/

/-- **A factor `D + iε` cancels a denominator.** If `Q' = D Q` for `ε > 0` and both `F Q'` and
`F Q` have limits, then `F (D + iε) Q` has the limit of `F Q'`. -/
theorem HasLimJ.of_denom {F s : (Fin 2 → Fin 4 → ℝ) → ℂ}
    {Q Q' D : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} {a b : ℂ}
    (hs : ∀ ε ℓ, s ℓ = D ε ℓ + (ε : ℂ) * I) (hQ : ∀ ε, 0 < ε → ∀ ℓ, Q' ε ℓ = D ε ℓ * Q ε ℓ)
    (h' : HasLimJ (fun ε ℓ => F ℓ * Q' ε ℓ) a) (h : HasLimJ (fun ε ℓ => F ℓ * Q ε ℓ) b) :
    HasLimJ (fun ε ℓ => F ℓ * s ℓ * Q ε ℓ) a := by
  have h2 := h'.add (h.const_mul I).eps_mul
  rw [add_zero] at h2
  refine h2.congr fun ε hε => funext fun ℓ => ?_
  rw [hs ε ℓ, hQ ε hε ℓ]
  ring

/-- The scalar `k_j² + M_j²` of a line is its denominator plus `iε`. -/
theorem sq_add_eq_lineDenom {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (p : Fin (n + 1) → Fin 4 → ℝ)
    (M : Fin (n + 1) → ℝ) (ε : ℝ) (j : Fin (n + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ((Minkowski.dot (lineMomentum α p j ℓ) (lineMomentum α p j ℓ) + M j ^ 2 : ℝ) : ℂ) =
      lineDenom α p M ε j ℓ + (ε : ℂ) * I := by
  simp [lineDenom]

/-- **Deleting a line** from the product of the inverse denominators, at `ε ≠ 0`. -/
theorem prod_inv_succAbove {n : ℕ} (α : Fin (n + 2) → Fin 2 → ℝ) (p : Fin (n + 2) → Fin 4 → ℝ)
    (M : Fin (n + 2) → ℝ) {ε : ℝ} (hε : ε ≠ 0) (j : Fin (n + 2)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i : Fin (n + 1), (lineDenom (fun i => α (j.succAbove i)) (fun i => p (j.succAbove i))
        (fun i => M (j.succAbove i)) ε i ℓ)⁻¹ =
      lineDenom α p M ε j ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹ := by
  have hD : lineDenom α p M ε j ℓ ≠ 0 := by
    rw [QED.TwoLoop.Bridge.lineDenom_eq_propDenom]
    exact QED.TwoLoop.Bridge.propDenom_ne_zero hε _
  rw [Fin.prod_univ_succAbove _ j, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]
  rfl

/-! ### The unit as an integer loop matrix -/

/-- The integer loop matrix of the ten-line unit with element slot `s`. -/
def unitZ (c : Class5) (s : Fin 8) : Fin 10 → Fin 2 → ℤ :=
  fun i => QED.Integration.TwoLoop.class5LoopMatrixPV c (mLine s i)

theorem unitMMatrix_comp_eq (c : Class5) (s : Fin 8) {k : ℕ} (ι : Fin (k + 1) → Fin 10) :
    (fun i => unitMMatrix c s (![1, 1] : Fin 2 → ℝ) (ι i)) =
      castLoopMatrix (fun i => unitZ c s (ι i)) := by
  funext i a
  have h1 : mScale (![1, 1] : Fin 2 → ℝ) (ι i) = 1 := by
    rcases mem_mEmb_or_mExtra (ι i) with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rw [hj]
    · simp [mScale, mExt_mEmb]
    · simp only [mScale, mExt_mExtra]; fin_cases j <;> rfl
  simp only [unitMMatrix, h1, one_smul, unitZ, castLoopMatrix]

/-! ### The parametric data of the unit along a line map -/

section Data

variable (c : Class5) (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (s : Fin 8)
  (hs : 4 ≤ (s : ℕ)) (R : Params) (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
  (p p' : Fin 4 → ℝ) (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

/-- The masses of the ten-line unit of the longitudinal part. -/
noncomputable abbrev dkMasses (R : Params) : Fin (2 + 8) → ℝ :=
  unitMMasses R.m R.mγ R.Λ R.mγ R.Λ ![R.mγ, R.Λ]

/-- **The parametric data of the unit restricted along `ι`**, for numerator lines `E`. -/
noncomputable def dkData {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k)
    (E : Finset (Fin (k + 1)))
    (hcrit : NoSubdivergenceRefined 2 E (castLoopMatrix fun i => unitZ c s (ι i))) :
    ParamData where
  m := k
  α := fun i => unitMMatrix c s ![1, 1] (ι i)
  p := fun i => unitMMomenta c s ![1, 1] p p' (ι i)
  M := fun i => dkMasses R (ι i)
  E := E
  hm := hk
  hcrit := by rw [unitMMatrix_comp_eq]; exact hcrit
  c := unitConst R.m R.mγ
  hc := unitConst_pos hm hγ
  hV := fun _ hz hz1 hU =>
    QED.Integration.TwoLoop.le_symanzikV_comp_of (σ := ι)
      (fun _ hw hw1 hUw => symanzikV_unitM_ge hc hs hγ ⟨le_rfl, hγΛ, le_rfl, hγΛ⟩
        (extraGe_two hγΛ) hp hp' hq hw hw1 hUw) (fun _ => le_rfl) hz hz1 hU

theorem dkData_prod {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k) (E : Finset (Fin (k + 1)))
    (hcrit : NoSubdivergenceRefined 2 E (castLoopMatrix fun i => unitZ c s (ι i))) (ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (i : Fin (k + 1)) :
    lineDenom (dkData c hc s hs R hm hγ hγΛ p p' hp hp' hq ι hk E hcrit).α
        (dkData c hc s hs R hm hγ hγΛ p p' hp hp' hq ι hk E hcrit).p
        (dkData c hc s hs R hm hγ hγΛ p p' hp hp' hq ι hk E hcrit).M ε i ℓ =
      lineDenom (unitMMatrix c s ![1, 1]) (unitMMomenta c s ![1, 1] p p') (dkMasses R) ε (ι i) ℓ :=
  rfl

end Data

end QED.ChainProof.SetCMain

end
