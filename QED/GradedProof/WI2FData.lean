/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2TwinWard
public import QED.GradedProof.WI2P
public import QED.GradedProof.SE2FormF

/-!
# The class `F` in the Ward–Takahashi routing: the data

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the class `F` (the `δ₂`, `δ_m` counterterm on the internal electron line). The
one-loop integrand `κ seChain(-S(k) Γ(k) S(k), D(q))`, `k = p + q`, `Γ = δ₂ k̸ + δ_m m`, times the
auxiliary loop `D_aux⁻³`, is the two-slot numerator over the seven-line product data `dF`: the
electron line doubled (lines `0`, `1`, both carrying `p`), the two Pauli–Villars photon lines
(`2`, `3`), the auxiliary loop (`4`, `5`, `6`). The middle matrix `Γ(p + ℓ₀)` is bounded by the
photon line `2`.

* `dF`, `eF`, `aSlotF`, `bSlotF`, `cSlotF`, `gF`: the data and the two-slot parameters.
* `twN_dF`: the two-slot numerator is `seChain(-(E Γ E), pvPhotonNum)`.
* `refinedBoundMat_gF`, `isLoopPolyMat_gF`, `isLoopPolyMat_gF_mom`, `gF_smul`: the hypotheses of
  `SEData.hasDerivAt_pvF_twN` on the middle matrix.
* `vpos_dF`: positivity of `V` below threshold.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.ClassIntegrable

/-- The line kinds of the data of `F`. -/
def kindsF : Fin 7 → LineKind := ![.inn, .inn, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the data of `F`. -/
def massesF (Q : Params) : Fin 7 → ℝ := ![Q.m, Q.m, Q.mγ, Q.Λ, Q.m, Q.m, Q.m]

theorem intCrit_F : IntNoSubdivergenceRefined 2 {0, 1, 2} fun i => (kindsF i).dir := by decide

/-- **The data of `F`.** -/
noncomputable def dF (Q : Params) : SEData where
  m := 6
  α := castLoopMatrix fun i => (kindsF i).dir
  cs := fun i => if kindsF i = .inn then 1 else 0
  M := massesF Q
  E := {0, 1, 2}
  hm := le_rfl
  hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr intCrit_F

/-- The two electron lines of `F`. -/
def eF : Fin 2 → Fin 7 := ![0, 1]

/-- The left factors `γ^ρ` of the numerator of `F`. -/
noncomputable def aSlotF : Fin 4 × Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun l => Dirac.gamma l.2

/-- The right factors `γ^ν` of the numerator of `F`. -/
noncomputable def bSlotF : Fin 4 × Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun l => Dirac.gamma l.1

/-- The coefficients `-pvPhotonNum_{νρ}` of the numerator of `F`. -/
noncomputable def cSlotF (Q : Params) : Fin 4 × Fin 4 → ℂ := fun l => -pvPhotonNum Q.mγ Q.Λ l.1 l.2

/-- The counterterm vertex `Γ(p + ℓ₀) = δ₂ (p + ℓ₀)̸ + δ_m m`, the middle matrix of `F`. -/
noncomputable def gF (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fermionCtMatrix Q.δ₂ Q.δm Q.m (p + ℓ 0)

theorem kindsF_ne_out : ∀ i, kindsF i ≠ .out := by decide

theorem alpha_dF_two (Q : Params) : (dF Q).α 2 = ![1, 0] := by
  funext s
  fin_cases s <;> simp [dF, castLoopMatrix, kindsF, LineKind.dir]

theorem mom_dF (Q : Params) (p : Fin 4 → ℝ) : (dF Q).mom p = fun i => (kindsF i).mom p p := by
  funext i
  have hκ := kindsF_ne_out i
  change (if kindsF i = .inn then (1 : ℝ) else 0) • p = _
  rcases h : kindsF i with _ | _ | _ | _ <;> simp_all [LineKind.mom]

theorem lineMomentum_dF (Q : Params) (p : Fin 4 → ℝ) (i : Fin 7) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (dF Q).α ((dF Q).mom p) i ℓ = (kindsF i).lineMom p p ℓ := by
  rw [mom_dF]
  exact lineMomentum_kinds _ _ _ _ _

theorem prod_lineDenom_dF (Q : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (lineDenom (dF Q).α ((dF Q).mom p) (dF Q).M ε i ℓ)⁻¹ =
      ∏ i : Fin 7, (propDenom (massesF Q i) ε ((kindsF i).lineMom p p ℓ))⁻¹ := by
  rw [mom_dF]
  exact prod_lineDenom_kinds _ _ _ _ _ _

theorem twN_dF (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dF Q).twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) p ℓ =
      seChain (-(electronNumerator Q.m (p + ℓ 0) * fermionCtMatrix Q.δ₂ Q.δm Q.m (p + ℓ 0) *
        electronNumerator Q.m (p + ℓ 0))) (pvPhotonNum Q.mγ Q.Λ) := by
  have h0 := lineMomentum_dF Q p 0 ℓ
  have h1 := lineMomentum_dF Q p 1 ℓ
  simp only [kindsF, LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  simp only [SEData.twN, SEData.tw, SEData.twE, seChain, Fintype.sum_prod_type, aSlotF, bSlotF,
    cSlotF, gF, eF, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h0, h1]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_smul, smul_neg, Matrix.mul_assoc]

theorem refinedBoundMat_gF (Q : Params) (p : Fin 4 → ℝ) :
    RefinedBoundMat (dF Q).α ({2} : Finset (Fin 7)) 1 (gF Q p) := fun a b => by
  have hl : ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      Integration.TwoLoop.lineMomentum (dF Q).α (fun _ => p) 2 ℓ = p + ℓ 0 := fun ℓ => by
    funext μ
    simp [Integration.TwoLoop.lineMomentum, alpha_dF_two, Fin.sum_univ_two, add_comm]
  have hE := (refinedBound_electronNumerator (dF Q).α (fun _ => p) 2 0 a b).const_mul
    (-(Q.δ₂ : ℂ))
  have hc := (RefinedBound.const (α := (dF Q).α)
    ((((Q.δm * Q.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b)).mono
      (E' := ({2} : Finset (Fin 7))) (Finset.empty_subset _) (Nat.zero_le 1)
  simp only [hl] at hE
  have h := hE.add hc
  refine (congrArg (RefinedBound (dF Q).α ({2} : Finset (Fin 7)) 1) (funext fun ℓ => ?_)).mp h
  simp only [gF, fermionCtMatrix_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem isLoopPolyMat_gF (Q : Params) (p : Fin 4 → ℝ) : IsLoopPolyMat 2 1 (gF Q p) := by
  have ha : IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => p + ℓ 0 :=
    ⟨![1, 0], p, fun ℓ => by funext μ; simp [Fin.sum_univ_two, add_comm]⟩
  have h := isLoopPolyMat_add (isLoopPolyMat_smul (-(Q.δ₂ : ℂ))
    (ha.isLoopPolyMat_electronNumerator 0)) (isLoopPolyMat_mono (isLoopPolyMat_smul
      ((Q.δm * Q.m : ℝ) : ℂ) (IsLoopPolyMat.const (L := 2) (1 : Matrix (Fin 4) (Fin 4) ℂ)))
      (Nat.zero_le _))
  convert h using 1
  funext ℓ
  exact fermionCtMatrix_eq _ _ _ _

theorem isLoopPolyMat_gF_mom (Q : Params) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPolyMat 1 1 fun y => gF Q (y 0) ℓ := by
  have h := isLoopPolyMat_add (isLoopPolyMat_smul (-(Q.δ₂ : ℂ))
    ((isLoopAffine_add_const (ℓ 0)).isLoopPolyMat_electronNumerator 0)) (isLoopPolyMat_mono
      (isLoopPolyMat_smul ((Q.δm * Q.m : ℝ) : ℂ)
        (IsLoopPolyMat.const (L := 1) (1 : Matrix (Fin 4) (Fin 4) ℂ))) (Nat.zero_le _))
  convert h using 1
  funext y
  exact fermionCtMatrix_eq _ _ _ _

theorem gF_smul (Q : Params) (r : Fin 4 → ℝ) (t : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    gF Q (t • r) ℓ = gF Q 0 ℓ + t • ((Q.δ₂ : ℂ) • Dirac.slash r) := by
  simp only [gF, fermionCtMatrix, zero_add, Dirac.slash_add, Dirac.slash_smul, smul_add]
  rw [smul_comm, Complex.coe_smul]
  abel

theorem vpos_dF (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ)
    {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) : (dF Q).VPos ((dF Q).mom p) := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  obtain ⟨h1, h2⟩ := sq_min_le Q hmγ hΛ
  have hMe : ∀ i, kindsF i ≠ .pho → Q.m ^ 2 ≤ massesF Q i ^ 2 := by
    intro i hi; fin_cases i <;> simp_all [kindsF, massesF]
  have hMp : ∀ i, kindsF i = .pho → ν ^ 2 ≤ massesF Q i ^ 2 := by
    intro i hi
    have hν2 := pow_le_pow_left₀ hν0.le hν 2
    fin_cases i <;> simp_all [kindsF, massesF] <;> linarith
  refine ⟨min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) * min (Q.m ^ 2) (ν ^ 2),
    min_one_mul_pos (by positivity) (lt_min (by positivity) (by positivity)) hp,
    fun z hz hz1 hU => ?_⟩
  rw [mom_dF]
  exact symanzikV_kinds_se_ge kindsF (by decide) (massesF Q) hm hν0 hp hMe hMp hz hz1 hU

end QED.GradedProof.WI2

end
