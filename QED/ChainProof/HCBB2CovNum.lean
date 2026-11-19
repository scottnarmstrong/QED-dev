/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2Num
public import QED.TwoLoop.LimitCovarianceCounterterm
public import QED.TwoLoop.CountertermLimit

/-!
# The four numerators of the bubble–bubble vertex: polynomiality and covariance

Helper level, Phase 5 Stage 1a (O3-8 for `QED.ChainProof.Enum.repBB`). The matrix families
`NG = vertexNumeratorMatrix` (the Feynman-gauge chain), `NS = ℓ² γ^μ`,
`NL = ℓ̸ (m - p̸') γ^μ + γ^μ (m - p̸) ℓ̸` and `NQ = ℓ̸ (m - p̸') γ^μ (m - p̸) ℓ̸`, whose entries
are the numerators `numG`, `numS`, `numL`, `numQ` of `QED/ChainProof/HCBB2Num.lean`:

* `isLoopPoly_numG`, …: every entry, as a function of `ℓ 0`, is a loop polynomial of degree
  `≤ 4` (in fact `≤ 2`) in two loop momenta, as the parametric representation needs;
* `NG_cov`, …: **covariance** under a real `L` with spinor lift `(S, T)`, with the external
  momenta moved: `S N(L p', L p)^μ(L ℓ) T = L^μ_ν N(p', p)^ν(ℓ)`.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.ChainProof.HCBB2

open QED.Dirac QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance QED.TwoLoop.CountertermLimit

/-! ### The matrix families -/

/-- The Feynman-gauge chain `∑ g_{νρ} γ^ρ (m - (p'+ℓ)̸) γ^μ (m - (p+ℓ)̸) γ^ν`. -/
noncomputable def NG (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  IsSpinLift.chain (fun ν ρ => ((Minkowski.metric ν ρ : ℝ) : ℂ))
    (electronNumerator m (p' + ℓ)) (electronNumerator m (p + ℓ)) μ

/-- `ℓ² γ^μ`. -/
noncomputable def NS (μ : Fin 4) (ℓ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) • gamma μ

/-- `ℓ̸ (m - p̸') γ^μ + γ^μ (m - p̸) ℓ̸`. -/
noncomputable def NL (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  slash ℓ * (electronNumerator m p' * gamma μ) + (gamma μ * electronNumerator m p) * slash ℓ

/-- `ℓ̸ (m - p̸') γ^μ (m - p̸) ℓ̸`. -/
noncomputable def NQ (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  slash ℓ * (electronNumerator m p' * gamma μ * electronNumerator m p) * slash ℓ

theorem NG_apply (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) :
    NG m p' p μ ℓ i j = numG m p' p μ i j ℓ := by
  simp only [NG, IsSpinLift.chain, numG, QED.OneLoop.vertexNumerator, electronNumerator,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem NS_apply (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) : NS μ ℓ i j = numS μ i j ℓ := by
  simp only [NS, numS, Matrix.smul_apply, smul_eq_mul]

theorem NL_apply (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) :
    NL m p' p μ ℓ i j = numL m p' p μ i j ℓ := rfl

theorem NQ_apply (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ℓ : Fin 4 → ℝ) :
    NQ m p' p μ ℓ i j = numQ m p' p μ i j ℓ := rfl

/-! ### Polynomiality -/

theorem isLoopPolyMat_slash_zero : IsLoopPolyMat 2 1 fun ℓ : Fin 2 → Fin 4 → ℝ => slash (ℓ 0) := by
  have h := isLoopPolyMat_smul (-1) ((isLoopAffine_add_zero 0).isLoopPolyMat_electronNumerator 0)
  refine fun i j => (congrArg (IsLoopPoly 2 1) (funext fun ℓ => ?_)).mp (h i j)
  simp [electronNumerator]

theorem isLoopPoly_NG (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => NG m p' p μ (ℓ 0) i j := by
  simp only [NG, IsSpinLift.chain, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun ν _ => IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.const_mul _ ?_
  have h := ((((IsLoopPolyMat.const (L := 2) (gamma ρ)).mul
    (isLoopPolyMat_electronNumerator_add m p')).mul (IsLoopPolyMat.const (gamma μ))).mul
    (isLoopPolyMat_electronNumerator_add m p)).mul (IsLoopPolyMat.const (gamma ν))
  exact (h i j).mono (by norm_num)

theorem isLoopPoly_NS (μ i j : Fin 4) : IsLoopPoly 2 4 fun ℓ => NS μ (ℓ 0) i j := by
  have h := (isLoopPolyMat_slash_zero.mul isLoopPolyMat_slash_zero).mul
    (IsLoopPolyMat.const (L := 2) (gamma μ))
  refine ((congrArg (IsLoopPoly 2 (1 + 1 + 0)) (funext fun ℓ => ?_)).mp
    ((isLoopPolyMat_smul (-1) h) i j)).mono (by norm_num)
  dsimp only
  rw [slash_mul_slash]
  simp only [NS, Matrix.smul_apply, Matrix.smul_mul, Matrix.one_mul, smul_eq_mul]
  push_cast
  ring

theorem isLoopPoly_NL (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => NL m p' p μ (ℓ 0) i j := by
  have h := isLoopPolyMat_add (isLoopPolyMat_slash_zero.mul (IsLoopPolyMat.const (L := 2)
    (electronNumerator m p' * gamma μ)))
    ((IsLoopPolyMat.const (L := 2) (gamma μ * electronNumerator m p)).mul
      isLoopPolyMat_slash_zero)
  exact ((show IsLoopPolyMat 2 1 fun ℓ => NL m p' p μ (ℓ 0) from h) i j).mono (by norm_num)

theorem isLoopPoly_NQ (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => NQ m p' p μ (ℓ 0) i j := by
  have h := (isLoopPolyMat_slash_zero.mul (IsLoopPolyMat.const (L := 2)
    (electronNumerator m p' * gamma μ * electronNumerator m p))).mul isLoopPolyMat_slash_zero
  exact (h i j).mono (by norm_num)

/-! ### Covariance -/

section Cov

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S T)
include h

theorem NG_cov (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    S * NG m (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ ℓ) * T = vecAct L (fun ν => NG m p' p ν ℓ) μ := by
  simp only [NG, h.mul_chain_mul, tensorAct_metric h, ← Matrix.mulVec_add,
    h.mul_electronNumerator_mul]

theorem NS_cov (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    S * NS μ (L *ᵥ ℓ) * T = vecAct L (fun ν => NS ν ℓ) μ := by
  simp only [NS, Matrix.mul_smul, Matrix.smul_mul, h.mul_gamma_mul, h.dot_mulVec, vecAct,
    Finset.smul_sum, smul_comm (((Minkowski.dot ℓ ℓ : ℝ) : ℂ))]

theorem NL_cov (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    S * NL m (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ ℓ) * T = vecAct L (fun ν => NL m p' p ν ℓ) μ := by
  simp only [NL, Matrix.mul_add, Matrix.add_mul, h.mul_mul_mul, h.mul_slash_mul,
    h.mul_electronNumerator_mul, h.mul_gamma_mul, vecAct, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_add_distrib, smul_add]

theorem NQ_cov (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    S * NQ m (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ ℓ) * T = vecAct L (fun ν => NQ m p' p ν ℓ) μ := by
  simp only [NQ, h.mul_mul_mul, h.mul_slash_mul, h.mul_electronNumerator_mul, h.mul_gamma_mul,
    vecAct, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end Cov

end QED.ChainProof.HCBB2

end
