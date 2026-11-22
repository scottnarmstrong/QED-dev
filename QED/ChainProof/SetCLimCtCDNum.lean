/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ReflCovarianceCounterterm
public import QED.Integration.X0Deg6Merge
public import QED.GradedProof.X0OneCtVertex
public import QED.GradedProof.X0Entry

/-!
# Set (c), classes `CD0`, `CD1`: the integrand as three products of degree four

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The value of
`CD1` (`CD0`) is the energy-first integral of the one-loop vertex chain with the inserted electron
line `-S̃ X S̃` on the incoming (outgoing) side and the inserted photon line
(`QED/ChainProof/SetCLimCtCDAmp.lean`); its numerator has degree six. With `A = m - k̸` and
`D = k·k + m² - iε`, the merge identity `A X A = D Y₁ + c A + iε Y₁`
(`QED.GradedProof.X0Deg6.electronNumerator_ct_electronNumerator`, with `Y₁ = δ₂ A + (δ₂ - δ_m) m`
and `c = 2m (δ_m - δ₂) m`) gives, at `ε ≠ 0`, the integrand as

`d₁ N₁ + d₂ N₂ + iε d₂ N₁` (`integrandIn_eq`, `integrandOut_eq`),

with `N₁`, `N₂` vertex chains of degree four (`numIn₁`, …) and `d₁`, `d₂` the inverse
denominators of the line kinds `kindsD3` and `kindsIn₂` (`kindsOut₂`: the doubled line). Each of
the three products is integrable in both stages of the energy-first prescription at `ε > 0`
(`energyFirstIntegrable_prodIn₁`, …).
-/

@[expose] public section

open Complex Matrix

namespace QED.ChainProof.SetCPauli

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.GradedProof.X0 (AffPoly)
open QED.GradedProof.X0Deg6 (affNum electronNumerator_ct_electronNumerator mergeU mergeV)

/-! ### The merge -/

/-- `Y₁ = δ₂ A + (δ₂ m - δ_m m)`. -/
noncomputable def mergeY (m δ₂ δm : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (δ₂ : ℂ) • electronNumerator m k + ((δ₂ : ℂ) * m - (δm * m : ℝ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The coefficient `2m (δ_m m - δ₂ m)` of `A` in `Y₂`. -/
noncomputable def mergeC (m δ₂ δm : ℝ) : ℂ := 2 * (m : ℂ) * ((δm * m : ℝ) - (δ₂ : ℂ) * m)

/-- **The merge of the inserted electron line** at `ε ≠ 0`:
`-S̃ X S̃ = D⁻¹ (-Y₁) + D⁻² (-c A) + iε D⁻² (-Y₁)`. -/
theorem electronInsertion_merge (m ε δ₂ δm : ℝ) (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    electronInsertion m ε δ₂ δm k = (propDenom m ε k)⁻¹ • -mergeY m δ₂ δm k +
      ((propDenom m ε k)⁻¹ * (propDenom m ε k)⁻¹) • -(mergeC m δ₂ δm • electronNumerator m k) +
      ((ε : ℂ) * I * ((propDenom m ε k)⁻¹ * (propDenom m ε k)⁻¹)) • -mergeY m δ₂ δm k := by
  have hD : propDenom m ε k ≠ 0 := propDenom_ne_zero hε k
  rw [electronInsertion_eq_smul, fermionCtMatrix,
    electronNumerator_ct_electronNumerator δ₂ δm m m ε]
  have e1 : affNum m k (mergeU δ₂ δm m m ε 0) (mergeV δ₂ δm m m ε 0) = mergeY m δ₂ δm k := by
    simp [affNum, mergeU, mergeV, mergeY]
  have e2 : affNum m k (mergeU δ₂ δm m m ε 1) (mergeV δ₂ δm m m ε 1) =
      mergeC m δ₂ δm • electronNumerator m k + ((ε : ℂ) * I) • mergeY m δ₂ δm k := by
    simp only [affNum, mergeU, mergeV, mergeY, mergeC, Matrix.cons_val_one, Matrix.cons_val_zero,
      smul_add, smul_smul, add_smul]
    push_cast
    module
  rw [e1, e2]
  simp only [smul_neg, smul_add, smul_smul, neg_add, ← mul_assoc]
  rw [show (propDenom m ε k)⁻¹ * (propDenom m ε k)⁻¹ * propDenom m ε k = (propDenom m ε k)⁻¹ by
    field_simp]
  module

/-! ### Degree bounds -/

/-- Every entry of the matrix function `A` is in `AffPoly d`. -/
def AffMat (d : ℕ) (A : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ i j, AffPoly d fun k => A k i j

namespace AffMat

theorem const (d : ℕ) (C : Matrix (Fin 4) (Fin 4) ℂ) : AffMat d fun _ => C :=
  fun _ _ => AffPoly.const' d _

theorem mono {d d' : ℕ} {A : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (h : d ≤ d')
    (hA : AffMat d A) : AffMat d' A := fun i j => (hA i j).mono h

theorem mul {d d' : ℕ} {A B : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hA : AffMat d A)
    (hB : AffMat d' B) : AffMat (d + d') fun k => A k * B k := fun i j => by
  simp only [Matrix.mul_apply]
  exact AffPoly.sum _ fun c _ => (hA i c).mul (hB c j)

theorem add {d : ℕ} {A B : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hA : AffMat d A)
    (hB : AffMat d B) : AffMat d fun k => A k + B k := fun i j => by
  simpa only [Matrix.add_apply] using (hA i j).add (hB i j)

theorem smul {d : ℕ} {A : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (z : ℂ) (hA : AffMat d A) :
    AffMat d fun k => z • A k := fun i j => by
  simpa only [Matrix.smul_apply, smul_eq_mul] using (hA i j).const_mul z

theorem neg {d : ℕ} {A : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hA : AffMat d A) :
    AffMat d fun k => -A k := by
  simpa only [neg_one_smul] using hA.smul (-1)

theorem electronNumerator (m : ℝ) (q : Fin 4 → ℝ) :
    AffMat 1 fun k => QED.TwoLoop.Bridge.electronNumerator m (q + k) := fun i j => by
  have h := AffPoly.comp_affine (QED.GradedProof.X0.electronNumerator_affine m i j) 1 q
  simpa only [one_smul, add_comm] using h

theorem mergeY (m δ₂ δm : ℝ) (q : Fin 4 → ℝ) :
    AffMat 1 fun k => SetCPauli.mergeY m δ₂ δm (q + k) :=
  ((electronNumerator m q).smul _).add ((const 1 _).smul _)

end AffMat

theorem affPoly_photonCtFactor (δ₃ : ℝ) (a b : Fin 4) :
    AffPoly 2 fun k => photonCtFactor δ₃ k a b := by
  have h := (((AffPoly.dot 1 0).const_mul ((Minkowski.metric a b : ℝ) : ℂ)).add
    (((AffPoly.coord 1 0 a).mul (AffPoly.coord 1 0 b)).const_mul (-1))).const_mul
      (-(I / 2) * δ₃)
  refine (congrArg (AffPoly 2) (funext fun k => ?_)).mp h
  simp only [photonCtFactor, one_smul, add_zero]
  push_cast
  ring

theorem affPoly_photonNum (δ₃ mγ Λ : ℝ) (ν ρ : Fin 4) :
    AffPoly 2 fun k => photonNum δ₃ mγ Λ k ν ρ := by
  unfold photonNum
  refine AffPoly.const_mul _ (AffPoly.sum _ fun a _ => AffPoly.sum _ fun b _ => ?_)
  have h := ((AffPoly.const (pvPhotonNum mγ Λ ν a)).mul (affPoly_photonCtFactor δ₃ a b)).mul
    (AffPoly.const (pvPhotonNum mγ Λ ρ b))
  simpa only [zero_add, add_zero] using h

theorem affMat_vertexChain (e : ℝ) (μ : Fin 4) {a b : ℕ}
    {A B : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (hA : AffMat a A) (hB : AffMat b B)
    (δ₃ mγ Λ : ℝ) :
    AffMat (2 + (a + b)) fun k => vertexChain e μ (A k) (B k) (photonNum δ₃ mγ Λ k) := by
  intro i j
  unfold vertexChain
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  refine AffPoly.const_mul _ (AffPoly.sum _ fun ν _ => AffPoly.sum _ fun ρ _ => ?_)
  have h := ((((AffMat.const 0 (Dirac.gamma ρ)).mul hA).mul (AffMat.const 0 (Dirac.gamma μ))).mul
    hB).mul (AffMat.const 0 (Dirac.gamma ν))
  have h' := (affPoly_photonNum δ₃ mγ Λ ν ρ).mul (h i j)
  simp only [add_zero, zero_add] at h'
  exact h'

/-! ### Integrability at `ε > 0` -/

theorem jointEnergyFirstIntegrable_affPoly_prod {ι : Type*} [Fintype ι] (q : ι → Fin 4 → ℝ)
    (Ms : ι → ℝ) {ε : ℝ} (hε : 0 < ε) (hcount : 4 + 4 < 2 * Fintype.card ι)
    {N : (Fin 4 → ℝ) → ℂ} (hN : AffPoly 4 N) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      N (ℓ 0) * ∏ i, (propDenom (Ms i) ε (ℓ 0 + q i))⁻¹ := by
  have h := QED.GradedProof.X0.jointEnergyFirstIntegrable_oneLoop_affPoly' (fun _ => 1)
    (fun _ => one_ne_zero) q Ms hε le_rfl hcount hN
  simpa only [one_smul] using h

/-! ### The integrands -/

section Integrand

variable (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4)

/-- The numerator `N₁` with the insertion on the incoming side. -/
noncomputable def numIn₁ (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (electronNumerator P.m (p' + k)) (-mergeY P.m P.δ₂ P.δm (p + k))
    (photonNum P.δ₃ P.mγ P.Λ k)

/-- The numerator `N₂` with the insertion on the incoming side. -/
noncomputable def numIn₂ (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (electronNumerator P.m (p' + k))
    (-(mergeC P.m P.δ₂ P.δm • electronNumerator P.m (p + k))) (photonNum P.δ₃ P.mγ P.Λ k)

/-- The numerator `N₁` with the insertion on the outgoing side. -/
noncomputable def numOut₁ (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (-mergeY P.m P.δ₂ P.δm (p' + k)) (electronNumerator P.m (p + k))
    (photonNum P.δ₃ P.mγ P.Λ k)

/-- The numerator `N₂` with the insertion on the outgoing side. -/
noncomputable def numOut₂ (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  vertexChain P.e μ (-(mergeC P.m P.δ₂ P.δm • electronNumerator P.m (p' + k)))
    (electronNumerator P.m (p + k)) (photonNum P.δ₃ P.mγ P.Λ k)

/-- The inverse photon denominators of the inserted photon line. -/
noncomputable def phDen (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹) *
    ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹)

/-- The inverse denominators of the kinds `kindsD3`. -/
noncomputable def den₁ (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹ * phDen P ε k

/-- The inverse denominators with the incoming line doubled. -/
noncomputable def denIn₂ (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (propDenom P.m ε (p' + k))⁻¹ * ((propDenom P.m ε (p + k))⁻¹ * (propDenom P.m ε (p + k))⁻¹) *
    phDen P ε k

/-- The inverse denominators with the outgoing line doubled. -/
noncomputable def denOut₂ (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ((propDenom P.m ε (p' + k))⁻¹ * (propDenom P.m ε (p' + k))⁻¹) * (propDenom P.m ε (p + k))⁻¹ *
    phDen P ε k

/-- **The `CD1` integrand as three products**, at `ε ≠ 0`. -/
theorem integrandIn_eq {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
        (electronInsertion P.m ε P.δ₂ P.δm (p + k)) (photonInsertion P.δ₃ P.mγ P.Λ ε k) =
      den₁ P p' p ε k • numIn₁ P p' p μ k + denIn₂ P p' p ε k • numIn₂ P p' p μ k +
        ((ε : ℂ) * I * denIn₂ P p' p ε k) • numIn₁ P p' p μ k := by
  rw [photonInsertion_eq_scalar _ _ _ hε, electronInsertion_merge _ _ _ _ hε,
    QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul P.m ε (p' + k), vertexChain_add_in,
    vertexChain_add_in,
    vertexChain_smul_in, vertexChain_smul_in, vertexChain_smul_in]
  simp only [vertexChain_smul_out, vertexChain_smul_photon, smul_smul]
  unfold numIn₁ numIn₂ den₁ denIn₂ phDen
  congr 2 <;> ring_nf

/-- **The `CD0` integrand as three products**, at `ε ≠ 0`. -/
theorem integrandOut_eq {ε : ℝ} (hε : ε ≠ 0) (k : Fin 4 → ℝ) :
    vertexChain P.e μ (electronInsertion P.m ε P.δ₂ P.δm (p' + k))
        (QED.OneLoop.electronPropagator P.m ε (p + k)) (photonInsertion P.δ₃ P.mγ P.Λ ε k) =
      den₁ P p' p ε k • numOut₁ P p' p μ k + denOut₂ P p' p ε k • numOut₂ P p' p μ k +
        ((ε : ℂ) * I * denOut₂ P p' p ε k) • numOut₁ P p' p μ k := by
  rw [photonInsertion_eq_scalar _ _ _ hε, electronInsertion_merge _ _ _ _ hε,
    QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul P.m ε (p + k), vertexChain_add_out,
    vertexChain_add_out,
    vertexChain_smul_out, vertexChain_smul_out, vertexChain_smul_out]
  simp only [vertexChain_smul_in, vertexChain_smul_photon, smul_smul]
  unfold numOut₁ numOut₂ den₁ denOut₂ phDen
  congr 2 <;> ring_nf

end Integrand

end QED.ChainProof.SetCPauli

end
