/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKQ
public import QED.GradedProof.X1CFactor
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegralOne

/-!
# Set (c): the doubly pinched value `Q(5, 1, 0)` splits into a vertex and a tadpole

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSumGe` (`QED/ChainProof/SetCRegKKGe.lean`).
By `QED.ChainProof.SetCRegDisp.tendsto_kkQ_five` (`QED/ChainProof/SetCRegKKCov.lean`) the sum of
the twelve longitudinal Pauli limits is the Pauli limit of `kCst · Q(5, 1, 0)`. In the class
`Cm` with the element on the photon line `4`, the electron lines `0`, `1` deleted leave the
electron lines `2`, `3` (momenta `ℓ₁ + p`, `ℓ₁ + p'`), the other photon `5`, `7` (momentum
`-ℓ₁`, masses `m_γ`, `Λ`) and the element lines `4`, `6`, `8`, `9` (momentum `k = ℓ₁ - ℓ₀`,
masses `m_γ`, `Λ`, `m_γ`, `Λ`). With `1` at both ends of the element line the chain is
`γ_z A(ℓ₁ + p') γ^μ A(ℓ₁ + p) γ^z`. After the unimodular change `ℓ₀ = ℓ₀' - ℓ₁'`, `ℓ₁ = ℓ₀'`
the integrand at fixed `ε` is a product of a function of `ℓ₀'` (the one-loop vertex) and a
function of `ℓ₁' = k` (a scalar tadpole), so its joint energy-first integral is the product of
the two one-loop energy-first integrals (`QED.GradedProof.X1C.jointEnergyFirstIntegral_mul`).

* `kkDn`, `kkVtxN`, `kkVtx`, `kkScl`: the denominators, the vertex chain, the vertex factor and
  the scalar factor `k² (t² + k²/4 - iε)⁻¹ (k² + m_γ² - iε)⁻² (k² + Λ² - iε)⁻²`;
* `kkT_five_split`: the integrand after the change;
* **`jointEnergyFirstIntegral_kkT_five`**: the value at fixed `ε` is the product of the
  energy-first integrals of `kkVtx` and `kkScl`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params vacuumPolarizationFeynmanMass)
open QED.Dirac (gamma)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCLink (mvReal)
open QED.TwoLoop.Bridge (electronNumerator)
open QED.Integration.TwoLoop (lineDenom)

/-- The Minkowski denominator `k² + M² - iε`. -/
noncomputable def kkDn (M ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot k k + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I

theorem kkDn_neg (M ε : ℝ) (k : Fin 4 → ℝ) : kkDn M ε (-k) = kkDn M ε k := by
  rw [kkDn, kkDn, dot_neg_neg']

/-- The one-loop vertex chain `γ_z A(ℓ + p') γ^μ A(ℓ + p) γ^z`. -/
noncomputable def kkVtxN (m : ℝ) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ z, ((Minkowski.metric z z : ℝ) : ℂ) • (gamma z * electronNumerator m (ℓ + p') * gamma μ *
    electronNumerator m (ℓ + p) * gamma z)

/-- **The vertex factor**: the chain over the two electron and the two photon denominators. -/
noncomputable def kkVtx (R : Params) (p p' : Fin 4 → ℝ) (ε : ℝ) (μ a b : Fin 4)
    (ℓ : Fin 4 → ℝ) : ℂ :=
  kkVtxN R.m p p' μ ℓ a b * ((kkDn R.m ε (ℓ + p'))⁻¹ * (kkDn R.m ε (ℓ + p))⁻¹ *
    (kkDn R.mγ ε ℓ)⁻¹ * (kkDn R.Λ ε ℓ)⁻¹)

/-- **The scalar factor** `k² (t² + k²/4 - iε)⁻¹ (k² + m_γ² - iε)⁻² (k² + Λ² - iε)⁻²`. -/
noncomputable def kkScl (mγ Λ t ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (Minkowski.dot k k : ℂ) *
    (((vacuumPolarizationFeynmanMass t (Minkowski.dot k k) (1 / 2) : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ *
      ((kkDn mγ ε k)⁻¹ ^ 2 * (kkDn Λ ε k)⁻¹ ^ 2)

/-- The change of loop momenta `ℓ₀ = ℓ₀' - ℓ₁'`, `ℓ₁ = ℓ₀'`. -/
def kkSplitM : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 1, 0]

theorem isUnit_det_kkSplitM : IsUnit kkSplitM.det := by
  rw [Int.isUnit_iff]; simp [kkSplitM, Matrix.det_fin_two]

theorem uVec_five_split : (fun b => uVec 5 kkSplitM 0 (qι 1 0 b)) =
    ![![1, 0, 1, 0], ![1, 0, 1, 1], ![0, 1, 0, 0], ![-1, 0, 0, 0], ![0, 1, 0, 0],
      ![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0]] := by
  decide

theorem uVec_five_split_eight : uVec 5 kkSplitM 0 8 = ![0, 1, 0, 0] := by decide

theorem uVec_five_split_two : uVec 5 kkSplitM 0 (eIdx 2) = ![1, 0, 1, 0] := by decide

theorem uVec_five_split_three : uVec 5 kkSplitM 0 (eIdx 3) = ![1, 0, 1, 1] := by decide

section Mv

variable (ℓ : Fin 2 → Fin 4 → ℝ) (p p' : Fin 4 → ℝ)

theorem mvReal_split_a : mvReal ℓ p (p' - p) ![1, 0, 1, 0] = ℓ 0 + p := by
  funext μ; simp [mvReal]

theorem mvReal_split_b : mvReal ℓ p (p' - p) ![1, 0, 1, 1] = ℓ 0 + p' := by
  funext μ; simp [mvReal]

theorem mvReal_split_c : mvReal ℓ p (p' - p) ![0, 1, 0, 0] = ℓ 1 := by
  funext μ; simp [mvReal]

theorem mvReal_split_d : mvReal ℓ p (p' - p) ![-1, 0, 0, 0] = -ℓ 0 := by
  funext μ; simp [mvReal]

end Mv

section Split

variable (R : Params) (p p' : Fin 4 → ℝ) (t ε : ℝ) (μ a b : Fin 4)

/-- The numerator of `Q(5, 1, 0)`. -/
noncomputable abbrev kkF5 (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  kNi 5 R p p' .one .one ((Finset.univ.erase 1).erase 0) μ ℓ a b *
    elemSq (repBClass 5) (repBSlot 5) p p' ℓ

theorem lineDenom_five_split (c : Fin 8) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (fun a => unitMMatrix (repBClass 5) (repBSlot 5) (![1, 1] : Fin 2 → ℝ) (qι 1 0 a))
        (fun a => unitMMomenta (repBClass 5) (repBSlot 5) ![1, 1] p p' (qι 1 0 a))
        (fun a => dkMasses R (qι 1 0 a)) ε c (chgD kkSplitM 0 p (p' - p) ℓ) =
      kkDn (dkMasses R (qι 1 0 c)) ε
        (mvReal ℓ p (p' - p) (uVec 5 kkSplitM 0 (qι 1 0 c))) := by
  change lineDenom (unitMMatrix (repBClass 5) (repBSlot 5) (![1, 1] : Fin 2 → ℝ))
    (unitMMomenta (repBClass 5) (repBSlot 5) ![1, 1] p p') (dkMasses R) ε (qι 1 0 c) _ = _
  unfold lineDenom kkDn
  rw [lineMomentum_unit_chgD]

theorem dkMasses_five_split : (fun c => dkMasses R (qι 1 0 c)) =
    ![R.m, R.m, R.mγ, R.mγ, R.Λ, R.Λ, R.mγ, R.Λ] := by
  funext c; fin_cases c <;> rfl

theorem kNi_five_split (ℓ : Fin 2 → Fin 4 → ℝ) :
    kNi 5 R p p' .one .one ((Finset.univ.erase 1).erase 0) μ (chgD kkSplitM 0 p (p' - p) ℓ) =
      kkVtxN R.m p p' μ (ℓ 0) := by
  unfold kNi kNum kOpen kkVtxN
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, kPermD_symm (i := 5) (t := 3) (k := 0) rfl,
    kPermD_symm (i := 5) (t := 2) (k := 1) rfl, kPermD_symm (i := 5) (t := 0) (k := 2) rfl,
    kPermD_symm (i := 5) (t := 4) (k := 3) rfl, kPermD_symm (i := 5) (t := 1) (k := 4) rfl]
  have h2 : (2 : Fin 4) ∈ (Finset.univ.erase 1).erase 0 := by decide
  have h3 : (3 : Fin 4) ∈ (Finset.univ.erase 1).erase 0 := by decide
  have h0 : (0 : Fin 4) ∉ (Finset.univ.erase 1).erase 0 := by decide
  have h1 : (1 : Fin 4) ∉ (Finset.univ.erase 1).erase 0 := by decide
  simp only [kSlotM, kEK, h0, h1, h2, h3, ite_true, ite_false, kK_chgD, uVec_five_split_two,
    uVec_five_split_three, mvReal_split_a, mvReal_split_b, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.mul_one]

theorem kkT_five_split (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkT 5 R p p' t (qι 1 0) (kkF5 R p p' μ a b) ε (1 / 2) (chgD kkSplitM 0 p (p' - p) ℓ) =
      kkVtx R p p' ε μ a b (ℓ 0) * kkScl R.mγ R.Λ t ε (ℓ 1) := by
  have hU := congrFun uVec_five_split
  unfold kkT kkDen kkSpec
  simp only [lineDenom_five_split, hU]
  rw [Fin.prod_univ_eight]
  have hM := congrFun (dkMasses_five_split R)
  simp only [hM, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mvReal_split_a,
    mvReal_split_b, mvReal_split_c, mvReal_split_d, elemMom_chgD, uVec_five_split_eight,
    kkF5, kNi_five_split, elemSq, kkVtx, kkScl, kkDn_neg]
  ring

/-- **The split at fixed `ε`**: the joint energy-first integral of the integrand of
`Q(5, 1, 0)` is the product of the energy-first integrals of the vertex factor and of the scalar
factor. -/
theorem jointEnergyFirstIntegral_kkT_five :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (kkT 5 R p p' t (qι 1 0) (kkF5 R p p' μ a b) ε (1 / 2)) =
      QED.OneLoop.energyFirstIntegral (kkVtx R p p' ε μ a b) *
        QED.OneLoop.energyFirstIntegral (kkScl R.mγ R.Λ t ε) := by
  have h := QED.GradedProof.X1C.jointEnergyFirstIntegral_mul (L₁ := 1) (L₂ := 1)
    (fun ℓ => kkVtx R p p' ε μ a b (ℓ 0)) (fun ℓ => kkScl R.mγ R.Λ t ε (ℓ 0))
  rw [QED.TwoLoop.jointEnergyFirstIntegral_one, QED.TwoLoop.jointEnergyFirstIntegral_one] at h
  rw [← h]
  refine (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_eq_of_comp kkSplitM isUnit_det_kkSplitM 0
    fun ℓ => ?_).symm
  rw [show (fun s => ∑ r, kkSplitM s r • ℓ r) + 0 = chgD kkSplitM 0 p (p' - p) ℓ by
    funext s μ; simp [chgD], kkT_five_split]
  rfl

end Split

end QED.ChainProof.SetCRegDisp

end
