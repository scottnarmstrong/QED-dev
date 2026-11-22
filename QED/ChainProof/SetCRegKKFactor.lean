/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKPauliSum

/-!
# Set (c): the self-energy-type doubly pinched values factor

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSumGe` (`QED/ChainProof/SetCRegKKGe.lean`).
Of the three doubly pinched values surviving the second Ward step
(`QED.ChainProof.SetCRegDisp.tendsto_kkQS`), two have `γ^μ` at an end of the chain:

* `Q(4, 1, 3)`: the chain `γ^μ (m - (ℓ₁ + p)̸) γ^z (m - (ℓ₀ - ℓ₁ + p)̸) γ_z`, so
  `Q(4, 1, 3)^μ = γ^μ X` with `X = γ⁰ Q(4, 1, 3)⁰` (`γ⁰ γ⁰ = 1`);
* `Q(9, 2, 0)`: the chain `γ^z (m - (p' - ℓ₁)̸) γ_z (m - (ℓ₀ + ℓ₁ + p')̸) γ^μ`, so
  `Q(9, 2, 0)^μ = Y γ^μ` with `Y = Q(9, 2, 0)⁰ γ⁰`.

All lines of `Q(4, 1, 3)` (denominators, numerator, element momentum) carry no `q = p' - p`, so
`X` depends on `p` alone; all lines of `Q(9, 2, 0)` carry `p` and `q` with equal coefficients,
so `Y` depends on `p'` alone.

* `kkLimX_eq_wsum`: linearity of the pointwise limit over a finite combination;
* `kkVal_kkQ`: a doubly pinched family has a dispersive limit;
* `kNi_four_eq`, `kNi_nine_eq`: `N^μ = γ^μ γ⁰ N⁰`, `N^μ = N⁰ γ⁰ γ^μ`;
* `kkQX`, `kkQY`, **`kkQ_four_eq`**, **`kkQ_nine_eq`**: the factorizations;
* **`kkQX_indep`**, **`kkQY_indep`**: the factors depend on one external momentum only.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open QED.WickModel (Params)
open QED.Dirac (gamma)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.ChainProof.SetCLink (mvReal)
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopPolyMat)
open QED.Integration.TwoLoop (RefinedBound lineDenom lineMomentum)

/-! ### Linearity of the pointwise limit -/

/-- **The pointwise limit of a finite combination** of families with dispersive limits. -/
theorem kkLimX_eq_wsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) {w : ℝ → ℂ}
    {H : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} {G : ι → ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hH : KKVal w H) (hG : ∀ j ∈ s, KKVal w (G j)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (h : ∀ ε : ℝ, 0 < ε → ∀ ℓ, H ε x ℓ = ∑ j ∈ s, c j * G j ε x ℓ) :
    kkLimX H x = ∑ j ∈ s, c j * kkLimX (G j) x := by
  have ht : Tendsto (fun ε => ∑ j ∈ s, c j * QED.TwoLoop.jointEnergyFirstIntegral 2 (G j ε x))
      (𝓝[>] 0) (𝓝 (∑ j ∈ s, c j * kkLimX (G j) x)) :=
    tendsto_finsetSum _ fun j hj => ((hG j hj).tendsto_limX hx).const_mul _
  refine tendsto_nhds_unique (hH.tendsto_limX hx) (ht.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [← (jointEnergyFirstIntegral_wsum s c (fun j => G j ε x)
    fun j hj => (hG j hj).2.2.2.1 ε hε x hx).2]
  exact congrArg _ (funext fun ℓ => (h ε hε ℓ).symm)

/-- A combination of terms over the same lines is the term of the combination. -/
theorem sum_mul_kkT {ι : Type*} (s : Finset ι) (c : ι → ℂ) {i : Fin 12} {R : Params}
    {p p' : Fin 4 → ℝ} {t : ℝ} {k : ℕ} (κ : Fin (k + 1) → Fin 10)
    (F : ι → (Fin 2 → Fin 4 → ℝ) → ℂ) (ε x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ j ∈ s, c j * kkT i R p p' t κ (F j) ε x ℓ =
      kkT i R p p' t κ (fun ℓ => ∑ j ∈ s, c j * F j ℓ) ε x ℓ := by
  simp only [kkT, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The doubly pinched families -/

section Val

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} {w : ℝ → ℂ}
  (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  (ht : R.m ≤ t) (hw : IntegrableOn w (Ioo 0 1))
include hm hγ hγΛ hp hp' hq ht hw

/-- **A doubly pinched family has a dispersive limit.** -/
theorem kkVal_kkQ {d d' : Fin 4} (hd : d ≠ d') (hok : QOk i d d') (μ a b : Fin 4) :
    KKVal w (kkT i R p p' t (qι d d') fun ℓ =>
      kNi i R p p' .one .one ((Finset.univ.erase d).erase d') μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ) := by
  have hK := card_erase_erase_le d d' hd
  refine kkVal_kkT hm hγ hγΛ hp hp' hq ht hw le_rfl hok.1
    ((isLoopPolyMat_kNum_one_one _ _ _ _ _ _ μ hK a b).mul (isLoopPoly_elemSq _ _ p p'))
    ((refinedBoundMat_kNum_one_one _ _ _ _ _ _ μ hK a b).mul (refinedBound_elemSq _ _ p p') ?_)
  refine Finset.disjoint_left.2 fun q hq hq' => ?_
  simp only [kSet, kSlotS, Finset.union_empty, Finset.mem_image] at hq
  obtain ⟨j, -, rfl⟩ := hq
  revert hq'
  revert j
  decide

end Val

/-! ### `γ^μ` at an end of the chain -/

section Chain

variable (R : Params) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)

theorem kNi_four_gamma_mul : ∃ B, ∀ μ, kNi 4 R p p' .one .one ((Finset.univ.erase 1).erase 3) μ ℓ =
    gamma μ * B := by
  have s4 : (kPermD 4).symm 4 = 2 := kPermD_symm (by rw [(kPermD_apply 4).2.2.1]; rfl)
  have s3 : (kPermD 4).symm 3 = 0 := kPermD_symm (by rw [(kPermD_apply 4).1]; rfl)
  have s2 : (kPermD 4).symm 2 = 3 := kPermD_symm (by rw [(kPermD_apply 4).2.2.2.1]; rfl)
  have s1 : (kPermD 4).symm 1 = 1 := kPermD_symm (by rw [(kPermD_apply 4).2.1]; rfl)
  have s0 : (kPermD 4).symm 0 = 4 := kPermD_symm (by rw [(kPermD_apply 4).2.2.2.2]; rfl)
  set E := fun j => kEK (repBClass 4) (repBSlot 4) R.m p p' ((Finset.univ.erase 1).erase 3) j ℓ
  have e3 : E 3 = 1 := by simp [E, kEK]
  have e1 : E 1 = 1 := by simp [E, kEK]
  refine ⟨∑ z, ((Minkowski.metric z z : ℝ) : ℂ) • (E 2 * gamma z * E 0 * gamma z), fun μ => ?_⟩
  simp only [kNi, kNum, kOpen, ocW_eq, s4, s3, s2, s1, s0, Finset.mul_sum, Matrix.mul_smul]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [kSlotM]
  rw [show kEK (repBClass 4) (repBSlot 4) R.m p p' ((Finset.univ.erase 1).erase 3) 3 ℓ = 1
    from e3, show kEK (repBClass 4) (repBSlot 4) R.m p p' ((Finset.univ.erase 1).erase 3) 1 ℓ = 1
    from e1]
  simp [E, Matrix.mul_assoc]

theorem kNi_nine_mul_gamma : ∃ B, ∀ μ,
    kNi 9 R p p' .one .one ((Finset.univ.erase 2).erase 0) μ ℓ = B * gamma μ := by
  have s4 : (kPermD 9).symm 4 = 3 := kPermD_symm (by rw [(kPermD_apply 9).2.2.2.1]; rfl)
  have s3 : (kPermD 9).symm 3 = 1 := kPermD_symm (by rw [(kPermD_apply 9).2.1]; rfl)
  have s2 : (kPermD 9).symm 2 = 4 := kPermD_symm (by rw [(kPermD_apply 9).2.2.2.2]; rfl)
  have s1 : (kPermD 9).symm 1 = 0 := kPermD_symm (by rw [(kPermD_apply 9).1]; rfl)
  have s0 : (kPermD 9).symm 0 = 2 := kPermD_symm (by rw [(kPermD_apply 9).2.2.1]; rfl)
  set E := fun j => kEK (repBClass 9) (repBSlot 9) R.m p p' ((Finset.univ.erase 2).erase 0) j ℓ
  have e2 : E 2 = 1 := by simp [E, kEK]
  have e0 : E 0 = 1 := by simp [E, kEK]
  refine ⟨∑ z, ((Minkowski.metric z z : ℝ) : ℂ) • (gamma z * E 3 * gamma z * E 1), fun μ => ?_⟩
  simp only [kNi, kNum, kOpen, ocW_eq, s4, s3, s2, s1, s0, Finset.sum_mul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [kSlotM]
  rw [show kEK (repBClass 9) (repBSlot 9) R.m p p' ((Finset.univ.erase 2).erase 0) 2 ℓ = 1
    from e2, show kEK (repBClass 9) (repBSlot 9) R.m p p' ((Finset.univ.erase 2).erase 0) 0 ℓ = 1
    from e0]
  simp [E, Matrix.mul_assoc]

/-- `N^μ = γ^μ γ⁰ N⁰` for the chain of `Q(4, 1, 3)`. -/
theorem kNi_four_eq (μ : Fin 4) :
    kNi 4 R p p' .one .one ((Finset.univ.erase 1).erase 3) μ ℓ =
      gamma μ * gamma 0 * kNi 4 R p p' .one .one ((Finset.univ.erase 1).erase 3) 0 ℓ := by
  obtain ⟨B, hB⟩ := kNi_four_gamma_mul R p p' ℓ
  rw [hB, hB, Matrix.mul_assoc, ← Matrix.mul_assoc (gamma 0), QED.Dirac.gamma_zero_mul_gamma_zero,
    Matrix.one_mul]

/-- `N^μ = N⁰ γ⁰ γ^μ` for the chain of `Q(9, 2, 0)`. -/
theorem kNi_nine_eq (μ : Fin 4) :
    kNi 9 R p p' .one .one ((Finset.univ.erase 2).erase 0) μ ℓ =
      kNi 9 R p p' .one .one ((Finset.univ.erase 2).erase 0) 0 ℓ * gamma 0 * gamma μ := by
  obtain ⟨B, hB⟩ := kNi_nine_mul_gamma R p p' ℓ
  rw [hB, hB, Matrix.mul_assoc B, QED.Dirac.gamma_zero_mul_gamma_zero, Matrix.mul_one]

end Chain

/-! ### The factorizations -/

/-- The right factor `X = γ⁰ Q(4, 1, 3)⁰` of `Q(4, 1, 3)^μ = γ^μ X`. -/
noncomputable def kkQX (R : Params) (p p' : Fin 4 → ℝ) (t x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun c b => ∑ d, gamma 0 c d * kkQ 4 R p p' t 1 3 0 d b x

/-- The left factor `Y = Q(9, 2, 0)⁰ γ⁰` of `Q(9, 2, 0)^μ = Y γ^μ`. -/
noncomputable def kkQY (R : Params) (p p' : Fin 4 → ℝ) (t x : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun a c => ∑ d, kkQ 9 R p p' t 2 0 0 a d x * gamma 0 d c

section Factor

variable {R : Params} {p p' : Fin 4 → ℝ} {t x : ℝ}
  (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  (ht : R.m ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1)
include hm hγ hγΛ hp hp' hq ht hx

/-- **`Q(4, 1, 3)^μ = γ^μ X`.** -/
theorem kkQ_four_eq (μ a b : Fin 4) :
    kkQ 4 R p p' t 1 3 μ a b x = (gamma μ * kkQX R p p' t x) a b := by
  have hw : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioo 0 1) := integrableOn_const (by simp)
  have hok : QOk 4 1 3 := by decide +kernel
  have v := fun ν a b => kkVal_kkQ hm hγ hγΛ hp hp' hq ht hw (by decide) hok ν a b
  have e : (gamma μ * kkQX R p p' t x) a b = ∑ j : Fin 4 × Fin 4,
      (gamma μ a j.1 * gamma 0 j.1 j.2) * kkQ 4 R p p' t 1 3 0 j.2 b x := by
    simp only [Matrix.mul_apply, kkQX, Matrix.of_apply, Finset.mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [e, kkQ]
  refine kkLimX_eq_wsum Finset.univ _ (v μ a b) (fun j _ => v 0 j.2 b) hx fun ε _ ℓ => ?_
  rw [sum_mul_kkT]
  congr 1
  funext ℓ
  rw [kNi_four_eq R p p' ℓ μ]
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- **`Q(9, 2, 0)^μ = Y γ^μ`.** -/
theorem kkQ_nine_eq (μ a b : Fin 4) :
    kkQ 9 R p p' t 2 0 μ a b x = (kkQY R p p' t x * gamma μ) a b := by
  have hw : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioo 0 1) := integrableOn_const (by simp)
  have hok : QOk 9 2 0 := by decide +kernel
  have v := fun ν a b => kkVal_kkQ hm hγ hγΛ hp hp' hq ht hw (by decide) hok ν a b
  have e : (kkQY R p p' t x * gamma μ) a b = ∑ j : Fin 4 × Fin 4,
      (gamma 0 j.1 j.2 * gamma μ j.2 b) * kkQ 9 R p p' t 2 0 0 a j.1 x := by
    simp only [Matrix.mul_apply, kkQY, Matrix.of_apply, Finset.sum_mul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [e, kkQ]
  refine kkLimX_eq_wsum Finset.univ _ (v μ a b) (fun j _ => v 0 a j.1) hx fun ε _ ℓ => ?_
  rw [sum_mul_kkT]
  congr 1
  funext ℓ
  rw [kNi_nine_eq R p p' ℓ μ]
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Factor

/-! ### One external momentum -/

theorem mvReal_of_three_eq_zero (ℓ : Fin 2 → Fin 4 → ℝ) (p q q' : Fin 4 → ℝ) {v : Fin 4 → ℤ}
    (hv : v 3 = 0) : mvReal ℓ p q v = mvReal ℓ p q' v := by
  simp [mvReal, hv]

theorem mvReal_of_two_eq_three (ℓ : Fin 2 → Fin 4 → ℝ) (p p₁ p' : Fin 4 → ℝ) {v : Fin 4 → ℤ}
    (hv : v 2 = v 3) : mvReal ℓ p (p' - p) v = mvReal ℓ p₁ (p' - p₁) v := by
  simp only [mvReal, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hv, smul_sub]
  abel

/-- A term depends on the external momenta only through its lines: if every kept line, every
numerator line and the element line has the same momentum at `(p₁, p₁')` as at `(p, p')`, the
terms agree. -/
theorem kkT_congr_mom {i : Fin 12} {R : Params} {p p' p₁ p₁' : Fin 4 → ℝ} {t : ℝ} {k : ℕ}
    (κ : Fin (k + 1) → Fin 10) (K : Finset (Fin 4))
    (hl : ∀ q, (q ∈ Finset.univ.image κ ∨ q = 8 ∨ q ∈ K.image eIdx) → ∀ ℓ,
      lineMomentum (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
        (unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p') q ℓ =
      lineMomentum (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
        (unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p₁ p₁') q ℓ)
    (μ a b : Fin 4) (ε x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkT i R p p' t κ (fun ℓ => kNi i R p p' .one .one K μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ) ε x ℓ =
      kkT i R p₁ p₁' t κ (fun ℓ => kNi i R p₁ p₁' .one .one K μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p₁ p₁' ℓ) ε x ℓ := by
  have h8 : elemMom (repBClass i) (repBSlot i) p p' ℓ =
      elemMom (repBClass i) (repBSlot i) p₁ p₁' ℓ := by
    rw [elemMom_eq_kQ, elemMom_eq_kQ]
    exact hl 8 (Or.inr (Or.inl rfl)) ℓ
  have hE : (fun j => kEK (repBClass i) (repBSlot i) R.m p p' K j ℓ) =
      fun j => kEK (repBClass i) (repBSlot i) R.m p₁ p₁' K j ℓ := funext fun j => by
    unfold kEK
    split_ifs with hj
    · unfold kK
      rw [hl (eIdx j) (Or.inr (Or.inr (Finset.mem_image_of_mem _ hj))) ℓ]
    · rfl
  have hD : kkDen i R p p' κ ε ℓ = kkDen i R p₁ p₁' κ ε ℓ := by
    unfold kkDen
    refine Finset.prod_congr rfl fun c _ => ?_
    have e : ∀ pp pp' : Fin 4 → ℝ,
        lineDenom (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (κ a))
          (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] pp pp' (κ a))
          (fun a => dkMasses R (κ a)) ε c ℓ =
        lineDenom (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
          (unitMMomenta (repBClass i) (repBSlot i) ![1, 1] pp pp') (dkMasses R) ε (κ c) ℓ :=
      fun _ _ => rfl
    rw [e, e]
    unfold lineDenom
    rw [hl (κ c) (Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ c))) ℓ]
  simp only [kkT, kkSpec, elemSq, h8, hD, kNi, kNum, kSlotM, hE]

theorem uVec_four_three : (∀ a, uVec 4 1 0 (qι 1 3 a) 3 = 0) ∧ uVec 4 1 0 8 3 = 0 ∧
    ∀ j : Fin 4, j ≠ 1 → j ≠ 3 → uVec 4 1 0 (eIdx j) 3 = 0 := by
  decide +kernel

theorem uVec_nine_two : (∀ a, uVec 9 1 0 (qι 2 0 a) 2 = uVec 9 1 0 (qι 2 0 a) 3) ∧
    uVec 9 1 0 8 2 = uVec 9 1 0 8 3 ∧
    ∀ j : Fin 4, j ≠ 2 → j ≠ 0 → uVec 9 1 0 (eIdx j) 2 = uVec 9 1 0 (eIdx j) 3 := by
  decide +kernel

/-- **`X` depends on `p` alone.** -/
theorem kkQX_indep (R : Params) (p p' p₁' : Fin 4 → ℝ) (t x : ℝ) :
    kkQX R p p' t x = kkQX R p p₁' t x := by
  obtain ⟨h₁, h₂, h₃⟩ := uVec_four_three
  have hT : ∀ μ a b, (kkT 4 R p p' t (qι 1 3) fun ℓ =>
      kNi 4 R p p' .one .one ((Finset.univ.erase 1).erase 3) μ ℓ a b *
        elemSq (repBClass 4) (repBSlot 4) p p' ℓ) = (kkT 4 R p p₁' t (qι 1 3) fun ℓ =>
      kNi 4 R p p₁' .one .one ((Finset.univ.erase 1).erase 3) μ ℓ a b *
        elemSq (repBClass 4) (repBSlot 4) p p₁' ℓ) := fun μ a b => by
    funext ε x ℓ
    refine kkT_congr_mom (qι 1 3) _ (fun q hq ℓ => ?_) μ a b ε x ℓ
    rw [lineMomentum_unit_eq, lineMomentum_unit_eq]
    refine mvReal_of_three_eq_zero ℓ p _ _ ?_
    rcases hq with hq | rfl | hq
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
      exact h₁ a
    · exact h₂
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
      exact h₃ j (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))
        (Finset.ne_of_mem_erase hj)
  simp only [kkQX, kkQ, hT]

/-- **`Y` depends on `p'` alone.** -/
theorem kkQY_indep (R : Params) (p p₁ p' : Fin 4 → ℝ) (t x : ℝ) :
    kkQY R p p' t x = kkQY R p₁ p' t x := by
  obtain ⟨h₁, h₂, h₃⟩ := uVec_nine_two
  have hT : ∀ μ a b, (kkT 9 R p p' t (qι 2 0) fun ℓ =>
      kNi 9 R p p' .one .one ((Finset.univ.erase 2).erase 0) μ ℓ a b *
        elemSq (repBClass 9) (repBSlot 9) p p' ℓ) = (kkT 9 R p₁ p' t (qι 2 0) fun ℓ =>
      kNi 9 R p₁ p' .one .one ((Finset.univ.erase 2).erase 0) μ ℓ a b *
        elemSq (repBClass 9) (repBSlot 9) p₁ p' ℓ) := fun μ a b => by
    funext ε x ℓ
    refine kkT_congr_mom (qι 2 0) _ (fun q hq ℓ => ?_) μ a b ε x ℓ
    rw [lineMomentum_unit_eq, lineMomentum_unit_eq]
    refine mvReal_of_two_eq_three ℓ p p₁ p' ?_
    rcases hq with hq | rfl | hq
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
      exact h₁ a
    · exact h₂
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
      exact h₃ j (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))
        (Finset.ne_of_mem_erase hj)
  simp only [kkQY, kkQ, hT]

end QED.ChainProof.SetCRegDisp

end
