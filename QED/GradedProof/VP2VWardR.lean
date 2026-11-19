/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VLim

/-!
# The remainder of the two-loop Ward identity: covariant limits

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. In the Ward
identity of the classes `VA`, `VB`, `VC` the product `N(ℓ₀ + k) k̸ N(ℓ₀)` of the two lines next to
the vertex `μ` leaves the remainder `iε k̸`; contracting back with `γ^μ`, the remainder is
`k_μ` times the class integrand with the numerators of the lines `0` and `3` replaced by `1`:

`rNum A m k ℓ μ ν = ∑_{ρσ} kV_{ρσ} Tr[A₀ A₁ N(y₁) A₂ N(y₂) A₃]`.

* `rT_eq`: the trace is `E₀ + m² Tr[A₀ A₁ A₂ A₃]` (odd traces vanish);
* `tcov_rNumA`, `tcov_rNumB`, `tcov_rNumC`, degrees and bounds;
* `vpj_rVA`, `vpj_rVB`, `vpj_rVC`: the block-summed flavour sums are `VPJ (2 m₀)`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- The loop trace with the numerators of the lines `0`, `3` replaced by `1`. -/
noncomputable def rT (G : Fin 4 → Mat) (m : ℝ) (y₁ y₂ : Fin 4 → ℝ) : ℂ :=
  (G 0 * G 1 * electronNumerator m y₁ * G 2 * electronNumerator m y₂ * G 3).trace

theorem rT_eq_tr4 (G : Fin 4 → Mat) (m : ℝ) (y₁ y₂ : Fin 4 → ℝ) :
    rT G m y₁ y₂ = tr4 G ![1, electronNumerator m y₁, electronNumerator m y₂, 1] := by
  simp [rT, tr4]

/-- The coefficient of `m⁰` in `rT`. -/
noncomputable def rE0 (G : Fin 4 → Mat) (y₁ y₂ : Fin 4 → ℝ) : ℂ :=
  (G 0 * (G 1 * (electronNumerator 0 y₁ * (G 2 * (electronNumerator 0 y₂ * G 3))))).trace

theorem rT_eq {G : Fin 4 → Mat} (hG : ∀ l, IsOddG (G l)) (m : ℝ) (y₁ y₂ : Fin 4 → ℝ) :
    rT G m y₁ y₂ = rE0 G y₁ y₂ + (m : ℂ) ^ 2 * vE4 G := by
  unfold rT rE0 vE4
  simp only [eN_eq_add m]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_assoc, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [IsOddG.trace5 (hG 0) (hG 1) (hG 2) (isOddG_eN0 _) (hG 3),
    IsOddG.trace5 (hG 0) (hG 1) (isOddG_eN0 _) (hG 2) (hG 3)]
  ring

section Props

variable (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
  (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

/-- The remainder numerator of one fermion loop of mass `m`. -/
noncomputable def rNum (m : ℝ) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * rT (A a b ρ σ) m (fm base (ppc c k) 1 ℓ) (fm base (ppc c k) 2 ℓ)

/-- The coefficient of `m⁰` in `rNum`. -/
noncomputable def rNumE0 (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * rE0 (A a b ρ σ) (fm base (ppc c k) 1 ℓ) (fm base (ppc c k) 2 ℓ)

/-- The coefficient of `m²` in `rNum`. -/
noncomputable def rNumE2 (_k : Fin 4 → ℝ) (_ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * vE4 (A a b ρ σ)

theorem rNum_eq (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l)) (m : ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    rNum e mγ Λ A base c m k ℓ a b = rNumE0 e mγ Λ A base c k ℓ a b +
      (m : ℂ) ^ 2 * rNumE2 e mγ Λ A k ℓ a b + ((m : ℂ) ^ 2) ^ 2 * (fun _ _ _ => 0) k a b := by
  simp only [rNum, rNumE0, rNumE2, rT_eq (hA a b _ _), Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [mul_zero, add_zero]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isLoopPoly_rT_aff {n : ℕ} (G : Fin 4 → Mat) (m : ℝ)
    (Y₁ Y₂ : (Fin n → Fin 4 → ℝ) → Fin 4 → ℝ) (h₁ : IsLoopAffine Y₁) (h₂ : IsLoopAffine Y₂) :
    IsLoopPoly n 2 fun x => rT G m (Y₁ x) (Y₂ x) := by
  have h := ((((((IsLoopPolyMat.const (G 0)).mul (IsLoopPolyMat.const (G 1))).mul
    (h₁.isLoopPolyMat_electronNumerator m)).mul (IsLoopPolyMat.const (G 2))).mul
    (h₂.isLoopPolyMat_electronNumerator m)).mul (IsLoopPolyMat.const (G 3))).trace
  exact h.mono (by norm_num)

theorem isLoopPoly_rNum (m : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => rNum e mγ Λ A base c m k ℓ a b :=
  (IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.sum _ fun σ _ =>
    (isLoopPoly_rT_aff (A a b ρ σ) m _ _ (isLoopAffine_lineMomentum _ _ _)
      (isLoopAffine_lineMomentum _ _ _)).const_mul _).mono (by norm_num)

theorem isLoopPoly_rNum_k (m : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 1 2 fun y => rNum e mγ Λ A base c m (y 0) ℓ a b :=
  IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.sum _ fun σ _ =>
    (isLoopPoly_rT_aff (A a b ρ σ) m _ _ (isLoopAffine_lineMomentum_k base c _ ℓ)
      (isLoopAffine_lineMomentum_k base c _ ℓ)).const_mul _

/-- The bound of the remainder numerator on the lines `1`, `2` of a shape. -/
theorem rb_rNum {n : ℕ} (sh : Fin (n + 1) → Fin 5) (e4 : Fin 4 → Fin (n + 1))
    (he : ∀ l, sh (e4 l) = l.castSucc) (h12 : e4 1 ≠ e4 2) (m : ℝ) (k : Fin 4 → ℝ)
    (a b : Fin 4) :
    RefinedBound (castLoopMatrix fun r => base (sh r)) {e4 0, e4 1, e4 2, e4 3} 4
      fun ℓ => rNum e mγ Λ A base c m k ℓ a b := by
  refine RefinedBound.sum _ fun ρ _ => RefinedBound.sum _ fun σ _ => RefinedBound.const_mul _ ?_
  have N := fun l => rbm_fm base (ppc c k) sh (e4 l) l (he l) m
  have h0 : RefinedBoundMat (castLoopMatrix fun r => base (sh r)) ∅ 0
      fun _ => A a b ρ σ 0 * A a b ρ σ 1 := RefinedBoundMat.const _
  have h := RefinedBoundMat.trace (RBM.mulC (RBM.mulN (RBM.mulC (RBM.mulN h0 (N 1)
    (Finset.notMem_empty _)) (A a b ρ σ 2)) (N 2) (by simp [h12.symm])) (A a b ρ σ 3))
  refine h.mono (fun x hx => ?_) (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

/-- **Covariance of a remainder numerator** from the two cyclic forms of its trace. -/
theorem tcov_rNum (tr : Mat → Mat → Mat → Mat → (Fin 4 → Mat) → ℂ)
    (hA : ∀ (S T : Mat) (a b ρ σ : Fin 4) (N : Fin 4 → Mat),
      tr4 (fun l => S * A a b ρ σ l * T) N = tr (S * Dirac.gamma a * T) (S * Dirac.gamma b * T)
        (S * Dirac.gamma ρ * T) (S * Dirac.gamma σ * T) N)
    (hA1 : ∀ (a b ρ σ : Fin 4) (N : Fin 4 → Mat),
      tr4 (A a b ρ σ) N = tr (Dirac.gamma a) (Dirac.gamma b) (Dirac.gamma ρ) (Dirac.gamma σ) N)
    (hrot : ∀ Ga Gb N, ∃ P Q : Mat, ∀ Gρ Gσ, tr Ga Gb Gρ Gσ N = (P * Gσ * Q * Gρ).trace)
    (hfree : ∀ Gρ Gσ N, ∃ A B : Mat, ∀ Ga Gb, tr Ga Gb Gρ Gσ N = (Ga * A * Gb * B).trace)
    (m : ℝ) : TCov2 (rNum e mγ Λ A base c m) := by
  intro L S T h k ℓ
  funext a b
  have e1 : ∀ ρ σ, rT (A a b ρ σ) m (fm base (ppc c (L *ᵥ k)) 1 (loopAct L ℓ))
      (fm base (ppc c (L *ᵥ k)) 2 (loopAct L ℓ)) =
      tr (S * Dirac.gamma a * T) (S * Dirac.gamma b * T) (S * Dirac.gamma ρ * T)
        (S * Dirac.gamma σ * T) ![1, electronNumerator m (fm base (ppc c k) 1 ℓ),
          electronNumerator m (fm base (ppc c k) 2 ℓ), 1] := fun ρ σ => by
    rw [← hA, ← tr4_conj, rT_eq_tr4, fm_loopAct, fm_loopAct, electronNumerator_mulVec h,
      electronNumerator_mulVec h]
    congr 1
    funext l
    fin_cases l <;> simp [h.mul_eq_one']
  simp only [rNum, e1]
  rw [tcov_of h e mγ Λ tr hrot hfree]
  simp only [← hA1, ← rT_eq_tr4]
  rfl

end Props

/-! ### The three classes -/

theorem rot_VA : ∀ (Ga Gb : Mat) (N : Fin 4 → Mat), ∃ P Q : Mat, ∀ Gρ Gσ,
    trVA Ga Gb Gρ Gσ N = (P * Gσ * Q * Gρ).trace := fun Ga Gb N =>
  ⟨N 2 * Gb * N 3 * Ga * N 0, N 1, fun Gρ Gσ => by
    unfold trVA
    rw [show Ga * N 0 * Gσ * N 1 * Gρ * N 2 * Gb * N 3 =
      (Ga * N 0 * Gσ * N 1 * Gρ) * (N 2 * Gb * N 3) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]⟩

theorem free_VA : ∀ (Gρ Gσ : Mat) (N : Fin 4 → Mat), ∃ A B : Mat, ∀ Ga Gb,
    trVA Ga Gb Gρ Gσ N = (Ga * A * Gb * B).trace := fun Gρ Gσ N =>
  ⟨N 0 * Gσ * N 1 * Gρ * N 2, N 3, fun Ga Gb => by unfold trVA; simp only [Matrix.mul_assoc]⟩

theorem rot_VB : ∀ (Ga Gb : Mat) (N : Fin 4 → Mat), ∃ P Q : Mat, ∀ Gρ Gσ,
    trVB Ga Gb Gρ Gσ N = (P * Gσ * Q * Gρ).trace := fun Ga Gb N =>
  ⟨N 3 * Ga * N 0, N 1 * Gb * N 2, fun Gρ Gσ => by
    unfold trVB
    rw [show Ga * N 0 * Gσ * N 1 * Gb * N 2 * Gρ * N 3 =
      (Ga * N 0 * Gσ * N 1 * Gb * N 2 * Gρ) * N 3 by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]⟩

theorem free_VB : ∀ (Gρ Gσ : Mat) (N : Fin 4 → Mat), ∃ A B : Mat, ∀ Ga Gb,
    trVB Ga Gb Gρ Gσ N = (Ga * A * Gb * B).trace := fun Gρ Gσ N =>
  ⟨N 0 * Gσ * N 1, N 2 * Gρ * N 3, fun Ga Gb => by unfold trVB; simp only [Matrix.mul_assoc]⟩

theorem rot_VC : ∀ (Ga Gb : Mat) (N : Fin 4 → Mat), ∃ P Q : Mat, ∀ Gρ Gσ,
    trVC Ga Gb Gρ Gσ N = (P * Gσ * Q * Gρ).trace := fun Ga Gb N =>
  ⟨N 3 * Ga * N 0 * Gb * N 1, N 2, fun Gρ Gσ => by
    unfold trVC
    rw [show Ga * N 0 * Gb * N 1 * Gσ * N 2 * Gρ * N 3 =
      (Ga * N 0 * Gb * N 1 * Gσ * N 2 * Gρ) * N 3 by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]⟩

theorem free_VC : ∀ (Gρ Gσ : Mat) (N : Fin 4 → Mat), ∃ A B : Mat, ∀ Ga Gb,
    trVC Ga Gb Gρ Gσ N = (Ga * A * Gb * B).trace := fun Gρ Gσ N =>
  ⟨N 0, N 1 * Gσ * N 2 * Gρ * N 3, fun Ga Gb => by unfold trVC; simp only [Matrix.mul_assoc]⟩

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ}
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e : ℝ) {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)

include hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ

/-- The block-summed remainder integrand of a class. -/
noncomputable abbrev rSumF (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (mγ Λ : ℝ) (ε : ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * gH base c (rNum e mγ Λ A base c) mγ Λ (Φ.mass f) ε k ℓ a b

theorem vpj_rVA : VPJ (2 * m₀) (rSumF Φ e aVA baseVA cVA mγ Λ) :=
  vpj_gBlock baseVA cVA ![0, 0] ![-1, -1] flowVA hm₀ hmγ hΛ critA_VA critB_VA _ _ _ _
    (rNum_eq e mγ Λ aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_rNum e mγ Λ aVA baseVA cVA) (fun _ _ _ => IsLoopPoly.const _)
    (fun m k a b i j => rb_rNum e mγ Λ aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) m k a b)
    (fun m k a b i => rb_rNum e mγ Λ aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) m k a b)
    (tcov_rNum e mγ Λ aVA baseVA cVA trVA (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      rot_VA free_VA) (isLoopPoly_rNum_k e mγ Λ aVA baseVA cVA)
    Φ rep hmass hrep hPV₁ hPV₂

theorem vpj_rVB : VPJ (2 * m₀) (rSumF Φ e aVB baseVB cVB mγ Λ) :=
  vpj_gBlock baseVB cVB ![0, 1] ![-1, 0] flowVB hm₀ hmγ hΛ critA_VB critB_VB _ _ _ _
    (rNum_eq e mγ Λ aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_rNum e mγ Λ aVB baseVB cVB) (fun _ _ _ => IsLoopPoly.const _)
    (fun m k a b i j => rb_rNum e mγ Λ aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) m k a b)
    (fun m k a b i => rb_rNum e mγ Λ aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) m k a b)
    (tcov_rNum e mγ Λ aVB baseVB cVB trVB (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      rot_VB free_VB) (isLoopPoly_rNum_k e mγ Λ aVB baseVB cVB)
    Φ rep hmass hrep hPV₁ hPV₂

theorem vpj_rVC : VPJ (2 * m₀) (rSumF Φ e aVC baseVC cVC mγ Λ) :=
  vpj_gBlock baseVC cVC ![0, 1] ![-1, 0] flowVC hm₀ hmγ hΛ critA_VC critB_VC _ _ _ _
    (rNum_eq e mγ Λ aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_rNum e mγ Λ aVC baseVC cVC) (fun _ _ _ => IsLoopPoly.const _)
    (fun m k a b i j => rb_rNum e mγ Λ aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) m k a b)
    (fun m k a b i => rb_rNum e mγ Λ aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) m k a b)
    (tcov_rNum e mγ Λ aVC baseVC cVC trVC (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      rot_VC free_VC) (isLoopPoly_rNum_k e mγ Λ aVC baseVC cVC)
    Φ rep hmass hrep hPV₁ hPV₂

end Classes

end QED.GradedProof.VP2

end
