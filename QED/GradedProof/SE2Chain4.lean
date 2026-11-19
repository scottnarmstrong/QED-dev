/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2CovTensor
public import QED.TwoLoop.LimitCovarianceOpen

/-!
# Spinor covariance of the open two-loop chain through four vertices

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, classes `R`, `X`.

* `chain4 w E₃ E₂ E₁ = ∑_l w(l) γ^{l₃} E₃ γ^{l₂} E₂ γ^{l₁} E₁ γ^{l₀}`, the open line through four
  `gauge` vertices with the photon weight `w`.
* `WeightCov L w`: `∑_l w(l) ∏ₜ L^{lₜ}_{zₜ} = w(z)`; it holds for the rainbow and crossed pairings
  of two Pauli–Villars photons (`weightCov_pair`).
* `mul_chain4_mul`: for a spinor lift `(S, S')` of `L` and `WeightCov L w`,
  `S chain4 w E S' = chain4 w (S E S')`.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.SE2

open QED.TwoLoop.LimitCovariance QED.WickModel

/-- The chain `G₃ E₃ G₂ E₂ G₁ E₁ G₀`. -/
def chainG (G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (E₃ E₂ E₁ : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  G 3 * E₃ * G 2 * E₂ * G 1 * E₁ * G 0

/-- The open two-loop chain with photon weight `w`. -/
noncomputable def chain4 (w : (Fin 4 → Fin 4) → ℂ) (E₃ E₂ E₁ : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ l : Fin 4 → Fin 4, w l • chainG (fun t => Dirac.gamma (l t)) E₃ E₂ E₁

/-- Sums over functions `Fin 4 → Fin 4` are four nested sums. -/
theorem sum_fin4_fun {M : Type*} [AddCommMonoid M] (g : (Fin 4 → Fin 4) → M) :
    ∑ l, g l = ∑ a₀, ∑ a₁, ∑ a₂, ∑ a₃, g ![a₀, a₁, a₂, a₃] := by
  let e : (Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃ (Fin 4 → Fin 4) :=
    { toFun := fun a => ![a.1, a.2.1, a.2.2.1, a.2.2.2]
      invFun := fun l => (l 0, l 1, l 2, l 3)
      left_inv := fun _ => rfl
      right_inv := fun l => by
        funext t
        fin_cases t <;> rfl }
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The chain is multilinear in the four vertex matrices. -/
theorem chainG_sum (a : Fin 4 → Fin 4 → ℂ) (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (E₃ E₂ E₁ : Matrix (Fin 4) (Fin 4) ℂ) :
    chainG (fun t => ∑ z, a t z • X z) E₃ E₂ E₁ =
      ∑ l : Fin 4 → Fin 4, (∏ t, a t (l t)) • chainG (fun t => X (l t)) E₃ E₂ E₁ := by
  rw [sum_fin4_fun]
  simp only [chainG, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Fin.prod_univ_four]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, mul_assoc]

/-- The photon weight transforms into itself under `L`. -/
def WeightCov (L : Matrix (Fin 4) (Fin 4) ℝ) (w : (Fin 4 → Fin 4) → ℂ) : Prop :=
  ∀ z : Fin 4 → Fin 4, ∑ l : Fin 4 → Fin 4, w l * ∏ t, ((L (l t) (z t) : ℝ) : ℂ) = w z

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}

theorem mul_chainG_mul (h : IsSpinLift L S S') (G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (E₃ E₂ E₁ : Matrix (Fin 4) (Fin 4) ℂ) :
    S * chainG G E₃ E₂ E₁ * S' =
      chainG (fun t => S * G t * S') (S * E₃ * S') (S * E₂ * S') (S * E₁ * S') := by
  simp only [chainG, h.mul_mul_mul]

/-- **Covariance of the open two-loop chain.** -/
theorem mul_chain4_mul (h : IsSpinLift L S S') {w : (Fin 4 → Fin 4) → ℂ} (hw : WeightCov L w)
    (E₃ E₂ E₁ : Matrix (Fin 4) (Fin 4) ℂ) :
    S * chain4 w E₃ E₂ E₁ * S' = chain4 w (S * E₃ * S') (S * E₂ * S') (S * E₁ * S') := by
  have e : ∀ l : Fin 4 → Fin 4, chainG (fun t => ∑ ν, ((L (l t) ν : ℝ) : ℂ) • Dirac.gamma ν)
      (S * E₃ * S') (S * E₂ * S') (S * E₁ * S') =
      ∑ z : Fin 4 → Fin 4, (∏ t, ((L (l t) (z t) : ℝ) : ℂ)) •
        chainG (fun t => Dirac.gamma (z t)) (S * E₃ * S') (S * E₂ * S') (S * E₁ * S') :=
    fun l => chainG_sum (fun t z => ((L (l t) z : ℝ) : ℂ)) Dirac.gamma _ _ _
  simp only [chain4, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_chainG_mul h, h.mul_gamma_mul, e, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_smul, hw z]

/-! ### The rainbow and crossed photon weights -/

/-- The rainbow weight: photons `0 – 3` and `1 – 2`. -/
noncomputable def wR (P : Params) (x : Fin 4 → Fin 4) : ℂ :=
  pvEta P (x 0) (x 3) * pvEta P (x 1) (x 2)

/-- The crossed weight: photons `0 – 2` and `1 – 3`. -/
noncomputable def wX (P : Params) (x : Fin 4 → Fin 4) : ℂ :=
  pvEta P (x 0) (x 2) * pvEta P (x 1) (x 3)

theorem weightCov_wR (h : IsSpinLift L S S') (P : Params) : WeightCov L (wR P) := by
  intro z
  rw [sum_fin4_fun, wR, ← pvEta_pair h P (z 0) (z 3), ← pvEta_pair h P (z 1) (z 2)]
  simp only [wR, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => enter [2, r]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem weightCov_wX (h : IsSpinLift L S S') (P : Params) : WeightCov L (wX P) := by
  intro z
  rw [sum_fin4_fun, wX, ← pvEta_pair h P (z 0) (z 2), ← pvEta_pair h P (z 1) (z 3)]
  simp only [wX, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => enter [2, r]; rw [Finset.sum_comm]
  conv_rhs => enter [2, r, 2, p]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end QED.GradedProof.SE2

end
