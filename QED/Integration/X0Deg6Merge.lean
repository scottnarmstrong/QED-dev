/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0OneCt

/-!
# The doubled fermion line at a fermion counterterm vertex: the matrix identity

Helper level for the Phase 5 Stage 3 goals (HA₀) and (HS₀) (decision D-58), for the classes
whose `fermionCt` vertex sits between two propagators of the same momentum `k` and mass `M`.
With `A = M - k̸` (`electronNumerator`) and `W = D_M(k) + iε`, `k̸ k̸ = -k·k` gives
`A A = 2M A - W` (`electronNumerator_mul_self`). Hence for `X = δ₂ k̸ + δm m`,
`A X A = D_M(k) Y₁ + Y₂` with `Y₁ = δ₂ A + (δ₂ M - δm m)` and
`Y₂ = (2M(δm m - δ₂ M) + iεδ₂) A + iε(δ₂ M - δm m)` (`electronNumerator_ct_electronNumerator`),
both affine in `k`: the double spinor sum at the vertex is
`∑_{a,b} (1/i) S_{xa} (-i X_{ab}) (1/i) S_{by} = i (Y₁_{xy} D⁻¹ + Y₂_{xy} D⁻²)`
(`sum_sum_ct_entry`). The numerator degree of the pair (two lines and the vertex) drops from three
to one. `sum_sum_resum` resums an index sum over the two spinor indices of one fermion vertex.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0Deg6

open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply)

/-- The affine matrix `u A + v` built on `A = M - k̸`. -/
noncomputable def affNum (M : ℝ) (k : Fin 4 → ℝ) (u v : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  u • electronNumerator M k + v • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The coefficients of `Y₁` (index `0`) and `Y₂` (index `1`). -/
noncomputable def mergeU (δ₂ δm m M ε : ℝ) : Fin 2 → ℂ :=
  ![(δ₂ : ℂ), 2 * (M : ℂ) * ((δm * m : ℝ) - (δ₂ : ℂ) * M) + (ε : ℂ) * I * δ₂]

/-- The constant parts of `Y₁` and `Y₂`. -/
noncomputable def mergeV (δ₂ δm m M ε : ℝ) : Fin 2 → ℂ :=
  ![(δ₂ : ℂ) * M - (δm * m : ℝ), (ε : ℂ) * I * ((δ₂ : ℂ) * M - (δm * m : ℝ))]

/-- `A A = 2M A - (D_M(k) + iε)`. -/
theorem electronNumerator_mul_self (M ε : ℝ) (k : Fin 4 → ℝ) :
    electronNumerator M k * electronNumerator M k =
      (2 * (M : ℂ)) • electronNumerator M k -
        (propDenom M ε k + (ε : ℂ) * I) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hs := Dirac.slash_mul_slash k
  simp only [electronNumerator, propDenom, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hs]
  push_cast
  module

/-- **The merge identity** `A X A = D_M(k) Y₁ + Y₂`. -/
theorem electronNumerator_ct_electronNumerator (δ₂ δm m M ε : ℝ) (k : Fin 4 → ℝ) :
    electronNumerator M k * ((δ₂ : ℂ) • Dirac.slash k + ((δm * m : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)) * electronNumerator M k =
      propDenom M ε k • affNum M k (mergeU δ₂ δm m M ε 0) (mergeV δ₂ δm m M ε 0) +
        affNum M k (mergeU δ₂ δm m M ε 1) (mergeV δ₂ δm m M ε 1) := by
  set A := electronNumerator M k with hA
  have hk : Dirac.slash k = (M : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - A := by
    simp [hA, electronNumerator]
  have h2 := electronNumerator_mul_self M ε k
  rw [← hA] at h2
  have h3 : A * A * A = (2 * (M : ℂ)) • (A * A) - (propDenom M ε k + (ε : ℂ) * I) • A := by
    conv_lhs => rw [h2]
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  have hX : A * ((δ₂ : ℂ) • Dirac.slash k + ((δm * m : ℝ) : ℂ) •
      (1 : Matrix (Fin 4) (Fin 4) ℂ)) * A =
      ((δ₂ : ℂ) * M + ((δm * m : ℝ) : ℂ)) • (A * A) - (δ₂ : ℂ) • (A * A * A) := by
    rw [hk]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    module
  rw [hX, h3, h2]
  simp only [affNum, mergeU, mergeV, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, smul_sub, smul_add, smul_smul]
  module

/-- **The double spinor sum at the counterterm vertex.** -/
theorem sum_sum_ct_entry (δ₂ δm m M ε : ℝ) (hε : ε ≠ 0) (k : Fin 4 → ℝ) (x y : Fin 4) :
    ∑ a, ∑ b, (1 / I) * QED.OneLoop.electronPropagator M ε k x a *
        (-I * (((δ₂ : ℂ) • Dirac.slash k + ((δm * m : ℝ) : ℂ) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b)) *
        ((1 / I) * QED.OneLoop.electronPropagator M ε k b y) =
      I * (affNum M k (mergeU δ₂ δm m M ε 0) (mergeV δ₂ δm m M ε 0) x y *
          (propDenom M ε k)⁻¹ +
        affNum M k (mergeU δ₂ δm m M ε 1) (mergeV δ₂ δm m M ε 1) x y *
          ((propDenom M ε k)⁻¹ * (propDenom M ε k)⁻¹)) := by
  have hD := propDenom_ne_zero (M := M) hε k
  have hX : ∑ b, (∑ a, electronNumerator M k x a * (((δ₂ : ℂ) • Dirac.slash k +
      ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b)) * electronNumerator M k b y =
      propDenom M ε k * affNum M k (mergeU δ₂ δm m M ε 0) (mergeV δ₂ δm m M ε 0) x y +
        affNum M k (mergeU δ₂ δm m M ε 1) (mergeV δ₂ δm m M ε 1) x y := by
    have h := congrFun (congrFun (electronNumerator_ct_electronNumerator δ₂ δm m M ε k) x) y
    simpa only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
  simp only [electronPropagator_apply]
  have hL : ∑ a, ∑ b, (1 / I) * (electronNumerator M k x a * (propDenom M ε k)⁻¹) *
      (-I * (((δ₂ : ℂ) • Dirac.slash k + ((δm * m : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b)) *
      ((1 / I) * (electronNumerator M k b y * (propDenom M ε k)⁻¹)) =
      I * ((propDenom M ε k)⁻¹ * (propDenom M ε k)⁻¹) *
        ∑ b, (∑ a, electronNumerator M k x a * (((δ₂ : ℂ) • Dirac.slash k +
          ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b)) *
          electronNumerator M k b y := by
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [hL, hX]
  field_simp

/-- Resummation over the two spinor indices `α s`, `β s` of a fermion vertex `s`, for summands
that read them only through the last two arguments. -/
theorem sum_sum_resum {V : Type*} [Fintype V] [DecidableEq V] (s : V)
    (Φ Φ' : (V → Fin 4) → (V → Fin 4) → Fin 4 → Fin 4 → ℂ)
    (hΦ : ∀ α β a b, Φ (Function.update α s a) (Function.update β s b) = Φ α β)
    (hΦ' : ∀ α β a b, Φ' (Function.update α s a) (Function.update β s b) = Φ' α β)
    (h : ∀ α β, ∑ a, ∑ b, Φ α β a b = ∑ a, ∑ b, Φ' α β a b) :
    ∑ α, ∑ β, Φ α β (α s) (β s) = ∑ α, ∑ β, Φ' α β (α s) (β s) := by
  set e := Equiv.piSplitAt s (fun _ : V => Fin 4)
  have hsymm : ∀ b r, e.symm (b, r) = Function.update (e.symm (0, r)) s b := fun b r => by
    funext j
    by_cases hj : j = s
    · subst hj; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, Equiv.piSplitAt_symm_apply, hj]
  have key : ∀ Ψ : (V → Fin 4) → (V → Fin 4) → Fin 4 → Fin 4 → ℂ,
      (∀ α β a b, Ψ (Function.update α s a) (Function.update β s b) = Ψ α β) →
      ∑ α, ∑ β, Ψ α β (α s) (β s) =
        ∑ r : {j // j ≠ s} → Fin 4, ∑ a : Fin 4, ∑ r' : {j // j ≠ s} → Fin 4,
          ∑ b : Fin 4, Ψ (e.symm (0, r)) (e.symm (0, r')) a b := fun Ψ hΨ => by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r' _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm a r, hsymm b r', Function.update_self, Function.update_self, hΨ]
  rw [key Φ hΦ, key Φ' hΦ']
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a r' => ∑ b, Φ' (e.symm (0, r)) (e.symm (0, r'))
    a b)]
  exact Finset.sum_congr rfl fun r' _ => h _ _

end QED.GradedProof.X0Deg6

end
