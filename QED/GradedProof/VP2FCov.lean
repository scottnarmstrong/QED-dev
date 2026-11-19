/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Kinds

/-!
# The numerators of the inserted bubble: covariance and degrees

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, classes `F0`,
`F1`. The numerators `E₀`, `E₂`, `E₄` of the second divided difference of the inserted bubble
(`QED.GradedProof.VP2.tri_ins_eq`) depend on `ε` through `D₀(y) = y² - iε`; with `V₀ = y²` they are
`E₀ = n₀ + (iε) n₁ + (iε)² n₂`, `E₂ = n₁ + 2 (iε) n₂`, `E₄ = n₂` (`eE0_eq`, `eE2_eq`) with the
`ε`-independent numerators

`n₀ = T₀ - V₀ T₂ + V₀² T₄`, `n₁ = T₂ - 2 V₀ T₄`, `n₂ = T₄`.

As tensors `N_k(q)^{μν} = n_j(γ^μ, γ^ν, x, y)` at `x, y ∈ {q, k + q}` they are covariant
(`tcovN_tn`, with the transpose `tcovN_tnT`), of degree `4, 2, 0` in `q` and polynomial in `k`.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Covariance -/

theorem TCovN.add {N N' : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (h : TCovN N)
    (h' : TCovN N') : TCovN fun k q i j => N k q i j + N' k q i j := by
  intro L S S' hL k q
  funext i j
  simp only [h L S S' hL k q, h' L S S' hL k q, upperAct, mul_add, Finset.sum_add_distrib]

/-- Multiplying by an invariant scalar keeps a tensor covariant. -/
theorem TCovN.mul_inv {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {c : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℂ} (h : TCovN N)
    (hc : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Mat), IsSpinLift L S S' →
      ∀ k q, c (L *ᵥ k) (L *ᵥ q) = c k q) :
    TCovN fun k q i j => c k q * N k q i j := by
  intro L S S' hL k q
  funext i j
  simp only [h L S S' hL k q, hc L S S' hL k q, upperAct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The transpose of a covariant tensor is covariant. -/
theorem TCovN.transpose {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (h : TCovN N) :
    TCovN fun k q i j => N k q j i := by
  intro L S S' hL k q
  funext i j
  simp only [h L S S' hL k q, upperAct]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Matrix families transforming as `A(Lk, Lq) = T A(k, q) S` under a spinor lift `(S, T)`. -/
def MCov (A : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Mat) : Prop :=
  ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Mat), IsSpinLift L S T →
    ∀ k q, A (L *ᵥ k) (L *ᵥ q) = T * A k q * S

theorem MCov.one : MCov fun _ _ => 1 := by
  intro L S T h k q
  rw [Matrix.mul_one, h.mul_eq_one']

theorem MCov.mul {A B : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Mat} (hA : MCov A) (hB : MCov B) :
    MCov fun k q => A k q * B k q := by
  intro L S T h k q
  beta_reduce
  rw [hA L S T h, hB L S T h]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S T, h.mul_eq_one, Matrix.one_mul]

theorem MCov.slash_zk (c : Bool) : MCov fun k q => Dirac.slash (zk k c q) := by
  intro L S T h k q
  beta_reduce
  rw [zk_mulVec, h.slash_mulVec]

theorem tcovN_traceT {A B : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Mat} (hA : MCov A) (hB : MCov B) :
    TCovN fun k q i j => traceT (A k q) (B k q) i j := by
  intro L S T h k q
  funext i j
  beta_reduce
  rw [hA L S T h, hB L S T h, traceT_conj h]

/-! ### The numerators -/

/-- `V₀ = y²` as a complex number. -/
noncomputable def v0 (y : Fin 4 → ℝ) : ℂ := propDenom 0 0 y

/-- `n₀ = T₀ - V₀ T₂ + V₀² T₄`. -/
noncomputable def nT0 (A B : Mat) (d₂ dm : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  insT0 A B d₂ x y - v0 y * insT2 A B d₂ dm x y + v0 y ^ 2 * insT4 A B dm

/-- `n₁ = T₂ - 2 V₀ T₄`. -/
noncomputable def nT1 (A B : Mat) (d₂ dm : ℝ) (x y : Fin 4 → ℝ) : ℂ :=
  insT2 A B d₂ dm x y - 2 * v0 y * insT4 A B dm

/-- `n₂ = T₄`. -/
noncomputable def nT2 (A B : Mat) (dm : ℝ) : ℂ := insT4 A B dm

theorem propDenom_zero_eps (ε : ℝ) (y : Fin 4 → ℝ) : propDenom 0 ε y = v0 y - ε * I := by
  simp only [v0, propDenom]
  push_cast
  ring

theorem eE0_eq (A B : Mat) (d₂ dm ε : ℝ) (x y : Fin 4 → ℝ) :
    insT0 A B d₂ x y - propDenom 0 ε y * insT2 A B d₂ dm x y +
        propDenom 0 ε y * propDenom 0 ε y * insT4 A B dm =
      nT0 A B d₂ dm x y + (ε * I) * nT1 A B d₂ dm x y + (ε * I) ^ 2 * nT2 A B dm := by
  rw [propDenom_zero_eps]
  simp only [nT0, nT1, nT2]
  ring

theorem eE2_eq (A B : Mat) (d₂ dm ε : ℝ) (x y : Fin 4 → ℝ) :
    insT2 A B d₂ dm x y - 2 * propDenom 0 ε y * insT4 A B dm =
      nT1 A B d₂ dm x y + 2 * (ε * I) * nT2 A B dm := by
  rw [propDenom_zero_eps]
  simp only [nT1, nT2]
  ring

/-! ### The numerators as tensors -/

theorem insT0_gamma (μ ν : Fin 4) (d₂ : ℝ) (x y : Fin 4 → ℝ) :
    insT0 (Dirac.gamma μ) (Dirac.gamma ν) d₂ x y =
      -(d₂ : ℂ) * traceT (Dirac.slash x) (Dirac.slash y * Dirac.slash y * Dirac.slash y) μ ν := by
  simp only [insT0, traceT, Matrix.mul_assoc]

theorem insT2_gamma (μ ν : Fin 4) (d₂ dm : ℝ) (x y : Fin 4 → ℝ) :
    insT2 (Dirac.gamma μ) (Dirac.gamma ν) d₂ dm x y =
      ((dm : ℂ) - 2 * d₂) * traceT 1 (Dirac.slash y * Dirac.slash y) μ ν +
        (2 * (dm : ℂ) - d₂) * traceT (Dirac.slash x) (Dirac.slash y) μ ν := by
  simp only [insT2, traceT, Matrix.mul_assoc, Matrix.one_mul]

theorem insT4_gamma (μ ν : Fin 4) (dm : ℝ) :
    insT4 (Dirac.gamma μ) (Dirac.gamma ν) dm = (dm : ℂ) * traceT 1 1 μ ν := by
  simp only [insT4, traceT, Matrix.mul_one]

/-- The tensor numerators `n_j(γ^μ, γ^ν, x, y)` at `x = zk k bx q`, `y = zk k bY q`. -/
noncomputable def tn (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    ℂ :=
  match j with
  | 0 => nT0 (Dirac.gamma μ) (Dirac.gamma ν) d₂ dm (zk k bx q) (zk k bY q)
  | 1 => nT1 (Dirac.gamma μ) (Dirac.gamma ν) d₂ dm (zk k bx q) (zk k bY q)
  | 2 => nT2 (Dirac.gamma μ) (Dirac.gamma ν) dm

theorem v0_inv (c : Bool) (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Mat) (h : IsSpinLift L S S')
    (k q : Fin 4 → ℝ) : v0 (zk (L *ᵥ k) c (L *ᵥ q)) = v0 (zk k c q) := by
  rw [zk_mulVec, v0, propDenom_mulVec' h, v0]

theorem tcovN_tn (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) : TCovN (tn j d₂ dm bx bY) := by
  have hc : ∀ c : ℂ, ∀ {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}, TCovN N →
      TCovN fun k q i j => c * N k q i j := fun c N h =>
    TCovN.mul_inv (c := fun _ _ => c) h fun _ _ _ _ _ _ => rfl
  have hv : ∀ n : ℕ, ∀ {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}, TCovN N →
      TCovN fun k q i j => v0 (zk k bY q) ^ n * N k q i j := fun n N h =>
    TCovN.mul_inv (c := fun k q => v0 (zk k bY q) ^ n) h fun L S S' hL k q => by
      simp only [v0_inv bY L S S' hL]
  have sx := MCov.slash_zk bx
  have sy := MCov.slash_zk bY
  have t0 : TCovN fun k q i j =>
      insT0 (Dirac.gamma i) (Dirac.gamma j) d₂ (zk k bx q) (zk k bY q) := by
    simp only [insT0_gamma]
    exact hc _ (tcovN_traceT sx ((sy.mul sy).mul sy))
  have t2 : TCovN fun k q i j =>
      insT2 (Dirac.gamma i) (Dirac.gamma j) d₂ dm (zk k bx q) (zk k bY q) := by
    simp only [insT2_gamma]
    exact (hc _ (tcovN_traceT MCov.one (sy.mul sy))).add (hc _ (tcovN_traceT sx sy))
  have t4 : TCovN fun (_ _ : Fin 4 → ℝ) i j => insT4 (Dirac.gamma i) (Dirac.gamma j) dm := by
    simp only [insT4_gamma]
    exact hc _ (tcovN_traceT MCov.one MCov.one)
  match j with
  | 0 =>
    have := ((t0.add ((hv 1 t2).mul_inv (c := fun _ _ => -1) fun _ _ _ _ _ _ => rfl)).add
      (hv 2 t4))
    refine (congrArg TCovN ?_).mp this
    funext k q i j
    simp only [tn, nT0, pow_one]
    ring
  | 1 =>
    have := t2.add (((hv 1 t4).mul_inv (c := fun _ _ => -2) fun _ _ _ _ _ _ => rfl))
    refine (congrArg TCovN ?_).mp this
    funext k q i j
    simp only [tn, nT1, pow_one]
    ring
  | 2 => exact t4

/-! ### Degrees -/

section Poly

variable {L : ℕ} {A B : Mat} {x y : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ}

theorem isLoopPolyMat_slash' {F : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ} (hF : IsLoopAffine F) :
    IsLoopPolyMat L 1 fun ℓ => Dirac.slash (F ℓ) := fun i j => by
  have h := (hF.isLoopPolyMat_electronNumerator 0 i j).const_mul (-1)
  refine (congrArg (IsLoopPoly L 1) (funext fun ℓ => ?_)).mp h
  simp [electronNumerator]

theorem isLoopPoly_insT0' (hx : IsLoopAffine x) (hy : IsLoopAffine y) (d₂ : ℝ) :
    IsLoopPoly L 4 fun ℓ => insT0 A B d₂ (x ℓ) (y ℓ) := by
  have h := (((IsLoopPolyMat.const A).mul ((isLoopPolyMat_slash' hx).mul
    ((IsLoopPolyMat.const B).mul ((isLoopPolyMat_slash' hy).mul ((isLoopPolyMat_slash' hy).mul
      (isLoopPolyMat_slash' hy))))))).trace.const_mul (-(d₂ : ℂ))
  exact h.mono (by norm_num)

theorem isLoopPoly_insT2' (hx : IsLoopAffine x) (hy : IsLoopAffine y) (d₂ dm : ℝ) :
    IsLoopPoly L 2 fun ℓ => insT2 A B d₂ dm (x ℓ) (y ℓ) := by
  have h1 := (((IsLoopPolyMat.const A).mul ((IsLoopPolyMat.const B).mul
    ((isLoopPolyMat_slash' hy).mul (isLoopPolyMat_slash' hy))))).trace.const_mul
      ((dm : ℂ) - 2 * d₂)
  have h2 := (((IsLoopPolyMat.const A).mul ((isLoopPolyMat_slash' hx).mul
    ((IsLoopPolyMat.const B).mul (isLoopPolyMat_slash' hy))))).trace.const_mul
      (2 * (dm : ℂ) - d₂)
  exact (h1.mono (by norm_num)).add (h2.mono (by norm_num))

theorem isLoopPoly_nT0 (hx : IsLoopAffine x) (hy : IsLoopAffine y) (d₂ dm : ℝ) :
    IsLoopPoly L 4 fun ℓ => nT0 A B d₂ dm (x ℓ) (y ℓ) := by
  have hV := hy.isLoopPoly_propDenom 0 0
  have h4 : IsLoopPoly L 0 fun _ => insT4 A B dm := IsLoopPoly.const _
  refine ((isLoopPoly_insT0' hx hy d₂).sub ((hV.mul (isLoopPoly_insT2' hx hy d₂ dm)).mono
    (by norm_num))).add ?_
  have := ((hV.mul hV).mul h4).mono (n' := 4) (by norm_num)
  refine (congrArg (IsLoopPoly L 4) (funext fun ℓ => ?_)).mp this
  simp only [v0]
  ring

theorem isLoopPoly_nT1 (hx : IsLoopAffine x) (hy : IsLoopAffine y) (d₂ dm : ℝ) :
    IsLoopPoly L 2 fun ℓ => nT1 A B d₂ dm (x ℓ) (y ℓ) := by
  have hV := hy.isLoopPoly_propDenom 0 0
  have h4 : IsLoopPoly L 0 fun _ => insT4 A B dm := IsLoopPoly.const _
  exact (isLoopPoly_insT2' hx hy d₂ dm).sub
    ((((IsLoopPoly.const (n := 0) (2 : ℂ)).mul hV).mul h4).mono (by norm_num))

end Poly

theorem isLoopAffine_zk' (k : Fin 4 → ℝ) (c : Bool) :
    IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => zk k c (ℓ 0) := isLoopAffine_zk k c

theorem isLoopPoly_tn (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 2 (![4, 2, 0] j) fun ℓ => tn j d₂ dm bx bY k (ℓ 0) μ ν := by
  match j with
  | 0 => exact isLoopPoly_nT0 (isLoopAffine_zk k bx) (isLoopAffine_zk k bY) d₂ dm
  | 1 => exact isLoopPoly_nT1 (isLoopAffine_zk k bx) (isLoopAffine_zk k bY) d₂ dm
  | 2 => exact IsLoopPoly.const _

theorem isLoopPoly_tn_k (j : Fin 3) (d₂ dm : ℝ) (bx bY : Bool) (q : Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 1 4 fun y => tn j d₂ dm bx bY (y 0) q μ ν := by
  match j with
  | 0 => exact isLoopPoly_nT0 (isLoopAffine_zk_one q bx) (isLoopAffine_zk_one q bY) d₂ dm
  | 1 => exact (isLoopPoly_nT1 (isLoopAffine_zk_one q bx) (isLoopAffine_zk_one q bY) d₂
      dm).mono (by norm_num)
  | 2 => exact IsLoopPoly.const _

end QED.GradedProof.VP2

end
