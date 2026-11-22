/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNVA

/-!
# Set (a), stage B3: the nested one-loop form of the class `VC`

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3. The class `VC`
(self-energy on `k + ℓ₀`) has the two equal lines `k + ℓ₀`; merged, its four lines are
`k + ℓ₀` (weight `z₀`), `ℓ₁` (the inner fermion), `ℓ₀`, `ℓ₀ - ℓ₁ + k` (the photon): the rows
`ksNBaseA` of `VA` with the shifts `ksNppC = (k, 0, 0, k)`. At the Cheng–Wu slice
`z = (a, x, b, 1 - x)` the loop shift is `-((σ - 1)k, ξσk)` (`σ = b/U`), and the moments of the
`(2, 3)` entry `ksNTC` there are again `k²k³ a₀(σ)` and `4 k²k³ a₁(σ)/U`, with the same `V`. So
the merged integrand at the slice is the outer `VA` integrand `ksNGA` *pointwise*, and:

* **`ksN_nest_VC`**, **`ksN_vDens_VC`**: `vDens(VC)₂₃ = -π⁴ ∫₀¹ x⁻¹ ∫_{Δ₂} ksNGAsum x dx`, the same
  nested form as `VA` (`ksN_vDens_VA`).
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.GradedProof.RPi4 QED.GradedProof.VP2
open QED.TwoLoop.PauliZeroExplicit.NumeratorCongr
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.GradedProof.WI2 (dbl ehat)
open QED.Integration.SimplexMerge (integral_simplex_splitAt splitAt)

/-! ### The moments of the `VC` entry -/

/-- The quadratic coefficient of `ksNTC` along the direction `(d₀, d₁)`. -/
noncomputable def ksNT2C (m : ℝ) (P Q k d₀ d₁ : Fin 4 → ℝ) : ℝ :=
  -16 * ((2 * m ^ 2 + Minkowski.dot (k + P) Q) * (2 * d₀ 2 * d₀ 3) + (Minkowski.dot d₀ Q +
  Minkowski.dot (k + P) d₁) * (d₀ 2 * (k + P) 3 + P 2 * d₀ 3 + d₀ 2 * P 3 + (k + P) 2 * d₀ 3) +
  Minkowski.dot d₀ d₁ * (P 2 * (k + P) 3 + (k + P) 2 * P 3)) + 8 * ((m ^ 2 + Minkowski.dot (k + P)
  (k + P)) * (d₀ 2 * d₁ 3 + d₁ 2 * d₀ 3) + (2 * Minkowski.dot (k + P) d₀) * (d₀ 2 * Q 3 + P 2 * d₁ 3
  + d₁ 2 * P 3 + Q 2 * d₀ 3) + Minkowski.dot d₀ d₀ * (P 2 * Q 3 + Q 2 * P 3))

/-- **`ksNTC` along a line** is a quartic polynomial in `t`. -/
theorem ksN_ksNTC_line (m : ℝ) (P Q k d₀ d₁ : Fin 4 → ℝ) :
    ∃ c₁ c₃ c₄ : ℝ, ∀ t : ℝ, ksNTC m (P + t • d₀) (Q + t • d₁) k =
      ksNTC m P Q k + c₁ * t + ksNT2C m P Q k d₀ d₁ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 := by
  refine ⟨
    -16 * ((2 * m ^ 2 + Minkowski.dot (k + P) Q) * (d₀ 2 * (k + P) 3 + P 2 * d₀ 3 + d₀ 2 * P 3 + (k
    + P) 2 * d₀ 3) + (Minkowski.dot d₀ Q + Minkowski.dot (k + P) d₁) * (P 2 * (k + P) 3 + (k + P) 2
    * P 3)) + 8 * ((m ^ 2 + Minkowski.dot (k + P) (k + P)) * (d₀ 2 * Q 3 + P 2 * d₁ 3 + d₁ 2 * P 3 +
    Q 2 * d₀ 3) + (2 * Minkowski.dot (k + P) d₀) * (P 2 * Q 3 + Q 2 * P 3)),
    -16 * ((Minkowski.dot d₀ Q + Minkowski.dot (k + P) d₁) * (2 * d₀ 2 * d₀ 3) + Minkowski.dot d₀ d₁
    * (d₀ 2 * (k + P) 3 + P 2 * d₀ 3 + d₀ 2 * P 3 + (k + P) 2 * d₀ 3)) + 8 * ((2 * Minkowski.dot (k
    + P) d₀) * (d₀ 2 * d₁ 3 + d₁ 2 * d₀ 3) + Minkowski.dot d₀ d₀ * (d₀ 2 * Q 3 + P 2 * d₁ 3 + d₁ 2 *
    P 3 + Q 2 * d₀ 3)),
    -16 * (Minkowski.dot d₀ d₁ * (2 * d₀ 2 * d₀ 3)) + 8 * (Minkowski.dot d₀ d₀ * (d₀ 2 * d₁ 3 + d₁ 2
    * d₀ 3)), fun t => ?_⟩
  have hkP : k + (P + t • d₀) = (k + P) + t • d₀ := by abel
  have hPQ := ksN_dot_line (k + P) d₀ Q d₁ t
  have hPP := ksN_dot_line (k + P) d₀ (k + P) d₀ t
  have hd : Minkowski.dot d₀ (k + P) = Minkowski.dot (k + P) d₀ := ksN_dot_comm (k + P) d₀
  simp only [ksNTC, ksNT2C, hkP, hPQ, hPP, hd]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The quadratic form of a `VC` numerator along a direction.** -/
theorem ksN_hessForm_VC {Q : LoopQuartic} {K : ℂ} {m : ℝ} {k : Fin 4 → ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTC m (ℓ 0) (ℓ 1) k : ℂ)) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q ℓ δ = K * (ksNT2C m (ℓ 0) (ℓ 1) k (δ 0) (δ 1) : ℂ) := by
  obtain ⟨c₁, c₃, c₄, h⟩ := ksN_ksNTC_line m (ℓ 0) (ℓ 1) k (δ 0) (δ 1)
  refine ksN_hessForm_of_poly Q ℓ δ (K * (ksNTC m (ℓ 0) (ℓ 1) k : ℂ)) (K * c₁) _ (K * c₃)
    (K * c₄) fun t => ?_
  rw [hQ]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [h t]
  push_cast
  ring

/-- **The moment `a₀` of the `VC` entry**: its value at the loop shift. -/
theorem ksN_ksNTC_shift (m σ ξ : ℝ) (k : Fin 4 → ℝ) :
    ksNTC m ((σ - 1) • k) ((ξ * σ) • k) k =
      k 2 * k 3 * (16 * σ * (1 - σ) * (4 * m ^ 2 - ξ * m ^ 2 + ξ * σ ^ 2 * Minkowski.dot k k)) := by
  have h : k + (σ - 1) • k = σ • k := by
    funext μ; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [ksNTC, h, ksN_dot_smul_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The moment `a₁` of the `VC` entry**: the Gaussian contraction at the loop shift, for
`A⁻¹ = U⁻¹ [[1, ξ], [ξ, c]]`. -/
theorem ksN_contractTwo_ksNTC {Q : LoopQuartic} {K : ℂ} {m : ℝ} {k : Fin 4 → ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTC m (ℓ 0) (ℓ 1) k : ℂ)) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.transpose = A) {U c σ ξ : ℝ} (h00 : A⁻¹ 0 0 = U⁻¹) (h01 : A⁻¹ 0 1 = ξ * U⁻¹)
    (h11 : A⁻¹ 1 1 = c * U⁻¹) :
    Q.contractTwo A (loopComp ![(σ - 1) • k, (ξ * σ) • k]) =
      K * ((4 * k 2 * k 3 * (-8 * ξ * σ * (4 * σ - 3)) * U⁻¹ : ℝ) : ℂ) := by
  rw [ksN_contractTwo_eq Q hA]
  simp only [ksN_hessForm_VC hQ, h00, h01, h11]
  simp only [ksNT2C, ksNE, Fin.sum_univ_four, Minkowski.dot, Minkowski.metric,
    Pi.add_apply, Pi.single_apply]
  simp
  ring

/-! ### The merged `VC` data at the slice -/

/-- The line shifts of the merged `VC` data: `k` on the merged line and the photon. -/
def ksNppC (k : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ := ![k, 0, 0, k]

section Slice

variable (k : Fin 4 → ℝ) (z : Fin 4 → ℝ)

theorem ksN_loopShift_C :
    loopShift (castLoopMatrix ksNBaseA) (ksNppC k) z =
      ![((symanzikU (castLoopMatrix ksNBaseA) z)⁻¹ * ((z 1 + z 3) * (z 0 + z 3) - z 3 ^ 2)) • k,
        ((symanzikU (castLoopMatrix ksNBaseA) z)⁻¹ * (-(z 2 * z 3))) • k] := by
  funext s μ
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply, ksN_inv_A]
  fin_cases s <;>
    simp [Fin.sum_univ_two, Fin.sum_univ_four, castLoopMatrix, ksNBaseA, ksNppC] <;> ring

theorem ksN_symanzikV_C (M : ℝ) :
    symanzikV (castLoopMatrix ksNBaseA) (ksNppC k) (ksNMA M) z =
      (z 0 + z 1 + z 2) * M ^ 2 + (z 0 + z 3) * Minkowski.dot k k -
        (symanzikU (castLoopMatrix ksNBaseA) z)⁻¹ * ((z 1 + z 3) * (z 0 + z 3) ^ 2 -
          2 * z 3 ^ 2 * (z 0 + z 3) + (z 0 + z 2 + z 3) * z 3 ^ 2) * Minkowski.dot k k := by
  have hB : symanzikVector (castLoopMatrix ksNBaseA) (ksNppC k) z =
      ![(z 0 + z 3) • k, (-z 3) • k] := by
    funext s μ
    fin_cases s
    · simp [symanzikVector, Fin.sum_univ_four, castLoopMatrix, ksNBaseA, ksNppC]
      ring
    · simp [symanzikVector, Fin.sum_univ_four, castLoopMatrix, ksNBaseA, ksNppC]
  rw [symanzikV, hB, ksN_inv_A]
  simp [Fin.sum_univ_two, Fin.sum_univ_four, ksNMA, ksNppC, Minkowski.dot]
  ring

/-- **The merged `VC` integrand at the Cheng–Wu slice** is the outer `VA` integrand. -/
theorem ksN_slice_VC {Q : LoopQuartic} {K : ℂ} {M : ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTC M (ℓ 0) (ℓ 1) k : ℂ))
    (hC4 : ∀ A, Q.contractFour A = 0) (u : ℝ) {x a b : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hb : 0 < b) :
    (a : ℂ) * pieceF 5 Q (castLoopMatrix ksNBaseA) (ksNppC k) (ksNMA M) 3 u ![a, x, b, 1 - x] =
      ((1 - x : ℝ) : ℂ) * (K * (ksNGA M u x k ![a, b, x * (1 - x)] : ℂ)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hξ : 0 < 1 - x := by linarith
  set z : Fin 4 → ℝ := ![a, x, b, 1 - x] with hz
  set U := a + b + x * (1 - x) with hUdef
  have hU0 : 0 < U := by positivity
  have hU : symanzikU (castLoopMatrix ksNBaseA) z = U := by
    rw [ksN_symanzikU_A]
    simp [hz, hUdef]
    ring
  have hinv := ksN_inv_A z
  rw [hU] at hinv
  have h00 : (symanzikMatrix (castLoopMatrix ksNBaseA) z)⁻¹ 0 0 = U⁻¹ := by
    rw [hinv]; simp [hz]
  have h01 : (symanzikMatrix (castLoopMatrix ksNBaseA) z)⁻¹ 0 1 = (1 - x) * U⁻¹ := by
    rw [hinv]; simp [hz]; ring
  have h11 : (symanzikMatrix (castLoopMatrix ksNBaseA) z)⁻¹ 1 1 = (a + b + (1 - x)) * U⁻¹ := by
    rw [hinv]; simp [hz]; ring
  set σ := U⁻¹ * b with hσ
  have z0 : z 0 = a := rfl
  have z1 : z 1 = x := rfl
  have z2 : z 2 = b := rfl
  have z3 : z 3 = 1 - x := rfl
  have hS : -loopShift (castLoopMatrix ksNBaseA) (ksNppC k) z =
      ![(σ - 1) • k, ((1 - x) * σ) • k] := by
    rw [ksN_loopShift_C, hU, z0, z1, z2, z3]
    funext s μ
    fin_cases s
    · simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hσ, hUdef]
      field_simp
      ring
    · simp only [Pi.neg_apply, Fin.mk_one, Matrix.cons_val_one]
      simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
      rw [hσ]
      ring
  have hE : Q.evalC (loopComp (-loopShift (castLoopMatrix ksNBaseA) (ksNppC k) z)) =
      K * ((k 2 * k 3 * (16 * σ * (1 - σ) * (4 * M ^ 2 - (1 - x) * M ^ 2 +
        (1 - x) * σ ^ 2 * Minkowski.dot k k)) : ℝ) : ℂ) := by
    rw [hS]
    have := congrFun hQ ![(σ - 1) • k, ((1 - x) * σ) • k]
    simp only [LoopQuartic.eval] at this
    rw [this]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ksN_ksNTC_shift]
  have hC : Q.contractTwo (symanzikMatrix (castLoopMatrix ksNBaseA) z)
      (loopComp (-loopShift (castLoopMatrix ksNBaseA) (ksNppC k) z)) =
      K * ((4 * k 2 * k 3 * (-8 * (1 - x) * σ * (4 * σ - 3)) * U⁻¹ : ℝ) : ℂ) := by
    rw [hS]
    exact ksN_contractTwo_ksNTC hQ (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose _ _)
      h00 h01 h11
  set W := (a + x + b) * M ^ 2 + b * Minkowski.dot k k -
    U⁻¹ * (x + (1 - x)) * b ^ 2 * Minkowski.dot k k + (1 - x) * u with hW
  have hV : symanzikV (castLoopMatrix ksNBaseA) (ksNppC k) (ksNMA M) z + (1 - x) * u = W := by
    rw [ksN_symanzikV_C, hU, z0, z1, z2, z3, hW]
    have hU' : U ≠ 0 := hU0.ne'
    field_simp
    rw [hUdef]
    ring
  have hG : ksNGA M u x k ![a, b, x * (1 - x)] = k 2 * k 3 * a *
      ((U ^ 2)⁻¹ * (16 * σ * (1 - σ) * (4 * M ^ 2 - (1 - x) * M ^ 2 +
        (1 - x) * σ ^ 2 * Minkowski.dot k k)) / W ^ 2 +
       2 * (U ^ 3)⁻¹ * (-8 * (1 - x) * σ * (4 * σ - 3)) / W) := by
    have hbU : b / (a + b + x * (1 - x)) = σ := by rw [hσ, ← hUdef, div_eq_inv_mul]
    have hD : b * (a + x * (1 - x)) * Minkowski.dot k k / (a + b + x * (1 - x)) +
        (a + b) * M ^ 2 + x * (1 - x) * (M ^ 2 / (1 - x) + u / x) = W := by
      rw [hW, ← hUdef]
      field_simp
      ring
    simp only [ksNGA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ← hUdef] at hbU hD ⊢
    rw [hbU, hD]
  rw [hG]
  simp only [pieceF, paramAtV, ehat, hE, hC, hC4, hU, hV, z3]
  simp only [show (5 - 4).factorial = 1 from rfl, show (5 - 5).factorial = 1 from rfl,
    show 5 - 3 = 2 from rfl, show 5 - 4 = 1 from rfl,
    show 5 - 5 = 0 from rfl]
  by_cases hW0 : W = 0
  · simp [hW0]
  · have hU' : (U : ℂ) ≠ 0 := ofReal_ne_zero.2 hU0.ne'
    have hW' : (W : ℂ) ≠ 0 := ofReal_ne_zero.2 hW0
    push_cast
    field_simp
    ring

end Slice

/-! ### The merge and the nested form -/

/-- The relabelling of the five `VC` lines: `k + ℓ₀, ℓ₁, ℓ₀, photon, k + ℓ₀`. -/
def ksNPermC : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 4

theorem ksN_permC_base :
    (fun l => castLoopMatrix baseVC (ksNPermC l)) = dbl 0 (castLoopMatrix ksNBaseA) := by
  funext l
  fin_cases l <;> rfl

theorem ksN_permC_pp (k : Fin 4 → ℝ) :
    (fun l => (fun l => cVC l • k) (ksNPermC l)) = dbl 0 (ksNppC k) := by
  funext l
  fin_cases l <;> simp [ksNPermC, cVC, ksNppC, dbl, Equiv.swap_apply_def]

theorem ksN_permC_M (M : ℝ) :
    (fun l => ksBM5 (fun _ => M) (ksNPermC l)) = Fin.snoc (ksNMA M) M := by
  funext l
  fin_cases l <;> rfl

theorem ksN_permC_last : ksNPermC (3 : Fin 4).castSucc = Fin.last 4 := by decide

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
  (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k)
  {u : ℝ} (hu : 0 < u)

theorem ksN_eval_VC (M : ℝ) :
    (ksBRep e aVC baseVC cVC M k).eval =
      fun ℓ => faceIdKV e 0 1 * (ksNTC M (ℓ 0) (ℓ 1) k : ℂ) := by
  rw [ksBRep_eval]
  funext ℓ
  exact ksN_vNum_VC e M k ℓ

include hPV₁ hPV₂ hm₀ hmass hk hu

/-- **The nested form of `VC`**: the same outer integrand as `VA`. -/
theorem ksN_nest_VC :
    IntegrableOn (fun x => x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y))
      (Ioo (0 : ℝ) 1) ∧
    ∫ y in simplexSet 4, ∑ f, (Φ.coeff f : ℂ) * ksBAtom baseVC cVC k
      (ksBRep e aVC baseVC cVC (Φ.mass f) k) u (simplexPoint y) (fun _ => Φ.mass f) =
    ∫ x in Ioo (0 : ℝ) 1, x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y) := by
  obtain ⟨hI5, -⟩ := ksB_vDens_VC Φ hPV₁ hPV₂ hm₀ hmass e hk hu
  set Qf := fun f => ksBRep e aVC baseVC cVC (Φ.mass f) k
  have hperm := ksB_integral_pieceF_perm Finset.univ ksNPermC 5 Qf (castLoopMatrix baseVC)
    (fun l => cVC l • k) (fun f => (Φ.coeff f : ℂ)) (fun f => ksBM5 fun _ => Φ.mass f)
    (3 : Fin 4).castSucc u
  rw [ksN_permC_last, ksN_permC_base, ksN_permC_pp] at hperm
  simp only [ksN_permC_M] at hperm
  simp only [ksBAtom] at hI5 ⊢
  rw [← hperm.1] at hI5
  rw [← hperm.2]
  set F3 : (Fin 4 → ℝ) → ℂ := fun z => ∑ f, (Φ.coeff f : ℂ) *
    ((z 0 : ℂ) * pieceF 5 (Qf f) (castLoopMatrix ksNBaseA) (ksNppC k) (ksNMA (Φ.mass f)) 3 u z)
    with hF3
  have hsplit : ∀ (z : Fin 4 → ℝ) (t : ℝ), (∑ f, (Φ.coeff f : ℂ) * pieceF 5 (Qf f)
      (dbl 0 (castLoopMatrix ksNBaseA)) (dbl 0 (ksNppC k)) (Fin.snoc (ksNMA (Φ.mass f))
        (Φ.mass f)) (3 : Fin 4).castSucc u (splitAt 0 z t)) = ∑ f, (Φ.coeff f : ℂ) *
      pieceF 5 (Qf f) (castLoopMatrix ksNBaseA) (ksNppC k) (ksNMA (Φ.mass f)) 3 u z :=
    fun z t => Finset.sum_congr rfl fun f _ =>
      congrArg _ (ksN_pieceF_merge (Qf f) (by decide) _ _ (ksNMA (Φ.mass f)) u z t)
  obtain ⟨hI4, hE4⟩ := integral_simplex_splitAt (m := 3) (by norm_num) (0 : Fin 4)
    (f := fun z : Fin 5 → ℝ => ∑ f, (Φ.coeff f : ℂ) * pieceF 5 (Qf f)
      (dbl 0 (castLoopMatrix ksNBaseA)) (dbl 0 (ksNppC k)) (Fin.snoc (ksNMA (Φ.mass f))
        (Φ.mass f)) (3 : Fin 4).castSucc u z) hI5
  simp only [hsplit, intervalIntegral.integral_const, sub_zero] at hI4 hE4
  have hF3eq : ∀ z : Fin 4 → ℝ, z 0 • (∑ f, (Φ.coeff f : ℂ) * pieceF 5 (Qf f)
      (castLoopMatrix ksNBaseA) (ksNppC k) (ksNMA (Φ.mass f)) 3 u z) = F3 z := by
    intro z
    rw [hF3, Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp only [hF3eq] at hI4 hE4
  rw [hE4]
  refine ksN_nest (F := F3) ?_ hI4 (ksNGAsum Φ e u k) ?_ ?_
  · intro z hz t ht
    rw [hF3, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ksN_pieceF_smul (ht := ht.ne'), Pi.smul_apply, smul_eq_mul]
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    push_cast
    field_simp
  · intro x _ z hz t ht
    simp only [ksNGAsum, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ksN_ksNGA_smul _ _ _ _ _ hz ht]
    push_cast
    ring
  · intro x hx v hv
    rw [ksN_vec_four, ksN_vec_three, hF3]
    simp only [ksNGAsum, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have h := ksN_slice_VC k (ksN_eval_VC e (Φ.mass f)) (ksBRep_contractFour e aVC baseVC cVC
      ksB_flip_VC (Φ.mass f) k) u hx (hv 0) (hv 1)
    simp only [Matrix.cons_val_zero]
    rw [h]
    ring

/-- **`VC` at the entry `(2, 3)` in nested one-loop form** (the same as `VA`). -/
theorem ksN_vDens_VC :
    IntegrableOn (fun x => x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y))
      (Ioo (0 : ℝ) 1) ∧
    vDens aVC baseVC cVC Φ e m₀ u k 2 3 = -((π : ℂ) ^ 4) *
      ∫ x in Ioo (0 : ℝ) 1, x⁻¹ • ∫ y in simplexSet 2, ksNGAsum Φ e u k x (simplexPoint y) := by
  obtain ⟨h1, h2⟩ := ksN_nest_VC Φ hPV₁ hPV₂ hm₀ hmass e hk hu
  exact ⟨h1, by rw [(ksB_vDens_VC Φ hPV₁ hPV₂ hm₀ hmass e hk hu).2, h2]⟩

end Classes

end QED.ChainProof.SetAKS

end
