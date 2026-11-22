/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecTens
public import QED.GradedProof.VP2VGen
public import QED.TwoLoop.PauliZeroExplicitQuartic
public import QED.TwoLoop.LoopPolySubst

/-!
# Set (a): the parametric coefficients of a piece are covariant polynomials in `k`

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`,
the tensor form at fixed `ε`. For a two-loop numerator tensor `N_k(ℓ)^{μν}` and line momenta
`cᵢ k`, the three coefficients `T₁, T₂, T₃` of the parametric integrand
(`QED.TwoLoop.ClassLimit.coeffOne`, …), computed from the canonical quartic of each entry
(`QED.TwoLoop.PauliZeroExplicit.numQuartic`), are at each Feynman point `x`:

* **covariant** under every reflection (`saT1_cov`, `saT2_cov`, `saT3_cov`), when `N` is
  (`QED.GradedProof.VP2.TCov2`): the loop shift moves with the reflection
  (`QED.TwoLoop.ReflCovariance.loopShift_map`), the contractions with `G = g ⊗ A⁻¹` are invariant;
* **polynomials of degree `≤ 4` in `k`** (`saT1_poly`, …), when `N` is along every affine line
  `ℓ = λ k + δ` (`SAPolyK`). The contractions are written through values of the numerator
  function: the Hessian form from the even part at `δ`, `2δ` (`saHf_eq`), its contraction with a
  symmetric matrix by polarization (`saPolar`, `saCt2_eq`), and the pairing contraction through
  the Hessian contraction at `±y`, `0` (`saCt4_eq`).

With `QED.ChainProof.SetASpec.SACov.eq_gk` each coefficient is then `X(k²) g + Y(k²) k k`.
-/

@[expose] public section

open Complex Matrix
open QED.Dirac

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.LimitCovariance QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)
open QED.TwoLoop.PauliZeroExplicit.NumeratorCongr (hessForm ofIndex loopComp_ofIndex
  contractTwo_congr hessForm_two_smul quartPart_two_smul two_mul_contractFour
  hess_add_hess_neg sum_comm4)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.GradedProof.VP2 (TCov2 rAct rAct_mul)
open QED.Integration.Feynman (simplexPoint)

/-! ### The contractions through values of the numerator function -/

/-- The unit vector of the loop index `a`. -/
noncomputable def saEI (a : LoopIndex) : LoopIndex → ℝ := Pi.single a 1

/-- The quadratic form of a matrix `K` at a real vector. -/
noncomputable def saQf (K : LoopIndex → LoopIndex → ℂ) (y : LoopIndex → ℝ) : ℂ :=
  ∑ c, ∑ d, K c d * (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ))

theorem saQf_polar (K : LoopIndex → LoopIndex → ℂ) (a b : LoopIndex) :
    saQf K (saEI a + saEI b) - saQf K (saEI a) - saQf K (saEI b) = K a b + K b a := by
  have e : ∀ y y' : LoopIndex → ℝ, saQf K (y + y') - saQf K y - saQf K y' =
      ∑ c, ∑ d, K c d * (((y c : ℝ) : ℂ) * ((y' d : ℝ) : ℂ)) +
        ∑ c, ∑ d, K c d * (((y' c : ℝ) : ℂ) * ((y d : ℝ) : ℂ)) := by
    intro y y'
    simp only [saQf, Pi.add_apply, ofReal_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [e]
  simp [saEI, Pi.single_apply, apply_ite (fun r : ℝ => (r : ℂ)), mul_ite,
    Finset.sum_ite_eq']

/-- **Polarization**: a contraction with a symmetric real matrix through the quadratic form. -/
theorem saPolar (K : LoopIndex → LoopIndex → ℂ) (G : Matrix LoopIndex LoopIndex ℝ)
    (hG : ∀ a b, G a b = G b a) :
    ∑ a, ∑ b, K a b * (G a b : ℂ) = ∑ a, ∑ b, (G a b : ℂ) / 2 *
      (saQf K (saEI a + saEI b) - saQf K (saEI a) - saQf K (saEI b)) := by
  simp only [saQf_polar]
  have hs : ∑ a, ∑ b, K b a * (G a b : ℂ) = ∑ a, ∑ b, K a b * (G a b : ℂ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hG]
  have h2 : ∑ a, ∑ b, (G a b : ℂ) / 2 * (K a b + K b a) =
      (∑ a, ∑ b, K a b * (G a b : ℂ) + ∑ a, ∑ b, K b a * (G a b : ℂ)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h2, hs]
  ring

/-- The Hessian form from values: `(8 E(δ) - E(2δ)/2 - 15 F(ℓ))/12`,
`E(δ) = F(ℓ + δ) + F(ℓ - δ)`. -/
noncomputable def saHf (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (ℓ δ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (8 * (F (ℓ + δ) + F (ℓ - δ)) - (F (ℓ + (2 : ℝ) • δ) + F (ℓ - (2 : ℝ) • δ)) / 2 -
    15 * F ℓ) / 12

theorem saHf_eq (Q : LoopQuartic) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    saHf Q.eval ℓ δ = hessForm Q ℓ δ := by
  have e1 : Q.eval (ℓ + δ) + Q.eval (ℓ - δ) =
      2 * (Q.eval ℓ + hessForm Q ℓ δ + Q.quartPart (loopComp δ)) := Q.eval_add_add_eval_sub ℓ δ
  have e2 : Q.eval (ℓ + (2 : ℝ) • δ) + Q.eval (ℓ - (2 : ℝ) • δ) =
      2 * (Q.eval ℓ + hessForm Q ℓ ((2 : ℝ) • δ) + Q.quartPart (loopComp ((2 : ℝ) • δ))) :=
    Q.eval_add_add_eval_sub ℓ _
  rw [hessForm_two_smul, quartPart_two_smul] at e2
  unfold saHf
  linear_combination (8 * e1 - e2 / 2) / 12

/-- **The Hessian contraction through values of the numerator function.** -/
theorem saCt2_eq (Q : LoopQuartic) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    Q.contractTwo A (loopComp ℓ) = ∑ a, ∑ b, (loopMetricInv A a b : ℂ) / 2 *
      (saHf Q.eval ℓ (ofIndex (saEI a + saEI b)) - saHf Q.eval ℓ (ofIndex (saEI a)) -
        saHf Q.eval ℓ (ofIndex (saEI b))) := by
  have hq : ∀ y, saHf Q.eval ℓ (ofIndex y) = saQf (Q.hess (loopComp ℓ)) y := fun y => by
    rw [saHf_eq]
    simp only [hessForm, loopComp_ofIndex, saQf]
  simp only [hq]
  exact saPolar _ _ (QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.loopMetricInv_symm hA)

/-- The pairing form at `y` through the Hessian contraction at `±y` and `0`. -/
theorem saCt4_key (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) (y : LoopIndex → ℝ) :
    2 * saQf (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ)) y =
      Q.contractTwo A (loopComp (ofIndex y)) + Q.contractTwo A (loopComp (-ofIndex y)) -
        2 * Q.contractTwo A (loopComp 0) := by
  have hneg : loopComp (-ofIndex y) = -loopComp (ofIndex y) := by
    funext a
    simp [loopComp]
  have h0 : loopComp (0 : Fin 2 → Fin 4 → ℝ) = 0 := by
    funext a
    simp [loopComp]
  rw [hneg, h0]
  simp only [LoopQuartic.contractTwo, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, saQf]
  have e : ∀ a b, Q.hess (loopComp (ofIndex y)) a b * ((loopMetricInv A a b : ℝ) : ℂ) +
      Q.hess (-loopComp (ofIndex y)) a b * ((loopMetricInv A a b : ℝ) : ℂ) -
      2 * (Q.hess 0 a b * ((loopMetricInv A a b : ℝ) : ℂ)) =
      ∑ c, ∑ d, 2 * (Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ) *
        (((y c : ℝ) : ℂ) * ((y d : ℝ) : ℂ))) := fun a b => by
    have := hess_add_hess_neg (Q := Q) (loopComp (ofIndex y)) a b
    simp only [loopComp_ofIndex] at this ⊢
    rw [← add_mul, ← mul_assoc, ← sub_mul, this, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [e]
  rw [← sum_comm4]
  simp only [Finset.mul_sum, Finset.sum_mul]

/-- The pairing form through values: `(ct(y) + ct(-y) - 2 ct(0))/2`. -/
noncomputable def saQ4 (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) (y : LoopIndex → ℝ) :
    ℂ :=
  (Q.contractTwo A (loopComp (ofIndex y)) + Q.contractTwo A (loopComp (-ofIndex y)) -
    2 * Q.contractTwo A (loopComp 0)) / 2

/-- **The pairing contraction through the Hessian contraction.** -/
theorem saCt4_eq (Q : LoopQuartic) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A) :
    Q.contractFour A = ∑ c, ∑ d, (loopMetricInv A c d : ℂ) / 4 *
      (saQ4 Q A (saEI c + saEI d) - saQ4 Q A (saEI c) - saQ4 Q A (saEI d)) := by
  have hq : ∀ y, saQ4 Q A y =
      saQf (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ)) y :=
    fun y => by rw [saQ4, ← saCt4_key]; ring
  have h := saPolar (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ))
    _ (QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.loopMetricInv_symm hA)
  have e := two_mul_contractFour (Q := Q) A
  simp only [hq]
  have h2 : ∑ c, ∑ d, (loopMetricInv A c d : ℂ) / 4 *
      (saQf (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ))
        (saEI c + saEI d) -
      saQf (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ))
        (saEI c) -
      saQf (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ))
        (saEI d)) =
      (∑ c, ∑ d, (loopMetricInv A c d : ℂ) / 2 *
      (saQf (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ))
        (saEI c + saEI d) -
      saQf (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ))
        (saEI c) -
      saQf (fun c d => ∑ a, ∑ b, Q.quartSym a b c d * ((loopMetricInv A a b : ℝ) : ℂ))
        (saEI d))) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [h2, ← h]
  linear_combination e / 2

/-! ### Covariance of the coefficients -/

section Cov

variable {L : Matrix (Fin 4) (Fin 4) ℝ}

/-- A quartic `Q'` whose values along `L ℓ` are a combination of the values of `Q α β`: so are
its two contractions. -/
theorem saContractTwo_map
    (hL : ∀ μ ν, ∑ a, ∑ b, L μ a * L ν b * Minkowski.metric a b = Minkowski.metric μ ν)
    {Q' : LoopQuartic} {Q : Fin 4 → Fin 4 → LoopQuartic} {w : Fin 4 → Fin 4 → ℂ}
    (h : ∀ ℓ, Q'.eval (loopAct L ℓ) = ∑ α, ∑ β, w α β * (Q α β).eval ℓ)
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Q'.contractTwo A (loopComp (loopAct L ℓ)) =
      ∑ α, ∑ β, w α β * (Q α β).contractTwo A (loopComp ℓ) := by
  set Qs := qsum Finset.univ (fun p : Fin 4 × Fin 4 => w p.1 p.2) (fun p => Q p.1 p.2)
  have he : (lmap (blockL L) Q').eval = Qs.eval := by
    funext ℓ'
    rw [eval_lmap_blockL, h, eval_qsum, Fintype.sum_prod_type]
  have h1 : (lmap (blockL L) Q').contractTwo A (loopComp ℓ) =
      Q'.contractTwo A (loopComp (loopAct L ℓ)) := by
    rw [contractTwo_lmap _ _ hA, actC_blockL_loopComp, blockL_conj_loopMetricInv hL]
    rfl
  rw [← h1, contractTwo_congr he hA, contractTwo_qsum, Fintype.sum_prod_type]

theorem saContractFour_map
    (hL : ∀ μ ν, ∑ a, ∑ b, L μ a * L ν b * Minkowski.metric a b = Minkowski.metric μ ν)
    {Q' : LoopQuartic} {Q : Fin 4 → Fin 4 → LoopQuartic} {w : Fin 4 → Fin 4 → ℂ}
    (h : ∀ ℓ, Q'.eval (loopAct L ℓ) = ∑ α, ∑ β, w α β * (Q α β).eval ℓ)
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A) :
    Q'.contractFour A = ∑ α, ∑ β, w α β * (Q α β).contractFour A := by
  set Qs := qsum Finset.univ (fun p : Fin 4 × Fin 4 => w p.1 p.2) (fun p => Q p.1 p.2)
  have he : (lmap (blockL L) Q').eval = Qs.eval := by
    funext ℓ'
    rw [eval_lmap_blockL, h, eval_qsum, Fintype.sum_prod_type]
  have h1 : (lmap (blockL L) Q').contractFour A = Q'.contractFour A := by
    rw [contractFour_lmap, blockL_conj_loopMetricInv hL]
    rfl
  rw [← h1, QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractFour_congr he hA,
    contractFour_qsum, Fintype.sum_prod_type]

end Cov

variable {m : ℕ} (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (α : Fin (m + 1) → Fin 2 → ℝ) (c : Fin (m + 1) → ℝ)

/-- The canonical quartic of the entry `(μ, ν)` of the numerator at `k`. -/
noncomputable def saQ (k : Fin 4 → ℝ) (μ ν : Fin 4) : LoopQuartic :=
  numQuartic fun ℓ => N k ℓ μ ν

/-- **The coefficient tensor `T₁(x, k)`.** -/
noncomputable def saT1 (x : Fin m → ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  coeffOne (saQ N k μ ν) α (fun i => c i • k) x

/-- **The coefficient tensor `T₂(x, k)`.** -/
noncomputable def saT2 (x : Fin m → ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  coeffTwo (saQ N k μ ν) α (fun i => c i • k) x

/-- **The coefficient tensor `T₃(x, k)`.** -/
noncomputable def saT3 (x : Fin m → ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  coeffThree (saQ N k μ ν) α x

variable {N}

theorem saQ_eval (hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) : (saQ N k μ ν).eval = fun ℓ => N k ℓ μ ν :=
  eval_numQuartic (hQ k μ ν)

/-- The values of the quartics along a reflection. -/
theorem saQ_eval_reflect (hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν)
    (hcov : TCov2 N) {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (k : Fin 4 → ℝ)
    (μ ν : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (saQ N (reflect a k) μ ν).eval (loopAct (QED.Dirac.reflectMatrix a) ℓ) =
      ∑ α, ∑ β, (((QED.Dirac.reflectMatrix a μ α : ℝ) : ℂ) *
        ((QED.Dirac.reflectMatrix a ν β : ℝ) : ℂ)) *
        (saQ N k α β).eval ℓ := by
  rw [saQ_eval hQ, ← QED.Dirac.reflectMatrix_mulVec]
  show N _ (loopAct _ ℓ) μ ν = _
  rw [hcov _ _ _ (QED.TwoLoop.ReflCovariance.isSpinLift_reflect ha) k ℓ]
  simp only [saQ_eval hQ, upperAct]

theorem saShift_reflect {a : Fin 4 → ℝ} (k : Fin 4 → ℝ) (z : Fin (m + 1) → ℝ) :
    -loopShift α (fun i => c i • reflect a k) z =
      loopAct (QED.Dirac.reflectMatrix a) (-loopShift α (fun i => c i • k) z) := by
  have hp : (fun i => c i • reflect a k) = fun i => QED.Dirac.reflectMatrix a *ᵥ (c i • k) := by
    funext i
    rw [← QED.Dirac.reflectMatrix_mulVec, Matrix.mulVec_smul]
  rw [hp, QED.TwoLoop.ReflCovariance.loopShift_map, loopAct_neg]

theorem rAct_apply_mul (a : Fin 4 → ℝ) (u : ℂ) (X : Fin 4 → Fin 4 → ℂ) (μ ν : Fin 4) :
    rAct a (fun μ ν => u * X μ ν) μ ν = u * rAct a X μ ν := by
  rw [rAct_mul]

/-- **`T₁(x, ·)` is covariant.** -/
theorem saT1_cov (hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν)
    (hcov : TCov2 N) (x : Fin m → ℝ) : SACov (saT1 N α c x) := by
  intro a ha k
  funext μ ν
  have e : ∀ k μ ν, saT1 N α c x k μ ν =
      (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * ((m - 4).factorial : ℂ)) *
        (saQ N k μ ν).eval (-loopShift α (fun i => c i • k) (simplexPoint x)) := fun k μ ν => by
    simp only [saT1, coeffOne]
    ring
  rw [e, saShift_reflect, saQ_eval_reflect hQ hcov ha]
  simp only [rAct, e, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **`T₂(x, ·)` is covariant.** -/
theorem saT2_cov (hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν)
    (hcov : TCov2 N) (x : Fin m → ℝ) : SACov (saT2 N α c x) := by
  intro a ha k
  funext μ ν
  have hL := (QED.TwoLoop.ReflCovariance.isSpinLift_reflect ha).lorentz_left
  have e : ∀ k μ ν, saT2 N α c x k μ ν =
      (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * (((m - 5).factorial : ℂ) / 2)) *
        (saQ N k μ ν).contractTwo (symanzikMatrix α (simplexPoint x))
          (loopComp (-loopShift α (fun i => c i • k) (simplexPoint x))) := fun k μ ν => by
    simp only [saT2, coeffTwo]
    ring
  rw [e, saShift_reflect, saContractTwo_map hL (saQ_eval_reflect hQ hcov ha k μ ν)
    (symanzikMatrix_transpose α _)]
  simp only [rAct, e, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **`T₃(x, ·)` is covariant.** -/
theorem saT3_cov (hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν)
    (hcov : TCov2 N) (x : Fin m → ℝ) : SACov (saT3 N α x) := by
  intro a ha k
  funext μ ν
  have hL := (QED.TwoLoop.ReflCovariance.isSpinLift_reflect ha).lorentz_left
  have e : ∀ k μ ν, saT3 N α x k μ ν =
      (((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * (((m - 6).factorial : ℂ) / 4)) *
        (saQ N k μ ν).contractFour (symanzikMatrix α (simplexPoint x)) := fun k μ ν => by
    simp only [saT3, coeffThree]
    ring
  rw [e, saContractFour_map hL (saQ_eval_reflect hQ hcov ha k μ ν)
    (symanzikMatrix_transpose α _)]
  simp only [rAct, e, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### Polynomiality in `k` -/

/-- **Polynomial along affine loop momenta**: `k ↦ N_k(λ k + δ)` has degree `≤ d` for every
`λ`, `δ`. -/
def SAPolyK (d : ℕ) (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ (lam : Fin 2 → ℝ) (δ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4),
    IsLoopPoly 1 d fun y => N (y 0) ((fun s => lam s • y 0) + δ) μ ν

/-- The scalar of the loop shift at line momenta `cᵢ k`: `S(z)ₛ = σₛ k`. -/
noncomputable def saSig (z : Fin (m + 1) → ℝ) (s : Fin 2) : ℝ :=
  ∑ t, (symanzikMatrix α z)⁻¹ s t * ∑ i, z i * α i t * c i

theorem saShift_eq (k : Fin 4 → ℝ) (z : Fin (m + 1) → ℝ) :
    -loopShift α (fun i => c i • k) z = (fun s => (-saSig α c z s) • k) + 0 := by
  funext s μ
  simp only [Pi.neg_apply, loopShift_apply, Pi.add_apply, Pi.zero_apply, add_zero,
    Pi.smul_apply, smul_eq_mul, saSig, Pi.smul_apply]
  rw [neg_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem saIsLoopPoly_div {F : (Fin 1 → Fin 4 → ℝ) → ℂ} (h : IsLoopPoly 1 4 F) (u : ℂ) :
    IsLoopPoly 1 4 fun y => F y / u := by
  simpa [div_eq_mul_inv, mul_comm] using h.const_mul u⁻¹

theorem SAPolyK.hf (hN : SAPolyK 4 N) (lam : Fin 2 → ℝ) (δ₀ δ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 1 4 fun y => saHf (fun ℓ => N (y 0) ℓ μ ν) ((fun s => lam s • y 0) + δ₀) δ := by
  unfold saHf
  simp only [add_assoc, add_sub_assoc]
  have h1 := fun δ' => hN lam δ' μ ν
  exact saIsLoopPoly_div (((((h1 _).add (h1 _)).const_mul 8).sub
    (saIsLoopPoly_div ((h1 _).add (h1 _)) 2)).sub ((h1 _).const_mul 15)) 12

theorem SAPolyK.hf0 (hN : SAPolyK 4 N) (δ₀ δ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 1 4 fun y => saHf (fun ℓ => N (y 0) ℓ μ ν) δ₀ δ := by
  have h := hN.hf 0 δ₀ δ μ ν
  have e2 : ∀ y : Fin 1 → Fin 4 → ℝ, (fun s => (0 : Fin 2 → ℝ) s • y 0) + δ₀ = δ₀ := by
    intro y; funext s μ; simp
  simpa only [e2] using h

variable (hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν)
include hQ

theorem saCt2_poly (hN : SAPolyK 4 N) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A)
    (lam : Fin 2 → ℝ) (δ₀ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 1 4 fun y =>
      (saQ N (y 0) μ ν).contractTwo A (loopComp ((fun s => lam s • y 0) + δ₀)) := by
  simp only [saCt2_eq _ hA, saQ_eval hQ]
  exact IsLoopPoly.sum _ fun a _ => IsLoopPoly.sum _ fun b _ =>
    (((hN.hf _ _ _ μ ν).sub (hN.hf _ _ _ μ ν)).sub (hN.hf _ _ _ μ ν)).const_mul _

theorem saCt2_poly0 (hN : SAPolyK 4 N) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aᵀ = A)
    (δ₀ : Fin 2 → Fin 4 → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 1 4 fun y => (saQ N (y 0) μ ν).contractTwo A (loopComp δ₀) := by
  simp only [saCt2_eq _ hA, saQ_eval hQ]
  exact IsLoopPoly.sum _ fun a _ => IsLoopPoly.sum _ fun b _ =>
    (((hN.hf0 _ _ μ ν).sub (hN.hf0 _ _ μ ν)).sub (hN.hf0 _ _ μ ν)).const_mul _

/-- **`T₁(x, k)` has degree `≤ 4` in `k`.** -/
theorem saT1_poly (hN : SAPolyK 4 N) (x : Fin m → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 1 4 fun y => saT1 N α c x (y 0) μ ν := by
  simp only [saT1, coeffOne, saShift_eq, saQ_eval hQ]
  exact ((hN _ 0 μ ν).const_mul _).const_mul _

/-- **`T₂(x, k)` has degree `≤ 4` in `k`.** -/
theorem saT2_poly (hN : SAPolyK 4 N) (x : Fin m → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 1 4 fun y => saT2 N α c x (y 0) μ ν := by
  simp only [saT2, coeffTwo, saShift_eq]
  exact ((saCt2_poly hQ hN (symanzikMatrix_transpose α _) _ 0 μ ν).const_mul _).const_mul _

/-- **`T₃(x, k)` has degree `≤ 4` in `k`.** -/
theorem saT3_poly (hN : SAPolyK 4 N) (x : Fin m → ℝ) (μ ν : Fin 4) :
    IsLoopPoly 1 4 fun y => saT3 N α x (y 0) μ ν := by
  have hA := symanzikMatrix_transpose α (simplexPoint x)
  have h4 : ∀ y : LoopIndex → ℝ, IsLoopPoly 1 4 fun y' =>
      saQ4 (saQ N (y' 0) μ ν) (symanzikMatrix α (simplexPoint x)) y := fun y =>
    saIsLoopPoly_div (((saCt2_poly0 hQ hN hA _ μ ν).add (saCt2_poly0 hQ hN hA _ μ ν)).sub
      ((saCt2_poly0 hQ hN hA _ μ ν).const_mul 2)) 2
  simp only [saT3, coeffThree, saCt4_eq _ hA]
  exact (IsLoopPoly.sum _ fun a _ => IsLoopPoly.sum _ fun b _ =>
    (((h4 _).sub (h4 _)).sub (h4 _)).const_mul _).const_mul _ |>.const_mul _

end QED.ChainProof.SetASpec

end
