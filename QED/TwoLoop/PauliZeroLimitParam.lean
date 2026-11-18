/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroLimitCore
public import QED.TwoLoop.ClassLimitParametric
public import QED.TwoLoop.ParametricBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The parametric integrand along a rational curve of external momenta

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). Let the external line
momenta `p(u)` of a parametric representation depend on `u ∈ (-1, 1)` so that `(1 - u²) p(u)` is
polynomial of degree at most `2` (as along the curve `p'(u) = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`).
For a **fixed** numerator `Q` the parametric integrand at `ε = 0` is

`paramIntegrand Q α p(u) M 0 x = paramNum Q α p(u) M x / V(x, u)^{m-3}`

wherever `V ≠ 0` (`paramIntegrand_zero_eq`), with `paramNum = T₁ + T₂ V + T₃ V²` built from the
coefficient functions of `QED/TwoLoop/ClassLimitParametric.lean`, and

* `(1 - u²)⁴ paramNum` is a polynomial of degree at most `8` in `u` at every `x`
  (`isUPoly_paramNum`);
* `(1 - u²)² V` is a polynomial of degree at most `4` (`isUPoly_symanzikV`);
* `paramNum` is integrable on the simplex at every fixed `u` (`integrableOn_paramNum`).

Also: a polynomial of total degree at most `n` in `L` four-vectors, evaluated at four-vectors with
`(1 - u²) ℓ(u)` polynomial of degree at most `2`, is `(1 - u²)⁻ⁿ` times a polynomial of degree at
most `2n` (`isUPoly_eval_of_isLoopPoly`). This is how the numerators enter.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.PauliZeroLimit

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)

/-! ### The weight -/

theorem isUPoly_wt {ι : Type*} : IsUPoly (ι := ι) 2 fun _ u => wt u := fun _ =>
  ⟨1 - X ^ 2, by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_one]; exact Nat.zero_le _
    · exact natDegree_X_pow_le 2, fun u _ => by simp [wt]⟩

theorem isUPoly_wt_pow {ι : Type*} (n : ℕ) : IsUPoly (ι := ι) (2 * n) fun _ u => wt u ^ n := by
  simpa only [mul_comm 2 n] using (isUPoly_wt (ι := ι)).pow n

/-! ### Polynomials in four-vectors along the curve -/

/-- **Polynomials in four-vectors along a rational curve.** If `G` has total degree at most `n`
in the `4L` coordinates and `(1 - u²) ℓ(x, u)` is polynomial of degree at most `2` in `u`, then
`(1 - u²)ⁿ G(ℓ(x, u))` is polynomial of degree at most `2n`. -/
theorem isUPoly_eval_of_isLoopPoly {L n : ℕ} {G : (Fin L → Fin 4 → ℝ) → ℂ} (hG : IsLoopPoly L n G)
    {ι : Type*} {ℓ : ι → ℝ → Fin L → Fin 4 → ℝ}
    (hℓ : ∀ s ν, IsUPoly 2 fun x u => wt u * ((ℓ x u s ν : ℝ) : ℂ)) :
    IsUPoly (2 * n) fun x u => wt u ^ n * G (ℓ x u) := by
  classical
  obtain ⟨Q, hQ, hGQ⟩ := hG
  have e : ∀ x u, wt u ^ n * G (ℓ x u) = ∑ d ∈ Q.support, Q.coeff d *
      (wt u ^ (n - d.sum fun _ e => e) *
        ∏ v ∈ d.support, (wt u * ((ℓ x u v.1 v.2 : ℝ) : ℂ)) ^ d v) := by
    intro x u
    rw [hGQ, MvPolynomial.eval_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdeg : (d.sum fun _ e => e) ≤ n := (MvPolynomial.le_totalDegree hd).trans hQ
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hs : (∑ v ∈ d.support, d v) = d.sum fun _ e => e := rfl
    rw [hs, ← mul_assoc (wt u ^ (n - _)), ← pow_add, Nat.sub_add_cancel hdeg]
    ring
  refine IsUPoly.congr ?_ (fun x u _ => (e x u).symm)
  refine IsUPoly.sum _ fun d hd => IsUPoly.const_mul _ ?_
  have hdeg : (d.sum fun _ e => e) ≤ n := (MvPolynomial.le_totalDegree hd).trans hQ
  have h1 := isUPoly_wt_pow (ι := ι) (n - d.sum fun _ e => e)
  have h2 := IsUPoly.prod d.support (fun v => d v * 2) fun v _ => (hℓ v.1 v.2).pow (d v)
  refine (h1.mul h2).mono ?_
  have hs : (∑ v ∈ d.support, d v * 2) = 2 * d.sum fun _ e => e := by
    rw [← Finset.sum_mul, mul_comm]
    rfl
  rw [hs]
  omega

/-! ### The loop shift and `V` along the curve -/

section Data

variable {ι : Type*} {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (mom : ℝ → Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) (z : ι → Fin (m + 1) → ℝ)

theorem isUPoly_loopShift (hmom : ∀ i μ, IsUPoly (ι := ι) 2 fun _ u => wt u * ((mom u i μ : ℝ) : ℂ))
    (s : Fin 2) (μ : Fin 4) :
    IsUPoly 2 fun x u => wt u * ((loopShift α (mom u) (z x) s μ : ℝ) : ℂ) := by
  have e : ∀ x u, wt u * ((loopShift α (mom u) (z x) s μ : ℝ) : ℂ) =
      ∑ t, (((symanzikMatrix α (z x))⁻¹ s t : ℝ) : ℂ) *
        ∑ i, ((z x i * α i t : ℝ) : ℂ) * (wt u * ((mom u i μ : ℝ) : ℂ)) := by
    intro x u
    have hS : loopShift α (mom u) (z x) s μ =
        ∑ t, (symanzikMatrix α (z x))⁻¹ s t * ∑ i, z x i * α i t * mom u i μ := by
      refine Fin.cases ?_ (fun c => ?_) μ <;> rfl
    rw [hS]
    push_cast
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring
  refine IsUPoly.congr ?_ (fun x u _ => (e x u).symm)
  exact IsUPoly.sum _ fun t _ => IsUPoly.const_mul _
    (IsUPoly.sum _ fun i _ => IsUPoly.const_mul _ (hmom i μ))

/-- The complex Minkowski product of two complex four-vectors. -/
def cdot (a b : Fin 4 → ℂ) : ℂ := -(a 0 * b 0) + a 1 * b 1 + a 2 * b 2 + a 3 * b 3

theorem ofReal_dot_mul (a b : Fin 4 → ℝ) (w w' : ℂ) :
    w * w' * ((Minkowski.dot a b : ℝ) : ℂ) =
      cdot (fun μ => w * ((a μ : ℝ) : ℂ)) (fun μ => w' * ((b μ : ℝ) : ℂ)) := by
  rw [Minkowski.dot_eq, cdot]
  push_cast
  ring

theorem IsUPoly.cdot {D E : ℕ} {a b : ι → ℝ → Fin 4 → ℂ} (ha : ∀ μ, IsUPoly D fun x u => a x u μ)
    (hb : ∀ μ, IsUPoly E fun x u => b x u μ) :
    IsUPoly (D + E) fun x u => QED.TwoLoop.PauliZeroLimit.cdot (a x u) (b x u) := by
  unfold QED.TwoLoop.PauliZeroLimit.cdot
  exact ((((ha 0).mul (hb 0)).neg.add ((ha 1).mul (hb 1))).add ((ha 2).mul (hb 2))).add
    ((ha 3).mul (hb 3))

/-- **`(1 - u²)² V` is polynomial of degree at most `4`.** -/
theorem isUPoly_symanzikV
    (hmom : ∀ i μ, IsUPoly (ι := ι) 2 fun _ u => wt u * ((mom u i μ : ℝ) : ℂ)) :
    IsUPoly 4 fun x u => wt u ^ 2 * ((symanzikV α (mom u) M (z x) : ℝ) : ℂ) := by
  have hB : ∀ s μ, IsUPoly (ι := ι) 2 fun x u =>
      wt u * ((symanzikVector α (mom u) (z x) s μ : ℝ) : ℂ) := fun s μ => by
    have e : ∀ x u, wt u * ((symanzikVector α (mom u) (z x) s μ : ℝ) : ℂ) =
        ∑ i, ((z x i * α i s : ℝ) : ℂ) * (wt u * ((mom u i μ : ℝ) : ℂ)) := by
      intro x u
      simp only [symanzikVector]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine IsUPoly.congr ?_ (fun x u _ => (e x u).symm)
    exact IsUPoly.sum _ fun i _ => IsUPoly.const_mul _ (hmom i μ)
  have e : ∀ x u, wt u ^ 2 * ((symanzikV α (mom u) M (z x) : ℝ) : ℂ) =
      ∑ i, ((z x i : ℝ) : ℂ) * (((M i ^ 2 : ℝ) : ℂ) * wt u ^ 2 +
        QED.TwoLoop.PauliZeroLimit.cdot (fun μ => wt u * ((mom u i μ : ℝ) : ℂ))
          (fun μ => wt u * ((mom u i μ : ℝ) : ℂ))) -
      ∑ s, ∑ t, (((symanzikMatrix α (z x))⁻¹ s t : ℝ) : ℂ) *
        QED.TwoLoop.PauliZeroLimit.cdot
          (fun μ => wt u * ((symanzikVector α (mom u) (z x) s μ : ℝ) : ℂ))
          (fun μ => wt u * ((symanzikVector α (mom u) (z x) t μ : ℝ) : ℂ)) := by
    intro x u
    simp only [symanzikV, ← ofReal_dot_mul]
    push_cast
    simp only [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
  refine IsUPoly.congr ?_ (fun x u _ => (e x u).symm)
  refine IsUPoly.sub ?_ ?_
  · refine IsUPoly.sum _ fun i _ => IsUPoly.const_mul _ (IsUPoly.add ?_ ?_)
    · exact IsUPoly.const_mul _ (isUPoly_wt_pow 2)
    · exact IsUPoly.cdot (fun μ => hmom i μ) (fun μ => hmom i μ)
  · exact IsUPoly.sum _ fun s _ => IsUPoly.sum _ fun t _ =>
      IsUPoly.const_mul _ (IsUPoly.cdot (fun μ => hB s μ) (fun μ => hB t μ))

end Data

/-! ### The contractions of a fixed numerator -/

section Contract

variable {ι : Type*} (Q : LoopQuartic) (X : ι → ℝ → LoopIndex → ℂ)

theorem isUPoly_evalC (hX : ∀ a, IsUPoly 2 fun x u => wt u * X x u a) :
    IsUPoly 8 fun x u => wt u ^ 4 * Q.evalC (X x u) := by
  have e : ∀ x u, wt u ^ 4 * Q.evalC (X x u) =
      wt u ^ 4 * Q.const + ∑ a, Q.lin a * (wt u ^ 3 * (wt u * X x u a)) +
        ∑ a, ∑ b, Q.quad a b * (wt u ^ 2 * ((wt u * X x u a) * (wt u * X x u b))) +
        ∑ a, ∑ b, ∑ c, Q.cub a b c *
          (wt u * ((wt u * X x u a) * (wt u * X x u b) * (wt u * X x u c))) +
        ∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d *
          ((wt u * X x u a) * (wt u * X x u b) * (wt u * X x u c) * (wt u * X x u d)) := by
    intro x u
    simp only [LoopQuartic.evalC, mul_add, Finset.mul_sum]
    congr 1; congr 1; congr 1; congr 1
    · exact Finset.sum_congr rfl fun a _ => by ring
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => by ring
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  refine IsUPoly.congr ?_ (fun x u _ => (e x u).symm)
  refine (((?_ : IsUPoly 8 _).add ?_).add ?_).add ?_ |>.add ?_
  · exact IsUPoly.mul_const _ (isUPoly_wt_pow 4)
  · exact IsUPoly.sum _ fun a _ => IsUPoly.const_mul _ ((isUPoly_wt_pow 3).mul (hX a))
  · exact IsUPoly.sum _ fun a _ => IsUPoly.sum _ fun b _ => IsUPoly.const_mul _
      ((isUPoly_wt_pow 2).mul ((hX a).mul (hX b)))
  · exact IsUPoly.sum _ fun a _ => IsUPoly.sum _ fun b _ => IsUPoly.sum _ fun c _ =>
      IsUPoly.const_mul _ (isUPoly_wt.mul (((hX a).mul (hX b)).mul (hX c)))
  · exact IsUPoly.sum _ fun a _ => IsUPoly.sum _ fun b _ => IsUPoly.sum _ fun c _ =>
      IsUPoly.sum _ fun d _ => IsUPoly.const_mul _ ((((hX a).mul (hX b)).mul (hX c)).mul (hX d))

theorem isUPoly_contractTwo (A : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (hX : ∀ a, IsUPoly 2 fun x u => wt u * X x u a) :
    IsUPoly 4 fun x u => wt u ^ 2 * Q.contractTwo (A x) (X x u) := by
  have eh : ∀ x u a b, wt u ^ 2 * Q.hess (X x u) a b =
      wt u ^ 2 * Q.quad a b + ∑ c, (Q.cub a b c + Q.cub a c b + Q.cub c a b) *
          (wt u * (wt u * X x u c)) +
        ∑ c, ∑ d, Q.quartSym a b c d * ((wt u * X x u c) * (wt u * X x u d)) := by
    intro x u a b
    simp only [LoopQuartic.hess, mul_add, Finset.mul_sum]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun c _ => by ring
    · exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have e : ∀ x u, wt u ^ 2 * Q.contractTwo (A x) (X x u) =
      ∑ a, ∑ b, ((loopMetricInv (A x) a b : ℝ) : ℂ) *
        (wt u ^ 2 * Q.quad a b + ∑ c, (Q.cub a b c + Q.cub a c b + Q.cub c a b) *
            (wt u * (wt u * X x u c)) +
          ∑ c, ∑ d, Q.quartSym a b c d * ((wt u * X x u c) * (wt u * X x u d))) := by
    intro x u
    simp only [LoopQuartic.contractTwo, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← eh]
    ring
  refine IsUPoly.congr ?_ (fun x u _ => (e x u).symm)
  refine IsUPoly.sum _ fun a _ => IsUPoly.sum _ fun b _ => IsUPoly.const_mul _ ?_
  refine ((IsUPoly.mul_const _ (isUPoly_wt_pow 2)).add ?_).add ?_
  · exact IsUPoly.sum _ fun c _ => IsUPoly.const_mul _ (isUPoly_wt.mul (hX c))
  · exact IsUPoly.sum _ fun c _ => IsUPoly.sum _ fun d _ =>
      IsUPoly.const_mul _ ((hX c).mul (hX d))

end Contract

/-! ### The integrand as numerator over a power of `V` -/

section ParamNum

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

/-- The numerator `T₁ + T₂ V + T₃ V²` of the parametric integrand at `ε = 0`. -/
noncomputable def paramNum (x : Fin m → ℝ) : ℂ :=
  coeffOne Q α p x + coeffTwo Q α p x * ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) +
    coeffThree Q α x * ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) ^ 2

/-- **The parametric integrand at `ε = 0` as `paramNum / V^{m-3}`**, where `V ≠ 0`. -/
theorem paramIntegrand_zero_eq (hm : 5 ≤ m) {x : Fin m → ℝ}
    (hV : symanzikV α p M (simplexPoint x) ≠ 0) :
    paramIntegrand Q α p M 0 x =
      paramNum Q α p M x / ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) ^ (m - 3) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 5 := ⟨m - 5, by omega⟩
  have hW : wBase α p M 0 x = ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) := by
    simp [wBase]
  have hV' : ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV
  rw [paramIntegrand_eq, hW, paramNum]
  rw [show n + 5 - 3 = n + 2 by omega, show n + 5 - 4 = n + 1 by omega,
    show n + 5 - 5 = n by omega]
  field_simp
  ring

/-- The parametric numerator is integrable on the simplex, for a numerator with the refined bound
and the criterion. -/
theorem integrableOn_paramNum (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval) :
    IntegrableOn (paramNum Q α p M) (simplexSet m) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  obtain ⟨hT₁, hT₂, hT₃⟩ := integrableOn_coeff Q α p hm hcrit hB
  set K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2)
  have hK := ae_abs_symanzikV_le α p M hm0 hspan
  have hVm : AEStronglyMeasurable (fun x => ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ))
      (volume.restrict (simplexSet m)) :=
    (Complex.measurable_ofReal.comp ((measurable_symanzikV α p M).comp
      continuous_simplexPoint'.measurable)).aestronglyMeasurable
  have hb1 : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ‖((symanzikV α p M (simplexPoint x) : ℝ) : ℂ)‖ ≤ K := by
    filter_upwards [hK] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hb2 : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ‖((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) ^ 2‖ ≤ K ^ 2 := by
    filter_upwards [hb1] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  exact (hT₁.add (hT₂.mul_bdd hVm hb1)).add (hT₃.mul_bdd (hVm.pow 2) hb2)

/-- **`(1 - u²)⁴ paramNum` is polynomial of degree at most `8`** along momenta `p(u)` with
`(1 - u²) p(u)` polynomial of degree at most `2`. -/
theorem isUPoly_paramNum (mom : ℝ → Fin (m + 1) → Fin 4 → ℝ)
    (hmom : ∀ i μ, IsUPoly (ι := Fin m → ℝ) 2 fun _ u => wt u * ((mom u i μ : ℝ) : ℂ)) :
    IsUPoly 8 fun x u => wt u ^ 4 * paramNum Q α (mom u) M x := by
  have hS := isUPoly_loopShift α mom (fun x => simplexPoint x) hmom
  have hX : ∀ a : LoopIndex, IsUPoly 2 fun (x : Fin m → ℝ) u =>
      wt u * loopComp (-loopShift α (mom u) (simplexPoint x)) a := fun a => by
    have e : ∀ (x : Fin m → ℝ) u, wt u * loopComp (-loopShift α (mom u) (simplexPoint x)) a =
        -(wt u * ((loopShift α (mom u) (simplexPoint x) a.1 a.2 : ℝ) : ℂ)) := by
      intro x u
      simp [loopComp]
    exact (hS a.1 a.2).neg.congr fun x u _ => (e x u).symm
  have hV := isUPoly_symanzikV α mom M (fun x => simplexPoint x) hmom
  have h1 := (isUPoly_evalC Q _ hX).const_mul
    (fun x => ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * ((m - 4).factorial : ℂ))
  have h2 := ((isUPoly_contractTwo Q _ (fun x => symanzikMatrix α (simplexPoint x)) hX).mul
    hV).const_mul
    (fun x => ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ * (((m - 5).factorial : ℂ) / 2))
  have h3 := (hV.mul hV).const_mul
    (fun x => ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
      (((m - 6).factorial : ℂ) / 4 * Q.contractFour (symanzikMatrix α (simplexPoint x))))
  refine ((h1.add h2).add h3).congr fun x u _ => ?_
  simp only [paramNum, coeffOne, coeffTwo, coeffThree, LoopQuartic.eval]
  ring

end ParamNum

end QED.TwoLoop.PauliZeroLimit

end
