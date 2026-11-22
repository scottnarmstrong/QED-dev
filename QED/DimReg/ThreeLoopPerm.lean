/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopPoly
public import QED.Algebra.IBPCertSym

/-!
# Relabelling symmetries of Lee–Pomeransky integrals

If a permutation `σ` of the Schwinger parameters leaves `G` invariant, `G (x ∘ σ) = G x`, then
the substitution `x ↦ x ∘ σ⁻¹` (measure preserving, and preserving the orthant) gives

  `∫ x ^ (ν ∘ σ - 1) G ^ (-d/2) = ∫ x ^ (ν - 1) G ^ (-d/2)`

together with the equivalence of absolute convergence (`QED.DimReg.lpIntegral_comp_perm`,
`QED.DimReg.lpConvergent_comp_perm_iff`). For a momentum-space family, a relabelling of the loop
momenta that permutes the denominators permutes the Schwinger parameters and leaves `U` and `F`
invariant; here the invariance is checked directly on `G`.

For a sparse polynomial the invariance is a kernel check on exponents
(`QED.DimReg.Sector.NPoly.permute`, `QED.DimReg.Sector.NPoly.eval_comp_perm`). For the set (d)
family `lbl` the only nontrivial permutation of the nine parameters fixing `G` (found by
exhaustive search) is `σ₀ = (D₁ D₃)(D₄ D₅)(D₇ D₈)`, the reflection of the closed electron loop
together with the open line (`QED.DimReg.ThreeLoop.lpPoly_comp_sigma0`). In the form of the
checker's `QED.Algebra.IBPCert.permLabel` it is the list `sigma0L = [2, 1, 0, 4, 3, 5, 7, 6, 8]`
(`QED.DimReg.ThreeLoop.toVec_permLabel_sigma0L`). The further symmetries that identify masters
(`(D₆ D₇)` on sectors without `D₇`, `D₈`, …) are symmetries of the restrictions of `G` to faces
`x_a = 0`; they act on the continued integrals only once the values at `ν_a = 0` are identified
with integrals of the restricted polynomial.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.DimReg

variable {N : ℕ}

theorem comp_perm_mem_posOrthant (σ : Equiv.Perm (Fin N)) {x : Fin N → ℝ} :
    x ∘ σ ∈ posOrthant N ↔ x ∈ posOrthant N := by
  simp only [mem_posOrthant, Function.comp_apply]
  exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

/-- The integrand at `x ∘ σ⁻¹` is the integrand with permuted exponents. -/
theorem lpIntegrand_comp_symm {G : (Fin N → ℝ) → ℝ} (σ : Equiv.Perm (Fin N))
    (hG : ∀ x, G (x ∘ σ) = G x) (ν : Fin N → ℂ) (d : ℂ) (x : Fin N → ℝ) :
    lpIntegrand G ν d (x ∘ σ.symm) = lpIntegrand G (ν ∘ σ) d x := by
  have hG' : G (x ∘ σ.symm) = G x := by
    have := hG (x ∘ σ.symm)
    rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] at this
    exact this.symm
  simp only [lpIntegrand, hG', Function.comp_apply]
  congr 1
  exact (Equiv.prod_comp σ fun i => (x (σ.symm i) : ℂ) ^ (ν i - 1)).symm.trans
    (by simp)

/-- The substitution `x ↦ x ∘ σ⁻¹` is measure preserving. -/
theorem measurePreserving_comp_symm (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' σ (MeasurableEquiv.refl ℝ))
      (volume : Measure (Fin N → ℝ)) volume :=
  volume_preserving_arrowCongr' σ (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)

theorem arrowCongr'_apply (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ) :
    MeasurableEquiv.arrowCongr' σ (MeasurableEquiv.refl ℝ) x = x ∘ σ.symm := rfl

theorem indicator_comp_symm {G : (Fin N → ℝ) → ℝ} (σ : Equiv.Perm (Fin N))
    (hG : ∀ x, G (x ∘ σ) = G x) (ν : Fin N → ℂ) (d : ℂ) :
    (posOrthant N).indicator (lpIntegrand G ν d) ∘
        MeasurableEquiv.arrowCongr' σ (MeasurableEquiv.refl ℝ) =
      (posOrthant N).indicator (lpIntegrand G (ν ∘ σ) d) := by
  funext x
  rw [Function.comp_apply, arrowCongr'_apply]
  by_cases hx : x ∈ posOrthant N
  · rw [indicator_of_mem ((comp_perm_mem_posOrthant σ.symm).2 hx), indicator_of_mem hx,
      lpIntegrand_comp_symm σ hG]
  · rw [indicator_of_notMem (mt (comp_perm_mem_posOrthant σ.symm).1 hx),
      indicator_of_notMem hx]

/-- **A relabelling symmetry of `G` permutes the Lee–Pomeransky integrals.** -/
theorem lpIntegral_comp_perm {G : (Fin N → ℝ) → ℝ} (σ : Equiv.Perm (Fin N))
    (hG : ∀ x, G (x ∘ σ) = G x) (ν : Fin N → ℂ) (d : ℂ) :
    lpIntegral G (ν ∘ σ) d = lpIntegral G ν d := by
  simp only [lpIntegral, ← integral_indicator (measurableSet_posOrthant N)]
  rw [← indicator_comp_symm σ hG]
  exact (measurePreserving_comp_symm σ).integral_comp' _

/-- The relabelling preserves absolute convergence. -/
theorem lpConvergent_comp_perm_iff {G : (Fin N → ℝ) → ℝ} (σ : Equiv.Perm (Fin N))
    (hG : ∀ x, G (x ∘ σ) = G x) (ν : Fin N → ℂ) (d : ℂ) :
    LPConvergent G (ν ∘ σ) d ↔ LPConvergent G ν d := by
  simp only [LPConvergent, ← integrable_indicator_iff (measurableSet_posOrthant N)]
  rw [← indicator_comp_symm σ hG]
  exact (measurePreserving_comp_symm σ).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)

namespace Sector

/-- The exponent list `k ↦ α (f k)`. -/
def permExp (f : Fin N → Fin N) (α : List ℕ) : List ℕ :=
  (List.finRange N).map fun k => α.getD (f k) 0

theorem getD_permExp (f : Fin N → Fin N) (α : List ℕ) (k : Fin N) :
    (permExp f α).getD k 0 = α.getD (f k) 0 := by
  simp [permExp]

/-- `y ^ α` at `y ∘ σ` is `y ^ (α ∘ σ⁻¹)`. -/
theorem mono_comp_perm (σ : Equiv.Perm (Fin N)) (α : List ℕ) (y : Fin N → ℝ) :
    mono α (y ∘ σ) = mono (permExp σ.symm α) y := by
  rw [mono, mono, ← Equiv.prod_comp σ (fun k => y k ^ (permExp σ.symm α).getD k 0)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [getD_permExp, Equiv.symm_apply_apply]
  rfl

/-- The polynomial `y ↦ P (y ∘ f⁻¹)` on exponents, for `f` given as `σ⁻¹`. -/
def NPoly.permute (f : Fin N → Fin N) (P : NPoly) : NPoly :=
  P.map fun t => (permExp f t.1, t.2)

theorem NPoly.eval_comp_perm (σ : Equiv.Perm (Fin N)) (P : NPoly) (y : Fin N → ℝ) :
    P.eval (y ∘ σ) = (P.permute σ.symm).eval y := by
  simp only [NPoly.eval, NPoly.permute, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, mono_comp_perm]

/-- The kernel check that `σ` fixes `P`. -/
def NPoly.permInvB (σ : Equiv.Perm (Fin N)) (P : NPoly) : Bool :=
  ZPoly.isZeroB (ZPoly.ofN (P.permute σ.symm) ++ ZPoly.smul (-1) (ZPoly.ofN P))

theorem NPoly.eval_comp_of_permInvB {σ : Equiv.Perm (Fin N)} {P : NPoly}
    (h : P.permInvB σ = true) (y : Fin N → ℝ) : P.eval (y ∘ σ) = P.eval y := by
  rw [NPoly.eval_comp_perm, ← ZPoly.eval_ofN, ← ZPoly.eval_ofN (N := N) P]
  exact ZPoly.eval_eq_of_isZeroB h y

end Sector

namespace ThreeLoop

open QED.Algebra.IBPCert Sector

/-- The reflection `σ₀ = (D₁ D₃)(D₄ D₅)(D₇ D₈)` (zero-based: `(0 2)(3 4)(6 7)`). -/
def sigma0 : Equiv.Perm (Fin 9) := Equiv.swap 0 2 * Equiv.swap 3 4 * Equiv.swap 6 7

/-- `σ₀` as the list of its values, for `QED.Algebra.IBPCert.permLabel`. -/
def sigma0L : List ℕ := [2, 1, 0, 4, 3, 5, 7, 6, 8]

theorem sigma0L_eq : sigma0L = (List.finRange 9).map fun a => (sigma0 a : ℕ) := by
  decide +kernel

theorem permInvB_sigma0 : lpPoly.permInvB sigma0 = true := by
  rw [lpPoly_eq_lit]; decide +kernel

/-- **`σ₀` fixes the Lee–Pomeransky polynomial of `lbl`.** -/
theorem lpPoly_comp_sigma0 (x : Fin 9 → ℝ) : lpPoly.eval (x ∘ sigma0) = lpPoly.eval x :=
  NPoly.eval_comp_of_permInvB permInvB_sigma0 x

/-- **`σ₀` permutes the Lee–Pomeransky integrals of `lbl`.** -/
theorem lpIntegral_sigma0 (ν : Fin 9 → ℂ) (d : ℂ) :
    lpIntegral (fun x => lpPoly.eval x) (ν ∘ sigma0) d = lpIntegral (fun x => lpPoly.eval x) ν d :=
  lpIntegral_comp_perm sigma0 lpPoly_comp_sigma0 ν d

/-- The checker's relabelling by `sigma0L` is composition with `σ₀`. -/
theorem toVec_permLabel_sigma0L (ν : List ℤ) :
    toVec 9 (permLabel sigma0L ν) = toVec 9 ν ∘ sigma0 := by
  funext a
  fin_cases a <;> rfl

end ThreeLoop

end QED.DimReg
