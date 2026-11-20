/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4CollapseSwap
public import QED.GradedProof.WI2Dbl

/-!
# (R-Π₄) step L6b′: a piece at a photon pair as an integral over the photon mass

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6b′ (heavy photon
pair). A parametric value `pvOf` over data whose line `i` is doubled (masses `(a, b)`), with the
photon factor `b² - a²` in its numerator, is `∫_{a²}^{b²} 𝒫(u) du` with the one-photon-line
density `pairDens`, which does not depend on `(a, b)`.

* `pairDens F α p M i u = -π⁴ ∫_{Δₘ} zᵢ paramAtV(V₀ + zᵢ u)` (numerator `numQuartic F`);
  `paramAtV_congr`, `pairDens_eq` (any quartic with the values of `F`).
* `symanzikV_dbl_ge`: a lower bound of the merged `V₀ + zᵢ a²` is one of `V` on the doubled data
  (every point of the doubled simplex is a split, `QED.GradedProof.WI2.exists_splitAt`).
* `pvOf_dbl_pair` (**piece at a photon pair**): under the criterion and the refined bound of the
  doubled data and a lower bound `c ≤ V₀ + zᵢ u` (`u ∈ [a², b²]`) of the merged data,
  `pvOf((b² - a²) F) = ∫_{a²}^{b²} pairDens F u du`, the density interval integrable.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.Integration.SimplexMerge
open QED.GradedProof.WI2 (dbl ehat symanzikU_dbl exists_splitAt)
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.GradedProof.VP2 (good_of_poly)

variable {m : ℕ}

theorem paramAtV_congr {Q Q' : LoopQuartic} (h : Q.eval = Q'.eval) (n : ℕ)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ) (v : ℝ) :
    paramAtV n Q α p z v = paramAtV n Q' α p z v := by
  have h1 : Q.evalC (loopComp (-loopShift α p z)) = Q'.evalC (loopComp (-loopShift α p z)) :=
    congrFun h _
  simp only [paramAtV, ehat, h1,
    QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractTwo_congr h
      (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose α _),
    QED.TwoLoop.PauliZeroExplicit.NumeratorCongr.contractFour_congr h
      (QED.TwoLoop.LimitCovariance.symanzikMatrix_transpose α _)]

/-- **The one-photon-line density** of data with a doubled line `i`: the merged data with the
photon parameter `zᵢ`, the squared photon mass `u` and the exponents of the doubled data,
`-π⁴ ∫_{Δₘ} zᵢ paramAtV(V₀ + zᵢ u)` (`V₀` at photon mass `0`). -/
noncomputable def pairDens (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (u : ℝ) : ℂ :=
  -((π : ℂ) ^ 4) * ∫ y in simplexSet m, (simplexPoint y i : ℂ) *
    paramAtV (m + 1) (numQuartic F) α p (simplexPoint y)
      (symanzikV α p (Function.update M i 0) (simplexPoint y) + simplexPoint y i * u)

theorem pairDens_eq {Q : LoopQuartic} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hQ : Q.eval = F)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) (u : ℝ) :
    pairDens F α p M i u = -((π : ℂ) ^ 4) * ∫ y in simplexSet m, (simplexPoint y i : ℂ) *
      paramAtV (m + 1) Q α p (simplexPoint y)
        (symanzikV α p (Function.update M i 0) (simplexPoint y) + simplexPoint y i * u) := by
  have h : (numQuartic F).eval = Q.eval := (eval_numQuartic ⟨Q, hQ⟩).trans hQ.symm
  simp only [pairDens, paramAtV_congr h]

/-- **Positivity on the doubled data from the merged data.** -/
theorem symanzikV_dbl_ge (i : Fin (m + 1)) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) {b c : ℝ} (hab : M i ^ 2 ≤ b ^ 2)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ j, 0 ≤ z j) → ∑ j, z j = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p (Function.update M i 0) z + z i * M i ^ 2)
    (z' : Fin (m + 2) → ℝ) (h0 : ∀ j, 0 ≤ z' j) (h1 : ∑ j, z' j = 1)
    (hU : symanzikU (dbl i α) z' ≠ 0) :
    c ≤ symanzikV (dbl i α) (dbl i p) (Fin.snoc M b) z' := by
  obtain ⟨z, t, hz0, hz1, rfl⟩ := exists_splitAt (i := i) h0 h1
  rw [symanzikU_dbl] at hU
  have ht : 0 ≤ t := by simpa [splitAt_castSucc] using h0 i.castSucc
  have ht' : 0 ≤ z i - t := by simpa [splitAt_last] using h0 (Fin.last _)
  rw [symanzikV_pair]
  have := hV z hz0 hz1 hU
  nlinarith [mul_le_mul_of_nonneg_left hab ht']

/-- **A piece at a photon pair is an integral over the photon mass.** Data `(dbl i α, dbl i p)`
with masses `(Mᵢ, b)` on the doubled line, `Mᵢ² < b²`, a numerator `F` of degree `m - 2`, the
criterion and the refined bound of the doubled data, and `c ≤ V₀ + zᵢ u` on the merged data for
`u ∈ [Mᵢ², b²]`: `pvOf((b² - Mᵢ²) F) = ∫_{Mᵢ²}^{b²} pairDens F u du`. -/
theorem pvOf_dbl_pair (hm : m = 5 ∨ m = 6) {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    {E : Finset (Fin (m + 2))} (i : Fin (m + 1)) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) {b : ℝ}
    (hcrit : NoSubdivergenceRefined 2 E (dbl i α)) (hpoly : IsLoopPoly 2 (m + 1 - 3) F)
    (hB : RefinedBound (dbl i α) E 4 F) (hab : M i ^ 2 < b ^ 2)
    (hspan : ∃ j l, α j 0 * α l 1 - α j 1 * α l 0 ≠ 0) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ j, 0 ≤ z j) → ∑ j, z j = 1 → symanzikU α z ≠ 0 →
      ∀ u ∈ Icc (M i ^ 2) (b ^ 2), c ≤ symanzikV α p (Function.update M i 0) z + z i * u) :
    IntervalIntegrable (pairDens F α p M i) volume (M i ^ 2) (b ^ 2) ∧
    pvOf (fun ℓ => ((b ^ 2 - M i ^ 2 : ℝ) : ℂ) * F ℓ) (dbl i α) (dbl i p) (Fin.snoc M b) =
      ∫ u in M i ^ 2..b ^ 2, pairDens F α p M i u := by
  have hm0 : 0 < m := by omega
  obtain ⟨Q, hq, hBQ, hQ⟩ := good_of_poly (n := m + 1) (by omega) hpoly hB
  have hcoef : IntegrableOn (coeffOne Q (dbl i α) (dbl i p)) (simplexSet (m + 1)) ∧
      IntegrableOn (coeffTwo Q (dbl i α) (dbl i p)) (simplexSet (m + 1)) ∧
      IntegrableOn (coeffThree Q (dbl i α)) (simplexSet (m + 1)) := by
    rcases hq with h7 | hq0
    · exact integrableOn_coeff Q (dbl i α) (dbl i p) h7 hcrit hBQ
    · exact integrableOn_coeff_cubic Q (dbl i α) (dbl i p) hq0 (by omega) hcrit hBQ
  have hV8 : ∀ z' : Fin (m + 2) → ℝ, (∀ j, 0 ≤ z' j) → ∑ j, z' j = 1 →
      symanzikU (dbl i α) z' ≠ 0 → c ≤ symanzikV (dbl i α) (dbl i p) (Fin.snoc M b) z' :=
    symanzikV_dbl_ge i α p M hab.le fun z hz0 hz1 hU =>
      hV z hz0 hz1 hU _ ⟨le_rfl, hab.le⟩
  have hI : IntegrableOn (paramIntegrand Q (dbl i α) (dbl i p) (Fin.snoc M b) 0)
      (simplexSet (m + 1)) := by
    rcases hq with h7 | hq0
    · exact integrableOn_paramIntegrand_zero Q (dbl i α) (dbl i p) _ h7 hcrit hBQ hc hV8
    · exact integrableOn_paramIntegrand_zero_cubic Q (dbl i α) (dbl i p) _ hq0 (by omega)
        hcrit hBQ hc hV8
  have hVy : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      ∀ u ∈ Ioc (M i ^ 2) (b ^ 2),
        c ≤ symanzikV α p (Function.update M i 0) (simplexPoint y) + simplexPoint y i * u :=
    fun y hy hU u hu => by
      have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hy
      exact hV _ hz.1 hz.2 hU u ⟨hu.1.le, hu.2⟩
  obtain ⟨hii, heq⟩ := integral_paramIntegrand_pair_swap hm0 Q i α p M hab hI
    hcoef.1 hcoef.2.1 hcoef.2.2 hspan hc hVy
  rw [show pairDens F α p M i = _ from funext (pairDens_eq hQ α p M i)]
  refine ⟨hii.const_mul _, ?_⟩
  rw [pvOf_const_mul hQ, pvOf_eq hQ, heq]
  rw [intervalIntegral.integral_const_mul, Complex.real_smul]
  push_cast
  have hne : (b : ℂ) ^ 2 - (M i : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (sub_pos.2 hab).ne'
  field_simp

end QED.GradedProof.RPi4

end
