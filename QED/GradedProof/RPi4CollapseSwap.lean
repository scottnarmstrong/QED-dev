/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Collapse

/-!
# (R-Π₄) step L6b′: the photon collapse with the mass integral outside

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6b′ (heavy photon
pair). After the collapse `QED.GradedProof.RPi4.integral_paramIntegrand_pair`, the integral over
the squared photon mass `u` is moved outside the simplex integral (Fubini), so that a piece at the
photon pair `(a, b)` is `(b² - a²)⁻¹ ∫_{a²}^{b²} 𝒫(u) du` with the one-photon-line density
`𝒫(u) = ∫_{Δₘ} zᵢ paramAtV(V₀ + zᵢ u)`.

* `cOneAt`, `cTwoAt`, `cThreeAt`: the coefficients of the parametric integrand at a Feynman point
  (`coeffOne_eq_cOneAt`, … : the simplex coefficients are these at `simplexPoint x`);
  `paramAtV_eq`, `norm_paramAtV_le` (for `v ≥ c > 0`); `cOneAt_dbl`, … (unchanged by a split).
* `integrableOn_mul_of_dbl`: a function on `Δₘ₊₁` that depends on a split pair only through its
  sum gives `zᵢ` times an integrable function on `Δₘ`.
* `integral_paramIntegrand_pair_swap` (**collapse, mass integral outside**): with integrable
  coefficients of the doubled data and `V₀ + zᵢ u ≥ c > 0` for `u ∈ (a², b²]`; the density is
  interval integrable.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.Integration.SimplexMerge
open QED.GradedProof.WI2 (dbl paramAt ehat symanzikU_dbl symanzikMatrix_dbl loopShift_dbl)
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)

variable {m : ℕ}

section Coefficients

variable (n : ℕ) (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (z : Fin (m + 1) → ℝ)

/-- The coefficient of `v^{3-n}` of the parametric integrand at the Feynman point `z`. -/
noncomputable def cOneAt : ℂ :=
  ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ *
    (((n - 4).factorial : ℂ) * Q.evalC (loopComp (-loopShift α p z)))

/-- The coefficient of `v^{4-n}` of the parametric integrand at the Feynman point `z`. -/
noncomputable def cTwoAt : ℂ :=
  ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ *
    (((n - 5).factorial : ℂ) / 2 *
      Q.contractTwo (symanzikMatrix α z) (loopComp (-loopShift α p z)))

/-- The coefficient of `v^{5-n}` of the parametric integrand at the Feynman point `z`. -/
noncomputable def cThreeAt : ℂ :=
  ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ *
    (((n - 6).factorial : ℂ) / 4 * Q.contractFour (symanzikMatrix α z))

theorem paramAtV_eq (v : ℝ) :
    paramAtV n Q α p z v = cOneAt n Q α p z * ((v : ℂ) ^ (n - 3))⁻¹ +
      cTwoAt n Q α p z * ((v : ℂ) ^ (n - 4))⁻¹ + cThreeAt n Q α z * ((v : ℂ) ^ (n - 5))⁻¹ := by
  simp only [paramAtV, ehat, cOneAt, cTwoAt, cThreeAt]
  ring

theorem norm_paramAtV_le {c v : ℝ} (hc : 0 < c) (hv : c ≤ v) :
    ‖paramAtV n Q α p z v‖ ≤ ‖cOneAt n Q α p z‖ * (c ^ (n - 3))⁻¹ +
      ‖cTwoAt n Q α p z‖ * (c ^ (n - 4))⁻¹ + ‖cThreeAt n Q α z‖ * (c ^ (n - 5))⁻¹ := by
  have hv0 : 0 < v := hc.trans_le hv
  have key : ∀ (a : ℂ) (k : ℕ), ‖a * ((v : ℂ) ^ k)⁻¹‖ ≤ ‖a‖ * (c ^ k)⁻¹ := fun a k => by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv0.le]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (pow_pos hc k) (pow_le_pow_left₀ hc.le hv k)) (norm_nonneg _)
  rw [paramAtV_eq]
  exact (norm_add₃_le).trans (add_le_add (add_le_add (key _ _) (key _ _)) (key _ _))

theorem cOneAt_dbl (i : Fin (m + 1)) (t : ℝ) :
    cOneAt n Q (dbl i α) (dbl i p) (splitAt i z t) = cOneAt n Q α p z := by
  simp only [cOneAt, symanzikU_dbl, loopShift_dbl]

theorem cTwoAt_dbl (i : Fin (m + 1)) (t : ℝ) :
    cTwoAt n Q (dbl i α) (dbl i p) (splitAt i z t) = cTwoAt n Q α p z := by
  simp only [cTwoAt, symanzikU_dbl, symanzikMatrix_dbl, loopShift_dbl]

theorem cThreeAt_dbl (i : Fin (m + 1)) (t : ℝ) :
    cThreeAt n Q (dbl i α) (splitAt i z t) = cThreeAt n Q α z := by
  simp only [cThreeAt, symanzikU_dbl, symanzikMatrix_dbl]

end Coefficients

theorem coeffOne_eq_cOneAt (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (x : Fin m → ℝ) :
    coeffOne Q α p x = cOneAt m Q α p (simplexPoint x) := rfl

theorem coeffTwo_eq_cTwoAt (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (x : Fin m → ℝ) :
    coeffTwo Q α p x = cTwoAt m Q α p (simplexPoint x) := rfl

theorem coeffThree_eq_cThreeAt (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (x : Fin m → ℝ) :
    coeffThree Q α x = cThreeAt m Q α (simplexPoint x) := rfl

/-- **Integrability after merging a pair**: if `f` on `Δₘ₊₁` depends on the split pair `(t, zᵢ - t)`
only through its sum (`f (splitAt i z t) = g z`), then `zᵢ g(z)` is integrable on `Δₘ`. -/
theorem integrableOn_mul_of_dbl (hm : 0 < m) (i : Fin (m + 1))
    {f : (Fin (m + 2) → ℝ) → ℂ} {g : (Fin (m + 1) → ℝ) → ℂ} (hfg : ∀ z t, f (splitAt i z t) = g z)
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet (m + 1))) :
    IntegrableOn (fun y => (simplexPoint y i : ℂ) * g (simplexPoint y)) (simplexSet m) := by
  obtain ⟨h1, -⟩ := integral_simplex_splitAt hm i hf
  refine h1.congr_fun (fun y _ => ?_) (measurableSet_simplexSet m)
  dsimp only
  rw [integral_splitAt_of_forall_eq i _ (fun t => by rw [hfg, hfg]), hfg, Complex.real_smul]

/-- **Photon collapse with the mass integral outside.** For a line `i` doubled with masses
`(a, b) = (Mᵢ, b)`, `a² < b²`, integrable coefficients of the doubled data and
`V₀ + zᵢ u ≥ c > 0` on `Δₘ × (a², b²]` where `U ≠ 0`:
`∫_{Δₘ₊₁} paramIntegrand = (b² - a²)⁻¹ ∫_{a²}^{b²} ∫_{Δₘ} zᵢ paramAtV(V₀ + zᵢ u) du`. -/
theorem integral_paramIntegrand_pair_swap (hm : 0 < m) (Q : LoopQuartic) (i : Fin (m + 1))
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) {b : ℝ}
    (hab : M i ^ 2 < b ^ 2)
    (hI : IntegrableOn (paramIntegrand Q (dbl i α) (dbl i p) (Fin.snoc M b) 0)
      (simplexSet (m + 1)))
    (h1 : IntegrableOn (coeffOne Q (dbl i α) (dbl i p)) (simplexSet (m + 1)))
    (h2 : IntegrableOn (coeffTwo Q (dbl i α) (dbl i p)) (simplexSet (m + 1)))
    (h3 : IntegrableOn (coeffThree Q (dbl i α)) (simplexSet (m + 1)))
    (hspan : ∃ j l, α j 0 * α l 1 - α j 1 * α l 0 ≠ 0) {c : ℝ} (hc : 0 < c)
    (hV : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 → ∀ u ∈ Ioc (M i ^ 2) (b ^ 2),
      c ≤ symanzikV α p (Function.update M i 0) (simplexPoint y) + simplexPoint y i * u) :
    IntervalIntegrable (fun u => ∫ y in simplexSet m,
        (simplexPoint y i : ℂ) * paramAtV (m + 1) Q α p (simplexPoint y)
          (symanzikV α p (Function.update M i 0) (simplexPoint y) + simplexPoint y i * u))
        volume (M i ^ 2) (b ^ 2) ∧
    ∫ x in simplexSet (m + 1), paramIntegrand Q (dbl i α) (dbl i p) (Fin.snoc M b) 0 x =
      ((b ^ 2 - M i ^ 2)⁻¹ : ℝ) • ∫ u in M i ^ 2..b ^ 2, ∫ y in simplexSet m,
        (simplexPoint y i : ℂ) * paramAtV (m + 1) Q α p (simplexPoint y)
          (symanzikV α p (Function.update M i 0) (simplexPoint y) + simplexPoint y i * u) := by
  set A := M i ^ 2
  set B := b ^ 2
  set V₀ : (Fin m → ℝ) → ℝ := fun y => symanzikV α p (Function.update M i 0) (simplexPoint y)
  set F : ℝ → (Fin m → ℝ) → ℂ := fun u y =>
    (simplexPoint y i : ℂ) * paramAtV (m + 1) Q α p (simplexPoint y) (V₀ y + simplexPoint y i * u)
  -- the merged coefficients, times `zᵢ`, are integrable
  have k1 := integrableOn_mul_of_dbl hm i (f := cOneAt (m + 1) Q (dbl i α) (dbl i p))
    (g := cOneAt (m + 1) Q α p) (cOneAt_dbl _ Q α p · i) h1
  have k2 := integrableOn_mul_of_dbl hm i (f := cTwoAt (m + 1) Q (dbl i α) (dbl i p))
    (g := cTwoAt (m + 1) Q α p) (cTwoAt_dbl _ Q α p · i) h2
  have k3 := integrableOn_mul_of_dbl hm i (f := cThreeAt (m + 1) Q (dbl i α))
    (g := cThreeAt (m + 1) Q α) (cThreeAt_dbl _ Q α · i) h3
  set K : (Fin m → ℝ) → ℝ := fun y =>
    ‖(simplexPoint y i : ℂ) * cOneAt (m + 1) Q α p (simplexPoint y)‖ * (c ^ (m + 1 - 3))⁻¹ +
      ‖(simplexPoint y i : ℂ) * cTwoAt (m + 1) Q α p (simplexPoint y)‖ * (c ^ (m + 1 - 4))⁻¹ +
      ‖(simplexPoint y i : ℂ) * cThreeAt (m + 1) Q α (simplexPoint y)‖ * (c ^ (m + 1 - 5))⁻¹
  have hK : IntegrableOn K (simplexSet m) :=
    ((k1.norm.mul_const _).add (k2.norm.mul_const _)).add (k3.norm.mul_const _)
  have : IsFiniteMeasure (volume.restrict (uIoc A B)) :=
    isFiniteMeasure_restrict.2 (by simp [uIoc_of_le hab.le])
  have hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (uIoc A B)).prod (volume.restrict (simplexSet m))) := by
    have e : Function.uncurry F = fun q : ℝ × (Fin m → ℝ) =>
        (simplexPoint q.2 i : ℂ) * cOneAt (m + 1) Q α p (simplexPoint q.2) *
            ((((V₀ q.2 + simplexPoint q.2 i * q.1 : ℝ) : ℂ)) ^ (m + 1 - 3))⁻¹ +
          (simplexPoint q.2 i : ℂ) * cTwoAt (m + 1) Q α p (simplexPoint q.2) *
            ((((V₀ q.2 + simplexPoint q.2 i * q.1 : ℝ) : ℂ)) ^ (m + 1 - 4))⁻¹ +
          (simplexPoint q.2 i : ℂ) * cThreeAt (m + 1) Q α (simplexPoint q.2) *
            ((((V₀ q.2 + simplexPoint q.2 i * q.1 : ℝ) : ℂ)) ^ (m + 1 - 5))⁻¹ := by
      funext q
      simp only [Function.uncurry, F, paramAtV_eq]
      ring
    have hz : Measurable fun y : Fin m → ℝ => simplexPoint y i :=
      (continuous_apply i).measurable.comp continuous_simplexPoint'.measurable
    have hV0 : Measurable V₀ :=
      (measurable_symanzikV α p _).comp continuous_simplexPoint'.measurable
    have hw : ∀ k : ℕ, AEStronglyMeasurable (fun q : ℝ × (Fin m → ℝ) =>
        ((((V₀ q.2 + simplexPoint q.2 i * q.1 : ℝ) : ℂ)) ^ k)⁻¹)
        ((volume.restrict (uIoc A B)).prod (volume.restrict (simplexSet m))) := fun k =>
      (((Complex.measurable_ofReal.comp ((hV0.comp measurable_snd).add
        ((hz.comp measurable_snd).mul measurable_fst))).pow_const k).inv).aestronglyMeasurable
    rw [e]
    exact (((k1.comp_snd _).aestronglyMeasurable.mul (hw _)).add
      ((k2.comp_snd _).aestronglyMeasurable.mul (hw _))).add
      ((k3.comp_snd _).aestronglyMeasurable.mul (hw _))
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc A B)).prod (volume.restrict (simplexSet m))) := by
    refine (hK.comp_snd _).mono' hFm ?_
    have hmem : ∀ᵐ q ∂((volume.restrict (uIoc A B)).prod (volume.restrict (simplexSet m))),
        q ∈ uIoc A B ×ˢ simplexSet m := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_uIoc.prod (measurableSet_simplexSet m))
    have hU : ∀ᵐ q ∂((volume.restrict (uIoc A B)).prod (volume.restrict (simplexSet m))),
        symanzikU α (simplexPoint q.2) ≠ 0 :=
      Measure.quasiMeasurePreserving_snd.ae
        (p := fun y => symanzikU α (simplexPoint y) ≠ 0)
        ((ae_posDef α hm hspan).mono fun y hy => hy.2.det_pos.ne')
    filter_upwards [hmem, hU] with q hq hq0
    obtain ⟨hu, hy⟩ := hq
    rw [uIoc_of_le hab.le] at hu
    have hb := norm_paramAtV_le (m + 1) Q α p (simplexPoint q.2) hc (hV q.2 hy hq0 q.1 hu)
    simp only [Function.uncurry, F, K, norm_mul]
    refine (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans (le_of_eq ?_)
    ring
  refine ⟨(intervalIntegrable_iff.2 hFi.integral_prod_left), ?_⟩
  rw [integral_paramIntegrand_pair hm Q i α p M hab.ne hI]
  have hin : ∀ y : Fin m → ℝ, (simplexPoint y i / (B - A)) •
      ∫ u in A..B, paramAtV (m + 1) Q α p (simplexPoint y) (V₀ y + simplexPoint y i * u) =
        ((B - A)⁻¹ : ℝ) • ∫ u in A..B, F u y := fun y => by
    simp only [F]
    rw [intervalIntegral.integral_const_mul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  refine (setIntegral_congr_fun (measurableSet_simplexSet m) fun y _ => hin y).trans ?_
  rw [integral_smul, intervalIntegral_integral_swap hFi]

end QED.GradedProof.RPi4

end
