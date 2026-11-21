/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecKin
public import QED.Integration.TwoLoopClassLimitCubic
public import QED.TwoLoop.VPHalfAtGenSpec

/-!
# Set (a): the fixed-`ε` spectral form of one two-loop vacuum-polarization piece

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
A *piece* is a two-loop joint energy-first integral `∫ P(ℓ) ∏ᵢ Dᵢ(ℓ)⁻¹` with line momenta
`cᵢ k` (two-point kinematics), `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε`, a numerator of degree at most four with the
refined bound and the refined no-subdivergence criterion: the form of the Pauli–Villars pieces of
the classes `VA`, `VB`, `VC` (`QED.GradedProof.VP2.jef_vBlock`). At fixed `ε > 0` and for **every**
`k ∈ ℝ⁴` (timelike above threshold included), such a piece is a superposition over the Feynman
simplex of powers of one photon-type factor:

`∫ P ∏ D⁻¹ = -π⁴ ∫_Δ (T₁ F^{-(m-3)} + T₂ F^{-(m-4)} + T₃ F^{-(m-5)})`,
`F(x, k) = fDen (√a(x)) ε ξ(x) k = a + ξ(1 - ξ) k² - iε`,

with the coefficients `Tₐ` of `QED.TwoLoop.ClassLimit.paramIntegrand_eq`, independent of `ε` and
integrable on the simplex (`QED.TwoLoop.ClassLimit.integrableOn_coeff`, `…_cubic`), the mass
`√a = √(∑ zᵢ Mᵢ²) ≥ M_lo`, and `ξ ∈ (0, 1)` almost everywhere. Equivalently
`F = ξ(1 - ξ) (k² + a/(ξ(1 - ξ)) - iε/(ξ(1 - ξ)))`: a propagator of mass² `a/w ≥ 4 m₀²`
(`QED.ChainProof.SetASpec.setASpec_threshold`) with prescription `ε/w`.

* `saPieceSpec`: the spectral integrand;
* `setASpec_paramIntegrand_eq_pieceSpec`: it is the parametric integrand off a null set;
* **`setASpec_piece_eq_spectral`** (`N ≥ 8` lines) and **`setASpec_piece_eq_spectral_cubic`**
  (`N ≥ 7` lines, cubic numerator): the fixed-`ε` spectral form of a piece;
* `setASpec_ae_mass_ge`, `setASpec_ae_saXi_mem_Ioo`: the hypotheses of the spectral engine
  `QED.TwoLoop.VPHalfAtGen.exists_good_specInt` on the parameters, almost everywhere;
* `setASpec_specInt_const`: `r` copies of the factor on an outer integrand are
  `QED.TwoLoop.VPHalfAtGen.specInt` with constant masses and Feynman parameters.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.VPHalfAtAssembly
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (c M : Fin (m + 1) → ℝ)

/-! ### The spectral integrand -/

/-- The mass `√a(x) = √(∑ᵢ zᵢ Mᵢ²)` of the photon-type factor at the simplex point `x`. -/
noncomputable def saMass (x : Fin m → ℝ) : ℝ := Real.sqrt (saMassSq M (simplexPoint x))

/-- The Feynman parameter `ξ(x)`, `ξ(1 - ξ) = w(x)`, of the factor at the simplex point `x`. -/
noncomputable def saXiAt (x : Fin m → ℝ) : ℝ := saXi (remainder α (simplexPoint x) c)

/-- **The spectral integrand of a piece**: the coefficients of the parametric integrand at the
line momenta `cᵢ k`, times powers of the photon-type factor
`fDen (saMass x) ε (saXiAt x) k = a + ξ(1 - ξ) k² - iε`. -/
noncomputable def saPieceSpec (ε : ℝ) (k : Fin 4 → ℝ) (x : Fin m → ℝ) : ℂ :=
  coeffOne P α (fun i => c i • k) x *
      (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 3))⁻¹ +
    coeffTwo P α (fun i => c i • k) x *
      (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 4))⁻¹ +
    coeffThree P α x * (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 5))⁻¹

variable {α c}

/-- The spectral integrand is the parametric integrand at every simplex point with `U ≠ 0`. -/
theorem setASpec_paramIntegrand_eq_pieceSpec (y : Fin 2 → ℝ)
    (hy : ∀ i, (∑ s, α i s * y s + c i) ^ 2 ≤ 1 / 4) {x : Fin m → ℝ} (hx : x ∈ simplexSet m)
    (hU : symanzikU α (simplexPoint x) ≠ 0) (ε : ℝ) (k : Fin 4 → ℝ) :
    paramIntegrand P α (fun i => c i • k) M ε x = saPieceSpec P α c M ε k x := by
  rw [paramIntegrand_eq, saPieceSpec, setASpec_wBase_eq_fDen α M c y hy hx hU]
  rfl

theorem setASpec_hspan {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α) :
    ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
  NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega

/-- The integrals of the parametric and the spectral integrand agree. -/
theorem setASpec_integral_paramIntegrand_eq (hm : 0 < m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (y : Fin 2 → ℝ)
    (hy : ∀ i, (∑ s, α i s * y s + c i) ^ 2 ≤ 1 / 4) (ε : ℝ) (k : Fin 4 → ℝ) :
    ∫ x in simplexSet m, paramIntegrand P α (fun i => c i • k) M ε x =
      ∫ x in simplexSet m, saPieceSpec P α c M ε k x := by
  refine integral_congr_ae ?_
  filter_upwards [ae_posDef α hm (setASpec_hspan hcrit)] with x ⟨hxS, hPD⟩
  exact setASpec_paramIntegrand_eq_pieceSpec P M y hy hxS hPD.det_pos.ne' ε k

/-! ### The spectral form of a piece -/

/-- **The fixed-`ε` spectral form of a piece with at least eight lines.** For `ε > 0`, every
`k ∈ ℝ⁴`, the refined criterion and bound, and a flow certificate `y`:
`∫ P ∏ D⁻¹ = -π⁴ ∫_Δ saPieceSpec`. -/
theorem setASpec_piece_eq_spectral (hm : 7 ≤ m) {ε : ℝ} (hε : 0 < ε)
    {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 P.eval) (y : Fin 2 → ℝ)
    (hy : ∀ i, (∑ s, α i s * y s + c i) ^ 2 ≤ 1 / 4) (k : Fin 4 → ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α (fun i => c i • k) M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, saPieceSpec P α c M ε k x := by
  rw [← setASpec_integral_paramIntegrand_eq P M (by omega) hcrit y hy ε k]
  exact (jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined P α
    (fun i => c i • k) M hm hε hcrit hB).2.2

/-- **The fixed-`ε` spectral form of a piece with seven lines and a cubic numerator.** -/
theorem setASpec_piece_eq_spectral_cubic (hq : P.quart = 0) (hm : 6 ≤ m) {ε : ℝ} (hε : 0 < ε)
    {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 P.eval) (y : Fin 2 → ℝ)
    (hy : ∀ i, (∑ s, α i s * y s + c i) ^ 2 ≤ 1 / 4) (k : Fin 4 → ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α (fun i => c i • k) M ε i ℓ)⁻¹) =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, saPieceSpec P α c M ε k x := by
  rw [← setASpec_integral_paramIntegrand_eq P M (by omega) hcrit y hy ε k]
  have hspan := setASpec_hspan hcrit
  have hW := integrableOn_refinedWeight_of_criterion α 2 E hcrit
  exact (jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_integrable P α
    (fun i => c i • k) M hm hε hspan
    (integrable_eval_mul_paramDenom_prod_of_refined P α _ M (by omega) hε hspan hB hW)
    (integrable_numEnergyValueQuartic_of_cubic P α _ M hq hm hε hspan hB hW)).2.2

/-- The spectral integrand is integrable at every `ε > 0` (eight or more lines). -/
theorem setASpec_integrableOn_pieceSpec (hm : 7 ≤ m) {ε : ℝ} (hε : 0 < ε)
    {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 P.eval) (y : Fin 2 → ℝ)
    (hy : ∀ i, (∑ s, α i s * y s + c i) ^ 2 ≤ 1 / 4) (k : Fin 4 → ℝ) :
    IntegrableOn (saPieceSpec P α c M ε k) (simplexSet m) := by
  refine (integrableOn_paramIntegrand P α (fun i => c i • k) M hm hε hcrit hB).congr_fun_ae ?_
  filter_upwards [ae_posDef α (by omega) (setASpec_hspan hcrit)] with x ⟨hxS, hPD⟩
  exact setASpec_paramIntegrand_eq_pieceSpec P M y hy hxS hPD.det_pos.ne' ε k

/-- The spectral integrand is integrable at every `ε > 0` (seven lines, cubic numerator). -/
theorem setASpec_integrableOn_pieceSpec_cubic (hq : P.quart = 0) (hm : 6 ≤ m) {ε : ℝ}
    (hε : 0 < ε) {E : Finset (Fin (m + 1))} (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 P.eval) (y : Fin 2 → ℝ)
    (hy : ∀ i, (∑ s, α i s * y s + c i) ^ 2 ≤ 1 / 4) (k : Fin 4 → ℝ) :
    IntegrableOn (saPieceSpec P α c M ε k) (simplexSet m) := by
  refine (integrableOn_paramIntegrand_cubic P α (fun i => c i • k) M hq hm hε hcrit
    hB).congr_fun_ae ?_
  filter_upwards [ae_posDef α (by omega) (setASpec_hspan hcrit)] with x ⟨hxS, hPD⟩
  exact setASpec_paramIntegrand_eq_pieceSpec P M y hy hxS hPD.det_pos.ne' ε k

/-! ### The parameters satisfy the hypotheses of the spectral engine -/

/-- With every mass at least `M_lo ≥ 0`, the factor mass is at least `M_lo` on the simplex. -/
theorem setASpec_mass_ge {x : Fin m → ℝ} (hx : x ∈ simplexSet m) {Mlo : ℝ} (hMlo : 0 ≤ Mlo)
    (hM : ∀ i, Mlo ≤ M i) : Mlo ≤ saMass M x := by
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
  exact setASpec_le_sqrt_saMassSq hz.1 hz.2 hMlo hM

theorem setASpec_ae_mass_ge {Mlo : ℝ} (hMlo : 0 ≤ Mlo) (hM : ∀ i, Mlo ≤ M i) :
    ∀ᵐ x ∂(volume.restrict (simplexSet m)), Mlo ≤ saMass M x := by
  rw [ae_restrict_iff' (QED.Integration.Feynman.measurableSet_simplexSet m)]
  exact Eventually.of_forall fun x hx => setASpec_mass_ge M hx hMlo hM

/-- **The Feynman parameter of the factor is in `(0, 1)` almost everywhere** when no `y`
annihilates every line. -/
theorem setASpec_ae_saXi_mem_Ioo (hm : 0 < m)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (hc : ∀ y : Fin 2 → ℝ, ∃ i, ∑ s, α i s * y s + c i ≠ 0) :
    ∀ᵐ x ∂(volume.restrict (simplexSet m)), saXiAt α c x ∈ Ioo (0 : ℝ) 1 := by
  have h1 := ae_posDef α hm hspan
  have h2 : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ∀ i, simplexPoint x i ≠ 0 :=
    ae_restrict_of_ae (ae_simplexPoint_ne_zero hm)
  filter_upwards [h1, h2] with x ⟨hxS, hPD⟩ hx0
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  have hzp : ∀ i, 0 < simplexPoint x i := fun i => lt_of_le_of_ne (hz.1 i) (hx0 i).symm
  exact setASpec_saXi_mem_Ioo (setASpec_remainder_pos α hzp hPD.det_pos.ne' c hc)

/-! ### The bridge to `specInt` -/

open QED.TwoLoop.VPHalfAtGen in
/-- **`r` copies of one photon-type factor on an outer integrand** are `specInt` with constant
masses and Feynman parameters. -/
theorem setASpec_specInt_const (N : (Fin 4 → ℝ) → ℂ) (me : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) (r : ℕ) (Msp ξ ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    specInt N me j Ms es (fun _ : Fin r => Msp) (fun _ => ξ) ε p' p ℓ =
      powInt N me j Ms es ε p' p ℓ * (fDen Msp ε ξ ℓ ^ r)⁻¹ := by
  simp [specInt, Finset.prod_const]

end QED.ChainProof.SetASpec

end
