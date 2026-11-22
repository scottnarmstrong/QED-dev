/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestVPiece
public import QED.ChainProof.SetCUnitMDispScale

/-!
# The spatial `L¹` norm of the energy integral for a graph with one rescaled line

Helper level for set (c) (stage L2, the `x`-Fubini of the `repB` classes). To move the bubble's
Feynman-parameter integral `∫₀¹ dx` through the two-loop joint energy-first integral
(`QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_setIntegral`, condition `h₂`) one needs
`∫ dx ∫ d⁶v |g(x, v)| < ∞`, `g(x, v)` the energy integral at fixed `x` and spatial `v`. The value
bound `QED.ChainProof.SetCUnitM.norm_jointEnergyFirstIntegral_scale_le` controls only
`|∫ d⁶v g|`; here the same scaling `κ⁻²` is proved for the spatial `L¹` norm, at fixed `ε > 0`.

For a two-loop integrand `Q(ℓ) ∏ᵢ Dᵢ(ℓ)⁻¹` with `N = m + 1 ≥ 8` lines, `ε > 0` and the
numerator-aware criterion, the energy integral is `m! ∫_Δ (numEnergyValueQuartic)` at every `v`,
and the shell bound `QED.ChainProof.SetANestV.integral_norm_numEnergyValueQuartic_le` bounds the
spatial `L¹` norm of the integrand at each Feynman parameter by a constant (depending on `ε`, the
masses and momenta, not on `α`) times `refinedWeight 2 E α`. For the graph with the line `i₀`
rescaled by `κ ∈ (0, 1]` (`σᵢ αᵢ`, `σᵢ pᵢ`, any masses) the weight is
`refinedWeight 2 E α (σ² z)`, and it is at most the homogeneous extension of
`refinedWeight 2 E α|_Δ` at `σ² z` when `|E| + 4 ≤ N`; the Cheng–Wu rescaling
`QED.ChainProof.SetCUnitM.integral_simplex_lineWeights` then gives the factor `κ⁻²`.

* **`integral_norm_energyIntegral_le_refinedWeight`**: for any graph,
  `∫ d⁶v |∫ dt Q ∏ Dᵢ⁻¹| ≤ m! numConst · ∫_Δ refinedWeight 2 E α`, with both stages integrable;
* `homExt`, `homExt_smul`: the homogeneous extension of a function on the simplex;
* `lineQuad_lineScale`, `refinedWeight_lineScale`, `refinedWeight_smul_le`: the weight of
  rescaled lines;
* **`integral_refinedWeight_lineScale_le`**:
  `∫_Δ refinedWeight 2 E (σ α) ≤ κ⁻² ∫_Δ refinedWeight 2 E α`;
* **`integral_norm_energyIntegral_scale_le`**, **`integral_norm_energyIntegral_scale_le'`**: the
  spatial `L¹` norm of the energy integral of the graph with one rescaled line is at most `κ⁻² C`,
  `C` independent of `κ` (and of the masses under a bound `K` on their squares).
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Integration.TwoLoop (symanzikU symanzikMatrix LoopQuartic NoSubdivergenceRefined
  RefinedBound lineDenom loopMomenta numEnergyValueQuartic refinedWeight lineWeight lineQuad
  pairDet loopNorm)
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.ChainProof.SetANestV (numConst shellConst_nonneg integral_norm_numEnergyValueQuartic_le)

/-! ### The spatial `L¹` bound of the energy integral -/

section Engine

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

theorem numConst_nonneg {Cb b K ε : ℝ} (hCb : 0 ≤ Cb) (hb : 0 ≤ b) (hK : 0 ≤ K) (hε : 0 < ε) :
    0 ≤ numConst m Cb b K ε := by
  unfold numConst
  have hs := fun j n => shellConst_nonneg (j := j) (n := n) hb hK hε
  have := hs 2 m; have := hs 2 (m - 1); have := hs 1 (m - 1); have := hs 0 (m - 2)
  positivity

/-- **The spatial `L¹` norm of the energy integral** of `Q ∏ᵢ Dᵢ⁻¹` (`N = m + 1 ≥ 8` lines,
`ε > 0`, the numerator-aware criterion, `‖Q(ℓ)‖ ≤ C_b w_E(A) (1 + ℓᵀAℓ)²`): both stages are
integrable and `∫ d⁶v |∫ dt Q ∏ Dᵢ⁻¹| ≤ m! numConst m C_b b K ε ∫_Δ refinedWeight 2 E α`, for
`b ≥ 1 + 2 Σᵢ |pᵢ|²` and `K ≥ Σᵢ (Mᵢ² + |pᵢ|²)`. -/
theorem integral_norm_energyIntegral_le_refinedWeight (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hB : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
      ‖Q.eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + loopNorm A ℓ) ^ 2)
    {b K : ℝ} (hb : 1 + 2 * ∑ i, ∑ μ, p i μ ^ 2 ≤ b) (hK : ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ => Q.eval (loopMomenta t v) *
        ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) ∧
      Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ, Q.eval (loopMomenta t v) *
        ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t : Fin 2 → ℝ, Q.eval (loopMomenta t v) *
        ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹‖ ≤
        (m.factorial : ℝ) * numConst m Cb b K ε *
          ∫ x in simplexSet m, refinedWeight 2 E α (simplexPoint x) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    QED.Integration.TwoLoop.NoSubdivergence.span (α := α) fun i => by
      have := hcrit.noSubdivergenceOfOrder i; omega
  have hW := QED.Integration.TwoLoop.integrableOn_refinedWeight_of_criterion α 2 E hcrit
  have hRB : RefinedBound α E 4 Q.eval := by
    refine ⟨Cb, hCb, fun A hA ℓ => (hB A hA ℓ).trans_eq ?_⟩
    have hL := QED.Integration.TwoLoop.loopNorm_nonneg hA ℓ
    have e : Real.sqrt (1 + loopNorm A ℓ) ^ 4 = (1 + loopNorm A ℓ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith)]
    rw [e]
  have hE := fun v => QED.Integration.TwoLoop.integrable_eval_mul_paramDenom_prod_of_refined
    Q α p M (by omega) hε hspan hRB hW v
  have hA' := fun v =>
    QED.Integration.TwoLoop.integral_loopQuartic_mul_prod_lineDenom_eq_of_integrable Q α p M
      (by omega) hε hspan v (hE v)
  have hSint : Integrable (fun q : (Fin m → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
      numEnergyValueQuartic Q α p M ε q.1 q.2) ((volume.restrict (simplexSet m)).prod volume) :=
    QED.Integration.TwoLoop.integrable_numEnergyValueQuartic_of_refined Q α p M hm hε hspan hRB
      hW
  have hJ : (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ, Q.eval (loopMomenta t v) *
      ∏ i, (lineDenom α p M ε i (loopMomenta t v))⁻¹) = fun v =>
      (m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic Q α p M ε x v :=
    funext fun v => (hA' v).2
  refine ⟨fun v => (hA' v).1, ?_, ?_⟩
  · rw [hJ]
    exact hSint.integral_prod_right.const_mul _
  simp only [fun v => (hA' v).2]
  have hpt : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ∫ v, ‖numEnergyValueQuartic Q α p M ε x v‖ ≤
        numConst m Cb b K ε * refinedWeight 2 E α (simplexPoint x) := by
    filter_upwards [QED.Integration.TwoLoop.ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    exact (integral_norm_numEnergyValueQuartic_le α p M Q (Or.inl hm) hε hxS hPD E hCb le_rfl
      (fun A hA ℓ => by simpa using hB A hA ℓ) (by simpa using hb) hK).2
  calc ∫ v, ‖(m.factorial : ℂ) * ∫ x in simplexSet m, numEnergyValueQuartic Q α p M ε x v‖
      = (m.factorial : ℝ) * ∫ v, ‖∫ x in simplexSet m, numEnergyValueQuartic Q α p M ε x v‖ := by
        simp only [norm_mul, Complex.norm_natCast]; rw [integral_const_mul]
    _ ≤ (m.factorial : ℝ) * ∫ v, ∫ x in simplexSet m, ‖numEnergyValueQuartic Q α p M ε x v‖ := by
        refine mul_le_mul_of_nonneg_left (integral_mono hSint.integral_prod_right.norm
          hSint.norm.integral_prod_right fun v => norm_integral_le_integral_norm _) (by positivity)
    _ = (m.factorial : ℝ) * ∫ x in simplexSet m, ∫ v, ‖numEnergyValueQuartic Q α p M ε x v‖ := by
        rw [integral_integral_swap (f := fun x v => ‖numEnergyValueQuartic Q α p M ε x v‖)
          hSint.norm]
    _ ≤ (m.factorial : ℝ) * ∫ x in simplexSet m,
          numConst m Cb b K ε * refinedWeight 2 E α (simplexPoint x) :=
        mul_le_mul_of_nonneg_left (integral_mono_ae hSint.norm.integral_prod_left
          (hW.const_mul _) hpt) (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

end Engine

/-! ### The homogeneous extension of a function on the simplex -/

section HomExt

variable {m : ℕ}

/-- The extension `z ↦ (Σ z)^{-(m+1)} G(z / Σ z)` of `G|_Δ`, homogeneous of degree `-(m+1)`. -/
noncomputable def homExt (G : (Fin (m + 1) → ℝ) → ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  ((∑ k, z k) ^ (m + 1))⁻¹ * G ((∑ k, z k)⁻¹ • z)

theorem homExt_smul (G : (Fin (m + 1) → ℝ) → ℝ) (z : Fin (m + 1) → ℝ) {t : ℝ} (ht : 0 < t) :
    homExt G (t • z) = (t ^ (m + 1))⁻¹ • homExt G z := by
  have hs : ∑ k, (t • z) k = t * ∑ k, z k := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have hv : (t * ∑ k, z k)⁻¹ • t • z = (∑ k, z k)⁻¹ • z := by
    rw [smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
  rw [homExt, homExt, hs, hv, smul_eq_mul, mul_pow, mul_inv]
  ring

theorem homExt_simplexPoint (G : (Fin (m + 1) → ℝ) → ℝ) (x : Fin m → ℝ) :
    homExt G (simplexPoint x) = G (simplexPoint x) := by
  rw [homExt, QED.Integration.TwoLoop.sum_simplexPoint]
  simp

end HomExt

/-! ### The weight of rescaled lines -/

section Weight

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)

theorem lineQuad_lineScale (σ : Fin (m + 1) → ℝ) (e : Fin (m + 1)) (z : Fin (m + 1) → ℝ) :
    lineQuad (fun i => σ i • α i) e z = σ e ^ 2 * lineQuad α e fun i => σ i ^ 2 * z i := by
  simp only [lineQuad, pairDet, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem lineQuad_smul (e : Fin (m + 1)) (z : Fin (m + 1) → ℝ) (t : ℝ) :
    lineQuad α e (t • z) = t * lineQuad α e z := by
  simp only [lineQuad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The weight of rescaled lines with scale `±1` on the numerator lines is that of the original
lines at `σ² z`. -/
theorem refinedWeight_lineScale (k : ℕ) {E : Finset (Fin (m + 1))} {σ : Fin (m + 1) → ℝ}
    (hσ : ∀ e ∈ E, σ e = 1) (z : Fin (m + 1) → ℝ) :
    refinedWeight k E (fun i => σ i • α i) z = refinedWeight k E α fun i => σ i ^ 2 * z i := by
  unfold refinedWeight
  rw [symanzikU_scale]
  congr 1
  refine Finset.prod_congr rfl fun e he => ?_
  rw [lineQuad_lineScale, hσ e he]
  simp

/-- **The weight below the homogeneous extension**: at `w = S y` with `0 < S ≤ 1`, `y` in the
standard simplex with `U(y) > 0`, and `|E| + 4 ≤ m + 1`,
`refinedWeight 2 E α (S y) ≤ S^{-(m+1)} refinedWeight 2 E α y`. -/
theorem refinedWeight_smul_le {E : Finset (Fin (m + 1))} (hE : E.card + 4 ≤ m + 1)
    {y : Fin (m + 1) → ℝ} (hy : ∀ k, 0 ≤ y k) (hU : 0 < symanzikU α y) {S : ℝ} (hS0 : 0 < S)
    (hS1 : S ≤ 1) :
    refinedWeight 2 E α (S • y) ≤ (S ^ (m + 1))⁻¹ * refinedWeight 2 E α y := by
  unfold refinedWeight
  rw [QED.ChainProof.SetAKS.ksN_symanzikU_smul]
  have hq : ∀ e, 0 ≤ lineQuad α e y / symanzikU α y := fun e =>
    div_nonneg (QED.Integration.TwoLoop.lineQuad_nonneg α e hy) hU.le
  have hfac : ∀ e ∈ E, Real.sqrt (1 + lineQuad α e (S • y) / (S ^ 2 * symanzikU α y)) ≤
      S⁻¹ * Real.sqrt (1 + lineQuad α e y / symanzikU α y) := fun e _ => by
    have e1 : lineQuad α e (S • y) / (S ^ 2 * symanzikU α y) =
        S⁻¹ * (lineQuad α e y / symanzikU α y) := by
      rw [lineQuad_smul]; field_simp
    rw [e1]
    have h0 := hq e
    generalize lineQuad α e y / symanzikU α y = r at h0 ⊢
    have hSi : 1 ≤ S⁻¹ := (one_le_inv₀ hS0).2 hS1
    rw [show S⁻¹ * Real.sqrt (1 + r) = Real.sqrt ((S⁻¹) ^ 2 * (1 + r)) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    have h1 := mul_nonneg (mul_nonneg h0 (zero_le_one.trans hSi)) (sub_nonneg.2 hSi)
    have h2 := mul_nonneg (sub_nonneg.2 hSi) (add_nonneg (zero_le_one.trans hSi) zero_le_one)
    nlinarith
  have hprod := Finset.prod_le_prod₀ (fun e _ => Real.sqrt_nonneg _) hfac
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have hP0 : 0 ≤ ∏ e ∈ E, Real.sqrt (1 + lineQuad α e y / symanzikU α y) :=
    Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  have hpow : (S⁻¹) ^ E.card * ((S ^ 2) ^ 2)⁻¹ ≤ (S ^ (m + 1))⁻¹ := by
    have e : S⁻¹ ^ E.card * ((S ^ 2) ^ 2)⁻¹ = S⁻¹ ^ (E.card + 4) := by
      rw [pow_add]; simp only [inv_pow]; ring
    rw [e, ← inv_pow]
    exact pow_le_pow_right₀ ((one_le_inv₀ hS0).2 hS1) (by omega)
  calc (((S ^ 2 * symanzikU α y) ^ 2)⁻¹ *
        ∏ e ∈ E, Real.sqrt (1 + lineQuad α e (S • y) / (S ^ 2 * symanzikU α y)))
      ≤ ((S ^ 2 * symanzikU α y) ^ 2)⁻¹ *
          ((S⁻¹) ^ E.card * ∏ e ∈ E, Real.sqrt (1 + lineQuad α e y / symanzikU α y)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ((S⁻¹) ^ E.card * ((S ^ 2) ^ 2)⁻¹) * ((symanzikU α y ^ 2)⁻¹ *
          ∏ e ∈ E, Real.sqrt (1 + lineQuad α e y / symanzikU α y)) := by
        rw [mul_pow, mul_inv]; ring
    _ ≤ (S ^ (m + 1))⁻¹ * ((symanzikU α y ^ 2)⁻¹ *
          ∏ e ∈ E, Real.sqrt (1 + lineQuad α e y / symanzikU α y)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)

/-- **The integrated weight of one rescaled line**: with the line `castSucc i` rescaled by
`κ ∈ (0, 1]` (not a numerator line), the others unscaled, and `|E| + 4 ≤ m + 1`,
`∫_Δ refinedWeight 2 E (σ α) ≤ κ⁻² ∫_Δ refinedWeight 2 E α`. -/
theorem integral_refinedWeight_lineScale_le {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hE : E.card + 4 ≤ m + 1) {i j : Fin m} (hij : i ≠ j)
    (hiE : Fin.castSucc i ∉ E) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {σ : Fin (m + 1) → ℝ}
    (hσi : σ (Fin.castSucc i) = κ) (hσ : ∀ k, k ≠ Fin.castSucc i → σ k = 1) :
    ∫ x in simplexSet m, refinedWeight 2 E (fun k => σ k • α k) (simplexPoint x) ≤
      (κ ^ 2)⁻¹ * ∫ x in simplexSet m, refinedWeight 2 E α (simplexPoint x) := by
  have hm0 : 0 < m := by have := hcrit.noSubdivergenceOfOrder.le; omega
  have hσ0 : ∀ k, σ k ≠ 0 := fun k => by
    by_cases hk : k = Fin.castSucc i
    · rw [hk, hσi]; exact hκ0.ne'
    · rw [hσ k hk]; exact one_ne_zero
  have hσE : ∀ e ∈ E, σ e = 1 := fun e he => hσ e fun h => hiE (h ▸ he)
  have ha : 0 < κ ^ 2 := by positivity
  have hd : (fun k => σ k ^ 2) = lineWeights i (κ ^ 2) := by
    funext k
    by_cases hk : k = Fin.castSucc i
    · rw [hk, hσi, lineWeights, Function.update_self]
    · rw [hσ k hk, lineWeights, Function.update_of_ne hk]; simp
  set G : (Fin (m + 1) → ℝ) → ℝ := refinedWeight 2 E α
  have hH : ∀ z : Fin (m + 1) → ℝ, ∀ t : ℝ, 0 < t →
      homExt G (t • z) = (t ^ (m + 1))⁻¹ • homExt G z := fun z t ht => homExt_smul G z ht
  have hW := QED.Integration.TwoLoop.integrableOn_refinedWeight_of_criterion α 2 E hcrit
  have hW' : IntegrableOn (fun x => homExt G (simplexPoint x)) (simplexSet m) := by
    simpa only [homExt_simplexPoint] using hW
  have hI := (integrableOn_simplex_lineWeights_iff _ hH hij ha).2 hW'
  have hint := integral_simplex_lineWeights _ hH hij ha
  simp only [homExt_simplexPoint, smul_eq_mul] at hint
  rw [← hint]
  have hspan' : ∃ i j, (σ i • α i) 0 * (σ j • α j) 1 - (σ i • α i) 1 * (σ j • α j) 0 ≠ 0 :=
    QED.Integration.TwoLoop.NoSubdivergence.span (α := fun k => σ k • α k) fun i => by
      have := (noSubdivergenceRefined_lineScale hcrit hσ0).noSubdivergenceOfOrder i; omega
  refine integral_mono_of_nonneg ?_ hI ?_
  · refine ae_restrict_of_forall_mem (QED.Integration.Feynman.measurableSet_simplexSet m)
      fun x hx => ?_
    simp only [Pi.zero_apply]
    rw [QED.Integration.TwoLoop.refinedWeight_eq_lineWeight]
    exact mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (QED.Integration.TwoLoop.lineWeight_nonneg _ _ _)
  filter_upwards [QED.Integration.TwoLoop.ae_posDef (fun k => σ k • α k) hm0 hspan'] with x
    ⟨hxS, hPD⟩
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  set z := simplexPoint x
  set w : Fin (m + 1) → ℝ := fun k => lineWeights i (κ ^ 2) k * z k
  have hw0 : ∀ k, κ ^ 2 ≤ lineWeights i (κ ^ 2) k := fun k => by
    by_cases hk : k = Fin.castSucc i
    · rw [hk, lineWeights, Function.update_self]
    · rw [lineWeights, Function.update_of_ne hk, Pi.one_apply]; nlinarith
  have hw1 : ∀ k, lineWeights i (κ ^ 2) k ≤ 1 := fun k => by
    by_cases hk : k = Fin.castSucc i
    · rw [hk, lineWeights, Function.update_self]; nlinarith
    · rw [lineWeights, Function.update_of_ne hk]; simp
  set S := ∑ k, w k
  have hSlo : κ ^ 2 ≤ S := by
    calc κ ^ 2 = ∑ k, κ ^ 2 * z k := by rw [← Finset.mul_sum, hz.2, mul_one]
      _ ≤ S := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hw0 k) (hz.1 k)
  have hShi : S ≤ 1 := by
    calc S ≤ ∑ k, z k := Finset.sum_le_sum fun k _ => by
          have := hz.1 k; nlinarith [hw1 k]
      _ = 1 := hz.2
  have hS0 : 0 < S := ha.trans_le hSlo
  set y : Fin (m + 1) → ℝ := S⁻¹ • w
  have hwy : w = S • y := by simp only [y, smul_smul, mul_inv_cancel₀ hS0.ne', one_smul]
  have hy0 : ∀ k, 0 ≤ y k := fun k => by
    simp only [y, w, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hS0.le) (mul_nonneg (ha.le.trans (hw0 k)) (hz.1 k))
  have hUw : 0 < symanzikU α w := by
    have h := hPD.det_pos
    change 0 < symanzikU (fun k => σ k • α k) z at h
    rw [symanzikU_scale] at h
    simpa only [w, ← hd] using h
  have hUy : 0 < symanzikU α y := by
    rw [hwy, QED.ChainProof.SetAKS.ksN_symanzikU_smul] at hUw
    exact pos_of_mul_pos_right hUw (by positivity)
  have hext : homExt G w = (S ^ (m + 1))⁻¹ * G y := rfl
  change refinedWeight 2 E (fun k => σ k • α k) z ≤ homExt G w
  rw [refinedWeight_lineScale α 2 hσE, hext]
  have e1 : (fun k => σ k ^ 2 * z k) = w := by funext k; simp only [w, ← hd]
  rw [e1, hwy]
  exact refinedWeight_smul_le α hE hy0 hUy hS0 hShi

end Weight

/-! ### One rescaled line: the spatial `L¹` norm with the factor `κ⁻²` -/

section Scale

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)

theorem lineWeight_lineScale {E : Finset (Fin (m + 1))} {σ : Fin (m + 1) → ℝ}
    (hσ : ∀ e ∈ E, σ e = 1) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    lineWeight (fun k => σ k • α k) E A = lineWeight α E A :=
  Finset.prod_congr rfl fun e he => by simp only [hσ e he, one_smul]

theorem sum_sq_lineScale_le {σ : Fin (m + 1) → ℝ} (hσ : ∀ k, σ k ^ 2 ≤ 1) :
    ∑ i, ∑ μ, (σ i • p i) μ ^ 2 ≤ ∑ i, ∑ μ, p i μ ^ 2 :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => by
    rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (hσ i)

/-- **The spatial `L¹` norm of the energy integral with one rescaled line.** Let the line
`castSucc i` (not a numerator line) be rescaled by `κ ∈ (0, 1]` (momentum `κ k`), the others
unscaled, the masses `M'` arbitrary, and let the criterion and the numerator bound hold for the
original lines, with `|E| + 4 ≤ m + 1`. Then at every `ε > 0` both stages are integrable and
`∫ d⁶v |∫ dt Q ∏ D'ᵢ⁻¹| ≤ κ⁻² m! numConst m C_b b K ε ∫_Δ refinedWeight 2 E α`, for
`b ≥ 1 + 2 Σ |pᵢ|²` and `K ≥ Σ (M'ᵢ² + |pᵢ|²)`: a constant independent of `κ`. -/
theorem integral_norm_energyIntegral_scale_le (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hE : E.card + 4 ≤ m + 1) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hB : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef → ∀ ℓ,
      ‖Q.eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + loopNorm A ℓ) ^ 2)
    {i j : Fin m} (hij : i ≠ j) (hiE : Fin.castSucc i ∉ E) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {σ : Fin (m + 1) → ℝ} (hσi : σ (Fin.castSucc i) = κ) (hσ : ∀ k, k ≠ Fin.castSucc i → σ k = 1)
    (M' : Fin (m + 1) → ℝ) {b K : ℝ} (hb : 1 + 2 * ∑ i, ∑ μ, p i μ ^ 2 ≤ b)
    (hK : ∑ i, (M' i ^ 2 + ∑ μ, p i μ ^ 2) ≤ K) {ε : ℝ} (hε : 0 < ε) :
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ => Q.eval (loopMomenta t v) *
        ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k (loopMomenta t v))⁻¹) ∧
      Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ, Q.eval (loopMomenta t v) *
        ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k (loopMomenta t v))⁻¹) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t : Fin 2 → ℝ, Q.eval (loopMomenta t v) *
        ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k (loopMomenta t v))⁻¹‖ ≤
        (κ ^ 2)⁻¹ * ((m.factorial : ℝ) * numConst m Cb b K ε *
          ∫ x in simplexSet m, refinedWeight 2 E α (simplexPoint x)) := by
  have hσ0 : ∀ k, σ k ≠ 0 := fun k => by
    by_cases hk : k = Fin.castSucc i
    · rw [hk, hσi]; exact hκ0.ne'
    · rw [hσ k hk]; exact one_ne_zero
  have hσ1 : ∀ k, σ k ^ 2 ≤ 1 := fun k => by
    by_cases hk : k = Fin.castSucc i
    · rw [hk, hσi]; nlinarith
    · rw [hσ k hk]; norm_num
  have hσE : ∀ e ∈ E, σ e = 1 := fun e he => hσ e fun h => hiE (h ▸ he)
  have hpp := sum_sq_lineScale_le p hσ1
  have hb' : 1 + 2 * ∑ i, ∑ μ, (σ i • p i) μ ^ 2 ≤ b := by linarith
  have hK' : ∑ i, (M' i ^ 2 + ∑ μ, (σ i • p i) μ ^ 2) ≤ K := by
    rw [Finset.sum_add_distrib] at hK ⊢; linarith
  have h := integral_norm_energyIntegral_le_refinedWeight Q (fun k => σ k • α k)
    (fun k => σ k • p k) M' hm (noSubdivergenceRefined_lineScale hcrit hσ0) hCb
    (fun A hA ℓ => by rw [lineWeight_lineScale α hσE]; exact hB A hA ℓ) hb' hK' hε
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  have hb0 : 0 ≤ b := by
    have : 0 ≤ ∑ i, ∑ μ, p i μ ^ 2 := by positivity
    linarith
  have hK0 : 0 ≤ K := (Finset.sum_nonneg fun i _ => by positivity).trans hK
  have hc := numConst_nonneg (m := m) hCb hb0 hK0 hε
  have hW := integral_refinedWeight_lineScale_le α hcrit hE hij hiE hκ0 hκ1 hσi hσ
  calc (m.factorial : ℝ) * numConst m Cb b K ε *
        ∫ x in simplexSet m, refinedWeight 2 E (fun k => σ k • α k) (simplexPoint x)
      ≤ (m.factorial : ℝ) * numConst m Cb b K ε *
          ((κ ^ 2)⁻¹ * ∫ x in simplexSet m, refinedWeight 2 E α (simplexPoint x)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by ring

/-- **One rescaled line at any position** (`m ≥ 7`): one constant `C`, independent of the scale
`κ ∈ (0, 1]` and of the masses `M'` with `Σ (M'ᵢ² + |pᵢ|²) ≤ K`, with
`∫ d⁶v |∫ dt Q ∏ D'ᵢ⁻¹| ≤ κ⁻² C` at the fixed `ε > 0`, both stages integrable. -/
theorem integral_norm_energyIntegral_scale_le' (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval)
    (hE : E.card + 4 ≤ m + 1) {i₀ : Fin (m + 1)} (hiE : i₀ ∉ E) {b K : ℝ}
    (hb : 1 + 2 * ∑ i, ∑ μ, p i μ ^ 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : ℝ) (σ : Fin (m + 1) → ℝ) (M' : Fin (m + 1) → ℝ), 0 < κ → κ ≤ 1 →
      σ i₀ = κ → (∀ k, k ≠ i₀ → σ k = 1) → ∑ i, (M' i ^ 2 + ∑ μ, p i μ ^ 2) ≤ K →
      (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ => Q.eval (loopMomenta t v) *
        ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k (loopMomenta t v))⁻¹) ∧
      Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ, Q.eval (loopMomenta t v) *
        ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k (loopMomenta t v))⁻¹) ∧
      ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t : Fin 2 → ℝ, Q.eval (loopMomenta t v) *
        ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k (loopMomenta t v))⁻¹‖ ≤
        (κ ^ 2)⁻¹ * C := by
  set i : Fin m := ⟨0, by omega⟩
  set j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  set τ := Equiv.swap (Fin.castSucc i) i₀
  set E' := E.map τ.symm.toEmbedding
  have hcrit' : NoSubdivergenceRefined 2 E' (fun k => α (τ k)) := by
    have h := noSubdivergenceRefined_scale_comp hcrit τ τ.symm.toEmbedding
      (fun k => by simp) (fun _ => 1) (fun _ => one_ne_zero)
    simpa using h
  have hB' : RefinedBound (fun k => α (τ k)) E' 4 Q.eval :=
    refinedBound_map τ.symm.toEmbedding (fun e _ => by simp) hB
  obtain ⟨Cb, hCb, hB''⟩ := hB'.exists_le_sq
  have hE' : E'.card + 4 ≤ m + 1 := by rw [Finset.card_map]; exact hE
  have hiE' : Fin.castSucc i ∉ E' := by
    simp only [E', Finset.mem_map_equiv, Equiv.symm_symm]
    simpa [τ] using hiE
  have hpτ : ∑ k, ∑ μ, p (τ k) μ ^ 2 = ∑ k, ∑ μ, p k μ ^ 2 :=
    Equiv.sum_comp τ (fun k => ∑ μ, p k μ ^ 2)
  have hb' : 1 + 2 * ∑ k, ∑ μ, p (τ k) μ ^ 2 ≤ b := by rw [hpτ]; exact hb
  refine ⟨max 0 ((m.factorial : ℝ) * numConst m Cb b K ε *
    ∫ x in simplexSet m, refinedWeight 2 E' (fun k => α (τ k)) (simplexPoint x)), le_max_left _ _,
    fun κ σ M' hκ0 hκ1 hσi hσ hK => ?_⟩
  have hKτ : ∑ k, (M' (τ k) ^ 2 + ∑ μ, p (τ k) μ ^ 2) ≤ K := by
    rw [Equiv.sum_comp τ (fun k => M' k ^ 2 + ∑ μ, p k μ ^ 2)]; exact hK
  have h := integral_norm_energyIntegral_scale_le Q (fun k => α (τ k)) (fun k => p (τ k)) hm
    hcrit' hE' hCb hB'' hij hiE' hκ0 hκ1 (σ := fun k => σ (τ k)) (by simp [τ, hσi])
    (fun k hk => hσ _ (by intro h; apply hk; simpa [τ] using congrArg τ h))
    (fun k => M' (τ k)) hb' hKτ hε
  have key : ∀ ℓ, ∏ k, (lineDenom (fun k => σ (τ k) • α (τ k)) (fun k => σ (τ k) • p (τ k))
      (fun k => M' (τ k)) ε k ℓ)⁻¹ =
      ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k ℓ)⁻¹ := fun ℓ =>
    Equiv.prod_comp τ (fun k => (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k
      ℓ)⁻¹)
  simp only [key] at h
  exact ⟨h.1, h.2.1, h.2.2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))⟩

end Scale

end QED.ChainProof.SetCUnitM

end
