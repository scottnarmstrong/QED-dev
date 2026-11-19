/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ParamPiece
public import QED.TwoLoop.PauliZeroLimitPiece

/-!
# Self-energy pieces: continuity of the limit along the null ray

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L3 (the origin). For a self-energy piece (`SEPiece`) whose
numerator is polynomial in the momentum at fixed loop momenta, the limit matrix `W` satisfies
`W(t n₀) → W(0)` as `t → 0⁺`, `n₀ = (1, 1, 0, 0)` (`SEPiece.tendsto_nullVec`), the hypothesis of
`exists_seMat_of_cov` at the origin.

## Proof

Along the null ray the external line momenta `cᵢ t n₀` have vanishing Minkowski products, so `V`
does not depend on `t` (`symanzikV_smul_null`). Parametrize `t = u / (1 - u²)`, `u ∈ (-1, 1)`, so
that `(1 - u²)` times the line momenta is polynomial in `u`. By interpolation
(`QED.TwoLoop.PauliZeroLimit.jointQuartic`) the numerators at all `u` are combinations of fixed
quartics with coefficients polynomial in `u` over a power of `1 - u²`, and the value is
`∫_Δ A(x, u) / ((1 - u²)ᵃ V(x)ᴺ)` with `A(x, ·)` polynomial with integrable coefficients
(`QED.TwoLoop.PauliZeroLimit.isUPoly_paramNum`, `integrableOn_paramNum_good`). Such an integral is
continuous at `u = 0` by dominated convergence (`tendsto_integral_upoly`). Finally
`u(t) = 2t / (1 + √(1 + 4t²))` inverts the parametrization and tends to `0`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Matrix Set Polynomial
open scoped Real

namespace QED.GradedProof.SE2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)

/-! ### Continuity of integrals of polynomial families -/

section Cont

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- **Continuity at `u = 0` of `∫ A(·, u) / ((1 - u²)ᵃ Vᴺ)`** for polynomial families `A` with
integrable values at the nodes and `V ≥ c > 0`. -/
theorem tendsto_integral_upoly {D a N : ℕ} {A : ι → ℝ → ℂ} {V : ι → ℝ} {c : ℝ}
    (hA : IsUPoly D A) (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) (hc : 0 < c)
    (hV : ∀ᵐ x ∂μ, c ≤ V x) (hVm : AEStronglyMeasurable (fun x => ((V x : ℝ) : ℂ)) μ) :
    Tendsto (fun u => ∫ x, A x u / (wt u ^ a * (V x : ℂ) ^ N) ∂μ) (𝓝 0)
      (𝓝 (∫ x, A x 0 / (V x : ℂ) ^ N ∂μ)) := by
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  set B : ℝ → ι → ℂ := fun u x =>
    ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * (u : ℂ) ^ j with hB
  set K : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ with hK
  have hKi : Integrable K μ := integrable_finsetSum _ fun j _ => (hcf j).norm
  have hK0 : ∀ x, 0 ≤ K x := fun x => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hAeq : ∀ x, ∀ u ∈ Ioo (-1 : ℝ) 1, A x u = B u x := fun x u hu => by
    rw [hA.eq_interp x u hu, eval_interp_eq_sum]
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hnear : ∀ᶠ u in 𝓝 (0 : ℝ), |u| ≤ 1 / 2 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    simpa [Real.dist_eq] using hu
  have hIoo : ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hlim : Tendsto (fun u => ∫ x, B u x / (wt u ^ a * (V x : ℂ) ^ N) ∂μ) (𝓝 0)
      (𝓝 (∫ x, B 0 x / (wt 0 ^ a * (V x : ℂ) ^ N) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => K x / ((3 / 4 : ℝ) ^ a * c ^ N)) ?_ ?_ (hKi.div_const _) ?_
    · refine Eventually.of_forall fun u => ?_
      refine AEStronglyMeasurable.div₀ ?_ (aestronglyMeasurable_const.mul (hVm.pow N))
      exact (integrable_finsetSum _ fun j _ => (hcf j).mul_const _).aestronglyMeasurable
    · filter_upwards [hnear] with u hu
      filter_upwards [hV] with x hx
      have hBn : ‖B u x‖ ≤ K x := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (abs_nonneg u) (hu.trans (by norm_num)))
      have hw := norm_wt_ge hu
      rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hc.trans_le hx)]
      exact div_le_div₀ (hK0 x) hBn (by positivity)
        (mul_le_mul (pow_le_pow_left₀ (by norm_num) hw a) (pow_le_pow_left₀ hc.le hx N)
          (by positivity) (by positivity))
    · filter_upwards [hV] with x hx
      have hc1 : Continuous fun u : ℝ => B u x := by
        simp only [hB]
        fun_prop
      have hc2 : Continuous fun u : ℝ => wt u ^ a * (V x : ℂ) ^ N := by
        unfold wt
        fun_prop
      have hVx : (V x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hc.trans_le hx).ne'
      refine (hc1.tendsto 0).div (hc2.tendsto 0) ?_
      simp [wt_zero, hVx]
  simp only [wt_zero, one_pow, one_mul] at hlim
  have e0 : ∀ x, B 0 x = A x 0 := fun x => (hAeq x 0 h0).symm
  simp only [e0] at hlim
  refine hlim.congr' ?_
  filter_upwards [hIoo] with u hu
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hAeq x u hu])

end Cont

/-! ### `V` along the null ray -/

theorem symanzikVector_smul {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (c : Fin (m + 1) → ℝ)
    (w : Fin 4 → ℝ) (z : Fin (m + 1) → ℝ) (s : Fin 2) :
    symanzikVector α (fun i => c i • w) z s = (∑ i, z i * α i s * c i) • w := by
  funext μ
  simp only [symanzikVector, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_smul_smul (a b : ℝ) (w : Fin 4 → ℝ) :
    Minkowski.dot (a • w) (b • w) = a * b * Minkowski.dot w w := by
  simp only [Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
  ring

/-- **`V` at external momenta on a null line** is `∑ᵢ zᵢ Mᵢ²`. -/
theorem symanzikV_smul_null {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (c : Fin (m + 1) → ℝ)
    {w : Fin 4 → ℝ} (hw : Minkowski.dot w w = 0) (M z : Fin (m + 1) → ℝ) :
    symanzikV α (fun i => c i • w) M z = ∑ i, z i * M i ^ 2 := by
  simp only [symanzikV, symanzikVector_smul, dot_smul_smul, hw, mul_zero, add_zero,
    Finset.sum_const_zero, sub_zero]

/-! ### Integrability of the parametric numerator -/

/-- The parametric numerator of an admissible quartic is integrable on the simplex. -/
theorem integrableOn_paramNum_good {D : SEData} {Q : LoopQuartic} (hQ : D.Good Q)
    (q : Fin (D.m + 1) → Fin 4 → ℝ) : IntegrableOn (paramNum Q D.α q D.M) (simplexSet D.m) := by
  rcases hQ.1 with h7 | hq
  · exact integrableOn_paramNum Q D.α q D.M h7 D.hcrit hQ.2
  have hm0 : 0 < D.m := by have := D.hm; omega
  have hspan : ∃ i j, D.α i 0 * D.α j 1 - D.α i 1 * D.α j 0 ≠ 0 :=
    NoSubdivergence.span (α := D.α) fun i => by
      have := D.hcrit.noSubdivergenceOfOrder i; have := D.hm; omega
  obtain ⟨hT₁, hT₂, hT₃⟩ := integrableOn_coeff_cubic Q D.α q hq D.hm D.hcrit hQ.2
  set K := ∑ i, (D.M i ^ 2 + ∑ μ, q i μ ^ 2)
  have hK := ae_abs_symanzikV_le D.α q D.M hm0 hspan
  have hVm : AEStronglyMeasurable (fun x => ((symanzikV D.α q D.M (simplexPoint x) : ℝ) : ℂ))
      (volume.restrict (simplexSet D.m)) :=
    (Complex.measurable_ofReal.comp ((measurable_symanzikV D.α q D.M).comp
      continuous_simplexPoint'.measurable)).aestronglyMeasurable
  have hb1 : ∀ᵐ x ∂(volume.restrict (simplexSet D.m)),
      ‖((symanzikV D.α q D.M (simplexPoint x) : ℝ) : ℂ)‖ ≤ K := by
    filter_upwards [hK] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hb2 : ∀ᵐ x ∂(volume.restrict (simplexSet D.m)),
      ‖((symanzikV D.α q D.M (simplexPoint x) : ℝ) : ℂ) ^ 2‖ ≤ K ^ 2 := by
    filter_upwards [hb1] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  exact (hT₁.add (hT₂.mul_bdd hVm hb1)).add (hT₃.mul_bdd (hVm.pow 2) hb2)

/-! ### The parametrization of the null ray -/

/-- `t = u / (1 - u²)`. -/
noncomputable def tpar (u : ℝ) : ℝ := u / (1 - u ^ 2)

/-- The inverse `u = 2t / (1 + √(1 + 4t²))`. -/
noncomputable def upar (t : ℝ) : ℝ := 2 * t / (1 + Real.sqrt (1 + 4 * t ^ 2))

theorem upar_mem (t : ℝ) : upar t ∈ Ioo (-1 : ℝ) 1 := by
  have hs : |2 * t| < Real.sqrt (1 + 4 * t ^ 2) := by
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
    nlinarith
  have hpos : 0 < 1 + Real.sqrt (1 + 4 * t ^ 2) := by positivity
  rw [abs_lt] at hs
  unfold upar
  constructor
  · rw [lt_div_iff₀ hpos]
    linarith
  · rw [div_lt_iff₀ hpos]
    linarith

theorem tpar_upar (t : ℝ) : tpar (upar t) = t := by
  set s := Real.sqrt (1 + 4 * t ^ 2) with hs_def
  have hs : s ^ 2 = 1 + 4 * t ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h1 : (1 + s) ≠ 0 := by positivity
  have h2 : 1 - upar t ^ 2 = 2 / (1 + s) := by
    unfold upar
    rw [← hs_def]
    field_simp
    linear_combination hs
  unfold tpar
  rw [h2]
  unfold upar
  rw [← hs_def]
  field_simp

theorem tendsto_upar : Tendsto upar (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous upar := by
    unfold upar
    refine Continuous.div (by fun_prop) (by fun_prop) fun t => ?_
    positivity
  have h := hc.tendsto 0
  simp only [upar, mul_zero, zero_div] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem isUPoly_tpar_smul {ι : Type*} (c : ℝ) (w : Fin 4 → ℝ) (μ : Fin 4) :
    IsUPoly (ι := ι) 2 fun _ u => wt u * (((c • (tpar u • w)) μ : ℝ) : ℂ) := by
  refine ((IsUPoly.var.const_mul fun _ => ((c * w μ : ℝ) : ℂ)).mono (by norm_num)).congr
    fun _ u hu => ?_
  have h : (1 : ℝ) - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  have h' : (1 : ℂ) - (u : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h
  simp only [Pi.smul_apply, smul_eq_mul, tpar, wt]
  push_cast
  field_simp

/-! ### The limit along the null ray -/

theorem dot_smul_nullVec (t : ℝ) : Minkowski.dot (t • nullVec) (t • nullVec) = 0 := by
  rw [show t • nullVec = t • nullVec from rfl, dot_smul_smul, dot_nullVec, mul_zero]

namespace SEPiece

variable {T : ℝ} (P : SEPiece T)

/-- **The limit along the null ray**: `W(t n₀) → W(0)` as `t → 0⁺`, for numerators polynomial
in the momentum at fixed loop momenta. -/
theorem tendsto_nullVec (hT : -T ^ 2 < 0) {d : ℕ}
    (hpoly : ∀ ℓ i j, IsLoopPoly 1 d fun y => P.N (y 0) ℓ i j) (i j : Fin 4) :
    Tendsto (fun t : ℝ => P.W (t • nullVec) i j) (𝓝[>] 0) (𝓝 (P.W 0 i j)) := by
  classical
  have hreg : ∀ t : ℝ, -T ^ 2 < Minkowski.dot (t • nullVec) (t • nullVec) := fun t => by
    rw [dot_smul_nullVec]; exact hT
  set mom : ℝ → Fin (P.D.m + 1) → Fin 4 → ℝ := fun u => P.D.mom (tpar u • nullVec) with hmom_def
  have hmom : ∀ k μ, IsUPoly (ι := Fin P.D.m → ℝ) 2 fun _ u => wt u * ((mom u k μ : ℝ) : ℂ) :=
    fun k μ => isUPoly_tpar_smul (P.D.cs k) nullVec μ
  -- `V` does not depend on `u`
  set V0 : (Fin P.D.m → ℝ) → ℝ := fun x => symanzikV P.D.α (P.D.mom 0) P.D.M (simplexPoint x)
  have hVc : ∀ u z, symanzikV P.D.α (mom u) P.D.M z =
      symanzikV P.D.α (P.D.mom 0) P.D.M z := fun u z => by
    have h1 := symanzikV_smul_null P.D.α P.D.cs (w := tpar u • nullVec) (dot_smul_nullVec _) P.D.M z
    have h2 := symanzikV_smul_null P.D.α P.D.cs (w := (0 : Fin 4 → ℝ)) (by simp [Minkowski.dot_eq])
      P.D.M z
    exact h1.trans h2.symm
  obtain ⟨c0, hc0, hV0⟩ := P.hV 0 (by simpa [Minkowski.dot_eq] using hT)
  have hm0 : 0 < P.D.m := by have := P.D.hm; omega
  have hspan : ∃ a b, P.D.α a 0 * P.D.α b 1 - P.D.α a 1 * P.D.α b 0 ≠ 0 :=
    NoSubdivergence.span (α := P.D.α) fun k => by
      have := P.D.hcrit.noSubdivergenceOfOrder k; have := P.D.hm; omega
  have hVae : ∀ᵐ x ∂(volume.restrict (simplexSet P.D.m)), c0 ≤ V0 x := by
    filter_upwards [ae_posDef P.D.α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    exact hV0 _ hz.1 hz.2 hPD.det_pos.ne'
  -- interpolation of the numerator
  set F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun u ℓ => P.N (tpar u • nullVec) ℓ i j
  have hF : IsUPoly (2 * d) fun ℓ u => wt u ^ d * F u ℓ := fun ℓ => by
    have h := isUPoly_eval_of_isLoopPoly (hpoly ℓ i j) (ι := Unit)
      (ℓ := fun _ u _ => tpar u • nullVec) fun _ ν => by
        simpa using isUPoly_tpar_smul (ι := Unit) 1 nullVec ν
    exact h ()
  set Qk : Fin (2 * d + 1) → LoopQuartic := fun k =>
    P.quartic (tpar (node (2 * d) k) • nullVec) i j
  have hQk : ∀ k, (Qk k).eval = F (node (2 * d) k) := fun k => P.eval_quartic _ _ _
  set J : ℝ → LoopQuartic := fun u => jointQuartic (2 * d) d Qk u
  have hJe : ∀ u ∈ Ioo (-1 : ℝ) 1, (J u).eval = F u := fun u hu => eval_jointQuartic hF hQk hu
  have hJg : ∀ u ∈ Ioo (-1 : ℝ) 1, P.D.Good (J u) := fun u hu => by
    refine ⟨?_, ?_⟩
    swap
    · rw [hJe u hu]
      show RefinedBound _ _ _ (fun ℓ => P.N (tpar u • nullVec) ℓ i j)
      rw [← P.eval_quartic]
      exact (P.good_quartic _ i j).2
    rcases Nat.lt_or_ge P.D.m 7 with h7 | h7
    · refine Or.inr (SEData.quart_qsum _ _ _ fun k _ => ?_)
      rcases (P.good_quartic (tpar (node (2 * d) k) • nullVec) i j).1 with h' | h'
      · exact absurd h' (by omega)
      · exact h'
    · exact Or.inl h7
  -- the value as an integral of a polynomial family
  set A : (Fin P.D.m → ℝ) → ℝ → ℂ := fun x u => ∑ k, (wt (node (2 * d) k) ^ d *
    (lbasis (2 * d) k).eval (u : ℂ)) * (wt u ^ 4 * paramNum (Qk k) P.D.α (mom u) P.D.M x)
  have hA : IsUPoly (2 * d + 8) A :=
    IsUPoly.sum _ fun k _ => ((isUPoly_lbasis (2 * d) k).const_mul _).mul
      (isUPoly_paramNum (Qk k) P.D.α P.D.M mom hmom)
  have hAi : ∀ k, Integrable (fun x => A x (node (2 * d + 8) k))
      (volume.restrict (simplexSet P.D.m)) := fun k => by
    refine integrable_finsetSum _ fun l _ => Integrable.const_mul ?_ _
    exact (integrableOn_paramNum_good (P.good_quartic _ i j) _).const_mul _
  have hval : ∀ u ∈ Ioo (-1 : ℝ) 1, P.W (tpar u • nullVec) i j = -((π : ℂ) ^ 4) *
      ∫ x in simplexSet P.D.m, A x u / (wt u ^ (d + 4) * (V0 x : ℂ) ^ (P.D.m - 3)) := by
    intro u hu
    rw [P.W_eq_pv (hreg _) (hJg u hu) (hJe u hu), SEData.pv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hVae] with x hx
    have hV0x : V0 x ≠ 0 := (hc0.trans_le hx).ne'
    have hV0x' : ((V0 x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV0x
    have hw := wt_ne_zero hu
    simp only [J, jointQuartic, paramIntegrand_qsum, A, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hVu : symanzikV P.D.α (mom u) P.D.M (simplexPoint x) ≠ 0 := by rw [hVc]; exact hV0x
    rw [paramIntegrand_zero_eq (Qk k) P.D.α (mom u) P.D.M (by have := P.D.hm; omega) hVu]
    simp only [hVc, lam, V0] at hV0x' ⊢
    field_simp
    ring
  have hVm : AEStronglyMeasurable (fun x => ((V0 x : ℝ) : ℂ))
      (volume.restrict (simplexSet P.D.m)) :=
    (Complex.measurable_ofReal.comp ((measurable_symanzikV P.D.α (P.D.mom 0) P.D.M).comp
      continuous_simplexPoint'.measurable)).aestronglyMeasurable
  have hlim := (tendsto_integral_upoly (a := d + 4) (N := P.D.m - 3) hA hAi hc0 hVae hVm).const_mul
    (-((π : ℂ) ^ 4))
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hW0 : P.W 0 i j = -((π : ℂ) ^ 4) *
      ∫ x in simplexSet P.D.m, A x 0 / ((V0 x : ℂ) ^ (P.D.m - 3)) := by
    have := hval 0 h0
    simp only [tpar, zero_div, zero_smul, wt_zero, one_pow, one_mul] at this
    exact this
  rw [← hW0] at hlim
  have hg : Tendsto (fun u => P.W (tpar u • nullVec) i j) (𝓝 0) (𝓝 (P.W 0 i j)) := by
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with u hu
    exact (hval u hu).symm
  exact (hg.comp tendsto_upar).congr fun t => by simp only [Function.comp_apply, tpar_upar]

/-- **A family converging to a multiple of the joint integrals of a piece has the covariant
form**: if `G_ε(p) = h(ε) ∫ N_p ∏ D⁻¹` eventually, with `h(ε) → h₀`, then `HasSEForm T G`. -/
theorem hasSEForm (hT : -T ^ 2 < 0) {d : ℕ}
    (hpoly : ∀ ℓ i j, IsLoopPoly 1 d fun y => P.N (y 0) ℓ i j) {h : ℝ → ℂ} {h₀ : ℂ}
    (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀)) {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hG : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ i j : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p i j = h ε * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹)) :
    HasSEForm T G := by
  refine hasSEForm_of_cov (W := fun p => h₀ • P.W p) (fun p hp i j => ?_) ?_ fun i j => ?_
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact (hh.mul (P.tendsto hp i j)).congr' (by
      filter_upwards [hG p hp i j] with ε hε
      exact hε.symm)
  · intro a ha p hp
    have e : ∀ A X B : Matrix (Fin 4) (Fin 4) ℂ, A * (h₀ • X) * B = h₀ • (A * X * B) :=
      fun A X B => by rw [Matrix.mul_smul, Matrix.smul_mul]
    show _ * (h₀ • P.W _) * _ = h₀ • P.W p
    rw [e, P.secov a ha p hp]
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact (P.tendsto_nullVec hT hpoly i j).const_mul h₀

end SEPiece

end QED.GradedProof.SE2

end
