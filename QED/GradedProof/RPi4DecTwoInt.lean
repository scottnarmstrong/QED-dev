/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecTwoAlg
public import QED.GradedProof.RPi4DecSegLip

/-!
# (R-Π₄) step L9: second differences of parametric integrals along a segment

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`). The second-order counterpart of `QED.GradedProof.RPi4.dec_lip_integral_upoly`
and `QED.GradedProof.RPi4.dec_symanzikV_line_bound`.

* `DecTwoReg.pow_unif` (constants of `fᴺ` uniform in `f`), `DecTwoReg.integral` (integration of
  a family with integrable constants);
* `dec_twoReg_pow_ofReal`, `dec_twoReg_upoly` (polynomial families, constants linear in the
  coefficient norms), `dec_twoReg_wt`;
* **`dec_two_integral_upoly`**: `∫ A(·, u) / ((1 - u²)ᵃ V(u)ᴺ)` is of class `DecTwoReg` on
  `[-1/2, 1/2]` when `V ≥ c > 0` is of class `DecTwoReg` uniformly off a null set;
* **`dec_symanzikV_line_two`**: `V` along a line of momenta is of class `DecTwoReg`, uniformly off
  a null set.
-/

@[expose] public section

open Complex MeasureTheory Set Polynomial
open scoped Real

namespace QED.GradedProof.RPi4

open QED.TwoLoop.PauliZeroLimit QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

namespace DecTwoReg

variable {𝕜 : Type*} [RCLike 𝕜] {lo hi : ℝ}

/-- The constants of `fⁿ` depend only on those of `f`. -/
theorem pow_unif (M L K : ℝ) (n : ℕ) : ∃ M₂ L₂ K₂ : ℝ, ∀ f : ℝ → 𝕜,
    DecTwoReg lo hi f M L K → DecTwoReg lo hi (fun u => f u ^ n) M₂ L₂ K₂ := by
  induction n with
  | zero => exact ⟨_, _, _, fun f _ => (const 1).congr fun u _ => (pow_zero _).symm⟩
  | succ n ih =>
    obtain ⟨M₂, L₂, K₂, h⟩ := ih
    exact ⟨_, _, _, fun f hf => ((h f hf).mul hf).congr fun u _ => (pow_succ _ _).symm⟩

/-- **Integration of a family with integrable constants.** -/
theorem integral {ι : Type*} [MeasurableSpace ι] {μ : Measure ι} {F : ι → ℝ → ℂ}
    {Mx Lx Kx : ι → ℝ} (hMi : Integrable Mx μ) (hLi : Integrable Lx μ) (hKi : Integrable Kx μ)
    (hFm : ∀ u ∈ Icc lo hi, AEStronglyMeasurable (fun x => F x u) μ)
    (hF : ∀ᵐ x ∂μ, DecTwoReg lo hi (F x) (Mx x) (Lx x) (Kx x)) :
    DecTwoReg lo hi (fun u => ∫ x, F x u ∂μ) (∫ x, Mx x ∂μ) (∫ x, Lx x ∂μ) (∫ x, Kx x ∂μ) := by
  have hFi : ∀ u ∈ Icc lo hi, Integrable (fun x => F x u) μ := fun u hu =>
    Integrable.mono' hMi (hFm u hu) (by filter_upwards [hF] with x hx using hx.bound u hu)
  refine ⟨⟨integral_nonneg_of_ae (by filter_upwards [hF] with x hx using hx.nonneg.1),
    integral_nonneg_of_ae (by filter_upwards [hF] with x hx using hx.nonneg.2.1),
    integral_nonneg_of_ae (by filter_upwards [hF] with x hx using hx.nonneg.2.2)⟩,
    fun u hu => ?_, fun u hu v hv => ?_, fun u h hu h2 => ?_⟩
  · exact norm_integral_le_of_norm_le hMi (by filter_upwards [hF] with x hx using hx.bound u hu)
  · rw [← integral_sub (hFi u hu) (hFi v hv), ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hLi.mul_const _)
      (by filter_upwards [hF] with x hx using hx.lip u hu v hv)
  · have h1 := dec_mid_mem hu h2
    have e : (∫ x, F x (u + 2 * h) ∂μ) - 2 * (∫ x, F x (u + h) ∂μ) + ∫ x, F x u ∂μ =
        ∫ x, (F x (u + 2 * h) - 2 * F x (u + h) + F x u) ∂μ := by
      symm
      rw [integral_add ?_ (hFi u hu), integral_sub (hFi _ h2) ((hFi _ h1).const_mul 2),
        integral_const_mul]
      exact (hFi _ h2).sub ((hFi _ h1).const_mul 2)
    rw [e, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hKi.mul_const _)
      (by filter_upwards [hF] with x hx using hx.two u h hu h2)

end DecTwoReg

theorem dec_twoReg_pow_ofReal (j : ℕ) :
    ∃ M L K : ℝ, DecTwoReg (-(1 / 2)) (1 / 2) (fun u : ℝ => (u : ℂ) ^ j) M L K :=
  (DecTwoReg.id.ofReal (𝕜 := ℂ)).pow j

theorem dec_Icc_half_mem_Ioo {u : ℝ} (hu : u ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    u ∈ Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- **Polynomial families**: constants linear in the norms of the interpolation coefficients. -/
theorem dec_twoReg_upoly {ι : Type*} {D : ℕ} {f : ι → ℝ → ℂ} (hf : IsUPoly D f)
    {Mj Lj Kj : ℕ → ℝ}
    (hj : ∀ j, DecTwoReg (-(1 / 2)) (1 / 2) (fun u : ℝ => (u : ℂ) ^ j) (Mj j) (Lj j) (Kj j))
    (x : ι) : DecTwoReg (-(1 / 2)) (1 / 2) (f x)
      (∑ j ∈ Finset.range (D + 1), ‖(interp D f x).coeff j‖ * Mj j)
      (∑ j ∈ Finset.range (D + 1), ‖(interp D f x).coeff j‖ * Lj j)
      (∑ j ∈ Finset.range (D + 1), ‖(interp D f x).coeff j‖ * Kj j) := by
  refine (DecTwoReg.sum (Finset.range (D + 1)) fun j _ =>
    (hj j).const_mul ((interp D f x).coeff j)).congr fun u hu => ?_
  rw [hf.eq_interp x u (dec_Icc_half_mem_Ioo hu), eval_interp_eq_sum]

theorem dec_twoReg_wt (a : ℕ) :
    ∃ M L K : ℝ, DecTwoReg (-(1 / 2)) (1 / 2) (fun u => wt u ^ a) M L K := by
  obtain ⟨M, L, K, h⟩ := dec_twoReg_pow_ofReal 2
  obtain ⟨M', L', K', h'⟩ := ((DecTwoReg.const (1 : ℂ)).sub h).pow a
  exact ⟨M', L', K', h'.congr fun u _ => by simp [wt]⟩

section Integral

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- **Second differences of `∫ A(·, u) / ((1 - u²)ᵃ V(u)ᴺ)`** on `[-1/2, 1/2]`, for polynomial
families `A` with integrable values at the nodes and `V ≥ c > 0` of class `DecTwoReg` with
constants uniform off a null set. -/
theorem dec_two_integral_upoly {D a N : ℕ} {A : ι → ℝ → ℂ} (hA : IsUPoly D A)
    (hAi : ∀ k, Integrable (fun x => A x (node D k)) μ) {c MV LV KV : ℝ} (hc : 0 < c)
    {V : ℝ → ι → ℝ} (hVm : ∀ u, AEStronglyMeasurable (V u) μ)
    (hV : ∀ᵐ x ∂μ, (∀ u : ℝ, |u| ≤ 1 / 2 → c ≤ V u x) ∧
      DecTwoReg (-(1 / 2)) (1 / 2) (fun u => ((V u x : ℝ) : ℂ)) MV LV KV) :
    ∃ M L K : ℝ, DecTwoReg (-(1 / 2)) (1 / 2)
      (fun u => ∫ x, A x u / (wt u ^ a * (V u x : ℂ) ^ N) ∂μ) M L K := by
  have hcf : ∀ j, Integrable (fun x => (interp D A x).coeff j) μ := integrable_interp_coeff hAi
  choose Mj Lj Kj hj using dec_twoReg_pow_ofReal
  obtain ⟨Mw, Lw, Kw, hw⟩ := dec_twoReg_wt a
  obtain ⟨MP, LP, KP, hP⟩ := DecTwoReg.pow_unif (𝕜 := ℂ) (lo := -(1 / 2)) (hi := 1 / 2)
    MV LV KV N
  set d₀ : ℝ := (3 / 4 : ℝ) ^ a * c ^ N with hd₀
  have hd₀p : 0 < d₀ := by positivity
  set Mi := d₀⁻¹
  set Li := (Lw * MP + Mw * LP) / d₀ ^ 2
  set Ki := (2 * (Lw * MP + Mw * LP) ^ 2 + Mw * MP * (Kw * MP + Mw * KP + 2 * (Lw * LP))) /
    d₀ ^ 3
  set cM : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ * Mj j
  set cL : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ * Lj j
  set cK : ι → ℝ := fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ * Kj j
  have hint : ∀ g : ℕ → ℝ, Integrable
      (fun x => ∑ j ∈ Finset.range (D + 1), ‖(interp D A x).coeff j‖ * g j) μ := fun g =>
    integrable_finsetSum _ fun j _ => (hcf j).norm.mul_const _
  have hpt : ∀ᵐ x ∂μ, DecTwoReg (-(1 / 2)) (1 / 2)
      (fun u => A x u / (wt u ^ a * (V u x : ℂ) ^ N))
      (cM x * Mi) (cL x * Mi + cM x * Li) (cK x * Mi + cM x * Ki + 2 * (cL x * Li)) := by
    filter_upwards [hV] with x ⟨hlow, hVx⟩
    have hD := hw.mul (hP _ hVx)
    have hDl : ∀ u ∈ Icc (-(1 / 2) : ℝ) (1 / 2), d₀ ≤ ‖wt u ^ a * ((V u x : ℝ) : ℂ) ^ N‖ :=
      fun u hu => by
        have hu' : |u| ≤ 1 / 2 := abs_le.mpr hu
        have hVx := hlow u hu'
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hc.trans_le hVx)]
        exact mul_le_mul (pow_le_pow_left₀ (by norm_num) (norm_wt_ge hu') a)
          (pow_le_pow_left₀ hc.le hVx N) (by positivity) (by positivity)
    exact ((dec_twoReg_upoly hA hj x).mul (hD.inv hd₀p hDl)).congr fun u _ =>
      (div_eq_mul_inv _ _).symm
  have hFm : ∀ u ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      AEStronglyMeasurable (fun x => A x u / (wt u ^ a * (V u x : ℂ) ^ N)) μ := by
    intro u hu
    have e : (fun x => A x u) =
        fun x => ∑ j ∈ Finset.range (D + 1), (interp D A x).coeff j * (u : ℂ) ^ j :=
      funext fun x => by rw [hA.eq_interp x u (dec_Icc_half_mem_Ioo hu), eval_interp_eq_sum]
    have hP' : AEStronglyMeasurable (fun x => A x u) μ := by
      rw [e]
      exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        (hcf j).aestronglyMeasurable.mul_const _
    have hVc : AEStronglyMeasurable (fun x => ((V u x : ℝ) : ℂ)) μ :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (hVm u)
    exact hP'.div₀ ((hVc.pow N).const_mul _)
  exact ⟨_, _, _, DecTwoReg.integral ((hint Mj).mul_const _)
    (((hint Lj).mul_const _).add ((hint Mj).mul_const _))
    ((((hint Kj).mul_const _).add ((hint Mj).mul_const _)).add
      (((hint Lj).mul_const _).const_mul _)) hFm hpt⟩

end Integral

/-- **`V` along a line of momenta is of class `DecTwoReg`**, uniformly off a null set. -/
theorem dec_symanzikV_line_two {m : ℕ} (hm0 : 0 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) (cs : Fin (m + 1) → ℝ)
    (M : Fin (m + 1) → ℝ) (k₀ w : Fin 4 → ℝ) :
    ∃ MV LV KV : ℝ, ∀ᵐ x ∂(volume.restrict (simplexSet m)), DecTwoReg (-(1 / 2)) (1 / 2)
      (fun u => ((symanzikV α (fun i => cs i • lineK k₀ w u) M (simplexPoint x) : ℝ) : ℂ))
      MV LV KV := by
  set mom : ℝ → Fin (m + 1) → Fin 4 → ℝ := fun u i => cs i • lineK k₀ w u with hmom_def
  have hmom : ∀ i ν, IsUPoly (ι := Fin m → ℝ) 2 fun _ u => wt u * ((mom u i ν : ℝ) : ℂ) :=
    fun i ν => isUPoly_lineK (cs i) k₀ w ν
  have hW := isUPoly_symanzikV α mom M (fun x => simplexPoint x) hmom
  set Bn : ℝ := ∑ k : Fin 5, ∑ i, (M i ^ 2 + ∑ μ, mom (node 4 k) i μ ^ 2) with hBn
  have hBk : ∀ k : Fin 5, ∑ i, (M i ^ 2 + ∑ μ, mom (node 4 k) i μ ^ 2) ≤ Bn := fun k =>
    Finset.single_le_sum (f := fun k : Fin 5 => ∑ i, (M i ^ 2 + ∑ μ, mom (node 4 k) i μ ^ 2))
      (fun k _ => by positivity) (Finset.mem_univ k)
  choose Mj Lj Kj hj using dec_twoReg_pow_ofReal
  set β : ℕ → ℝ := fun j => Bn * ∑ k : Fin 5, ‖(lbasis 4 k).coeff j‖
  have hβ : ∀ j, 0 ≤ β j := fun j => mul_nonneg (by positivity) (by positivity)
  obtain ⟨M2, L2, K2, h2⟩ := dec_twoReg_wt 2
  have hwl : ∀ u ∈ Icc (-(1 / 2) : ℝ) (1 / 2), (9 / 16 : ℝ) ≤ ‖wt u ^ 2‖ := fun u hu => by
    rw [norm_pow]
    have := norm_wt_ge (abs_le.mpr hu)
    nlinarith
  have hinv := h2.inv (by norm_num : (0 : ℝ) < 9 / 16) hwl
  set MW := ∑ j ∈ Finset.range (4 + 1), β j * Mj j
  set LW := ∑ j ∈ Finset.range (4 + 1), β j * Lj j
  set KW := ∑ j ∈ Finset.range (4 + 1), β j * Kj j
  set Mi : ℝ := (9 / 16)⁻¹
  set Li : ℝ := L2 / (9 / 16) ^ 2
  set Ki : ℝ := (2 * L2 ^ 2 + M2 * K2) / (9 / 16) ^ 3
  refine ⟨MW * Mi, LW * Mi + MW * Li, KW * Mi + MW * Ki + 2 * (LW * Li), ?_⟩
  filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  have hnode : ∀ k : Fin 5, ‖wt (node 4 k) ^ 2 *
      ((symanzikV α (mom (node 4 k)) M (simplexPoint x) : ℝ) : ℂ)‖ ≤ Bn := fun k => by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_symanzikV_le α (mom (node 4 k)) M hz.1 hz.2 hPD.det_pos.ne'
    have h2 : ‖wt (node 4 k)‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (dec_norm_wt_le_one' (node_mem 4 k))
    calc ‖wt (node 4 k)‖ ^ 2 * |symanzikV α (mom (node 4 k)) M (simplexPoint x)|
        ≤ 1 * (∑ i, (M i ^ 2 + ∑ μ, mom (node 4 k) i μ ^ 2)) :=
          mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
      _ ≤ Bn := by rw [one_mul]; exact hBk k
  have hc : ∀ j, ‖(interp 4 _ x).coeff j‖ ≤ β j := fun j =>
    dec_norm_interp_coeff_le (f := fun x u => wt u ^ 2 *
      ((symanzikV α (mom u) M (simplexPoint x) : ℝ) : ℂ)) x hnode j
  have hWr := dec_twoReg_upoly hW hj x
  have hWr' := hWr.mono
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (hj j).nonneg.1)
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (hj j).nonneg.2.1)
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (hj j).nonneg.2.2)
  refine (hWr'.mul hinv).congr fun u hu => ?_
  have hw0 : wt u ^ 2 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hwl u hu))
  simp only [mom]
  rw [mul_right_comm, mul_inv_cancel₀ hw0, one_mul]

end QED.GradedProof.RPi4

end
