/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKCov

/-!
# Set (c), the bubble classes: the Pauli quotients of a graph with a spectral line

Helper level for `QED.ChainProof.SetCMainB.MainBKKPauli`. A term of the longitudinal dispersive
part is a two-loop graph `G` along the curve `p'(u)` (a `CurveData`) with the spectral line
`κ² k² + t² - iε` on a copy of its line `j₀`, `κ² = x(1-x)`. The Pauli quotients of its values
must be bounded uniformly in `κ ∈ (0, 1]` for the dominated convergence in `x`. With `T = t/κ`:

* descaling: the value is `κ⁻²` times that of `G` with `j₀` doubled, the copy unscaled and of
  mass `T` (`kkV_descale`; the difference is `iε` times a convergent graph);
* partial fractions: that doubled value is `(M² - T²)⁻¹ (G_T - G)`, `G_T` the graph with the
  mass of `j₀` raised to `T` (`kkV_pf`), exact at every `ε`;
* the quotients of a curve with one heavy mass are bounded uniformly in that mass
  (`norm_evenQuot_heavy_le`, from `QED.ChainProof.SetCUnitM.norm_evenQuot_piece_le_var`).

For a light dispersion mass (`2κ²M² > t²`) the first and the third give `2M²/t²` times a bound on
the doubled curve; for a heavy one all three give `2/t²` times bounds on `G`.

* `kkV`, `isParamValue_kkV`: the `ε → 0⁺` value and its parametric form;
* `kkHeavy`, **`norm_evenQuot_heavy_le`**: a curve with one mass raised, and the uniform bound;
* `kkDouble`: the curve of `G` with the line `j₀` doubled;
* **`kkInt_descale`**, **`kkV_descale`**, **`kkV_pf`**;
* **`tendsto_evenQuot_kkCurve`**, **`norm_evenQuot_kkCurve_le`**: the Pauli quotients of the
  values with the spectral line converge at every scale and are bounded uniformly in the scale.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCUnitM QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance
open QED.Integration.TwoLoop (symanzikU symanzikV LoopQuartic NoSubdivergenceRefined
  RefinedBound lineDenom lineMomentum)
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Values -/

theorem kkSig_one {m : ℕ} (k : Fin (m + 1 + 1)) : kkSig 1 k = 1 :=
  Fin.cases rfl (fun j => kkSig_succ 1 j) k

/-- The `ε → 0⁺` value of the joint integral of a family of integrands. -/
noncomputable def kkV (H : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε)

theorem kkV_eq {H : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} {L : ℂ}
    (h : Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε)) (𝓝[>] 0) (𝓝 L)) :
    kkV H = L :=
  h.limUnder_eq

/-- **The value of a graph is its parametric value.** -/
theorem isParamValue_kkV {D : ParamData} {Q : LoopQuartic} (hB : RefinedBound D.α D.E 4 Q.eval)
    {M' : Fin (D.m + 1) → ℝ} (hM : D.M = M') {H : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hH : ∀ ε : ℝ, 0 < ε → H ε = fun ℓ => Q.eval ℓ * ∏ k, (lineDenom D.α D.p M' ε k ℓ)⁻¹) :
    IsParamValue D Q.eval (kkV H) := by
  subst hM
  have hP : IsParamValue D Q.eval (-((π : ℂ) ^ 4) * ∫ x in simplexSet D.m,
      QED.TwoLoop.ClassLimit.paramIntegrand Q D.α D.p D.M 0 x) := ⟨Q, rfl, hB, rfl⟩
  have hT : Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε)) (𝓝[>] 0)
      (𝓝 (-((π : ℂ) ^ 4) * ∫ x in simplexSet D.m,
        QED.TwoLoop.ClassLimit.paramIntegrand Q D.α D.p D.M 0 x)) := by
    refine hP.tendsto.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [hH ε hε]
  rwa [kkV_eq hT]

/-! ### One heavy mass -/

/-- `V` with the mass of line `h` replaced by `T`. -/
theorem symanzikV_update {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (h : Fin (m + 1)) (T : ℝ) (z : Fin (m + 1) → ℝ) :
    symanzikV α p (Function.update M h T) z = symanzikV α p M z + z h * (T ^ 2 - M h ^ 2) := by
  rw [← sub_eq_iff_eq_add', symanzikV_sub, Finset.sum_eq_single h]
  · simp only [Function.update_self]
  · intro b _ hb
    rw [Function.update_of_ne hb, sub_self, mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

/-- **The curve with the mass of line `h` raised to `T ≥ M_h ≥ 0`.** -/
noncomputable def kkHeavy (C : CurveData) (h : Fin (C.m + 1)) (T : ℝ) (hM : 0 ≤ C.M h)
    (hT : C.M h ≤ T) : CurveData where
  m := C.m
  α := C.α
  mom := C.mom
  M := Function.update C.M h T
  E := C.E
  hm := C.hm
  hcrit := C.hcrit
  c := C.c
  hc := C.hc
  hV u hu z hz hz1 hU := by
    rw [symanzikV_update]
    have h1 := C.hV u hu z hz hz1 hU
    have h2 : 0 ≤ z h * (T ^ 2 - C.M h ^ 2) := mul_nonneg (hz h) (by nlinarith)
    linarith
  hmom := C.hmom
  hVeven u z := by rw [symanzikV_update, symanzikV_update, C.hVeven]

/-- **The Pauli quotients of a curve with one heavy mass**, bounded uniformly in that mass: one
constant `B` with `‖(S(u) + S(-u))/(2u²)‖ ≤ B` for `0 < |u| ≤ 1/2` and every mass `T ≥ M_h` of
line `h` (`V = V₀ + z_h (T² - M_h²)` absorbs the growth of the numerator pointwise). -/
theorem norm_evenQuot_heavy_le (C : CurveData) (h : Fin (C.m + 1)) (hM : 0 ≤ C.M h)
    {J : Type*} [Fintype J] {D n r Dω : ℕ} (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) :
    ∃ B : ℝ, ∀ (T : ℝ) (hT : C.M h ≤ T) (v : ℝ → J → ℂ),
      (∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j,
        IsParamValue ((kkHeavy C h T hM hT).toParamData hu) (F u j) (v u j)) →
      ∀ u : ℝ, u ≠ 0 → |u| ≤ 1 / 2 →
        ‖((∑ j, ω u j * v u j) + ∑ j, ω (-u) j * v (-u) j) / (2 * (u : ℂ) ^ 2)‖ ≤ B := by
  classical
  choose Qk hQk using fun j (k : Fin (D + 1)) => hFq (node D k) (node_mem D k) j
  set Km : ℝ := ∑ t : Fin (Dω + (D + 8) + 1), ∑ i, ∑ μ,
    C.mom (node (Dω + (D + 8)) t) i μ ^ 2 with hKm
  have hKm0 : 0 ≤ Km := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  set K₀ : ℝ := ∑ i, C.M i ^ 2 + Km with hK₀
  have hK₀0 : 0 ≤ K₀ := add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hKm0
  have hc0 : 0 < C.c := C.hc
  set L : ℝ := ((1 + K₀) / C.c + 1) ^ 2 with hL
  refine ⟨L * pieceConst C.α C.mom D n r Dω Qk ω / ((3 / 4 : ℝ) ^ (r + n + 4) * C.c ^ (C.m - 5)),
    fun T hT v hv u hu0 hu => ?_⟩
  set δ := T ^ 2 - C.M h ^ 2 with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; nlinarith
  have hV : ∀ (x : Fin C.m → ℝ) u, (kkHeavy C h T hM hT).vfun x u =
      C.vfun x u + simplexPoint x h * δ := fun x u =>
    symanzikV_update _ _ _ _ _ _
  have hz0 : ∀ᵐ x ∂(volume.restrict (simplexSet C.m)), 0 ≤ simplexPoint x h := by
    filter_upwards [ae_restrict_mem (QED.Integration.Feynman.measurableSet_simplexSet _)]
      with x hx
    exact (QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx).1 _
  have hKb : ∀ t' : Fin (Dω + (D + 8) + 1), ∀ᵐ x ∂(volume.restrict (simplexSet C.m)),
      0 ≤ K₀ + simplexPoint x h * δ ∧
        |(kkHeavy C h T hM hT).vfun x (node (Dω + (D + 8)) t')| ≤
          K₀ + simplexPoint x h * δ := fun t' => by
    filter_upwards [QED.TwoLoop.ClassLimit.ae_abs_symanzikV_le C.α
      (C.mom (node (Dω + (D + 8)) t')) C.M (by have := C.hm; omega) C.hspan, hz0] with x hx hzx
    have hzδ : 0 ≤ simplexPoint x h * δ := mul_nonneg hzx hδ0
    refine ⟨by positivity, ?_⟩
    rw [hV]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hzδ]
    refine add_le_add ((show |C.vfun x (node (Dω + (D + 8)) t')| ≤ _ from hx).trans ?_) le_rfl
    have h1 : ∑ i, ∑ μ, C.mom (node (Dω + (D + 8)) t') i μ ^ 2 ≤ Km :=
      Finset.single_le_sum (f := fun t : Fin (Dω + (D + 8) + 1) => ∑ i, ∑ μ,
        C.mom (node (Dω + (D + 8)) t) i μ ^ 2)
        (fun t _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.mem_univ t')
    rw [Finset.sum_add_distrib]
    linarith
  have hcx : ∀ᵐ x ∂(volume.restrict (simplexSet C.m)),
      (kkHeavy C h T hM hT).c ≤ C.c + simplexPoint x h * δ ∧
        (∀ u ∈ Ioo (-1 : ℝ) 1, C.c + simplexPoint x h * δ ≤ (kkHeavy C h T hM hT).vfun x u) ∧
        (1 + (K₀ + simplexPoint x h * δ)) ^ 2 ≤ L * (C.c + simplexPoint x h * δ) ^ 2 := by
    filter_upwards [C.ae_le_vfun, hz0] with x hx hzx
    have hzδ : 0 ≤ simplexPoint x h * δ := mul_nonneg hzx hδ0
    refine ⟨le_add_of_nonneg_right hzδ, fun u hu => ?_, ?_⟩
    · rw [hV]
      exact add_le_add (hx u hu) le_rfl
    · rw [hL, ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      have e : ((1 + K₀) / C.c + 1) * (C.c + simplexPoint x h * δ) =
          (1 + K₀) + (1 + K₀) / C.c * (simplexPoint x h * δ) + C.c + simplexPoint x h * δ := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ (1 + K₀) / C.c * (simplexPoint x h * δ) := by positivity
      linarith
  exact norm_evenQuot_piece_le_var (kkHeavy C h T hM hT) F hFpoly Qk hQk hFB v hv ω hω hω0
    (K := fun x => K₀ + simplexPoint x h * δ) (cx := fun x => C.c + simplexPoint x h * δ)
    (by positivity) hKb hcx hu0 hu

/-! ### The doubled curve -/

/-- **The curve of `G` with the line `j₀` doubled**, the copy (line `0`) unscaled and of mass
`t`. -/
noncomputable def kkDouble (C : CurveData) (j₀ : Fin (C.m + 1)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hM0 : μ₀ ≤ C.M j₀) (hcμ : C.c ≤ μ₀ ^ 2)
    (hV : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (C.m + 1) → ℝ, (∀ i, 0 ≤ z i) →
      ∑ i, z i = 1 → symanzikU C.α z ≠ 0 →
        C.c ≤ symanzikV C.α (C.mom u) (Function.update C.M j₀ a) z)
    {t : ℝ} (ht : μ₀ ≤ t) : CurveData where
  m := C.m + 1
  α := fun k => kkSig 1 k • C.α (kkRho j₀ k)
  mom u := fun k => kkSig 1 k • C.mom u (kkRho j₀ k)
  M := Fin.cons t C.M
  E := C.E.map (Fin.succEmb (C.m + 1))
  hm := by have := C.hm; omega
  hcrit := kk_crit C.hcrit one_ne_zero
  c := C.c
  hc := C.hc
  hV u hu := (kkData C.hm C.hcrit hμ₀ C.hc hM0 (hV u hu) hcμ one_pos le_rfl ht).hV
  hmom i μ := fun _ => by
    obtain ⟨P, hP, hf⟩ := C.hmom (kkRho j₀ i) μ 0
    refine ⟨P, hP, fun u hu => ?_⟩
    have h1 := hf u hu
    simp only [kkSig_one, one_smul] at h1 ⊢
    exact h1
  hVeven u z := by
    simp only [kkSig_one, one_smul]
    rw [QED.Integration.TwoLoop.symanzikV_comp (kkRho j₀) C.α (C.mom (-u)) _ C.M,
      QED.Integration.TwoLoop.symanzikV_comp (kkRho j₀) C.α (C.mom u) _ C.M, C.hVeven]

/-! ### Descaling and partial fractions -/

section Values

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {p : Fin (m + 1) → Fin 4 → ℝ} {j₀ : Fin (m + 1)}
  {Q : LoopQuartic} {M : Fin (m + 1) → ℝ} {E : Finset (Fin (m + 1))}

theorem jointEnergyFirstIntegrable_kkInt (hm : 7 ≤ m) (hcrit : NoSubdivergenceRefined 2 E α)
    (hB : RefinedBound α E 4 Q.eval) {κ t ε : ℝ} (hκ : κ ≠ 0) (hε : 0 < ε) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (kkInt α p j₀ Q M κ t ε) :=
  QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q _ _ _ (by omega) hε (kk_crit hcrit hκ) (kk_bound hB (kkSig_succ κ))

theorem kkK_kkSig_one (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkK (fun k => kkSig 1 k • α (kkRho j₀ k)) (fun k => kkSig 1 k • p (kkRho j₀ k)) 0 ℓ =
      kkK α p j₀ ℓ := by
  have e : lineMomentum (fun k => kkSig 1 k • α (kkRho j₀ k))
      (fun k => kkSig 1 k • p (kkRho j₀ k)) 0 ℓ = lineMomentum α p j₀ ℓ := by
    funext μ
    unfold lineMomentum
    simp
  unfold kkK
  rw [e]

theorem kkLineDen_ne_zero {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) : ((x : ℝ) : ℂ) - (ε : ℂ) * I ≠ 0 :=
  fun h0 => by
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at this
    exact hε (by linarith)

/-- **Removing the scale of the spectral line at fixed `ε ≠ 0`**: with `D = κ² k² + t² - iε` and
`D' = k² + (t/κ)² - iε`, `D⁻¹ = κ⁻² D'⁻¹ + iε (1 - κ²) κ⁻² D⁻¹ D'⁻¹`; the last term is the doubled
graph with the spectral line on its copy. -/
theorem kkInt_descale {κ t ε : ℝ} (hκ : κ ≠ 0) (hε : ε ≠ 0) :
    kkInt α p j₀ Q M κ t ε = fun ℓ => ((κ ^ 2 : ℝ) : ℂ)⁻¹ * kkInt α p j₀ Q M 1 (t / κ) ε ℓ +
      (ε : ℂ) * I * (((1 - κ ^ 2) / κ ^ 2 : ℝ) : ℂ) *
        kkInt (fun k => kkSig 1 k • α (kkRho j₀ k)) (fun k => kkSig 1 k • p (kkRho j₀ k)) 0 Q
          (Fin.cons (t / κ) M) κ t ε ℓ := by
  funext ℓ
  rw [kkInt_eq, kkInt_eq, kkInt_eq, Fin.prod_univ_succ (n := m + 1), lineDenom_kk_zero,
    kkK_kkSig_one]
  simp only [lineDenom_kk_succ]
  set K := kkK α p j₀ ℓ
  set P := ∏ k, (lineDenom α p M ε k ℓ)⁻¹
  set D : ℂ := ((κ ^ 2 * K + t ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I with hDdef
  set D' : ℂ := ((1 ^ 2 * K + (t / κ) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I with hD'def
  have hD0 : D ≠ 0 := kkLineDen_ne_zero hε _
  have hD'0 : D' ≠ 0 := kkLineDen_ne_zero hε _
  have hκc : (κ : ℂ) ≠ 0 := ofReal_ne_zero.2 hκ
  have hrel : ((κ ^ 2 : ℝ) : ℂ) * D' = D + (ε : ℂ) * I * ((1 - κ ^ 2 : ℝ) : ℂ) := by
    simp only [hDdef, hD'def]
    push_cast
    field_simp
    ring
  have hκ2 : ((κ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hκ
  have key : D⁻¹ = ((κ ^ 2 : ℝ) : ℂ)⁻¹ * D'⁻¹ +
      (ε : ℂ) * I * (((1 - κ ^ 2) / κ ^ 2 : ℝ) : ℂ) * (D⁻¹ * D'⁻¹) := by
    have e2 : (((1 - κ ^ 2) / κ ^ 2 : ℝ) : ℂ) =
        ((1 - κ ^ 2 : ℝ) : ℂ) / ((κ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e2]
    field_simp
    linear_combination hrel
  linear_combination (Q.eval ℓ * P) * key

variable (hm : 7 ≤ m) (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval)
  {μ₀ c : ℝ} (hμ₀ : 0 < μ₀) (hc : 0 < c) (hM0 : μ₀ ≤ M j₀)
  (hV : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
    symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ a) z)
  (hcμ : c ≤ μ₀ ^ 2)
include hm hcrit hB hμ₀ hc hM0 hV hcμ

/-- **Descaling the value**: the value with the spectral line at scale `κ ∈ (0, 1]` is `κ⁻²`
times the value of the doubled graph with the unscaled copy of mass `t/κ`. -/
theorem kkV_descale {κ t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ht : μ₀ ≤ t) :
    kkV (kkInt α p j₀ Q M κ t) = ((κ ^ 2 : ℝ) : ℂ)⁻¹ * kkV (kkInt α p j₀ Q M 1 (t / κ)) := by
  have htκ : μ₀ ≤ t / κ := ht.trans (le_div_self (hμ₀.le.trans ht) hκ hκ1)
  obtain ⟨L, hL⟩ := tendsto_kkInt hm hcrit hB hμ₀ hc hM0 hV hcμ hκ hκ1 ht
  obtain ⟨L₁, hL₁⟩ := tendsto_kkInt hm hcrit hB hμ₀ hc hM0 hV hcμ one_pos le_rfl htκ
  have hV₂ : ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (m + 1 + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (fun k => kkSig 1 k • α (kkRho j₀ k)) z ≠ 0 →
      c ≤ symanzikV (fun k => kkSig 1 k • α (kkRho j₀ k))
        (fun k => kkSig 1 k • p (kkRho j₀ k)) (Function.update (Fin.cons (t / κ) M) 0 a) z :=
    fun a ha => by
      rw [Fin.update_cons_zero]
      exact (kkData hm hcrit hμ₀ hc hM0 hV hcμ one_pos le_rfl ha).hV
  obtain ⟨L₂, hL₂⟩ := tendsto_kkInt (j₀ := 0) (by omega) (kk_crit hcrit one_ne_zero)
    (kk_bound hB (kkSig_succ 1)) hμ₀ hc (by simpa using htκ) hV₂ hcμ hκ hκ1 ht
  have hcoef : Tendsto (fun ε : ℝ => (ε : ℂ) * I * (((1 - κ ^ 2) / κ ^ 2 : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (ε : ℂ) * I * (((1 - κ ^ 2) / κ ^ 2 : ℝ) : ℂ)) (𝓝 0)
        (𝓝 (((0 : ℝ) : ℂ) * I * (((1 - κ ^ 2) / κ ^ 2 : ℝ) : ℂ))) :=
      ((continuous_ofReal.mul continuous_const).mul continuous_const).tendsto 0
    rw [ofReal_zero, zero_mul, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim := (hL₁.const_mul (((κ ^ 2 : ℝ) : ℂ)⁻¹)).add (hcoef.mul hL₂)
  rw [zero_mul, add_zero] at hlim
  have hLL : L = ((κ ^ 2 : ℝ) : ℂ)⁻¹ * L₁ := by
    refine tendsto_nhds_unique hL (hlim.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [kkInt_descale (α := α) (p := p) (j₀ := j₀) (Q := Q) (M := M) hκ.ne' hε.ne']
    exact ((QED.ChainProof.SetCUnitM.jointEnergyFirstIntegrable_mul_add_mul
      (jointEnergyFirstIntegrable_kkInt hm hcrit hB one_ne_zero hε)
      (jointEnergyFirstIntegrable_kkInt (by omega) (kk_crit hcrit one_ne_zero)
        (kk_bound hB (kkSig_succ 1)) hκ.ne' hε) _ _).2).symm
  rw [kkV_eq hL, kkV_eq hL₁, hLL]

omit hμ₀ hM0 hV hcμ in
/-- **Partial fractions for the doubled graph**: with the unscaled copy of mass `T`,
`value = (M² - T²)⁻¹ (G_T - G)`, `G_T` the graph with the mass of `j₀` replaced by `T`. -/
theorem kkV_pf (hVM : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p M z) {T : ℝ}
    (hVT : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (Function.update M j₀ T) z)
    (hT : M j₀ ^ 2 ≠ T ^ 2) :
    kkV (kkInt α p j₀ Q M 1 T) = ((M j₀ ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹ *
      (kkV (kkG α p Q (Function.update M j₀ T)) - kkV (kkG α p Q M)) := by
  let DT : ParamData := ⟨m, α, p, Function.update M j₀ T, E, hm, hcrit, c, hc, hVT⟩
  let DM : ParamData := ⟨m, α, p, M, E, hm, hcrit, c, hc, hVM⟩
  have hPT : IsParamValue DT Q.eval (kkV (kkG α p Q (Function.update M j₀ T))) :=
    isParamValue_kkV (D := DT) hB rfl fun _ _ => rfl
  have hPM : IsParamValue DM Q.eval (kkV (kkG α p Q M)) :=
    isParamValue_kkV (D := DM) hB rfl fun _ _ => rfl
  have hT1 : Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (kkG α p Q (Function.update M j₀ T) ε)) (𝓝[>] 0)
      (𝓝 (kkV (kkG α p Q (Function.update M j₀ T)))) := hPT.tendsto
  have hT2 : Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (kkG α p Q M ε))
      (𝓝[>] 0) (𝓝 (kkV (kkG α p Q M))) := hPM.tendsto
  refine kkV_eq (((hT1.sub hT2).const_mul (((M j₀ ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hpf := kkInt_pf (α := α) (p := p) (j₀ := j₀) (Q := Q) (M := M) (t := T) one_ne_zero
    hε.ne' (by rwa [one_pow, one_mul])
  have hc1 : pfConst 1 (M j₀) T ε = ((M j₀ ^ 2 - T ^ 2 : ℝ) : ℂ) := by
    simp [pfConst]
  have hs : kkScaled α p j₀ Q M 1 (T / 1) ε = kkG α p Q (Function.update M j₀ T) ε := by
    have e1 : Function.update (1 : Fin (m + 1) → ℝ) j₀ 1 = 1 := by simp
    funext ℓ
    simp only [kkScaled, kkG, e1, div_one, Pi.one_apply, one_smul, one_mul]
  have h1 : QED.TwoLoop.jointEnergyFirstIntegrable 2 (kkG α p Q (Function.update M j₀ T) ε) :=
    QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      Q α p _ hm hε hcrit hB
  have h2 : QED.TwoLoop.jointEnergyFirstIntegrable 2 (kkG α p Q M ε) :=
    QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      Q α p M hm hε hcrit hB
  rw [hpf, hc1, hs]
  have e : (fun ℓ => ((M j₀ ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹ * (((1 ^ 2 : ℝ) : ℂ) *
      kkG α p Q (Function.update M j₀ T) ε ℓ - kkG α p Q M ε ℓ)) =
      fun ℓ => ((M j₀ ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹ * kkG α p Q (Function.update M j₀ T) ε ℓ +
        -((M j₀ ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹ * kkG α p Q M ε ℓ := funext fun ℓ => by
    push_cast; ring
  rw [e, (QED.ChainProof.SetCUnitM.jointEnergyFirstIntegrable_mul_add_mul h1 h2 _ _).2]
  ring

end Values

/-! ### The Pauli quotients with the spectral line along a curve -/

/-- The Pauli-weighted values along the curve of the graph with the spectral line at the scale
`κ`. -/
noncomputable def kkCurveS (C : CurveData) (j₀ : Fin (C.m + 1)) (t : ℝ) {J : Type*} [Fintype J]
    (Qf : ℝ → J → LoopQuartic) (ω : ℝ → J → ℂ) (κ u : ℝ) : ℂ :=
  ∑ j, ω u j * kkV (kkInt C.α (C.mom u) j₀ (Qf u j) C.M κ t)

theorem sum_mul_mul_sub {J : Type*} [Fintype J] (ω f g : J → ℂ) (a : ℂ) :
    ∑ j, ω j * (a * (f j - g j)) = a * (∑ j, ω j * f j - ∑ j, ω j * g j) := by
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

section Curve

variable (C : CurveData) (j₀ : Fin (C.m + 1)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) (hM0 : μ₀ ≤ C.M j₀)
  (hcμ : C.c ≤ μ₀ ^ 2)
  (hV : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ a : ℝ, μ₀ ≤ a → ∀ z : Fin (C.m + 1) → ℝ, (∀ i, 0 ≤ z i) →
    ∑ i, z i = 1 → symanzikU C.α z ≠ 0 →
      C.c ≤ symanzikV C.α (C.mom u) (Function.update C.M j₀ a) z)
  {t : ℝ} (ht : μ₀ ≤ t) {J : Type*} [Fintype J] {D n r Dω : ℕ}
  (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ) (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
  (Qf : ℝ → J → LoopQuartic) (hQf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, (Qf u j).eval = F u j)
  (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
  (ω : ℝ → J → ℂ) (hω : ∀ (ι : Type) j, IsUPoly (ι := ι) Dω fun _ u => wt u ^ r * ω u j)
  (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0)

include hμ₀ hM0 hcμ hV ht hQf hFB in
/-- Descaling along the curve. -/
theorem kkCurveS_descale {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    kkCurveS C j₀ t Qf ω κ u = ((κ ^ 2 : ℝ) : ℂ)⁻¹ *
      ∑ j, ω u j * kkV (kkInt C.α (C.mom u) j₀ (Qf u j) C.M 1 (t / κ)) := by
  unfold kkCurveS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hB : RefinedBound C.α C.E 4 (Qf u j).eval := by rw [hQf u hu j]; exact hFB u hu j
  rw [kkV_descale C.hm C.hcrit hB hμ₀ C.hc hM0 (hV u hu) hcμ hκ hκ1 ht]
  ring

omit [Fintype J] in
include hμ₀ hM0 hcμ hV ht hQf hFB in
/-- The values of the doubled graph along the curve are parametric values of the doubled curve
with the heavy copy. -/
theorem isParamValue_kkDouble {κ : ℝ} (hMD : 0 ≤ (kkDouble C j₀ hμ₀ hM0 hcμ hV ht).M 0)
    (hTD : (kkDouble C j₀ hμ₀ hM0 hcμ hV ht).M 0 ≤ t / κ) (u : ℝ)
    (hu : u ∈ Ioo (-1 : ℝ) 1) (j : J) :
    IsParamValue ((kkHeavy (kkDouble C j₀ hμ₀ hM0 hcμ hV ht) 0 (t / κ) hMD hTD).toParamData hu)
      (F u j) (kkV (kkInt C.α (C.mom u) j₀ (Qf u j) C.M 1 (t / κ))) := by
  have hB : RefinedBound C.α C.E 4 (Qf u j).eval := by rw [hQf u hu j]; exact hFB u hu j
  have h := isParamValue_kkV (D := (kkHeavy (kkDouble C j₀ hμ₀ hM0 hcμ hV ht) 0 (t / κ) hMD
    hTD).toParamData hu) (Q := Qf u j) (kk_bound hB (kkSig_succ 1)) (H := kkInt C.α (C.mom u) j₀
      (Qf u j) C.M 1 (t / κ)) (M' := Fin.cons (t / κ) C.M)
    (by
      show Function.update (Fin.cons t C.M : Fin (C.m + 1 + 1) → ℝ) 0 (t / κ) = _
      exact Fin.update_cons_zero _ _ _)
    fun _ _ => rfl
  rwa [hQf u hu j] at h

omit [Fintype J] in
include hFB in
theorem refinedBound_kkDouble (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) (j : J) :
    RefinedBound (kkDouble C j₀ hμ₀ hM0 hcμ hV ht).α (kkDouble C j₀ hμ₀ hM0 hcμ hV ht).E 4
      (F u j) :=
  refinedBound_map (Fin.succEmb (C.m + 1)) (fun e _ => by simp [kkDouble]) (hFB u hu j)

include hμ₀ hM0 hcμ hV ht hFpoly hQf hFB hω hω0 in
/-- **The Pauli quotients with the spectral line converge at every scale** `κ ∈ (0, 1]`. -/
theorem tendsto_evenQuot_kkCurve {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ Z : ℂ, Tendsto (QED.TwoLoop.PauliZeroLimit.evenQuot (kkCurveS C j₀ t Qf ω κ)) (𝓝[≠] 0)
      (𝓝 Z) := by
  have ht0 : 0 ≤ t := hμ₀.le.trans ht
  have hMD : 0 ≤ (kkDouble C j₀ hμ₀ hM0 hcμ hV ht).M 0 := by
    simp only [kkDouble]; exact ht0
  have hTD : (kkDouble C j₀ hμ₀ hM0 hcμ hV ht).M 0 ≤ t / κ := by
    simp only [kkDouble]; exact le_div_self ht0 hκ hκ1
  obtain ⟨L, hL⟩ := tendsto_piece (kkHeavy (kkDouble C j₀ hμ₀ hM0 hcμ hV ht) 0 (t / κ) hMD hTD)
    F hFpoly (fun u hu j => ⟨Qf u j, hQf u hu j⟩)
    (refinedBound_kkDouble C j₀ hμ₀ hM0 hcμ hV ht F hFB)
    (fun u j => kkV (kkInt C.α (C.mom u) j₀ (Qf u j) C.M 1 (t / κ)))
    (isParamValue_kkDouble C j₀ hμ₀ hM0 hcμ hV ht F Qf hQf hFB hMD hTD) ω (hω _) hω0
  refine ⟨((κ ^ 2 : ℝ) : ℂ)⁻¹ * L, (hL.const_mul _).congr' ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1))] with u hu
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  simp only [QED.TwoLoop.PauliZeroLimit.evenQuot]
  rw [kkCurveS_descale C j₀ hμ₀ hM0 hcμ hV ht F Qf hQf hFB ω hκ hκ1 hu,
    kkCurveS_descale C j₀ hμ₀ hM0 hcμ hV ht F Qf hQf hFB ω hκ hκ1 hu']
  ring

include hμ₀ hM0 hcμ hV ht hFpoly hQf hFB hω hω0 in
/-- **The Pauli quotients with the spectral line, bounded uniformly in the scale**: one constant
`B` with `‖(S_κ(u) + S_κ(-u))/(2u²)‖ ≤ B` for `0 < |u| ≤ 1/2` and every `κ ∈ (0, 1]`. -/
theorem norm_evenQuot_kkCurve_le : ∃ B : ℝ, ∀ u : ℝ, u ≠ 0 → |u| ≤ 1 / 2 → ∀ κ : ℝ, 0 < κ →
    κ ≤ 1 → ‖QED.TwoLoop.PauliZeroLimit.evenQuot (kkCurveS C j₀ t Qf ω κ) u‖ ≤ B := by
  have ht0 : 0 < t := hμ₀.trans_le ht
  have hM : 0 ≤ C.M j₀ := hμ₀.le.trans hM0
  have hMD : 0 ≤ (kkDouble C j₀ hμ₀ hM0 hcμ hV ht).M 0 := by
    simp only [kkDouble]; exact ht0.le
  have hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j :=
    fun u hu j => ⟨Qf u j, hQf u hu j⟩
  obtain ⟨BG, hBG⟩ := norm_evenQuot_heavy_le C j₀ hM F hFpoly hFq hFB ω (hω _) hω0
  obtain ⟨BD, hBD⟩ := norm_evenQuot_heavy_le (kkDouble C j₀ hμ₀ hM0 hcμ hV ht) 0 hMD F hFpoly
    hFq (refinedBound_kkDouble C j₀ hμ₀ hM0 hcμ hV ht F hFB) ω (hω _) hω0
  set Mj := C.M j₀ with hMj
  have ht2 : 0 < t ^ 2 := by positivity
  refine ⟨2 / t ^ 2 * (|BG| + |BG|) + 2 * Mj ^ 2 / t ^ 2 * |BD|,
    fun u hu0 hu κ hκ hκ1 => ?_⟩
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 := mem_Ioo_of_abs_le_half hu
  have hu1' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
  have hTD : (kkDouble C j₀ hμ₀ hM0 hcμ hV ht).M 0 ≤ t / κ := by
    simp only [kkDouble]; exact le_div_self ht0.le hκ hκ1
  set T := t / κ with hT
  have hκT : κ ^ 2 * T ^ 2 = t ^ 2 := by rw [hT]; field_simp
  set vD : ℝ → J → ℂ := fun u j => kkV (kkInt C.α (C.mom u) j₀ (Qf u j) C.M 1 T) with hvD
  have hEq : QED.TwoLoop.PauliZeroLimit.evenQuot (kkCurveS C j₀ t Qf ω κ) u =
      ((κ ^ 2 : ℝ) : ℂ)⁻¹ *
        (((∑ j, ω u j * vD u j) + ∑ j, ω (-u) j * vD (-u) j) / (2 * (u : ℂ) ^ 2)) := by
    simp only [QED.TwoLoop.PauliZeroLimit.evenQuot]
    rw [kkCurveS_descale C j₀ hμ₀ hM0 hcμ hV ht F Qf hQf hFB ω hκ hκ1 hu1,
      kkCurveS_descale C j₀ hμ₀ hM0 hcμ hV ht F Qf hQf hFB ω hκ hκ1 hu1']
    ring
  have hC0 : 0 ≤ 2 / t ^ 2 * (|BG| + |BG|) := by positivity
  have hC1 : 0 ≤ 2 * Mj ^ 2 / t ^ 2 * |BD| := by positivity
  rw [hEq]
  by_cases hcase : 2 * (κ ^ 2 * Mj ^ 2) ≤ t ^ 2
  · -- heavy dispersion mass: partial fractions against `j₀`
    have hκ2 : 0 < κ ^ 2 := by positivity
    have hT2 : 2 * Mj ^ 2 ≤ T ^ 2 := by nlinarith
    have hTM : Mj ≤ T := by
      have hT0 : 0 ≤ T := div_nonneg ht0.le hκ.le
      nlinarith
    have hne : Mj ^ 2 ≠ T ^ 2 := by
      intro h
      have : 0 < Mj ^ 2 := by have := hμ₀.trans_le hM0; positivity
      linarith
    set vT : ℝ → J → ℂ := fun u j => kkV (kkG C.α (C.mom u) (Qf u j)
      (Function.update C.M j₀ T)) with hvT
    set vM : ℝ → J → ℂ := fun u j => kkV (kkG C.α (C.mom u) (Qf u j) C.M) with hvM
    have hpf : ∀ u' ∈ Ioo (-1 : ℝ) 1, ∀ j, vD u' j =
        ((Mj ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹ * (vT u' j - vM u' j) := fun u' hu' j => by
      have hB : RefinedBound C.α C.E 4 (Qf u' j).eval := by rw [hQf u' hu' j]; exact hFB u' hu' j
      exact kkV_pf C.hm C.hcrit hB C.hc (C.hV u' hu') ((kkHeavy C j₀ T hM hTM).hV u' hu') hne
    have hvT' : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j,
        IsParamValue ((kkHeavy C j₀ T hM hTM).toParamData hu) (F u j) (vT u j) :=
      fun u hu j => by
        have hB : RefinedBound C.α C.E 4 (Qf u j).eval := by rw [hQf u hu j]; exact hFB u hu j
        have h := isParamValue_kkV (D := (kkHeavy C j₀ T hM hTM).toParamData hu) (Q := Qf u j)
          hB rfl (H := kkG C.α (C.mom u) (Qf u j) (Function.update C.M j₀ T)) fun _ _ => rfl
        rwa [hQf u hu j] at h
    have hvM' : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) j,
        IsParamValue ((kkHeavy C j₀ Mj hM le_rfl).toParamData hu) (F u j) (vM u j) :=
      fun u hu j => by
        have hB : RefinedBound C.α C.E 4 (Qf u j).eval := by rw [hQf u hu j]; exact hFB u hu j
        have h := isParamValue_kkV (D := (kkHeavy C j₀ Mj hM le_rfl).toParamData hu)
          (Q := Qf u j) hB (M' := C.M) (Function.update_eq_self _ _)
          (H := kkG C.α (C.mom u) (Qf u j) C.M) fun _ _ => rfl
        rwa [hQf u hu j] at h
    have h1 := hBG T hTM vT hvT' u hu0 hu
    have h2 := hBG Mj le_rfl vM hvM' u hu0 hu
    have hsum : ∀ u' ∈ Ioo (-1 : ℝ) 1, ∑ j, ω u' j * vD u' j =
        ((Mj ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹ *
          (∑ j, ω u' j * vT u' j - ∑ j, ω u' j * vM u' j) := fun u' hu' => by
      rw [← sum_mul_mul_sub]
      exact Finset.sum_congr rfl fun j _ => by rw [hpf u' hu' j]
    rw [hsum u hu1, hsum (-u) hu1']
    have hd : 0 < T ^ 2 - Mj ^ 2 := by
      have : 0 < Mj ^ 2 := by have := hμ₀.trans_le hM0; positivity
      linarith
    have hnorm : ‖((κ ^ 2 : ℝ) : ℂ)⁻¹ * ((Mj ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹‖ ≤ 2 / t ^ 2 := by
      rw [norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hκ2.le, Real.norm_eq_abs, abs_of_neg (by linarith), ← mul_inv]
      rw [inv_le_comm₀ (mul_pos hκ2 (by linarith)) (by positivity), inv_div]
      nlinarith
    calc _ = ‖((κ ^ 2 : ℝ) : ℂ)⁻¹ * ((Mj ^ 2 - T ^ 2 : ℝ) : ℂ)⁻¹ *
          ((((∑ j, ω u j * vT u j) + ∑ j, ω (-u) j * vT (-u) j) / (2 * (u : ℂ) ^ 2)) -
            (((∑ j, ω u j * vM u j) + ∑ j, ω (-u) j * vM (-u) j) / (2 * (u : ℂ) ^ 2)))‖ := by
          congr 1
          ring
      _ ≤ 2 / t ^ 2 * (|BG| + |BG|) := by
          rw [norm_mul]
          exact mul_le_mul hnorm ((norm_sub_le _ _).trans (add_le_add (h1.trans (le_abs_self _))
            (h2.trans (le_abs_self _)))) (norm_nonneg _) (by positivity)
      _ ≤ _ := le_add_of_nonneg_right hC1
  · -- light dispersion mass: the doubled curve and `κ⁻² ≤ 2 M² / t²`
    push Not at hcase
    have h3 := hBD T hTD vD (isParamValue_kkDouble C j₀ hμ₀ hM0 hcμ hV ht F Qf hQf hFB hMD hTD)
      u hu0 hu
    have hκinv : (κ ^ 2)⁻¹ ≤ 2 * Mj ^ 2 / t ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ ht2]
      nlinarith
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg κ)]
    calc (κ ^ 2)⁻¹ * _ ≤ 2 * Mj ^ 2 / t ^ 2 * |BD| :=
          mul_le_mul hκinv (h3.trans (le_abs_self _)) (norm_nonneg _) (by positivity)
      _ ≤ _ := le_add_of_nonneg_left hC0

end Curve

end QED.ChainProof.SetCMainB

end
