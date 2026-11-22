/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.ChengWu
public import QED.Integration.TwoLoopParametricAlgebra

/-!
# Set (a), stage B3: hierarchical Cheng–Wu variables for a one-loop insertion

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). For a function `F` on `ℝ⁴` homogeneous of degree `-4` (four line groups: an outer line,
the inner fermion `x`, a second outer line, the inner photon `1 - x`), the Cheng–Wu theorem with
the inner pair kept on the simplex and Fubini give `∫₀¹ dx ∫_{(0,∞)²} F(v₀, x, v₁, 1 - x) dv`. If
at fixed `x` the integrand is `(1 - x) G_x(v₀, v₁, x(1 - x))` with `G_x` homogeneous of degree
`-3` (the outer one-loop integrand with the inner loop as a third line of weight `x(1 - x)`), a
scaling and the Cheng–Wu theorem backwards return the outer simplex:

* `ksN_chengWuSet_prod`: `D_j ≅ (0, 1) × (0, ∞)ⁿ`, by inserting the coordinate `j`;
* `ksN_integral_pos_snoc`: `∫_{(0,∞)ⁿ} H(v, τ) dv = τ⁻¹ ∫_{(0,∞)ⁿ} H(v, 1) dv` for `H` of degree
  `-(n+1)` (`n = 2`);
* `ksN_integral_pos_snoc_one`: `∫_{(0,∞)²} H(v, 1) dv = ∫_{Δ₂} H` (Cheng–Wu with a split last
  line, then the merge `integral_simplex_splitAt`);
* **`ksN_nest`**: `∫_{Δ₃} F = ∫₀¹ x⁻¹ ∫_{Δ₂} G_x dx` (and `F` integrable is the only analytic
  hypothesis).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.ChengWu
open QED.Integration.SimplexMerge (integral_simplex_splitAt integral_splitAt_of_forall_eq
  splitAt splitAt_castSucc splitAt_last)

/-- The open positive orthant `(0, ∞)ⁿ`. -/
def ksNPos (n : ℕ) : Set (Fin n → ℝ) := {v | ∀ i, 0 < v i}

theorem measurableSet_ksNPos (n : ℕ) : MeasurableSet (ksNPos n) := by
  have : ksNPos n = ⋂ i, {v : Fin n → ℝ | 0 < v i} := by
    ext v
    simp [ksNPos]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)

theorem ksN_measurableSet_openSimplex (m : ℕ) : MeasurableSet (openSimplex m) := by
  have : openSimplex m = ksNPos m ∩ {x | ∑ i, x i < 1} := by
    ext x
    rw [mem_openSimplex]
    rfl
  rw [this]
  exact (measurableSet_ksNPos m).inter (measurableSet_lt (by fun_prop) measurable_const)

/-! ### The Cheng–Wu domain as a product -/

section Prod

variable {n : ℕ} (j : Fin (n + 1))

theorem ksN_preimage_chengWuSet :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm ⁻¹' chengWuSet j =
      Ioo (0 : ℝ) 1 ×ˢ ksNPos n := by
  ext ⟨x, v⟩
  simp only [mem_preimage, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, mem_chengWuSet, j.forall_iff_succAbove, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, mem_prod, mem_Ioo, ksNPos, mem_ofPred_eq]
  tauto

/-- **The Cheng–Wu domain is `(0, 1) × (0, ∞)ⁿ`** in the coordinate `j` and the others. -/
theorem ksN_chengWuSet_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin (n + 1) → ℝ) → E) :
    (IntegrableOn g (chengWuSet j) ↔ IntegrableOn (fun p : ℝ × (Fin n → ℝ) =>
      g (Fin.insertNth j p.1 p.2)) (Ioo (0 : ℝ) 1 ×ˢ ksNPos n) (volume.prod volume)) ∧
    ∫ w in chengWuSet j, g w =
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ ksNPos n, g (Fin.insertNth j p.1 p.2) ∂(volume.prod volume) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  have he : MeasurePreserving e.symm (volume.prod volume) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
  have hsymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth j p.1 p.2 := fun p => by
    simp [e, Fin.insertNthEquiv]
  have hpre := ksN_preimage_chengWuSet j
  refine ⟨?_, ?_⟩
  · rw [← he.integrableOn_comp_preimage e.symm.measurableEmbedding, hpre]
    simp only [Function.comp_def, hsymm]
  · rw [← he.setIntegral_preimage_emb e.symm.measurableEmbedding, hpre]
    simp only [hsymm]

end Prod

/-! ### Scaling the outer orthant -/

theorem ksN_snoc_smul {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    (Fin.snoc (t • v) t : Fin (n + 1) → ℝ) = t • Fin.snoc v 1 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem ksN_smul_mem_ksNPos {n : ℕ} {t : ℝ} (ht : 0 < t) (v : Fin n → ℝ) :
    t • v ∈ ksNPos n ↔ v ∈ ksNPos n := by
  simp only [ksNPos, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
  exact forall_congr' fun i => mul_pos_iff_of_pos_left ht

theorem ksN_snoc_pos {n : ℕ} {v : Fin n → ℝ} (hv : v ∈ ksNPos n) {t : ℝ} (ht : 0 < t) :
    ∀ i, 0 < (Fin.snoc v t : Fin (n + 1) → ℝ) i := fun i => by
  induction i using Fin.lastCases with
  | last => simpa using ht
  | cast i => simpa using hv i

section Scale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  {H : (Fin (n + 1) → ℝ) → E}
  (hH : ∀ z : Fin (n + 1) → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
    H (t • z) = (t ^ (n + 1))⁻¹ • H z)
include hH

theorem ksN_snoc_eq {τ : ℝ} (hτ : 0 < τ) {v : Fin n → ℝ} (hv : v ∈ ksNPos n) :
    H (Fin.snoc v τ) = (τ ^ (n + 1))⁻¹ • H (Fin.snoc (τ⁻¹ • v) 1) := by
  have h1 : (Fin.snoc v τ : Fin (n + 1) → ℝ) = τ • Fin.snoc (τ⁻¹ • v) 1 := by
    rw [← ksN_snoc_smul, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  rw [h1, hH _ (ksN_snoc_pos ((ksN_smul_mem_ksNPos (inv_pos.2 hτ) v).2 hv) one_pos) τ hτ]

/-- **Scaling the outer orthant** by the weight `τ` of the last line. -/
theorem ksN_integral_pos_snoc {τ : ℝ} (hτ : 0 < τ) :
    (IntegrableOn (fun v => H (Fin.snoc v τ)) (ksNPos n) ↔
      IntegrableOn (fun v => H (Fin.snoc v 1)) (ksNPos n)) ∧
    ∫ v in ksNPos n, H (Fin.snoc v τ) = τ⁻¹ • ∫ v in ksNPos n, H (Fin.snoc v 1) := by
  set G : (Fin n → ℝ) → E := (ksNPos n).indicator fun v => H (Fin.snoc v 1)
  have hpt : ∀ v, (ksNPos n).indicator (fun v => H (Fin.snoc v τ)) v =
      (τ ^ (n + 1))⁻¹ • G (τ⁻¹ • v) := fun v => by
    simp only [G]
    by_cases hv : v ∈ ksNPos n
    · rw [indicator_of_mem hv, ksN_snoc_eq hH hτ hv, indicator_of_mem
        ((ksN_smul_mem_ksNPos (inv_pos.2 hτ) v).2 hv)]
    · rw [indicator_of_notMem hv, indicator_of_notMem
        (mt (ksN_smul_mem_ksNPos (inv_pos.2 hτ) v).1 hv), smul_zero]
  have hfun : (ksNPos n).indicator (fun v => H (Fin.snoc v τ)) =
      fun v => (τ ^ (n + 1))⁻¹ • G (τ⁻¹ • v) := funext hpt
  have hc : (τ ^ (n + 1))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hτ.ne')
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff (measurableSet_ksNPos n),
      ← integrable_indicator_iff (measurableSet_ksNPos n), hfun]
    change Integrable ((τ ^ (n + 1))⁻¹ • fun v => G (τ⁻¹ • v)) volume ↔ Integrable G volume
    rw [integrable_smul_iff hc]
    exact integrable_comp_smul_iff volume G (inv_ne_zero hτ.ne')
  · rw [← integral_indicator (measurableSet_ksNPos n), ← integral_indicator
      (measurableSet_ksNPos n), hfun, integral_smul, Measure.integral_comp_smul,
      Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (by positivity), smul_smul]
    congr 1
    have := pow_ne_zero n hτ.ne'
    field_simp
    ring

end Scale

/-! ### The outer orthant back to the simplex -/

theorem ksN_vec_snoc (v : Fin 2 → ℝ) : (![v 0, v 1, 1] : Fin 3 → ℝ) = Fin.snoc v 1 := by
  funext i
  fin_cases i <;> rfl

theorem ksN_insertNth_two (x : ℝ) (v : Fin 2 → ℝ) :
    (Fin.insertNth 2 x v : Fin 3 → ℝ) = Fin.snoc v x := by
  funext i
  fin_cases i <;> rfl

section Back

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : (Fin 3 → ℝ) → E}

/-- The auxiliary four-line function: the last line of `H` split in two. -/
noncomputable def ksNSplit (H : (Fin 3 → ℝ) → E) (z : Fin 4 → ℝ) : E :=
  (z 2 + z 3)⁻¹ • H ![z 0, z 1, z 2 + z 3]

theorem ksN_ksNSplit_snoc (w : Fin 3 → ℝ) (a : ℝ) :
    ksNSplit H (Fin.snoc w a) = (w 2 + a)⁻¹ • H ![w 0, w 1, w 2 + a] := rfl

theorem ksN_ksNSplit_snoc_insertNth (p : ℝ × (Fin 2 → ℝ)) :
    ksNSplit H (Fin.snoc (Fin.insertNth 2 p.1 p.2 : Fin 3 → ℝ)
      (1 - (Fin.insertNth 2 p.1 p.2 : Fin 3 → ℝ) 2)) = H (Fin.snoc p.2 1) := by
  rw [ksN_insertNth_two, ksN_ksNSplit_snoc, ← ksN_vec_snoc]
  have e2 : (Fin.snoc p.2 p.1 : Fin 3 → ℝ) 2 = p.1 := rfl
  have e0 : (Fin.snoc p.2 p.1 : Fin 3 → ℝ) 0 = p.2 0 := rfl
  have e1 : (Fin.snoc p.2 p.1 : Fin 3 → ℝ) 1 = p.2 1 := rfl
  rw [e0, e1, e2, add_sub_cancel, inv_one, one_smul]

theorem ksN_ksNSplit_splitAt (z : Fin 3 → ℝ) (t : ℝ) :
    ksNSplit H (splitAt 2 z t) = (z 2)⁻¹ • H z := by
  have hz : (![z 0, z 1, z 2] : Fin 3 → ℝ) = z := by
    funext i
    fin_cases i <;> rfl
  rw [splitAt, ksN_ksNSplit_snoc]
  simp only [Function.update_self, add_sub_cancel]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hz]

variable (hH : ∀ z : Fin 3 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t → H (t • z) = (t ^ 3)⁻¹ • H z)
include hH

theorem ksN_ksNSplit_smul (z : Fin 4 → ℝ) (hz : ∀ i, 0 < z i) (t : ℝ) (ht : 0 < t) :
    ksNSplit H (t • z) = (t ^ 4)⁻¹ • ksNSplit H z := by
  have h3 : (![(t • z) 0, (t • z) 1, (t • z) 2 + (t • z) 3] : Fin 3 → ℝ) =
      t • ![z 0, z 1, z 2 + z 3] := by
    funext i
    fin_cases i <;> simp [mul_add]
  have hp : ∀ i, 0 < (![z 0, z 1, z 2 + z 3] : Fin 3 → ℝ) i := fun i => by
    fin_cases i
    · exact hz 0
    · exact hz 1
    · simpa using add_pos (hz 2) (hz 3)
  rw [ksNSplit, ksNSplit, h3, hH _ hp t ht, smul_smul, smul_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  have h2 : z 2 + z 3 ≠ 0 := (add_pos (hz 2) (hz 3)).ne'
  field_simp

/-- **The outer orthant with unit last weight is the simplex** (Cheng–Wu backwards). -/
theorem ksN_integral_pos_snoc_one [CompleteSpace E]
    (hI : IntegrableOn (fun v => H (Fin.snoc v 1)) (ksNPos 2)) :
    IntegrableOn (fun y => H (simplexPoint y)) (simplexSet 2) ∧
    ∫ v in ksNPos 2, H (Fin.snoc v 1) = ∫ y in simplexSet 2, H (simplexPoint y) := by
  have hF := ksN_ksNSplit_smul hH
  obtain ⟨hpi, hpe⟩ := ksN_chengWuSet_prod (2 : Fin 3)
    (fun w => ksNSplit H (Fin.snoc w (1 - w 2)))
  simp only [ksN_ksNSplit_snoc_insertNth] at hpi hpe
  have hprod : IntegrableOn (fun p : ℝ × (Fin 2 → ℝ) => H (Fin.snoc p.2 1))
      (Ioo (0 : ℝ) 1 ×ˢ ksNPos 2) (volume.prod volume) := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
      integrableOn_const (C := (1 : ℝ)) measure_Ioo_lt_top.ne
    have := h1.smul_prod hI
    rw [IntegrableOn, ← Measure.prod_restrict]
    simpa using this
  have hI4 : IntegrableOn (fun x => ksNSplit H (simplexPoint x)) (simplexSet 3) :=
    (integrableOn_simplex_chengWu_iff 2 (ksNSplit H) hF).2 (hpi.2 hprod)
  have hCW := integral_simplex_chengWu 2 (ksNSplit H) hF
  obtain ⟨hm1, hm2⟩ := integral_simplex_splitAt (by norm_num : 0 < 2) 2 hI4
  have hin : ∀ y ∈ openSimplex 2, ∫ t in (0 : ℝ)..simplexPoint y 2,
      ksNSplit H (splitAt 2 (simplexPoint y) t) = H (simplexPoint y) := fun y hy => by
    have hpos : 0 < simplexPoint y 2 := by
      have : simplexPoint y 2 = 1 - ∑ i, y i := QED.Integration.TwoLoop.simplexPoint_last y
      rw [this]
      linarith [(mem_openSimplex.1 hy).2]
    rw [integral_splitAt_of_forall_eq 2 (simplexPoint y) fun t => by
      rw [ksN_ksNSplit_splitAt, ksN_ksNSplit_splitAt], ksN_ksNSplit_splitAt, smul_smul,
      mul_inv_cancel₀ hpos.ne', one_smul]
  have hae := simplexSet_ae_eq_openSimplex (0 : Fin 2)
  have hEq : ∫ y in simplexSet 2, ∫ t in (0 : ℝ)..simplexPoint y 2,
      ksNSplit H (splitAt 2 (simplexPoint y) t) = ∫ y in simplexSet 2, H (simplexPoint y) := by
    rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
    exact setIntegral_congr_fun (ksN_measurableSet_openSimplex 2) hin
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn (fun y => ∫ t in (0 : ℝ)..simplexPoint y 2,
        ksNSplit H (splitAt 2 (simplexPoint y) t)) (openSimplex 2) := by
      rw [IntegrableOn, ← Measure.restrict_congr_set hae]
      exact hm1
    rw [IntegrableOn, Measure.restrict_congr_set hae]
    exact h1.congr_fun hin (ksN_measurableSet_openSimplex 2)
  · rw [← hEq, ← hm2, hCW, hpe, ← Measure.prod_restrict,
      integral_fun_snd (fun v => H (Fin.snoc v 1))]
    simp

end Back

/-! ### The nested form -/

section Nest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Hierarchical Cheng–Wu variables.** For `F` on `ℝ⁴` homogeneous of degree `-4` and
integrable on `Δ₃`, whose Cheng–Wu slice (inner pair `(x, 1 - x)` at the positions `1`, `3`) is
`(1 - x) G_x(v, x(1 - x))` with `G_x` homogeneous of degree `-3`:
`∫_{Δ₃} F = ∫₀¹ x⁻¹ ∫_{Δ₂} G_x dx`, the outer function integrable on `(0, 1)`. -/
theorem ksN_nest {F : (Fin 4 → ℝ) → E}
    (hF : ∀ z : Fin 4 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t → F (t • z) = (t ^ 4)⁻¹ • F z)
    (hI : IntegrableOn (fun y => F (simplexPoint y)) (simplexSet 3))
    (G : ℝ → (Fin 3 → ℝ) → E)
    (hG : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ z : Fin 3 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      G x (t • z) = (t ^ 3)⁻¹ • G x z)
    (hslice : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ ksNPos 2,
      F (Fin.snoc (Fin.insertNth 1 x v) (1 - x)) = (1 - x) • G x (Fin.snoc v (x * (1 - x)))) :
    IntegrableOn (fun x => x⁻¹ • ∫ y in simplexSet 2, G x (simplexPoint y)) (Ioo (0 : ℝ) 1) ∧
    ∫ y in simplexSet 3, F (simplexPoint y) =
      ∫ x in Ioo (0 : ℝ) 1, x⁻¹ • ∫ y in simplexSet 2, G x (simplexPoint y) := by
  have hCW := integral_simplex_chengWu (1 : Fin 3) F hF
  have hIw := (integrableOn_simplex_chengWu_iff (1 : Fin 3) F hF).1 hI
  obtain ⟨hpi, hpe⟩ := ksN_chengWuSet_prod (1 : Fin 3) (fun w => F (Fin.snoc w (1 - w 1)))
  simp only [Fin.insertNth_apply_same] at hpi hpe
  have hprod := hpi.1 hIw
  set g : ℝ × (Fin 2 → ℝ) → E := fun p => F (Fin.snoc (Fin.insertNth 1 p.1 p.2) (1 - p.1))
  have hprod' : Integrable g ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (ksNPos 2))) := by
    rw [Measure.prod_restrict]
    exact hprod
  -- the inner integral at a good `x`
  have hx : ∀ x ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun v => g (x, v)) (ksNPos 2) →
      ∫ v in ksNPos 2, g (x, v) = x⁻¹ • ∫ y in simplexSet 2, G x (simplexPoint y) := by
    intro x hx hsec
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have hτ : 0 < x * (1 - x) := mul_pos hx.1 h1x
    have hcg : EqOn (fun v => g (x, v)) (fun v => (1 - x) • G x (Fin.snoc v (x * (1 - x))))
        (ksNPos 2) := fun v hv => hslice x hx v hv
    have hsec' : IntegrableOn (fun v => G x (Fin.snoc v (x * (1 - x)))) (ksNPos 2) := by
      have := hsec.congr_fun hcg (measurableSet_ksNPos 2)
      have h2 : IntegrableOn (fun v => (1 - x)⁻¹ • ((1 - x) • G x (Fin.snoc v (x * (1 - x)))))
          (ksNPos 2) := this.smul ((1 - x)⁻¹)
      simpa only [smul_smul, inv_mul_cancel₀ h1x.ne', one_smul] using h2
    obtain ⟨hsc1, hsc2⟩ := ksN_integral_pos_snoc (hG x hx) hτ
    obtain ⟨-, hb⟩ := ksN_integral_pos_snoc_one (hG x hx) (hsc1.1 hsec')
    rw [setIntegral_congr_fun (measurableSet_ksNPos 2) hcg, integral_smul, hsc2, hb, smul_smul,
      mul_inv, ← mul_assoc, mul_comm (1 - x), mul_assoc, mul_inv_cancel₀ h1x.ne', mul_one]
  have hae : (fun x => ∫ v in ksNPos 2, g (x, v)) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => x⁻¹ • ∫ y in simplexSet 2, G x (simplexPoint y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hprod'.prod_right_ae] with x hxm hsec
    exact hx x hxm hsec
  refine ⟨hprod'.integral_prod_left.congr hae, ?_⟩
  rw [hCW, hpe, setIntegral_prod g hprod]
  exact integral_congr_ae hae

end Nest

end QED.ChainProof.SetAKS

end
