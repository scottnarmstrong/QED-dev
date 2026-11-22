/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMPow
public import QED.TwoLoop.VPHalfAtAssemblyPieces

/-!
# Multi-denominator two-loop vertex units: removing the scales of the extra lines

Helper level for set (c) (stage L2). The extra lines of the multi-denominator unit
(`QED/ChainProof/SetCUnitMUnit.lean`) carry scales `κⱼ ∈ (0, 1]`; the spectral factor of the
one-loop vacuum polarization has `κ² = x(1-x)`, which tends to `0` at the ends of the Feynman
interval. The bounds and the continuity of `QED/ChainProof/SetCUnitMPow.lean` hold at fixed scales.
This file removes the scales, as `QED.TwoLoop.VPHalfAtGen.specLimit` does for set (a):

`κ² k² + cs² - iε = κ² (k² + (cs/κ)² - iε) - iε (1 - κ²)`,

so at every `ε > 0` the unit is `κ⁻²` times the unit with the line unscaled and of mass `cs/κ`,
plus `iε (1 - κ²)/κ²` times a unit with one more extra line, whose limit exists; the second term
vanishes as `ε → 0⁺`.

* `unitMIntegrand_descale`: the identity of the integrands at `ε ≠ 0`;
* **`unitMLimitV_descale`**: `L(κ, cs) = κₑ⁻² L(κ[e ↦ 1], cs[e ↦ csₑ/κₑ])` for the limits;
* **`unitMLimitV_descale_all`**: `L(κ, cs) = (∏ₑ κₑ²)⁻¹ L(1, cs/κ)`: every limit is a dispersion
  value with unscaled lines and masses `√tₑ = csₑ/κₑ`;
* **`norm_unitMLimitV_descale_le`**: `‖L(κ, cs)‖ ≤ (∏ₑ κₑ²)⁻¹ C (1 + ∑ₑ (csₑ/κₑ)²)ⁿ`, one constant
  for all scales in `(0, 1]` and all masses `≥ μ₀`;
* **`continuousOn_unitMLimitV_descale`**: continuity along families of scales in `(0, 1]` and
  masses `≥ μ₀` (for instance in the Feynman parameter `x ∈ (0, 1)`);
* `lineDenom_unitM_spectral`, **`unitMLimitV_spectral`**: with `κₑ = √(x(1-x))`, `csₑ = M`, the
  extra line is set (a)'s factor `fDen M ε x k`, and the limit is `(x(1-x))⁻¹` times the limit with
  an unscaled line of mass `specMu M x = √(M²/(x(1-x)))`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrixPV)
open QED.TwoLoop.VPHalfAtAssembly (fDen specMu mem_Ioo_mul_pos)

/-! ### Linearity of the joint energy-first integral -/

section Linear

variable {F G : (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem jointEnergyFirstIntegrable_mul_add_mul
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 2 F)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable 2 G) (a b : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ => a * F ℓ + b * G ℓ) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => a * F ℓ + b * G ℓ) =
        a * QED.TwoLoop.jointEnergyFirstIntegral 2 F +
          b * QED.TwoLoop.jointEnergyFirstIntegral 2 G := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  have hin : ∀ v : Fin 2 → Fin 3 → ℝ,
      (∫ t : Fin 2 → ℝ, a * F (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) +
          b * G (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))) =
        a * (∫ t : Fin 2 → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) +
          b * ∫ t : Fin 2 → ℝ, G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) := fun v => by
    rw [integral_add ((hF1 v).const_mul a) ((hG1 v).const_mul b), integral_const_mul,
      integral_const_mul]
  refine ⟨⟨fun v => ((hF1 v).const_mul a).add ((hG1 v).const_mul b), ?_⟩, ?_⟩
  · simp only [hin]
    exact (hF2.const_mul a).add (hG2.const_mul b)
  · unfold QED.TwoLoop.jointEnergyFirstIntegral
    simp only [hin]
    rw [integral_add (hF2.const_mul a) (hG2.const_mul b), integral_const_mul, integral_const_mul]

end Linear

/-! ### Changing one extra line -/

section Update

variable {r : ℕ}

theorem mExtra_injective : Function.Injective (mExtra r) := fun j j' h => by
  have := congrArg Fin.val h
  simp only [mExtra] at this
  exact Fin.ext (by omega)

theorem mExt_update_of_ne {X : Type*} (x : Fin 8 → X) (y : Fin r → X) (e : Fin r) (v : X)
    {i : Fin (r + 8)} (hi : i ≠ mExtra r e) :
    mExt x (Function.update y e v) i = mExt x y i := by
  rcases mem_mEmb_or_mExtra i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [mExt_mEmb]
  · have hj : j ≠ e := fun h => hi (h ▸ rfl)
    simp only [mExt_mExtra, Function.update_of_ne hj]

theorem lineDenom_unitM_update_of_ne (c : Class5) (s : Fin 8) (κ : Fin r → ℝ)
    (p p' : Fin 4 → ℝ) (m a A b B : ℝ) (cs : Fin r → ℝ) (e : Fin r) (v w ε : ℝ)
    {i : Fin (r + 8)} (hi : i ≠ mExtra r e) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (unitMMatrix c s (Function.update κ e v))
        (unitMMomenta c s (Function.update κ e v) p p')
        (unitMMasses m a A b B (Function.update cs e w)) ε i ℓ =
      lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') (unitMMasses m a A b B cs) ε i ℓ :=
  by
  refine lineDenom_congr ?_ ?_ ?_ ε ℓ <;>
    simp only [unitMMatrix, unitMMomenta, unitMMasses, mScale, mExt_update_of_ne _ _ _ _ hi]

theorem init_snoc_eq {X : Type*} (y : Fin r → X) (v : X) :
    Fin.init (Fin.snoc y v : Fin (r + 1) → X) = y :=
  funext fun j => by simp [Fin.init]

/-- **Removing one scale at fixed `ε ≠ 0`.** With `D = κₑ² k² + csₑ² - iε` and
`D' = k² + (csₑ/κₑ)² - iε`: `D⁻¹ = κₑ⁻² D'⁻¹ + iε (1 - κₑ²) κₑ⁻² D⁻¹ D'⁻¹`; the last term is the
unit with the extra line `D'` appended. -/
theorem unitMIntegrand_descale (c : Class5) (P : Params) (s : Fin 8) {κ : Fin r → ℝ} {e : Fin r}
    (hκ : κ e ≠ 0) (m a A b B : ℝ) (cs : Fin r → ℝ) {ε : ℝ} (hε : ε ≠ 0) (p p' : Fin 4 → ℝ)
    (n : ℕ) (μ i j : Fin 4) :
    unitMIntegrand c P s κ (unitMMasses m a A b B cs) ε p p' n μ i j = fun ℓ =>
      ((κ e ^ 2 : ℝ) : ℂ)⁻¹ * unitMIntegrand c P s (Function.update κ e 1)
          (unitMMasses m a A b B (Function.update cs e (cs e / κ e))) ε p p' n μ i j ℓ +
        (ε : ℂ) * I * (((1 - κ e ^ 2) / κ e ^ 2 : ℝ) : ℂ) *
          unitMIntegrand c P s (Fin.snoc κ 1 : Fin (r + 1) → ℝ)
            (unitMMasses m a A b B (Fin.snoc cs (cs e / κ e) : Fin (r + 1) → ℝ)) ε p p' n
            μ i j ℓ := by
  funext ℓ
  set k2 : ℝ := Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ) with hk2
  -- the old product
  set f : Fin (r + 8) → ℂ := fun k =>
    (lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') (unitMMasses m a A b B cs) ε k ℓ)⁻¹
    with hf
  set R : ℂ := ∏ k ∈ Finset.univ.erase (mExtra r e), f k with hR
  have hD := lineDenom_unitM_mExtra c s κ p p' m a A b B cs ε e ℓ
  have hD' := lineDenom_unitM_mExtra c s (Function.update κ e 1) p p' m a A b B
    (Function.update cs e (cs e / κ e)) ε e ℓ
  simp only [Function.update_self] at hD'
  have hL := lineDenom_unitM_mExtra c s (Fin.snoc κ 1 : Fin (r + 1) → ℝ) p p' m a A b B
    (Fin.snoc cs (cs e / κ e) : Fin (r + 1) → ℝ) ε (Fin.last r) ℓ
  rw [mExtra_last] at hL
  simp only [Fin.snoc_last] at hL
  set D : ℂ := ((κ e ^ 2 * k2 + cs e ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I with hDdef
  set D' : ℂ := ((1 ^ 2 * k2 + (cs e / κ e) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I with hD'def
  have hne : ∀ x : ℝ, ((x : ℝ) : ℂ) - (ε : ℂ) * I ≠ 0 := fun x h0 => by
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at this
    exact hε (by linarith)
  have hD0 : D ≠ 0 := hne _
  have hD'0 : D' ≠ 0 := hne _
  have hold : ∏ k, f k = D⁻¹ * R := by
    rw [← Finset.mul_prod_erase _ f (Finset.mem_univ (mExtra r e))]
    simp only [hf, hD]
    rfl
  have hnew : ∏ k, (lineDenom (unitMMatrix c s (Function.update κ e 1))
      (unitMMomenta c s (Function.update κ e 1) p p')
      (unitMMasses m a A b B (Function.update cs e (cs e / κ e))) ε k ℓ)⁻¹ = D'⁻¹ * R := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (mExtra r e)), hD']
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [lineDenom_unitM_update_of_ne c s κ p p' m a A b B cs e 1 _ ε (Finset.ne_of_mem_erase hk)]
  have hsnoc : ∏ k, (lineDenom (unitMMatrix c s (Fin.snoc κ 1 : Fin (r + 1) → ℝ))
      (unitMMomenta c s (Fin.snoc κ 1 : Fin (r + 1) → ℝ) p p')
      (unitMMasses m a A b B (Fin.snoc cs (cs e / κ e) : Fin (r + 1) → ℝ)) ε k ℓ)⁻¹ =
        D⁻¹ * R * D'⁻¹ := by
    rw [Fin.prod_univ_castSucc]
    simp only [lineDenom_unitM_castSucc, init_snoc_eq]
    rw [hL, hold]
  have hrel : ((κ e ^ 2 : ℝ) : ℂ) * D' = D + (ε : ℂ) * I * ((1 - κ e ^ 2 : ℝ) : ℂ) := by
    have hκc : (κ e : ℂ) ≠ 0 := ofReal_ne_zero.2 hκ
    simp only [hDdef, hD'def]
    push_cast
    field_simp
    ring
  have hκ2 : ((κ e ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hκ
  have key : D⁻¹ = ((κ e ^ 2 : ℝ) : ℂ)⁻¹ * D'⁻¹ +
      (ε : ℂ) * I * (((1 - κ e ^ 2) / κ e ^ 2 : ℝ) : ℂ) * (D⁻¹ * D'⁻¹) := by
    have e2 : (((1 - κ e ^ 2) / κ e ^ 2 : ℝ) : ℂ) =
        ((1 - κ e ^ 2 : ℝ) : ℂ) / ((κ e ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e2]
    field_simp
    linear_combination hrel
  simp only [unitMIntegrand]
  rw [hold, hnew, hsnoc]
  linear_combination (unitNum c P p p' μ i j ℓ * elemSq c s p p' ℓ ^ n * R) * key

end Update

/-! ### Hypotheses after removing a scale -/

section Hyp

variable {r n : ℕ}

theorem TrailOne.update_one {κ : Fin r → ℝ} (h : TrailOne n κ) (e : Fin r) :
    TrailOne n (Function.update κ e 1) := fun j hj => by
  by_cases hje : j = e
  · subst hje; simp
  · rw [Function.update_of_ne hje]; exact h j hj

theorem TrailOne.snoc_one {κ : Fin r → ℝ} (h : TrailOne n κ) :
    TrailOne n (Fin.snoc κ 1 : Fin (r + 1) → ℝ) := fun j hj => by
  refine Fin.lastCases ?_ (fun j hj => ?_) j hj
  · intro _; simp
  · simp only [Fin.snoc_castSucc]
    exact h j (by simp at hj; omega)

theorem div_ge_of_extraGe {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {κ cs : Fin r → ℝ} (h : ExtraGe μ₀ κ cs)
    (e : Fin r) : μ₀ ≤ cs e / κ e := by
  obtain ⟨h0, h1, hc⟩ := h e
  rw [le_div_iff₀ h0]
  nlinarith

theorem ExtraGe.update_one {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {κ cs : Fin r → ℝ} (h : ExtraGe μ₀ κ cs)
    (e : Fin r) :
    ExtraGe μ₀ (Function.update κ e 1) (Function.update cs e (cs e / κ e)) := fun j => by
  by_cases hje : j = e
  · subst hje; simpa using div_ge_of_extraGe hμ₀ h j
  · rw [Function.update_of_ne hje, Function.update_of_ne hje]; exact h j

theorem ExtraGe.snoc_one {μ₀ : ℝ} {κ cs : Fin r → ℝ} (h : ExtraGe μ₀ κ cs) {w : ℝ}
    (hw : μ₀ ≤ w) :
    ExtraGe μ₀ (Fin.snoc κ 1 : Fin (r + 1) → ℝ) (Fin.snoc cs w : Fin (r + 1) → ℝ) := fun j => by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa using hw
  · simpa using h j

end Hyp

/-! ### The limits -/

section Limit

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
  {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hM hp hp' hq

/-- **Removing one scale from the limit**:
`L(κ, cs) = κₑ⁻² L(κ[e ↦ 1], cs[e ↦ csₑ/κₑ])`. -/
theorem unitMLimitV_descale {r n : ℕ} {κ cs : Fin r → ℝ} (hnr : n ≤ r) (hT : TrailOne n κ)
    (hX : ExtraGe μ₀ κ cs) (e : Fin r) (μ i j : Fin 4) :
    unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j =
      ((κ e ^ 2 : ℝ) : ℂ)⁻¹ * unitMLimitV c P s (Function.update κ e 1)
        (unitMMasses P.m a A b B (Function.update cs e (cs e / κ e))) p p' n μ i j := by
  have hκ : κ e ≠ 0 := hX.ne_zero e
  obtain ⟨_, hS⟩ := unitM_pow hc P hm hs hμ₀ hM hp hp' hq n hnr hT hX
  obtain ⟨hU₁, hU₂⟩ := unitM_pow hc P hm hs hμ₀ hM hp hp' hq n hnr (hT.update_one e)
    (hX.update_one hμ₀ e)
  obtain ⟨hN₁, hN₂⟩ := unitM_pow hc P hm hs hμ₀ hM hp hp' hq n (r := r + 1) (by omega)
    hT.snoc_one (hX.snoc_one (div_ge_of_extraGe hμ₀ hX e))
  have hcoef : Tendsto (fun ε : ℝ => (ε : ℂ) * I * (((1 - κ e ^ 2) / κ e ^ 2 : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (ε : ℂ) * I * (((1 - κ e ^ 2) / κ e ^ 2 : ℝ) : ℂ)) (𝓝 0)
        (𝓝 (((0 : ℝ) : ℂ) * I * (((1 - κ e ^ 2) / κ e ^ 2 : ℝ) : ℂ))) :=
      ((continuous_ofReal.mul continuous_const).mul continuous_const).tendsto 0
    rw [ofReal_zero, zero_mul, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim := ((hU₂ μ i j).const_mul (((κ e ^ 2 : ℝ) : ℂ)⁻¹)).add (hcoef.mul (hN₂ μ i j))
  rw [zero_mul, add_zero] at hlim
  refine tendsto_nhds_unique (hS μ i j) (hlim.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have h := jointEnergyFirstIntegrable_mul_add_mul (hU₁ ε hε μ i j) (hN₁ ε hε μ i j)
    (((κ e ^ 2 : ℝ) : ℂ)⁻¹) ((ε : ℂ) * I * (((1 - κ e ^ 2) / κ e ^ 2 : ℝ) : ℂ))
  unfold unitMValue
  rw [unitMIntegrand_descale c P s hκ P.m a A b B cs hε.ne' p p' n μ i j]
  exact h.2.symm

/-- The scales and masses after removing the scales of the lines in `S`. -/
def descaleK {r : ℕ} (S : Finset (Fin r)) (κ : Fin r → ℝ) : Fin r → ℝ :=
  fun e => if e ∈ S then 1 else κ e

/-- The masses after removing the scales of the lines in `S`: `csₑ/κₑ` on `S`. -/
noncomputable def descaleM {r : ℕ} (S : Finset (Fin r)) (κ cs : Fin r → ℝ) : Fin r → ℝ :=
  fun e => if e ∈ S then cs e / κ e else cs e

omit hc hm hs hM hp hp' hq in
theorem extraGe_descale {r : ℕ} {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) (S : Finset (Fin r)) :
    ExtraGe μ₀ (descaleK S κ) (descaleM S κ cs) := fun e => by
  by_cases he : e ∈ S
  · simpa [descaleK, descaleM, he] using div_ge_of_extraGe hμ₀ hX e
  · simpa [descaleK, descaleM, he] using hX e

theorem unitMLimitV_descale_finset {r n : ℕ} {κ cs : Fin r → ℝ} (hnr : n ≤ r)
    (hT : TrailOne n κ) (hX : ExtraGe μ₀ κ cs) (μ i j : Fin 4) (S : Finset (Fin r)) :
    unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j =
      (∏ e ∈ S, ((κ e ^ 2 : ℝ) : ℂ))⁻¹ * unitMLimitV c P s (descaleK S κ)
        (unitMMasses P.m a A b B (descaleM S κ cs)) p p' n μ i j := by
  induction S using Finset.induction_on with
  | empty =>
    have hK : descaleK ∅ κ = κ := funext fun e => by simp [descaleK]
    have hC : descaleM ∅ κ cs = cs := funext fun e => by simp [descaleM]
    simp [hK, hC]
  | insert e S he ih =>
    have hTS : TrailOne n (descaleK S κ) := fun j hj => by
      by_cases hjS : j ∈ S
      · simp [descaleK, hjS]
      · simpa [descaleK, hjS] using hT j hj
    have h := unitMLimitV_descale hc P hm hs hμ₀ hM hp hp' hq hnr hTS
      (extraGe_descale hμ₀ hX S) e μ i j
    have hKe : descaleK S κ e = κ e := by simp [descaleK, he]
    have hK : Function.update (descaleK S κ) e 1 = descaleK (insert e S) κ := by
      funext j
      by_cases hje : j = e
      · subst hje; simp [descaleK]
      · rw [Function.update_of_ne hje]; simp [descaleK, hje]
    have hC : Function.update (descaleM S κ cs) e (descaleM S κ cs e / descaleK S κ e) =
        descaleM (insert e S) κ cs := by
      funext j
      by_cases hje : j = e
      · subst hje; simp [descaleM, descaleK, he]
      · rw [Function.update_of_ne hje]; simp [descaleM, hje]
    rw [hK, hC, hKe] at h
    rw [ih, h, Finset.prod_insert he, mul_inv, ← mul_assoc, mul_comm (_ : ℂ)⁻¹]

/-- **Every limit is a dispersion value with unscaled lines**:
`L(κ, cs) = (∏ₑ κₑ²)⁻¹ L(1, cs/κ)`. -/
theorem unitMLimitV_descale_all {r n : ℕ} {κ cs : Fin r → ℝ} (hnr : n ≤ r)
    (hT : TrailOne n κ) (hX : ExtraGe μ₀ κ cs) (μ i j : Fin 4) :
    unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j =
      (∏ e, ((κ e ^ 2 : ℝ) : ℂ))⁻¹ * unitMLimitV c P s (fun _ => 1)
        (unitMMasses P.m a A b B fun e => cs e / κ e) p p' n μ i j := by
  rw [unitMLimitV_descale_finset hc P hm hs hμ₀ hM hp hp' hq hnr hT hX μ i j Finset.univ]
  congr 3 <;> funext e <;> simp [descaleK, descaleM]

end Limit

/-! ### Uniformity in the scales -/

/-- **A bound uniform in the scales and the masses**: one constant `C` with
`‖L(κ, cs)‖ ≤ (∏ₑ κₑ²)⁻¹ C (1 + ∑ₑ (csₑ/κₑ)²)ⁿ` for all scales in `(0, 1]` with the last `n`
equal to `1` and all photon and extra masses `≥ μ₀`. -/
theorem norm_unitMLimitV_descale_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) {r n : ℕ} (hnr : n ≤ r) :
    ∃ C : ℝ, ∀ (a A b B : ℝ) (κ cs : Fin r → ℝ), MassesGe μ₀ a A b B → TrailOne n κ →
      ExtraGe μ₀ κ cs →
      ‖unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j‖ ≤
        (∏ e, κ e ^ 2)⁻¹ * (C * (1 + ∑ e, (cs e / κ e) ^ 2) ^ n) := by
  obtain ⟨C, hC⟩ := norm_unitMLimitV_pow_le hc P hm hs hμ₀ hp hp' hq μ i j n (r := r)
    (κ := fun _ => 1) hnr (fun _ _ => rfl) fun _ => ⟨one_pos, le_rfl⟩
  refine ⟨C, fun a A b B κ cs hM hT hX => ?_⟩
  rw [unitMLimitV_descale_all hc P hm hs hμ₀ hM hp hp' hq hnr hT hX μ i j, norm_mul, norm_inv,
    ← Complex.ofReal_prod, Complex.norm_real,
    Real.norm_of_nonneg (Finset.prod_nonneg fun e _ => sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hC a A b B _ hM fun e => div_ge_of_extraGe hμ₀ hX e)
    (inv_nonneg.2 (Finset.prod_nonneg fun e _ => sq_nonneg _))

/-- **Continuity along families of scales and masses**: for scales in `(0, 1]` (the last `n` equal
to `1`) and masses `≥ μ₀`, continuous on `s'`, the limit is continuous on `s'`. -/
theorem continuousOn_unitMLimitV_descale {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {s' : Set X} {a A b B : X → ℝ}
    (ha : ContinuousOn a s') (hA : ContinuousOn A s') (hb : ContinuousOn b s')
    (hB : ContinuousOn B s') (hM : ∀ t ∈ s', MassesGe μ₀ (a t) (A t) (b t) (B t))
    (μ i j : Fin 4) {r n : ℕ} (hnr : n ≤ r) {κ cs : X → Fin r → ℝ}
    (hκc : ∀ e, ContinuousOn (fun t => κ t e) s') (hcsc : ∀ e, ContinuousOn (fun t => cs t e) s')
    (hT : ∀ t ∈ s', TrailOne n (κ t)) (hX : ∀ t ∈ s', ExtraGe μ₀ (κ t) (cs t)) :
    ContinuousOn (fun t => unitMLimitV c P s (κ t)
      (unitMMasses P.m (a t) (A t) (b t) (B t) (cs t)) p p' n μ i j) s' := by
  have hL := continuousOn_unitMLimitV_pow hc P hm hs hμ₀ hp hp' hq ha hA hb hB hM μ i j n
    (r := r) (κ := fun _ => 1) (cs := fun t e => cs t e / κ t e) hnr (fun _ _ => rfl)
    (fun _ => ⟨one_pos, le_rfl⟩)
    (fun e => (hcsc e).div (hκc e) fun t ht => (hX t ht e).1.ne')
    fun t ht e => div_ge_of_extraGe hμ₀ (hX t ht) e
  have hP : ContinuousOn (fun t => (∏ e, ((κ t e ^ 2 : ℝ) : ℂ))⁻¹) s' := by
    refine ContinuousOn.inv₀ (continuousOn_finsetProd _ fun e _ =>
      continuous_ofReal.comp_continuousOn ((hκc e).pow 2)) fun t ht => ?_
    exact Finset.prod_ne_zero_iff.2 fun e _ => by
      exact_mod_cast pow_ne_zero 2 (hX t ht e).1.ne'
  refine (hP.mul hL).congr fun t ht => ?_
  exact unitMLimitV_descale_all hc P hm hs hμ₀ (hM t ht) hp hp' hq hnr (hT t ht) (hX t ht) μ i j

/-! ### The spectral line of the vacuum polarization -/

/-- **The spectral line**: with `κₑ = √(x(1-x))` and `csₑ = M`, the extra line is set (a)'s
factor `fDen M ε x k = M² + x(1-x) k² - iε` of the element momentum `k`. -/
theorem lineDenom_unitM_spectral {r : ℕ} (c : Class5) (s : Fin 8) {κ : Fin r → ℝ}
    (p p' : Fin 4 → ℝ) (m a A b B : ℝ) {cs : Fin r → ℝ} (ε : ℝ) {e : Fin r} {x M : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hκ : κ e = √(x * (1 - x))) (hcs : cs e = M)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') (unitMMasses m a A b B cs) ε
        (mExtra r e) ℓ = fDen M ε x (elemMom c s p p' ℓ) := by
  rw [lineDenom_unitM_mExtra, hκ, hcs, Real.sq_sqrt (mem_Ioo_mul_pos hx).le, fDen,
    vacuumPolarizationFeynmanMass]
  push_cast
  ring

theorem div_sqrt_eq_specMu {M x : ℝ} (hM : 0 ≤ M) (hx : x ∈ Ioo (0 : ℝ) 1) :
    M / √(x * (1 - x)) = specMu M x := by
  rw [specMu, Real.sqrt_div' _ (mem_Ioo_mul_pos hx).le,
    Real.sqrt_sq hM]

/-- **The spectral line as a dispersion line**: with `κₑ = √(x(1-x))` and `csₑ = M`, the limit is
`(x(1-x))⁻¹` times the limit with the line unscaled, of mass `specMu M x = √(M²/(x(1-x)))` (the
form of `QED.TwoLoop.VPHalfAtGen.specLimit`). -/
theorem unitMLimitV_spectral {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {r n : ℕ} {κ cs : Fin r → ℝ} (hnr : n ≤ r) (hT : TrailOne n κ) (hX : ExtraGe μ₀ κ cs)
    {e : Fin r} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hκ : κ e = √(x * (1 - x))) (μ i j : Fin 4) :
    unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j =
      ((x * (1 - x) : ℝ) : ℂ)⁻¹ * unitMLimitV c P s (Function.update κ e 1)
        (unitMMasses P.m a A b B
          (Function.update cs e (specMu (cs e) x))) p p' n μ i j := by
  rw [unitMLimitV_descale hc P hm hs hμ₀ hM hp hp' hq hnr hT hX e μ i j, hκ,
    Real.sq_sqrt (mem_Ioo_mul_pos hx).le,
    div_sqrt_eq_specMu (hμ₀.le.trans (hX e).2.2) hx]

end QED.ChainProof.SetCUnitM

end
