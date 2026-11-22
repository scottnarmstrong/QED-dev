/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMDisp
public import QED.ChainProof.SetCUnitMDispScale

/-!
# The transverse unit of `repB` at fixed `ε`: decay uniform in `ε` and the `ε`/`x` interchange

Helper level for set (c) (stage L2, the bubble classes `repB i`). At the Feynman parameter `x`
of the inserted bubble the transverse unit carries the spectral line
`x(1-x) k² + M² - iε` (the first extra line, rescaled by `κ = √(x(1-x))`). The limit of this
unit is bounded by `C (1 + m_γ² + Λ²)³ / M²` uniformly in `x`
(`QED.ChainProof.SetCUnitM.norm_unitMLimitV_repB_disp_le`); here the same bound is proved at
every fixed `ε ∈ (0, 1]`, so that dominated convergence exchanges `ε → 0⁺` with `∫₀¹ dx`.

The descaling of the limit proof is not available at fixed `ε` (it would put the prescription
`ε/κ²` on one line); its two uses are replaced as follows.

* **Light dispersion mass** `M/κ`: the rescaled-line bound
  (`QED.ChainProof.SetCUnitM.norm_jointEnergyFirstIntegral_scale_le'`) gives `κ⁻² C` at every
  `ε`, uniformly in the masses (`norm_unitMScaled_le`), and `κ⁻² ≤ 2 μ_s² / M²`.
* **Heavy dispersion mass**: partial fractions against the element line `s` at fixed `ε`,
  `D_s⁻¹ D_t⁻¹ = (κ² D_t⁻¹ - D_s⁻¹) / (κ² D_s - D_t)`, with the complex constant
  `κ² μ_s² - M² + iε(1 - κ²)` of real part at most `-M²/2` (`unitMIntegrand_pf_scaled`): the
  first term is the unit with the element line rescaled (again `κ⁻² C`, cancelled by `κ²`), the
  second the unit without the dispersion line.

Results:

* `unitMScaled`, **`norm_unitMScaled_le`**: the unit with one rescaled line, bounded by `κ⁻² C`;
* **`unitMIntegrand_pf_scaled`**: the partial fraction at fixed `ε ≠ 0`;
* **`norm_unitMValue_disp_le`**: the unit with a dispersion line (`n = 0`), bounded by
  `C (1 + m_γ² + Λ²) / M²` uniformly in `ε > 0` and in `κ² ≤ 1/4`;
* `unitMValue_succ_eps`: the recursion in the powers `(k²)ⁿ` at fixed `ε`;
* **`norm_unitMValue_repB_disp_le`**: the transverse unit of `repB` at fixed `ε ∈ (0, 1]` is
  bounded by `C (1 + m_γ² + Λ²)³ / M²`, uniformly in `x ∈ (0, 1)` and `ε`;
* `stronglyMeasurable_jointEnergyFirstIntegral`, `continuous_unitMIntegrand_repB`: measurability
  in `x` at fixed `ε`;
* **`tendsto_integral_unitMValue_repB`**: for every weight `w` integrable on `(0, 1)`,
  `∫₀¹ w(x) I_ε(x) dx → unitMDispRepB = ∫₀¹ w(x) L(x) dx` as `ε → 0⁺`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrixPV classPVMasses
  LoopQuartic RefinedBound)
open QED.TwoLoop.VPHalfAtAssembly (specMu mem_Ioo_mul_pos)

variable {r : ℕ}

/-! ### One rescaled line of the unit -/

theorem mEmb_ne_mExtra (j : Fin 8) (e : Fin r) : mEmb r j ≠ mExtra r e := fun h => by
  have := congrArg Fin.val h
  have h1 : ((mExtra r e : Fin (r + 8)) : ℕ) = e + 8 := rfl
  have h2 : ((mEmb r j : Fin (r + 8)) : ℕ) = j := rfl
  have := j.isLt
  omega

theorem mExtra_not_mem_unitME (e : Fin r) : mExtra r e ∉ unitME r := by
  simp only [unitME, Finset.mem_map]
  rintro ⟨j, -, h⟩
  exact mEmb_ne_mExtra j e h

theorem mEmb_not_mem_unitME {s : Fin 8} (hs : 4 ≤ (s : ℕ)) : mEmb r s ∉ unitME r := by
  simp only [unitME, Finset.mem_map]
  rintro ⟨j, hj, h⟩
  have h' := (mEmb r).injective h
  subst h'
  revert hs
  fin_cases j <;> simp_all

theorem mScale_one : mScale (fun _ : Fin r => (1 : ℝ)) = 1 := by
  funext k
  rcases mem_mEmb_or_mExtra k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [mScale, mExt_mEmb]
  · simp [mScale, mExt_mExtra]

theorem mScale_update (e : Fin r) (κ : ℝ) :
    mScale (Function.update (fun _ => (1 : ℝ)) e κ) =
      Function.update (1 : Fin (r + 8) → ℝ) (mExtra r e) κ := by
  funext k
  rcases mem_mEmb_or_mExtra k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [mScale, mExt_mEmb, Function.update_of_ne (mEmb_ne_mExtra j e)]
  · simp only [mScale, mExt_mExtra, Function.update_apply, mExtra_injective.eq_iff]
    split_ifs <;> rfl

/-- The unit integrand (`n = 0`) with the line `i₀` rescaled by `κ`: its momentum is `κ k`, its
mass `κ Mᵢ₀`. -/
noncomputable def unitMScaled (c : Class5) (P : Params) (s : Fin 8) (i₀ : Fin (r + 8)) (κ : ℝ)
    (M : Fin (r + 8) → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  unitNum c P p p' μ i j ℓ * ∏ k, (lineDenom
    (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k • unitMMatrix c s (fun _ => 1) k)
    (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k •
      unitMMomenta c s (fun _ => 1) p p' k)
    (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k * M k) ε k ℓ)⁻¹

/-- **The unit with one rescaled extra line** is `unitMScaled`, the mass of that line divided
by its scale. -/
theorem unitMIntegrand_eq_scaled (c : Class5) (P : Params) (s : Fin 8) (e : Fin r) {κ : ℝ}
    (hκ : κ ≠ 0) (m a A b B : ℝ) (cs : Fin r → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ) (μ i j : Fin 4) :
    unitMIntegrand c P s (Function.update (fun _ => 1) e κ) (unitMMasses m a A b B cs) ε p p'
        0 μ i j =
      unitMScaled c P s (mExtra r e) κ (unitMMasses m a A b B (Function.update cs e (cs e / κ)))
        ε p p' μ i j := by
  have hα : unitMMatrix c s (Function.update (fun _ => 1) e κ) = fun k =>
      Function.update (1 : Fin (r + 8) → ℝ) (mExtra r e) κ k •
        unitMMatrix c s (fun _ => 1) k := by
    funext k
    simp only [unitMMatrix, mScale_update, mScale_one, Pi.one_apply, one_smul]
  have hp : unitMMomenta c s (Function.update (fun _ => 1) e κ) p p' = fun k =>
      Function.update (1 : Fin (r + 8) → ℝ) (mExtra r e) κ k •
        unitMMomenta c s (fun _ => 1) p p' k := by
    funext k
    simp only [unitMMomenta, mScale_update, mScale_one, Pi.one_apply, one_smul]
  have hM : unitMMasses m a A b B cs = fun k =>
      Function.update (1 : Fin (r + 8) → ℝ) (mExtra r e) κ k *
        unitMMasses m a A b B (Function.update cs e (cs e / κ)) k := by
    funext k
    rcases mem_mEmb_or_mExtra k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [unitMMasses, mExt_mEmb, Function.update_of_ne (mEmb_ne_mExtra j e)]
    · simp only [unitMMasses, mExt_mExtra, Function.update_apply, mExtra_injective.eq_iff]
      split_ifs with h
      · subst h; field_simp
      · simp
  funext ℓ
  simp only [unitMIntegrand, unitMScaled, pow_zero, mul_one, hα, hp]
  rw [hM]

section Scaled

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hp hp' hq

/-- **The unit with one rescaled line at fixed `ε`, bounded uniformly in `ε`**: one constant `C`
with `‖∫ unitMScaled‖ ≤ κ⁻² C` for all photon and extra masses `≥ μ₀` (those of the unscaled
lines; the rescaled line has mass `κ` times its entry), every `κ ≠ 0` and every `ε > 0`. -/
theorem norm_unitMScaled_le {i₀ : Fin (r + 8)} (hi₀ : i₀ ∉ unitME r) (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ (a A b B : ℝ) (cs : Fin r → ℝ) (κ ε : ℝ), MassesGe μ₀ a A b B →
      (∀ j, μ₀ ≤ cs j) → κ ≠ 0 → 0 < ε →
      ‖QED.TwoLoop.jointEnergyFirstIntegral 2
          (unitMScaled c P s i₀ κ (unitMMasses P.m a A b B cs) ε p p' μ i j)‖ ≤
        (κ ^ 2)⁻¹ * C := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hB : RefinedBound (unitMMatrix c s (fun _ : Fin r => (1 : ℝ))) (unitME r) 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitM hc P s _ p p' μ i j
  have hcrit := noSubdivergenceRefined_unitM hc s (κ := fun _ : Fin r => (1 : ℝ))
    (fun _ => one_ne_zero)
  refine ⟨π ^ 4 * ∫ x in QED.Integration.Feynman.simplexSet (r + 7), domFun Q
    (fun k => unitMMatrix c s (fun _ : Fin r => (1 : ℝ))
      (Equiv.swap (Fin.castSucc (⟨0, by omega⟩ : Fin (r + 7))) i₀ k))
    (fun k => unitMMomenta c s (fun _ : Fin r => (1 : ℝ)) p p'
      (Equiv.swap (Fin.castSucc (⟨0, by omega⟩ : Fin (r + 7))) i₀ k)) (unitConst P.m μ₀) x,
    fun a A b B cs κ ε hM hcs hκ hε => ?_⟩
  have hX : ExtraGe μ₀ (fun _ : Fin r => (1 : ℝ)) cs := fun j => ⟨one_pos, le_rfl, hcs j⟩
  have h := norm_jointEnergyFirstIntegral_scale_le' (Q := Q) (m := r + 7)
    (M := unitMMasses P.m a A b B cs) (by omega) hcrit hB (unitConst_pos hm hμ₀)
    (fun z hz hz1 hU => symanzikV_unitM_ge hc hs hμ₀ hM hX hp hp' hq hz hz1 hU) hi₀ hκ
    (σ := Function.update 1 i₀ κ) (Function.update_self _ _ _)
    (fun k hk => Function.update_of_ne hk _ _) hε
  have e : unitMScaled c P s i₀ κ (unitMMasses P.m a A b B cs) ε p p' μ i j = fun ℓ =>
      Q.eval ℓ * ∏ k, (lineDenom
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k • unitMMatrix c s (fun _ => 1) k)
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k •
          unitMMomenta c s (fun _ => 1) p p' k)
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k * unitMMasses P.m a A b B cs k)
        ε k ℓ)⁻¹ := by
    funext ℓ; rw [unitMScaled, hQ]
  rw [e]
  exact h

end Scaled

/-! ### Partial fractions against the element line at fixed `ε` -/

/-- The constant of the partial fraction `κ² D_u - D_t = κ² u² - t² + i ε (1 - κ²)`, with
`D_u = k² + u² - iε` and `D_t = κ² k² + t² - iε`. -/
noncomputable def pfConst (κ u t ε : ℝ) : ℂ :=
  ((κ ^ 2 * u ^ 2 - t ^ 2 : ℝ) : ℂ) + ((ε * (1 - κ ^ 2) : ℝ) : ℂ) * I

theorem pfConst_ne_zero {κ u t ε : ℝ} (h : κ ^ 2 * u ^ 2 ≠ t ^ 2) : pfConst κ u t ε ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp only [pfConst, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, zero_re] at this
  exact h (by linarith)

theorem abs_re_le_norm_pfConst (κ u t ε : ℝ) : |κ ^ 2 * u ^ 2 - t ^ 2| ≤ ‖pfConst κ u t ε‖ := by
  have hre : (pfConst κ u t ε).re = κ ^ 2 * u ^ 2 - t ^ 2 := by
    simp only [pfConst, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
  rw [← hre]
  exact Complex.abs_re_le_norm _

/-- The partial fraction `D_u⁻¹ D_t⁻¹ = (κ² D_t⁻¹ - D_u⁻¹) / (κ² D_u - D_t)`. -/
theorem pf_alg_scaled {K u t κ ε : ℝ} (hε : ε ≠ 0) (hcc : κ ^ 2 * u ^ 2 ≠ t ^ 2) (Z X : ℂ) :
    Z * (((((K + u ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * X) *
        (((κ ^ 2 * K + t ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹) =
      (pfConst κ u t ε)⁻¹ * (((κ ^ 2 : ℝ) : ℂ) *
          (Z * ((((κ ^ 2 * K + t ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * X)) -
        Z * ((((K + u ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * X)) := by
  have h1 := ofReal_sub_mul_I_ne_zero (y := K + u ^ 2) hε
  have h2 := ofReal_sub_mul_I_ne_zero (y := κ ^ 2 * K + t ^ 2) hε
  have h3 := pfConst_ne_zero (ε := ε) hcc
  have e : pfConst κ u t ε = ((κ ^ 2 : ℝ) : ℂ) * (((K + u ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) -
      ((((κ ^ 2 * K + t ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)) := by
    simp only [pfConst]; push_cast; ring
  rw [e] at h3 ⊢
  have key : ∀ D₁ D₂ k : ℂ, D₁ ≠ 0 → D₂ ≠ 0 → k * D₁ - D₂ ≠ 0 →
      Z * ((D₁⁻¹ * X) * D₂⁻¹) = (k * D₁ - D₂)⁻¹ * (k * (Z * (D₂⁻¹ * X)) - Z * (D₁⁻¹ * X)) := by
    intro D₁ D₂ k h₁ h₂ h₃
    rw [eq_inv_mul_iff_mul_eq₀ h₃]
    field_simp
  exact key _ _ _ h1 h2 h3

theorem lineMomentum_unitM_mEmb (c : Class5) (s : Fin 8) (κ : Fin r → ℝ) (p p' : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    QED.Integration.TwoLoop.lineMomentum (unitMMatrix c s κ) (unitMMomenta c s κ p p')
        (mEmb r s) ℓ = elemMom c s p p' ℓ := by
  have hα : unitMMatrix c s κ (mEmb r s) = castLoopMatrix (class5LoopMatrixPV c) s :=
    unitMMatrix_mEmb c s κ s
  have hp : unitMMomenta c s κ p p' (mEmb r s) = pvMomentaE c p p' s := by
    simp [unitMMomenta, mScale, mLine, mExt_mEmb]
  unfold QED.Integration.TwoLoop.lineMomentum elemMom
  rw [hα, hp]
  rfl

/-- **Partial fractions for a rescaled dispersion line at fixed `ε ≠ 0`.** With the last extra
line rescaled by `κ` (mass `t`), the others unscaled, and `μ_s` the mass of the element line `s`:
`I = c⁻¹ (κ² J - I(init cs))`, `c = κ² μ_s² - t² + iε(1-κ²)`, where `J` is the unit without the
last extra line and with the element line `s` rescaled by `κ`, of mass `t` (entry `t/κ`). -/
theorem unitMIntegrand_pf_scaled (c : Class5) (P : Params) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {κ : ℝ} (hκ : κ ≠ 0) {κv : Fin (r + 1) → ℝ} (hκl : κv (Fin.last r) = κ)
    (hinit : Fin.init κv = fun _ => 1) (m a A b B : ℝ) (cs : Fin (r + 1) → ℝ) {ε : ℝ}
    (hε : ε ≠ 0) (hcc : κ ^ 2 * unitMasses m a A b B s ^ 2 ≠ cs (Fin.last r) ^ 2)
    (p p' : Fin 4 → ℝ) (μ i j : Fin 4) :
    unitMIntegrand c P s κv (unitMMasses m a A b B cs) ε p p' 0 μ i j = fun ℓ =>
      (pfConst κ (unitMasses m a A b B s) (cs (Fin.last r)) ε)⁻¹ *
        (((κ ^ 2 : ℝ) : ℂ) * unitMScaled c P s (mEmb r s) κ
            (unitMMasses m (slotMa s (cs (Fin.last r) / κ) a) (slotMA s (cs (Fin.last r) / κ) A)
              (slotMb s (cs (Fin.last r) / κ) b) (slotMB s (cs (Fin.last r) / κ) B)
              (Fin.init cs)) ε p p' μ i j ℓ -
          unitMIntegrand c P s (fun _ => 1) (unitMMasses m a A b B (Fin.init cs)) ε p p' 0
            μ i j ℓ) := by
  funext ℓ
  set t := cs (Fin.last r)
  have hprod : ∀ f : Fin (r + 1 + 8) → ℂ,
      ∏ k, f k = (∏ k : Fin (r + 8), f (Fin.castSucc k)) * f (Fin.last (r + 8)) :=
    fun f => Fin.prod_univ_castSucc f
  have hlast := lineDenom_unitM_mExtra c s κv p p' m a A b B cs ε (Fin.last r) ℓ
  rw [mExtra_last] at hlast
  rw [hκl] at hlast
  set K := Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ)
  set u := unitMasses m a A b B s
  -- the line `s` of the unscaled unit and of the rescaled one
  have hDs : lineDenom (unitMMatrix c s (fun _ : Fin r => (1 : ℝ)))
      (unitMMomenta c s (fun _ : Fin r => (1 : ℝ)) p p') (unitMMasses m a A b B (Fin.init cs))
        ε (mEmb r s) ℓ = ((K + u ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := by
    rw [lineDenom_unitM_mEmb, unitMMasses_mEmb]
  have hDJ : lineDenom
      (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k •
        unitMMatrix c s (fun _ => 1) k)
      (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k •
        unitMMomenta c s (fun _ => 1) p p' k)
      (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k *
        unitMMasses m (slotMa s (t / κ) a) (slotMA s (t / κ) A) (slotMb s (t / κ) b)
          (slotMB s (t / κ) B) (Fin.init cs) k) ε (mEmb r s) ℓ =
      ((κ ^ 2 * K + t ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := by
    rw [lineDenom_scale, lineMomentum_unitM_mEmb, Function.update_self, unitMMasses_mEmb,
      unitMasses_slot hs, ite_eq_left rfl, mul_div_cancel₀ _ hκ]
  have hrest : ∏ k ∈ Finset.univ.erase (mEmb r s), (lineDenom
      (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k •
        unitMMatrix c s (fun _ => 1) k)
      (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k •
        unitMMomenta c s (fun _ => 1) p p' k)
      (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k *
        unitMMasses m (slotMa s (t / κ) a) (slotMA s (t / κ) A) (slotMb s (t / κ) b)
          (slotMB s (t / κ) B) (Fin.init cs) k) ε k ℓ)⁻¹ =
      ∏ k ∈ Finset.univ.erase (mEmb r s), (lineDenom (unitMMatrix c s (fun _ : Fin r => 1))
        (unitMMomenta c s (fun _ : Fin r => 1) p p') (unitMMasses m a A b B (Fin.init cs)) ε k
          ℓ)⁻¹ :=
    Finset.prod_congr rfl fun k hk => by
      have hk' := Finset.ne_of_mem_erase hk
      refine congrArg Inv.inv (lineDenom_congr ?_ ?_ ?_ ε ℓ)
      · simp [Function.update_of_ne hk']
      · simp [Function.update_of_ne hk']
      · simp [Function.update_of_ne hk', unitMMasses_slot hs _ _ _ _ _ _ _ k hk']
  simp only [unitMIntegrand, unitMScaled, hprod, lineDenom_unitM_castSucc, hlast, hinit,
    pow_zero, mul_one]
  rw [prod_split_at _ (mEmb r s), prod_split_at _ (mEmb r s), hDs, hDJ, hrest]
  exact pf_alg_scaled hε hcc _ _

/-! ### The dispersion line at fixed `ε`: decay uniform in its scale -/

theorem cons_one_eq_update (κ : ℝ) :
    (Fin.cons κ (fun _ => (1 : ℝ)) : Fin (r + 1) → ℝ) = Function.update (fun _ => 1) 0 κ := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp

theorem unitMIntegrand_one_eq_scaled (c : Class5) (P : Params) (s : Fin 8) (i₀ : Fin (r + 8))
    (M : Fin (r + 8) → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ) (μ i j : Fin 4) :
    unitMIntegrand c P s (fun _ => 1) M ε p p' 0 μ i j =
      unitMScaled c P s i₀ 1 M ε p p' μ i j := by
  have h1 : Function.update (1 : Fin (r + 8) → ℝ) i₀ 1 = 1 := by
    funext k; by_cases hk : k = i₀ <;> simp [hk]
  funext ℓ
  simp only [unitMIntegrand, unitMScaled, h1, pow_zero, mul_one, Pi.one_apply, one_smul,
    one_mul]

section Disp

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

include hc in
omit hc in
theorem jointEnergyFirstIntegrable_unitMScaled (hc : c ∈ openClasses) {i₀ : Fin (r + 8)}
    (hi₀ : i₀ ∉ unitME r) {κ : ℝ} (hκ : κ ≠ 0) (M : Fin (r + 8) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (μ i j : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMScaled c P s i₀ κ M ε p p' μ i j) := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hB : RefinedBound (unitMMatrix c s (fun _ : Fin r => (1 : ℝ))) (unitME r) 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitM hc P s _ p p' μ i j
  have hcrit := noSubdivergenceRefined_unitM hc s (κ := fun _ : Fin r => (1 : ℝ))
    (fun _ => one_ne_zero)
  have hσ0 : ∀ k, Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k ≠ 0 := fun k => by
    by_cases hk : k = i₀ <;> simp [hk, hκ]
  have h := jointEnergyFirstIntegrable_lineScale (m := r + 7) (p := unitMMomenta c s
    (fun _ : Fin r => (1 : ℝ)) p p') (by omega) hcrit hB hσ0 (fun e he =>
      Function.update_of_ne (by rintro rfl; exact hi₀ he) _ _)
    (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k * M k) hε
  have e : unitMScaled c P s i₀ κ M ε p p' μ i j = fun ℓ =>
      Q.eval ℓ * ∏ k, (lineDenom
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k • unitMMatrix c s (fun _ => 1) k)
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k •
          unitMMomenta c s (fun _ => 1) p p' k)
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k * M k) ε k ℓ)⁻¹ := by
    funext ℓ; rw [unitMScaled, hQ]
  rw [e]
  exact h

include hc hm hs hμ₀ hp hp' hq

/-- **The unit with a dispersion line at fixed `ε`, uniformly in `ε` and in the scale.** The
first extra line has scale `κ` with `κ² ≤ 1/4` and mass `M`, the others are unscaled: one
constant `C` with `‖I_ε‖ ≤ C (1 + m_γ² + Λ²) / M²` for all `ε > 0`, all such `κ` and all masses
`≥ μ₀` (photon masses `(m_γ, Λ, m_γ, Λ)`). Light dispersion mass `M/κ`: the rescaled-line bound
`κ⁻² C`; heavy: partial fractions against the element line (`unitMIntegrand_pf_scaled`). -/
theorem norm_unitMValue_disp_le (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ (κ M mγ Λ : ℝ) (cs : Fin r → ℝ) (ε : ℝ), 0 < κ → κ ^ 2 ≤ 1 / 4 → μ₀ ≤ M →
      μ₀ ≤ mγ → μ₀ ≤ Λ → (∀ j, μ₀ ≤ cs j) → 0 < ε →
      ‖unitMValue c P s (Fin.cons κ fun _ => 1) (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M cs)) ε
          p p' 0 μ i j‖ ≤ C * (1 + mγ ^ 2 + Λ ^ 2) / M ^ 2 := by
  obtain ⟨C₁, hC₁⟩ := norm_unitMScaled_le (r := r + 1) hc P hm hs hμ₀ hp hp' hq
    (mExtra_not_mem_unitME 0) μ i j
  obtain ⟨C₂, hC₂⟩ := norm_unitMScaled_le (r := r) hc P hm hs hμ₀ hp hp' hq
    (mEmb_not_mem_unitME hs) μ i j
  refine ⟨2 * |C₁| + 2 * (|C₂| + |C₂|), fun κ M mγ Λ cs ε hκ hκ4 hM hmγ hΛ hcs hε => ?_⟩
  have hM0 : 0 < M := hμ₀.trans_le hM
  have hκ1 : κ ≤ 1 := by nlinarith
  have hMκ : μ₀ ≤ M / κ := hM.trans (le_div_self hM0.le hκ hκ1)
  set S := 1 + mγ ^ 2 + Λ ^ 2 with hS
  set u := unitMasses P.m mγ Λ mγ Λ s with hu
  have hu0 : μ₀ ≤ u := by
    rcases unitMasses_photon hs P.m mγ Λ with h | h <;> rw [hu, h] <;> assumption
  have hu2 : u ^ 2 ≤ S := by
    rcases unitMasses_photon hs P.m mγ Λ with h | h <;> rw [hu, h] <;> nlinarith
  have hS1 : 1 ≤ S := by nlinarith [sq_nonneg mγ, sq_nonneg Λ]
  have hM2 : 0 < M ^ 2 := by positivity
  have hMg := massesGe_repB (μ₀ := μ₀) hmγ hΛ
  by_cases hcase : 2 * (κ ^ 2 * u ^ 2) ≤ M ^ 2
  · -- heavy dispersion mass: partial fractions
    have hcc : κ ^ 2 * u ^ 2 ≠ M ^ 2 := by intro h; nlinarith
    have hperm := unitMIntegrand_perm c P s (finRotate (r + 1)) (Fin.cons κ fun _ => 1) P.m mγ Λ
      mγ Λ (Fin.cons M cs) ε p p' 0 μ i j
    have hk : (Fin.cons κ fun _ => (1 : ℝ) : Fin (r + 1) → ℝ) ∘ finRotate (r + 1) =
        Fin.snoc (fun _ => 1) κ := (Fin.snoc_eq_cons_rotate _ _).symm
    have hc' : (Fin.cons M cs : Fin (r + 1) → ℝ) ∘ finRotate (r + 1) = Fin.snoc cs M :=
      (Fin.snoc_eq_cons_rotate _ _).symm
    rw [hk, hc'] at hperm
    have hpf := unitMIntegrand_pf_scaled c P hs hκ.ne' (κv := Fin.snoc (fun _ => 1) κ)
      (Fin.snoc_last _ _) (Fin.init_snoc _ _) P.m mγ Λ mγ Λ (Fin.snoc cs M) hε.ne'
      (by rw [Fin.snoc_last]; exact hcc) p p' μ i j
    rw [Fin.snoc_last, Fin.init_snoc] at hpf
    set k := pfConst κ u M ε
    set Mm := unitMMasses P.m (slotMa s (M / κ) mγ) (slotMA s (M / κ) Λ) (slotMb s (M / κ) mγ)
      (slotMB s (M / κ) Λ) cs
    have hJ := jointEnergyFirstIntegrable_unitMScaled P (s := s) (p := p) (p' := p') hc
      (mEmb_not_mem_unitME hs) hκ.ne' Mm hε μ i j
    have hB := jointEnergyFirstIntegrable_unitM hc P s (κ := fun _ : Fin r => (1 : ℝ))
      (fun _ => one_ne_zero) (unitMMasses P.m mγ Λ mγ Λ cs) p p' hε μ i j
    rw [unitMIntegrand_zero] at hB
    have hlin := jointEnergyFirstIntegrable_mul_add_mul hJ hB (k⁻¹ * ((κ ^ 2 : ℝ) : ℂ)) (-k⁻¹)
    have hval : unitMValue c P s (Fin.cons κ fun _ => 1)
        (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M cs)) ε p p' 0 μ i j =
        k⁻¹ * (((κ ^ 2 : ℝ) : ℂ) * QED.TwoLoop.jointEnergyFirstIntegral 2
          (unitMScaled c P s (mEmb r s) κ Mm ε p p' μ i j) -
          unitMValue c P s (fun _ => 1) (unitMMasses P.m mγ Λ mγ Λ cs) ε p p' 0 μ i j) := by
      unfold unitMValue
      rw [← hperm, hpf, unitMIntegrand_zero c P s (fun _ : Fin r => (1 : ℝ))]
      have e : (fun ℓ => k⁻¹ * (((κ ^ 2 : ℝ) : ℂ) * unitMScaled c P s (mEmb r s) κ Mm ε p p' μ i j
          ℓ - unitNum c P p p' μ i j ℓ * ∏ k, (lineDenom (unitMMatrix c s fun _ => 1)
            (unitMMomenta c s (fun _ => 1) p p') (unitMMasses P.m mγ Λ mγ Λ cs) ε k ℓ)⁻¹)) =
          fun ℓ => k⁻¹ * ((κ ^ 2 : ℝ) : ℂ) * unitMScaled c P s (mEmb r s) κ Mm ε p p' μ i j ℓ +
            -k⁻¹ * (unitNum c P p p' μ i j ℓ * ∏ k, (lineDenom (unitMMatrix c s fun _ => 1)
              (unitMMomenta c s (fun _ => 1) p p') (unitMMasses P.m mγ Λ mγ Λ cs) ε k ℓ)⁻¹) :=
        funext fun ℓ => by ring
      rw [e, hlin.2]
      ring
    have hJb := hC₂ (slotMa s (M / κ) mγ) (slotMA s (M / κ) Λ) (slotMb s (M / κ) mγ)
      (slotMB s (M / κ) Λ) cs κ ε (massesGe_slot hMg hMκ) hcs hκ.ne' hε
    have hBb := hC₂ mγ Λ mγ Λ cs 1 ε hMg hcs one_ne_zero hε
    rw [← unitMIntegrand_one_eq_scaled] at hBb
    change ‖unitMValue c P s (fun _ => 1) (unitMMasses P.m mγ Λ mγ Λ cs) ε p p' 0 μ i j‖ ≤ _
      at hBb
    have hkn : M ^ 2 / 2 ≤ ‖k‖ := by
      refine le_trans ?_ (abs_re_le_norm_pfConst κ u M ε)
      rw [abs_of_neg (by nlinarith)]
      linarith
    have hk0 : 0 < ‖k‖ := lt_of_lt_of_le (by positivity) hkn
    rw [hval, norm_mul, norm_inv]
    have hκ2 : ((κ ^ 2)⁻¹ : ℝ) * κ ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    calc ‖k‖⁻¹ * ‖((κ ^ 2 : ℝ) : ℂ) * QED.TwoLoop.jointEnergyFirstIntegral 2
            (unitMScaled c P s (mEmb r s) κ Mm ε p p' μ i j) -
          unitMValue c P s (fun _ => 1) (unitMMasses P.m mγ Λ mγ Λ cs) ε p p' 0 μ i j‖
        ≤ (M ^ 2 / 2)⁻¹ * (κ ^ 2 * ((κ ^ 2)⁻¹ * C₂) + (1 ^ 2)⁻¹ * C₂) := by
          refine mul_le_mul (inv_anti₀ (by positivity) hkn) ((norm_sub_le _ _).trans
            (add_le_add ?_ hBb)) (norm_nonneg _) (by positivity)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left hJb (by positivity)
      _ ≤ 2 * (|C₂| + |C₂|) / M ^ 2 := by
          rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (κ ^ 2 : ℝ) ≠ 0), one_mul,
            one_pow, inv_one, one_mul]
          rw [inv_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hM2]
          nlinarith [le_abs_self C₂]
      _ ≤ (2 * |C₁| + 2 * (|C₂| + |C₂|)) * S / M ^ 2 := by
          rw [div_le_div_iff_of_pos_right hM2]
          nlinarith [abs_nonneg C₁, abs_nonneg C₂]
  · -- light dispersion mass: the rescaled-line bound and `κ⁻² ≤ 2 u² / M²`
    push Not at hcase
    rw [unitMValue, cons_one_eq_update, unitMIntegrand_eq_scaled c P s 0 hκ.ne']
    have h := hC₁ mγ Λ mγ Λ (Function.update (Fin.cons M cs) 0 ((Fin.cons M cs : Fin (r + 1) → ℝ)
      0 / κ)) κ ε hMg (fun j => by
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa using hMκ
        · simpa [Function.update_of_ne (Fin.succ_ne_zero j)] using hcs j) hκ.ne' hε
    refine h.trans ?_
    have hκinv : (κ ^ 2)⁻¹ ≤ 2 * S / M ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ hM2]
      nlinarith
    calc (κ ^ 2)⁻¹ * C₁ ≤ (κ ^ 2)⁻¹ * |C₁| := mul_le_mul_of_nonneg_left (le_abs_self _)
          (by positivity)
      _ ≤ 2 * S / M ^ 2 * |C₁| := mul_le_mul_of_nonneg_right hκinv (abs_nonneg _)
      _ ≤ (2 * |C₁| + 2 * (|C₂| + |C₂|)) * S / M ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hM2]
          nlinarith [abs_nonneg C₁, abs_nonneg C₂]

omit hc hm hs hμ₀ hp hp' hq in
/-- **One factor `k²` cancels the last extra line, for the values at fixed `ε > 0`.** -/
theorem unitMValue_succ_eps {κ : Fin (r + 1) → ℝ} (hκ : κ (Fin.last r) = 1) (m a A b B : ℝ)
    (cs : Fin (r + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) (μ i j : Fin 4)
    (h₁ : QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s (Fin.init κ)
      (unitMMasses m a A b B (Fin.init cs)) ε p p' n μ i j))
    (h₂ : QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s κ
      (unitMMasses m a A b B cs) ε p p' n μ i j)) :
    unitMValue c P s κ (unitMMasses m a A b B cs) ε p p' (n + 1) μ i j =
      unitMValue c P s (Fin.init κ) (unitMMasses m a A b B (Fin.init cs)) ε p p' n μ i j -
        (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) *
          unitMValue c P s κ (unitMMasses m a A b B cs) ε p p' n μ i j := by
  have h := jointEnergyFirstIntegrable_sub_mul h₁ h₂
    (((cs (Fin.last r) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)
  unfold unitMValue
  rw [unitMIntegrand_succ c P s hκ m a A b B cs hε.ne' p p' n μ i j]
  exact h.2

omit hc hm hs hμ₀ hp hp' hq in
theorem norm_sq_sub_mul_I_le {a ε : ℝ} (hε : 0 ≤ ε) : ‖((a ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I‖ ≤
    a ^ 2 + ε := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg (sq_nonneg a), Real.norm_of_nonneg hε]

/-- **The transverse unit of `repB` at fixed `ε`, bounded uniformly in `ε` and `x`**: one
constant `C` with `‖I_ε(x)‖ ≤ C (1 + m_γ² + Λ²)³ / M²` for all `x ∈ (0, 1)`, `ε ∈ (0, 1]` and
all masses `≥ μ₀`. This is the `ε`-uniform version of `norm_unitMLimitV_repB_disp_le`. -/
theorem norm_unitMValue_repB_disp_le (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ M mγ Λ ε : ℝ, μ₀ ≤ M → μ₀ ≤ mγ → μ₀ ≤ Λ → 0 < ε → ε ≤ 1 →
      ‖unitMValue c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2
          μ i j‖ ≤ C * (1 + mγ ^ 2 + Λ ^ 2) ^ 3 / M ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := norm_unitMValue_disp_le (r := 0) hc P hm hs hμ₀ hp hp' hq μ i j
  obtain ⟨C₁, hC₁⟩ := norm_unitMValue_disp_le (r := 1) hc P hm hs hμ₀ hp hp' hq μ i j
  obtain ⟨C₂, hC₂⟩ := norm_unitMValue_disp_le (r := 2) hc P hm hs hμ₀ hp hp' hq μ i j
  refine ⟨|C₀| + 2 * |C₁| + |C₂|, fun x hx M mγ Λ ε hM hmγ hΛ hε hε1 => ?_⟩
  have hw := mem_Ioo_mul_pos hx
  set κ := √(x * (1 - x)) with hκdef
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hw
  have hκ2 : κ ^ 2 ≤ 1 / 4 := by
    rw [hκdef, Real.sq_sqrt hw.le]; nlinarith [sq_nonneg (x - 1 / 2)]
  have hκ1 : κ ≤ 1 := by nlinarith
  have hM0 : 0 < M := hμ₀.trans_le hM
  have hM2 : 0 < M ^ 2 := by positivity
  set S := 1 + mγ ^ 2 + Λ ^ 2 with hS
  have hS1 : 1 ≤ S := by nlinarith [sq_nonneg mγ, sq_nonneg Λ]
  set K₃ : Fin 3 → ℝ := Fin.cons κ fun _ => 1
  set K₂ : Fin 2 → ℝ := Fin.cons κ fun _ => 1
  set K₁ : Fin 1 → ℝ := Fin.cons κ fun _ => 1
  have hK₃ : repBKappa x = K₃ := by funext j; fin_cases j <;> rfl
  have hi₃ : Fin.init K₃ = K₂ := by funext j; fin_cases j <;> rfl
  have hi₂ : Fin.init K₂ = K₁ := by funext j; fin_cases j; rfl
  have hE₃ : repBExtra M mγ Λ = Fin.cons M ![mγ, Λ] := rfl
  have hj₃ : Fin.init (Fin.cons M ![mγ, Λ] : Fin 3 → ℝ) = Fin.cons M ![mγ] := by
    funext j; fin_cases j <;> rfl
  have hj₂ : Fin.init (Fin.cons M ![mγ] : Fin 2 → ℝ) = Fin.cons M ![] := by
    funext j; fin_cases j; rfl
  have hMg := massesGe_repB (μ₀ := μ₀) hmγ hΛ
  have hX₂ : ExtraGe μ₀ K₂ (Fin.cons M ![mγ]) := fun l => by
    fin_cases l
    · exact ⟨hκ0, hκ1, hM⟩
    · exact ⟨one_pos, le_rfl, hmγ⟩
  have hX₃ : ExtraGe μ₀ K₃ (Fin.cons M ![mγ, Λ]) := fun l => by
    fin_cases l
    · exact ⟨hκ0, hκ1, hM⟩
    · exact ⟨one_pos, le_rfl, hmγ⟩
    · exact ⟨one_pos, le_rfl, hΛ⟩
  have hT₂ : TrailOne 1 K₂ := fun l hl => by
    fin_cases l
    · simp at hl
    · rfl
  have hT₃ : TrailOne 1 K₃ := fun l hl => by
    fin_cases l
    · simp at hl
    · simp at hl
    · rfl
  -- integrability of the pieces
  have hI₁₂ := (unitM_pow hc P hm hs hμ₀ hMg hp hp' hq 1 (by norm_num) hT₂ hX₂).1 ε hε μ i j
  have hI₁₃ := (unitM_pow hc P hm hs hμ₀ hMg hp hp' hq 1 (by norm_num) hT₃ hX₃).1 ε hε μ i j
  have hI₀ : ∀ {r : ℕ} (κv cs : Fin r → ℝ), (∀ j, κv j ≠ 0) →
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s κv
        (unitMMasses P.m mγ Λ mγ Λ cs) ε p p' 0 μ i j) := fun κv cs h =>
    jointEnergyFirstIntegrable_unitM hc P s h _ p p' hε μ i j
  have hne : ∀ {r : ℕ} (j : Fin (r + 1)), (Fin.cons κ (fun _ => 1) : Fin (r + 1) → ℝ) j ≠ 0 :=
    fun j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hκ0.ne'
      · simp
  -- the recursion
  have e₂ := unitMValue_succ_eps (c := c) P (s := s) (p := p) (p' := p') (κ := K₃) rfl P.m mγ Λ
    mγ Λ (Fin.cons M ![mγ, Λ]) hε 1 μ i j (by rw [hi₃, hj₃]; exact hI₁₂) hI₁₃
  rw [hi₃, hj₃] at e₂
  have e₁a := unitMValue_succ_eps (c := c) P (s := s) (p := p) (p' := p') (κ := K₂) rfl P.m mγ Λ
    mγ Λ (Fin.cons M ![mγ]) hε 0 μ i j (by rw [hi₂, hj₂]; exact hI₀ _ _ hne) (hI₀ _ _ hne)
  rw [hi₂, hj₂] at e₁a
  have e₁b := unitMValue_succ_eps (c := c) P (s := s) (p := p) (p' := p') (κ := K₃) rfl P.m mγ Λ
    mγ Λ (Fin.cons M ![mγ, Λ]) hε 0 μ i j (by rw [hi₃, hj₃]; exact hI₀ _ _ hne) (hI₀ _ _ hne)
  rw [hi₃, hj₃] at e₁b
  rw [hK₃, hE₃, e₂, e₁a, e₁b]
  -- the bounds
  have b₀ := hC₀ κ M mγ Λ ![] ε hκ0 hκ2 hM hmγ hΛ (fun j => j.elim0) hε
  have b₁ := hC₁ κ M mγ Λ ![mγ] ε hκ0 hκ2 hM hmγ hΛ (fun j => by fin_cases j; exact hmγ) hε
  have b₂ := hC₂ κ M mγ Λ ![mγ, Λ] ε hκ0 hκ2 hM hmγ hΛ (fun j => by
    fin_cases j
    · exact hmγ
    · exact hΛ) hε
  have tγ : ‖((((Fin.cons M ![mγ] : Fin 2 → ℝ) (Fin.last 1)) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I‖ ≤ S :=
    (norm_sq_sub_mul_I_le hε.le).trans (by simp; nlinarith [sq_nonneg Λ])
  have tΛ : ‖((((Fin.cons M ![mγ, Λ] : Fin 3 → ℝ) (Fin.last 2)) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I‖ ≤
      S := (norm_sq_sub_mul_I_le hε.le).trans (by simp; nlinarith [sq_nonneg mγ])
  set v₀ := unitMValue c P s K₁ (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M ![])) ε p p' 0 μ i j
  set v₁ := unitMValue c P s K₂ (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M ![mγ])) ε p p' 0 μ i j
  set v₂ := unitMValue c P s K₃ (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M ![mγ, Λ])) ε p p' 0 μ i j
  set a := ((((Fin.cons M ![mγ] : Fin 2 → ℝ) (Fin.last 1)) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I
  set b := ((((Fin.cons M ![mγ, Λ] : Fin 3 → ℝ) (Fin.last 2)) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I
  have hv₀ : ‖v₀‖ ≤ |C₀| * S / M ^ 2 := b₀.trans (by gcongr; exact le_abs_self _)
  have hv₁ : ‖v₁‖ ≤ |C₁| * S / M ^ 2 := b₁.trans (by gcongr; exact le_abs_self _)
  have hv₂ : ‖v₂‖ ≤ |C₂| * S / M ^ 2 := b₂.trans (by gcongr; exact le_abs_self _)
  have ha : ‖a‖ ≤ S := tγ
  have hb : ‖b‖ ≤ S := tΛ
  clear_value v₀ v₁ v₂ a b
  have hS0 : 0 ≤ S := by linarith
  have hq0 : 0 ≤ S / M ^ 2 := by positivity
  have key : ‖v₀ - a * v₁ - b * (v₁ - b * v₂)‖ ≤
      ‖v₀‖ + ‖a‖ * ‖v₁‖ + ‖b‖ * (‖v₁‖ + ‖b‖ * ‖v₂‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (by
      rw [norm_mul])) ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
    rw [norm_mul]
  refine key.trans ?_
  set X := S / M ^ 2
  have e : (|C₀| + 2 * |C₁| + |C₂|) * S ^ 3 / M ^ 2 = (|C₀| + 2 * |C₁| + |C₂|) * S ^ 2 * X := by
    simp only [X]; ring
  rw [e]
  have hv₀' : ‖v₀‖ ≤ |C₀| * X := by simpa [X, mul_div_assoc] using hv₀
  have hv₁' : ‖v₁‖ ≤ |C₁| * X := by simpa [X, mul_div_assoc] using hv₁
  have hv₂' : ‖v₂‖ ≤ |C₂| * X := by simpa [X, mul_div_assoc] using hv₂
  have h1 : S ≤ S ^ 2 := le_self_pow₀ hS1 (by norm_num)
  have hA0 := abs_nonneg C₀
  have hA1 := abs_nonneg C₁
  have hA2 := abs_nonneg C₂
  have hn0 := norm_nonneg v₀
  have hn1 := norm_nonneg v₁
  have hn2 := norm_nonneg v₂
  have hna := norm_nonneg a
  have hnb := norm_nonneg b
  have hX0 : 0 ≤ X := hq0
  have t1 : ‖a‖ * ‖v₁‖ ≤ S * (|C₁| * X) := mul_le_mul ha hv₁' hn1 hS0
  have t2 : ‖b‖ * ‖v₂‖ ≤ S * (|C₂| * X) := mul_le_mul hb hv₂' hn2 hS0
  have t3 : ‖b‖ * (‖v₁‖ + ‖b‖ * ‖v₂‖) ≤ S * (|C₁| * X + S * (|C₂| * X)) :=
    mul_le_mul hb (add_le_add hv₁' t2) (by positivity) hS0
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS1
  have u0 := mul_le_mul_of_nonneg_left hS2 hA0
  have u1 := mul_le_mul_of_nonneg_left h1 hA1
  have hfin : |C₀| * X + S * (|C₁| * X) + S * (|C₁| * X + S * (|C₂| * X)) ≤
      (|C₀| + 2 * |C₁| + |C₂|) * S ^ 2 * X := by
    have e1 : |C₀| * X + S * (|C₁| * X) + S * (|C₁| * X + S * (|C₂| * X)) =
        (|C₀| * 1 + 2 * (|C₁| * S) + |C₂| * S ^ 2) * X := by ring
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ hX0
    linarith only [u0, u1]
  linarith only [t1, t3, hv₀', hfin]

end Disp

/-! ### Measurability in the Feynman parameter and the `ε → 0⁺` limit under `∫₀¹ dx` -/

/-- **Measurability of a joint energy-first integral in a parameter**: if `(x, ℓ) ↦ F x ℓ` is
continuous, `x ↦ ∫_D F x` is strongly measurable. -/
theorem stronglyMeasurable_jointEnergyFirstIntegral {F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hF : Continuous fun q : ℝ × (Fin 2 → Fin 4 → ℝ) => F q.1 q.2) :
    StronglyMeasurable fun x => QED.TwoLoop.jointEnergyFirstIntegral 2 (F x) := by
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  have hG : Continuous fun q : (ℝ × (Fin 2 → Fin 3 → ℝ)) × (Fin 2 → ℝ) =>
      F q.1.1 (fun s => (Fin.cons (q.2 s) (q.1.2 s) : Fin 4 → ℝ)) :=
    hF.comp (continuous_fst.fst.prodMk (continuous_pi fun s =>
      Continuous.finCons ((continuous_apply s).comp continuous_snd)
        ((continuous_apply s).comp continuous_fst.snd)))
  exact hG.stronglyMeasurable.integral_prod_right'.integral_prod_right'

theorem continuous_repBKappa_apply (l : Fin 3) : Continuous fun x => repBKappa x l := by
  fin_cases l
  · exact Real.continuous_sqrt.comp (continuous_id.mul (continuous_const.sub continuous_id))
  · exact continuous_const
  · exact continuous_const

theorem continuous_mScale_repBKappa (k : Fin (3 + 8)) :
    Continuous fun x => mScale (repBKappa x) k := by
  unfold mScale mExt
  split_ifs
  · exact continuous_const
  · exact continuous_repBKappa_apply _

theorem continuous_lineMomentum_apply {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ)
    (q : Fin (n + 1) → Fin 4 → ℝ) (k : Fin (n + 1)) :
    Continuous fun ℓ : Fin 2 → Fin 4 → ℝ => QED.Integration.TwoLoop.lineMomentum α q k ℓ := by
  unfold QED.Integration.TwoLoop.lineMomentum
  fun_prop

theorem continuous_dotSelf_comp {X : Type*} [TopologicalSpace X] {f : X → Fin 4 → ℝ}
    (hf : Continuous f) : Continuous fun x => Minkowski.dot (f x) (f x) := by
  unfold Minkowski.dot
  refine continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun ν _ => ?_
  exact (continuous_const.mul ((continuous_apply μ).comp hf)).mul ((continuous_apply ν).comp hf)

theorem continuous_inv_lineDenom_scale {n : ℕ} (σ : ℝ → Fin (n + 1) → ℝ)
    (hσ : ∀ k, Continuous fun x => σ x k) (α : Fin (n + 1) → Fin 2 → ℝ)
    (q : Fin (n + 1) → Fin 4 → ℝ) (M : Fin (n + 1) → ℝ) {ε : ℝ} (hε : ε ≠ 0) (k : Fin (n + 1)) :
    Continuous fun z : ℝ × (Fin 2 → Fin 4 → ℝ) =>
      (lineDenom (fun i => σ z.1 i • α i) (fun i => σ z.1 i • q i) M ε k z.2)⁻¹ := by
  simp only [lineDenom_scale]
  refine Continuous.inv₀ ?_ fun z => ofReal_sub_mul_I_ne_zero hε
  refine (continuous_ofReal.comp ?_).sub continuous_const
  exact ((((hσ k).comp continuous_fst).pow 2).mul
    (continuous_dotSelf_comp ((continuous_lineMomentum_apply α q k).comp continuous_snd))).add
    continuous_const

/-- The transverse integrand of `repB` is jointly continuous in the Feynman parameter and the
loop momenta at every `ε ≠ 0`. -/
theorem continuous_unitMIntegrand_repB {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (s : Fin 8) (M : Fin (3 + 8) → ℝ) {ε : ℝ} (hε : ε ≠ 0) (p p' : Fin 4 → ℝ) (n : ℕ)
    (μ i j : Fin 4) :
    Continuous fun q : ℝ × (Fin 2 → Fin 4 → ℝ) =>
      unitMIntegrand c P s (repBKappa q.1) M ε p p' n μ i j q.2 := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hN : Continuous fun q : ℝ × (Fin 2 → Fin 4 → ℝ) => unitNum c P p p' μ i j q.2 := by
    rw [← hQ]; exact Q.continuous_eval.comp continuous_snd
  have hE : Continuous fun q : ℝ × (Fin 2 → Fin 4 → ℝ) => elemSq c s p p' q.2 := by
    unfold elemSq elemMom
    exact continuous_ofReal.comp (continuous_dotSelf_comp
      ((continuous_lineMomentum_apply _ _ s).comp continuous_snd))
  have hD : ∀ k, Continuous fun q : ℝ × (Fin 2 → Fin 4 → ℝ) =>
      (lineDenom (unitMMatrix c s (repBKappa q.1)) (unitMMomenta c s (repBKappa q.1) p p') M ε
        k q.2)⁻¹ := fun k =>
    continuous_inv_lineDenom_scale (fun x => mScale (repBKappa x)) continuous_mScale_repBKappa
      (fun k => castLoopMatrix (class5LoopMatrixPV c) (mLine s k))
      (fun k => pvMomentaE c p p' (mLine s k)) M hε k
  unfold unitMIntegrand
  exact (hN.mul (hE.pow n)).mul (continuous_finsetProd _ fun k _ => hD k)

section Limit

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hp hp' hq

/-- **The `ε → 0⁺` limit commutes with the dispersion integral of `repB`**: for every weight
`w` integrable on `(0, 1)`,
`∫₀¹ w(x) I_ε(x) dx → ∫₀¹ w(x) L(x) dx = unitMDispRepB`, `I_ε(x)` the transverse unit of `repB`
at fixed `ε` and `L(x)` its limit (dominated convergence with the `ε`-uniform bound
`norm_unitMValue_repB_disp_le`). -/
theorem tendsto_integral_unitMValue_repB {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1))
    {M mγ Λ : ℝ} (hM : μ₀ ≤ M) (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ) (μ i j : Fin 4) :
    Tendsto (fun ε => ∫ x in Ioo (0 : ℝ) 1, w x * unitMValue c P s (repBKappa x)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j) (𝓝[>] 0)
      (𝓝 (unitMDispRepB c P s w M mγ Λ p p' μ i j)) := by
  obtain ⟨C, hC⟩ := norm_unitMValue_repB_disp_le hc P hm hs hμ₀ hp hp' hq μ i j
  simp only [unitMDispRepB, Matrix.of_apply]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖w x‖ * (C * (1 + mγ ^ 2 + Λ ^ 2) ^ 3 / M ^ 2)) ?_ ?_
    (hw.norm.mul_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hw.aestronglyMeasurable.mul (stronglyMeasurable_jointEnergyFirstIntegral
      (continuous_unitMIntegrand_repB hc P s _ hε.ne' p p' 2 μ i j)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x hx M mγ Λ ε hM hmγ hΛ hε.1 hε.2) (norm_nonneg _)
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
    exact ((unitM_repB hc P hm hs hμ₀ hmγ hΛ hp hp' hq hx hM).2 μ i j).const_mul (w x)

end Limit

end QED.ChainProof.SetCUnitM

end
