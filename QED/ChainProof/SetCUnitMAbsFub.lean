/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMAbsDisp
public import QED.ChainProof.SetCMainBFub

/-!
# The transverse unit of `repB`: the Feynman parameter through the joint energy-first integral

Helper level for set (c) (stage L2, the `x`-Fubini of the `repB` classes). Condition `h₁` of
`QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_setIntegral` for the weighted transverse unit
`w(x) I_x` of `repB`: at every fixed spatial `v`, the integrand is integrable jointly in the
Feynman parameter `x ∈ (0, 1)` and the energies `t`. Together with condition `h₂`
(`QED.ChainProof.SetCUnitM.integrable_energyIntegral_unitM_repB`) this moves `∫₀¹ dx` through the
joint energy-first integral.

At fixed `v` no scaling argument is needed: the dispersion line `D = κ² k² + M² - iε` satisfies
`|D⁻¹| ≤ ε⁻¹` for every `κ`, and the integrand with that line dropped does not depend on `x`. Its
energy integrability at `(k²)²` follows from the recursion `k² D⁻¹ = 1 - (μ² - iε) D⁻¹` on the two
unscaled extra lines.

* `jointEnergyFirstIntegrable_unitM_pow`: both stages integrable with `(k²)ⁿ`, the last `n` extra
  lines unscaled, any masses, `ε > 0`;
* `norm_unitMIntegrand_le_init`: dropping the last extra line costs at most `ε⁻¹`;
* **`integrable_unitM_repB_energy`**: condition `h₁` for `w(x) I_x`;
* **`jointEnergyFirstIntegral_setIntegral_unitM_repB`**: the joint energy-first integral of
  `∫₀¹ w(x) I_x dx` is `∫₀¹ w(x) unitMValue(x) dx`, both stages integrable.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.Integration.TwoLoop (lineDenom)

/-! ### Integrability with powers of `k²`, any masses -/

section Pow

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (s : Fin 8)
include hc

/-- **Both stages are integrable with `(k²)ⁿ`** when the last `n ≤ r` extra lines are unscaled
and all scales are nonzero, for any masses and `ε > 0`. -/
theorem jointEnergyFirstIntegrable_unitM_pow (n : ℕ) : ∀ {r : ℕ} {κ : Fin r → ℝ}, n ≤ r →
    TrailOne n κ → (∀ j, κ j ≠ 0) → ∀ (m a A b B : ℝ) (cs : Fin r → ℝ) {ε : ℝ}, 0 < ε →
    ∀ (p p' : Fin 4 → ℝ) (μ i j : Fin 4),
      QED.TwoLoop.jointEnergyFirstIntegrable 2
        (unitMIntegrand c P s κ (unitMMasses m a A b B cs) ε p p' n μ i j) := by
  induction n with
  | zero =>
    intro r κ _ _ hκ m a A b B cs ε hε p p' μ i j
    exact jointEnergyFirstIntegrable_unitM hc P s hκ _ p p' hε μ i j
  | succ n ih =>
    intro r κ hnr hT hκ m a A b B cs ε hε p p' μ i j
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [unitMIntegrand_succ c P s hT.last m a A b B cs hε.ne' p p' n μ i j]
    exact (jointEnergyFirstIntegrable_sub_mul
      (ih (by omega) hT.init (fun j => hκ _) m a A b B (Fin.init cs) hε p p' μ i j)
      (ih (by omega) hT.of_succ hκ m a A b B cs hε p p' μ i j) _).1

end Pow

/-! ### Dropping the last extra line -/

theorem norm_inv_ofReal_sub_mul_I_le (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖(((y : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹‖ ≤ ε⁻¹ := by
  have him : ε ≤ ‖((y : ℝ) : ℂ) - (ε : ℂ) * I‖ := by
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    simp [abs_of_pos hε]
  rw [norm_inv]
  exact inv_anti₀ hε him

/-- **Dropping the last extra line costs at most `ε⁻¹`**, whatever its scale and mass. -/
theorem norm_unitMIntegrand_le_init {r : ℕ} (c : Class5) (P : Params) (s : Fin 8)
    (κ : Fin (r + 1) → ℝ) (m a A b B : ℝ) (cs : Fin (r + 1) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (p p' : Fin 4 → ℝ) (n : ℕ) (μ i j : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖unitMIntegrand c P s κ (unitMMasses m a A b B cs) ε p p' n μ i j ℓ‖ ≤
      ε⁻¹ * ‖unitMIntegrand c P s (Fin.init κ) (unitMMasses m a A b B (Fin.init cs)) ε p p' n
        μ i j ℓ‖ := by
  have hprod : ∀ f : Fin (r + 1 + 8) → ℂ,
      ∏ k, f k = (∏ k : Fin (r + 8), f (Fin.castSucc k)) * f (Fin.last (r + 8)) :=
    fun f => Fin.prod_univ_castSucc f
  have hlast := lineDenom_unitM_mExtra c s κ p p' m a A b B cs ε (Fin.last r) ℓ
  rw [mExtra_last] at hlast
  simp only [unitMIntegrand, hprod, lineDenom_unitM_castSucc, hlast]
  rw [← mul_assoc, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_inv_ofReal_sub_mul_I_le _ hε) (norm_nonneg _)

/-! ### Condition `h₁` for the transverse unit of `repB` -/

theorem repBKappa_comp_finRotate (x : ℝ) :
    Fin.init (repBKappa x ∘ finRotate 3) = ![1, 1] := by
  funext j; fin_cases j <;> rfl

theorem repBExtra_comp_finRotate (M mγ Λ : ℝ) :
    Fin.init (repBExtra M mγ Λ ∘ finRotate 3) = ![mγ, Λ] := by
  funext j; fin_cases j <;> rfl

theorem norm_unitMIntegrand_repB_le (c : Class5) (P : Params) (s : Fin 8) (x : ℝ)
    (M mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (p p' : Fin 4 → ℝ) (n : ℕ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    ‖unitMIntegrand c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' n
        μ i j ℓ‖ ≤
      ε⁻¹ * ‖unitMIntegrand c P s ![1, 1] (unitMMasses P.m mγ Λ mγ Λ ![mγ, Λ]) ε p p' n
        μ i j ℓ‖ := by
  rw [← unitMIntegrand_perm c P s (finRotate 3) (repBKappa x) P.m mγ Λ mγ Λ
    (repBExtra M mγ Λ) ε p p' n μ i j]
  have h := norm_unitMIntegrand_le_init c P s (repBKappa x ∘ finRotate 3) P.m mγ Λ mγ Λ
    (repBExtra M mγ Λ ∘ finRotate 3) hε p p' n μ i j ℓ
  rwa [repBKappa_comp_finRotate, repBExtra_comp_finRotate] at h

theorem jointEnergyFirstIntegral_two_const_mul (a : ℂ) (F : (Fin 2 → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => a * F ℓ) =
      a * QED.TwoLoop.jointEnergyFirstIntegral 2 F := by
  unfold QED.TwoLoop.jointEnergyFirstIntegral
  simp only [integral_const_mul]

/-- **Joint integrability from a parameter-free dominating function**: if `(x, t) ↦ G x t` is
continuous, `‖G x t‖ ≤ C g(t)` with `g` integrable and `w` is integrable on `S`, then
`w(x) G x t` is integrable on `S × ℝ²`. -/
theorem integrable_mul_of_norm_le {G : ℝ → (Fin 2 → ℝ) → ℂ}
    (hG : Continuous fun q : ℝ × (Fin 2 → ℝ) => G q.1 q.2) {S : Set ℝ} {w : ℝ → ℂ}
    (hw : IntegrableOn w S) {g : (Fin 2 → ℝ) → ℝ} (hg : Integrable g) {C : ℝ}
    (hb : ∀ x t, ‖G x t‖ ≤ C * g t) :
    Integrable (fun q : ℝ × (Fin 2 → ℝ) => w q.1 * G q.1 q.2)
      ((volume.restrict S).prod volume) := by
  refine ((hw.norm.mul_prod hg).const_mul C).mono'
    (hw.aestronglyMeasurable.comp_fst.mul hG.aestronglyMeasurable)
    (Eventually.of_forall fun q => ?_)
  rw [norm_mul]
  calc ‖w q.1‖ * ‖G q.1 q.2‖ ≤ ‖w q.1‖ * (C * g q.2) :=
        mul_le_mul_of_nonneg_left (hb q.1 q.2) (norm_nonneg _)
    _ = _ := by ring

/-- Joint continuity in the parameter and the energies at a fixed spatial `v`. -/
theorem continuous_energy_slice {G : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hG : Continuous fun q : ℝ × (Fin 2 → Fin 4 → ℝ) => G q.1 q.2) (v : Fin 2 → Fin 3 → ℝ) :
    Continuous fun q : ℝ × (Fin 2 → ℝ) =>
      G q.1 fun s => (Fin.cons (q.2 s) (v s) : Fin 4 → ℝ) :=
  hG.comp (continuous_fst.prodMk (continuous_pi fun s =>
    Continuous.finCons ((continuous_apply s).comp continuous_snd) continuous_const))

section RepB

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (s : Fin 8) (p p' : Fin 4 → ℝ)
include hc

/-- **Condition `h₁` for the transverse unit of `repB`**: for a weight `w` integrable on `(0, 1)`
and fixed `ε > 0`, at every spatial `v` the integrand `w(x) I_x` is integrable jointly in the
Feynman parameter `x ∈ (0, 1)` and the energies. -/
theorem integrable_unitM_repB_energy (μ i j : Fin 4) (M mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun q : ℝ × (Fin 2 → ℝ) => w q.1 * unitMIntegrand c P s (repBKappa q.1)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j
          fun s => (Fin.cons (q.2 s) (v s) : Fin 4 → ℝ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  have hg := ((jointEnergyFirstIntegrable_unitM_pow hc P s 2 (κ := ![1, 1]) le_rfl
    (fun j _ => by fin_cases j <;> rfl) (fun j => by fin_cases j <;> simp) P.m mγ Λ mγ Λ
    ![mγ, Λ] hε p p' μ i j).1 v).norm
  exact integrable_mul_of_norm_le (G := fun x t => unitMIntegrand c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j
        fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))
    (continuous_energy_slice (G := fun x ℓ => unitMIntegrand c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j ℓ)
      (continuous_unitMIntegrand_repB hc P s _ hε.ne' p p' 2 μ i j) v) hw hg
    (fun x t => norm_unitMIntegrand_repB_le c P s x M mγ Λ hε p p' 2 μ i j _)

variable {s} in
/-- **The Feynman parameter of `repB` through the joint energy-first integral**: for a weight `w`
integrable on `(0, 1)`, fixed `ε > 0` and `M > 0`, the integrand `∫₀¹ w(x) I_x dx` is integrable
in both stages of (T₉) and its joint energy-first integral is `∫₀¹ w(x) unitMValue(x) dx`. -/
theorem jointEnergyFirstIntegral_setIntegral_unitM_repB (hs : 4 ≤ (s : ℕ)) (μ i j : Fin 4)
    {M : ℝ} (hM : 0 < M) (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℂ}
    (hw : IntegrableOn w (Ioo 0 1)) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ => ∫ x in Ioo (0 : ℝ) 1,
        w x * unitMIntegrand c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j ℓ) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => ∫ x in Ioo (0 : ℝ) 1,
        w x * unitMIntegrand c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j ℓ) =
        ∫ x in Ioo (0 : ℝ) 1, w x * unitMValue c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j := by
  obtain ⟨h1, h2⟩ := QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_setIntegral
    (S := Ioo (0 : ℝ) 1) (fun x ℓ => w x * unitMIntegrand c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j ℓ)
    (integrable_unitM_repB_energy hc P s p p' μ i j M mγ Λ hε hw)
    (integrable_energyIntegral_unitM_repB hc P hs p p' μ i j hM mγ Λ hε hw)
  refine ⟨h1, h2.trans (integral_congr_ae (ae_of_all _ fun x => ?_))⟩
  exact jointEnergyFirstIntegral_two_const_mul _ _

end RepB

end QED.ChainProof.SetCUnitM

end
