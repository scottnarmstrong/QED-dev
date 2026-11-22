/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMAbs
public import QED.ChainProof.SetCUnitMDispEps

/-!
# The transverse unit of `repB`: the spatial `L¹` norm, uniformly in the Feynman parameter

Helper level for set (c) (stage L2, the `x`-Fubini of the `repB` classes, condition `h₂` of
`QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_setIntegral`). At a fixed `ε > 0` and fixed
masses, the spatial `L¹` norm `∫ d⁶v |∫ dt I_x|` of the transverse unit of `repB` at the Feynman
parameter `x` of the inserted bubble is bounded uniformly in `x ∈ (0, 1)`. The proof follows the
value bound `QED.ChainProof.SetCUnitM.norm_unitMValue_repB_disp_le` with the `L¹` norm in place of
the value: the rescaled-line bound `QED.ChainProof.SetCUnitM.integral_norm_energyIntegral_scale_le'`
(`κ⁻² C`) for a light dispersion mass, and the partial fraction against the element line
(`QED.ChainProof.SetCUnitM.unitMIntegrand_pf_scaled`, an identity of integrands) for a heavy one,
then the recursion in the powers of `k²`. No lower bound on the masses beyond `M > 0` is needed:
the constants depend on `ε` and on the masses.

* `absL1`: the spatial `L¹` norm of the energy integral; `absL1_mul_add_mul_le`, `absL1_sub_mul_le`;
* **`integrable_energyIntegral_of_absL1_le`**: condition `h₂` for `w(x) G x` from joint continuity
  and an `L¹` bound uniform in `x`;
* **`absL1_unitMScaled_le`**: the unit with one rescaled line, `κ⁻² C`;
* **`absL1_unitMValue_disp_le`**: the unit with a dispersion line, uniformly in `κ² ≤ 1/4`;
* **`absL1_unitM_repB_le`**: the transverse unit of `repB`, uniformly in `x ∈ (0, 1)`;
* **`integrable_energyIntegral_unitM_repB`**: condition `h₂` for `w(x) I_x`, `w` integrable on
  `(0, 1)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrixPV LoopQuartic
  RefinedBound)
open QED.TwoLoop.VPHalfAtAssembly (mem_Ioo_mul_pos)

/-! ### The spatial `L¹` norm of the energy integral -/

/-- The spatial `L¹` norm of the energy integral, `∫ d⁶v |∫ d²t F|`. -/
noncomputable def absL1 (F : (Fin 2 → Fin 4 → ℝ) → ℂ) : ℝ :=
  ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t : Fin 2 → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)‖

section L1

variable {F G : (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem absL1_nonneg (F : (Fin 2 → Fin 4 → ℝ) → ℂ) : 0 ≤ absL1 F :=
  integral_nonneg fun _ => norm_nonneg _

theorem absL1_mul_add_mul_le (hF : QED.TwoLoop.jointEnergyFirstIntegrable 2 F)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable 2 G) (a b : ℂ) :
    absL1 (fun ℓ => a * F ℓ + b * G ℓ) ≤ ‖a‖ * absL1 F + ‖b‖ * absL1 G := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  have hin : ∀ v : Fin 2 → Fin 3 → ℝ,
      ∫ t : Fin 2 → ℝ, (a * F (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) +
        b * G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) =
      a * (∫ t : Fin 2 → ℝ, F (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))) +
        b * ∫ t : Fin 2 → ℝ, G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) := fun v => by
    rw [integral_add ((hF1 v).const_mul a) ((hG1 v).const_mul b), integral_const_mul,
      integral_const_mul]
  unfold absL1
  simp only [hin]
  have hI : Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
      ‖a‖ * ‖∫ t : Fin 2 → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)‖ +
        ‖b‖ * ‖∫ t : Fin 2 → ℝ, G fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)‖) :=
    (hF2.norm.const_mul _).add (hG2.norm.const_mul _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hI
    (ae_of_all _ fun v => ?_)).trans_eq ?_
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  · rw [integral_add (hF2.norm.const_mul _) (hG2.norm.const_mul _), integral_const_mul,
      integral_const_mul]

theorem absL1_sub_mul_le (hF : QED.TwoLoop.jointEnergyFirstIntegrable 2 F)
    (hG : QED.TwoLoop.jointEnergyFirstIntegrable 2 G) (a : ℂ) :
    absL1 (fun ℓ => F ℓ - a * G ℓ) ≤ absL1 F + ‖a‖ * absL1 G := by
  have e : (fun ℓ => F ℓ - a * G ℓ) = fun ℓ => 1 * F ℓ + (-a) * G ℓ := funext fun ℓ => by ring
  rw [e]
  refine (absL1_mul_add_mul_le hF hG 1 (-a)).trans_eq ?_
  rw [norm_one, one_mul, norm_neg]

/-- **Condition `h₂` from an `L¹` bound uniform in the parameter.** If `(x, ℓ) ↦ G x ℓ` is
continuous, both stages of `G x` are integrable and `∫ d⁶v |∫ dt G x| ≤ C` for `x ∈ S`, and `w` is
integrable on `S`, then the energy integral of `w(x) G x` is integrable on `S × ℝ⁶`. -/
theorem integrable_energyIntegral_of_absL1_le {G : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hcont : Continuous fun q : ℝ × (Fin 2 → Fin 4 → ℝ) => G q.1 q.2) {S : Set ℝ}
    (hS : MeasurableSet S) {w : ℝ → ℂ} (hw : IntegrableOn w S) {C : ℝ}
    (hC : ∀ x ∈ S, QED.TwoLoop.jointEnergyFirstIntegrable 2 (G x) ∧ absL1 (G x) ≤ C) :
    Integrable (fun q : ℝ × (Fin 2 → Fin 3 → ℝ) => ∫ t : Fin 2 → ℝ,
        w q.1 * G q.1 fun s => (Fin.cons (t s) (q.2 s) : Fin 4 → ℝ))
      ((volume.restrict S).prod volume) := by
  have hG : Continuous fun q : (ℝ × (Fin 2 → Fin 3 → ℝ)) × (Fin 2 → ℝ) =>
      G q.1.1 (fun s => (Fin.cons (q.2 s) (q.1.2 s) : Fin 4 → ℝ)) :=
    hcont.comp (continuous_fst.fst.prodMk (continuous_pi fun s =>
      Continuous.finCons ((continuous_apply s).comp continuous_snd)
        ((continuous_apply s).comp continuous_fst.snd)))
  have hJ : StronglyMeasurable fun q : ℝ × (Fin 2 → Fin 3 → ℝ) => ∫ t : Fin 2 → ℝ,
      G q.1 (fun s => (Fin.cons (t s) (q.2 s) : Fin 4 → ℝ)) :=
    hG.stronglyMeasurable.integral_prod_right'
  have e : (fun q : ℝ × (Fin 2 → Fin 3 → ℝ) => ∫ t : Fin 2 → ℝ,
      w q.1 * G q.1 (fun s => (Fin.cons (t s) (q.2 s) : Fin 4 → ℝ))) = fun q =>
      w q.1 * ∫ t : Fin 2 → ℝ, G q.1 (fun s => (Fin.cons (t s) (q.2 s) : Fin 4 → ℝ)) :=
    funext fun q => integral_const_mul _ _
  rw [e]
  have hmeas : AEStronglyMeasurable (fun q : ℝ × (Fin 2 → Fin 3 → ℝ) =>
      w q.1 * ∫ t : Fin 2 → ℝ, G q.1 (fun s => (Fin.cons (t s) (q.2 s) : Fin 4 → ℝ)))
      ((volume.restrict S).prod volume) :=
    hw.aestronglyMeasurable.comp_fst.mul hJ.aestronglyMeasurable
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · exact ae_restrict_of_forall_mem hS fun x hx => ((hC x hx).1.2).const_mul (w x)
  · refine (hw.norm.mul_const C).mono' hmeas.norm.integral_prod_right' ?_
    refine ae_restrict_of_forall_mem hS fun x hx => ?_
    have hn : ∫ v : Fin 2 → Fin 3 → ℝ, ‖w x * ∫ t : Fin 2 → ℝ,
        G x (fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))‖ = ‖w x‖ * absL1 (G x) := by
      simp only [norm_mul]
      rw [integral_const_mul, absL1]
    have h0 := absL1_nonneg (G x)
    rw [hn, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) h0)]
    exact mul_le_mul_of_nonneg_left (hC x hx).2 (norm_nonneg _)

end L1

variable {r : ℕ}

/-! ### One rescaled line of the unit -/

section Scaled

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (s : Fin 8) (p p' : Fin 4 → ℝ)
include hc

/-- **The unit with one rescaled line, in the spatial `L¹` norm**: at fixed `ε > 0` and for a
bound `K` on the squared masses of the rescaled graph, one constant `C` with
`∫ d⁶v |∫ dt (unitMScaled)| ≤ κ⁻² C` for every `κ ∈ (0, 1]`, both stages integrable. -/
theorem absL1_unitMScaled_le {i₀ : Fin (r + 8)} (hi₀ : i₀ ∉ unitME r) (μ i j : Fin 4) (K : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : ℝ) (M : Fin (r + 8) → ℝ), 0 < κ → κ ≤ 1 →
      ∑ k, ((Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k * M k) ^ 2 +
        ∑ μ, unitMMomenta c s (fun _ => 1) p p' k μ ^ 2) ≤ K →
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMScaled c P s i₀ κ M ε p p' μ i j) ∧
        absL1 (unitMScaled c P s i₀ κ M ε p p' μ i j) ≤ (κ ^ 2)⁻¹ * C := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  have hB : RefinedBound (unitMMatrix c s (fun _ : Fin r => (1 : ℝ))) (unitME r) 4 Q.eval := by
    rw [hQ]; exact refinedBound_unitM hc P s _ p p' μ i j
  have hcrit := noSubdivergenceRefined_unitM hc s (κ := fun _ : Fin r => (1 : ℝ))
    (fun _ => one_ne_zero)
  have hE : (unitME r).card + 4 ≤ r + 7 + 1 := by
    simp [unitME]
  obtain ⟨C, hC0, hC⟩ := integral_norm_energyIntegral_scale_le' (m := r + 7) Q
    (unitMMatrix c s (fun _ : Fin r => (1 : ℝ))) (unitMMomenta c s (fun _ => 1) p p')
    (by omega) hcrit hB hE hi₀ (K := K) le_rfl hε
  refine ⟨C, hC0, fun κ M hκ0 hκ1 hK => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hC κ (Function.update (1 : Fin (r + 8) → ℝ) i₀ κ)
    (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k * M k)
    hκ0 hκ1 (Function.update_self _ _ _) (fun k hk => Function.update_of_ne hk _ _) hK
  have e : unitMScaled c P s i₀ κ M ε p p' μ i j = fun ℓ =>
      Q.eval ℓ * ∏ k, (lineDenom
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k • unitMMatrix c s (fun _ => 1) k)
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k •
          unitMMomenta c s (fun _ => 1) p p' k)
        (fun k => Function.update (1 : Fin (r + 8) → ℝ) i₀ κ k * M k) ε k ℓ)⁻¹ := by
    funext ℓ; rw [unitMScaled, hQ]
  rw [e]
  exact ⟨⟨h1, h2⟩, h3⟩

end Scaled

/-! ### The dispersion line: the `L¹` norm uniformly in its scale -/

section Disp

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
  (p p' : Fin 4 → ℝ)

/-- The masses of the element line rescaled by `κ` with entry `t / κ` are those with entry
`t`. -/
theorem update_mul_unitMMasses_slot (hs : 4 ≤ (s : ℕ)) {κ : ℝ} (hκ : κ ≠ 0) (m a A b B t : ℝ)
    (cs : Fin r → ℝ) :
    (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k *
        unitMMasses m (slotMa s (t / κ) a) (slotMA s (t / κ) A) (slotMb s (t / κ) b)
          (slotMB s (t / κ) B) cs k) =
      unitMMasses m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs := by
  funext k
  by_cases hk : k = mEmb r s
  · subst hk
    rw [Function.update_self, unitMMasses_mEmb, unitMMasses_mEmb, unitMasses_slot hs,
      unitMasses_slot hs, ite_eq_left rfl, ite_eq_left rfl]
    field_simp
  · rw [Function.update_of_ne hk, Pi.one_apply, one_mul, unitMMasses_slot hs _ _ _ _ _ _ _ k hk,
      unitMMasses_slot hs _ _ _ _ _ _ _ k hk]

/-- The masses of the extra line `e` rescaled by `κ` with entry `cs e / κ` are the original
ones. -/
theorem update_mul_unitMMasses_extra (e : Fin r) {κ : ℝ} (hκ : κ ≠ 0) (m a A b B : ℝ)
    (cs : Fin r → ℝ) :
    (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mExtra r e) κ k *
        unitMMasses m a A b B (Function.update cs e (cs e / κ)) k) = unitMMasses m a A b B cs := by
  funext k
  rcases mem_mEmb_or_mExtra k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [unitMMasses, mExt_mEmb, Function.update_of_ne (mEmb_ne_mExtra j e)]
  · simp only [unitMMasses, mExt_mExtra, Function.update_apply, mExtra_injective.eq_iff]
    split_ifs with h
    · subst h; field_simp
    · simp

include hc hs

/-- **The unit with a dispersion line in the spatial `L¹` norm, uniformly in its scale.** The
first extra line has scale `κ` with `κ² ≤ 1/4` and mass `M > 0`, the others are unscaled; at fixed
`ε > 0` and fixed masses one constant `C` bounds `∫ d⁶v |∫ dt I|` for all such `κ`. Light
dispersion mass: the rescaled-line bound `κ⁻² C`, with `κ⁻² ≤ 2 μ_s² / M²`; heavy: partial
fractions against the element line (`unitMIntegrand_pf_scaled`). -/
theorem absL1_unitMValue_disp_le (μ i j : Fin 4) (mγ Λ : ℝ) {M : ℝ} (hM : 0 < M)
    (cs : Fin r → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ κ : ℝ, 0 < κ → κ ^ 2 ≤ 1 / 4 →
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s (Fin.cons κ fun _ => 1)
          (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M cs)) ε p p' 0 μ i j) ∧
        absL1 (unitMIntegrand c P s (Fin.cons κ fun _ => 1)
          (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M cs)) ε p p' 0 μ i j) ≤ C := by
  set u := unitMasses P.m mγ Λ mγ Λ s with hu
  set Mm₁ : Fin (r + 1 + 8) → ℝ := unitMMasses P.m mγ Λ mγ Λ (Fin.cons M cs)
  set Mm₂ : Fin (r + 8) → ℝ := unitMMasses P.m (slotMa s M mγ) (slotMA s M Λ) (slotMb s M mγ)
    (slotMB s M Λ) cs
  set Mm₀ : Fin (r + 8) → ℝ := unitMMasses P.m mγ Λ mγ Λ cs
  obtain ⟨C₁, hC₁0, hC₁⟩ := absL1_unitMScaled_le (r := r + 1) hc P s p p'
    (mExtra_not_mem_unitME 0) μ i j
    (∑ k, (Mm₁ k ^ 2 + ∑ μ, unitMMomenta c s (fun _ => 1) p p' k μ ^ 2)) hε
  obtain ⟨C₂, hC₂0, hC₂⟩ := absL1_unitMScaled_le (r := r) hc P s p p'
    (mEmb_not_mem_unitME hs) μ i j
    (∑ k, (Mm₂ k ^ 2 + ∑ μ, unitMMomenta c s (fun _ => 1) p p' k μ ^ 2)) hε
  obtain ⟨C₀, hC₀0, hC₀⟩ := absL1_unitMScaled_le (r := r) hc P s p p'
    (mEmb_not_mem_unitME hs) μ i j
    (∑ k, (Mm₀ k ^ 2 + ∑ μ, unitMMomenta c s (fun _ => 1) p p' k μ ^ 2)) hε
  have hM2 : 0 < M ^ 2 := by positivity
  refine ⟨2 * u ^ 2 / M ^ 2 * C₁ + 2 / M ^ 2 * (C₂ + C₀), fun κ hκ hκ4 => ?_⟩
  have hκ1 : κ ≤ 1 := by nlinarith
  have hpos : 0 ≤ 2 * u ^ 2 / M ^ 2 * C₁ := by positivity
  have hpos' : 0 ≤ 2 / M ^ 2 * (C₂ + C₀) := by positivity
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
    have hMm : (fun k => Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k * Mm k) = Mm₂ :=
      update_mul_unitMMasses_slot hs hκ.ne' P.m mγ Λ mγ Λ M cs
    have hMm' : ∀ k, Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) κ k * Mm k = Mm₂ k :=
      fun k => congrFun hMm k
    obtain ⟨hJ, hJb⟩ := hC₂ κ Mm hκ hκ1 (by simp only [hMm']; exact le_rfl)
    have h1 : Function.update (1 : Fin (r + 8) → ℝ) (mEmb r s) 1 = 1 := by
      funext k; by_cases hk : k = mEmb r s <;> simp [hk]
    obtain ⟨hB, hBb⟩ := hC₀ 1 Mm₀ one_pos le_rfl (by simp [h1])
    rw [← unitMIntegrand_one_eq_scaled] at hB hBb
    have hval : unitMIntegrand c P s (Fin.cons κ fun _ => 1) Mm₁ ε p p' 0 μ i j = fun ℓ =>
        (k⁻¹ * ((κ ^ 2 : ℝ) : ℂ)) * unitMScaled c P s (mEmb r s) κ Mm ε p p' μ i j ℓ +
          (-k⁻¹) * unitMIntegrand c P s (fun _ => 1) Mm₀ ε p p' 0 μ i j ℓ := by
      rw [← hperm, hpf]
      funext ℓ; ring
    rw [hval]
    refine ⟨(jointEnergyFirstIntegrable_mul_add_mul hJ hB _ _).1,
      (absL1_mul_add_mul_le hJ hB _ _).trans ?_⟩
    have hkn : M ^ 2 / 2 ≤ ‖k‖ := by
      refine le_trans ?_ (abs_re_le_norm_pfConst κ u M ε)
      rw [abs_of_neg (by nlinarith)]
      linarith
    have hk0 : 0 < ‖k‖ := lt_of_lt_of_le (by positivity) hkn
    have hki : ‖k⁻¹‖ ≤ 2 / M ^ 2 := by
      rw [norm_inv, inv_le_comm₀ hk0 (by positivity)]
      simpa [inv_div] using hkn
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_neg]
    have hκ2 : κ ^ 2 * (κ ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hA1 := absL1_nonneg (unitMScaled c P s (mEmb r s) κ Mm ε p p' μ i j)
    have hA2 := absL1_nonneg (unitMIntegrand c P s (fun _ => 1) Mm₀ ε p p' 0 μ i j)
    calc ‖k⁻¹‖ * κ ^ 2 * absL1 (unitMScaled c P s (mEmb r s) κ Mm ε p p' μ i j) +
          ‖k⁻¹‖ * absL1 (unitMIntegrand c P s (fun _ => 1) Mm₀ ε p p' 0 μ i j)
        ≤ 2 / M ^ 2 * κ ^ 2 * ((κ ^ 2)⁻¹ * C₂) + 2 / M ^ 2 * ((1 ^ 2)⁻¹ * C₀) := by
          gcongr
      _ = 2 / M ^ 2 * (C₂ + C₀) := by
          rw [one_pow, inv_one, one_mul, mul_assoc (2 / M ^ 2), ← mul_assoc (κ ^ 2), hκ2,
            one_mul]
          ring
      _ ≤ _ := by linarith
  · -- light dispersion mass: the rescaled-line bound and `κ⁻² ≤ 2 u² / M²`
    push Not at hcase
    rw [cons_one_eq_update, unitMIntegrand_eq_scaled c P s 0 hκ.ne']
    have hMs := update_mul_unitMMasses_extra (r := r + 1) 0 hκ.ne' P.m mγ Λ mγ Λ
      (Fin.cons M cs)
    have hMs' : ∀ k, Function.update (1 : Fin (r + 1 + 8) → ℝ) (mExtra (r + 1) 0) κ k *
        unitMMasses P.m mγ Λ mγ Λ (Function.update (Fin.cons M cs : Fin (r + 1) → ℝ) 0
          ((Fin.cons M cs : Fin (r + 1) → ℝ) 0 / κ)) k = Mm₁ k := fun k => congrFun hMs k
    obtain ⟨hI, hIb⟩ := hC₁ κ (unitMMasses P.m mγ Λ mγ Λ (Function.update
      (Fin.cons M cs : Fin (r + 1) → ℝ) 0 ((Fin.cons M cs : Fin (r + 1) → ℝ) 0 / κ))) hκ hκ1
      (by simp only [hMs']; exact le_rfl)
    refine ⟨hI, hIb.trans ?_⟩
    have hκinv : (κ ^ 2)⁻¹ ≤ 2 * u ^ 2 / M ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ hM2]
      nlinarith
    calc (κ ^ 2)⁻¹ * C₁ ≤ 2 * u ^ 2 / M ^ 2 * C₁ := mul_le_mul_of_nonneg_right hκinv hC₁0
      _ ≤ _ := by linarith

end Disp

/-! ### The transverse unit of `repB` and the Fubini condition in the Feynman parameter -/

section RepB

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
  (p p' : Fin 4 → ℝ)
include hc hs

/-- **The transverse unit of `repB` in the spatial `L¹` norm, uniformly in `x`**: at fixed
`ε > 0` and fixed masses (`M > 0`), one constant `C` with `∫ d⁶v |∫ dt I_x| ≤ C` for all
`x ∈ (0, 1)`, both stages integrable. -/
theorem absL1_unitM_repB_le (μ i j : Fin 4) {M : ℝ} (hM : 0 < M) (mγ Λ : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1,
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j) ∧
        absL1 (unitMIntegrand c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j) ≤ C := by
  obtain ⟨C₀, hC₀⟩ := absL1_unitMValue_disp_le (r := 0) hc P hs p p' μ i j mγ Λ hM ![] hε
  obtain ⟨C₁, hC₁⟩ := absL1_unitMValue_disp_le (r := 1) hc P hs p p' μ i j mγ Λ hM ![mγ] hε
  obtain ⟨C₂, hC₂⟩ := absL1_unitMValue_disp_le (r := 2) hc P hs p p' μ i j mγ Λ hM ![mγ, Λ] hε
  set A := mγ ^ 2 + ε
  set B := Λ ^ 2 + ε
  refine ⟨C₀ + A * C₁ + B * (C₁ + B * C₂), fun x hx => ?_⟩
  have hw := mem_Ioo_mul_pos hx
  set κ := √(x * (1 - x)) with hκdef
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hw
  have hκ2 : κ ^ 2 ≤ 1 / 4 := by
    rw [hκdef, Real.sq_sqrt hw.le]; nlinarith [sq_nonneg (x - 1 / 2)]
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
  -- the recursion, at the level of integrands
  have e₂ := unitMIntegrand_succ c P s (κ := K₃) rfl P.m mγ Λ mγ Λ (Fin.cons M ![mγ, Λ])
    hε.ne' p p' 1 μ i j
  rw [hi₃, hj₃] at e₂
  have e₁a := unitMIntegrand_succ c P s (κ := K₂) rfl P.m mγ Λ mγ Λ (Fin.cons M ![mγ])
    hε.ne' p p' 0 μ i j
  rw [hi₂, hj₂] at e₁a
  have e₁b := unitMIntegrand_succ c P s (κ := K₃) rfl P.m mγ Λ mγ Λ (Fin.cons M ![mγ, Λ])
    hε.ne' p p' 0 μ i j
  rw [hi₃, hj₃] at e₁b
  obtain ⟨j₀, b₀⟩ := hC₀ κ hκ0 hκ2
  obtain ⟨j₁, b₁⟩ := hC₁ κ hκ0 hκ2
  obtain ⟨j₂, b₂⟩ := hC₂ κ hκ0 hκ2
  set a' := ((((Fin.cons M ![mγ] : Fin 2 → ℝ) (Fin.last 1)) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I
  set b' := ((((Fin.cons M ![mγ, Λ] : Fin 3 → ℝ) (Fin.last 2)) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I
  have ha : ‖a'‖ ≤ A := (norm_sq_sub_mul_I_le hε.le).trans (by simp [A])
  have hb : ‖b'‖ ≤ B := (norm_sq_sub_mul_I_le hε.le).trans (by simp [B])
  -- the pieces with one power of `k²`
  have j₁a : QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s K₂
      (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M ![mγ])) ε p p' 1 μ i j) := by
    rw [e₁a]; exact (jointEnergyFirstIntegrable_sub_mul j₀ j₁ a').1
  have b₁a : absL1 (unitMIntegrand c P s K₂
      (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M ![mγ])) ε p p' 1 μ i j) ≤ C₀ + A * C₁ := by
    rw [e₁a]
    refine (absL1_sub_mul_le j₀ j₁ a').trans (add_le_add b₀ ?_)
    exact mul_le_mul ha b₁ (absL1_nonneg _) ((norm_nonneg _).trans ha)
  have j₁b : QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s K₃
      (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M ![mγ, Λ])) ε p p' 1 μ i j) := by
    rw [e₁b]; exact (jointEnergyFirstIntegrable_sub_mul j₁ j₂ b').1
  have b₁b : absL1 (unitMIntegrand c P s K₃
      (unitMMasses P.m mγ Λ mγ Λ (Fin.cons M ![mγ, Λ])) ε p p' 1 μ i j) ≤ C₁ + B * C₂ := by
    rw [e₁b]
    refine (absL1_sub_mul_le j₁ j₂ b').trans (add_le_add b₁ ?_)
    exact mul_le_mul hb b₂ (absL1_nonneg _) ((norm_nonneg _).trans hb)
  rw [hK₃, hE₃, e₂]
  refine ⟨(jointEnergyFirstIntegrable_sub_mul j₁a j₁b b').1,
    (absL1_sub_mul_le j₁a j₁b b').trans (add_le_add b₁a ?_)⟩
  exact mul_le_mul hb b₁b (absL1_nonneg _) ((norm_nonneg _).trans hb)

/-- **Condition `h₂` for the transverse unit of `repB`**: for a weight `w` integrable on `(0, 1)`
and fixed `ε > 0`, the energy integral of `w(x) I_x` is integrable jointly in the Feynman
parameter `x ∈ (0, 1)` and the spatial momenta. -/
theorem integrable_energyIntegral_unitM_repB (μ i j : Fin 4) {M : ℝ} (hM : 0 < M) (mγ Λ : ℝ)
    {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) :
    Integrable (fun q : ℝ × (Fin 2 → Fin 3 → ℝ) => ∫ t : Fin 2 → ℝ,
        w q.1 * unitMIntegrand c P s (repBKappa q.1)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j
          fun s => (Fin.cons (t s) (q.2 s) : Fin 4 → ℝ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  obtain ⟨C, hC⟩ := absL1_unitM_repB_le hc P hs p p' μ i j hM mγ Λ hε
  exact integrable_energyIntegral_of_absL1_le
    (continuous_unitMIntegrand_repB hc P s _ hε.ne' p p' 2 μ i j) measurableSet_Ioo hw hC

end RepB

end QED.ChainProof.SetCUnitM

end
