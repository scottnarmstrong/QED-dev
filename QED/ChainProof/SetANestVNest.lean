/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestVOuter
public import QED.ChainProof.SetANestVL1

/-!
# The nested form of a class from the integrated bound on its inner integrands

Helper level for the set (a) headline (HA₆), obligation (N), step NL for `VA`, `VB`, `VC`.
`QED.ChainProof.SetANestV.loopNested_of_nestG` takes the analytic core in the pointwise form
`InnerBound`. The bound proved for the two-loop vacuum-polarization integrands
(`QED.ChainProof.SetANestV.el1_VA`, …) is integrated over the inner spatial momenta:

`InnerBoundL1 Y`: `∫ d⁶v |∫ dt Y(k; t, v)| ≤ C (1 + Σ_μ k_μ²)⁴`, with `v ↦ ∫ dt Y` integrable.

By Tonelli this is enough for the Fubini condition against an outer factor decaying like
`(1 + |t₃|)⁻¹⁰` (`integrable_outer_mul_innerL1`: the effective decay is `(1 + |t₃|)⁻²`), and
`loopNested_of_nestGL1` is `loopNested_of_nestG` with `InnerBoundL1` in place of `InnerBound`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANestV

open QED.TwoLoop.NestedVPFubiniBound (DecaysLike one_add_abs_pos)
open QED.Integration.TwoLoop (loopMomenta)

/-- **The integrated bound on the inner energy integrals** of a two-loop integrand `Y(k, q)`:
the energy integral `∫ dt₁ dt₂ Y(k, ·)` is measurable in `(t₃, v)` along `k = (t₃, w)`,
integrable in `v` at every `k`, and its `L¹` norm in `v` is at most `C (1 + Σ k²)⁴`. -/
structure InnerBoundL1 (Y : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) : Prop where
  meas : ∀ w : Fin 3 → ℝ, AEStronglyMeasurable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) =>
    ∫ t : Fin 2 → ℝ, Y (Fin.cons x.1 w) fun s => (Fin.cons (t s) (x.2 s) : Fin 4 → ℝ)
  bound : ∃ C : ℝ, ∀ k,
    Integrable (fun v : Fin 2 → Fin 3 → ℝ =>
      ∫ t : Fin 2 → ℝ, Y k fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) ∧
    ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t : Fin 2 → ℝ, Y k fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)‖ ≤
      C * (1 + kSq k) ^ 4

theorem kSq_cons (t : ℝ) (w : Fin 3 → ℝ) : kSq (Fin.cons t w) = t ^ 2 + ∑ i, w i ^ 2 := by
  simp [kSq, Fin.sum_univ_succ]

theorem one_add_kSq_cons_le (t : ℝ) (w : Fin 3 → ℝ) :
    (1 + kSq (Fin.cons t w)) ^ 4 ≤ (1 + |t|) ^ 8 * (1 + ∑ i, w i ^ 2) ^ 4 := by
  have hW : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ht := abs_nonneg t
  have h : 1 + kSq (Fin.cons t w) ≤ (1 + |t|) ^ 2 * (1 + ∑ i, w i ^ 2) := by
    rw [kSq_cons, ← sq_abs t]
    nlinarith [mul_nonneg (sq_nonneg |t|) hW, mul_nonneg ht hW]
  calc (1 + kSq (Fin.cons t w)) ^ 4 ≤ ((1 + |t|) ^ 2 * (1 + ∑ i, w i ^ 2)) ^ 4 :=
        pow_le_pow_left₀ (by linarith [kSq_nonneg (Fin.cons t w)]) h 4
    _ = _ := by ring

/-- **One term of the Fubini condition, integrated form**: a continuous factor decaying like
`(1 + |t|)⁻¹⁰` times an inner energy integral with `InnerBoundL1` is integrable in `(t₃, v)`. -/
theorem integrable_outer_mul_innerL1 {g : ℝ → ℂ} (hc : Continuous g) (hd : DecaysLike g 10)
    {Y : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} (hY : InnerBoundL1 Y) (w : Fin 3 → ℝ) :
    Integrable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) => g x.1 *
      ∫ t : Fin 2 → ℝ, Y (Fin.cons x.1 w) fun s => (Fin.cons (t s) (x.2 s) : Fin 4 → ℝ) := by
  obtain ⟨Co, hCo⟩ := hd
  obtain ⟨Ci, hCi⟩ := hY.bound
  have hm : AEStronglyMeasurable (fun x : ℝ × (Fin 2 → Fin 3 → ℝ) => g x.1 *
      ∫ t : Fin 2 → ℝ, Y (Fin.cons x.1 w) fun s => (Fin.cons (t s) (x.2 s) : Fin 4 → ℝ))
      (volume.prod volume) :=
    (hc.comp continuous_fst).aestronglyMeasurable.mul (hY.meas w)
  rw [Measure.volume_eq_prod, integrable_prod_iff hm]
  refine ⟨Filter.Eventually.of_forall fun t => ((hCi (Fin.cons t w)).1.const_mul (g t)), ?_⟩
  set K := Co * |Ci| * (1 + ∑ i, w i ^ 2) ^ 4
  have hint : Integrable fun t : ℝ => K * (1 + ‖t‖) ^ (-(2 : ℝ)) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul K
  refine hint.mono' hm.norm.integral_prod_right' (Filter.Eventually.of_forall fun t => ?_)
  have hW : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ht0 : 0 < 1 + |t| := one_add_abs_pos t
  have hn : 0 ≤ ∫ v : Fin 2 → Fin 3 → ℝ, ‖g t * ∫ t' : Fin 2 → ℝ,
      Y (Fin.cons t w) fun s => (Fin.cons (t' s) (v s) : Fin 4 → ℝ)‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_of_nonneg hn]
  simp only [norm_mul]
  rw [integral_const_mul]
  have h1 := hCo t
  have h2 := (hCi (Fin.cons t w)).2
  have h3 := one_add_kSq_cons_le t w
  have hz : (1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ 8 = (1 + |t|) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_add ht0]
    norm_num
  have hI : 0 ≤ ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t' : Fin 2 → ℝ,
      Y (Fin.cons t w) fun s => (Fin.cons (t' s) (v s) : Fin 4 → ℝ)‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hCo0 : 0 ≤ Co := QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const_nonneg hCo
  have hK4 : 0 ≤ (1 + kSq (Fin.cons t w)) ^ 4 := by
    have := kSq_nonneg (Fin.cons t w); positivity
  rw [Real.norm_eq_abs t]
  calc ‖g t‖ * ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t' : Fin 2 → ℝ,
        Y (Fin.cons t w) fun s => (Fin.cons (t' s) (v s) : Fin 4 → ℝ)‖
      ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) * (|Ci| * (1 + kSq (Fin.cons t w)) ^ 4) :=
        mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_right (le_abs_self Ci) hK4)) hI
          (by positivity)
    _ ≤ (Co * (1 + |t|) ^ (-(10 : ℤ))) *
        (|Ci| * ((1 + |t|) ^ 8 * (1 + ∑ i, w i ^ 2) ^ 4)) := by gcongr
    _ = K * ((1 + |t|) ^ (-(10 : ℤ)) * (1 + |t|) ^ 8) := by ring
    _ = K * (1 + |t|) ^ (-(2 : ℝ)) := by rw [hz]

/-- **The Fubini condition for `nestG`**, integrated form of `integrable_innerT_nestG`. -/
theorem integrable_innerT_nestGL1 (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (Y : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hc : ∀ w a b, Continuous fun t => O (Fin.cons t w) a b)
    (hd : ∀ w a b, DecaysLike (fun t => O (Fin.cons t w) a b) 10)
    (hY : ∀ a b k, QED.TwoLoop.jointEnergyFirstIntegrable 2 (Y a b k))
    (hB : ∀ a b, InnerBoundL1 (Y a b)) (w : Fin 3 → ℝ) :
    Integrable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) => innerT (nestG O Y) x.1 w x.2 := by
  simp only [innerT_nestG O Y hY]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    integrable_outer_mul_innerL1 (hc w a b) (hd w a b) (hB a b) w

open QED.ChainProof.SetANest QED.WickModel in
/-- **The nested form of a class with a two-loop inner insertion**, with the analytic core in
the integrated form `InnerBoundL1` (`loopNested_of_nestG` takes the pointwise `InnerBound`). -/
theorem loopNested_of_nestGL1 (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (hε : 0 < P.ε) (p' p : Fin 4 → ℝ)
    (Y : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hval : ∀ μ i j, Graded.contractionValue P Φ D C 0 (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 3
        (nestG (nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) Y))
    (hF : ∀ μ i j, QED.TwoLoop.jointEnergyFirstIntegrable 3
        (nestG (nestOuter P.e (Φ.mass Φ.openLine) P.mγ P.Λ P.ε p' p μ i j) Y))
    (hY : ∀ a b k, QED.TwoLoop.jointEnergyFirstIntegrable 2 (Y a b k))
    (hB : ∀ a b, InnerBoundL1 (Y a b)) :
    LoopNested P Φ D C (fun k a b => QED.TwoLoop.jointEnergyFirstIntegral 2 (Y a b k)) p' p :=
  loopNested_of_joint P Φ D C _ p' p _ hval hF
    (fun μ i j => integrable_innerT_nestGL1 _ Y
      (continuous_nestOuter hε _ _ _ _ p' p μ i j) (decaysLike_nestOuter hε _ _ _ _ p' p μ i j)
      hY hB)
    (fun μ i j k => by
      rw [innerJ_nestG _ Y hY, nestInt_eq_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _)

/-! ### From `EL1` -/

/-- **`EL1` gives `InnerBoundL1`** for every multiple `c · F_ε(·)_{i j}` at `ε > 0`, given the
measurability along `k = (t₃, w)`. -/
theorem innerBoundL1_of_el1 {F : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : EL1 F) {ε : ℝ} (hε : 0 < ε) (c : ℂ) (i j : Fin 4)
    (hm : ∀ w : Fin 3 → ℝ, AEStronglyMeasurable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) =>
      ∫ t : Fin 2 → ℝ, F ε (Fin.cons x.1 w) (fun s => (Fin.cons (t s) (x.2 s) : Fin 4 → ℝ)) i j) :
    InnerBoundL1 fun k ℓ => c * F ε k ℓ i j := by
  obtain ⟨C, hC⟩ := hF ε hε i j
  refine ⟨fun w => ?_, ‖c‖ * C, fun k => ?_⟩
  · simp only [integral_const_mul]
    exact (hm w).const_mul c
  · obtain ⟨-, h2, h3⟩ := hC k
    refine ⟨?_, ?_⟩
    · simp only [integral_const_mul]
      exact h2.const_mul c
    · simp only [integral_const_mul, norm_mul]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)


/-! ### Measurability of the inner energy integral of a class -/

section Meas

open QED.TwoLoop.Bridge (electronNumerator electronNumerator_apply propDenom propDenom_ne_zero)
open QED.Integration.TwoLoop (lineMomentum castLoopMatrix)

variable {X : Type*} [TopologicalSpace X]

theorem continuous_electronNumerator_comp {f : X → Fin 4 → ℝ} (hf : Continuous f) (M : ℝ) :
    Continuous fun x => electronNumerator M (f x) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [electronNumerator_apply]
  have := fun ν => (continuous_apply ν).comp hf
  fun_prop

theorem continuous_propDenom_inv_comp {f : X → Fin 4 → ℝ} (hf : Continuous f) (M : ℝ) {ε : ℝ}
    (hε : 0 < ε) : Continuous fun x => (propDenom M ε (f x))⁻¹ := by
  refine Continuous.inv₀ ?_ fun x => propDenom_ne_zero hε.ne' _
  simp only [propDenom, Minkowski.dot]
  have := fun ν => (continuous_apply ν).comp hf
  fun_prop

theorem continuous_lineMomentum_comp (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (r : Fin 5)
    {k : X → Fin 4 → ℝ} {ℓ : X → Fin 2 → Fin 4 → ℝ} (hk : Continuous k) (hℓ : Continuous ℓ) :
    Continuous fun x => lineMomentum (castLoopMatrix base) (fun r => c r • k x) r (ℓ x) := by
  refine continuous_pi fun ν => ?_
  simp only [lineMomentum, Pi.smul_apply, smul_eq_mul]
  have h1 := fun s => (continuous_apply ν).comp ((continuous_apply s).comp hℓ)
  have h2 := (continuous_apply ν).comp hk
  fun_prop

open QED.GradedProof.VP2 in
/-- **The block-summed integrand of a class is continuous** in the photon and loop momenta at
`ε > 0`. -/
theorem continuous_vSumF {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (a b : Fin 4)
    {k : X → Fin 4 → ℝ} {ℓ : X → Fin 2 → Fin 4 → ℝ} (hk : Continuous k) (hℓ : Continuous ℓ) :
    Continuous fun x => vSumF Φ e A base c mγ Λ ε (k x) (ℓ x) a b := by
  have hL := fun r => continuous_lineMomentum_comp base c r hk hℓ
  have hN := fun r M => continuous_electronNumerator_comp (hL r) M
  have hD := fun r M => continuous_propDenom_inv_comp (hL r) M hε
  simp only [vSumF, gH, vD, vNum, vT, fm, phm]
  refine continuous_finsetSum _ fun f _ => continuous_const.mul ?_
  refine ((hD _ _).mul (hD _ _)).mul ((continuous_finsetSum _ fun ρ _ =>
    continuous_finsetSum _ fun σ _ => continuous_const.mul ?_).mul
      (continuous_finsetProd _ fun l _ => hD _ _))
  exact (((((((continuous_const.matrix_mul (hN _ _)).matrix_mul continuous_const).matrix_mul
    (hN _ _)).matrix_mul continuous_const).matrix_mul (hN _ _)).matrix_mul
      continuous_const).matrix_mul (hN _ _)).matrix_trace

open QED.GradedProof.VP2 in
/-- The measurability field of `InnerBoundL1` for a class. -/
theorem aestronglyMeasurable_vSumF {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e : ℝ)
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (a b : Fin 4)
    (w : Fin 3 → ℝ) :
    AEStronglyMeasurable fun x : ℝ × (Fin 2 → Fin 3 → ℝ) => ∫ t : Fin 2 → ℝ,
      vSumF Φ e A base c mγ Λ ε (Fin.cons x.1 w) (fun s => (Fin.cons (t s) (x.2 s) : Fin 4 → ℝ))
        a b := by
  have hc : Continuous fun y : (ℝ × (Fin 2 → Fin 3 → ℝ)) × (Fin 2 → ℝ) =>
      vSumF Φ e A base c mγ Λ ε (Fin.cons y.1.1 w) (loopMomenta y.2 y.1.2) a b :=
    continuous_vSumF Φ e A base c mγ Λ hε a b
      (Continuous.finCons (A := fun _ => ℝ) (continuous_fst.comp continuous_fst)
        (continuous_const (y := w)))
      (QED.Integration.TwoLoop.continuous_loopMomenta.comp
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

end Meas

/-! ### The classes -/

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (e mγ Λ : ℝ)
  (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

open QED.GradedProof.VP2 in
/-- **The inner integrands of a class satisfy `InnerBoundL1`**, from `EL1` of its block-summed
integrand: `Y_{a b}(k, q) = c · F_ε(k, q)_{a b}`, `F = vSumF`. -/
theorem innerBoundL1_vSumF (hF : EL1 (vSumF Φ e A base c mγ Λ)) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) (a b : Fin 4) :
    InnerBoundL1 fun k ℓ => z * vSumF Φ e A base c mγ Λ ε k ℓ a b :=
  innerBoundL1_of_el1 hF hε z a b (aestronglyMeasurable_vSumF Φ e A base c mγ Λ hε a b)

open QED.GradedProof.VP2 in
/-- **The inner integrands of a class are integrable in both stages** at every photon momentum,
from `EL1`. -/
theorem jointEnergyFirstIntegrable_vSumF (hF : EL1 (vSumF Φ e A base c mγ Λ)) {ε : ℝ}
    (hε : 0 < ε) (z : ℂ) (a b : Fin 4) (k : Fin 4 → ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => z * vSumF Φ e A base c mγ Λ ε k ℓ a b := by
  obtain ⟨C, hC⟩ := hF ε hε a b
  obtain ⟨h1, h2, -⟩ := hC k
  refine ⟨fun v => (h1 v).const_mul z, ?_⟩
  simp only [integral_const_mul]
  exact h2.const_mul z

theorem kSq_neg (k : Fin 4 → ℝ) : kSq (-k) = kSq k := by simp [kSq]

open QED.GradedProof.VP2 in
/-- `innerBoundL1_vSumF` at the reversed photon momentum `-k`. -/
theorem innerBoundL1_vSumF_neg (hF : EL1 (vSumF Φ e A base c mγ Λ)) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) (a b : Fin 4) :
    InnerBoundL1 fun k ℓ => z * vSumF Φ e A base c mγ Λ ε (-k) ℓ a b := by
  obtain ⟨C, hC⟩ := hF ε hε a b
  refine ⟨fun w => ?_, ‖z‖ * C, fun k => ?_⟩
  · have hc : Continuous fun y : (ℝ × (Fin 2 → Fin 3 → ℝ)) × (Fin 2 → ℝ) =>
        vSumF Φ e A base c mγ Λ ε (-Fin.cons y.1.1 w) (loopMomenta y.2 y.1.2) a b :=
      continuous_vSumF Φ e A base c mγ Λ hε a b
        (Continuous.finCons (A := fun _ => ℝ) (continuous_fst.comp continuous_fst)
          (continuous_const (y := w))).neg
        (QED.Integration.TwoLoop.continuous_loopMomenta.comp
          (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
    simp only [integral_const_mul]
    exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable.const_mul
      z
  · obtain ⟨-, h2, h3⟩ := hC (-k)
    rw [kSq_neg] at h3
    refine ⟨?_, ?_⟩
    · simp only [integral_const_mul]
      exact h2.const_mul z
    · simp only [integral_const_mul, norm_mul]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)

open QED.GradedProof.VP2 in
/-- `jointEnergyFirstIntegrable_vSumF` at the reversed photon momentum `-k`. -/
theorem jointEnergyFirstIntegrable_vSumF_neg (hF : EL1 (vSumF Φ e A base c mγ Λ)) {ε : ℝ}
    (hε : 0 < ε) (z : ℂ) (a b : Fin 4) (k : Fin 4 → ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      z * vSumF Φ e A base c mγ Λ ε (-k) ℓ a b :=
  jointEnergyFirstIntegrable_vSumF Φ e mγ Λ A base c hF hε z a b (-k)

end Classes

end QED.ChainProof.SetANestV

end
