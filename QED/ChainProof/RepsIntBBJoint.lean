/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBBRot
public import QED.TwoLoop.NestedVP
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (T₉′) for the bubble–bubble integrand in the nested routing

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53).

**`jointEnergyFirstIntegrable_bbIntegrand`**: at `ε > 0` and under the two Pauli–Villars
conditions, with no condition on the masses, both stages of the joint energy-first integral of
`bbIntegrand P (chainOuter P p kext · α β μ)` converge absolutely.

* Stage 1 (energies at fixed spatial momenta): the bound `exists_Fz_rect` at `z = 1`.
* Stage 2: by `QED.Integration.ThreeLoop.integral_eq_rotate` the energy integral equals
  `(1 + s i)³` times the energy integral at the rotated energies `(1 + s i) t`, where every
  denominator is elliptic. There the integrand is bounded by
  `C ρ(ℓ₂)⁻⁶ (ρ(ℓ₀ + ℓ₂)⁻⁵ + ρ(ℓ₀)⁻⁵)(ρ(ℓ₁ + ℓ₂)⁻⁵ + ρ(ℓ₁)⁻⁵)`, `ρ(ℓ) = 1 + |ℓ|`, jointly
  integrable over `(ℝ⁴)³` (`integrable_Gl`, by unimodular shears), and the splitting
  `(t, v) ↦ ℓ` preserves measure (`measurePreserving_join`).
-/

@[expose] public section

open Complex MeasureTheory QED.Integration.ThreeLoop QED.TwoLoop.JointIntegralInvariance

namespace QED.ChainProof.RepsIntBB

open QED.WickModel

/-! ### Measure theory on `(ℝ⁴)³` -/

/-- The splitting of the loop momenta into energies and spatial components preserves measure. -/
theorem measurePreserving_join :
    MeasurePreserving (fun x : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → ℝ) => joinMomenta x.2 x.1) := by
  have h1 : MeasurePreserving (Prod.swap : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → ℝ) → _) :=
    Measure.measurePreserving_swap
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ (Fin 3 → ℝ) (Fin 3)).symm
  have h3 := volume_preserving_pi (ι := Fin 3)
    (fun _ => (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm)
  have := h3.comp (h2.comp h1)
  convert this using 1
  funext x s
  simp [joinMomenta, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
    MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

/-- `ρ(x)⁻ᵏ`, `ρ(x) = 1 + |x|`. -/
noncomputable def jb (k : ℕ) (x : Fin 4 → ℝ) : ℝ := ((1 + ‖x‖) ^ k)⁻¹

theorem jb_nonneg (k : ℕ) (x : Fin 4 → ℝ) : 0 ≤ jb k x := by unfold jb; positivity

theorem integrable_jb {k : ℕ} (hk : 5 ≤ k) : Integrable (jb k) := by
  have := integrable_one_add_norm (E := Fin 4 → ℝ) (μ := volume) (r := k)
    (by simp; exact_mod_cast hk)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [jb]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- The unimodular shear `(ℓ₀, ℓ₁, ℓ₂) ↦ (ℓ₀ + c₀ ℓ₂, ℓ₁ + c₁ ℓ₂, ℓ₂)`. -/
def shearM (c0 c1 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, c0; 0, 1, c1; 0, 0, 1]

theorem integrable_shear (c0 c1 : ℤ) :
    Integrable (fun ℓ : Fin 3 → Fin 4 → ℝ =>
      jb 5 (ℓ 0 + (c0 : ℝ) • ℓ 2) * jb 5 (ℓ 1 + (c1 : ℝ) • ℓ 2) * jb 6 (ℓ 2)) := by
  have hH : Integrable (fun ℓ : Fin 3 → Fin 4 → ℝ => ∏ i, ![jb 5, jb 5, jb 6] i (ℓ i)) :=
    Integrable.fintype_prod (μ := fun _ => volume) fun i => by
      fin_cases i <;> simp <;> exact integrable_jb (by norm_num)
  have hdet : |LinearMap.det (matrixAct (Fin 4 → ℝ) (shearM c0 c1))| = 1 := by
    rw [det_matrixAct_pi]
    simp [shearM, Matrix.det_fin_three]
  obtain ⟨hmp, hemb⟩ := QED.TwoLoop.NestedVP.measurePreserving_linear_add volume
    (matrixAct (Fin 4 → ℝ) (shearM c0 c1)) hdet 0
  have := (hmp.integrable_comp_emb hemb).mpr hH
  refine this.congr (Filter.Eventually.of_forall fun ℓ => ?_)
  simp [Fin.prod_univ_three, matrixAct_apply, Fin.sum_univ_three, shearM, Int.cast_smul_eq_zsmul]

/-- The joint dominating function at the rotated energies. -/
noncomputable def Gl (ℓ : Fin 3 → Fin 4 → ℝ) : ℝ :=
  jb 6 (ℓ 2) * (jb 5 (ℓ 0 + ℓ 2) + jb 5 (ℓ 0)) * (jb 5 (ℓ 1 + ℓ 2) + jb 5 (ℓ 1))

theorem integrable_Gl : Integrable Gl := by
  have h11 : Integrable (fun ℓ : Fin 3 → Fin 4 → ℝ =>
      jb 5 (ℓ 0 + ℓ 2) * jb 5 (ℓ 1 + ℓ 2) * jb 6 (ℓ 2)) := by
    simpa using integrable_shear 1 1
  have h10 : Integrable (fun ℓ : Fin 3 → Fin 4 → ℝ =>
      jb 5 (ℓ 0 + ℓ 2) * jb 5 (ℓ 1) * jb 6 (ℓ 2)) := by
    simpa using integrable_shear 1 0
  have h01 : Integrable (fun ℓ : Fin 3 → Fin 4 → ℝ =>
      jb 5 (ℓ 0) * jb 5 (ℓ 1 + ℓ 2) * jb 6 (ℓ 2)) := by
    simpa using integrable_shear 0 1
  have h00 : Integrable (fun ℓ : Fin 3 → Fin 4 → ℝ =>
      jb 5 (ℓ 0) * jb 5 (ℓ 1) * jb 6 (ℓ 2)) := by
    simpa using integrable_shear 0 0
  refine ((h11.add h10).add (h01.add h00)).congr (Filter.Eventually.of_forall fun ℓ => ?_)
  simp only [Gl, Pi.add_apply]
  ring

/-- **Stage 2 from joint integrability**: if `K` is integrable on `(ℝ⁴)³`, its energy integral
at fixed spatial momenta is integrable in the spatial momenta. -/
theorem integrable_integral_join {K : (Fin 3 → Fin 4 → ℝ) → ℂ} (hK : Integrable K) :
    Integrable fun v : Fin 3 → Fin 3 → ℝ => ∫ τ, K (joinMomenta τ v) := by
  have h2 := (measurePreserving_join.integrable_comp hK.aestronglyMeasurable).mpr hK
  exact h2.integral_prod_left

theorem integrable_inv_one_add_abs_pow {k : ℕ} (hk : 2 ≤ k) :
    Integrable (fun t : ℝ => ((1 + |t|) ^ k)⁻¹) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := k)
    (by simp; exact_mod_cast (by omega : 1 < k))
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem integrable_rectBound :
    Integrable (fun τ : Fin 3 → ℝ =>
      ((1 + |τ 0|) ^ 2)⁻¹ * ((1 + |τ 1|) ^ 2)⁻¹ * ((1 + |τ 2|) ^ 6)⁻¹) := by
  have := Integrable.fintype_prod (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun i t => ((1 + |t|) ^ (![2, 2, 6] i))⁻¹)
    fun i => integrable_inv_one_add_abs_pow (by fin_cases i <;> simp)
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp [Fin.prod_univ_three]
  ring

/-! ### From `σ` to `ρ` -/

theorem norm_cons_le (t : ℝ) (y : Fin 3 → ℝ) : ‖(Fin.cons t y : Fin 4 → ℝ)‖ ≤ |t| + ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, Real.norm_eq_abs]
    linarith [norm_nonneg y]
  · simp only [Fin.cons_succ]
    linarith [norm_le_pi_norm y j, abs_nonneg t]

theorem inv_sig_pow_le (t : ℝ) (y : Fin 3 → ℝ) (k : ℕ) :
    (sig t y)⁻¹ ^ k ≤ jb k (Fin.cons t y) := by
  rw [jb, ← inv_pow]
  refine pow_le_pow_left₀ (inv_nonneg.2 (sig_pos t y).le) ?_ k
  refine inv_anti₀ (by positivity) ?_
  unfold sig
  linarith [norm_cons_le t y]

theorem cons_add_cons (a b : ℝ) (y y' : Fin 3 → ℝ) :
    (Fin.cons (a + b) (y + y') : Fin 4 → ℝ) = Fin.cons a y + Fin.cons b y' := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem inv_sig_pow_le_jb (ℓ : Fin 3 → Fin 4 → ℝ) (i : Fin 3) (k : ℕ) :
    (sig (ℓ i 0) (Fin.tail (ℓ i)))⁻¹ ^ k ≤ jb k (ℓ i) := by
  have := inv_sig_pow_le (ℓ i 0) (Fin.tail (ℓ i)) k
  rwa [Fin.cons_self_tail] at this

theorem inv_sig_pow_le_jb_add (ℓ : Fin 3 → Fin 4 → ℝ) (i j : Fin 3) (k : ℕ) :
    (sig (ℓ i 0 + ℓ j 0) (Fin.tail (ℓ i) + Fin.tail (ℓ j)))⁻¹ ^ k ≤ jb k (ℓ i + ℓ j) := by
  have := inv_sig_pow_le (ℓ i 0 + ℓ j 0) (Fin.tail (ℓ i) + Fin.tail (ℓ j)) k
  rwa [cons_add_cons, Fin.cons_self_tail, Fin.cons_self_tail] at this

/-! ### Regularity of the rotated integrand -/

theorem differentiableAt_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : E → ℂ} {Y : E → Fin 3 → ℂ} {x : E} (hX : DifferentiableAt ℂ X x)
    (hY : DifferentiableAt ℂ Y x) :
    DifferentiableAt ℂ (fun e => (Fin.cons (X e) (Y e) : Fin 4 → ℂ)) x := by
  refine differentiableAt_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hX
  · simpa using differentiableAt_pi.1 hY j

theorem differentiableAt_Fz_z (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (v : Fin 3 → Fin 3 → ℝ) (τ : Fin 3 → ℝ) {z : ℂ}
    (hg : GoodBB P (cv p) (cv kext) (rl z τ v)) :
    DifferentiableAt ℂ (fun w => Fz P p kext α β μ v w τ) z := by
  have hℓ : DifferentiableAt ℂ (fun w : ℂ => rl w τ v) z := by
    refine differentiableAt_pi.2 fun s => ?_
    change DifferentiableAt ℂ (fun w : ℂ => (Fin.cons (w * (τ s : ℂ))
      (fun i => ((v s i : ℝ) : ℂ)) : Fin 4 → ℂ)) z
    exact differentiableAt_cons (differentiableAt_id.mul_const _) (differentiableAt_const _)
  exact differentiableAt_bbC P (cv p) (cv kext) α β μ hℓ hg

theorem continuous_Fz (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) {z : ℂ}
    (hg : ∀ τ v, GoodBB P (cv p) (cv kext) (rl z τ v)) :
    Continuous (fun x : (Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) => Fz P p kext α β μ x.2 z x.1) := by
  let L : (Fin 3 → ℂ) × (Fin 3 → Fin 3 → ℂ) → Fin 3 → Fin 4 → ℂ :=
    fun w s => Fin.cons (z * w.1 s) (w.2 s)
  let ι : (Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) → (Fin 3 → ℂ) × (Fin 3 → Fin 3 → ℂ) :=
    fun x => (fun s => (x.1 s : ℂ), fun s i => (x.2 s i : ℂ))
  have hι : Continuous ι := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun s => continuous_ofReal.comp ((continuous_apply s).comp continuous_fst)
    · exact continuous_pi fun s => continuous_pi fun i => continuous_ofReal.comp
        ((continuous_apply i).comp ((continuous_apply s).comp continuous_snd))
  have hL : ∀ w, DifferentiableAt ℂ L w := fun w => differentiableAt_pi.2 fun s =>
    differentiableAt_cons ((differentiableAt_pi.1 differentiableAt_fst s).const_mul z)
      (differentiableAt_pi.1 differentiableAt_snd s)
  have heq : ∀ x, L (ι x) = rl z x.1 x.2 := fun x => rfl
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hd := differentiableAt_bbC P (cv p) (cv kext) α β μ (hL (ι x))
    (by rw [heq]; exact hg _ _)
  exact hd.continuousAt.comp (f := ι) hι.continuousAt

theorem continuous_Fz_tau (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) {z : ℂ}
    (hg : ∀ τ v, GoodBB P (cv p) (cv kext) (rl z τ v)) (v : Fin 3 → Fin 3 → ℝ) :
    Continuous (fun τ => Fz P p kext α β μ v z τ) := by
  have := (continuous_Fz P p kext α β μ hg).comp
    (Continuous.prodMk continuous_id (continuous_const (y := v)))
  simpa only [Function.comp_def, id] using this

/-- The rotated integrand as a function of the loop momenta. -/
noncomputable def Kz (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (z : ℂ)
    (ℓ : Fin 3 → Fin 4 → ℝ) : ℂ :=
  Fz P p kext α β μ (fun s => Fin.tail (ℓ s)) z (fun s => ℓ s 0)

theorem Kz_join (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (z : ℂ) (τ : Fin 3 → ℝ)
    (v : Fin 3 → Fin 3 → ℝ) : Kz P p kext α β μ z (joinMomenta τ v) = Fz P p kext α β μ v z τ := by
  simp [Kz, joinMomenta]

theorem continuous_Kz (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) {z : ℂ}
    (hg : ∀ τ v, GoodBB P (cv p) (cv kext) (rl z τ v)) : Continuous (Kz P p kext α β μ z) := by
  have hi : Continuous fun ℓ : Fin 3 → Fin 4 → ℝ => ((fun s => ℓ s 0), fun s => Fin.tail (ℓ s)) :=
    Continuous.prodMk (continuous_pi fun s => (continuous_apply 0).comp (continuous_apply s))
      (continuous_pi fun s => continuous_pi fun j => (continuous_apply j.succ).comp
        (continuous_apply s))
  have := (continuous_Fz P p kext α β μ hg).comp hi
  rw [show Kz P p kext α β μ z = fun ℓ => Fz P p kext α β μ (fun s => Fin.tail (ℓ s)) z
    (fun s => ℓ s 0) from rfl]
  simpa only [Function.comp_def] using this

/-! ### Both stages -/

/-- **(T₉′) for the bubble–bubble integrand in the nested routing**, at `ε > 0` under the two
Pauli–Villars conditions, at all masses, external momenta and indices. -/
theorem jointEnergyFirstIntegrable_bbIntegrand (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (p kext : Fin 4 → ℝ) (α β μ : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3
      (QED.ChainProof.HCLimit.bbIntegrand P
        (fun k => QED.ChainProof.HCLimit.chainOuter P p kext k α β μ)) := by
  set A := 1 + p 0 ^ 2 + (p 0 + kext 0) ^ 2
  have hA : 0 < A := by positivity
  set h := min 1 (P.ε / (4 * A))
  have hh0 : 0 < h := lt_min one_pos (by positivity)
  have hh1 : h ≤ 1 := min_le_left _ _
  have hhA : h ≤ P.ε / (4 * A) := min_le_right _ _
  have key : ∀ x, x ≤ h → 0 ≤ x → ∀ a : ℝ, a ^ 2 ≤ A → x * a ^ 2 ≤ P.ε / 4 := by
    intro x hx hx0 a ha
    calc x * a ^ 2 ≤ (P.ε / (4 * A)) * A :=
          mul_le_mul (hx.trans hhA) ha (sq_nonneg _) (by positivity)
      _ = P.ε / 4 := by field_simp
  have hp1 : p 0 ^ 2 ≤ A := by simp only [A]; nlinarith [sq_nonneg (p 0 + kext 0)]
  have hp2 : (p 0 + kext 0) ^ 2 ≤ A := by simp only [A]; nlinarith [sq_nonneg (p 0)]
  set s := h / 2
  have hs0 : 0 < s := by positivity
  have hsh : s < h := by simp only [s]; linarith
  have hs1 : s ≤ 1 := by linarith
  have ha1 := key h le_rfl hh0.le _ hp1
  have ha2 := key h le_rfl hh0.le _ hp2
  have hgr : ∀ z ∈ rotRect h, ∀ τ v, GoodBB P (cv p) (cv kext) (rl z τ v) := fun z hz τ v =>
    goodBB_rect P hε p kext ha1 ha2 hz τ v
  have hF1 : ∀ (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ),
      QED.ChainProof.HCLimit.bbIntegrand P
        (fun k => QED.ChainProof.HCLimit.chainOuter P p kext k α β μ)
        (fun s => (Fin.cons (τ s) (v s) : Fin 4 → ℝ)) = Fz P p kext α β μ v 1 τ := by
    intro τ v
    rw [Fz, rl_one]
    exact (bbC_real P p kext α β μ (fun s => Fin.cons (τ s) (v s))).symm
  refine ⟨fun v => ?_, ?_⟩
  · simp only [hF1]
    obtain ⟨C, hC0, hC⟩ := exists_Fz_rect P hε p kext α β μ v hh1 ha1 ha2
    exact Integrable.mono' (integrable_rectBound.const_mul C)
      (continuous_Fz_tau P p kext α β μ (hgr 1 (one_mem_rotRect hh0.le)) v).aestronglyMeasurable
      (ae_of_all _ fun τ => hC 1 (one_mem_rotRect hh0.le) τ)
  · have hrot : ∀ v, ∫ τ, Fz P p kext α β μ v 1 τ =
        (1 + s * I) ^ 3 * ∫ τ, Fz P p kext α β μ v (1 + s * I) τ := by
      intro v
      obtain ⟨C, hC0, hC⟩ := exists_Fz_rect P hε p kext α β μ v hh1 ha1 ha2
      exact integral_eq_rotate (f := fun z τ => Fz P p kext α β μ v z τ)
        (fun z τ r _ => by simp only [Fz, rl_smul]) hh0 (integrable_rectBound.const_mul C) hC
        (fun τ z hz => differentiableAt_Fz_z P p kext α β μ v τ (hgr z hz τ v))
        (fun z hz => (continuous_Fz_tau P p kext α β μ (hgr z hz) v).aestronglyMeasurable)
        hs0 hsh
    simp only [hF1, hrot]
    refine Integrable.const_mul ?_ _
    have hb1 := key s hsh.le hs0.le _ hp1
    have hb2 := key s hsh.le hs0.le _ hp2
    obtain ⟨C, hC0, hC⟩ := exists_Fz_rot P hε hc₁ hc₂ p kext α β μ hs0 hs1 hb1 hb2
    have hgz : ∀ τ v, GoodBB P (cv p) (cv kext) (rl (1 + s * I) τ v) :=
      goodBB_rot P hε p kext hs0 hb1 hb2
    have hK : Integrable (Kz P p kext α β μ (1 + s * I)) := by
      refine Integrable.mono' (integrable_Gl.const_mul C)
        (continuous_Kz P p kext α β μ hgz).aestronglyMeasurable (ae_of_all _ fun ℓ => ?_)
      refine (hC (fun s => ℓ s 0) (fun s => Fin.tail (ℓ s))).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hC0
      have n := fun (t : ℝ) (y : Fin 3 → ℝ) (k : ℕ) =>
        pow_nonneg (inv_nonneg.2 (sig_pos t y).le) k
      unfold Gl
      refine mul_le_mul (mul_le_mul (inv_sig_pow_le_jb ℓ 2 6)
        (add_le_add (inv_sig_pow_le_jb_add ℓ 0 2 5) (inv_sig_pow_le_jb ℓ 0 5))
        (add_nonneg (n _ _ _) (n _ _ _)) (jb_nonneg _ _))
        (add_le_add (inv_sig_pow_le_jb_add ℓ 1 2 5) (inv_sig_pow_le_jb ℓ 1 5))
        (add_nonneg (n _ _ _) (n _ _ _))
        (mul_nonneg (jb_nonneg _ _) (add_nonneg (jb_nonneg _ _) (jb_nonneg _ _)))
    have := integrable_integral_join hK
    simpa only [Kz_join] using this

end QED.ChainProof.RepsIntBB

end
