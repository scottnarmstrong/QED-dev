/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.NestedVPAmplitude
public import QED.OneLoop.VertexAlgebra
public import Mathlib.Analysis.Matrix.Normed
import QED.Integration.LoopBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Decay of the outer factor of the vacuum-polarization class in the photon energy

Part of the Fubini condition `hG` of the nested-equals-joint theorem
`QED.TwoLoop.NestedVP.contractionValue₂_VP_eq_nested_energyFirst` (obligation O2-8). At fixed
`ε > 0`, fixed external momenta and fixed spatial photon momentum `w`, the outer factor
`vpOuter … (t, w) α β μ ρ σ` (the open-line chain times the two photon propagators) decays like
`(1 + |t|)⁻¹⁰` in the photon energy `t`: each electron propagator contributes `(1 + |t|)⁻¹` and
each Pauli–Villars regulated photon propagator `(1 + |t|)⁻⁴`.

## Main statements

* `QED.TwoLoop.NestedVPFubiniBound.DecaysLike`: `‖f t‖ ≤ C (1 + |t|)^{-n}`, with its calculus.
* `QED.TwoLoop.NestedVPFubiniBound.exists_norm_denom_ge`: a denominator `q² + M² - iε` whose
  momentum has fixed spatial part and energy `±t + b` is at least `c (1 + |t|)²` in norm.
* `QED.TwoLoop.NestedVPFubiniBound.decaysLike_vpOuter`: **the decay of the outer factor**.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Complex

namespace QED.TwoLoop.NestedVPFubiniBound

open QED.WickModel QED.OneLoop

/-! ### The decay predicate -/

/-- `f t` decays like `(1 + |t|)^{-n}`: `‖f t‖ ≤ C (1 + |t|)^{-n}` for all `t`. -/
def DecaysLike {E : Type*} [Norm E] (f : ℝ → E) (n : ℤ) : Prop :=
  ∃ C : ℝ, ∀ t, ‖f t‖ ≤ C * (1 + |t|) ^ (-n)

theorem one_add_abs_pos (t : ℝ) : 0 < 1 + |t| := by positivity

theorem one_le_one_add_abs (t : ℝ) : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]

namespace DecaysLike

variable {E : Type*}

theorem const_nonneg [SeminormedAddGroup E] {f : ℝ → E} {n : ℤ} {C : ℝ}
    (h : ∀ t, ‖f t‖ ≤ C * (1 + |t|) ^ (-n)) : 0 ≤ C := by
  have h0 := h 0
  rw [abs_zero, add_zero, one_zpow, mul_one] at h0
  exact (norm_nonneg _).trans h0

theorem mono [SeminormedAddGroup E] {f : ℝ → E} {n n' : ℤ} (hf : DecaysLike f n) (h : n' ≤ n) :
    DecaysLike f n' := by
  obtain ⟨C, hC⟩ := hf
  have hC0 := const_nonneg hC
  refine ⟨C, fun t => (hC t).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (one_le_one_add_abs t) (by omega)) hC0

theorem const [SeminormedAddGroup E] (c : E) : DecaysLike (fun _ : ℝ => c) 0 :=
  ⟨‖c‖, fun t => by simp⟩

theorem add [SeminormedAddGroup E] {f g : ℝ → E} {n : ℤ} (hf : DecaysLike f n)
    (hg : DecaysLike g n) : DecaysLike (fun t => f t + g t) n := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun t => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add (hC t) (hD t))⟩

theorem sub [SeminormedAddGroup E] {f g : ℝ → E} {n : ℤ} (hf : DecaysLike f n)
    (hg : DecaysLike g n) : DecaysLike (fun t => f t - g t) n := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun t => (norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add (hC t) (hD t))⟩

theorem sum [SeminormedAddCommGroup E] {ι : Type*} (s : Finset ι) {f : ι → ℝ → E} {n : ℤ}
    (hf : ∀ i ∈ s, DecaysLike (f i) n) : DecaysLike (fun t => ∑ i ∈ s, f i t) n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun t => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mul [SeminormedRing E] {f g : ℝ → E} {a b : ℤ} (hf : DecaysLike f a)
    (hg : DecaysLike g b) : DecaysLike (fun t => f t * g t) (a + b) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  have hC0 := const_nonneg hC
  refine ⟨C * D, fun t => ?_⟩
  have hw := (one_add_abs_pos t).ne'
  calc ‖f t * g t‖ ≤ ‖f t‖ * ‖g t‖ := norm_mul_le _ _
    _ ≤ (C * (1 + |t|) ^ (-a)) * (D * (1 + |t|) ^ (-b)) :=
        mul_le_mul (hC t) (hD t) (norm_nonneg _) (by positivity)
    _ = C * D * (1 + |t|) ^ (-(a + b)) := by
        rw [neg_add, zpow_add₀ hw]
        ring

theorem smul [SeminormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → ℂ} {g : ℝ → E} {a b : ℤ}
    (hf : DecaysLike f a) (hg : DecaysLike g b) : DecaysLike (fun t => f t • g t) (a + b) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  have hC0 := const_nonneg hC
  refine ⟨C * D, fun t => ?_⟩
  have hw := (one_add_abs_pos t).ne'
  calc ‖f t • g t‖ ≤ ‖f t‖ * ‖g t‖ := norm_smul_le _ _
    _ ≤ (C * (1 + |t|) ^ (-a)) * (D * (1 + |t|) ^ (-b)) :=
        mul_le_mul (hC t) (hD t) (norm_nonneg _) (by positivity)
    _ = C * D * (1 + |t|) ^ (-(a + b)) := by
        rw [neg_add, zpow_add₀ hw]
        ring

theorem congr {E : Type*} [Norm E] {f g : ℝ → E} {n : ℤ} (hf : DecaysLike f n)
    (h : ∀ t, f t = g t) : DecaysLike g n := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun t => h t ▸ hC t⟩

/-- A quantity bounded below by `c (1 + |t|)²` has inverse decaying like `(1 + |t|)⁻²`. -/
theorem inv {f : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hf : ∀ t, c * (1 + |t|) ^ 2 ≤ ‖f t‖) :
    DecaysLike (fun t => (f t)⁻¹) 2 := by
  refine ⟨c⁻¹, fun t => ?_⟩
  have hw := one_add_abs_pos t
  have hpos : 0 < c * (1 + |t|) ^ 2 := by positivity
  rw [norm_inv, zpow_neg, ← mul_inv, zpow_two, ← sq]
  exact inv_anti₀ hpos (hf t)

/-- Linear growth is decay of order `-1`. -/
theorem of_linear [SeminormedAddGroup E] {f : ℝ → E} {C : ℝ} (hf : ∀ t, ‖f t‖ ≤ C * (1 + |t|)) :
    DecaysLike f (-1) :=
  ⟨C, fun t => by simpa using hf t⟩

end DecaysLike

/-! ### Lower bounds on the denominators -/

theorem abs_re_sub_le (X ε : ℝ) : |X| ≤ ‖(X : ℂ) - (ε : ℂ) * I‖ := by
  have h := Complex.abs_re_le_norm ((X : ℂ) - (ε : ℂ) * I)
  have hr : ((X : ℂ) - (ε : ℂ) * I).re = X := by simp
  rwa [hr] at h

theorem le_norm_sub_mul_I (X : ℝ) {ε : ℝ} (hε : 0 < ε) : ε ≤ ‖(X : ℂ) - (ε : ℂ) * I‖ := by
  have h := Complex.abs_im_le_norm ((X : ℂ) - (ε : ℂ) * I)
  have hi : ((X : ℂ) - (ε : ℂ) * I).im = -ε := by simp
  rwa [hi, abs_neg, abs_of_pos hε] at h

/-- `‖(-τ² + A) - iε‖ ≥ min ε 1 / (2 (A + 1)) · (1 + τ²)` for `A ≥ 0`, `ε > 0`. -/
theorem norm_sub_mul_I_ge {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (τ : ℝ) :
    min ε 1 / (2 * (A + 1)) * (1 + τ ^ 2) ≤ ‖((-τ ^ 2 + A : ℝ) : ℂ) - (ε : ℂ) * I‖ := by
  have hre := abs_re_sub_le (-τ ^ 2 + A) ε
  have him := le_norm_sub_mul_I (-τ ^ 2 + A) hε
  have hA1 : 0 < 2 * (A + 1) := by positivity
  have hm1 : min ε 1 ≤ 1 := min_le_right _ _
  have hmε : min ε 1 ≤ ε := min_le_left _ _
  have hm0 : 0 < min ε 1 := lt_min hε one_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ hA1]
  rcases le_or_gt (2 * A + 1) (τ ^ 2) with h | h
  · -- far from the shell: the real part dominates
    have hr : τ ^ 2 - A ≤ |-τ ^ 2 + A| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    nlinarith [sq_nonneg τ]
  · -- near the shell: the imaginary part
    nlinarith [sq_nonneg τ]

/-- **The denominators decay quadratically.** If the momentum `q t` has fixed spatial part and
energy with `|t| ≤ |q t 0| + b`, then `‖q² + M² - iε‖ ≥ c (1 + |t|)²`. -/
theorem exists_norm_denom_ge (M : ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℝ → Fin 4 → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hq0 : ∀ t, |t| ≤ |q t 0| + b) (hqs : ∀ t (i : Fin 3), q t i.succ = q 0 i.succ) :
    ∃ c > 0, ∀ t, c * (1 + |t|) ^ 2 ≤ ‖denom M ε (q t)‖ := by
  set A : ℝ := q 0 1 ^ 2 + q 0 2 ^ 2 + q 0 3 ^ 2 + M ^ 2
  have hA : 0 ≤ A := by positivity
  set c₀ := min ε 1 / (2 * (A + 1))
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨c₀ / (2 * (1 + b) ^ 2), by positivity, fun t => ?_⟩
  have h1 : q t 1 = q 0 1 := hqs t 0
  have h2 : q t 2 = q 0 2 := hqs t 1
  have h3 : q t 3 = q 0 3 := hqs t 2
  have hD : denom M ε (q t) = ((-(q t 0) ^ 2 + A : ℝ) : ℂ) - (ε : ℂ) * I := by
    simp only [denom, Minkowski.dot_eq, h1, h2, h3, A]
    congr 2
    ring
  rw [hD]
  refine le_trans ?_ (norm_sub_mul_I_ge hε hA (q t 0))
  have hτ := hq0 t
  have hw : (1 + |t|) ^ 2 ≤ 2 * (1 + b) ^ 2 * (1 + q t 0 ^ 2) := by
    have h' : 1 + |t| ≤ (1 + |q t 0|) * (1 + b) := by nlinarith [abs_nonneg (q t 0)]
    have h'' : (1 + |q t 0|) ^ 2 ≤ 2 * (1 + q t 0 ^ 2) := by
      nlinarith [sq_abs (q t 0), sq_nonneg (|q t 0| - 1)]
    calc (1 + |t|) ^ 2 ≤ ((1 + |q t 0|) * (1 + b)) ^ 2 := by gcongr
      _ = (1 + |q t 0|) ^ 2 * (1 + b) ^ 2 := by ring
      _ ≤ 2 * (1 + q t 0 ^ 2) * (1 + b) ^ 2 := by gcongr
      _ = _ := by ring
  have hb2 : 0 < 2 * (1 + b) ^ 2 := by positivity
  calc c₀ / (2 * (1 + b) ^ 2) * (1 + |t|) ^ 2
      ≤ c₀ / (2 * (1 + b) ^ 2) * (2 * (1 + b) ^ 2 * (1 + q t 0 ^ 2)) := by gcongr
    _ = c₀ * (1 + q t 0 ^ 2) := by field_simp

/-! ### The propagators along the photon energy -/

/-- The inverse denominator along `a - (t, w)`, `±(t, w)` decays like `(1 + |t|)⁻²`. -/
theorem decaysLike_inv_denom (M : ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℝ → Fin 4 → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hq0 : ∀ t, |t| ≤ |q t 0| + b) (hqs : ∀ t (i : Fin 3), q t i.succ = q 0 i.succ) :
    DecaysLike (fun t => (denom M ε (q t))⁻¹) 2 := by
  obtain ⟨c, hc, h⟩ := exists_norm_denom_ge M hε q hb hq0 hqs
  exact DecaysLike.inv hc h

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem norm_apply_le_norm (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => zero_le)
      (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))
  exact_mod_cast h

theorem norm_lower_le (ℓ : Fin 4 → ℝ) (κ : Fin 4) : ‖Minkowski.lower ℓ κ‖ ≤ ‖ℓ‖ := by
  have h := norm_le_pi_norm ℓ
  rw [Minkowski.lower_eq]
  fin_cases κ
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · simpa using h 3

theorem norm_slash_le (ℓ : Fin 4 → ℝ) :
    ‖Dirac.slash ℓ‖ ≤ (∑ κ, ‖Dirac.gamma κ‖) * ‖ℓ‖ := by
  rw [Dirac.slash, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  rw [norm_smul, Complex.norm_real, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_lower_le ℓ κ) (norm_nonneg _)

/-- The electron numerator `m - q̸` grows linearly along a momentum of norm `≤ |t| + B`. -/
theorem decaysLike_electronNumerator (m : ℝ) (q : ℝ → Fin 4 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hq : ∀ t, ‖q t‖ ≤ |t| + B) :
    DecaysLike (fun t => (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (q t)) (-1) := by
  set G := ∑ κ, ‖Dirac.gamma κ‖
  set a := ‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)‖
  have hG : 0 ≤ G := Finset.sum_nonneg fun κ _ => norm_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  refine DecaysLike.of_linear (C := a + G * (1 + B)) fun t => ?_
  have h1 := norm_slash_le (q t)
  have h2 : G * ‖q t‖ ≤ G * (|t| + B) := mul_le_mul_of_nonneg_left (hq t) hG
  refine (norm_sub_le _ _).trans ?_
  have := abs_nonneg t
  nlinarith [mul_nonneg hG this, mul_nonneg ha this, mul_nonneg (mul_nonneg hG hB) this]

/-- **The electron propagator along the photon energy** decays like `(1 + |t|)⁻¹`. -/
theorem decaysLike_electronPropagator (m : ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℝ → Fin 4 → ℝ) {b B : ℝ}
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hq0 : ∀ t, |t| ≤ |q t 0| + b)
    (hqs : ∀ t (i : Fin 3), q t i.succ = q 0 i.succ) (hq : ∀ t, ‖q t‖ ≤ |t| + B) :
    DecaysLike (fun t => electronPropagator m ε (q t)) 1 := by
  have h := (decaysLike_inv_denom m hε q hb hq0 hqs).smul (decaysLike_electronNumerator m q hB hq)
  exact h.congr fun t => rfl

/-- **The open-line chain** decays like `(1 + |t|)⁻²` along `k = (t, w)`. -/
theorem decaysLike_outerChain (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (w : Fin 3 → ℝ)
    (μ ρ ν : Fin 4) :
    DecaysLike (fun t => NestedVP.outerChain P p kext (Fin.cons t w) μ ρ ν) 2 := by
  have hsub : ∀ a : Fin 4 → ℝ, DecaysLike (fun t => electronPropagator P.m P.ε
      (a - (Fin.cons t w : Fin 4 → ℝ))) 1 := fun a => by
    refine decaysLike_electronPropagator P.m hε _ (abs_nonneg (a 0)) (by positivity : 0 ≤ ‖a‖ + ‖w‖)
      (fun t => ?_) (fun t i => ?_) (fun t => ?_)
    · simp only [Pi.sub_apply, Fin.cons_zero]
      have := abs_sub_abs_le_abs_sub t (a 0)
      rw [abs_sub_comm] at this
      linarith [abs_sub_comm (a 0) t]
    · simp
    · refine (norm_sub_le _ _).trans ?_
      have := QED.Integration.norm_finCons_le t w
      linarith
  have h := (((((DecaysLike.const (Dirac.gamma ν)).mul (hsub (p + kext))).mul
    (DecaysLike.const (Dirac.gamma μ))).mul (hsub p)).mul (DecaysLike.const (Dirac.gamma ρ)))
  exact h.congr fun t => rfl

/-- An entry of a decaying matrix decays. -/
theorem DecaysLike.apply {f : ℝ → Matrix (Fin 4) (Fin 4) ℂ} {n : ℤ} (hf : DecaysLike f n)
    (i j : Fin 4) : DecaysLike (fun t => f t i j) n := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun t => (norm_apply_le_norm _ i j).trans (hC t)⟩

end MatrixNorm

/-- **The regulated photon propagator** decays like `(1 + |t|)⁻⁴` along `±(t, w)`. -/
theorem decaysLike_photonPropagator (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℝ → Fin 4 → ℝ)
    (hq0 : ∀ t, |t| ≤ |q t 0|) (hqs : ∀ t (i : Fin 3), q t i.succ = q 0 i.succ) (ρ σ : Fin 4) :
    DecaysLike (fun t => photonPropagator mγ Λ ε (q t) ρ σ) 4 := by
  have hq0' : ∀ t, |t| ≤ |q t 0| + 0 := fun t => by simpa using hq0 t
  have hγ := decaysLike_inv_denom mγ hε q le_rfl hq0' hqs
  have hΛ := decaysLike_inv_denom Λ hε q le_rfl hq0' hqs
  have h := (DecaysLike.const ((Minkowski.metric ρ σ : ℝ) : ℂ)).mul
    ((hγ.mul (DecaysLike.const (((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ)))).mul hΛ)
  refine h.congr fun t => ?_
  have hne : ∀ M : ℝ, denom M ε (q t) ≠ 0 := fun M h0 => by
    have := congrArg Complex.im h0
    rw [denom_im] at this
    simp at this
    exact hε.ne' this
  simp only [photonPropagator]
  change _ = ((Minkowski.metric ρ σ : ℝ) : ℂ) * ((denom mγ ε (q t))⁻¹ - (denom Λ ε (q t))⁻¹)
  rw [inv_sub_inv' (hne mγ) (hne Λ)]
  congr 2
  simp only [denom]
  push_cast
  ring

/-- **The outer factor decays like `(1 + |t|)⁻¹⁰`** in the photon energy `t`, at fixed `ε > 0`,
external momenta and spatial photon momentum `w`. -/
theorem decaysLike_vpOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (w : Fin 3 → ℝ)
    (α β μ ρ σ : Fin 4) :
    DecaysLike (fun t => NestedVP.vpOuter P p kext (Fin.cons t w) α β μ ρ σ) 10 := by
  have hk := decaysLike_photonPropagator P.mγ P.Λ hε (fun t => (Fin.cons t w : Fin 4 → ℝ))
    (fun t => by simp) (fun t i => by simp)
  have hk' := decaysLike_photonPropagator P.mγ P.Λ hε (fun t => -(Fin.cons t w : Fin 4 → ℝ))
    (fun t => by simp) (fun t i => by simp)
  have h := (DecaysLike.const (-(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 4)).mul
    (DecaysLike.sum Finset.univ fun l0 _ => DecaysLike.sum Finset.univ fun l2 _ =>
      (((decaysLike_outerChain P hε p kext w μ l0 l2).apply α β).mul (hk l0 ρ)).mul (hk' l2 σ))
  exact h.congr fun t => rfl

end QED.TwoLoop.NestedVPFubiniBound

end
