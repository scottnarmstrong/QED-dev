/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtAssemblyBound

/-!
# Powers of `k²` over any number of photon-type denominators

Generic layer of the `ε → 0⁺` engine for one-loop vertices with inserted photon functions
(helper level; used by the bubble–`δ₃` classes of set (b) and reusable by the bubble–bubble
class). The engine of `QED/TwoLoop/VPHalfAtLimitPhoton.lean` treats
`N(ℓ) / (D_m(p'+ℓ) D_m(p+ℓ) ∏_j D_{M_j}(ℓ; ε_j))` with `k + 2 ≥ 2` photon-type denominators,
arbitrary masses `M_j ≥ M₀ > 0` and arbitrary positive prescriptions. This file adds a factor
`(k²)ʲ` for every `j ≤ k`, i.e. whenever at least two photon-type denominators remain after the
`k²` are absorbed.

* `powInt j Ms es`: `(k²)ʲ` times `QED.TwoLoop.VPHalfAtLimit.prodIntegrand` with masses `Ms` and
  prescriptions `es`.
* `powInt_succ`: `(k²)^{j+1} ∏_i D_i⁻¹ = (k²)ʲ ∏_{i ≥ 1} D_i⁻¹ - t₀ (k²)ʲ ∏_i D_i⁻¹`,
  `t₀ = M₀² - iε₀`: one `k²` is absorbed by the first denominator.
* `powLimit j Ms`: the limit, defined by the same recursion from
  `QED.TwoLoop.VPHalfAtLimit.prodLimit`; it depends on the masses only.
* **`tendsto_efi_powInt`**: for `j ≤ k`, along any countably generated filter on which the
  electron prescription and **every** photon prescription tend to `0⁺`, the energy-first integral
  of `powInt j Ms es` tends to `powLimit j Ms`.
* **`exists_goodEF_powInt`, `exists_ptBd_powInt`**: bounds uniform in the masses `≥ M₀` and in the
  prescriptions: if the first `j` shifts satisfy `‖M_i² - iε_i‖ ≤ T`, the vertex is `GoodEF` with
  constant `(1 + T)ʲ K`, `K` independent of everything else, and satisfies the pointwise bound
  `(1 + T)ʲ G` for photon prescriptions `≥ e₀`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtGen

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly

/-! ### Definitions -/

/-- `(k²)ʲ N(ℓ) / (D_m(p'+ℓ; ε) D_m(p+ℓ; ε) ∏_i D_{M_i}(ℓ; ε_i))`. -/
noncomputable def powInt (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * prodIntegrand N m Ms es ε p' p ℓ

/-- The limit of the energy-first integral of `powInt j Ms`, by the absorption recursion. -/
noncomputable def powLimit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) :
    (j : ℕ) → {k : ℕ} → (Fin (k + 2) → ℝ) → ℂ
  | 0, _, Ms => prodLimit α N m Ms p' p
  | _ + 1, 0, _ => 0
  | j + 1, _ + 1, Ms =>
      powLimit α N m p' p j (Fin.tail Ms) - ((Ms 0 ^ 2 : ℝ) : ℂ) * powLimit α N m p' p j Ms

theorem powLimit_zero (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) : powLimit α N m p' p 0 Ms = prodLimit α N m Ms p' p := by
  simp [powLimit]

theorem powLimit_succ (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ}
    (Ms : Fin (k + 3) → ℝ) :
    powLimit α N m p' p (j + 1) Ms =
      powLimit α N m p' p j (Fin.tail Ms) - ((Ms 0 ^ 2 : ℝ) : ℂ) * powLimit α N m p' p j Ms := by
  simp [powLimit]

theorem powInt_zero (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ) (ε : ℝ)
    (p' p ℓ : Fin 4 → ℝ) : powInt N m 0 Ms es ε p' p ℓ = prodIntegrand N m Ms es ε p' p ℓ := by
  simp [powInt]

/-- **One `k²` absorbed by the first denominator.** -/
theorem powInt_succ (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ} (Ms es : Fin (k + 3) → ℝ)
    (hes0 : 0 < es 0) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    powInt N m (j + 1) Ms es ε p' p ℓ =
      powInt N m j (Fin.tail Ms) (Fin.tail es) ε p' p ℓ -
        massShift (Ms 0) (es 0) * powInt N m j Ms es ε p' p ℓ := by
  have h := prodIntegrand_mul_s N m Ms es hes0 ε p' p ℓ
  simp only [powInt, pow_succ]
  linear_combination ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * h

theorem tendsto_massShift (M : ℝ) {ι : Type*} {l : Filter ι} {e : ι → ℝ}
    (he : Tendsto e l (𝓝 0)) :
    Tendsto (fun i => massShift M (e i)) l (𝓝 ((M ^ 2 : ℝ) : ℂ)) := by
  have h : Tendsto (fun i => ((M ^ 2 : ℝ) : ℂ) - ((e i : ℝ) : ℂ) * I) l
      (𝓝 (((M ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)) :=
    tendsto_const_nhds.sub (((continuous_ofReal.tendsto 0).comp he).mul_const I)
  simpa [massShift] using h

/-! ### Uniform bounds -/

section Bounds

variable {m M₀ : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

/-- **The `GoodEF` bound for `(k²)ʲ` over `k + 2` denominators**, `j ≤ k`: the constant is
`(1 + T)ʲ K` whenever the first `j` shifts are bounded by `T`, with `K` independent of the
masses `≥ M₀`, of `T` and of all prescriptions. -/
theorem exists_goodEF_powInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) :
    ∀ (j k : ℕ), j ≤ k → ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ Ms es : Fin (k + 2) → ℝ,
      (∀ i, M₀ ≤ Ms i) → (∀ i, 0 < es i) →
      (∀ i : Fin (k + 2), i.val < j → ‖massShift (Ms i) (es i)‖ ≤ T) →
      ∀ ε : ℝ, 0 < ε → GoodEF (powInt N m j Ms es ε p' p) ((1 + T) ^ j * K) := by
  intro j
  induction j with
  | zero =>
    intro k _
    obtain ⟨K, hK, h⟩ := exists_goodEF_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb k
    refine ⟨K, hK, fun T _ Ms es hMs hes _ ε hε => ?_⟩
    exact ((h Ms es hMs hes ε hε).congr fun ℓ => (powInt_zero N m Ms es ε p' p ℓ).symm).mono'
      (by simp)
  | succ j ih =>
    intro k hjk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨K1, hK1, h1⟩ := ih k (by omega)
    obtain ⟨K2, hK2, h2⟩ := ih (k + 1) (by omega)
    refine ⟨K1 + K2, by positivity, fun T hT Ms es hMs hes hTs ε hε => ?_⟩
    have g1 := h1 T hT (Fin.tail Ms) (Fin.tail es) (fun i => hMs _) (fun i => hes _)
      (fun i hi => hTs i.succ (by simp; omega)) ε hε
    have g2 := h2 T hT Ms es hMs hes (fun i hi => hTs i (by omega)) ε hε
    have t0 : ‖massShift (Ms 0) (es 0)‖ ≤ T := hTs 0 (by simp)
    have h := g1.sub (g2.const_mul (massShift (Ms 0) (es 0)))
    refine (h.congr fun ℓ => (powInt_succ N m j Ms es (hes 0) ε p' p ℓ).symm).mono' ?_
    have hTj : 0 ≤ (1 + T) ^ j := by positivity
    have a : ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2) ≤ T * ((1 + T) ^ j * K2) :=
      mul_le_mul_of_nonneg_right t0 (by positivity)
    have b : (1 + T) ^ j * K1 ≤ (1 + T) ^ j * ((1 + T) * K1) := by
      gcongr; nlinarith
    have c : T * ((1 + T) ^ j * K2) ≤ (1 + T) ^ j * ((1 + T) * K2) := by
      have : T * K2 ≤ (1 + T) * K2 := by nlinarith
      nlinarith
    calc (1 + T) ^ j * K1 + ‖massShift (Ms 0) (es 0)‖ * ((1 + T) ^ j * K2)
        ≤ (1 + T) ^ j * ((1 + T) * K1) + (1 + T) ^ j * ((1 + T) * K2) := by linarith
      _ = (1 + T) ^ (j + 1) * (K1 + K2) := by ring

/-- **The pointwise bound for `(k²)ʲ` over `k + 2` denominators**, `j ≤ k`, uniform in the
masses and in photon prescriptions `≥ e₀`, at a fixed electron prescription `ε`. -/
theorem exists_ptBd_powInt (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {ε e₀ : ℝ}
    (hε : 0 < ε) (he₀ : 0 < e₀) (p' p : Fin 4 → ℝ) :
    ∀ (j k : ℕ), j ≤ k → ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ Ms es : Fin (k + 2) → ℝ, (∀ i, e₀ ≤ es i) →
      (∀ i : Fin (k + 2), i.val < j → ‖massShift (Ms i) (es i)‖ ≤ T) →
      PtBd (powInt N m j Ms es ε p' p) (fun v => (1 + T) ^ j * G v) := by
  intro j
  induction j with
  | zero =>
    intro k _
    obtain ⟨G, hG, h⟩ := exists_ptBd_prodIntegrand hNb m k hε he₀ p' p
    refine ⟨G, hG, fun T _ Ms es hes _ v t => ?_⟩
    rw [powInt_zero]
    simpa using h Ms es hes v t
  | succ j ih =>
    intro k hjk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨G1, hG1, h1⟩ := ih k (by omega)
    obtain ⟨G2, hG2, h2⟩ := ih (k + 1) (by omega)
    refine ⟨fun v => G1 v + G2 v, fun v => by have := hG1 v; have := hG2 v; positivity,
      fun T hT Ms es hes hTs => ?_⟩
    have hes0 : 0 < es 0 := he₀.trans_le (hes 0)
    have g1 := h1 T hT (Fin.tail Ms) (Fin.tail es) (fun i => hes _)
      (fun i hi => hTs i.succ (by simp; omega))
    have g2 := h2 T hT Ms es hes (fun i hi => hTs i (by omega))
    have t0 : ‖massShift (Ms 0) (es 0)‖ ≤ T := hTs 0 (by simp)
    intro v t
    rw [powInt_succ N m j Ms es hes0 ε p' p]
    have a1 := g1 v t
    have a2 := g2 v t
    have hT1 : 0 ≤ (1 + T) ^ j := by positivity
    have ht : 0 < (1 + t ^ 2)⁻¹ := by positivity
    have hG1v := hG1 v
    have hG2v := hG2 v
    calc ‖powInt N m j (Fin.tail Ms) (Fin.tail es) ε p' p (Fin.cons t v) -
          massShift (Ms 0) (es 0) * powInt N m j Ms es ε p' p (Fin.cons t v)‖
        ≤ ‖powInt N m j (Fin.tail Ms) (Fin.tail es) ε p' p (Fin.cons t v)‖ +
          ‖massShift (Ms 0) (es 0)‖ * ‖powInt N m j Ms es ε p' p (Fin.cons t v)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ (1 + T) ^ j * G1 v * (1 + t ^ 2)⁻¹ + T * ((1 + T) ^ j * G2 v * (1 + t ^ 2)⁻¹) := by
          gcongr
      _ ≤ (1 + T) ^ (j + 1) * (G1 v + G2 v) * (1 + t ^ 2)⁻¹ := by
          have e1 : 0 ≤ (1 + T) ^ j * G1 v * (1 + t ^ 2)⁻¹ := by positivity
          have e2 : 0 ≤ (1 + T) ^ j * G2 v * (1 + t ^ 2)⁻¹ := by positivity
          have key : (1 + T) ^ (j + 1) * (G1 v + G2 v) * (1 + t ^ 2)⁻¹ =
              (1 + T) ^ j * G1 v * (1 + t ^ 2)⁻¹ + T * ((1 + T) ^ j * G1 v * (1 + t ^ 2)⁻¹) +
              (1 + T) ^ j * G2 v * (1 + t ^ 2)⁻¹ +
              T * ((1 + T) ^ j * G2 v * (1 + t ^ 2)⁻¹) := by ring
          rw [key]
          nlinarith [mul_nonneg hT e1, mul_nonneg hT e2]

/-- The two bounds together: `Good`. -/
theorem exists_good_powInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (j k : ℕ) (hjk : j ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε e₀ : ℝ, 0 < ε → 0 < e₀ → ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧
      ∀ T : ℝ, 0 ≤ T → ∀ Ms es : Fin (k + 2) → ℝ, (∀ i, M₀ ≤ Ms i) → (∀ i, e₀ ≤ es i) →
      (∀ i : Fin (k + 2), i.val < j → ‖massShift (Ms i) (es i)‖ ≤ T) →
      Good (powInt N m j Ms es ε p' p) ((1 + T) ^ j * K) (fun v => (1 + T) ^ j * G v) := by
  obtain ⟨K, hK, hEF⟩ := exists_goodEF_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb j k hjk
  refine ⟨K, hK, fun ε e₀ hε he₀ => ?_⟩
  obtain ⟨G, hG, hPt⟩ := exists_ptBd_powInt (N := N) hNb m hε he₀ p' p j k hjk
  exact ⟨G, hG, fun T hT Ms es hMs hes hTs =>
    ⟨hEF T hT Ms es hMs (fun i => he₀.trans_le (hes i)) hTs ε hε, hPt T hT Ms es hes hTs⟩⟩

/-- Integrability in both stages, for `j ≤ k` and positive prescriptions. -/
theorem efInt_powInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {j k : ℕ} (hjk : j ≤ k) {Ms es : Fin (k + 2) → ℝ}
    (hMs : ∀ i, M₀ ≤ Ms i) (hes : ∀ i, 0 < es i) {ε : ℝ} (hε : 0 < ε) :
    EFInt (powInt N m j Ms es ε p' p) := by
  obtain ⟨K, -, h⟩ := exists_goodEF_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb j k hjk
  have hT : 0 ≤ ∑ i, ‖massShift (Ms i) (es i)‖ := by positivity
  exact (h _ hT Ms es hMs hes (fun i _ => Finset.single_le_sum
    (f := fun i => ‖massShift (Ms i) (es i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    ε hε).1

/-! ### The limit -/

/-- **The `ε → 0⁺` limit of `(k²)ʲ` over `k + 2` denominators**, `j ≤ k`: along any countably
generated filter on which the electron prescription and every photon prescription tend to `0⁺`,
the energy-first integral tends to `powLimit j Ms`, which depends on the masses only. -/
theorem tendsto_efi_powInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) :
    ∀ (j k : ℕ), j ≤ k → ∀ (Ms : Fin (k + 2) → ℝ) (es : ι → Fin (k + 2) → ℝ),
      (∀ i, M₀ ≤ Ms i) → (∀ i, Tendsto (fun t => es t i) l (𝓝[>] 0)) →
      Tendsto (fun t => energyFirstIntegral (powInt N m j Ms (es t) (ε t) p' p)) l
        (𝓝 (powLimit α N m p' p j Ms)) := by
  have hεpos : ∀ᶠ t in l, 0 < ε t := hε self_mem_nhdsWithin
  intro j
  induction j with
  | zero =>
    intro k _ Ms es hMs hes
    rw [powLimit_zero]
    have e : ∀ t, powInt N m 0 Ms (es t) (ε t) p' p = prodIntegrand N m Ms (es t) (ε t) p' p :=
      fun t => funext fun ℓ => powInt_zero N m Ms (es t) (ε t) p' p ℓ
    simp only [e]
    exact tendsto_energyFirstIntegral_prodIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hε hes
  | succ j ih =>
    intro k hjk Ms es hMs hes
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hespos : ∀ᶠ t in l, ∀ i, 0 < es t i :=
      eventually_all.2 fun i => (hes i) self_mem_nhdsWithin
    have l1 := ih k (by omega) (Fin.tail Ms) (fun t => Fin.tail (es t)) (fun i => hMs _)
      (fun i => hes _)
    have l2 := ih (k + 1) (by omega) Ms es hMs hes
    have l0 := tendsto_massShift (Ms 0) ((hes 0).mono_right nhdsWithin_le_nhds)
    rw [powLimit_succ]
    refine (l1.sub (l0.mul l2)).congr' ?_
    filter_upwards [hεpos, hespos] with t ht hest
    have i1 := efInt_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := j) (k := k) (by omega)
      (Ms := Fin.tail Ms) (es := Fin.tail (es t)) (fun i => hMs _) (fun i => hest _) ht
    have i2 := efInt_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := j) (k := k + 1) (by omega)
      (Ms := Ms) (es := es t) hMs hest ht
    have e : powInt N m (j + 1) Ms (es t) (ε t) p' p = fun ℓ =>
        powInt N m j (Fin.tail Ms) (Fin.tail (es t)) (ε t) p' p ℓ +
          (-massShift (Ms 0) (es t 0)) * powInt N m j Ms (es t) (ε t) p' p ℓ := by
      funext ℓ
      rw [powInt_succ N m j Ms (es t) (hest 0)]
      ring
    rw [e, efi_add i1 (i2.const_mul _), efi_const_mul]
    ring

end Bounds

end QED.TwoLoop.VPHalfAtGen

end
