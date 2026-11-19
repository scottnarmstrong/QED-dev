/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtGenPow
public import QED.TwoLoop.VPHalfAtAssemblyPieces

/-!
# Spectral insertions over any number of photon-type denominators

Generic layer of the `ε → 0⁺` engine (helper level; used by the bubble–`δ₃` classes of set (b),
reusable by the bubble–bubble class). After the integration by parts in its Feynman parameter `x`,
each inserted one-loop vacuum polarization `Π̂_ε` contributes, per loop flavour of mass `M`, a
factor `1/(M² + x(1-x)k² - iε)` (`QED.TwoLoop.VPHalfAtAssembly.fDen`). For `0 < x < 1` this is
`(x(1-x))⁻¹` times a photon-type denominator of mass `μ_x = √(M²/(x(1-x)))` and prescription
`ε/(x(1-x))`. This file treats any number `r` of such insertions, with their own masses and
Feynman parameters, on top of `(k²)ʲ` and any list of photon-type denominators with their own
prescriptions.

* `specInt j Ms es Msp xs`: `QED.TwoLoop.VPHalfAtGen.powInt j Ms es` times
  `∏_{i<r} 1/(M_i² + x_i(1-x_i)k² - iε)`.
* `specInt_succ_lim` (**limit form**): one insertion becomes `(x(1-x))⁻¹` times one more
  photon-type denominator, appended at the end of the list, with its own prescription.
* `specInt_succ_fact` (**factored form**): `1/(M² + x(1-x)k² - iε) = t⁻¹ (1 - k²/D_{μ_x})`,
  `t = M² - iε`, so one insertion becomes the difference of two terms bounded uniformly in `x`.
* **`tendsto_efi_specInt`**: at fixed Feynman parameters in `(0, 1)`, for `j ≤ k`, the
  energy-first integral tends to `specLimit j Ms Msp xs` when the electron prescription and every
  photon prescription tend to `0⁺` (the spectral prescriptions `ε/(x(1-x))` follow).
* **`exists_good_specInt`**: for `j ≤ k` and `j + r ≤ k + 2`, the vertex is `Good` with constants
  `(1 + T)^{j+r} K`, `(1 + T)^{j+r} G` uniform in the Feynman parameters `x_i ∈ (0, 1)`, in the
  flavour masses `≥ M_lo` and in the photon masses `≥ M₀`, when the first `j + r` shifts are
  bounded by `T`: every `k²` (including the one produced by each factored insertion) is absorbed
  by a photon-type denominator of bounded mass.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtGen

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration
open QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly

/-! ### Definitions -/

/-- `(k²)ʲ N / (D D ∏ D_{M_i}(ε_i)) · ∏_{i<r} 1/(M_i² + x_i(1-x_i)k² - iε)`. -/
noncomputable def specInt (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) {r : ℕ} (Msp xs : Fin r → ℝ) (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  powInt N m j Ms es ε p' p ℓ * ∏ i, (fDen (Msp i) ε (xs i) ℓ)⁻¹

/-- The limit of `specInt` at fixed Feynman parameters. -/
noncomputable def specLimit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) :
    (r : ℕ) → {k : ℕ} → (Fin (k + 2) → ℝ) → (Fin r → ℝ) → (Fin r → ℝ) → ℂ
  | 0, _, Ms, _, _ => powLimit α N m p' p j Ms
  | r + 1, k, Ms, Msp, xs => ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ *
      specLimit α N m p' p j r (k := k + 1)
        (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp) (Fin.tail xs)

theorem specLimit_zero (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin 0 → ℝ) :
    specLimit α N m p' p j 0 Ms Msp xs = powLimit α N m p' p j Ms := rfl

theorem specLimit_succ (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ) (j r : ℕ)
    {k : ℕ} (Ms : Fin (k + 2) → ℝ) (Msp xs : Fin (r + 1) → ℝ) :
    specLimit α N m p' p j (r + 1) Ms Msp xs = ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ *
      specLimit α N m p' p j r (k := k + 1)
        (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp)
        (Fin.tail xs) := rfl

/-! ### Appending a photon-type denominator -/

theorem prodIntegrand_snoc (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (μ η ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    prodIntegrand N m (Fin.snoc Ms μ : Fin (k + 1 + 2) → ℝ) (Fin.snoc es η : Fin (k + 1 + 2) → ℝ)
        ε p' p ℓ = prodIntegrand N m Ms es ε p' p ℓ * (denom μ η ℓ)⁻¹ := by
  unfold prodIntegrand
  rw [Fin.prod_univ_castSucc (n := k + 2)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem powInt_snoc (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (μ η ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    powInt N m j (Fin.snoc Ms μ : Fin (k + 1 + 2) → ℝ) (Fin.snoc es η : Fin (k + 1 + 2) → ℝ)
        ε p' p ℓ = powInt N m j Ms es ε p' p ℓ * (denom μ η ℓ)⁻¹ := by
  rw [powInt, powInt, prodIntegrand_snoc]
  ring

theorem snoc_castSucc_of_lt {k : ℕ} {β : Type*} (f : Fin (k + 2) → β) (b : β) (i : Fin (k + 3))
    (hi : i.val < k + 2) :
    (Fin.snoc f b : Fin (k + 1 + 2) → β) i = f ⟨i.val, hi⟩ := by
  simp only [Fin.snoc, hi, dite_true]
  rfl

/-! ### The limit and factored forms of one insertion -/

/-- **The limit form of one insertion**: `(x(1-x))⁻¹` times one more photon-type denominator of
mass `μ_x` and prescription `ε/(x(1-x))`, appended at the end. -/
theorem specInt_succ_lim (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    {r : ℕ} (Msp xs : Fin (r + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) (hx : xs 0 ∈ Ioo (0 : ℝ) 1)
    (p' p ℓ : Fin 4 → ℝ) :
    specInt N m j Ms es Msp xs ε p' p ℓ = ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ *
      specInt N m j (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ)
        (Fin.snoc es (specEta ε (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp) (Fin.tail xs)
        ε p' p ℓ := by
  have h0 : ((xs 0 * (1 - xs 0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioo_mul_pos hx).ne'
  have hD := fDen_ne_zero (Msp 0) hε (xs 0) ℓ
  unfold specInt
  rw [powInt_snoc, denom_specMu hx, Fin.prod_univ_succ]
  simp only [Fin.tail]
  field_simp

/-- **The factored form of one insertion**:
`1/(M² + x(1-x)k² - iε) = t⁻¹ (1 - k² D_{μ_x}⁻¹)`, `t = M² - iε`. -/
theorem specInt_succ_fact (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) {r : ℕ} (Msp xs : Fin (r + 1) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hx : xs 0 ∈ Ioo (0 : ℝ) 1) (p' p ℓ : Fin 4 → ℝ) :
    specInt N m j Ms es Msp xs ε p' p ℓ = (massShift (Msp 0) ε)⁻¹ *
      (specInt N m j Ms es (Fin.tail Msp) (Fin.tail xs) ε p' p ℓ -
        specInt N m (j + 1) (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ)
          (Fin.snoc es (specEta ε (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp) (Fin.tail xs)
          ε p' p ℓ) := by
  have h0 : ((xs 0 * (1 - xs 0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioo_mul_pos hx).ne'
  have hD := fDen_ne_zero (Msp 0) hε (xs 0) ℓ
  have hS := massShift_ne_zero (Msp 0) hε
  have e : fDen (Msp 0) ε (xs 0) ℓ = massShift (Msp 0) ε +
      ((xs 0 * (1 - xs 0) : ℝ) : ℂ) * ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) := by
    simp only [fDen, massShift, QED.WickModel.vacuumPolarizationFeynmanMass]
    push_cast
    ring
  unfold specInt
  rw [powInt_snoc, denom_specMu hx, Fin.prod_univ_succ]
  simp only [Fin.tail, powInt, pow_succ]
  field_simp
  rw [e]
  ring

/-! ### The limit at fixed Feynman parameters -/

theorem tendsto_specEta' {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) :
    Tendsto (fun t => specEta (ε t) x) l (𝓝[>] 0) := by
  have h0 := mem_Ioo_mul_pos hx
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun e : ℝ => e / (x * (1 - x))) (𝓝 0) (𝓝 (0 / (x * (1 - x)))) :=
      (continuous_id.div_const _).tendsto 0
    rw [zero_div] at h
    exact h.comp (hε.mono_right nhdsWithin_le_nhds)
  · filter_upwards [hε self_mem_nhdsWithin] with t (ht : 0 < ε t)
    exact div_pos ht h0

section Engine

variable {m M₀ : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

/-- **The `ε → 0⁺` limit with `r` spectral insertions at fixed Feynman parameters**, `j ≤ k`. -/
theorem tendsto_efi_specInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (j : ℕ) :
    ∀ (r k : ℕ), j ≤ k → ∀ (Ms : Fin (k + 2) → ℝ) (es : ι → Fin (k + 2) → ℝ)
      (Msp xs : Fin r → ℝ), (∀ i, M₀ ≤ Ms i) → (∀ i, M₀ ≤ Msp i) →
      (∀ i, xs i ∈ Ioo (0 : ℝ) 1) → (∀ i, Tendsto (fun t => es t i) l (𝓝[>] 0)) →
      Tendsto (fun t => energyFirstIntegral (specInt N m j Ms (es t) Msp xs (ε t) p' p)) l
        (𝓝 (specLimit α N m p' p j r Ms Msp xs)) := by
  have hεpos : ∀ᶠ t in l, 0 < ε t := hε self_mem_nhdsWithin
  intro r
  induction r with
  | zero =>
    intro k hjk Ms es Msp xs hMs _ _ hes
    have e : ∀ t, specInt N m j Ms (es t) Msp xs (ε t) p' p = powInt N m j Ms (es t) (ε t) p' p :=
      fun t => funext fun ℓ => by simp [specInt]
    simp only [e, specLimit_zero]
    exact tendsto_efi_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hε j k hjk Ms es hMs hes
  | succ r ih =>
    intro k hjk Ms es Msp xs hMs hMsp hxs hes
    have hx0 := hxs 0
    have hμ : M₀ ≤ specMu (Msp 0) (xs 0) := (hMsp 0).trans (specMu_ge (hM₀.trans_le (hMsp 0)) hx0)
    have hlim := ih (k + 1) (by omega) (Fin.snoc Ms (specMu (Msp 0) (xs 0)))
      (fun t => Fin.snoc (es t) (specEta (ε t) (xs 0))) (Fin.tail Msp) (Fin.tail xs)
      (fun i => Fin.lastCases (by simpa using hμ) (fun i => by simpa using hMs i) i)
      (fun i => hMsp _) (fun i => hxs _)
      (fun i => Fin.lastCases (by simpa using tendsto_specEta' hx0 hε)
        (fun i => by simpa using hes i) i)
    rw [specLimit_succ]
    refine (hlim.const_mul _).congr' ?_
    filter_upwards [hεpos] with t ht
    have e : specInt N m j Ms (es t) Msp xs (ε t) p' p = fun ℓ =>
        ((xs 0 * (1 - xs 0) : ℝ) : ℂ)⁻¹ *
          specInt N m j (Fin.snoc Ms (specMu (Msp 0) (xs 0)) : Fin (k + 1 + 2) → ℝ)
            (Fin.snoc (es t) (specEta (ε t) (xs 0)) : Fin (k + 1 + 2) → ℝ) (Fin.tail Msp)
            (Fin.tail xs) (ε t) p' p ℓ :=
      funext fun ℓ => specInt_succ_lim N m j Ms (es t) Msp xs ht hx0 p' p ℓ
    rw [e, efi_const_mul]

/-! ### Bounds uniform in the Feynman parameters -/

/-- **`specInt` is `Good` uniformly in the Feynman parameters and the flavour masses**, for
`j ≤ k` and `j + r ≤ k + 2`, when the first `j + r` shifts are bounded by `T`. -/
theorem exists_good_specInt (hm : 0 < m) (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {Mlo : ℝ} (hMlo : M₀ ≤ Mlo) :
    ∀ (r j k : ℕ), j ≤ k → j + r ≤ k + 2 → ∃ K : ℝ, 0 ≤ K ∧ ∀ ε e₀ : ℝ, 0 < ε → 0 < e₀ → e₀ ≤ ε →
      ∃ G : (Fin 3 → ℝ) → ℝ, (∀ v, 0 ≤ G v) ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ Ms es : Fin (k + 2) → ℝ, (∀ i, M₀ ≤ Ms i) → (∀ i, e₀ ≤ es i) →
      (∀ i : Fin (k + 2), i.val < j + r → ‖massShift (Ms i) (es i)‖ ≤ T) →
      ∀ Msp xs : Fin r → ℝ, (∀ i, Mlo ≤ Msp i) → (∀ i, xs i ∈ Ioo (0 : ℝ) 1) →
      Good (specInt N m j Ms es Msp xs ε p' p) ((1 + T) ^ (j + r) * K)
        (fun v => (1 + T) ^ (j + r) * G v) := by
  intro r
  induction r with
  | zero =>
    intro j k hjk _
    obtain ⟨K, hK, h⟩ := exists_good_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb j k hjk
    refine ⟨K, hK, fun ε e₀ hε he₀ _ => ?_⟩
    obtain ⟨G, hG, hg⟩ := h ε e₀ hε he₀
    refine ⟨G, hG, fun T hT Ms es hMs hes hTs Msp xs _ _ => ?_⟩
    exact (hg T hT Ms es hMs hes (fun i hi => hTs i (by simpa using hi))).congr
      fun ℓ => by simp [specInt]
  | succ r ih =>
    intro j k hjk hjr
    have hMlo0 : 0 < Mlo := hM₀.trans_le hMlo
    obtain ⟨K1, hK1, h1⟩ := ih j k hjk (by omega)
    obtain ⟨K2, hK2, h2⟩ := ih (j + 1) (k + 1) (by omega) (by omega)
    set L : ℝ := (Mlo ^ 2)⁻¹
    have hL : 0 ≤ L := by positivity
    refine ⟨L * (K1 + K2), by positivity, fun ε e₀ hε he₀ he₀ε => ?_⟩
    obtain ⟨G1, hG1, g1⟩ := h1 ε e₀ hε he₀ he₀ε
    obtain ⟨G2, hG2, g2⟩ := h2 ε e₀ hε he₀ he₀ε
    refine ⟨fun v => L * (G1 v + G2 v), fun v => by have := hG1 v; have := hG2 v; positivity,
      fun T hT Ms es hMs hes hTs Msp xs hMsp hxs => ?_⟩
    have hx0 := hxs 0
    have hμ : M₀ ≤ specMu (Msp 0) (xs 0) :=
      hMlo.trans ((hMsp 0).trans (specMu_ge (hMlo0.trans_le (hMsp 0)) hx0))
    have hη : e₀ ≤ specEta ε (xs 0) := he₀ε.trans (specEta_ge hε hx0)
    have a1 := g1 T hT Ms es hMs hes (fun i hi => hTs i (by omega)) (Fin.tail Msp) (Fin.tail xs)
      (fun i => hMsp _) (fun i => hxs _)
    have a2 := g2 T hT (Fin.snoc Ms (specMu (Msp 0) (xs 0)))
      (Fin.snoc es (specEta ε (xs 0)))
      (fun i => Fin.lastCases (by simpa using hμ) (fun i => by simpa using hMs i) i)
      (fun i => Fin.lastCases (by simpa using hη) (fun i => by simpa using hes i) i)
      (fun i hi => by
        rw [snoc_castSucc_of_lt Ms _ i (by omega), snoc_castSucc_of_lt es _ i (by omega)]
        exact hTs _ (by simp only; omega))
      (Fin.tail Msp) (Fin.tail xs) (fun i => hMsp _) (fun i => hxs _)
    have hinv : ‖(massShift (Msp 0) ε)⁻¹‖ ≤ L :=
      (norm_inv_massShift_le ε (hMlo0.trans_le (hMsp 0))).trans
        (inv_anti₀ (by positivity) (pow_le_pow_left₀ hMlo0.le (hMsp 0) 2))
    have h := (a1.sub a2).const_mul (massShift (Msp 0) ε)⁻¹
    refine (h.congr fun ℓ => (specInt_succ_fact N m j Ms es Msp xs hε hx0 p' p ℓ).symm).mono
      ?_ ?_
    · have hTj : 0 ≤ (1 + T) ^ (j + r) := by positivity
      have hT1 : (1 + T) ^ (j + r) ≤ (1 + T) ^ (j + (r + 1)) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have e2 : (1 + T) ^ (j + 1 + r) = (1 + T) ^ (j + (r + 1)) := by ring_nf
      rw [e2]
      calc ‖(massShift (Msp 0) ε)⁻¹‖ * ((1 + T) ^ (j + r) * K1 + (1 + T) ^ (j + (r + 1)) * K2)
          ≤ L * ((1 + T) ^ (j + (r + 1)) * K1 + (1 + T) ^ (j + (r + 1)) * K2) := by
            gcongr
        _ = (1 + T) ^ (j + (r + 1)) * (L * (K1 + K2)) := by ring
    · intro v
      have hTj : 0 ≤ (1 + T) ^ (j + r) := by positivity
      have hT1 : (1 + T) ^ (j + r) ≤ (1 + T) ^ (j + (r + 1)) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have e2 : (1 + T) ^ (j + 1 + r) = (1 + T) ^ (j + (r + 1)) := by ring_nf
      have := hG1 v
      have := hG2 v
      simp only
      rw [e2]
      calc ‖(massShift (Msp 0) ε)⁻¹‖ * ((1 + T) ^ (j + r) * G1 v +
            (1 + T) ^ (j + (r + 1)) * G2 v)
          ≤ L * ((1 + T) ^ (j + (r + 1)) * G1 v + (1 + T) ^ (j + (r + 1)) * G2 v) := by
            gcongr
        _ = (1 + T) ^ (j + (r + 1)) * (L * (G1 v + G2 v)) := by ring

end Engine

end QED.TwoLoop.VPHalfAtGen

end
