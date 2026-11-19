/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormLemma
public import QED.TwoLoop.ReflCovarianceParam

/-!
# Reflection-covariant transverse tensors have the form `Π(k²) (k² g - k k)`

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, step L2. Let `W`
be a two-index tensor function of a four-vector on the region `k² > -T²`, covariant under every
reflection `R_a` (`a² ≠ 0`), `W(R_a k) = R_a W(k) R_aᵀ` (`TCov`), and transverse,
`k_μ W^{μν}(k) = 0` (`Transv`). If moreover `W(t n₀) → W(0)` as `t → 0⁺` along the null vector
`n₀ = (1, 1, 0, 0)`, then `W(k) = Π(k²) (k² g - k k)` on the region (`exists_pol_of_cov`).

## Proof

* **Canonical vectors.** At `c = (x, 0, 0, 0)` the reflections in `e₁, e₂, e₃` fix `c` and kill the
  off-diagonal entries, transversality kills `W^{00}`, and the reflections in `e₁ - e₂`,
  `e₁ - e₃` equate the spatial diagonal. At `c = (0, x, 0, 0)` the same with `e₀, e₂, e₃`,
  `e₂ - e₃`, and the reflection in `(1, 0, 2, 0)` gives `W^{00} = -W^{22}`. At `n₀` the reflections
  in `e₂, e₃, e₂ - e₃` and `(1, 1, 1, 0)` with transversality leave `W = w n₀ n₀`.
* **Transport** along one or two reflections, as in `QED/GradedProof/SE2FormLemma.lean`:
  `k² g - k k` is covariant (`rAct_vpT`).
* **The origin.** `W(t n₀) = -Π(0) t² n₀ n₀ → 0`, so `W(0) = 0`.
-/

@[expose] public section

open Complex Filter Topology
open QED.Dirac

namespace QED.GradedProof.VP2

open QED.GradedProof.SE2 (reflect_sub_self reflect_add_self reflect_self_neg dot_neg_neg nullVec
  dot_nullVec canonVec dot_canonVec)

/-- The transverse tensor `k² g^{μν} - k^μ k^ν`. -/
noncomputable def vpT (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)

/-- The action of the reflection `R_a` on both (upper) indices. -/
noncomputable def rAct (a : Fin 4 → ℝ) (X : Fin 4 → Fin 4 → ℂ) (μ ν : Fin 4) : ℂ :=
  ∑ α, ∑ β, ((reflectMatrix a μ α : ℝ) : ℂ) * ((reflectMatrix a ν β : ℝ) : ℂ) * X α β

/-- **Covariance under reflections** on the region `k² > -T²`. -/
def TCov (T : ℝ) (W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ a : Fin 4 → ℝ, Minkowski.dot a a ≠ 0 → ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k →
    W (reflect a k) = rAct a (W k)

/-- **Transversality** `k_μ W^{μν}(k) = 0` on the region `k² > -T²`. -/
def Transv (T : ℝ) (W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ ν : Fin 4,
    ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * W k μ ν = 0

variable {T : ℝ} {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

/-! ### The transverse tensor is covariant -/

theorem rAct_vpT {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (k : Fin 4 → ℝ) :
    rAct a (vpT k) = vpT (reflect a k) := by
  funext μ ν
  have hl := (QED.TwoLoop.ReflCovariance.isSpinLift_reflect ha).lorentz_left μ ν
  have hm : ∀ ρ, ∑ α, reflectMatrix a ρ α * k α = reflect a k ρ := fun ρ => by
    rw [← reflectMatrix_mulVec]
    rfl
  have key : ∑ α, ∑ β, reflectMatrix a μ α * reflectMatrix a ν β *
      (Minkowski.dot k k * Minkowski.metric α β - k α * k β) =
      Minkowski.dot k k * Minkowski.metric μ ν - reflect a k μ * reflect a k ν := by
    rw [← hl, ← hm μ, ← hm ν, Finset.mul_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  simp only [rAct, vpT, dot_reflect ha, ← key]
  push_cast
  rfl

theorem rAct_mul (a : Fin 4 → ℝ) (x : ℂ) (X : Fin 4 → Fin 4 → ℂ) :
    rAct a (fun μ ν => x * X μ ν) = fun μ ν => x * rAct a X μ ν := by
  funext μ ν
  simp only [rAct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

/-! ### Transport along reflections -/

theorem form_reflect (hcov : TCov T W) {a q : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (hq : -T ^ 2 < Minkowski.dot q q) {x : ℂ} (hW : W q = fun μ ν => x * vpT q μ ν) :
    W (reflect a q) = fun μ ν => x * vpT (reflect a q) μ ν := by
  rw [hcov a ha q hq, hW, rAct_mul, rAct_vpT ha]

/-- **Transport between vectors of equal nonzero square.** -/
theorem form_of_dot_eq (hcov : TCov T W) {c p : Fin 4 → ℝ}
    (hs : Minkowski.dot c c = Minkowski.dot p p) (hs0 : Minkowski.dot c c ≠ 0)
    (hc : -T ^ 2 < Minkowski.dot c c) {x : ℂ} (hW : W c = fun μ ν => x * vpT c μ ν) :
    W p = fun μ ν => x * vpT p μ ν := by
  by_cases h : Minkowski.dot (c - p) (c - p) = 0
  · have hcp : Minkowski.dot (c + p) (c + p) ≠ 0 := by
      have : Minkowski.dot (c + p) (c + p) = 4 * Minkowski.dot c c := by
        simp only [Minkowski.dot_eq, Pi.sub_apply, Pi.add_apply] at hs h ⊢
        linarith
      rw [this]
      exact mul_ne_zero (by norm_num) hs0
    have h1 := form_reflect hcov hcp hc hW
    rw [reflect_add_self hs hs0 h] at h1
    have h2 := form_reflect hcov (hs ▸ hs0) (by rw [dot_neg_neg, ← hs]; exact hc) h1
    rwa [reflect_self_neg (hs ▸ hs0)] at h2
  · have h1 := form_reflect hcov h hc hW
    rwa [reflect_sub_self hs h] at h1

/-- **Transport from `n₀` to a nonzero null vector.** -/
theorem form_of_null (hcov : TCov T W) (hT : -T ^ 2 < 0) {p : Fin 4 → ℝ} (hp0 : p ≠ 0)
    (hpp : Minkowski.dot p p = 0) {x : ℂ} (hW : W nullVec = fun μ ν => x * vpT nullVec μ ν) :
    W p = fun μ ν => x * vpT p μ ν := by
  have hn : -T ^ 2 < Minkowski.dot nullVec nullVec := by rwa [dot_nullVec]
  have hs : Minkowski.dot nullVec nullVec = Minkowski.dot p p := by rw [dot_nullVec, hpp]
  by_cases h : Minkowski.dot (nullVec - p) (nullVec - p) = 0
  · have he : Minkowski.dot (![0, 1, 0, 0] : Fin 4 → ℝ) ![0, 1, 0, 0] ≠ 0 := by
      simp [Minkowski.dot_eq]
    have h1 := form_reflect hcov he hn hW
    have hc' : reflect ![0, 1, 0, 0] nullVec = ![1, -1, 0, 0] := by
      funext μ
      fin_cases μ <;> norm_num [reflect, Minkowski.dot_eq, nullVec]
    rw [hc'] at h1
    have hc'' : -T ^ 2 < Minkowski.dot (![1, -1, 0, 0] : Fin 4 → ℝ) ![1, -1, 0, 0] := by
      simpa [Minkowski.dot_eq] using hT
    have hs' : Minkowski.dot (![1, -1, 0, 0] : Fin 4 → ℝ) ![1, -1, 0, 0] =
        Minkowski.dot p p := by
      rw [hpp]
      simp [Minkowski.dot_eq]
    have hne : Minkowski.dot ((![1, -1, 0, 0] : Fin 4 → ℝ) - p) (![1, -1, 0, 0] - p) ≠ 0 := by
      simp only [Minkowski.dot_eq, Pi.sub_apply, nullVec, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] at h hpp ⊢
      intro h'
      have e01 : p 1 = p 0 := by nlinarith
      have e0 : p 0 = 0 := by nlinarith
      have e2 : p 2 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
      have e3 : p 3 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
      apply hp0
      funext μ
      fin_cases μ <;> simp [e0, e01, e2, e3]
    have h2 := form_reflect hcov hne hc'' h1
    rwa [reflect_sub_self hs' hne] at h2
  · have h1 := form_reflect hcov h hn hW
    rwa [reflect_sub_self hs h] at h1

/-! ### Reflections fixing a vector -/

theorem reflect_of_dot_zero {a v : Fin 4 → ℝ} (h : Minkowski.dot a v = 0) : reflect a v = v := by
  simp [reflect, h]

theorem cov_fix (hcov : TCov T W) {a c : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0)
    (hac : Minkowski.dot a c = 0) (hc : -T ^ 2 < Minkowski.dot c c) (μ ν : Fin 4) :
    W c μ ν = rAct a (W c) μ ν := by
  have h := hcov a ha c hc
  rw [reflect_of_dot_zero hac] at h
  exact congrFun (congrFun h μ) ν

/-- The sign of the reflection in a basis vector. -/
def flip (i μ : Fin 4) : ℝ := if μ = i then -1 else 1

theorem reflectMatrix_single (i μ α : Fin 4) :
    reflectMatrix (Pi.single i 1) μ α = if μ = α then flip i μ else 0 := by
  fin_cases i <;> fin_cases μ <;> fin_cases α <;>
    norm_num [reflectMatrix, flip, Minkowski.lower, Minkowski.metric, Minkowski.dot_eq,
      Fin.sum_univ_four, Pi.single_apply]

theorem rAct_single (i : Fin 4) (X : Fin 4 → Fin 4 → ℂ) (μ ν : Fin 4) :
    rAct (Pi.single i 1) X μ ν = ((flip i μ * flip i ν : ℝ) : ℂ) * X μ ν := by
  simp only [rAct, reflectMatrix_single]
  rw [Finset.sum_eq_single μ (fun α _ h => by simp [Ne.symm h]) (by simp),
    Finset.sum_eq_single ν (fun β _ h => by simp [Ne.symm h]) (by simp)]
  simp only [ite_true]
  push_cast
  ring

theorem dot_single_self (i : Fin 4) :
    Minkowski.dot (Pi.single i 1 : Fin 4 → ℝ) (Pi.single i 1) ≠ 0 := by
  fin_cases i <;> norm_num [Minkowski.dot_eq, Pi.single_apply]

/-- A reflection in a basis vector orthogonal to `c` kills the entries of `W(c)` with exactly one
index equal to the basis index. -/
theorem eq_zero_of_flip (hcov : TCov T W) {c : Fin 4 → ℝ} (i : Fin 4) (hci : c i = 0)
    (hc : -T ^ 2 < Minkowski.dot c c) {μ ν : Fin 4}
    (hμν : (μ = i ∧ ν ≠ i) ∨ (μ ≠ i ∧ ν = i)) : W c μ ν = 0 := by
  have hf : flip i μ * flip i ν = -1 := by
    rcases hμν with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [flip, h1, h2]
  have hd : Minkowski.dot (Pi.single i 1) c = 0 := by
    fin_cases i <;> simp_all [Minkowski.dot_eq]
  have h := cov_fix hcov (dot_single_self i) hd hc μ ν
  rw [rAct_single, hf] at h
  push_cast at h
  linear_combination h / 2

/-! ### The explicit reflections -/

theorem rm_12 : reflectMatrix ![0, 1, -1, 0] =
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
  ext μ α
  fin_cases μ <;> fin_cases α <;>
    norm_num [reflectMatrix, Minkowski.lower, Minkowski.metric, Minkowski.dot_eq, Fin.sum_univ_four]

theorem rm_13 : reflectMatrix ![0, 1, 0, -1] =
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0] := by
  ext μ α
  fin_cases μ <;> fin_cases α <;>
    norm_num [reflectMatrix, Minkowski.lower, Minkowski.metric, Minkowski.dot_eq, Fin.sum_univ_four]

theorem rm_23 : reflectMatrix ![0, 0, 1, -1] =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  ext μ α
  fin_cases μ <;> fin_cases α <;>
    norm_num [reflectMatrix, Minkowski.lower, Minkowski.metric, Minkowski.dot_eq, Fin.sum_univ_four]

theorem rm_102 : reflectMatrix ![1, 0, 2, 0] =
    !![5 / 3, 0, -4 / 3, 0; 0, 1, 0, 0; 4 / 3, 0, -5 / 3, 0; 0, 0, 0, 1] := by
  ext μ α
  fin_cases μ <;> fin_cases α <;>
    norm_num [reflectMatrix, Minkowski.lower, Minkowski.metric, Minkowski.dot_eq, Fin.sum_univ_four]

theorem rm_111 : reflectMatrix ![1, 1, 1, 0] =
    !![3, -2, -2, 0; 2, -1, -2, 0; 2, -2, -1, 0; 0, 0, 0, 1] := by
  ext μ α
  fin_cases μ <;> fin_cases α <;>
    norm_num [reflectMatrix, Minkowski.lower, Minkowski.metric, Minkowski.dot_eq, Fin.sum_univ_four]

/-- The entries of `rAct a X` for an explicit matrix of `R_a`. -/
theorem rAct_of_eq {a : Fin 4 → ℝ} {r : Matrix (Fin 4) (Fin 4) ℝ} (hr : reflectMatrix a = r)
    (X : Fin 4 → Fin 4 → ℂ) (μ ν : Fin 4) :
    rAct a X μ ν = ∑ α, ∑ β, ((r μ α : ℝ) : ℂ) * ((r ν β : ℝ) : ℂ) * X α β := by
  rw [rAct, hr]

/-! ### The canonical vectors -/

/-- **At rest**: `c = (x, 0, 0, 0)`. -/
theorem form_rest (hcov : TCov T W) (htr : Transv T W) {x : ℝ} (hx : x ≠ 0)
    (hc : -T ^ 2 < Minkowski.dot ![x, 0, 0, 0] ![x, 0, 0, 0]) :
    ∃ y : ℂ, W ![x, 0, 0, 0] = fun μ ν => y * vpT ![x, 0, 0, 0] μ ν := by
  set c : Fin 4 → ℝ := ![x, 0, 0, 0] with hcdef
  have hz : ∀ i : Fin 4, i ≠ 0 → c i = 0 := by
    intro i hi
    fin_cases i <;> simp_all [c]
  have off : ∀ μ ν : Fin 4, μ ≠ ν → W c μ ν = 0 := by
    intro μ ν h
    fin_cases μ <;> fin_cases ν <;>
      first
        | exact absurd rfl h
        | exact eq_zero_of_flip hcov 1 (hz 1 (by decide)) hc (by decide)
        | exact eq_zero_of_flip hcov 2 (hz 2 (by decide)) hc (by decide)
        | exact eq_zero_of_flip hcov 3 (hz 3 (by decide)) hc (by decide)
  have h00 : W c 0 0 = 0 := by
    have h := htr c hc 0
    simp only [Fin.sum_univ_four, off 1 0 (by decide), off 2 0 (by decide),
      off 3 0 (by decide), mul_zero, add_zero] at h
    have hl : Minkowski.lower c 0 = -x := by
      simp [Minkowski.lower, Minkowski.metric, c]
    rw [hl] at h
    have hx' : ((-x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast neg_ne_zero.2 hx
    exact (mul_eq_zero.1 h).resolve_left hx'
  have h12 : W c 1 1 = W c 2 2 := by
    have h := cov_fix hcov (a := ![0, 1, -1, 0]) (by norm_num [Minkowski.dot_eq])
      (by simp [Minkowski.dot_eq, c]) hc 1 1
    rw [rAct_of_eq rm_12] at h
    simpa [Fin.sum_univ_four] using h
  have h13 : W c 1 1 = W c 3 3 := by
    have h := cov_fix hcov (a := ![0, 1, 0, -1]) (by norm_num [Minkowski.dot_eq])
      (by simp [Minkowski.dot_eq, c]) hc 1 1
    rw [rAct_of_eq rm_13] at h
    simpa [Fin.sum_univ_four] using h
  refine ⟨-W c 1 1 / ((x ^ 2 : ℝ) : ℂ), funext fun μ => funext fun ν => ?_⟩
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [hcdef] at h12 h13 h00 off ⊢
  fin_cases μ <;> fin_cases ν <;>
    simp [vpT, Minkowski.dot_eq, Minkowski.metric, off, h00, ← h12, ← h13] <;>
    field_simp

/-- **Space-like**: `c = (0, x, 0, 0)`. -/
theorem form_space (hcov : TCov T W) (htr : Transv T W) {x : ℝ} (hx : x ≠ 0)
    (hc : -T ^ 2 < Minkowski.dot ![0, x, 0, 0] ![0, x, 0, 0]) :
    ∃ y : ℂ, W ![0, x, 0, 0] = fun μ ν => y * vpT ![0, x, 0, 0] μ ν := by
  set c : Fin 4 → ℝ := ![0, x, 0, 0] with hcdef
  have hz : ∀ i : Fin 4, i ≠ 1 → c i = 0 := by
    intro i hi
    fin_cases i <;> simp_all [c]
  have off : ∀ μ ν : Fin 4, μ ≠ ν → W c μ ν = 0 := by
    intro μ ν h
    fin_cases μ <;> fin_cases ν <;>
      first
        | exact absurd rfl h
        | exact eq_zero_of_flip hcov 0 (hz 0 (by decide)) hc (by decide)
        | exact eq_zero_of_flip hcov 2 (hz 2 (by decide)) hc (by decide)
        | exact eq_zero_of_flip hcov 3 (hz 3 (by decide)) hc (by decide)
  have h11 : W c 1 1 = 0 := by
    have h := htr c hc 1
    simp only [Fin.sum_univ_four, off 0 1 (by decide), off 2 1 (by decide),
      off 3 1 (by decide), mul_zero, zero_add, add_zero] at h
    have hl : Minkowski.lower c 1 = x := by
      simp [Minkowski.lower, Minkowski.metric, c]
    rw [hl] at h
    have hx' : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
    exact (mul_eq_zero.1 h).resolve_left hx'
  have h23 : W c 2 2 = W c 3 3 := by
    have h := cov_fix hcov (a := ![0, 0, 1, -1]) (by norm_num [Minkowski.dot_eq])
      (by simp [Minkowski.dot_eq, c]) hc 2 2
    rw [rAct_of_eq rm_23] at h
    simpa [Fin.sum_univ_four] using h
  have h02 : W c 0 0 = -W c 2 2 := by
    have h := cov_fix hcov (a := ![1, 0, 2, 0]) (by norm_num [Minkowski.dot_eq])
      (by simp [Minkowski.dot_eq, c]) hc 0 0
    rw [rAct_of_eq rm_102] at h
    simp [Fin.sum_univ_four, off 0 2 (by decide), off 2 0 (by decide)] at h
    linear_combination (-9 / 16 : ℂ) * h
  refine ⟨W c 2 2 / ((x ^ 2 : ℝ) : ℂ), funext fun μ => funext fun ν => ?_⟩
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [hcdef] at h11 h23 h02 off ⊢
  fin_cases μ <;> fin_cases ν <;>
    simp [vpT, Minkowski.dot_eq, Minkowski.metric, off, h11, h02, ← h23] <;>
    field_simp

/-- **Null**: `n₀ = (1, 1, 0, 0)`. -/
theorem form_null (hcov : TCov T W) (htr : Transv T W)
    (hc : -T ^ 2 < Minkowski.dot nullVec nullVec) :
    ∃ y : ℂ, W nullVec = fun μ ν => y * vpT nullVec μ ν := by
  have hn2 : nullVec 2 = 0 := rfl
  have hn3 : nullVec 3 = 0 := rfl
  have z : ∀ μ ν : Fin 4, ((μ = 2 ∧ ν ≠ 2) ∨ (μ ≠ 2 ∧ ν = 2)) ∨
      ((μ = 3 ∧ ν ≠ 3) ∨ (μ ≠ 3 ∧ ν = 3)) → W nullVec μ ν = 0 := by
    intro μ ν h
    rcases h with h | h
    · exact eq_zero_of_flip hcov 2 hn2 hc h
    · exact eq_zero_of_flip hcov 3 hn3 hc h
  have h23 : W nullVec 2 2 = W nullVec 3 3 := by
    have h := cov_fix hcov (a := ![0, 0, 1, -1]) (by norm_num [Minkowski.dot_eq])
      (by simp [Minkowski.dot_eq, nullVec]) hc 2 2
    rw [rAct_of_eq rm_23] at h
    simpa [Fin.sum_univ_four] using h
  have hl : ∀ ν, W nullVec 1 ν = W nullVec 0 ν := by
    intro ν
    have h := htr nullVec hc ν
    have l0 : Minkowski.lower nullVec 0 = -1 := by
      simp [Minkowski.lower, Minkowski.metric, nullVec]
    have l1 : Minkowski.lower nullVec 1 = 1 := by
      simp [Minkowski.lower, Minkowski.metric, nullVec]
    have l2 : Minkowski.lower nullVec 2 = 0 := by
      simp [Minkowski.lower, Minkowski.metric, nullVec]
    have l3 : Minkowski.lower nullVec 3 = 0 := by
      simp [Minkowski.lower, Minkowski.metric, nullVec]
    simp only [Fin.sum_univ_four, l0, l1, l2, l3] at h
    push_cast at h
    linear_combination h
  have e20 := cov_fix hcov (a := ![1, 1, 1, 0]) (by norm_num [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq, nullVec]) hc 2 0
  have e02 := cov_fix hcov (a := ![1, 1, 1, 0]) (by norm_num [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq, nullVec]) hc 0 2
  rw [rAct_of_eq rm_111] at e20 e02
  simp [Fin.sum_univ_four, z] at e20 e02
  have h10 := hl 0
  have h11 := hl 1
  have h22 : W nullVec 2 2 = 0 := by
    linear_combination (-1 / 2 : ℂ) * e20 + 3 * h10 - 2 * h11
  have h01 : W nullVec 0 1 = W nullVec 0 0 := by
    linear_combination (1 / 2 : ℂ) * e02 - 2 * h10 + 2 * h11 + h22
  have hn0 : nullVec 0 = 1 := rfl
  have hn1 : nullVec 1 = 1 := rfl
  refine ⟨-W nullVec 0 0, funext fun μ => funext fun ν => ?_⟩
  fin_cases μ <;> fin_cases ν <;>
    simp [vpT, dot_nullVec, hn0, hn1, hn2, hn3, z, h22, ← h23, h10, h11, h01]

/-! ### Assembly -/

theorem exists_form_canonVec (hcov : TCov T W) (htr : Transv T W) {s : ℝ} (hs : -T ^ 2 < s) :
    ∃ y : ℂ, W (canonVec s) = fun μ ν => y * vpT (canonVec s) μ ν := by
  have hc : -T ^ 2 < Minkowski.dot (canonVec s) (canonVec s) := by rwa [dot_canonVec]
  unfold canonVec at hc ⊢
  split_ifs at hc ⊢ with h1 h2
  · exact form_rest hcov htr (Real.sqrt_ne_zero'.mpr (by linarith)) hc
  · exact form_space hcov htr (Real.sqrt_ne_zero'.mpr h2) hc
  · exact form_null hcov htr hc

theorem vpT_smul (t : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    vpT (t • k) μ ν = ((t ^ 2 : ℝ) : ℂ) * vpT k μ ν := by
  simp only [vpT, Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **Reflection-covariant transverse tensors with a limit at the origin along `n₀` have the
form `Π(k²) (k² g - k k)`.** -/
theorem exists_pol_of_cov (hcov : TCov T W) (htr : Transv T W)
    (hcont : ∀ μ ν : Fin 4, Tendsto (fun t : ℝ => W (t • nullVec) μ ν) (𝓝[>] 0)
      (𝓝 (W 0 μ ν))) :
    ∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ μ ν : Fin 4,
      W k μ ν = Pol (Minkowski.dot k k) * vpT k μ ν := by
  classical
  choose! y hy using fun s (hs : -T ^ 2 < s) => exists_form_canonVec hcov htr hs
  refine ⟨y, fun k hk μ ν => ?_⟩
  have hc := hy _ hk
  by_cases hs0 : Minkowski.dot k k = 0
  · have hT : -T ^ 2 < 0 := hs0 ▸ hk
    have hn : W nullVec = fun μ ν => y 0 * vpT nullVec μ ν := by
      have h := hy 0 hT
      rwa [show canonVec 0 = nullVec by simp [canonVec]] at h
    rw [hs0]
    by_cases hk0 : k = 0
    · subst hk0
      have hv0 : vpT 0 μ ν = 0 := by simp [vpT, Minkowski.dot_eq]
      rw [hv0, mul_zero]
      have hlim : Tendsto (fun t : ℝ => y 0 * vpT (t • nullVec) μ ν) (𝓝[>] 0)
          (𝓝 (y 0 * vpT ((0 : ℝ) • nullVec) μ ν)) := by
        simp only [vpT_smul]
        refine Tendsto.const_mul _ (Tendsto.mul_const _ ?_)
        exact (Complex.continuous_ofReal.comp (continuous_pow 2)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      rw [zero_smul, hv0, mul_zero] at hlim
      refine tendsto_nhds_unique (hcont μ ν) (hlim.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      refine (congrFun (congrFun (form_of_null hcov hT ?_ ?_ hn) μ) ν).symm
      · intro h0
        have := congrFun h0 0
        simp [nullVec] at this
        linarith
      · simp [Minkowski.dot_eq, nullVec]
    · exact congrFun (congrFun (form_of_null hcov hT hk0 hs0 hn) μ) ν
  · exact congrFun (congrFun (form_of_dot_eq hcov (dot_canonVec _) (by rw [dot_canonVec]; exact hs0)
      (by rw [dot_canonVec]; exact hk) hc) μ) ν

end QED.GradedProof.VP2

end
