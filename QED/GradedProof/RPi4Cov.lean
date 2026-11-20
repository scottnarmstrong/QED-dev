/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4PairQ

/-!
# (R-Π₄): the projection at `s` through covariance, with no division by `s`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), uniformity in `s`. The
projection `projS X s` reads the coefficient `-B` of `X = A g + B k k`: through `trProj` at
`canonVec s` (weight `1/(3s²)`) for `s ≠ 0`, through the entry `(0, 1)` at `n₀` for `s = 0`. The
class tensors are not transverse one by one, so bounds on their entries do not bound `trProj`
near `s = 0`. Covariance removes the weight: the same `B` is an entry at a tilted vector.

* `exists_gk_rest`, `exists_gk_space`, `exists_gk_null`: a reflection-covariant tensor
  (`QED.GradedProof.VP2.TCov`) is `gkTensor A B k = A g + B k k` at `(x, 0, 0, 0)`,
  `(0, x, 0, 0)` and `n₀`, without transversality.
* `tiltVec c s = (√(2c² - s), 0, c, c)`, of square `s`; `(k₀ - k'(s))² ≠ 0` for the vector `k₀`
  read by `projS`, so one reflection maps `k₀` to `k'(s)` for every `s < 2c²`.
* `projS_eq_tilt`: `projS W s = -W(k'(s))²³ / c²` for covariant `W`, every `s` of the region below
  `2c²`, including `s = 0`.
* `qPair_eq_tilt`: the class sum at a photon pair is `-(i/c²)` times the sum of the class entries
  `(2, 3)` at `k'(s)`; `{k'(s) : s ∈ [S₀, S]}` is a compact set of momenta of the region.
-/

@[expose] public section
open Complex
open QED.Dirac
open QED.GradedProof.VP2
open QED.GradedProof.SE2 (canonVec dot_canonVec nullVec dot_nullVec reflect_sub_self)

namespace QED.GradedProof.RPi4

/-- **The covariant tensor** `A g^{μν} + B k^μ k^ν`. -/
noncomputable def gkTensor (A B : ℂ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  A * ((Minkowski.metric μ ν : ℝ) : ℂ) + B * ((k μ * k ν : ℝ) : ℂ)

theorem rAct_gkTensor {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (A B : ℂ) (k : Fin 4 → ℝ) :
    rAct a (gkTensor A B k) = gkTensor A B (reflect a k) := by
  funext μ ν
  have hl := (QED.TwoLoop.ReflCovariance.isSpinLift_reflect ha).lorentz_left μ ν
  have hm : ∀ ρ, ∑ α, reflectMatrix a ρ α * k α = reflect a k ρ := fun ρ => by
    rw [← reflectMatrix_mulVec]
    rfl
  have key : ∑ α, ∑ β, ((reflectMatrix a μ α : ℝ) : ℂ) * ((reflectMatrix a ν β : ℝ) : ℂ) *
      gkTensor A B k α β = A * ((∑ α, ∑ β, reflectMatrix a μ α * reflectMatrix a ν β *
        Minkowski.metric α β : ℝ) : ℂ) + B * (((∑ α, reflectMatrix a μ α * k α) *
        (∑ β, reflectMatrix a ν β * k β) : ℝ) : ℂ) := by
    rw [Finset.sum_mul_sum]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, gkTensor]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by push_cast; ring
  rw [rAct, key, hl, hm, hm]
  rfl

/-- **Transport of the covariant form along a reflection.** -/
theorem form_gk_reflect {T : ℝ} {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hcov : TCov T W)
    {a q : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (hq : -T ^ 2 < Minkowski.dot q q) {A B : ℂ}
    (hW : W q = gkTensor A B q) : W (reflect a q) = gkTensor A B (reflect a q) := by
  rw [hcov a ha q hq, hW, rAct_gkTensor ha]

section Canon

variable {T : ℝ} {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

/-- **At rest**, a covariant tensor is `A g + B c c` (no transversality). -/
theorem exists_gk_rest (hcov : TCov T W) {x : ℝ} (hx : x ≠ 0)
    (hc : -T ^ 2 < Minkowski.dot ![x, 0, 0, 0] ![x, 0, 0, 0]) :
    ∃ A B : ℂ, W ![x, 0, 0, 0] = gkTensor A B ![x, 0, 0, 0] := by
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
  refine ⟨W c 1 1, (W c 0 0 + W c 1 1) / ((x ^ 2 : ℝ) : ℂ),
    funext fun μ => funext fun ν => ?_⟩
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [hcdef] at h12 h13 off ⊢
  fin_cases μ <;> fin_cases ν <;>
    simp [gkTensor, Minkowski.metric, off, ← h12, ← h13]
  all_goals field_simp
  all_goals ring

/-- **Space-like**, a covariant tensor is `A g + B c c` (no transversality). -/
theorem exists_gk_space (hcov : TCov T W) {x : ℝ} (hx : x ≠ 0)
    (hc : -T ^ 2 < Minkowski.dot ![0, x, 0, 0] ![0, x, 0, 0]) :
    ∃ A B : ℂ, W ![0, x, 0, 0] = gkTensor A B ![0, x, 0, 0] := by
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
  refine ⟨W c 2 2, (W c 1 1 - W c 2 2) / ((x ^ 2 : ℝ) : ℂ),
    funext fun μ => funext fun ν => ?_⟩
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [hcdef] at h23 h02 off ⊢
  fin_cases μ <;> fin_cases ν <;>
    simp [gkTensor, Minkowski.metric, off, h02, ← h23]
  all_goals field_simp
  all_goals ring

/-- **Null**: at `n₀ = (1, 1, 0, 0)` a covariant tensor is `A g + B n₀ n₀` (no
transversality). -/
theorem exists_gk_null (hcov : TCov T W) (hc : -T ^ 2 < Minkowski.dot nullVec nullVec) :
    ∃ A B : ℂ, W nullVec = gkTensor A B nullVec := by
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
  have e02 := cov_fix hcov (a := ![1, 1, 1, 0]) (by norm_num [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq, nullVec]) hc 0 2
  have e20 := cov_fix hcov (a := ![1, 1, 1, 0]) (by norm_num [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq, nullVec]) hc 2 0
  have e12 := cov_fix hcov (a := ![1, 1, 1, 0]) (by norm_num [Minkowski.dot_eq])
    (by simp [Minkowski.dot_eq, nullVec]) hc 1 2
  rw [rAct_of_eq rm_111] at e02 e20 e12
  simp [Fin.sum_univ_four, z] at e02 e20 e12
  have h01 : W nullVec 0 1 = W nullVec 1 1 - W nullVec 2 2 := by
    linear_combination (3 / 2 : ℂ) * e02 - (1 / 2 : ℂ) * e20 - (3 / 2 : ℂ) * e12
  have h10 : W nullVec 1 0 = W nullVec 1 1 - W nullVec 2 2 := by
    linear_combination e02 - (3 / 2 : ℂ) * e12
  have h00 : W nullVec 0 0 = W nullVec 1 1 - 2 * W nullVec 2 2 := by
    linear_combination 2 * e02 - (1 / 2 : ℂ) * e20 - (5 / 2 : ℂ) * e12
  have hn0 : nullVec 0 = 1 := rfl
  have hn1 : nullVec 1 = 1 := rfl
  refine ⟨W nullVec 2 2, W nullVec 1 1 - W nullVec 2 2, funext fun μ => funext fun ν => ?_⟩
  fin_cases μ <;> fin_cases ν <;>
    simp [gkTensor, Minkowski.metric, hn0, hn1, hn2, hn3, z, h01, h10, h00, ← h23]
  all_goals ring

end Canon

/-! ### The projections of the covariant form -/

theorem trProj_gkTensor {k : Fin 4 → ℝ} (hs : Minkowski.dot k k ≠ 0) (A B : ℂ) :
    trProj k (gkTensor A B k) = -B := by
  have hs' : ((Minkowski.dot k k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  have e : ((Minkowski.dot k k : ℝ) : ℂ) = -(k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2 +
      (k 3 : ℂ) ^ 2 := by
    simp only [Minkowski.dot_eq]
    push_cast
    ring
  simp only [trProj, trWt, gkTensor, Fin.sum_univ_four, Minkowski.lower_eq]
  push_cast
  simp only [e]
  rw [e] at hs'
  simp [Minkowski.metric]
  field_simp
  ring

theorem nProj_gkTensor (A B : ℂ) : nProj (gkTensor A B nullVec) = -B := by
  simp [nProj, gkTensor, Minkowski.metric, nullVec]

/-! ### The tilted vector -/

/-- **The tilted vector** `(√(2c² - s), 0, c, c)` of square `s`. -/
noncomputable def tiltVec (c s : ℝ) : Fin 4 → ℝ := ![Real.sqrt (2 * c ^ 2 - s), 0, c, c]

theorem dot_tiltVec {c s : ℝ} (hs : s ≤ 2 * c ^ 2) :
    Minkowski.dot (tiltVec c s) (tiltVec c s) = s := by
  simp only [tiltVec, Minkowski.dot_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [Real.mul_self_sqrt (by linarith)]
  ring

theorem gkTensor_tilt (A B : ℂ) (c s : ℝ) :
    gkTensor A B (tiltVec c s) 2 3 = B * ((c ^ 2 : ℝ) : ℂ) := by
  simp [gkTensor, tiltVec, Minkowski.metric, sq]

/-- The vector read by `projS` at `s`. -/
theorem dot_sub_tiltVec_ne {c s : ℝ} (hc : 0 < c) (hs : s < 2 * c ^ 2) :
    Minkowski.dot ((if s = 0 then nullVec else canonVec s) - tiltVec c s)
      ((if s = 0 then nullVec else canonVec s) - tiltVec c s) ≠ 0 := by
  have hv := Real.sqrt_nonneg (2 * c ^ 2 - s)
  have hv2 := Real.sq_sqrt (show 0 ≤ 2 * c ^ 2 - s by linarith)
  split_ifs with h0
  · subst h0
    simp only [tiltVec, nullVec, Minkowski.dot_eq, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    nlinarith
  · unfold canonVec
    split_ifs with h1 h2
    · have hu := Real.sqrt_pos.mpr (show 0 < -s by linarith)
      have hu2 := Real.sq_sqrt (show 0 ≤ -s by linarith)
      simp only [tiltVec, Minkowski.dot_eq, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons]
      have hlt : Real.sqrt (-s) < Real.sqrt (2 * c ^ 2 - s) :=
        Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
      nlinarith
    · have hu2 := Real.sq_sqrt h2.le
      simp only [tiltVec, Minkowski.dot_eq, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons]
      nlinarith
    · exact absurd (le_antisymm (not_lt.mp h2) (not_lt.mp h1)) h0

/-- **The projection at `s` of a covariant tensor is one entry at the tilted vector**:
`projS W s = -W(k'(s))²³ / c²`, `k'(s) = (√(2c² - s), 0, c, c)`, for every `s` of the region
below `2c²` (no division by `s`). -/
theorem projS_eq_tilt {T : ℝ} {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hcov : TCov T W)
    {c s : ℝ} (hc : 0 < c) (hs : -T ^ 2 < s) (hs2 : s < 2 * c ^ 2) :
    projS W s = -W (tiltVec c s) 2 3 / ((c ^ 2 : ℝ) : ℂ) := by
  set k₀ : Fin 4 → ℝ := if s = 0 then nullVec else canonVec s with hk₀
  have hd0 : Minkowski.dot k₀ k₀ = s := by
    rw [hk₀]
    split_ifs with h
    · rw [dot_nullVec, h]
    · exact dot_canonVec s
  obtain ⟨A, B, hW, hP⟩ : ∃ A B : ℂ, W k₀ = gkTensor A B k₀ ∧ projS W s = -B := by
    unfold projS
    rw [hk₀] at *
    split_ifs with h0
    · obtain ⟨A, B, hAB⟩ := exists_gk_null hcov (by rw [dot_nullVec]; rw [h0] at hs; exact hs)
      exact ⟨A, B, hAB, by rw [hAB, nProj_gkTensor]⟩
    · have hc' : -T ^ 2 < Minkowski.dot (canonVec s) (canonVec s) := by rwa [dot_canonVec]
      have hex : ∃ A B : ℂ, W (canonVec s) = gkTensor A B (canonVec s) := by
        unfold canonVec at hc' ⊢
        split_ifs at hc' ⊢ with h1 h2
        · exact exists_gk_rest hcov (Real.sqrt_ne_zero'.mpr (by linarith)) hc'
        · exact exists_gk_space hcov (Real.sqrt_ne_zero'.mpr h2) hc'
        · exact absurd (le_antisymm (not_lt.mp h2) (not_lt.mp h1)) h0
      obtain ⟨A, B, hAB⟩ := hex
      exact ⟨A, B, hAB, by rw [hAB, trProj_gkTensor (by rw [dot_canonVec]; exact h0)]⟩
  have hne := dot_sub_tiltVec_ne hc hs2
  rw [← hk₀] at hne
  have hrefl := reflect_sub_self (hd0.trans (dot_tiltVec hs2.le).symm) hne
  have hT := form_gk_reflect hcov hne (hd0 ▸ hs) hW
  rw [hrefl] at hT
  have hc2 : ((c ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [hP, hT, gkTensor_tilt]
  field_simp

/-! ### The class sum at the tilted vector -/

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

omit [DecidableEq F] in
/-- The class limit at a photon pair is covariant. -/
theorem tcov_wV {T e a b : ℝ} {A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {base : Fin 5 → Fin 2 → ℤ} {c : Fin 5 → ℝ} (hV : VPJ T (vSumF Φ e A base c a b)) :
    TCov T (wV Φ e A base c a b) :=
  tcov_limT hV.hasVPLim

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- The limit of the weighted block is covariant. -/
theorem tcov_fLim (P : QED.WickModel.Params) (he : P.e ≠ 0) (δ : F → ℝ) :
    TCov (2 * m₀) (fLim Φ rep P.e δ) :=
  two_mul m₀ ▸ tcov_limT (vpf_dBlockD Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ).hasVPLim

/-- **The class sum at the photon pair `(a, b)` through the tilted vector**: for `c > 0` and
`-4m₀² < s < 2c²`, `Q(a, b; s) = -(i/c²) ∑_X W_X(a, b; k'(s))²³`. -/
theorem qPair_eq_tilt (P : QED.WickModel.Params) (he : P.e ≠ 0) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) {c s : ℝ} (hc : 0 < c) (hs : -(4 * m₀ ^ 2) < s) (hs2 : s < 2 * c ^ 2) :
    qPair Φ rep P.e a b s = -I / ((c ^ 2 : ℝ) : ℂ) *
      (wV Φ P.e aVA baseVA cVA a b (tiltVec c s) 2 3 +
        wV Φ P.e aVB baseVB cVB a b (tiltVec c s) 2 3 +
        wV Φ P.e aVC baseVC cVC a b (tiltVec c s) 2 3 +
        fLim Φ rep P.e (fun g => ctPair P.e (Φ.mass g) a b) (tiltVec c s) 2 3) := by
  have hs' : -(2 * m₀) ^ 2 < s := by linarith [show (2 * m₀) ^ 2 = 4 * m₀ ^ 2 by ring]
  rw [qPair,
    projS_eq_tilt (tcov_wV Φ (vpj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb)) hc hs' hs2,
    projS_eq_tilt (tcov_wV Φ (vpj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb)) hc hs' hs2,
    projS_eq_tilt (tcov_wV Φ (vpj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb)) hc hs' hs2,
    projS_eq_tilt (tcov_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _) hc hs' hs2]
  ring

end Classes

end QED.GradedProof.RPi4

end
