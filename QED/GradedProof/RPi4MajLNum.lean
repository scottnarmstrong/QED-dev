/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VNum
public import QED.GradedProof.RPi4MajFlow
public import QED.GradedProof.RPi4LightBd
public import QED.Integration.SymanzikIntegrabilityClasses

/-!
# (R-Π₄) step L10, two loops: the class numerators along the ray and at the saddle

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.IR). The
coefficients `E₀`, `E₂` of the class numerators `QED.GradedProof.VP2.vNum` are homogeneous of
degrees four and two in `(k, ℓ)`, and `E₀` is multilinear in the four fermion momenta. At the
saddle of the loop momenta the fermion line `l` carries `τ_l k` (`τ_l` the flow
`QED.GradedProof.RPi4.majFlow`), so `E₀(k, -S) = τ₀ τ₁ τ₂ τ₃ E₀⁰(k)`.

* `maj_fm_smul`, `maj_vE0_smul`, `maj_vE2_smul`, `maj_vNumE0_smul`, `maj_vNumE2_smul`:
  homogeneity;
* `maj_fm_shift`: the fermion momenta at the saddle are `τ_l k`;
* `maj_vNumE0_flow`: `E₀` at fermion momenta `t_l k` is `t₀ t₁ t₂ t₃ E₀⁰(k)`;
* `maj_exists_abs_flow_le`: the flows are bounded on the simplex;
* `MajIntCrit`, `maj_crit_of_int`: the integer form (decidable) of the criterion of
  `QED.GradedProof.RPi4.maj_integrableOn_weight`.
-/

@[expose] public section

open Complex Matrix

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.Integration.TwoLoop QED.TwoLoop.Bridge

section Hom

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

theorem maj_fm_smul (k : Fin 4 → ℝ) (l : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) {r : ℝ} (hr : r ≠ 0) :
    fm base (ppc c (r • k)) l ℓ = r • fm base (ppc c k) l (r⁻¹ • ℓ) := by
  funext μ
  simp only [lineMomentum, castLoopMatrix, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
  congr 1
  · exact Finset.sum_congr rfl fun s _ => by field_simp
  · ring

theorem maj_eN_smul (t : ℝ) (p : Fin 4 → ℝ) :
    electronNumerator 0 (t • p) = (t : ℂ) • electronNumerator 0 p := by
  simp [electronNumerator, QED.Dirac.slash_smul]

/-- **`E₀` is multilinear in the four momenta.** -/
theorem maj_vE0_smul (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (t : Fin 4 → ℝ)
    (y : Fin 4 → Fin 4 → ℝ) :
    vE0 A (fun l => t l • y l) = ((t 0 * t 1 * t 2 * t 3 : ℝ) : ℂ) * vE0 A y := by
  simp only [vE0, maj_eN_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

theorem maj_vE2_smul (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (r : ℝ) (y : Fin 4 → Fin 4 → ℝ) :
    vE2 A (fun l => r • y l) = ((r ^ 2 : ℝ) : ℂ) * vE2 A y := by
  simp only [vE2, maj_eN_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

variable (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)

theorem maj_vNumE0_smul (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) {r : ℝ} (hr : r ≠ 0)
    (a b : Fin 4) :
    vNumE0 e mγ Λ A base c (r • k) ℓ a b =
      ((r : ℂ) ^ 2) ^ 2 * vNumE0 e mγ Λ A base c k (r⁻¹ • ℓ) a b := by
  simp only [vNumE0, maj_fm_smul base c k _ ℓ hr]
  simp only [maj_vE0_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

theorem maj_vNumE2_smul (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) {r : ℝ} (hr : r ≠ 0)
    (a b : Fin 4) :
    vNumE2 e mγ Λ A base c (r • k) ℓ a b =
      (r : ℂ) ^ 2 * vNumE2 e mγ Λ A base c k (r⁻¹ • ℓ) a b := by
  simp only [vNumE2, maj_fm_smul base c k _ ℓ hr]
  simp only [maj_vE2_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

/-- **`E₀` at fermion momenta `t_l k`**: `t₀ t₁ t₂ t₃ E₀⁰(k)`. -/
theorem maj_vNumE0_flow (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (t : Fin 4 → ℝ)
    (ht : ∀ l, fm base (ppc c k) l ℓ = t l • k) (a b : Fin 4) :
    vNumE0 e mγ Λ A base c k ℓ a b = ((t 0 * t 1 * t 2 * t 3 : ℝ) : ℂ) *
      ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * vE0 (A a b ρ σ) (fun _ => k) := by
  simp only [vNumE0, ht, maj_vE0_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The fermion momenta at the saddle**: line `l'` of a shape with row `l` carries
`τ_{l'} k`. -/
theorem maj_fm_shift {n : ℕ} (sh : Fin (n + 1) → Fin 5) (z : Fin (n + 1) → ℝ)
    (k : Fin 4 → ℝ) {l' : Fin (n + 1)} {l : Fin 4} (hl : sh l' = l.castSucc) :
    fm base (ppc c k) l (-QED.Integration.TwoLoop.loopShift (castLoopMatrix fun i => base (sh i))
      (fun i => c (sh i) • k) z) =
      majFlow (castLoopMatrix fun i => base (sh i)) z (fun i => c (sh i)) l' • k := by
  funext μ
  have e : coefVec (castLoopMatrix fun i => base (sh i)) z (fun i => c (sh i) * k μ) =
      k μ • coefVec (castLoopMatrix fun i => base (sh i)) z fun i => c (sh i) := by
    funext t
    simp only [coefVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [lineMomentum, Pi.neg_apply, loopShift_eq_mulVec, Pi.smul_apply, smul_eq_mul,
    majFlow, castLoopMatrix, hl]
  rw [e, mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [add_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

end Hom

/-- **The flows are bounded** on `z ≥ 0` with `U ≠ 0`. -/
theorem maj_exists_abs_flow_le {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → symanzikU α z ≠ 0 → ∀ l,
      |majFlow α z q l| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_mulVec_coefVec_le α q
  refine ⟨∑ l, (∑ s, |α l s| * |C| + |q l|), by positivity, fun z hz hU l => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun l => ∑ s, |α l s| * |C| + |q l|)
    (fun _ _ => by positivity) (Finset.mem_univ l))
  unfold majFlow
  refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [abs_mul, Pi.neg_apply, abs_neg]
  exact mul_le_mul_of_nonneg_left ((hC z hz hU s).trans (le_abs_self C)) (abs_nonneg _)

/-! ### The integer criterion -/

/-- Every line `l` has three lines `t ∉ {i, j}` with `det(a_l, a_t) ≠ 0` (integer rows). -/
def MajIntCrit {n : ℕ} (a : Fin (n + 1) → Fin 2 → ℤ) (i j : Fin (n + 1)) : Prop :=
  ∀ l, 3 ≤ (Finset.univ.filter fun t => t ≠ i ∧ t ≠ j ∧ a l 0 * a t 1 - a l 1 * a t 0 ≠ 0).card

instance {n : ℕ} (a : Fin (n + 1) → Fin 2 → ℤ) (i j : Fin (n + 1)) :
    Decidable (MajIntCrit a i j) :=
  inferInstanceAs (Decidable (∀ l, 3 ≤ (Finset.univ.filter fun t =>
    t ≠ i ∧ t ≠ j ∧ a l 0 * a t 1 - a l 1 * a t 0 ≠ 0).card))

theorem maj_crit_of_int {n : ℕ} {a : Fin (n + 1) → Fin 2 → ℤ} {i j : Fin (n + 1)}
    (h : MajIntCrit a i j) (l : Fin (n + 1)) :
    ∃ T : Finset (Fin (n + 1)), T.card = 3 ∧ i ∉ T ∧ j ∉ T ∧
      ∀ t ∈ T, pairDet (castLoopMatrix a) l t ≠ 0 := by
  obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq (h l)
  refine ⟨T, hc, fun hi => (Finset.mem_filter.mp (hT hi)).2.1 rfl,
    fun hj => (Finset.mem_filter.mp (hT hj)).2.2.1 rfl, fun t ht => ?_⟩
  have h3 := (Finset.mem_filter.mp (hT ht)).2.2.2
  simp only [pairDet, castLoopMatrix]
  exact_mod_cast h3

end QED.GradedProof.RPi4

end
