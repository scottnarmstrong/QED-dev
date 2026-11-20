/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# (R-Π₄) step L6d2: families uniformly Lipschitz at the face

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. The face lemma
`norm_face_sub_le` needs `‖g(ρ, σ) - g(0, σ)‖ ≤ ρ B₁(σ)` for the rescaled face integrand, with
constants uniform in the remaining integration variables. The rescaled integrand is built from
rational functions of `ρ` by sums, products and inverses, so the bound is proved once for the
building blocks and carried through by closure lemmas:

* `UnifLip ρ₀ F`: the family `F i` is bounded on `[0, ρ₀]` and satisfies
  `‖F i ρ - F i 0‖ ≤ L ρ` there, with constants `B`, `L` independent of `i`;
* closure under `const`, `const_bdd`, `id`, `add`, `neg`, `sub`, `mul`, `sum`, `pow`, `inv`
  (with a uniform lower bound), `comp_index` (reindexing).
-/

@[expose] public section

namespace QED.GradedProof.RPi4

/-- **A family uniformly bounded and uniformly Lipschitz at `0` on `[0, ρ₀]`.** -/
def UnifLip {ι : Type*} (ρ₀ : ℝ) (F : ι → ℝ → ℂ) : Prop :=
  ∃ B L : ℝ, ∀ i, ∀ ρ, 0 ≤ ρ → ρ ≤ ρ₀ → ‖F i ρ‖ ≤ B ∧ ‖F i ρ - F i 0‖ ≤ L * ρ

namespace UnifLip

variable {ι κ : Type*} {ρ₀ : ℝ} {F G : ι → ℝ → ℂ}

theorem const_bdd (c : ι → ℂ) {B : ℝ} (hc : ∀ i, ‖c i‖ ≤ B) :
    UnifLip ρ₀ fun i (_ : ℝ) => c i :=
  ⟨B, 0, fun i ρ hρ _ => ⟨hc i, by simp⟩⟩

theorem const (c : ℂ) : UnifLip ρ₀ fun (_ : ι) (_ : ℝ) => c :=
  const_bdd (fun _ => c) fun _ => le_rfl

theorem id : UnifLip ρ₀ fun (_ : ι) (ρ : ℝ) => (ρ : ℂ) :=
  ⟨|ρ₀|, 1, fun _ ρ hρ hρ' => ⟨by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
    exact hρ'.trans (le_abs_self _), by
    simp only [Complex.ofReal_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ, one_mul, le_refl]⟩⟩

theorem comp_index (hF : UnifLip ρ₀ F) (f : κ → ι) : UnifLip ρ₀ fun j => F (f j) := by
  obtain ⟨B, L, h⟩ := hF
  exact ⟨B, L, fun j => h (f j)⟩

theorem add (hF : UnifLip ρ₀ F) (hG : UnifLip ρ₀ G) : UnifLip ρ₀ fun i ρ => F i ρ + G i ρ := by
  obtain ⟨B, L, h⟩ := hF
  obtain ⟨B', L', h'⟩ := hG
  refine ⟨B + B', L + L', fun i ρ hρ hρ' => ⟨?_, ?_⟩⟩
  · exact (norm_add_le _ _).trans (add_le_add (h i ρ hρ hρ').1 (h' i ρ hρ hρ').1)
  · have e : F i ρ + G i ρ - (F i 0 + G i 0) = (F i ρ - F i 0) + (G i ρ - G i 0) := by ring
    rw [e, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h i ρ hρ hρ').2 (h' i ρ hρ hρ').2)

theorem neg (hF : UnifLip ρ₀ F) : UnifLip ρ₀ fun i ρ => -F i ρ := by
  obtain ⟨B, L, h⟩ := hF
  refine ⟨B, L, fun i ρ hρ hρ' => ⟨by rw [norm_neg]; exact (h i ρ hρ hρ').1, ?_⟩⟩
  rw [← neg_sub', norm_neg]
  exact (h i ρ hρ hρ').2

theorem sub (hF : UnifLip ρ₀ F) (hG : UnifLip ρ₀ G) : UnifLip ρ₀ fun i ρ => F i ρ - G i ρ := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem mul (hF : UnifLip ρ₀ F) (hG : UnifLip ρ₀ G) : UnifLip ρ₀ fun i ρ => F i ρ * G i ρ := by
  obtain ⟨B, L, h⟩ := hF
  obtain ⟨B', L', h'⟩ := hG
  refine ⟨B * B', B * L' + L * B', fun i ρ hρ hρ' => ⟨?_, ?_⟩⟩
  · have h1 := h i ρ hρ hρ'
    have h2 := h' i ρ hρ hρ'
    rw [norm_mul]
    exact mul_le_mul h1.1 h2.1 (norm_nonneg _) ((norm_nonneg _).trans h1.1)
  · have h1 := h i ρ hρ hρ'
    have h2 := h' i ρ hρ hρ'
    have h0 := h' i 0 le_rfl (hρ.trans hρ')
    have e : F i ρ * G i ρ - F i 0 * G i 0 =
        F i ρ * (G i ρ - G i 0) + (F i ρ - F i 0) * G i 0 := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hB : 0 ≤ B := (norm_nonneg _).trans h1.1
    have hL' : 0 ≤ L' * ρ := (norm_nonneg _).trans h2.2
    have hB' : 0 ≤ B' := (norm_nonneg _).trans h0.1
    calc ‖F i ρ‖ * ‖G i ρ - G i 0‖ + ‖F i ρ - F i 0‖ * ‖G i 0‖ ≤
          B * (L' * ρ) + (L * ρ) * B' :=
        add_le_add (mul_le_mul h1.1 h2.2 (norm_nonneg _) hB)
          (mul_le_mul h1.2 h0.1 (norm_nonneg _) ((norm_nonneg _).trans h1.2))
      _ = (B * L' + L * B') * ρ := by ring

theorem sum (s : Finset κ) {F : κ → ι → ℝ → ℂ} (h : ∀ k ∈ s, UnifLip ρ₀ (F k)) :
    UnifLip ρ₀ fun i ρ => ∑ k ∈ s, F k i ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (ι := ι) (ρ₀ := ρ₀) 0)
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (h k (Finset.mem_insert_self k s)).add
      (ih fun k' hk' => h k' (Finset.mem_insert_of_mem hk'))

theorem pow (hF : UnifLip ρ₀ F) (n : ℕ) : UnifLip ρ₀ fun i ρ => F i ρ ^ n := by
  induction n with
  | zero => simpa using (const (ι := ι) (ρ₀ := ρ₀) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hF

/-- **Inverse of a family bounded below.** -/
theorem inv (hF : UnifLip ρ₀ F) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ i ρ, 0 ≤ ρ → ρ ≤ ρ₀ → c ≤ ‖F i ρ‖) : UnifLip ρ₀ fun i ρ => (F i ρ)⁻¹ := by
  obtain ⟨B, L, h⟩ := hF
  refine ⟨c⁻¹, L / c ^ 2, fun i ρ hρ hρ' => ⟨?_, ?_⟩⟩
  · rw [norm_inv]
    exact inv_anti₀ hc (hlow i ρ hρ hρ')
  · have ha := hlow i ρ hρ hρ'
    have hb := hlow i 0 le_rfl (hρ.trans hρ')
    have ha0 : F i ρ ≠ 0 := norm_pos_iff.mp (hc.trans_le ha)
    have hb0 : F i 0 ≠ 0 := norm_pos_iff.mp (hc.trans_le hb)
    have e : (F i ρ)⁻¹ - (F i 0)⁻¹ = (F i 0 - F i ρ) / (F i ρ * F i 0) := by
      field_simp
    rw [e, norm_div, norm_mul, ← norm_neg (F i 0 - F i ρ), neg_sub]
    have hd : c ^ 2 ≤ ‖F i ρ‖ * ‖F i 0‖ := by
      rw [sq]; exact mul_le_mul ha hb hc.le (hc.le.trans ha)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖F i ρ‖ * ‖F i 0‖)]
    calc ‖F i ρ - F i 0‖ ≤ L * ρ := (h i ρ hρ hρ').2
      _ = L / c ^ 2 * ρ * c ^ 2 := by field_simp
      _ ≤ L / c ^ 2 * ρ * (‖F i ρ‖ * ‖F i 0‖) := by
        have : 0 ≤ L / c ^ 2 * ρ := by
          have hL : 0 ≤ L * ρ := (norm_nonneg _).trans (h i ρ hρ hρ').2
          have : L / c ^ 2 * ρ = L * ρ / c ^ 2 := by ring
          rw [this]; positivity
        exact mul_le_mul_of_nonneg_left hd this

end UnifLip

end QED.GradedProof.RPi4

end
