/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Block

/-!
# (X₀): the block-sum expansion with abstract line momenta and term hypotheses

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the two-loop
contractions of `TwoLoopClosedGoal` whose closed fermion loop shares lines with the other loop.
This is `jointEnergyFirstIntegrable_blockSum` with the loop lines `l : L` carrying arbitrary
momenta `k_l(ℓ)`, `ℓ` in any number `n` of loop momenta, and with the (T₉′) of the individual
terms of the expansion as hypotheses (`jointEnergyFirstIntegrable_blockSumGen`). With
`a_l = D₀(k_l)⁻¹`, `g_l = D_M(k_l)⁻¹` and `A = ∏ a_l`, the terms are

* `E₂ ∏_l g_l` (the loop lines at mass `M`);
* `E₁ A a_l` (one extra massless line parallel to `l`);
* `E_i A a_l g_l`, `i = 0, 1` (two extra lines parallel to `l`);
* `E_i A ∏_{l ∈ S} g_l`, `i = 0, 1`, `|S| ≥ 2` (extra lines parallel to the lines of `S`);

the parts of order `s⁰` and `s¹` of the flavour sum vanish by the block conditions.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero)
open QED.TwoLoop.ClassIntegrable (jointEnergyFirstIntegrable_add)

variable {F : Type} [Fintype F] [DecidableEq F]

/-- (T₉′) for a weighted finite sum, the weight outside. -/
theorem jointEnergyFirstIntegrable_mul_sum {n : ℕ} {ι : Type*} (U : Finset ι) (z : ℂ)
    (E : (Fin n → Fin 4 → ℝ) → ℂ) (X : ι → (Fin n → Fin 4 → ℝ) → ℂ)
    (h : ∀ i ∈ U, QED.TwoLoop.jointEnergyFirstIntegrable n fun ℓ => z * (E ℓ * X i ℓ)) :
    QED.TwoLoop.jointEnergyFirstIntegrable n fun ℓ => z * (E ℓ * ∑ i ∈ U, X i ℓ) := by
  simp only [Finset.mul_sum]
  exact jointEnergyFirstIntegrable_sum' U h

/-- **(T₉′) of a block-summed integrand with an even numerator**, from (T₉′) of the terms of its
mass expansion; any number of loop momenta, any masses. -/
theorem jointEnergyFirstIntegrable_blockSumGen (Φ : Lepton.Flavors F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    {n : ℕ} {L : Type*} [Fintype L] [DecidableEq L]
    (k : L → (Fin n → Fin 4 → ℝ) → Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε)
    (E₀ E₁ E₂ : F → (Fin n → Fin 4 → ℝ) → ℂ)
    (T₂ : ∀ b (M : ℝ) (z : ℂ), QED.TwoLoop.jointEnergyFirstIntegrable n fun ℓ =>
      z * (E₂ b ℓ * ∏ l, (propDenom M ε (k l ℓ))⁻¹))
    (T₁ : ∀ b (z : ℂ) (l : L), QED.TwoLoop.jointEnergyFirstIntegrable n fun ℓ =>
      z * (E₁ b ℓ * ((∏ l', (propDenom 0 ε (k l' ℓ))⁻¹) * (propDenom 0 ε (k l ℓ))⁻¹)))
    (T₀₁ : ∀ E ∈ [E₀, E₁], ∀ b (M : ℝ) (z : ℂ) (l : L),
      QED.TwoLoop.jointEnergyFirstIntegrable n fun ℓ =>
        z * (E b ℓ * ((∏ l', (propDenom 0 ε (k l' ℓ))⁻¹) * (propDenom 0 ε (k l ℓ))⁻¹ *
          (propDenom M ε (k l ℓ))⁻¹)))
    (TS : ∀ E ∈ [E₀, E₁], ∀ b (M : ℝ) (z : ℂ) (S : Finset L), 2 ≤ S.card →
      QED.TwoLoop.jointEnergyFirstIntegrable n fun ℓ =>
        z * (E b ℓ * ((∏ l', (propDenom 0 ε (k l' ℓ))⁻¹) *
          ∏ l ∈ S, (propDenom M ε (k l ℓ))⁻¹))) :
    QED.TwoLoop.jointEnergyFirstIntegrable n fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * ((E₀ (rep f) ℓ + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) ℓ +
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * E₂ (rep f) ℓ) * ∏ l, (propDenom (Φ.mass f) ε (k l ℓ))⁻¹) := by
  classical
  -- notation
  set a : L → (Fin n → Fin 4 → ℝ) → ℂ := fun l ℓ => (propDenom 0 ε (k l ℓ))⁻¹ with ha
  set g : ℝ → L → (Fin n → Fin 4 → ℝ) → ℂ := fun M l ℓ => (propDenom M ε (k l ℓ))⁻¹ with hg
  set A : (Fin n → Fin 4 → ℝ) → ℂ := fun ℓ => ∏ l, a l ℓ with hA
  have hrel : ∀ M l ℓ, g M l ℓ = a l ℓ - (M : ℂ) ^ 2 * a l ℓ * g M l ℓ := fun M l ℓ => by
    have h0 := propDenom_ne_zero (M := 0) hε.ne' (k l ℓ)
    have hM := propDenom_ne_zero (M := M) hε.ne' (k l ℓ)
    have hD : propDenom M ε (k l ℓ) = propDenom 0 ε (k l ℓ) + (M : ℂ) ^ 2 := by
      simp only [propDenom]; push_cast; ring
    simp only [hg, ha]
    field_simp
    rw [hD]
    ring
  -- the remainder `X = ∏ g - A + s ∑ A a`
  have hX : ∀ M ℓ, ∏ l, g M l ℓ - A ℓ + (M : ℂ) ^ 2 * ∑ l, A ℓ * a l ℓ =
      (M : ℂ) ^ 2 * (M : ℂ) ^ 2 * ∑ l, A ℓ * a l ℓ * g M l ℓ +
        ∑ S ∈ (Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card),
          (-(M : ℂ) ^ 2) ^ S.card * (A ℓ * ∏ l ∈ S, g M l ℓ) := fun M ℓ => by
    rw [prod_inv_expand _ (fun l => a l ℓ) (fun l => g M l ℓ) _ fun l => hrel M l ℓ,
      sum_powerset_split]
    have e1 : ∑ l, (-(M : ℂ) ^ 2) ^ ({l} : Finset L).card *
        ((∏ l, a l ℓ) * ∏ i ∈ ({l} : Finset L), g M i ℓ) =
        ∑ l, (-(M : ℂ) ^ 2 * (A ℓ * a l ℓ) + (M : ℂ) ^ 2 * (M : ℂ) ^ 2 *
          (A ℓ * a l ℓ * g M l ℓ)) :=
      Finset.sum_congr rfl fun l _ => by
        rw [Finset.card_singleton, Finset.prod_singleton, pow_one]
        linear_combination (-(M : ℂ) ^ 2 * A ℓ) * hrel M l ℓ
    rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one, one_mul]
    simp only [hA, Finset.mul_sum]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  -- the integrand as the flavour sum of the remainders
  have hkey : ∀ ℓ : Fin n → Fin 4 → ℝ,
      ∑ f, (Φ.coeff f : ℂ) * ((E₀ (rep f) ℓ + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) ℓ +
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * E₂ (rep f) ℓ) * ∏ l, (propDenom (Φ.mass f) ε (k l ℓ))⁻¹) =
      ∑ f, (Φ.coeff f : ℂ) * (((Φ.mass f : ℂ) ^ 2) ^ 2 * (E₂ (rep f) ℓ *
          ∏ l, g (Φ.mass f) l ℓ) -
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * (E₁ (rep f) ℓ * ∑ l, A ℓ * a l ℓ) +
        (E₀ (rep f) ℓ + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) ℓ) *
          ((Φ.mass f : ℂ) ^ 2 * (Φ.mass f : ℂ) ^ 2 * ∑ l, A ℓ * a l ℓ * g (Φ.mass f) l ℓ +
          ∑ S ∈ (Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card),
            (-(Φ.mass f : ℂ) ^ 2) ^ S.card * (A ℓ * ∏ l ∈ S, g (Φ.mass f) l ℓ))) := by
    intro ℓ
    have hz := VP2.sum_block_affine_eq_zero Φ rep hrep hPV₁ hPV₂ 1 0 (fun b => E₀ b ℓ * A ℓ)
    have hz' := VP2.sum_block_affine_eq_zero Φ rep hrep hPV₁ hPV₂ 0 (-1)
      (fun b => E₀ b ℓ * ∑ l, A ℓ * a l ℓ)
    have hz'' := VP2.sum_block_affine_eq_zero Φ rep hrep hPV₁ hPV₂ 0 1 (fun b => E₁ b ℓ * A ℓ)
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    have hsum : ∑ f, ((Φ.coeff f : ℂ) * ((E₀ (rep f) ℓ + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) ℓ +
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * E₂ (rep f) ℓ) * ∏ l, (propDenom (Φ.mass f) ε (k l ℓ))⁻¹) -
      (Φ.coeff f : ℂ) * (((Φ.mass f : ℂ) ^ 2) ^ 2 * (E₂ (rep f) ℓ * ∏ l, g (Φ.mass f) l ℓ) -
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * (E₁ (rep f) ℓ * ∑ l, A ℓ * a l ℓ) +
        (E₀ (rep f) ℓ + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) ℓ) *
          ((Φ.mass f : ℂ) ^ 2 * (Φ.mass f : ℂ) ^ 2 * ∑ l, A ℓ * a l ℓ * g (Φ.mass f) l ℓ +
          ∑ S ∈ (Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card),
            (-(Φ.mass f : ℂ) ^ 2) ^ S.card * (A ℓ * ∏ l ∈ S, g (Φ.mass f) l ℓ)))) =
      ∑ f, (Φ.coeff f : ℂ) * ((1 + 0 * (Φ.mass f : ℂ) ^ 2) * (E₀ (rep f) ℓ * A ℓ)) +
      ∑ f, (Φ.coeff f : ℂ) * ((0 + -1 * (Φ.mass f : ℂ) ^ 2) *
        (E₀ (rep f) ℓ * ∑ l, A ℓ * a l ℓ)) +
      ∑ f, (Φ.coeff f : ℂ) * ((0 + 1 * (Φ.mass f : ℂ) ^ 2) * (E₁ (rep f) ℓ * A ℓ)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      have hXf := hX (Φ.mass f) ℓ
      rw [show (∏ l, (propDenom (Φ.mass f) ε (k l ℓ))⁻¹) = ∏ l, g (Φ.mass f) l ℓ from rfl]
      linear_combination (Φ.coeff f : ℂ) * (E₀ (rep f) ℓ + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) ℓ) *
        hXf
    rw [hsum, hz, hz', hz'']
    ring
  simp only [hkey]
  refine jointEnergyFirstIntegrable_sum' _ fun f _ => ?_
  set M := Φ.mass f
  set b := rep f
  set s : ℂ := (M : ℂ) ^ 2
  have hE₀ : E₀ ∈ [E₀, E₁] := List.mem_cons_self
  have hE₁ : E₁ ∈ [E₀, E₁] := List.mem_cons_of_mem _ List.mem_cons_self
  have T1 := T₂ b M ((Φ.coeff f : ℂ) * s ^ 2)
  have T2 := jointEnergyFirstIntegrable_mul_sum Finset.univ (-(Φ.coeff f : ℂ) * s ^ 2) (E₁ b)
    (fun l ℓ => A ℓ * a l ℓ) fun l _ => T₁ b _ l
  have T3 := jointEnergyFirstIntegrable_mul_sum Finset.univ ((Φ.coeff f : ℂ) * s * s) (E₀ b)
    (fun l ℓ => A ℓ * a l ℓ * g M l ℓ) fun l _ => T₀₁ E₀ hE₀ b M _ l
  have T4 := jointEnergyFirstIntegrable_mul_sum Finset.univ ((Φ.coeff f : ℂ) * s * s * s) (E₁ b)
    (fun l ℓ => A ℓ * a l ℓ * g M l ℓ) fun l _ => T₀₁ E₁ hE₁ b M _ l
  have T5 := jointEnergyFirstIntegrable_mul_sum
    ((Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card))
    (Φ.coeff f : ℂ) (E₀ b) (fun S ℓ => (-s) ^ S.card * (A ℓ * ∏ l ∈ S, g M l ℓ))
    fun S hS => by
      have := TS E₀ hE₀ b M ((Φ.coeff f : ℂ) * (-s) ^ S.card) S (Finset.mem_filter.mp hS).2
      refine (congrArg _ (funext fun ℓ => ?_)).mp this
      ring
  have T6 := jointEnergyFirstIntegrable_mul_sum
    ((Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card))
    ((Φ.coeff f : ℂ) * s) (E₁ b) (fun S ℓ => (-s) ^ S.card * (A ℓ * ∏ l ∈ S, g M l ℓ))
    fun S hS => by
      have := TS E₁ hE₁ b M ((Φ.coeff f : ℂ) * s * (-s) ^ S.card) S (Finset.mem_filter.mp hS).2
      refine (congrArg _ (funext fun ℓ => ?_)).mp this
      ring
  have hall := jointEnergyFirstIntegrable_add T1 (jointEnergyFirstIntegrable_add T2
    (jointEnergyFirstIntegrable_add T3 (jointEnergyFirstIntegrable_add T4
      (jointEnergyFirstIntegrable_add T5 T6))))
  refine (congrArg _ (funext fun ℓ => ?_)).mp hall
  ring

end QED.GradedProof.X0

end
