/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0AffPoly
public import QED.GradedProof.X0Sep
public import QED.GradedProof.VP2Loop
public import QED.TwoLoop.ClassIntegrableVP

/-!
# (X₀): a block-summed one-loop integrand with an even numerator, at any masses

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the closed
fermion loops at one loop (bubbles and tadpoles). A closed loop of flavour `f` contributes
`c_f N_{rep f}(M_f², ℓ) ∏_l D_{M_f}(c_l ℓ + q_l)⁻¹` with `N_b(s, k) = E₀ + s E₁ + s² E₂`.
If the block conditions hold, the flavour sum satisfies (T₉′) for `ε > 0` and ANY masses
(`jointEnergyFirstIntegrable_blockSum`), under the counts `4 + deg E₀ < 2 (r + 2)`,
`4 + deg E₁ < 2 (r + 1)`, `4 + deg E₂ < 2 r` (`r` loop lines; `E₁`, `E₂` may instead vanish).

## Proof
With `a_l = D₀⁻¹` (mass `0`) and `g_l = D_M⁻¹`, `g_l = a_l - s a_l g_l`, so
`∏ g = ∑_{S} (-s)^{|S|} (∏ a) ∏_S g` (`prod_inv_expand`). The parts of order `s⁰` and `s¹` of
`N · ∏ g` are affine in `s` with flavour-independent `ℓ`-dependence, so their flavour sum
vanishes by the block conditions (`VP2.sum_block_affine_eq_zero`). Every remaining term has
enough denominators for `jointEnergyFirstIntegrable_oneLoop_affPoly'`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero)
open QED.TwoLoop.ClassIntegrable (jointEnergyFirstIntegrable_add)

/-- (T₉′) of the zero integrand. -/
theorem jointEnergyFirstIntegrable_zero_fun :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun _ => (0 : ℂ) :=
  ⟨fun _ => by simp, by simp⟩

/-- **One term**: `z E(ℓ) ∏_{t : T} D_{m_t}(c_{j t} ℓ + q_{j t})⁻¹`. -/
theorem jointEnergyFirstIntegrable_term {L T : Type*} [Fintype T] (c : L → ℝ)
    (hc : ∀ l, c l ≠ 0) (q : L → Fin 4 → ℝ) (j : T → L) (m : T → ℝ) {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : d ≤ 4) {E : (Fin 4 → ℝ) → ℂ} (hE : AffPoly d E)
    (h : 4 + d < 2 * Fintype.card T ∨ ∀ k, E k = 0) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      z * (E (ℓ 0) * ∏ t, (propDenom (m t) ε ((c (j t) : ℝ) • ℓ 0 + q (j t)))⁻¹) := by
  rcases h with h | h
  · have := jointEnergyFirstIntegrable_oneLoop_affPoly' (fun t => c (j t)) (fun t => hc _)
      (fun t => q (j t)) m hε hd h (hE.const_mul z)
    simpa only [mul_assoc] using this
  · simpa only [h, zero_mul, mul_zero] using jointEnergyFirstIntegrable_zero_fun

/-- The expansion of `∏ g` when `g_l = a_l - s a_l g_l`. -/
theorem prod_inv_expand {L : Type*} [DecidableEq L] (U : Finset L) (a g : L → ℂ) (s : ℂ)
    (hg : ∀ l, g l = a l - s * a l * g l) :
    ∏ l ∈ U, g l = ∑ S ∈ U.powerset, (-s) ^ S.card * ((∏ l ∈ U, a l) * ∏ l ∈ S, g l) := by
  have h1 : ∏ l ∈ U, g l = ∏ l ∈ U, ((-s) * (a l * g l) + a l) :=
    Finset.prod_congr rfl fun l _ => by linear_combination hg l
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_mul_distrib,
    ← Finset.prod_sdiff hS]
  ring

/-- The powerset sum split into `∅`, singletons, and subsets of size at least two. -/
theorem sum_powerset_split {L : Type*} [DecidableEq L] (U : Finset L) (F : Finset L → ℂ) :
    ∑ S ∈ U.powerset, F S = F ∅ + ∑ l ∈ U, F {l} +
      ∑ S ∈ U.powerset.filter (fun S => 2 ≤ S.card), F S := by
  rw [← Finset.sum_filter_add_sum_filter_not U.powerset (fun S => 2 ≤ S.card), add_comm]
  congr 1
  have hset : U.powerset.filter (fun S => ¬ 2 ≤ S.card) = insert ∅ (U.image fun l => {l}) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_image,
      not_le]
    constructor
    · rintro ⟨hS, hc⟩
      rcases (show S.card = 0 ∨ S.card = 1 by omega) with h | h
      · exact Or.inl (Finset.card_eq_zero.mp h)
      · obtain ⟨l, rfl⟩ := Finset.card_eq_one.mp h
        exact Or.inr ⟨l, hS (Finset.mem_singleton_self l), rfl⟩
    · rintro (rfl | ⟨l, hl, rfl⟩)
      · simp
      · simp [hl]
  rw [hset, Finset.sum_insert (by simp), Finset.sum_image (by simp)]

variable {F : Type} [Fintype F] [DecidableEq F]

/-- **(T₉′) of a block-summed one-loop integrand with an even numerator**, any masses. -/
theorem jointEnergyFirstIntegrable_blockSum (Φ : Lepton.Flavors F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    {L : Type*} [Fintype L] [DecidableEq L] (c : L → ℝ) (hc : ∀ l, c l ≠ 0)
    (q : L → Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) {d₀ d₁ d₂ : ℕ} (h₀ : d₀ ≤ 4) (h₁ : d₁ ≤ 4)
    (h₂ : d₂ ≤ 4) (E₀ E₁ E₂ : F → (Fin 4 → ℝ) → ℂ) (hE₀ : ∀ b, AffPoly d₀ (E₀ b))
    (hE₁ : ∀ b, AffPoly d₁ (E₁ b)) (hE₂ : ∀ b, AffPoly d₂ (E₂ b))
    (hc₀ : 4 + d₀ < 2 * (Fintype.card L + 2))
    (hc₁ : 4 + d₁ < 2 * (Fintype.card L + 1) ∨ ∀ b k, E₁ b k = 0)
    (hc₂ : 4 + d₂ < 2 * Fintype.card L ∨ ∀ b k, E₂ b k = 0) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * ((E₀ (rep f) (ℓ 0) + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) (ℓ 0) +
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * E₂ (rep f) (ℓ 0)) *
          ∏ l, (propDenom (Φ.mass f) ε ((c l : ℝ) • ℓ 0 + q l))⁻¹) := by
  classical
  -- notation
  set a : L → (Fin 4 → ℝ) → ℂ := fun l k => (propDenom 0 ε ((c l : ℝ) • k + q l))⁻¹ with ha
  set g : ℝ → L → (Fin 4 → ℝ) → ℂ := fun M l k => (propDenom M ε ((c l : ℝ) • k + q l))⁻¹
    with hg
  set A : (Fin 4 → ℝ) → ℂ := fun k => ∏ l, a l k with hA
  have hrel : ∀ M l k, g M l k = a l k - (M : ℂ) ^ 2 * a l k * g M l k := fun M l k => by
    have h0 := propDenom_ne_zero (M := 0) hε.ne' ((c l : ℝ) • k + q l)
    have hM := propDenom_ne_zero (M := M) hε.ne' ((c l : ℝ) • k + q l)
    have hD : propDenom M ε ((c l : ℝ) • k + q l) =
        propDenom 0 ε ((c l : ℝ) • k + q l) + (M : ℂ) ^ 2 := by
      simp only [propDenom]; push_cast; ring
    simp only [hg, ha]
    field_simp
    rw [hD]
    ring
  -- the remainder `X = ∏ g - A + s ∑ A a`
  have hX : ∀ M k, ∏ l, g M l k - A k + (M : ℂ) ^ 2 * ∑ l, A k * a l k =
      (M : ℂ) ^ 2 * (M : ℂ) ^ 2 * ∑ l, A k * a l k * g M l k +
        ∑ S ∈ (Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card),
          (-(M : ℂ) ^ 2) ^ S.card * (A k * ∏ l ∈ S, g M l k) := fun M k => by
    rw [prod_inv_expand _ (fun l => a l k) (fun l => g M l k) _ fun l => hrel M l k,
      sum_powerset_split]
    have e1 : ∑ l, (-(M : ℂ) ^ 2) ^ ({l} : Finset L).card *
        ((∏ l, a l k) * ∏ i ∈ ({l} : Finset L), g M i k) =
        ∑ l, (-(M : ℂ) ^ 2 * (A k * a l k) + (M : ℂ) ^ 2 * (M : ℂ) ^ 2 *
          (A k * a l k * g M l k)) :=
      Finset.sum_congr rfl fun l _ => by
        rw [Finset.card_singleton, Finset.prod_singleton, pow_one]
        linear_combination (-(M : ℂ) ^ 2 * A k) * hrel M l k
    rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one, one_mul]
    simp only [hA, Finset.mul_sum]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  -- the integrand as the flavour sum of the remainders
  have hkey : ∀ ℓ : Fin 1 → Fin 4 → ℝ,
      ∑ f, (Φ.coeff f : ℂ) * ((E₀ (rep f) (ℓ 0) + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) (ℓ 0) +
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * E₂ (rep f) (ℓ 0)) *
          ∏ l, (propDenom (Φ.mass f) ε ((c l : ℝ) • ℓ 0 + q l))⁻¹) =
      ∑ f, (Φ.coeff f : ℂ) * (((Φ.mass f : ℂ) ^ 2) ^ 2 * (E₂ (rep f) (ℓ 0) *
          ∏ l, g (Φ.mass f) l (ℓ 0)) -
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * (E₁ (rep f) (ℓ 0) * ∑ l, A (ℓ 0) * a l (ℓ 0)) +
        (E₀ (rep f) (ℓ 0) + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) (ℓ 0)) *
          ((Φ.mass f : ℂ) ^ 2 * (Φ.mass f : ℂ) ^ 2 *
            ∑ l, A (ℓ 0) * a l (ℓ 0) * g (Φ.mass f) l (ℓ 0) +
          ∑ S ∈ (Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card),
            (-(Φ.mass f : ℂ) ^ 2) ^ S.card * (A (ℓ 0) * ∏ l ∈ S, g (Φ.mass f) l (ℓ 0)))) := by
    intro ℓ
    set k := ℓ 0
    have hz := VP2.sum_block_affine_eq_zero Φ rep hrep hPV₁ hPV₂ 1 0
      (fun b => E₀ b k * A k)
    have hz' := VP2.sum_block_affine_eq_zero Φ rep hrep hPV₁ hPV₂ 0 (-1)
      (fun b => E₀ b k * ∑ l, A k * a l k)
    have hz'' := VP2.sum_block_affine_eq_zero Φ rep hrep hPV₁ hPV₂ 0 1
      (fun b => E₁ b k * A k)
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    have hsum : ∑ f, ((Φ.coeff f : ℂ) * ((E₀ (rep f) k + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) k +
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * E₂ (rep f) k) *
          ∏ l, (propDenom (Φ.mass f) ε ((c l : ℝ) • k + q l))⁻¹) -
      (Φ.coeff f : ℂ) * (((Φ.mass f : ℂ) ^ 2) ^ 2 * (E₂ (rep f) k *
          ∏ l, g (Φ.mass f) l k) -
        ((Φ.mass f : ℂ) ^ 2) ^ 2 * (E₁ (rep f) k * ∑ l, A k * a l k) +
        (E₀ (rep f) k + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) k) *
          ((Φ.mass f : ℂ) ^ 2 * (Φ.mass f : ℂ) ^ 2 * ∑ l, A k * a l k * g (Φ.mass f) l k +
          ∑ S ∈ (Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card),
            (-(Φ.mass f : ℂ) ^ 2) ^ S.card * (A k * ∏ l ∈ S, g (Φ.mass f) l k)))) =
      ∑ f, (Φ.coeff f : ℂ) * ((1 + 0 * (Φ.mass f : ℂ) ^ 2) * (E₀ (rep f) k * A k)) +
      ∑ f, (Φ.coeff f : ℂ) * ((0 + -1 * (Φ.mass f : ℂ) ^ 2) *
        (E₀ (rep f) k * ∑ l, A k * a l k)) +
      ∑ f, (Φ.coeff f : ℂ) * ((0 + 1 * (Φ.mass f : ℂ) ^ 2) * (E₁ (rep f) k * A k)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      have hXf := hX (Φ.mass f) k
      rw [show (∏ l, (propDenom (Φ.mass f) ε ((c l : ℝ) • k + q l))⁻¹) =
        ∏ l, g (Φ.mass f) l k from rfl]
      linear_combination (Φ.coeff f : ℂ) * (E₀ (rep f) k + (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) k) *
        hXf
    rw [hsum, hz, hz', hz'']
    ring
  simp only [hkey]
  refine jointEnergyFirstIntegrable_sum' _ fun f _ => ?_
  set M := Φ.mass f
  set b := rep f
  set s : ℂ := (M : ℂ) ^ 2
  -- the individual terms
  have tG : ∀ {d : ℕ} {E : (Fin 4 → ℝ) → ℂ}, d ≤ 4 → AffPoly d E →
      (4 + d < 2 * Fintype.card L ∨ ∀ k, E k = 0) → ∀ z : ℂ,
      QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => z * (E (ℓ 0) * ∏ l, g M l (ℓ 0)) :=
    fun hd hE h z => jointEnergyFirstIntegrable_term c hc q id (fun _ => M) hε hd hE h z
  have tA : ∀ {d : ℕ} {E : (Fin 4 → ℝ) → ℂ}, d ≤ 4 → AffPoly d E →
      (4 + d < 2 * (Fintype.card L + 1) ∨ ∀ k, E k = 0) → ∀ (z : ℂ) (l : L),
      QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
        z * (E (ℓ 0) * (A (ℓ 0) * a l (ℓ 0))) := fun hd hE h z l => by
    have := jointEnergyFirstIntegrable_term (T := L ⊕ Unit) c hc q (Sum.elim id fun _ => l)
      (fun _ => 0) hε hd hE (by simpa using h) z
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, id, Finset.univ_unique,
      Finset.prod_singleton] using this
  have tAG : ∀ {d : ℕ} {E : (Fin 4 → ℝ) → ℂ}, d ≤ 4 → AffPoly d E →
      (4 + d < 2 * (Fintype.card L + 2) ∨ ∀ k, E k = 0) → ∀ (z : ℂ) (l : L),
      QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
        z * (E (ℓ 0) * (A (ℓ 0) * a l (ℓ 0) * g M l (ℓ 0))) := fun hd hE h z l => by
    have := jointEnergyFirstIntegrable_term (T := L ⊕ Fin 2) c hc q (Sum.elim id fun _ => l)
      (Sum.elim (fun _ => 0) fun i => if i = 0 then 0 else M) hε hd hE (by simpa using h) z
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, id, Fin.prod_univ_two,
      Fin.isValue, ite_true, one_ne_zero, ite_false, mul_assoc] using this
  have tS : ∀ {d : ℕ} {E : (Fin 4 → ℝ) → ℂ}, d ≤ 4 → AffPoly d E →
      (4 + d < 2 * (Fintype.card L + 2) ∨ ∀ k, E k = 0) → ∀ (z : ℂ) (S : Finset L),
      2 ≤ S.card → QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
        z * (E (ℓ 0) * (A (ℓ 0) * ∏ l ∈ S, g M l (ℓ 0))) := fun hd hE h z S hS => by
    have := jointEnergyFirstIntegrable_term (T := L ⊕ S) c hc q (Sum.elim id fun x => x.1)
      (Sum.elim (fun _ => 0) fun _ => M) hε hd hE (by
        rcases h with h | h
        · left; simp only [Fintype.card_sum, Fintype.card_coe]; omega
        · exact Or.inr h) z
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, id] at this
    refine (congrArg _ (funext fun ℓ => ?_)).mp this
    rw [Finset.prod_coe_sort S (fun l => (propDenom M ε ((c l : ℝ) • ℓ 0 + q l))⁻¹)]
  have hsumT : ∀ {ι : Type _} (U : Finset ι) (z : ℂ) (E : (Fin 4 → ℝ) → ℂ)
      (X : ι → (Fin 1 → Fin 4 → ℝ) → ℂ),
      (∀ i ∈ U, QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => z * (E (ℓ 0) * X i ℓ)) →
      QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => z * (E (ℓ 0) * ∑ i ∈ U, X i ℓ) :=
    fun U z E X h => by
      simp only [Finset.mul_sum]
      exact jointEnergyFirstIntegrable_sum' U h
  have h1' : 4 + d₁ < 2 * (Fintype.card L + 1) ∨ ∀ k, E₁ b k = 0 :=
    hc₁.imp id fun h => h b
  have h1'' : 4 + d₁ < 2 * (Fintype.card L + 2) ∨ ∀ k, E₁ b k = 0 :=
    hc₁.imp (fun h => by omega) fun h => h b
  have T1 := tG h₂ (hE₂ b) (hc₂.imp id fun h => h b) ((Φ.coeff f : ℂ) * s ^ 2)
  have T2 := hsumT Finset.univ (-(Φ.coeff f : ℂ) * s ^ 2) (E₁ b) (fun l ℓ => A (ℓ 0) * a l (ℓ 0))
    fun l _ => tA h₁ (hE₁ b) h1' _ l
  have T3 := hsumT Finset.univ ((Φ.coeff f : ℂ) * s * s) (E₀ b)
    (fun l ℓ => A (ℓ 0) * a l (ℓ 0) * g M l (ℓ 0)) fun l _ => tAG h₀ (hE₀ b) (Or.inl hc₀) _ l
  have T4 := hsumT Finset.univ ((Φ.coeff f : ℂ) * s * s * s) (E₁ b)
    (fun l ℓ => A (ℓ 0) * a l (ℓ 0) * g M l (ℓ 0)) fun l _ => tAG h₁ (hE₁ b) h1'' _ l
  have T5 := hsumT ((Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card))
    (Φ.coeff f : ℂ) (E₀ b) (fun S ℓ => (-s) ^ S.card * (A (ℓ 0) * ∏ l ∈ S, g M l (ℓ 0)))
    fun S hS => by
      have := tS h₀ (hE₀ b) (Or.inl hc₀) ((Φ.coeff f : ℂ) * (-s) ^ S.card) S
        (Finset.mem_filter.mp hS).2
      refine (congrArg _ (funext fun ℓ => ?_)).mp this
      ring
  have T6 := hsumT ((Finset.univ : Finset L).powerset.filter (fun S => 2 ≤ S.card))
    ((Φ.coeff f : ℂ) * s) (E₁ b) (fun S ℓ => (-s) ^ S.card * (A (ℓ 0) * ∏ l ∈ S, g M l (ℓ 0)))
    fun S hS => by
      have := tS h₁ (hE₁ b) h1'' ((Φ.coeff f : ℂ) * s * (-s) ^ S.card) S
        (Finset.mem_filter.mp hS).2
      refine (congrArg _ (funext fun ℓ => ?_)).mp this
      ring
  have hall := jointEnergyFirstIntegrable_add T1 (jointEnergyFirstIntegrable_add T2
    (jointEnergyFirstIntegrable_add T3 (jointEnergyFirstIntegrable_add T4
      (jointEnergyFirstIntegrable_add T5 T6))))
  refine (congrArg _ (funext fun ℓ => ?_)).mp hall
  ring

end QED.GradedProof.X0

end
