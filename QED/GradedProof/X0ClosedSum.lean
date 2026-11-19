/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Block
public import QED.TwoLoop.ClassIntegrableFurryEven

/-!
# (X₀): a block-summed one-loop integrand built from chirality-pure entries

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the closed
fermion loops at one loop. In the Weyl representation `γ⁵ = diag(-1, -1, 1, 1)`; call indices
`a, b` *in the same block* if `blk a = blk b` (`blk a = (a < 2)`). Every entry met on a closed
loop is *pure*: on a same-block pair it is `M u` (mass entries: `M δ_{ab}`, `δ_m M δ_{ab}`; the
`γ^μ` entries vanish there), on a different-block pair it is `v(k)`, free of `M`
(`gamma_eq_zero_of_blk`, `slash_eq_zero_of_blk`, `electronNumerator_eq_ite`).

If the sign product `∏_e sgn(a_e) sgn(b_e)` of the entries is `1` and their number is even, the
number `p` of same-block entries is even (`even_card_blk`), so the product of the entries is
`(M²)^{p/2} W(k)` (`prod_ite_mass`), and `jointEnergyFirstIntegrable_entrySum` feeds this to
`jointEnergyFirstIntegrable_blockSum`: with `w_e ∈ {0, 1}` the degree of `v_e`, `d = ∑ w_e`,
`d ≤ 4` and `d < 2 r` (`r` loop lines) give (T₉′) of the flavour sum, at any masses.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.TwoLoop.Bridge (propDenom electronNumerator)
open QED.TwoLoop.FurryIntegrable (sgn gamma_mul_sgn)

/-- The chirality block of a spinor index. -/
def blk (a : Fin 4) : Bool := decide (a.val < 2)

theorem sgn_mul_sgn (a b : Fin 4) : sgn a * sgn b = if blk a = blk b then 1 else -1 := by
  fin_cases a <;> fin_cases b <;> norm_num [sgn, blk]

theorem gamma_eq_zero_of_blk (μ : Fin 4) {a b : Fin 4} (h : blk a = blk b) :
    Dirac.gamma μ a b = 0 := by
  have h1 := gamma_mul_sgn μ a b
  rw [sgn_mul_sgn] at h1
  simp only [h, ite_true, mul_one] at h1
  linear_combination h1 / 2

theorem slash_eq_zero_of_blk (p : Fin 4 → ℝ) {a b : Fin 4} (h : blk a = blk b) :
    Dirac.slash p a b = 0 := by
  simp only [Dirac.slash, Matrix.sum_apply, Matrix.smul_apply, gamma_eq_zero_of_blk _ h,
    smul_zero, Finset.sum_const_zero]

theorem one_eq_zero_of_blk {a b : Fin 4} (h : ¬ blk a = blk b) :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) a b = 0 := by
  rw [Matrix.one_apply_ne]
  rintro rfl
  exact h rfl

theorem gamma_eq_ite (μ a b : Fin 4) :
    Dirac.gamma μ a b = if blk a = blk b then 0 else Dirac.gamma μ a b := by
  split_ifs with h
  · exact gamma_eq_zero_of_blk μ h
  · rfl

/-- The entries of `M - k̸` are pure. -/
theorem electronNumerator_eq_ite (M : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    electronNumerator M k a b = if blk a = blk b then (M : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b
      else -Dirac.slash k a b := by
  simp only [electronNumerator, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [slash_eq_zero_of_blk k h, sub_zero]
  · rw [one_eq_zero_of_blk h, mul_zero, zero_sub]

/-- A product of pure entries. -/
theorem prod_ite_mass {E : Type*} [Fintype E] (S : E → Prop) [DecidablePred S] (M : ℂ)
    (u v : E → ℂ) :
    ∏ e, (if S e then M * u e else v e) =
      M ^ (Finset.univ.filter S).card * ∏ e, (if S e then u e else v e) := by
  rw [Finset.prod_ite, Finset.prod_ite, Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-- **Parity**: if the sign product is `1` and the number of entries is even, an even number
of entries are same-block. -/
theorem even_card_blk {E : Type*} [Fintype E] (a b : E → Fin 4)
    (h : ∏ e, sgn (a e) * sgn (b e) = 1) (hE : Even (Fintype.card E)) :
    Even (Finset.univ.filter fun e => blk (a e) = blk (b e)).card := by
  classical
  have h1 : ∏ e, sgn (a e) * sgn (b e) =
      (-1 : ℂ) ^ (Finset.univ.filter fun e => ¬ blk (a e) = blk (b e)).card := by
    simp only [sgn_mul_sgn]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [h1] at h
  have hodd : Even (Finset.univ.filter fun e => ¬ blk (a e) = blk (b e)).card := by
    by_contra hn
    rw [Nat.not_even_iff_odd] at hn
    rw [hn.neg_one_pow] at h
    norm_num at h
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset E)) (fun e => blk (a e) = blk (b e))
  rw [Finset.card_univ] at hsum
  rw [← hsum] at hE
  exact (Nat.even_add.mp hE).mpr hodd

variable {F : Type} [Fintype F] [DecidableEq F]

/-- **(T₉′) of a block-summed loop of pure entries**, any masses. The entries `e : E` sit at the
index pairs `(a e, b e)`; a same-block entry is `M_f u_{rep f, e}`, a different-block one
`v_{rep f, e}(ℓ)` of degree `w e` (and `u = 0` where `w = 0`); `K` is a constant factor. -/
theorem jointEnergyFirstIntegrable_entrySum (Φ : Lepton.Flavors F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    {L : Type*} [Fintype L] [DecidableEq L] (c : L → ℝ) (hc : ∀ l, c l ≠ 0)
    (q : L → Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) {E : Type*} [Fintype E] (a b : E → Fin 4)
    (hpar : Even (Finset.univ.filter fun e => blk (a e) = blk (b e)).card) (w : E → ℕ)
    (u : F → E → ℂ) (v : F → E → (Fin 4 → ℝ) → ℂ) (hv : ∀ x e, AffPoly (w e) (v x e))
    (hu : ∀ x e, w e = 0 → u x e = 0) (K : (Fin 4 → ℝ) → ℂ) (hK : AffPoly 0 K)
    (hd : ∑ e, w e ≤ 4) (hr : ∑ e, w e < 2 * Fintype.card L) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * ((K (ℓ 0) * ∏ e, (if blk (a e) = blk (b e) then
        (Φ.mass f : ℂ) * u (rep f) e else v (rep f) e (ℓ 0))) *
          ∏ l, (propDenom (Φ.mass f) ε ((c l : ℝ) • ℓ 0 + q l))⁻¹) := by
  classical
  set S : E → Prop := fun e => blk (a e) = blk (b e)
  set p := (Finset.univ.filter S).card with hp
  set W : F → (Fin 4 → ℝ) → ℂ := fun x k => K k * ∏ e, (if S e then u x e else v x e k)
  set dW : ℕ := ∑ e, (if S e then 0 else w e)
  have hW : ∀ x, AffPoly dW (W x) := fun x => by
    have := hK.mul (AffPoly.prod Finset.univ (fun e => if S e then 0 else w e)
      (N := fun e k => if S e then u x e else v x e k) fun e _ => by
        by_cases h : S e
        · simp only [h, ite_true]; exact AffPoly.const _
        · simp only [h, ite_false]; exact hv x e)
    simpa only [zero_add] using this
  have hrw : ∀ (f : F) (k : Fin 4 → ℝ), K k * ∏ e, (if S e then
      (Φ.mass f : ℂ) * u (rep f) e else v (rep f) e k) =
      ((Φ.mass f : ℂ) ^ 2) ^ (p / 2) * W (rep f) k := fun f k => by
    rw [prod_ite_mass, ← pow_mul, Nat.two_mul_div_two_of_even hpar]
    ring
  simp only [S] at hrw
  simp only [hrw]
  -- if some same-block entry has degree `0`, everything vanishes
  by_cases hz : ∃ e, S e ∧ w e = 0
  · obtain ⟨e₀, he₀, hw₀⟩ := hz
    have h0 : ∀ x k, W x k = 0 := fun x k => by
      simp only [W]
      rw [Finset.prod_eq_zero (Finset.mem_univ e₀) (by simp [he₀, hu x e₀ hw₀]), mul_zero]
    simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun
  push Not at hz
  have hdeg : dW + p ≤ ∑ e, w e := by
    rw [hp, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    split_ifs with h
    · have := hz e h
      omega
    · omega
  have hpe := hpar
  obtain ⟨j, hj⟩ := hpe
  have hj2 : p / 2 = j := by omega
  rw [hj2]
  have hj3 : j ≤ 2 := by omega
  have hC : ∀ {d₀ d₁ d₂ : ℕ} (E₀ E₁ E₂ : F → (Fin 4 → ℝ) → ℂ),
      (∀ f k, ((Φ.mass f : ℂ) ^ 2) ^ j * W (rep f) k = E₀ (rep f) k +
        (Φ.mass f : ℂ) ^ 2 * E₁ (rep f) k + ((Φ.mass f : ℂ) ^ 2) ^ 2 * E₂ (rep f) k) →
      d₀ ≤ 4 → d₁ ≤ 4 → d₂ ≤ 4 → (∀ b, AffPoly d₀ (E₀ b)) → (∀ b, AffPoly d₁ (E₁ b)) →
      (∀ b, AffPoly d₂ (E₂ b)) → 4 + d₀ < 2 * (Fintype.card L + 2) →
      (4 + d₁ < 2 * (Fintype.card L + 1) ∨ ∀ b k, E₁ b k = 0) →
      (4 + d₂ < 2 * Fintype.card L ∨ ∀ b k, E₂ b k = 0) →
      QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
        ∑ f, (Φ.coeff f : ℂ) * (((Φ.mass f : ℂ) ^ 2) ^ j * W (rep f) (ℓ 0) *
          ∏ l, (propDenom (Φ.mass f) ε ((c l : ℝ) • ℓ 0 + q l))⁻¹) :=
    fun E₀ E₁ E₂ hE h₀ h₁ h₂ hE₀ hE₁ hE₂ hc₀ hc₁ hc₂ => by
      simp only [hE]
      exact jointEnergyFirstIntegrable_blockSum Φ rep hrep hPV₁ hPV₂ c hc q hε h₀ h₁ h₂ E₀ E₁ E₂
        hE₀ hE₁ hE₂ hc₀ hc₁ hc₂
  have hZ : ∀ _ : F, AffPoly 0 fun _ : Fin 4 → ℝ => (0 : ℂ) := fun _ => AffPoly.const 0
  have hpj : p = 2 * j := by omega
  clear_value W dW p
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · exact hC W (fun _ _ => 0) (fun _ _ => 0) (fun f k => by ring) (by omega) (by norm_num)
      (by norm_num) hW hZ hZ (by omega) (Or.inr fun _ _ => rfl)
      (Or.inr fun _ _ => rfl)
  · exact hC (fun _ _ => 0) W (fun _ _ => 0) (fun f k => by ring) (by norm_num) (by omega)
      (by norm_num) hZ hW hZ (by omega) (Or.inl (by omega)) (Or.inr fun _ _ => rfl)
  · exact hC (fun _ _ => 0) (fun _ _ => 0) W (fun f k => by ring) (by norm_num) (by norm_num)
      (by omega) hZ hZ hW (by omega) (Or.inr fun _ _ => rfl) (Or.inl (by omega))

end QED.GradedProof.X0

end
