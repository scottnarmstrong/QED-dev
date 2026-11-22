/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.TwoLoopSERel
public import QED.Algebra.IBPCertPilotData

/-!
# Relations at `λ = 0` and the scaleless sectors

* `val_relation`: a dimension-shift relation `P · J(n, d) = (d/2) Σ_t c_t J(n + γ_t, d + 2)` along
  the lines gives `P(0) · val n d₀ = Σ_t c_t ρ_t(0) · val (n + γ_t) (d₀ + 2)` for `d₀ ∉ ℚ`.
* **Zero sectors by scaling (item 5).** On the face `x_S = 0` of a scaleless sector `S`, `G` is
  homogeneous of degree one in a single variable `x_c`: `x_c ∂_c G = G + r` with every monomial of
  `r` divisible by some `x_a`, `a ∈ S` (data `rZero`, checked by `ring` and `decide`). The resulting
  relation `(ν_c - d/2) J(ν, d) = (d/2) Σ c_γ(r) J(ν + γ, d + 2)` at `λ = 0` has, for every term,
  either a vanishing Pochhammer factor `(n_a)_{γ_a}` (when `n_a + γ_a ≥ 1`) or a label still in the
  sector with smaller depth; since `n_c - d₀/2 ≠ 0`, induction gives `val n d₀ = 0`
  (`val_eq_zero_of_sector`). This is a theorem about the continued integrals, not a convention.
-/

@[expose] public section

open Complex Filter Topology Set QED.DimReg

namespace QED.DimReg.TwoLoopSESector

/-- **A dimension-shift relation at `λ = 0`.** -/
theorem val_relation {n : Fin 5 → ℤ} {d₀ : ℂ} (hd : Irr d₀) {P : ℂ → ℂ}
    (hP : Differentiable ℂ P) (r : MonoList 5) (hr : ∀ t ∈ r, ∑ j, t.2 j ≤ 3)
    (hJ : ∀ᶠ l in atRe, P l * Jline n d₀ l -
      lineD d₀ l / 2 * (r.map fun t => (t.1 : ℂ) * Jline (n + natZ t.2) (d₀ + 2) l).sum = 0) :
    P 0 * val n d₀ =
      (r.map fun t => (t.1 : ℂ) * rho n d₀ t.2 0 * val (n + natZ t.2) (d₀ + 2)).sum := by
  have h := nhdsNE_normalized hP r (eventually_normalized r hr hJ)
  have T1 : Tendsto (fun l => P l * Iline n d₀ l) (𝓝[≠] 0) (𝓝 (P 0 * val n d₀)) :=
    ((hP 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul (tendsto_Iline n hd)
  have T2 := tendsto_list_sum r (f := fun t l => (t.1 : ℂ) * rho n d₀ t.2 l *
    Iline (n + natZ t.2) (d₀ + 2) l) fun t _ => (tendsto_const_nhds.mul
      ((analyticAt_rho n d₀ t.2 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).mul
      (tendsto_Iline _ hd.add_two)
  exact tendsto_nhds_unique (T1.congr' h) T2

theorem natZ_zero : natZ (0 : Fin 5 → ℕ) = 0 := by funext j; simp [natZ]

theorem polyEval_one (x : Fin 5 → ℝ) : polyEval [((1 : ℤ), (0 : Fin 5 → ℕ))] x = 1 := by
  simp [polyEval, monoEval]

/-- The scaling relation `(ν_c - d/2) J(ν, d) = (d/2) Σ c_γ(r) J(ν + γ, d + 2)` along the line,
from `x_c ∂_c G = G + r`. -/
theorem eventually_scaling (c : Fin 5) (r : MonoList 5)
    (hr : ∀ x, x c * gD c x = Gx x + polyEval r x) (n : Fin 5 → ℤ) (d₀ : ℂ) :
    ∀ᶠ l in atRe, (lineNu n l c - lineD d₀ l / 2) * Jline n d₀ l - lineD d₀ l / 2 *
      (r.map fun t => (t.1 : ℂ) * Jline (n + natZ t.2) (d₀ + 2) l).sum = 0 := by
  have h := eventually_annihilator (fun b => if b = c then [((1 : ℤ), Pi.single c 1)] else [])
    [((1 : ℤ), (0 : Fin 5 → ℕ))] r (fun b => if b = c then rRaise c else [])
    (fun x => by
      rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb, polyEval]) (by simp)]
      simp only [eq_self, ↓reduceIte]
      rw [polyEval_single, polyEval_one, hr]
      ring)
    (fun b x => by
      by_cases hb : b = c
      · subst hb
        simp only [eq_self, ↓reduceIte]
        rw [polyEval_single, polyEval_rRaise]
      · simp [hb, polyEval]) n d₀
  filter_upwards [h] with l hl
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at hl
  simp only [eq_self, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    lowZ_single, natZ_zero, add_zero, Int.cast_one, one_mul] at hl
  rw [Pi.single_eq_same] at hl
  linear_combination hl

/-- A vanishing Pochhammer factor: `(m)_k = 0` for an integer `m ≤ 0` with `m + k ≥ 1`. -/
theorem poch_eq_zero {m : ℤ} (hm : m ≤ 0) {k : ℕ} (hk : 1 ≤ m + k) : poch (m : ℂ) k = 0 := by
  refine Finset.prod_eq_zero (i := (-m).toNat) (Finset.mem_range.2 (by omega)) ?_
  have : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
  rw [show (((-m).toNat : ℕ) : ℂ) = ((((-m).toNat : ℕ) : ℤ) : ℂ) by push_cast; rfl, this]
  push_cast
  ring

theorem rho_zero_eq_zero {m : Fin 5 → ℤ} {d₀ : ℂ} {γ : Fin 5 → ℕ} {a : Fin 5} (ha : m a ≤ 0)
    (hγ : 1 ≤ m a + γ a) : rho m d₀ γ 0 = 0 := by
  unfold rho
  rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simpa [lineNu] using poch_eq_zero ha hγ),
    mul_zero]

/-- The depth of a label in the sector `S`. -/
def depth (S : Finset (Fin 5)) (n : Fin 5 → ℤ) : ℕ := ∑ a ∈ S, (-n a).toNat

/-- **A scaleless sector vanishes** (item 5): if `x_c ∂_c G = G + r` with every monomial of `r`
divisible by some `x_a`, `a ∈ S`, then `val n d₀ = 0` whenever `n_a ≤ 0` for all `a ∈ S` and
`d₀ ∉ ℚ`. -/
theorem val_eq_zero_of_sector (S : Finset (Fin 5)) (c : Fin 5) (r : MonoList 5)
    (hr : ∀ x, x c * gD c x = Gx x + polyEval r x)
    (hspec : ∀ t ∈ r, ∑ j, t.2 j ≤ 3 ∧ ∃ a ∈ S, 1 ≤ t.2 a) (n : Fin 5 → ℤ)
    (hn : ∀ a ∈ S, n a ≤ 0) {d₀ : ℂ} (hd : Irr d₀) : val n d₀ = 0 := by
  suffices h : ∀ k, ∀ n : Fin 5 → ℤ, depth S n ≤ k → (∀ a ∈ S, n a ≤ 0) → ∀ d₀, Irr d₀ →
      val n d₀ = 0 from h _ n le_rfl hn d₀ hd
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n hk hn d₀ hd
  have hrel := val_relation hd (P := fun l => lineNu n l c - lineD d₀ l / 2)
    (by unfold lineNu lineD; fun_prop) r (fun t ht => (hspec t ht).1)
    (eventually_scaling c r hr n d₀)
  have hsum : (r.map fun t => (t.1 : ℂ) * rho n d₀ t.2 0 * val (n + natZ t.2) (d₀ + 2)).sum =
      0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a, haS, hta⟩ := (hspec t ht).2
    by_cases hin : ∀ b ∈ S, (n + natZ t.2) b ≤ 0
    · have hlt : depth S (n + natZ t.2) < depth S n := by
        refine Finset.sum_lt_sum (fun b hb => ?_) ⟨a, haS, ?_⟩
        · have := hin b hb
          simp only [Pi.add_apply, natZ] at this ⊢
          omega
        · have := hin a haS
          simp only [Pi.add_apply, natZ] at this ⊢
          omega
      rw [ih _ (by omega) _ le_rfl hin _ hd.add_two, mul_zero]
    · push Not at hin
      obtain ⟨b, hbS, hb⟩ := hin
      simp only [Pi.add_apply, natZ] at hb
      rw [rho_zero_eq_zero (hn b hbS) (by omega), mul_zero, zero_mul]
  rw [hsum] at hrel
  have hne : lineNu n 0 c - lineD d₀ 0 / 2 ≠ 0 := by
    intro h
    apply hd (2 * n c)
    simp only [lineNu, lineD, add_zero, mul_zero] at h
    push_cast
    linear_combination -2 * h
  exact (mul_eq_zero.1 hrel).resolve_left hne

/-! ### The four scaleless sectors of `twoLoopSE` -/

theorem polyEval_rZero0 (x : Fin 5 → ℝ) :
    x 1 * gD 1 x = Gx x + polyEval rZero0 x := by
  simp [rZero0, polyEval, monoEval, Fin.prod_univ_five, gD, Gx]
  ring

theorem rZero0_spec :
    ∀ t ∈ rZero0, ∑ j, t.2 j ≤ 3 ∧ ∃ a ∈ ({3, 4} : Finset (Fin 5)), 1 ≤ t.2 a := by
  decide +kernel

theorem polyEval_rZero1 (x : Fin 5 → ℝ) :
    x 0 * gD 0 x = Gx x + polyEval rZero1 x := by
  simp [rZero1, polyEval, monoEval, Fin.prod_univ_five, gD, Gx]
  ring

theorem rZero1_spec :
    ∀ t ∈ rZero1, ∑ j, t.2 j ≤ 3 ∧ ∃ a ∈ ({2, 4} : Finset (Fin 5)), 1 ≤ t.2 a := by
  decide +kernel

theorem polyEval_rZero2 (x : Fin 5 → ℝ) :
    x 0 * gD 0 x = Gx x + polyEval rZero2 x := by
  simp [rZero2, polyEval, monoEval, Fin.prod_univ_five, gD, Gx]
  ring

theorem rZero2_spec :
    ∀ t ∈ rZero2, ∑ j, t.2 j ≤ 3 ∧ ∃ a ∈ ({1, 2, 3} : Finset (Fin 5)), 1 ≤ t.2 a := by
  decide +kernel

theorem polyEval_rZero3 (x : Fin 5 → ℝ) :
    x 1 * gD 1 x = Gx x + polyEval rZero3 x := by
  simp [rZero3, polyEval, monoEval, Fin.prod_univ_five, gD, Gx]
  ring

theorem rZero3_spec :
    ∀ t ∈ rZero3, ∑ j, t.2 j ≤ 3 ∧ ∃ a ∈ ({0, 2, 3} : Finset (Fin 5)), 1 ≤ t.2 a := by
  decide +kernel

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Pilot in
/-- **The declared zero sectors of `twoLoopSE` vanish, as values of the continuation** (item 5):
for `d ∉ ℚ`, `val ν d = 0` whenever `ν_a ≤ 0` throughout one of `{3, 4}`, `{2, 4}`, `{1, 2, 3}`,
`{0, 2, 3}`. -/
theorem zeroSectors_val {d : ℂ} (hd : Irr d) : twoLoopSE.ZeroSectors val d := by
  intro S hS ν hν
  have hv : ∀ a : Fin 5, (a : ℕ) ∈ S → ν a ≤ 0 := fun a ha => by
    have := hν a ha
    simpa [vecGet, twoLoopSE, a.isLt] using this
  simp only [twoLoopSE, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · exact val_eq_zero_of_sector _ 1 rZero0 polyEval_rZero0 rZero0_spec ν
      (fun a ha => hv a (by fin_cases a <;> simp_all)) hd
  · exact val_eq_zero_of_sector _ 0 rZero1 polyEval_rZero1 rZero1_spec ν
      (fun a ha => hv a (by fin_cases a <;> simp_all)) hd
  · exact val_eq_zero_of_sector _ 0 rZero2 polyEval_rZero2 rZero2_spec ν
      (fun a ha => hv a (by fin_cases a <;> simp_all)) hd
  · exact val_eq_zero_of_sector _ 1 rZero3 polyEval_rZero3 rZero3_spec ν
      (fun a ha => hv a (by fin_cases a <;> simp_all)) hd

end QED.DimReg.TwoLoopSESector
