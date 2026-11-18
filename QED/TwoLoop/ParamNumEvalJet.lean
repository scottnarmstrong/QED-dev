/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicitPiece
public import QED.TwoLoop.PauliZeroLimitCurve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Second-order jets at `u = 0` and the second-order coefficient

Infrastructure for stage 1 of section 8 of `docs/TWO-LOOP-UNITS.md`. The class values
`openZero c P = ∫ c₂[N(x, ·)] / V(x)⁴` use the second-order coefficient
`c₂[g] = lim_{u → 0} (g(u) + g(-u) - 2 g(0)) / (2u²)`
(`QED.TwoLoop.PauliZeroExplicit.secondCoeff`). Along the curve `p'(u)` the numerator `N(x, u)` is
built from the components of `p'(u)` by sums and products, so its coefficient is computed by the
algebra of second-order jets:

* `HasJet2 g a b c`: `g(u) = a + b u + c u² + u² ε(u)` with `ε → 0` at `0`;
* `HasJet2.secondCoeff`: then `c₂[g] = c`;
* closure under constants, the identity, sums, finite sums, scalar multiples and products
  (`HasJet2.add`, `HasJet2.sum`, `HasJet2.const_mul`, `HasJet2.mul`, …), with the product rule
  `(a₁, b₁, c₁)(a₂, b₂, c₂) = (a₁a₂, a₁b₂ + b₁a₂, a₁c₂ + b₁b₂ + c₁a₂)`;
* the curve components: `(1 + u²)/(1 - u²) = 1 + 2u² + o(u²)` and `2u/(1 - u²) = 2u + o(u²)`
  (`hasJet2_curve_zero`, `hasJet2_curve_one`), so `p'(u) = p + 2m u e₁ + 2m u² e₀ + o(u²)`
  (`hasJet2_curveMomentum`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.TwoLoop.ParamNumEval

open QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZero

/-- **A second-order jet at `0`**: `g(u) = a + b u + c u² + u² ε(u)` with `ε(u) → 0`. -/
def HasJet2 (g : ℝ → ℂ) (a b c : ℂ) : Prop :=
  ∃ ε : ℝ → ℂ, Tendsto ε (𝓝 0) (𝓝 0) ∧ ∀ u, g u = a + b * u + c * (u : ℂ) ^ 2 + (u : ℂ) ^ 2 * ε u

namespace HasJet2

variable {g h : ℝ → ℂ} {a b c a' b' c' : ℂ}

theorem apply_zero (hg : HasJet2 g a b c) : g 0 = a := by
  obtain ⟨ε, -, he⟩ := hg
  simpa using he 0

/-- The second-order quotient converges to the jet coefficient. -/
theorem tendsto_quot (hg : HasJet2 g a b c) :
    Tendsto (fun u => (g u + g (-u) - 2 * g 0) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 c) := by
  obtain ⟨ε, hε, he⟩ := hg
  have hε' : Tendsto (fun u : ℝ => ε (-u)) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun u : ℝ => -u) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact hε.comp this
  have hlim : Tendsto (fun u => c + (ε u + ε (-u)) / 2) (𝓝 0) (𝓝 c) := by
    simpa using tendsto_const_nhds.add ((hε.add hε').div_const 2)
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu
  rw [he u, he (-u), he 0]
  push_cast
  field_simp
  ring

/-- **The second-order coefficient of a jet.** -/
theorem secondCoeff_eq (hg : HasJet2 g a b c) : secondCoeff g = c :=
  hg.tendsto_quot.limUnder_eq

theorem const (a : ℂ) : HasJet2 (fun _ => a) a 0 0 :=
  ⟨fun _ => 0, tendsto_const_nhds, fun u => by ring⟩

theorem id : HasJet2 (fun u => (u : ℂ)) 0 1 0 :=
  ⟨fun _ => 0, tendsto_const_nhds, fun u => by ring⟩

theorem congr (hg : HasJet2 g a b c) (h' : ∀ u, h u = g u) : HasJet2 h a b c := by
  obtain ⟨ε, hε, he⟩ := hg
  exact ⟨ε, hε, fun u => by rw [h', he]⟩

theorem of_eq (hg : HasJet2 g a b c) (h' : ∀ u, h u = g u) (ha : a = a') (hb : b = b')
    (hc : c = c') : HasJet2 h a' b' c' := by
  subst ha hb hc
  exact hg.congr h'

theorem add (hg : HasJet2 g a b c) (hh : HasJet2 h a' b' c') :
    HasJet2 (fun u => g u + h u) (a + a') (b + b') (c + c') := by
  obtain ⟨ε, hε, he⟩ := hg
  obtain ⟨δ, hδ, hd⟩ := hh
  refine ⟨fun u => ε u + δ u, by simpa using hε.add hδ, fun u => ?_⟩
  dsimp only
  rw [he, hd]
  ring

theorem neg (hg : HasJet2 g a b c) : HasJet2 (fun u => -g u) (-a) (-b) (-c) := by
  obtain ⟨ε, hε, he⟩ := hg
  refine ⟨fun u => -ε u, by simpa using hε.neg, fun u => ?_⟩
  dsimp only
  rw [he]
  ring

theorem sub (hg : HasJet2 g a b c) (hh : HasJet2 h a' b' c') :
    HasJet2 (fun u => g u - h u) (a - a') (b - b') (c - c') := by
  have := hg.add hh.neg
  simpa [sub_eq_add_neg] using this

theorem const_mul (k : ℂ) (hg : HasJet2 g a b c) :
    HasJet2 (fun u => k * g u) (k * a) (k * b) (k * c) := by
  obtain ⟨ε, hε, he⟩ := hg
  refine ⟨fun u => k * ε u, by simpa using hε.const_mul k, fun u => ?_⟩
  dsimp only
  rw [he]
  ring

/-- **The product rule for second-order jets.** -/
theorem mul (hg : HasJet2 g a b c) (hh : HasJet2 h a' b' c') :
    HasJet2 (fun u => g u * h u) (a * a') (a * b' + b * a') (a * c' + b * b' + c * a') := by
  obtain ⟨ε, hε, he⟩ := hg
  obtain ⟨δ, hδ, hd⟩ := hh
  set G : ℝ → ℂ := fun u => a + b * u + c * (u : ℂ) ^ 2 + (u : ℂ) ^ 2 * ε u
  have hG : Tendsto G (𝓝 0) (𝓝 a) := by
    have hu : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_ofReal.tendsto (0 : ℝ))
    simpa [G] using ((tendsto_const_nhds.add (hu.const_mul b)).add
      ((hu.pow 2).const_mul c)).add ((hu.pow 2).mul hε)
  have hu : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_ofReal.tendsto (0 : ℝ))
  refine ⟨fun u => b * c' * u + c * b' * u + c * c' * (u : ℂ) ^ 2 + G u * δ u +
      ε u * (a' + b' * u + c' * (u : ℂ) ^ 2), ?_, fun u => ?_⟩
  · have h1 := ((hu.const_mul (b * c')).add (hu.const_mul (c * b'))).add
      ((hu.pow 2).const_mul (c * c'))
    have h2 := hG.mul hδ
    have h3 := hε.mul (((tendsto_const_nhds (x := a')).add (hu.const_mul b')).add
      ((hu.pow 2).const_mul c'))
    simpa using (h1.add h2).add h3
  · dsimp only
    rw [he, hd]
    simp only [G]
    ring

theorem sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ} {a b c : ι → ℂ}
    (hg : ∀ k ∈ s, HasJet2 (g k) (a k) (b k) (c k)) :
    HasJet2 (fun u => ∑ k ∈ s, g k u) (∑ k ∈ s, a k) (∑ k ∈ s, b k) (∑ k ∈ s, c k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const 0).congr fun u => by simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, Finset.sum_insert hk]
    exact ((hg k (Finset.mem_insert_self k s)).add
      (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))).congr fun u => Finset.sum_insert hk

end HasJet2


/-! ### The curve -/

theorem tendsto_ofReal_zero : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝 0) (𝓝 0) := by
  simpa using (continuous_ofReal.tendsto (0 : ℝ))

theorem tendsto_div_one_sub_sq (k : ℕ) :
    Tendsto (fun u : ℝ => (u : ℂ) ^ (k + 1) / (1 - (u : ℂ) ^ 2)) (𝓝 0) (𝓝 0) := by
  have h := (tendsto_ofReal_zero.pow (k + 1)).div
    (tendsto_const_nhds.sub (tendsto_ofReal_zero.pow 2)) (by norm_num : (1 : ℂ) - 0 ^ 2 ≠ 0)
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    zero_div] at h
  exact h

theorem one_sub_sq_ne_zero' {u : ℝ} (hu : 1 - u ^ 2 ≠ 0) : (1 : ℂ) - (u : ℂ) ^ 2 ≠ 0 := by
  intro h
  apply hu
  exact_mod_cast h

/-- `(1 + u²)/(1 - u²) = 1 + 2u² + o(u²)` (with any value where `u² = 1`). -/
theorem hasJet2_curve_zero (m : ℝ) :
    HasJet2 (fun u => ((m * (1 + u ^ 2) / (1 - u ^ 2) : ℝ) : ℂ)) m 0 (2 * m) := by
  refine ⟨fun u => if 1 - u ^ 2 = 0 then -(m + 2 * m * (u : ℂ) ^ 2) / (u : ℂ) ^ 2 + (m : ℂ) *
      (1 + (u : ℂ) ^ 2) * 0 else 2 * m * ((u : ℂ) ^ 2 / (1 - (u : ℂ) ^ 2)), ?_, fun u => ?_⟩
  · have hev : ∀ᶠ u : ℝ in 𝓝 0, 1 - u ^ 2 ≠ 0 := by
      have : ∀ᶠ u : ℝ in 𝓝 0, u ∈ Set.Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [this] with u hu
      nlinarith [hu.1, hu.2]
    have h := (tendsto_div_one_sub_sq 1).const_mul (2 * (m : ℂ))
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [hev] with u hu
    simp [hu]
  · by_cases hu : 1 - u ^ 2 = 0
    · have hu2 : (u : ℂ) ^ 2 = 1 := by
        have : u ^ 2 = 1 := by linarith
        exact_mod_cast this
      simp only [hu, ite_true, div_zero, mul_zero, ofReal_zero]
      rw [hu2]
      ring
    · have hc := one_sub_sq_ne_zero' hu
      simp only [hu, ite_false]
      push_cast
      field_simp
      ring


/-- `2u/(1 - u²) = 2u + o(u²)` (with any value where `u² = 1`). -/
theorem hasJet2_curve_one (m : ℝ) :
    HasJet2 (fun u => ((2 * m * u / (1 - u ^ 2) : ℝ) : ℂ)) 0 (2 * m) 0 := by
  refine ⟨fun u => if 1 - u ^ 2 = 0 then -(2 * m * (u : ℂ)) / (u : ℂ) ^ 2
      else 2 * m * ((u : ℂ) ^ 1 / (1 - (u : ℂ) ^ 2)), ?_, fun u => ?_⟩
  · have hev : ∀ᶠ u : ℝ in 𝓝 0, 1 - u ^ 2 ≠ 0 := by
      have : ∀ᶠ u : ℝ in 𝓝 0, u ∈ Set.Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [this] with u hu
      nlinarith [hu.1, hu.2]
    have h := (tendsto_div_one_sub_sq 0).const_mul (2 * (m : ℂ))
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [hev] with u hu
    simp [hu]
  · by_cases hu : 1 - u ^ 2 = 0
    · have hu2 : (u : ℂ) ^ 2 = 1 := by
        have : u ^ 2 = 1 := by linarith
        exact_mod_cast this
      simp only [hu, ite_true, div_zero, ofReal_zero]
      rw [hu2]
      ring
    · have hc := one_sub_sq_ne_zero' hu
      simp only [hu, ite_false]
      push_cast
      field_simp
      ring

/-- **The jet of the curve** `p'(u) = p + 2m u e₁ + 2m u² e₀ + o(u²)`, componentwise. -/
theorem hasJet2_curveMomentum (m : ℝ) (ν : Fin 4) :
    HasJet2 (fun u => ((curveMomentum m u ν : ℝ) : ℂ)) (restMomentum m ν)
      ((![0, 2 * m, 0, 0] : Fin 4 → ℂ) ν) ((![2 * m, 0, 0, 0] : Fin 4 → ℂ) ν) := by
  fin_cases ν
  · refine (hasJet2_curve_zero m).of_eq (fun u => ?_) ?_ ?_ ?_ <;>
      simp [curveMomentum, restMomentum]
  · refine (hasJet2_curve_one m).of_eq (fun u => ?_) ?_ ?_ ?_ <;>
      simp [curveMomentum, restMomentum]
  · refine (HasJet2.const 0).of_eq (fun u => ?_) ?_ ?_ ?_ <;>
      simp [curveMomentum, restMomentum]
  · refine (HasJet2.const 0).of_eq (fun u => ?_) ?_ ?_ ?_ <;>
      simp [curveMomentum, restMomentum]

end QED.TwoLoop.ParamNumEval

end
