/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals of coordinate derivatives over the orthant vanish

The analytic core of integration by parts for Lee–Pomeransky integrals. If `φ` has partial
derivative `φ'` in the coordinate `xᵢ` on the open orthant, and both `φ'` and `φ / xᵢ` are
integrable on the orthant, then `∫_{(0,∞)^N} φ' = 0`.

No boundary hypothesis is needed: integrability of `φ / xᵢ` forces the boundary values at
`xᵢ → 0` and `xᵢ → ∞` to vanish. In one variable, the substitution `t = eˢ` turns
`∫₀^∞ g'(t) dt` into `∫_ℝ (g ∘ exp)'`, and `g ∘ exp` is integrable on `ℝ` exactly when
`g(t) / t` is integrable on `(0, ∞)`; Mathlib's `integral_eq_zero_of_hasDerivAt_of_integrable`
then applies. In `N` variables we split off the coordinate `xᵢ` and use Fubini.

For a Lee–Pomeransky integrand `φ = xᵢ · x ^ (ν - 1) G ^ (-d / 2)` the quotient `φ / xᵢ` is the
integrand at `(ν, d)` itself, so the hypotheses are exactly the convergence of the integrals
that appear in the identity.

## Main results

* `QED.DimReg.integral_Ioi_eq_zero_of_hasDerivAt`: the one-variable statement.
* `QED.DimReg.integral_posOrthant_eq_zero_of_hasDerivAt`: the `N`-variable statement.
-/

public section

open MeasureTheory Set Real

namespace QED.DimReg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **One-variable vanishing.** If `g` has derivative `g'` on `(0, ∞)`, and `g'` and
`t⁻¹ • g` are integrable on `(0, ∞)`, then `∫₀^∞ g' = 0`. -/
theorem integral_Ioi_eq_zero_of_hasDerivAt {g g' : ℝ → E}
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (g' t) t) (hg' : IntegrableOn g' (Ioi 0))
    (hg : IntegrableOn (fun t => t⁻¹ • g t) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), g' t = 0 := by
  rw [← integral_comp_exp]
  refine integral_eq_zero_of_hasDerivAt_of_integrable (f := g ∘ exp) (fun s => ?_)
    ((integrable_comp_exp g').mpr hg') ?_
  · exact (hd (exp s) (exp_pos s)).scomp s (hasDerivAt_exp s)
  · refine ((integrable_comp_exp _).mpr hg).congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp, smul_smul, mul_inv_cancel₀ (exp_pos s).ne', one_smul]

theorem preimage_piFinSuccAbove_posOrthant {n : ℕ} (i : Fin (n + 1)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) ⁻¹'
      (Ioi 0 ×ˢ posOrthant n) = posOrthant (n + 1) := by
  ext x
  simp only [mem_preimage, mem_prod, mem_posOrthant, mem_Ioi,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply, Fin.removeNth]
  exact (Fin.forall_iff_succAbove (P := fun j => 0 < x j) i).symm

/-- **Vanishing of integrals of coordinate derivatives over the orthant.** If for every `x`
in the orthant `t ↦ φ (update x i t)` has derivative `φ' x` at `t = xᵢ`, and `φ'` and
`x ↦ xᵢ⁻¹ • φ x` are integrable on the orthant, then `∫_{(0,∞)^N} φ' = 0`. -/
theorem integral_posOrthant_eq_zero_of_hasDerivAt [CompleteSpace E] {N : ℕ} (i : Fin N)
    {φ φ' : (Fin N → ℝ) → E}
    (hd : ∀ x ∈ posOrthant N, HasDerivAt (fun t => φ (Function.update x i t)) (φ' x) (x i))
    (hφ' : IntegrableOn φ' (posOrthant N))
    (hφ : IntegrableOn (fun x => (x i)⁻¹ • φ x) (posOrthant N)) :
    ∫ x in posOrthant N, φ' x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i.pos; omega⟩
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hp : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ => ℝ) i
  have he : ∀ z : ℝ × (Fin n → ℝ), e.symm z = Fin.insertNth i z.1 z.2 := fun _ => rfl
  rw [← preimage_piFinSuccAbove_posOrthant i] at hφ' hφ ⊢
  have A1 : IntegrableOn ((fun z => φ' (e.symm z)) ∘ e) (e ⁻¹' (Ioi 0 ×ˢ posOrthant n)) := by
    convert hφ' using 1
    funext x
    simp
  have A2 : IntegrableOn ((fun z : ℝ × (Fin n → ℝ) => (z.1)⁻¹ • φ (e.symm z)) ∘ e)
      (e ⁻¹' (Ioi 0 ×ˢ posOrthant n)) := by
    convert hφ using 1
    funext x
    simp only [Function.comp, e.symm_apply_apply]
    rfl
  have hφ'' := (hp.integrableOn_comp_preimage e.measurableEmbedding).mp A1
  have hφ2 := (hp.integrableOn_comp_preimage e.measurableEmbedding).mp A2
  have hint : ∫ x in e ⁻¹' (Ioi 0 ×ˢ posOrthant n), φ' x =
      ∫ z in Ioi 0 ×ˢ posOrthant n, φ' (e.symm z) := by
    rw [← hp.setIntegral_preimage_emb e.measurableEmbedding]
    simp
  rw [hint]
  unfold IntegrableOn at hφ'' hφ2
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hφ'' hφ2 ⊢
  rw [integral_prod_symm _ hφ'']
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [hφ''.prod_left_ae, hφ2.prod_left_ae,
    ae_restrict_mem (measurableSet_posOrthant n)] with y h1 h2 hy
  refine integral_Ioi_eq_zero_of_hasDerivAt (g := fun t => φ (e.symm (t, y))) (fun t ht => ?_)
    h1 h2
  have hx : e.symm (t, y) ∈ posOrthant (n + 1) := by
    rw [← preimage_piFinSuccAbove_posOrthant i, mem_preimage, e.apply_symm_apply]
    exact ⟨ht, hy⟩
  have := hd _ hx
  simpa [he, Fin.update_insertNth] using this

end QED.DimReg
