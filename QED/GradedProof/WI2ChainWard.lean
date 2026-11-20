/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2ChainNum

/-!
# The Ward–Takahashi derivative of an open-chain self-energy piece

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the classes `R` and `X`: `SEData.hasDerivAt_pvF_chN`. On self-energy data whose
external momentum flows only through the three electron lines `e j` of an open chain (the other
lines have `cᵢ = 0`), the derivative along the ray `t ↦ t r` of the parametric value of an entry
of the chain is minus the sum over the three electron lines of the parametric values, over the
data with that line doubled, of the chain with the insertion `(m - k̸) (cₑⱼ r)̸ (m - k̸)` in its
slot. This is `SEData.hasDerivAt_pv_ray_ward` with the line terms grouped by the fibres of `e`
(each fibre has at most one element), the derivative of the chain from `hasDerivAt_chainAt_line`,
and the insertion identity `chainAt_update_ins`.
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassIntegrable QED.TwoLoop.Bridge QED.GradedProof.WI2
open QED.TwoLoop.LimitCovariance (qsum eval_qsum)

variable (D : SEData) {e : Fin 3 → Fin (D.m + 1)} (w : (Fin 4 → Fin 4) → ℂ) (mass : ℝ)

theorem chE_smul (r : Fin 4 → ℝ) (t : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    D.chE e mass (t • r) ℓ = fun j => electronNumerator mass
      (lineMomentum D.α (D.mom 0) (e j) ℓ + t • D.mom r (e j)) := by
  funext j
  simp only [chE]
  congr 1
  funext μ
  simp only [lineMomentum, mom, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  ring

theorem fibre_cases (he : Function.Injective e) (i : Fin (D.m + 1)) :
    (∃ j, e j = i ∧ (Finset.univ.filter fun j => e j = i) = {j}) ∨
      ((∀ j, e j ≠ i) ∧ (Finset.univ.filter fun j => e j = i) = ∅) := by
  by_cases h : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := h
    refine Or.inl ⟨j, rfl, ?_⟩
    ext k
    simp [he.eq_iff]
  · simp only [not_exists] at h
    refine Or.inr ⟨h, ?_⟩
    ext k
    simp [h k]

/-- **The Ward–Takahashi derivative of an open-chain piece along a ray.** -/
theorem hasDerivAt_pvF_chN (he : Function.Injective e) (hE : ∀ j, e j ∈ D.E)
    (hM : ∀ j, D.M (e j) = mass) (h0 : ∀ i, (∀ j, e j ≠ i) → D.cs i = 0) (r : Fin 4 → ℝ)
    {t₀ : ℝ} (hV : ∀ᶠ t in 𝓝 t₀, D.VPos (D.mom (t • r))) (a b : Fin 4) :
    HasDerivAt (fun t => D.pvF (fun ℓ => D.chN e w mass (t • r) ℓ a b) (D.mom (t • r)))
      (-∑ j, (D.dup (e j)).pvF (fun ℓ => D.chV e w mass (t₀ • r) r ℓ j a b)
        (dbl (e j) (D.mom (t₀ • r)))) t₀ := by
  classical
  have hV₀ := hV.self_of_nhds
  have hQ := fun p => D.good_chN w mass he hE p a b
  set Qf : ℝ → LoopQuartic := fun t => (hQ (t • r)).choose
  have hQf : ∀ t, D.Good (Qf t) ∧ (Qf t).eval = fun ℓ => D.chN e w mass (t • r) ℓ a b :=
    fun t => ⟨(hQ _).choose_spec.1, (hQ _).choose_spec.2.2⟩
  have hQf0 : (Qf t₀).quart = 0 := (hQ _).choose_spec.2.1
  choose Q2 hQ2g hQ2q hQ2e using fun j => D.good_chQ w mass he hE (t₀ • r) r j a b
  choose QVq hVqg hQVe using fun j => D.good_chV w mass he hE (t₀ • r) r j a b
  set F : Fin (D.m + 1) → Finset (Fin 3) := fun i => Finset.univ.filter fun j => e j = i
  set Q₂ : Fin (D.m + 1) → LoopQuartic := fun i => qsum (F i) (fun _ => 1) Q2
  set QV : Fin (D.m + 1) → LoopQuartic := fun i => qsum (F i) (fun _ => 1) QVq
  have hQ₂e : ∀ i ℓ, (Q₂ i).eval ℓ = ∑ j ∈ F i, D.chQ e w mass (t₀ • r) r ℓ j a b :=
    fun i ℓ => by
      simp only [Q₂, eval_qsum, one_mul, hQ2e]
  have hQVe' : ∀ i ℓ, (QV i).eval ℓ = ∑ j ∈ F i, D.chV e w mass (t₀ • r) r ℓ j a b :=
    fun i ℓ => by
      simp only [QV, eval_qsum, one_mul, hQVe]
  have hQ₂g : ∀ i, D.Good (Q₂ i) := fun i => by
    refine ⟨Or.inr (quart_qsum _ _ _ fun j _ => hQ2q j), ?_⟩
    rw [show (Q₂ i).eval = fun ℓ => ∑ j ∈ F i, (Q2 j).eval ℓ from
      funext fun ℓ => by simp only [Q₂, eval_qsum, one_mul]]
    exact RefinedBound.sum _ fun j _ => (hQ2g j).2
  have hQVg : ∀ i, (D.dup i).Good (QV i) := fun i => by
    refine ⟨Or.inl (by change 7 ≤ D.m + 1; have := D.hm; omega), ?_⟩
    rw [show (QV i).eval = fun ℓ => ∑ j ∈ F i, (QVq j).eval ℓ from
      funext fun ℓ => by simp only [QV, eval_qsum, one_mul]]
    refine RefinedBound.sum _ fun j hj => ?_
    obtain rfl : e j = i := (Finset.mem_filter.mp hj).2
    exact (hVqg j).2
  have hder : ∀ ℓ, deriv (fun t => D.chN e w mass (t • r) ℓ a b) t₀ =
      -∑ i, (Q₂ i).eval ℓ := fun ℓ => by
    have h := hasDerivAt_chainAt_line w mass (fun j => lineMomentum D.α (D.mom 0) (e j) ℓ)
      (fun j => D.mom r (e j)) t₀ a b
    simp only [chN, D.chE_smul]
    rw [h.deriv]
    simp only [hQ₂e, F]
    rw [Finset.sum_fiberwise Finset.univ e fun j => D.chQ e w mass (t₀ • r) r ℓ j a b]
    simp only [chQ, D.chE_smul]
  have hQVi : ∀ i ℓ, (QV i).eval ℓ =
      ((Minkowski.dot (lineMomentum D.α (D.mom (t₀ • r)) i ℓ)
        (lineMomentum D.α (D.mom (t₀ • r)) i ℓ) + D.M i ^ 2 : ℝ) : ℂ) * (Q₂ i).eval ℓ +
      D.chN e w mass (t₀ • r) ℓ a b * (dLineC (D.mom (t₀ • r) i) (D.mom r i) +
        linF (dLineL (D.α i) (D.mom r i)) (loopComp ℓ)) := fun i ℓ => by
    rw [hQVe' i ℓ, hQ₂e i ℓ]
    rcases D.fibre_cases he i with ⟨j, rfl, hF⟩ | ⟨hne, hF⟩
    · simp only [F] at hF ⊢
      have hk : D.chE e mass (t₀ • r) ℓ j =
          electronNumerator mass (lineMomentum D.α (D.mom (t₀ • r)) (e j) ℓ) := rfl
      rw [hF, Finset.sum_singleton, Finset.sum_singleton, chV, hk, chainAt_update_ins, ← hk,
        chainAt_update_self, dLineC_add_linF, hM]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, chQ, chN]
      have hd : Minkowski.dot (D.mom r (e j)) (lineMomentum D.α (D.mom (t₀ • r)) (e j) ℓ) =
          Minkowski.dot (fun μ => ∑ s, D.α (e j) s * ℓ s μ + D.mom (t₀ • r) (e j) μ)
            (D.mom r (e j)) := by
        simp only [Minkowski.dot_eq, lineMomentum]
        ring
      rw [hd]
      push_cast
      ring
    · simp only [F] at hF ⊢
      have hr : D.mom r i = 0 := by simp [mom, h0 i hne]
      rw [hF, Finset.sum_empty, Finset.sum_empty, hr]
      simp [dLineC, dLineL, linF, Minkowski.lower, Minkowski.dot_eq]
  have h := hasDerivAt_pv_ray_ward D (fun ℓ => D.isLoopPoly_chN_mom w mass ℓ a b)
    hQ (fun p => (D.refinedBound_chN w mass he hE p a b)) r hV
    (Filter.Eventually.of_forall hQf) hQf0 hQ₂g hder hQVg hQVi
  have hfun : (fun t => D.pvF (fun ℓ => D.chN e w mass (t • r) ℓ a b) (D.mom (t • r))) =ᶠ[𝓝 t₀]
      fun t => D.pv (Qf t) (D.mom (t • r)) := by
    filter_upwards [hV] with t ht
    exact pvF_eq (hQf t).1 (hQf t).2 ht
  refine (h.congr_of_eventuallyEq hfun).congr_deriv ?_
  congr 1
  have hpv : ∀ i, (D.dup i).pv (QV i) (dbl i (D.mom (t₀ • r))) =
      ∑ j ∈ F i, (D.dup (e j)).pvF (fun ℓ => D.chV e w mass (t₀ • r) r ℓ j a b)
        (dbl (e j) (D.mom (t₀ • r))) := fun i => by
    have hl := pv_qsum (D := D.dup i) (F i) (fun _ => 1) QVq (q := dbl i (D.mom (t₀ • r)))
      fun j hj => by
        obtain rfl : e j = i := (Finset.mem_filter.mp hj).2
        exact integrableOn_pv (hVqg j) (hV₀.dup _)
    rw [show QV i = qsum (F i) (fun _ => 1) QVq from rfl, hl]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain rfl : e j = i := (Finset.mem_filter.mp hj).2
    rw [one_mul, pvF_eq (hVqg j) (hQVe j) (hV₀.dup _)]
  simp only [hpv, F]
  exact Finset.sum_fiberwise Finset.univ e fun j => (D.dup (e j)).pvF
    (fun ℓ => D.chV e w mass (t₀ • r) r ℓ j a b) (dbl (e j) (D.mom (t₀ • r)))

end QED.GradedProof.SE2.SEData

end
