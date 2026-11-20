/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Twin
public import QED.GradedProof.WI2WardAdd

/-!
# The Ward–Takahashi derivative of a two-slot piece

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the class `F`. For the numerator `∑ₗ cₗ Aₗ (m - k̸₀) G (m - k̸₁) Bₗ` on data whose
external momentum flows only through the two electron lines `e 0`, `e 1`, with the middle matrix
affine along the ray (`G(t r) = G(0) + t Y`):

* `SEData.hasDerivAt_twN`: the entrywise product rule;
* `SEData.hasDerivAt_pvF_twN`: the derivative of the parametric value along `t ↦ t r` is the
  parametric value of the numerator with `Y` in the middle, minus the sum over the two lines of
  the parametric values of the numerator with the zero-momentum insertion on that line, over the
  data with the line doubled (`SEData.hasDerivAt_pv_ray_ward_add`).
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassIntegrable QED.TwoLoop.Bridge QED.GradedProof.WI2
open QED.TwoLoop.LimitCovariance (qsum eval_qsum)

variable (D : SEData) {e : Fin 2 → Fin (D.m + 1)} (mass : ℝ) {ι : Type*} [Fintype ι]
  {A B : ι → Matrix (Fin 4) (Fin 4) ℂ} {c : ι → ℂ}
  {G : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}

theorem twE_smul (r : Fin 4 → ℝ) (t : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 2) :
    D.twE e mass (t • r) ℓ j =
      D.twE e mass 0 ℓ j - t • Dirac.slash (D.mom r (e j)) := by
  simp only [twE, electronNumerator]
  rw [sub_sub, ← Complex.coe_smul, ← Dirac.slash_smul, ← Dirac.slash_add]
  congr 2
  funext μ
  simp only [lineMomentum, mom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_twN (r : Fin 4 → ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (hG : ∀ (t : ℝ) ℓ, G (t • r) ℓ = G 0 ℓ + t • Y) (ℓ : Fin 2 → Fin 4 → ℝ) (t₀ : ℝ)
    (a b : Fin 4) :
    HasDerivAt (fun t : ℝ => D.twN e mass A B c G (t • r) ℓ a b)
      (D.twR e mass A B c (t₀ • r) Y ℓ a b - D.twQ e mass A B c G (t₀ • r) r ℓ 0 a b -
        D.twQ e mass A B c G (t₀ • r) r ℓ 1 a b) t₀ := by
  have hX : ∀ j, HasDerivAt (fun t : ℝ => D.twE e mass (t • r) ℓ j)
      (-Dirac.slash (D.mom r (e j))) t₀ := fun j => by
    have h := ((hasDerivAt_id t₀).smul_const (Dirac.slash (D.mom r (e j)))).const_sub
      (D.twE e mass 0 ℓ j)
    simp only [one_smul] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => D.twE_smul mass r t ℓ j)
  have hGd : HasDerivAt (fun t : ℝ => G (t • r) ℓ) Y t₀ := by
    have h := ((hasDerivAt_id t₀).smul_const Y).const_add (G 0 ℓ)
    simp only [one_smul] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => hG t ℓ)
  have hS := HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    (((((hasDerivAt_const t₀ (A l)).mul (hX 0)).mul hGd).mul (hX 1)).mul
      (hasDerivAt_const t₀ (B l))).const_smul (c l)
  have hS' : HasDerivAt (fun t : ℝ => D.twN e mass A B c G (t • r) ℓ)
      (D.twR e mass A B c (t₀ • r) Y ℓ - D.twQ e mass A B c G (t₀ • r) r ℓ 0 -
        D.twQ e mass A B c G (t₀ • r) r ℓ 1) t₀ := by
    refine (hS.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [twR, twQ, tw, ← Finset.sum_sub_distrib, ← smul_sub]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      simp [Function.update, Pi.mul_apply]
      noncomm_ring
    · simp only [twN, tw, Pi.mul_apply, Pi.smul_apply]
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).hasFDerivAt
    |>.comp_hasDerivAt t₀ hS'

end Deriv

theorem fibre_cases_two (he : e 0 ≠ e 1) (i : Fin (D.m + 1)) :
    (∃ j, e j = i ∧ (Finset.univ.filter fun j => e j = i) = {j}) ∨
      ((∀ j, e j ≠ i) ∧ (Finset.univ.filter fun j => e j = i) = ∅) := by
  have hinj : Function.Injective e := by
    intro j k hjk
    fin_cases j <;> fin_cases k
    · rfl
    · exact absurd hjk he
    · exact absurd hjk.symm he
    · rfl
  by_cases h : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := h
    refine Or.inl ⟨j, rfl, ?_⟩
    ext k
    simp [hinj.eq_iff]
  · simp only [not_exists] at h
    refine Or.inr ⟨h, ?_⟩
    ext k
    simp [h k]

/-- **The Ward–Takahashi derivative of a two-slot piece along a ray.** -/
theorem hasDerivAt_pvF_twN {e₂ : Fin (D.m + 1)} (he : e 0 ≠ e 1) (h20 : e₂ ≠ e 0)
    (h21 : e₂ ≠ e 1) (hE : ∀ j, e j ∈ D.E) (hE2 : e₂ ∈ D.E)
    (hGb : ∀ p, RefinedBoundMat D.α {e₂} 1 (G p)) (hGp : ∀ p, IsLoopPolyMat 2 1 (G p))
    (hGy : ∀ ℓ, IsLoopPolyMat 1 1 fun y => G (y 0) ℓ) (hM : ∀ j, D.M (e j) = mass)
    (h0 : ∀ i, (∀ j, e j ≠ i) → D.cs i = 0) (r : Fin 4 → ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (hG : ∀ (t : ℝ) ℓ, G (t • r) ℓ = G 0 ℓ + t • Y) {t₀ : ℝ}
    (hV : ∀ᶠ t in 𝓝 t₀, D.VPos (D.mom (t • r))) (a b : Fin 4) :
    HasDerivAt (fun t => D.pvF (fun ℓ => D.twN e mass A B c G (t • r) ℓ a b) (D.mom (t • r)))
      (D.pvF (fun ℓ => D.twR e mass A B c (t₀ • r) Y ℓ a b) (D.mom (t₀ • r)) -
        ∑ j, (D.dup (e j)).pvF (fun ℓ => D.twV e mass A B c G (t₀ • r) r ℓ j a b)
          (dbl (e j) (D.mom (t₀ • r)))) t₀ := by
  classical
  have hV₀ := hV.self_of_nhds
  have hQ : ∀ p, ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧
      Q.eval = fun ℓ => D.twN e mass A B c G p ℓ a b := fun p => by
    obtain ⟨Q, hq, hQ⟩ := IsLoopPoly.exists_loopQuartic_cubic
      (D.isLoopPoly_twN e mass A B c G hGp p a b)
    refine ⟨Q, ⟨Or.inr hq, ?_⟩, hq, hQ⟩
    rw [hQ]
    exact (D.refinedBound_twN e mass A B c G he h20 h21 hE hE2 hGb p a b).mono subset_rfl
      (by norm_num)
  set Qf : ℝ → LoopQuartic := fun t => (hQ (t • r)).choose
  have hQf : ∀ t, D.Good (Qf t) ∧ (Qf t).eval = fun ℓ => D.twN e mass A B c G (t • r) ℓ a b :=
    fun t => ⟨(hQ _).choose_spec.1, (hQ _).choose_spec.2.2⟩
  have hQf0 : (Qf t₀).quart = 0 := (hQ _).choose_spec.2.1
  have hQ2 : ∀ j, ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧
      Q.eval = fun ℓ => D.twQ e mass A B c G (t₀ • r) r ℓ j a b := fun j => by
    obtain ⟨Q, hq, hQ⟩ := IsLoopPoly.exists_loopQuartic_cubic
      (D.isLoopPoly_twQ e mass A B c G hGp (t₀ • r) r j a b)
    refine ⟨Q, ⟨Or.inr hq, ?_⟩, hq, hQ⟩
    rw [hQ]
    exact D.refinedBound_twQ e mass A B c G h20 h21 hE hE2 hGb (t₀ • r) r j a b
  choose Q2 hQ2g hQ2q hQ2e using hQ2
  obtain ⟨QR, hRq, hRe⟩ := IsLoopPoly.exists_loopQuartic_cubic
    (D.isLoopPoly_twR e mass A B c (t₀ • r) Y a b)
  have hRg : D.Good QR := ⟨Or.inr hRq, by
    rw [hRe]; exact D.refinedBound_twR e mass A B c he hE (t₀ • r) Y a b⟩
  have hQV : ∀ j, ∃ Q : LoopQuartic, (D.dup (e j)).Good Q ∧
      Q.eval = fun ℓ => D.twV e mass A B c G (t₀ • r) r ℓ j a b := fun j => by
    obtain ⟨Q, hQ⟩ := IsLoopPoly.exists_loopQuartic
      (D.isLoopPoly_twV e mass A B c G hGp (t₀ • r) r j a b)
    refine ⟨Q, ⟨Or.inl (by change 7 ≤ D.m + 1; have := D.hm; omega), ?_⟩, hQ⟩
    rw [hQ]
    exact D.refinedBound_twV e mass A B c G he h20 h21 hE hE2 hGb (t₀ • r) r j a b
  choose QVq hVqg hQVe using hQV
  set F : Fin (D.m + 1) → Finset (Fin 2) := fun i => Finset.univ.filter fun j => e j = i
  set Q₂ : Fin (D.m + 1) → LoopQuartic := fun i => qsum (F i) (fun _ => 1) Q2
  set QV : Fin (D.m + 1) → LoopQuartic := fun i => qsum (F i) (fun _ => 1) QVq
  have hQ₂e : ∀ i ℓ, (Q₂ i).eval ℓ = ∑ j ∈ F i, D.twQ e mass A B c G (t₀ • r) r ℓ j a b :=
    fun i ℓ => by simp only [Q₂, eval_qsum, one_mul, hQ2e]
  have hQVe' : ∀ i ℓ, (QV i).eval ℓ = ∑ j ∈ F i, D.twV e mass A B c G (t₀ • r) r ℓ j a b :=
    fun i ℓ => by simp only [QV, eval_qsum, one_mul, hQVe]
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
  have hder : ∀ ℓ, deriv (fun t => D.twN e mass A B c G (t • r) ℓ a b) t₀ =
      -∑ i, (Q₂ i).eval ℓ + QR.eval ℓ := fun ℓ => by
    rw [(D.hasDerivAt_twN mass r Y hG ℓ t₀ a b).deriv, hRe]
    simp only [hQ₂e, F]
    rw [Finset.sum_fiberwise Finset.univ e fun j => D.twQ e mass A B c G (t₀ • r) r ℓ j a b,
      Fin.sum_univ_two]
    ring
  have hQVi : ∀ i ℓ, (QV i).eval ℓ =
      ((Minkowski.dot (lineMomentum D.α (D.mom (t₀ • r)) i ℓ)
        (lineMomentum D.α (D.mom (t₀ • r)) i ℓ) + D.M i ^ 2 : ℝ) : ℂ) * (Q₂ i).eval ℓ +
      D.twN e mass A B c G (t₀ • r) ℓ a b * (dLineC (D.mom (t₀ • r) i) (D.mom r i) +
        linF (dLineL (D.α i) (D.mom r i)) (loopComp ℓ)) := fun i ℓ => by
    rw [hQVe' i ℓ, hQ₂e i ℓ]
    rcases D.fibre_cases_two he i with ⟨j, rfl, hF⟩ | ⟨hne, hF⟩
    · simp only [F] at hF ⊢
      rw [hF, Finset.sum_singleton, Finset.sum_singleton, twV_eq, dLineC_add_linF, hM]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
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
  have h := hasDerivAt_pv_ray_ward_add D
    (fun ℓ => D.isLoopPoly_twN_mom e mass A B c G hGy ℓ a b) hQ
    (fun p => D.refinedBound_twN e mass A B c G he h20 h21 hE hE2 hGb p a b) r hV
    (Filter.Eventually.of_forall hQf) hQf0 hQ₂g hRg hder hQVg hQVi
  have hfun : (fun t => D.pvF (fun ℓ => D.twN e mass A B c G (t • r) ℓ a b)
      (D.mom (t • r))) =ᶠ[𝓝 t₀] fun t => D.pv (Qf t) (D.mom (t • r)) := by
    filter_upwards [hV] with t ht
    exact pvF_eq (hQf t).1 (hQf t).2 ht
  refine (h.congr_of_eventuallyEq hfun).congr_deriv ?_
  have hpv : ∀ i, (D.dup i).pv (QV i) (dbl i (D.mom (t₀ • r))) =
      ∑ j ∈ F i, (D.dup (e j)).pvF (fun ℓ => D.twV e mass A B c G (t₀ • r) r ℓ j a b)
        (dbl (e j) (D.mom (t₀ • r))) := fun i => by
    have hl := pv_qsum (D := D.dup i) (F i) (fun _ => 1) QVq (q := dbl i (D.mom (t₀ • r)))
      fun j hj => by
        obtain rfl : e j = i := (Finset.mem_filter.mp hj).2
        exact integrableOn_pv (hVqg j) (hV₀.dup _)
    rw [show QV i = qsum (F i) (fun _ => 1) QVq from rfl, hl]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain rfl : e j = i := (Finset.mem_filter.mp hj).2
    rw [one_mul, pvF_eq (hVqg j) (hQVe j) (hV₀.dup _)]
  rw [pvF_eq hRg hRe hV₀]
  congr 1
  simp only [hpv, F]
  exact Finset.sum_fiberwise Finset.univ e fun j => (D.dup (e j)).pvF
    (fun ℓ => D.twV e mass A B c G (t₀ • r) r ℓ j a b) (dbl (e j) (D.mom (t₀ • r)))

end QED.GradedProof.SE2.SEData

end
