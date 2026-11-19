/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealSharp
public import QED.GradedProof.SE2Clause3
public import QED.GradedProof.GEx2Inputs

/-!
# Limits with a `♯`-symmetry, and the reality of the on-shell self-energy data

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`.

* `HasSharpLim T c G`: on the region `p² > -T²` the family `G ε p` of matrices converges as
  `ε → 0⁺` to a matrix `W p` with `W(p)♯ = c W(p)` (`QED.GradedProof.SE2Real.sharp`). It is stable
  under sums, multiplication by real constants (`const_mul_real`) and by `1/i` (`mul_inv_I`, which
  flips the sign of `c`), and congruence.
* `seReal_of_hasSharpLim`: if the order-`4` self-energy of flavour `f` has a limit with
  `W♯ = W` on a region `p² > -(M_f + r)²`, then `SEReal` holds: every pair `A, B` with the limit
  property is real near the shell (the trace projections, `im_eq_zero_of_sharp_seForm`), so the
  on-shell value and the derivative of `Σ(z) = A(-z²) z + B(-z²) M_f` at `z = -M_f` are real.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2Real

open QED.Graded
open QED.WickModel (Params)

/-- **A `♯`-symmetric limit below `-T²`**: the family converges to `W` with `W♯ = c W`. -/
def HasSharpLim (T : ℝ) (c : ℂ) (G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∃ W : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ, ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p →
    (∀ α β : Fin 4, Tendsto (fun ε => G ε p α β) (𝓝[>] 0) (𝓝 (W p α β))) ∧
      sharp (W p) = c • W p

namespace HasSharpLim

variable {T : ℝ} {c : ℂ} {G H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hG : HasSharpLim T c G) (hH : HasSharpLim T c H) :
    HasSharpLim T c fun ε p α β => G ε p α β + H ε p α β := by
  obtain ⟨W, hW⟩ := hG
  obtain ⟨W', hW'⟩ := hH
  refine ⟨fun p => W p + W' p, fun p hp => ⟨fun α β => ?_, ?_⟩⟩
  · exact ((hW p hp).1 α β).add ((hW' p hp).1 α β)
  · rw [sharp_add, (hW p hp).2, (hW' p hp).2, smul_add]

theorem zero : HasSharpLim T c fun _ _ _ _ => 0 :=
  ⟨fun _ => 0, fun _ _ => ⟨fun _ _ => tendsto_const_nhds, by rw [sharp_zero, smul_zero]⟩⟩

/-- Multiplication by a constant fixed by complex conjugation. -/
theorem const_mul_conj (k : ℂ) (hk : starRingEnd ℂ k = k) (hG : HasSharpLim T c G) :
    HasSharpLim T c fun ε p α β => k * G ε p α β := by
  obtain ⟨W, hW⟩ := hG
  refine ⟨fun p => k • W p, fun p hp => ⟨fun α β => ?_, ?_⟩⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact ((hW p hp).1 α β).const_mul _
  · rw [sharp_smul, hk, (hW p hp).2, smul_comm]

/-- Multiplication by a real constant. -/
theorem const_mul_real (r : ℝ) (hG : HasSharpLim T c G) :
    HasSharpLim T c fun ε p α β => (r : ℂ) * G ε p α β :=
  const_mul_conj _ (Complex.conj_ofReal r) hG

/-- Multiplication by `1/i` flips the sign of the phase. -/
theorem mul_inv_I (hG : HasSharpLim T c G) :
    HasSharpLim T (-c) fun ε p α β => (1 / I) * G ε p α β := by
  obtain ⟨W, hW⟩ := hG
  refine ⟨fun p => (1 / I) • W p, fun p hp => ⟨fun α β => ?_, ?_⟩⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact ((hW p hp).1 α β).const_mul _
  · rw [sharp_smul, (hW p hp).2, smul_smul, smul_smul]
    congr 1
    simp only [one_div, Complex.inv_I, map_neg, Complex.conj_I]
    ring

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ s, HasSharpLim T c (G i)) :
    HasSharpLim T c fun ε p α β => ∑ i ∈ s, G i ε p α β := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : HasSharpLim T c fun _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : HasSharpLim T c G)
    (h : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p α β = H ε p α β) : HasSharpLim T c H := by
  obtain ⟨W, hW⟩ := hG
  exact ⟨W, fun p hp => ⟨fun α β => ((hW p hp).1 α β).congr' (h p hp α β), (hW p hp).2⟩⟩

end HasSharpLim

/-! ### The on-shell data -/

/-- A `♯`-fixed limit of the form `A p̸ + B M` with `p² ≠ 0`, `M ≠ 0` has real `A`, `B`. -/
theorem im_eq_zero_of_limit {p : Fin 4 → ℝ} {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {W : Matrix (Fin 4) (Fin 4) ℂ} (hW : ∀ α β : Fin 4,
      Tendsto (fun ε => G ε p α β) (𝓝[>] 0) (𝓝 (W α β))) (hs : sharp W = W)
    {a b : ℂ} {M : ℝ} (hM : M ≠ 0) (hp : Minkowski.dot p p ≠ 0)
    (hab : ∀ α β : Fin 4, Tendsto (fun ε => G ε p α β) (𝓝[>] 0)
      (𝓝 ((a • Dirac.slash p + (b * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) :
    a.im = 0 ∧ b.im = 0 := by
  have he : W = a • Dirac.slash p + (b * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext α β
    exact tendsto_nhds_unique (hW α β) (hab α β)
  rw [he] at hs
  obtain ⟨ha, hb⟩ := im_eq_zero_of_sharp_seForm hp hs
  refine ⟨ha, ?_⟩
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at hb
  exact (mul_eq_zero.1 hb).resolve_right hM

/-- A function real on a neighbourhood of `x` has a real derivative at `x`. -/
theorem im_deriv_eq_zero {g : ℝ → ℂ} {x : ℝ} (h : ∀ᶠ z in 𝓝 x, (g z).im = 0) :
    (deriv g x).im = 0 := by
  by_cases hd : DifferentiableAt ℝ g x
  · have h1 : HasDerivAt (fun z => (g z).im) (deriv g x).im x := by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt
      convert this using 1
      · funext z
        simp
      · simp
    have h2 : HasDerivAt (fun z => (g z).im) 0 x :=
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h
    exact h1.unique h2
  · rw [deriv_zero_of_not_differentiableAt hd]
    simp

/-- **`SEReal` from a `♯`-fixed limit of the order-`4` self-energy.** -/
theorem seReal_of_hasSharpLim (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) {r : ℝ} (hr : 0 < r)
    (hM : 0 < Φ.mass f)
    (h : HasSharpLim (Φ.mass f + r) 1 fun ε p α β =>
      selfEnergyPart { P with ε := ε } Φ D f 2 p α β) :
    GEx2.SEReal P Φ D f := by
  intro r' hr' A B hlim
  obtain ⟨W, hW⟩ := h
  set M := Φ.mass f
  set ρ := min r r' with hρ
  have hρ0 : 0 < ρ := lt_min hr hr'
  -- reality of `A, B` at `-t²` for `t` near `M`
  have key : ∀ t : ℝ, 0 < t → t < M + ρ → (A (-t ^ 2)).im = 0 ∧ (B (-t ^ 2)).im = 0 := by
    intro t ht htM
    set p := t • SE2.timeVec
    have hpp : Minkowski.dot p p = -t ^ 2 := SE2.dot_smul_timeVec t
    have hlt : ∀ R : ℝ, ρ ≤ R → -(M + R) ^ 2 < Minkowski.dot p p := by
      intro R hR
      rw [hpp]
      nlinarith
    have h1 := hW p (hlt r (min_le_left _ _))
    have h2 := hlim p (hlt r' (min_le_right _ _))
    have hs : sharp (W p) = W p := by rw [h1.2, one_smul]
    rw [hpp] at h2
    exact im_eq_zero_of_limit h1.1 hs hM.ne' (by rw [hpp]; nlinarith) h2
  have hreal : ∀ z : ℝ, z < 0 → -(M + ρ) < z → (GEx2.shellFun A B M z).im = 0 := by
    intro z hz0 hz1
    obtain ⟨ha, hb⟩ := key (-z) (by linarith) (by linarith)
    rw [neg_sq] at ha hb
    simp only [GEx2.shellFun, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, ha, hb]
    ring
  constructor
  · have := hreal (-M) (by linarith) (by linarith)
    simpa only [GEx2.shellFun, Complex.ofReal_neg, neg_sq] using this
  · refine im_deriv_eq_zero ?_
    have hmem : Set.Ioo (-(M + ρ)) 0 ∈ 𝓝 (-M) := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hmem] with z hz
    exact hreal z hz.2 hz.1

end QED.GradedProof.SE2Real

end
