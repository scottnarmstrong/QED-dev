/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkShareAlg
public import QED.GradedProof.SE2Clause2
public import QED.GradedProof.SE2RealFinal
public import QED.GradedProof.SE2RealLim

/-!
# Set (c), model link: the self-energy input (I1) of the VP share

Helper for (G-ex-s) `QED.ThreeLoop.existsUnique_isVPShareOnShell` and (WI-s)
`QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂` (decision D-58): the input
`QED.ChainProof.SetCLink.VPSEInput`, the analogue of `GEx2.exists_seData` for the
vacuum-polarization family of the self-energy.

The Stage 2 proofs of (G-Σ₂) and of `SEReal` go contraction by contraction: every 1PI one-fermion
contraction of graded order `4` has a covariant limit (`SE2.hasSEForm_zero`, `SE2.hasSEForm_tree`),
differentiable along lines (`SE2.hasSEFormD_zero`, `SE2.hasSEFormD_tree`), with the `♯`-phase
`-1` (`SE2Real.hasSharpLim_zero`, `SE2Real.hasSharpLim_tree`), and these properties are stable
under finite sums. The selection `selSE` only removes terms, so the same traversal gives

* `hasSEForm_selSE`, `hasSEFormD_selSE`, `hasSharpLim_selSE`: the selected order-`4` self-energy
  has a covariant limit, differentiable along lines, `♯`-fixed;
* `selReal_of_hasSharpLim`: a `♯`-fixed limit has real on-shell value and derivative (the proof of
  `SE2Real.seReal_of_hasSharpLim` for an arbitrary family);
* **`vpSEInput`**: under the hypotheses of (G-Σ₂), `VPSEInput P Φ D` for every `D`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.ChainProof.SetCLink

open QED.Graded QED.GradedProof
open QED.WickModel (Params Contraction IsOnePI)

/-- Membership in a filter, for any decidability instance. -/
theorem prop_of_mem_filter {α : Type} {p : α → Prop} {inst : DecidablePred p} {s : Finset α}
    {x : α} (h : x ∈ @Finset.filter α p inst s) : p x :=
  ((@Finset.mem_filter α p inst s x).1 h).2

section Family

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : ∑ g, Φ.coeff g = 0)
  (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0)
include hm₀ hmass hmγ hΛ hPV₁ hPV₂

/-- **The selected order-`4` self-energy has a covariant limit.** -/
theorem hasSEForm_selSE :
    SE2.HasSEForm (Φ.mass Φ.openLine + min (min P.mγ P.Λ) (2 * m₀)) fun ε p α β =>
      selfEnergySelPart { P with ε := ε } Φ D selSE Φ.openLine 2 p α β := by
  classical
  refine SE2.HasSEForm.congr (G := fun ε p α β => (1 / I) * selectedPart { P with ε := ε }
    { Φ with openLine := Φ.openLine } D 1 0 selSE (2 * 2) ![p] ![p] ![] ![α] ![β] ![]) ?_
    fun p _ α β => Eventually.of_forall fun ε => rfl
  refine SE2.HasSEForm.const_mul _ ?_
  unfold selectedPart
  refine SE2.HasSEForm.sum _ fun N _ => SE2.HasSEForm.const_mul _ (SE2.HasSEForm.sum _ fun κ _ =>
    SE2.HasSEForm.sum _ fun g hg => SE2.HasSEForm.sum _ fun C hC => SE2.HasSEForm.const_mul _ ?_)
  have hg4 := (Finset.mem_filter.1 hg).2
  have hC' : IsOnePI C := (prop_of_mem_filter hC).1
  by_cases hg0 : g = 0
  · subst hg0
    exact SE2.hasSEForm_zero (fun C h4 hC => SE2.classForm_of_order_four SE2.classForm_repR
      SE2.classForm_repX SE2.classForm_repV SE2.classForm_repF SE2.classForm_repP0
      SE2.classForm_repP1 SE2.classForm_repC1 SE2.classForm_repC2 h4 C hC) P Φ D Φ.openLine m₀
      hm₀ hmass hmγ hΛ hPV₁ hPV₂ (by rwa [gradedOrder_zero] at hg4) C hC'
  · exact SE2.hasSEForm_tree P Φ D Φ.openLine _ g hg0 hg4 C hC'

/-- **The selected order-`4` self-energy has a limit differentiable along lines.** -/
theorem hasSEFormD_selSE :
    SE2.HasSEFormD (Φ.mass Φ.openLine + min (min P.mγ P.Λ) (2 * m₀)) fun ε p α β =>
      selfEnergySelPart { P with ε := ε } Φ D selSE Φ.openLine 2 p α β := by
  classical
  refine SE2.HasSEFormD.congr (G := fun ε p α β => (1 / I) * selectedPart { P with ε := ε }
    { Φ with openLine := Φ.openLine } D 1 0 selSE (2 * 2) ![p] ![p] ![] ![α] ![β] ![]) ?_
    fun p _ α β => Eventually.of_forall fun ε => rfl
  refine SE2.HasSEFormD.const_mul _ ?_
  unfold selectedPart
  refine SE2.HasSEFormD.sum _ fun N _ => SE2.HasSEFormD.const_mul _
    (SE2.HasSEFormD.sum _ fun κ _ => SE2.HasSEFormD.sum _ fun g hg =>
      SE2.HasSEFormD.sum _ fun C hC => SE2.HasSEFormD.const_mul _ ?_)
  have hg4 := (Finset.mem_filter.1 hg).2
  have hC' : IsOnePI C := (prop_of_mem_filter hC).1
  by_cases hg0 : g = 0
  · subst hg0
    exact SE2.hasSEFormD_zero (fun C h4 hC => SE2.classFormD_of_order_four SE2.classFormD_repR
      SE2.classFormD_repX SE2.classFormD_repV SE2.classFormD_repF SE2.classFormD_repP0
      SE2.classFormD_repP1 SE2.classFormD_repC1 SE2.classFormD_repC2 h4 C hC) P Φ D Φ.openLine
      m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂ (by rwa [gradedOrder_zero] at hg4) C hC'
  · exact SE2.hasSEFormD_tree P Φ D Φ.openLine _ g hg0 hg4 C hC'

/-- **The selected order-`4` self-energy has a `♯`-fixed limit.** -/
theorem hasSharpLim_selSE :
    SE2Real.HasSharpLim (Φ.mass Φ.openLine + min (min P.mγ P.Λ) (2 * m₀)) 1 fun ε p α β =>
      selfEnergySelPart { P with ε := ε } Φ D selSE Φ.openLine 2 p α β := by
  classical
  have h : SE2Real.HasSharpLim (Φ.mass Φ.openLine + min (min P.mγ P.Λ) (2 * m₀)) (-(-1))
      fun ε p α β => (1 / I) * selectedPart { P with ε := ε } { Φ with openLine := Φ.openLine }
        D 1 0 selSE (2 * 2) ![p] ![p] ![] ![α] ![β] ![] := by
    refine SE2Real.HasSharpLim.mul_inv_I ?_
    unfold selectedPart
    refine SE2Real.HasSharpLim.sum _ fun N _ => SE2Real.HasSharpLim.const_mul_conj _ (by simp)
      (SE2Real.HasSharpLim.sum _ fun κ _ => SE2Real.HasSharpLim.sum _ fun g hg =>
        SE2Real.HasSharpLim.sum _ fun C hC =>
          SE2Real.HasSharpLim.const_mul_conj _ (by simp) ?_)
    have hg4 := (Finset.mem_filter.1 hg).2
    have hC' : IsOnePI C := (prop_of_mem_filter hC).1
    by_cases hg0 : g = 0
    · subst hg0
      exact SE2Real.hasSharpLim_zero (fun C h4 hC => SE2Real.classSharp_of_order_four
        SE2Real.classSharp_repR SE2Real.classSharp_repX SE2Real.classSharp_repV
        SE2Real.classSharp_repF SE2Real.classSharp_repP0 SE2Real.classSharp_repP1
        SE2Real.classSharp_repC1 SE2Real.classSharp_repC2 h4 C hC) P Φ D Φ.openLine m₀ hm₀ hmass
        hmγ hΛ hPV₁ hPV₂ (by rwa [gradedOrder_zero] at hg4) C hC'
    · exact SE2Real.hasSharpLim_tree P Φ D Φ.openLine _ g hg0 hg4 C hC'
  rw [neg_neg] at h
  exact h.congr fun p _ α β => Eventually.of_forall fun ε => rfl

end Family

/-- **Real on-shell data from a `♯`-fixed limit**: the proof of
`SE2Real.seReal_of_hasSharpLim` for the selected self-energy. -/
theorem selReal_of_hasSharpLim (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {r : ℝ} (hr : 0 < r)
    (hM : 0 < Φ.mass Φ.openLine)
    (h : SE2Real.HasSharpLim (Φ.mass Φ.openLine + r) 1 fun ε p α β =>
      selfEnergySelPart { P with ε := ε } Φ D selSE Φ.openLine 2 p α β)
    {r' : ℝ} (hr' : 0 < r') {A B : ℝ → ℂ} (hlim : SELimitSel P Φ D r' A B) :
    (A (-Φ.mass Φ.openLine ^ 2) * ((-Φ.mass Φ.openLine : ℝ) : ℂ) +
        B (-Φ.mass Φ.openLine ^ 2) * Φ.mass Φ.openLine).im = 0 ∧
      (deriv (GEx2.shellFun A B (Φ.mass Φ.openLine)) (-Φ.mass Φ.openLine)).im = 0 := by
  obtain ⟨W, hW⟩ := h
  set M := Φ.mass Φ.openLine
  set ρ := min r r' with hρ
  have hρ0 : 0 < ρ := lt_min hr hr'
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
    have hs : SE2Real.sharp (W p) = W p := by rw [h1.2, one_smul]
    rw [hpp] at h2
    exact SE2Real.im_eq_zero_of_limit h1.1 hs hM.ne' (by rw [hpp]; nlinarith) h2
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
  · refine SE2Real.im_deriv_eq_zero ?_
    have hmem : Set.Ioo (-(M + ρ)) 0 ∈ 𝓝 (-M) := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hmem] with z hz
    exact hreal z hz.2 hz.1

/-- **Input (I1).** Under the hypotheses of (G-Σ₂), the selected order-`4` self-energy of any
data `D` has a covariant limit near the open-line shell with real shell value and slope. -/
theorem vpSEInput (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) : VPSEInput P Φ D := by
  set M := Φ.mass Φ.openLine with hMdef
  set r := min (min P.mγ P.Λ) (2 * m₀) with hrdef
  have hM : 0 < M := hm₀.trans_le (hmass _)
  have hr : 0 < r := lt_min (lt_min hmγ hΛ) (by linarith)
  obtain ⟨AB, hAB, -⟩ := SE2.existsUnique_of_hasSEForm hM.ne'
    (hasSEForm_selSE P Φ D m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂)
  set A : ℝ → ℂ := fun s => if h : -(M + r) ^ 2 < s then (AB ⟨s, h⟩).1 else 0
  set B : ℝ → ℂ := fun s => if h : -(M + r) ^ 2 < s then (AB ⟨s, h⟩).2 else 0
  have hlim : SELimitSel P Φ D r A B := by
    intro p hp α β
    have h := hAB p hp α β
    have hp' : -(M + r) ^ 2 < Minkowski.dot p p := hp
    simp only [A, B, hp', dite_true]
    exact h
  have hd : DifferentiableAt ℝ (GEx2.shellFun A B M) (-M) :=
    SE2.differentiableAt_of_hasSEFormD (hasSEFormD_selSE P Φ D m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂)
      hM (by linarith) A B hlim
  obtain ⟨h0, h1⟩ := selReal_of_hasSharpLim P Φ D hr hM
    (hasSharpLim_selSE P Φ D m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂) hr hlim
  set v := A (-M ^ 2) * ((-M : ℝ) : ℂ) + B (-M ^ 2) * M
  set d := deriv (GEx2.shellFun A B M) (-M)
  refine ⟨r, hr, A, B, hlim, v.re, d.re,
    Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact h0), ?_⟩
  have hdre : ((d.re : ℝ) : ℂ) = d :=
    Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact h1.symm)
  rw [hdre]
  exact hd.hasDerivAt

end QED.ChainProof.SetCLink

end
