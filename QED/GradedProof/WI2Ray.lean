/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2RayPoint
public import QED.GradedProof.WI2Diff
public import Mathlib.Topology.Algebra.Polynomial

/-!
# The derivative of a parametric value along a ray

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
steps A2 and A4. For self-energy data `D` and a numerator `N(p, ℓ)` polynomial in `p`, with
admissible cubic quartics at every momentum and the refined bound with exponent three
(`SEData.hasDerivAt_pv_ray`):

`d/dt pv[N(t w)](t w) = pv[∂ₜN] - ∑ᵢ pv^{dup i}[N(t w) · 2 kᵢ·qᵢ](t w)`, `qᵢ = csᵢ w`,

the last values over the data with line `i` doubled (`SEData.dup`).

## Proof

As in `QED.GradedProof.SE2.SEPiece.differentiableAt_line`: near `t₀` put `t = t₀ + tpar u`;
interpolation writes the value at `u` as `-π⁴ ∫_Δ A(x, u)/V(x, u)` for polynomial families, and
`hasDerivAt_integral_upoly` gives the derivative as the integral of the pointwise derivative. The
pointwise derivative is that of the parametric integrand of the joint quartics `J u`; along
`s = tpar u` these form a polynomial path, so the parametric derivative identity applies
(`hasDerivAt_paramIntegrand_tpar`), and the doubled-line merge
(`integral_paramIntegrand_dbl`) turns its second term into the doubled-line values. Finally
`pv_unique` returns to the given quartics.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit QED.GradedProof.WI2
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)

/-- **The derivative of a parametric value along a ray.** -/
theorem hasDerivAt_pv_ray (D : SEData) {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ} {d : ℕ}
    (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ p, ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧ Q.eval = N p)
    (hN3 : ∀ p, RefinedBound D.α D.E 3 (N p)) (w : Fin 4 → ℝ) {t₀ : ℝ}
    (hV : ∀ᶠ t in 𝓝 t₀, D.VPos (D.mom (t • w))) {Qf : ℝ → LoopQuartic}
    (hQf : ∀ᶠ t in 𝓝 t₀, D.Good (Qf t) ∧ (Qf t).eval = N (t • w)) (hQf0 : (Qf t₀).quart = 0)
    {Q' : LoopQuartic} (hQ' : D.Good Q')
    (hQ'e : Q'.eval = fun ℓ => deriv (fun t => N (t • w) ℓ) t₀) :
    HasDerivAt (fun t => D.pv (Qf t) (D.mom (t • w)))
      (D.pv Q' (D.mom (t₀ • w)) - ∑ i, (D.dup i).pv (Cubic.mulLin (Qf t₀)
          (dLineC (D.mom (t₀ • w) i) (D.mom w i)) (dLineL (D.α i) (D.mom w i)))
        (dbl i (D.mom (t₀ • w)))) t₀ := by
  classical
  obtain ⟨m, α, cs, M, E, hm, hcrit⟩ := D
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 6 := ⟨m - 6, by omega⟩
  set D : SEData := ⟨n + 6, α, cs, M, E, hm, hcrit⟩ with hD
  set tt : ℝ → ℝ := fun u => t₀ + tpar u with htt
  set mom : ℝ → Fin (n + 6 + 1) → Fin 4 → ℝ := fun u => D.mom (tt u • w) with hmom_def
  set p₀ := D.mom (t₀ • w) with hp₀
  set q := D.mom w with hq_def
  have hmom : ∀ k μ, IsUPoly (ι := Fin (n + 6) → ℝ) 2 fun _ u => wt u * ((mom u k μ : ℝ) : ℂ) :=
    fun k μ => isUPoly_shift_smul (cs k) t₀ w μ
  have hmomL : ∀ u ∈ Ioo (-1 : ℝ) 1, mom u = p₀ + tpar u • q := fun u _ => by
    funext k μ
    simp only [mom, tt, p₀, q, SEData.mom, D, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  set μS : Measure (Fin (n + 6) → ℝ) := volume.restrict (simplexSet (n + 6)) with hμS
  have htt0 : tt 0 = t₀ := by simp [tt, tpar]
  have htend : Tendsto tt (𝓝 0) (𝓝 t₀) := by
    have h : ContinuousAt tt 0 := continuousAt_const.add continuousAt_tpar
    have h' := h.tendsto
    rwa [htt0] at h'
  have hreg : ∀ᶠ u in 𝓝 (0 : ℝ), D.VPos (mom u) := htend.eventually hV
  have hQfu : ∀ᶠ u in 𝓝 (0 : ℝ), D.Good (Qf (tt u)) ∧ (Qf (tt u)).eval = N (tt u • w) :=
    htend.eventually hQf
  have hIoo : ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm0 : 0 < n + 6 := by omega
  have hspan : ∃ a b, α a 0 * α b 1 - α a 1 * α b 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun k => by
      have := hcrit.noSubdivergenceOfOrder k; omega
  set V : (Fin (n + 6) → ℝ) → ℝ → ℝ := fun x u => symanzikV α (mom u) M (simplexPoint x)
    with hV_def
  have hVpos : ∀ u, D.VPos (mom u) → ∃ c, 0 < c ∧ ∀ᵐ x ∂μS, c ≤ V x u := fun u hu => by
    obtain ⟨c, hc, hV⟩ := hu
    refine ⟨c, hc, ?_⟩
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    exact hV _ hz.1 hz.2 hPD.det_pos.ne'
  have hV₀ : D.VPos p₀ := by
    have := hreg.self_of_nhds
    simp only [mom, htt0] at this
    exact this
  obtain ⟨c0, hc0, hV0⟩ := hVpos 0 hreg.self_of_nhds
  -- interpolation of the numerator
  set F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun u ℓ => N (tt u • w) ℓ with hF_def
  have hF : IsUPoly (2 * d) fun ℓ u => wt u ^ d * F u ℓ := fun ℓ => by
    have h := isUPoly_eval_of_isLoopPoly (hpoly ℓ) (ι := Unit)
      (ℓ := fun _ u _ => tt u • w) fun _ ν => by
        have h1 := isUPoly_shift_smul (ι := Unit) 1 t₀ w ν
        simp only [one_smul] at h1
        exact h1
    exact h ()
  set Qk : Fin (2 * d + 1) → LoopQuartic := fun k => Classical.choose (hQ (tt (node (2 * d) k) • w))
  have hQk : ∀ k, D.Good (Qk k) ∧ (Qk k).quart = 0 ∧ (Qk k).eval = F (node (2 * d) k) :=
    fun k => Classical.choose_spec (hQ (tt (node (2 * d) k) • w))
  set J : ℝ → LoopQuartic := fun u => jointQuartic (2 * d) d Qk u with hJ_def
  have hJe : ∀ u ∈ Ioo (-1 : ℝ) 1, (J u).eval = F u := fun u hu =>
    eval_jointQuartic hF (fun k => (hQk k).2.2) hu
  have hJq : ∀ u, (J u).quart = 0 := fun u =>
    quart_qsum _ _ _ fun k _ => (hQk k).2.1
  have hJg : ∀ u ∈ Ioo (-1 : ℝ) 1, D.Good (J u) := fun u hu =>
    ⟨Or.inr (hJq u), by rw [hJe u hu]; exact (hN3 _).mono le_rfl (by norm_num)⟩
  -- the path in `s = tpar u`
  set c' : Fin (2 * d + 1) → ℂ := fun k => deriv (fun s => lam (2 * d) d (upar s) k) 0
  set J' : LoopQuartic := qsum Finset.univ c' Qk with hJ'_def
  have hJ' : HasQDerivAt (fun s => J (upar s)) J' 0 :=
    hasQDerivAt_qsum Finset.univ (fun k _ => (differentiableAt_lam_upar _ _ k).hasDerivAt) Qk
  have hJ'g : D.Good J' := by
    refine ⟨Or.inr (quart_qsum _ _ _ fun k _ => (hQk k).2.1), ?_⟩
    have e : J'.eval = fun ℓ => ∑ k, c' k * (Qk k).eval ℓ := funext fun ℓ => eval_qsum _ _ _ ℓ
    rw [e]
    exact RefinedBound.sum _ fun k _ => ((hQk k).1.2).const_mul _
  have hJ'e : J'.eval = Q'.eval := by
    rw [hQ'e]
    funext ℓ
    have hpath : ∀ s, (J (upar s)).eval ℓ = N ((t₀ + s) • w) ℓ := fun s => by
      rw [hJe _ (upar_mem s)]
      simp only [F, tt, tpar_upar]
    have hd : HasDerivAt (fun s => (J (upar s)).eval ℓ) (J'.eval ℓ) 0 := by
      have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
        ((differentiableAt_lam_upar (2 * d) d k).hasDerivAt).mul_const ((Qk k).eval ℓ)
      simp only [J, jointQuartic, eval_qsum, J', eval_qsum]
      exact h
    simp only [hpath] at hd
    have hd' : HasDerivAt (fun s => N ((t₀ + s) • w) ℓ) (J'.eval ℓ) (t₀ - t₀) := by
      rw [sub_self]; exact hd
    have h3 := hd'.comp_sub_const t₀ t₀
    simp only [add_sub_cancel] at h3
    exact h3.deriv.symm
  -- the value as an integral of a ratio of polynomial families
  set k3 : ℕ := n + 6 - 3 with hk3
  set A : (Fin (n + 6) → ℝ) → ℝ → ℂ := fun x u => ∑ k, (wt (node (2 * d) k) ^ d *
    (lbasis (2 * d) k).eval (u : ℂ)) * (wt u ^ 4 * paramNum (Qk k) α (mom u) M x)
  have hA : IsUPoly (2 * d + 8) A :=
    IsUPoly.sum _ fun k _ => ((isUPoly_lbasis (2 * d) k).const_mul _).mul
      (isUPoly_paramNum (Qk k) α M mom hmom)
  have hAi : ∀ u, Integrable (fun x => A x u) μS := fun u => by
    refine integrable_finsetSum _ fun l _ => Integrable.const_mul ?_ _
    exact (integrableOn_paramNum_good (D := D) (hQk l).1 _).const_mul _
  set A' : (Fin (n + 6) → ℝ) → ℝ → ℂ := fun x u => A x u * wt u ^ (2 * k3)
  set V' : (Fin (n + 6) → ℝ) → ℝ → ℂ := fun x u =>
    wt u ^ (d + 4) * (wt u ^ 2 * ((V x u : ℝ) : ℂ)) ^ k3
  have hA' : IsUPoly (2 * d + 8 + 2 * (2 * k3)) A' := hA.mul (isUPoly_wt_pow _)
  have hV' : IsUPoly (2 * (d + 4) + k3 * 4) V' :=
    (isUPoly_wt_pow _).mul ((isUPoly_symanzikV α mom M (fun x => simplexPoint x) hmom).pow k3)
  have hrat : ∀ x u, u ∈ Ioo (-1 : ℝ) 1 → V x u ≠ 0 →
      paramIntegrand (J u) α (mom u) M 0 x = A' x u / V' x u ^ 1 := fun x u hu hVx => by
    have hVx' : ((V x u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hVx
    have hw := wt_ne_zero hu
    simp only [J, jointQuartic, paramIntegrand_qsum, A', A, V', Finset.sum_mul, Finset.sum_div,
      pow_one]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [paramIntegrand_zero_eq (Qk k) α (mom u) M (by omega) hVx]
    simp only [lam, V] at hVx' ⊢
    field_simp
    ring
  have hval : ∀ᶠ u in 𝓝 (0 : ℝ), D.pv (Qf (tt u)) (mom u) = -((π : ℂ) ^ 4) *
      ∫ x, A' x u / V' x u ^ 1 ∂μS := by
    filter_upwards [hreg, hIoo, hQfu] with u hreg hu hQu
    obtain ⟨cu, hcu, hVu⟩ := hVpos u hreg
    rw [pv_unique hQu.1 (hJg u hu) (by rw [hQu.2, hJe u hu]) hreg, SEData.pv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hVu] with x hx
    exact hrat x u hu (hcu.trans_le hx).ne'
  -- the derivative at `u = 0`
  have hVm : ∀ u, AEStronglyMeasurable (fun x => ((V x u : ℝ) : ℂ)) μS := fun u =>
    (Complex.measurable_ofReal.comp ((measurable_symanzikV α (mom u) M).comp
      continuous_simplexPoint'.measurable)).aestronglyMeasurable
  set Kq : ℝ → ℝ := fun u => ∑ k, (M k ^ 2 + ∑ μ, mom u k μ ^ 2)
  have hKq0 : ∀ u, 0 ≤ Kq u := fun u => Finset.sum_nonneg fun _ _ => by positivity
  set Ed := 2 * (d + 4) + k3 * 4
  have hK : ∀ k, ∀ᵐ x ∂μS, ‖V' x (node Ed k)‖ ≤ ∑ k', Kq (node Ed k') ^ k3 := fun k => by
    filter_upwards [ae_abs_symanzikV_le α (mom (node Ed k)) M hm0 hspan] with x hx
    have hw1 := norm_wt_le_one (node_mem Ed k)
    simp only [V']
    rw [norm_mul, norm_pow, norm_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc ‖wt (node Ed k)‖ ^ (d + 4) * (‖wt (node Ed k)‖ ^ 2 * |V x (node Ed k)|) ^ k3
        ≤ 1 * (1 * Kq (node Ed k)) ^ k3 := by
          refine mul_le_mul (pow_le_one₀ (norm_nonneg _) hw1) (pow_le_pow_left₀ (by positivity)
            (mul_le_mul (pow_le_one₀ (norm_nonneg _) hw1) hx (abs_nonneg _) zero_le_one) k3)
            (by positivity) zero_le_one
      _ = Kq (node Ed k) ^ k3 := by ring
      _ ≤ ∑ k', Kq (node Ed k') ^ k3 :=
          Finset.single_le_sum (f := fun k' => Kq (node Ed k') ^ k3)
            (fun k' _ => pow_nonneg (hKq0 _) k3) (Finset.mem_univ k)
  have hV0' : ∀ᵐ x ∂μS, c0 ^ k3 ≤ ‖V' x 0‖ := by
    filter_upwards [hV0] with x hx
    simp only [V', wt_zero, one_pow, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ hc0.le (hx.trans (le_abs_self _)) k3
  have hg := (hasDerivAt_integral_upoly (N := 1) hA'
    (fun k => (hAi _).mul_const _) hV'
    (fun k => aestronglyMeasurable_const.mul ((aestronglyMeasurable_const.mul (hVm _)).pow k3))
    hK (pow_pos hc0 k3) hV0').const_mul (-((π : ℂ) ^ 4))
  -- the pointwise derivative
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmom0 : mom 0 = p₀ := by rw [hmomL 0 h0, tpar_zero, zero_smul, add_zero]
  have hk3 : 1 ≤ k3 := by omega
  have hpt : ∀ᵐ x ∂μS, deriv (fun u => A' x u / V' x u ^ 1) 0 =
      paramIntegrand J' α p₀ M 0 x - ∑ i, (simplexPoint x i : ℂ) *
        paramAt (n + 7) (Cubic.mulLin (J 0) (dLineC (p₀ i) (q i)) (dLineL (α i) (q i))) α p₀ M 0
          (simplexPoint x) := by
    filter_upwards [hV0] with x hx
    have hV'0 : V' x 0 ≠ 0 := by
      intro h
      simp only [V', wt_zero, one_pow, one_mul] at h
      have hV0x : V x 0 ≠ 0 := (hc0.trans_le hx).ne'
      exact pow_ne_zero _ (ofReal_ne_zero.mpr hV0x) h
    have hcont : ContinuousAt (fun u => V' x u) 0 := by
      have hp : Continuous fun u : ℝ => (interp (2 * (d + 4) + k3 * 4) V' x).eval (u : ℂ) :=
        (interp (2 * (d + 4) + k3 * 4) V' x).continuous.comp continuous_ofReal
      refine hp.continuousAt.congr ?_
      filter_upwards [hIoo] with u hu
      exact (hV'.eq_interp x u hu).symm
    have hne : ∀ᶠ u in 𝓝 (0 : ℝ), V' x u ≠ 0 := hcont.eventually_ne hV'0
    have hev : (fun u => A' x u / V' x u ^ 1) =ᶠ[𝓝 0]
        fun u => paramIntegrand (J u) α (mom u) M 0 x := by
      filter_upwards [hIoo, hne] with u hu hu'
      refine (hrat x u hu fun hV => hu' ?_).symm
      simp only [V', hV, ofReal_zero, mul_zero, zero_pow (by omega : k3 ≠ 0)]
    have hW : ((symanzikV α p₀ M (simplexPoint x) : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I ≠ 0 := by
      have : V x 0 = symanzikV α p₀ M (simplexPoint x) := by simp only [V, hmom0]
      rw [ofReal_zero, zero_mul, sub_zero, ofReal_ne_zero, ← this]
      exact (hc0.trans_le hx).ne'
    rw [hev.deriv_eq]
    exact (hasDerivAt_paramIntegrand_tpar n hJ' (hJq 0) α p₀ q hmomL M x hW).deriv
  -- the doubled-line values
  have hJ3 : RefinedBound α E 3 (J 0).eval := by rw [hJe 0 h0]; exact hN3 _
  have hIdup : ∀ i, IntegrableOn (paramIntegrand (Cubic.mulLin (J 0) (dLineC (p₀ i) (q i))
      (dLineL (α i) (q i))) (dbl i α) (dbl i p₀) (dbl i M) 0) (simplexSet (n + 6 + 1)) := fun i =>
    integrableOn_pv (D := D.dup i) (good_mulLin D i (hJq 0) hJ3 p₀ q) (hV₀.dup i)
  have hI1 : Integrable (paramIntegrand J' α p₀ M 0) μS := integrableOn_pv hJ'g hV₀
  have hI2 : ∀ i, Integrable (fun x => (simplexPoint x i : ℂ) * paramAt (n + 7)
      (Cubic.mulLin (J 0) (dLineC (p₀ i) (q i)) (dLineL (α i) (q i))) α p₀ M 0
        (simplexPoint x)) μS := fun i =>
    (integral_paramIntegrand_dbl hm0 _ i α p₀ M 0 (hIdup i)).1
  have hdup : ∀ i, (D.dup i).pv (Cubic.mulLin (J 0) (dLineC (p₀ i) (q i)) (dLineL (α i) (q i)))
      (dbl i p₀) = -((π : ℂ) ^ 4) * ∫ x, (simplexPoint x i : ℂ) * paramAt (n + 7)
        (Cubic.mulLin (J 0) (dLineC (p₀ i) (q i)) (dLineL (α i) (q i))) α p₀ M 0
          (simplexPoint x) ∂μS := fun i => by
    show -((π : ℂ) ^ 4) * ∫ x in simplexSet (n + 6 + 1), paramIntegrand _ (dbl i α) (dbl i p₀)
      (dbl i M) 0 x = _
    rw [(integral_paramIntegrand_dbl hm0 _ i α p₀ M 0 (hIdup i)).2]
  have hJQf : (J 0).eval = (Qf t₀).eval := by
    rw [hJe 0 h0, hQf.self_of_nhds.2]
    simp only [F, htt0]
  have hswap : ∀ i, (D.dup i).pv (Cubic.mulLin (J 0) (dLineC (p₀ i) (q i)) (dLineL (α i) (q i)))
      (dbl i p₀) = (D.dup i).pv (Cubic.mulLin (Qf t₀) (dLineC (p₀ i) (q i))
        (dLineL (α i) (q i))) (dbl i p₀) := fun i => by
    have hQ3 : RefinedBound α E 3 (Qf t₀).eval := by rw [← hJQf]; exact hJ3
    refine pv_unique (good_mulLin D i (hJq 0) hJ3 p₀ q) (good_mulLin D i hQf0 hQ3 p₀ q) ?_
      (hV₀.dup i)
    funext ℓ
    simp only [LoopQuartic.eval]
    rw [evalC_mulLin _ (hJq 0), evalC_mulLin _ hQf0]
    have := congrFun hJQf ℓ
    simp only [LoopQuartic.eval] at this
    rw [this]
  have hG : -((π : ℂ) ^ 4) * ∫ x, deriv (fun u => A' x u / V' x u ^ 1) 0 ∂μS =
      D.pv Q' p₀ - ∑ i, (D.dup i).pv (Cubic.mulLin (Qf t₀) (dLineC (p₀ i) (q i))
        (dLineL (α i) (q i))) (dbl i p₀) := by
    rw [integral_congr_ae hpt, integral_sub hI1 (integrable_finsetSum _ fun i _ => hI2 i),
      integral_finsetSum _ fun i _ => hI2 i, ← pv_unique hJ'g hQ' hJ'e hV₀]
    simp only [← hswap, hdup]
    rw [mul_sub, Finset.mul_sum]
    rfl
  -- back to `t`
  have hgu := (hg.congr_of_eventuallyEq hval)
  rw [hG] at hgu
  have hup : upar (t₀ - t₀) = 0 := by simp [upar]
  have hinner : HasDerivAt (fun t => upar (t - t₀)) 1 t₀ := by
    have h : HasDerivAt upar 1 (t₀ - t₀) := by rw [sub_self]; exact hasDerivAt_upar
    exact h.comp_sub_const t₀ t₀
  rw [← hup] at hgu
  have hc := hgu.scomp t₀ hinner
  rw [one_smul] at hc
  refine hc.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Function.comp, mom, tt, tpar_upar, add_sub_cancel]

end QED.GradedProof.SE2.SEData

end
