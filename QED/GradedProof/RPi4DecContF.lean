/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecSegCont
public import QED.GradedProof.RPi4DecWeak

/-!
# (R-Π₄) step L9: the one-loop functional is continuous at `s = 0` (`DecContD`)

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
regularity input `DecContD` of `QED.GradedProof.RPi4.dec_scalAff_of_weak`. The limit `fLim` of
the weighted mass-derivative block is, on the region, a finite sum of eight-line parametric values
(`QED.GradedProof.RPi4.fLim_eq_fbVal`), each continuous along a segment
(`QED.GradedProof.RPi4.dec_segCont_kinds`); the tilted vectors `k'(s)` of an interval are the
points of one segment, with a parameter `decTiltU` continuous in `s`.

* `dec_segCont_fVal5`, …, `dec_segCont_fbVal`: the one-loop pieces, as in `RPi4UnifF`;
* `decTiltU`, `dec_tiltVec_eq_lineK`, `dec_continuousOn_tilt`: the tilted vectors along the
  segment, continuously in `s`;
* `dec_continuousOn_fLim_tilt`: `s ↦ fLim δ (k'(s))` is continuous on `[S₀, S]`;
* `dec_continuousAt_projS_fLim`: the projection `projS (fLim δ)` is continuous at every `s` of
  the region;
* **`dec_contD : DecContD P.e`**.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.CountertermLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Graded (Counterterms)
open QED.WickModel (Params)

/-! ### The one-loop pieces along the segment -/

section Pieces

variable {m₀ : ℝ} (hm₀ : 0 < m₀) {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(4 * m₀ ^ 2) < S₀)
  (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
include hm₀ hS₀ hseg

theorem dec_segCont_fVal5 (Ms : Fin 5 → ℝ) (hMs : ∀ l, m₀ ≤ Ms l) (b : Fin 5 → Bool)
    (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j)
    {d : ℕ} (hpoly : ∀ q i j, IsLoopPoly 1 d fun y => N (y 0) q i j) (i j : Fin 4) :
    DecSegCont k₀ w fun k => fVal5 m₀ Ms b N k i j := by
  have hsq : ∀ l, m₀ ^ 2 ≤ Ms l ^ 2 := fun l => pow_le_pow_left₀ hm₀.le (hMs l) 2
  have hM : ∀ i, m₀ ^ 2 ≤ (![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] : Fin 8 → ℝ) i ^ 2 := by
    intro i
    fin_cases i
    exacts [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4, le_rfl, le_rfl, le_rfl]
  have hout : ∀ c : Bool, kd c ≠ .out := fun c => by cases c <;> decide
  have h := dec_segCont_kinds (by norm_num) (kinds5 b) (fun i => by
      fin_cases i <;> simp [kinds5, hout])
    ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, m₀, m₀, m₀] hm₀ hm₀ (fun i _ => hM i) (fun i _ => hM i)
    (crit_kinds5 _) (by decide) (ne_aux_kinds5 _) N hN hpoly
    (by nlinarith : -(m₀ + m₀) ^ 2 < S₀) hseg i j
  exact (h.const_mul (auxLimit m₀)⁻¹).congr fun u _ => rfl

variable (sw : Bool) (d₂ dm : ℝ) (bx bY : Bool)

theorem dec_segCont_eVal0 (m0 m1 m2 m3 m4 : ℝ)
    (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3 ∧ m₀ ≤ m4) (c0 c1 c2 c3 c4 : Bool) (i j : Fin 4) :
    DecSegCont k₀ w fun k => eVal0 m₀ sw d₂ dm bx bY m0 m1 m2 m3 m4 c0 c1 c2 c3 c4 k i j := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hm
  exact dec_segCont_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _
    (isLoopPoly_tnS0 sw d₂ dm bx bY) (isLoopPoly_tnS_k sw 0 d₂ dm bx bY) i j

theorem dec_segCont_eVal2 (m0 m1 m2 m3 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2 ∧ m₀ ≤ m3)
    (c0 c1 c2 c3 : Bool) (i j : Fin 4) :
    DecSegCont k₀ w fun k => eVal2 m₀ sw d₂ dm bx bY m0 m1 m2 m3 c0 c1 c2 c3 k i j := by
  obtain ⟨h0, h1, h2, h3⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 4 fun ℓ => padN (tnS sw 1 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS1 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 1 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact dec_segCont_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _ hN' hpoly'
    i j

theorem dec_segCont_eVal4 (m0 m1 m2 : ℝ) (hm : m₀ ≤ m0 ∧ m₀ ≤ m1 ∧ m₀ ≤ m2) (c0 c1 c2 : Bool)
    (i j : Fin 4) :
    DecSegCont k₀ w fun k => eVal4 m₀ sw d₂ dm bx bY m0 m1 m2 c0 c1 c2 k i j := by
  obtain ⟨h0, h1, h2⟩ := hm
  have hN' : ∀ p i j, IsLoopPoly 2 2 fun ℓ => padN (tnS sw 2 d₂ dm bx bY) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((isLoopPoly_tnS2 sw d₂ dm bx bY p i j).mul
      ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono (by norm_num)
  have hN'' : ∀ p i j, IsLoopPoly 2 4 fun ℓ =>
      padN (padN (tnS sw 2 d₂ dm bx bY) m0 c0) m0 c0 p (ℓ 0) i j :=
    fun p i j => ((hN' p i j).mul ((isLoopAffine_zk p c0).isLoopPoly_propDenom m0 0)).mono
      (by norm_num)
  have hpoly' := fun q i j => (isLoopPoly_tnS_k sw 2 d₂ dm bx bY q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  have hpoly'' := fun q i j => (hpoly' q i j).mul
    ((isLoopAffine_zk_one q c0).isLoopPoly_propDenom m0 0)
  exact dec_segCont_fVal5 hm₀ hS₀ hseg _ (fun l => by fin_cases l <;> assumption) _ _ hN'' hpoly''
    i j

theorem dec_segCont_insVal (M X Y : ℝ) (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (i j : Fin 4) :
    DecSegCont k₀ w fun k => insVal m₀ sw d₂ dm bx bY M X Y k i j := by
  have E0 := fun m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 =>
    dec_segCont_eVal0 hm₀ hS₀ hseg sw d₂ dm bx bY m0 m1 m2 m3 m4 hm c0 c1 c2 c3 c4 i j
  have E2 := fun m0 m1 m2 m3 hm c0 c1 c2 c3 =>
    dec_segCont_eVal2 hm₀ hS₀ hseg sw d₂ dm bx bY m0 m1 m2 m3 hm c0 c1 c2 c3 i j
  have E4 := dec_segCont_eVal4 hm₀ hS₀ hseg sw d₂ dm bx bY M X Y ⟨hM, hX, hY⟩ bx bx bx i j
  exact (((((((((((E0 M M X Y M ⟨hM, hM, hX, hY, hM⟩ bx bY bY bY bY).add
    (E0 M M X Y X ⟨hM, hM, hX, hY, hX⟩ bx bY bY bY bY)).add
    (E0 M M X Y Y ⟨hM, hM, hX, hY, hY⟩ bx bY bY bY bY)).add
    (E0 M X X Y X ⟨hM, hX, hX, hY, hX⟩ bx bx bY bY bY)).add
    (E0 M X X Y Y ⟨hM, hX, hX, hY, hY⟩ bx bx bY bY bY)).add
    (E0 M X Y Y Y ⟨hM, hX, hY, hY, hY⟩ bx bx bx bY bY)).add
    (E2 M M X Y ⟨hM, hM, hX, hY⟩ bx bY bY bY)).add
    (E2 M X X Y ⟨hM, hX, hX, hY⟩ bx bx bY bY)).add
    (E2 M X Y Y ⟨hM, hX, hY, hY⟩ bx bx bx bY)).add E4).const_mul _).congr fun u _ => rfl

end Pieces

theorem dec_segCont_fbVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ} (D : Counterterms F) {k₀ w : Fin 4 → ℝ}
    {S₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hS₀ : -(4 * m₀ ^ 2) < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
    (sw bx bY : Bool) (i j : Fin 4) :
    DecSegCont k₀ w fun k => fbVal P Φ D rep m₀ sw bx bY k i j := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hlt : ∀ g, Φ.mass g < auxX Φ := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [auxX]
    linarith
  exact (DecSegCont.sum Finset.univ fun f _ => (dec_segCont_insVal hm₀ hS₀ hseg sw _ _ bx bY
    (Φ.mass f) (auxX Φ) (auxX Φ + 1) (hmass f) (by linarith [hlt f, hmass f])
    (by linarith [hlt f, hmass f]) i j).const_mul ((Φ.coeff f : ℂ) * kF P.e)).congr
    fun u _ => rfl

/-! ### The tilted vectors along the segment, continuously in `s` -/

/-- The segment parameter of the tilted vector `k'(s)` on the segment of `[S₀, S]`. -/
noncomputable def decTiltU (c S₀ S s : ℝ) : ℝ :=
  upar ((Real.sqrt (2 * c ^ 2 - s) -
      (Real.sqrt (2 * c ^ 2 - S) + Real.sqrt (2 * c ^ 2 - S₀)) / 2) /
    (3 / 4 * (Real.sqrt (2 * c ^ 2 - S₀) - Real.sqrt (2 * c ^ 2 - S))))

theorem dec_continuous_upar : Continuous upar := by
  unfold upar
  refine Continuous.div (by fun_prop) (by fun_prop) fun t => ?_
  have := Real.sqrt_nonneg (1 + 4 * t ^ 2)
  positivity

theorem dec_continuous_tiltU (c S₀ S : ℝ) : Continuous (decTiltU c S₀ S) := by
  unfold decTiltU
  exact dec_continuous_upar.comp (by fun_prop)

/-- **The tilted vector of `s ∈ [S₀, S]` is the point `decTiltU s` of the segment.** -/
theorem dec_tiltVec_eq_lineK {c S₀ S s : ℝ} (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2) (h₀ : S₀ ≤ s)
    (h₁ : s ≤ S) : |decTiltU c S₀ S s| ≤ 1 / 2 ∧
      tiltVec c s = lineK (tiltBase c S₀ S) (tiltDir c S₀ S) (decTiltU c S₀ S s) := by
  set lo := Real.sqrt (2 * c ^ 2 - S)
  set hi := Real.sqrt (2 * c ^ 2 - S₀)
  set τ := Real.sqrt (2 * c ^ 2 - s)
  have hlo : lo ≤ τ := Real.sqrt_le_sqrt (by linarith)
  have hhi : τ ≤ hi := Real.sqrt_le_sqrt (by linarith)
  have hlohi : lo < hi := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  set w := 3 / 4 * (hi - lo)
  have hwd : w = 3 / 4 * (hi - lo) := rfl
  have hw : 0 < w := by rw [hwd]; linarith
  set t := (τ - (lo + hi) / 2) / w
  have ht : |t| ≤ 2 / 3 := by
    rw [abs_div, abs_of_pos hw, div_le_iff₀ hw, abs_le]
    constructor <;> linarith
  have htw : (lo + hi) / 2 + t * w = τ := by
    simp only [t]
    field_simp
    ring
  refine ⟨abs_upar_le ht, ?_⟩
  rw [lineK_tilt, show decTiltU c S₀ S s = upar t from rfl, tpar_upar]
  funext ν
  fin_cases ν <;> simp [tiltVec]
  exact htw.symm

/-- **Continuity along the segment gives continuity in `s` at the tilted vectors.** -/
theorem dec_continuousOn_tilt {c S₀ S : ℝ} (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2)
    {G : (Fin 4 → ℝ) → ℂ} (hG : DecSegCont (tiltBase c S₀ S) (tiltDir c S₀ S) G) :
    ContinuousOn (fun s => G (tiltVec c s)) (Icc S₀ S) := by
  have hmap : MapsTo (decTiltU c S₀ S) (Icc S₀ S) (Icc (-(1 / 2)) (1 / 2)) := fun s hs =>
    dec_mem_Icc_half.mpr (dec_tiltVec_eq_lineK hS₀S hS hs.1 hs.2).1
  refine (hG.comp (dec_continuous_tiltU c S₀ S).continuousOn hmap).congr fun s hs => ?_
  simp only [Function.comp_apply, ← (dec_tiltVec_eq_lineK hS₀S hS hs.1 hs.2).2]

/-! ### The limit of the weighted block along the tilted vectors -/

section Block

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F]
  (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The limit of the weighted block is continuous in `s` at the tilted vectors.** -/
theorem dec_continuousOn_fLim_tilt (he : P.e ≠ 0) (δ : F → ℝ) {c S₀ S : ℝ}
    (hS₀ : -(4 * m₀ ^ 2) < S₀) (hS₀S : S₀ < S) (hS : S < 2 * c ^ 2) (i j : Fin 4) :
    ContinuousOn (fun s => fLim Φ rep P.e δ (tiltVec c s) i j) (Icc S₀ S) := by
  have hseg := fun u (hu : |u| ≤ 1 / 2) => (dot_lineK_tilt_mem (c := c) hS hS₀S.le hu).1
  have h := DecSegCont.congr (H := fun k => fLim Φ rep P.e δ k i j)
    ((dec_segCont_fbVal P Φ rep (ctδ (ctOf P.e δ)) hm₀ hmass hS₀ hseg true true false i j).add
      (dec_segCont_fbVal P Φ rep (ctδ (ctOf P.e δ)) hm₀ hmass hS₀ hseg false false true i j))
      fun u hu => ?_
  · exact dec_continuousOn_tilt hS₀S hS h
  exact (fLim_eq_fbVal P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he δ (by linarith [hseg u hu]) i j).symm

/-- **The projection of the limit of the weighted block is continuous** at every `s` of the
region. -/
theorem dec_continuousAt_projS_fLim (he : P.e ≠ 0) (δ : F → ℝ) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) : ContinuousAt (projS (fLim Φ rep P.e δ)) s := by
  set c : ℝ := 1 + |s|
  have hc : 0 < c := by positivity
  have hsc : s + 1 < 2 * c ^ 2 := by
    have := le_abs_self s
    nlinarith [abs_nonneg s]
  set S₀ : ℝ := (s - 4 * m₀ ^ 2) / 2
  have hS₀ : -(4 * m₀ ^ 2) < S₀ := by simp only [S₀]; linarith
  have hS₀s : S₀ < s := by simp only [S₀]; nlinarith
  have hcont := dec_continuousOn_fLim_tilt P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he δ hS₀
    (hS₀s.trans (lt_add_one s)) hsc 2 3
  have hmem : Icc S₀ (s + 1) ∈ 𝓝 s := Icc_mem_nhds hS₀s (lt_add_one s)
  have hT : TCov (2 * m₀) (fLim Φ rep P.e δ) :=
    tcov_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ
  have hT' : -(2 * m₀) ^ 2 < S₀ := by nlinarith
  refine ((((hcont.continuousAt hmem).neg).div_const ((c ^ 2 : ℝ) : ℂ))).congr ?_
  filter_upwards [hmem] with t ht
  exact (projS_eq_tilt hT hc (hT'.trans_le ht.1) (by linarith [ht.2])).symm

end Block

/-! ### `DecContD` -/

theorem dec_min_one_pos {x : ℝ} (hx : 0 < x) : 0 < min 1 x := lt_min one_pos hx

theorem dec_min_one_sq_le {x : ℝ} (hx : 0 < x) : min 1 x ^ 2 ≤ x := by
  rcases le_total 1 x with h | h
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right h]
    nlinarith

/-- **`DecContD`: the one-loop functional is continuous at `s = 0`.** -/
theorem dec_contD (P : Params) : DecContD P.e := by
  intro x hx
  by_cases he : P.e = 0
  · have e0 : decD₀ P.e 1 x = fun _ => 0 := funext fun s => by simp [decD₀, he]
    rw [e0]
    exact tendsto_const_nhds
  set m₀ : ℝ := min 1 x with hm₀d
  have hm₀ : 0 < m₀ := dec_min_one_pos hx
  have hmass : ∀ g, m₀ ≤ (decCfg 1 x).mass g := dec_cfg_mass_ge (min_le_left _ _) hm₀
    (dec_min_one_sq_le hx)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero hx.le
  have h0 : -(4 * m₀ ^ 2) < 0 := by nlinarith
  have hc := dec_continuousAt_projS_fLim P (decCfg 1 x) (fun _ => 0) hm₀ hmass (fun _ => rfl)
    hpv.1 hpv.2 he (fun _ => 1) h0
  have h : ContinuousAt (decD₀ P.e 1 x) 0 := by
    show ContinuousAt (fun s => I * (projS (fLim (decCfg 1 x) (fun _ => 0) P.e fun _ => 1) s -
      projS (fLim (decCfg 1 x) (fun _ => 0) P.e fun _ => 1) 0) / (P.e : ℂ) ^ 2) 0
    exact ((hc.sub continuousAt_const).const_mul I).div_const _
  have h' := h.tendsto
  rwa [decD₀_zero] at h'

end QED.GradedProof.RPi4

end
