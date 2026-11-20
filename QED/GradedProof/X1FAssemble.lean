/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1FLeg
public import QED.GradedProof.X1FAbs
public import QED.GradedProof.X1FVertexZero
public import QED.GradedProof.X1EPhoton
public import QED.GradedProof.X1Glue
public import QED.GradedProof.X1SEReg
public import QED.GradedProof.X1CSEOne
public import QED.GradedProof.X1DGraded
public import QED.GradedProof.X1EVertexOne
public import QED.GradedProof.GEx2Inputs
public import QED.Frozen.Graded.IsRenormalizedThrough

/-!
# (X₁) piece F: the assembly, conditional on the Dyson decomposition

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece F. `isLSZAmplitudePart_five_self_of_dysonFive` is the conclusion of (X₁)
under its exact hypotheses **and** the order-`e⁵` Dyson decomposition
`QED.GradedProof.X1C.DysonFive` at every `ε > 0` (piece C, a separate proof). The route:

* by `QED.GradedProof.X1C.lszIntegrand_eventuallyEq` the integrand of (G-L₁) is the sandwiched
  `dysonFive` for `ε > 0`;
* at off-shell pairs near `(p, p)` every factor has an `ε → 0⁺` limit
  (`QED.GradedProof.X1F.tendsto_dysonFive`): the legs from the on-shell data (G₉) of orders `1, 2`
  (`tendsto_inLeg`, `tendsto_outLeg`), the vertices of orders `1` (the tree,
  `vertexPart_zero_apply`), `3` (`QED.GradedProof.X1D.exists_vertexPart_one_offShell`) and `5`
  (`QED.GradedProof.X1D.exists_vertexPart_two_offShell_self`), the photon legs from piece E
  (`QED.GradedProof.X1E.zLim_photonLeg_self`);
* through off-shell pairs the limit tends to `0` (`tendsto_sandwich_dysonLim`), and
  `QED.GradedProof.X1.exists_and_eq_zero_of_tendsto` concludes.
-/

@[expose] public section

open Matrix Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1F

theorem eventually_dot_gt_of_shell {m R : ℝ} (hm : 0 < m) (hR : 0 < R) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) : ∀ᶠ r in 𝓝 p, -(m + R) ^ 2 < Minkowski.dot r r :=
  (isOpen_lt continuous_const X1E.continuous_dot_self).mem_nhds (by
    show -(m + R) ^ 2 < Minkowski.dot p p
    rw [hp]; nlinarith)

/-- **(X₁) from the Dyson decomposition.** Under the hypotheses of
`QED.Graded.isLSZAmplitudePart_five_self` and `X1C.DysonFive` at every `ε > 0`, the conclusion
of (X₁) holds. -/
theorem isLSZAmplitudePart_five_self_of_dysonFive (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hopen : rep Φ.openLine = Φ.openLine) (hD : IsRenormalizedThrough P Φ D rep 2)
    (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2) (hp0 : 0 < p 0)
    (hC : ∀ ε > 0, X1C.DysonFive { P with ε := ε } Φ D) :
    (∃ M, IsLSZAmplitudePart P Φ D 5 p p M) ∧ ∀ M, IsLSZAmplitudePart P Φ D 5 p p M → M = 0 := by
  classical
  have hm : 0 < Φ.mass Φ.openLine := hm₀.trans_le (hmass _)
  have h₁ := GEx2.sum_eq_zero_of_blocks rep hrep Φ.coeff hPV₁
  have h₂ := GEx2.sum_eq_zero_of_blocks rep hrep (fun f => Φ.coeff f * Φ.mass f ^ 2) hPV₂
  obtain ⟨R₁, hR₁, A₁, B₁, hAB₁, h0₁, hd₁⟩ :=
    ((hD.2 1 le_rfl (by norm_num)).1 Φ.openLine hopen).1
  obtain ⟨R₂, hR₂, A₂, B₂, hAB₂, h0₂, hd₂⟩ :=
    ((hD.2 2 (by norm_num) le_rfl).1 Φ.openLine hopen).1
  have hA₁ : ContinuousAt A₁ (-Φ.mass Φ.openLine ^ 2) :=
    X1C.continuousAt_A_selfEnergyPart_one P Φ D Φ.openLine hm hmγ hΛ
      (R := Φ.mass Φ.openLine + R₁) (by linarith) A₁ B₁ hAB₁
  have hA₂ : ContinuousAt A₂ (-Φ.mass Φ.openLine ^ 2) :=
    X1.continuousAt_A_selfEnergyPart_two P Φ D Φ.openLine m₀ hm₀ hmass hmγ hΛ h₁ h₂
      (R := Φ.mass Φ.openLine + R₂) (by linarith) A₂ B₂ hAB₂
  obtain ⟨V₁, hV₁, hV₁c⟩ :=
    X1D.exists_vertexPart_one_offShell P Φ D Φ.openLine hm hmγ hΛ hp hp hp0 hp0
  obtain ⟨V₂, hV₂, hV₂c, hV₂0⟩ := X1D.exists_vertexPart_two_offShell_self P Φ D rep m₀ hm₀
    hmass hmγ hΛ hrep hPV₁ hPV₂ hopen hD p hp hp0
  have hZ : ∀ (d : ℕ) (ν μ : Fin 4), ∃ G : (Fin 4 → ℝ) → ℂ, d < 3 →
      (∀ᶠ q in 𝓝 (0 : Fin 4 → ℝ), Tendsto
        (fun ε : ℝ => X1C.photonLeg { P with ε := ε } Φ D d q ν μ) (𝓝[>] 0) (𝓝 (G q))) ∧
      ContinuousAt G 0 ∧ G 0 = if d = 0 ∧ ν = μ then 1 else 0 := by
    intro d ν μ
    by_cases hd : d < 3
    · obtain ⟨G, hG⟩ := X1E.zLim_photonLeg_self P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD
        hd ν μ
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose PL hPL using hZ
  set Vf : ℕ → (Fin 4 → ℝ) × (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun b x ν =>
    if b = 0 then Matrix.of fun i j => (P.e : ℂ) * Dirac.gamma ν i j
    else if b = 1 then V₁ x ν else V₂ x ν with hVf
  have hsubT : Tendsto (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => x.1 - x.2) (𝓝 (p, p)) (𝓝 0) := by
    have h : Continuous fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => x.1 - x.2 :=
      continuous_fst.sub continuous_snd
    have h' := h.tendsto (p, p)
    rwa [show (p, p).1 - (p, p).2 = 0 from sub_self p] at h'
  refine X1.exists_and_eq_zero_of_tendsto hm.ne' hp fun s' s μ => ?_
  have hu : Dirac.slash p *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s =
      -((Φ.mass Φ.openLine : ℂ) • Dirac.spinor (Φ.mass Φ.openLine) p s) :=
    Dirac.slash_mulVec_spinor _ p hp s
  have hw : Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p s') ᵥ* Dirac.slash p =
      -((Φ.mass Φ.openLine : ℂ) • Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p s')) :=
    Dirac.bar_vecMul_slash _ p _ (Dirac.slash_mulVec_spinor _ p hp s')
  refine ⟨fun x => Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p s') ⬝ᵥ
    (dysonLim (fun a => outLim (Φ.mass Φ.openLine) A₁ B₁ A₂ B₂ a x.1)
      (fun c => inLim (Φ.mass Φ.openLine) A₁ B₁ A₂ B₂ c x.2) (fun b ν => Vf b x ν)
      (fun d ν => PL d ν μ (x.1 - x.2)) *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s), ?_, ?_⟩
  · -- the `ε → 0⁺` limits at off-shell pairs near `(p, p)`
    have Ed : ∀ d, d < 3 → ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p, p), ∀ ν, Tendsto
        (fun ε : ℝ => X1C.photonLeg { P with ε := ε } Φ D d (x.1 - x.2) ν μ) (𝓝[>] 0)
        (𝓝 (PL d ν μ (x.1 - x.2))) := fun d hd =>
      eventually_all.2 fun ν => hsubT.eventually (hPL d ν μ hd).1
    have E₁ := eventually_dot_gt_of_shell hm hR₁ hp
    have E₂ := eventually_dot_gt_of_shell hm hR₂ hp
    filter_upwards [Ed 0 (by norm_num), Ed 1 (by norm_num), Ed 2 (by norm_num), hV₁, hV₂,
      continuous_fst.continuousAt.eventually E₁, continuous_fst.continuousAt.eventually E₂,
      continuous_snd.continuousAt.eventually E₁, continuous_snd.continuousAt.eventually E₂]
      with x e0 e1 e2 v1 v2 a1 a2 b1 b2 hx1 hx2
    have key := X1C.lszIntegrand_eventuallyEq P Φ D hC x.1 x.2 μ
      (Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p s')) (Dirac.spinor (Φ.mass Φ.openLine) p s)
    have hT := tendsto_dysonFive P Φ D x.1 x.2 μ
      (O := fun a => outLim (Φ.mass Φ.openLine) A₁ B₁ A₂ B₂ a x.1)
      (I := fun c => inLim (Φ.mass Φ.openLine) A₁ B₁ A₂ B₂ c x.2) (V := fun b ν => Vf b x ν)
      (L := fun d ν => PL d ν μ (x.1 - x.2))
      (fun a _ => tendsto_outLeg P Φ D hx1 (hAB₁ x.1 a1) (hAB₂ x.1 a2) a)
      (fun c _ => tendsto_inLeg P Φ D hx2 (hAB₁ x.2 b1) (hAB₂ x.2 b2) c)
      (fun b hb ν => by
        interval_cases b
        · have e : ∀ ε : ℝ, vertexPart { P with ε := ε } Φ D Φ.openLine 0 x.1 x.2 ν =
              Matrix.of fun i j => (P.e : ℂ) * Dirac.gamma ν i j := fun ε => by
            ext i j
            exact vertexPart_zero_apply _ Φ D _ _ _ ν i j
          simp only [hVf, e, ↓reduceIte]
          exact tendsto_const_nhds
        · simpa [hVf] using v1 ν
        · simpa [hVf] using v2 ν)
      (fun d hd ν => by
        interval_cases d
        exacts [e0 ν, e1 ν, e2 ν])
    have hcβ : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ =>
        Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p s') ⬝ᵥ
          (M *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    have hβ := (hcβ.tendsto _).comp hT
    exact hβ.congr' key.symm
  · -- the off-shell limit
    have hfst := WickModel.LszLimit.tendsto_fst_offShell (Φ.mass Φ.openLine) p p
    have hsnd := WickModel.LszLimit.tendsto_snd_offShell (Φ.mass Φ.openLine) p p
    refine tendsto_sandwich_dysonLim (O := fun a x => outLim (Φ.mass Φ.openLine) A₁ B₁ A₂ B₂ a x.1)
      (I := fun c x => inLim (Φ.mass Φ.openLine) A₁ B₁ A₂ B₂ c x.2) (V := Vf)
      (L := fun d x ν => PL d ν μ (x.1 - x.2)) (V₀ := fun b ν => Vf b (p, p) ν) (μ := μ)
      (fun a ha => ?_) (fun c hc => ?_) (fun b hb ν => ?_) (fun d hd ν => ?_) (fun ν => ?_)
    · by_cases ha0 : a = 0
      · subst ha0
        simp only [outLim, Matrix.vecMul_one, ↓reduceIte]
        exact tendsto_const_nhds
      · simp only [ha0, ↓reduceIte]
        exact (tendsto_vecMul_outLim hm hp hA₁ h0₁ hd₁ hA₂ h0₂ hd₂ hw ha0).comp hfst
    · by_cases hc0 : c = 0
      · subst hc0
        simp only [inLim, Matrix.one_mulVec, ↓reduceIte]
        exact tendsto_const_nhds
      · simp only [hc0, ↓reduceIte]
        exact (tendsto_inLim_mulVec hm hp hA₁ h0₁ hd₁ hA₂ h0₂ hd₂ hu hc0).comp hsnd
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      interval_cases b
      · simp only [hVf, ↓reduceIte]
        exact tendsto_const_nhds
      · simp only [hVf, one_ne_zero, ↓reduceIte]
        exact (tendsto_pi_nhds.1 hV₁c.tendsto) ν
      · simp only [hVf, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte]
        exact (tendsto_pi_nhds.1 hV₂c.tendsto) ν
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have h := ((hPL d ν μ hd).2.1.tendsto).comp hsubT
      rwa [(hPL d ν μ hd).2.2] at h
    · simp only [hVf, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte]
      exact hV₂0 ν _ _ hu hw

end QED.GradedProof.X1F

end
