/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1FAssemble
public import QED.GradedProof.X2Photon

/-!
# (X₂) piece E: the order-`e⁵` LSZ amplitude at a scattering pair, given the Dyson decomposition

Helper level for the Phase 5 Stage 2 goal (X₂)
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` (decision D-57), piece E. Under the
hypotheses of (X₁) and the order-`e⁵` Dyson decomposition `QED.GradedProof.X1C.DysonFive` at every
`ε > 0` (X₁ piece C, a separate proof, used here only as a hypothesis), at on-shell
positive-energy momenta `(p', p)` with `q² ≥ 0` (`q = p' - p`) the order-`5` LSZ amplitude (G-L₁)
exists and equals `lszFive`:
`ū' V⁽⁵⁾ u + ∑_ν L⁽²⁾_{νμ}(q) ū' V⁽³⁾ν u + ∑_ν L⁽⁴⁾_{νμ}(q) e ū' γ^ν u`, with `V⁽³⁾`, `V⁽⁵⁾` the
`ε → 0⁺` limits of the graded vertices at `(p', p)` and `L⁽²ᵈ⁾ = QED.GradedProof.X2.legLim d` the
photon-leg limits. The leg corrections vanish on shell, as in (X₁).

* `tendsto_sandwich_dysonLim_gen`: the off-shell limit of the sandwiched `dysonLim` for general
  vertex and photon-leg limits.
* `lszFive`, `isLSZAmplitudePart_five_of_dysonFive`.
-/

@[expose] public section

open Matrix Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X2

open QED.GradedProof.X1F (dysonLim sandwich_dysonLim tendsto_dysonFive outLim inLim)

/-- The two-index form of the surviving terms (`a = c = 0`) of the sandwiched `dysonLim`. -/
theorem sum_four_eq_sum_two (V₀ : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (L₀ : ℕ → Fin 4 → ℂ)
    (w u : Fin 4 → ℂ) :
    (∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ∑ c ∈ Finset.range 3, ∑ d ∈ Finset.range 3,
      if a + b + c + d = 2 then ∑ ν, L₀ d ν *
        ((if a = 0 then w else 0) ⬝ᵥ (V₀ b ν *ᵥ (if c = 0 then u else 0))) else 0) =
      ∑ ν, L₀ 0 ν * (w ⬝ᵥ (V₀ 2 ν *ᵥ u)) + ∑ ν, L₀ 1 ν * (w ⬝ᵥ (V₀ 1 ν *ᵥ u)) +
        ∑ ν, L₀ 2 ν * (w ⬝ᵥ (V₀ 0 ν *ᵥ u)) := by
  simp [Finset.sum_range_succ]
  ring

/-- **The off-shell limit of the sandwiched `dysonLim`** for general vertex and photon-leg
limits: only the terms without leg corrections survive. -/
theorem tendsto_sandwich_dysonLim_gen {X : Type*} {𝓕 : Filter X}
    {O I : ℕ → X → Matrix (Fin 4) (Fin 4) ℂ} {V : ℕ → X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {L : ℕ → X → Fin 4 → ℂ} {w u : Fin 4 → ℂ} {V₀ : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {L₀ : ℕ → Fin 4 → ℂ}
    (hO : ∀ a < 3, Tendsto (fun x => w ᵥ* O a x) 𝓕 (𝓝 (if a = 0 then w else 0)))
    (hI : ∀ c < 3, Tendsto (fun x => I c x *ᵥ u) 𝓕 (𝓝 (if c = 0 then u else 0)))
    (hV : ∀ b < 3, ∀ ν, Tendsto (fun x => V b x ν) 𝓕 (𝓝 (V₀ b ν)))
    (hL : ∀ d < 3, ∀ ν, Tendsto (fun x => L d x ν) 𝓕 (𝓝 (L₀ d ν))) :
    Tendsto (fun x => w ⬝ᵥ (dysonLim (O · x) (I · x) (V · x) (L · x) *ᵥ u)) 𝓕
      (𝓝 (∑ ν, L₀ 0 ν * (w ⬝ᵥ (V₀ 2 ν *ᵥ u)) + ∑ ν, L₀ 1 ν * (w ⬝ᵥ (V₀ 1 ν *ᵥ u)) +
        ∑ ν, L₀ 2 ν * (w ⬝ᵥ (V₀ 0 ν *ᵥ u)))) := by
  rw [← sum_four_eq_sum_two]
  simp only [sandwich_dysonLim]
  refine tendsto_finsetSum _ fun a ha => tendsto_finsetSum _ fun b hb =>
    tendsto_finsetSum _ fun c hc => tendsto_finsetSum _ fun d hd => ?_
  rw [Finset.mem_range] at ha hb hc hd
  by_cases h : a + b + c + d = 2
  · simp only [h, ↓reduceIte]
    refine tendsto_finsetSum _ fun ν _ => ?_
    have hVu := ((continuous_fst.matrix_mulVec continuous_snd).tendsto _).comp
      ((hV b hb ν).prodMk_nhds (hI c hc))
    have hdot := ((continuous_fst.dotProduct continuous_snd).tendsto _).comp
      ((hO a ha).prodMk_nhds hVu)
    exact (hL d hd ν).mul hdot
  · simp only [h, ↓reduceIte]
    exact tendsto_const_nhds

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- The order-`5` LSZ amplitude at `(p', p)` from the vertex limits `V₁` (order `3`) and `V₂`
(order `5`) and the photon-leg limits `legLim`. -/
noncomputable def lszFive (rep : F → F) (m₀ : ℝ) (V₁ V₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (p' p : Fin 4 → ℝ) (s' s : Fin 2) (μ : Fin 4) : ℂ :=
  Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p' s') ⬝ᵥ
      (V₂ μ *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s) +
    ∑ ν, legLim P Φ D rep m₀ 1 (p' - p) ν μ *
      (Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p' s') ⬝ᵥ
        (V₁ ν *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s)) +
    ∑ ν, legLim P Φ D rep m₀ 2 (p' - p) ν μ *
      (Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p' s') ⬝ᵥ
        ((Matrix.of fun i j => (P.e : ℂ) * Dirac.gamma ν i j) *ᵥ
          Dirac.spinor (Φ.mass Φ.openLine) p s))

/-- **(X₂) piece E: the order-`5` LSZ amplitude at a scattering pair, given the Dyson
decomposition.** Under the hypotheses of `QED.Graded.isLSZAmplitudePart_five_self`, at
on-shell positive-energy `(p', p)` with `(p' - p)² ≥ 0`, if `V₁`, `V₂` are the `ε → 0⁺` limits
of the order-`3` and order-`5` vertices at `(p', p)`, the LSZ amplitude is `lszFive`. -/
theorem isLSZAmplitudePart_five_of_dysonFive (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hopen : rep Φ.openLine = Φ.openLine) (hD : IsRenormalizedThrough P Φ D rep 2)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -Φ.mass Φ.openLine ^ 2)
    (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hC : ∀ ε > 0, X1C.DysonFive { P with ε := ε } Φ D)
    {V₁ V₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV₁ : ∀ μ, Tendsto (fun ε => vertexPart { P with ε := ε } Φ D Φ.openLine 1 p' p μ)
      (𝓝[>] 0) (𝓝 (V₁ μ)))
    (hV₂ : ∀ μ, Tendsto (fun ε => vertexPart { P with ε := ε } Φ D Φ.openLine 2 p' p μ)
      (𝓝[>] 0) (𝓝 (V₂ μ))) :
    IsLSZAmplitudePart P Φ D 5 p' p (lszFive P Φ D rep m₀ V₁ V₂ p' p) := by
  classical
  set m := Φ.mass Φ.openLine with hm_def
  have hm : 0 < m := hm₀.trans_le (hmass _)
  have h₁ := GEx2.sum_eq_zero_of_blocks rep hrep Φ.coeff hPV₁
  have h₂ := GEx2.sum_eq_zero_of_blocks rep hrep (fun f => Φ.coeff f * Φ.mass f ^ 2) hPV₂
  obtain ⟨R₁, hR₁, A₁, B₁, hAB₁, h0₁, hd₁⟩ :=
    ((hD.2 1 le_rfl (by norm_num)).1 Φ.openLine hopen).1
  obtain ⟨R₂, hR₂, A₂, B₂, hAB₂, h0₂, hd₂⟩ :=
    ((hD.2 2 (by norm_num) le_rfl).1 Φ.openLine hopen).1
  have hA₁ : ContinuousAt A₁ (-m ^ 2) :=
    X1C.continuousAt_A_selfEnergyPart_one P Φ D Φ.openLine hm hmγ hΛ
      (R := m + R₁) (by linarith) A₁ B₁ hAB₁
  have hA₂ : ContinuousAt A₂ (-m ^ 2) :=
    X1.continuousAt_A_selfEnergyPart_two P Φ D Φ.openLine m₀ hm₀ hmass hmγ hΛ h₁ h₂
      (R := m + R₂) (by linarith) A₂ B₂ hAB₂
  obtain ⟨W₁, hW₁, hW₁c⟩ :=
    X1D.exists_vertexPart_one_offShell P Φ D Φ.openLine hm hmγ hΛ hp hp' hp0 hp0'
  obtain ⟨W₂, hW₂, hW₂c⟩ := X1D.exists_vertexPart_two_offShell P Φ D Φ.openLine m₀ hm₀
    hmass hmγ hΛ h₁ h₂ hp hp' hp0 hp0' hq
  have eW₁ : W₁ (p', p) = V₁ := funext fun μ =>
    tendsto_nhds_unique (hW₁.self_of_nhds μ) (hV₁ μ)
  have eW₂ : W₂ (p', p) = V₂ := funext fun μ =>
    tendsto_nhds_unique (hW₂.self_of_nhds μ) (hV₂ μ)
  have hZ : ∀ (d : ℕ) (ν μ : Fin 4), ∃ G : (Fin 4 → ℝ) → ℂ, d < 3 →
      (∀ᶠ k in 𝓝 (p' - p), Tendsto
        (fun ε : ℝ => X1C.photonLeg { P with ε := ε } Φ D d k ν μ) (𝓝[>] 0) (𝓝 (G k))) ∧
      ContinuousAt G (p' - p) ∧ G (p' - p) = legLim P Φ D rep m₀ d (p' - p) ν μ := by
    intro d ν μ
    by_cases hd : d < 3
    · obtain ⟨G, hG⟩ := zLim_photonLeg_spacelike hq P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁
        hPV₂ hD hd ν μ
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose PL hPL using hZ
  set Vf : ℕ → (Fin 4 → ℝ) × (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun b x ν =>
    if b = 0 then Matrix.of fun i j => (P.e : ℂ) * Dirac.gamma ν i j
    else if b = 1 then W₁ x ν else W₂ x ν with hVf
  have hsubT : Tendsto (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => x.1 - x.2) (𝓝 (p', p))
      (𝓝 (p' - p)) :=
    (continuous_fst.sub continuous_snd).tendsto (p', p)
  refine X1.isLSZAmplitudePart_of_tendsto fun s' s μ => ?_
  set w := Dirac.bar (Dirac.spinor m p' s') with hw_def
  set u := Dirac.spinor m p s with hu_def
  have hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u) := Dirac.slash_mulVec_spinor _ p hp s
  have hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w) :=
    Dirac.bar_vecMul_slash _ p' _ (Dirac.slash_mulVec_spinor _ p' hp' s')
  refine ⟨fun x => w ⬝ᵥ (dysonLim (fun a => outLim m A₁ B₁ A₂ B₂ a x.1)
      (fun c => inLim m A₁ B₁ A₂ B₂ c x.2) (fun b ν => Vf b x ν)
      (fun d ν => PL d ν μ (x.1 - x.2)) *ᵥ u), ?_, ?_⟩
  · -- the `ε → 0⁺` limits at off-shell pairs near `(p', p)`
    have Ed : ∀ d, d < 3 → ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p), ∀ ν, Tendsto
        (fun ε : ℝ => X1C.photonLeg { P with ε := ε } Φ D d (x.1 - x.2) ν μ) (𝓝[>] 0)
        (𝓝 (PL d ν μ (x.1 - x.2))) := fun d hd =>
      eventually_all.2 fun ν => hsubT.eventually (hPL d ν μ hd).1
    have E₁ := X1F.eventually_dot_gt_of_shell hm hR₁ hp
    have E₂ := X1F.eventually_dot_gt_of_shell hm hR₂ hp
    have E₁' := X1F.eventually_dot_gt_of_shell hm hR₁ hp'
    have E₂' := X1F.eventually_dot_gt_of_shell hm hR₂ hp'
    filter_upwards [Ed 0 (by norm_num), Ed 1 (by norm_num), Ed 2 (by norm_num), hW₁, hW₂,
      continuous_fst.continuousAt.eventually E₁', continuous_fst.continuousAt.eventually E₂',
      continuous_snd.continuousAt.eventually E₁, continuous_snd.continuousAt.eventually E₂]
      with x e0 e1 e2 v1 v2 a1 a2 b1 b2 hx1 hx2
    have key := X1C.lszIntegrand_eventuallyEq P Φ D hC x.1 x.2 μ w u
    have hT := tendsto_dysonFive P Φ D x.1 x.2 μ
      (O := fun a => outLim m A₁ B₁ A₂ B₂ a x.1)
      (I := fun c => inLim m A₁ B₁ A₂ B₂ c x.2) (V := fun b ν => Vf b x ν)
      (L := fun d ν => PL d ν μ (x.1 - x.2))
      (fun a _ => X1F.tendsto_outLeg P Φ D hx1 (hAB₁ x.1 a1) (hAB₂ x.1 a2) a)
      (fun c _ => X1F.tendsto_inLeg P Φ D hx2 (hAB₁ x.2 b1) (hAB₂ x.2 b2) c)
      (fun b hb ν => by
        interval_cases b
        · have e : ∀ ε : ℝ, vertexPart { P with ε := ε } Φ D Φ.openLine 0 x.1 x.2 ν =
              Matrix.of fun i j => (P.e : ℂ) * Dirac.gamma ν i j := fun ε => by
            ext i j
            exact X1F.vertexPart_zero_apply _ Φ D _ _ _ ν i j
          simp only [hVf, e, ↓reduceIte]
          exact tendsto_const_nhds
        · simpa [hVf] using v1 ν
        · simpa [hVf] using v2 ν)
      (fun d hd ν => by
        interval_cases d
        exacts [e0 ν, e1 ν, e2 ν])
    have hcβ : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ => w ⬝ᵥ (M *ᵥ u) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact ((hcβ.tendsto _).comp hT).congr' key.symm
  · -- the off-shell limit
    have hfst := WickModel.LszLimit.tendsto_fst_offShell m p' p
    have hsnd := WickModel.LszLimit.tendsto_snd_offShell m p' p
    have hlim := tendsto_sandwich_dysonLim_gen
      (O := fun a x => outLim m A₁ B₁ A₂ B₂ a x.1)
      (I := fun c x => inLim m A₁ B₁ A₂ B₂ c x.2) (V := Vf)
      (L := fun d x ν => PL d ν μ (x.1 - x.2)) (V₀ := fun b ν => Vf b (p', p) ν)
      (L₀ := fun d ν => legLim P Φ D rep m₀ d (p' - p) ν μ) (w := w) (u := u)
      (𝓕 := 𝓝[WickModel.LszLimit.offShellPairs m] (p', p))
      (fun a ha => ?_) (fun c hc => ?_) (fun b hb ν => ?_) (fun d hd ν => ?_)
    · convert hlim using 2
      simp only [lszFive, legLim, hVf, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
        one_ne_zero, eW₁, eW₂, ← hm_def, ← hw_def, ← hu_def, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ]
    · by_cases ha0 : a = 0
      · subst ha0
        simp only [outLim, Matrix.vecMul_one, ↓reduceIte]
        exact tendsto_const_nhds
      · simp only [ha0, ↓reduceIte]
        exact (X1F.tendsto_vecMul_outLim hm hp' hA₁ h0₁ hd₁ hA₂ h0₂ hd₂ hw ha0).comp hfst
    · by_cases hc0 : c = 0
      · subst hc0
        simp only [inLim, Matrix.one_mulVec, ↓reduceIte]
        exact tendsto_const_nhds
      · simp only [hc0, ↓reduceIte]
        exact (X1F.tendsto_inLim_mulVec hm hp hA₁ h0₁ hd₁ hA₂ h0₂ hd₂ hu hc0).comp hsnd
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      interval_cases b
      · simp only [hVf, ↓reduceIte]
        exact tendsto_const_nhds
      · simp only [hVf, one_ne_zero, ↓reduceIte]
        exact (tendsto_pi_nhds.1 hW₁c.tendsto) ν
      · simp only [hVf, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte]
        exact (tendsto_pi_nhds.1 hW₂c.tendsto) ν
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have h := ((hPL d ν μ hd).2.1.tendsto).comp hsubT
      rwa [(hPL d ν μ hd).2.2] at h

end QED.GradedProof.X2

end
