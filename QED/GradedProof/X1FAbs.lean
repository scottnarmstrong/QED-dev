/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CStatement
public import Mathlib.Topology.Instances.Matrix

/-!
# (X₁) piece F: limits of the Dyson decomposition, factor by factor

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece F (assembly). `dysonLim O I V L` is the right side of
`QED.GradedProof.X1C.dysonFive` with arbitrary factors (out-legs `O a`, in-legs `I c`, vertices
`V b ν`, photon legs `L d ν`).

* `tendsto_dysonFive`: if every factor of `dysonFive` at fixed momenta has an `ε → 0⁺` limit,
  then `dysonFive` tends to `dysonLim` of the limits;
* `tendsto_sandwich_dysonLim`: along any filter, if the sandwiched out-legs `w O_a` tend to
  `δ_{a0} w`, the in-legs `I_c u` to `δ_{c0} u`, the vertices converge with the on-shell sandwich
  of the order-`5` vertex `0`, and the photon legs tend to `δ_{d0} δ_ν^μ`, then the sandwiched
  `dysonLim` tends to `0`: every index tuple other than `(0, 2, 0, 0)` has a vanishing factor.
-/

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1F

/-- The right side of the Dyson decomposition with arbitrary factors. -/
noncomputable def dysonLim (O I : ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (V : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (L : ℕ → Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ∑ c ∈ Finset.range 3, ∑ d ∈ Finset.range 3,
    if a + b + c + d = 2 then ∑ ν, L d ν • (O a * V b ν * I c) else 0

/-- **The `ε → 0⁺` limit of `dysonFive` from the limits of its factors.** -/
theorem tendsto_dysonFive (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (r' r : Fin 4 → ℝ) (μ : Fin 4)
    {O I : ℕ → Matrix (Fin 4) (Fin 4) ℂ} {V : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {L : ℕ → Fin 4 → ℂ}
    (hO : ∀ a < 3, Tendsto (fun ε : ℝ => X1C.outLeg { P with ε := ε } Φ D a r') (𝓝[>] 0)
      (𝓝 (O a)))
    (hI : ∀ c < 3, Tendsto (fun ε : ℝ => X1C.inLeg { P with ε := ε } Φ D c r) (𝓝[>] 0)
      (𝓝 (I c)))
    (hV : ∀ b < 3, ∀ ν, Tendsto (fun ε : ℝ => vertexPart { P with ε := ε } Φ D Φ.openLine b r' r ν)
      (𝓝[>] 0) (𝓝 (V b ν)))
    (hL : ∀ d < 3, ∀ ν, Tendsto (fun ε : ℝ => X1C.photonLeg { P with ε := ε } Φ D d (r' - r) ν μ)
      (𝓝[>] 0) (𝓝 (L d ν))) :
    Tendsto (fun ε : ℝ => X1C.dysonFive { P with ε := ε } Φ D r' r μ) (𝓝[>] 0)
      (𝓝 (dysonLim O I V L)) := by
  unfold X1C.dysonFive dysonLim
  refine tendsto_finsetSum _ fun a ha => tendsto_finsetSum _ fun b hb =>
    tendsto_finsetSum _ fun c hc => tendsto_finsetSum _ fun d hd => ?_
  rw [Finset.mem_range] at ha hb hc hd
  by_cases h : a + b + c + d = 2
  · simp only [h, ↓reduceIte]
    exact tendsto_finsetSum _ fun ν _ =>
      (hL d hd ν).smul (((hO a ha).mul (hV b hb ν)).mul (hI c hc))
  · simp only [h, ↓reduceIte]
    exact tendsto_const_nhds

/-- The sandwich of `dysonLim`, expanded. -/
theorem sandwich_dysonLim (O I : ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (V : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (L : ℕ → Fin 4 → ℂ) (w u : Fin 4 → ℂ) :
    w ⬝ᵥ (dysonLim O I V L *ᵥ u) =
      ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ∑ c ∈ Finset.range 3, ∑ d ∈ Finset.range 3,
        if a + b + c + d = 2 then
          ∑ ν, L d ν * ((w ᵥ* O a) ⬝ᵥ (V b ν *ᵥ (I c *ᵥ u))) else 0 := by
  unfold dysonLim
  simp only [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  · simp

theorem tendsto_sum_zero {X ι : Type*} {𝓕 : Filter X} (s : Finset ι) {f : ι → X → ℂ}
    (h : ∀ i ∈ s, Tendsto (f i) 𝓕 (𝓝 0)) : Tendsto (fun x => ∑ i ∈ s, f i x) 𝓕 (𝓝 0) := by
  simpa using tendsto_finsetSum s h

/-- **The sandwiched `dysonLim` tends to `0`** under on-shell leg and vertex limits. -/
theorem tendsto_sandwich_dysonLim {X : Type*} {𝓕 : Filter X}
    {O I : ℕ → X → Matrix (Fin 4) (Fin 4) ℂ} {V : ℕ → X → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {L : ℕ → X → Fin 4 → ℂ} {w u : Fin 4 → ℂ} {V₀ : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {μ : Fin 4}
    (hO : ∀ a < 3, Tendsto (fun x => w ᵥ* O a x) 𝓕 (𝓝 (if a = 0 then w else 0)))
    (hI : ∀ c < 3, Tendsto (fun x => I c x *ᵥ u) 𝓕 (𝓝 (if c = 0 then u else 0)))
    (hV : ∀ b < 3, ∀ ν, Tendsto (fun x => V b x ν) 𝓕 (𝓝 (V₀ b ν)))
    (hL : ∀ d < 3, ∀ ν, Tendsto (fun x => L d x ν) 𝓕 (𝓝 (if d = 0 ∧ ν = μ then 1 else 0)))
    (h₂ : ∀ ν, w ⬝ᵥ (V₀ 2 ν *ᵥ u) = 0) :
    Tendsto (fun x => w ⬝ᵥ (dysonLim (O · x) (I · x) (V · x) (L · x) *ᵥ u)) 𝓕 (𝓝 0) := by
  simp only [sandwich_dysonLim]
  refine tendsto_sum_zero _ fun a ha => tendsto_sum_zero _ fun b hb =>
    tendsto_sum_zero _ fun c hc => tendsto_sum_zero _ fun d hd => ?_
  rw [Finset.mem_range] at ha hb hc hd
  by_cases h : a + b + c + d = 2
  · simp only [h, ↓reduceIte]
    refine tendsto_sum_zero _ fun ν _ => ?_
    have hVu := ((continuous_fst.matrix_mulVec continuous_snd).tendsto _).comp
      ((hV b hb ν).prodMk_nhds (hI c hc))
    have hdot := ((continuous_fst.dotProduct continuous_snd).tendsto _).comp
      ((hO a ha).prodMk_nhds hVu)
    have ht := (hL d hd ν).mul hdot
    convert ht using 2
    simp only [Function.comp_def]
    by_cases ha0 : a = 0
    · by_cases hc0 : c = 0
      · by_cases hd0 : d = 0
        · have hb2 : b = 2 := by omega
          subst ha0 hc0 hd0 hb2
          simp only [↓reduceIte, h₂, mul_zero]
        · simp [hd0]
      · simp [hc0]
    · simp [ha0]
  · simp only [h, ↓reduceIte]
    exact (tendsto_const_nhds : Tendsto (fun _ : X => (0 : ℂ)) 𝓕 (𝓝 0))

end QED.GradedProof.X1F

end
