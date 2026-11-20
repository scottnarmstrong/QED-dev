/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecLin
public import QED.GradedProof.RPi4DecAnom

/-!
# (R-Π₄) step L9, D3b: changing the counterterm mass of a block

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3b. Two flavour sets with the same measure of masses whose counterterm flavours carry the
masses `μ` and `μ'` differ only in the mass insertion, which is `ctPair(μ)` resp. `ctPair(μ')`
times the same one-loop block `fLim(1)`:

* `dec_qPair_sub_of_rep`: `qPair Φ - qPair Ψ = i (ctPair(μ) - ctPair(μ')) projS fLim(1)` at
  every photon pair;
* `dec_asmPolLim_sub_of_rep`: **`asmPolLim Φ - asmPolLim Ψ =
  i (3e²/16π²) log(μ²/μ'²) (projS fLim(1)(s) - projS fLim(1)(0))`**, given the face-limit
  identity.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

variable {F : Type} [Fintype F] [DecidableEq F] {Φ Ψ : Lepton.Flavors F} {repΦ repΨ : F → F}

omit [DecidableEq F] in
/-- The weighted block of a block with counterterm mass `μ` and weight `ctPair` is `ctPair(μ)`
times the block with unit weight. -/
theorem dec_dBlockD_rep (e a b : ℝ) {μ : ℝ} (hμ : ∀ f, Φ.mass (repΦ f) = μ) (ε : ℝ)
    (k q : Fin 4 → ℝ) (i j : Fin 4) :
    dBlockD Φ repΦ e (fun g => ctPair e (Φ.mass g) a b) ε k q i j =
      (ctPair e μ a b : ℂ) * dBlockD Φ repΦ e (fun _ => 1) ε k q i j := by
  simp only [dBlockD, hμ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

/-- The same measure of masses (the counterterm masses play no role). -/
def DecSameMass (Φ Ψ : Lepton.Flavors F) : Prop :=
  ∀ g : ℝ → ℂ, ∑ f, (Φ.coeff f : ℂ) * g (Φ.mass f) = ∑ f, (Ψ.coeff f : ℂ) * g (Ψ.mass f)

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, repΦ (repΦ f) = repΦ f)
  (hPV₁ : ∀ b, repΦ b = b → ∑ f ∈ Finset.univ.filter (fun f => repΦ f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, repΦ b = b →
    ∑ f ∈ Finset.univ.filter (fun f => repΦ f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hmassΨ : ∀ g, m₀ ≤ Ψ.mass g)
  (hrepΨ : ∀ f, repΨ (repΨ f) = repΨ f)
  (hPV₁Ψ : ∀ b, repΨ b = b → ∑ f ∈ Finset.univ.filter (fun f => repΨ f = b), Ψ.coeff f = 0)
  (hPV₂Ψ : ∀ b, repΨ b = b →
    ∑ f ∈ Finset.univ.filter (fun f => repΨ f = b), Ψ.coeff f * Ψ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂ in
/-- The mass-insertion limit of a block with counterterm mass `μ`. -/
theorem dec_fLim_rep (P : Params) (he : P.e ≠ 0) (a b : ℝ) {μ : ℝ}
    (hμ : ∀ f, Φ.mass (repΦ f) = μ) {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k)
    (i j : Fin 4) :
    fLim Φ repΦ P.e (fun g => ctPair P.e (Φ.mass g) a b) k i j =
      (ctPair P.e μ a b : ℂ) * fLim Φ repΦ P.e (fun _ => 1) k i j := by
  have t := (tendsto_fLim Φ repΦ hm₀ hmass hrep hPV₁ hPV₂ P he (fun _ => 1) hk i j).const_mul
    (ctPair P.e μ a b : ℂ)
  refine limT_eq (t.congr fun ε => ?_)
  rw [← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  exact congrArg _ (funext fun q => (dec_dBlockD_rep P.e a b hμ ε k q i j).symm)

omit [DecidableEq F] in
theorem dec_fLim_one_congr (hw : DecSameMass Φ Ψ) (e : ℝ) :
    fLim Φ repΦ e (fun _ => 1) = fLim Ψ repΨ e (fun _ => 1) := by
  unfold fLim dBlockD
  congr 1
  funext ε k i j
  congr 1
  funext q
  have := hw fun x => (((1 : ℝ) * x : ℝ) : ℂ) * dBubbleW e x ε k q i j
  simpa only [mul_assoc] using this

include hm₀ hmass hrep hPV₁ hPV₂ in
/-- **Changing the counterterm mass at a photon pair.** -/
theorem dec_qPair_sub_of_rep (hw : DecSameMass Φ Ψ) (P : Params) (he : P.e ≠ 0) {μ μ' : ℝ}
    (hμ : ∀ f, Φ.mass (repΦ f) = μ) (hμ' : ∀ f, Ψ.mass (repΨ f) = μ') (hmassΨ : ∀ g, m₀ ≤ Ψ.mass g)
    (hrepΨ : ∀ f, repΨ (repΨ f) = repΨ f)
    (hPV₁Ψ : ∀ b, repΨ b = b → ∑ f ∈ Finset.univ.filter (fun f => repΨ f = b), Ψ.coeff f = 0)
    (hPV₂Ψ : ∀ b, repΨ b = b →
      ∑ f ∈ Finset.univ.filter (fun f => repΨ f = b), Ψ.coeff f * Ψ.mass f ^ 2 = 0)
    (a b : ℝ) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s) :
    qPair Φ repΦ P.e a b s - qPair Ψ repΨ P.e a b s =
      I * ((ctPair P.e μ a b - ctPair P.e μ' a b : ℝ) : ℂ) *
        projS (fLim Φ repΦ P.e fun _ => 1) s := by
  have hT : (0 : ℝ) < 4 * m₀ ^ 2 := by positivity
  have hv : ∀ (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
      (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ),
      wV Φ P.e A base c a b = wV Ψ P.e A base c a b := by
    intro A base c
    unfold wV
    congr 1
    funext ε k i j
    congr 1
    funext ℓ
    exact hw fun x => gH base c (vNum P.e a b A base c) a b x ε k ℓ i j
  have e1 := dec_projS_lin hT (ctPair P.e μ a b : ℂ)
    (X := fLim Φ repΦ P.e fun g => ctPair P.e (Φ.mass g) a b)
    (Y := fLim Φ repΦ P.e fun _ => 1) (Z := fun _ _ _ => 0)
    (fun k hk i j => by
      rw [dec_fLim_rep hm₀ hmass hrep hPV₁ hPV₂ P he a b hμ hk i j, add_zero]) hs
  have e2 := dec_projS_lin hT (ctPair P.e μ' a b : ℂ)
    (X := fLim Ψ repΨ P.e fun g => ctPair P.e (Ψ.mass g) a b)
    (Y := fLim Ψ repΨ P.e fun _ => 1) (Z := fun _ _ _ => 0)
    (fun k hk i j => by
      rw [dec_fLim_rep hm₀ hmassΨ hrepΨ hPV₁Ψ hPV₂Ψ P he a b hμ' hk i j, add_zero]) hs
  have hz : projS (fun _ _ _ => (0 : ℂ)) s = 0 := by
    unfold projS; split_ifs <;> simp [nProj, trProj]
  rw [hz, add_zero] at e1 e2
  simp only [qPair, hv]
  rw [e1, e2, dec_fLim_one_congr (repΦ := repΦ) (repΨ := repΨ) hw P.e]
  push_cast
  ring

include hm₀ hmass hrep hPV₁ hPV₂ hmassΨ hrepΨ hPV₁Ψ hPV₂Ψ in
/-- **D3b: changing the counterterm mass of a block in the photon-regulator limit.** -/
theorem dec_asmPolLim_sub_of_rep (hw : DecSameMass Φ Ψ) (P : Params) (he : P.e ≠ 0)
    (hF : DecFaceGen P.e) {μ μ' : ℝ} (hμp : 0 < μ) (hμp' : 0 < μ')
    (hμ : ∀ f, Φ.mass (repΦ f) = μ) (hμ' : ∀ f, Ψ.mass (repΨ f) = μ') {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) :
    asmPolLim Φ repΦ P.e s - asmPolLim Ψ repΨ P.e s =
      I * ((3 * P.e ^ 2 / (16 * Real.pi ^ 2) * Real.log (μ ^ 2 / μ' ^ 2) : ℝ) : ℂ) *
        (projS (fLim Φ repΦ P.e fun _ => 1) s - projS (fLim Φ repΦ P.e fun _ => 1) 0) := by
  have h00 : -(4 * m₀ ^ 2) < 0 := by nlinarith
  have tΦ := dec_tendsto_asmPolLim (Φ := Φ) (rep := repΦ) hm₀ hmass hrep P he hPV₁ hPV₂ hF hs
  have tΨ := dec_tendsto_asmPolLim (Φ := Ψ) (rep := repΨ) hm₀ hmassΨ hrepΨ P he hPV₁Ψ hPV₂Ψ hF hs
  have tc := dec_tendsto_ctPair_sub P.e hμp' hμp
  have tc' := ((Complex.continuous_ofReal.tendsto _).comp tc).const_mul I
  have := tc'.mul_const (projS (fLim Φ repΦ P.e fun _ => 1) s -
    projS (fLim Φ repΦ P.e fun _ => 1) 0)
  refine tendsto_nhds_unique (tΦ.sub tΨ) (this.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with Λ hΛ
  have q1 := dec_qPair_sub_of_rep hm₀ hmass hrep hPV₁ hPV₂ hw P he hμ hμ' hmassΨ hrepΨ hPV₁Ψ
    hPV₂Ψ Λ⁻¹ Λ hs
  have q0 := dec_qPair_sub_of_rep hm₀ hmass hrep hPV₁ hPV₂ hw P he hμ hμ' hmassΨ hrepΨ hPV₁Ψ
    hPV₂Ψ Λ⁻¹ Λ h00
  simp only [Function.comp_apply]
  linear_combination -q1 + q0

end QED.GradedProof.RPi4

end
