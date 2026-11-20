/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1EPiOne
public import QED.GradedProof.X1CStatement
public import QED.GradedProof.X1DOffLim

/-!
# (X₁) piece E: the photon legs near `q = 0`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece E. In the Dyson decomposition `QED.GradedProof.X1C.dysonFive` the photon
leg of order `2d` is evaluated at `q = r' - r`, which tends to `0` at the LSZ point `(p, p)`. The
assembly (piece F) needs: for every `d ≤ 2` and indices `ν μ`, the leg has an `ε → 0⁺` limit
near `q = 0`, continuous at `q = 0`, with value `δ_{d0} δ_ν^μ` there. This is
`ZLim (fun ε q => photonLeg { P with ε := ε } Φ D d q ν μ) 0 (if d = 0 ∧ ν = μ then 1 else 0)`.

* `ZLim`: a limit near the point, continuous there, with a given value; closed under sums and
  products;
* `zLim_photonProp`: the photon propagator, with the `ε = 0` propagator as limit;
* `zLim_photonLeg`: the photon legs of orders `0`, `2`, `4`, from `vpZeroLim_one`,
  `vpZeroLim_two`.
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1E

section ZLim

variable {Y : Type*} [TopologicalSpace Y]

/-- `F ε y` has an `ε → 0⁺` limit `G y` at every `y` near `y₀`, `G` is continuous at `y₀`, and
`G y₀ = v`. -/
def ZLim (F : ℝ → Y → ℂ) (y₀ : Y) (v : ℂ) : Prop :=
  ∃ G : Y → ℂ, (∀ᶠ y in 𝓝 y₀, Tendsto (fun ε => F ε y) (𝓝[>] 0) (𝓝 (G y))) ∧
    ContinuousAt G y₀ ∧ G y₀ = v

namespace ZLim

variable {F H : ℝ → Y → ℂ} {y₀ : Y} {v w : ℂ}

theorem const (a : ℂ) : ZLim (fun _ _ => a) y₀ a :=
  ⟨fun _ => a, Eventually.of_forall fun _ => tendsto_const_nhds, continuousAt_const, rfl⟩

theorem add (hF : ZLim F y₀ v) (hH : ZLim H y₀ w) :
    ZLim (fun ε y => F ε y + H ε y) y₀ (v + w) := by
  obtain ⟨G, hG, hGc, rfl⟩ := hF
  obtain ⟨K, hK, hKc, rfl⟩ := hH
  exact ⟨fun y => G y + K y, by filter_upwards [hG, hK] with y h1 h2 using h1.add h2,
    hGc.add hKc, rfl⟩

theorem mul (hF : ZLim F y₀ v) (hH : ZLim H y₀ w) :
    ZLim (fun ε y => F ε y * H ε y) y₀ (v * w) := by
  obtain ⟨G, hG, hGc, rfl⟩ := hF
  obtain ⟨K, hK, hKc, rfl⟩ := hH
  exact ⟨fun y => G y * K y, by filter_upwards [hG, hK] with y h1 h2 using h1.mul h2,
    hGc.mul hKc, rfl⟩

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → Y → ℂ} {v : ι → ℂ}
    (h : ∀ i ∈ s, ZLim (F i) y₀ (v i)) :
    ZLim (fun ε y => ∑ i ∈ s, F i ε y) y₀ (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const 0 : ZLim (fun _ _ => (0 : ℂ)) y₀ 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr_val (hF : ZLim F y₀ v) (h : v = w) : ZLim F y₀ w := h ▸ hF

/-- A `ZLim` carries an `OffLim` (`QED.GradedProof.X1D.OffLim`). -/
theorem offLim (hF : ZLim F y₀ v) : QED.GradedProof.X1D.OffLim F y₀ := by
  obtain ⟨G, hG, hGc, -⟩ := hF
  exact ⟨G, hG, hGc⟩

end ZLim

end ZLim

/-- The `ε = 0` photon propagator is continuous at `q = 0` for positive regulator masses. -/
theorem continuousAt_photonPropagator_zero {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) (ν ρ : Fin 4) :
    ContinuousAt (fun q => QED.OneLoop.photonPropagator mγ Λ 0 q ν ρ) 0 := by
  have h : ∀ M : ℝ, 0 < M → ContinuousAt (fun q : Fin 4 → ℝ =>
      (((Minkowski.dot q q + M ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)⁻¹) 0 := fun M hM => by
    refine ContinuousAt.inv₀ ?_ ?_
    · exact ((continuous_ofReal.comp (continuous_dot_self.add continuous_const)).sub
        continuous_const).continuousAt
    · rw [dot_zero_self]
      push_cast
      simp only [zero_mul, sub_zero, zero_add]
      exact pow_ne_zero 2 (ofReal_ne_zero.mpr hM.ne')
  unfold QED.OneLoop.photonPropagator
  exact continuousAt_const.mul ((h mγ hmγ).sub (h Λ hΛ))

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

open QED.GradedProof.X1C

theorem zLim_photonProp (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (ν ρ : Fin 4) :
    ZLim (fun ε q => photonProp { P with ε := ε } q ν ρ) 0
      (QED.OneLoop.photonPropagator P.mγ P.Λ 0 0 ν ρ) := by
  have hγ : ∀ᶠ q in 𝓝 (0 : Fin 4 → ℝ), -P.mγ ^ 2 < Minkowski.dot q q :=
    eventually_dot_gt (pow_pos hmγ 2)
  have hL : ∀ᶠ q in 𝓝 (0 : Fin 4 → ℝ), -P.Λ ^ 2 < Minkowski.dot q q :=
    eventually_dot_gt (pow_pos hΛ 2)
  refine ⟨fun q => QED.OneLoop.photonPropagator P.mγ P.Λ 0 q ν ρ, ?_,
    continuousAt_photonPropagator_zero hmγ hΛ ν ρ, rfl⟩
  filter_upwards [hγ, hL] with q h1 h2
  exact QED.WickModel.tendsto_photonPropagator_zero h1.ne' h2.ne' ν ρ

theorem zLim_of_vpZeroLim {n : ℕ} (h : VPZeroLim P Φ D n) (μ ν : Fin 4) :
    ZLim (fun ε k => vacuumPolarizationPart { P with ε := ε } Φ D n k μ ν) 0 0 := by
  obtain ⟨G, hG, hc⟩ := h
  exact ⟨fun k => G k μ ν, hG.mono fun k hk => hk μ ν, (hc μ ν).1, (hc μ ν).2⟩

/-- **The photon legs near `q = 0`**, from the order-`2` and order-`4` vacuum-polarization
limits. -/
theorem zLim_photonLeg (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (h₁ : VPZeroLim P Φ D 1)
    (h₂ : VPZeroLim P Φ D 2) {d : ℕ} (hd : d < 3) (ν μ : Fin 4) :
    ZLim (fun ε q => photonLeg { P with ε := ε } Φ D d q ν μ) 0
      (if d = 0 ∧ ν = μ then 1 else 0) := by
  have Δ := zLim_photonProp P hmγ hΛ
  have P1 := zLim_of_vpZeroLim P Φ D h₁
  have P2 := zLim_of_vpZeroLim P Φ D h₂
  interval_cases d
  · by_cases h : ν = μ
    · simpa [photonLeg, h] using (ZLim.const 1 : ZLim (fun _ (_ : Fin 4 → ℝ) => (1 : ℂ)) 0 1)
    · simpa [photonLeg, h] using (ZLim.const 0 : ZLim (fun _ (_ : Fin 4 → ℝ) => (0 : ℂ)) 0 0)
  · refine (ZLim.sum Finset.univ fun ρ _ => (Δ ν ρ).mul (P1 μ ρ)).congr_val ?_
    simp
  · refine ((ZLim.sum Finset.univ fun ρ _ => (Δ ν ρ).mul (P2 μ ρ)).add
      (ZLim.sum Finset.univ fun ρ _ => ZLim.sum Finset.univ fun l _ =>
        ZLim.sum Finset.univ fun k _ => ((Δ ν ρ).mul (P1 l ρ)).mul ((Δ l k).mul (P1 μ k)))
      ).congr_val ?_
    simp

/-- **(X₁) piece E**: under the hypotheses of (X₁), every photon leg of order `2d ≤ 4` has an
`ε → 0⁺` limit near `q = 0`, continuous at `q = 0`, with value `δ_{d0} δ_ν^μ`. -/
theorem zLim_photonLeg_self (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) {d : ℕ} (hd : d < 3) (ν μ : Fin 4) :
    ZLim (fun ε q => photonLeg { P with ε := ε } Φ D d q ν μ) 0
      (if d = 0 ∧ ν = μ then 1 else 0) :=
  zLim_photonLeg P Φ D hmγ hΛ (vpZeroLim_one P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD)
    (vpZeroLim_two P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD) hd ν μ

end QED.GradedProof.X1E

end
