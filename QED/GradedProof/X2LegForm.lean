/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X2Lsz
public import QED.GradedProof.X2Transverse
public import QED.GradedProof.RPi4Setup
public import QED.Frozen.OneLoop.IsFormFactorPair

/-!
# (X₂) piece F: the photon legs on transverse vectors

Helper level for the Phase 5 Stage 2 goal (X₂)
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` (decision D-57), piece F. At the
photon momentum `q` the `ε = 0` photon propagator is `g_{νρ} D(q²)` (Feynman gauge), and the
vacuum-polarization limits are transverse: `Π⁽²⁾_{μρ}(q) = Pol₁(q²) (q² g_{μρ} - q_μ q_ρ)`
(`polOne`, explicit) and `Π⁽⁴⁾_{μρ}(q) = Pol₂(q²) (q² g_{μρ} - q_μ q_ρ)` (by uniqueness of limits
with the sealed (G-Pi₂) form). So on vectors `Y` with `q_ν Y^ν = 0` the photon legs act as scalars:
`L⁽²⁾ Y = κ Y`, `L⁽⁴⁾ Y = (D Pol₂ q² + κ²) Y` with `κ = D Pol₁ q²`. The vectors `ū' γ^ν u` and
`ū' V^ν u` for `V` with a form-factor pair are transverse at `q = p' - p` on shell, so
(`lszFive_eq`) the LSZ amplitude of piece E is `ū' V⁽⁵⁾ u + e c ū' γ^μ u + κ ū' V⁽³⁾ u`.
Finally `κ → 0` as `q² → 0` at fixed regulators (`exists_kappa_small`).

* `dprop`, `photonPropagator_zero_eq`, `continuousAt_dprop_zero`;
* `polOne`, `piOneLim_eq`, `continuousAt_polOne_zero`;
* `exists_piTwoLim_eq`;
* `sum_legOne_mul`, `sum_legTwo_mul`, `dotProduct_tree_mulVec`, `lszFive_eq`,
  `exists_kappa_small`.
-/

@[expose] public section

open Matrix Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X2

open QED.GradedProof.VP2 QED.GradedProof.PhotonSplit QED.Lepton.Proof.HM
open QED.GradedProof.X1E (piOneLim piTwoLim oneParams)

/-! ### The propagator and the vacuum-polarization limits -/

/-- The scalar factor `D(s) = 1/(s + m_γ²) - 1/(s + Λ²)` of the `ε = 0` photon propagator. -/
noncomputable def dprop (mγ Λ s : ℝ) : ℂ :=
  (((s + mγ ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)⁻¹ - (((s + Λ ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)⁻¹

theorem photonPropagator_zero_eq (mγ Λ : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ 0 k ν ρ =
      ((Minkowski.metric ν ρ : ℝ) : ℂ) * dprop mγ Λ (Minkowski.dot k k) :=
  rfl

theorem continuousAt_dprop_zero {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ContinuousAt (dprop mγ Λ) 0 := by
  have h : ∀ M : ℝ, 0 < M → ContinuousAt
      (fun s : ℝ => (((s + M ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)⁻¹) 0 := fun M hM => by
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    simp only [zero_add, ofReal_zero, zero_mul, sub_zero, ne_eq, ofReal_eq_zero]
    positivity
  exact (h mγ hmγ).sub (h Λ hΛ)

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- The scalar coefficient of the order-`2` vacuum-polarization limit. -/
noncomputable def polOne (s : ℝ) : ℂ :=
  ((-(oneParams P D).δ₃ + QED.WickModel.vacuumPolarizationLoop (refParams (oneParams P D)) s
    : ℝ) : ℂ) +
    ∑ i, (atomCoeff Φ i : ℂ) * ((-(oneParams P D).δ₃ + QED.WickModel.vacuumPolarizationLoop
      (blockParams (oneParams P D) Φ i) s : ℝ) : ℂ)

omit [DecidableEq F] in
theorem piOneLim_eq (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    piOneLim P Φ D k μ ν = polOne P Φ D (Minkowski.dot k k) * vpT k μ ν := by
  simp only [piOneLim, polOne, add_mul, Finset.sum_mul, mul_assoc]

omit [DecidableEq F] in
theorem continuousAt_polOne_zero {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    ContinuousAt (polOne P Φ D) 0 := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hX := four_le_bigX Φ
  have hL : ∀ {Q : Params}, 0 < Q.m → Q.m < Q.M₁ → Q.m < Q.M₂ →
      ContinuousAt (QED.WickModel.vacuumPolarizationLoop Q) 0 := fun {Q} hm hM₁ hM₂ =>
    (QED.WickModel.continuousOn_vacuumPolarizationLoop hm hM₁ hM₂).continuousAt
      (Ioi_mem_nhds (by have := pow_pos hm 2; linarith))
  have href := hL (Q := refParams (oneParams P D)) (by norm_num [refParams])
    (by norm_num [refParams]) (by norm_num [refParams])
  have hblk : ∀ i, ContinuousAt (QED.WickModel.vacuumPolarizationLoop
      (blockParams (oneParams P D) Φ i)) 0 := fun i =>
    hL (atomMass_pos Φ hpos i) (atomMass_lt_bigX Φ i)
      (by show atomMass Φ i < bigX Φ + 1; linarith [atomMass_lt_bigX Φ i])
  exact (continuous_ofReal.continuousAt.comp (continuousAt_const.add href)).add
    (tendsto_finsetSum _ fun i _ => continuousAt_const.mul
      (continuous_ofReal.continuousAt.comp (continuousAt_const.add (hblk i))))

/-- **The order-`4` vacuum-polarization limit is transverse** (sealed (G-Pi₂) form, by
uniqueness of limits). -/
theorem exists_piTwoLim_eq (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 2) :
    ∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * m₀ ^ 2) < Minkowski.dot k k → ∀ μ ν : Fin 4,
      piTwoLim P Φ D rep m₀ k μ ν = Pol (Minkowski.dot k k) * vpT k μ ν := by
  obtain ⟨Pol, hPol⟩ := RPi4.exists_pol P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD
  have hD₁ : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 := fun f => (hD.1 f 0 (by norm_num)).1
  have hD₂ : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 :=
    fun f => (hD.1 f 0 (by norm_num)).2
  refine ⟨Pol, fun k hk μ ν => tendsto_nhds_unique
    (X1E.tendsto_piTwo P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD₁ hD₂ hk μ ν) ?_⟩
  exact hPol k hk μ ν

/-! ### The photon legs on transverse vectors -/

/-- A chain `∑_ρ g_{νρ} d · a (q² g_{μρ} - q_μ q_ρ)` on a transverse vector. -/
theorem sum_legOne_mul (q : Fin 4 → ℝ) {dd a : ℂ} {prop Pi : Fin 4 → Fin 4 → ℂ}
    (hprop : ∀ ν ρ, prop ν ρ = ((Minkowski.metric ν ρ : ℝ) : ℂ) * dd)
    (hPi : ∀ μ ρ, Pi μ ρ = a * vpT q μ ρ) (Y : Fin 4 → ℂ)
    (hY : ∑ ν, ((Minkowski.lower q ν : ℝ) : ℂ) * Y ν = 0) (μ : Fin 4) :
    ∑ ν, (∑ ρ, prop ν ρ * Pi μ ρ) * Y ν = dd * a * ((Minkowski.dot q q : ℝ) : ℂ) * Y μ := by
  have e : ∀ ν, ∑ ρ, prop ν ρ * Pi μ ρ =
      ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) * (dd * a * vpT q μ ρ) := fun ν =>
    Finset.sum_congr rfl fun ρ _ => by rw [hprop, hPi]; ring
  simp only [e]
  exact sum_leg_mul_of_transverse q (dd * a) Y hY μ

/-- The order-`4` chain `Δ Π₂ + Δ Π₁ Δ Π₁` on a transverse vector. -/
theorem sum_legTwo_mul (q : Fin 4 → ℝ) {dd a b : ℂ} {prop Pi₁ Pi₂ : Fin 4 → Fin 4 → ℂ}
    (hprop : ∀ ν ρ, prop ν ρ = ((Minkowski.metric ν ρ : ℝ) : ℂ) * dd)
    (h₁ : ∀ μ ρ, Pi₁ μ ρ = a * vpT q μ ρ) (h₂ : ∀ μ ρ, Pi₂ μ ρ = b * vpT q μ ρ) (Y : Fin 4 → ℂ)
    (hY : ∑ ν, ((Minkowski.lower q ν : ℝ) : ℂ) * Y ν = 0) (μ : Fin 4) :
    ∑ ν, (∑ ρ, prop ν ρ * Pi₂ μ ρ +
      ∑ ρ, ∑ l, ∑ k, prop ν ρ * Pi₁ l ρ * (prop l k * Pi₁ μ k)) * Y ν =
      (dd * b * ((Minkowski.dot q q : ℝ) : ℂ) +
        (dd * a * ((Minkowski.dot q q : ℝ) : ℂ)) ^ 2) * Y μ := by
  set T : Fin 4 → ℂ := fun l => ∑ k, prop l k * Pi₁ μ k with hT
  have e : ∀ ν, ∑ ρ, ∑ l, ∑ k, prop ν ρ * Pi₁ l ρ * (prop l k * Pi₁ μ k) =
      ∑ l, (∑ ρ, prop ν ρ * Pi₁ l ρ) * T l := fun ν => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hT, Finset.mul_sum]
  have e2 : ∑ ν, (∑ l, (∑ ρ, prop ν ρ * Pi₁ l ρ) * T l) * Y ν =
      ∑ l, (∑ ν, (∑ ρ, prop ν ρ * Pi₁ l ρ) * Y ν) * T l := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun ρ _ => by ring
  have e3 : ∑ l, (∑ ν, (∑ ρ, prop ν ρ * Pi₁ l ρ) * Y ν) * T l =
      dd * a * ((Minkowski.dot q q : ℝ) : ℂ) * ∑ l, T l * Y l := by
    simp only [sum_legOne_mul q hprop h₁ Y hY, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e4 : ∑ l, T l * Y l = dd * a * ((Minkowski.dot q q : ℝ) : ℂ) * Y μ :=
    sum_legOne_mul q hprop h₁ Y hY μ
  simp only [add_mul, Finset.sum_add_distrib, e, e2, e3, e4, sum_legOne_mul q hprop h₂ Y hY]
  ring

/-! ### The LSZ amplitude on shell -/

/-- `ū' (e γ^ν) u = e ū' γ^ν u` for the tree vertex as a matrix. -/
theorem dotProduct_tree_mulVec (e : ℝ) (w u : Fin 4 → ℂ) (ν : Fin 4) :
    w ⬝ᵥ ((Matrix.of fun i j => (e : ℂ) * Dirac.gamma ν i j) *ᵥ u) =
      (e : ℂ) * (w ⬝ᵥ (Dirac.gamma ν *ᵥ u)) := by
  have h : (Matrix.of fun i j => (e : ℂ) * Dirac.gamma ν i j) = (e : ℂ) • Dirac.gamma ν := by
    ext i j
    simp
  rw [h, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

omit [DecidableEq F] in
/-- **The LSZ amplitude of piece E on shell**: with transverse vacuum-polarization limits at
`q = p' - p` and an order-`3` vertex limit `V₁` with a form-factor pair, the photon legs act as
scalars, so `M = ū' V₂ u + e (D Pol₂ q² + κ²) ū' γ^μ u + κ ū' V₁ u`, `κ = D a q²`. -/
theorem lszFive_eq (rep : F → F) (m₀ : ℝ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -Φ.mass Φ.openLine ^ 2)
    (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2) {a b : ℂ}
    (h₁ : ∀ μ ρ, piOneLim P Φ D (p' - p) μ ρ = a * vpT (p' - p) μ ρ)
    (h₂ : ∀ μ ρ, piTwoLim P Φ D rep m₀ (p' - p) μ ρ = b * vpT (p' - p) μ ρ)
    {V₁ V₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {e' : ℝ} {G : ℂ × ℂ}
    (hV₁ : QED.OneLoop.IsFormFactorPair e' (Φ.mass Φ.openLine) p' p V₁ G)
    (s' s : Fin 2) (μ : Fin 4) :
    lszFive P Φ D rep m₀ V₁ V₂ p' p s' s μ =
      Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p' s') ⬝ᵥ
          (V₂ μ *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s) +
        (P.e : ℂ) * (dprop P.mγ P.Λ (Minkowski.dot (p' - p) (p' - p)) * b *
            ((Minkowski.dot (p' - p) (p' - p) : ℝ) : ℂ) +
          (dprop P.mγ P.Λ (Minkowski.dot (p' - p) (p' - p)) * a *
            ((Minkowski.dot (p' - p) (p' - p) : ℝ) : ℂ)) ^ 2) *
          (Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p' s') ⬝ᵥ
            (Dirac.gamma μ *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s)) +
        dprop P.mγ P.Λ (Minkowski.dot (p' - p) (p' - p)) * a *
            ((Minkowski.dot (p' - p) (p' - p) : ℝ) : ℂ) *
          (Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p' s') ⬝ᵥ
            (V₁ μ *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s)) := by
  set m := Φ.mass Φ.openLine
  set w := Dirac.bar (Dirac.spinor m p' s')
  set u := Dirac.spinor m p s
  have hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u) := Dirac.slash_mulVec_spinor _ p hp s
  have hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w) :=
    Dirac.bar_vecMul_slash _ p' _ (Dirac.slash_mulVec_spinor _ p' hp' s')
  have hY₁ : ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) * (w ⬝ᵥ (V₁ ν *ᵥ u)) = 0 := by
    simp only [fun ν => hV₁ ν u w hu hw, mul_left_comm _ (e' : ℂ), ← Finset.mul_sum,
      sum_lower_mul_formFactor_sandwich hu hw G.1 G.2, mul_zero]
  have hY₂ : ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) *
      (w ⬝ᵥ ((Matrix.of fun i j => (P.e : ℂ) * Dirac.gamma ν i j) *ᵥ u)) = 0 := by
    simp only [dotProduct_tree_mulVec, mul_left_comm _ (P.e : ℂ), ← Finset.mul_sum,
      sum_lower_mul_gamma_sandwich hu hw, mul_zero]
  have hprop := photonPropagator_zero_eq P.mγ P.Λ (p' - p)
  have L₁ := sum_legOne_mul (p' - p) hprop h₁ _ hY₁ μ
  have L₂ := sum_legTwo_mul (p' - p) hprop h₁ h₂ _ hY₂ μ
  change w ⬝ᵥ (V₂ μ *ᵥ u) + (∑ ν, (∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ 0 (p' - p) ν ρ *
      piOneLim P Φ D (p' - p) μ ρ) * (w ⬝ᵥ (V₁ ν *ᵥ u))) +
    ∑ ν, (∑ ρ, QED.OneLoop.photonPropagator P.mγ P.Λ 0 (p' - p) ν ρ *
        piTwoLim P Φ D rep m₀ (p' - p) μ ρ +
      ∑ ρ, ∑ l, ∑ k, QED.OneLoop.photonPropagator P.mγ P.Λ 0 (p' - p) ν ρ *
        piOneLim P Φ D (p' - p) l ρ * (QED.OneLoop.photonPropagator P.mγ P.Λ 0 (p' - p) l k *
          piOneLim P Φ D (p' - p) μ k)) *
      (w ⬝ᵥ ((Matrix.of fun i j => (P.e : ℂ) * Dirac.gamma ν i j) *ᵥ u)) = _
  rw [L₁, L₂, dotProduct_tree_mulVec]
  ring

omit [DecidableEq F] in
/-- **`κ = D(s) Pol₁(s) s → 0` as `s → 0`** at fixed regulators. -/
theorem exists_kappa_small {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, ∀ s : ℝ, |s| < δ → ‖dprop P.mγ P.Λ s * polOne P Φ D s * (s : ℂ)‖ < t := by
  have hc : ContinuousAt (fun s : ℝ => dprop P.mγ P.Λ s * polOne P Φ D s * (s : ℂ)) 0 :=
    ((continuousAt_dprop_zero hmγ hΛ).mul (continuousAt_polOne_zero P Φ D hm₀ hmass)).mul
      continuous_ofReal.continuousAt
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc t ht
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have := h (x := s) (by simpa [Real.dist_eq] using hs)
  simpa [dist_eq_norm] using this

end QED.GradedProof.X2

end
