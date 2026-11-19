/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MassInsLim
public import QED.GradedProof.RPi4PhotonMass

/-!
# (R-Π₄) step L6: the mass-insertion classes at a photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6. After the Ward step
(L2) and the mass-insertion step (L3) the classes `F0`, `F1` enter the order-`e⁴` vacuum
polarization only through the block-summed mass derivative of the bubble, weighted by the
on-shell mass insertion `δ_b = e² (d_m - d₂)(b)` of each block `b`. The photon masses enter only
through `δ_b`. Here:

* `dBlockD Φ rep e δ`: the block sum `∑_f c_f δ(rep f) M_f ∂_M bubble(M_f)` for an arbitrary
  weight `δ`; it is `VPF` (`vpf_dBlockD`, for `e ≠ 0`), and its named limit `fLim` is additive in
  `δ` (`fLim_add`).
* `wCl_F_eq_fLim`: the class limits `W_F0[ctδ D] + W_F1[ctδ D]` are `fLim` at `δ = e²(d_m - d₂)`.
* `ctPair e m a b`: the closed form `(B - A)(-m²)` at the photon pair `(a, b)`; it is additive,
  `ctPair e m a d = ctPair e m a b + ctPair e m b d` (`ctPair_add`, from the logarithm), and it is
  the mass insertion of every on-shell representative (`sq_mul_dm_sub_d₂_eq_ctPair`).
-/

@[expose] public section

open Complex Filter Topology Set intervalIntegral
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

/-! ### The weighted mass-derivative block -/

section Block

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The block sum of mass derivatives of the bubble with weight `δ`**:
`∑_f c_f δ(rep f) M_f ∂_M bubble(M_f)`. -/
noncomputable def dBlockD (e : ℝ) (δ : F → ℝ) (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (((δ (rep f) * Φ.mass f : ℝ) : ℂ) * dBubbleW e (Φ.mass f) ε k q μ ν)

/-- Counterterms realizing the weight `δ` as `e² (d_m - d₂)`. -/
noncomputable def ctOf (e : ℝ) (δ : F → ℝ) : Counterterms F :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun g _ => δ g / e ^ 2, fun _ => 0⟩

omit [DecidableEq F] in
theorem dBlock_eq_dBlockD (P : Params) (D : Counterterms F) :
    dBlock P Φ D rep = dBlockD Φ rep P.e fun g => P.e ^ 2 * (D.dm g 0 - D.d₂ g 0) :=
  rfl

omit [DecidableEq F] in
theorem dBlock_ctOf (P : Params) (he : P.e ≠ 0) (δ : F → ℝ) :
    dBlock P Φ (ctOf P.e δ) rep = dBlockD Φ rep P.e δ := by
  rw [dBlock_eq_dBlockD]
  congr 1
  funext g
  simp only [ctOf]
  field_simp
  ring

omit [DecidableEq F] in
theorem dBlockD_add (e : ℝ) (δ₁ δ₂ : F → ℝ) (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    dBlockD Φ rep e (δ₁ + δ₂) ε k q μ ν =
      dBlockD Φ rep e δ₁ ε k q μ ν + dBlockD Φ rep e δ₂ ε k q μ ν := by
  simp only [dBlockD, ← Finset.sum_add_distrib, Pi.add_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The mass-derivative block of any counterterms is `VPF`.** -/
theorem vpf_dBlock (P : Params) (D : Counterterms F) :
    VPF (m₀ + m₀) fun ε k q μ ν => dBlock P Φ D rep ε k q μ ν := by
  have h := ((vpf_fBubble P Φ (ctδ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ true true false).add
    (vpf_fBubble P Φ (ctδ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ false false true)).add
    ((vpf_remMBlock hm₀ P Φ D rep hmass).mul tendsto_epsI)
  refine h.congr fun ε hε k q μ ν => ?_
  rw [dBlock_eq P Φ D rep hε.ne']

/-- **The weighted block is `VPF`** (for `e ≠ 0`). -/
theorem vpf_dBlockD (P : Params) (he : P.e ≠ 0) (δ : F → ℝ) :
    VPF (m₀ + m₀) fun ε k q μ ν => dBlockD Φ rep P.e δ ε k q μ ν := by
  have h := vpf_dBlock Φ rep hm₀ hmass hrep hPV₁ hPV₂ P (ctOf P.e δ)
  rwa [dBlock_ctOf Φ rep P he δ] at h

end Block

section Lim

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The named limit of the weighted block.** -/
noncomputable def fLim (e : ℝ) (δ : F → ℝ) : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  limT fun ε k μ ν => QED.OneLoop.energyFirstIntegral fun q => dBlockD Φ rep e δ ε k q μ ν

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

theorem tendsto_fLim (P : Params) (he : P.e ≠ 0) (δ : F → ℝ) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q => dBlockD Φ rep P.e δ ε k q μ ν)
      (𝓝[>] 0) (𝓝 (fLim Φ rep P.e δ k μ ν)) :=
  tendsto_limT_of_hasVPLim (vpf_dBlockD Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ).hasVPLim
    (by nlinarith) μ ν

/-- **The limit of the weighted block is additive in the weight.** -/
theorem fLim_add (P : Params) (he : P.e ≠ 0) (δ₁ δ₂ : F → ℝ) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    fLim Φ rep P.e (δ₁ + δ₂) k μ ν = fLim Φ rep P.e δ₁ k μ ν + fLim Φ rep P.e δ₂ k μ ν := by
  have h1 := tendsto_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ₁ hk μ ν
  have h2 := tendsto_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ₂ hk μ ν
  refine limT_eq ((h1.add h2).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have i1 := (vpf_dBlockD Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ₁).2 ε hε k μ ν
  have i2 := (vpf_dBlockD Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he δ₂).2 ε hε k μ ν
  rw [← efi_add i1 i2]
  exact congrArg _ (funext fun q => (dBlockD_add Φ rep P.e δ₁ δ₂ ε k q μ ν).symm)

/-- **The mass-insertion class limits are the limit of the weighted block** at
`δ = e² (d_m - d₂)`. -/
theorem wCl_F_eq_fLim (P : Params) (he : P.e ≠ 0) (D : Counterterms F)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    wCl P Φ (ctδ D) repF0 k μ ν + wCl P Φ (ctδ D) repF1 k μ ν =
      fLim Φ rep P.e (fun g => P.e ^ 2 * (D.dm g 0 - D.d₂ g 0)) k μ ν := by
  have h := tendsto_dBlock P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD hk μ ν
  rw [dBlock_eq_dBlockD] at h
  exact tendsto_nhds_unique h (tendsto_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ hk μ ν)

end Lim

/-! ### The on-shell mass insertion at a photon pair -/

/-- **The on-shell mass insertion `(B - A)(-m²)` at the photon pair `(a, b)`.** -/
noncomputable def ctPair (e m a b : ℝ) : ℝ :=
  -(e ^ 2 / (4 * Real.pi ^ 2)) * (∫ x in (0 : ℝ)..1, onShellL m a b x) +
    e ^ 2 / (8 * Real.pi ^ 2) * ∫ x in (0 : ℝ)..1, (1 - x) * onShellL m a b x

theorem onShellL_add {m a b d x : ℝ} (hm : m ≠ 0) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hx : x ∈ Icc (0 : ℝ) 1) : onShellL m a d x = onShellL m a b x + onShellL m b d x := by
  have pa := onShell_denom_pos hm hx (pow_pos ha 2)
  have pb := onShell_denom_pos hm hx (pow_pos hb 2)
  have pd := onShell_denom_pos hm hx (pow_pos hd 2)
  simp only [onShellL]
  rw [← Real.log_mul (div_pos pb pa).ne' (div_pos pd pb).ne']
  congr 1
  field_simp

theorem continuousOn_onShellL {m a b : ℝ} (hm : m ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (onShellL m a b) (uIcc (0 : ℝ) 1) := by
  rw [uIcc_of_le zero_le_one]
  refine ContinuousOn.log ?_ fun x hx => ?_
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    exact (onShell_denom_pos hm hx (pow_pos ha 2)).ne'
  · exact (div_pos (onShell_denom_pos hm hx (pow_pos hb 2))
      (onShell_denom_pos hm hx (pow_pos ha 2))).ne'

/-- **The on-shell mass insertion is additive in the photon pair.** -/
theorem ctPair_add (e : ℝ) {m a b d : ℝ} (hm : m ≠ 0) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ctPair e m a d = ctPair e m a b + ctPair e m b d := by
  have c1 := continuousOn_onShellL hm ha hb
  have c2 := continuousOn_onShellL hm hb hd
  have hL : ∀ x ∈ uIcc (0 : ℝ) 1, onShellL m a d x = onShellL m a b x + onShellL m b d x :=
    fun x hx => onShellL_add hm ha hb hd (by rwa [uIcc_of_le zero_le_one] at hx)
  have hL' : ∀ x ∈ uIcc (0 : ℝ) 1, (1 - x) * onShellL m a d x =
      (1 - x) * onShellL m a b x + (1 - x) * onShellL m b d x :=
    fun x hx => by rw [hL x hx, mul_add]
  have i1 : IntervalIntegrable (fun x => (1 - x) * onShellL m a b x) MeasureTheory.volume 0 1 :=
    (ContinuousOn.mul (by fun_prop) c1).intervalIntegrable
  have i2 : IntervalIntegrable (fun x => (1 - x) * onShellL m b d x) MeasureTheory.volume 0 1 :=
    (ContinuousOn.mul (by fun_prop) c2).intervalIntegrable
  simp only [ctPair]
  rw [integral_congr hL, integral_congr hL',
    integral_add c1.intervalIntegrable c2.intervalIntegrable, integral_add i1 i2]
  ring

/-- **The mass insertion of an on-shell flavour is `ctPair` at its mass and the photon pair of
the model.** -/
theorem sq_mul_dm_sub_d₂_eq_ctPair {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {f : F} (hf : 0 < Φ.mass f) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hon : IsOnShellAt P Φ D f 1) :
    P.e ^ 2 * (D.dm f 0 - D.d₂ f 0) = ctPair P.e (Φ.mass f) P.mγ P.Λ := by
  rw [sq_mul_dm_sub_d₂ hf hmγ hΛ hon, onShellδm_sub_onShellδ₂_eq_integral]
  rfl

end QED.GradedProof.RPi4

end
