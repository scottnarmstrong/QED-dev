/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBWickInt
public import QED.ChainProof.SetCMainDKLink
public import QED.ChainProof.SetCUnitMAbsFub
public import QED.ChainProof.SetCUnitMDispEps

/-!
# Set (c), the bubble classes: the split of the inserted vacuum polarization

Helper level for set (c), the bubble classes `QED.ChainProof.SetCLink.repB i`, at fixed
`ε > 0`. With the bubble in closed form the outer integrand is the insertion `-T(k)^{ab}` into
`repD i 0` (`QED.ChainProof.SetCMainB.outerBub_outerBW`), `T = i Π̂_ε(k²)(k² g - k k) + ε S_ε g`.
After the integration by parts in the Feynman parameter
(`QED.TwoLoop.VPHalfAt.vpLoopEps_eq_spectral`),
`Π̂_ε(s) = c (L_ε / 6 - J_ε(s))`, `c = e²/(2π²)`, `L_ε = ∑_f c_f log(M_f² - iε)`,
`J_ε(s) = ∫₀¹ ∑_f c_f (1 - 2x) s / (M_f² + x(1-x)s - iε) · (x²/2 - x³/3) dx`, the insertion is

`-T = (c L_ε / 3) · ctF 1 + (-2 c J_ε(k²)) · ctGD 1 + rest`,
`rest = (-2 c J_ε(k²)) · ctKD 1 - ε S_ε(k²) g`:

* (i) the log constant times the `photonCt` factor with `δ₃ = 1`, i.e. the transverse plus the
  longitudinal part of `repD i 0` at `δ₃ = 1` (`insD_ctF`);
* (ii) the transverse dispersive part `(-2 c J_ε(k²)) k² g`; at the Feynman parameter `x` and
  flavour `f` it is the transverse unit of `repB` (`QED.ChainProof.SetCUnitM.repBKappa x`, the
  spectral mass `M_f`, `(k²)²`) times `wD 1` (`dispIns_eq_unit`);
* the rest: the longitudinal dispersive part and the `ε S_ε` part.

Results:

* `insD_add`, `insD_mul_fun`, `insD_smul`, `insD_ctF`: linearity of the insertion;
* **`neg_vpT_split`**, **`outerBub_split`**: the split of the insertion and of the outer
  integrand;
* `unitMIntegrand_last_extra`, **`unitMIntegrand_repB_succ`**: the transverse unit of `repB` is
  the unit of `repD` times `k² / (M² + x(1-x)k² - iε)`;
* `vpJ_mul`, **`dispIns_eq_unit`**: the piece (ii) as a sum over flavours of integrals over the
  Feynman parameter of units;
* **`jointEnergyFirstIntegral_dispIns`**: its value `-2c · wD 1 · ∑_f ∫₀¹ w_f(x) I_ε(x) dx`, the
  form of `QED.ChainProof.SetCUnitM.tendsto_integral_unitMValue_repB`;
* **`jointEnergyFirstIntegral_outerBub_split`**: for an outer integrand integrable in both
  stages, its value is `(c L_ε / 3)(V_G + V_K) + (-2c · wD 1 · ∑_f ∫₀¹ w_f I_ε) + V_rest`,
  `V_G`, `V_K` the transverse and longitudinal values of `repD i 0` at `δ₃ = 1`, and the rest is
  integrable in both stages.
-/

@[expose] public section

open Complex MeasureTheory Set
open QED.WickModel (Params Contraction lineMomentum₂ photonMomentum₂)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.GradedProof.X0
open QED.ChainProof.SetCMain (dGIntegrand dKIntegrand wD sqD chgD chgMD chgAD
  dGIntegrand_repD_eq_unit photonMomentum₂_repD_sq isUnit_det_chgMD)
open QED.ChainProof.SetCUnitM
open QED.ChainProof.Enum (pc)
open QED.TwoLoop.VPHalfAt (vpLoopEps vpExtraEps vpRatSum vpLoopEps_eq_spectral)
open QED.TwoLoop.VPHalfAtAssembly (vpT mem_Ioo_mul_pos)
open QED.WickModel (vacuumPolarizationFeynmanMass)
open QED.TwoLoop.Enumeration (Class5)
open QED.TwoLoop.ClassIntegrable (openClasses)

variable {F : Type}

/-! ### Linearity of the insertion -/

section Lin

variable (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 1 kD)
  (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ)

theorem insD_add (X Y : (Wick.PhotonSlot kD → Fin 4) → (Fin 4 → ℝ) → ℂ) :
    insD P Φ (fun lor k => X lor k + Y lor k) C pOut pIn kIn αOut βIn μ ℓ =
      insD P Φ X C pOut pIn kIn αOut βIn μ ℓ + insD P Φ Y C pOut pIn kIn αOut βIn μ ℓ := by
  unfold insD
  simp only [add_mul, mul_add, Finset.sum_add_distrib]

/-- A factor depending only on the photon momentum comes out of the insertion. -/
theorem insD_mul_fun (h : (Fin 4 → ℝ) → ℂ)
    (X : (Wick.PhotonSlot kD → Fin 4) → (Fin 4 → ℝ) → ℂ) :
    insD P Φ (fun lor k => h k * X lor k) C pOut pIn kIn αOut βIn μ ℓ =
      h (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
        insD P Φ X C pOut pIn kIn αOut βIn μ ℓ := by
  unfold insD
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  ring

theorem insD_smul (c : ℂ) (X : (Wick.PhotonSlot kD → Fin 4) → (Fin 4 → ℝ) → ℂ) :
    insD P Φ (fun lor k => c * X lor k) C pOut pIn kIn αOut βIn μ ℓ =
      c * insD P Φ X C pOut pIn kIn αOut βIn μ ℓ :=
  insD_mul_fun P Φ C pOut pIn kIn αOut βIn μ ℓ (fun _ => c) X

/-- The `photonCt` insertion is the transverse plus the longitudinal part. -/
theorem insD_ctF [Fintype F] [DecidableEq F] (δ₃ : ℝ) :
    insD P Φ (ctF δ₃) C pOut pIn kIn αOut βIn μ ℓ =
      dGIntegrand P Φ δ₃ C pOut pIn kIn αOut βIn μ ℓ +
        dKIntegrand P Φ δ₃ C pOut pIn kIn αOut βIn μ ℓ := by
  rw [show ctF δ₃ = fun lor k => ctGD δ₃ lor k + ctKD δ₃ lor k from
    funext fun lor => funext fun k => ctF_eq δ₃ lor k, insD_add]
  rfl

end Lin

/-! ### The split of the inserted vacuum polarization -/

/-- The constant `e²/(2π²)`. -/
noncomputable def vpCst (P : Params) : ℂ := ((P.e ^ 2 / (2 * Real.pi ^ 2) : ℝ) : ℂ)

/-- The log constant `L_ε = ∑_f c_f log(M_f² - iε)`. -/
noncomputable def bubLogSum (P : Params) (ε : ℝ) : ℂ :=
  ∑ f, (P.loopCoeff f : ℂ) * log (((P.mass f ^ 2 : ℝ) : ℂ) - ε * I)

/-- The dispersive integral `J_ε(s)`. -/
noncomputable def vpJ (P : Params) (ε s : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, vpRatSum P ε s x * ((x ^ 2 / 2 - x ^ 3 / 3 : ℝ) : ℂ)

/-- The coefficient `c L_ε / 3` of the piece (i). -/
noncomputable def logW (P : Params) (ε : ℝ) : ℂ := vpCst P * bubLogSum P ε / 3

/-- The coefficient `-2 c J_ε(s)` of the dispersive pieces. -/
noncomputable def dispW (P : Params) (ε s : ℝ) : ℂ := -2 * vpCst P * vpJ P ε s

/-- The rest: the longitudinal dispersive part and the `ε S_ε` part. -/
noncomputable def restIns (P : Params) (ε : ℝ) (lor : Wick.PhotonSlot kD → Fin 4)
    (k : Fin 4 → ℝ) : ℂ :=
  dispW P ε (Minkowski.dot k k) * ctKD 1 lor k -
    (ε : ℂ) * vpExtraEps P ε (Minkowski.dot k k) *
      (Minkowski.metric (lor (pc kD 5 0)) (lor (pc kD 5 1)) : ℂ)

/-- **The split of the inserted vacuum polarization** (every `ε > 0`). -/
theorem neg_vpT_split (P : Params) {ε : ℝ} (hε : 0 < ε) (lor : Wick.PhotonSlot kD → Fin 4)
    (k : Fin 4 → ℝ) :
    -vpT (I * vpLoopEps P ε (Minkowski.dot k k)) ((ε : ℂ) * vpExtraEps P ε (Minkowski.dot k k)) k
        (lor (pc kD 5 0)) (lor (pc kD 5 1)) =
      logW P ε * ctF 1 lor k + (dispW P ε (Minkowski.dot k k) * ctGD 1 lor k +
        restIns P ε lor k) := by
  rw [vpLoopEps_eq_spectral P hε]
  simp only [vpT, ctF, ctGD, ctKD, restIns, dispW, logW, vpJ, vpCst, bubLogSum]
  push_cast
  ring

variable (P : Params) (Φ : Lepton.Flavors F) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}

/-- **The split of the outer integrand of `repB i`** (every `ε > 0`): the log constant times the
`photonCt` insertion at `δ₃ = 1`, the transverse dispersive insertion and the rest. -/
theorem outerBub_split (hε : 0 < P.ε) (i : Fin 12) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    outerBub P (outerBW P Φ i pOut pIn kIn αOut βIn μ) (kBW i pOut pIn kIn) ℓ =
      logW P P.ε * insD P Φ (ctF 1) (repD i 0) pOut pIn kIn αOut βIn μ ℓ +
        (dispW P P.ε (Minkowski.dot (kBW i pOut pIn kIn ℓ) (kBW i pOut pIn kIn ℓ)) *
            insD P Φ (ctGD 1) (repD i 0) pOut pIn kIn αOut βIn μ ℓ +
          insD P Φ (restIns P P.ε) (repD i 0) pOut pIn kIn αOut βIn μ ℓ) := by
  rw [outerBub_outerBW]
  simp only [neg_vpT_split P hε]
  rw [insD_add, insD_add, insD_smul,
    insD_mul_fun P Φ _ _ _ _ _ _ _ ℓ (fun k => dispW P P.ε (Minkowski.dot k k)) (ctGD 1)]
  rfl

/-! ### The transverse unit of `repB` from that of `repD` -/

theorem unitMIntegrand_last_extra {r : ℕ} (c : Class5) (P : Params) (s : Fin 8)
    (κ : Fin (r + 1) → ℝ) (m a A b B : ℝ) (cs : Fin (r + 1) → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ)
    (n : ℕ) (μ i j : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    unitMIntegrand c P s κ (unitMMasses m a A b B cs) ε p p' (n + 1) μ i j ℓ =
      unitMIntegrand c P s (Fin.init κ) (unitMMasses m a A b B (Fin.init cs)) ε p p' n μ i j ℓ *
        elemSq c s p p' ℓ * (((κ (Fin.last r) ^ 2 *
          Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ) + cs (Fin.last r) ^ 2 : ℝ) :
            ℂ) - (ε : ℂ) * I)⁻¹ := by
  have hprod : ∀ f : Fin (r + 1 + 8) → ℂ,
      ∏ k, f k = (∏ k : Fin (r + 8), f (Fin.castSucc k)) * f (Fin.last (r + 8)) :=
    fun f => Fin.prod_univ_castSucc f
  have hlast := lineDenom_unitM_mExtra c s κ p p' m a A b B cs ε (Fin.last r) ℓ
  rw [mExtra_last] at hlast
  simp only [unitMIntegrand, hprod, lineDenom_unitM_castSucc, hlast]
  ring

/-- **The transverse unit of `repB` at `x ∈ (0, 1)`** is the unit of `repD` (two unscaled extra
lines) with one more power `k²` and the spectral factor `(M² + x(1-x)k² - iε)⁻¹`. -/
theorem unitMIntegrand_repB_succ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (c : Class5) (P : Params)
    (s : Fin 8) (m mγ Λ M ε : ℝ) (p p' : Fin 4 → ℝ) (n : ℕ) (μ i j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    unitMIntegrand c P s (repBKappa x) (unitMMasses m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p'
        (n + 1) μ i j ℓ =
      unitMIntegrand c P s ![1, 1] (unitMMasses m mγ Λ mγ Λ ![mγ, Λ]) ε p p' n μ i j ℓ *
        elemSq c s p p' ℓ * (((vacuumPolarizationFeynmanMass M
          (Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ)) x : ℝ) : ℂ) -
            (ε : ℂ) * I)⁻¹ := by
  rw [← unitMIntegrand_perm c P s (finRotate 3) (repBKappa x) m mγ Λ mγ Λ (repBExtra M mγ Λ) ε
    p p' (n + 1) μ i j, unitMIntegrand_last_extra, repBKappa_comp_finRotate,
    repBExtra_comp_finRotate]
  have h1 : (repBKappa x ∘ finRotate 3) (Fin.last 2) = √(x * (1 - x)) := rfl
  have h2 : (repBExtra M mγ Λ ∘ finRotate 3) (Fin.last 2) = M := rfl
  rw [h1, h2, Real.sq_sqrt (mem_Ioo_mul_pos hx).le]
  unfold vacuumPolarizationFeynmanMass
  ring_nf

/-! ### The transverse dispersive piece as units -/

/-- The weight of flavour `f` on the Feynman parameter: `c_f (1 - 2x)(x²/2 - x³/3)`. -/
noncomputable def dispWt (P : Params) (f : Fin 3) (x : ℝ) : ℂ :=
  (P.loopCoeff f : ℂ) * (((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) : ℝ) : ℂ)

theorem continuous_dispWt (P : Params) (f : Fin 3) : Continuous (dispWt P f) := by
  unfold dispWt
  fun_prop

theorem integrableOn_dispWt (P : Params) (f : Fin 3) : IntegrableOn (dispWt P f) (Ioo 0 1) :=
  ((continuous_dispWt P f).integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem feynmanDen_ne_zero {ε : ℝ} (hε : ε ≠ 0) (M s x : ℝ) :
    ((vacuumPolarizationFeynmanMass M s x : ℝ) : ℂ) - (ε : ℂ) * I ≠ 0 := fun h =>
  hε (by simpa using congrArg Complex.im h)

/-- `J_ε(s) U` as a sum over flavours of integrals over the Feynman parameter. -/
theorem vpJ_mul (P : Params) {ε : ℝ} (hε : ε ≠ 0) (s : ℝ) (U : ℂ) :
    vpJ P ε s * U = ∑ f, ∫ x in Ioo (0 : ℝ) 1, dispWt P f x *
      (U * (s : ℂ) * (((vacuumPolarizationFeynmanMass (P.mass f) s x : ℝ) : ℂ) -
        (ε : ℂ) * I)⁻¹) := by
  have hint : ∀ f, Integrable (fun x => dispWt P f x * (U * (s : ℂ) *
      (((vacuumPolarizationFeynmanMass (P.mass f) s x : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹))
      (volume.restrict (Ioo (0 : ℝ) 1)) := fun f => by
    have hc : Continuous fun x => dispWt P f x * (U * (s : ℂ) *
        (((vacuumPolarizationFeynmanMass (P.mass f) s x : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹) := by
      refine (continuous_dispWt P f).mul (continuous_const.mul (Continuous.inv₀ ?_
        fun x => feynmanDen_ne_zero hε _ s x))
      unfold vacuumPolarizationFeynmanMass
      fun_prop
    exact (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  unfold vpJ
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_mul_const, ← integral_finsetSum _ fun f _ => hint f]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [vpRatSum, Finset.sum_mul, dispWt]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

/-! ### Finite sums of joint integrals -/

/-- Both stages and the value of a finite sum of integrands integrable in both stages. -/
theorem jointEnergyFirstIntegrable_finSum {ι : Type*} (s : Finset ι) {L : ℕ}
    (G : ι → (Fin L → Fin 4 → ℝ) → ℂ)
    (h : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L (G i)) :
    QED.TwoLoop.jointEnergyFirstIntegrable L (fun ℓ => ∑ i ∈ s, G i ℓ) ∧
      QED.TwoLoop.jointEnergyFirstIntegral L (fun ℓ => ∑ i ∈ s, G i ℓ) =
        ∑ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegral L (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨⟨fun _ => integrable_zero _ _ _, ?_⟩, ?_⟩
    · simp only [integral_zero]
      exact integrable_zero _ _ _
    · unfold QED.TwoLoop.jointEnergyFirstIntegral
      simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha]
    exact ⟨QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add ha' h1,
      by rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add ha' h1, h2]⟩

/-! ### The value of the transverse dispersive piece -/

section Disp

variable (Q R : Params) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (hm : Φ.mass Φ.openLine = R.m) (he : R.e = Q.e) (hγ : R.mγ = Q.mγ) (hΛ : R.Λ = Q.Λ)
  (i : Fin 12) (p p' : Fin 4 → ℝ) (μ α β : Fin 4)

/-- **The piece (ii)**: the transverse dispersive part of the outer integrand of `repB i`. -/
noncomputable def dispIns (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  dispW Q Q.ε (Minkowski.dot (kBW i (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ)
      (kBW i (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ)) *
    insD Q Φ (ctGD 1) (repD i 0) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
      (fun _ => β) (fun _ => μ) ℓ

/-- The transverse unit of `repB i` at flavour `f` and Feynman parameter `x`. -/
noncomputable def dispUnit (f : Fin 3) (x : ℝ) : (Fin 2 → Fin 4 → ℝ) → ℂ :=
  unitMIntegrand (repBClass i) R (repBSlot i) (repBKappa x)
    (unitMMasses R.m Q.mγ Q.Λ Q.mγ Q.Λ (repBExtra (Q.mass f) Q.mγ Q.Λ)) Q.ε p p' 2 μ α β

/-- The rest of the outer integrand of `repB i`. -/
noncomputable def restB (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  insD Q Φ (restIns Q Q.ε) (repD i 0) (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => α) (fun _ => β) (fun _ => μ) ℓ

include hm he hγ hΛ in
/-- **The piece (ii) as units**: `-2c · wD 1 · ∑_f ∫₀¹ w_f(x) I_x dx` at the changed loop
momenta of `repD i 0` (every `ε ≠ 0`). -/
theorem dispIns_eq_unit (hε : Q.ε ≠ 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    dispIns Q Φ i p p' μ α β ℓ = -2 * vpCst Q * wD Q 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1,
      dispWt Q f x * dispUnit Q R i p p' μ α β f x (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) := by
  unfold dispIns
  rw [← dGIntegrand_eq_insD, dGIntegrand_repD_eq_unit Q R Φ hm he hγ hΛ 1 i 0 p p' μ α β ℓ]
  have hK := photonMomentum₂_repD_sq i 0 p p' ℓ
  simp only [kBW]
  rw [hK]
  set ℓ' := chgD (chgMD i) (chgAD i) p (p' - p) ℓ
  unfold dispW
  rw [show ∀ a b c d : ℂ, -2 * a * b * (c * d) = -2 * a * c * (b * d) from
    fun _ _ _ _ => by ring, vpJ_mul Q hε]
  congr 1
  refine Finset.sum_congr rfl fun f _ => setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h : dispUnit Q R i p p' μ α β f x ℓ' = _ := unitMIntegrand_repB_succ hx (repBClass i) R
    (repBSlot i) R.m Q.mγ Q.Λ (Q.mass f) Q.ε p p' 1 μ α β ℓ'
  rw [h]
  rfl

include hm he hγ hΛ in
/-- **The value of the piece (ii)** (every `ε > 0`, positive masses): both stages integrable, and
the value is `-2c · wD 1 · ∑_f ∫₀¹ w_f(x) I_ε(x) dx`, `I_ε(x)` the value of the transverse unit of
`repB` (the form of `QED.ChainProof.SetCUnitM.tendsto_integral_unitMValue_repB`). -/
theorem jointEnergyFirstIntegral_dispIns (hε : 0 < Q.ε) (hM : ∀ f, 0 < Q.mass f) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (dispIns Q Φ i p p' μ α β) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (dispIns Q Φ i p p' μ α β) =
        -2 * vpCst Q * wD Q 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1, dispWt Q f x *
          unitMValue (repBClass i) R (repBSlot i) (repBKappa x)
            (unitMMasses R.m Q.mγ Q.Λ Q.mγ Q.Λ (repBExtra (Q.mass f) Q.mγ Q.Λ)) Q.ε p p' 2
            μ α β := by
  have hU := fun f => jointEnergyFirstIntegral_setIntegral_unitM_repB (repBClass_mem i) R p p'
    (four_le_repBSlot i) μ α β (hM f) Q.mγ Q.Λ hε (integrableOn_dispWt Q f)
  obtain ⟨hS1, hS2⟩ := jointEnergyFirstIntegrable_finSum Finset.univ
    (fun f ℓ' => ∫ x in Ioo (0 : ℝ) 1, dispWt Q f x * dispUnit Q R i p p' μ α β f x ℓ')
    fun f _ => (hU f).1
  have hG := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul
    (-2 * vpCst Q * wD Q 1) hS1
  have hpt := dispIns_eq_unit Q R Φ hm he hγ hΛ i p p' μ α β hε.ne'
  refine ⟨QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_of_comp (chgMD i)
    (isUnit_det_chgMD i) _ hG hpt, ?_⟩
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_eq_of_comp (chgMD i) (isUnit_det_chgMD i)
    (G := fun ℓ' => -2 * vpCst Q * wD Q 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1,
      dispWt Q f x * dispUnit Q R i p p' μ α β f x ℓ') _ hpt,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul, hS2]
  congr 1
  exact Finset.sum_congr rfl fun f _ => (hU f).2

end Disp

/-! ### The value of the outer integrand at fixed `ε` -/

/-- Both stages of the transverse and the longitudinal part of a `kD` contraction with the data
of `QED.ChainProof.SetCLink.classIntA_of_data` are integrable, at any `δ₃` (every `ε > 0`). -/
theorem integrable_dG_dK_kD (P : Params) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (hε : 0 < P.ε) (δ₃ : ℝ) (C : Contraction 1 1 kD) (hG : GData C)
    (hK : WardData C ∨ ExtData C) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (dGIntegrand P Φ δ₃ C pOut pIn kIn αOut βIn μ) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (dKIntegrand P Φ δ₃ C pOut pIn kIn αOut βIn μ) := by
  obtain ⟨g, hρ, h₀, h₁⟩ := hG
  have hA := jointEnergyFirstIntegrable_ctG P Φ hε δ₃ C pOut pIn kIn hmom αOut βIn μ g hρ h₀ h₁
  have hB : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => ∑ α, ∑ β, ∑ lor,
      extI C αOut βIn μ α β lor *
        (ctKD δ₃ lor (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ) (pc kD 5 0)) *
          (gV P.e α β lor *
            lineProd P.ε (dNum P Φ α β lor) (dMs P Φ) (lineMomentum₂ C pOut pIn kIn ℓ))) := by
    rcases hK with ⟨fa, fb, gW, gK, sW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ |
      ⟨f0, f3, gW, gK, sW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · exact jointEnergyFirstIntegrable_ctK_ward P Φ hε _ C pOut pIn kIn hmom αOut βIn μ fa fb
        gW gK sW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    · exact jointEnergyFirstIntegrable_ctK_ext P Φ hε _ C pOut pIn kIn hmom αOut βIn μ f0 f3
        gW gK sW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul _ hA,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul _ hB⟩

section Value

variable (Q R : Params) [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (hm : Φ.mass Φ.openLine = R.m) (he : R.e = Q.e) (hγ : R.mγ = Q.mγ) (hΛ : R.Λ = Q.Λ)
  (i : Fin 12) (p p' : Fin 4 → ℝ) (μ α β : Fin 4)

include hm he hγ hΛ in
/-- **The value of the outer integrand of `repB i` at fixed `ε > 0`**, when it is integrable in
both stages: the log constant times the transverse plus longitudinal values of `repD i 0` at
`δ₃ = 1`, plus the value of the piece (ii) as units, plus the value of the rest, which is
integrable in both stages. -/
theorem jointEnergyFirstIntegral_outerBub_split (hε : 0 < Q.ε) (hM : ∀ f, 0 < Q.mass f)
    (hO : QED.TwoLoop.jointEnergyFirstIntegrable 2 (outerBub Q
      (outerBW Q Φ i (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
        (fun _ => μ)) (kBW i (fun _ => p') (fun _ => p) (fun _ => p' - p)))) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (restB Q Φ i p p' μ α β) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (outerBub Q
        (outerBW Q Φ i (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
          (fun _ => μ)) (kBW i (fun _ => p') (fun _ => p) (fun _ => p' - p))) =
        logW Q Q.ε * (QED.TwoLoop.jointEnergyFirstIntegral 2 (dGIntegrand Q Φ 1 (repD i 0)
            (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
            (fun _ => μ)) +
          QED.TwoLoop.jointEnergyFirstIntegral 2 (dKIntegrand Q Φ 1 (repD i 0) (fun _ => p')
            (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ))) +
        -2 * vpCst Q * wD Q 1 * (∑ f, ∫ x in Ioo (0 : ℝ) 1, dispWt Q f x *
          unitMValue (repBClass i) R (repBSlot i) (repBKappa x)
            (unitMMasses R.m Q.mγ Q.Λ Q.mγ Q.Λ (repBExtra (Q.mass f) Q.mγ Q.Λ)) Q.ε p p' 2
            μ α β) +
        QED.TwoLoop.jointEnergyFirstIntegral 2 (restB Q Φ i p p' μ α β) := by
  set dG := dGIntegrand Q Φ 1 (repD i 0) (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => α) (fun _ => β) (fun _ => μ)
  set dK := dKIntegrand Q Φ 1 (repD i 0) (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => α) (fun _ => β) (fun _ => μ)
  have hsplit : outerBub Q (outerBW Q Φ i (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ)) (kBW i (fun _ => p') (fun _ => p)
        (fun _ => p' - p)) = fun ℓ => logW Q Q.ε * (dG ℓ + dK ℓ) +
          (dispIns Q Φ i p p' μ α β ℓ + restB Q Φ i p p' μ α β ℓ) := funext fun ℓ => by
    rw [outerBub_split Q Φ hε i _ _ _ ℓ, insD_ctF]
    rfl
  obtain ⟨hGi, hKi⟩ := integrable_dG_dK_kD Q Φ hε 1 (repD i 0) (data_repD i 0).1
    (data_repD i 0).2 (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p)
    (by simp) (fun _ => α) (fun _ => β) (fun _ => μ)
  have hA := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul (logW Q Q.ε)
    (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add hGi hKi)
  obtain ⟨hD1, hD2⟩ := jointEnergyFirstIntegral_dispIns Q R Φ hm he hγ hΛ i p p' μ α β hε hM
  have hR : QED.TwoLoop.jointEnergyFirstIntegrable 2 (restB Q Φ i p p' μ α β) := by
    have e : restB Q Φ i p p' μ α β = fun ℓ =>
        (outerBub Q (outerBW Q Φ i (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
          (fun _ => β) (fun _ => μ)) (kBW i (fun _ => p') (fun _ => p) (fun _ => p' - p)) ℓ +
            -1 * (logW Q Q.ε * (dG ℓ + dK ℓ))) + -1 * dispIns Q Φ i p p' μ α β ℓ :=
        funext fun ℓ => by
      rw [congrFun hsplit ℓ]
      ring
    rw [e]
    exact QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add
      (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add hO
        (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul (-1) hA))
      (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul (-1) hD1)
  refine ⟨hR, ?_⟩
  rw [hsplit, QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add hA
    (QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add hD1 hR),
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add hD1 hR,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add hGi hKi, hD2]
  ring

end Value

end QED.ChainProof.SetCMainB

end
