/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBSplitLim

/-!
# Set (c), the bubble classes: the `ε S_ε` part of the rest

Helper level for the rest link `QED.ChainProof.SetCMainB.MainBRestLink` of the bubble classes
`repB i`. The rest of the split outer integrand
(`QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_outerBub_split`) is
`restIns = (-2c J_ε(k²)) · ctKD 1 - ε S_ε(k²) g`; here it is split into the longitudinal
dispersive part `kkB` and the `ε S_ε` part `sB` (`restB_eq`), and the latter is shown to be
integrable in both stages with an explicit value, and to tend to zero as `ε → 0⁺`.

With `S_ε(s) = (e²/4π²)(L_ε - ∫₀¹ x ∑_f c_f (1 - 2x) s / (M_f² + x(1-x)s - iε) dx)`
(`QED.TwoLoop.VPHalfAt.vpExtraEps_eq_spectral`), the metric insertion is `2i · wD 1` times the
transverse unit of `repD` with no power of `k²`, and its spectral part is the transverse unit of
`repB` with one power `k²`.

* `gIns`, **`insD_gIns_repD_eq_unit`**: the metric insertion as a unit (`n = 0`);
* `absL1_unitM_repB_one_le`, `integrable_unitM_repB_energy_one`,
  `integrable_energyIntegral_unitM_repB_one`,
  **`jointEnergyFirstIntegral_setIntegral_unitM_repB_one`**: the `x`-Fubini for the
  transverse unit of `repB` with one power `k²` (the recursion
  `k² D_Λ⁻¹ = 1 - (Λ² - iε) D_Λ⁻¹` onto two dispersion-line units at `n = 0`);
* **`norm_unitMValue_repB_one_le`**: its value is bounded uniformly in `x ∈ (0, 1)` and
  `ε ∈ (0, 1]`;
* `sWt`, `vpX_mul`, `sIns`, `kkIns`, `restIns_eq`, `sB`, `kkB`, **`restB_eq`**;
* **`sB_eq_unit`**, **`jointEnergyFirstIntegral_sB`**: the `ε S_ε` part as units, its value;
* **`kkB_eq_unit`**: the longitudinal dispersive part pointwise, as `-2c · wKD 1` times
  `∑_f ∫₀¹ w_f(x) K k² (M_f² + x(1-x)k² - iε)⁻¹ dx` with `K` the longitudinal integrand of `repD`;
* **`tendsto_sB`**: the `ε S_ε` part tends to zero.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open QED.WickModel (Params Contraction lineMomentum₂ photonMomentum₂)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.GradedProof.X0
open QED.ChainProof.SetCMain
open QED.ChainProof.SetCUnitM
open QED.ChainProof.Enum (pc)
open QED.TwoLoop.Bridge (electronNumerator extMomenta)
open QED.TwoLoop.LimitCovariance (pvEta)
open QED.Integration.TwoLoop (lineMomentum castLoopMatrix class5LoopMatrix)
open QED.ChainProof.SetCUnit (unitNum MassesGe)
open QED.TwoLoop.VPHalfAt (vpExtraEps vpRatSum vpExtraEps_eq_spectral)
open QED.WickModel (vacuumPolarizationFeynmanMass)

/-! ### The metric insertion -/

/-- The metric insertion `g^{ab}`. -/
noncomputable def gIns (lor : Wick.PhotonSlot kD → Fin 4) (_k : Fin 4 → ℝ) : ℂ :=
  (Minkowski.metric (lor (pc kD 5 0)) (lor (pc kD 5 1)) : ℂ)

/-- A unit spatial vector, `e₁ · e₁ = 1`. -/
def eOne : Fin 4 → ℝ := Pi.single 1 1

theorem dot_eOne : Minkowski.dot eOne eOne = 1 := by
  simp [Minkowski.dot, eOne, Minkowski.metric, Pi.single_apply]

theorem gIns_eq (lor : Wick.PhotonSlot kD → Fin 4) (k : Fin 4 → ℝ) :
    gIns lor k = 2 * I * ctGD 1 lor eOne := by
  simp only [gIns, ctGD, dot_eOne]
  push_cast
  ring_nf
  simp

/-- **The metric insertion into `repD i s` is a unit** with no power of `k²`: `2i · wD 1` times
the transverse unit with two unscaled extra lines at `n = 0`. -/
theorem insD_gIns_repD_eq_unit (Q P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (hm : Φ.mass Φ.openLine = P.m) (he : P.e = Q.e) (hγ : P.mγ = Q.mγ)
    (hΛ : P.Λ = Q.Λ) (i : Fin 12) (s : Fin 2) (p p' : Fin 4 → ℝ) (μ α β : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    insD Q Φ gIns (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
        (fun _ => β) (fun _ => μ) ℓ =
      2 * I * wD Q 1 * unitMIntegrand (repBClass i) P (repBSlot i) ![1, 1]
        (unitMMasses P.m Q.mγ Q.Λ Q.mγ Q.Λ ![Q.mγ, Q.Λ]) Q.ε p p' 0 μ α β
        (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) := by
  have hX : gIns = fun lor _ => 2 * I * ctGD 1 lor eOne := funext fun lor => funext fun k =>
    gIns_eq lor k
  rw [hX, insD_smul, mul_assoc (2 * I)]
  congr 1
  unfold insD
  rw [dG_repD_chain, prod_dProd_repD]
  unfold unitMIntegrand unitNum
  rw [classNumeratorE_chainD (repBClass_mem i), prod_lineDenom_unitM_two]
  obtain ⟨h0, hp⟩ := chainPermD_repD i s
  rw [chainNum_apply_pairsD _ _ _ _ _ _ h0 hp]
  have hE : (fun j => electronNumerator P.m (lineMomentum (castLoopMatrix
      (class5LoopMatrix (repBClass i))) (extMomenta (repBClass i) p p') (Fin.castLE (by omega) j)
        (chgD (chgMD i) (chgAD i) p (p' - p) ℓ))) =
      fun j => electronNumerator (Φ.mass Φ.openLine) (lineMomentum₂ (repD i s) (fun _ => p')
        (fun _ => p) (fun _ => p' - p) ℓ (.inl (lineRD i s j))) := by
    funext j
    rw [hm, lineMomentum₂_repD_fermion]
  have hη : pvEta P = pvEta Q := by
    funext x y
    simp only [pvEta, hγ, hΛ]
  simp only [hE, hη, he, hm, dot_eOne, pow_zero, mul_one, Complex.ofReal_one]
  rcases slotD_cases i with ⟨h4, h5⟩ | ⟨h5, h4⟩ <;> rw [h4, h5] <;> unfold wD <;>
    simp only [Complex.ofReal_one] <;>
    ring

end QED.ChainProof.SetCMainB

/-! ### The transverse unit of `repB` with one power of `k²` -/

namespace QED.ChainProof.SetCUnitM

open QED.TwoLoop.ClassIntegrable (openClasses)
open QED.TwoLoop.Enumeration (Class5)
open QED.TwoLoop.VPHalfAtAssembly (mem_Ioo_mul_pos)

theorem repBKappa_eq_cons {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < √(x * (1 - x)) ∧ √(x * (1 - x)) ^ 2 ≤ 1 / 4 ∧
      repBKappa x = Fin.cons (√(x * (1 - x))) fun _ => 1 := by
  have hw := mem_Ioo_mul_pos hx
  refine ⟨Real.sqrt_pos.2 hw, ?_, by funext j; fin_cases j <;> rfl⟩
  rw [Real.sq_sqrt hw.le]
  nlinarith [sq_nonneg (x - 1 / 2)]

section RepBOne

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
  (p p' : Fin 4 → ℝ)
include hc hs

/-- **The transverse unit of `repB` with one power `k²` in the spatial `L¹` norm**, uniformly
in `x ∈ (0, 1)`, at fixed `ε > 0` and fixed masses (`M > 0`). -/
theorem absL1_unitM_repB_one_le (μ i j : Fin 4) {M : ℝ} (hM : 0 < M) (mγ Λ : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1,
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j) ∧
        absL1 (unitMIntegrand c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j) ≤ C := by
  obtain ⟨C₁, hC₁⟩ := absL1_unitMValue_disp_le (r := 1) hc P hs p p' μ i j mγ Λ hM ![mγ] hε
  obtain ⟨C₂, hC₂⟩ := absL1_unitMValue_disp_le (r := 2) hc P hs p p' μ i j mγ Λ hM ![mγ, Λ] hε
  set B := Λ ^ 2 + ε
  refine ⟨C₁ + B * C₂, fun x hx => ?_⟩
  obtain ⟨hκ0, hκ2, hK⟩ := repBKappa_eq_cons hx
  set κ := √(x * (1 - x))
  set K₃ : Fin 3 → ℝ := Fin.cons κ fun _ => 1
  set K₂ : Fin 2 → ℝ := Fin.cons κ fun _ => 1
  have hi₃ : Fin.init K₃ = K₂ := by funext j; fin_cases j <;> rfl
  have hE₃ : repBExtra M mγ Λ = Fin.cons M ![mγ, Λ] := rfl
  have hj₃ : Fin.init (Fin.cons M ![mγ, Λ] : Fin 3 → ℝ) = Fin.cons M ![mγ] := by
    funext j; fin_cases j <;> rfl
  have e₁b := unitMIntegrand_succ c P s (κ := K₃) rfl P.m mγ Λ mγ Λ (Fin.cons M ![mγ, Λ])
    hε.ne' p p' 0 μ i j
  rw [hi₃, hj₃] at e₁b
  obtain ⟨j₁, b₁⟩ := hC₁ κ hκ0 hκ2
  obtain ⟨j₂, b₂⟩ := hC₂ κ hκ0 hκ2
  set b' := ((((Fin.cons M ![mγ, Λ] : Fin 3 → ℝ) (Fin.last 2)) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I
  have hb : ‖b'‖ ≤ B := (norm_sq_sub_mul_I_le hε.le).trans (by simp [B])
  rw [hK, hE₃, e₁b]
  refine ⟨(jointEnergyFirstIntegrable_sub_mul j₁ j₂ b').1,
    (absL1_sub_mul_le j₁ j₂ b').trans (add_le_add b₁ ?_)⟩
  exact mul_le_mul hb b₂ (absL1_nonneg _) ((norm_nonneg _).trans hb)

omit hs in
/-- Condition `h₁` for `w(x) I_x` with one power `k²`. -/
theorem integrable_unitM_repB_energy_one (μ i j : Fin 4) (M mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) (v : Fin 2 → Fin 3 → ℝ) :
    Integrable (fun q : ℝ × (Fin 2 → ℝ) => w q.1 * unitMIntegrand c P s (repBKappa q.1)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j
          fun s => (Fin.cons (q.2 s) (v s) : Fin 4 → ℝ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  have hg := ((jointEnergyFirstIntegrable_unitM_pow hc P s 1 (κ := ![1, 1]) (by norm_num)
    QED.ChainProof.SetCMain.trailOne_one_two (fun j => by fin_cases j <;> simp) P.m mγ Λ mγ Λ
    ![mγ, Λ] hε p p' μ i j).1 v).norm
  exact integrable_mul_of_norm_le (G := fun x t => unitMIntegrand c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j
        fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))
    (continuous_energy_slice (G := fun x ℓ => unitMIntegrand c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j ℓ)
      (continuous_unitMIntegrand_repB hc P s _ hε.ne' p p' 1 μ i j) v) hw hg
    (fun x t => norm_unitMIntegrand_repB_le c P s x M mγ Λ hε p p' 1 μ i j _)

/-- Condition `h₂` for `w(x) I_x` with one power `k²`. -/
theorem integrable_energyIntegral_unitM_repB_one (μ i j : Fin 4) {M : ℝ} (hM : 0 < M)
    (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) :
    Integrable (fun q : ℝ × (Fin 2 → Fin 3 → ℝ) => ∫ t : Fin 2 → ℝ,
        w q.1 * unitMIntegrand c P s (repBKappa q.1)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j
          fun s => (Fin.cons (t s) (q.2 s) : Fin 4 → ℝ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  obtain ⟨C, hC⟩ := absL1_unitM_repB_one_le hc P hs p p' μ i j hM mγ Λ hε
  exact integrable_energyIntegral_of_absL1_le
    (continuous_unitMIntegrand_repB hc P s _ hε.ne' p p' 1 μ i j) measurableSet_Ioo hw hC

/-- **The Feynman parameter of `repB` through the joint energy-first integral, one power
`k²`**: for a weight `w` integrable on `(0, 1)`, fixed `ε > 0` and `M > 0`, the integrand
`∫₀¹ w(x) I_x dx` is integrable in both stages and its value is `∫₀¹ w(x) unitMValue(x) dx`. -/
theorem jointEnergyFirstIntegral_setIntegral_unitM_repB_one (μ i j : Fin 4) {M : ℝ} (hM : 0 < M)
    (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ => ∫ x in Ioo (0 : ℝ) 1,
        w x * unitMIntegrand c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j ℓ) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => ∫ x in Ioo (0 : ℝ) 1,
        w x * unitMIntegrand c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j ℓ) =
        ∫ x in Ioo (0 : ℝ) 1, w x * unitMValue c P s (repBKappa x)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j := by
  obtain ⟨h1, h2⟩ := QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_setIntegral
    (S := Ioo (0 : ℝ) 1) (fun x ℓ => w x * unitMIntegrand c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1 μ i j ℓ)
    (integrable_unitM_repB_energy_one hc P p p' μ i j M mγ Λ hε hw)
    (integrable_energyIntegral_unitM_repB_one hc P hs p p' μ i j hM mγ Λ hε hw)
  refine ⟨h1, h2.trans (integral_congr_ae (ae_of_all _ fun x => ?_))⟩
  exact jointEnergyFirstIntegral_two_const_mul _ _

/-- **The transverse unit of `repB` with one power `k²` at fixed `ε`, bounded uniformly in
`x ∈ (0, 1)` and `ε ∈ (0, 1]`**, at fixed masses `≥ μ₀`. -/
theorem norm_unitMValue_repB_one_le (hm : 0 < P.m) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) {M mγ Λ : ℝ} (hM : μ₀ ≤ M)
    (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖unitMValue c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 1
          μ i j‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := norm_unitMValue_disp_le (r := 1) hc P hm hs hμ₀ hp hp' hq μ i j
  obtain ⟨C₂, hC₂⟩ := norm_unitMValue_disp_le (r := 2) hc P hm hs hμ₀ hp hp' hq μ i j
  set S := 1 + mγ ^ 2 + Λ ^ 2
  refine ⟨‖C₁ * S / M ^ 2‖ + (Λ ^ 2 + 1) * ‖C₂ * S / M ^ 2‖, fun x hx ε hε hε1 => ?_⟩
  obtain ⟨hκ0, hκ2, hK⟩ := repBKappa_eq_cons hx
  set κ := √(x * (1 - x))
  set K₃ : Fin 3 → ℝ := Fin.cons κ fun _ => 1
  set K₂ : Fin 2 → ℝ := Fin.cons κ fun _ => 1
  have hi₃ : Fin.init K₃ = K₂ := by funext j; fin_cases j <;> rfl
  have hE₃ : repBExtra M mγ Λ = Fin.cons M ![mγ, Λ] := rfl
  have hj₃ : Fin.init (Fin.cons M ![mγ, Λ] : Fin 3 → ℝ) = Fin.cons M ![mγ] := by
    funext j; fin_cases j <;> rfl
  have hne : ∀ {r : ℕ} (j : Fin (r + 1)), (Fin.cons κ (fun _ => 1) : Fin (r + 1) → ℝ) j ≠ 0 :=
    fun j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hκ0.ne'
      · simp
  have hI₀ : ∀ {r : ℕ} (κv cs : Fin r → ℝ), (∀ j, κv j ≠ 0) →
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (unitMIntegrand c P s κv
        (unitMMasses P.m mγ Λ mγ Λ cs) ε p p' 0 μ i j) := fun κv cs h =>
    jointEnergyFirstIntegrable_unitM hc P s h _ p p' hε μ i j
  have e₁b := unitMValue_succ_eps (c := c) P (s := s) (p := p) (p' := p') (κ := K₃) rfl P.m mγ Λ
    mγ Λ (Fin.cons M ![mγ, Λ]) hε 0 μ i j (by rw [hi₃, hj₃]; exact hI₀ _ _ hne) (hI₀ _ _ hne)
  rw [hi₃, hj₃] at e₁b
  rw [hK, hE₃, e₁b]
  have b₁ := hC₁ κ M mγ Λ ![mγ] ε hκ0 hκ2 hM hmγ hΛ (fun j => by fin_cases j; exact hmγ) hε
  have b₂ := hC₂ κ M mγ Λ ![mγ, Λ] ε hκ0 hκ2 hM hmγ hΛ (fun j => by
    fin_cases j
    · exact hmγ
    · exact hΛ) hε
  have hb : ‖((((Fin.cons M ![mγ, Λ] : Fin 3 → ℝ) (Fin.last 2)) ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I‖ ≤
      Λ ^ 2 + 1 := (norm_sq_sub_mul_I_le hε.le).trans (by simp; linarith)
  refine (norm_sub_le _ _).trans (add_le_add (b₁.trans (Real.le_norm_self _)) ?_)
  rw [norm_mul]
  exact mul_le_mul hb (b₂.trans (Real.le_norm_self _)) (norm_nonneg _) (by positivity)

end RepBOne

end QED.ChainProof.SetCUnitM

/-! ### The `ε S_ε` part of the rest -/

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.GradedProof.X0
open QED.ChainProof.SetCMain
open QED.ChainProof.SetCUnitM
open QED.TwoLoop.VPHalfAt (vpExtraEps vpRatSum vpExtraEps_eq_spectral)
open QED.WickModel (vacuumPolarizationFeynmanMass)
open QED.ChainProof.SetCUnit (MassesGe)

/-- The weight of flavour `f` in `S_ε`: `c_f (1 - 2x) x`. -/
noncomputable def sWt (P : Params) (f : Fin 3) (x : ℝ) : ℂ :=
  (P.loopCoeff f : ℂ) * (((1 - 2 * x) * x : ℝ) : ℂ)

theorem continuous_sWt (P : Params) (f : Fin 3) : Continuous (sWt P f) := by
  unfold sWt
  fun_prop

theorem integrableOn_sWt (P : Params) (f : Fin 3) : IntegrableOn (sWt P f) (Ioo 0 1) :=
  ((continuous_sWt P f).integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- The `x`-integral of `S_ε(s) U` as a sum over flavours of integrals over the Feynman
parameter. -/
theorem vpX_mul (P : Params) {ε : ℝ} (hε : ε ≠ 0) (s : ℝ) (U : ℂ) :
    (∫ x in (0 : ℝ)..1, vpRatSum P ε s x * (x : ℂ)) * U = ∑ f, ∫ x in Ioo (0 : ℝ) 1,
      sWt P f x * (U * (s : ℂ) * (((vacuumPolarizationFeynmanMass (P.mass f) s x : ℝ) : ℂ) -
        (ε : ℂ) * I)⁻¹) := by
  have hint : ∀ f, Integrable (fun x => sWt P f x * (U * (s : ℂ) *
      (((vacuumPolarizationFeynmanMass (P.mass f) s x : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹))
      (volume.restrict (Ioo (0 : ℝ) 1)) := fun f => by
    have hc : Continuous fun x => sWt P f x * (U * (s : ℂ) *
        (((vacuumPolarizationFeynmanMass (P.mass f) s x : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹) := by
      refine (continuous_sWt P f).mul (continuous_const.mul (Continuous.inv₀ ?_
        fun x => feynmanDen_ne_zero hε _ s x))
      unfold vacuumPolarizationFeynmanMass
      fun_prop
    exact (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_mul_const, ← integral_finsetSum _ fun f _ => hint f]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [vpRatSum, Finset.sum_mul, sWt]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  ring

/-- The `ε S_ε g` insertion. -/
noncomputable def sIns (P : Params) (ε : ℝ) (lor : Wick.PhotonSlot kD → Fin 4)
    (k : Fin 4 → ℝ) : ℂ :=
  (ε : ℂ) * vpExtraEps P ε (Minkowski.dot k k) * gIns lor k

/-- The longitudinal dispersive insertion `(-2c J_ε(k²)) · ctKD 1`. -/
noncomputable def kkIns (P : Params) (ε : ℝ) (lor : Wick.PhotonSlot kD → Fin 4)
    (k : Fin 4 → ℝ) : ℂ :=
  dispW P ε (Minkowski.dot k k) * ctKD 1 lor k

theorem restIns_eq (P : Params) (ε : ℝ) :
    restIns P ε = fun lor k => kkIns P ε lor k + -1 * sIns P ε lor k := by
  funext lor k
  simp only [restIns, kkIns, sIns, gIns]
  ring

section Rest

variable (Q R : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (hm : Φ.mass Φ.openLine = R.m) (he : R.e = Q.e) (hγ : R.mγ = Q.mγ) (hΛ : R.Λ = Q.Λ)
  (i : Fin 12) (p p' : Fin 4 → ℝ) (μ α β : Fin 4)

/-- The `ε S_ε` part of the rest of `repB i`. -/
noncomputable def sB (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  insD Q Φ (sIns Q Q.ε) (repD i 0) (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => α) (fun _ => β) (fun _ => μ) ℓ

/-- The longitudinal dispersive part of the rest of `repB i`. -/
noncomputable def kkB (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  insD Q Φ (kkIns Q Q.ε) (repD i 0) (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => α) (fun _ => β) (fun _ => μ) ℓ

omit [Fintype F] [DecidableEq F] in
theorem restB_eq (ℓ : Fin 2 → Fin 4 → ℝ) :
    restB Q Φ i p p' μ α β ℓ = kkB Q Φ i p p' μ α β ℓ + -1 * sB Q Φ i p p' μ α β ℓ := by
  unfold restB kkB sB
  rw [restIns_eq, insD_add, insD_smul]

/-- The metric unit of `repD i 0` (`n = 0`). -/
noncomputable def gUnit : (Fin 2 → Fin 4 → ℝ) → ℂ :=
  unitMIntegrand (repBClass i) R (repBSlot i) ![1, 1]
    (unitMMasses R.m Q.mγ Q.Λ Q.mγ Q.Λ ![Q.mγ, Q.Λ]) Q.ε p p' 0 μ α β

/-- The transverse unit of `repB i` with one power `k²`, at flavour `f` and parameter `x`. -/
noncomputable def sUnit (f : Fin 3) (x : ℝ) : (Fin 2 → Fin 4 → ℝ) → ℂ :=
  unitMIntegrand (repBClass i) R (repBSlot i) (repBKappa x)
    (unitMMasses R.m Q.mγ Q.Λ Q.mγ Q.Λ (repBExtra (Q.mass f) Q.mγ Q.Λ)) Q.ε p p' 1 μ α β

/-- The constant `ε (e²/4π²) · 2i wD 1` of the `ε S_ε` part. -/
noncomputable def sCst : ℂ :=
  (Q.ε : ℂ) * ((Q.e ^ 2 / (4 * Real.pi ^ 2) : ℝ) : ℂ) * (2 * I * wD Q 1)

include hm he hγ hΛ in
/-- **The `ε S_ε` part as units** (every `ε > 0`). -/
theorem sB_eq_unit (hε : 0 < Q.ε) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sB Q Φ i p p' μ α β ℓ = sCst Q * (bubLogSum Q Q.ε *
      gUnit Q R i p p' μ α β (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) -
      ∑ f, ∫ x in Ioo (0 : ℝ) 1, sWt Q f x *
        sUnit Q R i p p' μ α β f x (chgD (chgMD i) (chgAD i) p (p' - p) ℓ)) := by
  unfold sB
  rw [show sIns Q Q.ε = fun lor k => ((Q.ε : ℂ) * vpExtraEps Q Q.ε (Minkowski.dot k k)) *
    gIns lor k from rfl, insD_mul_fun Q Φ _ _ _ _ _ _ _ ℓ
      (fun k => (Q.ε : ℂ) * vpExtraEps Q Q.ε (Minkowski.dot k k)) gIns,
    insD_gIns_repD_eq_unit Q R Φ hm he hγ hΛ i 0 p p' μ α β ℓ]
  rw [photonMomentum₂_repD_sq i 0 p p' ℓ, vpExtraEps_eq_spectral Q hε]
  set ℓ' := chgD (chgMD i) (chgAD i) p (p' - p) ℓ
  unfold sCst gUnit bubLogSum
  rw [show ∀ a b c d K U : ℂ, a * (b * (c - d)) * (K * U) = a * b * K * (c * U - d * U) from
    fun _ _ _ _ _ _ => by ring, vpX_mul Q hε.ne']
  congr 2
  refine Finset.sum_congr rfl fun f _ => setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h : sUnit Q R i p p' μ α β f x ℓ' = _ := unitMIntegrand_repB_succ hx (repBClass i) R
    (repBSlot i) R.m Q.mγ Q.Λ (Q.mass f) Q.ε p p' 0 μ α β ℓ'
  rw [h]
  rfl

include hm he hγ hΛ in
/-- **The longitudinal dispersive part pointwise** (every `ε ≠ 0`): `-2c · wKD 1` times
`∑_f ∫₀¹ w_f(x) K(ℓ') k² (M_f² + x(1-x)k² - iε)⁻¹ dx` at the changed loop momenta `ℓ'` of
`repD i 0`, `K` the longitudinal integrand `dKUnitIntegrandD` of `repD i 0` and `k` the element
momentum. -/
theorem kkB_eq_unit (hε : Q.ε ≠ 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkB Q Φ i p p' μ α β ℓ = -2 * vpCst Q * wKD Q 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1,
      dispWt Q f x * (dKUnitIntegrandD i 0 R (unitMMasses R.m Q.mγ Q.Λ Q.mγ Q.Λ ![Q.mγ, Q.Λ])
        Q.ε p p' μ α β (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) *
        elemSq (repBClass i) (repBSlot i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) *
        (((vacuumPolarizationFeynmanMass (Q.mass f) (Minkowski.dot
          (elemMom (repBClass i) (repBSlot i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ))
          (elemMom (repBClass i) (repBSlot i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ)))
          x : ℝ) : ℂ) - (Q.ε : ℂ) * I)⁻¹) := by
  unfold kkB
  rw [show kkIns Q Q.ε = fun lor k => dispW Q Q.ε (Minkowski.dot k k) * ctKD 1 lor k from rfl,
    insD_mul_fun Q Φ _ _ _ _ _ _ _ ℓ (fun k => dispW Q Q.ε (Minkowski.dot k k)) (ctKD 1)]
  rw [show insD Q Φ (ctKD 1) (repD i 0) (fun _ => p') (fun _ => p) (fun _ => p' - p)
      (fun _ => α) (fun _ => β) (fun _ => μ) ℓ = dKIntegrand Q Φ 1 (repD i 0) (fun _ => p')
      (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ from rfl,
    dKIntegrand_repD_eq_unit Q R Φ hm he hγ hΛ 1 i 0 p p' μ α β ℓ,
    photonMomentum₂_repD_sq i 0 p p' ℓ]
  unfold dispW
  rw [show ∀ a b c d : ℂ, -2 * a * b * (c * d) = -2 * a * c * (b * d) from
    fun _ _ _ _ => by ring, vpJ_mul Q hε]
  rfl

include hm he hγ hΛ in
/-- **The value of the `ε S_ε` part** (every `ε > 0`, positive masses): both stages integrable,
and the value is `sCst · (L_ε · V_g - ∑_f ∫₀¹ w_f(x) I_ε(x) dx)`. -/
theorem jointEnergyFirstIntegral_sB (hε : 0 < Q.ε) (hM : ∀ f, 0 < Q.mass f) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (sB Q Φ i p p' μ α β) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (sB Q Φ i p p' μ α β) =
        sCst Q * (bubLogSum Q Q.ε * unitMValue (repBClass i) R (repBSlot i) ![1, 1]
            (unitMMasses R.m Q.mγ Q.Λ Q.mγ Q.Λ ![Q.mγ, Q.Λ]) Q.ε p p' 0 μ α β -
          ∑ f, ∫ x in Ioo (0 : ℝ) 1, sWt Q f x *
            unitMValue (repBClass i) R (repBSlot i) (repBKappa x)
              (unitMMasses R.m Q.mγ Q.Λ Q.mγ Q.Λ (repBExtra (Q.mass f) Q.mγ Q.Λ)) Q.ε p p' 1
              μ α β) := by
  have hU := fun f => jointEnergyFirstIntegral_setIntegral_unitM_repB_one (repBClass_mem i) R
    (four_le_repBSlot i) p p' μ α β (hM f) Q.mγ Q.Λ hε (integrableOn_sWt Q f)
  obtain ⟨hS1, hS2⟩ := jointEnergyFirstIntegrable_finSum Finset.univ
    (fun f ℓ' => ∫ x in Ioo (0 : ℝ) 1, sWt Q f x * sUnit Q R i p p' μ α β f x ℓ')
    fun f _ => (hU f).1
  have hg : QED.TwoLoop.jointEnergyFirstIntegrable 2 (gUnit Q R i p p' μ α β) :=
    jointEnergyFirstIntegrable_unitM (repBClass_mem i) R (repBSlot i) (κ := ![1, 1])
      (fun j => by fin_cases j <;> simp) _ p p' hε μ α β
  obtain ⟨hD1, hD2⟩ := jointEnergyFirstIntegrable_sub_mul
    (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul (bubLogSum Q Q.ε) hg) hS1 1
  have hG := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul (sCst Q) hD1
  have hpt : ∀ ℓ, sB Q Φ i p p' μ α β ℓ = (fun ℓ' => sCst Q * (bubLogSum Q Q.ε *
      gUnit Q R i p p' μ α β ℓ' - 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1,
        sWt Q f x * sUnit Q R i p p' μ α β f x ℓ')) (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) :=
    fun ℓ => by rw [sB_eq_unit Q R Φ hm he hγ hΛ i p p' μ α β hε]; beta_reduce; rw [one_mul]
  refine ⟨QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_of_comp (chgMD i)
    (isUnit_det_chgMD i) _ hG hpt, ?_⟩
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_eq_of_comp (chgMD i) (isUnit_det_chgMD i)
    (G := fun ℓ' => sCst Q * (bubLogSum Q Q.ε * gUnit Q R i p p' μ α β ℓ' - 1 * ∑ f,
      ∫ x in Ioo (0 : ℝ) 1, sWt Q f x * sUnit Q R i p p' μ α β f x ℓ')) _ hpt,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul, hD2,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul, hS2, one_mul]
  congr 2
  exact Finset.sum_congr rfl fun f _ => (hU f).2

end Rest

section Lim

variable {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hγ hγΛ hp hp' hq

/-- **The `ε S_ε` part tends to zero** as `ε → 0⁺`: `ε` times a quantity bounded near `0⁺` (the
log constant times the convergent metric unit, and the `x`-integrals of the transverse units
with one power `k²`, bounded uniformly in `x` and `ε ∈ (0, 1]`). -/
theorem tendsto_sB {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (hΦ : Φ.mass Φ.openLine = R.m) (hMf : ∀ f, R.m ≤ R.mass f) (i : Fin 12) (μ α β : Fin 4) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (sB { R with ε := ε } Φ i p p' μ α β)) (𝓝[>] 0) (𝓝 0) := by
  have hMp : ∀ f, 0 < R.mass f := fun f => hm.trans_le (hMf f)
  set μ₀ := min R.mγ R.m
  have hμ₀ : 0 < μ₀ := lt_min hγ hm
  set X : ℝ → ℂ := fun ε => bubLogSum R ε * unitMValue (repBClass i) R (repBSlot i) ![1, 1]
      (unitMMasses R.m R.mγ R.Λ R.mγ R.Λ ![R.mγ, R.Λ]) ε p p' 0 μ α β -
    ∑ f, ∫ x in Ioo (0 : ℝ) 1, sWt R f x * unitMValue (repBClass i) R (repBSlot i) (repBKappa x)
      (unitMMasses R.m R.mγ R.Λ R.mγ R.Λ (repBExtra (R.mass f) R.mγ R.Λ)) ε p p' 1 μ α β
  set K : ℂ := ((R.e ^ 2 / (4 * Real.pi ^ 2) : ℝ) : ℂ) * (2 * I * wD R 1)
  -- the prefactor `ε`
  have hT : Tendsto (fun ε : ℝ => (ε : ℂ) * K) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Complex.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).mul_const K
    simpa using h
  -- the metric part converges
  have hMG : MassesGe R.mγ R.mγ R.Λ R.mγ R.Λ := ⟨le_rfl, hγΛ, le_rfl, hγΛ⟩
  have hg := (tendsto_bubLogSum R hMp).mul ((unitM_pow (repBClass_mem i) R hm
    (four_le_repBSlot i) hγ hMG hp hp' hq 0 (r := 2) (κ := ![1, 1]) (cs := ![R.mγ, R.Λ])
    (by norm_num) (fun j hj => absurd hj (by have := j.isLt; omega))
    (extraGe_two hγΛ)).2 μ α β)
  obtain ⟨v, hv⟩ : ∃ v, Tendsto (fun ε => bubLogSum R ε * unitMValue (repBClass i) R
      (repBSlot i) ![1, 1] (unitMMasses R.m R.mγ R.Λ R.mγ R.Λ ![R.mγ, R.Λ]) ε p p' 0 μ α β)
      (𝓝[>] 0) (𝓝 v) := ⟨_, hg⟩
  have hg' := hv.norm.eventually (Iic_mem_nhds (lt_add_one ‖v‖))
  -- the integrals are bounded
  have hC : ∀ f, ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖unitMValue (repBClass i) R (repBSlot i) (repBKappa x)
        (unitMMasses R.m R.mγ R.Λ R.mγ R.Λ (repBExtra (R.mass f) R.mγ R.Λ)) ε p p' 1
          μ α β‖ ≤ C := fun f =>
    norm_unitMValue_repB_one_le (repBClass_mem i) R (four_le_repBSlot i) hm hμ₀ hp hp' hq
      μ α β ((min_le_right _ _).trans (hMf f)) (min_le_left _ _)
      ((min_le_left _ _).trans hγΛ)
  choose C hC using hC
  have hB : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) fun ε => ‖X ε‖ := by
    refine isBoundedUnder_of_eventually_le (a := ‖v‖ + 1 + ∑ f, ∫ x in Ioo (0 : ℝ) 1,
      ‖sWt R f x‖ * C f) ?_
    filter_upwards [hg', Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε h1 hε
    refine (norm_sub_le _ _).trans (add_le_add h1 ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun f _ => ?_)))
    refine norm_integral_le_of_norm_le ((integrableOn_sWt R f).norm.mul_const _)
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC f x hx ε hε.1 hε.2) (norm_nonneg _)
  refine (hT.zero_mul_isBoundedUnder_le hB).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hval := (jointEnergyFirstIntegral_sB { R with ε := ε } R Φ (hm := hΦ) (he := rfl)
    (hγ := rfl) (hΛ := rfl) i p p' μ α β hε hMp).2
  have e1 : wD { R with ε := ε } 1 = wD R 1 := rfl
  have e2 : bubLogSum { R with ε := ε } ε = bubLogSum R ε := rfl
  have e3 : sWt { R with ε := ε } = sWt R := rfl
  have e4 : ∀ f, ({ R with ε := ε } : Params).mass f = R.mass f := fun _ => rfl
  rw [hval]
  simp only [X, sCst, K, e1, e2, e3, e4]
  ring

end Lim

end QED.ChainProof.SetCMainB

end
