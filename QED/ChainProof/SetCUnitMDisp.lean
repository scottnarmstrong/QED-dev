/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMRepB

/-!
# Multi-denominator units: decay in a heavy extra mass and the dispersion integral of `repB`

Helper level for set (c) (stage L2). The transverse unit of `repB` at the Feynman parameter `x` is
`(x(1-x))⁻¹` times the unscaled unit with a dispersion line of mass
`μ_x = √(M²/(x(1-x)))` (`QED.ChainProof.SetCUnitM.unitMLimitV_repB_eq`). The bounds of
`QED/ChainProof/SetCUnitMPow.lean` are uniform in this mass but do not decay, so
`(x(1-x))⁻¹ L` would not be integrable at `x → 0, 1`. This file proves the decay `μ⁻²`:

**Partial fractions against the element line.** The heavy extra line `D_t = k² + t² - iε` and the
element line `s` of the eight-line unit, `D_s = k² + μ_s² - iε`, carry the same momentum, so
`D_s⁻¹ D_t⁻¹ = (D_s⁻¹ - D_t⁻¹)/(t² - μ_s²)` (the `iε` cancels). The first term drops the heavy
line; the second is the unit with the heavy mass moved onto line `s` of the eight-line unit, whose
bounds are uniform in its photon masses (`QED.ChainProof.SetCUnitM.norm_unitMLimitV_pow_le`): the
powers `(k²)ⁿ` are still cancelled by the light extra lines.

* `extPerm`, **`unitMIntegrand_perm`**, **`unitMLimitV_perm`**: the unit does not depend on the
  order of the extra lines;
* `slotMa`, `slotMA`, `slotMb`, `slotMB`, `unitMasses_slot`: the photon masses with the mass of
  line `s` replaced;
* `lineDenom_unitM_mEmb`; **`unitMIntegrand_pf`**, **`unitMLimitV_pf`**: the partial fraction at
  fixed `ε ≠ 0` and for the limits;
* **`norm_unitMLimitV_pf_le`**: `‖L‖ ≤ C (1 + ∑ light²)ⁿ / |t² - μ_s²|`;
* **`norm_unitMLimitV_repB_disp_le`**: the transverse unit of `repB` at `x` is bounded by
  `C (1 + m_γ² + Λ²)³ / M²`, uniformly in `x ∈ (0, 1)`;
* `unitMDispRepB`, **`integrableOn_unitMLimitV_repB_mul`**, **`norm_unitMDispRepB_le`**: the
  dispersion integral `∫₀¹ w(x) L(x) dx` against any integrable weight, and its bound.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrixPV
  classPVMasses)
open QED.TwoLoop.VPHalfAtAssembly (specMu mem_Ioo_mul_pos)

/-! ### Permuting the extra lines -/

section Perm

variable {r : ℕ}

/-- The map of the `r + 8` lines induced by a permutation of the extra lines. -/
def extPermFun (σ : Equiv.Perm (Fin r)) : Fin (r + 8) → Fin (r + 8) :=
  mExt (mEmb r) fun j => mExtra r (σ j)

theorem extPermFun_mEmb (σ : Equiv.Perm (Fin r)) (j : Fin 8) :
    extPermFun σ (mEmb r j) = mEmb r j :=
  mExt_mEmb _ _ j

theorem extPermFun_mExtra (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    extPermFun σ (mExtra r j) = mExtra r (σ j) :=
  mExt_mExtra _ _ j

/-- The permutation of the `r + 8` lines induced by a permutation of the extra lines. -/
def extPerm (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r + 8)) where
  toFun := extPermFun σ
  invFun := extPermFun σ.symm
  left_inv i := by
    rcases mem_mEmb_or_mExtra i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [extPermFun_mEmb, extPermFun_mEmb]
    · rw [extPermFun_mExtra, extPermFun_mExtra, Equiv.symm_apply_apply]
  right_inv i := by
    rcases mem_mEmb_or_mExtra i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [extPermFun_mEmb, extPermFun_mEmb]
    · rw [extPermFun_mExtra, extPermFun_mExtra, Equiv.apply_symm_apply]

theorem mExt_comp_perm {X : Type*} (x : Fin 8 → X) (y : Fin r → X) (σ : Equiv.Perm (Fin r))
    (i : Fin (r + 8)) : mExt x (y ∘ σ) i = mExt x y (extPerm σ i) := by
  change mExt x (y ∘ σ) i = mExt x y (extPermFun σ i)
  rcases mem_mEmb_or_mExtra i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [extPermFun_mEmb, mExt_mEmb, mExt_mEmb]
  · rw [extPermFun_mExtra, mExt_mExtra, mExt_mExtra]
    rfl

theorem lineDenom_unitM_perm (c : Class5) (s : Fin 8) (σ : Equiv.Perm (Fin r)) (κ : Fin r → ℝ)
    (p p' : Fin 4 → ℝ) (m a A b B : ℝ) (cs : Fin r → ℝ) (ε : ℝ) (i : Fin (r + 8))
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (unitMMatrix c s (κ ∘ σ)) (unitMMomenta c s (κ ∘ σ) p p')
        (unitMMasses m a A b B (cs ∘ σ)) ε i ℓ =
      lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') (unitMMasses m a A b B cs) ε
        (extPerm σ i) ℓ := by
  have hS : mScale (κ ∘ σ) i = mScale κ (extPerm σ i) := mExt_comp_perm _ _ σ i
  have hL : mLine (r := r) s i = mLine s (extPerm σ i) := mExt_comp_perm id (fun _ => s) σ i
  refine lineDenom_congr ?_ ?_ ?_ ε ℓ
  · simp only [unitMMatrix, hS, hL]
  · simp only [unitMMomenta, hS, hL]
  · exact mExt_comp_perm _ _ σ i

/-- **The unit does not depend on the order of the extra lines.** -/
theorem unitMIntegrand_perm (c : Class5) (P : Params) (s : Fin 8) (σ : Equiv.Perm (Fin r))
    (κ : Fin r → ℝ) (m a A b B : ℝ) (cs : Fin r → ℝ) (ε : ℝ) (p p' : Fin 4 → ℝ) (n : ℕ)
    (μ i j : Fin 4) :
    unitMIntegrand c P s (κ ∘ σ) (unitMMasses m a A b B (cs ∘ σ)) ε p p' n μ i j =
      unitMIntegrand c P s κ (unitMMasses m a A b B cs) ε p p' n μ i j := by
  funext ℓ
  unfold unitMIntegrand
  congr 1
  exact Fintype.prod_equiv (extPerm σ) _ _ fun k => by rw [lineDenom_unitM_perm]

/-- **The limit does not depend on the order of the extra lines.** -/
theorem unitMLimitV_perm (c : Class5) (P : Params) (s : Fin 8) (σ : Equiv.Perm (Fin r))
    (κ : Fin r → ℝ) (m a A b B : ℝ) (cs : Fin r → ℝ) (p p' : Fin 4 → ℝ) (n : ℕ) :
    unitMLimitV c P s (κ ∘ σ) (unitMMasses m a A b B (cs ∘ σ)) p p' n =
      unitMLimitV c P s κ (unitMMasses m a A b B cs) p p' n := by
  unfold unitMLimitV unitMValue
  simp only [unitMIntegrand_perm]

end Perm

/-! ### Partial fractions against the element line -/

section Slot

/-- The photon mass `a` (line `4`), replaced by `t` if `s = 4`. -/
def slotMa (s : Fin 8) (t a : ℝ) : ℝ := if s = 4 then t else a

/-- The photon mass `A` (line `6`), replaced by `t` if `s = 6`. -/
def slotMA (s : Fin 8) (t A : ℝ) : ℝ := if s = 6 then t else A

/-- The photon mass `b` (line `5`), replaced by `t` if `s = 5`. -/
def slotMb (s : Fin 8) (t b : ℝ) : ℝ := if s = 5 then t else b

/-- The photon mass `B` (line `7`), replaced by `t` if `s = 7`. -/
def slotMB (s : Fin 8) (t B : ℝ) : ℝ := if s = 7 then t else B

theorem unitMasses_slot {s : Fin 8} (hs : 4 ≤ (s : ℕ)) (m a A b B t : ℝ) (i : Fin 8) :
    unitMasses m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) i =
      if i = s then t else unitMasses m a A b B i := by
  revert hs
  fin_cases s <;> fin_cases i <;>
    simp [unitMasses, classPVMasses, slotMa, slotMA, slotMb, slotMB]

theorem massesGe_slot {s : Fin 8} {μ₀ a A b B t : ℝ} (hM : MassesGe μ₀ a A b B) (ht : μ₀ ≤ t) :
    MassesGe μ₀ (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [slotMa, slotMA, slotMb, slotMB] <;> split_ifs <;>
    assumption

variable {r : ℕ}

theorem unitMMasses_slot {s : Fin 8} (hs : 4 ≤ (s : ℕ)) (m a A b B t : ℝ) (cs : Fin r → ℝ)
    (i : Fin (r + 8)) (hi : i ≠ mEmb r s) :
    unitMMasses m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs i =
      unitMMasses m a A b B cs i := by
  rcases mem_mEmb_or_mExtra i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hj : j ≠ s := fun h => hi (by rw [h])
    simp only [unitMMasses, mExt_mEmb, unitMasses_slot hs, hj, ite_false]
  · simp only [unitMMasses, mExt_mExtra]

theorem unitMMasses_mEmb (m a A b B : ℝ) (cs : Fin r → ℝ) (j : Fin 8) :
    unitMMasses m a A b B cs (mEmb r j) = unitMasses m a A b B j :=
  mExt_mEmb _ _ j

/-- The element line `s` of the eight-line unit: `D_s = k² + M_s² - iε`. -/
theorem lineDenom_unitM_mEmb (c : Class5) (s : Fin 8) (κ : Fin r → ℝ) (p p' : Fin 4 → ℝ)
    (M : Fin (r + 8) → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (unitMMatrix c s κ) (unitMMomenta c s κ p p') M ε (mEmb r s) ℓ =
      ((Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ) + M (mEmb r s) ^ 2 : ℝ) : ℂ) -
        (ε : ℂ) * I := by
  have hα : unitMMatrix c s κ (mEmb r s) = castLoopMatrix (class5LoopMatrixPV c) s :=
    unitMMatrix_mEmb c s κ s
  have hp : unitMMomenta c s κ p p' (mEmb r s) = pvMomentaE c p p' s := by
    simp [unitMMomenta, mScale, mLine, mExt_mEmb]
  have hk : QED.Integration.TwoLoop.lineMomentum (unitMMatrix c s κ)
      (unitMMomenta c s κ p p') (mEmb r s) ℓ = elemMom c s p p' ℓ := by
    unfold QED.Integration.TwoLoop.lineMomentum elemMom
    rw [hα, hp]
    rfl
  simp only [lineDenom, hk]

theorem prod_split_at {n : ℕ} (f : Fin n → ℂ) (i₀ : Fin n) :
    ∏ k, f k = f i₀ * ∏ k ∈ Finset.univ.erase i₀, f k :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm

theorem ofReal_sub_mul_I_ne_zero {y ε : ℝ} (hε : ε ≠ 0) : ((y : ℝ) : ℂ) - (ε : ℂ) * I ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, Complex.zero_im] at this
  exact hε (by linarith)

/-- The partial fraction `D_u⁻¹ D_v⁻¹ = (D_u⁻¹ - D_v⁻¹)/(v² - u²)`, `D_w = K + w² - iε`. -/
theorem pf_alg {K u v ε : ℝ} (hε : ε ≠ 0) (huv : v ^ 2 ≠ u ^ 2) (Z X : ℂ) :
    Z * (((((K + u ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * X) *
        (((1 ^ 2 * K + v ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹) =
      ((v ^ 2 - u ^ 2 : ℝ) : ℂ)⁻¹ * (Z * ((((K + u ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * X) -
        Z * ((((K + v ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ * X)) := by
  have h1 := ofReal_sub_mul_I_ne_zero (y := K + u ^ 2) hε
  have h2 := ofReal_sub_mul_I_ne_zero (y := K + v ^ 2) hε
  have h3 : ((v ^ 2 - u ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sub_ne_zero.mpr huv)
  rw [one_pow, one_mul]
  field_simp
  push_cast
  ring

theorem prod_erase_slot {s : Fin 8} (hs : 4 ≤ (s : ℕ)) (α : Fin (r + 8) → Fin 2 → ℝ)
    (q : Fin (r + 8) → Fin 4 → ℝ) (m a A b B t : ℝ) (cs : Fin r → ℝ) (ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ k ∈ Finset.univ.erase (mEmb r s),
        (lineDenom α q (unitMMasses m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B)
          cs) ε k ℓ)⁻¹ =
      ∏ k ∈ Finset.univ.erase (mEmb r s), (lineDenom α q (unitMMasses m a A b B cs) ε k ℓ)⁻¹ :=
  Finset.prod_congr rfl fun k hk => by
    rw [lineDenom_congr (i := k) (i' := k) rfl rfl
      (unitMMasses_slot hs m a A b B t cs k (Finset.ne_of_mem_erase hk))]

/-- **Partial fractions against the element line** at fixed `ε ≠ 0`. With the last extra line
unscaled, of mass `t`, and `μ_s` the mass of the element line `s`:
`I(cs) = (t² - μ_s²)⁻¹ (I(init cs) - I'(init cs))`, `I'` the integrand with the mass of line `s`
replaced by `t`. -/
theorem unitMIntegrand_pf (c : Class5) (P : Params) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {κ : Fin (r + 1) → ℝ} (hκ : κ (Fin.last r) = 1) (m a A b B : ℝ) (cs : Fin (r + 1) → ℝ)
    {ε : ℝ} (hε : ε ≠ 0) (ht : cs (Fin.last r) ^ 2 ≠ unitMasses m a A b B s ^ 2)
    (p p' : Fin 4 → ℝ) (n : ℕ) (μ i j : Fin 4) :
    unitMIntegrand c P s κ (unitMMasses m a A b B cs) ε p p' n μ i j = fun ℓ =>
      ((cs (Fin.last r) ^ 2 - unitMasses m a A b B s ^ 2 : ℝ) : ℂ)⁻¹ *
        (unitMIntegrand c P s (Fin.init κ) (unitMMasses m a A b B (Fin.init cs)) ε p p' n μ i j
            ℓ -
          unitMIntegrand c P s (Fin.init κ)
            (unitMMasses m (slotMa s (cs (Fin.last r)) a) (slotMA s (cs (Fin.last r)) A)
              (slotMb s (cs (Fin.last r)) b) (slotMB s (cs (Fin.last r)) B) (Fin.init cs))
            ε p p' n μ i j ℓ) := by
  funext ℓ
  have hprod : ∀ f : Fin (r + 1 + 8) → ℂ,
      ∏ k, f k = (∏ k : Fin (r + 8), f (Fin.castSucc k)) * f (Fin.last (r + 8)) :=
    fun f => Fin.prod_univ_castSucc f
  have hlast := lineDenom_unitM_mExtra c s κ p p' m a A b B cs ε (Fin.last r) ℓ
  rw [mExtra_last, hκ] at hlast
  simp only [unitMIntegrand, hprod, lineDenom_unitM_castSucc, hlast]
  rw [prod_split_at _ (mEmb r s), prod_split_at _ (mEmb r s), prod_erase_slot hs]
  simp only [lineDenom_unitM_mEmb, unitMMasses_mEmb, unitMasses_slot hs, ite_true]
  exact pf_alg hε ht _ _

end Slot

/-! ### The limits -/

section Limit

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
  {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hM hp hp' hq

/-- **Partial fractions for the limits**: with the last extra line unscaled, of mass `t ≠ ±μ_s`,
`L(cs) = (t² - μ_s²)⁻¹ (L(init cs) - L'(init cs))`, `L'` with the mass of line `s` replaced by `t`.
The powers `(k²)ⁿ` are cancelled by the first `r` extra lines (`TrailOne n (init κ)`). -/
theorem unitMLimitV_pf {r n : ℕ} {κ cs : Fin (r + 1) → ℝ} (hnr : n ≤ r)
    (hT : TrailOne n (Fin.init κ)) (hκ : κ (Fin.last r) = 1) (hX : ExtraGe μ₀ κ cs)
    (ht : cs (Fin.last r) ^ 2 ≠ unitMasses P.m a A b B s ^ 2) (μ i j : Fin 4) :
    unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j =
      ((cs (Fin.last r) ^ 2 - unitMasses P.m a A b B s ^ 2 : ℝ) : ℂ)⁻¹ *
        (unitMLimitV c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) p p' n μ i j -
          unitMLimitV c P s (Fin.init κ)
            (unitMMasses P.m (slotMa s (cs (Fin.last r)) a) (slotMA s (cs (Fin.last r)) A)
              (slotMb s (cs (Fin.last r)) b) (slotMB s (cs (Fin.last r)) B) (Fin.init cs))
            p p' n μ i j) := by
  set t := cs (Fin.last r)
  have hM' := massesGe_slot (s := s) hM (hX (Fin.last r)).2.2
  obtain ⟨hI₁, hL₁⟩ := unitM_pow hc P hm hs hμ₀ hM hp hp' hq n hnr hT hX.init
  obtain ⟨hI₂, hL₂⟩ := unitM_pow hc P hm hs hμ₀ hM' hp hp' hq n hnr hT hX.init
  set k : ℂ := ((t ^ 2 - unitMasses P.m a A b B s ^ 2 : ℝ) : ℂ)⁻¹
  have hlim : Tendsto (fun ε => unitMValue c P s κ (unitMMasses P.m a A b B cs) ε p p' n μ i j)
      (𝓝[>] 0) (𝓝 (k * (unitMLimitV c P s (Fin.init κ)
        (unitMMasses P.m a A b B (Fin.init cs)) p p' n μ i j -
          unitMLimitV c P s (Fin.init κ) (unitMMasses P.m (slotMa s t a) (slotMA s t A)
            (slotMb s t b) (slotMB s t B) (Fin.init cs)) p p' n μ i j))) := by
    refine (((hL₁ μ i j).sub (hL₂ μ i j)).const_mul k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h := jointEnergyFirstIntegrable_mul_add_mul (hI₁ ε hε μ i j) (hI₂ ε hε μ i j) k (-k)
    unfold unitMValue
    rw [unitMIntegrand_pf c P hs hκ P.m a A b B cs hε.ne' ht p p' n μ i j]
    have e : (fun ℓ => k * (unitMIntegrand c P s (Fin.init κ)
        (unitMMasses P.m a A b B (Fin.init cs)) ε p p' n μ i j ℓ -
          unitMIntegrand c P s (Fin.init κ) (unitMMasses P.m (slotMa s t a) (slotMA s t A)
            (slotMb s t b) (slotMB s t B) (Fin.init cs)) ε p p' n μ i j ℓ)) =
        fun ℓ => k * unitMIntegrand c P s (Fin.init κ)
          (unitMMasses P.m a A b B (Fin.init cs)) ε p p' n μ i j ℓ +
          (-k) * unitMIntegrand c P s (Fin.init κ) (unitMMasses P.m (slotMa s t a)
            (slotMA s t A) (slotMb s t b) (slotMB s t B) (Fin.init cs)) ε p p' n μ i j ℓ :=
      funext fun ℓ => by ring
    rw [e, h.2]
    ring
  have e := hlim.limUnder_eq
  simp only [unitMLimitV, Matrix.of_apply] at e ⊢
  exact e

end Limit

/-- **Decay in a heavy extra mass.** With the last extra line unscaled and the powers cancelled by
the others: one constant `C` with `‖L‖ ≤ C (1 + ∑ⱼ (init cs)ⱼ²)ⁿ / |t² - μ_s²|` for all photon
masses and extra masses `≥ μ₀`, `t` the last extra mass, `μ_s` the mass of line `s`. -/
theorem norm_unitMLimitV_pf_le {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) {r n : ℕ}
    {κ : Fin (r + 1) → ℝ} (hnr : n ≤ r) (hT : TrailOne n (Fin.init κ))
    (hκl : κ (Fin.last r) = 1) (hκ : ∀ j, 0 < κ j ∧ κ j ≤ 1) :
    ∃ C : ℝ, ∀ (a A b B : ℝ) (cs : Fin (r + 1) → ℝ), MassesGe μ₀ a A b B → (∀ j, μ₀ ≤ cs j) →
      cs (Fin.last r) ^ 2 ≠ unitMasses P.m a A b B s ^ 2 →
      ‖unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n μ i j‖ ≤
        C * (1 + ∑ j, Fin.init cs j ^ 2) ^ n /
          |cs (Fin.last r) ^ 2 - unitMasses P.m a A b B s ^ 2| := by
  obtain ⟨C, hC⟩ := norm_unitMLimitV_pow_le hc P hm hs hμ₀ hp hp' hq μ i j n (r := r)
    (κ := Fin.init κ) hnr hT fun j => hκ _
  refine ⟨2 * |C|, fun a A b B cs hM hcs ht => ?_⟩
  have hX : ExtraGe μ₀ κ cs := fun j => ⟨(hκ j).1, (hκ j).2, hcs j⟩
  have hM' := massesGe_slot (s := s) hM (hcs (Fin.last r))
  have hd : 0 < |cs (Fin.last r) ^ 2 - unitMasses P.m a A b B s ^ 2| :=
    abs_pos.mpr (sub_ne_zero.mpr ht)
  rw [unitMLimitV_pf hc P hm hs hμ₀ hM hp hp' hq hnr hT hκl hX ht, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, inv_mul_eq_div, div_le_div_iff_of_pos_right hd]
  have h1 := hC a A b B (Fin.init cs) hM fun j => hcs _
  have h2 := hC _ _ _ _ (Fin.init cs) hM' fun j => hcs _
  have hC' : C ≤ |C| := le_abs_self C
  have hP0 : 0 ≤ (1 + ∑ j, Fin.init cs j ^ 2) ^ n := by positivity
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ C * (1 + ∑ j, Fin.init cs j ^ 2) ^ n + C * (1 + ∑ j, Fin.init cs j ^ 2) ^ n :=
        add_le_add h1 h2
    _ ≤ 2 * |C| * (1 + ∑ j, Fin.init cs j ^ 2) ^ n := by nlinarith

/-! ### The transverse unit of `repB` -/

theorem repBExtra_rot (t mγ Λ : ℝ) :
    (![mγ, Λ, t] : Fin 3 → ℝ) ∘ (finRotate 3).symm = repBExtra t mγ Λ := by
  funext j
  fin_cases j <;> rfl

/-- The unscaled `repB` unit with the dispersion line moved last. -/
theorem unitMLimitV_repBExtra_rot (c : Class5) (P : Params) (s : Fin 8) (m a A b B t mγ Λ : ℝ)
    (p p' : Fin 4 → ℝ) (n : ℕ) :
    unitMLimitV c P s (fun _ : Fin 3 => (1 : ℝ)) (unitMMasses m a A b B (repBExtra t mγ Λ)) p p'
        n =
      unitMLimitV c P s (fun _ : Fin 3 => (1 : ℝ)) (unitMMasses m a A b B ![mγ, Λ, t]) p p' n := by
  rw [← repBExtra_rot]
  exact unitMLimitV_perm c P s (finRotate 3).symm (fun _ => 1) m a A b B ![mγ, Λ, t] p p' n

theorem unitMasses_photon {s : Fin 8} (hs : 4 ≤ (s : ℕ)) (m mγ Λ : ℝ) :
    unitMasses m mγ Λ mγ Λ s = mγ ∨ unitMasses m mγ Λ mγ Λ s = Λ := by
  revert hs
  fin_cases s <;> simp [unitMasses, classPVMasses]

/-- **The decay of the `repB` unit in the dispersion mass**: one constant `C` with
`‖L(x)‖ ≤ C (1 + m_γ² + Λ²)³ / M²` for all `x ∈ (0, 1)` and all masses `≥ μ₀`. In particular the
transverse unit of `repB` is bounded uniformly in the Feynman parameter of the inserted bubble. -/
theorem norm_unitMLimitV_repB_disp_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ M mγ Λ : ℝ, μ₀ ≤ M → μ₀ ≤ mγ → μ₀ ≤ Λ →
      ‖unitMLimitV c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) p p' 2
          μ i j‖ ≤ C * (1 + mγ ^ 2 + Λ ^ 2) ^ 3 / M ^ 2 := by
  obtain ⟨C₁, hC₁⟩ := norm_unitMLimitV_pf_le hc P hm hs hμ₀ hp hp' hq μ i j (r := 2) (n := 2)
    (κ := fun _ => 1) le_rfl (fun _ _ => rfl) rfl fun _ => ⟨one_pos, le_rfl⟩
  obtain ⟨C₂, hC₂⟩ := norm_unitMLimitV_repB_le hc P hm hs hμ₀ hp hp' hq μ i j
  refine ⟨2 * |C₁| + 18 * |C₂|, fun x hx M mγ Λ hM hmγ hΛ => ?_⟩
  have hw := mem_Ioo_mul_pos hx
  have hM0 : 0 < M := hμ₀.trans_le hM
  set w := x * (1 - x) with hwdef
  set μ' := specMu M x with hμdef
  have hμ2 : μ' ^ 2 = M ^ 2 / w := Real.sq_sqrt (div_nonneg (sq_nonneg M) hw.le)
  have hwμ : w * μ' ^ 2 = M ^ 2 := by rw [hμ2]; field_simp
  set μs := unitMasses P.m mγ Λ mγ Λ s with hμs
  have hμs0 : μ₀ ≤ μs := by
    rcases unitMasses_photon hs P.m mγ Λ with h | h <;> rw [hμs, h] <;> assumption
  have hμs2 : μs ^ 2 ≤ mγ ^ 2 + Λ ^ 2 := by
    rcases unitMasses_photon hs P.m mγ Λ with h | h <;> rw [hμs, h] <;> nlinarith
  set S := 1 + mγ ^ 2 + Λ ^ 2 with hS
  have hS1 : 1 ≤ S := by rw [hS]; nlinarith [sq_nonneg mγ, sq_nonneg Λ]
  have hS0 : 0 ≤ S := by linarith
  have hM2 : 0 < M ^ 2 := by positivity
  have hfin : 0 ≤ (2 * |C₁| + 18 * |C₂|) * S ^ 3 / M ^ 2 := by positivity
  by_cases hcase : 2 * μs ^ 2 ≤ μ' ^ 2
  · -- partial fractions
    have hμs2p : 0 < μs ^ 2 := pow_pos (hμ₀.trans_le hμs0) 2
    have hne : μ' ^ 2 ≠ μs ^ 2 := by intro h; linarith
    have hμ'0 : μ₀ ≤ μ' := hM.trans (QED.TwoLoop.VPHalfAtAssembly.specMu_ge hM0 hx)
    have h1 := hC₁ mγ Λ mγ Λ ![mγ, Λ, μ'] (massesGe_repB hmγ hΛ)
      (fun j => by fin_cases j <;> assumption) hne
    have hsum : ∑ j, Fin.init (![mγ, Λ, μ'] : Fin 3 → ℝ) j ^ 2 = mγ ^ 2 + Λ ^ 2 := by
      simp [Fin.sum_univ_two, Fin.init]
    rw [hsum, ← unitMLimitV_repBExtra_rot] at h1
    rw [unitMLimitV_repB_eq hc P hm hs hμ₀ hmγ hΛ hp hp' hq hx hM μ i j, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg hw.le]
    have hd : μ' ^ 2 / 2 ≤ |μ' ^ 2 - μs ^ 2| := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have hμp : 0 < μ' ^ 2 / 2 := by linarith
    have hS2 : S ^ 2 ≤ S ^ 3 := pow_le_pow_right₀ hS1 (by norm_num)
    have hA : (C₁ * (1 + (mγ ^ 2 + Λ ^ 2)) ^ 2) ≤ |C₁| * S ^ 3 := by
      rw [show 1 + (mγ ^ 2 + Λ ^ 2) = S by ring]
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hS2 (abs_nonneg _))
    calc w⁻¹ * ‖_‖ ≤ w⁻¹ * (|C₁| * S ^ 3 / (μ' ^ 2 / 2)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
          exact div_le_div₀ (by positivity) hA hμp hd
      _ = 2 * |C₁| * S ^ 3 / M ^ 2 := by
          rw [← hwμ]; field_simp
      _ ≤ (2 * |C₁| + 18 * |C₂|) * S ^ 3 / M ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by linarith [abs_nonneg C₂]) (by positivity)) hM2.le
  · -- the dispersion mass is light: `(x(1-x))⁻¹ = μ²/M²` is bounded
    push Not at hcase
    have h2 := hC₂ x hx M mγ Λ hM hmγ hΛ
    have hwinv : w⁻¹ ≤ 2 * S / M ^ 2 := by
      have hμ2ne : μ' ^ 2 ≠ 0 := fun h => by rw [h, mul_zero] at hwμ; linarith
      have e : w⁻¹ = μ' ^ 2 / M ^ 2 := by
        rw [← hwμ, mul_comm, ← div_div, div_self hμ2ne, one_div]
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) hM2.le
    have hB : C₂ * (1 + (μ' ^ 2 + mγ ^ 2 + Λ ^ 2)) ^ 2 ≤ |C₂| * (3 * S) ^ 2 := by
      refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    calc _ ≤ w⁻¹ * (C₂ * (1 + (μ' ^ 2 + mγ ^ 2 + Λ ^ 2)) ^ 2) := h2
      _ ≤ w⁻¹ * (|C₂| * (3 * S) ^ 2) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ (2 * S / M ^ 2) * (|C₂| * (3 * S) ^ 2) :=
          mul_le_mul_of_nonneg_right hwinv (by positivity)
      _ = 18 * |C₂| * S ^ 3 / M ^ 2 := by ring
      _ ≤ (2 * |C₁| + 18 * |C₂|) * S ^ 3 / M ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by linarith [abs_nonneg C₁]) (by positivity)) hM2.le

/-! ### The dispersion integral -/

/-- **The dispersion integral of the transverse unit of `repB`** against a weight `w` on the
Feynman parameter `x ∈ (0, 1)` of the inserted bubble: `∫₀¹ w(x) L(x) dx`. -/
noncomputable def unitMDispRepB (c : Class5) (P : Params) (s : Fin 8) (w : ℝ → ℂ) (M mγ Λ : ℝ)
    (p p' : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun i j => ∫ x in Ioo (0 : ℝ) 1, w x *
    unitMLimitV c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) p p' 2 μ i j

section Disp

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hp hp' hq

/-- **Integrability of the dispersion integrand** for every weight integrable on `(0, 1)`. -/
theorem integrableOn_unitMLimitV_repB_mul {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1))
    {M mγ Λ : ℝ} (hM : μ₀ ≤ M) (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ) (μ i j : Fin 4) :
    IntegrableOn (fun x => w x * unitMLimitV c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) p p' 2 μ i j) (Ioo 0 1) := by
  obtain ⟨C, hC⟩ := norm_unitMLimitV_repB_disp_le hc P hm hs hμ₀ hp hp' hq μ i j
  refine Integrable.mul_bdd (c := C * (1 + mγ ^ 2 + Λ ^ 2) ^ 3 / M ^ 2) hw
    ((continuousOn_unitMLimitV_repB hc P hm hs hμ₀ hM hmγ hΛ hp hp'
      hq μ i j).aestronglyMeasurable measurableSet_Ioo) ?_
  exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx =>
    hC x hx M mγ Λ hM hmγ hΛ)

/-- **The bound of the dispersion integral**: one constant `C` with
`‖∫₀¹ w L‖ ≤ C (1 + m_γ² + Λ²)³ / M² ∫₀¹ ‖w‖` for every integrable weight and all masses
`≥ μ₀`. -/
theorem norm_unitMDispRepB_le (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ w : ℝ → ℂ, IntegrableOn w (Ioo 0 1) → ∀ M mγ Λ : ℝ, μ₀ ≤ M → μ₀ ≤ mγ →
      μ₀ ≤ Λ → ‖unitMDispRepB c P s w M mγ Λ p p' μ i j‖ ≤
        C * (1 + mγ ^ 2 + Λ ^ 2) ^ 3 / M ^ 2 * ∫ x in Ioo (0 : ℝ) 1, ‖w x‖ := by
  obtain ⟨C, hC⟩ := norm_unitMLimitV_repB_disp_le hc P hm hs hμ₀ hp hp' hq μ i j
  refine ⟨C, fun w hw M mγ Λ hM hmγ hΛ => ?_⟩
  simp only [unitMDispRepB, Matrix.of_apply]
  rw [mul_comm _ (∫ x in Ioo (0 : ℝ) 1, ‖w x‖), ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hw.norm.mul_const _) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC x hx M mγ Λ hM hmγ hΛ) (norm_nonneg _)

end Disp

end QED.ChainProof.SetCUnitM

end
