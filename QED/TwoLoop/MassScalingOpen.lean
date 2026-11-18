/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.MassScalingBasic
public import QED.TwoLoop.PauliZeroExplicitOpen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Mass scaling of the open-line class values

For the six open-line classes `c ∈ {L, X, C₊, C₋, S₊, S₋}` and `s > 0`,

`openZero c (massScale s P) = s⁵ · openZero c P`

(`openZero_massScale`). The class numerator is a chain of four electron numerators `m - k̸` and two
Pauli–Villars photon factors `(Λ² - m_γ²) g`, so it is homogeneous of degree `8` in the masses,
external and loop momenta jointly (`classNumM_massScale`). With the Pauli weights (degree `5`) the
projected parametric numerator `N_c(x, u)` scales by `s¹³` (`openNum_massScale`), the second
Symanzik function `V_c(x)` by `s²` (`openV_massScale`), and `s¹³ / (s²)⁴ = s⁵`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.TwoLoop.MassScaling

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix class5LoopMatrixPV lineMomentum
  classLXMomenta classCpSpMomenta classCmSmMomenta classVPMomenta classPVMasses)

/-! ### The chain form -/

theorem pvEta_massScale (s : ℝ) (P : Params) (x y : Fin 4) :
    pvEta (massScale s P) x y = (s : ℂ) ^ 2 * pvEta P x y := by
  simp only [pvEta, massScale_Λ, massScale_mγ]
  push_cast
  ring

theorem openChain_smul (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (a : ℂ) : openChain G (fun i => a • E i) = a ^ 4 • openChain G E := by
  simp only [openChain, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

theorem chainNum_massScale (s : ℝ) (P : Params) (σ : Equiv.Perm (Fin 5))
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    chainNum (massScale s P) σ (fun i => (s : ℂ) • E i) μ = (s : ℂ) ^ 8 • chainNum P σ E μ := by
  simp only [chainNum, pvEta_massScale, openChain_smul, smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  ring

/-! ### Momenta -/

theorem extMomenta_smul (s : ℝ) (c : Class5) (p p' : Fin 4 → ℝ) (i : Fin 6) :
    extMomenta c (s • p) (s • p') i = s • extMomenta c p p' i := by
  cases c <;> fin_cases i <;>
    simp [extMomenta, classLXMomenta, classCpSpMomenta, classCmSmMomenta, classVPMomenta]

theorem lineMomentum_smul {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (i : Fin (m + 1)) {s : ℝ} (hs : s ≠ 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum α (fun k => s • q k) i ℓ = s • lineMomentum α q i (s⁻¹ • ℓ) := by
  funext μ
  simp only [QED.Integration.TwoLoop.lineMomentum, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by field_simp

theorem classMomE_smul (c : Class5) (p p' : Fin 4 → ℝ) {s : ℝ} (hs : s ≠ 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line c.rep) :
    classMomE c (s • p) (s • p') ℓ f = s • classMomE c p p' (s⁻¹ • ℓ) f := by
  unfold classMomE
  rw [show extMomenta c (s • p) (s • p') = fun i => s • extMomenta c p p' i from
    funext (extMomenta_smul s c p p')]
  exact lineMomentum_smul _ _ _ hs ℓ

theorem pvMomentaE_smul (s : ℝ) (c : Class5) (p p' : Fin 4 → ℝ) :
    pvMomentaE c (s • p) (s • p') = s • pvMomentaE c p p' :=
  funext fun _ => extMomenta_smul s c p p' _

theorem pvMasses_massScale (s : ℝ) (P : Params) : pvMasses (massScale s P) = s • pvMasses P := by
  funext i
  fin_cases i <;> simp [pvMasses, classPVMasses]

/-! ### The class numerators -/

theorem classNumM_massScale_of_chain {c : Class5} (σ : Equiv.Perm (Fin 5))
    (line : Fin 4 → FermionLine c.rep)
    (heq : ∀ (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
      (ℓ : Fin 2 → Fin 4 → ℝ),
      classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
        chainNum P σ (fun i => electronNumerator P.m
          (classMomE c (pIn 0) (pOut 0) ℓ (.inl (line i)))) (μ 0) (αOut 0) (βIn 0))
    {s : ℝ} (hs : s ≠ 0) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumM c (massScale s P) (s • p) (s • p') μ ℓ =
      (s : ℂ) ^ 8 • classNumM c P p p' μ (s⁻¹ • ℓ) := by
  have hE : (fun i => electronNumerator (massScale s P).m
      (classMomE c (s • p) (s • p') ℓ (.inl (line i)))) =
      fun i => (s : ℂ) • electronNumerator P.m (classMomE c p p' (s⁻¹ • ℓ) (.inl (line i))) := by
    funext i
    rw [massScale_m, classMomE_smul c p p' hs, electronNumerator_smul]
  ext i j
  simp only [classNumM, Matrix.of_apply, heq, Matrix.smul_apply, smul_eq_mul]
  rw [hE, chainNum_massScale, Matrix.smul_apply, smul_eq_mul, massScale_e]
  ring

/-- **The open-class numerators are homogeneous of degree `8`** in the masses, the external and
the loop momenta. -/
theorem classNumM_massScale {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    {s : ℝ} (hs : s ≠ 0) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumM c (massScale s P) (s • p) (s • p') μ ℓ =
      (s : ℂ) ^ 8 • classNumM c P p p' μ (s⁻¹ • ℓ) := by
  simp only [QED.TwoLoop.ClassIntegrable.openClasses, Finset.mem_insert,
    Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact classNumM_massScale_of_chain permL lineL chain_L hs P p p' μ ℓ
  · exact classNumM_massScale_of_chain permX lineX chain_X hs P p p' μ ℓ
  · exact classNumM_massScale_of_chain permCp lineCp chain_Cp hs P p p' μ ℓ
  · exact classNumM_massScale_of_chain permCm lineCm chain_Cm hs P p p' μ ℓ
  · exact classNumM_massScale_of_chain permSp lineSp chain_Sp hs P p p' μ ℓ
  · exact classNumM_massScale_of_chain permSm lineSm chain_Sm hs P p p' μ ℓ

theorem openF_massScale {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    {s : ℝ} (hs : s ≠ 0) (P : Params) (p' : Fin 4 → ℝ) (j : Idx) :
    openF c (massScale s P) (s • p') j = fun ℓ => (s : ℂ) ^ 8 * openF c P p' j (s⁻¹ • ℓ) := by
  funext ℓ
  simp only [openF, massScale_m, restMomentum_smul, classNumM_massScale hc hs,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem exists_quartic_openF {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (p' : Fin 4 → ℝ) (j : Idx) : ∃ Q : LoopQuartic, Q.eval = openF c P p' j := by
  have hF : openF c P p' j = fun ℓ => twoLoopNorm * classNumeratorE c P (fun _ => p')
      (fun _ => restMomentum P.m) (fun _ => p' - restMomentum P.m) (fun _ => j.2.1)
      (fun _ => j.2.2) (fun _ => j.1) ℓ :=
    funext fun ℓ => by simp only [openF, Matrix.smul_apply, classNumM, Matrix.of_apply,
      smul_eq_mul]
  rw [hF]
  exact ((QED.TwoLoop.ClassIntegrable.isLoopPoly_classNumeratorE hc P _ _ _ _ _ _).const_mul
    _).exists_loopQuartic

/-! ### The class values -/

/-- **The projected parametric numerator of an open class scales by `s¹³`.** -/
theorem openNum_massScale {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    {s : ℝ} (hs : s ≠ 0) (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum c (massScale s P) x u = (s : ℂ) ^ 13 * openNum c P x u := by
  simp only [openNum, massScale_m, curveMomentum_smul, restMomentum_smul, pauliWt_smul,
    pvMomentaE_smul, pvMasses_massScale, openF_massScale hc hs]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [paramNumOf_smul (exists_quartic_openF hc P _ j) _ hs]
  ring

theorem openV_massScale (c : Class5) (s : ℝ) (P : Params) (x : Fin 7 → ℝ) :
    openV c (massScale s P) x = s ^ 2 * openV c P x := by
  simp only [openV, massScale_m, restMomentum_smul, pvMomentaE_smul, pvMasses_massScale,
    symanzikV_smul]

theorem secondCoeff_const_mul_openNum {c : Class5}
    (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (x : Fin 7 → ℝ) (a : ℂ) :
    secondCoeff (fun u => a * openNum c P x u) = a * secondCoeff (openNum c P x) := by
  have hpn : openNum c P x = projNum (openCurve hc P hm hmγ hΛ)
      (fun u (j : Idx) ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m)
        (curveMomentum P.m u) j.1 ℓ) j.2.1 j.2.2)
      (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
      x := rfl
  rw [hpn]
  exact secondCoeff_const_mul_projNum (openCurve hc P hm hmγ hΛ) (D := 8) (n := 4) (r := 4)
    (Dω := 8) (fun u (j : Idx) ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m)
        (curveMomentum P.m u) j.1 ℓ) j.2.1 j.2.2)
    (fun j => by
      have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => twoLoopNorm * classNumeratorE c P (fun _ => y 0)
          (fun _ => restMomentum P.m) (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1)
          (fun _ => j.2.2) (fun _ => j.1) ℓ)
        (fun ℓ => (isLoopPoly_classNumeratorE_out hc P _ _ _ _ ℓ).const_mul _)
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
      refine h.congr fun ℓ u _ => ?_
      simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul])
    (fun u _ j => exists_quartic_openF hc P _ j)
    (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
    (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m) x a

/-- **Mass scaling of an open-line class value**: `openZero c (massScale s P) = s⁵ openZero c P`
for `s > 0`. -/
theorem openZero_massScale {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {s : ℝ} (hs : 0 < s) :
    openZero c (massScale s P) = (s : ℂ) ^ 5 * openZero c P := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  unfold openZero
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hN : openNum c (massScale s P) x = fun u => (s : ℂ) ^ 13 * openNum c P x u :=
    funext (openNum_massScale hc hs.ne' P x)
  simp only [hN, openV_massScale]
  rw [secondCoeff_const_mul_openNum hc P hm hmγ hΛ x]
  have hV : ((s ^ 2 * openV c P x : ℝ) : ℂ) ^ 4 = (s : ℂ) ^ 8 * ((openV c P x : ℝ) : ℂ) ^ 4 := by
    push_cast
    ring
  rw [hV, show (s : ℂ) ^ 13 = (s : ℂ) ^ 8 * (s : ℂ) ^ 5 by ring, mul_assoc,
    mul_div_mul_left _ _ (pow_ne_zero 8 hs0), mul_div_assoc]

end QED.TwoLoop.MassScaling

end
