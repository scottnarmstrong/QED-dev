/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetACovLimit
public import QED.ChainProof.SetAMirror
public import QED.ChainProof.SetANestMatch
public import QED.ChainProof.SetANestSum

/-!
# The set (a) headline (HA₆), assembled from the loop classes and a regulator limit

Helper level for (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetAPauliLimit.lean`, `DRAFT_SORRY`, not imported).

* `SetANestClasses P₀` (**open**, obligation (N)): at admissible regulators, on-shell
  positive-energy pairs with `q² > 0` and `ε ∈ (0, 1]`, the seven loop classes `VA, VB, VC, GW,
  GU, FA, FB` of set (a) are in nested form (`QED.ChainProof.SetANest.LoopNested`) with photon
  tensors whose three group sums (vertex-type, `gaugeCt`, `fermionCt`) are `(1/i)` times the
  values at `-ℓ` of the matching two-photon classes of `Π⁽⁴⁾`.
* **`setANestForm_of_classes`**: `SetANestClasses P₀ → SetANestForm P₀`
  (`familyVertex_setA_eq_nested` with `hsum_of_groups`; the hypotheses of T★ᵤ at the flavours of
  (HA₆) are proved).
* **`setALimitLink_of_nestForm`**: `SetANestForm P₀ → SetALimitLink P₀` (the nested form, T★ᵤ
  `regFlavors_spec` and the outer reduction `saOuterForm_list`).
* `SetARegLimitPV a`: the regulator limit of (HA₆) for the fixed-regulator value `a`, over the
  regulator masses `M₁ ≠ M₂` only. Admissible regulators have `M₁ ≠ M₂` (`ne_of_pv`), and a value
  built from admissible data is unconstrained at `M₁ = M₂`: for `a = setAPauliValue P₀ (setAR P₀)`
  it is `0` there, so `SetARegLimit a` of `QED/ChainProof/SetAPauliCond.lean` is false for it.
  `setAFixedLink_patch`, `setARegLimit_patch`: the value patched to `A₁⁽⁶⁾(a)` at `M₁ = M₂` has
  the same fixed link and satisfies `SetARegLimit`.
* **`isFormFactorPair_vertexSetA_pauli_limit_of_nestForm`**: the proposition of (HA₆) from
  `SetANestForm P₀`, the nested value `SetANestedAt P₀ R`, the regularity `SetAPhotonReg P₀ R` and
  `SetARegLimitPV (setAPauliValue P₀ R)`, for any photon function `R`.
* **`isFormFactorPair_vertexSetA_pauli_limit_of_classes`**: the same with `SetANestClasses P₀`.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetAPauliAssembly

open QED.OneLoop QED.TwoLoop.VPUnitNested QED.ChainProof.SetASpec QED.ChainProof.SetANest
open QED.ChainProof.SetANestedAt QED.ChainProof.SetAPauli

/-! ### Obligation (N): the loop classes -/

/-- The parameters of (HA₆) at fixed regulators and `ε`. -/
abbrev regParamsε (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ ε : ℝ) : Params :=
  { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }

/-- **Obligation (N) of (HA₆)** (open): at admissible regulators, every on-shell positive-energy
pair with `q² > 0` and every `ε ∈ (0, 1]`, the seven set (a) loop classes are in nested form with
photon tensors `X_R`, and the group sums of the `X_R` are `(1/i)` times the values at `-ℓ` of the
matching two-photon classes of `Π⁽⁴⁾` (`QED.GradedProof.VP2`). -/
def SetANestClasses (P₀ : Params) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D, SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D →
    ∀ p' p, IsPairQ P₀.m p' p → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ XVA XVB XVC XGW XGU XFA XFB : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ,
        LoopNested (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
            SetALink.repVA XVA p' p ∧
          LoopNested (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
            SetALink.repVB XVB p' p ∧
          LoopNested (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
            SetALink.repVC XVC p' p ∧
          LoopNested (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
            SetALink.repGW XGW p' p ∧
          LoopNested (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
            SetALink.repGU XGU p' p ∧
          LoopNested (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
            SetALink.repFA XFA p' p ∧
          LoopNested (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D
            SetALink.repFB XFB p' p ∧
          (∀ ℓ a b, XVA ℓ a b + XVB ℓ a b + XVC ℓ a b = (1 / I) *
            (GradedProof.VP2.val0 (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
                (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (-ℓ) a b GradedProof.VP2.repVA +
              GradedProof.VP2.val0 (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
                (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (-ℓ) a b GradedProof.VP2.repVB +
              GradedProof.VP2.val0 (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
                (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (-ℓ) a b GradedProof.VP2.repVC)) ∧
          (∀ ℓ a b, XGW ℓ a b + XGU ℓ a b = (1 / I) *
            (GradedProof.VP2.val0 (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
                (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (-ℓ) a b GradedProof.VP2.repG0 +
              GradedProof.VP2.val0 (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
                (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (-ℓ) a b GradedProof.VP2.repG1)) ∧
          (∀ ℓ a b, XFA ℓ a b + XFB ℓ a b = (1 / I) *
            (GradedProof.VP2.val0 (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
                (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (-ℓ) a b GradedProof.VP2.repF0 +
              GradedProof.VP2.val0 (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
                (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D (-ℓ) a b GradedProof.VP2.repF1))

/-- **The nested form from the loop classes**: `SetANestClasses P₀ → SetANestForm P₀`. -/
theorem setANestForm_of_classes {P₀ : Params} (hm : 0 < P₀.m) (hC : SetANestClasses P₀) :
    SetANestForm P₀ := by
  intro M₁ M₂ c₁ c₂ mγ Λ D hA p' p hpq ε hε hε1 μ i j
  obtain ⟨XVA, XVB, XVC, XGW, XGU, XFA, XFB, hVA, hVB, hVC, hGW, hGU, hFA, hFB, hV, hG, hF⟩ :=
    hC M₁ M₂ c₁ c₂ mγ Λ D hA p' p hpq ε hε hε1
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, -, hD⟩ := hA
  obtain ⟨hp', hp, hp0', hp0, -⟩ := hpq
  have hsum := hsum_of_groups (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D Graded.leptonRep P₀.m hm
    (QED.GradedProof.RPi4.le_leptonFlavors_mass (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hM₁ hM₂
      (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0))
    hmγ hΛ QED.GradedProof.RPi4.leptonRep_idem
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₁ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hPV₁
      fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.leptonFlavors_blockPV₂ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) _ hPV₂
      fun ℓ => ℓ.elim0)
    (QED.GradedProof.RPi4.hD_of_renormalized _ _ _ hD) hε hε1
    XVA XVB XVC XGW XGU XFA XFB hV hG hF
  exact familyVertex_setA_eq_nested (regParamsε P₀ M₁ M₂ c₁ c₂ mγ Λ ε)
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D hε hm hmγ hmΛ.le hp' hp hp0' hp0
    XVA XVB XVC XGW XGU XFA XFB hVA hVB hVC hGW hGU hFA hFB hsum μ i j

/-! ### The limit link from the nested form -/

/-- **The limit link of (HA₆) from the nested form**: `SetANestForm P₀ → SetALimitLink P₀`. -/
theorem setALimitLink_of_nestForm {P₀ : Params} (hm : 0 < P₀.m) (hN : SetANestForm P₀) :
    SetALimitLink P₀ := by
  intro M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD p' p hp' hp hp0' hp0 hq
  have hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D := ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, hm2, hD⟩
  have hpq : IsPairQ P₀.m p' p := ⟨hp', hp, hp0', hp0, hq⟩
  obtain ⟨L, hL, hVP⟩ := regFlavors_spec hm hA
  set Mlo := min P₀.m (min mγ Λ)
  have hMlo : 0 < Mlo := lt_min hm (lt_min hmγ hΛ)
  have h1 : Mlo ≤ mγ := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : Mlo ≤ Λ := (min_le_right _ _).trans (min_le_right _ _)
  have hMs : ∀ i, Mlo ≤ saMs4 mγ Λ i := fun i => by
    fin_cases i <;> simp [saMs4, h1, h2]
  refine ⟨Mlo, Mlo, 2, saMs4 mγ Λ, hMlo, le_rfl, hMs, fun μ a b => ?_⟩
  obtain ⟨s, c, τ, hτ, hval⟩ :=
    (saOuterForm_list hm hMlo le_rfl h1 h2 hp' hp hp0' hp0 P₀.e L hL μ a b).exists_finset
  refine ⟨s, fun i => (1 / I) * c i, τ, hτ, fun ε hε hε1 => ?_⟩
  obtain ⟨-, he⟩ := hN M₁ M₂ c₁ c₂ mγ Λ D hA p' p hpq ε hε hε1 μ a b
  have hX : vpTwo P₀ M₁ M₂ c₁ c₂ mγ Λ D ε = fun k a b => saOuterTensor L ε k a b :=
    funext fun k => funext fun a => funext fun b => hVP ε hε hε1 k a b
  rw [hX] at he
  refine he.trans ?_
  have e2 : energyFirstIntegral (nestInt P₀.e P₀.m mγ Λ ε p' p
      (fun k a b => saOuterTensor L ε k a b) μ a b) =
      ∑ i ∈ s, c i * (τ i).val P₀.m (saMs4 mγ Λ) p' p ε := (hval ε hε hε1).2
  rw [e2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The regulator limit away from `M₁ = M₂` -/

/-- **The regulator limit of (HA₆) over `M₁ ≠ M₂`** (open for a given `a`): the
fixed-regulator value `a` tends to `A₁⁽⁶⁾(a)` in the iterated order of D-37.4, the regulator
fermion masses ranging over distinct pairs (the admissible ones, `ne_of_pv`). -/
def SetARegLimitPV (a : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ η > 0, ∃ RM : ℝ, ∀ M₁ M₂ : ℝ, RM < M₁ → RM < M₂ → M₁ ≠ M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
    ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → |a mγ Λ M₁ M₂ - ThreeLoop.a1SixSetA| < η

/-- Pauli–Villars regulators heavier than `m > 0` are distinct. -/
theorem ne_of_pv {m M₁ M₂ c₁ c₂ : ℝ} (hm : 0 < m) (hM₁ : m < M₁) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) : M₁ ≠ M₂ := by
  rintro rfl
  have e : m ^ 2 = M₁ ^ 2 := by linear_combination hPV₂ - M₁ ^ 2 * hPV₁
  nlinarith

open scoped Classical in
/-- The fixed-regulator value patched to `A₁⁽⁶⁾(a)` at `M₁ = M₂`. -/
noncomputable def patch (a : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun mγ Λ M₁ M₂ => if M₁ = M₂ then ThreeLoop.a1SixSetA else a mγ Λ M₁ M₂

theorem setAFixedLink_patch {P₀ : Params} {a : ℝ → ℝ → ℝ → ℝ → ℝ} (hm : 0 < P₀.m)
    (h : SetAFixedLink P₀ a) : SetAFixedLink P₀ (patch a) := by
  intro M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD η hη
  have hp : patch a mγ Λ M₁ M₂ = a mγ Λ M₁ M₂ := by simp [patch, ne_of_pv hm hM₁ hPV₁ hPV₂]
  rw [hp]
  exact h M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD η hη

theorem setARegLimit_patch {a : ℝ → ℝ → ℝ → ℝ → ℝ} (h : SetARegLimitPV a) :
    SetARegLimit (patch a) := by
  intro η hη
  obtain ⟨RM, hRM⟩ := h η hη
  refine ⟨RM, fun M₁ M₂ h₁ h₂ => ?_⟩
  by_cases hM : M₁ = M₂
  · exact ⟨1, one_pos, 0, fun mγ Λ _ _ _ => by simp [patch, hM, hη]⟩
  · obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hRM M₁ M₂ h₁ h₂ hM
    exact ⟨δ, hδ, Λ₀, fun mγ Λ h0 h1 h2 => by
      simpa [patch, hM] using hΛ₀ mγ Λ h0 h1 h2⟩

/-! ### The headline proposition -/

/-- **(HA₆) from the nested form, the nested value and the regulator limit**, for any photon
function `R`. The conclusion is, verbatim, the proposition of the frozen
`QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`. -/
theorem isFormFactorPair_vertexSetA_pauli_limit_of_nestForm {R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (P₀ : Params) (hN : SetANestForm P₀) (hNA : SetANestedAt P₀ R) (hR : SetAPhotonReg P₀ R)
    (hreg : SetARegLimitPV (setAPauliValue P₀ R)) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ)
    (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (ThreeLoop.a1SixSetA : ℂ)‖ < η :=
  isFormFactorPair_vertexSetA_pauli_limit_of_links P₀
    (setAFixedLink_patch hm (setAFixedLink_of_nested he hm (setALimitLink_of_nestForm hm hN)
      (SetACov.setACovLink_of_nestForm hm hN) (SetAMirror.setAMirrorAt P₀) hNA hR))
    (setARegLimit_patch hreg) he hm η hη

/-- **(HA₆) from the loop classes, the nested value and the regulator limit**, for any photon
function `R`. -/
theorem isFormFactorPair_vertexSetA_pauli_limit_of_classes {R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (P₀ : Params) (hC : SetANestClasses P₀) (hNA : SetANestedAt P₀ R) (hR : SetAPhotonReg P₀ R)
    (hreg : SetARegLimitPV (setAPauliValue P₀ R)) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ)
    (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (ThreeLoop.a1SixSetA : ℂ)‖ < η :=
  isFormFactorPair_vertexSetA_pauli_limit_of_nestForm P₀ (setANestForm_of_classes hm hC) hNA hR
    hreg he hm η hη

end QED.ChainProof.SetAPauliAssembly

end
