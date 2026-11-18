/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitMirror

/-!
# Charge conjugation of the class limits and the mirror identity

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). The mirror identity
`QED.OneLoop.IsMirrorSymmetric` at `(p', p)` (charge conjugation followed by the reflection `R_K`
in `K = p' + p`) splits into two steps:

1. **Charge conjugation at fixed `ε`, then `ε → 0⁺`.** For a pair of classes `(c, c')` whose
   values are exchanged by reversing the open line (`IsChargeConjPair c c'`, e.g. `C₊ ↔ C₋`,
   `QED.TwoLoop.LimitMirror.contractionValue₂_Cm_cc`), the limits `W_c(p', p)` of the values
   (`classLimit`) satisfy `C W_c(p', p)ᵀ C = -W_{c'}(-p, -p')`
   (`chargeConj_classLimit_of_pair`). The point `(-p, -p')` has negative energies; the limits of
   the open-line classes exist there (`QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_open` does
   not use positive energies).
2. **The reflection.** For on-shell `p, p'` with `q² > 0`, `R_K p' = -p` and `R_K p = -p'`
   (`QED.OneLoop.reflect_add_self`), so `(-p, -p') = (R_K p', R_K p)`. If the limits are covariant
   under `R_K` between these two points (`IsReflCovariantAt`), step 1 gives the mirror identity
   (`isMirrorSymmetric_of_chargeConj`).

The reflection `R_K` reverses the time direction (`K` is timelike), so it is not a symmetry of the
energy-first prescription at `ε > 0`; its covariance is a property of the `ε → 0⁺` limits, through
their parametric form (obligation O2-20), and is kept here as the explicit hypothesis
`IsReflCovariantAt`.

## Main statements

* `chargeConj_classLimit_of_pair`, `chargeConj_classLimit_of_pair'`: step 1, in both directions.
* `isMirrorSymmetric_of_chargeConj`: step 2.
* `isReflCovariantAt_of_transform`: `IsReflCovariantAt` from covariance in transformation form,
  `W(R_K p', R_K p) = R_K S_K W(p', p) S_K⁻¹`.
* `isMirrorSymmetric_classLimit_self`, `isMirrorSymmetric_classLimit_pair`: a self-conjugate
  open-line class, and a charge-conjugate pair, are mirror symmetric given the `R_K` covariance
  of their limits.
* `isMirrorSymmetric_classLimit_Cp_add_Cm`: **the pair `C₊ + C₋` is mirror symmetric**, given the
  `R_K` covariance of the two class limits.
-/

@[expose] public section

open Matrix Complex Filter Topology

namespace QED.TwoLoop.LimitMirror

open QED.WickModel QED.TwoLoop.Enumeration QED.Dirac QED.OneLoop

/-! ### Charge conjugation of matrices -/

/-- Entrywise, `(C Xᵀ C)_{ab} = s(a) s(b) X_{p(b) p(a)}`. -/
theorem chargeConj_transpose_apply (X : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    (chargeConj * Xᵀ * chargeConj) a b = ccSign a * ccSign b * X (ccIdx b) (ccIdx a) := by
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, chargeConj_apply, ccIdx, ccSign] <;> ring_nf <;>
    simp [Complex.I_sq]

/-- `X ↦ C Xᵀ C` is an involution. -/
theorem chargeConj_transpose_involutive (X : Matrix (Fin 4) (Fin 4) ℂ) :
    chargeConj * (chargeConj * Xᵀ * chargeConj)ᵀ * chargeConj = X := by
  ext a b
  rw [chargeConj_transpose_apply, chargeConj_transpose_apply, ccIdx_ccIdx, ccIdx_ccIdx,
    ccSign_ccIdx, ccSign_ccIdx]
  linear_combination X a b * (ccSign_mul_self a * ccSign b * ccSign b + ccSign_mul_self b)

/-! ### Pairs of classes exchanged by charge conjugation -/

/-- The values (T₁₀) of the classes `c` and `c'` are exchanged by charge conjugation: at every
parameter set and under momentum conservation, the value of `c'` with the external data
`(-p_in, -p_out, k)` and spinor indices `(p(b), p(a))` is `-s(a) s(b)` times the value of `c` with
`(p_out, p_in, k)` and `(a, b)`. -/
def IsChargeConjPair (c c' : Class5) : Prop :=
  ∀ (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ), pOut 0 = pIn 0 + kIn 0 →
    ∀ αOut βIn μ : Fin 1 → Fin 4,
      contractionValue₂ P c'.rep (fun i => -pIn i) (fun i => -pOut i) kIn
          (fun i => ccIdx (βIn i)) (fun i => ccIdx (αOut i)) μ =
        -(ccSign (αOut 0) * ccSign (βIn 0)) * contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ

theorem isChargeConjPair_Cp_Cm : IsChargeConjPair .Cp .Cm :=
  fun P _ _ _ hmom αOut βIn μ => contractionValue₂_Cm_cc P hmom αOut βIn μ

/-- The value (T₁₀) of class `c` at the prescription `ε`, at `(p', p)` with photon momentum
`p' - p` and indices `(μ, a, b)`. -/
noncomputable def classValue (c : Class5) (P : Params) (p' p : Fin 4 → ℝ) (μ a b : Fin 4)
    (ε : ℝ) : ℂ :=
  contractionValue₂ { P with ε := ε } c.rep (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (fun _ => a) (fun _ => b) (fun _ => μ)

/-- The `ε → 0⁺` limit of the value of class `c` at `(p', p)`, as a vertex `W_c(p', p)^μ_{ab}`. -/
noncomputable def classLimit (c : Class5) (P : Params) (p' p : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun a b => limUnder (𝓝[>] 0) (classValue c P p' p μ a b)

/-- The values of a class converge as `ε → 0⁺` at `(p', p)`, for all indices. -/
def HasClassLimit (c : Class5) (P : Params) (p' p : Fin 4 → ℝ) : Prop :=
  ∀ μ a b, ∃ L, Tendsto (classValue c P p' p μ a b) (𝓝[>] 0) (𝓝 L)

theorem tendsto_classLimit {c : Class5} {P : Params} {p' p : Fin 4 → ℝ}
    (h : HasClassLimit c P p' p) (μ a b : Fin 4) :
    Tendsto (classValue c P p' p μ a b) (𝓝[>] 0) (𝓝 (classLimit c P p' p μ a b)) := by
  obtain ⟨L, hL⟩ := h μ a b
  exact tendsto_nhds_limUnder ⟨L, hL⟩

/-- **The open-line classes have limits at every on-shell pair with `q² ≥ 0`**, of either energy
sign. -/
theorem hasClassLimit_open {c : Class5} (hc : c ∈ ClassIntegrable.openClasses) (P : Params)
    (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) : HasClassLimit c P p' p := fun μ a b => by
  obtain ⟨Q, -, -, h⟩ := ClassLimit.tendsto_contractionValue₂_open hc P hm hmγ hΛ
    (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) (by simp) hp hp' hq
    (fun _ => a) (fun _ => b) (fun _ => μ)
  exact ⟨_, h⟩

/-- **Step 1: charge conjugation of the limits.** For a charge-conjugate pair `(c, c')` whose values
converge at `(p', p)` and at `(-p, -p')`: `C W_c(p', p)ᵀ C = -W_{c'}(-p, -p')`. -/
theorem chargeConj_classLimit_of_pair {c c' : Class5} (hcc : IsChargeConjPair c c') (P : Params)
    {p' p : Fin 4 → ℝ} (h : HasClassLimit c P p' p) (h' : HasClassLimit c' P (-p) (-p'))
    (μ : Fin 4) :
    chargeConj * (classLimit c P p' p μ)ᵀ * chargeConj = -classLimit c' P (-p) (-p') μ := by
  ext a b
  rw [chargeConj_transpose_apply, Matrix.neg_apply]
  have hk : (fun _ : Fin 1 => -p - -p') = fun _ => p' - p := by
    funext _
    abel
  have e : classValue c' P (-p) (-p') μ a b = fun ε =>
      -(ccSign (ccIdx b) * ccSign (ccIdx a)) * classValue c P p' p μ (ccIdx b) (ccIdx a) ε := by
    funext ε
    have := hcc { P with ε := ε } (fun _ => p') (fun _ => p) (fun _ => p' - p) (by simp)
      (fun _ => ccIdx b) (fun _ => ccIdx a) (fun _ => μ)
    simp only [ccIdx_ccIdx] at this
    simp only [classValue, hk]
    exact this
  have hlim := (tendsto_classLimit h μ (ccIdx b) (ccIdx a)).const_mul
    (-(ccSign (ccIdx b) * ccSign (ccIdx a)))
  rw [← e] at hlim
  have huniq := tendsto_nhds_unique hlim (tendsto_classLimit h' μ a b)
  simp only [classLimit, Matrix.of_apply] at huniq ⊢
  rw [← huniq, ccSign_ccIdx, ccSign_ccIdx]
  ring

/-- **Step 1, the other direction**: `C W_{c'}(p', p)ᵀ C = -W_c(-p, -p')`, given the limits of `c`
at `(-p, -p')` and of `c'` at `(p', p)`. -/
theorem chargeConj_classLimit_of_pair' {c c' : Class5} (hcc : IsChargeConjPair c c')
    (P : Params) {p' p : Fin 4 → ℝ} (h : HasClassLimit c P (-p) (-p'))
    (h' : HasClassLimit c' P p' p) (μ : Fin 4) :
    chargeConj * (classLimit c' P p' p μ)ᵀ * chargeConj = -classLimit c P (-p) (-p') μ := by
  have h'' : HasClassLimit c' P (-(-p')) (-(-p)) := by simpa using h'
  have := chargeConj_classLimit_of_pair hcc P h h'' μ
  simp only [neg_neg] at this
  rw [show classLimit c' P p' p μ = -(chargeConj * (classLimit c P (-p) (-p') μ)ᵀ * chargeConj) by
    rw [this, neg_neg], Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul,
    chargeConj_transpose_involutive]

/-! ### The reflection -/

/-- **Covariance under the reflection `R_K`, `K = p' + p`, between `(p', p)` and
`(R_K p', R_K p)`**: `S_K W(R_K p', R_K p)^μ S_K⁻¹ = (R_K)^μ_ν W(p', p)^ν`. -/
def IsReflCovariantAt (W : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (p' p : Fin 4 → ℝ) : Prop :=
  ∀ μ, reflSpin (p' + p) * W (reflect (p' + p) p') (reflect (p' + p) p) μ *
      (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p)) =
    vecAct (reflectMatrix (p' + p)) (W p' p) μ

/-- **The covariance of a vertex function under `R_K` in transformation form gives
`IsReflCovariantAt`**: if `W(R_K p', R_K p)^μ = (R_K)^μ_ν S_K W(p', p)^ν S_K⁻¹` (the covariance of
`W` under the Lorentz map `R_K` with its spinor lift `S_K = K̸Γ`), then
`S_K W(R_K p', R_K p) S_K⁻¹ = R_K W(p', p)`, since `S_K² = (K·K)·1`. -/
theorem isReflCovariantAt_of_transform
    {W : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {p' p : Fin 4 → ℝ}
    (hK : Minkowski.dot (p' + p) (p' + p) ≠ 0)
    (h : ∀ μ, W (reflect (p' + p) p') (reflect (p' + p) p) μ =
      vecAct (reflectMatrix (p' + p)) (fun ν => reflSpin (p' + p) * W p' p ν *
        (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p))) μ) :
    IsReflCovariantAt W p' p := by
  intro μ
  set S := reflSpin (p' + p)
  set T := (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p))
  have hST : S * T = 1 := reflSpin_mul_inv hK
  have hTS : T * S = 1 := inv_mul_reflSpin hK
  have hSS : S * S * (T * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S T T, hST, Matrix.one_mul, hST]
  have hc : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, S * (S * X * T) * T = X := fun X => by
    have e1 : S * S = ((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ) • 1 :=
      reflSpin_mul_reflSpin (p' + p)
    have e2 : T * T = ((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • 1 := by
      rw [show T * T = T * (S * T) * T from by rw [hST, Matrix.mul_one]]
      rw [show T * (S * T) * T = (T * S) * (T * T) from by simp only [Matrix.mul_assoc]]
      rw [hTS, Matrix.one_mul]
      have : S * S * (T * T) = 1 := hSS
      rw [e1, Matrix.smul_mul, Matrix.one_mul] at this
      have hk : ((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hK
      rw [← this, smul_smul, inv_mul_cancel₀ hk, one_smul]
    calc S * (S * X * T) * T = (S * S) * X * (T * T) := by simp only [Matrix.mul_assoc]
      _ = X := by
        have hk : ((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hK
        rw [e1, e2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
          inv_mul_cancel₀ hk, one_smul]
  rw [h μ, mul_vecAct_mul]
  simp only [hc]

/-- **Step 2: charge conjugation plus covariance under `R_K` give the mirror identity.** If
`C W(p', p)ᵀ C = -W'` and `S_K W' S_K⁻¹ = R_K W(p', p)`, then `W(p', p)` is mirror symmetric. -/
theorem isMirrorSymmetric_of_chargeConj {p' p : Fin 4 → ℝ}
    {W W' : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hC : ∀ μ, chargeConj * (W μ)ᵀ * chargeConj = -W' μ)
    (hR : ∀ μ, reflSpin (p' + p) * W' μ *
        (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p)) =
      vecAct (reflectMatrix (p' + p)) W μ) :
    IsMirrorSymmetric p' p W := by
  intro μ
  rw [hC, Matrix.mul_neg, Matrix.neg_mul, hR]

theorem vecAct_add' (L : Matrix (Fin 4) (Fin 4) ℝ) (A B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : vecAct L (A + B) μ = vecAct L A μ + vecAct L B μ :=
  vecAct_add L A B μ

/-- The mirror identity is additive. -/
theorem isMirrorSymmetric_add {p' p : Fin 4 → ℝ} {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsMirrorSymmetric p' p V) (hW : IsMirrorSymmetric p' p W) :
    IsMirrorSymmetric p' p (V + W) := by
  intro μ
  rw [Pi.add_apply, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.add_mul, hV μ, hW μ, vecAct_add', neg_add]

section OnShell

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ}
  (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
  (hq : 0 < Minkowski.dot (p' - p) (p' - p))
include hm hmγ hΛ hp' hp hq

theorem hasClassLimit_open_neg {c : Class5} (hc : c ∈ ClassIntegrable.openClasses) :
    HasClassLimit c P (-p) (-p') := by
  have hp'n : Minkowski.dot (-p') (-p') = -P.m ^ 2 := by simpa [Minkowski.dot] using hp'
  have hpn : Minkowski.dot (-p) (-p) = -P.m ^ 2 := by simpa [Minkowski.dot] using hp
  have hqn : 0 ≤ Minkowski.dot (-p - -p') (-p - -p') := by
    rw [show -p - -p' = p' - p by abel]
    exact hq.le
  exact hasClassLimit_open hc P hm hmγ hΛ hpn hp'n hqn

/-- **A self-conjugate open-line class is mirror symmetric**, given the covariance of its limit
under the reflection `R_K`. For `m, m_γ, Λ > 0` and on-shell `p, p'` with `q² > 0` (of any energy
sign). -/
theorem isMirrorSymmetric_classLimit_self {c : Class5} (hc : c ∈ ClassIntegrable.openClasses)
    (hcc : IsChargeConjPair c c) (hcov : IsReflCovariantAt (classLimit c P) p' p) :
    IsMirrorSymmetric p' p (classLimit c P p' p) := by
  obtain ⟨hRp, hRp', -⟩ := reflect_add_self hp' hp hq
  refine isMirrorSymmetric_of_chargeConj (W' := classLimit c P (-p) (-p'))
    (fun μ => chargeConj_classLimit_of_pair hcc P (hasClassLimit_open hc P hm hmγ hΛ hp' hp hq.le)
      (hasClassLimit_open_neg P hm hmγ hΛ hp' hp hq hc) μ) (fun μ => ?_)
  have h1 := hcov μ
  rwa [hRp, hRp'] at h1

/-- **A charge-conjugate pair of open-line classes is mirror symmetric**, given the covariance of
the two class limits under the reflection `R_K`. -/
theorem isMirrorSymmetric_classLimit_pair {c c' : Class5} (hc : c ∈ ClassIntegrable.openClasses)
    (hc' : c' ∈ ClassIntegrable.openClasses) (hcc : IsChargeConjPair c c')
    (hcov : IsReflCovariantAt (classLimit c P) p' p)
    (hcov' : IsReflCovariantAt (classLimit c' P) p' p) :
    IsMirrorSymmetric p' p (classLimit c P p' p + classLimit c' P p' p) := by
  obtain ⟨hRp, hRp', -⟩ := reflect_add_self hp' hp hq
  have h := hasClassLimit_open hc P hm hmγ hΛ hp' hp hq.le
  have h' := hasClassLimit_open hc' P hm hmγ hΛ hp' hp hq.le
  have hn := hasClassLimit_open_neg P hm hmγ hΛ hp' hp hq hc
  have hn' := hasClassLimit_open_neg P hm hmγ hΛ hp' hp hq hc'
  refine isMirrorSymmetric_of_chargeConj (W' := classLimit c' P (-p) (-p') +
    classLimit c P (-p) (-p')) (fun μ => ?_) (fun μ => ?_)
  · rw [Pi.add_apply, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
      chargeConj_classLimit_of_pair hcc P h hn' μ, chargeConj_classLimit_of_pair' hcc P hn h' μ,
      Pi.add_apply, neg_add]
  · have h1 := hcov μ
    have h2 := hcov' μ
    rw [hRp, hRp'] at h1 h2
    rw [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, h1, h2, vecAct_add', add_comm]

/-- **The corner pair `C₊ + C₋` is mirror symmetric**, given the covariance of the two class
limits under the reflection `R_K` (`IsReflCovariantAt`, a consequence of their covariance,
obligation O2-20). For `m, m_γ, Λ > 0` and on-shell `p, p'` with `q² > 0` (of any energy sign);
`W_c(p', p)` is the `ε → 0⁺` limit of the value of class `c` (`classLimit`). -/
theorem isMirrorSymmetric_classLimit_Cp_add_Cm
    (hcovP : IsReflCovariantAt (classLimit .Cp P) p' p)
    (hcovM : IsReflCovariantAt (classLimit .Cm P) p' p) :
    IsMirrorSymmetric p' p (classLimit .Cp P p' p + classLimit .Cm P p' p) :=
  isMirrorSymmetric_classLimit_pair P hm hmγ hΛ hp' hp hq (by decide) (by decide)
    isChargeConjPair_Cp_Cm hcovP hcovM

end OnShell

end QED.TwoLoop.LimitMirror

end
