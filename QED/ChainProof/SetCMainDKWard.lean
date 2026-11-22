/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDK
public import QED.Integration.X0Deg6Ward

/-!
# Set (c), the `δ₃` classes: the longitudinal chain with slashed vertices, Ward identities

Helper level for the open links `QED.ChainProof.SetCMain.DKLimLink`, `DKCovLink`. The chain
`kChainD` of the longitudinal part contracts the element momentum `q` into two vertices; summed
over those indices they become slashed vertices `q̸`, and the photon line `c — d` is
`η_{xy} = (1/i)(Λ² - m_γ²) g_{xy}`:

`kChainD = (1/i)(Λ² - m_γ²) · ∑_z g_{zz} (openChain with γ^μ, q̸, q̸, γ^z, γ^z at π 0, …, π 4)`.

* `ocW`, `kOpen`: the chain with vertex matrices given in the photon labels `π`;
  **`kChainD_eq_kOpen`**;
* `ocW_slot`: linearity in one vertex; **`mul_kOpen_mul`**: covariance of `kOpen` for covariant
  fixed vertices and electron matrices;
* the Ward identities on the open chain: **`openChain_ward_int`** (an internal vertex),
  **`openChain_ward_out`**, **`openChain_ward_in`** (the end vertices, one-sided, leaving the
  matrices `2m - A(p')` and `A(p) - 2m`), and on the longitudinal chain at the vertices
  `π 1`, `π 2`: **`kOpen_ward_int`**, **`kOpen_ward_out`**, **`kOpen_ward_in`**.
-/

@[expose] public section
open Complex Matrix
open QED.Dirac (gamma slash vecAct)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.LimitCovariance QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM
open QED.WickModel (Params)
open QED.TwoLoop.Bridge (electronNumerator extMomenta)

/-! ### The chain in the photon labels -/

/-- The open chain with the vertex matrices `W k` at the vertices `π k`. -/
noncomputable def ocW (π : Equiv.Perm (Fin 5)) (W : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  openChain (fun t => W (π.symm t)) E

/-- The longitudinal chain: `γ^μ` at `π 0`, the fixed matrices `X`, `Y` at `π 1`, `π 2`, and the
photon line `π 3 — π 4` contracted with the metric. -/
noncomputable def kOpen (π : Equiv.Perm (Fin 5)) (μ : Fin 4) (X Y : Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ z, ((Minkowski.metric z z : ℝ) : ℂ) • ocW π ![gamma μ, X, Y, gamma z, gamma z] E

theorem openChain_update_sum (u : Fin 5) (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : Fin 4 → ℂ)
    (M : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    openChain (Function.update G u (∑ x, c x • M x)) E =
      ∑ x, c x • openChain (Function.update G u (M x)) E := by
  fin_cases u <;>
    simp [openChain, Finset.sum_mul, Finset.mul_sum]

/-- **Linearity of `ocW` in one vertex.** -/
theorem ocW_slot (π : Equiv.Perm (Fin 5)) (k : Fin 5) (V : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (W : Fin 4 → Fin 5 → Matrix (Fin 4) (Fin 4) ℂ) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (c : Fin 4 → ℂ) (hW : ∀ x j, j ≠ k → W x j = V j) (hV : V k = ∑ x, c x • W x k) :
    ocW π V E = ∑ x, c x • ocW π (W x) E := by
  have hV' : (fun t => V (π.symm t)) =
      Function.update (fun t => V (π.symm t)) (π k) (∑ x, c x • W x k) := by
    funext t
    by_cases ht : t = π k
    · subst ht; simp [hV]
    · rw [Function.update_of_ne ht]
  have hW' : ∀ x, (fun t => W x (π.symm t)) =
      Function.update (fun t => V (π.symm t)) (π k) (W x k) := fun x => by
    funext t
    by_cases ht : t = π k
    · subst ht; simp
    · rw [Function.update_of_ne ht, hW x _ fun h => ht (by rw [← h]; simp)]
  unfold ocW
  rw [hV', openChain_update_sum]
  simp only [hW']

theorem lowD_eq_lower (q : Fin 4 → ℝ) (u : Fin 4) :
    lowD q u = ((Minkowski.lower q u : ℝ) : ℂ) := by
  simp only [lowD, Minkowski.lower, Minkowski.metric, Fin.sum_univ_four]
  fin_cases u <;> simp

theorem sum_lowD_gamma (q : Fin 4 → ℝ) : ∑ x, lowD q x • gamma x = slash q := by
  simp only [lowD_eq_lower, slash]

theorem pvEta_eq_sum (P : Params) (x y : Fin 4) :
    pvEta P x y = (1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) *
      ∑ z, ((Minkowski.metric z z : ℝ) : ℂ) * (kron z x * kron z y) := by
  rw [Finset.sum_eq_single x (fun z _ hz => by simp [kron, Ne.symm hz]) (by simp)]
  by_cases h : x = y
  · subst h; simp [pvEta, kron]; ring
  · simp [pvEta, kron, Minkowski.metric, h, Ne.symm h]

theorem ocW_kVec (π : Equiv.Perm (Fin 5)) (μ z : Fin 4) (q : Fin 4 → ℝ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ocW π ![gamma μ, slash q, slash q, gamma z, gamma z] E =
      ∑ l : Fin 5 → Fin 4, (kron μ (l (π 0)) * lowD q (l (π 1)) * lowD q (l (π 2)) *
        (kron z (l (π 3)) * kron z (l (π 4)))) • openChain (fun t => gamma (l t)) E := by
  have hv : (![gamma μ, slash q, slash q, gamma z, gamma z] : Fin 5 → _) = fun k =>
      ∑ x, (![kron μ, lowD q, lowD q, kron z, kron z] : Fin 5 → Fin 4 → ℂ) k x • gamma x := by
    funext k
    fin_cases k <;> simp [sum_kron_mul, sum_lowD_gamma]
  rw [hv]
  unfold ocW
  rw [openChain_sum (fun t x => (![kron μ, lowD q, lowD q, kron z, kron z] :
    Fin 5 → Fin 4 → ℂ) (π.symm t) x) gamma E]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [← Equiv.prod_comp π, Fin.prod_univ_five]
  simp only [Equiv.symm_apply_apply]
  simp
  ring

/-- **The longitudinal chain with slashed vertices.** -/
theorem kChainD_eq_kOpen (c : Class5) (P : Params) (σ : Fin 8) (π : Equiv.Perm (Fin 5))
    (p p' : Fin 4 → ℝ) (μ α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kChainD c P σ (π 0) (π 1) (π 2) (π 3) (π 4) p p' μ α β ℓ =
      (((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) • kOpen π μ (slash (elemMom c σ p p' ℓ))
        (slash (elemMom c σ p p' ℓ)) (fun j => electronNumerator P.m
          (QED.Integration.TwoLoop.lineMomentum
            (QED.Integration.TwoLoop.castLoopMatrix (QED.Integration.TwoLoop.class5LoopMatrix c))
            (extMomenta c p p') (Fin.castLE (by omega) j) ℓ))) α β := by
  unfold kChainD kOpen
  simp only [ocW_kVec, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pvEta_eq_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

/-! ### Covariance of the longitudinal chain -/

section Cov

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem kOpen_expand (π : Equiv.Perm (Fin 5)) (X Y : Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (a b c : Fin 4 → ℂ) :
    ocW π ![∑ ν, a ν • gamma ν, X, Y, ∑ ρ, b ρ • gamma ρ, ∑ κ, c κ • gamma κ] E =
      ∑ ν, ∑ ρ, ∑ κ, (a ν * b ρ * c κ) • ocW π ![gamma ν, X, Y, gamma ρ, gamma κ] E := by
  rw [ocW_slot π 0 _ (fun ν => ![gamma ν, X, Y, ∑ ρ, b ρ • gamma ρ, ∑ κ, c κ • gamma κ]) E a
    (fun x j hj => by fin_cases j <;> simp_all) rfl]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [ocW_slot π 3 _ (fun ρ => ![gamma ν, X, Y, gamma ρ, ∑ κ, c κ • gamma κ]) E b
    (fun x j hj => by fin_cases j <;> simp_all) rfl, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [ocW_slot π 4 _ (fun κ => ![gamma ν, X, Y, gamma ρ, gamma κ]) E c
    (fun x j hj => by fin_cases j <;> simp_all) rfl, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [smul_smul, smul_smul, mul_assoc]

/-- **Covariance of the longitudinal chain**: `S kOpen^μ(X₂, Y₂, E₂) T = L^μ_ν kOpen^ν(X, Y, E)`
when `S X₂ T = X`, `S Y₂ T = Y`, `S E₂ T = E`. -/
theorem mul_kOpen_mul (h : IsSpinLift L S T) (π : Equiv.Perm (Fin 5))
    {X Y X₂ Y₂ : Matrix (Fin 4) (Fin 4) ℂ} {E E₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hX : S * X₂ * T = X) (hY : S * Y₂ * T = Y) (hE : ∀ j, S * E₂ j * T = E j) (μ : Fin 4) :
    S * kOpen π μ X₂ Y₂ E₂ * T = vecAct L (fun ν => kOpen π ν X Y E) μ := by
  have h1 : ∀ z, S * ocW π ![gamma μ, X₂, Y₂, gamma z, gamma z] E₂ * T =
      ocW π ![∑ ν, ((L μ ν : ℝ) : ℂ) • gamma ν, X, Y, ∑ ρ, ((L z ρ : ℝ) : ℂ) • gamma ρ,
        ∑ κ, ((L z κ : ℝ) : ℂ) • gamma κ] E := fun z => by
    unfold ocW
    rw [mul_openChain_mul h]
    congr 1
    · funext t
      generalize π.symm t = k
      fin_cases k <;> simp [h.mul_gamma_mul, hX, hY]
    · funext j; exact hE j
  have hg : ∀ ρ κ, ∑ z, ((Minkowski.metric z z : ℝ) : ℂ) * (((L z ρ : ℝ) : ℂ) *
      ((L z κ : ℝ) : ℂ)) = ((Minkowski.metric ρ κ : ℝ) : ℂ) := fun ρ κ => by
    have := h.lorentz_right ρ κ
    have e : ∀ z, ∑ w, L z ρ * L w κ * Minkowski.metric z w =
        Minkowski.metric z z * (L z ρ * L z κ) := fun z => by
      rw [Finset.sum_eq_single z (fun w _ hw => by simp [Minkowski.metric, Ne.symm hw])
        (by simp)]
      ring
    simp only [e] at this
    rw [← this]
    push_cast
    rfl
  set O : Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
    fun ν ρ κ => ocW π ![gamma ν, X, Y, gamma ρ, gamma κ] E with hO
  have step1 : S * kOpen π μ X₂ Y₂ E₂ * T = ∑ z, ∑ ν, ∑ ρ, ∑ κ,
      (((Minkowski.metric z z : ℝ) : ℂ) * (((L μ ν : ℝ) : ℂ) * ((L z ρ : ℝ) : ℂ) *
        ((L z κ : ℝ) : ℂ))) • O ν ρ κ := by
    unfold kOpen
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, h1,
      kOpen_expand, Finset.smul_sum, smul_smul, hO]
  have step2 : vecAct L (fun ν => kOpen π ν X Y E) μ = ∑ ν, ∑ ρ, ∑ κ,
      (((L μ ν : ℝ) : ℂ) * ((Minkowski.metric ρ κ : ℝ) : ℂ)) • O ν ρ κ := by
    unfold vecAct kOpen
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_eq_single ρ (fun κ _ hκ => by simp [Minkowski.metric, Ne.symm hκ])
      (by simp), smul_smul]
  rw [step1, step2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [← Finset.sum_smul, ← hg ρ κ, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun z _ => by ring

end Cov

/-! ### Ward identities on the open chain -/

theorem ward_scalar (M : ℝ) (k : Fin 4 → ℝ) :
    QED.TwoLoop.Bridge.propDenom M 0 k + ((0 : ℝ) : ℂ) * I =
      ((Minkowski.dot k k + M ^ 2 : ℝ) : ℂ) := by
  simp [QED.TwoLoop.Bridge.propDenom]

/-- **The Ward identity at an internal vertex** `j + 1` of the open chain, `q = σ (k₁ - k₂)`
with `k₁` the momentum of the electron line on the left, `k₂` on the right. -/
theorem openChain_ward_int (j : Fin 3) (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (M σ : ℝ) (k₁ k₂ q : Fin 4 → ℝ)
    (hq : q = σ • (k₁ - k₂)) (hG : G j.succ.castSucc = slash q)
    (h1 : E j.succ = electronNumerator M k₁) (h2 : E j.castSucc = electronNumerator M k₂) :
    openChain G E = (σ : ℂ) •
      (((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) •
          openChain (Function.update G j.succ.castSucc 1) (Function.update E j.succ 1) -
        ((Minkowski.dot k₂ k₂ + M ^ 2 : ℝ) : ℂ) •
          openChain (Function.update G j.succ.castSucc 1) (Function.update E j.castSucc 1)) := by
  have hs : slash q = (σ : ℂ) • slash (k₁ - k₂) := by
    rw [hq, QED.Dirac.slash_smul]
  have hW := QED.GradedProof.X0Deg6.electronNumerator_slash_electronNumerator M 0 k₁ k₂
  rw [ward_scalar, ward_scalar] at hW
  have hW2 : ∀ Z : Matrix (Fin 4) (Fin 4) ℂ, electronNumerator M k₁ * (slash (k₁ - k₂) *
      (electronNumerator M k₂ * Z)) = ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) •
        (electronNumerator M k₂ * Z) - ((Minkowski.dot k₂ k₂ + M ^ 2 : ℝ) : ℂ) •
          (electronNumerator M k₁ * Z) := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW]
    simp only [Matrix.sub_mul, Matrix.smul_mul]
  have hW' : ∀ Z : Matrix (Fin 4) (Fin 4) ℂ, electronNumerator M k₁ * (slash q *
      (electronNumerator M k₂ * Z)) = (σ : ℂ) • (((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) •
        (electronNumerator M k₂ * Z) - ((Minkowski.dot k₂ k₂ + M ^ 2 : ℝ) : ℂ) •
          (electronNumerator M k₁ * Z)) := fun Z => by
    rw [hs, Matrix.smul_mul, Matrix.mul_smul, hW2]
  fin_cases j
  · change G 1 = _ at hG; change E 1 = _ at h1; change E 0 = _ at h2
    simp only [openChain, Matrix.mul_assoc]
    simp [hG, h1, h2, hW', Matrix.mul_sub, smul_sub]
  · change G 2 = _ at hG; change E 2 = _ at h1; change E 1 = _ at h2
    simp only [openChain, Matrix.mul_assoc]
    simp [hG, h1, h2, hW', Matrix.mul_sub, smul_sub]
  · change G 3 = _ at hG; change E 3 = _ at h1; change E 2 = _ at h2
    simp only [openChain, Matrix.mul_assoc]
    simp [hG, h1, h2, hW', Matrix.mul_sub, smul_sub]

/-- **The one-sided Ward identity at the outgoing end** (vertex `4`), `q = σ (k₀ - k₁)`, `k₁`
the momentum of the last electron line: `2m - A(k₀)` is left at the vertex. -/
theorem openChain_ward_out (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (M σ : ℝ) (k₀ k₁ q : Fin 4 → ℝ)
    (hq : q = σ • (k₀ - k₁)) (hG : G 4 = slash q) (h1 : E 3 = electronNumerator M k₁) :
    openChain G E = (σ : ℂ) •
      (openChain (Function.update G 4 ((2 * (M : ℂ)) • 1 - electronNumerator M k₀)) E -
        ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) •
          openChain (Function.update G 4 1) (Function.update E 3 1)) := by
  have hs : slash q = (σ : ℂ) • slash (k₀ - k₁) := by
    rw [hq, QED.Dirac.slash_smul]
  have hW := QED.GradedProof.X0Deg6.slash_sub_mul_electronNumerator M 0 k₀ k₁
  rw [ward_scalar] at hW
  have hW' : ∀ Z : Matrix (Fin 4) (Fin 4) ℂ, slash q * (electronNumerator M k₁ * Z) =
      (σ : ℂ) • (((2 * (M : ℂ)) • 1 - electronNumerator M k₀) * (electronNumerator M k₁ * Z) -
        ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) • Z) := fun Z => by
    rw [hs, Matrix.smul_mul, ← Matrix.mul_assoc, hW]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.one_mul]
    congr 1
    abel
  simp only [openChain, Matrix.mul_assoc]
  simp [hG, h1, hW', smul_sub]

/-- **The one-sided Ward identity at the incoming end** (vertex `0`), `q = σ (k₁ - k₀)`, `k₁`
the momentum of the first electron line: `A(k₀) - 2m` is left at the vertex. -/
theorem openChain_ward_in (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (M σ : ℝ) (k₀ k₁ q : Fin 4 → ℝ)
    (hq : q = σ • (k₁ - k₀)) (hG : G 0 = slash q) (h1 : E 0 = electronNumerator M k₁) :
    openChain G E = (σ : ℂ) •
      (openChain (Function.update G 0 (electronNumerator M k₀ - (2 * (M : ℂ)) • 1)) E +
        ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) •
          openChain (Function.update G 0 1) (Function.update E 0 1)) := by
  have hs : slash q = (σ : ℂ) • slash (k₁ - k₀) := by
    rw [hq, QED.Dirac.slash_smul]
  have hW := QED.GradedProof.X0Deg6.electronNumerator_mul_slash_sub M 0 k₀ k₁
  rw [ward_scalar] at hW
  have hW' : electronNumerator M k₁ * slash q = (σ : ℂ) • (electronNumerator M k₁ *
      (electronNumerator M k₀ - (2 * (M : ℂ)) • 1) +
        ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) • 1) := by
    rw [hs, Matrix.mul_smul, hW]
    simp [Matrix.mul_sub]
  simp only [openChain]
  simp [hG, h1, hW', Matrix.mul_add, smul_add, Matrix.mul_assoc]

/-! ### The Ward identities on the longitudinal chain -/

theorem update_comp_symm (π : Equiv.Perm (Fin 5)) (W : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (k : Fin 5) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Function.update (fun t => W (π.symm t)) (π k) X =
      fun t => Function.update W k X (π.symm t) := by
  funext t
  by_cases ht : t = π k
  · subst ht; simp
  · rw [Function.update_of_ne ht, Function.update_of_ne fun h => ht (by rw [← h]; simp)]

variable (π : Equiv.Perm (Fin 5)) (μ : Fin 4) (M σ : ℝ)

/-- **Ward at an internal vertex `π 1 = j + 1`** of the longitudinal chain. -/
theorem kOpen_ward_int (j : Fin 3) (hπ : π 1 = j.succ.castSucc) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k₁ k₂ q : Fin 4 → ℝ) (hq : q = σ • (k₁ - k₂))
    (h1 : E j.succ = electronNumerator M k₁) (h2 : E j.castSucc = electronNumerator M k₂) :
    kOpen π μ (slash q) Y E = (σ : ℂ) •
      (((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) • kOpen π μ 1 Y (Function.update E j.succ 1) -
        ((Minkowski.dot k₂ k₂ + M ^ 2 : ℝ) : ℂ) •
          kOpen π μ 1 Y (Function.update E j.castSucc 1)) := by
  have hz : ∀ z, ocW π ![gamma μ, slash q, Y, gamma z, gamma z] E = (σ : ℂ) •
      (((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) •
          ocW π ![gamma μ, 1, Y, gamma z, gamma z] (Function.update E j.succ 1) -
        ((Minkowski.dot k₂ k₂ + M ^ 2 : ℝ) : ℂ) •
          ocW π ![gamma μ, 1, Y, gamma z, gamma z] (Function.update E j.castSucc 1)) := by
    intro z
    have hu : Function.update (![gamma μ, slash q, Y, gamma z, gamma z] : Fin 5 → _) 1 1 =
        ![gamma μ, 1, Y, gamma z, gamma z] := by
      funext k; fin_cases k <;> rfl
    unfold ocW
    rw [openChain_ward_int j _ E M σ k₁ k₂ q hq (by rw [← hπ]; simp) h1 h2, ← hπ,
      update_comp_symm, hu]
  unfold kOpen
  simp only [hz, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
  congr 1 <;> exact Finset.sum_congr rfl fun z _ => by congr 1; ring

/-- **Ward at the outgoing end `π 1 = 4`** of the longitudinal chain. -/
theorem kOpen_ward_out (hπ : π 1 = 4) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k₀ k₁ q : Fin 4 → ℝ) (hq : q = σ • (k₀ - k₁))
    (h1 : E 3 = electronNumerator M k₁) :
    kOpen π μ (slash q) Y E = (σ : ℂ) •
      (kOpen π μ ((2 * (M : ℂ)) • 1 - electronNumerator M k₀) Y E -
        ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) • kOpen π μ 1 Y (Function.update E 3 1)) := by
  have hz : ∀ z, ocW π ![gamma μ, slash q, Y, gamma z, gamma z] E = (σ : ℂ) •
      (ocW π ![gamma μ, (2 * (M : ℂ)) • 1 - electronNumerator M k₀, Y, gamma z, gamma z] E -
        ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) •
          ocW π ![gamma μ, 1, Y, gamma z, gamma z] (Function.update E 3 1)) := by
    intro z
    have hu : ∀ X, Function.update (![gamma μ, slash q, Y, gamma z, gamma z] : Fin 5 → _) 1 X =
        ![gamma μ, X, Y, gamma z, gamma z] := fun X => by
      funext k; fin_cases k <;> rfl
    unfold ocW
    rw [openChain_ward_out _ E M σ k₀ k₁ q hq (by rw [← hπ]; simp) h1, ← hπ,
      update_comp_symm, update_comp_symm, hu, hu]
  unfold kOpen
  simp only [hz, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
  congr 1 <;> exact Finset.sum_congr rfl fun z _ => by congr 1; ring

/-- **Ward at the incoming end `π 2 = 0`** of the longitudinal chain. -/
theorem kOpen_ward_in (hπ : π 2 = 0) (X : Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k₀ k₁ q : Fin 4 → ℝ) (hq : q = σ • (k₁ - k₀))
    (h1 : E 0 = electronNumerator M k₁) :
    kOpen π μ X (slash q) E = (σ : ℂ) •
      (kOpen π μ X (electronNumerator M k₀ - (2 * (M : ℂ)) • 1) E +
        ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) • kOpen π μ X 1 (Function.update E 0 1)) := by
  have hz : ∀ z, ocW π ![gamma μ, X, slash q, gamma z, gamma z] E = (σ : ℂ) •
      (ocW π ![gamma μ, X, electronNumerator M k₀ - (2 * (M : ℂ)) • 1, gamma z, gamma z] E +
        ((Minkowski.dot k₁ k₁ + M ^ 2 : ℝ) : ℂ) •
          ocW π ![gamma μ, X, 1, gamma z, gamma z] (Function.update E 0 1)) := by
    intro z
    have hu : ∀ Y, Function.update (![gamma μ, X, slash q, gamma z, gamma z] : Fin 5 → _) 2 Y =
        ![gamma μ, X, Y, gamma z, gamma z] := fun Y => by
      funext k; fin_cases k <;> rfl
    unfold ocW
    rw [openChain_ward_in _ E M σ k₀ k₁ q hq (by rw [← hπ]; simp) h1, ← hπ,
      update_comp_symm, update_comp_symm, hu, hu]
  unfold kOpen
  simp only [hz, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
  congr 1 <;> exact Finset.sum_congr rfl fun z _ => by congr 1; ring

end QED.ChainProof.SetCMain

end
