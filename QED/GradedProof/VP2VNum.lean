/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VTriple

/-!
# The numerators of the classes `VA`, `VB`, `VC`

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. The numerator of
one fermion loop of mass `m` in a class with vertex matrices `A_{μνρσ}` is
`vNum A m k ℓ μ ν = ∑_{ρσ} kV_{ρσ} vT(A_{μνρσ}, m, y(k, ℓ))`.

* `tcov_of`: a loop trace with the internal photon indices contracted by `kV` is covariant, given
  its two cyclic forms (`Tr[P γ^σ Q γ^ρ]` and `Tr[γ^μ A γ^ν B]`); `tcov_vNumA`, `tcov_vNumB`,
  `tcov_vNumC` for the three classes;
* `vNum_eq` (even quadratic in `m²`), `isLoopPoly_vNum`, `isLoopPoly_vNumE2`, `rb_vNum`,
  `isLoopPoly_vNum_k`: the hypotheses of `QED.GradedProof.VP2.vpj_gBlock`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Mat}

/-! ### Covariance of contracted loop traces -/

theorem kV_pair (h : IsSpinLift L S T) (e mγ Λ : ℝ) (u v : Fin 4) :
    ∑ x, ∑ y, kV e mγ Λ x y * (((L x u : ℝ) : ℂ) * ((L y v : ℝ) : ℂ)) = kV e mγ Λ u v := by
  have hr := h.lorentz_right u v
  have hc : ((∑ a, ∑ b, L a u * L b v * Minkowski.metric a b : ℝ) : ℂ) =
      ((Minkowski.metric u v : ℝ) : ℂ) := by rw [hr]
  simp only [kV, pvPhotonNum, ofReal_mul, ofReal_sum] at hc ⊢
  rw [← hc]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **The contracted internal photon indices are invariant.** -/
theorem kV_trace_pair (h : IsSpinLift L S T) (e mγ Λ : ℝ) (P Q : Mat) :
    ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * (P * (S * Dirac.gamma σ * T) * Q * (S * Dirac.gamma ρ * T)).trace =
      ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * (P * Dirac.gamma σ * Q * Dirac.gamma ρ).trace := by
  simp only [h.mul_gamma_mul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  have e1 : ∀ ρ σ : Fin 4, ∑ w, ∑ z, kV e mγ Λ ρ σ * (((L ρ w : ℝ) : ℂ) * (((L σ z : ℝ) : ℂ) *
      (P * Dirac.gamma z * Q * Dirac.gamma w).trace)) =
      ∑ w, ∑ z, kV e mγ Λ ρ σ * (((L ρ w : ℝ) : ℂ) * ((L σ z : ℝ) : ℂ)) *
        (P * Dirac.gamma z * Q * Dirac.gamma w).trace := fun ρ σ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => e1 ρ σ, sum_block2]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  rw [← kV_pair h e mγ Λ w z, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by rw [Finset.sum_mul]

/-- **The free indices transform by `L`.** -/
theorem trace_pair_free (h : IsSpinLift L S T) (A B : Mat) (a b : Fin 4) :
    ((S * Dirac.gamma a * T) * A * (S * Dirac.gamma b * T) * B).trace =
      upperAct L (fun a' b' => (Dirac.gamma a' * A * Dirac.gamma b' * B).trace) a b := by
  simp only [h.mul_gamma_mul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, upperAct]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **A contracted loop trace with two cyclic forms is covariant.** -/
theorem tcov_of (h : IsSpinLift L S T) (e mγ Λ : ℝ) {X : Type*}
    (tr : Mat → Mat → Mat → Mat → X → ℂ)
    (hrot : ∀ Ga Gb N, ∃ P Q : Mat, ∀ Gρ Gσ, tr Ga Gb Gρ Gσ N = (P * Gσ * Q * Gρ).trace)
    (hfree : ∀ Gρ Gσ N, ∃ A B : Mat, ∀ Ga Gb, tr Ga Gb Gρ Gσ N = (Ga * A * Gb * B).trace)
    (N : X) (a b : Fin 4) :
    ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * tr (S * Dirac.gamma a * T) (S * Dirac.gamma b * T)
        (S * Dirac.gamma ρ * T) (S * Dirac.gamma σ * T) N =
      upperAct L (fun a b => ∑ ρ, ∑ σ, kV e mγ Λ ρ σ *
        tr (Dirac.gamma a) (Dirac.gamma b) (Dirac.gamma ρ) (Dirac.gamma σ) N) a b := by
  obtain ⟨P, Q, hPQ⟩ := hrot (S * Dirac.gamma a * T) (S * Dirac.gamma b * T) N
  simp only [hPQ]
  rw [kV_trace_pair h]
  simp only [← hPQ]
  have hf : ∀ ρ σ : Fin 4, tr (S * Dirac.gamma a * T) (S * Dirac.gamma b * T) (Dirac.gamma ρ)
      (Dirac.gamma σ) N = upperAct L (fun a' b' => tr (Dirac.gamma a') (Dirac.gamma b')
        (Dirac.gamma ρ) (Dirac.gamma σ) N) a b := fun ρ σ => by
    obtain ⟨A, B, hAB⟩ := hfree (Dirac.gamma ρ) (Dirac.gamma σ) N
    simp only [hAB]
    exact trace_pair_free h A B a b
  simp only [hf, upperAct, Finset.mul_sum]
  rw [sum_block2]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### The numerators -/

/-- The numerator of one fermion loop of mass `m` in a class with vertex matrices `A`. -/
noncomputable def vNum (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (m : ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * vT (A a b ρ σ) m (fun l => fm base (ppc c k) l ℓ)

/-- The trace of a loop with vertex matrices `G` and numerators `N`. -/
noncomputable def tr4 (G N : Fin 4 → Mat) : ℂ :=
  (G 0 * N 0 * G 1 * N 1 * G 2 * N 2 * G 3 * N 3).trace

theorem tr4_conj (G N : Fin 4 → Mat) :
    tr4 G (fun l => T * N l * S) = tr4 (fun l => S * G l * T) N := by
  unfold tr4
  rw [show G 0 * (T * N 0 * S) * G 1 * (T * N 1 * S) * G 2 * (T * N 2 * S) * G 3 * (T * N 3 * S) =
      (G 0 * (T * N 0 * S) * G 1 * (T * N 1 * S) * G 2 * (T * N 2 * S) * G 3 * (T * N 3)) * S by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem fm_loopAct (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ) (l : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    fm base (ppc c (L *ᵥ k)) l (loopAct L ℓ) = L *ᵥ fm base (ppc c k) l ℓ :=
  lineMomentum_loopAct_smul L _ c _ k ℓ

/-- **Covariance of a class numerator** from the two cyclic forms of its trace. -/
theorem tcov_vNum (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
    (tr : Mat → Mat → Mat → Mat → (Fin 4 → Mat) → ℂ)
    (hA : ∀ (S T : Mat) (a b ρ σ : Fin 4) (N : Fin 4 → Mat),
      tr4 (fun l => S * A a b ρ σ l * T) N = tr (S * Dirac.gamma a * T) (S * Dirac.gamma b * T)
        (S * Dirac.gamma ρ * T) (S * Dirac.gamma σ * T) N)
    (hA1 : ∀ (a b ρ σ : Fin 4) (N : Fin 4 → Mat),
      tr4 (A a b ρ σ) N = tr (Dirac.gamma a) (Dirac.gamma b) (Dirac.gamma ρ) (Dirac.gamma σ) N)
    (hrot : ∀ Ga Gb N, ∃ P Q : Mat, ∀ Gρ Gσ, tr Ga Gb Gρ Gσ N = (P * Gσ * Q * Gρ).trace)
    (hfree : ∀ Gρ Gσ N, ∃ A B : Mat, ∀ Ga Gb, tr Ga Gb Gρ Gσ N = (Ga * A * Gb * B).trace)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (m : ℝ) :
    TCov2 (vNum e mγ Λ A base c m) := by
  intro L S T h k ℓ
  funext a b
  have e1 : ∀ ρ σ, vT (A a b ρ σ) m (fun l => fm base (ppc c (L *ᵥ k)) l (loopAct L ℓ)) =
      tr (S * Dirac.gamma a * T) (S * Dirac.gamma b * T) (S * Dirac.gamma ρ * T)
        (S * Dirac.gamma σ * T) (fun l => electronNumerator m (fm base (ppc c k) l ℓ)) :=
    fun ρ σ => by
      simp only [fm_loopAct, ← hA]
      rw [← tr4_conj]
      simp only [← electronNumerator_mulVec h]
      rfl
  simp only [vNum, e1]
  rw [tcov_of h e mγ Λ tr hrot hfree]
  simp only [← hA1]
  rfl

/-! ### Degrees, bounds and the mass expansion -/

section Props

variable (e mγ Λ : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Mat)
  (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

/-- The coefficient of `m²` in `vNum`. -/
noncomputable def vNumE2 (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * vE2 (A a b ρ σ) (fun l => fm base (ppc c k) l ℓ)

/-- The coefficient of `m⁰` in `vNum`. -/
noncomputable def vNumE0 (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * vE0 (A a b ρ σ) (fun l => fm base (ppc c k) l ℓ)

/-- The coefficient of `m⁴` in `vNum`. -/
noncomputable def vNumE4 (_k : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  ∑ ρ, ∑ σ, kV e mγ Λ ρ σ * vE4 (A a b ρ σ)

theorem vNum_eq (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l)) (m : ℝ) (k : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    vNum e mγ Λ A base c m k ℓ a b = vNumE0 e mγ Λ A base c k ℓ a b +
      (m : ℂ) ^ 2 * vNumE2 e mγ Λ A base c k ℓ a b + ((m : ℂ) ^ 2) ^ 2 * vNumE4 e mγ Λ A k a b := by
  simp only [vNum, vNumE0, vNumE2, vNumE4, vT_eq (hA a b _ _), Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isLoopPoly_vNum (m : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => vNum e mγ Λ A base c m k ℓ a b :=
  IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.sum _ fun σ _ =>
    (isLoopPoly_vT base (ppc c k) (A a b ρ σ) m).const_mul _

theorem isLoopPoly_vNumE2 (k : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 2 2 fun ℓ => vNumE2 e mγ Λ A base c k ℓ a b :=
  IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.sum _ fun σ _ =>
    (isLoopPoly_vE2 base (ppc c k) (A a b ρ σ)).const_mul _

/-- The bound of a class numerator on the four fermion lines of a shape. -/
theorem rb_vNum {n : ℕ} (sh : Fin (n + 1) → Fin 5) (e4 : Fin 4 → Fin (n + 1))
    (he : ∀ l, sh (e4 l) = l.castSucc) (h01 : e4 0 ≠ e4 1) (h02 : e4 0 ≠ e4 2)
    (h03 : e4 0 ≠ e4 3) (h12 : e4 1 ≠ e4 2) (h13 : e4 1 ≠ e4 3) (h23 : e4 2 ≠ e4 3) (m : ℝ)
    (k : Fin 4 → ℝ) (a b : Fin 4) :
    RefinedBound (castLoopMatrix fun r => base (sh r)) {e4 0, e4 1, e4 2, e4 3} 4
      fun ℓ => vNum e mγ Λ A base c m k ℓ a b :=
  RefinedBound.sum _ fun ρ _ => RefinedBound.sum _ fun σ _ =>
    (rb_vT base (ppc c k) sh e4 he h01 h02 h03 h12 h13 h23 (A a b ρ σ) m).const_mul _

theorem isLoopPoly_vT_aff {n : ℕ} (G : Fin 4 → Mat) (m : ℝ)
    (Y : Fin 4 → (Fin n → Fin 4 → ℝ) → Fin 4 → ℝ) (hY : ∀ l, IsLoopAffine (Y l)) :
    IsLoopPoly n 4 fun x => vT G m (fun l => Y l x) := by
  have N := fun l => (hY l).isLoopPolyMat_electronNumerator m
  have h := ((((((((IsLoopPolyMat.const (G 0)).mul (N 0)).mul (IsLoopPolyMat.const (G 1))).mul
    (N 1)).mul (IsLoopPolyMat.const (G 2))).mul (N 2)).mul (IsLoopPolyMat.const (G 3))).mul
    (N 3)).trace
  exact h.mono (by norm_num)

theorem isLoopPoly_vNum_k (m : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 1 4 fun y => vNum e mγ Λ A base c m (y 0) ℓ a b :=
  IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.sum _ fun σ _ =>
    (isLoopPoly_vT_aff (A a b ρ σ) m _ fun l =>
      isLoopAffine_lineMomentum_k base c l.castSucc ℓ).const_mul _

end Props

/-! ### The three classes -/

/-- The loop trace of `VA` with vertex matrices `G_μ, G_ν, G_ρ, G_σ`. -/
noncomputable def trVA (Ga Gb Gρ Gσ : Mat) (N : Fin 4 → Mat) : ℂ :=
  (Ga * N 0 * Gσ * N 1 * Gρ * N 2 * Gb * N 3).trace

/-- The loop trace of `VB`. -/
noncomputable def trVB (Ga Gb Gρ Gσ : Mat) (N : Fin 4 → Mat) : ℂ :=
  (Ga * N 0 * Gσ * N 1 * Gb * N 2 * Gρ * N 3).trace

/-- The loop trace of `VC`. -/
noncomputable def trVC (Ga Gb Gρ Gσ : Mat) (N : Fin 4 → Mat) : ℂ :=
  (Ga * N 0 * Gb * N 1 * Gσ * N 2 * Gρ * N 3).trace

theorem tcov_vNumA (e mγ Λ : ℝ) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (m : ℝ) :
    TCov2 (vNum e mγ Λ aVA base c m) := by
  refine tcov_vNum e mγ Λ aVA trVA (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun Ga Gb N => ⟨N 2 * Gb * N 3 * Ga * N 0, N 1, fun Gρ Gσ => ?_⟩)
    (fun Gρ Gσ N => ⟨N 0 * Gσ * N 1 * Gρ * N 2, N 3, fun Ga Gb => ?_⟩) base c m
  · unfold trVA
    rw [show Ga * N 0 * Gσ * N 1 * Gρ * N 2 * Gb * N 3 =
      (Ga * N 0 * Gσ * N 1 * Gρ) * (N 2 * Gb * N 3) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  · unfold trVA
    simp only [Matrix.mul_assoc]

theorem tcov_vNumB (e mγ Λ : ℝ) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (m : ℝ) :
    TCov2 (vNum e mγ Λ aVB base c m) := by
  refine tcov_vNum e mγ Λ aVB trVB (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun Ga Gb N => ⟨N 3 * Ga * N 0, N 1 * Gb * N 2, fun Gρ Gσ => ?_⟩)
    (fun Gρ Gσ N => ⟨N 0 * Gσ * N 1, N 2 * Gρ * N 3, fun Ga Gb => ?_⟩) base c m
  · unfold trVB
    rw [show Ga * N 0 * Gσ * N 1 * Gb * N 2 * Gρ * N 3 =
      (Ga * N 0 * Gσ * N 1 * Gb * N 2 * Gρ) * N 3 by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  · unfold trVB
    simp only [Matrix.mul_assoc]

theorem tcov_vNumC (e mγ Λ : ℝ) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (m : ℝ) :
    TCov2 (vNum e mγ Λ aVC base c m) := by
  refine tcov_vNum e mγ Λ aVC trVC (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun Ga Gb N => ⟨N 3 * Ga * N 0 * Gb * N 1, N 2, fun Gρ Gσ => ?_⟩)
    (fun Gρ Gσ N => ⟨N 0, N 1 * Gσ * N 2 * Gρ * N 3, fun Ga Gb => ?_⟩) base c m
  · unfold trVC
    rw [show Ga * N 0 * Gb * N 1 * Gσ * N 2 * Gρ * N 3 =
      (Ga * N 0 * Gb * N 1 * Gσ * N 2 * Gρ) * N 3 by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  · unfold trVC
    simp only [Matrix.mul_assoc]

end QED.GradedProof.VP2

end
