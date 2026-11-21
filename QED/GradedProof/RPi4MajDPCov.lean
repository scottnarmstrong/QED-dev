/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajDRed
public import QED.GradedProof.RPi4InstClass
public import QED.GradedProof.RPi4Cov
public import QED.TwoLoop.ReflCovarianceParam
public import QED.GradedProof.WI2Merge

/-!
# (R-Π₄) step L10, two loops: covariance of a photon-mass density and the null half of `MajDRay`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV). The bound
`QED.GradedProof.RPi4.MajDRay` has a ray half (at `k'(s) = tiltVec √s s`) and a null half (at
`tiltVec √s 0`). The null vectors `tiltVec c 0` all have square `0`, so for a reflection-covariant
tensor the entry `(2, 3)` at `tiltVec c 0` is `c²` times the entry at `tiltVec 1 0`
(`tcov_tilt_null`, through `QED.GradedProof.RPi4.projS_eq_tilt`). The null half is then the
heavy-photon bound `‖t D(t, k₀)‖ ≤ C` at the single null vector `k₀ = tiltVec 1 0`, which
`QED.GradedProof.RPi4.HeavyRate` gives.

* `paramAtV_map`, `paramAtV_qsum`: the parametric integrand under a Lorentz map of the external
  data, and its linearity in the quartic;
* **`pairDens_reflect`**, `tcov_pairDens`: the photon-mass density of a covariant numerator family
  (`QED.GradedProof.VP2.TCov2`) is reflection covariant (`QED.GradedProof.VP2.TCov`), given the
  integrability of its entries;
* `majDP_tcov_zero`, `.._add`, `.._const_mul`, `.._sum`, `.._congr`: closure of `TCov`;
* `tcov_tilt_null`: the entry `(2, 3)` along the null tilted vectors;
* `MajDRayRay`, `MajDRayNull`: the two halves of `MajDRay` (`majDRay_of_halves`), the ray half
  closed under finite linear combinations;
* **`majDRayNull_of_tcov`**: covariance at every `u ≥ 1` and the heavy-photon rate at
  `tiltVec 1 0` give the null half.
-/

@[expose] public section

open Complex MeasureTheory Matrix
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.GradedProof.WI2 (ehat ehat_qsum)
open QED.Integration.TwoLoop QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)

variable {m : ℕ}

/-! ### The parametric integrand under a Lorentz map -/

section Map

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **The integrand `paramAtV` at the external data `L pᵢ`** is the integrand at `pᵢ` with the
numerator `ℓ ↦ Q(L ℓ)`. -/
theorem paramAtV_map (h : IsSpinLift L S T) (n : ℕ) (Q : LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ) (v : ℝ) :
    paramAtV n Q α (fun i => L *ᵥ p i) z v = paramAtV n (lmap (blockL L) Q) α p z v := by
  have hX : actC (blockL L) (loopComp (-loopShift α p z)) =
      loopComp (-loopShift α (fun i => L *ᵥ p i) z) := by
    rw [actC_blockL_loopComp, loopAct_neg, loopShift_map]
  have h1 : (lmap (blockL L) Q).evalC (loopComp (-loopShift α p z)) =
      Q.evalC (loopComp (-loopShift α (fun i => L *ᵥ p i) z)) := by
    rw [evalC_lmap, hX]
  have h2 : (lmap (blockL L) Q).contractTwo (symanzikMatrix α z) (loopComp (-loopShift α p z)) =
      Q.contractTwo (symanzikMatrix α z) (loopComp (-loopShift α (fun i => L *ᵥ p i) z)) := by
    rw [contractTwo_lmap _ _ (symanzikMatrix_transpose _ _), hX,
      blockL_conj_loopMetricInv h.lorentz_left]
    rfl
  have h3 : (lmap (blockL L) Q).contractFour (symanzikMatrix α z) =
      Q.contractFour (symanzikMatrix α z) := by
    rw [contractFour_lmap, blockL_conj_loopMetricInv h.lorentz_left]
    rfl
  simp only [paramAtV, ehat, h1, h2, h3]

end Map

/-- `paramAtV` is linear in the quartic. -/
theorem paramAtV_qsum (n : ℕ) {ι : Type*} (s : Finset ι) (w : ι → ℂ) (Q : ι → LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → ℝ) (v : ℝ) :
    paramAtV n (qsum s w Q) α p z v = ∑ i ∈ s, w i * paramAtV n (Q i) α p z v := by
  simp only [paramAtV, ehat_qsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### Covariance of the photon-mass density -/

section Density

variable {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

/-- The integrand of an entry of `pairDens` at the momentum `k`. -/
noncomputable def pairDensIntegrand (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (y : Fin m → ℝ) : ℂ :=
  (simplexPoint y γ : ℂ) *
    paramAtV (m + 1) (numQuartic fun ℓ => N k ℓ μ ν) α (fun l => cs l • k) (simplexPoint y)
      (symanzikV α (fun l => cs l • k) (Function.update M γ 0) (simplexPoint y) +
        simplexPoint y γ * u)

theorem pairDens_eq_integrand (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ)
    (M : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    pairDens (fun ℓ => N k ℓ μ ν) α (fun l => cs l • k) M γ u =
      -((π : ℂ) ^ 4) * ∫ y in simplexSet m, pairDensIntegrand N α cs M γ u k μ ν y :=
  rfl

/-- **The photon-mass density of a covariant numerator family is reflection covariant**, at a
momentum `k` where the entries of its integrand are integrable. -/
theorem pairDens_reflect (hN : TCov2 N)
    (hpoly : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν)
    (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) (k : Fin 4 → ℝ)
    (hint : ∀ μ ν, IntegrableOn (pairDensIntegrand N α cs M γ u k μ ν) (simplexSet m)) :
    (fun μ ν => pairDens (fun ℓ => N (QED.Dirac.reflect a k) ℓ μ ν) α
        (fun l => cs l • QED.Dirac.reflect a k) M γ u) =
      rAct a fun μ ν => pairDens (fun ℓ => N k ℓ μ ν) α (fun l => cs l • k) M γ u := by
  classical
  set L := QED.Dirac.reflectMatrix a with hLdef
  have hL := isSpinLift_reflect ha
  have hp : (fun l => cs l • QED.Dirac.reflect a k) = fun l => L *ᵥ (cs l • k) := by
    funext l
    rw [Matrix.mulVec_smul, hLdef, QED.Dirac.reflectMatrix_mulVec]
  have he : ∀ μ' ν', (numQuartic fun ℓ => N k ℓ μ' ν').eval = fun ℓ => N k ℓ μ' ν' :=
    fun μ' ν' => eval_numQuartic (hpoly k μ' ν')
  funext μ ν
  set w : Fin 4 × Fin 4 → ℂ := fun kl => ((L μ kl.1 : ℝ) : ℂ) * ((L ν kl.2 : ℝ) : ℂ) with hw
  set Qs := qsum Finset.univ w fun kl => numQuartic fun ℓ => N k ℓ kl.1 kl.2 with hQs
  have hev : (lmap (blockL L) (numQuartic fun ℓ => N (QED.Dirac.reflect a k) ℓ μ ν)).eval =
      Qs.eval := by
    funext ℓ
    rw [eval_lmap_blockL, eval_numQuartic (hpoly _ μ ν), hQs, eval_qsum]
    simp only [he]
    rw [hN.reflect ha (QED.Dirac.reflect a k) (loopAct L ℓ) μ ν, QED.Dirac.reflect_reflect ha,
      TCov2.loopAct_loopAct ha, Fintype.sum_prod_type]
  have hval : ∀ y : Fin m → ℝ,
      pairDensIntegrand N α cs M γ u (QED.Dirac.reflect a k) μ ν y =
        ∑ kl : Fin 4 × Fin 4, w kl * pairDensIntegrand N α cs M γ u k kl.1 kl.2 y := by
    intro y
    simp only [pairDensIntegrand]
    rw [hp, symanzikV_map hL, paramAtV_map hL, paramAtV_congr hev, hQs, paramAtV_qsum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [pairDens_eq_integrand (N := N) α cs M γ u (QED.Dirac.reflect a k) μ ν]
  simp only [hval]
  rw [integral_finsetSum _ fun kl _ => (hint kl.1 kl.2).const_mul (w kl)]
  simp only [integral_const_mul, rAct, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pairDens_eq_integrand (N := N) α cs M γ u k i j, hw]
  ring

/-- **Covariance of the photon-mass density** on a region where the entries are integrable. -/
theorem tcov_pairDens (hN : TCov2 N)
    (hpoly : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν)
    (α : Fin (m + 1) → Fin 2 → ℝ) (cs : Fin (m + 1) → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) {T : ℝ}
    (hint : ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ μ ν,
      IntegrableOn (pairDensIntegrand N α cs M γ u k μ ν) (simplexSet m)) :
    TCov T fun k μ ν => pairDens (fun ℓ => N k ℓ μ ν) α (fun l => cs l • k) M γ u :=
  fun _ ha k hk => pairDens_reflect hN hpoly α cs M γ u ha k (hint k hk)

end Density

/-! ### Closure of covariance -/

section Closure

variable {T : ℝ} {W W' : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem majDP_tcov_zero : TCov T fun _ _ _ => 0 := fun a _ _ _ => by
  funext μ ν
  simp [rAct]

theorem majDP_tcov_add (h : TCov T W) (h' : TCov T W') :
    TCov T fun k μ ν => W k μ ν + W' k μ ν := fun a ha k hk => by
  funext μ ν
  beta_reduce
  rw [h a ha k hk, h' a ha k hk]
  simp only [rAct, mul_add, Finset.sum_add_distrib]

theorem majDP_tcov_const_mul (h : TCov T W) (r : ℂ) : TCov T fun k μ ν => r * W k μ ν :=
  fun a ha k hk => by
    funext μ ν
    beta_reduce
    rw [h a ha k hk]
    simp only [rAct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem majDP_tcov_sum {ι : Type*} (t : Finset ι) {W : ι → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ t, TCov T (W i)) : TCov T fun k μ ν => ∑ i ∈ t, W i k μ ν := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (majDP_tcov_zero : TCov T fun _ _ _ => 0)
  | insert b t hb ih =>
    simp only [Finset.sum_insert hb]
    exact majDP_tcov_add (h b (Finset.mem_insert_self b t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem majDP_tcov_congr (h : TCov T W) (e : ∀ k μ ν, W k μ ν = W' k μ ν) : TCov T W' := by
  have : W = W' := funext fun k => funext fun μ => funext fun ν => e k μ ν
  exact this ▸ h

/-- **The entry `(2, 3)` along the null tilted vectors**: `W(tiltVec c 0)²³ = c² W(tiltVec 1 0)²³`
for a covariant `W` (`T ≠ 0`, `c > 0`). -/
theorem tcov_tilt_null (hcov : TCov T W) (hT : T ≠ 0) {c : ℝ} (hc : 0 < c) :
    W (tiltVec c 0) 2 3 = ((c ^ 2 : ℝ) : ℂ) * W (tiltVec 1 0) 2 3 := by
  have hT2 : -T ^ 2 < 0 := by
    have := pow_pos (abs_pos.2 hT) 2
    rw [sq_abs] at this
    linarith
  have h1 := projS_eq_tilt hcov hc hT2 (by positivity : (0 : ℝ) < 2 * c ^ 2)
  have h2 := projS_eq_tilt hcov one_pos hT2 (by norm_num : (0 : ℝ) < 2 * 1 ^ 2)
  rw [h1] at h2
  have hc2 : ((c ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have h3 : W (tiltVec c 0) 2 3 = ((c ^ 2 : ℝ) : ℂ) * (W (tiltVec c 0) 2 3 / ((c ^ 2 : ℝ) : ℂ)) :=
    by field_simp
  rw [h3]
  congr 1
  have h4 := congrArg Neg.neg h2
  simp only [neg_div, neg_neg, one_pow, ofReal_one, div_one] at h4
  exact h4

end Closure

/-! ### The two halves of `MajDRay` -/

/-- **The ray half of `MajDRay`**: `‖u G(u, k'(s))‖ ≤ C s` at `k'(s) = tiltVec √s s`. -/
def MajDRayRay (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) s)‖ ≤ C * s

/-- **The null half of `MajDRay`**: `‖u G(u, tiltVec √s 0)‖ ≤ C s`. -/
def MajDRayNull (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
    ‖(u : ℂ) * G u (tiltVec (Real.sqrt s) 0)‖ ≤ C * s

theorem majDRay_of_halves {G : ℝ → (Fin 4 → ℝ) → ℂ} (hR : MajDRayRay G) (hN : MajDRayNull G) :
    MajDRay G := by
  obtain ⟨C, hC⟩ := hR
  obtain ⟨D, hD⟩ := hN
  refine ⟨max C D, fun s hs u hu => ⟨?_, ?_⟩⟩
  · exact (hC s hs u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · exact (hD s hs u hu).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))

namespace MajDRayRay

variable {G H : ℝ → (Fin 4 → ℝ) → ℂ}

theorem zero : MajDRayRay fun _ _ => 0 :=
  ⟨0, fun s _ u _ => by simp⟩

theorem add (hG : MajDRayRay G) (hH : MajDRayRay H) : MajDRayRay fun u k => G u k + H u k := by
  obtain ⟨C, hC⟩ := hG
  obtain ⟨D, hD⟩ := hH
  refine ⟨C + D, fun s hs u hu => ?_⟩
  rw [mul_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC s hs u hu) (hD s hs u hu))

theorem const_mul (hG : MajDRayRay G) (r : ℂ) : MajDRayRay fun u k => r * G u k := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨‖r‖ * C, fun s hs u hu => ?_⟩
  rw [mul_left_comm, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC s hs u hu) (norm_nonneg _)

theorem sum {ι : Type*} (t : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ t, MajDRayRay (G i)) : MajDRayRay fun u k => ∑ i ∈ t, G i u k := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (zero : MajDRayRay fun _ _ => 0)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : MajDRayRay G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
      G u (tiltVec (Real.sqrt s) s) = H u (tiltVec (Real.sqrt s) s)) : MajDRayRay H := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun s hs u hu => by rw [← e s hs u hu]; exact hC s hs u hu⟩

end MajDRayRay

/-- **The null half from covariance and the heavy-photon rate at one null vector.** If the
tensor `W u` is reflection covariant for every `u ≥ 1` (`T ≠ 0`) and its entry `(2, 3)` has the
heavy-photon rate at `tiltVec 1 0` (a constant segment), the entry `(2, 3)` has the null half. -/
theorem majDRayNull_of_tcov {T : ℝ} (hT : T ≠ 0) {W : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hcov : ∀ u : ℝ, 1 ≤ u → TCov T (W u))
    (hH : HeavyRate (tiltVec 1 0) 0 fun t k => W t k 2 3) :
    MajDRayNull fun u k => W u k 2 3 := by
  obtain ⟨C, L, hC⟩ := hH
  refine ⟨‖L 0‖ + |C|, fun s hs u hu => ?_⟩
  have hk : lineK (tiltVec 1 0) 0 0 = tiltVec 1 0 := by simp [lineK]
  have h0 := hC 0 (by norm_num) u hu
  rw [hk] at h0
  have hr : u ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
  have hb : ‖(u : ℂ) * W u (tiltVec 1 0) 2 3‖ ≤ ‖L 0‖ + |C| := by
    calc ‖(u : ℂ) * W u (tiltVec 1 0) 2 3‖
        = ‖((u : ℂ) * W u (tiltVec 1 0) 2 3 - L 0) + L 0‖ := by ring_nf
      _ ≤ ‖(u : ℂ) * W u (tiltVec 1 0) 2 3 - L 0‖ + ‖L 0‖ := norm_add_le _ _
      _ ≤ |C| * 1 + ‖L 0‖ := by
          gcongr
          exact h0.trans (mul_le_mul (le_abs_self C) hr (by positivity) (abs_nonneg C))
      _ = ‖L 0‖ + |C| := by ring
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.2 (by linarith)
  have e := tcov_tilt_null (hcov u hu) hT hs0
  rw [Real.sq_sqrt (by linarith)] at e
  have hsn : ‖((s : ℝ) : ℂ)‖ = s := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  calc ‖(u : ℂ) * W u (tiltVec (Real.sqrt s) 0) 2 3‖
      = ‖((s : ℝ) : ℂ)‖ * ‖(u : ℂ) * W u (tiltVec 1 0) 2 3‖ := by
        rw [e, ← norm_mul]; ring_nf
    _ ≤ s * (‖L 0‖ + |C|) := by rw [hsn]; exact mul_le_mul_of_nonneg_left hb (by linarith)
    _ = (‖L 0‖ + |C|) * s := by ring

end QED.GradedProof.RPi4

end
