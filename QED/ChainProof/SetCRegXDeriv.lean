/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegX

/-!
# Derivative of the crossed integrand

Differentiate the two resolvents of the crossed integrand in
`QED/ChainProof/SetCKRegX.lean` with respect to the second photon's squared mass.
-/

public section

open Filter Topology

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitXGraph

/-- Each differentiated resolvent acquires a factor of the second photon weight over (V). -/
theorem hasDerivAt_crossedAt_right (a b : ℝ) (z : Fin 5 → ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : ∀ j, 0 < z j) :
    let U := gXU (z 0) (z 1) (z 2) (z 3) (z 4)
    let V := gXE (z 0) (z 1) (z 2) (z 3) (z 4) + a * z 3 + b * z 4
    let F := z 1 * gPsi1 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 6)
    let G := z 1 * gPsi2 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 5)
    HasDerivAt (fun t => crossedAt a t z) ((z 4 / V) * (-2 * (F / V ^ 2) + G / V)) b := by
  dsimp only
  let E := gXE (z 0) (z 1) (z 2) (z 3) (z 4)
  let U := gXU (z 0) (z 1) (z 2) (z 3) (z 4)
  let F := z 1 * gPsi1 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 6)
  let G := z 1 * gPsi2 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 5)
  let D (t : ℝ) := E + a * z 3 + t * z 4
  have hp : 0 < D b :=
    add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (gXE_pos (hz 0) (hz 1) (hz 2) (hz 3) (hz 4))
        (mul_nonneg ha (hz 3).le)) (mul_nonneg hb (hz 4).le)
  have h : HasDerivAt D (z 4) b := by
    simpa only [D, one_mul, id_eq] using
      ((hasDerivAt_id b).mul_const (z 4)).const_add (E + a * z 3)
  have hf : (fun t => crossedAt a t z) = fun t => F * (D t)⁻¹ ^ 2 - G * (D t)⁻¹ := by
    funext t
    rw [crossedAt_eq_inv]
    change z 1 * (_ * (D t)⁻¹ ^ 2 - _ * (D t)⁻¹) = _
    unfold F G
    ring
  rw [hf]
  have ht : HasDerivAt (fun t => F * (D t)⁻¹ ^ 2 - G * (D t)⁻¹)
      (F * (2 * (D b)⁻¹ * (-z 4 / (D b) ^ 2)) - G * (-z 4 / (D b) ^ 2)) b := by
    have hpi : ((fun t => F * (D t)⁻¹ ^ 2) - fun t => G * (D t)⁻¹) =
        (fun t => F * (D t)⁻¹ ^ 2 - G * (D t)⁻¹) := by
      funext t
      rw [Pi.sub_apply]
    rw [← hpi]
    simpa only [Pi.inv_apply, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
      using (((h.inv hp.ne').pow 2).const_mul F).sub ((h.inv hp.ne').const_mul G)
  convert ht using 1
  change z 4 / D b * (-2 * (F / (D b) ^ 2) + G / D b) = _
  generalize hV : D b = V at hp ⊢
  field_simp [hp.ne']
  ring

/-- The mass-scaled derivative tends to zero pointwise, uniformly in the sense that
the first squared mass may vary arbitrarily in the nonnegative half-line. -/
theorem tendsto_mul_deriv_crossedAt_right {ι : Type*} {l : Filter ι} {a b : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 ≤ a i) (hb : Tendsto b l atTop)
    {z : Fin 5 → ℝ} (hz : ∀ j, 0 < z j) :
    Tendsto (fun i => b i * deriv (fun t => crossedAt (a i) t z) (b i)) l (𝓝 0) := by
  let E := gXE (z 0) (z 1) (z 2) (z 3) (z 4)
  let U := gXU (z 0) (z 1) (z 2) (z 3) (z 4)
  let F := z 1 * gPsi1 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 6)
  let G := z 1 * gPsi2 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 5)
  let V i := E + a i * z 3 + b i * z 4
  have hE : 0 < E := gXE_pos (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  have hV₀ : ∀ᶠ i in l, b i * z 4 ≤ V i := ha.mono fun i hi =>
    le_add_of_nonneg_left (add_nonneg hE.le (mul_nonneg hi (hz 3).le))
  have hV := tendsto_atTop_mono' l hV₀ (hb.atTop_mul_const (hz 4))
  have hinv := tendsto_inv_atTop_zero.comp hV
  have hlim : Tendsto (fun i => -2 * (F / V i ^ 2) + G / V i) l (𝓝 0) := by
    simp only [div_eq_mul_inv]
    simpa using ((tendsto_const_nhds (x := (-2 : ℝ))).mul
      ((tendsto_const_nhds (x := F)).mul (hinv.pow 2))).add
      ((tendsto_const_nhds (x := G)).mul hinv)
  refine squeeze_zero_norm' ?_ (by simpa only [norm_zero] using hlim.norm)
  filter_upwards [ha, hb.eventually_ge_atTop 0, hV₀] with i hai hbi hle
  have hp : 0 < V i := add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg hE (mul_nonneg hai (hz 3).le)) (mul_nonneg hbi (hz 4).le)
  rw [(hasDerivAt_crossedAt_right (a i) (b i) z hai hbi hz).deriv]
  change ‖b i * (z 4 / V i * (-2 * (F / V i ^ 2) + G / V i))‖ ≤ _
  rw [← mul_assoc, ← mul_div_assoc, norm_mul, Real.norm_of_nonneg
    (div_nonneg (mul_nonneg hbi (hz 4).le) hp.le)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hp).mpr hle)

end QED.ChainProof.SetCK

end
