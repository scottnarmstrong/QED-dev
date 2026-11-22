/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKSecond
public import QED.ChainProof.SetCRegKKShell
public import QED.ChainProof.SetCRegKKGe

/-!
# Set (c): the Pauli assembly of the longitudinal integrand

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSumGe` (`QED/ChainProof/SetCRegKKGe.lean`).
After the second Ward step (`QED.ChainProof.SetCRegDisp.kkLimX_sum_second`) the sum of the
pointwise limits of the twelve longitudinal integrands is
`kCst (Q(5, 1, 0) + Q(4, 1, 3) + Q(9, 2, 0) + E) - kCst (Z₀ + Z₆ + Z₁₀)`. The end terms `E` and
the terms `Zᵢ` carry `2m - A(p')` next to the outgoing spinor or `A(p) - 2m` next to the incoming
one, so their Pauli-weighted sums vanish on shell, pointwise in the loop momenta
(`QED/ChainProof/SetCRegKKShell.lean`); by linearity of the pointwise limit so do those of their
limits. Hence the sum `kkSumP` of the twelve Pauli limits is the Pauli limit of the three doubly
pinched values alone, for every spectral mass `T ≥ 4` (where `t = √(m² T)/2 ≥ m`).

* `jointEnergyFirstIntegral_wsum`, **`kkLimX_wsum_eq_zero`**: linearity of the pointwise limit
  over a finite combination whose integrand vanishes;
* `pauliSum_kkLimX_kkT_eq_zero`: a term whose numerator has zero Pauli-weighted sum;
* `pauliSum_kkEnd_out`, `pauliSum_kkEnd_inn`, `pauliSum_kkZ`, `pauliSum_kkEndSum`: the end terms;
* **`pauliSum_sum_kkLimX_kkH`**: the Pauli-weighted sum of the twelve pointwise limits is `kCst`
  times that of `Q(5, 1, 0) + Q(4, 1, 3) + Q(9, 2, 0)`;
* `kkQS`, **`tendsto_kkQS`**: `kkSumP` is the Pauli limit of `kCst` times the three doubly pinched
  values along the curve.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit

/-! ### Linearity of the pointwise limit -/

/-- The joint integral of a finite combination of integrable integrands. -/
theorem jointEnergyFirstIntegral_wsum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (G : ι → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (h : ∀ j ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable 2 (G j)) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ => ∑ j ∈ s, c j * G j ℓ) ∧
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => ∑ j ∈ s, c j * G j ℓ) =
        ∑ j ∈ s, c j * QED.TwoLoop.jointEnergyFirstIntegral 2 (G j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨⟨fun _ => by simp, by simp⟩, ?_⟩
    unfold QED.TwoLoop.jointEnergyFirstIntegral
    simp
  | insert a s ha ih =>
    obtain ⟨hi, he⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have ha' := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul (c a)
      (h a (Finset.mem_insert_self a s))
    simp only [Finset.sum_insert ha]
    refine ⟨QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add ha' hi, ?_⟩
    rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add ha' hi, he,
      QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]

/-- **A finite combination of pointwise limits with vanishing integrand is zero.** -/
theorem kkLimX_wsum_eq_zero {ι : Type*} (s : Finset ι) (c : ι → ℂ) {w : ℝ → ℂ}
    {H : ι → ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} (hH : ∀ j ∈ s, KKVal w (H j)) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (h0 : ∀ ε : ℝ, 0 < ε → ∀ ℓ, ∑ j ∈ s, c j * H j ε x ℓ = 0) :
    ∑ j ∈ s, c j * kkLimX (H j) x = 0 := by
  have ht : Tendsto (fun ε => ∑ j ∈ s, c j * QED.TwoLoop.jointEnergyFirstIntegral 2 (H j ε x))
      (𝓝[>] 0) (𝓝 (∑ j ∈ s, c j * kkLimX (H j) x)) :=
    tendsto_finsetSum _ fun j hj => ((hH j hj).tendsto_limX hx).const_mul _
  have hz : Tendsto (fun ε => ∑ j ∈ s, c j * QED.TwoLoop.jointEnergyFirstIntegral 2 (H j ε x))
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [← (jointEnergyFirstIntegral_wsum s c (fun j => H j ε x)
      fun j hj => (hH j hj).2.2.2.1 ε hε x hx).2]
    simp only [h0 ε hε]
    unfold QED.TwoLoop.jointEnergyFirstIntegral
    simp
  exact tendsto_nhds_unique ht hz

/-! ### The terms with zero Pauli weight -/

section Terms

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t x : ℝ}
  (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  (ht : R.m ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1)
include hm hγ hγΛ hp hp' hq ht hx

/-- **A term whose numerator has zero Pauli-weighted sum** has a pointwise limit with zero
Pauli-weighted sum. -/
theorem pauliSum_kkLimX_kkT_eq_zero {k : ℕ} (hk : 7 ≤ k) {ι : Fin (k + 1) → Fin 10}
    {X Y : KSlot} {K : Finset (Fin 4)} (hXY : Disjoint (kSlotS X) (kSlotS Y))
    (hd : kSlotD X + kSlotD Y + K.card ≤ 4) (hok : KKOk i ι (kSet X Y K))
    (h0 : ∀ μ ℓ, ∑ a, ∑ b, pauliWt R.m p' p μ a b * kNi i R p p' X Y K μ ℓ a b = 0) :
    ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 *
      kkLimX (kkT i R p p' t ι fun ℓ => kNi i R p p' X Y K j.1 ℓ j.2.1 j.2.2) x = 0 := by
  refine kkLimX_wsum_eq_zero Finset.univ _ (w := fun _ => 1) (fun j _ =>
    kkVal_kkT hm hγ hγΛ hp hp' hq ht (integrableOn_const (by simp)) hk hok
      (isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ j.1 hd j.2.1 j.2.2)
      (refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ j.1 hXY hd j.2.1 j.2.2)) hx fun ε _ ℓ => ?_
  have hs : ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * kNi i R p p' X Y K j.1 ℓ j.2.1 j.2.2 =
      0 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun μ _ => by rw [Fintype.sum_prod_type]; exact h0 μ ℓ
  simp only [kkT]
  calc _ = (∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * kNi i R p p' X Y K j.1 ℓ j.2.1 j.2.2) *
        kkDen i R p p' ι ε ℓ * kkSpec i p p' t ε x ℓ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by rw [hs, zero_mul, zero_mul]

omit hm hγ hγΛ hp hp' hq ht hx in
theorem pauliSum_sub (f g : Idx → ℂ) (c : ℂ) :
    ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * (f j - c * g j) =
      ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f j -
        c * ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * g j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **An end term at the outgoing other end** has zero Pauli-weighted sum. -/
theorem pauliSum_kkEnd_out {d : Fin 4} (hO : kOthD i = 4) (he : EOk i d .out) :
    ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * kkEnd i R p p' t d .out j.1 j.2.1 j.2.2 x =
      0 := by
  have hd : kSlotD .one + kSlotD .out + (Finset.univ.erase d).card ≤ 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp [kSlotD]
  have h0 : ∀ μ ℓ, ∑ a, ∑ b, pauliWt R.m p' p μ a b *
      kNi i R p p' .one .out (Finset.univ.erase d) μ ℓ a b = 0 := fun μ ℓ =>
    pauliWt_sum_kNum_Y_out _ _ _ μ ℓ ((kPermD_apply i).2.2.1.trans hO) hp' _
  simp only [kkEnd]
  rw [pauliSum_sub,
    pauliSum_kkLimX_kkT_eq_zero hm hγ hγΛ hp hp' hq ht hx le_rfl (by simp [kSlotS]) hd he.1 h0,
    pauliSum_kkLimX_kkT_eq_zero hm hγ hγΛ hp hp' hq ht hx (by norm_num) (by simp [kSlotS]) hd
      he.2 h0]
  ring

/-- **An end term at the incoming other end** has zero Pauli-weighted sum. -/
theorem pauliSum_kkEnd_inn {d : Fin 4} (hO : kOthD i = 0) (he : EOk i d .inn) :
    ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * kkEnd i R p p' t d .inn j.1 j.2.1 j.2.2 x =
      0 := by
  have hd : kSlotD .one + kSlotD .inn + (Finset.univ.erase d).card ≤ 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp [kSlotD]
  have h0 : ∀ μ ℓ, ∑ a, ∑ b, pauliWt R.m p' p μ a b *
      kNi i R p p' .one .inn (Finset.univ.erase d) μ ℓ a b = 0 := fun μ ℓ =>
    pauliWt_sum_kNum_inn _ _ _ μ ℓ ((kPermD_apply i).2.2.1.trans hO) hp _
  simp only [kkEnd]
  rw [pauliSum_sub,
    pauliSum_kkLimX_kkT_eq_zero hm hγ hγΛ hp hp' hq ht hx le_rfl (by simp [kSlotS]) hd he.1 h0,
    pauliSum_kkLimX_kkT_eq_zero hm hγ hγΛ hp hp' hq ht hx (by norm_num) (by simp [kSlotS]) hd
      he.2 h0]
  ring

/-- **The end terms of a class with the Ward identities at both ends** have zero Pauli-weighted
sum. -/
theorem pauliSum_kkZ (hW : kWardD i = 4) (hO : kOthD i = 0) :
    ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * kkZ i R p p' t j.1 j.2.1 j.2.2 x = 0 := by
  obtain ⟨hall, h1d, h1d9, h2d, h2d9, -⟩ := kkOk_ext i hW
  have hW' : kPermD i 1 = 4 := (kPermD_apply i).2.1.trans hW
  have hO' : kPermD i 2 = 0 := (kPermD_apply i).2.2.1.trans hO
  have z₀ := fun {k : ℕ} (hk : 7 ≤ k) {ι : Fin (k + 1) → Fin 10} (hok : KKOk i ι (kSetE 0)) =>
    pauliSum_kkLimX_kkT_eq_zero hm hγ hγΛ hp hp' hq ht hx hk (X := .out) (Y := .inn)
      (K := Finset.univ) (by simp [kSlotS]) (by decide) hok
      fun μ ℓ => pauliWt_sum_kNum_out _ _ _ μ ℓ hW' hp' _
  have z₁ := fun {k : ℕ} (hk : 7 ≤ k) {ι : Fin (k + 1) → Fin 10} (hok : KKOk i ι (kSetE 1)) =>
    pauliSum_kkLimX_kkT_eq_zero hm hγ hγΛ hp hp' hq ht hx hk (X := .out) (Y := .one)
      (K := Finset.univ.erase 0) (by simp [kSlotS]) (by decide) hok
      fun μ ℓ => pauliWt_sum_kNum_out _ _ _ μ ℓ hW' hp' _
  have z₂ := fun {k : ℕ} (hk : 7 ≤ k) {ι : Fin (k + 1) → Fin 10} (hok : KKOk i ι (kSetE 2)) =>
    pauliSum_kkLimX_kkT_eq_zero hm hγ hγΛ hp hp' hq ht hx hk (X := .one) (Y := .inn)
      (K := Finset.univ.erase 3) (by simp [kSlotS]) (by decide) hok
      fun μ ℓ => pauliWt_sum_kNum_inn _ _ _ μ ℓ hO' hp _
  have e : ∀ f₁ g₁ f₂ g₂ f₃ g₃ : Idx → ℂ, ∀ c : ℂ,
      ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 *
        ((f₁ j - c * g₁ j) + (f₂ j - c * g₂ j) + -1 * (f₃ j - c * g₃ j)) =
      ((∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₁ j -
          c * ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * g₁ j) +
        (∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₂ j -
          c * ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * g₂ j)) +
        -1 * (∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₃ j -
          c * ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * g₃ j) := fun _ _ _ _ _ _ c => by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [kkZ]
  rw [e, z₀ (by norm_num) (hall 0).2, z₀ (by norm_num) (hall 0).1,
    z₁ le_rfl h1d9, z₁ (by norm_num) h1d, z₂ le_rfl h2d9, z₂ (by norm_num) h2d]
  ring

/-- **The eight end terms of the second Ward step** have zero Pauli-weighted sum. -/
theorem pauliSum_kkEndSum :
    ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * kkEndSum R p p' t j.1 j.2.1 j.2.2 x = 0 := by
  have o₂ := pauliSum_kkEnd_out hm hγ hγΛ hp hp' hq ht hx (i := 2) (d := 0) rfl
    (by decide +kernel)
  have n₃ := pauliSum_kkEnd_inn hm hγ hγΛ hp hp' hq ht hx (i := 3) (d := 3) rfl
    (by decide +kernel)
  have o₄₁ := pauliSum_kkEnd_out hm hγ hγΛ hp hp' hq ht hx (i := 4) (d := 1) rfl
    (by decide +kernel)
  have o₄₀ := pauliSum_kkEnd_out hm hγ hγΛ hp hp' hq ht hx (i := 4) (d := 0) rfl
    (by decide +kernel)
  have n₅ := pauliSum_kkEnd_inn hm hγ hγΛ hp hp' hq ht hx (i := 5) (d := 1) rfl
    (by decide +kernel)
  have o₈ := pauliSum_kkEnd_out hm hγ hγΛ hp hp' hq ht hx (i := 8) (d := 2) rfl
    (by decide +kernel)
  have n₉₃ := pauliSum_kkEnd_inn hm hγ hγΛ hp hp' hq ht hx (i := 9) (d := 3) rfl
    (by decide +kernel)
  have n₉₂ := pauliSum_kkEnd_inn hm hγ hγΛ hp hp' hq ht hx (i := 9) (d := 2) rfl
    (by decide +kernel)
  have e : ∀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Idx → ℂ,
      ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 *
        (f₁ j - f₂ j - f₃ j + f₄ j + f₅ j - f₆ j - f₇ j + f₈ j) =
      ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₁ j -
        ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₂ j -
        ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₃ j +
        ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₄ j +
        ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₅ j -
        ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₆ j -
        ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₇ j +
        ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * f₈ j := fun _ _ _ _ _ _ _ _ => by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [kkEndSum]
  rw [e, o₂, n₃, o₄₁, o₄₀, n₅, o₈, n₉₃, n₉₂]
  ring

/-- **The Pauli-weighted sum of the twelve pointwise limits** is `kCst` times that of the three
surviving doubly pinched values `Q(5, 1, 0) + Q(4, 1, 3) + Q(9, 2, 0)`. -/
theorem pauliSum_sum_kkLimX_kkH :
    ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 *
        ∑ i, kkLimX (kkH i R p p' t j.1 j.2.1 j.2.2) x =
      kCst R * ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 *
        (kkQ 5 R p p' t 1 0 j.1 j.2.1 j.2.2 x + kkQ 4 R p p' t 1 3 j.1 j.2.1 j.2.2 x +
          kkQ 9 R p p' t 2 0 j.1 j.2.1 j.2.2 x) := by
  have z₀ := pauliSum_kkZ hm hγ hγΛ hp hp' hq ht hx (i := 0) rfl rfl
  have z₆ := pauliSum_kkZ hm hγ hγΛ hp hp' hq ht hx (i := 6) rfl rfl
  have z₁₀ := pauliSum_kkZ hm hγ hγΛ hp hp' hq ht hx (i := 10) rfl rfl
  have hE := pauliSum_kkEndSum hm hγ hγΛ hp hp' hq ht hx
  simp only [kkLimX_sum_second hm hγ hγΛ hp hp' hq ht hx]
  have e : ∀ Q E Z₀ Z₆ Z₁₀ : Idx → ℂ,
      ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 *
        (kCst R * (Q j + E j) - kCst R * (Z₀ j + Z₆ j + Z₁₀ j)) =
      kCst R * (∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * Q j +
        ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * E j -
        (∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * Z₀ j +
          ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * Z₆ j +
          ∑ j : Idx, pauliWt R.m p' p j.1 j.2.1 j.2.2 * Z₁₀ j)) := fun _ _ _ _ _ => by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e (fun j => kkQ 5 R p p' t 1 0 j.1 j.2.1 j.2.2 x + kkQ 4 R p p' t 1 3 j.1 j.2.1 j.2.2 x +
      kkQ 9 R p p' t 2 0 j.1 j.2.1 j.2.2 x) (fun j => kkEndSum R p p' t j.1 j.2.1 j.2.2 x)
      (fun j => kkZ 0 R p p' t j.1 j.2.1 j.2.2 x) (fun j => kkZ 6 R p p' t j.1 j.2.1 j.2.2 x)
      (fun j => kkZ 10 R p p' t j.1 j.2.1 j.2.2 x), hE, z₀, z₆, z₁₀]
  ring

end Terms

/-! ### The Pauli limit of the three doubly pinched values -/

/-- The Pauli-weighted sum of the three surviving doubly pinched values `Q(5, 1, 0)`,
`Q(4, 1, 3)`, `Q(9, 2, 0)` at `x = 1/2` along the curve. -/
noncomputable def kkQS (R : Params) (t u : ℝ) : ℂ :=
  kkPW R.m (fun j =>
    kkQ 5 R (restMomentum R.m) (curveMomentum R.m u) t 1 0 j.1 j.2.1 j.2.2 (1 / 2) +
      kkQ 4 R (restMomentum R.m) (curveMomentum R.m u) t 1 3 j.1 j.2.1 j.2.2 (1 / 2) +
      kkQ 9 R (restMomentum R.m) (curveMomentum R.m u) t 2 0 j.1 j.2.1 j.2.2 (1 / 2)) u

theorem le_half_sqrt {m T : ℝ} (hm : 0 < m) (hT : 4 ≤ T) : m ≤ √(m ^ 2 * T) / 2 := by
  have h : 2 * m ≤ √(m ^ 2 * T) := (Real.le_sqrt (by positivity) (by positivity)).2 (by nlinarith)
  linarith

/-- **The sum of the twelve longitudinal Pauli limits is the Pauli limit of the three surviving
doubly pinched values**: for `T ≥ 4` the even quotient of `kCst · kkQS` converges to
`kkSumP`. -/
theorem tendsto_kkQS (P₀ : Params) (hm : 0 < P₀.m) {mγ Λ T : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ)
    (hT : 4 ≤ T) :
    Tendsto (evenQuot fun u => kCst { P₀ with mγ := mγ, Λ := Λ } *
        kkQS { P₀ with mγ := mγ, Λ := Λ } (√(P₀.m ^ 2 * T) / 2) u) (𝓝[≠] 0)
      (𝓝 (kkSumP P₀ mγ Λ T)) := by
  set R : Params := { P₀ with mγ := mγ, Λ := Λ }
  set t := √(P₀.m ^ 2 * T) / 2
  have hm' : 0 < R.m := hm
  have hγ : 0 < R.mγ := hmγ
  have hγΛ : R.mγ ≤ R.Λ := hΛ.le
  have ht : R.m ≤ t := le_half_sqrt hm hT
  have hZ : ∀ i : Fin 12, Tendsto (evenQuot (kkPT R i t (1 / 2))) (𝓝[≠] 0)
      (𝓝 (kkLimP R i t (1 / 2))) := fun i => by
    obtain ⟨Z, hZ⟩ := (kkPauliW_kkH (i := i) hm' hγ hγΛ ht).1 (1 / 2) half_mem_Ioo
    exact tendsto_nhds_limUnder ⟨Z, hZ⟩
  have hsum := tendsto_finsetSum Finset.univ fun i _ => hZ i
  refine hsum.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1))] with u hu
  have key : ∀ v ∈ Ioo (-1 : ℝ) 1, ∑ i, kkPT R i t (1 / 2) v = kCst R * kkQS R t v :=
    fun v hv => by
      have hq : 0 ≤ Minkowski.dot (curveMomentum R.m v - restMomentum R.m)
          (curveMomentum R.m v - restMomentum R.m) :=
        (dot_curveMomentum_sub R.m hv).symm ▸ curveQ_nonneg R.m hv
      have h := pauliSum_sum_kkLimX_kkH hm' hγ hγΛ (dot_restMomentum (m := R.m))
        (dot_curveMomentum R.m hv) hq ht half_mem_Ioo
      simp only [kkPT, kkPW, kkQS]
      rw [Finset.sum_comm, ← h]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := neg_mem_Ioo_one' hu
  simp only [evenQuot]
  rw [← key u hu, ← key (-u) hu', ← Finset.sum_add_distrib, Finset.sum_div]

end QED.ChainProof.SetCRegDisp

end
