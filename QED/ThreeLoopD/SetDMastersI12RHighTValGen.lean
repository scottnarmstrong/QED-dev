/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLMobius
public import QED.Polylog.HPLShuffle
public import QED.Polylog.ExtraIntegrals
import QED.Polylog.HPLLowWeight
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₂`: primitives of logarithmic integrands through harmonic polylogarithms

Tools for evaluating `∫₀¹ J` when `J` is a polynomial in `log s`, `log (1 - s)`, `log (1 + s)`
with rational coefficients, by an explicit primitive.

* A monomial `log^i x (-log (1 - x))^j log^k (1 + x)` is the product of the weight-one harmonic
  polylogarithms `H(0)^i H(1)^j H(-1)^k`, hence (iterated shuffle product,
  `QED.Polylog.HPL.hpl_mul_hpl`) the sum of `H(w; x)` over the iterated shuffles `w` of these
  letters (`QED.ThreeLoopD.i12TVMono_eq_sum`). Prefixing a letter `c` gives a primitive of
  `f_c(x)` times the monomial (`QED.ThreeLoopD.hasDerivAt_i12TVH`), with limits `H(c · w; 1)` at
  `1` when `c ≠ 1` and `0` at `0` when `c ≠ 0` or the monomial contains `log (1 ∓ x)`.
* The same for polynomials given as coefficient lists (`QED.ThreeLoopD.i12TVPsi`), and for their
  composition with the Möbius involution `φ(s) = (1 - s)/(1 + s)`: the difference
  `Ψ₋₁(φ(s)) - Ψ₀(φ(s))` is a primitive of `P(φ(s))/(1 - s)`
  (`QED.ThreeLoopD.hasDerivAt_i12TVMob`).
* Elementary endpoint atoms (`QED.ThreeLoopD.i12TVZ`, `QED.ThreeLoopD.i12TVO`): products of a
  power of the divergent logarithm with enough powers of the vanishing combinations
  `log (1 - s) + s`, `log (1 + s) - s` (at `0`), resp. `log s + (1 - s)`,
  `log ((1 + s)/2) + (1 - s)/2` (at `1`), tend to `0`.
* The fundamental theorem of calculus on `(0, 1)` in the form used
  (`QED.ThreeLoopD.i12TV_integral_eq`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory
open QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### Iterated shuffles -/

/-- The iterated shuffles of a list of words, counted with multiplicity. -/
def i12TVsh : List (List Letter) → List (List Letter)
  | [] => [[]]
  | u :: ws => (i12TVsh ws).flatMap (shuffle u)

theorem i12TVsh_perm : ∀ {ws : List (List Letter)} {w : List Letter}, w ∈ i12TVsh ws →
    w.Perm ws.flatten
  | [], w, h => by
    simp only [i12TVsh, List.mem_singleton] at h
    simp [h]
  | u :: ws, w, h => by
    simp only [i12TVsh, List.mem_flatMap] at h
    obtain ⟨v, hv, hw⟩ := h
    rw [List.flatten_cons]
    exact (perm_of_mem_shuffle hw).trans ((i12TVsh_perm hv).append_left u)

theorem i12TV_sum_flatMap (L : List (List Letter)) (g : List Letter → List (List Letter))
    (f : List Letter → ℝ) :
    ((L.flatMap g).map f).sum = (L.map fun v => ((g v).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons v L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- The product of harmonic polylogarithms is the sum over the iterated shuffles. -/
theorem prod_hpl_eq_sum_i12TVsh (ws : List (List Letter)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (ws.map fun w => hpl w x).prod = ((i12TVsh ws).map fun w => hpl w x).sum := by
  induction ws with
  | nil => simp [i12TVsh]
  | cons u ws ih =>
    rw [List.map_cons, List.prod_cons, ih, i12TVsh, i12TV_sum_flatMap, ← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun v _ => hpl_mul_hpl u v hx

/-! ### Monomials -/

/-- The letters of the monomial `H(0)^i H(1)^j H(-1)^k`. -/
def i12TVws (i j k : ℕ) : List (List Letter) :=
  List.replicate i [zero] ++ List.replicate j [one] ++ List.replicate k [negOne]

/-- The monomial `log^i x (-log (1 - x))^j log^k (1 + x)`. -/
noncomputable def i12TVMono (i j k : ℕ) (x : ℝ) : ℝ :=
  log x ^ i * (-log (1 - x)) ^ j * log (1 + x) ^ k

theorem i12TVMono_eq_sum (i j k : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i12TVMono i j k x = ((i12TVsh (i12TVws i j k)).map fun w => hpl w x).sum := by
  rw [← prod_hpl_eq_sum_i12TVsh _ hx, i12TVws]
  simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate,
    hpl_zero, hpl_one hx, hpl_negOne hx, i12TVMono]

/-- The primitive `∑_w H(c · w; x)` of `f_c(x)` times the monomial `(i, j, k)`. -/
noncomputable def i12TVH (c : Letter) (i j k : ℕ) (x : ℝ) : ℝ :=
  (((i12TVsh (i12TVws i j k)).map (c :: ·)).map fun w => hpl w x).sum

theorem hasDerivAt_i12TVH (c : Letter) (i j k : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12TVH c i j k) (c.kernel x * i12TVMono i j k x) x := by
  rw [i12TVMono_eq_sum i j k hx]
  exact hasDerivAt_sum_hpl_cons c _ hx

theorem tendsto_i12TVH_one {c : Letter} (hc : c ≠ one) (i j k : ℕ) :
    Tendsto (i12TVH c i j k) (𝓝[<] 1) (𝓝 (i12TVH c i j k 1)) := by
  refine tendsto_list_sum (f := fun w => hpl w) (a := fun w => hpl w 1) _ fun w hw => ?_
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hw
  exact tendsto_hpl_one hc v

theorem not_allZero_of_mem_i12TVsh {i j k : ℕ} (hjk : 0 < j + k) {v : List Letter}
    (hv : v ∈ i12TVsh (i12TVws i j k)) : ¬AllZero v := by
  intro hz
  have h := hz.of_perm (i12TVsh_perm hv)
  rcases Nat.eq_zero_or_pos j with hj | hj
  · have hk : 0 < k := by omega
    have hm : negOne ∈ (i12TVws i j k).flatten := by
      simp only [i12TVws, List.flatten_append, List.mem_append]
      right
      simp [List.mem_replicate, hk.ne']
    exact absurd (h _ hm) (by decide)
  · have hm : one ∈ (i12TVws i j k).flatten := by
      simp only [i12TVws, List.flatten_append, List.mem_append]
      left; right
      simp [List.mem_replicate, hj.ne']
    exact absurd (h _ hm) (by decide)

theorem tendsto_i12TVH_zero {c : Letter} {i j k : ℕ} (h : c ≠ zero ∨ 0 < j + k) :
    Tendsto (i12TVH c i j k) (𝓝[>] 0) (𝓝 0) := by
  have := tendsto_list_sum (f := fun w => hpl w) (a := fun _ => (0 : ℝ)) (x := 𝓝[>] (0 : ℝ))
    ((i12TVsh (i12TVws i j k)).map (c :: ·)) fun w hw => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      refine tendsto_hpl_zero fun hz => ?_
      rcases h with hc | hjk
      · exact hc (allZero_cons.1 hz).1
      · exact not_allZero_of_mem_i12TVsh hjk hv (allZero_cons.1 hz).2
  rw [show (((i12TVsh (i12TVws i j k)).map (c :: ·)).map fun _ => (0 : ℝ)).sum = 0 from
    List.sum_eq_zero fun y hy => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hy; rfl] at this
  exact this

/-! ### Polynomials -/

/-- A polynomial `∑ c log^i x (-log (1 - x))^j log^k (1 + x)`, as a list of `(c, i, j, k)`. -/
noncomputable def i12TVPoly (P : List (ℝ × ℕ × ℕ × ℕ)) (x : ℝ) : ℝ :=
  (P.map fun t => t.1 * i12TVMono t.2.1 t.2.2.1 t.2.2.2 x).sum

/-- The derivative of `QED.ThreeLoopD.i12TVPoly`. -/
noncomputable def i12TVPolyD (P : List (ℝ × ℕ × ℕ × ℕ)) (x : ℝ) : ℝ :=
  (P.map fun t => t.1 * ((t.2.1 : ℝ) * log x ^ (t.2.1 - 1) / x * (-log (1 - x)) ^ t.2.2.1 *
      log (1 + x) ^ t.2.2.2 +
    log x ^ t.2.1 * ((t.2.2.1 : ℝ) * (-log (1 - x)) ^ (t.2.2.1 - 1) / (1 - x)) *
      log (1 + x) ^ t.2.2.2 +
    log x ^ t.2.1 * (-log (1 - x)) ^ t.2.2.1 *
      ((t.2.2.2 : ℝ) * log (1 + x) ^ (t.2.2.2 - 1) / (1 + x)))).sum

/-- The primitive `∑ c H(c' · (i, j, k); x)` of `f_{c'}(x) P(x)`. -/
noncomputable def i12TVPsi (c : Letter) (P : List (ℝ × ℕ × ℕ × ℕ)) (x : ℝ) : ℝ :=
  (P.map fun t => t.1 * i12TVH c t.2.1 t.2.2.1 t.2.2.2 x).sum

theorem hasDerivAt_i12TVMono (i j k : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12TVMono i j k)
      ((i : ℝ) * log x ^ (i - 1) / x * (-log (1 - x)) ^ j * log (1 + x) ^ k +
        log x ^ i * ((j : ℝ) * (-log (1 - x)) ^ (j - 1) / (1 - x)) * log (1 + x) ^ k +
        log x ^ i * (-log (1 - x)) ^ j * ((k : ℝ) * log (1 + x) ^ (k - 1) / (1 + x))) x := by
  have h1 : HasDerivAt log (1 / x) x := by
    simpa [one_div] using hasDerivAt_log hx.1.ne'
  have h2 : HasDerivAt (fun y => -log (1 - y)) (1 / (1 - x)) x := by
    have := ((hasDerivAt_id x).const_sub 1).log (by simp; linarith [hx.2])
    convert this.neg using 1
    · funext y; simp
    · simp only [id, neg_div, neg_neg, one_div]
  have h3 : HasDerivAt (fun y => log (1 + y)) (1 / (1 + x)) x := by
    have := ((hasDerivAt_id x).const_add 1).log (by simp; linarith [hx.1])
    simpa using this
  have := ((h1.pow i).mul (h2.pow j)).mul (h3.pow k)
  convert this using 1
  · funext y; simp [i12TVMono]
  · simp only [Pi.pow_apply, Pi.mul_apply]
    ring

theorem hasDerivAt_i12TVPoly (P : List (ℝ × ℕ × ℕ × ℕ)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12TVPoly P) (i12TVPolyD P x) x := by
  induction P with
  | nil => exact hasDerivAt_const x (0 : ℝ)
  | cons t P ih =>
    exact ((hasDerivAt_i12TVMono t.2.1 t.2.2.1 t.2.2.2 hx).const_mul t.1).add ih

theorem hasDerivAt_i12TVPsi (c : Letter) (P : List (ℝ × ℕ × ℕ × ℕ)) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i12TVPsi c P) (c.kernel x * i12TVPoly P x) x := by
  induction P with
  | nil =>
    convert hasDerivAt_const x (0 : ℝ) using 1
    · rfl
    · rw [show i12TVPoly [] x = 0 from rfl, mul_zero]
  | cons t P ih =>
    have := ((hasDerivAt_i12TVH c t.2.1 t.2.2.1 t.2.2.2 hx).const_mul t.1).add ih
    convert this using 1
    · rfl
    · rw [show i12TVPoly (t :: P) x = t.1 * i12TVMono t.2.1 t.2.2.1 t.2.2.2 x + i12TVPoly P x
        from rfl]
      ring

theorem tendsto_i12TVPsi_one {c : Letter} (hc : c ≠ one) (P : List (ℝ × ℕ × ℕ × ℕ)) :
    Tendsto (i12TVPsi c P) (𝓝[<] 1) (𝓝 (i12TVPsi c P 1)) := by
  induction P with
  | nil => exact tendsto_const_nhds
  | cons t P ih =>
    exact ((tendsto_i12TVH_one hc t.2.1 t.2.2.1 t.2.2.2).const_mul t.1).add ih

theorem tendsto_i12TVPsi_zero {c : Letter} {P : List (ℝ × ℕ × ℕ × ℕ)}
    (h : ∀ t ∈ P, c ≠ zero ∨ 0 < t.2.2.1 + t.2.2.2) :
    Tendsto (i12TVPsi c P) (𝓝[>] 0) (𝓝 0) := by
  induction P with
  | nil => exact tendsto_const_nhds
  | cons t P ih =>
    have h1 := (tendsto_i12TVH_zero (i := t.2.1) (h t List.mem_cons_self)).const_mul t.1
    have h2 := ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    have h3 := h1.add h2
    rw [mul_zero, add_zero] at h3
    exact h3

/-! ### The Möbius involution -/

theorem i12TV_log_mobMap {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    log (mobMap s) = log (1 - s) - log (1 + s) := by
  unfold mobMap
  rw [log_div (by linarith [hs.2]) (by linarith [hs.1])]

theorem i12TV_log_one_sub_mobMap {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    log (1 - mobMap s) = log 2 + log s - log (1 + s) := by
  have h : 1 - mobMap s = 2 * s / (1 + s) := by
    have : 1 + s ≠ 0 := by linarith [hs.1]
    unfold mobMap
    field_simp
    ring
  rw [h, log_div (by linarith [hs.1]) (by linarith [hs.1]), log_mul (by norm_num) hs.1.ne']

theorem i12TV_log_one_add_mobMap {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    log (1 + mobMap s) = log 2 - log (1 + s) := by
  have h : 1 + mobMap s = 2 / (1 + s) := by
    have : 1 + s ≠ 0 := by linarith [hs.1]
    unfold mobMap
    field_simp
    ring
  rw [h, log_div (by norm_num) (by linarith [hs.1])]

theorem i12TVMono_mobMap (i j k : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    i12TVMono i j k (mobMap s) = (log (1 - s) - log (1 + s)) ^ i *
      (-(log 2 + log s - log (1 + s))) ^ j * (log 2 - log (1 + s)) ^ k := by
  rw [i12TVMono, i12TV_log_mobMap hs, i12TV_log_one_sub_mobMap hs, i12TV_log_one_add_mobMap hs]

/-- **The Möbius primitive**: `Ψ₋₁(φ(s)) - Ψ₀(φ(s))` is a primitive of `P(φ(s))/(1 - s)`. -/
theorem hasDerivAt_i12TVMob (P : List (ℝ × ℕ × ℕ × ℕ)) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => i12TVPsi negOne P (mobMap y) - i12TVPsi zero P (mobMap y))
      (i12TVPoly P (mobMap s) / (1 - s)) s := by
  have hm := hasDerivAt_mobMap (x := s) (by linarith [hs.1])
  have h1 := (hasDerivAt_i12TVPsi negOne P (mobMap_mem_Ioo hs)).comp s hm
  have h0 := (hasDerivAt_i12TVPsi zero P (mobMap_mem_Ioo hs)).comp s hm
  refine (h1.sub h0).congr_deriv ?_
  have h1s : 0 < 1 - s := by linarith [hs.2]
  have h1s' : 0 < 1 + s := by linarith [hs.1]
  simp only [kernel_negOne, kernel_zero, mobMap]
  field_simp
  ring

theorem tendsto_i12TVMob_zero (P : List (ℝ × ℕ × ℕ × ℕ)) :
    Tendsto (fun y => i12TVPsi negOne P (mobMap y) - i12TVPsi zero P (mobMap y)) (𝓝[>] 0)
      (𝓝 (i12TVPsi negOne P 1 - i12TVPsi zero P 1)) :=
  ((tendsto_i12TVPsi_one (by decide) P).comp tendsto_mobMap_zero).sub
    ((tendsto_i12TVPsi_one (by decide) P).comp tendsto_mobMap_zero)

theorem tendsto_i12TVMob_one {P : List (ℝ × ℕ × ℕ × ℕ)}
    (h : ∀ t ∈ P, 0 < t.2.2.1 + t.2.2.2) :
    Tendsto (fun y => i12TVPsi negOne P (mobMap y) - i12TVPsi zero P (mobMap y)) (𝓝[<] 1)
      (𝓝 0) := by
  have h1 := (tendsto_i12TVPsi_zero (c := negOne) (P := P) fun t _ => Or.inl (by decide)).comp
    tendsto_mobMap_one
  have h0 := (tendsto_i12TVPsi_zero (c := zero) (P := P) fun t ht => Or.inr (h t ht)).comp
    tendsto_mobMap_one
  simpa using h1.sub h0

/-! ### Endpoint atoms -/

theorem i12TV_abs_log_one_sub_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have h := abs_log_sub_add_sum_range_le (x := x) (by linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one] at h
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  calc |log (1 - x) + x| = |x + log (1 - x)| := by rw [add_comm]
    _ ≤ |x| ^ 2 / (1 - |x|) := h
    _ ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith), hx2]
      nlinarith [sq_nonneg x, abs_nonneg x]

/-- The common bound of the endpoint atoms. -/
theorem abs_i12TV_atom_le {i j k m n g : ℕ} (h : n + 1 ≤ 2 * j + 2 * k + m) {L X Y W t C : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C) (hL : |L| ^ i ≤ C * t ^ (-(1 / 2 : ℝ)))
    (hX : |X| ≤ 2 * t ^ 2) (hY : |Y| ≤ 2 * t ^ 2) (hW : |W| ≤ 2) :
    |L ^ i * X ^ j * Y ^ k * t ^ m * t⁻¹ ^ n * W ^ g| ≤ C * 2 ^ (j + k + g) * t ^ (1 / 2 : ℝ) := by
  have key : |L ^ i * X ^ j * Y ^ k * t ^ m * t⁻¹ ^ n * W ^ g| ≤
      C * t ^ (-(1 / 2 : ℝ)) * (2 * t ^ 2) ^ j * (2 * t ^ 2) ^ k * t ^ m * t⁻¹ ^ n * 2 ^ g := by
    simp only [abs_mul, abs_pow, abs_inv, abs_of_pos ht0]
    gcongr
  have e1 : t ^ (2 * j + 2 * k + m) * t⁻¹ ^ n ≤ t := by
    calc t ^ (2 * j + 2 * k + m) * t⁻¹ ^ n ≤ t ^ (n + 1) * t⁻¹ ^ n := by
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0.le ht1 h) (by positivity)
      _ = t := by
          rw [pow_succ, inv_pow, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht0.ne'),
            one_mul]
  have e2 : t ^ (-(1 / 2 : ℝ)) * t = t ^ (1 / 2 : ℝ) := by
    rw [← rpow_add_one ht0.ne']
    norm_num
  calc _ ≤ _ := key
    _ = C * 2 ^ (j + k + g) * t ^ (-(1 / 2 : ℝ)) * (t ^ (2 * j + 2 * k + m) * t⁻¹ ^ n) := by
        ring
    _ ≤ C * 2 ^ (j + k + g) * t ^ (-(1 / 2 : ℝ)) * t := by gcongr
    _ = C * 2 ^ (j + k + g) * t ^ (1 / 2 : ℝ) := by rw [mul_assoc _ _ t, e2]

/-- An endpoint atom at `0`: `log^i s (log (1 - s) + s)^j (log (1 + s) - s)^k sᵐ s⁻ⁿ (1 - s)⁻ᵍ`. -/
noncomputable def i12TVZ (i j k m n g : ℕ) (s : ℝ) : ℝ :=
  log s ^ i * (log (1 - s) + s) ^ j * (log (1 + s) - s) ^ k * s ^ m * s⁻¹ ^ n * (1 - s)⁻¹ ^ g

theorem tendsto_i12TVZ {i j k m n g : ℕ} (h : n + 1 ≤ 2 * j + 2 * k + m) :
    Tendsto (i12TVZ i j k m n g) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hlog⟩ := abs_log_pow_le i (δ := 1 / 2) (by norm_num)
  refine tendsto_zero_of_abs_le_rpow (C := C * 2 ^ (j + k + g)) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) fun t ht => ?_
  have ht0 := ht.1
  have ht1 : t ≤ 1 / 2 := ht.2
  have hat : |t| = t := abs_of_pos ht0
  refine abs_i12TV_atom_le h ht0 (by linarith) hC (hlog t ⟨ht0, by linarith⟩)
    (i12TV_abs_log_one_sub_add_le (by rw [hat]; exact ht1)) ?_ ?_
  · have := i12TV_abs_log_one_sub_add_le (x := -t) (by rw [abs_neg, hat]; exact ht1)
    rw [sub_neg_eq_add, neg_sq] at this
    rwa [sub_eq_add_neg]
  · rw [abs_inv, abs_of_pos (by linarith), inv_le_comm₀ (by linarith) (by norm_num)]
    linarith

/-- An endpoint atom at `1`: `log^i (1 - s) (log s + (1 - s))^j
(log (1 + s) - log 2 + (1 - s)/2)^k (1 - s)ᵐ (1 - s)⁻ⁿ s⁻ᵍ`. -/
noncomputable def i12TVO (i j k m n g : ℕ) (s : ℝ) : ℝ :=
  log (1 - s) ^ i * (log s + (1 - s)) ^ j * (log (1 + s) - log 2 + (1 - s) / 2) ^ k *
    (1 - s) ^ m * (1 - s)⁻¹ ^ n * s⁻¹ ^ g

theorem tendsto_i12TVO {i j k m n g : ℕ} (h : n + 1 ≤ 2 * j + 2 * k + m) :
    Tendsto (i12TVO i j k m n g) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨C, hC, hlog⟩ := abs_log_pow_le i (δ := 1 / 2) (by norm_num)
  have hF : Tendsto (fun t => i12TVO i j k m n g (1 - t)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_zero_of_abs_le_rpow (C := C * 2 ^ (j + k + g))
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) fun t ht => ?_
    have ht0 := ht.1
    have ht1 : t ≤ 1 / 2 := ht.2
    have hat : |t| = t := abs_of_pos ht0
    unfold i12TVO
    rw [sub_sub_cancel]
    refine abs_i12TV_atom_le h ht0 (by linarith) hC (hlog t ⟨ht0, by linarith⟩) ?_ ?_ ?_
    · exact i12TV_abs_log_one_sub_add_le (by rw [hat]; exact ht1)
    · have e : log (1 + (1 - t)) - log 2 = log (1 - t / 2) := by
        rw [← log_div (by linarith) (by norm_num)]
        congr 1
        ring
      rw [e]
      have := i12TV_abs_log_one_sub_add_le (x := t / 2) (by rw [abs_of_pos (by linarith)]; linarith)
      calc _ ≤ 2 * (t / 2) ^ 2 := this
        _ ≤ 2 * t ^ 2 := by nlinarith
    · rw [abs_inv, abs_of_pos (by linarith), inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
  refine (hF.comp QED.Polylog.tendsto_one_sub_nhdsLT_one).congr fun x => ?_
  simp

/-! ### Lists of endpoint atoms -/

/-- Whether an atom `(i, j, k, m, n, g)` has `n + 1 ≤ 2j + 2k + m`. -/
def i12TVok (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (x.2.2.2.2.1 + 1 ≤ 2 * x.2.1 + 2 * x.2.2.1 + x.2.2.2.1)

/-- A combination of endpoint atoms at `0`. -/
noncomputable def i12TVZs (L : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (s : ℝ) : ℝ :=
  (L.map fun t => t.1 * i12TVZ t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
    t.2.2.2.2.2.2 s).sum

/-- A combination of endpoint atoms at `1`. -/
noncomputable def i12TVOs (L : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (s : ℝ) : ℝ :=
  (L.map fun t => t.1 * i12TVO t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
    t.2.2.2.2.2.2 s).sum

theorem tendsto_i12TVZs (L : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ))
    (h : (L.map Prod.snd).all i12TVok = true) : Tendsto (i12TVZs L) (𝓝[>] 0) (𝓝 0) := by
  induction L with
  | nil => exact tendsto_const_nhds
  | cons t L ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    have h1 := (tendsto_i12TVZ (i := t.2.1) (g := t.2.2.2.2.2.2)
      (by simpa [i12TVok] using h.1)).const_mul t.1
    have h3 := h1.add (ih h.2)
    rw [mul_zero, add_zero] at h3
    exact h3

theorem tendsto_i12TVOs (L : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ))
    (h : (L.map Prod.snd).all i12TVok = true) : Tendsto (i12TVOs L) (𝓝[<] 1) (𝓝 0) := by
  induction L with
  | nil => exact tendsto_const_nhds
  | cons t L ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    have h1 := (tendsto_i12TVO (i := t.2.1) (g := t.2.2.2.2.2.2)
      (by simpa [i12TVok] using h.1)).const_mul t.1
    have h3 := h1.add (ih h.2)
    rw [mul_zero, add_zero] at h3
    exact h3

/-! ### The fundamental theorem of calculus on `(0, 1)` -/

theorem i12TV_integral_eq {J Φ : ℝ → ℝ} {A B : ℝ}
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (J s) s) (hJ : IntegrableOn J (Ioo 0 1))
    (h0 : Tendsto Φ (𝓝[>] 0) (𝓝 A)) (h1 : Tendsto Φ (𝓝[<] 1) (𝓝 B)) :
    ∫ s in Ioo (0 : ℝ) 1, J s = B - A := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hd
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hJ) h0 h1

end QED.ThreeLoopD
