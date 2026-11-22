/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWNode
public import QED.ChainProof.SetAKSKWLogSq
public import QED.ChainProof.SetAKSKDNode
public import QED.ChainProof.SetAKSKUVAExp

/-!
# Set (a), stage D: the dispersion of the `VA` finite part at a fixed node

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. At unit
mass and a fixed node `(x, σ) ∈ (0,1)²`, the finite part `Q(s) = ksUQ 1 s x σ` of the `VA` class
is a combination, with `s`-independent coefficients, of the nodes `1/A`, `log A`, `log² A`,
`L = log(1 + B/A)`, `A L`, `(log(A + B) - log B)/A` and `K(B/A)` in `A = 1 + s/T₀`,
`T₀ = 1/(σ(1-σ))`, `B = x(1-σ)/(1-x)` (`ksW_ksUQ_nodeForm`). With the dispersion of each node,

  `Q(s) - Q(0) = -C s/(s + T₀) + ∫_{T > T₀} n(T) s/(T(s + T)) dT`,

with `C = α Y log((1-x)/x²)` and, in `a = Tσ(1-σ) - 1`, `Y = 1 - σ`, `b = x/(1-x)`,

  `n = -2a₁Y(c - log a) + [a > bY](αY/a - βY + 2a₁Y)`
      `+ [a ≤ bY](α/b + (2a₁ - β)a/b + 2a₁Y log(bY/a))`,

`c = -log x + log Y`, `a₀ = α + βA` (`α = 16σ(1-σ)(3+x) - 16(1-x)σ²`, `β = 16(1-x)σ²`).

Main results:

* `ksW_ksUQ_nodeForm`: the node form of `ksUPhiInf - ksUPhi`;
* **`ksW_ksUQ_sub_eq`**: the dispersion of `ksUQ 1 s x σ - ksUQ 1 0 x σ`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- **The node form of the `VA` finite part**, for `a₀ = α + βA`, `B = bY`. -/
theorem ksW_ksUQ_nodeForm {A b Y : ℝ} (α β a₁ ℓ : ℝ) (hA : 0 < A) (hb : 0 < b) (hY : 0 < Y) :
    ksUPhiInf A Y (α + β * A) a₁ ℓ - ksUPhi A b Y (α + β * A) a₁ =
      α * Y * (ℓ + log Y - log (b * Y)) / A +
        (β * Y * (ℓ + log Y) - 2 * a₁ * Y * (ℓ + log Y) + 4 * a₁ * Y * ksUK 1) +
        a₁ * Y * (ℓ + log Y - log A) ^ 2 - α * Y * ((log (A + b * Y) - log (b * Y)) / A) +
        (-(α / b) - β * Y + 2 * a₁ * Y) * log (1 + b * Y / A) +
        (2 * a₁ - β) / b * (A * log (1 + b * Y / A)) + (2 * a₁ * Y - β * Y) * log A -
        2 * a₁ * Y * ksUK (b * Y / A) := by
  have hq : 0 < 1 + b * Y / A := by positivity
  have e1 : (A + b * Y) / A = 1 + b * Y / A := by field_simp
  have e2 : log (A + b * Y) = log A + log (1 + b * Y / A) := by
    rw [← log_mul hA.ne' hq.ne']
    congr 1
    field_simp
  unfold ksUPhiInf ksUPhi
  rw [e1, e2]
  generalize log (1 + b * Y / A) = L
  generalize log A = lA
  field_simp
  ring

/-- The constant part `α` of the `VA` moment `a₀ = α + βA` (unit mass). -/
def ksWal (x σ : ℝ) : ℝ := 16 * σ * (1 - σ) * (3 + x) - 16 * (1 - x) * σ ^ 2

/-- The slope `β` of the `VA` moment `a₀ = α + βA` (unit mass). -/
def ksWbe (x σ : ℝ) : ℝ := 16 * (1 - x) * σ ^ 2

/-- The weight `C = αY log((1-x)/x²)` of the threshold term. -/
noncomputable def ksWCA (x σ : ℝ) : ℝ := ksWal x σ * (1 - σ) * log ((1 - x) / x ^ 2)

/-- The `VA` spectral density at the node `(x, σ)` in `a = Tσ(1-σ) - 1`. -/
noncomputable def ksWnAa (x σ a : ℝ) : ℝ :=
  -2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ) - log a) +
    if x / (1 - x) * (1 - σ) < a then
      ksWal x σ * (1 - σ) / a - ksWbe x σ * (1 - σ) + 2 * ksDa1 x σ * (1 - σ)
    else
      ksWal x σ / (x / (1 - x)) + (2 * ksDa1 x σ - ksWbe x σ) * a / (x / (1 - x)) +
        2 * ksDa1 x σ * (1 - σ) * log (x / (1 - x) * (1 - σ) / a)

/-- The `VA` spectral density at the node `(x, σ)` in the spectral variable `T`. -/
noncomputable def ksWnA (x σ T : ℝ) : ℝ := ksWnAa x σ (T * (σ * (1 - σ)) - 1)

theorem ksW_log_threshold {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {Y : ℝ} (hY : 0 < Y) :
    -log x + log Y - log (x / (1 - x) * Y) = log ((1 - x) / x ^ 2) := by
  have h0 := hx.1
  have h1 : 0 < 1 - x := by linarith [hx.2]
  rw [log_mul (div_pos h0 h1).ne' hY.ne', log_div h0.ne' h1.ne', log_div h1.ne' (by positivity),
    log_pow]
  push_cast
  ring

theorem ksW_ksWnA_arg {σ T : ℝ} (hp : 0 < σ * (1 - σ)) :
    T * (σ * (1 - σ)) - 1 = (T - (σ * (1 - σ))⁻¹) / (σ * (1 - σ))⁻¹ := by
  rw [div_inv_eq_mul, sub_mul, inv_mul_cancel₀ hp.ne']

/-- The density below the second threshold, `T₀ < T ≤ T₀(1 + B)`: affine in `a`. -/
theorem ksW_ksWnA_low {x σ T : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (hT : (σ * (1 - σ))⁻¹ < T) (hT₁ : T ≤ (σ * (1 - σ))⁻¹ * (1 + x / (1 - x) * (1 - σ))) :
    ksWnA x σ T = (-2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) +
        ksWal x σ / (x / (1 - x)) + 2 * ksDa1 x σ * (1 - σ) * log (x / (1 - x) * (1 - σ))) +
      (2 * ksDa1 x σ - ksWbe x σ) / (x / (1 - x)) *
        ((T - (σ * (1 - σ))⁻¹) / (σ * (1 - σ))⁻¹) := by
  have hp : 0 < σ * (1 - σ) := mul_pos hσ.1 (by linarith [hσ.2])
  have hB : 0 < x / (1 - x) * (1 - σ) :=
    mul_pos (div_pos hx.1 (by linarith [hx.2])) (by linarith [hσ.2])
  have ht₀ : 0 < (σ * (1 - σ))⁻¹ := inv_pos.2 hp
  have ha : 0 < T * (σ * (1 - σ)) - 1 := by
    rw [ksW_ksWnA_arg hp]
    exact div_pos (by linarith) ht₀
  have haB : T * (σ * (1 - σ)) - 1 ≤ x / (1 - x) * (1 - σ) := by
    rw [ksW_ksWnA_arg hp, div_le_iff₀ ht₀]
    nlinarith
  unfold ksWnA ksWnAa
  simp only [show ¬(x / (1 - x) * (1 - σ) < T * (σ * (1 - σ)) - 1) from not_lt.2 haB,
    ↓reduceIte]
  rw [log_div hB.ne' ha.ne', ← ksW_ksWnA_arg hp]
  ring

/-- The density above the second threshold, `T > T₀(1 + B)`. -/
theorem ksW_ksWnA_high {x σ T : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (hT₁ : (σ * (1 - σ))⁻¹ * (1 + x / (1 - x) * (1 - σ)) < T) :
    ksWnA x σ T = (-2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) -
        ksWbe x σ * (1 - σ) + 2 * ksDa1 x σ * (1 - σ)) +
      ksDa1 x σ * (1 - σ) * (2 * log ((T - (σ * (1 - σ))⁻¹) / (σ * (1 - σ))⁻¹)) +
      -(ksWal x σ * (1 - σ)) * (-((σ * (1 - σ))⁻¹ / (T - (σ * (1 - σ))⁻¹))) := by
  have hp : 0 < σ * (1 - σ) := mul_pos hσ.1 (by linarith [hσ.2])
  have hB : 0 < x / (1 - x) * (1 - σ) :=
    mul_pos (div_pos hx.1 (by linarith [hx.2])) (by linarith [hσ.2])
  have ht₀ : 0 < (σ * (1 - σ))⁻¹ := inv_pos.2 hp
  have haB : x / (1 - x) * (1 - σ) < T * (σ * (1 - σ)) - 1 := by
    rw [ksW_ksWnA_arg hp, lt_div_iff₀ ht₀]
    nlinarith
  have hd : 0 < T - (σ * (1 - σ))⁻¹ := by nlinarith
  unfold ksWnA ksWnAa
  simp only [haB, ↓reduceIte]
  rw [ksW_ksWnA_arg hp]
  field_simp
  ring

/-- **The dispersion of the `VA` finite part at a fixed node** (unit mass):
`Q(s) - Q(0) = -C s/(s + T₀) + ∫_{T > T₀} n(T) s/(T(s + T)) dT`, `T₀ = 1/(σ(1-σ))`. -/
theorem ksW_ksUQ_sub_eq {x σ s : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (hs : -4 < s) :
    ksUQ 1 s x σ - ksUQ 1 0 x σ = -ksWCA x σ * (s / (s + (σ * (1 - σ))⁻¹)) +
      ∫ T in Ioi (σ * (1 - σ))⁻¹, ksWnA x σ T * (s / (T * (s + T))) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hY : 0 < 1 - σ := by linarith
  have hp : 0 < σ * (1 - σ) := mul_pos hσ0 hY
  have hp4 : σ * (1 - σ) ≤ 1 / 4 := by nlinarith [sq_nonneg (σ - 1 / 2)]
  set t₀ := (σ * (1 - σ))⁻¹ with ht₀def
  have ht₀ : 0 < t₀ := inv_pos.2 hp
  have h4 : 4 ≤ t₀ := by
    rw [ht₀def, le_inv_comm₀ (by norm_num) hp]
    linarith
  have hst : -t₀ < s := by linarith
  have hb : 0 < x / (1 - x) := div_pos hx0 (by linarith)
  set b := x / (1 - x) with hbdef
  set Y := 1 - σ with hYdef
  set B := b * Y with hBdef
  have hB : 0 < B := mul_pos hb hY
  set T₁ := t₀ * (1 + B) with hT₁def
  have hT₁ : t₀ < T₁ := by rw [hT₁def]; nlinarith
  set α := ksWal x σ
  set β := ksWbe x σ
  set a₁ := ksDa1 x σ
  have hA : ksDA 1 s σ = 1 + s / t₀ := by
    simp only [ksDA, one_pow, ht₀def, div_inv_eq_mul]
    ring
  have hA0 : ksDA 1 0 σ = 1 := by simp [ksDA]
  have hApos : 0 < 1 + s / t₀ := by
    rw [show 1 + s / t₀ = (t₀ + s) / t₀ by field_simp]
    exact div_pos (by linarith) ht₀
  have hQ : ∀ u : ℝ, ksUQ 1 u x σ = ksUPhiInf (ksDA 1 u σ) Y (α + β * ksDA 1 u σ) a₁ (-log x) -
      ksUPhi (ksDA 1 u σ) b Y (α + β * ksDA 1 u σ) a₁ := fun u => by
    have e1 : ksDb 1 0 x = b := by
      rw [ksU_ksDb_zero ⟨hx0, hx1⟩, hbdef]
      ring
    have e2 : ksDa0 1 x u σ = α + β * ksDA 1 u σ := by
      simp only [ksDa0, α, β, ksWal, ksWbe, ksDA]
      ring
    simp only [ksUQ, e1, e2]
    rfl
  rw [hQ, hQ, hA, hA0, ksW_ksUQ_nodeForm _ _ _ _ hApos hb hY,
    ksW_ksUQ_nodeForm _ _ _ _ one_pos hb hY]
  -- the kernels
  have hk0 : IntegrableOn (fun T => s / (T * (s + T))) (Ioi t₀) :=
    ksD_integrableOn_logNodeKer ht₀ hst
  have hl0 : IntegrableOn (fun T => 2 * log ((T - t₀) / t₀) * (s / (T * (s + T)))) (Ioi t₀) :=
    ksW_integrableOn_logSq ht₀ hst
  have hr1 : IntegrableOn (fun T => -(t₀ / (T - t₀)) * (s / (T * (s + T)))) (Ioi T₁) :=
    ksW_integrableOn_logRatio ht₀ hst hT₁
  have ha1 : IntegrableOn (fun T => (T - t₀) / t₀ * (s / (T * (s + T)))) (Ioc t₀ T₁) := by
    have hc : ContinuousOn (fun T => (T - t₀) / t₀ * (s / (T * (s + T)))) (Icc t₀ T₁) := by
      refine ContinuousOn.mul (by fun_prop) (continuousOn_const.div (by fun_prop) fun T hT => ?_)
      exact (mul_pos (by linarith [hT.1]) (by linarith [hT.1])).ne'
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hsub₁ : Ioc t₀ T₁ ⊆ Ioi t₀ := Ioc_subset_Ioi_self
  have hsub₂ : Ioi T₁ ⊆ Ioi t₀ := Ioi_subset_Ioi hT₁.le
  -- the nodes
  have N_log := ksD_log_eq_integral ht₀ hst
  have N_log₁ := ksD_log_eq_integral (lt_trans ht₀ hT₁) (by linarith : -T₁ < s)
  have N_sq := ksW_logSq_eq_integral ht₀ hst
  have N_ratio := ksW_logRatio_node ht₀ hst hB
  have N_AL := ksW_mulLog_node ht₀ hst hB.le
  have N_K := ksW_ksUK_node ht₀ hst hB
  rw [intervalIntegral.integral_of_le hT₁.le] at N_AL N_K
  -- `L(A) - L(1) = log(1 + s/T₁) - log A`
  have hL : log (1 + B / (1 + s / t₀)) =
      log (1 + B) + log (1 + s / T₁) - log (1 + s / t₀) := by
    have hq : 0 < 1 + B / (1 + s / t₀) := by positivity
    have hT₁0 : T₁ ≠ 0 := by linarith
    have hts : t₀ + s ≠ 0 := by linarith
    have hq₁ : 0 < 1 + s / T₁ := by
      rw [show 1 + s / T₁ = (T₁ + s) / T₁ by field_simp]
      exact div_pos (by linarith) (by linarith)
    rw [← log_mul (by linarith) hq₁.ne', eq_sub_iff_add_eq, ← log_mul hq.ne' hApos.ne']
    congr 1
    rw [hT₁def]
    field_simp
    ring
  -- the `K` node in the atoms
  have hKf : ∫ T in Ioc t₀ T₁, (log ((T - t₀) / t₀) - log B) * (s / (T * (s + T))) =
      (∫ T in Ioc t₀ T₁, 2 * log ((T - t₀) / t₀) * (s / (T * (s + T)))) / 2 -
        log B * ∫ T in Ioc t₀ T₁, s / (T * (s + T)) := by
    rw [← integral_const_mul, ← integral_div, ← integral_sub ((hl0.mono_set hsub₁).div_const 2)
      ((hk0.mono_set hsub₁).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioc fun T _ => ?_
    ring
  -- the split of the density integral
  have hsplit : ∀ f : ℝ → ℝ, IntegrableOn f (Ioc t₀ T₁) → IntegrableOn f (Ioi T₁) →
      ∫ T in Ioi t₀, f T = (∫ T in Ioc t₀ T₁, f T) + ∫ T in Ioi T₁, f T := fun f h₁ h₂ => by
    rw [← Ioc_union_Ioi_eq_Ioi hT₁.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      h₁ h₂]
  -- the density on the two pieces
  set n₁ := -2 * a₁ * Y * (-log x + log Y) + α / b + 2 * a₁ * Y * log B with hn₁
  set n₂ := (2 * a₁ - β) / b with hn₂
  set m₁ := -2 * a₁ * Y * (-log x + log Y) - β * Y + 2 * a₁ * Y with hm₁
  have hlow : ∀ T ∈ Ioc t₀ T₁, ksWnA x σ T * (s / (T * (s + T))) =
      n₁ * (s / (T * (s + T))) + n₂ * ((T - t₀) / t₀ * (s / (T * (s + T)))) := fun T hT => by
    rw [ksW_ksWnA_low ⟨hx0, hx1⟩ ⟨hσ0, hσ1⟩ hT.1 hT.2]
    ring
  have hhigh : ∀ T ∈ Ioi T₁, ksWnA x σ T * (s / (T * (s + T))) =
      m₁ * (s / (T * (s + T))) + a₁ * Y * (2 * log ((T - t₀) / t₀) * (s / (T * (s + T)))) +
        -(α * Y) * (-(t₀ / (T - t₀)) * (s / (T * (s + T)))) := fun T hT => by
    rw [ksW_ksWnA_high ⟨hx0, hx1⟩ ⟨hσ0, hσ1⟩ hT]
    ring
  have iL : IntegrableOn (fun T => n₁ * (s / (T * (s + T))) +
      n₂ * ((T - t₀) / t₀ * (s / (T * (s + T))))) (Ioc t₀ T₁) :=
    ((hk0.mono_set hsub₁).const_mul n₁).add (ha1.const_mul n₂)
  have iH₀ : IntegrableOn (fun T => m₁ * (s / (T * (s + T))) +
      a₁ * Y * (2 * log ((T - t₀) / t₀) * (s / (T * (s + T))))) (Ioi T₁) :=
    ((hk0.mono_set hsub₂).const_mul m₁).add ((hl0.mono_set hsub₂).const_mul (a₁ * Y))
  have iH : IntegrableOn (fun T => m₁ * (s / (T * (s + T))) +
      a₁ * Y * (2 * log ((T - t₀) / t₀) * (s / (T * (s + T)))) +
        -(α * Y) * (-(t₀ / (T - t₀)) * (s / (T * (s + T))))) (Ioi T₁) :=
    iH₀.add (hr1.const_mul (-(α * Y)))
  rw [hsplit _ (IntegrableOn.congr_fun iL (fun T hT => (hlow T hT).symm) measurableSet_Ioc)
      (IntegrableOn.congr_fun iH (fun T hT => (hhigh T hT).symm) measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioc hlow, setIntegral_congr_fun measurableSet_Ioi hhigh,
    integral_add ((hk0.mono_set hsub₁).const_mul n₁) (ha1.const_mul n₂),
    integral_add iH₀ (hr1.const_mul (-(α * Y))),
    integral_add ((hk0.mono_set hsub₂).const_mul m₁) ((hl0.mono_set hsub₂).const_mul (a₁ * Y)),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  have R1 := hsplit _ (hk0.mono_set hsub₁) (hk0.mono_set hsub₂)
  have R2 := hsplit _ (hl0.mono_set hsub₁) (hl0.mono_set hsub₂)
  have hthr := ksW_log_threshold ⟨hx0, hx1⟩ hY
  have hinv : (1 + s / t₀)⁻¹ = 1 - s / (s + t₀) := by
    have : s + t₀ ≠ 0 := by linarith
    have : t₀ + s ≠ 0 := by linarith
    field_simp
    ring
  rw [hL] at N_AL ⊢
  simp only [div_one, log_one, one_mul] at N_AL ⊢
  unfold ksWCA
  rw [← hthr]
  linear_combination a₁ * Y * N_sq + (-2 * a₁ * Y * (-log x + log Y) -
      (-(α / b) - β * Y + 2 * a₁ * Y) + (2 * a₁ * Y - β * Y)) * (N_log.trans R1) +
    (-(α / b) - β * Y + 2 * a₁ * Y) * N_log₁ + a₁ * Y * R2 + (-(α * Y)) * N_ratio +
    n₂ * N_AL + (-2 * a₁ * Y) * (N_K.trans hKf) +
    α * Y * (-log x + log Y - log (x / (1 - x) * Y)) * hinv

/-- The integrand of the node dispersion is integrable on `T > T₀`. -/
theorem ksW_integrableOn_ksWnA {x σ s : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (hs : -4 < s) :
    IntegrableOn (fun T => ksWnA x σ T * (s / (T * (s + T)))) (Ioi (σ * (1 - σ))⁻¹) := by
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  have hp : 0 < σ * (1 - σ) := mul_pos hσ.1 hY
  have hp4 : σ * (1 - σ) ≤ 1 / 4 := by nlinarith [sq_nonneg (σ - 1 / 2)]
  set t₀ := (σ * (1 - σ))⁻¹ with ht₀def
  have ht₀ : 0 < t₀ := inv_pos.2 hp
  have h4 : 4 ≤ t₀ := by
    rw [ht₀def, le_inv_comm₀ (by norm_num) hp]
    linarith
  have hst : -t₀ < s := by linarith
  have hB : 0 < x / (1 - x) * (1 - σ) := mul_pos (div_pos hx.1 (by linarith [hx.2])) hY
  set T₁ := t₀ * (1 + x / (1 - x) * (1 - σ)) with hT₁def
  have hT₁ : t₀ < T₁ := by rw [hT₁def]; nlinarith
  have hk0 : IntegrableOn (fun T => s / (T * (s + T))) (Ioi t₀) :=
    ksD_integrableOn_logNodeKer ht₀ hst
  have hl0 : IntegrableOn (fun T => 2 * log ((T - t₀) / t₀) * (s / (T * (s + T)))) (Ioi t₀) :=
    ksW_integrableOn_logSq ht₀ hst
  have hr1 : IntegrableOn (fun T => -(t₀ / (T - t₀)) * (s / (T * (s + T)))) (Ioi T₁) :=
    ksW_integrableOn_logRatio ht₀ hst hT₁
  have ha1 : IntegrableOn (fun T => (T - t₀) / t₀ * (s / (T * (s + T)))) (Ioc t₀ T₁) := by
    have hc : ContinuousOn (fun T => (T - t₀) / t₀ * (s / (T * (s + T)))) (Icc t₀ T₁) := by
      refine ContinuousOn.mul (by fun_prop) (continuousOn_const.div (by fun_prop) fun T hT => ?_)
      exact (mul_pos (by linarith [hT.1]) (by linarith [hT.1])).ne'
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hsub₁ : Ioc t₀ T₁ ⊆ Ioi t₀ := Ioc_subset_Ioi_self
  have hsub₂ : Ioi T₁ ⊆ Ioi t₀ := Ioi_subset_Ioi hT₁.le
  have iL := ((hk0.mono_set hsub₁).const_mul (-2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) +
        ksWal x σ / (x / (1 - x)) + 2 * ksDa1 x σ * (1 - σ) * log (x / (1 - x) * (1 - σ)))).add
    (ha1.const_mul ((2 * ksDa1 x σ - ksWbe x σ) / (x / (1 - x))))
  have iH := (((hk0.mono_set hsub₂).const_mul (-2 * ksDa1 x σ * (1 - σ) * (-log x + log (1 - σ)) -
        ksWbe x σ * (1 - σ) + 2 * ksDa1 x σ * (1 - σ))).add
    ((hl0.mono_set hsub₂).const_mul (ksDa1 x σ * (1 - σ)))).add
    (hr1.const_mul (-(ksWal x σ * (1 - σ))))
  rw [← Ioc_union_Ioi_eq_Ioi hT₁.le]
  refine IntegrableOn.union (IntegrableOn.congr_fun iL (fun T hT => ?_) measurableSet_Ioc)
    (IntegrableOn.congr_fun iH (fun T hT => ?_) measurableSet_Ioi)
  · simp only [Pi.add_apply]
    rw [ksW_ksWnA_low hx hσ hT.1 hT.2]
    ring
  · simp only [Pi.add_apply]
    rw [ksW_ksWnA_high hx hσ hT]
    ring

end QED.ChainProof.SetAKS

end
