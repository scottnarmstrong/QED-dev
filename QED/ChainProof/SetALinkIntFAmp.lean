/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntFLines
public import QED.ChainProof.SetALinkIntFTerm
public import QED.ChainProof.SetALinkInt

/-!
# The class obligation for a fermion counterterm on a closed loop

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58), for the classes `FA`, `FB`. Let `C` be a two-loop contraction of `gauge`
vertices and one `fermionCt` vertex on its closed fermion loop, `fo` the loop line leaving the
counterterm. After the resummation at the counterterm (`sum_ampTerm_eq`), each term `fcTerm` of
variant `v` is `M_f^p` times a product of line factors and of `D_{M_f}⁻¹` on the lines of
`fcZ C fo v` (`prod_fcFac`); the constant is non-zero only if the `gauge` vertex pairs are
different-block and the counterterm pair same-block, and then the number of different-block
loop lines has the parity of `|loop| - 1` (`parity_fc`). With the multiplicities of the
decidable test `FCrit`, the flavour sum of each term satisfies (T₉′)
(`jointEnergyFirstIntegrable_fcTerm`, by `jointEnergyFirstIntegrable_blockLines`), hence the
class obligation (`classIntA_of_fc`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALink

open QED.GradedProof.X0 QED.Graded QED.WickModel
open QED.TwoLoop.Bridge (propDenom)
open QED.TwoLoop.FurryIntegrable (sgn)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type}

/-! ### The decidable test -/

/-- The lines of a variant carrying the flavour mass. -/
def fcZ (C : Contraction 1 nA κ) (fo : FermionLine C) (v : Fin 3) : Finset (Line C) :=
  if v = 0 then (zSet C).erase (.inl fo) else zSet C

/-- The denominators of the lines. -/
def fcN (C : Contraction 1 nA κ) (Z : Finset (Line C)) : Line C → ℕ :=
  fun l => (if isZL C l = true then 0 else baseN C l) + if l ∈ Z then 1 else 0

/-- The numerator degrees of the lines, `E'` the different-block loop lines. -/
def fcD (C : Contraction 1 nA κ) (fo : FermionLine C) (v : Fin 3) (E' : Finset (Line C)) :
    Line C → ℕ :=
  fun l => if l = .inl fo ∧ v ≠ 2 then 0 else baseD C E' l

/-- The power of the flavour mass. -/
def fcPow (C : Contraction 1 nA κ) (v : Fin 3) (E' : Finset (Line C)) : ℕ :=
  if v = 2 then (zSet C).card - E'.card + 1 else (zSet C).card - E'.card - 1

/-- The test for one pattern `E'` and one variant `v`: the mass power is even and the
multiplicities pass `BlockCrit`. -/
def FPat (C : Contraction 1 nA κ) (fo : FermionLine C) (E' : Finset (Line C)) (v : Fin 3) :
    Prop :=
  fcPow C v E' % 2 = 0 ∧
    BlockCrit (rowOf C) (fcN C (fcZ C fo v)) (fcD C fo v E') (fcZ C fo v) (fcPow C v E' / 2)

instance (C : Contraction 1 nA κ) (fo : FermionLine C) (E' : Finset (Line C)) (v : Fin 3) :
    Decidable (FPat C fo E' v) := by
  unfold FPat; infer_instance

/-- The admissible variants of a pattern. -/
def FPats (C : Contraction 1 nA κ) (fo : FermionLine C) (E' : Finset (Line C)) : Prop :=
  ∀ v : Fin 3, (v = 2 ∨ (Sum.inl fo : Line C) ∉ E') → FPat C fo E' v

instance (C : Contraction 1 nA κ) (fo : FermionLine C) (E' : Finset (Line C)) :
    Decidable (FPats C fo E') := by
  unfold FPats; infer_instance

/-- **The test for a fermion counterterm on the closed loop**: every admissible pattern `E'`
(the different-block loop lines) passes `FPats`. -/
def FCrit (C : Contraction 1 nA κ) (fo : FermionLine C) : Prop :=
  ∀ E' ∈ (zSet C).powerset, (E'.card + 1) % 2 = (zSet C).card % 2 → FPats C fo E'

instance (C : Contraction 1 nA κ) (fo : FermionLine C) : Decidable (FCrit C fo) := by
  unfold FCrit; infer_instance

/-! ### The line factors -/

/-- The numerator factors of a variant. -/
noncomputable def fcNum (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (fo : FermionLine C)
    (v : Fin 3) (l : Line C) : (Fin 4 → ℝ) → ℂ :=
  if l = .inl fo ∧ v ≠ 2 then fun _ => (1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) (β fo.1) (α fo.tail)
  else nsNum P Φ C α β lor l

theorem length_nsMs (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ) (l : Line C) :
    (nsMs P Φ C l).length = if isZL C l = true then 0 else baseN C l := by
  rcases l with f | g
  · by_cases hz : isZL C (.inl f) = true
    · simp [nsMs, hz]
    · by_cases ht : isTree C (.inl f) = true <;> simp [nsMs, baseN, hz, ht]
  · simp only [nsMs, baseN, isZL_inr, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> rfl

theorem mem_fcZ_iff {C : Contraction 1 nA κ} {fo : FermionLine C} {v : Fin 3} {l : Line C}
    (hl : ¬ (l = .inl fo ∧ v ≠ 2)) : l ∈ fcZ C fo v ↔ isZL C l = true := by
  have hz : l ∈ zSet C ↔ isZL C l = true := by simp [zSet]
  unfold fcZ
  split_ifs with hv
  · rw [Finset.mem_erase, hz]
    refine ⟨fun h => h.2, fun h => ⟨fun h' => hl ⟨h', by rw [hv]; decide⟩, h⟩⟩
  · exact hz

/-- **A line factor of a variant, split.** -/
theorem fcFac_eq (P : Params) (Φ : Lepton.Flavors F) (hε : P.ε ≠ 0) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (fo : FermionLine C)
    (hz : zOf C fo.1) (v : Fin 3) (M : ℝ) (l : Line C) (k : Fin 4 → ℝ) :
    fcFac P Φ C α β lor fo v M l k =
      (if isZL C l = true ∧ sameB α β l = true ∧ ¬ (l = .inl fo ∧ v ≠ 2) then (M : ℂ) else 1) *
        (fcNum P Φ C α β lor fo v l k * dProd P.ε (nsMs P Φ C l) k) *
        (if l ∈ fcZ C fo v then (propDenom M P.ε k)⁻¹ else 1) := by
  by_cases hl : l = .inl fo ∧ v ≠ 2
  · obtain ⟨rfl, hv⟩ := hl
    have hz' : isZL C (.inl fo) = true := by simp [isZL, hz]
    have hms : nsMs P Φ C (.inl fo) = [] := by simp [nsMs, hz']
    fin_cases v
    · simp [fcFac, foFac, fcNum, fcZ, hms, dProd]
    · simp [fcFac, foFac, fcNum, fcZ, hms, dProd, zSet, hz']
    · exact absurd rfl hv
  · have h1 : fcFac P Φ C α β lor fo v M l k = nsFac P Φ C α β lor M l k := by
      unfold fcFac
      split_ifs with h
      · subst h
        have hv : v = 2 := by by_contra hv; exact hl ⟨rfl, hv⟩
        subst hv
        rfl
      · rfl
    rw [h1, nsFac_eq P Φ hε α β lor M l k]
    simp only [fcNum, hl, ↓reduceIte, not_false_eq_true, and_true]
    congr 1
    simp only [mem_fcZ_iff hl]

/-- **The product of the line factors of a variant.** -/
theorem prod_fcFac (P : Params) (Φ : Lepton.Flavors F) (hε : P.ε ≠ 0) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (fo : FermionLine C)
    (hz : zOf C fo.1) (v : Fin 3) (M : ℝ) (k : Line C → Fin 4 → ℝ) :
    ∏ l, fcFac P Φ C α β lor fo v M l (k l) =
      (M : ℂ) ^ (Finset.univ.filter fun l =>
          isZL C l = true ∧ sameB α β l = true ∧ ¬ (l = .inl fo ∧ v ≠ 2)).card *
        ((∏ l, fcNum P Φ C α β lor fo v l (k l) * dProd P.ε (nsMs P Φ C l) (k l)) *
          ∏ l ∈ fcZ C fo v, (propDenom M P.ε (k l))⁻¹) := by
  classical
  simp only [fcFac_eq P Φ hε C α β lor fo hz v M _ (k _), Finset.prod_mul_distrib]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Finset.prod_ite_mem,
    Finset.univ_inter]
  ring

/-! ### Counting and parity -/

theorem card_fcMass {C : Contraction 1 nA κ} (α β : Wick.FermionVertex κ → Fin 4)
    (fo : FermionLine C) (hz : zOf C fo.1) (v : Fin 3)
    (hs : v ≠ 2 → sameB α β (Sum.inl fo : Line C) = true) :
    (Finset.univ.filter fun l : Line C =>
        isZL C l = true ∧ sameB α β l = true ∧ ¬ (l = .inl fo ∧ v ≠ 2)).card +
      (if v = 2 then 1 else 0) = fcPow C v (nsE α β C) := by
  classical
  have hc := card_zSet_eq (C := C) α β
  set S := (zSet C).filter fun l => sameB α β l = true with hS
  have hf : (Finset.univ.filter fun l : Line C =>
      isZL C l = true ∧ sameB α β l = true ∧ ¬ (l = .inl fo ∧ v ≠ 2)) =
      S.filter fun l => ¬ (l = .inl fo ∧ v ≠ 2) := by
    ext l
    simp only [hS, zSet, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hf]
  have hP : nsP α β C = S.card := rfl
  unfold fcPow
  by_cases hv : v = 2
  · have h2 : S.filter (fun l => ¬ (l = .inl fo ∧ v ≠ 2)) = S :=
      Finset.filter_true_of_mem fun l _ h => h.2 hv
    rw [h2, ite_eq_left hv, ite_eq_left hv]
    omega
  · have hmem : (Sum.inl fo : Line C) ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [isZL, hz]⟩,
        hs hv⟩
    have he : S.filter (fun l => ¬ (l = .inl fo ∧ v ≠ 2)) = S.erase (.inl fo) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
      tauto
    rw [he, Finset.card_erase_of_mem hmem, ite_eq_right hv, ite_eq_right hv]
    have h1 := Finset.card_pos.mpr ⟨_, hmem⟩
    omega

/-- The loop lines satisfying a predicate, as fermion lines of the closed loop. -/
theorem card_zSet_filter {C : Contraction 1 nA κ} (R : Line C → Prop) [DecidablePred R] :
    ((zSet C).filter R).card =
      (Finset.univ.filter fun f : ZLine C (zOf C) => R (.inl f.1)).card := by
  refine (Finset.card_bij (fun f _ => (Sum.inl f.1 : Line C)) (fun f hf => ?_)
    (fun f _ f' _ h => Subtype.ext (Sum.inl_injective h)) (fun l hl => ?_)).symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and, isZL_inl, decide_eq_true_eq]
    exact ⟨f.2, hf⟩
  · simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rcases l with fl | g
    · exact ⟨⟨fl, by simpa [isZL] using hl.1⟩, by simpa using hl.2, rfl⟩
    · exact absurd hl.1 (by simp [isZL])

/-- **Parity**: with a non-zero constant, the number of different-block loop lines has the
parity of the number of loop lines minus one. -/
theorem parity_fc (e : ℝ) {C : Contraction 1 nA κ} (fo : FermionLine C)
    (hct : κ fo.1.1 = .fermionCt) (hκ : ∀ t, t ≠ fo.1.1 → κ t = .gauge) (hz : zOf C fo.1)
    (hZ : ∀ x, isZ (zOf C) (C.1.1 x) = isZ (zOf C) x) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4)
    (hΓ : ∏ t, Wick.vertexFactor e 0 0 1 0 1 α β lor 0 0 t ≠ 0) :
    ((nsE α β C).card + 1) % 2 = (zSet C).card % 2 := by
  classical
  have hv : ∀ s : {s // zOf C s}, sgn (α s.1) * sgn (β s.1) =
      if s = ⟨fo.1, hz⟩ then 1 else -1 := fun s => by
    have hne := (Finset.prod_ne_zero_iff.mp hΓ) s.1.1 (Finset.mem_univ _)
    rw [sgn_mul_sgn]
    by_cases hs : s = ⟨fo.1, hz⟩
    · subst hs
      rw [vertexFactor_ct_eq _ _ _ _ _ _ _ _ _ _ _ fo.1 hct] at hne
      simp only [ofReal_zero, zero_smul, mul_one, ofReal_one, one_smul, zero_add] at hne
      have hab : α fo.1 = β fo.1 := by
        by_contra h
        exact hne (by rw [Matrix.one_apply_ne h, mul_zero])
      simp [hab]
    · have hg : κ s.1.1 = .gauge := hκ _ fun h => hs (Subtype.ext (Subtype.ext h))
      have hb : ¬ blk (α s.1) = blk (β s.1) := fun hb => hne (by
        rw [← vertexFactor_gauge_eq e 0 0 0 0 0 α β lor 0 0 _ hg]
        exact vertexFactor_gauge_eq_zero_of_blk e α β lor s.1 hg hb)
      simp [hb, hs]
  have hV : ∏ s : {s // zOf C s}, sgn (α s.1) * sgn (β s.1) =
      (-1 : ℂ) ^ (Fintype.card {s // zOf C s} - 1) := by
    rw [Fintype.prod_eq_mul_prod_compl ⟨fo.1, hz⟩, hv, ite_eq_left rfl, one_mul,
      Finset.prod_congr rfl fun s hs => (hv s).trans (ite_eq_right (by simpa using hs)),
      Finset.prod_const, Finset.card_compl, Finset.card_singleton]
  have hcl := prod_sgn_closed hZ α β
  rw [hV, prod_sgn_eq (fun f : ZLine C (zOf C) => β f.1.1) (fun f => α f.1.tail), ← pow_add]
    at hcl
  have he : (Finset.univ.filter fun f : ZLine C (zOf C) =>
      ¬ blk (β f.1.1) = blk (α f.1.tail)).card = (nsE α β C).card := by
    rw [nsE, card_zSet_filter]
    congr 1
  have hr : Fintype.card {s // zOf C s} = (zSet C).card := by
    rw [← card_zLine hZ, ← Finset.filter_true_of_mem (s := zSet C) (p := fun _ => True)
      (fun _ _ => trivial), card_zSet_filter, Finset.filter_true_of_mem fun _ _ => trivial,
      Finset.card_univ]
  have hpos : 0 < (zSet C).card :=
    Finset.card_pos.mpr ⟨.inl fo, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [isZL, hz]⟩⟩
  have hev := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp hcl
  rw [he, hr, Nat.even_iff] at hev
  omega

/-! ### One resummed term, summed over the flavours -/

/-- The weight of a variant without its mass factor. -/
noncomputable def fcW₀ (P : Params) (D : Counterterms F) (f : F) : Fin 3 → ℂ
  | 0 => ((P.e ^ 2 * D.d₂ f 0 : ℝ) : ℂ)
  | 1 => ((P.e ^ 2 * D.d₂ f 0 : ℝ) : ℂ) * ((P.ε : ℂ) * I)
  | 2 => ((P.e ^ 2 * D.dm f 0 - P.e ^ 2 * D.d₂ f 0 : ℝ) : ℂ)

theorem fcW_mul_pow (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (v : Fin 3)
    (c : ℕ) : fcW P Φ D f v * (Φ.mass f : ℂ) ^ c =
      fcW₀ P D f v * (Φ.mass f : ℂ) ^ (c + if v = 2 then 1 else 0) := by
  fin_cases v <;> simp [fcW, fcW₀, pow_succ]
  ring

theorem fcW₀_rep (P : Params) (D : Counterterms F) (rep : F → F)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) (f : F) (v : Fin 3) :
    fcW₀ P D f v = fcW₀ P D (rep f) v := by
  fin_cases v <;> simp [fcW₀, (hD f).1, (hD f).2]

theorem affPoly_fcNum (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (fo : FermionLine C)
    (v : Fin 3) (l : Line C) :
    AffPoly (fcD C fo v (nsE α β C) l) (fcNum P Φ C α β lor fo v l) ∨ rowOf C l = 0 := by
  by_cases hl : l = .inl fo ∧ v ≠ 2
  · refine Or.inl ?_
    rw [show fcD C fo v (nsE α β C) l = 0 from ite_eq_left hl,
      show fcNum P Φ C α β lor fo v l = _ from ite_eq_left hl]
    exact AffPoly.const _
  · simp only [fcD, fcNum, hl, ↓reduceIte]
    exact affPoly_nsNum P Φ α β lor l

variable [Fintype F] [DecidableEq F]

/-- **(T₉′) of one resummed term, summed over the flavours.** -/
theorem jointEnergyFirstIntegrable_fcTerm (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) (hε : 0 < P.ε)
    (C : Contraction 1 nA κ) (fo : FermionLine C) (hct : κ fo.1.1 = .fermionCt)
    (hκ : ∀ t, t ≠ fo.1.1 → κ t = .gauge) (hz : zOf C fo.1)
    (hZ : ∀ x, isZ (zOf C) (C.1.1 x) = isZ (zOf C) x) (hcrit : FCrit C fo)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (v : Fin 3) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * (z * fcTerm P Φ D C αOut βIn μ fo v f α β lor
        (lineMomentum₂ C pOut pIn kIn ℓ)) := by
  classical
  -- the vanishing terms
  by_cases hΓ : ∏ t, Wick.vertexFactor P.e 0 0 1 0 1 α β lor 0 0 t = 0
  · simp only [fcTerm, fcConst, hΓ, mul_zero, zero_mul, Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  by_cases h0 : v ≠ 2 ∧ sameB α β (Sum.inl fo : Line C) = false
  · have hb : ¬ blk (β fo.1) = blk (α fo.tail) := by simpa using h0.2
    have h1 : (1 : Matrix (Fin 4) (Fin 4) ℂ) (β fo.1) (α fo.tail) = 0 := one_eq_zero_of_blk hb
    have hz0 : ∀ f k, fcTerm P Φ D C αOut βIn μ fo v f α β lor k = 0 := fun f k => by
      have hp : ∏ l, fcFac P Φ C α β lor fo v (Φ.mass f) l (k l) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ (Sum.inl fo)) ?_
        simp only [fcFac, ↓reduceIte]
        rcases (by omega : v.val = 0 ∨ v.val = 1 ∨ v.val = 2) with h | h | h
        · obtain rfl : v = 0 := Fin.ext h; simp [foFac, h1]
        · obtain rfl : v = 1 := Fin.ext h; simp [foFac, h1]
        · exact absurd (Fin.ext h) h0.1
      simp only [fcTerm, hp, mul_zero]
    simp only [hz0, mul_zero, Finset.sum_const_zero]
    exact jointEnergyFirstIntegrable_zero_fun'
  -- the pattern
  have hs : v ≠ 2 → sameB α β (Sum.inl fo : Line C) = true := fun hv => by
    simpa [hv] using h0
  have hpar := parity_fc P.e fo hct hκ hz hZ α β lor hΓ
  have hfo : v = 2 ∨ (Sum.inl fo : Line C) ∉ nsE α β C := by
    by_cases hv : v = 2
    · exact Or.inl hv
    · refine Or.inr fun h => ?_
      have := (Finset.mem_filter.mp h).2
      rw [hs hv] at this
      exact Bool.noConfusion this
  obtain ⟨hp, hB⟩ := hcrit (nsE α β C) (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) hpar
    v hfo
  set j := fcPow C v (nsE α β C) / 2 with hj
  have hcnt := card_fcMass α β fo hz v hs
  have hn : (fun l => (nsMs P Φ C l).length + if l ∈ fcZ C fo v then 1 else 0) =
      fcN C (fcZ C fo v) := funext fun l => by simp only [fcN, length_nsMs]
  have h := jointEnergyFirstIntegrable_blockLines Φ rep hrep hPV₁ hPV₂ (rowOf C)
    (extPart C pOut pIn kIn) (nsMs P Φ C) (fcD C fo v (nsE α β C))
    (fcNum P Φ C α β lor fo v) (affPoly_fcNum P Φ C α β lor fo v) (fcZ C fo v) j
    (by rw [hn]; exact hB) hε (fun f => z * fcConst P C αOut βIn μ α β lor * fcW₀ P D f v)
    (fun f => by rw [fcW₀_rep P D rep hD f v])
  refine (congrArg _ (funext fun ℓ => Finset.sum_congr rfl fun f _ => ?_)).mp h
  simp only [← lineMomentum₂_eq_rowMom]
  rw [fcTerm, prod_fcFac P Φ hε.ne' C α β lor fo hz v (Φ.mass f), ← mul_assoc (fcW P Φ D f v),
    fcW_mul_pow, hcnt, show fcPow C v (nsE α β C) = 2 * j by omega, pow_mul]
  ring

/-! ### The class obligation -/

omit [DecidableEq F] in
theorem sum_comm_five_fc {A B B' V : Type*} [Fintype A] [Fintype B] [Fintype B'] [Fintype V]
    (X : F → A → B → B' → V → ℂ) :
    ∑ a, ∑ b, ∑ b', ∑ v, ∑ f, X f a b b' v = ∑ f, ∑ a, ∑ b, ∑ b', ∑ v, X f a b b' v := by
  have h1 : ∀ a b b', ∑ v, ∑ f, X f a b b' v = ∑ f, ∑ v, X f a b b' v :=
    fun _ _ _ => Finset.sum_comm
  simp only [h1]
  exact sum_comm_four fun f a b b' => ∑ v, X f a b b' v

/-- **The class obligation for a two-loop contraction with one `fermionCt` vertex on its closed
fermion loop**, from the decidable test `FCrit`. -/
theorem classIntA_of_fc {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (fo : FermionLine C) (hct : κ fo.1.1 = .fermionCt) (hκ : ∀ t, t ≠ fo.1.1 → κ t = .gauge)
    (hz : zOf C fo.1) (hC : ClosedShape C (zOf C)) (hL : loopCount C = 2)
    (hcrit : FCrit C fo) : ClassIntA C 0 := by
  intro P F _ _ Φ D rep hH pOut pIn kIn _ αOut βIn μ
  rw [hL]
  simp only [regulatedAmplitude_eq_closed Φ P D hC, contractionAmplitude_zero_eq]
  set z : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹
  have hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 :=
    fun f => ⟨(hH.hD f).2.1, (hH.hD f).2.2⟩
  have h := jointEnergyFirstIntegrable_sum' Finset.univ fun α _ =>
    jointEnergyFirstIntegrable_sum' Finset.univ fun lor _ =>
      jointEnergyFirstIntegrable_sum' Finset.univ fun β _ =>
        jointEnergyFirstIntegrable_sum' Finset.univ fun v _ =>
          jointEnergyFirstIntegrable_fcTerm P Φ D rep hH.hrep hH.hPV₁ hH.hPV₂ hD hH.hε C fo hct hκ
            hz hC.inv hcrit pOut pIn kIn αOut βIn μ α β lor v z
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [sum_comm_five_fc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hA : ∀ α lor, ∑ β, ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn
      (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor =
      ∑ β, ∑ v : Fin 3, fcTerm P Φ D C αOut βIn μ fo v f α β lor
        (lineMomentum₂ C pOut pIn kIn ℓ) := fun α lor =>
    sum_ampTerm_eq P Φ D hH.hε.ne' C fo hct hκ hz f pIn kIn _ αOut βIn μ α lor
  have hc : ∀ α, ∑ β, ∑ lor, ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn
      (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor =
      ∑ lor, ∑ β, ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn
      (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ α β lor := fun α => Finset.sum_comm
  simp only [hc, hA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun lor _ =>
    Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun v _ => ?_
  ring

end QED.ChainProof.SetALink

end
