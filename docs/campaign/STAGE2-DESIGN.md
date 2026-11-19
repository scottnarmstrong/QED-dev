# Stage 2 statement draft: the order-graded counterterm successor (design note)

Scratch, untracked. Drafted 2026-11-19 at repository commit `7b3856f`, revised at `d3a2e60` after
the review (APPROVE WITH NITS) and the author's ruling S2′ ("D-55 revised"), under D-49, D-52,
D-53, D-54, D-55 revised and the provisional overnight rulings S1–S11 below. **Nothing here is frozen, approved or
staged, and no tracked file was edited.** The candidate Lean text is in `Stage2/*.lean`,
concatenated in build order in `PACKET.lean.txt`. `Check/*.lean` is scratch evidence and not part
of the packet. Blueprint: `../threeloop/STAGE2-MEMO.md` (§2, §2.6, §3, §5) and
`../threeloop/B4-CHECK.md`.

| File | SHA-256 (first 16) | Contents |
| --- | --- | --- |
| `Stage2/Data.lean` | `7f6a62bea6359de3` | (G₀) (G₀′) (G₁)–(G₁‴) (G₂)–(G₂″) (G₁₂′) |
| `Stage2/Value.lean` | `28e65debffde8ae7` | (G₃) (G₄) (G₅) (G₆) (G₆′) (G₆″) |
| `Stage2/Objects.lean` | `b25ae4d10a87e499` | (G₈ₛ) (G₈ᵥ) (G₈ₚ) |
| `Stage2/Conditions.lean` | `dce0c0e61d0de83e` | (G₉) (G₁₀) (G₁₁) (G₁₂) |
| `Stage2/Meaning.lean` | `c5577b77aa96cda8` | (G-hom) (G-loc) (E-G₁) (E-G₂ₛ) (E-G₂ₖ) (E-G₂ₚ) (E-G₃) (E-G₅) |
| `Stage2/LevelOne.lean` | `d672ded79715b323` | (G-ex₁) (WI₁′) |
| `Stage2/LevelTwo.lean` | `915e2c1a4059fd0b` | (G-Σ₂) (G-Π₂) (G-ex₂) (WI₂) |
| `Stage2/Reusable.lean` | `d4db40ec01c25fc8` | (R-Π₄) |
| `Stage2/LSZ.lean` | `a0ef6ef674f49747` | (G-L₁) (G-L₂) (X₀) (X₁) (X₂) |
| `Check/Basic.lean` | `f8b073357ba5020a` | level 0 = (V₁); `withLevel`; placeholders unread; `leptonRep` facts; block PV non-vacuity; S2 vacuity |
| `Check/Rep.lean` | `bc4fe4e7eaa6a655` | kernel-checked 1PI order-4 VP contraction with a `fermionCt` on its loop, any flavour |
| `Check/Trivial.lean` | `65a0151cca38290e` | at `e = 0` every data is renormalized through every order (conditions satisfiable) |
| `Check/Axioms.lean` | `fb0a72821a4f645c` | `#print axioms` of the checks |
| `PACKET.lean.txt` | `af84a4778be3728c` | the nine packet files, in build order, with full hashes |

43 declarations: 25 definitions, 18 theorem goals (each `by sorry`).

## 1. Summary

- **The successor is a decoration of the frozen contraction machinery** (S1). `Grading κ`
  (levels of the counterterm vertices) and `Flavoring F κ` (unrestricted) decorate the frozen
  `Wick.VertexKind` sequences; the frozen vertex factor (V₁₉), contractions, routing (T₄), joint
  energy-first integral (T₉), `IsOnePI`, `fermionSign` are reused verbatim. The amplitude (G₃) is
  (F₅)'s text with only the coefficient and mass lookups substituted.
- **Order separation is definitional** (S3). Coefficients are `e^{2(k+1)} d` with `e`-free `d`;
  (G₆) `selectedPart` is the part of order *exactly* `K`; (G-hom) states it is `e^K` times its value
  at `e = 1`.
- **Conditions generic in the order** (S4, S10, D-54.3). (G₉)–(G₁₁) are stated at any order `2n`
  in limit form, choosing no form factor (existential, as (F₁₁) does for `Π`), so no `∃!` goal is
  needed before them. (G₁₂) bundles them through order `2n`.
- **Finding F1 (resolved by the ruling S2′, D-55 revised).** With full per-flavour counterterms
  (`rep = id`), a contraction with a counterterm vertex on a closed fermion loop is *not*
  integrable at fixed regulators, so its value (G₅) is `0` by Lean's default and the order-`e⁴`
  vacuum polarization (and everything built on it: (G-Π₂), the order-`e⁴` photon condition,
  (R-Π₄), set (a)) is mis-defined. Section 2. The draft therefore parametrizes the scheme by a map
  `rep : F → F` ((G₁₂)): S2 is `rep = id`; the adopted provisional ruling S2′ (D-55 revised) is
  `leptonRep` ((G₁₂′)): each physical lepton on shell at its own mass, its regulators sharing its
  counterterms, with `d_m · M_f` on a regulator line.
  Every scheme-neutral statement holds for every `rep`; the three statements that need the loop
  sums to cancel ((G-Π₂), (G-ex₂), (X₁)) carry explicit per-block Pauli–Villars hypotheses, which
  are unsatisfiable for `rep = id` (proved: `Check/Basic.blockPV_id_coeff`) and are (HM₂)'s
  conditions for `leptonRep` (proved: `Check/Basic.leptonFlavors_blockPV`).
- **Exit test** (S8): (X₁) charge non-renormalization at order `e⁵` in LSZ form, and (X₂) the
  two-loop LSZ lift of (HV₃)/(HM₂) with the target `A₁⁽⁴⁾ + Σ_ℓ A₂⁽⁴⁾(m/m_ℓ)`.
- **Reusable object** (S7): (R-Π₄), the regulator limit of `Π̂⁽⁴⁾(s)/e⁴` locally uniformly on the
  region with a uniform log² majorant, with the limit function existential; its identification
  with Källén–Sabry is deferred (no pinned source).
- **Revision after review** (section 11): S2′ adopted; (G-Σ₂) gains a differentiability clause
  feeding (G-ex₂); two new goals, the connected embedding (E-G₅) and the order-5 integrability
  companion (X₀); (R-Π₄)'s domain stated.
- **Elaboration**: all nine packet files and four check files exit 0; the only warnings are the
  18 `declaration uses 'sorry'` of the theorem goals. Section 6.

## 2. Finding F1: per-flavour counterterms break per-contraction integrability

**Claim.** Under S2, let `C` be the order-`e⁴` two-photon contraction of `Check/Rep.lean`: a
closed loop `0 → 1 → 2 → 0` with two `gauge` vertices and one `fermionCt` vertex. Its regulated
integrand (G₄) is, for the loop momentum `ℓ`,
`Σ_g c_g e⁴ tr[γ^μ S_g(ℓ) γ^ν S_g(ℓ+k) (d₂ g 0 (ℓ̸+k̸) + d_m g 0 M_g) S_g(ℓ+k)]`.
At large `ℓ` the `d₂` term is `(Σ_g c_g d₂ g 0) · a(ℓ̂)/|ℓ|² + (Σ_g c_g d₂ g 0 M_g²) · O(|ℓ|⁻⁴) +
(Σ_g c_g d_m g 0 M_g²) · O(|ℓ|⁻⁴) + O(|ℓ|⁻⁶)` with `a ≠ 0` (the trace is `ℓ²`-weighted
`ℓ^μ ℓ^ν`/`g^{μν}` structure; the odd-in-`M` terms vanish by the trace). The energy integral
converges, but the resulting spatial integrand decays like `|ℓ⃗|⁻¹` in ℝ³: not integrable unless
`Σ_g c_g d₂ g 0 = 0`, and then the `|ℓ|⁻⁴` terms need `Σ_g c_g M_g² d_{2,m} g 0 = 0`.

- With per-flavour on-shell values these sums do not vanish: the one-loop `δ₂` and `δ_m` of flavour
  `g` depend on `ln M_g` (`δ₂ ∋ ln(m_γ²/M_g²)`, `δ_m ∋ ln(Λ²/M_g²)`), so `Σ_g c_g d₂ g 0 ∝
  Σ_g c_g ln M_g² ≠ 0` for every admissible regulator set.
- The same holds for the `gaugeCt` insertion (`Σ_g c_g d₁ g 0`). The `δ₁`/`δ₂` cancellation of
  `B4-CHECK.md` §2 is real but happens *across* contractions (different `κ`), while the frozen
  value prescription (T₁₀)/(F₇)/(G₅) integrates each contraction separately and returns `0` for a
  non-integrable one.
- With block-shared counterterms (`leptonRep`) every sum is `d_block · Σ_{g ∈ block} c_g M_g^{2j}`,
  `j = 0, 1`, which vanishes by the block's two Pauli–Villars conditions. The genuine two-loop
  bubble has overall degree `0` (Pauli–Villars photon), lowered to `−2` by `Σ c_g = 0`, so by
  power counting it needs only `Σ c_g = 0`; the second condition is needed by the one-loop bubbles
  and the counterterm insertions (section 8, R2).
- Physics of S2′: each physical lepton keeps its exact on-shell pole (the muon is renormalized at
  `m_μ`); the regulator fermions of a block get `δm_ℓ · M_f`, the "universal `Z_m`" variant V2 of
  `B4-CHECK.md` §5, restricted to the block. B4 found V2 Λ-independent with a residue
  `∝ (m/M)² ln(M/m)` that vanishes as `M → ∞`, which is the last limit (D-37.4), so the D-37
  limits exist. The B4 objection to V2 (it shifts the muon pole) does not apply to the per-block
  version.

**Numerical check** (`../s2check/ct_integrability.py`, output `ct_integrability.out`). For the
counterterm contraction above, the spatial integrand after the energy integral, `G(R n̂)` at
`R = |ℓ⃗|`, has local log–log slopes `d ln|G| / d ln R` tending to `−1` under S2, `−5` under S2′,
and `−3` for the variant of S2′ with `d_m · m` (the lepton mass) on regulator lines; for the `00`
component `−3`, `−6`, `−4`. So S2 is not integrable in ℝ³ (`|ℓ⃗|⁻¹`), the `d_m · m` variant
decays only like `|ℓ⃗|⁻³` (also not integrable: the mass counterterm then escapes the second
Pauli–Villars cancellation), and S2′ decays like `|ℓ⃗|⁻⁵`, integrable with the two block
conditions. `setA_s2prime.py` checks that the set (a) residue under S2′ is
Λ-independent and vanishes as `M → ∞`. The author adopted S2′ (D-55 revised); the earlier
question Q1 is closed.

## 3. Provisional rulings (overnight mode, author approval pending)

| # | Ruling adopted | Where |
| --- | --- | --- |
| S1 | grading as a decoration over frozen `VertexKind` | (G₂′), (G₃) |
| S2′ | **D-55 revised (provisional, author approval pending): per-lepton-block counterterms.** Data stored per flavour `d_i : F → ℕ → ℝ`, flavour-`f` conditions = the open-line conditions with `openLine := f`, `d₃` shared; the scheme is the parameter `rep` of (G₁₂), and the adopted scheme is `rep = leptonRep` (G₁₂′): each lepton on shell at its own mass, its two regulator fermions carrying its `d₁, d₂, d_m`, with `d_m · M_f` on a regulator line ((G₃) reads `Φ.mass fl`). The literal S2 (`rep = id`) is expressible but not used (F1) | (G₀), (G₃), (G₈), (G₉)–(G₁₂), (G₁₂′) |
| S3 | coefficients `e^{2(k+1)} d k`, `d` free of `e` | (G₀), (G₃), (G-hom) |
| S4 | charge condition on the graded vertex at `q = 0`; Ward identity as a theorem | (G₁₀), (WI₁′), (WI₂) |
| S5 | substitution with family-restricted conditions | prepared only: (G₆) takes a selection that may read the grading; shares deferred (D2) |
| S6 | `IsPhotonChain (ins : List ℕ)` | deferred to the set (a) packet (D1) |
| S7 | reusable objects as anchors with fixed-regulator, limit and majorant clauses | (G-Π₂) (fixed regulator), (R-Π₄) (limit, majorant) |
| S8 | LSZ lift (D-44.1) as the Stage 2 exit test | (G-L₁), (G-L₂), (X₁), (X₂) |
| S9 | exact per-set targets | (X₂) uses the exact `a1Four`, `a2Four`; set targets are later packets |
| S10 | generic algebraic `∃!` step plus per-level analytic inputs | the generic step is a **planned helper** (`QED.GradedProof`), not an anchor: its premises would be proof obligations; anchors are the per-level `∃!` goals (G-ex₁), (G-ex₂) |
| S11 | namespace `QED.Graded` | all; intended frozen directory `QED/Frozen/Graded/` |

Also used: D-54.3 (generic in the loop order: all definitions and (G₉)–(G₁₂) take `n`); D-13
(provider binder convention: every goal's binders precede the colon); D-37.4/D-49.2 (limit order and
the single threshold `R_M`) in (R-Π₄), (X₂); D-36.1 (route A, no new regularization).

No new scope ruling of the D-52 kind is needed: every Stage 2 sum ((G₈) at orders ≤ 5, the
order-`e⁵` connected function) has at most two loops.

## 4. Declarations

Intended frozen path: `QED/Frozen/Graded/<File>.lean`, one declaration per file; providers in
`QED/Provider/Graded/`, helpers in `QED/GradedProof/` (never in `QED.Graded`). Sources: SRED =
`srednicki-draft`; MEMO = Stage 2 memo; B4 = `B4-CHECK.md`. "Imports" lists the direct frozen
dependencies (the freezer prunes transitively).

### 4.1 Definitions (25)

| Label | Name | File | Meaning | Source / decisions | Direct deps |
| --- | --- | --- | --- | --- | --- |
| G₀ | `Counterterms` | `Counterterms` | `d₁ d₂ dm : F → ℕ → ℝ`, `d₃ : ℕ → ℝ`; `Z_i − 1 = Σ_k e^{2(k+1)} d_i k` | SRED (62.2)–(62.3); MEMO §2.1; S2′ (D-55 revised), S3; plan Q5 (ii) | Mathlib real |
| G₀′ | `Counterterms.withLevel` | `CountertermsWithLevel` | replace level `k` by `(x, y)` | as (Z₆), (Z₉) replacing `Params` fields | G₀ |
| G₁ | `Flavoring` | `Flavoring` | `FermionVertex κ → F`, unrestricted | MEMO §2.2; B4 §1; S2 | V₃ |
| G₁′ | `fermionFlavor` | `FermionFlavor` | externals `Φ.openLine`, vertex `t` `φ t` | (F₂) | F₀, G₁ |
| G₁″ | `Preserves` | `Preserves` | `σ` preserves flavour | (F₃); D-22 | X₃, G₁′ |
| G₁‴ | `loopWeight` | `LoopWeight` | `∏_loops c_{flavour}` | (F₄) | X₆, G₁′ |
| G₂ | `CtVertex` | `CtVertex` | `{t // κ t ≠ gauge}` | MEMO §2.2 | V₀ |
| G₂′ | `Grading` | `Grading` | `CtVertex κ → ℕ` | S1 | G₂ |
| G₂″ | `gradedOrder` | `GradedOrder` | `Σ (κ t).order + Σ_ct 2 g t` | (V₁); D-19 | V₁, G₂′ |
| G₁₂′ | `leptonRep` | `LeptonRep` | each flavour of (L₁) ↦ its physical lepton | F1; S2′ (D-55 revised); D-49.4 | none |
| G₃ | `contractionAmplitude` | `ContractionAmplitude` | (F₅) with per-vertex `e^{2(k+1)}d`, `M_f`; placeholders unread | SRED rule 9, (62.2)–(62.3); S1; (F₅) | V₁₉, T₅, T₆, A, B |
| G₄ | `regulatedAmplitude` | `RegulatedAmplitude` | flavour sum with weights | (F₆); D-22 | G₃, G₁″, G₁‴ |
| G₅ | `contractionValue` | `ContractionValue` | `(2π)^{-4L}` × (G₄), joint energy-first | (F₇); D-37.5 | G₄, T₂, T₄, T₉ |
| G₆ | `selectedPart` | `SelectedPart` | order-exactly-`K` sum over `N, κ, g` and selected `C`, `1/N!`, sign | SRED (58.17)–(58.18); (F₈), (C₂); plan Q5 (ii) | G₅, G₂″, X₅ |
| G₆′ | `onePIPart` | `OnePIPart` | (G₆) with `IsOnePI` | (F₈) | G₆, X₁₈ |
| G₆″ | `connectedPart` | `ConnectedPart` | (G₆) with attached and connected | (X₂₉); D-23.1 | G₆, X₁₆, X₁₇ |
| G₈ₛ | `selfEnergyPart` | `SelfEnergyPart` | order-`2n` self-energy, flavour `f` | SRED (62.27)–(62.28); (Z₁) | G₆′ |
| G₈ᵥ | `vertexPart` | `VertexPart` | order-`(2n+1)` vertex, flavour `f` | SRED (62.39); (F₉) | G₆′ |
| G₈ₚ | `vacuumPolarizationPart` | `VacuumPolarizationPart` | order-`2n` VP | SRED (62.4), (62.12); (F₁₁) | G₆′ |
| G₉ | `IsOnShellAt` | `IsOnShellAt` | covariant limit near shell, `Σ(−M) = Σ'(−M) = 0` | SRED (62.27), (62.36)–(62.38); (Z₅); D-25 | G₈ₛ |
| G₁₀ | `IsChargeNormalizedAt` | `IsChargeNormalizedAt` | `w V^{(2n+1)}(p,p) u → 0` | SRED (63.1)–(63.2); (K₀); S4 | G₈ᵥ |
| G₁₁ | `IsPhotonOnShellAt` | `IsPhotonOnShellAt` | VP → 0 at lightlike `k` | SRED (62.11); (F₁₁) | G₈ₚ |
| G₁₂ | `IsRenormalizedThrough` | `IsRenormalizedThrough` | constancy on `rep` classes below level `n`; (G₉)–(G₁₁) at orders `2..2n` for `rep`-fixed flavours | S2′ (D-55 revised: `rep = leptonRep`), S4; F1 | G₉–G₁₁ |
| G-L₁ | `IsLSZAmplitudePart` | `IsLSZAmplitudePart` | iterated limit of the sandwiched order-`K` connected function | SRED (41.17), (41.25); (L₁)/(L₂); D-23, D-29; S8 | G₆″, spinors |
| G-L₂ | `IsSpinFormFactorPair` | `IsSpinFormFactorPair` | (63.18) for a spin-indexed amplitude | SRED (63.18); (H₀) | spinors, `lorentzGen` |

### 4.2 Theorem goals (18)

| Label | Name | File | Statement (one line) |
| --- | --- | --- | --- |
| G-hom | `selectedPart_eq_pow_mul` | `SelectedPartEqPowMul` | (G₆) at `e` = `e^K` · (G₆) at `e = 1` |
| G-loc | `selectedPart_congr` | `SelectedPartCongr` | (G₆) at order `K` reads only levels with `2k + 2 ≤ K` |
| E-G₁ | `onePIPart_eq_onePIFunction₂_sub` | `OnePIPartEqOnePIFunctionSub` | level-0 data `= P.δ/e²`, no higher levels, `nf ≥ 1`, `K+1 ≤ 2nf+nA+3`: (G₆′) = (F₈)(K+1) − (F₈)(K) |
| E-G₂ₛ | `isOnShellAt_one_iff` | `IsOnShellAtOneIff` | (G₉) at `n = 1` ⟺ (Z₅) at mass `M_f`, `δ = e² d` |
| E-G₂ₖ | `isChargeNormalizedAt_one_iff` | `IsChargeNormalizedAtOneIff` | (G₁₀) at `n = 1` ⟺ (K₀) at mass `M_f`, `Z₁ = 1 + e² d₁ f 0` |
| E-G₂ₚ | `isPhotonOnShellAt_one_iff` | `IsPhotonOnShellAtOneIff` | (G₁₁) at `n = 1` ⟺ (F₁₁) with `δ₃ = e² d₃ 0` |
| E-G₃ | `vertexPart_two_eq` | `VertexPartTwoEq` | order-5 graded vertex = (F₉) + `e⁵ d₁ 1 γ^μ` |
| E-G₅ | `connectedPart_eq_connectedFunction_sub` | `ConnectedPartEqConnectedFunctionSub` | T1's flavours, level-0 data `= P.δ/e²`, no higher levels, `K+1 ≤ 2nf+nA+1`: (G₆″) = (X₂₉)(K+1) − (X₂₉)(K) |
| G-ex₁ | `existsUnique_withLevel_zero` | `ExistsUniqueWithLevelZero` | `∃!` level-0 data renormalized through `e²` (any `rep`) |
| WI₁′ | `d₁_eq_d₂_zero` | `WardIdentityZero` | `d₁ f 0 = d₂ f 0` |
| G-Σ₂ | `selfEnergyPart_two_existsUnique` | `SelfEnergyPartTwoExistsUnique` | order-`e⁴` SE: (T₉′) for every term; `∃!` covariant form below `M_f + min(m_γ, Λ, 2m₀)`; for every `A, B` with the limit property, `z ↦ A(−z²)z + B(−z²)M_f` differentiable at `−M_f` |
| G-Π₂ | `vacuumPolarizationPart_two_existsUnique` | `VacuumPolarizationPartTwoExistsUnique` | order-`e⁴` VP, block scheme: (T₉′) for every term; `∃!` transverse form on `s > −4m₀²` |
| G-ex₂ | `existsUnique_withLevel_one` | `ExistsUniqueWithLevelOne` | given (G₁₂) through `e²`: `∃!` level-1 data renormalized through `e⁴` |
| WI₂ | `d₁_eq_d₂_one` | `WardIdentityOne` | `d₁ f 1 = d₂ f 1` from flavour-`f` conditions at orders 2, 4 |
| R-Π₄ | `vacuumPolarizationPart_two_lepton_limit` | `VacuumPolarizationPartTwoLeptonLimit` | `∃ Π_∞, C`: `Π̂⁽⁴⁾/e⁴ → Π_∞` on compacts in the D-37 order, `|Π̂⁽⁴⁾/e⁴| ≤ C(1+ln(1+s/m²))²`; limit for `s > −4m²`, majorant for `s ≥ 0` (timelike above threshold deferred, Q6) |
| X₀ | `jointEnergyFirstIntegrable_connectedPart_five` | `JointEnergyFirstIntegrableConnectedPartFive` | block scheme, `ε > 0`: every attached, connected `(1,1)` contraction at graded order 5 satisfies (T₉′) |
| X₁ | `isLSZAmplitudePart_five_self` | `IsLSZAmplitudePartFiveSelf` | order-5 LSZ amplitude at `(p, p)` exists and is 0 |
| X₂ | `isSpinFormFactorPair_lszFive_lepton_pauli_limit` | `LszFiveLeptonPauliLimit` | (HM₂) with the order-5 LSZ amplitude and (G₁₂) in the `leptonRep` scheme |

### 4.3 Binder classification (main goals)

| Binder | Class |
| --- | --- |
| `P`, `Φ`, `D`, `f`, `rep`, `n`, `K`, `Sel` | typing data (`P`'s `δ`, `m`, `M`, `c` fields unread by the graded model) |
| `he : P.e ≠ 0` | standing assumption (uniqueness of counterterms; `F₂/e⁴` is a coefficient) |
| `hmass`, `hm₀`, `hf`, `hmγ`, `hΛ` | standing assumptions (positive masses and regulators; `m₀` a common lower mass bound, typing data for the threshold region) |
| `hPV₁`, `hPV₂` (total or per block), `hrep` | rulings D-22, D-49.4, and the scheme choice (F1/Q1) |
| `hD` (constancy at level 0 in (G-Π₂) and (X₀)), `hD : IsRenormalizedThrough …` | source premises (the on-shell scheme; the constancy is the first clause of (G₁₂)) |
| `hε`, `hmom` of (X₀) | standing assumptions of (T₉′)-type companions ((HC₀) precedent: `ε > 0`, momentum conservation) |
| `h₁ h₂ hm h₃ hmass hD hD₃` of (E-G₁), (E-G₃), (E-G₅) | the identification of the frozen counterterms with the graded data (not obligations: they define the comparison) |
| (X₂), (R-Π₄) regulator binders | (HM₂)'s, unchanged (D-37.4, D-49.2) |

No goal has a proof obligation as a hypothesis: the analytic inputs of (G-ex₂) ((G-Σ₂) including
its differentiability clause at `z = −M_f`, (G-Π₂), the order-5 vertex at `q = 0`) are
conclusions of other goals, not premises.

## 5. Design choices and their alternatives

- **Conditions in existential form (G₉).** The form factors are quantified (`∃ r > 0, ∃ A B`),
  not chosen, so the definition needs no prior `∃!` goal and is generic in `n`. For `M_f > 0` it
  is independent of the choice (docstring argument), and at `n = 1` it is equivalent to the frozen
  (Z₅) (E-G₂ₛ). Alternative: a frozen `∃!` per order and `.choose` (the T1 pattern); rejected
  because it would need an analytic theorem at every order before the definition.
- **A generic `selectedPart` (G₆)** with the selection as a parameter, and two named
  specializations, instead of copying (F₈)'s text twice (1PI, connected) and later a third time for
  families. The selection reads the grading (needed for set (c)/(e) shares, S5).
- **Placeholders in (G₃).** The level of a `gauge` vertex (`0`) and the flavour of a `photonCt`
  vertex (`Φ.openLine`) are dummy arguments of (V₁₉) that it does not read; proved in
  `Check/Basic` (`vertexFactor_gauge_indep`, `vertexFactor_photonCt_indep`). Alternative: a
  total grading on `Fin N` with gauge vertices forced to level 0, which adds a constraint to the
  sum; rejected.
- **Levels summed outside the value** (memo §2.3 choice point): the grading changes only scalar
  coefficients; outside is simpler.
- **The scheme parameter `rep`** (F1). Keeps S2 expressible (`rep = id`) and lets the author choose
  without redrafting. The block hypotheses are explicit in the three goals that need them.
- **(R-Π₄) with an existential limit** rather than a named Källén–Sabry function: exact now,
  and a later identification theorem can state `Π_∞ = Π_KS` with the same clauses (the limit is
  unique). The majorant is in the same statement so that `C` is uniform.
- **The exit test in predicate form** (G-L₁), (G-L₂) (the (HV₂)/(HV₃) pattern: `∃ M, … ∧ ∀ M, …`),
  avoiding an `∃!` goal and `.choose` for a new LSZ amplitude.

## 6. Elaboration

`sh build.sh <modules>` (one niced `lean` at a time against the repository oleans; log in
`elaboration.log`), from clean outputs:

| Module | Time | Peak RSS | Exit | Warnings |
| --- | --- | --- | --- | --- |
| Stage2/Data | 1.87 s | 1.42 GB | 0 | none |
| Stage2/Value | 1.96 s | 1.67 GB | 0 | none |
| Stage2/Objects | 1.78 s | 1.67 GB | 0 | none |
| Stage2/Conditions | 1.93 s | 1.67 GB | 0 | none |
| Stage2/Meaning | 2.04 s | 1.69 GB | 0 | 8 × `sorry` (goals) |
| Stage2/LevelOne | 1.80 s | 1.67 GB | 0 | 2 × `sorry` |
| Stage2/LevelTwo | 2.21 s | 1.68 GB | 0 | 4 × `sorry` |
| Stage2/Reusable | 2.10 s | 1.68 GB | 0 | 1 × `sorry` |
| Stage2/LSZ | 2.00 s | 1.69 GB | 0 | 3 × `sorry` |
| Check/Basic, Rep, Trivial, Axioms | 1.9–3.6 s | ≤ 1.71 GB | 0 | none; axioms `propext, Classical.choice, Quot.sound` |

(Revision build at `d3a2e60`, all outputs deleted first; the machine was loaded, so times are
about twice the first build's.)

No `axiom`, `native_decide`, `set_option`; lines ≤ 100 characters; every file is a module with
`public import` and `@[expose] public section`.

**Scratch evidence (`Check/`), all proved:**
- `gradedOrder_zero`: level 0 is (V₁); `withLevel_d₁`, `withLevel_d₃_self`.
- `vertexFactor_gauge_indep`, `vertexFactor_photonCt_indep`: the (G₃) placeholders are unread.
- `leptonRep_idem`, `leptonRep_eq_self_iff`, `sum_filter_leptonRep`, `leptonFlavors_blockPV`: the
  block hypotheses of (G-Π₂), (G-ex₂), (X₁) are (HM₂)'s Pauli–Villars conditions (non-vacuity).
- `blockPV_id_coeff`: under S2 (`rep = id`) those hypotheses force every `c_f = 0` (F1, formal).
- `exists_ct_on_loop`, `preserves_const` (`decide +kernel`): a 1PI order-`e⁴` two-photon
  contraction with a `fermionCt` on its closed loop exists and admits any loop flavour, so the
  successor really differs from (F₈) there (the B4 content, and the contraction of F1).
- `isRenormalizedThrough_e_zero`: at `e = 0` every part of order `≥ 1` vanishes and every data
  is renormalized through every order: the conditions are satisfiable, and the plumbing of
  (G₃)–(G₁₂) (order filter, `N = 0` term, record updates) works end to end.

## 7. Deferred, with reasons

| # | Item | Reason |
| --- | --- | --- |
| D1 | (G₁₃) `IsPhotonChain`, (E-G₄) chain embedding, (HC₆ₐ) | set (a) packet (Stage 3a); not needed by Stage 2 |
| D2 | (G₁₄) `ctVPShare`, (G₁₅) `vertexSetC`, the split theorem | set (c) packet (Stage 3c); (G₆) already accepts grading-reading selections |
| D3 | (R-Σ₄), (R-Γ₅) renormalized SE and vertex functions | no Stage 2 consumer; their region and IR clauses should be fixed by the set (c)/(e) insertion engines; stating them now would guess the interface |
| D4 | (R-δ) counterterm asymptotics `a ln²Λ + b lnΛ + c` | the coefficients come from the proofs; cannot be stated exactly now |
| D5 | (R-Π₆), (R-Λ), (G-ex₃), (WI₃) | four-loop inputs (memo §3); same definitions at `n = 3` |
| D6 | Källén–Sabry identification and spectral representation of (R-Π₄) | no pinned Källén–Sabry source in `docs/SOURCES.md`; needs signed-measure machinery |
| D7 | generic algebraic `∃!` step (S10) | helper, not anchor: its premises are the analytic inputs |
| D8 | Landé-factor and wave-packet lift ((H)'s response/source clauses) at two loops | beyond the form-factor exit test; can follow (X₂) |
| D9 | order-7 completeness in the graded model | Stage 5 (D-49 Q8) |

## 8. Risks

1. **R1 (F1, scheme).** Resolved provisionally: the author adopted S2′ = `leptonRep` (D-55
   revised; slopes in section 2). If the ruling were reversed to S2, (G-Π₂)'s integrability clause
   would be false for `rep = id` and the hypotheses of (G-Π₂)/(G-ex₂)/(X₀)/(X₁) unsatisfiable for
   flavour sets with a unit coefficient (`blockPV_id_coeff`); the `rep` parameter keeps the text
   unchanged either way.
2. **R2, two Pauli–Villars conditions at two loops.** The genuine order-`e⁴` VP integrands (and the
   order-5 photon-leg bubbles of (X₀)) are claimed integrable with two conditions per block. Power
   counting of the two-loop bubble (degrees of divergence in four dimensions per loop): the
   self-energy subgraph `−1`, the vertex subgraphs `−2`, the photon line with three fermion lines
   `−3`, all convergent by the photon regulator alone; the fermion loop alone at fixed photon
   momentum has degree `0` and needs `Σ c = 0` (its leading `ℓ⁻⁴` and `ℓ⁻⁵` coefficients are
   mass-independent); the overall degree is `0` (Pauli–Villars photon), lowered to `−2` by
   `Σ c = 0`. So by power counting the genuine two-loop bubble needs only `Σ c = 0`; the second
   condition is needed by the one-loop bubbles and the counterterm insertions. Not yet a proof (D-55 revised
   records it as the open risk), to check first in Phase 2.2.
3. **R3, regulator-fermion on-shell points.** Not needed under `leptonRep` (regulators are not
   renormalized on their own shell); under S2 the memo's estimate (on-shell point below
   threshold) stands unverified.
4. **R4, (E-G₁)/(E-G₅) ranges.** For (E-G₅) the range is (X₂₉)'s own, `K + 1 ≤ 2nf + nA + 1`
   (at most one loop, no counterterm on a closed loop since that needs order `≥ 2nf + nA + 2`).
   For (E-G₁): The "no counterterm on a closed loop" argument (`L ≥ 2` hence
   `K ≥ 2nf + nA + 4`) is a sketch; it fails for `nf = 0` (hence the hypothesis `1 ≤ nf`).
5. **R5, the (R-Π₄) majorant.** `C(1 + ln(1 + s/m²))²` uniform in the regulators beyond the
   thresholds is an estimate (one-loop PV-regulated VP saturates at `ln(M²/m²) ≤ ln(s/m²)` for
   `s ≫ M²`); log² leaves margin.
6. **R6, (X₁)/(X₂) leg terms.** The LSZ limit relies on `Σ(r)S(r) → Σ'(−m) = 0` on the `−m`
   eigenspace and on spinor projection on the other; standard but new for order `e⁴` legs.
7. **R7, uniformity of (R-Π₄) near threshold.** Avoided by compact intervals `[S₀, S]` with
   `S₀ > −4m²`.
8. **R8, implicit-lambda elaboration of `Sel`** (as Stage 1a R5): `fun C _ => IsOnePI C` elaborates
   to `fun {N} {κ} C _ => …`; checked by the build.

## 9. Open questions for the author

- **Q1 (closed).** Counterterm scheme: ruled S2′ = `leptonRep` (D-55 revised, provisional,
  author approval pending).
- **Q2 (adopted provisionally).** Keep `rep` as a parameter of (G₁₂).
- **Q3 (adopted provisionally).** (R-Π₄) with an existential limit now, the Källén–Sabry
  identification later.
- **Q4 (adopted provisionally).** Exit test: form factors only ((X₁), (X₂)).
- **Q5 (adopted provisionally).** A common lower mass bound `m₀`.
- **Q6 (new).** (R-Π₄) states the limit for `s > −4m²` (on compacts) and the majorant for `s ≥ 0`.
  Should the timelike region above the pair threshold (`s < −4m²` in the metric of (T₁), where
  `Π̂⁽⁴⁾` is complex) be added now? Recommended: defer. The planned consumers, the set (a) chain
  integral after the Wick rotation and the dispersive (spectral) form, do not evaluate it there.

## 10. Proof effort (estimates, files)

| Goal | Effort | Notes |
| --- | --- | --- |
| G-hom | 3–6 | multiplicativity of (V₁₉) in `e` per vertex, sum of orders = `K`, linearity of the integrals |
| G-loc | 2–4 | per-vertex level bound from `gradedOrder = K`; congruence through the sums |
| E-G₁ | 15–30 | flavouring bijection, no-counterterm-on-loop lemma (loop counting), order filter rearrangement |
| E-G₂ₛ, E-G₂ₖ, E-G₂ₚ | 6–12 each | via (E-G₁) at `K = 2, 3` and the sealed (Z₁), (Z₃′), (Y₁)-type identifications; (E-G₂ₛ) needs the region-independence argument |
| E-G₃ | 4–8 | (E-G₁) at level 0 plus the level-1 tree term and the 1PI exclusion of the other level-1 terms |
| G-ex₁ | 6–10 | from (E-G₂) and the sealed (Z₆), (Z₉), (K), (F₁₁) solutions; constancy via `rep` |
| WI₁′ | 2 | (E-G₂) and the sealed (WI₁) |
| G-Σ₂ | 45–80 | two-loop integrability (Phase 4 helpers, now with flavour-`f` open line and level-0 insertions), covariant form; differentiability at `z = −M_f` (real analyticity below threshold, differentiation under the integral) |
| G-Π₂ | 50–90 | **new**: two-loop VP integrability with PV blocks (R2), transversality at fixed regulators |
| G-ex₂ | 15–30 | generic affine step + analytic inputs ((G-Σ₂) with its differentiability clause, (G-Π₂), order-5 vertex at `q = 0`) |
| WI₂ | 15–30 | Ward–Takahashi identity at order `e⁴`/`e⁵` at fixed regulators |
| R-Π₄ | 50–100 | KS-type limit at two loops, decoupling of regulator blocks (V2 residue), majorant |
| E-G₅ | 10–20 | as (E-G₁) with the connected selection; the frozen `K ≤ 2nf + nA + 1` loop bound; no `nf ≥ 1` needed |
| X₀ | 40–70 | (G-Σ₂)/(G-Π₂) integrability plus the one-loop vertex, leg and tadpole terms and counterterm-on-loop bubbles under the block conditions |
| X₁ | 20–40 | LSZ leg analysis at order `e⁴`, photon-leg vanishing at `q = 0` |
| X₂ | 30–60 | (E-G₃) + (HM₂) + leg and photon-leg terms; `q² → 0` of the vertex × leg-bubble term |

Total about 315–590 files for Stage 2: the memo's 230–440, the scheme work of F1, and the two
new goals (E-G₅), (X₀).

## 11. Revision after review (2026-11-19, at `d3a2e60`)

Review verdict APPROVE WITH NITS; the author's ruling S2′ (D-55 revised). Changes:

| Declaration | Change |
| --- | --- |
| (G₀) `Counterterms` | docstring: rulings S2′ (D-55 revised) and S3; per-flavour storage constrained by `rep` of (G₁₂); `d_m · M_f` on regulator lines |
| (G₁₂) `IsRenormalizedThrough` | docstring: the adopted S2′ is `rep = leptonRep`; `rep = id` (S2) not used |
| (G-Σ₂) `selfEnergyPart_two_existsUnique` | **statement**: third conjunct, for all `A B : ℝ → ℂ` with the limit property on the region, `DifferentiableAt ℝ (fun z => A (-z ^ 2) * z + B (-z ^ 2) * M_f) (-M_f)` |
| (G-ex₂) `existsUnique_withLevel_one` | docstring: names the differentiability clause of (G-Σ₂) among its analytic inputs |
| (E-G₅) `connectedPart_eq_connectedFunction_sub` | **new goal** (`Meaning.lean`) |
| (X₀) `jointEnergyFirstIntegrable_connectedPart_five` | **new goal** (`LSZ.lean`) |
| (X₂) `isSpinFormFactorPair_lszFive_lepton_pauli_limit` | docstring: photon-leg terms vanish because `q² D(q²) → 0` at `m_γ > 0` with `q² → 0` first |
| (R-Π₄) `vacuumPolarizationPart_two_lepton_limit` | docstring: domain of the limit (`s > −4m²`) and majorant (`s ≥ 0`); Q6 |

The differentiability clause quantifies over every `A, B` with the limit property rather than
the unique `AB` of the second clause, because (G₉) quantifies over such `A, B` (on its own
neighbourhood `r`); on the overlap of the regions the two agree, so the clause is what (G-ex₂)
consumes. Its truth: below `(M_f + min(m_γ, Λ, 2m₀))²` the regulated two-loop form factors are
real-analytic in `s`, and `z ↦ −z²` maps a neighbourhood of `−M_f` into the region.

**Delta review (APPROVE WITH NITS), applied:**
1. (X₀) docstring: a counterterm on a closed loop is *made integrable* by the block conditions
   (the one-loop bubble then decays like `|ℓ⃗|⁻⁵`); the two-loop bubble's overall degree is `0`
   (regulated photon `k⁻⁴`), lowered to `−2` by `∑ c_f = 0`.
2. §2 and §8 R2: same correction; the genuine two-loop bubble needs only `Σ c = 0` by power
   counting, the second condition serves the one-loop bubbles and counterterm insertions.
3. (E-G₅) docstring: at `nf = nA = 1`, `K = 2` it identifies the order-`3` input of (G-L₁) with
   the input of the frozen (L₁), (X₂₉) at order `3`, minus its order-`1` tree term.
4. (X₀) **statement**: option (a), `hD` at level `0` only,
   `(hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)`;
   the docstring says that level-`≥ 1` counterterms enter only tree contractions at this order.

**Freezer dry run** (`../s2freeze/`): `spec.py` (43 entries; decision D-57, `ID_PREFIX` `graded`,
`CONTRACT_PREFIX` `qed_dev.packetG1`, provisional approval block; generated by `gen_spec.py`),
`freeze.py` and `closure.py` copied from `../s1afreeze/` with three changes (`--out DIR` for dry
runs outside the repository; continued header open lines; pruning through packet files and public
imports only). `python3 freeze.py spec.py --no-manifest --out out` wrote 43 frozen files and 18
provider stubs under `out/`; `buildout.sh` elaborated all 61 against the repository oleans
(through the symlink overlay `ov/`): every file exits 0, the only warnings are the 18
`declaration uses 'sorry'` of the frozen theorem anchors, and no line exceeds 100 characters. The
manifest step was not run.
