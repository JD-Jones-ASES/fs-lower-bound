# fs-lower-bound-lean

A Lean 4 / Mathlib formalization of the construction behind

> liminf_{N→∞} log D(N) / log N ≥ α∞ = 0.753741541837329405…

where D(N) is the largest size of a subset of {1,…,N} no two of whose elements differ by a
nonzero perfect square. The mathematics — definitions, the one new lemma (the composite
even-digit lift), the pool, and the closed form — lives in the companion repository
[fs-lower-bound](https://github.com/JD-Jones-ASES/fs-lower-bound), whose `README.md` is
the source this formalization follows and whose `verify.py` checks the same finite data in
Python. This repository is the machine-checked version of that chain, built in stages.

## What is proved (Stages 1, 2, 3 and 4)

Every theorem in all four lists below is fully proved, with no placeholder and no added
axioms. Nothing in this repository is stated ahead of its proof: `lake build` emits no
warning, the axiom audit reaches every public declaration, and CI rejects a placeholder
proof in any `.lean` file of the repository.

### Stage 1 — the certified data

| Theorem | File | Content |
|---|---|---|
| `paley3` … `paley103` (ten) | `FsLowerBound/PaleyChains.lean` | each named tuple `chain3` … `chain103` is a Paley chain: p prime, p ≡ 3 (mod 4), entries distinct residues, every forward difference a nonzero square mod p |
| `cert235_valid` | `FsLowerBound/Certificates.lean` | `ValidRankedSupport 235 cert235 11` — the 17-vertex support on 235 = 5·47 with its exhibited ranking of height 11 |
| `cert299_valid` | `FsLowerBound/Certificates.lean` | `ValidRankedSupport 299 cert299 12` — the 19-vertex support on 299 = 13·23 with a ranking of height 12 |
| `cert235_height_attained`, `cert299_height_attained`, `cert235_ranks_complete`, `cert299_ranks_complete` | `FsLowerBound/Certificates.lean` | the claimed heights are attained (largest rank 10 resp. 11), and every rank below the height occurs. With the `_valid` theorems (ranks strictly below 11 resp. 12) the rank sets are exactly {0,…,10} and {0,…,11}, so "height 11" and "height 12" are theorems rather than prose |
| `pool_mem_paley3` … `pool_mem_paley103`, `pool_mem_cert235`, `pool_mem_cert299` | `FsLowerBound/Bridges.lean` | each of the eleven pool blocks *is* the certified object it stands for. The triples are built out of `chainP.length`, and out of `cert235.length` / `cert299.length` with the very height literals `cert235_valid` / `cert299_valid` certify — never out of retyped numerals |
| `pool_length`, `pool_coprime` | `FsLowerBound/Bridges.lean` | the pool has exactly eleven blocks, so those eleven memberships account for all of them; and its moduli are pairwise coprime, the hypothesis under which the blocks combine |
| `six_not_unit_square_mod_15` | `FsLowerBound/Defs.lean` | Remark 1 as a negative control: no *unit* squares to 6 mod 15, while 6 nonetheless is a nonzero square mod 15 (via the non-unit z = 6, the `example` beside it) |
| `sdfFinset_iff` | `FsLowerBound/Defs.lean` | the `Finset` and `Set` forms of square-difference-freeness agree |

`pool` is a list of bare numerals, and a typo in it would leave every other theorem in the
repository true and the constant wrong. The bridge theorems close that seam: they are the
only place where the numbers in `pool` and the certified data are forced to be the same
numbers.

`ValidRankedSupport m sup H` is the "square-DAG with valid ranking" condition: distinct
vertices below m, ranks below H, and a strict rank drop along every ordered pair whose
difference lies in Q_m. Acyclicity is not a separate hypothesis — it follows from the
existence of the ranking. Q_m is the **full** image of squaring mod m with 0 removed, so
non-unit squares are arcs; the unit-only variant would make the lift lemma false (Remark 1
of the source note).

The chain at p = 23 is proved but is not in the pool: 23 divides 299. It is here because
Krachun's constant α★ uses it.

### Stage 2 — Lemma A, the composite even-digit lift

| Theorem | File | Content |
|---|---|---|
| `RankedBlock.of_validRankedSupport`, `cert235_rankedBlock`, `cert299_rankedBlock` | `FsLowerBound/RankedBlocks.lean` | the bridge from the decidable *list* form `ValidRankedSupport` — the form `decide` can check in the kernel — to the *functional* form `RankedBlock P C h H` the lift quantifies over, and the two certificates carried across it |
| `lemmaA` | `FsLowerBound/LemmaA.lean` | §5 of the source note: for square-free m ≥ 2, a ranked block on Z/mZ of height H₀ lifts to a ranked block on Z/m^{2e}Z — the residues whose *even* base-m digits all lie in S — of height H₀^e |
| `step0_exact_dvd` … `step5_rank_drop` | `FsLowerBound/LemmaA.lean` | the step spine, one named lemma per step of §5 so the audit maps Lean to prose one-to-one: r = v_m(d) exactly; the leading digit without borrows; r even (this is where square-freeness is used); m^j ∣ z; the leading digit is a nonzero square mod m; the geometric rank drop |
| `liftBlock_card` | `FsLowerBound/LemmaA.lean` | the size count `(liftBlock m e S).card = (m * S.card) ^ e` — e free odd digits and e digits from S — in the brief's pinned form, with no side condition on m |
| `cert235_lift_rankedBlock`, `cert299_lift_rankedBlock` | `FsLowerBound/LemmaA.lean` | the two composite blocks lifted, at general e ≥ 1: height 11^e on Z/235^{2e}Z and height 12^e on Z/299^{2e}Z |
| `cert235_lift_card`, `cert299_lift_card` | `FsLowerBound/LemmaA.lean` | their sizes, at general e: (235·17)^e and (299·19)^e |

`lemmaA` is the one lemma of the source note that is new rather than quoted, and it is the
only place in the chain where square-freeness of the modulus is used. It enters at exactly
two points: Step 2, where v_m(d) is a minimum of prime valuations and therefore even, and
Step 3, where the per-prime bounds reassemble into m^j ∣ z. Step 2's two coordinate cases
and all of Step 4 hold for any m ≥ 2. The four `cert*_lift_*` corollaries are stated at
general `e` because that is the form Stage 4's exponent arithmetic consumes.

### Stage 3 — Lemmas B and C, proved rather than cited

| Theorem | File | Content |
|---|---|---|
| `lemmaB_sdf` | `FsLowerBound/LemmaB.lean` | §1.3 of the source note (Krachun's Lemma 4): for `P = n²` a perfect square, a ranked block `C` on `Z/PZ` of height `H` and any word length `L ≥ 1`, the set `integerSet P L H C h` of integers is square-difference-free |
| `word_step0_exact_dvd` … `word_step5_rank_drop` | `FsLowerBound/LemmaB.lean` | the step spine, one named lemma per move of §1.3, as Stage 2 does for §5: `P^j` divides `Y − X` exactly; the leading digit without borrows; `P^j ∣ k²`; `q^j ∣ k`; the leading digit is a square mod `P`; the rank drop. `word_step3_root_split` is where `P = q²` is used — and it is *all* that is used, replacing Stage 2's square-freeness argument outright |
| `integerSet_subset` | `FsLowerBound/LemmaB.lean` | the interval: `A_L ⊆ {1, …, (P·H)^L}` — the translate by one supplies the lower end, `X ≤ P^L − 1` and `h_L ≤ H^L − 1` the upper |
| `integerSet_card` | `FsLowerBound/LemmaB.lean` | the size: `|A_L| = |C|^L`, from injectivity of the digit-string embedding and `wordBlock_card` |
| `le_D_of_sdf` | `FsLowerBound/LemmaB.lean` | the `D`-link: a square-difference-free subset of `{1, …, N}` is one of the sets `D N` is a supremum over, so its size bounds `D N` below |
| `lemmaB_card_le_D` | `FsLowerBound/LemmaB.lean` | the four composed, in the one form Stage 4 consumes: `|C|^L ≤ D ((P·H)^L)` |
| `lemmaC` | `FsLowerBound/LemmaC.lean` | §1.5 (Krachun's Lemma 5), binary form: ranked blocks on coprime moduli `P`, `Q` glue by the Chinese remainder theorem to a ranked block on `P·Q`, with supports multiplying, ranks adding, and height `H_p + H_q − 1`. No perfect-square hypothesis appears, and none is needed — H5.2 |
| `crtBlock_card` | `FsLowerBound/LemmaC.lean` | `|C| = |C_p|·|C_q|`, via `crt_injOn` and `crt_image`. No positivity hypothesis: coprimality forces the other modulus to `1` when one is `0` |
| `trivialBlock_rankedBlock`, `glueList_fst`, `glueList_mem_lt`, `glueList_height`, `glueList_card`, `glueList_rankedBlock` | `FsLowerBound/LemmaC.lean` | the fold: `glueList` is `lemmaC` folded with `List.foldr` from the block on `Z/1Z`, so the eleven-block pool is stated once instead of chaining ten binary applications. The glued modulus is `Π m_i`, the glued size `Π |C_i|`, and the glued height the closed form `H = 1 + Σ (H_i − 1)` |

Lemma B is where the perfect square enters and where square-freeness leaves: `P = q²`
makes `P^j = (q^j)²` a square outright, so `(q^j)² ∣ k²` gives `q^j ∣ k` for every
positive `q` in one application of `Nat.pow_dvd_pow_iff`. That single lemma replaces the
two-case `p`-adic valuation argument Stage 2 needed. Lemma C, conversely, uses neither:
its interface is `RankedBlock` on both sides, and carrying the perfect-square property
across the product is the caller's bookkeeping, which belongs to Stage 4.

The fold is offered, not imposed: Stage 4 may use `glueList_rankedBlock` or chain `lemmaC`
ten times by hand, and the two routes are interchangeable.

### Stage 4 — the endgame

| Theorem | File | Content |
|---|---|---|
| `paleyCert3_valid` … `paleyCert103_valid` | `FsLowerBound/PaleyBlocks.lean` | the nine Paley chains with an exhibited ranking attached — rank `t − 1 − i` down the chain — re-checked as `ValidRankedSupport` by `decide`, then turned into `RankedBlock`s with their support sizes and residue bounds |
| `paleyCert3_chain` … `paleyCert103_chain`, `paleyCert3_height_exact` … `paleyCert103_height_exact` | `FsLowerBound/PaleyBlocks.lean` | each certificate forgets its ranks to the chain of `FsLowerBound/PaleyChains.lean` — `paleyCertP.map Prod.fst = chainP`, by `rfl`, so the provenance is a theorem and not a comment — and each claimed height is *exact*: `ValidRankedSupport p paleyCertP (t−1)` is `decide`d **false**, so rank `t − 1` occurs |
| `baseBlocks`, `baseBlocks_pool` | `FsLowerBound/Construction.lean` | the eleven certified blocks as one list, and the seam that ties them to `pool`: reading `(m, |S|, H)` off the list returns `pool` on the nose, with every numeral coming from a certificate rather than being retyped |
| `stageModulus`, `stageCard`, `stageHeight` | `FsLowerBound/Construction.lean` | (2.5′) of the source note, for a multiplicity vector `E`: `P = Π mᵢ^(2eᵢ)`, `\|C\| = Π (mᵢtᵢ)^eᵢ`, `H = 1 + Σ (Hᵢ^eᵢ − 1)`, each proved equal to the corresponding field of `glueList (stageBlocks E)` |
| `stageModulus_eq_sq`, `stage_rankedBlock`, `stage_D_bound` | `FsLowerBound/Construction.lean` | the stage modulus is `(Π mᵢ^eᵢ)²`; the glue is a ranked block; and Lemma B applied to it: `stageCard E ^ L ≤ D ((P·H)^L)` for `L ≥ 1` |
| `D_mono`, `D_le`, `alloc`, `one_le_alloc` | `FsLowerBound/Asymptotics.lean` | `D` is monotone and `D N ≤ N`, and §6.2's allocation `eᵢ(U) = ⌊U / log Hᵢ⌋` with `eᵢ(U) log Hᵢ ∈ (U − log Hᵢ, U]` |
| `log_stageModulus`, `log_stageCard`, `pow_height_le_stageHeight`, `stageHeight_le_of_forall_le`, `log_stageHeight_lower`, `log_stageHeight_upper` | `FsLowerBound/Asymptotics.lean` | the two logarithm exchanges `log P = 2 Σ eᵢ log mᵢ` and `log \|C\| = Σ eᵢ log(mᵢtᵢ)`, and §6.2's height sandwich `maxᵢ Hᵢ^eᵢ ≤ H ≤ 11 maxᵢ Hᵢ^eᵢ` in the form `U − log 12 ≤ log H ≤ U + log 11` |
| `stageExponent`, `tendsto_stageExponent`, `exists_stage_exponent_gt` | `FsLowerBound/Asymptotics.lean` | §6.2: the exponent `α(e) = log \|C\| / log(P H)` of a stage tends to `alphaInf` along the allocation, so below `alphaInf` there is an honest finite stage. Numerator and denominator are `Θ(U)` with additive `O(1)` errors, and the ratio is squeezed |
| `stage_pointwise`, `sdf_pointwise_internal`, `sdf_liminf_internal` | `FsLowerBound/Asymptotics.lean` | §6.3: `B^L ≤ N < B^(L+1)` at `L = ⌊log N / log(P H)⌋` carries the count at the special values to every `N`, giving `D N ≥ N^ρ` eventually for each `ρ < alphaInf`; the liminf statement is then read off the family |
| `lt_log_div_log`, `log_div_log_lt` | `FsLowerBound/Numeric.lean` | a rational bound on `log a / log b` *is* a comparison of natural powers: `p/q < log a / log b ↔ bᵖ < aᑫ` for `a, b ≥ 2` |
| `alphaInf_gt_internal` | `FsLowerBound/Numeric.lean` | `0.7537 < alphaInf`, from twenty-two such bounds — one lower bound on `log(mᵢtᵢ)/log Hᵢ` and one upper bound on `log mᵢ/log Hᵢ` per block, each a single kernel comparison of naturals — assembled by rational arithmetic. No transcendental numerics anywhere |

## Pinned targets

`FsLowerBound/Pool.lean` defines `pool` (the eleven blocks as triples (m, t, H)) and
`alphaInf` (the closed form evaluated on it); `FsLowerBound/Statements.lean` states the
three targets:

- `sdf_liminf_ge : alphaInf ≤ Filter.liminf (fun N => Real.log (D N) / Real.log N) Filter.atTop`
- `sdf_pointwise (ρ) (hρ : ρ < alphaInf) : ∀ᶠ N in atTop, (N : ℝ) ^ ρ ≤ (D N : ℝ)`
- `alphaInf_gt : (0.7537 : ℝ) < alphaInf`

All three are **proved**, and all three are in the axiom audit. The third is discharged by
`FsLowerBound/Numeric.lean`; the first two delegate to `sdf_liminf_internal` and
`sdf_pointwise_internal` in `FsLowerBound/Asymptotics.lean`, which are those statements
verbatim, so `Statements.lean` is wiring and proves nothing itself. The delegation is not a
formality: it is what kept the pinned statements byte-identical across the four stages while
the proof work moved around behind them.

`FsLowerBound/Bridges.lean` ties `pool` to the certified data, so the pinned targets are
stated about the eleven blocks this repository actually checked.

## Staging

| Stage | Content | Status |
|---|---|---|
| 1 | Definitions, the ten Paley chains, the two composite certificates, the pool bridges and height attainments, the Remark 1 negative control, the axiom audit, targets pinned | done |
| 2 | Lemma A — the composite even-digit lift: the `RankedBlock` bridge, the six-step spine, the lift itself, the size count, and the two certificates lifted at general `e` | done |
| 3 | Krachun's Lemmas 4 and 5, proved rather than cited: Lemma B (the §1.3 spine, the square-difference-free set, its interval and size, the `D`-link) and Lemma C (the CRT glue, its size count, and the list fold) | done |
| 4 | The eleven blocks glued and lifted, the exponent arithmetic, the liminf passage, and the numeric bound | done: Layers P, G, A and N complete — all three pinned targets discharged and audited |

Lean takes no citations, so Stages 3 and 4 have to reprove what the note is entitled to
quote. Stage 3 did that for both cited lemmas. Stage 4's numeric half bounds the constant
below with no floating-point arithmetic and no appeal to a decision procedure outside the
kernel; its analytic half carries a family of finite stages to the liminf. Both halves are
in, so the chain from the eleven certificates to the headline is closed end to end.

## Building

Install [elan](https://github.com/leanprover/elan); the toolchain (Lean 4.33.1) and the
Mathlib revision are pinned by `lean-toolchain` and `lake-manifest.json`.

```
lake exe cache get     # Mathlib .olean cache; once, and only on a fresh clone
lake build
```

A full build of this package on top of a warm Mathlib cache takes well under a minute.

The output is a contract, and with every stage landed it takes its strictest form: **zero
warnings, one axiom-audit info line, and nothing else.** That line reads

```
info: Test/AxiomAudit.lean:207:0: axiom audit passed: 126 declarations,
  axioms confined to [propext, Classical.choice, Quot.sound]
```

and *any* warning at all is a regression. This section used to carry a table naming the
declarations stated ahead of their proofs — thirteen when the Stage-4 skeleton landed, then
eleven, then three — alongside the CI exemption that let their placeholders through. The
table, the declarations and the exemption are all gone.

The toolchain and the Mathlib revision are deliberately frozen for the lifetime of the
staged formalization — a moving Mathlib would churn proofs that are meant to stay checkable
as written — so there is no automatic dependency-bump workflow; updates are manual and
reviewed.

## Trust base

Every finite check is discharged by `decide`, so the Lean **kernel** re-runs it; the
compiler is not trusted. `native_decide` is not used anywhere in this repository, and
neither is `axiom`, `unsafe`, or `partial`. The heaviest check, `cert299_valid`, is about
ten seconds of kernel and elaboration time.

```
#print axioms cert235_valid
  'cert235_valid' depends on axioms: [propext, Quot.sound]
#print axioms cert299_valid
  'cert299_valid' depends on axioms: [propext, Quot.sound]
#print axioms paley103
  'paley103' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms pool_mem_cert235
  'pool_mem_cert235' depends on axioms: [propext, Quot.sound]
#print axioms pool_coprime
  'pool_coprime' does not depend on any axioms
#print axioms lemmaA
  'lemmaA' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms lemmaB_card_le_D
  'lemmaB_card_le_D' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms lemmaC
  'lemmaC' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms sdf_liminf_ge
  'sdf_liminf_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The certificates and the pool bridges rest on nothing but `propext` and `Quot.sound`; the
structural facts about `pool` rest on nothing at all. The Paley theorems add
`Classical.choice`, which enters through Mathlib's primality API rather than through the
finite computation. So does `lemmaA`, and with it the whole Stage-2 layer — through
Mathlib's `padicValNat` and factorization API, which Step 2 and Step 3 run on. So does the
whole Stage-3 layer, through Mathlib's `Finset` and divisibility API. And so does
`sdf_liminf_ge`, the headline itself, which sits above every other line in this list:
Stage 4's real analysis — `liminf`, `Real.log`, `Filter.Tendsto` — is classical throughout.
The list is the same three axioms either way. A `native_decide` anywhere below a proof would show up
in its list as a generated `._native.native_decide.ax_*` axiom (older toolchains print
`Lean.ofReduceBool`); none appears. To reproduce: put those commands in a file importing
`FsLowerBound` and run `lake env lean` on it.

That check is automated rather than left to the reader. `Test/AxiomAudit.lean` — a default
build target, so `lake build` runs it — calls `Lean.collectAxioms` on all 126 finished
theorems and **fails the build** if any of them reaches outside
{`propext`, `Classical.choice`, `Quot.sound`} — an allowlist, so whatever axiom a future
`native_decide` or `axiom` declaration introduces is rejected without being named. Because
`collectAxioms` is transitive, those 126 names cover more than themselves: every declaration
this project exports is inside their closure, and the handful that nothing else
reaches — five toolkit lemmas, and Stage 4's nine provenance and nine height-exactness
records — are named individually, so that stays true. §6.2 and §6.3 are named in full as
well, redundantly: `sdf_liminf_ge` and `sdf_pointwise` already reach that chain, but it is
where the analysis lives and the record says so outright rather than by argument.

CI adds two source-level guards. The first: no `native_decide`, `axiom`, `unsafe`,
`partial`, or `admit` anywhere in `FsLowerBound/`. The second, in its strict form: no
placeholder proof in *any* `.lean` file of the repository outside `.lake/` — no exemption
for an in-flight stage, as it once carried, and no exemption for prose or for a scratch
file that slipped past `.gitignore` and got committed. A grep can only see this
repository's source; the axiom audit sees what the proofs actually depend on.

## What this repository proves

End to end, from eleven kernel-checked finite certificates to a statement about all
sufficiently large `N`: `sdf_liminf_ge`, that `α∞ ≤ liminf log D(N) / log N`;
`sdf_pointwise`, its ε-form, that `N^ρ ≤ D(N)` eventually for every `ρ < α∞`; and
`alphaInf_gt`, that `0.7537 < α∞`. Together they say that a subset of `{1,…,N}` avoiding
nonzero square differences can be taken of size at least `N^0.7537` for all large `N`.

Nothing along that chain is cited, postulated, or checked outside the kernel: Krachun's two
lemmas are reproved, the one new lemma is proved, the constant is bounded below by
comparisons of natural numbers rather than by floating-point arithmetic, and all three
theorems rest on `[propext, Classical.choice, Quot.sound]` and nothing else.

## Provenance

AI-generated formalization with human managing the workflow.

Released under the MIT License; see [LICENSE](LICENSE).
