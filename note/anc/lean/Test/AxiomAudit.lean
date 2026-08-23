import FsLowerBound
import Lean

set_option linter.style.header false

/-!
# Axiom audit

A grep can only see the source of this repository. It cannot see what a proof *depends*
on, and `native_decide` leaves its trace in the axiom list (on this toolchain, a generated
`<decl>._native.native_decide.ax_*` axiom; older toolchains used `Lean.ofReduceBool`)
rather than necessarily in the file that uses it. So this module runs `Lean.collectAxioms`
over every finished claim of the project at build time and fails the build if anything
reaches outside Lean's three standard axioms.

This is a build-time check, not a theorem: it is `#eval`'d while the module is elaborated,
so `lake build` fails — with the offending declaration and axiom named — the moment a
`native_decide`, an `axiom`, or a stray placeholder proof appears below the audited list.
(That last word is spelled around rather than written: CI's second guard rejects the
placeholder token in *any* `.lean` file of this repository, prose and scratch included, and
a check with an exception for the file that documents it would be no check at all.)

All four stages have landed, so there is no in-flight set and no exempt group: every public
declaration this repository exports is proved, and every one of them is inside the
transitive closure of the list below. Two rules govern what that list names.
`Lean.collectAxioms` is transitive, so a headline audits everything beneath it and the list
names headlines rather than every declaration; and a declaration nothing else reaches is
named one by one, so that "inside the closure" stays true of the whole file set rather than
of most of it. Where those two rules leave a name redundant — the three pinned targets,
their two internal statements, and the §6.2/§6.3 chain beneath them are the main case — it
is named anyway, because this list is the public record of what has been verified and a
reader should be able to find the headline claims in it by name rather than by argument.

The Stage-2 layer — `FsLowerBound.RankedBlocks` (the bridge) and `FsLowerBound.LemmaA`
(the lift) — is audited as of this list. Mostly the *headline* declarations of that layer
are named below, which is enough for what hangs beneath them: `Lean.collectAxioms` is
transitive, so auditing `lemmaA` audits the whole step spine, every digit basic it rests
on, and the `diffMod` toolkit that now sits in `FsLowerBound.Defs` — `diffMod_lt`,
`diffMod_ne_zero`, `diffMod_add` and the generalized `diffMod_unique` — and
auditing the two `cert*_lift_card` leaves audits `liftBlock_card`, the
counting helpers and the two `supportFinset` lemmas underneath. The exceptions are named
one by one: `padicValNat_add_of_lt`, `digit_add_mul_pow_succ` and
`digit_eq_zero_of_pow_dvd` are proved and public but reached by no other proof in the
project, so nothing else would pull them in. `digit_eq_zero_of_lt` is named alongside them
because it was in the same position when Stage 2 landed; Stage 3's
`exists_least_digit_ne_of_lt` now calls it, so it also sits inside the closure of
`lemmaB_sdf`, and naming it here is redundant rather than necessary.

The Stage-3 layer — `FsLowerBound.LemmaB`, from a ranked block to a square-difference-free
set of integers — is audited on the same principle. The four headline claims
(`lemmaB_sdf`, `integerSet_subset`, `integerSet_card`, `le_D_of_sdf`) and the composite
`lemmaB_card_le_D` are named; between them they reach the whole §1.3 step spine
(`word_step0_exact_dvd` through `word_step5_rank_drop`), the bridge
`diffMod_pow_mod_pow`, the `wordRank` bookkeeping and the `wordBlock` counting chain. The
one exception is `word_base_count`, which is proved as pinned but which the counting chain
does not call — `wordBlock_succ_card` runs off `mem_wordBlock_succ` instead — so it is
named individually, as the Stage-2 four are.

`FsLowerBound.LemmaC` — the CRT glue — closes Stage 3 and is audited on the same
principle. The binary headline `lemmaC` and its size count `crtBlock_card` reach §1.5's
coordinate machinery (`exists_sq_mod_of_dvd`, `coord_ne_zero`, `diffMod_mod_of_dvd`,
`coord_rank_le`, `coord_rank_lt`, `crtRank_lt`) and the counting pair `crt_injOn`,
`crt_image`; the list fold is named by its six finished claims — `trivialBlock_rankedBlock`,
`glueList_rankedBlock`, `glueList_fst`, `glueList_height`, `glueList_card`,
`glueList_mem_lt` — which between them reach `glueList_cons` and the tuple definitions
`trivialBlock`, `glueTwo`, `glueList`. This layer needs no individually named exception:
nothing in it is stranded outside the closure.

Stage 4 has landed, and is audited on the same principle.
Layer P — the nine Paley blocks of `FsLowerBound.PaleyBlocks` — is reached mostly through
the nine `baseBlocks_*` facts of `FsLowerBound.Construction`: `baseBlocks_rankedBlock`
pulls in the nine `paleyCert*_rankedBlock` and so the nine `decide`-checked
`paleyCert*_valid`, `baseBlocks_squarefree` the nine `squarefree_*`,
`baseBlocks_support_lt` the nine `paleyCert*_lt`, and `baseBlocks_pool` and
`baseBlocks_two_le_card` the nine `paleyCert*_card` together with the two composite card
facts. Two families in that file are deliberately reached by nothing — the nine
`paleyCert*_chain` provenance theorems, which say each certificate forgets its ranks to the
corresponding chain, and the nine `paleyCert*_height_exact` negative certificates, which
say the claimed height is attained and not merely bounded — so, like the Stage-2 and
Stage-3 strays, they are named one by one below. Layer G is headed by `stage_D_bound`,
which reaches `stage_rankedBlock`, `stageModulus_eq_sq`, the three `glue_*` closed forms
and the four `stageBlocks_*` hypotheses beneath them; those four are named as well, since
they are the interface Layer G presents to the glue. Layer A is named in full: `D_mono` and
`D_le`, the allocation arithmetic, the two logarithm exchanges, the height sandwich,
`tendsto_stageExponent` and `exists_stage_exponent_gt` (§6.2), `stage_pointwise` and the two
internal targets `sdf_pointwise_internal` and `sdf_liminf_internal` (§6.3). Naming that
chain is redundant — `sdf_liminf_ge` and `sdf_pointwise` reach all of it — and it is done
because §6.2/§6.3 is where the analysis lives and the record should say so outright. Layer N
is named by `alphaInf_gt_internal`, which reaches `alphaInf_eq_numerals` and all twenty-two rational
bounds, together with the two translation lemmas `lt_log_div_log` and `log_div_log_lt` that
turn each of those bounds into a kernel comparison of naturals; `alphaInf_gt` is the target
it discharges.

Every public *proved* declaration of the project is inside the transitive closure of this
list, and with all four stages complete that is every public declaration of the project.
The two `Decidable` instances of `FsLowerBound.Defs` are named nowhere below, but `decide`
pulls them in under `cert235_valid` and `cert299_valid` anyway.

The list — not the file set — is the record of what has actually been verified.
-/

open Lean

/-- The axioms this project is allowed to rest on. The list is an allowlist, so anything a
`native_decide` introduces — a generated `._native.native_decide.ax_*` axiom on this
toolchain — is rejected without needing to be named here. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Every finished claim of the project: the two composite certificates and their height
attainments, the ten Paley chains, the pool bridges, the Remark 1 negative control, the
two set/finset forms of square-difference-freeness, the Stage-2 lift — the
`RankedBlock` bridge, `lemmaA`, the size count `liftBlock_card`, the two lifted
certificate blocks, the two lifted size counts `(235 · 17) ^ e` and `(299 · 19) ^ e` — the
Stage-3 pair — Lemma B with its `D` bound, and Lemma C with its size count and the list
fold — the five toolkit lemmas named individually rather than reached, and Stage 4 entire:
the nine Paley provenance and height-exactness records, the eleven certified blocks, the
glued stage's `D` bound, the counting function's two order facts, the allocation
arithmetic, the §6.2/§6.3 chain in full — the logarithm exchanges, the height sandwich,
the exponent limit, the pointwise passage and the two internal targets — the two rational
translations, the numeric headline `0.7537 < alphaInf`, and the three pinned targets
themselves. -/
def auditedDeclarations : List Name :=
  [ -- Definitions layer
    ``sdfFinset_iff, ``six_not_unit_square_mod_15,
    -- The two composite certificates and their heights
    ``cert235_valid, ``cert299_valid,
    ``cert235_height_attained, ``cert299_height_attained,
    ``cert235_ranks_complete, ``cert299_ranks_complete,
    -- The ten Paley chains
    ``paley3, ``paley7, ``paley11, ``paley19, ``paley23,
    ``paley31, ``paley43, ``paley59, ``paley71, ``paley103,
    -- The pool bridges
    ``pool_length, ``pool_coprime,
    ``pool_mem_cert235, ``pool_mem_cert299,
    ``pool_mem_paley3, ``pool_mem_paley7, ``pool_mem_paley11, ``pool_mem_paley19,
    ``pool_mem_paley31, ``pool_mem_paley43, ``pool_mem_paley59, ``pool_mem_paley71,
    ``pool_mem_paley103,
    -- Stage 2: the bridge from the list form to `RankedBlock`
    ``RankedBlock.of_validRankedSupport, ``cert235_rankedBlock, ``cert299_rankedBlock,
    -- Stage 2: the lift, its size count, and the square-freeness it needs
    ``lemmaA, ``liftBlock_card, ``squarefree_235, ``squarefree_299,
    ``cert235_lift_rankedBlock, ``cert299_lift_rankedBlock,
    -- Stage 2: the two lifted size counts, `(235 · 17) ^ e` and `(299 · 19) ^ e`
    ``cert235_lift_card, ``cert299_lift_card,
    -- Stage 3: Lemma B — the four headline claims and the inequality Stage 4 consumes
    ``lemmaB_sdf, ``integerSet_subset, ``integerSet_card, ``le_D_of_sdf,
    ``lemmaB_card_le_D,
    -- Stage 3: Lemma C — the binary glue, its size count, and the list fold
    ``lemmaC, ``crtBlock_card,
    ``trivialBlock_rankedBlock, ``glueList_rankedBlock,
    ``glueList_fst, ``glueList_height, ``glueList_card, ``glueList_mem_lt,
    -- Named individually so the closure is exhaustive (`digit_eq_zero_of_lt` is also
    -- reached, through Stage 3's `exists_least_digit_ne_of_lt`; the rest are not)
    ``padicValNat_add_of_lt, ``digit_add_mul_pow_succ,
    ``digit_eq_zero_of_lt, ``digit_eq_zero_of_pow_dvd, ``word_base_count,
    -- Stage 4, Layer P: the provenance and height-exactness records, which nothing
    -- downstream consumes and which are therefore named individually
    ``paleyCert3_chain, ``paleyCert7_chain, ``paleyCert11_chain, ``paleyCert19_chain,
    ``paleyCert31_chain, ``paleyCert43_chain, ``paleyCert59_chain, ``paleyCert71_chain,
    ``paleyCert103_chain,
    ``paleyCert3_height_exact, ``paleyCert7_height_exact, ``paleyCert11_height_exact,
    ``paleyCert19_height_exact, ``paleyCert31_height_exact, ``paleyCert43_height_exact,
    ``paleyCert59_height_exact, ``paleyCert71_height_exact, ``paleyCert103_height_exact,
    -- Stage 4, Layers P and G: the eleven certified blocks, and the glued stage
    ``baseBlocks_moduli, ``baseBlocks_coprime, ``baseBlocks_two_le,
    ``baseBlocks_two_le_height, ``baseBlocks_two_le_card, ``baseBlocks_squarefree,
    ``baseBlocks_rankedBlock, ``baseBlocks_support_lt, ``baseBlocks_pool,
    ``glue_modulus, ``glue_height, ``glue_card, ``stageModulus_eq_sq,
    ``stageHeight_pos, ``stageModulus_pos, ``one_lt_stageModulus, ``one_lt_stageHeight,
    ``one_lt_stageCard, ``stage_rankedBlock, ``stage_D_bound,
    -- Stage 4, Layer G: the four hypotheses the glue consumes
    ``stageBlocks_rankedBlock, ``stageBlocks_coprime, ``stageBlocks_height_pos,
    ``stageBlocks_support_lt,
    -- Stage 4, Layer A: monotonicity of `D`, its trivial upper bound, and the allocation
    ``D_mono, ``D_le, ``logHeight_pos, ``logHeight_le_max, ``one_le_alloc,
    ``alloc_mul_logHeight_le, ``sub_logHeight_lt_alloc_mul,
    -- Stage 4, Layer A, §6.2: the two logarithm exchanges, the height sandwich, and the
    -- limit of the stage exponent along the allocation
    ``log_stageModulus, ``log_stageCard,
    ``pow_height_le_stageHeight, ``stageHeight_le_of_forall_le,
    ``log_stageHeight_lower, ``log_stageHeight_upper,
    ``tendsto_stageExponent, ``exists_stage_exponent_gt,
    -- Stage 4, Layer A, §6.3: the passage from the stages to every `N`, and the two
    -- internal statements the pinned targets delegate to
    ``stage_pointwise, ``sdf_pointwise_internal, ``sdf_liminf_internal,
    -- Stage 4, Layer N: the two rational translations and the numeric headline
    ``lt_log_div_log, ``log_div_log_lt, ``alphaInf_gt_internal,
    -- The three pinned targets
    ``sdf_liminf_ge, ``sdf_pointwise, ``alphaInf_gt]

/-- Run the audit. Throws — and so fails `lake build` — on any axiom outside
`allowedAxioms`. -/
def runAxiomAudit : MetaM Unit := do
  let mut offenders : Array String := #[]
  for d in auditedDeclarations do
    unless (← getEnv).contains d do
      throwError "axiom audit: audited declaration `{d}` does not exist"
    let axs ← Lean.collectAxioms d
    let bad := axs.filter fun a => !allowedAxioms.contains a
    unless bad.isEmpty do
      offenders := offenders.push s!"{d} depends on {bad.toList}"
  unless offenders.isEmpty do
    throwError "axiom audit FAILED: {String.intercalate "; " offenders.toList}"
  logInfo s!"axiom audit passed: {auditedDeclarations.length} declarations, \
    axioms confined to {allowedAxioms}"

#eval runAxiomAudit
