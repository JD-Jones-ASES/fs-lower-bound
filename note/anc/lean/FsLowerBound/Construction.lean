import FsLowerBound.PaleyBlocks
import FsLowerBound.Pool
import FsLowerBound.LemmaA
import FsLowerBound.LemmaB
import FsLowerBound.LemmaC

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false

/-!
# The glued stage construction

This is Layer G of Stage 4: the eleven certified blocks, lifted with multiplicities and
glued by the Chinese remainder theorem into a single ranked block on a perfect-square
modulus, which Lemma B then turns into a lower bound on `D`.

`krachun-proofs.md` §6.1 writes the outcome as (2.5′):

`P = Π mᵢ ^ (2 eᵢ)`, `|C| = Π (mᵢ tᵢ) ^ eᵢ`, `H = 1 + Σ (Hᵢ ^ eᵢ − 1)`,

and those three are `stageModulus`, `stageCard` and `stageHeight` below. The one inequality
this file exports is `stage_D_bound`:

`stageCard E ^ L ≤ D ((stageModulus E * stageHeight E) ^ L)` for every `L ≥ 1`,

which is (2.5′) fed to Lemma B. Everything above it is bookkeeping that connects the
eleven concrete blocks to the three closed forms.

## The multiplicity vector

`krachun-proofs.md` §6.2 allocates a multiplicity `eᵢ` to each block, and the allocation it
uses — `eᵢ(U) = ⌊U / log Hᵢ⌋` — depends on the block only through its height. The
multiplicity therefore travels here as a *function of the block*, `E : Block → ℕ`, rather
than as a vector of eleven numbers: the eleven blocks are distinct, so a function on blocks
restricts to an arbitrary vector, and `FsLowerBound.Asymptotics` instantiates it at the
allocation without any indexing apparatus. Every closed form below is a `List.map` over
`baseBlocks`, which is what makes the logarithms of §6.2 a `List.sum` exchange rather than
an induction.

## Correspondence to `pool`

`alphaInf` is defined over `pool`'s bare numerals, so the construction has to be tied back
to them. `baseBlocks_pool` is that tie: the map that reads `(modulus, support size, height)`
off `baseBlocks` returns `pool` on the nose. Its proof consumes the nine Paley card facts of
`FsLowerBound.PaleyBlocks` and the two composite ones of `FsLowerBound.RankedBlocks`; the
numerals are never retyped.

## Trust rules (ADR-033)

The ADR-033 trust rules apply: no kernel-external decision procedures, no postulated
constants, no compiler escape hatches. Every declaration below is proved — Layer G carries
no placeholder — and the nine `baseBlocks_*` facts, the three `glue_*` closed forms,
`stageModulus_eq_sq`, `stage_rankedBlock` and `stage_D_bound` are named in
`auditedDeclarations` in `Test/AxiomAudit.lean`. That audit is transitive, so the nine
`baseBlocks_*` facts between them cover the whole of `FsLowerBound.PaleyBlocks`.
-/

set_option maxRecDepth 10000

/-! ## Blocks -/

/-- A block travelling through Lemma C's fold: `(modulus, support, ranking, height)`. This
is the tuple `FsLowerBound.LemmaC` folds; naming it keeps the eleven-block list readable. -/
abbrev Block : Type := ℕ × Finset ℕ × (ℕ → ℕ) × ℕ

/-- The eleven certified blocks: the nine Paley blocks of `FsLowerBound.PaleyBlocks`, then
the two composite certificates. Each entry is `(m, S, h, H)` with the support and ranking
taken from the certified object itself, never retyped. -/
def baseBlocks : List Block :=
  [(3, supportFinset paleyCert3, rankOf paleyCert3, 2),
   (7, supportFinset paleyCert7, rankOf paleyCert7, 3),
   (11, supportFinset paleyCert11, rankOf paleyCert11, 4),
   (19, supportFinset paleyCert19, rankOf paleyCert19, 5),
   (31, supportFinset paleyCert31, rankOf paleyCert31, 7),
   (43, supportFinset paleyCert43, rankOf paleyCert43, 7),
   (59, supportFinset paleyCert59, rankOf paleyCert59, 9),
   (71, supportFinset paleyCert71, rankOf paleyCert71, 9),
   (103, supportFinset paleyCert103, rankOf paleyCert103, 11),
   (235, supportFinset cert235, rankOf cert235, 11),
   (299, supportFinset cert299, rankOf cert299, 12)]

/-- One block lifted to multiplicity `e`, in the shape `lemmaA` produces: modulus
`m ^ (2 e)`, support `liftBlock`, ranking `liftRank`, height `H ^ e`. -/
def liftOf (b : Block) (e : ℕ) : Block :=
  (b.1 ^ (2 * e), liftBlock b.1 e b.2.1, liftRank b.1 e b.2.2.2 b.2.2.1, b.2.2.2 ^ e)

/-- The eleven lifted blocks at multiplicity vector `E`. -/
def stageBlocks (E : Block → ℕ) : List Block := baseBlocks.map (fun b => liftOf b (E b))

/-! ## The three closed forms of (2.5′) -/

/-- `Π mᵢ ^ eᵢ` — the square root of the stage modulus, which is what Lemma B's
perfect-square hypothesis needs exhibited. -/
def stageRoot (E : Block → ℕ) : ℕ := (baseBlocks.map fun b => b.1 ^ E b).prod

/-- `P = Π mᵢ ^ (2 eᵢ)` of (2.5′). -/
def stageModulus (E : Block → ℕ) : ℕ := (baseBlocks.map fun b => b.1 ^ (2 * E b)).prod

/-- `|C| = Π (mᵢ tᵢ) ^ eᵢ` of (2.5′). -/
def stageCard (E : Block → ℕ) : ℕ := (baseBlocks.map fun b => (b.1 * b.2.1.card) ^ E b).prod

/-- `H = 1 + Σ (Hᵢ ^ eᵢ − 1)` of (2.5′). -/
def stageHeight (E : Block → ℕ) : ℕ := 1 + (baseBlocks.map fun b => b.2.2.2 ^ E b - 1).sum

/-! ## What the eleven blocks are

Eleven facts, each read off the list one entry at a time. They are the hypotheses `lemmaA`,
`lemmaC` and `lemmaB_card_le_D` take, collected once so that no proof below re-enumerates
the pool. -/

/-- The eleven moduli, as a list of numerals. -/
theorem baseBlocks_moduli :
    baseBlocks.map Prod.fst = [3, 7, 11, 19, 31, 43, 59, 71, 103, 235, 299] := rfl

/-- The eleven moduli are pairwise coprime — Lemma C's hypothesis. -/
theorem baseBlocks_coprime : (baseBlocks.map Prod.fst).Pairwise Nat.Coprime := by
  rw [baseBlocks_moduli]; decide

/-- Every modulus is at least `2` — Lemma A's hypothesis. -/
theorem baseBlocks_two_le : ∀ b ∈ baseBlocks, 2 ≤ b.1 := by
  intro b hb
  simp only [baseBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Every height is at least `2` — the hypothesis `Hᵢ ≥ 2` of §6.2, which is what makes
`log Hᵢ > 0` and the allocation meaningful. -/
theorem baseBlocks_two_le_height : ∀ b ∈ baseBlocks, 2 ≤ b.2.2.2 := by
  intro b hb
  simp only [baseBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Every modulus is square-free — Lemma A's hypothesis. -/
theorem baseBlocks_squarefree : ∀ b ∈ baseBlocks, Squarefree b.1 := by
  intro b hb
  simp only [baseBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [squarefree_3, squarefree_7, squarefree_11, squarefree_19, squarefree_31,
    squarefree_43, squarefree_59, squarefree_71, squarefree_103,
    squarefree_235, squarefree_299]

/-- Every entry is a ranked block. -/
theorem baseBlocks_rankedBlock : ∀ b ∈ baseBlocks, RankedBlock b.1 b.2.1 b.2.2.1 b.2.2.2 := by
  intro b hb
  simp only [baseBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [paleyCert3_rankedBlock, paleyCert7_rankedBlock, paleyCert11_rankedBlock,
    paleyCert19_rankedBlock, paleyCert31_rankedBlock, paleyCert43_rankedBlock,
    paleyCert59_rankedBlock, paleyCert71_rankedBlock, paleyCert103_rankedBlock,
    cert235_rankedBlock, cert299_rankedBlock]

/-- Every support consists of residues — `liftBlock_card`'s hypothesis. -/
theorem baseBlocks_support_lt : ∀ b ∈ baseBlocks, ∀ s ∈ b.2.1, s < b.1 := by
  intro b hb
  simp only [baseBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [paleyCert3_lt, paleyCert7_lt, paleyCert11_lt, paleyCert19_lt, paleyCert31_lt,
    paleyCert43_lt, paleyCert59_lt, paleyCert71_lt, paleyCert103_lt,
    cert235_supportFinset_lt, cert299_supportFinset_lt]

/-- **The tie to `pool`.** Reading `(modulus, support size, height)` off the eleven
certified blocks returns exactly the eleven numeric triples `alphaInf` is evaluated on. This
is the seam between the construction and the constant: without it, the eleven blocks and the
eleven numerals could drift apart and every other theorem would stay true. -/
theorem baseBlocks_pool : baseBlocks.map (fun b => (b.1, b.2.1.card, b.2.2.2)) = pool := by
  simp only [baseBlocks, pool, List.map_cons, List.map_nil, paleyCert3_card, paleyCert7_card,
    paleyCert11_card, paleyCert19_card, paleyCert31_card, paleyCert43_card, paleyCert59_card,
    paleyCert71_card, paleyCert103_card, cert235_supportFinset_card, cert299_supportFinset_card]

/-! ## The lifted blocks

`lemmaA` applied entrywise, and the closed forms that result. -/

/-- Each lifted block is a ranked block — `lemmaA`, entry by entry. -/
theorem stageBlocks_rankedBlock (E : Block → ℕ) (hE : ∀ b ∈ baseBlocks, 1 ≤ E b) :
    ∀ c ∈ stageBlocks E, RankedBlock c.1 c.2.1 c.2.2.1 c.2.2.2 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact lemmaA b.1 (baseBlocks_two_le b hb) (baseBlocks_squarefree b hb) b.2.1 b.2.2.1 b.2.2.2
    (baseBlocks_rankedBlock b hb) (E b) (hE b hb)

/-- The lifted moduli are pairwise coprime: powers of pairwise coprime numbers, through
`Nat.Coprime.pow`. -/
theorem stageBlocks_coprime (E : Block → ℕ) :
    ((stageBlocks E).map Prod.fst).Pairwise Nat.Coprime := by
  rw [stageBlocks, List.map_map]
  refine List.pairwise_map.mpr ?_
  exact (List.pairwise_map.mp baseBlocks_coprime).imp fun h => Nat.Coprime.pow _ _ h

/-- Every lifted height is positive — Lemma C's fold hypothesis. -/
theorem stageBlocks_height_pos (E : Block → ℕ) : ∀ c ∈ stageBlocks E, 1 ≤ c.2.2.2 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact Nat.one_le_pow _ _ (by have := baseBlocks_two_le_height b hb; omega)

/-- Every lifted support consists of residues — the counting hypothesis of Lemma C's fold. -/
theorem stageBlocks_support_lt (E : Block → ℕ) :
    ∀ c ∈ stageBlocks E, ∀ s ∈ c.2.1, s < c.1 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  intro s hs
  exact ((mem_liftBlock b.1 (E b) b.2.1 s).mp hs).1

/-- The glued modulus is `stageModulus` — `glueList_fst` at the eleven lifted blocks. -/
theorem glue_modulus (E : Block → ℕ) : (glueList (stageBlocks E)).1 = stageModulus E := by
  rw [glueList_fst, stageBlocks, stageModulus, List.map_map]
  rfl

/-- The glued height is `stageHeight` — `glueList_height` at the eleven lifted blocks. -/
theorem glue_height (E : Block → ℕ) : (glueList (stageBlocks E)).2.2.2 = stageHeight E := by
  rw [glueList_height _ (stageBlocks_height_pos E), stageBlocks, stageHeight, List.map_map]
  rfl

/-- The glued support size is `stageCard` — `glueList_card` and `liftBlock_card`. -/
theorem glue_card (E : Block → ℕ) : (glueList (stageBlocks E)).2.1.card = stageCard E := by
  rw [glueList_card _ (stageBlocks_coprime E) (stageBlocks_support_lt E), stageBlocks,
    stageCard, List.map_map]
  exact congrArg List.prod
    (List.map_congr_left fun b hb => liftBlock_card b.1 (E b) b.2.1 (baseBlocks_support_lt b hb))

/-- Squares come out of a product one factor at a time. The shape of `stageModulus`'s
perfect-square claim, stated over an arbitrary list so that it is an induction and not an
eleven-fold computation. -/
private theorem prod_map_sq (l : List Block) (f : Block → ℕ) :
    (l.map fun b => f b ^ 2).prod = (l.map f).prod ^ 2 := by
  induction l with
  | nil => simp
  | cons b t ih => simp [List.map_cons, List.prod_cons, ih, mul_pow]

/-- The stage modulus is a perfect square, `(Π mᵢ ^ eᵢ) ²` — Lemma B's hypothesis, and the
reason the exponents in (2.5′) carry the factor `2`. -/
theorem stageModulus_eq_sq (E : Block → ℕ) : stageModulus E = stageRoot E ^ 2 := by
  rw [stageModulus, stageRoot, ← prod_map_sq]
  exact congrArg List.prod
    (List.map_congr_left fun b _ => by rw [Nat.mul_comm, pow_mul])

/-- The glued object is a ranked block on `stageModulus E` of height `stageHeight E` —
`glueList_rankedBlock`, with the three closed forms substituted. -/
theorem stage_rankedBlock (E : Block → ℕ) (hE : ∀ b ∈ baseBlocks, 1 ≤ E b) :
    RankedBlock (stageModulus E) (glueList (stageBlocks E)).2.1
      (glueList (stageBlocks E)).2.2.1 (stageHeight E) := by
  rw [← glue_modulus E, ← glue_height E]
  exact glueList_rankedBlock (stageBlocks E) (stageBlocks_coprime E)
    (stageBlocks_rankedBlock E hE) (stageBlocks_height_pos E)

/-! ## Size facts

The positivity the analysis layer needs before it may take logarithms. -/

/-- The stage height is positive: it is `1 + …` in ℕ. -/
theorem stageHeight_pos (E : Block → ℕ) : 1 ≤ stageHeight E := Nat.le_add_right 1 _

/-- The stage modulus is positive. -/
theorem stageModulus_pos (E : Block → ℕ) : 0 < stageModulus E := by
  refine List.prod_pos ?_
  intro n hn
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hn
  exact pow_pos (by have := baseBlocks_two_le b hb; omega) _

/-- Every support has at least two vertices — the smallest is the `3` block's `t = 2`. -/
theorem baseBlocks_two_le_card : ∀ b ∈ baseBlocks, 2 ≤ b.2.1.card := by
  intro b hb
  simp only [baseBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact le_of_eq paleyCert3_card.symm
  · exact le_of_lt (by rw [paleyCert7_card]; norm_num)
  · exact le_of_lt (by rw [paleyCert11_card]; norm_num)
  · exact le_of_lt (by rw [paleyCert19_card]; norm_num)
  · exact le_of_lt (by rw [paleyCert31_card]; norm_num)
  · exact le_of_lt (by rw [paleyCert43_card]; norm_num)
  · exact le_of_lt (by rw [paleyCert59_card]; norm_num)
  · exact le_of_lt (by rw [paleyCert71_card]; norm_num)
  · exact le_of_lt (by rw [paleyCert103_card]; norm_num)
  · exact le_of_lt (by rw [cert235_supportFinset_card]; norm_num)
  · exact le_of_lt (by rw [cert299_supportFinset_card]; norm_num)

/-- The first block of the pool, named so that the three size facts below have a member of
`baseBlocks` to point at. Nothing distinguishes it but being first. -/
private def block3 : Block := (3, supportFinset paleyCert3, rankOf paleyCert3, 2)

private theorem block3_mem : block3 ∈ baseBlocks := List.mem_cons_self

/-- With every multiplicity positive the stage modulus exceeds `1`, so
`log (stageModulus E) > 0` and the exponent ratio of §6.2 is well formed. -/
theorem one_lt_stageModulus (E : Block → ℕ) (hE : ∀ b ∈ baseBlocks, 1 ≤ E b) :
    1 < stageModulus E := by
  have h1 : ∀ n ∈ baseBlocks.map fun b => b.1 ^ (2 * E b), 1 ≤ n := by
    intro n hn
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hn
    exact Nat.one_le_pow _ _ (by have := baseBlocks_two_le b hbm; omega)
  have hmem : (3 : ℕ) ^ (2 * E block3) ∈ baseBlocks.map fun b => b.1 ^ (2 * E b) :=
    List.mem_map_of_mem block3_mem
  refine lt_of_lt_of_le ?_ (List.single_le_prod h1 _ hmem)
  exact Nat.one_lt_pow (by have := hE block3 block3_mem; omega) (by norm_num)

/-- With every multiplicity positive the stage height exceeds `1`. -/
theorem one_lt_stageHeight (E : Block → ℕ) (hE : ∀ b ∈ baseBlocks, 1 ≤ E b) :
    1 < stageHeight E := by
  have h0 : ∀ n ∈ baseBlocks.map fun b => b.2.2.2 ^ E b - 1, 0 ≤ n := fun _ _ => Nat.zero_le _
  have hmem : (2 : ℕ) ^ E block3 - 1 ∈ baseBlocks.map fun b => b.2.2.2 ^ E b - 1 :=
    List.mem_map_of_mem block3_mem
  have hle := List.single_le_sum h0 _ hmem
  have h2 : (2 : ℕ) ≤ 2 ^ E block3 := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ E block3 := Nat.pow_le_pow_right (by norm_num) (hE block3 block3_mem)
  rw [stageHeight]
  omega

/-- The stage support is nonempty, so `stageCard E > 1`: it is a product of factors
`mᵢ tᵢ ≥ 6`. -/
theorem one_lt_stageCard (E : Block → ℕ) (hE : ∀ b ∈ baseBlocks, 1 ≤ E b) :
    1 < stageCard E := by
  have h1 : ∀ n ∈ baseBlocks.map fun b => (b.1 * b.2.1.card) ^ E b, 1 ≤ n := by
    intro n hn
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hn
    refine Nat.one_le_pow _ _ ?_
    have h2 := baseBlocks_two_le b hbm
    have h3 := baseBlocks_two_le_card b hbm
    exact Nat.mul_pos (by omega) (by omega)
  have hmem : ((3 : ℕ) * (supportFinset paleyCert3).card) ^ E block3 ∈
      baseBlocks.map fun b => (b.1 * b.2.1.card) ^ E b := List.mem_map_of_mem block3_mem
  refine lt_of_lt_of_le ?_ (List.single_le_prod h1 _ hmem)
  refine Nat.one_lt_pow (by have := hE block3 block3_mem; omega) ?_
  rw [paleyCert3_card]
  norm_num

/-! ## The bound on `D`

Lemma B, applied to the glued block. This is the one inequality Layer A consumes. -/

/-- **(2.5′) fed to Lemma B.** For every multiplicity vector with all `eᵢ ≥ 1` and every
word length `L ≥ 1`, the glued stage certifies

`(Π (mᵢ tᵢ) ^ eᵢ) ^ L ≤ D ((P · H) ^ L)`, `P = Π mᵢ ^ (2 eᵢ)`, `H = 1 + Σ (Hᵢ ^ eᵢ − 1)`.

Intended discharge: `lemmaB_card_le_D` at `n := stageRoot E`, `P := stageModulus E`,
`C := (glueList (stageBlocks E)).2.1`, `H := stageHeight E`, with `stageModulus_eq_sq`
supplying the perfect square, `stage_rankedBlock` the block, `stageHeight_pos` the height,
and `glue_card` rewriting the conclusion's `C.card ^ L` into `stageCard E ^ L`. -/
theorem stage_D_bound (E : Block → ℕ) (hE : ∀ b ∈ baseBlocks, 1 ≤ E b) (L : ℕ) (hL : 1 ≤ L) :
    stageCard E ^ L ≤ D ((stageModulus E * stageHeight E) ^ L) := by
  have h := lemmaB_card_le_D (stageRoot E) (stageModulus E) (stageModulus_eq_sq E)
    (glueList (stageBlocks E)).2.1 (glueList (stageBlocks E)).2.2.1 (stageHeight E)
    (stage_rankedBlock E hE) (stageHeight_pos E) L hL
  rwa [glue_card E] at h
