import FsLowerBound.RankedBlocks
import FsLowerBound.PaleyChains
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false

/-!
# The nine Paley blocks as certified ranked blocks

`FsLowerBound.PaleyChains` certifies nine lists of residues as *Paley chains*: for each
prime `p ≡ 3 (mod 4)` in `{3, 7, 11, 19, 31, 43, 59, 71, 103}`, the entries are distinct
residues and every forward difference is a nonzero square mod `p`. What the construction
of Stage 4 consumes is not a chain but a `RankedBlock` — the interface Lemma A lifts,
Lemma C glues and Lemma B counts. This file supplies the nine.

For each prime the certificate is the chain with an *exhibited ranking* attached: the
`i`-th entry of a chain of length `t` gets rank `t − 1 − i`, so the ranks run
`t − 1, t − 2, …, 1, 0` down the chain and height `t` is attained. The ranking is correct
because an arc runs from an earlier entry to a later one and never back: `p ≡ 3 (mod 4)`
makes `−1` a non-residue, so `d ∈ Q_p` forces `p − d ∉ Q_p`.

That the certificate *is* the chain is a theorem here rather than a claim about how the
lists were typed: `paleyCert3_chain … paleyCert103_chain` state
`paleyCertP.map Prod.fst = chainP` and hold by `rfl`. Nothing below depends on them — the
ranked-support check is re-decided from scratch, so a mistyped list would still be a
certified block, just not the block advertised — and that is exactly why they are here:
they are what makes the advertisement checkable.

## Why the chain certificates are not reused

`ValidRankedSupport p paleyCertP t` is *re-checked* here by `decide` rather than derived
from `paleyP`. Deriving it would need a general "chain ⟹ ranked DAG" lemma: from the
`List.Pairwise` forward-difference condition and the quadratic character of `−1` at a prime
`p ≡ 3 (mod 4)`, conclude that no backward difference is an arc. That is a genuine piece of
number theory — Euler's criterion at `p ≡ 3 (mod 4)` — and it is not needed: the ranked
check is one pass over `t²` ordered pairs at a modulus of at most `103`, which the kernel
does in milliseconds. The chain theorems `paley3 … paley103` remain the record that these
lists are Krachun's chains; the blocks below are the record that they rank.

Every declaration in this file is proved. The two `decide`-checked facts per prime —
`ValidRankedSupport p paleyCertP t`, and its *failure* at `t − 1`, which is what makes the
height exactly `t` rather than merely at most `t` — are kernel checks, as everywhere else in
this repository.

## Choices made here beyond the design brief

* **Ranks descend rather than ascend.** The brief pins `rank i ↦ t − 1 − i`; that is what
  is written. Stated positively: the chain's *first* entry is its highest rank, matching
  the two composite certificates, where rank `0` is a sink.
* **`paleyCertP_card` and `paleyCertP_lt` accompany each block**, exactly as
  `cert235_supportFinset_card` and `cert235_supportFinset_lt` accompany the composite ones.
  They are what `liftBlock_card` and Lemma C's counting need, and they are stated at the
  numerals `2, 3, 4, 5, 7, 7, 9, 9, 11` that `pool` carries.
* **`squarefree_3 … squarefree_103` are stated here.** A prime is square-free, so these are
  one-liners; they are the hypothesis `lemmaA` takes, and collecting them beside the blocks
  keeps `FsLowerBound.Construction` free of per-prime bookkeeping.

## Trust rules (ADR-033)

The ADR-033 trust rules apply: no kernel-external decision procedures, no postulated
constants, no compiler escape hatches. This file carries no placeholders.
-/

set_option maxRecDepth 100000

/-! ## The nine certificates

Each list is the chain of `FsLowerBound.PaleyChains` with the ranking `t − 1, …, 0`
attached entry by entry. -/

/-- The Paley block at `p = 3`: the chain `[0, 1]`, ranked `1, 0`. -/
def paleyCert3 : List (ℕ × ℕ) := [(0, 1), (1, 0)]

/-- The Paley block at `p = 7`: the chain `[0, 4, 1]`, ranked `2, 1, 0`. -/
def paleyCert7 : List (ℕ × ℕ) := [(0, 2), (4, 1), (1, 0)]

/-- The Paley block at `p = 11`: the chain `[0, 3, 1, 4]`, ranked `3, …, 0`. -/
def paleyCert11 : List (ℕ × ℕ) := [(0, 3), (3, 2), (1, 1), (4, 0)]

/-- The Paley block at `p = 19`: the chain `[0, 5, 11, 9, 16]`, ranked `4, …, 0`. -/
def paleyCert19 : List (ℕ × ℕ) := [(0, 4), (5, 3), (11, 2), (9, 1), (16, 0)]

/-- The Paley block at `p = 31`: the chain `[0, 25, 14, 1, 19, 8, 2]`, ranked `6, …, 0`. -/
def paleyCert31 : List (ℕ × ℕ) :=
  [(0, 6), (25, 5), (14, 4), (1, 3), (19, 2), (8, 1), (2, 0)]

/-- The Paley block at `p = 43`: the chain `[0, 31, 9, 23, 4, 40, 1]`, ranked `6, …, 0`. -/
def paleyCert43 : List (ℕ × ℕ) :=
  [(0, 6), (31, 5), (9, 4), (23, 3), (4, 2), (40, 1), (1, 0)]

/-- The Paley block at `p = 59`: the chain `[0, 49, 15, 7, 16, 19, 35, 36, 5]`, ranked
`8, …, 0`. -/
def paleyCert59 : List (ℕ × ℕ) :=
  [(0, 8), (49, 7), (15, 6), (7, 5), (16, 4), (19, 3), (35, 2), (36, 1), (5, 0)]

/-- The Paley block at `p = 71`: the chain `[0, 8, 12, 18, 48, 27, 1, 37, 20]`, ranked
`8, …, 0`. -/
def paleyCert71 : List (ℕ × ℕ) :=
  [(0, 8), (8, 7), (12, 6), (18, 5), (48, 4), (27, 3), (1, 2), (37, 1), (20, 0)]

/-- The Paley block at `p = 103`: the chain `[0, 79, 25, 58, 55, 81, 4, 1, 34, 83, 59]`,
ranked `10, …, 0`. -/
def paleyCert103 : List (ℕ × ℕ) :=
  [(0, 10), (79, 9), (25, 8), (58, 7), (55, 6), (81, 5), (4, 4), (1, 3), (34, 2), (83, 1),
   (59, 0)]

/-! ## Provenance: each certificate is its chain

Forgetting the ranks returns the chain of `FsLowerBound.PaleyChains` on the nose. Each is
`rfl`. These theorems carry no weight in the construction; they carry the claim that the
nine lists above are Krachun's chains and not nine plausible lists of residues. -/

/-- `paleyCert3` is `chain3`, ranked. -/
theorem paleyCert3_chain : paleyCert3.map Prod.fst = chain3 := rfl

/-- `paleyCert7` is `chain7`, ranked. -/
theorem paleyCert7_chain : paleyCert7.map Prod.fst = chain7 := rfl

/-- `paleyCert11` is `chain11`, ranked. -/
theorem paleyCert11_chain : paleyCert11.map Prod.fst = chain11 := rfl

/-- `paleyCert19` is `chain19`, ranked. -/
theorem paleyCert19_chain : paleyCert19.map Prod.fst = chain19 := rfl

/-- `paleyCert31` is `chain31`, ranked. -/
theorem paleyCert31_chain : paleyCert31.map Prod.fst = chain31 := rfl

/-- `paleyCert43` is `chain43`, ranked. -/
theorem paleyCert43_chain : paleyCert43.map Prod.fst = chain43 := rfl

/-- `paleyCert59` is `chain59`, ranked. -/
theorem paleyCert59_chain : paleyCert59.map Prod.fst = chain59 := rfl

/-- `paleyCert71` is `chain71`, ranked. -/
theorem paleyCert71_chain : paleyCert71.map Prod.fst = chain71 := rfl

/-- `paleyCert103` is `chain103`, ranked. -/
theorem paleyCert103_chain : paleyCert103.map Prod.fst = chain103 := rfl

/-! ## The ranked-support checks

One `decide` per prime: distinct vertices below `p`, ranks below `t`, and a strict rank
drop along every arc. -/

theorem paleyCert3_valid : ValidRankedSupport 3 paleyCert3 2 := by decide

theorem paleyCert7_valid : ValidRankedSupport 7 paleyCert7 3 := by decide

theorem paleyCert11_valid : ValidRankedSupport 11 paleyCert11 4 := by decide

theorem paleyCert19_valid : ValidRankedSupport 19 paleyCert19 5 := by decide

theorem paleyCert31_valid : ValidRankedSupport 31 paleyCert31 7 := by decide

theorem paleyCert43_valid : ValidRankedSupport 43 paleyCert43 7 := by decide

theorem paleyCert59_valid : ValidRankedSupport 59 paleyCert59 9 := by decide

theorem paleyCert71_valid : ValidRankedSupport 71 paleyCert71 9 := by decide

theorem paleyCert103_valid : ValidRankedSupport 103 paleyCert103 11 := by decide

/-! ## The heights are exact

`ValidRankedSupport p paleyCertP t` bounds every rank strictly below `t`; only the second
conjunct of the definition mentions `t`, so its failure at `t − 1` says exactly that the
rank `t − 1` occurs. The pair is therefore "height exactly `t`", the same thing
`cert235_height_attained` and `cert299_height_attained` say for the composite certificates,
in the form the nine descending rankings make cheapest to check. Nothing downstream needs
these — the construction only ever uses the lower bound — so they are a record, not a
dependency. -/

theorem paleyCert3_height_exact : ¬ ValidRankedSupport 3 paleyCert3 1 := by decide

theorem paleyCert7_height_exact : ¬ ValidRankedSupport 7 paleyCert7 2 := by decide

theorem paleyCert11_height_exact : ¬ ValidRankedSupport 11 paleyCert11 3 := by decide

theorem paleyCert19_height_exact : ¬ ValidRankedSupport 19 paleyCert19 4 := by decide

theorem paleyCert31_height_exact : ¬ ValidRankedSupport 31 paleyCert31 6 := by decide

theorem paleyCert43_height_exact : ¬ ValidRankedSupport 43 paleyCert43 6 := by decide

theorem paleyCert59_height_exact : ¬ ValidRankedSupport 59 paleyCert59 8 := by decide

theorem paleyCert71_height_exact : ¬ ValidRankedSupport 71 paleyCert71 8 := by decide

theorem paleyCert103_height_exact : ¬ ValidRankedSupport 103 paleyCert103 10 := by decide

/-! ## The nine ranked blocks

The Stage-2 bridge `RankedBlock.of_validRankedSupport`, applied nine times. -/

/-- The `3` block as a ranked block on `Z/3Z`, height `2`. -/
theorem paleyCert3_rankedBlock :
    RankedBlock 3 (supportFinset paleyCert3) (rankOf paleyCert3) 2 :=
  RankedBlock.of_validRankedSupport 3 2 paleyCert3 paleyCert3_valid

/-- The `7` block as a ranked block on `Z/7Z`, height `3`. -/
theorem paleyCert7_rankedBlock :
    RankedBlock 7 (supportFinset paleyCert7) (rankOf paleyCert7) 3 :=
  RankedBlock.of_validRankedSupport 7 3 paleyCert7 paleyCert7_valid

/-- The `11` block as a ranked block on `Z/11Z`, height `4`. -/
theorem paleyCert11_rankedBlock :
    RankedBlock 11 (supportFinset paleyCert11) (rankOf paleyCert11) 4 :=
  RankedBlock.of_validRankedSupport 11 4 paleyCert11 paleyCert11_valid

/-- The `19` block as a ranked block on `Z/19Z`, height `5`. -/
theorem paleyCert19_rankedBlock :
    RankedBlock 19 (supportFinset paleyCert19) (rankOf paleyCert19) 5 :=
  RankedBlock.of_validRankedSupport 19 5 paleyCert19 paleyCert19_valid

/-- The `31` block as a ranked block on `Z/31Z`, height `7`. -/
theorem paleyCert31_rankedBlock :
    RankedBlock 31 (supportFinset paleyCert31) (rankOf paleyCert31) 7 :=
  RankedBlock.of_validRankedSupport 31 7 paleyCert31 paleyCert31_valid

/-- The `43` block as a ranked block on `Z/43Z`, height `7`. -/
theorem paleyCert43_rankedBlock :
    RankedBlock 43 (supportFinset paleyCert43) (rankOf paleyCert43) 7 :=
  RankedBlock.of_validRankedSupport 43 7 paleyCert43 paleyCert43_valid

/-- The `59` block as a ranked block on `Z/59Z`, height `9`. -/
theorem paleyCert59_rankedBlock :
    RankedBlock 59 (supportFinset paleyCert59) (rankOf paleyCert59) 9 :=
  RankedBlock.of_validRankedSupport 59 9 paleyCert59 paleyCert59_valid

/-- The `71` block as a ranked block on `Z/71Z`, height `9`. -/
theorem paleyCert71_rankedBlock :
    RankedBlock 71 (supportFinset paleyCert71) (rankOf paleyCert71) 9 :=
  RankedBlock.of_validRankedSupport 71 9 paleyCert71 paleyCert71_valid

/-- The `103` block as a ranked block on `Z/103Z`, height `11`. -/
theorem paleyCert103_rankedBlock :
    RankedBlock 103 (supportFinset paleyCert103) (rankOf paleyCert103) 11 :=
  RankedBlock.of_validRankedSupport 103 11 paleyCert103 paleyCert103_valid

/-! ## Support sizes and residue bounds

`t` for each block, and the fact that its support lies in `[0, p)`. Together these are the
hypotheses `liftBlock_card` and the counting side of Lemma C take. -/

theorem paleyCert3_card : (supportFinset paleyCert3).card = 2 := by
  rw [supportFinset_card paleyCert3 paleyCert3_valid.1]; rfl

theorem paleyCert7_card : (supportFinset paleyCert7).card = 3 := by
  rw [supportFinset_card paleyCert7 paleyCert7_valid.1]; rfl

theorem paleyCert11_card : (supportFinset paleyCert11).card = 4 := by
  rw [supportFinset_card paleyCert11 paleyCert11_valid.1]; rfl

theorem paleyCert19_card : (supportFinset paleyCert19).card = 5 := by
  rw [supportFinset_card paleyCert19 paleyCert19_valid.1]; rfl

theorem paleyCert31_card : (supportFinset paleyCert31).card = 7 := by
  rw [supportFinset_card paleyCert31 paleyCert31_valid.1]; rfl

theorem paleyCert43_card : (supportFinset paleyCert43).card = 7 := by
  rw [supportFinset_card paleyCert43 paleyCert43_valid.1]; rfl

theorem paleyCert59_card : (supportFinset paleyCert59).card = 9 := by
  rw [supportFinset_card paleyCert59 paleyCert59_valid.1]; rfl

theorem paleyCert71_card : (supportFinset paleyCert71).card = 9 := by
  rw [supportFinset_card paleyCert71 paleyCert71_valid.1]; rfl

theorem paleyCert103_card : (supportFinset paleyCert103).card = 11 := by
  rw [supportFinset_card paleyCert103 paleyCert103_valid.1]; rfl

theorem paleyCert3_lt : ∀ s ∈ supportFinset paleyCert3, s < 3 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert3 _).mp hs
  exact (paleyCert3_valid.2.1 (_, r) hr).1

theorem paleyCert7_lt : ∀ s ∈ supportFinset paleyCert7, s < 7 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert7 _).mp hs
  exact (paleyCert7_valid.2.1 (_, r) hr).1

theorem paleyCert11_lt : ∀ s ∈ supportFinset paleyCert11, s < 11 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert11 _).mp hs
  exact (paleyCert11_valid.2.1 (_, r) hr).1

theorem paleyCert19_lt : ∀ s ∈ supportFinset paleyCert19, s < 19 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert19 _).mp hs
  exact (paleyCert19_valid.2.1 (_, r) hr).1

theorem paleyCert31_lt : ∀ s ∈ supportFinset paleyCert31, s < 31 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert31 _).mp hs
  exact (paleyCert31_valid.2.1 (_, r) hr).1

theorem paleyCert43_lt : ∀ s ∈ supportFinset paleyCert43, s < 43 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert43 _).mp hs
  exact (paleyCert43_valid.2.1 (_, r) hr).1

theorem paleyCert59_lt : ∀ s ∈ supportFinset paleyCert59, s < 59 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert59 _).mp hs
  exact (paleyCert59_valid.2.1 (_, r) hr).1

theorem paleyCert71_lt : ∀ s ∈ supportFinset paleyCert71, s < 71 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert71 _).mp hs
  exact (paleyCert71_valid.2.1 (_, r) hr).1

theorem paleyCert103_lt : ∀ s ∈ supportFinset paleyCert103, s < 103 := fun _ hs => by
  obtain ⟨r, hr⟩ := (mem_supportFinset paleyCert103 _).mp hs
  exact (paleyCert103_valid.2.1 (_, r) hr).1

/-! ## Square-freeness of the nine moduli

A prime is square-free. These are the hypotheses `lemmaA` takes when the blocks are
lifted in `FsLowerBound.Construction`. -/

theorem squarefree_3 : Squarefree 3 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible

theorem squarefree_7 : Squarefree 7 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible

theorem squarefree_11 : Squarefree 11 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible

theorem squarefree_19 : Squarefree 19 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible

theorem squarefree_31 : Squarefree 31 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible

theorem squarefree_43 : Squarefree 43 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible

theorem squarefree_59 : Squarefree 59 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible

theorem squarefree_71 : Squarefree 71 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible

theorem squarefree_103 : Squarefree 103 :=
  Irreducible.squarefree (Nat.Prime.prime (by norm_num)).irreducible
