import FsLowerBound.LemmaA

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false
-- The step lemmas carry §1.3's standing hypotheses whether or not their proofs consume
-- them, exactly as in `FsLowerBound.LemmaA`; the module docstring's inert-hypothesis roll
-- call lists all eleven and says why they stay.
set_option linter.unusedVariables false

/-!
# Lemma B — from a ranked block to a square-difference-free set of integers

This file formalizes §1.3 of `krachun-proofs.md` (Krachun's Lemma 4): a ranked block `C`
on `Z/PZ` with `P` a perfect square and a ranking of height `H` produces, for every
`L ≥ 1`, a square-difference-free set `A_L ⊆ {1, …, (P H)^L}` with `|A_L| = |C|^L`.

The headline is the triple `lemmaB_sdf`, `integerSet_subset`, `integerSet_card`; `D`'s
link to those three, `le_D_of_sdf`, is at the bottom, and `lemmaB_card_le_D` packages all
four into the one inequality Stage 4 consumes.

Everything between is the step spine, one named lemma per move of §1.3 so that the audit
can map Lean to prose one-to-one:

| Lean | §1.3 |
| --- | --- |
| `exists_least_digit_ne_of_lt` | "let `j` be the least base-`P` position where `X`, `Y` differ" |
| Stage 2's `diffMod_unique` | reduction mod `P^L`: `k² ≡ Y − X` |
| `word_step0_exact_dvd` | `Y − X = P^j(δ + PZ)`, i.e. `P^j` divides exactly |
| `word_step1_leading_digit` | `δ = y_j − x_j`, no borrows from below `j` |
| `word_step2_pow_dvd_sq` | `P^j` divides both `Y − X` and `P^L`, hence `P^j ∣ k²` |
| `word_step3_root_split` | `q^{2j} ∣ k²` hence `q^j ∣ k` — H4.1, `P = q²` for *any* `q` |
| `word_step4_leading_square` | "dividing by `P^j` shows that `δ` is a square modulo `P`" |
| `word_step5_rank_drop` | "since `j` is the smallest index …, `h_L(X) > h_L(Y)`" |
| `word_mod_pow`, `wordEmbed_injOn` | "the reductions of two distinct elements are distinct" |
| `integerSet_lt_of_rank_lt` | "the displayed integer would be at most `(P^L − 1) − P^L`" |
| `wordBlock_card` | "`B_L` … has `|C|^L` elements" |
| `wordRank_lt_pow` | `h_L ≤ H^L − 1`, the interval bookkeeping H4.6 |

The contrast with Stage 2 is worth stating, because it is where §1.3 is *easier* than §5.
Lemma A needed square-freeness of `m` and a two-case `p`-adic valuation argument to know
that the valuation of a nonzero square residue is even (Steps 2 and 3 there). Lemma B
needs none of it: `P = q²` makes `P^j = (q^j)²` a square outright, so
`(q^j)² ∣ k²` gives `q^j ∣ k` for *every* positive `q` — one application of
`Nat.pow_dvd_pow_iff`. That single lemma, `word_step3_root_split`, replaces Stage 2's
entire Step 2/Step 3 block. No primality and no square-freeness enters this file.

## Choices made here beyond the design brief

The brief pinned `wordBlock`, `wordRank`, `integerSet`, `lemmaB_sdf`, `integerSet_subset`,
`integerSet_card` and `le_D_of_sdf` verbatim; those are reproduced exactly. The rest is
decided here.

* **The spine is stated at general word length `L`, not at `2 * e`.** Stage 2's
  `step0_exact_dvd` and `step1_leading_digit` say the same two things, but their statements
  hard-code the modulus `m ^ (2 * e)` and the bound `r < 2 * e`, because §5's positions come
  in pairs. Lemma B's `L` is arbitrary. Rather than restate Stage 2 at a general exponent —
  which would move frozen, audited statements — the two facts are re-stated here at
  `P ^ L` and bridged back to Stage 2 by `diffMod_pow_mod_pow`: for `X, Y < P ^ L` the two
  differences `diffMod (P ^ L) X Y` and `diffMod (P ^ (2 * L)) X Y` agree modulo `P ^ L`,
  and every conclusion of Steps 0 and 1 at a position `j < L` reads only the difference
  modulo `P ^ (j + 1)`. So `word_step0_exact_dvd` and `word_step1_leading_digit` are
  intended to be *derived* from their Stage-2 namesakes, not reproved. A later refactor
  could instead generalize the Stage-2 pair to a bare exponent `N` and derive both; that is
  a Stage-2 edit and is deliberately not taken here.
* **`exists_least_digit_ne_of_lt` is a wrapper, not a copy.** Stage 2's
  `exists_least_digit_ne` applied with `e := L` already produces a least differing position
  below `2 * L`; `digit_eq_zero_of_lt` then rules out the positions from `L` up, since both
  words are below `P ^ L`.
* **The unreduced-witness form of `diffMod_unique` is taken from Stage 2, not restated
  here.** Lemma B needs `(X + c) % M = Y → diffMod M X Y = c % M` with `c` the square
  `k ^ 2`, which is not a residue. An earlier draft carried its own
  `diffMod_eq_of_add_mod` for that; Stage 2's `diffMod_unique` has instead been generalized
  in place — its `c < m` hypothesis dropped, its conclusion reduced, and it made public —
  and has since joined the rest of the `diffMod` toolkit in `FsLowerBound.Defs`, so
  `word_rank_drop_of_sq` and `lemmaB_sdf` call it directly and this file states nothing
  of its own about `diffMod`.
* **Two Stage-2 lemmas are promoted from `private` to public** rather than duplicated
  here: `sum_reflect_lt_pow` (the reversed-weight base-`H` string bound, which is exactly
  `wordRank_lt_pow` and `wordRank_tail_lt` at radix `P`) and `digit_succ` (peeling one
  digit off the bottom, which is what `mem_wordBlock_succ` runs on). Both were already
  inside the transitive closure of `auditedDeclarations`, so the audit's exhaustiveness is
  unchanged.
* **`hH : 1 ≤ H` is kept on `integerSet_subset` and `integerSet_card`,** as pinned, even
  though it looks derivable: if `C = ∅` and `L ≥ 1` the block is empty and both claims are
  vacuous, if `L = 0` the set is `{1}` and the interval is `{1}`, and otherwise some
  `h c < H` forces `H ≥ 1`. It is kept because the brief pins it and because the prose
  carries it. On `integerSet_subset` it turned out to be load-bearing after all — it is
  what feeds `wordRank_lt_pow` — and on `integerSet_card` it is inert, as expected.

  As in Stage 2, the finished proofs need less than §1.3's paragraphs assume. Eleven
  binders across seven declarations are *inert*, in that the declaration carrying them
  never consumes them, and they are kept for the same reason Stage 2 keeps its own: each
  statement is meant to match its §1.3 sentence hypothesis for hypothesis, so a reader
  checking Lean against the prose never has to reconcile two lists. That, and not a wish
  to rename them `_hL`, is why `linter.unusedVariables` is off at the top of the file.
  The roll call, taken from a build with the linter on:

  * `wordRank_lt_pow`, `wordRank_tail_lt`: `hH : 0 < H`. Both reduce to Stage 2's
    `sum_reflect_lt_pow`, where the digit bound already forces `H` positive whenever the
    range is nonempty, and the empty range gives `0 < H ^ 0 = 1`. Stage 2's
    `liftRank_lt_pow` and `liftRank_tail_lt` carry the same pair inertly.
  * `word_step4_leading_square`: `hL : 1 ≤ L`, `hd : d ≠ 0`, `hdlt : d < P ^ L`,
    `hk : k ≠ 0`. §1.3 states all four, and Stage 2's `step4_leading_square` carries their
    analogues; here the proof runs entirely off `hj : j < L` (which supplies `1 ≤ L`, and
    `L - j ≠ 0` for the `dvd_pow_self`), off `hsq` and off `h2`. The nonzeroness of `δ`
    comes from `h2 : ¬ P ^ (j + 1) ∣ d`, not from `hd`.
  * `word_step5_rank_drop`: `hXC`. The tail bound is needed only for `Y`, so only `hYC`
    is consumed; `hXC` is kept because §1.3's lexicographic step is symmetric in the two
    words and stating it one-sided would misdescribe the hypothesis.
  * `word_base_count`: `hP : 0 < P`. `hC : ∀ c ∈ C, c < P` already empties `C` when
    `P = 0`, and both sides are then `0`.
  * `integerSet_lt_of_rank_lt`: `hP : 0 < P`, `hX : X < P ^ L`. The inequality is
    `Y < P ^ L ≤ P ^ L · (rank X − rank Y)` plus `0 ≤ X`; the bound on `X` and the
    positivity of `P` never enter.
  * `integerSet_card`: `hH : 1 ≤ H`. Only `hC.1`, the residue bound, is used —
    `wordEmbed_injOn` needs no hypothesis at all.
* **No `2 ≤ P` hypothesis on the headline statements.** `hP : P = n ^ 2` supplies it where
  it is needed: `n = 0` makes the block empty for `L ≥ 1`, and `n = 1` makes `P ^ L = 1`,
  so `X = Y = 0` and there is no pair to check. The degenerate branches are part of the
  work `lemmaB_sdf` and `word_rank_drop_of_sq` have to do; the step lemmas below take
  `2 ≤ P` explicitly, as Stage 2's do.
* **`word_rank_drop_of_sq` is the seam.** It is §1.3's first paragraph entire — from a
  square congruence mod `P ^ L` between two distinct words to a strict drop of `wordRank` —
  and `lemmaB_sdf` is then that lemma plus `integerSet_lt_of_rank_lt`, the size
  contradiction of §1.3's second paragraph. Splitting there keeps the perfect-square
  hypothesis and the interval bookkeeping in separate proofs.
* **`wordBlock_card` is stated with no side condition on `P`,** matching the shape
  `liftBlock_card` settled on. The digit-string bijection is `wordBlock_card_of_pos`;
  `P = 0` is settled by inspection, `hC` having emptied `C`. Note that unlike
  `liftBlock_card` there is **no free-digit factor**: all `L` positions are constrained, so
  the count is `C.card ^ L`, not `(P * C.card) ^ L`.
* **`lemmaB_card_le_D` is an addition.** It is the single inequality Stage 4 wants —
  `|C|^L ≤ D((P H)^L)` — and stating it now pins the shape the three headline lemmas have
  to compose into.
* **Two `private` helpers carry work that no pinned statement names.**
  `dvd_iff_of_mod_eq` transports divisibility by a divisor `k` of `M` across a congruence
  mod `M`; it is what turns `diffMod_pow_mod_pow`'s statement *about residues* into Step
  0's conclusion *about divisibility*, since `P ^ j` and `P ^ (j + 1)` both divide `P ^ L`
  for `j < L`. `wordBlock_succ_card` is the one level of the counting recursion where the
  bijection `X ↦ (X % P, X / P)` is actually built; `wordBlock_card_of_pos` is then a
  three-line induction on it. Both sit immediately before their single use, and neither
  states anything the audit needs to see separately — each is inside the transitive
  closure of a named headline.
* **`word_base_count` is proved as pinned but goes unused.** Because the skeleton also
  pins `mem_wordBlock_succ`, `wordBlock_succ_card`'s `card_nbij'` runs straight off that
  iff rather than redoing the digit bookkeeping against a filtered `range P`. The lemma is
  kept — it is pinned, and it is the honest contrast with Stage 2's `base_count`, which
  returns `|S| · m` where this returns `|C|` — and it is named in `auditedDeclarations`
  individually, since nothing else reaches it.

## Trust rules (ADR-033)

The ADR-033 trust rules apply: no kernel-external decision procedures, no postulated
constants, no compiler escape hatches. Every declaration below is proved; this file
carries no placeholders. `lemmaB_sdf`, `integerSet_subset`, `integerSet_card`,
`le_D_of_sdf` and `lemmaB_card_le_D` are named in `auditedDeclarations` in
`Test/AxiomAudit.lean`, which reaches the whole step spine beneath them, together with
`word_base_count` — the one lemma here that nothing else calls.
-/

/-! ## Words in base `P` -/

/-- `C^L` read as a set of residues: the `X < P ^ L` whose *every* base-`P` digit below
position `L` lies in `C`.

Unlike `liftBlock` there are no free positions — all `L` digits are constrained — which is
why `wordBlock_card` has no factor of `P` in it. -/
def wordBlock (P L : ℕ) (C : Finset ℕ) : Finset ℕ :=
  (Finset.range (P ^ L)).filter (fun X => ∀ j < L, digit P j X ∈ C)

/-- `h_L` of §1.3: the base-`H` number whose digits are the ranks of the base-`P` digits of
`X`, with the *lowest* position most significant. The weight `H ^ (L − 1 − j)` at position
`j` is what makes the lexicographic comparison of `word_step5_rank_drop` work. -/
def wordRank (P L H : ℕ) (h : ℕ → ℕ) (X : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, h (digit P j X) * H ^ (L - 1 - j)

/-- `A_L` of §1.3: the set `B_L = {X + P^L · h_L(X) : X ∈ wordBlock}`, translated by one so
that it lands in `{1, …, (P H)^L}` rather than `{0, …, (P H)^L − 1}`. -/
def integerSet (P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) : Finset ℕ :=
  (wordBlock P L C).image (fun X => X + P ^ L * wordRank P L H h X + 1)

/-- Membership in the word block, unfolded. -/
theorem mem_wordBlock (P L : ℕ) (C : Finset ℕ) (X : ℕ) :
    X ∈ wordBlock P L C ↔ X < P ^ L ∧ ∀ j < L, digit P j X ∈ C := by
  simp [wordBlock, Finset.mem_filter, Finset.mem_range]

/-- Membership in `A_L`, unfolded: an element is the translate of some word's code. -/
theorem mem_integerSet (P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) (a : ℕ) :
    a ∈ integerSet P L H C h ↔
      ∃ X ∈ wordBlock P L C, X + P ^ L * wordRank P L H h X + 1 = a := by
  simp only [integerSet, Finset.mem_image]

/-! ## The rank as a base-`H` string -/

/-- `h_L` is a base-`H` string of length `L`, hence `< H ^ L`. This is H4.6's half of the
interval bookkeeping. Discharges from Stage 2's `sum_reflect_lt_pow`. -/
theorem wordRank_lt_pow (P L H : ℕ) (h : ℕ → ℕ) (X : ℕ) (hH : 0 < H)
    (hb : ∀ i < L, h (digit P i X) < H) :
    wordRank P L H h X < H ^ L :=
  sum_reflect_lt_pow H (fun i => h (digit P i X)) L hb

/-- `wordRank` split at position `j`: the digits below `j`, the digit at `j`, the tail. -/
theorem wordRank_split (P L H j : ℕ) (h : ℕ → ℕ) (X : ℕ) (hj : j < L) :
    wordRank P L H h X =
      (∑ i ∈ Finset.range j, h (digit P i X) * H ^ (L - 1 - i))
        + h (digit P j X) * H ^ (L - 1 - j)
        + ∑ i ∈ Finset.Ico (j + 1) L, h (digit P i X) * H ^ (L - 1 - i) := by
  rw [wordRank, ← Finset.sum_range_add_sum_Ico
    (fun i => h (digit P i X) * H ^ (L - 1 - i)) (Nat.succ_le_of_lt hj),
    Finset.sum_range_succ]

/-- The geometric bound behind the lexicographic step: everything strictly above position
`j` is worth less than one unit at position `j`. -/
theorem wordRank_tail_lt (P L H j : ℕ) (h : ℕ → ℕ) (X : ℕ) (hH : 0 < H) (hj : j < L)
    (hb : ∀ i < L, h (digit P i X) < H) :
    ∑ i ∈ Finset.Ico (j + 1) L, h (digit P i X) * H ^ (L - 1 - i) < H ^ (L - 1 - j) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hN : L - 1 - j = L - (j + 1) := by omega
  have hcongr : ∑ k ∈ Finset.range (L - (j + 1)),
        h (digit P (j + 1 + k) X) * H ^ (L - 1 - (j + 1 + k))
      = ∑ k ∈ Finset.range (L - (j + 1)),
        h (digit P (j + 1 + k) X) * H ^ (L - (j + 1) - 1 - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    congr 2
    omega
  rw [hN, hcongr]
  exact sum_reflect_lt_pow H (fun k => h (digit P (j + 1 + k) X)) (L - (j + 1))
    fun k hk => hb _ (by omega)

/-! ## The least differing position, and the bridge to Stage 2's modulus -/

/-- §1.3's `j`: the least base-`P` position at which two distinct words below `P ^ L`
differ. A wrapper on Stage 2's `exists_least_digit_ne` at `e := L`, with the positions from
`L` up ruled out by `digit_eq_zero_of_lt`. -/
theorem exists_least_digit_ne_of_lt (P L X Y : ℕ) (hP : 2 ≤ P)
    (hX : X < P ^ L) (hY : Y < P ^ L) (hXY : X ≠ Y) :
    ∃ j, j < L ∧ digit P j X ≠ digit P j Y ∧ ∀ i < j, digit P i X = digit P i Y := by
  have hP0 : 0 < P := by omega
  have hle : P ^ L ≤ P ^ (2 * L) := Nat.pow_le_pow_right hP0 (by omega)
  obtain ⟨r, hrlt, hrne, hrlow⟩ :=
    exists_least_digit_ne P L X Y hP (lt_of_lt_of_le hX hle) (lt_of_lt_of_le hY hle) hXY
  refine ⟨r, ?_, hrne, hrlow⟩
  by_contra hcon
  have hLr : L ≤ r := by omega
  have hxz : digit P r X = 0 :=
    digit_eq_zero_of_lt P r X (lt_of_lt_of_le hX (Nat.pow_le_pow_right hP0 hLr))
  have hyz : digit P r Y = 0 :=
    digit_eq_zero_of_lt P r Y (lt_of_lt_of_le hY (Nat.pow_le_pow_right hP0 hLr))
  exact hrne (by rw [hxz, hyz])

/-- The bridge that lets Stage 2's Steps 0 and 1 be reused at word length `L`. For words
below `P ^ L`, the difference taken modulo `P ^ L` and the difference taken modulo the
larger `P ^ N` agree modulo `P ^ L` — the two wraparound terms differ by a multiple of
`P ^ L`. Every conclusion of Steps 0 and 1 at a position `j < L` reads the difference only
modulo `P ^ (j + 1)`, and `j + 1 ≤ L`. -/
theorem diffMod_pow_mod_pow (P L N X Y : ℕ) (hP : 2 ≤ P) (hLN : L ≤ N)
    (hX : X < P ^ L) (hY : Y < P ^ L) :
    diffMod (P ^ L) X Y % P ^ L = diffMod (P ^ N) X Y % P ^ L := by
  have hP0 : 0 < P := by omega
  have hLpos : 0 < P ^ L := Nat.pow_pos hP0
  have hNpos : 0 < P ^ N := Nat.pow_pos hP0
  have hle : P ^ L ≤ P ^ N := Nat.pow_le_pow_right hP0 hLN
  obtain ⟨c, hc⟩ : P ^ L ∣ P ^ N := Nat.pow_dvd_pow P hLN
  have hmod : (X + diffMod (P ^ N) X Y) % P ^ L = Y := by
    rcases diffMod_add (P ^ N) X Y hNpos (lt_of_lt_of_le hX hle) (lt_of_lt_of_le hY hle) with
      hh | hh
    · rw [hh, Nat.mod_eq_of_lt hY]
    · rw [hh, hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hY]
  rw [Nat.mod_eq_of_lt (diffMod_lt _ X Y hLpos)]
  exact diffMod_unique (P ^ L) X Y (diffMod (P ^ N) X Y) hLpos hX hY hmod

/-- Congruence modulo `M` transfers divisibility by any divisor `k` of `M`. This is what
turns `diffMod_pow_mod_pow` into a statement about `P ^ j ∣ ·`: the two differences agree
modulo `P ^ L`, and both `P ^ j` and `P ^ (j + 1)` divide `P ^ L` when `j < L`. -/
private theorem dvd_iff_of_mod_eq (a b M k : ℕ) (hdvd : k ∣ M) (h : a % M = b % M) :
    k ∣ a ↔ k ∣ b := by
  have hk : a % k = b % k := by
    rw [← Nat.mod_mod_of_dvd a hdvd, h, Nat.mod_mod_of_dvd b hdvd]
  constructor
  · intro ha
    exact Nat.dvd_of_mod_eq_zero (by rw [← hk]; exact Nat.mod_eq_zero_of_dvd ha)
  · intro hb
    exact Nat.dvd_of_mod_eq_zero (by rw [hk]; exact Nat.mod_eq_zero_of_dvd hb)

/-! ## Step 0 — exact divisibility at the least differing position -/

/-- Step 0 at word length `L`: with `j` the least differing digit position,
`j = v_P(diffMod (P ^ L) X Y)`. §1.3 writes this as `Y − X = P^j(δ + PZ)` with
`δ ≢ 0 (mod P)`.

Intended discharge: `diffMod_pow_mod_pow` with `N := 2 * L`, then Stage 2's
`step0_exact_dvd` at `m := P`, `e := L`. -/
theorem word_step0_exact_dvd (P L X Y j : ℕ) (hP : 2 ≤ P) (hL : 1 ≤ L)
    (hX : X < P ^ L) (hY : Y < P ^ L) (hj : j < L)
    (hne : digit P j X ≠ digit P j Y) (hlow : ∀ i < j, digit P i X = digit P i Y) :
    P ^ j ∣ diffMod (P ^ L) X Y ∧ ¬ P ^ (j + 1) ∣ diffMod (P ^ L) X Y := by
  have hP0 : 0 < P := by omega
  have hle : P ^ L ≤ P ^ (2 * L) := Nat.pow_le_pow_right hP0 (by omega)
  have hbridge := diffMod_pow_mod_pow P L (2 * L) X Y hP (by omega) hX hY
  obtain ⟨h1, h2⟩ := step0_exact_dvd P L X Y j hP hL (lt_of_lt_of_le hX hle)
    (lt_of_lt_of_le hY hle) (by omega) hne hlow
  refine ⟨?_, fun hcon => h2 ?_⟩
  · exact (dvd_iff_of_mod_eq _ _ _ _ (Nat.pow_dvd_pow P (by omega : j ≤ L)) hbridge).mpr h1
  · exact (dvd_iff_of_mod_eq _ _ _ _ (Nat.pow_dvd_pow P (by omega : j + 1 ≤ L)) hbridge).mp hcon

/-! ## Step 1 — the leading digit, without borrows -/

/-- Step 1 at word length `L`: the `j`-th digit of the difference is the difference of the
`j`-th digits, `δ = y_j − x_j`. Positions below `j` agree, so nothing borrows into `j`.

Intended discharge: `diffMod_pow_mod_pow` with `N := 2 * L`, then Stage 2's
`step1_leading_digit`. -/
theorem word_step1_leading_digit (P L X Y j : ℕ) (hP : 2 ≤ P) (hL : 1 ≤ L)
    (hX : X < P ^ L) (hY : Y < P ^ L) (hj : j < L)
    (hlow : ∀ i < j, digit P i X = digit P i Y) :
    digit P j (diffMod (P ^ L) X Y) = diffMod P (digit P j X) (digit P j Y) := by
  have hP0 : 0 < P := by omega
  have hle : P ^ L ≤ P ^ (2 * L) := Nat.pow_le_pow_right hP0 (by omega)
  have hbridge := diffMod_pow_mod_pow P L (2 * L) X Y hP (by omega) hX hY
  have hdig : digit P j (diffMod (P ^ L) X Y) = digit P j (diffMod (P ^ (2 * L)) X Y) :=
    (mod_pow_eq_iff_digits_eq P L _ _ hP).mp hbridge j hj
  rw [hdig]
  exact step1_leading_digit P L X Y j hP hL (lt_of_lt_of_le hX hle) (lt_of_lt_of_le hY hle)
    (by omega) hlow

/-! ## Steps 2–4 — the leading digit is a nonzero square mod `P`

This is the short stretch of §1.3 that replaces Stage 2's valuation machinery outright.
`P = q²` is the whole of it. -/

/-- Step 2: `P ^ j` divides `diffMod (P ^ L) X Y` and divides `P ^ L`, so it divides
`k ^ 2` as well. -/
theorem word_step2_pow_dvd_sq (P L j k d : ℕ) (hj : j < L)
    (hd : k ^ 2 % P ^ L = d) (h1 : P ^ j ∣ d) :
    P ^ j ∣ k ^ 2 := by
  have hdvdL : P ^ j ∣ P ^ L := Nat.pow_dvd_pow P (Nat.le_of_lt hj)
  have hsplit : P ^ L * (k ^ 2 / P ^ L) + k ^ 2 % P ^ L = k ^ 2 := Nat.div_add_mod _ _
  rw [← hsplit, hd]
  exact Nat.dvd_add (hdvdL.mul_right _) h1

/-- Step 3, and the whole of H4.1: for `P = q²` a perfect square with `q` *any* natural
number — no primality, no square-freeness — `P ^ j = (q ^ j) ^ 2` divides `k ^ 2` exactly
when `q ^ j` divides `k`, so the square splits off a factor `P ^ j`.

Intended discharge: `Nat.pow_dvd_pow_iff` at exponent `2`. -/
theorem word_step3_root_split (n P j k : ℕ) (hP : P = n ^ 2) (hdvd : P ^ j ∣ k ^ 2) :
    ∃ u, k ^ 2 = P ^ j * u ^ 2 := by
  subst hP
  have h1 : (n ^ j) ^ 2 ∣ k ^ 2 := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    exact hdvd
  obtain ⟨u, hu⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).mp h1
  refine ⟨u, ?_⟩
  rw [hu, mul_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]

/-- Step 4: after dividing by `P ^ j`, the leading digit `δ` is congruent to `u ^ 2` mod
`P` — the tail `lam * P ^ (L − j)` is a multiple of `P` because `j < L` — and it is nonzero
because `P ^ (j + 1)` does not divide the difference. So `δ ∈ Q_P`.

The analogue of Stage 2's `step4_leading_square`, with `hsq` in place of that lemma's
`hu : z = m ^ j * u`; here the square, not the root, is what splits. -/
theorem word_step4_leading_square (P L j k lam u d : ℕ) (hP : 2 ≤ P) (hL : 1 ≤ L)
    (hd : d ≠ 0) (hdlt : d < P ^ L) (hk : k ≠ 0) (hj : j < L)
    (hlam : k ^ 2 = d + lam * P ^ L) (hsq : k ^ 2 = P ^ j * u ^ 2)
    (h1 : P ^ j ∣ d) (h2 : ¬ P ^ (j + 1) ∣ d) :
    IsNonzeroSquareMod P (digit P j d) := by
  have hP0 : 0 < P := by omega
  have hp : 0 < P ^ j := Nat.pow_pos hP0
  obtain ⟨d', hd'⟩ := h1
  have hdig : digit P j d = d' % P := by
    rw [digit, hd', Nat.mul_div_cancel_left _ hp]
  have hsplit : P ^ L = P ^ j * P ^ (L - j) := by
    rw [← pow_add]; congr 1; omega
  have hkey : P ^ j * u ^ 2 = P ^ j * (d' + lam * P ^ (L - j)) := by
    rw [← hsq, hlam, hd', hsplit]; ring
  have hu2 : u ^ 2 = d' + lam * P ^ (L - j) := Nat.eq_of_mul_eq_mul_left hp hkey
  obtain ⟨c, hc⟩ : P ∣ P ^ (L - j) := dvd_pow_self P (by omega)
  have hrw : lam * (P * c) = P * (lam * c) := by ring
  have hmod : u ^ 2 % P = d' % P := by
    rw [hu2, hc, hrw, Nat.add_mul_mod_self_left]
  refine ⟨?_, u % P, Nat.mod_lt _ hP0, ?_⟩
  · rw [hdig, Nat.mod_mod_of_dvd _ dvd_rfl]
    intro hzero
    obtain ⟨c₂, hc₂⟩ : P ∣ d' := Nat.dvd_of_mod_eq_zero hzero
    exact h2 ⟨c₂, by rw [hd', hc₂, pow_succ]; ring⟩
  · rw [hdig, Nat.mod_mod_of_dvd _ dvd_rfl, ← Nat.mul_mod, ← pow_two, hmod]

/-! ## Step 5 — the rank drop -/

/-- Step 5 at word length `L`: a drop of at least one unit at position `j`, equal digits
below it, and the geometric tail bound above it give `h_L(Y) < h_L(X)`. The analogue of
Stage 2's `step5_rank_drop`, with every position constrained rather than every even one. -/
theorem word_step5_rank_drop (P L H j : ℕ) (h : ℕ → ℕ) (C : Finset ℕ) (X Y : ℕ)
    (hH : 0 < H) (hj : j < L)
    (hXC : ∀ i < L, digit P i X ∈ C) (hYC : ∀ i < L, digit P i Y ∈ C)
    (hbd : ∀ c ∈ C, h c < H)
    (hlow : ∀ i < j, digit P i X = digit P i Y)
    (hdrop : h (digit P j Y) < h (digit P j X)) :
    wordRank P L H h Y < wordRank P L H h X := by
  have hby : ∀ i < L, h (digit P i Y) < H := fun i hi => hbd _ (hYC i hi)
  have htail := wordRank_tail_lt P L H j h Y hH hj hby
  have hmul : (h (digit P j Y) + 1) * H ^ (L - 1 - j)
      ≤ h (digit P j X) * H ^ (L - 1 - j) := Nat.mul_le_mul_right _ hdrop
  have hexp : (h (digit P j Y) + 1) * H ^ (L - 1 - j)
      = h (digit P j Y) * H ^ (L - 1 - j) + H ^ (L - 1 - j) := by ring
  have hlowsum : (∑ i ∈ Finset.range j, h (digit P i X) * H ^ (L - 1 - i))
      = ∑ i ∈ Finset.range j, h (digit P i Y) * H ^ (L - 1 - i) :=
    Finset.sum_congr rfl fun i hi => by rw [hlow i (Finset.mem_range.mp hi)]
  rw [wordRank_split P L H j h X hj, wordRank_split P L H j h Y hj, hlowsum]
  omega

/-! ## The word is recoverable from its code -/

/-- The code `X + P^L h_L(X)` reduces to `X` modulo `P ^ L`: the rank term is a multiple of
`P ^ L` and `X` is below it. This is H4.4, "equality of the reductions would give the same
word". -/
theorem word_mod_pow (P L H : ℕ) (h : ℕ → ℕ) (X : ℕ) (hX : X < P ^ L) :
    (X + P ^ L * wordRank P L H h X) % P ^ L = X := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]

/-- H4.4 as injectivity: distinct words get distinct integers. No hypothesis is needed —
for `P = 0` and `L ≥ 1` the block is empty, and otherwise `word_mod_pow` recovers the
word. This is what `integerSet_card` counts with. -/
theorem wordEmbed_injOn (P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) :
    Set.InjOn (fun X => X + P ^ L * wordRank P L H h X + 1)
      (wordBlock P L C : Set ℕ) := by
  intro X hX Y hY hXY
  simp only [Finset.mem_coe, mem_wordBlock] at hX hY
  dsimp only at hXY
  have h' : X + P ^ L * wordRank P L H h X = Y + P ^ L * wordRank P L H h Y := by omega
  calc X = (X + P ^ L * wordRank P L H h X) % P ^ L := (word_mod_pow P L H h X hX.1).symm
    _ = (Y + P ^ L * wordRank P L H h Y) % P ^ L := by rw [h']
    _ = Y := word_mod_pow P L H h Y hY.1

/-! ## Counting the words -/

/-- One digit peeled off the bottom: the last base-`P` digit must lie in `C`, and what is
left is a word of length `L` on `X / P`. The recursion `wordBlock_card_of_pos` runs on.
Discharges from Stage 2's `digit_succ`. -/
theorem mem_wordBlock_succ (P L : ℕ) (C : Finset ℕ) (hP : 0 < P) (X : ℕ) :
    X ∈ wordBlock P (L + 1) C ↔ X % P ∈ C ∧ X / P ∈ wordBlock P L C := by
  rw [mem_wordBlock, mem_wordBlock]
  constructor
  · rintro ⟨hlt, hdig⟩
    refine ⟨by simpa [digit] using hdig 0 (Nat.succ_pos L), ?_, ?_⟩
    · refine Nat.div_lt_of_lt_mul ?_
      rw [Nat.mul_comm, ← pow_succ]
      exact hlt
    · intro j hj
      rw [← digit_succ]
      exact hdig (j + 1) (by omega)
  · rintro ⟨h0, hlt, hdig⟩
    refine ⟨?_, ?_⟩
    · have hmod : X % P < P := Nat.mod_lt _ hP
      have hkey : P * (X / P) + X % P = X := Nat.div_add_mod X P
      calc X = P * (X / P) + X % P := hkey.symm
        _ < P * (X / P) + P := by omega
        _ = P * (X / P + 1) := by ring
        _ ≤ P * P ^ L := Nat.mul_le_mul_left _ hlt
        _ = P ^ (L + 1) := by rw [pow_succ, Nat.mul_comm]
    · intro j hj
      match j with
      | 0 => simpa [digit] using h0
      | (i + 1) => rw [digit_succ]; exact hdig i (by omega)

/-- The bottom level, counted: of the `P` residues below `P`, exactly the `|C|` in `C`
qualify. There is no free digit to multiply by — the contrast with Stage 2's
`base_count`, which returns `|S| · m`. -/
theorem word_base_count (P : ℕ) (hP : 0 < P) (C : Finset ℕ) (hC : ∀ c ∈ C, c < P) :
    ((Finset.range P).filter (fun u => u % P ∈ C)).card = C.card := by
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hu, hmem⟩; rwa [Nat.mod_eq_of_lt hu] at hmem
  · intro hu; have := hC u hu; exact ⟨this, by rwa [Nat.mod_eq_of_lt this]⟩

/-- One level of the digit-string recursion, as a count: splitting `X` into `X % P` and
`X / P` is a bijection from `wordBlock P (L + 1) C` onto `C ×ˢ wordBlock P L C`. This is
`mem_wordBlock_succ` transported through `Finset.card_nbij'`, and the only place the
counting argument does any work. -/
private theorem wordBlock_succ_card (P L : ℕ) (hP : 0 < P) (C : Finset ℕ)
    (hC : ∀ c ∈ C, c < P) :
    (wordBlock P (L + 1) C).card = C.card * (wordBlock P L C).card := by
  have hcard : C.card * (wordBlock P L C).card = (C ×ˢ wordBlock P L C).card :=
    (Finset.card_product _ _).symm
  rw [hcard]
  refine Finset.card_nbij' (fun x => (x % P, x / P)) (fun p => p.1 + P * p.2) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, mem_wordBlock_succ P L C hP] at hx
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨hx.1, hx.2⟩
  · rintro ⟨u, v⟩ huv
    simp only [Finset.mem_coe, Finset.mem_product] at huv
    have hulp : u < P := hC u huv.1
    simp only [Finset.mem_coe, mem_wordBlock_succ P L C hP]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hulp, Nat.add_mul_div_left _ _ hP,
      Nat.div_eq_of_lt hulp, Nat.zero_add]
    exact ⟨huv.1, huv.2⟩
  · intro x hx
    change x % P + P * (x / P) = x
    exact Nat.mod_add_div x P
  · rintro ⟨u, v⟩ huv
    simp only [Finset.mem_coe, Finset.mem_product] at huv
    have hulp : u < P := hC u huv.1
    change ((u + P * v) % P, (u + P * v) / P) = (u, v)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hulp, Nat.add_mul_div_left _ _ hP,
      Nat.div_eq_of_lt hulp, Nat.zero_add]

/-- The digit-string bijection, where it is available. -/
theorem wordBlock_card_of_pos (P L : ℕ) (hP : 0 < P) (C : Finset ℕ) (hC : ∀ c ∈ C, c < P) :
    (wordBlock P L C).card = C.card ^ L := by
  induction L with
  | zero => simp [wordBlock, digit]
  | succ L ih => rw [wordBlock_succ_card P L hP C hC, ih, pow_succ, Nat.mul_comm]

/-- The size count `|C^L| = |C|^L`, with no side condition on `P`: `P = 0` collapses `C`
to `∅` through `hC`, and both sides are then `0` for `L ≥ 1` and `1` for `L = 0`. -/
theorem wordBlock_card (P L : ℕ) (C : Finset ℕ) (hC : ∀ c ∈ C, c < P) :
    (wordBlock P L C).card = C.card ^ L := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · have he : C = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => by have := hC c hc; omega
    subst he
    match L with
    | 0 => simp [wordBlock, digit]
    | (n + 1) => simp [wordBlock]
  · exact wordBlock_card_of_pos P L hP C hC

/-! ## Lemma B -/

/-- §1.3's first paragraph, entire: if two distinct words are congruent modulo `P ^ L` up
to a positive square, the rank strictly drops from `X` to `Y`.

This is where the perfect-square hypothesis lives, and where the degenerate `n = 0` and
`n = 1` cases are discharged — the first empties the block, the second collapses `P ^ L`
to `1` so that `X = Y = 0` contradicts `hXY`.

`hcong` is the reduction `k² ≡ Y − X` of the table above; Stage 2's `diffMod_unique`, at
the unreduced witness `c := k ^ 2`, is what puts it in this `diffMod` form. -/
theorem word_rank_drop_of_sq (n P : ℕ) (hP : P = n ^ 2) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)
    (hC : RankedBlock P C h H) (L : ℕ) (hL : 1 ≤ L) (X Y k : ℕ)
    (hX : X ∈ wordBlock P L C) (hY : Y ∈ wordBlock P L C) (hXY : X ≠ Y) (hk : 0 < k)
    (hcong : k ^ 2 % P ^ L = diffMod (P ^ L) X Y) :
    wordRank P L H h Y < wordRank P L H h X := by
  obtain ⟨-, hCbd, hCarc⟩ := hC
  obtain ⟨hXlt, hXC⟩ := (mem_wordBlock P L C X).mp hX
  obtain ⟨hYlt, hYC⟩ := (mem_wordBlock P L C Y).mp hY
  have hPLpos : 0 < P ^ L := Nat.lt_of_le_of_lt (Nat.zero_le X) hXlt
  -- `n = 0` empties the block; `n = 1` collapses `P ^ L` to `1`, so `X = Y` and `hXY` fires.
  have hP2 : 2 ≤ P := by
    rcases Nat.eq_zero_or_pos P with rfl | hPpos
    · rw [Nat.zero_pow (by omega)] at hPLpos; omega
    · rcases Nat.lt_or_ge P 2 with hlt | hge
      · have hP1 : P = 1 := by omega
        subst hP1
        rw [Nat.one_pow] at hXlt hYlt
        omega
      · exact hge
  have hHpos : 0 < H := Nat.lt_of_le_of_lt (Nat.zero_le _) (hCbd _ (hXC 0 (by omega)))
  have hdlt : diffMod (P ^ L) X Y < P ^ L := diffMod_lt _ X Y hPLpos
  have hd0 : diffMod (P ^ L) X Y ≠ 0 := diffMod_ne_zero _ X Y hXlt hYlt hXY
  obtain ⟨j, hjlt, hjne, hjlow⟩ := exists_least_digit_ne_of_lt P L X Y hP2 hXlt hYlt hXY
  obtain ⟨hdvd1, hdvd2⟩ := word_step0_exact_dvd P L X Y j hP2 hL hXlt hYlt hjlt hjne hjlow
  have hks : P ^ j ∣ k ^ 2 :=
    word_step2_pow_dvd_sq P L j k (diffMod (P ^ L) X Y) hjlt hcong hdvd1
  obtain ⟨u, hu⟩ := word_step3_root_split n P j k hP hks
  have hlam : k ^ 2 = diffMod (P ^ L) X Y + k ^ 2 / P ^ L * P ^ L := by
    rw [← hcong]
    exact (Nat.mod_add_div' _ _).symm
  have hsq : IsNonzeroSquareMod P (digit P j (diffMod (P ^ L) X Y)) :=
    word_step4_leading_square P L j k (k ^ 2 / P ^ L) u (diffMod (P ^ L) X Y)
      hP2 hL hd0 hdlt hk.ne' hjlt hlam hu hdvd1 hdvd2
  rw [word_step1_leading_digit P L X Y j hP2 hL hXlt hYlt hjlt hjlow] at hsq
  exact word_step5_rank_drop P L H j h C X Y hHpos hjlt hXC hYC hCbd hjlow
    (hCarc _ (hXC j hjlt) _ (hYC j hjlt) hjne hsq)

/-- §1.3's second paragraph: a strict rank drop makes the code of `Y` *smaller* than the
code of `X`, because the whole word contributes at most `P^L − 1` while one unit of rank
is worth `P^L`. This is the contradiction that closes Lemma B. -/
theorem integerSet_lt_of_rank_lt (P L H : ℕ) (h : ℕ → ℕ) (X Y : ℕ) (hP : 0 < P)
    (hX : X < P ^ L) (hY : Y < P ^ L)
    (hlt : wordRank P L H h Y < wordRank P L H h X) :
    Y + P ^ L * wordRank P L H h Y + 1 < X + P ^ L * wordRank P L H h X + 1 := by
  have hmul : P ^ L * (wordRank P L H h Y + 1) ≤ P ^ L * wordRank P L H h X :=
    Nat.mul_le_mul_left _ hlt
  have hexp : P ^ L * (wordRank P L H h Y + 1)
      = P ^ L * wordRank P L H h Y + P ^ L := by ring
  omega

/-- **Lemma B (Krachun's Lemma 4).** For `P` a perfect square and `C` a ranked block on
`Z/PZ` of height `H`, the integer set `A_L` is square-difference-free.

This is §1.3's theorem, with `RankedBlock` supplying (2.3).

Intended discharge: from `sdfFinset`'s `b = a + k * k`, Stage 2's `diffMod_unique` at
`c := k ^ 2` produces the `hcong` of `word_rank_drop_of_sq`, and
`integerSet_lt_of_rank_lt` turns the resulting rank drop into the contradiction. -/
theorem lemmaB_sdf (n P : ℕ) (hP : P = n ^ 2) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)
    (hC : RankedBlock P C h H) (L : ℕ) (hL : 1 ≤ L) :
    sdfFinset (integerSet P L H C h) := by
  rintro a ha b hb hab ⟨k, hk, hbk⟩
  obtain ⟨X, hX, hXa⟩ := (mem_integerSet P L H C h a).mp ha
  obtain ⟨Y, hY, hYb⟩ := (mem_integerSet P L H C h b).mp hb
  have hXlt : X < P ^ L := ((mem_wordBlock P L C X).mp hX).1
  have hYlt : Y < P ^ L := ((mem_wordBlock P L C Y).mp hY).1
  have hPLpos : 0 < P ^ L := Nat.lt_of_le_of_lt (Nat.zero_le X) hXlt
  have hP0 : 0 < P := by
    rcases Nat.eq_zero_or_pos P with rfl | hPpos
    · rw [Nat.zero_pow (by omega)] at hPLpos; omega
    · exact hPpos
  have hXY : X ≠ Y := by
    rintro rfl
    omega
  -- reduce `b = a + k²` modulo `P ^ L`: the two rank terms are multiples of `P ^ L`
  have hkk : k ^ 2 = k * k := pow_two k
  have heq : X + k ^ 2 + P ^ L * wordRank P L H h X
      = Y + P ^ L * wordRank P L H h Y := by omega
  have hmod : (X + k ^ 2) % P ^ L = Y := by
    rw [← Nat.add_mul_mod_self_left (X + k ^ 2) (P ^ L) (wordRank P L H h X), heq,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hYlt]
  have hcong : k ^ 2 % P ^ L = diffMod (P ^ L) X Y :=
    (diffMod_unique (P ^ L) X Y (k ^ 2) hPLpos hXlt hYlt hmod).symm
  have hdrop := word_rank_drop_of_sq n P hP C h H hC L hL X Y k hX hY hXY hk hcong
  have hlt := integerSet_lt_of_rank_lt P L H h X Y hP0 hXlt hYlt hdrop
  omega

/-- `A_L ⊆ {1, …, (P H)^L}`: the interval bookkeeping H4.6. The translate by one supplies
the lower end; `X ≤ P^L − 1` and `h_L ≤ H^L − 1` supply the upper. -/
theorem integerSet_subset (P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ)
    (hC : RankedBlock P C h H) (hH : 1 ≤ H) :
    integerSet P L H C h ⊆ Finset.Icc 1 ((P * H) ^ L) := by
  intro a ha
  obtain ⟨X, hX, rfl⟩ := (mem_integerSet P L H C h a).mp ha
  obtain ⟨-, hCbd, -⟩ := hC
  obtain ⟨hXlt, hXC⟩ := (mem_wordBlock P L C X).mp hX
  have hw : wordRank P L H h X < H ^ L :=
    wordRank_lt_pow P L H h X (by omega) fun i hi => hCbd _ (hXC i hi)
  rw [Finset.mem_Icc, Nat.mul_pow]
  refine ⟨by omega, ?_⟩
  have hle : P ^ L * wordRank P L H h X + P ^ L ≤ P ^ L * H ^ L := by
    calc P ^ L * wordRank P L H h X + P ^ L = P ^ L * (wordRank P L H h X + 1) := by ring
      _ ≤ P ^ L * H ^ L := Nat.mul_le_mul_left _ hw
  omega

/-- `|A_L| = |C|^L`: `wordEmbed_injOn` plus `wordBlock_card`. -/
theorem integerSet_card (P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ)
    (hC : RankedBlock P C h H) (hH : 1 ≤ H) :
    (integerSet P L H C h).card = C.card ^ L := by
  rw [integerSet, Finset.card_image_of_injOn (wordEmbed_injOn P L H C h)]
  exact wordBlock_card P L C hC.1

/-! ## The link to `D` -/

/-- A square-difference-free subset of `{1, …, N}` is one of the sets `D N` takes the
supremum over, so its size bounds `D N` from below. Unfold `D`, then `Finset.le_sup` on
membership in the filtered powerset. -/
theorem le_D_of_sdf (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (hsdf : sdfFinset A) :
    A.card ≤ D N := by
  unfold D
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hA, hsdf⟩

/-- The one inequality Stage 4 consumes: a ranked block on a perfect-square modulus gives
`D` a lower bound at every word length. `lemmaB_sdf`, `integerSet_subset`,
`integerSet_card` and `le_D_of_sdf`, composed. -/
theorem lemmaB_card_le_D (n P : ℕ) (hP : P = n ^ 2) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)
    (hC : RankedBlock P C h H) (hH : 1 ≤ H) (L : ℕ) (hL : 1 ≤ L) :
    C.card ^ L ≤ D ((P * H) ^ L) := by
  rw [← integerSet_card P L H C h hC hH]
  exact le_D_of_sdf ((P * H) ^ L) (integerSet P L H C h)
    (integerSet_subset P L H C h hC hH) (lemmaB_sdf n P hP C h H hC L hL)
