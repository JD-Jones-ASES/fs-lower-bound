import FsLowerBound.RankedBlocks
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Padics.PadicVal.Basic

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false
-- The step lemmas carry §5's standing hypotheses whether or not their proofs consume them;
-- the module docstring's inert-hypothesis roll call lists all 21 and says why they stay.
set_option linter.unusedVariables false

/-!
# Lemma A — the composite even-digit lift

This file formalizes §5 of `krachun-proofs.md` ("The composite square-free Lemma 3 —
complete proof"): a square-DAG `S` on `Z/mZ` with a ranking of height `H₀`, for `m ≥ 2`
square-free, lifts to a square-DAG on `Z/m^{2e}Z` — the residues whose *even* base-`m`
digits all lie in `S` — with a ranking of height `H₀ ^ e`.

The headline is `lemmaA`. Everything above it is the step spine, one named lemma per step
of §5 so the audit can map Lean to prose one-to-one:

| Lean | §5 |
| --- | --- |
| `exists_least_digit_ne` | the "least differing base-`m` position `r`" of Step 0 |
| `step0_exact_dvd` | Step 0: `m ^ r ∣ d`, `m ^ (r+1) ∤ d`, i.e. `r = v_m(d)` |
| `step1_leading_digit` | Step 1: `δ := (d / m^r) mod m ≡ y_r − x_r`, no borrows below `r` |
| `pow_dvd_iff_forall_prime`, `exists_padicValNat_eq` | `v_m(d) = min_q v_q(d)` |
| `padicValNat_add_of_lt` | Step 2's dominated-term move, as a toolkit lemma (see below) |
| `step2_uncapped`, `step2_capped` | the two coordinate kinds of Step 2 |
| `step2_even` | Step 2's conclusion: `r` is even (and `< 2e`) |
| `step3_pow_dvd` | Step 3: global divisibility `m ^ j ∣ z` |
| `step4_leading_square` | Step 4: the leading digit is in `Q_m` |
| `liftRank_split`, `liftRank_tail_lt`, `step5_rank_drop` | Step 5: the geometric assembly |

One row of that table is a statement of §5's argument rather than a link in the spine.
`padicValNat_add_of_lt` says the dominated term wins in a sum, which is what Step 2's
uncapped case is doing, but `step2_uncapped` does not call it: it runs the same argument
inline on `z ^ 2 = d + lam * m ^ (2 * e)` through `exact_dvd_of_add`, staying at the level
of exact divisibility and never naming the valuation of a sum. The three digit basics
`digit_add_mul_pow_succ`, `digit_eq_zero_of_lt` and `digit_eq_zero_of_pow_dvd` are likewise
proved and public but called by no proof here. All four are named individually in
`auditedDeclarations`, so the audit's transitive closure still covers every proved
declaration this file exports.

## Choices made here beyond the design brief

The brief pinned `digit`, `liftBlock`, `liftRank`, `RankedBlock` and `lemmaA` verbatim;
those are reproduced exactly. The following were left open and are decided here.

* **`Even r` rather than `∃ j, r = 2 * j` as Step 2's conclusion.** `Even` is the Mathlib
  idiom and composes with the `Nat.even_iff` / `Even.two_dvd` toolkit. The `j` of §5 is
  recovered at the point of use in `lemmaA`; the step lemmas that follow (Steps 3–5) take
  `j` explicitly, with `2 * j` substituted for `r` in their hypotheses, so the
  correspondence to the prose stays one-to-one.
* **The λ-decomposition is stated in ℕ as `z ^ 2 = d + lam * m ^ (2 * e)`,** matching the
  brief, with `lam` an explicit parameter rather than `z ^ 2 / m ^ (2 * e)`. Taking it as a
  parameter keeps the step lemmas free of division and lets `lemmaA` supply it once.
  `exists_lambda_of_isNonzeroSquareMod` is the single point where the parameter is produced
  from the `IsNonzeroSquareMod` hypothesis of `RankedBlock`.
* **`z ≠ 0`, `d ≠ 0`, `d < m ^ (2 * e)`, `r < 2 * e`, `j < e` are explicit hypotheses**
  on the step lemmas, even where derivable from the others. §5 uses each of them by name,
  and a skeleton whose hypotheses are exactly the prose's is what lets each proof be
  discharged from its own paragraph rather than from a re-derivation.

  The finished proofs turn out to need less than §5's paragraphs assume: twenty
  binders across eleven declarations — those hypotheses and others — are *inert*, in
  that the declaration carrying them never consumes them. They are kept on purpose — each
  statement is meant to match its §5 paragraph hypothesis for hypothesis, so that a reader
  checking Lean against the prose never
  has to reconcile two different lists — and `linter.unusedVariables` is switched off at
  the top of the file for exactly that reason, rather than the binders being renamed to
  `_he`, `_hsf`, and so on. The roll call, taken from a build with the linter on:

  * `liftRank_lt_pow`, `liftRank_tail_lt`: `hH : 0 < H₀`. Both reduce to
    `sum_reflect_lt_pow`, where the digit bound already forces `H₀` positive whenever the
    range is nonempty, and the empty range gives `0 < H₀ ^ 0 = 1`.
  * `exists_lambda_of_isNonzeroSquareMod`: `hM : 0 < M`. The decomposition is
    `Nat.div_add_mod`, which holds for `M = 0` too; `hd : d < M` is what is used.
  * `step0_exact_dvd`, `step1_leading_digit`: `he : 1 ≤ e` — both run off `hr : r < 2 * e`,
    which already forces `e` positive; `he` is kept so every step lemma of the spine states
    the same standing hypothesis on `e`.
  * `step2_uncapped`, `step2_capped`: `hm : 2 ≤ m` and `hsf : Squarefree m`. Each
    coordinate case runs at a single prime `q ∣ m` on the λ-decomposition alone, so
    neither the size of `m` nor its square-freeness enters.
  * `step2_even`: `he : 1 ≤ e` and `hdlt : d < m ^ (2 * e)`. The parity argument runs on
    valuations, through `h1` / `h2` and the two coordinate cases; the size bound on `d` is
    §5's standing assumption, not a premise of this step. `hsf` *is* consumed here.
  * `step3_pow_dvd`: `he`, `hdlt`, and `h2 : ¬ m ^ (2 * j + 1) ∣ d` — Step 3 needs only the
    lower bound `h1` on the valuation; exactness is what Steps 2 and 4 use. `h2` travels
    with `h1` because §5 states the pair together as `v_m(d) = 2j`. `hsf` is consumed.
  * `step4_leading_square`: `hsf`, `he`, `hd`, `hdlt`, `hz` — five, the largest group. The
    proof runs off `h1`, `h2`, `hj` and `hu : z = m ^ j * u` alone.
  * `step5_rank_drop`: `hxS : ∀ i < e, digit m (2 * i) x ∈ S` — only `y`'s digits need the
    rank bound `hbd` in the tail estimate; `x` enters through `hdrop` alone. Both
    memberships are stated because Step 5 is applied to an arc of the lifted block, where
    both endpoints are in the block.

  One entry there is a fact about the mathematics rather than about Lean, and is worth
  stating plainly: `step2_uncapped`, `step2_capped` and `step4_leading_square` do not
  consume `hsf`. Square-freeness enters the spine at exactly two points — `step2_even`,
  through `exists_padicValNat_eq` (some prime attains `v_m(d)` exactly), and
  `step3_pow_dvd`, through `pow_dvd_iff_forall_prime` (the per-prime bounds reassemble
  into `m ^ j ∣ z`). Steps 2's two coordinate cases and Step 4 hold for any `m ≥ 2`.
* **The κ ∈ {0,1} wraparound is exposed as `diffMod_add`,** a disjunction in ℕ
  (`x + d = y ∨ x + d = y + M`), rather than being hidden inside Step 0. Steps 0 and 1
  both need it, and stating it once in ℕ avoids an `Int.ModEq` layer in the interface.
  Using `Int.ModEq` *inside* a proof remains fine; no statement in this file mentions ℤ.
  It, `diffMod_lt`, `diffMod_ne_zero` and `diffMod_unique` now live in `FsLowerBound.Defs`
  beside `diffMod` itself: they are facts about the definition, used by every stage, and
  nothing in them is particular to the lift.
* **`diffMod_unique` is public and stated at an unreduced witness.** It says
  `(a + c) % m = b → diffMod m a b = c % m`, rather than requiring `c < m` and concluding
  `diffMod m a b = c`. Step 1's witness *is* a residue and recovers the old form through
  `Nat.mod_eq_of_lt`; Lemma B's witness is a square `k ^ 2`, which is not reduced, and it
  consumes this lemma directly rather than restating it. It is stated in
  `FsLowerBound.Defs` with the rest of the `diffMod` toolkit (see below).
* **Step 2's coordinate split is on `padicValNat q z < e` vs `e ≤ padicValNat q z`**
  (rather than the doubled `2 * padicValNat q z < 2 * e` of the prose), which is the same
  split with the factor of `2` cancelled.
* **`digit_add_mul_pow_succ`, `digit_eq_zero_of_lt`, `digit_eq_zero_of_pow_dvd`,
  `eq_of_digits_eq`, `mod_pow_eq_iff_digits_eq`, `mem_liftBlock`, `liftRank_lt_pow`** are
  supporting lemmas the brief called for only as "digit basics"; the exact list and
  signatures are chosen here. The two `diffMod` size facts of that list, `diffMod_lt` and
  `diffMod_ne_zero`, were chosen here too and have since moved to `FsLowerBound.Defs`.
* **`liftBlock_card` is proved in the brief's pinned form, with no side condition on
  `m`.** An earlier draft carried an added `hm : 2 ≤ m`, on the ground that the intended
  proof is the digit-string bijection — residues below `m ^ (2 * e)` correspond to their
  `2 * e` base-`m` digits, `e` of them free and `e` of them ranging over `S` — and that
  bijection degenerates for `m ≤ 1`, where `Finset.range (m ^ (2 * e))` is empty or a
  point and "digit" carries no information. That hypothesis is gone: the bijection now
  lives in the private `liftBlock_card_of_two_le`, and the public statement discharges
  `m ≤ 1` by inspection first. There `hS` collapses `S` to `∅` (for `m = 0`, or for
  `m = 1` with `0 ∉ S`) or to `{0}`, and the block to `∅` or `{0}`, so both sides are `0`
  or `1` by cases on `e`. The pinned statement is therefore reproduced verbatim, and no
  caller has a side condition to check.
* **`squarefree_235` / `squarefree_299` and the four `cert*_lift_*` corollaries** are
  additions: they are the instantiations Stage 4 will consume, and stating them now pins
  the shape `lemmaA` has to have to be usable.

## Stage-3 amendments to the Stage-2 API

This file was frozen when Stage 2 landed. Stage 3 (`FsLowerBound.LemmaB`,
`FsLowerBound.LemmaC`) made exactly four edits to it, all recorded here so that a reader
diffing against the Stage-2 commit finds nothing unexplained:

1. **The `diffMod` toolkit moved to `FsLowerBound.Defs`.** `diffMod_lt`,
   `diffMod_ne_zero`, `diffMod_add` and — completing the same move — `diffMod_unique` are
   facts about the definition rather than about the lift, and all three stages use them.
   Location only: the first three carry their Stage-2 statements byte for byte, and every
   proof moved unchanged. (`diffMod_unique` moved in the generalized form of item 4 below,
   not in its Stage-2 form.)
2. **`digit_succ` was promoted from `private` to public**, for Stage 3's
   `mem_wordBlock_succ`, which peels the same digit at radix `P`.
3. **`sum_reflect_lt_pow` was promoted from `private` to public**, for Stage 3's
   `wordRank_lt_pow` and `wordRank_tail_lt`, which are that bound at radix `P`.
   Both promotions are visibility-only — the statement text is unchanged in each case, and
   both names were already inside the transitive closure of `auditedDeclarations`, so the
   audit's exhaustiveness is untouched.
4. **`diffMod_unique` was generalized in place**, before moving on to `FsLowerBound.Defs`
   with the rest of the toolkit: its `hc : c < m` hypothesis was dropped and its conclusion
   became `diffMod m a b = c % m` instead of `diffMod m a b = c`. This is the one statement
   change, and it is a strict generalization — nothing was weakened and no proof was lost.
   It was `private` in Stage 2, so it was never part of the critiqued public surface. The
   one caller here, `step1_leading_digit`, recovers the old form through `Nat.mod_eq_of_lt`
   (its witness is a digit, already reduced); Stage 3 consumes the unreduced form directly.

No other statement in this file changed, and nothing was deleted.

## Trust rules (ADR-033)

The ADR-033 trust rules apply: no kernel-external decision procedures, no postulated
constants, no compiler escape hatches. Every declaration below is now proved — this file
carries no unproved placeholder — and `lemmaA`, `liftBlock_card`, the two size counts,
`squarefree_235`, `squarefree_299`, the two `cert*_lift_rankedBlock` corollaries and the
four unreached toolkit lemmas are named in `auditedDeclarations` in
`Test/AxiomAudit.lean`. That audit is transitive, so naming `lemmaA` covers the whole
step spine and the digit basics beneath it; the four named separately are the ones no
proof here reaches.
-/

/-! ## Digits -/

/-- The `j`-th base-`m` digit of `x`. Digits are a ℕ-valued *function*, never a list:
`liftBlock` and `liftRank` are conditions on digits, not enumerations of digit strings. -/
def digit (m j x : ℕ) : ℕ := x / m ^ j % m

/-- Digits are residues. -/
theorem digit_lt (m j x : ℕ) (hm : 0 < m) : digit m j x < m :=
  Nat.mod_lt _ hm

/-- Digits above the leading position vanish. -/
theorem digit_eq_zero_of_lt (m j x : ℕ) (hx : x < m ^ j) : digit m j x = 0 := by
  simp [digit, Nat.div_eq_of_lt hx]

/-- Peeling one digit off the bottom: the `(j+1)`-st digit of `x` is the `j`-th digit of
`x / m`. This is the induction hook for `eq_of_digits_eq`, and public because Stage 3's
`mem_wordBlock_succ` peels the same digit at radix `P`. -/
theorem digit_succ (m j x : ℕ) : digit m (j + 1) x = digit m j (x / m) := by
  unfold digit
  rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm,
    ← Nat.div_div_eq_div_mul]

/-- Adding a multiple of `m ^ (j + 1)` leaves the `j`-th digit alone: the carry lands
strictly above position `j`. This is the "no borrows" mechanism of Step 1. -/
theorem digit_add_mul_pow_succ (m j x c : ℕ) (hm : 0 < m) :
    digit m j (x + c * m ^ (j + 1)) = digit m j x := by
  have hp : 0 < m ^ j := Nat.pow_pos hm
  have hrw : x + c * m ^ (j + 1) = x + m ^ j * (c * m) := by ring
  unfold digit
  rw [hrw, Nat.add_mul_div_left _ _ hp, Nat.add_mul_mod_self_right]

/-- If `m ^ r ∣ d` then every digit of `d` below position `r` is zero. -/
theorem digit_eq_zero_of_pow_dvd (m r i d : ℕ) (hm : 0 < m) (hi : i < r) (hdvd : m ^ r ∣ d) :
    digit m i d = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = i + 1 + s := ⟨r - i - 1, by omega⟩
  obtain ⟨k, rfl⟩ := hdvd
  have hp : 0 < m ^ i := Nat.pow_pos hm
  have hrw : m ^ (i + 1 + s) * k = m ^ i * (m * (m ^ s * k)) := by
    rw [pow_add, pow_add, pow_one]; ring
  rw [digit, hrw, Nat.mul_div_cancel_left _ hp, Nat.mul_mod_right]

/-- Two residues below `m ^ n` agreeing in all `n` digits are equal. The contrapositive is
what produces the least differing position `r` of Step 0. -/
private theorem eq_of_digits_eq_aux (m : ℕ) (hm : 0 < m) :
    ∀ (n x y : ℕ), x < m ^ n → y < m ^ n → (∀ j < n, digit m j x = digit m j y) → x = y := by
  intro n
  induction n with
  | zero => intro x y hx hy _; simp at hx hy; omega
  | succ n ih =>
    intro x y hx hy h
    have h0 : x % m = y % m := by simpa [digit] using h 0 (Nat.succ_pos n)
    have hd : x / m = y / m := by
      refine ih _ _ ?_ ?_ ?_
      · rw [Nat.div_lt_iff_lt_mul hm]; rw [pow_succ] at hx; omega
      · rw [Nat.div_lt_iff_lt_mul hm]; rw [pow_succ] at hy; omega
      · intro j hj; rw [← digit_succ, ← digit_succ]; exact h (j + 1) (by omega)
    calc x = m * (x / m) + x % m := (Nat.div_add_mod x m).symm
      _ = m * (y / m) + y % m := by rw [hd, h0]
      _ = y := Nat.div_add_mod y m

theorem eq_of_digits_eq (m n x y : ℕ) (hm : 2 ≤ m) (hx : x < m ^ n) (hy : y < m ^ n)
    (hdig : ∀ i < n, digit m i x = digit m i y) :
    x = y :=
  eq_of_digits_eq_aux m (by omega) n x y hx hy hdig

/-- Truncating `x` at `m ^ n` leaves every digit below position `n` untouched. -/
private theorem digit_mod_pow (m n i x : ℕ) (hi : i < n) :
    digit m i (x % m ^ n) = digit m i x := by
  have hK : m ^ n = m ^ i * m ^ (n - i) := by rw [← pow_add]; congr 1; omega
  have hd : m ∣ m ^ (n - i) := dvd_pow_self m (by omega)
  unfold digit
  rw [hK, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hd]

/-- Agreement of the bottom `n` digits *is* congruence mod `m ^ n`. This is the digit
workhorse the low-position bookkeeping runs on: `eq_of_digits_eq` is its `n`-th-power-free
corollary, and `step0_exact_dvd` and `step1_leading_digit` should both cite it — Step 0 to
turn `hlow` (digits below `r` agree) into `m ^ r ∣ d`, and Step 1 to know that the
positions below `r` contribute nothing to the `r`-th digit of the difference. -/
theorem mod_pow_eq_iff_digits_eq (m n x y : ℕ) (hm : 2 ≤ m) :
    x % m ^ n = y % m ^ n ↔ ∀ i < n, digit m i x = digit m i y := by
  have hm0 : 0 < m := by omega
  have hpow : 0 < m ^ n := Nat.pow_pos hm0
  constructor
  · intro h i hi
    rw [← digit_mod_pow m n i x hi, ← digit_mod_pow m n i y hi, h]
  · intro h
    refine eq_of_digits_eq m n _ _ hm (Nat.mod_lt _ hpow) (Nat.mod_lt _ hpow) ?_
    intro i hi
    rw [digit_mod_pow m n i x hi, digit_mod_pow m n i y hi]
    exact h i hi

/-- Step 0's `r`: the least base-`m` position at which two distinct residues below
`m ^ (2 * e)` differ. It exists and is `< 2 * e`. -/
theorem exists_least_digit_ne (m e x y : ℕ) (hm : 2 ≤ m)
    (hx : x < m ^ (2 * e)) (hy : y < m ^ (2 * e)) (hxy : x ≠ y) :
    ∃ r, r < 2 * e ∧ digit m r x ≠ digit m r y ∧ ∀ i < r, digit m i x = digit m i y := by
  have hex : ∃ i, i < 2 * e ∧ digit m i x ≠ digit m i y := by
    by_contra hcon
    refine hxy (eq_of_digits_eq m (2 * e) x y hm hx hy fun i hi => ?_)
    by_contra hne
    exact hcon ⟨i, hi, hne⟩
  obtain ⟨i₀, hi₀lt, hi₀ne⟩ := hex
  have hP : ∃ j, digit m j x ≠ digit m j y := ⟨i₀, hi₀ne⟩
  refine ⟨Nat.find hP, lt_of_le_of_lt (Nat.find_min' hP hi₀ne) hi₀lt, Nat.find_spec hP, ?_⟩
  intro i hi
  exact not_not.mp (Nat.find_min hP hi)

/-! ## The lift -/

/-- `C(m, S, e)` of §5: the residues below `m ^ (2 * e)` whose even base-`m` digits
`x_0, x_2, …, x_{2e−2}` all lie in `S`. The odd digits are unconstrained. -/
def liftBlock (m e : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (m ^ (2 * e))).filter (fun x => ∀ j < e, digit m (2 * j) x ∈ S)

/-- The lifted ranking of §5: `h(x) = Σ_{j<e} h₀(x_{2j}) · H₀^{e−1−j}`, the base-`H₀`
number whose digits are the ranks of the even digits, most significant first. -/
def liftRank (m e H₀ : ℕ) (h₀ : ℕ → ℕ) (x : ℕ) : ℕ :=
  ∑ j ∈ Finset.range e, h₀ (digit m (2 * j) x) * H₀ ^ (e - 1 - j)

/-- Membership in the lifted block, unfolded. -/
theorem mem_liftBlock (m e : ℕ) (S : Finset ℕ) (x : ℕ) :
    x ∈ liftBlock m e S ↔ x < m ^ (2 * e) ∧ ∀ j < e, digit m (2 * j) x ∈ S := by
  simp [liftBlock, Finset.mem_filter, Finset.mem_range]

/-- A base-`H` string of length `n`, digits first, is `< H ^ n`. -/
private theorem sum_coeff_lt_pow (H : ℕ) (c : ℕ → ℕ) :
    ∀ n, (∀ i < n, c i < H) → ∑ i ∈ Finset.range n, c i * H ^ i < H ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro h
    have hH : 0 < H := lt_of_le_of_lt (Nat.zero_le _) (h n (by omega))
    have hlt := ih fun i hi => h i (by omega)
    calc ∑ i ∈ Finset.range (n + 1), c i * H ^ i
        = (∑ i ∈ Finset.range n, c i * H ^ i) + c n * H ^ n := Finset.sum_range_succ _ _
      _ < H ^ n + c n * H ^ n := by omega
      _ = (c n + 1) * H ^ n := by ring
      _ ≤ H * H ^ n := Nat.mul_le_mul_right _ (h n (by omega))
      _ = H ^ (n + 1) := by ring

/-- The same bound with the weights reversed — most significant digit first, which is the
order `liftRank` uses. Public because Stage 3's `wordRank` is the same string at radix
`P`, and its two size bounds are this estimate again. -/
theorem sum_reflect_lt_pow (H : ℕ) (a : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, a i < H) :
    ∑ i ∈ Finset.range n, a i * H ^ (n - 1 - i) < H ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | -
  · simp
  have key : ∑ i ∈ Finset.range n, a i * H ^ (n - 1 - i)
      = ∑ i ∈ Finset.range n, a (n - 1 - i) * H ^ i := by
    rw [← Finset.sum_range_reflect (fun i => a (n - 1 - i) * H ^ i) n]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hji : n - 1 - (n - 1 - j) = j := by omega
    rw [hji]
  rw [key]
  exact sum_coeff_lt_pow H (fun i => a (n - 1 - i)) n fun i hi => h _ (by omega)

/-- The lifted rank is a base-`H₀` string of length `e`, hence `< H₀ ^ e`: the height
claim of Lemma A's conclusion. -/
theorem liftRank_lt_pow (m e H₀ : ℕ) (h₀ : ℕ → ℕ) (x : ℕ) (hH : 0 < H₀)
    (hb : ∀ i < e, h₀ (digit m (2 * i) x) < H₀) :
    liftRank m e H₀ h₀ x < H₀ ^ e :=
  sum_reflect_lt_pow H₀ (fun i => h₀ (digit m (2 * i) x)) e hb

/-- `liftRank` split at position `j`: the digits below `j`, the digit at `j`, the tail. -/
theorem liftRank_split (m e H₀ j : ℕ) (h₀ : ℕ → ℕ) (x : ℕ) (hj : j < e) :
    liftRank m e H₀ h₀ x =
      (∑ i ∈ Finset.range j, h₀ (digit m (2 * i) x) * H₀ ^ (e - 1 - i))
        + h₀ (digit m (2 * j) x) * H₀ ^ (e - 1 - j)
        + ∑ i ∈ Finset.Ico (j + 1) e, h₀ (digit m (2 * i) x) * H₀ ^ (e - 1 - i) := by
  rw [liftRank, ← Finset.sum_range_add_sum_Ico
    (fun i => h₀ (digit m (2 * i) x) * H₀ ^ (e - 1 - i)) (Nat.succ_le_of_lt hj),
    Finset.sum_range_succ]

/-- The geometric bound of Step 5: everything above position `j` is worth strictly less
than one unit at position `j`, since `(H₀ − 1) Σ_{j' > j} H₀^{e−1−j'} = H₀^{e−1−j} − 1`. -/
theorem liftRank_tail_lt (m e H₀ j : ℕ) (h₀ : ℕ → ℕ) (x : ℕ) (hH : 0 < H₀) (hj : j < e)
    (hb : ∀ i < e, h₀ (digit m (2 * i) x) < H₀) :
    ∑ i ∈ Finset.Ico (j + 1) e, h₀ (digit m (2 * i) x) * H₀ ^ (e - 1 - i) < H₀ ^ (e - 1 - j) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hN : e - 1 - j = e - (j + 1) := by omega
  have hcongr : ∑ k ∈ Finset.range (e - (j + 1)),
        h₀ (digit m (2 * (j + 1 + k)) x) * H₀ ^ (e - 1 - (j + 1 + k))
      = ∑ k ∈ Finset.range (e - (j + 1)),
        h₀ (digit m (2 * (j + 1 + k)) x) * H₀ ^ (e - (j + 1) - 1 - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    congr 2
    omega
  rw [hN, hcongr]
  exact sum_reflect_lt_pow H₀ (fun k => h₀ (digit m (2 * (j + 1 + k)) x)) (e - (j + 1))
    fun k hk => hb _ (by omega)

/-! ## Differences modulo `m ^ (2 * e)` -/

/-- The λ-decomposition, produced once from the `IsNonzeroSquareMod` hypothesis carried by
`RankedBlock`: a nonzero square residue `d < M` is `z ^ 2 − lam * M` for some `z ≠ 0`. -/
theorem exists_lambda_of_isNonzeroSquareMod (M d : ℕ) (hM : 0 < M) (hd : d < M)
    (hsq : IsNonzeroSquareMod M d) :
    d ≠ 0 ∧ ∃ z lam : ℕ, z ≠ 0 ∧ z < M ∧ z ^ 2 = d + lam * M := by
  obtain ⟨hne, z, hzM, hz⟩ := hsq
  rw [Nat.mod_eq_of_lt hd] at hne hz
  refine ⟨hne, z, z * z / M, ?_, hzM, ?_⟩
  · rintro rfl
    exact hne (by simpa using hz.symm)
  · calc z ^ 2 = z * z := pow_two z
      _ = M * (z * z / M) + z * z % M := (Nat.div_add_mod _ _).symm
      _ = M * (z * z / M) + d := by rw [hz]
      _ = d + z * z / M * M := by ring

/-! ## Step 0 — exact divisibility -/

/-- Reducing `x + d` modulo any `m ^ k` with `k ≤ 2 * e` recovers `y`: the wraparound term
`κ m ^ (2 * e)` is a multiple of `m ^ k`, so it is invisible below position `2 * e`. -/
private theorem diffMod_add_mod_pow (m e x y k : ℕ) (hm : 2 ≤ m)
    (hx : x < m ^ (2 * e)) (hy : y < m ^ (2 * e)) (hk : k ≤ 2 * e) :
    (x + diffMod (m ^ (2 * e)) x y) % m ^ k = y % m ^ k := by
  have hm0 : 0 < m := by omega
  have hMpos : 0 < m ^ (2 * e) := Nat.pow_pos hm0
  obtain ⟨c, hc⟩ : m ^ k ∣ m ^ (2 * e) := Nat.pow_dvd_pow m hk
  rcases diffMod_add (m ^ (2 * e)) x y hMpos hx hy with h | h
  · rw [h]
  · rw [h, hc, Nat.add_mul_mod_self_left]

/-- The divisibility half of Step 0, isolated: agreement of the digits below `r` already
forces `m ^ r ∣ d`. Step 1 needs this too, without Step 0's `hne`. -/
private theorem pow_dvd_diffMod (m e x y r : ℕ) (hm : 2 ≤ m)
    (hx : x < m ^ (2 * e)) (hy : y < m ^ (2 * e)) (hr : r ≤ 2 * e)
    (hlow : ∀ i < r, digit m i x = digit m i y) :
    m ^ r ∣ diffMod (m ^ (2 * e)) x y := by
  have hxy : x % m ^ r = y % m ^ r := (mod_pow_eq_iff_digits_eq m r x y hm).mpr hlow
  have h1 : x ≡ x + diffMod (m ^ (2 * e)) x y [MOD m ^ r] := by
    unfold Nat.ModEq
    rw [diffMod_add_mod_pow m e x y r hm hx hy hr, hxy]
  simpa using (Nat.modEq_iff_dvd' (Nat.le_add_right x _)).mp h1

/-- Step 0. With `r` the least differing digit position, `r = v_m(d)` for
`d = diffMod (m ^ (2 * e)) x y`: exactly `r` factors of `m` divide `d`. The wraparound
`κ m^{2e}` does not disturb this because `r < 2 * e`.

The divisibility half should go through `mod_pow_eq_iff_digits_eq` applied to `hlow`. -/
theorem step0_exact_dvd (m e x y r : ℕ) (hm : 2 ≤ m) (he : 1 ≤ e)
    (hx : x < m ^ (2 * e)) (hy : y < m ^ (2 * e)) (hr : r < 2 * e)
    (hne : digit m r x ≠ digit m r y) (hlow : ∀ i < r, digit m i x = digit m i y) :
    m ^ r ∣ diffMod (m ^ (2 * e)) x y ∧ ¬ m ^ (r + 1) ∣ diffMod (m ^ (2 * e)) x y := by
  refine ⟨pow_dvd_diffMod m e x y r hm hx hy (by omega) hlow, ?_⟩
  rintro ⟨c, hc⟩
  have h1 : (x + diffMod (m ^ (2 * e)) x y) % m ^ (r + 1) = y % m ^ (r + 1) :=
    diffMod_add_mod_pow m e x y (r + 1) hm hx hy (by omega)
  rw [hc, Nat.add_mul_mod_self_left] at h1
  exact hne ((mod_pow_eq_iff_digits_eq m (r + 1) x y hm).mp h1 r (by omega))

/-! ## Step 1 — the leading digit, without borrows -/

/-- Step 1. The `r`-th digit of the difference is the difference of the `r`-th digits:
positions above `r` contribute multiples of `m`, positions below `r` agree, and the
wraparound contributes `m^{2e−r} ≡ 0`.

The "positions below `r` agree" half should cite `mod_pow_eq_iff_digits_eq` as well. -/
theorem step1_leading_digit (m e x y r : ℕ) (hm : 2 ≤ m) (he : 1 ≤ e)
    (hx : x < m ^ (2 * e)) (hy : y < m ^ (2 * e)) (hr : r < 2 * e)
    (hlow : ∀ i < r, digit m i x = digit m i y) :
    digit m r (diffMod (m ^ (2 * e)) x y) = diffMod m (digit m r x) (digit m r y) := by
  have hm0 : 0 < m := by omega
  have hpr : 0 < m ^ r := Nat.pow_pos hm0
  have hMpos : 0 < m ^ (2 * e) := Nat.pow_pos hm0
  obtain ⟨D, hD⟩ := pow_dvd_diffMod m e x y r hm hx hy (by omega) hlow
  have hDdiv : diffMod (m ^ (2 * e)) x y / m ^ r = D := by
    rw [hD, Nat.mul_div_cancel_left _ hpr]
  -- the borrow-free relation at position `r`, before reducing mod `m`
  have hkey : (x / m ^ r + D) % m = (y / m ^ r) % m := by
    rcases diffMod_add (m ^ (2 * e)) x y hMpos hx hy with h | h
    · rw [hD] at h
      rw [← h, Nat.add_mul_div_left _ _ hpr]
    · rw [hD] at h
      have hsplit : m ^ (2 * e) = m ^ r * (m * m ^ (2 * e - r - 1)) := by
        rw [← pow_succ']
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit] at h
      have h2 : (x + m ^ r * D) / m ^ r = (y + m ^ r * (m * m ^ (2 * e - r - 1))) / m ^ r := by
        rw [h]
      rw [Nat.add_mul_div_left _ _ hpr, Nat.add_mul_div_left _ _ hpr] at h2
      rw [h2, Nat.add_mul_mod_self_left]
  -- `diffMod_unique` returns the witness reduced; the witness here is a digit, already `< m`,
  -- so `Nat.mod_eq_of_lt` puts it back.
  have huniq : diffMod m (digit m r x) (digit m r y)
      = digit m r (diffMod (m ^ (2 * e)) x y) % m := by
    refine diffMod_unique m (digit m r x) (digit m r y) (digit m r (diffMod (m ^ (2 * e)) x y))
      hm0 (digit_lt m r x hm0) (digit_lt m r y hm0) ?_
    unfold digit
    rw [hDdiv, ← Nat.add_mod, hkey]
  rw [huniq, Nat.mod_eq_of_lt (digit_lt m r _ hm0)]

/-! ## Step 2 — the valuation of a nonzero square residue is even -/

/-- For square-free `m`, a common power of `m` divides `d` exactly when the same power of
each prime factor of `m` does. There is no Mathlib lemma for this direction; the proof runs
on `Nat.factorization`, where square-freeness is `v_q(m) ≤ 1`. -/
private theorem sf_pow_dvd_iff {m : ℕ} (hsf : Squarefree m) (hm : m ≠ 0) {k d : ℕ}
    (hd : d ≠ 0) : m ^ k ∣ d ↔ ∀ q ∈ m.primeFactors, q ^ k ∣ d := by
  constructor
  · intro h q hq
    exact dvd_trans (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hq) k) h
  · intro h
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hm) hd, Nat.factorization_pow,
      Finsupp.le_def]
    intro q
    by_cases hq : q ∈ m.primeFactors
    · have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have h1 : m.factorization q ≤ 1 := (Nat.squarefree_iff_factorization_le_one hm).mp hsf q
      have h2 := (Nat.Prime.pow_dvd_iff_le_factorization hqp hd).mp (h q hq)
      simp only [Finsupp.smul_apply, smul_eq_mul]
      calc k * m.factorization q ≤ k * 1 := Nat.mul_le_mul_left _ h1
        _ = k := by ring
        _ ≤ d.factorization q := h2
    · have hz : m.factorization q = 0 := by
        simpa [Nat.support_factorization] using (Finsupp.notMem_support_iff).mp
          (by simpa [Nat.support_factorization] using hq)
      simp [hz]

/-- Exact divisibility survives the addition of a strictly more divisible term. This is the
ℕ-level stand-in for `emultiplicity_add_of_gt`, which is gated on `[Ring α]`. -/
private theorem exact_dvd_add {p k a b : ℕ} (ha : p ^ k ∣ a) (hna : ¬ p ^ (k + 1) ∣ a)
    (hb : p ^ (k + 1) ∣ b) : p ^ k ∣ a + b ∧ ¬ p ^ (k + 1) ∣ a + b :=
  ⟨dvd_add ha ((pow_dvd_pow p (Nat.le_succ k)).trans hb),
    fun h => hna ((Nat.dvd_add_right hb).mp (by rwa [Nat.add_comm a b] at h))⟩

/-- The same move run backwards: exact divisibility of `a + b` descends to `a` when `b` is
strictly more divisible. This is the direction Steps 2 and 3 need, since it is `z ^ 2` whose
valuation is known and `d` whose valuation is wanted. -/
private theorem exact_dvd_of_add {p k a b : ℕ} (hb : p ^ (k + 1) ∣ b)
    (h1 : p ^ k ∣ a + b) (h2 : ¬ p ^ (k + 1) ∣ a + b) :
    p ^ k ∣ a ∧ ¬ p ^ (k + 1) ∣ a := by
  have hbk : p ^ k ∣ b := (pow_dvd_pow p (Nat.le_succ k)).trans hb
  exact ⟨(Nat.dvd_add_right hbk).mp (by rwa [Nat.add_comm a b] at h1),
    fun h => h2 (dvd_add h hb)⟩

/-- Exact divisibility names the valuation. -/
private theorem padicValNat_eq_of_exact {q k n : ℕ} (hq : q.Prime) (hn : n ≠ 0)
    (h1 : q ^ k ∣ n) (h2 : ¬ q ^ (k + 1) ∣ n) : padicValNat q n = k := by
  have : Fact q.Prime := ⟨hq⟩
  have hle : k ≤ padicValNat q n := (padicValNat_dvd_iff_le hn).mp h1
  have hlt : ¬ (k + 1 ≤ padicValNat q n) := fun h => h2 ((padicValNat_dvd_iff_le hn).mpr h)
  omega

/-- Square-freeness as a valuation statement: `v_q(m) = 1` for every prime `q ∣ m`, so
`m ^ r ∣ d` iff `q ^ r ∣ d` for each of them. This is `v_m(d) = min_q v_q(d)` in the form
Step 2 uses it. -/
theorem pow_dvd_iff_forall_prime (m d r : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (hd : d ≠ 0) :
    m ^ r ∣ d ↔ ∀ q : ℕ, q.Prime → q ∣ m → r ≤ padicValNat q d := by
  have hm0 : m ≠ 0 := by omega
  rw [sf_pow_dvd_iff hsf hm0 hd]
  constructor
  · intro h q hq hqm
    have : Fact q.Prime := ⟨hq⟩
    exact (padicValNat_dvd_iff_le hd).mp (h q (Nat.mem_primeFactors.mpr ⟨hq, hqm, hm0⟩))
  · intro h q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hqp⟩
    exact (padicValNat_dvd_iff_le hd).mpr (h q hqp (Nat.dvd_of_mem_primeFactors hq))

/-- Exact divisibility exhibits a prime attaining the minimum: `r = v_m(d)` means some
`q ∣ m` has `v_q(d) = r` exactly. -/
theorem exists_padicValNat_eq (m d r : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (hd : d ≠ 0)
    (h1 : m ^ r ∣ d) (h2 : ¬ m ^ (r + 1) ∣ d) :
    ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ padicValNat q d = r := by
  have hlow := (pow_dvd_iff_forall_prime m d r hm hsf hd).mp h1
  by_contra hcon
  refine h2 ((pow_dvd_iff_forall_prime m d (r + 1) hm hsf hd).mpr fun q hq hqm => ?_)
  have hge := hlow q hq hqm
  rcases Nat.lt_or_ge (padicValNat q d) (r + 1) with hlt | hge'
  · exact absurd ⟨q, hq, hqm, by omega⟩ hcon
  · exact hge'

/-- The dominated-term move: a strictly smaller valuation wins in a sum. Step 2's uncapped
case is this applied to `z ^ 2 = d + lam * m ^ (2 * e)`. -/
theorem padicValNat_add_of_lt (q a b : ℕ) (hq : q.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : padicValNat q a < padicValNat q b) :
    padicValNat q (a + b) = padicValNat q a := by
  have : Fact q.Prime := ⟨hq⟩
  have h1 : q ^ padicValNat q a ∣ a := pow_padicValNat_dvd
  have h2 : ¬ q ^ (padicValNat q a + 1) ∣ a := pow_succ_padicValNat_not_dvd ha
  have h3 : q ^ (padicValNat q a + 1) ∣ b := (padicValNat_dvd_iff_le hb).mpr (by omega)
  obtain ⟨h4, h5⟩ := exact_dvd_add h1 h2 h3
  exact padicValNat_eq_of_exact hq (by omega) h4 h5

/-- Step 2, *uncapped* coordinate: when `2 v_q(z) < 2e`, the square term dominates and
`v_q(d) = 2 v_q(z)` — an even number. -/
theorem step2_uncapped (m e d z lam q : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m)
    (hq : q.Prime) (hqm : q ∣ m) (hd : d ≠ 0) (hz : z ≠ 0)
    (hlam : z ^ 2 = d + lam * m ^ (2 * e)) (hunc : padicValNat q z < e) :
    padicValNat q d = 2 * padicValNat q z := by
  have : Fact q.Prime := ⟨hq⟩
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hval : padicValNat q (z ^ 2) = 2 * padicValNat q z := padicValNat.pow z 2
  have h1 : q ^ (2 * padicValNat q z) ∣ z ^ 2 := by
    rw [← hval]; exact pow_padicValNat_dvd
  have h2 : ¬ q ^ (2 * padicValNat q z + 1) ∣ z ^ 2 := by
    rw [← hval]; exact pow_succ_padicValNat_not_dvd hz2
  have hB : q ^ (2 * padicValNat q z + 1) ∣ lam * m ^ (2 * e) :=
    (pow_dvd_pow q (by omega)).trans ((pow_dvd_pow_of_dvd hqm (2 * e)).mul_left lam)
  rw [hlam] at h1 h2
  obtain ⟨h4, h5⟩ := exact_dvd_of_add hB h1 h2
  exact padicValNat_eq_of_exact hq hd h4 h5

/-- Step 2, *capped* coordinate: when `2 v_q(z) ≥ 2e`, both terms are divisible by
`q ^ (2e)`, so `v_q(d) ≥ 2e` and the coordinate carries no parity information — and cannot
achieve the minimum, which is `< 2e`. -/
theorem step2_capped (m e d z lam q : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m)
    (hq : q.Prime) (hqm : q ∣ m) (hd : d ≠ 0) (hz : z ≠ 0)
    (hlam : z ^ 2 = d + lam * m ^ (2 * e)) (hcap : e ≤ padicValNat q z) :
    2 * e ≤ padicValNat q d := by
  have : Fact q.Prime := ⟨hq⟩
  have hval : padicValNat q (z ^ 2) = 2 * padicValNat q z := padicValNat.pow z 2
  have h1 : q ^ (2 * e) ∣ z ^ 2 := (padicValNat_dvd_iff_le (pow_ne_zero 2 hz)).mpr (by omega)
  have hB : q ^ (2 * e) ∣ lam * m ^ (2 * e) := (pow_dvd_pow_of_dvd hqm (2 * e)).mul_left lam
  rw [hlam] at h1
  exact (padicValNat_dvd_iff_le hd).mp ((Nat.dvd_add_right hB).mp (by rwa [Nat.add_comm] at h1))

/-- Step 2 (headline). `r = v_m(d)` is a minimum of even numbers, hence even. This is where
square-freeness is essential: for `m = 9`, `d = 9` has `v_m(d) = 1`. -/
theorem step2_even (m e d z lam r : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (he : 1 ≤ e)
    (hd : d ≠ 0) (hdlt : d < m ^ (2 * e)) (hz : z ≠ 0)
    (hlam : z ^ 2 = d + lam * m ^ (2 * e))
    (hr : r < 2 * e) (h1 : m ^ r ∣ d) (h2 : ¬ m ^ (r + 1) ∣ d) :
    Even r := by
  obtain ⟨q, hq, hqm, hqv⟩ := exists_padicValNat_eq m d r hm hsf hd h1 h2
  rcases Nat.lt_or_ge (padicValNat q z) e with hunc | hcap
  · have hu := step2_uncapped m e d z lam q hm hsf hq hqm hd hz hlam hunc
    exact ⟨padicValNat q z, by omega⟩
  · have hc := step2_capped m e d z lam q hm hsf hq hqm hd hz hlam hcap
    exfalso; omega

/-! ## Step 3 — global divisibility -/

/-- Step 3. With `r = 2 * j`, every coordinate satisfies `v_q(z) ≥ j`: uncapped ones
because `2 v_q(z) ≥ r`, capped ones because `2 v_q(z) ≥ 2e ≥ 2j + 2`. Square-freeness then
assembles the coordinates into `m ^ j ∣ z`. -/
theorem step3_pow_dvd (m e j d z lam : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (he : 1 ≤ e)
    (hd : d ≠ 0) (hdlt : d < m ^ (2 * e)) (hz : z ≠ 0)
    (hlam : z ^ 2 = d + lam * m ^ (2 * e)) (hj : j < e)
    (h1 : m ^ (2 * j) ∣ d) (h2 : ¬ m ^ (2 * j + 1) ∣ d) :
    m ^ j ∣ z := by
  refine (pow_dvd_iff_forall_prime m z j hm hsf hz).mpr fun q hq hqm => ?_
  rcases Nat.lt_or_ge (padicValNat q z) e with hunc | hcap
  · have hv := step2_uncapped m e d z lam q hm hsf hq hqm hd hz hlam hunc
    have hge := (pow_dvd_iff_forall_prime m d (2 * j) hm hsf hd).mp h1 q hq hqm
    omega
  · omega

/-! ## Step 4 — the leading digit is a nonzero square mod `m` -/

/-- Step 4. Writing `z = m ^ j * u`, we get `d / m^{2j} ≡ u ^ 2 (mod m^{2e−2j})` with
`2e − 2j ≥ 2`, so reducing mod `m` puts the leading digit `δ` in `Q_m` with witness
`u % m`. Note `u` need not be a unit: `δ` can be a *non-unit* square, which is exactly why
`IsNonzeroSquareMod` is the full image of squaring (Remark 3). -/
theorem step4_leading_square (m e j d z lam u : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m)
    (he : 1 ≤ e) (hd : d ≠ 0) (hdlt : d < m ^ (2 * e)) (hz : z ≠ 0)
    (hlam : z ^ 2 = d + lam * m ^ (2 * e)) (hj : j < e)
    (h1 : m ^ (2 * j) ∣ d) (h2 : ¬ m ^ (2 * j + 1) ∣ d) (hu : z = m ^ j * u) :
    IsNonzeroSquareMod m (digit m (2 * j) d) := by
  have hm0 : 0 < m := by omega
  have hp : 0 < m ^ (2 * j) := Nat.pow_pos hm0
  obtain ⟨d', hd'⟩ := h1
  have hdig : digit m (2 * j) d = d' % m := by
    rw [digit, hd', Nat.mul_div_cancel_left _ hp]
  have hzsq : z ^ 2 = m ^ (2 * j) * u ^ 2 := by
    rw [hu, mul_pow, ← pow_mul, Nat.mul_comm j 2]
  have hsplit : m ^ (2 * e) = m ^ (2 * j) * m ^ (2 * e - 2 * j) := by
    rw [← pow_add]; congr 1; omega
  have hkey : m ^ (2 * j) * u ^ 2 = m ^ (2 * j) * (d' + lam * m ^ (2 * e - 2 * j)) := by
    rw [← hzsq, hlam, hd', hsplit]; ring
  have hu2 : u ^ 2 = d' + lam * m ^ (2 * e - 2 * j) := Nat.eq_of_mul_eq_mul_left hp hkey
  obtain ⟨c, hc⟩ : m ∣ m ^ (2 * e - 2 * j) := dvd_pow_self m (by omega)
  have hrw : lam * (m * c) = m * (lam * c) := by ring
  have hmod : u ^ 2 % m = d' % m := by
    rw [hu2, hc, hrw, Nat.add_mul_mod_self_left]
  refine ⟨?_, u % m, Nat.mod_lt _ hm0, ?_⟩
  · rw [hdig, Nat.mod_mod_of_dvd _ dvd_rfl]
    intro hzero
    obtain ⟨c₂, hc₂⟩ : m ∣ d' := Nat.dvd_of_mod_eq_zero hzero
    exact h2 ⟨c₂, by rw [hd', hc₂, pow_succ]; ring⟩
  · rw [hdig, Nat.mod_mod_of_dvd _ dvd_rfl, ← Nat.mul_mod, ← pow_two, hmod]

/-! ## Step 5 — the rank drop -/

/-- Step 5. A drop of at least one unit at even position `2j`, equal digits below it, and
the geometric tail bound above it, give a strict drop in the lifted rank. -/
theorem step5_rank_drop (m e H₀ j : ℕ) (h₀ : ℕ → ℕ) (S : Finset ℕ) (x y : ℕ)
    (hH : 0 < H₀) (hj : j < e)
    (hxS : ∀ i < e, digit m (2 * i) x ∈ S) (hyS : ∀ i < e, digit m (2 * i) y ∈ S)
    (hbd : ∀ s ∈ S, h₀ s < H₀)
    (hlow : ∀ i < j, digit m (2 * i) x = digit m (2 * i) y)
    (hdrop : h₀ (digit m (2 * j) y) < h₀ (digit m (2 * j) x)) :
    liftRank m e H₀ h₀ y < liftRank m e H₀ h₀ x := by
  have hby : ∀ i < e, h₀ (digit m (2 * i) y) < H₀ := fun i hi => hbd _ (hyS i hi)
  have htail := liftRank_tail_lt m e H₀ j h₀ y hH hj hby
  have hmul : (h₀ (digit m (2 * j) y) + 1) * H₀ ^ (e - 1 - j)
      ≤ h₀ (digit m (2 * j) x) * H₀ ^ (e - 1 - j) := Nat.mul_le_mul_right _ hdrop
  have hexp : (h₀ (digit m (2 * j) y) + 1) * H₀ ^ (e - 1 - j)
      = h₀ (digit m (2 * j) y) * H₀ ^ (e - 1 - j) + H₀ ^ (e - 1 - j) := by ring
  have hlowsum : (∑ i ∈ Finset.range j, h₀ (digit m (2 * i) x) * H₀ ^ (e - 1 - i))
      = ∑ i ∈ Finset.range j, h₀ (digit m (2 * i) y) * H₀ ^ (e - 1 - i) :=
    Finset.sum_congr rfl fun i hi => by rw [hlow i (Finset.mem_range.mp hi)]
  rw [liftRank_split m e H₀ j h₀ x hj, liftRank_split m e H₀ j h₀ y hj, hlowsum]
  omega

/-! ## Lemma A -/

/-- **Lemma A (composite even-digit lift).** A ranked block on `Z/mZ` for square-free
`m ≥ 2` lifts to a ranked block on `Z/m^{2e}Z` of height `H₀ ^ e`.

This is §5's theorem verbatim, with `RankedBlock` on both sides. -/
theorem lemmaA (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m)
    (S : Finset ℕ) (h₀ : ℕ → ℕ) (H₀ : ℕ)
    (hS : RankedBlock m S h₀ H₀) (e : ℕ) (he : 1 ≤ e) :
    RankedBlock (m ^ (2 * e)) (liftBlock m e S) (liftRank m e H₀ h₀) (H₀ ^ e) := by
  obtain ⟨-, hSbd, hSarc⟩ := hS
  have hm0 : 0 < m := by omega
  have hMpos : 0 < m ^ (2 * e) := Nat.pow_pos hm0
  have hmem : ∀ x ∈ liftBlock m e S, x < m ^ (2 * e) ∧ ∀ i < e, digit m (2 * i) x ∈ S :=
    fun x hx => (mem_liftBlock m e S x).mp hx
  have hHpos : ∀ x ∈ liftBlock m e S, 0 < H₀ := fun x hx =>
    lt_of_le_of_lt (Nat.zero_le _) (hSbd _ ((hmem x hx).2 0 (by omega)))
  refine ⟨fun x hx => (hmem x hx).1, fun x hx => ?_, ?_⟩
  · exact liftRank_lt_pow m e H₀ h₀ x (hHpos x hx) fun i hi => hSbd _ ((hmem x hx).2 i hi)
  · intro x hx y hy hxy hsq
    obtain ⟨hxlt, hxS⟩ := hmem x hx
    obtain ⟨hylt, hyS⟩ := hmem y hy
    have hdlt : diffMod (m ^ (2 * e)) x y < m ^ (2 * e) := diffMod_lt _ x y hMpos
    have hd0 : diffMod (m ^ (2 * e)) x y ≠ 0 := diffMod_ne_zero _ x y hxlt hylt hxy
    obtain ⟨-, z, lam, hz0, -, hlam⟩ :=
      exists_lambda_of_isNonzeroSquareMod (m ^ (2 * e)) _ hMpos hdlt hsq
    obtain ⟨r, hrlt, hrne, hrlow⟩ := exists_least_digit_ne m e x y hm hxlt hylt hxy
    obtain ⟨hdvd1, hdvd2⟩ := step0_exact_dvd m e x y r hm he hxlt hylt hrlt hrne hrlow
    obtain ⟨j, hj⟩ :=
      step2_even m e _ z lam r hm hsf he hd0 hdlt hz0 hlam hrlt hdvd1 hdvd2
    have hr2 : r = 2 * j := by omega
    subst hr2
    have hjlt : j < e := by omega
    obtain ⟨u, hu⟩ :=
      step3_pow_dvd m e j _ z lam hm hsf he hd0 hdlt hz0 hlam hjlt hdvd1 hdvd2
    have hsq0 : IsNonzeroSquareMod m (digit m (2 * j) (diffMod (m ^ (2 * e)) x y)) :=
      step4_leading_square m e j _ z lam u hm hsf he hd0 hdlt hz0 hlam hjlt hdvd1 hdvd2 hu
    rw [step1_leading_digit m e x y (2 * j) hm he hxlt hylt hrlt hrlow] at hsq0
    exact step5_rank_drop m e H₀ j h₀ S x y (hHpos x hx) hjlt hxS hyS hSbd
      (fun i hi => hrlow (2 * i) (by omega))
      (hSarc _ (hxS j hjlt) _ (hyS j hjlt) hrne hsq0)

/-- Peeling two digit positions off the bottom: position `i + 2` of `x` is position `i` of
`x / m ^ 2`. This is the digit half of the `x ↦ (x % m², x / m²)` split that drives the
count, one lifted block level per `m ^ 2`. -/
private theorem digit_add_two (m i x : ℕ) : digit m (i + 2) x = digit m i (x / (m * m)) := by
  have h : x / m ^ (i + 2) = x / (m * m) / m ^ i := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  unfold digit
  rw [h]

/-- One level of the block, split at `m ^ 2`: the bottom two digits contribute the single
constraint `x mod m ∈ S`, and everything above is a block of one level less on `x / m ^ 2`.
This is the recursion `liftBlock_card` runs on. -/
private theorem mem_liftBlock_succ (m e : ℕ) (S : Finset ℕ) (hm : 0 < m) (x : ℕ) :
    x ∈ liftBlock m (e + 1) S ↔ x % m ∈ S ∧ x / (m * m) ∈ liftBlock m e S := by
  have hmm : 0 < m * m := Nat.mul_pos hm hm
  have hsize : x < m ^ (2 * (e + 1)) ↔ x / (m * m) < m ^ (2 * e) := by
    rw [Nat.div_lt_iff_lt_mul hmm, show m ^ (2 * e) * (m * m) = m ^ (2 * (e + 1)) by ring]
  rw [mem_liftBlock, mem_liftBlock, hsize]
  constructor
  · rintro ⟨hlt, hdig⟩
    refine ⟨by simpa [digit] using hdig 0 (by omega), hlt, fun j hj => ?_⟩
    have h := hdig (j + 1) (by omega)
    rwa [show 2 * (j + 1) = 2 * j + 2 by ring, digit_add_two] at h
  · rintro ⟨h0, hlt, hdig⟩
    refine ⟨hlt, fun j hj => ?_⟩
    cases j with
    | zero => simpa [digit] using h0
    | succ j =>
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, digit_add_two]
      exact hdig j (by omega)

/-- The bottom level, counted: of the `m ^ 2` residues below `m ^ 2`, exactly `|S| · m`
have their last digit in `S` — one free digit times the constrained one. -/
private theorem base_count (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : ∀ s ∈ S, s < m) :
    ((Finset.range (m * m)).filter (fun u => u % m ∈ S)).card = S.card * m := by
  have hcard : S.card * m = (S ×ˢ Finset.range m).card := by
    rw [Finset.card_product, Finset.card_range]
  rw [hcard]
  refine (Finset.card_nbij' (fun p => p.1 + m * p.2) (fun u => (u % m, u / m)) ?_ ?_ ?_ ?_).symm
  · rintro ⟨s, t⟩ hst
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hst
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range]
    have hs := hS s hst.1
    refine ⟨by nlinarith [hst.2], ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
    exact hst.1
  · intro u hu
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hu
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    exact ⟨hu.2, Nat.div_lt_of_lt_mul (by omega)⟩
  · rintro ⟨s, t⟩ hst
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hst
    have hs := hS s hst.1
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs, Nat.add_mul_div_left _ _ hm,
      Nat.div_eq_of_lt hs]
  · intro u hu
    exact Nat.mod_add_div u m

/-- The size count for `m ≥ 2`, where the digit-string bijection runs: a residue below
`m ^ (2 * (e + 1))` splits as a bottom pair of digits — one constrained to `S`, one free —
times a residue below `m ^ (2 * e)`. `liftBlock_card` below adds the two degenerate
moduli, where there is no such bijection to run. -/
private theorem liftBlock_card_of_two_le (m e : ℕ) (S : Finset ℕ) (hm : 2 ≤ m)
    (hS : ∀ s ∈ S, s < m) :
    (liftBlock m e S).card = (m * S.card) ^ e := by
  have hm0 : 0 < m := by omega
  have hmm : 0 < m * m := Nat.mul_pos hm0 hm0
  have hsplit : ∀ u v : ℕ, u < m * m →
      (u + m * m * v) % (m * m) = u ∧ (u + m * m * v) / (m * m) = v := by
    intro u v hu
    refine ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu], ?_⟩
    rw [Nat.add_mul_div_left _ _ hmm, Nat.div_eq_of_lt hu, Nat.zero_add]
  induction e with
  | zero =>
    have hset : liftBlock m 0 S = {0} := by
      ext x
      rw [mem_liftBlock]
      simp
    rw [hset]
    simp
  | succ e ih =>
    have hbij : (liftBlock m (e + 1) S).card
        = (((Finset.range (m * m)).filter (fun u => u % m ∈ S)) ×ˢ liftBlock m e S).card := by
      refine Finset.card_nbij' (fun x => (x % (m * m), x / (m * m)))
        (fun p => p.1 + m * m * p.2) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe] at hx ⊢
        rw [mem_liftBlock_succ m e S hm0] at hx
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
        refine ⟨⟨Nat.mod_lt _ hmm, ?_⟩, hx.2⟩
        rw [Nat.mod_mod_of_dvd _ (⟨m, rfl⟩ : m ∣ m * m)]
        exact hx.1
      · rintro ⟨u, v⟩ huv
        simp only [Finset.mem_coe] at huv ⊢
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at huv
        obtain ⟨⟨hult, huS⟩, hv⟩ := huv
        obtain ⟨hmod, hdiv⟩ := hsplit u v hult
        rw [mem_liftBlock_succ m e S hm0, hdiv]
        refine ⟨?_, hv⟩
        rw [← Nat.mod_mod_of_dvd _ (⟨m, rfl⟩ : m ∣ m * m), hmod]
        exact huS
      · intro x _
        exact Nat.mod_add_div x (m * m)
      · rintro ⟨u, v⟩ huv
        simp only [Finset.mem_coe] at huv
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at huv
        obtain ⟨hmod, hdiv⟩ := hsplit u v huv.1.1
        simp [hmod, hdiv]
    rw [hbij, Finset.card_product, base_count m hm0 S hS, ih]
    ring

/-- The size count `|C(m, S, e)| = (m t)^e`: `e` free odd digits and `e` digits from `S`.
Needed by Stage 4's exponent arithmetic. This is the brief's statement verbatim, with no
side condition on `m`: the digit-string bijection needs `2 ≤ m` and is run by
`liftBlock_card_of_two_le`, while `m ≤ 1` is settled by inspection, `hS` having collapsed
`S` to `∅` or `{0}`. -/
theorem liftBlock_card (m e : ℕ) (S : Finset ℕ) (hS : ∀ s ∈ S, s < m) :
    (liftBlock m e S).card = (m * S.card) ^ e := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · -- `e = 0`: the block is the single residue `0`, whatever `m` and `S` are.
      have h0 : liftBlock m 0 S = {0} := by
        ext x
        rw [mem_liftBlock, Finset.mem_singleton]
        exact ⟨fun h => by simpa using h.1,
          fun h => ⟨by simp [h], fun j hj => absurd hj (by omega)⟩⟩
      rw [h0]
      simp
    · interval_cases m
      · -- `m = 0`: `hS` empties `S`, and there are no residues below `0 ^ (2 * e) = 0`.
        have hSe : S = ∅ := Finset.eq_empty_of_forall_notMem fun s hs => by
          have := hS s hs; omega
        have hb : liftBlock 0 e S = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
          have h := ((mem_liftBlock 0 e S x).mp hx).1
          rw [zero_pow (by omega : 2 * e ≠ 0)] at h
          omega
        rw [hb, hSe]
        simp [zero_pow (by omega : e ≠ 0)]
      · -- `m = 1`: every digit is `0`, so `S` is `{0}` or `∅` and the block follows suit.
        by_cases h0 : (0 : ℕ) ∈ S
        · have hS1 : S = {0} :=
            Finset.eq_singleton_iff_unique_mem.mpr ⟨h0, fun x hx => by have := hS x hx; omega⟩
          subst hS1
          have hb : liftBlock 1 e ({0} : Finset ℕ) = {0} := by
            ext x
            rw [mem_liftBlock, Finset.mem_singleton]
            refine ⟨fun h => by simpa using h.1, fun h => ⟨by simp [h], fun j hj => ?_⟩⟩
            simp [digit, Nat.mod_one]
          rw [hb]
          simp
        · have hSe : S = ∅ := by
            refine Finset.eq_empty_of_forall_notMem fun s hs => h0 ?_
            have := hS s hs
            have hs0 : s = 0 := by omega
            exact hs0 ▸ hs
          subst hSe
          have hb : liftBlock 1 e (∅ : Finset ℕ) = ∅ := by
            refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
            have h := ((mem_liftBlock 1 e ∅ x).mp hx).2 0 he
            simp at h
          rw [hb]
          simp [zero_pow (by omega : e ≠ 0)]
  · exact liftBlock_card_of_two_le m e S hm hS

/-! ## The two composite blocks, lifted

The instantiations Stage 4 consumes. `235 = 5 · 47` and `299 = 13 · 23` are square-free,
which is the hypothesis of `lemmaA` these two blocks have to meet. -/

/-- `235 = 5 · 47` is square-free. -/
theorem squarefree_235 : Squarefree 235 := by
  have h : (235 : ℕ) = 5 * 47 := by norm_num
  rw [h, Nat.squarefree_mul (by decide)]
  exact ⟨Irreducible.squarefree (Nat.Prime.prime (by decide)).irreducible,
    Irreducible.squarefree (Nat.Prime.prime (by decide)).irreducible⟩

/-- `299 = 13 · 23` is square-free. -/
theorem squarefree_299 : Squarefree 299 := by
  have h : (299 : ℕ) = 13 * 23 := by norm_num
  rw [h, Nat.squarefree_mul (by decide)]
  exact ⟨Irreducible.squarefree (Nat.Prime.prime (by decide)).irreducible,
    Irreducible.squarefree (Nat.Prime.prime (by decide)).irreducible⟩

/-- The `235` block lifted: a ranked block on `Z/235^{2e}Z` of height `11 ^ e`. -/
theorem cert235_lift_rankedBlock (e : ℕ) (he : 1 ≤ e) :
    RankedBlock (235 ^ (2 * e)) (liftBlock 235 e (supportFinset cert235))
      (liftRank 235 e 11 (rankOf cert235)) (11 ^ e) :=
  lemmaA 235 (by norm_num) squarefree_235 (supportFinset cert235) (rankOf cert235) 11
    cert235_rankedBlock e he

/-- The `299` block lifted: a ranked block on `Z/299^{2e}Z` of height `12 ^ e`. -/
theorem cert299_lift_rankedBlock (e : ℕ) (he : 1 ≤ e) :
    RankedBlock (299 ^ (2 * e)) (liftBlock 299 e (supportFinset cert299))
      (liftRank 299 e 12 (rankOf cert299)) (12 ^ e) :=
  lemmaA 299 (by norm_num) squarefree_299 (supportFinset cert299) (rankOf cert299) 12
    cert299_rankedBlock e he

/-- The lifted `235` block has `(235 · 17) ^ e` elements. -/
theorem cert235_lift_card (e : ℕ) :
    (liftBlock 235 e (supportFinset cert235)).card = (235 * 17) ^ e := by
  rw [liftBlock_card 235 e (supportFinset cert235) cert235_supportFinset_lt,
    cert235_supportFinset_card]

/-- The lifted `299` block has `(299 · 19) ^ e` elements. -/
theorem cert299_lift_card (e : ℕ) :
    (liftBlock 299 e (supportFinset cert299)).card = (299 * 19) ^ e := by
  rw [liftBlock_card 299 e (supportFinset cert299) cert299_supportFinset_lt,
    cert299_supportFinset_card]
