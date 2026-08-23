import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false

/-!
# Definitions for the Furstenberg–Sárközy lower bound

This file fixes the vocabulary of the construction: the arc set `Q_m` (as a predicate),
differences modulo `m` taken without truncated subtraction, ranked supports on `Z/mZ`,
Paley chains, and the counting function `D`.

All arithmetic here is in `ℕ`, so that every finite claim about a concrete modulus is
decidable and can be discharged by `decide`. Vertices are always residues `a < m`.

Reference: `README.md` of the companion repository `fs-lower-bound`.
-/

/-- `d` (already reduced mod `m`) is a nonzero square modulo `m`: `d ≠ 0` and some `z < m`
has `z² ≡ d (mod m)`. This is membership in `Q_m = (image of squaring) \ {0}`.

The image of squaring is taken in full: elements of `Q_m` may be non-units. That is part
of the definition, not an implementation choice — the unit-only variant makes the lift
lemma false (see Remark 1 of the source note). -/
def IsNonzeroSquareMod (m d : ℕ) : Prop :=
  d % m ≠ 0 ∧ ∃ z < m, z * z % m = d % m

/-- A kernel-friendly decision procedure: search `z` over `List.range m`. -/
instance instDecidableIsNonzeroSquareMod (m d : ℕ) : Decidable (IsNonzeroSquareMod m d) :=
  decidable_of_iff
    (d % m ≠ 0 ∧ ((List.range m).any fun z => z * z % m == d % m) = true) <| by
      simp [IsNonzeroSquareMod, List.any_eq_true, List.mem_range]

/-- Remark 1 of the source note, as a negative control: **no unit** squares to `6` mod
`15`, and yet `6` is a nonzero square mod `15` (the `example` just below, via the non-unit
`z = 6`). That is why `Q_m` has to be the full image of squaring with `0` removed — the
unit-only arc set would wrongly omit `6`, delete the arcs it carries, and so make the
composite lift lemma false. -/
theorem six_not_unit_square_mod_15 :
    ¬ ∃ z, z < 15 ∧ Nat.gcd z 15 = 1 ∧ z * z % 15 = 6 := by decide

-- The other half of Remark 1: `6` *is* a nonzero square mod `15`.
example : IsNonzeroSquareMod 15 6 := by decide

/-- The residue of `b − a` mod `m`, for `a b < m`, in `ℕ` without truncation surprises. -/
def diffMod (m a b : ℕ) : ℕ := (b + m - a) % m

/-- `diffMod` lands in `[0, M)`. -/
theorem diffMod_lt (M a b : ℕ) (hM : 0 < M) : diffMod M a b < M :=
  Nat.mod_lt _ hM

/-- Distinct residues have a nonzero difference. -/
theorem diffMod_ne_zero (M x y : ℕ) (hx : x < M) (hy : y < M) (hxy : x ≠ y) :
    diffMod M x y ≠ 0 := by
  unfold diffMod
  by_cases h : x ≤ y
  · have h1 : y + M - x = y - x + M := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The κ ∈ {0, 1} wraparound in ℕ: `x + d` is either `y` or `y + M`. Steps 0 and 1 of
Lemma A both consume this; stating it once keeps ℤ out of every statement downstream. -/
theorem diffMod_add (M x y : ℕ) (hM : 0 < M) (hx : x < M) (hy : y < M) :
    x + diffMod M x y = y ∨ x + diffMod M x y = y + M := by
  unfold diffMod
  by_cases h : x ≤ y
  · left
    have h1 : y + M - x = y - x + M := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · right
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- `diffMod m a b` is *the* shift from `a` to `b`, for any witness `c` — not only for a
witness already reduced: `a + c ≡ b (mod m)` forces `diffMod m a b = c % m`. Lemma A's
Step 1 identifies the `r`-th digit of the difference by exhibiting it as such a `c`, Lemma
B uses the unreduced form, where the witness in hand is a square `k ^ 2`, and Lemma C's
`diffMod_mod_of_dvd` calls it at a divisor of the modulus. -/
theorem diffMod_unique (m a b c : ℕ) (hm : 0 < m) (ha : a < m) (hb : b < m)
    (h : (a + c) % m = b) : diffMod m a b = c % m := by
  have hc : c % m < m := Nat.mod_lt _ hm
  have h' : (a + c % m) % m = b := by rw [← h]; simp [Nat.add_mod]
  clear h
  unfold diffMod
  by_cases hlt : a + c % m < m
  · rw [Nat.mod_eq_of_lt hlt] at h'
    subst h'
    have hrw : a + c % m + m - a = c % m + m := by omega
    rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt hc]
  · have h2 : (a + c % m) % m = a + c % m - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h2] at h'
    subst h'
    have hrw : a + c % m - m + m - a = c % m := by omega
    rw [hrw, Nat.mod_eq_of_lt hc]

/-- A support with an exhibited ranking of height `H` on `Z/mZ`: entries `(vertex, rank)`,
vertices distinct and `< m`, ranks `< H`, and along every arc (difference in `Q_m`) the
rank strictly drops. This is exactly "square-DAG with valid ranking"; acyclicity follows
from the existence of the ranking and is not stated separately. -/
def ValidRankedSupport (m : ℕ) (sup : List (ℕ × ℕ)) (H : ℕ) : Prop :=
  sup.Pairwise (fun p q => p.1 ≠ q.1) ∧
  (∀ p ∈ sup, p.1 < m ∧ p.2 < H) ∧
  ∀ p ∈ sup, ∀ q ∈ sup, p.1 ≠ q.1 →
    IsNonzeroSquareMod m (diffMod m p.1 q.1) → q.2 < p.2

instance instDecidableValidRankedSupport (m : ℕ) (sup : List (ℕ × ℕ)) (H : ℕ) :
    Decidable (ValidRankedSupport m sup H) := by
  unfold ValidRankedSupport; infer_instance

/-- Krachun's Paley chain: a prime `p ≡ 3 (mod 4)`, entries `< p` and pairwise distinct,
with every forward difference a nonzero square mod `p`. The list order carries the `a < b`
of the chain condition. -/
def IsPaleyChain (p : ℕ) (s : List ℕ) : Prop :=
  Nat.Prime p ∧ p % 4 = 3 ∧ (∀ x ∈ s, x < p) ∧
  s.Pairwise (fun a b => a ≠ b ∧ IsNonzeroSquareMod p (diffMod p a b))

/-- No two elements differ by a positive perfect square (additive form; no `ℕ`-subtraction). -/
def SquareDifferenceFree (A : Set ℕ) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ k : ℕ, 0 < k → a + k * k ∉ A

/-- `Finset` form, used to define `D`. -/
def sdfFinset (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a < b → ¬ ∃ k, 0 < k ∧ b = a + k * k

theorem sdfFinset_iff (A : Finset ℕ) : sdfFinset A ↔ SquareDifferenceFree (A : Set ℕ) := by
  constructor
  · intro h a ha k hk hmem
    exact h a ha (a + k * k) hmem (Nat.lt_add_of_pos_right (Nat.mul_pos hk hk)) ⟨k, hk, rfl⟩
  · rintro h a ha b hb - ⟨k, hk, rfl⟩
    exact h ha k hk hb

/-- `D N` is the largest size of a square-difference-free subset of `{1, …, N}`.

`D` is never computed, so the `Finset.filter` is given a classical decidability
instance. -/
noncomputable def D (N : ℕ) : ℕ :=
  letI := Classical.decPred sdfFinset
  ((Finset.Icc 1 N).powerset.filter sdfFinset).sup Finset.card
