import FsLowerBound.Defs
import Mathlib.Tactic.NormNum.Prime

set_option linter.style.header false

/-!
# The ten Paley chains

Each theorem below certifies that the exhibited tuple is a Paley chain for its prime:
`p` is prime, `p ≡ 3 (mod 4)`, the entries are distinct residues, and every forward
difference is a nonzero square mod `p`.

The tuples are given as named definitions `chain3 … chain103` rather than as inline
literals, so that the pool bridge in `FsLowerBound.Bridges` can tie each pool triple to
the *same* list this file certifies, rather than to a retyped copy of it.

Nine of these — all but `p = 23` — form the Paley part of the eleven-block pool. The
chain at `23` is stated for comparison only: `23 ∣ 299`, so it is excluded from the pool
of this construction, and it appears here because Krachun's constant `α★` uses it.

The primality component is discharged by `norm_num`; the three finite components by
`decide`, so the kernel checks them.
-/

set_option maxRecDepth 4000

/-- Paley chain at `p = 3`. -/
def chain3 : List ℕ := [0, 1]

/-- Paley chain at `p = 7`. -/
def chain7 : List ℕ := [0, 4, 1]

/-- Paley chain at `p = 11`. -/
def chain11 : List ℕ := [0, 3, 1, 4]

/-- Paley chain at `p = 19`. -/
def chain19 : List ℕ := [0, 5, 11, 9, 16]

/-- Krachun's chain at `p = 23`; not a pool block, since `23 ∣ 299`. -/
def chain23 : List ℕ := [0, 18, 1, 3, 4]

/-- Paley chain at `p = 31`. -/
def chain31 : List ℕ := [0, 25, 14, 1, 19, 8, 2]

/-- Paley chain at `p = 43`. -/
def chain43 : List ℕ := [0, 31, 9, 23, 4, 40, 1]

/-- Paley chain at `p = 59`. -/
def chain59 : List ℕ := [0, 49, 15, 7, 16, 19, 35, 36, 5]

/-- Paley chain at `p = 71`. -/
def chain71 : List ℕ := [0, 8, 12, 18, 48, 27, 1, 37, 20]

/-- Paley chain at `p = 103`. -/
def chain103 : List ℕ := [0, 79, 25, 58, 55, 81, 4, 1, 34, 83, 59]

theorem paley3 : IsPaleyChain 3 chain3 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

theorem paley7 : IsPaleyChain 7 chain7 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

theorem paley11 : IsPaleyChain 11 chain11 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

theorem paley19 : IsPaleyChain 19 chain19 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

/-- Krachun's chain at `23`. Not part of this construction's pool, since `23 ∣ 299`. -/
theorem paley23 : IsPaleyChain 23 chain23 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

theorem paley31 : IsPaleyChain 31 chain31 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

theorem paley43 : IsPaleyChain 43 chain43 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

theorem paley59 : IsPaleyChain 59 chain59 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

theorem paley71 : IsPaleyChain 71 chain71 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

theorem paley103 : IsPaleyChain 103 chain103 :=
  ⟨by norm_num, by decide, by decide, by decide⟩
