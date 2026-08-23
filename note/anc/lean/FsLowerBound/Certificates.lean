import FsLowerBound.Defs

set_option linter.style.header false

/-!
# The two composite certificates

Two square-DAGs on square-free composite moduli, each with an exhibited ranking whose
height is strictly below the support size: `(m, t, H₀) = (235, 17, 11)` with
`235 = 5 · 47`, and `(299, 19, 12)` with `299 = 13 · 23`. These are the blocks that carry
the construction past Krachun's constant.

`ValidRankedSupport m sup H` says: the vertices are distinct residues mod `m`, the ranks
lie in `{0, …, H-1}`, and along every arc — every ordered pair whose difference is a
nonzero square mod `m` — the rank strictly drops. Checking it is one pass over the ordered
pairs of the support, which is what `decide` performs in the kernel.

The blocks are lower-bound certificates only. No minimality of the heights, and no
maximality of the supports, is claimed or proved.

"Height 11" and "height 12" are theorems here, not prose. `cert235_valid` bounds every
rank strictly below 11, and `cert235_ranks_complete` shows every rank in `{0, …, 10}`
occurs, so the rank set is exactly `{0, …, 10}`; likewise `cert299_valid` with
`cert299_ranks_complete` for `{0, …, 11}`. None of this says the ranking is optimal —
only that this ranking has that many levels and no more.
-/

set_option maxRecDepth 100000

/-- Certificate on `m = 235`, as `(vertex, rank)` pairs; the ranking is the exhibited one
from the source note. Its height is pinned by `cert235_valid` (ranks `< 11`) together with
`cert235_height_attained` (rank `10` occurs). -/
def cert235 : List (ℕ × ℕ) :=
  [(0, 10), (112, 10), (196, 9), (224, 9), (155, 8), (136, 7), (67, 6), (110, 6),
   (92, 5), (189, 5), (126, 4), (193, 4), (22, 3), (50, 3), (64, 2), (73, 1), (148, 0)]

/-- Certificate on `m = 299`, as `(vertex, rank)` pairs. The ranks are the computed
reversed longest-path layers of the support's induced digraph. How they were obtained does
not enter the proof; `cert299_valid` is the whole claim, and its height is pinned by that
theorem (ranks `< 12`) together with `cert299_height_attained` (rank `11` occurs). -/
def cert299 : List (ℕ × ℕ) :=
  [(7, 6), (21, 10), (25, 2), (40, 3), (46, 4), (78, 6), (83, 4), (116, 7), (153, 5),
   (161, 2), (165, 1), (206, 9), (207, 8), (210, 1), (212, 11), (244, 10), (264, 5),
   (289, 3), (292, 0)]

theorem cert235_valid : ValidRankedSupport 235 cert235 11 := by decide

theorem cert299_valid : ValidRankedSupport 299 cert299 12 := by decide

/-- The height claimed for `cert235` is attained: the largest rank appearing is `10`. -/
theorem cert235_height_attained : (cert235.map Prod.snd).max? = some 10 := by decide

/-- The height claimed for `cert299` is attained: the largest rank appearing is `11`. -/
theorem cert299_height_attained : (cert299.map Prod.snd).max? = some 11 := by decide

/-- Every rank in `{0, …, 10}` occurs in `cert235`. With `cert235_valid` (every rank
`< 11`) the rank set is exactly `{0, …, 10}`, so "height 11" is a theorem rather than a
description. -/
theorem cert235_ranks_complete : ∀ r < 11, r ∈ cert235.map Prod.snd := by decide

/-- Every rank in `{0, …, 11}` occurs in `cert299`. With `cert299_valid` (every rank
`< 12`) the rank set is exactly `{0, …, 11}`. -/
theorem cert299_ranks_complete : ∀ r < 12, r ∈ cert299.map Prod.snd := by decide
