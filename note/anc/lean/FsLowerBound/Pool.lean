import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false

/-!
# The eleven-block pool and the constant it evaluates to

`pool` and `alphaInf` used to sit at the top of `FsLowerBound.Statements`, above the three
pinned targets. Stage 4 needs them *below* the construction — `FsLowerBound.Construction`
matches its eleven certified blocks against `pool`'s numerals, and
`FsLowerBound.Numeric` bounds `alphaInf` from below — while `FsLowerBound.Statements` needs
to import all of that machinery in order to discharge the targets. Keeping the two
definitions in `Statements.lean` would make the import graph circular, so they live here.

Both definitions are reproduced byte for byte from the Stage-3 `Statements.lean`, together
with their docstrings; nothing about them changed in the move. `FsLowerBound.Bridges`,
which ties `pool`'s numerals to the certified objects, now imports this file instead of
`FsLowerBound.Statements`.

This file states no theorem. It is definitions only, and every downstream statement about
them is proved elsewhere.
-/

/-- The eleven-block pool, as triples `(m, t, H)`: the nine Paley pairs `(p, t, t)`
certified in `FsLowerBound.PaleyChains`, then the two composite certificates of
`FsLowerBound.Certificates` with their exhibited heights. Krachun's chain at `23` is
absent because `23 ∣ 299`.

The entries are bare numerals here. `FsLowerBound.Bridges` ties each of the eleven back to
the certified object it stands for (`pool_mem_paley3 … pool_mem_paley103`,
`pool_mem_cert235`, `pool_mem_cert299`) and proves `pool_length` and `pool_coprime` — that
last is the pairwise coprimality of the moduli. -/
def pool : List (ℕ × ℕ × ℕ) :=
  [(3, 2, 2), (7, 3, 3), (11, 4, 4), (19, 5, 5), (31, 7, 7), (43, 7, 7),
   (59, 9, 9), (71, 9, 9), (103, 11, 11), (235, 17, 11), (299, 19, 12)]

/-- The closed form `α∞ = (Σ log(mᵢtᵢ)/log Hᵢ) / (1 + 2 Σ log mᵢ/log Hᵢ)`, evaluated on
`pool`. Numerically `0.753741541837329405…`. -/
noncomputable def alphaInf : ℝ :=
  (pool.map fun x => Real.log (x.1 * x.2.1) / Real.log x.2.2).sum /
  (1 + 2 * (pool.map fun x => Real.log x.1 / Real.log x.2.2).sum)
