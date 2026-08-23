import FsLowerBound.Pool
import FsLowerBound.PaleyChains
import FsLowerBound.Certificates

set_option linter.style.header false

/-!
# Bridging the pool to the certified data

`pool` in `FsLowerBound.Pool` is a list of bare numeric triples `(m, t, H)`. Nothing
in that definition forces those numbers to be the numbers this project actually certified:
a typo in the pool — a wrong support size, a height one too small — would leave every
other theorem in the repository true and the constant wrong. This file closes that seam.

For each of the eleven blocks there is a `decide`-proved membership fact whose triple is
built *from the certified objects themselves*, never from retyped literals:

* the two composite blocks use `cert235.length` / `cert299.length` and the very height
  literals that `cert235_valid` / `cert299_valid` certify (`11` and `12`);
* the nine Paley blocks use `chainP.length` in both the `t` and the `H` slot, with
  `chainP` the same definition `paleyP` certifies.

Two structural facts complete the picture: `pool_length` (there are eleven blocks, so the
eleven memberships account for all of them) and `pool_coprime` (the moduli are pairwise
coprime, the hypothesis the product construction needs). This is the one seam mutation
testing could not break, and it is now decidable data rather than commentary.
-/

/-- The pool has exactly eleven blocks. -/
theorem pool_length : pool.length = 11 := by decide

/-- The eleven moduli are pairwise coprime — the hypothesis under which the blocks
combine by CRT. -/
theorem pool_coprime : pool.Pairwise (fun a b => Nat.Coprime a.1 b.1) := by decide

/-! ### The two composite blocks

The height literals below are exactly the ones appearing in `cert235_valid` and
`cert299_valid`, and the support sizes are the lengths of the certified lists. -/

/-- The `235` block of `pool` is the certificate of `FsLowerBound.Certificates`: its
support size is `cert235.length` and its height is the `11` of `cert235_valid`. -/
theorem pool_mem_cert235 : (235, cert235.length, 11) ∈ pool := by decide

/-- The `299` block of `pool` is the certificate of `FsLowerBound.Certificates`: its
support size is `cert299.length` and its height is the `12` of `cert299_valid`. -/
theorem pool_mem_cert299 : (299, cert299.length, 12) ∈ pool := by decide

/-! ### The nine Paley blocks

A Paley block contributes `(p, t, t)`: for a chain the height equals the chain length, so
the same `chainP.length` fills both slots. -/

theorem pool_mem_paley3 : (3, chain3.length, chain3.length) ∈ pool := by decide

theorem pool_mem_paley7 : (7, chain7.length, chain7.length) ∈ pool := by decide

theorem pool_mem_paley11 : (11, chain11.length, chain11.length) ∈ pool := by decide

theorem pool_mem_paley19 : (19, chain19.length, chain19.length) ∈ pool := by decide

theorem pool_mem_paley31 : (31, chain31.length, chain31.length) ∈ pool := by decide

theorem pool_mem_paley43 : (43, chain43.length, chain43.length) ∈ pool := by decide

theorem pool_mem_paley59 : (59, chain59.length, chain59.length) ∈ pool := by decide

theorem pool_mem_paley71 : (71, chain71.length, chain71.length) ∈ pool := by decide

theorem pool_mem_paley103 : (103, chain103.length, chain103.length) ∈ pool := by decide
