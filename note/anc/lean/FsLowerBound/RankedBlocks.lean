import FsLowerBound.Defs
import FsLowerBound.Certificates
import Mathlib.Data.Finset.Dedup

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false

/-!
# Ranked blocks — the single predicate the whole chain speaks

`ValidRankedSupport` (in `FsLowerBound.Defs`) is the *list* form of a ranked block: it is
what the two composite certificates satisfy, and it is decidable, which is why `decide`
can check them in the kernel. It is a poor interface for the lift of Stage 2, which has to
quantify over a set of residues mod `m ^ (2 * e)` far too large to enumerate.

`RankedBlock P C h H` below is the *functional* form of the same idea: a `Finset` of
vertices, a ranking given as a plain function `ℕ → ℕ`, and the same two conditions —
ranks below `H`, and a strict rank drop along every arc, where an arc is a pair whose
difference is a nonzero square mod `P` (`IsNonzeroSquareMod`, the full image of squaring
with `0` removed; Remark 3 of the source note is why the unit-only variant is wrong).

With `P = m` this *is* "square-DAG on `Z/mZ` with a ranking of height `H`". Acyclicity is
not stated separately: it follows from the existence of the ranking. Lemma A
(`FsLowerBound.LemmaA`) maps `RankedBlock` to `RankedBlock`, and Stages 3–4 consume the
same predicate, so this is the one interface that crosses every stage boundary.

## Correspondence to the source note

This file is the *bridge*, not the mathematics: `krachun-proofs.md` §5's "square-DAG and
ranking" definition becomes `RankedBlock`, and `RankedBlock.of_validRankedSupport` is the
translation that lets `cert235_valid` / `cert299_valid` feed the lift.

## Choices made here beyond the design brief

* **Support as a `Finset`, rank as a total function.** The brief pinned
  `RankedBlock (P : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)`; it left open how a
  `List (ℕ × ℕ)` certificate turns into that pair. Chosen: `supportFinset` is
  `(sup.map Prod.fst).toFinset`, and `rankOf` is `List.lookup` with `0` as the junk value
  off the support. A total function with junk values (rather than a `Subtype`-indexed one)
  keeps `liftRank` a plain `ℕ → ℕ`, which is what the brief's `liftRank` signature needs;
  the junk value is never observed, because every use is guarded by membership in `C`.
* **`rankOf` picks the first occurrence.** `List.lookup` returns the first match. On a
  support whose vertices are pairwise distinct — which `ValidRankedSupport` asserts — there
  is only one match, so this is not a real choice; it is recorded because the statement of
  `rankOf_eq_of_mem` carries the distinctness hypothesis explicitly rather than silently.
* **Extra card / bound lemmas.** `supportFinset_card`, `cert235_supportFinset_card`,
  `cert299_supportFinset_card` and the two `_lt` lemmas are not in the brief. They are the
  facts Stage 4 needs to know that `t = 17` and `t = 19` are the `|S|` appearing in
  `liftBlock_card`, and that `S ⊆ [0, m)`, which is `liftBlock_card`'s hypothesis.

Every declaration below is proved: this file carries no placeholders. The ADR-033 trust rules
apply throughout — no kernel-external decision procedures, no postulated constants, no
compiler escape hatches. `RankedBlock.of_validRankedSupport`, `cert235_rankedBlock` and
`cert299_rankedBlock` are named in `auditedDeclarations` in `Test/AxiomAudit.lean`.
-/

/-- A ranked block on `Z/PZ`: vertices `C` are residues `< P`, ranks are `< H`, and along
every arc — every ordered pair whose difference is a nonzero square mod `P` — the rank
strictly drops.

With `P = m` this is "square-DAG with a valid ranking of height `H`"; with
`P = m ^ (2 * e)` it is the conclusion of Lemma A. One predicate, both ends of the lift. -/
def RankedBlock (P : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ) : Prop :=
  (∀ x ∈ C, x < P) ∧ (∀ x ∈ C, h x < H) ∧
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → IsNonzeroSquareMod P (diffMod P x y) → h y < h x

/-- The vertex set of a certificate list, as a `Finset`. -/
def supportFinset (sup : List (ℕ × ℕ)) : Finset ℕ := (sup.map Prod.fst).toFinset

/-- The ranking of a certificate list, as a total function: the rank recorded for `x` if
`x` is on the support, and the junk value `0` otherwise. Off-support values are never
observed — every use is guarded by membership in the support. -/
def rankOf (sup : List (ℕ × ℕ)) (x : ℕ) : ℕ := (sup.lookup x).getD 0

/-- Membership in `supportFinset` is "some rank is recorded for `x`". -/
theorem mem_supportFinset (sup : List (ℕ × ℕ)) (x : ℕ) :
    x ∈ supportFinset sup ↔ ∃ r : ℕ, (x, r) ∈ sup := by
  simp only [supportFinset, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨a, r⟩, hp, rfl⟩
    exact ⟨r, hp⟩
  · rintro ⟨r, hr⟩
    exact ⟨(x, r), hr, rfl⟩

/-- On a support with pairwise distinct vertices, `rankOf` reads back the recorded rank. -/
theorem rankOf_eq_of_mem (sup : List (ℕ × ℕ)) (x r : ℕ)
    (hd : sup.Pairwise (fun p q => p.1 ≠ q.1)) (hx : (x, r) ∈ sup) :
    rankOf sup x = r := by
  unfold rankOf
  induction sup with
  | nil => simp at hx
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.mp hx with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq x r a b ▸ h
      simp [List.lookup]
    · have hne : ¬ (x = a) := fun hxa => hd.1 (x, r) h (by simp [hxa])
      have hbeq : (x == a) = false := beq_eq_false_iff_ne.mpr hne
      simp only [List.lookup, hbeq]
      exact ih hd.2 h

/-- Pairwise distinct vertices means no collapse: the support size is the list length. -/
theorem supportFinset_card (sup : List (ℕ × ℕ))
    (hd : sup.Pairwise (fun p q => p.1 ≠ q.1)) :
    (supportFinset sup).card = sup.length := by
  have hnd : (sup.map Prod.fst).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hd
  rw [supportFinset, List.toFinset_card_of_nodup hnd, List.length_map]

/-- The bridge from Stage 1: the decidable list form implies the functional form, so the
`decide`-checked certificates can be fed to Lemma A. -/
theorem RankedBlock.of_validRankedSupport (m H : ℕ) (sup : List (ℕ × ℕ))
    (hv : ValidRankedSupport m sup H) :
    RankedBlock m (supportFinset sup) (rankOf sup) H := by
  obtain ⟨hd, hbd, harc⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := (mem_supportFinset sup x).mp hx
    exact (hbd (x, r) hr).1
  · intro x hx
    obtain ⟨r, hr⟩ := (mem_supportFinset sup x).mp hx
    rw [rankOf_eq_of_mem sup x r hd hr]
    exact (hbd (x, r) hr).2
  · intro x hx y hy hxy hsq
    obtain ⟨rx, hrx⟩ := (mem_supportFinset sup x).mp hx
    obtain ⟨ry, hry⟩ := (mem_supportFinset sup y).mp hy
    rw [rankOf_eq_of_mem sup x rx hd hrx, rankOf_eq_of_mem sup y ry hd hry]
    exact harc (x, rx) hrx (y, ry) hry hxy hsq

/-- The `235` certificate as a ranked block on `Z/235Z`, height `11`. -/
theorem cert235_rankedBlock :
    RankedBlock 235 (supportFinset cert235) (rankOf cert235) 11 :=
  RankedBlock.of_validRankedSupport 235 11 cert235 cert235_valid

/-- The `299` certificate as a ranked block on `Z/299Z`, height `12`. -/
theorem cert299_rankedBlock :
    RankedBlock 299 (supportFinset cert299) (rankOf cert299) 12 :=
  RankedBlock.of_validRankedSupport 299 12 cert299 cert299_valid

/-- The `235` block has `t = 17` vertices — the `|S|` of the size count in Stage 4. -/
theorem cert235_supportFinset_card : (supportFinset cert235).card = 17 := by
  rw [supportFinset_card cert235 cert235_valid.1]
  rfl

/-- The `299` block has `t = 19` vertices. -/
theorem cert299_supportFinset_card : (supportFinset cert299).card = 19 := by
  rw [supportFinset_card cert299 cert299_valid.1]
  rfl

/-- The `235` support lies in `[0, 235)` — the hypothesis of `liftBlock_card`. -/
theorem cert235_supportFinset_lt : ∀ s ∈ supportFinset cert235, s < 235 := by
  intro s hs
  obtain ⟨r, hr⟩ := (mem_supportFinset cert235 s).mp hs
  exact (cert235_valid.2.1 (s, r) hr).1

/-- The `299` support lies in `[0, 299)`. -/
theorem cert299_supportFinset_lt : ∀ s ∈ supportFinset cert299, s < 299 := by
  intro s hs
  obtain ⟨r, hr⟩ := (mem_supportFinset cert299 s).mp hs
  exact (cert299_valid.2.1 (s, r) hr).1
