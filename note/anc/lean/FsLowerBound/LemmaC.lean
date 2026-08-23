import FsLowerBound.RankedBlocks
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Intervals

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false
-- §1.5's standing hypotheses are carried whether or not the finished proofs consume them,
-- exactly as in `FsLowerBound.LemmaA`. With the proofs in, `crtRank_lt` is the one that
-- still trips the linter: its `P Q Cp Cq` are §1.5's bookkeeping, naming which two blocks
-- the two heights belong to, and its arithmetic never touches them.
set_option linter.unusedVariables false

/-!
# Lemma C — gluing ranked blocks by the Chinese remainder theorem

This file formalizes §1.5 of `krachun-proofs.md` (Krachun's Lemma 5): ranked blocks on
coprime moduli glue to a ranked block on the product, with the supports multiplying and
the heights adding, `H = 1 + Σ (H_i − 1)`.

The headline is `lemmaC` — the binary case — together with `crtBlock_card`. `glueList`
and `glueList_rankedBlock` fold the binary case along a list, which is what Stage 4 needs
for the eleven-block pool.

| Lean | §1.5 |
| --- | --- |
| `crtBlock` | `C = Π C_i` under the Chinese remainder identification |
| `crtRank_lt` | `h = Σ h_i` lands in `{0, …, H − 1}` for `H = H_p + H_q − 1` |
| `exists_sq_mod_of_dvd` | "its reduction in every coordinate is a square modulo `P_i`" (H5.4) |
| `coord_ne_zero` | "since `x ≠ y`, at least one coordinate is nonzero" |
| `diffMod_mod_of_dvd` | the coordinate bookkeeping: a difference reduces to a difference |
| `coord_rank_le` | "a zero coordinate leaves the corresponding rank unchanged" |
| `coord_rank_lt` | "a nonzero coordinate strictly decreases it" |
| `lemmaC` | "summing the local inequalities proves `h(x) > h(y)`" |
| `crt_injOn`, `crt_image`, `crtBlock_card` | `|C| = Π |C_i|` |

## No perfect-square hypothesis

§2.3's H5.2 records that the `P_i` being perfect squares is **not used in Lemma 5's own
proof**. It is carried by the caller, so that the product handed to Lemma B is again a
perfect square. That bookkeeping belongs to Stage 4, and no statement in this file mentions
it. Likewise nothing here knows about Paley chains, digits, or lifts: the interface is
`RankedBlock` on both sides, as it is everywhere else in the chain.

## Choices made here beyond the design brief

The brief pinned `crtBlock`, `lemmaC` and `crtBlock_card` verbatim; those are reproduced
exactly. The rest is decided here.

* **The list glue is a plain tuple fold, not a structure.** `glueList` folds `glueTwo`
  with `List.foldr` from the trivial block `trivialBlock = (1, {0}, fun _ ↦ 0, 1)`. Two
  reasons for `foldr` over `foldl`: the recursion `glueList (b :: l) = glueTwo b
  (glueList l)` is definitional, which makes `glueList_cons` free and every induction a
  plain `List.rec`; and the coprimality side condition at each step is then
  "`b`'s modulus is coprime to the product of the rest", which is exactly what
  `List.Pairwise Nat.Coprime` on the moduli hands over through
  `Nat.coprime_list_prod_right_iff` (`k.Coprime l.prod ↔ ∀ n ∈ l, k.Coprime n`). That is
  the **List** form, and it is the one this file needs: the moduli travel as
  `l.map Prod.fst`, a `List ℕ`, and `glueList_fst` states the glued modulus as
  `(l.map Prod.fst).prod`. Mathlib's `Nat.Coprime.prod_right` is the Finset form
  (`(∀ i ∈ t, x.Coprime (s i)) → x.Coprime (∏ i ∈ t, s i)`) and does not apply here.
  A structure would read better at Stage 4's call site but would need its own bridge to
  and from `RankedBlock`; the tuple needs none.
* **The trivial block is `(1, {0}, fun _ ↦ 0, 1)`,** the ranked block on `Z/1Z`. It is a
  genuine `RankedBlock` (`trivialBlock_rankedBlock`), so the fold has no empty-list case to
  special-case, and its height `1` is the `1` of `H = 1 + Σ (H_i − 1)`: gluing it on adds
  `1 − 1 = 0`.
* **Coprimality is `(l.map Prod.fst).Pairwise Nat.Coprime`,** on the moduli only. The
  fold additionally needs each modulus coprime to the product of the later ones, which
  `glueList_fst` turns back into the pairwise statement.
* **`crtBlock_card` is stated with no positivity hypothesis on `P` or `Q`,** as pinned.
  The degenerate cases survive: `Nat.Coprime 0 Q` forces `Q = 1`, so `hCp` empties `Cp` and
  both sides are `0`; symmetrically for `Q = 0`. No `1 ≤ P` is added.
* **`lemmaC` needs no positivity hypothesis either.** Membership in `crtBlock P Q Cp Cq`
  already gives `x < P * Q`, which forces both moduli positive whenever there is anything
  to check.
* **`diffMod_mod_of_dvd` is stated once at a general divisor `K ∣ M`,** rather than twice
  for `P` and for `Q`. Both coordinates of `lemmaC` are the same statement.
* **The square-reduction lemma is stated as a bare witness,** `∃ w < K, w * w % K = d % K`,
  rather than as `IsNonzeroSquareMod K (d % K)`. §1.5's zero branch is exactly the case
  where the reduction is a square but *not* a nonzero one (H5.4), so the nonzero clause
  cannot be part of the conclusion; `coord_rank_lt` reattaches it from `a ≠ b`.
* **`glueList_card`, `glueList_height`, `glueList_fst` and `glueList_mem_lt` are
  additions.** Stage 4 needs the modulus, the support size and the height of the folded
  block in closed form, not merely the fact that it is a ranked block.
* **The glued ranking is deliberately left in fold form.** `glueList`'s ranking is
  whatever the nested `glueTwo` applications build — `fun x => a.2.2.1 (x % a.1) + …` one
  layer per block — and no closed-form rank lemma is stated to match `glueList_fst`,
  `glueList_height` and `glueList_card`. None is needed: Stage 4 reads only the modulus,
  the height and the support size off the folded block, never the value of the ranking at
  a point. `glueList_rankedBlock` is what certifies the ranking, and it says all Stage 4
  asks of it.

## Trust rules (ADR-033)

The ADR-033 trust rules apply: no kernel-external decision procedures, no postulated
constants, no compiler escape hatches. Every declaration below is proved: this file carries
no placeholders. `auditedDeclarations` in `Test/AxiomAudit.lean` names eight declarations
from this file. Four of them would do: `collectAxioms` is transitive, and `lemmaC`,
`crtBlock_card`, `glueList_rankedBlock` and `glueList_card` between them reach everything
else here — `glueList_rankedBlock` pulls in `trivialBlock_rankedBlock`, `glueList_cons`,
`glueList_fst` and `glueList_height`, and `glueList_card` pulls in `glueList_mem_lt`
(`glueList_rankedBlock` does not: it never needs the support size). The other four —
`trivialBlock_rankedBlock`, `glueList_fst`, `glueList_height`, `glueList_mem_lt` — are
listed for readability, so that the fold's whole interface can be read off the audit list,
and not because the closure would miss them.
-/

/-! ## The glued support -/

/-- `C_p × C_q` under the Chinese remainder identification, as a set of residues below
`P * Q`: the `x < P * Q` whose reduction mod `P` lies in `Cp` and whose reduction mod `Q`
lies in `Cq`. -/
def crtBlock (P Q : ℕ) (Cp Cq : Finset ℕ) : Finset ℕ :=
  (Finset.range (P * Q)).filter (fun x => x % P ∈ Cp ∧ x % Q ∈ Cq)

/-- Membership in the glued support, unfolded. -/
theorem mem_crtBlock (P Q : ℕ) (Cp Cq : Finset ℕ) (x : ℕ) :
    x ∈ crtBlock P Q Cp Cq ↔ x < P * Q ∧ x % P ∈ Cp ∧ x % Q ∈ Cq := by
  simp only [crtBlock, Finset.mem_filter, Finset.mem_range]

/-! ## Coordinate bookkeeping -/

/-- H5.4: a square modulo `M` reduces to a square modulo any divisor `K` of `M` — possibly
to the square `0`, which is why the conclusion is a bare witness and not
`IsNonzeroSquareMod`. -/
theorem exists_sq_mod_of_dvd (M K d : ℕ) (hK : 0 < K) (hdvd : K ∣ M)
    (hsq : IsNonzeroSquareMod M d) :
    ∃ w < K, w * w % K = d % K := by
  obtain ⟨-, z, -, hzz⟩ := hsq
  refine ⟨z % K, Nat.mod_lt _ hK, ?_⟩
  rw [← Nat.mul_mod, ← Nat.mod_mod_of_dvd (z * z) hdvd, hzz, Nat.mod_mod_of_dvd _ hdvd]

/-- "Since `x ≠ y`, at least one coordinate is nonzero": for coprime `P` and `Q`, a
difference that vanishes in both coordinates vanishes mod `P * Q`. -/
theorem coord_ne_zero (P Q d : ℕ) (hco : Nat.Coprime P Q) (hd : d % (P * Q) ≠ 0) :
    d % P ≠ 0 ∨ d % Q ≠ 0 := by
  by_contra hc
  have h1 : d % P = 0 := by
    by_contra h; exact hc (Or.inl h)
  have h2 : d % Q = 0 := by
    by_contra h; exact hc (Or.inr h)
  obtain ⟨c, hcc⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hco
    (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
  exact hd (by rw [hcc, Nat.mul_mod_right])

/-- The difference of the reductions is the reduction of the difference. Stated once at a
general divisor `K ∣ M`; `lemmaC` uses it at `K := P` and at `K := Q`. -/
theorem diffMod_mod_of_dvd (M K x y : ℕ) (hK : 0 < K) (hdvd : K ∣ M)
    (hx : x < M) (hy : y < M) :
    diffMod M x y % K = diffMod K (x % K) (y % K) := by
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le x) hx
  obtain ⟨c, hcM⟩ := hdvd
  have hmod : (x + diffMod M x y) % K = y % K := by
    rcases diffMod_add M x y hM hx hy with h | h
    · rw [h]
    · rw [h, hcM, Nat.add_mul_mod_self_left]
  refine (diffMod_unique K (x % K) (y % K) (diffMod M x y) hK
    (Nat.mod_lt _ hK) (Nat.mod_lt _ hK) ?_).symm
  rw [Nat.mod_add_mod]
  exact hmod

/-- "A nonzero coordinate strictly decreases the rank": in a ranked block, a square
difference between two *distinct* support elements is a nonzero square, so the block's
arc condition applies. -/
theorem coord_rank_lt (K : ℕ) (Ck : Finset ℕ) (hk : ℕ → ℕ) (Hk : ℕ)
    (hB : RankedBlock K Ck hk Hk) (a b : ℕ) (ha : a ∈ Ck) (hb : b ∈ Ck) (hab : a ≠ b)
    (hw : ∃ w < K, w * w % K = diffMod K a b % K) :
    hk b < hk a := by
  obtain ⟨hlt, -, harc⟩ := hB
  have haK : a < K := hlt a ha
  have hbK : b < K := hlt b hb
  have hK : 0 < K := by omega
  refine harc a ha b hb hab ⟨?_, hw⟩
  rw [Nat.mod_eq_of_lt (diffMod_lt K a b hK)]
  exact diffMod_ne_zero K a b haK hbK hab

/-- "A zero coordinate leaves the corresponding rank unchanged": the same statement with
the distinctness dropped, which is the form the sum of §1.5 needs in every coordinate. -/
theorem coord_rank_le (K : ℕ) (Ck : Finset ℕ) (hk : ℕ → ℕ) (Hk : ℕ)
    (hB : RankedBlock K Ck hk Hk) (a b : ℕ) (ha : a ∈ Ck) (hb : b ∈ Ck)
    (hw : ∃ w < K, w * w % K = diffMod K a b % K) :
    hk b ≤ hk a := by
  rcases eq_or_ne a b with rfl | hab
  · exact le_rfl
  · exact le_of_lt (coord_rank_lt K Ck hk Hk hB a b ha hb hab hw)

/-- The height clause: `h_p + h_q ≤ (H_p − 1) + (H_q − 1) < H_p + H_q − 1`. The two
positivity hypotheses are what keep the truncated subtraction honest. -/
theorem crtRank_lt (P Q : ℕ) (Cp Cq : Finset ℕ) (hp hq : ℕ → ℕ) (Hp Hq : ℕ)
    (hHp : 1 ≤ Hp) (hHq : 1 ≤ Hq) (a b : ℕ) (hpa : hp a < Hp) (hqb : hq b < Hq) :
    hp a + hq b < Hp + Hq - 1 := by
  omega

/-! ## Lemma C -/

/-- A residue differs from itself by `0`. The converse of `diffMod_ne_zero`, and the form
`lemmaC` needs: a coordinate whose difference is nonzero has distinct residues there. -/
private theorem diffMod_self' (M a : ℕ) (ha : a < M) : diffMod M a a = 0 := by
  unfold diffMod
  have h : a + M - a = M := by omega
  rw [h, Nat.mod_self]

/-- **Lemma C (Krachun's Lemma 5), binary form.** Two ranked blocks on coprime moduli glue
to a ranked block on the product: supports multiply, ranks add, heights add with one
subtracted.

No perfect-square hypothesis appears — §2.3's H5.2 — and none is needed. -/
theorem lemmaC (P Q : ℕ) (hco : Nat.Coprime P Q)
    (Cp : Finset ℕ) (hp : ℕ → ℕ) (Hp : ℕ) (hP : RankedBlock P Cp hp Hp)
    (Cq : Finset ℕ) (hq : ℕ → ℕ) (Hq : ℕ) (hQ : RankedBlock Q Cq hq Hq)
    (hHp : 1 ≤ Hp) (hHq : 1 ≤ Hq) :
    RankedBlock (P * Q) (crtBlock P Q Cp Cq)
      (fun x => hp (x % P) + hq (x % Q)) (Hp + Hq - 1) := by
  refine ⟨fun x hx => ((mem_crtBlock P Q Cp Cq x).mp hx).1, fun x hx => ?_, ?_⟩
  · obtain ⟨-, hxp, hxq⟩ := (mem_crtBlock P Q Cp Cq x).mp hx
    exact crtRank_lt P Q Cp Cq hp hq Hp Hq hHp hHq (x % P) (x % Q)
      (hP.2.1 _ hxp) (hQ.2.1 _ hxq)
  · intro x hx y hy hxy hsq
    obtain ⟨hxlt, hxp, hxq⟩ := (mem_crtBlock P Q Cp Cq x).mp hx
    obtain ⟨hylt, hyp, hyq⟩ := (mem_crtBlock P Q Cp Cq y).mp hy
    have hPQ : 0 < P * Q := Nat.lt_of_le_of_lt (Nat.zero_le x) hxlt
    have hPpos : 0 < P := Nat.pos_of_ne_zero (by rintro rfl; simp at hPQ)
    have hQpos : 0 < Q := Nat.pos_of_ne_zero (by rintro rfl; simp at hPQ)
    -- The difference, and its two coordinates.
    have hdlt : diffMod (P * Q) x y < P * Q := diffMod_lt _ _ _ hPQ
    have hdmod : diffMod (P * Q) x y % (P * Q) ≠ 0 := by
      rw [Nat.mod_eq_of_lt hdlt]
      exact diffMod_ne_zero _ _ _ hxlt hylt hxy
    have hdP : diffMod (P * Q) x y % P = diffMod P (x % P) (y % P) :=
      diffMod_mod_of_dvd (P * Q) P x y hPpos ⟨Q, rfl⟩ hxlt hylt
    have hdQ : diffMod (P * Q) x y % Q = diffMod Q (x % Q) (y % Q) :=
      diffMod_mod_of_dvd (P * Q) Q x y hQpos ⟨P, Nat.mul_comm P Q⟩ hxlt hylt
    -- H5.4 in each coordinate.
    have hwP : ∃ w < P, w * w % P = diffMod P (x % P) (y % P) % P := by
      obtain ⟨w, hw, hww⟩ :=
        exists_sq_mod_of_dvd (P * Q) P (diffMod (P * Q) x y) hPpos ⟨Q, rfl⟩ hsq
      exact ⟨w, hw, by rw [hww, hdP, Nat.mod_eq_of_lt (diffMod_lt P _ _ hPpos)]⟩
    have hwQ : ∃ w < Q, w * w % Q = diffMod Q (x % Q) (y % Q) % Q := by
      obtain ⟨w, hw, hww⟩ :=
        exists_sq_mod_of_dvd (P * Q) Q (diffMod (P * Q) x y) hQpos
          ⟨P, Nat.mul_comm P Q⟩ hsq
      exact ⟨w, hw, by rw [hww, hdQ, Nat.mod_eq_of_lt (diffMod_lt Q _ _ hQpos)]⟩
    -- Every coordinate is weakly decreasing; the nonzero one is strictly decreasing.
    have hleP : hp (y % P) ≤ hp (x % P) := coord_rank_le P Cp hp Hp hP _ _ hxp hyp hwP
    have hleQ : hq (y % Q) ≤ hq (x % Q) := coord_rank_le Q Cq hq Hq hQ _ _ hxq hyq hwQ
    change hp (y % P) + hq (y % Q) < hp (x % P) + hq (x % Q)
    rcases coord_ne_zero P Q (diffMod (P * Q) x y) hco hdmod with h | h
    · have hne : x % P ≠ y % P := by
        intro he
        exact h (by rw [hdP, he, diffMod_self' P (y % P) (Nat.mod_lt _ hPpos)])
      have := coord_rank_lt P Cp hp Hp hP _ _ hxp hyp hne hwP
      omega
    · have hne : x % Q ≠ y % Q := by
        intro he
        exact h (by rw [hdQ, he, diffMod_self' Q (y % Q) (Nat.mod_lt _ hQpos)])
      have := coord_rank_lt Q Cq hq Hq hQ _ _ hxq hyq hne hwQ
      omega

/-! ## Counting the glued support -/

/-- CRT uniqueness: on `[0, P * Q)` a residue is determined by its two coordinates. -/
theorem crt_injOn (P Q : ℕ) (hco : Nat.Coprime P Q) :
    Set.InjOn (fun x => (x % P, x % Q)) (Finset.range (P * Q) : Set ℕ) := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_range] at hx hy
  simp only [Prod.mk.injEq] at hxy
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨hxy.1, hxy.2⟩
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h

/-- CRT existence, in the form the count needs: the coordinate map sends the glued support
onto the full product of the two supports. -/
theorem crt_image (P Q : ℕ) (hco : Nat.Coprime P Q) (Cp Cq : Finset ℕ)
    (hCp : ∀ c ∈ Cp, c < P) (hCq : ∀ c ∈ Cq, c < Q) :
    (crtBlock P Q Cp Cq).image (fun x => (x % P, x % Q)) = Cp ×ˢ Cq := by
  ext ab
  obtain ⟨a, b⟩ := ab
  simp only [Finset.mem_image, Finset.mem_product, Prod.mk.injEq, mem_crtBlock]
  constructor
  · rintro ⟨x, ⟨-, hxp, hxq⟩, rfl, rfl⟩
    exact ⟨hxp, hxq⟩
  · rintro ⟨ha, hb⟩
    have hPpos : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le a) (hCp a ha)
    have hQpos : 0 < Q := Nat.lt_of_le_of_lt (Nat.zero_le b) (hCq b hb)
    have h1 : (Nat.chineseRemainder hco a b : ℕ) % P = a := by
      have h := (Nat.chineseRemainder hco a b).2.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt (hCp a ha)] at h
      exact h
    have h2 : (Nat.chineseRemainder hco a b : ℕ) % Q = b := by
      have h := (Nat.chineseRemainder hco a b).2.2
      rw [Nat.ModEq, Nat.mod_eq_of_lt (hCq b hb)] at h
      exact h
    refine ⟨(Nat.chineseRemainder hco a b : ℕ), ⟨?_, ?_, ?_⟩, h1, h2⟩
    · exact Nat.chineseRemainder_lt_mul hco a b hPpos.ne' hQpos.ne'
    · rw [h1]; exact ha
    · rw [h2]; exact hb

/-- `|C| = |C_p| · |C_q|`. No positivity hypothesis: coprimality forces the other modulus
to be `1` when one of them is `0`, and `hCp` / `hCq` then empty the corresponding
support. -/
theorem crtBlock_card (P Q : ℕ) (hco : Nat.Coprime P Q)
    (Cp Cq : Finset ℕ) (hCp : ∀ c ∈ Cp, c < P) (hCq : ∀ c ∈ Cq, c < Q) :
    (crtBlock P Q Cp Cq).card = Cp.card * Cq.card := by
  have hsub : (crtBlock P Q Cp Cq : Set ℕ) ⊆ (Finset.range (P * Q) : Set ℕ) := by
    intro x hx
    simp only [Finset.mem_coe, mem_crtBlock] at hx
    simp only [Finset.mem_coe, Finset.mem_range]
    exact hx.1
  have h := Finset.card_image_of_injOn ((crt_injOn P Q hco).mono hsub)
  rw [crt_image P Q hco Cp Cq hCp hCq] at h
  rw [← h, Finset.card_product]

/-! ## The list glue

A block travels as the tuple `(modulus, support, ranking, height)`. Stage 4 glues eleven of
them; `glueList` is `lemmaC` folded along the list, so that Stage 4 states its pool once
rather than chaining ten binary applications by hand. -/

/-- The ranked block on `Z/1Z`: one vertex, rank `0`, height `1`. The identity of the
fold — gluing it on multiplies the modulus by `1` and adds `1 − 1 = 0` to the height. -/
def trivialBlock : ℕ × Finset ℕ × (ℕ → ℕ) × ℕ := (1, {0}, fun _ => 0, 1)

/-- One step of the fold: `lemmaC`'s conclusion, read off the two tuples. -/
def glueTwo (a b : ℕ × Finset ℕ × (ℕ → ℕ) × ℕ) : ℕ × Finset ℕ × (ℕ → ℕ) × ℕ :=
  (a.1 * b.1, crtBlock a.1 b.1 a.2.1 b.2.1,
    (fun x => a.2.2.1 (x % a.1) + b.2.2.1 (x % b.1)), a.2.2.2 + b.2.2.2 - 1)

/-- The eleven-block glue of §1.5, as a fold. `foldr` so that
`glueList (b :: l) = glueTwo b (glueList l)` holds definitionally. -/
def glueList (l : List (ℕ × Finset ℕ × (ℕ → ℕ) × ℕ)) : ℕ × Finset ℕ × (ℕ → ℕ) × ℕ :=
  l.foldr glueTwo trivialBlock

/-- The trivial block really is one. -/
theorem trivialBlock_rankedBlock :
    RankedBlock trivialBlock.1 trivialBlock.2.1 trivialBlock.2.2.1 trivialBlock.2.2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [trivialBlock, Finset.mem_singleton] at hx
    simp [trivialBlock, hx]
  · intro x hx
    simp [trivialBlock]
  · intro x hx y hy hxy _
    simp only [trivialBlock, Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy

/-- The fold's recursion, made explicit for the inductions below. -/
theorem glueList_cons (b : ℕ × Finset ℕ × (ℕ → ℕ) × ℕ)
    (l : List (ℕ × Finset ℕ × (ℕ → ℕ) × ℕ)) :
    glueList (b :: l) = glueTwo b (glueList l) := rfl

/-- The glued modulus is the product of the moduli. This is also what turns
`List.Pairwise Nat.Coprime` into the side condition each fold step needs, through
`Nat.coprime_list_prod_right_iff` — the List form; the Finset `Nat.Coprime.prod_right` is
not the lemma here. -/
theorem glueList_fst (l : List (ℕ × Finset ℕ × (ℕ → ℕ) × ℕ)) :
    (glueList l).1 = (l.map Prod.fst).prod := by
  induction l with
  | nil => simp [glueList, trivialBlock]
  | cons b t ih => rw [glueList_cons]; simp [glueTwo, ih]

/-- The glued support consists of residues, which is `crtBlock_card`'s hypothesis at the
next step up the fold. -/
theorem glueList_mem_lt (l : List (ℕ × Finset ℕ × (ℕ → ℕ) × ℕ)) :
    ∀ c ∈ (glueList l).2.1, c < (glueList l).1 := by
  induction l with
  | nil =>
    intro c hc
    simp only [glueList, trivialBlock, List.foldr_nil, Finset.mem_singleton] at hc
    simp [glueList, trivialBlock, hc]
  | cons b t ih =>
    intro c hc
    rw [glueList_cons] at hc ⊢
    simp only [glueTwo] at hc ⊢
    exact ((mem_crtBlock _ _ _ _ c).mp hc).1

/-- The glued height in closed form: `H = 1 + Σ (H_i − 1)`, exactly §1.5's. -/
theorem glueList_height (l : List (ℕ × Finset ℕ × (ℕ → ℕ) × ℕ))
    (hH : ∀ b ∈ l, 1 ≤ b.2.2.2) :
    (glueList l).2.2.2 = 1 + (l.map (fun b => b.2.2.2 - 1)).sum := by
  induction l with
  | nil => simp [glueList, trivialBlock]
  | cons b t ih =>
    have hb : 1 ≤ b.2.2.2 := hH b List.mem_cons_self
    have ih' := ih fun c hc => hH c (List.mem_cons_of_mem b hc)
    rw [glueList_cons]
    simp only [glueTwo, List.map_cons, List.sum_cons]
    omega

/-- The glued support size in closed form: `|C| = Π |C_i|`. -/
theorem glueList_card (l : List (ℕ × Finset ℕ × (ℕ → ℕ) × ℕ))
    (hco : (l.map Prod.fst).Pairwise Nat.Coprime)
    (hlt : ∀ b ∈ l, ∀ c ∈ b.2.1, c < b.1) :
    (glueList l).2.1.card = (l.map (fun b => b.2.1.card)).prod := by
  induction l with
  | nil => simp [glueList, trivialBlock]
  | cons b t ih =>
    rw [List.map_cons, List.pairwise_cons] at hco
    have hcop : Nat.Coprime b.1 (glueList t).1 := by
      rw [glueList_fst]
      exact Nat.coprime_list_prod_right_iff.mpr hco.1
    have ih' := ih hco.2 fun c hc => hlt c (List.mem_cons_of_mem b hc)
    rw [glueList_cons]
    simp only [glueTwo, List.map_cons, List.prod_cons]
    rw [crtBlock_card b.1 (glueList t).1 hcop b.2.1 (glueList t).2.1
      (hlt b List.mem_cons_self) (glueList_mem_lt t), ih']

/-- **Lemma C, list form.** A list of ranked blocks on pairwise coprime moduli, each of
positive height, folds to a ranked block on the product modulus.

Stage 4 may use this or chain `lemmaC` ten times by hand; the two routes are
interchangeable, and this one exists so that the pool is stated once. -/
theorem glueList_rankedBlock (l : List (ℕ × Finset ℕ × (ℕ → ℕ) × ℕ))
    (hco : (l.map Prod.fst).Pairwise Nat.Coprime)
    (hB : ∀ b ∈ l, RankedBlock b.1 b.2.1 b.2.2.1 b.2.2.2)
    (hH : ∀ b ∈ l, 1 ≤ b.2.2.2) :
    RankedBlock (glueList l).1 (glueList l).2.1 (glueList l).2.2.1 (glueList l).2.2.2 := by
  induction l with
  | nil => exact trivialBlock_rankedBlock
  | cons b t ih =>
    rw [List.map_cons, List.pairwise_cons] at hco
    have hcop : Nat.Coprime b.1 (glueList t).1 := by
      rw [glueList_fst]
      exact Nat.coprime_list_prod_right_iff.mpr hco.1
    have hHt : ∀ c ∈ t, 1 ≤ c.2.2.2 := fun c hc => hH c (List.mem_cons_of_mem b hc)
    have hBt := ih hco.2 (fun c hc => hB c (List.mem_cons_of_mem b hc)) hHt
    have hHtail : 1 ≤ (glueList t).2.2.2 := by
      rw [glueList_height t hHt]
      omega
    rw [glueList_cons]
    simp only [glueTwo]
    exact lemmaC b.1 (glueList t).1 hcop b.2.1 b.2.2.1 b.2.2.2 (hB b List.mem_cons_self)
      (glueList t).2.1 (glueList t).2.2.1 (glueList t).2.2.2 hBt
      (hH b List.mem_cons_self) hHtail
