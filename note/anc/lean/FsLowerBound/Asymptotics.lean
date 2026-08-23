import FsLowerBound.Construction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false

/-!
# Layer A — the limit formula and the passage to all `N`

This file is §6.2 and §6.3 of `krachun-proofs.md`. §6.2 allocates multiplicities
`eᵢ(U) = ⌊U / log Hᵢ⌋` and shows that the exponent of the resulting stage tends to
`alphaInf` as `U → ∞`. §6.3 turns any single stage whose exponent exceeds `ρ` into a bound
`D N ≥ N ^ ρ` valid for all large `N`, and then reads the liminf statement off the family.

The two exports are `sdf_pointwise_internal` and `sdf_liminf_internal`: they are the
targets `sdf_pointwise` and `sdf_liminf_ge` of `FsLowerBound.Statements` verbatim, stated
here so that `Statements.lean` is a wiring file and not a proof file.

## The shape of §6.2, and why it is additive

§6.2's estimate is `log H = U + O(1)`: the sandwich

`maxᵢ Hᵢ ^ eᵢ ≤ 1 + Σᵢ (Hᵢ ^ eᵢ − 1) ≤ ℓ · maxᵢ Hᵢ ^ eᵢ`

with `ℓ = 11`, together with `eᵢ(U) log Hᵢ ∈ (U − log Hᵢ, U]`. That is an *additive*
`O(1)`, and the numerator and denominator of (2.6′) are then `Θ(U)` with additive `O(1)`
errors, so the ratio converges. Nothing here is a ratio-of-limits abstraction; the two
sandwich lemmas `log_stageHeight_lower` and `log_stageHeight_upper` are the whole content,
and both are stated with the explicit constants this pool provides.

Those constants are `log 12` and `log 11`, not a `Finset.max` over the pool: the largest
height in `baseBlocks` is the `299` block's `12`, and the pool has eleven entries. Writing
the two numerals keeps every statement below first-order in the pool and spares the file a
`Finset.sup` layer that would say nothing extra. `logHeight_le_max` is where the numeral
`12` is justified, one block at a time.

## The decomposition chosen for the limit

The brief left open whether to name the stage exponent and prove a `Tendsto`, or to skip
the name and produce a good stage directly for each `ρ < alphaInf`. Both are here, and in
that dependency order: `stageExponent` is named, `tendsto_stageExponent` is §6.2's
headline, and `exists_stage_exponent_gt` is the corollary §6.3 actually consumes — a single
multiplicity vector, with all `eᵢ ≥ 1`, whose exponent beats `ρ`. Naming the exponent is
what lets §6.2 be stated once as a limit rather than re-derived inside an `∃`; the
corollary is what keeps §6.3 free of any mention of `U`.

## Trust rules (ADR-033)

The ADR-033 trust rules apply: no kernel-external decision procedures, no postulated
constants, no compiler escape hatches. This file was the one Stage-4 module still in flight,
and the last file in the repository to carry a placeholder; Stage 4's proof pass has now
finished, so every statement below is final *and* proved and the repository is
placeholder-free. `D_mono`, `D_le` and the allocation arithmetic (`logHeight_pos`,
`logHeight_le_max`, `one_le_alloc`, `alloc_mul_logHeight_le`, `sub_logHeight_lt_alloc_mul`)
are named in `auditedDeclarations` in `Test/AxiomAudit.lean`; the §6.2/§6.3 chain above them
reaches the audit through the two targets of `FsLowerBound.Statements` that it discharges.
-/

/-! ## The counting function is monotone, and bounded by its argument

§6.3 needs `D N ≥ D N'` for `N ≥ N'`, which is immediate from the definition: a larger
interval has a larger powerset, so the supremum is taken over a larger family. The liminf
passage needs the trivial upper bound `D N ≤ N` as well — see `sdf_liminf_internal`, where
it is what makes the sequence `log (D N) / log N` cobounded. -/

/-- `D` is monotone. A square-difference-free subset of `{1, …, N'}` is one of the sets
`D N` takes the supremum over whenever `N' ≤ N`. -/
theorem D_mono : Monotone D := by
  intro N N' h
  classical
  unfold D
  exact Finset.sup_mono
    (Finset.filter_subset_filter _ (Finset.powerset_mono.mpr (Finset.Icc_subset_Icc_right h)))

/-- `D N ≤ N`. Every competitor is a subset of `{1, …, N}`, which has `N` elements. Trivial,
and load-bearing: `Filter.le_liminf_of_le` asks for `IsCoboundedUnder (· ≥ ·)`, and this is
where that comes from. -/
theorem D_le (N : ℕ) : D N ≤ N := by
  classical
  unfold D
  refine Finset.sup_le fun A hA => ?_
  have hsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  simpa [Nat.card_Icc] using Finset.card_le_card hsub

/-! ## The allocation

`eᵢ(U) = ⌊U / log Hᵢ⌋`, and the two facts §6.2 reads off it. -/

/-- `maxᵢ log Hᵢ` for this pool: the `299` block's height `12` is the largest of the eleven,
so `log 12` dominates every `log Hᵢ`. -/
noncomputable def maxLogHeight : ℝ := Real.log 12

/-- §6.2's allocation: `eᵢ(U) = ⌊U / log Hᵢ⌋`, as a multiplicity vector in the sense of
`FsLowerBound.Construction` — a function of the block, which reads only its height. -/
noncomputable def alloc (U : ℝ) (b : Block) : ℕ := ⌊U / Real.log b.2.2.2⌋₊

/-- Every height in the pool has positive logarithm: `Hᵢ ≥ 2`. This is §6.2's hypothesis
`Hᵢ ≥ 2` (HT.2) in the form the allocation needs — it is what makes `U / log Hᵢ` a
meaningful quantity at all. -/
theorem logHeight_pos : ∀ b ∈ baseBlocks, 0 < Real.log b.2.2.2 := by
  intro b hb
  have h := baseBlocks_two_le_height b hb
  refine Real.log_pos ?_
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two h

/-- No height exceeds `12`, so `log 12` is the `maxᵢ log Hᵢ` of §6.2's sandwich. -/
theorem logHeight_le_max : ∀ b ∈ baseBlocks, Real.log b.2.2.2 ≤ maxLogHeight := by
  intro b hb
  have h : b.2.2.2 ≤ 12 := by
    simp only [baseBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  refine Real.log_le_log ?_ ?_
  · have := baseBlocks_two_le_height b hb
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two this
  · exact_mod_cast h

/-- Each multiplicity is at least `1` once `U` clears every `log Hᵢ` — §6.2's "for
`U ≥ maxᵢ log Hᵢ`, every `eᵢ(U) ≥ 1`", which is what makes the composite Lemma A
applicable at every block. -/
theorem one_le_alloc (U : ℝ) (hU : maxLogHeight ≤ U) : ∀ b ∈ baseBlocks, 1 ≤ alloc U b := by
  intro b hb
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ (logHeight_pos b hb), one_mul]
  exact le_trans (logHeight_le_max b hb) hU

/-- The upper half of `eᵢ(U) log Hᵢ ∈ (U − log Hᵢ, U]`. -/
theorem alloc_mul_logHeight_le (U : ℝ) (hU : 0 ≤ U) (b : Block) (hb : b ∈ baseBlocks) :
    (alloc U b : ℝ) * Real.log b.2.2.2 ≤ U := by
  have hpos := logHeight_pos b hb
  have h : (alloc U b : ℝ) ≤ U / Real.log b.2.2.2 :=
    Nat.floor_le (by positivity)
  rw [le_div_iff₀ hpos] at h
  exact h

/-- The lower half of `eᵢ(U) log Hᵢ ∈ (U − log Hᵢ, U]`. -/
theorem sub_logHeight_lt_alloc_mul (U : ℝ) (b : Block) (hb : b ∈ baseBlocks) :
    U - Real.log b.2.2.2 < (alloc U b : ℝ) * Real.log b.2.2.2 := by
  have hpos := logHeight_pos b hb
  have h : U / Real.log b.2.2.2 < (alloc U b : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hpos] at h
  nlinarith

/-! ## The logarithms of the three closed forms

`log` turns each product of (2.5′) into a sum over the eleven blocks. These are the
statements §6.2 substitutes into. -/

/-- `Real.log` of a list product of positive naturals is the sum of the logarithms. The
general lemma the two closed forms below are instances of: an induction on the list, with
`Real.log_mul` at each cons and the positivity of the tail product carried along. -/
private theorem log_natProd (l : List Block) (f : Block → ℕ) (hf : ∀ b ∈ l, 0 < f b) :
    Real.log (((l.map f).prod : ℕ) : ℝ) = (l.map fun b => Real.log ((f b : ℕ) : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : (0 : ℕ) < f a := hf a List.mem_cons_self
    have ht : ∀ b ∈ t, 0 < f b := fun b hb => hf b (List.mem_cons_of_mem _ hb)
    have hp : (0 : ℕ) < (t.map f).prod :=
      List.prod_pos (by
        intro n hn
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hn
        exact ht b hb)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hp.ne'), ih ht]

/-- Pulling a constant out of a mapped sum — the constant `2` of `log P = 2 Σ eᵢ log mᵢ`
just below, and again the `U` of §6.2's weighted estimate further down. -/
private theorem sum_map_const_mul (l : List Block) (c : ℝ) (g : Block → ℝ) :
    (l.map fun b => c * g b).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `log P = 2 Σ eᵢ log mᵢ`.

Intended discharge: `Nat.cast_prod`-style exchange for `List.prod` (induction on
`baseBlocks` through a general lemma `Real.log` of a list product of positives), then
`Real.log_pow` at each factor, and `stageModulus_pos` for the positivity. -/
theorem log_stageModulus (E : Block → ℕ) :
    Real.log (stageModulus E) = 2 * (baseBlocks.map fun b => (E b : ℝ) * Real.log b.1).sum := by
  rw [stageModulus,
    log_natProd _ _ fun b hb => pow_pos (by have := baseBlocks_two_le b hb; omega) _]
  rw [List.map_congr_left (g := fun b => 2 * ((E b : ℝ) * Real.log b.1))
    fun b _ => by push_cast; rw [Real.log_pow]; push_cast; ring]
  exact sum_map_const_mul _ 2 _

/-- `log |C| = Σ eᵢ log (mᵢ tᵢ)`.

Intended discharge: as for `log_stageModulus`, at the factors `(mᵢ tᵢ) ^ eᵢ`. -/
theorem log_stageCard (E : Block → ℕ) :
    Real.log (stageCard E) =
      (baseBlocks.map fun b => (E b : ℝ) * Real.log (b.1 * b.2.1.card)).sum := by
  rw [stageCard, log_natProd _ _ fun b hb => pow_pos (Nat.mul_pos
    (by have := baseBlocks_two_le b hb; omega)
    (by have := baseBlocks_two_le_card b hb; omega)) _]
  exact congrArg List.sum (List.map_congr_left fun b _ => by push_cast; rw [Real.log_pow])

/-! ## The height sandwich

§6.2's `maxᵢ Hᵢ ^ eᵢ ≤ H ≤ ℓ · maxᵢ Hᵢ ^ eᵢ`, stated without naming the maximum: the lower
half is one block at a time, and the upper half takes any common bound. -/

/-- The lower half: the height dominates each `Hᵢ ^ eᵢ` on its own, because the sum
`1 + Σ (Hⱼ ^ eⱼ − 1)` contains the term `Hᵢ ^ eᵢ − 1` and every other term is nonnegative.

Intended discharge: `List.single_le_sum` on the mapped list, at the member `b`. -/
theorem pow_height_le_stageHeight (E : Block → ℕ) (b : Block) (hb : b ∈ baseBlocks) :
    b.2.2.2 ^ E b ≤ stageHeight E := by
  have h1 : 1 ≤ b.2.2.2 ^ E b :=
    Nat.one_le_pow _ _ (by have := baseBlocks_two_le_height b hb; omega)
  have hmem : b.2.2.2 ^ E b - 1 ∈ baseBlocks.map fun c => c.2.2.2 ^ E c - 1 :=
    List.mem_map_of_mem hb
  have hsum := List.single_le_sum (l := baseBlocks.map fun c => c.2.2.2 ^ E c - 1)
    (fun x _ => Nat.zero_le x) _ hmem
  rw [stageHeight]
  omega

/-- The upper half, with the maximum supplied by the caller: eleven terms, each at most
`M − 1`, plus one.

Intended discharge: `List.sum_le_card_nsmul` on the mapped list at `M − 1` — each summand
is `Hᵢ ^ eᵢ − 1 ≤ M − 1` — with `baseBlocks.length` computing to `11` by `rfl`. That gives
`stageHeight E ≤ 1 + 11 (M − 1) = 11 M − 10`, hence the stated bound for `M ≥ 1`; applying
the lemma at `M` itself would only give `1 + 11 M`, which is not the statement. `M = 0` is
vacuous, since `hM` at any block forces `M ≥ 1`. -/
theorem stageHeight_le_of_forall_le (E : Block → ℕ) (M : ℕ)
    (hM : ∀ b ∈ baseBlocks, b.2.2.2 ^ E b ≤ M) : stageHeight E ≤ 11 * M := by
  have hlen : (baseBlocks.map fun c => c.2.2.2 ^ E c - 1).length = 11 := by
    rw [List.length_map]; rfl
  have hterm : ∀ x ∈ baseBlocks.map fun c => c.2.2.2 ^ E c - 1, x ≤ M - 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    have := hM b hb
    omega
  have hsum := List.sum_le_card_nsmul _ (M - 1) hterm
  rw [hlen, smul_eq_mul] at hsum
  have hM1 : 1 ≤ M := by
    obtain ⟨b, hb⟩ : ∃ b, b ∈ baseBlocks := ⟨_, List.mem_cons_self⟩
    have h1 : 1 ≤ b.2.2.2 ^ E b :=
      Nat.one_le_pow _ _ (by have := baseBlocks_two_le_height b hb; omega)
    have := hM b hb
    omega
  rw [stageHeight]
  omega

/-- The last block of the pool, named so that the sandwich's lower half has a member of
`baseBlocks` to point at. It is the `299` block, whose height `12` is the largest of the
eleven; nothing below needs that, since the bound holds at every block. -/
private def block299 : Block := (299, supportFinset cert299, rankOf cert299, 12)

private theorem block299_mem : block299 ∈ baseBlocks := by simp [baseBlocks, block299]

/-- §6.2's `log H ≥ U − maxᵢ log Hᵢ`, at the allocation. The witness is any single block:
`log (Hᵢ ^ eᵢ(U)) = eᵢ(U) log Hᵢ > U − log Hᵢ ≥ U − maxᵢ log Hᵢ`.

Intended discharge: `pow_height_le_stageHeight` at the `299` block, `Real.log_le_log`,
`Real.log_pow`, then `sub_logHeight_lt_alloc_mul` and `logHeight_le_max`. -/
theorem log_stageHeight_lower (U : ℝ) (hU : maxLogHeight ≤ U) :
    U - maxLogHeight ≤ Real.log (stageHeight (alloc U)) := by
  have hb := block299_mem
  have hpos : (0 : ℕ) < block299.2.2.2 ^ alloc U block299 :=
    pow_pos (by have := baseBlocks_two_le_height _ hb; omega) _
  have hle := pow_height_le_stageHeight (alloc U) block299 hb
  have hlog : Real.log ((block299.2.2.2 ^ alloc U block299 : ℕ) : ℝ)
      ≤ Real.log ((stageHeight (alloc U) : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  have heq : Real.log ((block299.2.2.2 ^ alloc U block299 : ℕ) : ℝ)
      = (alloc U block299 : ℝ) * Real.log ((block299.2.2.2 : ℕ) : ℝ) := by
    push_cast; rw [Real.log_pow]
  have h1 := sub_logHeight_lt_alloc_mul U block299 hb
  have h2 := logHeight_le_max block299 hb
  rw [heq] at hlog
  -- This half of the sandwich holds at every `U`: `sub_logHeight_lt_alloc_mul` carries no
  -- hypothesis on `U`. The regime hypothesis is part of the statement because §6.2 states
  -- both halves in it, and the upper half does need it.
  have _hU : maxLogHeight ≤ U := hU
  linarith

/-- §6.2's `log H ≤ U + log ℓ`, at the allocation, with `ℓ = 11`. Every `Hᵢ ^ eᵢ(U)` is at
most `exp U` because `eᵢ(U) log Hᵢ ≤ U`, so the sandwich's upper half applies with
`M = ⌊exp U⌋`.

Intended discharge: `alloc_mul_logHeight_le` gives `Hᵢ ^ eᵢ(U) ≤ exp U` for each block;
being a natural, each is then `≤ ⌊exp U⌋` by `Nat.le_floor`. Feed that to
`stageHeight_le_of_forall_le` at `M = ⌊exp U⌋₊`, then `Real.log_le_log`, `Real.log_mul` and
`Nat.floor_le` to land on `log 11 + log (exp U) = U + log 11`.

The floor is the point: with `M = ⌈exp U⌉` the bound is `11 ⌈e^U⌉ ≤ 11 (e^U + 1)`, whose
logarithm can exceed `U + log 11` — the ceiling rounds the wrong way once it is multiplied
by eleven. `⌊e^U⌋ ≤ e^U` rounds the right way and the constant `11` is then exact. -/
theorem log_stageHeight_upper (U : ℝ) (hU : maxLogHeight ≤ U) :
    Real.log (stageHeight (alloc U)) ≤ U + Real.log 11 := by
  have hmax : (0 : ℝ) < maxLogHeight := Real.log_pos (by norm_num)
  have hU0 : (0 : ℝ) ≤ U := le_trans hmax.le hU
  have hexp1 : (1 : ℝ) ≤ Real.exp U := by
    have h := Real.exp_le_exp.mpr hU0
    rwa [Real.exp_zero] at h
  set M := ⌊Real.exp U⌋₊
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hexp1)
  have hkey : ∀ b ∈ baseBlocks, b.2.2.2 ^ alloc U b ≤ M := by
    intro b hb
    refine Nat.le_floor ?_
    have hposr : (0 : ℝ) < ((b.2.2.2 ^ alloc U b : ℕ) : ℝ) := by
      have h : (0 : ℕ) < b.2.2.2 ^ alloc U b :=
        pow_pos (by have := baseBlocks_two_le_height b hb; omega) _
      exact_mod_cast h
    have hlog : Real.log ((b.2.2.2 ^ alloc U b : ℕ) : ℝ) ≤ U := by
      push_cast
      rw [Real.log_pow]
      exact alloc_mul_logHeight_le U hU0 b hb
    calc ((b.2.2.2 ^ alloc U b : ℕ) : ℝ)
        = Real.exp (Real.log ((b.2.2.2 ^ alloc U b : ℕ) : ℝ)) := (Real.exp_log hposr).symm
      _ ≤ Real.exp U := Real.exp_le_exp.mpr hlog
  have hH := stageHeight_le_of_forall_le (alloc U) M hkey
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hstep : Real.log ((stageHeight (alloc U) : ℕ) : ℝ) ≤ Real.log ((11 * M : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast stageHeight_pos (alloc U)) (by exact_mod_cast hH)
  have hsplit : Real.log ((11 * M : ℕ) : ℝ) = Real.log 11 + Real.log (M : ℝ) := by
    push_cast
    exact Real.log_mul (by norm_num) (ne_of_gt hMR)
  have hMle : Real.log (M : ℝ) ≤ U := by
    have h1 : (M : ℝ) ≤ Real.exp U := Nat.floor_le (Real.exp_nonneg U)
    calc Real.log (M : ℝ) ≤ Real.log (Real.exp U) := Real.log_le_log hMR h1
      _ = U := Real.log_exp U
  rw [hsplit] at hstep
  linarith

/-! ## §6.2 — the exponent of a stage, and its limit -/

/-- The exponent a stage certifies: `α(e) = log |C| / log (P H)`, which is (2.6′) once the
logarithms above are substituted. Lemma B turns this into
`D ((P H) ^ L) ≥ ((P H) ^ L) ^ α(e)`. -/
noncomputable def stageExponent (E : Block → ℕ) : ℝ :=
  Real.log (stageCard E) / Real.log (stageModulus E * stageHeight E)

/-! ### The two pool constants, and the estimates that feed the squeeze

`alphaInf` is `A / B` with `A = Σ log(mᵢtᵢ)/log Hᵢ` and `B = 1 + 2 Σ log mᵢ/log Hᵢ`, both
evaluated on `pool`'s numerals. `poolNum` and `poolDen` are the same two sums read off
`baseBlocks` instead, and `alphaInf_eq_poolRatio` is `baseBlocks_pool` in that form — the seam that
makes §6.2 a statement about the certified construction rather than about eleven numerals.

Everything between here and `tendsto_stageExponent` is the `O(1)` bookkeeping: a triangle
inequality for list sums, the per-block estimate `|eᵢ(U) wᵢ − U wᵢ/log Hᵢ| ≤ wᵢ` that the
allocation's two-sided bound gives for any nonnegative weight `w`, and the squeeze
`(A U + O(1)) / (B U + O(1)) → A / B` for `B > 0`. -/

/-- The triangle inequality for two mapped sums: termwise `O(1)` control gives control of
the difference of the sums, with the constant the sum of the termwise ones. -/
private theorem abs_sum_map_sub_le (l : List Block) (f g k : Block → ℝ)
    (h : ∀ b ∈ l, |f b - g b| ≤ k b) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map k).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    calc |f a + (t.map f).sum - (g a + (t.map g).sum)|
        = |(f a - g a) + ((t.map f).sum - (t.map g).sum)| := by ring_nf
      _ ≤ |f a - g a| + |(t.map f).sum - (t.map g).sum| := abs_add_le _ _
      _ ≤ k a + (t.map k).sum := add_le_add h1 h2

/-- The shape of the per-block error: a nonnegative weight `L`, divided by a positive
`h`, times a quantity confined to `(−h, 0]`, is confined to `[−L, L]`. -/
private theorem abs_ratio_mul_le (L h x : ℝ) (hL : 0 ≤ L) (hh : 0 < h)
    (h1 : -h < x) (h2 : x ≤ 0) : |L / h * x| ≤ L := by
  have hLh : 0 ≤ L / h := div_nonneg hL hh.le
  have hid : L / h * h = L := div_mul_cancel₀ L (ne_of_gt hh)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left h1.le hLh
    rw [mul_neg, hid] at hm
    linarith
  · nlinarith

/-- **The `O(1)` of §6.2, once for both sums.** For any nonnegative weight `w` on the pool,
`Σᵢ eᵢ(U) wᵢ = U Σᵢ wᵢ / log Hᵢ + O(1)`, with the implied constant `Σᵢ wᵢ` — depending on
the pool only, as §6.2 requires. Both the numerator (`w = log (mᵢ tᵢ)`) and the modulus part
of the denominator (`w = log mᵢ`) are instances; the error is `eᵢ(U) log Hᵢ − U ∈ (−log Hᵢ,
0]`, which is exactly `sub_logHeight_lt_alloc_mul` and `alloc_mul_logHeight_le`. -/
private theorem abs_alloc_weighted_sub_le (U : ℝ) (hU : 0 ≤ U) (w : Block → ℝ)
    (hw : ∀ b ∈ baseBlocks, 0 ≤ w b) :
    |(baseBlocks.map fun b => (alloc U b : ℝ) * w b).sum
        - U * (baseBlocks.map fun b => w b / Real.log b.2.2.2).sum| ≤
      (baseBlocks.map w).sum := by
  rw [show U * (baseBlocks.map fun b => w b / Real.log b.2.2.2).sum
      = (baseBlocks.map fun b => U * (w b / Real.log b.2.2.2)).sum from
    (sum_map_const_mul _ _ _).symm]
  refine abs_sum_map_sub_le _ _ _ _ ?_
  intro b hb
  have hh : 0 < Real.log b.2.2.2 := logHeight_pos b hb
  have hlt : -Real.log b.2.2.2 < (alloc U b : ℝ) * Real.log b.2.2.2 - U := by
    have := sub_logHeight_lt_alloc_mul U b hb; linarith
  have hle : (alloc U b : ℝ) * Real.log b.2.2.2 - U ≤ 0 := by
    have := alloc_mul_logHeight_le U hU b hb; linarith
  have hid : (alloc U b : ℝ) * w b - U * (w b / Real.log b.2.2.2)
      = w b / Real.log b.2.2.2 * ((alloc U b : ℝ) * Real.log b.2.2.2 - U) := by
    field_simp
  rw [hid]
  exact abs_ratio_mul_le _ _ _ (hw b hb) hh hlt hle

/-- `Σᵢ log (mᵢ tᵢ) / log Hᵢ`, over the certified blocks: `alphaInf`'s numerator. -/
private noncomputable def poolNum : ℝ :=
  (baseBlocks.map fun b => Real.log (b.1 * b.2.1.card) / Real.log b.2.2.2).sum

/-- `1 + 2 Σᵢ log mᵢ / log Hᵢ`, over the certified blocks: `alphaInf`'s denominator. -/
private noncomputable def poolDen : ℝ :=
  1 + 2 * (baseBlocks.map fun b => Real.log b.1 / Real.log b.2.2.2).sum

/-- `alphaInf` is `poolNum / poolDen`. This is `baseBlocks_pool` — the tie between the
eleven certified blocks and the eleven numerals — transported through both sums. -/
private theorem alphaInf_eq_poolRatio : alphaInf = poolNum / poolDen := by
  rw [alphaInf, poolNum, poolDen, ← baseBlocks_pool, List.map_map, List.map_map]
  rfl

/-- The denominator is at least `1`: every term of `Σ log mᵢ / log Hᵢ` is nonnegative. This
is the `b > 0` the squeeze needs, and the reason the limit is a genuine real number. -/
private theorem poolDen_pos : 0 < poolDen := by
  have h : 0 ≤ (baseBlocks.map fun b => Real.log b.1 / Real.log b.2.2.2).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact div_nonneg (Real.log_natCast_nonneg _) (logHeight_pos b hb).le
  rw [poolDen]; linarith

/-- `g U = a U + O(1)` implies `g U / U → a`: squeeze between `a ± k/U`. -/
private theorem tendsto_div_atTop_of_abs_sub_le (a k : ℝ) (g : ℝ → ℝ)
    (hg : ∀ᶠ U in Filter.atTop, |g U - a * U| ≤ k) :
    Filter.Tendsto (fun U => g U / U) Filter.atTop (nhds a) := by
  have hk : Filter.Tendsto (fun U : ℝ => k / U) Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop Filter.tendsto_id k
  have hlow : Filter.Tendsto (fun U : ℝ => a - k / U) Filter.atTop (nhds a) := by
    simpa using tendsto_const_nhds.sub hk
  have hhigh : Filter.Tendsto (fun U : ℝ => a + k / U) Filter.atTop (nhds a) := by
    simpa using tendsto_const_nhds.add hk
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [hg, Filter.eventually_gt_atTop (0 : ℝ)] with U hU hU0
    rw [le_div_iff₀ hU0, show (a - k / U) * U = a * U - k by field_simp]
    linarith [(abs_le.mp hU).1]
  · filter_upwards [hg, Filter.eventually_gt_atTop (0 : ℝ)] with U hU hU0
    rw [div_le_iff₀ hU0, show (a + k / U) * U = a * U + k by field_simp]
    linarith [(abs_le.mp hU).2]

/-- **The squeeze §6.2 ends on:** `(A U + O(1)) / (B U + O(1)) → A / B` when `B > 0`. Each
of `num U / U` and `den U / U` is squeezed on its own and the two limits divided; no
ratio-of-limits abstraction and no hypothesis on the sign of `A`. -/
private theorem tendsto_ratio_of_abs_sub_le (A B k₁ k₂ : ℝ) (hB : 0 < B) (num den : ℝ → ℝ)
    (hn : ∀ᶠ U in Filter.atTop, |num U - A * U| ≤ k₁)
    (hd : ∀ᶠ U in Filter.atTop, |den U - B * U| ≤ k₂) :
    Filter.Tendsto (fun U => num U / den U) Filter.atTop (nhds (A / B)) := by
  have h3 : Filter.Tendsto (fun U => num U / U / (den U / U)) Filter.atTop (nhds (A / B)) :=
    Filter.Tendsto.div (tendsto_div_atTop_of_abs_sub_le A k₁ num hn)
      (tendsto_div_atTop_of_abs_sub_le B k₂ den hd) (ne_of_gt hB)
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with U hU0
  exact div_div_div_cancel_right₀ (ne_of_gt hU0) _ _

/-- **§6.2, the limit formula.** Along the allocation `eᵢ(U) = ⌊U / log Hᵢ⌋`, the stage
exponent tends to `alphaInf`.

Intended discharge: substitute `log_stageCard`, `log_stageModulus` and the height sandwich
into `stageExponent`; the numerator is `U · Σ log(mᵢ tᵢ)/log Hᵢ + O(1)` and the denominator
is `U · (1 + 2 Σ log mᵢ/log Hᵢ) + O(1)`, both by `sub_logHeight_lt_alloc_mul` and
`alloc_mul_logHeight_le` term by term, so the ratio converges to `alphaInf` by the
squeeze on `(a U + O(1)) / (b U + O(1))` with `b > 0`. `baseBlocks_pool` is what identifies
the two pool sums with `alphaInf`'s. -/
theorem tendsto_stageExponent :
    Filter.Tendsto (fun U : ℝ => stageExponent (alloc U)) Filter.atTop (nhds alphaInf) := by
  have hshape : (fun U : ℝ => stageExponent (alloc U)) = fun U : ℝ =>
      Real.log (stageCard (alloc U)) /
        Real.log ((stageModulus (alloc U) : ℝ) * (stageHeight (alloc U) : ℝ)) := rfl
  have hmax : (0 : ℝ) < maxLogHeight := Real.log_pos (by norm_num)
  have hlog11 : (0 : ℝ) ≤ Real.log 11 := Real.log_nonneg (by norm_num)
  rw [hshape, alphaInf_eq_poolRatio]
  refine tendsto_ratio_of_abs_sub_le poolNum poolDen
    ((baseBlocks.map fun b => Real.log ((b.1 : ℝ) * (b.2.1.card : ℝ))).sum)
    (2 * (baseBlocks.map fun b => Real.log (b.1 : ℝ)).sum + maxLogHeight + Real.log 11)
    poolDen_pos _ _ ?_ ?_
  · -- numerator: `log |C| = Σ eᵢ(U) log (mᵢ tᵢ) = U · poolNum + O(1)`
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with U hU
    have hmul : poolNum * U =
        U * (baseBlocks.map fun b => Real.log ((b.1 : ℝ) * (b.2.1.card : ℝ))
          / Real.log (b.2.2.2 : ℝ)).sum := by rw [poolNum]; ring
    rw [log_stageCard, hmul]
    refine abs_alloc_weighted_sub_le U hU _ ?_
    intro b hb
    have h1 := baseBlocks_two_le b hb
    have h2 := baseBlocks_two_le_card b hb
    have h3 : (1 : ℕ) ≤ b.1 * b.2.1.card := Nat.mul_pos (by omega) (by omega)
    exact Real.log_nonneg (by exact_mod_cast h3)
  · -- denominator: `log P + log H = 2 U Σ log mᵢ/log Hᵢ + U + O(1)`, the height's `O(1)`
    -- being the sandwich and the modulus' the same weighted estimate at `w = log mᵢ`
    filter_upwards [Filter.eventually_ge_atTop maxLogHeight] with U hU
    have hU0 : (0 : ℝ) ≤ U := le_trans hmax.le hU
    have hP : ((stageModulus (alloc U) : ℕ) : ℝ) ≠ 0 := by
      have := stageModulus_pos (alloc U); positivity
    have hH : ((stageHeight (alloc U) : ℕ) : ℝ) ≠ 0 := by
      have := stageHeight_pos (alloc U); positivity
    have hS := abs_alloc_weighted_sub_le U hU0 (fun b => Real.log (b.1 : ℝ))
      (fun b _ => Real.log_natCast_nonneg _)
    have hLH1 := log_stageHeight_lower U hU
    have hLH2 := log_stageHeight_upper U hU
    rw [Real.log_mul hP hH, log_stageModulus, poolDen, abs_le]
    constructor <;> [linarith [(abs_le.mp hS).1]; linarith [(abs_le.mp hS).2]]

/-- The corollary §6.3 consumes: below `alphaInf` there is an honest finite stage, with
every multiplicity positive and a stage size worth taking logarithms of.

Intended discharge: `tendsto_stageExponent` with `hρ` gives `ρ < stageExponent (alloc U)`
eventually; intersect with `U ≥ maxLogHeight`, which supplies `one_le_alloc`, and with the
`one_lt_stageModulus` / `one_lt_stageHeight` of `FsLowerBound.Construction`. -/
theorem exists_stage_exponent_gt (ρ : ℝ) (hρ : ρ < alphaInf) :
    ∃ E : Block → ℕ, (∀ b ∈ baseBlocks, 1 ≤ E b) ∧ 1 < stageModulus E * stageHeight E ∧
      ρ < stageExponent E := by
  have h1 : ∀ᶠ U : ℝ in Filter.atTop, ρ < stageExponent (alloc U) :=
    tendsto_stageExponent.eventually_const_lt hρ
  obtain ⟨U, hU1, hU2⟩ := (h1.and (Filter.eventually_ge_atTop maxLogHeight)).exists
  refine ⟨alloc U, one_le_alloc U hU2, ?_, hU1⟩
  have hP := one_lt_stageModulus (alloc U) (one_le_alloc U hU2)
  have hH := (one_lt_stageHeight (alloc U) (one_le_alloc U hU2)).le
  calc 1 < stageModulus (alloc U) := hP
    _ = stageModulus (alloc U) * 1 := (mul_one _).symm
    _ ≤ stageModulus (alloc U) * stageHeight (alloc U) := Nat.mul_le_mul_left _ hH

/-! ## §6.3 — from the special `N_L` to all `N`

The passage is a statement about two bare naturals `B ≥ 2` and `C ≥ 2` and nothing else:
if `C ^ L ≤ D (B ^ L)` for every `L ≥ 1`, then `D N ≥ N ^ ρ` eventually, for every
`ρ` below `log C / log B`. `passage` states it in exactly that generality — the stage
enters only through `stage_D_bound`, at `B = P H` and `C = |C|`. -/

/-- **§6.3, with the stage abstracted away.** `B ^ L ≤ N < B ^ (L+1)` at
`L = ⌊log N / log B⌋` puts `N` between two consecutive special values, and monotonicity of
`D` carries the count at the lower one up to `N`:

`D N ≥ D (B ^ L) ≥ C ^ L = B ^ (α L) ≥ N ^ α / B ^ α`,  `α := log C / log B`,

the last step because `N < B ^ (L+1)` and `x ↦ x ^ α` is monotone. The leftover factor
`B ^ (−α)` is a constant, and `N ^ ρ · B ^ α ≤ N ^ α` for all large `N` because
`N ^ (α − ρ) → ∞`; that absorption is where `ρ < α` is spent, and it is the only place. -/
private theorem passage (B C : ℕ) (hB : 2 ≤ B) (hC : 2 ≤ C) (ρ : ℝ)
    (hstage : ∀ L : ℕ, 1 ≤ L → C ^ L ≤ D (B ^ L))
    (hρ : ρ < Real.log C / Real.log B) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D N : ℝ) := by
  set α := Real.log C / Real.log B with hαdef
  have hb1 : (1 : ℝ) < B := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hB
  have hb0 : (0 : ℝ) < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos hb1
  have hc1 : (1 : ℝ) < C := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hC
  have hlogC : 0 < Real.log C := Real.log_pos hc1
  have hα0 : 0 < α := div_pos hlogC hlogB
  have hBα : (B : ℝ) ^ α = (C : ℝ) := by
    rw [Real.rpow_def_of_pos hb0, hαdef,
      show Real.log B * (Real.log C / Real.log B) = Real.log C by field_simp]
    exact Real.exp_log (by linarith)
  have hBα0 : (0 : ℝ) < (B : ℝ) ^ α := Real.rpow_pos_of_pos hb0 α
  -- The constant `B ^ α` is absorbed by `N ^ (α − ρ) → ∞`.
  have habs : ∀ᶠ N : ℕ in Filter.atTop, (B : ℝ) ^ α * (N : ℝ) ^ ρ ≤ (N : ℝ) ^ α := by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (α - ρ)) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by linarith)
    have h1' : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (α - ρ)) Filter.atTop Filter.atTop :=
      h1.comp tendsto_natCast_atTop_atTop
    filter_upwards [h1'.eventually_ge_atTop ((B : ℝ) ^ α), Filter.eventually_ge_atTop 1]
      with N hN hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hp : (0 : ℝ) < (N : ℝ) ^ ρ := Real.rpow_pos_of_pos hN0 ρ
    have h2 := mul_le_mul_of_nonneg_right hN hp.le
    rwa [← Real.rpow_add hN0, sub_add_cancel] at h2
  filter_upwards [habs, Filter.eventually_ge_atTop B, Filter.eventually_ge_atTop 1]
    with N hN hNB hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNB' : (B : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNB
  have hN1' : (1 : ℝ) < N := lt_of_lt_of_le hb1 hNB'
  have hlogN : 0 < Real.log N := Real.log_pos hN1'
  set L := ⌊Real.log N / Real.log B⌋₊ with hL
  have hnn : (0 : ℝ) ≤ Real.log N / Real.log B :=
    div_nonneg (Real.log_natCast_nonneg _) hlogB.le
  have hLratio : (1 : ℝ) ≤ Real.log N / Real.log B :=
    (one_le_div hlogB).mpr (Real.log_le_log hb0 hNB')
  have hL1 : 1 ≤ L := Nat.le_floor (by exact_mod_cast hLratio)
  have hfl : (L : ℝ) ≤ Real.log N / Real.log B := Nat.floor_le hnn
  have hBLle : (B : ℝ) ^ L ≤ (N : ℝ) := by
    have h : (L : ℝ) * Real.log B ≤ Real.log N := by rw [← le_div_iff₀ hlogB]; exact hfl
    have h2 : Real.log ((B : ℝ) ^ L) ≤ Real.log N := by rw [Real.log_pow]; exact h
    exact (Real.log_le_log_iff (by positivity) hN0).mp h2
  have hBLleN : B ^ L ≤ N := by exact_mod_cast hBLle
  have hNlt : (N : ℝ) < (B : ℝ) ^ (L + 1) := by
    have h := Nat.lt_floor_add_one (Real.log N / Real.log B)
    rw [← hL] at h
    have h2 : Real.log N < ((L : ℝ) + 1) * Real.log B := by rw [← div_lt_iff₀ hlogB]; exact h
    have h3 : Real.log N < Real.log ((B : ℝ) ^ (L + 1)) := by
      rw [Real.log_pow]; push_cast; linarith
    exact (Real.log_lt_log_iff hN0 (by positivity)).mp h3
  have hcount : (C : ℝ) ^ L ≤ (D N : ℝ) := by
    have h1 := hstage L hL1
    have h2 : D (B ^ L) ≤ D N := D_mono hBLleN
    have h3 : C ^ L ≤ D N := le_trans h1 h2
    exact_mod_cast h3
  have hCL : (B : ℝ) ^ (α * (L : ℝ)) = (C : ℝ) ^ L := by
    rw [Real.rpow_mul hb0.le, hBα, Real.rpow_natCast]
  have hupper : (N : ℝ) ^ α ≤ (B : ℝ) ^ (α * (L : ℝ)) * (B : ℝ) ^ α := by
    have h1 : (N : ℝ) ^ α ≤ ((B : ℝ) ^ (L + 1)) ^ α :=
      Real.rpow_le_rpow hN0.le hNlt.le hα0.le
    have h2 : ((B : ℝ) ^ (L + 1)) ^ α = (B : ℝ) ^ (α * (L : ℝ)) * (B : ℝ) ^ α := by
      rw [← Real.rpow_natCast (B : ℝ) (L + 1), ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
      push_cast; ring_nf
    rwa [h2] at h1
  have hkey : (B : ℝ) ^ α * (N : ℝ) ^ ρ ≤ (B : ℝ) ^ α * (D N : ℝ) := by
    calc (B : ℝ) ^ α * (N : ℝ) ^ ρ ≤ (N : ℝ) ^ α := hN
      _ ≤ (B : ℝ) ^ (α * (L : ℝ)) * (B : ℝ) ^ α := hupper
      _ = (C : ℝ) ^ L * (B : ℝ) ^ α := by rw [hCL]
      _ ≤ (D N : ℝ) * (B : ℝ) ^ α := by nlinarith
      _ = (B : ℝ) ^ α * (D N : ℝ) := by ring
  exact le_of_mul_le_mul_left hkey hBα0

/-- **§6.3's chain, at a fixed stage.** With `P H > 1` and `α := α(e) > ρ`, take
`L := ⌊log N / log (P H)⌋` for `N ≥ P H`; then `L ≥ 1`, `(P H) ^ L ≤ N`, and

`D N ≥ D ((P H) ^ L) ≥ |C| ^ L = ((P H) ^ L) ^ α > (N / (P H)) ^ α = (P H) ^ (−α) N ^ α`,

which exceeds `N ^ ρ` once `N` is large, since `α > ρ`.

Intended discharge: `D_mono` for the first inequality, `stage_D_bound` for the second,
`Real.rpow_natCast` and `Real.rpow_le_rpow_left_iff` to move between the ℕ powers and the
real exponent, and `Nat.lt_floor_add_one` for `N < (P H) ^ (L + 1)`. -/
theorem stage_pointwise (E : Block → ℕ) (hE : ∀ b ∈ baseBlocks, 1 ≤ E b)
    (hPH : 1 < stageModulus E * stageHeight E) (ρ : ℝ) (hρ : ρ < stageExponent E) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D N : ℝ) := by
  refine passage (stageModulus E * stageHeight E) (stageCard E) (by omega)
    (by have := one_lt_stageCard E hE; omega) ρ (fun L hL => stage_D_bound E hE L hL) ?_
  rw [Nat.cast_mul]
  exact hρ

/-- **Target 2, internally.** For every `ρ < alphaInf`, eventually `N ^ ρ ≤ D N`.

Intended discharge: `exists_stage_exponent_gt` then `stage_pointwise`. -/
theorem sdf_pointwise_internal (ρ : ℝ) (hρ : ρ < alphaInf) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D N : ℝ) := by
  obtain ⟨E, hE, hPH, hex⟩ := exists_stage_exponent_gt ρ hρ
  exact stage_pointwise E hE hPH ρ hex

/-- **Target 1, internally.** The liminf bound, derived from the pointwise form: for each
`ρ < alphaInf` the pointwise bound gives `log (D N) / log N ≥ ρ` eventually, hence
`ρ ≤ liminf`; letting `ρ ↗ alphaInf` gives the claim.

Intended discharge: `Filter.le_liminf_of_le` at each `ρ < alphaInf`, then
`le_of_forall_lt_imp_le_of_dense` (there is no `le_of_forall_lt_iff_le` on this toolchain)
to pass to the supremum. The step from `N ^ ρ ≤ D N` to `ρ ≤ log (D N) / log N` is
`Real.log_le_log` plus `Real.log_rpow`, valid for `N ≥ 2`.

One gap has to be paid explicitly. ℝ is not a complete lattice, so `Filter.le_liminf_of_le`
carries an `IsCoboundedUnder (· ≥ ·) atTop` side condition, and its `isBoundedDefault`
autoParam does *not* discharge it here. The cheap route is an eventual *upper* bound:
`D_le` gives `D N ≤ N`, hence `log (D N) / log N ≤ 1` for `N ≥ 2` (with the `D N = 0`
branch handled by `Real.log_zero`), and then
`Filter.IsBoundedUnder.isCoboundedUnder_ge ⟨1, hb⟩` is the whole of it. So `D_le` is a
prerequisite of this theorem, not a convenience. -/
theorem sdf_liminf_internal :
    alphaInf ≤ Filter.liminf (fun N : ℕ => Real.log (D N) / Real.log N) Filter.atTop := by
  set u : ℕ → ℝ := fun N => Real.log (D N) / Real.log N with hu
  -- The cobounded side condition, paid with `D_le`: `u N ≤ 1` for `N ≥ 2`.
  have hb : ∀ᶠ N : ℕ in Filter.atTop, u N ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have hlogN : 0 < Real.log N := Real.log_pos hN1
    have hDN : (D N : ℝ) ≤ (N : ℝ) := by exact_mod_cast D_le N
    have hlog : Real.log (D N) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos (D N) with h0 | h0
      · rw [h0]; simpa using hlogN.le
      · exact Real.log_le_log (by exact_mod_cast h0) hDN
    rw [hu]; simp only
    rw [div_le_one hlogN]
    exact hlog
  have hcob : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u :=
    Filter.IsBoundedUnder.isCoboundedUnder_ge ⟨1, hb⟩
  refine le_of_forall_lt_imp_le_of_dense fun ρ hρ => ?_
  refine Filter.le_liminf_of_le hcob ?_
  filter_upwards [sdf_pointwise_internal ρ hρ, Filter.eventually_ge_atTop 2] with N h hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hpos : (0 : ℝ) < (N : ℝ) ^ ρ := Real.rpow_pos_of_pos hN0 ρ
  have hlog : Real.log ((N : ℝ) ^ ρ) ≤ Real.log (D N) := Real.log_le_log hpos h
  rw [Real.log_rpow hN0] at hlog
  rw [hu]; simp only
  rw [le_div_iff₀ hlogN]
  linarith
