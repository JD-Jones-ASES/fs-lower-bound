import FsLowerBound.Pool
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Linarith

-- This project carries a single MIT LICENSE file rather than per-file headers.
set_option linter.style.header false

/-!
# Layer N — the numeric lower bound on `alphaInf`

This file proves `0.7537 < alphaInf` with no transcendental numerics anywhere. The one idea
is that every fact about a logarithm that the bound needs has the form

`p / q < log a / log b`  or  `log a / log b < p / q`,   `a, b ≥ 2` naturals,

and that — `log b` being positive — each is equivalent to a comparison of two natural
numbers: `b ^ p < a ^ q` in the first case, `a ^ q < b ^ p` in the second. Those comparisons
the Lean kernel settles directly. `lt_log_div_log` and `log_div_log_lt` are the two
translations, and everything below is those two applied twenty-two times and the resulting
rationals added up.

## Why `decide` and not `norm_num` on the power comparisons

The design brief expected `norm_num` to discharge the twenty-two comparisons, and under the
full `Mathlib.Tactic.NormNum` bundle it does — measurably fast, at these sizes. This file
deliberately imports only `Mathlib.Tactic.NormNum.Basic`, which is enough for the small
rational arithmetic below but *not* enough for the comparisons: with that narrow import
`norm_num` evaluates both powers and then leaves the goal as a bare inequality between two
`1182`-digit literals, unsolved. The claim is about the import surface of this file, not
about the tactic.

`decide` is the answer to that, and the better answer anyway: the kernel's arbitrary
precision arithmetic evaluates `Nat.pow` and `Nat.decLt` directly, so the largest pair here
— `11 ^ 1135` against `1133 ^ 387` — costs tens of milliseconds and the whole file
elaborates in about ten seconds. Since `decide` is *more* kernel-bound than `norm_num`, not
less, this is a strengthening of the trust posture rather than a relaxation; ADR-033 asks
for kernel checks and this is one. `norm_num` is still what closes the purely rational
assembly at the end, where the numbers are small.

## The rationals

The twenty-two pairs `p / q` below are best rational approximations with denominator at
most `400`, computed from `Decimal` logarithms at eighty digits of working precision and
verified in two ways before being written here: each `p / q` was checked against the true
ratio, and each *natural-number* comparison `b ^ p < a ^ q` was checked in exact integer
arithmetic. The assembled bound is

`alphaInf > A / B = 0.75372508855680…`, `A = Σ ρᵢ`, `B = 1 + 2 Σ σᵢ`,

against a true value of `0.75374154183732940…`, so the twenty-two roundings cost
`1.65 × 10⁻⁵` of the `4.15 × 10⁻⁵` available above `0.7537` and the bound clears the target
with a margin of `2.51 × 10⁻⁵` — a safety factor of about `2.5` on the rounding loss, which
is the "leave a 2× factor" the brief asks for.

Every numeral in the `ρ` and `σ` sections is *substitutable*: the numeric scout's final
choice replaces the four numbers in a line and nothing else, since each lemma's proof is
the same three-argument application of a translation lemma plus a `decide`. The pairs
carried here are the ones this file was verified with, so the file is honest as written and
a tightening is an improvement rather than a repair.

## Trust rules (ADR-033)

The ADR-033 trust rules apply: no kernel-external decision procedures, no postulated
constants, no compiler escape hatches. Every declaration in this file is proved.
-/

set_option maxRecDepth 10000
-- Lean core's `exponentiation.threshold` is an evaluation guard, default `256`; every
-- comparison here exceeds it. Without this the kernel-backed `decide`s still succeed, but
-- each logs a threshold warning, which would break the zero-warning contract. The proof
-- terms are kernel-checked either way.
set_option exponentiation.threshold 100000

/-! ## The two translations

A rational bound on `log a / log b` *is* a comparison of natural powers. Both directions are
one application of strict monotonicity of `log` to `Real.log_pow`.

The hypothesis `2 ≤ a` is inert in `lt_log_div_log`: what that proof needs about `a` is
supplied by `b ^ p < a ^ q` itself. It is kept because the two statements are meant to be
read as a pair, with the same standing hypotheses on `a` and `b`, and because every caller
has it to hand — and it is named `_ha` there, which is how Lean spells "deliberately
retained, deliberately unused". -/

/-- `p / q < log a / log b`, from the natural-number comparison `b ^ p < a ^ q`. -/
theorem lt_log_div_log (a b : ℝ) (p q : ℕ) (_ha : 2 ≤ a) (hb : 2 ≤ b) (hq : 0 < q)
    (h : b ^ p < a ^ q) : (p : ℝ) / q < Real.log a / Real.log b := by
  have hb1 : (1 : ℝ) < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbp : (0 : ℝ) < b ^ p := by positivity
  have h1 : Real.log (b ^ p) < Real.log (a ^ q) := Real.log_lt_log hbp h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_lt_div_iff₀ hqR hlb]
  linarith

/-- `log a / log b < p / q`, from the natural-number comparison `a ^ q < b ^ p`. -/
theorem log_div_log_lt (a b : ℝ) (p q : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hq : 0 < q)
    (h : a ^ q < b ^ p) : Real.log a / Real.log b < (p : ℝ) / q := by
  have hb1 : (1 : ℝ) < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haq : (0 : ℝ) < a ^ q := by positivity
  have h1 : Real.log (a ^ q) < Real.log (b ^ p) := Real.log_lt_log haq h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_lt_div_iff₀ hlb hqR]
  linarith

/-! ## `alphaInf` as an expression in eleven pairs of logarithms

`alphaInf` is a fold over `pool`. Unfolding it once, here, is what lets the rest of the file
speak in numerals. -/

/-- `alphaInf`, with the `pool` fold evaluated. -/
theorem alphaInf_eq_numerals :
    alphaInf =
      (Real.log 6 / Real.log 2 + Real.log 21 / Real.log 3 + Real.log 44 / Real.log 4 +
        Real.log 95 / Real.log 5 + Real.log 217 / Real.log 7 + Real.log 301 / Real.log 7 +
        Real.log 531 / Real.log 9 + Real.log 639 / Real.log 9 + Real.log 1133 / Real.log 11 +
        Real.log 3995 / Real.log 11 + Real.log 5681 / Real.log 12) /
      (1 + 2 * (Real.log 3 / Real.log 2 + Real.log 7 / Real.log 3 + Real.log 11 / Real.log 4 +
        Real.log 19 / Real.log 5 + Real.log 31 / Real.log 7 + Real.log 43 / Real.log 7 +
        Real.log 59 / Real.log 9 + Real.log 71 / Real.log 9 + Real.log 103 / Real.log 11 +
        Real.log 235 / Real.log 11 + Real.log 299 / Real.log 12)) := by
  norm_num [alphaInf, pool]
  ring

/-! ## The eleven lower bounds `ρᵢ < log (mᵢ tᵢ) / log Hᵢ`

**Substitutable numerals.** Each line is `lt_log_div_log (mᵢ tᵢ) Hᵢ p q … (b ^ p < a ^ q)`;
replacing `p` and `q` in the statement and in the `decide`d comparison is the whole of a
retuning. -/

theorem logLo3 : (928 : ℝ) / 359 < Real.log 6 / Real.log 2 :=
  lt_log_div_log 6 2 928 359 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (2 : ℕ) ^ 928 < 6 ^ 359))

theorem logLo7 : (424 : ℝ) / 153 < Real.log 21 / Real.log 3 :=
  lt_log_div_log 21 3 424 153 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (3 : ℕ) ^ 424 < 21 ^ 153))

theorem logLo11 : (1040 : ℝ) / 381 < Real.log 44 / Real.log 4 :=
  lt_log_div_log 44 4 1040 381 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (4 : ℕ) ^ 1040 < 44 ^ 381))

theorem logLo19 : (979 : ℝ) / 346 < Real.log 95 / Real.log 5 :=
  lt_log_div_log 95 5 979 346 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (5 : ℕ) ^ 979 < 95 ^ 346))

theorem logLo31 : (47 : ℝ) / 17 < Real.log 217 / Real.log 7 :=
  lt_log_div_log 217 7 47 17 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (7 : ℕ) ^ 47 < 217 ^ 17))

theorem logLo43 : (830 : ℝ) / 283 < Real.log 301 / Real.log 7 :=
  lt_log_div_log 301 7 830 283 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (7 : ℕ) ^ 830 < 301 ^ 283))

theorem logLo59 : (871 : ℝ) / 305 < Real.log 531 / Real.log 9 :=
  lt_log_div_log 531 9 871 305 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (9 : ℕ) ^ 871 < 531 ^ 305))

theorem logLo71 : (147 : ℝ) / 50 < Real.log 639 / Real.log 9 :=
  lt_log_div_log 639 9 147 50 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (9 : ℕ) ^ 147 < 639 ^ 50))

theorem logLo103 : (1135 : ℝ) / 387 < Real.log 1133 / Real.log 11 :=
  lt_log_div_log 1133 11 1135 387 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (11 : ℕ) ^ 1135 < 1133 ^ 387))

theorem logLo235 : (83 : ℝ) / 24 < Real.log 3995 / Real.log 11 :=
  lt_log_div_log 3995 11 83 24 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (11 : ℕ) ^ 83 < 3995 ^ 24))

theorem logLo299 : (661 : ℝ) / 190 < Real.log 5681 / Real.log 12 :=
  lt_log_div_log 5681 12 661 190 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (12 : ℕ) ^ 661 < 5681 ^ 190))

/-! ## The eleven upper bounds `log mᵢ / log Hᵢ < σᵢ`

**Substitutable numerals**, on the same terms as the section above. -/

theorem logHi3 : Real.log 3 / Real.log 2 < (485 : ℝ) / 306 :=
  log_div_log_lt 3 2 485 306 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (3 : ℕ) ^ 306 < 2 ^ 485))

theorem logHi7 : Real.log 7 / Real.log 3 < (604 : ℝ) / 341 :=
  log_div_log_lt 7 3 604 341 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (7 : ℕ) ^ 341 < 3 ^ 604))

theorem logHi11 : Real.log 11 / Real.log 4 < (64 : ℝ) / 37 :=
  log_div_log_lt 11 4 64 37 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (11 : ℕ) ^ 37 < 4 ^ 64))

theorem logHi19 : Real.log 19 / Real.log 5 < (397 : ℝ) / 217 :=
  log_div_log_lt 19 5 397 217 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (19 : ℕ) ^ 217 < 5 ^ 397))

theorem logHi31 : Real.log 31 / Real.log 7 < (683 : ℝ) / 387 :=
  log_div_log_lt 31 7 683 387 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (31 : ℕ) ^ 387 < 7 ^ 683))

theorem logHi43 : Real.log 43 / Real.log 7 < (288 : ℝ) / 149 :=
  log_div_log_lt 43 7 288 149 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (43 : ℕ) ^ 149 < 7 ^ 288))

theorem logHi59 : Real.log 59 / Real.log 9 < (193 : ℝ) / 104 :=
  log_div_log_lt 59 9 193 104 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (59 : ℕ) ^ 104 < 9 ^ 193))

theorem logHi71 : Real.log 71 / Real.log 9 < (712 : ℝ) / 367 :=
  log_div_log_lt 71 9 712 367 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (71 : ℕ) ^ 367 < 9 ^ 712))

theorem logHi103 : Real.log 103 / Real.log 11 < (259 : ℝ) / 134 :=
  log_div_log_lt 103 11 259 134 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (103 : ℕ) ^ 134 < 11 ^ 259))

theorem logHi235 : Real.log 235 / Real.log 11 < (403 : ℝ) / 177 :=
  log_div_log_lt 235 11 403 177 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (235 : ℕ) ^ 177 < 11 ^ 403))

theorem logHi299 : Real.log 299 / Real.log 12 < (39 : ℝ) / 17 :=
  log_div_log_lt 299 12 39 17 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (299 : ℕ) ^ 17 < 12 ^ 39))

/-! ## The assembly

`A / B` with `A = Σ ρᵢ` and `B = 1 + 2 Σ σᵢ` is a rational number, and it exceeds `0.7537`.
The passage from the twenty-two bounds to `alphaInf > A / B` needs only that the
denominator is positive, which every `log Hᵢ > 0` supplies. -/

/-- **Target 3, internally.** `0.7537 < alphaInf`, from the twenty-two rational bounds. -/
theorem alphaInf_gt_internal : (0.7537 : ℝ) < alphaInf := by
  have l2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have l3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have l4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have l5 : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)
  have l7 : (0 : ℝ) < Real.log 7 := Real.log_pos (by norm_num)
  have l9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have l11 : (0 : ℝ) < Real.log 11 := Real.log_pos (by norm_num)
  have l12 : (0 : ℝ) < Real.log 12 := Real.log_pos (by norm_num)
  have l19 : (0 : ℝ) < Real.log 19 := Real.log_pos (by norm_num)
  have l31 : (0 : ℝ) < Real.log 31 := Real.log_pos (by norm_num)
  have l43 : (0 : ℝ) < Real.log 43 := Real.log_pos (by norm_num)
  have l59 : (0 : ℝ) < Real.log 59 := Real.log_pos (by norm_num)
  have l71 : (0 : ℝ) < Real.log 71 := Real.log_pos (by norm_num)
  have l103 : (0 : ℝ) < Real.log 103 := Real.log_pos (by norm_num)
  have l235 : (0 : ℝ) < Real.log 235 := Real.log_pos (by norm_num)
  have l299 : (0 : ℝ) < Real.log 299 := Real.log_pos (by norm_num)
  have d1 : (0 : ℝ) < Real.log 3 / Real.log 2 := div_pos l3 l2
  have d2 : (0 : ℝ) < Real.log 7 / Real.log 3 := div_pos l7 l3
  have d3 : (0 : ℝ) < Real.log 11 / Real.log 4 := div_pos l11 l4
  have d4 : (0 : ℝ) < Real.log 19 / Real.log 5 := div_pos l19 l5
  have d5 : (0 : ℝ) < Real.log 31 / Real.log 7 := div_pos l31 l7
  have d6 : (0 : ℝ) < Real.log 43 / Real.log 7 := div_pos l43 l7
  have d7 : (0 : ℝ) < Real.log 59 / Real.log 9 := div_pos l59 l9
  have d8 : (0 : ℝ) < Real.log 71 / Real.log 9 := div_pos l71 l9
  have d9 : (0 : ℝ) < Real.log 103 / Real.log 11 := div_pos l103 l11
  have d10 : (0 : ℝ) < Real.log 235 / Real.log 11 := div_pos l235 l11
  have d11 : (0 : ℝ) < Real.log 299 / Real.log 12 := div_pos l299 l12
  have hden : (0 : ℝ) <
      1 + 2 * (Real.log 3 / Real.log 2 + Real.log 7 / Real.log 3 + Real.log 11 / Real.log 4 +
        Real.log 19 / Real.log 5 + Real.log 31 / Real.log 7 + Real.log 43 / Real.log 7 +
        Real.log 59 / Real.log 9 + Real.log 71 / Real.log 9 + Real.log 103 / Real.log 11 +
        Real.log 235 / Real.log 11 + Real.log 299 / Real.log 12) := by linarith
  rw [alphaInf_eq_numerals, lt_div_iff₀ hden]
  linarith [logLo3, logLo7, logLo11, logLo19, logLo31, logLo43, logLo59, logLo71, logLo103,
    logLo235, logLo299, logHi3, logHi7, logHi11, logHi19, logHi31, logHi43, logHi59, logHi71,
    logHi103, logHi235, logHi299]
