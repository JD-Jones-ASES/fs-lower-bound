import FsLowerBound.Pool
import FsLowerBound.Asymptotics
import FsLowerBound.Numeric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.style.header false

/-!
# The target statements

The three theorems below are the goal of the formalization. They are pinned here as
targets, and the stages that discharge them are:

* Stage 2 — Lemma A, the composite even-digit lift;
* Stage 3 — Krachun's Lemmas 4 and 5, which must be proved here, not cited;
* Stage 4 — the exponent arithmetic, the liminf passage, and the numeric bound.

All four stages have landed. Stage 4's five modules —
`FsLowerBound.Pool`, `FsLowerBound.PaleyBlocks`, `FsLowerBound.Construction`,
`FsLowerBound.Asymptotics` and `FsLowerBound.Numeric` — are now imported above, and this
file has become the wiring that ties them to the three targets rather than a file that
proves anything itself.

All three targets are wired, all three are proved, and this file contains no proof of its
own. `alphaInf_gt` is discharged by `FsLowerBound.Numeric`, from twenty-two kernel-checked
comparisons of natural powers and one rational assembly. `sdf_liminf_ge` and `sdf_pointwise`
delegate to the internal statements `sdf_liminf_internal` and `sdf_pointwise_internal` of
`FsLowerBound.Asymptotics`, which are these two verbatim and where §6.2 and §6.3 are proved.
All three are in `auditedDeclarations`, and the CI grep now exempts no file from being
placeholder-free: the in-flight list it once carried is empty.

The delegation is not a formality: it is what keeps the pinned statements byte-identical
across the stages while the proof work moves around behind them. A target that changed
shape to suit a proof would not be the target any more.

`pool` and `alphaInf` used to be defined at the top of this file. They now live in
`FsLowerBound.Pool`, unchanged, because Stage 4's machinery has to speak about them and this
file has to import that machinery; see that module's header for the move. They are
definitions, not conjectures: `alphaInf` is the closed form evaluated on the eleven-block
pool, and `sdf_liminf_ge` asserts that it bounds the liminf from below.
-/

/-- Main target: the liminf lower bound. -/
theorem sdf_liminf_ge :
    alphaInf ≤ Filter.liminf (fun N : ℕ => Real.log (D N) / Real.log N) Filter.atTop :=
  sdf_liminf_internal

/-- Pointwise ε-form. -/
theorem sdf_pointwise (ρ : ℝ) (hρ : ρ < alphaInf) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D N : ℝ) :=
  sdf_pointwise_internal ρ hρ

/-- Verified numeric headline (Stage 4; rational bounds on ratios of logarithms, each
certified by a comparison of natural powers). -/
theorem alphaInf_gt : (0.7537 : ℝ) < alphaInf := alphaInf_gt_internal
