# A lower bound for the Furstenberg–Sárközy problem

Let D(N) be the largest size of a subset of {1,…,N} no two of whose elements differ by a
nonzero perfect square. This note proves

> **Theorem.** liminf_{N→∞} log D(N) / log N ≥ α∞, where
>
> α∞ = 0.753741541837329405…  (nearest IEEE double: 0.7537415418373294)
>
> is the value of an explicit closed-form optimization over an eleven-block pool: nine
> Paley chains and two square-DAG certificates on the composite moduli 235 and 299,
> lifted by Lemma A below, glued by Krachun's Lemma 5, and converted into integer sets
> by his Lemma 4.

Equivalently, in pointwise form: for every ε > 0 there is an N₀(ε) with
D(N) ≥ N^(α∞−ε) for all N ≥ N₀(ε). The statement is a liminf: the argument supplies no
constant c with D(N) ≥ c·N^(α∞) for all N, and no such claim is made here.

The previous record is Krachun's α★ = 0.752796455874514… (arXiv:2608.01325), the first
bound past 3/4. Only one lemma is new: the lift of a
square-DAG on a square-free composite modulus (Lemma A). Krachun's Lemmas 4 and 5 are
used exactly as published.

**Corollary.** For prime q, let IM(2,q) be the largest induced matching in the point–line
incidence graph of F_q². Then for every ε > 0, IM(2,q) ≫_ε q^(1/2 + α∞ − ε). This follows
from Hunter–Pohoata–Verstraëte–Zhang, Prop. 2.3: a square-difference-free A ⊆ {1,…,⌊q/10⌋}
yields an induced point–line matching in F_q² of size Ω(√q·|A|); the implication is a
black box in A. Prime q only; the statement is not made for prime powers.

## Context

| Year | Source | Exponent |
|---|---|---|
| 1984 | Ruzsa | 0.733077 |
| 2008, 2015 | Beigel–Gasarch; Lewko (independently) | 0.733412 |
| 2026 | Krachun | 0.752796… |
| 2026 | this repository | 0.753741… |

The classical constructions are the height-1 case — a support with no square difference at
all, no ranks, used as alternating digits — with exponent ½(1 + log t / log m). The record
for that quantity is ½(1 + log 12 / log 205) = 0.733412, from m = 205, t = 12. For prime m
the height-1 exponent never exceeds 3/4: a square-difference-free support mod p is an
independent set in the Paley graph, of size at most √p when p ≡ 1 (mod 4), and is a single
point when p ≡ 3 (mod 4) or p = 2. Krachun crossed 3/4 by making height, rather than width, the
quantity that pays for itself in the CRT glue. This note keeps his glue and widens the
supply of blocks: square-DAGs on square-free composite moduli, where height can be strictly
smaller than width (11 < 17 and 12 < 19 for the two certificates below).

For the size of the remaining gap, the best upper bound is Green–Sawhney,
D(N) ≪ N·e^(−c√(log N)).

## Definitions

**D(N).** The largest |A| over A ⊆ {1,…,N} with no two elements differing by a nonzero
perfect square. Such an A is called *square-difference-free* (SDF).

**The arc set.** For m ≥ 2,

```
Q_m := {z² mod m : z ∈ Z} ∖ {0},
```

the full image of squaring modulo m with 0 removed. For square-free m, by CRT,
d ∈ Q_m ∪ {0} if and only if d mod q is a square (possibly 0) in F_q for every prime
q | m. Elements of Q_m may be **non-units** — zero in some CRT coordinates but not all.
This is part of the definition, not an implementation choice: Remark 1 below exhibits a
counterexample showing that the unit-only variant makes Lemma A false. Sizes:
|Q_235| = 71, |Q_299| = 83.

**Square-DAG.** S ⊆ Z/mZ such that the digraph on S with arcs x → y whenever
y − x ∈ Q_m is acyclic. Acyclicity forces antisymmetry, since a two-way pair is a
2-cycle; no hypothesis on −1 being a nonresidue is needed.

**Ranking.** A map h₀ : S → {0,…,H₀−1} with h₀(x) > h₀(y) for every arc x → y; call H₀ the
height of the ranking. The reversed longest-path rank is such a map, and it realizes the
minimum H₀ over all rankings; that minimum value is the height of the DAG (the number of
layers, equivalently the longest directed path counted in vertices).

**Ranked block.** A triple (C, h, H) with C ⊆ Z/PZ and h : C → {0,…,H−1} strictly
decreasing along every nonzero square difference mod P: if x ≠ y in C and y − x is a
square mod P, then h(x) > h(y).

**Paley chain** (Krachun, Def. 2). For a prime p ≡ 3 (mod 4), a tuple (s₀,…,s_{t−1}) in
F_p with s_b − s_a a nonzero quadratic residue for all a < b. A Paley chain is a
square-DAG whose digraph is a transitive tournament, so its height equals its length t.

**Valuations.** For a nonzero integer d, v_m(d) := max{j : m^j | d}; for square-free
m = q₁⋯q_k this equals min_l v_{q_l}(d). For a nonzero class d in Z/m^(2e)Z, v_m(d) is
well defined and < 2e, computed on any representative.

## Lemma A (composite even-digit lift) — the one new lemma

**Statement.** Let m ≥ 2 be square-free, let S be a square-DAG on Z/mZ with ranking h₀ of
height H₀ and |S| = t, and let e ≥ 1. Put

```
C(m,S,e) := { x = Σ_{j=0}^{2e−1} x_j m^j : 0 ≤ x_j < m, x_{2j} ∈ S for 0 ≤ j ≤ e−1 }
            ⊆ Z/m^(2e)Z,        |C(m,S,e)| = (mt)^e,

h(x) := Σ_{j=0}^{e−1} h₀(x_{2j}) · H₀^(e−1−j)  ∈ {0,…,H₀^e − 1}.
```

Then for all x ≠ y in C with y − x ≡ z² (mod m^(2e)) for some integer z and y − x ≠ 0,
one has h(x) > h(y). That is, (C, h, H₀^e) is a ranked block on Z/m^(2e)Z of size (mt)^e.

**Proof.**

*Step 0 (setup).* Let x ≠ y in C and let d := (y − x) mod m^(2e) satisfy d ≡ z² (mod
m^(2e)) with d ≠ 0. Let r be the least base-m position at which the digit strings of x
and y differ. Both are strings of 2e digits, so r ≤ 2e−1 automatically. As integers,
y − x = Σ_{l ≥ r} (y_l − x_l) m^l with y_r ≠ x_r, so m^r | (y − x) and m^(r+1) ∤ (y − x);
the same holds for d = (y − x) + κm^(2e) with κ ∈ {0,1}, since r + 1 ≤ 2e gives
m^(r+1) | m^(2e). Hence m^r | d, m^(r+1) ∤ d, that is r = v_m(d). Step 2 sharpens this to
r even and r ≤ 2e−2.

*Step 1 (leading digit, no borrows).* Every term with l > r contributes a multiple of m to
(y − x)/m^r, so (y − x)/m^r ≡ y_r − x_r (mod m); and d/m^r ≡ (y − x)/m^r (mod m^(2e−r))
because κm^(2e)/m^r ≡ 0. The leading digit is therefore

```
δ := (d/m^r) mod m ≡ y_r − x_r (mod m),   δ ≠ 0.
```

*Step 2 (the valuation of a nonzero square residue is even, and r ≤ 2e−2).* Fix a prime
q_l | m and set v_l := v_{q_l}(z). Write d = z² + λm^(2e) for an integer λ. Then:

- if 2v_l < 2e, then v_{q_l}(z²) = 2v_l < 2e ≤ v_{q_l}(λm^(2e)), so v_{q_l}(d) = 2v_l,
  which is **even**; call such a coordinate *uncapped*;
- if 2v_l ≥ 2e, then v_{q_l}(d) ≥ 2e and no parity information is available; call such a
  coordinate *capped*.

Since d ≠ 0 in Z/m^(2e)Z, not every coordinate can have v_{q_l}(d) ≥ 2e, so at least one
coordinate is uncapped, and

```
r = v_m(d) = min_l v_{q_l}(d) = min over uncapped l of 2v_l,
```

a minimum of even numbers: the capped coordinates all have v_{q_l}(d) ≥ 2e and cannot
achieve the minimum, which is < 2e. Hence r = 2j is even with 0 ≤ j ≤ e−1.

Square-freeness is essential here. For m = Π q_l^(a_l) with a repeated prime factor,
v_m(d) = min_l ⌊v_{q_l}(d)/a_l⌋ and evenness fails: take m = 9 and d = 9 = 3², where
v_9(d) = 1 is odd.

*Step 3 (global divisibility m^j | z).* Every coordinate satisfies v_{q_l}(z²) ≥ 2j. For
uncapped l this reads 2v_l ≥ r = 2j, since otherwise v_{q_l}(d) = 2v_l < r would
contradict r being the minimum; for capped l it holds because 2v_l ≥ 2e ≥ 2j + 2. Hence
v_{q_l}(z) ≥ j for every l, and by square-freeness m^j | z. Put u := z/m^j ∈ Z.

*Step 4 (the leading digit is a nonzero square mod m).* From
d = z² + λm^(2e) = m^(2j)(u² + λm^(2e−2j)) we get

```
d/m^(2j) ≡ u² (mod m^(2e−2j)),   with 2e − 2j ≥ 2.
```

Reducing modulo m and combining with Step 1: δ ≡ u² (mod m) and δ ≠ 0, so **δ ∈ Q_m**.
Here u need not be a unit modulo m, so δ may be a non-unit square, zero in some CRT
coordinates. This case occurs for genuine differences of the certificates below, which is
why Q_m must be the full image of squaring.

*Step 5 (rank drop).* The first differing position r = 2j is even, so x_{2j}, y_{2j} ∈ S,
and δ ≡ y_{2j} − x_{2j} (mod m) with δ ∈ Q_m gives an arc x_{2j} → y_{2j}, hence
h₀(x_{2j}) > h₀(y_{2j}), a drop of at least 1. All even positions 2j′ < 2j carry equal
digits and contribute equally to h. Therefore

```
h(x) − h(y) = [h₀(x_{2j}) − h₀(y_{2j})]·H₀^(e−1−j)
              + Σ_{j′ > j} [h₀(x_{2j′}) − h₀(y_{2j′})]·H₀^(e−1−j′)
            ≥ H₀^(e−1−j) − (H₀ − 1)·Σ_{j′ > j} H₀^(e−1−j′)
            = H₀^(e−1−j) − (H₀^(e−1−j) − 1) = 1 > 0.   ∎
```

**Remark 1 (the unit-only variant is false).** Suppose the arc set were taken to be the
unit squares mod m only. Let m = 15, whose unit squares are {1, 4}. Then S = {0, 1, 6} is
acyclic for unit arcs — the only such arc is 0 → 1 — and h₀(0) = 1, h₀(1) = 0, h₀(6) = 1
is a valid ranking for that arc set. Lift with e = 1: x = 0 and y = 36 = 6 + 2·15 both lie
in C, and y − x = 36 = 6² is a square modulo 225 with v_15 = 0 and leading digit 6, a
non-unit square mod 15 (the full square set mod 15 is {1, 4, 6, 9, 10}). But
h(x) = 1 ≤ 1 = h(y), so the lifted ranking fails, and Lemma B applied to it would
manufacture a false SDF set. The definition Q_m = image of squaring minus 0 is therefore a
hypothesis of the lemma.

**Remark 2 (what differs from the prime case).** Four points, and nothing else.
(1) In Step 2, for prime p the capped case collapses, since a capped single coordinate
forces d ≡ 0; for composite m a coordinate can hit the cap while the difference stays
nonzero, so evenness must come from the minimum over uncapped coordinates.
(2) In the prime case p^j | z is immediate from v_p(d) = 2j = 2·v_p(z); for composite m the
divisibility must be assembled coordinate by coordinate, the capped coordinates included.
Step 3 is the composite form of the "n^(2j) | z², hence n^j | z" step inside Krachun's
Lemma 4.
(3) In Steps 4 and 5 the leading digit is automatically a unit square for prime p, and may
be a non-unit square for composite m; transplanting the phrase "nonzero quadratic residue
modulo p" verbatim would produce a false lemma.
(4) Krachun extracts the order from his chain condition (2.1) — every forward difference
along the chain a nonzero quadratic residue — together with −1 being a nonresidue mod p,
which forces b > a; here that is replaced by "acyclicity yields a ranking", so p ≡ 3 (mod 4)
is not needed in any form, and the height t^e becomes H₀^e.
Everything else — the digit representation, the borrow-free leading digit, the
lexicographic descent, the size count — is Krachun's mechanism verbatim.

## Lemma B (= Krachun, Lemma 4) — used as published

**Statement.** Let P = n² be a perfect square, n any positive integer, with no primality
or square-freeness hypothesis, and let (C, h, H) be a ranked block on Z/PZ. Then for every
L ≥ 1 there is a square-difference-free A_L ⊆ {1,…,(PH)^L} with |A_L| = |C|^L.

*Mechanism, in one sentence:* base-P words (x₀,…,x_{L−1}) ∈ C^L give X = Σ x̄_j P^j, where
x̄_j ∈ {0,…,P−1} is the representative of x_j, with
rank h_L(X) = Σ h(x_j) H^(L−1−j), and B_L = {X + P^L·h_L(X)} works, because a positive
square difference in B_L would force h_L not to decrease along its own reduction mod P^L,
contradicting the strict decrease. For the proof see Krachun, Lemma 4. Our
P = Π m_i^(2e_i) = (Π m_i^(e_i))² satisfies the hypothesis; nothing needs extending.

## Lemma C (= Krachun, Lemma 5) — used as published

**Statement.** For 1 ≤ i ≤ ℓ let P_i be pairwise coprime perfect squares and (C_i, h_i, H_i)
ranked blocks on Z/P_iZ. Under the CRT identification, C = Π C_i ⊆ Z/PZ with P = Π P_i and
h(x₁,…,x_ℓ) = Σ h_i(x_i) is a ranked block of height H = 1 + Σ (H_i − 1).

*Mechanism, in one sentence:* the reduction of a square mod P is a square mod each P_i,
possibly 0; a zero coordinate leaves its rank unchanged, a nonzero one drops it strictly,
and at least one is nonzero. For the proof see Krachun, Lemma 5. The statement never
mentions chains or primes, so it accepts arbitrary ranked blocks as given.

## The pool

Eleven blocks, all moduli pairwise coprime. Krachun's chain at p = 23 is omitted because
23 | 299.

### Nine Paley chains (Krachun's chains); for these, (m, t, H₀) = (p, t, t)

| p | chain | t |
|---|---|---|
| 3 | (0, 1) | 2 |
| 7 | (0, 4, 1) | 3 |
| 11 | (0, 3, 1, 4) | 4 |
| 19 | (0, 5, 11, 9, 16) | 5 |
| 31 | (0, 25, 14, 1, 19, 8, 2) | 7 |
| 43 | (0, 31, 9, 23, 4, 40, 1) | 7 |
| 59 | (0, 49, 15, 7, 16, 19, 35, 36, 5) | 9 |
| 71 | (0, 8, 12, 18, 48, 27, 1, 37, 20) | 9 |
| 103 | (0, 79, 25, 58, 55, 81, 4, 1, 34, 83, 59) | 11 |

Krachun's tenth chain, 23: (0, 18, 1, 3, 4) with t = 5, is used here only to restate his
constant α★.

### Composite block 1: (m, t, H₀) = (235, 17, 11), with 235 = 5·47 square-free

Support with its exhibited ranking, written as *vertex: rank*:

```
0: 10   112: 10   196: 9   224: 9   155: 8   136: 7   67: 6   110: 6
92: 5   189: 5    126: 4   193: 4   22: 3    50: 3    64: 2   73: 1   148: 0
```

Seventeen vertices, ranks 0…10, so height 11. Checking this is a square-DAG with this
ranking is one pass over the 17·16 ordered pairs: for each pair test whether the
difference lies in Q_235, and if so that the rank strictly drops.

### Composite block 2: (m, t, H₀) = (299, 19, 12), with 299 = 13·23 square-free

Support:

```
7, 21, 25, 40, 46, 78, 83, 116, 153, 161, 165, 206, 207, 210, 212, 244, 264, 289, 292
```

Nineteen vertices. The induced digraph under Q_299 is acyclic, and its reversed
longest-path rank has height 12; both are computed directly from the support in
milliseconds.

Both blocks are presented as lower-bound certificates only. The cited heights H₀ = 11 and
12 are the heights of these exhibited certificates and nothing more; no minimality,
maximality, or census claim is made about them or about the pool.

## The exponent chain

Write m_i, t_i, H_i for the modulus, size, and height H₀ of pool block i; after Lemma A
with multiplicity e_i, block i is a ranked block of height H_i^(e_i), which is what Lemma C
receives. Glue across the pool with Lemma C and feed the result to Lemma B at length L.
Then

```
P = Π m_i^(2e_i),   |C| = Π (m_i t_i)^(e_i),   H = 1 + Σ (H_i^(e_i) − 1),
```

and the SDF sets produced by Lemma B have exponent

```
α(e) = [Σ e_i log(m_i t_i)] / [2 Σ e_i log m_i + log(1 + Σ (H_i^(e_i) − 1))].
```

**The limit.** Every pool block has H_i ≥ 2. Allocate e_i(U) := ⌊U / log H_i⌋ for a real
parameter U ≥ max_i log H_i, so that every e_i(U) ≥ 1 and Lemma A applies. Then
e_i(U)·log H_i ∈ (U − log H_i, U], so e_i(U) = U/log H_i + O(1), and

```
max_i H_i^(e_i) ≤ 1 + Σ_i (H_i^(e_i) − 1) ≤ ℓ · max_i H_i^(e_i)   ⟹   log H = U + O(1),
```

with implied constants depending only on the pool. Substituting,

```
numerator   = U · Σ_i log(m_i t_i)/log H_i + O(1),
denominator = U · (1 + 2 Σ_i log m_i/log H_i) + O(1),
```

both Θ(U), so α(e(U)) → α∞ as U → ∞, where

```
α∞ = [Σ_i log(m_i t_i)/log H_i] / [1 + 2 Σ_i log m_i/log H_i].
```

This is Krachun's Theorem 1 computation with log t_i replaced by log H_i; for a Paley
chain H = t, so his formula is the special case.

**Passage to all N.** Fix ρ < α∞ and choose U with α := α(e(U)) > ρ. Write P = P(U),
H = H(U), N_L := (PH)^L, so Lemma B gives SDF A_L ⊆ {1,…,N_L} with
|A_L| = |C|^L = N_L^α. For arbitrary N ≥ PH set L := ⌊log N / log(PH)⌋ ≥ 1. Then N_L ≤ N
and A_L ⊆ {1,…,N} is square-difference-free, so

```
D(N) ≥ |A_L| = N_L^α > (N/(PH))^α = (PH)^(−α) · N^α,
```

whence log D(N)/log N ≥ α − α·log(PH)/log N → α > ρ, so
liminf_{N→∞} log D(N)/log N ≥ ρ. Letting ρ ↗ α∞ proves the Theorem. ∎

**Finite-stage certifiability.** No limit is needed for an unconditional bound. Each finite
U certifies its own exponent with an explicit constant: with P = P(U) and H = H(U),

```
D(N) ≥ (PH)^(−α(e(U))) · N^(α(e(U)))   for all N ≥ PH.
```

The limit is approached from below through these finite constructions: α(e(U)) = 0.744217
at U = 5, 0.751542 at U = 20, 0.753210 at U = 80, 0.753616 at U = 320, gap of order 1/U.

## The value

Evaluating α∞ on the eleven-block pool:

```
α∞ = 0.753741541837329405…      nearest double 0.7537415418373294
```

For comparison, the same closed form over Krachun's ten Paley pairs (his (1.1)):

```
α★ = 0.752796455874514…
```

## Verification

Three independent routes, in ascending effort. None requires trusting the other two.

1. **Run the script.** `python3 verify.py` — standard library only, well under a minute,
   all data inlined in that one file, exit status nonzero on any failure. It rebuilds
   Q_235 and Q_299 from the definition and checks their sizes; checks both certificates
   for size, acyclicity, and longest-path height, validating the exhibited ranking for
   235 and the computed longest-path ranking for 299;
   checks all ten Paley chains for primality, p ≡ 3 (mod 4), distinctness, and every
   forward difference a nonzero quadratic residue; and recomputes α∞ and α★ in
   high-precision decimal. The flag `--lift-demo` additionally builds the e = 1, L = 1
   lifted integer set for the 235 block and brute-checks square-difference-freeness — an
   empirical witness of Lemmas A and B at the smallest scale, a demonstration, not a proof.

2. **Check the proof.** It is one page: Lemma A's proof above, plus Krachun's published
   Lemmas 4 and 5, used here without modification.

3. **Reimplement from scratch.** Everything needed is stated above: the definition of
   Q_m, the two certificates with their supports (and the exhibited ranking for 235),
   the nine chains, the
   allocation e_i(U) = ⌊U/log H_i⌋, and the closed form. verify.py is not an input to the
   mathematics; it only re-checks what is stated above.

A fourth route requires the most machinery and the least trust. The full chain — the
definitions above, Lemma A, Krachun's Lemmas 4 and 5 reproved rather than cited, the
exponent computation, and the Theorem's liminf statement — is formalized in Lean 4 with
Mathlib: [fs-lower-bound-lean](https://github.com/JD-Jones-ASES/fs-lower-bound-lean).
Every theorem there rests on Lean's three standard axioms (propext, Classical.choice,
Quot.sound), and the numeric headline 0.7537 < α∞ is certified by kernel-checked integer
comparisons, with no floating-point or transcendental arithmetic anywhere.

## Scope

No optimality is claimed — not of the two certificates, not of their heights, not of the
pool, and not of the method. The blocks are lower-bound certificates: exhibited objects
that a reader checks in milliseconds. Krachun's §3 discussion of the limit of the approach
is heuristic, restricted to prime moduli, and stated by its author to be without precise
proofs, so it bears on none of the above.

## References

- H. Furstenberg, *Ergodic behavior of diagonal measures and a theorem of Szemerédi on
  arithmetic progressions*, J. Analyse Math. **31** (1977), 204–256.
- A. Sárközy, *On difference sets of sequences of integers I*, Acta Math. Acad. Sci.
  Hungar. **31** (1978), 125–149.
- I. Z. Ruzsa, *Difference sets without squares*, Period. Math. Hungar. **15** (1984),
  205–209.
- R. Beigel, W. Gasarch, *Square-difference-free sets of size Ω(n^0.7334)*,
  arXiv:0804.4892 (2008).
- M. Lewko, *An improved lower bound related to the Furstenberg–Sárközy theorem*,
  Electron. J. Combin. **22** (2015), #P1.32.
- B. Green, M. Sawhney, *New bounds for the Furstenberg–Sárközy theorem*,
  arXiv:2411.17448 (2024).
- Z. Hunter, C. Pohoata, J. Verstraëte, S. Zhang, *Large point-line matchings and small
  Nikodym sets*, arXiv:2601.19879 (2026).
- D. Krachun, *Square-difference-free sets beyond the three-quarter barrier*,
  arXiv:2608.01325 (2026).

## Provenance

AI-generated results with human managing the workflow. Final report generated by Claude
Code (Fable 5) with contributions from Codex (GPT 5.6 Sol) and Grok Build (Grok 4.6).

See [DISCLOSURE.md](DISCLOSURE.md). Released under the MIT License; see
[LICENSE](LICENSE).

A LaTeX version of this note, prepared for arXiv submission, is in
[note/](note/).
