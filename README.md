# SmallRatio

Lean 4 / Mathlib formalization of the small-ratio formula for Dedekind sums, from J. S. Farland,
*Mean squares of Dirichlet L-functions at s = 1 over characters of fixed order and over subgroups*
(manuscript, 2026), Section 5.

The companion paper is J. S. Farland, *The small-ratio formula for Dedekind sums, formalized in Lean*
(preprint, Zenodo, 2026; DOI to be added).

For `0 < h < k` coprime let `r_0 = k`, `r_1 = h`, `r_{j+1} = r_{j-1} mod r_j` be the remainders of Euclid's
algorithm, ending at `r_n = 1`, and `q_{-1} = 0`, `q_0 = 1`, `q_j = a_j q_{j-1} + q_{j-2}` the denominators of
the convergents. Write `s(h,k)` for the Dedekind sum. This repository proves:

- **Dedekind reciprocity**, `s(h,k) + s(k,h) = (h/k + k/h + 1/(hk))/12 - 1/4`, from scratch, by counting
  lattice points.
- **Euclid's algorithm:** `r_{j-1} q_{j-1} + r_j q_{j-2} = k`, `h q_{j-1} ≡ (-1)^{j+1} r_j (mod k)` and
  `n ≤ 2 log₂ k + 1`.
- **Dedekind sums along Euclid's algorithm** (Lemma 5.12):
  `|12 s(h,k) - ∑_{j=1}^n (-1)^{j+1} k/(r_j q_{j-1})| ≤ 4n`.
- **Legendre's pairing** (Lemma 5.13): if `u, v ≥ 1` are coprime, `uv < k/2` and `hv ≡ ±u (mod k)`, then
  `(u, v) = (r_j, q_{j-1})` for some `1 ≤ j ≤ n`, with sign `(-1)^{j+1}`.
- **The small-ratio formula** (Theorem 5.14, Dedekind-sum form). For a prime `p` and `0 < h < p`,

  `|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 6n ≤ 12 log₂ p + 6`,

  the sum over the coprime pairs `u, v ≥ 1` with `uv < p/2`. For every set `H` of residues modulo `p`,
  in particular every subgroup of odd order,

  `|12 ∑_{h ∈ H} s(h,p) - p S_H(p)| ≤ |H| (12 log₂ p + 6)`,  `S_H(p) = ∑ (1_H(u/v) - 1_H(-u/v))/(uv)`.

With the exact formula `M(p,H) = (2π²/p) ∑_{h ∈ H} s(h,p)` for the mean square of `L(1,χ)` over the odd
characters trivial on `H` (Walum; Louboutin and Munsch), which is quoted and not formalized, the last
statement is the manuscript's `M(p,H) = (π²/6) S_H(p) + O(log p / m)`, `m` the index of `H`. Here
`log₂` is `Nat.log 2`, the floor of the binary logarithm.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`. The export of `Solution` is accepted by the Lean kernel, nanoda and con-ron.

## Scope, hypotheses and limitations

- **No `L`-functions.** The mean square `M(p,H)` is not defined here. Theorem 5.14 is formalized in its
  Dedekind-sum form, and the bridge, Proposition 5.1 of the manuscript, is quoted.
- **Explicit constants.** `|E| ≤ 4n` in Lemma 5.12, `6n` per residue, and `n ≤ 2 log₂ p + 1` (the manuscript
  states `2 log₂ p + 2`).
- **Generality.** Reciprocity, the Euclid identities, Lemma 5.12 and Lemma 5.13 hold for every modulus `k`.
  The coprimality of the pairs `(r_j, q_{j-1})`, and with it the small-ratio formula, needs `k` prime: for
  `k = 12`, `h = 5` the pair `(r_2, q_1) = (2, 2)` is not coprime. The set `H` is any finite set of
  residues; the manuscript takes subgroups of odd order.
- **Indexing.** `rem k h j = r_j`, and `den k h j = q_{j-1}` is shifted by one so that both sequences have the
  same index. `steps k h = n`.
- **Lemma 5.13** is proved by a lattice argument (consecutive vectors `(r_j, (-1)^{j+1} q_{j-1})` form a
  basis of `{(x, y) : x ≡ hy (mod k)}`) instead of Legendre's theorem on convergents. Uniqueness of `j`
  follows from the strict decrease of `r_j`, part of `euclid_terminates`.
- **Not formalized:** Proposition 5.1; the pointwise approximation through Burgess' bound (Proposition 5.15,
  Theorem 5.16); Corollary 5.18 and the remarks after Theorem 5.14.

## Sources and novelty

Dedekind reciprocity is classical (Rademacher and Grosswald, *Dedekind Sums*, 1972); it was formalized in
Isabelle/HOL by Eberl, Bordg, Paulson and Li (Archive of Formal Proofs, 2025), and is formalized here in Lean
for the first time as far as we know. Lemma 5.12 is a reformulation of the Barkan, Hickerson and Knuth
evaluation of `s(h,k)` through partial quotients, obtained, as by Hall and Huxley (Acta Arith. 63 (1993)),
by iterating reciprocity along the convergents. Lemma 5.13 is Legendre's theorem on convergents (Hardy and
Wright, Theorem 184). The approximation of `12 s(h,k)` by `k/(uv)` near a single fraction of small height is
known (Conrey, Fransen, Klein and Scott, J. Number Theory 56 (1996), Lemma 2; Girstmair, Acta Arith. 109
(2003), Theorem 3(b)). What the manuscript claims is the summed form: all small fractions at once, with
the exact cut `uv < p/2`, an `O(log p)` error, and the subgroup sum `S_H(p)`. For the second moment it is an
unsmoothed, explicit version of the identity (5.3) of Munsch and Shparlinski (Forum Math. 38 (2026)), their
case `k = 1` (there `k` indexes the moment), and it was not found in these sources. Novelty is claimed only relative to them.

## Authorship, AI assistance and licence

The mathematics, the statements and the manuscript are by Joseph S. Farland. The Lean code was drafted
and repaired by Claude (Anthropic) against the manuscript's statements and proofs. The code is released
under the Apache License 2.0 (`LICENSE`); the paper is CC BY 4.0.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface to audit. It restates the definitions exactly as the
  development has them and states the 12 results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `SmallRatio/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the Palomar starter template.
- `check/statements.py` recomputes every formalized statement numerically.

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

| Manuscript | Challenge declaration |
|---|---|
| reciprocity (used in Lemma 5.12) | `reciprocity` |
| the identities before Lemma 5.12 | `euclid_terminates`, `euclid_identity`, `euclid_congruence`, `euclid_length`, `pairs_coprime` |
| Lemma 5.12 | `along_euclid` |
| Lemma 5.13 | `pairing` |
| Theorem 5.14, one residue | `small_ratio`, `small_ratio_log` |
| Theorem 5.14, Dedekind-sum form | `sum_over_set`, `small_ratio_subgroup` |

## Files

| File | Contents |
|---|---|
| `Defs` | `sawtooth` and `dedekindSum` (copied from DedekindSubgroups), `rem`, `den`, `steps`, `smallRatioSum`, `subgroupSmallRatio` |
| `Reciprocity` | Dedekind reciprocity |
| `Euclid` | Euclid's algorithm: termination, identities, length |
| `AlongEuclid` | Lemma 5.12 |
| `Legendre` | Lemma 5.13 |
| `Main` | the small-ratio formula for one residue |
| `Subgroup` | sums over a set of residues |
