module

public import Mathlib

@[expose] public section

/-!
# Definitions

* `sawtooth x = ((x))`, equal to `x - ⌊x⌋ - 1/2` if `x ∉ ℤ` and to `0` if `x ∈ ℤ`.
* `dedekindSum h k = s(h,k) = ∑_{r mod k} ((r/k)) ((hr/k))`. These two definitions are those of
  DedekindSubgroups (doi:10.5281/zenodo.23424615), copied verbatim.
* `rem k h j = r_j` and `den k h j = q_{j-1}`: Euclid's algorithm on `(k, h)`, with `r_0 = k`,
  `r_1 = h`, `r_{j+2} = r_j mod r_{j+1}`, and `q_{-1} = 0`, `q_0 = 1`, `q_{j+1} = a_{j+1} q_j + q_{j-1}`
  where `a_{j+1} = ⌊r_j / r_{j+1}⌋`. The shift `den k h j = q_{j-1}` makes the indices agree with
  those of `rem`.
* `steps k h = n`, the least `j` with `r_j ≤ 1` (capped at `k + 1`); for `0 < h < k` coprime,
  `r_n = 1`.
* `smallRatioSum p h = ∑ ([hv ≡ u] - [hv ≡ -u]) / (uv)` over the coprime pairs `u, v ≥ 1` with
  `uv < p/2`.
* `subgroupSmallRatio p H = S_H(p) = ∑ (1_H(u/v) - 1_H(-u/v)) / (uv)` over the same pairs, for a
  set `H` of residues modulo `p`.
-/

namespace SmallRatio

open Finset

/-- The sawtooth function `((x))`: `x - ⌊x⌋ - 1/2` if `x ∉ ℤ`, and `0` if `x ∈ ℤ`. -/
noncomputable def sawtooth (x : ℚ) : ℚ := if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

/-- The Dedekind sum `s(h,k) = ∑_{r mod k} ((r/k)) ((hr/k))`. -/
noncomputable def dedekindSum (h k : ℕ) : ℚ :=
  ∑ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k)

/-- The remainders of Euclid's algorithm on `(k, h)`: `r_0 = k`, `r_1 = h`,
`r_{j+2} = r_j mod r_{j+1}`. -/
def rem (k h : ℕ) : ℕ → ℕ
  | 0 => k
  | 1 => h
  | j + 2 => rem k h j % rem k h (j + 1)

/-- The denominators of the convergents, shifted: `den k h j = q_{j-1}`, so `den k h 0 = 0`,
`den k h 1 = 1` and `den k h (j+2) = ⌊r_j / r_{j+1}⌋ den k h (j+1) + den k h j`. -/
def den (k h : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => rem k h j / rem k h (j + 1) * den k h (j + 1) + den k h j

/-- The length `n` of Euclid's algorithm: the least `j` with `r_j ≤ 1`, capped at `k + 1`. -/
def steps (k h : ℕ) : ℕ := Nat.find (⟨k + 1, Or.inr rfl⟩ : ∃ j, rem k h j ≤ 1 ∨ j = k + 1)

/-- The small-ratio sum of one residue `h` modulo `p`:
`∑ ([hv ≡ u] - [hv ≡ -u]) / (uv)` over coprime `u, v ≥ 1` with `2uv < p`. -/
noncomputable def smallRatioSum (p h : ℕ) : ℚ :=
  ∑ u ∈ Icc 1 p, ∑ v ∈ Icc 1 p,
    if Nat.Coprime u v ∧ 2 * u * v < p then
      ((if ((h * v : ℕ) : ZMod p) = (u : ZMod p) then 1 else 0) -
        (if ((h * v : ℕ) : ZMod p) = -(u : ZMod p) then 1 else 0)) / ((u : ℚ) * v)
    else 0

/-- `S_H(p) = ∑ (1_H(u/v) - 1_H(-u/v)) / (uv)` over coprime `u, v ≥ 1` with `2uv < p`, where
`u/v = u v⁻¹` in `ZMod p`. -/
noncomputable def subgroupSmallRatio (p : ℕ) (H : Finset (ZMod p)) : ℚ :=
  ∑ u ∈ Icc 1 p, ∑ v ∈ Icc 1 p,
    if Nat.Coprime u v ∧ 2 * u * v < p then
      ((if (u : ZMod p) * (v : ZMod p)⁻¹ ∈ H then 1 else 0) -
        (if -((u : ZMod p) * (v : ZMod p)⁻¹) ∈ H then 1 else 0)) / ((u : ℚ) * v)
    else 0

end SmallRatio
