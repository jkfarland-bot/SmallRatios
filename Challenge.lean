module

public import Mathlib

public section

/-!
# The small-ratio formula: statements

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development
in `SmallRatio/`. The numbering follows the manuscript (Farland, *Mean squares of Dirichlet
`L`-functions at `s = 1` over characters of fixed order and over subgroups*, Section 5).

Notation: `s(h,k) = dedekindSum h k`; `r_j = rem k h j` and `q_{j-1} = den k h j` are the remainders
and the convergent denominators of Euclid's algorithm on `(k, h)`; `n = steps k h` is its length;
`S_H(p) = subgroupSmallRatio p H`.
-/

namespace SmallRatio

open Finset

/-! ### Definitions -/

section Defs

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

end Defs

/-! ### Statements -/

section Statements

/-- **Dedekind reciprocity.** For coprime positive `h`, `k`:
`s(h,k) + s(k,h) = (h/k + k/h + 1/(hk))/12 - 1/4`. -/
theorem reciprocity (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k + dedekindSum k h =
      ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4 := by
  sorry

/-- **Euclid's algorithm.** For `0 < h < k` coprime, with `r_j = rem k h j` and `n = steps k h`:
`r_n = 1`, `r_j ≥ 2` for `j < n`, and `r` decreases strictly on `[0, n]`. -/
theorem euclid_terminates {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    rem k h (steps k h) = 1 ∧ (∀ j < steps k h, 2 ≤ rem k h j) ∧
      ∀ i j, i < j → j ≤ steps k h → rem k h j < rem k h i := by
  sorry

/-- **The identity `r_{j-1} q_{j-1} + r_j q_{j-2} = k`** of the manuscript, with `den k h j = q_{j-1}`:
`r_j Q_{j+1} + r_{j+1} Q_j = k` for `j ≤ n`. -/
theorem euclid_identity {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    ∀ j ≤ steps k h, rem k h j * den k h (j + 1) + rem k h (j + 1) * den k h j = k := by
  sorry

/-- **The congruence `h q_{j-1} ≡ (-1)^{j+1} r_j (mod k)`**, for every `j`. -/
theorem euclid_congruence (k h j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j := by
  sorry

/-- **The length of the algorithm:** `n ≤ 2 log₂ k + 1`. -/
theorem euclid_length {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    steps k h ≤ 2 * Nat.log 2 k + 1 := by
  sorry

/-- **Dedekind sums along Euclid's algorithm** (manuscript, Lemma 5.12):
`12 s(h,k) = ∑_{j=1}^n (-1)^{j+1} k/(r_j q_{j-1}) + E` with `|E| ≤ 4n`. -/
theorem along_euclid {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    |12 * dedekindSum h k - ∑ i ∈ Icc 1 (steps k h),
        (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| ≤ 4 * steps k h := by
  sorry

/-- **Legendre's pairing** (manuscript, Lemma 5.13). If `u, v ≥ 1` are coprime, `uv < k/2` and
`hv ≡ εu (mod k)` with `ε = ±1`, then `(u, v) = (r_j, q_{j-1})` and `ε = (-1)^{j+1}` for some `1 ≤ j ≤ n`. -/
theorem pairing {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
    (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : Nat.Coprime u v) (hsmall : 2 * u * v < k)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hcong : (k : ℤ) ∣ (h : ℤ) * v - ε * u) :
    ∃ j ∈ Icc 1 (steps k h), rem k h j = u ∧ den k h j = v ∧ ε = (-1) ^ (j + 1) := by
  sorry

/-- For a prime modulus the pairs `(r_j, q_{j-1})`, `1 ≤ j ≤ n`, are coprime. -/
theorem pairs_coprime {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    ∀ j, 1 ≤ j → j ≤ steps p h → Nat.Coprime (rem p h j) (den p h j) := by
  sorry

/-- **The small-ratio formula for one residue**, with the number of steps:
`|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 6n`, the sum over coprime `u, v ≥ 1` with `uv < p/2`. -/
theorem small_ratio {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 6 * steps p h := by
  sorry

/-- **The small-ratio formula for one residue:**
`|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 12 log₂ p + 6`. -/
theorem small_ratio_log {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 12 * Nat.log 2 p + 6 := by
  sorry

/-- Summing the small-ratio sums over a set `H` of residues gives `S_H(p)`. -/
theorem sum_over_set {p : ℕ} (hp : p.Prime) (H : Finset (ZMod p)) :
    ∑ x ∈ H, smallRatioSum p x.val = subgroupSmallRatio p H := by
  sorry

/-- **The small-ratio formula** (manuscript, Theorem 5.14, Dedekind-sum form). For every set `H` of
residues modulo a prime `p`, in particular every subgroup of odd order:
`|12 ∑_{h ∈ H} s(h,p) - p S_H(p)| ≤ |H| (12 log₂ p + 6)`. -/
theorem small_ratio_subgroup {p : ℕ} (hp : p.Prime) (H : Finset (ZMod p)) :
    |12 * ∑ x ∈ H, dedekindSum x.val p - p * subgroupSmallRatio p H| ≤
      H.card * (12 * Nat.log 2 p + 6) := by
  sorry

end Statements

end SmallRatio
