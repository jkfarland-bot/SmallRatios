module

public import SmallRatio

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `SmallRatio/`. The definitions used in the statements come from
`SmallRatio/Defs.lean` and are compared with the copies in `Challenge.lean`.
-/

namespace SmallRatio

open Finset

section Statements

/-- **Dedekind reciprocity.** For coprime positive `h`, `k`:
`s(h,k) + s(k,h) = (h/k + k/h + 1/(hk))/12 - 1/4`. -/
theorem reciprocity (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k + dedekindSum k h =
      ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4 :=
  dedekind_reciprocity h k hh hk hc

/-- **Euclid's algorithm.** For `0 < h < k` coprime, with `r_j = rem k h j` and `n = steps k h`:
`r_n = 1`, `r_j ≥ 2` for `j < n`, and `r` decreases strictly on `[0, n]`. -/
theorem euclid_terminates {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    rem k h (steps k h) = 1 ∧ (∀ j < steps k h, 2 ≤ rem k h j) ∧
      ∀ i j, i < j → j ≤ steps k h → rem k h j < rem k h i :=
  ⟨rem_steps hh hhk hc, fun _ hj => two_le_rem_of_lt_steps hj,
    fun _ _ hij hj => rem_strictAnti hh hhk hc hij hj⟩

/-- **The identity `r_{j-1} q_{j-1} + r_j q_{j-2} = k`** of the manuscript, with `den k h j = q_{j-1}`:
`r_j Q_{j+1} + r_{j+1} Q_j = k` for `j ≤ n`. -/
theorem euclid_identity {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    ∀ j ≤ steps k h, rem k h j * den k h (j + 1) + rem k h (j + 1) * den k h j = k :=
  fun _ hj => rem_den_identity hh hhk hc hj

/-- **The congruence `h q_{j-1} ≡ (-1)^{j+1} r_j (mod k)`**, for every `j`. -/
theorem euclid_congruence (k h j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j :=
  den_congr j

/-- **The length of the algorithm:** `n ≤ 2 log₂ k + 1`. -/
theorem euclid_length {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    steps k h ≤ 2 * Nat.log 2 k + 1 :=
  steps_le_log hh hhk hc

/-- **Dedekind sums along Euclid's algorithm** (manuscript, Lemma 5.12):
`12 s(h,k) = ∑_{j=1}^n (-1)^{j+1} k/(r_j q_{j-1}) + E` with `|E| ≤ 4n`. -/
theorem along_euclid {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    |12 * dedekindSum h k - ∑ i ∈ Icc 1 (steps k h),
        (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| ≤ 4 * steps k h :=
  dedekind_along_euclid hh hhk hc

/-- **Legendre's pairing** (manuscript, Lemma 5.13). If `u, v ≥ 1` are coprime, `uv < k/2` and
`hv ≡ εu (mod k)` with `ε = ±1`, then `(u, v) = (r_j, q_{j-1})` and `ε = (-1)^{j+1}` for some `1 ≤ j ≤ n`. -/
theorem pairing {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
    (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : Nat.Coprime u v) (hsmall : 2 * u * v < k)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hcong : (k : ℤ) ∣ (h : ℤ) * v - ε * u) :
    ∃ j ∈ Icc 1 (steps k h), rem k h j = u ∧ den k h j = v ∧ ε = (-1) ^ (j + 1) :=
  legendre_pairing hh hhk hc u v hu hv huv hsmall ε hε hcong

/-- For a prime modulus the pairs `(r_j, q_{j-1})`, `1 ≤ j ≤ n`, are coprime. -/
theorem pairs_coprime {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    ∀ j, 1 ≤ j → j ≤ steps p h → Nat.Coprime (rem p h j) (den p h j) :=
  fun _ hj1 hj => coprime_rem_den hp hh hhp hj1 hj

/-- **The small-ratio formula for one residue**, with the number of steps:
`|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 6n`, the sum over coprime `u, v ≥ 1` with `uv < p/2`. -/
theorem small_ratio {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 6 * steps p h :=
  small_ratio_steps hp hh hhp

/-- **The small-ratio formula for one residue:**
`|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 12 log₂ p + 6`. -/
theorem small_ratio_log {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 12 * Nat.log 2 p + 6 :=
  small_ratio_element hp hh hhp

/-- Summing the small-ratio sums over a set `H` of residues gives `S_H(p)`. -/
theorem sum_over_set {p : ℕ} (hp : p.Prime) (H : Finset (ZMod p)) :
    ∑ x ∈ H, smallRatioSum p x.val = subgroupSmallRatio p H :=
  sum_smallRatioSum hp H

/-- **The small-ratio formula** (manuscript, Theorem 5.14, Dedekind-sum form). For every set `H` of
residues modulo a prime `p`, in particular every subgroup of odd order:
`|12 ∑_{h ∈ H} s(h,p) - p S_H(p)| ≤ |H| (12 log₂ p + 6)`. -/
theorem small_ratio_subgroup {p : ℕ} (hp : p.Prime) (H : Finset (ZMod p)) :
    |12 * ∑ x ∈ H, dedekindSum x.val p - p * subgroupSmallRatio p H| ≤
      H.card * (12 * Nat.log 2 p + 6) :=
  small_ratio_set hp H

end Statements

end SmallRatio
