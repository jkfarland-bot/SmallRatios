module

public import SmallRatio.AlongEuclid
public import SmallRatio.Legendre

@[expose] public section

/-!
# The small-ratio formula (Theorem 5.14 of the manuscript, Dedekind-sum form)

For a prime `p` and `0 < h < p`, the terms of Lemma 5.12 with `2 r_j Q_j < p` are exactly the
coprime pairs `(u, v)` with `2uv < p` and `hv ≡ ±u (mod p)`, each once, with sign `+` for `hv ≡ u`
and `-` for `hv ≡ -u` (Legendre's pairing). The other terms are at most `2` each. Hence

  `|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 6n ≤ 12 log₂ p + 6`,

and, summing over a set `H` of residues, `|12 ∑_{h ∈ H} s(h,p) - p S_H(p)| ≤ |H| (12 log₂ p + 6)`.
With the exact formula `M(p,H) = (2π²/p) ∑_{h ∈ H} s(h,p)` (Walum; Louboutin and Munsch), which is
not formalized here, this is the manuscript's `M(p,H) = (π²/6) S_H(p) + O(log p / m)`.
-/

namespace SmallRatio

open Finset

variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp

lemma coprime_p_h : Nat.Coprime p h := Nat.coprime_of_lt_prime hh.ne' hhp hp

/-- For prime `p` the pairs `(r_j, Q_j)` are coprime. -/
lemma coprime_rem_den {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps p h) :
    Nat.Coprime (rem p h j) (den p h j) := by
  have hc := coprime_p_h hp hh hhp
  have e := rem_den_identity hh hhp hc hj
  set d := Nat.gcd (rem p h j) (den p h j)
  have hdp : d ∣ p := by
    rw [← e]
    exact dvd_add (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _)
  rcases (Nat.dvd_prime hp).1 hdp with h1 | h1
  · exact h1
  · exfalso
    have hr := pos_rem_of_le_steps hh hhp hc hj
    have hrh := rem_le_h hh hhp hc hj1 hj
    have hd : d ∣ rem p h j := Nat.gcd_dvd_left _ _
    rw [h1] at hd
    have := Nat.le_of_dvd hr hd
    omega

/-- The small-ratio sum as a sum over the steps of the algorithm. -/
lemma smallRatioSum_eq :
    smallRatioSum p h = ∑ i ∈ Icc 1 (steps p h),
      if 2 * rem p h i * den p h i < p then
        (-1) ^ (i + 1) / ((rem p h i : ℚ) * den p h i) else 0 := by
  have hc := coprime_p_h hp hh hhp
  have : Fact p.Prime := ⟨hp⟩
  unfold smallRatioSum
  rw [← sum_product']
  symm
  apply sum_bij_ne_zero (fun i _ _ => (rem p h i, den p h i))
  · intro i hi hne
    rw [mem_Icc] at hi
    simp only [mem_product, mem_Icc]
    have hr := pos_rem_of_le_steps hh hhp hc hi.2
    have hrh := rem_le_h hh hhp hc hi.1 hi.2
    have hd := den_pos hh hhp hc hi.1 (by omega)
    have hdl := den_le hh hhp hc hi.1 hi.2
    omega
  · intro i hi _ j hj _ hij
    simp only [Prod.mk.injEq] at hij
    rw [mem_Icc] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := rem_strictAnti hh hhp hc hlt hj.2; omega
    · have := rem_strictAnti hh hhp hc hlt hi.2; omega
  · rintro ⟨u, v⟩ huv hne
    simp only [mem_product, mem_Icc] at huv
    by_cases hcond : Nat.Coprime u v ∧ 2 * u * v < p
    · rw [ite_eq_left hcond] at hne
      -- one of the two congruences holds
      have hcong : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((h * v : ℕ) : ZMod p) = (ε : ZMod p) * u := by
        by_cases h1 : ((h * v : ℕ) : ZMod p) = (u : ZMod p)
        · exact ⟨1, Or.inl rfl, by simp [h1]⟩
        · by_cases h2 : ((h * v : ℕ) : ZMod p) = -(u : ZMod p)
          · exact ⟨-1, Or.inr rfl, by simp [h2]⟩
          · rw [ite_eq_right h1, ite_eq_right h2] at hne; simp at hne
      obtain ⟨ε, hε, hcg⟩ := hcong
      have hdvd : (p : ℤ) ∣ (h : ℤ) * v - ε * u := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hcg ⊢
        rw [hcg]; ring
      obtain ⟨j, hj, hju, hjv, hjε⟩ := legendre_pairing hh hhp hc u v huv.1.1 huv.2.1 hcond.1
        hcond.2 ε hε hdvd
      refine ⟨j, hj, ?_, by simp [hju, hjv]⟩
      rw [hju, hjv, ite_eq_left hcond.2]
      have : (u : ℚ) * v ≠ 0 := by
        have : (u : ℚ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
        have : (v : ℚ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
        positivity
      rw [div_ne_zero_iff]
      exact ⟨by simp, this⟩
    · rw [ite_eq_right hcond] at hne; exact absurd rfl hne
  · intro i hi hne
    rw [mem_Icc] at hi
    have hsmall : 2 * rem p h i * den p h i < p := by
      by_contra hs; rw [ite_eq_right hs] at hne; exact hne rfl
    rw [ite_eq_left hsmall]
    have hcop := coprime_rem_den hp hh hhp hi.1 hi.2
    simp only
    rw [ite_eq_left ⟨hcop, hsmall⟩]
    -- the congruence `h Q_i ≡ (-1)^{i+1} r_i`
    have hcg := den_congr (k := p) (h := h) i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hcg
    push_cast at hcg
    have hcg' : ((h * den p h i : ℕ) : ZMod p) = (-1) ^ (i + 1) * (rem p h i : ZMod p) := by
      push_cast; linear_combination hcg
    have hr := pos_rem_of_le_steps hh hhp hc hi.2
    -- `r ≢ -r`
    have hne2 : (rem p h i : ZMod p) ≠ -(rem p h i : ZMod p) := by
      intro heq
      have h2 : ((2 * rem p h i : ℕ) : ZMod p) = 0 := by push_cast; linear_combination heq
      rw [ZMod.natCast_eq_zero_iff] at h2
      have := Nat.le_of_dvd (by omega) h2
      have hd := den_pos hh hhp hc hi.1 (by omega)
      have : 2 * rem p h i ≤ 2 * rem p h i * den p h i := Nat.le_mul_of_pos_right _ hd
      omega
    rcases Nat.even_or_odd i with he | ho
    · have hs : (-1 : ZMod p) ^ (i + 1) = -1 := by rw [pow_succ, he.neg_one_pow]; ring
      have hs' : (-1 : ℚ) ^ (i + 1) = -1 := by rw [pow_succ, he.neg_one_pow]; ring
      rw [hs, neg_one_mul] at hcg'
      rw [ite_eq_right (by rw [hcg']; exact fun h => hne2 h.symm), ite_eq_left hcg', hs']
      ring
    · have hs : (-1 : ZMod p) ^ (i + 1) = 1 := by rw [pow_succ, ho.neg_one_pow]; ring
      have hs' : (-1 : ℚ) ^ (i + 1) = 1 := by rw [pow_succ, ho.neg_one_pow]; ring
      rw [hs, one_mul] at hcg'
      rw [ite_eq_left hcg', ite_eq_right (by rw [hcg']; exact hne2), hs']
      ring

/-- **The small-ratio formula for one residue.**
`|12 s(h,p) - p ∑ ([hv ≡ u] - [hv ≡ -u])/(uv)| ≤ 6n`. -/
theorem small_ratio_steps :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 6 * steps p h := by
  have hc := coprime_p_h hp hh hhp
  have h1 := dedekind_along_euclid hh hhp hc
  set n := steps p h
  set A := ∑ i ∈ Icc 1 n, (-1) ^ (i + 1) * ((p : ℚ) / ((rem p h i : ℚ) * den p h i))
  have h2 : |A - p * smallRatioSum p h| ≤ 2 * n := by
    rw [smallRatioSum_eq hp hh hhp, mul_sum, ← sum_sub_distrib]
    calc |∑ i ∈ Icc 1 n, ((-1) ^ (i + 1) * ((p : ℚ) / ((rem p h i : ℚ) * den p h i)) -
            p * (if 2 * rem p h i * den p h i < p then
              (-1) ^ (i + 1) / ((rem p h i : ℚ) * den p h i) else 0))|
        ≤ ∑ i ∈ Icc 1 n, |(-1) ^ (i + 1) * ((p : ℚ) / ((rem p h i : ℚ) * den p h i)) -
            p * (if 2 * rem p h i * den p h i < p then
              (-1) ^ (i + 1) / ((rem p h i : ℚ) * den p h i) else 0)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Icc 1 n, (2 : ℚ) := by
          apply sum_le_sum
          intro i hi
          rw [mem_Icc] at hi
          by_cases hs : 2 * rem p h i * den p h i < p
          · rw [ite_eq_left hs, mul_div_assoc', mul_comm (p : ℚ), div_mul_eq_mul_div, sub_self, abs_zero]
            norm_num
          · rw [ite_eq_right hs, mul_zero, sub_zero, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
            have hr := pos_rem_of_le_steps hh hhp hc hi.2
            have hd := den_pos hh hhp hc hi.1 (by omega)
            have hpos : (0 : ℚ) < (rem p h i : ℚ) * den p h i := by positivity
            rw [abs_of_nonneg (by positivity), div_le_iff₀ hpos]
            have : (p : ℚ) ≤ 2 * rem p h i * den p h i := by exact_mod_cast (not_lt.1 hs)
            linarith
      _ = 2 * n := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  calc |12 * dedekindSum h p - p * smallRatioSum p h|
      = |(12 * dedekindSum h p - A) + (A - p * smallRatioSum p h)| := by ring_nf
    _ ≤ |12 * dedekindSum h p - A| + |A - p * smallRatioSum p h| := abs_add_le _ _
    _ ≤ 4 * n + 2 * n := add_le_add h1 h2
    _ = 6 * n := by ring

/-- **The small-ratio formula for one residue**, with `n ≤ 2 log₂ p + 1`. -/
theorem small_ratio_element :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 12 * Nat.log 2 p + 6 := by
  have hc := coprime_p_h hp hh hhp
  have h1 := small_ratio_steps hp hh hhp
  have h2 := steps_le_log hh hhp hc
  have : (6 : ℚ) * steps p h ≤ 12 * Nat.log 2 p + 6 := by
    have : (steps p h : ℚ) ≤ 2 * Nat.log 2 p + 1 := by exact_mod_cast h2
    linarith
  linarith

end SmallRatio
