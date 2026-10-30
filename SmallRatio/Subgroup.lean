module

public import SmallRatio.Main

@[expose] public section

/-!
# Sums over a set of residues

For a set `H` of residues modulo a prime `p` (for instance a subgroup of `(ℤ/p)ˣ` of odd order),
`∑_{h ∈ H} T(h) = S_H(p)`, where `T(h)` is the small-ratio sum of `h`; hence

  `|12 ∑_{h ∈ H} s(h,p) - p S_H(p)| ≤ |H| (12 log₂ p + 6)`.
-/

namespace SmallRatio

open Finset

variable {p : ℕ}

lemma dedekindSum_zero_left (k : ℕ) : dedekindSum 0 k = 0 := by
  simp [dedekindSum, sawtooth]

lemma smallRatioSum_zero (hp : p.Prime) : smallRatioSum p 0 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold smallRatioSum
  apply sum_eq_zero
  intro u hu
  apply sum_eq_zero
  intro v hv
  rw [mem_Icc] at hu hv
  by_cases hcond : Nat.Coprime u v ∧ 2 * u * v < p
  · rw [ite_eq_left hcond]
    have hu' : (u : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      have : u ≤ 2 * u * v := by nlinarith [hv.1]
      omega
    have h1 : ¬ (((0 * v : ℕ) : ZMod p) = (u : ZMod p)) := by
      rw [zero_mul, Nat.cast_zero]; exact fun h => hu' h.symm
    have h2 : ¬ (((0 * v : ℕ) : ZMod p) = -(u : ZMod p)) := by
      rw [zero_mul, Nat.cast_zero]; exact fun h => hu' (neg_eq_zero.1 h.symm)
    rw [ite_eq_right h1, ite_eq_right h2]; simp
  · rw [ite_eq_right hcond]

lemma sum_smallRatioSum (hp : p.Prime) (H : Finset (ZMod p)) :
    ∑ x ∈ H, smallRatioSum p x.val = subgroupSmallRatio p H := by
  have : Fact p.Prime := ⟨hp⟩
  unfold smallRatioSum subgroupSmallRatio
  rw [sum_comm]
  refine sum_congr rfl fun u hu => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v hv => ?_
  by_cases hcond : Nat.Coprime u v ∧ 2 * u * v < p
  · simp only [ite_eq_left hcond]
    rw [mem_Icc] at hv hu
    have hv0 : (v : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      have : v ≤ 2 * u * v := by nlinarith [hu.1]
      omega
    have key1 : ∀ x : ZMod p, ((x.val * v : ℕ) : ZMod p) = (u : ZMod p) ↔
        x = (u : ZMod p) * (v : ZMod p)⁻¹ := by
      intro x
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, eq_mul_inv_iff_mul_eq₀ hv0]
    have key2 : ∀ x : ZMod p, ((x.val * v : ℕ) : ZMod p) = -(u : ZMod p) ↔
        x = -((u : ZMod p) * (v : ZMod p)⁻¹) := by
      intro x
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, neg_mul_eq_neg_mul, eq_mul_inv_iff_mul_eq₀ hv0]
    rw [← sum_div, sum_sub_distrib]
    congr 2
    · simp_rw [key1]; rw [sum_ite_eq']
    · simp_rw [key2]; rw [sum_ite_eq']
  · simp only [ite_eq_right hcond, sum_const_zero]

/-- **The small-ratio formula over a set of residues.**
`|12 ∑_{h ∈ H} s(h,p) - p S_H(p)| ≤ |H| (12 log₂ p + 6)`. -/
theorem small_ratio_set (hp : p.Prime) (H : Finset (ZMod p)) :
    |12 * ∑ x ∈ H, dedekindSum x.val p - p * subgroupSmallRatio p H| ≤
      H.card * (12 * Nat.log 2 p + 6) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← sum_smallRatioSum hp, mul_sum, mul_sum, ← sum_sub_distrib]
  calc |∑ x ∈ H, (12 * dedekindSum x.val p - p * smallRatioSum p x.val)|
      ≤ ∑ x ∈ H, |12 * dedekindSum x.val p - p * smallRatioSum p x.val| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ H, ((12 * Nat.log 2 p + 6 : ℕ) : ℚ) := by
        apply sum_le_sum
        intro x _
        by_cases hx : x = 0
        · subst hx
          rw [ZMod.val_zero, dedekindSum_zero_left, smallRatioSum_zero hp]
          simp only [mul_zero, sub_zero, abs_zero]
          positivity
        · have h1 := small_ratio_element hp (Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).2 hx))
            (ZMod.val_lt x)
          push_cast; exact h1
    _ = H.card * (12 * Nat.log 2 p + 6) := by
        rw [sum_const, nsmul_eq_mul]; push_cast; ring

end SmallRatio
