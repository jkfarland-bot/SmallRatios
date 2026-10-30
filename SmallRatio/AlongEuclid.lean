module

public import SmallRatio.Reciprocity
public import SmallRatio.Euclid

@[expose] public section

/-!
# Dedekind sums along Euclid's algorithm (Lemma 5.12 of the manuscript)

Unrolling reciprocity along the algorithm,

  `12 s(h,k) = ∑_{j=1}^n (-1)^{j+1} (r_{j-1}/r_j + r_j/r_{j-1} + 1/(r_j r_{j-1}) - 3)`,

and `r_{j-1}/r_j = k/(r_j Q_j) - Q_{j-1}/Q_j`. Each remaining term lies in `[-4, -1]`, so

  `|12 s(h,k) - ∑_{j=1}^n (-1)^{j+1} k/(r_j Q_j)| ≤ 4n`.
-/

namespace SmallRatio

open Finset

lemma dedekindSum_mod (h k : ℕ) (hk : 0 < k) : dedekindSum h k = dedekindSum (h % k) k := by
  unfold dedekindSum
  apply sum_congr rfl
  intro r _
  congr 1
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have e : (h : ℚ) = ((h % k : ℕ) : ℚ) + k * ((h / k : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mod_add_div h k).symm
  have e2 : (h : ℚ) * r / k = ((h % k : ℕ) : ℚ) * r / k + (((h / k) * r : ℕ) : ℚ) := by
    rw [e]; push_cast; field_simp
  unfold sawtooth
  rw [e2, Int.fract_add_natCast]

lemma dedekindSum_one (h : ℕ) : dedekindSum h 1 = 0 := by
  simp [dedekindSum, sawtooth]

/-- The reciprocity term `12 (s(r_j, r_{j-1}) + s(r_{j-1}, r_j))`. -/
noncomputable def recipTerm (k h : ℕ) (j : ℕ) : ℚ :=
  (rem k h (j - 1) : ℚ) / rem k h j + (rem k h j : ℚ) / rem k h (j - 1)
    + 1 / ((rem k h j : ℚ) * rem k h (j - 1)) - 3

variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc

lemma telescope {j : ℕ} (hj : j ≤ steps k h) :
    12 * dedekindSum h k = ∑ i ∈ Ico 1 (j + 1), (-1) ^ (i + 1) * recipTerm k h i
      + (-1) ^ j * (12 * dedekindSum (rem k h (j + 1)) (rem k h j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih (by omega), sum_Ico_succ_top (a := 1) (b := j + 1) (by omega)]
    have h0 := pos_rem_of_le_steps hh hhk hc (show j ≤ steps k h by omega)
    have h1 := pos_rem_of_le_steps hh hhk hc hj
    have hg := gcd_rem (k := k) (h := h) j
    rw [hc] at hg
    have hrec := dedekind_reciprocity (rem k h (j + 1)) (rem k h j) h1 h0
      (by rw [Nat.Coprime, Nat.gcd_comm]; exact hg)
    have hmod := dedekindSum_mod (rem k h j) (rem k h (j + 1)) h1
    rw [← rem_add_two] at hmod
    have hR : recipTerm k h (j + 1) = 12 * (dedekindSum (rem k h (j + 1)) (rem k h j) +
        dedekindSum (rem k h j) (rem k h (j + 1))) := by
      rw [hrec]
      unfold recipTerm
      simp only [Nat.add_sub_cancel]
      have : (rem k h j : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
      have : (rem k h (j + 1) : ℚ) ≠ 0 := by exact_mod_cast h1.ne'
      field_simp
      ring
    rw [show j + 1 + 1 = j + 2 by ring, ← hmod, hR]
    ring

lemma twelve_s_eq_sum :
    12 * dedekindSum h k = ∑ i ∈ Icc 1 (steps k h), (-1) ^ (i + 1) * recipTerm k h i := by
  have := telescope hh hhk hc (le_refl (steps k h))
  rw [rem_steps hh hhk hc, dedekindSum_one, mul_zero, mul_zero, add_zero] at this
  rw [this]
  rfl

/-- The error term `e_j = r_{j-1}/r_j - k/(r_j Q_j) + r_j/r_{j-1} + 1/(r_j r_{j-1}) - 3`. -/
lemma recipTerm_eq {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ steps k h) :
    recipTerm k h i = (k : ℚ) / ((rem k h i : ℚ) * den k h i) +
      (-(den k h (i - 1) : ℚ) / den k h i + (rem k h i : ℚ) / rem k h (i - 1)
        + 1 / ((rem k h i : ℚ) * rem k h (i - 1)) - 3) := by
  have e := rem_den_identity hh hhk hc (show i - 1 ≤ steps k h by omega)
  rw [show i - 1 + 1 = i by omega] at e
  have hr : (rem k h i : ℚ) ≠ 0 := by exact_mod_cast (pos_rem_of_le_steps hh hhk hc hi).ne'
  have hd : (den k h i : ℚ) ≠ 0 := by
    have := den_pos hh hhk hc hi1 (by omega); exact_mod_cast (by omega : den k h i ≠ 0)
  have hr' : (rem k h (i - 1) : ℚ) ≠ 0 := by
    exact_mod_cast (pos_rem_of_le_steps hh hhk hc (show i - 1 ≤ steps k h by omega)).ne'
  have eQ : (k : ℚ) = (rem k h (i - 1) : ℚ) * den k h i + (rem k h i : ℚ) * den k h (i - 1) := by
    exact_mod_cast e.symm
  unfold recipTerm
  rw [eQ]
  field_simp
  ring

lemma err_bound {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ steps k h) :
    |(-(den k h (i - 1) : ℚ) / den k h i + (rem k h i : ℚ) / rem k h (i - 1)
        + 1 / ((rem k h i : ℚ) * rem k h (i - 1)) - 3)| ≤ 4 := by
  have hr := pos_rem_of_le_steps hh hhk hc hi
  have hlt := rem_succ_lt hh hhk hc (show i - 1 < steps k h by omega)
  rw [show i - 1 + 1 = i by omega] at hlt
  have hd := den_pos hh hhk hc hi1 (by omega)
  have hmono := den_mono hh hhk hc (show i - 1 ≤ steps k h by omega)
  rw [show i - 1 + 1 = i by omega] at hmono
  have hrq : (0 : ℚ) < rem k h i := by exact_mod_cast hr
  have hlq : (rem k h i : ℚ) < rem k h (i - 1) := by exact_mod_cast hlt
  have hdq : (1 : ℚ) ≤ den k h i := by exact_mod_cast hd
  have hmq : (den k h (i - 1) : ℚ) ≤ den k h i := by exact_mod_cast hmono
  have hd0 : (0 : ℚ) ≤ den k h (i - 1) := by positivity
  have a1 : (den k h (i - 1) : ℚ) / den k h i ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hmq
  have a2 : 0 ≤ (den k h (i - 1) : ℚ) / den k h i := by positivity
  have a3 : (rem k h i : ℚ) / rem k h (i - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hlq.le
  have a4 : 0 ≤ (rem k h i : ℚ) / rem k h (i - 1) := by positivity
  have hprod : (1 : ℚ) ≤ (rem k h i : ℚ) * rem k h (i - 1) := by
    have : (1 : ℚ) ≤ rem k h i := by exact_mod_cast hr
    nlinarith
  have a5 : 1 / ((rem k h i : ℚ) * rem k h (i - 1)) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hprod
  have a6 : 0 ≤ 1 / ((rem k h i : ℚ) * rem k h (i - 1)) := by positivity
  rw [abs_le]
  constructor
  · rw [neg_div]; linarith
  · rw [neg_div]; linarith

/-- **Dedekind sums along Euclid's algorithm.**
`|12 s(h,k) - ∑_{j=1}^n (-1)^{j+1} k/(r_j Q_j)| ≤ 4n`. -/
theorem dedekind_along_euclid :
    |12 * dedekindSum h k - ∑ i ∈ Icc 1 (steps k h),
        (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| ≤ 4 * steps k h := by
  rw [twelve_s_eq_sum hh hhk hc, ← sum_sub_distrib]
  calc |∑ i ∈ Icc 1 (steps k h), ((-1) ^ (i + 1) * recipTerm k h i -
          (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i)))|
      ≤ ∑ i ∈ Icc 1 (steps k h), |(-1) ^ (i + 1) * recipTerm k h i -
          (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Icc 1 (steps k h), (4 : ℚ) := by
        apply sum_le_sum
        intro i hi
        rw [mem_Icc] at hi
        rw [recipTerm_eq hh hhk hc hi.1 hi.2, ← mul_sub, abs_mul, abs_pow, abs_neg, abs_one,
          one_pow, one_mul, add_sub_cancel_left]
        exact err_bound hh hhk hc hi.1 hi.2
    _ = 4 * steps k h := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

end SmallRatio
