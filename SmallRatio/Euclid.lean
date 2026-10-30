module

public import SmallRatio.Defs

@[expose] public section

/-!
# Euclid's algorithm

For `0 < h < k` coprime, with `r_j = rem k h j`, `Q_j = den k h j = q_{j-1}` and `n = steps k h`:

* `r_n = 1`, `r_j ≥ 2` for `j < n`, and `r` is strictly decreasing on `[0, n]`;
* `r_j Q_{j+1} + r_{j+1} Q_j = k` for `j ≤ n` (the manuscript's `r_{j-1} q_{j-1} + r_j q_{j-2} = p`);
* `h Q_j ≡ (-1)^{j+1} r_j (mod k)` for every `j`;
* `1 ≤ Q_j ≤ Q_{j+1}` for `1 ≤ j ≤ n`;
* `2 r_{j+2} < r_j`, hence `n ≤ 2 log₂ k + 1`.
-/

namespace SmallRatio

open Finset

variable {k h : ℕ}

@[simp] lemma rem_zero : rem k h 0 = k := rfl
@[simp] lemma rem_one : rem k h 1 = h := rfl
lemma rem_add_two (j : ℕ) : rem k h (j + 2) = rem k h j % rem k h (j + 1) := rfl
@[simp] lemma den_zero : den k h 0 = 0 := rfl
@[simp] lemma den_one : den k h 1 = 1 := rfl
lemma den_add_two (j : ℕ) :
    den k h (j + 2) = rem k h j / rem k h (j + 1) * den k h (j + 1) + den k h j := rfl

lemma gcd_rem (j : ℕ) : Nat.gcd (rem k h j) (rem k h (j + 1)) = Nat.gcd k h := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [rem_add_two, ← ih, Nat.gcd_comm (rem k h (j + 1)), ← Nat.gcd_rec, Nat.gcd_comm]

lemma rem_add_two_lt (j : ℕ) (hpos : 0 < rem k h (j + 1)) : rem k h (j + 2) < rem k h (j + 1) := by
  rw [rem_add_two]; exact Nat.mod_lt _ hpos

/-- While the remainders stay `≥ 2`, they decrease from `r_1 = h`. -/
lemma rem_le_of_ge_two (j : ℕ) (hge : ∀ i ≤ j + 1, 2 ≤ rem k h i) : rem k h (j + 1) + j ≤ h := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ih (fun i hi => hge i (by omega))
    have h2 : rem k h (j + 1 + 1) < rem k h (j + 1) :=
      rem_add_two_lt (k := k) (h := h) j (by have := hge (j + 1) (by omega); omega)
    omega

lemma exists_rem_le_one : ∃ j ≤ h + 1, rem k h j ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have := rem_le_of_ge_two (k := k) (h := h) h (fun i hi => hcon i hi)
  have := hcon (h + 1) le_rfl
  omega

variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc

omit hh hc in
lemma steps_spec : rem k h (steps k h) ≤ 1 := by
  obtain ⟨j, hj, hj1⟩ := exists_rem_le_one (k := k) (h := h)
  have hle : steps k h ≤ j := Nat.find_min' _ (Or.inl hj1)
  rcases Nat.find_spec (⟨k + 1, Or.inr rfl⟩ : ∃ j, rem k h j ≤ 1 ∨ j = k + 1) with h1 | h1
  · exact h1
  · exfalso; unfold steps at hle; omega

omit hh hhk hc in
lemma two_le_rem_of_lt_steps {j : ℕ} (hj : j < steps k h) : 2 ≤ rem k h j := by
  have := Nat.find_min (⟨k + 1, Or.inr rfl⟩ : ∃ j, rem k h j ≤ 1 ∨ j = k + 1) hj
  push Not at this
  omega

omit hc in
lemma one_le_steps : 1 ≤ steps k h := by
  by_contra h0
  have h0 : steps k h = 0 := by omega
  have := steps_spec hhk
  rw [h0, rem_zero] at this
  omega

lemma rem_steps : rem k h (steps k h) = 1 := by
  have hs := steps_spec hhk
  have h1 := one_le_steps hh hhk
  obtain ⟨m, hm⟩ : ∃ m, steps k h = m + 1 := ⟨steps k h - 1, by omega⟩
  have hg := gcd_rem (k := k) (h := h) m
  rw [hc, ← hm] at hg
  have h2 := two_le_rem_of_lt_steps (show m < steps k h by omega)
  rcases (show rem k h (steps k h) = 0 ∨ rem k h (steps k h) = 1 by omega) with h0 | h0
  · rw [h0, Nat.gcd_zero_right] at hg; omega
  · exact h0

lemma pos_rem_of_le_steps {j : ℕ} (hj : j ≤ steps k h) : 0 < rem k h j := by
  rcases Nat.lt_or_eq_of_le hj with hlt | heq
  · have := two_le_rem_of_lt_steps hlt; omega
  · rw [heq, rem_steps hh hhk hc]; omega

/-- The remainders decrease strictly on `[0, n]`. -/
lemma rem_succ_lt {j : ℕ} (hj : j < steps k h) : rem k h (j + 1) < rem k h j := by
  cases j with
  | zero => simpa using hhk
  | succ j =>
    rw [rem_add_two]
    exact Nat.mod_lt _ (pos_rem_of_le_steps hh hhk hc (by omega))

lemma rem_strictAnti {i j : ℕ} (hij : i < j) (hj : j ≤ steps k h) : rem k h j < rem k h i := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := rem_succ_lt hh hhk hc (show j < steps k h by omega)
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hij) with h2 | h2
    · exact lt_trans h1 (ih h2 (by omega))
    · subst h2; exact h1

lemma rem_le_h {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps k h) : rem k h j ≤ h := by
  rcases Nat.lt_or_eq_of_le hj1 with h1 | h1
  · exact (rem_strictAnti hh hhk hc h1 hj).le
  · subst h1; rfl

lemma rem_div_rem_pos {j : ℕ} (hj : j < steps k h) : 1 ≤ rem k h j / rem k h (j + 1) := by
  have hp := pos_rem_of_le_steps hh hhk hc (show j + 1 ≤ steps k h by omega)
  have hl := rem_succ_lt hh hhk hc hj
  exact (Nat.one_le_div_iff hp).2 hl.le

/-- `r_j Q_{j+1} + r_{j+1} Q_j = k` for `j ≤ n`. -/
lemma rem_den_identity {j : ℕ} (hj : j ≤ steps k h) :
    rem k h j * den k h (j + 1) + rem k h (j + 1) * den k h j = k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ih := ih (by omega)
    have hp := pos_rem_of_le_steps hh hhk hc hj
    have hmod := Nat.mod_add_div (rem k h j) (rem k h (j + 1))
    rw [den_add_two, rem_add_two]
    calc rem k h (j + 1) * (rem k h j / rem k h (j + 1) * den k h (j + 1) + den k h j) +
          rem k h j % rem k h (j + 1) * den k h (j + 1)
        = (rem k h j % rem k h (j + 1) + rem k h (j + 1) * (rem k h j / rem k h (j + 1))) *
            den k h (j + 1) + rem k h (j + 1) * den k h j := by ring
      _ = k := by rw [hmod]; exact ih

omit hh hhk hc in
/-- `h Q_j ≡ (-1)^{j+1} r_j (mod k)` for every `j`. -/
lemma den_congr (j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => exact ⟨1, by simp⟩
    | 1, _ => exact ⟨0, by simp⟩
    | j + 2, ih =>
      have h0 := ih j (by omega)
      have h1 := ih (j + 1) (by omega)
      have hmod := Nat.mod_add_div (rem k h j) (rem k h (j + 1))
      set a := rem k h j / rem k h (j + 1)
      have hmodZ : ((rem k h j % rem k h (j + 1) : ℕ) : ℤ) =
          (rem k h j : ℤ) - (rem k h (j + 1) : ℤ) * a := by
        have : ((rem k h j % rem k h (j + 1) : ℕ) : ℤ) + (rem k h (j + 1) : ℤ) * a =
            (rem k h j : ℤ) := by exact_mod_cast hmod
        linarith
      rw [den_add_two, rem_add_two, Nat.cast_add, Nat.cast_mul, hmodZ]
      have e : (h : ℤ) * (a * den k h (j + 1) + den k h j) - (-1) ^ (j + 2 + 1) *
          ((rem k h j : ℤ) - rem k h (j + 1) * a) =
          a * ((h : ℤ) * den k h (j + 1) - (-1) ^ (j + 1 + 1) * rem k h (j + 1)) +
          ((h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j) := by ring
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right h1 _) h0

lemma den_pos {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps k h + 1) : 1 ≤ den k h j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => omega
    | 1, _ => simp
    | j + 2, ih =>
      have h1 := ih (j + 1) (by omega) (by omega) (by omega)
      have ha := rem_div_rem_pos hh hhk hc (show j < steps k h by omega)
      rw [den_add_two]
      nlinarith

lemma den_mono {j : ℕ} (hj : j ≤ steps k h) : den k h j ≤ den k h (j + 1) := by
  cases j with
  | zero => simp
  | succ j =>
    have ha := rem_div_rem_pos hh hhk hc (show j < steps k h by omega)
    rw [den_add_two]
    nlinarith

lemma den_le {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps k h) : den k h j ≤ k := by
  have e := rem_den_identity hh hhk hc (show j - 1 ≤ steps k h by omega)
  rw [show j - 1 + 1 = j by omega] at e
  have hp := pos_rem_of_le_steps hh hhk hc (show j - 1 ≤ steps k h by omega)
  nlinarith

/-- `2 r_{j+2} < r_j` for `j + 2 ≤ n`. -/
lemma two_rem_lt {j : ℕ} (hj : j + 1 < steps k h) : 2 * rem k h (j + 2) < rem k h j := by
  have hp := pos_rem_of_le_steps hh hhk hc (show j + 1 ≤ steps k h by omega)
  have hl := rem_succ_lt hh hhk hc (show j < steps k h by omega)
  have hmod := Nat.mod_add_div (rem k h j) (rem k h (j + 1))
  have hlt := Nat.mod_lt (rem k h j) hp
  have ha := rem_div_rem_pos hh hhk hc (show j < steps k h by omega)
  rw [rem_add_two]
  set a := rem k h j / rem k h (j + 1)
  set b := rem k h (j + 1)
  set c := rem k h j % rem k h (j + 1)
  rcases Nat.lt_or_ge a 2 with h2 | h2
  · have : a = 1 := by omega
    rw [this] at hmod; omega
  · nlinarith

lemma pow_mul_rem_le (i : ℕ) (hi : 2 * i ≤ steps k h) :
    2 ^ i * rem k h (2 * i) ≤ k ∧ (2 * i + 1 ≤ steps k h → 2 ^ i * rem k h (2 * i + 1) ≤ k) := by
  induction i with
  | zero => exact ⟨by simp, fun _ => by simpa using hhk.le⟩
  | succ i ih =>
    have ih := ih (by omega)
    constructor
    · have h1 := two_rem_lt hh hhk hc (show 2 * i + 1 < steps k h by omega)
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_succ]
      nlinarith [ih.1]
    · intro hle
      have h1 := two_rem_lt hh hhk hc (show 2 * i + 1 + 1 < steps k h by omega)
      have h2 := ih.2 (by omega)
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring, pow_succ]
      nlinarith

/-- `n ≤ 2 log₂ k + 1`. -/
theorem steps_le_log : steps k h ≤ 2 * Nat.log 2 k + 1 := by
  have hr := rem_steps hh hhk hc
  obtain ⟨i, hi⟩ : ∃ i, steps k h = 2 * i ∨ steps k h = 2 * i + 1 :=
    ⟨steps k h / 2, by omega⟩
  have hpow : 2 ^ i ≤ k := by
    rcases hi with hi | hi
    · have := (pow_mul_rem_le hh hhk hc i (by omega)).1
      rw [← hi, hr, mul_one] at this; exact this
    · have := (pow_mul_rem_le hh hhk hc i (by omega)).2 (by omega)
      rw [← hi, hr, mul_one] at this; exact this
  have := Nat.le_log_of_pow_le (by norm_num) hpow
  omega

end SmallRatio
