module

public import SmallRatio.Defs

@[expose] public section

/-!
# Dedekind reciprocity

For coprime positive integers `h`, `k`,

  `s(h,k) + s(k,h) = (h/k + k/h + 1/(hk))/12 - 1/4`.

The proof is elementary. With `A(h,k) = ∑_{r<k} r (hr mod k)` one has `s(h,k) = A(h,k)/k² - (k-1)/4`,
and `A(h,k) = h ∑ r² - k ∑ r ⌊hr/k⌋`. Since `r ↦ hr mod k` permutes the residues,
`∑ (hr mod k)² = ∑ r²`, which expresses `∑ r ⌊hr/k⌋` through `∑ ⌊hr/k⌋²`; counting lattice points
under the line `y = hx/k` gives `∑_{r<k} ⌊hr/k⌋² = ∑_{0<j<h} (2j-1)(k-1-⌊kj/h⌋)`, which brings in
`∑ j ⌊kj/h⌋`, the corresponding sum for `A(k,h)`.
-/

namespace SmallRatio

open Finset

lemma fract_natCast_div (n k : ℕ) (hk : 0 < k) :
    Int.fract ((n : ℚ) / k) = ((n % k : ℕ) : ℚ) / k := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h0 : ((n : ℕ) : ℚ) = ((n % k : ℕ) : ℚ) + (k : ℚ) * ((n / k : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mod_add_div n k).symm
  have h1 : (n : ℚ) / k = ((n % k : ℕ) : ℚ) / k + ((n / k : ℕ) : ℤ) := by
    rw [Int.cast_natCast]
    nth_rewrite 1 [h0]
    field_simp
  rw [h1, Int.fract_add_intCast]
  apply Int.fract_eq_self.2
  constructor
  · positivity
  · rw [div_lt_one (by exact_mod_cast hk)]
    exact_mod_cast Nat.mod_lt n hk

lemma sawtooth_natCast_div (n k : ℕ) (hk : 0 < k) (hn : ¬ k ∣ n) :
    sawtooth ((n : ℚ) / k) = ((n % k : ℕ) : ℚ) / k - 1 / 2 := by
  unfold sawtooth
  rw [fract_natCast_div n k hk, ite_eq_right]
  have : n % k ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [div_eq_zero_iff]
  push Not
  exact ⟨by exact_mod_cast this, hk'⟩

lemma sawtooth_zero : sawtooth 0 = 0 := by simp [sawtooth]

/-- Multiplication by a unit permutes `range k`. -/
lemma sum_mul_mod_perm {M : Type*} [AddCommMonoid M] (h k : ℕ) (hk : 0 < k) (hc : Nat.Coprime h k)
    (f : ℕ → M) : ∑ r ∈ range k, f (h * r % k) = ∑ r ∈ range k, f r := by
  have hinj : Set.InjOn (fun r => h * r % k) (range k : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : h * a ≡ h * b [MOD k] := hab
    have h2 : a ≡ b [MOD k] := Nat.ModEq.cancel_left_of_coprime (by
      rw [Nat.gcd_comm]; exact hc) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  have himage : (range k).image (fun r => h * r % k) = range k := by
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image, mem_range] at hx
      obtain ⟨r, _, rfl⟩ := hx
      exact mem_range.2 (Nat.mod_lt _ hk)
    · rw [card_image_of_injOn hinj]
  calc ∑ r ∈ range k, f (h * r % k) = ∑ x ∈ (range k).image (fun r => h * r % k), f x :=
        (sum_image hinj).symm
    _ = ∑ r ∈ range k, f r := by rw [himage]

/-- `A(h,k) = ∑_{r<k} r (hr mod k)`. -/
def Asum (h k : ℕ) : ℕ := ∑ r ∈ range k, r * (h * r % k)

lemma dedekindSum_eq_Asum (h k : ℕ) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k = (Asum h k : ℚ) / (k : ℚ) ^ 2 - ((k : ℚ) - 1) / 4 := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  -- each term, with the term `r = 0` corrected
  have hterm : ∀ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k) =
      ((r : ℚ) / k - 1 / 2) * (((h * r % k : ℕ) : ℚ) / k - 1 / 2) - if r = 0 then 1 / 4 else 0 := by
    intro r hr
    rw [mem_range] at hr
    by_cases h0 : r = 0
    · subst h0; simp [sawtooth_zero]; norm_num
    · rw [ite_eq_right h0]
      have hnr : ¬ k ∣ r := fun hd => h0 (Nat.eq_zero_of_dvd_of_lt hd hr)
      have hnhr : ¬ k ∣ h * r := by
        intro hd
        exact hnr ((Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hc) hd))
      have e1 := sawtooth_natCast_div r k hk hnr
      have e2 := sawtooth_natCast_div (h * r) k hk hnhr
      rw [Nat.mod_eq_of_lt hr] at e1
      push_cast at e2
      rw [e1, e2, sub_zero]
  rw [dedekindSum, sum_congr rfl hterm, sum_sub_distrib, sum_ite_eq' (range k) 0 (fun _ => (1 : ℚ) / 4),
    ite_eq_left (mem_range.2 hk)]
  -- expand
  have hsumr : ∑ r ∈ range k, (r : ℚ) = (k : ℚ) * (k - 1) / 2 := by
    have := Finset.sum_range_id_mul_two k
    have h2 : (∑ r ∈ range k, (r : ℚ)) * 2 = (k : ℚ) * (k - 1) := by
      have : ((∑ i ∈ range k, i : ℕ) : ℚ) * 2 = ((k * (k - 1) : ℕ) : ℚ) := by exact_mod_cast this
      push_cast at this
      rw [Nat.cast_sub (by omega)] at this
      simpa using this
    linarith
  have hsumt : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) = (k : ℚ) * (k - 1) / 2 := by
    rw [sum_mul_mod_perm h k hk hc (fun r => ((r : ℕ) : ℚ)), hsumr]
  have hA : (Asum h k : ℚ) = ∑ r ∈ range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ) := by
    unfold Asum; push_cast; rfl
  have hexp : ∑ r ∈ range k, ((r : ℚ) / k - 1 / 2) * (((h * r % k : ℕ) : ℚ) / k - 1 / 2) =
      (∑ r ∈ range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ)) / k ^ 2
        - (∑ r ∈ range k, (r : ℚ)) / (2 * k) - (∑ r ∈ range k, ((h * r % k : ℕ) : ℚ)) / (2 * k)
        + (k : ℚ) / 4 := by
    rw [sum_div, sum_div, sum_div]
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    have : (k : ℚ) / 4 = ∑ _r ∈ range k, (1 : ℚ) / 4 := by
      rw [sum_const, card_range, nsmul_eq_mul]; ring
    rw [this, ← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    field_simp
    ring
  rw [hexp, hsumr, hsumt, ← hA]
  field_simp
  ring

/-- `∑_{j=1}^{m} (2j - 1) = m²`. -/
lemma sum_odd (m : ℕ) : ∑ j ∈ Ico 1 (m + 1), (2 * (j : ℤ) - 1) = (m : ℤ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_Ico_succ_top (by omega), ih]
    push_cast
    ring

/-- Lattice points under `y = hx/k`: `∑_{r<k} ⌊hr/k⌋² = ∑_{0<j<h} (2j-1)(k-1-⌊kj/h⌋)`. -/
lemma sum_floor_sq (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 =
      ∑ j ∈ Ico 1 h, (2 * (j : ℤ) - 1) * ((k : ℤ) - 1 - ((k * j / h : ℕ) : ℤ)) := by
  have hle : ∀ r ∈ range k, h * r / k < h := by
    intro r hr
    rw [mem_range] at hr
    rw [Nat.div_lt_iff_lt_mul hk]
    exact Nat.mul_lt_mul_of_pos_left hr hh
  have step1 : ∀ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 =
      ∑ j ∈ Ico 1 h, if j ≤ h * r / k then (2 * (j : ℤ) - 1) else 0 := by
    intro r hr
    rw [← sum_odd, sum_ite, sum_const_zero, add_zero]
    congr 1
    ext j
    simp only [mem_Ico, mem_filter]
    have := hle r hr
    omega
  rw [sum_congr rfl step1, sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [mem_Ico] at hj
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  -- count the `r < k` with `j ≤ ⌊hr/k⌋`
  have hset : (range k).filter (fun r => j ≤ h * r / k) = Ioo (k * j / h) k := by
    ext r
    simp only [mem_filter, mem_range, mem_Ioo]
    rw [Nat.le_div_iff_mul_le hk, Nat.div_lt_iff_lt_mul hh]
    constructor
    · rintro ⟨hr, hjr⟩
      refine ⟨?_, hr⟩
      rcases Nat.lt_or_eq_of_le hjr with hlt | heq
      · linarith
      · exfalso
        have : h ∣ k * j := ⟨r, by linarith⟩
        have := Nat.le_of_dvd (by omega) ((Nat.Coprime.dvd_of_dvd_mul_left hc) this)
        omega
    · rintro ⟨hjr, hr⟩
      exact ⟨hr, by linarith⟩
  rw [hset, Nat.card_Ioo]
  have hlt : k * j / h < k := by
    rw [Nat.div_lt_iff_lt_mul hh]
    exact Nat.mul_lt_mul_of_pos_left hj.2 hk
  generalize k * j / h = g at hlt ⊢
  omega

/-- `∑_{j<h} ⌊kj/h⌋ = (h-1)(k-1)/2`. -/
lemma sum_floor (h k : ℕ) (hh : 0 < h) (hc : Nat.Coprime h k) :
    2 * ∑ j ∈ range h, ((k * j / h : ℕ) : ℤ) = ((h : ℤ) - 1) * ((k : ℤ) - 1) := by
  have hperm := sum_mul_mod_perm k h hh (Nat.Coprime.symm hc) (fun r => ((r : ℕ) : ℤ))
  have hmod : ∀ j ∈ range h, ((k * j % h : ℕ) : ℤ) = (k : ℤ) * j - h * ((k * j / h : ℕ) : ℤ) := by
    intro j _
    have := Nat.mod_add_div (k * j) h
    have : ((k * j % h : ℕ) : ℤ) + h * ((k * j / h : ℕ) : ℤ) = (k : ℤ) * j := by exact_mod_cast this
    linarith
  rw [sum_congr rfl hmod, sum_sub_distrib, ← mul_sum, ← mul_sum] at hperm
  have hs : 2 * ∑ j ∈ range h, (j : ℤ) = (h : ℤ) * (h - 1) := by
    have := Finset.sum_range_id_mul_two h
    have : ((∑ i ∈ range h, i : ℕ) : ℤ) * 2 = ((h * (h - 1) : ℕ) : ℤ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (by omega : 1 ≤ h)] at this
    linarith
  have hh' : (h : ℤ) ≠ 0 := by exact_mod_cast hh.ne'
  apply mul_left_cancel₀ hh'
  nlinarith [hperm, hs]

lemma sum_sq_range (m : ℕ) : 6 * ∑ r ∈ range m, (r : ℚ) ^ 2 = ((m : ℚ) - 1) * m * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

/-- **Dedekind reciprocity.** -/
theorem dedekind_reciprocity (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k + dedekindSum k h =
      ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4 := by
  rw [dedekindSum_eq_Asum h k hk hc, dedekindSum_eq_Asum k h hh (Nat.Coprime.symm hc)]
  -- the unknowns
  set S2k : ℚ := ∑ r ∈ range k, (r : ℚ) ^ 2
  set S2h : ℚ := ∑ j ∈ range h, (j : ℚ) ^ 2
  set F : ℚ := ∑ r ∈ range k, (r : ℚ) * ((h * r / k : ℕ) : ℚ)
  set G : ℚ := ∑ j ∈ range h, (j : ℚ) * ((k * j / h : ℕ) : ℚ)
  set Sf2 : ℚ := ∑ r ∈ range k, ((h * r / k : ℕ) : ℚ) ^ 2
  set Sg : ℚ := ∑ j ∈ range h, ((k * j / h : ℕ) : ℚ)
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  -- `hr mod k = hr - k ⌊hr/k⌋`
  have hmodk : ∀ r : ℕ, ((h * r % k : ℕ) : ℚ) = (h : ℚ) * r - k * ((h * r / k : ℕ) : ℚ) := by
    intro r
    have := Nat.mod_add_div (h * r) k
    have : ((h * r % k : ℕ) : ℚ) + k * ((h * r / k : ℕ) : ℚ) = (h : ℚ) * r := by exact_mod_cast this
    linarith
  have hmodh : ∀ j : ℕ, ((k * j % h : ℕ) : ℚ) = (k : ℚ) * j - h * ((k * j / h : ℕ) : ℚ) := by
    intro j
    have := Nat.mod_add_div (k * j) h
    have : ((k * j % h : ℕ) : ℚ) + h * ((k * j / h : ℕ) : ℚ) = (k : ℚ) * j := by exact_mod_cast this
    linarith
  have e1 : (Asum h k : ℚ) = h * S2k - k * F := by
    unfold Asum; push_cast
    simp_rw [hmodk]
    simp only [S2k, F, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro r _; ring
  have e2 : (Asum k h : ℚ) = k * S2h - h * G := by
    unfold Asum; push_cast
    simp_rw [hmodh]
    simp only [S2h, G, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro r _; ring
  -- `∑ (hr mod k)² = ∑ r²`
  have e3 : (h : ℚ) ^ 2 * S2k - 2 * h * k * F + k ^ 2 * Sf2 = S2k := by
    have hp := sum_mul_mod_perm h k hk hc (fun r => ((r : ℕ) : ℚ) ^ 2)
    simp_rw [hmodk] at hp
    rw [show (h : ℚ) ^ 2 * S2k - 2 * h * k * F + k ^ 2 * Sf2 =
        ∑ x ∈ range k, ((h : ℚ) * x - k * ((h * x / k : ℕ) : ℚ)) ^ 2 from ?_]
    · exact hp
    · simp only [S2k, F, Sf2, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro r _; ring
  -- lattice points
  have e4 : Sf2 = ((k : ℚ) - 1) * ((h : ℚ) - 1) ^ 2 - 2 * G + Sg := by
    have hl := sum_floor_sq h k hh hk hc
    have hl' : Sf2 = ∑ j ∈ Ico 1 h, (2 * (j : ℚ) - 1) * ((k : ℚ) - 1 - ((k * j / h : ℕ) : ℚ)) := by
      have := congrArg (Int.cast : ℤ → ℚ) hl
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
        Int.cast_ofNat, Int.cast_one] at this
      simp only [Sf2]; exact this
    rw [hl']
    have hshift : ∀ f : ℕ → ℚ, f 0 = 0 → ∑ j ∈ Ico 1 h, f j = ∑ j ∈ range h, f j := by
      intro f hf0
      rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ h)]
      simp [hf0]
    have hodd : ∑ j ∈ Ico 1 h, (2 * (j : ℚ) - 1) = ((h : ℚ) - 1) ^ 2 := by
      obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
      have := sum_odd m
      have : ∑ j ∈ Ico 1 (m + 1), (2 * (j : ℚ) - 1) = (m : ℚ) ^ 2 := by exact_mod_cast this
      rw [this]; push_cast; ring
    have hsplit : ∑ j ∈ Ico 1 h, (2 * (j : ℚ) - 1) * ((k : ℚ) - 1 - ((k * j / h : ℕ) : ℚ)) =
        ((k : ℚ) - 1) * ∑ j ∈ Ico 1 h, (2 * (j : ℚ) - 1)
          - 2 * ∑ j ∈ Ico 1 h, (j : ℚ) * ((k * j / h : ℕ) : ℚ)
          + ∑ j ∈ Ico 1 h, ((k * j / h : ℕ) : ℚ) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro j _; ring
    rw [hsplit, hodd, hshift (fun j => (j : ℚ) * ((k * j / h : ℕ) : ℚ)) (by simp),
      hshift (fun j => ((k * j / h : ℕ) : ℚ)) (by simp)]
  have e5 : 2 * Sg = ((h : ℚ) - 1) * ((k : ℚ) - 1) := by
    have := congrArg (Int.cast : ℤ → ℚ) (sum_floor h k hh hc)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      Int.cast_ofNat, Int.cast_one] at this
    simp only [Sg]; exact this
  have e6 : 6 * S2k = ((k : ℚ) - 1) * k * (2 * k - 1) := by
    simp only [S2k]; exact sum_sq_range k
  have e7 : 6 * S2h = ((h : ℚ) - 1) * h * (2 * h - 1) := by
    simp only [S2h]; exact sum_sq_range h
  have key : 12 * (h : ℚ) ^ 2 * (h * S2k - k * F) + 12 * (k : ℚ) ^ 2 * (k * S2h - h * G) =
      (h : ℚ) ^ 3 * k + h * k ^ 3 + h * k + 3 * h ^ 2 * k ^ 2 * (h + k - 3) := by
    linear_combination 6 * (h : ℚ) * e3 - 6 * (h : ℚ) * k ^ 2 * e4 - 3 * (h : ℚ) * k ^ 2 * e5
      + (h : ℚ) * (h ^ 2 + 1) * e6 + 2 * (k : ℚ) ^ 3 * e7
  rw [e1, e2]
  field_simp
  linear_combination 4 * key

end SmallRatio
