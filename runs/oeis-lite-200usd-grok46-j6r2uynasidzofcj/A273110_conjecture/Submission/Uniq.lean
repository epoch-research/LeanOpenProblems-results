import FormalConjectures.Util.ProblemImports

open scoped NumberTheorySymbols
open Nat Int

/-
  Development of uniqueness for A273110 when `n` is not of the form `4^k (8m+7)`.
  Once complete, lemmas are copied into `Spec.lean`.
-/

def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n
  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2
    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

def Valid (n x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
  y > 0 ∧ y ≥ z ∧ z ≤ w ∧
  IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2)

instance {n x y z w : ℕ} : Decidable (Valid n x y z w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

lemma valid_x_zero {n y z w : ℕ} (hsum : y ^ 2 + z ^ 2 + w ^ 2 = n)
    (hy : y > 0) (hyz : y ≥ z) (hzw : z ≤ w) : Valid n 0 y z w := by
  refine ⟨by simpa using hsum, hy, hyz, hzw, ?_⟩
  refine ⟨5 * (y + z), ?_⟩
  ring

lemma valid_x_eq_sum {n y z w : ℕ} (hsum : (y + z) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (hy : y > 0) (hyz : y ≥ z) (hzw : z ≤ w) : Valid n (y + z) y z w := by
  refine ⟨hsum, hy, hyz, hzw, ?_⟩
  refine ⟨13 * (y + z), ?_⟩
  ring

lemma le_of_sq_le_self (a n : ℕ) (h : a ^ 2 ≤ n) : a ≤ n := by
  cases a with
  | zero => exact Nat.zero_le _
  | succ a =>
    have : a + 1 ≤ (a + 1) ^ 2 := by nlinarith
    exact this.trans h

lemma valid_coords_le {n x y z w : ℕ} (h : Valid n x y z w) :
    x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ w ≤ n := by
  have hsum := h.1
  have hx : x ^ 2 ≤ n := by omega
  have hy : y ^ 2 ≤ n := by omega
  have hz : z ^ 2 ≤ n := by omega
  have hw : w ^ 2 ≤ n := by omega
  exact ⟨le_of_sq_le_self _ _ hx, le_of_sq_le_self _ _ hy,
    le_of_sq_le_self _ _ hz, le_of_sq_le_self _ _ hw⟩

def validFinset (n : ℕ) : Finset ((ℕ × ℕ) × ℕ × ℕ) :=
  (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)) ×ˢ
    (Finset.range (n + 1) ×ˢ Finset.range (n + 1)))).filter
    (fun p => Valid n p.1.1 p.1.2 p.2.1 p.2.2)

lemma A273110_eq_card_validFinset (n : ℕ) : A273110 n = (validFinset n).card := by
  classical
  unfold A273110 validFinset
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
  simp [Valid]

lemma mem_validFinset {n x y z w : ℕ} (h : Valid n x y z w) :
    ((x, y), z, w) ∈ validFinset n := by
  obtain ⟨hx, hy, hz, hw⟩ := valid_coords_le h
  refine Finset.mem_filter.mpr ⟨?_, h⟩
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hx),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hy)⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hz),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hw)⟩

lemma A273110_ge_two_of_two_valid {n x y z w x' y' z' w' : ℕ}
    (h : Valid n x y z w) (h' : Valid n x' y' z' w')
    (hne : ¬ (x = x' ∧ y = y' ∧ z = z' ∧ w = w')) :
    2 ≤ A273110 n := by
  rw [A273110_eq_card_validFinset]
  have hp := mem_validFinset h
  have hq := mem_validFinset h'
  have hne' : ((x, y), z, w) ≠ ((x', y'), z', w') := by
    intro eq
    apply hne
    have hx : x = x' := congrArg (fun p => p.1.1) eq
    have hy : y = y' := congrArg (fun p => p.1.2) eq
    have hz : z = z' := congrArg (fun p => p.2.1) eq
    have hw : w = w' := congrArg (fun p => p.2.2) eq
    exact ⟨hx, hy, hz, hw⟩
  exact Finset.one_lt_card.mpr ⟨_, hp, _, hq, hne'⟩

lemma two_reps_of_two_mul_sq {k : ℕ} (hk : 0 < k) :
    Valid (2 * k ^ 2) 0 k 0 k ∧ Valid (2 * k ^ 2) k k 0 0 := by
  constructor
  · exact valid_x_zero (by ring) hk (Nat.zero_le _) (Nat.zero_le _)
  · exact valid_x_eq_sum (by ring) hk (Nat.zero_le _) (Nat.zero_le _)

lemma two_reps_of_three_mul_sq {k : ℕ} (hk : 0 < k) :
    Valid (3 * k ^ 2) 0 k k k ∧ Valid (3 * k ^ 2) k k 0 k := by
  constructor
  · exact valid_x_zero (by ring) hk le_rfl le_rfl
  · exact valid_x_eq_sum (by ring) hk (Nat.zero_le _) (Nat.zero_le _)

lemma quat_identity (a b c d : ℤ) :
    (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) ^ 2 + (2 * a * c + 2 * b * d) ^ 2
      + (2 * a * d - 2 * b * c) ^ 2
      = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 := by
  ring

lemma three_sq_of_sq_of_four (a b c d : ℕ) :
    ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 - (c : ℤ) ^ 2 - (d : ℤ) ^ 2).natAbs ^ 2
      + (2 * a * c + 2 * b * d) ^ 2
      + ((2 * a * d : ℤ) - (2 * b * c : ℤ)).natAbs ^ 2
      = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 := by
  have h := quat_identity (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ)
  rw [← Int.natCast_inj]
  push_cast
  simpa [sq_abs] using h

lemma A273110_ge_two_of_two_pos_zero {n A B : ℕ}
    (hs : A ^ 2 + B ^ 2 = n) (hA : 0 < A) (hB : 0 < B) (hAB : A ≠ B) :
    2 ≤ A273110 n := by
  have hv1 : Valid n 0 A 0 B :=
    valid_x_zero (by linarith) hA (Nat.zero_le _) (Nat.zero_le _)
  have hv2 : Valid n 0 B 0 A :=
    valid_x_zero (by linarith) hB (Nat.zero_le _) (Nat.zero_le _)
  refine A273110_ge_two_of_two_valid hv1 hv2 ?_
  intro h
  exact hAB h.2.1

lemma A273110_ge_two_of_two_eq_zero {k : ℕ} (hk : 0 < k) :
    2 ≤ A273110 (2 * k ^ 2) := by
  obtain ⟨h1, h2⟩ := two_reps_of_two_mul_sq hk
  refine A273110_ge_two_of_two_valid h1 h2 ?_
  intro h
  exact (Nat.succ_ne_zero 0).symm (by
    have : 0 = k := h.1
    omega)

lemma A273110_ge_two_of_three_eq {k : ℕ} (hk : 0 < k) :
    2 ≤ A273110 (3 * k ^ 2) := by
  obtain ⟨h1, h2⟩ := two_reps_of_three_mul_sq hk
  refine A273110_ge_two_of_two_valid h1 h2 ?_
  intro h
  exact (Nat.succ_ne_zero 0).symm (by
    have : 0 = k := h.1
    omega)

lemma A273110_ge_two_of_pair_and_pos {n A B : ℕ}
    (hs : A ^ 2 + 2 * B ^ 2 = n) (hA : B < A) (hB : 0 < B) :
    2 ≤ A273110 n := by
  have hv1 : Valid n 0 A B B :=
    valid_x_zero (by linarith) (Nat.lt_trans hB hA) (Nat.le_of_lt hA) le_rfl
  have hv2 : Valid n 0 B B A :=
    valid_x_zero (by linarith) hB le_rfl (Nat.le_of_lt hA)
  refine A273110_ge_two_of_two_valid hv1 hv2 ?_
  intro h
  exact Nat.ne_of_gt hA h.2.1

lemma A273110_ge_two_of_two_eq_and_pos {n A C : ℕ}
    (hs : 2 * A ^ 2 + C ^ 2 = n) (hC : 0 < C) (hCA : C < A) :
    2 ≤ A273110 n := by
  have hApos : 0 < A := Nat.lt_trans hC hCA
  have hv1 : Valid n 0 A C A :=
    valid_x_zero (by linarith) hApos (Nat.le_of_lt hCA) (Nat.le_of_lt hCA)
  have hv2 : Valid n A A 0 C :=
    valid_x_eq_sum (by linarith) hApos (Nat.zero_le _) (Nat.zero_le _)
  refine A273110_ge_two_of_two_valid hv1 hv2 ?_
  intro h
  exact (Nat.succ_ne_zero 0).symm (by
    have : 0 = A := h.1
    omega)

lemma A273110_ge_two_of_three_distinct {n A B C : ℕ}
    (hs : A ^ 2 + B ^ 2 + C ^ 2 = n)
    (hA : B < A) (hB : C < B) (hC : 0 < C) :
    2 ≤ A273110 n := by
  have hApos : 0 < A := Nat.lt_trans (Nat.lt_trans hC hB) hA
  have hv1 : Valid n 0 A C B :=
    valid_x_zero (by linarith) hApos (Nat.le_of_lt (Nat.lt_trans hB hA)) (Nat.le_of_lt hB)
  have hv2 : Valid n 0 B C A :=
    valid_x_zero (by linarith) (Nat.lt_trans hC hB) (Nat.le_of_lt hB)
      (Nat.le_of_lt (Nat.lt_trans hB hA))
  refine A273110_ge_two_of_two_valid hv1 hv2 ?_
  intro h
  exact Nat.ne_of_gt hA h.2.1

lemma A273110_ge_two_of_three_sq_not_pure {n A B C : ℕ}
    (hn : 0 < n)
    (hs : A ^ 2 + B ^ 2 + C ^ 2 = n)
    (hord : A ≥ B ∧ B ≥ C)
    (hnot : ¬ (0 < A ∧ B = 0 ∧ C = 0)) :
    2 ≤ A273110 n := by
  obtain ⟨hAB, hBC⟩ := hord
  by_cases hC0 : C = 0
  · subst hC0
    by_cases hB0 : B = 0
    · subst hB0
      have hA0 : A = 0 := by
        by_contra hApos
        exact hnot ⟨Nat.pos_of_ne_zero hApos, rfl, rfl⟩
      subst hA0
      simp at hs
      omega
    · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      by_cases hAeq : A = B
      · subst hAeq
        have hn' : n = 2 * A ^ 2 := by linarith
        rw [hn']
        exact A273110_ge_two_of_two_eq_zero hBpos
      · have hAgt : B < A := Nat.lt_of_le_of_ne hAB (Ne.symm hAeq)
        exact A273110_ge_two_of_two_pos_zero (by linarith)
          (Nat.lt_trans hBpos hAgt) hBpos (Nat.ne_of_gt hAgt)
  · have hCpos : 0 < C := Nat.pos_of_ne_zero hC0
    by_cases hBeqC : B = C
    · subst hBeqC
      by_cases hAeq : A = B
      · subst hAeq
        have hn' : n = 3 * A ^ 2 := by linarith
        rw [hn']
        exact A273110_ge_two_of_three_eq (Nat.lt_of_lt_of_le hCpos hAB)
      · have hAgt : B < A := Nat.lt_of_le_of_ne hAB (Ne.symm hAeq)
        exact A273110_ge_two_of_pair_and_pos (by linarith) hAgt hCpos
    · have hBgtC : C < B := Nat.lt_of_le_of_ne hBC (Ne.symm hBeqC)
      by_cases hAeq : A = B
      · subst hAeq
        exact A273110_ge_two_of_two_eq_and_pos (by linarith) hCpos hBgtC
      · have hAgt : B < A := Nat.lt_of_le_of_ne hAB (Ne.symm hAeq)
        exact A273110_ge_two_of_three_distinct hs hAgt hBgtC hCpos

lemma exists_sorted_of_three_sq {n a b c : ℕ} (hs : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    ∃ A B C, A ≥ B ∧ B ≥ C ∧ A ^ 2 + B ^ 2 + C ^ 2 = n := by
  rcases le_total b a with hba | hab
  · rcases le_total c b with hcb | hbc
    · exact ⟨a, b, c, hba, hcb, hs⟩
    · rcases le_total c a with hca | hac
      · exact ⟨a, c, b, hca, hbc, by linarith⟩
      · exact ⟨c, a, b, hac, hba, by linarith⟩
  · rcases le_total c a with hca | hac
    · exact ⟨b, a, c, hab, hca, by linarith⟩
    · rcases le_total c b with hcb | hbc
      · exact ⟨b, c, a, hcb, hac, by linarith⟩
      · exact ⟨c, b, a, hbc, hab, by linarith⟩

lemma valid_of_pure_square {A : ℕ} (hA : 0 < A) :
    Valid (A ^ 2) 0 A 0 0 :=
  valid_x_zero (by ring) hA (Nat.zero_le _) le_rfl

lemma valid_of_three_sq {n a b c : ℕ} (hn : 0 < n)
    (hs : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    ∃ y z w, Valid n 0 y z w := by
  have ha0 : 0 < a ∨ 0 < b ∨ 0 < c := by
    by_contra H
    push_neg at H
    have : a = 0 ∧ b = 0 ∧ c = 0 := by omega
    simp [this] at hs
    omega
  cases le_total b a with
  | inl hba =>
    cases le_total c a with
    | inl hca =>
      cases le_total c b with
      | inl hcb =>
          exact ⟨a, c, b, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) hca hcb⟩
      | inr hbc =>
          exact ⟨a, b, c, valid_x_zero hs (by omega) hba hbc⟩
    | inr hac =>
      exact ⟨c, b, a, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) (hba.trans hac) hba⟩
  | inr hab =>
    cases le_total c b with
    | inl hcb =>
      cases le_total c a with
      | inl hca =>
          exact ⟨b, c, a, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) (hca.trans hab) hca⟩
      | inr hac =>
          exact ⟨b, a, c, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) hab hac⟩
    | inr hbc =>
      exact ⟨c, a, b, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) (hab.trans hbc) hab⟩

lemma not_prime_sq {n : ℕ} (h : (n ^ 2).Prime) : False :=
  Nat.Prime.not_prime_pow (n := 2) (by decide) h

lemma sq_add_sq_pos_of_prime_one_mod_four {p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u ^ 2 + v ^ 2 = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne3 : p % 4 ≠ 3 := by omega
  obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq hne3
  have hu : 0 < u := by
    by_contra hu
    have : u = 0 := by omega
    subst this
    simp at huv
    exact not_prime_sq (huv ▸ hp)
  have hv : 0 < v := by
    by_contra hv
    have : v = 0 := by omega
    subst this
    simp at huv
    exact not_prime_sq (huv ▸ hp)
  exact ⟨u, v, hu, hv, huv⟩

lemma brahmagupta_diff (u v : ℕ) :
    (u ^ 2 + v ^ 2) ^ 2 =
      ((u : ℤ) ^ 2 - (v : ℤ) ^ 2).natAbs ^ 2 + (2 * u * v) ^ 2 := by
  rw [← Int.natCast_inj]
  push_cast
  simpa [sq_abs] using
    (show ((u : ℤ) ^ 2 + (v : ℤ) ^ 2) ^ 2
        = ((u : ℤ) ^ 2 - (v : ℤ) ^ 2) ^ 2 + (2 * u * v : ℤ) ^ 2 by ring)

lemma two_sq_of_mul_one_mod_four {A p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1)
    (hdvd : p ∣ A) (hA : 0 < A) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧ C ^ 2 + D ^ 2 = A ^ 2 := by
  obtain ⟨u, v, hu, hv, huv⟩ := sq_add_sq_pos_of_prime_one_mod_four hp h1
  obtain ⟨M, hM⟩ := hdvd
  have hMpos : 0 < M := by
    by_contra hM0
    have : M = 0 := by omega
    subst this
    simp at hM
    omega
  have hne : u ≠ v := by
    intro heq
    subst heq
    have hpEq : p = 2 * u ^ 2 := by linarith
    have hpEven : Even p := even_iff_two_dvd.mpr ⟨u ^ 2, hpEq⟩
    have hp2 : p = 2 :=
      hp.eq_two_or_odd'.resolve_right (Nat.not_odd_iff_even.mpr hpEven)
    omega
  have hCpos : 0 < ((u : ℤ) ^ 2 - (v : ℤ) ^ 2).natAbs := by
    rw [Int.natAbs_pos]
    intro hz
    have hsq : (u : ℤ) ^ 2 = (v : ℤ) ^ 2 := by linarith
    have : u ^ 2 = v ^ 2 := by exact_mod_cast hsq
    exact hne (Nat.pow_left_injective (by decide : 2 ≠ 0) this)
  refine ⟨((u : ℤ) ^ 2 - (v : ℤ) ^ 2).natAbs * M, 2 * u * v * M, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hCpos hMpos
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hu) hv) hMpos
  · have hbrah := brahmagupta_diff u v
    calc
      (((u : ℤ) ^ 2 - (v : ℤ) ^ 2).natAbs * M) ^ 2 + (2 * u * v * M) ^ 2
          = (((u : ℤ) ^ 2 - (v : ℤ) ^ 2).natAbs ^ 2 + (2 * u * v) ^ 2) * M ^ 2 := by ring
      _ = (u ^ 2 + v ^ 2) ^ 2 * M ^ 2 := by rw [← hbrah]
      _ = p ^ 2 * M ^ 2 := by rw [huv]
      _ = (p * M) ^ 2 := by ring
      _ = A ^ 2 := by rw [hM]

lemma A273110_ge_two_of_two_pos_squares {n C D : ℕ}
    (hs : C ^ 2 + D ^ 2 = n) (hC : 0 < C) (hD : 0 < D) :
    2 ≤ A273110 n := by
  by_cases hCD : C = D
  · subst hCD
    have hn : n = 2 * C ^ 2 := by linarith
    rw [hn]
    exact A273110_ge_two_of_two_eq_zero hC
  · exact A273110_ge_two_of_two_pos_zero hs hC hD hCD

lemma A273110_ge_two_of_has_prime_one_mod_four {A p : ℕ}
    (hp : p.Prime) (h1 : p % 4 = 1) (hdvd : p ∣ A) (hA : 1 < A) :
    2 ≤ A273110 (A ^ 2) := by
  have hApos : 0 < A := lt_trans Nat.zero_lt_one hA
  obtain ⟨C, D, hC, hD, hsum⟩ := two_sq_of_mul_one_mod_four hp h1 hdvd hApos
  have hv0 : Valid (A ^ 2) 0 A 0 0 := valid_of_pure_square hApos
  have hge : 2 ≤ A273110 (A ^ 2) := A273110_ge_two_of_two_pos_squares hsum hC hD
  exact hge

lemma not_two_pos_sq_hyp_three_mod_four {p x y : ℕ}
    (hp : p.Prime) (h3 : p % 4 = 3)
    (h : x ^ 2 + y ^ 2 = p ^ 2) (hx : 0 < x) (hy : 0 < y) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpx : p ∣ x
  · have hpy : p ∣ y := by
      have hp2 : p ∣ x ^ 2 + y ^ 2 := by
        rw [h]; exact dvd_pow_self p (by decide)
      have hx2 : p ∣ x ^ 2 := dvd_pow hpx (by decide : 2 ≠ 0)
      have hy2 : p ∣ y ^ 2 := by
        have : (p : ℤ) ∣ (y : ℤ) ^ 2 := by
          have h1 : (p : ℤ) ∣ (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by
            exact_mod_cast hp2
          have h2 : (p : ℤ) ∣ (x : ℤ) ^ 2 := by
            exact_mod_cast hx2
          simpa using dvd_sub h1 h2
        exact_mod_cast this
      exact hp.dvd_of_dvd_pow hy2
    obtain ⟨k, hk⟩ := hpx
    obtain ⟨m, hm⟩ := hpy
    have heq : p ^ 2 * (k ^ 2 + m ^ 2) = p ^ 2 := by
      calc
        p ^ 2 * (k ^ 2 + m ^ 2) = (p * k) ^ 2 + (p * m) ^ 2 := by ring
        _ = x ^ 2 + y ^ 2 := by rw [hk, hm]
        _ = p ^ 2 := h
    have hkm : k ^ 2 + m ^ 2 = 1 := by
      have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
      exact (Nat.mul_right_inj hpos.ne').mp (by linarith [heq])
    have hkpos : 0 < k := by
      by_contra hk0
      have : k = 0 := by omega
      subst this
      simp at hk
      omega
    have hk1 : k = 1 := by
      have : k ≤ 1 := by nlinarith [hkm]
      omega
    subst hk1
    simp at hkm
    have : y = 0 := by simp [hm, hkm]
    omega
  · have hpy : ¬ p ∣ y := by
      intro hpy
      have hp2 : p ∣ x ^ 2 + y ^ 2 := by
        rw [h]; exact dvd_pow_self p (by decide)
      have hy2 : p ∣ y ^ 2 := dvd_pow hpy (by decide : 2 ≠ 0)
      have hx2 : p ∣ x ^ 2 := by
        have : (p : ℤ) ∣ (x : ℤ) ^ 2 := by
          have h1 : (p : ℤ) ∣ (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by
            exact_mod_cast hp2
          have h2 : (p : ℤ) ∣ (y : ℤ) ^ 2 := by
            exact_mod_cast hy2
          simpa using dvd_sub h1 h2
        exact_mod_cast this
      exact hpx (hp.dvd_of_dvd_pow hx2)
    have hx0 : (x : ZMod p) ≠ 0 := by
      intro hx0
      exact hpx ((ZMod.natCast_eq_zero_iff x p).mp hx0)
    have hy0 : (y : ZMod p) ≠ 0 := by
      intro hy0
      exact hpy ((ZMod.natCast_eq_zero_iff y p).mp hy0)
    have hsum0 : (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, h, Nat.cast_pow]
      simp
    have hsq : IsSquare (-1 : ZMod p) := by
      refine ⟨(x : ZMod p) * (y : ZMod p)⁻¹, ?_⟩
      field_simp [hy0]
      rw [neg_eq_iff_add_eq_zero, add_comm]
      exact hsum0
    have : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
    exact this h3

lemma not_two_squares_of_three_mod_four {p x y : ℕ}
    (hp : p.Prime) (h3 : p % 4 = 3) (h : x ^ 2 + y ^ 2 = p) : False := by
  have : ¬ ∃ a b, p = a ^ 2 + b ^ 2 := by
    intro hex
    have hiff := (Nat.eq_sq_add_sq_iff (n := p)).mp (by
      obtain ⟨a, b, hab⟩ := hex
      exact ⟨a, b, hab⟩)
    have hp_mem : p ∈ p.primeFactors := by
      simp [Nat.mem_primeFactors, hp, hp.ne_zero, hp.pos]
    have hEven : Even (padicValNat p p) := hiff p hp_mem h3
    have hval : padicValNat p p = 1 := padicValNat.self hp.one_lt
    rw [hval] at hEven
    exact Nat.not_even_one hEven
  exact this ⟨x, y, h.symm⟩

lemma quat_yz_zero {a b c d : ℕ}
    (hY : 2 * a * c + 2 * b * d = 0)
    (hZ : ((2 * a * d : ℤ) - 2 * b * c).natAbs = 0) :
    (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) := by
  have hacbd : a * c + b * d = 0 := by
    have : 2 * (a * c + b * d) = 0 := by
      convert hY using 1
      ring
    omega
  obtain ⟨hac, hbd⟩ := Nat.add_eq_zero.mp hacbd
  have hZeq : (2 * a * d : ℤ) = 2 * b * c := by
    have := Int.natAbs_eq_zero.mp hZ
    linarith
  have had_eq : a * d = b * c := by
    have : (a * d : ℤ) = b * c := by
      apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
      convert hZeq using 1 <;> ring
    exact_mod_cast this
  rcases Nat.mul_eq_zero.mp hac with ha | hc
  · rcases Nat.mul_eq_zero.mp hbd with hb | hd
    · exact Or.inl ⟨ha, hb⟩
    · subst ha; subst hd
      have : b * c = 0 := by simpa using had_eq
      rcases Nat.mul_eq_zero.mp this with hb | hc
      · exact Or.inl ⟨rfl, hb⟩
      · exact Or.inr ⟨hc, rfl⟩
  · rcases Nat.mul_eq_zero.mp hbd with hb | hd
    · subst hc; subst hb
      have : a * d = 0 := by simpa using had_eq
      rcases Nat.mul_eq_zero.mp this with ha | hd'
      · exact Or.inl ⟨ha, rfl⟩
      · exact Or.inr ⟨rfl, hd'⟩
    · exact Or.inr ⟨hc, hd⟩

lemma three_pos_sq_of_prime_sq {p a b c d : ℕ} (hp : p.Prime) (h3 : p % 4 = 3)
    (h4 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p) :
    ∃ X Y Z : ℕ, 0 < X ∧ 0 < Y ∧ 0 < Z ∧ X ^ 2 + Y ^ 2 + Z ^ 2 = p ^ 2 := by
  set X := ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 - (c : ℤ) ^ 2 - (d : ℤ) ^ 2).natAbs
  set Y := 2 * a * c + 2 * b * d
  set Z := ((2 * a * d : ℤ) - (2 * b * c : ℤ)).natAbs
  have hsum : X ^ 2 + Y ^ 2 + Z ^ 2 = p ^ 2 := by
    have := three_sq_of_sq_of_four a b c d
    simpa [X, Y, Z, h4] using this
  have hp_even_of_two : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 → False := by
    intro habcd
    have hpEq : p = 2 * (a ^ 2 + b ^ 2) := by linarith [h4, habcd]
    have hpEven : Even p := even_iff_two_dvd.mpr ⟨a ^ 2 + b ^ 2, hpEq⟩
    have hp2 : p = 2 :=
      hp.eq_two_or_odd'.resolve_right (Nat.not_odd_iff_even.mpr hpEven)
    omega
  have hXpos : 0 < X := by
    by_contra hX
    have hX0 : X = 0 := Nat.eq_zero_of_not_pos hX
    have habcd : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
      have : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 - (c : ℤ) ^ 2 - (d : ℤ) ^ 2) = 0 :=
        Int.natAbs_eq_zero.mp hX0
      exact_mod_cast (by linarith)
    exact hp_even_of_two habcd
  have hYpos : 0 < Y := by
    by_contra hY
    have hY0 : Y = 0 := Nat.eq_zero_of_not_pos hY
    by_cases hZ : Z = 0
    · rcases quat_yz_zero (by simpa [Y] using hY0) (by simpa [Z] using hZ) with h | h
      · obtain ⟨ha, hb⟩ := h
        subst ha; subst hb
        exact not_two_squares_of_three_mod_four hp h3 (by simpa using h4)
      · obtain ⟨hc, hd⟩ := h
        subst hc; subst hd
        exact not_two_squares_of_three_mod_four hp h3 (by simpa using h4)
    · exact not_two_pos_sq_hyp_three_mod_four hp h3
        (by simpa [hY0] using hsum) hXpos (Nat.pos_of_ne_zero hZ)
  have hZpos : 0 < Z := by
    by_contra hZ
    have hZ0 : Z = 0 := Nat.eq_zero_of_not_pos hZ
    exact not_two_pos_sq_hyp_three_mod_four hp h3
      (by simpa [hZ0] using hsum) hXpos hYpos
  exact ⟨X, Y, Z, hXpos, hYpos, hZpos, hsum⟩


lemma A273110_ge_two_of_three_pos {n X Y Z : ℕ}
    (hs : X ^ 2 + Y ^ 2 + Z ^ 2 = n)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    2 ≤ A273110 n := by
  have hn : 0 < n := by nlinarith
  rcases le_total Y X with hYX | hXY
  · rcases le_total Z Y with hZY | hYZ
    · exact A273110_ge_two_of_three_sq_not_pure hn hs ⟨hYX, hZY⟩
        (fun h => (hZ.ne' h.2.2).elim)
    · rcases le_total Z X with hZX | hXZ
      · exact A273110_ge_two_of_three_sq_not_pure hn (by linarith : X ^ 2 + Z ^ 2 + Y ^ 2 = n)
          ⟨hZX, hYZ⟩ (fun h => (hY.ne' h.2.2).elim)
      · exact A273110_ge_two_of_three_sq_not_pure hn (by linarith : Z ^ 2 + X ^ 2 + Y ^ 2 = n)
          ⟨hXZ, hYX⟩ (fun h => (hY.ne' h.2.2).elim)
  · rcases le_total Z X with hZX | hXZ
    · exact A273110_ge_two_of_three_sq_not_pure hn (by linarith : Y ^ 2 + X ^ 2 + Z ^ 2 = n)
        ⟨hXY, hZX⟩ (fun h => (hZ.ne' h.2.2).elim)
    · rcases le_total Z Y with hZY | hYZ
      · exact A273110_ge_two_of_three_sq_not_pure hn (by linarith : Y ^ 2 + Z ^ 2 + X ^ 2 = n)
          ⟨hZY, hXZ⟩ (fun h => (hX.ne' h.2.2).elim)
      · exact A273110_ge_two_of_three_sq_not_pure hn (by linarith : Z ^ 2 + Y ^ 2 + X ^ 2 = n)
          ⟨hYZ, hXY⟩ (fun h => (hX.ne' h.2.2).elim)

lemma A273110_ge_two_of_has_prime_three_mod_four {A p : ℕ}
    (hp : p.Prime) (h3 : p % 4 = 3) (hdvd : p ∣ A) (hA : 1 < A) :
    2 ≤ A273110 (A ^ 2) := by
  obtain ⟨M, hM⟩ := hdvd
  obtain ⟨a, b, c, d, h4⟩ := Nat.sum_four_squares p
  obtain ⟨X, Y, Z, hX, hY, hZ, hsum⟩ := three_pos_sq_of_prime_sq hp h3 h4
  have hMpos : 0 < M := by
    by_contra hM0
    have : M = 0 := Nat.eq_zero_of_not_pos hM0
    subst this
    simp at hM
    omega
  refine A273110_ge_two_of_three_pos (X := X * M) (Y := Y * M) (Z := Z * M) ?_
    (Nat.mul_pos hX hMpos) (Nat.mul_pos hY hMpos) (Nat.mul_pos hZ hMpos)
  calc
    (X * M) ^ 2 + (Y * M) ^ 2 + (Z * M) ^ 2
        = (X ^ 2 + Y ^ 2 + Z ^ 2) * M ^ 2 := by ring
    _ = p ^ 2 * M ^ 2 := by rw [hsum]
    _ = (p * M) ^ 2 := by ring
    _ = A ^ 2 := by rw [hM]

lemma prime_mod_four_one_or_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : p % 2 = 1 := by
    have : Odd p := hp.odd_of_ne_two hp2
    exact Nat.odd_iff.mp this
  have hlt : p % 4 < 4 := Nat.mod_lt p (by decide)
  interval_cases h4 : p % 4 <;> omega

lemma A273110_ge_two_of_odd_square {A : ℕ} (hA : 1 < A) (hodd : Odd A) :
    2 ≤ A273110 (A ^ 2) := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hA)
  have hp2 : p ≠ 2 := by
    intro hpeq
    subst hpeq
    have hEven : Even A := even_iff_two_dvd.mpr hpdvd
    exact Nat.not_even_iff_odd.mpr hodd hEven
  rcases prime_mod_four_one_or_three hp hp2 with h1 | h3
  · exact A273110_ge_two_of_has_prime_one_mod_four hp h1 hpdvd hA
  · exact A273110_ge_two_of_has_prime_three_mod_four hp h3 hpdvd hA


lemma A273110_ge_two_of_three_sq {n a b c : ℕ}
    (hn : 1 < n) (h4 : ¬ 4 ∣ n)
    (hs : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    2 ≤ A273110 n := by
  obtain ⟨A, B, C, hAB, hBC, hs'⟩ := exists_sorted_of_three_sq hs
  by_cases hpure : 0 < A ∧ B = 0 ∧ C = 0
  · obtain ⟨hA, hB0, hC0⟩ := hpure
    subst hB0; subst hC0
    have hnA : n = A ^ 2 := by linarith
    rw [hnA]
    have hA1 : 1 < A := by
      have hAne : A ≠ 1 := by
        intro hAeq
        subst hAeq
        simp at hnA
        omega
      omega
    have hAodd : Odd A := by
      by_contra heven
      rw [Nat.not_odd_iff_even] at heven
      obtain ⟨k, hk⟩ := even_iff_two_dvd.mp heven
      have : 4 ∣ A ^ 2 := by
        rw [hk]
        exact ⟨k ^ 2, by ring⟩
      exact h4 (by rwa [hnA])
    exact A273110_ge_two_of_odd_square hA1 hAodd
  · exact A273110_ge_two_of_three_sq_not_pure (lt_trans Nat.zero_lt_one hn) hs'
      ⟨hAB, hBC⟩ hpure

lemma exists_four_free {n : ℕ} (hn : 0 < n) :
    ∃ k m, n = 4 ^ k * m ∧ ¬ 4 ∣ m ∧ 0 < m := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h4 : 4 ∣ n
    · obtain ⟨n', rfl⟩ := h4
      have hn'pos : 0 < n' := by
        by_contra h0
        have : n' = 0 := Nat.eq_zero_of_not_pos h0
        subst this
        simp at hn
      have hn'lt : n' < 4 * n' := by nlinarith
      obtain ⟨k, m, hkm, hm, hmpos⟩ := ih n' hn'lt hn'pos
      refine ⟨k + 1, m, ?_, hm, hmpos⟩
      rw [pow_succ, mul_comm (4 ^ k), mul_assoc, hkm]
    · exact ⟨0, n, by simp, h4, hn⟩

lemma not_forbidden_of_not_seven {m : ℕ} (h4 : ¬ 4 ∣ m) (h7 : m % 8 ≠ 7) :
    ¬ ∃ k t, m = 4 ^ k * (8 * t + 7) := by
  rintro ⟨k, t, hkt⟩
  have hk0 : k = 0 := by
    by_contra hkpos
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (by omega)
    have hdiv : 4 ∣ 4 ^ k := ⟨4 ^ (k - 1), by
      rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel hk1]⟩
    have : 4 ∣ m := by
      rw [hkt]
      exact dvd_mul_of_dvd_left hdiv _
    exact h4 this
  subst hk0
  simp at hkt
  have : m % 8 = 7 := by
    rw [hkt]
    omega
  exact h7 this
