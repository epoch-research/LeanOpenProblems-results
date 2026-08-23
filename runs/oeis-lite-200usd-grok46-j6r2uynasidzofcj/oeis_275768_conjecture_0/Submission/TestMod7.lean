import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma zmod7_two_ne_zero : (2 : ZMod 7) ≠ 0 := by decide

lemma two_n_ne_zero_mod_seven {n : ZMod 7} (hn : n ≠ 0) : (2 : ZMod 7) * n ≠ 0 := by
  fin_cases n <;> first | exact (hn rfl).elim | decide

lemma n_ne_neg_n_mod_seven {n : ZMod 7} (hn : n ≠ 0) : n ≠ -n := by
  intro h
  apply two_n_ne_zero_mod_seven hn
  have := congrArg (fun x => x + n) h
  simpa [two_mul] using this

lemma card_pair_zmod7 {a b : ZMod 7} (h : a ≠ b) : #({a, b} : Finset (ZMod 7)) = 2 := by
  rw [card_insert_of_notMem, card_singleton]
  simpa using h

lemma card_triple_zmod7 {a b c : ZMod 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    #({a, b, c} : Finset (ZMod 7)) = 3 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simpa using hbc
  · simp [hab, hac]

lemma card_quad_zmod7 {a b c d : ZMod 7}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    #({a, b, c, d} : Finset (ZMod 7)) = 4 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simpa using hcd
  · simp [hbc, hbd]
  · simp [hab, hac, had]

lemma sum_univ_zmod7 : (∑ x : ZMod 7, x) = 0 := by decide

lemma sum_forbidden_zmod7 (n : ZMod 7) : (∑ x ∈ ({0, n, -n} : Finset (ZMod 7)), x) = 0 := by
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases hnn : n = -n
    · have := n_ne_neg_n_mod_seven h0 hnn
      contradiction
    · rw [sum_insert, sum_insert, sum_singleton]
      · ring
      · simpa using hnn
      · simpa [Ne.symm h0] using h0

/-- If four distinct residues avoid `{0, n, -n}` in `ZMod 7` (with `n ≠ 0`),
they occupy the whole complement and therefore sum to `0`. -/
lemma four_allowed_residues_sum_zero
    (n a b c d : ZMod 7)
    (hn : n ≠ 0)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (han : a ≠ n) (hbn : b ≠ n) (hcn : c ≠ n) (hdn : d ≠ n)
    (hann : a ≠ -n) (hbnn : b ≠ -n) (hcnn : c ≠ -n) (hdnn : d ≠ -n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    a + b + c + d = 0 := by
  let S : Finset (ZMod 7) := {a, b, c, d}
  let F : Finset (ZMod 7) := {0, n, -n}
  have hFn : n ≠ -n := n_ne_neg_n_mod_seven hn
  have hF0n : (0 : ZMod 7) ≠ n := by intro h; exact hn h.symm
  have hF0nn : (0 : ZMod 7) ≠ -n := by
    intro h
    have : n = 0 := neg_eq_zero.mp h.symm
    exact hn this
  have hcardF : #F = 3 := card_triple_zmod7 hF0n hF0nn hFn
  have hcardS : #S = 4 := card_quad_zmod7 hab hac had hbc hbd hcd
  have hcard_compl : #(univ \ F) = 4 := by
    rw [card_sdiff_of_subset (subset_univ _), hcardF]
    have : #(univ : Finset (ZMod 7)) = 7 := by decide
    omega
  have hsub : S ⊆ univ \ F := by
    intro x hx
    simp only [mem_sdiff, mem_univ, true_and]
    intro hF
    simp only [F, mem_insert, mem_singleton] at hF
    simp only [S, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hF with rfl | rfl | rfl <;> contradiction
  have hSF : S = univ \ F :=
    eq_of_subset_of_card_le hsub (by simp [hcardS, hcard_compl])
  have hsumS : (∑ x ∈ S, x) = a + b + c + d := by
    simp only [S]
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · ring
    · simp [hcd]
    · simp [hbc, hbd]
    · simp [hab, hac, had]
  have hsum_compl : (∑ x ∈ univ \ F, x) = 0 := by
    have hss : (∑ x ∈ (univ : Finset (ZMod 7)) \ F, x) =
        (∑ x ∈ univ, x) - ∑ x ∈ F, x :=
      sum_sdiff_eq_sub (subset_univ F)
    rw [hss, sum_univ_zmod7, sum_forbidden_zmod7 n, sub_zero]
  rw [← hsumS, hSF, hsum_compl]

lemma two_diamonds_cast_sub {n r : ℕ} (hrle : r ≤ n) :
    ((n - r : ℕ) : ZMod 7) = (n : ZMod 7) - r :=
  Nat.cast_sub hrle

lemma two_diamonds_sum_eq_two_n {n r s : ℕ} (hrle : r ≤ n) (hsle : s ≤ n) :
    (r : ZMod 7) + ((n - r : ℕ) : ZMod 7) +
      (s : ZMod 7) + ((n - s : ℕ) : ZMod 7) = (2 : ZMod 7) * n := by
  rw [two_diamonds_cast_sub hrle, two_diamonds_cast_sub hsle]
  ring

/-- Two pairing orbits cannot occupy four distinct allowed residues modulo 7. -/
lemma two_diamonds_residues_not_all_distinct_mod_seven
    {n r s : ℕ} (hrle : r ≤ n) (hsle : s ≤ n)
    (hn7 : (n : ZMod 7) ≠ 0)
    (hr0 : (r : ZMod 7) ≠ 0) (hs0 : (s : ZMod 7) ≠ 0)
    (hrn : (r : ZMod 7) ≠ n) (hsn : (s : ZMod 7) ≠ n)
    (hrnn : (r : ZMod 7) ≠ -n) (hsnn : (s : ZMod 7) ≠ -n)
    (hnr0 : ((n - r : ℕ) : ZMod 7) ≠ 0) (hns0 : ((n - s : ℕ) : ZMod 7) ≠ 0)
    (hnrn : ((n - r : ℕ) : ZMod 7) ≠ n) (hnsn : ((n - s : ℕ) : ZMod 7) ≠ n)
    (hnrnn : ((n - r : ℕ) : ZMod 7) ≠ -n) (hnsnn : ((n - s : ℕ) : ZMod 7) ≠ -n)
    (hrs : (r : ZMod 7) ≠ s)
    (hrns : (r : ZMod 7) ≠ (n - s : ℕ))
    (hrnr : (r : ZMod 7) ≠ (n - r : ℕ))
    (hsns : (s : ZMod 7) ≠ (n - s : ℕ))
    (hnrns : ((n - r : ℕ) : ZMod 7) ≠ (n - s : ℕ))
    (hnrs : ((n - r : ℕ) : ZMod 7) ≠ s) :
    False := by
  have hsum0 := four_allowed_residues_sum_zero (n : ZMod 7)
    (r : ZMod 7) ((n - r : ℕ) : ZMod 7) (s : ZMod 7) ((n - s : ℕ) : ZMod 7)
    hn7 hr0 hnr0 hs0 hns0
    hrn hnrn hsn hnsn
    hrnn hnrnn hsnn hnsnn
    hrnr hrs hrns hnrs hnrns hsns
  have hsum2 := two_diamonds_sum_eq_two_n hrle hsle
  have h2n := two_n_ne_zero_mod_seven hn7
  exact h2n (hsum2 ▸ hsum0)

lemma natCast_zmod7_ne_zero {m : ℕ} (h : ¬ 7 ∣ m) : (m : ZMod 7) ≠ 0 := by
  intro h0
  exact h ((ZMod.natCast_eq_zero_iff m 7).mp h0)

lemma prime_ne_seven_cast {p : ℕ} (hp : p.Prime) (h7 : p ≠ 7) : (p : ZMod 7) ≠ 0 := by
  intro h0
  have : 7 ∣ p := (ZMod.natCast_eq_zero_iff p 7).mp h0
  have : 7 = p := (prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hp).mp this
  exact h7 this.symm

lemma dvd_prime_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ∣ q) : p = q :=
  (prime_dvd_prime_iff_eq hp hq).mp h

/-- If eight diamond values are primes larger than 7 and `7 ∤ n`, the two
orbits collide modulo 7. -/
lemma diamonds_collide_mod_seven
    {n r s : ℕ} (hrle : r ≤ n) (hsle : s ≤ n)
    (hn7 : ¬ 7 ∣ n)
    (hrP : r.Prime) (hsP : s.Prime)
    (hnrP : (n - r).Prime) (hnsP : (n - s).Prime)
    (hsumrP : (n + r).Prime) (hsumsP : (n + s).Prime)
    (h2nrP : (2 * n - r).Prime) (h2nsP : (2 * n - s).Prime)
    (hrne7 : r ≠ 7) (hsne7 : s ≠ 7)
    (hnrne7 : n - r ≠ 7) (hnsne7 : n - s ≠ 7)
    (hsumrne7 : n + r ≠ 7) (hsumsne7 : n + s ≠ 7)
    (h2nrne7 : 2 * n - r ≠ 7) (h2nsne7 : 2 * n - s ≠ 7) :
    (r : ZMod 7) = s ∨ (r : ZMod 7) = ((n - s : ℕ) : ZMod 7) ∨
    (r : ZMod 7) = ((n - r : ℕ) : ZMod 7) ∨
    (s : ZMod 7) = ((n - s : ℕ) : ZMod 7) := by
  have hn7Z := natCast_zmod7_ne_zero hn7
  have not7 {p : ℕ} (hp : p.Prime) (hne7 : p ≠ 7) : (p : ZMod 7) ≠ 0 := by
    intro h0
    have : 7 ∣ p := (ZMod.natCast_eq_zero_iff p 7).mp h0
    have heq : 7 = p :=
      (prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hp).mp this
    exact hne7 heq.symm
  have hr0 := not7 hrP hrne7
  have hs0 := not7 hsP hsne7
  have hnr0 := not7 hnrP hnrne7
  have hns0 := not7 hnsP hnsne7
  have hrn : (r : ZMod 7) ≠ n := by
    intro h
    apply hnr0
    rw [Nat.cast_sub hrle, h, sub_self]
  have hsn : (s : ZMod 7) ≠ n := by
    intro h
    apply hns0
    rw [Nat.cast_sub hsle, h, sub_self]
  have hrnn : (r : ZMod 7) ≠ -n := by
    intro h
    have : ((n + r : ℕ) : ZMod 7) = 0 := by push_cast; simp [h]
    exact not7 hsumrP hsumrne7 this
  have hsnn : (s : ZMod 7) ≠ -n := by
    intro h
    have : ((n + s : ℕ) : ZMod 7) = 0 := by push_cast; simp [h]
    exact not7 hsumsP hsumsne7 this
  have hnrn : ((n - r : ℕ) : ZMod 7) ≠ n := by
    intro h
    apply hr0
    have h' : (n : ZMod 7) - ((n - r : ℕ) : ZMod 7) = 0 := by rw [h, sub_self]
    rw [Nat.cast_sub hrle] at h'
    -- n - (n - r) = r
    simpa using h'
  have hnsn : ((n - s : ℕ) : ZMod 7) ≠ n := by
    intro h
    apply hs0
    have h' : (n : ZMod 7) - ((n - s : ℕ) : ZMod 7) = 0 := by rw [h, sub_self]
    rw [Nat.cast_sub hsle] at h'
    simpa using h'
  have h2rle : r ≤ 2 * n := by omega
  have h2sle : s ≤ 2 * n := by omega
  have hnrnn : ((n - r : ℕ) : ZMod 7) ≠ -n := by
    intro h
    have hcast : ((2 * n - r : ℕ) : ZMod 7) =
        (n : ZMod 7) + ((n - r : ℕ) : ZMod 7) := by
      rw [Nat.cast_sub h2rle, Nat.cast_sub hrle, Nat.cast_mul, Nat.cast_two]
      simp [sub_eq_add_neg, two_mul]; ac_rfl
    have : ((2 * n - r : ℕ) : ZMod 7) = 0 := by
      rw [hcast, h]; abel
    exact not7 h2nrP h2nrne7 this
  have hnsnn : ((n - s : ℕ) : ZMod 7) ≠ -n := by
    intro h
    have hcast : ((2 * n - s : ℕ) : ZMod 7) =
        (n : ZMod 7) + ((n - s : ℕ) : ZMod 7) := by
      rw [Nat.cast_sub h2sle, Nat.cast_sub hsle, Nat.cast_mul, Nat.cast_two]
      simp [sub_eq_add_neg, two_mul]; ac_rfl
    have : ((2 * n - s : ℕ) : ZMod 7) = 0 := by
      rw [hcast, h]; abel
    exact not7 h2nsP h2nsne7 this
  by_contra hnone
  simp only [not_or] at hnone
  obtain ⟨hrs, hrns, hrnr, hsns⟩ := hnone
  have hnrns : ((n - r : ℕ) : ZMod 7) ≠ (n - s : ℕ) := by
    intro h
    apply hrs
    rw [Nat.cast_sub hrle, Nat.cast_sub hsle] at h
    -- n-r = n-s ⇒ r = s
    have : -(r : ZMod 7) = -s := by
      simpa using h
    exact neg_injective this
  have hnrs : ((n - r : ℕ) : ZMod 7) ≠ s := by
    intro h
    apply hrns
    rw [Nat.cast_sub hrle] at h
    rw [Nat.cast_sub hsle]
    apply eq_sub_of_add_eq
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp h).symm
  exact two_diamonds_residues_not_all_distinct_mod_seven hrle hsle hn7Z
    hr0 hs0 hrn hsn hrnn hsnn hnr0 hns0 hnrn hnsn hnrnn hnsnn
    hrs hrns hrnr hsns hnrns hnrs
