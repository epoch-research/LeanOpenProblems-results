import FormalConjectures.Util.ProblemImports

open Finset Nat

set_option maxRecDepth 400000
set_option maxHeartbeats 400000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/--
A355228: $a(n)$ is the smallest integer $m$ such that there exist $n$ of its distinct divisors $(d_1, d_2, \dots, d_n)$ with the property that $m = d_1 + d_2 + \dots + d_n = \operatorname{lcm}(d_1, d_2, \dots, d_n)$, or 0 if no such number $m$ exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m ∧
        D.lcm id = m }
  sInf candidates

-- A081512: Smallest number $m$ such that $m$ is the sum of $n$ distinct divisors $d_1, \dots, d_n$ of $m$.
noncomputable def a081512 (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m }
  sInf candidates

def HasSumN (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ m.divisors.powerset, D.card = n ∧ D.sum id = m

def HasSumNLcm (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ m.divisors.powerset, D.card = n ∧ D.sum id = m ∧ D.lcm id = m

instance (n m : ℕ) : Decidable (HasSumN n m) := by
  unfold HasSumN; infer_instance

instance (n m : ℕ) : Decidable (HasSumNLcm n m) := by
  unfold HasSumNLcm; infer_instance

lemma HasSumN_iff (n m : ℕ) :
    HasSumN n m ↔ 0 < m ∧ ∃ D : Finset ℕ,
      D ⊆ m.divisors ∧ D.card = n ∧ D.sum id = m := by
  simp [HasSumN, Finset.mem_powerset]

lemma HasSumNLcm_iff (n m : ℕ) :
    HasSumNLcm n m ↔ 0 < m ∧ ∃ D : Finset ℕ,
      D ⊆ m.divisors ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m := by
  simp [HasSumNLcm, Finset.mem_powerset]

lemma candidates081512_eq (n : ℕ) :
    { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m } =
    { m : ℕ | HasSumN n m } := by
  ext m; simp [HasSumN_iff]

lemma candidatesA_eq (n : ℕ) :
    { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧
        D.sum id = m ∧ D.lcm id = m } =
    { m : ℕ | HasSumNLcm n m } := by
  ext m; simp [HasSumNLcm_iff]

lemma a081512_eq (n : ℕ) : a081512 n = sInf { m : ℕ | HasSumN n m } := by
  simp only [a081512, candidates081512_eq]

lemma a_eq (n : ℕ) : a n = sInf { m : ℕ | HasSumNLcm n m } := by
  simp only [a, candidatesA_eq]

lemma a081512_le_of_has {n m : ℕ} (h : HasSumN n m) : a081512 n ≤ m := by
  rw [a081512_eq]; exact csInf_le' h

lemma a_le_of_has {n m : ℕ} (h : HasSumNLcm n m) : a n ≤ m := by
  rw [a_eq]; exact csInf_le' h

lemma a081512_eq_zero_of_forall {n : ℕ} (h : ∀ m, ¬ HasSumN n m) : a081512 n = 0 := by
  rw [a081512_eq]
  have : { m : ℕ | HasSumN n m } = ∅ := by
    ext m; simp [h m]
  simp [this]

lemma a_eq_zero_of_forall {n : ℕ} (h : ∀ m, ¬ HasSumNLcm n m) : a n = 0 := by
  rw [a_eq]
  have : { m : ℕ | HasSumNLcm n m } = ∅ := by
    ext m; simp [h m]
  simp [this]

lemma a081512_eq_of {n m : ℕ} (hwit : HasSumN n m)
    (hmin : ∀ k : Fin m, ¬ HasSumN n k.val) : a081512 n = m := by
  apply le_antisymm
  · exact a081512_le_of_has hwit
  · rw [a081512_eq]
    have hne : { k : ℕ | HasSumN n k }.Nonempty := ⟨m, hwit⟩
    have hmem : HasSumN n (sInf { k : ℕ | HasSumN n k }) := Nat.sInf_mem hne
    have hnotlt : ¬ sInf { k : ℕ | HasSumN n k } < m := fun hlt =>
      hmin ⟨sInf { k : ℕ | HasSumN n k }, hlt⟩ hmem
    exact Nat.le_of_not_gt hnotlt

lemma a_eq_of {n m : ℕ} (hwit : HasSumNLcm n m)
    (hmin : ∀ k : Fin m, ¬ HasSumNLcm n k.val) : a n = m := by
  apply le_antisymm
  · exact a_le_of_has hwit
  · rw [a_eq]
    have hne : { k : ℕ | HasSumNLcm n k }.Nonempty := ⟨m, hwit⟩
    have hmem : HasSumNLcm n (sInf { k : ℕ | HasSumNLcm n k }) := Nat.sInf_mem hne
    have hnotlt : ¬ sInf { k : ℕ | HasSumNLcm n k } < m := fun hlt =>
      hmin ⟨sInf { k : ℕ | HasSumNLcm n k }, hlt⟩ hmem
    exact Nat.le_of_not_gt hnotlt

lemma hasSumN_of_hasSumNLcm {n m : ℕ} (h : HasSumNLcm n m) : HasSumN n m := by
  rw [HasSumNLcm_iff] at h
  rw [HasSumN_iff]
  exact ⟨h.1, h.2.imp fun D ⟨hD, hc, hs, _⟩ => ⟨hD, hc, hs⟩⟩

lemma not_mem_of_hasSumN {n k : ℕ} {D : Finset ℕ}
    (hn : 2 ≤ n) (hD : D ⊆ k.divisors) (hc : D.card = n) (hs : D.sum id = k) :
    k ∉ D := by
  intro hkD
  have hsum : D.sum id = (D.erase k).sum id + k := by
    rw [← sum_erase_add D id hkD]; simp [id]
  have herase : D.erase k = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
    have hxD : x ∈ D := mem_of_mem_erase hx
    have hxpos : 0 < x := pos_of_mem_divisors (hD hxD)
    have : 0 < (D.erase k).sum id :=
      Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x, hx, hxpos⟩
    omega
  have hcard : D.card = 1 := by
    have := congrArg card herase
    simp [card_erase_of_mem hkD] at this
    omega
  omega

lemma not_hasSumN_zero (m : ℕ) : ¬ HasSumN 0 m := by
  rw [HasSumN_iff]
  rintro ⟨hm, D, hD, hc, hs⟩
  have : D = ∅ := card_eq_zero.mp hc
  subst this
  simp at hs
  exact hm.ne' hs.symm

lemma a081512_zero : a081512 0 = 0 :=
  a081512_eq_zero_of_forall not_hasSumN_zero

lemma not_hasSumNLcm_zero (m : ℕ) : ¬ HasSumNLcm 0 m := fun h =>
  not_hasSumN_zero m (hasSumN_of_hasSumNLcm h)

lemma a_zero : a 0 = 0 := a_eq_zero_of_forall not_hasSumNLcm_zero

lemma hasSumNLcm_one : HasSumNLcm 1 1 := by decide
lemma a081512_one : a081512 1 = 1 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_one) (by decide)
lemma a_one : a 1 = 1 := a_eq_of hasSumNLcm_one (by decide)

lemma not_hasSumN_two (m : ℕ) : ¬ HasSumN 2 m := by
  rw [HasSumN_iff]
  rintro ⟨hm, D, hD, hc, hs⟩
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hc
  simp [sum_pair hxy] at hs
  have hx := hD (by simp : x ∈ ({x, y} : Finset ℕ))
  have hy := hD (by simp : y ∈ ({x, y} : Finset ℕ))
  have hxd := dvd_of_mem_divisors hx
  have hyd := dvd_of_mem_divisors hy
  have hxy_dvd : x ∣ y :=
    (Nat.dvd_add_right (dvd_refl x)).1 (by simpa [hs] using hxd)
  have hyx_dvd : y ∣ x :=
    (Nat.dvd_add_left (dvd_refl y)).1 (by simpa [hs] using hyd)
  exact hxy (Nat.dvd_antisymm hxy_dvd hyx_dvd)

lemma a081512_two : a081512 2 = 0 := a081512_eq_zero_of_forall not_hasSumN_two
lemma not_hasSumNLcm_two (m : ℕ) : ¬ HasSumNLcm 2 m := fun h =>
  not_hasSumN_two m (hasSumN_of_hasSumNLcm h)
lemma a_two : a 2 = 0 := a_eq_zero_of_forall not_hasSumNLcm_two

lemma a081512_three : a081512 3 = 6 := a081512_eq_of (by decide) (by decide)
lemma a_three : a 3 = 6 := a_eq_of (by decide) (by decide)
lemma a081512_four : a081512 4 = 12 := a081512_eq_of (by decide) (by decide)
lemma a_four : a 4 = 18 := a_eq_of (by decide) (by decide)
lemma a081512_five : a081512 5 = 24 := a081512_eq_of (by decide) (by decide)
lemma a_five : a 5 = 28 := a_eq_of (by decide) (by decide)
lemma a081512_six : a081512 6 = 24 := a081512_eq_of (by decide) (by decide)
lemma a_six : a 6 = 24 := a_eq_of (by decide) (by decide)
lemma a081512_seven : a081512 7 = 48 := a081512_eq_of (by decide) (by decide)
lemma a_seven : a 7 = 48 := a_eq_of (by decide) (by decide)

lemma not_lt_of_eq_seq {n : ℕ} (h : a n = a081512 n) : ¬ a n > a081512 n := by omega
lemma not_lt_of_le_seq {n : ℕ} (h : a n ≤ a081512 n) : ¬ a n > a081512 n := by omega

lemma hasSumNLcm_of_explicit (n m : ℕ) (D : Finset ℕ)
    (hD : D ⊆ m.divisors) (hc : D.card = n) (hs : D.sum id = m)
    (hl : D.lcm id = m) (hm : 0 < m) : HasSumNLcm n m := by
  rw [HasSumNLcm_iff]
  exact ⟨hm, D, hD, hc, hs, hl⟩

lemma subset_divisors_of_forall_dvd {m : ℕ} {D : Finset ℕ} (hm : 0 < m)
    (h : ∀ d ∈ D, d ∣ m) : D ⊆ m.divisors := by
  intro d hd
  exact mem_divisors.2 ⟨h d hd, hm.ne'⟩

lemma hasSumNLcm_of_dvd (n m : ℕ) (D : Finset ℕ)
    (hdiv : ∀ d ∈ D, d ∣ m) (hc : D.card = n) (hs : D.sum id = m)
    (hl : D.lcm id = m) (hm : 0 < m) : HasSumNLcm n m :=
  hasSumNLcm_of_explicit n m D (subset_divisors_of_forall_dvd hm hdiv) hc hs hl hm

lemma mem_properDivisors_of_hasSumN {n k : ℕ} {D : Finset ℕ}
    (hn : 2 ≤ n) (hD : D ⊆ k.divisors) (hc : D.card = n) (hs : D.sum id = k) :
    D ⊆ k.properDivisors := by
  intro x hx
  have hxD := hD hx
  have hxne : x ≠ k := fun h => (not_mem_of_hasSumN hn hD hc hs) (h ▸ hx)
  exact Nat.mem_properDivisors.2 ⟨dvd_of_mem_divisors hxD, lt_of_le_of_ne (divisor_le hxD) hxne⟩

lemma properDivisor_le_div_two {k d : ℕ} (hd : d ∈ k.properDivisors) : d ≤ k / 2 := by
  obtain ⟨q, hq, hkq⟩ := (Nat.mem_properDivisors_iff_exists (by
    have : 1 < k := Nat.one_lt_of_mem_properDivisors hd
    omega)).1 hd
  have hdpos : 0 < d := Nat.pos_of_mem_properDivisors hd
  have : d * 2 ≤ d * q := Nat.mul_le_mul_left d hq
  rw [← hkq] at this
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by simpa [mul_comm] using this)

lemma sum_le_card_mul {s : Finset ℕ} {M : ℕ} (h : ∀ x ∈ s, x ≤ M) :
    s.sum id ≤ s.card * M := by
  calc
    s.sum id ≤ s.sum (fun _ => M) := sum_le_sum (fun x hx => h x hx)
    _ = s.card * M := by simp [sum_const, smul_eq_mul]

lemma proper_card {k : ℕ} (hk : k ≠ 0) :
    k.properDivisors.card = k.divisors.card - 1 := by
  have := congrArg card (Nat.insert_self_properDivisors hk)
  rw [card_insert_of_notMem Nat.self_notMem_properDivisors] at this
  omega

lemma proper_sum {k : ℕ} (hk : k ≠ 0) :
    k.properDivisors.sum id + k = k.divisors.sum id := by
  have hdis : Disjoint k.properDivisors {k} :=
    disjoint_singleton_right.2 Nat.self_notMem_properDivisors
  have hun : k.properDivisors ∪ {k} = k.divisors := by
    rw [union_comm, ← insert_eq]
    exact Nat.insert_self_properDivisors hk
  have hsum := sum_union (f := id) hdis
  rw [hun] at hsum
  simpa [sum_singleton, id] using hsum.symm

lemma mem_sdiff_left {α : Type*} [DecidableEq α] {s t : Finset α} {x : α}
    (h : x ∈ s \ t) : x ∈ s := (mem_sdiff.mp h).1

lemma sum_sdiff_proper {k : ℕ} {D : Finset ℕ} (hne : k ≠ 0)
    (hsub : D ⊆ k.properDivisors) (hsum : D.sum id = k) :
    (k.properDivisors \ D).sum id + 2 * k = k.divisors.sum id := by
  have h1 : (k.properDivisors \ D).sum id + D.sum id = k.properDivisors.sum id := by
    simpa [id] using sum_sdiff hsub
  have hσ : k.properDivisors.sum id + k = k.divisors.sum id := proper_sum hne
  calc
    (k.properDivisors \ D).sum id + 2 * k
        = ((k.properDivisors \ D).sum id + D.sum id) + k := by
          rw [hsum, two_mul]; ac_rfl
    _ = k.properDivisors.sum id + k := by rw [h1]
    _ = k.divisors.sum id := hσ

lemma not_hasSumN_of_excess_half {n k : ℕ} (hn : 2 ≤ n)
    (hnτ : n + 1 ≤ k.divisors.card)
    (hE : k.divisors.sum id > 2 * k + (k.divisors.card - 1 - n) * (k / 2)) :
    ¬ HasSumN n k := by
  intro hs
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hk, D, hD, hc, hsum⟩
  have hsub : D ⊆ k.properDivisors := mem_properDivisors_of_hasSumN hn hD hc hsum
  have hne : k ≠ 0 := hk.ne'
  have hXcard : (k.properDivisors \ D).card = k.divisors.card - 1 - n := by
    have := card_sdiff_of_subset hsub
    have := proper_card hne
    omega
  have hle : (k.properDivisors \ D).sum id ≤ (k.properDivisors \ D).card * (k / 2) :=
    sum_le_card_mul (fun x hx => properDivisor_le_div_two (mem_sdiff_left hx))
  have hsumX : (k.properDivisors \ D).sum id + 2 * k = k.divisors.sum id :=
    sum_sdiff_proper hne hsub hsum
  have hbound : (k.properDivisors \ D).sum id ≤
      (k.divisors.card - 1 - n) * (k / 2) := by
    rw [← hXcard]; exact hle
  have : k.divisors.sum id ≤ 2 * k + (k.divisors.card - 1 - n) * (k / 2) := by
    rw [← hsumX]
    have := Nat.add_le_add_right hbound (2 * k)
    simpa [add_comm] using this
  omega

lemma not_hasSumN_all_proper {n k : ℕ} (hn2 : 2 ≤ n)
    (hn : n + 1 = k.divisors.card)
    (hE : k.divisors.sum id ≠ 2 * k) :
    ¬ HasSumN n k := by
  intro hs
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hk, D, hD, hc, hsum⟩
  have hsub : D ⊆ k.properDivisors := mem_properDivisors_of_hasSumN hn2 hD hc hsum
  have hne : k ≠ 0 := hk.ne'
  have hDeq : D = k.properDivisors := by
    apply Finset.eq_of_subset_of_card_le hsub
    have := proper_card hne
    omega
  have : k.divisors.sum id = 2 * k := by
    have hps := proper_sum hne
    rw [hDeq] at hsum
    rw [hsum] at hps
    simpa [two_mul] using hps.symm
  exact hE this

lemma properDivisor_eq_div_two_of_gt_third {k d : ℕ}
    (hd : d ∈ k.properDivisors) (hgt : k / 3 < d) : d = k / 2 := by
  obtain ⟨q, hq, hkq⟩ := (Nat.mem_properDivisors_iff_exists (by
    have : 1 < k := Nat.one_lt_of_mem_properDivisors hd
    omega)).1 hd
  have hdpos : 0 < d := Nat.pos_of_mem_properDivisors hd
  have hk_lt : k < 3 * d := by
    have := (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).1 hgt
    simpa [mul_comm] using this
  have : d * q < d * 3 := by rw [← hkq]; simpa [mul_comm] using hk_lt
  have hqlt : q < 3 := Nat.lt_of_mul_lt_mul_left this
  have hq2 : q = 2 := by omega
  subst hq2
  exact (Nat.div_eq_of_eq_mul_left (by decide : 0 < 2) hkq).symm

lemma not_hasSumN_of_excess_half_third {n k : ℕ} (hn : 2 ≤ n)
    (hr : n + 2 ≤ k.divisors.card)
    (hE : k.divisors.sum id >
      2 * k + k / 2 + (k.divisors.card - 1 - n - 1) * (k / 3)) :
    ¬ HasSumN n k := by
  intro hs
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hk, D, hD, hc, hsum⟩
  have hsub : D ⊆ k.properDivisors := mem_properDivisors_of_hasSumN hn hD hc hsum
  have hne : k ≠ 0 := hk.ne'
  have hX : (k.properDivisors \ D).card = k.divisors.card - 1 - n := by
    have := card_sdiff_of_subset hsub
    have := proper_card hne
    omega
  have hrpos : 1 ≤ k.divisors.card - 1 - n := by omega
  let X := k.properDivisors \ D
  have hXcard : X.card = k.divisors.card - 1 - n := hX
  have hXle : X.sum id ≤ k / 2 + (X.card - 1) * (k / 3) := by
    by_cases hbig : ∃ x ∈ X, k / 3 < x
    · rcases hbig with ⟨x, hx, hxt⟩
      have hxeq : x = k / 2 := properDivisor_eq_div_two_of_gt_third (mem_sdiff_left hx) hxt
      have hx2 : k / 2 ∈ X := by simpa [hxeq] using hx
      have hrest : ∀ y ∈ X.erase (k / 2), y ≤ k / 3 := by
        intro y hy
        have hyX : y ∈ X := mem_of_mem_erase hy
        have : ¬ k / 3 < y := by
          intro hgt
          have hyeq : y = k / 2 := properDivisor_eq_div_two_of_gt_third (mem_sdiff_left hyX) hgt
          exact (ne_of_mem_erase hy) hyeq
        omega
      have hsumX : X.sum id = (X.erase (k / 2)).sum id + k / 2 := by
        have := sum_erase_add (s := X) (f := id) hx2
        simp [id] at this
        exact this.symm
      have hleRest : (X.erase (k / 2)).sum id ≤ (X.erase (k / 2)).card * (k / 3) :=
        sum_le_card_mul hrest
      have hcardE : (X.erase (k / 2)).card = X.card - 1 := card_erase_of_mem hx2
      have hle2 : (X.erase (k / 2)).sum id ≤ (X.card - 1) * (k / 3) := by
        rw [← hcardE]; exact hleRest
      have : X.sum id ≤ (X.card - 1) * (k / 3) + k / 2 := by
        rw [hsumX]; exact Nat.add_le_add_right hle2 _
      omega
    · have hrest : ∀ y ∈ X, y ≤ k / 3 := by
        intro y hy; have : ¬ k / 3 < y := fun h => hbig ⟨y, hy, h⟩; omega
      have hle0 : X.sum id ≤ X.card * (k / 3) := sum_le_card_mul hrest
      have hle13 : k / 3 ≤ k / 2 := Nat.div_le_div_left (by decide : 2 ≤ 3) (by decide)
      have hcpos : 1 ≤ X.card := by
        have : X.card = k.divisors.card - 1 - n := hXcard
        omega
      have hsplit : X.card * (k / 3) = (X.card - 1) * (k / 3) + k / 3 := by
        have : X.card = (X.card - 1) + 1 := by omega
        rw [this, add_mul]; simp
      omega
  have hsumX : X.sum id + 2 * k = k.divisors.sum id := by
    simpa [X] using sum_sdiff_proper hne hsub hsum
  have hcard' : X.card - 1 = k.divisors.card - 1 - n - 1 := by omega
  have hXle' : X.sum id ≤ k / 2 + (k.divisors.card - 1 - n - 1) * (k / 3) := by
    rw [← hcard']; exact hXle
  have : k.divisors.sum id ≤ 2 * k + k / 2 + (k.divisors.card - 1 - n - 1) * (k / 3) := by
    rw [← hsumX]; omega
  omega

def isAbTau (T k : ℕ) : Bool :=
  decide (T ≤ k.divisors.card) && decide (2 * k ≤ k.divisors.sum id)

lemma not_hasSumN_of_not_abTau {n k : ℕ} (hn : 2 ≤ n)
    (h : isAbTau (n + 1) k = false) : ¬ HasSumN n k := by
  intro hs
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hk, D, hD, hc, hsum⟩
  have hτ : n + 1 ≤ k.divisors.card := by
    have hsub : D ⊆ k.properDivisors := mem_properDivisors_of_hasSumN hn hD hc hsum
    have hle := card_le_card hsub
    have := proper_card hk.ne'
    omega
  have hσ : 2 * k ≤ k.divisors.sum id := by
    have hsub : D ⊆ k.properDivisors := mem_properDivisors_of_hasSumN hn hD hc hsum
    have hps : D.sum id ≤ k.properDivisors.sum id :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    have := proper_sum hk.ne'
    omega
  unfold isAbTau at h
  simp only [Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not] at h
  rcases h with h | h <;> omega

lemma mem_filter_isAbTau {T M k : ℕ} (hk : k < M) (hd : isAbTau T k = true) :
    k ∈ (List.range M).filter (isAbTau T) := by
  simp [List.mem_filter, List.mem_range, hk, hd]

lemma not_hasSumN_of_checked_ab {n M : ℕ} (hn : 2 ≤ n)
    (hlist : ∀ k, k ∈ (List.range M).filter (isAbTau (n + 1)) → ¬ HasSumN n k) :
    ∀ k : Fin M, ¬ HasSumN n k := by
  intro k hs
  have hab : isAbTau (n + 1) k.val = true := by
    by_contra hf
    exact not_hasSumN_of_not_abTau hn (Bool.eq_false_iff.mpr hf) hs
  exact hlist k.val (mem_filter_isAbTau k.isLt hab) hs

lemma not_hasSumN_r2 {n k E : ℕ}
    (hn : 2 ≤ n)
    (hτ : k.divisors.card = n + 3)
    (hE : k.divisors.sum id = 2 * k + E)
    (hno : ∀ x ∈ k.properDivisors, ∀ y ∈ k.properDivisors, x < y → x + y ≠ E) :
    ¬ HasSumN n k := by
  intro hs
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hk, D, hD, hc, hsum⟩
  have hsub : D ⊆ k.properDivisors := mem_properDivisors_of_hasSumN hn hD hc hsum
  have hne : k ≠ 0 := hk.ne'
  have hXcard : (k.properDivisors \ D).card = 2 := by
    have := card_sdiff_of_subset hsub
    have := proper_card hne
    omega
  obtain ⟨x, y, hxy, hXeq⟩ := card_eq_two.mp hXcard
  have hxP : x ∈ k.properDivisors :=
    mem_sdiff_left (by rw [hXeq]; exact mem_insert_self _ _)
  have hyP : y ∈ k.properDivisors :=
    mem_sdiff_left (by rw [hXeq]; simp)
  have hsumX : x + y = E := by
    have hsp := sum_sdiff_proper hne hsub hsum
    have : (k.properDivisors \ D).sum id = x + y := by
      rw [hXeq, sum_pair hxy]; simp [id]
    omega
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact hno x hxP y hyP hlt hsumX
  · exact hxy heq
  · exact hno y hyP x hxP hgt (by omega)

lemma not_hasSumN_r3 {n k E : ℕ}
    (hn : 2 ≤ n)
    (hτ : k.divisors.card = n + 4)
    (hE : k.divisors.sum id = 2 * k + E)
    (hno : ∀ x ∈ k.properDivisors, ∀ y ∈ k.properDivisors, ∀ z ∈ k.properDivisors,
      x < y → y < z → x + y + z ≠ E) :
    ¬ HasSumN n k := by
  intro hs
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hk, D, hD, hc, hsum⟩
  have hsub : D ⊆ k.properDivisors := mem_properDivisors_of_hasSumN hn hD hc hsum
  have hne : k ≠ 0 := hk.ne'
  have hXcard : (k.properDivisors \ D).card = 3 := by
    have := card_sdiff_of_subset hsub
    have := proper_card hne
    omega
  obtain ⟨x, y, z, hxy, hxz, hyz, hXeq⟩ := card_eq_three.mp hXcard
  have memP : ∀ w, w ∈ ({x, y, z} : Finset ℕ) → w ∈ k.properDivisors := by
    intro w hw
    exact mem_sdiff_left (by rw [hXeq]; exact hw)
  have hxP := memP x (by simp)
  have hyP := memP y (by simp)
  have hzP := memP z (by simp)
  have hsumX : x + y + z = E := by
    have hsp := sum_sdiff_proper hne hsub hsum
    have : (k.properDivisors \ D).sum id = x + y + z := by
      rw [hXeq]
      simp [sum_insert, hxy, hxz, hyz, id]
      ac_rfl
    omega
  -- order the three
  have hord : ∃ a b c, a < b ∧ b < c ∧ a + b + c = E ∧
      a ∈ k.properDivisors ∧ b ∈ k.properDivisors ∧ c ∈ k.properDivisors := by
    rcases lt_trichotomy x y with xy | xy | xy <;>
      rcases lt_trichotomy y z with yz | yz | yz <;>
      rcases lt_trichotomy x z with xz | xz | xz
    all_goals
      first
      | exact ⟨x, y, z, by omega, by omega, hsumX, hxP, hyP, hzP⟩
      | exact ⟨x, z, y, by omega, by omega, by omega, hxP, hzP, hyP⟩
      | exact ⟨y, x, z, by omega, by omega, by omega, hyP, hxP, hzP⟩
      | exact ⟨y, z, x, by omega, by omega, by omega, hyP, hzP, hxP⟩
      | exact ⟨z, x, y, by omega, by omega, by omega, hzP, hxP, hyP⟩
      | exact ⟨z, y, x, by omega, by omega, by omega, hzP, hyP, hxP⟩
  rcases hord with ⟨a, b, c, hab, hbc, hsE, ha, hb, hc'⟩
  exact hno a ha b hb c hc' hab hbc hsE

/- Reciprocal-set / gcd lemmas for the 2δ bound -/

lemma factorization_lcm_finset (D : Finset ℕ) (h0 : ∀ d ∈ D, d ≠ 0) (p : ℕ) :
    (D.lcm id).factorization p = D.sup (fun d => d.factorization p) := by
  classical
  induction D using Finset.induction with
  | empty =>
      simp [Finset.lcm_empty, Nat.factorization_one]
  | insert a s ha ih =>
      have ha0 : a ≠ 0 := h0 a (mem_insert_self _ _)
      have hs0 : ∀ d ∈ s, d ≠ 0 := fun d hd => h0 d (mem_insert_of_mem hd)
      specialize ih hs0
      rw [lcm_insert, sup_insert]
      have hL : GCDMonoid.lcm (id a) (s.lcm id) = Nat.lcm a (s.lcm id) := rfl
      rw [hL]
      by_cases hse : s.Nonempty
      · have hl0 : s.lcm id ≠ 0 := by
          rw [lcm_ne_zero_iff]
          exact hs0
        rw [factorization_lcm ha0 hl0]
        simp [Finsupp.sup_apply, ih]
      · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hse
        subst hsempty
        simp [lcm_empty, ha0]

lemma lcm_ne_zero_of_ne_zero {D : Finset ℕ} (h0 : ∀ d ∈ D, d ≠ 0) :
    D.lcm id ≠ 0 := by
  rw [lcm_ne_zero_iff]
  exact h0

lemma ne_zero_of_dvd_pos {m d : ℕ} (hm : 0 < m) (hd : d ∣ m) : d ≠ 0 := by
  rintro rfl
  exact hm.ne' (eq_zero_of_zero_dvd hd)

lemma lcm_eq_of_gcd_recip_one {m : ℕ} {D : Finset ℕ} (hm : 0 < m)
    (hD : ∀ d ∈ D, d ∣ m) (hne : D.Nonempty)
    (hg : (D.image (fun d => m / d)).gcd id = 1) :
    D.lcm id = m := by
  have h0 : ∀ d ∈ D, d ≠ 0 := fun d hd => ne_zero_of_dvd_pos hm (hD d hd)
  have hl0 : D.lcm id ≠ 0 := lcm_ne_zero_of_ne_zero h0
  refine eq_of_factorization_eq hl0 hm.ne' (fun p => ?_)
  rw [factorization_lcm_finset D h0 p]
  apply le_antisymm
  · exact Finset.sup_le fun d hd =>
      (factorization_le_iff_dvd (h0 d hd) hm.ne').mpr (hD d hd) p
  · by_cases hp : p.Prime
    · have not_all : ¬ ∀ t ∈ D.image (fun d => m / d), p ∣ t := by
        intro hall
        have : p ∣ (D.image (fun d => m / d)).gcd id := dvd_gcd hall
        rw [hg] at this
        exact hp.not_dvd_one this
      obtain ⟨t, ht, hpt⟩ : ∃ t, t ∈ D.image (fun d => m / d) ∧ ¬ p ∣ t := by
        push_neg at not_all
        exact not_all
      obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
      have hv0 : (m / d).factorization p = 0 :=
        factorization_eq_zero_of_not_dvd hpt
      have hsub : (m / d).factorization = m.factorization - d.factorization :=
        factorization_div (hD d hd)
      have hdiff : m.factorization p - d.factorization p = 0 := by
        simpa [hsub] using hv0
      have hle : d.factorization p ≤ m.factorization p :=
        (factorization_le_iff_dvd (h0 d hd) hm.ne').mpr (hD d hd) p
      have heq : d.factorization p = m.factorization p := by omega
      have : d.factorization p ≤ D.sup (fun x => x.factorization p) :=
        le_sup (f := fun x : ℕ => x.factorization p) hd
      omega
    · simp [factorization_eq_zero_of_not_prime, hp]

lemma tau_of_recip {m : ℕ} {D : Finset ℕ} (hm : 0 < m)
    (hD : ∀ d ∈ D, d ∣ m) :
    (D.image (fun d => m / d)).card = D.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  have ha0 : 0 < a := Nat.pos_of_ne_zero (ne_zero_of_dvd_pos hm (hD a ha))
  have hb0 : 0 < b := Nat.pos_of_ne_zero (ne_zero_of_dvd_pos hm (hD b hb))
  have haeq : m / (m / a) = a := by
    have hmul : a * (m / a) = m := Nat.mul_div_cancel' (hD a ha)
    have hq : 0 < m / a := Nat.div_pos (Nat.le_of_dvd hm (hD a ha)) ha0
    exact (Nat.eq_div_of_mul_eq_left hq.ne' hmul).symm
  have hbeq : m / (m / b) = b := by
    have hmul : b * (m / b) = m := Nat.mul_div_cancel' (hD b hb)
    have hq : 0 < m / b := Nat.div_pos (Nat.le_of_dvd hm (hD b hb)) hb0
    exact (Nat.eq_div_of_mul_eq_left hq.ne' hmul).symm
  have hab : m / a = m / b := heq
  rw [← haeq, ← hbeq, hab]

lemma image_div_g_card {g : ℕ} {T : Finset ℕ} (hg : 0 < g)
    (hT : ∀ t ∈ T, g ∣ t) :
    (T.image (fun t => t / g)).card = T.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  have haeq : a = (a / g) * g := (Nat.div_mul_cancel (hT a ha)).symm
  have hbeq : b = (b / g) * g := (Nat.div_mul_cancel (hT b hb)).symm
  have hab : a / g = b / g := heq
  rw [haeq, hbeq, hab]

lemma div_dvd_div_of {m g t : ℕ} (hgpos : 0 < g) (hgt : g ∣ t) (htm : t ∣ m) :
    t / g ∣ m / g := by
  obtain ⟨k, hk⟩ := htm
  obtain ⟨l, hl⟩ := hgt
  have : m / g = (t / g) * k := by
    rw [hk, hl, mul_assoc, Nat.mul_div_cancel_left _ hgpos,
      Nat.mul_div_cancel_left _ hgpos]
  exact ⟨k, this⟩

lemma image_div_g_dvd {m g : ℕ} {T : Finset ℕ} (hgpos : 0 < g)
    (hT : ∀ t ∈ T, t ∣ m) (hgT : ∀ t ∈ T, g ∣ t) :
    ∀ u ∈ T.image (fun t => t / g), u ∣ m / g := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
  exact div_dvd_div_of hgpos (hgT t ht) (hT t ht)

lemma gcd_dvd_each {T : Finset ℕ} {t : ℕ} (ht : t ∈ T) :
    T.gcd id ∣ t :=
  gcd_dvd ht

lemma gcd_pos_of_nonempty {T : Finset ℕ} (hne : T.Nonempty)
    (hpos : ∀ t ∈ T, 0 < t) : 0 < T.gcd id := by
  obtain ⟨t, ht⟩ := hne
  exact Nat.pos_of_dvd_of_pos (gcd_dvd ht) (hpos t ht)

lemma hasSumN_sInf {n : ℕ} (hpos : 0 < a081512 n) : HasSumN n (a081512 n) := by
  rw [a081512_eq] at hpos ⊢
  have hne : ({m | HasSumN n m} : Set ℕ).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have : sInf (∅ : Set ℕ) = 0 := Nat.sInf_empty
    simp [hempty] at hpos
  exact Nat.sInf_mem hne

lemma two_mul_div_le_of_two_le {m g : ℕ} (hg : 2 ≤ g) (hd : g ∣ m) :
    2 * (m / g) ≤ m := by
  have hgpos : 0 < g := by omega
  have h1 : m / g ≤ m / 2 := Nat.div_le_div_left hg (by decide : 0 < 2)
  have h2 : 2 * (m / g) ≤ 2 * (m / 2) := Nat.mul_le_mul_left 2 h1
  have h3 : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
  omega

lemma hasSumN_bad_ge {n m B : ℕ} (hn : 1 ≤ n)
    (hs : HasSumN n m) (hnolcm : ¬ HasSumNLcm n m)
    (hτ : ∀ k < B, k.divisors.card < n) :
    2 * B ≤ m := by
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hm, D, hD, hc, hsum⟩
  have hne : D.Nonempty := card_pos.mp (by omega)
  have hDvd : ∀ d ∈ D, d ∣ m := fun d hd => dvd_of_mem_divisors (hD hd)
  have hlcm_ne : D.lcm id ≠ m := by
    intro hl
    exact hnolcm ⟨hm, D, mem_powerset.mpr hD, hc, hsum, hl⟩
  have hg_ne : (D.image (fun d => m / d)).gcd id ≠ 1 := by
    intro hg
    exact hlcm_ne (lcm_eq_of_gcd_recip_one hm hDvd hne hg)
  set T := D.image (fun d => m / d) with hTdef
  set g := T.gcd id with hgdef
  have hTne : T.Nonempty := hne.image _
  have hTpos : ∀ t ∈ T, 0 < t := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
    have hd0 : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_pos hm (hDvd d hd))
    exact Nat.div_pos (Nat.le_of_dvd hm (hDvd d hd)) hd0
  have hgpos : 0 < g := gcd_pos_of_nonempty hTne hTpos
  have hg2 : 2 ≤ g := by
    have : g ≠ 1 := by simpa [T, g] using hg_ne
    omega
  have hgT : ∀ t ∈ T, g ∣ t := fun t ht => gcd_dvd_each ht
  have hg_dvd_m : g ∣ m := by
    obtain ⟨t, ht⟩ := hTne
    have htD : t ∣ m := by
      obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
      exact div_dvd_of_dvd (hDvd d hd)
    exact (hgT t ht).trans htD
  have hUcard : (T.image (fun t => t / g)).card = D.card := by
    rw [image_div_g_card hgpos hgT, tau_of_recip hm hDvd]
  have hTdiv : ∀ t ∈ T, t ∣ m := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
    exact div_dvd_of_dvd (hDvd d hd)
  have hUdvd : ∀ u ∈ T.image (fun t => t / g), u ∣ m / g :=
    image_div_g_dvd hgpos hTdiv hgT
  have hmg_pos : 0 < m / g := Nat.div_pos (Nat.le_of_dvd hm hg_dvd_m) hgpos
  have hτmg : n ≤ (m / g).divisors.card := by
    have hsub : T.image (fun t => t / g) ⊆ (m / g).divisors := by
      intro u hu
      exact mem_divisors.2 ⟨hUdvd u hu, hmg_pos.ne'⟩
    have := card_le_card hsub
    omega
  have hmg_ge : B ≤ m / g := by
    by_contra hlt
    have : (m / g).divisors.card < n := hτ (m / g) (lt_of_not_ge hlt)
    omega
  have : 2 * (m / g) ≤ m := two_mul_div_le_of_two_le hg2 hg_dvd_m
  omega

lemma a081512_pos_of_has {n m : ℕ} (h : HasSumN n m) : 0 < a081512 n := by
  have hne : ({k | HasSumN n k} : Set ℕ).Nonempty := ⟨m, h⟩
  have hmem : HasSumN n (a081512 n) := by
    rw [a081512_eq]
    exact Nat.sInf_mem hne
  exact ((HasSumN_iff n (a081512 n)).1 hmem).1

lemma not_gt_of_witness_tau {n U B : ℕ} (hU : HasSumNLcm n U)
    (h2 : U ≤ 2 * B) (hτ : ∀ k < B, k.divisors.card < n)
    (hn : 1 ≤ n) : ¬ a n > a081512 n := by
  intro hgt
  have hsU : HasSumN n U := hasSumN_of_hasSumNLcm hU
  have haU : a n ≤ U := a_le_of_has hU
  have h081 : a081512 n ≤ U := a081512_le_of_has hsU
  have hpos : 0 < a081512 n := a081512_pos_of_has hsU
  have hs : HasSumN n (a081512 n) := hasSumN_sInf hpos
  have hnolcm : ¬ HasSumNLcm n (a081512 n) := by
    intro h
    have : a n ≤ a081512 n := a_le_of_has h
    omega
  have hge : 2 * B ≤ a081512 n := hasSumN_bad_ge hn hs hnolcm hτ
  omega


/- n = 8 -/

lemma hasSumNLcm_8_60 : HasSumNLcm 8 60 :=
  hasSumNLcm_of_dvd 8 60 {1,2,3,4,5,10,15,20}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_8 : (List.range 60).filter (isAbTau 9) = [36, 48] := by decide

lemma not_has_8_36 : ¬ HasSumN 8 36 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_8_48 : ¬ HasSumN 8 48 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma min_8 : ∀ k : Fin 60, ¬ HasSumN 8 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_8] at hk
  simp at hk
  rcases hk with rfl | rfl
  · exact not_has_8_36
  · exact not_has_8_48

lemma a081512_8_eq : a081512 8 = 60 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_8_60) min_8

lemma a_le_8 : a 8 ≤ a081512 8 := by
  have h1 := a_le_of_has hasSumNLcm_8_60
  have h2 := a081512_8_eq
  omega

lemma a_eq_a081512_8 : ¬ a 8 > a081512 8 :=
  not_lt_of_le_seq a_le_8

/- n = 9 -/

lemma hasSumNLcm_9_84 : HasSumNLcm 9 84 :=
  hasSumNLcm_of_dvd 9 84 {1,2,3,4,6,7,12,21,28}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_9 : (List.range 84).filter (isAbTau 10) = [48, 60, 72, 80] := by decide

lemma not_has_9_48 : ¬ HasSumN 9 48 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_9_60 : ¬ HasSumN 9 60 :=
  not_hasSumN_r2 (E := 48) (by decide) (by decide) (by decide) (by decide)

lemma not_has_9_72 : ¬ HasSumN 9 72 :=
  not_hasSumN_r2 (E := 51) (by decide) (by decide) (by decide) (by decide)

lemma not_has_9_80 : ¬ HasSumN 9 80 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma min_9 : ∀ k : Fin 84, ¬ HasSumN 9 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_9] at hk
  simp at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact not_has_9_48
  · exact not_has_9_60
  · exact not_has_9_72
  · exact not_has_9_80

lemma a081512_9_eq : a081512 9 = 84 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_9_84) min_9

lemma a_le_9 : a 9 ≤ a081512 9 := by
  have h1 := a_le_of_has hasSumNLcm_9_84
  have h2 := a081512_9_eq
  omega

lemma a_eq_a081512_9 : ¬ a 9 > a081512 9 :=
  not_lt_of_le_seq a_le_9

/- n = 10 -/

lemma hasSumNLcm_10_120 : HasSumNLcm 10 120 :=
  hasSumNLcm_of_dvd 10 120 {1,2,3,4,5,6,15,20,24,40}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_10 : (List.range 120).filter (isAbTau 11) = [60, 72, 84, 90, 96, 108] := by decide

lemma not_has_10_60 : ¬ HasSumN 10 60 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_10_72 : ¬ HasSumN 10 72 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_10_84 : ¬ HasSumN 10 84 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_10_90 : ¬ HasSumN 10 90 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_10_96 : ¬ HasSumN 10 96 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_10_108 : ¬ HasSumN 10 108 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma min_10 : ∀ k : Fin 120, ¬ HasSumN 10 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_10] at hk
  simp at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_has_10_60
  · exact not_has_10_72
  · exact not_has_10_84
  · exact not_has_10_90
  · exact not_has_10_96
  · exact not_has_10_108

lemma a081512_10_eq : a081512 10 = 120 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_10_120) min_10

lemma a_le_10 : a 10 ≤ a081512 10 := by
  have h1 := a_le_of_has hasSumNLcm_10_120
  have h2 := a081512_10_eq
  omega

lemma a_eq_a081512_10 : ¬ a 10 > a081512 10 :=
  not_lt_of_le_seq a_le_10

/- n = 11 -/

lemma hasSumNLcm_11_120 : HasSumNLcm 11 120 :=
  hasSumNLcm_of_dvd 11 120 {1,2,3,4,5,6,8,12,15,24,40}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_11 : (List.range 120).filter (isAbTau 12) = [60, 72, 84, 90, 96, 108] := by decide

lemma not_has_11_60 : ¬ HasSumN 11 60 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_11_72 : ¬ HasSumN 11 72 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_11_84 : ¬ HasSumN 11 84 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_11_90 : ¬ HasSumN 11 90 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_11_96 : ¬ HasSumN 11 96 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_11_108 : ¬ HasSumN 11 108 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma min_11 : ∀ k : Fin 120, ¬ HasSumN 11 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_11] at hk
  simp at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_has_11_60
  · exact not_has_11_72
  · exact not_has_11_84
  · exact not_has_11_90
  · exact not_has_11_96
  · exact not_has_11_108

lemma a081512_11_eq : a081512 11 = 120 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_11_120) min_11

lemma a_le_11 : a 11 ≤ a081512 11 := by
  have h1 := a_le_of_has hasSumNLcm_11_120
  have h2 := a081512_11_eq
  omega

lemma a_eq_a081512_11 : ¬ a 11 > a081512 11 :=
  not_lt_of_le_seq a_le_11

/- n = 12 -/

lemma hasSumNLcm_12_120 : HasSumNLcm 12 120 :=
  hasSumNLcm_of_dvd 12 120 {1,2,3,4,5,6,8,10,12,15,24,30}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_12 : (List.range 120).filter (isAbTau 13) = [] := by decide

lemma min_12 : ∀ k : Fin 120, ¬ HasSumN 12 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_12] at hk
  simp at hk

lemma a081512_12_eq : a081512 12 = 120 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_12_120) min_12

lemma a_le_12 : a 12 ≤ a081512 12 := by
  have h1 := a_le_of_has hasSumNLcm_12_120
  have h2 := a081512_12_eq
  omega

lemma a_eq_a081512_12 : ¬ a 12 > a081512 12 :=
  not_lt_of_le_seq a_le_12

/- n = 13 -/

lemma hasSumNLcm_13_180 : HasSumNLcm 13 180 :=
  hasSumNLcm_of_dvd 13 180 {1,2,3,4,5,9,10,12,15,18,20,36,45}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_13 : (List.range 180).filter (isAbTau 14) = [120, 144, 168] := by decide

lemma not_has_13_120 : ¬ HasSumN 13 120 :=
  not_hasSumN_of_excess_half_third (by decide) (by decide) (by decide)

lemma not_has_13_144 : ¬ HasSumN 13 144 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_13_168 : ¬ HasSumN 13 168 :=
  not_hasSumN_of_excess_half_third (by decide) (by decide) (by decide)

lemma min_13 : ∀ k : Fin 180, ¬ HasSumN 13 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_13] at hk
  simp at hk
  rcases hk with rfl | rfl | rfl
  · exact not_has_13_120
  · exact not_has_13_144
  · exact not_has_13_168

lemma a081512_13_eq : a081512 13 = 180 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_13_180) min_13

lemma a_le_13 : a 13 ≤ a081512 13 := by
  have h1 := a_le_of_has hasSumNLcm_13_180
  have h2 := a081512_13_eq
  omega

lemma a_eq_a081512_13 : ¬ a 13 > a081512 13 :=
  not_lt_of_le_seq a_le_13

/- n = 14 -/

lemma hasSumNLcm_14_180 : HasSumNLcm 14 180 :=
  hasSumNLcm_of_dvd 14 180 {1,2,3,4,5,6,9,10,12,15,18,20,30,45}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_14 : (List.range 180).filter (isAbTau 15) = [120, 144, 168] := by decide

lemma not_has_14_120 : ¬ HasSumN 14 120 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_14_144 : ¬ HasSumN 14 144 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_14_168 : ¬ HasSumN 14 168 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma min_14 : ∀ k : Fin 180, ¬ HasSumN 14 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_14] at hk
  simp at hk
  rcases hk with rfl | rfl | rfl
  · exact not_has_14_120
  · exact not_has_14_144
  · exact not_has_14_168

lemma a081512_14_eq : a081512 14 = 180 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_14_180) min_14

lemma a_le_14 : a 14 ≤ a081512 14 := by
  have h1 := a_le_of_has hasSumNLcm_14_180
  have h2 := a081512_14_eq
  omega

lemma a_eq_a081512_14 : ¬ a 14 > a081512 14 :=
  not_lt_of_le_seq a_le_14

/- n = 15 -/

lemma hasSumNLcm_15_240 : HasSumNLcm 15 240 :=
  hasSumNLcm_of_dvd 15 240 {1,2,3,5,6,8,10,12,15,16,20,24,30,40,48}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_15 : (List.range 240).filter (isAbTau 16) = [120, 168, 180, 210, 216] := by decide

lemma not_has_15_120 : ¬ HasSumN 15 120 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_15_168 : ¬ HasSumN 15 168 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_15_180 : ¬ HasSumN 15 180 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_15_210 : ¬ HasSumN 15 210 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_15_216 : ¬ HasSumN 15 216 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma min_15 : ∀ k : Fin 240, ¬ HasSumN 15 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_15] at hk
  simp at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact not_has_15_120
  · exact not_has_15_168
  · exact not_has_15_180
  · exact not_has_15_210
  · exact not_has_15_216

lemma a081512_15_eq : a081512 15 = 240 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_15_240) min_15

lemma a_le_15 : a 15 ≤ a081512 15 := by
  have h1 := a_le_of_has hasSumNLcm_15_240
  have h2 := a081512_15_eq
  omega

lemma a_eq_a081512_15 : ¬ a 15 > a081512 15 :=
  not_lt_of_le_seq a_le_15

/- n = 16 -/

lemma hasSumNLcm_16_360 : HasSumNLcm 16 360 :=
  hasSumNLcm_of_dvd 16 360 {3,4,5,6,8,9,10,15,18,20,24,30,36,40,60,72}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_16 : (List.range 360).filter (isAbTau 17) = [180, 240, 252, 288, 300, 336] := by decide

lemma not_has_16_180 : ¬ HasSumN 16 180 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_16_240 : ¬ HasSumN 16 240 :=
  not_hasSumN_r3 (E := 264) (by decide) (by decide) (by decide) (by decide)

lemma not_has_16_252 : ¬ HasSumN 16 252 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_16_288 : ¬ HasSumN 16 288 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_16_300 : ¬ HasSumN 16 300 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_16_336 : ¬ HasSumN 16 336 :=
  not_hasSumN_r3 (E := 320) (by decide) (by decide) (by decide) (by decide)

lemma min_16 : ∀ k : Fin 360, ¬ HasSumN 16 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_16] at hk
  simp at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_has_16_180
  · exact not_has_16_240
  · exact not_has_16_252
  · exact not_has_16_288
  · exact not_has_16_300
  · exact not_has_16_336

lemma a081512_16_eq : a081512 16 = 360 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_16_360) min_16

lemma a_le_16 : a 16 ≤ a081512 16 := by
  have h1 := a_le_of_has hasSumNLcm_16_360
  have h2 := a081512_16_eq
  omega

lemma a_eq_a081512_16 : ¬ a 16 > a081512 16 :=
  not_lt_of_le_seq a_le_16

/- n = 17 -/

lemma hasSumNLcm_17_360 : HasSumNLcm 17 360 :=
  hasSumNLcm_of_dvd 17 360 {1,3,4,5,6,8,9,10,12,15,20,24,30,36,45,60,72}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_17 : (List.range 360).filter (isAbTau 18) = [180, 240, 252, 288, 300, 336] := by decide

lemma not_has_17_180 : ¬ HasSumN 17 180 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_17_240 : ¬ HasSumN 17 240 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_17_252 : ¬ HasSumN 17 252 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_17_288 : ¬ HasSumN 17 288 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_17_300 : ¬ HasSumN 17 300 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_17_336 : ¬ HasSumN 17 336 :=
  not_hasSumN_of_excess_half_third (by decide) (by decide) (by decide)

lemma min_17 : ∀ k : Fin 360, ¬ HasSumN 17 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_17] at hk
  simp at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_has_17_180
  · exact not_has_17_240
  · exact not_has_17_252
  · exact not_has_17_288
  · exact not_has_17_300
  · exact not_has_17_336

lemma a081512_17_eq : a081512 17 = 360 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_17_360) min_17

lemma a_le_17 : a 17 ≤ a081512 17 := by
  have h1 := a_le_of_has hasSumNLcm_17_360
  have h2 := a081512_17_eq
  omega

lemma a_eq_a081512_17 : ¬ a 17 > a081512 17 :=
  not_lt_of_le_seq a_le_17

/- n = 18 -/

lemma hasSumNLcm_18_360 : HasSumNLcm 18 360 :=
  hasSumNLcm_of_dvd 18 360 {1,2,3,4,5,6,8,9,10,12,18,20,24,30,36,40,60,72}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_18 : (List.range 360).filter (isAbTau 19) = [240, 336] := by decide

lemma not_has_18_240 : ¬ HasSumN 18 240 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma not_has_18_336 : ¬ HasSumN 18 336 :=
  not_hasSumN_of_excess_half (by decide) (by decide) (by decide)

lemma min_18 : ∀ k : Fin 360, ¬ HasSumN 18 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_18] at hk
  simp at hk
  rcases hk with rfl | rfl
  · exact not_has_18_240
  · exact not_has_18_336

lemma a081512_18_eq : a081512 18 = 360 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_18_360) min_18

lemma a_le_18 : a 18 ≤ a081512 18 := by
  have h1 := a_le_of_has hasSumNLcm_18_360
  have h2 := a081512_18_eq
  omega

lemma a_eq_a081512_18 : ¬ a 18 > a081512 18 :=
  not_lt_of_le_seq a_le_18

/- n = 19 -/

lemma hasSumNLcm_19_360 : HasSumNLcm 19 360 :=
  hasSumNLcm_of_dvd 19 360 {1,2,3,4,5,6,8,9,10,12,15,18,20,24,30,36,40,45,72}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma abTau_19 : (List.range 360).filter (isAbTau 20) = [240, 336] := by decide

lemma not_has_19_240 : ¬ HasSumN 19 240 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma not_has_19_336 : ¬ HasSumN 19 336 :=
  not_hasSumN_all_proper (by decide) (by decide) (by decide)

lemma min_19 : ∀ k : Fin 360, ¬ HasSumN 19 k.val := by
  apply not_hasSumN_of_checked_ab (by decide)
  intro k hk
  rw [abTau_19] at hk
  simp at hk
  rcases hk with rfl | rfl
  · exact not_has_19_240
  · exact not_has_19_336

lemma a081512_19_eq : a081512 19 = 360 :=
  a081512_eq_of (hasSumN_of_hasSumNLcm hasSumNLcm_19_360) min_19

lemma a_le_19 : a 19 ≤ a081512 19 := by
  have h1 := a_le_of_has hasSumNLcm_19_360
  have h2 := a081512_19_eq
  omega

lemma a_eq_a081512_19 : ¬ a 19 > a081512 19 :=
  not_lt_of_le_seq a_le_19



/- n = 21, 22, 23 via 2δ bound -/

lemma tau_lt_360 : ∀ k : Fin 360, k.val.divisors.card ≤ 20 := by decide

lemma tau_lt_360' : ∀ k < 360, k.divisors.card < 21 := by
  intro k hk
  have h : k.divisors.card ≤ 20 := by simpa using tau_lt_360 ⟨k, hk⟩
  omega

lemma tau_lt_360_of {n : ℕ} (hn : 21 ≤ n) : ∀ k < 360, k.divisors.card < n := by
  intro k hk
  have := tau_lt_360' k hk
  omega

lemma hasSumNLcm_21_720 : HasSumNLcm 21 720 :=
  hasSumNLcm_of_dvd 21 720
    {1,2,3,4,5,6,8,9,10,12,15,16,18,20,24,36,45,72,90,144,180}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_22_720 : HasSumNLcm 22 720 :=
  hasSumNLcm_of_dvd 22 720
    {1,2,3,4,5,8,9,10,15,16,18,20,24,30,36,40,45,48,72,80,90,144}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_23_720 : HasSumNLcm 23 720 :=
  hasSumNLcm_of_dvd 23 720
    {1,2,3,4,5,8,9,10,12,15,16,18,20,24,30,36,40,45,48,60,80,90,144}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma a_eq_a081512_21 : ¬ a 21 > a081512 21 :=
  not_gt_of_witness_tau hasSumNLcm_21_720 (by decide) (tau_lt_360_of (by decide)) (by decide)

lemma a_eq_a081512_22 : ¬ a 22 > a081512 22 :=
  not_gt_of_witness_tau hasSumNLcm_22_720 (by decide) (tau_lt_360_of (by decide)) (by decide)

lemma a_eq_a081512_23 : ¬ a 23 > a081512 23 :=
  not_gt_of_witness_tau hasSumNLcm_23_720 (by decide) (tau_lt_360_of (by decide)) (by decide)

/- n = 25 .. 29 : B = 720, τ ≤ 24 -/

lemma tau_le_24_off360 : ∀ k : Fin 120, (k.val + 360).divisors.card ≤ 24 := by decide
lemma tau_le_24_off480 : ∀ k : Fin 120, (k.val + 480).divisors.card ≤ 24 := by decide
lemma tau_le_24_off600 : ∀ k : Fin 120, (k.val + 600).divisors.card ≤ 24 := by decide

lemma tau_le_24_720 : ∀ k < 720, k.divisors.card ≤ 24 := by
  intro k hk
  if h : k < 360 then
    have : k.divisors.card ≤ 20 := by simpa using tau_lt_360 ⟨k, h⟩
    omega
  else if h : k < 480 then
    have : k - 360 < 120 := by omega
    have h2 := tau_le_24_off360 ⟨k - 360, this⟩
    have hk' : k - 360 + 360 = k := by omega
    simpa [hk'] using h2
  else if h : k < 600 then
    have : k - 480 < 120 := by omega
    have h2 := tau_le_24_off480 ⟨k - 480, this⟩
    have hk' : k - 480 + 480 = k := by omega
    simpa [hk'] using h2
  else
    have : k - 600 < 120 := by omega
    have h2 := tau_le_24_off600 ⟨k - 600, this⟩
    have hk' : k - 600 + 600 = k := by omega
    simpa [hk'] using h2

lemma tau_le_720_lt {n : ℕ} (hn : 25 ≤ n) : ∀ k < 720, k.divisors.card < n := by
  intro k hk
  have := tau_le_24_720 k hk
  omega

lemma hasSumNLcm_25_840 : HasSumNLcm 25 840 :=
  hasSumNLcm_of_dvd 25 840
    {1,3,4,5,6,7,8,10,12,14,15,20,21,24,28,30,35,40,42,56,60,70,84,105,140}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_26_1080 : HasSumNLcm 26 1080 :=
  hasSumNLcm_of_dvd 26 1080
    {1,2,3,4,5,6,8,9,10,12,15,18,20,24,27,30,36,40,45,54,60,72,108,120,135,216}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_27_1260 : HasSumNLcm 27 1260 :=
  hasSumNLcm_of_dvd 27 1260
    {1,2,3,4,5,6,9,10,12,14,15,18,20,21,28,30,36,42,45,60,63,70,84,90,140,180,252}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_28_1260 : HasSumNLcm 28 1260 :=
  hasSumNLcm_of_dvd 28 1260
    {1,2,3,4,5,6,7,9,10,12,14,15,18,20,21,28,30,35,36,45,60,63,70,84,90,140,180,252}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_29_1260 : HasSumNLcm 29 1260 :=
  hasSumNLcm_of_dvd 29 1260
    {1,2,3,4,5,6,7,9,10,12,14,15,18,20,28,30,35,36,42,45,60,63,70,84,90,105,126,140,180}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma a_eq_a081512_25 : ¬ a 25 > a081512 25 :=
  not_gt_of_witness_tau hasSumNLcm_25_840 (by decide) (tau_le_720_lt (by decide)) (by decide)

lemma a_eq_a081512_26 : ¬ a 26 > a081512 26 :=
  not_gt_of_witness_tau hasSumNLcm_26_1080 (by decide) (tau_le_720_lt (by decide)) (by decide)

lemma a_eq_a081512_27 : ¬ a 27 > a081512 27 :=
  not_gt_of_witness_tau hasSumNLcm_27_1260 (by decide) (tau_le_720_lt (by decide)) (by decide)

lemma a_eq_a081512_28 : ¬ a 28 > a081512 28 :=
  not_gt_of_witness_tau hasSumNLcm_28_1260 (by decide) (tau_le_720_lt (by decide)) (by decide)

lemma a_eq_a081512_29 : ¬ a 29 > a081512 29 :=
  not_gt_of_witness_tau hasSumNLcm_29_1260 (by decide) (tau_le_720_lt (by decide)) (by decide)



/- Refined structure of a "bad" HasSumN (no lcm). -/

lemma mul_div_le_of_le_dvd {m g c : ℕ} (hc : c ≤ g) (hg : 0 < g) (hd : g ∣ m) :
    c * (m / g) ≤ m := by
  cases c with
  | zero => simp
  | succ c =>
      have h1 : m / g ≤ m / c.succ := Nat.div_le_div_left hc (Nat.succ_pos _)
      have h2 : c.succ * (m / g) ≤ c.succ * (m / c.succ) := Nat.mul_le_mul_left _ h1
      have h3 : c.succ * (m / c.succ) ≤ m := Nat.mul_div_le m c.succ
      exact h2.trans h3

lemma dvd_div_of_dvd_quot {m g d : ℕ} (hm : 0 < m) (hg : 0 < g)
    (hd : d ∣ m) (hgt : g ∣ m / d) : d ∣ m / g := by
  have hdm : d * (m / d) = m := Nat.mul_div_cancel' hd
  obtain ⟨k, hk⟩ := hgt
  have : d * k = m / g := by
    have hmul : (d * k) * g = m := by
      calc
        (d * k) * g = d * (k * g) := by ring
        _ = d * (g * k) := by rw [mul_comm k]
        _ = d * (m / d) := by rw [← hk]
        _ = m := hdm
    exact Nat.eq_div_of_mul_eq_left hg.ne' hmul
  exact ⟨k, this.symm⟩

lemma exists_bad_gcd {n m : ℕ} (hn : 1 ≤ n)
    (hs : HasSumN n m) (hnolcm : ¬ HasSumNLcm n m) :
    ∃ (D : Finset ℕ) (g : ℕ),
      D ⊆ m.divisors ∧ D.card = n ∧ D.sum id = m ∧
      2 ≤ g ∧ g ∣ m ∧
      (∀ d ∈ D, g ∣ m / d) ∧
      (∀ d ∈ D, d ∣ m / g) := by
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hm, D, hD, hc, hsum⟩
  have hne : D.Nonempty := card_pos.mp (by omega)
  have hDvd : ∀ d ∈ D, d ∣ m := fun d hd => dvd_of_mem_divisors (hD hd)
  have hlcm_ne : D.lcm id ≠ m := by
    intro hl
    exact hnolcm ⟨hm, D, mem_powerset.mpr hD, hc, hsum, hl⟩
  have hg_ne : (D.image (fun d => m / d)).gcd id ≠ 1 := by
    intro hg
    exact hlcm_ne (lcm_eq_of_gcd_recip_one hm hDvd hne hg)
  set T := D.image (fun d => m / d) with hTdef
  set g := T.gcd id with hgdef
  have hTne : T.Nonempty := hne.image _
  have hTpos : ∀ t ∈ T, 0 < t := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
    have hd0 : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_pos hm (hDvd d hd))
    exact Nat.div_pos (Nat.le_of_dvd hm (hDvd d hd)) hd0
  have hgpos : 0 < g := gcd_pos_of_nonempty hTne hTpos
  have hg2 : 2 ≤ g := by
    have : g ≠ 1 := by simpa [T, g] using hg_ne
    omega
  have hgT : ∀ t ∈ T, g ∣ t := fun t ht => gcd_dvd_each ht
  have hg_dvd_m : g ∣ m := by
    obtain ⟨t, ht⟩ := hTne
    have htD : t ∣ m := by
      obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
      exact div_dvd_of_dvd (hDvd d hd)
    exact (hgT t ht).trans htD
  have hall_g : ∀ d ∈ D, g ∣ m / d := by
    intro d hd
    have : m / d ∈ T := mem_image.mpr ⟨d, hd, rfl⟩
    exact hgT _ this
  have hall_d : ∀ d ∈ D, d ∣ m / g :=
    fun d hd => dvd_div_of_dvd_quot hm hgpos (hDvd d hd) (hall_g d hd)
  exact ⟨D, g, hD, hc, hsum, hg2, hg_dvd_m, hall_g, hall_d⟩

lemma hasSumN_of_half {n m : ℕ} {D : Finset ℕ}
    (hm : 2 ≤ m) (h2 : 2 ∣ m)
    (hD : D ⊆ m.divisors) (hc : D.card = n) (hs : D.sum id = m)
    (hhalf : m / 2 ∈ D)
    (hevenT : ∀ d ∈ D, 2 ∣ m / d)
    (hn : 1 ≤ n) :
    HasSumN (n - 1) (m / 2) := by
  rw [HasSumN_iff]
  have hm2 : 0 < m / 2 := Nat.div_pos (Nat.le_of_dvd (by omega) h2) (by decide)
  refine ⟨hm2, D.erase (m / 2), ?_, ?_, ?_⟩
  · intro d hd
    have hdD : d ∈ D := mem_of_mem_erase hd
    have hdiv : d ∣ m / 2 :=
      dvd_div_of_dvd_quot (by omega) (by decide)
        (dvd_of_mem_divisors (hD hdD)) (hevenT d hdD)
    exact mem_divisors.2 ⟨hdiv, hm2.ne'⟩
  · rw [card_erase_of_mem hhalf, hc]
  · have hse := sum_erase_add (s := D) (f := id) hhalf
    rw [hs] at hse
    change (D.erase (m / 2)).sum id + m / 2 = m at hse
    have heq : 2 * (m / 2) = m := Nat.mul_div_cancel' h2
    have : (D.erase (m / 2)).sum id = m / 2 := by omega
    exact this

lemma not_gt_of_special {n U B3 B2 A : ℕ} (hU : HasSumNLcm n U)
    (hn : 2 ≤ n)
    (hU3 : U ≤ 3 * B3) (hτ3 : ∀ k < B3, k.divisors.card < n)
    (hU2 : U ≤ 2 * B2) (hτ2 : ∀ k < B2, k.divisors.card < n + 1)
    (hUA : U ≤ 2 * A) (hA : A ≤ a081512 (n - 1)) :
    ¬ a n > a081512 n := by
  intro hgt
  have hsU : HasSumN n U := hasSumN_of_hasSumNLcm hU
  have haU : a n ≤ U := a_le_of_has hU
  have hpos : 0 < a081512 n := a081512_pos_of_has hsU
  have hs : HasSumN n (a081512 n) := hasSumN_sInf hpos
  have hnolcm : ¬ HasSumNLcm n (a081512 n) := by
    intro h
    have : a n ≤ a081512 n := a_le_of_has h
    omega
  obtain ⟨D, g, hD, hc, hsum, hg2, hg_dvd, hall_g, hall_d⟩ :=
    exists_bad_gcd (by omega) hs hnolcm
  have hm : 0 < a081512 n := hpos
  by_cases hg3 : 3 ≤ g
  · have hmg_ge : B3 ≤ a081512 n / g := by
      have hmg_pos : 0 < a081512 n / g :=
        Nat.div_pos (Nat.le_of_dvd hm hg_dvd) (by omega)
      have hsub : D ⊆ (a081512 n / g).divisors := by
        intro d hd
        exact mem_divisors.2 ⟨hall_d d hd, hmg_pos.ne'⟩
      have hτmg : n ≤ (a081512 n / g).divisors.card := by
        have := card_le_card hsub
        omega
      by_contra hlt
      have : (a081512 n / g).divisors.card < n := hτ3 _ (lt_of_not_ge hlt)
      omega
    have : 3 * (a081512 n / g) ≤ a081512 n :=
      mul_div_le_of_le_dvd hg3 (by omega) hg_dvd
    omega
  · have hg_eq : g = 2 := by omega
    subst hg_eq
    by_cases hhalf : a081512 n / 2 ∈ D
    · have hhalfN : HasSumN (n - 1) (a081512 n / 2) :=
        hasSumN_of_half (by omega) hg_dvd hD hc hsum hhalf hall_g (by omega)
      have hle : a081512 (n - 1) ≤ a081512 n / 2 := a081512_le_of_has hhalfN
      have : 2 * (a081512 n / 2) = a081512 n := Nat.mul_div_cancel' hg_dvd
      omega
    · have hmg_pos : 0 < a081512 n / 2 :=
        Nat.div_pos (Nat.le_of_dvd hm hg_dvd) (by decide)
      have hsub : D ⊆ (a081512 n / 2).divisors := by
        intro d hd
        exact mem_divisors.2 ⟨hall_d d hd, hmg_pos.ne'⟩
      have hproper : D ⊆ (a081512 n / 2).properDivisors := by
        intro d hd
        have hd' := hsub hd
        rw [mem_properDivisors]
        refine ⟨dvd_of_mem_divisors hd', ?_⟩
        have hdvd := dvd_of_mem_divisors hd'
        have hne : d ≠ a081512 n / 2 := by
          intro hdeq
          apply hhalf
          simpa [hdeq] using hd
        exact lt_of_le_of_ne (Nat.le_of_dvd hmg_pos hdvd) hne
      have hτmg : n < (a081512 n / 2).divisors.card := by
        have hpc : (a081512 n / 2).properDivisors.card =
            (a081512 n / 2).divisors.card - 1 := proper_card hmg_pos.ne'
        have := card_le_card hproper
        have hneD : D.Nonempty := card_pos.mp (by omega)
        have : 0 < (a081512 n / 2).properDivisors.card :=
          card_pos.mpr ⟨_, hproper hneD.choose_spec⟩
        omega
      have hmg_ge : B2 ≤ a081512 n / 2 := by
        by_contra hlt
        have : (a081512 n / 2).divisors.card < n + 1 := hτ2 _ (lt_of_not_ge hlt)
        omega
      have : 2 * (a081512 n / 2) ≤ a081512 n :=
        mul_div_le_of_le_dvd (by decide) (by decide) hg_dvd
      omega

/- n = 20 -/

lemma hasSumNLcm_20_672 : HasSumNLcm 20 672 :=
  hasSumNLcm_of_dvd 20 672
    {1,2,3,4,6,7,8,12,14,16,21,24,28,32,42,48,56,84,96,168}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma tau_le_19_off0 : ∀ k : Fin 120, k.val.divisors.card ≤ 19 := by decide
lemma tau_le_19_off120 : ∀ k : Fin 120, (k.val + 120).divisors.card ≤ 19 := by decide

lemma tau_lt_20_240' : ∀ k < 240, k.divisors.card < 20 := by
  intro k hk
  if h : k < 120 then
    have : k.divisors.card ≤ 19 := by simpa using tau_le_19_off0 ⟨k, h⟩
    omega
  else
    have : k - 120 < 120 := by omega
    have h2 := tau_le_19_off120 ⟨k - 120, this⟩
    have hk' : k - 120 + 120 = k := by omega
    have : k.divisors.card ≤ 19 := by simpa [hk'] using h2
    omega

lemma a_eq_a081512_20 : ¬ a 20 > a081512 20 :=
  not_gt_of_special hasSumNLcm_20_672 (by decide)
    (by decide) tau_lt_20_240'
    (by decide) tau_lt_360'
    (by decide) (le_of_eq a081512_19_eq.symm)

/- n = 23 lower bound for n = 24 -/

lemma tau_360_eq_24 : (360 : ℕ).divisors.card = 24 := by decide
lemma not_perfect_360 : (360 : ℕ).divisors.sum id ≠ 2 * 360 := by decide

lemma tau_le_23_off361 : ∀ k : Fin 59, (k.val + 361).divisors.card ≤ 23 := by decide

lemma tau_lt_24_of_lt_420_ne_360 {k : ℕ} (hk : k < 420) (hne : k ≠ 360) :
    k.divisors.card < 24 := by
  if h : k < 360 then
    have := tau_lt_360' k h
    omega
  else
    have : k - 361 < 59 := by omega
    have h2 := tau_le_23_off361 ⟨k - 361, this⟩
    have hk' : k - 361 + 361 = k := by omega
    have : k.divisors.card ≤ 23 := by simpa [hk'] using h2
    omega

lemma not_hasSumN_23_360 : ¬ HasSumN 23 360 := by
  intro hs
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hk, D, hD, hc, hsum⟩
  have hsub : D ⊆ (360 : ℕ).properDivisors :=
    mem_properDivisors_of_hasSumN (by decide) hD hc hsum
  have hDeq : D = (360 : ℕ).properDivisors := by
    apply Finset.eq_of_subset_of_card_le hsub
    have : (360 : ℕ).properDivisors.card = 23 := by
      have := tau_360_eq_24
      have hpc := proper_card (by decide : (360 : ℕ) ≠ 0)
      omega
    omega
  have hps := proper_sum (by decide : (360 : ℕ) ≠ 0)
  rw [← hDeq, hsum] at hps
  have : (360 : ℕ).divisors.sum id = 2 * 360 := by omega
  exact not_perfect_360 this

lemma a081512_23_ge_420 : 420 ≤ a081512 23 := by
  have hpos := a081512_pos_of_has (hasSumN_of_hasSumNLcm hasSumNLcm_23_720)
  have hs := hasSumN_sInf hpos
  by_contra hlt
  have hk : a081512 23 < 420 := lt_of_not_ge hlt
  have hτge : 24 ≤ (a081512 23).divisors.card := by
    rw [HasSumN_iff] at hs
    rcases hs with ⟨hkpos, D, hD, hc, hsum⟩
    have hsub : D ⊆ (a081512 23).properDivisors :=
      mem_properDivisors_of_hasSumN (by decide) hD hc hsum
    have := card_le_card hsub
    have hpc := proper_card hkpos.ne'
    omega
  if heq : a081512 23 = 360 then
    rw [heq] at hs
    exact not_hasSumN_23_360 hs
  else
    have : (a081512 23).divisors.card < 24 :=
      tau_lt_24_of_lt_420_ne_360 hk heq
    omega

/- n = 24 -/

lemma hasSumNLcm_24_840 : HasSumNLcm 24 840 :=
  hasSumNLcm_of_dvd 24 840
    {1,2,3,4,5,6,7,8,10,12,14,20,21,24,28,35,40,42,56,60,70,84,120,168}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma tau_lt_360_24 : ∀ k < 360, k.divisors.card < 24 := by
  intro k hk
  have := tau_lt_360' k hk
  omega

lemma tau_le_720_lt25 : ∀ k < 720, k.divisors.card < 25 := by
  intro k hk
  have := tau_le_24_720 k hk
  omega

lemma a_eq_a081512_24 : ¬ a 24 > a081512 24 :=
  not_gt_of_special hasSumNLcm_24_840 (by decide)
    (by decide) tau_lt_360_24
    (by decide) tau_le_720_lt25
    (by decide) a081512_23_ge_420

/- n = 30 -/

lemma hasSumNLcm_30_1680 : HasSumNLcm 30 1680 :=
  hasSumNLcm_of_dvd 30 1680
    {1,2,3,4,5,7,8,10,12,14,15,16,20,21,28,30,35,40,42,48,56,60,70,80,105,112,120,140,240,336}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma tau_le_29_off721 : ∀ k : Fin 119, (k.val + 721).divisors.card ≤ 29 := by decide

lemma tau_720_eq_30 : (720 : ℕ).divisors.card = 30 := by decide
lemma not_perfect_720 : (720 : ℕ).divisors.sum id ≠ 2 * 720 := by decide

lemma tau_lt_720_30 : ∀ k < 720, k.divisors.card < 30 := by
  intro k hk
  have := tau_le_24_720 k hk
  omega

lemma tau_lt_31_840 : ∀ k < 840, k.divisors.card < 31 := by
  intro k hk
  if h : k < 720 then
    have := tau_le_24_720 k h
    omega
  else if h720 : k = 720 then
    subst h720
    have := tau_720_eq_30
    omega
  else
    have hk' : k - 721 < 119 := by omega
    have h2 := tau_le_29_off721 ⟨k - 721, hk'⟩
    have hkq : k - 721 + 721 = k := by omega
    have : k.divisors.card ≤ 29 := by simpa [hkq] using h2
    omega

lemma not_hasSumN_29_720 : ¬ HasSumN 29 720 := by
  intro hs
  rw [HasSumN_iff] at hs
  rcases hs with ⟨hk, D, hD, hc, hsum⟩
  have hsub : D ⊆ (720 : ℕ).properDivisors :=
    mem_properDivisors_of_hasSumN (by decide) hD hc hsum
  have hDeq : D = (720 : ℕ).properDivisors := by
    apply Finset.eq_of_subset_of_card_le hsub
    have : (720 : ℕ).properDivisors.card = 29 := by
      have := tau_720_eq_30
      have hpc := proper_card (by decide : (720 : ℕ) ≠ 0)
      omega
    omega
  have hps := proper_sum (by decide : (720 : ℕ) ≠ 0)
  rw [← hDeq, hsum] at hps
  have : (720 : ℕ).divisors.sum id = 2 * 720 := by omega
  exact not_perfect_720 this

lemma a081512_29_ge_840 : 840 ≤ a081512 29 := by
  have hpos := a081512_pos_of_has (hasSumN_of_hasSumNLcm hasSumNLcm_29_1260)
  have hs := hasSumN_sInf hpos
  by_contra hlt
  have hk : a081512 29 < 840 := lt_of_not_ge hlt
  have hτge : 30 ≤ (a081512 29).divisors.card := by
    rw [HasSumN_iff] at hs
    rcases hs with ⟨hkpos, D, hD, hc, hsum⟩
    have hsub : D ⊆ (a081512 29).properDivisors :=
      mem_properDivisors_of_hasSumN (by decide) hD hc hsum
    have := card_le_card hsub
    have hpc := proper_card hkpos.ne'
    omega
  if h : a081512 29 < 720 then
    have : (a081512 29).divisors.card ≤ 24 := tau_le_24_720 _ h
    omega
  else if heq : a081512 29 = 720 then
    rw [heq] at hs
    exact not_hasSumN_29_720 hs
  else
    have : (a081512 29).divisors.card ≤ 29 := by
      have hk' : a081512 29 - 721 < 119 := by omega
      have h2 := tau_le_29_off721 ⟨a081512 29 - 721, hk'⟩
      have hkq : a081512 29 - 721 + 721 = a081512 29 := by omega
      simpa [hkq] using h2
    omega

lemma a_eq_a081512_30 : ¬ a 30 > a081512 30 :=
  not_gt_of_special hasSumNLcm_30_1680 (by decide)
    (by decide) tau_lt_720_30
    (by decide) tau_lt_31_840
    (by decide) a081512_29_ge_840


/- n = 31, 32 : B = 840, already have tau_lt_31_840 -/

lemma hasSumNLcm_31_1680 : HasSumNLcm 31 1680 :=
  hasSumNLcm_of_dvd 31 1680
    {1,2,3,4,5,6,7,8,10,12,14,15,16,20,21,24,28,35,40,42,48,56,60,70,80,105,112,120,140,240,336}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_32_1680 : HasSumNLcm 32 1680 :=
  hasSumNLcm_of_dvd 32 1680
    {1,2,3,4,5,6,7,8,10,12,14,15,20,21,24,28,30,35,40,42,48,56,60,70,80,84,105,112,120,168,210,240}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma tau_lt_32_840 : ∀ k < 840, k.divisors.card < 32 :=
  fun k hk => (tau_lt_31_840 k hk).trans (by decide)

lemma a_eq_a081512_31 : ¬ a 31 > a081512 31 :=
  not_gt_of_witness_tau (B := 840) hasSumNLcm_31_1680 (by decide) tau_lt_31_840 (by decide)

lemma a_eq_a081512_32 : ¬ a 32 > a081512 32 :=
  not_gt_of_witness_tau (B := 840) hasSumNLcm_32_1680 (by decide) tau_lt_32_840 (by decide)



/-- Smallest number with at least `n` divisors. -/
noncomputable def delta (n : ℕ) : ℕ := sInf {k | n ≤ k.divisors.card}

lemma tau_lt_of_lt_delta {n k : ℕ} (hk : k < delta n) :
    k.divisors.card < n := by
  by_contra h
  have : delta n ≤ k := csInf_le' (le_of_not_gt h)
  omega

lemma delta_le_of_tau_ge {n k : ℕ} (h : n ≤ k.divisors.card) : delta n ≤ k :=
  csInf_le' h

lemma pow_two_tau (k : ℕ) : (2 ^ k).divisors.card = k + 1 := by
  rw [divisors_prime_pow prime_two, card_map, card_range]

lemma exists_tau_ge (n : ℕ) : ∃ k : ℕ, n ≤ k.divisors.card :=
  ⟨2 ^ n, by rw [pow_two_tau]; omega⟩

lemma le_tau_delta (n : ℕ) : n ≤ (delta n).divisors.card :=
  Nat.sInf_mem (exists_tau_ge n)

lemma delta_pos {n : ℕ} (_hn : 1 ≤ n) : 0 < delta n := by
  have h := le_tau_delta n
  by_contra hz
  have : delta n = 0 := by omega
  rw [this, divisors_zero, card_empty] at h
  omega

/-- Powers of two are practical: every `m ≤ 2^k` is a sum of distinct divisors. -/
lemma isPractical_pow_two (k : ℕ) : IsPractical (2 ^ k) := by
  intro m hm
  refine ⟨m.bitIndices.toFinset.image (fun i => 2 ^ i), ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ m.bitIndices.toFinset.image (fun i => 2 ^ i) := mem_coe.mp hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx'
    have hle : 2 ^ i ≤ m := two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
    have hik : i ≤ k :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (hle.trans hm)
    exact mem_divisors.2 ⟨pow_dvd_pow (a := 2) hik, pow_ne_zero _ two_ne_zero⟩
  · have hinj : Set.InjOn (fun i => 2 ^ i) (m.bitIndices.toFinset : Set ℕ) :=
      fun a _ b _ h => Nat.pow_right_injective (by decide : 2 ≤ 2) h
    rw [sum_image hinj]
    exact (twoPowSum_toFinset_bitIndices m).symm

/-- If `S` can form every value `≤ ∑ S` and we insert `s ≤ ∑ S + 1`, the new set
can form every value `≤ ∑ S + s`. -/
lemma subsetSums_insert {S : Finset ℕ} {s : ℕ} (hs : s ∉ S)
    (hS : ∀ t ≤ S.sum id, t ∈ subsetSums (S : Set ℕ))
    (hbound : s ≤ S.sum id + 1) :
    ∀ t ≤ (insert s S).sum id, t ∈ subsetSums ((insert s S) : Set ℕ) := by
  intro t ht
  have hsum : (insert s S).sum id = S.sum id + s := by
    rw [sum_insert hs]; simp [add_comm]
  rw [hsum] at ht
  by_cases hle : t ≤ S.sum id
  · obtain ⟨T, hT, hsumT⟩ := hS t hle
    exact ⟨T, fun x hx => by
      have : x ∈ (S : Set ℕ) := hT hx
      simp [this], hsumT⟩
  · have : s ≤ t := by omega
    have ht' : t - s ≤ S.sum id := by omega
    obtain ⟨T, hT, hsumT⟩ := hS (t - s) ht'
    refine ⟨insert s T, ?_, ?_⟩
    · intro x hx
      have hx' : x = s ∨ x ∈ T := by
        simpa [mem_insert] using hx
      rcases hx' with rfl | hxT
      · simp
      · have : x ∈ (S : Set ℕ) := hT (by simpa using hxT)
        simp [this]
    · have hsT : s ∉ T := fun h => hs (by
        have : s ∈ (S : Set ℕ) := hT (by simpa using h)
        simpa using this)
      rw [sum_insert hsT, ← hsumT]
      omega

lemma practical_sum_lt {n s : ℕ} (hp : IsPractical n) (hs : s ∈ n.divisors) :
    s ≤ (n.divisors.filter (· < s)).sum id + 1 := by
  by_contra h
  set g := (n.divisors.filter (· < s)).sum id + 1 with hgdef
  have hg : g < s := by
    have : ¬ s ≤ (n.divisors.filter (· < s)).sum id + 1 := h
    omega
  have hgle : g ≤ n := (Nat.le_of_lt hg).trans (divisor_le hs)
  obtain ⟨T, hT, hsum⟩ := hp g hgle
  have hTsmall : T ⊆ n.divisors.filter (· < s) := by
    intro x hxT
    have hxD : x ∈ n.divisors := by
      have : x ∈ (n.divisors : Set ℕ) := hT (by simpa using hxT)
      simpa using this
    have hxlt : x < s := by
      by_contra hge
      have hxle : s ≤ x := by omega
      have hsingle : x ≤ ∑ i ∈ T, i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le i) hxT
      have : s ≤ ∑ i ∈ T, i := hxle.trans hsingle
      omega
    exact mem_filter.2 ⟨hxD, hxlt⟩
  have hleSum : ∑ i ∈ T, i ≤ ∑ i ∈ n.divisors.filter (· < s), i :=
    sum_le_sum_of_subset_of_nonneg hTsmall (fun i _ _ => Nat.zero_le i)
  have h1 : g = ∑ i ∈ T, i := hsum
  have h2 : g = (∑ i ∈ n.divisors.filter (· < s), i) + 1 := by
    simp [g, id]
  omega

lemma filter_divisors_le_succ (n a : ℕ) :
    n.divisors.filter (· ≤ a + 1) =
      if a + 1 ∈ n.divisors then
        insert (a + 1) (n.divisors.filter (· ≤ a))
      else
        n.divisors.filter (· ≤ a) := by
  ext x
  by_cases hmem : a + 1 ∈ n.divisors
  · simp only [hmem, ↓reduceIte, mem_filter, mem_insert]
    constructor
    · intro ⟨hx, hle⟩
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨hx, Nat.lt_succ_iff.mp hlt⟩
    · intro h
      rcases h with rfl | ⟨hx, hle⟩
      · exact ⟨hmem, le_rfl⟩
      · exact ⟨hx, Nat.le_succ_of_le hle⟩
  · simp only [hmem, ↓reduceIte, mem_filter]
    constructor
    · intro ⟨hx, hle⟩
      refine ⟨hx, ?_⟩
      have : x ≠ a + 1 := fun eq => hmem (eq ▸ hx)
      omega
    · intro ⟨hx, hle⟩
      exact ⟨hx, Nat.le_succ_of_le hle⟩

lemma filter_lt_succ_eq_le (n a : ℕ) :
    n.divisors.filter (· < a + 1) = n.divisors.filter (· ≤ a) := by
  ext x
  simp only [mem_filter, Nat.lt_succ_iff]

lemma filter_divisors_le_zero (n : ℕ) :
    n.divisors.filter (· ≤ 0) = ∅ := by
  ext x
  simp only [mem_filter, notMem_empty, iff_false, not_and]
  intro hx hle
  have : 0 < x := pos_of_mem_divisors hx
  omega

/-- A practical number's divisors form every integer up to `σ(n)`. -/
lemma practical_subsetSums_upto_sigma {n : ℕ} (hp : IsPractical n) :
    ∀ m ≤ n.divisors.sum id, m ∈ subsetSums (n.divisors : Set ℕ) := by
  classical
  have step : ∀ a : ℕ, ∀ t ≤ (n.divisors.filter (· ≤ a)).sum id,
      t ∈ subsetSums ((n.divisors.filter (· ≤ a)) : Set ℕ) := by
    intro a
    induction a with
    | zero =>
      intro t ht
      rw [filter_divisors_le_zero] at ht
      simp at ht
      subst t
      exact ⟨∅, by simp [filter_divisors_le_zero], by simp⟩
    | succ a ih =>
      intro t ht
      rw [filter_divisors_le_succ] at ht
      by_cases hmem : a + 1 ∈ n.divisors
      · simp only [hmem, ↓reduceIte] at ht
        have hnot : a + 1 ∉ n.divisors.filter (· ≤ a) := by simp
        have hchain : a + 1 ≤ (n.divisors.filter (· ≤ a)).sum id + 1 := by
          simpa [filter_lt_succ_eq_le] using practical_sum_lt hp hmem
        have hss := subsetSums_insert hnot ih hchain t ht
        rw [filter_divisors_le_succ, if_pos hmem]
        simpa [coe_insert] using hss
      · simp only [hmem, ↓reduceIte] at ht
        rw [filter_divisors_le_succ, if_neg hmem]
        exact ih t ht
  intro m hm
  have hfil : n.divisors.filter (· ≤ n) = n.divisors := by
    ext x
    simp only [mem_filter, and_iff_left_iff_imp]
    exact fun hx => divisor_le hx
  simpa [hfil] using step n m (by simpa [hfil] using hm)

/-! ### Structure of `delta n` -/

lemma delta_monotone {m n : ℕ} (hmn : m ≤ n) : delta m ≤ delta n :=
  delta_le_of_tau_ge (hmn.trans (le_tau_delta n))

lemma factorization_pos_of_dvd_prime {K p : ℕ} (hp : p.Prime) (hd : p ∣ K) (hK : K ≠ 0) :
    0 < K.factorization p := by
  rw [pos_iff_ne_zero, Ne, factorization_eq_zero_iff]
  push_neg
  exact ⟨hp, hd, hK⟩

/-- Replacing the prime power `p^b ‖ K` by `q^b` does not change `τ`. -/
lemma tau_swap_prime {K p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpd : p ∣ K) (hK : K ≠ 0) (hqK : ¬ q ∣ K) :
    ((q ^ K.factorization p) * ordCompl[p] K).divisors.card = K.divisors.card := by
  have hproj : ordProj[p] K ∣ K := ordProj_dvd K p
  have hdecomp : K = ordProj[p] K * ordCompl[p] K := (Nat.mul_div_cancel' hproj).symm
  have hcop : Coprime (ordProj[p] K) (ordCompl[p] K) :=
    (Nat.coprime_ordCompl hp hK).pow_left _
  have hcop' : Coprime (q ^ K.factorization p) (ordCompl[p] K) := by
    refine (Nat.Coprime.pow_left _ ?_)
    have : ¬ q ∣ ordCompl[p] K := by
      intro hdvd
      exact hqK (hdvd.trans (div_dvd_of_dvd hproj))
    exact (hq.coprime_iff_not_dvd).2 this
  have hτK : K.divisors.card =
      (ordProj[p] K).divisors.card * (ordCompl[p] K).divisors.card := by
    have h := hcop.card_divisors_mul
    rwa [← hdecomp] at h
  have hτp : (ordProj[p] K).divisors.card = K.factorization p + 1 := by
    rw [divisors_prime_pow hp, card_map, card_range]
  have hτq : (q ^ K.factorization p).divisors.card = K.factorization p + 1 := by
    rw [divisors_prime_pow hq, card_map, card_range]
  rw [hcop'.card_divisors_mul, hτq, hτK, hτp]

lemma two_dvd_delta {n : ℕ} (hn : 3 ≤ n) : 2 ∣ delta n := by
  set K := delta n
  have hτ : n ≤ K.divisors.card := le_tau_delta n
  have hKpos : 0 < K := delta_pos (by omega)
  by_contra hodd
  have hK1 : K ≠ 1 := by
    intro h
    have hτ1 : n ≤ (1 : ℕ).divisors.card := by simpa [h] using hτ
    have : (1 : ℕ).divisors.card = 1 := by simp
    omega
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd hK1
  have hpne2 : p ≠ 2 := fun e => hodd (e ▸ hpdvd)
  let K' := (2 ^ K.factorization p) * ordCompl[p] K
  have hτeq : K'.divisors.card = K.divisors.card :=
    tau_swap_prime hp prime_two hpdvd hKpos.ne' hodd
  have hlt : K' < K := by
    have hproj : ordProj[p] K ∣ K := ordProj_dvd K p
    have hdecomp : K = ordProj[p] K * ordCompl[p] K := (Nat.mul_div_cancel' hproj).symm
    have hb : 0 < K.factorization p := factorization_pos_of_dvd_prime hp hpdvd hKpos.ne'
    have hcompl_pos : 0 < ordCompl[p] K :=
      Nat.div_pos (Nat.le_of_dvd hKpos hproj) (pow_pos hp.pos _)
    have : 2 ^ K.factorization p < p ^ K.factorization p :=
      Nat.pow_lt_pow_left (lt_of_le_of_ne hp.two_le hpne2.symm) hb.ne'
    rw [hdecomp]
    exact Nat.mul_lt_mul_of_pos_right this hcompl_pos
  have : delta n ≤ K' := delta_le_of_tau_ge (hτ.trans_eq hτeq.symm)
  omega

lemma three_dvd_delta {n : ℕ} (hn : 4 ≤ n) : 3 ∣ delta n := by
  set K := delta n
  have hτ : n ≤ K.divisors.card := le_tau_delta n
  have hKpos : 0 < K := delta_pos (by omega)
  have h2 : 2 ∣ K := two_dvd_delta (by omega)
  by_contra h3
  by_cases hex : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ K
  · obtain ⟨p, hp, hp5, hpdvd⟩ := hex
    let K' := (3 ^ K.factorization p) * ordCompl[p] K
    have hτeq : K'.divisors.card = K.divisors.card :=
      tau_swap_prime hp prime_three hpdvd hKpos.ne' h3
    have hlt : K' < K := by
      have hproj : ordProj[p] K ∣ K := ordProj_dvd K p
      have hdecomp : K = ordProj[p] K * ordCompl[p] K := (Nat.mul_div_cancel' hproj).symm
      have hb : 0 < K.factorization p := factorization_pos_of_dvd_prime hp hpdvd hKpos.ne'
      have hcompl_pos : 0 < ordCompl[p] K :=
        Nat.div_pos (Nat.le_of_dvd hKpos hproj) (pow_pos hp.pos _)
      have : 3 ^ K.factorization p < p ^ K.factorization p :=
        Nat.pow_lt_pow_left (by omega) hb.ne'
      rw [hdecomp]
      exact Nat.mul_lt_mul_of_pos_right this hcompl_pos
    have : delta n ≤ K' := delta_le_of_tau_ge (hτ.trans_eq hτeq.symm)
    omega
  · have honly2 : ∀ q : ℕ, q.Prime → q ∣ K → q = 2 := by
      intro q hq hdq
      by_contra hne
      have hne3 : q ≠ 3 := fun e => by subst e; exact h3 hdq
      have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three hne hne3
      exact hex ⟨q, hq, hq5, hdq⟩
    have hlen : K.primeFactorsList.length = K.factorization 2 := by
      rw [← primeFactorsList_count_eq (p := 2)]
      refine (List.count_eq_length.2 ?_).symm
      intro x hx
      exact (honly2 x (prime_of_mem_primeFactorsList hx)
        (dvd_of_mem_primeFactorsList hx)).symm
    have hKpow : K = 2 ^ K.factorization 2 := by
      calc
        K = 2 ^ K.primeFactorsList.length :=
          eq_prime_pow_of_unique_prime_dvd hKpos.ne'
            (fun {d} hd hdvd => honly2 d hd hdvd)
        _ = 2 ^ K.factorization 2 := by rw [hlen]
    set a := K.factorization 2
    have hτeq : K.divisors.card = a + 1 := by
      have h := pow_two_tau a
      rwa [← hKpow] at h
    have ha : 3 ≤ a := by omega
    let K' := 2 ^ (a - 2) * 3
    have hτ' : n ≤ K'.divisors.card := by
      have hapos : 0 < a - 2 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 3) ha)
      have hcop : Coprime (2 ^ (a - 2)) 3 :=
        (Nat.coprime_pow_left_iff hapos _ _).2 (by decide)
      have h3c : (3 : ℕ).divisors.card = 2 := by
        rw [prime_three.divisors, card_insert_of_notMem (by decide), card_singleton]
      have h2c : (2 ^ (a - 2)).divisors.card = a - 2 + 1 := pow_two_tau _
      have hcard : K'.divisors.card = (a - 2 + 1) * 2 := by
        simpa [K', h2c, h3c] using hcop.card_divisors_mul
      have : n ≤ a + 1 := by omega
      have : a + 1 ≤ (a - 2 + 1) * 2 := by omega
      omega
    have hlt : K' < K := by
      have hpow : 2 ^ a = 2 ^ (a - 2 + 2) := by rw [Nat.sub_add_cancel (by omega)]
      have hmul : 2 ^ (a - 2) * 3 < 2 ^ (a - 2) * 4 :=
        Nat.mul_lt_mul_of_pos_left (by decide : 3 < 4) (pow_pos (by decide : 0 < 2) _)
      have : K' < 2 ^ a := by
        calc
          K' = 2 ^ (a - 2) * 3 := rfl
          _ < 2 ^ (a - 2) * 4 := hmul
          _ = 2 ^ (a - 2) * (2 ^ 2) := by norm_num
          _ = 2 ^ (a - 2 + 2) := (pow_add 2 _ _).symm
          _ = 2 ^ a := hpow.symm
      exact this.trans_eq hKpow.symm
    have : delta n ≤ K' := delta_le_of_tau_ge hτ'
    omega

lemma six_dvd_delta {n : ℕ} (hn : 4 ≤ n) : 6 ∣ delta n := by
  have h2 := two_dvd_delta (by omega : 3 ≤ n)
  have h3 := three_dvd_delta hn
  have : Nat.lcm 2 3 ∣ delta n := Nat.lcm_dvd h2 h3
  simpa using this

/-- Seed: `{K, 2K/3, K/3}` sums to `2K` when `6 ∣ K`. -/
lemma seed_sum {K : ℕ} (h6 : 6 ∣ K) :
    K + 2 * K / 3 + K / 3 = 2 * K := by
  have h3 : 3 ∣ K := (dvd_trans (by decide : 3 ∣ 6) h6)
  have h2 : 2 ∣ K := (dvd_trans (by decide : 2 ∣ 6) h6)
  have : 2 * K / 3 + K / 3 = K := by
    have : 2 * (K / 3) + K / 3 = K := by
      have := Nat.mul_div_cancel' h3
      omega
    have hmul : 2 * K / 3 = 2 * (K / 3) := by
      rw [Nat.mul_div_assoc 2 h3]
    omega
  omega

lemma seed_dvd_two_mul {K : ℕ} (h6 : 6 ∣ K) :
    K ∣ 2 * K ∧ 2 * K / 3 ∣ 2 * K ∧ K / 3 ∣ 2 * K := by
  have h3 : 3 ∣ K := (dvd_trans (by decide : 3 ∣ 6) h6)
  refine ⟨dvd_mul_left _ _, ?_, ?_⟩
  · have : 2 * K / 3 = 2 * (K / 3) := Nat.mul_div_assoc 2 h3
    rw [this]
    exact mul_dvd_mul_left 2 (div_dvd_of_dvd h3)
  · exact (div_dvd_of_dvd h3).trans (dvd_mul_left _ _)

lemma six_dvd_pos {K : ℕ} (h6 : 6 ∣ K) (hK : K ≠ 0) : 6 ≤ K :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hK) h6

lemma seed_pos {K : ℕ} (h6 : 6 ∣ K) (hK : K ≠ 0) :
    0 < K ∧ 0 < 2 * K / 3 ∧ 0 < K / 3 := by
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK
  have h3 : 3 ∣ K := dvd_trans (by decide : 3 ∣ 6) h6
  have hK3 : 0 < K / 3 := Nat.div_pos (Nat.le_of_dvd hKpos h3) (by decide)
  refine ⟨hKpos, ?_, hK3⟩
  have : 2 * K / 3 = 2 * (K / 3) := Nat.mul_div_assoc 2 h3
  rw [this]; omega

lemma seed_distinct {K : ℕ} (h6 : 6 ∣ K) (hK0 : K ≠ 0) :
    K ≠ 2 * K / 3 ∧ K ≠ K / 3 ∧ 2 * K / 3 ≠ K / 3 := by
  have ⟨hK, h23, h13⟩ := seed_pos h6 hK0
  have h3 : 3 ∣ K := dvd_trans (by decide : 3 ∣ 6) h6
  have hmul : 2 * K / 3 = 2 * (K / 3) := Nat.mul_div_assoc 2 h3
  have hK3 : K = 3 * (K / 3) := (Nat.mul_div_cancel' h3).symm
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : K = 2 * (K / 3) := h.trans hmul
    omega
  · intro h
    have : 3 * (K / 3) = K / 3 := hK3 ▸ h
    omega
  · intro h
    have : 2 * (K / 3) = K / 3 := hmul ▸ h
    omega

lemma seed_card {K : ℕ} (h6 : 6 ∣ K) (hK0 : K ≠ 0) :
    ({K, 2 * K / 3, K / 3} : Finset ℕ).card = 3 := by
  have ⟨h1, h2, h3⟩ := seed_distinct h6 hK0
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp [h3]
  · simp [h1, h2]

lemma seed_sum_finset {K : ℕ} (h6 : 6 ∣ K) (hK0 : K ≠ 0) :
    ({K, 2 * K / 3, K / 3} : Finset ℕ).sum id = 2 * K := by
  have ⟨h1, h2, h3⟩ := seed_distinct h6 hK0
  rw [sum_insert, sum_insert, sum_singleton]
  · simp [id]
    have := seed_sum h6
    omega
  · simp [h3]
  · simp [h1, h2]

lemma gcd_K_two_K_div_three {K : ℕ} (h6 : 6 ∣ K) :
    Nat.gcd K (2 * K / 3) = K / 3 := by
  have h3 : 3 ∣ K := dvd_trans (by decide : 3 ∣ 6) h6
  have hmul : 2 * K / 3 = 2 * (K / 3) := Nat.mul_div_assoc 2 h3
  have hKeq : K = 3 * (K / 3) := (Nat.mul_div_cancel' h3).symm
  rw [hmul, hKeq, Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
  rw [mul_comm 3, mul_comm 2, Nat.gcd_mul_left]
  norm_num

lemma lcm_K_two_K_div_three {K : ℕ} (h6 : 6 ∣ K) :
    Nat.lcm K (2 * K / 3) = 2 * K := by
  rcases eq_or_ne K 0 with rfl | hK0
  · simp
  have h3 : 3 ∣ K := dvd_trans (by decide : 3 ∣ 6) h6
  have hmul : 2 * K / 3 = 2 * (K / 3) := Nat.mul_div_assoc 2 h3
  have hg : Nat.gcd K (2 * K / 3) = K / 3 := gcd_K_two_K_div_three h6
  have hpos : 0 < K / 3 := (seed_pos h6 hK0).2.2
  have hKeq : K = 3 * (K / 3) := (Nat.mul_div_cancel' h3).symm
  have hmul' : K * (2 * K / 3) = 2 * K * (K / 3) := by
    rw [hmul, hKeq]; ring
  have hprod := Nat.gcd_mul_lcm K (2 * K / 3)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    (K / 3) * Nat.lcm K (2 * K / 3)
        = Nat.gcd K (2 * K / 3) * Nat.lcm K (2 * K / 3) := by rw [hg]
    _ = K * (2 * K / 3) := hprod
    _ = 2 * K * (K / 3) := hmul'
    _ = (K / 3) * (2 * K) := by ring

lemma two_K_div_three_dvd_form {K : ℕ} (h6 : 6 ∣ K) :
    K / 3 ∣ 2 * K / 3 := by
  have h3 : 3 ∣ K := dvd_trans (by decide : 3 ∣ 6) h6
  have hmul : 2 * K / 3 = 2 * (K / 3) := Nat.mul_div_assoc 2 h3
  rw [hmul]
  exact dvd_mul_left _ _

lemma seed_lcm {K : ℕ} (h6 : 6 ∣ K) (hK0 : K ≠ 0) :
    ({K, 2 * K / 3, K / 3} : Finset ℕ).lcm id = 2 * K := by
  have ⟨h1, h2, h3⟩ := seed_distinct h6 hK0
  have hl12 := lcm_K_two_K_div_three h6
  have hdiv := two_K_div_three_dvd_form h6
  rw [lcm_insert, lcm_insert, lcm_singleton]
  simp only [id, normalize_eq]
  have hleft : GCDMonoid.lcm (2 * K / 3) (K / 3) = 2 * K / 3 :=
    Nat.dvd_antisymm (Nat.lcm_dvd dvd_rfl hdiv) (Nat.dvd_lcm_left _ _)
  rw [hleft]
  exact hl12

/-- The seed triple is a 3-element divisor set of `2K` summing to `2K` with lcm `2K`. -/
lemma seed_subset_divisors {K : ℕ} (h6 : 6 ∣ K) (hK0 : K ≠ 0) :
    ({K, 2 * K / 3, K / 3} : Finset ℕ) ⊆ (2 * K).divisors := by
  intro d hd
  have ⟨hd1, hd2, hd3⟩ := seed_dvd_two_mul h6
  have hpos : 0 < 2 * K := by have := (seed_pos h6 hK0).1; omega
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · exact mem_divisors.2 ⟨hd1, hpos.ne'⟩
  · exact mem_divisors.2 ⟨hd2, hpos.ne'⟩
  · exact mem_divisors.2 ⟨hd3, hpos.ne'⟩

lemma seed_proper {K : ℕ} (h6 : 6 ∣ K) (hK0 : K ≠ 0) :
    ({K, 2 * K / 3, K / 3} : Finset ℕ) ⊆ (2 * K).properDivisors := by
  intro d hd
  have hsub := seed_subset_divisors h6 hK0 hd
  have ⟨h1, h2, h3⟩ := seed_distinct h6 hK0
  have ⟨hp1, hp2, hp3⟩ := seed_pos h6 hK0
  have hdvd := dvd_of_mem_divisors hsub
  have hlt : d < 2 * K := by
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> omega
  exact Nat.mem_properDivisors.2 ⟨hdvd, hlt⟩

lemma hasSumNLcm_seed {K : ℕ} (h6 : 6 ∣ K) (hK0 : K ≠ 0) :
    HasSumNLcm 3 (2 * K) :=
  hasSumNLcm_of_dvd 3 (2 * K) {K, 2 * K / 3, K / 3}
    (fun d hd => dvd_of_mem_divisors (seed_subset_divisors h6 hK0 hd))
    (seed_card h6 hK0) (seed_sum_finset h6 hK0) (seed_lcm h6 hK0)
    (by have := (seed_pos h6 hK0).1; omega)

lemma tau_le_16_of_lt_120 {k : ℕ} (hk : k < 120) : k.divisors.card ≤ 16 := by
  interval_cases k <;> decide

lemma tau_le_20_of_lt_240 {k : ℕ} (hk : k < 240) : k.divisors.card ≤ 20 := by
  interval_cases k <;> decide

lemma tau_prime_pow {p e : ℕ} (hp : p.Prime) :
    (p ^ e).divisors.card = e + 1 := by
  rw [divisors_prime_pow hp, card_map, card_range]

lemma coprime_two_three (a b : ℕ) : Coprime (2 ^ a) (3 ^ b) :=
  ((by decide : Coprime 2 3).pow a b)

lemma coprime_two_five (a c : ℕ) : Coprime (2 ^ a) (5 ^ c) :=
  ((by decide : Coprime 2 5).pow a c)

lemma coprime_two_seven (a d : ℕ) : Coprime (2 ^ a) (7 ^ d) :=
  ((by decide : Coprime 2 7).pow a d)

lemma coprime_three_five (b c : ℕ) : Coprime (3 ^ b) (5 ^ c) :=
  ((by decide : Coprime 3 5).pow b c)

lemma coprime_three_seven (b d : ℕ) : Coprime (3 ^ b) (7 ^ d) :=
  ((by decide : Coprime 3 7).pow b d)

lemma coprime_five_seven (c d : ℕ) : Coprime (5 ^ c) (7 ^ d) :=
  ((by decide : Coprime 5 7).pow c d)

lemma tau_2a3b (a b : ℕ) :
    (2 ^ a * 3 ^ b).divisors.card = (a + 1) * (b + 1) := by
  rw [(coprime_two_three a b).card_divisors_mul,
    tau_prime_pow prime_two, tau_prime_pow prime_three]

lemma tau_2a3b5c (a b c : ℕ) :
    (2 ^ a * 3 ^ b * 5 ^ c).divisors.card = (a + 1) * (b + 1) * (c + 1) := by
  have hcop : Coprime (2 ^ a * 3 ^ b) (5 ^ c) :=
    Coprime.mul_left (coprime_two_five a c) (coprime_three_five b c)
  rw [hcop.card_divisors_mul, tau_2a3b, tau_prime_pow prime_five]

lemma tau_2a3b5c7d (a b c d : ℕ) :
    (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d).divisors.card =
      (a + 1) * (b + 1) * (c + 1) * (d + 1) := by
  have hcop : Coprime (2 ^ a * 3 ^ b * 5 ^ c) (7 ^ d) :=
    Coprime.mul_left
      (Coprime.mul_left (coprime_two_seven a d) (coprime_three_seven b d))
      (coprime_five_seven c d)
  rw [hcop.card_divisors_mul, tau_2a3b5c, tau_prime_pow prime_seven]

lemma le_form_of_3pow (a b c d : ℕ) :
    3 ^ b ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
  have h1 : 3 ^ b ≤ 2 ^ a * 3 ^ b :=
    Nat.le_mul_of_pos_left _ (pow_pos (by decide : 0 < 2) a)
  have h2 : 2 ^ a * 3 ^ b ≤ 2 ^ a * 3 ^ b * 5 ^ c :=
    Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < 5) c)
  have h3 : 2 ^ a * 3 ^ b * 5 ^ c ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d :=
    Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < 7) d)
  exact h1.trans (h2.trans h3)

lemma le_form_of_5pow (a b c d : ℕ) :
    5 ^ c ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
  have h1 : 5 ^ c ≤ 2 ^ a * 3 ^ b * 5 ^ c :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (pow_pos (by decide : 0 < 2) a)
      (pow_pos (by decide : 0 < 3) b))
  have h2 : 2 ^ a * 3 ^ b * 5 ^ c ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d :=
    Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < 7) d)
  exact h1.trans h2

lemma le_form_of_7pow (a b c d : ℕ) :
    7 ^ d ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d :=
  Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos
      (pow_pos (by decide : 0 < 2) a) (pow_pos (by decide : 0 < 3) b))
      (pow_pos (by decide : 0 < 5) c))

lemma le_form_of_2pow (a b c d : ℕ) :
    2 ^ a ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
  have h1 : 2 ^ a ≤ 2 ^ a * 3 ^ b :=
    Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < 3) b)
  have h2 : 2 ^ a * 3 ^ b ≤ 2 ^ a * 3 ^ b * 5 ^ c :=
    Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < 5) c)
  have h3 : 2 ^ a * 3 ^ b * 5 ^ c ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d :=
    Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < 7) d)
  exact h1.trans (h2.trans h3)

lemma eq_form_of_primes_le_seven {k : ℕ} (h0 : k ≠ 0)
    (h : ∀ p ∈ k.primeFactors, p ≤ 7) :
    k = 2 ^ k.factorization 2 * 3 ^ k.factorization 3 *
        5 ^ k.factorization 5 * 7 ^ k.factorization 7 := by
  have hsupp : k.factorization.support ⊆ ({2, 3, 5, 7} : Finset ℕ) := by
    intro p hp
    have hpP : p.Prime := prime_of_mem_primeFactors (by
      simpa [Nat.support_factorization] using hp)
    have hple : p ≤ 7 := h p (by simpa [Nat.support_factorization] using hp)
    have : 2 ≤ p := hpP.two_le
    interval_cases p
    · simp
    · simp
    · exact absurd hpP (by decide : ¬ Nat.Prime 4)
    · simp
    · exact absurd hpP (by decide : ¬ Nat.Prime 6)
    · simp
  have hprod := Finsupp.prod_of_support_subset k.factorization hsupp (fun p e => p ^ e)
      (fun _ _ => by simp)
  nth_rw 1 [← factorization_prod_pow_eq_self h0]
  rw [hprod]
  rw [prod_insert (by decide : (2 : ℕ) ∉ {3, 5, 7}),
      prod_insert (by decide : (3 : ℕ) ∉ {5, 7}),
      prod_insert (by decide : (5 : ℕ) ∉ {7}),
      prod_singleton]
  simp [mul_assoc]

lemma tau_mul_ppow {k p : ℕ} (hp : p.Prime) (h0 : k ≠ 0) (hpd : p ∣ k) :
    k.divisors.card =
      (k.factorization p + 1) * (k / p ^ k.factorization p).divisors.card := by
  have hpe : p ^ k.factorization p ∣ k :=
    (hp.pow_dvd_iff_le_factorization h0).2 le_rfl
  have hdecomp : k = p ^ k.factorization p * (k / p ^ k.factorization p) :=
    (Nat.mul_div_cancel' hpe).symm
  have hcop : Coprime (p ^ k.factorization p) (k / p ^ k.factorization p) :=
    (Nat.coprime_ordCompl hp h0).pow_left _
  have h := hcop.card_divisors_mul
  rw [← hdecomp, tau_prime_pow hp] at h
  exact h

lemma fact_pos_of_mem {k p : ℕ} (hp : p.Prime) (h0 : k ≠ 0) (hpd : p ∣ k) :
    0 < k.factorization p := by
  rw [pos_iff_ne_zero, Ne, factorization_eq_zero_iff]
  push_neg
  exact ⟨hp, hpd, h0⟩

lemma primes_le_seven_of_not_ge_eleven {k : ℕ}
    (hex : ¬ ∃ p ∈ k.primeFactors, 11 ≤ p) :
    ∀ p ∈ k.primeFactors, p ≤ 7 := by
  intro p hp'
  have hpP := prime_of_mem_primeFactors hp'
  by_cases h2 : p = 2
  · omega
  by_cases h3 : p = 3
  · omega
  by_cases h5 : p = 5
  · omega
  by_cases h7 : p = 7
  · omega
  have hp5 : 5 ≤ p := hpP.five_le_of_ne_two_of_ne_three h2 h3
  have hp11 : 11 ≤ p := by
    have hpne5 : p ≠ 5 := h5
    have : 6 ≤ p := by omega
    have : p ≠ 6 := fun e => by subst e; exact absurd hpP (by decide : ¬ Nat.Prime 6)
    have : 7 ≤ p := by omega
    have hpne7 : p ≠ 7 := h7
    have : 8 ≤ p := by omega
    have : p ≠ 8 := fun e => by subst e; exact absurd hpP (by decide : ¬ Nat.Prime 8)
    have : 9 ≤ p := by omega
    have : p ≠ 9 := fun e => by subst e; exact absurd hpP (by decide : ¬ Nat.Prime 9)
    have : 10 ≤ p := by omega
    have : p ≠ 10 := fun e => by subst e; exact absurd hpP (by decide : ¬ Nat.Prime 10)
    omega
  exact (hex ⟨p, hp', hp11⟩).elim

lemma tau_le_32_of_form_lt_1260 (a b c d : ℕ)
    (hle : 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d < 1260) :
    (a + 1) * (b + 1) * (c + 1) * (d + 1) ≤ 32 := by
  have ha : a ≤ 10 := by
    contrapose! hle
    have : 2 ^ 11 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1260 ≤ 2048 := by decide
      _ = 2 ^ 11 := by decide
      _ ≤ 2 ^ a := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_2pow a b c d
  have hb : b ≤ 6 := by
    contrapose! hle
    have : 3 ^ 7 ≤ 3 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1260 ≤ 2187 := by decide
      _ = 3 ^ 7 := by decide
      _ ≤ 3 ^ b := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_3pow a b c d
  have hc : c ≤ 4 := by
    contrapose! hle
    have : 5 ^ 5 ≤ 5 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1260 ≤ 3125 := by decide
      _ = 5 ^ 5 := by decide
      _ ≤ 5 ^ c := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_5pow a b c d
  have hd : d ≤ 3 := by
    contrapose! hle
    have : 7 ^ 4 ≤ 7 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1260 ≤ 2401 := by decide
      _ = 7 ^ 4 := by decide
      _ ≤ 7 ^ d := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_7pow a b c d
  revert hle
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> decide

lemma tau_le_32_of_lt_1260 {k : ℕ} (hk : k < 1260) : k.divisors.card ≤ 32 := by
  rcases eq_or_ne k 0 with rfl | h0
  · simp
  by_cases hex : ∃ p ∈ k.primeFactors, 11 ≤ p
  · obtain ⟨p, hpS, hp11⟩ := hex
    have hp : p.Prime := prime_of_mem_primeFactors hpS
    have hpd : p ∣ k := dvd_of_mem_primeFactors hpS
    have hepos := fact_pos_of_mem hp h0 hpd
    have hτ := tau_mul_ppow hp h0 hpd
    have he2 : k.factorization p ≤ 2 := by
      by_contra h
      have hdiv : p ^ 3 ∣ k := (hp.pow_dvd_iff_le_factorization h0).2 (by omega)
      have : 11 ^ 3 ≤ k :=
        (Nat.pow_le_pow_left hp11 3).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdiv)
      omega
    rcases eq_or_lt_of_le he2 with heq | hlt
    · have hm : k / p ^ 2 ≤ 10 := by
        have hp2 : 121 ≤ p ^ 2 := by
          have := Nat.pow_le_pow_left hp11 2
          simpa using this
        have hdiv1 : k / p ^ 2 ≤ k / 121 :=
          Nat.div_le_div_left hp2 (by decide : 0 < 121)
        have hdiv2 : k / 121 ≤ 1259 / 121 :=
          Nat.div_le_div_right (Nat.le_of_lt_succ hk)
        omega
      have hmτ : (k / p ^ 2).divisors.card ≤ 10 :=
        (k / p ^ 2).card_divisors_le_self.trans hm
      rw [hτ, heq]
      omega
    · have he1 : k.factorization p = 1 := by omega
      have hm_lt : k / p < 120 := by
        have : k / p ≤ k / 11 :=
          Nat.div_le_div_left hp11 (by decide : 0 < 11)
        omega
      have hmτ : (k / p).divisors.card ≤ 16 := tau_le_16_of_lt_120 hm_lt
      rw [hτ, he1, pow_one]
      omega
  · have hle7 := primes_le_seven_of_not_ge_eleven hex
    have hform := eq_form_of_primes_le_seven h0 hle7
    have hval : 2 ^ k.factorization 2 * 3 ^ k.factorization 3 *
        5 ^ k.factorization 5 * 7 ^ k.factorization 7 < 1260 := by rwa [← hform]
    rw [hform, tau_2a3b5c7d]
    exact tau_le_32_of_form_lt_1260 _ _ _ _ hval

lemma tau_1260 : (1260 : ℕ).divisors.card = 36 := by decide

lemma delta_eq_1260 {n : ℕ} (hn : 33 ≤ n) (h36 : n ≤ 36) : delta n = 1260 := by
  apply le_antisymm
  · exact delta_le_of_tau_ge (by have := tau_1260; omega)
  · by_contra h
    have hlt : delta n < 1260 := Nat.lt_of_le_of_ne (Nat.le_of_not_ge h) (Ne.symm (by omega))
    have hτ := tau_le_32_of_lt_1260 hlt
    have hge := le_tau_delta n
    omega

lemma tau_le_16_of_lt_168 {k : ℕ} (hk : k < 168) : k.divisors.card ≤ 16 := by
  interval_cases k <;> decide

lemma tau_le_36_of_form_lt_1680 (a b c d : ℕ)
    (hle : 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d < 1680) :
    (a + 1) * (b + 1) * (c + 1) * (d + 1) ≤ 36 := by
  have ha : a ≤ 10 := by
    contrapose! hle
    have : 2 ^ 11 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1680 ≤ 2048 := by decide
      _ = 2 ^ 11 := by decide
      _ ≤ 2 ^ a := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_2pow a b c d
  have hb : b ≤ 6 := by
    contrapose! hle
    have : 3 ^ 7 ≤ 3 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1680 ≤ 2187 := by decide
      _ = 3 ^ 7 := by decide
      _ ≤ 3 ^ b := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_3pow a b c d
  have hc : c ≤ 4 := by
    contrapose! hle
    have : 5 ^ 5 ≤ 5 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1680 ≤ 3125 := by decide
      _ = 5 ^ 5 := by decide
      _ ≤ 5 ^ c := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_5pow a b c d
  have hd : d ≤ 3 := by
    contrapose! hle
    have : 7 ^ 4 ≤ 7 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      1680 ≤ 2401 := by decide
      _ = 7 ^ 4 := by decide
      _ ≤ 7 ^ d := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_7pow a b c d
  revert hle
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> decide

lemma tau_le_36_of_lt_1680 {k : ℕ} (hk : k < 1680) : k.divisors.card ≤ 36 := by
  rcases eq_or_ne k 0 with rfl | h0
  · simp
  by_cases hex : ∃ p ∈ k.primeFactors, 11 ≤ p
  · obtain ⟨p, hpS, hp11⟩ := hex
    have hp : p.Prime := prime_of_mem_primeFactors hpS
    have hpd : p ∣ k := dvd_of_mem_primeFactors hpS
    have hτ := tau_mul_ppow hp h0 hpd
    have he3 : k.factorization p ≤ 3 := by
      by_contra h
      have hdiv : p ^ 4 ∣ k := (hp.pow_dvd_iff_le_factorization h0).2 (by omega)
      have : 11 ^ 4 ≤ k :=
        (Nat.pow_le_pow_left hp11 4).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdiv)
      omega
    rcases le_iff_eq_or_lt.mp he3 with heq3 | hlt3
    · -- e = 3
      have hm : k / p ^ 3 ≤ 1 := by
        have hp3 : 1331 ≤ p ^ 3 := by
          have := Nat.pow_le_pow_left hp11 3
          simpa using this
        have hdiv1 : k / p ^ 3 ≤ k / 1331 :=
          Nat.div_le_div_left hp3 (by decide : 0 < 1331)
        have hdiv2 : k / 1331 ≤ 1679 / 1331 :=
          Nat.div_le_div_right (Nat.le_of_lt_succ hk)
        omega
      have hmτ : (k / p ^ 3).divisors.card ≤ 1 :=
        (k / p ^ 3).card_divisors_le_self.trans hm
      rw [hτ, heq3]
      omega
    · rcases le_iff_eq_or_lt.mp (Nat.le_of_lt_succ hlt3) with heq2 | hlt2
      · -- e = 2
        have hm : k / p ^ 2 ≤ 13 := by
          have hp2 : 121 ≤ p ^ 2 := by
            have := Nat.pow_le_pow_left hp11 2
            simpa using this
          have hdiv1 : k / p ^ 2 ≤ k / 121 :=
            Nat.div_le_div_left hp2 (by decide : 0 < 121)
          have hdiv2 : k / 121 ≤ 1679 / 121 :=
            Nat.div_le_div_right (Nat.le_of_lt_succ hk)
          omega
        have hmτ' : (k / p ^ 2).divisors.card ≤ 6 := by
          have : k / p ^ 2 < 14 := by omega
          interval_cases k / p ^ 2 <;> decide
        rw [hτ, heq2]
        omega
      · -- e = 1 (or 0, but 0 is impossible)
        have he1 : k.factorization p = 1 := by
          have hpos := fact_pos_of_mem hp h0 hpd
          omega
        have hm_lt : k / p < 168 := by
          have h1 : k / p ≤ k / 11 := Nat.div_le_div_left hp11 (by decide : 0 < 11)
          have h2 : k / 11 ≤ 1679 / 11 := Nat.div_le_div_right (Nat.le_of_lt_succ hk)
          omega
        have hmτ : (k / p).divisors.card ≤ 16 := tau_le_16_of_lt_168 hm_lt
        rw [hτ, he1, pow_one]
        omega
  · have hle7 := primes_le_seven_of_not_ge_eleven hex
    have hform := eq_form_of_primes_le_seven h0 hle7
    have hval : 2 ^ k.factorization 2 * 3 ^ k.factorization 3 *
        5 ^ k.factorization 5 * 7 ^ k.factorization 7 < 1680 := by rwa [← hform]
    rw [hform, tau_2a3b5c7d]
    exact tau_le_36_of_form_lt_1680 _ _ _ _ hval

lemma tau_1680 : (1680 : ℕ).divisors.card = 40 := by decide

lemma delta_eq_1680 {n : ℕ} (hn : 37 ≤ n) (h40 : n ≤ 40) : delta n = 1680 := by
  apply le_antisymm
  · exact delta_le_of_tau_ge (by have := tau_1680; omega)
  · by_contra h
    have hlt : delta n < 1680 := Nat.lt_of_le_of_ne (Nat.le_of_not_ge h) (Ne.symm (by omega))
    have hτ := tau_le_36_of_lt_1680 hlt
    have hge := le_tau_delta n
    omega

lemma tau_le_40_of_form_lt_2520 (a b c d : ℕ)
    (hle : 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d < 2520) :
    (a + 1) * (b + 1) * (c + 1) * (d + 1) ≤ 40 := by
  have ha : a ≤ 11 := by
    contrapose! hle
    have : 2 ^ 12 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      2520 ≤ 4096 := by decide
      _ = 2 ^ 12 := by decide
      _ ≤ 2 ^ a := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_2pow a b c d
  have hb : b ≤ 7 := by
    contrapose! hle
    have : 3 ^ 8 ≤ 3 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      2520 ≤ 6561 := by decide
      _ = 3 ^ 8 := by decide
      _ ≤ 3 ^ b := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_3pow a b c d
  have hc : c ≤ 4 := by
    contrapose! hle
    have : 5 ^ 5 ≤ 5 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      2520 ≤ 3125 := by decide
      _ = 5 ^ 5 := by decide
      _ ≤ 5 ^ c := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_5pow a b c d
  have hd : d ≤ 4 := by
    contrapose! hle
    have : 7 ^ 5 ≤ 7 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      2520 ≤ 16807 := by decide
      _ = 7 ^ 5 := by decide
      _ ≤ 7 ^ d := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_7pow a b c d
  revert hle
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> decide

lemma tau_le_40_of_lt_2520 {k : ℕ} (hk : k < 2520) : k.divisors.card ≤ 40 := by
  rcases eq_or_ne k 0 with rfl | h0
  · simp
  by_cases hex : ∃ p ∈ k.primeFactors, 11 ≤ p
  · obtain ⟨p, hpS, hp11⟩ := hex
    have hp : p.Prime := prime_of_mem_primeFactors hpS
    have hpd : p ∣ k := dvd_of_mem_primeFactors hpS
    have hτ := tau_mul_ppow hp h0 hpd
    have he3 : k.factorization p ≤ 3 := by
      by_contra h
      have hdiv : p ^ 4 ∣ k := (hp.pow_dvd_iff_le_factorization h0).2 (by omega)
      have : 11 ^ 4 ≤ k :=
        (Nat.pow_le_pow_left hp11 4).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdiv)
      omega
    rcases le_iff_eq_or_lt.mp he3 with heq3 | hlt3
    · have hm : k / p ^ 3 ≤ 1 := by
        have hp3 : 1331 ≤ p ^ 3 := by
          have := Nat.pow_le_pow_left hp11 3
          simpa using this
        have hdiv1 : k / p ^ 3 ≤ k / 1331 :=
          Nat.div_le_div_left hp3 (by decide : 0 < 1331)
        have hdiv2 : k / 1331 ≤ 2519 / 1331 :=
          Nat.div_le_div_right (Nat.le_of_lt_succ hk)
        omega
      have hmτ : (k / p ^ 3).divisors.card ≤ 1 :=
        (k / p ^ 3).card_divisors_le_self.trans hm
      rw [hτ, heq3]
      omega
    · rcases le_iff_eq_or_lt.mp (Nat.le_of_lt_succ hlt3) with heq2 | hlt2
      · have hmτ' : (k / p ^ 2).divisors.card ≤ 6 := by
          have hp2 : 121 ≤ p ^ 2 := by
            have := Nat.pow_le_pow_left hp11 2
            simpa using this
          have hdiv1 : k / p ^ 2 ≤ k / 121 :=
            Nat.div_le_div_left hp2 (by decide : 0 < 121)
          have hdiv2 : k / 121 ≤ 2519 / 121 :=
            Nat.div_le_div_right (Nat.le_of_lt_succ hk)
          have : k / p ^ 2 ≤ 20 := by omega
          have : k / p ^ 2 < 21 := by omega
          interval_cases k / p ^ 2 <;> decide
        rw [hτ, heq2]
        omega
      · have he1 : k.factorization p = 1 := by
          have hpos := fact_pos_of_mem hp h0 hpd
          omega
        have hm_lt : k / p < 240 := by
          have h1 : k / p ≤ k / 11 := Nat.div_le_div_left hp11 (by decide : 0 < 11)
          have h2 : k / 11 ≤ 2519 / 11 := Nat.div_le_div_right (Nat.le_of_lt_succ hk)
          omega
        have hmτ : (k / p).divisors.card ≤ 20 := tau_le_20_of_lt_240 hm_lt
        rw [hτ, he1, pow_one]
        omega
  · have hle7 := primes_le_seven_of_not_ge_eleven hex
    have hform := eq_form_of_primes_le_seven h0 hle7
    have hval : 2 ^ k.factorization 2 * 3 ^ k.factorization 3 *
        5 ^ k.factorization 5 * 7 ^ k.factorization 7 < 2520 := by rwa [← hform]
    rw [hform, tau_2a3b5c7d]
    exact tau_le_40_of_form_lt_2520 _ _ _ _ hval

lemma tau_2520 : (2520 : ℕ).divisors.card = 48 := by decide

lemma delta_eq_2520 {n : ℕ} (hn : 41 ≤ n) (h48 : n ≤ 48) : delta n = 2520 := by
  apply le_antisymm
  · exact delta_le_of_tau_ge (by have := tau_2520; omega)
  · by_contra h
    have hlt : delta n < 2520 := Nat.lt_of_le_of_ne (Nat.le_of_not_ge h) (Ne.symm (by omega))
    have hτ := tau_le_40_of_lt_2520 hlt
    have hge := le_tau_delta n
    omega

lemma hasSumNLcm_33_2520 : HasSumNLcm 33 2520 :=
  hasSumNLcm_of_dvd 33 2520 {6,7,8,9,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45,56,63,70,72,84,90,105,120,126,168,180,210,252,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_34_2520 : HasSumNLcm 34 2520 :=
  hasSumNLcm_of_dvd 34 2520 {3,6,7,8,9,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45,56,60,70,72,84,90,105,120,126,168,180,210,252,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_35_2520 : HasSumNLcm 35 2520 :=
  hasSumNLcm_of_dvd 35 2520 {3,4,5,6,7,8,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45,56,60,70,72,84,90,105,120,126,168,180,210,252,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_36_2520 : HasSumNLcm 36 2520 :=
  hasSumNLcm_of_dvd 36 2520 {3,4,5,6,7,8,9,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45,56,60,63,70,84,90,105,120,126,168,180,210,252,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_37_3360 : HasSumNLcm 37 3360 :=
  hasSumNLcm_of_dvd 37 3360 {1,3,4,5,6,7,8,12,14,15,20,21,24,28,30,32,35,40,42,48,60,70,80,84,96,105,112,120,140,160,168,210,224,240,280,336,480}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_38_3360 : HasSumNLcm 38 3360 :=
  hasSumNLcm_of_dvd 38 3360 {1,2,3,4,5,6,7,8,10,14,15,20,21,24,28,30,32,35,40,42,48,60,70,80,84,96,105,112,120,140,160,168,210,224,240,280,336,480}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_39_3360 : HasSumNLcm 39 3360 :=
  hasSumNLcm_of_dvd 39 3360 {1,2,3,4,5,6,7,8,10,12,14,15,16,20,21,24,30,32,35,40,42,48,60,70,80,84,96,105,112,120,140,160,168,210,224,240,280,336,480}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_40_3360 : HasSumNLcm 40 3360 :=
  hasSumNLcm_of_dvd 40 3360 {1,2,3,4,5,6,7,8,10,12,14,15,16,20,21,24,28,30,32,35,40,42,48,56,60,70,80,96,105,112,120,140,160,168,210,224,240,280,336,480}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_41_5040 : HasSumNLcm 41 5040 :=
  hasSumNLcm_of_dvd 41 5040 {4,10,12,14,15,18,20,21,24,28,30,35,36,40,42,48,56,60,63,70,72,80,84,90,105,112,120,126,140,144,168,180,210,240,252,280,315,336,360,420,560}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_42_5040 : HasSumNLcm 42 5040 :=
  hasSumNLcm_of_dvd 42 5040 {3,4,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45,56,60,63,70,72,80,84,90,105,112,120,126,140,144,168,180,210,240,252,280,315,336,360,420,560}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_43_5040 : HasSumNLcm 43 5040 :=
  hasSumNLcm_of_dvd 43 5040 {3,4,8,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45,48,60,63,70,72,80,84,90,105,112,120,126,140,144,168,180,210,240,252,280,315,336,360,420,560}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_44_5040 : HasSumNLcm 44 5040 :=
  hasSumNLcm_of_dvd 44 5040 {3,4,8,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45,48,56,60,63,70,72,80,84,90,105,112,120,126,140,144,168,180,210,240,252,280,315,336,360,420,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_45_5040 : HasSumNLcm 45 5040 :=
  hasSumNLcm_of_dvd 45 5040 {3,4,5,8,10,12,14,15,16,18,20,24,28,30,35,36,40,42,45,48,56,60,63,70,72,80,84,90,105,112,120,126,140,144,168,180,210,240,252,280,315,336,360,420,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_46_5040 : HasSumNLcm 46 5040 :=
  hasSumNLcm_of_dvd 46 5040 {3,4,5,8,9,10,12,14,15,16,18,20,21,24,28,35,36,40,42,45,48,56,60,63,70,72,80,84,90,105,112,120,126,140,144,168,180,210,240,252,280,315,336,360,420,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_47_5040 : HasSumNLcm 47 5040 :=
  hasSumNLcm_of_dvd 47 5040 {3,4,5,6,8,9,10,12,14,15,16,18,20,21,24,28,30,35,40,42,45,48,56,60,63,70,72,80,84,90,105,112,120,126,140,144,168,180,210,240,252,280,315,336,360,420,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_48_5040 : HasSumNLcm 48 5040 :=
  hasSumNLcm_of_dvd 48 5040 {2,3,4,5,6,7,8,10,12,14,15,16,18,20,21,24,28,30,35,40,42,45,48,56,60,63,70,72,80,84,90,105,112,120,126,140,144,168,180,210,240,252,280,315,336,360,420,504}
    (by decide) (by decide) (by decide) (by decide) (by decide)


lemma tau_le_24_of_lt_459 {k : ℕ} (hk : k < 459) : k.divisors.card ≤ 24 := by
  interval_cases k <;> decide

lemma tau_le_48_of_form_lt_5040 (a b c d : ℕ)
    (hle : 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d < 5040) :
    (a + 1) * (b + 1) * (c + 1) * (d + 1) ≤ 48 := by
  have ha : a ≤ 12 := by
    contrapose! hle
    have : 2 ^ 13 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      5040 ≤ 8192 := by decide
      _ = 2 ^ 13 := by decide
      _ ≤ 2 ^ a := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_2pow a b c d
  have hb : b ≤ 8 := by
    contrapose! hle
    have : 3 ^ 9 ≤ 3 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      5040 ≤ 19683 := by decide
      _ = 3 ^ 9 := by decide
      _ ≤ 3 ^ b := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_3pow a b c d
  have hc : c ≤ 5 := by
    contrapose! hle
    have : 5 ^ 6 ≤ 5 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      5040 ≤ 15625 := by decide
      _ = 5 ^ 6 := by decide
      _ ≤ 5 ^ c := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_5pow a b c d
  have hd : d ≤ 4 := by
    contrapose! hle
    have : 7 ^ 5 ≤ 7 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      5040 ≤ 16807 := by decide
      _ = 7 ^ 5 := by decide
      _ ≤ 7 ^ d := this
      _ ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := le_form_of_7pow a b c d
  revert hle
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> decide

lemma tau_le_48_of_lt_5040 {k : ℕ} (hk : k < 5040) : k.divisors.card ≤ 48 := by
  rcases eq_or_ne k 0 with rfl | h0
  · simp
  by_cases hex : ∃ p ∈ k.primeFactors, 11 ≤ p
  · obtain ⟨p, hpS, hp11⟩ := hex
    have hp : p.Prime := prime_of_mem_primeFactors hpS
    have hpd : p ∣ k := dvd_of_mem_primeFactors hpS
    have hτ := tau_mul_ppow hp h0 hpd
    have he3 : k.factorization p ≤ 3 := by
      by_contra h
      have hdiv : p ^ 4 ∣ k := (hp.pow_dvd_iff_le_factorization h0).2 (by omega)
      have : 11 ^ 4 ≤ k :=
        (Nat.pow_le_pow_left hp11 4).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdiv)
      omega
    rcases le_iff_eq_or_lt.mp he3 with heq3 | hlt3
    · have hm : k / p ^ 3 ≤ 3 := by
        have hp3 : 1331 ≤ p ^ 3 := by
          have := Nat.pow_le_pow_left hp11 3
          simpa using this
        have hdiv1 : k / p ^ 3 ≤ k / 1331 :=
          Nat.div_le_div_left hp3 (by decide : 0 < 1331)
        have hdiv2 : k / 1331 ≤ 5039 / 1331 :=
          Nat.div_le_div_right (Nat.le_of_lt_succ hk)
        omega
      have hmτ : (k / p ^ 3).divisors.card ≤ 3 :=
        (k / p ^ 3).card_divisors_le_self.trans hm
      rw [hτ, heq3]
      omega
    · rcases le_iff_eq_or_lt.mp (Nat.le_of_lt_succ hlt3) with heq2 | hlt2
      · have hmτ' : (k / p ^ 2).divisors.card ≤ 16 := by
          have hp2 : 121 ≤ p ^ 2 := by
            have := Nat.pow_le_pow_left hp11 2
            simpa using this
          have hdiv1 : k / p ^ 2 ≤ k / 121 :=
            Nat.div_le_div_left hp2 (by decide : 0 < 121)
          have hdiv2 : k / 121 ≤ 5039 / 121 :=
            Nat.div_le_div_right (Nat.le_of_lt_succ hk)
          have : k / p ^ 2 < 42 := by omega
          interval_cases k / p ^ 2 <;> decide
        rw [hτ, heq2]
        omega
      · have he1 : k.factorization p = 1 := by
          have hpos := fact_pos_of_mem hp h0 hpd
          omega
        have hm_lt : k / p < 459 := by
          have h1 : k / p ≤ k / 11 := Nat.div_le_div_left hp11 (by decide : 0 < 11)
          have h2 : k / 11 ≤ 5039 / 11 := Nat.div_le_div_right (Nat.le_of_lt_succ hk)
          omega
        have hmτ : (k / p).divisors.card ≤ 24 := tau_le_24_of_lt_459 hm_lt
        rw [hτ, he1, pow_one]
        omega
  · have hle7 := primes_le_seven_of_not_ge_eleven hex
    have hform := eq_form_of_primes_le_seven h0 hle7
    have hval : 2 ^ k.factorization 2 * 3 ^ k.factorization 3 *
        5 ^ k.factorization 5 * 7 ^ k.factorization 7 < 5040 := by rwa [← hform]
    rw [hform, tau_2a3b5c7d]
    exact tau_le_48_of_form_lt_5040 _ _ _ _ hval

lemma tau_5040 : (5040 : ℕ).divisors.card = 60 := by decide

lemma delta_eq_5040 {n : ℕ} (hn : 49 ≤ n) (h60 : n ≤ 60) : delta n = 5040 := by
  apply le_antisymm
  · exact delta_le_of_tau_ge (by have := tau_5040; omega)
  · by_contra h
    have hlt : delta n < 5040 := Nat.lt_of_le_of_ne (Nat.le_of_not_ge h) (Ne.symm (by omega))
    have hτ := tau_le_48_of_lt_5040 hlt
    have hge := le_tau_delta n
    omega

lemma hasSumNLcm_49_10080 : HasSumNLcm 49 10080 :=
  hasSumNLcm_of_dvd 49 10080 {9,12,16,20,21,24,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,112,120,126,140,144,160,168,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_50_10080 : HasSumNLcm 50 10080 :=
  hasSumNLcm_of_dvd 50 10080 {9,12,15,16,20,21,24,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,126,140,144,160,168,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_51_10080 : HasSumNLcm 51 10080 :=
  hasSumNLcm_of_dvd 51 10080 {6,9,12,15,16,20,21,24,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,140,144,160,168,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_52_10080 : HasSumNLcm 52 10080 :=
  hasSumNLcm_of_dvd 52 10080 {6,9,12,15,16,18,20,21,24,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,160,168,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_53_10080 : HasSumNLcm 53 10080 :=
  hasSumNLcm_of_dvd 53 10080 {6,9,10,12,14,15,16,18,20,21,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,160,168,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_54_10080 : HasSumNLcm 54 10080 :=
  hasSumNLcm_of_dvd 54 10080 {6,9,10,12,14,15,16,18,20,21,24,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,144,160,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_55_10080 : HasSumNLcm 55 10080 :=
  hasSumNLcm_of_dvd 55 10080 {6,7,8,9,10,12,14,16,18,20,21,24,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,144,160,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_56_10080 : HasSumNLcm 56 10080 :=
  hasSumNLcm_of_dvd 56 10080 {5,6,7,8,9,10,12,14,15,16,18,21,24,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,144,160,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_57_10080 : HasSumNLcm 57 10080 :=
  hasSumNLcm_of_dvd 57 10080 {4,5,6,7,8,9,10,12,14,15,16,18,20,21,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,144,160,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_58_10080 : HasSumNLcm 58 10080 :=
  hasSumNLcm_of_dvd 58 10080 {2,3,4,6,7,8,9,10,12,14,15,16,18,20,21,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,144,160,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_59_10080 : HasSumNLcm 59 10080 :=
  hasSumNLcm_of_dvd 59 10080 {1,2,3,4,5,7,8,9,10,12,14,15,16,18,20,21,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,144,160,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_60_10080 : HasSumNLcm 60 10080 :=
  hasSumNLcm_of_dvd 60 10080 {1,2,3,4,5,6,7,8,9,10,12,14,15,16,18,20,21,24,28,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96,105,112,120,126,140,144,160,180,210,224,240,252,280,288,315,336,360,420,480,504,560,672,720,840,1120}
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma hasSumNLcm_two_mul_delta {n : ℕ} (hn : 33 ≤ n) :
    HasSumNLcm n (2 * delta n) := by
  by_cases h36 : n ≤ 36
  · have hK : delta n = 1260 := delta_eq_1260 hn h36
    rw [hK]
    interval_cases n
    · exact hasSumNLcm_33_2520
    · exact hasSumNLcm_34_2520
    · exact hasSumNLcm_35_2520
    · exact hasSumNLcm_36_2520
  · by_cases h40 : n ≤ 40
    · have h37 : 37 ≤ n := by omega
      have hK : delta n = 1680 := delta_eq_1680 h37 h40
      rw [hK]
      interval_cases n
      · exact hasSumNLcm_37_3360
      · exact hasSumNLcm_38_3360
      · exact hasSumNLcm_39_3360
      · exact hasSumNLcm_40_3360
    · by_cases h48 : n ≤ 48
      · have h41 : 41 ≤ n := by omega
        have hK : delta n = 2520 := delta_eq_2520 h41 h48
        rw [hK]
        interval_cases n
        · exact hasSumNLcm_41_5040
        · exact hasSumNLcm_42_5040
        · exact hasSumNLcm_43_5040
        · exact hasSumNLcm_44_5040
        · exact hasSumNLcm_45_5040
        · exact hasSumNLcm_46_5040
        · exact hasSumNLcm_47_5040
        · exact hasSumNLcm_48_5040
      · by_cases h60 : n ≤ 60
        · have h49 : 49 ≤ n := by omega
          have hK : delta n = 5040 := delta_eq_5040 h49 h60
          rw [hK]
          interval_cases n
          · exact hasSumNLcm_49_10080
          · exact hasSumNLcm_50_10080
          · exact hasSumNLcm_51_10080
          · exact hasSumNLcm_52_10080
          · exact hasSumNLcm_53_10080
          · exact hasSumNLcm_54_10080
          · exact hasSumNLcm_55_10080
          · exact hasSumNLcm_56_10080
          · exact hasSumNLcm_57_10080
          · exact hasSumNLcm_58_10080
          · exact hasSumNLcm_59_10080
          · exact hasSumNLcm_60_10080
        · -- n ≥ 61
          sorry


lemma a_eq_a081512_zero : a 0 = a081512 0 := by rw [a_zero, a081512_zero]
lemma a_eq_a081512_one : a 1 = a081512 1 := by rw [a_one, a081512_one]
lemma a_eq_a081512_two : a 2 = a081512 2 := by rw [a_two, a081512_two]
lemma a_eq_a081512_three : a 3 = a081512 3 := by rw [a_three, a081512_three]
lemma a_eq_a081512_six : a 6 = a081512 6 := by rw [a_six, a081512_six]
lemma a_eq_a081512_seven : a 7 = a081512 7 := by rw [a_seven, a081512_seven]


lemma not_gt_of_ge_33 {n : ℕ} (hn : 33 ≤ n) : ¬ a n > a081512 n := by
  have h1 : 1 ≤ n := by omega
  have hτ : ∀ k < delta n, k.divisors.card < n := fun k hk => tau_lt_of_lt_delta hk
  have hU : HasSumNLcm n (2 * delta n) := hasSumNLcm_two_mul_delta hn
  have h2 : 2 * delta n ≤ 2 * delta n := le_rfl
  exact not_gt_of_witness_tau hU h2 hτ h1


/-
A355228 a(n) >= A081512(n) because in A081512, it is not required that m = lcm(d_1, d_2, ..., d_n).
Currently, the strict inequality happens for n = 4 and n = 5; are there other such cases?

This conjecture states that the set of natural numbers $n$ for which the strict inequality $a(n) > a_081512(n)$ holds is exactly $\{4, 5\}$.
-/
theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  constructor
  · intro hgt
    match n with
    | 0 => exact (not_lt_of_eq_seq a_eq_a081512_zero hgt).elim
    | 1 => exact (not_lt_of_eq_seq a_eq_a081512_one hgt).elim
    | 2 => exact (not_lt_of_eq_seq a_eq_a081512_two hgt).elim
    | 3 => exact (not_lt_of_eq_seq a_eq_a081512_three hgt).elim
    | 4 => simp
    | 5 => simp
    | 6 => exact (not_lt_of_eq_seq a_eq_a081512_six hgt).elim
    | 7 => exact (not_lt_of_eq_seq a_eq_a081512_seven hgt).elim
    | 8 => exact (a_eq_a081512_8 hgt).elim
    | 9 => exact (a_eq_a081512_9 hgt).elim
    | 10 => exact (a_eq_a081512_10 hgt).elim
    | 11 => exact (a_eq_a081512_11 hgt).elim
    | 12 => exact (a_eq_a081512_12 hgt).elim
    | 13 => exact (a_eq_a081512_13 hgt).elim
    | 14 => exact (a_eq_a081512_14 hgt).elim
    | 15 => exact (a_eq_a081512_15 hgt).elim
    | 16 => exact (a_eq_a081512_16 hgt).elim
    | 17 => exact (a_eq_a081512_17 hgt).elim
    | 18 => exact (a_eq_a081512_18 hgt).elim
    | 19 => exact (a_eq_a081512_19 hgt).elim
    | 20 => exact (a_eq_a081512_20 hgt).elim
    | 21 => exact (a_eq_a081512_21 hgt).elim
    | 22 => exact (a_eq_a081512_22 hgt).elim
    | 23 => exact (a_eq_a081512_23 hgt).elim
    | 24 => exact (a_eq_a081512_24 hgt).elim
    | 25 => exact (a_eq_a081512_25 hgt).elim
    | 26 => exact (a_eq_a081512_26 hgt).elim
    | 27 => exact (a_eq_a081512_27 hgt).elim
    | 28 => exact (a_eq_a081512_28 hgt).elim
    | 29 => exact (a_eq_a081512_29 hgt).elim
    | 30 => exact (a_eq_a081512_30 hgt).elim
    | 31 => exact (a_eq_a081512_31 hgt).elim
    | 32 => exact (a_eq_a081512_32 hgt).elim
    | n + 33 =>
      exact (not_gt_of_ge_33 (Nat.le_add_left 33 n) hgt).elim
  · rintro (rfl | rfl)
    · have h1 := a_four
      have h2 := a081512_four
      omega
    · have h1 := a_five
      have h2 := a081512_five
      omega
