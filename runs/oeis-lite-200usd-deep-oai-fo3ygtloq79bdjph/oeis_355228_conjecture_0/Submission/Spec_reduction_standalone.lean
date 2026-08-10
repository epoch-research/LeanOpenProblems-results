import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000


open Finset Nat Set

noncomputable def a (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m }
  sInf candidates

noncomputable def a081512 (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m }
  sInf candidates

lemma no_two_sum_divisors (m : ℕ) (hmpos : 0 < m) (D : Finset ℕ)
    (hD : D ⊆ Nat.divisors m) (hc : D.card = 2) (hs : D.sum id = m) : False := by
  rcases Finset.card_eq_two.mp hc with ⟨x,y,hxy,rfl⟩
  have hsxy : x + y = m := by
    simpa [hxy] using hs
  have hxmem : x ∈ Nat.divisors m := hD (by simp [hxy])
  have hymem : y ∈ Nat.divisors m := hD (by simp)
  have hxdvd : x ∣ m := (Nat.mem_divisors.mp hxmem).1
  have hydvd : y ∣ m := (Nat.mem_divisors.mp hymem).1
  have hxy_dvd : x ∣ y := by
    rw [← hsxy] at hxdvd
    exact (Nat.dvd_add_iff_right (dvd_refl x)).mpr hxdvd
  have hyx_dvd : y ∣ x := by
    rw [← hsxy] at hydvd
    rw [add_comm] at hydvd
    exact (Nat.dvd_add_iff_right (dvd_refl y)).mpr hydvd
  exact hxy (Nat.dvd_antisymm hxy_dvd hyx_dvd)

lemma finset_lcm_id_dvd_of_subset_divisors (m : ℕ) (D : Finset ℕ)
    (hD : D ⊆ Nat.divisors m) : D.lcm id ∣ m := by
  rw [Finset.lcm_dvd_iff]
  intro d hd
  exact (Nat.mem_divisors.mp (hD hd)).1

lemma subset_divisors_lcm_of_subset_divisors (m : ℕ) (D : Finset ℕ)
    (hD : D ⊆ Nat.divisors m) : D ⊆ Nat.divisors (D.lcm id) := by
  intro d hd
  rw [Nat.mem_divisors]
  constructor
  · exact Finset.dvd_lcm hd
  · have hdvdm : D.lcm id ∣ m := finset_lcm_id_dvd_of_subset_divisors m D hD
    intro hzero
    rw [hzero] at hdvdm
    rcases hdvdm with ⟨c, hc⟩
    have hmem : d ∈ Nat.divisors m := hD hd
    have hmne : m ≠ 0 := (Nat.mem_divisors.mp hmem).2
    omega

lemma bad_lcm_lt (m : ℕ) (hmpos : 0 < m) (D : Finset ℕ)
    (hD : D ⊆ Nat.divisors m) (hbad : D.lcm id ≠ m) : D.lcm id < m := by
  have hdvd : D.lcm id ∣ m := finset_lcm_id_dvd_of_subset_divisors m D hD
  have hle : D.lcm id ≤ m := Nat.le_of_dvd hmpos hdvd
  exact lt_of_le_of_ne hle hbad

lemma bad_lcm_sum_as_multiple (m : ℕ) (hmpos : 0 < m) (D : Finset ℕ)
    (hD : D ⊆ Nat.divisors m) (hs : D.sum id = m) (hbad : D.lcm id ≠ m) :
    D.sum id = (m / D.lcm id) * D.lcm id ∧ 2 ≤ m / D.lcm id := by
  let L := D.lcm id
  have hdvd : L ∣ m := finset_lcm_id_dvd_of_subset_divisors m D hD
  have hLpos : 0 < L := by
    apply Nat.pos_of_ne_zero
    intro hLzero
    rw [hLzero] at hdvd
    rcases hdvd with ⟨c, hc⟩
    omega
  constructor
  · rw [hs]
    exact (Nat.div_mul_cancel hdvd).symm
  · rw [Nat.two_le_iff]
    constructor
    · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hmpos hdvd) hLpos)
    · intro hquot
      have hm_eq_L : m = L := by
        calc
          m = (m / L) * L := (Nat.div_mul_cancel hdvd).symm
          _ = L := by rw [hquot, one_mul]
      exact hbad (by simpa [L] using hm_eq_L.symm)


lemma a081512_le_a_of_lcm_candidate (n : ℕ)
    (hne : ({m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m} : Set ℕ).Nonempty) :
    a081512 n ≤ a n := by
  unfold a a081512
  let A : Set ℕ := {m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m}
  let B : Set ℕ := {m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m}
  change sInf B ≤ sInf A
  have hmemA : sInf A ∈ A := Nat.sInf_mem hne
  have hmemB : sInf A ∈ B := by
    rcases hmemA with ⟨hpos, D, hD, hcard, hsum, _hlcm⟩
    exact ⟨hpos, D, hD, hcard, hsum⟩
  exact Nat.sInf_le hmemB

lemma a0815120 : a081512 0 = 0 := by
  unfold a081512
  have h : ({m : ℕ | 0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = 0 ∧ D.sum id = m} : Set ℕ) = ∅ := by
    ext m; constructor
    · intro hm
      rcases hm with ⟨hmpos,D,hD,hc,hs⟩
      have hDempty : D = ∅ := Finset.card_eq_zero.mp hc
      rw [hDempty] at hs
      simp at hs
      omega
    · intro hm; simp at hm
  rw [h]
  exact Nat.sInf_empty

lemma a0 : a 0 = 0 := by
  unfold a
  have h : ({m : ℕ | 0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = 0 ∧ D.sum id = m ∧ D.lcm id = m} : Set ℕ) = ∅ := by
    ext m; constructor
    · intro hm
      rcases hm with ⟨hmpos,D,hD,hc,hs,hl⟩
      have hDempty : D = ∅ := Finset.card_eq_zero.mp hc
      rw [hDempty] at hs
      simp at hs
      omega
    · intro hm; simp at hm
  rw [h]
  exact Nat.sInf_empty

lemma a0815121 : a081512 1 = 1 := by
  unfold a081512
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨1, by decide⟩
    · intro b hb
      by_contra h
      have hb1 : b < 1 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a1 : a 1 = 1 := by
  unfold a
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨1, by decide⟩
    · intro b hb
      by_contra h
      have hb1 : b < 1 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a0815122 : a081512 2 = 0 := by
  unfold a081512
  have h : ({m : ℕ | 0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = 2 ∧ D.sum id = m} : Set ℕ) = ∅ := by
    ext m; constructor
    · intro hm
      rcases hm with ⟨hmpos,D,hD,hc,hs⟩
      exact (no_two_sum_divisors m hmpos D hD hc hs).elim
    · intro hm; simp at hm
  rw [h]
  exact Nat.sInf_empty

lemma a2 : a 2 = 0 := by
  unfold a
  have h : ({m : ℕ | 0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = 2 ∧ D.sum id = m ∧ D.lcm id = m} : Set ℕ) = ∅ := by
    ext m; constructor
    · intro hm
      rcases hm with ⟨hmpos,D,hD,hc,hs,_hl⟩
      exact (no_two_sum_divisors m hmpos D hD hc hs).elim
    · intro hm; simp at hm
  rw [h]
  exact Nat.sInf_empty

lemma a0815123 : a081512 3 = 6 := by
  unfold a081512
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨6, by decide⟩
    · intro b hb
      by_contra h
      have hb6 : b < 6 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a3 : a 3 = 6 := by
  unfold a
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨6, by decide⟩
    · intro b hb
      by_contra h
      have hb6 : b < 6 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a0815124 : a081512 4 = 12 := by
  unfold a081512
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨12, by decide⟩
    · intro b hb
      by_contra h
      have hb12 : b < 12 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a4 : a 4 = 18 := by
  unfold a
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨18, by decide⟩
    · intro b hb
      by_contra h
      have hb18 : b < 18 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a0815125 : a081512 5 = 24 := by
  unfold a081512
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨24, by decide⟩
    · intro b hb
      by_contra h
      have hb24 : b < 24 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a0815126 : a081512 6 = 24 := by
  unfold a081512
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨24, by decide⟩
    · intro b hb
      by_contra h
      have hb24 : b < 24 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a6 : a 6 = 24 := by
  unfold a
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨24, by decide⟩
    · intro b hb
      by_contra h
      have hb24 : b < 24 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a0815127 : a081512 7 = 48 := by
  unfold a081512
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨48, by decide⟩
    · intro b hb
      by_contra h
      have hb48 : b < 48 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a7 : a 7 = 48 := by
  unfold a
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨48, by decide⟩
    · intro b hb
      by_contra h
      have hb48 : b < 48 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a0815128 : a081512 8 = 60 := by
  unfold a081512
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨60, by decide⟩
    · intro b hb
      by_contra h
      have hb60 : b < 60 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma a8 : a 8 = 60 := by
  unfold a
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨60, by decide⟩
    · intro b hb
      by_contra h
      have hb60 : b < 60 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma not_strict_six : ¬ a 6 > a081512 6 := by
  rw [a6, a0815126]
  decide

lemma not_strict_seven : ¬ a 7 > a081512 7 := by
  rw [a7, a0815127]
  decide

lemma not_strict_eight : ¬ a 8 > a081512 8 := by
  rw [a8, a0815128]
  decide

lemma a5 : a 5 = 28 := by
  unfold a
  apply le_antisymm
  · apply Nat.sInf_le; decide
  · apply le_csInf
    · exact ⟨28, by decide⟩
    · intro b hb
      by_contra h
      have hb28 : b < 28 := Nat.lt_of_not_ge h
      interval_cases b <;> revert hb <;> decide

lemma strict_four : a 4 > a081512 4 := by
  rw [a4, a0815124]
  decide

lemma strict_five : a 5 > a081512 5 := by
  rw [a5, a0815125]
  decide

lemma right_to_left (n : ℕ) (h : n = 4 ∨ n = 5) : a n > a081512 n := by
  rcases h with rfl | rfl
  · exact strict_four
  · exact strict_five

lemma not_strict_small (n : ℕ) (h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) : ¬ a n > a081512 n := by
  rcases h with rfl | rfl | rfl | rfl
  · rw [a0, a0815120]; decide
  · rw [a1, a0815121]; decide
  · rw [a2, a0815122]; decide
  · rw [a3, a0815123]; decide

/--
If the eventual case `n > 8` is ruled out, the existing finite computations in
this file close the submitted theorem.  The hypothesis below is the isolated
remaining mathematical lemma.
-/
theorem oeis_355228_conjecture_0_of_no_strict_above_eight
    (no_strict_above_eight : ∀ n : ℕ, 8 < n → ¬ a n > a081512 n) (n : ℕ) :
    (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  constructor
  · intro hstrict
    by_cases hn8 : n ≤ 8
    · interval_cases n
      · exfalso; exact (not_strict_small 0 (Or.inl rfl)) hstrict
      · exfalso; exact (not_strict_small 1 (Or.inr (Or.inl rfl))) hstrict
      · exfalso; exact (not_strict_small 2 (Or.inr (Or.inr (Or.inl rfl)))) hstrict
      · exfalso; exact (not_strict_small 3 (Or.inr (Or.inr (Or.inr rfl)))) hstrict
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exfalso; exact not_strict_six hstrict
      · exfalso; exact not_strict_seven hstrict
      · exfalso; exact not_strict_eight hstrict
    · have hn8lt : 8 < n := Nat.lt_of_not_ge hn8
      exfalso
      exact no_strict_above_eight n hn8lt hstrict
  · intro h
    exact right_to_left n h

/-- Single missing lemma, in the exact form that completes `Submission/Spec.lean`
when combined with the verified finite computations above. -/
def MissingLemma_no_strict_above_eight : Prop :=
  ∀ n : ℕ, 8 < n → ¬ a n > a081512 n
