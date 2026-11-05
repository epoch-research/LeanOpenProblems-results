import Mathlib

/-! Finite greedy residue selection and allocation of one prime per leftover point. -/

open scoped BigOperators

namespace Erdos5EfficientCover

/-- The points in `S` not in any chosen class at the moduli in `F`. -/
noncomputable def uncovered (S F : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun n => ∀ p ∈ F, n % p ≠ a p)

@[simp] theorem mem_uncovered {S F : Finset ℕ} {a : ℕ → ℕ} {n : ℕ} :
    n ∈ uncovered S F a ↔ n ∈ S ∧ ∀ p ∈ F, n % p ≠ a p := by
  classical
  simp [uncovered]

/-- A residue class contains at least the average number of points. -/
theorem exists_large_residue (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ r < p, (S.card : ℝ) / p ≤ ((S.filter (fun n => n % p = r)).card : ℝ) := by
  classical
  have hpartition : S.card = ∑ r ∈ Finset.range p, (S.filter (fun n => n % p = r)).card :=
    Finset.card_eq_sum_card_fiberwise (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hp))
  have hsum : (∑ r ∈ Finset.range p, (S.card : ℝ) / p) ≤
      ∑ r ∈ Finset.range p, ((S.filter (fun n => n % p = r)).card : ℝ) := by
    rw [← Nat.cast_sum, ← hpartition]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    rw [mul_div_cancel₀ _ hp']
  obtain ⟨r, hr, hbound⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hp.ne') hsum
  exact ⟨r, Finset.mem_range.mp hr, hbound⟩

/-- Deleting a largest residue class leaves at most a `(1-1/p)` fraction. -/
theorem exists_residue_deletion (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ r < p, ((S.filter (fun n => n % p ≠ r)).card : ℝ) ≤
      (1 - 1 / (p : ℝ)) * S.card := by
  classical
  obtain ⟨r, hr, hlarge⟩ := exists_large_residue S p hp
  refine ⟨r, hr, ?_⟩
  have hpartition := Finset.card_filter_add_card_filter_not (s := S) (fun n => n % p = r)
  have hpart : ((S.filter (fun n => n % p = r)).card : ℝ) +
      ((S.filter (fun n => n % p ≠ r)).card : ℝ) = S.card := by
    exact_mod_cast hpartition
  have hid : (1 - 1 / (p : ℝ)) * S.card = S.card - (S.card : ℝ) / p := by ring
  rw [hid]
  linarith

/-- Successive greedy choices multiply the surviving cardinality by the local densities. -/
theorem greedy_residue_cover (S F : Finset ℕ) (hp : ∀ p ∈ F, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ F, a p < p) ∧
      ((uncovered S F a).card : ℝ) ≤
        (∏ p ∈ F, (1 - 1 / (p : ℝ))) * S.card := by
  classical
  induction F using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨fun _ => 0, by simp, ?_⟩
      simp [uncovered]
  | @insert p F hpF ih =>
      have hp0 := hp p (Finset.mem_insert_self p F)
      have hF : ∀ q ∈ F, 0 < q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
      obtain ⟨r, hr, hdelete⟩ := exists_residue_deletion S p hp0
      let S' := S.filter (fun n => n % p ≠ r)
      obtain ⟨a, ha, hcard⟩ := ih S' hF
      let b := Function.update a p r
      refine ⟨b, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · simpa [b] using hr
        · have hqp : q ≠ p := fun h => hpF (h ▸ hq)
          simpa [b, Function.update_of_ne hqp] using ha q hq
      · have heq : uncovered S (insert p F) b = uncovered S' F a := by
          ext n
          simp only [mem_uncovered, S', Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
          simp only [b, Function.update_self]
          constructor
          · rintro ⟨hn, hp', hrest⟩
            refine ⟨⟨hn, hp'⟩, ?_⟩
            intro q hq
            have hqp : q ≠ p := fun h => hpF (h ▸ hq)
            simpa [Function.update_of_ne hqp] using hrest q hq
          · rintro ⟨⟨hn, hp'⟩, hrest⟩
            refine ⟨hn, hp', ?_⟩
            intro q hq
            have hqp : q ≠ p := fun h => hpF (h ▸ hq)
            simpa [Function.update_of_ne hqp] using hrest q hq
        have hnonneg : 0 ≤ ∏ q ∈ F, (1 - 1 / (q : ℝ)) := by
          apply Finset.prod_nonneg
          intro q hq
          have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hF q hq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast hF q hq
          exact sub_nonneg.mpr ((div_le_one hq0).mpr hq1)
        rw [heq, Finset.prod_insert hpF]
        calc
          ((uncovered S' F a).card : ℝ) ≤ (∏ q ∈ F, (1 - 1 / (q : ℝ))) * S'.card := hcard
          _ ≤ (∏ q ∈ F, (1 - 1 / (q : ℝ))) *
              ((1 - 1 / (p : ℝ)) * S.card) :=
            mul_le_mul_of_nonneg_left hdelete hnonneg
          _ = _ := by ring

/-- A supply of distinct positive moduli can cover one arbitrary point per modulus. -/
theorem allocate_reserve (S F : Finset ℕ) (hp : ∀ p ∈ F, 0 < p) (hcard : S.card ≤ F.card) :
    ∃ a : ℕ → ℕ, (∀ p ∈ F, a p < p) ∧
      ∀ s ∈ S, ∃ p ∈ F, s % p = a p := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
      refine ⟨fun _ => 0, hp, ?_⟩
      simp
  | @insert s S hsS ih =>
      have hF : F.Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_insert_of_notMem hsS] at hcard
        omega)
      obtain ⟨p, hpF⟩ := hF
      have hcard' : S.card ≤ (F.erase p).card := by
        have herase := Finset.card_erase_add_one hpF
        rw [Finset.card_insert_of_notMem hsS] at hcard
        omega
      obtain ⟨a, ha, hcover⟩ := ih (F.erase p)
        (fun q hq => hp q (Finset.mem_of_mem_erase hq)) hcard'
      let b := Function.update a p (s % p)
      refine ⟨b, ?_, ?_⟩
      · intro q hq
        by_cases hqp : q = p
        · subst q
          simpa [b] using Nat.mod_lt s (hp p hpF)
        · simpa [b, Function.update_of_ne hqp] using
            ha q (Finset.mem_erase.mpr ⟨hqp, hq⟩)
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact ⟨p, hpF, by simp [b]⟩
        · obtain ⟨q, hq, hqeq⟩ := hcover t ht
          refine ⟨q, Finset.mem_of_mem_erase hq, ?_⟩
          simpa [b, Function.update_of_ne (Finset.mem_erase.mp hq).1] using hqeq

end Erdos5EfficientCover

#print axioms Erdos5EfficientCover.greedy_residue_cover
#print axioms Erdos5EfficientCover.allocate_reserve
