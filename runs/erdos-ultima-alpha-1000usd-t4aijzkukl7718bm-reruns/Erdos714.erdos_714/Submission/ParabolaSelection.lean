import Submission.UnbalancedParabolas

/-! The unbalanced parabola family cannot be balanced just by selecting
vertices (even with additional arbitrary edge deletions). Its pairwise
intersection bound forces an O(N^(3/2)) edge bound in every such selection. -/

set_option maxHeartbeats 3000000
noncomputable section
open Classical Finset SimpleGraph
namespace Erdos714PairSelection
variable {A B : Type*} [Fintype A] [Fintype B]

/-- A one-sided bounded pair-intersection hypothesis suffices for a total-order
KST bound, with no balance or regularity assumptions. -/
theorem edge_square_bound (S : A → Finset B) (c : ℕ)
    (hc : ∀ a a', a ≠ a' → (S a ∩ S a').card ≤ c) :
    (Erdos714Packing.incidence S).edgeFinset.card^2 ≤
      (c+1)*(Fintype.card A+Fintype.card B)^3 := by
  let D (b : B) := (univ.filter (fun a => b ∈ S a)).card
  let E := ∑ a, (S a).card
  have hE : ∑ b, D b=E := by
    dsimp [D,E]
    simp_rw [card_filter]
    rw [sum_comm]
    simp
  have hb (b : B) : D b^2 = ∑ a : A, ∑ a' : A,
      if b ∈ S a ∧ b ∈ S a' then 1 else 0 := by
    dsimp [D]
    rw [card_filter,pow_two,sum_mul]
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro a' _
    by_cases h : b ∈ S a <;> by_cases h' : b ∈ S a' <;> simp [h,h']
  have hm : ∑ b, D b^2 = ∑ a : A, ∑ a' : A, (S a ∩ S a').card := by
    simp_rw [hb]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [sum_comm]
    apply sum_congr rfl
    intro a' _
    simp only [←mem_inter]
    simp only [sum_boole,Nat.cast_id]
    congr 1
    ext b
    simp
  have hlocal (a a' : A) : (S a ∩ S a').card ≤ (if a=a' then (S a).card else 0)+c := by
    by_cases h : a=a'
    · subst a'; simp
    · simpa [h] using hc a a' h
  have hm_bound : ∑ b, D b^2 ≤ E+c*(Fintype.card A)^2 := by
    rw [hm]
    calc
      _ ≤ ∑ a : A, ∑ a' : A, ((if a=a' then (S a).card else 0)+c) :=
        sum_le_sum (fun a _ => sum_le_sum (fun a' _ => hlocal a a'))
      _ = _ := by simp [sum_add_distrib,E]; ring
  have hcs : E^2 ≤ Fintype.card B * ∑ b, D b^2 := by
    have hh := sum_mul_sq_le_sq_mul_sq (univ : Finset B) (fun _ => (1:ℕ)) D
    simpa only [one_mul,one_pow,sum_const,card_univ,smul_eq_mul,mul_one,hE] using hh
  have hemax : E ≤ Fintype.card A*Fintype.card B := by
    calc
      E ≤ ∑ _a : A, Fintype.card B := sum_le_sum (fun a _ => card_le_univ (S a))
      _ = _ := by simp
  let N := Fintype.card A+Fintype.card B
  have hA : Fintype.card A ≤ N := Nat.le_add_right _ _
  have hB : Fintype.card B ≤ N := Nat.le_add_left _ _
  have heN : E ≤ N^2 := by
    exact hemax.trans (by simpa [pow_two] using Nat.mul_le_mul hA hB)
  have hAN : (Fintype.card A)^2 ≤ N^2 := Nat.pow_le_pow_left hA 2
  have hsum : E+c*(Fintype.card A)^2 ≤ (c+1)*N^2 := by
    have hh := Nat.add_le_add heN (Nat.mul_le_mul_left c hAN)
    convert hh using 1; ring
  rw [Erdos714Packing.incidence_edges]
  change E^2 ≤ (c+1)*N^3
  calc
    E^2 ≤ Fintype.card B * (E+c*(Fintype.card A)^2) :=
      hcs.trans (Nat.mul_le_mul_left _ hm_bound)
    _ ≤ N*((c+1)*N^2) := Nat.mul_le_mul hB hsum
    _ = _ := by ring

end Erdos714PairSelection

namespace Erdos714Parabolas
variable {F A B : Type*} [Field F] [Fintype F] [Fintype A] [Fintype B]

/-- Arbitrary injective vertex selections and arbitrary retained cross edges.
The bound is independent of q and does not assume that all possible selected
incidences are kept. -/
theorem selected_edge_square_bound (a : A ↪ FullRow F) (b : B ↪ F × F)
    (S : A → Finset B) (hS : ∀ i j, j ∈ S i → b j ∈ fullPoints (a i)) :
    (Erdos714Packing.incidence S).edgeFinset.card^2 ≤
      5*(Fintype.card A+Fintype.card B)^3 := by
  apply Erdos714PairSelection.edge_square_bound S 4
  intro i i' hii'
  apply le_trans _ (pair_intersection_bound (a i) (a i') (a.injective.ne hii'))
  apply card_le_card_of_injOn b
  · intro j hj
    exact mem_inter.mpr ⟨hS i j (mem_inter.mp hj).1,hS i' j (mem_inter.mp hj).2⟩
  · exact b.injective.injOn


/-- At the conjectured fourth-case scale, every such selected construction
has a bounded scale parameter. In particular it cannot work along an
unbounded sequence with fixed constants C and D. -/
theorem selected_critical_scale_bound (a : A ↪ FullRow F) (b : B ↪ F × F)
    (S : A → Finset B) (hS : ∀ i j, j ∈ S i → b j ∈ fullPoints (a i))
    (q C D : ℕ) (hq : 0 < q)
    (hsize : Fintype.card A+Fintype.card B ≤ D*q^4)
    (hedges : q^7 ≤ C*(Erdos714Packing.incidence S).edgeFinset.card) :
    q^2 ≤ 5*C^2*D^3 := by
  have he := selected_edge_square_bound a b S hS
  have hs := Nat.pow_le_pow_left hsize 3
  have he' := he.trans (Nat.mul_le_mul_left 5 hs)
  have hl := Nat.pow_le_pow_left hedges 2
  rw [mul_pow] at hl
  have ht := hl.trans (Nat.mul_le_mul_left (C^2) he')
  apply Nat.le_of_mul_le_mul_right (c := q^12) _ (pow_pos hq _)
  convert ht using 1 <;> ring

end Erdos714Parabolas
#print axioms Erdos714PairSelection.edge_square_bound
#print axioms Erdos714Parabolas.selected_edge_square_bound

#print axioms Erdos714Parabolas.selected_critical_scale_bound
