import FormalConjectures.Util.ProblemImports

open Nat Finset

def totient_range_acc (n : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, L, R, acc =>
    if L > R then acc
    else if L = R then
      if L.Coprime n then acc + 1 else acc
    else
      let mid := (L + R) / 2
      let acc' := totient_range_acc n fuel L mid acc
      totient_range_acc n fuel (mid + 1) R acc'

lemma Ico_split {L mid R : ℕ} (h1 : L ≤ mid) (h2 : mid < R) :
    Ico L R = Ico L (mid + 1) ∪ Ico (mid + 1) R := by
  ext x
  simp only [mem_Ico, mem_union]
  omega

lemma card_filter_union_disjoint {α : Type _} [DecidableEq α] (s1 s2 : Finset α) (p : α → Prop) [DecidablePred p]
    (h : Disjoint s1 s2) :
    (filter p (s1 ∪ s2)).card = (filter p s1).card + (filter p s2).card := by
  rw [filter_union, card_union_of_disjoint (h.filter_left _).filter_right]

lemma totient_range_acc_eq (n : Nat) (fuel : Nat) : ∀ L R acc, L ≤ R → R - L < 2 ^ fuel →
    totient_range_acc n fuel L R acc = acc + ((Ico L (R + 1)).filter (·.Coprime n)).card := by
  induction fuel with
  | zero =>
    intro L R acc h_le h_lt
    simp only [Nat.pow_zero] at h_lt
    omega
  | succ fuel ih =>
    intro L R acc h_le h_lt
    dsimp [totient_range_acc]
    by_cases h_eq : L = R
    · rw [if_neg (by omega), if_pos h_eq]
      rw [h_eq]
      simp only [show R - R = 0 by omega, Nat.pow_succ] at h_lt
      have h_range : Ico R (R + 1) = {R} := by
        ext x
        simp only [mem_Ico, mem_singleton]
        omega
      rw [h_range, filter_singleton]
      by_cases h_cop : R.Coprime n
      · rw [if_pos h_cop, if_pos h_cop]
        simp
      · rw [if_neg h_cop, if_neg h_cop]
        simp
    · have h_lt_R : L < R := by omega
      rw [if_neg (by omega), if_neg h_eq]
      let mid := (L + R) / 2
      have h_mid_ge : L ≤ mid := by omega
      have h_mid_lt : mid < R := by omega
      have h_lt_left : mid - L < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := by ring
        omega
      have h_lt_right : R - (mid + 1) < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := by ring
        omega
      rw [ih L mid acc h_mid_ge h_lt_left]
      rw [ih (mid + 1) R (acc + ((Ico L (mid + 1)).filter (·.Coprime n)).card) (by omega) h_lt_right]
      have h_split : Ico L (R + 1) = Ico L (mid + 1) ∪ Ico (mid + 1) (R + 1) := by
        apply Ico_split h_mid_ge (by omega)
      rw [h_split]
      rw [card_filter_union_disjoint]
      · ring
      · rw [disjoint_iff_ne]
        intro x hx y hy hxy
        simp only [mem_Ico] at hx hy
        omega

