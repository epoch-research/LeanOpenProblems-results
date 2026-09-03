import Submission.ResidueBalancedError
import Submission.IntervalRescaling

/-! Exact residue-class moments for hits at different offsets, retaining the
shared-modulus improvement for a difference of two assignments. -/
namespace Erdos970.AdjacentShift
open Finset BrunCriterion

noncomputable def hit (p r b j : ℕ) : ℝ := if j+b ≡ r [MOD p] then 1 else 0
noncomputable def count (m p r b : ℕ) : ℝ := ∑ j ∈ range m, hit p r b j
noncomputable def pairCount (m p q r s a b : ℕ) : ℝ :=
  ∑ j ∈ range m, hit p r a j * hit q s b j

lemma hit_eq_residue (p r b : ℕ) (hp : 0 < p) :
    ∃ a : ℕ, ∀ j, hit p r b j = if j ≡ a [MOD p] then 1 else 0 := by
  obtain ⟨a, ha⟩ := IntervalRescaling.exists_affine_residue b 1 p r hp (by simp)
  refine ⟨a, fun j => ?_⟩
  have hh : j+b ≡ r [MOD p] ↔ j ≡ a [MOD p] := by simpa [add_comm] using ha j
  simp only [hit, hh]

lemma count_error (m p r b : ℕ) (hp : 0 < p) :
    |count m p r b - (m : ℝ)/p| ≤ 1 := by
  classical
  obtain ⟨a, ha⟩ := hit_eq_residue p r b hp
  simp_rw [count, ha]
  rw [sum_boole]
  exact residue_count_error m p a hp

lemma pairCount_eq_intersection (m p q r s a b : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) :
    ∃ z : ℕ → ℕ, pairCount m p q r s a b =
      (((range m).filter (fun j => ∀ t ∈ ({p,q} : Finset ℕ), j ≡ z t [MOD t])).card : ℝ) := by
  classical
  obtain ⟨x, hx⟩ := hit_eq_residue p r a hp
  obtain ⟨y, hy⟩ := hit_eq_residue q s b hq
  refine ⟨fun t => if t = p then x else y, ?_⟩
  have hh (j : ℕ) : hit p r a j * hit q s b j =
      if ∀ t ∈ ({p,q} : Finset ℕ), j ≡ (if t = p then x else y) [MOD t] then (1 : ℝ) else 0 := by
    rw [hx, hy]
    simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      if_pos rfl, if_neg (Ne.symm hpq)]
    split_ifs <;> simp_all
  simp_rw [pairCount, hh]
  rw [sum_boole]

lemma pairCount_error (m p q r s a b : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    |pairCount m p q r s a b - (m : ℝ)/((p : ℝ)*q)| ≤ 1 := by
  classical
  obtain ⟨z, hz⟩ := pairCount_eq_intersection m p q r s a b hp.pos hq.pos hpq
  rw [hz]
  have hP : ∀ t ∈ ({p,q} : Finset ℕ), t.Prime := by simp [hp,hq]
  have he := intersection_count_error {p,q} hP z m
  simpa [hpq] using he

lemma pairCount_difference_error (m p q r s a b c d : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    |pairCount m p q r s a b - pairCount m p q r s c d| ≤ 1 := by
  classical
  obtain ⟨z, hz⟩ := pairCount_eq_intersection m p q r s a b hp.pos hq.pos hpq
  obtain ⟨w, hw⟩ := pairCount_eq_intersection m p q r s c d hp.pos hq.pos hpq
  rw [hz, hw]
  exact intersection_count_pair_error {p,q} (by simp [hp,hq]) z w m

#print axioms count_error
#print axioms pairCount_error
#print axioms pairCount_difference_error
end Erdos970.AdjacentShift
