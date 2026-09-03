import Submission.RecurrentIncrementObstruction
import Submission.PeriodicIncrementObstruction

/-! Every position in the increment word of an injective Gaussian-prime
sequence is distinguished by a finite block. This is stronger than failure
of recurrence but is not an obstruction to arbitrary finite-alphabet words. -/

namespace Erdos952Investigation
namespace UniqueIncrementBlocks
open RecurrentIncrementObstruction
set_option maxHeartbeats 0

abbrev increment (x : ℕ → GaussianInt) (n : ℕ) : GaussianInt :=
  x (n+1)-x n

lemma equal_increment_suffixes_of_le (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (a b : ℕ) (hab : a ≤ b)
    (h : ∀ i, increment x (a+i) = increment x (b+i)) : a = b := by
  by_contra hne
  have hlt : a < b := lt_of_le_of_ne hab hne
  apply prime_walk_increments_not_eventually_periodic x hx hp
  refine ⟨a,b-a,Nat.sub_pos_of_lt hlt,?_⟩
  intro n hn
  have he1 : a+(n-a) = n := by omega
  have he2 : b+(n-a) = n+(b-a) := by omega
  have hh := (h (n-a)).symm
  simpa only [he1,he2,increment] using hh

lemma equal_increment_suffixes (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (a b : ℕ)
    (h : ∀ i, increment x (a+i) = increment x (b+i)) : a = b := by
  rcases le_total a b with hab | hba
  · exact equal_increment_suffixes_of_le x hx hp a b hab h
  · exact (equal_increment_suffixes_of_le x hx hp b a hba (fun i => (h i).symm)).symm

/-- Distinct positions have different infinite increment suffixes. -/
lemma distinct_increment_suffixes (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (a b : ℕ) (hab : a ≠ b) :
    ∃ i, increment x (a+i) ≠ increment x (b+i) := by
  by_contra! he
  exact hab (equal_increment_suffixes x hx hp a b he)

/-- Every position starts a block that occurs at that position only. There
is no uniform assertion about the length of these distinguishing blocks. -/
theorem unique_increment_block (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) (a : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∀ b : ℕ,
      (∀ i < L, increment x (b+i) = increment x (a+i)) → b = a := by
  classical
  let y : ℕ → GaussianInt := fun n => x (a+n)
  have hy : Function.Injective y := by
    intro i j hij
    exact Nat.add_left_cancel (hx hij)
  have hyp (n : ℕ) : Prime (y n) := hp (a+n)
  obtain ⟨L,N,hN⟩ := exists_nonrecurrent_increment_prefix y hy hyp
  have hfinite (b : Fin (a+N)) : ∃ K : ℕ,
      (∀ i < K, increment x (b.val+i) = increment x (a+i)) → b.val = a := by
    by_cases hba : b.val = a
    · exact ⟨0,fun _ => hba⟩
    · obtain ⟨i,hi⟩ := distinct_increment_suffixes x hx hp b.val a hba
      exact ⟨i+1,fun he => False.elim (hi (he i (by omega)))⟩
  choose K hK using hfinite
  let M := (Finset.univ : Finset (Fin (a+N))).sup K
  refine ⟨max (max L M) 1,by omega,?_⟩
  intro b hb
  by_cases hsmall : b < a+N
  · apply hK ⟨b,hsmall⟩
    intro i hi
    have hKM : K ⟨b,hsmall⟩ ≤ M := Finset.le_sup (Finset.mem_univ _)
    exact hb i (by omega)
  · have hbn : N ≤ b-a := by omega
    obtain ⟨i,hi,hne⟩ := hN (b-a) hbn
    apply False.elim
    apply hne
    have hbi : a+(b-a+i) = b+i := by omega
    have hbi1 : a+(b-a+i+1) = b+i+1 := by omega
    have hai1 : a+(i+1) = a+i+1 := by omega
    simpa only [y,hbi,hbi1,hai1,increment] using hb i (by omega)

/-- The same uniqueness condition can be expressed as an injective orbit
whose individual points are isolated by finite-coordinate observations. -/
theorem finitely_distinguishable_increment_suffixes (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ∀ a, ∃ L, ∀ b, (∀ i < L, increment x (b+i) = increment x (a+i)) ↔ b = a := by
  intro a
  obtain ⟨L,_,hL⟩ := unique_increment_block x hx hp a
  refine ⟨L,fun b => ⟨hL b,?_⟩⟩
  rintro rfl i hi
  rfl

#print axioms unique_increment_block
#print axioms finitely_distinguishable_increment_suffixes

end UniqueIncrementBlocks
end Erdos952Investigation
