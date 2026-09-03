import FormalConjecturesUtil

/-!
# A finite prime-removal necessary condition

If `(x, x + H]` contains no squarefree integer, multiplication by a prime `p`
bijects the squarefree integers in `(x / p, (x + H) / p]` with the integers
`p² * a` in the original interval for which `a` is squarefree and `p ∤ a`.
These defect sets are disjoint for distinct primes, giving a finite packing
bound. Without the gap hypothesis, an additional term counts squarefree
multiples of `p`. These are necessary conditions only, not a solution of a gap conjecture.
-/

namespace PrimeRemoval

open Finset

/-- Squarefree integers in the interval obtained by dividing the endpoints by `p`. -/
noncomputable def child (x H p : ℕ) : Finset ℕ := by
  classical
  exact (Ioc (x / p) ((x + H) / p)).filter Squarefree

/-- For prime `p`, interval members whose only repeated prime is `p`, of exponent two. -/
noncomputable def defect (x H p : ℕ) : Finset ℕ := by
  classical
  exact (Ioc x (x + H)).filter
    (fun n => ∃ a : ℕ, n = p ^ 2 * a ∧ Squarefree a ∧ ¬ p ∣ a)

/-- The quotient endpoints correspond exactly to membership after multiplication. -/
theorem mem_child_iff {x H p m : ℕ} (hp : 0 < p) :
    m ∈ child x H p ↔ p * m ∈ Ioc x (x + H) ∧ Squarefree m := by
  classical
  simp only [child, mem_filter, mem_Ioc, Nat.div_lt_iff_lt_mul hp,
    Nat.le_div_iff_mul_le hp, Nat.mul_comm m p]

/-- The divisible children are precisely those whose images are defects, without a gap assumption. -/
theorem mul_mem_defect_iff {x H p m : ℕ} (hp : p.Prime) :
    p * m ∈ defect x H p ↔ m ∈ child x H p ∧ p ∣ m := by
  classical
  rw [mem_child_iff hp.pos]
  constructor
  · rintro hn
    obtain ⟨hi, a, heq, ha, hpa⟩ := mem_filter.mp hn
    have hm : m = p * a := Nat.eq_of_mul_eq_mul_left hp.pos
      (by simpa only [pow_two, mul_assoc] using heq)
    refine ⟨⟨hi, ?_⟩, ?_⟩
    · rw [hm]
      exact Nat.squarefree_mul_iff.mpr
        ⟨hp.coprime_iff_not_dvd.mpr hpa, (Nat.prime_iff.mp hp).squarefree, ha⟩
    · exact ⟨a, hm⟩
  · rintro ⟨⟨hi, hm⟩, a, rfl⟩
    exact mem_filter.mpr ⟨hi, a, by simp only [pow_two, mul_assoc],
      hm.of_mul_right, hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hm)⟩

/-- In a squarefree-free interval every child must contain the removed prime. -/
theorem prime_dvd_of_mem_child {x H p m : ℕ} (hp : p.Prime)
    (hgap : ∀ n ∈ Ioc x (x + H), ¬ Squarefree n) (hm : m ∈ child x H p) :
    p ∣ m := by
  obtain ⟨hi, hs⟩ := (mem_child_iff hp.pos).mp hm
  by_contra hpm
  exact hgap (p * m) hi (Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hpm, (Nat.prime_iff.mp hp).squarefree, hs⟩)

/-- Under the gap hypothesis, multiplication by `p` bijects children onto defects. -/
theorem mul_bijOn_child_defect {x H p : ℕ} (hp : p.Prime)
    (hgap : ∀ n ∈ Ioc x (x + H), ¬ Squarefree n) :
    Set.BijOn (fun m : ℕ => p * m) (child x H p) (defect x H p) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    exact (mul_mem_defect_iff hp).mpr ⟨hm, prime_dvd_of_mem_child hp hgap hm⟩
  · intro m _ k _ heq
    exact Nat.eq_of_mul_eq_mul_left hp.pos heq
  · intro n hn
    change n ∈ defect x H p at hn
    obtain ⟨_, a, rfl, _, _⟩ := mem_filter.mp hn
    have hm : p * (p * a) ∈ defect x H p := by
      simpa only [pow_two, mul_assoc] using hn
    exact ⟨p * a, ((mul_mem_defect_iff hp).mp hm).1,
      by simp only [pow_two, mul_assoc]⟩

/-- The prime-removal cardinality equality in a squarefree-free interval. -/
theorem card_child_eq_card_defect {x H p : ℕ} (hp : p.Prime)
    (hgap : ∀ n ∈ Ioc x (x + H), ¬ Squarefree n) :
    (child x H p).card = (defect x H p).card := by
  have h := mul_bijOn_child_defect hp hgap
  exact card_nbij _ h.mapsTo h.injOn h.surjOn

/-- Defects belonging to distinct primes are disjoint, even without a gap assumption. -/
theorem defect_disjoint {x H p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Disjoint (defect x H p) (defect x H q) := by
  classical
  apply disjoint_left.mpr
  intro n hnp hnq
  obtain ⟨_, a, hna, _, _⟩ := mem_filter.mp hnp
  obtain ⟨_, b, hnb, hb, _⟩ := mem_filter.mp hnq
  have hd : p ^ 2 ∣ q ^ 2 * b := by
    rw [← hnb, hna]
    exact dvd_mul_right _ _
  have hpb : p ^ 2 ∣ b :=
    (Nat.coprime_pow_primes 2 2 hp hq hpq).dvd_of_dvd_mul_left hd
  exact Nat.squarefree_iff_prime_squarefree.mp hb p hp (by simpa only [pow_two] using hpb)

/-- An unconditional finite packing bound for defects. -/
theorem sum_card_defect_le (x H : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, (defect x H p).card ≤ H := by
  classical
  have hd : (P : Set ℕ).PairwiseDisjoint (defect x H) := by
    intro p hp q hq hpq
    exact defect_disjoint (hP p hp) (hP q hq) hpq
  calc
    ∑ p ∈ P, (defect x H p).card = (P.biUnion (defect x H)).card :=
      (card_biUnion hd).symm
    _ ≤ (Ioc x (x + H)).card := card_le_card (by
      intro n hn
      obtain ⟨p, _, hp⟩ := mem_biUnion.mp hn
      exact (mem_filter.mp hp).1)
    _ = H := by simp

/-- A finite necessary condition for a squarefree-free interval, for any finite prime set. -/
theorem sum_card_child_le {x H : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hgap : ∀ n ∈ Ioc x (x + H), ¬ Squarefree n) :
    ∑ p ∈ P, (child x H p).card ≤ H := by
  calc
    ∑ p ∈ P, (child x H p).card = ∑ p ∈ P, (defect x H p).card :=
      sum_congr rfl (fun p hp => card_child_eq_card_defect (hP p hp) hgap)
    _ ≤ H := sum_card_defect_le x H P hP

open scoped Classical in
/-- Without a gap assumption, children split into squarefree multiples and defects. -/
theorem card_child_eq_card_squarefree_multiples_add_card_defect {x H p : ℕ} (hp : p.Prime) :
    (child x H p).card =
      ((Ioc x (x + H)).filter (fun n => Squarefree n ∧ p ∣ n)).card +
        (defect x H p).card := by
  classical
  have hgood : ((child x H p).filter (fun m => ¬ p ∣ m)).card =
      ((Ioc x (x + H)).filter (fun n => Squarefree n ∧ p ∣ n)).card := by
    refine card_bij (fun m _ => p * m) ?_
      (fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_left hp.pos heq) ?_
    · intro m hm
      obtain ⟨hm, hpm⟩ := mem_filter.mp hm
      obtain ⟨hi, hs⟩ := (mem_child_iff hp.pos).mp hm
      exact mem_filter.mpr ⟨hi, Nat.squarefree_mul_iff.mpr
        ⟨hp.coprime_iff_not_dvd.mpr hpm, (Nat.prime_iff.mp hp).squarefree, hs⟩,
        dvd_mul_right p m⟩
    · intro n hn
      obtain ⟨hi, hs, m, rfl⟩ := mem_filter.mp hn
      exact ⟨m, mem_filter.mpr ⟨(mem_child_iff hp.pos).mpr ⟨hi, hs.of_mul_right⟩,
        hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)⟩, rfl⟩
  have hbad : ((child x H p).filter (fun m => p ∣ m)).card =
      (defect x H p).card := by
    refine card_bij (fun m _ => p * m) ?_
      (fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_left hp.pos heq) ?_
    · intro m hm
      exact (mul_mem_defect_iff hp).mpr (mem_filter.mp hm)
    · intro n hn
      obtain ⟨_, a, rfl, _, _⟩ := mem_filter.mp hn
      have hm : p * (p * a) ∈ defect x H p := by
        simpa only [pow_two, mul_assoc] using hn
      exact ⟨p * a, mem_filter.mpr ((mul_mem_defect_iff hp).mp hm),
        by simp only [pow_two, mul_assoc]⟩
  rw [← hgood, ← hbad, Nat.add_comm]
  exact (card_filter_add_card_filter_not (fun m => p ∣ m)).symm

#print axioms mul_bijOn_child_defect
#print axioms card_child_eq_card_defect
#print axioms defect_disjoint
#print axioms sum_card_defect_le
#print axioms sum_card_child_le
#print axioms card_child_eq_card_squarefree_multiples_add_card_defect

end PrimeRemoval
