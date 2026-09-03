import Submission.InertPrimeCollision

/-!
A uniform obstruction to root selection using only the number of prime factors.
This does not address arbitrary positive-density sets in the conjecture.
-/

namespace Erdos1206.FactorCountObstruction
open ArithmeticFunction

/-- Every positive prime-factor-count fiber contains a strict cubic collision. -/
theorem collision_in_cardFactors_fiber (k : ℕ) (hk : 0 < k) :
    ∃ a b c d : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < d ∧
      a^3+d^3=b^3+c^3 ∧
      cardFactors a=k ∧ cardFactors b=k ∧
      cardFactors c=k ∧ cardFactors d=k := by
  obtain ⟨hp₁,hp₂,hp₃,hp₄,_,_,_,_,he,h₁,h₂,h₃,_⟩ :=
    four_inert_prime_collision
  let q := 2^(k-1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hcount {p : ℕ} (hp : p.Prime) : cardFactors (q*p)=k := by
    rw [cardFactors_mul hq.ne' hp.ne_zero,cardFactors_apply_prime hp]
    dsimp [q]
    rw [cardFactors_apply_prime_pow (by norm_num : Nat.Prime 2)]
    omega
  refine ⟨q*26711,q*31469,q*32009,q*35543,
    by positivity,Nat.mul_lt_mul_of_pos_left h₁ hq,
    Nat.mul_lt_mul_of_pos_left h₂ hq,Nat.mul_lt_mul_of_pos_left h₃ hq,
    ?_,hcount hp₁,hcount hp₂,hcount hp₃,hcount hp₄⟩
  simpa only [mul_pow,← mul_add] using congrArg (fun n : ℕ => q^3*n) he

/-- No nonzero factor-count fiber has Sidon cubes. -/
theorem cardFactors_fiber_not_sidon (k : ℕ) (hk : 0 < k) :
    ¬ IsSidon ((fun n : ℕ => n^3) '' {n | cardFactors n=k}) := by
  intro h
  obtain ⟨a,b,c,d,_,hab,hbc,_,he,ha,hb,hc,hd⟩ :=
    collision_in_cardFactors_fiber k hk
  have hh := h _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨d,hd,rfl⟩ _ ⟨c,hc,rfl⟩ he
  rcases hh with hh | hh
  · have := Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1
    omega
  · have := Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1
    omega

/-- If membership depends only on the prime-factor count and the cubes are
Sidon, the root set is contained in `{0,1}`. -/
theorem subset_zero_one_of_cardFactors_selection (A : Set ℕ)
    (hA : IsSidon ((fun n : ℕ => n^3) '' A))
    (hsel : ∀ m n : ℕ, cardFactors m=cardFactors n → (m∈A ↔ n∈A)) :
    A ⊆ {0,1} := by
  intro n hn
  have hz : cardFactors n=0 := by
    by_contra hh
    apply cardFactors_fiber_not_sidon (cardFactors n) (Nat.pos_of_ne_zero hh)
    apply Set.IsSidon.subset hA
    rintro _ ⟨m,hm,rfl⟩
    exact ⟨m,(hsel m n hm).mpr hn,rfl⟩
  simpa using cardFactors_eq_zero_iff_eq_zero_or_one.mp hz

/-- In particular, such a root set cannot be infinite. -/
theorem finite_of_cardFactors_selection (A : Set ℕ)
    (hA : IsSidon ((fun n : ℕ => n^3) '' A))
    (hsel : ∀ m n : ℕ, cardFactors m=cardFactors n → (m∈A ↔ n∈A)) :
    A.Finite :=
  (Set.toFinite ({0,1} : Set ℕ)).subset (subset_zero_one_of_cardFactors_selection A hA hsel)

/-- An arbitrary function of the prime-factor count cannot color all roots
into cube-Sidon fibers, regardless of the number of colors. -/
theorem no_cardFactors_coloring {ι : Type*} (f : ℕ → ι) :
    ¬ ∀ i, IsSidon ((fun n : ℕ => n^3) '' {n | f (cardFactors n)=i}) := by
  intro h
  apply cardFactors_fiber_not_sidon 1 (by decide)
  apply Set.IsSidon.subset (h (f 1))
  rintro _ ⟨n,hn,rfl⟩
  exact ⟨n,congrArg f hn,rfl⟩

#print axioms collision_in_cardFactors_fiber

/-- Arbitrarily many distinct prime factors can be chosen away from a fixed
positive integer. -/
lemma exists_squarefree_coprime_cardFactors (N k : ℕ) (hN : 0 < N) :
    ∃ q : ℕ, Squarefree q ∧ Nat.Coprime q N ∧ cardFactors q=k := by
  induction k with
  | zero => exact ⟨1,squarefree_one,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨q,hsq,hqN,hqk⟩ := ih
    have hq : 0 < q := Nat.pos_of_ne_zero hsq.ne_zero
    obtain ⟨p,hpbig,hp⟩ := Nat.exists_infinite_primes (q*N+1)
    have hpq : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd hq hd
      have := Nat.le_mul_of_pos_right q hN
      omega)
    have hpN : Nat.Coprime p N := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd hN hd
      have := Nat.le_mul_of_pos_left N hq
      omega)
    refine ⟨p*q,(Nat.squarefree_mul hpq).mpr ⟨hp.squarefree,hsq⟩,
      hpN.mul_left hqN,?_⟩
    rw [cardFactors_mul hp.ne_zero hq.ne',cardFactors_apply_prime hp,hqk]
    omega

/-- The same obstruction holds inside the squarefree source: every positive
factor count occurs on all four roots of one squarefree collision. -/
theorem squarefree_collision_in_cardFactors_fiber (k : ℕ) (hk : 0 < k) :
    ∃ a b c d : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < d ∧
      a^3+d^3=b^3+c^3 ∧
      Squarefree a ∧ Squarefree b ∧ Squarefree c ∧ Squarefree d ∧
      cardFactors a=k ∧ cardFactors b=k ∧
      cardFactors c=k ∧ cardFactors d=k := by
  obtain ⟨hp₁,hp₂,hp₃,hp₄,_,_,_,_,he,h₁,h₂,h₃,_⟩ :=
    four_inert_prime_collision
  obtain ⟨q,hsq,hqN,hqk⟩ := exists_squarefree_coprime_cardFactors
    (26711*31469*32009*35543) (k-1) (by norm_num)
  have hq : 0 < q := Nat.pos_of_ne_zero hsq.ne_zero
  have hsf {p : ℕ} (hp : p.Prime) (hd : p ∣ 26711*31469*32009*35543) :
      Squarefree (q*p) :=
    (Nat.squarefree_mul (hqN.of_dvd_right hd)).mpr ⟨hsq,hp.squarefree⟩
  have hcount {p : ℕ} (hp : p.Prime) : cardFactors (q*p)=k := by
    rw [cardFactors_mul hq.ne' hp.ne_zero,cardFactors_apply_prime hp,hqk]
    omega
  refine ⟨q*26711,q*31469,q*32009,q*35543,
    by positivity,Nat.mul_lt_mul_of_pos_left h₁ hq,
    Nat.mul_lt_mul_of_pos_left h₂ hq,Nat.mul_lt_mul_of_pos_left h₃ hq,
    ?_,hsf hp₁ (by norm_num),hsf hp₂ (by norm_num),
    hsf hp₃ (by norm_num),hsf hp₄ (by norm_num),
    hcount hp₁,hcount hp₂,hcount hp₃,hcount hp₄⟩
  simpa only [mul_pow,← mul_add] using congrArg (fun n : ℕ => q^3*n) he

/-- Restricting a factor-count fiber to squarefree integers still does not
make its cubes Sidon. -/
theorem squarefree_cardFactors_fiber_not_sidon (k : ℕ) (hk : 0 < k) :
    ¬ IsSidon ((fun n : ℕ => n^3) '' {n | Squarefree n ∧ cardFactors n=k}) := by
  intro h
  obtain ⟨a,b,c,d,_,hab,hbc,_,he,hsa,hsb,hsc,hsd,ha,hb,hc,hd⟩ :=
    squarefree_collision_in_cardFactors_fiber k hk
  have hh := h _ ⟨a,⟨hsa,ha⟩,rfl⟩ _ ⟨b,⟨hsb,hb⟩,rfl⟩
    _ ⟨d,⟨hsd,hd⟩,rfl⟩ _ ⟨c,⟨hsc,hc⟩,rfl⟩ he
  rcases hh with hh | hh
  · have := Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1
    omega
  · have := Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1
    omega

/-- A squarefree cube-Sidon source selected solely by its factor count is
contained in `{1}`. -/
theorem subset_one_of_squarefree_cardFactors_selection (A : Set ℕ)
    (hAsf : ∀ n∈A, Squarefree n)
    (hA : IsSidon ((fun n : ℕ => n^3) '' A))
    (hsel : ∀ m n : ℕ, Squarefree m → Squarefree n →
      cardFactors m=cardFactors n → (m∈A ↔ n∈A)) : A ⊆ {1} := by
  intro n hn
  have hz : cardFactors n=0 := by
    by_contra hh
    apply squarefree_cardFactors_fiber_not_sidon (cardFactors n)
      (Nat.pos_of_ne_zero hh)
    apply Set.IsSidon.subset hA
    rintro _ ⟨m,hm,rfl⟩
    exact ⟨m,(hsel m n hm.1 (hAsf n hn) hm.2).mpr hn,rfl⟩
  rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp hz with h | h
  · exact ((hAsf n hn).ne_zero h).elim
  · simpa using h

/-- Counting distinct prime factors instead does not repair the construction. -/
theorem cardDistinctFactors_fiber_not_sidon (k : ℕ) (hk : 0 < k) :
    ¬ IsSidon ((fun n : ℕ => n^3) '' {n | cardDistinctFactors n=k}) := by
  intro h
  apply squarefree_cardFactors_fiber_not_sidon k hk
  apply Set.IsSidon.subset h
  rintro _ ⟨n,⟨hs,hn⟩,rfl⟩
  refine ⟨n,?_,rfl⟩
  exact ((cardDistinctFactors_eq_cardFactors_iff_squarefree hs.ne_zero).mpr hs).trans hn

/-- A cube-Sidon root set selected solely by its number of distinct prime
factors is also contained in `{0,1}`. -/
theorem subset_zero_one_of_cardDistinctFactors_selection (A : Set ℕ)
    (hA : IsSidon ((fun n : ℕ => n^3) '' A))
    (hsel : ∀ m n : ℕ, cardDistinctFactors m=cardDistinctFactors n → (m∈A ↔ n∈A)) :
    A ⊆ {0,1} := by
  intro n hn
  have hz : cardDistinctFactors n=0 := by
    by_contra hh
    apply cardDistinctFactors_fiber_not_sidon (cardDistinctFactors n)
      (Nat.pos_of_ne_zero hh)
    apply Set.IsSidon.subset hA
    rintro _ ⟨m,hm,rfl⟩
    exact ⟨m,(hsel m n hm).mpr hn,rfl⟩
  have := cardDistinctFactors_eq_zero.mp hz
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  omega

#print axioms subset_zero_one_of_cardDistinctFactors_selection

#print axioms squarefree_collision_in_cardFactors_fiber
#print axioms subset_one_of_squarefree_cardFactors_selection

#print axioms finite_of_cardFactors_selection
#print axioms no_cardFactors_coloring

end Erdos1206.FactorCountObstruction
