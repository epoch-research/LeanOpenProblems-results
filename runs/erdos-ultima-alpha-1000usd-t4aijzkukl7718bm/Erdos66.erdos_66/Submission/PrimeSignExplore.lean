import FormalConjecturesUtil

/-! Prescribing finitely many quadratic-character values at arbitrarily large
primes. Auxiliary work toward a finite cyclic construction, not Erdős 66 itself. -/
namespace Erdos66PrimeSign

/-- Dirichlet's theorem with simultaneous pairwise-coprime congruences. -/
lemma exists_prime_congruences {ι : Type*} (S : Finset ι) (a m : ι → ℕ)
    (hm : ∀ i ∈ S, m i ≠ 0)
    (hp : (S : Set ι).Pairwise (Function.onFun Nat.Coprime m))
    (ha : ∀ i ∈ S, (a i).Coprime (m i)) (N : ℕ) :
    ∃ p > N, p.Prime ∧ ∀ i ∈ S, Nat.ModEq (m i) p (a i) := by
  classical
  let c := Nat.chineseRemainderOfFinset a m S hm hp
  have hc : c.val.Coprime (∏ i ∈ S, m i) := by
    apply Nat.Coprime.prod_right
    intro i hi
    rw [Nat.coprime_iff_gcd_eq_one, (c.property i hi).gcd_eq]
    exact (ha i hi).gcd_eq_one
  have hM : (∏ i ∈ S, m i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hm
  obtain ⟨p, hpN, hprime, hpc⟩ := Nat.forall_exists_prime_gt_and_modEq N hM hc
  refine ⟨p, hpN, hprime, ?_⟩
  intro i hi
  exact (hpc.of_dvd (Finset.dvd_prod_of_mem m hi)).trans (c.property i hi)

lemma exists_legendre_residue (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ r : ℕ, r.Coprime q ∧ @legendreSym q ⟨hq⟩ (r : ℤ) = ε := by
  letI : Fact q.Prime := ⟨hq⟩
  rcases hε with rfl | rfl
  · exact ⟨1, Nat.coprime_one_left q, by simp [legendreSym]⟩
  · obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one
      (F := ZMod q) (by simpa only [ZMod.ringChar_zmod_n] using hq2)
    have ha0 : a ≠ 0 := by
      intro h
      simp only [h, map_zero] at ha
      norm_num at ha
    refine ⟨a.val, ?_, ?_⟩
    · apply (ZMod.isUnit_iff_coprime a.val q).mp
      rw [ZMod.natCast_zmod_val]
      exact isUnit_iff_ne_zero.mpr ha0
    · simpa only [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val] using ha

/-- Any signs at finitely many odd primes can simultaneously occur as
Legendre symbols for arbitrarily large primes `p ≡ 1 (mod 8)`. -/
theorem exists_prime_legendre_signs (S : Finset ℕ)
    (hprime : ∀ q ∈ S, q.Prime) (hodd : ∀ q ∈ S, q ≠ 2)
    (ε : ℕ → ℤ) (hε : ∀ q ∈ S, ε q = 1 ∨ ε q = -1) (N : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime, N < p ∧ p % 8 = 1 ∧
      ∀ q ∈ S, @legendreSym p ⟨hp⟩ (q : ℤ) = ε q := by
  classical
  have hr : ∀ q (hq : q ∈ S), ∃ r : ℕ, r.Coprime q ∧
      @legendreSym q ⟨hprime q hq⟩ (r : ℤ) = ε q := by
    intro q hq
    exact exists_legendre_residue q (hprime q hq) (hodd q hq) (ε q) (hε q hq)
  let r (q : ℕ) : ℕ := if h : q ∈ S then Classical.choose (hr q h) else 1
  have hr' (q : ℕ) (hq : q ∈ S) : (r q).Coprime q ∧
      @legendreSym q ⟨hprime q hq⟩ ((r q : ℕ) : ℤ) = ε q := by
    dsimp only [r]
    rw [dif_pos hq]
    exact Classical.choose_spec (hr q hq)
  let T := insert 2 S
  let m (q : ℕ) := if q = 2 then 8 else q
  let a (q : ℕ) := if q = 2 then 1 else r q
  have htprime (q : ℕ) (hq : q ∈ T) : q.Prime := by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Nat.prime_two
    · exact hprime q hq
  have hm (q : ℕ) (hq : q ∈ T) : m q ≠ 0 := by
    dsimp [m]
    split_ifs with h
    · norm_num
    · exact (htprime q hq).ne_zero
  have hpair : (T : Set ℕ).Pairwise (Function.onFun Nat.Coprime m) := by
    intro q hq u hu hqu
    have hcop := (Nat.coprime_primes (htprime q hq) (htprime u hu)).mpr hqu
    dsimp only [Function.onFun, m]
    split_ifs with hq2 hu2 hu2
    · exact False.elim (hqu (hq2.trans hu2.symm))
    · subst q
      simpa using hcop.pow_left 3
    · subst u
      simpa using hcop.pow_right 3
    · exact hcop
  have ha (q : ℕ) (hq : q ∈ T) : (a q).Coprime (m q) := by
    dsimp only [a, m]
    split_ifs with hq2
    · norm_num
    · exact (hr' q ((Finset.mem_insert.mp hq).resolve_left hq2)).1
  obtain ⟨p, hpN, hp, hcong⟩ := exists_prime_congruences T a m hm hpair ha N
  have hp8 : p % 8 = 1 := by
    have hh := hcong 2 (Finset.mem_insert_self _ _)
    simpa [m, a, Nat.ModEq] using hh
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpN, hp8, ?_⟩
  intro q hq
  letI : Fact q.Prime := ⟨hprime q hq⟩
  have hp4 : p % 4 = 1 := by omega
  rw [← legendreSym.quadratic_reciprocity_one_mod_four hp4 (hodd q hq)]
  have hh : Nat.ModEq q p (r q) := by
    simpa only [m, a, if_neg (hodd q hq)] using hcong q (Finset.mem_insert_of_mem hq)
  have hz : (p : ZMod q) = (r q : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh
  simp only [legendreSym, Int.cast_natCast]
  rw [hz]
  simpa only [legendreSym, Int.cast_natCast] using (hr' q hq).2

end Erdos66PrimeSign
