import FormalConjecturesUtil

/-! The complementary product of a quartic representation need not divide
any fixed multiple of a fixed power of its target. This rules out one proposed
divisor-bound shortcut, not a bound for the full representation count. -/
namespace Erdos322Research.QuarticComplementDivisibilityObstruction

private def testTuple (p : ℕ) : Fin 4 → ℕ := ![1,1,1,p-2]

private lemma tuple_norm (p : ℕ) :
    ∑ i, testTuple p i ^ 4 = 3+(p-2)^4 := by
  simp [testTuple,Fin.sum_univ_four]

private lemma tuple_product (p : ℕ) (hp : 2 ≤ p) :
    ∏ i, ((∑ j, testTuple p j)-testTuple p i) = 3*p^3 := by
  have hs : ∑ j, testTuple p j=p+1 := by
    simp [testTuple,Fin.sum_univ_four]
    omega
  rw [show (fun i => (∑ j, testTuple p j)-testTuple p i) =
    (fun i => p+1-testTuple p i) by funext i; rw [hs]]
  rw [Fin.prod_univ_four]
  change (p+1-1)*(p+1-1)*(p+1-1)*(p+1-(p-2)) = 3*p^3
  have h1 : p+1-1=p := by omega
  have h2 : p+1-(p-2)=3 := by omega
  rw [h1,h2]
  ring

private lemma prime_not_dvd_norm (p : ℕ) (hp : p.Prime) (hp19 : 19 < p) :
    ¬ p ∣ 3+(p-2)^4 := by
  intro hd
  have hp2 : 2 ≤ p := hp.two_le
  have hdz : (p : ℤ) ∣ ((3+(p-2)^4 : ℕ) : ℤ) := by exact_mod_cast hd
  have he : ((3+(p-2)^4 : ℕ) : ℤ) =
      19+(p : ℤ)*((p : ℤ)^3-8*(p : ℤ)^2+24*p-32) := by
    push_cast [hp2]
    ring
  rw [he] at hdz
  have hz : (p : ℤ) ∣ 19 := by
    have hh := dvd_sub hdz (dvd_mul_right (p : ℤ)
      ((p : ℤ)^3-8*(p : ℤ)^2+24*p-32))
    simpa only [add_sub_cancel_right] using hh
  have hn : p ∣ 19 := by exact_mod_cast hz
  have hh := Nat.le_of_dvd (by decide : 0 < 19) hn
  omega

/-- No fixed positive multiplier and no fixed target power can absorb the
complementary products of all positive quartic tuples. -/
theorem no_eventual_fixed_target_divisibility (C D M : ℕ) (hC : 0 < C) :
    ∃ a : Fin 4 → ℕ,
      (∀ i, 0 < a i) ∧ M < (∑ i, a i^4) ∧
      ¬ (∏ i, ((∑ j, a j)-a i)) ∣ C*(∑ i, a i^4)^D := by
  obtain ⟨p,hpbig,hp⟩ := Nat.exists_infinite_primes (C+M+20)
  have hpC : C < p := by omega
  have hp19 : 19 < p := by omega
  refine ⟨testTuple p,?_,?_,?_⟩
  · intro i
    fin_cases i <;> simp [testTuple]
    omega
  · rw [tuple_norm]
    have hpow : p-2 ≤ (p-2)^4 := Nat.le_pow (by decide)
    omega
  · rw [tuple_product p hp.two_le,tuple_norm]
    intro hd
    have hpd : p ∣ 3*p^3 := by
      exact dvd_mul_of_dvd_right (dvd_pow_self p (by decide : 3 ≠ 0)) 3
    have hh := hp.dvd_mul.mp (hpd.trans hd)
    rcases hh with hc | hn
    · have hh := Nat.le_of_dvd hC hc
      omega
    · exact prime_not_dvd_norm p hp hp19 (hp.dvd_of_dvd_pow hn)

/-- The unrestricted fixed-divisibility shortcut fails in particular. -/
theorem no_fixed_target_divisibility (C D : ℕ) (hC : 0 < C) :
    ∃ a : Fin 4 → ℕ,
      (∀ i, 0 < a i) ∧
      ¬ (∏ i, ((∑ j, a j)-a i)) ∣ C*(∑ i, a i^4)^D := by
  obtain ⟨a,ha,_,hbad⟩ := no_eventual_fixed_target_divisibility C D 0 hC
  exact ⟨a,ha,hbad⟩

end Erdos322Research.QuarticComplementDivisibilityObstruction
