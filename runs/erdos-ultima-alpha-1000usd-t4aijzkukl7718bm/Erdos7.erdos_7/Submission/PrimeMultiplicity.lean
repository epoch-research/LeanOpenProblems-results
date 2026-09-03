import FormalConjecturesUtil

/-! Necessary multiplicity of maximal prime-exponents in an irredundant cover. -/

namespace Erdos7Reduction

private theorem dvd_step_of_two_dvd {m D : ℤ} {p t : ℕ}
    (hp : p.Prime) (ht0 : 0 < t) (htp : t < p)
    (hm : m ∣ (p : ℤ) * D) (ht : m ∣ (t : ℤ) * D) : m ∣ D := by
  obtain ⟨u, v, huv⟩ := (Nat.coprime_of_lt_prime (by omega) htp hp).isCoprime
  have h := dvd_add (dvd_mul_of_dvd_right hm u) (dvd_mul_of_dvd_right ht v)
  convert h using 1
  calc
    D = (u * (p : ℤ) + v * (t : ℤ)) * D := by rw [huv, one_mul]
    _ = u * ((p : ℤ) * D) + v * ((t : ℤ) * D) := by ring

private theorem prime_step_unique {m D a x : ℤ} {p : ℕ} (hp : p.Prime)
    (hm : m ∣ (p : ℤ) * D) (hD : ¬ m ∣ D) (k l : Fin p)
    (hk : m ∣ x + (k : ℤ) * D - a) (hl : m ∣ x + (l : ℤ) * D - a) :
    k = l := by
  have helper : ∀ k l : Fin p, k.val < l.val →
      m ∣ x + (k : ℤ) * D - a → m ∣ x + (l : ℤ) * D - a → False := by
    intro k l hkl hk hl
    have hdiff : m ∣ ((l.val - k.val : ℕ) : ℤ) * D := by
      have h := dvd_sub hl hk
      rw [Nat.cast_sub (by omega : k.val ≤ l.val)]
      convert h using 1 <;> ring
    exact hD (dvd_step_of_two_dvd hp (by omega) (by omega) hm hdiff)
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact helper k l h hk hl
  · exact helper l k h hl hk

/-- If an arithmetic cover has a private point belonging to a modulus not dividing `D`,
while all its moduli divide `pD`, at least `p` moduli fail to divide `D`. -/
theorem prime_step_multiplicity {ι : Type} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (p D : ℕ) (hp : p.Prime)
    (hdiv : ∀ i, m i ∣ p * D)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (i₀ : ι) (hi₀ : ¬ m i₀ ∣ D)
    (x : ℤ) (hprivate : ∀ j, j ≠ i₀ → ¬ (m j : ℤ) ∣ x - a j) :
    p ≤ Fintype.card {i : ι // ¬ m i ∣ D} := by
  classical
  have hmem (k : Fin p) :
      ∃ i : {i : ι // ¬ m i ∣ D}, (m i.val : ℤ) ∣ x + (k : ℤ) * D - a i.val := by
    obtain ⟨i, hi⟩ := hcover (x + (k : ℤ) * D)
    have hni : ¬ m i ∣ D := by
      intro h
      have hh : (m i : ℤ) ∣ (D : ℤ) := by exact_mod_cast h
      have hbase : (m i : ℤ) ∣ x - a i := by
        have hs := dvd_sub hi (dvd_mul_of_dvd_right hh (k : ℤ))
        convert hs using 1 <;> ring
      by_cases hii : i = i₀
      · subst i
        exact hi₀ h
      · exact hprivate i hii hbase
    exact ⟨⟨i, hni⟩, hi⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro k l hkl
    have hk := hf k
    have hl := hf l
    rw [hkl] at hk
    apply prime_step_unique hp (m := (m (f l).val : ℤ))
      (D := (D : ℤ)) (a := a (f l).val) (x := x) ?_ ?_ k l hk hl
    · exact_mod_cast hdiv (f l).val
    · exact_mod_cast (f l).property
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hinj


/-- Dropping a prime from a common multiple detects exactly the moduli having
maximal exponent at that prime. -/
theorem not_dvd_div_prime_iff {m N p : ℕ} (hm : m ≠ 0) (hN : N ≠ 0)
    (hp : p.Prime) (hpN : p ∣ N) (hmN : m ∣ N) :
    (¬ m ∣ N / p) ↔ m.factorization p = N.factorization p := by
  have hle := (Nat.factorization_le_iff_dvd hm hN).mpr hmN
  rw [Nat.dvd_div_iff_mul_dvd hpN,
    ← Nat.factorization_le_iff_dvd (mul_ne_zero hp.ne_zero hm) hN,
    Nat.factorization_mul hp.ne_zero hm, hp.factorization]
  constructor
  · intro hnot
    by_contra hne
    apply hnot
    intro q
    by_cases hqp : q = p
    · subst q
      have hmp := hle p
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      omega
    · simpa [Finsupp.single_apply, hqp, Ne.symm hqp] using hle q
  · intro heq h
    have hh := h p
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at hh
    omega

/-- Every prime in the common period of an irredundant arithmetic cover attains
its maximal exponent in at least that many moduli. Distinctness is not needed. -/
theorem maximal_prime_exponent_multiplicity {ι : Type} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (hprivate : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ Finset.univ.lcm m) :
    p ≤ Fintype.card {i : ι //
      (m i).factorization p = (Finset.univ.lcm m).factorization p} := by
  classical
  let N := Finset.univ.lcm m
  have hN : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by simpa using hm)
  have hmN (i : ι) : m i ∣ N := Finset.dvd_lcm (Finset.mem_univ i)
  have hex : ∃ i, ¬ m i ∣ N / p := by
    by_contra hh
    push_neg at hh
    have hNd : N ∣ N / p := Finset.lcm_dvd (by simpa using hh)
    have heq : N = N / p := Nat.dvd_antisymm hNd (Nat.div_dvd_of_dvd hpN)
    have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hN) hp.one_lt
    omega
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x, hx⟩ := hprivate i
  have hbound := prime_step_multiplicity m a p (N / p) hp
    (fun j => by rw [Nat.mul_div_cancel' hpN]; exact hmN j) hcover i hi x hx
  let e : {i : ι // ¬ m i ∣ N / p} ≃
      {i : ι // (m i).factorization p = N.factorization p} :=
    Equiv.subtypeEquivRight (fun i => not_dvd_div_prime_iff (hm i) hN hp hpN (hmN i))
  rwa [Fintype.card_congr e] at hbound

#print axioms maximal_prime_exponent_multiplicity

/-- An essential congruence cannot have a period component absent from all other
congruences in the cover. -/
theorem private_modulus_dvd_common_period {ι : Type}
    (m : ι → ℕ) (a : ι → ℤ)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (i₀ : ι) (D : ℕ) (hD : ∀ j, j ≠ i₀ → m j ∣ D)
    (x : ℤ) (hprivate : ∀ j, j ≠ i₀ → ¬ (m j : ℤ) ∣ x - a j) :
    m i₀ ∣ D := by
  have hx : (m i₀ : ℤ) ∣ x - a i₀ := by
    obtain ⟨j, hj⟩ := hcover x
    by_cases heq : j = i₀
    · simpa [heq] using hj
    · exact False.elim (hprivate j heq hj)
  obtain ⟨j, hj⟩ := hcover (x + D)
  have heq : j = i₀ := by
    by_contra hne
    have hDj : (m j : ℤ) ∣ (D : ℤ) := by exact_mod_cast hD j hne
    apply hprivate j hne
    convert dvd_sub hj hDj using 1 <;> ring
  subst j
  have hDz : (m i₀ : ℤ) ∣ (D : ℤ) := by
    convert dvd_sub hj hx using 1 <;> ring
  exact_mod_cast hDz

#print axioms private_modulus_dvd_common_period


#print axioms prime_step_multiplicity
end Erdos7Reduction
