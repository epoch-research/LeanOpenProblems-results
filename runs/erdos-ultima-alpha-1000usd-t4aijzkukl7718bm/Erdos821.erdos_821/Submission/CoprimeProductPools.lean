import Submission.PrimeSubsetModuli

/-!
# Products of cross-coprime modulus pools

Exact mass and divisor-incidence identities. The entries of either pool
need not be prime; cross-coprimality is required for every pair.
-/
open Nat Finset
open scoped Classical BigOperators
namespace Erdos821
set_option maxHeartbeats 2000000

lemma coprime_pair_product_inj (D E : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d)
    (hDE : ∀ d ∈ D, ∀ e ∈ E, d.Coprime e) :
    Set.InjOn (fun z : ℕ × ℕ => z.1*z.2) (↑(D ×ˢ E) : Set (ℕ × ℕ)) := by
  intro z hz w hw he
  obtain ⟨hzD,hzE⟩ := mem_product.mp hz
  obtain ⟨hwD,hwE⟩ := mem_product.mp hw
  change z.1*z.2 = w.1*w.2 at he
  have hzw : z.1 ∣ w.1 := (hDE _ hzD _ hwE).dvd_of_dvd_mul_right
    (he ▸ dvd_mul_right z.1 z.2)
  have hwz : w.1 ∣ z.1 := (hDE _ hwD _ hzE).dvd_of_dvd_mul_right
    (he.symm ▸ dvd_mul_right w.1 w.2)
  have h := Nat.dvd_antisymm hzw hwz
  apply Prod.ext h
  rw [h] at he
  exact Nat.eq_of_mul_eq_mul_left (hD _ hwD) he

lemma sum_coprime_pairProducts (D E : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d)
    (hDE : ∀ d ∈ D, ∀ e ∈ E, d.Coprime e) (F : ℕ → ℝ) :
    (∑ q ∈ pairPrimeProducts D E, F q) = ∑ d ∈ D, ∑ e ∈ E, F (d*e) := by
  rw [pairPrimeProducts,sum_image (coprime_pair_product_inj D E hD hDE),sum_product]

lemma coprime_pairProducts_mass (D E : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d)
    (hDE : ∀ d ∈ D, ∀ e ∈ E, d.Coprime e) :
    poolTotientMass (pairPrimeProducts D E) = poolTotientMass D * poolTotientMass E := by
  unfold poolTotientMass
  rw [sum_coprime_pairProducts D E hD hDE,sum_mul]
  apply sum_congr rfl
  intro d hd
  rw [mul_sum]
  apply sum_congr rfl
  intro e he
  rw [Nat.totient_mul (hDE d hd e he),Nat.cast_mul,mul_inv_rev,mul_comm]

lemma coprime_pairProducts_divisor_count (D E : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d)
    (hDE : ∀ d ∈ D, ∀ e ∈ E, d.Coprime e) (n : ℕ) :
    ((pairPrimeProducts D E).filter (fun q => q ∣ n)).card =
      (D.filter (fun d => d ∣ n)).card * (E.filter (fun e => e ∣ n)).card := by
  have he : (D ×ˢ E).filter (fun z => z.1*z.2 ∣ n) =
      (D.filter (fun d => d ∣ n)) ×ˢ (E.filter (fun e => e ∣ n)) := by
    ext z
    simp only [mem_filter,mem_product]
    constructor
    · rintro ⟨⟨hd,he⟩,h⟩
      exact ⟨⟨hd,(dvd_mul_right z.1 z.2).trans h⟩,
        ⟨he,(dvd_mul_left z.2 z.1).trans h⟩⟩
    · rintro ⟨⟨hd,hdn⟩,⟨he,hen⟩⟩
      exact ⟨⟨hd,he⟩,(hDE _ hd _ he).mul_dvd_of_dvd_of_dvd hdn hen⟩
  unfold pairPrimeProducts
  rw [filter_image,he,Finset.card_image_of_injOn
    (coprime_pair_product_inj _ _ (fun d hd => hD d (mem_filter.mp hd).1)
      (fun d hd e he => hDE d (mem_filter.mp hd).1 e (mem_filter.mp he).1)),card_product]

lemma pairProducts_pos (D E : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) (hE : ∀ e ∈ E, 0 < e)
    {q : ℕ} (hq : q ∈ pairPrimeProducts D E) : 0 < q := by
  obtain ⟨⟨d,e⟩,hde,rfl⟩ := mem_image.mp hq
  exact Nat.mul_pos (hD d (mem_product.mp hde).1) (hE e (mem_product.mp hde).2)

lemma pairProducts_le (D E : Finset ℕ) (A B : ℕ)
    (hD : ∀ d ∈ D, d ≤ A) (hE : ∀ e ∈ E, e ≤ B)
    {q : ℕ} (hq : q ∈ pairPrimeProducts D E) : q ≤ A*B := by
  obtain ⟨⟨d,e⟩,hde,rfl⟩ := mem_image.mp hq
  exact Nat.mul_le_mul (hD d (mem_product.mp hde).1) (hE e (mem_product.mp hde).2)

lemma pairProducts_rough (D E : Finset ℕ) (L : ℕ)
    (hD : ∀ d ∈ D, 0 < d) (hE : ∀ e ∈ E, 0 < e)
    (hDr : ∀ d ∈ D, ∀ c ∈ d.divisors.erase 1, L ≤ c)
    (hEr : ∀ e ∈ E, ∀ c ∈ e.divisors.erase 1, L ≤ c)
    {q : ℕ} (hq : q ∈ pairPrimeProducts D E) {c : ℕ}
    (hc : c ∈ q.divisors.erase 1) : L ≤ c := by
  obtain ⟨hc1,hcd⟩ := mem_erase.mp hc
  obtain ⟨p,hp,hpc⟩ := Nat.exists_prime_and_dvd hc1
  obtain ⟨⟨d,e⟩,hde,rfl⟩ := mem_image.mp hq
  obtain ⟨hd,he⟩ := mem_product.mp hde
  have hpd : p ∣ d*e := hpc.trans (Nat.dvd_of_mem_divisors hcd)
  have hpL : L ≤ p := by
    rcases hp.dvd_mul.mp hpd with h | h
    · exact hDr d hd p (mem_erase.mpr ⟨hp.ne_one,Nat.mem_divisors.mpr ⟨h,(hD d hd).ne'⟩⟩)
    · exact hEr e he p (mem_erase.mpr ⟨hp.ne_one,Nat.mem_divisors.mpr ⟨h,(hE e he).ne'⟩⟩)
  exact hpL.trans (Nat.le_of_dvd (Nat.pos_of_mem_divisors hcd) hpc)

lemma disjoint_primeSubset_coprime (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) {r s d e : ℕ}
    (hd : d ∈ primeSubsetModuli P r) (he : e ∈ primeSubsetModuli Q s) : d.Coprime e := by
  obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
  obtain ⟨T,hT,rfl⟩ := mem_image.mp he
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  exact pair_prime_coprime hP hQ hPQ ((mem_powersetCard.mp hS).1 hp)
    ((mem_powersetCard.mp hT).1 hq)

lemma joint_primeSubset_divisor_count (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) (r s n : ℕ) (hn : 0 < n) :
    ((pairPrimeProducts (primeSubsetModuli P r) (primeSubsetModuli Q s)).filter
      (fun d => d ∣ n)).card =
      (P.filter (fun p => p ∣ n)).card.choose r *
        (Q.filter (fun q => q ∣ n)).card.choose s := by
  rw [coprime_pairProducts_divisor_count _ _
    (fun d hd => primeSubsetModuli_pos P hP hd)
    (fun d hd e he => disjoint_primeSubset_coprime P Q hP hQ hPQ hd he),
    primeSubsetModuli_divisor_count P hP r n hn,
    primeSubsetModuli_divisor_count Q hQ s n hn]

end Erdos821
