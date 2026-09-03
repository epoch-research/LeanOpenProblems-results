import FormalConjecturesUtil

/-! Intervals with individually distinguished prime factors, constructed by CRT.
This provides finite independent squareclasses; it does not address infinite
integer representation counts. -/
namespace Erdos66IntervalSquareclass

lemma exists_large_distinct_primes (h : ℕ) :
    ∃ q : Fin h → ℕ, Function.Injective q ∧ ∀ i, (q i).Prime ∧ h + 2 < q i := by
  let q (i : Fin h) := Nat.nth Nat.Prime (h + 3 + i.val)
  refine ⟨q, ?_, ?_⟩
  · intro i j hij
    have hh := Nat.nth_injective Nat.infinite_setOf_prime hij
    apply Fin.ext
    omega
  · intro i
    refine ⟨Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _, ?_⟩
    have hh : h + 3 + i.val ≤ q i :=
      Nat.le_nth (fun hf ↦ False.elim (Nat.infinite_setOf_prime hf))
    omega

/-- Each entry of a suitably translated interval has a prime divisor occurring
exactly once, and that prime divides no other entry of the interval. -/
theorem exists_interval_private_primes (h : ℕ) :
    ∃ a : ℕ, 0 < a ∧ ∃ q : Fin h → ℕ, Function.Injective q ∧
      ∀ i, (q i).Prime ∧ h + 2 < q i ∧ (a + i.val).factorization (q i) = 1 ∧
        ∀ j : Fin h, j ≠ i → ¬q i ∣ a + j.val := by
  classical
  obtain ⟨q, hqinj, hq⟩ := exists_large_distinct_primes h
  have hmods (i : Fin h) (_hi : i ∈ Finset.univ) : (q i) ^ 2 ≠ 0 :=
    pow_ne_zero _ (hq i).1.ne_zero
  have hpair : (↑(Finset.univ : Finset (Fin h)) : Set (Fin h)).Pairwise
      (Function.onFun Nat.Coprime (fun i ↦ (q i) ^ 2)) := by
    intro i hi j hj hij
    exact Nat.coprime_pow_primes 2 2 (hq i).1 (hq j).1 (hqinj.ne hij)
  let r := Nat.chineseRemainderOfFinset (fun i : Fin h ↦ q i - i.val)
    (fun i ↦ (q i) ^ 2) Finset.univ hmods hpair
  let M := ∏ i : Fin h, (q i) ^ 2
  have hMpos : 0 < M := Finset.prod_pos (fun i _ ↦ pow_pos (hq i).1.pos _)
  let a := r.val + M
  have ha : 0 < a := by dsimp [a]; omega
  have hc (i : Fin h) : Nat.ModEq ((q i) ^ 2) (a + i.val) (q i) := by
    have hMi : (q i) ^ 2 ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hM0 : Nat.ModEq ((q i) ^ 2) M 0 := Nat.modEq_zero_iff_dvd.mpr hMi
    have hh := ((r.property i (Finset.mem_univ i)).add hM0).add_right i.val
    have hiq : i.val ≤ q i := by have hi := i.isLt; have hh := (hq i).2; omega
    simpa only [a, Nat.add_zero, Nat.sub_add_cancel hiq] using hh
  have hdiv (i : Fin h) : q i ∣ a + i.val :=
    ((hc i).dvd_iff (dvd_pow_self _ (by omega : 2 ≠ 0))).mpr (dvd_refl _)
  refine ⟨a, ha, q, hqinj, ?_⟩
  intro i
  refine ⟨(hq i).1, (hq i).2, ?_, ?_⟩
  · have hai : a + i.val ≠ 0 := by omega
    have hone : 1 ≤ (a + i.val).factorization (q i) :=
      ((hq i).1.pow_dvd_iff_le_factorization hai).mp (by simpa only [pow_one] using hdiv i)
    have hnottwo : ¬2 ≤ (a + i.val).factorization (q i) := by
      intro ht
      have hd := ((hq i).1.pow_dvd_iff_le_factorization hai).mpr ht
      have hbad := ((hc i).dvd_iff (dvd_refl _)).mp hd
      have hqi := (hq i).1.two_le
      exact (Nat.not_dvd_of_pos_of_lt (hq i).1.pos (by nlinarith)) hbad
    omega
  · intro j hji hbad
    have heq : Nat.ModEq (q i) (a + i.val) (a + j.val) :=
      (Nat.modEq_zero_iff_dvd.mpr (hdiv i)).trans (Nat.modEq_zero_iff_dvd.mpr hbad).symm
    have hij := Nat.ModEq.add_left_cancel (Nat.ModEq.refl a) heq
    have hi : i.val < q i := by have hh := (hq i).2; have hh' := i.isLt; omega
    have hj : j.val < q i := by have hh := (hq i).2; have hh' := j.isLt; omega
    exact hji (Fin.ext ((hij.eq_of_lt_of_lt hi hj).symm))

end Erdos66IntervalSquareclass
