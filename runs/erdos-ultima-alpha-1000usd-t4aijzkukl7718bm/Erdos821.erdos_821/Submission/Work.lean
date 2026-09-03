import FormalConjecturesUtil

/-!
# Auxiliary results for Erdős problem 821

These results do not settle the conjecture. They establish finiteness of totient fibers,
the range ε ≥ 1, cardinality bounds, and unbounded multiplicity on every tail of ℕ.
They also give an explicit exponential lower bound using primes in dyadic intervals,
and uniform subpower upper bounds when the number of distinct prime factors of the output
is bounded.
A fully quantitative conditional result reduces the full conjecture to an explicit
dyadic density hypothesis for smooth shifted primes. A converse weighted argument now
proves equivalence with divergence of smooth shifted-prime Dirichlet series at every
root scale. Neither the density hypothesis nor the series-divergence condition is proved.
The full near-linear assertion for every 0 < ε < 1 remains unproved.
`Submission/Combined.lean` combines these lemmas with the finite sieve to prove
an unconditional lower bound with some fixed positive exponent.
-/

open Nat Filter

namespace Erdos821

noncomputable def g (n : ℕ) : ℕ :=
  { m : ℕ | totient m = n }.ncard

lemma finite_totient_fiber (n : ℕ) : {m : ℕ | totient m = n}.Finite := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  apply (Set.finite_Iic (n * (n + 2).factorial)).subset
  intro m hm
  change m ≤ n * (n + 2).factorial
  change totient m = n at hm
  have hsub : m.primeFactors ⊆ Finset.range (n + 2) := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.totient_prime hpprime, hm] at hpdvd
    have hple := Nat.le_of_dvd hnpos hpdvd
    simp only [Finset.mem_range]
    omega
  have hprodpos : 0 < ∏ p ∈ m.primeFactors, p :=
    Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  have hmdvd : m ∣ n * ∏ p ∈ m.primeFactors, p := by
    rw [← hm, Nat.totient_mul_prod_primeFactors]
    exact Nat.dvd_mul_right _ _
  have hprodle : (∏ p ∈ m.primeFactors, p) ≤ (n + 2).factorial := by
    calc
      (∏ p ∈ m.primeFactors, p) ≤ ∏ p ∈ m.primeFactors, (p + 1) :=
        Finset.prod_le_prod' (fun p _ => Nat.le_succ p)
      _ ≤ ∏ p ∈ Finset.range (n + 2), (p + 1) :=
        Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p _ _ => Nat.succ_le_succ (Nat.zero_le p))
      _ = (n + 2).factorial := Finset.prod_range_add_one_eq_factorial _
  exact (Nat.le_of_dvd (Nat.mul_pos hnpos hprodpos) hmdvd).trans
    (Nat.mul_le_mul_left n hprodle)

lemma one_lt_g_of_odd {m : ℕ} (hm : Odd m) (hmpos : 0 < m) :
    1 < g (totient m) := by
  apply (Set.one_lt_ncard (finite_totient_fiber (totient m))).mpr
  refine ⟨m, rfl, 2 * m, ?_, ?_⟩
  · exact Nat.totient_two_mul_of_odd hm
  · omega

lemma erdos_821_of_one_le {ε : ℝ} (hε : 1 ≤ ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 3)
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  refine ⟨p - 1, ?_, by omega⟩
  change (p - 1 : ℕ).cast ^ (1 - ε) < (g (p - 1) : ℝ)
  have hg : 1 < g (p - 1) := by
    simpa only [Nat.totient_prime hp] using one_lt_g_of_odd hpodd hp.pos
  have hbase : 1 ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ p - 1 by omega)
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hbase (show 1 - ε ≤ 0 by linarith)
  exact hpow.trans_lt (by exact_mod_cast hg)

lemma exists_g_gt_of_card (s t : Finset ℕ) (B : ℝ)
    (hmap : ∀ m ∈ s, totient m ∈ t)
    (hcard : (t.card : ℝ) * B < s.card) :
    ∃ n ∈ t, B < (g n : ℝ) := by
  obtain ⟨n, hnt, hn⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to
    hmap (by simpa only [nsmul_eq_mul] using hcard)
  refine ⟨n, hnt, hn.trans_le ?_⟩
  have hsub : (↑(s.filter (fun m => totient m = n)) : Set ℕ) ⊆
      {m : ℕ | totient m = n} := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  have hle := Set.ncard_le_ncard hsub (finite_totient_fiber n)
  simpa only [Set.ncard_coe_finset, g] using (Nat.cast_le (α := ℝ)).mpr hle

lemma eq_of_totient_eq_of_primeFactors_eq {a b : ℕ}
    (hφ : totient a = totient b) (hf : a.primeFactors = b.primeFactors) : a = b := by
  have ha := Nat.totient_mul_prod_primeFactors a
  have hb := Nat.totient_mul_prod_primeFactors b
  rw [hφ, hf] at ha
  have hpos : 0 < ∏ p ∈ b.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  exact Nat.eq_of_mul_eq_mul_right hpos (ha.symm.trans hb)

lemma g_le_two_pow_shifted_prime_divisors (n : ℕ) :
    g n ≤ 2 ^ ((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)).card := by
  let t := (Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)
  have hinj : Set.InjOn Nat.primeFactors {m : ℕ | totient m = n} := by
    intro a ha b hb hab
    exact eq_of_totient_eq_of_primeFactors_eq (ha.trans hb.symm) hab
  have hsub : Nat.primeFactors '' {m : ℕ | totient m = n} ⊆
      (↑t.powerset : Set (Finset ℕ)) := by
    rintro _ ⟨m, hm, rfl⟩
    change totient m = n at hm
    change m.primeFactors ∈ t.powerset
    apply Finset.mem_powerset.mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.totient_prime hprime, hm] at hdvd
    have hnpos : 0 < n := by
      rw [← hm, Nat.totient_pos]
      exact Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hp).2.2
    have hple := Nat.le_of_dvd hnpos hdvd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime, hdvd⟩
  have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet t.powerset)
  simpa only [Set.ncard_image_of_injOn hinj, Set.ncard_coe_finset,
    Finset.card_powerset, g, t] using hle

lemma exists_coprime_multiplier (n M : ℕ) (hn : Even n) (hM : M ≠ 0) :
    ∃ a : ℕ, a.Coprime M ∧ (n * a + 1).Coprime M := by
  let r : ℕ → ℕ := fun q => if q ∣ n + 1 then 2 else 1
  have hpair : Set.Pairwise (↑M.primeFactors : Set ℕ) Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset r id M.primeFactors
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero) hpair
  have hr (q : ℕ) (hq : q.Prime) (hqd : q ∣ M) :
      ¬q ∣ r q ∧ ¬q ∣ n * r q + 1 := by
    by_cases hqn : q ∣ n + 1
    · have hq2 : q ≠ 2 := by
        intro h
        subst q
        have hneven := hn.two_dvd
        omega
      simp only [r, if_pos hqn]
      constructor
      · intro h
        exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
      · intro h
        have h' : q ∣ 2 * (n + 1) := dvd_mul_of_dvd_right hqn 2
        have h'' : q ∣ 1 := by
          convert Nat.dvd_sub h' h using 1
          omega
        exact hq.not_dvd_one h''
    · simp only [r, if_neg hqn, mul_one]
      exact ⟨hq.not_dvd_one, hqn⟩
  refine ⟨a, ?_, ?_⟩
  · apply Nat.coprime_of_dvd
    intro q hq hqa hqM
    have haq := ha q (hq.mem_primeFactors hqM hM)
    exact (hr q hq hqM).1 ((haq.dvd_iff (dvd_refl q)).mp hqa)
  · apply Nat.coprime_of_dvd
    intro q hq hqa hqM
    have haq := (ha q (hq.mem_primeFactors hqM hM)).mul_left n |>.add_right 1
    exact (hr q hq hqM).2 ((haq.dvd_iff (dvd_refl q)).mp hqa)

lemma exists_prime_multiplier (n M B : ℕ) (hn : 0 < n) (hne : Even n) (hM : M ≠ 0) :
    ∃ p K : ℕ, B < p ∧ p.Prime ∧ 0 < K ∧ K.Coprime M ∧ p = n * K + 1 := by
  obtain ⟨a, ha, ha'⟩ := exists_coprime_multiplier n M hne hM
  have hcop : (n * a + 1).Coprime (n * M) := by
    apply Nat.coprime_mul_iff_right.mpr
    refine ⟨?_, ha'⟩
    simp [Nat.coprime_mul_left_add_left]
  obtain ⟨p, hpB, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_modEq
    (B + (n * a + 1)) (Nat.mul_ne_zero hn.ne' hM) hcop
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add (show n * a + 1 ≤ p by omega)).mp hpa.symm
  refine ⟨p, a + M * t, by omega, hp, ?_, ?_, ?_⟩
  · have hp2 := hp.two_le
    by_contra h
    have hzero : a + M * t = 0 := by omega
    have heq : p = n * (a + M * t) + 1 := by rw [ht]; ring
    rw [hzero] at heq
    omega
  · simpa only [Nat.coprime_add_mul_left_left] using ha
  · rw [ht]; ring

lemma totient_sq (K : ℕ) : totient (K ^ 2) = K * totient K := by
  by_cases hK : K = 0
  · simp [hK]
  have h := Nat.totient_gcd_mul_totient_mul K K
  simp only [Nat.gcd_self] at h
  apply Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hK))
  calc
    totient K * totient (K ^ 2) = totient K * totient K * K := by simpa only [pow_two] using h
    _ = totient K * (K * totient K) := by ring

lemma enlarge_totient_fiber (n N : ℕ) (s : Finset ℕ) (hn : 0 < n) (hne : Even n)
    (hs : ∀ m ∈ s, totient m = n) :
    ∃ n' : ℕ, ∃ s' : Finset ℕ, N < n' ∧ Even n' ∧
      s'.card = s.card + 1 ∧ ∀ m ∈ s', totient m = n' := by
  have hspos (m : ℕ) (hm : m ∈ s) : 0 < m := by
    apply Nat.totient_pos.mp
    rw [hs m hm]
    exact hn
  have hM : (∏ m ∈ s, m) ≠ 0 :=
    (Finset.prod_pos (fun m hm => hspos m hm)).ne'
  obtain ⟨p, K, hpB, hp, hK, hKM, hpeq⟩ :=
    exists_prime_multiplier n (∏ m ∈ s, m) (s.sup id + N + 1) hn hne hM
  have hpKlt : K < p := by nlinarith
  have hpK : p.Coprime K := Nat.coprime_of_lt_prime hK.ne' hpKlt hp
  have hφK : 0 < totient K := Nat.totient_pos.mpr hK
  have hmK (m : ℕ) (hm : m ∈ s) : m.Coprime (K ^ 2) :=
    (Nat.coprime_prod_right_iff.mp hKM m hm).symm.pow_right 2
  have hpnot : p * K ∉ s.image (fun m => m * K ^ 2) := by
    rintro h
    obtain ⟨m, hm, heq⟩ := Finset.mem_image.mp h
    have heq' : p = m * K := by
      apply Nat.eq_of_mul_eq_mul_right hK
      simpa only [pow_two, mul_assoc] using heq.symm
    have hpm : p ∣ m := hpK.dvd_mul_right.mp (heq' ▸ dvd_refl p)
    have hmp := Nat.le_of_dvd (hspos m hm) hpm
    have hms := Finset.le_sup (f := id) hm
    change m ≤ s.sup id at hms
    omega
  refine ⟨n * K * totient K, insert (p * K) (s.image (fun m => m * K ^ 2)),
    ?_, (hne.mul_right K).mul_right (totient K), ?_, ?_⟩
  · have hnk : N < n * K := by omega
    have hle : n * K ≤ n * K * totient K :=
      Nat.le_mul_of_pos_right _ hφK
    exact hnk.trans_le hle
  · rw [Finset.card_insert_of_notMem hpnot, Finset.card_image_of_injective]
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hK 2) hab
  · intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · rw [Nat.totient_mul hpK, Nat.totient_prime hp, hpeq, Nat.add_sub_cancel]
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
      rw [Nat.totient_mul (hmK a ha), hs a ha, totient_sq]
      exact (mul_assoc _ _ _).symm

lemma exists_large_totient_fiber (k N : ℕ) :
    ∃ n : ℕ, ∃ s : Finset ℕ, N < n ∧ Even n ∧
      k < s.card ∧ ∀ m ∈ s, totient m = n := by
  induction k generalizing N with
  | zero =>
    obtain ⟨n, s, hn, hne, hcard, hs⟩ :=
      enlarge_totient_fiber 2 N ∅ (by decide) (by decide) (by simp)
    exact ⟨n, s, hn, hne, by simp_all, hs⟩
  | succ k ih =>
    obtain ⟨n, s, hn, hne, hcard, hs⟩ := ih 0
    obtain ⟨n', s', hn', hne', hcard', hs'⟩ :=
      enlarge_totient_fiber n N s hn hne hs
    exact ⟨n', s', hn', hne', by omega, hs'⟩

lemma infinite_g_gt (k : ℕ) : {n : ℕ | k < g n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, s, hn, hne, hcard, hs⟩ := exists_large_totient_fiber k N
  refine ⟨n, ?_, hn⟩
  have hsub : (↑s : Set ℕ) ⊆ {m : ℕ | totient m = n} := hs
  have hle := Set.ncard_le_ncard hsub (finite_totient_fiber n)
  simp only [Set.ncard_coe_finset] at hle
  exact hcard.trans_le hle

lemma smoothNumbersUpTo_two_pow_card_le (E y : ℕ) :
    (Nat.smoothNumbersUpTo (2 ^ E) y).card ≤ (E + 1) ^ y := by
  let A := Nat.smoothNumbersUpTo (2 ^ E) y
  have hexp (m : A) (p : ℕ) : m.val.factorization p ≤ E := by
    by_cases hp : p.Prime
    · apply Nat.factorization_le_of_le_pow
      exact (Nat.mem_smoothNumbersUpTo.mp m.property).1.trans
        (Nat.pow_le_pow_left hp.two_le E)
    · simp only [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.zero_le]
  let f : A → (Fin y → Fin (E + 1)) := fun m p =>
    ⟨m.val.factorization p.val, Nat.lt_succ_of_le (hexp m p.val)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq
      (Nat.mem_smoothNumbersUpTo.mp a.property).2.1
      (Nat.mem_smoothNumbersUpTo.mp b.property).2.1
    intro p
    by_cases hp : p < y
    · exact congrArg Fin.val (congrFun hab ⟨p, hp⟩)
    · have hz (m : A) : m.val.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hpm
        have hp' := Nat.prime_of_mem_primeFactors hpm
        have hpd := Nat.dvd_of_mem_primeFactors hpm
        exact hp (Nat.mem_smoothNumbers'.mp
          (Nat.mem_smoothNumbersUpTo.mp m.property).2 p hp' hpd)
      rw [hz a, hz b]
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective f hinj

lemma totient_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    totient (∏ p ∈ P, p) = ∏ p ∈ P, (p - 1) := by
  let F : ArithmeticFunction ℕ := ⟨totient, Nat.totient_zero⟩
  have hF : F.IsMultiplicative := ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩
  calc
    totient (∏ p ∈ P, p) = ∏ p ∈ P, totient p :=
      hF.map_prod_of_prime P hP
    _ = ∏ p ∈ P, (p - 1) := Finset.prod_congr rfl (fun p hp => Nat.totient_prime (hP p hp))

lemma prod_smooth {ι : Type*} (s : Finset ι) (f : ι → ℕ) (y : ℕ)
    (hs : ∀ i ∈ s, f i ∈ Nat.smoothNumbers y) :
    (∏ i ∈ s, f i) ∈ Nat.smoothNumbers y := by
  apply Nat.mem_smoothNumbers'.mpr
  intro p hp hpd
  obtain ⟨i, hi, hd⟩ := (hp.prime.dvd_finset_prod_iff _).mp hpd
  exact Nat.mem_smoothNumbers'.mp (hs i hi) p hp hd

lemma large_g_of_smooth_shifted_primes (P : Finset ℕ) (L y k : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ L ∧ p - 1 ∈ Nat.smoothNumbers y)
    (hcard : ((L * k + 1) ^ y : ℝ) * B < (P.card.choose k : ℝ)) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 2 ^ (L * k) ∧ B < (g n : ℝ) := by
  let S := (P.powersetCard k).image (fun T : Finset ℕ => ∏ p ∈ T, p)
  let T := Nat.smoothNumbersUpTo (2 ^ (L * k)) y
  have hSinj : Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) (↑(P.powersetCard k) : Set (Finset ℕ)) := by
    intro s hs t ht heq
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => (hP p ((Finset.mem_powersetCard.mp hs).1 hp)).1
    have htp : ∀ p ∈ t, p.Prime := fun p hp => (hP p ((Finset.mem_powersetCard.mp ht).1 hp)).1
    have heq' := congrArg Nat.primeFactors heq
    simpa only [Nat.primeFactors_prod hsp, Nat.primeFactors_prod htp] using heq'
  have hScard : S.card = P.card.choose k := by
    dsimp only [S]
    rw [Finset.card_image_of_injOn hSinj, Finset.card_powersetCard]
  have hmap : ∀ m ∈ S, totient m ∈ T := by
    intro m hm
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hsP, hsk⟩ := Finset.mem_powersetCard.mp hs
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => (hP p (hsP hp)).1
    apply Nat.mem_smoothNumbersUpTo.mpr
    constructor
    · calc
        totient (∏ p ∈ s, p) ≤ ∏ p ∈ s, p := Nat.totient_le _
        _ ≤ (2 ^ L) ^ s.card := Finset.prod_le_pow_card s id (2 ^ L)
          (fun p hp => (hP p (hsP hp)).2.1)
        _ = 2 ^ (L * k) := by rw [hsk, pow_mul]
    · rw [totient_prod_primes s hsp]
      exact prod_smooth s (fun p => p - 1) y (fun p hp => (hP p (hsP hp)).2.2)
  have hTcard : (T.card : ℝ) ≤ ((L * k + 1) ^ y : ℝ) := by
    exact_mod_cast smoothNumbersUpTo_two_pow_card_le (L * k) y
  have hcount : (T.card : ℝ) * B < S.card := by
    rw [hScard]
    exact (mul_le_mul_of_nonneg_right hTcard hB).trans_lt hcard
  obtain ⟨n, hn, hg⟩ := exists_g_gt_of_card S T B hmap hcount
  obtain ⟨hnle, hnsmooth⟩ := Nat.mem_smoothNumbersUpTo.mp hn
  exact ⟨n, Nat.pos_of_ne_zero hnsmooth.1, hnle, hg⟩

lemma erdos_821_of_shifted_prime_estimate
    (H : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ C : ℕ,
      ∃ (P : Finset ℕ) (L y k : ℕ),
        (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ L ∧ p - 1 ∈ Nat.smoothNumbers y) ∧
        ((L * k + 1) ^ y : ℝ) *
          max (C : ℝ) (((2 ^ (L * k) : ℕ) : ℝ) ^ (1 - ε)) < (P.card.choose k : ℝ)) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  intro ε hε
  by_cases hεone : 1 ≤ ε
  · exact erdos_821_of_one_le hεone
  have hεlt : ε < 1 := lt_of_not_ge hεone
  apply Set.infinite_of_forall_exists_gt
  intro N
  let C := (Finset.range (N + 1)).sup g
  obtain ⟨P, L, y, k, hP, hcard⟩ := H ε hε hεlt C
  have hB : 0 ≤ max (C : ℝ) (((2 ^ (L * k) : ℕ) : ℝ) ^ (1 - ε)) :=
    (Nat.cast_nonneg C).trans (le_max_left _ _)
  obtain ⟨n, hnpos, hnle, hg⟩ := large_g_of_smooth_shifted_primes P L y k _ hB hP hcard
  refine ⟨n, ?_, ?_⟩
  · change (n : ℝ) ^ (1 - ε) < (g n : ℝ)
    have hp : (n : ℝ) ^ (1 - ε) ≤ (((2 ^ (L * k) : ℕ) : ℝ) ^ (1 - ε)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnle) (by linarith)
    exact (hp.trans (le_max_right _ _)).trans_lt hg
  · by_contra h
    have hnmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hgC : (g n : ℝ) ≤ C := by
      exact_mod_cast (Finset.le_sup (f := g) hnmem)
    exact (not_lt_of_ge hgC) ((le_max_left _ _).trans_lt hg)

def shiftedPrimeDivisors (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)

def admissibleSupports (n : ℕ) : Finset (Finset ℕ) :=
  (shiftedPrimeDivisors n).powerset.filter (fun S =>
    (∏ p ∈ S, (p - 1)) ∣ n ∧ (n / ∏ p ∈ S, (p - 1)).primeFactors ⊆ S)

lemma totient_mul_of_primeFactors_subset (m k : ℕ) (hm : m ≠ 0) (hk : k ≠ 0)
    (hsub : k.primeFactors ⊆ m.primeFactors) : totient (m * k) = k * totient m := by
  have hpf : (m * k).primeFactors = m.primeFactors := by
    rw [Nat.primeFactors_mul hm hk, Finset.union_eq_left.mpr hsub]
  have hrad : 0 < ∏ p ∈ m.primeFactors, p :=
    Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  apply Nat.eq_of_mul_eq_mul_right hrad
  calc
    totient (m * k) * (∏ p ∈ m.primeFactors, p) =
        (m * k) * (∏ p ∈ m.primeFactors, (p - 1)) := by
      simpa only [hpf] using Nat.totient_mul_prod_primeFactors (m * k)
    _ = k * (m * ∏ p ∈ m.primeFactors, (p - 1)) := by ring
    _ = k * (totient m * ∏ p ∈ m.primeFactors, p) := by
      rw [Nat.totient_mul_prod_primeFactors]
    _ = (k * totient m) * (∏ p ∈ m.primeFactors, p) := by ring

lemma primeFactors_mem_admissibleSupports {m n : ℕ} (hn : 0 < n) (hm : totient m = n) :
    m.primeFactors ∈ admissibleSupports n := by
  have hmpos : 0 < m := Nat.totient_pos.mp (hm ▸ hn)
  have hsub : m.primeFactors ⊆ shiftedPrimeDivisors n := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.totient_prime hprime, hm] at hpdvd
    have hple := Nat.le_of_dvd hn hpdvd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime, hpdvd⟩
  have hApos : 0 < ∏ p ∈ m.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr hsub, ?_, ?_⟩
  · rw [← hm, Nat.totient_eq_div_primeFactors_mul m]
    exact dvd_mul_left _ _
  · have hq : n / (∏ p ∈ m.primeFactors, (p - 1)) =
        m / (∏ p ∈ m.primeFactors, p) := by
      rw [← hm, Nat.totient_eq_div_primeFactors_mul m, Nat.mul_div_cancel _ hApos]
    rw [hq]
    exact Nat.primeFactors_mono (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_dvd m)) hmpos.ne'

lemma exists_preimage_of_admissibleSupport {n : ℕ} (hn : 0 < n) {S : Finset ℕ}
    (hS : S ∈ admissibleSupports n) :
    ∃ m : ℕ, totient m = n ∧ m.primeFactors = S := by
  obtain ⟨hSp, hAdvd, hqsub⟩ := Finset.mem_filter.mp hS
  have hSsub := Finset.mem_powerset.mp hSp
  have hSpr : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp (hSsub hp)).2.1
  have hradpos : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hSpr p hp).pos)
  have hApos : 0 < ∏ p ∈ S, (p - 1) :=
    Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (hSpr p hp).one_lt)
  have hqpos : 0 < n / (∏ p ∈ S, (p - 1)) :=
    Nat.div_pos (Nat.le_of_dvd hn hAdvd) hApos
  refine ⟨(∏ p ∈ S, p) * (n / (∏ p ∈ S, (p - 1))), ?_, ?_⟩
  · rw [totient_mul_of_primeFactors_subset _ _ hradpos.ne' hqpos.ne']
    · rw [totient_prod_primes S hSpr, Nat.div_mul_cancel hAdvd]
    · rwa [Nat.primeFactors_prod hSpr]
  · rw [Nat.primeFactors_mul hradpos.ne' hqpos.ne', Nat.primeFactors_prod hSpr,
      Finset.union_eq_left.mpr hqsub]

lemma g_eq_card_admissibleSupports {n : ℕ} (hn : 0 < n) :
    g n = (admissibleSupports n).card := by
  rw [g, Set.ncard_eq_toFinset_card _ (finite_totient_fiber n)]
  apply Finset.card_bij (fun m _ => m.primeFactors)
  · intro m hm
    exact primeFactors_mem_admissibleSupports hn ((finite_totient_fiber n).mem_toFinset.mp hm)
  · intro a ha b hb hab
    have ha' := (finite_totient_fiber n).mem_toFinset.mp ha
    have hb' := (finite_totient_fiber n).mem_toFinset.mp hb
    exact eq_of_totient_eq_of_primeFactors_eq (ha'.trans hb'.symm) hab
  · intro S hS
    obtain ⟨m, hm, hmf⟩ := exists_preimage_of_admissibleSupport hn hS
    exact ⟨m, (finite_totient_fiber n).mem_toFinset.mpr hm, hmf⟩

lemma pow_le_pred_pow_succ {p k : ℕ} (hp : 2 ≤ p) (hlarge : 2 ^ (k + 1) ≤ p) :
    p ^ k ≤ (p - 1) ^ (k + 1) := by
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ (k + 1)) _ (by positivity)
  calc
    p ^ k * 2 ^ (k + 1) ≤ p ^ k * p := Nat.mul_le_mul_left _ hlarge
    _ = p ^ (k + 1) := (pow_succ _ _).symm
    _ ≤ (2 * (p - 1)) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
    _ = (p - 1) ^ (k + 1) * 2 ^ (k + 1) := by rw [mul_pow, mul_comm]

lemma input_pow_le_totient_pow (m k : ℕ) (hk : 0 < k) :
    m ^ k ≤ ((2 ^ (k + 1)).factorial) ^ k * (totient m) ^ (k + 1) := by
  by_cases hm : m = 0
  · simp [hm, Nat.ne_of_gt hk]
  let P := 2 ^ (k + 1)
  let R := ∏ p ∈ m.primeFactors, p
  let A := ∏ p ∈ m.primeFactors, (p - 1)
  let q := m / R
  have hRpos : 0 < R := Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  have hRdvd : R ∣ m := Nat.prod_primeFactors_dvd m
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hRdvd) hRpos
  have hmq : q * R = m := Nat.div_mul_cancel hRdvd
  have hφ : totient m = q * A := Nat.totient_eq_div_primeFactors_mul m
  have hsmallsub : m.primeFactors.filter (fun p => p < P) ⊆ Finset.range P := by
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  have hsmall : (∏ p ∈ m.primeFactors.filter (fun p => p < P), p) ≤ P.factorial := by
    calc
      (∏ p ∈ m.primeFactors.filter (fun p => p < P), p) ≤
          ∏ p ∈ m.primeFactors.filter (fun p => p < P), (p + 1) :=
        Finset.prod_le_prod' (fun p _ => Nat.le_succ p)
      _ ≤ ∏ p ∈ Finset.range P, (p + 1) :=
        Finset.prod_le_prod_of_subset_of_one_le' hsmallsub
          (fun p _ _ => Nat.succ_le_succ (Nat.zero_le p))
      _ = P.factorial := Finset.prod_range_add_one_eq_factorial _
  have hpoint (p : ℕ) (hp : p ∈ m.primeFactors) :
      p ^ k ≤ (if p < P then p ^ k else 1) * (p - 1) ^ (k + 1) := by
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hpP : p < P
    · rw [if_pos hpP]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    · rw [if_neg hpP, one_mul]
      exact pow_le_pred_pow_succ hp2 (Nat.le_of_not_gt hpP)
  have hrad : R ^ k ≤ P.factorial ^ k * A ^ (k + 1) := by
    calc
      R ^ k = ∏ p ∈ m.primeFactors, p ^ k := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ p ∈ m.primeFactors, (if p < P then p ^ k else 1) * (p - 1) ^ (k + 1) :=
        Finset.prod_le_prod' hpoint
      _ = (∏ p ∈ m.primeFactors.filter (fun p => p < P), p) ^ k * A ^ (k + 1) := by
        rw [Finset.prod_mul_distrib, ← Finset.prod_filter, Finset.prod_pow, Finset.prod_pow]
      _ ≤ P.factorial ^ k * A ^ (k + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hsmall k)
  calc
    m ^ k = (q * R) ^ k := by rw [hmq]
    _ = q ^ k * R ^ k := mul_pow _ _ _
    _ ≤ q ^ k * (P.factorial ^ k * A ^ (k + 1)) := Nat.mul_le_mul_left _ hrad
    _ ≤ q ^ (k + 1) * (P.factorial ^ k * A ^ (k + 1)) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hqpos (Nat.le_succ k))
    _ = P.factorial ^ k * (q * A) ^ (k + 1) := by rw [mul_pow]; ring
    _ = P.factorial ^ k * (totient m) ^ (k + 1) := by rw [hφ]

lemma g_pow_le (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (g n) ^ k ≤ ((2 ^ (k + 1)).factorial) ^ k * n ^ (k + 1) := by
  let S := (finite_totient_fiber n).toFinset
  have hScard : S.card = g n := (Set.ncard_eq_toFinset_card _ (finite_totient_fiber n)).symm
  by_cases hS : S.Nonempty
  · let M := S.max' hS
    have hM : totient M = n :=
      (finite_totient_fiber n).mem_toFinset.mp (Finset.max'_mem S hS)
    have hsub : S ⊆ Finset.Icc 1 M := by
      intro m hm
      have hmφ : totient m = n := (finite_totient_fiber n).mem_toFinset.mp hm
      have hmpos : 0 < m := Nat.totient_pos.mp (hmφ ▸ hn)
      exact Finset.mem_Icc.mpr ⟨hmpos, Finset.le_max' S m hm⟩
    have hcardle : S.card ≤ M := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
    have hgM : g n ≤ M := by simpa only [hScard] using hcardle
    exact (Nat.pow_le_pow_left hgM k).trans (by
      simpa only [hM] using input_pow_le_totient_pow M k hk)
  · have hg : g n = 0 := by
      rw [← hScard, Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
    simp [hg, Nat.ne_of_gt hk]

lemma eventually_g_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hkR : 0 < (k : ℝ) := (div_pos (by norm_num) hε).trans hk
  have hkN : 0 < k := by exact_mod_cast hkR
  have hkε : 2 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  filter_upwards [eventually_ge_atTop 1,
    eventually_ge_atTop (((2 ^ (k + 1)).factorial) ^ k)] with n hn hC
  have hpow : (g n) ^ k ≤ n ^ (k + 2) := by
    calc
      (g n) ^ k ≤ ((2 ^ (k + 1)).factorial) ^ k * n ^ (k + 1) :=
        g_pow_le n k hn hkN
      _ ≤ n * n ^ (k + 1) := Nat.mul_le_mul_right _ hC
      _ = n ^ (k + 2) := (pow_succ' n (k + 1)).symm
  have hpowR : (g n : ℝ) ^ k ≤ (n : ℝ) ^ (k + 2) := by exact_mod_cast hpow
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbound : (n : ℝ) ^ (k + 2) ≤ ((n : ℝ) ^ (1 + ε)) ^ k := by
    rw [← Real.rpow_natCast (n : ℝ) (k + 2),
      ← Real.rpow_natCast ((n : ℝ) ^ (1 + ε)) k,
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    apply Real.rpow_le_rpow_of_exponent_le hnr
    push_cast
    nlinarith
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg (g n))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hkN.ne').mp (hpowR.trans hbound)

lemma finite_g_gt_one_add (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 + ε)}.Finite := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_g_le_rpow ε hε)
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra h
  exact (not_lt_of_ge (hN n (Nat.le_of_not_gt h))) hn

/-- Each optional prime support gives a different inverse image of the same totient. -/
lemma two_pow_card_sdiff_le_g_prod_pred (P C : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hCP : C ⊆ P)
    (hclosed : ∀ p ∈ P, (p - 1).primeFactors ⊆ C) :
    2 ^ (P \ C).card ≤ g (∏ p ∈ P, (p - 1)) := by
  let n := ∏ p ∈ P, (p - 1)
  have hn : 0 < n := Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (hP p hp).one_lt)
  have hnC : n.primeFactors ⊆ C := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    obtain ⟨p, hp, hqp'⟩ := (hqp.prime.dvd_finset_prod_iff _).mp (Nat.dvd_of_mem_primeFactors hq)
    exact hclosed p hp (hqp.mem_primeFactors hqp' (Nat.sub_pos_of_lt (hP p hp).one_lt).ne')
  have hS (T : Finset ℕ) (hT : T ∈ (P \ C).powerset) :
      C ∪ T ∈ admissibleSupports n := by
    have hTP := Finset.mem_powerset.mp hT
    have hSP : C ∪ T ⊆ P := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hCP hp
      · exact Finset.mem_sdiff.mp (hTP hp) |>.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro p hp
      have hpP := hSP hp
      have hpdvd : p - 1 ∣ n := Finset.dvd_prod_of_mem (fun p => p - 1) hpP
      have hple := Nat.le_of_dvd hn hpdvd
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hP p hpP, hpdvd⟩
    · have hdiv : (∏ p ∈ C ∪ T, (p - 1)) ∣ n := Finset.prod_dvd_prod_of_subset _ _ _ hSP
      refine ⟨hdiv, ?_⟩
      exact (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdiv) hn.ne').trans
        (hnC.trans Finset.subset_union_left)
  have hinj : Set.InjOn (fun T : Finset ℕ => C ∪ T) (↑(P \ C).powerset : Set (Finset ℕ)) := by
    intro T hT U hU heq
    have hTP := Finset.mem_powerset.mp hT
    have hUP := Finset.mem_powerset.mp hU
    change C ∪ T = C ∪ U at heq
    ext p
    constructor
    · intro hp
      have hpC := (Finset.mem_sdiff.mp (hTP hp)).2
      have hp' : p ∈ C ∪ U := by rw [← heq]; exact Finset.mem_union_right C hp
      exact (Finset.mem_union.mp hp').resolve_left hpC
    · intro hp
      have hpC := (Finset.mem_sdiff.mp (hUP hp)).2
      have hp' : p ∈ C ∪ T := by rw [heq]; exact Finset.mem_union_right C hp
      exact (Finset.mem_union.mp hp').resolve_left hpC
  have hsub : ((P \ C).powerset.image (fun T => C ∪ T)) ⊆ admissibleSupports n := by
    intro S hS'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS'
    exact hS T hT
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Finset.card_powerset,
    ← g_eq_card_admissibleSupports hn] at hcard

lemma prime_le_half_of_dvd_prime_pred {p q x : ℕ} (hx : 4 ≤ x)
    (hp : p.Prime) (hpx : p ≤ x) (hq : q.Prime) (hqp : q ∣ p - 1) :
    q ≤ x / 2 := by
  by_cases hq2 : q = 2
  · omega
  by_cases hp2 : p = 2
  · subst p
    exact (hq.not_dvd_one hqp).elim
  have heven : 2 ∣ p - 1 := (hp.even_sub_one hp2).two_dvd
  have hcop : (2 : ℕ).Coprime q :=
    (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  have hdvd : 2 * q ∣ p - 1 := hcop.mul_dvd_of_dvd_of_dvd heven hqp
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hdvd
  omega

/-- An explicit fiber with an independently selectable support for each prime in `(x/2,x]`. -/
lemma dyadic_primes_g_lower_bound (x : ℕ) (hx : 4 ≤ x) :
    2 ^ ((x + 1).primesBelow \ (x / 2 + 1).primesBelow).card ≤
      g (∏ p ∈ (x + 1).primesBelow, (p - 1)) := by
  apply two_pow_card_sdiff_le_g_prod_pred
  · intro p hp
    exact (Nat.mem_primesBelow.mp hp).2
  · intro p hp
    obtain ⟨hplt, hprime⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩
  · intro p hp q hq
    obtain ⟨hplt, hprime⟩ := Nat.mem_primesBelow.mp hp
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hqle := prime_le_half_of_dvd_prime_pred hx hprime (by omega) hqprime
      (Nat.dvd_of_mem_primeFactors hq)
    exact Nat.mem_primesBelow.mpr ⟨by omega, hqprime⟩

/-- Pigeonholing the smooth part still works when all totients have a common,
possibly nonsmooth, factor. The family may impose additional support constraints. -/
lemma large_g_of_common_smooth_part
    (F : Finset (Finset ℕ)) (E y c : ℕ) (B : ℝ)
    (hc : 0 < c) (hB : 0 ≤ B)
    (hF : ∀ S ∈ F, (∀ p ∈ S, p.Prime) ∧
      (∏ p ∈ S, p) ≤ 2 ^ E ∧
      ∃ a ∈ Nat.smoothNumbers y, (∏ p ∈ S, (p - 1)) = c * a)
    (hcard : ((E + 1) ^ y : ℝ) * B < (F.card : ℝ)) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 2 ^ E ∧ B < (g n : ℝ) := by
  let inputs := F.image (fun S => ∏ p ∈ S, p)
  let smoothParts := Nat.smoothNumbersUpTo (2 ^ E) y
  let outputs := (smoothParts.image (fun a => c * a)).filter (fun n => n ≤ 2 ^ E)
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (↑F : Set (Finset ℕ)) := by
    intro S hS T hT hprod
    have h := congrArg Nat.primeFactors hprod
    simpa only [Nat.primeFactors_prod (hF S hS).1,
      Nat.primeFactors_prod (hF T hT).1] using h
  have hinputs : inputs.card = F.card := Finset.card_image_of_injOn hinj
  have hmap : ∀ m ∈ inputs, totient m ∈ outputs := by
    intro m hm
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hprime, hprodle, a, hasmooth, ha⟩ := hF S hS
    have hφ : totient (∏ p ∈ S, p) = c * a := by
      rw [totient_prod_primes S hprime]
      exact ha
    have hφle : totient (∏ p ∈ S, p) ≤ 2 ^ E :=
      (Nat.totient_le _).trans hprodle
    have hale : a ≤ 2 ^ E := calc
      a ≤ c * a := Nat.le_mul_of_pos_left _ hc
      _ = totient (∏ p ∈ S, p) := hφ.symm
      _ ≤ 2 ^ E := hφle
    apply Finset.mem_filter.mpr
    refine ⟨?_, hφle⟩
    apply Finset.mem_image.mpr
    exact ⟨a, Nat.mem_smoothNumbersUpTo.mpr ⟨hale, hasmooth⟩, hφ.symm⟩
  have houtle : outputs.card ≤ (E + 1) ^ y := calc
    outputs.card ≤ (smoothParts.image (fun a => c * a)).card := Finset.card_filter_le _ _
    _ ≤ smoothParts.card := Finset.card_image_le
    _ ≤ (E + 1) ^ y := smoothNumbersUpTo_two_pow_card_le E y
  have hcount : (outputs.card : ℝ) * B < inputs.card := by
    rw [hinputs]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast houtle) hB).trans_lt hcard
  obtain ⟨n, hn, hg⟩ := exists_g_gt_of_card inputs outputs B hmap hcount
  obtain ⟨hnimage, hnle⟩ := Finset.mem_filter.mp hn
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnimage
  have hapos : 0 < a := Nat.pos_of_ne_zero (Nat.mem_smoothNumbersUpTo.mp ha).2.1
  exact ⟨c * a, Nat.mul_pos hc hapos, hnle, hg⟩

/-- A block version of the smooth-part argument: choose one prime from each
pairwise disjoint block, fixing the product of their nonsmooth parts. -/
lemma large_g_of_prime_blocks (r L y : ℕ) (P : Fin r → Finset ℕ)
    (c : Fin r → ℕ) (a : Fin r → ℕ → ℕ) (B : ℝ)
    (hc : ∀ i, 0 < c i) (hB : 0 ≤ B)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hP : ∀ i p, p ∈ P i → p.Prime ∧ p ≤ 2 ^ L ∧
      p - 1 = c i * a i p ∧ a i p ∈ Nat.smoothNumbers y)
    (hcard : ((L * r + 1) ^ y : ℝ) * B < ∏ i, ((P i).card : ℝ)) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 2 ^ (L * r) ∧ B < (g n : ℝ) := by
  classical
  let Choice := ∀ i : Fin r, {p : ℕ // p ∈ P i}
  let supp : Choice → Finset ℕ := fun f => Finset.univ.image (fun i => (f i).val)
  let F := Finset.univ.image supp
  have hval_inj (f : Choice) : Function.Injective (fun i => (f i).val) := by
    intro i j heq
    change (f i).val = (f j).val at heq
    by_contra hij
    exact Finset.disjoint_left.mp (hdisj i j hij) (f i).property (by rw [heq]; exact (f j).property)
  have hsupp_inj : Function.Injective supp := by
    intro f g heq
    funext i
    apply Subtype.ext
    have hmem : (f i).val ∈ supp g := by
      rw [← heq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    have hij : i = j := by
      by_contra hij
      exact Finset.disjoint_left.mp (hdisj i j hij) (f i).property (hj ▸ (g j).property)
    subst j
    exact hj.symm
  have hFcard : F.card = ∏ i, (P i).card := by
    dsimp only [F]
    rw [Finset.card_image_of_injective _ hsupp_inj, Finset.card_univ]
    simp only [Choice, Fintype.card_pi, Fintype.card_coe]
  apply large_g_of_common_smooth_part F (L * r) y (∏ i, c i) B
    (Finset.prod_pos fun i _ => hc i) hB
  · intro S hS
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hS
    have hprime : ∀ p ∈ supp f, p.Prime := by
      intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact (hP i _ (f i).property).1
    refine ⟨hprime, ?_, ?_⟩
    · calc
        (∏ p ∈ supp f, p) = ∏ i : Fin r, (f i).val := by
          exact Finset.prod_image (fun i _ j _ heq => hval_inj f heq)
        _ ≤ (2 ^ L) ^ (Finset.univ : Finset (Fin r)).card :=
          Finset.prod_le_pow_card _ _ _ (fun i _ => (hP i _ (f i).property).2.1)
        _ = 2 ^ (L * r) := by simp only [Finset.card_univ, Fintype.card_fin, pow_mul]
    · refine ⟨∏ i, a i (f i).val, ?_, ?_⟩
      · exact prod_smooth Finset.univ (fun i => a i (f i).val) y
          (fun i _ => (hP i _ (f i).property).2.2.2)
      · calc
          (∏ p ∈ supp f, (p - 1)) = ∏ i : Fin r, ((f i).val - 1) := by
            exact Finset.prod_image (fun i _ j _ heq => hval_inj f heq)
          _ = ∏ i, c i * a i (f i).val :=
            Finset.prod_congr rfl (fun i _ => (hP i _ (f i).property).2.2.1)
          _ = (∏ i, c i) * ∏ i, a i (f i).val := Finset.prod_mul_distrib
  · simpa only [hFcard, Nat.cast_prod, Nat.cast_mul] using hcard

lemma eq_fermatNumber_of_prime_pred_dvd_two_pow {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p - 1 ∣ 2 ^ k) :
    p = Nat.fermatNumber (Nat.log 2 (Nat.log 2 (p - 1))) := by
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hpa : p = 2 ^ a + 1 := by have := hp.two_le; omega
  have ha0 : a ≠ 0 := by intro h; simp [h] at hpa; exact hp2 hpa
  obtain ⟨j, rfl⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < (2 : ℕ)) ha0 (hpa ▸ hp)
  rw [ha, Nat.log_pow (by decide), Nat.log_pow (by decide)]
  exact hpa

/-- Powers of two cannot themselves witness a positive-power lower bound for `g`. -/
lemma g_two_pow_le (k : ℕ) : g (2 ^ k) ≤ k + 2 := by
  let A := admissibleSupports (2 ^ k)
  let I : ℕ → ℕ := fun p => Nat.log 2 (Nat.log 2 (p - 1))
  let T : Finset ℕ → Finset ℕ := fun S => (S.erase 2).image I
  let t : Finset ℕ → ℕ := fun S => ∑ j ∈ T S, 2 ^ j
  have hn : 0 < 2 ^ k := by positivity
  have hp (S : Finset ℕ) (hS : S ∈ A) (p : ℕ) (hpS : p ∈ S) :
      p.Prime ∧ p - 1 ∣ 2 ^ k := by
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    exact (Finset.mem_filter.mp (hsub hpS)).2
  have hrepr (S : Finset ℕ) (hS : S ∈ A) :
      S.erase 2 = (T S).image Nat.fermatNumber := by
    dsimp only [T]
    rw [Finset.image_image]
    symm
    calc
      _ = (S.erase 2).image id := by
        apply Finset.image_congr
        intro p hpS
        obtain ⟨hp2, hpS⟩ := Finset.mem_erase.mp hpS
        exact (eq_fermatNumber_of_prime_pred_dvd_two_pow (hp S hS p hpS).1 hp2
          (hp S hS p hpS).2).symm
      _ = S.erase 2 := Finset.image_id
  have hprod (S : Finset ℕ) (hS : S ∈ A) :
      (∏ p ∈ S, (p - 1)) = 2 ^ t S := by
    rw [← Finset.prod_erase S (f := fun p : ℕ => p - 1) (a := 2) (by decide), hrepr S hS]
    rw [Finset.prod_image (fun i _ j _ h => Nat.fermatNumber_injective h)]
    simp only [Nat.fermatNumber, Nat.add_sub_cancel, Finset.prod_pow_eq_pow_sum, t]
  have htle (S : Finset ℕ) (hS : S ∈ A) : t S ≤ k := by
    have hdiv := (Finset.mem_filter.mp hS).2.1
    rw [hprod S hS] at hdiv
    exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mp hdiv
  have ht_eq (S : Finset ℕ) (hS : S ∈ A) (h2 : 2 ∉ S) : t S = k := by
    apply le_antisymm (htle S hS)
    by_contra h
    have htk : t S < k := by omega
    have hq : 2 ^ k / (∏ p ∈ S, (p - 1)) = 2 ^ (k - t S) := by
      rw [hprod S hS]
      have he : 2 ^ k = 2 ^ t S * 2 ^ (k - t S) := by
        rw [← pow_add, Nat.add_sub_of_le (htle S hS)]
      rw [he, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ t S)]
    have hsub := (Finset.mem_filter.mp hS).2.2
    rw [hq, Nat.primeFactors_pow 2 (by omega)] at hsub
    exact h2 (hsub (by simp))
  have hrec (S U : Finset ℕ) (hS : S ∈ A) (hU : U ∈ A)
      (ht : t S = t U) (h2 : 2 ∈ S ↔ 2 ∈ U) : S = U := by
    have hT : T S = T U := Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ)) ht
    have herase : S.erase 2 = U.erase 2 := by rw [hrepr S hS, hrepr U hU, hT]
    ext p
    by_cases hp2 : p = 2
    · subst p
      exact h2
    · simpa only [Finset.mem_erase, ne_eq, hp2, not_false_eq_true, true_and]
        using Finset.ext_iff.mp herase p
  let code : Finset ℕ → ℕ := fun S => if 2 ∈ S then t S else k + 1
  have hmaps : Set.MapsTo code (↑A : Set (Finset ℕ)) (↑(Finset.range (k + 2)) : Set ℕ) := by
    intro S hS
    apply Finset.mem_range.mpr
    dsimp only [code]
    split_ifs
    · exact lt_of_le_of_lt (htle S hS) (by omega)
    · omega
  have hinj : Set.InjOn code (↑A : Set (Finset ℕ)) := by
    intro S hS U hU heq
    by_cases hS2 : 2 ∈ S <;> by_cases hU2 : 2 ∈ U
    · refine hrec S U hS hU ?_ ?_
      · simpa only [code, if_pos hS2, if_pos hU2] using heq
      · simp only [hS2, hU2]
    · have hle := htle S hS
      simp only [code, if_pos hS2, if_neg hU2] at heq
      omega
    · have hle := htle U hU
      simp only [code, if_neg hS2, if_pos hU2] at heq
      omega
    · refine hrec S U hS hU ?_ ?_
      · rw [ht_eq S hS hS2, ht_eq U hU hU2]
      · simp only [hS2, hU2]
  have hcard := Finset.card_le_card_of_injOn code hmaps hinj
  simpa only [Finset.card_range, A, ← g_eq_card_admissibleSupports hn] using hcard

lemma eventually_g_two_pow_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (g (2 ^ k) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) ^ δ := by
  have hr : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have hO := isLittleO_coe_const_pow_of_one_lt (R := ℝ) hr
  filter_upwards [hO.bound (by norm_num : 0 < (1 / 2 : ℝ)),
    eventually_ge_atTop 2] with k hk hk2
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hk' : (k : ℝ) ≤ (1 / 2 : ℝ) * ((2 : ℝ) ^ δ) ^ k := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ k by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ ((2 : ℝ) ^ δ) ^ k by positivity)] using hk
  calc
    (g (2 ^ k) : ℝ) ≤ k + 2 := by exact_mod_cast g_two_pow_le k
    _ ≤ ((2 : ℝ) ^ δ) ^ k := by linarith
    _ = ((2 ^ k : ℕ) : ℝ) ^ δ := by
      rw [Real.rpow_pow_comm (by norm_num), Nat.cast_pow, Nat.cast_ofNat]

lemma finite_g_two_pow_gt_rpow (δ : ℝ) (hδ : 0 < δ) :
    {k : ℕ | (g (2 ^ k) : ℝ) > ((2 ^ k : ℕ) : ℝ) ^ δ}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_g_two_pow_le_rpow δ hδ)
  apply (Set.finite_Iio N).subset
  intro k hk
  change k < N
  by_contra h
  exact (not_lt_of_ge (hN k (Nat.le_of_not_gt h))) hk

/-- A weighted count of admissible prime supports. -/
lemma g_mul_rpow_neg_le_support_product {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 ≤ s) :
    (g n : ℝ) * (n : ℝ) ^ (-s) ≤
      ∏ p ∈ shiftedPrimeDivisors n, (1 + ((p - 1 : ℕ) : ℝ) ^ (-s)) := by
  let w : ℕ → ℝ := fun p => ((p - 1 : ℕ) : ℝ) ^ (-s)
  have hpoint (S : Finset ℕ) (hS : S ∈ admissibleSupports n) :
      (n : ℝ) ^ (-s) ≤ ∏ p ∈ S, w p := by
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hSpr (p : ℕ) (hp : p ∈ S) : p.Prime :=
      (Finset.mem_filter.mp (hsub hp)).2.1
    have hpos : 0 < ∏ p ∈ S, (p - 1) :=
      Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (hSpr p hp).one_lt)
    have hle : (∏ p ∈ S, (p - 1)) ≤ n :=
      Nat.le_of_dvd hn (Finset.mem_filter.mp hS).2.1
    have hr := Real.rpow_le_rpow_of_nonpos
      (show (0 : ℝ) < ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) by exact_mod_cast hpos)
      (show ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) ≤ n by exact_mod_cast hle)
      (neg_nonpos.mpr hs)
    simpa only [Nat.cast_prod, ← Real.finset_prod_rpow S
      (fun p => ((p - 1 : ℕ) : ℝ)) (fun p _ => Nat.cast_nonneg _) (-s), w] using hr
  calc
    (g n : ℝ) * (n : ℝ) ^ (-s) =
        ∑ _S ∈ admissibleSupports n, (n : ℝ) ^ (-s) := by
      rw [Finset.sum_const, nsmul_eq_mul, g_eq_card_admissibleSupports hn]
    _ ≤ ∑ S ∈ admissibleSupports n, ∏ p ∈ S, w p := Finset.sum_le_sum hpoint
    _ ≤ ∑ S ∈ (shiftedPrimeDivisors n).powerset, ∏ p ∈ S, w p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S _ _
      exact Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ∏ p ∈ shiftedPrimeDivisors n, (1 + w p) := (Finset.prod_one_add _).symm

lemma exists_g_le_rpow_on_smooth (y : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ∈ Nat.smoothNumbers y, (g n : ℝ) ≤ C * (n : ℝ) ^ s := by
  let f : ℕ →* ℝ := {
    toFun := fun n => (n : ℝ) ^ (-s)
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [Nat.cast_mul]
      exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b) }
  have hsmall {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ) ^ (-s)‖ < 1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  let M : ℝ := ∏ p ∈ y.primesBelow, (1 - f p)⁻¹
  have hsum : HasSum (fun d : Nat.smoothNumbers y => f d) M :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hsmall y).2
  have hind : HasSum ((Nat.smoothNumbers y).indicator f) M :=
    hasSum_subtype_iff_indicator.mp hsum
  refine ⟨Real.exp M, Real.exp_pos _, ?_⟩
  intro n hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn.1
  let P := shiftedPrimeDivisors n
  let D := P.image (fun p => p - 1)
  have hD (d : ℕ) (hd : d ∈ D) : d ∈ Nat.smoothNumbers y := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mem_smoothNumbers_of_dvd hn (Finset.mem_filter.mp hp).2.2
  have hpredinj : Set.InjOn (fun p : ℕ => p - 1) (↑P : Set ℕ) := by
    intro p hp q hq heq
    change p ∈ shiftedPrimeDivisors n at hp
    change q ∈ shiftedPrimeDivisors n at hq
    have hp2 := (Finset.mem_filter.mp hp).2.1.two_le
    have hq2 := (Finset.mem_filter.mp hq).2.1.two_le
    change p - 1 = q - 1 at heq
    omega
  have hsumle : ∑ p ∈ P, f (p - 1) ≤ M := calc
    (∑ p ∈ P, f (p - 1)) = ∑ d ∈ D, f d := (Finset.sum_image hpredinj).symm
    _ = ∑ d ∈ D, (Nat.smoothNumbers y).indicator f d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (Set.indicator_of_mem (hD d hd) f).symm
    _ ≤ ∑' d, (Nat.smoothNumbers y).indicator f d :=
      Summable.sum_le_tsum _ (fun d _ => Set.indicator_nonneg
        (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) _) hind.summable
    _ = M := hind.tsum_eq
  have hprodle : (∏ p ∈ P, (1 + f (p - 1))) ≤ Real.exp M := calc
    (∏ p ∈ P, (1 + f (p - 1))) ≤ ∏ p ∈ P, Real.exp (f (p - 1)) := by
      apply Finset.prod_le_prod
      · intro p _
        exact add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (f (p - 1))
    _ = Real.exp (∑ p ∈ P, f (p - 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp M := Real.exp_le_exp.mpr hsumle
  have hweighted : (g n : ℝ) * (n : ℝ) ^ (-s) ≤ Real.exp M :=
    (g_mul_rpow_neg_le_support_product hnpos hs.le).trans hprodle
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  calc
    (g n : ℝ) = ((g n : ℝ) * (n : ℝ) ^ (-s)) * (n : ℝ) ^ s := by
      rw [mul_assoc, ← Real.rpow_add hnR, neg_add_cancel, Real.rpow_zero, mul_one]
    _ ≤ Real.exp M * (n : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hweighted (Real.rpow_nonneg hnR.le _)

/-- Restricting the output to any fixed set of allowed prime factors yields subpower multiplicity. -/
lemma finite_g_gt_rpow_on_smooth (y : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    {n : ℕ | n ∈ Nat.smoothNumbers y ∧ (g n : ℝ) > (n : ℝ) ^ δ}.Finite := by
  obtain ⟨C, _, hC⟩ := exists_g_le_rpow_on_smooth y (δ / 2) (half_pos hδ)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,
      n ∈ Nat.smoothNumbers y → (g n : ℝ) ≤ (n : ℝ) ^ δ := by
    filter_upwards [hlim.eventually (eventually_ge_atTop C), eventually_ge_atTop 1]
      with n hnC hn hnsm
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      (g n : ℝ) ≤ C * (n : ℝ) ^ (δ / 2) := hC n hnsm
      _ ≤ (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (δ / 2) :=
        mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hnR.le _)
      _ = (n : ℝ) ^ δ := by rw [← Real.rpow_add hnR]; congr 1; ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra h
  exact (not_lt_of_ge (hN n (Nat.le_of_not_gt h) hn.1)) hn.2

/-- An upper bound whose only arithmetic parameter is an Euler product over the output's primes. -/
lemma g_le_rpow_mul_exp_primeFactors (n : ℕ) (hnpos : 0 < n) (s : ℝ) (hs : 0 < s) :
    (g n : ℝ) ≤
      Real.exp (∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-s))⁻¹) * (n : ℝ) ^ s := by
  let f : ℕ →* ℝ := {
    toFun := fun n => (n : ℝ) ^ (-s)
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [Nat.cast_mul]
      exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b) }
  have hsmall {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ) ^ (-s)‖ < 1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  let M : ℝ := ∏ p ∈ n.primeFactors, (1 - f p)⁻¹
  have hfilter : n.primeFactors.filter Nat.Prime = n.primeFactors :=
    Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hsum : HasSum (fun d : Nat.factoredNumbers n.primeFactors => f d) M := by
    simpa only [hfilter] using
      (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
        hsmall n.primeFactors).2
  have hind : HasSum ((Nat.factoredNumbers n.primeFactors).indicator f) M :=
    hasSum_subtype_iff_indicator.mp hsum
  have hn : n ∈ Nat.factoredNumbers n.primeFactors :=
    Nat.mem_factoredNumbers_of_primeFactors_subset hnpos.ne' (Finset.Subset.refl _)
  let P := shiftedPrimeDivisors n
  let D := P.image (fun p => p - 1)
  have hD (d : ℕ) (hd : d ∈ D) : d ∈ Nat.factoredNumbers n.primeFactors := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mem_factoredNumbers_of_dvd hn (Finset.mem_filter.mp hp).2.2
  have hpredinj : Set.InjOn (fun p : ℕ => p - 1) (↑P : Set ℕ) := by
    intro p hp q hq heq
    change p ∈ shiftedPrimeDivisors n at hp
    change q ∈ shiftedPrimeDivisors n at hq
    have hp2 := (Finset.mem_filter.mp hp).2.1.two_le
    have hq2 := (Finset.mem_filter.mp hq).2.1.two_le
    change p - 1 = q - 1 at heq
    omega
  have hsumle : ∑ p ∈ P, f (p - 1) ≤ M := calc
    (∑ p ∈ P, f (p - 1)) = ∑ d ∈ D, f d := (Finset.sum_image hpredinj).symm
    _ = ∑ d ∈ D, (Nat.factoredNumbers n.primeFactors).indicator f d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (Set.indicator_of_mem (hD d hd) f).symm
    _ ≤ ∑' d, (Nat.factoredNumbers n.primeFactors).indicator f d :=
      Summable.sum_le_tsum _ (fun d _ => Set.indicator_nonneg
        (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) _) hind.summable
    _ = M := hind.tsum_eq
  have hprodle : (∏ p ∈ P, (1 + f (p - 1))) ≤ Real.exp M := calc
    (∏ p ∈ P, (1 + f (p - 1))) ≤ ∏ p ∈ P, Real.exp (f (p - 1)) := by
      apply Finset.prod_le_prod
      · intro p _
        exact add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (f (p - 1))
    _ = Real.exp (∑ p ∈ P, f (p - 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp M := Real.exp_le_exp.mpr hsumle
  have hweighted : (g n : ℝ) * (n : ℝ) ^ (-s) ≤ Real.exp M :=
    (g_mul_rpow_neg_le_support_product hnpos hs.le).trans hprodle
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  calc
    (g n : ℝ) = ((g n : ℝ) * (n : ℝ) ^ (-s)) * (n : ℝ) ^ s := by
      rw [mul_assoc, ← Real.rpow_add hnR, neg_add_cancel, Real.rpow_zero, mul_one]
    _ ≤ Real.exp M * (n : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hweighted (Real.rpow_nonneg hnR.le _)

lemma g_le_rpow_of_primeFactors_card_le (r n : ℕ) (hn : 0 < n)
    (hr : n.primeFactors.card ≤ r) (s : ℝ) (hs : 0 < s) :
    (g n : ℝ) ≤ Real.exp (((1 - (2 : ℝ) ^ (-s))⁻¹) ^ r) * (n : ℝ) ^ s := by
  let c : ℝ := (1 - (2 : ℝ) ^ (-s))⁻¹
  have htwo : (2 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
  have hden : 0 < 1 - (2 : ℝ) ^ (-s) := sub_pos.mpr htwo
  have hc : 1 ≤ c := (one_le_inv₀ hden).mpr (by
    have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
    linarith)
  have hpbound (p : ℕ) (hp : p ∈ n.primeFactors) :
      (1 - (p : ℝ) ^ (-s))⁻¹ ≤ c := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hpow : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (neg_nonpos.mpr hs.le)
    exact (inv_le_inv₀ (by linarith) hden).mpr (by linarith)
  have hprod : (∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-s))⁻¹) ≤ c ^ r := calc
    (∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-s))⁻¹) ≤ c ^ n.primeFactors.card :=
      calc
        _ ≤ ∏ _p ∈ n.primeFactors, c := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp1 : (1 : ℝ) < p := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
            exact inv_nonneg.mpr (sub_nonneg.mpr
              (Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos hs)).le)
          · exact hpbound
        _ = c ^ n.primeFactors.card := Finset.prod_const c
    _ ≤ c ^ r := pow_le_pow_right₀ hc hr
  exact (g_le_rpow_mul_exp_primeFactors n hn s hs).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hprod)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- Uniformly over all choices of at most `r` prime factors, `g` has subpower growth. -/
lemma finite_g_gt_rpow_of_primeFactors_card_le (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    {n : ℕ | n.primeFactors.card ≤ r ∧ (g n : ℝ) > (n : ℝ) ^ δ}.Finite := by
  let C : ℝ := Real.exp (((1 - (2 : ℝ) ^ (-(δ / 2)))⁻¹) ^ r)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,
      n.primeFactors.card ≤ r → (g n : ℝ) ≤ (n : ℝ) ^ δ := by
    filter_upwards [hlim.eventually (eventually_ge_atTop C), eventually_ge_atTop 1]
      with n hnC hn hr
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    calc
      (g n : ℝ) ≤ C * (n : ℝ) ^ (δ / 2) :=
        g_le_rpow_of_primeFactors_card_le r n hnpos hr (δ / 2) (half_pos hδ)
      _ ≤ (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (δ / 2) :=
        mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hnR.le _)
      _ = (n : ℝ) ^ δ := by rw [← Real.rpow_add hnR]; congr 1; ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra h
  exact (not_lt_of_ge (hN n (Nat.le_of_not_gt h) hn.1)) hn.2

/-- No sequence of powers of a fixed base greater than one can witness a
positive-power lower bound for the totient multiplicity infinitely often. -/
lemma finite_g_pow_gt_rpow (b : ℕ) (hb : 2 ≤ b) (δ : ℝ) (hδ : 0 < δ) :
    {k : ℕ | (g (b ^ k) : ℝ) > ((b ^ k : ℕ) : ℝ) ^ δ}.Finite := by
  have hfin := finite_g_gt_rpow_of_primeFactors_card_le b.primeFactors.card δ hδ
  have hpre := Set.Finite.preimage (Nat.pow_right_injective hb).injOn hfin
  apply hpre.subset
  intro k hk
  change (b ^ k).primeFactors.card ≤ b.primeFactors.card ∧
    (g (b ^ k) : ℝ) > ((b ^ k : ℕ) : ℝ) ^ δ
  refine ⟨?_, hk⟩
  by_cases hk0 : k = 0
  · simp [hk0]
  · rw [Nat.primeFactors_pow b hk0]

/-- Selecting one point in each of `k` disjoint blocks of size `r` gives
`r^k` distinct subsets of cardinality `k`. -/
lemma pow_le_choose_mul (r k : ℕ) : r ^ k ≤ (k * r).choose k := by
  classical
  let graph : (Fin k → Fin r) → Finset (Fin k × Fin r) :=
    fun f => Finset.univ.image (fun i => (i, f i))
  have hgraph (f : Fin k → Fin r) :
      graph f ∈ (Finset.univ : Finset (Fin k × Fin r)).powersetCard k := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    simp only [graph, Finset.card_image_of_injective _ (fun i j h => Prod.mk.inj h |>.1),
      Finset.card_univ, Fintype.card_fin]
  have hinj : Function.Injective graph := by
    intro f g h
    funext i
    have hi : (i, f i) ∈ graph g := by
      rw [← h]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact (congrArg Prod.snd hj).symm
  have hcard := Finset.card_le_card (show Finset.univ.image graph ⊆
      (Finset.univ : Finset (Fin k × Fin r)).powersetCard k from by
    intro S hS
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hS
    exact hgraph f)
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Finset.card_powersetCard,
    Fintype.card_prod] using hcard

lemma two_pow_mul_le_choose (A k N : ℕ) (hN : k * 2 ^ A ≤ N) :
    2 ^ (A * k) ≤ N.choose k := by
  rw [pow_mul]
  exact (pow_le_choose_mul (2 ^ A) k).trans (Nat.choose_le_choose k hN)

/-- An explicit parameter choice for the smooth-part pigeonhole argument. -/
lemma smooth_prime_counting_margin (t L : ℕ) (ht : 4 ≤ t) (hL : 3 ≤ L)
    (htL : t ≤ L) :
    (t * L * 2 ^ (2 * L) + 1) ^ (2 ^ L) *
        2 ^ ((t - 4) * L * 2 ^ (2 * L)) <
      (2 ^ ((t - 1) * L)).choose (2 ^ (2 * L)) := by
  let k := 2 ^ (2 * L)
  have hL0 : 0 < L := by omega
  have hk : 0 < k := by dsimp [k]; positivity
  have hLp : L ≤ 2 ^ L := Nat.lt_two_pow_self.le
  have htp : t ≤ 2 ^ L := htL.trans hLp
  have hsmall : t * L * k ≤ 2 ^ (4 * L) := by
    calc
      t * L * k ≤ 2 ^ L * 2 ^ L * 2 ^ (2 * L) :=
        Nat.mul_le_mul_right k (Nat.mul_le_mul htp hLp)
      _ = 2 ^ (4 * L) := by rw [← pow_add, ← pow_add]; congr 1; ring
  have hbase : t * L * k + 1 ≤ 2 ^ (5 * L) := by
    calc
      t * L * k + 1 ≤ 2 ^ (4 * L) + 2 ^ (4 * L) :=
        Nat.add_le_add hsmall (Nat.one_le_pow _ _ (by decide))
      _ = 2 ^ (4 * L + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ (5 * L) := Nat.pow_le_pow_right (by decide) (by omega)
  have h5 : 5 < 2 ^ L := by
    have hh : 2 ^ 3 ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL
    omega
  have hdim : (t * L * k + 1) ^ (2 ^ L) < 2 ^ (L * k) := by
    calc
      (t * L * k + 1) ^ (2 ^ L) ≤ (2 ^ (5 * L)) ^ (2 ^ L) :=
        Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((5 * L) * 2 ^ L) := (pow_mul _ _ _).symm
      _ < 2 ^ (L * k) := by
        apply Nat.pow_lt_pow_right (by decide)
        dsimp [k]
        rw [show 2 * L = L + L by omega, pow_add]
        nlinarith [Nat.mul_lt_mul_of_pos_left h5 (Nat.mul_pos hL0
          (show 0 < 2 ^ L by positivity))]
  have hcount : 2 ^ (((t - 3) * L) * k) ≤
      (2 ^ ((t - 1) * L)).choose k := by
    apply two_pow_mul_le_choose
    dsimp [k]
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have ht3 : t - 3 + 2 = t - 1 := by omega
    nlinarith
  calc
    (t * L * k + 1) ^ (2 ^ L) * 2 ^ ((t - 4) * L * k) <
        2 ^ (L * k) * 2 ^ ((t - 4) * L * k) :=
      Nat.mul_lt_mul_of_pos_right hdim (by positivity)
    _ = 2 ^ (((t - 3) * L) * k) := by
      rw [← pow_add]
      congr 1
      have ht4 : t - 4 + 1 = t - 3 := by omega
      rw [← ht4]
      ring
    _ ≤ _ := hcount

/-- A finite, fully quantitative consequence of a supply of smooth shifted primes. -/
lemma large_g_of_dyadic_smooth_primes (t L : ℕ) (ht : 4 ≤ t) (hL : 3 ≤ L)
    (htL : t ≤ L) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
      p - 1 ∈ Nat.smoothNumbers (2 ^ L))
    (hcard : 2 ^ ((t - 1) * L) ≤ P.card) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 2 ^ (t * L * 2 ^ (2 * L)) ∧
      (2 ^ ((t - 4) * L * 2 ^ (2 * L)) : ℝ) < (g n : ℝ) := by
  apply large_g_of_smooth_shifted_primes P (t * L) (2 ^ L) (2 ^ (2 * L)) _
    (by positivity) hP
  exact_mod_cast (smooth_prime_counting_margin t L ht hL htL).trans_le
    (Nat.choose_le_choose (2 ^ (2 * L)) hcard)

/-- An explicit smooth-shifted-prime density hypothesis sufficient for the
full conjecture. The hypothesis is not asserted here. -/
lemma erdos_821_of_dyadic_smooth_prime_density
    (H : ∀ t : ℕ, 5 ≤ t → ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧
      ∃ P : Finset ℕ,
        (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
          p - 1 ∈ Nat.smoothNumbers (2 ^ L)) ∧
        2 ^ ((t - 1) * L) ≤ P.card) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  intro ε hε
  by_cases hεone : 1 ≤ ε
  · exact erdos_821_of_one_le hεone
  have hεlt : ε < 1 := lt_of_not_ge hεone
  obtain ⟨t, ht⟩ := exists_nat_gt (4 / ε + 5)
  have hdiv : 0 < 4 / ε := div_pos (by norm_num) hε
  have ht5 : 5 ≤ t := by exact_mod_cast (show (5 : ℝ) ≤ t by linarith)
  have htep : 4 < (t : ℝ) * ε := (div_lt_iff₀ hε).mp (by linarith)
  have hscale : (t : ℝ) * (1 - ε) ≤ t - 4 := by nlinarith
  apply Set.infinite_of_forall_exists_gt
  intro N
  let C := (Finset.range (N + 1)).sup g
  obtain ⟨L, hLM, P, hP, hcard⟩ := H t ht5 (max 3 (max t C))
  have hL : 3 ≤ L := (le_max_left _ _).trans hLM
  have htL : t ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hCL : C ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLM)
  let k := 2 ^ (2 * L)
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨n, hn, hnle, hg⟩ := large_g_of_dyadic_smooth_primes t L (by omega)
    hL htL P hP hcard
  have hLB : L ≤ (t - 4) * L * k := by
    calc
      L ≤ L * ((t - 4) * k) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hk)
      _ = (t - 4) * L * k := by ring
  have hCB : (C : ℝ) ≤ (2 : ℝ) ^ ((t - 4) * L * k) := by
    exact_mod_cast hCL.trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by decide) hLB))
  have hexp : ((t * L * k : ℕ) : ℝ) * (1 - ε) ≤
      (((t - 4) * L * k : ℕ) : ℝ) := by
    push_cast
    rw [Nat.cast_sub (show 4 ≤ t by omega)]
    push_cast
    calc
      (t : ℝ) * L * k * (1 - ε) = ((t : ℝ) * (1 - ε)) * ((L : ℝ) * k) := by ring
      _ ≤ ((t : ℝ) - 4) * ((L : ℝ) * k) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = _ := by ring
  have hpow : (n : ℝ) ^ (1 - ε) ≤ (2 : ℝ) ^ ((t - 4) * L * k) := by
    calc
      (n : ℝ) ^ (1 - ε) ≤ ((2 : ℝ) ^ (t * L * k)) ^ (1 - ε) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnle) (by linarith)
      _ = (2 : ℝ) ^ (((t * L * k : ℕ) : ℝ) * (1 - ε)) :=
        (Real.rpow_natCast_mul (by norm_num) _ _).symm
      _ ≤ (2 : ℝ) ^ ((((t - 4) * L * k : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = _ := Real.rpow_natCast _ _
  refine ⟨n, hpow.trans_lt hg, ?_⟩
  by_contra h
  have hnmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hgC : (g n : ℝ) ≤ C := by exact_mod_cast (Finset.le_sup (f := g) hnmem)
  exact (not_lt_of_ge (hgC.trans hCB)) hg

/-- A weighted union bound for integers having a specified relatively large divisor.
No primality assumption is needed in this combinatorial estimate. -/
lemma rough_divisor_weight_sum (D Q : Finset ℕ) (k : ℕ) (s u : ℝ)
    (hsu : s ≤ u) (hu : 1 < u)
    (hD : ∀ d ∈ D, 0 < d)
    (hQ : ∀ q ∈ Q, 0 < q)
    (hcover : ∀ d ∈ D, ∃ q ∈ Q, q ∣ d ∧ d ≤ q ^ k) :
    (∑ d ∈ D, (d : ℝ) ^ (-s)) ≤
      (∑' a : ℕ, (a : ℝ) ^ (-u)) *
        ∑ q ∈ Q, (q : ℝ) ^ ((k : ℝ) * (u - s) - u) := by
  have hsum : Summable (fun a : ℕ => (a : ℝ) ^ (-u)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hqbound (q : ℕ) (hq : q ∈ Q) :
      (∑ d ∈ D with q ∣ d ∧ d ≤ q ^ k, (d : ℝ) ^ (-s)) ≤
      (q : ℝ) ^ ((k : ℝ) * (u - s) - u) * ∑' a : ℕ, (a : ℝ) ^ (-u) := by
    let E := D.filter (fun d => q ∣ d ∧ d ≤ q ^ k)
    have hqR : (0 : ℝ) < q := by exact_mod_cast hQ q hq
    have hinj : Set.InjOn (fun d : ℕ => d / q) (↑E : Set ℕ) := by
      intro d hd e he h
      have hdq := (Finset.mem_filter.mp hd).2.1
      have heq := (Finset.mem_filter.mp he).2.1
      change d / q = e / q at h
      rw [← Nat.mul_div_cancel' hdq, ← Nat.mul_div_cancel' heq, h]
    have hpoint (d : ℕ) (hd : d ∈ E) :
        (d : ℝ) ^ (-s) ≤ (q : ℝ) ^ ((k : ℝ) * (u - s) - u) *
          ((d / q : ℕ) : ℝ) ^ (-u) := by
      obtain ⟨hdD, hdq, hdk⟩ := Finset.mem_filter.mp hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast hD d hdD
      have hscale : (d : ℝ) ^ (u - s) ≤ (q : ℝ) ^ ((k : ℝ) * (u - s)) := by
        rw [Real.rpow_natCast_mul hqR.le]
        exact Real.rpow_le_rpow hdR.le (by exact_mod_cast hdk) (sub_nonneg.mpr hsu)
      calc
        (d : ℝ) ^ (-s) = (d : ℝ) ^ (u - s) * (d : ℝ) ^ (-u) := by
          rw [← Real.rpow_add hdR]; congr 1; ring
        _ ≤ (q : ℝ) ^ ((k : ℝ) * (u - s)) * (d : ℝ) ^ (-u) :=
          mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hdR.le _)
        _ = (q : ℝ) ^ ((k : ℝ) * (u - s) - u) * ((d / q : ℕ) : ℝ) ^ (-u) := by
          nth_rw 1 [← Nat.mul_div_cancel' hdq]
          rw [Nat.cast_mul, Real.mul_rpow hqR.le (Nat.cast_nonneg _),
            ← mul_assoc, ← Real.rpow_add hqR]
          congr 2
    calc
      (∑ d ∈ E, (d : ℝ) ^ (-s)) ≤
          ∑ d ∈ E, (q : ℝ) ^ ((k : ℝ) * (u - s) - u) * ((d / q : ℕ) : ℝ) ^ (-u) :=
        Finset.sum_le_sum hpoint
      _ = (q : ℝ) ^ ((k : ℝ) * (u - s) - u) *
          ∑ a ∈ E.image (fun d => d / q), (a : ℝ) ^ (-u) := by
        rw [← Finset.mul_sum, Finset.sum_image hinj]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg a) _) hsum)
        (Real.rpow_nonneg hqR.le _)
  calc
    (∑ d ∈ D, (d : ℝ) ^ (-s)) ≤
        ∑ d ∈ D, ∑ q ∈ Q, if q ∣ d ∧ d ≤ q ^ k then (d : ℝ) ^ (-s) else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨q, hq, hqd, hdk⟩ := hcover d hd
      have hsingle := Finset.single_le_sum
        (s := Q) (f := fun q => if q ∣ d ∧ d ≤ q ^ k then (d : ℝ) ^ (-s) else 0)
        (fun q _ => by dsimp only; split_ifs <;> positivity) hq
      simpa only [if_pos (And.intro hqd hdk)] using hsingle
    _ = ∑ q ∈ Q, ∑ d ∈ D with q ∣ d ∧ d ≤ q ^ k, (d : ℝ) ^ (-s) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ q ∈ Q, (q : ℝ) ^ ((k : ℝ) * (u - s) - u) * ∑' a : ℕ, (a : ℝ) ^ (-u) :=
      Finset.sum_le_sum hqbound
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

lemma g_le_rpow_mul_exp_shifted (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s) :
    (g n : ℝ) ≤ Real.exp (∑ p ∈ shiftedPrimeDivisors n,
      ((p - 1 : ℕ) : ℝ) ^ (-s)) * (n : ℝ) ^ s := by
  have hprod : (∏ p ∈ shiftedPrimeDivisors n, (1 + ((p - 1 : ℕ) : ℝ) ^ (-s))) ≤
      Real.exp (∑ p ∈ shiftedPrimeDivisors n, ((p - 1 : ℕ) : ℝ) ^ (-s)) := by
    calc
      _ ≤ ∏ p ∈ shiftedPrimeDivisors n, Real.exp (((p - 1 : ℕ) : ℝ) ^ (-s)) := by
        apply Finset.prod_le_prod
        · intro p _; positivity
        · intro p _; simpa only [add_comm] using Real.add_one_le_exp (((p - 1 : ℕ) : ℝ) ^ (-s))
      _ = _ := (Real.exp_sum _ _).symm
  have hweighted := (g_mul_rpow_neg_le_support_product hn hs).trans hprod
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (g n : ℝ) = ((g n : ℝ) * (n : ℝ) ^ (-s)) * (n : ℝ) ^ s := by
      rw [mul_assoc, ← Real.rpow_add hnR, neg_add_cancel, Real.rpow_zero, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hweighted (Real.rpow_nonneg hnR.le _)

/-- Predecessors of primes whose own prime factors are all at most the
`k`-th root of the predecessor. -/
def smoothShiftedPredecessors (k : ℕ) : Set ℕ :=
  {d | (d + 1).Prime ∧ ∀ q ∈ d.primeFactors, q ^ k ≤ d}

/-- If the smooth shifted-prime contribution is summable, all remaining
contributions can be charged to relatively large prime factors of the output. -/
lemma g_le_of_summable_smooth_shifted (k : ℕ) (s u : ℝ)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : 1 < u)
    (H : Summable ((smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s))))
    (n : ℕ) (hn : 0 < n) :
    (g n : ℝ) ≤ (n : ℝ) ^ s * Real.exp
      ((∑' d : ℕ, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d) +
        (∑' a : ℕ, (a : ℝ) ^ (-u)) *
          ∑ q ∈ n.primeFactors, (q : ℝ) ^ ((k : ℝ) * (u - s) - u)) := by
  classical
  let P := shiftedPrimeDivisors n
  let D := P.image (fun p => p - 1)
  have hD (d : ℕ) (hd : d ∈ D) : 0 < d ∧ (d + 1).Prime ∧ d ∣ n := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨_, hpprime, hpdvd⟩ := Finset.mem_filter.mp hp
    refine ⟨Nat.sub_pos_of_lt hpprime.one_lt, ?_, hpdvd⟩
    simpa only [Nat.sub_add_cancel hpprime.one_lt.le] using hpprime
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑P : Set ℕ) := by
    intro p hp q hq h
    change p ∈ shiftedPrimeDivisors n at hp
    change q ∈ shiftedPrimeDivisors n at hq
    have hp2 := (Finset.mem_filter.mp hp).2.1.two_le
    have hq2 := (Finset.mem_filter.mp hq).2.1.two_le
    change p - 1 = q - 1 at h
    omega
  let E := D.filter (fun d => d ∉ smoothShiftedPredecessors k)
  have hrough := rough_divisor_weight_sum E n.primeFactors k s u hsu hu
    (fun d hd => (hD d (Finset.mem_filter.mp hd).1).1)
    (fun q hq => Nat.pos_of_mem_primeFactors hq) (by
      intro d hd
      obtain ⟨hdD, hdns⟩ := Finset.mem_filter.mp hd
      have hdp := (hD d hdD).2.1
      have hnot : ¬∀ q ∈ d.primeFactors, q ^ k ≤ d := fun h => hdns ⟨hdp, h⟩
      push_neg at hnot
      obtain ⟨q, hq, hqd⟩ := hnot
      refine ⟨q, ?_, Nat.dvd_of_mem_primeFactors hq, hqd.le⟩
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
        (Nat.dvd_of_mem_primeFactors hq).trans (hD d hdD).2.2, hn.ne'⟩)
  have hsmooth : (∑ d ∈ D with d ∈ smoothShiftedPredecessors k, (d : ℝ) ^ (-s)) ≤
      ∑' d : ℕ, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d := by
    calc
      _ = ∑ d ∈ D, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d := by
        simp only [Finset.sum_filter, Set.indicator_apply]
      _ ≤ _ := Summable.sum_le_tsum _ (fun d _ => Set.indicator_nonneg
        (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) _) H
  have htotal : (∑ p ∈ P, ((p - 1 : ℕ) : ℝ) ^ (-s)) ≤
      (∑' d : ℕ, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d) +
        (∑' a : ℕ, (a : ℝ) ^ (-u)) *
          ∑ q ∈ n.primeFactors, (q : ℝ) ^ ((k : ℝ) * (u - s) - u) := by
    rw [← Finset.sum_image (f := fun d : ℕ => (d : ℝ) ^ (-s)) hinj]
    change (∑ d ∈ D, (d : ℝ) ^ (-s)) ≤ _
    rw [← Finset.sum_filter_add_sum_filter_not D (fun d => d ∈ smoothShiftedPredecessors k)]
    exact add_le_add hsmooth hrough
  calc
    (g n : ℝ) ≤ Real.exp (∑ p ∈ P, ((p - 1 : ℕ) : ℝ) ^ (-s)) * (n : ℝ) ^ s :=
      g_le_rpow_mul_exp_shifted n hn s hs
    _ ≤ Real.exp _ * (n : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htotal) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = _ := mul_comm _ _

/-- Every negative-power weight over the distinct prime factors of an integer
is smaller than an arbitrary positive multiple of its logarithm, up to a constant. -/
lemma exists_sum_primeFactors_rpow_le_log (β C δ : ℝ) (hβ : 0 < β)
    (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      C * (∑ q ∈ n.primeFactors, (q : ℝ) ^ (-β)) ≤ A + δ * Real.log n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun p : ℕ => C * (p : ℝ) ^ (-β)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (mul_pos hδ hlog2)))
  refine ⟨C * K, ?_⟩
  intro n hn
  have hpoint (p : ℕ) (hp : p ∈ n.primeFactors) :
      C * (p : ℝ) ^ (-β) ≤ (if p < K then C else 0) + δ * Real.log p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    by_cases hpK : p < K
    · rw [if_pos hpK]
      have hpow := Real.rpow_le_one_of_one_le_of_nonpos
        (show (1 : ℝ) ≤ p by linarith) (show -β ≤ 0 by linarith)
      have := mul_le_mul_of_nonneg_left hpow hC
      have := mul_nonneg hδ.le (hlog2.le.trans hlogp)
      nlinarith
    · rw [if_neg hpK, zero_add]
      exact (hK p (Nat.le_of_not_gt hpK)).le.trans
        (mul_le_mul_of_nonneg_left hlogp hδ.le)
  have hsmall : (∑ p ∈ n.primeFactors, if p < K then C else 0) ≤ C * K := by
    rw [← Finset.sum_filter]
    have hsub : n.primeFactors.filter (fun p => p < K) ⊆ Finset.range K := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    have hcard : (n.primeFactors.filter (fun p => p < K)).card ≤ K := by
      simpa only [Finset.card_range] using Finset.card_le_card hsub
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (K : ℝ) * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC
      _ = _ := mul_comm _ _
  have hlogsum : (∑ p ∈ n.primeFactors, Real.log (p : ℝ)) ≤ Real.log n := by
    rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne')]
    apply Real.log_le_log
    · exact Finset.prod_pos (fun p hp => by exact_mod_cast Nat.pos_of_mem_primeFactors hp)
    · rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  calc
    C * (∑ q ∈ n.primeFactors, (q : ℝ) ^ (-β)) =
        ∑ q ∈ n.primeFactors, C * (q : ℝ) ^ (-β) := Finset.mul_sum _ _ _
    _ ≤ ∑ q ∈ n.primeFactors, ((if q < K then C else 0) + δ * Real.log q) :=
      Finset.sum_le_sum hpoint
    _ = (∑ q ∈ n.primeFactors, if q < K then C else 0) +
        δ * (∑ q ∈ n.primeFactors, Real.log q) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add hsmall (mul_le_mul_of_nonneg_left hlogsum hδ.le)

/-- Summability of the smooth shifted-prime series forces a power upper bound
for the totient multiplicity. The parameter condition makes the rough contribution
subpower. -/
lemma eventually_g_le_rpow_of_summable_smooth_shifted (k : ℕ) (s u t : ℝ)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : 1 < u) (hst : s < t)
    (hrough : (k : ℝ) * (u - s) - u < 0)
    (H : Summable ((smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)))) :
    ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ) ^ t := by
  let δ := (t - s) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hst)
  let β := u - (k : ℝ) * (u - s)
  have hβ : 0 < β := by dsimp [β]; linarith
  let C := ∑' a : ℕ, (a : ℝ) ^ (-u)
  have hC : 0 ≤ C := tsum_nonneg (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _)
  let M := ∑' d : ℕ, (smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s)) d
  obtain ⟨A, hA⟩ := exists_sum_primeFactors_rpow_le_log β C δ hβ hC hδ
  let K := Real.exp (M + A)
  have hbound (n : ℕ) (hn : 0 < n) : (g n : ℝ) ≤ K * (n : ℝ) ^ (s + δ) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hg := g_le_of_summable_smooth_shifted k s u hs hsu hu H n hn
    have heq : (k : ℝ) * (u - s) - u = -β := by dsimp [β]; ring
    rw [heq] at hg
    have hExp : Real.exp (M + (A + δ * Real.log n)) = K * (n : ℝ) ^ δ := by
      rw [show M + (A + δ * Real.log n) = (M + A) + Real.log n * δ by ring,
        Real.exp_add, ← Real.rpow_def_of_pos hnR δ]
    calc
      (g n : ℝ) ≤ (n : ℝ) ^ s * Real.exp (M + C * ∑ q ∈ n.primeFactors, (q : ℝ) ^ (-β)) := hg
      _ ≤ (n : ℝ) ^ s * Real.exp (M + (A + δ * Real.log n)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (add_le_add le_rfl (hA n hn)))
          (Real.rpow_nonneg hnR.le _)
      _ = _ := by rw [hExp, Real.rpow_add hnR]; ring
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop K), eventually_ge_atTop 1]
    with n hnK hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (g n : ℝ) ≤ K * (n : ℝ) ^ (s + δ) := hbound n (by omega)
    _ ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (s + δ) :=
      mul_le_mul_of_nonneg_right hnK (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ t := by rw [← Real.rpow_add hnR]; congr 1; dsimp [δ]; ring

/-- A necessary condition for the original conjecture: for every `k ≥ 1`,
a Dirichlet series of primes with `k`-th-root-smooth predecessors must diverge
already at an exponent strictly below one. -/
lemma not_summable_smooth_shifted_of_erdos_821
    (H : ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite)
    (k : ℕ) (hk : 1 ≤ k) :
    ¬Summable ((smoothShiftedPredecessors k).indicator
      (fun d : ℕ => (d : ℝ) ^ (-(1 - 1 / (2 * (k : ℝ)))))) := by
  intro hsum
  let e : ℝ := 1 / (2 * (k : ℝ))
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 2 * k := by positivity
  have he : 0 < e := one_div_pos.mpr hden
  have heid : (2 * (k : ℝ)) * e = 1 := mul_one_div_cancel hden.ne'
  have hehalf : e ≤ 1 / 2 := (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hev := eventually_g_le_rpow_of_summable_smooth_shifted k
    (1 - e) (1 + e) (1 - e / 2) (by linarith) (by linarith) (by linarith)
    (by linarith) (by nlinarith) hsum
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hfinite : {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - e / 2)}.Finite := by
    apply (Set.finite_Iio N).subset
    intro n hn
    change n < N
    by_contra h
    exact (not_lt_of_ge (hN n (Nat.le_of_not_gt h))) hn
  exact hfinite.not_infinite (H (e / 2) (half_pos he))

/-- A dyadic counting bound with a power saving gives convergence of the
corresponding weighted series. -/
lemma summable_indicator_rpow_of_dyadic_count (S : Set ℕ) [DecidablePred (fun d => d ∈ S)]
    (t a : ℕ) (s C : ℝ)
    (ht : 1 ≤ t) (hs : 0 ≤ s) (hC : 0 ≤ C) (ha : (a : ℝ) < (t : ℝ) * s)
    (hcount : ∀ L : ℕ, (((Finset.range (2 ^ (t * L))).filter (fun d => d ∈ S)).card : ℝ) ≤
      C * (2 : ℝ) ^ (a * L)) :
    Summable (S.indicator (fun d : ℕ => (d : ℝ) ^ (-s))) := by
  classical
  let f := S.indicator (fun d : ℕ => (d : ℝ) ^ (-s))
  let b : ℕ → ℕ := fun L => 2 ^ (t * L)
  let r : ℝ := (2 : ℝ) ^ ((a : ℝ) - (t : ℝ) * s)
  let c : ℝ := C * (2 : ℝ) ^ a
  have hf : ∀ d, 0 ≤ f d := fun d => Set.indicator_nonneg
    (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc : 0 ≤ c := mul_nonneg hC (by positivity)
  have hgeom : Summable (fun L : ℕ => c * r ^ L) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  have hb (L : ℕ) : 0 < b L := by dsimp [b]; positivity
  have hbmono (L : ℕ) : b L ≤ b (L + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left t (Nat.le_succ L))
  have hblock (L : ℕ) : (∑ d ∈ Finset.Ico (b L) (b (L + 1)), f d) ≤ c * r ^ L := by
    let E := (Finset.Ico (b L) (b (L + 1))).filter (fun d => d ∈ S)
    have hE : (E.card : ℝ) ≤ C * (2 : ℝ) ^ (a * (L + 1)) := by
      apply le_trans ?_ (hcount (L + 1))
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro d hd
      obtain ⟨hdI, hdS⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hdI).2, hdS⟩
    have hbR : (0 : ℝ) < b L := by exact_mod_cast hb L
    calc
      (∑ d ∈ Finset.Ico (b L) (b (L + 1)), f d) = ∑ d ∈ E, (d : ℝ) ^ (-s) := by
        simp only [E, f, Finset.sum_filter, Set.indicator_apply]
      _ ≤ ∑ _d ∈ E, (b L : ℝ) ^ (-s) := by
        apply Finset.sum_le_sum
        intro d hd
        exact Real.rpow_le_rpow_of_nonpos hbR
          (by exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hd).1).1) (neg_nonpos.mpr hs)
      _ = (b L : ℝ) ^ (-s) * E.card := by simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ (b L : ℝ) ^ (-s) * (C * (2 : ℝ) ^ (a * (L + 1))) :=
        mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hbR.le _)
      _ = c * r ^ L := by
        dsimp [b, c, r]
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num),
          ← Real.rpow_natCast (2 : ℝ) (a * (L + 1)),
          ← Real.rpow_mul_natCast (by norm_num)]
        calc
          _ = C * ((2 : ℝ) ^ (((t * L : ℕ) : ℝ) * (-s)) *
            (2 : ℝ) ^ ((a * (L + 1) : ℕ) : ℝ)) := by ring
          _ = C * (2 : ℝ) ^ (((t * L : ℕ) : ℝ) * (-s) + ((a * (L + 1) : ℕ) : ℝ)) := by
            rw [Real.rpow_add (by norm_num)]
          _ = C * (2 : ℝ) ^ ((a : ℝ) + ((a : ℝ) - (t : ℝ) * s) * (L : ℝ)) := by
            congr 2
            push_cast
            ring
          _ = _ := by rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; ring
  have hpartial (L : ℕ) : (∑ d ∈ Finset.range (b L), f d) ≤
      (∑ d ∈ Finset.range (b 0), f d) + ∑ j ∈ Finset.range L, c * r ^ j := by
    induction L with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
    | succ L ih =>
      rw [← Finset.sum_range_add_sum_Ico f (hbmono L), Finset.sum_range_succ]
      exact (add_le_add ih (hblock L)).trans_eq (add_assoc _ _ _)
  apply summable_of_sum_range_le hf
    (c := (∑ d ∈ Finset.range (b 0), f d) + ∑' j : ℕ, c * r ^ j)
  intro N
  have hNb : N ≤ b N := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega)))
  calc
    (∑ d ∈ Finset.range N, f d) ≤ ∑ d ∈ Finset.range (b N), f d :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNb) (fun d _ _ => hf d)
    _ ≤ _ := (hpartial N).trans (add_le_add le_rfl
      (Summable.sum_le_tsum _ (fun j _ => mul_nonneg hc (pow_nonneg hr0 _)) hgeom))

lemma exists_large_dyadic_count_of_not_summable (S : Set ℕ)
    [DecidablePred (fun d => d ∈ S)] (t a : ℕ) (s : ℝ)
    (ht : 1 ≤ t) (hs : 0 ≤ s) (ha : (a : ℝ) < (t : ℝ) * s)
    (H : ¬Summable (S.indicator (fun d : ℕ => (d : ℝ) ^ (-s)))) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ 2 ^ (a * L) ≤
      ((Finset.range (2 ^ (t * L))).filter (fun d => d ∈ S)).card := by
  by_contra h
  push_neg at h
  apply H
  let C : ℝ := (2 : ℝ) ^ (t * M)
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  apply summable_indicator_rpow_of_dyadic_count S t a s C ht hs (by linarith) ha
  intro L
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (a * L) := one_le_pow₀ (by norm_num)
  by_cases hML : M ≤ L
  · have hcard : ((Finset.range (2 ^ (t * L))).filter (fun d => d ∈ S)).card ≤
        2 ^ (a * L) := (h L hML).le
    calc
      _ ≤ (2 : ℝ) ^ (a * L) := by exact_mod_cast hcard
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hC
  · have hcard := (Finset.card_filter_le (Finset.range (2 ^ (t * L))) (fun d => d ∈ S)).trans
        (show (Finset.range (2 ^ (t * L))).card ≤ 2 ^ (t * M) by
          rw [Finset.card_range]
          exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left t (by omega)))
    calc
      _ ≤ C := by dsimp [C]; exact_mod_cast hcard
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hpow

/-- Divergence of the smooth shifted-prime series at each root scale supplies
exactly the dyadic prime families used in the quantitative lower bound. -/
lemma dyadic_density_of_not_summable_smooth_shifted
    (H : ∀ k : ℕ, 1 ≤ k → ¬Summable ((smoothShiftedPredecessors k).indicator
      (fun d : ℕ => (d : ℝ) ^ (-(1 - 1 / (2 * (k : ℝ))))))) :
    ∀ t : ℕ, 5 ≤ t → ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧
      ∃ P : Finset ℕ,
        (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
          p - 1 ∈ Nat.smoothNumbers (2 ^ L)) ∧
        2 ^ ((t - 1) * L) ≤ P.card := by
  classical
  intro t ht M
  have htR : (5 : ℝ) ≤ t := by exact_mod_cast ht
  have hden : (0 : ℝ) < 2 * t := by positivity
  let e : ℝ := 1 / (2 * (t : ℝ))
  have he : 0 < e := one_div_pos.mpr hden
  have heid : (2 * (t : ℝ)) * e = 1 := mul_one_div_cancel hden.ne'
  have hehalf : e ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs : 0 ≤ 1 - e := by linarith
  have ha : ((t - 1 : ℕ) : ℝ) < (t : ℝ) * (1 - e) := by
    rw [Nat.cast_sub (show 1 ≤ t by omega), Nat.cast_one]
    nlinarith
  obtain ⟨L, hLM, hcount⟩ := exists_large_dyadic_count_of_not_summable
    (smoothShiftedPredecessors t) t (t - 1) (1 - e) (by omega) hs ha (H t (by omega)) M
  let D := (Finset.range (2 ^ (t * L))).filter (fun d => d ∈ smoothShiftedPredecessors t)
  let P := D.image (fun d => d + 1)
  refine ⟨L, hLM, P, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hdlt, hdS⟩ := Finset.mem_filter.mp hd
    have hdprime : (d + 1).Prime := hdS.1
    have hdlt' : d < 2 ^ (t * L) := Finset.mem_range.mp hdlt
    refine ⟨hdprime, by omega, ?_⟩
    simp only [Nat.add_sub_cancel]
    apply Nat.mem_smoothNumbers'.mpr
    intro q hq hqd
    have hd0 : d ≠ 0 := by intro h; subst d; exact Nat.not_prime_one hdprime
    have hqmem : q ∈ d.primeFactors := hq.mem_primeFactors hqd hd0
    have hqpow : q ^ t < (2 ^ L) ^ t := by
      calc
        q ^ t ≤ d := hdS.2 q hqmem
        _ < 2 ^ (t * L) := hdlt'
        _ = (2 ^ L) ^ t := by rw [← pow_mul]; congr 1; ring
    exact (Nat.pow_lt_pow_iff_left (by omega : t ≠ 0)).mp hqpow
  · have hcard : P.card = D.card := Finset.card_image_of_injective _
      (fun a b hab => Nat.add_right_cancel hab)
    rw [hcard]
    exact hcount

/-- A series-theoretic characterization of the full conjecture. Neither side
of this equivalence is asserted without a hypothesis. -/
lemma erdos_821_iff_smooth_shifted_nonsummable :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
      ∀ k : ℕ, 1 ≤ k → ¬Summable ((smoothShiftedPredecessors k).indicator
        (fun d : ℕ => (d : ℝ) ^ (-(1 - 1 / (2 * (k : ℝ)))))) := by
  constructor
  · intro H k hk
    exact not_summable_smooth_shifted_of_erdos_821 H k hk
  · intro H
    exact erdos_821_of_dyadic_smooth_prime_density (dyadic_density_of_not_summable_smooth_shifted H)

/-- A second explicit parameter choice, suited to a fixed smoothness exponent
close to one. -/
lemma weak_smooth_prime_counting_margin (t L : ℕ) (ht : 6 ≤ t) (hL : 3 ≤ L)
    (htL : t ≤ L) :
    (t * L * 2 ^ ((t - 4) * L) + 1) ^ (2 ^ ((t - 5) * L)) *
        2 ^ (2 * L * 2 ^ ((t - 4) * L)) <
      (2 ^ ((t - 1) * L)).choose (2 ^ ((t - 4) * L)) := by
  let k := 2 ^ ((t - 4) * L)
  let y := 2 ^ ((t - 5) * L)
  have hL0 : 0 < L := by omega
  have hk : 0 < k := by dsimp [k]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hLp : L ≤ 2 ^ L := Nat.lt_two_pow_self.le
  have htp : t ≤ 2 ^ L := htL.trans hLp
  have hsmall : t * L * k ≤ 2 ^ ((t - 2) * L) := by
    calc
      t * L * k ≤ 2 ^ L * 2 ^ L * 2 ^ ((t - 4) * L) :=
        Nat.mul_le_mul_right k (Nat.mul_le_mul htp hLp)
      _ = 2 ^ ((t - 2) * L) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have ht4 : t - 4 + 2 = t - 2 := by omega
        nlinarith
  have hbase : t * L * k + 1 ≤ 2 ^ ((t - 1) * L) := by
    calc
      t * L * k + 1 ≤ 2 ^ ((t - 2) * L) + 2 ^ ((t - 2) * L) :=
        Nat.add_le_add hsmall (Nat.one_le_pow _ _ (by decide))
      _ = 2 ^ ((t - 2) * L + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ ((t - 1) * L) := Nat.pow_le_pow_right (by decide) (by
        have ht2 : t - 2 + 1 = t - 1 := by omega
        nlinarith)
  have hky : k = 2 ^ L * y := by
    dsimp [k, y]
    rw [← pow_add]
    congr 1
    have ht5 : t - 5 + 1 = t - 4 := by omega
    nlinarith
  have hdim : (t * L * k + 1) ^ y < 2 ^ (L * k) := by
    calc
      (t * L * k + 1) ^ y ≤ (2 ^ ((t - 1) * L)) ^ y := Nat.pow_le_pow_left hbase _
      _ = 2 ^ (((t - 1) * L) * y) := (pow_mul _ _ _).symm
      _ < 2 ^ (L * k) := by
        apply Nat.pow_lt_pow_right (by decide)
        rw [hky]
        have hgap : t - 1 < 2 ^ L := by omega
        have h := Nat.mul_lt_mul_of_pos_right hgap (Nat.mul_pos hL0 hy)
        nlinarith
  have hcount : 2 ^ ((3 * L) * k) ≤ (2 ^ ((t - 1) * L)).choose k := by
    apply two_pow_mul_le_choose
    dsimp [k]
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have ht4 : t - 4 + 3 = t - 1 := by omega
    nlinarith
  calc
    (t * L * k + 1) ^ y * 2 ^ (2 * L * k) < 2 ^ (L * k) * 2 ^ (2 * L * k) :=
      Nat.mul_lt_mul_of_pos_right hdim (by positivity)
    _ = 2 ^ ((3 * L) * k) := by rw [← pow_add]; congr 1; ring
    _ ≤ _ := hcount

lemma large_g_of_weak_dyadic_smooth_primes (t L : ℕ) (ht : 6 ≤ t) (hL : 3 ≤ L)
    (htL : t ≤ L) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
      p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L)))
    (hcard : 2 ^ ((t - 1) * L) ≤ P.card) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 2 ^ (t * L * 2 ^ ((t - 4) * L)) ∧
      (2 ^ (2 * L * 2 ^ ((t - 4) * L)) : ℝ) < (g n : ℝ) := by
  apply large_g_of_smooth_shifted_primes P (t * L) (2 ^ ((t - 5) * L))
    (2 ^ ((t - 4) * L)) _ (by positivity) hP
  exact_mod_cast (weak_smooth_prime_counting_margin t L ht hL htL).trans_le
    (Nat.choose_le_choose (2 ^ ((t - 4) * L)) hcard)

lemma infinite_g_gt_fixed_power_of_weak_density (t : ℕ) (ht : 6 ≤ t)
    (H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (2 / (t : ℝ))}.Infinite := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hδ : 0 < 2 / (t : ℝ) := div_pos (by norm_num) htR
  apply Set.infinite_of_forall_exists_gt
  intro N
  let C := (Finset.range (N + 1)).sup g
  obtain ⟨L, hLM, P, hP, hcard⟩ := H (max 3 (max t C))
  have hL : 3 ≤ L := (le_max_left _ _).trans hLM
  have htL : t ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hCL : C ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLM)
  let k := 2 ^ ((t - 4) * L)
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨n, hn, hnle, hg⟩ := large_g_of_weak_dyadic_smooth_primes t L ht hL htL P hP hcard
  have hCB : (C : ℝ) ≤ (2 : ℝ) ^ (2 * L * k) := by
    have hLB : L ≤ 2 * L * k := by nlinarith
    exact_mod_cast hCL.trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by decide) hLB))
  have hexp : ((t * L * k : ℕ) : ℝ) * (2 / (t : ℝ)) =
      ((2 * L * k : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hpow : (n : ℝ) ^ (2 / (t : ℝ)) ≤ (2 : ℝ) ^ (2 * L * k) := by
    calc
      (n : ℝ) ^ (2 / (t : ℝ)) ≤ ((2 : ℝ) ^ (t * L * k)) ^ (2 / (t : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnle) hδ.le
      _ = (2 : ℝ) ^ (((t * L * k : ℕ) : ℝ) * (2 / (t : ℝ))) :=
        (Real.rpow_natCast_mul (by norm_num) _ _).symm
      _ = _ := by rw [hexp, Real.rpow_natCast]
  refine ⟨n, hpow.trans_lt hg, ?_⟩
  by_contra h
  have hnmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hgC : (g n : ℝ) ≤ C := by exact_mod_cast (Finset.le_sup (f := g) hnmem)
  exact (not_lt_of_ge (hgC.trans hCB)) hg

#print axioms infinite_g_gt_fixed_power_of_weak_density
#print axioms large_g_of_weak_dyadic_smooth_primes
#print axioms erdos_821_iff_smooth_shifted_nonsummable
#print axioms summable_indicator_rpow_of_dyadic_count
#print axioms not_summable_smooth_shifted_of_erdos_821
#print axioms eventually_g_le_rpow_of_summable_smooth_shifted
#print axioms exists_sum_primeFactors_rpow_le_log
#print axioms g_le_of_summable_smooth_shifted
#print axioms rough_divisor_weight_sum
#print axioms g_le_rpow_mul_exp_shifted
#print axioms erdos_821_of_dyadic_smooth_prime_density
#print axioms large_g_of_dyadic_smooth_primes
#print axioms finite_g_pow_gt_rpow
#print axioms finite_g_gt_rpow_of_primeFactors_card_le
#print axioms g_le_rpow_mul_exp_primeFactors
#print axioms finite_g_gt_rpow_on_smooth
#print axioms exists_g_le_rpow_on_smooth
#print axioms finite_g_two_pow_gt_rpow
#print axioms g_two_pow_le
#print axioms large_g_of_prime_blocks
#print axioms large_g_of_common_smooth_part
#print axioms dyadic_primes_g_lower_bound
#print axioms finite_g_gt_one_add
#print axioms g_pow_le
#print axioms g_eq_card_admissibleSupports
#print axioms erdos_821_of_shifted_prime_estimate
#print axioms large_g_of_smooth_shifted_primes
#print axioms infinite_g_gt
#print axioms erdos_821_of_one_le
#print axioms exists_g_gt_of_card
#print axioms g_le_two_pow_shifted_prime_divisors

end Erdos821
