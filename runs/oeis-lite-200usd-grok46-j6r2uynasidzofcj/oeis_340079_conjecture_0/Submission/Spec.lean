import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

/-- Pillai's arithmetical function $P(n) = \sum_{k=1}^n \gcd(k,n)$. -/
def pillai (n : ℕ) : ℕ :=
  ∑ k ∈ Ico 1 (n + 1), k.gcd n

lemma pillai_eq_a_aux (n : ℕ) :
    a n = n / Nat.gcd n (1 + pillai n) := rfl

lemma pillai_eq_sum_range (n : ℕ) :
    pillai n = ∑ k ∈ range n, k.gcd n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [pillai]
  have hI : Ico 1 (n + 1) = (range (n + 1)).erase 0 := by
    ext k
    simp only [mem_Ico, mem_erase, mem_range]
    constructor
    · intro ⟨hk1, hk2⟩
      exact ⟨Nat.ne_of_gt hk1, hk2⟩
    · intro ⟨hk0, hk⟩
      exact ⟨Nat.pos_of_ne_zero hk0, hk⟩
  have h0 : 0 ∈ range (n + 1) := mem_range.2 (Nat.succ_pos _)
  unfold pillai
  rw [hI]
  have hsum := add_sum_erase (range (n + 1)) (fun k => k.gcd n) h0
  simp only [Nat.gcd_zero_left] at hsum
  rw [sum_range_succ, Nat.gcd_self] at hsum
  exact Nat.add_right_cancel (by rw [add_comm, hsum, add_comm])

lemma pillai_zero : pillai 0 = 0 := by simp [pillai]

lemma pillai_one : pillai 1 = 1 := by simp [pillai]

/-- $P(n) = \sum_{d \mid n} d\,\varphi(n/d)$. -/
lemma pillai_eq_sum_mul_totient (n : ℕ) :
    pillai n = ∑ d ∈ n.divisors, d * φ (n / d) := by
  rw [pillai_eq_sum_range]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hmaps : ∀ k ∈ range n, n.gcd k ∈ n.divisors := fun k _ =>
    mem_divisors.2 ⟨Nat.gcd_dvd_left n k, hn.ne'⟩
  have hswap : ∑ k ∈ range n, k.gcd n = ∑ k ∈ range n, n.gcd k := by
    simp [Nat.gcd_comm]
  rw [hswap, ← sum_fiberwise_of_maps_to' hmaps (fun d => d)]
  refine sum_congr rfl fun d hd => ?_
  have hcard : #{k ∈ range n | n.gcd k = d} = φ (n / d) := by
    have : d ∣ n := dvd_of_mem_divisors hd
    simpa [Nat.gcd_comm] using (totient_div_of_dvd this).symm
  simp [hcard, sum_const, mul_comm]

/-- $P(n) = \sum_{d \mid n} \varphi(d)\,(n/d)$. -/
lemma pillai_eq_sum_totient_mul (n : ℕ) :
    pillai n = ∑ d ∈ n.divisors, φ d * (n / d) := by
  rw [pillai_eq_sum_mul_totient, ← sum_div_divisors n fun d => d * φ (n / d)]
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := dvd_of_mem_divisors hd
  have : n / (n / d) = d := Nat.div_div_self hdn (ne_zero_of_mem_divisors hd)
  rw [this, mul_comm]

lemma a_eq_one_iff {n : ℕ} (hn : 0 < n) :
    a n = 1 ↔ n ∣ pillai n + 1 := by
  rw [pillai_eq_a_aux]
  set g := n.gcd (1 + pillai n)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hgdvd : g ∣ n := Nat.gcd_dvd_left _ _
  have hdecomp : n = g * (n / g) := (Nat.mul_div_cancel' hgdvd).symm
  constructor
  · intro h
    have : n / g = 1 := h
    rw [this, mul_one] at hdecomp
    have hg : g ∣ 1 + pillai n := Nat.gcd_dvd_right n (1 + pillai n)
    rw [add_comm] at hg
    simpa [hdecomp] using hg
  · intro h
    have : 1 + pillai n = pillai n + 1 := add_comm _ _
    have hg' : g = n := Nat.gcd_eq_left (this ▸ h)
    rw [hg', Nat.div_self hn]

lemma a_zero : a 0 = 0 := by
  simp [a]

lemma a_one : a 1 = 1 := by
  simp [a]

lemma pillai_prime {p : ℕ} (hp : p.Prime) : pillai p = 2 * p - 1 := by
  rw [pillai_eq_sum_totient_mul, hp.divisors, sum_insert (by simp [hp.ne_one.symm]),
    sum_singleton]
  simp [totient_one, totient_prime hp, hp.pos, Nat.div_self hp.pos]
  have : 1 ≤ p := hp.pos
  omega

lemma a_prime {p : ℕ} (hp : p.Prime) : a p = 1 := by
  rw [a_eq_one_iff hp.pos, pillai_prime hp]
  have : 2 * p - 1 + 1 = 2 * p := by
    have : 1 ≤ 2 * p := by nlinarith [hp.pos]
    omega
  rw [this]
  exact dvd_mul_left p 2

lemma not_dvd_succ_of_dvd {n p : ℕ} (hp : p.Prime) (h : p ∣ n) : ¬ p ∣ n + 1 := by
  intro hp1
  have : p ∣ 1 := (Nat.dvd_add_right h).mp hp1
  exact hp.not_dvd_one this

/-- If $p^2 \mid n$ then $p \mid P(n)$. -/
lemma pillai_dvd_of_sq_dvd {n p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ n) :
    p ∣ pillai n := by
  rw [pillai_eq_sum_totient_mul]
  refine dvd_sum fun d hd => ?_
  have hdn : d ∣ n := dvd_of_mem_divisors hd
  have hdecomp : n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
  by_cases hpd : p ∣ d
  · by_cases hnd : p ∣ n / d
    · exact dvd_mul_of_dvd_right hnd _
    · have hp2d : p ^ 2 ∣ d := by
        have hpow : p ^ 2 ∣ d * (n / d) := hdecomp ▸ h
        exact Coprime.dvd_of_dvd_mul_right
          ((hp.coprime_iff_not_dvd.2 hnd).pow_left _) hpow
      have hpd' : p ∣ d := dvd_trans (dvd_pow_self p (by decide)) hp2d
      have hdivp : p ∣ d / p := by
        have : d = p * (d / p) := (Nat.mul_div_cancel' hpd').symm
        have : p ^ 2 ∣ p * (d / p) := this ▸ hp2d
        have : p * p ∣ p * (d / p) := by simpa [pow_two] using this
        exact (Nat.mul_dvd_mul_iff_left hp.pos).1 this
      have hφ : φ d = p * φ (d / p) := by
        have hd_eq : d = p * (d / p) := (Nat.mul_div_cancel' hpd').symm
        rw [hd_eq, totient_mul_of_prime_of_dvd hp hdivp, Nat.mul_div_cancel_left _ hp.pos]
      rw [hφ]
      exact dvd_mul_of_dvd_left (dvd_mul_right p _) _
  · have : p ∣ n / d := by
      have hpow : p ∣ d * (n / d) :=
        dvd_trans (dvd_pow_self p (by decide)) (hdecomp ▸ h)
      exact (hp.dvd_mul.mp hpow).resolve_left hpd
    exact dvd_mul_of_dvd_right this _

lemma a_ne_one_of_not_squarefree {n : ℕ} (hn : ¬ Squarefree n) (hn0 : n ≠ 0) :
    a n ≠ 1 := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  intro ha
  rw [a_eq_one_iff hnpos] at ha
  obtain ⟨p, hp, hpn⟩ : ∃ p, p.Prime ∧ p * p ∣ n := by
    rw [Nat.squarefree_iff_prime_squarefree] at hn
    push_neg at hn
    exact hn
  have hpn' : p ^ 2 ∣ n := by simpa [pow_two] using hpn
  have : p ∣ pillai n := pillai_dvd_of_sq_dvd hp hpn'
  have hp1 : p ∣ pillai n + 1 :=
    dvd_trans (dvd_trans (dvd_mul_left p p) hpn) ha
  exact not_dvd_succ_of_dvd hp this hp1

lemma divisors_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    (m * p).divisors = m.divisors ∪ m.divisors.image (· * p) := by
  ext d
  simp only [mem_union, mem_image, mem_divisors]
  constructor
  · intro ⟨hdvd, hnz⟩
    by_cases hpd : p ∣ d
    · refine Or.inr ⟨d / p, ⟨?_, hm0⟩, ?_⟩
      · have : d = p * (d / p) := (Nat.mul_div_cancel' hpd).symm
        have : p * (d / p) ∣ m * p := this ▸ hdvd
        rwa [mul_comm p, Nat.mul_dvd_mul_iff_right hp.pos] at this
      · rw [Nat.div_mul_cancel hpd]
    · refine Or.inl ⟨?_, hm0⟩
      exact Coprime.dvd_of_dvd_mul_right (hp.coprime_iff_not_dvd.2 hpd).symm hdvd
  · intro h
    rcases h with ⟨hdvd, _⟩ | ⟨d', ⟨hd', _⟩, rfl⟩
    · exact ⟨hdvd.mul_right p, mul_ne_zero hm0 hp.ne_zero⟩
    · exact ⟨mul_dvd_mul_right hd' p, mul_ne_zero hm0 hp.ne_zero⟩

lemma disjoint_divisors_image_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    Disjoint m.divisors (m.divisors.image (· * p)) := by
  refine disjoint_left.2 fun d hd hd' => ?_
  obtain ⟨d', hd'm, rfl⟩ := mem_image.1 hd'
  have : p ∣ d' * p := dvd_mul_left p d'
  have : p ∣ m := (this.trans (dvd_of_mem_divisors hd))
  exact hpm this

/-- Recurrence: if $p$ is prime not dividing $m$, then $P(mp)=(2p-1)P(m)$. -/
lemma pillai_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    pillai (m * p) = (2 * p - 1) * pillai m := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [pillai_zero]
  have hdisj := disjoint_divisors_image_mul_prime hp hpm
  rw [pillai_eq_sum_totient_mul, pillai_eq_sum_totient_mul,
    divisors_mul_prime hp hpm hm0, sum_union hdisj]
  have hinj : Set.InjOn (fun x => x * p) (m.divisors : Set ℕ) := by
    intro x _ y _ hxy
    exact Nat.mul_right_cancel hp.pos hxy
  conv_lhs => arg 2; rw [sum_image hinj]
  have sum1 : ∑ d ∈ m.divisors, φ d * (m * p / d) = p * pillai m := by
    rw [pillai_eq_sum_totient_mul, mul_sum]
    refine sum_congr rfl fun d hd => ?_
    have hdm : d ∣ m := dvd_of_mem_divisors hd
    have hquot : m * p / d = (m / d) * p := by
      rw [mul_comm m p, Nat.mul_div_assoc p hdm, mul_comm]
    rw [hquot]
    ring
  have sum2 : ∑ d ∈ m.divisors, φ (d * p) * (m * p / (d * p)) = (p - 1) * pillai m := by
    rw [pillai_eq_sum_totient_mul, mul_sum]
    refine sum_congr rfl fun d hd => ?_
    have hdm : d ∣ m := dvd_of_mem_divisors hd
    have hquot : m * p / (d * p) = m / d := by
      rw [mul_comm d p, mul_comm m p, Nat.mul_div_mul_left _ _ hp.pos]
    have hφ : φ (d * p) = φ d * (p - 1) := by
      have hcop : Coprime d p :=
        (hp.coprime_iff_not_dvd.2 (fun hpd => hpm (hpd.trans hdm))).symm
      rw [totient_mul hcop, totient_prime hp]
    rw [hquot, hφ]
    ring
  rw [sum1, sum2, pillai_eq_sum_totient_mul]
  have : p + (p - 1) = 2 * p - 1 := by
    have : 1 ≤ p := hp.pos
    omega
  rw [← this, add_mul]

lemma not_prime_dvd_div_of_squarefree {n p : ℕ} (hn : Squarefree n)
    (hp : p.Prime) (hpn : p ∣ n) : ¬ p ∣ n / p := by
  intro h
  have hnp : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
  have : p * p ∣ n := by
    rw [hnp]
    exact mul_dvd_mul_left p h
  exact (squarefree_iff_prime_squarefree.1 hn p hp) this

/-- For squarefree $n$, $P(n)=\prod_{p\mid n}(2p-1)$. -/
lemma pillai_squarefree : ∀ {n : ℕ}, Squarefree n → n ≠ 0 →
    pillai n = ∏ p ∈ n.primeFactors, (2 * p - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hn0
    rcases eq_or_ne n 1 with rfl | hn1
    · simp [pillai_one]
    obtain ⟨p, hp, hpn⟩ := n.exists_prime_and_dvd hn1
    set m := n / p
    have hm0 : m ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn) hp.pos).ne'
    have hpm : ¬ p ∣ m := not_prime_dvd_div_of_squarefree hn hp hpn
    have hn_eq : n = m * p := by
      rw [mul_comm]
      exact (Nat.mul_div_cancel' hpn).symm
    have hsf : Squarefree m := by
      rw [hn_eq] at hn
      exact hn.of_mul_left
    have hlt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hp.one_lt
    have hp_not_mem : p ∉ m.primeFactors := fun hmem =>
      hpm (dvd_of_mem_primeFactors hmem)
    have hpf : (m * p).primeFactors = insert p m.primeFactors := by
      rw [primeFactors_mul hm0 hp.ne_zero, hp.primeFactors, union_comm, insert_eq]
    rw [hn_eq, pillai_mul_prime hp hpm, hpf, prod_insert hp_not_mem, ih m hlt hsf hm0]

/--
Counterexample to the A340079 conjecture: `a(n) = 1` for the composite
`n = 3 * 37 * 43 * 42307 * 116341`.
-/
theorem oeis_340079_conjecture_0.disproof :
    ¬ (∀ n : ℕ, a n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  intro h
  set n := 3 * 37 * 43 * 42307 * 116341
  have hpos : 0 < n := by norm_num
  have hn0 : n ≠ 0 := hpos.ne'
  have hp3 : Nat.Prime 3 := by norm_num
  have hp37 : Nat.Prime 37 := by norm_num
  have hp43 : Nat.Prime 43 := by norm_num
  have hp4 : Nat.Prime 42307 := by norm_num
  have hp5 : Nat.Prime 116341 := by norm_num
  have hsf : Squarefree n := by
    have s3 : Squarefree 3 := hp3.prime.squarefree
    have s37 : Squarefree 37 := hp37.prime.squarefree
    have s43 : Squarefree 43 := hp43.prime.squarefree
    have s4 : Squarefree 42307 := hp4.prime.squarefree
    have s5 : Squarefree 116341 := hp5.prime.squarefree
    have c1 : Coprime 3 37 := by rw [Nat.coprime_iff_gcd_eq_one]; norm_num
    have c2 : Coprime (3 * 37) 43 := by rw [Nat.coprime_iff_gcd_eq_one]; norm_num
    have c3 : Coprime (3 * 37 * 43) 42307 := by
      rw [Nat.coprime_iff_gcd_eq_one]; norm_num
    have c4 : Coprime (3 * 37 * 43 * 42307) 116341 := by
      rw [Nat.coprime_iff_gcd_eq_one]; norm_num
    have h1 : Squarefree (3 * 37) := (squarefree_mul c1).2 ⟨s3, s37⟩
    have h2 : Squarefree (3 * 37 * 43) := (squarefree_mul c2).2 ⟨h1, s43⟩
    have h3 : Squarefree (3 * 37 * 43 * 42307) := (squarefree_mul c3).2 ⟨h2, s4⟩
    exact (squarefree_mul c4).2 ⟨h3, s5⟩
  have hpf : n.primeFactors = {3, 37, 43, 42307, 116341} := by
    rw [primeFactors_mul (by norm_num : 3 * 37 * 43 * 42307 ≠ 0)
        (by norm_num : 116341 ≠ 0)]
    rw [primeFactors_mul (by norm_num : 3 * 37 * 43 ≠ 0)
        (by norm_num : 42307 ≠ 0)]
    rw [primeFactors_mul (by norm_num : 3 * 37 ≠ 0) (by norm_num : 43 ≠ 0)]
    rw [primeFactors_mul (by norm_num : 3 ≠ 0) (by norm_num : 37 ≠ 0)]
    rw [hp3.primeFactors, hp37.primeFactors, hp43.primeFactors,
      hp4.primeFactors, hp5.primeFactors]
    decide
  have hprod :
      ({3, 37, 43, 42307, 116341} : Finset ℕ).prod (fun p => 2 * p - 1) =
        (2 * 3 - 1) * (2 * 37 - 1) * (2 * 43 - 1) *
          (2 * 42307 - 1) * (2 * 116341 - 1) := by
    have h3 : 3 ∉ ({37, 43, 42307, 116341} : Finset ℕ) := by decide
    have h37 : 37 ∉ ({43, 42307, 116341} : Finset ℕ) := by decide
    have h43 : 43 ∉ ({42307, 116341} : Finset ℕ) := by decide
    have h4 : 42307 ∉ ({116341} : Finset ℕ) := by decide
    rw [prod_insert h3, prod_insert h37, prod_insert h43, prod_insert h4,
      prod_singleton]
    ring
  have hPval :
      (2 * 3 - 1) * (2 * 37 - 1) * (2 * 43 - 1) *
          (2 * 42307 - 1) * (2 * 116341 - 1) =
        610815156979325 := by
    norm_num
  have hP : pillai n = 610815156979325 := by
    rw [pillai_squarefree hsf hn0, hpf, hprod, hPval]
  have hdvd : n ∣ pillai n + 1 := by
    rw [hP]
    norm_num
  have ha : a n = 1 := (a_eq_one_iff hpos).2 hdvd
  have hnot : ¬ (n = 1 ∨ Nat.Prime n) := by
    intro hnp
    rcases hnp with h1 | hp
    · have : n ≠ 1 := by norm_num
      exact this h1
    · have : ¬ Nat.Prime n :=
        Nat.not_prime_mul (by norm_num) (by norm_num)
      exact this hp
  exact hnot ((h n).1 ha)

