import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A281009: Number of odd divisors of $n$ minus the number of middle divisors of $n$.
A divisor $d$ of $n$ is a "middle divisor" if $\sqrt{n/2} \le d < \sqrt{2n}$,
which is equivalent to $n \le 2d^2$ and $d^2 < 2n$ for $d \in \mathbb{N}$.
-/
def A281009 (n : ℕ) : ℤ :=
  if h : n = 0 then
    0
  else
    let odd_div_count : ℕ := (divisors n).filter (fun d => d % 2 = 1) |>.card
    let middle_div_condition (d : ℕ) : Prop := n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n
    let middle_div_count : ℕ := (divisors n).filter middle_div_condition |>.card
    (odd_div_count : ℤ) - (middle_div_count : ℤ)

open scoped Pointwise

lemma odd_divisors_pow_two_mul_odd_set (k m : ℕ) (hm : Odd m) :
    (divisors (2 ^ k * m)).filter (fun d => d % 2 = 1) = divisors m := by
  classical
  ext d
  constructor
  · intro hd
    rw [mem_filter, Nat.mem_divisors] at hd
    rw [Nat.mem_divisors]
    rcases hd with ⟨⟨hdvd, hn0⟩, hoddmod⟩
    have hodd : Odd d := Nat.odd_iff.mpr hoddmod
    have hcop : d.Coprime (2 ^ k) := by
      exact (Nat.Coprime.pow_right k ((Nat.coprime_two_right).mpr hodd))
    have hdvdm : d ∣ m := hcop.dvd_of_dvd_mul_left hdvd
    exact ⟨hdvdm, Nat.ne_of_gt hm.pos⟩
  · intro hd
    rw [Nat.mem_divisors] at hd
    rw [mem_filter, Nat.mem_divisors]
    rcases hd with ⟨hdvdm, hm0⟩
    have hdvdn : d ∣ 2 ^ k * m := dvd_mul_of_dvd_right hdvdm (2 ^ k)
    have hodd : Odd d := Odd.of_dvd_nat hm hdvdm
    exact ⟨⟨hdvdn, mul_ne_zero (pow_ne_zero k (by norm_num)) hm0⟩, Nat.odd_iff.mp hodd⟩


lemma large_odd_divisors_pow_two_mul_odd_set (k m : ℕ) (hm : Odd m) :
    (divisors (2 ^ k * m)).filter (fun d => d % 2 = 1 ∧ 2 * (2 ^ k * m) < d ^ 2)
      = (divisors m).filter (fun d => 2 * (2 ^ k * m) < d ^ 2) := by
  classical
  ext d
  constructor
  · intro hd
    rw [mem_filter, Nat.mem_divisors] at hd
    rw [mem_filter, Nat.mem_divisors]
    rcases hd with ⟨⟨hdvd, hn0⟩, hoddmod, hlarge⟩
    have hodd : Odd d := Nat.odd_iff.mpr hoddmod
    have hcop : d.Coprime (2 ^ k) := Nat.Coprime.pow_right k ((Nat.coprime_two_right).mpr hodd)
    have hdvdm : d ∣ m := hcop.dvd_of_dvd_mul_left hdvd
    exact ⟨⟨hdvdm, Nat.ne_of_gt hm.pos⟩, hlarge⟩
  · intro hd
    rw [mem_filter, Nat.mem_divisors] at hd
    rw [mem_filter, Nat.mem_divisors]
    rcases hd with ⟨⟨hdvdm, hm0⟩, hlarge⟩
    have hdvdn : d ∣ 2 ^ k * m := dvd_mul_of_dvd_right hdvdm (2 ^ k)
    have hodd : Odd d := Odd.of_dvd_nat hm hdvdm
    exact ⟨⟨hdvdn, mul_ne_zero (pow_ne_zero k (by norm_num)) hm0⟩, Nat.odd_iff.mp hodd, hlarge⟩


lemma factorization_two_pow_mul_odd (i e : ℕ) (he : Odd e) :
    (2 ^ i * e).factorization 2 = i := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hpow0 : 2 ^ i ≠ 0 := pow_ne_zero i (by norm_num)
  have he0 : e ≠ 0 := Nat.ne_of_gt he.pos
  rw [Nat.factorization_mul hpow0 he0]
  simp [Nat.Prime.factorization_pow hp, Nat.factorization_eq_zero_of_not_dvd,
    (Nat.two_dvd_ne_zero).mpr (Nat.odd_iff.mp he)]


lemma chainMap_injective_on_odd_divisors (k m : ℕ) (hm : Odd m) :
    ∀ p ∈ (range (k + 1)).product (divisors m),
      ∀ q ∈ (range (k + 1)).product (divisors m),
        2 ^ p.1 * p.2 = 2 ^ q.1 * q.2 → p = q := by
  intro p hp q hq hEq
  simp [Finset.mem_product] at hp hq
  rcases hp with ⟨hpi, hpe⟩
  rcases hq with ⟨hqi, hqe⟩
  have hoddp : Odd p.2 := Odd.of_dvd_nat hm hpe.1
  have hoddq : Odd q.2 := Odd.of_dvd_nat hm hqe.1
  have hi : p.1 = q.1 := by
    calc
      p.1 = (2 ^ p.1 * p.2).factorization 2 := (factorization_two_pow_mul_odd p.1 p.2 hoddp).symm
      _ = (2 ^ q.1 * q.2).factorization 2 := by rw [hEq]
      _ = q.1 := factorization_two_pow_mul_odd q.1 q.2 hoddq
  cases p with
  | mk pi pe =>
  cases q with
  | mk qi qe =>
  simp only at hi hEq hoddp hoddq ⊢
  subst qi
  simpa using (Nat.mul_left_cancel (pow_pos (by norm_num) pi) hEq)


lemma divisors_pow_two_mul_image (k m : ℕ) :
    divisors (2 ^ k * m) =
      ((range (k + 1)).product (divisors m)).image (fun p : ℕ × ℕ => 2 ^ p.1 * p.2) := by
  classical
  rw [Nat.divisors_mul, Nat.divisors_prime_pow Nat.prime_two]
  ext d
  constructor
  · intro hd
    rw [Finset.mem_mul] at hd
    rcases hd with ⟨y, hy, z, hz, hyz⟩
    rw [Finset.mem_map] at hy
    rcases hy with ⟨i, hi, rfl⟩
    rw [Finset.mem_image]
    exact ⟨(i, z), by simpa [Finset.mem_product, hi, hz], by simpa using hyz⟩
  · intro hd
    rw [Finset.mem_image] at hd
    rcases hd with ⟨p, hp, rfl⟩
    rw [Finset.mem_mul]
    simp [Finset.mem_product] at hp
    rcases hp with ⟨hi, hz⟩
    refine ⟨2 ^ p.1, ?_, p.2, Nat.mem_divisors.mpr hz, rfl⟩
    rw [Finset.mem_map]
    exact ⟨p.1, mem_range.mpr (Nat.lt_succ_iff.mpr hi), rfl⟩


lemma middle_count_as_chain_pairs (k m : ℕ) (hm : Odd m) :
    ((divisors (2 ^ k * m)).filter
      (fun d => 2 ^ k * m ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * (2 ^ k * m))).card
    = (((range (k + 1)).product (divisors m)).filter
      (fun p : ℕ × ℕ => 2 ^ k * m ≤ 2 * (2 ^ p.1 * p.2) ^ 2 ∧
        (2 ^ p.1 * p.2) ^ 2 < 2 * (2 ^ k * m))).card := by
  classical
  let s := (range (k + 1)).product (divisors m)
  let f : (ℕ × ℕ) → ℕ := fun p => 2 ^ p.1 * p.2
  have hdiv : divisors (2 ^ k * m) = s.image f := by
    simpa [s, f] using divisors_pow_two_mul_image k m
  have hinj : Set.InjOn f ↑(s.filter (fun p : ℕ × ℕ =>
      2 ^ k * m ≤ 2 * (f p) ^ 2 ∧ (f p) ^ 2 < 2 * (2 ^ k * m))) := by
    intro a ha b hb hab
    have has : a ∈ s := (mem_filter.mp ha).1
    have hbs : b ∈ s := (mem_filter.mp hb).1
    exact chainMap_injective_on_odd_divisors k m hm a (by simpa [s] using has) b (by simpa [s] using hbs) (by simpa [f] using hab)
  calc
    ((divisors (2 ^ k * m)).filter
      (fun d => 2 ^ k * m ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * (2 ^ k * m))).card
        = ((s.image f).filter
      (fun d => 2 ^ k * m ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * (2 ^ k * m))).card := by rw [hdiv]
    _ = (s.filter (fun p : ℕ × ℕ =>
      2 ^ k * m ≤ 2 * (f p) ^ 2 ∧ (f p) ^ 2 < 2 * (2 ^ k * m))).card := by
        rw [Finset.filter_image]
        exact Finset.card_image_of_injOn hinj
    _ = (((range (k + 1)).product (divisors m)).filter
      (fun p : ℕ × ℕ => 2 ^ k * m ≤ 2 * (2 ^ p.1 * p.2) ^ 2 ∧
        (2 ^ p.1 * p.2) ^ 2 < 2 * (2 ^ k * m))).card := by rfl


lemma sq_pow_succ_mul (i e : ℕ) :
    (2 ^ (i + 1) * e) ^ 2 = 4 * (2 ^ i * e) ^ 2 := by
  ring_nf

lemma pow_mul_mono_left_two {i j e : ℕ} (hij : i ≤ j) :
    2 ^ i * e ≤ 2 ^ j * e := by
  exact Nat.mul_le_mul_right e (Nat.pow_le_pow_right (by norm_num) hij)

lemma sq_pow_mul_mono_left_two {i j e : ℕ} (hij : i ≤ j) :
    (2 ^ i * e) ^ 2 ≤ (2 ^ j * e) ^ 2 := by
  exact Nat.pow_le_pow_left (pow_mul_mono_left_two (e := e) hij) 2

lemma exists_unique_middle_in_chain (k e n : ℕ)
    (hlo : e ^ 2 < 2 * n)
    (hhi : n ≤ 2 * (2 ^ k * e) ^ 2) :
    ∃! i, i ∈ range (k + 1) ∧ n ≤ 2 * (2 ^ i * e) ^ 2 ∧
      (2 ^ i * e) ^ 2 < 2 * n := by
  classical
  let Q : ℕ → Prop := fun i => n ≤ 2 * (2 ^ i * e) ^ 2
  have hex : ∃ i, Q i := ⟨k, hhi⟩
  let i := Nat.find hex
  have hiQ : Q i := Nat.find_spec hex
  have hik : i ≤ k := Nat.find_min' hex hhi
  have hi_mem : i ∈ range (k + 1) := mem_range.mpr (Nat.lt_succ_iff.mpr hik)
  have hi_upper : (2 ^ i * e) ^ 2 < 2 * n := by
    by_cases hi0 : i = 0
    · change (2 ^ i * e) ^ 2 < 2 * n
      rw [hi0]
      simpa using hlo
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      let j := i - 1
      have hjsucc : j + 1 = i := Nat.succ_pred_eq_of_pos hipos
      have hjlt : j < Nat.find hex := by
        change j < i
        rw [← hjsucc]
        exact Nat.lt_succ_self j
      have hnot : ¬ Q j := Nat.find_min hex hjlt
      have hlt : 2 * (2 ^ j * e) ^ 2 < n := Nat.lt_of_not_ge hnot
      have hs : (2 ^ i * e) ^ 2 = 4 * (2 ^ j * e) ^ 2 := by
        rw [← hjsucc]
        exact sq_pow_succ_mul j e
      rw [hs]
      nlinarith
  refine ⟨i, ⟨hi_mem, hiQ, hi_upper⟩, ?_⟩
  intro j hj
  rcases hj with ⟨hjmem, hjQ, hjupper⟩
  have hjle : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hjmem)
  by_cases hji : j < i
  · have hnot : ¬ Q j := Nat.find_min hex hji
    exact (hnot hjQ).elim
  · have hij : i ≤ j := le_of_not_gt hji
    by_cases hEq : i = j
    · exact hEq.symm
    · have hltij : i < j := lt_of_le_of_ne hij hEq
      have hsuc : i + 1 ≤ j := Nat.succ_le_iff.mpr hltij

      have hmono : (2 ^ (i + 1) * e) ^ 2 ≤ (2 ^ j * e) ^ 2 :=
        sq_pow_mul_mono_left_two (e := e) hsuc
      have hs : (2 ^ (i + 1) * e) ^ 2 = 4 * (2 ^ i * e) ^ 2 := sq_pow_succ_mul i e
      have hcontr : 2 * n ≤ (2 ^ j * e) ^ 2 := by
        calc
          2 * n ≤ 4 * (2 ^ i * e) ^ 2 := by nlinarith
          _ = (2 ^ (i + 1) * e) ^ 2 := hs.symm
          _ ≤ (2 ^ j * e) ^ 2 := hmono
      exact (not_lt_of_ge hcontr hjupper).elim


lemma odd_sq_lt_of_not_large {n e : ℕ} (he : Odd e) (hnot : ¬ 2 * n < e ^ 2) :
    e ^ 2 < 2 * n := by
  have hle : e ^ 2 ≤ 2 * n := le_of_not_gt hnot
  have hne : e ^ 2 ≠ 2 * n := by
    intro h
    have hmod := congrArg (fun x : ℕ => x % 2) h
    change (e ^ 2) % 2 = (2 * n) % 2 at hmod
    have hoddmod : (e ^ 2) % 2 = 1 := Nat.odd_iff.mp (he.pow)
    have hevenmod : (2 * n) % 2 = 0 := by simp
    rw [hoddmod, hevenmod] at hmod
    norm_num at hmod
  exact Nat.lt_of_le_of_ne hle hne

lemma complement_sq_le_of_chain_lower {k m e i : ℕ} (he_dvd : e ∣ m)
    (hmpos : 0 < m) (hepos : 0 < e) (hik : i ≤ k)
    (hlow : 2 ^ k * m ≤ 2 * (2 ^ i * e) ^ 2) :
    (m / e) ^ 2 ≤ 2 * (2 ^ k * m) := by
  let c := m / e
  have hcm : c * e = m := Nat.div_mul_cancel he_dvd
  have hmec : m = e * c := by rw [← hcm, mul_comm]
  have hcpos : 0 < c := by
    rw [Nat.div_pos_iff]
    exact ⟨hepos, Nat.le_of_dvd hmpos he_dvd⟩
  let A := 2 ^ i
  let B := 2 ^ k
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hAleB : A ≤ B := Nat.pow_le_pow_right (by norm_num) hik
  have hA2leB2 : A ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hAleB 2
  have hlow' : B * (e * c) ≤ 2 * (A * e) ^ 2 := by
    simpa [A, B, hmec, mul_assoc, mul_comm, mul_left_comm] using hlow
  have hlow'' : B * e * c ≤ 2 * A ^ 2 * e ^ 2 := by nlinarith
  have hmulbound : (B * e) * c ≤ (B * e) * (2 * B * e) := by nlinarith
  have hbound : c ≤ 2 * B * e :=
    Nat.le_of_mul_le_mul_left hmulbound (Nat.mul_pos hBpos hepos)
  have hgoal : c ^ 2 ≤ 2 * (B * (e * c)) := by nlinarith
  change c ^ 2 ≤ 2 * (2 ^ k * m)
  rw [hmec]
  change c ^ 2 ≤ 2 * (B * (e * c))
  exact hgoal

lemma chain_top_lower_of_complement_sq_le {k m e : ℕ} (he_dvd : e ∣ m)
    (hmpos : 0 < m) (hepos : 0 < e) (hcomp : (m / e) ^ 2 ≤ 2 * (2 ^ k * m)) :
    2 ^ k * m ≤ 2 * (2 ^ k * e) ^ 2 := by
  let c := m / e
  have hcm : c * e = m := Nat.div_mul_cancel he_dvd
  have hmec : m = e * c := by rw [← hcm, mul_comm]
  have hcpos : 0 < c := by
    rw [Nat.div_pos_iff]
    exact ⟨hepos, Nat.le_of_dvd hmpos he_dvd⟩
  let B := 2 ^ k
  have hBpos : 0 < B := by positivity
  have hcomp0 : c ^ 2 ≤ 2 * (2 ^ k * m) := by simpa [c] using hcomp
  have hcomp' : c ^ 2 ≤ 2 * (B * (e * c)) := by
    rw [hmec] at hcomp0
    simpa [B, mul_assoc, mul_comm, mul_left_comm] using hcomp0
  have hmulbound : c * c ≤ (2 * B * e) * c := by nlinarith
  have hbound : c ≤ 2 * B * e := Nat.le_of_mul_le_mul_right hmulbound hcpos
  have hgoal : B * (e * c) ≤ 2 * (B * e) ^ 2 := by nlinarith
  change 2 ^ k * m ≤ 2 * (2 ^ k * e) ^ 2
  rw [hmec]
  change B * (e * c) ≤ 2 * (B * e) ^ 2
  exact hgoal

lemma middle_chain_pairs_card_eq_good (k m : ℕ) (hm : Odd m) :
    (((range (k + 1)).product (divisors m)).filter
      (fun p : ℕ × ℕ => 2 ^ k * m ≤ 2 * (2 ^ p.1 * p.2) ^ 2 ∧
        (2 ^ p.1 * p.2) ^ 2 < 2 * (2 ^ k * m))).card
    = ((divisors m).filter
      (fun e => ¬ 2 * (2 ^ k * m) < e ^ 2 ∧ ¬ 2 * (2 ^ k * m) < (m / e) ^ 2)).card := by
  classical
  let n := 2 ^ k * m
  let P : ℕ × ℕ → Prop := fun p => n ≤ 2 * (2 ^ p.1 * p.2) ^ 2 ∧
        (2 ^ p.1 * p.2) ^ 2 < 2 * n
  let G : ℕ → Prop := fun e => ¬ 2 * n < e ^ 2 ∧ ¬ 2 * n < (m / e) ^ 2
  let s := ((range (k + 1)).product (divisors m)).filter P
  let t := (divisors m).filter G
  have hmpos : 0 < m := hm.pos
  apply Finset.card_bij (fun p hp => p.2)
  · intro p hp
    have hp_mem := (mem_filter.mp hp).1
    have hp_P := (mem_filter.mp hp).2
    have hp_prod : p.1 ∈ range (k + 1) ∧ p.2 ∈ divisors m := by
      simpa [Finset.mem_product] using hp_mem
    have hpi : p.1 ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hp_prod.1)
    have hpdvd : p.2 ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp hp_prod.2
    have hlow : 2 ^ k * m ≤ 2 * (2 ^ p.1 * p.2) ^ 2 := hp_P.1
    have hupp : (2 ^ p.1 * p.2) ^ 2 < 2 * (2 ^ k * m) := hp_P.2
    have heodd : Odd p.2 := Odd.of_dvd_nat hm hpdvd.1
    have hele_d : p.2 ^ 2 ≤ (2 ^ p.1 * p.2) ^ 2 := by
      simpa using (sq_pow_mul_mono_left_two (e := p.2) (Nat.zero_le p.1))
    have hnotlarge : ¬ 2 * n < p.2 ^ 2 := by
      have : p.2 ^ 2 < 2 * n := lt_of_le_of_lt hele_d (by simpa [n] using hupp)
      omega
    have hepos : 0 < p.2 := heodd.pos
    have hcomp_le : (m / p.2) ^ 2 ≤ 2 * n := by
      simpa [n] using complement_sq_le_of_chain_lower hpdvd.1 hmpos hepos hpi (by simpa [n] using hlow)
    have hnotcomp : ¬ 2 * n < (m / p.2) ^ 2 := not_lt_of_ge hcomp_le
    exact mem_filter.mpr ⟨hp_prod.2, ⟨by simpa [n] using hnotlarge, by simpa [n] using hnotcomp⟩⟩
  · intro p hp q hq hpq
    have hp_mem := (mem_filter.mp hp).1
    have hp_P := (mem_filter.mp hp).2
    have hq_mem := (mem_filter.mp hq).1
    have hq_P := (mem_filter.mp hq).2
    have hp_prod : p.1 ∈ range (k + 1) ∧ p.2 ∈ divisors m := by
      simpa [Finset.mem_product] using hp_mem
    have hq_prod : q.1 ∈ range (k + 1) ∧ q.2 ∈ divisors m := by
      simpa [Finset.mem_product] using hq_mem
    have hpi : p.1 ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hp_prod.1)
    have hqi : q.1 ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hq_prod.1)
    have hpdvd : p.2 ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp hp_prod.2
    have hqdvd : q.2 ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp hq_prod.2
    have hplow : 2 ^ k * m ≤ 2 * (2 ^ p.1 * p.2) ^ 2 := hp_P.1
    have hpupp : (2 ^ p.1 * p.2) ^ 2 < 2 * (2 ^ k * m) := hp_P.2
    have hqlow : 2 ^ k * m ≤ 2 * (2 ^ q.1 * q.2) ^ 2 := hq_P.1
    have hqupp : (2 ^ q.1 * q.2) ^ 2 < 2 * (2 ^ k * m) := hq_P.2
    cases p with
    | mk pi e =>
    cases q with
    | mk qi f =>
    simp only at hpq
    subst f
    simp only at hpi hpdvd hplow hpupp hqi hqdvd hqlow hqupp ⊢
    have hele_d : e ^ 2 ≤ (2 ^ pi * e) ^ 2 := by
      simpa using (sq_pow_mul_mono_left_two (e := e) (Nat.zero_le pi))
    have hlo : e ^ 2 < 2 * n := lt_of_le_of_lt hele_d (by simpa [n] using hpupp)
    have htopmono : (2 ^ pi * e) ^ 2 ≤ (2 ^ k * e) ^ 2 :=
      sq_pow_mul_mono_left_two (e := e) hpi
    have hhi : n ≤ 2 * (2 ^ k * e) ^ 2 := by
      exact le_trans (by simpa [n] using hplow) (Nat.mul_le_mul_left 2 htopmono)
    obtain ⟨w, hw, huniq⟩ := exists_unique_middle_in_chain k e n hlo hhi
    have hpi_prop : pi ∈ range (k + 1) ∧ n ≤ 2 * (2 ^ pi * e) ^ 2 ∧ (2 ^ pi * e) ^ 2 < 2 * n := by
      exact ⟨mem_range.mpr (Nat.lt_succ_iff.mpr hpi), by simpa [n] using hplow, by simpa [n] using hpupp⟩
    have hqi_prop : qi ∈ range (k + 1) ∧ n ≤ 2 * (2 ^ qi * e) ^ 2 ∧ (2 ^ qi * e) ^ 2 < 2 * n := by
      exact ⟨mem_range.mpr (Nat.lt_succ_iff.mpr hqi), by simpa [n] using hqlow, by simpa [n] using hqupp⟩
    have hpi_eq : pi = w := (huniq pi hpi_prop)
    have hqi_eq : qi = w := (huniq qi hqi_prop)
    have hpqidx : pi = qi := hpi_eq.trans hqi_eq.symm
    subst qi
    subst pi
    rfl
  · intro e he
    have he_mem := (mem_filter.mp he).1
    have he_G := (mem_filter.mp he).2
    have hedvd : e ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp he_mem
    have hnotlarge : ¬ 2 * n < e ^ 2 := he_G.1
    have hnotcomp : ¬ 2 * n < (m / e) ^ 2 := he_G.2
    have heodd : Odd e := Odd.of_dvd_nat hm hedvd.1
    have hepos : 0 < e := heodd.pos
    have hlo : e ^ 2 < 2 * n := odd_sq_lt_of_not_large heodd hnotlarge
    have hcomp_le : (m / e) ^ 2 ≤ 2 * n := le_of_not_gt hnotcomp
    have hhi : n ≤ 2 * (2 ^ k * e) ^ 2 := by
      simpa [n] using chain_top_lower_of_complement_sq_le hedvd.1 hmpos hepos (by simpa [n] using hcomp_le)
    obtain ⟨i, hi, huniq⟩ := exists_unique_middle_in_chain k e n hlo hhi
    refine ⟨(i, e), ?_, rfl⟩
    rcases hi with ⟨himem, hilow, hiupp⟩
    simp [s, P, n, Finset.mem_product, himem, hedvd, hilow, hiupp]

lemma large_and_complement_large_false {k m e : ℕ} (he_dvd : e ∣ m)
    (hmpos : 0 < m) (hepos : 0 < e)
    (hL : 2 * (2 ^ k * m) < e ^ 2)
    (hS : 2 * (2 ^ k * m) < (m / e) ^ 2) : False := by
  let c := m / e
  have hcm : c * e = m := Nat.div_mul_cancel he_dvd
  have hmec : m = e * c := by rw [← hcm, mul_comm]
  have hcpos : 0 < c := by
    rw [Nat.div_pos_iff]
    exact ⟨hepos, Nat.le_of_dvd hmpos he_dvd⟩
  let B := 2 ^ k
  have hBge : 1 ≤ B := Nat.one_le_two_pow
  have hL0 : 2 * (B * (e * c)) < e ^ 2 := by
    simpa [B, hmec, mul_assoc, mul_comm, mul_left_comm] using hL
  have hS0 : 2 * (B * (e * c)) < c ^ 2 := by
    change 2 * (2 ^ k * m) < c ^ 2 at hS
    rw [hmec] at hS
    simpa [B, mul_assoc, mul_comm, mul_left_comm] using hS
  have hL' : (2 * B * c) * e < e * e := by
    nlinarith
  have hS' : (2 * B * e) * c < c * c := by
    nlinarith
  have hc_lt_e : 2 * B * c < e := Nat.lt_of_mul_lt_mul_right hL'
  have he_lt_c : 2 * B * e < c := Nat.lt_of_mul_lt_mul_right hS'
  have hc2_lt_e : 2 * c < e := by nlinarith
  have he2_lt_c : 2 * e < c := by nlinarith
  omega

lemma complement_large_card_eq_large (k m : ℕ) (hm : Odd m) :
    ((divisors m).filter (fun e => 2 * (2 ^ k * m) < (m / e) ^ 2)).card =
      ((divisors m).filter (fun e => 2 * (2 ^ k * m) < e ^ 2)).card := by
  classical
  let S := (divisors m).filter (fun e => 2 * (2 ^ k * m) < (m / e) ^ 2)
  let L := (divisors m).filter (fun e => 2 * (2 ^ k * m) < e ^ 2)
  apply Finset.card_bij (fun e he => m / e)
  · intro e he
    have he_mem := (mem_filter.mp he).1
    have heS := (mem_filter.mp he).2
    have hedvd : e ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp he_mem
    have hcomp_mem : m / e ∈ divisors m := Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hedvd.1, hedvd.2⟩
    have hinv : m / (m / e) = e := Nat.div_div_self hedvd.1 hedvd.2
    exact mem_filter.mpr ⟨hcomp_mem, by simpa [hinv] using heS⟩
  · intro e he f hf hef
    have he_mem := (mem_filter.mp he).1
    have hf_mem := (mem_filter.mp hf).1
    have hedvd : e ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp he_mem
    have hfdvd : f ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp hf_mem
    calc
      e = m / (m / e) := (Nat.div_div_self hedvd.1 hedvd.2).symm
      _ = m / (m / f) := by rw [hef]
      _ = f := Nat.div_div_self hfdvd.1 hfdvd.2
  · intro e he
    have he_mem := (mem_filter.mp he).1
    have heL := (mem_filter.mp he).2
    have hedvd : e ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp he_mem
    refine ⟨m / e, ?_, ?_⟩
    · have hcomp_mem : m / e ∈ divisors m := Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hedvd.1, hedvd.2⟩
      have hinv : m / (m / e) = e := Nat.div_div_self hedvd.1 hedvd.2
      exact mem_filter.mpr ⟨hcomp_mem, by simpa [hinv] using heL⟩
    · exact Nat.div_div_self hedvd.1 hedvd.2

lemma good_card_add_twice_large (k m : ℕ) (hm : Odd m) :
    ((divisors m).filter
      (fun e => ¬ 2 * (2 ^ k * m) < e ^ 2 ∧ ¬ 2 * (2 ^ k * m) < (m / e) ^ 2)).card
      + 2 * ((divisors m).filter (fun e => 2 * (2 ^ k * m) < e ^ 2)).card
    = (divisors m).card := by
  classical
  let E := divisors m
  let Lp : ℕ → Prop := fun e => 2 * (2 ^ k * m) < e ^ 2
  let Sp : ℕ → Prop := fun e => 2 * (2 ^ k * m) < (m / e) ^ 2
  have hgood_eq : E.filter (fun e => ¬ Lp e ∧ ¬ Sp e) = E.filter (fun e => ¬ (Lp e ∨ Sp e)) := by
    ext e; by_cases hL : Lp e <;> by_cases hS : Sp e <;> simp [Lp, Sp, hL, hS]
  have hpart := Finset.card_filter_add_card_filter_not (s := E) (p := fun e => Lp e ∨ Sp e)
  have hor : E.filter (fun e => Lp e ∨ Sp e) = E.filter Lp ∪ E.filter Sp := Finset.filter_or Lp Sp E
  have hdisj : Disjoint (E.filter Lp) (E.filter Sp) := by
    rw [Finset.disjoint_left]
    intro e heL heS
    have he_mem : e ∈ E := (mem_filter.mp heL).1
    have hL : Lp e := (mem_filter.mp heL).2
    have hS : Sp e := (mem_filter.mp heS).2
    have hedvd : e ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp he_mem
    have heodd : Odd e := Odd.of_dvd_nat hm hedvd.1
    exact (large_and_complement_large_false hedvd.1 hm.pos heodd.pos hL hS).elim
  have hcard_or : (E.filter (fun e => Lp e ∨ Sp e)).card = (E.filter Lp).card + (E.filter Sp).card := by
    rw [hor, Finset.card_union_of_disjoint hdisj]
  have hS_card : (E.filter Sp).card = (E.filter Lp).card := by
    simpa [E, Lp, Sp] using complement_large_card_eq_large k m hm
  have hpart' : (E.filter (fun e => ¬ (Lp e ∨ Sp e))).card + (E.filter (fun e => Lp e ∨ Sp e)).card = E.card := by
    rw [add_comm]
    exact hpart
  rw [hcard_or, hS_card, ← hgood_eq] at hpart'
  change (E.filter (fun e => ¬ Lp e ∧ ¬ Sp e)).card + 2 * (E.filter Lp).card = E.card
  omega


lemma middle_add_twice_large_eq_odd_pow_two_mul_odd (k m : ℕ) (hm : Odd m) :
    ((divisors (2 ^ k * m)).filter
      (fun d => 2 ^ k * m ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * (2 ^ k * m))).card
      + 2 * ((divisors (2 ^ k * m)).filter
        (fun d => d % 2 = 1 ∧ 2 * (2 ^ k * m) < d ^ 2)).card
    = ((divisors (2 ^ k * m)).filter (fun d => d % 2 = 1)).card := by
  classical
  have hmid1 := middle_count_as_chain_pairs k m hm
  have hmid2 := middle_chain_pairs_card_eq_good k m hm
  have hgood := good_card_add_twice_large k m hm
  have hlarge_set := large_odd_divisors_pow_two_mul_odd_set k m hm
  have hodd_set := odd_divisors_pow_two_mul_odd_set k m hm
  calc
    ((divisors (2 ^ k * m)).filter
      (fun d => 2 ^ k * m ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * (2 ^ k * m))).card
      + 2 * ((divisors (2 ^ k * m)).filter
        (fun d => d % 2 = 1 ∧ 2 * (2 ^ k * m) < d ^ 2)).card
        = ((divisors m).filter
      (fun e => ¬ 2 * (2 ^ k * m) < e ^ 2 ∧ ¬ 2 * (2 ^ k * m) < (m / e) ^ 2)).card
          + 2 * ((divisors m).filter (fun e => 2 * (2 ^ k * m) < e ^ 2)).card := by
            rw [hmid1, hmid2, hlarge_set]
    _ = (divisors m).card := hgood
    _ = ((divisors (2 ^ k * m)).filter (fun d => d % 2 = 1)).card := by rw [hodd_set]

/--
Conjecture 1: a(n) is also twice the number of odd divisors of n greater than sqrt(2*n).
-/
theorem oeis_281009_conjecture_0 (n : ℕ) (hn : n ≠ 0) :
    (A281009 n : ℤ) = 2 * (↑(((divisors n).filter (fun d => d % 2 = 1 ∧ 2 * n < d ^ 2)).card) : ℤ) :=
by
  classical
  unfold A281009
  simp [hn]
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hnat := middle_add_twice_large_eq_odd_pow_two_mul_odd k m hm
  omega
