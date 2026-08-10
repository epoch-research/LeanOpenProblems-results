import FormalConjectures.Util.ProblemImports
open Finset ZMod
set_option linter.all false
set_option linter.unusedSimpArgs false
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have hn : NeZero n := NeZero.mk h
    let S : Set ℕ := { m : ℕ | A232616_prop n m }
    sInf S
set_option maxHeartbeats 0
set_option maxRecDepth 3000
set_option exponentiation.threshold 200000
def phiCount (N : ℕ) (ps : List ℕ) : ℕ :=
  ((Finset.range N).filter fun i => ∀ q ∈ ps, ¬ q ∣ i + 1).card
lemma dvd_mul_cancel_prime_of_ne {p q n : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : q ≠ p) :
    q ∣ p * n ↔ q ∣ n := by
  constructor
  · intro h
    have h' := (hq.dvd_mul).mp h
    rcases h' with hq_dvd_p | hn
    · have hqp := hp.eq_one_or_self_of_dvd q hq_dvd_p
      rcases hqp with h1 | hself
      · exact (hq.ne_one h1).elim
      · exact (hne hself).elim
    · exact hn
  · intro hn
    exact dvd_mul_of_dvd_right hn p
lemma removed_multiples_card (N p : ℕ) (hp : Nat.Prime p) (ps : List ℕ)
    (hps : ∀ q ∈ ps, Nat.Prime q ∧ q ≠ p) :
    ((Finset.range N).filter fun i => p ∣ i + 1 ∧ ∀ q ∈ ps, ¬ q ∣ i + 1).card =
      phiCount (N / p) ps := by
  unfold phiCount
  let A := (Finset.range N).filter fun i => p ∣ i + 1 ∧ ∀ q ∈ ps, ¬ q ∣ i + 1
  let B := (Finset.range (N / p)).filter fun j => ∀ q ∈ ps, ¬ q ∣ j + 1
  change A.card = B.card
  refine Finset.card_bij (fun i hi => (i + 1) / p - 1) ?_ ?_ ?_
  · intro i hi
    dsimp [A, B] at hi ⊢
    simp only [mem_filter, mem_range] at hi ⊢
    rcases hi with ⟨hiN, hpdiv, hno⟩
    rcases hpdiv with ⟨m, hm⟩
    have hp_pos : 0 < p := hp.pos
    have himul : i + 1 = p * m := by omega
    have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm0
      have hzero : i + 1 = 0 := by simp [himul, hm0]
      exact Nat.succ_ne_zero i hzero
    have hdiv_eq : (i + 1) / p = m := by
      rw [himul, Nat.mul_div_right _ hp_pos]
    constructor
    · rw [hdiv_eq]
      have hle : m ≤ N / p := by
        rw [← hdiv_eq]
        exact Nat.div_le_div_right (Nat.succ_le_of_lt hiN)
      exact (Nat.sub_one_lt (Nat.ne_of_gt hmpos)).trans_le hle
    · intro q hqmem hqdiv
      have hqprime := (hps q hqmem).1
      have hqne := (hps q hqmem).2
      have hqdiv_i : q ∣ i + 1 := by
        rw [himul]
        have hqm : q ∣ m := by simpa [hdiv_eq, Nat.sub_add_cancel hmpos] using hqdiv
        exact (dvd_mul_cancel_prime_of_ne hp hqprime hqne).mpr hqm
      exact hno q hqmem hqdiv_i
  · intro i hi j hj hEq
    dsimp [A] at hi hj
    simp only [mem_filter, mem_range] at hi hj
    have hpi : p ∣ i + 1 := hi.2.1
    have hpj : p ∣ j + 1 := hj.2.1
    have hi_eq : p * ((i + 1) / p) = i + 1 := by exact Nat.mul_div_cancel' hpi
    have hj_eq : p * ((j + 1) / p) = j + 1 := by exact Nat.mul_div_cancel' hpj
    have hdiv_pos_i : 0 < (i + 1) / p := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have : i + 1 = 0 := by rw [← hi_eq, hzero, Nat.mul_zero]
      exact Nat.succ_ne_zero i this
    have hdiv_pos_j : 0 < (j + 1) / p := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have : j + 1 = 0 := by rw [← hj_eq, hzero, Nat.mul_zero]
      exact Nat.succ_ne_zero j this
    have hEq' := congrArg (fun x => x + 1) hEq
    have hdiv_eq : (i + 1) / p = (j + 1) / p := by
      simpa [Nat.sub_add_cancel hdiv_pos_i, Nat.sub_add_cancel hdiv_pos_j] using hEq'
    have hij1 : i + 1 = j + 1 := by rw [← hi_eq, ← hj_eq, hdiv_eq]
    omega
  · intro j hj
    dsimp [A, B] at hj ⊢
    simp only [mem_filter, mem_range] at hj ⊢
    rcases hj with ⟨hjlt, hno⟩
    let i := p * (j + 1) - 1
    have hp_pos : 0 < p := hp.pos
    have hmul_le : p * (j + 1) ≤ N := by
      have hjle : j + 1 ≤ N / p := by omega
      have := (Nat.le_div_iff_mul_le hp_pos).mp hjle
      simpa [mul_comm] using this
    have hi_succ : i + 1 = p * (j + 1) := by
      dsimp [i]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hp_pos (Nat.succ_pos j)))
    refine ⟨i, ?_, ?_⟩
    · constructor
      · omega
      · constructor
        · rw [hi_succ]; exact dvd_mul_right p (j + 1)
        · intro q hqmem hqdiv
          have hqprime := (hps q hqmem).1
          have hqne := (hps q hqmem).2
          have hqdivj : q ∣ j + 1 := by
            rw [hi_succ] at hqdiv
            exact (dvd_mul_cancel_prime_of_ne hp hqprime hqne).mp hqdiv
          exact hno q hqmem hqdivj
    · rw [hi_succ, Nat.mul_div_right _ hp_pos]
      omega
lemma phiCount_cons (N p : ℕ) (hp : Nat.Prime p) (ps : List ℕ)
    (hps : ∀ q ∈ ps, Nat.Prime q ∧ q ≠ p) :
    phiCount N (p :: ps) = phiCount N ps - phiCount (N / p) ps := by
  unfold phiCount
  have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.range N).filter fun i => ∀ q ∈ ps, ¬ q ∣ i + 1) (p := fun i => p ∣ i + 1)
  have hleft : ((Finset.range N).filter (fun i => ∀ q ∈ ps, ¬q ∣ i + 1)).filter (fun i => p ∣ i + 1)
      = (Finset.range N).filter (fun i => p ∣ i + 1 ∧ ∀ q ∈ ps, ¬ q ∣ i + 1) := by
    ext i; simp [and_comm, and_left_comm, and_assoc]
  have hright : ((Finset.range N).filter (fun i => ∀ q ∈ ps, ¬q ∣ i + 1)).filter (fun i => ¬ p ∣ i + 1)
      = (Finset.range N).filter (fun i => ∀ q ∈ p :: ps, ¬ q ∣ i + 1) := by
    ext i; simp [and_comm, and_left_comm, and_assoc]
  rw [hleft, hright, removed_multiples_card N p hp ps hps] at hpart
  exact Nat.eq_sub_of_add_eq (by rw [Nat.add_comm]; exact hpart)
lemma phiCount_nil (N : ℕ) : phiCount N [] = N := by
  unfold phiCount; simp
lemma phiCount_all_gt (N : ℕ) (ps : List ℕ) (hgt : ∀ q ∈ ps, N < q) : phiCount N ps = N := by
  unfold phiCount
  have hfilter : (Finset.range N).filter (fun i => ∀ q ∈ ps, ¬ q ∣ i + 1) = Finset.range N := by
    apply Finset.filter_true_of_mem
    intro i hi q hq hd
    have hi1 : i + 1 ≤ N := Nat.succ_le_of_lt (by simpa using hi)
    have hqgt : N < q := hgt q hq
    have hpos : 0 < i + 1 := Nat.succ_pos i
    exact (Nat.not_dvd_of_pos_of_lt hpos (lt_of_le_of_lt hi1 hqgt)) hd
  rw [hfilter, Finset.card_range]
def Inc (ps : List ℕ) : Prop := ps.Pairwise (· < ·)
lemma Inc_tail_gt {p q : ℕ} {ps : List ℕ} (hinc : Inc (p::ps)) (hq : q ∈ ps) : p < q := by
  exact List.rel_of_pairwise_cons hinc hq
def primes46 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]
theorem primes46_inc : Inc primes46 := by
  unfold Inc primes46
  decide
theorem primes46_prime : ∀ p ∈ primes46, Nat.Prime p := by decide
def sumDiv (N : Nat) : List Nat -> Nat
| [] => 0
| p::ps => N / p + sumDiv N ps
def phiOpt : Nat -> List Nat -> Nat
| N, [] => N
| N, p::ps => if N < p then N else if N < p*p then N - sumDiv N (p::ps) else phiOpt N ps - phiOpt (N/p) ps
lemma sumDiv_eq_zero_of_all_gt {N : Nat} : ∀ ps : List Nat, (∀ q ∈ ps, N < q) -> sumDiv N ps = 0
| [], h => rfl
| p::ps, h => by
    simp [sumDiv, Nat.div_eq_of_lt (h p (by simp)), sumDiv_eq_zero_of_all_gt ps (by intro q hq; exact h q (by simp [hq]))]
lemma phiCount_eq_sub_sumDiv_of_sq (N : Nat) : ∀ ps : List Nat, Inc ps -> (∀ p ∈ ps, Nat.Prime p) -> (∀ p ∈ ps, N < p*p) ->
    phiCount N ps = N - sumDiv N ps
| [], hinc, hpr, hsq => by simp [phiCount_nil, sumDiv]
| p::ps, hinc, hpr, hsq => by
    have hp : Nat.Prime p := hpr p (by simp)
    by_cases hpN : N < p
    · have hgt : ∀ q ∈ p::ps, N < q := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hqps
        · exact hpN
        · exact lt_trans hpN (Inc_tail_gt hinc hqps)
      rw [phiCount_all_gt N (p::ps) hgt]
      have hsum : sumDiv N (p::ps) = 0 := sumDiv_eq_zero_of_all_gt (p::ps) hgt
      simp [hsum]
    · have hinc_tail : Inc ps := List.Pairwise.of_cons hinc
      have hpr_tail : ∀ q ∈ ps, Nat.Prime q := by intro q hq; exact hpr q (by simp [hq])
      have hsq_tail : ∀ q ∈ ps, N < q*q := by intro q hq; exact hsq q (by simp [hq])
      have hne : ∀ q ∈ ps, Nat.Prime q ∧ q ≠ p := by
        intro q hq; exact ⟨hpr_tail q hq, ne_of_gt (Inc_tail_gt hinc hq)⟩
      rw [phiCount_cons N p hp ps hne]
      rw [phiCount_eq_sub_sumDiv_of_sq N ps hinc_tail hpr_tail hsq_tail]
      have hNp_lt_p : N / p < p := by
        rw [Nat.div_lt_iff_lt_mul hp.pos]
        exact hsq p (by simp)
      have hsmall : phiCount (N / p) ps = N / p := by
        apply phiCount_all_gt
        intro q hq
        exact lt_trans hNp_lt_p (Inc_tail_gt hinc hq)
      rw [hsmall]
      simp [sumDiv]
      omega
opaque phiOpt_eq_phiCount (N : Nat) (ps : List Nat) (hinc : Inc ps) (hprime : ∀ p ∈ ps, Nat.Prime p) :
    phiOpt N ps = phiCount N ps := by
  induction ps generalizing N with
  | nil => simp [phiOpt, phiCount_nil]
  | cons p ps ih =>
      have hp : Nat.Prime p := hprime p (by simp)
      have hinc_tail : Inc ps := List.Pairwise.of_cons hinc
      have hprime_tail : ∀ q ∈ ps, Nat.Prime q := by intro q hq; exact hprime q (by simp [hq])
      simp [phiOpt]
      by_cases hNp : N < p
      · rw [if_pos hNp]
        have hgt : ∀ q ∈ p::ps, N < q := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hqps
          · exact hNp
          · exact lt_trans hNp (Inc_tail_gt hinc hqps)
        exact (phiCount_all_gt N (p::ps) hgt).symm
      · rw [if_neg hNp]
        by_cases hsq : N < p*p
        · rw [if_pos hsq]
          have hall : ∀ q ∈ p::ps, N < q*q := by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hqps
            · exact hsq
            · have hpq := Inc_tail_gt hinc hqps
              nlinarith
          exact (phiCount_eq_sub_sumDiv_of_sq N (p::ps) hinc hprime hall).symm
        · rw [if_neg hsq]
          have hne : ∀ q ∈ ps, Nat.Prime q ∧ q ≠ p := by intro q hq; exact ⟨hprime_tail q hq, ne_of_gt (Inc_tail_gt hinc hq)⟩
          rw [phiCount_cons N p hp ps hne]
          rw [ih N hinc_tail hprime_tail, ih (N/p) hinc_tail hprime_tail]
opaque phiOpt_primes46_cert : phiOpt 8567964 primes46 = 894773 := by decide
opaque phiCount_primes46_lower : 894773 ≤ phiCount 8567964 primes46 := by
  rw [← phiOpt_eq_phiCount 8567964 primes46 primes46_inc primes46_prime]
  rw [phiOpt_primes46_cert]
def primes22 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79]
def base24 : List ℕ := [83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]
def roughC (y : ℕ) : Finset ℕ := (Finset.Icc 1 y).filter fun c => ∀ p ∈ primes22, ¬ p ∣ c
lemma roughC_card_eq_phiCount (y : ℕ) : (roughC y).card = phiCount y primes22 := by
  unfold roughC phiCount
  let A := (Finset.Icc 1 y).filter fun c => ∀ p ∈ primes22, ¬ p ∣ c
  let B := (Finset.range y).filter fun i => ∀ q ∈ primes22, ¬ q ∣ i + 1
  change A.card = B.card
  refine Finset.card_bij (fun c hc => c - 1) ?_ ?_ ?_
  · intro c hc
    dsimp [A,B] at hc ⊢
    simp only [mem_filter, mem_Icc, mem_range] at hc ⊢
    rcases hc with ⟨⟨h1, hy⟩, hgood⟩
    constructor
    · omega
    · simpa [Nat.sub_add_cancel h1] using hgood
  · intro c hc d hd heq
    dsimp [A] at hc hd
    simp only [mem_filter, mem_Icc] at hc hd
    have hcpos : 1 ≤ c := hc.1.1
    have hdpos : 1 ≤ d := hd.1.1
    have hEq' : c - 1 = d - 1 := by simpa using heq
    calc
      c = c - 1 + 1 := (Nat.sub_add_cancel hcpos).symm
      _ = d - 1 + 1 := by rw [hEq']
      _ = d := Nat.sub_add_cancel hdpos
  · intro i hi
    dsimp [A,B] at hi ⊢
    simp only [mem_filter, mem_range, mem_Icc] at hi ⊢
    rcases hi with ⟨hiy, hgood⟩
    refine ⟨i+1, ?_, ?_⟩
    · constructor
      · constructor <;> omega
      · exact hgood
    · omega
def lowW (tail : List ℕ) (j : ℕ) : Finset ℕ := insert 1 ((base24 ++ tail.take j).toFinset)
theorem base24_nodup : base24.Nodup := by decide
theorem base24_len : base24.length = 24 := by decide
theorem base24_gt1 : ∀ x ∈ base24, 1 < x := by decide
theorem base24_lt200 : ∀ x ∈ base24, x < 200 := by decide
theorem base24_not_mem_tail_of_tail_ge200 {tail : List ℕ}
    (htail_ge : ∀ x ∈ tail, 200 ≤ x) : ∀ x ∈ base24, x ∉ tail := by
  intro x hx hxt
  have hxlt : x < 200 := base24_lt200 x hx
  have hxge := htail_ge x hxt
  omega
lemma card_lowW (tail : List ℕ) (j : ℕ) (htail_nodup : tail.Nodup)
    (htail_ge : ∀ x ∈ tail, 200 ≤ x) :
    (lowW tail j).card = (tail.take j).length + 25 := by
  unfold lowW
  have hbase_tail_disj : Disjoint base24.toFinset (tail.take j).toFinset := by
    rw [Finset.disjoint_left]
    intro x hxb hxt
    simp at hxb hxt
    have hxnot := base24_not_mem_tail_of_tail_ge200 htail_ge x hxb
    exact hxnot (List.mem_of_mem_take hxt)
  have h1not : 1 ∉ (base24 ++ tail.take j).toFinset := by
    simp
    constructor
    · intro h
      have := base24_gt1 1 h
      omega
    · intro h
      have hmemtail : 1 ∈ tail := List.mem_of_mem_take h
      have := htail_ge 1 hmemtail
      omega
  rw [Finset.card_insert_of_notMem h1not]
  rw [List.toFinset_append, Finset.card_union_of_disjoint hbase_tail_disj]
  have htake_nodup : (tail.take j).Nodup := List.Pairwise.take htail_nodup
  rw [List.toFinset_card_of_nodup base24_nodup, List.toFinset_card_of_nodup htake_nodup, base24_len]
  omega
lemma mem_take_lt_get {tail : List ℕ} (hinc : Inc tail) {j : ℕ} (hj : j < tail.length)
    {x : ℕ} (hx : x ∈ tail.take j) : x < tail.get ⟨j, hj⟩ := by
  have hxmem : x ∈ tail := List.mem_of_mem_take hx
  have hidxlt : tail.idxOf x < j := by
    simpa using (List.mem_take_iff_idxOf_lt hxmem).mp hx
  have hidxlen : tail.idxOf x < tail.length := List.idxOf_lt_length_iff.mpr hxmem
  have hrel := List.Pairwise.rel_get_of_lt hinc (a := ⟨tail.idxOf x, hidxlen⟩) (b := ⟨j, hj⟩) (by simpa using hidxlt)
  have hxget : tail.get ⟨tail.idxOf x, hidxlen⟩ = x := List.idxOf_get hidxlen
  simpa [hxget] using hrel
theorem primes22_prime : ∀ p ∈ primes22, Nat.Prime p := by decide
theorem base24_prime : ∀ p ∈ base24, Nat.Prime p := by decide
theorem primes22_le79 : ∀ p ∈ primes22, p ≤ 79 := by decide
theorem base24_ge83 : ∀ p ∈ base24, 83 ≤ p := by decide
def cofC (N q : ℕ) : Finset ℕ := (Finset.Icc q (N / q)).filter fun c => ∀ p ∈ primes22, ¬ p ∣ c
lemma lowW_subset_roughC {N : ℕ} {tail : List ℕ} (hinc : Inc tail)
    (htail_prime : ∀ x ∈ tail, Nat.Prime x ∧ 200 ≤ x) {j : ℕ} (hj : j < tail.length)
    (hqle : tail.get ⟨j,hj⟩ ≤ N / tail.get ⟨j,hj⟩) :
    lowW tail j ⊆ roughC (N / tail.get ⟨j,hj⟩) := by
  intro c hc
  unfold lowW at hc
  unfold roughC
  simp only [Finset.mem_insert, List.mem_toFinset, List.mem_append, Finset.mem_filter, Finset.mem_Icc] at hc ⊢
  have hqge200 : 200 ≤ tail.get ⟨j,hj⟩ := (htail_prime _ (List.get_mem _ _)).2
  rcases hc with hc1 | (hcbase | hctail)
  · subst c
    constructor
    · constructor
      · norm_num
      · omega
    · intro p hp hdiv
      have hpprime := primes22_prime p hp
      have hpeq1 := Nat.dvd_one.mp hdiv
      exact hpprime.ne_one hpeq1
  · have hcprime := base24_prime c hcbase
    have hclt200 := base24_lt200 c hcbase
    constructor
    · constructor
      · exact Nat.succ_le_of_lt hcprime.pos
      · omega
    · intro p hp hdiv
      have hpprime := primes22_prime p hp
      have hplt : p < c := by
        have hp_le79 : p ≤ 79 := primes22_le79 p hp
        have hc_ge83 : 83 ≤ c := base24_ge83 c hcbase
        omega
      have h := hcprime.eq_one_or_self_of_dvd p hdiv
      rcases h with h | h
      · exact hpprime.ne_one h
      · exact hplt.ne h
  · have hctailmem : c ∈ tail := List.mem_of_mem_take hctail
    have hcprime := (htail_prime c hctailmem).1
    have hcltq : c < tail.get ⟨j,hj⟩ := mem_take_lt_get hinc hj hctail
    constructor
    · constructor
      · exact Nat.succ_le_of_lt hcprime.pos
      · omega
    · intro p hp hdiv
      have hpprime := primes22_prime p hp
      have hp_le79 : p ≤ 79 := primes22_le79 p hp
      have htail_ge200 := (htail_prime c hctailmem).2
      have hplt : p < c := by omega
      have h := hcprime.eq_one_or_self_of_dvd p hdiv
      rcases h with h | h
      · exact hpprime.ne_one h
      · exact hplt.ne h
lemma cofC_subset_roughC {N q : ℕ} (hq1 : 1 ≤ q) : cofC N q ⊆ roughC (N / q) := by
  intro c hc
  unfold cofC at hc
  unfold roughC
  simp only [Finset.mem_filter, Finset.mem_Icc] at hc ⊢
  exact ⟨⟨le_trans hq1 hc.1.1, hc.1.2⟩, hc.2⟩
lemma lowW_disjoint_cofC {N : ℕ} {tail : List ℕ} (hinc : Inc tail)
    (htail_ge : ∀ x ∈ tail, 200 ≤ x) {j : ℕ} (hj : j < tail.length) :
    Disjoint (lowW tail j) (cofC N (tail.get ⟨j,hj⟩)) := by
  rw [Finset.disjoint_left]
  intro c hc hcof
  unfold cofC at hcof
  simp only [Finset.mem_filter, Finset.mem_Icc] at hcof
  unfold lowW at hc
  simp only [Finset.mem_insert, List.mem_toFinset, List.mem_append] at hc
  have hqge : 200 ≤ tail.get ⟨j,hj⟩ := htail_ge _ (List.get_mem _ _)
  have hltq : c < tail.get ⟨j,hj⟩ := by
    rcases hc with rfl | (hcbase | hctail)
    · omega
    · have hclt200 := base24_lt200 c hcbase
      omega
    · exact mem_take_lt_get hinc hj hctail
  omega
lemma cofC_card_add_lowW_card_le_roughC {N : ℕ} {tail : List ℕ} (hinc : Inc tail)
    (htail_prime : ∀ x ∈ tail, Nat.Prime x ∧ 200 ≤ x) {j : ℕ} (hj : j < tail.length)
    (hqle : tail.get ⟨j,hj⟩ ≤ N / tail.get ⟨j,hj⟩) :
    (cofC N (tail.get ⟨j,hj⟩)).card + (lowW tail j).card ≤
      (roughC (N / tail.get ⟨j,hj⟩)).card := by
  have hq1 : 1 ≤ tail.get ⟨j,hj⟩ := by
    have := (htail_prime (tail.get ⟨j,hj⟩) (List.get_mem tail ⟨j,hj⟩)).2
    omega
  have hsub1 := cofC_subset_roughC (N := N) (q := tail.get ⟨j,hj⟩) hq1
  have hsub2 := lowW_subset_roughC (N := N) hinc htail_prime hj hqle
  have hdisj := (lowW_disjoint_cofC (N := N) hinc (fun x hx => (htail_prime x hx).2) hj).symm
  have hunion_sub : (cofC N (tail.get ⟨j,hj⟩) ∪ lowW tail j) ⊆ roughC (N / tail.get ⟨j,hj⟩) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hsub1 hx
    · exact hsub2 hx
  calc
    (cofC N (tail.get ⟨j,hj⟩)).card + (lowW tail j).card
        = (cofC N (tail.get ⟨j,hj⟩) ∪ lowW tail j).card := by
            rw [Finset.card_union_of_disjoint hdisj]
    _ ≤ (roughC (N / tail.get ⟨j,hj⟩)).card := Finset.card_le_card hunion_sub
def small46 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]
def primes16 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53]
def goodQ (q : ℕ) : Bool := primes16.all (fun p => q % p != 0)
def genTail : List ℕ := (List.range (2928 - 200)).map (fun i => 200 + i) |>.filter goodQ
theorem primes16_props : ∀ p ∈ primes16, Nat.Prime p ∧ p ≤ 53 := by decide
theorem prime_lt200_mem_small46 (p : ℕ) (hp : Nat.Prime p) (hlt : p < 200) : p ∈ small46 := by
  interval_cases p <;> simp [small46] at hp ⊢ <;> norm_num at hp
theorem prime_le53_mem_primes16 (p : ℕ) (hp : Nat.Prime p) (hle : p ≤ 53) : p ∈ primes16 := by
  interval_cases p <;> simp [primes16] at hp ⊢ <;> norm_num at hp
theorem goodQ_prime (q : ℕ) (hlo : 200 ≤ q) (hhi : q ≤ 2927) (hg : goodQ q = true) : Nat.Prime q := by
  by_contra hn
  have hpos : 0 < q := by omega
  have hmfprime : Nat.Prime (Nat.minFac q) := Nat.minFac_prime (by omega)
  have hmfdvd : Nat.minFac q ∣ q := Nat.minFac_dvd q
  have hsq : Nat.minFac q ^ 2 ≤ q := Nat.minFac_sq_le_self hpos hn
  have hle53 : Nat.minFac q ≤ 53 := by
    by_contra h
    have h59 : 59 ≤ Nat.minFac q := by
      by_contra hlt
      interval_cases Nat.minFac q <;> norm_num at hmfprime
    have : 59^2 ≤ Nat.minFac q ^ 2 := by gcongr
    nlinarith [hhi]
  have hmem := prime_le53_mem_primes16 (Nat.minFac q) hmfprime hle53
  have hmod : q % Nat.minFac q = 0 := Nat.mod_eq_zero_of_dvd hmfdvd
  unfold goodQ at hg
  rw [List.all_eq_true] at hg
  have := hg (Nat.minFac q) hmem
  simp [hmod] at this
lemma mem_genTail_iff (q : ℕ) : q ∈ genTail ↔ 200 ≤ q ∧ q < 2928 ∧ goodQ q = true := by
  simp only [genTail, List.mem_filter, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hg⟩
    exact ⟨by omega, by omega, hg⟩
  · rintro ⟨hlo, hhi, hg⟩
    refine ⟨⟨q - 200, ?_, by omega⟩, hg⟩
    omega
theorem genTail_prime_of_mem (q : ℕ) (hq : q ∈ genTail) : Nat.Prime q ∧ 200 ≤ q ∧ q ≤ 2927 := by
  have h := (mem_genTail_iff q).mp hq
  exact ⟨goodQ_prime q h.1 (by omega) h.2.2, h.1, by omega⟩
theorem prime_mem_genTail (q : ℕ) (hp : Nat.Prime q) (hlo : 200 ≤ q) (hhi : q ≤ 2927) : q ∈ genTail := by
  rw [mem_genTail_iff]
  refine ⟨hlo, by omega, ?_⟩
  unfold goodQ
  rw [List.all_eq_true]
  intro p hpmem
  have hprops : p ∈ primes16 := hpmem
  have hpprime : Nat.Prime p := (primes16_props p hprops).1
  have hplt : p < q := by
    have : p ≤ 53 := (primes16_props p hprops).2
    omega
  have hndvd : ¬ p ∣ q := by
    intro hd
    have h := hp.eq_one_or_self_of_dvd p hd
    rcases h with h | h
    · exact hpprime.ne_one h
    · exact hplt.ne h
  have hmodne : q % p ≠ 0 := by
    intro hm
    exact hndvd (Nat.dvd_of_mod_eq_zero hm)
  cases h : q % p <;> simp [hmodne] at h ⊢
theorem primes22_mem_primes46 : ∀ p ∈ primes22, p ∈ primes46 := by decide
def roughC46 (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter fun c => ∀ p ∈ primes46, ¬ p ∣ c
def compSurvivors (N : ℕ) : Finset ℕ := (roughC46 N).filter fun m => m ≠ 1 ∧ ¬ Nat.Prime m
def qOfGen (q : ℕ) (hq : q ∈ genTail) : Fin genTail.length := ⟨genTail.idxOf q, List.idxOf_lt_length_iff.mpr hq⟩
def tailSigma (N : ℕ) : Finset (Σ j : Fin genTail.length, ℕ) :=
  (Finset.univ : Finset (Fin genTail.length)).sigma fun j => cofC N (genTail.get j)
opaque minFac_mem_genTail_of_compSurvivor {m : ℕ} (hm : m ∈ compSurvivors 8567964) :
    Nat.minFac m ∈ genTail := by
  unfold compSurvivors roughC46 at hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm
  rcases hm with ⟨⟨⟨hm1le, hmN⟩, hno⟩, hmne1, hnprime⟩
  have hmpos : 0 < m := by omega
  have hqprime : Nat.Prime (Nat.minFac m) := Nat.minFac_prime hmne1
  have hqdvd : Nat.minFac m ∣ m := Nat.minFac_dvd m
  have hqnotlt200 : ¬ Nat.minFac m < 200 := by
    intro hlt
    have hmem46 : Nat.minFac m ∈ primes46 := by
      have hs : Nat.minFac m ∈ small46 := prime_lt200_mem_small46 (Nat.minFac m) hqprime hlt
      simpa [small46, primes46] using hs
    exact hno (Nat.minFac m) hmem46 hqdvd
  have hqge200 : 200 ≤ Nat.minFac m := by omega
  have hsq : Nat.minFac m ^ 2 ≤ m := Nat.minFac_sq_le_self hmpos hnprime
  have hqle2927 : Nat.minFac m ≤ 2927 := by
    nlinarith [hsq, hmN]
  exact prime_mem_genTail (Nat.minFac m) hqprime hqge200 hqle2927
opaque comp_to_tailSigma_maps {m : ℕ} (hm : m ∈ compSurvivors 8567964) :
    (Sigma.mk (qOfGen (Nat.minFac m) (minFac_mem_genTail_of_compSurvivor hm)) (m / Nat.minFac m)) ∈
      tailSigma 8567964 := by
  unfold tailSigma
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
  let j := qOfGen (Nat.minFac m) (minFac_mem_genTail_of_compSurvivor hm)
  change m / Nat.minFac m ∈ cofC 8567964 (genTail.get j)
  have hget : genTail.get j = Nat.minFac m := by
    dsimp [j, qOfGen]
    exact List.idxOf_get (List.idxOf_lt_length_iff.mpr (minFac_mem_genTail_of_compSurvivor hm))
  rw [hget]
  unfold compSurvivors roughC46 at hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm
  rcases hm with ⟨⟨⟨hm1le, hmN⟩, hno⟩, hmne1, hnprime⟩
  have hmpos : 0 < m := by omega
  have hqprime : Nat.Prime (Nat.minFac m) := Nat.minFac_prime hmne1
  have hqdvd : Nat.minFac m ∣ m := Nat.minFac_dvd m
  have hqpos : 0 < Nat.minFac m := hqprime.pos
  have hsq : Nat.minFac m ^ 2 ≤ m := Nat.minFac_sq_le_self hmpos hnprime
  unfold cofC
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · constructor
    · rw [Nat.le_div_iff_mul_le hqpos]
      simpa [pow_two] using hsq
    · exact Nat.div_le_div_right hmN
  · intro p hp hpdvd
    have hpmem46 : p ∈ primes46 := primes22_mem_primes46 p hp
    have hmul : Nat.minFac m * (m / Nat.minFac m) = m := Nat.mul_div_cancel' hqdvd
    have hpdm : p ∣ m := by
      rw [← hmul]
      exact dvd_mul_of_dvd_right hpdvd (Nat.minFac m)
    exact hno p hpmem46 hpdm
set_option maxRecDepth 5000 in
opaque compSurvivors_card_le_tailSigma :
    (compSurvivors 8567964).card ≤ (tailSigma 8567964).card := by
  let F : (compSurvivors 8567964) → (tailSigma 8567964) := fun x =>
    ⟨Sigma.mk (qOfGen (Nat.minFac x.1) (minFac_mem_genTail_of_compSurvivor x.2)) (x.1 / Nat.minFac x.1),
      comp_to_tailSigma_maps x.2⟩
  refine Finset.card_le_card_of_injective (f := F) ?_
  intro a b h
  apply Subtype.ext
  have hval : (F a).1 = (F b).1 := congrArg Subtype.val h
  dsimp [F] at hval
  have hqa_mem := minFac_mem_genTail_of_compSurvivor a.2
  have hqb_mem := minFac_mem_genTail_of_compSurvivor b.2
  let ja := qOfGen (Nat.minFac a.1) hqa_mem
  let jb := qOfGen (Nat.minFac b.1) hqb_mem
  have hget_a : genTail.get ja = Nat.minFac a.1 := by
    dsimp [ja, qOfGen]
    exact List.idxOf_get (List.idxOf_lt_length_iff.mpr hqa_mem)
  have hget_b : genTail.get jb = Nat.minFac b.1 := by
    dsimp [jb, qOfGen]
    exact List.idxOf_get (List.idxOf_lt_length_iff.mpr hqb_mem)
  change (Sigma.mk ja (a.1 / Nat.minFac a.1) : Σ j : Fin genTail.length, ℕ) = Sigma.mk jb (b.1 / Nat.minFac b.1) at hval
  have hidx : ja = jb := (Sigma.ext_iff.mp hval).1
  subst jb
  have hquot : a.1 / Nat.minFac a.1 = b.1 / Nat.minFac b.1 := by
    simpa using congrArg Sigma.snd hval
  have hq : Nat.minFac a.1 = Nat.minFac b.1 := by
    rw [← hget_a, ← hget_b, hidx]
  have hda : Nat.minFac a.1 ∣ a.1 := Nat.minFac_dvd a.1
  have hdb : Nat.minFac b.1 ∣ b.1 := Nat.minFac_dvd b.1
  have hmula : Nat.minFac a.1 * (a.1 / Nat.minFac a.1) = a.1 := Nat.mul_div_cancel' hda
  have hmulb : Nat.minFac b.1 * (b.1 / Nat.minFac b.1) = b.1 := Nat.mul_div_cancel' hdb
  calc
    (a.1) = Nat.minFac a.1 * (a.1 / Nat.minFac a.1) := hmula.symm
    _ = Nat.minFac b.1 * (b.1 / Nat.minFac b.1) := by rw [hquot, hq]
    _ = b.1 := hmulb
theorem primes22_inc : Inc primes22 := by
  unfold Inc primes22
  decide
theorem primes22_prime_all : ∀ p ∈ primes22, Nat.Prime p := primes22_prime
theorem genTail_inc : Inc genTail := by
  unfold Inc genTail goodQ primes16
  decide
theorem genTail_prime_ge200 : ∀ x ∈ genTail, Nat.Prime x ∧ 200 ≤ x := by
  intro x hx
  have h := genTail_prime_of_mem x hx
  exact ⟨h.1, h.2.1⟩
theorem genTail_ge211 : ∀ x ∈ genTail, 211 ≤ x := by
  intro x hx
  have hmem := (mem_genTail_iff x).mp hx
  by_contra hlt
  have hxlo : 200 ≤ x := hmem.1
  have hxhi : x ≤ 210 := by omega
  interval_cases x <;> simp [mem_genTail_iff, goodQ, primes16] at hx
theorem genTail_nodup : genTail.Nodup := by
  unfold genTail goodQ primes16
  decide
theorem genTail_ge200 : ∀ x ∈ genTail, 200 ≤ x := fun x hx => (genTail_prime_ge200 x hx).2
opaque qOf_sq_le_N (j : ℕ) (hj : j < genTail.length) :
    genTail.get ⟨j,hj⟩ ≤ 8567964 / genTail.get ⟨j,hj⟩ := by
  have hle : genTail.get ⟨j,hj⟩ ≤ 2927 := (genTail_prime_of_mem _ (List.get_mem _ _)).2.2
  have hpos : 0 < genTail.get ⟨j,hj⟩ := (genTail_prime_of_mem _ (List.get_mem _ _)).1.pos
  rw [Nat.le_div_iff_mul_le hpos]
  nlinarith
opaque roughC46_card_eq_phiCount (N : ℕ) : (roughC46 N).card = phiCount N primes46 := by
  unfold roughC46 phiCount
  let A := (Finset.Icc 1 N).filter fun c => ∀ p ∈ primes46, ¬ p ∣ c
  let B := (Finset.range N).filter fun i => ∀ q ∈ primes46, ¬ q ∣ i + 1
  change A.card = B.card
  refine Finset.card_bij (fun c hc => c - 1) ?_ ?_ ?_
  · intro c hc
    dsimp [A,B] at hc ⊢
    simp only [mem_filter, mem_Icc, mem_range] at hc ⊢
    rcases hc with ⟨⟨h1, hN⟩, hgood⟩
    exact ⟨by omega, by simpa [Nat.sub_add_cancel h1] using hgood⟩
  · intro c hc d hd heq
    dsimp [A] at hc hd
    simp only [mem_filter, mem_Icc] at hc hd
    have hcpos : 1 ≤ c := hc.1.1
    have hdpos : 1 ≤ d := hd.1.1
    have hEq' : c - 1 = d - 1 := by simpa using heq
    calc
      c = c - 1 + 1 := (Nat.sub_add_cancel hcpos).symm
      _ = d - 1 + 1 := by rw [hEq']
      _ = d := Nat.sub_add_cancel hdpos
  · intro i hi
    dsimp [A,B] at hi ⊢
    simp only [mem_filter, mem_range, mem_Icc] at hi ⊢
    rcases hi with ⟨hiN, hgood⟩
    refine ⟨i+1, ?_, ?_⟩
    · exact ⟨⟨by omega, by omega⟩, hgood⟩
    · omega
opaque roughC46_card_le_one_primecount_comp (N : ℕ) :
    (roughC46 N).card ≤ 1 + Nat.count Nat.Prime (N+1) + (compSurvivors N).card := by
  let primeR := (roughC46 N).filter Nat.Prime
  have hsub : roughC46 N ⊆ insert 1 (primeR ∪ compSurvivors N) := by
    intro m hm
    by_cases h1 : m = 1
    · simp [h1]
    · by_cases hp : Nat.Prime m
      · simp [primeR, hm, hp]
      · simp [compSurvivors, hm, h1, hp]
  have hcard := Finset.card_le_card hsub
  have hprime_sub : primeR ⊆ (Finset.range (N+1)).filter Nat.Prime := by
    intro m hm
    have hmrough : m ∈ roughC46 N := (Finset.mem_filter.mp hm).1
    have hp : Nat.Prime m := (Finset.mem_filter.mp hm).2
    simp only [Finset.mem_filter, Finset.mem_range]
    unfold roughC46 at hmrough
    simp only [Finset.mem_filter, Finset.mem_Icc] at hmrough
    exact ⟨by omega, hp⟩
  have hprime_card : primeR.card ≤ Nat.count Nat.Prime (N+1) := by
    rw [Nat.count_eq_card_filter_range]
    exact Finset.card_le_card hprime_sub
  have hmain : (roughC46 N).card ≤ (insert 1 (primeR ∪ compSurvivors N)).card := hcard
  have hbound : (insert 1 (primeR ∪ compSurvivors N)).card ≤ 1 + primeR.card + (compSurvivors N).card := by
    calc
      (insert 1 (primeR ∪ compSurvivors N)).card ≤ 1 + (primeR ∪ compSurvivors N).card := by
        by_cases hmem : 1 ∈ primeR ∪ compSurvivors N
        · rw [Finset.insert_eq_of_mem hmem]; omega
        · rw [Finset.card_insert_of_notMem hmem]
          omega
      _ ≤ 1 + primeR.card + (compSurvivors N).card := by
        have := Finset.card_union_le (s := primeR) (t := compSurvivors N)
        omega
  omega
opaque endpoint0_cert : phiOpt 3160 primes22 = 425 := by decide
opaque endpoint1_cert : phiOpt 3306 primes22 = 443 := by decide
opaque endpoint2_cert : phiOpt 3515 primes22 = 469 := by decide
opaque endpoint3_cert : phiOpt 3672 primes22 = 491 := by decide
opaque endpoint4_cert : phiOpt 3889 primes22 = 518 := by decide
opaque endpoint5_cert : phiOpt 4117 primes22 = 545 := by decide
opaque endpoint6_cert : phiOpt 4329 primes22 = 570 := by decide
opaque endpoint7_cert : phiOpt 4589 primes22 = 599 := by decide
opaque endpoint8_cert : phiOpt 4921 primes22 = 636 := by decide
opaque endpoint9_cert : phiOpt 5170 primes22 = 667 := by decide
opaque endpoint10_cert : phiOpt 5467 primes22 = 700 := by decide
opaque endpoint11_cert : phiOpt 5785 primes22 = 738 := by decide
opaque endpoint12_cert : phiOpt 6021 primes22 = 764 := by decide
opaque endpoint13_cert : phiOpt 6295 primes22 = 797 := by decide
opaque endpoint14_cert : phiOpt 6709 primes22 = 845 := by decide
opaque endpoint15_cert : phiOpt 7063 primes22 = 887 := by decide
opaque endpoint16_cert : phiOpt 7443 primes22 = 923 := by decide
opaque endpoint17_cert : phiOpt 7882 primes22 = 977 := by decide
opaque endpoint18_cert : phiOpt 8491 primes22 = 1043 := by decide
opaque endpoint19_cert : phiOpt 8860 primes22 = 1089 := by decide
opaque endpoint20_cert : phiOpt 9446 primes22 = 1162 := by decide
opaque endpoint21_cert : phiOpt 10044 primes22 = 1229 := by decide
opaque endpoint22_cert : phiOpt 10590 primes22 = 1293 := by decide
opaque endpoint23_cert : phiOpt 11408 primes22 = 1387 := by decide
opaque endpoint24_cert : phiOpt 11916 primes22 = 1445 := by decide
opaque endpoint25_cert : phiOpt 12731 primes22 = 1545 := by decide
opaque endpoint26_cert : phiOpt 13366 primes22 = 1618 := by decide
opaque endpoint27_cert : phiOpt 14303 primes22 = 1724 := by decide
opaque endpoint28_cert : phiOpt 15057 primes22 = 1818 := by decide
opaque endpoint29_cert : phiOpt 15837 primes22 = 1916 := by decide
opaque endpoint30_cert : phiOpt 17170 primes22 = 2071 := by decide
opaque endpoint31_cert : phiOpt 17887 primes22 = 2158 := by decide
opaque endpoint32_cert : phiOpt 18748 primes22 = 2260 := by decide
opaque endpoint33_cert : phiOpt 19879 primes22 = 2395 := by decide
opaque endpoint34_cert : phiOpt 20448 primes22 = 2467 := by decide
opaque endpoint35_cert : phiOpt 21581 primes22 = 2602 := by decide
opaque endpoint36_cert : phiOpt 22606 primes22 = 2726 := by decide
opaque endpoint37_cert : phiOpt 23345 primes22 = 2820 := by decide
opaque endpoint38_cert : phiOpt 24691 primes22 = 2983 := by decide
opaque endpoint39_cert : phiOpt 25885 primes22 = 3126 := by decide
opaque endpoint40_cert : phiOpt 27908 primes22 = 3372 := by decide
opaque endpoint41_cert : phiOpt 30490 primes22 = 3683 := by decide
opaque endpoint42_cert : phiOpt 31851 primes22 = 3849 := by decide
opaque endpoint43_cert : phiOpt 34135 primes22 = 4133 := by decide
opaque endpoint44_cert : phiOpt 35849 primes22 = 4342 := by decide
opaque endpoint45_cert : phiOpt 37744 primes22 = 4579 := by decide
opaque endpoint46_cert : phiOpt 38421 primes22 = 4661 := by decide
opaque endpoint47_cert : phiOpt 40606 primes22 = 4926 := by decide
def epPair_0_0 (y : ℕ) : ℕ × ℕ := (3160,425)
def epPair_1_1 (y : ℕ) : ℕ × ℕ := (3306,443)
def epPair_2_2 (y : ℕ) : ℕ × ℕ := (3515,469)
def epPair_3_3 (y : ℕ) : ℕ × ℕ := (3672,491)
def epPair_4_4 (y : ℕ) : ℕ × ℕ := (3889,518)
def epPair_5_5 (y : ℕ) : ℕ × ℕ := (4117,545)
def epPair_6_6 (y : ℕ) : ℕ × ℕ := (4329,570)
def epPair_7_7 (y : ℕ) : ℕ × ℕ := (4589,599)
def epPair_8_8 (y : ℕ) : ℕ × ℕ := (4921,636)
def epPair_9_9 (y : ℕ) : ℕ × ℕ := (5170,667)
def epPair_10_10 (y : ℕ) : ℕ × ℕ := (5467,700)
def epPair_11_11 (y : ℕ) : ℕ × ℕ := (5785,738)
def epPair_12_12 (y : ℕ) : ℕ × ℕ := (6021,764)
def epPair_13_13 (y : ℕ) : ℕ × ℕ := (6295,797)
def epPair_14_14 (y : ℕ) : ℕ × ℕ := (6709,845)
def epPair_15_15 (y : ℕ) : ℕ × ℕ := (7063,887)
def epPair_16_16 (y : ℕ) : ℕ × ℕ := (7443,923)
def epPair_17_17 (y : ℕ) : ℕ × ℕ := (7882,977)
def epPair_18_18 (y : ℕ) : ℕ × ℕ := (8491,1043)
def epPair_19_19 (y : ℕ) : ℕ × ℕ := (8860,1089)
def epPair_20_20 (y : ℕ) : ℕ × ℕ := (9446,1162)
def epPair_21_21 (y : ℕ) : ℕ × ℕ := (10044,1229)
def epPair_22_22 (y : ℕ) : ℕ × ℕ := (10590,1293)
def epPair_23_23 (y : ℕ) : ℕ × ℕ := (11408,1387)
def epPair_24_24 (y : ℕ) : ℕ × ℕ := (11916,1445)
def epPair_25_25 (y : ℕ) : ℕ × ℕ := (12731,1545)
def epPair_26_26 (y : ℕ) : ℕ × ℕ := (13366,1618)
def epPair_27_27 (y : ℕ) : ℕ × ℕ := (14303,1724)
def epPair_28_28 (y : ℕ) : ℕ × ℕ := (15057,1818)
def epPair_29_29 (y : ℕ) : ℕ × ℕ := (15837,1916)
def epPair_30_30 (y : ℕ) : ℕ × ℕ := (17170,2071)
def epPair_31_31 (y : ℕ) : ℕ × ℕ := (17887,2158)
def epPair_32_32 (y : ℕ) : ℕ × ℕ := (18748,2260)
def epPair_33_33 (y : ℕ) : ℕ × ℕ := (19879,2395)
def epPair_34_34 (y : ℕ) : ℕ × ℕ := (20448,2467)
def epPair_35_35 (y : ℕ) : ℕ × ℕ := (21581,2602)
def epPair_36_36 (y : ℕ) : ℕ × ℕ := (22606,2726)
def epPair_37_37 (y : ℕ) : ℕ × ℕ := (23345,2820)
def epPair_38_38 (y : ℕ) : ℕ × ℕ := (24691,2983)
def epPair_39_39 (y : ℕ) : ℕ × ℕ := (25885,3126)
def epPair_40_40 (y : ℕ) : ℕ × ℕ := (27908,3372)
def epPair_41_41 (y : ℕ) : ℕ × ℕ := (30490,3683)
def epPair_42_42 (y : ℕ) : ℕ × ℕ := (31851,3849)
def epPair_43_43 (y : ℕ) : ℕ × ℕ := (34135,4133)
def epPair_44_44 (y : ℕ) : ℕ × ℕ := (35849,4342)
def epPair_45_45 (y : ℕ) : ℕ × ℕ := (37744,4579)
def epPair_46_46 (y : ℕ) : ℕ × ℕ := (38421,4661)
def epPair_47_47 (y : ℕ) : ℕ × ℕ := (40606,4926)
def epPair_0_1 (y : ℕ) : ℕ × ℕ := if y ≤ 3160 then epPair_0_0 y else epPair_1_1 y
def epPair_0_2 (y : ℕ) : ℕ × ℕ := if y ≤ 3306 then epPair_0_1 y else epPair_2_2 y
def epPair_3_4 (y : ℕ) : ℕ × ℕ := if y ≤ 3672 then epPair_3_3 y else epPair_4_4 y
def epPair_3_5 (y : ℕ) : ℕ × ℕ := if y ≤ 3889 then epPair_3_4 y else epPair_5_5 y
def epPair_0_5 (y : ℕ) : ℕ × ℕ := if y ≤ 3515 then epPair_0_2 y else epPair_3_5 y
def epPair_6_7 (y : ℕ) : ℕ × ℕ := if y ≤ 4329 then epPair_6_6 y else epPair_7_7 y
def epPair_6_8 (y : ℕ) : ℕ × ℕ := if y ≤ 4589 then epPair_6_7 y else epPair_8_8 y
def epPair_9_10 (y : ℕ) : ℕ × ℕ := if y ≤ 5170 then epPair_9_9 y else epPair_10_10 y
def epPair_9_11 (y : ℕ) : ℕ × ℕ := if y ≤ 5467 then epPair_9_10 y else epPair_11_11 y
def epPair_6_11 (y : ℕ) : ℕ × ℕ := if y ≤ 4921 then epPair_6_8 y else epPair_9_11 y
def epPair_0_11 (y : ℕ) : ℕ × ℕ := if y ≤ 4117 then epPair_0_5 y else epPair_6_11 y
def epPair_12_13 (y : ℕ) : ℕ × ℕ := if y ≤ 6021 then epPair_12_12 y else epPair_13_13 y
def epPair_12_14 (y : ℕ) : ℕ × ℕ := if y ≤ 6295 then epPair_12_13 y else epPair_14_14 y
def epPair_15_16 (y : ℕ) : ℕ × ℕ := if y ≤ 7063 then epPair_15_15 y else epPair_16_16 y
def epPair_15_17 (y : ℕ) : ℕ × ℕ := if y ≤ 7443 then epPair_15_16 y else epPair_17_17 y
def epPair_12_17 (y : ℕ) : ℕ × ℕ := if y ≤ 6709 then epPair_12_14 y else epPair_15_17 y
def epPair_18_19 (y : ℕ) : ℕ × ℕ := if y ≤ 8491 then epPair_18_18 y else epPair_19_19 y
def epPair_18_20 (y : ℕ) : ℕ × ℕ := if y ≤ 8860 then epPair_18_19 y else epPair_20_20 y
def epPair_21_22 (y : ℕ) : ℕ × ℕ := if y ≤ 10044 then epPair_21_21 y else epPair_22_22 y
def epPair_21_23 (y : ℕ) : ℕ × ℕ := if y ≤ 10590 then epPair_21_22 y else epPair_23_23 y
def epPair_18_23 (y : ℕ) : ℕ × ℕ := if y ≤ 9446 then epPair_18_20 y else epPair_21_23 y
def epPair_12_23 (y : ℕ) : ℕ × ℕ := if y ≤ 7882 then epPair_12_17 y else epPair_18_23 y
def epPair_0_23 (y : ℕ) : ℕ × ℕ := if y ≤ 5785 then epPair_0_11 y else epPair_12_23 y
def epPair_24_25 (y : ℕ) : ℕ × ℕ := if y ≤ 11916 then epPair_24_24 y else epPair_25_25 y
def epPair_24_26 (y : ℕ) : ℕ × ℕ := if y ≤ 12731 then epPair_24_25 y else epPair_26_26 y
def epPair_27_28 (y : ℕ) : ℕ × ℕ := if y ≤ 14303 then epPair_27_27 y else epPair_28_28 y
def epPair_27_29 (y : ℕ) : ℕ × ℕ := if y ≤ 15057 then epPair_27_28 y else epPair_29_29 y
def epPair_24_29 (y : ℕ) : ℕ × ℕ := if y ≤ 13366 then epPair_24_26 y else epPair_27_29 y
def epPair_30_31 (y : ℕ) : ℕ × ℕ := if y ≤ 17170 then epPair_30_30 y else epPair_31_31 y
def epPair_30_32 (y : ℕ) : ℕ × ℕ := if y ≤ 17887 then epPair_30_31 y else epPair_32_32 y
def epPair_33_34 (y : ℕ) : ℕ × ℕ := if y ≤ 19879 then epPair_33_33 y else epPair_34_34 y
def epPair_33_35 (y : ℕ) : ℕ × ℕ := if y ≤ 20448 then epPair_33_34 y else epPair_35_35 y
def epPair_30_35 (y : ℕ) : ℕ × ℕ := if y ≤ 18748 then epPair_30_32 y else epPair_33_35 y
def epPair_24_35 (y : ℕ) : ℕ × ℕ := if y ≤ 15837 then epPair_24_29 y else epPair_30_35 y
def epPair_36_37 (y : ℕ) : ℕ × ℕ := if y ≤ 22606 then epPair_36_36 y else epPair_37_37 y
def epPair_36_38 (y : ℕ) : ℕ × ℕ := if y ≤ 23345 then epPair_36_37 y else epPair_38_38 y
def epPair_39_40 (y : ℕ) : ℕ × ℕ := if y ≤ 25885 then epPair_39_39 y else epPair_40_40 y
def epPair_39_41 (y : ℕ) : ℕ × ℕ := if y ≤ 27908 then epPair_39_40 y else epPair_41_41 y
def epPair_36_41 (y : ℕ) : ℕ × ℕ := if y ≤ 24691 then epPair_36_38 y else epPair_39_41 y
def epPair_42_43 (y : ℕ) : ℕ × ℕ := if y ≤ 31851 then epPair_42_42 y else epPair_43_43 y
def epPair_42_44 (y : ℕ) : ℕ × ℕ := if y ≤ 34135 then epPair_42_43 y else epPair_44_44 y
def epPair_45_46 (y : ℕ) : ℕ × ℕ := if y ≤ 37744 then epPair_45_45 y else epPair_46_46 y
def epPair_45_47 (y : ℕ) : ℕ × ℕ := if y ≤ 38421 then epPair_45_46 y else epPair_47_47 y
def epPair_42_47 (y : ℕ) : ℕ × ℕ := if y ≤ 35849 then epPair_42_44 y else epPair_45_47 y
def epPair_36_47 (y : ℕ) : ℕ × ℕ := if y ≤ 30490 then epPair_36_41 y else epPair_42_47 y
def epPair_24_47 (y : ℕ) : ℕ × ℕ := if y ≤ 21581 then epPair_24_35 y else epPair_36_47 y
def epPair_0_47 (y : ℕ) : ℕ × ℕ := if y ≤ 11408 then epPair_0_23 y else epPair_24_47 y
def epPair (y : ℕ) : ℕ × ℕ := epPair_0_47 y
def epY (y : ℕ) : ℕ := (epPair y).1
def epCY (y : ℕ) : ℕ := (epPair y).2

opaque roughC_mono {a b : ℕ} (hab : a ≤ b) : roughC a ⊆ roughC b := by
  intro c hc
  unfold roughC at hc ⊢
  simp only [Finset.mem_filter, Finset.mem_Icc] at hc ⊢
  exact ⟨⟨hc.1.1, le_trans hc.1.2 hab⟩, hc.2⟩
opaque endpointY_spec (y : ℕ) (hy : y ≤ 40606) : y ≤ epY y ∧ phiOpt (epY y) primes22 = epCY y := by
  by_cases h0_47 : y ≤ 11408
  ·
    by_cases h0_23 : y ≤ 5785
    ·
      by_cases h0_11 : y ≤ 4117
      ·
        by_cases h0_5 : y ≤ 3515
        ·
          by_cases h0_2 : y ≤ 3306
          ·
            by_cases h0_1 : y ≤ 3160
            ·
              have hpair : epPair y = (3160,425) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_0_5 epPair_0_2 epPair_0_1 epPair_0_0
                rw [if_pos h0_47, if_pos h0_23, if_pos h0_11, if_pos h0_5, if_pos h0_2, if_pos h0_1]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint0_cert
            ·
              have hpair : epPair y = (3306,443) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_0_5 epPair_0_2 epPair_0_1 epPair_1_1
                rw [if_pos h0_47, if_pos h0_23, if_pos h0_11, if_pos h0_5, if_pos h0_2, if_neg h0_1]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint1_cert
          ·
            have hpair : epPair y = (3515,469) := by
              unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_0_5 epPair_0_2 epPair_2_2
              rw [if_pos h0_47, if_pos h0_23, if_pos h0_11, if_pos h0_5, if_neg h0_2]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint2_cert
        ·
          by_cases h3_5 : y ≤ 3889
          ·
            by_cases h3_4 : y ≤ 3672
            ·
              have hpair : epPair y = (3672,491) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_0_5 epPair_3_5 epPair_3_4 epPair_3_3
                rw [if_pos h0_47, if_pos h0_23, if_pos h0_11, if_neg h0_5, if_pos h3_5, if_pos h3_4]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint3_cert
            ·
              have hpair : epPair y = (3889,518) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_0_5 epPair_3_5 epPair_3_4 epPair_4_4
                rw [if_pos h0_47, if_pos h0_23, if_pos h0_11, if_neg h0_5, if_pos h3_5, if_neg h3_4]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint4_cert
          ·
            have hpair : epPair y = (4117,545) := by
              unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_0_5 epPair_3_5 epPair_5_5
              rw [if_pos h0_47, if_pos h0_23, if_pos h0_11, if_neg h0_5, if_neg h3_5]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint5_cert
      ·
        by_cases h6_11 : y ≤ 4921
        ·
          by_cases h6_8 : y ≤ 4589
          ·
            by_cases h6_7 : y ≤ 4329
            ·
              have hpair : epPair y = (4329,570) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_6_11 epPair_6_8 epPair_6_7 epPair_6_6
                rw [if_pos h0_47, if_pos h0_23, if_neg h0_11, if_pos h6_11, if_pos h6_8, if_pos h6_7]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint6_cert
            ·
              have hpair : epPair y = (4589,599) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_6_11 epPair_6_8 epPair_6_7 epPair_7_7
                rw [if_pos h0_47, if_pos h0_23, if_neg h0_11, if_pos h6_11, if_pos h6_8, if_neg h6_7]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint7_cert
          ·
            have hpair : epPair y = (4921,636) := by
              unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_6_11 epPair_6_8 epPair_8_8
              rw [if_pos h0_47, if_pos h0_23, if_neg h0_11, if_pos h6_11, if_neg h6_8]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint8_cert
        ·
          by_cases h9_11 : y ≤ 5467
          ·
            by_cases h9_10 : y ≤ 5170
            ·
              have hpair : epPair y = (5170,667) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_6_11 epPair_9_11 epPair_9_10 epPair_9_9
                rw [if_pos h0_47, if_pos h0_23, if_neg h0_11, if_neg h6_11, if_pos h9_11, if_pos h9_10]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint9_cert
            ·
              have hpair : epPair y = (5467,700) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_6_11 epPair_9_11 epPair_9_10 epPair_10_10
                rw [if_pos h0_47, if_pos h0_23, if_neg h0_11, if_neg h6_11, if_pos h9_11, if_neg h9_10]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint10_cert
          ·
            have hpair : epPair y = (5785,738) := by
              unfold epPair epPair_0_47 epPair_0_23 epPair_0_11 epPair_6_11 epPair_9_11 epPair_11_11
              rw [if_pos h0_47, if_pos h0_23, if_neg h0_11, if_neg h6_11, if_neg h9_11]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint11_cert
    ·
      by_cases h12_23 : y ≤ 7882
      ·
        by_cases h12_17 : y ≤ 6709
        ·
          by_cases h12_14 : y ≤ 6295
          ·
            by_cases h12_13 : y ≤ 6021
            ·
              have hpair : epPair y = (6021,764) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_12_17 epPair_12_14 epPair_12_13 epPair_12_12
                rw [if_pos h0_47, if_neg h0_23, if_pos h12_23, if_pos h12_17, if_pos h12_14, if_pos h12_13]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint12_cert
            ·
              have hpair : epPair y = (6295,797) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_12_17 epPair_12_14 epPair_12_13 epPair_13_13
                rw [if_pos h0_47, if_neg h0_23, if_pos h12_23, if_pos h12_17, if_pos h12_14, if_neg h12_13]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint13_cert
          ·
            have hpair : epPair y = (6709,845) := by
              unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_12_17 epPair_12_14 epPair_14_14
              rw [if_pos h0_47, if_neg h0_23, if_pos h12_23, if_pos h12_17, if_neg h12_14]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint14_cert
        ·
          by_cases h15_17 : y ≤ 7443
          ·
            by_cases h15_16 : y ≤ 7063
            ·
              have hpair : epPair y = (7063,887) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_12_17 epPair_15_17 epPair_15_16 epPair_15_15
                rw [if_pos h0_47, if_neg h0_23, if_pos h12_23, if_neg h12_17, if_pos h15_17, if_pos h15_16]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint15_cert
            ·
              have hpair : epPair y = (7443,923) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_12_17 epPair_15_17 epPair_15_16 epPair_16_16
                rw [if_pos h0_47, if_neg h0_23, if_pos h12_23, if_neg h12_17, if_pos h15_17, if_neg h15_16]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint16_cert
          ·
            have hpair : epPair y = (7882,977) := by
              unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_12_17 epPair_15_17 epPair_17_17
              rw [if_pos h0_47, if_neg h0_23, if_pos h12_23, if_neg h12_17, if_neg h15_17]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint17_cert
      ·
        by_cases h18_23 : y ≤ 9446
        ·
          by_cases h18_20 : y ≤ 8860
          ·
            by_cases h18_19 : y ≤ 8491
            ·
              have hpair : epPair y = (8491,1043) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_18_23 epPair_18_20 epPair_18_19 epPair_18_18
                rw [if_pos h0_47, if_neg h0_23, if_neg h12_23, if_pos h18_23, if_pos h18_20, if_pos h18_19]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint18_cert
            ·
              have hpair : epPair y = (8860,1089) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_18_23 epPair_18_20 epPair_18_19 epPair_19_19
                rw [if_pos h0_47, if_neg h0_23, if_neg h12_23, if_pos h18_23, if_pos h18_20, if_neg h18_19]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint19_cert
          ·
            have hpair : epPair y = (9446,1162) := by
              unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_18_23 epPair_18_20 epPair_20_20
              rw [if_pos h0_47, if_neg h0_23, if_neg h12_23, if_pos h18_23, if_neg h18_20]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint20_cert
        ·
          by_cases h21_23 : y ≤ 10590
          ·
            by_cases h21_22 : y ≤ 10044
            ·
              have hpair : epPair y = (10044,1229) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_18_23 epPair_21_23 epPair_21_22 epPair_21_21
                rw [if_pos h0_47, if_neg h0_23, if_neg h12_23, if_neg h18_23, if_pos h21_23, if_pos h21_22]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint21_cert
            ·
              have hpair : epPair y = (10590,1293) := by
                unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_18_23 epPair_21_23 epPair_21_22 epPair_22_22
                rw [if_pos h0_47, if_neg h0_23, if_neg h12_23, if_neg h18_23, if_pos h21_23, if_neg h21_22]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint22_cert
          ·
            have hpair : epPair y = (11408,1387) := by
              unfold epPair epPair_0_47 epPair_0_23 epPair_12_23 epPair_18_23 epPair_21_23 epPair_23_23
              rw [if_pos h0_47, if_neg h0_23, if_neg h12_23, if_neg h18_23, if_neg h21_23]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint23_cert
  ·
    by_cases h24_47 : y ≤ 21581
    ·
      by_cases h24_35 : y ≤ 15837
      ·
        by_cases h24_29 : y ≤ 13366
        ·
          by_cases h24_26 : y ≤ 12731
          ·
            by_cases h24_25 : y ≤ 11916
            ·
              have hpair : epPair y = (11916,1445) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_24_29 epPair_24_26 epPair_24_25 epPair_24_24
                rw [if_neg h0_47, if_pos h24_47, if_pos h24_35, if_pos h24_29, if_pos h24_26, if_pos h24_25]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint24_cert
            ·
              have hpair : epPair y = (12731,1545) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_24_29 epPair_24_26 epPair_24_25 epPair_25_25
                rw [if_neg h0_47, if_pos h24_47, if_pos h24_35, if_pos h24_29, if_pos h24_26, if_neg h24_25]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint25_cert
          ·
            have hpair : epPair y = (13366,1618) := by
              unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_24_29 epPair_24_26 epPair_26_26
              rw [if_neg h0_47, if_pos h24_47, if_pos h24_35, if_pos h24_29, if_neg h24_26]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint26_cert
        ·
          by_cases h27_29 : y ≤ 15057
          ·
            by_cases h27_28 : y ≤ 14303
            ·
              have hpair : epPair y = (14303,1724) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_24_29 epPair_27_29 epPair_27_28 epPair_27_27
                rw [if_neg h0_47, if_pos h24_47, if_pos h24_35, if_neg h24_29, if_pos h27_29, if_pos h27_28]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint27_cert
            ·
              have hpair : epPair y = (15057,1818) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_24_29 epPair_27_29 epPair_27_28 epPair_28_28
                rw [if_neg h0_47, if_pos h24_47, if_pos h24_35, if_neg h24_29, if_pos h27_29, if_neg h27_28]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint28_cert
          ·
            have hpair : epPair y = (15837,1916) := by
              unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_24_29 epPair_27_29 epPair_29_29
              rw [if_neg h0_47, if_pos h24_47, if_pos h24_35, if_neg h24_29, if_neg h27_29]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint29_cert
      ·
        by_cases h30_35 : y ≤ 18748
        ·
          by_cases h30_32 : y ≤ 17887
          ·
            by_cases h30_31 : y ≤ 17170
            ·
              have hpair : epPair y = (17170,2071) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_30_35 epPair_30_32 epPair_30_31 epPair_30_30
                rw [if_neg h0_47, if_pos h24_47, if_neg h24_35, if_pos h30_35, if_pos h30_32, if_pos h30_31]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint30_cert
            ·
              have hpair : epPair y = (17887,2158) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_30_35 epPair_30_32 epPair_30_31 epPair_31_31
                rw [if_neg h0_47, if_pos h24_47, if_neg h24_35, if_pos h30_35, if_pos h30_32, if_neg h30_31]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint31_cert
          ·
            have hpair : epPair y = (18748,2260) := by
              unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_30_35 epPair_30_32 epPair_32_32
              rw [if_neg h0_47, if_pos h24_47, if_neg h24_35, if_pos h30_35, if_neg h30_32]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint32_cert
        ·
          by_cases h33_35 : y ≤ 20448
          ·
            by_cases h33_34 : y ≤ 19879
            ·
              have hpair : epPair y = (19879,2395) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_30_35 epPair_33_35 epPair_33_34 epPair_33_33
                rw [if_neg h0_47, if_pos h24_47, if_neg h24_35, if_neg h30_35, if_pos h33_35, if_pos h33_34]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint33_cert
            ·
              have hpair : epPair y = (20448,2467) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_30_35 epPair_33_35 epPair_33_34 epPair_34_34
                rw [if_neg h0_47, if_pos h24_47, if_neg h24_35, if_neg h30_35, if_pos h33_35, if_neg h33_34]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint34_cert
          ·
            have hpair : epPair y = (21581,2602) := by
              unfold epPair epPair_0_47 epPair_24_47 epPair_24_35 epPair_30_35 epPair_33_35 epPair_35_35
              rw [if_neg h0_47, if_pos h24_47, if_neg h24_35, if_neg h30_35, if_neg h33_35]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint35_cert
    ·
      by_cases h36_47 : y ≤ 30490
      ·
        by_cases h36_41 : y ≤ 24691
        ·
          by_cases h36_38 : y ≤ 23345
          ·
            by_cases h36_37 : y ≤ 22606
            ·
              have hpair : epPair y = (22606,2726) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_36_41 epPair_36_38 epPair_36_37 epPair_36_36
                rw [if_neg h0_47, if_neg h24_47, if_pos h36_47, if_pos h36_41, if_pos h36_38, if_pos h36_37]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint36_cert
            ·
              have hpair : epPair y = (23345,2820) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_36_41 epPair_36_38 epPair_36_37 epPair_37_37
                rw [if_neg h0_47, if_neg h24_47, if_pos h36_47, if_pos h36_41, if_pos h36_38, if_neg h36_37]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint37_cert
          ·
            have hpair : epPair y = (24691,2983) := by
              unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_36_41 epPair_36_38 epPair_38_38
              rw [if_neg h0_47, if_neg h24_47, if_pos h36_47, if_pos h36_41, if_neg h36_38]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint38_cert
        ·
          by_cases h39_41 : y ≤ 27908
          ·
            by_cases h39_40 : y ≤ 25885
            ·
              have hpair : epPair y = (25885,3126) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_36_41 epPair_39_41 epPair_39_40 epPair_39_39
                rw [if_neg h0_47, if_neg h24_47, if_pos h36_47, if_neg h36_41, if_pos h39_41, if_pos h39_40]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint39_cert
            ·
              have hpair : epPair y = (27908,3372) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_36_41 epPair_39_41 epPair_39_40 epPair_40_40
                rw [if_neg h0_47, if_neg h24_47, if_pos h36_47, if_neg h36_41, if_pos h39_41, if_neg h39_40]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint40_cert
          ·
            have hpair : epPair y = (30490,3683) := by
              unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_36_41 epPair_39_41 epPair_41_41
              rw [if_neg h0_47, if_neg h24_47, if_pos h36_47, if_neg h36_41, if_neg h39_41]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint41_cert
      ·
        by_cases h42_47 : y ≤ 35849
        ·
          by_cases h42_44 : y ≤ 34135
          ·
            by_cases h42_43 : y ≤ 31851
            ·
              have hpair : epPair y = (31851,3849) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_42_47 epPair_42_44 epPair_42_43 epPair_42_42
                rw [if_neg h0_47, if_neg h24_47, if_neg h36_47, if_pos h42_47, if_pos h42_44, if_pos h42_43]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint42_cert
            ·
              have hpair : epPair y = (34135,4133) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_42_47 epPair_42_44 epPair_42_43 epPair_43_43
                rw [if_neg h0_47, if_neg h24_47, if_neg h36_47, if_pos h42_47, if_pos h42_44, if_neg h42_43]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint43_cert
          ·
            have hpair : epPair y = (35849,4342) := by
              unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_42_47 epPair_42_44 epPair_44_44
              rw [if_neg h0_47, if_neg h24_47, if_neg h36_47, if_pos h42_47, if_neg h42_44]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint44_cert
        ·
          by_cases h45_47 : y ≤ 38421
          ·
            by_cases h45_46 : y ≤ 37744
            ·
              have hpair : epPair y = (37744,4579) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_42_47 epPair_45_47 epPair_45_46 epPair_45_45
                rw [if_neg h0_47, if_neg h24_47, if_neg h36_47, if_neg h42_47, if_pos h45_47, if_pos h45_46]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint45_cert
            ·
              have hpair : epPair y = (38421,4661) := by
                unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_42_47 epPair_45_47 epPair_45_46 epPair_46_46
                rw [if_neg h0_47, if_neg h24_47, if_neg h36_47, if_neg h42_47, if_pos h45_47, if_neg h45_46]
              constructor
              · rw [epY, hpair]
                omega
              · rw [epY, epCY, hpair]
                exact endpoint46_cert
          ·
            have hpair : epPair y = (40606,4926) := by
              unfold epPair epPair_0_47 epPair_24_47 epPair_36_47 epPair_42_47 epPair_45_47 epPair_47_47
              rw [if_neg h0_47, if_neg h24_47, if_neg h36_47, if_neg h42_47, if_neg h45_47]
            constructor
            · rw [epY, hpair]
              omega
            · rw [epY, epCY, hpair]
              exact endpoint47_cert
opaque cofC_card_le_endpointY (j : ℕ) (hj : j < genTail.length) :
    ((cofC 8567964 (genTail.get ⟨j,hj⟩)).card : ℤ) ≤ (epCY (8567964 / genTail.get ⟨j,hj⟩) : ℤ) - (j + 25 : ℤ) := by
  have hbase := cofC_card_add_lowW_card_le_roughC (N := 8567964) genTail_inc genTail_prime_ge200 hj (qOf_sq_le_N j hj)
  have hlow := card_lowW genTail j genTail_nodup genTail_ge200
  have htakelen : (genTail.take j).length = j := by rw [List.length_take]; omega
  rw [hlow, htakelen] at hbase
  have hy : 8567964 / genTail.get ⟨j,hj⟩ ≤ 40606 := by
    have hqge : 211 ≤ genTail.get ⟨j,hj⟩ := genTail_ge211 _ (List.get_mem _ _)
    have hqpos : 0 < genTail.get ⟨j,hj⟩ := by omega
    have hlt : 8567964 / genTail.get ⟨j,hj⟩ < 40607 := by
      rw [Nat.div_lt_iff_lt_mul hqpos]
      nlinarith
    omega
  rcases endpointY_spec (8567964 / genTail.get ⟨j,hj⟩) hy with ⟨hey, hecnt⟩
  have hmono := Finset.card_le_card (roughC_mono hey)
  have hroughphi := roughC_card_eq_phiCount (epY (8567964 / genTail.get ⟨j,hj⟩))
  have hrec := phiOpt_eq_phiCount (epY (8567964 / genTail.get ⟨j,hj⟩)) primes22 primes22_inc primes22_prime_all
  rw [hroughphi, ← hrec, hecnt] at hmono
  linarith
def tailEndpointYUB : ℤ := ∑ j : Fin genTail.length, ((epCY (8567964 / genTail.get j) : ℤ) - (j.val + 25 : ℤ))
opaque tailSigma_card_le_endpointYUB : ((tailSigma 8567964).card : ℤ) ≤ tailEndpointYUB := by
  unfold tailEndpointYUB tailSigma
  rw [Finset.card_sigma, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact cofC_card_le_endpointY j.val j.isLt
opaque tailEndpointYUB_le_cert : tailEndpointYUB ≤ 344600 := by decide
set_option maxRecDepth 5000 in
opaque compSurvivors_bound : (compSurvivors 8567964).card ≤ 344600 := by
  have h1 := compSurvivors_card_le_tailSigma
  have h2 := tailSigma_card_le_endpointYUB
  have h3 := tailEndpointYUB_le_cert
  norm_num at h2 h3 ⊢
  omega
opaque prime_count_lower : 550171 < Nat.count Nat.Prime 8567965 := by
  have hphi := phiCount_primes46_lower
  have hrough : 894773 ≤ (roughC46 8567964).card := by
    rw [roughC46_card_eq_phiCount]
    exact hphi
  have hle := roughC46_card_le_one_primecount_comp 8567964
  have hcomp := compSurvivors_bound
  norm_num at hle ⊢
  omega
opaque nth_prime_bound : Nat.nth Nat.Prime 550171 ≤ 8567964 := by
  have h := (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mp prime_count_lower
  exact Nat.le_of_lt_succ h
opaque zmod343_eq_to_check {s : ℕ} (hs : s < 1029)
    (h : (2 : ZMod 343) ^ s - (s : ZMod 343) = (147 : ZMod 343)) :
    (2 ^ s + 343 - (s % 343)) % 343 = 147 := by
  have hcast : ((2 ^ s + 343 - (s % 343) : ℕ) : ZMod 343) = (147 : ZMod 343) := by
    rw [Nat.cast_sub]
    · simp only [Nat.cast_add, Nat.cast_pow]
      have hs_cast : ((s % 343 : ℕ) : ZMod 343) = (s : ZMod 343) := by
        exact (ZMod.natCast_eq_natCast_iff' (s % 343) s 343).mpr (by
          exact Nat.mod_eq_of_lt (Nat.mod_lt s (by norm_num : 0 < 343)))
      have h343zero : (343 : ZMod 343) = 0 := by
        change ((343 : ℕ) : ZMod 343) = 0
        rw [ZMod.natCast_eq_zero_iff]
      change (2 : ZMod 343) ^ s + (343 : ZMod 343) - ((s % 343 : ℕ) : ZMod 343) = (147 : ZMod 343)
      rw [hs_cast, h343zero]
      simpa using h
    · have hle : s % 343 < 343 := Nat.mod_lt s (by norm_num : 0 < 343)
      have hp : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      omega
  have hmod := (ZMod.natCast_eq_natCast_iff' (2 ^ s + 343 - s % 343) 147 343).mp hcast
  exact hmod.trans (by norm_num)
set_option maxRecDepth 10000 in
opaque eq550_to_check343 {k : ℕ}
    (h : (2 : ZMod 550172) ^ k - (k : ZMod 550172) = (63945 : ZMod 550172)) :
    let s := k % 1029
    (2 ^ s + 343 - (s % 343)) % 343 = 147 := by
  intro s
  have h343 : (2 : ZMod 343) ^ k - (k : ZMod 343) = (147 : ZMod 343) := by
    have hc := congrArg (fun z => ZMod.castHom (by norm_num : 343 ∣ 550172) (ZMod 343) z) h
    simpa [ZMod.castHom_apply, map_sub, map_pow] using hc
  have hper : (2 : ZMod 343) ^ 1029 = 1 := by
    change (((2 ^ 1029 : ℕ) : ZMod 343) = (1 : ZMod 343))
    exact (ZMod.natCast_eq_natCast_iff (2 ^ 1029) 1 343).mpr (by norm_num [Nat.ModEq])
  have hkmod : k ≡ s [MOD 1029] := by
    dsimp [s]
    exact (Nat.mod_modEq k 1029).symm
  have hpow : (2 : ZMod 343) ^ k = (2 : ZMod 343) ^ s := pow_eq_pow_of_modEq hkmod hper
  have hkmod343 : k ≡ s [MOD 343] := hkmod.of_dvd (by norm_num)
  have hcastks : (k : ZMod 343) = (s : ZMod 343) := by
    exact (ZMod.natCast_eq_natCast_iff k s 343).mpr hkmod343
  have h343s : (2 : ZMod 343) ^ s - (s : ZMod 343) = (147 : ZMod 343) := by
    simpa [hpow, hcastks] using h343
  exact zmod343_eq_to_check (Nat.mod_lt _ (by norm_num)) h343s
opaque zmod401_pow_period : (2 : ZMod 401) ^ 400 = 1 := by
  change (((2 ^ 400 : ℕ) : ZMod 401) = (1 : ZMod 401))
  exact (ZMod.natCast_eq_natCast_iff (2 ^ 400) 1 401).mpr
    (Nat.ModEq.pow_card_sub_one_eq_one (by norm_num : Nat.Prime 401) (by norm_num : Nat.Coprime 2 401))
opaque zmod401_pow_eq_of_mod (a b : ℕ) (h : a ≡ b [MOD 400]) :
    (2 : ZMod 401) ^ a = (2 : ZMod 401) ^ b :=
  pow_eq_pow_of_modEq h zmod401_pow_period
opaque zmod401_eq_to_check (r C t : ℕ)
    (hC : (2 : ZMod 401) ^ r = (C : ZMod 401))
    (h : (2 : ZMod 401) ^ (r + 4116 * t) - ((r + 4116 * t : ℕ) : ZMod 401) = (186 : ZMod 401)) :
    (C * 228 ^ t + 401 - ((r + 4116 * t) % 401)) % 401 = 186 := by
  have h228 : (2 : ZMod 401) ^ 4116 = (228 : ZMod 401) := by
    rw [zmod401_pow_eq_of_mod 4116 116 (by norm_num [Nat.ModEq])]
    change (((2 ^ 116 : ℕ) : ZMod 401) = (228 : ZMod 401))
    exact (ZMod.natCast_eq_natCast_iff (2 ^ 116) 228 401).mpr (by norm_num [Nat.ModEq])
  have hpow : (2 : ZMod 401) ^ (r + 4116 * t) = (C : ZMod 401) * (228 : ZMod 401) ^ t := by
    rw [pow_add, pow_mul, hC, h228]
  have hk_cast : (((r + 4116 * t) % 401 : ℕ) : ZMod 401) = ((r + 4116 * t : ℕ) : ZMod 401) := by
    exact (ZMod.natCast_eq_natCast_iff' ((r + 4116 * t) % 401) (r + 4116 * t) 401).mpr (by
      exact Nat.mod_eq_of_lt (Nat.mod_lt (r + 4116 * t) (by norm_num : 0 < 401)))
  have hcast : ((C * 228 ^ t + 401 - ((r + 4116 * t) % 401) : ℕ) : ZMod 401) = (186 : ZMod 401) := by
    rw [Nat.cast_sub]
    · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      have h401zero : (401 : ZMod 401) = 0 := by
        change ((401 : ℕ) : ZMod 401) = 0
        rw [ZMod.natCast_eq_zero_iff]
      change (C : ZMod 401) * (228 : ZMod 401) ^ t + (401 : ZMod 401) - (((r + 4116 * t) % 401 : ℕ) : ZMod 401) = (186 : ZMod 401)
      rw [hk_cast, h401zero]
      simpa [hpow] using h
    · have hlt : (r + 4116 * t) % 401 < 401 := Nat.mod_lt _ (by norm_num : 0 < 401)
      have hp : 1 ≤ C * 228 ^ t + 401 := by omega
      omega
  have hmod := (ZMod.natCast_eq_natCast_iff' (C * 228 ^ t + 401 - ((r + 4116 * t) % 401)) 186 401).mp hcast
  exact hmod.trans (by norm_num)
opaque eq550_to_check401_1019 {t : ℕ}
    (h : (2 : ZMod 550172) ^ (1019 + 4116 * t) - ((1019 + 4116 * t : ℕ) : ZMod 550172) = (63945 : ZMod 550172)) :
    (181 * 228 ^ t + 401 - ((1019 + 4116 * t) % 401)) % 401 = 186 := by
  have h401 : (2 : ZMod 401) ^ (1019 + 4116 * t) - ((1019 + 4116 * t : ℕ) : ZMod 401) = (186 : ZMod 401) := by
    have hc := congrArg (fun z => ZMod.castHom (by norm_num : 401 ∣ 550172) (ZMod 401) z) h
    simpa [ZMod.castHom_apply, map_sub, map_pow] using hc
  apply zmod401_eq_to_check 1019 181 t
  · rw [zmod401_pow_eq_of_mod 1019 219 (by norm_num [Nat.ModEq])]
    change (((2 ^ 219 : ℕ) : ZMod 401) = (181 : ZMod 401))
    exact (ZMod.natCast_eq_natCast_iff (2 ^ 219) 181 401).mpr (by norm_num [Nat.ModEq])
  · exact h401
opaque eq550_to_check401_771 {t : ℕ}
    (h : (2 : ZMod 550172) ^ (771 + 4116 * t) - ((771 + 4116 * t : ℕ) : ZMod 550172) = (63945 : ZMod 550172)) :
    (357 * 228 ^ t + 401 - ((771 + 4116 * t) % 401)) % 401 = 186 := by
  have h401 : (2 : ZMod 401) ^ (771 + 4116 * t) - ((771 + 4116 * t : ℕ) : ZMod 401) = (186 : ZMod 401) := by
    have hc := congrArg (fun z => ZMod.castHom (by norm_num : 401 ∣ 550172) (ZMod 401) z) h
    simpa [ZMod.castHom_apply, map_sub, map_pow] using hc
  apply zmod401_eq_to_check 771 357 t
  · rw [zmod401_pow_eq_of_mod 771 371 (by norm_num [Nat.ModEq])]
    change (((2 ^ 371 : ℕ) : ZMod 401) = (357 : ZMod 401))
    exact (ZMod.natCast_eq_natCast_iff (2 ^ 371) 357 401).mpr (by norm_num [Nat.ModEq])
  · exact h401
opaque eq550_to_check401_2767 {t : ℕ}
    (h : (2 : ZMod 550172) ^ (2767 + 4116 * t) - ((2767 + 4116 * t : ℕ) : ZMod 550172) = (63945 : ZMod 550172)) :
    (298 * 228 ^ t + 401 - ((2767 + 4116 * t) % 401)) % 401 = 186 := by
  have h401 : (2 : ZMod 401) ^ (2767 + 4116 * t) - ((2767 + 4116 * t : ℕ) : ZMod 401) = (186 : ZMod 401) := by
    have hc := congrArg (fun z => ZMod.castHom (by norm_num : 401 ∣ 550172) (ZMod 401) z) h
    simpa [ZMod.castHom_apply, map_sub, map_pow] using hc
  apply zmod401_eq_to_check 2767 298 t
  · rw [zmod401_pow_eq_of_mod 2767 367 (by norm_num [Nat.ModEq])]
    change (((2 ^ 367 : ℕ) : ZMod 401) = (298 : ZMod 401))
    exact (ZMod.natCast_eq_natCast_iff (2 ^ 367) 298 401).mpr (by norm_num [Nat.ModEq])
  · exact h401
def good343 (s : Nat) : Bool :=
  decide ((2 ^ s + 343 - (s % 343)) % 343 = 147 → s = 709 ∨ s = 771 ∨ s = 1019)
def check343From : Nat -> Bool
| 0 => true
| n+1 => good343 n && check343From n
opaque check343_cert : check343From 1029 = true := by decide
lemma check343From_spec {n s : Nat} (hcheck : check343From n = true) (hs : s < n) : good343 s = true := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp [check343From] at hcheck
      rcases hcheck with ⟨hn, hrest⟩
      by_cases hsn : s = n
      · subst s
        exact hn
      · have hs' : s < n := by omega
        exact ih hrest hs'
lemma check343_last_fast (s : ℕ) (hs : s < 1029) :
    (2 ^ s + 343 - (s % 343)) % 343 = 147 →
      s = 709 ∨ s = 771 ∨ s = 1019 := by
  have hb := check343From_spec check343_cert hs
  dsimp [good343] at hb
  exact of_decide_eq_true hb
def bad401 (C r t : Nat) : Bool :=
  decide ((C * 228 ^ t + 401 - ((r + 4116 * t) % 401)) % 401 = 186)
def check401From (C r : Nat) : Nat -> Bool
| 0 => true
| n+1 => (! bad401 C r n) && check401From C r n
set_option maxRecDepth 10000 in
opaque check401_771_cert : check401From 357 771 4163 = true := by decide
set_option maxRecDepth 10000 in
opaque check401_1019_cert : check401From 181 1019 4163 = true := by decide
set_option maxRecDepth 10000 in
opaque check401_2767_cert : check401From 298 2767 4163 = true := by decide
lemma check401From_spec {C r n t : Nat} (hcheck : check401From C r n = true) (ht : t < n) :
    bad401 C r t = false := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp [check401From] at hcheck
      rcases hcheck with ⟨hn, hrest⟩
      by_cases htn : t = n
      · subst t
        exact hn
      · have ht' : t < n := by omega
        exact ih hrest ht'
lemma check401_last_771_fast (t : ℕ) (ht : t < 4163) :
  (357 * 228 ^ t + 401 - ((771 + 4116 * t) % 401)) % 401 ≠ 186 := by
  have hb := check401From_spec check401_771_cert ht
  dsimp [bad401] at hb
  exact of_decide_eq_false hb
lemma check401_last_1019_fast (t : ℕ) (ht : t < 4163) :
  (181 * 228 ^ t + 401 - ((1019 + 4116 * t) % 401)) % 401 ≠ 186 := by
  have hb := check401From_spec check401_1019_cert ht
  dsimp [bad401] at hb
  exact of_decide_eq_false hb
lemma check401_last_2767_fast (t : ℕ) (ht : t < 4163) :
  (298 * 228 ^ t + 401 - ((2767 + 4116 * t) % 401)) % 401 ≠ 186 := by
  have hb := check401From_spec check401_2767_cert ht
  dsimp [bad401] at hb
  exact of_decide_eq_false hb
opaque k_mod4_eq_three_of_eq {k : ℕ} (hkge : 2 ≤ k)
    (h : (2 : ZMod 550172) ^ k - (k : ZMod 550172) = (63945 : ZMod 550172)) :
    k % 4 = 3 := by
  have h4 : (2 : ZMod 4) ^ k - (k : ZMod 4) = (1 : ZMod 4) := by
    have hc := congrArg (fun z => ZMod.castHom (by norm_num : 4 ∣ 550172) (ZMod 4) z) h
    norm_num [ZMod.castHom_apply, map_sub, map_pow] at hc ⊢
    exact hc
  have hpow0 : (2 : ZMod 4) ^ k = 0 := by
    have hcast : (((2 ^ k : ℕ) : ZMod 4) = 0) := by
      rw [ZMod.natCast_eq_zero_iff]
      have hd : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hkge
      simpa using hd
    simpa [Nat.cast_pow] using hcast
  have hkz : (k : ZMod 4) = (3 : ZMod 4) := by
    have : -(k : ZMod 4) = 1 := by simpa [hpow0] using h4
    have : (k : ZMod 4) = -1 := by simpa using congrArg Neg.neg this
    norm_num at this ⊢
    exact this
  exact (ZMod.natCast_eq_natCast_iff' k 3 4).mp hkz
opaque residue_4116_709 {k : ℕ} (h1029 : k % 1029 = 709) (h4 : k % 4 = 3) : k % 4116 = 2767 := by
  have h1029' : k ≡ 2767 [MOD 1029] := by
    rw [Nat.ModEq, h1029]
  have h4' : k ≡ 2767 [MOD 4] := by
    rw [Nat.ModEq, h4]
  have hcrt : k ≡ 2767 [MOD 1029 * 4] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 1029 4)).mp ⟨h1029', h4'⟩
  have hcrt' : k % 4116 ≡ 2767 [MOD 4116] := by
    change k % 4116 ≡ 2767 [MOD 1029 * 4]
    exact (Nat.mod_modEq k (1029 * 4)).trans hcrt
  rw [Nat.ModEq] at hcrt'
  simpa using hcrt'
opaque residue_4116_771 {k : ℕ} (h1029 : k % 1029 = 771) (h4 : k % 4 = 3) : k % 4116 = 771 := by
  have h1029' : k ≡ 771 [MOD 1029] := by
    rw [Nat.ModEq, h1029]
  have h4' : k ≡ 771 [MOD 4] := by
    rw [Nat.ModEq, h4]
  have hcrt : k ≡ 771 [MOD 1029 * 4] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 1029 4)).mp ⟨h1029', h4'⟩
  have hcrt' : k % 4116 ≡ 771 [MOD 4116] := by
    change k % 4116 ≡ 771 [MOD 1029 * 4]
    exact (Nat.mod_modEq k (1029 * 4)).trans hcrt
  rw [Nat.ModEq] at hcrt'
  simpa using hcrt'
opaque residue_4116_1019 {k : ℕ} (h1029 : k % 1029 = 1019) (h4 : k % 4 = 3) : k % 4116 = 1019 := by
  have h1029' : k ≡ 1019 [MOD 1029] := by
    rw [Nat.ModEq, h1029]
  have h4' : k ≡ 1019 [MOD 4] := by
    rw [Nat.ModEq, h4]
  have hcrt : k ≡ 1019 [MOD 1029 * 4] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 1029 4)).mp ⟨h1029', h4'⟩
  have hcrt' : k % 4116 ≡ 1019 [MOD 4116] := by
    change k % 4116 ≡ 1019 [MOD 1029 * 4]
    exact (Nat.mod_modEq k (1029 * 4)).trans hcrt
  rw [Nat.ModEq] at hcrt'
  simpa using hcrt'
opaque eq_of_mod_4116 {k r : ℕ} (hr : r < 4116) (hmod : k % 4116 = r) : k = r + 4116 * (k / 4116) := by
  have hdiv := Nat.div_add_mod k 4116
  omega
opaque nohit_63945_before :
    ∀ k : Fin 17135927, 1 ≤ k.val →
      ((2 : ZMod 550172) ^ k.val - (k.val : ZMod 550172)) ≠ (63945 : ZMod 550172) := by
  intro k hkpos h
  let s := k.val % 1029
  have hslt : s < 1029 := Nat.mod_lt _ (by norm_num : 0 < 1029)
  have hcheck343 := eq550_to_check343 h
  change (2 ^ s + 343 - (s % 343)) % 343 = 147 at hcheck343
  have hs_cases := check343_last_fast s hslt hcheck343
  have hkge2 : 2 ≤ k.val := by
    rcases hs_cases with hs | hs | hs <;> dsimp [s] at hs <;> omega
  have hk4 : k.val % 4 = 3 := k_mod4_eq_three_of_eq hkge2 h
  rcases hs_cases with hs | hs | hs
  · have hmod : k.val % 4116 = 2767 := residue_4116_709 (by simpa [s] using hs) hk4
    let t := k.val / 4116
    have hk_eq : k.val = 2767 + 4116 * t := by
      dsimp [t]
      exact eq_of_mod_4116 (by norm_num) hmod
    have ht : t < 4163 := by
      have hklt := k.isLt
      dsimp [t]
      omega
    have h' : (2 : ZMod 550172) ^ (2767 + 4116 * t) - ((2767 + 4116 * t : ℕ) : ZMod 550172) = (63945 : ZMod 550172) := by
      simpa [hk_eq] using h
    exact check401_last_2767_fast t ht (eq550_to_check401_2767 h')
  · have hmod : k.val % 4116 = 771 := residue_4116_771 (by simpa [s] using hs) hk4
    let t := k.val / 4116
    have hk_eq : k.val = 771 + 4116 * t := by
      dsimp [t]
      exact eq_of_mod_4116 (by norm_num) hmod
    have ht_le : t ≤ 4163 := by
      have hklt := k.isLt
      dsimp [t]
      omega
    have h' : (2 : ZMod 550172) ^ (771 + 4116 * t) - ((771 + 4116 * t : ℕ) : ZMod 550172) = (63945 : ZMod 550172) := by
      simpa [hk_eq] using h
    by_cases ht : t < 4163
    · exact check401_last_771_fast t ht (eq550_to_check401_771 h')
    · have htEq : t = 4163 := by omega
      have bad := eq550_to_check401_771 h'
      rw [htEq] at bad
      norm_num at bad
  · have hmod : k.val % 4116 = 1019 := residue_4116_1019 (by simpa [s] using hs) hk4
    let t := k.val / 4116
    have hk_eq : k.val = 1019 + 4116 * t := by
      dsimp [t]
      exact eq_of_mod_4116 (by norm_num) hmod
    have ht : t < 4163 := by
      have hklt := k.isLt
      dsimp [t]
      omega
    have h' : (2 : ZMod 550172) ^ (1019 + 4116 * t) - ((1019 + 4116 * t : ℕ) : ZMod 550172) = (63945 : ZMod 550172) := by
      simpa [hk_eq] using h
    exact check401_last_1019_fast t ht (eq550_to_check401_1019 h')
opaque two_pow_ge (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ k + 2 ^ k := by
          gcongr
          exact Nat.one_le_two_pow
        _ = 2 ^ (k + 1) := by rw [pow_succ]; omega
def w196 : Nat -> Nat
| 0 => 36
| 1 => 143
| 2 => 2
| 3 => 349
| 4 => 308
| 5 => 3
| 6 => 26
| 7 => 225
| 8 => 332
| 9 => 191
| 10 => 50
| 11 => 81
| 12 => 4
| 13 => 31
| 14 => 58
| 15 => 85
| 16 => 48
| 17 => 139
| 18 => 98
| 19 => 193
| 20 => 220
| 21 => 15
| 22 => 122
| 23 => 237
| 24 => 328
| 25 => 287
| 26 => 146
| 27 => 5
| 28 => 204
| 29 => 311
| 30 => 170
| 31 => 29
| 32 => 60
| 33 => 171
| 34 => 10
| 35 => 37
| 36 => 64
| 37 => 27
| 38 => 118
| 39 => 77
| 40 => 172
| 41 => 199
| 42 => 226
| 43 => 101
| 44 => 216
| 45 => 307
| 46 => 266
| 47 => 125
| 48 => 72
| 49 => 183
| 50 => 290
| 51 => 149
| 52 => 8
| 53 => 39
| 54 => 150
| 55 => 173
| 56 => 16
| 57 => 43
| 58 => 6
| 59 => 97
| 60 => 56
| 61 => 151
| 62 => 178
| 63 => 205
| 64 => 80
| 65 => 195
| 66 => 286
| 67 => 245
| 68 => 104
| 69 => 51
| 70 => 162
| 71 => 269
| 72 => 128
| 73 => 475
| 74 => 18
| 75 => 129
| 76 => 152
| 77 => 11
| 78 => 22
| 79 => 49
| 80 => 76
| 81 => 35
| 82 => 130
| 83 => 157
| 84 => 184
| 85 => 59
| 86 => 174
| 87 => 265
| 88 => 224
| 89 => 83
| 90 => 30
| 91 => 141
| 92 => 248
| 93 => 107
| 94 => 454
| 95 => 413
| 96 => 108
| 97 => 131
| 98 => 330
| 99 => 437
| 100 => 28
| 101 => 55
| 102 => 14
| 103 => 109
| 104 => 136
| 105 => 163
| 106 => 38
| 107 => 153
| 108 => 244
| 109 => 203
| 110 => 62
| 111 => 9
| 112 => 120
| 113 => 227
| 114 => 86
| 115 => 433
| 116 => 392
| 117 => 87
| 118 => 110
| 119 => 309
| 120 => 416
| 121 => 7
| 122 => 34
| 123 => 61
| 124 => 88
| 125 => 115
| 126 => 142
| 127 => 17
| 128 => 132
| 129 => 223
| 130 => 182
| 131 => 41
| 132 => 304
| 133 => 99
| 134 => 206
| 135 => 65
| 136 => 412
| 137 => 371
| 138 => 66
| 139 => 89
| 140 => 288
| 141 => 395
| 142 => 254
| 143 => 13
| 144 => 40
| 145 => 67
| 146 => 94
| 147 => 121
| 148 => 148
| 149 => 111
| 150 => 202
| 151 => 161
| 152 => 20
| 153 => 283
| 154 => 78
| 155 => 185
| 156 => 44
| 157 => 391
| 158 => 350
| 159 => 45
| 160 => 68
| 161 => 267
| 162 => 374
| 163 => 233
| 164 => 12
| 165 => 19
| 166 => 46
| 167 => 73
| 168 => 100
| 169 => 127
| 170 => 90
| 171 => 181
| 172 => 140
| 173 => 235
| 174 => 262
| 175 => 57
| 176 => 164
| 177 => 23
| 178 => 370
| 179 => 329
| 180 => 24
| 181 => 47
| 182 => 246
| 183 => 353
| 184 => 212
| 185 => 71
| 186 => 102
| 187 => 25
| 188 => 52
| 189 => 79
| 190 => 106
| 191 => 69
| 192 => 160
| 193 => 119
| 194 => 214
| 195 => 241
| _ => 2
opaque w196_spec (i : ℕ) (hi : i < 196) :
    (2 ^ (w196 i) - w196 i) ≡ i [MOD 196] := by
  decide +revert
opaque totient_137543 : Nat.totient 137543 = 117600 := by
  have hsplit : 137543 = 7^3 * 401 := by norm_num
  rw [hsplit]
  rw [Nat.totient_mul]
  · rw [Nat.totient_prime_pow (p:=7) (n:=3) (by norm_num) (by norm_num)]
    rw [Nat.totient_prime (by norm_num : Nat.Prime 401)]
    norm_num
  · norm_num [Nat.Coprime]
opaque pow_period_137543 : (2 ^ 117600 : ℕ) ≡ 1 [MOD 137543] := by
  rw [← totient_137543]
  exact Nat.ModEq.pow_totient (by norm_num : Nat.Coprime 2 137543)
opaque top_linear (u : ℤ) :
    (117600 * ((Int.toNat ((1938 * u) % 2807) : ℕ) : ℤ)) ≡ 49 * u [ZMOD 137543] := by
  have ht : (((Int.toNat ((1938 * u) % 2807) : ℕ) : ℤ)) = (1938 * u) % 2807 := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  rw [ht]
  have hmod : (1938 * u) % 2807 ≡ 1938 * u [ZMOD (2807:ℤ)] := by
    rw [Int.ModEq]
    exact Int.emod_emod _ _
  have hinv : (2400 * (1938 * u) : ℤ) ≡ u [ZMOD (2807:ℤ)] := by
    have hbase : (2400 * 1938 : ℤ) ≡ 1 [ZMOD (2807:ℤ)] := by norm_num [Int.ModEq]
    calc
      (2400 * (1938 * u) : ℤ) = (2400 * 1938) * u := by ring
      _ ≡ 1 * u [ZMOD (2807:ℤ)] := Int.ModEq.mul hbase Int.ModEq.rfl
      _ = u := by ring
  have h2400 : (2400 * ((1938 * u) % 2807) : ℤ) ≡ u [ZMOD (2807:ℤ)] := by
    exact (Int.ModEq.mul Int.ModEq.rfl hmod).trans hinv
  have h49 := Int.ModEq.mul_left' (c := (49:ℤ)) h2400
  change (49 * (2400 * ((1938 * u) % 2807)) : ℤ) ≡ 49 * u [ZMOD 49 * (2807:ℤ)] at h49
  convert h49 using 1 <;> ring
opaque w196_ge2 (i : Nat) (hi : i < 196) : 2 ≤ w196 i := by
  decide +revert
opaque w196_le475 (i : Nat) (hi : i < 196) : w196 i ≤ 475 := by
  decide +revert
opaque cover_exists_mod (a : Nat) (ha : a < 550172) :
    ∃ k, 1 ≤ k ∧ k ≤ 329986075 ∧ (2 ^ k - k) ≡ a [MOD 550172] := by
  let i := a % 196
  let r := w196 i
  let d : Int := ((2 ^ r : Nat) : Int) - (r : Int) - (a : Int)
  let u : Int := d / 49
  let t : Nat := Int.toNat ((1938 * u) % 2807)
  let k : Nat := r + 117600 * t
  refine ⟨k, ?_, ?_, ?_⟩
  · have hi : i < 196 := Nat.mod_lt _ (by norm_num : 0 < 196)
    have hr : 2 ≤ r := by simpa [r] using w196_ge2 i hi
    change 1 ≤ r + 117600 * t
    omega
  · have hi : i < 196 := Nat.mod_lt _ (by norm_num : 0 < 196)
    have hr : r ≤ 475 := by simpa [r] using w196_le475 i hi
    have ht_lt_int : (1938 * u) % 2807 < 2807 := Int.emod_lt_of_pos _ (by norm_num)
    have htlt : t < 2807 := by
      change Int.toNat ((1938 * u) % 2807) < 2807
      exact (Int.toNat_lt_of_ne_zero (by norm_num : (2807:ℕ) ≠ 0)).mpr ht_lt_int
    change r + 117600 * t ≤ 329986075
    omega
  · have hi : i < 196 := Nat.mod_lt _ (by norm_num : 0 < 196)
    have hr_ge : 2 ≤ r := by simpa [r] using w196_ge2 i hi
    have hk_ge : 2 ≤ k := by
      change 2 ≤ r + 117600 * t
      omega
    have hrpow : r ≤ 2 ^ r := two_pow_ge r
    have hkpow : k ≤ 2 ^ k := two_pow_ge k
    have hw : (2 ^ r - r) ≡ i [MOD 196] := by simpa [r] using w196_spec i hi
    have hia : i ≡ a [MOD 196] := by
      change a % 196 ≡ a [MOD 196]
      exact Nat.mod_modEq a 196
    have hbase196 : (2 ^ r - r) ≡ a [MOD 196] := hw.trans hia
    have hbase4 : (2 ^ r - r) ≡ a [MOD 4] := hbase196.of_dvd (by norm_num : 4 ∣ 196)
    have h4cast : ((2 ^ k - k : Nat) : ZMod 4) = ((2 ^ r - r : Nat) : ZMod 4) := by
      rw [Nat.cast_sub hkpow, Nat.cast_sub hrpow, Nat.cast_pow, Nat.cast_pow]
      have hpowk0 : (2 : ZMod 4) ^ k = 0 := by
        have hcast : (((2 ^ k : Nat) : ZMod 4) = 0) := by
          rw [ZMod.natCast_eq_zero_iff]
          have hd : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk_ge
          simpa using hd
        simpa [Nat.cast_pow] using hcast
      have hpowr0 : (2 : ZMod 4) ^ r = 0 := by
        have hcast : (((2 ^ r : Nat) : ZMod 4) = 0) := by
          rw [ZMod.natCast_eq_zero_iff]
          have hd : 2 ^ 2 ∣ 2 ^ r := pow_dvd_pow 2 hr_ge
          simpa using hd
        simpa [Nat.cast_pow] using hcast
      have hkr4 : (k : ZMod 4) = (r : ZMod 4) := by
        change ((r + 117600 * t : Nat) : ZMod 4) = (r : ZMod 4)
        simp only [Nat.cast_add, Nat.cast_mul]
        change (r : ZMod 4) + (117600 : ZMod 4) * (t : ZMod 4) = (r : ZMod 4)
        have h117 : (117600 : ZMod 4) = 0 := by
          change ((117600 : Nat) : ZMod 4) = 0
          rw [ZMod.natCast_eq_zero_iff]
          norm_num
        rw [h117, zero_mul, add_zero]
      change (2 : ZMod 4) ^ k - (k : ZMod 4) = (2 : ZMod 4) ^ r - (r : ZMod 4)
      rw [hpowk0, hpowr0, hkr4]
    have hmod4 : (2 ^ k - k) ≡ a [MOD 4] := by
      exact (ZMod.natCast_eq_natCast_iff (2 ^ k - k) a 4).mp
        (h4cast.trans ((ZMod.natCast_eq_natCast_iff (2 ^ r - r) a 4).mpr hbase4))
    have h196dvd : (196 : ℤ) ∣ d := by
      have hdvd := hbase196.symm.dvd
      change (196 : ℤ) ∣ ((2 ^ r : Nat) : Int) - (r : Int) - (a : Int)
      convert hdvd using 1
      rw [Int.ofNat_sub hrpow]
    have h49dvd : (49 : ℤ) ∣ d := (show (49 : ℤ) ∣ (196 : ℤ) by norm_num).trans h196dvd
    have hdu : (49 : ℤ) * u = d := by
      have h := Int.ediv_mul_cancel h49dvd
      change (49 : ℤ) * (d / 49) = d
      rw [mul_comm]
      exact h
    have hpowtopNat : 2 ^ k ≡ 2 ^ r [MOD 137543] := by
      change 2 ^ (r + 117600 * t) ≡ 2 ^ r [MOD 137543]
      rw [pow_add, pow_mul]
      have hperpow : (2 ^ 117600) ^ t ≡ 1 ^ t [MOD 137543] := Nat.ModEq.pow t pow_period_137543
      simpa using (Nat.ModEq.rfl.mul hperpow)
    have hpowtopZ : ((2 ^ k : Nat) : ZMod 137543) = ((2 ^ r : Nat) : ZMod 137543) :=
      (ZMod.natCast_eq_natCast_iff (2 ^ k) (2 ^ r) 137543).mpr hpowtopNat
    have hlin := top_linear u
    have hlinZ : (((117600 * t : Nat) : ℤ) : ZMod 137543) = ((49 * u : ℤ) : ZMod 137543) := by
      change (((117600 * Int.toNat ((1938 * u) % 2807) : Nat) : ℤ) : ZMod 137543) = ((49 * u : ℤ) : ZMod 137543)
      exact (ZMod.intCast_eq_intCast_iff ((117600 * (Int.toNat ((1938 * u) % 2807) : Nat) : ℤ)) (49 * u) 137543).mpr hlin
    have hkZ : (k : ZMod 137543) = ((2 ^ r : Nat) : ZMod 137543) - (a : ZMod 137543) := by
      change ((r + 117600 * t : Nat) : ZMod 137543) = ((2 ^ r : Nat) : ZMod 137543) - (a : ZMod 137543)
      simp only [Nat.cast_add]
      change (r : ZMod 137543) + (((117600 * t : Nat) : ℤ) : ZMod 137543) = ((2 ^ r : Nat) : ZMod 137543) - (a : ZMod 137543)
      rw [hlinZ, hdu]
      change (r : ZMod 137543) + (((((2 ^ r : Nat) : Int) - (r : Int) - (a : Int)) : Int) : ZMod 137543) = ((2 ^ r : Nat) : ZMod 137543) - (a : ZMod 137543)
      rw [Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]
      ring
    have htopcast : ((2 ^ k - k : Nat) : ZMod 137543) = (a : ZMod 137543) := by
      rw [Nat.cast_sub hkpow]
      change ((2 ^ k : Nat) : ZMod 137543) - (k : ZMod 137543) = (a : ZMod 137543)
      rw [hpowtopZ, hkZ]
      ring
    have hmodtop : (2 ^ k - k) ≡ a [MOD 137543] :=
      (ZMod.natCast_eq_natCast_iff (2 ^ k - k) a 137543).mp htopcast
    have hmod550 : (2 ^ k - k) ≡ a [MOD 4 * 137543] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 4 137543)).mp ⟨hmod4, hmodtop⟩
    change (2 ^ k - k) ≡ a [MOD 550172]
    exact hmod550
opaque A232616_prop_mono {n a b : ℕ} [NeZero n] (hab : a ≤ b)
    (ha : A232616_prop n a) : A232616_prop n b := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxu : x ∈ (Finset.univ : Finset (ZMod n)) := Finset.mem_univ x
    have hxa : x ∈ (Finset.Icc 1 a).image (fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)) := by
      rw [ha] at hxu
      exact hxu
    rcases Finset.mem_image.mp hxa with ⟨k, hk, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans hab⟩
  · intro _
    simp
opaque not_A232616_prop_of_nohit {q B : ℕ} [NeZero q] (x : ZMod q)
    (hno : ∀ k : Fin B, 1 ≤ k.val → ((2 : ZMod q) ^ k.val - (k.val : ZMod q)) ≠ x) :
    ¬ A232616_prop q (B - 1) := by
  intro hprop
  have hxuniv : x ∈ (Finset.univ : Finset (ZMod q)) := Finset.mem_univ x
  rw [hprop] at hxuniv
  rcases Finset.mem_image.mp hxuniv with ⟨k, hk, hkx⟩
  rw [Finset.mem_Icc] at hk
  have hkltB : k < B := by omega
  let kfin : Fin B := ⟨k, hkltB⟩
  have hcast : (Nat.cast (2 ^ k - k) : ZMod q) = (2 : ZMod q) ^ k - (k : ZMod q) := by
    rw [Nat.cast_sub (two_pow_ge k), Nat.cast_pow]
    rfl
  have hkx' : ((2 : ZMod q) ^ k - (k : ZMod q)) = x := by
    simpa [hcast] using hkx
  exact hno kfin hk.1 hkx'
opaque A232616_prop_550172_big : A232616_prop 550172 329986075 := by
  apply Finset.ext
  intro x
  constructor
  · intro _hx
    let a := x.val
    have ha : a < 550172 := by simpa [a] using ZMod.val_lt x
    rcases cover_exists_mod a ha with ⟨k, hk1, hkM, hkmod⟩
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨hk1, hkM⟩
    · have hcast : ((2 ^ k - k : ℕ) : ZMod 550172) = (a : ZMod 550172) :=
        (ZMod.natCast_eq_natCast_iff (2 ^ k - k) a 550172).mpr hkmod
      calc
        (Nat.cast (2 ^ k - k) : ZMod 550172) = (a : ZMod 550172) := hcast
        _ = x := by simpa [a] using (ZMod.natCast_zmod_val x).symm
  · intro _hx
    simp
opaque A232616_550172_lower : 17135927 ≤ A232616 550172 := by
  let S : Set ℕ := {m : ℕ | A232616_prop 550172 m}
  have hSnon : S.Nonempty := ⟨329986075, A232616_prop_550172_big⟩
  have hAeq : A232616 550172 = sInf S := by
    simp [A232616, S]
  by_contra hnot
  have hlt : A232616 550172 < 17135927 := Nat.lt_of_not_ge hnot
  have hmem : A232616 550172 ∈ S := by
    rw [hAeq]
    exact Nat.sInf_mem hSnon
  have hpropA : A232616_prop 550172 (A232616 550172) := hmem
  have hle : A232616 550172 ≤ 17135927 - 1 := by omega
  have hpropB : A232616_prop 550172 (17135927 - 1) := A232616_prop_mono hle hpropA
  have hnotprop : ¬ A232616_prop 550172 (17135927 - 1) :=
    not_A232616_prop_of_nohit (q := 550172) (B := 17135927) (63945 : ZMod 550172) nohit_63945_before
  exact hnotprop hpropB
theorem oeis_232616_conjecture_i.disproof :
    ¬ (∀ (n : ℕ), 0 < n →
       A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro h
  have hc := h 550172 (by norm_num : 0 < 550172)
  have hp : Nat.nth Nat.Prime (550172 - 1) ≤ 8567964 := by
    simpa using nth_prime_bound
  have hrhs : 2 * (Nat.nth Nat.Prime (550172 - 1) - 1) ≤ 17135926 := by
    omega
  have hlt : A232616 550172 < 17135927 := by
    omega
  have hlower := A232616_550172_lower
  omega
