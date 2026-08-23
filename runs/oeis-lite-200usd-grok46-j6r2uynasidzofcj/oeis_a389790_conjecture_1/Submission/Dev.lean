import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

theorem next_prime_spec (r : ℕ) :
    Nat.Prime (next_prime r) ∧ r < next_prime r ∧
      ∀ k, Nat.Prime k → r < k → next_prime r ≤ k := by
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (r + 1)
    exact ⟨p, hprime, Nat.lt_of_succ_le hp⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.sInf_mem hne).1
  · exact (Nat.sInf_mem hne).2
  · intro k hk hlt
    exact Nat.sInf_le ⟨hk, hlt⟩

theorem next_prime_eq {r p : ℕ} (hp : Nat.Prime p) (hlt : r < p)
    (hmin : ∀ k, r < k → k < p → ¬ Nat.Prime k) : next_prime r = p := by
  have h := next_prime_spec r
  apply le_antisymm
  · exact h.2.2 p hp hlt
  · have hle : next_prime r ≤ p := h.2.2 p hp hlt
    rcases eq_or_lt_of_le hle with h_eq | h_lt
    · exact h_eq.symm.le
    · exact absurd h.1 (hmin (next_prime r) h.2.1 h_lt)

theorem next_prime_two : next_prime 2 = 3 :=
  next_prime_eq Nat.prime_three (by omega) (by
    intro k hk1 hk2; interval_cases k)

theorem next_prime_three : next_prime 3 = 5 :=
  next_prime_eq Nat.prime_five (by omega) (by
    intro k hk1 hk2
    interval_cases k
    · decide)

theorem next_prime_five : next_prime 5 = 7 :=
  next_prime_eq Nat.prime_seven (by omega) (by
    intro k hk1 hk2
    interval_cases k
    · decide)

noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range n
  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

theorem a_pos_of_pair {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    (hpn : p < n) (hqn : q < n)
    (hsum : S_sum p + S_sum q = 2 * n) : 0 < a n := by
  refine Finset.card_pos.mpr ?_
  refine ⟨(p, q), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨hpn, hqn⟩, hp, hq, hpq, hsum⟩

theorem not_prime_of_minFac {n : ℕ} (h : n.minFac ≠ n) : ¬ n.Prime := by
  intro hp
  exact h hp.minFac_eq

theorem next_prime_seven : next_prime 7 = 11 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem next_prime_463 : next_prime 463 = 467 :=
  next_prime_eq (by norm_num) (by omega) (by
    intro k hk1 hk2
    interval_cases k <;> (apply not_prime_of_minFac; norm_num))

theorem a_474_pos : 0 < a 474 := by
  apply a_pos_of_pair (p := 7) (q := 463)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [next_prime_seven, next_prime_463]

/-- Explicit trial division. -/
def trialDiv (n d : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.blt n (d * d) then true
    else if n % d == 0 then false
    else trialDiv n (d + 1) fuel

-- Fully Bool-based primality so it reduces under `open Classical`.
def isPrimeBool (n : ℕ) : Bool :=
  if Nat.blt n 2 then false else trialDiv n 2 n

example : isPrimeBool 17 = true := rfl
example : isPrimeBool 18 = false := rfl
example : isPrimeBool 97 = true := rfl
example : isPrimeBool 1 = false := rfl
example : isPrimeBool 4 = false := rfl

def nextPrimeGo (k : ℕ) : ℕ → ℕ
  | 0 => k
  | f + 1 => if isPrimeBool k then k else nextPrimeGo (k + 1) f

/-- Next prime after `n`, searching at most `fuel` candidates starting at `n+1`. -/
def nextPrimeFuel (n fuel : ℕ) : ℕ := nextPrimeGo (n + 1) fuel

def nextPrimeComp (n : ℕ) : ℕ := nextPrimeFuel n (n + 3)

example : nextPrimeComp 2 = 3 := rfl
example : nextPrimeComp 3 = 5 := rfl
example : nextPrimeComp 7 = 11 := rfl
example : nextPrimeComp 463 = 467 := rfl

/-- Is `m` a sum of two consecutive primes (the smaller being odd, or 2)? -/
def isSsumBool (m : ℕ) : Bool :=
  let rec go (q : ℕ) : ℕ → Bool
    | 0 => false
    | f + 1 =>
      if isPrimeBool q && (q + nextPrimeComp q == m) then true
      else go (q + 1) f
  go 2 m

example : isSsumBool 8 = true := rfl   -- 3+5
example : isSsumBool 12 = true := rfl  -- 5+7
example : isSsumBool 10 = false := rfl

def hasRep (n : ℕ) : Bool :=
  let rec go (p : ℕ) : ℕ → Bool
    | 0 => false
    | f + 1 =>
      if isPrimeBool p && Nat.ble (p + nextPrimeComp p) n &&
          isSsumBool (2 * n - (p + nextPrimeComp p)) then true
      else go (p + 1) f
  go 2 n

set_option maxRecDepth 1000000

def primesUpTo (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun k => isPrimeBool k)

/-- Consecutive pair-sums of a list. -/
def consecutiveSums : List ℕ → List ℕ
  | p :: p' :: rest => (p + p') :: consecutiveSums (p' :: rest)
  | _ => []

def ssumList (n : ℕ) : List ℕ :=
  let ps := primesUpTo n
  match ps.getLast? with
  | none => []
  | some lastP =>
    let inner := consecutiveSums ps
    let nxt := nextPrimeComp lastP
    if Nat.blt n nxt then inner ++ [lastP + nxt] else inner

example : ssumList 10 = [5, 8, 12, 18] := rfl

def listHas (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => if x == y then true else listHas x ys

def listHasPair (n : ℕ) (ss : List ℕ) : List ℕ → Bool
  | [] => false
  | s :: rest =>
    if Nat.ble s n && listHas (2 * n - s) ss then true
    else listHasPair n ss rest

def hasRepFast (n : ℕ) : Bool :=
  let ss := ssumList n
  listHasPair n ss ss

example : hasRepFast 8 = true := rfl
example : hasRepFast 5 = true := rfl
example : hasRepFast 4 = false := rfl
example : hasRepFast 474 = true := rfl
example : hasRepFast 473 = false := rfl

def checkFrom (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => hasRepFast (lo + n) && checkFrom lo n

-- checkFrom lo (k) checks hasRepFast for n = lo, lo+1, ..., lo+k-1
example : checkFrom 474 5 = true := rfl  -- 474..478
example : checkFrom 474 30 = true := rfl  -- 474..503

theorem trialDiv_true_spec {n d fuel : ℕ}
    (hfuel : n < (d + fuel) * (d + fuel))
    (h : trialDiv n d fuel = true) :
    ∀ k, d ≤ k → k * k ≤ n → ¬ k ∣ n := by
  induction fuel generalizing d with
  | zero =>
    intro k hdk hkk hdvd
    simp at hfuel
    have hlt : k * k < d * d := Nat.lt_of_le_of_lt hkk hfuel
    have hk : k < d := Nat.mul_self_lt_mul_self_iff.mp hlt
    omega
  | succ fuel ih =>
    intro k hdk hkk hdvd
    simp only [trialDiv] at h
    by_cases hsq : Nat.blt n (d * d)
    · simp [hsq] at h
      have : n < d * d := Nat.blt_eq.mp hsq
      have : k * k < d * d := Nat.lt_of_le_of_lt hkk this
      have : k < d := Nat.mul_self_lt_mul_self_iff.mp this
      omega
    · simp [hsq] at h
      obtain ⟨hmod, htrue⟩ := h
      have hfuel' : n < (d + 1 + fuel) * (d + 1 + fuel) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel
      rcases lt_or_eq_of_le hdk with hlt | heq
      · exact ih hfuel' htrue k (by omega) hkk hdvd
      · subst heq
        exact hmod (Nat.dvd_iff_mod_eq_zero.mp hdvd)

theorem isPrimeBool_prime {n : ℕ} (h : isPrimeBool n = true) : n.Prime := by
  unfold isPrimeBool at h
  by_cases hn : Nat.blt n 2
  · simp [hn] at h
  · simp [hn] at h
    have hn2 : 2 ≤ n := by
      have : ¬ n < 2 := mt Nat.blt_eq.mpr hn
      omega
    have hfuel : n < (2 + n) * (2 + n) := by nlinarith
    have hdiv := trialDiv_true_spec hfuel h
    rw [Nat.prime_def_le_sqrt]
    refine ⟨hn2, ?_⟩
    intro m hm2 hmsqrt
    have hkk : m * m ≤ n := (Nat.le_sqrt.mp hmsqrt)
    exact hdiv m hm2 hkk

theorem trialDiv_true_of {n d fuel : ℕ}
    (h : ∀ k, d ≤ k → k * k ≤ n → ¬ k ∣ n) :
    trialDiv n d fuel = true := by
  induction fuel generalizing d with
  | zero => simp [trialDiv]
  | succ fuel ih =>
    simp only [trialDiv]
    by_cases hsq : Nat.blt n (d * d)
    · simp [hsq]
    · simp [hsq]
      constructor
      · intro hdv
        have : d ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hdv
        have hd2 : d * d ≤ n := le_of_not_gt (mt Nat.blt_eq.mpr hsq)
        exact h d le_rfl hd2 this
      · apply ih
        intro k hk hkk
        exact h k (Nat.le_of_succ_le hk) hkk

theorem isPrimeBool_of_prime {n : ℕ} (hp : n.Prime) : isPrimeBool n = true := by
  unfold isPrimeBool
  have hn2 : 2 ≤ n := hp.two_le
  have hblt : Nat.blt n 2 = false := by
    have : ¬ n < 2 := not_lt.mpr hn2
    cases hb : Nat.blt n 2
    · rfl
    · exact absurd (Nat.blt_eq.mp hb) this
  simp [hblt]
  apply trialDiv_true_of
  intro k hk hkk hdvd
  have hsqrt : k ≤ n.sqrt := Nat.le_sqrt.mpr hkk
  exact (Nat.prime_def_le_sqrt.mp hp).2 k hk hsqrt hdvd

theorem isPrimeBool_false_of_not_prime {m : ℕ} (h : ¬ m.Prime) : isPrimeBool m = false := by
  cases hm : isPrimeBool m
  · rfl
  · exact absurd (isPrimeBool_prime hm) h

theorem isPrimeBool_iff (n : ℕ) : isPrimeBool n = true ↔ n.Prime :=
  ⟨isPrimeBool_prime, isPrimeBool_of_prime⟩

theorem sInf_primes_ge_eq {k : ℕ} (hnp : ¬ k.Prime) :
    sInf {p : ℕ | p.Prime ∧ k ≤ p} = sInf {p : ℕ | p.Prime ∧ k + 1 ≤ p} := by
  have hset : {p : ℕ | p.Prime ∧ k ≤ p} = {p : ℕ | p.Prime ∧ k + 1 ≤ p} := by
    ext p
    constructor
    · intro ⟨hp, hkp⟩
      refine ⟨hp, ?_⟩
      have : k ≠ p := fun e => hnp (e ▸ hp)
      omega
    · intro ⟨hp, hkp⟩
      exact ⟨hp, Nat.le_of_succ_le hkp⟩
  rw [hset]

theorem nextPrimeGo_eq {k fuel : ℕ}
    (hex : ∃ p, p.Prime ∧ k ≤ p ∧ p ≤ k + fuel) :
    nextPrimeGo k fuel = sInf {p : ℕ | p.Prime ∧ k ≤ p} := by
  induction fuel generalizing k with
  | zero =>
    obtain ⟨p, hp, hkp, hpk⟩ := hex
    have heq : p = k := Nat.le_antisymm hpk hkp
    rw [heq] at hp
    have hmem : k ∈ {q : ℕ | q.Prime ∧ k ≤ q} := ⟨hp, le_rfl⟩
    simp [nextPrimeGo]
    apply le_antisymm
    · exact le_csInf ⟨_, hmem⟩ (fun b hb => hb.2)
    · exact Nat.sInf_le hmem
  | succ fuel ih =>
    by_cases hk : isPrimeBool k = true
    · have hp : k.Prime := isPrimeBool_prime hk
      have hmem : k ∈ {p : ℕ | p.Prime ∧ k ≤ p} := ⟨hp, le_rfl⟩
      simp [nextPrimeGo, hk]
      apply le_antisymm
      · exact le_csInf ⟨_, hmem⟩ (fun b hb => hb.2)
      · exact Nat.sInf_le hmem
    · have hnp : ¬ k.Prime := fun hp => hk (isPrimeBool_of_prime hp)
      have hkb : isPrimeBool k = false := isPrimeBool_false_of_not_prime hnp
      simp [nextPrimeGo, hkb]
      have hex' : ∃ p, p.Prime ∧ k + 1 ≤ p ∧ p ≤ k + 1 + fuel := by
        obtain ⟨p, hp, hkp, hpk⟩ := hex
        refine ⟨p, hp, ?_, by omega⟩
        have : k ≠ p := fun e => hnp (e ▸ hp)
        omega
      rw [ih hex', sInf_primes_ge_eq hnp]

theorem next_prime_eq_sInf_ge (r : ℕ) :
    next_prime r = sInf {p : ℕ | p.Prime ∧ r + 1 ≤ p} := by
  unfold next_prime
  simp [Nat.succ_le_iff]

theorem nextPrimeComp_eq (r : ℕ) : nextPrimeComp r = next_prime r := by
  unfold nextPrimeComp nextPrimeFuel
  have hex : ∃ p, p.Prime ∧ r + 1 ≤ p ∧ p ≤ r + 1 + (r + 3) := by
    cases r with
    | zero =>
      exact ⟨2, Nat.prime_two, by omega, by omega⟩
    | succ r =>
      obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (r + 1) (by omega)
      refine ⟨p, hp, Nat.succ_le_of_lt hlt, ?_⟩
      have : p ≤ 2 * (r + 1) := hle
      omega
  rw [nextPrimeGo_eq hex, next_prime_eq_sInf_ge]

theorem mem_primesUpTo {n p : ℕ} (hp : p ∈ primesUpTo n) :
    p.Prime ∧ p ≤ n := by
  simp [primesUpTo, List.mem_filter, List.mem_range] at hp
  exact ⟨isPrimeBool_prime hp.2, hp.1⟩

theorem primesUpTo_complete {n p : ℕ} (hp : p.Prime) (hle : p ≤ n) :
    p ∈ primesUpTo n := by
  simp [primesUpTo, List.mem_filter, List.mem_range]
  exact ⟨hle, isPrimeBool_of_prime hp⟩

theorem S_sum_eq (p : ℕ) : S_sum p = p + nextPrimeComp p := by
  unfold S_sum
  rw [nextPrimeComp_eq]

theorem consecutive_primes_ssum {p p' : ℕ}
    (hp' : p'.Prime) (hlt : p < p')
    (hnone : ∀ k, p < k → k < p' → ¬ k.Prime) :
    S_sum p = p + p' := by
  unfold S_sum
  rw [next_prime_eq hp' hlt hnone]

theorem listHas_iff {x : ℕ} {l : List ℕ} : listHas x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [listHas]
  | cons y ys ih =>
    simp only [listHas, List.mem_cons]
    by_cases hxy : x == y
    · simp [hxy]
      have : x = y := beq_iff_eq.mp hxy
      simp [this]
    · simp [hxy]
      have : x ≠ y := fun e => hxy (beq_iff_eq.mpr e)
      simp [this, ih]

theorem listHasPair_true {n : ℕ} {ss l : List ℕ} (h : listHasPair n ss l = true) :
    ∃ s, s ∈ l ∧ s ≤ n ∧ (2 * n - s) ∈ ss := by
  induction l with
  | nil => simp [listHasPair] at h
  | cons s rest ih =>
    simp only [listHasPair] at h
    cases hb : (Nat.ble s n && listHas (2 * n - s) ss) with
    | false =>
      simp [hb] at h
      obtain ⟨s', hs', hle, hmem⟩ := ih h
      exact ⟨s', List.mem_cons_of_mem _ hs', hle, hmem⟩
    | true =>
      have hab := Bool.and_eq_true_iff.mp hb
      exact ⟨s, List.mem_cons_self, Nat.le_of_ble_eq_true hab.1, listHas_iff.mp hab.2⟩

theorem mem_consecutiveSums_cons {p p' : ℕ} {rest : List ℕ} {s : ℕ} :
    s ∈ consecutiveSums (p :: p' :: rest) ↔
      s = p + p' ∨ s ∈ consecutiveSums (p' :: rest) := by
  simp [consecutiveSums]

theorem mem_consecutiveSums_short {ps : List ℕ} (h : ps.length ≤ 1) {s : ℕ} :
    s ∉ consecutiveSums ps := by
  match ps with
  | [] => simp [consecutiveSums]
  | [x] => simp [consecutiveSums]
  | _ :: _ :: _ => simp at h

theorem exists_consecutive_of_mem_sums {ps : List ℕ} {s : ℕ}
    (h : s ∈ consecutiveSums ps) :
    ∃ i : ℕ, ∃ hi : i + 1 < ps.length,
      s = ps[i]'(Nat.lt_of_succ_lt hi) + ps[i + 1]'hi := by
  induction ps with
  | nil => simp [consecutiveSums] at h
  | cons p rest ih =>
    match rest with
    | [] => simp [consecutiveSums] at h
    | p' :: rest' =>
      rw [mem_consecutiveSums_cons] at h
      rcases h with h | h
      · refine ⟨0, ?_, ?_⟩
        · simp
        · simp [h]
      · obtain ⟨i, hi, hs⟩ := ih h
        refine ⟨i + 1, ?_, ?_⟩
        · simpa using hi
        · simpa using hs

theorem primesUpTo_get_prime {n : ℕ} {i : ℕ} (hi : i < (primesUpTo n).length) :
    ((primesUpTo n)[i]).Prime ∧ (primesUpTo n)[i] ≤ n :=
  mem_primesUpTo (List.getElem_mem hi)

theorem primesUpTo_pairwise (n : ℕ) : (primesUpTo n).Pairwise (· < ·) := by
  simpa [primesUpTo] using (List.pairwise_lt_range (n := n + 1)).filter (fun k => isPrimeBool k)

theorem primesUpTo_lt {n i j : ℕ}
    (hi : i < (primesUpTo n).length) (hj : j < (primesUpTo n).length) (hij : i < j) :
    (primesUpTo n)[i] < (primesUpTo n)[j] :=
  List.Pairwise.rel_get_of_lt (primesUpTo_pairwise n) hij

theorem index_lt_of_primesUpTo_lt {n i j : ℕ}
    (hi : i < (primesUpTo n).length) (hj : j < (primesUpTo n).length)
    (h : (primesUpTo n)[i] < (primesUpTo n)[j]) : i < j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact hij
  · exact (lt_irrefl _ h).elim
  · exact (lt_asymm h (primesUpTo_lt hj hi hij)).elim

theorem no_prime_between_primesUpTo {n i : ℕ} (hi : i + 1 < (primesUpTo n).length)
    {k : ℕ} (hk1 : (primesUpTo n)[i] < k) (hk2 : k < (primesUpTo n)[i + 1]) :
    ¬ k.Prime := by
  intro hp
  have hklen : k ≤ n := by
    have := (primesUpTo_get_prime (show i + 1 < (primesUpTo n).length from hi)).2
    omega
  have hkin := primesUpTo_complete hp hklen
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hkin
  have h1 : i < j := index_lt_of_primesUpTo_lt (by omega) hj hk1
  have h2 : j < i + 1 := index_lt_of_primesUpTo_lt hj (by omega) hk2
  omega

theorem getLast?_eq_getLast {l : List ℕ} (h : l ≠ []) :
    l.getLast? = some (l.getLast h) := by
  cases l with
  | nil => contradiction
  | cons x xs => simp [List.getLast?]

theorem primesUpTo_getLast_spec {n : ℕ} (h : primesUpTo n ≠ []) :
    (primesUpTo n).getLast h = n.minFac ∨
      ((primesUpTo n).getLast h).Prime ∧ (primesUpTo n).getLast h ≤ n := by
  have := mem_primesUpTo (List.getLast_mem h)
  exact Or.inr this

theorem mem_consecutiveSums_ssum {n s : ℕ}
    (h : s ∈ consecutiveSums (primesUpTo n)) :
    ∃ p, p.Prime ∧ p ≤ n ∧ S_sum p = s := by
  obtain ⟨i, hi, hs⟩ := exists_consecutive_of_mem_sums h
  have hi0 : i < (primesUpTo n).length := Nat.lt_of_succ_lt hi
  let p := (primesUpTo n)[i]
  let p' := (primesUpTo n)[i + 1]
  have hp := primesUpTo_get_prime hi0
  have hp' := primesUpTo_get_prime hi
  have hlt : p < p' := primesUpTo_lt hi0 hi (Nat.lt_succ_self i)
  have hnone : ∀ k, p < k → k < p' → ¬ k.Prime :=
    fun k => no_prime_between_primesUpTo hi
  refine ⟨p, hp.1, hp.2, ?_⟩
  have hseq : s = p + p' := hs
  rw [hseq]
  exact consecutive_primes_ssum hp'.1 hlt hnone

theorem last_prime_ssum {n p : ℕ} (hps : (primesUpTo n).getLast? = some p) :
    p.Prime ∧ p ≤ n ∧ S_sum p = p + nextPrimeComp p := by
  have hne : primesUpTo n ≠ [] := by
    intro he
    simp [he] at hps
  have hgl : (primesUpTo n).getLast hne = p := by
    have := getLast?_eq_getLast (l := primesUpTo n) hne
    rw [this] at hps
    exact Option.some.inj hps
  have hmem : p ∈ primesUpTo n := by
    rw [← hgl]
    exact List.getLast_mem hne
  obtain ⟨hp, hle⟩ := mem_primesUpTo hmem
  exact ⟨hp, hle, S_sum_eq p⟩

theorem mem_ssumList {n s : ℕ} (h : s ∈ ssumList n) :
    ∃ p, p.Prime ∧ p ≤ n ∧ S_sum p = s := by
  dsimp [ssumList] at h
  cases hlast : (primesUpTo n).getLast? with
  | none =>
    rw [hlast] at h
    simp at h
  | some lastP =>
    rw [hlast] at h
    cases hblt : Nat.blt n (nextPrimeComp lastP) with
    | true =>
      simp [hblt] at h
      rcases h with h | h
      · exact mem_consecutiveSums_ssum h
      · refine ⟨lastP, ?_⟩
        have spec := last_prime_ssum hlast
        exact ⟨spec.1, spec.2.1, by rw [spec.2.2, h]⟩
    | false =>
      simp [hblt] at h
      exact mem_consecutiveSums_ssum h

theorem hasRepFast_pos {n : ℕ} (h : hasRepFast n = true) : 0 < a n := by
  unfold hasRepFast at h
  obtain ⟨s, hs, hle, hmem⟩ := listHasPair_true h
  obtain ⟨p, hp, hp_le, hpS⟩ := mem_ssumList hs
  obtain ⟨q, hq, hq_le, hqS⟩ := mem_ssumList hmem
  have hsum : S_sum p + S_sum q = 2 * n := by
    rw [hpS, hqS]
    exact Nat.add_sub_of_le (by omega)
  have hpn : p < n := by
    by_contra hnp
    have heq : p = n := Nat.le_antisymm hp_le (Nat.le_of_not_lt hnp)
    have hgt : n < next_prime n := (next_prime_spec n).2.1
    have hsS : s = n + next_prime n := by
      rw [← hpS, heq]
      rfl
    omega
  have hqn : q < n := by
    by_contra hnq
    have heq : q = n := Nat.le_antisymm hq_le (Nat.le_of_not_lt hnq)
    have hgt : n < next_prime n := (next_prime_spec n).2.1
    have hqseq : 2 * n - s = n + next_prime n := by
      rw [← hqS, heq]
      rfl
    omega
  rcases le_total p q with hpq | hqp
  · exact a_pos_of_pair hp hq hpq hpn hqn hsum
  · exact a_pos_of_pair hq hp hqp hqn hpn (by rw [Nat.add_comm, hsum])

set_option maxHeartbeats 2000000
example : 0 < a 2501 := by
  apply a_pos_of_pair (p := 23) (q := 2473)
  · norm_num
  · norm_num
  · omega
  · omega
  · omega
  · unfold S_sum
    rw [← nextPrimeComp_eq, ← nextPrimeComp_eq]
    rfl

theorem checkFrom_pos {lo k : ℕ} (h : checkFrom lo k = true) :
    ∀ n, lo ≤ n → n < lo + k → 0 < a n := by
  induction k with
  | zero =>
    intro n hlo hn
    omega
  | succ k ih =>
    simp only [checkFrom] at h
    have hab := Bool.and_eq_true_iff.mp h
    intro n hlo hn
    have : n = lo + k ∨ n < lo + k := by omega
    rcases this with rfl | hlt
    · exact hasRepFast_pos hab.1
    · exact ih hab.2 n hlo hlt











/-- An interprime: the average of two consecutive odd primes. -/
def IsInterprime (k : ℕ) : Prop :=
  ∃ p, p.Prime ∧ 2 < p ∧ p < k ∧ S_sum p = 2 * k

theorem a_pos_of_interprimes {n m k : ℕ}
    (hm : IsInterprime m) (hk : IsInterprime k) (hsum : m + k = n) :
    0 < a n := by
  obtain ⟨p, hp, hp2, hpm, hSp⟩ := hm
  obtain ⟨q, hq, hq2, hqk, hSq⟩ := hk
  have hpn : p < n := by omega
  have hqn : q < n := by omega
  have hsumS : S_sum p + S_sum q = 2 * n := by
    calc S_sum p + S_sum q = 2 * m + 2 * k := by simp [hSp, hSq]
      _ = 2 * (m + k) := by ring
      _ = 2 * n := by rw [hsum]
  rcases le_total p q with hpq | hqp
  · exact a_pos_of_pair hp hq hpq hpn hqn hsumS
  · exact a_pos_of_pair hq hp hqp hqn hpn (by rw [Nat.add_comm, hsumS])

theorem isInterprime_of_consecutive {p p' : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hp2 : 2 < p) (hlt : p < p')
    (hnone : ∀ k, p < k → k < p' → ¬ k.Prime) :
    IsInterprime ((p + p') / 2) := by
  have hnp : next_prime p = p' := next_prime_eq hp' hlt hnone
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hp'_odd : Odd p' := hp'.odd_of_ne_two (by omega)
  have h2 : Even (p + p') := hp_odd.add_odd hp'_odd
  have hdiv : 2 ∣ p + p' := even_iff_two_dvd.mp h2
  refine ⟨p, hp, hp2, ?_, ?_⟩
  · have hmul : 2 * ((p + p') / 2) = p + p' := Nat.mul_div_cancel' hdiv
    have : 2 * p < 2 * ((p + p') / 2) := by
      rw [hmul]; omega
    exact (mul_lt_mul_iff_right₀ (by omega : 0 < 2)).mp this
  · unfold S_sum
    rw [hnp]
    have : 2 * ((p + p') / 2) = p + p' := Nat.mul_div_cancel' hdiv
    exact this.symm

theorem isInterprime_4 : IsInterprime 4 := by
  have h := isInterprime_of_consecutive (p := 3) (p' := 5) Nat.prime_three Nat.prime_five
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_6 : IsInterprime 6 := by
  have h := isInterprime_of_consecutive (p := 5) (p' := 7) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k
        apply not_prime_of_minFac
        norm_num)
  simpa using h

theorem isInterprime_9 : IsInterprime 9 := by
  have h := isInterprime_of_consecutive (p := 7) (p' := 11) (by norm_num) (by norm_num)
      (by omega) (by omega) (by
        intro k hk1 hk2
        interval_cases k <;> (apply not_prime_of_minFac; norm_num))
  simpa using h

theorem a_pos_of_sub_interprime (n m : ℕ) (hm : IsInterprime m)
    (hnm : IsInterprime (n - m)) (hle : m ≤ n) : 0 < a n :=
  a_pos_of_interprimes hm hnm (Nat.add_sub_of_le hle)

theorem a_pos_of_sub4 {n : ℕ} (h : 4 ≤ n) (hm : IsInterprime (n - 4)) : 0 < a n :=
  a_pos_of_sub_interprime n 4 isInterprime_4 hm h

theorem a_pos_of_sub6 {n : ℕ} (h : 6 ≤ n) (hm : IsInterprime (n - 6)) : 0 < a n :=
  a_pos_of_sub_interprime n 6 isInterprime_6 hm h

/-- The previous prime strictly below `k` (for `k ≥ 3`). -/
noncomputable def prev_prime (k : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ p < k}

theorem prev_prime_spec {k : ℕ} (hk : 3 ≤ k) :
    (prev_prime k).Prime ∧ prev_prime k < k ∧
      ∀ p, p.Prime → p < k → p ≤ prev_prime k := by
  let S := {p : ℕ | p.Prime ∧ p < k}
  have h2 : 2 ∈ S := ⟨Nat.prime_two, by omega⟩
  have hne : S.Nonempty := ⟨2, h2⟩
  have hfin : S.Finite := (Set.finite_lt_nat k).subset (fun _ hp => hp.2)
  refine ⟨?_, ?_, ?_⟩
  · exact (hfin.sSup_mem hne).1
  · exact (hfin.sSup_mem hne).2
  · intro p hp hpk
    exact hfin.le_sSup ⟨hp, hpk⟩

theorem isInterprime_not_prime {k : ℕ} (h : IsInterprime k) : ¬ k.Prime := by
  intro hk
  obtain ⟨p, hp, hp2, hpk, hS⟩ := h
  have hsum : p + next_prime p = 2 * k := by simpa [S_sum] using hS
  have hgt : k < next_prime p := by omega
  have hle := (next_prime_spec p).2.2 k hk hpk
  omega

theorem next_prime_of_prev {k : ℕ} (hk : 3 ≤ k) :
    next_prime (prev_prime k) = k ∨ k < next_prime (prev_prime k) := by
  have hps := prev_prime_spec hk
  have hnp := next_prime_spec (prev_prime k)
  have : prev_prime k < next_prime (prev_prime k) := hnp.2.1
  have : ¬ next_prime (prev_prime k) < k := by
    intro hlt
    have := hps.2.2 _ hnp.1 hlt
    omega
  omega

theorem isInterprime_iff_prev_next {k : ℕ} (hk : 4 ≤ k) :
    IsInterprime k ↔ ¬ k.Prime ∧ prev_prime k + next_prime k = 2 * k := by
  have hps := prev_prime_spec (k := k) (by omega)
  have hns := next_prime_spec k
  constructor
  · intro h
    refine ⟨isInterprime_not_prime h, ?_⟩
    obtain ⟨p, hp, hp2, hpk, hS⟩ := h
    have hsum : p + next_prime p = 2 * k := by simpa [S_sum] using hS
    have hklt : k < next_prime p := by omega
    have hprev : prev_prime k = p := by
      apply le_antisymm
      · by_contra hnp
        have := (next_prime_spec p).2.2 (prev_prime k) hps.1 (by omega)
        omega
      · exact hps.2.2 p hp hpk
    have hnxt : next_prime k = next_prime p := by
      apply le_antisymm
      · exact hns.2.2 (next_prime p) (next_prime_spec p).1 hklt
      · exact (next_prime_spec p).2.2 (next_prime k) hns.1 (by omega)
    omega
  · intro ⟨hnpk, hsum⟩
    refine ⟨prev_prime k, hps.1, ?_, hps.2.1, ?_⟩
    · have hne2 : prev_prime k ≠ 2 := by
        intro h2
        have : 3 ≤ prev_prime k := hps.2.2 3 Nat.prime_three (by omega)
        omega
      omega
    · unfold S_sum
      have hnxt : next_prime (prev_prime k) = next_prime k := by
        apply le_antisymm
        · exact (next_prime_spec (prev_prime k)).2.2 (next_prime k) hns.1 (by omega)
        · rcases next_prime_of_prev (k := k) (by omega) with heq | hlt
          · exact absurd (heq ▸ (next_prime_spec (prev_prime k)).1) hnpk
          · exact hns.2.2 _ (next_prime_spec (prev_prime k)).1 hlt
      omega

example : 0 < a 10 := a_pos_of_interprimes isInterprime_4 isInterprime_6 (by norm_num)

/- The completed proof of `exists_even_interprime_gt` lives in Spec.lean. -/
theorem exists_even_interprime_gt_placeholder (N : ℕ) : ∃ k, N ≤ k ∧ Even k ∧ IsInterprime k := by
  -- All primes ≥ max(N, 3) would share one residue mod 4 if even interprimes died out.
  let P0 := max N 3
  obtain ⟨p1, hp1gt, hp1p, hp1mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq P0 (q := 4) (a := 1) (by decide) (by decide)
  obtain ⟨p3, hp3gt, hp3p, hp3mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq p1 (q := 4) (a := 3) (by decide) (by decide)
  -- There is a first prime ≡ 3 (mod 4) after p1; its predecessor is a prime ≥ p1 ≡ 1 (mod 4).
  -- So some consecutive pair is mixed. We search the finite interval (p1, p3].
  have hlt : p1 < p3 := hp3gt
  -- Use p3 and the previous prime before p3.
  have hp3ge3 : 3 ≤ p3 := by
    have : 2 < p3 := lt_trans (by omega : 2 < p1) hlt
    omega
  let prev : ℕ := sSup {p : ℕ | p.Prime ∧ p < p3}
  have hSne : {p : ℕ | p.Prime ∧ p < p3}.Nonempty := ⟨2, Nat.prime_two, by omega⟩
  have hSbdd : BddAbove {p : ℕ | p.Prime ∧ p < p3} := ⟨p3, fun x hx => le_of_lt hx.2⟩
  have hprev_mem : prev ∈ {p : ℕ | p.Prime ∧ p < p3} := Nat.sSup_mem hSne hSbdd
  have hprevp : prev.Prime := hprev_mem.1
  have hprevlt : prev < p3 := hprev_mem.2
  have hnone : ∀ k, prev < k → k < p3 → ¬ k.Prime := by
    intro k hk1 hk2 hk
    have : k ≤ prev := Nat.le_sSup hSbdd ⟨hk, hk2⟩
    omega
  have hprev_ge : p1 ≤ prev := by
    have : p1 ∈ {p : ℕ | p.Prime ∧ p < p3} := ⟨hp1p, hlt⟩
    exact Nat.le_sSup hSbdd this
  have hmid : IsInterprime ((prev + p3) / 2) :=
    isInterprime_of_consecutive hprevp hp3p (by
      have : 2 < p1 := by
        have : 3 ≤ p1 := by
          have hP : 3 ≤ P0 := le_max_right _ _
          omega
        omega
      omega) hprevlt hnone
  refine ⟨(prev + p3) / 2, ?_, ?_, hmid⟩
  · have hdiv : 2 ∣ prev + p3 := by
      have ho1 : Odd prev := hprevp.odd_of_ne_two (by
        have : 2 < p1 := by omega
        have : 2 < prev := lt_of_lt_of_le this hprev_ge
        omega)
      have ho2 : Odd p3 := hp3p.odd_of_ne_two (by omega)
      exact even_iff_two_dvd.mp (ho1.add_odd ho2)
    have : prev ≤ (prev + p3) / 2 := by
      have hmul := Nat.mul_div_cancel' hdiv
      have : 2 * prev ≤ prev + p3 := by omega
      have : 2 * prev ≤ 2 * ((prev + p3) / 2) := by simpa [hmul]
      exact (Nat.mul_le_mul_iff_right (by omega : 0 < 2)).1 this
    have : N ≤ prev := le_trans (le_max_left N 3) (le_trans (Nat.le_of_lt hp1gt) hprev_ge)
    omega
  · -- prev ≡ 1 [MOD 4] or mixed with p3 ≡ 3. Midpoint even iff gap ≡ 2 [MOD 4].
    -- p3 ≡ 3 [MOD 4]. If prev ≡ 1, gap ≡ 2 [MOD 4], midpoint even. If prev ≡ 3, gap ≡ 0, midpoint odd.
    -- If prev ≡ 3, then this pair is not mixed; but then we look further... 
    -- Actually prev ≥ p1 ≡ 1, but prev could be ≡ 3.
    -- Key: if prev ≡ 1 [MOD 4] we are done. If prev ≡ 3, then (prev,p3) both 3, midpoint odd.
    -- In that case take the pair (p1, next p1) and walk until we find a mixed pair.
    -- Since p1 ≡ 1 and p3 ≡ 3, the first time we jump from 1-class to 3-class is mixed.
    -- prev is the prime immediately before p3. If prev ≡ 1 we are mixed. If prev ≡ 3,
    -- then p3 is not the FIRST 3 after p1. Still prev could be 3.
    -- Wait: we only need SOME mixed pair between p1 and p3. The pair (prev, p3):
    -- if prev ≡ 1, mixed. If prev ≡ 3, not mixed.
    -- There MUST be a mixed pair because we go from a 1 to a 3.
    -- We'll prove existence of a mixed consecutive pair in (p1-ε, p3] by contradiction:
    -- if all consecutive pairs from p1 to p3 are unmixed, all these primes share p1's residue,
    -- so p3 ≡ 1, contradiction.
    have ho1 : Odd prev := hprevp.odd_of_ne_two (by omega)
    have ho2 : Odd p3 := hp3p.odd_of_ne_two (by omega)
    have hdiv : 2 ∣ prev + p3 := even_iff_two_dvd.mp (ho1.add_odd ho2)
    -- Prove prev ≢ p3 (mod 4) by showing there is a mixed pair; specifically this pair or we
    -- use a different argument.
    -- Simpler approach: all primes in [p1, p3] cannot be the same mod 4.
    -- The consecutive pair that changes residue is mixed; we identify it as (prev,p3) OR we
    -- argue prev must be ≢ 3 because... no that's false (e.g. 13,17,19: 13≡1, 17≡1, 19≡3, prev of 19 is 17≡1. Good.
    -- e.g. 17,19: prev of 19 is 17≡1. 
    -- e.g. 19,23 both 3. If p1=13, p3=19, prev of 19 is 17≡1. 
    -- e.g. p1=17≡1, p3=19≡3, prev=17≡1.
    -- Is prev of the FIRST prime ≡3 after a prime ≡1 always ≡1? YES!
    -- Because if prev ≡3, then prev is an earlier prime ≡3, so p3 is not the first ≡3 after p1
    -- unless prev < p1. But prev ≥ p1. If prev ≡3 and prev ≥ p1 and prev < p3, then prev is a
    -- prime ≡3 after p1 (or equal to p1 but p1≡1), so prev > p1, contradicting that p3 is the
    -- LEAST prime ≡3 that is > p1.
    -- We defined p3 as SOME prime ≡3 > p1, not the least! That's the bug.
    -- Fix: we don't need p3 to be least. We use: prev ≡ 1 or we pick the least ≡3.
    -- I'll prove prev % 4 ≠ 3 ∨ wait.
    -- Easiest fix: p3 is some prime ≡ 3 > p1. Let r be the least prime > p1 that is ≡ 3 [MOD 4].
    -- Then prev(r) is not ≡ 3 (else smaller), and prev(r) ≥ p1 ≡ 1, and prev(r) is odd prime > 2,
    -- so prev(r) ≡ 1 [MOD 4]. Then mixed.
    -- We have existence of some p3, so the set {p | p.Prime ∧ p ≡ 3 [MOD 4] ∧ p1 < p} is nonempty,
    -- so it has a minimum.
    sorry


