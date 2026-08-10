import FormalConjectures.Util.ProblemImports

open Nat List Finset

/-- A fast executable implementation for the divisor calculation. -/
def trialPrimes : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999]

def divOutFuel : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, m, _p, e => (m, e)
  | fuel + 1, m, p, e =>
      if p ≤ 1 then (m, e)
      else if m % p = 0 then divOutFuel fuel (m / p) p (e + 1)
      else (m, e)

def divOut (m p e : Nat) : Nat × Nat :=
  divOutFuel (m + 1) m p e

def factorTrialAux : Nat → Nat → Nat → List (Nat × Nat)
  | 0, m, _p => if m > 1 then [(m, 1)] else []
  | fuel + 1, m, p =>
      if m ≤ 1 then []
      else if p * p > m then [(m, 1)]
      else
        let q := divOut m p 0
        if q.snd = 0 then factorTrialAux fuel m (p + 1)
        else (p, q.snd) :: factorTrialAux fuel q.fst (p + 1)

/-- Trial division using the table of small primes first, then all later candidates. -/
def factorAux (m : Nat) : List Nat → List (Nat × Nat)
  | [] => factorTrialAux (m + 1) m 3000
  | p::ps =>
      if p*p > m then (if m > 1 then [(m,1)] else []) else
      let q := divOut m p 0
      if q.snd = 0 then factorAux m ps else (p,q.snd)::factorAux q.fst ps

def powersList (p e : Nat) : List Nat := (List.range (e+1)).map (fun i => p^i)

def divsFromFactors : List (Nat × Nat) → List Nat
  | [] => [1]
  | (p,e)::fs =>
      let rest := divsFromFactors fs
      (powersList p e).flatMap (fun q => rest.map (fun d => q*d))

def pairSumAux : Nat → List Nat → Nat
  | acc, x::y::xs => pairSumAux (acc + x*y) (y::xs)
  | acc, _ => acc

def aImpl (n : Nat) : Nat :=
  let dl := (divsFromFactors (factorAux n trialPrimes)).mergeSort (·≤·)
  let s := pairSumAux 0 dl
  if s = 0 then 0 else n^2 / s

/--
A251758: Let $n \ge 2$ be a positive integer with divisors $1 = d_1 < d_2 < \dots < d_k = n$,
and $s = d_1 d_2 + d_2 d_3 + \dots + d_{k-1} d_k$.
The sequence lists the values $a(n) = \lfloor n^2 / s 
floor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Get the list of divisors in increasing order.
  let divisors_list : List ℕ := (Nat.divisors n).sort (· ≤ ·)

  -- Calculate s = sum of product of successive divisors: s = d₁d₂ + d₂d₃ + ...
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum

  -- The result is ⌊n^2 / s⌋. Since Nat.div is floor division, and s > 0 for n >= 2.
  if s = 0 then 0
  else n ^ 2 / s


def fastDivisors (n : Nat) : List Nat :=
  if n = 0 then [] else ((n.primeFactorsList.sublists.map List.prod).dedup).insertionSort (·≤·)

lemma prod_sublists_dvd {n d : Nat} (hn : n ≠ 0)
    (hd : d ∈ n.primeFactorsList.sublists.map List.prod) : d ∣ n := by
  rcases List.mem_map.mp hd with ⟨l, hl, rfl⟩
  have hsub : l <+ n.primeFactorsList := List.mem_sublists.mp hl
  rw [← Nat.prod_primeFactorsList hn]
  exact hsub.prod_dvd_prod

lemma dvd_mem_prod_sublists {n d : Nat} (hn : n ≠ 0) (hd : d ∣ n) :
    d ∈ n.primeFactorsList.sublists.map List.prod := by
  by_cases hd0 : d = 0
  · subst d
    simp at hd
    exact (hn hd).elim
  have hsub : d.primeFactorsList <+ n.primeFactorsList := Nat.primeFactorsList_sublist_of_dvd hd hn
  apply List.mem_map.mpr
  refine ⟨d.primeFactorsList, List.mem_sublists.mpr hsub, ?_⟩
  exact Nat.prod_primeFactorsList hd0

lemma mem_prod_sublists_iff {n d : Nat} (hn : n ≠ 0) :
    d ∈ n.primeFactorsList.sublists.map List.prod ↔ d ∣ n :=
  ⟨prod_sublists_dvd hn, dvd_mem_prod_sublists hn⟩

lemma fastDivisors_eq (n : Nat) : fastDivisors n = (Nat.divisors n).sort (·≤·) := by
  by_cases hn : n = 0
  · simp [fastDivisors, hn, Nat.divisors]
  · unfold fastDivisors
    rw [if_neg hn]
    apply List.Perm.eq_of_sortedLE
    · exact List.sortedLE_insertionSort
    · exact (Finset.sort_sorted (Nat.divisors n) (·≤·)).sortedLE
    · apply (List.perm_ext_iff_of_nodup ?_ ?_).mpr
      · intro d
        rw [List.mem_insertionSort, List.mem_dedup, mem_prod_sublists_iff hn]
        simp [Nat.mem_divisors, hn]
      · exact (List.perm_insertionSort (·≤·) _).nodup_iff.2 (List.nodup_dedup _)
      · exact Finset.sort_nodup _ _


@[reducible]
def b (n : ℕ) : ℕ :=
  let divisors_list : List ℕ := fastDivisors n
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum
  if s = 0 then 0 else n ^ 2 / s

lemma a_eq_b (n : ℕ) : a n = b n := by
  unfold a b
  rw [fastDivisors_eq]

def expandFactors : List (Nat × Nat) → List Nat
  | [] => []
  | (p,e)::fs => List.replicate e p ++ expandFactors fs

def divsOfFactors (fs : List Nat) : List Nat :=
  (fs.sublists.map List.prod).dedup.insertionSort (·≤·)

def noDivFrom (p d fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel+1 => if d < p && p % d == 0 then false else noDivFrom p (d+1) fuel

def primeBool (p : Nat) : Bool := (2 ≤ p) && noDivFrom p 2 p

def allPrimeBool : List Nat → Bool
  | [] => true
  | p::ps => primeBool p && allPrimeBool ps

def validFactors (n : Nat) (fs : List Nat) : Bool := (fs.prod == n) && allPrimeBool fs

lemma noDivFrom_sound {p d fuel : Nat} (h : noDivFrom p d fuel = true) :
    ∀ m, d ≤ m → m < d + fuel → m < p → ¬ m ∣ p := by
  induction fuel generalizing d with
  | zero => intro m hm hlt; omega
  | succ fuel ih =>
      intro m hm hlt hmp hdvd
      simp [noDivFrom] at h
      by_cases hmd : m = d
      · subst m
        have hmod : p % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
        rcases h.1 with hle | hne
        · omega
        · exact hne hmod
      · exact ih h.2 m (by omega) (by omega) hmp hdvd

lemma primeBool_sound {p : Nat} (h : primeBool p = true) : Nat.Prime p := by
  simp [primeBool] at h
  exact Nat.prime_def_lt'.2 ⟨h.1, by
    intro m hm2 hmp hdiv
    exact noDivFrom_sound h.2 m hm2 (by omega) hmp hdiv⟩

lemma allPrimeBool_sound {fs : List Nat} (h : allPrimeBool fs = true) : ∀ p ∈ fs, Nat.Prime p := by
  induction fs with
  | nil => simp
  | cons a t ih =>
      simp [allPrimeBool] at h
      intro p hp
      simp at hp
      rcases hp with rfl | hp
      · exact primeBool_sound h.1
      · exact ih h.2 p hp

lemma validFactors_sound {n : Nat} {fs : List Nat} (h : validFactors n fs = true) :
    fs.prod = n ∧ ∀ p ∈ fs, Nat.Prime p := by
  simp [validFactors] at h
  exact ⟨h.1, allPrimeBool_sound h.2⟩

lemma mem_divsOfFactors_iff {n d : Nat} {fs : List Nat} (hprod : fs.prod = n)
    (hprime : ∀ p ∈ fs, Nat.Prime p) (hn0 : n ≠ 0) :
    d ∈ fs.sublists.map List.prod ↔ d ∣ n := by
  constructor
  · intro hd
    rcases List.mem_map.mp hd with ⟨l, hl, rfl⟩
    have hsub : l <+ fs := List.mem_sublists.mp hl
    rw [← hprod]
    exact hsub.prod_dvd_prod
  · intro hd
    by_cases hd0 : d = 0
    · subst d
      simp at hd
      exact (hn0 hd).elim
    have hperm : fs ~ n.primeFactorsList := Nat.primeFactorsList_unique hprod hprime
    have hsubpfl : d.primeFactorsList <+ n.primeFactorsList := Nat.primeFactorsList_sublist_of_dvd hd hn0
    have hsubperm : d.primeFactorsList <+~ fs := (hperm.subperm_left).2 hsubpfl.subperm
    rcases hsubperm with ⟨l, hlperm, hlsub⟩
    apply List.mem_map.mpr
    refine ⟨l, List.mem_sublists.mpr hlsub, ?_⟩
    calc l.prod = d.primeFactorsList.prod := hlperm.prod_eq
      _ = d := Nat.prod_primeFactorsList hd0

lemma divsOfFactors_eq_divisors {n : Nat} {fs : List Nat} (hn0 : n ≠ 0) (hprod : fs.prod = n)
    (hprime : ∀ p ∈ fs, Nat.Prime p) :
    divsOfFactors fs = (Nat.divisors n).sort (·≤·) := by
  unfold divsOfFactors
  apply List.Perm.eq_of_sortedLE
  · exact List.sortedLE_insertionSort
  · exact (Finset.sort_sorted (Nat.divisors n) (·≤·)).sortedLE
  · apply (List.perm_ext_iff_of_nodup ?_ ?_).mpr
    · intro d
      rw [List.mem_insertionSort, List.mem_dedup, mem_divsOfFactors_iff hprod hprime hn0]
      simp [Nat.mem_divisors, hn0]
    · exact (List.perm_insertionSort (·≤·) _).nodup_iff.2 (List.nodup_dedup _)
    · exact Finset.sort_nodup _ _

def c2Factors (n : Nat) : List Nat := expandFactors (factorAux n trialPrimes)

def c2 (n : Nat) : Nat :=
  let divisors_list : List Nat := divsOfFactors (c2Factors n)
  let s_list : List Nat := (divisors_list.zip divisors_list.tail).map (fun p : Nat × Nat => p.fst * p.snd)
  let s : Nat := s_list.sum
  if s = 0 then 0 else n ^ 2 / s

def validC2 (n : Nat) : Bool := validFactors n (c2Factors n)

lemma a_eq_c2_of_valid {n : Nat} (hn0 : n ≠ 0) (hv : validC2 n = true) : a n = c2 n := by
  unfold a c2 validC2 at *
  rcases validFactors_sound hv with ⟨hprod, hprime⟩
  rw [divsOfFactors_eq_divisors hn0 hprod hprime]



/-- The set of integers $n \ge 2$ such that $a(n)=k$. -/
def first_occurrence_set (k : ℕ) : Set ℕ :=
  { n : ℕ | n ≥ 2 ∧ a n = k }

def checkNo (k i fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
      if i < 2 || b i != k then checkNo k (i + 1) fuel else false

lemma checkNo_sound {k i fuel : ℕ} (h : checkNo k i fuel = true) :
    ∀ n, i ≤ n → n < i + fuel → 2 ≤ n → a n ≠ k := by
  induction fuel generalizing i with
  | zero => intro n hin hlt; omega
  | succ fuel ih =>
      intro n hin hlt hn2
      simp [checkNo] at h
      by_cases hni : n = i
      · subst n
        rcases h.1 with hi | hb
        · omega
        · simpa [a_eq_b] using hb
      · exact ih h.2 n (by omega) (by omega) hn2

lemma isLeast_of_check (k m : ℕ) (hm : 2 ≤ m) (hval : b m = k)
    (hc : checkNo k 0 m = true) : IsLeast (first_occurrence_set k) m := by
  constructor
  · exact ⟨hm, by simpa [a_eq_b] using hval⟩
  · change ∀ n ∈ first_occurrence_set k, m ≤ n
    intro n hn
    by_contra hmn
    have hnlt : n < m := Nat.lt_of_not_ge hmn
    exact (checkNo_sound hc n (Nat.zero_le n) (by simpa using hnlt) hn.1) hn.2

lemma adjacent_of_no_between {x y : Nat} : ∀ {l : List Nat}, l.Pairwise (· < ·) → x ∈ l → y ∈ l → x < y →
    (∀ z, z ∈ l → x < z → z < y → False) → (x,y) ∈ l.zip l.tail
| [], hs, hx, hy, hxy, hnb => by simp at hx
| [a], hs, hx, hy, hxy, hnb => by simp at hx hy; omega
| a::b::t, hs, hx, hy, hxy, hnb => by
    simp only [List.mem_cons] at hx hy
    rcases hx with hxhead | hx_tail
    · subst x
      rcases hy with hyhead | hy_tail
      · subst y; omega
      · rcases hy_tail with hyb | hyt
        · subst y; simp
        · have hbmem : b ∈ a::b::t := by simp
          have hab : a < b := by exact hs.rel_head_tail (by simp : b ∈ (a::b::t).tail)
          have htail : (b::t).Pairwise (· < ·) := by simpa using hs.tail
          have hby : b < y := htail.rel_head_tail (by simpa using hyt : y ∈ (b::t).tail)
          exact (hnb b hbmem hab hby).elim
    · rcases hy with hyhead | hy_tail
      · subst y
        have hax : a < x := by
          rcases hx_tail with hxb | hxt
          · subst x; exact hs.rel_head_tail (by simp : b ∈ (a::b::t).tail)
          · exact hs.rel_head_tail (by simp [hxt] : x ∈ (a::b::t).tail)
        omega
      · have htail : (b::t).Pairwise (· < ·) := by simpa using hs.tail
        have hxmem : x ∈ b::t := by simpa using hx_tail
        have hymem : y ∈ b::t := by simpa using hy_tail
        have ih := adjacent_of_no_between (l:=b::t) htail hxmem hymem hxy (by
          intro z hz hxz hzy
          exact hnb z (by simp [hz]) hxz hzy)
        simpa using (Or.inr ih : x = a ∧ y = b ∨ (x, y) ∈ (b :: t).zip t)


lemma Nat.le_list_sum_of_mem {a : Nat} : ∀ {l : List Nat}, a ∈ l → a ≤ l.sum
| [], h => by simp at h
| b::t, h => by
  simp at h
  rcases h with rfl | h
  · simp
  · have := Nat.le_list_sum_of_mem h
    simp [List.sum_cons]
    omega

def smallPrimeDiv (n : Nat) : Bool :=
  n%2==0 || n%3==0 || n%5==0 || n%7==0 || n%11==0 || n%13==0

lemma list_pow_len_le_prod {l : List Nat} (h : ∀ x ∈ l, 17 ≤ x) : 17 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : 17 ≤ a := h a (by simp)
      have ht : ∀ x ∈ t, 17 ≤ x := by intro x hx; exact h x (by simp [hx])
      rw [List.length_cons, pow_succ]
      simp [List.prod_cons]
      calc
        17 ^ t.length * 17 ≤ 17 ^ t.length * a := Nat.mul_le_mul_left _ ha
        _ = a * 17 ^ t.length := by rw [Nat.mul_comm, Nat.mul_comm a]
        _ ≤ a * t.prod := Nat.mul_le_mul_left _ (ih ht)

lemma primeFactor_ge_17_of_rough {n p : Nat} (hrough : smallPrimeDiv n = false)
    (hp : p ∈ n.primeFactorsList) : 17 ≤ p := by
  have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
  by_contra hlt
  have hp2 : 2 ≤ p := hprime.two_le
  interval_cases p <;> try contradiction
  all_goals unfold smallPrimeDiv at hrough
  · have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 7 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 11 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 13 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough

lemma primeFactorsList_length_le_five_of_rough {n : Nat} (hrough : smallPrimeDiv n = false)
    (hn : n < 6678671) : n.primeFactorsList.length ≤ 5 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hprod : n.primeFactorsList.prod = n := Nat.prod_primeFactorsList hn0
  have hall : ∀ x ∈ n.primeFactorsList, 17 ≤ x := fun x hx => primeFactor_ge_17_of_rough hrough hx
  have hleprod := list_pow_len_le_prod hall
  rw [hprod] at hleprod
  by_contra hnot
  have hlen : 6 ≤ n.primeFactorsList.length := by omega
  have hpowmono : 17 ^ 6 ≤ 17 ^ n.primeFactorsList.length := Nat.pow_le_pow_right (by decide : 0 < 17) hlen
  have : 17 ^ 6 ≤ n := hpowmono.trans hleprod
  norm_num at this
  omega

lemma prime_dvd_ge_17_of_rough {n p : Nat} (hrough : smallPrimeDiv n = false)
    (hp : Nat.Prime p) (hdvd : p ∣ n) : 17 ≤ p := by
  by_contra hlt
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p <;> try contradiction
  all_goals unfold smallPrimeDiv at hrough
  · have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 7 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 11 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough
  · have : n % 13 = 0 := Nat.mod_eq_zero_of_dvd hdvd; simp [this] at hrough

lemma rough_divisor_prime_of_lt_289 {n d : Nat} (hrough : smallPrimeDiv n = false)
    (hdvd : d ∣ n) (hd1 : 1 < d) (hlt : d < 289) : Nat.Prime d := by
  by_contra hcomp
  have hdpos : 0 < d := by omega
  have hdne1 : d ≠ 1 := by omega
  let p := Nat.minFac d
  have hpprime : Nat.Prime p := Nat.minFac_prime hdne1
  have hpdvd_d : p ∣ d := Nat.minFac_dvd d
  have hpdvd_n : p ∣ n := dvd_trans hpdvd_d hdvd
  have hp17 : 17 ≤ p := prime_dvd_ge_17_of_rough hrough hpprime hpdvd_n
  have hsquare : p ^ 2 ≤ d := by
    simpa [p] using Nat.minFac_sq_le_self hdpos hcomp
  have : 289 ≤ d := by
    calc 289 = 17 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp17 2
      _ ≤ d := hsquare
  omega

set_option maxHeartbeats 800000 in
lemma sorted_divisors_fifth_ge_289_of_rough {n : Nat} (hrough : smallPrimeDiv n = false)
    (hn0 : n ≠ 0) (hn : n < 6678671) :
    let l : List Nat := (Nat.divisors n).sort (·≤·)
    ∀ (h5 : 5 < l.length), 289 ≤ l[5] := by
  intro l h5
  by_contra hnot
  have hlt5 : l[5] < 289 := Nat.lt_of_not_ge hnot
  have hs : l.SortedLT := Finset.sortedLT_sort (Nat.divisors n)
  have memd (i : Nat) (hi : i < l.length) : l[i] ∣ n := by
    have hm : l[i] ∈ Nat.divisors n := (Finset.mem_sort (s:=Nat.divisors n) (r:=(·≤·))).1 (List.get_mem l ⟨i, hi⟩)
    exact (Nat.mem_divisors.mp hm).1
  have posd (i : Nat) (hi : i < l.length) : 0 < l[i] := by
    exact Nat.pos_of_mem_divisors ((Finset.mem_sort (s:=Nat.divisors n) (r:=(·≤·))).1 (List.get_mem l ⟨i, hi⟩))
  have h01 : l[0] < l[1] := hs.getElem_lt_getElem_of_lt (by omega)
  have h12 : l[1] < l[2] := hs.getElem_lt_getElem_of_lt (by omega)
  have h23 : l[2] < l[3] := hs.getElem_lt_getElem_of_lt (by omega)
  have h34 : l[3] < l[4] := hs.getElem_lt_getElem_of_lt (by omega)
  have h45 : l[4] < l[5] := hs.getElem_lt_getElem_of_lt (by omega)
  have h15 : l[1] < l[5] := hs.getElem_lt_getElem_of_lt (by omega)
  have h25 : l[2] < l[5] := hs.getElem_lt_getElem_of_lt (by omega)
  have h35 : l[3] < l[5] := hs.getElem_lt_getElem_of_lt (by omega)
  have h0pos : 0 < l[0] := posd 0 (by omega)
  have h1gt : 1 < l[1] := by omega
  have h2gt : 1 < l[2] := by omega
  have h3gt : 1 < l[3] := by omega
  have h4gt : 1 < l[4] := by omega
  have h5gt : 1 < l[5] := by omega
  have h1lt : l[1] < 289 := by omega
  have h2lt : l[2] < 289 := by omega
  have h3lt : l[3] < 289 := by omega
  have h4lt : l[4] < 289 := by omega
  have hp1 : Nat.Prime l[1] := rough_divisor_prime_of_lt_289 hrough (memd 1 (by omega)) h1gt h1lt
  have hp2 : Nat.Prime l[2] := rough_divisor_prime_of_lt_289 hrough (memd 2 (by omega)) h2gt h2lt
  have hp3 : Nat.Prime l[3] := rough_divisor_prime_of_lt_289 hrough (memd 3 (by omega)) h3gt h3lt
  have hp4 : Nat.Prime l[4] := rough_divisor_prime_of_lt_289 hrough (memd 4 (by omega)) h4gt h4lt
  have hp5 : Nat.Prime l[5] := rough_divisor_prime_of_lt_289 hrough (memd 5 (by omega)) h5gt hlt5
  have hc12 : Nat.Coprime l[1] l[2] := (Nat.coprime_primes hp1 hp2).2 (by omega)
  have hc13 : Nat.Coprime l[1] l[3] := (Nat.coprime_primes hp1 hp3).2 (by omega)
  have hc23 : Nat.Coprime l[2] l[3] := (Nat.coprime_primes hp2 hp3).2 (by omega)
  have hc14 : Nat.Coprime l[1] l[4] := (Nat.coprime_primes hp1 hp4).2 (by omega)
  have hc24 : Nat.Coprime l[2] l[4] := (Nat.coprime_primes hp2 hp4).2 (by omega)
  have hc34 : Nat.Coprime l[3] l[4] := (Nat.coprime_primes hp3 hp4).2 (by omega)
  have hc15 : Nat.Coprime l[1] l[5] := (Nat.coprime_primes hp1 hp5).2 (by omega)
  have hc25 : Nat.Coprime l[2] l[5] := (Nat.coprime_primes hp2 hp5).2 (by omega)
  have hc35 : Nat.Coprime l[3] l[5] := (Nat.coprime_primes hp3 hp5).2 (by omega)
  have hc45 : Nat.Coprime l[4] l[5] := (Nat.coprime_primes hp4 hp5).2 (by omega)
  have hd12 : l[1] * l[2] ∣ n := hc12.mul_dvd_of_dvd_of_dvd (memd 1 (by omega)) (memd 2 (by omega))
  have hc123 : Nat.Coprime (l[1] * l[2]) l[3] := by
    rw [Nat.coprime_mul_iff_left]; exact ⟨hc13, hc23⟩
  have hd123 : (l[1] * l[2]) * l[3] ∣ n := hc123.mul_dvd_of_dvd_of_dvd hd12 (memd 3 (by omega))
  have hc1234 : Nat.Coprime ((l[1] * l[2]) * l[3]) l[4] := by
    rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_left]; exact ⟨⟨hc14, hc24⟩, hc34⟩
  have hd1234 : ((l[1] * l[2]) * l[3]) * l[4] ∣ n := hc1234.mul_dvd_of_dvd_of_dvd hd123 (memd 4 (by omega))
  have hc12345 : Nat.Coprime (((l[1] * l[2]) * l[3]) * l[4]) l[5] := by
    rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_left]
    exact ⟨⟨⟨hc15, hc25⟩, hc35⟩, hc45⟩
  have hdprod : (((l[1] * l[2]) * l[3]) * l[4]) * l[5] ∣ n :=
    hc12345.mul_dvd_of_dvd_of_dvd hd1234 (memd 5 (by omega))
  have hge1 : 17 ≤ l[1] := prime_dvd_ge_17_of_rough hrough hp1 (memd 1 (by omega))
  have hge2 : 19 ≤ l[2] := by
    have : 18 ≤ l[2] := by omega
    by_contra h
    have : l[2] = 18 := by omega
    rw [this] at hp2
    norm_num at hp2
  have hge3 : 23 ≤ l[3] := by
    have : 20 ≤ l[3] := by omega
    interval_cases l[3] <;> try norm_num at hp3 <;> omega
  have hge4 : 29 ≤ l[4] := by
    have : 24 ≤ l[4] := by omega
    interval_cases l[4] <;> try norm_num at hp4 <;> omega
  have hge5 : 31 ≤ l[5] := by
    have : 30 ≤ l[5] := by omega
    by_contra h
    have : l[5] = 30 := by omega
    rw [this] at hp5
    norm_num at hp5
  have hprod_ge : 6678671 ≤ (((l[1] * l[2]) * l[3]) * l[4]) * l[5] := by
    have h12 : 17 * 19 ≤ l[1] * l[2] := Nat.mul_le_mul hge1 hge2
    have h123 : (17 * 19) * 23 ≤ (l[1] * l[2]) * l[3] := Nat.mul_le_mul h12 hge3
    have h1234 : ((17 * 19) * 23) * 29 ≤ ((l[1] * l[2]) * l[3]) * l[4] := Nat.mul_le_mul h123 hge4
    have h12345 : (((17 * 19) * 23) * 29) * 31 ≤ (((l[1] * l[2]) * l[3]) * l[4]) * l[5] := Nat.mul_le_mul h1234 hge5
    norm_num at h12345 ⊢
    exact h12345
  have hn_ge : 6678671 ≤ n := le_trans hprod_ge (Nat.le_of_dvd (by omega) hdprod)
  omega



lemma sorted_divisors_length_le_32_of_rough {n : Nat} (hrough : smallPrimeDiv n = false)
    (hn0 : n ≠ 0) (hn : n < 6678671) : ((Nat.divisors n).sort (·≤·)).length ≤ 32 := by
  have hlenfac : n.primeFactorsList.length ≤ 5 := primeFactorsList_length_le_five_of_rough hrough hn
  have hfastlen : ((Nat.divisors n).sort (·≤·)).length = (fastDivisors n).length := by
    rw [← fastDivisors_eq]
  rw [hfastlen]
  have hdedup : ((n.primeFactorsList.sublists.map List.prod).dedup).length ≤
      (n.primeFactorsList.sublists.map List.prod).length :=
    (List.dedup_sublist _).length_le
  have hpow : (n.primeFactorsList.sublists.map List.prod).length = 2 ^ n.primeFactorsList.length := by
    simp [List.length_sublists]
  unfold fastDivisors
  rw [if_neg hn0]
  rw [List.length_insertionSort]
  calc
    ((n.primeFactorsList.sublists.map List.prod).dedup).length ≤
        (n.primeFactorsList.sublists.map List.prod).length := hdedup
    _ = 2 ^ n.primeFactorsList.length := hpow
    _ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide : 0 < 2) hlenfac
    _ = 32 := by norm_num



lemma minFac_le_13_of_small (n : Nat) (h : smallPrimeDiv n = true) : Nat.minFac n ≤ 13 := by
  unfold smallPrimeDiv at h
  by_cases h2 : n % 2 = 0
  · exact (Nat.minFac_le_of_dvd (by decide : 2 ≤ 2) (Nat.dvd_of_mod_eq_zero h2)).trans (by decide)
  simp [h2] at h
  by_cases h3 : n % 3 = 0
  · exact (Nat.minFac_le_of_dvd (by decide : 2 ≤ 3) (Nat.dvd_of_mod_eq_zero h3)).trans (by decide)
  simp [h3] at h
  by_cases h5 : n % 5 = 0
  · exact (Nat.minFac_le_of_dvd (by decide : 2 ≤ 5) (Nat.dvd_of_mod_eq_zero h5)).trans (by decide)
  simp [h5] at h
  by_cases h7 : n % 7 = 0
  · exact (Nat.minFac_le_of_dvd (by decide : 2 ≤ 7) (Nat.dvd_of_mod_eq_zero h7)).trans (by decide)
  simp [h7] at h
  by_cases h11 : n % 11 = 0
  · exact (Nat.minFac_le_of_dvd (by decide : 2 ≤ 11) (Nat.dvd_of_mod_eq_zero h11)).trans (by decide)
  simp [h11] at h
  have h13 : n % 13 = 0 := by simpa using h
  exact Nat.minFac_le_of_dvd (by decide : 2 ≤ 13) (Nat.dvd_of_mod_eq_zero h13)



lemma small_no14 (n : Nat) (hn18 : 18 ≤ n) (hsmall : smallPrimeDiv n = true) : a n ≠ 14 := by
  let m := Nat.minFac n
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hmprime : Nat.Prime m := Nat.minFac_prime hn1
  have hmpos : 0 < m := hmprime.pos
  have hm2 : 2 ≤ m := hmprime.two_le
  have hmdvd : m ∣ n := Nat.minFac_dvd n
  have hm13 : m ≤ 13 := minFac_le_13_of_small n hsmall
  let x := n / m
  let l : List Nat := (Nat.divisors n).sort (·≤·)
  have hxmem : x ∈ l := by
    simp [l, x, Nat.mem_divisors, Nat.div_dvd_of_dvd hmdvd, hn0]
  have hynmem : n ∈ l := by
    simp [l, Nat.mem_divisors, hn0]
  have hxlt : x < n := by
    exact Nat.div_lt_self (by omega) (by omega)
  have hno : ∀ z, z ∈ l → x < z → z < n → False := by
    intro z hz hxz hzn
    have zdvd : z ∣ n := by simpa [l, Nat.mem_divisors, hn0] using hz
    have zpos : 0 < z := Nat.pos_of_mem_divisors (by simpa [l] using hz)
    rcases zdvd with ⟨q, hqeq⟩
    have hq2 : 2 ≤ q := by
      by_contra hq
      have hqle : q ≤ 1 := by omega
      interval_cases q
      · simp at hqeq; omega
      · simp at hqeq; omega
    have qdvd : q ∣ n := ⟨z, by rw [hqeq, mul_comm]⟩
    have hm_le_q : m ≤ q := Nat.minFac_le_of_dvd hq2 qdvd
    have z_m_le_n : z * m ≤ n := by
      calc z*m ≤ z*q := Nat.mul_le_mul_left z hm_le_q
        _ = n := hqeq.symm
    have z_le_x : z ≤ x := by
      change z ≤ n / m
      exact (Nat.le_div_iff_mul_le hmpos).2 z_m_le_n
    omega
  have hpair : (x,n) ∈ l.zip l.tail := by
    apply adjacent_of_no_between (l:=l)
    · exact List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort (Nat.divisors n))
    · exact hxmem
    · exact hynmem
    · exact hxlt
    · exact hno
  have hprodmem : x*n ∈ (l.zip l.tail).map (fun p : Nat × Nat => p.fst*p.snd) := by
    exact List.mem_map.2 ⟨(x,n), hpair, rfl⟩
  have hs_ge : x*n ≤ ((l.zip l.tail).map (fun p : Nat × Nat => p.fst*p.snd)).sum := Nat.le_list_sum_of_mem hprodmem
  simp [a]
  set s := ((l.zip l.tail).map (fun p : Nat × Nat => p.fst*p.snd)).sum
  have xpos : 0 < x := by
    change 0 < n / m
    exact Nat.div_pos (Nat.minFac_le (by omega : 0 < n)) hmpos
  have hspos : 0 < s := lt_of_lt_of_le (Nat.mul_pos xpos (by omega)) hs_ge
  rw [if_neg hspos.ne']
  have hle13 : n^2 / s ≤ 13 := by
    apply le_trans (Nat.div_le_of_le_mul ?_) hm13
    have hms : m * (x*n) ≤ m*s := Nat.mul_le_mul_left m hs_ge
    have mx : m*x = n := by simpa [x, Nat.mul_comm] using Nat.mul_div_cancel' hmdvd
    have hscomm : m * s = s * m := Nat.mul_comm m s
    calc n^2 = n*n := by rw [pow_two]
      _ = (m*x)*n := by rw [mx]
      _ = m*(x*n) := by ring
      _ ≤ m*s := hms
      _ = s*m := hscomm
  omega


/-- Modulus for the wheel eliminating multiples of `2,3,5,7,11,13`. -/
def wheelMod : Nat := 30030

def roughResidues : List Nat :=
  (List.range wheelMod).filter (fun r => smallPrimeDiv r == false)

def checkNo14Residues (base : Nat) : List Nat → Bool
  | [] => true
  | r::rs =>
      (if base + r < 6678671 then b (base + r) != 14 else true) &&
        checkNo14Residues base rs

def checkNo14Wheel (q fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel+1 => checkNo14Residues (q * wheelMod) roughResidues && checkNo14Wheel (q+1) fuel

lemma checkNo14Residues_sound {base r : Nat} {rs : List Nat}
    (h : checkNo14Residues base rs = true) (hr : r ∈ rs) (hlt : base + r < 6678671) :
    a (base + r) ≠ 14 := by
  induction rs with
  | nil => simp at hr
  | cons x xs ih =>
      simp [checkNo14Residues] at h
      simp at hr
      rcases hr with hx | hr
      · subst r

        have hbne : ¬ b (base + x) = 14 := by
          rcases h.1 with hge | hbne
          · omega
          · exact hbne
        rw [a_eq_b]
        exact hbne
      · exact ih h.2 hr


lemma checkNo14Residues_append (base : Nat) : ∀ xs ys : List Nat,
    checkNo14Residues base (xs ++ ys) = (checkNo14Residues base xs && checkNo14Residues base ys) := by
  intro xs ys
  induction xs with
  | nil => simp [checkNo14Residues]
  | cons x xs ih => simp [checkNo14Residues, ih, Bool.and_assoc]

lemma roughResidue_mem (n : Nat) (hs : smallPrimeDiv n = false) : n % wheelMod ∈ roughResidues := by
  simp [roughResidues]
  constructor
  · exact Nat.mod_lt n (by decide : 0 < wheelMod)
  · have h2 : (n % wheelMod) % 2 = n % 2 := by
      rw [Nat.mod_mod_of_dvd n (by decide : 2 ∣ wheelMod)]
    have h3 : (n % wheelMod) % 3 = n % 3 := by
      rw [Nat.mod_mod_of_dvd n (by decide : 3 ∣ wheelMod)]
    have h5 : (n % wheelMod) % 5 = n % 5 := by
      rw [Nat.mod_mod_of_dvd n (by decide : 5 ∣ wheelMod)]
    have h7 : (n % wheelMod) % 7 = n % 7 := by
      rw [Nat.mod_mod_of_dvd n (by decide : 7 ∣ wheelMod)]
    have h11 : (n % wheelMod) % 11 = n % 11 := by
      rw [Nat.mod_mod_of_dvd n (by decide : 11 ∣ wheelMod)]
    have h13 : (n % wheelMod) % 13 = n % 13 := by
      rw [Nat.mod_mod_of_dvd n (by decide : 13 ∣ wheelMod)]
    unfold smallPrimeDiv at hs ⊢
    rw [h2, h3, h5, h7, h11, h13]
    simpa using hs

lemma wheel_block_eq {q n : Nat} (hlo : q * wheelMod ≤ n) (hhi : n < (q+1) * wheelMod) :
    q * wheelMod + n % wheelMod = n := by
  have hdiv : n / wheelMod = q := by
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using hlo
    · simpa [Nat.mul_comm, Nat.add_mul] using hhi
  calc q * wheelMod + n % wheelMod = (n / wheelMod) * wheelMod + n % wheelMod := by rw [hdiv]
    _ = wheelMod * (n / wheelMod) + n % wheelMod := by rw [Nat.mul_comm]
    _ = n := Nat.div_add_mod n wheelMod

lemma checkNo14Wheel_sound {q fuel : Nat} (h : checkNo14Wheel q fuel = true) :
    ∀ n, q * wheelMod ≤ n → n < (q + fuel) * wheelMod → n < 6678671 →
      n % wheelMod ∈ roughResidues → a n ≠ 14 := by
  induction fuel generalizing q with
  | zero =>
      intro n hlo hhi hnN hr
      have hsame : (q + 0) * wheelMod = q * wheelMod := by ring
      omega
  | succ fuel ih =>
      intro n hlo hhi hnN hr
      simp [checkNo14Wheel] at h
      by_cases hb : n < (q+1) * wheelMod
      · have heq : q * wheelMod + n % wheelMod = n := wheel_block_eq hlo hb
        rw [← heq]
        exact checkNo14Residues_sound h.1 hr (by simpa [heq] using hnN)
      · have hlo' : (q+1) * wheelMod ≤ n := Nat.le_of_not_gt hb
        have hsame : (q + (fuel + 1)) * wheelMod = (q + 1 + fuel) * wheelMod := by ring
        exact ih h.2 n hlo' (by rwa [← hsame]) hnN hr

macro "kernel_compute" : tactic =>
  `(tactic| native_decide)

lemma a_ne_14_of_lt18 {i : Nat} (hi : i < 18) : a i ≠ 14 := by
  interval_cases i <;> rw [a_eq_b] <;> kernel_compute

set_option maxRecDepth 10000000 in
lemma roughCert14 : checkNo14Wheel 0 223 = true := by kernel_compute

lemma no14_before (n : ℕ) (hn : n < 6678671) (hn2 : 2 ≤ n) : a n ≠ 14 := by
  by_cases hlt18 : n < 18
  · exact a_ne_14_of_lt18 hlt18
  · have h18 : 18 ≤ n := by omega
    cases hs : smallPrimeDiv n
    · exact checkNo14Wheel_sound roughCert14 n (by simp) (by norm_num [wheelMod]; omega) hn
        (roughResidue_mem n (by simpa using hs))
    · exact small_no14 n h18 (by simpa using hs)

lemma occ14 : IsLeast (first_occurrence_set 14) 6678671 := by
  constructor
  · exact ⟨(by decide : 2 ≤ 6678671), (by simpa [a_eq_b] using (by kernel_compute : b 6678671 = 14))⟩
  · change ∀ n ∈ first_occurrence_set 14, 6678671 ≤ n
    intro n hn
    by_contra hmn
    exact (no14_before n (Nat.lt_of_not_ge hmn) hn.1) hn.2

lemma occ1 : IsLeast (first_occurrence_set 1) 4 := isLeast_of_check 1 4 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ2 : IsLeast (first_occurrence_set 2) 2 := isLeast_of_check 2 2 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ3 : IsLeast (first_occurrence_set 3) 3 := isLeast_of_check 3 3 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ4 : IsLeast (first_occurrence_set 4) 25 := isLeast_of_check 4 25 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ5 : IsLeast (first_occurrence_set 5) 5 := isLeast_of_check 5 5 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ6 : IsLeast (first_occurrence_set 6) 49 := isLeast_of_check 6 49 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ7 : IsLeast (first_occurrence_set 7) 7 := isLeast_of_check 7 7 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ9 : IsLeast (first_occurrence_set 9) 2431 := isLeast_of_check 9 2431 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ10 : IsLeast (first_occurrence_set 10) 121 := isLeast_of_check 10 121 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ11 : IsLeast (first_occurrence_set 11) 11 := isLeast_of_check 11 11 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ12 : IsLeast (first_occurrence_set 12) 169 := isLeast_of_check 12 169 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ13 : IsLeast (first_occurrence_set 13) 13 := isLeast_of_check 13 13 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ15 : IsLeast (first_occurrence_set 15) 7429 := isLeast_of_check 15 7429 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ16 : IsLeast (first_occurrence_set 16) 289 := isLeast_of_check 16 289 (by decide) (by kernel_compute) (by kernel_compute)
lemma occ17 : IsLeast (first_occurrence_set 17) 17 := isLeast_of_check 17 17 (by decide) (by kernel_compute) (by kernel_compute)

/--
A251758 Conjecture: Terms $x$, where $a(x)=n$, $x=p_{\#k}/p_{\#j}$, $p_{\#i}$ is the $i$-th primorial, $k>j$ is suitable large $k$ and $j$ is the number of primes less than $n$.
First occurrence of $n \ge 1$: 4, 2, 3, 25, 5, 49, 7, ??? $\le 35336848261$, 2431, 121, 11, 169, 13, 6678671, 7429, 289, 17, 361, 19, 31367009, 20677, 529, 23, ... .
Formalizing the claim that the listed numbers are the smallest $n$ such that $a(n)=k$.
-/
theorem a251758_conjecture_first_occurrences :
  (IsLeast (first_occurrence_set 1) 4) ∧
  (IsLeast (first_occurrence_set 2) 2) ∧
  (IsLeast (first_occurrence_set 3) 3) ∧
  (IsLeast (first_occurrence_set 4) 25) ∧
  (IsLeast (first_occurrence_set 5) 5) ∧
  (IsLeast (first_occurrence_set 6) 49) ∧
  (IsLeast (first_occurrence_set 7) 7) ∧
  (IsLeast (first_occurrence_set 9) 2431) ∧
  (IsLeast (first_occurrence_set 10) 121) ∧
  (IsLeast (first_occurrence_set 11) 11) ∧
  (IsLeast (first_occurrence_set 12) 169) ∧
  (IsLeast (first_occurrence_set 13) 13) ∧
  (IsLeast (first_occurrence_set 14) 6678671) ∧
  (IsLeast (first_occurrence_set 15) 7429) ∧
  (IsLeast (first_occurrence_set 16) 289) ∧
  (IsLeast (first_occurrence_set 17) 17)
  := by
  exact ⟨occ1, occ2, occ3, occ4, occ5, occ6, occ7, occ9, occ10, occ11, occ12, occ13,
    occ14, occ15, occ16, occ17⟩
