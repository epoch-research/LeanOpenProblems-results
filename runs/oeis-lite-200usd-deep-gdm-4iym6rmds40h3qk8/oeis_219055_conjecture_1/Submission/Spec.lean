import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 200000000
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

open Nat Finset

/--
A219055: Number of ways to write n = p+q(3-(-1)^n)/2 with p>q and p, q, p-6, q+6 all prime.
-/
def A219055 (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun q : ℕ =>
    -- c = 1 + n % 2. The condition p > q is equivalent to (c + 1) * q < n.
    ((1 + n % 2) + 1) * q < n ∧

    -- Primality conditions for q and derived terms
    q.Prime ∧
    (q + 6).Prime ∧

    -- Primality conditions for p = n - c * q and p - 6
    (n - (1 + n % 2) * q).Prime ∧        -- p must be prime
    (n - (1 + n % 2) * q - 6).Prime      -- p - 6 must be prime
  ) (Finset.range n)

-- Formal definition of Goldbach's Conjecture
def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

-- Formal definition of Lemoine's Conjecture (or Levy's Conjecture)
def lemoine_conjecture : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

-- Formalization of the conjecture that there are infinitely many cousin primes (p, p+6)
def six_prime_gap_conjecture : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ (p + 6).Prime}

/--
The core conjecture about the sequence A219055:
a(n) > 0 for all even n > 8012 and odd n > 15727.
-/
def a219055_core_conjecture : Prop :=
  ∀ n : ℕ,
    (Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)
      → A219055 n > 0

lemma exists_of_A219055_even (n : ℕ) (heven : Even n) (hpos : A219055 n > 0) :
    ∃ q < n, 2 * q < n ∧ q.Prime ∧ (q + 6).Prime ∧ (n - q).Prime ∧ (n - q - 6).Prime := by
  have h_ne : (Finset.filter (fun q : ℕ =>
    ((1 + n % 2) + 1) * q < n ∧
    q.Prime ∧
    (q + 6).Prime ∧
    (n - (1 + n % 2) * q).Prime ∧
    (n - (1 + n % 2) * q - 6).Prime
  ) (Finset.range n)).Nonempty := by
    rw [A219055] at hpos
    apply Finset.card_pos.mp
    omega
  rcases h_ne with ⟨q, hq⟩
  rw [Finset.mem_filter, Finset.mem_range] at hq
  rcases hq with ⟨hq_lt, hq_cond⟩
  have hn2 : n % 2 = 0 := Nat.even_iff.mp heven
  rw [hn2] at hq_cond
  have h_one : 1 + 0 = 1 := rfl
  have h_mul : 1 * q = q := Nat.one_mul q
  rw [h_one, h_mul] at hq_cond
  exact ⟨q, hq_lt, hq_cond.1, hq_cond.2.1, hq_cond.2.2.1, hq_cond.2.2.2.1, hq_cond.2.2.2.2⟩

lemma exists_of_A219055_odd (n : ℕ) (hodd : Odd n) (hpos : A219055 n > 0) :
    ∃ q < n, 3 * q < n ∧ q.Prime ∧ (q + 6).Prime ∧ (n - 2 * q).Prime ∧ (n - 2 * q - 6).Prime := by
  have h_ne : (Finset.filter (fun q : ℕ =>
    ((1 + n % 2) + 1) * q < n ∧
    q.Prime ∧
    (q + 6).Prime ∧
    (n - (1 + n % 2) * q).Prime ∧
    (n - (1 + n % 2) * q - 6).Prime
  ) (Finset.range n)).Nonempty := by
    rw [A219055] at hpos
    apply Finset.card_pos.mp
    omega
  rcases h_ne with ⟨q, hq⟩
  rw [Finset.mem_filter, Finset.mem_range] at hq
  rcases hq with ⟨hq_lt, hq_cond⟩
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  rw [hn2] at hq_cond
  have h_two : 1 + 1 = 2 := rfl
  rw [h_two] at hq_cond
  exact ⟨q, hq_lt, hq_cond.1, hq_cond.2.1, hq_cond.2.2.1, hq_cond.2.2.2.1, hq_cond.2.2.2.2⟩

inductive PrimeTree where
  | leaf
  | node (val : ℕ) (left right : PrimeTree)

def bst_sub_0 : PrimeTree := (PrimeTree.node 109 (PrimeTree.node 47 (PrimeTree.node 19 (PrimeTree.node 7 (PrimeTree.node 3 (PrimeTree.node 2 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13 (PrimeTree.node 11 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 17 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 37 (PrimeTree.node 29 (PrimeTree.node 23 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 31 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 43 (PrimeTree.node 41 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 79 (PrimeTree.node 67 (PrimeTree.node 59 (PrimeTree.node 53 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 61 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 73 (PrimeTree.node 71 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 101 (PrimeTree.node 89 (PrimeTree.node 83 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 97 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 107 (PrimeTree.node 103 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 193 (PrimeTree.node 157 (PrimeTree.node 137 (PrimeTree.node 127 (PrimeTree.node 113 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 131 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 149 (PrimeTree.node 139 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 151 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 179 (PrimeTree.node 167 (PrimeTree.node 163 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 173 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 191 (PrimeTree.node 181 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 233 (PrimeTree.node 223 (PrimeTree.node 199 (PrimeTree.node 197 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 211 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 229 (PrimeTree.node 227 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 257 (PrimeTree.node 241 (PrimeTree.node 239 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 251 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 269 (PrimeTree.node 263 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_1 : PrimeTree := (PrimeTree.node 449 (PrimeTree.node 367 (PrimeTree.node 317 (PrimeTree.node 293 (PrimeTree.node 281 (PrimeTree.node 277 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 283 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 311 (PrimeTree.node 307 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 313 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 349 (PrimeTree.node 337 (PrimeTree.node 331 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 347 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 359 (PrimeTree.node 353 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 409 (PrimeTree.node 389 (PrimeTree.node 379 (PrimeTree.node 373 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 383 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 401 (PrimeTree.node 397 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 433 (PrimeTree.node 421 (PrimeTree.node 419 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 431 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 443 (PrimeTree.node 439 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 547 (PrimeTree.node 491 (PrimeTree.node 467 (PrimeTree.node 461 (PrimeTree.node 457 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 463 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 487 (PrimeTree.node 479 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 521 (PrimeTree.node 503 (PrimeTree.node 499 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 509 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 541 (PrimeTree.node 523 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 593 (PrimeTree.node 571 (PrimeTree.node 563 (PrimeTree.node 557 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 569 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 587 (PrimeTree.node 577 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 613 (PrimeTree.node 601 (PrimeTree.node 599 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 607 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 619 (PrimeTree.node 617 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_2 : PrimeTree := (PrimeTree.node 827 (PrimeTree.node 733 (PrimeTree.node 677 (PrimeTree.node 653 (PrimeTree.node 643 (PrimeTree.node 641 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 647 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 661 (PrimeTree.node 659 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 673 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 709 (PrimeTree.node 691 (PrimeTree.node 683 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 701 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 727 (PrimeTree.node 719 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 773 (PrimeTree.node 757 (PrimeTree.node 743 (PrimeTree.node 739 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 751 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 769 (PrimeTree.node 761 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 811 (PrimeTree.node 797 (PrimeTree.node 787 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 809 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 823 (PrimeTree.node 821 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 937 (PrimeTree.node 881 (PrimeTree.node 857 (PrimeTree.node 839 (PrimeTree.node 829 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 853 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 863 (PrimeTree.node 859 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 877 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 911 (PrimeTree.node 887 (PrimeTree.node 883 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 907 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 929 (PrimeTree.node 919 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 983 (PrimeTree.node 967 (PrimeTree.node 947 (PrimeTree.node 941 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 953 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 977 (PrimeTree.node 971 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 1013 (PrimeTree.node 997 (PrimeTree.node 991 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1009 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1021 (PrimeTree.node 1019 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_3 : PrimeTree := (PrimeTree.node 1231 (PrimeTree.node 1123 (PrimeTree.node 1087 (PrimeTree.node 1051 (PrimeTree.node 1039 (PrimeTree.node 1033 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1049 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1063 (PrimeTree.node 1061 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1069 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 1103 (PrimeTree.node 1093 (PrimeTree.node 1091 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1097 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1117 (PrimeTree.node 1109 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 1187 (PrimeTree.node 1163 (PrimeTree.node 1151 (PrimeTree.node 1129 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1153 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1181 (PrimeTree.node 1171 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 1217 (PrimeTree.node 1201 (PrimeTree.node 1193 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1213 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1229 (PrimeTree.node 1223 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 1321 (PrimeTree.node 1289 (PrimeTree.node 1277 (PrimeTree.node 1249 (PrimeTree.node 1237 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1259 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1283 (PrimeTree.node 1279 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 1303 (PrimeTree.node 1297 (PrimeTree.node 1291 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1301 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1319 (PrimeTree.node 1307 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 1409 (PrimeTree.node 1373 (PrimeTree.node 1361 (PrimeTree.node 1327 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1367 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1399 (PrimeTree.node 1381 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 1433 (PrimeTree.node 1427 (PrimeTree.node 1423 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1429 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1447 (PrimeTree.node 1439 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_4 : PrimeTree := (PrimeTree.node 1637 (PrimeTree.node 1553 (PrimeTree.node 1493 (PrimeTree.node 1481 (PrimeTree.node 1459 (PrimeTree.node 1453 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1471 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1487 (PrimeTree.node 1483 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1489 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 1531 (PrimeTree.node 1511 (PrimeTree.node 1499 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1523 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1549 (PrimeTree.node 1543 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 1601 (PrimeTree.node 1579 (PrimeTree.node 1567 (PrimeTree.node 1559 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1571 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1597 (PrimeTree.node 1583 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 1619 (PrimeTree.node 1609 (PrimeTree.node 1607 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1613 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1627 (PrimeTree.node 1621 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 1759 (PrimeTree.node 1709 (PrimeTree.node 1669 (PrimeTree.node 1663 (PrimeTree.node 1657 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1667 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1697 (PrimeTree.node 1693 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1699 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 1741 (PrimeTree.node 1723 (PrimeTree.node 1721 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1733 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1753 (PrimeTree.node 1747 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 1823 (PrimeTree.node 1789 (PrimeTree.node 1783 (PrimeTree.node 1777 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1787 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1811 (PrimeTree.node 1801 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 1867 (PrimeTree.node 1847 (PrimeTree.node 1831 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1861 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1873 (PrimeTree.node 1871 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_5 : PrimeTree := (PrimeTree.node 2099 (PrimeTree.node 1999 (PrimeTree.node 1949 (PrimeTree.node 1907 (PrimeTree.node 1889 (PrimeTree.node 1879 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1901 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1931 (PrimeTree.node 1913 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1933 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 1987 (PrimeTree.node 1973 (PrimeTree.node 1951 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 1979 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 1997 (PrimeTree.node 1993 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 2053 (PrimeTree.node 2027 (PrimeTree.node 2011 (PrimeTree.node 2003 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2017 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2039 (PrimeTree.node 2029 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 2083 (PrimeTree.node 2069 (PrimeTree.node 2063 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2081 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2089 (PrimeTree.node 2087 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 2221 (PrimeTree.node 2143 (PrimeTree.node 2131 (PrimeTree.node 2113 (PrimeTree.node 2111 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2129 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2141 (PrimeTree.node 2137 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 2203 (PrimeTree.node 2161 (PrimeTree.node 2153 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2179 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2213 (PrimeTree.node 2207 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 2273 (PrimeTree.node 2251 (PrimeTree.node 2239 (PrimeTree.node 2237 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2243 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2269 (PrimeTree.node 2267 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 2297 (PrimeTree.node 2287 (PrimeTree.node 2281 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2293 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2311 (PrimeTree.node 2309 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_6 : PrimeTree := (PrimeTree.node 2551 (PrimeTree.node 2423 (PrimeTree.node 2381 (PrimeTree.node 2351 (PrimeTree.node 2341 (PrimeTree.node 2339 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2347 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2371 (PrimeTree.node 2357 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2377 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 2399 (PrimeTree.node 2389 (PrimeTree.node 2383 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2393 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2417 (PrimeTree.node 2411 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 2477 (PrimeTree.node 2459 (PrimeTree.node 2441 (PrimeTree.node 2437 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2447 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2473 (PrimeTree.node 2467 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 2539 (PrimeTree.node 2521 (PrimeTree.node 2503 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2531 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2549 (PrimeTree.node 2543 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 2677 (PrimeTree.node 2621 (PrimeTree.node 2593 (PrimeTree.node 2579 (PrimeTree.node 2557 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2591 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2617 (PrimeTree.node 2609 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 2659 (PrimeTree.node 2647 (PrimeTree.node 2633 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2657 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2671 (PrimeTree.node 2663 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 2711 (PrimeTree.node 2693 (PrimeTree.node 2687 (PrimeTree.node 2683 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2689 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2707 (PrimeTree.node 2699 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 2731 (PrimeTree.node 2719 (PrimeTree.node 2713 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2729 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2749 (PrimeTree.node 2741 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_7 : PrimeTree := (PrimeTree.node 3001 (PrimeTree.node 2879 (PrimeTree.node 2819 (PrimeTree.node 2791 (PrimeTree.node 2777 (PrimeTree.node 2767 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2789 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2801 (PrimeTree.node 2797 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2803 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 2851 (PrimeTree.node 2837 (PrimeTree.node 2833 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2843 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2861 (PrimeTree.node 2857 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 2939 (PrimeTree.node 2909 (PrimeTree.node 2897 (PrimeTree.node 2887 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2903 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2927 (PrimeTree.node 2917 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 2969 (PrimeTree.node 2957 (PrimeTree.node 2953 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 2963 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 2999 (PrimeTree.node 2971 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 3121 (PrimeTree.node 3061 (PrimeTree.node 3037 (PrimeTree.node 3019 (PrimeTree.node 3011 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3023 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3049 (PrimeTree.node 3041 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 3089 (PrimeTree.node 3079 (PrimeTree.node 3067 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3083 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3119 (PrimeTree.node 3109 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 3191 (PrimeTree.node 3169 (PrimeTree.node 3163 (PrimeTree.node 3137 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3167 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3187 (PrimeTree.node 3181 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 3221 (PrimeTree.node 3209 (PrimeTree.node 3203 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3217 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3251 (PrimeTree.node 3229 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_8 : PrimeTree := (PrimeTree.node 3491 (PrimeTree.node 3361 (PrimeTree.node 3319 (PrimeTree.node 3299 (PrimeTree.node 3259 (PrimeTree.node 3257 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3271 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3307 (PrimeTree.node 3301 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3313 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 3343 (PrimeTree.node 3329 (PrimeTree.node 3323 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3331 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3359 (PrimeTree.node 3347 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 3433 (PrimeTree.node 3391 (PrimeTree.node 3373 (PrimeTree.node 3371 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3389 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3413 (PrimeTree.node 3407 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 3463 (PrimeTree.node 3457 (PrimeTree.node 3449 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3461 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3469 (PrimeTree.node 3467 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 3593 (PrimeTree.node 3541 (PrimeTree.node 3527 (PrimeTree.node 3511 (PrimeTree.node 3499 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3517 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3533 (PrimeTree.node 3529 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3539 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 3571 (PrimeTree.node 3557 (PrimeTree.node 3547 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3559 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3583 (PrimeTree.node 3581 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 3643 (PrimeTree.node 3623 (PrimeTree.node 3613 (PrimeTree.node 3607 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3617 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3637 (PrimeTree.node 3631 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 3677 (PrimeTree.node 3671 (PrimeTree.node 3659 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3673 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3697 (PrimeTree.node 3691 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_9 : PrimeTree := (PrimeTree.node 3931 (PrimeTree.node 3833 (PrimeTree.node 3769 (PrimeTree.node 3733 (PrimeTree.node 3719 (PrimeTree.node 3709 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3727 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3761 (PrimeTree.node 3739 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3767 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 3803 (PrimeTree.node 3793 (PrimeTree.node 3779 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3797 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3823 (PrimeTree.node 3821 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 3889 (PrimeTree.node 3863 (PrimeTree.node 3851 (PrimeTree.node 3847 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3853 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3881 (PrimeTree.node 3877 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 3919 (PrimeTree.node 3911 (PrimeTree.node 3907 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3917 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 3929 (PrimeTree.node 3923 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 4057 (PrimeTree.node 4007 (PrimeTree.node 3989 (PrimeTree.node 3947 (PrimeTree.node 3943 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 3967 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4003 (PrimeTree.node 4001 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 4027 (PrimeTree.node 4019 (PrimeTree.node 4013 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4021 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4051 (PrimeTree.node 4049 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 4127 (PrimeTree.node 4093 (PrimeTree.node 4079 (PrimeTree.node 4073 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4091 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4111 (PrimeTree.node 4099 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 4153 (PrimeTree.node 4133 (PrimeTree.node 4129 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4139 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4159 (PrimeTree.node 4157 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_10 : PrimeTree := (PrimeTree.node 4441 (PrimeTree.node 4289 (PrimeTree.node 4243 (PrimeTree.node 4219 (PrimeTree.node 4211 (PrimeTree.node 4201 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4217 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4231 (PrimeTree.node 4229 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4241 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 4271 (PrimeTree.node 4259 (PrimeTree.node 4253 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4261 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4283 (PrimeTree.node 4273 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 4363 (PrimeTree.node 4339 (PrimeTree.node 4327 (PrimeTree.node 4297 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4337 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4357 (PrimeTree.node 4349 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 4409 (PrimeTree.node 4391 (PrimeTree.node 4373 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4397 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4423 (PrimeTree.node 4421 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 4549 (PrimeTree.node 4493 (PrimeTree.node 4463 (PrimeTree.node 4451 (PrimeTree.node 4447 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4457 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4483 (PrimeTree.node 4481 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 4519 (PrimeTree.node 4513 (PrimeTree.node 4507 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4517 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4547 (PrimeTree.node 4523 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 4621 (PrimeTree.node 4591 (PrimeTree.node 4567 (PrimeTree.node 4561 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4583 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4603 (PrimeTree.node 4597 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 4649 (PrimeTree.node 4639 (PrimeTree.node 4637 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4643 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4657 (PrimeTree.node 4651 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_11 : PrimeTree := (PrimeTree.node 4937 (PrimeTree.node 4799 (PrimeTree.node 4733 (PrimeTree.node 4703 (PrimeTree.node 4679 (PrimeTree.node 4673 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4691 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4723 (PrimeTree.node 4721 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4729 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 4787 (PrimeTree.node 4759 (PrimeTree.node 4751 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4783 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4793 (PrimeTree.node 4789 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 4877 (PrimeTree.node 4831 (PrimeTree.node 4813 (PrimeTree.node 4801 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4817 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4871 (PrimeTree.node 4861 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 4919 (PrimeTree.node 4903 (PrimeTree.node 4889 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4909 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4933 (PrimeTree.node 4931 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 5023 (PrimeTree.node 4987 (PrimeTree.node 4967 (PrimeTree.node 4951 (PrimeTree.node 4943 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 4957 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 4973 (PrimeTree.node 4969 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 5009 (PrimeTree.node 4999 (PrimeTree.node 4993 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5003 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5021 (PrimeTree.node 5011 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 5099 (PrimeTree.node 5077 (PrimeTree.node 5051 (PrimeTree.node 5039 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5059 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5087 (PrimeTree.node 5081 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 5119 (PrimeTree.node 5107 (PrimeTree.node 5101 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5113 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5153 (PrimeTree.node 5147 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_12 : PrimeTree := (PrimeTree.node 5431 (PrimeTree.node 5303 (PrimeTree.node 5233 (PrimeTree.node 5197 (PrimeTree.node 5179 (PrimeTree.node 5171 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5189 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5227 (PrimeTree.node 5209 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5231 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 5279 (PrimeTree.node 5261 (PrimeTree.node 5237 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5273 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5297 (PrimeTree.node 5281 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 5387 (PrimeTree.node 5347 (PrimeTree.node 5323 (PrimeTree.node 5309 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5333 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5381 (PrimeTree.node 5351 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 5413 (PrimeTree.node 5399 (PrimeTree.node 5393 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5407 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5419 (PrimeTree.node 5417 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 5531 (PrimeTree.node 5483 (PrimeTree.node 5449 (PrimeTree.node 5441 (PrimeTree.node 5437 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5443 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5477 (PrimeTree.node 5471 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5479 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 5519 (PrimeTree.node 5503 (PrimeTree.node 5501 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5507 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5527 (PrimeTree.node 5521 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 5623 (PrimeTree.node 5573 (PrimeTree.node 5563 (PrimeTree.node 5557 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5569 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5591 (PrimeTree.node 5581 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 5651 (PrimeTree.node 5641 (PrimeTree.node 5639 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5647 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5657 (PrimeTree.node 5653 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_13 : PrimeTree := (PrimeTree.node 5881 (PrimeTree.node 5801 (PrimeTree.node 5737 (PrimeTree.node 5693 (PrimeTree.node 5683 (PrimeTree.node 5669 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5689 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5711 (PrimeTree.node 5701 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5717 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 5779 (PrimeTree.node 5743 (PrimeTree.node 5741 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5749 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5791 (PrimeTree.node 5783 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 5849 (PrimeTree.node 5827 (PrimeTree.node 5813 (PrimeTree.node 5807 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5821 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5843 (PrimeTree.node 5839 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 5867 (PrimeTree.node 5857 (PrimeTree.node 5851 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5861 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5879 (PrimeTree.node 5869 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 6047 (PrimeTree.node 5981 (PrimeTree.node 5927 (PrimeTree.node 5903 (PrimeTree.node 5897 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 5923 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 5953 (PrimeTree.node 5939 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 6029 (PrimeTree.node 6007 (PrimeTree.node 5987 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6011 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6043 (PrimeTree.node 6037 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 6101 (PrimeTree.node 6079 (PrimeTree.node 6067 (PrimeTree.node 6053 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6073 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6091 (PrimeTree.node 6089 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 6133 (PrimeTree.node 6121 (PrimeTree.node 6113 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6131 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6151 (PrimeTree.node 6143 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_14 : PrimeTree := (PrimeTree.node 6379 (PrimeTree.node 6287 (PrimeTree.node 6229 (PrimeTree.node 6203 (PrimeTree.node 6197 (PrimeTree.node 6173 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6199 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6217 (PrimeTree.node 6211 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6221 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 6269 (PrimeTree.node 6257 (PrimeTree.node 6247 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6263 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6277 (PrimeTree.node 6271 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 6337 (PrimeTree.node 6317 (PrimeTree.node 6301 (PrimeTree.node 6299 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6311 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6329 (PrimeTree.node 6323 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 6361 (PrimeTree.node 6353 (PrimeTree.node 6343 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6359 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6373 (PrimeTree.node 6367 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 6551 (PrimeTree.node 6469 (PrimeTree.node 6427 (PrimeTree.node 6397 (PrimeTree.node 6389 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6421 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6451 (PrimeTree.node 6449 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 6521 (PrimeTree.node 6481 (PrimeTree.node 6473 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6491 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6547 (PrimeTree.node 6529 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 6599 (PrimeTree.node 6571 (PrimeTree.node 6563 (PrimeTree.node 6553 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6569 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6581 (PrimeTree.node 6577 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 6653 (PrimeTree.node 6619 (PrimeTree.node 6607 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6637 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6661 (PrimeTree.node 6659 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_15 : PrimeTree := (PrimeTree.node 6911 (PrimeTree.node 6793 (PrimeTree.node 6733 (PrimeTree.node 6701 (PrimeTree.node 6689 (PrimeTree.node 6679 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6691 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6709 (PrimeTree.node 6703 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6719 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 6779 (PrimeTree.node 6761 (PrimeTree.node 6737 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6763 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6791 (PrimeTree.node 6781 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 6857 (PrimeTree.node 6829 (PrimeTree.node 6823 (PrimeTree.node 6803 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6827 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6841 (PrimeTree.node 6833 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 6883 (PrimeTree.node 6869 (PrimeTree.node 6863 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6871 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6907 (PrimeTree.node 6899 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 7019 (PrimeTree.node 6971 (PrimeTree.node 6959 (PrimeTree.node 6947 (PrimeTree.node 6917 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6949 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 6967 (PrimeTree.node 6961 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 6997 (PrimeTree.node 6983 (PrimeTree.node 6977 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 6991 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7013 (PrimeTree.node 7001 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 7103 (PrimeTree.node 7057 (PrimeTree.node 7039 (PrimeTree.node 7027 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7043 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7079 (PrimeTree.node 7069 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 7129 (PrimeTree.node 7121 (PrimeTree.node 7109 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7127 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7159 (PrimeTree.node 7151 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_16 : PrimeTree := (PrimeTree.node 7477 (PrimeTree.node 7309 (PrimeTree.node 7237 (PrimeTree.node 7211 (PrimeTree.node 7193 (PrimeTree.node 7187 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7207 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7219 (PrimeTree.node 7213 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7229 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 7283 (PrimeTree.node 7247 (PrimeTree.node 7243 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7253 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7307 (PrimeTree.node 7297 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 7393 (PrimeTree.node 7349 (PrimeTree.node 7331 (PrimeTree.node 7321 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7333 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7369 (PrimeTree.node 7351 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 7451 (PrimeTree.node 7417 (PrimeTree.node 7411 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7433 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7459 (PrimeTree.node 7457 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 7573 (PrimeTree.node 7529 (PrimeTree.node 7499 (PrimeTree.node 7487 (PrimeTree.node 7481 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7489 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7517 (PrimeTree.node 7507 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7523 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 7549 (PrimeTree.node 7541 (PrimeTree.node 7537 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7547 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7561 (PrimeTree.node 7559 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 7621 (PrimeTree.node 7591 (PrimeTree.node 7583 (PrimeTree.node 7577 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7589 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7607 (PrimeTree.node 7603 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 7669 (PrimeTree.node 7643 (PrimeTree.node 7639 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7649 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7681 (PrimeTree.node 7673 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_17 : PrimeTree := (PrimeTree.node 7949 (PrimeTree.node 7829 (PrimeTree.node 7753 (PrimeTree.node 7717 (PrimeTree.node 7699 (PrimeTree.node 7691 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7703 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7727 (PrimeTree.node 7723 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7741 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 7793 (PrimeTree.node 7759 (PrimeTree.node 7757 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7789 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7823 (PrimeTree.node 7817 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 7883 (PrimeTree.node 7873 (PrimeTree.node 7853 (PrimeTree.node 7841 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7867 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7879 (PrimeTree.node 7877 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 7927 (PrimeTree.node 7907 (PrimeTree.node 7901 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7919 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 7937 (PrimeTree.node 7933 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 8093 (PrimeTree.node 8039 (PrimeTree.node 8009 (PrimeTree.node 7963 (PrimeTree.node 7951 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 7993 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8017 (PrimeTree.node 8011 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 8081 (PrimeTree.node 8059 (PrimeTree.node 8053 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8069 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8089 (PrimeTree.node 8087 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 8167 (PrimeTree.node 8123 (PrimeTree.node 8111 (PrimeTree.node 8101 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8117 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8161 (PrimeTree.node 8147 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 8209 (PrimeTree.node 8179 (PrimeTree.node 8171 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8191 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8221 (PrimeTree.node 8219 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_18 : PrimeTree := (PrimeTree.node 8513 (PrimeTree.node 8363 (PrimeTree.node 8291 (PrimeTree.node 8263 (PrimeTree.node 8237 (PrimeTree.node 8233 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8243 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8273 (PrimeTree.node 8269 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8287 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 8317 (PrimeTree.node 8297 (PrimeTree.node 8293 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8311 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8353 (PrimeTree.node 8329 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 8429 (PrimeTree.node 8389 (PrimeTree.node 8377 (PrimeTree.node 8369 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8387 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8423 (PrimeTree.node 8419 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 8461 (PrimeTree.node 8443 (PrimeTree.node 8431 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8447 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8501 (PrimeTree.node 8467 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 8629 (PrimeTree.node 8573 (PrimeTree.node 8539 (PrimeTree.node 8527 (PrimeTree.node 8521 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8537 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8563 (PrimeTree.node 8543 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 8609 (PrimeTree.node 8597 (PrimeTree.node 8581 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8599 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8627 (PrimeTree.node 8623 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 8689 (PrimeTree.node 8669 (PrimeTree.node 8647 (PrimeTree.node 8641 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8663 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8681 (PrimeTree.node 8677 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 8713 (PrimeTree.node 8699 (PrimeTree.node 8693 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8707 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8731 (PrimeTree.node 8719 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_19 : PrimeTree := (PrimeTree.node 9001 (PrimeTree.node 8861 (PrimeTree.node 8807 (PrimeTree.node 8761 (PrimeTree.node 8747 (PrimeTree.node 8741 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8753 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8783 (PrimeTree.node 8779 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8803 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 8837 (PrimeTree.node 8821 (PrimeTree.node 8819 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8831 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8849 (PrimeTree.node 8839 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 8933 (PrimeTree.node 8893 (PrimeTree.node 8867 (PrimeTree.node 8863 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8887 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8929 (PrimeTree.node 8923 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 8969 (PrimeTree.node 8951 (PrimeTree.node 8941 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 8963 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 8999 (PrimeTree.node 8971 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 9133 (PrimeTree.node 9049 (PrimeTree.node 9029 (PrimeTree.node 9011 (PrimeTree.node 9007 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9013 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9043 (PrimeTree.node 9041 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 9103 (PrimeTree.node 9067 (PrimeTree.node 9059 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9091 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9127 (PrimeTree.node 9109 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 9187 (PrimeTree.node 9161 (PrimeTree.node 9151 (PrimeTree.node 9137 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9157 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9181 (PrimeTree.node 9173 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 9221 (PrimeTree.node 9203 (PrimeTree.node 9199 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9209 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9239 (PrimeTree.node 9227 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_20 : PrimeTree := (PrimeTree.node 9479 (PrimeTree.node 9391 (PrimeTree.node 9323 (PrimeTree.node 9283 (PrimeTree.node 9277 (PrimeTree.node 9257 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9281 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9311 (PrimeTree.node 9293 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9319 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 9349 (PrimeTree.node 9341 (PrimeTree.node 9337 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9343 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9377 (PrimeTree.node 9371 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 9433 (PrimeTree.node 9419 (PrimeTree.node 9403 (PrimeTree.node 9397 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9413 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9431 (PrimeTree.node 9421 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 9463 (PrimeTree.node 9439 (PrimeTree.node 9437 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9461 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9473 (PrimeTree.node 9467 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 9631 (PrimeTree.node 9551 (PrimeTree.node 9521 (PrimeTree.node 9497 (PrimeTree.node 9491 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9511 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9539 (PrimeTree.node 9533 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9547 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 9619 (PrimeTree.node 9601 (PrimeTree.node 9587 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9613 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9629 (PrimeTree.node 9623 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 9697 (PrimeTree.node 9677 (PrimeTree.node 9649 (PrimeTree.node 9643 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9661 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9689 (PrimeTree.node 9679 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 9739 (PrimeTree.node 9721 (PrimeTree.node 9719 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9733 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9749 (PrimeTree.node 9743 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_21 : PrimeTree := (PrimeTree.node 10039 (PrimeTree.node 9883 (PrimeTree.node 9829 (PrimeTree.node 9791 (PrimeTree.node 9781 (PrimeTree.node 9769 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9787 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9811 (PrimeTree.node 9803 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9817 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 9857 (PrimeTree.node 9839 (PrimeTree.node 9833 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9851 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9871 (PrimeTree.node 9859 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 9941 (PrimeTree.node 9923 (PrimeTree.node 9901 (PrimeTree.node 9887 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9907 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 9931 (PrimeTree.node 9929 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 10007 (PrimeTree.node 9967 (PrimeTree.node 9949 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 9973 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10037 (PrimeTree.node 10009 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 10159 (PrimeTree.node 10099 (PrimeTree.node 10079 (PrimeTree.node 10067 (PrimeTree.node 10061 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10069 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10093 (PrimeTree.node 10091 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 10139 (PrimeTree.node 10111 (PrimeTree.node 10103 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10133 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10151 (PrimeTree.node 10141 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 10223 (PrimeTree.node 10181 (PrimeTree.node 10169 (PrimeTree.node 10163 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10177 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10211 (PrimeTree.node 10193 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 10259 (PrimeTree.node 10247 (PrimeTree.node 10243 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10253 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10271 (PrimeTree.node 10267 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_22 : PrimeTree := (PrimeTree.node 10567 (PrimeTree.node 10429 (PrimeTree.node 10337 (PrimeTree.node 10313 (PrimeTree.node 10301 (PrimeTree.node 10289 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10303 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10331 (PrimeTree.node 10321 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10333 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 10391 (PrimeTree.node 10357 (PrimeTree.node 10343 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10369 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10427 (PrimeTree.node 10399 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 10487 (PrimeTree.node 10459 (PrimeTree.node 10453 (PrimeTree.node 10433 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10457 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10477 (PrimeTree.node 10463 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 10529 (PrimeTree.node 10501 (PrimeTree.node 10499 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10513 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10559 (PrimeTree.node 10531 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 10691 (PrimeTree.node 10631 (PrimeTree.node 10607 (PrimeTree.node 10597 (PrimeTree.node 10589 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10601 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10627 (PrimeTree.node 10613 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 10663 (PrimeTree.node 10651 (PrimeTree.node 10639 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10657 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10687 (PrimeTree.node 10667 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 10753 (PrimeTree.node 10729 (PrimeTree.node 10711 (PrimeTree.node 10709 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10723 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10739 (PrimeTree.node 10733 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 10799 (PrimeTree.node 10781 (PrimeTree.node 10771 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10789 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10837 (PrimeTree.node 10831 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_23 : PrimeTree := (PrimeTree.node 11117 (PrimeTree.node 10979 (PrimeTree.node 10903 (PrimeTree.node 10867 (PrimeTree.node 10859 (PrimeTree.node 10853 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10861 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10889 (PrimeTree.node 10883 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10891 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 10949 (PrimeTree.node 10937 (PrimeTree.node 10909 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 10939 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 10973 (PrimeTree.node 10957 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 11059 (PrimeTree.node 11027 (PrimeTree.node 10993 (PrimeTree.node 10987 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11003 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11057 (PrimeTree.node 11047 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 11087 (PrimeTree.node 11071 (PrimeTree.node 11069 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11083 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11113 (PrimeTree.node 11093 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 11257 (PrimeTree.node 11173 (PrimeTree.node 11159 (PrimeTree.node 11131 (PrimeTree.node 11119 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11149 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11171 (PrimeTree.node 11161 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 11239 (PrimeTree.node 11197 (PrimeTree.node 11177 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11213 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11251 (PrimeTree.node 11243 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 11317 (PrimeTree.node 11287 (PrimeTree.node 11273 (PrimeTree.node 11261 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11279 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11311 (PrimeTree.node 11299 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 11353 (PrimeTree.node 11329 (PrimeTree.node 11321 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11351 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11383 (PrimeTree.node 11369 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_24 : PrimeTree := (PrimeTree.node 11699 (PrimeTree.node 11527 (PrimeTree.node 11471 (PrimeTree.node 11437 (PrimeTree.node 11411 (PrimeTree.node 11399 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11423 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11447 (PrimeTree.node 11443 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11467 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 11497 (PrimeTree.node 11489 (PrimeTree.node 11483 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11491 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11519 (PrimeTree.node 11503 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 11617 (PrimeTree.node 11587 (PrimeTree.node 11551 (PrimeTree.node 11549 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11579 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11597 (PrimeTree.node 11593 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 11677 (PrimeTree.node 11633 (PrimeTree.node 11621 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11657 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11689 (PrimeTree.node 11681 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 11831 (PrimeTree.node 11783 (PrimeTree.node 11731 (PrimeTree.node 11717 (PrimeTree.node 11701 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11719 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11777 (PrimeTree.node 11743 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11779 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 11813 (PrimeTree.node 11801 (PrimeTree.node 11789 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11807 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11827 (PrimeTree.node 11821 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 11903 (PrimeTree.node 11867 (PrimeTree.node 11839 (PrimeTree.node 11833 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11863 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11897 (PrimeTree.node 11887 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 11933 (PrimeTree.node 11923 (PrimeTree.node 11909 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11927 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 11941 (PrimeTree.node 11939 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_25 : PrimeTree := (PrimeTree.node 12239 (PrimeTree.node 12101 (PrimeTree.node 12037 (PrimeTree.node 11981 (PrimeTree.node 11969 (PrimeTree.node 11959 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 11971 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12007 (PrimeTree.node 11987 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12011 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 12071 (PrimeTree.node 12043 (PrimeTree.node 12041 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12049 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12097 (PrimeTree.node 12073 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 12157 (PrimeTree.node 12119 (PrimeTree.node 12109 (PrimeTree.node 12107 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12113 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12149 (PrimeTree.node 12143 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 12203 (PrimeTree.node 12163 (PrimeTree.node 12161 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12197 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12227 (PrimeTree.node 12211 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 12373 (PrimeTree.node 12281 (PrimeTree.node 12263 (PrimeTree.node 12251 (PrimeTree.node 12241 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12253 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12277 (PrimeTree.node 12269 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 12329 (PrimeTree.node 12301 (PrimeTree.node 12289 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12323 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12347 (PrimeTree.node 12343 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 12421 (PrimeTree.node 12401 (PrimeTree.node 12379 (PrimeTree.node 12377 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12391 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12413 (PrimeTree.node 12409 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 12457 (PrimeTree.node 12437 (PrimeTree.node 12433 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12451 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12479 (PrimeTree.node 12473 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_26 : PrimeTree := (PrimeTree.node 12721 (PrimeTree.node 12601 (PrimeTree.node 12541 (PrimeTree.node 12511 (PrimeTree.node 12497 (PrimeTree.node 12491 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12503 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12527 (PrimeTree.node 12517 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12539 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 12577 (PrimeTree.node 12553 (PrimeTree.node 12547 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12569 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12589 (PrimeTree.node 12583 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 12653 (PrimeTree.node 12637 (PrimeTree.node 12613 (PrimeTree.node 12611 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12619 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12647 (PrimeTree.node 12641 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 12697 (PrimeTree.node 12671 (PrimeTree.node 12659 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12689 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12713 (PrimeTree.node 12703 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 12889 (PrimeTree.node 12799 (PrimeTree.node 12763 (PrimeTree.node 12743 (PrimeTree.node 12739 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12757 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12791 (PrimeTree.node 12781 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 12829 (PrimeTree.node 12821 (PrimeTree.node 12809 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12823 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12853 (PrimeTree.node 12841 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 12923 (PrimeTree.node 12911 (PrimeTree.node 12899 (PrimeTree.node 12893 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12907 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12919 (PrimeTree.node 12917 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 12967 (PrimeTree.node 12953 (PrimeTree.node 12941 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 12959 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 12979 (PrimeTree.node 12973 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_27 : PrimeTree := (PrimeTree.node 13259 (PrimeTree.node 13127 (PrimeTree.node 13049 (PrimeTree.node 13009 (PrimeTree.node 13003 (PrimeTree.node 13001 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13007 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13037 (PrimeTree.node 13033 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13043 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 13103 (PrimeTree.node 13093 (PrimeTree.node 13063 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13099 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13121 (PrimeTree.node 13109 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 13183 (PrimeTree.node 13163 (PrimeTree.node 13151 (PrimeTree.node 13147 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13159 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13177 (PrimeTree.node 13171 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 13229 (PrimeTree.node 13217 (PrimeTree.node 13187 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13219 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13249 (PrimeTree.node 13241 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 13411 (PrimeTree.node 13331 (PrimeTree.node 13309 (PrimeTree.node 13291 (PrimeTree.node 13267 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13297 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13327 (PrimeTree.node 13313 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 13381 (PrimeTree.node 13339 (PrimeTree.node 13337 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13367 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13399 (PrimeTree.node 13397 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 13469 (PrimeTree.node 13451 (PrimeTree.node 13421 (PrimeTree.node 13417 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13441 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13463 (PrimeTree.node 13457 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 13513 (PrimeTree.node 13487 (PrimeTree.node 13477 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13499 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13537 (PrimeTree.node 13523 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_28 : PrimeTree := (PrimeTree.node 13807 (PrimeTree.node 13693 (PrimeTree.node 13633 (PrimeTree.node 13597 (PrimeTree.node 13577 (PrimeTree.node 13567 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13591 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13619 (PrimeTree.node 13613 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13627 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 13681 (PrimeTree.node 13669 (PrimeTree.node 13649 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13679 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13691 (PrimeTree.node 13687 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 13751 (PrimeTree.node 13721 (PrimeTree.node 13709 (PrimeTree.node 13697 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13711 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13729 (PrimeTree.node 13723 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 13781 (PrimeTree.node 13759 (PrimeTree.node 13757 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13763 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13799 (PrimeTree.node 13789 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 13933 (PrimeTree.node 13883 (PrimeTree.node 13859 (PrimeTree.node 13831 (PrimeTree.node 13829 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13841 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13877 (PrimeTree.node 13873 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13879 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 13913 (PrimeTree.node 13903 (PrimeTree.node 13901 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13907 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 13931 (PrimeTree.node 13921 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 14029 (PrimeTree.node 13999 (PrimeTree.node 13967 (PrimeTree.node 13963 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 13997 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14011 (PrimeTree.node 14009 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 14071 (PrimeTree.node 14051 (PrimeTree.node 14033 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14057 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14083 (PrimeTree.node 14081 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_29 : PrimeTree := (PrimeTree.node 14423 (PrimeTree.node 14293 (PrimeTree.node 14197 (PrimeTree.node 14153 (PrimeTree.node 14143 (PrimeTree.node 14107 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14149 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14173 (PrimeTree.node 14159 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14177 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 14249 (PrimeTree.node 14221 (PrimeTree.node 14207 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14243 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14281 (PrimeTree.node 14251 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 14369 (PrimeTree.node 14327 (PrimeTree.node 14321 (PrimeTree.node 14303 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14323 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14347 (PrimeTree.node 14341 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 14407 (PrimeTree.node 14389 (PrimeTree.node 14387 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14401 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14419 (PrimeTree.node 14411 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 14551 (PrimeTree.node 14489 (PrimeTree.node 14449 (PrimeTree.node 14437 (PrimeTree.node 14431 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14447 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14479 (PrimeTree.node 14461 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 14537 (PrimeTree.node 14519 (PrimeTree.node 14503 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14533 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14549 (PrimeTree.node 14543 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 14627 (PrimeTree.node 14591 (PrimeTree.node 14561 (PrimeTree.node 14557 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14563 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14621 (PrimeTree.node 14593 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 14653 (PrimeTree.node 14633 (PrimeTree.node 14629 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14639 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14669 (PrimeTree.node 14657 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_30 : PrimeTree := (PrimeTree.node 14929 (PrimeTree.node 14797 (PrimeTree.node 14747 (PrimeTree.node 14723 (PrimeTree.node 14713 (PrimeTree.node 14699 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14717 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14737 (PrimeTree.node 14731 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14741 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 14771 (PrimeTree.node 14759 (PrimeTree.node 14753 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14767 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14783 (PrimeTree.node 14779 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 14867 (PrimeTree.node 14831 (PrimeTree.node 14821 (PrimeTree.node 14813 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14827 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14851 (PrimeTree.node 14843 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 14891 (PrimeTree.node 14879 (PrimeTree.node 14869 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14887 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14923 (PrimeTree.node 14897 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 15083 (PrimeTree.node 15013 (PrimeTree.node 14957 (PrimeTree.node 14947 (PrimeTree.node 14939 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 14951 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 14983 (PrimeTree.node 14969 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 15061 (PrimeTree.node 15031 (PrimeTree.node 15017 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15053 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15077 (PrimeTree.node 15073 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 15139 (PrimeTree.node 15121 (PrimeTree.node 15101 (PrimeTree.node 15091 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15107 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15137 (PrimeTree.node 15131 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 15187 (PrimeTree.node 15161 (PrimeTree.node 15149 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15173 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15199 (PrimeTree.node 15193 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))
def bst_sub_31 : PrimeTree := (PrimeTree.node 15451 (PrimeTree.node 15329 (PrimeTree.node 15277 (PrimeTree.node 15259 (PrimeTree.node 15233 (PrimeTree.node 15227 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15241 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15269 (PrimeTree.node 15263 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15271 PrimeTree.leaf PrimeTree.leaf))) (PrimeTree.node 15307 (PrimeTree.node 15289 (PrimeTree.node 15287 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15299 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15319 (PrimeTree.node 15313 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 15383 (PrimeTree.node 15361 (PrimeTree.node 15349 (PrimeTree.node 15331 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15359 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15377 (PrimeTree.node 15373 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 15427 (PrimeTree.node 15401 (PrimeTree.node 15391 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15413 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15443 (PrimeTree.node 15439 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))) (PrimeTree.node 15601 (PrimeTree.node 15527 (PrimeTree.node 15493 (PrimeTree.node 15467 (PrimeTree.node 15461 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15473 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15511 (PrimeTree.node 15497 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 15569 (PrimeTree.node 15551 (PrimeTree.node 15541 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15559 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15583 (PrimeTree.node 15581 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf))) (PrimeTree.node 15649 (PrimeTree.node 15641 (PrimeTree.node 15619 (PrimeTree.node 15607 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15629 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15647 (PrimeTree.node 15643 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)) (PrimeTree.node 15679 (PrimeTree.node 15667 (PrimeTree.node 15661 PrimeTree.leaf PrimeTree.leaf) (PrimeTree.node 15671 PrimeTree.leaf PrimeTree.leaf)) (PrimeTree.node 15727 (PrimeTree.node 15683 PrimeTree.leaf PrimeTree.leaf) PrimeTree.leaf)))))


def bst : PrimeTree := (PrimeTree.node 7177 (PrimeTree.node 3253 (PrimeTree.node 1451 (PrimeTree.node 631 (PrimeTree.node 271 bst_sub_0 bst_sub_1) (PrimeTree.node 1031 bst_sub_2 bst_sub_3)) (PrimeTree.node 2333 (PrimeTree.node 1877 bst_sub_4 bst_sub_5) (PrimeTree.node 2753 bst_sub_6 bst_sub_7))) (PrimeTree.node 5167 (PrimeTree.node 4177 (PrimeTree.node 3701 bst_sub_8 bst_sub_9) (PrimeTree.node 4663 bst_sub_10 bst_sub_11)) (PrimeTree.node 6163 (PrimeTree.node 5659 bst_sub_12 bst_sub_13) (PrimeTree.node 6673 bst_sub_14 bst_sub_15)))) (PrimeTree.node 11393 (PrimeTree.node 9241 (PrimeTree.node 8231 (PrimeTree.node 7687 bst_sub_16 bst_sub_17) (PrimeTree.node 8737 bst_sub_18 bst_sub_19)) (PrimeTree.node 10273 (PrimeTree.node 9767 bst_sub_20 bst_sub_21) (PrimeTree.node 10847 bst_sub_22 bst_sub_23))) (PrimeTree.node 13553 (PrimeTree.node 12487 (PrimeTree.node 11953 bst_sub_24 bst_sub_25) (PrimeTree.node 12983 bst_sub_26 bst_sub_27)) (PrimeTree.node 14683 (PrimeTree.node 14087 bst_sub_28 bst_sub_29) (PrimeTree.node 15217 bst_sub_30 bst_sub_31)))))

def bst_contains (n : ℕ) : PrimeTree → Bool
  | .leaf => false
  | .node val l r =>
    if n = val then true
    else if n < val then bst_contains n l
    else bst_contains n r

def is_prime_lookup (n : ℕ) : Bool :=
  if n < 15728 then
    bst_contains n bst
  else
    false

lemma lt_of_is_prime_lookup_eq_true (x : ℕ) (h : is_prime_lookup x = true) : x < 15728 := by
  unfold is_prime_lookup at h
  by_contra hc
  rw [if_neg hc] at h
  contradiction

lemma k_lt_n_of_le (n k : ℕ) (h : 3 + 2 * k ≤ n) : k < n := by omega

lemma le_mul_self_of_ge_one (k : ℕ) : 3 + 2 * k ≤ (3 + 2 * k) * (3 + 2 * k) := by
  have : 1 ≤ 3 + 2 * k := by omega
  exact Nat.le_mul_self (3 + 2 * k)

def has_odd_divisor_from (n : ℕ) (d : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if d * d > n then false
    else if n % d == 0 then true
    else has_odd_divisor_from n (d + 2) f

def is_prime_custom (n : ℕ) : Bool :=
  if n ≤ 1 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else !(has_odd_divisor_from n 3 65)

lemma no_odd_divisor_of_has_odd_divisor_from_eq_false (n d fuel : ℕ) (h : has_odd_divisor_from n d fuel = false) :
    ∀ m, d ≤ m → m * m ≤ n → (∃ k < fuel, m = d + 2 * k) → ¬ m ∣ n := by
  induction fuel generalizing d with
  | zero =>
    intro m hd hm h_exists hdvd
    rcases h_exists with ⟨k, hk, _⟩
    omega
  | succ f ih =>
    intro m hd hm h_exists hdvd
    rw [has_odd_divisor_from] at h
    by_cases h_lt : d * d > n
    · rw [if_pos h_lt] at h
      have : d * d ≤ m * m := Nat.mul_le_mul hd hd
      omega
    · rw [if_neg h_lt] at h
      by_cases hdiv : n % d = 0
      · have h_true : (n % d == 0) = true := beq_iff_eq.mpr hdiv
        rw [h_true] at h
        contradiction
      · have h_false : (n % d == 0) = false := beq_eq_false_iff_ne.mpr hdiv
        rw [h_false] at h
        rcases h_exists with ⟨k, hk, rfl⟩
        rcases k with _ | p
        · simp only [mul_zero, add_zero] at hdvd ⊢
          exact hdiv (Nat.dvd_iff_mod_eq_zero.mp hdvd)
        · have h_m : d + 2 * (p + 1) = (d + 2) + 2 * p := by ring
          have hp_lt : p < f := by omega
          have hd_le : d + 2 ≤ d + 2 * (p + 1) := by omega
          have h_ex : ∃ k'' < f, d + 2 * (p + 1) = (d + 2) + 2 * k'' := ⟨p, hp_lt, h_m⟩
          exact ih (d + 2) h (d + 2 * (p + 1)) hd_le hm h_ex hdvd

lemma minFac_odd_of_odd {n : ℕ} (h_odd : n % 2 = 1) (hn : 2 ≤ n) : (Nat.minFac n) % 2 = 1 := by
  have hn1 : n ≠ 1 := by omega
  have h_prime := Nat.minFac_prime hn1
  have h_dvd := Nat.minFac_dvd n
  by_contra hc
  have hc2 : Nat.minFac n % 2 = 0 := by omega
  have h2_dvd : 2 ∣ Nat.minFac n := Nat.dvd_of_mod_eq_zero hc2
  rcases (Nat.Prime.eq_one_or_self_of_dvd h_prime 2 h2_dvd) with h1 | h2
  · contradiction
  · rw [← h2] at h_dvd
    have : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h_dvd
    omega

lemma prime_of_is_prime_custom (n : ℕ) (hn_lt : n < 15728) (h : is_prime_custom n = true) : Nat.Prime n := by
  rw [is_prime_custom] at h
  by_cases hn1 : n ≤ 1
  · rw [if_pos hn1] at h; contradiction
  · rw [if_neg hn1] at h
    by_cases hn2 : n = 2
    · subst hn2; exact Nat.prime_two
    · have h_n2_eq : (n == 2) = false := beq_eq_false_iff_ne.mpr hn2
      rw [h_n2_eq] at h
      by_cases hn_even : n % 2 = 0
      · have h_even_eq : (n % 2 == 0) = true := beq_iff_eq.mpr hn_even
        rw [h_even_eq] at h
        contradiction
      · have h_even_eq : (n % 2 == 0) = false := beq_eq_false_iff_ne.mpr hn_even
        rw [h_even_eq] at h
        simp at h
        have hn_odd : n % 2 = 1 := by omega
        have hn_ge_2 : 2 ≤ n := by omega
        by_contra h_not_prime
        have h_minFac_sq : (Nat.minFac n) ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) h_not_prime
        have h_minFac_dvd : (Nat.minFac n) ∣ n := Nat.minFac_dvd n
        have h_minFac_prime : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
        have h_minFac_ge_3 : 3 ≤ Nat.minFac n := by
          have : (Nat.minFac n) % 2 = 1 := minFac_odd_of_odd hn_odd hn_ge_2
          have : 2 ≤ Nat.minFac n := Nat.Prime.two_le h_minFac_prime
          omega
        have h_exists_k : ∃ k, Nat.minFac n = 3 + 2 * k := by
          have h_even : 2 ∣ Nat.minFac n - 3 := by
            have : (Nat.minFac n - 3) % 2 = 0 := by
              have : (Nat.minFac n) % 2 = 1 := minFac_odd_of_odd hn_odd hn_ge_2
              clear h_minFac_sq h_minFac_prime h_minFac_dvd h_not_prime
              omega
            exact Nat.dvd_of_mod_eq_zero this
          have h_div := Nat.mul_div_cancel' h_even
          use (Nat.minFac n - 3) / 2
          clear h_minFac_sq h_minFac_prime h_minFac_dvd h_not_prime
          omega
        rcases h_exists_k with ⟨k, hk⟩
        have h_minFac_sq_mul : (Nat.minFac n) * (Nat.minFac n) ≤ n := by
          have h_sq : (Nat.minFac n) ^ 2 = (Nat.minFac n) * (Nat.minFac n) := by ring
          omega
        have h_exists_k_lt : ∃ k < 65, Nat.minFac n = 3 + 2 * k := by
          have h_sq : (3 + 2 * k) * (3 + 2 * k) ≤ 15727 := by
            have h_eq : 3 + 2 * k = Nat.minFac n := hk.symm
            have : (3 + 2 * k) * (3 + 2 * k) = (Nat.minFac n) * (Nat.minFac n) := by rw [h_eq]
            omega
          have h_k_lt : k < 65 := by
            by_contra hc
            have : 3 + 2 * k ≥ 133 := by omega
            have : (3 + 2 * k) * (3 + 2 * k) ≥ 17689 := by nlinarith
            omega
          refine ⟨k, h_k_lt, hk⟩
        have h_not_dvd := no_odd_divisor_of_has_odd_divisor_from_eq_false n 3 65 h (Nat.minFac n) h_minFac_ge_3 h_minFac_sq_mul h_exists_k_lt
        exact h_not_dvd h_minFac_dvd

def bst_all_prime : PrimeTree → Bool
  | .leaf => true
  | .node val l r => decide (val < 15728) && is_prime_custom val && bst_all_prime l && bst_all_prime r

lemma bst_contains_sound (n : ℕ) (t : PrimeTree) (h_all : bst_all_prime t = true) (h_mem : bst_contains n t = true) : n.Prime := by
  induction t with
  | leaf =>
    unfold bst_contains at h_mem
    contradiction
  | node val l r ih_l ih_r =>
    unfold bst_all_prime at h_all
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h_all
    rcases h_all with ⟨⟨⟨h_lt_15728, h_val⟩, h_l⟩, h_r⟩
    unfold bst_contains at h_mem
    split_ifs at h_mem with h_eq h_lt
    · rw [h_eq]
      have h_lt_val : val < 15728 := of_decide_eq_true h_lt_15728
      exact prime_of_is_prime_custom val h_lt_val h_val
    · exact ih_l h_l h_mem
    · exact ih_r h_r h_mem

theorem bst_safe : bst_all_prime bst = true := by decide

theorem is_prime_lookup_sound_bounded : ∀ n < 15728, is_prime_lookup n = true → n.Prime := by
  intro n hn hp
  have hp2 : bst_contains n bst = true := by
    unfold is_prime_lookup at hp
    rw [if_pos hn] at hp
    exact hp
  exact bst_contains_sound n bst bst_safe hp2

def goldbach_primes : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173
]

def goldbach_decidable (n : ℕ) : Bool :=
  goldbach_primes.any (fun p => is_prime_lookup p && decide (p < n) && is_prime_lookup (n - p))

lemma goldbach_of_decidable (n : ℕ) (h : goldbach_decidable n = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  have h1 : ∃ p ∈ goldbach_primes, (is_prime_lookup p && decide (p < n) && is_prime_lookup (n - p)) = true := by
    exact List.any_eq_true.mp h
  rcases h1 with ⟨p, hp_mem, hp_cond⟩
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff] at hp_cond
  rcases hp_cond with ⟨⟨hp_lookup, hp_lt⟩, hnp_lookup⟩
  have hp_prime : p.Prime := is_prime_lookup_sound_bounded p (lt_of_is_prime_lookup_eq_true p hp_lookup) hp_lookup
  have hnp_prime : (n - p).Prime := is_prime_lookup_sound_bounded (n - p) (lt_of_is_prime_lookup_eq_true (n - p) hnp_lookup) hnp_lookup
  use p, n - p
  refine ⟨hp_prime, hnp_prime, ?_⟩
  omega

def check_interval_fuel (fuel a b : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if b < a then true
    else if a == b then
      if 4 ≤ a && a % 2 == 0 then goldbach_decidable a else true
    else
      let mid := (a + b) / 2
      check_interval_fuel f a mid && check_interval_fuel f (mid + 1) b

lemma check_interval_fuel_sound (fuel : ℕ) (a b x : ℕ) (h : check_interval_fuel fuel a b = true)
    (hx1 : a ≤ x) (hx2 : x ≤ b) (h4 : 4 ≤ x) (heven : Even x) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ x = p + q := by
  induction fuel generalizing a b with
  | zero =>
    rw [check_interval_fuel] at h
    contradiction
  | succ f ih =>
    rw [check_interval_fuel] at h
    by_cases h1 : b < a
    · rw [if_pos h1] at h
      omega
    · rw [if_neg h1] at h
      by_cases h2 : a = b
      · have h2_b : (a == b) = true := beq_iff_eq.mpr h2
        rw [if_pos h2_b] at h
        have ha_eq : a = x := by omega
        rw [ha_eq] at h
        have h_cond_x : (decide (4 ≤ x) && (x % 2 == 0)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_iff]
          have hx2 : x % 2 = 0 := Nat.even_iff.mp heven
          rw [hx2]
          exact ⟨h4, rfl⟩
        rw [h_cond_x] at h
        exact goldbach_of_decidable x h
      · have h2_b : (a == b) = false := decide_eq_false h2
        have h2_b_ne : (a == b) ≠ true := by rw [h2_b]; decide
        rw [if_neg h2_b_ne] at h
        rw [Bool.and_eq_true] at h
        rcases h with ⟨h_left, h_right⟩
        let mid := (a + b) / 2
        by_cases hx_mid : x ≤ mid
        · exact ih a mid h_left hx1 hx_mid
        · have hx_gt : x ≥ mid + 1 := by omega
          exact ih (mid + 1) b h_right hx_gt hx2
theorem gold_h_dec_0 : check_interval_fuel 12 0 499 = true := by decide
theorem gold_h_dec_1 : check_interval_fuel 12 500 999 = true := by decide
theorem gold_h_dec_2 : check_interval_fuel 12 1000 1499 = true := by decide
theorem gold_h_dec_3 : check_interval_fuel 12 1500 1999 = true := by decide
theorem gold_h_dec_4 : check_interval_fuel 12 2000 2499 = true := by decide
theorem gold_h_dec_5 : check_interval_fuel 12 2500 2999 = true := by decide
theorem gold_h_dec_6 : check_interval_fuel 12 3000 3499 = true := by decide
theorem gold_h_dec_7 : check_interval_fuel 12 3500 3999 = true := by decide
theorem gold_h_dec_8 : check_interval_fuel 12 4000 4499 = true := by decide
theorem gold_h_dec_9 : check_interval_fuel 12 4500 4999 = true := by decide
theorem gold_h_dec_10 : check_interval_fuel 12 5000 5499 = true := by decide
theorem gold_h_dec_11 : check_interval_fuel 12 5500 5999 = true := by decide
theorem gold_h_dec_12 : check_interval_fuel 12 6000 6499 = true := by decide
theorem gold_h_dec_13 : check_interval_fuel 12 6500 6999 = true := by decide
theorem gold_h_dec_14 : check_interval_fuel 12 7000 7499 = true := by decide
theorem gold_h_dec_15 : check_interval_fuel 12 7500 7999 = true := by decide
theorem gold_h_dec_16 : check_interval_fuel 12 8000 8012 = true := by decide

lemma goldbach_of_core (hcore : a219055_core_conjecture) : goldbach_conjecture := by
  intro n hn heven
  by_cases hn_gt : n > 8012
  · have hpos : A219055 n > 0 := by
      apply hcore n
      left
      exact ⟨heven, hn_gt⟩
    rcases exists_of_A219055_even n heven hpos with ⟨q, hq_lt, _, hq_prime, _, hp_prime, _⟩
    use n - q, q
    refine ⟨hp_prime, hq_prime, ?_⟩
    omega
  · have hn_le : n ≤ 8012 := by omega
    by_cases hg_0 : n ≤ 499
    · exact check_interval_fuel_sound 12 0 499 n gold_h_dec_0 (by omega) hg_0 hn heven
    by_cases hg_1 : n ≤ 999
    · exact check_interval_fuel_sound 12 500 999 n gold_h_dec_1 (by omega) hg_1 hn heven
    by_cases hg_2 : n ≤ 1499
    · exact check_interval_fuel_sound 12 1000 1499 n gold_h_dec_2 (by omega) hg_2 hn heven
    by_cases hg_3 : n ≤ 1999
    · exact check_interval_fuel_sound 12 1500 1999 n gold_h_dec_3 (by omega) hg_3 hn heven
    by_cases hg_4 : n ≤ 2499
    · exact check_interval_fuel_sound 12 2000 2499 n gold_h_dec_4 (by omega) hg_4 hn heven
    by_cases hg_5 : n ≤ 2999
    · exact check_interval_fuel_sound 12 2500 2999 n gold_h_dec_5 (by omega) hg_5 hn heven
    by_cases hg_6 : n ≤ 3499
    · exact check_interval_fuel_sound 12 3000 3499 n gold_h_dec_6 (by omega) hg_6 hn heven
    by_cases hg_7 : n ≤ 3999
    · exact check_interval_fuel_sound 12 3500 3999 n gold_h_dec_7 (by omega) hg_7 hn heven
    by_cases hg_8 : n ≤ 4499
    · exact check_interval_fuel_sound 12 4000 4499 n gold_h_dec_8 (by omega) hg_8 hn heven
    by_cases hg_9 : n ≤ 4999
    · exact check_interval_fuel_sound 12 4500 4999 n gold_h_dec_9 (by omega) hg_9 hn heven
    by_cases hg_10 : n ≤ 5499
    · exact check_interval_fuel_sound 12 5000 5499 n gold_h_dec_10 (by omega) hg_10 hn heven
    by_cases hg_11 : n ≤ 5999
    · exact check_interval_fuel_sound 12 5500 5999 n gold_h_dec_11 (by omega) hg_11 hn heven
    by_cases hg_12 : n ≤ 6499
    · exact check_interval_fuel_sound 12 6000 6499 n gold_h_dec_12 (by omega) hg_12 hn heven
    by_cases hg_13 : n ≤ 6999
    · exact check_interval_fuel_sound 12 6500 6999 n gold_h_dec_13 (by omega) hg_13 hn heven
    by_cases hg_14 : n ≤ 7499
    · exact check_interval_fuel_sound 12 7000 7499 n gold_h_dec_14 (by omega) hg_14 hn heven
    by_cases hg_15 : n ≤ 7999
    · exact check_interval_fuel_sound 12 7500 7999 n gold_h_dec_15 (by omega) hg_15 hn heven
    exact check_interval_fuel_sound 12 8000 8012 n gold_h_dec_16 (by omega) (by omega) hn heven

def lemoine_primes : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173, 179, 181
]

def lemoine_decidable (n : ℕ) : Bool :=
  lemoine_primes.any (fun q => is_prime_lookup q && decide (2 * q < n) && is_prime_lookup (n - 2 * q))

lemma lemoine_of_decidable (n : ℕ) (h : lemoine_decidable n = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  have h1 : ∃ q ∈ lemoine_primes, (is_prime_lookup q && decide (2 * q < n) && is_prime_lookup (n - 2 * q)) = true := by
    exact List.any_eq_true.mp h
  rcases h1 with ⟨q, hq_mem, hq_cond⟩
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff] at hq_cond
  rcases hq_cond with ⟨⟨hq_lookup, hq_lt⟩, hnp_lookup⟩
  have hq_prime : q.Prime := is_prime_lookup_sound_bounded q (lt_of_is_prime_lookup_eq_true q hq_lookup) hq_lookup
  have hp_prime : (n - 2 * q).Prime := is_prime_lookup_sound_bounded (n - 2 * q) (lt_of_is_prime_lookup_eq_true (n - 2 * q) hnp_lookup) hnp_lookup
  use n - 2 * q, q
  refine ⟨hp_prime, hq_prime, ?_⟩
  omega

def check_lemoine_interval_fuel (fuel a b : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if b < a then true
    else if a == b then
      if 7 ≤ a && a % 2 == 1 then lemoine_decidable a else true
    else
      let mid := (a + b) / 2
      check_lemoine_interval_fuel f a mid && check_lemoine_interval_fuel f (mid + 1) b

lemma check_lemoine_interval_fuel_sound (fuel : ℕ) (a b x : ℕ) (h : check_lemoine_interval_fuel fuel a b = true)
    (hx1 : a ≤ x) (hx2 : x ≤ b) (h7 : 7 ≤ x) (hodd : Odd x) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ x = p + 2 * q := by
  induction fuel generalizing a b with
  | zero =>
    rw [check_lemoine_interval_fuel] at h
    contradiction
  | succ f ih =>
    rw [check_lemoine_interval_fuel] at h
    by_cases h1 : b < a
    · rw [if_pos h1] at h
      omega
    · rw [if_neg h1] at h
      by_cases h2 : a = b
      · have h2_b : (a == b) = true := beq_iff_eq.mpr h2
        rw [if_pos h2_b] at h
        have ha_eq : a = x := by omega
        rw [ha_eq] at h
        have h_cond_x : (decide (7 ≤ x) && (x % 2 == 1)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_iff]
          have hx2 : x % 2 = 1 := Nat.odd_iff.mp hodd
          rw [hx2]
          exact ⟨h7, rfl⟩
        rw [h_cond_x] at h
        exact lemoine_of_decidable x h
      · have h2_b : (a == b) = false := decide_eq_false h2
        have h2_b_ne : (a == b) ≠ true := by rw [h2_b]; decide
        rw [if_neg h2_b_ne] at h
        rw [Bool.and_eq_true] at h
        rcases h with ⟨h_left, h_right⟩
        let mid := (a + b) / 2
        by_cases hx_mid : x ≤ mid
        · exact ih a mid h_left hx1 hx_mid
        · have hx_gt : x ≥ mid + 1 := by omega
          exact ih (mid + 1) b h_right hx_gt hx2
theorem lemoine_h_dec_0 : check_lemoine_interval_fuel 12 0 499 = true := by decide
theorem lemoine_h_dec_1 : check_lemoine_interval_fuel 12 500 999 = true := by decide
theorem lemoine_h_dec_2 : check_lemoine_interval_fuel 12 1000 1499 = true := by decide
theorem lemoine_h_dec_3 : check_lemoine_interval_fuel 12 1500 1999 = true := by decide
theorem lemoine_h_dec_4 : check_lemoine_interval_fuel 12 2000 2499 = true := by decide
theorem lemoine_h_dec_5 : check_lemoine_interval_fuel 12 2500 2999 = true := by decide
theorem lemoine_h_dec_6 : check_lemoine_interval_fuel 12 3000 3499 = true := by decide
theorem lemoine_h_dec_7 : check_lemoine_interval_fuel 12 3500 3999 = true := by decide
theorem lemoine_h_dec_8 : check_lemoine_interval_fuel 12 4000 4499 = true := by decide
theorem lemoine_h_dec_9 : check_lemoine_interval_fuel 12 4500 4999 = true := by decide
theorem lemoine_h_dec_10 : check_lemoine_interval_fuel 12 5000 5499 = true := by decide
theorem lemoine_h_dec_11 : check_lemoine_interval_fuel 12 5500 5999 = true := by decide
theorem lemoine_h_dec_12 : check_lemoine_interval_fuel 12 6000 6499 = true := by decide
theorem lemoine_h_dec_13 : check_lemoine_interval_fuel 12 6500 6999 = true := by decide
theorem lemoine_h_dec_14 : check_lemoine_interval_fuel 12 7000 7499 = true := by decide
theorem lemoine_h_dec_15 : check_lemoine_interval_fuel 12 7500 7999 = true := by decide
theorem lemoine_h_dec_16 : check_lemoine_interval_fuel 12 8000 8499 = true := by decide
theorem lemoine_h_dec_17 : check_lemoine_interval_fuel 12 8500 8999 = true := by decide
theorem lemoine_h_dec_18 : check_lemoine_interval_fuel 12 9000 9499 = true := by decide
theorem lemoine_h_dec_19 : check_lemoine_interval_fuel 12 9500 9999 = true := by decide
theorem lemoine_h_dec_20 : check_lemoine_interval_fuel 12 10000 10499 = true := by decide
theorem lemoine_h_dec_21 : check_lemoine_interval_fuel 12 10500 10999 = true := by decide
theorem lemoine_h_dec_22 : check_lemoine_interval_fuel 12 11000 11499 = true := by decide
theorem lemoine_h_dec_23 : check_lemoine_interval_fuel 12 11500 11999 = true := by decide
theorem lemoine_h_dec_24 : check_lemoine_interval_fuel 12 12000 12499 = true := by decide
theorem lemoine_h_dec_25 : check_lemoine_interval_fuel 12 12500 12999 = true := by decide
theorem lemoine_h_dec_26 : check_lemoine_interval_fuel 12 13000 13499 = true := by decide
theorem lemoine_h_dec_27 : check_lemoine_interval_fuel 12 13500 13999 = true := by decide
theorem lemoine_h_dec_28 : check_lemoine_interval_fuel 12 14000 14499 = true := by decide
theorem lemoine_h_dec_29 : check_lemoine_interval_fuel 12 14500 14999 = true := by decide
theorem lemoine_h_dec_30 : check_lemoine_interval_fuel 12 15000 15499 = true := by decide
theorem lemoine_h_dec_31 : check_lemoine_interval_fuel 12 15500 15727 = true := by decide

lemma lemoine_of_core (hcore : a219055_core_conjecture) : lemoine_conjecture := by
  intro n hn hodd
  by_cases hn_gt : n > 15727
  · have hpos : A219055 n > 0 := by
      apply hcore n
      right
      exact ⟨hodd, hn_gt⟩
    rcases exists_of_A219055_odd n hodd hpos with ⟨q, hq_lt, h_3q, hq_prime, _, hp_prime, _⟩
    use n - 2 * q, q
    refine ⟨hp_prime, hq_prime, ?_⟩
    omega
  · have hn_le : n ≤ 15727 := by omega
    by_cases hg_0 : n ≤ 499
    · exact check_lemoine_interval_fuel_sound 12 0 499 n lemoine_h_dec_0 (by omega) hg_0 hn hodd
    by_cases hg_1 : n ≤ 999
    · exact check_lemoine_interval_fuel_sound 12 500 999 n lemoine_h_dec_1 (by omega) hg_1 hn hodd
    by_cases hg_2 : n ≤ 1499
    · exact check_lemoine_interval_fuel_sound 12 1000 1499 n lemoine_h_dec_2 (by omega) hg_2 hn hodd
    by_cases hg_3 : n ≤ 1999
    · exact check_lemoine_interval_fuel_sound 12 1500 1999 n lemoine_h_dec_3 (by omega) hg_3 hn hodd
    by_cases hg_4 : n ≤ 2499
    · exact check_lemoine_interval_fuel_sound 12 2000 2499 n lemoine_h_dec_4 (by omega) hg_4 hn hodd
    by_cases hg_5 : n ≤ 2999
    · exact check_lemoine_interval_fuel_sound 12 2500 2999 n lemoine_h_dec_5 (by omega) hg_5 hn hodd
    by_cases hg_6 : n ≤ 3499
    · exact check_lemoine_interval_fuel_sound 12 3000 3499 n lemoine_h_dec_6 (by omega) hg_6 hn hodd
    by_cases hg_7 : n ≤ 3999
    · exact check_lemoine_interval_fuel_sound 12 3500 3999 n lemoine_h_dec_7 (by omega) hg_7 hn hodd
    by_cases hg_8 : n ≤ 4499
    · exact check_lemoine_interval_fuel_sound 12 4000 4499 n lemoine_h_dec_8 (by omega) hg_8 hn hodd
    by_cases hg_9 : n ≤ 4999
    · exact check_lemoine_interval_fuel_sound 12 4500 4999 n lemoine_h_dec_9 (by omega) hg_9 hn hodd
    by_cases hg_10 : n ≤ 5499
    · exact check_lemoine_interval_fuel_sound 12 5000 5499 n lemoine_h_dec_10 (by omega) hg_10 hn hodd
    by_cases hg_11 : n ≤ 5999
    · exact check_lemoine_interval_fuel_sound 12 5500 5999 n lemoine_h_dec_11 (by omega) hg_11 hn hodd
    by_cases hg_12 : n ≤ 6499
    · exact check_lemoine_interval_fuel_sound 12 6000 6499 n lemoine_h_dec_12 (by omega) hg_12 hn hodd
    by_cases hg_13 : n ≤ 6999
    · exact check_lemoine_interval_fuel_sound 12 6500 6999 n lemoine_h_dec_13 (by omega) hg_13 hn hodd
    by_cases hg_14 : n ≤ 7499
    · exact check_lemoine_interval_fuel_sound 12 7000 7499 n lemoine_h_dec_14 (by omega) hg_14 hn hodd
    by_cases hg_15 : n ≤ 7999
    · exact check_lemoine_interval_fuel_sound 12 7500 7999 n lemoine_h_dec_15 (by omega) hg_15 hn hodd
    by_cases hg_16 : n ≤ 8499
    · exact check_lemoine_interval_fuel_sound 12 8000 8499 n lemoine_h_dec_16 (by omega) hg_16 hn hodd
    by_cases hg_17 : n ≤ 8999
    · exact check_lemoine_interval_fuel_sound 12 8500 8999 n lemoine_h_dec_17 (by omega) hg_17 hn hodd
    by_cases hg_18 : n ≤ 9499
    · exact check_lemoine_interval_fuel_sound 12 9000 9499 n lemoine_h_dec_18 (by omega) hg_18 hn hodd
    by_cases hg_19 : n ≤ 9999
    · exact check_lemoine_interval_fuel_sound 12 9500 9999 n lemoine_h_dec_19 (by omega) hg_19 hn hodd
    by_cases hg_20 : n ≤ 10499
    · exact check_lemoine_interval_fuel_sound 12 10000 10499 n lemoine_h_dec_20 (by omega) hg_20 hn hodd
    by_cases hg_21 : n ≤ 10999
    · exact check_lemoine_interval_fuel_sound 12 10500 10999 n lemoine_h_dec_21 (by omega) hg_21 hn hodd
    by_cases hg_22 : n ≤ 11499
    · exact check_lemoine_interval_fuel_sound 12 11000 11499 n lemoine_h_dec_22 (by omega) hg_22 hn hodd
    by_cases hg_23 : n ≤ 11999
    · exact check_lemoine_interval_fuel_sound 12 11500 11999 n lemoine_h_dec_23 (by omega) hg_23 hn hodd
    by_cases hg_24 : n ≤ 12499
    · exact check_lemoine_interval_fuel_sound 12 12000 12499 n lemoine_h_dec_24 (by omega) hg_24 hn hodd
    by_cases hg_25 : n ≤ 12999
    · exact check_lemoine_interval_fuel_sound 12 12500 12999 n lemoine_h_dec_25 (by omega) hg_25 hn hodd
    by_cases hg_26 : n ≤ 13499
    · exact check_lemoine_interval_fuel_sound 12 13000 13499 n lemoine_h_dec_26 (by omega) hg_26 hn hodd
    by_cases hg_27 : n ≤ 13999
    · exact check_lemoine_interval_fuel_sound 12 13500 13999 n lemoine_h_dec_27 (by omega) hg_27 hn hodd
    by_cases hg_28 : n ≤ 14499
    · exact check_lemoine_interval_fuel_sound 12 14000 14499 n lemoine_h_dec_28 (by omega) hg_28 hn hodd
    by_cases hg_29 : n ≤ 14999
    · exact check_lemoine_interval_fuel_sound 12 14500 14999 n lemoine_h_dec_29 (by omega) hg_29 hn hodd
    by_cases hg_30 : n ≤ 15499
    · exact check_lemoine_interval_fuel_sound 12 15000 15499 n lemoine_h_dec_30 (by omega) hg_30 hn hodd
    exact check_lemoine_interval_fuel_sound 12 15500 15727 n lemoine_h_dec_31 (by omega) (by omega) hn hodd

lemma six_prime_gap_of_core (hcore : a219055_core_conjecture) : six_prime_gap_conjecture := by
  rw [six_prime_gap_conjecture, Set.infinite_iff_exists_gt]
  intro M
  let n := 2 * M + 8014
  have hn_even : Even n := ⟨M + 4007, by omega⟩
  have hn_8012 : 8012 < n := by omega
  have h_core_pos : A219055 n > 0 := by
    apply hcore n
    left
    exact ⟨hn_even, hn_8012⟩
  rcases exists_of_A219055_even n hn_even h_core_pos with ⟨q, hq_lt, _, hq_prime, hq6_prime, hp_prime, hp6_prime⟩
  by_cases hq : M < q
  · use q
    refine ⟨⟨hq_prime, hq6_prime⟩, hq⟩
  · have hq_le : q ≤ M := by omega
    use n - q - 6
    have hp6_cond1 : (n - q - 6).Prime := hp6_prime
    have hp6_cond2 : (n - q - 6 + 6).Prime := by
      have : n - q - 6 + 6 = n - q := by omega
      rw [this]
      exact hp_prime
    refine ⟨⟨hp6_cond1, hp6_cond2⟩, ?_⟩
    omega

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture := by
  intro hcore
  refine ⟨goldbach_of_core hcore, lemoine_of_core hcore, six_prime_gap_of_core hcore⟩
