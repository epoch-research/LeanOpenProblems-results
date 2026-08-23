import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000
set_option maxRecDepth 10000

open Nat Finset

/--
A219055: Number of ways to write $n = p+q(3-(-1)^n)/2$ with $p>q$ and $p, q, p-6, q+6$ all prime.
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

private def rvld (c n : ℕ) : List ℕ → Prop
  | [] => True
  | q :: qs => (n - c*q).Prime ∧ q.Prime ∧ n = (n-c*q)+c*q ∧ rvld c (n+2) qs

private theorem rvc {c n q : ℕ} {qs : List ℕ} (hp : (n-c*q).Prime) (hq : q.Prime)
    (ht : rvld c (n+2) qs) : rvld c n (q::qs) := by
  refine ⟨hp, hq, ?_, ht⟩
  have := hp.two_le
  omega

private theorem rvld_ex {c n k : ℕ} {qs : List ℕ} (hv : rvld c n qs) (hk : k < qs.length) :
    ∃ q, (n+2*k-c*q).Prime ∧ q.Prime ∧ n+2*k=(n+2*k-c*q)+c*q := by
  induction k generalizing n qs with
  | zero =>
      cases qs with
      | nil => simp at hk
      | cons q qs =>
          simp only [rvld] at hv
          exact ⟨q, by simpa using hv.1, hv.2.1, by simpa using hv.2.2.1⟩
  | succ k ih =>
      cases qs with
      | nil => simp at hk
      | cons q qs =>
          simp only [rvld] at hv
          have hk' : k < qs.length := by simpa using hk
          obtain ⟨r, hp, hr, heq⟩ := ih hv.2.2.2 hk'
          refine ⟨r, ?_, hr, ?_⟩
          · convert hp using 1 <;> omega
          · omega

private theorem p2 : Nat.Prime 2 := by norm_num
private theorem p3 : Nat.Prime 3 := by norm_num
private theorem p5 : Nat.Prime 5 := by norm_num
private theorem p7 : Nat.Prime 7 := by norm_num
private theorem p11 : Nat.Prime 11 := by norm_num
private theorem p13 : Nat.Prime 13 := by norm_num
private theorem p17 : Nat.Prime 17 := by norm_num
private theorem p19 : Nat.Prime 19 := by norm_num
private theorem p23 : Nat.Prime 23 := by norm_num
private theorem p29 : Nat.Prime 29 := by norm_num
private theorem p31 : Nat.Prime 31 := by norm_num
private theorem p37 : Nat.Prime 37 := by norm_num
private theorem p41 : Nat.Prime 41 := by norm_num
private theorem p43 : Nat.Prime 43 := by norm_num
private theorem p47 : Nat.Prime 47 := by norm_num
private theorem p53 : Nat.Prime 53 := by norm_num
private theorem p59 : Nat.Prime 59 := by norm_num
private theorem p61 : Nat.Prime 61 := by norm_num
private theorem p67 : Nat.Prime 67 := by norm_num
private theorem p71 : Nat.Prime 71 := by norm_num
private theorem p73 : Nat.Prime 73 := by norm_num
private theorem p79 : Nat.Prime 79 := by norm_num
private theorem p83 : Nat.Prime 83 := by norm_num
private theorem p89 : Nat.Prime 89 := by norm_num
private theorem p97 : Nat.Prime 97 := by norm_num
private theorem p101 : Nat.Prime 101 := by norm_num
private theorem p103 : Nat.Prime 103 := by norm_num
private theorem p107 : Nat.Prime 107 := by norm_num
private theorem p109 : Nat.Prime 109 := by norm_num
private theorem p113 : Nat.Prime 113 := by norm_num
private theorem p127 : Nat.Prime 127 := by norm_num
private theorem p131 : Nat.Prime 131 := by norm_num
private theorem p137 : Nat.Prime 137 := by norm_num
private theorem p139 : Nat.Prime 139 := by norm_num
private theorem p149 : Nat.Prime 149 := by norm_num
private theorem p151 : Nat.Prime 151 := by norm_num
private theorem p157 : Nat.Prime 157 := by norm_num
private theorem p163 : Nat.Prime 163 := by norm_num
private theorem p167 : Nat.Prime 167 := by norm_num
private theorem p173 : Nat.Prime 173 := by norm_num
private theorem p179 : Nat.Prime 179 := by norm_num
private theorem p181 : Nat.Prime 181 := by norm_num
private theorem p191 : Nat.Prime 191 := by norm_num
private theorem p193 : Nat.Prime 193 := by norm_num
private theorem p197 : Nat.Prime 197 := by norm_num
private theorem p199 : Nat.Prime 199 := by norm_num
private theorem p211 : Nat.Prime 211 := by norm_num
private theorem p223 : Nat.Prime 223 := by norm_num
private theorem p227 : Nat.Prime 227 := by norm_num
private theorem p229 : Nat.Prime 229 := by norm_num
private theorem p233 : Nat.Prime 233 := by norm_num
private theorem p239 : Nat.Prime 239 := by norm_num
private theorem p241 : Nat.Prime 241 := by norm_num
private theorem p251 : Nat.Prime 251 := by norm_num
private theorem p257 : Nat.Prime 257 := by norm_num
private theorem p263 : Nat.Prime 263 := by norm_num
private theorem p269 : Nat.Prime 269 := by norm_num
private theorem p271 : Nat.Prime 271 := by norm_num
private theorem p277 : Nat.Prime 277 := by norm_num
private theorem p281 : Nat.Prime 281 := by norm_num
private theorem p283 : Nat.Prime 283 := by norm_num
private theorem p293 : Nat.Prime 293 := by norm_num
private theorem p307 : Nat.Prime 307 := by norm_num
private theorem p311 : Nat.Prime 311 := by norm_num
private theorem p313 : Nat.Prime 313 := by norm_num
private theorem p317 : Nat.Prime 317 := by norm_num
private theorem p331 : Nat.Prime 331 := by norm_num
private theorem p337 : Nat.Prime 337 := by norm_num
private theorem p347 : Nat.Prime 347 := by norm_num
private theorem p349 : Nat.Prime 349 := by norm_num
private theorem p353 : Nat.Prime 353 := by norm_num
private theorem p359 : Nat.Prime 359 := by norm_num
private theorem p367 : Nat.Prime 367 := by norm_num
private theorem p373 : Nat.Prime 373 := by norm_num
private theorem p379 : Nat.Prime 379 := by norm_num
private theorem p383 : Nat.Prime 383 := by norm_num
private theorem p389 : Nat.Prime 389 := by norm_num
private theorem p397 : Nat.Prime 397 := by norm_num
private theorem p401 : Nat.Prime 401 := by norm_num
private theorem p409 : Nat.Prime 409 := by norm_num
private theorem p419 : Nat.Prime 419 := by norm_num
private theorem p421 : Nat.Prime 421 := by norm_num
private theorem p431 : Nat.Prime 431 := by norm_num
private theorem p433 : Nat.Prime 433 := by norm_num
private theorem p439 : Nat.Prime 439 := by norm_num
private theorem p443 : Nat.Prime 443 := by norm_num
private theorem p449 : Nat.Prime 449 := by norm_num
private theorem p457 : Nat.Prime 457 := by norm_num
private theorem p461 : Nat.Prime 461 := by norm_num
private theorem p463 : Nat.Prime 463 := by norm_num
private theorem p467 : Nat.Prime 467 := by norm_num
private theorem p479 : Nat.Prime 479 := by norm_num
private theorem p487 : Nat.Prime 487 := by norm_num
private theorem p491 : Nat.Prime 491 := by norm_num
private theorem p499 : Nat.Prime 499 := by norm_num
private theorem p503 : Nat.Prime 503 := by norm_num
private theorem p509 : Nat.Prime 509 := by norm_num
private theorem p521 : Nat.Prime 521 := by norm_num
private theorem p523 : Nat.Prime 523 := by norm_num
private theorem p541 : Nat.Prime 541 := by norm_num
private theorem p547 : Nat.Prime 547 := by norm_num
private theorem p557 : Nat.Prime 557 := by norm_num
private theorem p563 : Nat.Prime 563 := by norm_num
private theorem p569 : Nat.Prime 569 := by norm_num
private theorem p571 : Nat.Prime 571 := by norm_num
private theorem p577 : Nat.Prime 577 := by norm_num
private theorem p587 : Nat.Prime 587 := by norm_num
private theorem p593 : Nat.Prime 593 := by norm_num
private theorem p599 : Nat.Prime 599 := by norm_num
private theorem p601 : Nat.Prime 601 := by norm_num
private theorem p607 : Nat.Prime 607 := by norm_num
private theorem p613 : Nat.Prime 613 := by norm_num
private theorem p617 : Nat.Prime 617 := by norm_num
private theorem p619 : Nat.Prime 619 := by norm_num
private theorem p631 : Nat.Prime 631 := by norm_num
private theorem p641 : Nat.Prime 641 := by norm_num
private theorem p643 : Nat.Prime 643 := by norm_num
private theorem p647 : Nat.Prime 647 := by norm_num
private theorem p653 : Nat.Prime 653 := by norm_num
private theorem p659 : Nat.Prime 659 := by norm_num
private theorem p661 : Nat.Prime 661 := by norm_num
private theorem p673 : Nat.Prime 673 := by norm_num
private theorem p677 : Nat.Prime 677 := by norm_num
private theorem p683 : Nat.Prime 683 := by norm_num
private theorem p691 : Nat.Prime 691 := by norm_num
private theorem p701 : Nat.Prime 701 := by norm_num
private theorem p709 : Nat.Prime 709 := by norm_num
private theorem p719 : Nat.Prime 719 := by norm_num
private theorem p727 : Nat.Prime 727 := by norm_num
private theorem p733 : Nat.Prime 733 := by norm_num
private theorem p739 : Nat.Prime 739 := by norm_num
private theorem p743 : Nat.Prime 743 := by norm_num
private theorem p751 : Nat.Prime 751 := by norm_num
private theorem p757 : Nat.Prime 757 := by norm_num
private theorem p761 : Nat.Prime 761 := by norm_num
private theorem p769 : Nat.Prime 769 := by norm_num
private theorem p773 : Nat.Prime 773 := by norm_num
private theorem p787 : Nat.Prime 787 := by norm_num
private theorem p797 : Nat.Prime 797 := by norm_num
private theorem p809 : Nat.Prime 809 := by norm_num
private theorem p811 : Nat.Prime 811 := by norm_num
private theorem p821 : Nat.Prime 821 := by norm_num
private theorem p823 : Nat.Prime 823 := by norm_num
private theorem p827 : Nat.Prime 827 := by norm_num
private theorem p829 : Nat.Prime 829 := by norm_num
private theorem p839 : Nat.Prime 839 := by norm_num
private theorem p853 : Nat.Prime 853 := by norm_num
private theorem p857 : Nat.Prime 857 := by norm_num
private theorem p859 : Nat.Prime 859 := by norm_num
private theorem p863 : Nat.Prime 863 := by norm_num
private theorem p877 : Nat.Prime 877 := by norm_num
private theorem p881 : Nat.Prime 881 := by norm_num
private theorem p883 : Nat.Prime 883 := by norm_num
private theorem p887 : Nat.Prime 887 := by norm_num
private theorem p907 : Nat.Prime 907 := by norm_num
private theorem p911 : Nat.Prime 911 := by norm_num
private theorem p919 : Nat.Prime 919 := by norm_num
private theorem p929 : Nat.Prime 929 := by norm_num
private theorem p937 : Nat.Prime 937 := by norm_num
private theorem p941 : Nat.Prime 941 := by norm_num
private theorem p947 : Nat.Prime 947 := by norm_num
private theorem p953 : Nat.Prime 953 := by norm_num
private theorem p967 : Nat.Prime 967 := by norm_num
private theorem p971 : Nat.Prime 971 := by norm_num
private theorem p977 : Nat.Prime 977 := by norm_num
private theorem p983 : Nat.Prime 983 := by norm_num
private theorem p991 : Nat.Prime 991 := by norm_num
private theorem p997 : Nat.Prime 997 := by norm_num
private theorem p1009 : Nat.Prime 1009 := by norm_num
private theorem p1013 : Nat.Prime 1013 := by norm_num
private theorem p1019 : Nat.Prime 1019 := by norm_num
private theorem p1021 : Nat.Prime 1021 := by norm_num
private theorem p1031 : Nat.Prime 1031 := by norm_num
private theorem p1033 : Nat.Prime 1033 := by norm_num
private theorem p1039 : Nat.Prime 1039 := by norm_num
private theorem p1049 : Nat.Prime 1049 := by norm_num
private theorem p1051 : Nat.Prime 1051 := by norm_num
private theorem p1061 : Nat.Prime 1061 := by norm_num
private theorem p1063 : Nat.Prime 1063 := by norm_num
private theorem p1069 : Nat.Prime 1069 := by norm_num
private theorem p1087 : Nat.Prime 1087 := by norm_num
private theorem p1091 : Nat.Prime 1091 := by norm_num
private theorem p1093 : Nat.Prime 1093 := by norm_num
private theorem p1097 : Nat.Prime 1097 := by norm_num
private theorem p1103 : Nat.Prime 1103 := by norm_num
private theorem p1109 : Nat.Prime 1109 := by norm_num
private theorem p1117 : Nat.Prime 1117 := by norm_num
private theorem p1123 : Nat.Prime 1123 := by norm_num
private theorem p1129 : Nat.Prime 1129 := by norm_num
private theorem p1151 : Nat.Prime 1151 := by norm_num
private theorem p1153 : Nat.Prime 1153 := by norm_num
private theorem p1163 : Nat.Prime 1163 := by norm_num
private theorem p1171 : Nat.Prime 1171 := by norm_num
private theorem p1181 : Nat.Prime 1181 := by norm_num
private theorem p1187 : Nat.Prime 1187 := by norm_num
private theorem p1193 : Nat.Prime 1193 := by norm_num
private theorem p1201 : Nat.Prime 1201 := by norm_num
private theorem p1213 : Nat.Prime 1213 := by norm_num
private theorem p1217 : Nat.Prime 1217 := by norm_num
private theorem p1223 : Nat.Prime 1223 := by norm_num
private theorem p1229 : Nat.Prime 1229 := by norm_num
private theorem p1231 : Nat.Prime 1231 := by norm_num
private theorem p1237 : Nat.Prime 1237 := by norm_num
private theorem p1249 : Nat.Prime 1249 := by norm_num
private theorem p1259 : Nat.Prime 1259 := by norm_num
private theorem p1277 : Nat.Prime 1277 := by norm_num
private theorem p1279 : Nat.Prime 1279 := by norm_num
private theorem p1283 : Nat.Prime 1283 := by norm_num
private theorem p1289 : Nat.Prime 1289 := by norm_num
private theorem p1291 : Nat.Prime 1291 := by norm_num
private theorem p1297 : Nat.Prime 1297 := by norm_num
private theorem p1301 : Nat.Prime 1301 := by norm_num
private theorem p1303 : Nat.Prime 1303 := by norm_num
private theorem p1307 : Nat.Prime 1307 := by norm_num
private theorem p1319 : Nat.Prime 1319 := by norm_num
private theorem p1321 : Nat.Prime 1321 := by norm_num
private theorem p1327 : Nat.Prime 1327 := by norm_num
private theorem p1361 : Nat.Prime 1361 := by norm_num
private theorem p1367 : Nat.Prime 1367 := by norm_num
private theorem p1373 : Nat.Prime 1373 := by norm_num
private theorem p1381 : Nat.Prime 1381 := by norm_num
private theorem p1399 : Nat.Prime 1399 := by norm_num
private theorem p1409 : Nat.Prime 1409 := by norm_num
private theorem p1423 : Nat.Prime 1423 := by norm_num
private theorem p1427 : Nat.Prime 1427 := by norm_num
private theorem p1429 : Nat.Prime 1429 := by norm_num
private theorem p1433 : Nat.Prime 1433 := by norm_num
private theorem p1439 : Nat.Prime 1439 := by norm_num
private theorem p1447 : Nat.Prime 1447 := by norm_num
private theorem p1451 : Nat.Prime 1451 := by norm_num
private theorem p1453 : Nat.Prime 1453 := by norm_num
private theorem p1459 : Nat.Prime 1459 := by norm_num
private theorem p1471 : Nat.Prime 1471 := by norm_num
private theorem p1481 : Nat.Prime 1481 := by norm_num
private theorem p1483 : Nat.Prime 1483 := by norm_num
private theorem p1487 : Nat.Prime 1487 := by norm_num
private theorem p1489 : Nat.Prime 1489 := by norm_num
private theorem p1493 : Nat.Prime 1493 := by norm_num
private theorem p1499 : Nat.Prime 1499 := by norm_num
private theorem p1511 : Nat.Prime 1511 := by norm_num
private theorem p1523 : Nat.Prime 1523 := by norm_num
private theorem p1531 : Nat.Prime 1531 := by norm_num
private theorem p1543 : Nat.Prime 1543 := by norm_num
private theorem p1549 : Nat.Prime 1549 := by norm_num
private theorem p1553 : Nat.Prime 1553 := by norm_num
private theorem p1559 : Nat.Prime 1559 := by norm_num
private theorem p1567 : Nat.Prime 1567 := by norm_num
private theorem p1571 : Nat.Prime 1571 := by norm_num
private theorem p1579 : Nat.Prime 1579 := by norm_num
private theorem p1583 : Nat.Prime 1583 := by norm_num
private theorem p1597 : Nat.Prime 1597 := by norm_num
private theorem p1601 : Nat.Prime 1601 := by norm_num
private theorem p1607 : Nat.Prime 1607 := by norm_num
private theorem p1609 : Nat.Prime 1609 := by norm_num
private theorem p1613 : Nat.Prime 1613 := by norm_num
private theorem p1619 : Nat.Prime 1619 := by norm_num
private theorem p1621 : Nat.Prime 1621 := by norm_num
private theorem p1627 : Nat.Prime 1627 := by norm_num
private theorem p1637 : Nat.Prime 1637 := by norm_num
private theorem p1657 : Nat.Prime 1657 := by norm_num
private theorem p1663 : Nat.Prime 1663 := by norm_num
private theorem p1667 : Nat.Prime 1667 := by norm_num
private theorem p1669 : Nat.Prime 1669 := by norm_num
private theorem p1693 : Nat.Prime 1693 := by norm_num
private theorem p1697 : Nat.Prime 1697 := by norm_num
private theorem p1699 : Nat.Prime 1699 := by norm_num
private theorem p1709 : Nat.Prime 1709 := by norm_num
private theorem p1721 : Nat.Prime 1721 := by norm_num
private theorem p1723 : Nat.Prime 1723 := by norm_num
private theorem p1733 : Nat.Prime 1733 := by norm_num
private theorem p1741 : Nat.Prime 1741 := by norm_num
private theorem p1747 : Nat.Prime 1747 := by norm_num
private theorem p1753 : Nat.Prime 1753 := by norm_num
private theorem p1759 : Nat.Prime 1759 := by norm_num
private theorem p1777 : Nat.Prime 1777 := by norm_num
private theorem p1783 : Nat.Prime 1783 := by norm_num
private theorem p1787 : Nat.Prime 1787 := by norm_num
private theorem p1789 : Nat.Prime 1789 := by norm_num
private theorem p1801 : Nat.Prime 1801 := by norm_num
private theorem p1811 : Nat.Prime 1811 := by norm_num
private theorem p1823 : Nat.Prime 1823 := by norm_num
private theorem p1831 : Nat.Prime 1831 := by norm_num
private theorem p1847 : Nat.Prime 1847 := by norm_num
private theorem p1861 : Nat.Prime 1861 := by norm_num
private theorem p1867 : Nat.Prime 1867 := by norm_num
private theorem p1871 : Nat.Prime 1871 := by norm_num
private theorem p1873 : Nat.Prime 1873 := by norm_num
private theorem p1877 : Nat.Prime 1877 := by norm_num
private theorem p1879 : Nat.Prime 1879 := by norm_num
private theorem p1889 : Nat.Prime 1889 := by norm_num
private theorem p1901 : Nat.Prime 1901 := by norm_num
private theorem p1907 : Nat.Prime 1907 := by norm_num
private theorem p1913 : Nat.Prime 1913 := by norm_num
private theorem p1931 : Nat.Prime 1931 := by norm_num
private theorem p1933 : Nat.Prime 1933 := by norm_num
private theorem p1949 : Nat.Prime 1949 := by norm_num
private theorem p1951 : Nat.Prime 1951 := by norm_num
private theorem p1973 : Nat.Prime 1973 := by norm_num
private theorem p1979 : Nat.Prime 1979 := by norm_num
private theorem p1987 : Nat.Prime 1987 := by norm_num
private theorem p1993 : Nat.Prime 1993 := by norm_num
private theorem p1997 : Nat.Prime 1997 := by norm_num
private theorem p1999 : Nat.Prime 1999 := by norm_num
private theorem p2003 : Nat.Prime 2003 := by norm_num
private theorem p2011 : Nat.Prime 2011 := by norm_num
private theorem p2017 : Nat.Prime 2017 := by norm_num
private theorem p2027 : Nat.Prime 2027 := by norm_num
private theorem p2029 : Nat.Prime 2029 := by norm_num
private theorem p2039 : Nat.Prime 2039 := by norm_num
private theorem p2053 : Nat.Prime 2053 := by norm_num
private theorem p2063 : Nat.Prime 2063 := by norm_num
private theorem p2069 : Nat.Prime 2069 := by norm_num
private theorem p2081 : Nat.Prime 2081 := by norm_num
private theorem p2083 : Nat.Prime 2083 := by norm_num
private theorem p2087 : Nat.Prime 2087 := by norm_num
private theorem p2089 : Nat.Prime 2089 := by norm_num
private theorem p2099 : Nat.Prime 2099 := by norm_num
private theorem p2111 : Nat.Prime 2111 := by norm_num
private theorem p2113 : Nat.Prime 2113 := by norm_num
private theorem p2129 : Nat.Prime 2129 := by norm_num
private theorem p2131 : Nat.Prime 2131 := by norm_num
private theorem p2137 : Nat.Prime 2137 := by norm_num
private theorem p2141 : Nat.Prime 2141 := by norm_num
private theorem p2143 : Nat.Prime 2143 := by norm_num
private theorem p2153 : Nat.Prime 2153 := by norm_num
private theorem p2161 : Nat.Prime 2161 := by norm_num
private theorem p2179 : Nat.Prime 2179 := by norm_num
private theorem p2203 : Nat.Prime 2203 := by norm_num
private theorem p2207 : Nat.Prime 2207 := by norm_num
private theorem p2213 : Nat.Prime 2213 := by norm_num
private theorem p2221 : Nat.Prime 2221 := by norm_num
private theorem p2237 : Nat.Prime 2237 := by norm_num
private theorem p2239 : Nat.Prime 2239 := by norm_num
private theorem p2243 : Nat.Prime 2243 := by norm_num
private theorem p2251 : Nat.Prime 2251 := by norm_num
private theorem p2267 : Nat.Prime 2267 := by norm_num
private theorem p2269 : Nat.Prime 2269 := by norm_num
private theorem p2273 : Nat.Prime 2273 := by norm_num
private theorem p2281 : Nat.Prime 2281 := by norm_num
private theorem p2287 : Nat.Prime 2287 := by norm_num
private theorem p2293 : Nat.Prime 2293 := by norm_num
private theorem p2297 : Nat.Prime 2297 := by norm_num
private theorem p2309 : Nat.Prime 2309 := by norm_num
private theorem p2311 : Nat.Prime 2311 := by norm_num
private theorem p2333 : Nat.Prime 2333 := by norm_num
private theorem p2339 : Nat.Prime 2339 := by norm_num
private theorem p2341 : Nat.Prime 2341 := by norm_num
private theorem p2347 : Nat.Prime 2347 := by norm_num
private theorem p2351 : Nat.Prime 2351 := by norm_num
private theorem p2357 : Nat.Prime 2357 := by norm_num
private theorem p2371 : Nat.Prime 2371 := by norm_num
private theorem p2377 : Nat.Prime 2377 := by norm_num
private theorem p2381 : Nat.Prime 2381 := by norm_num
private theorem p2383 : Nat.Prime 2383 := by norm_num
private theorem p2389 : Nat.Prime 2389 := by norm_num
private theorem p2393 : Nat.Prime 2393 := by norm_num
private theorem p2399 : Nat.Prime 2399 := by norm_num
private theorem p2411 : Nat.Prime 2411 := by norm_num
private theorem p2417 : Nat.Prime 2417 := by norm_num
private theorem p2423 : Nat.Prime 2423 := by norm_num
private theorem p2437 : Nat.Prime 2437 := by norm_num
private theorem p2441 : Nat.Prime 2441 := by norm_num
private theorem p2447 : Nat.Prime 2447 := by norm_num
private theorem p2459 : Nat.Prime 2459 := by norm_num
private theorem p2467 : Nat.Prime 2467 := by norm_num
private theorem p2473 : Nat.Prime 2473 := by norm_num
private theorem p2477 : Nat.Prime 2477 := by norm_num
private theorem p2503 : Nat.Prime 2503 := by norm_num
private theorem p2521 : Nat.Prime 2521 := by norm_num
private theorem p2531 : Nat.Prime 2531 := by norm_num
private theorem p2539 : Nat.Prime 2539 := by norm_num
private theorem p2543 : Nat.Prime 2543 := by norm_num
private theorem p2549 : Nat.Prime 2549 := by norm_num
private theorem p2551 : Nat.Prime 2551 := by norm_num
private theorem p2557 : Nat.Prime 2557 := by norm_num
private theorem p2579 : Nat.Prime 2579 := by norm_num
private theorem p2591 : Nat.Prime 2591 := by norm_num
private theorem p2593 : Nat.Prime 2593 := by norm_num
private theorem p2609 : Nat.Prime 2609 := by norm_num
private theorem p2617 : Nat.Prime 2617 := by norm_num
private theorem p2621 : Nat.Prime 2621 := by norm_num
private theorem p2633 : Nat.Prime 2633 := by norm_num
private theorem p2647 : Nat.Prime 2647 := by norm_num
private theorem p2657 : Nat.Prime 2657 := by norm_num
private theorem p2659 : Nat.Prime 2659 := by norm_num
private theorem p2663 : Nat.Prime 2663 := by norm_num
private theorem p2671 : Nat.Prime 2671 := by norm_num
private theorem p2677 : Nat.Prime 2677 := by norm_num
private theorem p2683 : Nat.Prime 2683 := by norm_num
private theorem p2687 : Nat.Prime 2687 := by norm_num
private theorem p2689 : Nat.Prime 2689 := by norm_num
private theorem p2693 : Nat.Prime 2693 := by norm_num
private theorem p2699 : Nat.Prime 2699 := by norm_num
private theorem p2707 : Nat.Prime 2707 := by norm_num
private theorem p2711 : Nat.Prime 2711 := by norm_num
private theorem p2713 : Nat.Prime 2713 := by norm_num
private theorem p2719 : Nat.Prime 2719 := by norm_num
private theorem p2729 : Nat.Prime 2729 := by norm_num
private theorem p2731 : Nat.Prime 2731 := by norm_num
private theorem p2741 : Nat.Prime 2741 := by norm_num
private theorem p2749 : Nat.Prime 2749 := by norm_num
private theorem p2753 : Nat.Prime 2753 := by norm_num
private theorem p2767 : Nat.Prime 2767 := by norm_num
private theorem p2777 : Nat.Prime 2777 := by norm_num
private theorem p2789 : Nat.Prime 2789 := by norm_num
private theorem p2791 : Nat.Prime 2791 := by norm_num
private theorem p2797 : Nat.Prime 2797 := by norm_num
private theorem p2801 : Nat.Prime 2801 := by norm_num
private theorem p2803 : Nat.Prime 2803 := by norm_num
private theorem p2819 : Nat.Prime 2819 := by norm_num
private theorem p2833 : Nat.Prime 2833 := by norm_num
private theorem p2837 : Nat.Prime 2837 := by norm_num
private theorem p2843 : Nat.Prime 2843 := by norm_num
private theorem p2851 : Nat.Prime 2851 := by norm_num
private theorem p2857 : Nat.Prime 2857 := by norm_num
private theorem p2861 : Nat.Prime 2861 := by norm_num
private theorem p2879 : Nat.Prime 2879 := by norm_num
private theorem p2887 : Nat.Prime 2887 := by norm_num
private theorem p2897 : Nat.Prime 2897 := by norm_num
private theorem p2903 : Nat.Prime 2903 := by norm_num
private theorem p2909 : Nat.Prime 2909 := by norm_num
private theorem p2917 : Nat.Prime 2917 := by norm_num
private theorem p2927 : Nat.Prime 2927 := by norm_num
private theorem p2939 : Nat.Prime 2939 := by norm_num
private theorem p2953 : Nat.Prime 2953 := by norm_num
private theorem p2957 : Nat.Prime 2957 := by norm_num
private theorem p2963 : Nat.Prime 2963 := by norm_num
private theorem p2969 : Nat.Prime 2969 := by norm_num
private theorem p2971 : Nat.Prime 2971 := by norm_num
private theorem p2999 : Nat.Prime 2999 := by norm_num
private theorem p3001 : Nat.Prime 3001 := by norm_num
private theorem p3011 : Nat.Prime 3011 := by norm_num
private theorem p3019 : Nat.Prime 3019 := by norm_num
private theorem p3023 : Nat.Prime 3023 := by norm_num
private theorem p3037 : Nat.Prime 3037 := by norm_num
private theorem p3041 : Nat.Prime 3041 := by norm_num
private theorem p3049 : Nat.Prime 3049 := by norm_num
private theorem p3061 : Nat.Prime 3061 := by norm_num
private theorem p3067 : Nat.Prime 3067 := by norm_num
private theorem p3079 : Nat.Prime 3079 := by norm_num
private theorem p3083 : Nat.Prime 3083 := by norm_num
private theorem p3089 : Nat.Prime 3089 := by norm_num
private theorem p3109 : Nat.Prime 3109 := by norm_num
private theorem p3119 : Nat.Prime 3119 := by norm_num
private theorem p3121 : Nat.Prime 3121 := by norm_num
private theorem p3137 : Nat.Prime 3137 := by norm_num
private theorem p3163 : Nat.Prime 3163 := by norm_num
private theorem p3167 : Nat.Prime 3167 := by norm_num
private theorem p3169 : Nat.Prime 3169 := by norm_num
private theorem p3181 : Nat.Prime 3181 := by norm_num
private theorem p3187 : Nat.Prime 3187 := by norm_num
private theorem p3191 : Nat.Prime 3191 := by norm_num
private theorem p3203 : Nat.Prime 3203 := by norm_num
private theorem p3209 : Nat.Prime 3209 := by norm_num
private theorem p3217 : Nat.Prime 3217 := by norm_num
private theorem p3221 : Nat.Prime 3221 := by norm_num
private theorem p3229 : Nat.Prime 3229 := by norm_num
private theorem p3251 : Nat.Prime 3251 := by norm_num
private theorem p3253 : Nat.Prime 3253 := by norm_num
private theorem p3257 : Nat.Prime 3257 := by norm_num
private theorem p3259 : Nat.Prime 3259 := by norm_num
private theorem p3271 : Nat.Prime 3271 := by norm_num
private theorem p3299 : Nat.Prime 3299 := by norm_num
private theorem p3301 : Nat.Prime 3301 := by norm_num
private theorem p3307 : Nat.Prime 3307 := by norm_num
private theorem p3313 : Nat.Prime 3313 := by norm_num
private theorem p3319 : Nat.Prime 3319 := by norm_num
private theorem p3323 : Nat.Prime 3323 := by norm_num
private theorem p3329 : Nat.Prime 3329 := by norm_num
private theorem p3331 : Nat.Prime 3331 := by norm_num
private theorem p3343 : Nat.Prime 3343 := by norm_num
private theorem p3347 : Nat.Prime 3347 := by norm_num
private theorem p3359 : Nat.Prime 3359 := by norm_num
private theorem p3361 : Nat.Prime 3361 := by norm_num
private theorem p3371 : Nat.Prime 3371 := by norm_num
private theorem p3373 : Nat.Prime 3373 := by norm_num
private theorem p3389 : Nat.Prime 3389 := by norm_num
private theorem p3391 : Nat.Prime 3391 := by norm_num
private theorem p3407 : Nat.Prime 3407 := by norm_num
private theorem p3413 : Nat.Prime 3413 := by norm_num
private theorem p3433 : Nat.Prime 3433 := by norm_num
private theorem p3449 : Nat.Prime 3449 := by norm_num
private theorem p3457 : Nat.Prime 3457 := by norm_num
private theorem p3461 : Nat.Prime 3461 := by norm_num
private theorem p3463 : Nat.Prime 3463 := by norm_num
private theorem p3467 : Nat.Prime 3467 := by norm_num
private theorem p3469 : Nat.Prime 3469 := by norm_num
private theorem p3491 : Nat.Prime 3491 := by norm_num
private theorem p3499 : Nat.Prime 3499 := by norm_num
private theorem p3511 : Nat.Prime 3511 := by norm_num
private theorem p3517 : Nat.Prime 3517 := by norm_num
private theorem p3527 : Nat.Prime 3527 := by norm_num
private theorem p3529 : Nat.Prime 3529 := by norm_num
private theorem p3533 : Nat.Prime 3533 := by norm_num
private theorem p3539 : Nat.Prime 3539 := by norm_num
private theorem p3541 : Nat.Prime 3541 := by norm_num
private theorem p3547 : Nat.Prime 3547 := by norm_num
private theorem p3557 : Nat.Prime 3557 := by norm_num
private theorem p3559 : Nat.Prime 3559 := by norm_num
private theorem p3571 : Nat.Prime 3571 := by norm_num
private theorem p3581 : Nat.Prime 3581 := by norm_num
private theorem p3583 : Nat.Prime 3583 := by norm_num
private theorem p3593 : Nat.Prime 3593 := by norm_num
private theorem p3607 : Nat.Prime 3607 := by norm_num
private theorem p3613 : Nat.Prime 3613 := by norm_num
private theorem p3617 : Nat.Prime 3617 := by norm_num
private theorem p3623 : Nat.Prime 3623 := by norm_num
private theorem p3631 : Nat.Prime 3631 := by norm_num
private theorem p3637 : Nat.Prime 3637 := by norm_num
private theorem p3643 : Nat.Prime 3643 := by norm_num
private theorem p3659 : Nat.Prime 3659 := by norm_num
private theorem p3671 : Nat.Prime 3671 := by norm_num
private theorem p3673 : Nat.Prime 3673 := by norm_num
private theorem p3677 : Nat.Prime 3677 := by norm_num
private theorem p3691 : Nat.Prime 3691 := by norm_num
private theorem p3697 : Nat.Prime 3697 := by norm_num
private theorem p3701 : Nat.Prime 3701 := by norm_num
private theorem p3709 : Nat.Prime 3709 := by norm_num
private theorem p3719 : Nat.Prime 3719 := by norm_num
private theorem p3727 : Nat.Prime 3727 := by norm_num
private theorem p3733 : Nat.Prime 3733 := by norm_num
private theorem p3739 : Nat.Prime 3739 := by norm_num
private theorem p3761 : Nat.Prime 3761 := by norm_num
private theorem p3767 : Nat.Prime 3767 := by norm_num
private theorem p3769 : Nat.Prime 3769 := by norm_num
private theorem p3779 : Nat.Prime 3779 := by norm_num
private theorem p3793 : Nat.Prime 3793 := by norm_num
private theorem p3797 : Nat.Prime 3797 := by norm_num
private theorem p3803 : Nat.Prime 3803 := by norm_num
private theorem p3821 : Nat.Prime 3821 := by norm_num
private theorem p3823 : Nat.Prime 3823 := by norm_num
private theorem p3833 : Nat.Prime 3833 := by norm_num
private theorem p3847 : Nat.Prime 3847 := by norm_num
private theorem p3851 : Nat.Prime 3851 := by norm_num
private theorem p3853 : Nat.Prime 3853 := by norm_num
private theorem p3863 : Nat.Prime 3863 := by norm_num
private theorem p3877 : Nat.Prime 3877 := by norm_num
private theorem p3881 : Nat.Prime 3881 := by norm_num
private theorem p3889 : Nat.Prime 3889 := by norm_num
private theorem p3907 : Nat.Prime 3907 := by norm_num
private theorem p3911 : Nat.Prime 3911 := by norm_num
private theorem p3917 : Nat.Prime 3917 := by norm_num
private theorem p3919 : Nat.Prime 3919 := by norm_num
private theorem p3923 : Nat.Prime 3923 := by norm_num
private theorem p3929 : Nat.Prime 3929 := by norm_num
private theorem p3931 : Nat.Prime 3931 := by norm_num
private theorem p3943 : Nat.Prime 3943 := by norm_num
private theorem p3947 : Nat.Prime 3947 := by norm_num
private theorem p3967 : Nat.Prime 3967 := by norm_num
private theorem p3989 : Nat.Prime 3989 := by norm_num
private theorem p4001 : Nat.Prime 4001 := by norm_num
private theorem p4003 : Nat.Prime 4003 := by norm_num
private theorem p4007 : Nat.Prime 4007 := by norm_num
private theorem p4013 : Nat.Prime 4013 := by norm_num
private theorem p4019 : Nat.Prime 4019 := by norm_num
private theorem p4021 : Nat.Prime 4021 := by norm_num
private theorem p4027 : Nat.Prime 4027 := by norm_num
private theorem p4049 : Nat.Prime 4049 := by norm_num
private theorem p4051 : Nat.Prime 4051 := by norm_num
private theorem p4057 : Nat.Prime 4057 := by norm_num
private theorem p4073 : Nat.Prime 4073 := by norm_num
private theorem p4079 : Nat.Prime 4079 := by norm_num
private theorem p4091 : Nat.Prime 4091 := by norm_num
private theorem p4093 : Nat.Prime 4093 := by norm_num
private theorem p4099 : Nat.Prime 4099 := by norm_num
private theorem p4111 : Nat.Prime 4111 := by norm_num
private theorem p4127 : Nat.Prime 4127 := by norm_num
private theorem p4129 : Nat.Prime 4129 := by norm_num
private theorem p4133 : Nat.Prime 4133 := by norm_num
private theorem p4139 : Nat.Prime 4139 := by norm_num
private theorem p4153 : Nat.Prime 4153 := by norm_num
private theorem p4157 : Nat.Prime 4157 := by norm_num
private theorem p4159 : Nat.Prime 4159 := by norm_num
private theorem p4177 : Nat.Prime 4177 := by norm_num
private theorem p4201 : Nat.Prime 4201 := by norm_num
private theorem p4211 : Nat.Prime 4211 := by norm_num
private theorem p4217 : Nat.Prime 4217 := by norm_num
private theorem p4219 : Nat.Prime 4219 := by norm_num
private theorem p4229 : Nat.Prime 4229 := by norm_num
private theorem p4231 : Nat.Prime 4231 := by norm_num
private theorem p4241 : Nat.Prime 4241 := by norm_num
private theorem p4243 : Nat.Prime 4243 := by norm_num
private theorem p4253 : Nat.Prime 4253 := by norm_num
private theorem p4259 : Nat.Prime 4259 := by norm_num
private theorem p4261 : Nat.Prime 4261 := by norm_num
private theorem p4271 : Nat.Prime 4271 := by norm_num
private theorem p4273 : Nat.Prime 4273 := by norm_num
private theorem p4283 : Nat.Prime 4283 := by norm_num
private theorem p4289 : Nat.Prime 4289 := by norm_num
private theorem p4297 : Nat.Prime 4297 := by norm_num
private theorem p4327 : Nat.Prime 4327 := by norm_num
private theorem p4337 : Nat.Prime 4337 := by norm_num
private theorem p4339 : Nat.Prime 4339 := by norm_num
private theorem p4349 : Nat.Prime 4349 := by norm_num
private theorem p4357 : Nat.Prime 4357 := by norm_num
private theorem p4363 : Nat.Prime 4363 := by norm_num
private theorem p4373 : Nat.Prime 4373 := by norm_num
private theorem p4391 : Nat.Prime 4391 := by norm_num
private theorem p4397 : Nat.Prime 4397 := by norm_num
private theorem p4409 : Nat.Prime 4409 := by norm_num
private theorem p4421 : Nat.Prime 4421 := by norm_num
private theorem p4423 : Nat.Prime 4423 := by norm_num
private theorem p4441 : Nat.Prime 4441 := by norm_num
private theorem p4447 : Nat.Prime 4447 := by norm_num
private theorem p4451 : Nat.Prime 4451 := by norm_num
private theorem p4457 : Nat.Prime 4457 := by norm_num
private theorem p4463 : Nat.Prime 4463 := by norm_num
private theorem p4481 : Nat.Prime 4481 := by norm_num
private theorem p4483 : Nat.Prime 4483 := by norm_num
private theorem p4493 : Nat.Prime 4493 := by norm_num
private theorem p4507 : Nat.Prime 4507 := by norm_num
private theorem p4513 : Nat.Prime 4513 := by norm_num
private theorem p4517 : Nat.Prime 4517 := by norm_num
private theorem p4519 : Nat.Prime 4519 := by norm_num
private theorem p4523 : Nat.Prime 4523 := by norm_num
private theorem p4547 : Nat.Prime 4547 := by norm_num
private theorem p4549 : Nat.Prime 4549 := by norm_num
private theorem p4561 : Nat.Prime 4561 := by norm_num
private theorem p4567 : Nat.Prime 4567 := by norm_num
private theorem p4583 : Nat.Prime 4583 := by norm_num
private theorem p4591 : Nat.Prime 4591 := by norm_num
private theorem p4597 : Nat.Prime 4597 := by norm_num
private theorem p4603 : Nat.Prime 4603 := by norm_num
private theorem p4621 : Nat.Prime 4621 := by norm_num
private theorem p4637 : Nat.Prime 4637 := by norm_num
private theorem p4639 : Nat.Prime 4639 := by norm_num
private theorem p4643 : Nat.Prime 4643 := by norm_num
private theorem p4649 : Nat.Prime 4649 := by norm_num
private theorem p4651 : Nat.Prime 4651 := by norm_num
private theorem p4657 : Nat.Prime 4657 := by norm_num
private theorem p4663 : Nat.Prime 4663 := by norm_num
private theorem p4673 : Nat.Prime 4673 := by norm_num
private theorem p4679 : Nat.Prime 4679 := by norm_num
private theorem p4691 : Nat.Prime 4691 := by norm_num
private theorem p4703 : Nat.Prime 4703 := by norm_num
private theorem p4721 : Nat.Prime 4721 := by norm_num
private theorem p4723 : Nat.Prime 4723 := by norm_num
private theorem p4729 : Nat.Prime 4729 := by norm_num
private theorem p4733 : Nat.Prime 4733 := by norm_num
private theorem p4751 : Nat.Prime 4751 := by norm_num
private theorem p4759 : Nat.Prime 4759 := by norm_num
private theorem p4783 : Nat.Prime 4783 := by norm_num
private theorem p4787 : Nat.Prime 4787 := by norm_num
private theorem p4789 : Nat.Prime 4789 := by norm_num
private theorem p4793 : Nat.Prime 4793 := by norm_num
private theorem p4799 : Nat.Prime 4799 := by norm_num
private theorem p4801 : Nat.Prime 4801 := by norm_num
private theorem p4813 : Nat.Prime 4813 := by norm_num
private theorem p4817 : Nat.Prime 4817 := by norm_num
private theorem p4831 : Nat.Prime 4831 := by norm_num
private theorem p4861 : Nat.Prime 4861 := by norm_num
private theorem p4871 : Nat.Prime 4871 := by norm_num
private theorem p4877 : Nat.Prime 4877 := by norm_num
private theorem p4889 : Nat.Prime 4889 := by norm_num
private theorem p4903 : Nat.Prime 4903 := by norm_num
private theorem p4909 : Nat.Prime 4909 := by norm_num
private theorem p4919 : Nat.Prime 4919 := by norm_num
private theorem p4931 : Nat.Prime 4931 := by norm_num
private theorem p4933 : Nat.Prime 4933 := by norm_num
private theorem p4937 : Nat.Prime 4937 := by norm_num
private theorem p4943 : Nat.Prime 4943 := by norm_num
private theorem p4951 : Nat.Prime 4951 := by norm_num
private theorem p4957 : Nat.Prime 4957 := by norm_num
private theorem p4967 : Nat.Prime 4967 := by norm_num
private theorem p4969 : Nat.Prime 4969 := by norm_num
private theorem p4973 : Nat.Prime 4973 := by norm_num
private theorem p4987 : Nat.Prime 4987 := by norm_num
private theorem p4993 : Nat.Prime 4993 := by norm_num
private theorem p4999 : Nat.Prime 4999 := by norm_num
private theorem p5003 : Nat.Prime 5003 := by norm_num
private theorem p5009 : Nat.Prime 5009 := by norm_num
private theorem p5011 : Nat.Prime 5011 := by norm_num
private theorem p5021 : Nat.Prime 5021 := by norm_num
private theorem p5023 : Nat.Prime 5023 := by norm_num
private theorem p5039 : Nat.Prime 5039 := by norm_num
private theorem p5051 : Nat.Prime 5051 := by norm_num
private theorem p5059 : Nat.Prime 5059 := by norm_num
private theorem p5077 : Nat.Prime 5077 := by norm_num
private theorem p5081 : Nat.Prime 5081 := by norm_num
private theorem p5087 : Nat.Prime 5087 := by norm_num
private theorem p5099 : Nat.Prime 5099 := by norm_num
private theorem p5101 : Nat.Prime 5101 := by norm_num
private theorem p5107 : Nat.Prime 5107 := by norm_num
private theorem p5113 : Nat.Prime 5113 := by norm_num
private theorem p5119 : Nat.Prime 5119 := by norm_num
private theorem p5147 : Nat.Prime 5147 := by norm_num
private theorem p5153 : Nat.Prime 5153 := by norm_num
private theorem p5167 : Nat.Prime 5167 := by norm_num
private theorem p5171 : Nat.Prime 5171 := by norm_num
private theorem p5179 : Nat.Prime 5179 := by norm_num
private theorem p5189 : Nat.Prime 5189 := by norm_num
private theorem p5197 : Nat.Prime 5197 := by norm_num
private theorem p5209 : Nat.Prime 5209 := by norm_num
private theorem p5227 : Nat.Prime 5227 := by norm_num
private theorem p5231 : Nat.Prime 5231 := by norm_num
private theorem p5233 : Nat.Prime 5233 := by norm_num
private theorem p5237 : Nat.Prime 5237 := by norm_num
private theorem p5261 : Nat.Prime 5261 := by norm_num
private theorem p5273 : Nat.Prime 5273 := by norm_num
private theorem p5279 : Nat.Prime 5279 := by norm_num
private theorem p5281 : Nat.Prime 5281 := by norm_num
private theorem p5297 : Nat.Prime 5297 := by norm_num
private theorem p5303 : Nat.Prime 5303 := by norm_num
private theorem p5309 : Nat.Prime 5309 := by norm_num
private theorem p5323 : Nat.Prime 5323 := by norm_num
private theorem p5333 : Nat.Prime 5333 := by norm_num
private theorem p5347 : Nat.Prime 5347 := by norm_num
private theorem p5351 : Nat.Prime 5351 := by norm_num
private theorem p5381 : Nat.Prime 5381 := by norm_num
private theorem p5387 : Nat.Prime 5387 := by norm_num
private theorem p5393 : Nat.Prime 5393 := by norm_num
private theorem p5399 : Nat.Prime 5399 := by norm_num
private theorem p5407 : Nat.Prime 5407 := by norm_num
private theorem p5413 : Nat.Prime 5413 := by norm_num
private theorem p5417 : Nat.Prime 5417 := by norm_num
private theorem p5419 : Nat.Prime 5419 := by norm_num
private theorem p5431 : Nat.Prime 5431 := by norm_num
private theorem p5437 : Nat.Prime 5437 := by norm_num
private theorem p5441 : Nat.Prime 5441 := by norm_num
private theorem p5443 : Nat.Prime 5443 := by norm_num
private theorem p5449 : Nat.Prime 5449 := by norm_num
private theorem p5471 : Nat.Prime 5471 := by norm_num
private theorem p5477 : Nat.Prime 5477 := by norm_num
private theorem p5479 : Nat.Prime 5479 := by norm_num
private theorem p5483 : Nat.Prime 5483 := by norm_num
private theorem p5501 : Nat.Prime 5501 := by norm_num
private theorem p5503 : Nat.Prime 5503 := by norm_num
private theorem p5507 : Nat.Prime 5507 := by norm_num
private theorem p5519 : Nat.Prime 5519 := by norm_num
private theorem p5521 : Nat.Prime 5521 := by norm_num
private theorem p5527 : Nat.Prime 5527 := by norm_num
private theorem p5531 : Nat.Prime 5531 := by norm_num
private theorem p5557 : Nat.Prime 5557 := by norm_num
private theorem p5563 : Nat.Prime 5563 := by norm_num
private theorem p5569 : Nat.Prime 5569 := by norm_num
private theorem p5573 : Nat.Prime 5573 := by norm_num
private theorem p5581 : Nat.Prime 5581 := by norm_num
private theorem p5591 : Nat.Prime 5591 := by norm_num
private theorem p5623 : Nat.Prime 5623 := by norm_num
private theorem p5639 : Nat.Prime 5639 := by norm_num
private theorem p5641 : Nat.Prime 5641 := by norm_num
private theorem p5647 : Nat.Prime 5647 := by norm_num
private theorem p5651 : Nat.Prime 5651 := by norm_num
private theorem p5653 : Nat.Prime 5653 := by norm_num
private theorem p5657 : Nat.Prime 5657 := by norm_num
private theorem p5659 : Nat.Prime 5659 := by norm_num
private theorem p5669 : Nat.Prime 5669 := by norm_num
private theorem p5683 : Nat.Prime 5683 := by norm_num
private theorem p5689 : Nat.Prime 5689 := by norm_num
private theorem p5693 : Nat.Prime 5693 := by norm_num
private theorem p5701 : Nat.Prime 5701 := by norm_num
private theorem p5711 : Nat.Prime 5711 := by norm_num
private theorem p5717 : Nat.Prime 5717 := by norm_num
private theorem p5737 : Nat.Prime 5737 := by norm_num
private theorem p5741 : Nat.Prime 5741 := by norm_num
private theorem p5743 : Nat.Prime 5743 := by norm_num
private theorem p5749 : Nat.Prime 5749 := by norm_num
private theorem p5779 : Nat.Prime 5779 := by norm_num
private theorem p5783 : Nat.Prime 5783 := by norm_num
private theorem p5791 : Nat.Prime 5791 := by norm_num
private theorem p5801 : Nat.Prime 5801 := by norm_num
private theorem p5807 : Nat.Prime 5807 := by norm_num
private theorem p5813 : Nat.Prime 5813 := by norm_num
private theorem p5821 : Nat.Prime 5821 := by norm_num
private theorem p5827 : Nat.Prime 5827 := by norm_num
private theorem p5839 : Nat.Prime 5839 := by norm_num
private theorem p5843 : Nat.Prime 5843 := by norm_num
private theorem p5849 : Nat.Prime 5849 := by norm_num
private theorem p5851 : Nat.Prime 5851 := by norm_num
private theorem p5857 : Nat.Prime 5857 := by norm_num
private theorem p5861 : Nat.Prime 5861 := by norm_num
private theorem p5867 : Nat.Prime 5867 := by norm_num
private theorem p5869 : Nat.Prime 5869 := by norm_num
private theorem p5879 : Nat.Prime 5879 := by norm_num
private theorem p5881 : Nat.Prime 5881 := by norm_num
private theorem p5897 : Nat.Prime 5897 := by norm_num
private theorem p5903 : Nat.Prime 5903 := by norm_num
private theorem p5923 : Nat.Prime 5923 := by norm_num
private theorem p5927 : Nat.Prime 5927 := by norm_num
private theorem p5939 : Nat.Prime 5939 := by norm_num
private theorem p5953 : Nat.Prime 5953 := by norm_num
private theorem p5981 : Nat.Prime 5981 := by norm_num
private theorem p5987 : Nat.Prime 5987 := by norm_num
private theorem p6007 : Nat.Prime 6007 := by norm_num
private theorem p6011 : Nat.Prime 6011 := by norm_num
private theorem p6029 : Nat.Prime 6029 := by norm_num
private theorem p6037 : Nat.Prime 6037 := by norm_num
private theorem p6043 : Nat.Prime 6043 := by norm_num
private theorem p6047 : Nat.Prime 6047 := by norm_num
private theorem p6053 : Nat.Prime 6053 := by norm_num
private theorem p6067 : Nat.Prime 6067 := by norm_num
private theorem p6073 : Nat.Prime 6073 := by norm_num
private theorem p6079 : Nat.Prime 6079 := by norm_num
private theorem p6089 : Nat.Prime 6089 := by norm_num
private theorem p6091 : Nat.Prime 6091 := by norm_num
private theorem p6101 : Nat.Prime 6101 := by norm_num
private theorem p6113 : Nat.Prime 6113 := by norm_num
private theorem p6121 : Nat.Prime 6121 := by norm_num
private theorem p6131 : Nat.Prime 6131 := by norm_num
private theorem p6133 : Nat.Prime 6133 := by norm_num
private theorem p6143 : Nat.Prime 6143 := by norm_num
private theorem p6151 : Nat.Prime 6151 := by norm_num
private theorem p6163 : Nat.Prime 6163 := by norm_num
private theorem p6173 : Nat.Prime 6173 := by norm_num
private theorem p6197 : Nat.Prime 6197 := by norm_num
private theorem p6199 : Nat.Prime 6199 := by norm_num
private theorem p6203 : Nat.Prime 6203 := by norm_num
private theorem p6211 : Nat.Prime 6211 := by norm_num
private theorem p6217 : Nat.Prime 6217 := by norm_num
private theorem p6221 : Nat.Prime 6221 := by norm_num
private theorem p6229 : Nat.Prime 6229 := by norm_num
private theorem p6247 : Nat.Prime 6247 := by norm_num
private theorem p6257 : Nat.Prime 6257 := by norm_num
private theorem p6263 : Nat.Prime 6263 := by norm_num
private theorem p6269 : Nat.Prime 6269 := by norm_num
private theorem p6271 : Nat.Prime 6271 := by norm_num
private theorem p6277 : Nat.Prime 6277 := by norm_num
private theorem p6287 : Nat.Prime 6287 := by norm_num
private theorem p6299 : Nat.Prime 6299 := by norm_num
private theorem p6301 : Nat.Prime 6301 := by norm_num
private theorem p6311 : Nat.Prime 6311 := by norm_num
private theorem p6317 : Nat.Prime 6317 := by norm_num
private theorem p6323 : Nat.Prime 6323 := by norm_num
private theorem p6329 : Nat.Prime 6329 := by norm_num
private theorem p6337 : Nat.Prime 6337 := by norm_num
private theorem p6343 : Nat.Prime 6343 := by norm_num
private theorem p6353 : Nat.Prime 6353 := by norm_num
private theorem p6359 : Nat.Prime 6359 := by norm_num
private theorem p6361 : Nat.Prime 6361 := by norm_num
private theorem p6367 : Nat.Prime 6367 := by norm_num
private theorem p6373 : Nat.Prime 6373 := by norm_num
private theorem p6379 : Nat.Prime 6379 := by norm_num
private theorem p6389 : Nat.Prime 6389 := by norm_num
private theorem p6397 : Nat.Prime 6397 := by norm_num
private theorem p6421 : Nat.Prime 6421 := by norm_num
private theorem p6427 : Nat.Prime 6427 := by norm_num
private theorem p6449 : Nat.Prime 6449 := by norm_num
private theorem p6451 : Nat.Prime 6451 := by norm_num
private theorem p6469 : Nat.Prime 6469 := by norm_num
private theorem p6473 : Nat.Prime 6473 := by norm_num
private theorem p6481 : Nat.Prime 6481 := by norm_num
private theorem p6491 : Nat.Prime 6491 := by norm_num
private theorem p6521 : Nat.Prime 6521 := by norm_num
private theorem p6529 : Nat.Prime 6529 := by norm_num
private theorem p6547 : Nat.Prime 6547 := by norm_num
private theorem p6551 : Nat.Prime 6551 := by norm_num
private theorem p6553 : Nat.Prime 6553 := by norm_num
private theorem p6563 : Nat.Prime 6563 := by norm_num
private theorem p6569 : Nat.Prime 6569 := by norm_num
private theorem p6571 : Nat.Prime 6571 := by norm_num
private theorem p6577 : Nat.Prime 6577 := by norm_num
private theorem p6581 : Nat.Prime 6581 := by norm_num
private theorem p6599 : Nat.Prime 6599 := by norm_num
private theorem p6607 : Nat.Prime 6607 := by norm_num
private theorem p6619 : Nat.Prime 6619 := by norm_num
private theorem p6637 : Nat.Prime 6637 := by norm_num
private theorem p6653 : Nat.Prime 6653 := by norm_num
private theorem p6659 : Nat.Prime 6659 := by norm_num
private theorem p6661 : Nat.Prime 6661 := by norm_num
private theorem p6673 : Nat.Prime 6673 := by norm_num
private theorem p6679 : Nat.Prime 6679 := by norm_num
private theorem p6689 : Nat.Prime 6689 := by norm_num
private theorem p6691 : Nat.Prime 6691 := by norm_num
private theorem p6701 : Nat.Prime 6701 := by norm_num
private theorem p6703 : Nat.Prime 6703 := by norm_num
private theorem p6709 : Nat.Prime 6709 := by norm_num
private theorem p6719 : Nat.Prime 6719 := by norm_num
private theorem p6733 : Nat.Prime 6733 := by norm_num
private theorem p6737 : Nat.Prime 6737 := by norm_num
private theorem p6761 : Nat.Prime 6761 := by norm_num
private theorem p6763 : Nat.Prime 6763 := by norm_num
private theorem p6779 : Nat.Prime 6779 := by norm_num
private theorem p6781 : Nat.Prime 6781 := by norm_num
private theorem p6791 : Nat.Prime 6791 := by norm_num
private theorem p6793 : Nat.Prime 6793 := by norm_num
private theorem p6803 : Nat.Prime 6803 := by norm_num
private theorem p6823 : Nat.Prime 6823 := by norm_num
private theorem p6827 : Nat.Prime 6827 := by norm_num
private theorem p6829 : Nat.Prime 6829 := by norm_num
private theorem p6833 : Nat.Prime 6833 := by norm_num
private theorem p6841 : Nat.Prime 6841 := by norm_num
private theorem p6857 : Nat.Prime 6857 := by norm_num
private theorem p6863 : Nat.Prime 6863 := by norm_num
private theorem p6869 : Nat.Prime 6869 := by norm_num
private theorem p6871 : Nat.Prime 6871 := by norm_num
private theorem p6883 : Nat.Prime 6883 := by norm_num
private theorem p6899 : Nat.Prime 6899 := by norm_num
private theorem p6907 : Nat.Prime 6907 := by norm_num
private theorem p6911 : Nat.Prime 6911 := by norm_num
private theorem p6917 : Nat.Prime 6917 := by norm_num
private theorem p6947 : Nat.Prime 6947 := by norm_num
private theorem p6949 : Nat.Prime 6949 := by norm_num
private theorem p6959 : Nat.Prime 6959 := by norm_num
private theorem p6961 : Nat.Prime 6961 := by norm_num
private theorem p6967 : Nat.Prime 6967 := by norm_num
private theorem p6971 : Nat.Prime 6971 := by norm_num
private theorem p6977 : Nat.Prime 6977 := by norm_num
private theorem p6983 : Nat.Prime 6983 := by norm_num
private theorem p6991 : Nat.Prime 6991 := by norm_num
private theorem p6997 : Nat.Prime 6997 := by norm_num
private theorem p7001 : Nat.Prime 7001 := by norm_num
private theorem p7013 : Nat.Prime 7013 := by norm_num
private theorem p7019 : Nat.Prime 7019 := by norm_num
private theorem p7027 : Nat.Prime 7027 := by norm_num
private theorem p7039 : Nat.Prime 7039 := by norm_num
private theorem p7043 : Nat.Prime 7043 := by norm_num
private theorem p7057 : Nat.Prime 7057 := by norm_num
private theorem p7069 : Nat.Prime 7069 := by norm_num
private theorem p7079 : Nat.Prime 7079 := by norm_num
private theorem p7103 : Nat.Prime 7103 := by norm_num
private theorem p7109 : Nat.Prime 7109 := by norm_num
private theorem p7121 : Nat.Prime 7121 := by norm_num
private theorem p7127 : Nat.Prime 7127 := by norm_num
private theorem p7129 : Nat.Prime 7129 := by norm_num
private theorem p7151 : Nat.Prime 7151 := by norm_num
private theorem p7159 : Nat.Prime 7159 := by norm_num
private theorem p7177 : Nat.Prime 7177 := by norm_num
private theorem p7187 : Nat.Prime 7187 := by norm_num
private theorem p7193 : Nat.Prime 7193 := by norm_num
private theorem p7207 : Nat.Prime 7207 := by norm_num
private theorem p7211 : Nat.Prime 7211 := by norm_num
private theorem p7213 : Nat.Prime 7213 := by norm_num
private theorem p7219 : Nat.Prime 7219 := by norm_num
private theorem p7229 : Nat.Prime 7229 := by norm_num
private theorem p7237 : Nat.Prime 7237 := by norm_num
private theorem p7243 : Nat.Prime 7243 := by norm_num
private theorem p7247 : Nat.Prime 7247 := by norm_num
private theorem p7253 : Nat.Prime 7253 := by norm_num
private theorem p7283 : Nat.Prime 7283 := by norm_num
private theorem p7297 : Nat.Prime 7297 := by norm_num
private theorem p7307 : Nat.Prime 7307 := by norm_num
private theorem p7309 : Nat.Prime 7309 := by norm_num
private theorem p7321 : Nat.Prime 7321 := by norm_num
private theorem p7331 : Nat.Prime 7331 := by norm_num
private theorem p7333 : Nat.Prime 7333 := by norm_num
private theorem p7349 : Nat.Prime 7349 := by norm_num
private theorem p7351 : Nat.Prime 7351 := by norm_num
private theorem p7369 : Nat.Prime 7369 := by norm_num
private theorem p7393 : Nat.Prime 7393 := by norm_num
private theorem p7411 : Nat.Prime 7411 := by norm_num
private theorem p7417 : Nat.Prime 7417 := by norm_num
private theorem p7433 : Nat.Prime 7433 := by norm_num
private theorem p7451 : Nat.Prime 7451 := by norm_num
private theorem p7457 : Nat.Prime 7457 := by norm_num
private theorem p7459 : Nat.Prime 7459 := by norm_num
private theorem p7477 : Nat.Prime 7477 := by norm_num
private theorem p7481 : Nat.Prime 7481 := by norm_num
private theorem p7487 : Nat.Prime 7487 := by norm_num
private theorem p7489 : Nat.Prime 7489 := by norm_num
private theorem p7499 : Nat.Prime 7499 := by norm_num
private theorem p7507 : Nat.Prime 7507 := by norm_num
private theorem p7517 : Nat.Prime 7517 := by norm_num
private theorem p7523 : Nat.Prime 7523 := by norm_num
private theorem p7529 : Nat.Prime 7529 := by norm_num
private theorem p7537 : Nat.Prime 7537 := by norm_num
private theorem p7541 : Nat.Prime 7541 := by norm_num
private theorem p7547 : Nat.Prime 7547 := by norm_num
private theorem p7549 : Nat.Prime 7549 := by norm_num
private theorem p7559 : Nat.Prime 7559 := by norm_num
private theorem p7561 : Nat.Prime 7561 := by norm_num
private theorem p7573 : Nat.Prime 7573 := by norm_num
private theorem p7577 : Nat.Prime 7577 := by norm_num
private theorem p7583 : Nat.Prime 7583 := by norm_num
private theorem p7589 : Nat.Prime 7589 := by norm_num
private theorem p7591 : Nat.Prime 7591 := by norm_num
private theorem p7603 : Nat.Prime 7603 := by norm_num
private theorem p7607 : Nat.Prime 7607 := by norm_num
private theorem p7621 : Nat.Prime 7621 := by norm_num
private theorem p7639 : Nat.Prime 7639 := by norm_num
private theorem p7643 : Nat.Prime 7643 := by norm_num
private theorem p7649 : Nat.Prime 7649 := by norm_num
private theorem p7669 : Nat.Prime 7669 := by norm_num
private theorem p7673 : Nat.Prime 7673 := by norm_num
private theorem p7681 : Nat.Prime 7681 := by norm_num
private theorem p7687 : Nat.Prime 7687 := by norm_num
private theorem p7691 : Nat.Prime 7691 := by norm_num
private theorem p7699 : Nat.Prime 7699 := by norm_num
private theorem p7703 : Nat.Prime 7703 := by norm_num
private theorem p7717 : Nat.Prime 7717 := by norm_num
private theorem p7723 : Nat.Prime 7723 := by norm_num
private theorem p7727 : Nat.Prime 7727 := by norm_num
private theorem p7741 : Nat.Prime 7741 := by norm_num
private theorem p7753 : Nat.Prime 7753 := by norm_num
private theorem p7757 : Nat.Prime 7757 := by norm_num
private theorem p7759 : Nat.Prime 7759 := by norm_num
private theorem p7789 : Nat.Prime 7789 := by norm_num
private theorem p7793 : Nat.Prime 7793 := by norm_num
private theorem p7817 : Nat.Prime 7817 := by norm_num
private theorem p7823 : Nat.Prime 7823 := by norm_num
private theorem p7829 : Nat.Prime 7829 := by norm_num
private theorem p7841 : Nat.Prime 7841 := by norm_num
private theorem p7853 : Nat.Prime 7853 := by norm_num
private theorem p7867 : Nat.Prime 7867 := by norm_num
private theorem p7873 : Nat.Prime 7873 := by norm_num
private theorem p7877 : Nat.Prime 7877 := by norm_num
private theorem p7879 : Nat.Prime 7879 := by norm_num
private theorem p7883 : Nat.Prime 7883 := by norm_num
private theorem p7901 : Nat.Prime 7901 := by norm_num
private theorem p7907 : Nat.Prime 7907 := by norm_num
private theorem p7919 : Nat.Prime 7919 := by norm_num
private theorem p7927 : Nat.Prime 7927 := by norm_num
private theorem p7933 : Nat.Prime 7933 := by norm_num
private theorem p7937 : Nat.Prime 7937 := by norm_num
private theorem p7949 : Nat.Prime 7949 := by norm_num
private theorem p7951 : Nat.Prime 7951 := by norm_num
private theorem p7963 : Nat.Prime 7963 := by norm_num
private theorem p7993 : Nat.Prime 7993 := by norm_num
private theorem p8009 : Nat.Prime 8009 := by norm_num
private theorem p9781 : Nat.Prime 9781 := by norm_num

private def qg4 : List ℕ := [2,3,5,7,5,11,13,7,17,19,5,23,17,11,29,31,17,19,37,23,41,43,29,47,41,43,53,47,41,59,61,47,61,67,53,71,73,59,61,79,73,83,83,71,89,83,89,79,97,83,101,103,89,107,109,103,113,107,101,103,113,107,109,127,113,131,131,127,137,139,137,127,137,131,149,151,137,139,157,151,157,163,149,167,167,163,173,167,173,179,181,167,181,179,173,191,193,179,197,199,7,199,11,191,193,211,197,199,23,211,151,223,31,227,229,37,233,41,43,239,241,227,229,53,233,251,59,239,257,251,67,263,71,251,269,271,257,271,277,263,281,283,269,271,281,97,293,101,281,283,107,109,31,307,293,311,313,307,317,311,127,307,131,311,313,331,317,331,337,331,337,149,151,347,349,157,353,347,163,359,167,347,349,367,353,367,373,359,373,379,373,383,191,193,389,197,199,379,397,383,401,401,389,337,409,409,397,239,401,419,421,229,409,233,421,431,433,419,421,439,433,443,251,431,449,257,449,439,457,443,461,463,449,467,461,277,457,281,461,479,479,467,211,487,487,491,491,479,223,499,307,503,311,491,509,317,509,499,509,503,521,523,509,523,521,337,37,359,521,523,541,349,541,547,541,547,359,547,557,557,367,563,557,373,569,571,557,571,577,563,577,389,569,587,587,397,593,401,593,599,601,587,601,607,593,607,613,599,617,619,613,607,431,433,613,631,617,619,443,631,641,643,641,647,641,457,653,461,641,659,661,647,661,659,653,397,673,659,677,677,487,683,491,683,673,691,677,691,503,683,701,509,701,691,709,709,709,521,701,719,719,719,709,727,727,727,733,719,733,739,547,743,743,739,733,751,751,739,757,743,761,569,571,751,769,577,773,773,761,283,587,607,769,787,773,787,599,601,797,797]
private theorem vg4 : rvld 1 4 qg4 := by
  unfold qg4
  exact rvc p2 p2 (rvc p3 p3 (rvc p3 p5 (rvc p3 p7 (rvc p7 p5 (rvc p3 p11 (rvc p3 p13 (rvc p11 p7 (rvc p3 p17 (rvc p3 p19 (rvc p19 p5 (rvc p3 p23 (rvc p11 p17 (rvc p19 p11 (rvc p3 p29 (rvc p3 p31 (rvc p19 p17 (rvc p19 p19 (rvc p3 p37 (rvc p19 p23 (rvc p3 p41 (rvc p3 p43 (rvc p19 p29 (rvc p3 p47 (rvc p11 p41 (rvc p11 p43 (rvc p3 p53 (rvc p11 p47 (rvc p19 p41 (rvc p3 p59 (rvc p3 p61 (rvc p19 p47 (rvc p7 p61 (rvc p3 p67 (rvc p19 p53 (rvc p3 p71 (rvc p3 p73 (rvc p19 p59 (rvc p19 p61 (rvc p3 p79 (rvc p11 p73 (rvc p3 p83 (rvc p5 p83 (rvc p19 p71 (rvc p3 p89 (rvc p11 p83 (rvc p7 p89 (rvc p19 p79 (rvc p3 p97 (rvc p19 p83 (rvc p3 p101 (rvc p3 p103 (rvc p19 p89 (rvc p3 p107 (rvc p3 p109 (rvc p11 p103 (rvc p3 p113 (rvc p11 p107 (rvc p19 p101 (rvc p19 p103 (rvc p11 p113 (rvc p19 p107 (rvc p19 p109 (rvc p3 p127 (rvc p19 p113 (rvc p3 p131 (rvc p5 p131 (rvc p11 p127 (rvc p3 p137 (rvc p3 p139 (rvc p7 p137 (rvc p19 p127 (rvc p11 p137 (rvc p19 p131 (rvc p3 p149 (rvc p3 p151 (rvc p19 p137 (rvc p19 p139 (rvc p3 p157 (rvc p11 p151 (rvc p7 p157 (rvc p3 p163 (rvc p19 p149 (rvc p3 p167 (rvc p5 p167 (rvc p11 p163 (rvc p3 p173 (rvc p11 p167 (rvc p7 p173 (rvc p3 p179 (rvc p3 p181 (rvc p19 p167 (rvc p7 p181 (rvc p11 p179 (rvc p19 p173 (rvc p3 p191 (rvc p3 p193 (rvc p19 p179 (rvc p3 p197 (rvc p3 p199 (rvc p197 p7 (rvc p7 p199 (rvc p197 p11 (rvc p19 p191 (rvc p19 p193 (rvc p3 p211 (rvc p19 p197 (rvc p19 p199 (rvc p197 p23 (rvc p11 p211 (rvc p73 p151 (rvc p3 p223 (rvc p197 p31 (rvc p3 p227 (rvc p3 p229 (rvc p197 p37 (rvc p3 p233 (rvc p197 p41 (rvc p197 p43 (rvc p3 p239 (rvc p3 p241 (rvc p19 p227 (rvc p19 p229 (rvc p197 p53 (rvc p19 p233 (rvc p3 p251 (rvc p197 p59 (rvc p19 p239 (rvc p3 p257 (rvc p11 p251 (rvc p197 p67 (rvc p3 p263 (rvc p197 p71 (rvc p19 p251 (rvc p3 p269 (rvc p3 p271 (rvc p19 p257 (rvc p7 p271 (rvc p3 p277 (rvc p19 p263 (rvc p3 p281 (rvc p3 p283 (rvc p19 p269 (rvc p19 p271 (rvc p11 p281 (rvc p197 p97 (rvc p3 p293 (rvc p197 p101 (rvc p19 p281 (rvc p19 p283 (rvc p197 p107 (rvc p197 p109 (rvc p277 p31 (rvc p3 p307 (rvc p19 p293 (rvc p3 p311 (rvc p3 p313 (rvc p11 p307 (rvc p3 p317 (rvc p11 p311 (rvc p197 p127 (rvc p19 p307 (rvc p197 p131 (rvc p19 p311 (rvc p19 p313 (rvc p3 p331 (rvc p19 p317 (rvc p7 p331 (rvc p3 p337 (rvc p11 p331 (rvc p7 p337 (rvc p197 p149 (rvc p197 p151 (rvc p3 p347 (rvc p3 p349 (rvc p197 p157 (rvc p3 p353 (rvc p11 p347 (rvc p197 p163 (rvc p3 p359 (rvc p197 p167 (rvc p19 p347 (rvc p19 p349 (rvc p3 p367 (rvc p19 p353 (rvc p7 p367 (rvc p3 p373 (rvc p19 p359 (rvc p7 p373 (rvc p3 p379 (rvc p11 p373 (rvc p3 p383 (rvc p197 p191 (rvc p197 p193 (rvc p3 p389 (rvc p197 p197 (rvc p197 p199 (rvc p19 p379 (rvc p3 p397 (rvc p19 p383 (rvc p3 p401 (rvc p5 p401 (rvc p19 p389 (rvc p73 p337 (rvc p3 p409 (rvc p5 p409 (rvc p19 p397 (rvc p179 p239 (rvc p19 p401 (rvc p3 p419 (rvc p3 p421 (rvc p197 p229 (rvc p19 p409 (rvc p197 p233 (rvc p11 p421 (rvc p3 p431 (rvc p3 p433 (rvc p19 p419 (rvc p19 p421 (rvc p3 p439 (rvc p11 p433 (rvc p3 p443 (rvc p197 p251 (rvc p19 p431 (rvc p3 p449 (rvc p197 p257 (rvc p7 p449 (rvc p19 p439 (rvc p3 p457 (rvc p19 p443 (rvc p3 p461 (rvc p3 p463 (rvc p19 p449 (rvc p3 p467 (rvc p11 p461 (rvc p197 p277 (rvc p19 p457 (rvc p197 p281 (rvc p19 p461 (rvc p3 p479 (rvc p5 p479 (rvc p19 p467 (rvc p277 p211 (rvc p3 p487 (rvc p5 p487 (rvc p3 p491 (rvc p5 p491 (rvc p19 p479 (rvc p277 p223 (rvc p3 p499 (rvc p197 p307 (rvc p3 p503 (rvc p197 p311 (rvc p19 p491 (rvc p3 p509 (rvc p197 p317 (rvc p7 p509 (rvc p19 p499 (rvc p11 p509 (rvc p19 p503 (rvc p3 p521 (rvc p3 p523 (rvc p19 p509 (rvc p7 p523 (rvc p11 p521 (rvc p197 p337 (rvc p499 p37 (rvc p179 p359 (rvc p19 p521 (rvc p19 p523 (rvc p3 p541 (rvc p197 p349 (rvc p7 p541 (rvc p3 p547 (rvc p11 p541 (rvc p7 p547 (rvc p197 p359 (rvc p11 p547 (rvc p3 p557 (rvc p5 p557 (rvc p197 p367 (rvc p3 p563 (rvc p11 p557 (rvc p197 p373 (rvc p3 p569 (rvc p3 p571 (rvc p19 p557 (rvc p7 p571 (rvc p3 p577 (rvc p19 p563 (rvc p7 p577 (rvc p197 p389 (rvc p19 p569 (rvc p3 p587 (rvc p5 p587 (rvc p197 p397 (rvc p3 p593 (rvc p197 p401 (rvc p7 p593 (rvc p3 p599 (rvc p3 p601 (rvc p19 p587 (rvc p7 p601 (rvc p3 p607 (rvc p19 p593 (rvc p7 p607 (rvc p3 p613 (rvc p19 p599 (rvc p3 p617 (rvc p3 p619 (rvc p11 p613 (rvc p19 p607 (rvc p197 p431 (rvc p197 p433 (rvc p19 p613 (rvc p3 p631 (rvc p19 p617 (rvc p19 p619 (rvc p197 p443 (rvc p11 p631 (rvc p3 p641 (rvc p3 p643 (rvc p7 p641 (rvc p3 p647 (rvc p11 p641 (rvc p197 p457 (rvc p3 p653 (rvc p197 p461 (rvc p19 p641 (rvc p3 p659 (rvc p3 p661 (rvc p19 p647 (rvc p7 p661 (rvc p11 p659 (rvc p19 p653 (rvc p277 p397 (rvc p3 p673 (rvc p19 p659 (rvc p3 p677 (rvc p5 p677 (rvc p197 p487 (rvc p3 p683 (rvc p197 p491 (rvc p7 p683 (rvc p19 p673 (rvc p3 p691 (rvc p19 p677 (rvc p7 p691 (rvc p197 p503 (rvc p19 p683 (rvc p3 p701 (rvc p197 p509 (rvc p7 p701 (rvc p19 p691 (rvc p3 p709 (rvc p5 p709 (rvc p7 p709 (rvc p197 p521 (rvc p19 p701 (rvc p3 p719 (rvc p5 p719 (rvc p7 p719 (rvc p19 p709 (rvc p3 p727 (rvc p5 p727 (rvc p7 p727 (rvc p3 p733 (rvc p19 p719 (rvc p7 p733 (rvc p3 p739 (rvc p197 p547 (rvc p3 p743 (rvc p5 p743 (rvc p11 p739 (rvc p19 p733 (rvc p3 p751 (rvc p5 p751 (rvc p19 p739 (rvc p3 p757 (rvc p19 p743 (rvc p3 p761 (rvc p197 p569 (rvc p197 p571 (rvc p19 p751 (rvc p3 p769 (rvc p197 p577 (rvc p3 p773 (rvc p5 p773 (rvc p19 p761 (rvc p499 p283 (rvc p197 p587 (rvc p179 p607 (rvc p19 p769 (rvc p3 p787 (rvc p19 p773 (rvc p7 p787 (rvc p197 p599 (rvc p197 p601 (rvc p3 p797 (rvc p5 p797 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg4 (m : ℕ) (hl : 4 ≤ m) (hh : m ≤ 803) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-4)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 4+2*k := by simp [k]; omega
  have hk : k < qg4.length := by simp [k,qg4]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg4 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg804 : List ℕ := [607,787,797,613,809,811,797,811,809,811,821,823,809,827,829,823,829,641,821,839,647,827,829,653,673,577,853,839,857,859,853,863,857,673,853,677,857,859,877,863,881,883,691,887,881,883,877,701,881,883,677,887,409,907,907,911,719,907,421,919,727,907,701,911,929,929,739,919,937,937,941,941,929,947,941,757,953,761,941,463,953,947,691,967,953,971,971,967,977,971,787,983,977,971,919,991,977,991,997,983,997,809,811,991,1009,1009,1013,821,823,1019,1021,829,1009,1019,1013,1031,1033,1019,1021,1039,1033,1039,821,1031,1049,1051,859,1039,863,1051,1061,1063,1049,1051,1069,877,1069,881,1061,1063,887,907,1069,1087,1087,1091,1093,1087,1097,1091,907,1103,911,1091,1109,1103,1097,619,1117,1103,1117,1123,1109,1123,1129,937,1117,941,1129,1123,947,967,1129,953,653,1151,1153,1151,1153,1151,967,1163,971,1151,1153,1171,1171,1171,983,1163,1181,1181,991,1187,1181,997,1193,1187,1181,1129,1201,1187,1201,1013,1193,937,1213,1021,1217,1217,1213,1223,1031,1033,1229,1231,1217,1231,1237,1223,1237,1049,1229,1231,1249,1249,1237,1061,1063,1259,1259,1069,1249,1259,41,43,1097,1259,1277,1279,1087,1283,1091,1093,1289,1291,1277,1279,1297,1283,1301,1303,1289,1307,1301,1117,1297,1307,1301,1319,1321,1307,1321,1327,1321,1327,1109,1319,1321,1163,113,1327,1151,1153,853,953,857,127,1163,131,1361,1361,1171,1367,1361,1367,1373,1181,1361,151,1381,1367,1381,1193,1373,163,1217,1201,1381,1399,1399,1399,1229,1213,1409,1217,1409,1399,1223,191,193,1423,1409,1427,1429,1237,1433,1427,1429,1439,1433,1427,1429,1447,1433,1451,1453,1439,1453,1459,1453,1447,1289,1451,1453,1471,1279,1459,1283,1471,1481,1483,1291,1487,1489,1297,1493,1301,1481,1499,1307,1487,1489,1499,1493,1511,1319,1499,1021,1511,1327,1523,1523,1511,1033,1531,1531,1531,1361,1523,313,1543,1543,1531,1549,1543,1553,1361,1549,1559,1367,1559,1549,1567,1553,1571,1571,1559,349,1579,1579,1583,1583,1571,1093,1583,1399,1579,1597,1583]
private theorem vg804 : rvld 1 804 qg804 := by
  unfold qg804
  exact rvc p197 p607 (rvc p19 p787 (rvc p11 p797 (rvc p197 p613 (rvc p3 p809 (rvc p3 p811 (rvc p19 p797 (rvc p7 p811 (rvc p11 p809 (rvc p11 p811 (rvc p3 p821 (rvc p3 p823 (rvc p19 p809 (rvc p3 p827 (rvc p3 p829 (rvc p11 p823 (rvc p7 p829 (rvc p197 p641 (rvc p19 p821 (rvc p3 p839 (rvc p197 p647 (rvc p19 p827 (rvc p19 p829 (rvc p197 p653 (rvc p179 p673 (rvc p277 p577 (rvc p3 p853 (rvc p19 p839 (rvc p3 p857 (rvc p3 p859 (rvc p11 p853 (rvc p3 p863 (rvc p11 p857 (rvc p197 p673 (rvc p19 p853 (rvc p197 p677 (rvc p19 p857 (rvc p19 p859 (rvc p3 p877 (rvc p19 p863 (rvc p3 p881 (rvc p3 p883 (rvc p197 p691 (rvc p3 p887 (rvc p11 p881 (rvc p11 p883 (rvc p19 p877 (rvc p197 p701 (rvc p19 p881 (rvc p19 p883 (rvc p227 p677 (rvc p19 p887 (rvc p499 p409 (rvc p3 p907 (rvc p5 p907 (rvc p3 p911 (rvc p197 p719 (rvc p11 p907 (rvc p499 p421 (rvc p3 p919 (rvc p197 p727 (rvc p19 p907 (rvc p227 p701 (rvc p19 p911 (rvc p3 p929 (rvc p5 p929 (rvc p197 p739 (rvc p19 p919 (rvc p3 p937 (rvc p5 p937 (rvc p3 p941 (rvc p5 p941 (rvc p19 p929 (rvc p3 p947 (rvc p11 p941 (rvc p197 p757 (rvc p3 p953 (rvc p197 p761 (rvc p19 p941 (rvc p499 p463 (rvc p11 p953 (rvc p19 p947 (rvc p277 p691 (rvc p3 p967 (rvc p19 p953 (rvc p3 p971 (rvc p5 p971 (rvc p11 p967 (rvc p3 p977 (rvc p11 p971 (rvc p197 p787 (rvc p3 p983 (rvc p11 p977 (rvc p19 p971 (rvc p73 p919 (rvc p3 p991 (rvc p19 p977 (rvc p7 p991 (rvc p3 p997 (rvc p19 p983 (rvc p7 p997 (rvc p197 p809 (rvc p197 p811 (rvc p19 p991 (rvc p3 p1009 (rvc p5 p1009 (rvc p3 p1013 (rvc p197 p821 (rvc p197 p823 (rvc p3 p1019 (rvc p3 p1021 (rvc p197 p829 (rvc p19 p1009 (rvc p11 p1019 (rvc p19 p1013 (rvc p3 p1031 (rvc p3 p1033 (rvc p19 p1019 (rvc p19 p1021 (rvc p3 p1039 (rvc p11 p1033 (rvc p7 p1039 (rvc p227 p821 (rvc p19 p1031 (rvc p3 p1049 (rvc p3 p1051 (rvc p197 p859 (rvc p19 p1039 (rvc p197 p863 (rvc p11 p1051 (rvc p3 p1061 (rvc p3 p1063 (rvc p19 p1049 (rvc p19 p1051 (rvc p3 p1069 (rvc p197 p877 (rvc p7 p1069 (rvc p197 p881 (rvc p19 p1061 (rvc p19 p1063 (rvc p197 p887 (rvc p179 p907 (rvc p19 p1069 (rvc p3 p1087 (rvc p5 p1087 (rvc p3 p1091 (rvc p3 p1093 (rvc p11 p1087 (rvc p3 p1097 (rvc p11 p1091 (rvc p197 p907 (rvc p3 p1103 (rvc p197 p911 (rvc p19 p1091 (rvc p3 p1109 (rvc p11 p1103 (rvc p19 p1097 (rvc p499 p619 (rvc p3 p1117 (rvc p19 p1103 (rvc p7 p1117 (rvc p3 p1123 (rvc p19 p1109 (rvc p7 p1123 (rvc p3 p1129 (rvc p197 p937 (rvc p19 p1117 (rvc p197 p941 (rvc p11 p1129 (rvc p19 p1123 (rvc p197 p947 (rvc p179 p967 (rvc p19 p1129 (rvc p197 p953 (rvc p499 p653 (rvc p3 p1151 (rvc p3 p1153 (rvc p7 p1151 (rvc p7 p1153 (rvc p11 p1151 (rvc p197 p967 (rvc p3 p1163 (rvc p197 p971 (rvc p19 p1151 (rvc p19 p1153 (rvc p3 p1171 (rvc p5 p1171 (rvc p7 p1171 (rvc p197 p983 (rvc p19 p1163 (rvc p3 p1181 (rvc p5 p1181 (rvc p197 p991 (rvc p3 p1187 (rvc p11 p1181 (rvc p197 p997 (rvc p3 p1193 (rvc p11 p1187 (rvc p19 p1181 (rvc p73 p1129 (rvc p3 p1201 (rvc p19 p1187 (rvc p7 p1201 (rvc p197 p1013 (rvc p19 p1193 (rvc p277 p937 (rvc p3 p1213 (rvc p197 p1021 (rvc p3 p1217 (rvc p5 p1217 (rvc p11 p1213 (rvc p3 p1223 (rvc p197 p1031 (rvc p197 p1033 (rvc p3 p1229 (rvc p3 p1231 (rvc p19 p1217 (rvc p7 p1231 (rvc p3 p1237 (rvc p19 p1223 (rvc p7 p1237 (rvc p197 p1049 (rvc p19 p1229 (rvc p19 p1231 (rvc p3 p1249 (rvc p5 p1249 (rvc p19 p1237 (rvc p197 p1061 (rvc p197 p1063 (rvc p3 p1259 (rvc p5 p1259 (rvc p197 p1069 (rvc p19 p1249 (rvc p11 p1259 (rvc p1231 p41 (rvc p1231 p43 (rvc p179 p1097 (rvc p19 p1259 (rvc p3 p1277 (rvc p3 p1279 (rvc p197 p1087 (rvc p3 p1283 (rvc p197 p1091 (rvc p197 p1093 (rvc p3 p1289 (rvc p3 p1291 (rvc p19 p1277 (rvc p19 p1279 (rvc p3 p1297 (rvc p19 p1283 (rvc p3 p1301 (rvc p3 p1303 (rvc p19 p1289 (rvc p3 p1307 (rvc p11 p1301 (rvc p197 p1117 (rvc p19 p1297 (rvc p11 p1307 (rvc p19 p1301 (rvc p3 p1319 (rvc p3 p1321 (rvc p19 p1307 (rvc p7 p1321 (rvc p3 p1327 (rvc p11 p1321 (rvc p7 p1327 (rvc p227 p1109 (rvc p19 p1319 (rvc p19 p1321 (rvc p179 p1163 (rvc p1231 p113 (rvc p19 p1327 (rvc p197 p1151 (rvc p197 p1153 (rvc p499 p853 (rvc p401 p953 (rvc p499 p857 (rvc p1231 p127 (rvc p197 p1163 (rvc p1231 p131 (rvc p3 p1361 (rvc p5 p1361 (rvc p197 p1171 (rvc p3 p1367 (rvc p11 p1361 (rvc p7 p1367 (rvc p3 p1373 (rvc p197 p1181 (rvc p19 p1361 (rvc p1231 p151 (rvc p3 p1381 (rvc p19 p1367 (rvc p7 p1381 (rvc p197 p1193 (rvc p19 p1373 (rvc p1231 p163 (rvc p179 p1217 (rvc p197 p1201 (rvc p19 p1381 (rvc p3 p1399 (rvc p5 p1399 (rvc p7 p1399 (rvc p179 p1229 (rvc p197 p1213 (rvc p3 p1409 (rvc p197 p1217 (rvc p7 p1409 (rvc p19 p1399 (rvc p197 p1223 (rvc p1231 p191 (rvc p1231 p193 (rvc p3 p1423 (rvc p19 p1409 (rvc p3 p1427 (rvc p3 p1429 (rvc p197 p1237 (rvc p3 p1433 (rvc p11 p1427 (rvc p11 p1429 (rvc p3 p1439 (rvc p11 p1433 (rvc p19 p1427 (rvc p19 p1429 (rvc p3 p1447 (rvc p19 p1433 (rvc p3 p1451 (rvc p3 p1453 (rvc p19 p1439 (rvc p7 p1453 (rvc p3 p1459 (rvc p11 p1453 (rvc p19 p1447 (rvc p179 p1289 (rvc p19 p1451 (rvc p19 p1453 (rvc p3 p1471 (rvc p197 p1279 (rvc p19 p1459 (rvc p197 p1283 (rvc p11 p1471 (rvc p3 p1481 (rvc p3 p1483 (rvc p197 p1291 (rvc p3 p1487 (rvc p3 p1489 (rvc p197 p1297 (rvc p3 p1493 (rvc p197 p1301 (rvc p19 p1481 (rvc p3 p1499 (rvc p197 p1307 (rvc p19 p1487 (rvc p19 p1489 (rvc p11 p1499 (rvc p19 p1493 (rvc p3 p1511 (rvc p197 p1319 (rvc p19 p1499 (rvc p499 p1021 (rvc p11 p1511 (rvc p197 p1327 (rvc p3 p1523 (rvc p5 p1523 (rvc p19 p1511 (rvc p499 p1033 (rvc p3 p1531 (rvc p5 p1531 (rvc p7 p1531 (rvc p179 p1361 (rvc p19 p1523 (rvc p1231 p313 (rvc p3 p1543 (rvc p5 p1543 (rvc p19 p1531 (rvc p3 p1549 (rvc p11 p1543 (rvc p3 p1553 (rvc p197 p1361 (rvc p11 p1549 (rvc p3 p1559 (rvc p197 p1367 (rvc p7 p1559 (rvc p19 p1549 (rvc p3 p1567 (rvc p19 p1553 (rvc p3 p1571 (rvc p5 p1571 (rvc p19 p1559 (rvc p1231 p349 (rvc p3 p1579 (rvc p5 p1579 (rvc p3 p1583 (rvc p5 p1583 (rvc p19 p1571 (rvc p499 p1093 (rvc p11 p1583 (rvc p197 p1399 (rvc p19 p1579 (rvc p3 p1597 (rvc p19 p1583 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg804 (m : ℕ) (hl : 804 ≤ m) (hh : m ≤ 1603) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-804)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 804+2*k := by simp [k]; omega
  have hk : k < qg804.length := by simp [k,qg804]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg804 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg1604 : List ℕ := [1601,1409,1597,1607,1609,1607,1613,1607,1601,1619,1621,1607,1609,1627,1613,1627,1439,1619,1637,1637,1447,1627,1451,1453,421,1427,1637,1381,1657,1657,1657,1663,1471,1667,1669,1663,1657,1481,1483,1663,1487,1667,1669,1493,461,463,1693,1693,1697,1699,1693,1699,1511,1699,1709,1709,1697,1699,1523,491,1721,1723,1709,1723,1721,1723,1733,1733,1721,1723,1741,1549,1741,1747,1733,1747,1753,1747,1741,1759,1567,1747,1571,1759,1753,1373,1579,1759,1777,1777,1777,1783,1777,1787,1789,1597,1777,1601,1789,1783,1801,1787,1789,1613,1801,1811,1619,1621,1801,1811,1627,1823,1823,1811,601,1831,1831,1831,1613,1823,613,1667,617,1847,1847,1657,1579,1847,1663,631,1861,1847,1861,1867,1861,1871,1873,1867,1877,1879,1873,1867,1877,1871,1889,1697,1877,1879,1889,1723,1901,1709,1889,1907,1901,1907,1913,1721,1901,691,1913,1907,1429,1733,1913,1931,1933,1741,1933,1931,1747,1447,1721,1931,1949,1951,1759,1951,1949,1951,733,1787,1949,1951,1571,1777,1973,1973,1783,1979,1787,1789,757,1987,1973,1987,1993,1979,1997,1999,1993,2003,1811,1999,1993,2011,1997,1999,2017,2003,2017,1847,1831,2027,2029,2027,2017,2027,2029,2039,1847,2027,2029,2039,821,823,2053,2039,2053,1559,1867,2063,1871,1873,2069,1877,1879,1579,2069,2063,2081,2083,2069,2087,2089,2083,2089,1901,2081,2099,1907,2087,2089,1913,881,2111,2113,2099,2113,2111,2113,1627,1931,2111,2129,2131,2129,2131,2137,2131,2141,2143,2129,2131,2141,2143,2153,2153,2141,2143,2161,2161,2161,1973,2153,883,1979,947,2161,2179,1987,2179,1787,1993,1693,1997,1999,2179,2003,971,2131,2203,2011,2207,2207,2017,2213,2207,2213,2203,2221,2207,2221,2003,2213,2161,2039,2011,2237,2239,2237,2243,2237,2053,1021,2251,2237,2239,2063,2243,1033,2069,2089,2267,2269,2267,2273,2081,2083,1051,2281,2267,2269,2287,2273,2287,2293,2287,2297,2297,2293,2287,2111,2113,2309,2311,2297,2311,2309,2311,1093,2129,2309,2311,2153,2137,2333,2141,2143,2339,2341,2339,2341,2347,2333,2351,2351,2339,2357,2351,2357,2347,2357,2351,1873,2371,2357,2371,2377,2371,2381,2383,2377,2371,2389,2383,2393,2393,2381,2399]
private theorem vg1604 : rvld 1 1604 qg1604 := by
  unfold qg1604
  exact rvc p3 p1601 (rvc p197 p1409 (rvc p11 p1597 (rvc p3 p1607 (rvc p3 p1609 (rvc p7 p1607 (rvc p3 p1613 (rvc p11 p1607 (rvc p19 p1601 (rvc p3 p1619 (rvc p3 p1621 (rvc p19 p1607 (rvc p19 p1609 (rvc p3 p1627 (rvc p19 p1613 (rvc p7 p1627 (rvc p197 p1439 (rvc p19 p1619 (rvc p3 p1637 (rvc p5 p1637 (rvc p197 p1447 (rvc p19 p1627 (rvc p197 p1451 (rvc p197 p1453 (rvc p1231 p421 (rvc p227 p1427 (rvc p19 p1637 (rvc p277 p1381 (rvc p3 p1657 (rvc p5 p1657 (rvc p7 p1657 (rvc p3 p1663 (rvc p197 p1471 (rvc p3 p1667 (rvc p3 p1669 (rvc p11 p1663 (rvc p19 p1657 (rvc p197 p1481 (rvc p197 p1483 (rvc p19 p1663 (rvc p197 p1487 (rvc p19 p1667 (rvc p19 p1669 (rvc p197 p1493 (rvc p1231 p461 (rvc p1231 p463 (rvc p3 p1693 (rvc p5 p1693 (rvc p3 p1697 (rvc p3 p1699 (rvc p11 p1693 (rvc p7 p1699 (rvc p197 p1511 (rvc p11 p1699 (rvc p3 p1709 (rvc p5 p1709 (rvc p19 p1697 (rvc p19 p1699 (rvc p197 p1523 (rvc p1231 p491 (rvc p3 p1721 (rvc p3 p1723 (rvc p19 p1709 (rvc p7 p1723 (rvc p11 p1721 (rvc p11 p1723 (rvc p3 p1733 (rvc p5 p1733 (rvc p19 p1721 (rvc p19 p1723 (rvc p3 p1741 (rvc p197 p1549 (rvc p7 p1741 (rvc p3 p1747 (rvc p19 p1733 (rvc p7 p1747 (rvc p3 p1753 (rvc p11 p1747 (rvc p19 p1741 (rvc p3 p1759 (rvc p197 p1567 (rvc p19 p1747 (rvc p197 p1571 (rvc p11 p1759 (rvc p19 p1753 (rvc p401 p1373 (rvc p197 p1579 (rvc p19 p1759 (rvc p3 p1777 (rvc p5 p1777 (rvc p7 p1777 (rvc p3 p1783 (rvc p11 p1777 (rvc p3 p1787 (rvc p3 p1789 (rvc p197 p1597 (rvc p19 p1777 (rvc p197 p1601 (rvc p11 p1789 (rvc p19 p1783 (rvc p3 p1801 (rvc p19 p1787 (rvc p19 p1789 (rvc p197 p1613 (rvc p11 p1801 (rvc p3 p1811 (rvc p197 p1619 (rvc p197 p1621 (rvc p19 p1801 (rvc p11 p1811 (rvc p197 p1627 (rvc p3 p1823 (rvc p5 p1823 (rvc p19 p1811 (rvc p1231 p601 (rvc p3 p1831 (rvc p5 p1831 (rvc p7 p1831 (rvc p227 p1613 (rvc p19 p1823 (rvc p1231 p613 (rvc p179 p1667 (rvc p1231 p617 (rvc p3 p1847 (rvc p5 p1847 (rvc p197 p1657 (rvc p277 p1579 (rvc p11 p1847 (rvc p197 p1663 (rvc p1231 p631 (rvc p3 p1861 (rvc p19 p1847 (rvc p7 p1861 (rvc p3 p1867 (rvc p11 p1861 (rvc p3 p1871 (rvc p3 p1873 (rvc p11 p1867 (rvc p3 p1877 (rvc p3 p1879 (rvc p11 p1873 (rvc p19 p1867 (rvc p11 p1877 (rvc p19 p1871 (rvc p3 p1889 (rvc p197 p1697 (rvc p19 p1877 (rvc p19 p1879 (rvc p11 p1889 (rvc p179 p1723 (rvc p3 p1901 (rvc p197 p1709 (rvc p19 p1889 (rvc p3 p1907 (rvc p11 p1901 (rvc p7 p1907 (rvc p3 p1913 (rvc p197 p1721 (rvc p19 p1901 (rvc p1231 p691 (rvc p11 p1913 (rvc p19 p1907 (rvc p499 p1429 (rvc p197 p1733 (rvc p19 p1913 (rvc p3 p1931 (rvc p3 p1933 (rvc p197 p1741 (rvc p7 p1933 (rvc p11 p1931 (rvc p197 p1747 (rvc p499 p1447 (rvc p227 p1721 (rvc p19 p1931 (rvc p3 p1949 (rvc p3 p1951 (rvc p197 p1759 (rvc p7 p1951 (rvc p11 p1949 (rvc p11 p1951 (rvc p1231 p733 (rvc p179 p1787 (rvc p19 p1949 (rvc p19 p1951 (rvc p401 p1571 (rvc p197 p1777 (rvc p3 p1973 (rvc p5 p1973 (rvc p197 p1783 (rvc p3 p1979 (rvc p197 p1787 (rvc p197 p1789 (rvc p1231 p757 (rvc p3 p1987 (rvc p19 p1973 (rvc p7 p1987 (rvc p3 p1993 (rvc p19 p1979 (rvc p3 p1997 (rvc p3 p1999 (rvc p11 p1993 (rvc p3 p2003 (rvc p197 p1811 (rvc p11 p1999 (rvc p19 p1993 (rvc p3 p2011 (rvc p19 p1997 (rvc p19 p1999 (rvc p3 p2017 (rvc p19 p2003 (rvc p7 p2017 (rvc p179 p1847 (rvc p197 p1831 (rvc p3 p2027 (rvc p3 p2029 (rvc p7 p2027 (rvc p19 p2017 (rvc p11 p2027 (rvc p11 p2029 (rvc p3 p2039 (rvc p197 p1847 (rvc p19 p2027 (rvc p19 p2029 (rvc p11 p2039 (rvc p1231 p821 (rvc p1231 p823 (rvc p3 p2053 (rvc p19 p2039 (rvc p7 p2053 (rvc p503 p1559 (rvc p197 p1867 (rvc p3 p2063 (rvc p197 p1871 (rvc p197 p1873 (rvc p3 p2069 (rvc p197 p1877 (rvc p197 p1879 (rvc p499 p1579 (rvc p11 p2069 (rvc p19 p2063 (rvc p3 p2081 (rvc p3 p2083 (rvc p19 p2069 (rvc p3 p2087 (rvc p3 p2089 (rvc p11 p2083 (rvc p7 p2089 (rvc p197 p1901 (rvc p19 p2081 (rvc p3 p2099 (rvc p197 p1907 (rvc p19 p2087 (rvc p19 p2089 (rvc p197 p1913 (rvc p1231 p881 (rvc p3 p2111 (rvc p3 p2113 (rvc p19 p2099 (rvc p7 p2113 (rvc p11 p2111 (rvc p11 p2113 (rvc p499 p1627 (rvc p197 p1931 (rvc p19 p2111 (rvc p3 p2129 (rvc p3 p2131 (rvc p7 p2129 (rvc p7 p2131 (rvc p3 p2137 (rvc p11 p2131 (rvc p3 p2141 (rvc p3 p2143 (rvc p19 p2129 (rvc p19 p2131 (rvc p11 p2141 (rvc p11 p2143 (rvc p3 p2153 (rvc p5 p2153 (rvc p19 p2141 (rvc p19 p2143 (rvc p3 p2161 (rvc p5 p2161 (rvc p7 p2161 (rvc p197 p1973 (rvc p19 p2153 (rvc p1291 p883 (rvc p197 p1979 (rvc p1231 p947 (rvc p19 p2161 (rvc p3 p2179 (rvc p197 p1987 (rvc p7 p2179 (rvc p401 p1787 (rvc p197 p1993 (rvc p499 p1693 (rvc p197 p1997 (rvc p197 p1999 (rvc p19 p2179 (rvc p197 p2003 (rvc p1231 p971 (rvc p73 p2131 (rvc p3 p2203 (rvc p197 p2011 (rvc p3 p2207 (rvc p5 p2207 (rvc p197 p2017 (rvc p3 p2213 (rvc p11 p2207 (rvc p7 p2213 (rvc p19 p2203 (rvc p3 p2221 (rvc p19 p2207 (rvc p7 p2221 (rvc p227 p2003 (rvc p19 p2213 (rvc p73 p2161 (rvc p197 p2039 (rvc p227 p2011 (rvc p3 p2237 (rvc p3 p2239 (rvc p7 p2237 (rvc p3 p2243 (rvc p11 p2237 (rvc p197 p2053 (rvc p1231 p1021 (rvc p3 p2251 (rvc p19 p2237 (rvc p19 p2239 (rvc p197 p2063 (rvc p19 p2243 (rvc p1231 p1033 (rvc p197 p2069 (rvc p179 p2089 (rvc p3 p2267 (rvc p3 p2269 (rvc p7 p2267 (rvc p3 p2273 (rvc p197 p2081 (rvc p197 p2083 (rvc p1231 p1051 (rvc p3 p2281 (rvc p19 p2267 (rvc p19 p2269 (rvc p3 p2287 (rvc p19 p2273 (rvc p7 p2287 (rvc p3 p2293 (rvc p11 p2287 (rvc p3 p2297 (rvc p5 p2297 (rvc p11 p2293 (rvc p19 p2287 (rvc p197 p2111 (rvc p197 p2113 (rvc p3 p2309 (rvc p3 p2311 (rvc p19 p2297 (rvc p7 p2311 (rvc p11 p2309 (rvc p11 p2311 (rvc p1231 p1093 (rvc p197 p2129 (rvc p19 p2309 (rvc p19 p2311 (rvc p179 p2153 (rvc p197 p2137 (rvc p3 p2333 (rvc p197 p2141 (rvc p197 p2143 (rvc p3 p2339 (rvc p3 p2341 (rvc p7 p2339 (rvc p7 p2341 (rvc p3 p2347 (rvc p19 p2333 (rvc p3 p2351 (rvc p5 p2351 (rvc p19 p2339 (rvc p3 p2357 (rvc p11 p2351 (rvc p7 p2357 (rvc p19 p2347 (rvc p11 p2357 (rvc p19 p2351 (rvc p499 p1873 (rvc p3 p2371 (rvc p19 p2357 (rvc p7 p2371 (rvc p3 p2377 (rvc p11 p2371 (rvc p3 p2381 (rvc p3 p2383 (rvc p11 p2377 (rvc p19 p2371 (rvc p3 p2389 (rvc p11 p2383 (rvc p3 p2393 (rvc p5 p2393 (rvc p19 p2381 (rvc p3 p2399 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg1604 (m : ℕ) (hl : 1604 ≤ m) (hh : m ≤ 2403) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-1604)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 1604+2*k := by simp [k]; omega
  have hk : k < qg1604.length := by simp [k,qg1604]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg1604 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg2404 : List ℕ := [2207,2399,2389,2213,2393,2411,2411,2399,2417,2411,2417,2423,2417,2411,1201,2237,2417,2161,2437,2423,2441,2441,2251,2447,2441,2447,2437,2447,2441,2459,2267,2447,1237,2467,2467,2467,2473,2459,2477,2477,2287,2467,2477,2293,2473,2297,2477,1999,2273,2003,1213,2503,2311,2503,2333,2503,2017,2339,1289,2503,2521,2521,2521,2333,2521,2531,2339,2341,2521,2539,2347,2543,2351,2531,2549,2551,2549,2539,2557,2543,2557,2339,2549,2551,2393,2377,2557,2381,2383,2579,2579,2389,2089,2393,1361,2591,2593,2579,2593,2591,2593,2467,2411,2591,2609,2417,2609,2341,2617,2617,2621,2621,2609,1399,2621,2437,2633,2441,2621,2143,2447,2467,2371,2647,2633,2647,2459,2647,2657,2659,2467,2663,2657,2473,1381,2671,2657,2659,2677,2663,2677,2683,2677,2687,2689,2683,2693,2687,2503,2699,2693,2687,2689,2707,2693,2711,2713,2699,2713,2719,2713,2707,2531,2711,2729,2731,2539,2719,2543,2731,2741,2549,2729,2731,2749,2557,2753,2753,2741,1531,2753,2267,2749,2767,2753,2767,2579,2767,2777,2777,2777,2767,2591,2593,2789,2791,2777,2791,2797,2791,2801,2803,2789,2791,2801,2617,2797,2621,2801,2819,2819,2819,1597,2633,1601,2557,2833,2819,2837,2837,2647,2843,2837,2843,2833,2851,2837,2851,2857,2843,2861,2861,2671,2851,2861,2677,2857,2699,2861,2879,2687,2689,1657,2887,2887,2887,2699,2879,2897,2897,2707,2903,2711,2713,2909,2903,2897,1627,2917,2903,2917,2729,2909,2927,2927,2927,2917,2741,1709,2939,2939,2927,2671,2753,1721,1723,2953,2939,2957,2957,2767,2963,2957,2963,2969,2971,2957,2971,2969,2963,1753,2789,2969,2971,2591,2797,2719,2801,2803,2999,3001,2999,3001,2999,3001,3011,2819,2999,3001,3019,3019,3023,3023,3011,1801,2837,2857,3019,3037,3023,3041,3041,2851,2551,3049,2857,3037,2861,3041,1831,3061,3061,3049,3067,3061,3067,2879,3067,3061,3079,2887,3083,3083,3079,3089,2897,3089,3079,2903,3083,1873,2909,3089,1879,3109,2917,3109,2939,3109,3119,3121,3119,3109,3119,3121,2857,2939,3119,3137,3137,3137,2647,3137,2953,1861,2957,3137,2659,2963,1931,1933,3163,2971,3167,3169,3163,3169,3167,3169,3163,3181,3167,3169,3187,3181,3191,2999,3001,3181,3191]
private theorem vg2404 : rvld 1 2404 qg2404 := by
  unfold qg2404
  exact rvc p197 p2207 (rvc p7 p2399 (rvc p19 p2389 (rvc p197 p2213 (rvc p19 p2393 (rvc p3 p2411 (rvc p5 p2411 (rvc p19 p2399 (rvc p3 p2417 (rvc p11 p2411 (rvc p7 p2417 (rvc p3 p2423 (rvc p11 p2417 (rvc p19 p2411 (rvc p1231 p1201 (rvc p197 p2237 (rvc p19 p2417 (rvc p277 p2161 (rvc p3 p2437 (rvc p19 p2423 (rvc p3 p2441 (rvc p5 p2441 (rvc p197 p2251 (rvc p3 p2447 (rvc p11 p2441 (rvc p7 p2447 (rvc p19 p2437 (rvc p11 p2447 (rvc p19 p2441 (rvc p3 p2459 (rvc p197 p2267 (rvc p19 p2447 (rvc p1231 p1237 (rvc p3 p2467 (rvc p5 p2467 (rvc p7 p2467 (rvc p3 p2473 (rvc p19 p2459 (rvc p3 p2477 (rvc p5 p2477 (rvc p197 p2287 (rvc p19 p2467 (rvc p11 p2477 (rvc p197 p2293 (rvc p19 p2473 (rvc p197 p2297 (rvc p19 p2477 (rvc p499 p1999 (rvc p227 p2273 (rvc p499 p2003 (rvc p1291 p1213 (rvc p3 p2503 (rvc p197 p2311 (rvc p7 p2503 (rvc p179 p2333 (rvc p11 p2503 (rvc p499 p2017 (rvc p179 p2339 (rvc p1231 p1289 (rvc p19 p2503 (rvc p3 p2521 (rvc p5 p2521 (rvc p7 p2521 (rvc p197 p2333 (rvc p11 p2521 (rvc p3 p2531 (rvc p197 p2339 (rvc p197 p2341 (rvc p19 p2521 (rvc p3 p2539 (rvc p197 p2347 (rvc p3 p2543 (rvc p197 p2351 (rvc p19 p2531 (rvc p3 p2549 (rvc p3 p2551 (rvc p7 p2549 (rvc p19 p2539 (rvc p3 p2557 (rvc p19 p2543 (rvc p7 p2557 (rvc p227 p2339 (rvc p19 p2549 (rvc p19 p2551 (rvc p179 p2393 (rvc p197 p2377 (rvc p19 p2557 (rvc p197 p2381 (rvc p197 p2383 (rvc p3 p2579 (rvc p5 p2579 (rvc p197 p2389 (rvc p499 p2089 (rvc p197 p2393 (rvc p1231 p1361 (rvc p3 p2591 (rvc p3 p2593 (rvc p19 p2579 (rvc p7 p2593 (rvc p11 p2591 (rvc p11 p2593 (rvc p139 p2467 (rvc p197 p2411 (rvc p19 p2591 (rvc p3 p2609 (rvc p197 p2417 (rvc p7 p2609 (rvc p277 p2341 (rvc p3 p2617 (rvc p5 p2617 (rvc p3 p2621 (rvc p5 p2621 (rvc p19 p2609 (rvc p1231 p1399 (rvc p11 p2621 (rvc p197 p2437 (rvc p3 p2633 (rvc p197 p2441 (rvc p19 p2621 (rvc p499 p2143 (rvc p197 p2447 (rvc p179 p2467 (rvc p277 p2371 (rvc p3 p2647 (rvc p19 p2633 (rvc p7 p2647 (rvc p197 p2459 (rvc p11 p2647 (rvc p3 p2657 (rvc p3 p2659 (rvc p197 p2467 (rvc p3 p2663 (rvc p11 p2657 (rvc p197 p2473 (rvc p1291 p1381 (rvc p3 p2671 (rvc p19 p2657 (rvc p19 p2659 (rvc p3 p2677 (rvc p19 p2663 (rvc p7 p2677 (rvc p3 p2683 (rvc p11 p2677 (rvc p3 p2687 (rvc p3 p2689 (rvc p11 p2683 (rvc p3 p2693 (rvc p11 p2687 (rvc p197 p2503 (rvc p3 p2699 (rvc p11 p2693 (rvc p19 p2687 (rvc p19 p2689 (rvc p3 p2707 (rvc p19 p2693 (rvc p3 p2711 (rvc p3 p2713 (rvc p19 p2699 (rvc p7 p2713 (rvc p3 p2719 (rvc p11 p2713 (rvc p19 p2707 (rvc p197 p2531 (rvc p19 p2711 (rvc p3 p2729 (rvc p3 p2731 (rvc p197 p2539 (rvc p19 p2719 (rvc p197 p2543 (rvc p11 p2731 (rvc p3 p2741 (rvc p197 p2549 (rvc p19 p2729 (rvc p19 p2731 (rvc p3 p2749 (rvc p197 p2557 (rvc p3 p2753 (rvc p5 p2753 (rvc p19 p2741 (rvc p1231 p1531 (rvc p11 p2753 (rvc p499 p2267 (rvc p19 p2749 (rvc p3 p2767 (rvc p19 p2753 (rvc p7 p2767 (rvc p197 p2579 (rvc p11 p2767 (rvc p3 p2777 (rvc p5 p2777 (rvc p7 p2777 (rvc p19 p2767 (rvc p197 p2591 (rvc p197 p2593 (rvc p3 p2789 (rvc p3 p2791 (rvc p19 p2777 (rvc p7 p2791 (rvc p3 p2797 (rvc p11 p2791 (rvc p3 p2801 (rvc p3 p2803 (rvc p19 p2789 (rvc p19 p2791 (rvc p11 p2801 (rvc p197 p2617 (rvc p19 p2797 (rvc p197 p2621 (rvc p19 p2801 (rvc p3 p2819 (rvc p5 p2819 (rvc p7 p2819 (rvc p1231 p1597 (rvc p197 p2633 (rvc p1231 p1601 (rvc p277 p2557 (rvc p3 p2833 (rvc p19 p2819 (rvc p3 p2837 (rvc p5 p2837 (rvc p197 p2647 (rvc p3 p2843 (rvc p11 p2837 (rvc p7 p2843 (rvc p19 p2833 (rvc p3 p2851 (rvc p19 p2837 (rvc p7 p2851 (rvc p3 p2857 (rvc p19 p2843 (rvc p3 p2861 (rvc p5 p2861 (rvc p197 p2671 (rvc p19 p2851 (rvc p11 p2861 (rvc p197 p2677 (rvc p19 p2857 (rvc p179 p2699 (rvc p19 p2861 (rvc p3 p2879 (rvc p197 p2687 (rvc p197 p2689 (rvc p1231 p1657 (rvc p3 p2887 (rvc p5 p2887 (rvc p7 p2887 (rvc p197 p2699 (rvc p19 p2879 (rvc p3 p2897 (rvc p5 p2897 (rvc p197 p2707 (rvc p3 p2903 (rvc p197 p2711 (rvc p197 p2713 (rvc p3 p2909 (rvc p11 p2903 (rvc p19 p2897 (rvc p1291 p1627 (rvc p3 p2917 (rvc p19 p2903 (rvc p7 p2917 (rvc p197 p2729 (rvc p19 p2909 (rvc p3 p2927 (rvc p5 p2927 (rvc p7 p2927 (rvc p19 p2917 (rvc p197 p2741 (rvc p1231 p1709 (rvc p3 p2939 (rvc p5 p2939 (rvc p19 p2927 (rvc p277 p2671 (rvc p197 p2753 (rvc p1231 p1721 (rvc p1231 p1723 (rvc p3 p2953 (rvc p19 p2939 (rvc p3 p2957 (rvc p5 p2957 (rvc p197 p2767 (rvc p3 p2963 (rvc p11 p2957 (rvc p7 p2963 (rvc p3 p2969 (rvc p3 p2971 (rvc p19 p2957 (rvc p7 p2971 (rvc p11 p2969 (rvc p19 p2963 (rvc p1231 p1753 (rvc p197 p2789 (rvc p19 p2969 (rvc p19 p2971 (rvc p401 p2591 (rvc p197 p2797 (rvc p277 p2719 (rvc p197 p2801 (rvc p197 p2803 (rvc p3 p2999 (rvc p3 p3001 (rvc p7 p2999 (rvc p7 p3001 (rvc p11 p2999 (rvc p11 p3001 (rvc p3 p3011 (rvc p197 p2819 (rvc p19 p2999 (rvc p19 p3001 (rvc p3 p3019 (rvc p5 p3019 (rvc p3 p3023 (rvc p5 p3023 (rvc p19 p3011 (rvc p1231 p1801 (rvc p197 p2837 (rvc p179 p2857 (rvc p19 p3019 (rvc p3 p3037 (rvc p19 p3023 (rvc p3 p3041 (rvc p5 p3041 (rvc p197 p2851 (rvc p499 p2551 (rvc p3 p3049 (rvc p197 p2857 (rvc p19 p3037 (rvc p197 p2861 (rvc p19 p3041 (rvc p1231 p1831 (rvc p3 p3061 (rvc p5 p3061 (rvc p19 p3049 (rvc p3 p3067 (rvc p11 p3061 (rvc p7 p3067 (rvc p197 p2879 (rvc p11 p3067 (rvc p19 p3061 (rvc p3 p3079 (rvc p197 p2887 (rvc p3 p3083 (rvc p5 p3083 (rvc p11 p3079 (rvc p3 p3089 (rvc p197 p2897 (rvc p7 p3089 (rvc p19 p3079 (rvc p197 p2903 (rvc p19 p3083 (rvc p1231 p1873 (rvc p197 p2909 (rvc p19 p3089 (rvc p1231 p1879 (rvc p3 p3109 (rvc p197 p2917 (rvc p7 p3109 (rvc p179 p2939 (rvc p11 p3109 (rvc p3 p3119 (rvc p3 p3121 (rvc p7 p3119 (rvc p19 p3109 (rvc p11 p3119 (rvc p11 p3121 (rvc p277 p2857 (rvc p197 p2939 (rvc p19 p3119 (rvc p3 p3137 (rvc p5 p3137 (rvc p7 p3137 (rvc p499 p2647 (rvc p11 p3137 (rvc p197 p2953 (rvc p1291 p1861 (rvc p197 p2957 (rvc p19 p3137 (rvc p499 p2659 (rvc p197 p2963 (rvc p1231 p1931 (rvc p1231 p1933 (rvc p3 p3163 (rvc p197 p2971 (rvc p3 p3167 (rvc p3 p3169 (rvc p11 p3163 (rvc p7 p3169 (rvc p11 p3167 (rvc p11 p3169 (rvc p19 p3163 (rvc p3 p3181 (rvc p19 p3167 (rvc p19 p3169 (rvc p3 p3187 (rvc p11 p3181 (rvc p3 p3191 (rvc p197 p2999 (rvc p197 p3001 (rvc p19 p3181 (rvc p11 p3191 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg2404 (m : ℕ) (hl : 2404 ≤ m) (hh : m ≤ 3203) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-2404)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 2404+2*k := by simp [k]; omega
  have hk : k < qg2404.length := by simp [k,qg2404]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg2404 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg3204 : List ℕ := [1973,3203,3011,3191,3209,3203,3019,1987,3217,3203,3221,3221,3209,1999,3229,3037,3217,3041,3221,2011,2843,3049,3229,3023,2753,3251,3253,3061,3257,3259,3067,3259,3257,3251,3253,3271,3257,3259,3083,3271,2053,3089,3109,3271,2789,2063,2797,3119,2069,3299,3301,3109,3301,3307,3301,3307,3313,3299,3301,3319,3313,3323,3323,3319,3329,3331,3329,3319,3329,3323,2113,3343,3329,3347,3347,3343,2857,3347,3163,3359,3361,3347,3361,3359,3361,3371,3373,3359,3361,3371,3187,2887,3191,3371,3389,3391,3389,3391,3203,3391,2113,3209,3389,3407,3407,3217,3413,3221,3413,2131,3413,3407,2137,3251,3413,2203,3433,3433,3433,3041,3433,3169,3251,3253,3449,3257,3259,3181,3457,3457,3461,3463,3449,3467,3469,3463,3457,3467,3461,3463,3257,3467,3469,3089,3313,3491,3299,3301,2269,3499,3307,3499,3329,3491,2281,3511,3319,3499,3517,3511,3517,3329,3331,3527,3529,3527,3533,3527,3343,3539,3541,3527,3529,3547,3533,3547,3359,3539,3557,3559,3557,3547,3371,3373,2341,3571,3557,3559,1601,3571,3581,3583,3391,3571,3581,3583,3593,3593,3581,3583,3407,3329,2377,3607,3593,3607,3613,3607,3617,3617,3613,3623,3617,3433,3613,3631,3617,3631,3637,3623,3637,3643,3637,3631,3251,3457,3637,3461,3463,3659,3467,3469,2437,3659,2441,3671,3673,3659,3677,3671,3673,3187,3491,3671,3673,3691,3677,3691,3697,3691,3701,3701,3511,3691,3709,3517,3697,3539,3701,3719,3527,3529,3709,3727,3727,3727,3733,3719,3733,3739,3547,3727,3347,3739,3733,3557,3559,3739,3581,2531,3761,3761,3571,3767,3769,3767,3769,3581,3761,3779,3779,3767,3769,3593,3613,3517,3793,3779,3797,3797,3607,3803,3797,3613,3793,3617,3797,3319,3623,3803,3821,3823,3631,3823,3821,3637,3833,3833,3821,3823,3833,3347,2617,3847,3833,3851,3853,3847,3853,3851,3853,3863,3671,3851,3853,3677,3697,2647,3877,3863,3881,3881,3691,2659,3889,3697,3877,3701,3881,2671,3677,3709,3889,3907,3907,3911,3719,3907,3917,3919,3727,3923,3917,3911,3929,3931,3917,3919,3929,3923,2713,3943,3929,3947,3947,3943,3457,3761,2729,3943,3767,3947,3469,3967,3967,3967,3779,3967,2749,3803,2753,3967,3761,3793,3989,3797,3989,2767,3803,3823]
private theorem vg3204 : rvld 1 3204 qg3204 := by
  unfold qg3204
  exact rvc p1231 p1973 (rvc p3 p3203 (rvc p197 p3011 (rvc p19 p3191 (rvc p3 p3209 (rvc p11 p3203 (rvc p197 p3019 (rvc p1231 p1987 (rvc p3 p3217 (rvc p19 p3203 (rvc p3 p3221 (rvc p5 p3221 (rvc p19 p3209 (rvc p1231 p1999 (rvc p3 p3229 (rvc p197 p3037 (rvc p19 p3217 (rvc p197 p3041 (rvc p19 p3221 (rvc p1231 p2011 (rvc p401 p2843 (rvc p197 p3049 (rvc p19 p3229 (rvc p227 p3023 (rvc p499 p2753 (rvc p3 p3251 (rvc p3 p3253 (rvc p197 p3061 (rvc p3 p3257 (rvc p3 p3259 (rvc p197 p3067 (rvc p7 p3259 (rvc p11 p3257 (rvc p19 p3251 (rvc p19 p3253 (rvc p3 p3271 (rvc p19 p3257 (rvc p19 p3259 (rvc p197 p3083 (rvc p11 p3271 (rvc p1231 p2053 (rvc p197 p3089 (rvc p179 p3109 (rvc p19 p3271 (rvc p503 p2789 (rvc p1231 p2063 (rvc p499 p2797 (rvc p179 p3119 (rvc p1231 p2069 (rvc p3 p3299 (rvc p3 p3301 (rvc p197 p3109 (rvc p7 p3301 (rvc p3 p3307 (rvc p11 p3301 (rvc p7 p3307 (rvc p3 p3313 (rvc p19 p3299 (rvc p19 p3301 (rvc p3 p3319 (rvc p11 p3313 (rvc p3 p3323 (rvc p5 p3323 (rvc p11 p3319 (rvc p3 p3329 (rvc p3 p3331 (rvc p7 p3329 (rvc p19 p3319 (rvc p11 p3329 (rvc p19 p3323 (rvc p1231 p2113 (rvc p3 p3343 (rvc p19 p3329 (rvc p3 p3347 (rvc p5 p3347 (rvc p11 p3343 (rvc p499 p2857 (rvc p11 p3347 (rvc p197 p3163 (rvc p3 p3359 (rvc p3 p3361 (rvc p19 p3347 (rvc p7 p3361 (rvc p11 p3359 (rvc p11 p3361 (rvc p3 p3371 (rvc p3 p3373 (rvc p19 p3359 (rvc p19 p3361 (rvc p11 p3371 (rvc p197 p3187 (rvc p499 p2887 (rvc p197 p3191 (rvc p19 p3371 (rvc p3 p3389 (rvc p3 p3391 (rvc p7 p3389 (rvc p7 p3391 (rvc p197 p3203 (rvc p11 p3391 (rvc p1291 p2113 (rvc p197 p3209 (rvc p19 p3389 (rvc p3 p3407 (rvc p5 p3407 (rvc p197 p3217 (rvc p3 p3413 (rvc p197 p3221 (rvc p7 p3413 (rvc p1291 p2131 (rvc p11 p3413 (rvc p19 p3407 (rvc p1291 p2137 (rvc p179 p3251 (rvc p19 p3413 (rvc p1231 p2203 (rvc p3 p3433 (rvc p5 p3433 (rvc p7 p3433 (rvc p401 p3041 (rvc p11 p3433 (rvc p277 p3169 (rvc p197 p3251 (rvc p197 p3253 (rvc p3 p3449 (rvc p197 p3257 (rvc p197 p3259 (rvc p277 p3181 (rvc p3 p3457 (rvc p5 p3457 (rvc p3 p3461 (rvc p3 p3463 (rvc p19 p3449 (rvc p3 p3467 (rvc p3 p3469 (rvc p11 p3463 (rvc p19 p3457 (rvc p11 p3467 (rvc p19 p3461 (rvc p19 p3463 (rvc p227 p3257 (rvc p19 p3467 (rvc p19 p3469 (rvc p401 p3089 (rvc p179 p3313 (rvc p3 p3491 (rvc p197 p3299 (rvc p197 p3301 (rvc p1231 p2269 (rvc p3 p3499 (rvc p197 p3307 (rvc p7 p3499 (rvc p179 p3329 (rvc p19 p3491 (rvc p1231 p2281 (rvc p3 p3511 (rvc p197 p3319 (rvc p19 p3499 (rvc p3 p3517 (rvc p11 p3511 (rvc p7 p3517 (rvc p197 p3329 (rvc p197 p3331 (rvc p3 p3527 (rvc p3 p3529 (rvc p7 p3527 (rvc p3 p3533 (rvc p11 p3527 (rvc p197 p3343 (rvc p3 p3539 (rvc p3 p3541 (rvc p19 p3527 (rvc p19 p3529 (rvc p3 p3547 (rvc p19 p3533 (rvc p7 p3547 (rvc p197 p3359 (rvc p19 p3539 (rvc p3 p3557 (rvc p3 p3559 (rvc p7 p3557 (rvc p19 p3547 (rvc p197 p3371 (rvc p197 p3373 (rvc p1231 p2341 (rvc p3 p3571 (rvc p19 p3557 (rvc p19 p3559 (rvc p1979 p1601 (rvc p11 p3571 (rvc p3 p3581 (rvc p3 p3583 (rvc p197 p3391 (rvc p19 p3571 (rvc p11 p3581 (rvc p11 p3583 (rvc p3 p3593 (rvc p5 p3593 (rvc p19 p3581 (rvc p19 p3583 (rvc p197 p3407 (rvc p277 p3329 (rvc p1231 p2377 (rvc p3 p3607 (rvc p19 p3593 (rvc p7 p3607 (rvc p3 p3613 (rvc p11 p3607 (rvc p3 p3617 (rvc p5 p3617 (rvc p11 p3613 (rvc p3 p3623 (rvc p11 p3617 (rvc p197 p3433 (rvc p19 p3613 (rvc p3 p3631 (rvc p19 p3617 (rvc p7 p3631 (rvc p3 p3637 (rvc p19 p3623 (rvc p7 p3637 (rvc p3 p3643 (rvc p11 p3637 (rvc p19 p3631 (rvc p401 p3251 (rvc p197 p3457 (rvc p19 p3637 (rvc p197 p3461 (rvc p197 p3463 (rvc p3 p3659 (rvc p197 p3467 (rvc p197 p3469 (rvc p1231 p2437 (rvc p11 p3659 (rvc p1231 p2441 (rvc p3 p3671 (rvc p3 p3673 (rvc p19 p3659 (rvc p3 p3677 (rvc p11 p3671 (rvc p11 p3673 (rvc p499 p3187 (rvc p197 p3491 (rvc p19 p3671 (rvc p19 p3673 (rvc p3 p3691 (rvc p19 p3677 (rvc p7 p3691 (rvc p3 p3697 (rvc p11 p3691 (rvc p3 p3701 (rvc p5 p3701 (rvc p197 p3511 (rvc p19 p3691 (rvc p3 p3709 (rvc p197 p3517 (rvc p19 p3697 (rvc p179 p3539 (rvc p19 p3701 (rvc p3 p3719 (rvc p197 p3527 (rvc p197 p3529 (rvc p19 p3709 (rvc p3 p3727 (rvc p5 p3727 (rvc p7 p3727 (rvc p3 p3733 (rvc p19 p3719 (rvc p7 p3733 (rvc p3 p3739 (rvc p197 p3547 (rvc p19 p3727 (rvc p401 p3347 (rvc p11 p3739 (rvc p19 p3733 (rvc p197 p3557 (rvc p197 p3559 (rvc p19 p3739 (rvc p179 p3581 (rvc p1231 p2531 (rvc p3 p3761 (rvc p5 p3761 (rvc p197 p3571 (rvc p3 p3767 (rvc p3 p3769 (rvc p7 p3767 (rvc p7 p3769 (rvc p197 p3581 (rvc p19 p3761 (rvc p3 p3779 (rvc p5 p3779 (rvc p19 p3767 (rvc p19 p3769 (rvc p197 p3593 (rvc p179 p3613 (rvc p277 p3517 (rvc p3 p3793 (rvc p19 p3779 (rvc p3 p3797 (rvc p5 p3797 (rvc p197 p3607 (rvc p3 p3803 (rvc p11 p3797 (rvc p197 p3613 (rvc p19 p3793 (rvc p197 p3617 (rvc p19 p3797 (rvc p499 p3319 (rvc p197 p3623 (rvc p19 p3803 (rvc p3 p3821 (rvc p3 p3823 (rvc p197 p3631 (rvc p7 p3823 (rvc p11 p3821 (rvc p197 p3637 (rvc p3 p3833 (rvc p5 p3833 (rvc p19 p3821 (rvc p19 p3823 (rvc p11 p3833 (rvc p499 p3347 (rvc p1231 p2617 (rvc p3 p3847 (rvc p19 p3833 (rvc p3 p3851 (rvc p3 p3853 (rvc p11 p3847 (rvc p7 p3853 (rvc p11 p3851 (rvc p11 p3853 (rvc p3 p3863 (rvc p197 p3671 (rvc p19 p3851 (rvc p19 p3853 (rvc p197 p3677 (rvc p179 p3697 (rvc p1231 p2647 (rvc p3 p3877 (rvc p19 p3863 (rvc p3 p3881 (rvc p5 p3881 (rvc p197 p3691 (rvc p1231 p2659 (rvc p3 p3889 (rvc p197 p3697 (rvc p19 p3877 (rvc p197 p3701 (rvc p19 p3881 (rvc p1231 p2671 (rvc p227 p3677 (rvc p197 p3709 (rvc p19 p3889 (rvc p3 p3907 (rvc p5 p3907 (rvc p3 p3911 (rvc p197 p3719 (rvc p11 p3907 (rvc p3 p3917 (rvc p3 p3919 (rvc p197 p3727 (rvc p3 p3923 (rvc p11 p3917 (rvc p19 p3911 (rvc p3 p3929 (rvc p3 p3931 (rvc p19 p3917 (rvc p19 p3919 (rvc p11 p3929 (rvc p19 p3923 (rvc p1231 p2713 (rvc p3 p3943 (rvc p19 p3929 (rvc p3 p3947 (rvc p5 p3947 (rvc p11 p3943 (rvc p499 p3457 (rvc p197 p3761 (rvc p1231 p2729 (rvc p19 p3943 (rvc p197 p3767 (rvc p19 p3947 (rvc p499 p3469 (rvc p3 p3967 (rvc p5 p3967 (rvc p7 p3967 (rvc p197 p3779 (rvc p11 p3967 (rvc p1231 p2749 (rvc p179 p3803 (rvc p1231 p2753 (rvc p19 p3967 (rvc p227 p3761 (rvc p197 p3793 (rvc p3 p3989 (rvc p197 p3797 (rvc p7 p3989 (rvc p1231 p2767 (rvc p197 p3803 (rvc p179 p3823 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg3204 (m : ℕ) (hl : 3204 ≤ m) (hh : m ≤ 4003) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-3204)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 3204+2*k := by simp [k]; omega
  have hk : k < qg3204.length := by simp [k,qg3204]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg3204 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg4004 : List ℕ := [4001,4003,3989,4007,4001,4003,4013,3821,4001,4019,4021,4007,4021,4027,4013,4027,3533,4019,4021,3863,3847,4027,3851,3853,4049,4051,4049,4051,4057,4051,4057,2087,4049,4051,3671,3877,4073,3881,4073,4079,4073,3889,2857,4079,4073,4091,4093,4079,4093,4099,3907,4099,3911,4091,4093,4111,3919,4099,3923,4111,3847,3929,3931,4127,4129,4127,4133,4127,3943,4139,3947,4127,4129,4139,4133,3877,4153,4139,4157,4159,3967,4159,4157,4159,4153,3947,4157,4159,4177,4177,4177,3989,4177,3691,4013,2963,4177,4001,4003,2971,4201,4201,4201,4013,4201,4211,4019,4021,4217,4219,4027,4219,4217,4211,4229,4231,4217,4219,4229,4231,4241,4243,4229,4231,4241,4057,4253,4253,4241,4259,4261,4259,4261,4073,4253,4271,4273,4259,4261,4271,4273,4283,4091,4271,4289,4283,4099,3067,4297,4283,4297,4127,4289,3079,4133,3083,4297,4139,3089,3823,4127,4129,4051,4327,4327,4327,4139,4327,4337,4339,4337,4327,4337,4153,4349,4157,4337,4339,4357,4357,4357,4363,4349,4363,2393,4177,4373,4373,4373,4363,4373,4159,3889,4211,4373,4391,4391,4201,4397,4391,4397,3907,4211,4391,4409,4217,4397,3187,4409,3191,4421,4423,4409,4423,4421,4423,4159,4241,4421,4423,4441,4441,4441,4447,4441,4451,4259,4261,4457,4451,4457,4463,4271,4451,3181,4463,4457,4201,4283,4463,4481,4483,4481,4483,4481,4297,4493,4493,4481,4483,4493,4327,4231,4507,4493,4507,4513,4507,4517,4519,4327,4523,4517,4519,4513,4337,4517,4519,4139,4523,3313,4349,4049,4547,4549,4357,4549,4547,4363,3331,4561,4547,4549,4567,4561,4567,4397,4567,4561,4079,4357,4583,4391,4583,3361,4591,4591,4591,4597,4583,4597,4603,4597,4591,4211,4603,4597,4421,4423,4603,4621,4621,4621,4451,4621,4357,4457,4441,4637,4639,4447,4643,4451,4639,4649,4651,4637,4639,4657,4643,4657,4663,4649,4651,4493,4663,4673,4481,4483,4679,4673,4679,3457,4493,4673,4691,4691,4679,3469,4691,4507,4703,4703,4691,4639,4517,4519,4219,4523,4703,4721,4723,4721,4723,4729,4723,4733,4733,4721,4723,4547,4549,4729,4523,4733,4751,4751,4561,3529,4759,4567,4759,2789,4751,3541,4547,4597,4759,4583,4603,4507,4783,4591,4787,4789,4597,4793,4787,4603,4799]
private theorem vg4004 : rvld 1 4004 qg4004 := by
  unfold qg4004
  exact rvc p3 p4001 (rvc p3 p4003 (rvc p19 p3989 (rvc p3 p4007 (rvc p11 p4001 (rvc p11 p4003 (rvc p3 p4013 (rvc p197 p3821 (rvc p19 p4001 (rvc p3 p4019 (rvc p3 p4021 (rvc p19 p4007 (rvc p7 p4021 (rvc p3 p4027 (rvc p19 p4013 (rvc p7 p4027 (rvc p503 p3533 (rvc p19 p4019 (rvc p19 p4021 (rvc p179 p3863 (rvc p197 p3847 (rvc p19 p4027 (rvc p197 p3851 (rvc p197 p3853 (rvc p3 p4049 (rvc p3 p4051 (rvc p7 p4049 (rvc p7 p4051 (rvc p3 p4057 (rvc p11 p4051 (rvc p7 p4057 (rvc p1979 p2087 (rvc p19 p4049 (rvc p19 p4051 (rvc p401 p3671 (rvc p197 p3877 (rvc p3 p4073 (rvc p197 p3881 (rvc p7 p4073 (rvc p3 p4079 (rvc p11 p4073 (rvc p197 p3889 (rvc p1231 p2857 (rvc p11 p4079 (rvc p19 p4073 (rvc p3 p4091 (rvc p3 p4093 (rvc p19 p4079 (rvc p7 p4093 (rvc p3 p4099 (rvc p197 p3907 (rvc p7 p4099 (rvc p197 p3911 (rvc p19 p4091 (rvc p19 p4093 (rvc p3 p4111 (rvc p197 p3919 (rvc p19 p4099 (rvc p197 p3923 (rvc p11 p4111 (rvc p277 p3847 (rvc p197 p3929 (rvc p197 p3931 (rvc p3 p4127 (rvc p3 p4129 (rvc p7 p4127 (rvc p3 p4133 (rvc p11 p4127 (rvc p197 p3943 (rvc p3 p4139 (rvc p197 p3947 (rvc p19 p4127 (rvc p19 p4129 (rvc p11 p4139 (rvc p19 p4133 (rvc p277 p3877 (rvc p3 p4153 (rvc p19 p4139 (rvc p3 p4157 (rvc p3 p4159 (rvc p197 p3967 (rvc p7 p4159 (rvc p11 p4157 (rvc p11 p4159 (rvc p19 p4153 (rvc p227 p3947 (rvc p19 p4157 (rvc p19 p4159 (rvc p3 p4177 (rvc p5 p4177 (rvc p7 p4177 (rvc p197 p3989 (rvc p11 p4177 (rvc p499 p3691 (rvc p179 p4013 (rvc p1231 p2963 (rvc p19 p4177 (rvc p197 p4001 (rvc p197 p4003 (rvc p1231 p2971 (rvc p3 p4201 (rvc p5 p4201 (rvc p7 p4201 (rvc p197 p4013 (rvc p11 p4201 (rvc p3 p4211 (rvc p197 p4019 (rvc p197 p4021 (rvc p3 p4217 (rvc p3 p4219 (rvc p197 p4027 (rvc p7 p4219 (rvc p11 p4217 (rvc p19 p4211 (rvc p3 p4229 (rvc p3 p4231 (rvc p19 p4217 (rvc p19 p4219 (rvc p11 p4229 (rvc p11 p4231 (rvc p3 p4241 (rvc p3 p4243 (rvc p19 p4229 (rvc p19 p4231 (rvc p11 p4241 (rvc p197 p4057 (rvc p3 p4253 (rvc p5 p4253 (rvc p19 p4241 (rvc p3 p4259 (rvc p3 p4261 (rvc p7 p4259 (rvc p7 p4261 (rvc p197 p4073 (rvc p19 p4253 (rvc p3 p4271 (rvc p3 p4273 (rvc p19 p4259 (rvc p19 p4261 (rvc p11 p4271 (rvc p11 p4273 (rvc p3 p4283 (rvc p197 p4091 (rvc p19 p4271 (rvc p3 p4289 (rvc p11 p4283 (rvc p197 p4099 (rvc p1231 p3067 (rvc p3 p4297 (rvc p19 p4283 (rvc p7 p4297 (rvc p179 p4127 (rvc p19 p4289 (rvc p1231 p3079 (rvc p179 p4133 (rvc p1231 p3083 (rvc p19 p4297 (rvc p179 p4139 (rvc p1231 p3089 (rvc p499 p3823 (rvc p197 p4127 (rvc p197 p4129 (rvc p277 p4051 (rvc p3 p4327 (rvc p5 p4327 (rvc p7 p4327 (rvc p197 p4139 (rvc p11 p4327 (rvc p3 p4337 (rvc p3 p4339 (rvc p7 p4337 (rvc p19 p4327 (rvc p11 p4337 (rvc p197 p4153 (rvc p3 p4349 (rvc p197 p4157 (rvc p19 p4337 (rvc p19 p4339 (rvc p3 p4357 (rvc p5 p4357 (rvc p7 p4357 (rvc p3 p4363 (rvc p19 p4349 (rvc p7 p4363 (rvc p1979 p2393 (rvc p197 p4177 (rvc p3 p4373 (rvc p5 p4373 (rvc p7 p4373 (rvc p19 p4363 (rvc p11 p4373 (rvc p227 p4159 (rvc p499 p3889 (rvc p179 p4211 (rvc p19 p4373 (rvc p3 p4391 (rvc p5 p4391 (rvc p197 p4201 (rvc p3 p4397 (rvc p11 p4391 (rvc p7 p4397 (rvc p499 p3907 (rvc p197 p4211 (rvc p19 p4391 (rvc p3 p4409 (rvc p197 p4217 (rvc p19 p4397 (rvc p1231 p3187 (rvc p11 p4409 (rvc p1231 p3191 (rvc p3 p4421 (rvc p3 p4423 (rvc p19 p4409 (rvc p7 p4423 (rvc p11 p4421 (rvc p11 p4423 (rvc p277 p4159 (rvc p197 p4241 (rvc p19 p4421 (rvc p19 p4423 (rvc p3 p4441 (rvc p5 p4441 (rvc p7 p4441 (rvc p3 p4447 (rvc p11 p4441 (rvc p3 p4451 (rvc p197 p4259 (rvc p197 p4261 (rvc p3 p4457 (rvc p11 p4451 (rvc p7 p4457 (rvc p3 p4463 (rvc p197 p4271 (rvc p19 p4451 (rvc p1291 p3181 (rvc p11 p4463 (rvc p19 p4457 (rvc p277 p4201 (rvc p197 p4283 (rvc p19 p4463 (rvc p3 p4481 (rvc p3 p4483 (rvc p7 p4481 (rvc p7 p4483 (rvc p11 p4481 (rvc p197 p4297 (rvc p3 p4493 (rvc p5 p4493 (rvc p19 p4481 (rvc p19 p4483 (rvc p11 p4493 (rvc p179 p4327 (rvc p277 p4231 (rvc p3 p4507 (rvc p19 p4493 (rvc p7 p4507 (rvc p3 p4513 (rvc p11 p4507 (rvc p3 p4517 (rvc p3 p4519 (rvc p197 p4327 (rvc p3 p4523 (rvc p11 p4517 (rvc p11 p4519 (rvc p19 p4513 (rvc p197 p4337 (rvc p19 p4517 (rvc p19 p4519 (rvc p401 p4139 (rvc p19 p4523 (rvc p1231 p3313 (rvc p197 p4349 (rvc p499 p4049 (rvc p3 p4547 (rvc p3 p4549 (rvc p197 p4357 (rvc p7 p4549 (rvc p11 p4547 (rvc p197 p4363 (rvc p1231 p3331 (rvc p3 p4561 (rvc p19 p4547 (rvc p19 p4549 (rvc p3 p4567 (rvc p11 p4561 (rvc p7 p4567 (rvc p179 p4397 (rvc p11 p4567 (rvc p19 p4561 (rvc p503 p4079 (rvc p227 p4357 (rvc p3 p4583 (rvc p197 p4391 (rvc p7 p4583 (rvc p1231 p3361 (rvc p3 p4591 (rvc p5 p4591 (rvc p7 p4591 (rvc p3 p4597 (rvc p19 p4583 (rvc p7 p4597 (rvc p3 p4603 (rvc p11 p4597 (rvc p19 p4591 (rvc p401 p4211 (rvc p11 p4603 (rvc p19 p4597 (rvc p197 p4421 (rvc p197 p4423 (rvc p19 p4603 (rvc p3 p4621 (rvc p5 p4621 (rvc p7 p4621 (rvc p179 p4451 (rvc p11 p4621 (rvc p277 p4357 (rvc p179 p4457 (rvc p197 p4441 (rvc p3 p4637 (rvc p3 p4639 (rvc p197 p4447 (rvc p3 p4643 (rvc p197 p4451 (rvc p11 p4639 (rvc p3 p4649 (rvc p3 p4651 (rvc p19 p4637 (rvc p19 p4639 (rvc p3 p4657 (rvc p19 p4643 (rvc p7 p4657 (rvc p3 p4663 (rvc p19 p4649 (rvc p19 p4651 (rvc p179 p4493 (rvc p11 p4663 (rvc p3 p4673 (rvc p197 p4481 (rvc p197 p4483 (rvc p3 p4679 (rvc p11 p4673 (rvc p7 p4679 (rvc p1231 p3457 (rvc p197 p4493 (rvc p19 p4673 (rvc p3 p4691 (rvc p5 p4691 (rvc p19 p4679 (rvc p1231 p3469 (rvc p11 p4691 (rvc p197 p4507 (rvc p3 p4703 (rvc p5 p4703 (rvc p19 p4691 (rvc p73 p4639 (rvc p197 p4517 (rvc p197 p4519 (rvc p499 p4219 (rvc p197 p4523 (rvc p19 p4703 (rvc p3 p4721 (rvc p3 p4723 (rvc p7 p4721 (rvc p7 p4723 (rvc p3 p4729 (rvc p11 p4723 (rvc p3 p4733 (rvc p5 p4733 (rvc p19 p4721 (rvc p19 p4723 (rvc p197 p4547 (rvc p197 p4549 (rvc p19 p4729 (rvc p227 p4523 (rvc p19 p4733 (rvc p3 p4751 (rvc p5 p4751 (rvc p197 p4561 (rvc p1231 p3529 (rvc p3 p4759 (rvc p197 p4567 (rvc p7 p4759 (rvc p1979 p2789 (rvc p19 p4751 (rvc p1231 p3541 (rvc p227 p4547 (rvc p179 p4597 (rvc p19 p4759 (rvc p197 p4583 (rvc p179 p4603 (rvc p277 p4507 (rvc p3 p4783 (rvc p197 p4591 (rvc p3 p4787 (rvc p3 p4789 (rvc p197 p4597 (rvc p3 p4793 (rvc p11 p4787 (rvc p197 p4603 (rvc p3 p4799 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg4004 (m : ℕ) (hl : 4004 ≤ m) (hh : m ≤ 4803) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-4004)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 4004+2*k := by simp [k]; omega
  have hk : k < qg4004.length := by simp [k,qg4004]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg4004 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg4804 : List ℕ := [4801,4787,4789,4799,4793,3583,4813,4799,4817,4817,4813,4327,4817,4651,4813,4831,4817,4831,4643,4831,3613,4649,4651,4831,4673,4657,4357,4679,4663,3631,4861,4861,4861,4673,4861,4871,4679,4871,4877,4871,4877,4813,4691,4871,4889,4889,4877,4621,4703,3671,3673,4903,4889,4903,4909,4903,4909,4721,4723,4919,4919,4729,4909,4733,3701,4931,4933,4919,4937,4931,4933,4943,4751,4931,4933,4951,4937,4951,4957,4943,4957,4787,4957,4967,4969,4967,4973,4967,4783,4483,4787,4967,4969,4987,4973,4987,4993,4801,4993,4999,4993,5003,5003,4813,5009,5011,5009,4999,5009,5003,5021,5023,5009,5011,5021,5023,4759,4637,5021,5039,5039,5039,4549,5039,3821,5051,5051,5039,4561,5059,5059,5059,4871,5051,4999,4877,4799,5059,5077,5077,5081,4889,5077,5087,5081,5087,5077,5087,5081,5099,5101,5087,5101,5107,5101,5107,5113,5099,5101,5119,5113,5107,4931,4933,5113,4937,4957,5119,4943,3911,3853,4967,4951,5147,5147,4957,5153,5147,5153,3931,4967,5147,3877,5167,5153,5171,5171,5167,4903,5179,4987,5167,5009,5171,5189,5189,4999,5179,5197,5197,5197,5009,5189,4933,5209,5209,5197,5021,5023,4723,4721,4999,5209,5227,5227,5231,5233,5227,5237,5231,5233,5227,5051,5231,5233,4751,5237,4027,5081,4861,5261,5261,5261,4993,5261,5077,5273,5081,5261,5279,5281,5279,5281,5279,5273,4003,5099,5279,5297,5297,5107,5303,5297,5113,5309,5303,5297,4027,5309,5303,4093,5323,5309,5323,5153,5323,5333,5333,5333,5323,5147,5167,4057,5347,5333,5351,5351,5347,4129,5351,5167,5347,5171,5351,2011,5147,5179,5101,5153,4091,5381,5189,5381,5387,5381,5197,5393,5387,5381,5399,5393,5387,4177,5407,5393,5407,5413,5399,5417,5419,5227,5407,5231,5233,5413,5431,5417,5419,5437,5431,5441,5443,5437,5431,5449,5443,5437,5261,5441,5443,5237,4967,5449,5273,4241,5471,5279,5281,5477,5479,5477,5483,5477,5471,4261,5297,5477,5479,5303,5483,5501,5503,5501,5507,5501,5503,5443,5507,5501,5519,5521,5507,5521,5527,5521,5531,5531,5519,5521,5531,5347,5527,5351,5531,4261,5153,5279,4327,5557,5557,5557,5563,5557,5563,5569,5563,5573,5381,5569,5563,5581,5581,5569,5393,5573,5591,5399,5591,5581,5591]
private theorem vg4804 : rvld 1 4804 qg4804 := by
  unfold qg4804
  exact rvc p3 p4801 (rvc p19 p4787 (rvc p19 p4789 (rvc p11 p4799 (rvc p19 p4793 (rvc p1231 p3583 (rvc p3 p4813 (rvc p19 p4799 (rvc p3 p4817 (rvc p5 p4817 (rvc p11 p4813 (rvc p499 p4327 (rvc p11 p4817 (rvc p179 p4651 (rvc p19 p4813 (rvc p3 p4831 (rvc p19 p4817 (rvc p7 p4831 (rvc p197 p4643 (rvc p11 p4831 (rvc p1231 p3613 (rvc p197 p4649 (rvc p197 p4651 (rvc p19 p4831 (rvc p179 p4673 (rvc p197 p4657 (rvc p499 p4357 (rvc p179 p4679 (rvc p197 p4663 (rvc p1231 p3631 (rvc p3 p4861 (rvc p5 p4861 (rvc p7 p4861 (rvc p197 p4673 (rvc p11 p4861 (rvc p3 p4871 (rvc p197 p4679 (rvc p7 p4871 (rvc p3 p4877 (rvc p11 p4871 (rvc p7 p4877 (rvc p73 p4813 (rvc p197 p4691 (rvc p19 p4871 (rvc p3 p4889 (rvc p5 p4889 (rvc p19 p4877 (rvc p277 p4621 (rvc p197 p4703 (rvc p1231 p3671 (rvc p1231 p3673 (rvc p3 p4903 (rvc p19 p4889 (rvc p7 p4903 (rvc p3 p4909 (rvc p11 p4903 (rvc p7 p4909 (rvc p197 p4721 (rvc p197 p4723 (rvc p3 p4919 (rvc p5 p4919 (rvc p197 p4729 (rvc p19 p4909 (rvc p197 p4733 (rvc p1231 p3701 (rvc p3 p4931 (rvc p3 p4933 (rvc p19 p4919 (rvc p3 p4937 (rvc p11 p4931 (rvc p11 p4933 (rvc p3 p4943 (rvc p197 p4751 (rvc p19 p4931 (rvc p19 p4933 (rvc p3 p4951 (rvc p19 p4937 (rvc p7 p4951 (rvc p3 p4957 (rvc p19 p4943 (rvc p7 p4957 (rvc p179 p4787 (rvc p11 p4957 (rvc p3 p4967 (rvc p3 p4969 (rvc p7 p4967 (rvc p3 p4973 (rvc p11 p4967 (rvc p197 p4783 (rvc p499 p4483 (rvc p197 p4787 (rvc p19 p4967 (rvc p19 p4969 (rvc p3 p4987 (rvc p19 p4973 (rvc p7 p4987 (rvc p3 p4993 (rvc p197 p4801 (rvc p7 p4993 (rvc p3 p4999 (rvc p11 p4993 (rvc p3 p5003 (rvc p5 p5003 (rvc p197 p4813 (rvc p3 p5009 (rvc p3 p5011 (rvc p7 p5009 (rvc p19 p4999 (rvc p11 p5009 (rvc p19 p5003 (rvc p3 p5021 (rvc p3 p5023 (rvc p19 p5009 (rvc p19 p5011 (rvc p11 p5021 (rvc p11 p5023 (rvc p277 p4759 (rvc p401 p4637 (rvc p19 p5021 (rvc p3 p5039 (rvc p5 p5039 (rvc p7 p5039 (rvc p499 p4549 (rvc p11 p5039 (rvc p1231 p3821 (rvc p3 p5051 (rvc p5 p5051 (rvc p19 p5039 (rvc p499 p4561 (rvc p3 p5059 (rvc p5 p5059 (rvc p7 p5059 (rvc p197 p4871 (rvc p19 p5051 (rvc p73 p4999 (rvc p197 p4877 (rvc p277 p4799 (rvc p19 p5059 (rvc p3 p5077 (rvc p5 p5077 (rvc p3 p5081 (rvc p197 p4889 (rvc p11 p5077 (rvc p3 p5087 (rvc p11 p5081 (rvc p7 p5087 (rvc p19 p5077 (rvc p11 p5087 (rvc p19 p5081 (rvc p3 p5099 (rvc p3 p5101 (rvc p19 p5087 (rvc p7 p5101 (rvc p3 p5107 (rvc p11 p5101 (rvc p7 p5107 (rvc p3 p5113 (rvc p19 p5099 (rvc p19 p5101 (rvc p3 p5119 (rvc p11 p5113 (rvc p19 p5107 (rvc p197 p4931 (rvc p197 p4933 (rvc p19 p5113 (rvc p197 p4937 (rvc p179 p4957 (rvc p19 p5119 (rvc p197 p4943 (rvc p1231 p3911 (rvc p1291 p3853 (rvc p179 p4967 (rvc p197 p4951 (rvc p3 p5147 (rvc p5 p5147 (rvc p197 p4957 (rvc p3 p5153 (rvc p11 p5147 (rvc p7 p5153 (rvc p1231 p3931 (rvc p197 p4967 (rvc p19 p5147 (rvc p1291 p3877 (rvc p3 p5167 (rvc p19 p5153 (rvc p3 p5171 (rvc p5 p5171 (rvc p11 p5167 (rvc p277 p4903 (rvc p3 p5179 (rvc p197 p4987 (rvc p19 p5167 (rvc p179 p5009 (rvc p19 p5171 (rvc p3 p5189 (rvc p5 p5189 (rvc p197 p4999 (rvc p19 p5179 (rvc p3 p5197 (rvc p5 p5197 (rvc p7 p5197 (rvc p197 p5009 (rvc p19 p5189 (rvc p277 p4933 (rvc p3 p5209 (rvc p5 p5209 (rvc p19 p5197 (rvc p197 p5021 (rvc p197 p5023 (rvc p499 p4723 (rvc p503 p4721 (rvc p227 p4999 (rvc p19 p5209 (rvc p3 p5227 (rvc p5 p5227 (rvc p3 p5231 (rvc p3 p5233 (rvc p11 p5227 (rvc p3 p5237 (rvc p11 p5231 (rvc p11 p5233 (rvc p19 p5227 (rvc p197 p5051 (rvc p19 p5231 (rvc p19 p5233 (rvc p503 p4751 (rvc p19 p5237 (rvc p1231 p4027 (rvc p179 p5081 (rvc p401 p4861 (rvc p3 p5261 (rvc p5 p5261 (rvc p7 p5261 (rvc p277 p4993 (rvc p11 p5261 (rvc p197 p5077 (rvc p3 p5273 (rvc p197 p5081 (rvc p19 p5261 (rvc p3 p5279 (rvc p3 p5281 (rvc p7 p5279 (rvc p7 p5281 (rvc p11 p5279 (rvc p19 p5273 (rvc p1291 p4003 (rvc p197 p5099 (rvc p19 p5279 (rvc p3 p5297 (rvc p5 p5297 (rvc p197 p5107 (rvc p3 p5303 (rvc p11 p5297 (rvc p197 p5113 (rvc p3 p5309 (rvc p11 p5303 (rvc p19 p5297 (rvc p1291 p4027 (rvc p11 p5309 (rvc p19 p5303 (rvc p1231 p4093 (rvc p3 p5323 (rvc p19 p5309 (rvc p7 p5323 (rvc p179 p5153 (rvc p11 p5323 (rvc p3 p5333 (rvc p5 p5333 (rvc p7 p5333 (rvc p19 p5323 (rvc p197 p5147 (rvc p179 p5167 (rvc p1291 p4057 (rvc p3 p5347 (rvc p19 p5333 (rvc p3 p5351 (rvc p5 p5351 (rvc p11 p5347 (rvc p1231 p4129 (rvc p11 p5351 (rvc p197 p5167 (rvc p19 p5347 (rvc p197 p5171 (rvc p19 p5351 (rvc p3361 p2011 (rvc p227 p5147 (rvc p197 p5179 (rvc p277 p5101 (rvc p227 p5153 (rvc p1291 p4091 (rvc p3 p5381 (rvc p197 p5189 (rvc p7 p5381 (rvc p3 p5387 (rvc p11 p5381 (rvc p197 p5197 (rvc p3 p5393 (rvc p11 p5387 (rvc p19 p5381 (rvc p3 p5399 (rvc p11 p5393 (rvc p19 p5387 (rvc p1231 p4177 (rvc p3 p5407 (rvc p19 p5393 (rvc p7 p5407 (rvc p3 p5413 (rvc p19 p5399 (rvc p3 p5417 (rvc p3 p5419 (rvc p197 p5227 (rvc p19 p5407 (rvc p197 p5231 (rvc p197 p5233 (rvc p19 p5413 (rvc p3 p5431 (rvc p19 p5417 (rvc p19 p5419 (rvc p3 p5437 (rvc p11 p5431 (rvc p3 p5441 (rvc p3 p5443 (rvc p11 p5437 (rvc p19 p5431 (rvc p3 p5449 (rvc p11 p5443 (rvc p19 p5437 (rvc p197 p5261 (rvc p19 p5441 (rvc p19 p5443 (rvc p227 p5237 (rvc p499 p4967 (rvc p19 p5449 (rvc p197 p5273 (rvc p1231 p4241 (rvc p3 p5471 (rvc p197 p5279 (rvc p197 p5281 (rvc p3 p5477 (rvc p3 p5479 (rvc p7 p5477 (rvc p3 p5483 (rvc p11 p5477 (rvc p19 p5471 (rvc p1231 p4261 (rvc p197 p5297 (rvc p19 p5477 (rvc p19 p5479 (rvc p197 p5303 (rvc p19 p5483 (rvc p3 p5501 (rvc p3 p5503 (rvc p7 p5501 (rvc p3 p5507 (rvc p11 p5501 (rvc p11 p5503 (rvc p73 p5443 (rvc p11 p5507 (rvc p19 p5501 (rvc p3 p5519 (rvc p3 p5521 (rvc p19 p5507 (rvc p7 p5521 (rvc p3 p5527 (rvc p11 p5521 (rvc p3 p5531 (rvc p5 p5531 (rvc p19 p5519 (rvc p19 p5521 (rvc p11 p5531 (rvc p197 p5347 (rvc p19 p5527 (rvc p197 p5351 (rvc p19 p5531 (rvc p1291 p4261 (rvc p401 p5153 (rvc p277 p5279 (rvc p1231 p4327 (rvc p3 p5557 (rvc p5 p5557 (rvc p7 p5557 (rvc p3 p5563 (rvc p11 p5557 (rvc p7 p5563 (rvc p3 p5569 (rvc p11 p5563 (rvc p3 p5573 (rvc p197 p5381 (rvc p11 p5569 (rvc p19 p5563 (rvc p3 p5581 (rvc p5 p5581 (rvc p19 p5569 (rvc p197 p5393 (rvc p19 p5573 (rvc p3 p5591 (rvc p197 p5399 (rvc p7 p5591 (rvc p19 p5581 (rvc p11 p5591 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg4804 (m : ℕ) (hl : 4804 ≤ m) (hh : m ≤ 5603) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-4804)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 4804+2*k := by simp [k]; omega
  have hk : k < qg4804.length := by simp [k,qg4804]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg4804 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg5604 : List ℕ := [5407,5107,5381,5591,5113,5417,5419,5119,5441,4391,5347,5623,5431,5623,5231,5437,5563,5441,5443,5639,5641,5449,5641,5647,5641,5651,5653,5639,5657,5659,5653,5647,5471,5651,5669,5477,5657,5659,5483,4451,5407,5683,5669,5683,5689,5683,5693,5501,5503,5683,5701,5701,5689,5531,5693,5711,5519,5521,5717,5711,5527,5227,5531,5711,5233,5507,5717,4507,5737,5737,5741,5743,5737,5743,5749,5557,5737,5531,5741,5743,5261,5569,5749,5573,5273,4483,5273,5581,4549,5779,5779,5783,5591,5779,4561,5791,5791,5779,5573,5783,5801,5801,5801,5807,5801,5807,5813,5807,5801,4591,5821,5807,5821,5827,5813,5827,5639,5641,5821,5839,5647,5843,5651,5653,5849,5851,5659,5839,5857,5843,5861,5669,5849,5867,5869,5867,5857,5867,5861,5879,5881,5867,5869,5693,5881,4663,5717,5879,5897,5897,5897,5903,5711,5903,5413,5717,5897,5419,5741,5903,5647,5923,5923,5927,5927,5737,5437,5741,5743,5939,5939,5927,5449,5939,4721,4723,5953,5939,5953,5783,5953,5689,5741,5791,5953,5573,5779,5479,5783,4751,5981,5981,5791,5987,5981,5987,5923,5801,5981,5503,5807,5987,2647,6007,6007,6011,6011,5821,4789,6011,5827,6007,5849,6011,6029,6029,5839,2677,6037,6037,6037,6043,6029,6047,6047,5857,6053,5861,6053,6043,5867,6047,5569,6067,6053,6067,6073,5881,6073,6079,6073,6067,5861,6079,6089,6091,6089,6079,5903,6091,6101,6101,6089,6091,6101,2753,6113,6113,6101,5623,6121,6121,6121,5903,6113,6131,6133,6131,6121,6131,6133,6143,6143,6131,6133,6151,6151,6151,5981,6143,4933,6163,6163,6151,5669,6163,6173,5981,6173,6163,5987,6007,4957,6011,6173,4903,5693,4967,6197,6199,6007,6203,6011,6199,2851,6211,6197,6199,6217,6203,6221,6029,6217,6211,6229,6037,6217,6011,6221,5011,6047,6067,6229,6247,6247,6247,6029,6247,6257,6257,6067,6263,6257,6073,6269,6271,6257,6271,6277,6263,6277,6089,6269,6287,6287,6287,6277,6101,6121,6299,6301,6287,6301,6113,6301,6311,6311,6299,6317,6311,6317,6323,6131,6311,6329,6323,6317,5107,6337,6323,6337,6343,6329,6343,6173,6343,6353,6353,6163,6359,6361,6359,6361,6367,6353,6367,6373,6359,6361,6379,6373,6367,5987,6379,6389,6197,6199,6379,6397,6397]
private theorem vg5604 : rvld 1 5604 qg5604 := by
  unfold qg5604
  exact rvc p197 p5407 (rvc p499 p5107 (rvc p227 p5381 (rvc p19 p5591 (rvc p499 p5113 (rvc p197 p5417 (rvc p197 p5419 (rvc p499 p5119 (rvc p179 p5441 (rvc p1231 p4391 (rvc p277 p5347 (rvc p3 p5623 (rvc p197 p5431 (rvc p7 p5623 (rvc p401 p5231 (rvc p197 p5437 (rvc p73 p5563 (rvc p197 p5441 (rvc p197 p5443 (rvc p3 p5639 (rvc p3 p5641 (rvc p197 p5449 (rvc p7 p5641 (rvc p3 p5647 (rvc p11 p5641 (rvc p3 p5651 (rvc p3 p5653 (rvc p19 p5639 (rvc p3 p5657 (rvc p3 p5659 (rvc p11 p5653 (rvc p19 p5647 (rvc p197 p5471 (rvc p19 p5651 (rvc p3 p5669 (rvc p197 p5477 (rvc p19 p5657 (rvc p19 p5659 (rvc p197 p5483 (rvc p1231 p4451 (rvc p277 p5407 (rvc p3 p5683 (rvc p19 p5669 (rvc p7 p5683 (rvc p3 p5689 (rvc p11 p5683 (rvc p3 p5693 (rvc p197 p5501 (rvc p197 p5503 (rvc p19 p5683 (rvc p3 p5701 (rvc p5 p5701 (rvc p19 p5689 (rvc p179 p5531 (rvc p19 p5693 (rvc p3 p5711 (rvc p197 p5519 (rvc p197 p5521 (rvc p3 p5717 (rvc p11 p5711 (rvc p197 p5527 (rvc p499 p5227 (rvc p197 p5531 (rvc p19 p5711 (rvc p499 p5233 (rvc p227 p5507 (rvc p19 p5717 (rvc p1231 p4507 (rvc p3 p5737 (rvc p5 p5737 (rvc p3 p5741 (rvc p3 p5743 (rvc p11 p5737 (rvc p7 p5743 (rvc p3 p5749 (rvc p197 p5557 (rvc p19 p5737 (rvc p227 p5531 (rvc p19 p5741 (rvc p19 p5743 (rvc p503 p5261 (rvc p197 p5569 (rvc p19 p5749 (rvc p197 p5573 (rvc p499 p5273 (rvc p1291 p4483 (rvc p503 p5273 (rvc p197 p5581 (rvc p1231 p4549 (rvc p3 p5779 (rvc p5 p5779 (rvc p3 p5783 (rvc p197 p5591 (rvc p11 p5779 (rvc p1231 p4561 (rvc p3 p5791 (rvc p5 p5791 (rvc p19 p5779 (rvc p227 p5573 (rvc p19 p5783 (rvc p3 p5801 (rvc p5 p5801 (rvc p7 p5801 (rvc p3 p5807 (rvc p11 p5801 (rvc p7 p5807 (rvc p3 p5813 (rvc p11 p5807 (rvc p19 p5801 (rvc p1231 p4591 (rvc p3 p5821 (rvc p19 p5807 (rvc p7 p5821 (rvc p3 p5827 (rvc p19 p5813 (rvc p7 p5827 (rvc p197 p5639 (rvc p197 p5641 (rvc p19 p5821 (rvc p3 p5839 (rvc p197 p5647 (rvc p3 p5843 (rvc p197 p5651 (rvc p197 p5653 (rvc p3 p5849 (rvc p3 p5851 (rvc p197 p5659 (rvc p19 p5839 (rvc p3 p5857 (rvc p19 p5843 (rvc p3 p5861 (rvc p197 p5669 (rvc p19 p5849 (rvc p3 p5867 (rvc p3 p5869 (rvc p7 p5867 (rvc p19 p5857 (rvc p11 p5867 (rvc p19 p5861 (rvc p3 p5879 (rvc p3 p5881 (rvc p19 p5867 (rvc p19 p5869 (rvc p197 p5693 (rvc p11 p5881 (rvc p1231 p4663 (rvc p179 p5717 (rvc p19 p5879 (rvc p3 p5897 (rvc p5 p5897 (rvc p7 p5897 (rvc p3 p5903 (rvc p197 p5711 (rvc p7 p5903 (rvc p499 p5413 (rvc p197 p5717 (rvc p19 p5897 (rvc p499 p5419 (rvc p179 p5741 (rvc p19 p5903 (rvc p277 p5647 (rvc p3 p5923 (rvc p5 p5923 (rvc p3 p5927 (rvc p5 p5927 (rvc p197 p5737 (rvc p499 p5437 (rvc p197 p5741 (rvc p197 p5743 (rvc p3 p5939 (rvc p5 p5939 (rvc p19 p5927 (rvc p499 p5449 (rvc p11 p5939 (rvc p1231 p4721 (rvc p1231 p4723 (rvc p3 p5953 (rvc p19 p5939 (rvc p7 p5953 (rvc p179 p5783 (rvc p11 p5953 (rvc p277 p5689 (rvc p227 p5741 (rvc p179 p5791 (rvc p19 p5953 (rvc p401 p5573 (rvc p197 p5779 (rvc p499 p5479 (rvc p197 p5783 (rvc p1231 p4751 (rvc p3 p5981 (rvc p5 p5981 (rvc p197 p5791 (rvc p3 p5987 (rvc p11 p5981 (rvc p7 p5987 (rvc p73 p5923 (rvc p197 p5801 (rvc p19 p5981 (rvc p499 p5503 (rvc p197 p5807 (rvc p19 p5987 (rvc p3361 p2647 (rvc p3 p6007 (rvc p5 p6007 (rvc p3 p6011 (rvc p5 p6011 (rvc p197 p5821 (rvc p1231 p4789 (rvc p11 p6011 (rvc p197 p5827 (rvc p19 p6007 (rvc p179 p5849 (rvc p19 p6011 (rvc p3 p6029 (rvc p5 p6029 (rvc p197 p5839 (rvc p3361 p2677 (rvc p3 p6037 (rvc p5 p6037 (rvc p7 p6037 (rvc p3 p6043 (rvc p19 p6029 (rvc p3 p6047 (rvc p5 p6047 (rvc p197 p5857 (rvc p3 p6053 (rvc p197 p5861 (rvc p7 p6053 (rvc p19 p6043 (rvc p197 p5867 (rvc p19 p6047 (rvc p499 p5569 (rvc p3 p6067 (rvc p19 p6053 (rvc p7 p6067 (rvc p3 p6073 (rvc p197 p5881 (rvc p7 p6073 (rvc p3 p6079 (rvc p11 p6073 (rvc p19 p6067 (rvc p227 p5861 (rvc p11 p6079 (rvc p3 p6089 (rvc p3 p6091 (rvc p7 p6089 (rvc p19 p6079 (rvc p197 p5903 (rvc p11 p6091 (rvc p3 p6101 (rvc p5 p6101 (rvc p19 p6089 (rvc p19 p6091 (rvc p11 p6101 (rvc p3361 p2753 (rvc p3 p6113 (rvc p5 p6113 (rvc p19 p6101 (rvc p499 p5623 (rvc p3 p6121 (rvc p5 p6121 (rvc p7 p6121 (rvc p227 p5903 (rvc p19 p6113 (rvc p3 p6131 (rvc p3 p6133 (rvc p7 p6131 (rvc p19 p6121 (rvc p11 p6131 (rvc p11 p6133 (rvc p3 p6143 (rvc p5 p6143 (rvc p19 p6131 (rvc p19 p6133 (rvc p3 p6151 (rvc p5 p6151 (rvc p7 p6151 (rvc p179 p5981 (rvc p19 p6143 (rvc p1231 p4933 (rvc p3 p6163 (rvc p5 p6163 (rvc p19 p6151 (rvc p503 p5669 (rvc p11 p6163 (rvc p3 p6173 (rvc p197 p5981 (rvc p7 p6173 (rvc p19 p6163 (rvc p197 p5987 (rvc p179 p6007 (rvc p1231 p4957 (rvc p179 p6011 (rvc p19 p6173 (rvc p1291 p4903 (rvc p503 p5693 (rvc p1231 p4967 (rvc p3 p6197 (rvc p3 p6199 (rvc p197 p6007 (rvc p3 p6203 (rvc p197 p6011 (rvc p11 p6199 (rvc p3361 p2851 (rvc p3 p6211 (rvc p19 p6197 (rvc p19 p6199 (rvc p3 p6217 (rvc p19 p6203 (rvc p3 p6221 (rvc p197 p6029 (rvc p11 p6217 (rvc p19 p6211 (rvc p3 p6229 (rvc p197 p6037 (rvc p19 p6217 (rvc p227 p6011 (rvc p19 p6221 (rvc p1231 p5011 (rvc p197 p6047 (rvc p179 p6067 (rvc p19 p6229 (rvc p3 p6247 (rvc p5 p6247 (rvc p7 p6247 (rvc p227 p6029 (rvc p11 p6247 (rvc p3 p6257 (rvc p5 p6257 (rvc p197 p6067 (rvc p3 p6263 (rvc p11 p6257 (rvc p197 p6073 (rvc p3 p6269 (rvc p3 p6271 (rvc p19 p6257 (rvc p7 p6271 (rvc p3 p6277 (rvc p19 p6263 (rvc p7 p6277 (rvc p197 p6089 (rvc p19 p6269 (rvc p3 p6287 (rvc p5 p6287 (rvc p7 p6287 (rvc p19 p6277 (rvc p197 p6101 (rvc p179 p6121 (rvc p3 p6299 (rvc p3 p6301 (rvc p19 p6287 (rvc p7 p6301 (rvc p197 p6113 (rvc p11 p6301 (rvc p3 p6311 (rvc p5 p6311 (rvc p19 p6299 (rvc p3 p6317 (rvc p11 p6311 (rvc p7 p6317 (rvc p3 p6323 (rvc p197 p6131 (rvc p19 p6311 (rvc p3 p6329 (rvc p11 p6323 (rvc p19 p6317 (rvc p1231 p5107 (rvc p3 p6337 (rvc p19 p6323 (rvc p7 p6337 (rvc p3 p6343 (rvc p19 p6329 (rvc p7 p6343 (rvc p179 p6173 (rvc p11 p6343 (rvc p3 p6353 (rvc p5 p6353 (rvc p197 p6163 (rvc p3 p6359 (rvc p3 p6361 (rvc p7 p6359 (rvc p7 p6361 (rvc p3 p6367 (rvc p19 p6353 (rvc p7 p6367 (rvc p3 p6373 (rvc p19 p6359 (rvc p19 p6361 (rvc p3 p6379 (rvc p11 p6373 (rvc p19 p6367 (rvc p401 p5987 (rvc p11 p6379 (rvc p3 p6389 (rvc p197 p6197 (rvc p197 p6199 (rvc p19 p6379 (rvc p3 p6397 (rvc p5 p6397 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg5604 (m : ℕ) (hl : 5604 ≤ m) (hh : m ≤ 6403) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-5604)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 5604+2*k := by simp [k]; omega
  have hk : k < qg5604.length := by simp [k,qg5604]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg5604 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg6404 : List ℕ := [6397,5903,6389,5179,6011,6217,6397,6221,5189,5923,6421,6229,6421,6427,6421,6427,6257,6427,6421,6263,6247,6427,6269,6271,6449,6451,6449,6451,6263,6451,5233,6269,6449,6451,6469,6277,6473,6473,6469,3121,6481,6481,6469,6311,6473,6491,6299,6301,6481,6491,5273,6007,6311,6491,5281,6317,6337,5227,6323,6343,6521,6329,6521,3169,6529,6337,6529,6359,6521,6043,6317,6367,6529,6547,6547,6551,6553,6361,6553,6551,6367,6563,6563,6551,6569,6571,6379,6571,6577,6563,6581,6389,6569,6571,6581,6397,6577,6197,6581,6599,6599,6599,6469,6607,6607,6607,6389,6599,6121,6619,6427,6607,6449,6619,6133,6131,6359,6619,6637,6637,6637,6449,6451,5419,6473,6427,6653,6653,6653,6659,6661,6469,6661,6473,6653,5443,6673,6659,6661,6679,6673,6679,6491,6679,6689,6691,6689,6679,6689,6691,6701,6703,6689,6691,6709,6703,6709,6521,6701,6719,6719,6529,6709,6719,5501,5503,6733,6719,6737,6737,6547,6247,6551,6553,6733,6353,6737,5527,6563,5531,6761,6763,6571,6763,6761,6577,6277,6581,6761,6779,6781,6779,6781,6779,6781,6791,6793,6779,6781,6791,6607,6803,6803,6791,6793,6803,6619,5527,6317,6803,6547,6823,6823,6827,6829,6637,6833,6827,6829,6823,6841,6827,6829,6653,6833,5623,6659,6661,6857,6857,6857,6863,6857,6673,6869,6871,6857,6871,6869,6863,5653,6883,6869,6871,6491,6883,6397,6701,6703,6899,6899,6709,3547,6907,6907,6911,6719,6899,6917,6911,6917,6907,6917,6911,5701,6737,6917,6661,6761,5711,5653,6719,5717,6947,6949,6947,6949,6761,6763,6959,6961,6947,6949,6967,6961,6971,6779,6959,6977,6971,6977,6983,6791,6971,5701,6991,6977,6991,6997,6983,7001,7001,6997,6991,7001,5783,7013,7013,7001,7019,6827,6829,6529,7027,7013,7027,6857,7019,6763,7039,7039,7043,7043,7039,5821,6857,6779,7039,7057,7043,7057,6869,6871,5839,7069,7069,7057,6899,6883,7079,7079,7079,7069,7079,5861,3733,6899,7079,5869,6701,6907,7103,6911,7103,7109,6917,7109,6619,7109,7103,7121,7121,7109,7127,7129,7127,7129,7127,7121,5851,6947,7127,7129,6971,6653,7151,6959,6961,6661,7159,6967,7159,6971,7151,6673,6977,6997,7159,7177,7177,7177,6959,6991,7187,7187,6997,7193,7001,7193,6703]
private theorem vg6404 : rvld 1 6404 qg6404 := by
  unfold qg6404
  exact rvc p7 p6397 (rvc p503 p5903 (rvc p19 p6389 (rvc p1231 p5179 (rvc p401 p6011 (rvc p197 p6217 (rvc p19 p6397 (rvc p197 p6221 (rvc p1231 p5189 (rvc p499 p5923 (rvc p3 p6421 (rvc p197 p6229 (rvc p7 p6421 (rvc p3 p6427 (rvc p11 p6421 (rvc p7 p6427 (rvc p179 p6257 (rvc p11 p6427 (rvc p19 p6421 (rvc p179 p6263 (rvc p197 p6247 (rvc p19 p6427 (rvc p179 p6269 (rvc p179 p6271 (rvc p3 p6449 (rvc p3 p6451 (rvc p7 p6449 (rvc p7 p6451 (rvc p197 p6263 (rvc p11 p6451 (rvc p1231 p5233 (rvc p197 p6269 (rvc p19 p6449 (rvc p19 p6451 (rvc p3 p6469 (rvc p197 p6277 (rvc p3 p6473 (rvc p5 p6473 (rvc p11 p6469 (rvc p3361 p3121 (rvc p3 p6481 (rvc p5 p6481 (rvc p19 p6469 (rvc p179 p6311 (rvc p19 p6473 (rvc p3 p6491 (rvc p197 p6299 (rvc p197 p6301 (rvc p19 p6481 (rvc p11 p6491 (rvc p1231 p5273 (rvc p499 p6007 (rvc p197 p6311 (rvc p19 p6491 (rvc p1231 p5281 (rvc p197 p6317 (rvc p179 p6337 (rvc p1291 p5227 (rvc p197 p6323 (rvc p179 p6343 (rvc p3 p6521 (rvc p197 p6329 (rvc p7 p6521 (rvc p3361 p3169 (rvc p3 p6529 (rvc p197 p6337 (rvc p7 p6529 (rvc p179 p6359 (rvc p19 p6521 (rvc p499 p6043 (rvc p227 p6317 (rvc p179 p6367 (rvc p19 p6529 (rvc p3 p6547 (rvc p5 p6547 (rvc p3 p6551 (rvc p3 p6553 (rvc p197 p6361 (rvc p7 p6553 (rvc p11 p6551 (rvc p197 p6367 (rvc p3 p6563 (rvc p5 p6563 (rvc p19 p6551 (rvc p3 p6569 (rvc p3 p6571 (rvc p197 p6379 (rvc p7 p6571 (rvc p3 p6577 (rvc p19 p6563 (rvc p3 p6581 (rvc p197 p6389 (rvc p19 p6569 (rvc p19 p6571 (rvc p11 p6581 (rvc p197 p6397 (rvc p19 p6577 (rvc p401 p6197 (rvc p19 p6581 (rvc p3 p6599 (rvc p5 p6599 (rvc p7 p6599 (rvc p139 p6469 (rvc p3 p6607 (rvc p5 p6607 (rvc p7 p6607 (rvc p227 p6389 (rvc p19 p6599 (rvc p499 p6121 (rvc p3 p6619 (rvc p197 p6427 (rvc p19 p6607 (rvc p179 p6449 (rvc p11 p6619 (rvc p499 p6133 (rvc p503 p6131 (rvc p277 p6359 (rvc p19 p6619 (rvc p3 p6637 (rvc p5 p6637 (rvc p7 p6637 (rvc p197 p6449 (rvc p197 p6451 (rvc p1231 p5419 (rvc p179 p6473 (rvc p227 p6427 (rvc p3 p6653 (rvc p5 p6653 (rvc p7 p6653 (rvc p3 p6659 (rvc p3 p6661 (rvc p197 p6469 (rvc p7 p6661 (rvc p197 p6473 (rvc p19 p6653 (rvc p1231 p5443 (rvc p3 p6673 (rvc p19 p6659 (rvc p19 p6661 (rvc p3 p6679 (rvc p11 p6673 (rvc p7 p6679 (rvc p197 p6491 (rvc p11 p6679 (rvc p3 p6689 (rvc p3 p6691 (rvc p7 p6689 (rvc p19 p6679 (rvc p11 p6689 (rvc p11 p6691 (rvc p3 p6701 (rvc p3 p6703 (rvc p19 p6689 (rvc p19 p6691 (rvc p3 p6709 (rvc p11 p6703 (rvc p7 p6709 (rvc p197 p6521 (rvc p19 p6701 (rvc p3 p6719 (rvc p5 p6719 (rvc p197 p6529 (rvc p19 p6709 (rvc p11 p6719 (rvc p1231 p5501 (rvc p1231 p5503 (rvc p3 p6733 (rvc p19 p6719 (rvc p3 p6737 (rvc p5 p6737 (rvc p197 p6547 (rvc p499 p6247 (rvc p197 p6551 (rvc p197 p6553 (rvc p19 p6733 (rvc p401 p6353 (rvc p19 p6737 (rvc p1231 p5527 (rvc p197 p6563 (rvc p1231 p5531 (rvc p3 p6761 (rvc p3 p6763 (rvc p197 p6571 (rvc p7 p6763 (rvc p11 p6761 (rvc p197 p6577 (rvc p499 p6277 (rvc p197 p6581 (rvc p19 p6761 (rvc p3 p6779 (rvc p3 p6781 (rvc p7 p6779 (rvc p7 p6781 (rvc p11 p6779 (rvc p11 p6781 (rvc p3 p6791 (rvc p3 p6793 (rvc p19 p6779 (rvc p19 p6781 (rvc p11 p6791 (rvc p197 p6607 (rvc p3 p6803 (rvc p5 p6803 (rvc p19 p6791 (rvc p19 p6793 (rvc p11 p6803 (rvc p197 p6619 (rvc p1291 p5527 (rvc p503 p6317 (rvc p19 p6803 (rvc p277 p6547 (rvc p3 p6823 (rvc p5 p6823 (rvc p3 p6827 (rvc p3 p6829 (rvc p197 p6637 (rvc p3 p6833 (rvc p11 p6827 (rvc p11 p6829 (rvc p19 p6823 (rvc p3 p6841 (rvc p19 p6827 (rvc p19 p6829 (rvc p197 p6653 (rvc p19 p6833 (rvc p1231 p5623 (rvc p197 p6659 (rvc p197 p6661 (rvc p3 p6857 (rvc p5 p6857 (rvc p7 p6857 (rvc p3 p6863 (rvc p11 p6857 (rvc p197 p6673 (rvc p3 p6869 (rvc p3 p6871 (rvc p19 p6857 (rvc p7 p6871 (rvc p11 p6869 (rvc p19 p6863 (rvc p1231 p5653 (rvc p3 p6883 (rvc p19 p6869 (rvc p19 p6871 (rvc p401 p6491 (rvc p11 p6883 (rvc p499 p6397 (rvc p197 p6701 (rvc p197 p6703 (rvc p3 p6899 (rvc p5 p6899 (rvc p197 p6709 (rvc p3361 p3547 (rvc p3 p6907 (rvc p5 p6907 (rvc p3 p6911 (rvc p197 p6719 (rvc p19 p6899 (rvc p3 p6917 (rvc p11 p6911 (rvc p7 p6917 (rvc p19 p6907 (rvc p11 p6917 (rvc p19 p6911 (rvc p1231 p5701 (rvc p197 p6737 (rvc p19 p6917 (rvc p277 p6661 (rvc p179 p6761 (rvc p1231 p5711 (rvc p1291 p5653 (rvc p227 p6719 (rvc p1231 p5717 (rvc p3 p6947 (rvc p3 p6949 (rvc p7 p6947 (rvc p7 p6949 (rvc p197 p6761 (rvc p197 p6763 (rvc p3 p6959 (rvc p3 p6961 (rvc p19 p6947 (rvc p19 p6949 (rvc p3 p6967 (rvc p11 p6961 (rvc p3 p6971 (rvc p197 p6779 (rvc p19 p6959 (rvc p3 p6977 (rvc p11 p6971 (rvc p7 p6977 (rvc p3 p6983 (rvc p197 p6791 (rvc p19 p6971 (rvc p1291 p5701 (rvc p3 p6991 (rvc p19 p6977 (rvc p7 p6991 (rvc p3 p6997 (rvc p19 p6983 (rvc p3 p7001 (rvc p5 p7001 (rvc p11 p6997 (rvc p19 p6991 (rvc p11 p7001 (rvc p1231 p5783 (rvc p3 p7013 (rvc p5 p7013 (rvc p19 p7001 (rvc p3 p7019 (rvc p197 p6827 (rvc p197 p6829 (rvc p499 p6529 (rvc p3 p7027 (rvc p19 p7013 (rvc p7 p7027 (rvc p179 p6857 (rvc p19 p7019 (rvc p277 p6763 (rvc p3 p7039 (rvc p5 p7039 (rvc p3 p7043 (rvc p5 p7043 (rvc p11 p7039 (rvc p1231 p5821 (rvc p197 p6857 (rvc p277 p6779 (rvc p19 p7039 (rvc p3 p7057 (rvc p19 p7043 (rvc p7 p7057 (rvc p197 p6869 (rvc p197 p6871 (rvc p1231 p5839 (rvc p3 p7069 (rvc p5 p7069 (rvc p19 p7057 (rvc p179 p6899 (rvc p197 p6883 (rvc p3 p7079 (rvc p5 p7079 (rvc p7 p7079 (rvc p19 p7069 (rvc p11 p7079 (rvc p1231 p5861 (rvc p3361 p3733 (rvc p197 p6899 (rvc p19 p7079 (rvc p1231 p5869 (rvc p401 p6701 (rvc p197 p6907 (rvc p3 p7103 (rvc p197 p6911 (rvc p7 p7103 (rvc p3 p7109 (rvc p197 p6917 (rvc p7 p7109 (rvc p499 p6619 (rvc p11 p7109 (rvc p19 p7103 (rvc p3 p7121 (rvc p5 p7121 (rvc p19 p7109 (rvc p3 p7127 (rvc p3 p7129 (rvc p7 p7127 (rvc p7 p7129 (rvc p11 p7127 (rvc p19 p7121 (rvc p1291 p5851 (rvc p197 p6947 (rvc p19 p7127 (rvc p19 p7129 (rvc p179 p6971 (rvc p499 p6653 (rvc p3 p7151 (rvc p197 p6959 (rvc p197 p6961 (rvc p499 p6661 (rvc p3 p7159 (rvc p197 p6967 (rvc p7 p7159 (rvc p197 p6971 (rvc p19 p7151 (rvc p499 p6673 (rvc p197 p6977 (rvc p179 p6997 (rvc p19 p7159 (rvc p3 p7177 (rvc p5 p7177 (rvc p7 p7177 (rvc p227 p6959 (rvc p197 p6991 (rvc p3 p7187 (rvc p5 p7187 (rvc p197 p6997 (rvc p3 p7193 (rvc p197 p7001 (rvc p7 p7193 (rvc p499 p6703 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg6404 (m : ℕ) (hl : 6404 ≤ m) (hh : m ≤ 7203) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-6404)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 6404+2*k := by simp [k]; omega
  have hk : k < qg6404.length := by simp [k,qg6404]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg6404 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg7204 : List ℕ := [7193,7187,6709,7207,7193,7211,7213,7207,7213,7219,7027,7207,7001,7211,7229,7229,7039,7219,7237,7237,7237,7243,7229,7247,7247,7057,7253,7247,7253,7243,7253,7247,6037,7043,7253,6043,7079,6047,6781,7103,6053,7283,7283,7283,6793,7283,7019,6067,7297,7283,7297,7109,7297,7307,7309,7307,7297,7121,7309,6091,7321,7307,7309,7151,7321,7331,7333,7331,7321,7331,7333,7069,7151,7331,7349,7351,7159,7351,7349,7351,6133,7187,7349,7351,7369,7177,7369,7151,7369,6151,7187,7207,7369,7193,7213,6163,7393,7393,7393,7001,7207,6907,7211,7213,7393,7411,7219,7411,7417,7411,7417,7229,7417,7411,7253,7237,7433,7433,7243,6211,7247,6947,6217,7253,7433,7451,7451,7451,7457,7459,7457,7459,7457,7451,4111,7247,7457,7459,7477,7477,7481,7481,7477,7487,7489,7297,7477,7487,7481,7499,7307,7487,7489,7507,7507,7507,7013,7499,7517,7517,7517,7523,7331,7333,7529,7523,7517,7039,7537,7523,7541,7349,7529,7547,7549,7547,7537,7547,7541,7559,7561,7547,7549,7559,7561,6343,7573,7559,7577,7577,7573,7583,7577,7393,7589,7591,7577,7591,7589,7583,6373,7603,7589,7607,7607,7417,7477,7607,6389,7603,7621,7607,7621,7433,7621,6343,7457,7459,7621,7639,7639,7643,7451,7639,7649,7457,7459,7639,7649,7643,6373,7487,7649,7393,7669,7477,7673,7481,7669,6451,7681,7489,7669,7687,7673,7691,7499,7687,7681,7699,7507,7703,7703,7691,6481,7517,7537,7699,7717,7703,7717,7723,7717,7727,7727,7537,7717,7541,7561,7723,7741,7727,7741,7523,7741,7477,7753,7561,7757,7759,7753,7759,7757,7573,7753,7577,7757,7759,7583,6551,6553,7589,7591,7717,7789,7789,7793,7793,7603,6571,7607,7307,7789,7583,7793,7537,7589,7621,7817,7817,7817,7823,7817,7823,7829,7823,7817,6607,7643,7823,7841,7649,7829,6619,7841,7577,7853,7853,7841,6571,7853,7669,6637,7867,7853,7867,7873,7681,7877,7879,7687,7883,7691,7879,7873,7883,7877,7879,7703,7883,7901,7901,7901,7907,7901,7717,7417,7907,7901,7919,7727,7907,6637,7927,7927,7927,7933,7919,7937,7937,7933,7927,7937,7753,7949,7951,7937,7951,7949,7951,6733,7963,7949,7951,7793,7963,7477,7577,7481,7963,7757,7789,7489,7793,6761,6763,7993,7993,7993,7823]
private theorem vg7204 : rvld 1 7204 qg7204 := by
  unfold qg7204
  exact rvc p11 p7193 (rvc p19 p7187 (rvc p499 p6709 (rvc p3 p7207 (rvc p19 p7193 (rvc p3 p7211 (rvc p3 p7213 (rvc p11 p7207 (rvc p7 p7213 (rvc p3 p7219 (rvc p197 p7027 (rvc p19 p7207 (rvc p227 p7001 (rvc p19 p7211 (rvc p3 p7229 (rvc p5 p7229 (rvc p197 p7039 (rvc p19 p7219 (rvc p3 p7237 (rvc p5 p7237 (rvc p7 p7237 (rvc p3 p7243 (rvc p19 p7229 (rvc p3 p7247 (rvc p5 p7247 (rvc p197 p7057 (rvc p3 p7253 (rvc p11 p7247 (rvc p7 p7253 (rvc p19 p7243 (rvc p11 p7253 (rvc p19 p7247 (rvc p1231 p6037 (rvc p227 p7043 (rvc p19 p7253 (rvc p1231 p6043 (rvc p197 p7079 (rvc p1231 p6047 (rvc p499 p6781 (rvc p179 p7103 (rvc p1231 p6053 (rvc p3 p7283 (rvc p5 p7283 (rvc p7 p7283 (rvc p499 p6793 (rvc p11 p7283 (rvc p277 p7019 (rvc p1231 p6067 (rvc p3 p7297 (rvc p19 p7283 (rvc p7 p7297 (rvc p197 p7109 (rvc p11 p7297 (rvc p3 p7307 (rvc p3 p7309 (rvc p7 p7307 (rvc p19 p7297 (rvc p197 p7121 (rvc p11 p7309 (rvc p1231 p6091 (rvc p3 p7321 (rvc p19 p7307 (rvc p19 p7309 (rvc p179 p7151 (rvc p11 p7321 (rvc p3 p7331 (rvc p3 p7333 (rvc p7 p7331 (rvc p19 p7321 (rvc p11 p7331 (rvc p11 p7333 (rvc p277 p7069 (rvc p197 p7151 (rvc p19 p7331 (rvc p3 p7349 (rvc p3 p7351 (rvc p197 p7159 (rvc p7 p7351 (rvc p11 p7349 (rvc p11 p7351 (rvc p1231 p6133 (rvc p179 p7187 (rvc p19 p7349 (rvc p19 p7351 (rvc p3 p7369 (rvc p197 p7177 (rvc p7 p7369 (rvc p227 p7151 (rvc p11 p7369 (rvc p1231 p6151 (rvc p197 p7187 (rvc p179 p7207 (rvc p19 p7369 (rvc p197 p7193 (rvc p179 p7213 (rvc p1231 p6163 (rvc p3 p7393 (rvc p5 p7393 (rvc p7 p7393 (rvc p401 p7001 (rvc p197 p7207 (rvc p499 p6907 (rvc p197 p7211 (rvc p197 p7213 (rvc p19 p7393 (rvc p3 p7411 (rvc p197 p7219 (rvc p7 p7411 (rvc p3 p7417 (rvc p11 p7411 (rvc p7 p7417 (rvc p197 p7229 (rvc p11 p7417 (rvc p19 p7411 (rvc p179 p7253 (rvc p197 p7237 (rvc p3 p7433 (rvc p5 p7433 (rvc p197 p7243 (rvc p1231 p6211 (rvc p197 p7247 (rvc p499 p6947 (rvc p1231 p6217 (rvc p197 p7253 (rvc p19 p7433 (rvc p3 p7451 (rvc p5 p7451 (rvc p7 p7451 (rvc p3 p7457 (rvc p3 p7459 (rvc p7 p7457 (rvc p7 p7459 (rvc p11 p7457 (rvc p19 p7451 (rvc p3361 p4111 (rvc p227 p7247 (rvc p19 p7457 (rvc p19 p7459 (rvc p3 p7477 (rvc p5 p7477 (rvc p3 p7481 (rvc p5 p7481 (rvc p11 p7477 (rvc p3 p7487 (rvc p3 p7489 (rvc p197 p7297 (rvc p19 p7477 (rvc p11 p7487 (rvc p19 p7481 (rvc p3 p7499 (rvc p197 p7307 (rvc p19 p7487 (rvc p19 p7489 (rvc p3 p7507 (rvc p5 p7507 (rvc p7 p7507 (rvc p503 p7013 (rvc p19 p7499 (rvc p3 p7517 (rvc p5 p7517 (rvc p7 p7517 (rvc p3 p7523 (rvc p197 p7331 (rvc p197 p7333 (rvc p3 p7529 (rvc p11 p7523 (rvc p19 p7517 (rvc p499 p7039 (rvc p3 p7537 (rvc p19 p7523 (rvc p3 p7541 (rvc p197 p7349 (rvc p19 p7529 (rvc p3 p7547 (rvc p3 p7549 (rvc p7 p7547 (rvc p19 p7537 (rvc p11 p7547 (rvc p19 p7541 (rvc p3 p7559 (rvc p3 p7561 (rvc p19 p7547 (rvc p19 p7549 (rvc p11 p7559 (rvc p11 p7561 (rvc p1231 p6343 (rvc p3 p7573 (rvc p19 p7559 (rvc p3 p7577 (rvc p5 p7577 (rvc p11 p7573 (rvc p3 p7583 (rvc p11 p7577 (rvc p197 p7393 (rvc p3 p7589 (rvc p3 p7591 (rvc p19 p7577 (rvc p7 p7591 (rvc p11 p7589 (rvc p19 p7583 (rvc p1231 p6373 (rvc p3 p7603 (rvc p19 p7589 (rvc p3 p7607 (rvc p5 p7607 (rvc p197 p7417 (rvc p139 p7477 (rvc p11 p7607 (rvc p1231 p6389 (rvc p19 p7603 (rvc p3 p7621 (rvc p19 p7607 (rvc p7 p7621 (rvc p197 p7433 (rvc p11 p7621 (rvc p1291 p6343 (rvc p179 p7457 (rvc p179 p7459 (rvc p19 p7621 (rvc p3 p7639 (rvc p5 p7639 (rvc p3 p7643 (rvc p197 p7451 (rvc p11 p7639 (rvc p3 p7649 (rvc p197 p7457 (rvc p197 p7459 (rvc p19 p7639 (rvc p11 p7649 (rvc p19 p7643 (rvc p1291 p6373 (rvc p179 p7487 (rvc p19 p7649 (rvc p277 p7393 (rvc p3 p7669 (rvc p197 p7477 (rvc p3 p7673 (rvc p197 p7481 (rvc p11 p7669 (rvc p1231 p6451 (rvc p3 p7681 (rvc p197 p7489 (rvc p19 p7669 (rvc p3 p7687 (rvc p19 p7673 (rvc p3 p7691 (rvc p197 p7499 (rvc p11 p7687 (rvc p19 p7681 (rvc p3 p7699 (rvc p197 p7507 (rvc p3 p7703 (rvc p5 p7703 (rvc p19 p7691 (rvc p1231 p6481 (rvc p197 p7517 (rvc p179 p7537 (rvc p19 p7699 (rvc p3 p7717 (rvc p19 p7703 (rvc p7 p7717 (rvc p3 p7723 (rvc p11 p7717 (rvc p3 p7727 (rvc p5 p7727 (rvc p197 p7537 (rvc p19 p7717 (rvc p197 p7541 (rvc p179 p7561 (rvc p19 p7723 (rvc p3 p7741 (rvc p19 p7727 (rvc p7 p7741 (rvc p227 p7523 (rvc p11 p7741 (rvc p277 p7477 (rvc p3 p7753 (rvc p197 p7561 (rvc p3 p7757 (rvc p3 p7759 (rvc p11 p7753 (rvc p7 p7759 (rvc p11 p7757 (rvc p197 p7573 (rvc p19 p7753 (rvc p197 p7577 (rvc p19 p7757 (rvc p19 p7759 (rvc p197 p7583 (rvc p1231 p6551 (rvc p1231 p6553 (rvc p197 p7589 (rvc p197 p7591 (rvc p73 p7717 (rvc p3 p7789 (rvc p5 p7789 (rvc p3 p7793 (rvc p5 p7793 (rvc p197 p7603 (rvc p1231 p6571 (rvc p197 p7607 (rvc p499 p7307 (rvc p19 p7789 (rvc p227 p7583 (rvc p19 p7793 (rvc p277 p7537 (rvc p227 p7589 (rvc p197 p7621 (rvc p3 p7817 (rvc p5 p7817 (rvc p7 p7817 (rvc p3 p7823 (rvc p11 p7817 (rvc p7 p7823 (rvc p3 p7829 (rvc p11 p7823 (rvc p19 p7817 (rvc p1231 p6607 (rvc p197 p7643 (rvc p19 p7823 (rvc p3 p7841 (rvc p197 p7649 (rvc p19 p7829 (rvc p1231 p6619 (rvc p11 p7841 (rvc p277 p7577 (rvc p3 p7853 (rvc p5 p7853 (rvc p19 p7841 (rvc p1291 p6571 (rvc p11 p7853 (rvc p197 p7669 (rvc p1231 p6637 (rvc p3 p7867 (rvc p19 p7853 (rvc p7 p7867 (rvc p3 p7873 (rvc p197 p7681 (rvc p3 p7877 (rvc p3 p7879 (rvc p197 p7687 (rvc p3 p7883 (rvc p197 p7691 (rvc p11 p7879 (rvc p19 p7873 (rvc p11 p7883 (rvc p19 p7877 (rvc p19 p7879 (rvc p197 p7703 (rvc p19 p7883 (rvc p3 p7901 (rvc p5 p7901 (rvc p7 p7901 (rvc p3 p7907 (rvc p11 p7901 (rvc p197 p7717 (rvc p499 p7417 (rvc p11 p7907 (rvc p19 p7901 (rvc p3 p7919 (rvc p197 p7727 (rvc p19 p7907 (rvc p1291 p6637 (rvc p3 p7927 (rvc p5 p7927 (rvc p7 p7927 (rvc p3 p7933 (rvc p19 p7919 (rvc p3 p7937 (rvc p5 p7937 (rvc p11 p7933 (rvc p19 p7927 (rvc p11 p7937 (rvc p197 p7753 (rvc p3 p7949 (rvc p3 p7951 (rvc p19 p7937 (rvc p7 p7951 (rvc p11 p7949 (rvc p11 p7951 (rvc p1231 p6733 (rvc p3 p7963 (rvc p19 p7949 (rvc p19 p7951 (rvc p179 p7793 (rvc p11 p7963 (rvc p499 p7477 (rvc p401 p7577 (rvc p499 p7481 (rvc p19 p7963 (rvc p227 p7757 (rvc p197 p7789 (rvc p499 p7489 (rvc p197 p7793 (rvc p1231 p6761 (rvc p1231 p6763 (rvc p3 p7993 (rvc p5 p7993 (rvc p7 p7993 (rvc p179 p7823 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xg7204 (m : ℕ) (hl : 7204 ≤ m) (hh : m ≤ 8003) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-7204)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 7204+2*k := by simp [k]; omega
  have hk : k < qg7204.length := by simp [k,qg7204]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg7204 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def qg8004 : List ℕ := [7993,7507,7829,6779,8009]
private theorem vg8004 : rvld 1 8004 qg8004 := by
  unfold qg8004
  exact rvc p11 p7993 (rvc p499 p7507 (rvc p179 p7829 (rvc p1231 p6779 (rvc p3 p8009 (True.intro)))))
private theorem xg8004 (m : ℕ) (hl : 8004 ≤ m) (hh : m ≤ 8012) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  let k := (m-8004)/2
  have hm : m % 2 = 0 := Nat.even_iff.mp he
  have heq : m = 8004+2*k := by simp [k]; omega
  have hk : k < qg8004.length := by simp [k,qg8004]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vg8004 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private theorem goldbach_bounded (m : ℕ) (hl : 4 ≤ m) (hh : m ≤ 8012) (he : Even m) :
    ∃ q ∈ Finset.range (m+1), (m-1*q).Prime ∧ q.Prime ∧ m=(m-1*q)+1*q := by
  by_cases h : m ≤ 803
  · exact xg4 m (by omega) h he
  by_cases h : m ≤ 1603
  · exact xg804 m (by omega) h he
  by_cases h : m ≤ 2403
  · exact xg1604 m (by omega) h he
  by_cases h : m ≤ 3203
  · exact xg2404 m (by omega) h he
  by_cases h : m ≤ 4003
  · exact xg3204 m (by omega) h he
  by_cases h : m ≤ 4803
  · exact xg4004 m (by omega) h he
  by_cases h : m ≤ 5603
  · exact xg4804 m (by omega) h he
  by_cases h : m ≤ 6403
  · exact xg5604 m (by omega) h he
  by_cases h : m ≤ 7203
  · exact xg6404 m (by omega) h he
  by_cases h : m ≤ 8003
  · exact xg7204 m (by omega) h he
  exact xg8004 m (by omega) hh he

private def ql7 : List ℕ := [2,3,3,5,5,7,3,2,3,11,5,13,7,2,11,17,11,19,13,19,17,23,17,5,19,7,23,29,23,31,19,13,2,3,29,37,31,7,23,41,37,43,37,13,41,47,41,17,43,19,47,53,47,23,3,5,5,59,53,61,37,31,11,13,59,67,61,37,17,71,19,73,67,43,23,13,71,79,73,17,29,83,31,53,79,23,83,89,83,59,7,61,41,31,89,97,13,67,47,101,97,103,97,73,53,107,101,109,103,79,59,113,107,83,109,53,113,67,113,89,37,59,71,61,73,127,43,97,53,131,79,101,127,103,83,137,131,139,127,109,89,79,137,113,139,83,71,149,97,151,67,89,101,37,149,157,151,127,107,97,109,163,157,101,113,167,163,137,163,139,167,173,167,107,163,113,173,179,173,181,97,151,131,67,179,167,181,157,137,191,139,193,109,163,191,197,191,199,193,137,149,139,197,173,199,139,41,157,157,211,13,181,47,151,163,149,211,151,167,157,23,223,139,193,173,227,29,229,223,199,179,233,227,167,229,173,233,239,233,241,43,211,191,181,239,179,241,181,197,251,199,233,241,223,251,257,251,227,61,229,257,263,257,233,67,199,263,269,263,271,73,241,269,211,269,277,271,211,227,281,229,283,277,167,233,223,281,257,283,227,239,293,241,263,97,233,293,181,293,269,103,271,251,241,107,307,109,277,257,311,113,313,307,283,263,317,311,251,313,257,269,271,317,293,127,263,251,211,277,331,3,269,281,271,283,337,331,307,173,277,337,311,337,313,293,347,149,349,151,283,347,353,347,107,349,293,353,359,353,293,163,331,311,313,359,367,283,337,317,307,173,373,367,311,47,313,179,379,373,349,53,383,331,353,379,269,383,389,383,359,193,373,389,331,389,397,199,367,347,401]
private theorem vl7 : rvld 2 7 ql7 := by
  unfold ql7
  exact rvc p3 p2 (rvc p3 p3 (rvc p5 p3 (rvc p3 p5 (rvc p5 p5 (rvc p3 p7 (rvc p13 p3 (rvc p17 p2 (rvc p17 p3 (rvc p3 p11 (rvc p17 p5 (rvc p3 p13 (rvc p17 p7 (rvc p29 p2 (rvc p13 p11 (rvc p3 p17 (rvc p17 p11 (rvc p3 p19 (rvc p17 p13 (rvc p7 p19 (rvc p13 p17 (rvc p3 p23 (rvc p17 p17 (rvc p43 p5 (rvc p17 p19 (rvc p43 p7 (rvc p13 p23 (rvc p3 p29 (rvc p17 p23 (rvc p3 p31 (rvc p29 p19 (rvc p43 p13 (rvc p67 p2 (rvc p67 p3 (rvc p17 p29 (rvc p3 p37 (rvc p17 p31 (rvc p67 p7 (rvc p37 p23 (rvc p3 p41 (rvc p13 p37 (rvc p3 p43 (rvc p17 p37 (rvc p67 p13 (rvc p13 p41 (rvc p3 p47 (rvc p17 p41 (rvc p67 p17 (rvc p17 p43 (rvc p67 p19 (rvc p13 p47 (rvc p3 p53 (rvc p17 p47 (rvc p67 p23 (rvc p109 p3 (rvc p107 p5 (rvc p109 p5 (rvc p3 p59 (rvc p17 p53 (rvc p3 p61 (rvc p53 p37 (rvc p67 p31 (rvc p109 p11 (rvc p107 p13 (rvc p17 p59 (rvc p3 p67 (rvc p17 p61 (rvc p67 p37 (rvc p109 p17 (rvc p3 p71 (rvc p109 p19 (rvc p3 p73 (rvc p17 p67 (rvc p67 p43 (rvc p109 p23 (rvc p131 p13 (rvc p17 p71 (rvc p3 p79 (rvc p17 p73 (rvc p131 p17 (rvc p109 p29 (rvc p3 p83 (rvc p109 p31 (rvc p67 p53 (rvc p17 p79 (rvc p131 p23 (rvc p13 p83 (rvc p3 p89 (rvc p17 p83 (rvc p67 p59 (rvc p173 p7 (rvc p67 p61 (rvc p109 p41 (rvc p131 p31 (rvc p17 p89 (rvc p3 p97 (rvc p173 p13 (rvc p67 p67 (rvc p109 p47 (rvc p3 p101 (rvc p13 p97 (rvc p3 p103 (rvc p17 p97 (rvc p67 p73 (rvc p109 p53 (rvc p3 p107 (rvc p17 p101 (rvc p3 p109 (rvc p17 p103 (rvc p67 p79 (rvc p109 p59 (rvc p3 p113 (rvc p17 p107 (rvc p67 p83 (rvc p17 p109 (rvc p131 p53 (rvc p13 p113 (rvc p107 p67 (rvc p17 p113 (rvc p67 p89 (rvc p173 p37 (rvc p131 p59 (rvc p109 p71 (rvc p131 p61 (rvc p109 p73 (rvc p3 p127 (rvc p173 p43 (rvc p67 p97 (rvc p157 p53 (rvc p3 p131 (rvc p109 p79 (rvc p67 p101 (rvc p17 p127 (rvc p67 p103 (rvc p109 p83 (rvc p3 p137 (rvc p17 p131 (rvc p3 p139 (rvc p29 p127 (rvc p67 p109 (rvc p109 p89 (rvc p131 p79 (rvc p17 p137 (rvc p67 p113 (rvc p17 p139 (rvc p131 p83 (rvc p157 p71 (rvc p3 p149 (rvc p109 p97 (rvc p3 p151 (rvc p173 p67 (rvc p131 p89 (rvc p109 p101 (rvc p239 p37 (rvc p17 p149 (rvc p3 p157 (rvc p17 p151 (rvc p67 p127 (rvc p109 p107 (rvc p131 p97 (rvc p109 p109 (rvc p3 p163 (rvc p17 p157 (rvc p131 p101 (rvc p109 p113 (rvc p3 p167 (rvc p13 p163 (rvc p67 p137 (rvc p17 p163 (rvc p67 p139 (rvc p13 p167 (rvc p3 p173 (rvc p17 p167 (rvc p139 p107 (rvc p29 p163 (rvc p131 p113 (rvc p13 p173 (rvc p3 p179 (rvc p17 p173 (rvc p3 p181 (rvc p173 p97 (rvc p67 p151 (rvc p109 p131 (rvc p239 p67 (rvc p17 p179 (rvc p43 p167 (rvc p17 p181 (rvc p67 p157 (rvc p109 p137 (rvc p3 p191 (rvc p109 p139 (rvc p3 p193 (rvc p173 p109 (rvc p67 p163 (rvc p13 p191 (rvc p3 p197 (rvc p17 p191 (rvc p3 p199 (rvc p17 p193 (rvc p131 p137 (rvc p109 p149 (rvc p131 p139 (rvc p17 p197 (rvc p67 p173 (rvc p17 p199 (rvc p139 p139 (rvc p337 p41 (rvc p107 p157 (rvc p109 p157 (rvc p3 p211 (rvc p401 p13 (rvc p67 p181 (rvc p337 p47 (rvc p131 p151 (rvc p109 p163 (rvc p139 p149 (rvc p17 p211 (rvc p139 p151 (rvc p109 p167 (rvc p131 p157 (rvc p401 p23 (rvc p3 p223 (rvc p173 p139 (rvc p67 p193 (rvc p109 p173 (rvc p3 p227 (rvc p401 p29 (rvc p3 p229 (rvc p17 p223 (rvc p67 p199 (rvc p109 p179 (rvc p3 p233 (rvc p17 p227 (rvc p139 p167 (rvc p17 p229 (rvc p131 p173 (rvc p13 p233 (rvc p3 p239 (rvc p17 p233 (rvc p3 p241 (rvc p401 p43 (rvc p67 p211 (rvc p109 p191 (rvc p131 p181 (rvc p17 p239 (rvc p139 p179 (rvc p17 p241 (rvc p139 p181 (rvc p109 p197 (rvc p3 p251 (rvc p109 p199 (rvc p43 p233 (rvc p29 p241 (rvc p67 p223 (rvc p13 p251 (rvc p3 p257 (rvc p17 p251 (rvc p67 p227 (rvc p401 p61 (rvc p67 p229 (rvc p13 p257 (rvc p3 p263 (rvc p17 p257 (rvc p67 p233 (rvc p401 p67 (rvc p139 p199 (rvc p13 p263 (rvc p3 p269 (rvc p17 p263 (rvc p3 p271 (rvc p401 p73 (rvc p67 p241 (rvc p13 p269 (rvc p131 p211 (rvc p17 p269 (rvc p3 p277 (rvc p17 p271 (rvc p139 p211 (rvc p109 p227 (rvc p3 p281 (rvc p109 p229 (rvc p3 p283 (rvc p17 p277 (rvc p239 p167 (rvc p109 p233 (rvc p131 p223 (rvc p17 p281 (rvc p67 p257 (rvc p17 p283 (rvc p131 p227 (rvc p109 p239 (rvc p3 p293 (rvc p109 p241 (rvc p67 p263 (rvc p401 p97 (rvc p131 p233 (rvc p13 p293 (rvc p239 p181 (rvc p17 p293 (rvc p67 p269 (rvc p401 p103 (rvc p67 p271 (rvc p109 p251 (rvc p131 p241 (rvc p401 p107 (rvc p3 p307 (rvc p401 p109 (rvc p67 p277 (rvc p109 p257 (rvc p3 p311 (rvc p401 p113 (rvc p3 p313 (rvc p17 p307 (rvc p67 p283 (rvc p109 p263 (rvc p3 p317 (rvc p17 p311 (rvc p139 p251 (rvc p17 p313 (rvc p131 p257 (rvc p109 p269 (rvc p107 p271 (rvc p17 p317 (rvc p67 p293 (rvc p401 p127 (rvc p131 p263 (rvc p157 p251 (rvc p239 p211 (rvc p109 p277 (rvc p3 p331 (rvc p661 p3 (rvc p131 p269 (rvc p109 p281 (rvc p131 p271 (rvc p109 p283 (rvc p3 p337 (rvc p17 p331 (rvc p67 p307 (rvc p337 p173 (rvc p131 p277 (rvc p13 p337 (rvc p67 p311 (rvc p17 p337 (rvc p67 p313 (rvc p109 p293 (rvc p3 p347 (rvc p401 p149 (rvc p3 p349 (rvc p401 p151 (rvc p139 p283 (rvc p13 p347 (rvc p3 p353 (rvc p17 p347 (rvc p499 p107 (rvc p17 p349 (rvc p131 p293 (rvc p13 p353 (rvc p3 p359 (rvc p17 p353 (rvc p139 p293 (rvc p401 p163 (rvc p67 p331 (rvc p109 p311 (rvc p107 p313 (rvc p17 p359 (rvc p3 p367 (rvc p173 p283 (rvc p67 p337 (rvc p109 p317 (rvc p131 p307 (rvc p401 p173 (rvc p3 p373 (rvc p17 p367 (rvc p131 p311 (rvc p661 p47 (rvc p131 p313 (rvc p401 p179 (rvc p3 p379 (rvc p17 p373 (rvc p67 p349 (rvc p661 p53 (rvc p3 p383 (rvc p109 p331 (rvc p67 p353 (rvc p17 p379 (rvc p239 p269 (rvc p13 p383 (rvc p3 p389 (rvc p17 p383 (rvc p67 p359 (rvc p401 p193 (rvc p43 p373 (rvc p13 p389 (rvc p131 p331 (rvc p17 p389 (rvc p3 p397 (rvc p401 p199 (rvc p67 p367 (rvc p109 p347 (rvc p3 p401 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl7 (m : ℕ) (hl : 7 ≤ m) (hh : m ≤ 806) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-7)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 7+2*k := by simp [k]; omega
  have hk : k < ql7.length := by simp [k,ql7]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl7 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql807 : List ℕ := [349,383,397,373,353,367,401,409,211,379,359,349,409,383,409,353,251,419,367,421,223,359,419,307,419,359,421,397,263,431,379,433,349,367,383,373,431,439,433,409,389,443,439,197,439,383,443,449,443,419,367,421,401,337,449,457,373,439,293,461,409,463,457,433,461,467,461,401,463,439,419,409,467,443,277,409,311,479,281,449,283,419,431,421,479,487,463,457,461,491,439,461,487,463,443,433,491,499,487,433,449,503,499,257,499,443,503,509,503,479,313,449,461,397,509,449,433,487,467,521,193,523,439,461,521,463,521,461,523,499,479,421,367,503,337,419,461,421,487,541,457,479,491,433,347,547,541,431,383,487,499,521,547,523,503,557,359,491,547,443,509,563,557,317,367,503,563,569,563,571,373,541,521,457,569,577,571,547,251,463,383,563,577,521,419,587,389,557,577,523,587,593,587,563,397,479,593,599,593,601,577,571,599,541,599,607,601,577,557,547,607,613,607,547,563,617,419,619,613,557,569,571,617,593,619,563,461,577,577,631,433,601,467,571,631,569,631,607,587,641,443,643,631,613,593,647,641,617,643,619,599,653,647,587,457,593,653,659,653,661,463,631,659,601,659,599,661,601,617,607,619,673,661,643,509,677,479,647,673,617,677,683,677,653,487,619,683,571,683,691,607,661,641,631,643,677,691,631,647,701,503,683,619,673,653,643,701,709,487,647,659,661,661,683,709,653,389,719,521,653,523,691,719,661,719,727,643,661,677,613,727,733,727,617,683,673,733,739,733,709,317,743,691,677,739,683,743,631,743,751,739,701,701,691,557,757,751,727,593,761,709,743,757,733,761,727,761,769,571,739,719,773,769,743,769,709,773,661,773,761,769,751,617,733,733,787,13,757,461,727,739,761,787,727,743,797,599,557,601,769]
private theorem vl807 : rvld 2 807 ql807 := by
  unfold ql807
  exact rvc p109 p349 (rvc p43 p383 (rvc p17 p397 (rvc p67 p373 (rvc p109 p353 (rvc p83 p367 (rvc p17 p401 (rvc p3 p409 (rvc p401 p211 (rvc p67 p379 (rvc p109 p359 (rvc p131 p349 (rvc p13 p409 (rvc p67 p383 (rvc p17 p409 (rvc p131 p353 (rvc p337 p251 (rvc p3 p419 (rvc p109 p367 (rvc p3 p421 (rvc p401 p223 (rvc p131 p359 (rvc p13 p419 (rvc p239 p307 (rvc p17 p419 (rvc p139 p359 (rvc p17 p421 (rvc p67 p397 (rvc p337 p263 (rvc p3 p431 (rvc p109 p379 (rvc p3 p433 (rvc p173 p349 (rvc p139 p367 (rvc p109 p383 (rvc p131 p373 (rvc p17 p431 (rvc p3 p439 (rvc p17 p433 (rvc p67 p409 (rvc p109 p389 (rvc p3 p443 (rvc p13 p439 (rvc p499 p197 (rvc p17 p439 (rvc p131 p383 (rvc p13 p443 (rvc p3 p449 (rvc p17 p443 (rvc p67 p419 (rvc p173 p367 (rvc p67 p421 (rvc p109 p401 (rvc p239 p337 (rvc p17 p449 (rvc p3 p457 (rvc p173 p373 (rvc p43 p439 (rvc p337 p293 (rvc p3 p461 (rvc p109 p409 (rvc p3 p463 (rvc p17 p457 (rvc p67 p433 (rvc p13 p461 (rvc p3 p467 (rvc p17 p461 (rvc p139 p401 (rvc p17 p463 (rvc p67 p439 (rvc p109 p419 (rvc p131 p409 (rvc p17 p467 (rvc p67 p443 (rvc p401 p277 (rvc p139 p409 (rvc p337 p311 (rvc p3 p479 (rvc p401 p281 (rvc p67 p449 (rvc p401 p283 (rvc p131 p419 (rvc p109 p431 (rvc p131 p421 (rvc p17 p479 (rvc p3 p487 (rvc p53 p463 (rvc p67 p457 (rvc p61 p461 (rvc p3 p491 (rvc p109 p439 (rvc p67 p461 (rvc p17 p487 (rvc p67 p463 (rvc p109 p443 (rvc p131 p433 (rvc p17 p491 (rvc p3 p499 (rvc p29 p487 (rvc p139 p433 (rvc p109 p449 (rvc p3 p503 (rvc p13 p499 (rvc p499 p257 (rvc p17 p499 (rvc p131 p443 (rvc p13 p503 (rvc p3 p509 (rvc p17 p503 (rvc p67 p479 (rvc p401 p313 (rvc p131 p449 (rvc p109 p461 (rvc p239 p397 (rvc p17 p509 (rvc p139 p449 (rvc p173 p433 (rvc p67 p487 (rvc p109 p467 (rvc p3 p521 (rvc p661 p193 (rvc p3 p523 (rvc p173 p439 (rvc p131 p461 (rvc p13 p521 (rvc p131 p463 (rvc p17 p521 (rvc p139 p461 (rvc p17 p523 (rvc p67 p499 (rvc p109 p479 (rvc p227 p421 (rvc p337 p367 (rvc p67 p503 (rvc p401 p337 (rvc p239 p419 (rvc p157 p461 (rvc p239 p421 (rvc p109 p487 (rvc p3 p541 (rvc p173 p457 (rvc p131 p479 (rvc p109 p491 (rvc p227 p433 (rvc p401 p347 (rvc p3 p547 (rvc p17 p541 (rvc p239 p431 (rvc p337 p383 (rvc p131 p487 (rvc p109 p499 (rvc p67 p521 (rvc p17 p547 (rvc p67 p523 (rvc p109 p503 (rvc p3 p557 (rvc p401 p359 (rvc p139 p491 (rvc p29 p547 (rvc p239 p443 (rvc p109 p509 (rvc p3 p563 (rvc p17 p557 (rvc p499 p317 (rvc p401 p367 (rvc p131 p503 (rvc p13 p563 (rvc p3 p569 (rvc p17 p563 (rvc p3 p571 (rvc p401 p373 (rvc p67 p541 (rvc p109 p521 (rvc p239 p457 (rvc p17 p569 (rvc p3 p577 (rvc p17 p571 (rvc p67 p547 (rvc p661 p251 (rvc p239 p463 (rvc p401 p383 (rvc p43 p563 (rvc p17 p577 (rvc p131 p521 (rvc p337 p419 (rvc p3 p587 (rvc p401 p389 (rvc p67 p557 (rvc p29 p577 (rvc p139 p523 (rvc p13 p587 (rvc p3 p593 (rvc p17 p587 (rvc p67 p563 (rvc p401 p397 (rvc p239 p479 (rvc p13 p593 (rvc p3 p599 (rvc p17 p593 (rvc p3 p601 (rvc p53 p577 (rvc p67 p571 (rvc p13 p599 (rvc p131 p541 (rvc p17 p599 (rvc p3 p607 (rvc p17 p601 (rvc p67 p577 (rvc p109 p557 (rvc p131 p547 (rvc p13 p607 (rvc p3 p613 (rvc p17 p607 (rvc p139 p547 (rvc p109 p563 (rvc p3 p617 (rvc p401 p419 (rvc p3 p619 (rvc p17 p613 (rvc p131 p557 (rvc p109 p569 (rvc p107 p571 (rvc p17 p617 (rvc p67 p593 (rvc p17 p619 (rvc p131 p563 (rvc p337 p461 (rvc p107 p577 (rvc p109 p577 (rvc p3 p631 (rvc p401 p433 (rvc p67 p601 (rvc p337 p467 (rvc p131 p571 (rvc p13 p631 (rvc p139 p569 (rvc p17 p631 (rvc p67 p607 (rvc p109 p587 (rvc p3 p641 (rvc p401 p443 (rvc p3 p643 (rvc p29 p631 (rvc p67 p613 (rvc p109 p593 (rvc p3 p647 (rvc p17 p641 (rvc p67 p617 (rvc p17 p643 (rvc p67 p619 (rvc p109 p599 (rvc p3 p653 (rvc p17 p647 (rvc p139 p587 (rvc p401 p457 (rvc p131 p593 (rvc p13 p653 (rvc p3 p659 (rvc p17 p653 (rvc p3 p661 (rvc p401 p463 (rvc p67 p631 (rvc p13 p659 (rvc p131 p601 (rvc p17 p659 (rvc p139 p599 (rvc p17 p661 (rvc p139 p601 (rvc p109 p617 (rvc p131 p607 (rvc p109 p619 (rvc p3 p673 (rvc p29 p661 (rvc p67 p643 (rvc p337 p509 (rvc p3 p677 (rvc p401 p479 (rvc p67 p647 (rvc p17 p673 (rvc p131 p617 (rvc p13 p677 (rvc p3 p683 (rvc p17 p677 (rvc p67 p653 (rvc p401 p487 (rvc p139 p619 (rvc p13 p683 (rvc p239 p571 (rvc p17 p683 (rvc p3 p691 (rvc p173 p607 (rvc p67 p661 (rvc p109 p641 (rvc p131 p631 (rvc p109 p643 (rvc p43 p677 (rvc p17 p691 (rvc p139 p631 (rvc p109 p647 (rvc p3 p701 (rvc p401 p503 (rvc p43 p683 (rvc p173 p619 (rvc p67 p673 (rvc p109 p653 (rvc p131 p643 (rvc p17 p701 (rvc p3 p709 (rvc p449 p487 (rvc p131 p647 (rvc p109 p659 (rvc p107 p661 (rvc p109 p661 (rvc p67 p683 (rvc p17 p709 (rvc p131 p653 (rvc p661 p389 (rvc p3 p719 (rvc p401 p521 (rvc p139 p653 (rvc p401 p523 (rvc p67 p691 (rvc p13 p719 (rvc p131 p661 (rvc p17 p719 (rvc p3 p727 (rvc p173 p643 (rvc p139 p661 (rvc p109 p677 (rvc p239 p613 (rvc p13 p727 (rvc p3 p733 (rvc p17 p727 (rvc p239 p617 (rvc p109 p683 (rvc p131 p673 (rvc p13 p733 (rvc p3 p739 (rvc p17 p733 (rvc p67 p709 (rvc p853 p317 (rvc p3 p743 (rvc p109 p691 (rvc p139 p677 (rvc p17 p739 (rvc p131 p683 (rvc p13 p743 (rvc p239 p631 (rvc p17 p743 (rvc p3 p751 (rvc p29 p739 (rvc p107 p701 (rvc p109 p701 (rvc p131 p691 (rvc p401 p557 (rvc p3 p757 (rvc p17 p751 (rvc p67 p727 (rvc p337 p593 (rvc p3 p761 (rvc p109 p709 (rvc p43 p743 (rvc p17 p757 (rvc p67 p733 (rvc p13 p761 (rvc p83 p727 (rvc p17 p761 (rvc p3 p769 (rvc p401 p571 (rvc p67 p739 (rvc p109 p719 (rvc p3 p773 (rvc p13 p769 (rvc p67 p743 (rvc p17 p769 (rvc p139 p709 (rvc p13 p773 (rvc p239 p661 (rvc p17 p773 (rvc p43 p761 (rvc p29 p769 (rvc p67 p751 (rvc p337 p617 (rvc p107 p733 (rvc p109 p733 (rvc p3 p787 (rvc p1553 p13 (rvc p67 p757 (rvc p661 p461 (rvc p131 p727 (rvc p109 p739 (rvc p67 p761 (rvc p17 p787 (rvc p139 p727 (rvc p109 p743 (rvc p3 p797 (rvc p401 p599 (rvc p487 p557 (rvc p401 p601 (rvc p67 p769 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl807 (m : ℕ) (hl : 807 ≤ m) (hh : m ≤ 1606) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-807)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 807+2*k := by simp [k]; omega
  have hk : k < ql807.length := by simp [k,ql807]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl807 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql1607 : List ℕ := [797,739,797,773,607,743,641,809,757,811,613,761,761,751,809,797,811,787,653,821,769,823,739,761,773,827,821,829,823,811,827,769,827,191,829,773,509,839,787,809,643,811,839,727,839,827,31,797,797,787,653,853,769,823,83,857,659,859,853,829,809,863,857,797,859,223,863,751,863,839,673,809,821,811,823,877,61,811,827,881,829,883,877,853,881,887,881,857,883,859,839,829,887,863,811,829,569,181,701,881,127,839,131,787,853,907,709,877,857,911,859,881,907,883,863,853,911,919,907,857,593,859,919,857,919,863,761,929,877,863,733,881,881,883,929,937,739,907,887,941,743,911,937,881,941,947,941,881,751,919,947,953,947,887,757,839,953,907,953,929,877,911,911,853,881,967,769,937,641,971,919,941,967,911,971,977,971,947,967,863,929,983,977,953,787,919,983,937,983,991,907,929,941,877,797,997,991,967,947,937,997,971,997,941,953,967,809,1009,811,947,683,1013,1009,983,1009,953,1013,1019,1013,1021,823,991,971,907,1019,383,1021,997,977,1031,947,1033,1021,971,983,919,1031,1039,1033,1009,269,991,991,1013,1039,983,881,1049,997,1051,853,1021,1049,991,1049,809,1051,991,191,1061,1009,1063,1051,1033,1013,349,1061,1069,1063,1039,1019,1009,1021,431,1069,1013,911,1039,881,1049,883,1051,1031,1021,1033,1087,271,1021,761,1091,1039,1093,1087,1063,1091,1097,1091,1031,1093,1069,1049,1103,1097,461,907,1039,1103,1109,1103,1091,337,1049,1061,1051,1109,1117,919,1087,953,1069,1069,1123,1117,1093,797,1063,929,1129,1123,1063,359,1069,1129,1103,1129,1069,971,1021,1087,1109,1129,1091,1091,1093,1093,503,1063,1117,1097,1151,953,1153,1069,1123,1103,1093,1151,1091,1153,1129,1109,1163,997,1097,967,1103,1163,1051,1163,1171,1087,1109,401,1123,1123,1109,1171,1061,1013,1181,1129,1151,1171,1153,1181,1187,1181,941,991,1123,1187,1193,1187,1163,997,1129,1193,1087,1193,1201]
private theorem vl1607 : rvld 2 1607 ql1607 := by
  unfold ql1607
  exact rvc p13 p797 (rvc p131 p739 (rvc p17 p797 (rvc p67 p773 (rvc p401 p607 (rvc p131 p743 (rvc p337 p641 (rvc p3 p809 (rvc p109 p757 (rvc p3 p811 (rvc p401 p613 (rvc p107 p761 (rvc p109 p761 (rvc p131 p751 (rvc p17 p809 (rvc p43 p797 (rvc p17 p811 (rvc p67 p787 (rvc p337 p653 (rvc p3 p821 (rvc p109 p769 (rvc p3 p823 (rvc p173 p739 (rvc p131 p761 (rvc p109 p773 (rvc p3 p827 (rvc p17 p821 (rvc p3 p829 (rvc p17 p823 (rvc p43 p811 (rvc p13 p827 (rvc p131 p769 (rvc p17 p827 (rvc p1291 p191 (rvc p17 p829 (rvc p131 p773 (rvc p661 p509 (rvc p3 p839 (rvc p109 p787 (rvc p67 p809 (rvc p401 p643 (rvc p67 p811 (rvc p13 p839 (rvc p239 p727 (rvc p17 p839 (rvc p43 p827 (rvc p1637 p31 (rvc p107 p797 (rvc p109 p797 (rvc p131 p787 (rvc p401 p653 (rvc p3 p853 (rvc p173 p769 (rvc p67 p823 (rvc p1549 p83 (rvc p3 p857 (rvc p401 p659 (rvc p3 p859 (rvc p17 p853 (rvc p67 p829 (rvc p109 p809 (rvc p3 p863 (rvc p17 p857 (rvc p139 p797 (rvc p17 p859 (rvc p1291 p223 (rvc p13 p863 (rvc p239 p751 (rvc p17 p863 (rvc p67 p839 (rvc p401 p673 (rvc p131 p809 (rvc p109 p821 (rvc p131 p811 (rvc p109 p823 (rvc p3 p877 (rvc p1637 p61 (rvc p139 p811 (rvc p109 p827 (rvc p3 p881 (rvc p109 p829 (rvc p3 p883 (rvc p17 p877 (rvc p67 p853 (rvc p13 p881 (rvc p3 p887 (rvc p17 p881 (rvc p67 p857 (rvc p17 p883 (rvc p67 p859 (rvc p109 p839 (rvc p131 p829 (rvc p17 p887 (rvc p67 p863 (rvc p173 p811 (rvc p139 p829 (rvc p661 p569 (rvc p1439 p181 (rvc p401 p701 (rvc p43 p881 (rvc p1553 p127 (rvc p131 p839 (rvc p1549 p131 (rvc p239 p787 (rvc p109 p853 (rvc p3 p907 (rvc p401 p709 (rvc p67 p877 (rvc p109 p857 (rvc p3 p911 (rvc p109 p859 (rvc p67 p881 (rvc p17 p907 (rvc p67 p883 (rvc p109 p863 (rvc p131 p853 (rvc p17 p911 (rvc p3 p919 (rvc p29 p907 (rvc p131 p857 (rvc p661 p593 (rvc p131 p859 (rvc p13 p919 (rvc p139 p857 (rvc p17 p919 (rvc p131 p863 (rvc p337 p761 (rvc p3 p929 (rvc p109 p877 (rvc p139 p863 (rvc p401 p733 (rvc p107 p881 (rvc p109 p881 (rvc p107 p883 (rvc p17 p929 (rvc p3 p937 (rvc p401 p739 (rvc p67 p907 (rvc p109 p887 (rvc p3 p941 (rvc p401 p743 (rvc p67 p911 (rvc p17 p937 (rvc p131 p881 (rvc p13 p941 (rvc p3 p947 (rvc p17 p941 (rvc p139 p881 (rvc p401 p751 (rvc p67 p919 (rvc p13 p947 (rvc p3 p953 (rvc p17 p947 (rvc p139 p887 (rvc p401 p757 (rvc p239 p839 (rvc p13 p953 (rvc p107 p907 (rvc p17 p953 (rvc p67 p929 (rvc p173 p877 (rvc p107 p911 (rvc p109 p911 (rvc p227 p853 (rvc p173 p881 (rvc p3 p967 (rvc p401 p769 (rvc p67 p937 (rvc p661 p641 (rvc p3 p971 (rvc p109 p919 (rvc p67 p941 (rvc p17 p967 (rvc p131 p911 (rvc p13 p971 (rvc p3 p977 (rvc p17 p971 (rvc p67 p947 (rvc p29 p967 (rvc p239 p863 (rvc p109 p929 (rvc p3 p983 (rvc p17 p977 (rvc p67 p953 (rvc p401 p787 (rvc p139 p919 (rvc p13 p983 (rvc p107 p937 (rvc p17 p983 (rvc p3 p991 (rvc p173 p907 (rvc p131 p929 (rvc p109 p941 (rvc p239 p877 (rvc p401 p797 (rvc p3 p997 (rvc p17 p991 (rvc p67 p967 (rvc p109 p947 (rvc p131 p937 (rvc p13 p997 (rvc p67 p971 (rvc p17 p997 (rvc p131 p941 (rvc p109 p953 (rvc p83 p967 (rvc p401 p809 (rvc p3 p1009 (rvc p401 p811 (rvc p131 p947 (rvc p661 p683 (rvc p3 p1013 (rvc p13 p1009 (rvc p67 p983 (rvc p17 p1009 (rvc p131 p953 (rvc p13 p1013 (rvc p3 p1019 (rvc p17 p1013 (rvc p3 p1021 (rvc p401 p823 (rvc p67 p991 (rvc p109 p971 (rvc p239 p907 (rvc p17 p1019 (rvc p1291 p383 (rvc p17 p1021 (rvc p67 p997 (rvc p109 p977 (rvc p3 p1031 (rvc p173 p947 (rvc p3 p1033 (rvc p29 p1021 (rvc p131 p971 (rvc p109 p983 (rvc p239 p919 (rvc p17 p1031 (rvc p3 p1039 (rvc p17 p1033 (rvc p67 p1009 (rvc p1549 p269 (rvc p107 p991 (rvc p109 p991 (rvc p67 p1013 (rvc p17 p1039 (rvc p131 p983 (rvc p337 p881 (rvc p3 p1049 (rvc p109 p997 (rvc p3 p1051 (rvc p401 p853 (rvc p67 p1021 (rvc p13 p1049 (rvc p131 p991 (rvc p17 p1049 (rvc p499 p809 (rvc p17 p1051 (rvc p139 p991 (rvc p1741 p191 (rvc p3 p1061 (rvc p109 p1009 (rvc p3 p1063 (rvc p29 p1051 (rvc p67 p1033 (rvc p109 p1013 (rvc p1439 p349 (rvc p17 p1061 (rvc p3 p1069 (rvc p17 p1063 (rvc p67 p1039 (rvc p109 p1019 (rvc p131 p1009 (rvc p109 p1021 (rvc p1291 p431 (rvc p17 p1069 (rvc p131 p1013 (rvc p337 p911 (rvc p83 p1039 (rvc p401 p881 (rvc p67 p1049 (rvc p401 p883 (rvc p67 p1051 (rvc p109 p1031 (rvc p131 p1021 (rvc p109 p1033 (rvc p3 p1087 (rvc p1637 p271 (rvc p139 p1021 (rvc p661 p761 (rvc p3 p1091 (rvc p109 p1039 (rvc p3 p1093 (rvc p17 p1087 (rvc p67 p1063 (rvc p13 p1091 (rvc p3 p1097 (rvc p17 p1091 (rvc p139 p1031 (rvc p17 p1093 (rvc p67 p1069 (rvc p109 p1049 (rvc p3 p1103 (rvc p17 p1097 (rvc p1291 p461 (rvc p401 p907 (rvc p139 p1039 (rvc p13 p1103 (rvc p3 p1109 (rvc p17 p1103 (rvc p43 p1091 (rvc p1553 p337 (rvc p131 p1049 (rvc p109 p1061 (rvc p131 p1051 (rvc p17 p1109 (rvc p3 p1117 (rvc p401 p919 (rvc p67 p1087 (rvc p337 p953 (rvc p107 p1069 (rvc p109 p1069 (rvc p3 p1123 (rvc p17 p1117 (rvc p67 p1093 (rvc p661 p797 (rvc p131 p1063 (rvc p401 p929 (rvc p3 p1129 (rvc p17 p1123 (rvc p139 p1063 (rvc p1549 p359 (rvc p131 p1069 (rvc p13 p1129 (rvc p67 p1103 (rvc p17 p1129 (rvc p139 p1069 (rvc p337 p971 (rvc p239 p1021 (rvc p109 p1087 (rvc p67 p1109 (rvc p29 p1129 (rvc p107 p1091 (rvc p109 p1091 (rvc p107 p1093 (rvc p109 p1093 (rvc p1291 p503 (rvc p173 p1063 (rvc p67 p1117 (rvc p109 p1097 (rvc p3 p1151 (rvc p401 p953 (rvc p3 p1153 (rvc p173 p1069 (rvc p67 p1123 (rvc p109 p1103 (rvc p131 p1093 (rvc p17 p1151 (rvc p139 p1091 (rvc p17 p1153 (rvc p67 p1129 (rvc p109 p1109 (rvc p3 p1163 (rvc p337 p997 (rvc p139 p1097 (rvc p401 p967 (rvc p131 p1103 (rvc p13 p1163 (rvc p239 p1051 (rvc p17 p1163 (rvc p3 p1171 (rvc p173 p1087 (rvc p131 p1109 (rvc p1549 p401 (rvc p107 p1123 (rvc p109 p1123 (rvc p139 p1109 (rvc p17 p1171 (rvc p239 p1061 (rvc p337 p1013 (rvc p3 p1181 (rvc p109 p1129 (rvc p67 p1151 (rvc p29 p1171 (rvc p67 p1153 (rvc p13 p1181 (rvc p3 p1187 (rvc p17 p1181 (rvc p499 p941 (rvc p401 p991 (rvc p139 p1123 (rvc p13 p1187 (rvc p3 p1193 (rvc p17 p1187 (rvc p67 p1163 (rvc p401 p997 (rvc p139 p1129 (rvc p13 p1193 (rvc p227 p1087 (rvc p17 p1193 (rvc p3 p1201 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl1607 (m : ℕ) (hl : 1607 ≤ m) (hh : m ≤ 2406) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-1607)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 1607+2*k := by simp [k]; omega
  have hk : k < ql1607.length := by simp [k,ql1607]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl1607 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql2407 : List ℕ := [1117,1171,1151,1087,1153,1187,1201,1091,881,1093,1013,1213,1129,1151,1163,1217,1019,1187,1213,1153,1217,1223,1217,1193,1213,1163,1223,1229,1223,1231,1033,1201,1181,1171,1229,1237,1231,1171,1187,1123,1237,1223,1237,1213,1193,1129,1049,1249,1051,1187,479,1201,1201,1223,1249,1193,1091,1259,1061,1229,1063,1231,1259,1201,1259,1019,1069,1237,1217,1153,1187,1031,457,1223,1223,1277,1193,1279,463,1249,1229,1283,1277,1217,1279,1223,1283,1289,1283,1291,1093,1229,1289,1231,1289,1297,1291,1231,971,1301,1249,1303,1297,1237,1301,1307,1301,1277,1303,1279,1259,1249,1307,1283,1117,1249,1151,1319,1153,1321,1123,1291,1319,607,1319,1327,1321,1297,1277,1213,1279,1301,1327,1303,1283,619,1171,1307,1327,1277,1289,1279,1291,1277,571,1283,1181,1231,1297,1319,1153,1321,1301,1291,1303,1289,541,1327,1307,1361,1163,719,1279,1301,1361,1367,1361,1301,1171,1307,1319,1373,1367,1307,1291,1259,1373,1327,1373,1381,1297,1319,1217,1321,1187,1319,1381,1321,1223,1327,1193,1361,1381,1327,1229,1279,1231,1399,1201,1283,977,829,1399,1373,1399,1289,983,1409,593,1163,1213,1381,1361,1297,1409,773,601,1301,1367,1303,1223,1423,607,1361,1373,1427,1229,1429,1423,1399,1427,1433,1427,1367,1429,1373,1433,1439,1433,1409,1429,1423,1439,1381,1439,1447,1249,1381,1283,1451,1399,1453,1447,1423,1451,739,1451,1459,1453,1429,1409,1399,1459,1433,1459,1399,1301,751,1303,1471,1459,1409,1307,1423,1423,1409,1471,1447,1427,1481,1429,1483,1399,1453,1433,1487,1481,1489,1483,1459,1439,1493,1487,1427,1489,1433,1493,1499,1493,1433,1303,1471,1451,1453,1499,1439,1423,1489,1181,1511,1459,1481,1429,1483,1511,1453,1511,1487,1321,1489,1193,1523,1471,1493,1327,1459,1523,811,1523,1531,1447,1481,1481,1471,1483,1289,1531,1471,1487,1423,1489,1543,1459,1481,1493,1483,1543,1549,1543,1487,1499,1553,1549,1523,1549,1493,1553,1559,1553,1493,1549,1531,1511,1447,1559,1567,1483,1451,797,1571,1373,1553,1567,1543,1523,1459,1571,1579,1381,1549,809,1583,1531,1553,1579,1523,1583,1471,1583,1559,1579,1553,1427,1531,1543,1597,1399,1567,1433,1601]
private theorem vl2407 : rvld 2 2407 ql2407 := by
  unfold ql2407
  exact rvc p173 p1117 (rvc p67 p1171 (rvc p109 p1151 (rvc p239 p1087 (rvc p109 p1153 (rvc p43 p1187 (rvc p17 p1201 (rvc p239 p1091 (rvc p661 p881 (rvc p239 p1093 (rvc p401 p1013 (rvc p3 p1213 (rvc p173 p1129 (rvc p131 p1151 (rvc p109 p1163 (rvc p3 p1217 (rvc p401 p1019 (rvc p67 p1187 (rvc p17 p1213 (rvc p139 p1153 (rvc p13 p1217 (rvc p3 p1223 (rvc p17 p1217 (rvc p67 p1193 (rvc p29 p1213 (rvc p131 p1163 (rvc p13 p1223 (rvc p3 p1229 (rvc p17 p1223 (rvc p3 p1231 (rvc p401 p1033 (rvc p67 p1201 (rvc p109 p1181 (rvc p131 p1171 (rvc p17 p1229 (rvc p3 p1237 (rvc p17 p1231 (rvc p139 p1171 (rvc p109 p1187 (rvc p239 p1123 (rvc p13 p1237 (rvc p43 p1223 (rvc p17 p1237 (rvc p67 p1213 (rvc p109 p1193 (rvc p239 p1129 (rvc p401 p1049 (rvc p3 p1249 (rvc p401 p1051 (rvc p131 p1187 (rvc p1549 p479 (rvc p107 p1201 (rvc p109 p1201 (rvc p67 p1223 (rvc p17 p1249 (rvc p131 p1193 (rvc p337 p1091 (rvc p3 p1259 (rvc p401 p1061 (rvc p67 p1229 (rvc p401 p1063 (rvc p67 p1231 (rvc p13 p1259 (rvc p131 p1201 (rvc p17 p1259 (rvc p499 p1019 (rvc p401 p1069 (rvc p67 p1237 (rvc p109 p1217 (rvc p239 p1153 (rvc p173 p1187 (rvc p487 p1031 (rvc p1637 p457 (rvc p107 p1223 (rvc p109 p1223 (rvc p3 p1277 (rvc p173 p1193 (rvc p3 p1279 (rvc p1637 p463 (rvc p67 p1249 (rvc p109 p1229 (rvc p3 p1283 (rvc p17 p1277 (rvc p139 p1217 (rvc p17 p1279 (rvc p131 p1223 (rvc p13 p1283 (rvc p3 p1289 (rvc p17 p1283 (rvc p3 p1291 (rvc p401 p1093 (rvc p131 p1229 (rvc p13 p1289 (rvc p131 p1231 (rvc p17 p1289 (rvc p3 p1297 (rvc p17 p1291 (rvc p139 p1231 (rvc p661 p971 (rvc p3 p1301 (rvc p109 p1249 (rvc p3 p1303 (rvc p17 p1297 (rvc p139 p1237 (rvc p13 p1301 (rvc p3 p1307 (rvc p17 p1301 (rvc p67 p1277 (rvc p17 p1303 (rvc p67 p1279 (rvc p109 p1259 (rvc p131 p1249 (rvc p17 p1307 (rvc p67 p1283 (rvc p401 p1117 (rvc p139 p1249 (rvc p337 p1151 (rvc p3 p1319 (rvc p337 p1153 (rvc p3 p1321 (rvc p401 p1123 (rvc p67 p1291 (rvc p13 p1319 (rvc p1439 p607 (rvc p17 p1319 (rvc p3 p1327 (rvc p17 p1321 (rvc p67 p1297 (rvc p109 p1277 (rvc p239 p1213 (rvc p109 p1279 (rvc p67 p1301 (rvc p17 p1327 (rvc p67 p1303 (rvc p109 p1283 (rvc p1439 p619 (rvc p337 p1171 (rvc p67 p1307 (rvc p29 p1327 (rvc p131 p1277 (rvc p109 p1289 (rvc p131 p1279 (rvc p109 p1291 (rvc p139 p1277 (rvc p1553 p571 (rvc p131 p1283 (rvc p337 p1181 (rvc p239 p1231 (rvc p109 p1297 (rvc p67 p1319 (rvc p401 p1153 (rvc p67 p1321 (rvc p109 p1301 (rvc p131 p1291 (rvc p109 p1303 (rvc p139 p1289 (rvc p1637 p541 (rvc p67 p1327 (rvc p109 p1307 (rvc p3 p1361 (rvc p401 p1163 (rvc p1291 p719 (rvc p173 p1279 (rvc p131 p1301 (rvc p13 p1361 (rvc p3 p1367 (rvc p17 p1361 (rvc p139 p1301 (rvc p401 p1171 (rvc p131 p1307 (rvc p109 p1319 (rvc p3 p1373 (rvc p17 p1367 (rvc p139 p1307 (rvc p173 p1291 (rvc p239 p1259 (rvc p13 p1373 (rvc p107 p1327 (rvc p17 p1373 (rvc p3 p1381 (rvc p173 p1297 (rvc p131 p1319 (rvc p337 p1217 (rvc p131 p1321 (rvc p401 p1187 (rvc p139 p1319 (rvc p17 p1381 (rvc p139 p1321 (rvc p337 p1223 (rvc p131 p1327 (rvc p401 p1193 (rvc p67 p1361 (rvc p29 p1381 (rvc p139 p1327 (rvc p337 p1229 (rvc p239 p1279 (rvc p337 p1231 (rvc p3 p1399 (rvc p401 p1201 (rvc p239 p1283 (rvc p853 p977 (rvc p1151 p829 (rvc p13 p1399 (rvc p67 p1373 (rvc p17 p1399 (rvc p239 p1289 (rvc p853 p983 (rvc p3 p1409 (rvc p1637 p593 (rvc p499 p1163 (rvc p401 p1213 (rvc p67 p1381 (rvc p109 p1361 (rvc p239 p1297 (rvc p17 p1409 (rvc p1291 p773 (rvc p1637 p601 (rvc p239 p1301 (rvc p109 p1367 (rvc p239 p1303 (rvc p401 p1223 (rvc p3 p1423 (rvc p1637 p607 (rvc p131 p1361 (rvc p109 p1373 (rvc p3 p1427 (rvc p401 p1229 (rvc p3 p1429 (rvc p17 p1423 (rvc p67 p1399 (rvc p13 p1427 (rvc p3 p1433 (rvc p17 p1427 (rvc p139 p1367 (rvc p17 p1429 (rvc p131 p1373 (rvc p13 p1433 (rvc p3 p1439 (rvc p17 p1433 (rvc p67 p1409 (rvc p29 p1429 (rvc p43 p1423 (rvc p13 p1439 (rvc p131 p1381 (rvc p17 p1439 (rvc p3 p1447 (rvc p401 p1249 (rvc p139 p1381 (rvc p337 p1283 (rvc p3 p1451 (rvc p109 p1399 (rvc p3 p1453 (rvc p17 p1447 (rvc p67 p1423 (rvc p13 p1451 (rvc p1439 p739 (rvc p17 p1451 (rvc p3 p1459 (rvc p17 p1453 (rvc p67 p1429 (rvc p109 p1409 (rvc p131 p1399 (rvc p13 p1459 (rvc p67 p1433 (rvc p17 p1459 (rvc p139 p1399 (rvc p337 p1301 (rvc p1439 p751 (rvc p337 p1303 (rvc p3 p1471 (rvc p29 p1459 (rvc p131 p1409 (rvc p337 p1307 (rvc p107 p1423 (rvc p109 p1423 (rvc p139 p1409 (rvc p17 p1471 (rvc p67 p1447 (rvc p109 p1427 (rvc p3 p1481 (rvc p109 p1429 (rvc p3 p1483 (rvc p173 p1399 (rvc p67 p1453 (rvc p109 p1433 (rvc p3 p1487 (rvc p17 p1481 (rvc p3 p1489 (rvc p17 p1483 (rvc p67 p1459 (rvc p109 p1439 (rvc p3 p1493 (rvc p17 p1487 (rvc p139 p1427 (rvc p17 p1489 (rvc p131 p1433 (rvc p13 p1493 (rvc p3 p1499 (rvc p17 p1493 (rvc p139 p1433 (rvc p401 p1303 (rvc p67 p1471 (rvc p109 p1451 (rvc p107 p1453 (rvc p17 p1499 (rvc p139 p1439 (rvc p173 p1423 (rvc p43 p1489 (rvc p661 p1181 (rvc p3 p1511 (rvc p109 p1459 (rvc p67 p1481 (rvc p173 p1429 (rvc p67 p1483 (rvc p13 p1511 (rvc p131 p1453 (rvc p17 p1511 (rvc p67 p1487 (rvc p401 p1321 (rvc p67 p1489 (rvc p661 p1193 (rvc p3 p1523 (rvc p109 p1471 (rvc p67 p1493 (rvc p401 p1327 (rvc p139 p1459 (rvc p13 p1523 (rvc p1439 p811 (rvc p17 p1523 (rvc p3 p1531 (rvc p173 p1447 (rvc p107 p1481 (rvc p109 p1481 (rvc p131 p1471 (rvc p109 p1483 (rvc p499 p1289 (rvc p17 p1531 (rvc p139 p1471 (rvc p109 p1487 (rvc p239 p1423 (rvc p109 p1489 (rvc p3 p1543 (rvc p173 p1459 (rvc p131 p1481 (rvc p109 p1493 (rvc p131 p1483 (rvc p13 p1543 (rvc p3 p1549 (rvc p17 p1543 (rvc p131 p1487 (rvc p109 p1499 (rvc p3 p1553 (rvc p13 p1549 (rvc p67 p1523 (rvc p17 p1549 (rvc p131 p1493 (rvc p13 p1553 (rvc p3 p1559 (rvc p17 p1553 (rvc p139 p1493 (rvc p29 p1549 (rvc p67 p1531 (rvc p109 p1511 (rvc p239 p1447 (rvc p17 p1559 (rvc p3 p1567 (rvc p173 p1483 (rvc p239 p1451 (rvc p1549 p797 (rvc p3 p1571 (rvc p401 p1373 (rvc p43 p1553 (rvc p17 p1567 (rvc p67 p1543 (rvc p109 p1523 (rvc p239 p1459 (rvc p17 p1571 (rvc p3 p1579 (rvc p401 p1381 (rvc p67 p1549 (rvc p1549 p809 (rvc p3 p1583 (rvc p109 p1531 (rvc p67 p1553 (rvc p17 p1579 (rvc p131 p1523 (rvc p13 p1583 (rvc p239 p1471 (rvc p17 p1583 (rvc p67 p1559 (rvc p29 p1579 (rvc p83 p1553 (rvc p337 p1427 (rvc p131 p1531 (rvc p109 p1543 (rvc p3 p1597 (rvc p401 p1399 (rvc p67 p1567 (rvc p337 p1433 (rvc p3 p1601 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl2407 (m : ℕ) (hl : 2407 ≤ m) (hh : m ≤ 3206) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-2407)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 2407+2*k := by simp [k]; omega
  have hk : k < ql2407.length := by simp [k,ql2407]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl2407 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql3207 : List ℕ := [1549,1571,1597,1487,1553,1607,1601,1609,1597,1579,1559,1613,1607,1583,1609,1553,1613,1619,1613,1621,1423,1559,1571,907,1619,1627,1621,1597,1301,1567,1579,1601,1627,1571,1583,1637,1439,1607,1627,1609,1637,1579,1637,1613,1447,1583,1481,1531,1597,1619,1453,1621,1601,937,1489,1657,1459,1627,1607,1597,1609,1663,1657,1601,1613,1667,1663,1669,1663,1607,1619,1609,1667,1607,1669,1613,1511,1627,1627,1613,1483,1619,911,1621,1487,1619,1489,1657,1637,1627,1493,1693,1609,1663,1367,1697,1499,1699,1693,1669,1697,1663,1697,1637,1699,1063,839,1709,1657,1607,1627,1693,1709,1597,1709,1697,1693,1601,1667,1721,1669,1723,907,1693,1721,1663,1721,1697,1723,1699,863,1733,1567,1667,1723,1669,1733,1621,1733,1741,1543,1723,971,1627,1693,1747,1741,1697,1697,1699,1699,1753,1747,1723,1427,1693,1559,1759,1753,1697,1709,1699,1759,1733,1759,1699,1601,1051,1571,1523,1759,1741,1721,1657,1723,1777,1579,1747,1613,1663,1583,1783,1777,1753,1733,1787,1783,1789,1783,1759,1787,1741,1787,1151,1789,1733,929,1747,1747,1801,1789,1783,1637,1741,1753,1787,1801,1777,1481,1811,1759,1571,1801,1783,1811,1753,1811,1787,1621,1789,1493,1823,1657,1181,1627,1759,1823,1777,1823,1831,1747,1801,1667,1783,1783,1193,1831,1721,1787,1777,1789,1811,1759,1777,977,1847,1031,1601,1033,1787,1847,1789,1847,1823,1657,1789,1433,1741,1693,1861,1663,1831,1811,1801,1667,1867,1861,1801,1097,1871,1867,1873,1867,1811,1823,1877,1871,1879,1873,1861,1877,1831,1877,1637,1879,1823,1721,1889,1723,1823,1693,1861,1889,1831,1889,1877,1699,1867,1847,1901,1889,1871,1087,1873,1901,1907,1901,1877,1093,1879,1907,1913,1907,1847,1831,1877,1913,1801,1913,1889,1723,1871,1871,1861,1873,1907,1153,1861,1877,1931,1879,1933,1117,1871,1931,1873,1931,1907,1933,1877,1889,1879,1777,1913,1747,1879,1619,1949,1783,1951,1753,1889,1901,1237,1949,1889,1951,1907,1907,79,1877,1931,1879,1933,1913,1249,1801,1901,1153,1907,1103,1973,1889,1907,1777,1913,1973,1979,1973,1949,1783,1951,1931,1867,1979,1987,1789,1871,1823,1873,1987,1993,1987,1931,1667,1997,1993,1999,1993,1933]
private theorem vl3207 : rvld 2 3207 ql3207 := by
  unfold ql3207
  exact rvc p109 p1549 (rvc p67 p1571 (rvc p17 p1597 (rvc p239 p1487 (rvc p109 p1553 (rvc p3 p1607 (rvc p17 p1601 (rvc p3 p1609 (rvc p29 p1597 (rvc p67 p1579 (rvc p109 p1559 (rvc p3 p1613 (rvc p17 p1607 (rvc p67 p1583 (rvc p17 p1609 (rvc p131 p1553 (rvc p13 p1613 (rvc p3 p1619 (rvc p17 p1613 (rvc p3 p1621 (rvc p401 p1423 (rvc p131 p1559 (rvc p109 p1571 (rvc p1439 p907 (rvc p17 p1619 (rvc p3 p1627 (rvc p17 p1621 (rvc p67 p1597 (rvc p661 p1301 (rvc p131 p1567 (rvc p109 p1579 (rvc p67 p1601 (rvc p17 p1627 (rvc p131 p1571 (rvc p109 p1583 (rvc p3 p1637 (rvc p401 p1439 (rvc p67 p1607 (rvc p29 p1627 (rvc p67 p1609 (rvc p13 p1637 (rvc p131 p1579 (rvc p17 p1637 (rvc p67 p1613 (rvc p401 p1447 (rvc p131 p1583 (rvc p337 p1481 (rvc p239 p1531 (rvc p109 p1597 (rvc p67 p1619 (rvc p401 p1453 (rvc p67 p1621 (rvc p109 p1601 (rvc p1439 p937 (rvc p337 p1489 (rvc p3 p1657 (rvc p401 p1459 (rvc p67 p1627 (rvc p109 p1607 (rvc p131 p1597 (rvc p109 p1609 (rvc p3 p1663 (rvc p17 p1657 (rvc p131 p1601 (rvc p109 p1613 (rvc p3 p1667 (rvc p13 p1663 (rvc p3 p1669 (rvc p17 p1663 (rvc p131 p1607 (rvc p109 p1619 (rvc p131 p1609 (rvc p17 p1667 (rvc p139 p1607 (rvc p17 p1669 (rvc p131 p1613 (rvc p337 p1511 (rvc p107 p1627 (rvc p109 p1627 (rvc p139 p1613 (rvc p401 p1483 (rvc p131 p1619 (rvc p1549 p911 (rvc p131 p1621 (rvc p401 p1487 (rvc p139 p1619 (rvc p401 p1489 (rvc p67 p1657 (rvc p109 p1637 (rvc p131 p1627 (rvc p401 p1493 (rvc p3 p1693 (rvc p173 p1609 (rvc p67 p1663 (rvc p661 p1367 (rvc p3 p1697 (rvc p401 p1499 (rvc p3 p1699 (rvc p17 p1693 (rvc p67 p1669 (rvc p13 p1697 (rvc p83 p1663 (rvc p17 p1697 (rvc p139 p1637 (rvc p17 p1699 (rvc p1291 p1063 (rvc p1741 p839 (rvc p3 p1709 (rvc p109 p1657 (rvc p211 p1607 (rvc p173 p1627 (rvc p43 p1693 (rvc p13 p1709 (rvc p239 p1597 (rvc p17 p1709 (rvc p43 p1697 (rvc p53 p1693 (rvc p239 p1601 (rvc p109 p1667 (rvc p3 p1721 (rvc p109 p1669 (rvc p3 p1723 (rvc p1637 p907 (rvc p67 p1693 (rvc p13 p1721 (rvc p131 p1663 (rvc p17 p1721 (rvc p67 p1697 (rvc p17 p1723 (rvc p67 p1699 (rvc p1741 p863 (rvc p3 p1733 (rvc p337 p1567 (rvc p139 p1667 (rvc p29 p1723 (rvc p139 p1669 (rvc p13 p1733 (rvc p239 p1621 (rvc p17 p1733 (rvc p3 p1741 (rvc p401 p1543 (rvc p43 p1723 (rvc p1549 p971 (rvc p239 p1627 (rvc p109 p1693 (rvc p3 p1747 (rvc p17 p1741 (rvc p107 p1697 (rvc p109 p1697 (rvc p107 p1699 (rvc p109 p1699 (rvc p3 p1753 (rvc p17 p1747 (rvc p67 p1723 (rvc p661 p1427 (rvc p131 p1693 (rvc p401 p1559 (rvc p3 p1759 (rvc p17 p1753 (rvc p131 p1697 (rvc p109 p1709 (rvc p131 p1699 (rvc p13 p1759 (rvc p67 p1733 (rvc p17 p1759 (rvc p139 p1699 (rvc p337 p1601 (rvc p1439 p1051 (rvc p401 p1571 (rvc p499 p1523 (rvc p29 p1759 (rvc p67 p1741 (rvc p109 p1721 (rvc p239 p1657 (rvc p109 p1723 (rvc p3 p1777 (rvc p401 p1579 (rvc p67 p1747 (rvc p337 p1613 (rvc p239 p1663 (rvc p401 p1583 (rvc p3 p1783 (rvc p17 p1777 (rvc p67 p1753 (rvc p109 p1733 (rvc p3 p1787 (rvc p13 p1783 (rvc p3 p1789 (rvc p17 p1783 (rvc p67 p1759 (rvc p13 p1787 (rvc p107 p1741 (rvc p17 p1787 (rvc p1291 p1151 (rvc p17 p1789 (rvc p131 p1733 (rvc p1741 p929 (rvc p107 p1747 (rvc p109 p1747 (rvc p3 p1801 (rvc p29 p1789 (rvc p43 p1783 (rvc p337 p1637 (rvc p131 p1741 (rvc p109 p1753 (rvc p43 p1787 (rvc p17 p1801 (rvc p67 p1777 (rvc p661 p1481 (rvc p3 p1811 (rvc p109 p1759 (rvc p487 p1571 (rvc p29 p1801 (rvc p67 p1783 (rvc p13 p1811 (rvc p131 p1753 (rvc p17 p1811 (rvc p67 p1787 (rvc p401 p1621 (rvc p67 p1789 (rvc p661 p1493 (rvc p3 p1823 (rvc p337 p1657 (rvc p1291 p1181 (rvc p401 p1627 (rvc p139 p1759 (rvc p13 p1823 (rvc p107 p1777 (rvc p17 p1823 (rvc p3 p1831 (rvc p173 p1747 (rvc p67 p1801 (rvc p337 p1667 (rvc p107 p1783 (rvc p109 p1783 (rvc p1291 p1193 (rvc p17 p1831 (rvc p239 p1721 (rvc p109 p1787 (rvc p131 p1777 (rvc p109 p1789 (rvc p67 p1811 (rvc p173 p1759 (rvc p139 p1777 (rvc p1741 p977 (rvc p3 p1847 (rvc p1637 p1031 (rvc p499 p1601 (rvc p1637 p1033 (rvc p131 p1787 (rvc p13 p1847 (rvc p131 p1789 (rvc p17 p1847 (rvc p67 p1823 (rvc p401 p1657 (rvc p139 p1789 (rvc p853 p1433 (rvc p239 p1741 (rvc p337 p1693 (rvc p3 p1861 (rvc p401 p1663 (rvc p67 p1831 (rvc p109 p1811 (rvc p131 p1801 (rvc p401 p1667 (rvc p3 p1867 (rvc p17 p1861 (rvc p139 p1801 (rvc p1549 p1097 (rvc p3 p1871 (rvc p13 p1867 (rvc p3 p1873 (rvc p17 p1867 (rvc p131 p1811 (rvc p109 p1823 (rvc p3 p1877 (rvc p17 p1871 (rvc p3 p1879 (rvc p17 p1873 (rvc p43 p1861 (rvc p13 p1877 (rvc p107 p1831 (rvc p17 p1877 (rvc p499 p1637 (rvc p17 p1879 (rvc p131 p1823 (rvc p337 p1721 (rvc p3 p1889 (rvc p337 p1723 (rvc p139 p1823 (rvc p401 p1693 (rvc p67 p1861 (rvc p13 p1889 (rvc p131 p1831 (rvc p17 p1889 (rvc p43 p1877 (rvc p401 p1699 (rvc p67 p1867 (rvc p109 p1847 (rvc p3 p1901 (rvc p29 p1889 (rvc p67 p1871 (rvc p1637 p1087 (rvc p67 p1873 (rvc p13 p1901 (rvc p3 p1907 (rvc p17 p1901 (rvc p67 p1877 (rvc p1637 p1093 (rvc p67 p1879 (rvc p13 p1907 (rvc p3 p1913 (rvc p17 p1907 (rvc p139 p1847 (rvc p173 p1831 (rvc p83 p1877 (rvc p13 p1913 (rvc p239 p1801 (rvc p17 p1913 (rvc p67 p1889 (rvc p401 p1723 (rvc p107 p1871 (rvc p109 p1871 (rvc p131 p1861 (rvc p109 p1873 (rvc p43 p1907 (rvc p1553 p1153 (rvc p139 p1861 (rvc p109 p1877 (rvc p3 p1931 (rvc p109 p1879 (rvc p3 p1933 (rvc p1637 p1117 (rvc p131 p1871 (rvc p13 p1931 (rvc p131 p1873 (rvc p17 p1931 (rvc p67 p1907 (rvc p17 p1933 (rvc p131 p1877 (rvc p109 p1889 (rvc p131 p1879 (rvc p337 p1777 (rvc p67 p1913 (rvc p401 p1747 (rvc p139 p1879 (rvc p661 p1619 (rvc p3 p1949 (rvc p337 p1783 (rvc p3 p1951 (rvc p401 p1753 (rvc p131 p1889 (rvc p109 p1901 (rvc p1439 p1237 (rvc p17 p1949 (rvc p139 p1889 (rvc p17 p1951 (rvc p107 p1907 (rvc p109 p1907 (rvc p3767 p79 (rvc p173 p1877 (rvc p67 p1931 (rvc p173 p1879 (rvc p67 p1933 (rvc p109 p1913 (rvc p1439 p1249 (rvc p337 p1801 (rvc p139 p1901 (rvc p1637 p1153 (rvc p131 p1907 (rvc p1741 p1103 (rvc p3 p1973 (rvc p173 p1889 (rvc p139 p1907 (rvc p401 p1777 (rvc p131 p1913 (rvc p13 p1973 (rvc p3 p1979 (rvc p17 p1973 (rvc p67 p1949 (rvc p401 p1783 (rvc p67 p1951 (rvc p109 p1931 (rvc p239 p1867 (rvc p17 p1979 (rvc p3 p1987 (rvc p401 p1789 (rvc p239 p1871 (rvc p337 p1823 (rvc p239 p1873 (rvc p13 p1987 (rvc p3 p1993 (rvc p17 p1987 (rvc p131 p1931 (rvc p661 p1667 (rvc p3 p1997 (rvc p13 p1993 (rvc p3 p1999 (rvc p17 p1993 (rvc p139 p1933 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl3207 (m : ℕ) (hl : 3207 ≤ m) (hh : m ≤ 4006) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-3207)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 3207+2*k := by simp [k]; omega
  have hk : k < ql3207.length := by simp [k,ql3207]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl3207 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql4007 : List ℕ := [1949,2003,1997,1973,1999,1889,2003,1291,2003,2011,1999,1949,1847,1951,2011,2017,2011,1987,1151,1303,1823,2003,2017,1993,1973,2027,1861,2029,1831,1999,1979,1993,2027,2003,2029,1973,1871,2039,1987,1973,2029,2011,2039,1993,2039,1979,1231,2017,1997,1987,1999,2053,1237,1987,2003,1993,2053,2027,2053,2029,1733,2063,2011,1997,1867,2003,2063,2069,2063,2039,1873,2053,2069,2011,2069,1433,1879,2011,2027,2081,2029,2083,1999,2053,2081,2087,2081,2089,2083,2027,2039,2029,2087,2063,2089,2029,1931,2099,1901,2069,2017,2039,2099,1987,2099,2039,1291,2089,3,2111,1913,2113,2029,2083,2063,2053,2111,2087,2113,2089,2069,2083,2039,1481,2113,2063,1259,2129,1931,2131,1933,2069,2081,2017,2129,2137,2131,2087,2087,2141,2089,2143,2137,2113,2141,2083,2141,2081,2143,2087,2099,2153,1987,2087,2143,2089,2153,277,2153,2161,2137,2131,2111,2113,2113,2099,2161,2137,2003,2053,1973,2141,2089,2143,1847,2113,1979,2179,73,2113,2129,2131,2131,2153,2179,2069,1319,2137,2137,1949,1993,2161,2141,2131,2143,2129,1999,2131,1871,2137,2003,2203,1429,2141,2153,2207,2203,2141,2203,2179,2207,2213,2207,1571,2017,2153,2213,2179,2213,2221,2137,2203,1451,2161,2027,2207,2221,2161,2063,2113,2179,2213,2221,2203,2069,2237,2039,2239,1423,2221,2237,2243,2237,2213,2239,2179,2243,2131,2243,2251,2053,2221,2087,2137,2203,2237,2251,2141,2207,2143,2063,2243,2179,2213,2213,2267,2069,2269,1453,2239,2267,2273,2267,2243,2269,2213,2273,2161,2273,2281,2083,2251,1511,2221,2087,2287,2281,2221,2237,2239,2239,2293,2287,2243,2243,2297,2099,2267,2293,2269,2297,2239,2297,2273,2221,2243,2141,2309,2111,2311,2113,2281,2309,2251,2309,2297,2311,2287,2267,2203,2269,2081,2239,2293,2273,1609,2129,2297,2131,2267,2003,2333,2281,2267,2137,2273,2333,2339,2333,2341,2143,2311,2339,2281,2339,2347,2341,2281,2297,2351,2153,2333,2347,2287,2351,2357,2351,2339,2161,2297,2309,2311,2357,2333,2281,2347,2039,2251,2203,2371,2287,2341,2207,2311,2371,2377,2371,2347,2213,2381,2377,2383,2377,2267,2333,2269,2381,2389,2383,2273,2339,2393,2341,2153,2389,2333,2393,2399,2393,2333]
private theorem vl4007 : rvld 2 4007 ql4007 := by
  unfold ql4007
  exact rvc p109 p1949 (rvc p3 p2003 (rvc p17 p1997 (rvc p67 p1973 (rvc p17 p1999 (rvc p239 p1889 (rvc p13 p2003 (rvc p1439 p1291 (rvc p17 p2003 (rvc p3 p2011 (rvc p29 p1999 (rvc p131 p1949 (rvc p337 p1847 (rvc p131 p1951 (rvc p13 p2011 (rvc p3 p2017 (rvc p17 p2011 (rvc p67 p1987 (rvc p1741 p1151 (rvc p1439 p1303 (rvc p401 p1823 (rvc p43 p2003 (rvc p17 p2017 (rvc p67 p1993 (rvc p109 p1973 (rvc p3 p2027 (rvc p337 p1861 (rvc p3 p2029 (rvc p401 p1831 (rvc p67 p1999 (rvc p109 p1979 (rvc p83 p1993 (rvc p17 p2027 (rvc p67 p2003 (rvc p17 p2029 (rvc p131 p1973 (rvc p337 p1871 (rvc p3 p2039 (rvc p109 p1987 (rvc p139 p1973 (rvc p29 p2029 (rvc p67 p2011 (rvc p13 p2039 (rvc p107 p1993 (rvc p17 p2039 (rvc p139 p1979 (rvc p1637 p1231 (rvc p67 p2017 (rvc p109 p1997 (rvc p131 p1987 (rvc p109 p1999 (rvc p3 p2053 (rvc p1637 p1237 (rvc p139 p1987 (rvc p109 p2003 (rvc p131 p1993 (rvc p13 p2053 (rvc p67 p2027 (rvc p17 p2053 (rvc p67 p2029 (rvc p661 p1733 (rvc p3 p2063 (rvc p109 p2011 (rvc p139 p1997 (rvc p401 p1867 (rvc p131 p2003 (rvc p13 p2063 (rvc p3 p2069 (rvc p17 p2063 (rvc p67 p2039 (rvc p401 p1873 (rvc p43 p2053 (rvc p13 p2069 (rvc p131 p2011 (rvc p17 p2069 (rvc p1291 p1433 (rvc p401 p1879 (rvc p139 p2011 (rvc p109 p2027 (rvc p3 p2081 (rvc p109 p2029 (rvc p3 p2083 (rvc p173 p1999 (rvc p67 p2053 (rvc p13 p2081 (rvc p3 p2087 (rvc p17 p2081 (rvc p3 p2089 (rvc p17 p2083 (rvc p131 p2027 (rvc p109 p2039 (rvc p131 p2029 (rvc p17 p2087 (rvc p67 p2063 (rvc p17 p2089 (rvc p139 p2029 (rvc p337 p1931 (rvc p3 p2099 (rvc p401 p1901 (rvc p67 p2069 (rvc p173 p2017 (rvc p131 p2039 (rvc p13 p2099 (rvc p239 p1987 (rvc p17 p2099 (rvc p139 p2039 (rvc p1637 p1291 (rvc p43 p2089 (rvc p4217 p3 (rvc p3 p2111 (rvc p401 p1913 (rvc p3 p2113 (rvc p173 p2029 (rvc p67 p2083 (rvc p109 p2063 (rvc p131 p2053 (rvc p17 p2111 (rvc p67 p2087 (rvc p17 p2113 (rvc p67 p2089 (rvc p109 p2069 (rvc p83 p2083 (rvc p173 p2039 (rvc p1291 p1481 (rvc p29 p2113 (rvc p131 p2063 (rvc p1741 p1259 (rvc p3 p2129 (rvc p401 p1931 (rvc p3 p2131 (rvc p401 p1933 (rvc p131 p2069 (rvc p109 p2081 (rvc p239 p2017 (rvc p17 p2129 (rvc p3 p2137 (rvc p17 p2131 (rvc p107 p2087 (rvc p109 p2087 (rvc p3 p2141 (rvc p109 p2089 (rvc p3 p2143 (rvc p17 p2137 (rvc p67 p2113 (rvc p13 p2141 (rvc p131 p2083 (rvc p17 p2141 (rvc p139 p2081 (rvc p17 p2143 (rvc p131 p2087 (rvc p109 p2099 (rvc p3 p2153 (rvc p337 p1987 (rvc p139 p2087 (rvc p29 p2143 (rvc p139 p2089 (rvc p13 p2153 (rvc p3767 p277 (rvc p17 p2153 (rvc p3 p2161 (rvc p53 p2137 (rvc p67 p2131 (rvc p109 p2111 (rvc p107 p2113 (rvc p109 p2113 (rvc p139 p2099 (rvc p17 p2161 (rvc p67 p2137 (rvc p337 p2003 (rvc p239 p2053 (rvc p401 p1973 (rvc p67 p2141 (rvc p173 p2089 (rvc p67 p2143 (rvc p661 p1847 (rvc p131 p2113 (rvc p401 p1979 (rvc p3 p2179 (rvc p4217 p73 (rvc p139 p2113 (rvc p109 p2129 (rvc p107 p2131 (rvc p109 p2131 (rvc p67 p2153 (rvc p17 p2179 (rvc p239 p2069 (rvc p1741 p1319 (rvc p107 p2137 (rvc p109 p2137 (rvc p487 p1949 (rvc p401 p1993 (rvc p67 p2161 (rvc p109 p2141 (rvc p131 p2131 (rvc p109 p2143 (rvc p139 p2129 (rvc p401 p1999 (rvc p139 p2131 (rvc p661 p1871 (rvc p131 p2137 (rvc p401 p2003 (rvc p3 p2203 (rvc p1553 p1429 (rvc p131 p2141 (rvc p109 p2153 (rvc p3 p2207 (rvc p13 p2203 (rvc p139 p2141 (rvc p17 p2203 (rvc p67 p2179 (rvc p13 p2207 (rvc p3 p2213 (rvc p17 p2207 (rvc p1291 p1571 (rvc p401 p2017 (rvc p131 p2153 (rvc p13 p2213 (rvc p83 p2179 (rvc p17 p2213 (rvc p3 p2221 (rvc p173 p2137 (rvc p43 p2203 (rvc p1549 p1451 (rvc p131 p2161 (rvc p401 p2027 (rvc p43 p2207 (rvc p17 p2221 (rvc p139 p2161 (rvc p337 p2063 (rvc p239 p2113 (rvc p109 p2179 (rvc p43 p2213 (rvc p29 p2221 (rvc p67 p2203 (rvc p337 p2069 (rvc p3 p2237 (rvc p401 p2039 (rvc p3 p2239 (rvc p1637 p1423 (rvc p43 p2221 (rvc p13 p2237 (rvc p3 p2243 (rvc p17 p2237 (rvc p67 p2213 (rvc p17 p2239 (rvc p139 p2179 (rvc p13 p2243 (rvc p239 p2131 (rvc p17 p2243 (rvc p3 p2251 (rvc p401 p2053 (rvc p67 p2221 (rvc p337 p2087 (rvc p239 p2137 (rvc p109 p2203 (rvc p43 p2237 (rvc p17 p2251 (rvc p239 p2141 (rvc p109 p2207 (rvc p239 p2143 (rvc p401 p2063 (rvc p43 p2243 (rvc p173 p2179 (rvc p107 p2213 (rvc p109 p2213 (rvc p3 p2267 (rvc p401 p2069 (rvc p3 p2269 (rvc p1637 p1453 (rvc p67 p2239 (rvc p13 p2267 (rvc p3 p2273 (rvc p17 p2267 (rvc p67 p2243 (rvc p17 p2269 (rvc p131 p2213 (rvc p13 p2273 (rvc p239 p2161 (rvc p17 p2273 (rvc p3 p2281 (rvc p401 p2083 (rvc p67 p2251 (rvc p1549 p1511 (rvc p131 p2221 (rvc p401 p2087 (rvc p3 p2287 (rvc p17 p2281 (rvc p139 p2221 (rvc p109 p2237 (rvc p107 p2239 (rvc p109 p2239 (rvc p3 p2293 (rvc p17 p2287 (rvc p107 p2243 (rvc p109 p2243 (rvc p3 p2297 (rvc p401 p2099 (rvc p67 p2267 (rvc p17 p2293 (rvc p67 p2269 (rvc p13 p2297 (rvc p131 p2239 (rvc p17 p2297 (rvc p67 p2273 (rvc p173 p2221 (rvc p131 p2243 (rvc p337 p2141 (rvc p3 p2309 (rvc p401 p2111 (rvc p3 p2311 (rvc p401 p2113 (rvc p67 p2281 (rvc p13 p2309 (rvc p131 p2251 (rvc p17 p2309 (rvc p43 p2297 (rvc p17 p2311 (rvc p67 p2287 (rvc p109 p2267 (rvc p239 p2203 (rvc p109 p2269 (rvc p487 p2081 (rvc p173 p2239 (rvc p67 p2293 (rvc p109 p2273 (rvc p1439 p1609 (rvc p401 p2129 (rvc p67 p2297 (rvc p401 p2131 (rvc p131 p2267 (rvc p661 p2003 (rvc p3 p2333 (rvc p109 p2281 (rvc p139 p2267 (rvc p401 p2137 (rvc p131 p2273 (rvc p13 p2333 (rvc p3 p2339 (rvc p17 p2333 (rvc p3 p2341 (rvc p401 p2143 (rvc p67 p2311 (rvc p13 p2339 (rvc p131 p2281 (rvc p17 p2339 (rvc p3 p2347 (rvc p17 p2341 (rvc p139 p2281 (rvc p109 p2297 (rvc p3 p2351 (rvc p401 p2153 (rvc p43 p2333 (rvc p17 p2347 (rvc p139 p2287 (rvc p13 p2351 (rvc p3 p2357 (rvc p17 p2351 (rvc p43 p2339 (rvc p401 p2161 (rvc p131 p2297 (rvc p109 p2309 (rvc p107 p2311 (rvc p17 p2357 (rvc p67 p2333 (rvc p173 p2281 (rvc p43 p2347 (rvc p661 p2039 (rvc p239 p2251 (rvc p337 p2203 (rvc p3 p2371 (rvc p173 p2287 (rvc p67 p2341 (rvc p337 p2207 (rvc p131 p2311 (rvc p13 p2371 (rvc p3 p2377 (rvc p17 p2371 (rvc p67 p2347 (rvc p337 p2213 (rvc p3 p2381 (rvc p13 p2377 (rvc p3 p2383 (rvc p17 p2377 (rvc p239 p2267 (rvc p109 p2333 (rvc p239 p2269 (rvc p17 p2381 (rvc p3 p2389 (rvc p17 p2383 (rvc p239 p2273 (rvc p109 p2339 (rvc p3 p2393 (rvc p109 p2341 (rvc p487 p2153 (rvc p17 p2389 (rvc p131 p2333 (rvc p13 p2393 (rvc p3 p2399 (rvc p17 p2393 (rvc p139 p2333 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl4007 (m : ℕ) (hl : 4007 ≤ m) (hh : m ≤ 4806) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-4007)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 4007+2*k := by simp [k]; omega
  have hk : k < ql4007.length := by simp [k,ql4007]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl4007 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql4807 : List ℕ := [2203,2371,2351,2341,2399,2339,2383,2377,2357,2411,2213,2381,1597,2383,2411,2417,2411,2351,2221,2389,2417,2423,2417,2393,2341,2309,2423,2311,2423,2399,2347,2381,2381,2371,2383,2437,2239,2371,2273,2441,2389,2411,2437,2381,2393,2447,2441,2417,2251,2383,2399,2389,2447,2423,2371,2393,2129,2459,2293,2393,2377,2399,2411,2347,2459,2467,2269,2437,2417,1753,2273,2473,2467,2411,2423,2477,2473,2447,2473,2417,2477,601,2477,2417,2287,2423,1619,2371,2437,2459,2293,2441,2441,2377,2297,2477,1723,2467,2447,2437,2417,2503,397,2473,2339,2389,2309,2477,2503,2447,2459,2473,2347,2447,2503,2399,2351,2467,2467,2521,2437,2459,2357,2473,2473,2459,2521,2411,2477,2531,2333,1889,2521,2503,2531,2473,2531,2539,2341,2477,2213,2543,2539,2477,2539,1973,2543,2549,2543,2551,2467,2521,2549,2437,2549,2557,2551,2441,2393,2521,2557,2531,2557,2447,2399,2503,2239,2549,2371,2539,2243,2521,2521,2543,2377,2459,2411,2579,2381,2549,2383,2551,2531,2521,2579,2339,2389,2557,2423,2591,2539,2593,1777,2531,2543,1879,2591,2531,2593,2549,2549,2539,2551,2357,2521,2543,2441,2609,2557,2579,2389,2549,2609,2551,2609,2617,1801,2551,1847,2621,2423,2591,2617,2593,2621,2053,2621,2609,2617,2579,2579,2633,2467,2393,2437,2617,2633,2521,2633,2609,2557,2579,2591,2593,2593,2647,1831,2617,1877,1933,2647,2621,2647,2591,1787,2657,2459,2659,2647,2593,2609,2663,2657,2633,2659,2549,2663,2551,2663,2671,2473,2609,2621,2557,2477,2677,2671,2647,2351,2617,2677,2683,2677,2621,2633,2687,2683,2689,2683,2659,2687,2693,2687,2663,2689,2633,2693,2699,2693,2633,2503,2671,2699,1987,2699,2707,1933,2677,2657,2711,2659,2713,2707,2683,2663,1999,2711,2719,2713,2689,2393,2659,2671,2693,2719,2663,2399,2729,2677,2731,2647,2713,2729,2671,2729,2633,2731,2707,2687,2741,2689,2711,2659,2713,2693,2683,2741,2749,2551,2719,2699,2753,2749,2687,2749,2693,2753,2707,2753,2729,2677,2731,2711,2647,2713,2767,2683,2749,2441,2707,2719,2741,2767,2711,2609,2777,2579,2711,2767,2749,2729,2719,2777,2753,2011,2719,2621,2789,2591,2791,2593,2729,2741,2731,2789,2797,2791,2767,2633,2801]
private theorem vl4807 : rvld 2 4807 ql4807 := by
  unfold ql4807
  exact rvc p401 p2203 (rvc p67 p2371 (rvc p109 p2351 (rvc p131 p2341 (rvc p17 p2399 (rvc p139 p2339 (rvc p53 p2383 (rvc p67 p2377 (rvc p109 p2357 (rvc p3 p2411 (rvc p401 p2213 (rvc p67 p2381 (rvc p1637 p1597 (rvc p67 p2383 (rvc p13 p2411 (rvc p3 p2417 (rvc p17 p2411 (rvc p139 p2351 (rvc p401 p2221 (rvc p67 p2389 (rvc p13 p2417 (rvc p3 p2423 (rvc p17 p2417 (rvc p67 p2393 (rvc p173 p2341 (rvc p239 p2309 (rvc p13 p2423 (rvc p239 p2311 (rvc p17 p2423 (rvc p67 p2399 (rvc p173 p2347 (rvc p107 p2381 (rvc p109 p2381 (rvc p131 p2371 (rvc p109 p2383 (rvc p3 p2437 (rvc p401 p2239 (rvc p139 p2371 (rvc p337 p2273 (rvc p3 p2441 (rvc p109 p2389 (rvc p67 p2411 (rvc p17 p2437 (rvc p131 p2381 (rvc p109 p2393 (rvc p3 p2447 (rvc p17 p2441 (rvc p67 p2417 (rvc p401 p2251 (rvc p139 p2383 (rvc p109 p2399 (rvc p131 p2389 (rvc p17 p2447 (rvc p67 p2423 (rvc p173 p2371 (rvc p131 p2393 (rvc p661 p2129 (rvc p3 p2459 (rvc p337 p2293 (rvc p139 p2393 (rvc p173 p2377 (rvc p131 p2399 (rvc p109 p2411 (rvc p239 p2347 (rvc p17 p2459 (rvc p3 p2467 (rvc p401 p2269 (rvc p67 p2437 (rvc p109 p2417 (rvc p1439 p1753 (rvc p401 p2273 (rvc p3 p2473 (rvc p17 p2467 (rvc p131 p2411 (rvc p109 p2423 (rvc p3 p2477 (rvc p13 p2473 (rvc p67 p2447 (rvc p17 p2473 (rvc p131 p2417 (rvc p13 p2477 (rvc p3767 p601 (rvc p17 p2477 (rvc p139 p2417 (rvc p401 p2287 (rvc p131 p2423 (rvc p1741 p1619 (rvc p239 p2371 (rvc p109 p2437 (rvc p67 p2459 (rvc p401 p2293 (rvc p107 p2441 (rvc p109 p2441 (rvc p239 p2377 (rvc p401 p2297 (rvc p43 p2477 (rvc p1553 p1723 (rvc p67 p2467 (rvc p109 p2447 (rvc p131 p2437 (rvc p173 p2417 (rvc p3 p2503 (rvc p4217 p397 (rvc p67 p2473 (rvc p337 p2339 (rvc p239 p2389 (rvc p401 p2309 (rvc p67 p2477 (rvc p17 p2503 (rvc p131 p2447 (rvc p109 p2459 (rvc p83 p2473 (rvc p337 p2347 (rvc p139 p2447 (rvc p29 p2503 (rvc p239 p2399 (rvc p337 p2351 (rvc p107 p2467 (rvc p109 p2467 (rvc p3 p2521 (rvc p173 p2437 (rvc p131 p2459 (rvc p337 p2357 (rvc p107 p2473 (rvc p109 p2473 (rvc p139 p2459 (rvc p17 p2521 (rvc p239 p2411 (rvc p109 p2477 (rvc p3 p2531 (rvc p401 p2333 (rvc p1291 p1889 (rvc p29 p2521 (rvc p67 p2503 (rvc p13 p2531 (rvc p131 p2473 (rvc p17 p2531 (rvc p3 p2539 (rvc p401 p2341 (rvc p131 p2477 (rvc p661 p2213 (rvc p3 p2543 (rvc p13 p2539 (rvc p139 p2477 (rvc p17 p2539 (rvc p1151 p1973 (rvc p13 p2543 (rvc p3 p2549 (rvc p17 p2543 (rvc p3 p2551 (rvc p173 p2467 (rvc p67 p2521 (rvc p13 p2549 (rvc p239 p2437 (rvc p17 p2549 (rvc p3 p2557 (rvc p17 p2551 (rvc p239 p2441 (rvc p337 p2393 (rvc p83 p2521 (rvc p13 p2557 (rvc p67 p2531 (rvc p17 p2557 (rvc p239 p2447 (rvc p337 p2399 (rvc p131 p2503 (rvc p661 p2239 (rvc p43 p2549 (rvc p401 p2371 (rvc p67 p2539 (rvc p661 p2243 (rvc p107 p2521 (rvc p109 p2521 (rvc p67 p2543 (rvc p401 p2377 (rvc p239 p2459 (rvc p337 p2411 (rvc p3 p2579 (rvc p401 p2381 (rvc p67 p2549 (rvc p401 p2383 (rvc p67 p2551 (rvc p109 p2531 (rvc p131 p2521 (rvc p17 p2579 (rvc p499 p2339 (rvc p401 p2389 (rvc p67 p2557 (rvc p337 p2423 (rvc p3 p2591 (rvc p109 p2539 (rvc p3 p2593 (rvc p1637 p1777 (rvc p131 p2531 (rvc p109 p2543 (rvc p1439 p1879 (rvc p17 p2591 (rvc p139 p2531 (rvc p17 p2593 (rvc p107 p2549 (rvc p109 p2549 (rvc p131 p2539 (rvc p109 p2551 (rvc p499 p2357 (rvc p173 p2521 (rvc p131 p2543 (rvc p337 p2441 (rvc p3 p2609 (rvc p109 p2557 (rvc p67 p2579 (rvc p449 p2389 (rvc p131 p2549 (rvc p13 p2609 (rvc p131 p2551 (rvc p17 p2609 (rvc p3 p2617 (rvc p1637 p1801 (rvc p139 p2551 (rvc p1549 p1847 (rvc p3 p2621 (rvc p401 p2423 (rvc p67 p2591 (rvc p17 p2617 (rvc p67 p2593 (rvc p13 p2621 (rvc p1151 p2053 (rvc p17 p2621 (rvc p43 p2609 (rvc p29 p2617 (rvc p107 p2579 (rvc p109 p2579 (rvc p3 p2633 (rvc p337 p2467 (rvc p487 p2393 (rvc p401 p2437 (rvc p43 p2617 (rvc p13 p2633 (rvc p239 p2521 (rvc p17 p2633 (rvc p67 p2609 (rvc p173 p2557 (rvc p131 p2579 (rvc p109 p2591 (rvc p107 p2593 (rvc p109 p2593 (rvc p3 p2647 (rvc p1637 p1831 (rvc p67 p2617 (rvc p1549 p1877 (rvc p1439 p1933 (rvc p13 p2647 (rvc p67 p2621 (rvc p17 p2647 (rvc p131 p2591 (rvc p1741 p1787 (rvc p3 p2657 (rvc p401 p2459 (rvc p3 p2659 (rvc p29 p2647 (rvc p139 p2593 (rvc p109 p2609 (rvc p3 p2663 (rvc p17 p2657 (rvc p67 p2633 (rvc p17 p2659 (rvc p239 p2549 (rvc p13 p2663 (rvc p239 p2551 (rvc p17 p2663 (rvc p3 p2671 (rvc p401 p2473 (rvc p131 p2609 (rvc p109 p2621 (rvc p239 p2557 (rvc p401 p2477 (rvc p3 p2677 (rvc p17 p2671 (rvc p67 p2647 (rvc p661 p2351 (rvc p131 p2617 (rvc p13 p2677 (rvc p3 p2683 (rvc p17 p2677 (rvc p131 p2621 (rvc p109 p2633 (rvc p3 p2687 (rvc p13 p2683 (rvc p3 p2689 (rvc p17 p2683 (rvc p67 p2659 (rvc p13 p2687 (rvc p3 p2693 (rvc p17 p2687 (rvc p67 p2663 (rvc p17 p2689 (rvc p131 p2633 (rvc p13 p2693 (rvc p3 p2699 (rvc p17 p2693 (rvc p139 p2633 (rvc p401 p2503 (rvc p67 p2671 (rvc p13 p2699 (rvc p1439 p1987 (rvc p17 p2699 (rvc p3 p2707 (rvc p1553 p1933 (rvc p67 p2677 (rvc p109 p2657 (rvc p3 p2711 (rvc p109 p2659 (rvc p3 p2713 (rvc p17 p2707 (rvc p67 p2683 (rvc p109 p2663 (rvc p1439 p1999 (rvc p17 p2711 (rvc p3 p2719 (rvc p17 p2713 (rvc p67 p2689 (rvc p661 p2393 (rvc p131 p2659 (rvc p109 p2671 (rvc p67 p2693 (rvc p17 p2719 (rvc p131 p2663 (rvc p661 p2399 (rvc p3 p2729 (rvc p109 p2677 (rvc p3 p2731 (rvc p173 p2647 (rvc p43 p2713 (rvc p13 p2729 (rvc p131 p2671 (rvc p17 p2729 (rvc p211 p2633 (rvc p17 p2731 (rvc p67 p2707 (rvc p109 p2687 (rvc p3 p2741 (rvc p109 p2689 (rvc p67 p2711 (rvc p173 p2659 (rvc p67 p2713 (rvc p109 p2693 (rvc p131 p2683 (rvc p17 p2741 (rvc p3 p2749 (rvc p401 p2551 (rvc p67 p2719 (rvc p109 p2699 (rvc p3 p2753 (rvc p13 p2749 (rvc p139 p2687 (rvc p17 p2749 (rvc p131 p2693 (rvc p13 p2753 (rvc p107 p2707 (rvc p17 p2753 (rvc p67 p2729 (rvc p173 p2677 (rvc p67 p2731 (rvc p109 p2711 (rvc p239 p2647 (rvc p109 p2713 (rvc p3 p2767 (rvc p173 p2683 (rvc p43 p2749 (rvc p661 p2441 (rvc p131 p2707 (rvc p109 p2719 (rvc p67 p2741 (rvc p17 p2767 (rvc p131 p2711 (rvc p337 p2609 (rvc p3 p2777 (rvc p401 p2579 (rvc p139 p2711 (rvc p29 p2767 (rvc p67 p2749 (rvc p109 p2729 (rvc p131 p2719 (rvc p17 p2777 (rvc p67 p2753 (rvc p1553 p2011 (rvc p139 p2719 (rvc p337 p2621 (rvc p3 p2789 (rvc p401 p2591 (rvc p3 p2791 (rvc p401 p2593 (rvc p131 p2729 (rvc p109 p2741 (rvc p131 p2731 (rvc p17 p2789 (rvc p3 p2797 (rvc p17 p2791 (rvc p67 p2767 (rvc p337 p2633 (rvc p3 p2801 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl4807 (m : ℕ) (hl : 4807 ≤ m) (hh : m ≤ 5606) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-4807)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 4807+2*k := by simp [k]; omega
  have hk : k < ql4807.length := by simp [k,ql4807]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl4807 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql5607 : List ℕ := [2749,2803,2797,2741,2753,2689,2801,2777,2803,2693,2039,2749,2647,2711,2617,2753,1949,2819,2767,2789,2797,2791,2819,2707,2819,2579,2011,2797,2777,2767,2633,2833,2749,2803,2063,2837,2833,2819,2833,2777,2789,2843,2837,2777,2647,2729,2843,2731,2843,2851,2767,2789,2801,2791,2803,2857,2851,2791,2693,2861,2663,2843,2857,2833,2861,2803,2861,2837,2671,2803,2819,2833,2707,2843,2677,2857,2711,2879,2713,2861,2683,2851,2879,2767,2879,2887,2689,2857,2837,2851,2693,2861,2887,2777,2843,2897,2699,2879,2887,2837,2897,2903,2897,2837,2707,2843,2903,2909,2903,2879,2713,2861,2861,2851,2909,2917,2719,2887,2753,2857,2917,2903,2917,2861,2153,2927,2729,2897,2731,2879,2879,1051,2927,2903,2851,2819,2609,2939,2887,2909,2857,2879,2939,1063,2939,2879,2749,2917,2897,2887,2753,2953,2137,2887,2903,2957,2953,2927,2953,2897,2909,2963,2957,2897,2767,2903,2963,2969,2963,2971,2887,2909,2969,2857,2969,2909,2971,2861,2927,2917,2897,2963,2971,2953,2819,2269,2789,2957,2791,2927,2939,2953,2909,2963,2797,2879,2129,2999,2801,3001,2803,2971,2999,2887,2999,2939,3001,2957,2957,3011,2927,2909,3001,2897,2963,2953,3011,3019,2203,2957,2969,3023,2971,2957,3019,2963,3023,2311,3023,2999,2833,3001,2957,2971,2837,3037,2953,2971,2711,3041,2843,3011,3037,2927,3041,2473,3041,3049,2851,3019,2999,3001,3001,3023,3049,2939,2729,2341,2861,3061,3049,2999,3011,3001,3061,3067,3061,3037,2903,2953,3019,3041,3067,3011,3023,3037,2879,3079,3067,3049,2753,3083,3079,2441,3079,3023,3083,3089,3083,3023,3079,3061,3041,2377,3089,383,2281,3067,3023,3037,3049,3083,3019,3041,2939,2389,2909,3109,2293,3079,2339,3049,3061,3083,3109,3049,2789,3119,3067,3121,3037,3083,3119,3061,3119,2879,3121,3061,2963,3067,3079,419,3049,3067,3083,3137,2939,3119,1033,3109,3089,3079,3137,2897,3061,3083,2819,3109,3137,3119,2953,3121,2381,3037,2957,3089,2341,3041,3083,3109,3109,3163,3079,2521,2999,3167,2969,3169,3163,3119,3119,3109,3167,2531,3169,3109,3011,3061,2851,3181,3169,3119,2411,3121,3181,3187,3181,3121,3137,3191,3187,2549,3187,3163,3191,3079,3191,3167,3001,3169]
private theorem vl5607 : rvld 2 5607 ql5607 := by
  unfold ql5607
  exact rvc p109 p2749 (rvc p3 p2803 (rvc p17 p2797 (rvc p131 p2741 (rvc p109 p2753 (rvc p239 p2689 (rvc p17 p2801 (rvc p67 p2777 (rvc p17 p2803 (rvc p239 p2693 (rvc p1549 p2039 (rvc p131 p2749 (rvc p337 p2647 (rvc p211 p2711 (rvc p401 p2617 (rvc p131 p2753 (rvc p1741 p1949 (rvc p3 p2819 (rvc p109 p2767 (rvc p67 p2789 (rvc p53 p2797 (rvc p67 p2791 (rvc p13 p2819 (rvc p239 p2707 (rvc p17 p2819 (rvc p499 p2579 (rvc p1637 p2011 (rvc p67 p2797 (rvc p109 p2777 (rvc p131 p2767 (rvc p401 p2633 (rvc p3 p2833 (rvc p173 p2749 (rvc p67 p2803 (rvc p1549 p2063 (rvc p3 p2837 (rvc p13 p2833 (rvc p43 p2819 (rvc p17 p2833 (rvc p131 p2777 (rvc p109 p2789 (rvc p3 p2843 (rvc p17 p2837 (rvc p139 p2777 (rvc p401 p2647 (rvc p239 p2729 (rvc p13 p2843 (rvc p239 p2731 (rvc p17 p2843 (rvc p3 p2851 (rvc p173 p2767 (rvc p131 p2789 (rvc p109 p2801 (rvc p131 p2791 (rvc p109 p2803 (rvc p3 p2857 (rvc p17 p2851 (rvc p139 p2791 (rvc p337 p2693 (rvc p3 p2861 (rvc p401 p2663 (rvc p43 p2843 (rvc p17 p2857 (rvc p67 p2833 (rvc p13 p2861 (rvc p131 p2803 (rvc p17 p2861 (rvc p67 p2837 (rvc p401 p2671 (rvc p139 p2803 (rvc p109 p2819 (rvc p83 p2833 (rvc p337 p2707 (rvc p67 p2843 (rvc p401 p2677 (rvc p43 p2857 (rvc p337 p2711 (rvc p3 p2879 (rvc p337 p2713 (rvc p43 p2861 (rvc p401 p2683 (rvc p67 p2851 (rvc p13 p2879 (rvc p239 p2767 (rvc p17 p2879 (rvc p3 p2887 (rvc p401 p2689 (rvc p67 p2857 (rvc p109 p2837 (rvc p83 p2851 (rvc p401 p2693 (rvc p67 p2861 (rvc p17 p2887 (rvc p239 p2777 (rvc p109 p2843 (rvc p3 p2897 (rvc p401 p2699 (rvc p43 p2879 (rvc p29 p2887 (rvc p131 p2837 (rvc p13 p2897 (rvc p3 p2903 (rvc p17 p2897 (rvc p139 p2837 (rvc p401 p2707 (rvc p131 p2843 (rvc p13 p2903 (rvc p3 p2909 (rvc p17 p2903 (rvc p67 p2879 (rvc p401 p2713 (rvc p107 p2861 (rvc p109 p2861 (rvc p131 p2851 (rvc p17 p2909 (rvc p3 p2917 (rvc p401 p2719 (rvc p67 p2887 (rvc p337 p2753 (rvc p131 p2857 (rvc p13 p2917 (rvc p43 p2903 (rvc p17 p2917 (rvc p131 p2861 (rvc p1549 p2153 (rvc p3 p2927 (rvc p401 p2729 (rvc p67 p2897 (rvc p401 p2731 (rvc p107 p2879 (rvc p109 p2879 (rvc p3767 p1051 (rvc p17 p2927 (rvc p67 p2903 (rvc p173 p2851 (rvc p239 p2819 (rvc p661 p2609 (rvc p3 p2939 (rvc p109 p2887 (rvc p67 p2909 (rvc p173 p2857 (rvc p131 p2879 (rvc p13 p2939 (rvc p3767 p1063 (rvc p17 p2939 (rvc p139 p2879 (rvc p401 p2749 (rvc p67 p2917 (rvc p109 p2897 (rvc p131 p2887 (rvc p401 p2753 (rvc p3 p2953 (rvc p1637 p2137 (rvc p139 p2887 (rvc p109 p2903 (rvc p3 p2957 (rvc p13 p2953 (rvc p67 p2927 (rvc p17 p2953 (rvc p131 p2897 (rvc p109 p2909 (rvc p3 p2963 (rvc p17 p2957 (rvc p139 p2897 (rvc p401 p2767 (rvc p131 p2903 (rvc p13 p2963 (rvc p3 p2969 (rvc p17 p2963 (rvc p3 p2971 (rvc p173 p2887 (rvc p131 p2909 (rvc p13 p2969 (rvc p239 p2857 (rvc p17 p2969 (rvc p139 p2909 (rvc p17 p2971 (rvc p239 p2861 (rvc p109 p2927 (rvc p131 p2917 (rvc p173 p2897 (rvc p43 p2963 (rvc p29 p2971 (rvc p67 p2953 (rvc p337 p2819 (rvc p1439 p2269 (rvc p401 p2789 (rvc p67 p2957 (rvc p401 p2791 (rvc p131 p2927 (rvc p109 p2939 (rvc p83 p2953 (rvc p173 p2909 (rvc p67 p2963 (rvc p401 p2797 (rvc p239 p2879 (rvc p1741 p2129 (rvc p3 p2999 (rvc p401 p2801 (rvc p3 p3001 (rvc p401 p2803 (rvc p67 p2971 (rvc p13 p2999 (rvc p239 p2887 (rvc p17 p2999 (rvc p139 p2939 (rvc p17 p3001 (rvc p107 p2957 (rvc p109 p2957 (rvc p3 p3011 (rvc p173 p2927 (rvc p211 p2909 (rvc p29 p3001 (rvc p239 p2897 (rvc p109 p2963 (rvc p131 p2953 (rvc p17 p3011 (rvc p3 p3019 (rvc p1637 p2203 (rvc p131 p2957 (rvc p109 p2969 (rvc p3 p3023 (rvc p109 p2971 (rvc p139 p2957 (rvc p17 p3019 (rvc p131 p2963 (rvc p13 p3023 (rvc p1439 p2311 (rvc p17 p3023 (rvc p67 p2999 (rvc p401 p2833 (rvc p67 p3001 (rvc p157 p2957 (rvc p131 p2971 (rvc p401 p2837 (rvc p3 p3037 (rvc p173 p2953 (rvc p139 p2971 (rvc p661 p2711 (rvc p3 p3041 (rvc p401 p2843 (rvc p67 p3011 (rvc p17 p3037 (rvc p239 p2927 (rvc p13 p3041 (rvc p1151 p2473 (rvc p17 p3041 (rvc p3 p3049 (rvc p401 p2851 (rvc p67 p3019 (rvc p109 p2999 (rvc p107 p3001 (rvc p109 p3001 (rvc p67 p3023 (rvc p17 p3049 (rvc p239 p2939 (rvc p661 p2729 (rvc p1439 p2341 (rvc p401 p2861 (rvc p3 p3061 (rvc p29 p3049 (rvc p131 p2999 (rvc p109 p3011 (rvc p131 p3001 (rvc p13 p3061 (rvc p3 p3067 (rvc p17 p3061 (rvc p67 p3037 (rvc p337 p2903 (rvc p239 p2953 (rvc p109 p3019 (rvc p67 p3041 (rvc p17 p3067 (rvc p131 p3011 (rvc p109 p3023 (rvc p83 p3037 (rvc p401 p2879 (rvc p3 p3079 (rvc p29 p3067 (rvc p67 p3049 (rvc p661 p2753 (rvc p3 p3083 (rvc p13 p3079 (rvc p1291 p2441 (rvc p17 p3079 (rvc p131 p3023 (rvc p13 p3083 (rvc p3 p3089 (rvc p17 p3083 (rvc p139 p3023 (rvc p29 p3079 (rvc p67 p3061 (rvc p109 p3041 (rvc p1439 p2377 (rvc p17 p3089 (rvc p5431 p383 (rvc p1637 p2281 (rvc p67 p3067 (rvc p157 p3023 (rvc p131 p3037 (rvc p109 p3049 (rvc p43 p3083 (rvc p173 p3019 (rvc p131 p3041 (rvc p337 p2939 (rvc p1439 p2389 (rvc p401 p2909 (rvc p3 p3109 (rvc p1637 p2293 (rvc p67 p3079 (rvc p1549 p2339 (rvc p131 p3049 (rvc p109 p3061 (rvc p67 p3083 (rvc p17 p3109 (rvc p139 p3049 (rvc p661 p2789 (rvc p3 p3119 (rvc p109 p3067 (rvc p3 p3121 (rvc p173 p3037 (rvc p83 p3083 (rvc p13 p3119 (rvc p131 p3061 (rvc p17 p3119 (rvc p499 p2879 (rvc p17 p3121 (rvc p139 p3061 (rvc p337 p2963 (rvc p131 p3067 (rvc p109 p3079 (rvc p5431 p419 (rvc p173 p3049 (rvc p139 p3067 (rvc p109 p3083 (rvc p3 p3137 (rvc p401 p2939 (rvc p43 p3119 (rvc p4217 p1033 (rvc p67 p3109 (rvc p109 p3089 (rvc p131 p3079 (rvc p17 p3137 (rvc p499 p2897 (rvc p173 p3061 (rvc p131 p3083 (rvc p661 p2819 (rvc p83 p3109 (rvc p29 p3137 (rvc p67 p3119 (rvc p401 p2953 (rvc p67 p3121 (rvc p1549 p2381 (rvc p239 p3037 (rvc p401 p2957 (rvc p139 p3089 (rvc p1637 p2341 (rvc p239 p3041 (rvc p157 p3083 (rvc p107 p3109 (rvc p109 p3109 (rvc p3 p3163 (rvc p173 p3079 (rvc p1291 p2521 (rvc p337 p2999 (rvc p3 p3167 (rvc p401 p2969 (rvc p3 p3169 (rvc p17 p3163 (rvc p107 p3119 (rvc p109 p3119 (rvc p131 p3109 (rvc p17 p3167 (rvc p1291 p2531 (rvc p17 p3169 (rvc p139 p3109 (rvc p337 p3011 (rvc p239 p3061 (rvc p661 p2851 (rvc p3 p3181 (rvc p29 p3169 (rvc p131 p3119 (rvc p1549 p2411 (rvc p131 p3121 (rvc p13 p3181 (rvc p3 p3187 (rvc p17 p3181 (rvc p139 p3121 (rvc p109 p3137 (rvc p3 p3191 (rvc p13 p3187 (rvc p1291 p2549 (rvc p17 p3187 (rvc p67 p3163 (rvc p13 p3191 (rvc p239 p3079 (rvc p17 p3191 (rvc p67 p3167 (rvc p401 p3001 (rvc p67 p3169 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl5607 (m : ℕ) (hl : 5607 ≤ m) (hh : m ≤ 6406) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-5607)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 5607+2*k := by simp [k]; omega
  have hk : k < ql5607.length := by simp [k,ql5607]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl5607 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql6407 : List ℕ := [2333,3203,3037,3137,3121,3089,3203,3209,3203,3191,2437,3181,3209,3163,3209,3217,3019,3187,3167,3221,3169,3191,3217,3121,3221,3163,3221,3229,3217,3167,2903,3169,3181,3203,3229,3169,2909,3121,3187,3209,3229,3191,3191,3181,3079,2999,3049,3217,3083,3251,3167,3253,3169,3191,3203,3257,3251,3259,3253,3229,3209,1381,3257,2621,3259,3203,2939,3217,3217,3271,3187,3209,3221,2557,3271,3209,3271,3259,2411,3217,3229,3251,3271,3253,3119,3169,3089,3257,2473,3259,2963,3229,3209,3191,2521,3229,2969,3299,2971,3301,3217,3271,3251,3187,3299,3307,3301,3191,3257,3259,3259,3313,3307,3251,2543,3253,3119,3319,3313,3257,2549,3323,3271,3257,3319,3259,3323,3329,3323,3331,3319,3301,3329,3271,3329,2693,3331,3307,3011,3301,3257,3343,3259,3313,2477,3347,3343,3329,3343,3319,3299,3301,3347,3323,3271,2713,3191,3359,3307,3361,3163,3331,3359,3301,3359,3299,3361,3301,3203,3371,3319,3373,3361,3343,3323,3313,3371,3347,3373,3313,3329,3319,3331,2741,3187,3323,3221,3389,3191,3391,3307,3361,3389,3331,3389,3329,3391,3331,3347,2683,3203,3371,3319,3373,2633,3407,3209,3389,2593,3347,3359,3413,3407,3347,3217,3299,3413,3301,3413,3389,2647,3391,3371,3361,3373,3359,3229,3361,2657,3313,3347,3433,2617,3371,2663,3373,3433,3407,3433,3373,3389,3391,3391,3413,3361,3329,3119,3449,3251,3203,3253,3389,3449,3391,3449,3457,3259,3391,3407,3461,3457,3463,3457,3433,3413,3467,3461,3469,3463,3407,3467,3433,3467,3407,3469,3413,2609,3361,3313,3449,3469,3463,2711,3433,3433,3467,2671,3457,3323,3491,3407,3461,2677,3463,3491,3433,3491,3499,3301,3469,3449,3463,3499,2861,3499,3389,3083,3391,3457,3511,3313,3449,3461,3463,3463,3517,3511,3467,3467,3457,3469,3491,3517,3461,3359,3527,3329,3529,3331,3499,3527,3533,3527,3467,3529,3469,3533,3539,3533,3541,3343,3511,3491,1663,3539,3547,3541,3517,3221,3433,3499,3533,3547,3491,3389,3557,3359,3559,3361,3529,3557,3499,3557,3533,3559,3499,2699,3517,3517,3571,3373,3541,3407,3511,3571,3557,3571,3547,3527,3581,3529,3583,3499,3517,3533,3469,3581,3557,3583,3559,3539,3593,3541,3527,3511,3533,3593,3547,3593,3533]
private theorem vl6407 : rvld 2 6407 ql6407 := by
  unfold ql6407
  exact rvc p1741 p2333 (rvc p3 p3203 (rvc p337 p3037 (rvc p139 p3137 (rvc p173 p3121 (rvc p239 p3089 (rvc p13 p3203 (rvc p3 p3209 (rvc p17 p3203 (rvc p43 p3191 (rvc p1553 p2437 (rvc p67 p3181 (rvc p13 p3209 (rvc p107 p3163 (rvc p17 p3209 (rvc p3 p3217 (rvc p401 p3019 (rvc p67 p3187 (rvc p109 p3167 (rvc p3 p3221 (rvc p109 p3169 (rvc p67 p3191 (rvc p17 p3217 (rvc p211 p3121 (rvc p13 p3221 (rvc p131 p3163 (rvc p17 p3221 (rvc p3 p3229 (rvc p29 p3217 (rvc p131 p3167 (rvc p661 p2903 (rvc p131 p3169 (rvc p109 p3181 (rvc p67 p3203 (rvc p17 p3229 (rvc p139 p3169 (rvc p661 p2909 (rvc p239 p3121 (rvc p109 p3187 (rvc p67 p3209 (rvc p29 p3229 (rvc p107 p3191 (rvc p109 p3191 (rvc p131 p3181 (rvc p337 p3079 (rvc p499 p2999 (rvc p401 p3049 (rvc p67 p3217 (rvc p337 p3083 (rvc p3 p3251 (rvc p173 p3167 (rvc p3 p3253 (rvc p173 p3169 (rvc p131 p3191 (rvc p109 p3203 (rvc p3 p3257 (rvc p17 p3251 (rvc p3 p3259 (rvc p17 p3253 (rvc p67 p3229 (rvc p109 p3209 (rvc p3767 p1381 (rvc p17 p3257 (rvc p1291 p2621 (rvc p17 p3259 (rvc p131 p3203 (rvc p661 p2939 (rvc p107 p3217 (rvc p109 p3217 (rvc p3 p3271 (rvc p173 p3187 (rvc p131 p3209 (rvc p109 p3221 (rvc p1439 p2557 (rvc p13 p3271 (rvc p139 p3209 (rvc p17 p3271 (rvc p43 p3259 (rvc p1741 p2411 (rvc p131 p3217 (rvc p109 p3229 (rvc p67 p3251 (rvc p29 p3271 (rvc p67 p3253 (rvc p337 p3119 (rvc p239 p3169 (rvc p401 p3089 (rvc p67 p3257 (rvc p1637 p2473 (rvc p67 p3259 (rvc p661 p2963 (rvc p131 p3229 (rvc p173 p3209 (rvc p211 p3191 (rvc p1553 p2521 (rvc p139 p3229 (rvc p661 p2969 (rvc p3 p3299 (rvc p661 p2971 (rvc p3 p3301 (rvc p173 p3217 (rvc p67 p3271 (rvc p109 p3251 (rvc p239 p3187 (rvc p17 p3299 (rvc p3 p3307 (rvc p17 p3301 (rvc p239 p3191 (rvc p109 p3257 (rvc p107 p3259 (rvc p109 p3259 (rvc p3 p3313 (rvc p17 p3307 (rvc p131 p3251 (rvc p1549 p2543 (rvc p131 p3253 (rvc p401 p3119 (rvc p3 p3319 (rvc p17 p3313 (rvc p131 p3257 (rvc p1549 p2549 (rvc p3 p3323 (rvc p109 p3271 (rvc p139 p3257 (rvc p17 p3319 (rvc p139 p3259 (rvc p13 p3323 (rvc p3 p3329 (rvc p17 p3323 (rvc p3 p3331 (rvc p29 p3319 (rvc p67 p3301 (rvc p13 p3329 (rvc p131 p3271 (rvc p17 p3329 (rvc p1291 p2693 (rvc p17 p3331 (rvc p67 p3307 (rvc p661 p3011 (rvc p83 p3301 (rvc p173 p3257 (rvc p3 p3343 (rvc p173 p3259 (rvc p67 p3313 (rvc p1741 p2477 (rvc p3 p3347 (rvc p13 p3343 (rvc p43 p3329 (rvc p17 p3343 (rvc p67 p3319 (rvc p109 p3299 (rvc p107 p3301 (rvc p17 p3347 (rvc p67 p3323 (rvc p173 p3271 (rvc p1291 p2713 (rvc p337 p3191 (rvc p3 p3359 (rvc p109 p3307 (rvc p3 p3361 (rvc p401 p3163 (rvc p67 p3331 (rvc p13 p3359 (rvc p131 p3301 (rvc p17 p3359 (rvc p139 p3299 (rvc p17 p3361 (rvc p139 p3301 (rvc p337 p3203 (rvc p3 p3371 (rvc p109 p3319 (rvc p3 p3373 (rvc p29 p3361 (rvc p67 p3343 (rvc p109 p3323 (rvc p131 p3313 (rvc p17 p3371 (rvc p67 p3347 (rvc p17 p3373 (rvc p139 p3313 (rvc p109 p3329 (rvc p131 p3319 (rvc p109 p3331 (rvc p1291 p2741 (rvc p401 p3187 (rvc p131 p3323 (rvc p337 p3221 (rvc p3 p3389 (rvc p401 p3191 (rvc p3 p3391 (rvc p173 p3307 (rvc p67 p3361 (rvc p13 p3389 (rvc p131 p3331 (rvc p17 p3389 (rvc p139 p3329 (rvc p17 p3391 (rvc p139 p3331 (rvc p109 p3347 (rvc p1439 p2683 (rvc p401 p3203 (rvc p67 p3371 (rvc p173 p3319 (rvc p67 p3373 (rvc p1549 p2633 (rvc p3 p3407 (rvc p401 p3209 (rvc p43 p3389 (rvc p1637 p2593 (rvc p131 p3347 (rvc p109 p3359 (rvc p3 p3413 (rvc p17 p3407 (rvc p139 p3347 (rvc p401 p3217 (rvc p239 p3299 (rvc p13 p3413 (rvc p239 p3301 (rvc p17 p3413 (rvc p67 p3389 (rvc p1553 p2647 (rvc p67 p3391 (rvc p109 p3371 (rvc p131 p3361 (rvc p109 p3373 (rvc p139 p3359 (rvc p401 p3229 (rvc p139 p3361 (rvc p1549 p2657 (rvc p239 p3313 (rvc p173 p3347 (rvc p3 p3433 (rvc p1637 p2617 (rvc p131 p3371 (rvc p1549 p2663 (rvc p131 p3373 (rvc p13 p3433 (rvc p67 p3407 (rvc p17 p3433 (rvc p139 p3373 (rvc p109 p3389 (rvc p107 p3391 (rvc p109 p3391 (rvc p67 p3413 (rvc p173 p3361 (rvc p239 p3329 (rvc p661 p3119 (rvc p3 p3449 (rvc p401 p3251 (rvc p499 p3203 (rvc p401 p3253 (rvc p131 p3389 (rvc p13 p3449 (rvc p131 p3391 (rvc p17 p3449 (rvc p3 p3457 (rvc p401 p3259 (rvc p139 p3391 (rvc p109 p3407 (rvc p3 p3461 (rvc p13 p3457 (rvc p3 p3463 (rvc p17 p3457 (rvc p67 p3433 (rvc p109 p3413 (rvc p3 p3467 (rvc p17 p3461 (rvc p3 p3469 (rvc p17 p3463 (rvc p131 p3407 (rvc p13 p3467 (rvc p83 p3433 (rvc p17 p3467 (rvc p139 p3407 (rvc p17 p3469 (rvc p131 p3413 (rvc p1741 p2609 (rvc p239 p3361 (rvc p337 p3313 (rvc p67 p3449 (rvc p29 p3469 (rvc p43 p3463 (rvc p1549 p2711 (rvc p107 p3433 (rvc p109 p3433 (rvc p43 p3467 (rvc p1637 p2671 (rvc p67 p3457 (rvc p337 p3323 (rvc p3 p3491 (rvc p173 p3407 (rvc p67 p3461 (rvc p1637 p2677 (rvc p67 p3463 (rvc p13 p3491 (rvc p131 p3433 (rvc p17 p3491 (rvc p3 p3499 (rvc p401 p3301 (rvc p67 p3469 (rvc p109 p3449 (rvc p83 p3463 (rvc p13 p3499 (rvc p1291 p2861 (rvc p17 p3499 (rvc p239 p3389 (rvc p853 p3083 (rvc p239 p3391 (rvc p109 p3457 (rvc p3 p3511 (rvc p401 p3313 (rvc p131 p3449 (rvc p109 p3461 (rvc p107 p3463 (rvc p109 p3463 (rvc p3 p3517 (rvc p17 p3511 (rvc p107 p3467 (rvc p109 p3467 (rvc p131 p3457 (rvc p109 p3469 (rvc p67 p3491 (rvc p17 p3517 (rvc p131 p3461 (rvc p337 p3359 (rvc p3 p3527 (rvc p401 p3329 (rvc p3 p3529 (rvc p401 p3331 (rvc p67 p3499 (rvc p13 p3527 (rvc p3 p3533 (rvc p17 p3527 (rvc p139 p3467 (rvc p17 p3529 (rvc p139 p3469 (rvc p13 p3533 (rvc p3 p3539 (rvc p17 p3533 (rvc p3 p3541 (rvc p401 p3343 (rvc p67 p3511 (rvc p109 p3491 (rvc p3767 p1663 (rvc p17 p3539 (rvc p3 p3547 (rvc p17 p3541 (rvc p67 p3517 (rvc p661 p3221 (rvc p239 p3433 (rvc p109 p3499 (rvc p43 p3533 (rvc p17 p3547 (rvc p131 p3491 (rvc p337 p3389 (rvc p3 p3557 (rvc p401 p3359 (rvc p3 p3559 (rvc p401 p3361 (rvc p67 p3529 (rvc p13 p3557 (rvc p131 p3499 (rvc p17 p3557 (rvc p67 p3533 (rvc p17 p3559 (rvc p139 p3499 (rvc p1741 p2699 (rvc p107 p3517 (rvc p109 p3517 (rvc p3 p3571 (rvc p401 p3373 (rvc p67 p3541 (rvc p337 p3407 (rvc p131 p3511 (rvc p13 p3571 (rvc p43 p3557 (rvc p17 p3571 (rvc p67 p3547 (rvc p109 p3527 (rvc p3 p3581 (rvc p109 p3529 (rvc p3 p3583 (rvc p173 p3499 (rvc p139 p3517 (rvc p109 p3533 (rvc p239 p3469 (rvc p17 p3581 (rvc p67 p3557 (rvc p17 p3583 (rvc p67 p3559 (rvc p109 p3539 (rvc p3 p3593 (rvc p109 p3541 (rvc p139 p3527 (rvc p173 p3511 (rvc p131 p3533 (rvc p13 p3593 (rvc p107 p3547 (rvc p17 p3593 (rvc p139 p3533 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl6407 (m : ℕ) (hl : 6407 ≤ m) (hh : m ≤ 7206) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-6407)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 6407+2*k := by simp [k]; omega
  have hk : k < ql6407.length := by simp [k,ql6407]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl6407 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql7207 : List ℕ := [3517,3571,3527,3541,3407,3607,2791,3541,3557,3547,3559,3613,3607,3583,3449,3617,3613,3371,3613,3557,3617,3623,3617,3593,3541,3559,3623,3511,3623,3631,3433,3581,3581,3571,3583,3637,3631,3607,3623,1759,3637,3643,3637,3613,3593,3583,3449,3617,3643,3583,3323,3613,2837,3623,3457,3593,3491,3659,3607,3593,3463,3631,3659,3547,3659,3023,3469,3637,3617,3671,3343,3673,2857,3643,3623,3677,3671,3659,3673,3617,3677,3631,3677,3617,3673,3623,3359,3571,3637,3691,3607,3673,3527,3631,3643,3697,3691,3631,3533,3701,3697,3671,3697,3673,3701,3643,3701,3709,3511,3643,3659,3673,3709,3467,3709,3697,3389,3719,3391,3701,3637,3691,3671,3607,3719,3727,3529,3697,3677,3613,3533,3733,3727,3671,3407,3673,3539,3739,3733,3709,3413,3691,3691,3677,3739,3727,3581,3631,3697,3719,3739,3701,3701,3691,3557,2819,3559,3727,3593,3761,3709,3119,1657,3733,3761,3767,3761,3769,3571,3739,3719,3709,3767,3527,3769,3709,3449,3779,3727,3761,3583,3719,3779,3733,3779,3719,2971,3671,3623,3727,3739,3793,3709,3727,3467,3797,3793,3767,3793,3769,3797,3803,3797,3557,3607,3739,3803,3691,3803,3779,3613,3761,3761,3697,3617,3797,3733,3701,3767,3821,3769,3823,3739,3793,3821,3709,3821,3797,3823,3767,3779,3833,3821,3803,3637,3769,3833,3121,3833,3821,3643,3779,3677,3727,3793,3847,1741,3797,3797,3851,3847,3853,3847,3823,3803,3793,3851,3617,3853,3797,3533,3863,3697,3833,3853,3803,3863,1987,3863,3803,3673,3821,3821,3823,3823,3877,3793,3847,3011,3881,3877,3851,3877,3853,3833,3823,3881,3889,3691,3823,3119,3853,3889,3863,3889,3833,3821,3847,3847,3833,3889,3851,3851,3853,3853,3907,3709,3877,3581,3911,3907,3881,3907,3851,3863,3917,3911,3919,3907,3889,3917,3923,3917,3677,3919,3863,3923,3929,3923,3931,3733,3881,3881,3217,3929,3917,3931,3907,3167,3877,3889,3943,3931,3881,3779,3947,3943,3917,3943,3919,3947,3889,3947,3923,3943,3889,3089,3907,3907,3929,3877,3931,3911,3847,3767,3967,3769,3851,3917,3907,3919,3329,3967,3943,3923,3259,3779,3947,3967,3917,3929,3919,3931,3917,3169,3923,3821,3989,3823,3923,3793,3929,3989,3931,3989,3929,3181,3967,3947,4001]
private theorem vl7207 : rvld 2 7207 ql7207 := by
  unfold ql7207
  exact rvc p173 p3517 (rvc p67 p3571 (rvc p157 p3527 (rvc p131 p3541 (rvc p401 p3407 (rvc p3 p3607 (rvc p1637 p2791 (rvc p139 p3541 (rvc p109 p3557 (rvc p131 p3547 (rvc p109 p3559 (rvc p3 p3613 (rvc p17 p3607 (rvc p67 p3583 (rvc p337 p3449 (rvc p3 p3617 (rvc p13 p3613 (rvc p499 p3371 (rvc p17 p3613 (rvc p131 p3557 (rvc p13 p3617 (rvc p3 p3623 (rvc p17 p3617 (rvc p67 p3593 (rvc p173 p3541 (rvc p139 p3559 (rvc p13 p3623 (rvc p239 p3511 (rvc p17 p3623 (rvc p3 p3631 (rvc p401 p3433 (rvc p107 p3581 (rvc p109 p3581 (rvc p131 p3571 (rvc p109 p3583 (rvc p3 p3637 (rvc p17 p3631 (rvc p67 p3607 (rvc p37 p3623 (rvc p3767 p1759 (rvc p13 p3637 (rvc p3 p3643 (rvc p17 p3637 (rvc p67 p3613 (rvc p109 p3593 (rvc p131 p3583 (rvc p401 p3449 (rvc p67 p3617 (rvc p17 p3643 (rvc p139 p3583 (rvc p661 p3323 (rvc p83 p3613 (rvc p1637 p2837 (rvc p67 p3623 (rvc p401 p3457 (rvc p131 p3593 (rvc p337 p3491 (rvc p3 p3659 (rvc p109 p3607 (rvc p139 p3593 (rvc p401 p3463 (rvc p67 p3631 (rvc p13 p3659 (rvc p239 p3547 (rvc p17 p3659 (rvc p1291 p3023 (rvc p401 p3469 (rvc p67 p3637 (rvc p109 p3617 (rvc p3 p3671 (rvc p661 p3343 (rvc p3 p3673 (rvc p1637 p2857 (rvc p67 p3643 (rvc p109 p3623 (rvc p3 p3677 (rvc p17 p3671 (rvc p43 p3659 (rvc p17 p3673 (rvc p131 p3617 (rvc p13 p3677 (rvc p107 p3631 (rvc p17 p3677 (rvc p139 p3617 (rvc p29 p3673 (rvc p131 p3623 (rvc p661 p3359 (rvc p239 p3571 (rvc p109 p3637 (rvc p3 p3691 (rvc p173 p3607 (rvc p43 p3673 (rvc p337 p3527 (rvc p131 p3631 (rvc p109 p3643 (rvc p3 p3697 (rvc p17 p3691 (rvc p139 p3631 (rvc p337 p3533 (rvc p3 p3701 (rvc p13 p3697 (rvc p67 p3671 (rvc p17 p3697 (rvc p67 p3673 (rvc p13 p3701 (rvc p131 p3643 (rvc p17 p3701 (rvc p3 p3709 (rvc p401 p3511 (rvc p139 p3643 (rvc p109 p3659 (rvc p83 p3673 (rvc p13 p3709 (rvc p499 p3467 (rvc p17 p3709 (rvc p43 p3697 (rvc p661 p3389 (rvc p3 p3719 (rvc p661 p3391 (rvc p43 p3701 (rvc p173 p3637 (rvc p67 p3691 (rvc p109 p3671 (rvc p239 p3607 (rvc p17 p3719 (rvc p3 p3727 (rvc p401 p3529 (rvc p67 p3697 (rvc p109 p3677 (rvc p239 p3613 (rvc p401 p3533 (rvc p3 p3733 (rvc p17 p3727 (rvc p131 p3671 (rvc p661 p3407 (rvc p131 p3673 (rvc p401 p3539 (rvc p3 p3739 (rvc p17 p3733 (rvc p67 p3709 (rvc p661 p3413 (rvc p107 p3691 (rvc p109 p3691 (rvc p139 p3677 (rvc p17 p3739 (rvc p43 p3727 (rvc p337 p3581 (rvc p239 p3631 (rvc p109 p3697 (rvc p67 p3719 (rvc p29 p3739 (rvc p107 p3701 (rvc p109 p3701 (rvc p131 p3691 (rvc p401 p3557 (rvc p1879 p2819 (rvc p401 p3559 (rvc p67 p3727 (rvc p337 p3593 (rvc p3 p3761 (rvc p109 p3709 (rvc p1291 p3119 (rvc p4217 p1657 (rvc p67 p3733 (rvc p13 p3761 (rvc p3 p3767 (rvc p17 p3761 (rvc p3 p3769 (rvc p401 p3571 (rvc p67 p3739 (rvc p109 p3719 (rvc p131 p3709 (rvc p17 p3767 (rvc p499 p3527 (rvc p17 p3769 (rvc p139 p3709 (rvc p661 p3449 (rvc p3 p3779 (rvc p109 p3727 (rvc p43 p3761 (rvc p401 p3583 (rvc p131 p3719 (rvc p13 p3779 (rvc p107 p3733 (rvc p17 p3779 (rvc p139 p3719 (rvc p1637 p2971 (rvc p239 p3671 (rvc p337 p3623 (rvc p131 p3727 (rvc p109 p3739 (rvc p3 p3793 (rvc p173 p3709 (rvc p139 p3727 (rvc p661 p3467 (rvc p3 p3797 (rvc p13 p3793 (rvc p67 p3767 (rvc p17 p3793 (rvc p67 p3769 (rvc p13 p3797 (rvc p3 p3803 (rvc p17 p3797 (rvc p499 p3557 (rvc p401 p3607 (rvc p139 p3739 (rvc p13 p3803 (rvc p239 p3691 (rvc p17 p3803 (rvc p67 p3779 (rvc p401 p3613 (rvc p107 p3761 (rvc p109 p3761 (rvc p239 p3697 (rvc p401 p3617 (rvc p43 p3797 (rvc p173 p3733 (rvc p239 p3701 (rvc p109 p3767 (rvc p3 p3821 (rvc p109 p3769 (rvc p3 p3823 (rvc p173 p3739 (rvc p67 p3793 (rvc p13 p3821 (rvc p239 p3709 (rvc p17 p3821 (rvc p67 p3797 (rvc p17 p3823 (rvc p131 p3767 (rvc p109 p3779 (rvc p3 p3833 (rvc p29 p3821 (rvc p67 p3803 (rvc p401 p3637 (rvc p139 p3769 (rvc p13 p3833 (rvc p1439 p3121 (rvc p17 p3833 (rvc p43 p3821 (rvc p401 p3643 (rvc p131 p3779 (rvc p337 p3677 (rvc p239 p3727 (rvc p109 p3793 (rvc p3 p3847 (rvc p4217 p1741 (rvc p107 p3797 (rvc p109 p3797 (rvc p3 p3851 (rvc p13 p3847 (rvc p3 p3853 (rvc p17 p3847 (rvc p67 p3823 (rvc p109 p3803 (rvc p131 p3793 (rvc p17 p3851 (rvc p487 p3617 (rvc p17 p3853 (rvc p131 p3797 (rvc p661 p3533 (rvc p3 p3863 (rvc p337 p3697 (rvc p67 p3833 (rvc p29 p3853 (rvc p131 p3803 (rvc p13 p3863 (rvc p3767 p1987 (rvc p17 p3863 (rvc p139 p3803 (rvc p401 p3673 (rvc p107 p3821 (rvc p109 p3821 (rvc p107 p3823 (rvc p109 p3823 (rvc p3 p3877 (rvc p173 p3793 (rvc p67 p3847 (rvc p1741 p3011 (rvc p3 p3881 (rvc p13 p3877 (rvc p67 p3851 (rvc p17 p3877 (rvc p67 p3853 (rvc p109 p3833 (rvc p131 p3823 (rvc p17 p3881 (rvc p3 p3889 (rvc p401 p3691 (rvc p139 p3823 (rvc p1549 p3119 (rvc p83 p3853 (rvc p13 p3889 (rvc p67 p3863 (rvc p17 p3889 (rvc p131 p3833 (rvc p157 p3821 (rvc p107 p3847 (rvc p109 p3847 (rvc p139 p3833 (rvc p29 p3889 (rvc p107 p3851 (rvc p109 p3851 (rvc p107 p3853 (rvc p109 p3853 (rvc p3 p3907 (rvc p401 p3709 (rvc p67 p3877 (rvc p661 p3581 (rvc p3 p3911 (rvc p13 p3907 (rvc p67 p3881 (rvc p17 p3907 (rvc p131 p3851 (rvc p109 p3863 (rvc p3 p3917 (rvc p17 p3911 (rvc p3 p3919 (rvc p29 p3907 (rvc p67 p3889 (rvc p13 p3917 (rvc p3 p3923 (rvc p17 p3917 (rvc p499 p3677 (rvc p17 p3919 (rvc p131 p3863 (rvc p13 p3923 (rvc p3 p3929 (rvc p17 p3923 (rvc p3 p3931 (rvc p401 p3733 (rvc p107 p3881 (rvc p109 p3881 (rvc p1439 p3217 (rvc p17 p3929 (rvc p43 p3917 (rvc p17 p3931 (rvc p67 p3907 (rvc p1549 p3167 (rvc p131 p3877 (rvc p109 p3889 (rvc p3 p3943 (rvc p29 p3931 (rvc p131 p3881 (rvc p337 p3779 (rvc p3 p3947 (rvc p13 p3943 (rvc p67 p3917 (rvc p17 p3943 (rvc p67 p3919 (rvc p13 p3947 (rvc p131 p3889 (rvc p17 p3947 (rvc p67 p3923 (rvc p29 p3943 (rvc p139 p3889 (rvc p1741 p3089 (rvc p107 p3907 (rvc p109 p3907 (rvc p67 p3929 (rvc p173 p3877 (rvc p67 p3931 (rvc p109 p3911 (rvc p239 p3847 (rvc p401 p3767 (rvc p3 p3967 (rvc p401 p3769 (rvc p239 p3851 (rvc p109 p3917 (rvc p131 p3907 (rvc p109 p3919 (rvc p1291 p3329 (rvc p17 p3967 (rvc p67 p3943 (rvc p109 p3923 (rvc p1439 p3259 (rvc p401 p3779 (rvc p67 p3947 (rvc p29 p3967 (rvc p131 p3917 (rvc p109 p3929 (rvc p131 p3919 (rvc p109 p3931 (rvc p139 p3917 (rvc p1637 p3169 (rvc p131 p3923 (rvc p337 p3821 (rvc p3 p3989 (rvc p337 p3823 (rvc p139 p3923 (rvc p401 p3793 (rvc p131 p3929 (rvc p13 p3989 (rvc p131 p3931 (rvc p17 p3989 (rvc p139 p3929 (rvc p1637 p3181 (rvc p67 p3967 (rvc p109 p3947 (rvc p3 p4001 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl7207 (m : ℕ) (hl : 7207 ≤ m) (hh : m ≤ 8006) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-7207)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 7207+2*k := by simp [k]; omega
  have hk : k < ql7207.length := by simp [k,ql7207]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl7207 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql8007 : List ℕ := [3803,4003,3919,3361,4001,4007,4001,3989,4003,3947,4007,4013,4007,3947,3931,3373,4013,4019,4013,4021,3823,4003,4019,3907,4019,4027,4021,3911,3863,3967,3833,4001,4027,4003,3167,3919,3709,4007,4027,3923,3989,4003,3877,4013,3847,3929,3881,4049,3851,4051,3853,4021,4001,4003,4049,4057,4051,4027,4007,3943,3863,3821,4057,4001,4013,4003,3739,4001,4057,4007,4019,4073,4021,4007,3877,4013,4073,4079,4073,4049,3307,4051,4079,4021,4079,4019,3889,4057,3923,4091,4007,4093,3319,4027,4091,4057,4091,4099,4093,4049,4049,4051,4051,4073,4099,3989,3779,4057,4057,4111,4027,4049,3947,4051,3917,4049,4111,4051,3347,4057,3923,4091,4111,4093,4073,4127,3929,4129,3931,4099,4079,4133,4127,3491,4129,4073,4133,4139,4133,4073,3943,4111,4091,4027,4139,4079,3331,4129,3821,4099,4099,4153,4129,4091,3989,4157,4153,4159,4153,4129,4157,4099,4157,4133,4159,4099,4001,4051,4003,4139,4159,4153,4007,4111,4091,4177,4093,4111,4127,4129,4129,3539,4177,4153,4133,3469,3989,4157,4177,4159,4139,4129,4027,4127,4111,4133,3329,4159,4001,4201,4003,4139,4127,4153,4153,4139,4201,4177,4157,4211,4159,1499,4129,3571,4211,4217,4211,4219,4021,4157,4217,4159,4217,4157,4219,4159,3359,4229,4177,4231,4219,4201,4229,3517,4229,4217,4231,4219,4073,4241,4157,4243,4159,4177,4241,4129,4241,4217,4243,4219,3923,4253,4201,4007,4057,4139,4253,4259,4253,4261,4177,4231,4211,4201,4259,3623,4261,4201,4217,4271,4219,4273,4261,4243,4271,4159,4271,4211,4273,4217,4229,4283,4231,4253,4201,4219,4283,4289,4283,4259,4093,4261,4241,4231,4289,4297,4099,4231,4133,3583,4297,4271,4297,4273,4253,4243,3491,4241,4111,4243,4259,4261,4261,4283,4231,4253,3989,4201,4153,4289,3547,4259,4271,4261,4273,4327,4129,4297,4001,3613,4133,4091,4327,4271,4283,4337,4139,4339,4327,4273,4289,3769,4337,3701,4339,4283,4019,4349,4297,4283,4153,4289,4349,3637,4349,4357,4159,4327,3491,4297,4357,4363,4357,4297,3593,4327,4363,4337,4363,4339,3947,4373,4289,4127,4177,4259,4373,4261,4373,4349,4297,4363,4217,2503,4219,4139,3571,4357,4337,4391,4339,4373,2287,4363,4391,4397,4391,4157,4201,4337]
private theorem vl8007 : rvld 2 8007 ql8007 := by
  unfold ql8007
  exact rvc p401 p3803 (rvc p3 p4003 (rvc p173 p3919 (rvc p1291 p3361 (rvc p13 p4001 (rvc p3 p4007 (rvc p17 p4001 (rvc p43 p3989 (rvc p17 p4003 (rvc p131 p3947 (rvc p13 p4007 (rvc p3 p4013 (rvc p17 p4007 (rvc p139 p3947 (rvc p173 p3931 (rvc p1291 p3373 (rvc p13 p4013 (rvc p3 p4019 (rvc p17 p4013 (rvc p3 p4021 (rvc p401 p3823 (rvc p43 p4003 (rvc p13 p4019 (rvc p239 p3907 (rvc p17 p4019 (rvc p3 p4027 (rvc p17 p4021 (rvc p239 p3911 (rvc p337 p3863 (rvc p131 p3967 (rvc p401 p3833 (rvc p67 p4001 (rvc p17 p4027 (rvc p67 p4003 (rvc p1741 p3167 (rvc p239 p3919 (rvc p661 p3709 (rvc p67 p4007 (rvc p29 p4027 (rvc p239 p3923 (rvc p109 p3989 (rvc p83 p4003 (rvc p337 p3877 (rvc p67 p4013 (rvc p401 p3847 (rvc p239 p3929 (rvc p337 p3881 (rvc p3 p4049 (rvc p401 p3851 (rvc p3 p4051 (rvc p401 p3853 (rvc p67 p4021 (rvc p109 p4001 (rvc p107 p4003 (rvc p17 p4049 (rvc p3 p4057 (rvc p17 p4051 (rvc p67 p4027 (rvc p109 p4007 (rvc p239 p3943 (rvc p401 p3863 (rvc p487 p3821 (rvc p17 p4057 (rvc p131 p4001 (rvc p109 p4013 (rvc p131 p4003 (rvc p661 p3739 (rvc p139 p4001 (rvc p29 p4057 (rvc p131 p4007 (rvc p109 p4019 (rvc p3 p4073 (rvc p109 p4021 (rvc p139 p4007 (rvc p401 p3877 (rvc p131 p4013 (rvc p13 p4073 (rvc p3 p4079 (rvc p17 p4073 (rvc p67 p4049 (rvc p1553 p3307 (rvc p67 p4051 (rvc p13 p4079 (rvc p131 p4021 (rvc p17 p4079 (rvc p139 p4019 (rvc p401 p3889 (rvc p67 p4057 (rvc p337 p3923 (rvc p3 p4091 (rvc p173 p4007 (rvc p3 p4093 (rvc p1553 p3319 (rvc p139 p4027 (rvc p13 p4091 (rvc p83 p4057 (rvc p17 p4091 (rvc p3 p4099 (rvc p17 p4093 (rvc p107 p4049 (rvc p109 p4049 (rvc p107 p4051 (rvc p109 p4051 (rvc p67 p4073 (rvc p17 p4099 (rvc p239 p3989 (rvc p661 p3779 (rvc p107 p4057 (rvc p109 p4057 (rvc p3 p4111 (rvc p173 p4027 (rvc p131 p4049 (rvc p337 p3947 (rvc p131 p4051 (rvc p401 p3917 (rvc p139 p4049 (rvc p17 p4111 (rvc p139 p4051 (rvc p1549 p3347 (rvc p131 p4057 (rvc p401 p3923 (rvc p67 p4091 (rvc p29 p4111 (rvc p67 p4093 (rvc p109 p4073 (rvc p3 p4127 (rvc p401 p3929 (rvc p3 p4129 (rvc p401 p3931 (rvc p67 p4099 (rvc p109 p4079 (rvc p3 p4133 (rvc p17 p4127 (rvc p1291 p3491 (rvc p17 p4129 (rvc p131 p4073 (rvc p13 p4133 (rvc p3 p4139 (rvc p17 p4133 (rvc p139 p4073 (rvc p401 p3943 (rvc p67 p4111 (rvc p109 p4091 (rvc p239 p4027 (rvc p17 p4139 (rvc p139 p4079 (rvc p1637 p3331 (rvc p43 p4129 (rvc p661 p3821 (rvc p107 p4099 (rvc p109 p4099 (rvc p3 p4153 (rvc p53 p4129 (rvc p131 p4091 (rvc p337 p3989 (rvc p3 p4157 (rvc p13 p4153 (rvc p3 p4159 (rvc p17 p4153 (rvc p67 p4129 (rvc p13 p4157 (rvc p131 p4099 (rvc p17 p4157 (rvc p67 p4133 (rvc p17 p4159 (rvc p139 p4099 (rvc p337 p4001 (rvc p239 p4051 (rvc p337 p4003 (rvc p67 p4139 (rvc p29 p4159 (rvc p43 p4153 (rvc p337 p4007 (rvc p131 p4111 (rvc p173 p4091 (rvc p3 p4177 (rvc p173 p4093 (rvc p139 p4111 (rvc p109 p4127 (rvc p107 p4129 (rvc p109 p4129 (rvc p1291 p3539 (rvc p17 p4177 (rvc p67 p4153 (rvc p109 p4133 (rvc p1439 p3469 (rvc p401 p3989 (rvc p67 p4157 (rvc p29 p4177 (rvc p67 p4159 (rvc p109 p4139 (rvc p131 p4129 (rvc p337 p4027 (rvc p139 p4127 (rvc p173 p4111 (rvc p131 p4133 (rvc p1741 p3329 (rvc p83 p4159 (rvc p401 p4001 (rvc p3 p4201 (rvc p401 p4003 (rvc p131 p4139 (rvc p157 p4127 (rvc p107 p4153 (rvc p109 p4153 (rvc p139 p4139 (rvc p17 p4201 (rvc p67 p4177 (rvc p109 p4157 (rvc p3 p4211 (rvc p109 p4159 (rvc p5431 p1499 (rvc p173 p4129 (rvc p1291 p3571 (rvc p13 p4211 (rvc p3 p4217 (rvc p17 p4211 (rvc p3 p4219 (rvc p401 p4021 (rvc p131 p4157 (rvc p13 p4217 (rvc p131 p4159 (rvc p17 p4217 (rvc p139 p4157 (rvc p17 p4219 (rvc p139 p4159 (rvc p1741 p3359 (rvc p3 p4229 (rvc p109 p4177 (rvc p3 p4231 (rvc p29 p4219 (rvc p67 p4201 (rvc p13 p4229 (rvc p1439 p3517 (rvc p17 p4229 (rvc p43 p4217 (rvc p17 p4231 (rvc p43 p4219 (rvc p337 p4073 (rvc p3 p4241 (rvc p173 p4157 (rvc p3 p4243 (rvc p173 p4159 (rvc p139 p4177 (rvc p13 p4241 (rvc p239 p4129 (rvc p17 p4241 (rvc p67 p4217 (rvc p17 p4243 (rvc p67 p4219 (rvc p661 p3923 (rvc p3 p4253 (rvc p109 p4201 (rvc p499 p4007 (rvc p401 p4057 (rvc p239 p4139 (rvc p13 p4253 (rvc p3 p4259 (rvc p17 p4253 (rvc p3 p4261 (rvc p173 p4177 (rvc p67 p4231 (rvc p109 p4211 (rvc p131 p4201 (rvc p17 p4259 (rvc p1291 p3623 (rvc p17 p4261 (rvc p139 p4201 (rvc p109 p4217 (rvc p3 p4271 (rvc p109 p4219 (rvc p3 p4273 (rvc p29 p4261 (rvc p67 p4243 (rvc p13 p4271 (rvc p239 p4159 (rvc p17 p4271 (rvc p139 p4211 (rvc p17 p4273 (rvc p131 p4217 (rvc p109 p4229 (rvc p3 p4283 (rvc p109 p4231 (rvc p67 p4253 (rvc p173 p4201 (rvc p139 p4219 (rvc p13 p4283 (rvc p3 p4289 (rvc p17 p4283 (rvc p67 p4259 (rvc p401 p4093 (rvc p67 p4261 (rvc p109 p4241 (rvc p131 p4231 (rvc p17 p4289 (rvc p3 p4297 (rvc p401 p4099 (rvc p139 p4231 (rvc p337 p4133 (rvc p1439 p3583 (rvc p13 p4297 (rvc p67 p4271 (rvc p17 p4297 (rvc p67 p4273 (rvc p109 p4253 (rvc p131 p4243 (rvc p1637 p3491 (rvc p139 p4241 (rvc p401 p4111 (rvc p139 p4243 (rvc p109 p4259 (rvc p107 p4261 (rvc p109 p4261 (rvc p67 p4283 (rvc p173 p4231 (rvc p131 p4253 (rvc p661 p3989 (rvc p239 p4201 (rvc p337 p4153 (rvc p67 p4289 (rvc p1553 p3547 (rvc p131 p4259 (rvc p109 p4271 (rvc p131 p4261 (rvc p109 p4273 (rvc p3 p4327 (rvc p401 p4129 (rvc p67 p4297 (rvc p661 p4001 (rvc p1439 p3613 (rvc p401 p4133 (rvc p487 p4091 (rvc p17 p4327 (rvc p131 p4271 (rvc p109 p4283 (rvc p3 p4337 (rvc p401 p4139 (rvc p3 p4339 (rvc p29 p4327 (rvc p139 p4273 (rvc p109 p4289 (rvc p1151 p3769 (rvc p17 p4337 (rvc p1291 p3701 (rvc p17 p4339 (rvc p131 p4283 (rvc p661 p4019 (rvc p3 p4349 (rvc p109 p4297 (rvc p139 p4283 (rvc p401 p4153 (rvc p131 p4289 (rvc p13 p4349 (rvc p1439 p3637 (rvc p17 p4349 (rvc p3 p4357 (rvc p401 p4159 (rvc p67 p4327 (rvc p1741 p3491 (rvc p131 p4297 (rvc p13 p4357 (rvc p3 p4363 (rvc p17 p4357 (rvc p139 p4297 (rvc p1549 p3593 (rvc p83 p4327 (rvc p13 p4363 (rvc p67 p4337 (rvc p17 p4363 (rvc p67 p4339 (rvc p853 p3947 (rvc p3 p4373 (rvc p173 p4289 (rvc p499 p4127 (rvc p401 p4177 (rvc p239 p4259 (rvc p13 p4373 (rvc p239 p4261 (rvc p17 p4373 (rvc p67 p4349 (rvc p173 p4297 (rvc p43 p4363 (rvc p337 p4217 (rvc p3767 p2503 (rvc p337 p4219 (rvc p499 p4139 (rvc p1637 p3571 (rvc p67 p4357 (rvc p109 p4337 (rvc p3 p4391 (rvc p109 p4339 (rvc p43 p4373 (rvc p4217 p2287 (rvc p67 p4363 (rvc p13 p4391 (rvc p3 p4397 (rvc p17 p4391 (rvc p487 p4157 (rvc p401 p4201 (rvc p131 p4337 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl8007 (m : ℕ) (hl : 8007 ≤ m) (hh : m ≤ 8806) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-8007)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 8007+2*k := by simp [k]; omega
  have hk : k < ql8007.length := by simp [k,ql8007]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl8007 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql8807 : List ℕ := [4349,4339,4397,4373,3631,4339,4241,4409,4357,4391,4327,4349,4409,4297,4409,4349,4219,3701,4253,4421,4337,4423,4339,4357,4373,4363,4421,4397,4423,4363,3659,2551,4349,1721,4423,4373,4271,2557,4241,4441,4243,4391,4391,4327,4441,4447,4441,4397,4397,4451,4253,4421,4447,4423,4451,4457,4451,4391,4261,4397,4409,4463,4457,4397,3691,4349,4463,4357,4463,4451,4273,4441,4421,4357,4423,4409,2371,4447,4463,4481,4283,4483,3709,4421,4481,4423,4481,4457,4483,4423,3719,4493,4441,4463,4297,3853,4493,4447,4493,4481,3727,4451,4451,4441,4339,4507,4423,4441,4457,4447,4507,4513,4507,4483,4463,4517,4513,4519,4513,4457,4517,4523,4517,4493,4519,4463,4523,2647,4523,4463,4447,4481,4481,4483,4483,4517,4339,4507,4373,4423,4457,4523,3727,4513,4493,4547,4349,4549,3733,4519,4547,4513,4547,4523,4549,4493,4391,4441,4507,4561,4363,3919,4397,4447,4513,4567,4561,4451,4517,4507,4519,3929,4567,4507,4523,4513,4493,4547,4567,4549,4253,4583,3767,4517,3769,4523,4583,4549,4583,4591,4507,4561,3821,3877,4397,4597,4591,4567,4547,4483,4549,4603,4597,4357,3833,3889,4409,3671,4603,4547,4283,4549,4561,4583,4603,4549,4451,4567,4567,4621,4423,4591,4457,4561,4621,4523,4621,4597,4463,4567,4547,3989,4549,4603,4583,4637,3821,4639,4441,4523,4637,4643,4637,4001,4639,4583,4643,4649,4643,4651,4567,4621,4649,4591,4649,4657,4651,4591,4493,4597,4463,4663,4657,4597,4337,4603,4663,4637,4663,4639,3803,4673,4621,4643,4591,4657,4673,4679,4673,4649,4483,4651,4679,4621,4679,4583,4603,4657,4637,4691,4639,4673,3877,4663,4643,4657,4691,4679,2593,4637,4649,4703,4651,4673,4507,4643,4703,4591,4703,4679,4513,4649,4547,4651,4663,4649,4519,4651,4391,4721,4523,4723,4639,4657,4673,4663,4721,4729,4723,4663,4679,4733,4729,4703,4729,4673,4733,4621,4733,4673,4657,4679,4691,4027,4547,4679,4549,4729,4583,4751,4423,4721,2647,4723,4703,4639,4751,4759,4561,4729,3989,4723,4759,4733,4759,4703,4691,4651,4603,4703,4759,4721,4721,4657,4723,4133,4003,4759,4451,4663,4729,4783,3967,4721,4733,4787,4783,4789,4783,4759,4787,4793,4787,4547,4789,4733,4793,4799,4793,4801]
private theorem vl8807 : rvld 2 8807 ql8807 := by
  unfold ql8807
  exact rvc p109 p4349 (rvc p131 p4339 (rvc p17 p4397 (rvc p67 p4373 (rvc p1553 p3631 (rvc p139 p4339 (rvc p337 p4241 (rvc p3 p4409 (rvc p109 p4357 (rvc p43 p4391 (rvc p173 p4327 (rvc p131 p4349 (rvc p13 p4409 (rvc p239 p4297 (rvc p17 p4409 (rvc p139 p4349 (rvc p401 p4219 (rvc p1439 p3701 (rvc p337 p4253 (rvc p3 p4421 (rvc p173 p4337 (rvc p3 p4423 (rvc p173 p4339 (rvc p139 p4357 (rvc p109 p4373 (rvc p131 p4363 (rvc p17 p4421 (rvc p67 p4397 (rvc p17 p4423 (rvc p139 p4363 (rvc p1549 p3659 (rvc p3767 p2551 (rvc p173 p4349 (rvc p5431 p1721 (rvc p29 p4423 (rvc p131 p4373 (rvc p337 p4271 (rvc p3767 p2557 (rvc p401 p4241 (rvc p3 p4441 (rvc p401 p4243 (rvc p107 p4391 (rvc p109 p4391 (rvc p239 p4327 (rvc p13 p4441 (rvc p3 p4447 (rvc p17 p4441 (rvc p107 p4397 (rvc p109 p4397 (rvc p3 p4451 (rvc p401 p4253 (rvc p67 p4421 (rvc p17 p4447 (rvc p67 p4423 (rvc p13 p4451 (rvc p3 p4457 (rvc p17 p4451 (rvc p139 p4391 (rvc p401 p4261 (rvc p131 p4397 (rvc p109 p4409 (rvc p3 p4463 (rvc p17 p4457 (rvc p139 p4397 (rvc p1553 p3691 (rvc p239 p4349 (rvc p13 p4463 (rvc p227 p4357 (rvc p17 p4463 (rvc p43 p4451 (rvc p401 p4273 (rvc p67 p4441 (rvc p109 p4421 (rvc p239 p4357 (rvc p109 p4423 (rvc p139 p4409 (rvc p4217 p2371 (rvc p67 p4447 (rvc p37 p4463 (rvc p3 p4481 (rvc p401 p4283 (rvc p3 p4483 (rvc p1553 p3709 (rvc p131 p4421 (rvc p13 p4481 (rvc p131 p4423 (rvc p17 p4481 (rvc p67 p4457 (rvc p17 p4483 (rvc p139 p4423 (rvc p1549 p3719 (rvc p3 p4493 (rvc p109 p4441 (rvc p67 p4463 (rvc p401 p4297 (rvc p1291 p3853 (rvc p13 p4493 (rvc p107 p4447 (rvc p17 p4493 (rvc p43 p4481 (rvc p1553 p3727 (rvc p107 p4451 (rvc p109 p4451 (rvc p131 p4441 (rvc p337 p4339 (rvc p3 p4507 (rvc p173 p4423 (rvc p139 p4441 (rvc p109 p4457 (rvc p131 p4447 (rvc p13 p4507 (rvc p3 p4513 (rvc p17 p4507 (rvc p67 p4483 (rvc p109 p4463 (rvc p3 p4517 (rvc p13 p4513 (rvc p3 p4519 (rvc p17 p4513 (rvc p131 p4457 (rvc p13 p4517 (rvc p3 p4523 (rvc p17 p4517 (rvc p67 p4493 (rvc p17 p4519 (rvc p131 p4463 (rvc p13 p4523 (rvc p3767 p2647 (rvc p17 p4523 (rvc p139 p4463 (rvc p173 p4447 (rvc p107 p4481 (rvc p109 p4481 (rvc p107 p4483 (rvc p109 p4483 (rvc p43 p4517 (rvc p401 p4339 (rvc p67 p4507 (rvc p337 p4373 (rvc p239 p4423 (rvc p173 p4457 (rvc p43 p4523 (rvc p1637 p3727 (rvc p67 p4513 (rvc p109 p4493 (rvc p3 p4547 (rvc p401 p4349 (rvc p3 p4549 (rvc p1637 p3733 (rvc p67 p4519 (rvc p13 p4547 (rvc p83 p4513 (rvc p17 p4547 (rvc p67 p4523 (rvc p17 p4549 (rvc p131 p4493 (rvc p337 p4391 (rvc p239 p4441 (rvc p109 p4507 (rvc p3 p4561 (rvc p401 p4363 (rvc p1291 p3919 (rvc p337 p4397 (rvc p239 p4447 (rvc p109 p4513 (rvc p3 p4567 (rvc p17 p4561 (rvc p239 p4451 (rvc p109 p4517 (rvc p131 p4507 (rvc p109 p4519 (rvc p1291 p3929 (rvc p17 p4567 (rvc p139 p4507 (rvc p109 p4523 (rvc p131 p4513 (rvc p173 p4493 (rvc p67 p4547 (rvc p29 p4567 (rvc p67 p4549 (rvc p661 p4253 (rvc p3 p4583 (rvc p1637 p3767 (rvc p139 p4517 (rvc p1637 p3769 (rvc p131 p4523 (rvc p13 p4583 (rvc p83 p4549 (rvc p17 p4583 (rvc p3 p4591 (rvc p173 p4507 (rvc p67 p4561 (rvc p1549 p3821 (rvc p1439 p3877 (rvc p401 p4397 (rvc p3 p4597 (rvc p17 p4591 (rvc p67 p4567 (rvc p109 p4547 (rvc p239 p4483 (rvc p109 p4549 (rvc p3 p4603 (rvc p17 p4597 (rvc p499 p4357 (rvc p1549 p3833 (rvc p1439 p3889 (rvc p401 p4409 (rvc p1879 p3671 (rvc p17 p4603 (rvc p131 p4547 (rvc p661 p4283 (rvc p131 p4549 (rvc p109 p4561 (rvc p67 p4583 (rvc p29 p4603 (rvc p139 p4549 (rvc p337 p4451 (rvc p107 p4567 (rvc p109 p4567 (rvc p3 p4621 (rvc p401 p4423 (rvc p67 p4591 (rvc p337 p4457 (rvc p131 p4561 (rvc p13 p4621 (rvc p211 p4523 (rvc p17 p4621 (rvc p67 p4597 (rvc p337 p4463 (rvc p131 p4567 (rvc p173 p4547 (rvc p1291 p3989 (rvc p173 p4549 (rvc p67 p4603 (rvc p109 p4583 (rvc p3 p4637 (rvc p1637 p3821 (rvc p3 p4639 (rvc p401 p4441 (rvc p239 p4523 (rvc p13 p4637 (rvc p3 p4643 (rvc p17 p4637 (rvc p1291 p4001 (rvc p17 p4639 (rvc p131 p4583 (rvc p13 p4643 (rvc p3 p4649 (rvc p17 p4643 (rvc p3 p4651 (rvc p173 p4567 (rvc p67 p4621 (rvc p13 p4649 (rvc p131 p4591 (rvc p17 p4649 (rvc p3 p4657 (rvc p17 p4651 (rvc p139 p4591 (rvc p337 p4493 (rvc p131 p4597 (rvc p401 p4463 (rvc p3 p4663 (rvc p17 p4657 (rvc p139 p4597 (rvc p661 p4337 (rvc p131 p4603 (rvc p13 p4663 (rvc p67 p4637 (rvc p17 p4663 (rvc p67 p4639 (rvc p1741 p3803 (rvc p3 p4673 (rvc p109 p4621 (rvc p67 p4643 (rvc p173 p4591 (rvc p43 p4657 (rvc p13 p4673 (rvc p3 p4679 (rvc p17 p4673 (rvc p67 p4649 (rvc p401 p4483 (rvc p67 p4651 (rvc p13 p4679 (rvc p131 p4621 (rvc p17 p4679 (rvc p211 p4583 (rvc p173 p4603 (rvc p67 p4657 (rvc p109 p4637 (rvc p3 p4691 (rvc p109 p4639 (rvc p43 p4673 (rvc p1637 p3877 (rvc p67 p4663 (rvc p109 p4643 (rvc p83 p4657 (rvc p17 p4691 (rvc p43 p4679 (rvc p4217 p2593 (rvc p131 p4637 (rvc p109 p4649 (rvc p3 p4703 (rvc p109 p4651 (rvc p67 p4673 (rvc p401 p4507 (rvc p131 p4643 (rvc p13 p4703 (rvc p239 p4591 (rvc p17 p4703 (rvc p67 p4679 (rvc p401 p4513 (rvc p131 p4649 (rvc p337 p4547 (rvc p131 p4651 (rvc p109 p4663 (rvc p139 p4649 (rvc p401 p4519 (rvc p139 p4651 (rvc p661 p4391 (rvc p3 p4721 (rvc p401 p4523 (rvc p3 p4723 (rvc p173 p4639 (rvc p139 p4657 (rvc p109 p4673 (rvc p131 p4663 (rvc p17 p4721 (rvc p3 p4729 (rvc p17 p4723 (rvc p139 p4663 (rvc p109 p4679 (rvc p3 p4733 (rvc p13 p4729 (rvc p67 p4703 (rvc p17 p4729 (rvc p131 p4673 (rvc p13 p4733 (rvc p239 p4621 (rvc p17 p4733 (rvc p139 p4673 (rvc p173 p4657 (rvc p131 p4679 (rvc p109 p4691 (rvc p1439 p4027 (rvc p401 p4547 (rvc p139 p4679 (rvc p401 p4549 (rvc p43 p4729 (rvc p337 p4583 (rvc p3 p4751 (rvc p661 p4423 (rvc p67 p4721 (rvc p4217 p2647 (rvc p67 p4723 (rvc p109 p4703 (rvc p239 p4639 (rvc p17 p4751 (rvc p3 p4759 (rvc p401 p4561 (rvc p67 p4729 (rvc p1549 p3989 (rvc p83 p4723 (rvc p13 p4759 (rvc p67 p4733 (rvc p17 p4759 (rvc p131 p4703 (rvc p157 p4691 (rvc p239 p4651 (rvc p337 p4603 (rvc p139 p4703 (rvc p29 p4759 (rvc p107 p4721 (rvc p109 p4721 (rvc p239 p4657 (rvc p109 p4723 (rvc p1291 p4133 (rvc p1553 p4003 (rvc p43 p4759 (rvc p661 p4451 (rvc p239 p4663 (rvc p109 p4729 (rvc p3 p4783 (rvc p1637 p3967 (rvc p131 p4721 (rvc p109 p4733 (rvc p3 p4787 (rvc p13 p4783 (rvc p3 p4789 (rvc p17 p4783 (rvc p67 p4759 (rvc p13 p4787 (rvc p3 p4793 (rvc p17 p4787 (rvc p499 p4547 (rvc p17 p4789 (rvc p131 p4733 (rvc p13 p4793 (rvc p3 p4799 (rvc p17 p4793 (rvc p3 p4801 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl8807 (m : ℕ) (hl : 8807 ≤ m) (hh : m ≤ 9606) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-8807)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 8807+2*k := by simp [k]; omega
  have hk : k < ql8807.length := by simp [k,ql8807]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl8807 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql9607 : List ℕ := [4603,4751,4751,4231,4799,4787,4801,4691,4643,4759,4759,4813,4729,4783,4649,4817,4813,4787,4813,4789,4817,4759,4817,4793,4813,4759,4751,4111,4663,4831,4057,4801,4409,4783,4783,4817,4831,4721,4787,4723,4789,2129,4759,4813,4793,4783,4649,4817,4651,4787,4799,4789,4801,4787,4657,4793,4691,1459,2753,4861,4663,4831,4091,4801,4813,4799,4861,4801,4817,4871,4673,4229,4789,4231,4871,4877,4871,4637,4657,4817,4877,4831,4877,4817,4801,4243,4721,4889,4691,4871,3,4861,4889,4831,4889,4877,4813,4831,4733,4783,4703,4903,4129,4787,4133,4789,4903,4909,4903,4793,4583,4861,4861,4271,4909,4799,4751,4919,4721,4889,4723,4871,4871,4861,4919,4283,4729,4861,4877,4931,4733,4933,4159,4903,4931,4937,4931,4871,4933,4909,4889,4943,4937,4877,4861,4229,4943,4831,4943,4951,4177,4889,4787,4903,4903,4957,4951,4241,4793,4909,4909,4931,4957,4933,4799,4967,4801,4969,4957,4903,4919,4973,4967,4943,4969,4909,4973,4861,4973,4337,4783,4951,4931,4933,4933,4987,4789,4957,4937,4273,4793,4993,4987,4931,4943,4933,4799,4999,4993,4969,4673,5003,4951,4973,4999,4943,5003,5009,5003,5011,4813,4993,5009,4951,5009,4373,5011,4987,4967,5021,4969,5023,5011,4993,4973,4909,5021,5009,5023,4999,4703,4969,5021,5003,4951,4973,4871,5039,4987,5009,4957,5011,5039,4993,5039,4799,4231,4931,4721,5051,4999,5021,4969,5023,5003,4993,5051,5059,4861,4993,5009,4999,5011,4421,5059,5003,4643,4951,4871,5039,4987,5009,5021,5011,5023,5077,4993,5011,4751,5081,5077,5051,5077,5021,5081,5087,5081,5021,5077,5059,5039,4519,5087,4451,5011,5077,4931,5099,4933,5101,4903,5039,5051,4987,5099,5107,5101,5077,4943,4993,5059,5113,5107,5051,4787,4999,4919,5119,5113,5003,4793,5059,5119,4481,5119,5059,4799,5011,5077,5099,4933,5101,5081,3253,4937,4493,4363,5107,5087,5077,4943,5039,5059,5113,4817,5147,4373,5081,4951,5119,5099,5153,5147,5087,4957,5039,5153,5107,5153,4517,5077,5099,4391,5101,5113,5167,4969,5101,5003,5171,5119,5153,5167,5107,5171,5113,5171,5179,5167,5113,4409,5119,5179,5153,5179,5119,5021,5189,5023,5171,4993,4549,5189,5077,5189,5197,4999,5167,5147,4483]
private theorem vl9607 : rvld 2 9607 ql9607 := by
  unfold ql9607
  exact rvc p401 p4603 (rvc p107 p4751 (rvc p109 p4751 (rvc p1151 p4231 (rvc p17 p4799 (rvc p43 p4787 (rvc p17 p4801 (rvc p239 p4691 (rvc p337 p4643 (rvc p107 p4759 (rvc p109 p4759 (rvc p3 p4813 (rvc p173 p4729 (rvc p67 p4783 (rvc p337 p4649 (rvc p3 p4817 (rvc p13 p4813 (rvc p67 p4787 (rvc p17 p4813 (rvc p67 p4789 (rvc p13 p4817 (rvc p131 p4759 (rvc p17 p4817 (rvc p67 p4793 (rvc p29 p4813 (rvc p139 p4759 (rvc p157 p4751 (rvc p1439 p4111 (rvc p337 p4663 (rvc p3 p4831 (rvc p1553 p4057 (rvc p67 p4801 (rvc p853 p4409 (rvc p107 p4783 (rvc p109 p4783 (rvc p43 p4817 (rvc p17 p4831 (rvc p239 p4721 (rvc p109 p4787 (rvc p239 p4723 (rvc p109 p4789 (rvc p5431 p2129 (rvc p173 p4759 (rvc p67 p4813 (rvc p109 p4793 (rvc p131 p4783 (rvc p401 p4649 (rvc p67 p4817 (rvc p401 p4651 (rvc p131 p4787 (rvc p109 p4799 (rvc p131 p4789 (rvc p109 p4801 (rvc p139 p4787 (rvc p401 p4657 (rvc p131 p4793 (rvc p337 p4691 (rvc p6803 p1459 (rvc p4217 p2753 (rvc p3 p4861 (rvc p401 p4663 (rvc p67 p4831 (rvc p1549 p4091 (rvc p131 p4801 (rvc p109 p4813 (rvc p139 p4799 (rvc p17 p4861 (rvc p139 p4801 (rvc p109 p4817 (rvc p3 p4871 (rvc p401 p4673 (rvc p1291 p4229 (rvc p173 p4789 (rvc p1291 p4231 (rvc p13 p4871 (rvc p3 p4877 (rvc p17 p4871 (rvc p487 p4637 (rvc p449 p4657 (rvc p131 p4817 (rvc p13 p4877 (rvc p107 p4831 (rvc p17 p4877 (rvc p139 p4817 (rvc p173 p4801 (rvc p1291 p4243 (rvc p337 p4721 (rvc p3 p4889 (rvc p401 p4691 (rvc p43 p4871 (rvc p9781 p3 (rvc p67 p4861 (rvc p13 p4889 (rvc p131 p4831 (rvc p17 p4889 (rvc p43 p4877 (rvc p173 p4813 (rvc p139 p4831 (rvc p337 p4733 (rvc p239 p4783 (rvc p401 p4703 (rvc p3 p4903 (rvc p1553 p4129 (rvc p239 p4787 (rvc p1549 p4133 (rvc p239 p4789 (rvc p13 p4903 (rvc p3 p4909 (rvc p17 p4903 (rvc p239 p4793 (rvc p661 p4583 (rvc p107 p4861 (rvc p109 p4861 (rvc p1291 p4271 (rvc p17 p4909 (rvc p239 p4799 (rvc p337 p4751 (rvc p3 p4919 (rvc p401 p4721 (rvc p67 p4889 (rvc p401 p4723 (rvc p107 p4871 (rvc p109 p4871 (rvc p131 p4861 (rvc p17 p4919 (rvc p1291 p4283 (rvc p401 p4729 (rvc p139 p4861 (rvc p109 p4877 (rvc p3 p4931 (rvc p401 p4733 (rvc p3 p4933 (rvc p1553 p4159 (rvc p67 p4903 (rvc p13 p4931 (rvc p3 p4937 (rvc p17 p4931 (rvc p139 p4871 (rvc p17 p4933 (rvc p67 p4909 (rvc p109 p4889 (rvc p3 p4943 (rvc p17 p4937 (rvc p139 p4877 (rvc p173 p4861 (rvc p1439 p4229 (rvc p13 p4943 (rvc p239 p4831 (rvc p17 p4943 (rvc p3 p4951 (rvc p1553 p4177 (rvc p131 p4889 (rvc p337 p4787 (rvc p107 p4903 (rvc p109 p4903 (rvc p3 p4957 (rvc p17 p4951 (rvc p1439 p4241 (rvc p337 p4793 (rvc p107 p4909 (rvc p109 p4909 (rvc p67 p4931 (rvc p17 p4957 (rvc p67 p4933 (rvc p337 p4799 (rvc p3 p4967 (rvc p337 p4801 (rvc p3 p4969 (rvc p29 p4957 (rvc p139 p4903 (rvc p109 p4919 (rvc p3 p4973 (rvc p17 p4967 (rvc p67 p4943 (rvc p17 p4969 (rvc p139 p4909 (rvc p13 p4973 (rvc p239 p4861 (rvc p17 p4973 (rvc p1291 p4337 (rvc p401 p4783 (rvc p67 p4951 (rvc p109 p4931 (rvc p107 p4933 (rvc p109 p4933 (rvc p3 p4987 (rvc p401 p4789 (rvc p67 p4957 (rvc p109 p4937 (rvc p1439 p4273 (rvc p401 p4793 (rvc p3 p4993 (rvc p17 p4987 (rvc p131 p4931 (rvc p109 p4943 (rvc p131 p4933 (rvc p401 p4799 (rvc p3 p4999 (rvc p17 p4993 (rvc p67 p4969 (rvc p661 p4673 (rvc p3 p5003 (rvc p109 p4951 (rvc p67 p4973 (rvc p17 p4999 (rvc p131 p4943 (rvc p13 p5003 (rvc p3 p5009 (rvc p17 p5003 (rvc p3 p5011 (rvc p401 p4813 (rvc p43 p4993 (rvc p13 p5009 (rvc p131 p4951 (rvc p17 p5009 (rvc p1291 p4373 (rvc p17 p5011 (rvc p67 p4987 (rvc p109 p4967 (rvc p3 p5021 (rvc p109 p4969 (rvc p3 p5023 (rvc p29 p5011 (rvc p67 p4993 (rvc p109 p4973 (rvc p239 p4909 (rvc p17 p5021 (rvc p43 p5009 (rvc p17 p5023 (rvc p67 p4999 (rvc p661 p4703 (rvc p131 p4969 (rvc p29 p5021 (rvc p67 p5003 (rvc p173 p4951 (rvc p131 p4973 (rvc p337 p4871 (rvc p3 p5039 (rvc p109 p4987 (rvc p67 p5009 (rvc p173 p4957 (rvc p67 p5011 (rvc p13 p5039 (rvc p107 p4993 (rvc p17 p5039 (rvc p499 p4799 (rvc p1637 p4231 (rvc p239 p4931 (rvc p661 p4721 (rvc p3 p5051 (rvc p109 p4999 (rvc p67 p5021 (rvc p173 p4969 (rvc p67 p5023 (rvc p109 p5003 (rvc p131 p4993 (rvc p17 p5051 (rvc p3 p5059 (rvc p401 p4861 (rvc p139 p4993 (rvc p109 p5009 (rvc p131 p4999 (rvc p109 p5011 (rvc p1291 p4421 (rvc p17 p5059 (rvc p131 p5003 (rvc p853 p4643 (rvc p239 p4951 (rvc p401 p4871 (rvc p67 p5039 (rvc p173 p4987 (rvc p131 p5009 (rvc p109 p5021 (rvc p131 p5011 (rvc p109 p5023 (rvc p3 p5077 (rvc p173 p4993 (rvc p139 p5011 (rvc p661 p4751 (rvc p3 p5081 (rvc p13 p5077 (rvc p67 p5051 (rvc p17 p5077 (rvc p131 p5021 (rvc p13 p5081 (rvc p3 p5087 (rvc p17 p5081 (rvc p139 p5021 (rvc p29 p5077 (rvc p67 p5059 (rvc p109 p5039 (rvc p1151 p4519 (rvc p17 p5087 (rvc p1291 p4451 (rvc p173 p5011 (rvc p43 p5077 (rvc p337 p4931 (rvc p3 p5099 (rvc p337 p4933 (rvc p3 p5101 (rvc p401 p4903 (rvc p131 p5039 (rvc p109 p5051 (rvc p239 p4987 (rvc p17 p5099 (rvc p3 p5107 (rvc p17 p5101 (rvc p67 p5077 (rvc p337 p4943 (rvc p239 p4993 (rvc p109 p5059 (rvc p3 p5113 (rvc p17 p5107 (rvc p131 p5051 (rvc p661 p4787 (rvc p239 p4999 (rvc p401 p4919 (rvc p3 p5119 (rvc p17 p5113 (rvc p239 p5003 (rvc p661 p4793 (rvc p131 p5059 (rvc p13 p5119 (rvc p1291 p4481 (rvc p17 p5119 (rvc p139 p5059 (rvc p661 p4799 (rvc p239 p5011 (rvc p109 p5077 (rvc p67 p5099 (rvc p401 p4933 (rvc p67 p5101 (rvc p109 p5081 (rvc p3767 p3253 (rvc p401 p4937 (rvc p1291 p4493 (rvc p1553 p4363 (rvc p67 p5107 (rvc p109 p5087 (rvc p131 p5077 (rvc p401 p4943 (rvc p211 p5039 (rvc p173 p5059 (rvc p67 p5113 (rvc p661 p4817 (rvc p3 p5147 (rvc p1553 p4373 (rvc p139 p5081 (rvc p401 p4951 (rvc p67 p5119 (rvc p109 p5099 (rvc p3 p5153 (rvc p17 p5147 (rvc p139 p5087 (rvc p401 p4957 (rvc p239 p5039 (rvc p13 p5153 (rvc p107 p5107 (rvc p17 p5153 (rvc p1291 p4517 (rvc p173 p5077 (rvc p131 p5099 (rvc p1549 p4391 (rvc p131 p5101 (rvc p109 p5113 (rvc p3 p5167 (rvc p401 p4969 (rvc p139 p5101 (rvc p337 p5003 (rvc p3 p5171 (rvc p109 p5119 (rvc p43 p5153 (rvc p17 p5167 (rvc p139 p5107 (rvc p13 p5171 (rvc p131 p5113 (rvc p17 p5171 (rvc p3 p5179 (rvc p29 p5167 (rvc p139 p5113 (rvc p1549 p4409 (rvc p131 p5119 (rvc p13 p5179 (rvc p67 p5153 (rvc p17 p5179 (rvc p139 p5119 (rvc p337 p5021 (rvc p3 p5189 (rvc p337 p5023 (rvc p43 p5171 (rvc p401 p4993 (rvc p1291 p4549 (rvc p13 p5189 (rvc p239 p5077 (rvc p17 p5189 (rvc p3 p5197 (rvc p401 p4999 (rvc p67 p5167 (rvc p109 p5147 (rvc p1439 p4483 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl9607 (m : ℕ) (hl : 9607 ≤ m) (hh : m ≤ 10406) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-9607)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 9607+2*k := by simp [k]; omega
  have hk : k < ql9607.length := by simp [k,ql9607]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl9607 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql10407 : List ℕ := [5003,5171,5197,5087,5153,5167,5009,5209,5011,5179,4787,3331,5209,5147,5209,5153,5051,5101,5167,5189,5023,5171,5171,5107,5059,5227,3121,5197,4457,5231,5179,5233,5227,5171,5231,5237,5231,5171,5233,5209,5189,5179,5237,5003,5233,5179,5081,5197,5197,5231,5167,5189,5087,3373,5171,5189,5059,5227,4931,5261,5209,5231,5179,5233,5261,4549,5261,5237,3163,5153,4943,5273,5107,5171,5077,5209,5273,5279,5273,5281,5197,5231,5231,5167,5279,4643,5281,5171,5237,5227,5279,5261,5209,5231,4967,5297,5099,5231,5101,5237,5297,5303,5297,5273,5107,5189,5303,5309,5303,5279,5113,5281,5261,5197,5309,5297,5119,5279,5153,4603,5237,5323,4507,5261,5273,5209,5323,5297,5323,5279,5279,5333,5281,5303,5323,5273,5333,4621,5333,5309,4567,5279,4919,5281,5147,5347,5323,5281,5297,5351,5153,5333,5347,5323,5303,4639,5351,4421,5347,5297,5309,5323,5197,5333,5167,5303,5039,4651,5171,5303,4597,5309,5297,5323,5323,5309,5179,5347,5051,5381,5297,5351,4567,5333,5333,5387,5381,5147,5167,5323,5387,5393,5387,4751,5197,5333,5393,5399,5393,5333,5179,5351,5351,4831,5399,5407,5209,4691,5081,5347,5407,5413,5407,5351,5087,5417,5413,5419,5413,5303,5417,3541,5417,5393,5419,5309,5261,3547,5231,5431,5233,5381,5381,4861,5237,5437,5431,5407,5387,5441,5437,5443,5437,5413,5393,4729,5441,5449,5443,5419,5399,5413,5449,5387,5449,5393,5381,5407,5407,5393,5449,5431,5297,5347,5413,5399,4651,5437,5417,5471,5419,5441,4657,5443,5471,5477,5471,5479,5281,5449,5477,5483,5477,5417,5479,5419,5483,5437,5483,5471,5407,5441,5441,5431,5443,5477,5413,5431,5333,5501,5449,5503,5419,5441,5501,5507,5501,5477,5503,5479,5507,5449,5507,5483,5431,5449,5351,5519,5507,5521,5323,5471,5471,5407,5519,5527,5521,5477,5477,5531,5479,5501,5527,5503,5483,5419,5531,5507,5527,5477,4673,5479,5531,5477,5347,5483,5381,5431,5351,5519,5527,5521,5501,5437,5503,5557,4783,5527,5507,5443,5557,5563,5557,5501,5399,5503,5563,5569,5563,5507,5519,5573,5521,5507,5569,5557,5573,5527,5573,5581,5569,5519,5531,5521,5387,5519,5581,5557,5261,5591,5393,5573,5581,5563,5591,5479,5591,5531,4783,5569]
private theorem vl10407 : rvld 2 10407 ql10407 := by
  unfold ql10407
  exact rvc p401 p5003 (rvc p67 p5171 (rvc p17 p5197 (rvc p239 p5087 (rvc p109 p5153 (rvc p83 p5167 (rvc p401 p5009 (rvc p3 p5209 (rvc p401 p5011 (rvc p67 p5179 (rvc p853 p4787 (rvc p3767 p3331 (rvc p13 p5209 (rvc p139 p5147 (rvc p17 p5209 (rvc p131 p5153 (rvc p337 p5051 (rvc p239 p5101 (rvc p109 p5167 (rvc p67 p5189 (rvc p401 p5023 (rvc p107 p5171 (rvc p109 p5171 (rvc p239 p5107 (rvc p337 p5059 (rvc p3 p5227 (rvc p4217 p3121 (rvc p67 p5197 (rvc p1549 p4457 (rvc p3 p5231 (rvc p109 p5179 (rvc p3 p5233 (rvc p17 p5227 (rvc p131 p5171 (rvc p13 p5231 (rvc p3 p5237 (rvc p17 p5231 (rvc p139 p5171 (rvc p17 p5233 (rvc p67 p5209 (rvc p109 p5189 (rvc p131 p5179 (rvc p17 p5237 (rvc p487 p5003 (rvc p29 p5233 (rvc p139 p5179 (rvc p337 p5081 (rvc p107 p5197 (rvc p109 p5197 (rvc p43 p5231 (rvc p173 p5167 (rvc p131 p5189 (rvc p337 p5087 (rvc p3767 p3373 (rvc p173 p5171 (rvc p139 p5189 (rvc p401 p5059 (rvc p67 p5227 (rvc p661 p4931 (rvc p3 p5261 (rvc p109 p5209 (rvc p67 p5231 (rvc p173 p5179 (rvc p67 p5233 (rvc p13 p5261 (rvc p1439 p4549 (rvc p17 p5261 (rvc p67 p5237 (rvc p4217 p3163 (rvc p239 p5153 (rvc p661 p4943 (rvc p3 p5273 (rvc p337 p5107 (rvc p211 p5171 (rvc p401 p5077 (rvc p139 p5209 (rvc p13 p5273 (rvc p3 p5279 (rvc p17 p5273 (rvc p3 p5281 (rvc p173 p5197 (rvc p107 p5231 (rvc p109 p5231 (rvc p239 p5167 (rvc p17 p5279 (rvc p1291 p4643 (rvc p17 p5281 (rvc p239 p5171 (rvc p109 p5237 (rvc p131 p5227 (rvc p29 p5279 (rvc p67 p5261 (rvc p173 p5209 (rvc p131 p5231 (rvc p661 p4967 (rvc p3 p5297 (rvc p401 p5099 (rvc p139 p5231 (rvc p401 p5101 (rvc p131 p5237 (rvc p13 p5297 (rvc p3 p5303 (rvc p17 p5297 (rvc p67 p5273 (rvc p401 p5107 (rvc p239 p5189 (rvc p13 p5303 (rvc p3 p5309 (rvc p17 p5303 (rvc p67 p5279 (rvc p401 p5113 (rvc p67 p5281 (rvc p109 p5261 (rvc p239 p5197 (rvc p17 p5309 (rvc p43 p5297 (rvc p401 p5119 (rvc p83 p5279 (rvc p337 p5153 (rvc p1439 p4603 (rvc p173 p5237 (rvc p3 p5323 (rvc p1637 p4507 (rvc p131 p5261 (rvc p109 p5273 (rvc p239 p5209 (rvc p13 p5323 (rvc p67 p5297 (rvc p17 p5323 (rvc p107 p5279 (rvc p109 p5279 (rvc p3 p5333 (rvc p109 p5281 (rvc p67 p5303 (rvc p29 p5323 (rvc p131 p5273 (rvc p13 p5333 (rvc p1439 p4621 (rvc p17 p5333 (rvc p67 p5309 (rvc p1553 p4567 (rvc p131 p5279 (rvc p853 p4919 (rvc p131 p5281 (rvc p401 p5147 (rvc p3 p5347 (rvc p53 p5323 (rvc p139 p5281 (rvc p109 p5297 (rvc p3 p5351 (rvc p401 p5153 (rvc p43 p5333 (rvc p17 p5347 (rvc p67 p5323 (rvc p109 p5303 (rvc p1439 p4639 (rvc p17 p5351 (rvc p1879 p4421 (rvc p29 p5347 (rvc p131 p5297 (rvc p109 p5309 (rvc p83 p5323 (rvc p337 p5197 (rvc p67 p5333 (rvc p401 p5167 (rvc p131 p5303 (rvc p661 p5039 (rvc p1439 p4651 (rvc p401 p5171 (rvc p139 p5303 (rvc p1553 p4597 (rvc p131 p5309 (rvc p157 p5297 (rvc p107 p5323 (rvc p109 p5323 (rvc p139 p5309 (rvc p401 p5179 (rvc p67 p5347 (rvc p661 p5051 (rvc p3 p5381 (rvc p173 p5297 (rvc p67 p5351 (rvc p1637 p4567 (rvc p107 p5333 (rvc p109 p5333 (rvc p3 p5387 (rvc p17 p5381 (rvc p487 p5147 (rvc p449 p5167 (rvc p139 p5323 (rvc p13 p5387 (rvc p3 p5393 (rvc p17 p5387 (rvc p1291 p4751 (rvc p401 p5197 (rvc p131 p5333 (rvc p13 p5393 (rvc p3 p5399 (rvc p17 p5393 (rvc p139 p5333 (rvc p449 p5179 (rvc p107 p5351 (rvc p109 p5351 (rvc p1151 p4831 (rvc p17 p5399 (rvc p3 p5407 (rvc p401 p5209 (rvc p1439 p4691 (rvc p661 p5081 (rvc p131 p5347 (rvc p13 p5407 (rvc p3 p5413 (rvc p17 p5407 (rvc p131 p5351 (rvc p661 p5087 (rvc p3 p5417 (rvc p13 p5413 (rvc p3 p5419 (rvc p17 p5413 (rvc p239 p5303 (rvc p13 p5417 (rvc p3767 p3541 (rvc p17 p5417 (rvc p67 p5393 (rvc p17 p5419 (rvc p239 p5309 (rvc p337 p5261 (rvc p3767 p3547 (rvc p401 p5231 (rvc p3 p5431 (rvc p401 p5233 (rvc p107 p5381 (rvc p109 p5381 (rvc p1151 p4861 (rvc p401 p5237 (rvc p3 p5437 (rvc p17 p5431 (rvc p67 p5407 (rvc p109 p5387 (rvc p3 p5441 (rvc p13 p5437 (rvc p3 p5443 (rvc p17 p5437 (rvc p67 p5413 (rvc p109 p5393 (rvc p1439 p4729 (rvc p17 p5441 (rvc p3 p5449 (rvc p17 p5443 (rvc p67 p5419 (rvc p109 p5399 (rvc p83 p5413 (rvc p13 p5449 (rvc p139 p5387 (rvc p17 p5449 (rvc p131 p5393 (rvc p157 p5381 (rvc p107 p5407 (rvc p109 p5407 (rvc p139 p5393 (rvc p29 p5449 (rvc p67 p5431 (rvc p337 p5297 (rvc p239 p5347 (rvc p109 p5413 (rvc p139 p5399 (rvc p1637 p4651 (rvc p67 p5437 (rvc p109 p5417 (rvc p3 p5471 (rvc p109 p5419 (rvc p67 p5441 (rvc p1637 p4657 (rvc p67 p5443 (rvc p13 p5471 (rvc p3 p5477 (rvc p17 p5471 (rvc p3 p5479 (rvc p401 p5281 (rvc p67 p5449 (rvc p13 p5477 (rvc p3 p5483 (rvc p17 p5477 (rvc p139 p5417 (rvc p17 p5479 (rvc p139 p5419 (rvc p13 p5483 (rvc p107 p5437 (rvc p17 p5483 (rvc p43 p5471 (rvc p173 p5407 (rvc p107 p5441 (rvc p109 p5441 (rvc p131 p5431 (rvc p109 p5443 (rvc p43 p5477 (rvc p173 p5413 (rvc p139 p5431 (rvc p337 p5333 (rvc p3 p5501 (rvc p109 p5449 (rvc p3 p5503 (rvc p173 p5419 (rvc p131 p5441 (rvc p13 p5501 (rvc p3 p5507 (rvc p17 p5501 (rvc p67 p5477 (rvc p17 p5503 (rvc p67 p5479 (rvc p13 p5507 (rvc p131 p5449 (rvc p17 p5507 (rvc p67 p5483 (rvc p173 p5431 (rvc p139 p5449 (rvc p337 p5351 (rvc p3 p5519 (rvc p29 p5507 (rvc p3 p5521 (rvc p401 p5323 (rvc p107 p5471 (rvc p109 p5471 (rvc p239 p5407 (rvc p17 p5519 (rvc p3 p5527 (rvc p17 p5521 (rvc p107 p5477 (rvc p109 p5477 (rvc p3 p5531 (rvc p109 p5479 (rvc p67 p5501 (rvc p17 p5527 (rvc p67 p5503 (rvc p109 p5483 (rvc p239 p5419 (rvc p17 p5531 (rvc p67 p5507 (rvc p29 p5527 (rvc p131 p5477 (rvc p1741 p4673 (rvc p131 p5479 (rvc p29 p5531 (rvc p139 p5477 (rvc p401 p5347 (rvc p131 p5483 (rvc p337 p5381 (rvc p239 p5431 (rvc p401 p5351 (rvc p67 p5519 (rvc p53 p5527 (rvc p67 p5521 (rvc p109 p5501 (rvc p239 p5437 (rvc p109 p5503 (rvc p3 p5557 (rvc p1553 p4783 (rvc p67 p5527 (rvc p109 p5507 (rvc p239 p5443 (rvc p13 p5557 (rvc p3 p5563 (rvc p17 p5557 (rvc p131 p5501 (rvc p337 p5399 (rvc p131 p5503 (rvc p13 p5563 (rvc p3 p5569 (rvc p17 p5563 (rvc p131 p5507 (rvc p109 p5519 (rvc p3 p5573 (rvc p109 p5521 (rvc p139 p5507 (rvc p17 p5569 (rvc p43 p5557 (rvc p13 p5573 (rvc p107 p5527 (rvc p17 p5573 (rvc p3 p5581 (rvc p29 p5569 (rvc p131 p5519 (rvc p109 p5531 (rvc p131 p5521 (rvc p401 p5387 (rvc p139 p5519 (rvc p17 p5581 (rvc p67 p5557 (rvc p661 p5261 (rvc p3 p5591 (rvc p401 p5393 (rvc p43 p5573 (rvc p29 p5581 (rvc p67 p5563 (rvc p13 p5591 (rvc p239 p5479 (rvc p17 p5591 (rvc p139 p5531 (rvc p1637 p4783 (rvc p67 p5569 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl10407 (m : ℕ) (hl : 10407 ≤ m) (hh : m ≤ 11206) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-10407)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 10407+2*k := by simp [k]; omega
  have hk : k < ql10407.length := by simp [k,ql10407]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl10407 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql11207 : List ℕ := [5273,5563,5437,5573,5407,4889,5441,5557,5557,5591,5413,5581,5189,5563,5563,4973,5419,5501,4751,5557,5569,5623,3517,5557,5573,5563,5623,5381,5623,5563,5303,5569,5581,5387,5437,5573,5471,5639,5441,5641,5443,5591,5591,5581,5639,5647,5641,5581,5483,5651,5647,5653,5647,5623,5651,5657,5651,5659,5653,5641,5657,5623,5657,5021,5659,5647,5501,5669,5471,5639,5659,5641,5669,5557,5669,5657,5479,5647,5351,5563,5483,5683,4909,5653,5519,5623,5683,5689,5683,5659,5639,5693,5641,5051,5689,5657,5693,5581,5693,5701,5503,5639,5651,5641,5653,5639,5701,5641,5657,5711,5659,5693,5701,5683,5711,5717,5711,5651,5521,5689,5669,5659,5717,5693,5527,5659,5399,5011,5531,5711,5647,5701,5657,5683,5683,5737,5653,5021,5573,5741,5689,5743,5737,5693,5693,5683,5741,5749,5743,5683,863,5689,5701,5507,5749,5693,5591,5641,5431,5693,5563,5711,5711,5701,5437,5519,5569,5737,5717,5653,5573,5741,5689,5743,5003,5659,5693,5779,5581,5749,5009,5783,5779,5717,5779,5669,5783,5737,5783,5791,5779,5741,5741,5743,5743,5153,5791,5779,5471,5801,5749,5783,5791,5741,5801,5807,5801,5741,4993,5779,5807,5813,5807,5783,4999,5749,5813,5701,5813,5821,5623,5791,5657,5107,5821,5827,5821,5711,5501,5779,5779,5801,5827,5717,5783,5119,5639,5839,5641,5821,4973,5843,5791,5813,5839,5783,5843,5849,5843,5851,5653,5821,5801,5791,5849,5857,5851,5827,5807,5861,5857,5843,5857,5801,5813,5867,5861,5869,5857,5839,5867,5821,5867,5843,5869,5813,5711,5879,5827,5881,5683,5851,5879,5821,5879,5867,5881,5857,5021,5827,5839,5861,5881,5827,5843,5897,5813,5867,5701,5869,5849,5903,5897,5261,5821,5843,5903,5791,5903,5879,5827,5881,5861,5851,5717,5849,5101,5851,5867,5857,5869,5923,5839,5861,5153,5927,5923,5897,5923,5867,5879,5869,5927,5903,5737,5869,5861,5939,5741,5297,5743,5879,5939,5881,5939,5879,5749,5881,5897,5233,5867,5953,5869,5923,5903,5839,5953,5927,5953,5897,5189,5923,5879,5897,5881,5903,5801,5851,5641,5939,5197,5953,5807,5857,5923,5333,5779,5861,5927,5981,5783,5741,5167,5953,5981,5987,5981,5741,5791,5927,5939,5953,5987,5927,5179,5879,5669,5881,5801,5981]
private theorem vl11207 : rvld 2 11207 ql11207 := by
  unfold ql11207
  exact rvc p661 p5273 (rvc p83 p5563 (rvc p337 p5437 (rvc p67 p5573 (rvc p401 p5407 (rvc p1439 p4889 (rvc p337 p5441 (rvc p107 p5557 (rvc p109 p5557 (rvc p43 p5591 (rvc p401 p5413 (rvc p67 p5581 (rvc p853 p5189 (rvc p107 p5563 (rvc p109 p5563 (rvc p1291 p4973 (rvc p401 p5419 (rvc p239 p5501 (rvc p1741 p4751 (rvc p131 p5557 (rvc p109 p5569 (rvc p3 p5623 (rvc p4217 p3517 (rvc p139 p5557 (rvc p109 p5573 (rvc p131 p5563 (rvc p13 p5623 (rvc p499 p5381 (rvc p17 p5623 (rvc p139 p5563 (rvc p661 p5303 (rvc p131 p5569 (rvc p109 p5581 (rvc p499 p5387 (rvc p401 p5437 (rvc p131 p5573 (rvc p337 p5471 (rvc p3 p5639 (rvc p401 p5441 (rvc p3 p5641 (rvc p401 p5443 (rvc p107 p5591 (rvc p109 p5591 (rvc p131 p5581 (rvc p17 p5639 (rvc p3 p5647 (rvc p17 p5641 (rvc p139 p5581 (rvc p337 p5483 (rvc p3 p5651 (rvc p13 p5647 (rvc p3 p5653 (rvc p17 p5647 (rvc p67 p5623 (rvc p13 p5651 (rvc p3 p5657 (rvc p17 p5651 (rvc p3 p5659 (rvc p17 p5653 (rvc p43 p5641 (rvc p13 p5657 (rvc p83 p5623 (rvc p17 p5657 (rvc p1291 p5021 (rvc p17 p5659 (rvc p43 p5647 (rvc p337 p5501 (rvc p3 p5669 (rvc p401 p5471 (rvc p67 p5639 (rvc p29 p5659 (rvc p67 p5641 (rvc p13 p5669 (rvc p239 p5557 (rvc p17 p5669 (rvc p43 p5657 (rvc p401 p5479 (rvc p67 p5647 (rvc p661 p5351 (rvc p239 p5563 (rvc p401 p5483 (rvc p3 p5683 (rvc p1553 p4909 (rvc p67 p5653 (rvc p337 p5519 (rvc p131 p5623 (rvc p13 p5683 (rvc p3 p5689 (rvc p17 p5683 (rvc p67 p5659 (rvc p109 p5639 (rvc p3 p5693 (rvc p109 p5641 (rvc p1291 p5051 (rvc p17 p5689 (rvc p83 p5657 (rvc p13 p5693 (rvc p239 p5581 (rvc p17 p5693 (rvc p3 p5701 (rvc p401 p5503 (rvc p131 p5639 (rvc p109 p5651 (rvc p131 p5641 (rvc p109 p5653 (rvc p139 p5639 (rvc p17 p5701 (rvc p139 p5641 (rvc p109 p5657 (rvc p3 p5711 (rvc p109 p5659 (rvc p43 p5693 (rvc p29 p5701 (rvc p67 p5683 (rvc p13 p5711 (rvc p3 p5717 (rvc p17 p5711 (rvc p139 p5651 (rvc p401 p5521 (rvc p67 p5689 (rvc p109 p5669 (rvc p131 p5659 (rvc p17 p5717 (rvc p67 p5693 (rvc p401 p5527 (rvc p139 p5659 (rvc p661 p5399 (rvc p1439 p5011 (rvc p401 p5531 (rvc p43 p5711 (rvc p173 p5647 (rvc p67 p5701 (rvc p157 p5657 (rvc p107 p5683 (rvc p109 p5683 (rvc p3 p5737 (rvc p173 p5653 (rvc p1439 p5021 (rvc p337 p5573 (rvc p3 p5741 (rvc p109 p5689 (rvc p3 p5743 (rvc p17 p5737 (rvc p107 p5693 (rvc p109 p5693 (rvc p131 p5683 (rvc p17 p5741 (rvc p3 p5749 (rvc p17 p5743 (rvc p139 p5683 (rvc p9781 p863 (rvc p131 p5689 (rvc p109 p5701 (rvc p499 p5507 (rvc p17 p5749 (rvc p131 p5693 (rvc p337 p5591 (rvc p239 p5641 (rvc p661 p5431 (rvc p139 p5693 (rvc p401 p5563 (rvc p107 p5711 (rvc p109 p5711 (rvc p131 p5701 (rvc p661 p5437 (rvc p499 p5519 (rvc p401 p5569 (rvc p67 p5737 (rvc p109 p5717 (rvc p239 p5653 (rvc p401 p5573 (rvc p67 p5741 (rvc p173 p5689 (rvc p67 p5743 (rvc p1549 p5003 (rvc p239 p5659 (rvc p173 p5693 (rvc p3 p5779 (rvc p401 p5581 (rvc p67 p5749 (rvc p1549 p5009 (rvc p3 p5783 (rvc p13 p5779 (rvc p139 p5717 (rvc p17 p5779 (rvc p239 p5669 (rvc p13 p5783 (rvc p107 p5737 (rvc p17 p5783 (rvc p3 p5791 (rvc p29 p5779 (rvc p107 p5741 (rvc p109 p5741 (rvc p107 p5743 (rvc p109 p5743 (rvc p1291 p5153 (rvc p17 p5791 (rvc p43 p5779 (rvc p661 p5471 (rvc p3 p5801 (rvc p109 p5749 (rvc p43 p5783 (rvc p29 p5791 (rvc p131 p5741 (rvc p13 p5801 (rvc p3 p5807 (rvc p17 p5801 (rvc p139 p5741 (rvc p1637 p4993 (rvc p67 p5779 (rvc p13 p5807 (rvc p3 p5813 (rvc p17 p5807 (rvc p67 p5783 (rvc p1637 p4999 (rvc p139 p5749 (rvc p13 p5813 (rvc p239 p5701 (rvc p17 p5813 (rvc p3 p5821 (rvc p401 p5623 (rvc p67 p5791 (rvc p337 p5657 (rvc p1439 p5107 (rvc p13 p5821 (rvc p3 p5827 (rvc p17 p5821 (rvc p239 p5711 (rvc p661 p5501 (rvc p107 p5779 (rvc p109 p5779 (rvc p67 p5801 (rvc p17 p5827 (rvc p239 p5717 (rvc p109 p5783 (rvc p1439 p5119 (rvc p401 p5639 (rvc p3 p5839 (rvc p401 p5641 (rvc p43 p5821 (rvc p1741 p4973 (rvc p3 p5843 (rvc p109 p5791 (rvc p67 p5813 (rvc p17 p5839 (rvc p131 p5783 (rvc p13 p5843 (rvc p3 p5849 (rvc p17 p5843 (rvc p3 p5851 (rvc p401 p5653 (rvc p67 p5821 (rvc p109 p5801 (rvc p131 p5791 (rvc p17 p5849 (rvc p3 p5857 (rvc p17 p5851 (rvc p67 p5827 (rvc p109 p5807 (rvc p3 p5861 (rvc p13 p5857 (rvc p43 p5843 (rvc p17 p5857 (rvc p131 p5801 (rvc p109 p5813 (rvc p3 p5867 (rvc p17 p5861 (rvc p3 p5869 (rvc p29 p5857 (rvc p67 p5839 (rvc p13 p5867 (rvc p107 p5821 (rvc p17 p5867 (rvc p67 p5843 (rvc p17 p5869 (rvc p131 p5813 (rvc p337 p5711 (rvc p3 p5879 (rvc p109 p5827 (rvc p3 p5881 (rvc p401 p5683 (rvc p67 p5851 (rvc p13 p5879 (rvc p131 p5821 (rvc p17 p5879 (rvc p43 p5867 (rvc p17 p5881 (rvc p67 p5857 (rvc p1741 p5021 (rvc p131 p5827 (rvc p109 p5839 (rvc p67 p5861 (rvc p29 p5881 (rvc p139 p5827 (rvc p109 p5843 (rvc p3 p5897 (rvc p173 p5813 (rvc p67 p5867 (rvc p401 p5701 (rvc p67 p5869 (rvc p109 p5849 (rvc p3 p5903 (rvc p17 p5897 (rvc p1291 p5261 (rvc p173 p5821 (rvc p131 p5843 (rvc p13 p5903 (rvc p239 p5791 (rvc p17 p5903 (rvc p67 p5879 (rvc p173 p5827 (rvc p67 p5881 (rvc p109 p5861 (rvc p131 p5851 (rvc p401 p5717 (rvc p139 p5849 (rvc p1637 p5101 (rvc p139 p5851 (rvc p109 p5867 (rvc p131 p5857 (rvc p109 p5869 (rvc p3 p5923 (rvc p173 p5839 (rvc p131 p5861 (rvc p1549 p5153 (rvc p3 p5927 (rvc p13 p5923 (rvc p67 p5897 (rvc p17 p5923 (rvc p131 p5867 (rvc p109 p5879 (rvc p131 p5869 (rvc p17 p5927 (rvc p67 p5903 (rvc p401 p5737 (rvc p139 p5869 (rvc p157 p5861 (rvc p3 p5939 (rvc p401 p5741 (rvc p1291 p5297 (rvc p401 p5743 (rvc p131 p5879 (rvc p13 p5939 (rvc p131 p5881 (rvc p17 p5939 (rvc p139 p5879 (rvc p401 p5749 (rvc p139 p5881 (rvc p109 p5897 (rvc p1439 p5233 (rvc p173 p5867 (rvc p3 p5953 (rvc p173 p5869 (rvc p67 p5923 (rvc p109 p5903 (rvc p239 p5839 (rvc p13 p5953 (rvc p67 p5927 (rvc p17 p5953 (rvc p131 p5897 (rvc p1549 p5189 (rvc p83 p5923 (rvc p173 p5879 (rvc p139 p5897 (rvc p173 p5881 (rvc p131 p5903 (rvc p337 p5801 (rvc p239 p5851 (rvc p661 p5641 (rvc p67 p5939 (rvc p1553 p5197 (rvc p43 p5953 (rvc p337 p5807 (rvc p239 p5857 (rvc p109 p5923 (rvc p1291 p5333 (rvc p401 p5779 (rvc p239 p5861 (rvc p109 p5927 (rvc p3 p5981 (rvc p401 p5783 (rvc p487 p5741 (rvc p1637 p5167 (rvc p67 p5953 (rvc p13 p5981 (rvc p3 p5987 (rvc p17 p5981 (rvc p499 p5741 (rvc p401 p5791 (rvc p131 p5927 (rvc p109 p5939 (rvc p83 p5953 (rvc p17 p5987 (rvc p139 p5927 (rvc p1637 p5179 (rvc p239 p5879 (rvc p661 p5669 (rvc p239 p5881 (rvc p401 p5801 (rvc p43 p5981 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl11207 (m : ℕ) (hl : 11207 ≤ m) (hh : m ≤ 12006) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-11207)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 11207+2*k := by simp [k]; omega
  have hk : k < ql11207.length := by simp [k,ql11207]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl11207 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql12007 : List ℕ := [5227,5939,5231,5953,5953,6007,5923,4127,5843,6011,5813,5981,6007,5897,6011,5953,6011,5987,5821,5953,5693,5449,5857,5381,5827,6007,5861,6029,5701,6011,6007,5981,5981,4153,6029,6037,5839,6007,5987,5923,5843,6043,6037,5981,5879,6047,5849,5981,6043,5987,6047,6053,6047,5987,5857,5939,6053,6007,6053,6029,6037,6011,6011,5347,5867,6067,5869,6037,5903,6007,6067,6073,6067,6043,5303,6037,5879,6079,6073,6029,6029,6043,6079,6053,6079,6067,6011,6089,6037,6091,6007,6029,6089,6043,6089,6029,6091,6067,6047,6101,5903,5861,6091,6073,6053,6043,6101,6089,4003,6079,5783,6113,6029,6047,6091,6053,6113,6067,6113,6121,5923,6091,5351,6007,6073,5483,6121,6011,5801,6131,6079,6133,6121,6067,6131,6073,6131,5897,6133,6073,6089,6143,6091,6113,6133,6079,6143,5431,6143,6151,5953,6121,6101,6091,6151,6089,6151,6091,5387,6043,5387,6163,6079,6133,6113,5449,6163,6101,6163,6053,5843,6173,6121,6143,6091,6113,6173,4297,6173,6113,5407,6151,6131,6121,6133,5939,5413,6121,5861,6073,5419,6173,5419,6163,6143,6197,6113,6199,4093,6133,6197,6203,6197,6173,6199,6143,6203,6091,6203,6211,6199,5569,6047,6151,6163,6217,6211,6151,6053,6221,6217,6203,6217,6173,6173,6163,6221,6229,6217,6199,5903,5659,6229,6203,6229,6173,5813,6121,6073,6173,6043,6211,5471,5527,6047,6247,6163,6217,6197,6133,6199,6221,6247,6203,6203,6257,6091,6011,6247,6229,6257,6263,6257,6197,6067,6203,6263,6269,6263,6271,6073,6221,6221,6211,6269,6277,6271,6247,6113,6217,6229,6263,6277,6221,5417,6287,6089,6257,6091,6173,6287,6229,6287,6263,6211,6229,6131,6299,6247,6301,6217,6271,6299,4423,6299,6287,6301,6277,6257,6311,6113,5669,6229,6247,6263,6317,6311,6287,6121,6257,6269,6323,6317,6257,4219,6263,6323,6329,6323,6299,6133,6301,6329,6271,6329,6337,5521,6271,6287,6277,6143,6343,6337,6277,5573,6229,6343,6317,6343,6287,6299,6353,6301,6323,6271,6337,6353,6359,6353,6361,6163,6299,6311,6301,6359,6367,6361,6337,6317,5653,6173,6373,6367,6343,6323,5659,6373,6379,6373,6317,6329,6343,6379,6353,6379,6323,6221,6389,6337,6359,6379,6361,6389,6277,6389,6397,6199,6367,5531,6337]
private theorem vl12007 : rvld 2 12007 ql12007 := by
  unfold ql12007
  exact rvc p1553 p5227 (rvc p131 p5939 (rvc p1549 p5231 (rvc p107 p5953 (rvc p109 p5953 (rvc p3 p6007 (rvc p173 p5923 (rvc p3767 p4127 (rvc p337 p5843 (rvc p3 p6011 (rvc p401 p5813 (rvc p67 p5981 (rvc p17 p6007 (rvc p239 p5897 (rvc p13 p6011 (rvc p131 p5953 (rvc p17 p6011 (rvc p67 p5987 (rvc p401 p5821 (rvc p139 p5953 (rvc p661 p5693 (rvc p1151 p5449 (rvc p337 p5857 (rvc p1291 p5381 (rvc p401 p5827 (rvc p43 p6007 (rvc p337 p5861 (rvc p3 p6029 (rvc p661 p5701 (rvc p43 p6011 (rvc p53 p6007 (rvc p107 p5981 (rvc p109 p5981 (rvc p3767 p4153 (rvc p17 p6029 (rvc p3 p6037 (rvc p401 p5839 (rvc p67 p6007 (rvc p109 p5987 (rvc p239 p5923 (rvc p401 p5843 (rvc p3 p6043 (rvc p17 p6037 (rvc p131 p5981 (rvc p337 p5879 (rvc p3 p6047 (rvc p401 p5849 (rvc p139 p5981 (rvc p17 p6043 (rvc p131 p5987 (rvc p13 p6047 (rvc p3 p6053 (rvc p17 p6047 (rvc p139 p5987 (rvc p401 p5857 (rvc p239 p5939 (rvc p13 p6053 (rvc p107 p6007 (rvc p17 p6053 (rvc p67 p6029 (rvc p53 p6037 (rvc p107 p6011 (rvc p109 p6011 (rvc p1439 p5347 (rvc p401 p5867 (rvc p3 p6067 (rvc p401 p5869 (rvc p67 p6037 (rvc p337 p5903 (rvc p131 p6007 (rvc p13 p6067 (rvc p3 p6073 (rvc p17 p6067 (rvc p67 p6043 (rvc p1549 p5303 (rvc p83 p6037 (rvc p401 p5879 (rvc p3 p6079 (rvc p17 p6073 (rvc p107 p6029 (rvc p109 p6029 (rvc p83 p6043 (rvc p13 p6079 (rvc p67 p6053 (rvc p17 p6079 (rvc p43 p6067 (rvc p157 p6011 (rvc p3 p6089 (rvc p109 p6037 (rvc p3 p6091 (rvc p173 p6007 (rvc p131 p6029 (rvc p13 p6089 (rvc p107 p6043 (rvc p17 p6089 (rvc p139 p6029 (rvc p17 p6091 (rvc p67 p6067 (rvc p109 p6047 (rvc p3 p6101 (rvc p401 p5903 (rvc p487 p5861 (rvc p29 p6091 (rvc p67 p6073 (rvc p109 p6053 (rvc p131 p6043 (rvc p17 p6101 (rvc p43 p6089 (rvc p4217 p4003 (rvc p67 p6079 (rvc p661 p5783 (rvc p3 p6113 (rvc p173 p6029 (rvc p139 p6047 (rvc p53 p6091 (rvc p131 p6053 (rvc p13 p6113 (rvc p107 p6067 (rvc p17 p6113 (rvc p3 p6121 (rvc p401 p5923 (rvc p67 p6091 (rvc p1549 p5351 (rvc p239 p6007 (rvc p109 p6073 (rvc p1291 p5483 (rvc p17 p6121 (rvc p239 p6011 (rvc p661 p5801 (rvc p3 p6131 (rvc p109 p6079 (rvc p3 p6133 (rvc p29 p6121 (rvc p139 p6067 (rvc p13 p6131 (rvc p131 p6073 (rvc p17 p6131 (rvc p487 p5897 (rvc p17 p6133 (rvc p139 p6073 (rvc p109 p6089 (rvc p3 p6143 (rvc p109 p6091 (rvc p67 p6113 (rvc p29 p6133 (rvc p139 p6079 (rvc p13 p6143 (rvc p1439 p5431 (rvc p17 p6143 (rvc p3 p6151 (rvc p401 p5953 (rvc p67 p6121 (rvc p109 p6101 (rvc p131 p6091 (rvc p13 p6151 (rvc p139 p6089 (rvc p17 p6151 (rvc p139 p6091 (rvc p1549 p5387 (rvc p239 p6043 (rvc p1553 p5387 (rvc p3 p6163 (rvc p173 p6079 (rvc p67 p6133 (rvc p109 p6113 (rvc p1439 p5449 (rvc p13 p6163 (rvc p139 p6101 (rvc p17 p6163 (rvc p239 p6053 (rvc p661 p5843 (rvc p3 p6173 (rvc p109 p6121 (rvc p67 p6143 (rvc p173 p6091 (rvc p131 p6113 (rvc p13 p6173 (rvc p3767 p4297 (rvc p17 p6173 (rvc p139 p6113 (rvc p1553 p5407 (rvc p67 p6151 (rvc p109 p6131 (rvc p131 p6121 (rvc p109 p6133 (rvc p499 p5939 (rvc p1553 p5413 (rvc p139 p6121 (rvc p661 p5861 (rvc p239 p6073 (rvc p1549 p5419 (rvc p43 p6173 (rvc p1553 p5419 (rvc p67 p6163 (rvc p109 p6143 (rvc p3 p6197 (rvc p173 p6113 (rvc p3 p6199 (rvc p4217 p4093 (rvc p139 p6133 (rvc p13 p6197 (rvc p3 p6203 (rvc p17 p6197 (rvc p67 p6173 (rvc p17 p6199 (rvc p131 p6143 (rvc p13 p6203 (rvc p239 p6091 (rvc p17 p6203 (rvc p3 p6211 (rvc p29 p6199 (rvc p1291 p5569 (rvc p337 p6047 (rvc p131 p6151 (rvc p109 p6163 (rvc p3 p6217 (rvc p17 p6211 (rvc p139 p6151 (rvc p337 p6053 (rvc p3 p6221 (rvc p13 p6217 (rvc p43 p6203 (rvc p17 p6217 (rvc p107 p6173 (rvc p109 p6173 (rvc p131 p6163 (rvc p17 p6221 (rvc p3 p6229 (rvc p29 p6217 (rvc p67 p6199 (rvc p661 p5903 (rvc p1151 p5659 (rvc p13 p6229 (rvc p67 p6203 (rvc p17 p6229 (rvc p131 p6173 (rvc p853 p5813 (rvc p239 p6121 (rvc p337 p6073 (rvc p139 p6173 (rvc p401 p6043 (rvc p67 p6211 (rvc p1549 p5471 (rvc p1439 p5527 (rvc p401 p6047 (rvc p3 p6247 (rvc p173 p6163 (rvc p67 p6217 (rvc p109 p6197 (rvc p239 p6133 (rvc p109 p6199 (rvc p67 p6221 (rvc p17 p6247 (rvc p107 p6203 (rvc p109 p6203 (rvc p3 p6257 (rvc p337 p6091 (rvc p499 p6011 (rvc p29 p6247 (rvc p67 p6229 (rvc p13 p6257 (rvc p3 p6263 (rvc p17 p6257 (rvc p139 p6197 (rvc p401 p6067 (rvc p131 p6203 (rvc p13 p6263 (rvc p3 p6269 (rvc p17 p6263 (rvc p3 p6271 (rvc p401 p6073 (rvc p107 p6221 (rvc p109 p6221 (rvc p131 p6211 (rvc p17 p6269 (rvc p3 p6277 (rvc p17 p6271 (rvc p67 p6247 (rvc p337 p6113 (rvc p131 p6217 (rvc p109 p6229 (rvc p43 p6263 (rvc p17 p6277 (rvc p131 p6221 (rvc p1741 p5417 (rvc p3 p6287 (rvc p401 p6089 (rvc p67 p6257 (rvc p401 p6091 (rvc p239 p6173 (rvc p13 p6287 (rvc p131 p6229 (rvc p17 p6287 (rvc p67 p6263 (rvc p173 p6211 (rvc p139 p6229 (rvc p337 p6131 (rvc p3 p6299 (rvc p109 p6247 (rvc p3 p6301 (rvc p173 p6217 (rvc p67 p6271 (rvc p13 p6299 (rvc p3767 p4423 (rvc p17 p6299 (rvc p43 p6287 (rvc p17 p6301 (rvc p67 p6277 (rvc p109 p6257 (rvc p3 p6311 (rvc p401 p6113 (rvc p1291 p5669 (rvc p173 p6229 (rvc p139 p6247 (rvc p109 p6263 (rvc p3 p6317 (rvc p17 p6311 (rvc p67 p6287 (rvc p401 p6121 (rvc p131 p6257 (rvc p109 p6269 (rvc p3 p6323 (rvc p17 p6317 (rvc p139 p6257 (rvc p4217 p4219 (rvc p131 p6263 (rvc p13 p6323 (rvc p3 p6329 (rvc p17 p6323 (rvc p67 p6299 (rvc p401 p6133 (rvc p67 p6301 (rvc p13 p6329 (rvc p131 p6271 (rvc p17 p6329 (rvc p3 p6337 (rvc p1637 p5521 (rvc p139 p6271 (rvc p109 p6287 (rvc p131 p6277 (rvc p401 p6143 (rvc p3 p6343 (rvc p17 p6337 (rvc p139 p6277 (rvc p1549 p5573 (rvc p239 p6229 (rvc p13 p6343 (rvc p67 p6317 (rvc p17 p6343 (rvc p131 p6287 (rvc p109 p6299 (rvc p3 p6353 (rvc p109 p6301 (rvc p67 p6323 (rvc p173 p6271 (rvc p43 p6337 (rvc p13 p6353 (rvc p3 p6359 (rvc p17 p6353 (rvc p3 p6361 (rvc p401 p6163 (rvc p131 p6299 (rvc p109 p6311 (rvc p131 p6301 (rvc p17 p6359 (rvc p3 p6367 (rvc p17 p6361 (rvc p67 p6337 (rvc p109 p6317 (rvc p1439 p5653 (rvc p401 p6173 (rvc p3 p6373 (rvc p17 p6367 (rvc p67 p6343 (rvc p109 p6323 (rvc p1439 p5659 (rvc p13 p6373 (rvc p3 p6379 (rvc p17 p6373 (rvc p131 p6317 (rvc p109 p6329 (rvc p83 p6343 (rvc p13 p6379 (rvc p67 p6353 (rvc p17 p6379 (rvc p131 p6323 (rvc p337 p6221 (rvc p3 p6389 (rvc p109 p6337 (rvc p67 p6359 (rvc p29 p6379 (rvc p67 p6361 (rvc p13 p6389 (rvc p239 p6277 (rvc p17 p6389 (rvc p3 p6397 (rvc p401 p6199 (rvc p67 p6367 (rvc p1741 p5531 (rvc p131 p6337 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl12007 (m : ℕ) (hl : 12007 ≤ m) (hh : m ≤ 12806) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-12007)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 12007+2*k := by simp [k]; omega
  have hk : k < ql12007.length := by simp [k,ql12007]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl12007 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql12807 : List ℕ := [6203,6299,6397,6373,6353,6343,6323,6389,6211,6379,6359,6361,6361,6173,6217,6353,6089,6301,6367,6421,6337,6359,6257,6361,6373,6427,6421,6397,6263,6367,6379,6329,6427,6367,6269,6373,6271,6197,6427,6373,6389,6379,6277,5801,6247,6379,1559,6449,6397,6451,6367,6421,6449,6337,6449,6389,6451,6427,6131,6397,6263,6221,6379,6397,6299,5749,6269,6469,6271,6353,6143,6473,6421,3761,6469,6359,6473,6361,6473,6481,6397,6451,6317,6421,6287,5843,6481,6421,6323,6491,6163,6473,6481,6427,6491,6379,6491,6257,6301,6469,6449,6451,6451,6473,6421,6389,5639,5791,6311,6491,6427,6481,5741,6451,6317,6449,5701,6451,6353,6521,6469,6491,5749,6473,6473,5953,6521,6529,4423,5813,6203,6469,6481,6287,6529,6473,5669,6421,6373,6473,6343,6491,6491,6481,6379,6547,4441,6481,6221,6551,6353,6553,6547,6491,6551,5839,6551,6491,6553,6529,5693,6563,6397,6317,6367,6449,6563,6569,6563,6571,6373,6521,6521,5857,6569,6577,6571,6547,5807,6581,6529,6551,6577,6553,6581,6469,6581,6521,6577,6473,6263,6529,6427,6563,6397,6529,6269,6599,6547,6569,5827,6571,6551,6553,6599,6607,5791,6577,5741,6547,6607,6581,6607,6551,6563,6553,6451,6619,6421,6553,6569,6571,6571,5981,6619,6563,6299,6577,6577,6599,6547,6569,6581,6571,6469,6637,6553,6607,6473,6577,6637,3929,6637,6581,6317,6529,6449,6581,6451,6619,6599,6653,6569,6011,6571,6637,6653,6659,6653,6661,6577,6599,6659,6547,6659,6599,6661,6637,5897,6607,6619,6673,6661,6607,5903,6637,6673,6679,6673,6563,6353,6619,6679,6653,6679,6619,6521,6689,6637,6691,6607,6661,6689,6577,6689,6053,6691,6581,5927,6701,6373,6703,6619,6673,6653,6133,6701,6709,6703,6679,6659,6661,6661,6473,6709,6653,6551,6719,6521,6689,6637,6691,6719,6661,6719,6659,6529,6661,6563,6679,6679,6733,6709,6703,6569,6737,6733,6719,6733,6709,6689,6679,6737,6101,6547,6679,6581,6709,6551,6719,6553,6689,6701,6691,6703,6689,6673,6691,5987,6761,6709,6763,6679,6733,6761,6703,6761,6737,6763,6703,6719,6709,6607,6131,6577,6709,6449,6779,6581,6781,6007,6719,6779,6733,6779,6719,6781,6737,6737,6791,6779,6793,6709,6763,6791,6733,6791,6779,6793,6737]
private theorem vl12807 : rvld 2 12807 ql12807 := by
  unfold ql12807
  exact rvc p401 p6203 (rvc p211 p6299 (rvc p17 p6397 (rvc p67 p6373 (rvc p109 p6353 (rvc p131 p6343 (rvc p173 p6323 (rvc p43 p6389 (rvc p401 p6211 (rvc p67 p6379 (rvc p109 p6359 (rvc p107 p6361 (rvc p109 p6361 (rvc p487 p6173 (rvc p401 p6217 (rvc p131 p6353 (rvc p661 p6089 (rvc p239 p6301 (rvc p109 p6367 (rvc p3 p6421 (rvc p173 p6337 (rvc p131 p6359 (rvc p337 p6257 (rvc p131 p6361 (rvc p109 p6373 (rvc p3 p6427 (rvc p17 p6421 (rvc p67 p6397 (rvc p337 p6263 (rvc p131 p6367 (rvc p109 p6379 (rvc p211 p6329 (rvc p17 p6427 (rvc p139 p6367 (rvc p337 p6269 (rvc p131 p6373 (rvc p337 p6271 (rvc p487 p6197 (rvc p29 p6427 (rvc p139 p6373 (rvc p109 p6389 (rvc p131 p6379 (rvc p337 p6277 (rvc p1291 p5801 (rvc p401 p6247 (rvc p139 p6379 (rvc p9781 p1559 (rvc p3 p6449 (rvc p109 p6397 (rvc p3 p6451 (rvc p173 p6367 (rvc p67 p6421 (rvc p13 p6449 (rvc p239 p6337 (rvc p17 p6449 (rvc p139 p6389 (rvc p17 p6451 (rvc p67 p6427 (rvc p661 p6131 (rvc p131 p6397 (rvc p401 p6263 (rvc p487 p6221 (rvc p173 p6379 (rvc p139 p6397 (rvc p337 p6299 (rvc p1439 p5749 (rvc p401 p6269 (rvc p3 p6469 (rvc p401 p6271 (rvc p239 p6353 (rvc p661 p6143 (rvc p3 p6473 (rvc p109 p6421 (rvc p5431 p3761 (rvc p17 p6469 (rvc p239 p6359 (rvc p13 p6473 (rvc p239 p6361 (rvc p17 p6473 (rvc p3 p6481 (rvc p173 p6397 (rvc p67 p6451 (rvc p337 p6317 (rvc p131 p6421 (rvc p401 p6287 (rvc p1291 p5843 (rvc p17 p6481 (rvc p139 p6421 (rvc p337 p6323 (rvc p3 p6491 (rvc p661 p6163 (rvc p43 p6473 (rvc p29 p6481 (rvc p139 p6427 (rvc p13 p6491 (rvc p239 p6379 (rvc p17 p6491 (rvc p487 p6257 (rvc p401 p6301 (rvc p67 p6469 (rvc p109 p6449 (rvc p107 p6451 (rvc p109 p6451 (rvc p67 p6473 (rvc p173 p6421 (rvc p239 p6389 (rvc p1741 p5639 (rvc p1439 p5791 (rvc p401 p6311 (rvc p43 p6491 (rvc p173 p6427 (rvc p67 p6481 (rvc p1549 p5741 (rvc p131 p6451 (rvc p401 p6317 (rvc p139 p6449 (rvc p1637 p5701 (rvc p139 p6451 (rvc p337 p6353 (rvc p3 p6521 (rvc p109 p6469 (rvc p67 p6491 (rvc p1553 p5749 (rvc p107 p6473 (rvc p109 p6473 (rvc p1151 p5953 (rvc p17 p6521 (rvc p3 p6529 (rvc p4217 p4423 (rvc p1439 p5813 (rvc p661 p6203 (rvc p131 p6469 (rvc p109 p6481 (rvc p499 p6287 (rvc p17 p6529 (rvc p131 p6473 (rvc p1741 p5669 (rvc p239 p6421 (rvc p337 p6373 (rvc p139 p6473 (rvc p401 p6343 (rvc p107 p6491 (rvc p109 p6491 (rvc p131 p6481 (rvc p337 p6379 (rvc p3 p6547 (rvc p4217 p4441 (rvc p139 p6481 (rvc p661 p6221 (rvc p3 p6551 (rvc p401 p6353 (rvc p3 p6553 (rvc p17 p6547 (rvc p131 p6491 (rvc p13 p6551 (rvc p1439 p5839 (rvc p17 p6551 (rvc p139 p6491 (rvc p17 p6553 (rvc p67 p6529 (rvc p1741 p5693 (rvc p3 p6563 (rvc p337 p6397 (rvc p499 p6317 (rvc p401 p6367 (rvc p239 p6449 (rvc p13 p6563 (rvc p3 p6569 (rvc p17 p6563 (rvc p3 p6571 (rvc p401 p6373 (rvc p107 p6521 (rvc p109 p6521 (rvc p1439 p5857 (rvc p17 p6569 (rvc p3 p6577 (rvc p17 p6571 (rvc p67 p6547 (rvc p1549 p5807 (rvc p3 p6581 (rvc p109 p6529 (rvc p67 p6551 (rvc p17 p6577 (rvc p67 p6553 (rvc p13 p6581 (rvc p239 p6469 (rvc p17 p6581 (rvc p139 p6521 (rvc p29 p6577 (rvc p239 p6473 (rvc p661 p6263 (rvc p131 p6529 (rvc p337 p6427 (rvc p67 p6563 (rvc p401 p6397 (rvc p139 p6529 (rvc p661 p6269 (rvc p3 p6599 (rvc p109 p6547 (rvc p67 p6569 (rvc p1553 p5827 (rvc p67 p6571 (rvc p109 p6551 (rvc p107 p6553 (rvc p17 p6599 (rvc p3 p6607 (rvc p1637 p5791 (rvc p67 p6577 (rvc p1741 p5741 (rvc p131 p6547 (rvc p13 p6607 (rvc p67 p6581 (rvc p17 p6607 (rvc p131 p6551 (rvc p109 p6563 (rvc p131 p6553 (rvc p337 p6451 (rvc p3 p6619 (rvc p401 p6421 (rvc p139 p6553 (rvc p109 p6569 (rvc p107 p6571 (rvc p109 p6571 (rvc p1291 p5981 (rvc p17 p6619 (rvc p131 p6563 (rvc p661 p6299 (rvc p107 p6577 (rvc p109 p6577 (rvc p67 p6599 (rvc p173 p6547 (rvc p131 p6569 (rvc p109 p6581 (rvc p131 p6571 (rvc p337 p6469 (rvc p3 p6637 (rvc p173 p6553 (rvc p67 p6607 (rvc p337 p6473 (rvc p131 p6577 (rvc p13 p6637 (rvc p5431 p3929 (rvc p17 p6637 (rvc p131 p6581 (rvc p661 p6317 (rvc p239 p6529 (rvc p401 p6449 (rvc p139 p6581 (rvc p401 p6451 (rvc p67 p6619 (rvc p109 p6599 (rvc p3 p6653 (rvc p173 p6569 (rvc p1291 p6011 (rvc p173 p6571 (rvc p43 p6637 (rvc p13 p6653 (rvc p3 p6659 (rvc p17 p6653 (rvc p3 p6661 (rvc p173 p6577 (rvc p131 p6599 (rvc p13 p6659 (rvc p239 p6547 (rvc p17 p6659 (rvc p139 p6599 (rvc p17 p6661 (rvc p67 p6637 (rvc p1549 p5897 (rvc p131 p6607 (rvc p109 p6619 (rvc p3 p6673 (rvc p29 p6661 (rvc p139 p6607 (rvc p1549 p5903 (rvc p83 p6637 (rvc p13 p6673 (rvc p3 p6679 (rvc p17 p6673 (rvc p239 p6563 (rvc p661 p6353 (rvc p131 p6619 (rvc p13 p6679 (rvc p67 p6653 (rvc p17 p6679 (rvc p139 p6619 (rvc p337 p6521 (rvc p3 p6689 (rvc p109 p6637 (rvc p3 p6691 (rvc p173 p6607 (rvc p67 p6661 (rvc p13 p6689 (rvc p239 p6577 (rvc p17 p6689 (rvc p1291 p6053 (rvc p17 p6691 (rvc p239 p6581 (rvc p1549 p5927 (rvc p3 p6701 (rvc p661 p6373 (rvc p3 p6703 (rvc p173 p6619 (rvc p67 p6673 (rvc p109 p6653 (rvc p1151 p6133 (rvc p17 p6701 (rvc p3 p6709 (rvc p17 p6703 (rvc p67 p6679 (rvc p109 p6659 (rvc p107 p6661 (rvc p109 p6661 (rvc p487 p6473 (rvc p17 p6709 (rvc p131 p6653 (rvc p337 p6551 (rvc p3 p6719 (rvc p401 p6521 (rvc p67 p6689 (rvc p173 p6637 (rvc p67 p6691 (rvc p13 p6719 (rvc p131 p6661 (rvc p17 p6719 (rvc p139 p6659 (rvc p401 p6529 (rvc p139 p6661 (rvc p337 p6563 (rvc p107 p6679 (rvc p109 p6679 (rvc p3 p6733 (rvc p53 p6709 (rvc p67 p6703 (rvc p337 p6569 (rvc p3 p6737 (rvc p13 p6733 (rvc p43 p6719 (rvc p17 p6733 (rvc p67 p6709 (rvc p109 p6689 (rvc p131 p6679 (rvc p17 p6737 (rvc p1291 p6101 (rvc p401 p6547 (rvc p139 p6679 (rvc p337 p6581 (rvc p83 p6709 (rvc p401 p6551 (rvc p67 p6719 (rvc p401 p6553 (rvc p131 p6689 (rvc p109 p6701 (rvc p131 p6691 (rvc p109 p6703 (rvc p139 p6689 (rvc p173 p6673 (rvc p139 p6691 (rvc p1549 p5987 (rvc p3 p6761 (rvc p109 p6709 (rvc p3 p6763 (rvc p173 p6679 (rvc p67 p6733 (rvc p13 p6761 (rvc p131 p6703 (rvc p17 p6761 (rvc p67 p6737 (rvc p17 p6763 (rvc p139 p6703 (rvc p109 p6719 (rvc p131 p6709 (rvc p337 p6607 (rvc p1291 p6131 (rvc p401 p6577 (rvc p139 p6709 (rvc p661 p6449 (rvc p3 p6779 (rvc p401 p6581 (rvc p3 p6781 (rvc p1553 p6007 (rvc p131 p6719 (rvc p13 p6779 (rvc p107 p6733 (rvc p17 p6779 (rvc p139 p6719 (rvc p17 p6781 (rvc p107 p6737 (rvc p109 p6737 (rvc p3 p6791 (rvc p29 p6779 (rvc p3 p6793 (rvc p173 p6709 (rvc p67 p6763 (rvc p13 p6791 (rvc p131 p6733 (rvc p17 p6791 (rvc p43 p6779 (rvc p17 p6793 (rvc p131 p6737 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl12807 (m : ℕ) (hl : 12807 ≤ m) (hh : m ≤ 13606) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-12807)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 12807+2*k := by simp [k]; omega
  have hk : k < ql12807.length := by simp [k,ql12807]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl12807 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql13607 : List ℕ := [6473,6803,6637,6737,6607,6689,6803,6691,6803,6779,6037,6781,6761,6763,6763,6173,6619,6701,6653,6703,6737,6823,6007,6793,6659,6827,6823,6829,6823,6763,6779,6833,6827,6803,6829,6719,6833,6121,6833,6841,6829,6779,6791,6781,6793,6779,6841,6781,6521,6733,6653,6833,6841,6823,6803,6857,6659,6827,6661,6829,6857,6863,6857,6833,6781,6803,6863,6869,6863,6871,6673,6841,6869,6823,6869,6857,6871,6761,6827,6763,6829,6883,6871,6833,6833,6823,6689,6857,6883,6827,6563,6829,6841,6863,6883,6833,6569,6899,6701,6869,6703,6871,6899,6841,6899,6907,6709,6841,6857,6911,6907,6269,6907,6883,6863,6917,6911,6899,6907,6857,6869,6871,6917,6857,6841,6863,6761,6211,6763,6899,6733,6869,6857,6871,6883,6869,6121,6907,6863,6823,6857,6911,6871,6827,6779,6947,6781,6949,6133,6883,6899,6379,6947,6311,6949,6917,6791,6959,6907,6961,6763,6899,6911,6247,6959,6967,6961,6917,6917,6971,6967,6329,6967,6911,6971,6977,6971,6947,6781,6949,6977,6983,6977,6917,6211,6869,6983,6871,6983,6991,6793,6961,6827,6277,6991,6997,6991,6967,6947,7001,6949,6971,6997,6361,7001,6967,7001,6977,6997,6947,6959,7013,6961,6983,6199,6949,7013,7019,7013,7001,6823,6991,6971,6961,7019,7027,6829,6997,6977,6967,6833,7001,7027,6971,6983,6997,6871,7039,6841,6977,6269,7043,6991,7013,7039,6983,7043,6997,7043,7019,6967,7001,7001,6991,6857,7057,4951,7027,6287,6997,6863,7043,7057,7001,7013,6949,6869,7069,6871,7039,7019,6961,7069,7043,7069,7013,6911,7079,7027,7013,6883,7019,7079,6967,7079,7019,6271,7057,6761,7027,7039,6449,6277,7027,7043,6379,6899,7079,4993,7069,6329,7103,7019,6857,6907,7043,7103,7109,7103,7079,7027,6469,7109,6997,7109,6473,6301,7001,6791,7121,7069,7103,7039,7057,7121,7127,7121,7129,5023,7013,7079,7069,7127,7103,7129,7069,6971,6421,7127,7109,7057,7079,6977,7027,6947,7079,6949,7129,6983,7151,6823,7121,7069,7103,7103,7039,7151,7159,6961,7129,7109,5281,7159,6521,7159,7103,7001,6451,6971,7103,7159,7109,7121,7057,6977,7177,6361,7127,7127,7129,7129,7151,7177,7121,7019,7187,7103,7121,6991,7159,7187,7193,7187,7127,6997,7129,7193,6481,7193,6959]
private theorem vl13607 : rvld 2 13607 ql13607 := by
  unfold ql13607
  exact rvc p661 p6473 (rvc p3 p6803 (rvc p337 p6637 (rvc p139 p6737 (rvc p401 p6607 (rvc p239 p6689 (rvc p13 p6803 (rvc p239 p6691 (rvc p17 p6803 (rvc p67 p6779 (rvc p1553 p6037 (rvc p67 p6781 (rvc p109 p6761 (rvc p107 p6763 (rvc p109 p6763 (rvc p1291 p6173 (rvc p401 p6619 (rvc p239 p6701 (rvc p337 p6653 (rvc p239 p6703 (rvc p173 p6737 (rvc p3 p6823 (rvc p1637 p6007 (rvc p67 p6793 (rvc p337 p6659 (rvc p3 p6827 (rvc p13 p6823 (rvc p3 p6829 (rvc p17 p6823 (rvc p139 p6763 (rvc p109 p6779 (rvc p3 p6833 (rvc p17 p6827 (rvc p67 p6803 (rvc p17 p6829 (rvc p239 p6719 (rvc p13 p6833 (rvc p1439 p6121 (rvc p17 p6833 (rvc p3 p6841 (rvc p29 p6829 (rvc p131 p6779 (rvc p109 p6791 (rvc p131 p6781 (rvc p109 p6793 (rvc p139 p6779 (rvc p17 p6841 (rvc p139 p6781 (rvc p661 p6521 (rvc p239 p6733 (rvc p401 p6653 (rvc p43 p6833 (rvc p29 p6841 (rvc p67 p6823 (rvc p109 p6803 (rvc p3 p6857 (rvc p401 p6659 (rvc p67 p6827 (rvc p401 p6661 (rvc p67 p6829 (rvc p13 p6857 (rvc p3 p6863 (rvc p17 p6857 (rvc p67 p6833 (rvc p173 p6781 (rvc p131 p6803 (rvc p13 p6863 (rvc p3 p6869 (rvc p17 p6863 (rvc p3 p6871 (rvc p401 p6673 (rvc p67 p6841 (rvc p13 p6869 (rvc p107 p6823 (rvc p17 p6869 (rvc p43 p6857 (rvc p17 p6871 (rvc p239 p6761 (rvc p109 p6827 (rvc p239 p6763 (rvc p109 p6829 (rvc p3 p6883 (rvc p29 p6871 (rvc p107 p6833 (rvc p109 p6833 (rvc p131 p6823 (rvc p401 p6689 (rvc p67 p6857 (rvc p17 p6883 (rvc p131 p6827 (rvc p661 p6563 (rvc p131 p6829 (rvc p109 p6841 (rvc p67 p6863 (rvc p29 p6883 (rvc p131 p6833 (rvc p661 p6569 (rvc p3 p6899 (rvc p401 p6701 (rvc p67 p6869 (rvc p401 p6703 (rvc p67 p6871 (rvc p13 p6899 (rvc p131 p6841 (rvc p17 p6899 (rvc p3 p6907 (rvc p401 p6709 (rvc p139 p6841 (rvc p109 p6857 (rvc p3 p6911 (rvc p13 p6907 (rvc p1291 p6269 (rvc p17 p6907 (rvc p67 p6883 (rvc p109 p6863 (rvc p3 p6917 (rvc p17 p6911 (rvc p43 p6899 (rvc p29 p6907 (rvc p131 p6857 (rvc p109 p6869 (rvc p107 p6871 (rvc p17 p6917 (rvc p139 p6857 (rvc p173 p6841 (rvc p131 p6863 (rvc p337 p6761 (rvc p1439 p6211 (rvc p337 p6763 (rvc p67 p6899 (rvc p401 p6733 (rvc p131 p6869 (rvc p157 p6857 (rvc p131 p6871 (rvc p109 p6883 (rvc p139 p6869 (rvc p1637 p6121 (rvc p67 p6907 (rvc p157 p6863 (rvc p239 p6823 (rvc p173 p6857 (rvc p67 p6911 (rvc p149 p6871 (rvc p239 p6827 (rvc p337 p6779 (rvc p3 p6947 (rvc p337 p6781 (rvc p3 p6949 (rvc p1637 p6133 (rvc p139 p6883 (rvc p109 p6899 (rvc p1151 p6379 (rvc p17 p6947 (rvc p1291 p6311 (rvc p17 p6949 (rvc p83 p6917 (rvc p337 p6791 (rvc p3 p6959 (rvc p109 p6907 (rvc p3 p6961 (rvc p401 p6763 (rvc p131 p6899 (rvc p109 p6911 (rvc p1439 p6247 (rvc p17 p6959 (rvc p3 p6967 (rvc p17 p6961 (rvc p107 p6917 (rvc p109 p6917 (rvc p3 p6971 (rvc p13 p6967 (rvc p1291 p6329 (rvc p17 p6967 (rvc p131 p6911 (rvc p13 p6971 (rvc p3 p6977 (rvc p17 p6971 (rvc p67 p6947 (rvc p401 p6781 (rvc p67 p6949 (rvc p13 p6977 (rvc p3 p6983 (rvc p17 p6977 (rvc p139 p6917 (rvc p1553 p6211 (rvc p239 p6869 (rvc p13 p6983 (rvc p239 p6871 (rvc p17 p6983 (rvc p3 p6991 (rvc p401 p6793 (rvc p67 p6961 (rvc p337 p6827 (rvc p1439 p6277 (rvc p13 p6991 (rvc p3 p6997 (rvc p17 p6991 (rvc p67 p6967 (rvc p109 p6947 (rvc p3 p7001 (rvc p109 p6949 (rvc p67 p6971 (rvc p17 p6997 (rvc p1291 p6361 (rvc p13 p7001 (rvc p83 p6967 (rvc p17 p7001 (rvc p67 p6977 (rvc p29 p6997 (rvc p131 p6947 (rvc p109 p6959 (rvc p3 p7013 (rvc p109 p6961 (rvc p67 p6983 (rvc p1637 p6199 (rvc p139 p6949 (rvc p13 p7013 (rvc p3 p7019 (rvc p17 p7013 (rvc p43 p7001 (rvc p401 p6823 (rvc p67 p6991 (rvc p109 p6971 (rvc p131 p6961 (rvc p17 p7019 (rvc p3 p7027 (rvc p401 p6829 (rvc p67 p6997 (rvc p109 p6977 (rvc p131 p6967 (rvc p401 p6833 (rvc p67 p7001 (rvc p17 p7027 (rvc p131 p6971 (rvc p109 p6983 (rvc p83 p6997 (rvc p337 p6871 (rvc p3 p7039 (rvc p401 p6841 (rvc p131 p6977 (rvc p1549 p6269 (rvc p3 p7043 (rvc p109 p6991 (rvc p67 p7013 (rvc p17 p7039 (rvc p131 p6983 (rvc p13 p7043 (rvc p107 p6997 (rvc p17 p7043 (rvc p67 p7019 (rvc p173 p6967 (rvc p107 p7001 (rvc p109 p7001 (rvc p131 p6991 (rvc p401 p6857 (rvc p3 p7057 (rvc p4217 p4951 (rvc p67 p7027 (rvc p1549 p6287 (rvc p131 p6997 (rvc p401 p6863 (rvc p43 p7043 (rvc p17 p7057 (rvc p131 p7001 (rvc p109 p7013 (rvc p239 p6949 (rvc p401 p6869 (rvc p3 p7069 (rvc p401 p6871 (rvc p67 p7039 (rvc p109 p7019 (rvc p227 p6961 (rvc p13 p7069 (rvc p67 p7043 (rvc p17 p7069 (rvc p131 p7013 (rvc p337 p6911 (rvc p3 p7079 (rvc p109 p7027 (rvc p139 p7013 (rvc p401 p6883 (rvc p131 p7019 (rvc p13 p7079 (rvc p239 p6967 (rvc p17 p7079 (rvc p139 p7019 (rvc p1637 p6271 (rvc p67 p7057 (rvc p661 p6761 (rvc p131 p7027 (rvc p109 p7039 (rvc p1291 p6449 (rvc p1637 p6277 (rvc p139 p7027 (rvc p109 p7043 (rvc p1439 p6379 (rvc p401 p6899 (rvc p43 p7079 (rvc p4217 p4993 (rvc p67 p7069 (rvc p1549 p6329 (rvc p3 p7103 (rvc p173 p7019 (rvc p499 p6857 (rvc p401 p6907 (rvc p131 p7043 (rvc p13 p7103 (rvc p3 p7109 (rvc p17 p7103 (rvc p67 p7079 (rvc p173 p7027 (rvc p1291 p6469 (rvc p13 p7109 (rvc p239 p6997 (rvc p17 p7109 (rvc p1291 p6473 (rvc p1637 p6301 (rvc p239 p7001 (rvc p661 p6791 (rvc p3 p7121 (rvc p109 p7069 (rvc p43 p7103 (rvc p173 p7039 (rvc p139 p7057 (rvc p13 p7121 (rvc p3 p7127 (rvc p17 p7121 (rvc p3 p7129 (rvc p4217 p5023 (rvc p239 p7013 (rvc p109 p7079 (rvc p131 p7069 (rvc p17 p7127 (rvc p67 p7103 (rvc p17 p7129 (rvc p139 p7069 (rvc p337 p6971 (rvc p1439 p6421 (rvc p29 p7127 (rvc p67 p7109 (rvc p173 p7057 (rvc p131 p7079 (rvc p337 p6977 (rvc p239 p7027 (rvc p401 p6947 (rvc p139 p7079 (rvc p401 p6949 (rvc p43 p7129 (rvc p337 p6983 (rvc p3 p7151 (rvc p661 p6823 (rvc p67 p7121 (rvc p173 p7069 (rvc p107 p7103 (rvc p109 p7103 (rvc p239 p7039 (rvc p17 p7151 (rvc p3 p7159 (rvc p401 p6961 (rvc p67 p7129 (rvc p109 p7109 (rvc p3767 p5281 (rvc p13 p7159 (rvc p1291 p6521 (rvc p17 p7159 (rvc p131 p7103 (rvc p337 p7001 (rvc p1439 p6451 (rvc p401 p6971 (rvc p139 p7103 (rvc p29 p7159 (rvc p131 p7109 (rvc p109 p7121 (rvc p239 p7057 (rvc p401 p6977 (rvc p3 p7177 (rvc p1637 p6361 (rvc p107 p7127 (rvc p109 p7127 (rvc p107 p7129 (rvc p109 p7129 (rvc p67 p7151 (rvc p17 p7177 (rvc p131 p7121 (rvc p337 p7019 (rvc p3 p7187 (rvc p173 p7103 (rvc p139 p7121 (rvc p401 p6991 (rvc p67 p7159 (rvc p13 p7187 (rvc p3 p7193 (rvc p17 p7187 (rvc p139 p7127 (rvc p401 p6997 (rvc p139 p7129 (rvc p13 p7193 (rvc p1439 p6481 (rvc p17 p7193 (rvc p487 p6959 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl13607 (m : ℕ) (hl : 13607 ≤ m) (hh : m ≤ 14406) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-13607)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 13607+2*k := by simp [k]; omega
  have hk : k < ql13607.length := by simp [k,ql13607]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl13607 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql14407 : List ℕ := [6427,7151,7151,5323,7039,7207,5101,7177,7043,7211,7159,7213,7207,7151,7211,7177,7211,7219,7213,7103,6449,7159,7219,7193,7219,7159,6899,7229,7177,7211,7219,7213,7229,6661,7229,7237,7039,7207,7187,7177,7043,7243,7237,7213,7193,7247,7243,7229,7243,7219,7247,7253,7247,7187,7057,7193,7253,7207,7253,7229,7177,7211,7211,7213,7213,7247,7069,7237,7103,7207,7219,7253,5167,7243,7109,7213,7079,7247,7057,7213,7229,7283,7207,7253,6469,7219,7283,7237,7283,7043,7207,7229,7127,7177,7243,7297,7213,7247,7247,7237,7103,7283,7297,7237,7253,7307,7109,7309,7297,7247,7307,5431,7307,7283,7309,7253,7151,5437,7121,7321,7237,6679,6551,7207,7127,7307,7321,7297,7001,7331,7247,7333,7321,7283,7283,7219,7331,7307,7333,7309,7013,3943,7177,6701,7333,7283,7019,7349,7297,7351,6577,7321,7349,7237,7349,7109,7351,7307,7307,7297,7309,7331,7351,7333,7349,6793,7283,7369,6553,7307,7043,7309,7321,7307,7369,7309,7211,6661,7213,7349,7297,7351,7331,7321,7333,7283,6571,7321,6521,6673,7193,7393,7309,7331,7229,7333,7393,7331,7393,7369,7349,7351,7351,6761,7207,6763,7079,6691,7211,7411,7213,7349,7247,7351,7411,7417,7411,7351,7253,7369,7369,6779,7417,7393,6653,7309,7229,7187,7417,7411,7103,7433,7349,6791,7237,7369,7433,7321,7433,7193,7243,7411,7019,7393,7393,6803,6673,7417,7283,7451,7253,7433,7369,6737,7451,7457,7451,7459,7237,7393,7457,7411,7457,7433,7459,7349,6599,7351,7417,7451,7459,6829,7307,7411,7309,7477,7393,7411,7151,7481,7283,7451,7477,7417,7433,7487,7481,7489,7477,7459,7487,4093,7487,7247,7489,7433,7331,7499,7333,7433,7417,7451,7451,5623,7499,7507,7309,7477,7457,7393,7459,7481,7507,7451,7349,7517,7351,7487,7321,7489,7517,7523,7517,7457,6709,7459,7523,7529,7523,7499,7333,7481,7481,7417,7529,7537,6763,7507,7487,7541,7489,7523,7537,7481,7541,7547,7541,7549,7351,7487,7499,7489,7547,7523,7549,7489,7229,7559,7507,7561,7477,7499,7559,5683,7559,7499,7561,7537,7517,7507,7487,7573,7489,7507,7523,7577,7573,7547,7573,7549,7529,7583,7577,7517,7573,7523,7583,7589,7583,7591,7393,7561,7541,7477,7589,7529,7591,7481,7547,7537]
private theorem vl14407 : rvld 2 14407 ql14407 := by
  unfold ql14407
  exact rvc p1553 p6427 (rvc p107 p7151 (rvc p109 p7151 (rvc p3767 p5323 (rvc p337 p7039 (rvc p3 p7207 (rvc p4217 p5101 (rvc p67 p7177 (rvc p337 p7043 (rvc p3 p7211 (rvc p109 p7159 (rvc p3 p7213 (rvc p17 p7207 (rvc p131 p7151 (rvc p13 p7211 (rvc p83 p7177 (rvc p17 p7211 (rvc p3 p7219 (rvc p17 p7213 (rvc p239 p7103 (rvc p1549 p6449 (rvc p131 p7159 (rvc p13 p7219 (rvc p67 p7193 (rvc p17 p7219 (rvc p139 p7159 (rvc p661 p6899 (rvc p3 p7229 (rvc p109 p7177 (rvc p43 p7211 (rvc p29 p7219 (rvc p43 p7213 (rvc p13 p7229 (rvc p1151 p6661 (rvc p17 p7229 (rvc p3 p7237 (rvc p401 p7039 (rvc p67 p7207 (rvc p109 p7187 (rvc p131 p7177 (rvc p401 p7043 (rvc p3 p7243 (rvc p17 p7237 (rvc p67 p7213 (rvc p109 p7193 (rvc p3 p7247 (rvc p13 p7243 (rvc p43 p7229 (rvc p17 p7243 (rvc p67 p7219 (rvc p13 p7247 (rvc p3 p7253 (rvc p17 p7247 (rvc p139 p7187 (rvc p401 p7057 (rvc p131 p7193 (rvc p13 p7253 (rvc p107 p7207 (rvc p17 p7253 (rvc p67 p7229 (rvc p173 p7177 (rvc p107 p7211 (rvc p109 p7211 (rvc p107 p7213 (rvc p109 p7213 (rvc p43 p7247 (rvc p401 p7069 (rvc p67 p7237 (rvc p337 p7103 (rvc p131 p7207 (rvc p109 p7219 (rvc p43 p7253 (rvc p4217 p5167 (rvc p67 p7243 (rvc p337 p7109 (rvc p131 p7213 (rvc p401 p7079 (rvc p67 p7247 (rvc p449 p7057 (rvc p139 p7213 (rvc p109 p7229 (rvc p3 p7283 (rvc p157 p7207 (rvc p67 p7253 (rvc p1637 p6469 (rvc p139 p7219 (rvc p13 p7283 (rvc p107 p7237 (rvc p17 p7283 (rvc p499 p7043 (rvc p173 p7207 (rvc p131 p7229 (rvc p337 p7127 (rvc p239 p7177 (rvc p109 p7243 (rvc p3 p7297 (rvc p173 p7213 (rvc p107 p7247 (rvc p109 p7247 (rvc p131 p7237 (rvc p401 p7103 (rvc p43 p7283 (rvc p17 p7297 (rvc p139 p7237 (rvc p109 p7253 (rvc p3 p7307 (rvc p401 p7109 (rvc p3 p7309 (rvc p29 p7297 (rvc p131 p7247 (rvc p13 p7307 (rvc p3767 p5431 (rvc p17 p7307 (rvc p67 p7283 (rvc p17 p7309 (rvc p131 p7253 (rvc p337 p7151 (rvc p3767 p5437 (rvc p401 p7121 (rvc p3 p7321 (rvc p173 p7237 (rvc p1291 p6679 (rvc p1549 p6551 (rvc p239 p7207 (rvc p401 p7127 (rvc p43 p7307 (rvc p17 p7321 (rvc p67 p7297 (rvc p661 p7001 (rvc p3 p7331 (rvc p173 p7247 (rvc p3 p7333 (rvc p29 p7321 (rvc p107 p7283 (rvc p109 p7283 (rvc p239 p7219 (rvc p17 p7331 (rvc p67 p7307 (rvc p17 p7333 (rvc p67 p7309 (rvc p661 p7013 (rvc p6803 p3943 (rvc p337 p7177 (rvc p1291 p6701 (rvc p29 p7333 (rvc p131 p7283 (rvc p661 p7019 (rvc p3 p7349 (rvc p109 p7297 (rvc p3 p7351 (rvc p1553 p6577 (rvc p67 p7321 (rvc p13 p7349 (rvc p239 p7237 (rvc p17 p7349 (rvc p499 p7109 (rvc p17 p7351 (rvc p107 p7307 (rvc p109 p7307 (rvc p131 p7297 (rvc p109 p7309 (rvc p67 p7331 (rvc p29 p7351 (rvc p67 p7333 (rvc p37 p7349 (rvc p1151 p6793 (rvc p173 p7283 (rvc p3 p7369 (rvc p1637 p6553 (rvc p131 p7307 (rvc p661 p7043 (rvc p131 p7309 (rvc p109 p7321 (rvc p139 p7307 (rvc p17 p7369 (rvc p139 p7309 (rvc p337 p7211 (rvc p1439 p6661 (rvc p337 p7213 (rvc p67 p7349 (rvc p173 p7297 (rvc p67 p7351 (rvc p109 p7331 (rvc p131 p7321 (rvc p109 p7333 (rvc p211 p7283 (rvc p1637 p6571 (rvc p139 p7321 (rvc p1741 p6521 (rvc p1439 p6673 (rvc p401 p7193 (rvc p3 p7393 (rvc p173 p7309 (rvc p131 p7331 (rvc p337 p7229 (rvc p131 p7333 (rvc p13 p7393 (rvc p139 p7331 (rvc p17 p7393 (rvc p67 p7369 (rvc p109 p7349 (rvc p107 p7351 (rvc p109 p7351 (rvc p1291 p6761 (rvc p401 p7207 (rvc p1291 p6763 (rvc p661 p7079 (rvc p1439 p6691 (rvc p401 p7211 (rvc p3 p7411 (rvc p401 p7213 (rvc p131 p7349 (rvc p337 p7247 (rvc p131 p7351 (rvc p13 p7411 (rvc p3 p7417 (rvc p17 p7411 (rvc p139 p7351 (rvc p337 p7253 (rvc p107 p7369 (rvc p109 p7369 (rvc p1291 p6779 (rvc p17 p7417 (rvc p67 p7393 (rvc p1549 p6653 (rvc p239 p7309 (rvc p401 p7229 (rvc p487 p7187 (rvc p29 p7417 (rvc p43 p7411 (rvc p661 p7103 (rvc p3 p7433 (rvc p173 p7349 (rvc p1291 p6791 (rvc p401 p7237 (rvc p139 p7369 (rvc p13 p7433 (rvc p239 p7321 (rvc p17 p7433 (rvc p499 p7193 (rvc p401 p7243 (rvc p67 p7411 (rvc p853 p7019 (rvc p107 p7393 (rvc p109 p7393 (rvc p1291 p6803 (rvc p1553 p6673 (rvc p67 p7417 (rvc p337 p7283 (rvc p3 p7451 (rvc p401 p7253 (rvc p43 p7433 (rvc p173 p7369 (rvc p1439 p6737 (rvc p13 p7451 (rvc p3 p7457 (rvc p17 p7451 (rvc p3 p7459 (rvc p449 p7237 (rvc p139 p7393 (rvc p13 p7457 (rvc p107 p7411 (rvc p17 p7457 (rvc p67 p7433 (rvc p17 p7459 (rvc p239 p7349 (rvc p1741 p6599 (rvc p239 p7351 (rvc p109 p7417 (rvc p43 p7451 (rvc p29 p7459 (rvc p1291 p6829 (rvc p337 p7307 (rvc p131 p7411 (rvc p337 p7309 (rvc p3 p7477 (rvc p173 p7393 (rvc p139 p7411 (rvc p661 p7151 (rvc p3 p7481 (rvc p401 p7283 (rvc p67 p7451 (rvc p17 p7477 (rvc p139 p7417 (rvc p109 p7433 (rvc p3 p7487 (rvc p17 p7481 (rvc p3 p7489 (rvc p29 p7477 (rvc p67 p7459 (rvc p13 p7487 (rvc p6803 p4093 (rvc p17 p7487 (rvc p499 p7247 (rvc p17 p7489 (rvc p131 p7433 (rvc p337 p7331 (rvc p3 p7499 (rvc p337 p7333 (rvc p139 p7433 (rvc p173 p7417 (rvc p107 p7451 (rvc p109 p7451 (rvc p3767 p5623 (rvc p17 p7499 (rvc p3 p7507 (rvc p401 p7309 (rvc p67 p7477 (rvc p109 p7457 (rvc p239 p7393 (rvc p109 p7459 (rvc p67 p7481 (rvc p17 p7507 (rvc p131 p7451 (rvc p337 p7349 (rvc p3 p7517 (rvc p337 p7351 (rvc p67 p7487 (rvc p401 p7321 (rvc p67 p7489 (rvc p13 p7517 (rvc p3 p7523 (rvc p17 p7517 (rvc p139 p7457 (rvc p1637 p6709 (rvc p139 p7459 (rvc p13 p7523 (rvc p3 p7529 (rvc p17 p7523 (rvc p67 p7499 (rvc p401 p7333 (rvc p107 p7481 (rvc p109 p7481 (rvc p239 p7417 (rvc p17 p7529 (rvc p3 p7537 (rvc p1553 p6763 (rvc p67 p7507 (rvc p109 p7487 (rvc p3 p7541 (rvc p109 p7489 (rvc p43 p7523 (rvc p17 p7537 (rvc p131 p7481 (rvc p13 p7541 (rvc p3 p7547 (rvc p17 p7541 (rvc p3 p7549 (rvc p401 p7351 (rvc p131 p7487 (rvc p109 p7499 (rvc p131 p7489 (rvc p17 p7547 (rvc p67 p7523 (rvc p17 p7549 (rvc p139 p7489 (rvc p661 p7229 (rvc p3 p7559 (rvc p109 p7507 (rvc p3 p7561 (rvc p173 p7477 (rvc p131 p7499 (rvc p13 p7559 (rvc p3767 p5683 (rvc p17 p7559 (rvc p139 p7499 (rvc p17 p7561 (rvc p67 p7537 (rvc p109 p7517 (rvc p131 p7507 (rvc p173 p7487 (rvc p3 p7573 (rvc p173 p7489 (rvc p139 p7507 (rvc p109 p7523 (rvc p3 p7577 (rvc p13 p7573 (rvc p67 p7547 (rvc p17 p7573 (rvc p67 p7549 (rvc p109 p7529 (rvc p3 p7583 (rvc p17 p7577 (rvc p139 p7517 (rvc p29 p7573 (rvc p131 p7523 (rvc p13 p7583 (rvc p3 p7589 (rvc p17 p7583 (rvc p3 p7591 (rvc p401 p7393 (rvc p67 p7561 (rvc p109 p7541 (rvc p239 p7477 (rvc p17 p7589 (rvc p139 p7529 (rvc p17 p7591 (rvc p239 p7481 (rvc p109 p7547 (rvc p131 p7537 (True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl14407 (m : ℕ) (hl : 14407 ≤ m) (hh : m ≤ 15206) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-14407)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 14407+2*k := by simp [k]; omega
  have hk : k < ql14407.length := by simp [k,ql14407]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl14407 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private def ql15207 : List ℕ := [7549,7603,7591,7573,6833,7607,7603,7577,7603,7547,7559,7549,7607,7583,7417,7549,7451,5737,7607,7621,7537,7591,7457,7561,7573,7559,7621,7561,7577,7591,7433,7529,7549,7603,7583,7573,7309,7639,6823,7577,7589,7643,7591,7577,7639,7583,7643,7649,7643,7583,7639,7621,7649,7591,7649,7589,7459,7591,7607,7621,7577,7643,5557,7547,7499,7603,7583,7669,5563,7639,6899,7673,7621,7643,7669,7559,7673,7561,7673,7681,7669,7039,7517,7621,7487,7687,7681,7621,7523,7691,7639,7673,7687,7577,7643,4297,7691,7699,7687,7669,7649,7703,7699,7673,7699,7643,7703,7591,7703,7643,7699,7681,7547,6997,7517,7717,7717,7687,6947,7603,7669,7723,7717,7607,7673,7727,7529,7481,7723,7699,7727,7669,7727,7703,7537,7673,6869,7621,7687,7741,6967,7691,7691,7681,7547,7727,7741,7717,7583,7687,7699,7753,7669,7723,7703,7757,7559,7759,7753,7643,7757,7699,7757,7121,7759,7703,6899,7717,7717,7703,7573,7741,7607,7723,7723,7757,6961,7727,7727,7717,7583,7541,7699,7753,7457,7723,7589,7789,7591,7759,7019,7793,7741,7727,7789,7079,7793,7681,7793,7559,7603,7159,7727,7741,7753,7559,7723,7741,7757,7759,7759,7793,6997,7573,7649,7817,7489,7577,7621,7789,7817,7823,7817,7793,7741,7759,7823,7829,7823,7187,7057,7793,7829,7717,7829,7817,7639,7121,7673,7841,7789,7823,7759,7727,7793,7129,7841,7817,5743,7207,7523,7853,7687,7823,7039,7793,7853,7741,7853,7829,7639]
private theorem vl15207 : rvld 2 15207 ql15207 := by
  unfold ql15207
  exact rvc p109 p7549 (rvc p3 p7603 (rvc p29 p7591 (rvc p67 p7573 (rvc p1549 p6833 (rvc p3 p7607 (rvc p13 p7603 (rvc p67 p7577 (rvc p17 p7603 (rvc p131 p7547 (rvc p109 p7559 (rvc p131 p7549 (rvc p17 p7607 (rvc p67 p7583 (rvc p401 p7417 (rvc p139 p7549 (rvc p337 p7451 (rvc p3767 p5737 (rvc p29 p7607 (rvc p3 p7621 (rvc p173 p7537 (rvc p67 p7591 (rvc p337 p7457 (rvc p131 p7561 (rvc p109 p7573 (rvc p139 p7559 (rvc p17 p7621 (rvc p139 p7561 (rvc p109 p7577 (rvc p83 p7591 (rvc p401 p7433 (rvc p211 p7529 (rvc p173 p7549 (rvc p67 p7603 (rvc p109 p7583 (rvc p131 p7573 (rvc p661 p7309 (rvc p3 p7639 (rvc p1637 p6823 (rvc p131 p7577 (rvc p109 p7589 (rvc p3 p7643 (rvc p109 p7591 (rvc p139 p7577 (rvc p17 p7639 (rvc p131 p7583 (rvc p13 p7643 (rvc p3 p7649 (rvc p17 p7643 (rvc p139 p7583 (rvc p29 p7639 (rvc p67 p7621 (rvc p13 p7649 (rvc p131 p7591 (rvc p17 p7649 (rvc p139 p7589 (rvc p401 p7459 (rvc p139 p7591 (rvc p109 p7607 (rvc p83 p7621 (rvc p173 p7577 (rvc p43 p7643 (rvc p4217 p5557 (rvc p239 p7547 (rvc p337 p7499 (rvc p131 p7603 (rvc p173 p7583 (rvc p3 p7669 (rvc p4217 p5563 (rvc p67 p7639 (rvc p1549 p6899 (rvc p3 p7673 (rvc p109 p7621 (rvc p67 p7643 (rvc p17 p7669 (rvc p239 p7559 (rvc p13 p7673 (rvc p239 p7561 (rvc p17 p7673 (rvc p3 p7681 (rvc p29 p7669 (rvc p1291 p7039 (rvc p337 p7517 (rvc p131 p7621 (rvc p401 p7487 (rvc p3 p7687 (rvc p17 p7681 (rvc p139 p7621 (rvc p337 p7523 (rvc p3 p7691 (rvc p109 p7639 (rvc p43 p7673 (rvc p17 p7687 (rvc p239 p7577 (rvc p109 p7643 (rvc p6803 p4297 (rvc p17 p7691 (rvc p3 p7699 (rvc p29 p7687 (rvc p67 p7669 (rvc p109 p7649 (rvc p3 p7703 (rvc p13 p7699 (rvc p67 p7673 (rvc p17 p7699 (rvc p131 p7643 (rvc p13 p7703 (rvc p239 p7591 (rvc p17 p7703 (rvc p139 p7643 (rvc p29 p7699 (rvc p67 p7681 (rvc p337 p7547 (rvc p1439 p6997 (rvc p401 p7517 (rvc p3 p7717 (rvc p5 p7717 (rvc p67 p7687 (rvc p1549 p6947 (rvc p239 p7603 (rvc p109 p7669 (rvc p3 p7723 (rvc p17 p7717 (rvc p239 p7607 (rvc p109 p7673 (rvc p3 p7727 (rvc p401 p7529 (rvc p499 p7481 (rvc p17 p7723 (rvc p67 p7699 (rvc p13 p7727 (rvc p131 p7669 (rvc p17 p7727 (rvc p67 p7703 (rvc p401 p7537 (rvc p131 p7673 (rvc p1741 p6869 (rvc p239 p7621 (rvc p109 p7687 (rvc p3 p7741 (rvc p1553 p6967 (rvc p107 p7691 (rvc p109 p7691 (rvc p131 p7681 (rvc p401 p7547 (rvc p43 p7727 (rvc p17 p7741 (rvc p67 p7717 (rvc p337 p7583 (rvc p131 p7687 (rvc p109 p7699 (rvc p3 p7753 (rvc p173 p7669 (rvc p67 p7723 (rvc p109 p7703 (rvc p3 p7757 (rvc p401 p7559 (rvc p3 p7759 (rvc p17 p7753 (rvc p239 p7643 (rvc p13 p7757 (rvc p131 p7699 (rvc p17 p7757 (rvc p1291 p7121 (rvc p17 p7759 (rvc p131 p7703 (rvc p1741 p6899 (rvc p107 p7717 (rvc p109 p7717 (rvc p139 p7703 (rvc p401 p7573 (rvc p67 p7741 (rvc p337 p7607 (rvc p107 p7723 (rvc p109 p7723 (rvc p43 p7757 (rvc p1637 p6961 (rvc p107 p7727 (rvc p109 p7727 (rvc p131 p7717 (rvc p401 p7583 (rvc p487 p7541 (rvc p173 p7699 (rvc p67 p7753 (rvc p661 p7457 (rvc p131 p7723 (rvc p401 p7589 (rvc p3 p7789 (rvc p401 p7591 (rvc p67 p7759 (rvc p1549 p7019 (rvc p3 p7793 (rvc p109 p7741 (rvc p139 p7727 (rvc p17 p7789 (rvc p1439 p7079 (rvc p13 p7793 (rvc p239 p7681 (rvc p17 p7793 (rvc p487 p7559 (rvc p401 p7603 (rvc p1291 p7159 (rvc p157 p7727 (rvc p131 p7741 (rvc p109 p7753 (rvc p499 p7559 (rvc p173 p7723 (rvc p139 p7741 (rvc p109 p7757 (rvc p107 p7759 (rvc p109 p7759 (rvc p43 p7793 (rvc p1637 p6997 (rvc p487 p7573 (rvc p337 p7649 (rvc p3 p7817 (rvc p661 p7489 (rvc p487 p7577 (rvc p401 p7621 (rvc p67 p7789 (rvc p13 p7817 (rvc p3 p7823 (rvc p17 p7817 (rvc p67 p7793 (rvc p173 p7741 (rvc p139 p7759 (rvc p13 p7823 (rvc p3 p7829 (rvc p17 p7823 (rvc p1291 p7187 (rvc p1553 p7057 (rvc p83 p7793 (rvc p13 p7829 (rvc p239 p7717 (rvc p17 p7829 (rvc p43 p7817 (rvc p401 p7639 (rvc p1439 p7121 (rvc p337 p7673 (rvc p3 p7841 (rvc p109 p7789 (rvc p43 p7823 (rvc p173 p7759 (rvc p239 p7727 (rvc p109 p7793 (rvc p1439 p7129 (rvc p17 p7841 (rvc p67 p7817 (rvc p4217 p5743 (rvc p1291 p7207 (rvc p661 p7523 (rvc p3 p7853 (rvc p337 p7687 (rvc p67 p7823 (rvc p1637 p7039 (rvc p131 p7793 (rvc p13 p7853 (rvc p239 p7741 (rvc p17 p7853 (rvc p67 p7829 (rvc p449 p7639 (True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem xl15207 (m : ℕ) (hl : 15207 ≤ m) (hh : m ≤ 15727) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  let k := (m-15207)/2
  have hm : m % 2 = 1 := Nat.odd_iff.mp he
  have heq : m = 15207+2*k := by simp [k]; omega
  have hk : k < ql15207.length := by simp [k,ql15207]; omega
  obtain ⟨q,hp,hq,hs⟩ := rvld_ex vl15207 hk
  rw [← heq] at hp hs
  exact ⟨q, by simp; have := hp.two_le; omega, hp, hq, hs⟩

private theorem lemoine_bounded (m : ℕ) (hl : 7 ≤ m) (hh : m ≤ 15727) (he : Odd m) :
    ∃ q ∈ Finset.range (m+1), (m-2*q).Prime ∧ q.Prime ∧ m=(m-2*q)+2*q := by
  by_cases h : m ≤ 806
  · exact xl7 m (by omega) h he
  by_cases h : m ≤ 1606
  · exact xl807 m (by omega) h he
  by_cases h : m ≤ 2406
  · exact xl1607 m (by omega) h he
  by_cases h : m ≤ 3206
  · exact xl2407 m (by omega) h he
  by_cases h : m ≤ 4006
  · exact xl3207 m (by omega) h he
  by_cases h : m ≤ 4806
  · exact xl4007 m (by omega) h he
  by_cases h : m ≤ 5606
  · exact xl4807 m (by omega) h he
  by_cases h : m ≤ 6406
  · exact xl5607 m (by omega) h he
  by_cases h : m ≤ 7206
  · exact xl6407 m (by omega) h he
  by_cases h : m ≤ 8006
  · exact xl7207 m (by omega) h he
  by_cases h : m ≤ 8806
  · exact xl8007 m (by omega) h he
  by_cases h : m ≤ 9606
  · exact xl8807 m (by omega) h he
  by_cases h : m ≤ 10406
  · exact xl9607 m (by omega) h he
  by_cases h : m ≤ 11206
  · exact xl10407 m (by omega) h he
  by_cases h : m ≤ 12006
  · exact xl11207 m (by omega) h he
  by_cases h : m ≤ 12806
  · exact xl12007 m (by omega) h he
  by_cases h : m ≤ 13606
  · exact xl12807 m (by omega) h he
  by_cases h : m ≤ 14406
  · exact xl13607 m (by omega) h he
  by_cases h : m ≤ 15206
  · exact xl14407 m (by omega) h he
  exact xl15207 m (by omega) hh he

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture :=
  by
  intro hcore
  constructor
  · intro n hn he
    by_cases hsmall : n ≤ 8012
    · obtain ⟨q, _, hp, hq, heq⟩ := goldbach_bounded n hn hsmall he
      simpa using (show ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p+q from ⟨n-q,q, by simpa using hp,hq,by simpa using heq⟩)
    · have hmod : n % 2 = 0 := Nat.even_iff.mp he
      have hpos := hcore n (Or.inl ⟨he, by omega⟩)
      rw [A219055] at hpos
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_range] at hq
      rcases hq with ⟨hqn, hi, hqp, hq6p, hp, hp6⟩
      simp [hmod] at hi hp hp6
      exact ⟨n - q, q, hp, hqp, by omega⟩
  constructor
  · intro n hn ho
    by_cases hsmall : n ≤ 15727
    · obtain ⟨q, _, hp, hq, heq⟩ := lemoine_bounded n hn hsmall ho
      exact ⟨n - 2 * q, q, hp, hq, heq⟩
    · have hmod : n % 2 = 1 := Nat.odd_iff.mp ho
      have hpos := hcore n (Or.inr ⟨ho, by omega⟩)
      rw [A219055] at hpos
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_range] at hq
      rcases hq with ⟨hqn, hi, hqp, hq6p, hp, hp6⟩
      simp [hmod] at hi hp hp6
      exact ⟨n - 2 * q, q, hp, hqp, by omega⟩
  · apply Set.infinite_of_forall_exists_gt
    intro B
    let n := 2 * (B + 8014)
    have he : Even n := ⟨B + 8014, by simp [n, two_mul]⟩
    have hn : 8012 < n := by simp [n]; omega
    have hmod : n % 2 = 0 := Nat.even_iff.mp he
    have hpos := hcore n (Or.inl ⟨he, hn⟩)
    rw [A219055] at hpos
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    rcases hq with ⟨hqn, hi, hqp, hq6p, hp, hp6⟩
    simp [hmod] at hi hp hp6
    by_cases hBq : B < q
    · exact ⟨q, ⟨hqp, hq6p⟩, hBq⟩
    · refine ⟨n - q - 6, ⟨hp6, ?_⟩, ?_⟩
      · have h6 : 6 ≤ n - q := by
          have := hp6.two_le
          omega
        simpa [Nat.sub_add_cancel h6] using hp
      · omega
