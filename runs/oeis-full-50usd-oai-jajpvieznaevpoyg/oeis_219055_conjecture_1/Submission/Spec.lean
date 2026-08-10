import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000




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


/- Finite certificates for the small Goldbach and Lemoine ranges. -/
private theorem prime_2 : Nat.Prime 2 := by norm_num
private theorem prime_3 : Nat.Prime 3 := by norm_num
private theorem prime_5 : Nat.Prime 5 := by norm_num
private theorem prime_7 : Nat.Prime 7 := by norm_num
private theorem prime_11 : Nat.Prime 11 := by norm_num
private theorem prime_13 : Nat.Prime 13 := by norm_num
private theorem prime_17 : Nat.Prime 17 := by norm_num
private theorem prime_19 : Nat.Prime 19 := by norm_num
private theorem prime_23 : Nat.Prime 23 := by norm_num
private theorem prime_29 : Nat.Prime 29 := by norm_num
private theorem prime_31 : Nat.Prime 31 := by norm_num
private theorem prime_37 : Nat.Prime 37 := by norm_num
private theorem prime_41 : Nat.Prime 41 := by norm_num
private theorem prime_43 : Nat.Prime 43 := by norm_num
private theorem prime_47 : Nat.Prime 47 := by norm_num
private theorem prime_53 : Nat.Prime 53 := by norm_num
private theorem prime_59 : Nat.Prime 59 := by norm_num
private theorem prime_61 : Nat.Prime 61 := by norm_num
private theorem prime_67 : Nat.Prime 67 := by norm_num
private theorem prime_71 : Nat.Prime 71 := by norm_num
private theorem prime_73 : Nat.Prime 73 := by norm_num
private theorem prime_79 : Nat.Prime 79 := by norm_num
private theorem prime_83 : Nat.Prime 83 := by norm_num
private theorem prime_89 : Nat.Prime 89 := by norm_num
private theorem prime_97 : Nat.Prime 97 := by norm_num
private theorem prime_101 : Nat.Prime 101 := by norm_num
private theorem prime_103 : Nat.Prime 103 := by norm_num
private theorem prime_107 : Nat.Prime 107 := by norm_num
private theorem prime_109 : Nat.Prime 109 := by norm_num
private theorem prime_113 : Nat.Prime 113 := by norm_num
private theorem prime_127 : Nat.Prime 127 := by norm_num
private theorem prime_131 : Nat.Prime 131 := by norm_num
private theorem prime_137 : Nat.Prime 137 := by norm_num
private theorem prime_139 : Nat.Prime 139 := by norm_num
private theorem prime_149 : Nat.Prime 149 := by norm_num
private theorem prime_151 : Nat.Prime 151 := by norm_num
private theorem prime_157 : Nat.Prime 157 := by norm_num
private theorem prime_163 : Nat.Prime 163 := by norm_num
private theorem prime_167 : Nat.Prime 167 := by norm_num
private theorem prime_173 : Nat.Prime 173 := by norm_num
private theorem prime_179 : Nat.Prime 179 := by norm_num
private theorem prime_181 : Nat.Prime 181 := by norm_num
private theorem prime_191 : Nat.Prime 191 := by norm_num
private theorem prime_193 : Nat.Prime 193 := by norm_num
private theorem prime_197 : Nat.Prime 197 := by norm_num
private theorem prime_199 : Nat.Prime 199 := by norm_num
private theorem prime_211 : Nat.Prime 211 := by norm_num
private theorem prime_223 : Nat.Prime 223 := by norm_num
private theorem prime_227 : Nat.Prime 227 := by norm_num
private theorem prime_229 : Nat.Prime 229 := by norm_num
private theorem prime_233 : Nat.Prime 233 := by norm_num
private theorem prime_239 : Nat.Prime 239 := by norm_num
private theorem prime_241 : Nat.Prime 241 := by norm_num
private theorem prime_251 : Nat.Prime 251 := by norm_num
private theorem prime_257 : Nat.Prime 257 := by norm_num
private theorem prime_263 : Nat.Prime 263 := by norm_num
private theorem prime_269 : Nat.Prime 269 := by norm_num
private theorem prime_271 : Nat.Prime 271 := by norm_num
private theorem prime_277 : Nat.Prime 277 := by norm_num
private theorem prime_281 : Nat.Prime 281 := by norm_num
private theorem prime_283 : Nat.Prime 283 := by norm_num
private theorem prime_293 : Nat.Prime 293 := by norm_num
private theorem prime_307 : Nat.Prime 307 := by norm_num
private theorem prime_311 : Nat.Prime 311 := by norm_num
private theorem prime_313 : Nat.Prime 313 := by norm_num
private theorem prime_317 : Nat.Prime 317 := by norm_num
private theorem prime_331 : Nat.Prime 331 := by norm_num
private theorem prime_337 : Nat.Prime 337 := by norm_num
private theorem prime_347 : Nat.Prime 347 := by norm_num
private theorem prime_349 : Nat.Prime 349 := by norm_num
private theorem prime_353 : Nat.Prime 353 := by norm_num
private theorem prime_359 : Nat.Prime 359 := by norm_num
private theorem prime_367 : Nat.Prime 367 := by norm_num
private theorem prime_373 : Nat.Prime 373 := by norm_num
private theorem prime_379 : Nat.Prime 379 := by norm_num
private theorem prime_383 : Nat.Prime 383 := by norm_num
private theorem prime_389 : Nat.Prime 389 := by norm_num
private theorem prime_397 : Nat.Prime 397 := by norm_num
private theorem prime_401 : Nat.Prime 401 := by norm_num
private theorem prime_409 : Nat.Prime 409 := by norm_num
private theorem prime_419 : Nat.Prime 419 := by norm_num
private theorem prime_421 : Nat.Prime 421 := by norm_num
private theorem prime_431 : Nat.Prime 431 := by norm_num
private theorem prime_433 : Nat.Prime 433 := by norm_num
private theorem prime_439 : Nat.Prime 439 := by norm_num
private theorem prime_443 : Nat.Prime 443 := by norm_num
private theorem prime_449 : Nat.Prime 449 := by norm_num
private theorem prime_457 : Nat.Prime 457 := by norm_num
private theorem prime_461 : Nat.Prime 461 := by norm_num
private theorem prime_463 : Nat.Prime 463 := by norm_num
private theorem prime_467 : Nat.Prime 467 := by norm_num
private theorem prime_479 : Nat.Prime 479 := by norm_num
private theorem prime_487 : Nat.Prime 487 := by norm_num
private theorem prime_491 : Nat.Prime 491 := by norm_num
private theorem prime_499 : Nat.Prime 499 := by norm_num
private theorem prime_503 : Nat.Prime 503 := by norm_num
private theorem prime_509 : Nat.Prime 509 := by norm_num
private theorem prime_521 : Nat.Prime 521 := by norm_num
private theorem prime_523 : Nat.Prime 523 := by norm_num
private theorem prime_541 : Nat.Prime 541 := by norm_num
private theorem prime_547 : Nat.Prime 547 := by norm_num
private theorem prime_557 : Nat.Prime 557 := by norm_num
private theorem prime_563 : Nat.Prime 563 := by norm_num
private theorem prime_569 : Nat.Prime 569 := by norm_num
private theorem prime_571 : Nat.Prime 571 := by norm_num
private theorem prime_577 : Nat.Prime 577 := by norm_num
private theorem prime_587 : Nat.Prime 587 := by norm_num
private theorem prime_593 : Nat.Prime 593 := by norm_num
private theorem prime_599 : Nat.Prime 599 := by norm_num
private theorem prime_601 : Nat.Prime 601 := by norm_num
private theorem prime_607 : Nat.Prime 607 := by norm_num
private theorem prime_613 : Nat.Prime 613 := by norm_num
private theorem prime_617 : Nat.Prime 617 := by norm_num
private theorem prime_619 : Nat.Prime 619 := by norm_num
private theorem prime_631 : Nat.Prime 631 := by norm_num
private theorem prime_641 : Nat.Prime 641 := by norm_num
private theorem prime_643 : Nat.Prime 643 := by norm_num
private theorem prime_647 : Nat.Prime 647 := by norm_num
private theorem prime_653 : Nat.Prime 653 := by norm_num
private theorem prime_659 : Nat.Prime 659 := by norm_num
private theorem prime_661 : Nat.Prime 661 := by norm_num
private theorem prime_673 : Nat.Prime 673 := by norm_num
private theorem prime_677 : Nat.Prime 677 := by norm_num
private theorem prime_683 : Nat.Prime 683 := by norm_num
private theorem prime_691 : Nat.Prime 691 := by norm_num
private theorem prime_701 : Nat.Prime 701 := by norm_num
private theorem prime_709 : Nat.Prime 709 := by norm_num
private theorem prime_719 : Nat.Prime 719 := by norm_num
private theorem prime_727 : Nat.Prime 727 := by norm_num
private theorem prime_733 : Nat.Prime 733 := by norm_num
private theorem prime_739 : Nat.Prime 739 := by norm_num
private theorem prime_743 : Nat.Prime 743 := by norm_num
private theorem prime_751 : Nat.Prime 751 := by norm_num
private theorem prime_757 : Nat.Prime 757 := by norm_num
private theorem prime_761 : Nat.Prime 761 := by norm_num
private theorem prime_769 : Nat.Prime 769 := by norm_num
private theorem prime_773 : Nat.Prime 773 := by norm_num
private theorem prime_787 : Nat.Prime 787 := by norm_num
private theorem prime_797 : Nat.Prime 797 := by norm_num
private theorem prime_809 : Nat.Prime 809 := by norm_num
private theorem prime_811 : Nat.Prime 811 := by norm_num
private theorem prime_821 : Nat.Prime 821 := by norm_num
private theorem prime_823 : Nat.Prime 823 := by norm_num
private theorem prime_827 : Nat.Prime 827 := by norm_num
private theorem prime_829 : Nat.Prime 829 := by norm_num
private theorem prime_839 : Nat.Prime 839 := by norm_num
private theorem prime_853 : Nat.Prime 853 := by norm_num
private theorem prime_857 : Nat.Prime 857 := by norm_num
private theorem prime_859 : Nat.Prime 859 := by norm_num
private theorem prime_863 : Nat.Prime 863 := by norm_num
private theorem prime_877 : Nat.Prime 877 := by norm_num
private theorem prime_881 : Nat.Prime 881 := by norm_num
private theorem prime_883 : Nat.Prime 883 := by norm_num
private theorem prime_887 : Nat.Prime 887 := by norm_num
private theorem prime_907 : Nat.Prime 907 := by norm_num
private theorem prime_911 : Nat.Prime 911 := by norm_num
private theorem prime_919 : Nat.Prime 919 := by norm_num
private theorem prime_929 : Nat.Prime 929 := by norm_num
private theorem prime_937 : Nat.Prime 937 := by norm_num
private theorem prime_941 : Nat.Prime 941 := by norm_num
private theorem prime_947 : Nat.Prime 947 := by norm_num
private theorem prime_953 : Nat.Prime 953 := by norm_num
private theorem prime_967 : Nat.Prime 967 := by norm_num
private theorem prime_971 : Nat.Prime 971 := by norm_num
private theorem prime_977 : Nat.Prime 977 := by norm_num
private theorem prime_983 : Nat.Prime 983 := by norm_num
private theorem prime_991 : Nat.Prime 991 := by norm_num
private theorem prime_997 : Nat.Prime 997 := by norm_num
private theorem prime_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_1237 : Nat.Prime 1237 := by norm_num
private theorem prime_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_1571 : Nat.Prime 1571 := by norm_num
private theorem prime_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_1583 : Nat.Prime 1583 := by norm_num
private theorem prime_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_1667 : Nat.Prime 1667 := by norm_num
private theorem prime_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_1847 : Nat.Prime 1847 := by norm_num
private theorem prime_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_1913 : Nat.Prime 1913 := by norm_num
private theorem prime_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_1949 : Nat.Prime 1949 := by norm_num
private theorem prime_1951 : Nat.Prime 1951 := by norm_num
private theorem prime_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_1987 : Nat.Prime 1987 := by norm_num
private theorem prime_1993 : Nat.Prime 1993 := by norm_num
private theorem prime_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_2017 : Nat.Prime 2017 := by norm_num
private theorem prime_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_2089 : Nat.Prime 2089 := by norm_num
private theorem prime_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_2129 : Nat.Prime 2129 := by norm_num
private theorem prime_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_2141 : Nat.Prime 2141 := by norm_num
private theorem prime_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_2243 : Nat.Prime 2243 := by norm_num
private theorem prime_2251 : Nat.Prime 2251 := by norm_num
private theorem prime_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_2333 : Nat.Prime 2333 := by norm_num
private theorem prime_2339 : Nat.Prime 2339 := by norm_num
private theorem prime_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_2357 : Nat.Prime 2357 := by norm_num
private theorem prime_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_2389 : Nat.Prime 2389 := by norm_num
private theorem prime_2393 : Nat.Prime 2393 := by norm_num
private theorem prime_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_2411 : Nat.Prime 2411 := by norm_num
private theorem prime_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_2441 : Nat.Prime 2441 := by norm_num
private theorem prime_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_2459 : Nat.Prime 2459 := by norm_num
private theorem prime_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_2473 : Nat.Prime 2473 := by norm_num
private theorem prime_2477 : Nat.Prime 2477 := by norm_num
private theorem prime_2503 : Nat.Prime 2503 := by norm_num
private theorem prime_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_2539 : Nat.Prime 2539 := by norm_num
private theorem prime_2543 : Nat.Prime 2543 := by norm_num
private theorem prime_2549 : Nat.Prime 2549 := by norm_num
private theorem prime_2551 : Nat.Prime 2551 := by norm_num
private theorem prime_2557 : Nat.Prime 2557 := by norm_num
private theorem prime_2579 : Nat.Prime 2579 := by norm_num
private theorem prime_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_2609 : Nat.Prime 2609 := by norm_num
private theorem prime_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_2657 : Nat.Prime 2657 := by norm_num
private theorem prime_2659 : Nat.Prime 2659 := by norm_num
private theorem prime_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_2671 : Nat.Prime 2671 := by norm_num
private theorem prime_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_2683 : Nat.Prime 2683 := by norm_num
private theorem prime_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_2693 : Nat.Prime 2693 := by norm_num
private theorem prime_2699 : Nat.Prime 2699 := by norm_num
private theorem prime_2707 : Nat.Prime 2707 := by norm_num
private theorem prime_2711 : Nat.Prime 2711 := by norm_num
private theorem prime_2713 : Nat.Prime 2713 := by norm_num
private theorem prime_2719 : Nat.Prime 2719 := by norm_num
private theorem prime_2729 : Nat.Prime 2729 := by norm_num
private theorem prime_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_2741 : Nat.Prime 2741 := by norm_num
private theorem prime_2749 : Nat.Prime 2749 := by norm_num
private theorem prime_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_2767 : Nat.Prime 2767 := by norm_num
private theorem prime_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_2789 : Nat.Prime 2789 := by norm_num
private theorem prime_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_2797 : Nat.Prime 2797 := by norm_num
private theorem prime_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_2843 : Nat.Prime 2843 := by norm_num
private theorem prime_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_2909 : Nat.Prime 2909 := by norm_num
private theorem prime_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_2953 : Nat.Prime 2953 := by norm_num
private theorem prime_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_2999 : Nat.Prime 2999 := by norm_num
private theorem prime_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_3019 : Nat.Prime 3019 := by norm_num
private theorem prime_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_3037 : Nat.Prime 3037 := by norm_num
private theorem prime_3041 : Nat.Prime 3041 := by norm_num
private theorem prime_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_3067 : Nat.Prime 3067 := by norm_num
private theorem prime_3079 : Nat.Prime 3079 := by norm_num
private theorem prime_3083 : Nat.Prime 3083 := by norm_num
private theorem prime_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_3119 : Nat.Prime 3119 := by norm_num
private theorem prime_3121 : Nat.Prime 3121 := by norm_num
private theorem prime_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_3167 : Nat.Prime 3167 := by norm_num
private theorem prime_3169 : Nat.Prime 3169 := by norm_num
private theorem prime_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_3187 : Nat.Prime 3187 := by norm_num
private theorem prime_3191 : Nat.Prime 3191 := by norm_num
private theorem prime_3203 : Nat.Prime 3203 := by norm_num
private theorem prime_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_3217 : Nat.Prime 3217 := by norm_num
private theorem prime_3221 : Nat.Prime 3221 := by norm_num
private theorem prime_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_3251 : Nat.Prime 3251 := by norm_num
private theorem prime_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_3257 : Nat.Prime 3257 := by norm_num
private theorem prime_3259 : Nat.Prime 3259 := by norm_num
private theorem prime_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_3299 : Nat.Prime 3299 := by norm_num
private theorem prime_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_3313 : Nat.Prime 3313 := by norm_num
private theorem prime_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_3323 : Nat.Prime 3323 := by norm_num
private theorem prime_3329 : Nat.Prime 3329 := by norm_num
private theorem prime_3331 : Nat.Prime 3331 := by norm_num
private theorem prime_3343 : Nat.Prime 3343 := by norm_num
private theorem prime_3347 : Nat.Prime 3347 := by norm_num
private theorem prime_3359 : Nat.Prime 3359 := by norm_num
private theorem prime_3361 : Nat.Prime 3361 := by norm_num
private theorem prime_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_3373 : Nat.Prime 3373 := by norm_num
private theorem prime_3389 : Nat.Prime 3389 := by norm_num
private theorem prime_3391 : Nat.Prime 3391 := by norm_num
private theorem prime_3407 : Nat.Prime 3407 := by norm_num
private theorem prime_3413 : Nat.Prime 3413 := by norm_num
private theorem prime_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_3449 : Nat.Prime 3449 := by norm_num
private theorem prime_3457 : Nat.Prime 3457 := by norm_num
private theorem prime_3461 : Nat.Prime 3461 := by norm_num
private theorem prime_3463 : Nat.Prime 3463 := by norm_num
private theorem prime_3467 : Nat.Prime 3467 := by norm_num
private theorem prime_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_3491 : Nat.Prime 3491 := by norm_num
private theorem prime_3499 : Nat.Prime 3499 := by norm_num
private theorem prime_3511 : Nat.Prime 3511 := by norm_num
private theorem prime_3517 : Nat.Prime 3517 := by norm_num
private theorem prime_3527 : Nat.Prime 3527 := by norm_num
private theorem prime_3529 : Nat.Prime 3529 := by norm_num
private theorem prime_3533 : Nat.Prime 3533 := by norm_num
private theorem prime_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_3541 : Nat.Prime 3541 := by norm_num
private theorem prime_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_3557 : Nat.Prime 3557 := by norm_num
private theorem prime_3559 : Nat.Prime 3559 := by norm_num
private theorem prime_3571 : Nat.Prime 3571 := by norm_num
private theorem prime_3581 : Nat.Prime 3581 := by norm_num
private theorem prime_3583 : Nat.Prime 3583 := by norm_num
private theorem prime_3593 : Nat.Prime 3593 := by norm_num
private theorem prime_3607 : Nat.Prime 3607 := by norm_num
private theorem prime_3613 : Nat.Prime 3613 := by norm_num
private theorem prime_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_3623 : Nat.Prime 3623 := by norm_num
private theorem prime_3631 : Nat.Prime 3631 := by norm_num
private theorem prime_3637 : Nat.Prime 3637 := by norm_num
private theorem prime_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_3659 : Nat.Prime 3659 := by norm_num
private theorem prime_3671 : Nat.Prime 3671 := by norm_num
private theorem prime_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_3677 : Nat.Prime 3677 := by norm_num
private theorem prime_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_3697 : Nat.Prime 3697 := by norm_num
private theorem prime_3701 : Nat.Prime 3701 := by norm_num
private theorem prime_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_3727 : Nat.Prime 3727 := by norm_num
private theorem prime_3733 : Nat.Prime 3733 := by norm_num
private theorem prime_3739 : Nat.Prime 3739 := by norm_num
private theorem prime_3761 : Nat.Prime 3761 := by norm_num
private theorem prime_3767 : Nat.Prime 3767 := by norm_num
private theorem prime_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_3797 : Nat.Prime 3797 := by norm_num
private theorem prime_3803 : Nat.Prime 3803 := by norm_num
private theorem prime_3821 : Nat.Prime 3821 := by norm_num
private theorem prime_3823 : Nat.Prime 3823 := by norm_num
private theorem prime_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_3847 : Nat.Prime 3847 := by norm_num
private theorem prime_3851 : Nat.Prime 3851 := by norm_num
private theorem prime_3853 : Nat.Prime 3853 := by norm_num
private theorem prime_3863 : Nat.Prime 3863 := by norm_num
private theorem prime_3877 : Nat.Prime 3877 := by norm_num
private theorem prime_3881 : Nat.Prime 3881 := by norm_num
private theorem prime_3889 : Nat.Prime 3889 := by norm_num
private theorem prime_3907 : Nat.Prime 3907 := by norm_num
private theorem prime_3911 : Nat.Prime 3911 := by norm_num
private theorem prime_3917 : Nat.Prime 3917 := by norm_num
private theorem prime_3919 : Nat.Prime 3919 := by norm_num
private theorem prime_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_3929 : Nat.Prime 3929 := by norm_num
private theorem prime_3931 : Nat.Prime 3931 := by norm_num
private theorem prime_3943 : Nat.Prime 3943 := by norm_num
private theorem prime_3947 : Nat.Prime 3947 := by norm_num
private theorem prime_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_3989 : Nat.Prime 3989 := by norm_num
private theorem prime_4001 : Nat.Prime 4001 := by norm_num
private theorem prime_4003 : Nat.Prime 4003 := by norm_num
private theorem prime_4007 : Nat.Prime 4007 := by norm_num
private theorem prime_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_4021 : Nat.Prime 4021 := by norm_num
private theorem prime_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_4057 : Nat.Prime 4057 := by norm_num
private theorem prime_4073 : Nat.Prime 4073 := by norm_num
private theorem prime_4079 : Nat.Prime 4079 := by norm_num
private theorem prime_4091 : Nat.Prime 4091 := by norm_num
private theorem prime_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_4099 : Nat.Prime 4099 := by norm_num
private theorem prime_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_4127 : Nat.Prime 4127 := by norm_num
private theorem prime_4129 : Nat.Prime 4129 := by norm_num
private theorem prime_4133 : Nat.Prime 4133 := by norm_num
private theorem prime_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_4153 : Nat.Prime 4153 := by norm_num
private theorem prime_4157 : Nat.Prime 4157 := by norm_num
private theorem prime_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_4177 : Nat.Prime 4177 := by norm_num
private theorem prime_4201 : Nat.Prime 4201 := by norm_num
private theorem prime_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_4217 : Nat.Prime 4217 := by norm_num
private theorem prime_4219 : Nat.Prime 4219 := by norm_num
private theorem prime_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_4231 : Nat.Prime 4231 := by norm_num
private theorem prime_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_4243 : Nat.Prime 4243 := by norm_num
private theorem prime_4253 : Nat.Prime 4253 := by norm_num
private theorem prime_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_4261 : Nat.Prime 4261 := by norm_num
private theorem prime_4271 : Nat.Prime 4271 := by norm_num
private theorem prime_4273 : Nat.Prime 4273 := by norm_num
private theorem prime_4283 : Nat.Prime 4283 := by norm_num
private theorem prime_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_4297 : Nat.Prime 4297 := by norm_num
private theorem prime_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_4337 : Nat.Prime 4337 := by norm_num
private theorem prime_4339 : Nat.Prime 4339 := by norm_num
private theorem prime_4349 : Nat.Prime 4349 := by norm_num
private theorem prime_4357 : Nat.Prime 4357 := by norm_num
private theorem prime_4363 : Nat.Prime 4363 := by norm_num
private theorem prime_4373 : Nat.Prime 4373 := by norm_num
private theorem prime_4391 : Nat.Prime 4391 := by norm_num
private theorem prime_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_4409 : Nat.Prime 4409 := by norm_num
private theorem prime_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_4423 : Nat.Prime 4423 := by norm_num
private theorem prime_4441 : Nat.Prime 4441 := by norm_num
private theorem prime_4447 : Nat.Prime 4447 := by norm_num
private theorem prime_4451 : Nat.Prime 4451 := by norm_num
private theorem prime_4457 : Nat.Prime 4457 := by norm_num
private theorem prime_4463 : Nat.Prime 4463 := by norm_num
private theorem prime_4481 : Nat.Prime 4481 := by norm_num
private theorem prime_4483 : Nat.Prime 4483 := by norm_num
private theorem prime_4493 : Nat.Prime 4493 := by norm_num
private theorem prime_4507 : Nat.Prime 4507 := by norm_num
private theorem prime_4513 : Nat.Prime 4513 := by norm_num
private theorem prime_4517 : Nat.Prime 4517 := by norm_num
private theorem prime_4519 : Nat.Prime 4519 := by norm_num
private theorem prime_4523 : Nat.Prime 4523 := by norm_num
private theorem prime_4547 : Nat.Prime 4547 := by norm_num
private theorem prime_4549 : Nat.Prime 4549 := by norm_num
private theorem prime_4561 : Nat.Prime 4561 := by norm_num
private theorem prime_4567 : Nat.Prime 4567 := by norm_num
private theorem prime_4583 : Nat.Prime 4583 := by norm_num
private theorem prime_4591 : Nat.Prime 4591 := by norm_num
private theorem prime_4597 : Nat.Prime 4597 := by norm_num
private theorem prime_4603 : Nat.Prime 4603 := by norm_num
private theorem prime_4621 : Nat.Prime 4621 := by norm_num
private theorem prime_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_4639 : Nat.Prime 4639 := by norm_num
private theorem prime_4643 : Nat.Prime 4643 := by norm_num
private theorem prime_4649 : Nat.Prime 4649 := by norm_num
private theorem prime_4651 : Nat.Prime 4651 := by norm_num
private theorem prime_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_4663 : Nat.Prime 4663 := by norm_num
private theorem prime_4673 : Nat.Prime 4673 := by norm_num
private theorem prime_4679 : Nat.Prime 4679 := by norm_num
private theorem prime_4691 : Nat.Prime 4691 := by norm_num
private theorem prime_4703 : Nat.Prime 4703 := by norm_num
private theorem prime_4721 : Nat.Prime 4721 := by norm_num
private theorem prime_4723 : Nat.Prime 4723 := by norm_num
private theorem prime_4729 : Nat.Prime 4729 := by norm_num
private theorem prime_4733 : Nat.Prime 4733 := by norm_num
private theorem prime_4751 : Nat.Prime 4751 := by norm_num
private theorem prime_4759 : Nat.Prime 4759 := by norm_num
private theorem prime_4783 : Nat.Prime 4783 := by norm_num
private theorem prime_4787 : Nat.Prime 4787 := by norm_num
private theorem prime_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_4793 : Nat.Prime 4793 := by norm_num
private theorem prime_4799 : Nat.Prime 4799 := by norm_num
private theorem prime_4801 : Nat.Prime 4801 := by norm_num
private theorem prime_4813 : Nat.Prime 4813 := by norm_num
private theorem prime_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_4831 : Nat.Prime 4831 := by norm_num
private theorem prime_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_4871 : Nat.Prime 4871 := by norm_num
private theorem prime_4877 : Nat.Prime 4877 := by norm_num
private theorem prime_4889 : Nat.Prime 4889 := by norm_num
private theorem prime_4903 : Nat.Prime 4903 := by norm_num
private theorem prime_4909 : Nat.Prime 4909 := by norm_num
private theorem prime_4919 : Nat.Prime 4919 := by norm_num
private theorem prime_4931 : Nat.Prime 4931 := by norm_num
private theorem prime_4933 : Nat.Prime 4933 := by norm_num
private theorem prime_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_4943 : Nat.Prime 4943 := by norm_num
private theorem prime_4951 : Nat.Prime 4951 := by norm_num
private theorem prime_4957 : Nat.Prime 4957 := by norm_num
private theorem prime_4967 : Nat.Prime 4967 := by norm_num
private theorem prime_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_4973 : Nat.Prime 4973 := by norm_num
private theorem prime_4987 : Nat.Prime 4987 := by norm_num
private theorem prime_4993 : Nat.Prime 4993 := by norm_num
private theorem prime_4999 : Nat.Prime 4999 := by norm_num
private theorem prime_5003 : Nat.Prime 5003 := by norm_num
private theorem prime_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_5011 : Nat.Prime 5011 := by norm_num
private theorem prime_5021 : Nat.Prime 5021 := by norm_num
private theorem prime_5023 : Nat.Prime 5023 := by norm_num
private theorem prime_5039 : Nat.Prime 5039 := by norm_num
private theorem prime_5051 : Nat.Prime 5051 := by norm_num
private theorem prime_5059 : Nat.Prime 5059 := by norm_num
private theorem prime_5077 : Nat.Prime 5077 := by norm_num
private theorem prime_5081 : Nat.Prime 5081 := by norm_num
private theorem prime_5087 : Nat.Prime 5087 := by norm_num
private theorem prime_5099 : Nat.Prime 5099 := by norm_num
private theorem prime_5101 : Nat.Prime 5101 := by norm_num
private theorem prime_5107 : Nat.Prime 5107 := by norm_num
private theorem prime_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_5119 : Nat.Prime 5119 := by norm_num
private theorem prime_5147 : Nat.Prime 5147 := by norm_num
private theorem prime_5153 : Nat.Prime 5153 := by norm_num
private theorem prime_5167 : Nat.Prime 5167 := by norm_num
private theorem prime_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_5179 : Nat.Prime 5179 := by norm_num
private theorem prime_5189 : Nat.Prime 5189 := by norm_num
private theorem prime_5197 : Nat.Prime 5197 := by norm_num
private theorem prime_5209 : Nat.Prime 5209 := by norm_num
private theorem prime_5227 : Nat.Prime 5227 := by norm_num
private theorem prime_5231 : Nat.Prime 5231 := by norm_num
private theorem prime_5233 : Nat.Prime 5233 := by norm_num
private theorem prime_5237 : Nat.Prime 5237 := by norm_num
private theorem prime_5261 : Nat.Prime 5261 := by norm_num
private theorem prime_5273 : Nat.Prime 5273 := by norm_num
private theorem prime_5279 : Nat.Prime 5279 := by norm_num
private theorem prime_5281 : Nat.Prime 5281 := by norm_num
private theorem prime_5297 : Nat.Prime 5297 := by norm_num
private theorem prime_5303 : Nat.Prime 5303 := by norm_num
private theorem prime_5309 : Nat.Prime 5309 := by norm_num
private theorem prime_5323 : Nat.Prime 5323 := by norm_num
private theorem prime_5333 : Nat.Prime 5333 := by norm_num
private theorem prime_5347 : Nat.Prime 5347 := by norm_num
private theorem prime_5351 : Nat.Prime 5351 := by norm_num
private theorem prime_5381 : Nat.Prime 5381 := by norm_num
private theorem prime_5387 : Nat.Prime 5387 := by norm_num
private theorem prime_5393 : Nat.Prime 5393 := by norm_num
private theorem prime_5399 : Nat.Prime 5399 := by norm_num
private theorem prime_5407 : Nat.Prime 5407 := by norm_num
private theorem prime_5413 : Nat.Prime 5413 := by norm_num
private theorem prime_5417 : Nat.Prime 5417 := by norm_num
private theorem prime_5419 : Nat.Prime 5419 := by norm_num
private theorem prime_5431 : Nat.Prime 5431 := by norm_num
private theorem prime_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_5441 : Nat.Prime 5441 := by norm_num
private theorem prime_5443 : Nat.Prime 5443 := by norm_num
private theorem prime_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_5471 : Nat.Prime 5471 := by norm_num
private theorem prime_5477 : Nat.Prime 5477 := by norm_num
private theorem prime_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_5483 : Nat.Prime 5483 := by norm_num
private theorem prime_5501 : Nat.Prime 5501 := by norm_num
private theorem prime_5503 : Nat.Prime 5503 := by norm_num
private theorem prime_5507 : Nat.Prime 5507 := by norm_num
private theorem prime_5519 : Nat.Prime 5519 := by norm_num
private theorem prime_5521 : Nat.Prime 5521 := by norm_num
private theorem prime_5527 : Nat.Prime 5527 := by norm_num
private theorem prime_5531 : Nat.Prime 5531 := by norm_num
private theorem prime_5557 : Nat.Prime 5557 := by norm_num
private theorem prime_5563 : Nat.Prime 5563 := by norm_num
private theorem prime_5569 : Nat.Prime 5569 := by norm_num
private theorem prime_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_5581 : Nat.Prime 5581 := by norm_num
private theorem prime_5591 : Nat.Prime 5591 := by norm_num
private theorem prime_5623 : Nat.Prime 5623 := by norm_num
private theorem prime_5639 : Nat.Prime 5639 := by norm_num
private theorem prime_5641 : Nat.Prime 5641 := by norm_num
private theorem prime_5647 : Nat.Prime 5647 := by norm_num
private theorem prime_5651 : Nat.Prime 5651 := by norm_num
private theorem prime_5653 : Nat.Prime 5653 := by norm_num
private theorem prime_5657 : Nat.Prime 5657 := by norm_num
private theorem prime_5659 : Nat.Prime 5659 := by norm_num
private theorem prime_5669 : Nat.Prime 5669 := by norm_num
private theorem prime_5683 : Nat.Prime 5683 := by norm_num
private theorem prime_5689 : Nat.Prime 5689 := by norm_num
private theorem prime_5693 : Nat.Prime 5693 := by norm_num
private theorem prime_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_5711 : Nat.Prime 5711 := by norm_num
private theorem prime_5717 : Nat.Prime 5717 := by norm_num
private theorem prime_5737 : Nat.Prime 5737 := by norm_num
private theorem prime_5741 : Nat.Prime 5741 := by norm_num
private theorem prime_5743 : Nat.Prime 5743 := by norm_num
private theorem prime_5749 : Nat.Prime 5749 := by norm_num
private theorem prime_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_5783 : Nat.Prime 5783 := by norm_num
private theorem prime_5791 : Nat.Prime 5791 := by norm_num
private theorem prime_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_5807 : Nat.Prime 5807 := by norm_num
private theorem prime_5813 : Nat.Prime 5813 := by norm_num
private theorem prime_5821 : Nat.Prime 5821 := by norm_num
private theorem prime_5827 : Nat.Prime 5827 := by norm_num
private theorem prime_5839 : Nat.Prime 5839 := by norm_num
private theorem prime_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_5849 : Nat.Prime 5849 := by norm_num
private theorem prime_5851 : Nat.Prime 5851 := by norm_num
private theorem prime_5857 : Nat.Prime 5857 := by norm_num
private theorem prime_5861 : Nat.Prime 5861 := by norm_num
private theorem prime_5867 : Nat.Prime 5867 := by norm_num
private theorem prime_5869 : Nat.Prime 5869 := by norm_num
private theorem prime_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_5903 : Nat.Prime 5903 := by norm_num
private theorem prime_5923 : Nat.Prime 5923 := by norm_num
private theorem prime_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_5939 : Nat.Prime 5939 := by norm_num
private theorem prime_5953 : Nat.Prime 5953 := by norm_num
private theorem prime_5981 : Nat.Prime 5981 := by norm_num
private theorem prime_5987 : Nat.Prime 5987 := by norm_num
private theorem prime_6007 : Nat.Prime 6007 := by norm_num
private theorem prime_6011 : Nat.Prime 6011 := by norm_num
private theorem prime_6029 : Nat.Prime 6029 := by norm_num
private theorem prime_6037 : Nat.Prime 6037 := by norm_num
private theorem prime_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_6047 : Nat.Prime 6047 := by norm_num
private theorem prime_6053 : Nat.Prime 6053 := by norm_num
private theorem prime_6067 : Nat.Prime 6067 := by norm_num
private theorem prime_6073 : Nat.Prime 6073 := by norm_num
private theorem prime_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_6089 : Nat.Prime 6089 := by norm_num
private theorem prime_6091 : Nat.Prime 6091 := by norm_num
private theorem prime_6101 : Nat.Prime 6101 := by norm_num
private theorem prime_6113 : Nat.Prime 6113 := by norm_num
private theorem prime_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_6131 : Nat.Prime 6131 := by norm_num
private theorem prime_6133 : Nat.Prime 6133 := by norm_num
private theorem prime_6143 : Nat.Prime 6143 := by norm_num
private theorem prime_6151 : Nat.Prime 6151 := by norm_num
private theorem prime_6163 : Nat.Prime 6163 := by norm_num
private theorem prime_6173 : Nat.Prime 6173 := by norm_num
private theorem prime_6197 : Nat.Prime 6197 := by norm_num
private theorem prime_6199 : Nat.Prime 6199 := by norm_num
private theorem prime_6203 : Nat.Prime 6203 := by norm_num
private theorem prime_6211 : Nat.Prime 6211 := by norm_num
private theorem prime_6217 : Nat.Prime 6217 := by norm_num
private theorem prime_6221 : Nat.Prime 6221 := by norm_num
private theorem prime_6229 : Nat.Prime 6229 := by norm_num
private theorem prime_6247 : Nat.Prime 6247 := by norm_num
private theorem prime_6257 : Nat.Prime 6257 := by norm_num
private theorem prime_6263 : Nat.Prime 6263 := by norm_num
private theorem prime_6269 : Nat.Prime 6269 := by norm_num
private theorem prime_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_6277 : Nat.Prime 6277 := by norm_num
private theorem prime_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_6299 : Nat.Prime 6299 := by norm_num
private theorem prime_6301 : Nat.Prime 6301 := by norm_num
private theorem prime_6311 : Nat.Prime 6311 := by norm_num
private theorem prime_6317 : Nat.Prime 6317 := by norm_num
private theorem prime_6323 : Nat.Prime 6323 := by norm_num
private theorem prime_6329 : Nat.Prime 6329 := by norm_num
private theorem prime_6337 : Nat.Prime 6337 := by norm_num
private theorem prime_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_6353 : Nat.Prime 6353 := by norm_num
private theorem prime_6359 : Nat.Prime 6359 := by norm_num
private theorem prime_6361 : Nat.Prime 6361 := by norm_num
private theorem prime_6367 : Nat.Prime 6367 := by norm_num
private theorem prime_6373 : Nat.Prime 6373 := by norm_num
private theorem prime_6379 : Nat.Prime 6379 := by norm_num
private theorem prime_6389 : Nat.Prime 6389 := by norm_num
private theorem prime_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_6421 : Nat.Prime 6421 := by norm_num
private theorem prime_6427 : Nat.Prime 6427 := by norm_num
private theorem prime_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_6469 : Nat.Prime 6469 := by norm_num
private theorem prime_6473 : Nat.Prime 6473 := by norm_num
private theorem prime_6481 : Nat.Prime 6481 := by norm_num
private theorem prime_6491 : Nat.Prime 6491 := by norm_num
private theorem prime_6521 : Nat.Prime 6521 := by norm_num
private theorem prime_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_6547 : Nat.Prime 6547 := by norm_num
private theorem prime_6551 : Nat.Prime 6551 := by norm_num
private theorem prime_6553 : Nat.Prime 6553 := by norm_num
private theorem prime_6563 : Nat.Prime 6563 := by norm_num
private theorem prime_6569 : Nat.Prime 6569 := by norm_num
private theorem prime_6571 : Nat.Prime 6571 := by norm_num
private theorem prime_6577 : Nat.Prime 6577 := by norm_num
private theorem prime_6581 : Nat.Prime 6581 := by norm_num
private theorem prime_6599 : Nat.Prime 6599 := by norm_num
private theorem prime_6607 : Nat.Prime 6607 := by norm_num
private theorem prime_6619 : Nat.Prime 6619 := by norm_num
private theorem prime_6637 : Nat.Prime 6637 := by norm_num
private theorem prime_6653 : Nat.Prime 6653 := by norm_num
private theorem prime_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_6661 : Nat.Prime 6661 := by norm_num
private theorem prime_6673 : Nat.Prime 6673 := by norm_num
private theorem prime_6679 : Nat.Prime 6679 := by norm_num
private theorem prime_6689 : Nat.Prime 6689 := by norm_num
private theorem prime_6691 : Nat.Prime 6691 := by norm_num
private theorem prime_6701 : Nat.Prime 6701 := by norm_num
private theorem prime_6703 : Nat.Prime 6703 := by norm_num
private theorem prime_6709 : Nat.Prime 6709 := by norm_num
private theorem prime_6719 : Nat.Prime 6719 := by norm_num
private theorem prime_6733 : Nat.Prime 6733 := by norm_num
private theorem prime_6737 : Nat.Prime 6737 := by norm_num
private theorem prime_6761 : Nat.Prime 6761 := by norm_num
private theorem prime_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_6779 : Nat.Prime 6779 := by norm_num
private theorem prime_6781 : Nat.Prime 6781 := by norm_num
private theorem prime_6791 : Nat.Prime 6791 := by norm_num
private theorem prime_6793 : Nat.Prime 6793 := by norm_num
private theorem prime_6803 : Nat.Prime 6803 := by norm_num
private theorem prime_6823 : Nat.Prime 6823 := by norm_num
private theorem prime_6827 : Nat.Prime 6827 := by norm_num
private theorem prime_6829 : Nat.Prime 6829 := by norm_num
private theorem prime_6833 : Nat.Prime 6833 := by norm_num
private theorem prime_6841 : Nat.Prime 6841 := by norm_num
private theorem prime_6857 : Nat.Prime 6857 := by norm_num
private theorem prime_6863 : Nat.Prime 6863 := by norm_num
private theorem prime_6869 : Nat.Prime 6869 := by norm_num
private theorem prime_6871 : Nat.Prime 6871 := by norm_num
private theorem prime_6883 : Nat.Prime 6883 := by norm_num
private theorem prime_6899 : Nat.Prime 6899 := by norm_num
private theorem prime_6907 : Nat.Prime 6907 := by norm_num
private theorem prime_6911 : Nat.Prime 6911 := by norm_num
private theorem prime_6917 : Nat.Prime 6917 := by norm_num
private theorem prime_6947 : Nat.Prime 6947 := by norm_num
private theorem prime_6949 : Nat.Prime 6949 := by norm_num
private theorem prime_6959 : Nat.Prime 6959 := by norm_num
private theorem prime_6961 : Nat.Prime 6961 := by norm_num
private theorem prime_6967 : Nat.Prime 6967 := by norm_num
private theorem prime_6971 : Nat.Prime 6971 := by norm_num
private theorem prime_6977 : Nat.Prime 6977 := by norm_num
private theorem prime_6983 : Nat.Prime 6983 := by norm_num
private theorem prime_6991 : Nat.Prime 6991 := by norm_num
private theorem prime_6997 : Nat.Prime 6997 := by norm_num
private theorem prime_7001 : Nat.Prime 7001 := by norm_num
private theorem prime_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_7019 : Nat.Prime 7019 := by norm_num
private theorem prime_7027 : Nat.Prime 7027 := by norm_num
private theorem prime_7039 : Nat.Prime 7039 := by norm_num
private theorem prime_7043 : Nat.Prime 7043 := by norm_num
private theorem prime_7057 : Nat.Prime 7057 := by norm_num
private theorem prime_7069 : Nat.Prime 7069 := by norm_num
private theorem prime_7079 : Nat.Prime 7079 := by norm_num
private theorem prime_7103 : Nat.Prime 7103 := by norm_num
private theorem prime_7109 : Nat.Prime 7109 := by norm_num
private theorem prime_7121 : Nat.Prime 7121 := by norm_num
private theorem prime_7127 : Nat.Prime 7127 := by norm_num
private theorem prime_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_7151 : Nat.Prime 7151 := by norm_num
private theorem prime_7159 : Nat.Prime 7159 := by norm_num
private theorem prime_7177 : Nat.Prime 7177 := by norm_num
private theorem prime_7187 : Nat.Prime 7187 := by norm_num
private theorem prime_7193 : Nat.Prime 7193 := by norm_num
private theorem prime_7207 : Nat.Prime 7207 := by norm_num
private theorem prime_7211 : Nat.Prime 7211 := by norm_num
private theorem prime_7213 : Nat.Prime 7213 := by norm_num
private theorem prime_7219 : Nat.Prime 7219 := by norm_num
private theorem prime_7229 : Nat.Prime 7229 := by norm_num
private theorem prime_7237 : Nat.Prime 7237 := by norm_num
private theorem prime_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_7247 : Nat.Prime 7247 := by norm_num
private theorem prime_7253 : Nat.Prime 7253 := by norm_num
private theorem prime_7283 : Nat.Prime 7283 := by norm_num
private theorem prime_7297 : Nat.Prime 7297 := by norm_num
private theorem prime_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_7309 : Nat.Prime 7309 := by norm_num
private theorem prime_7321 : Nat.Prime 7321 := by norm_num
private theorem prime_7331 : Nat.Prime 7331 := by norm_num
private theorem prime_7333 : Nat.Prime 7333 := by norm_num
private theorem prime_7349 : Nat.Prime 7349 := by norm_num
private theorem prime_7351 : Nat.Prime 7351 := by norm_num
private theorem prime_7369 : Nat.Prime 7369 := by norm_num
private theorem prime_7393 : Nat.Prime 7393 := by norm_num
private theorem prime_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_7417 : Nat.Prime 7417 := by norm_num
private theorem prime_7433 : Nat.Prime 7433 := by norm_num
private theorem prime_7451 : Nat.Prime 7451 := by norm_num
private theorem prime_7457 : Nat.Prime 7457 := by norm_num
private theorem prime_7459 : Nat.Prime 7459 := by norm_num
private theorem prime_7477 : Nat.Prime 7477 := by norm_num
private theorem prime_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_7487 : Nat.Prime 7487 := by norm_num
private theorem prime_7489 : Nat.Prime 7489 := by norm_num
private theorem prime_7499 : Nat.Prime 7499 := by norm_num
private theorem prime_7507 : Nat.Prime 7507 := by norm_num
private theorem prime_7517 : Nat.Prime 7517 := by norm_num
private theorem prime_7523 : Nat.Prime 7523 := by norm_num
private theorem prime_7529 : Nat.Prime 7529 := by norm_num
private theorem prime_7537 : Nat.Prime 7537 := by norm_num
private theorem prime_7541 : Nat.Prime 7541 := by norm_num
private theorem prime_7547 : Nat.Prime 7547 := by norm_num
private theorem prime_7549 : Nat.Prime 7549 := by norm_num
private theorem prime_7559 : Nat.Prime 7559 := by norm_num
private theorem prime_7561 : Nat.Prime 7561 := by norm_num
private theorem prime_7573 : Nat.Prime 7573 := by norm_num
private theorem prime_7577 : Nat.Prime 7577 := by norm_num
private theorem prime_7583 : Nat.Prime 7583 := by norm_num
private theorem prime_7589 : Nat.Prime 7589 := by norm_num
private theorem prime_7591 : Nat.Prime 7591 := by norm_num
private theorem prime_7603 : Nat.Prime 7603 := by norm_num
private theorem prime_7607 : Nat.Prime 7607 := by norm_num
private theorem prime_7621 : Nat.Prime 7621 := by norm_num
private theorem prime_7639 : Nat.Prime 7639 := by norm_num
private theorem prime_7643 : Nat.Prime 7643 := by norm_num
private theorem prime_7649 : Nat.Prime 7649 := by norm_num
private theorem prime_7669 : Nat.Prime 7669 := by norm_num
private theorem prime_7673 : Nat.Prime 7673 := by norm_num
private theorem prime_7681 : Nat.Prime 7681 := by norm_num
private theorem prime_7687 : Nat.Prime 7687 := by norm_num
private theorem prime_7691 : Nat.Prime 7691 := by norm_num
private theorem prime_7699 : Nat.Prime 7699 := by norm_num
private theorem prime_7703 : Nat.Prime 7703 := by norm_num
private theorem prime_7717 : Nat.Prime 7717 := by norm_num
private theorem prime_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_7727 : Nat.Prime 7727 := by norm_num
private theorem prime_7741 : Nat.Prime 7741 := by norm_num
private theorem prime_7753 : Nat.Prime 7753 := by norm_num
private theorem prime_7757 : Nat.Prime 7757 := by norm_num
private theorem prime_7759 : Nat.Prime 7759 := by norm_num
private theorem prime_7789 : Nat.Prime 7789 := by norm_num
private theorem prime_7793 : Nat.Prime 7793 := by norm_num
private theorem prime_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_7823 : Nat.Prime 7823 := by norm_num
private theorem prime_7829 : Nat.Prime 7829 := by norm_num
private theorem prime_7841 : Nat.Prime 7841 := by norm_num
private theorem prime_7853 : Nat.Prime 7853 := by norm_num
private theorem prime_7867 : Nat.Prime 7867 := by norm_num
private theorem prime_7873 : Nat.Prime 7873 := by norm_num
private theorem prime_7877 : Nat.Prime 7877 := by norm_num
private theorem prime_7879 : Nat.Prime 7879 := by norm_num
private theorem prime_7883 : Nat.Prime 7883 := by norm_num
private theorem prime_7901 : Nat.Prime 7901 := by norm_num
private theorem prime_7907 : Nat.Prime 7907 := by norm_num
private theorem prime_7919 : Nat.Prime 7919 := by norm_num
private theorem prime_7927 : Nat.Prime 7927 := by norm_num
private theorem prime_7933 : Nat.Prime 7933 := by norm_num
private theorem prime_7937 : Nat.Prime 7937 := by norm_num
private theorem prime_7949 : Nat.Prime 7949 := by norm_num
private theorem prime_7951 : Nat.Prime 7951 := by norm_num
private theorem prime_7963 : Nat.Prime 7963 := by norm_num
private theorem prime_7993 : Nat.Prime 7993 := by norm_num
private theorem prime_8009 : Nat.Prime 8009 := by norm_num
private theorem prime_8011 : Nat.Prime 8011 := by norm_num
private theorem prime_8017 : Nat.Prime 8017 := by norm_num
private theorem prime_8039 : Nat.Prime 8039 := by norm_num
private theorem prime_8053 : Nat.Prime 8053 := by norm_num
private theorem prime_8059 : Nat.Prime 8059 := by norm_num
private theorem prime_8069 : Nat.Prime 8069 := by norm_num
private theorem prime_8081 : Nat.Prime 8081 := by norm_num
private theorem prime_8087 : Nat.Prime 8087 := by norm_num
private theorem prime_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_8093 : Nat.Prime 8093 := by norm_num
private theorem prime_8101 : Nat.Prime 8101 := by norm_num
private theorem prime_8111 : Nat.Prime 8111 := by norm_num
private theorem prime_8117 : Nat.Prime 8117 := by norm_num
private theorem prime_8123 : Nat.Prime 8123 := by norm_num
private theorem prime_8147 : Nat.Prime 8147 := by norm_num
private theorem prime_8161 : Nat.Prime 8161 := by norm_num
private theorem prime_8167 : Nat.Prime 8167 := by norm_num
private theorem prime_8171 : Nat.Prime 8171 := by norm_num
private theorem prime_8179 : Nat.Prime 8179 := by norm_num
private theorem prime_8191 : Nat.Prime 8191 := by norm_num
private theorem prime_8209 : Nat.Prime 8209 := by norm_num
private theorem prime_8219 : Nat.Prime 8219 := by norm_num
private theorem prime_8221 : Nat.Prime 8221 := by norm_num
private theorem prime_8231 : Nat.Prime 8231 := by norm_num
private theorem prime_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_8237 : Nat.Prime 8237 := by norm_num
private theorem prime_8243 : Nat.Prime 8243 := by norm_num
private theorem prime_8263 : Nat.Prime 8263 := by norm_num
private theorem prime_8269 : Nat.Prime 8269 := by norm_num
private theorem prime_8273 : Nat.Prime 8273 := by norm_num
private theorem prime_8287 : Nat.Prime 8287 := by norm_num
private theorem prime_8291 : Nat.Prime 8291 := by norm_num
private theorem prime_8293 : Nat.Prime 8293 := by norm_num
private theorem prime_8297 : Nat.Prime 8297 := by norm_num
private theorem prime_8311 : Nat.Prime 8311 := by norm_num
private theorem prime_8317 : Nat.Prime 8317 := by norm_num
private theorem prime_8329 : Nat.Prime 8329 := by norm_num
private theorem prime_8353 : Nat.Prime 8353 := by norm_num
private theorem prime_8363 : Nat.Prime 8363 := by norm_num
private theorem prime_8369 : Nat.Prime 8369 := by norm_num
private theorem prime_8377 : Nat.Prime 8377 := by norm_num
private theorem prime_8387 : Nat.Prime 8387 := by norm_num
private theorem prime_8389 : Nat.Prime 8389 := by norm_num
private theorem prime_8419 : Nat.Prime 8419 := by norm_num
private theorem prime_8423 : Nat.Prime 8423 := by norm_num
private theorem prime_8429 : Nat.Prime 8429 := by norm_num
private theorem prime_8431 : Nat.Prime 8431 := by norm_num
private theorem prime_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_8447 : Nat.Prime 8447 := by norm_num
private theorem prime_8461 : Nat.Prime 8461 := by norm_num
private theorem prime_8467 : Nat.Prime 8467 := by norm_num
private theorem prime_8501 : Nat.Prime 8501 := by norm_num
private theorem prime_8513 : Nat.Prime 8513 := by norm_num
private theorem prime_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_8527 : Nat.Prime 8527 := by norm_num
private theorem prime_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_8539 : Nat.Prime 8539 := by norm_num
private theorem prime_8543 : Nat.Prime 8543 := by norm_num
private theorem prime_8563 : Nat.Prime 8563 := by norm_num
private theorem prime_8573 : Nat.Prime 8573 := by norm_num
private theorem prime_8581 : Nat.Prime 8581 := by norm_num
private theorem prime_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_8599 : Nat.Prime 8599 := by norm_num
private theorem prime_8609 : Nat.Prime 8609 := by norm_num
private theorem prime_8623 : Nat.Prime 8623 := by norm_num
private theorem prime_8627 : Nat.Prime 8627 := by norm_num
private theorem prime_8629 : Nat.Prime 8629 := by norm_num
private theorem prime_8641 : Nat.Prime 8641 := by norm_num
private theorem prime_8647 : Nat.Prime 8647 := by norm_num
private theorem prime_8663 : Nat.Prime 8663 := by norm_num
private theorem prime_8669 : Nat.Prime 8669 := by norm_num
private theorem prime_8677 : Nat.Prime 8677 := by norm_num
private theorem prime_8681 : Nat.Prime 8681 := by norm_num
private theorem prime_8689 : Nat.Prime 8689 := by norm_num
private theorem prime_8693 : Nat.Prime 8693 := by norm_num
private theorem prime_8699 : Nat.Prime 8699 := by norm_num
private theorem prime_8707 : Nat.Prime 8707 := by norm_num
private theorem prime_8713 : Nat.Prime 8713 := by norm_num
private theorem prime_8719 : Nat.Prime 8719 := by norm_num
private theorem prime_8731 : Nat.Prime 8731 := by norm_num
private theorem prime_8737 : Nat.Prime 8737 := by norm_num
private theorem prime_8741 : Nat.Prime 8741 := by norm_num
private theorem prime_8747 : Nat.Prime 8747 := by norm_num
private theorem prime_8753 : Nat.Prime 8753 := by norm_num
private theorem prime_8761 : Nat.Prime 8761 := by norm_num
private theorem prime_8779 : Nat.Prime 8779 := by norm_num
private theorem prime_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_8803 : Nat.Prime 8803 := by norm_num
private theorem prime_8807 : Nat.Prime 8807 := by norm_num
private theorem prime_8819 : Nat.Prime 8819 := by norm_num
private theorem prime_8821 : Nat.Prime 8821 := by norm_num
private theorem prime_8831 : Nat.Prime 8831 := by norm_num
private theorem prime_8837 : Nat.Prime 8837 := by norm_num
private theorem prime_8839 : Nat.Prime 8839 := by norm_num
private theorem prime_8849 : Nat.Prime 8849 := by norm_num
private theorem prime_8861 : Nat.Prime 8861 := by norm_num
private theorem prime_8863 : Nat.Prime 8863 := by norm_num
private theorem prime_8867 : Nat.Prime 8867 := by norm_num
private theorem prime_8887 : Nat.Prime 8887 := by norm_num
private theorem prime_8893 : Nat.Prime 8893 := by norm_num
private theorem prime_8923 : Nat.Prime 8923 := by norm_num
private theorem prime_8929 : Nat.Prime 8929 := by norm_num
private theorem prime_8933 : Nat.Prime 8933 := by norm_num
private theorem prime_8941 : Nat.Prime 8941 := by norm_num
private theorem prime_8951 : Nat.Prime 8951 := by norm_num
private theorem prime_8963 : Nat.Prime 8963 := by norm_num
private theorem prime_8969 : Nat.Prime 8969 := by norm_num
private theorem prime_8971 : Nat.Prime 8971 := by norm_num
private theorem prime_8999 : Nat.Prime 8999 := by norm_num
private theorem prime_9001 : Nat.Prime 9001 := by norm_num
private theorem prime_9007 : Nat.Prime 9007 := by norm_num
private theorem prime_9011 : Nat.Prime 9011 := by norm_num
private theorem prime_9013 : Nat.Prime 9013 := by norm_num
private theorem prime_9029 : Nat.Prime 9029 := by norm_num
private theorem prime_9041 : Nat.Prime 9041 := by norm_num
private theorem prime_9043 : Nat.Prime 9043 := by norm_num
private theorem prime_9049 : Nat.Prime 9049 := by norm_num
private theorem prime_9059 : Nat.Prime 9059 := by norm_num
private theorem prime_9067 : Nat.Prime 9067 := by norm_num
private theorem prime_9091 : Nat.Prime 9091 := by norm_num
private theorem prime_9103 : Nat.Prime 9103 := by norm_num
private theorem prime_9109 : Nat.Prime 9109 := by norm_num
private theorem prime_9127 : Nat.Prime 9127 := by norm_num
private theorem prime_9133 : Nat.Prime 9133 := by norm_num
private theorem prime_9137 : Nat.Prime 9137 := by norm_num
private theorem prime_9151 : Nat.Prime 9151 := by norm_num
private theorem prime_9157 : Nat.Prime 9157 := by norm_num
private theorem prime_9161 : Nat.Prime 9161 := by norm_num
private theorem prime_9173 : Nat.Prime 9173 := by norm_num
private theorem prime_9181 : Nat.Prime 9181 := by norm_num
private theorem prime_9187 : Nat.Prime 9187 := by norm_num
private theorem prime_9199 : Nat.Prime 9199 := by norm_num
private theorem prime_9203 : Nat.Prime 9203 := by norm_num
private theorem prime_9209 : Nat.Prime 9209 := by norm_num
private theorem prime_9221 : Nat.Prime 9221 := by norm_num
private theorem prime_9227 : Nat.Prime 9227 := by norm_num
private theorem prime_9239 : Nat.Prime 9239 := by norm_num
private theorem prime_9241 : Nat.Prime 9241 := by norm_num
private theorem prime_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_9277 : Nat.Prime 9277 := by norm_num
private theorem prime_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_9283 : Nat.Prime 9283 := by norm_num
private theorem prime_9293 : Nat.Prime 9293 := by norm_num
private theorem prime_9311 : Nat.Prime 9311 := by norm_num
private theorem prime_9319 : Nat.Prime 9319 := by norm_num
private theorem prime_9323 : Nat.Prime 9323 := by norm_num
private theorem prime_9337 : Nat.Prime 9337 := by norm_num
private theorem prime_9341 : Nat.Prime 9341 := by norm_num
private theorem prime_9343 : Nat.Prime 9343 := by norm_num
private theorem prime_9349 : Nat.Prime 9349 := by norm_num
private theorem prime_9371 : Nat.Prime 9371 := by norm_num
private theorem prime_9377 : Nat.Prime 9377 := by norm_num
private theorem prime_9391 : Nat.Prime 9391 := by norm_num
private theorem prime_9397 : Nat.Prime 9397 := by norm_num
private theorem prime_9403 : Nat.Prime 9403 := by norm_num
private theorem prime_9413 : Nat.Prime 9413 := by norm_num
private theorem prime_9419 : Nat.Prime 9419 := by norm_num
private theorem prime_9421 : Nat.Prime 9421 := by norm_num
private theorem prime_9431 : Nat.Prime 9431 := by norm_num
private theorem prime_9433 : Nat.Prime 9433 := by norm_num
private theorem prime_9437 : Nat.Prime 9437 := by norm_num
private theorem prime_9439 : Nat.Prime 9439 := by norm_num
private theorem prime_9461 : Nat.Prime 9461 := by norm_num
private theorem prime_9463 : Nat.Prime 9463 := by norm_num
private theorem prime_9467 : Nat.Prime 9467 := by norm_num
private theorem prime_9473 : Nat.Prime 9473 := by norm_num
private theorem prime_9479 : Nat.Prime 9479 := by norm_num
private theorem prime_9491 : Nat.Prime 9491 := by norm_num
private theorem prime_9497 : Nat.Prime 9497 := by norm_num
private theorem prime_9511 : Nat.Prime 9511 := by norm_num
private theorem prime_9521 : Nat.Prime 9521 := by norm_num
private theorem prime_9533 : Nat.Prime 9533 := by norm_num
private theorem prime_9539 : Nat.Prime 9539 := by norm_num
private theorem prime_9547 : Nat.Prime 9547 := by norm_num
private theorem prime_9551 : Nat.Prime 9551 := by norm_num
private theorem prime_9587 : Nat.Prime 9587 := by norm_num
private theorem prime_9601 : Nat.Prime 9601 := by norm_num
private theorem prime_9613 : Nat.Prime 9613 := by norm_num
private theorem prime_9619 : Nat.Prime 9619 := by norm_num
private theorem prime_9623 : Nat.Prime 9623 := by norm_num
private theorem prime_9629 : Nat.Prime 9629 := by norm_num
private theorem prime_9631 : Nat.Prime 9631 := by norm_num
private theorem prime_9643 : Nat.Prime 9643 := by norm_num
private theorem prime_9649 : Nat.Prime 9649 := by norm_num
private theorem prime_9661 : Nat.Prime 9661 := by norm_num
private theorem prime_9677 : Nat.Prime 9677 := by norm_num
private theorem prime_9679 : Nat.Prime 9679 := by norm_num
private theorem prime_9689 : Nat.Prime 9689 := by norm_num
private theorem prime_9697 : Nat.Prime 9697 := by norm_num
private theorem prime_9719 : Nat.Prime 9719 := by norm_num
private theorem prime_9721 : Nat.Prime 9721 := by norm_num
private theorem prime_9733 : Nat.Prime 9733 := by norm_num
private theorem prime_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_9743 : Nat.Prime 9743 := by norm_num
private theorem prime_9749 : Nat.Prime 9749 := by norm_num
private theorem prime_9767 : Nat.Prime 9767 := by norm_num
private theorem prime_9769 : Nat.Prime 9769 := by norm_num
private theorem prime_9781 : Nat.Prime 9781 := by norm_num
private theorem prime_9787 : Nat.Prime 9787 := by norm_num
private theorem prime_9791 : Nat.Prime 9791 := by norm_num
private theorem prime_9803 : Nat.Prime 9803 := by norm_num
private theorem prime_9811 : Nat.Prime 9811 := by norm_num
private theorem prime_9817 : Nat.Prime 9817 := by norm_num
private theorem prime_9829 : Nat.Prime 9829 := by norm_num
private theorem prime_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_9839 : Nat.Prime 9839 := by norm_num
private theorem prime_9851 : Nat.Prime 9851 := by norm_num
private theorem prime_9857 : Nat.Prime 9857 := by norm_num
private theorem prime_9859 : Nat.Prime 9859 := by norm_num
private theorem prime_9871 : Nat.Prime 9871 := by norm_num
private theorem prime_9883 : Nat.Prime 9883 := by norm_num
private theorem prime_9887 : Nat.Prime 9887 := by norm_num
private theorem prime_9901 : Nat.Prime 9901 := by norm_num
private theorem prime_9907 : Nat.Prime 9907 := by norm_num
private theorem prime_9923 : Nat.Prime 9923 := by norm_num
private theorem prime_9929 : Nat.Prime 9929 := by norm_num
private theorem prime_9931 : Nat.Prime 9931 := by norm_num
private theorem prime_9941 : Nat.Prime 9941 := by norm_num
private theorem prime_9949 : Nat.Prime 9949 := by norm_num
private theorem prime_9967 : Nat.Prime 9967 := by norm_num
private theorem prime_9973 : Nat.Prime 9973 := by norm_num
private theorem prime_10007 : Nat.Prime 10007 := by norm_num
private theorem prime_10009 : Nat.Prime 10009 := by norm_num
private theorem prime_10037 : Nat.Prime 10037 := by norm_num
private theorem prime_10039 : Nat.Prime 10039 := by norm_num
private theorem prime_10061 : Nat.Prime 10061 := by norm_num
private theorem prime_10067 : Nat.Prime 10067 := by norm_num
private theorem prime_10069 : Nat.Prime 10069 := by norm_num
private theorem prime_10079 : Nat.Prime 10079 := by norm_num
private theorem prime_10091 : Nat.Prime 10091 := by norm_num
private theorem prime_10093 : Nat.Prime 10093 := by norm_num
private theorem prime_10099 : Nat.Prime 10099 := by norm_num
private theorem prime_10103 : Nat.Prime 10103 := by norm_num
private theorem prime_10111 : Nat.Prime 10111 := by norm_num
private theorem prime_10133 : Nat.Prime 10133 := by norm_num
private theorem prime_10139 : Nat.Prime 10139 := by norm_num
private theorem prime_10141 : Nat.Prime 10141 := by norm_num
private theorem prime_10151 : Nat.Prime 10151 := by norm_num
private theorem prime_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_10163 : Nat.Prime 10163 := by norm_num
private theorem prime_10169 : Nat.Prime 10169 := by norm_num
private theorem prime_10177 : Nat.Prime 10177 := by norm_num
private theorem prime_10181 : Nat.Prime 10181 := by norm_num
private theorem prime_10193 : Nat.Prime 10193 := by norm_num
private theorem prime_10211 : Nat.Prime 10211 := by norm_num
private theorem prime_10223 : Nat.Prime 10223 := by norm_num
private theorem prime_10243 : Nat.Prime 10243 := by norm_num
private theorem prime_10247 : Nat.Prime 10247 := by norm_num
private theorem prime_10253 : Nat.Prime 10253 := by norm_num
private theorem prime_10259 : Nat.Prime 10259 := by norm_num
private theorem prime_10267 : Nat.Prime 10267 := by norm_num
private theorem prime_10271 : Nat.Prime 10271 := by norm_num
private theorem prime_10273 : Nat.Prime 10273 := by norm_num
private theorem prime_10289 : Nat.Prime 10289 := by norm_num
private theorem prime_10301 : Nat.Prime 10301 := by norm_num
private theorem prime_10303 : Nat.Prime 10303 := by norm_num
private theorem prime_10313 : Nat.Prime 10313 := by norm_num
private theorem prime_10321 : Nat.Prime 10321 := by norm_num
private theorem prime_10331 : Nat.Prime 10331 := by norm_num
private theorem prime_10333 : Nat.Prime 10333 := by norm_num
private theorem prime_10337 : Nat.Prime 10337 := by norm_num
private theorem prime_10343 : Nat.Prime 10343 := by norm_num
private theorem prime_10357 : Nat.Prime 10357 := by norm_num
private theorem prime_10369 : Nat.Prime 10369 := by norm_num
private theorem prime_10391 : Nat.Prime 10391 := by norm_num
private theorem prime_10399 : Nat.Prime 10399 := by norm_num
private theorem prime_10427 : Nat.Prime 10427 := by norm_num
private theorem prime_10429 : Nat.Prime 10429 := by norm_num
private theorem prime_10433 : Nat.Prime 10433 := by norm_num
private theorem prime_10453 : Nat.Prime 10453 := by norm_num
private theorem prime_10457 : Nat.Prime 10457 := by norm_num
private theorem prime_10459 : Nat.Prime 10459 := by norm_num
private theorem prime_10463 : Nat.Prime 10463 := by norm_num
private theorem prime_10477 : Nat.Prime 10477 := by norm_num
private theorem prime_10487 : Nat.Prime 10487 := by norm_num
private theorem prime_10499 : Nat.Prime 10499 := by norm_num
private theorem prime_10501 : Nat.Prime 10501 := by norm_num
private theorem prime_10513 : Nat.Prime 10513 := by norm_num
private theorem prime_10529 : Nat.Prime 10529 := by norm_num
private theorem prime_10531 : Nat.Prime 10531 := by norm_num
private theorem prime_10559 : Nat.Prime 10559 := by norm_num
private theorem prime_10567 : Nat.Prime 10567 := by norm_num
private theorem prime_10589 : Nat.Prime 10589 := by norm_num
private theorem prime_10597 : Nat.Prime 10597 := by norm_num
private theorem prime_10601 : Nat.Prime 10601 := by norm_num
private theorem prime_10607 : Nat.Prime 10607 := by norm_num
private theorem prime_10613 : Nat.Prime 10613 := by norm_num
private theorem prime_10627 : Nat.Prime 10627 := by norm_num
private theorem prime_10631 : Nat.Prime 10631 := by norm_num
private theorem prime_10639 : Nat.Prime 10639 := by norm_num
private theorem prime_10651 : Nat.Prime 10651 := by norm_num
private theorem prime_10657 : Nat.Prime 10657 := by norm_num
private theorem prime_10663 : Nat.Prime 10663 := by norm_num
private theorem prime_10667 : Nat.Prime 10667 := by norm_num
private theorem prime_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_10709 : Nat.Prime 10709 := by norm_num
private theorem prime_10711 : Nat.Prime 10711 := by norm_num
private theorem prime_10723 : Nat.Prime 10723 := by norm_num
private theorem prime_10729 : Nat.Prime 10729 := by norm_num
private theorem prime_10733 : Nat.Prime 10733 := by norm_num
private theorem prime_10739 : Nat.Prime 10739 := by norm_num
private theorem prime_10753 : Nat.Prime 10753 := by norm_num
private theorem prime_10771 : Nat.Prime 10771 := by norm_num
private theorem prime_10781 : Nat.Prime 10781 := by norm_num
private theorem prime_10789 : Nat.Prime 10789 := by norm_num
private theorem prime_10799 : Nat.Prime 10799 := by norm_num
private theorem prime_10831 : Nat.Prime 10831 := by norm_num
private theorem prime_10837 : Nat.Prime 10837 := by norm_num
private theorem prime_10847 : Nat.Prime 10847 := by norm_num
private theorem prime_10853 : Nat.Prime 10853 := by norm_num
private theorem prime_10859 : Nat.Prime 10859 := by norm_num
private theorem prime_10861 : Nat.Prime 10861 := by norm_num
private theorem prime_10867 : Nat.Prime 10867 := by norm_num
private theorem prime_10883 : Nat.Prime 10883 := by norm_num
private theorem prime_10889 : Nat.Prime 10889 := by norm_num
private theorem prime_10891 : Nat.Prime 10891 := by norm_num
private theorem prime_10903 : Nat.Prime 10903 := by norm_num
private theorem prime_10909 : Nat.Prime 10909 := by norm_num
private theorem prime_10937 : Nat.Prime 10937 := by norm_num
private theorem prime_10939 : Nat.Prime 10939 := by norm_num
private theorem prime_10949 : Nat.Prime 10949 := by norm_num
private theorem prime_10957 : Nat.Prime 10957 := by norm_num
private theorem prime_10973 : Nat.Prime 10973 := by norm_num
private theorem prime_10979 : Nat.Prime 10979 := by norm_num
private theorem prime_10987 : Nat.Prime 10987 := by norm_num
private theorem prime_10993 : Nat.Prime 10993 := by norm_num
private theorem prime_11003 : Nat.Prime 11003 := by norm_num
private theorem prime_11027 : Nat.Prime 11027 := by norm_num
private theorem prime_11047 : Nat.Prime 11047 := by norm_num
private theorem prime_11057 : Nat.Prime 11057 := by norm_num
private theorem prime_11059 : Nat.Prime 11059 := by norm_num
private theorem prime_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_11071 : Nat.Prime 11071 := by norm_num
private theorem prime_11083 : Nat.Prime 11083 := by norm_num
private theorem prime_11087 : Nat.Prime 11087 := by norm_num
private theorem prime_11093 : Nat.Prime 11093 := by norm_num
private theorem prime_11113 : Nat.Prime 11113 := by norm_num
private theorem prime_11117 : Nat.Prime 11117 := by norm_num
private theorem prime_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_11131 : Nat.Prime 11131 := by norm_num
private theorem prime_11149 : Nat.Prime 11149 := by norm_num
private theorem prime_11159 : Nat.Prime 11159 := by norm_num
private theorem prime_11161 : Nat.Prime 11161 := by norm_num
private theorem prime_11171 : Nat.Prime 11171 := by norm_num
private theorem prime_11173 : Nat.Prime 11173 := by norm_num
private theorem prime_11177 : Nat.Prime 11177 := by norm_num
private theorem prime_11197 : Nat.Prime 11197 := by norm_num
private theorem prime_11213 : Nat.Prime 11213 := by norm_num
private theorem prime_11239 : Nat.Prime 11239 := by norm_num
private theorem prime_11243 : Nat.Prime 11243 := by norm_num
private theorem prime_11251 : Nat.Prime 11251 := by norm_num
private theorem prime_11257 : Nat.Prime 11257 := by norm_num
private theorem prime_11261 : Nat.Prime 11261 := by norm_num
private theorem prime_11273 : Nat.Prime 11273 := by norm_num
private theorem prime_11279 : Nat.Prime 11279 := by norm_num
private theorem prime_11287 : Nat.Prime 11287 := by norm_num
private theorem prime_11299 : Nat.Prime 11299 := by norm_num
private theorem prime_11311 : Nat.Prime 11311 := by norm_num
private theorem prime_11317 : Nat.Prime 11317 := by norm_num
private theorem prime_11321 : Nat.Prime 11321 := by norm_num
private theorem prime_11329 : Nat.Prime 11329 := by norm_num
private theorem prime_11351 : Nat.Prime 11351 := by norm_num
private theorem prime_11353 : Nat.Prime 11353 := by norm_num
private theorem prime_11369 : Nat.Prime 11369 := by norm_num
private theorem prime_11383 : Nat.Prime 11383 := by norm_num
private theorem prime_11393 : Nat.Prime 11393 := by norm_num
private theorem prime_11399 : Nat.Prime 11399 := by norm_num
private theorem prime_11411 : Nat.Prime 11411 := by norm_num
private theorem prime_11423 : Nat.Prime 11423 := by norm_num
private theorem prime_11437 : Nat.Prime 11437 := by norm_num
private theorem prime_11443 : Nat.Prime 11443 := by norm_num
private theorem prime_11447 : Nat.Prime 11447 := by norm_num
private theorem prime_11467 : Nat.Prime 11467 := by norm_num
private theorem prime_11471 : Nat.Prime 11471 := by norm_num
private theorem prime_11483 : Nat.Prime 11483 := by norm_num
private theorem prime_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_11491 : Nat.Prime 11491 := by norm_num
private theorem prime_11497 : Nat.Prime 11497 := by norm_num
private theorem prime_11503 : Nat.Prime 11503 := by norm_num
private theorem prime_11519 : Nat.Prime 11519 := by norm_num
private theorem prime_11527 : Nat.Prime 11527 := by norm_num
private theorem prime_11549 : Nat.Prime 11549 := by norm_num
private theorem prime_11551 : Nat.Prime 11551 := by norm_num
private theorem prime_11579 : Nat.Prime 11579 := by norm_num
private theorem prime_11587 : Nat.Prime 11587 := by norm_num
private theorem prime_11593 : Nat.Prime 11593 := by norm_num
private theorem prime_11597 : Nat.Prime 11597 := by norm_num
private theorem prime_11617 : Nat.Prime 11617 := by norm_num
private theorem prime_11621 : Nat.Prime 11621 := by norm_num
private theorem prime_11633 : Nat.Prime 11633 := by norm_num
private theorem prime_11657 : Nat.Prime 11657 := by norm_num
private theorem prime_11677 : Nat.Prime 11677 := by norm_num
private theorem prime_11681 : Nat.Prime 11681 := by norm_num
private theorem prime_11689 : Nat.Prime 11689 := by norm_num
private theorem prime_11699 : Nat.Prime 11699 := by norm_num
private theorem prime_11701 : Nat.Prime 11701 := by norm_num
private theorem prime_11717 : Nat.Prime 11717 := by norm_num
private theorem prime_11719 : Nat.Prime 11719 := by norm_num
private theorem prime_11731 : Nat.Prime 11731 := by norm_num
private theorem prime_11743 : Nat.Prime 11743 := by norm_num
private theorem prime_11777 : Nat.Prime 11777 := by norm_num
private theorem prime_11779 : Nat.Prime 11779 := by norm_num
private theorem prime_11783 : Nat.Prime 11783 := by norm_num
private theorem prime_11789 : Nat.Prime 11789 := by norm_num
private theorem prime_11801 : Nat.Prime 11801 := by norm_num
private theorem prime_11807 : Nat.Prime 11807 := by norm_num
private theorem prime_11813 : Nat.Prime 11813 := by norm_num
private theorem prime_11821 : Nat.Prime 11821 := by norm_num
private theorem prime_11827 : Nat.Prime 11827 := by norm_num
private theorem prime_11831 : Nat.Prime 11831 := by norm_num
private theorem prime_11833 : Nat.Prime 11833 := by norm_num
private theorem prime_11839 : Nat.Prime 11839 := by norm_num
private theorem prime_11863 : Nat.Prime 11863 := by norm_num
private theorem prime_11867 : Nat.Prime 11867 := by norm_num
private theorem prime_11887 : Nat.Prime 11887 := by norm_num
private theorem prime_11897 : Nat.Prime 11897 := by norm_num
private theorem prime_11903 : Nat.Prime 11903 := by norm_num
private theorem prime_11909 : Nat.Prime 11909 := by norm_num
private theorem prime_11923 : Nat.Prime 11923 := by norm_num
private theorem prime_11927 : Nat.Prime 11927 := by norm_num
private theorem prime_11933 : Nat.Prime 11933 := by norm_num
private theorem prime_11939 : Nat.Prime 11939 := by norm_num
private theorem prime_11941 : Nat.Prime 11941 := by norm_num
private theorem prime_11953 : Nat.Prime 11953 := by norm_num
private theorem prime_11959 : Nat.Prime 11959 := by norm_num
private theorem prime_11969 : Nat.Prime 11969 := by norm_num
private theorem prime_11971 : Nat.Prime 11971 := by norm_num
private theorem prime_11981 : Nat.Prime 11981 := by norm_num
private theorem prime_11987 : Nat.Prime 11987 := by norm_num
private theorem prime_12007 : Nat.Prime 12007 := by norm_num
private theorem prime_12011 : Nat.Prime 12011 := by norm_num
private theorem prime_12037 : Nat.Prime 12037 := by norm_num
private theorem prime_12041 : Nat.Prime 12041 := by norm_num
private theorem prime_12043 : Nat.Prime 12043 := by norm_num
private theorem prime_12049 : Nat.Prime 12049 := by norm_num
private theorem prime_12071 : Nat.Prime 12071 := by norm_num
private theorem prime_12073 : Nat.Prime 12073 := by norm_num
private theorem prime_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_12101 : Nat.Prime 12101 := by norm_num
private theorem prime_12107 : Nat.Prime 12107 := by norm_num
private theorem prime_12109 : Nat.Prime 12109 := by norm_num
private theorem prime_12113 : Nat.Prime 12113 := by norm_num
private theorem prime_12119 : Nat.Prime 12119 := by norm_num
private theorem prime_12143 : Nat.Prime 12143 := by norm_num
private theorem prime_12149 : Nat.Prime 12149 := by norm_num
private theorem prime_12157 : Nat.Prime 12157 := by norm_num
private theorem prime_12161 : Nat.Prime 12161 := by norm_num
private theorem prime_12163 : Nat.Prime 12163 := by norm_num
private theorem prime_12197 : Nat.Prime 12197 := by norm_num
private theorem prime_12203 : Nat.Prime 12203 := by norm_num
private theorem prime_12211 : Nat.Prime 12211 := by norm_num
private theorem prime_12227 : Nat.Prime 12227 := by norm_num
private theorem prime_12239 : Nat.Prime 12239 := by norm_num
private theorem prime_12241 : Nat.Prime 12241 := by norm_num
private theorem prime_12251 : Nat.Prime 12251 := by norm_num
private theorem prime_12253 : Nat.Prime 12253 := by norm_num
private theorem prime_12263 : Nat.Prime 12263 := by norm_num
private theorem prime_12269 : Nat.Prime 12269 := by norm_num
private theorem prime_12277 : Nat.Prime 12277 := by norm_num
private theorem prime_12281 : Nat.Prime 12281 := by norm_num
private theorem prime_12289 : Nat.Prime 12289 := by norm_num
private theorem prime_12301 : Nat.Prime 12301 := by norm_num
private theorem prime_12323 : Nat.Prime 12323 := by norm_num
private theorem prime_12329 : Nat.Prime 12329 := by norm_num
private theorem prime_12343 : Nat.Prime 12343 := by norm_num
private theorem prime_12347 : Nat.Prime 12347 := by norm_num
private theorem prime_12373 : Nat.Prime 12373 := by norm_num
private theorem prime_12377 : Nat.Prime 12377 := by norm_num
private theorem prime_12379 : Nat.Prime 12379 := by norm_num
private theorem prime_12391 : Nat.Prime 12391 := by norm_num
private theorem prime_12401 : Nat.Prime 12401 := by norm_num
private theorem prime_12409 : Nat.Prime 12409 := by norm_num
private theorem prime_12413 : Nat.Prime 12413 := by norm_num
private theorem prime_12421 : Nat.Prime 12421 := by norm_num
private theorem prime_12433 : Nat.Prime 12433 := by norm_num
private theorem prime_12437 : Nat.Prime 12437 := by norm_num
private theorem prime_12451 : Nat.Prime 12451 := by norm_num
private theorem prime_12457 : Nat.Prime 12457 := by norm_num
private theorem prime_12473 : Nat.Prime 12473 := by norm_num
private theorem prime_12479 : Nat.Prime 12479 := by norm_num
private theorem prime_12487 : Nat.Prime 12487 := by norm_num
private theorem prime_12491 : Nat.Prime 12491 := by norm_num
private theorem prime_12497 : Nat.Prime 12497 := by norm_num
private theorem prime_12503 : Nat.Prime 12503 := by norm_num
private theorem prime_12511 : Nat.Prime 12511 := by norm_num
private theorem prime_12517 : Nat.Prime 12517 := by norm_num
private theorem prime_12527 : Nat.Prime 12527 := by norm_num
private theorem prime_12539 : Nat.Prime 12539 := by norm_num
private theorem prime_12541 : Nat.Prime 12541 := by norm_num
private theorem prime_12547 : Nat.Prime 12547 := by norm_num
private theorem prime_12553 : Nat.Prime 12553 := by norm_num
private theorem prime_12569 : Nat.Prime 12569 := by norm_num
private theorem prime_12577 : Nat.Prime 12577 := by norm_num
private theorem prime_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_12589 : Nat.Prime 12589 := by norm_num
private theorem prime_12601 : Nat.Prime 12601 := by norm_num
private theorem prime_12611 : Nat.Prime 12611 := by norm_num
private theorem prime_12613 : Nat.Prime 12613 := by norm_num
private theorem prime_12619 : Nat.Prime 12619 := by norm_num
private theorem prime_12637 : Nat.Prime 12637 := by norm_num
private theorem prime_12641 : Nat.Prime 12641 := by norm_num
private theorem prime_12647 : Nat.Prime 12647 := by norm_num
private theorem prime_12653 : Nat.Prime 12653 := by norm_num
private theorem prime_12659 : Nat.Prime 12659 := by norm_num
private theorem prime_12671 : Nat.Prime 12671 := by norm_num
private theorem prime_12689 : Nat.Prime 12689 := by norm_num
private theorem prime_12697 : Nat.Prime 12697 := by norm_num
private theorem prime_12703 : Nat.Prime 12703 := by norm_num
private theorem prime_12713 : Nat.Prime 12713 := by norm_num
private theorem prime_12721 : Nat.Prime 12721 := by norm_num
private theorem prime_12739 : Nat.Prime 12739 := by norm_num
private theorem prime_12743 : Nat.Prime 12743 := by norm_num
private theorem prime_12757 : Nat.Prime 12757 := by norm_num
private theorem prime_12763 : Nat.Prime 12763 := by norm_num
private theorem prime_12781 : Nat.Prime 12781 := by norm_num
private theorem prime_12791 : Nat.Prime 12791 := by norm_num
private theorem prime_12799 : Nat.Prime 12799 := by norm_num
private theorem prime_12809 : Nat.Prime 12809 := by norm_num
private theorem prime_12821 : Nat.Prime 12821 := by norm_num
private theorem prime_12823 : Nat.Prime 12823 := by norm_num
private theorem prime_12829 : Nat.Prime 12829 := by norm_num
private theorem prime_12841 : Nat.Prime 12841 := by norm_num
private theorem prime_12853 : Nat.Prime 12853 := by norm_num
private theorem prime_12889 : Nat.Prime 12889 := by norm_num
private theorem prime_12893 : Nat.Prime 12893 := by norm_num
private theorem prime_12899 : Nat.Prime 12899 := by norm_num
private theorem prime_12907 : Nat.Prime 12907 := by norm_num
private theorem prime_12911 : Nat.Prime 12911 := by norm_num
private theorem prime_12917 : Nat.Prime 12917 := by norm_num
private theorem prime_12919 : Nat.Prime 12919 := by norm_num
private theorem prime_12923 : Nat.Prime 12923 := by norm_num
private theorem prime_12941 : Nat.Prime 12941 := by norm_num
private theorem prime_12953 : Nat.Prime 12953 := by norm_num
private theorem prime_12959 : Nat.Prime 12959 := by norm_num
private theorem prime_12967 : Nat.Prime 12967 := by norm_num
private theorem prime_12973 : Nat.Prime 12973 := by norm_num
private theorem prime_12979 : Nat.Prime 12979 := by norm_num
private theorem prime_12983 : Nat.Prime 12983 := by norm_num
private theorem prime_13001 : Nat.Prime 13001 := by norm_num
private theorem prime_13003 : Nat.Prime 13003 := by norm_num
private theorem prime_13007 : Nat.Prime 13007 := by norm_num
private theorem prime_13009 : Nat.Prime 13009 := by norm_num
private theorem prime_13033 : Nat.Prime 13033 := by norm_num
private theorem prime_13037 : Nat.Prime 13037 := by norm_num
private theorem prime_13043 : Nat.Prime 13043 := by norm_num
private theorem prime_13049 : Nat.Prime 13049 := by norm_num
private theorem prime_13063 : Nat.Prime 13063 := by norm_num
private theorem prime_13093 : Nat.Prime 13093 := by norm_num
private theorem prime_13099 : Nat.Prime 13099 := by norm_num
private theorem prime_13103 : Nat.Prime 13103 := by norm_num
private theorem prime_13109 : Nat.Prime 13109 := by norm_num
private theorem prime_13121 : Nat.Prime 13121 := by norm_num
private theorem prime_13127 : Nat.Prime 13127 := by norm_num
private theorem prime_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_13151 : Nat.Prime 13151 := by norm_num
private theorem prime_13159 : Nat.Prime 13159 := by norm_num
private theorem prime_13163 : Nat.Prime 13163 := by norm_num
private theorem prime_13171 : Nat.Prime 13171 := by norm_num
private theorem prime_13177 : Nat.Prime 13177 := by norm_num
private theorem prime_13183 : Nat.Prime 13183 := by norm_num
private theorem prime_13187 : Nat.Prime 13187 := by norm_num
private theorem prime_13217 : Nat.Prime 13217 := by norm_num
private theorem prime_13219 : Nat.Prime 13219 := by norm_num
private theorem prime_13229 : Nat.Prime 13229 := by norm_num
private theorem prime_13241 : Nat.Prime 13241 := by norm_num
private theorem prime_13249 : Nat.Prime 13249 := by norm_num
private theorem prime_13259 : Nat.Prime 13259 := by norm_num
private theorem prime_13267 : Nat.Prime 13267 := by norm_num
private theorem prime_13291 : Nat.Prime 13291 := by norm_num
private theorem prime_13297 : Nat.Prime 13297 := by norm_num
private theorem prime_13309 : Nat.Prime 13309 := by norm_num
private theorem prime_13313 : Nat.Prime 13313 := by norm_num
private theorem prime_13327 : Nat.Prime 13327 := by norm_num
private theorem prime_13331 : Nat.Prime 13331 := by norm_num
private theorem prime_13337 : Nat.Prime 13337 := by norm_num
private theorem prime_13339 : Nat.Prime 13339 := by norm_num
private theorem prime_13367 : Nat.Prime 13367 := by norm_num
private theorem prime_13381 : Nat.Prime 13381 := by norm_num
private theorem prime_13397 : Nat.Prime 13397 := by norm_num
private theorem prime_13399 : Nat.Prime 13399 := by norm_num
private theorem prime_13411 : Nat.Prime 13411 := by norm_num
private theorem prime_13417 : Nat.Prime 13417 := by norm_num
private theorem prime_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_13441 : Nat.Prime 13441 := by norm_num
private theorem prime_13451 : Nat.Prime 13451 := by norm_num
private theorem prime_13457 : Nat.Prime 13457 := by norm_num
private theorem prime_13463 : Nat.Prime 13463 := by norm_num
private theorem prime_13469 : Nat.Prime 13469 := by norm_num
private theorem prime_13477 : Nat.Prime 13477 := by norm_num
private theorem prime_13487 : Nat.Prime 13487 := by norm_num
private theorem prime_13499 : Nat.Prime 13499 := by norm_num
private theorem prime_13513 : Nat.Prime 13513 := by norm_num
private theorem prime_13523 : Nat.Prime 13523 := by norm_num
private theorem prime_13537 : Nat.Prime 13537 := by norm_num
private theorem prime_13553 : Nat.Prime 13553 := by norm_num
private theorem prime_13567 : Nat.Prime 13567 := by norm_num
private theorem prime_13577 : Nat.Prime 13577 := by norm_num
private theorem prime_13591 : Nat.Prime 13591 := by norm_num
private theorem prime_13597 : Nat.Prime 13597 := by norm_num
private theorem prime_13613 : Nat.Prime 13613 := by norm_num
private theorem prime_13619 : Nat.Prime 13619 := by norm_num
private theorem prime_13627 : Nat.Prime 13627 := by norm_num
private theorem prime_13633 : Nat.Prime 13633 := by norm_num
private theorem prime_13649 : Nat.Prime 13649 := by norm_num
private theorem prime_13669 : Nat.Prime 13669 := by norm_num
private theorem prime_13679 : Nat.Prime 13679 := by norm_num
private theorem prime_13681 : Nat.Prime 13681 := by norm_num
private theorem prime_13687 : Nat.Prime 13687 := by norm_num
private theorem prime_13691 : Nat.Prime 13691 := by norm_num
private theorem prime_13693 : Nat.Prime 13693 := by norm_num
private theorem prime_13697 : Nat.Prime 13697 := by norm_num
private theorem prime_13709 : Nat.Prime 13709 := by norm_num
private theorem prime_13711 : Nat.Prime 13711 := by norm_num
private theorem prime_13721 : Nat.Prime 13721 := by norm_num
private theorem prime_13723 : Nat.Prime 13723 := by norm_num
private theorem prime_13729 : Nat.Prime 13729 := by norm_num
private theorem prime_13751 : Nat.Prime 13751 := by norm_num
private theorem prime_13757 : Nat.Prime 13757 := by norm_num
private theorem prime_13759 : Nat.Prime 13759 := by norm_num
private theorem prime_13763 : Nat.Prime 13763 := by norm_num
private theorem prime_13781 : Nat.Prime 13781 := by norm_num
private theorem prime_13789 : Nat.Prime 13789 := by norm_num
private theorem prime_13799 : Nat.Prime 13799 := by norm_num
private theorem prime_13807 : Nat.Prime 13807 := by norm_num
private theorem prime_13829 : Nat.Prime 13829 := by norm_num
private theorem prime_13831 : Nat.Prime 13831 := by norm_num
private theorem prime_13841 : Nat.Prime 13841 := by norm_num
private theorem prime_13859 : Nat.Prime 13859 := by norm_num
private theorem prime_13873 : Nat.Prime 13873 := by norm_num
private theorem prime_13877 : Nat.Prime 13877 := by norm_num
private theorem prime_13879 : Nat.Prime 13879 := by norm_num
private theorem prime_13883 : Nat.Prime 13883 := by norm_num
private theorem prime_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_13903 : Nat.Prime 13903 := by norm_num
private theorem prime_13907 : Nat.Prime 13907 := by norm_num
private theorem prime_13913 : Nat.Prime 13913 := by norm_num
private theorem prime_13921 : Nat.Prime 13921 := by norm_num
private theorem prime_13931 : Nat.Prime 13931 := by norm_num
private theorem prime_13933 : Nat.Prime 13933 := by norm_num
private theorem prime_13963 : Nat.Prime 13963 := by norm_num
private theorem prime_13967 : Nat.Prime 13967 := by norm_num
private theorem prime_13997 : Nat.Prime 13997 := by norm_num
private theorem prime_13999 : Nat.Prime 13999 := by norm_num
private theorem prime_14009 : Nat.Prime 14009 := by norm_num
private theorem prime_14011 : Nat.Prime 14011 := by norm_num
private theorem prime_14029 : Nat.Prime 14029 := by norm_num
private theorem prime_14033 : Nat.Prime 14033 := by norm_num
private theorem prime_14051 : Nat.Prime 14051 := by norm_num
private theorem prime_14057 : Nat.Prime 14057 := by norm_num
private theorem prime_14071 : Nat.Prime 14071 := by norm_num
private theorem prime_14081 : Nat.Prime 14081 := by norm_num
private theorem prime_14083 : Nat.Prime 14083 := by norm_num
private theorem prime_14087 : Nat.Prime 14087 := by norm_num
private theorem prime_14107 : Nat.Prime 14107 := by norm_num
private theorem prime_14143 : Nat.Prime 14143 := by norm_num
private theorem prime_14149 : Nat.Prime 14149 := by norm_num
private theorem prime_14153 : Nat.Prime 14153 := by norm_num
private theorem prime_14159 : Nat.Prime 14159 := by norm_num
private theorem prime_14173 : Nat.Prime 14173 := by norm_num
private theorem prime_14177 : Nat.Prime 14177 := by norm_num
private theorem prime_14197 : Nat.Prime 14197 := by norm_num
private theorem prime_14207 : Nat.Prime 14207 := by norm_num
private theorem prime_14221 : Nat.Prime 14221 := by norm_num
private theorem prime_14243 : Nat.Prime 14243 := by norm_num
private theorem prime_14249 : Nat.Prime 14249 := by norm_num
private theorem prime_14251 : Nat.Prime 14251 := by norm_num
private theorem prime_14281 : Nat.Prime 14281 := by norm_num
private theorem prime_14293 : Nat.Prime 14293 := by norm_num
private theorem prime_14303 : Nat.Prime 14303 := by norm_num
private theorem prime_14321 : Nat.Prime 14321 := by norm_num
private theorem prime_14323 : Nat.Prime 14323 := by norm_num
private theorem prime_14327 : Nat.Prime 14327 := by norm_num
private theorem prime_14341 : Nat.Prime 14341 := by norm_num
private theorem prime_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_14369 : Nat.Prime 14369 := by norm_num
private theorem prime_14387 : Nat.Prime 14387 := by norm_num
private theorem prime_14389 : Nat.Prime 14389 := by norm_num
private theorem prime_14401 : Nat.Prime 14401 := by norm_num
private theorem prime_14407 : Nat.Prime 14407 := by norm_num
private theorem prime_14411 : Nat.Prime 14411 := by norm_num
private theorem prime_14419 : Nat.Prime 14419 := by norm_num
private theorem prime_14423 : Nat.Prime 14423 := by norm_num
private theorem prime_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_14437 : Nat.Prime 14437 := by norm_num
private theorem prime_14447 : Nat.Prime 14447 := by norm_num
private theorem prime_14449 : Nat.Prime 14449 := by norm_num
private theorem prime_14461 : Nat.Prime 14461 := by norm_num
private theorem prime_14479 : Nat.Prime 14479 := by norm_num
private theorem prime_14489 : Nat.Prime 14489 := by norm_num
private theorem prime_14503 : Nat.Prime 14503 := by norm_num
private theorem prime_14519 : Nat.Prime 14519 := by norm_num
private theorem prime_14533 : Nat.Prime 14533 := by norm_num
private theorem prime_14537 : Nat.Prime 14537 := by norm_num
private theorem prime_14543 : Nat.Prime 14543 := by norm_num
private theorem prime_14549 : Nat.Prime 14549 := by norm_num
private theorem prime_14551 : Nat.Prime 14551 := by norm_num
private theorem prime_14557 : Nat.Prime 14557 := by norm_num
private theorem prime_14561 : Nat.Prime 14561 := by norm_num
private theorem prime_14563 : Nat.Prime 14563 := by norm_num
private theorem prime_14591 : Nat.Prime 14591 := by norm_num
private theorem prime_14593 : Nat.Prime 14593 := by norm_num
private theorem prime_14621 : Nat.Prime 14621 := by norm_num
private theorem prime_14627 : Nat.Prime 14627 := by norm_num
private theorem prime_14629 : Nat.Prime 14629 := by norm_num
private theorem prime_14633 : Nat.Prime 14633 := by norm_num
private theorem prime_14639 : Nat.Prime 14639 := by norm_num
private theorem prime_14653 : Nat.Prime 14653 := by norm_num
private theorem prime_14657 : Nat.Prime 14657 := by norm_num
private theorem prime_14669 : Nat.Prime 14669 := by norm_num
private theorem prime_14683 : Nat.Prime 14683 := by norm_num
private theorem prime_14699 : Nat.Prime 14699 := by norm_num
private theorem prime_14713 : Nat.Prime 14713 := by norm_num
private theorem prime_14717 : Nat.Prime 14717 := by norm_num
private theorem prime_14723 : Nat.Prime 14723 := by norm_num
private theorem prime_14731 : Nat.Prime 14731 := by norm_num
private theorem prime_14737 : Nat.Prime 14737 := by norm_num
private theorem prime_14741 : Nat.Prime 14741 := by norm_num
private theorem prime_14747 : Nat.Prime 14747 := by norm_num
private theorem prime_14753 : Nat.Prime 14753 := by norm_num
private theorem prime_14759 : Nat.Prime 14759 := by norm_num
private theorem prime_14767 : Nat.Prime 14767 := by norm_num
private theorem prime_14771 : Nat.Prime 14771 := by norm_num
private theorem prime_14779 : Nat.Prime 14779 := by norm_num
private theorem prime_14783 : Nat.Prime 14783 := by norm_num
private theorem prime_14797 : Nat.Prime 14797 := by norm_num
private theorem prime_14813 : Nat.Prime 14813 := by norm_num
private theorem prime_14821 : Nat.Prime 14821 := by norm_num
private theorem prime_14827 : Nat.Prime 14827 := by norm_num
private theorem prime_14831 : Nat.Prime 14831 := by norm_num
private theorem prime_14843 : Nat.Prime 14843 := by norm_num
private theorem prime_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_14867 : Nat.Prime 14867 := by norm_num
private theorem prime_14869 : Nat.Prime 14869 := by norm_num
private theorem prime_14879 : Nat.Prime 14879 := by norm_num
private theorem prime_14887 : Nat.Prime 14887 := by norm_num
private theorem prime_14891 : Nat.Prime 14891 := by norm_num
private theorem prime_14897 : Nat.Prime 14897 := by norm_num
private theorem prime_14923 : Nat.Prime 14923 := by norm_num
private theorem prime_14929 : Nat.Prime 14929 := by norm_num
private theorem prime_14939 : Nat.Prime 14939 := by norm_num
private theorem prime_14947 : Nat.Prime 14947 := by norm_num
private theorem prime_14951 : Nat.Prime 14951 := by norm_num
private theorem prime_14957 : Nat.Prime 14957 := by norm_num
private theorem prime_14969 : Nat.Prime 14969 := by norm_num
private theorem prime_14983 : Nat.Prime 14983 := by norm_num
private theorem prime_15013 : Nat.Prime 15013 := by norm_num
private theorem prime_15017 : Nat.Prime 15017 := by norm_num
private theorem prime_15031 : Nat.Prime 15031 := by norm_num
private theorem prime_15053 : Nat.Prime 15053 := by norm_num
private theorem prime_15061 : Nat.Prime 15061 := by norm_num
private theorem prime_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_15077 : Nat.Prime 15077 := by norm_num
private theorem prime_15083 : Nat.Prime 15083 := by norm_num
private theorem prime_15091 : Nat.Prime 15091 := by norm_num
private theorem prime_15101 : Nat.Prime 15101 := by norm_num
private theorem prime_15107 : Nat.Prime 15107 := by norm_num
private theorem prime_15121 : Nat.Prime 15121 := by norm_num
private theorem prime_15131 : Nat.Prime 15131 := by norm_num
private theorem prime_15137 : Nat.Prime 15137 := by norm_num
private theorem prime_15139 : Nat.Prime 15139 := by norm_num
private theorem prime_15149 : Nat.Prime 15149 := by norm_num
private theorem prime_15161 : Nat.Prime 15161 := by norm_num
private theorem prime_15173 : Nat.Prime 15173 := by norm_num
private theorem prime_15187 : Nat.Prime 15187 := by norm_num
private theorem prime_15193 : Nat.Prime 15193 := by norm_num
private theorem prime_15199 : Nat.Prime 15199 := by norm_num
private theorem prime_15217 : Nat.Prime 15217 := by norm_num
private theorem prime_15227 : Nat.Prime 15227 := by norm_num
private theorem prime_15233 : Nat.Prime 15233 := by norm_num
private theorem prime_15241 : Nat.Prime 15241 := by norm_num
private theorem prime_15259 : Nat.Prime 15259 := by norm_num
private theorem prime_15263 : Nat.Prime 15263 := by norm_num
private theorem prime_15269 : Nat.Prime 15269 := by norm_num
private theorem prime_15271 : Nat.Prime 15271 := by norm_num
private theorem prime_15277 : Nat.Prime 15277 := by norm_num
private theorem prime_15287 : Nat.Prime 15287 := by norm_num
private theorem prime_15289 : Nat.Prime 15289 := by norm_num
private theorem prime_15299 : Nat.Prime 15299 := by norm_num
private theorem prime_15307 : Nat.Prime 15307 := by norm_num
private theorem prime_15313 : Nat.Prime 15313 := by norm_num
private theorem prime_15319 : Nat.Prime 15319 := by norm_num
private theorem prime_15329 : Nat.Prime 15329 := by norm_num
private theorem prime_15331 : Nat.Prime 15331 := by norm_num
private theorem prime_15349 : Nat.Prime 15349 := by norm_num
private theorem prime_15359 : Nat.Prime 15359 := by norm_num
private theorem prime_15361 : Nat.Prime 15361 := by norm_num
private theorem prime_15373 : Nat.Prime 15373 := by norm_num
private theorem prime_15377 : Nat.Prime 15377 := by norm_num
private theorem prime_15383 : Nat.Prime 15383 := by norm_num
private theorem prime_15391 : Nat.Prime 15391 := by norm_num
private theorem prime_15401 : Nat.Prime 15401 := by norm_num
private theorem prime_15413 : Nat.Prime 15413 := by norm_num
private theorem prime_15427 : Nat.Prime 15427 := by norm_num
private theorem prime_15439 : Nat.Prime 15439 := by norm_num
private theorem prime_15443 : Nat.Prime 15443 := by norm_num
private theorem prime_15451 : Nat.Prime 15451 := by norm_num
private theorem prime_15461 : Nat.Prime 15461 := by norm_num
private theorem prime_15467 : Nat.Prime 15467 := by norm_num
private theorem prime_15473 : Nat.Prime 15473 := by norm_num
private theorem prime_15493 : Nat.Prime 15493 := by norm_num
private theorem prime_15497 : Nat.Prime 15497 := by norm_num
private theorem prime_15511 : Nat.Prime 15511 := by norm_num
private theorem prime_15527 : Nat.Prime 15527 := by norm_num
private theorem prime_15541 : Nat.Prime 15541 := by norm_num
private theorem prime_15551 : Nat.Prime 15551 := by norm_num
private theorem prime_15559 : Nat.Prime 15559 := by norm_num
private theorem prime_15569 : Nat.Prime 15569 := by norm_num
private theorem prime_15581 : Nat.Prime 15581 := by norm_num
private theorem prime_15583 : Nat.Prime 15583 := by norm_num
private theorem prime_15601 : Nat.Prime 15601 := by norm_num
private theorem prime_15607 : Nat.Prime 15607 := by norm_num
private theorem prime_15619 : Nat.Prime 15619 := by norm_num
private theorem prime_15629 : Nat.Prime 15629 := by norm_num
private theorem prime_15641 : Nat.Prime 15641 := by norm_num
private theorem prime_15643 : Nat.Prime 15643 := by norm_num
private theorem prime_15647 : Nat.Prime 15647 := by norm_num
private theorem prime_15649 : Nat.Prime 15649 := by norm_num
private theorem prime_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_15667 : Nat.Prime 15667 := by norm_num
private theorem prime_15671 : Nat.Prime 15671 := by norm_num
private theorem prime_15679 : Nat.Prime 15679 := by norm_num
private theorem prime_15683 : Nat.Prime 15683 := by norm_num

private theorem goldbach_chunk_0 : ∀ k : ℕ, 2 ≤ k → k ≤ 101 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2, 2, prime_2, prime_2, by norm_num⟩
  · exact ⟨3, 3, prime_3, prime_3, by norm_num⟩
  · exact ⟨5, 3, prime_5, prime_3, by norm_num⟩
  · exact ⟨7, 3, prime_7, prime_3, by norm_num⟩
  · exact ⟨7, 5, prime_7, prime_5, by norm_num⟩
  · exact ⟨11, 3, prime_11, prime_3, by norm_num⟩
  · exact ⟨13, 3, prime_13, prime_3, by norm_num⟩
  · exact ⟨13, 5, prime_13, prime_5, by norm_num⟩
  · exact ⟨17, 3, prime_17, prime_3, by norm_num⟩
  · exact ⟨19, 3, prime_19, prime_3, by norm_num⟩
  · exact ⟨19, 5, prime_19, prime_5, by norm_num⟩
  · exact ⟨23, 3, prime_23, prime_3, by norm_num⟩
  · exact ⟨23, 5, prime_23, prime_5, by norm_num⟩
  · exact ⟨23, 7, prime_23, prime_7, by norm_num⟩
  · exact ⟨29, 3, prime_29, prime_3, by norm_num⟩
  · exact ⟨31, 3, prime_31, prime_3, by norm_num⟩
  · exact ⟨31, 5, prime_31, prime_5, by norm_num⟩
  · exact ⟨31, 7, prime_31, prime_7, by norm_num⟩
  · exact ⟨37, 3, prime_37, prime_3, by norm_num⟩
  · exact ⟨37, 5, prime_37, prime_5, by norm_num⟩
  · exact ⟨41, 3, prime_41, prime_3, by norm_num⟩
  · exact ⟨43, 3, prime_43, prime_3, by norm_num⟩
  · exact ⟨43, 5, prime_43, prime_5, by norm_num⟩
  · exact ⟨47, 3, prime_47, prime_3, by norm_num⟩
  · exact ⟨47, 5, prime_47, prime_5, by norm_num⟩
  · exact ⟨47, 7, prime_47, prime_7, by norm_num⟩
  · exact ⟨53, 3, prime_53, prime_3, by norm_num⟩
  · exact ⟨53, 5, prime_53, prime_5, by norm_num⟩
  · exact ⟨53, 7, prime_53, prime_7, by norm_num⟩
  · exact ⟨59, 3, prime_59, prime_3, by norm_num⟩
  · exact ⟨61, 3, prime_61, prime_3, by norm_num⟩
  · exact ⟨61, 5, prime_61, prime_5, by norm_num⟩
  · exact ⟨61, 7, prime_61, prime_7, by norm_num⟩
  · exact ⟨67, 3, prime_67, prime_3, by norm_num⟩
  · exact ⟨67, 5, prime_67, prime_5, by norm_num⟩
  · exact ⟨71, 3, prime_71, prime_3, by norm_num⟩
  · exact ⟨73, 3, prime_73, prime_3, by norm_num⟩
  · exact ⟨73, 5, prime_73, prime_5, by norm_num⟩
  · exact ⟨73, 7, prime_73, prime_7, by norm_num⟩
  · exact ⟨79, 3, prime_79, prime_3, by norm_num⟩
  · exact ⟨79, 5, prime_79, prime_5, by norm_num⟩
  · exact ⟨83, 3, prime_83, prime_3, by norm_num⟩
  · exact ⟨83, 5, prime_83, prime_5, by norm_num⟩
  · exact ⟨83, 7, prime_83, prime_7, by norm_num⟩
  · exact ⟨89, 3, prime_89, prime_3, by norm_num⟩
  · exact ⟨89, 5, prime_89, prime_5, by norm_num⟩
  · exact ⟨89, 7, prime_89, prime_7, by norm_num⟩
  · exact ⟨79, 19, prime_79, prime_19, by norm_num⟩
  · exact ⟨97, 3, prime_97, prime_3, by norm_num⟩
  · exact ⟨97, 5, prime_97, prime_5, by norm_num⟩
  · exact ⟨101, 3, prime_101, prime_3, by norm_num⟩
  · exact ⟨103, 3, prime_103, prime_3, by norm_num⟩
  · exact ⟨103, 5, prime_103, prime_5, by norm_num⟩
  · exact ⟨107, 3, prime_107, prime_3, by norm_num⟩
  · exact ⟨109, 3, prime_109, prime_3, by norm_num⟩
  · exact ⟨109, 5, prime_109, prime_5, by norm_num⟩
  · exact ⟨113, 3, prime_113, prime_3, by norm_num⟩
  · exact ⟨113, 5, prime_113, prime_5, by norm_num⟩
  · exact ⟨113, 7, prime_113, prime_7, by norm_num⟩
  · exact ⟨109, 13, prime_109, prime_13, by norm_num⟩
  · exact ⟨113, 11, prime_113, prime_11, by norm_num⟩
  · exact ⟨113, 13, prime_113, prime_13, by norm_num⟩
  · exact ⟨109, 19, prime_109, prime_19, by norm_num⟩
  · exact ⟨127, 3, prime_127, prime_3, by norm_num⟩
  · exact ⟨127, 5, prime_127, prime_5, by norm_num⟩
  · exact ⟨131, 3, prime_131, prime_3, by norm_num⟩
  · exact ⟨131, 5, prime_131, prime_5, by norm_num⟩
  · exact ⟨131, 7, prime_131, prime_7, by norm_num⟩
  · exact ⟨137, 3, prime_137, prime_3, by norm_num⟩
  · exact ⟨139, 3, prime_139, prime_3, by norm_num⟩
  · exact ⟨139, 5, prime_139, prime_5, by norm_num⟩
  · exact ⟨139, 7, prime_139, prime_7, by norm_num⟩
  · exact ⟨137, 11, prime_137, prime_11, by norm_num⟩
  · exact ⟨139, 11, prime_139, prime_11, by norm_num⟩
  · exact ⟨149, 3, prime_149, prime_3, by norm_num⟩
  · exact ⟨151, 3, prime_151, prime_3, by norm_num⟩
  · exact ⟨151, 5, prime_151, prime_5, by norm_num⟩
  · exact ⟨151, 7, prime_151, prime_7, by norm_num⟩
  · exact ⟨157, 3, prime_157, prime_3, by norm_num⟩
  · exact ⟨157, 5, prime_157, prime_5, by norm_num⟩
  · exact ⟨157, 7, prime_157, prime_7, by norm_num⟩
  · exact ⟨163, 3, prime_163, prime_3, by norm_num⟩
  · exact ⟨163, 5, prime_163, prime_5, by norm_num⟩
  · exact ⟨167, 3, prime_167, prime_3, by norm_num⟩
  · exact ⟨167, 5, prime_167, prime_5, by norm_num⟩
  · exact ⟨167, 7, prime_167, prime_7, by norm_num⟩
  · exact ⟨173, 3, prime_173, prime_3, by norm_num⟩
  · exact ⟨173, 5, prime_173, prime_5, by norm_num⟩
  · exact ⟨173, 7, prime_173, prime_7, by norm_num⟩
  · exact ⟨179, 3, prime_179, prime_3, by norm_num⟩
  · exact ⟨181, 3, prime_181, prime_3, by norm_num⟩
  · exact ⟨181, 5, prime_181, prime_5, by norm_num⟩
  · exact ⟨181, 7, prime_181, prime_7, by norm_num⟩
  · exact ⟨179, 11, prime_179, prime_11, by norm_num⟩
  · exact ⟨181, 11, prime_181, prime_11, by norm_num⟩
  · exact ⟨191, 3, prime_191, prime_3, by norm_num⟩
  · exact ⟨193, 3, prime_193, prime_3, by norm_num⟩
  · exact ⟨193, 5, prime_193, prime_5, by norm_num⟩
  · exact ⟨197, 3, prime_197, prime_3, by norm_num⟩
  · exact ⟨199, 3, prime_199, prime_3, by norm_num⟩

private theorem goldbach_chunk_1 : ∀ k : ℕ, 102 ≤ k → k ≤ 201 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨199, 5, prime_199, prime_5, by norm_num⟩
  · exact ⟨199, 7, prime_199, prime_7, by norm_num⟩
  · exact ⟨197, 11, prime_197, prime_11, by norm_num⟩
  · exact ⟨199, 11, prime_199, prime_11, by norm_num⟩
  · exact ⟨199, 13, prime_199, prime_13, by norm_num⟩
  · exact ⟨211, 3, prime_211, prime_3, by norm_num⟩
  · exact ⟨211, 5, prime_211, prime_5, by norm_num⟩
  · exact ⟨211, 7, prime_211, prime_7, by norm_num⟩
  · exact ⟨197, 23, prime_197, prime_23, by norm_num⟩
  · exact ⟨211, 11, prime_211, prime_11, by norm_num⟩
  · exact ⟨211, 13, prime_211, prime_13, by norm_num⟩
  · exact ⟨223, 3, prime_223, prime_3, by norm_num⟩
  · exact ⟨223, 5, prime_223, prime_5, by norm_num⟩
  · exact ⟨227, 3, prime_227, prime_3, by norm_num⟩
  · exact ⟨229, 3, prime_229, prime_3, by norm_num⟩
  · exact ⟨229, 5, prime_229, prime_5, by norm_num⟩
  · exact ⟨233, 3, prime_233, prime_3, by norm_num⟩
  · exact ⟨233, 5, prime_233, prime_5, by norm_num⟩
  · exact ⟨233, 7, prime_233, prime_7, by norm_num⟩
  · exact ⟨239, 3, prime_239, prime_3, by norm_num⟩
  · exact ⟨241, 3, prime_241, prime_3, by norm_num⟩
  · exact ⟨241, 5, prime_241, prime_5, by norm_num⟩
  · exact ⟨241, 7, prime_241, prime_7, by norm_num⟩
  · exact ⟨239, 11, prime_239, prime_11, by norm_num⟩
  · exact ⟨241, 11, prime_241, prime_11, by norm_num⟩
  · exact ⟨251, 3, prime_251, prime_3, by norm_num⟩
  · exact ⟨251, 5, prime_251, prime_5, by norm_num⟩
  · exact ⟨251, 7, prime_251, prime_7, by norm_num⟩
  · exact ⟨257, 3, prime_257, prime_3, by norm_num⟩
  · exact ⟨257, 5, prime_257, prime_5, by norm_num⟩
  · exact ⟨257, 7, prime_257, prime_7, by norm_num⟩
  · exact ⟨263, 3, prime_263, prime_3, by norm_num⟩
  · exact ⟨263, 5, prime_263, prime_5, by norm_num⟩
  · exact ⟨263, 7, prime_263, prime_7, by norm_num⟩
  · exact ⟨269, 3, prime_269, prime_3, by norm_num⟩
  · exact ⟨271, 3, prime_271, prime_3, by norm_num⟩
  · exact ⟨271, 5, prime_271, prime_5, by norm_num⟩
  · exact ⟨271, 7, prime_271, prime_7, by norm_num⟩
  · exact ⟨277, 3, prime_277, prime_3, by norm_num⟩
  · exact ⟨277, 5, prime_277, prime_5, by norm_num⟩
  · exact ⟨281, 3, prime_281, prime_3, by norm_num⟩
  · exact ⟨283, 3, prime_283, prime_3, by norm_num⟩
  · exact ⟨283, 5, prime_283, prime_5, by norm_num⟩
  · exact ⟨283, 7, prime_283, prime_7, by norm_num⟩
  · exact ⟨281, 11, prime_281, prime_11, by norm_num⟩
  · exact ⟨283, 11, prime_283, prime_11, by norm_num⟩
  · exact ⟨293, 3, prime_293, prime_3, by norm_num⟩
  · exact ⟨293, 5, prime_293, prime_5, by norm_num⟩
  · exact ⟨293, 7, prime_293, prime_7, by norm_num⟩
  · exact ⟨283, 19, prime_283, prime_19, by norm_num⟩
  · exact ⟨293, 11, prime_293, prime_11, by norm_num⟩
  · exact ⟨293, 13, prime_293, prime_13, by norm_num⟩
  · exact ⟨277, 31, prime_277, prime_31, by norm_num⟩
  · exact ⟨307, 3, prime_307, prime_3, by norm_num⟩
  · exact ⟨307, 5, prime_307, prime_5, by norm_num⟩
  · exact ⟨311, 3, prime_311, prime_3, by norm_num⟩
  · exact ⟨313, 3, prime_313, prime_3, by norm_num⟩
  · exact ⟨313, 5, prime_313, prime_5, by norm_num⟩
  · exact ⟨317, 3, prime_317, prime_3, by norm_num⟩
  · exact ⟨317, 5, prime_317, prime_5, by norm_num⟩
  · exact ⟨317, 7, prime_317, prime_7, by norm_num⟩
  · exact ⟨313, 13, prime_313, prime_13, by norm_num⟩
  · exact ⟨317, 11, prime_317, prime_11, by norm_num⟩
  · exact ⟨317, 13, prime_317, prime_13, by norm_num⟩
  · exact ⟨313, 19, prime_313, prime_19, by norm_num⟩
  · exact ⟨331, 3, prime_331, prime_3, by norm_num⟩
  · exact ⟨331, 5, prime_331, prime_5, by norm_num⟩
  · exact ⟨331, 7, prime_331, prime_7, by norm_num⟩
  · exact ⟨337, 3, prime_337, prime_3, by norm_num⟩
  · exact ⟨337, 5, prime_337, prime_5, by norm_num⟩
  · exact ⟨337, 7, prime_337, prime_7, by norm_num⟩
  · exact ⟨317, 29, prime_317, prime_29, by norm_num⟩
  · exact ⟨337, 11, prime_337, prime_11, by norm_num⟩
  · exact ⟨347, 3, prime_347, prime_3, by norm_num⟩
  · exact ⟨349, 3, prime_349, prime_3, by norm_num⟩
  · exact ⟨349, 5, prime_349, prime_5, by norm_num⟩
  · exact ⟨353, 3, prime_353, prime_3, by norm_num⟩
  · exact ⟨353, 5, prime_353, prime_5, by norm_num⟩
  · exact ⟨353, 7, prime_353, prime_7, by norm_num⟩
  · exact ⟨359, 3, prime_359, prime_3, by norm_num⟩
  · exact ⟨359, 5, prime_359, prime_5, by norm_num⟩
  · exact ⟨359, 7, prime_359, prime_7, by norm_num⟩
  · exact ⟨349, 19, prime_349, prime_19, by norm_num⟩
  · exact ⟨367, 3, prime_367, prime_3, by norm_num⟩
  · exact ⟨367, 5, prime_367, prime_5, by norm_num⟩
  · exact ⟨367, 7, prime_367, prime_7, by norm_num⟩
  · exact ⟨373, 3, prime_373, prime_3, by norm_num⟩
  · exact ⟨373, 5, prime_373, prime_5, by norm_num⟩
  · exact ⟨373, 7, prime_373, prime_7, by norm_num⟩
  · exact ⟨379, 3, prime_379, prime_3, by norm_num⟩
  · exact ⟨379, 5, prime_379, prime_5, by norm_num⟩
  · exact ⟨383, 3, prime_383, prime_3, by norm_num⟩
  · exact ⟨383, 5, prime_383, prime_5, by norm_num⟩
  · exact ⟨383, 7, prime_383, prime_7, by norm_num⟩
  · exact ⟨389, 3, prime_389, prime_3, by norm_num⟩
  · exact ⟨389, 5, prime_389, prime_5, by norm_num⟩
  · exact ⟨389, 7, prime_389, prime_7, by norm_num⟩
  · exact ⟨379, 19, prime_379, prime_19, by norm_num⟩
  · exact ⟨397, 3, prime_397, prime_3, by norm_num⟩
  · exact ⟨397, 5, prime_397, prime_5, by norm_num⟩

private theorem goldbach_chunk_2 : ∀ k : ℕ, 202 ≤ k → k ≤ 301 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨401, 3, prime_401, prime_3, by norm_num⟩
  · exact ⟨401, 5, prime_401, prime_5, by norm_num⟩
  · exact ⟨401, 7, prime_401, prime_7, by norm_num⟩
  · exact ⟨397, 13, prime_397, prime_13, by norm_num⟩
  · exact ⟨409, 3, prime_409, prime_3, by norm_num⟩
  · exact ⟨409, 5, prime_409, prime_5, by norm_num⟩
  · exact ⟨409, 7, prime_409, prime_7, by norm_num⟩
  · exact ⟨401, 17, prime_401, prime_17, by norm_num⟩
  · exact ⟨409, 11, prime_409, prime_11, by norm_num⟩
  · exact ⟨419, 3, prime_419, prime_3, by norm_num⟩
  · exact ⟨421, 3, prime_421, prime_3, by norm_num⟩
  · exact ⟨421, 5, prime_421, prime_5, by norm_num⟩
  · exact ⟨421, 7, prime_421, prime_7, by norm_num⟩
  · exact ⟨419, 11, prime_419, prime_11, by norm_num⟩
  · exact ⟨421, 11, prime_421, prime_11, by norm_num⟩
  · exact ⟨431, 3, prime_431, prime_3, by norm_num⟩
  · exact ⟨433, 3, prime_433, prime_3, by norm_num⟩
  · exact ⟨433, 5, prime_433, prime_5, by norm_num⟩
  · exact ⟨433, 7, prime_433, prime_7, by norm_num⟩
  · exact ⟨439, 3, prime_439, prime_3, by norm_num⟩
  · exact ⟨439, 5, prime_439, prime_5, by norm_num⟩
  · exact ⟨443, 3, prime_443, prime_3, by norm_num⟩
  · exact ⟨443, 5, prime_443, prime_5, by norm_num⟩
  · exact ⟨443, 7, prime_443, prime_7, by norm_num⟩
  · exact ⟨449, 3, prime_449, prime_3, by norm_num⟩
  · exact ⟨449, 5, prime_449, prime_5, by norm_num⟩
  · exact ⟨449, 7, prime_449, prime_7, by norm_num⟩
  · exact ⟨439, 19, prime_439, prime_19, by norm_num⟩
  · exact ⟨457, 3, prime_457, prime_3, by norm_num⟩
  · exact ⟨457, 5, prime_457, prime_5, by norm_num⟩
  · exact ⟨461, 3, prime_461, prime_3, by norm_num⟩
  · exact ⟨463, 3, prime_463, prime_3, by norm_num⟩
  · exact ⟨463, 5, prime_463, prime_5, by norm_num⟩
  · exact ⟨467, 3, prime_467, prime_3, by norm_num⟩
  · exact ⟨467, 5, prime_467, prime_5, by norm_num⟩
  · exact ⟨467, 7, prime_467, prime_7, by norm_num⟩
  · exact ⟨463, 13, prime_463, prime_13, by norm_num⟩
  · exact ⟨467, 11, prime_467, prime_11, by norm_num⟩
  · exact ⟨467, 13, prime_467, prime_13, by norm_num⟩
  · exact ⟨479, 3, prime_479, prime_3, by norm_num⟩
  · exact ⟨479, 5, prime_479, prime_5, by norm_num⟩
  · exact ⟨479, 7, prime_479, prime_7, by norm_num⟩
  · exact ⟨457, 31, prime_457, prime_31, by norm_num⟩
  · exact ⟨487, 3, prime_487, prime_3, by norm_num⟩
  · exact ⟨487, 5, prime_487, prime_5, by norm_num⟩
  · exact ⟨491, 3, prime_491, prime_3, by norm_num⟩
  · exact ⟨491, 5, prime_491, prime_5, by norm_num⟩
  · exact ⟨491, 7, prime_491, prime_7, by norm_num⟩
  · exact ⟨487, 13, prime_487, prime_13, by norm_num⟩
  · exact ⟨499, 3, prime_499, prime_3, by norm_num⟩
  · exact ⟨499, 5, prime_499, prime_5, by norm_num⟩
  · exact ⟨503, 3, prime_503, prime_3, by norm_num⟩
  · exact ⟨503, 5, prime_503, prime_5, by norm_num⟩
  · exact ⟨503, 7, prime_503, prime_7, by norm_num⟩
  · exact ⟨509, 3, prime_509, prime_3, by norm_num⟩
  · exact ⟨509, 5, prime_509, prime_5, by norm_num⟩
  · exact ⟨509, 7, prime_509, prime_7, by norm_num⟩
  · exact ⟨499, 19, prime_499, prime_19, by norm_num⟩
  · exact ⟨509, 11, prime_509, prime_11, by norm_num⟩
  · exact ⟨509, 13, prime_509, prime_13, by norm_num⟩
  · exact ⟨521, 3, prime_521, prime_3, by norm_num⟩
  · exact ⟨523, 3, prime_523, prime_3, by norm_num⟩
  · exact ⟨523, 5, prime_523, prime_5, by norm_num⟩
  · exact ⟨523, 7, prime_523, prime_7, by norm_num⟩
  · exact ⟨521, 11, prime_521, prime_11, by norm_num⟩
  · exact ⟨523, 11, prime_523, prime_11, by norm_num⟩
  · exact ⟨523, 13, prime_523, prime_13, by norm_num⟩
  · exact ⟨521, 17, prime_521, prime_17, by norm_num⟩
  · exact ⟨523, 17, prime_523, prime_17, by norm_num⟩
  · exact ⟨523, 19, prime_523, prime_19, by norm_num⟩
  · exact ⟨541, 3, prime_541, prime_3, by norm_num⟩
  · exact ⟨541, 5, prime_541, prime_5, by norm_num⟩
  · exact ⟨541, 7, prime_541, prime_7, by norm_num⟩
  · exact ⟨547, 3, prime_547, prime_3, by norm_num⟩
  · exact ⟨547, 5, prime_547, prime_5, by norm_num⟩
  · exact ⟨547, 7, prime_547, prime_7, by norm_num⟩
  · exact ⟨509, 47, prime_509, prime_47, by norm_num⟩
  · exact ⟨547, 11, prime_547, prime_11, by norm_num⟩
  · exact ⟨557, 3, prime_557, prime_3, by norm_num⟩
  · exact ⟨557, 5, prime_557, prime_5, by norm_num⟩
  · exact ⟨557, 7, prime_557, prime_7, by norm_num⟩
  · exact ⟨563, 3, prime_563, prime_3, by norm_num⟩
  · exact ⟨563, 5, prime_563, prime_5, by norm_num⟩
  · exact ⟨563, 7, prime_563, prime_7, by norm_num⟩
  · exact ⟨569, 3, prime_569, prime_3, by norm_num⟩
  · exact ⟨571, 3, prime_571, prime_3, by norm_num⟩
  · exact ⟨571, 5, prime_571, prime_5, by norm_num⟩
  · exact ⟨571, 7, prime_571, prime_7, by norm_num⟩
  · exact ⟨577, 3, prime_577, prime_3, by norm_num⟩
  · exact ⟨577, 5, prime_577, prime_5, by norm_num⟩
  · exact ⟨577, 7, prime_577, prime_7, by norm_num⟩
  · exact ⟨569, 17, prime_569, prime_17, by norm_num⟩
  · exact ⟨577, 11, prime_577, prime_11, by norm_num⟩
  · exact ⟨587, 3, prime_587, prime_3, by norm_num⟩
  · exact ⟨587, 5, prime_587, prime_5, by norm_num⟩
  · exact ⟨587, 7, prime_587, prime_7, by norm_num⟩
  · exact ⟨593, 3, prime_593, prime_3, by norm_num⟩
  · exact ⟨593, 5, prime_593, prime_5, by norm_num⟩
  · exact ⟨593, 7, prime_593, prime_7, by norm_num⟩
  · exact ⟨599, 3, prime_599, prime_3, by norm_num⟩

private theorem goldbach_chunk_3 : ∀ k : ℕ, 302 ≤ k → k ≤ 401 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨601, 3, prime_601, prime_3, by norm_num⟩
  · exact ⟨601, 5, prime_601, prime_5, by norm_num⟩
  · exact ⟨601, 7, prime_601, prime_7, by norm_num⟩
  · exact ⟨607, 3, prime_607, prime_3, by norm_num⟩
  · exact ⟨607, 5, prime_607, prime_5, by norm_num⟩
  · exact ⟨607, 7, prime_607, prime_7, by norm_num⟩
  · exact ⟨613, 3, prime_613, prime_3, by norm_num⟩
  · exact ⟨613, 5, prime_613, prime_5, by norm_num⟩
  · exact ⟨617, 3, prime_617, prime_3, by norm_num⟩
  · exact ⟨619, 3, prime_619, prime_3, by norm_num⟩
  · exact ⟨619, 5, prime_619, prime_5, by norm_num⟩
  · exact ⟨619, 7, prime_619, prime_7, by norm_num⟩
  · exact ⟨617, 11, prime_617, prime_11, by norm_num⟩
  · exact ⟨619, 11, prime_619, prime_11, by norm_num⟩
  · exact ⟨619, 13, prime_619, prime_13, by norm_num⟩
  · exact ⟨631, 3, prime_631, prime_3, by norm_num⟩
  · exact ⟨631, 5, prime_631, prime_5, by norm_num⟩
  · exact ⟨631, 7, prime_631, prime_7, by norm_num⟩
  · exact ⟨617, 23, prime_617, prime_23, by norm_num⟩
  · exact ⟨631, 11, prime_631, prime_11, by norm_num⟩
  · exact ⟨641, 3, prime_641, prime_3, by norm_num⟩
  · exact ⟨643, 3, prime_643, prime_3, by norm_num⟩
  · exact ⟨643, 5, prime_643, prime_5, by norm_num⟩
  · exact ⟨647, 3, prime_647, prime_3, by norm_num⟩
  · exact ⟨647, 5, prime_647, prime_5, by norm_num⟩
  · exact ⟨647, 7, prime_647, prime_7, by norm_num⟩
  · exact ⟨653, 3, prime_653, prime_3, by norm_num⟩
  · exact ⟨653, 5, prime_653, prime_5, by norm_num⟩
  · exact ⟨653, 7, prime_653, prime_7, by norm_num⟩
  · exact ⟨659, 3, prime_659, prime_3, by norm_num⟩
  · exact ⟨661, 3, prime_661, prime_3, by norm_num⟩
  · exact ⟨661, 5, prime_661, prime_5, by norm_num⟩
  · exact ⟨661, 7, prime_661, prime_7, by norm_num⟩
  · exact ⟨659, 11, prime_659, prime_11, by norm_num⟩
  · exact ⟨661, 11, prime_661, prime_11, by norm_num⟩
  · exact ⟨661, 13, prime_661, prime_13, by norm_num⟩
  · exact ⟨673, 3, prime_673, prime_3, by norm_num⟩
  · exact ⟨673, 5, prime_673, prime_5, by norm_num⟩
  · exact ⟨677, 3, prime_677, prime_3, by norm_num⟩
  · exact ⟨677, 5, prime_677, prime_5, by norm_num⟩
  · exact ⟨677, 7, prime_677, prime_7, by norm_num⟩
  · exact ⟨683, 3, prime_683, prime_3, by norm_num⟩
  · exact ⟨683, 5, prime_683, prime_5, by norm_num⟩
  · exact ⟨683, 7, prime_683, prime_7, by norm_num⟩
  · exact ⟨673, 19, prime_673, prime_19, by norm_num⟩
  · exact ⟨691, 3, prime_691, prime_3, by norm_num⟩
  · exact ⟨691, 5, prime_691, prime_5, by norm_num⟩
  · exact ⟨691, 7, prime_691, prime_7, by norm_num⟩
  · exact ⟨683, 17, prime_683, prime_17, by norm_num⟩
  · exact ⟨691, 11, prime_691, prime_11, by norm_num⟩
  · exact ⟨701, 3, prime_701, prime_3, by norm_num⟩
  · exact ⟨701, 5, prime_701, prime_5, by norm_num⟩
  · exact ⟨701, 7, prime_701, prime_7, by norm_num⟩
  · exact ⟨691, 19, prime_691, prime_19, by norm_num⟩
  · exact ⟨709, 3, prime_709, prime_3, by norm_num⟩
  · exact ⟨709, 5, prime_709, prime_5, by norm_num⟩
  · exact ⟨709, 7, prime_709, prime_7, by norm_num⟩
  · exact ⟨701, 17, prime_701, prime_17, by norm_num⟩
  · exact ⟨709, 11, prime_709, prime_11, by norm_num⟩
  · exact ⟨719, 3, prime_719, prime_3, by norm_num⟩
  · exact ⟨719, 5, prime_719, prime_5, by norm_num⟩
  · exact ⟨719, 7, prime_719, prime_7, by norm_num⟩
  · exact ⟨709, 19, prime_709, prime_19, by norm_num⟩
  · exact ⟨727, 3, prime_727, prime_3, by norm_num⟩
  · exact ⟨727, 5, prime_727, prime_5, by norm_num⟩
  · exact ⟨727, 7, prime_727, prime_7, by norm_num⟩
  · exact ⟨733, 3, prime_733, prime_3, by norm_num⟩
  · exact ⟨733, 5, prime_733, prime_5, by norm_num⟩
  · exact ⟨733, 7, prime_733, prime_7, by norm_num⟩
  · exact ⟨739, 3, prime_739, prime_3, by norm_num⟩
  · exact ⟨739, 5, prime_739, prime_5, by norm_num⟩
  · exact ⟨743, 3, prime_743, prime_3, by norm_num⟩
  · exact ⟨743, 5, prime_743, prime_5, by norm_num⟩
  · exact ⟨743, 7, prime_743, prime_7, by norm_num⟩
  · exact ⟨739, 13, prime_739, prime_13, by norm_num⟩
  · exact ⟨751, 3, prime_751, prime_3, by norm_num⟩
  · exact ⟨751, 5, prime_751, prime_5, by norm_num⟩
  · exact ⟨751, 7, prime_751, prime_7, by norm_num⟩
  · exact ⟨757, 3, prime_757, prime_3, by norm_num⟩
  · exact ⟨757, 5, prime_757, prime_5, by norm_num⟩
  · exact ⟨761, 3, prime_761, prime_3, by norm_num⟩
  · exact ⟨761, 5, prime_761, prime_5, by norm_num⟩
  · exact ⟨761, 7, prime_761, prime_7, by norm_num⟩
  · exact ⟨757, 13, prime_757, prime_13, by norm_num⟩
  · exact ⟨769, 3, prime_769, prime_3, by norm_num⟩
  · exact ⟨769, 5, prime_769, prime_5, by norm_num⟩
  · exact ⟨773, 3, prime_773, prime_3, by norm_num⟩
  · exact ⟨773, 5, prime_773, prime_5, by norm_num⟩
  · exact ⟨773, 7, prime_773, prime_7, by norm_num⟩
  · exact ⟨769, 13, prime_769, prime_13, by norm_num⟩
  · exact ⟨773, 11, prime_773, prime_11, by norm_num⟩
  · exact ⟨773, 13, prime_773, prime_13, by norm_num⟩
  · exact ⟨769, 19, prime_769, prime_19, by norm_num⟩
  · exact ⟨787, 3, prime_787, prime_3, by norm_num⟩
  · exact ⟨787, 5, prime_787, prime_5, by norm_num⟩
  · exact ⟨787, 7, prime_787, prime_7, by norm_num⟩
  · exact ⟨773, 23, prime_773, prime_23, by norm_num⟩
  · exact ⟨787, 11, prime_787, prime_11, by norm_num⟩
  · exact ⟨797, 3, prime_797, prime_3, by norm_num⟩
  · exact ⟨797, 5, prime_797, prime_5, by norm_num⟩

private theorem goldbach_chunk_4 : ∀ k : ℕ, 402 ≤ k → k ≤ 501 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨797, 7, prime_797, prime_7, by norm_num⟩
  · exact ⟨787, 19, prime_787, prime_19, by norm_num⟩
  · exact ⟨797, 11, prime_797, prime_11, by norm_num⟩
  · exact ⟨797, 13, prime_797, prime_13, by norm_num⟩
  · exact ⟨809, 3, prime_809, prime_3, by norm_num⟩
  · exact ⟨811, 3, prime_811, prime_3, by norm_num⟩
  · exact ⟨811, 5, prime_811, prime_5, by norm_num⟩
  · exact ⟨811, 7, prime_811, prime_7, by norm_num⟩
  · exact ⟨809, 11, prime_809, prime_11, by norm_num⟩
  · exact ⟨811, 11, prime_811, prime_11, by norm_num⟩
  · exact ⟨821, 3, prime_821, prime_3, by norm_num⟩
  · exact ⟨823, 3, prime_823, prime_3, by norm_num⟩
  · exact ⟨823, 5, prime_823, prime_5, by norm_num⟩
  · exact ⟨827, 3, prime_827, prime_3, by norm_num⟩
  · exact ⟨829, 3, prime_829, prime_3, by norm_num⟩
  · exact ⟨829, 5, prime_829, prime_5, by norm_num⟩
  · exact ⟨829, 7, prime_829, prime_7, by norm_num⟩
  · exact ⟨827, 11, prime_827, prime_11, by norm_num⟩
  · exact ⟨829, 11, prime_829, prime_11, by norm_num⟩
  · exact ⟨839, 3, prime_839, prime_3, by norm_num⟩
  · exact ⟨839, 5, prime_839, prime_5, by norm_num⟩
  · exact ⟨839, 7, prime_839, prime_7, by norm_num⟩
  · exact ⟨829, 19, prime_829, prime_19, by norm_num⟩
  · exact ⟨839, 11, prime_839, prime_11, by norm_num⟩
  · exact ⟨839, 13, prime_839, prime_13, by norm_num⟩
  · exact ⟨823, 31, prime_823, prime_31, by norm_num⟩
  · exact ⟨853, 3, prime_853, prime_3, by norm_num⟩
  · exact ⟨853, 5, prime_853, prime_5, by norm_num⟩
  · exact ⟨857, 3, prime_857, prime_3, by norm_num⟩
  · exact ⟨859, 3, prime_859, prime_3, by norm_num⟩
  · exact ⟨859, 5, prime_859, prime_5, by norm_num⟩
  · exact ⟨863, 3, prime_863, prime_3, by norm_num⟩
  · exact ⟨863, 5, prime_863, prime_5, by norm_num⟩
  · exact ⟨863, 7, prime_863, prime_7, by norm_num⟩
  · exact ⟨859, 13, prime_859, prime_13, by norm_num⟩
  · exact ⟨863, 11, prime_863, prime_11, by norm_num⟩
  · exact ⟨863, 13, prime_863, prime_13, by norm_num⟩
  · exact ⟨859, 19, prime_859, prime_19, by norm_num⟩
  · exact ⟨877, 3, prime_877, prime_3, by norm_num⟩
  · exact ⟨877, 5, prime_877, prime_5, by norm_num⟩
  · exact ⟨881, 3, prime_881, prime_3, by norm_num⟩
  · exact ⟨883, 3, prime_883, prime_3, by norm_num⟩
  · exact ⟨883, 5, prime_883, prime_5, by norm_num⟩
  · exact ⟨887, 3, prime_887, prime_3, by norm_num⟩
  · exact ⟨887, 5, prime_887, prime_5, by norm_num⟩
  · exact ⟨887, 7, prime_887, prime_7, by norm_num⟩
  · exact ⟨883, 13, prime_883, prime_13, by norm_num⟩
  · exact ⟨887, 11, prime_887, prime_11, by norm_num⟩
  · exact ⟨887, 13, prime_887, prime_13, by norm_num⟩
  · exact ⟨883, 19, prime_883, prime_19, by norm_num⟩
  · exact ⟨887, 17, prime_887, prime_17, by norm_num⟩
  · exact ⟨887, 19, prime_887, prime_19, by norm_num⟩
  · exact ⟨877, 31, prime_877, prime_31, by norm_num⟩
  · exact ⟨907, 3, prime_907, prime_3, by norm_num⟩
  · exact ⟨907, 5, prime_907, prime_5, by norm_num⟩
  · exact ⟨911, 3, prime_911, prime_3, by norm_num⟩
  · exact ⟨911, 5, prime_911, prime_5, by norm_num⟩
  · exact ⟨911, 7, prime_911, prime_7, by norm_num⟩
  · exact ⟨907, 13, prime_907, prime_13, by norm_num⟩
  · exact ⟨919, 3, prime_919, prime_3, by norm_num⟩
  · exact ⟨919, 5, prime_919, prime_5, by norm_num⟩
  · exact ⟨919, 7, prime_919, prime_7, by norm_num⟩
  · exact ⟨911, 17, prime_911, prime_17, by norm_num⟩
  · exact ⟨919, 11, prime_919, prime_11, by norm_num⟩
  · exact ⟨929, 3, prime_929, prime_3, by norm_num⟩
  · exact ⟨929, 5, prime_929, prime_5, by norm_num⟩
  · exact ⟨929, 7, prime_929, prime_7, by norm_num⟩
  · exact ⟨919, 19, prime_919, prime_19, by norm_num⟩
  · exact ⟨937, 3, prime_937, prime_3, by norm_num⟩
  · exact ⟨937, 5, prime_937, prime_5, by norm_num⟩
  · exact ⟨941, 3, prime_941, prime_3, by norm_num⟩
  · exact ⟨941, 5, prime_941, prime_5, by norm_num⟩
  · exact ⟨941, 7, prime_941, prime_7, by norm_num⟩
  · exact ⟨947, 3, prime_947, prime_3, by norm_num⟩
  · exact ⟨947, 5, prime_947, prime_5, by norm_num⟩
  · exact ⟨947, 7, prime_947, prime_7, by norm_num⟩
  · exact ⟨953, 3, prime_953, prime_3, by norm_num⟩
  · exact ⟨953, 5, prime_953, prime_5, by norm_num⟩
  · exact ⟨953, 7, prime_953, prime_7, by norm_num⟩
  · exact ⟨919, 43, prime_919, prime_43, by norm_num⟩
  · exact ⟨953, 11, prime_953, prime_11, by norm_num⟩
  · exact ⟨953, 13, prime_953, prime_13, by norm_num⟩
  · exact ⟨937, 31, prime_937, prime_31, by norm_num⟩
  · exact ⟨967, 3, prime_967, prime_3, by norm_num⟩
  · exact ⟨967, 5, prime_967, prime_5, by norm_num⟩
  · exact ⟨971, 3, prime_971, prime_3, by norm_num⟩
  · exact ⟨971, 5, prime_971, prime_5, by norm_num⟩
  · exact ⟨971, 7, prime_971, prime_7, by norm_num⟩
  · exact ⟨977, 3, prime_977, prime_3, by norm_num⟩
  · exact ⟨977, 5, prime_977, prime_5, by norm_num⟩
  · exact ⟨977, 7, prime_977, prime_7, by norm_num⟩
  · exact ⟨983, 3, prime_983, prime_3, by norm_num⟩
  · exact ⟨983, 5, prime_983, prime_5, by norm_num⟩
  · exact ⟨983, 7, prime_983, prime_7, by norm_num⟩
  · exact ⟨919, 73, prime_919, prime_73, by norm_num⟩
  · exact ⟨991, 3, prime_991, prime_3, by norm_num⟩
  · exact ⟨991, 5, prime_991, prime_5, by norm_num⟩
  · exact ⟨991, 7, prime_991, prime_7, by norm_num⟩
  · exact ⟨997, 3, prime_997, prime_3, by norm_num⟩
  · exact ⟨997, 5, prime_997, prime_5, by norm_num⟩

private theorem goldbach_chunk_5 : ∀ k : ℕ, 502 ≤ k → k ≤ 601 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨997, 7, prime_997, prime_7, by norm_num⟩
  · exact ⟨983, 23, prime_983, prime_23, by norm_num⟩
  · exact ⟨997, 11, prime_997, prime_11, by norm_num⟩
  · exact ⟨997, 13, prime_997, prime_13, by norm_num⟩
  · exact ⟨1009, 3, prime_1009, prime_3, by norm_num⟩
  · exact ⟨1009, 5, prime_1009, prime_5, by norm_num⟩
  · exact ⟨1013, 3, prime_1013, prime_3, by norm_num⟩
  · exact ⟨1013, 5, prime_1013, prime_5, by norm_num⟩
  · exact ⟨1013, 7, prime_1013, prime_7, by norm_num⟩
  · exact ⟨1019, 3, prime_1019, prime_3, by norm_num⟩
  · exact ⟨1021, 3, prime_1021, prime_3, by norm_num⟩
  · exact ⟨1021, 5, prime_1021, prime_5, by norm_num⟩
  · exact ⟨1021, 7, prime_1021, prime_7, by norm_num⟩
  · exact ⟨1019, 11, prime_1019, prime_11, by norm_num⟩
  · exact ⟨1021, 11, prime_1021, prime_11, by norm_num⟩
  · exact ⟨1031, 3, prime_1031, prime_3, by norm_num⟩
  · exact ⟨1033, 3, prime_1033, prime_3, by norm_num⟩
  · exact ⟨1033, 5, prime_1033, prime_5, by norm_num⟩
  · exact ⟨1033, 7, prime_1033, prime_7, by norm_num⟩
  · exact ⟨1039, 3, prime_1039, prime_3, by norm_num⟩
  · exact ⟨1039, 5, prime_1039, prime_5, by norm_num⟩
  · exact ⟨1039, 7, prime_1039, prime_7, by norm_num⟩
  · exact ⟨1031, 17, prime_1031, prime_17, by norm_num⟩
  · exact ⟨1039, 11, prime_1039, prime_11, by norm_num⟩
  · exact ⟨1049, 3, prime_1049, prime_3, by norm_num⟩
  · exact ⟨1051, 3, prime_1051, prime_3, by norm_num⟩
  · exact ⟨1051, 5, prime_1051, prime_5, by norm_num⟩
  · exact ⟨1051, 7, prime_1051, prime_7, by norm_num⟩
  · exact ⟨1049, 11, prime_1049, prime_11, by norm_num⟩
  · exact ⟨1051, 11, prime_1051, prime_11, by norm_num⟩
  · exact ⟨1061, 3, prime_1061, prime_3, by norm_num⟩
  · exact ⟨1063, 3, prime_1063, prime_3, by norm_num⟩
  · exact ⟨1063, 5, prime_1063, prime_5, by norm_num⟩
  · exact ⟨1063, 7, prime_1063, prime_7, by norm_num⟩
  · exact ⟨1069, 3, prime_1069, prime_3, by norm_num⟩
  · exact ⟨1069, 5, prime_1069, prime_5, by norm_num⟩
  · exact ⟨1069, 7, prime_1069, prime_7, by norm_num⟩
  · exact ⟨1061, 17, prime_1061, prime_17, by norm_num⟩
  · exact ⟨1069, 11, prime_1069, prime_11, by norm_num⟩
  · exact ⟨1069, 13, prime_1069, prime_13, by norm_num⟩
  · exact ⟨1061, 23, prime_1061, prime_23, by norm_num⟩
  · exact ⟨1069, 17, prime_1069, prime_17, by norm_num⟩
  · exact ⟨1069, 19, prime_1069, prime_19, by norm_num⟩
  · exact ⟨1087, 3, prime_1087, prime_3, by norm_num⟩
  · exact ⟨1087, 5, prime_1087, prime_5, by norm_num⟩
  · exact ⟨1091, 3, prime_1091, prime_3, by norm_num⟩
  · exact ⟨1093, 3, prime_1093, prime_3, by norm_num⟩
  · exact ⟨1093, 5, prime_1093, prime_5, by norm_num⟩
  · exact ⟨1097, 3, prime_1097, prime_3, by norm_num⟩
  · exact ⟨1097, 5, prime_1097, prime_5, by norm_num⟩
  · exact ⟨1097, 7, prime_1097, prime_7, by norm_num⟩
  · exact ⟨1103, 3, prime_1103, prime_3, by norm_num⟩
  · exact ⟨1103, 5, prime_1103, prime_5, by norm_num⟩
  · exact ⟨1103, 7, prime_1103, prime_7, by norm_num⟩
  · exact ⟨1109, 3, prime_1109, prime_3, by norm_num⟩
  · exact ⟨1109, 5, prime_1109, prime_5, by norm_num⟩
  · exact ⟨1109, 7, prime_1109, prime_7, by norm_num⟩
  · exact ⟨1087, 31, prime_1087, prime_31, by norm_num⟩
  · exact ⟨1117, 3, prime_1117, prime_3, by norm_num⟩
  · exact ⟨1117, 5, prime_1117, prime_5, by norm_num⟩
  · exact ⟨1117, 7, prime_1117, prime_7, by norm_num⟩
  · exact ⟨1123, 3, prime_1123, prime_3, by norm_num⟩
  · exact ⟨1123, 5, prime_1123, prime_5, by norm_num⟩
  · exact ⟨1123, 7, prime_1123, prime_7, by norm_num⟩
  · exact ⟨1129, 3, prime_1129, prime_3, by norm_num⟩
  · exact ⟨1129, 5, prime_1129, prime_5, by norm_num⟩
  · exact ⟨1129, 7, prime_1129, prime_7, by norm_num⟩
  · exact ⟨1109, 29, prime_1109, prime_29, by norm_num⟩
  · exact ⟨1129, 11, prime_1129, prime_11, by norm_num⟩
  · exact ⟨1129, 13, prime_1129, prime_13, by norm_num⟩
  · exact ⟨1103, 41, prime_1103, prime_41, by norm_num⟩
  · exact ⟨1129, 17, prime_1129, prime_17, by norm_num⟩
  · exact ⟨1129, 19, prime_1129, prime_19, by norm_num⟩
  · exact ⟨1109, 41, prime_1109, prime_41, by norm_num⟩
  · exact ⟨1129, 23, prime_1129, prime_23, by norm_num⟩
  · exact ⟨1151, 3, prime_1151, prime_3, by norm_num⟩
  · exact ⟨1153, 3, prime_1153, prime_3, by norm_num⟩
  · exact ⟨1153, 5, prime_1153, prime_5, by norm_num⟩
  · exact ⟨1153, 7, prime_1153, prime_7, by norm_num⟩
  · exact ⟨1151, 11, prime_1151, prime_11, by norm_num⟩
  · exact ⟨1153, 11, prime_1153, prime_11, by norm_num⟩
  · exact ⟨1163, 3, prime_1163, prime_3, by norm_num⟩
  · exact ⟨1163, 5, prime_1163, prime_5, by norm_num⟩
  · exact ⟨1163, 7, prime_1163, prime_7, by norm_num⟩
  · exact ⟨1153, 19, prime_1153, prime_19, by norm_num⟩
  · exact ⟨1171, 3, prime_1171, prime_3, by norm_num⟩
  · exact ⟨1171, 5, prime_1171, prime_5, by norm_num⟩
  · exact ⟨1171, 7, prime_1171, prime_7, by norm_num⟩
  · exact ⟨1163, 17, prime_1163, prime_17, by norm_num⟩
  · exact ⟨1171, 11, prime_1171, prime_11, by norm_num⟩
  · exact ⟨1181, 3, prime_1181, prime_3, by norm_num⟩
  · exact ⟨1181, 5, prime_1181, prime_5, by norm_num⟩
  · exact ⟨1181, 7, prime_1181, prime_7, by norm_num⟩
  · exact ⟨1187, 3, prime_1187, prime_3, by norm_num⟩
  · exact ⟨1187, 5, prime_1187, prime_5, by norm_num⟩
  · exact ⟨1187, 7, prime_1187, prime_7, by norm_num⟩
  · exact ⟨1193, 3, prime_1193, prime_3, by norm_num⟩
  · exact ⟨1193, 5, prime_1193, prime_5, by norm_num⟩
  · exact ⟨1193, 7, prime_1193, prime_7, by norm_num⟩
  · exact ⟨1171, 31, prime_1171, prime_31, by norm_num⟩

private theorem goldbach_chunk_6 : ∀ k : ℕ, 602 ≤ k → k ≤ 701 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1201, 3, prime_1201, prime_3, by norm_num⟩
  · exact ⟨1201, 5, prime_1201, prime_5, by norm_num⟩
  · exact ⟨1201, 7, prime_1201, prime_7, by norm_num⟩
  · exact ⟨1193, 17, prime_1193, prime_17, by norm_num⟩
  · exact ⟨1201, 11, prime_1201, prime_11, by norm_num⟩
  · exact ⟨1201, 13, prime_1201, prime_13, by norm_num⟩
  · exact ⟨1213, 3, prime_1213, prime_3, by norm_num⟩
  · exact ⟨1213, 5, prime_1213, prime_5, by norm_num⟩
  · exact ⟨1217, 3, prime_1217, prime_3, by norm_num⟩
  · exact ⟨1217, 5, prime_1217, prime_5, by norm_num⟩
  · exact ⟨1217, 7, prime_1217, prime_7, by norm_num⟩
  · exact ⟨1223, 3, prime_1223, prime_3, by norm_num⟩
  · exact ⟨1223, 5, prime_1223, prime_5, by norm_num⟩
  · exact ⟨1223, 7, prime_1223, prime_7, by norm_num⟩
  · exact ⟨1229, 3, prime_1229, prime_3, by norm_num⟩
  · exact ⟨1231, 3, prime_1231, prime_3, by norm_num⟩
  · exact ⟨1231, 5, prime_1231, prime_5, by norm_num⟩
  · exact ⟨1231, 7, prime_1231, prime_7, by norm_num⟩
  · exact ⟨1237, 3, prime_1237, prime_3, by norm_num⟩
  · exact ⟨1237, 5, prime_1237, prime_5, by norm_num⟩
  · exact ⟨1237, 7, prime_1237, prime_7, by norm_num⟩
  · exact ⟨1229, 17, prime_1229, prime_17, by norm_num⟩
  · exact ⟨1237, 11, prime_1237, prime_11, by norm_num⟩
  · exact ⟨1237, 13, prime_1237, prime_13, by norm_num⟩
  · exact ⟨1249, 3, prime_1249, prime_3, by norm_num⟩
  · exact ⟨1249, 5, prime_1249, prime_5, by norm_num⟩
  · exact ⟨1249, 7, prime_1249, prime_7, by norm_num⟩
  · exact ⟨1229, 29, prime_1229, prime_29, by norm_num⟩
  · exact ⟨1249, 11, prime_1249, prime_11, by norm_num⟩
  · exact ⟨1259, 3, prime_1259, prime_3, by norm_num⟩
  · exact ⟨1259, 5, prime_1259, prime_5, by norm_num⟩
  · exact ⟨1259, 7, prime_1259, prime_7, by norm_num⟩
  · exact ⟨1249, 19, prime_1249, prime_19, by norm_num⟩
  · exact ⟨1259, 11, prime_1259, prime_11, by norm_num⟩
  · exact ⟨1259, 13, prime_1259, prime_13, by norm_num⟩
  · exact ⟨1237, 37, prime_1237, prime_37, by norm_num⟩
  · exact ⟨1259, 17, prime_1259, prime_17, by norm_num⟩
  · exact ⟨1259, 19, prime_1259, prime_19, by norm_num⟩
  · exact ⟨1277, 3, prime_1277, prime_3, by norm_num⟩
  · exact ⟨1279, 3, prime_1279, prime_3, by norm_num⟩
  · exact ⟨1279, 5, prime_1279, prime_5, by norm_num⟩
  · exact ⟨1283, 3, prime_1283, prime_3, by norm_num⟩
  · exact ⟨1283, 5, prime_1283, prime_5, by norm_num⟩
  · exact ⟨1283, 7, prime_1283, prime_7, by norm_num⟩
  · exact ⟨1289, 3, prime_1289, prime_3, by norm_num⟩
  · exact ⟨1291, 3, prime_1291, prime_3, by norm_num⟩
  · exact ⟨1291, 5, prime_1291, prime_5, by norm_num⟩
  · exact ⟨1291, 7, prime_1291, prime_7, by norm_num⟩
  · exact ⟨1297, 3, prime_1297, prime_3, by norm_num⟩
  · exact ⟨1297, 5, prime_1297, prime_5, by norm_num⟩
  · exact ⟨1301, 3, prime_1301, prime_3, by norm_num⟩
  · exact ⟨1303, 3, prime_1303, prime_3, by norm_num⟩
  · exact ⟨1303, 5, prime_1303, prime_5, by norm_num⟩
  · exact ⟨1307, 3, prime_1307, prime_3, by norm_num⟩
  · exact ⟨1307, 5, prime_1307, prime_5, by norm_num⟩
  · exact ⟨1307, 7, prime_1307, prime_7, by norm_num⟩
  · exact ⟨1303, 13, prime_1303, prime_13, by norm_num⟩
  · exact ⟨1307, 11, prime_1307, prime_11, by norm_num⟩
  · exact ⟨1307, 13, prime_1307, prime_13, by norm_num⟩
  · exact ⟨1319, 3, prime_1319, prime_3, by norm_num⟩
  · exact ⟨1321, 3, prime_1321, prime_3, by norm_num⟩
  · exact ⟨1321, 5, prime_1321, prime_5, by norm_num⟩
  · exact ⟨1321, 7, prime_1321, prime_7, by norm_num⟩
  · exact ⟨1327, 3, prime_1327, prime_3, by norm_num⟩
  · exact ⟨1327, 5, prime_1327, prime_5, by norm_num⟩
  · exact ⟨1327, 7, prime_1327, prime_7, by norm_num⟩
  · exact ⟨1319, 17, prime_1319, prime_17, by norm_num⟩
  · exact ⟨1327, 11, prime_1327, prime_11, by norm_num⟩
  · exact ⟨1327, 13, prime_1327, prime_13, by norm_num⟩
  · exact ⟨1319, 23, prime_1319, prime_23, by norm_num⟩
  · exact ⟨1327, 17, prime_1327, prime_17, by norm_num⟩
  · exact ⟨1327, 19, prime_1327, prime_19, by norm_num⟩
  · exact ⟨1319, 29, prime_1319, prime_29, by norm_num⟩
  · exact ⟨1327, 23, prime_1327, prime_23, by norm_num⟩
  · exact ⟨1321, 31, prime_1321, prime_31, by norm_num⟩
  · exact ⟨1307, 47, prime_1307, prime_47, by norm_num⟩
  · exact ⟨1327, 29, prime_1327, prime_29, by norm_num⟩
  · exact ⟨1327, 31, prime_1327, prime_31, by norm_num⟩
  · exact ⟨1319, 41, prime_1319, prime_41, by norm_num⟩
  · exact ⟨1321, 41, prime_1321, prime_41, by norm_num⟩
  · exact ⟨1361, 3, prime_1361, prime_3, by norm_num⟩
  · exact ⟨1361, 5, prime_1361, prime_5, by norm_num⟩
  · exact ⟨1361, 7, prime_1361, prime_7, by norm_num⟩
  · exact ⟨1367, 3, prime_1367, prime_3, by norm_num⟩
  · exact ⟨1367, 5, prime_1367, prime_5, by norm_num⟩
  · exact ⟨1367, 7, prime_1367, prime_7, by norm_num⟩
  · exact ⟨1373, 3, prime_1373, prime_3, by norm_num⟩
  · exact ⟨1373, 5, prime_1373, prime_5, by norm_num⟩
  · exact ⟨1373, 7, prime_1373, prime_7, by norm_num⟩
  · exact ⟨1321, 61, prime_1321, prime_61, by norm_num⟩
  · exact ⟨1381, 3, prime_1381, prime_3, by norm_num⟩
  · exact ⟨1381, 5, prime_1381, prime_5, by norm_num⟩
  · exact ⟨1381, 7, prime_1381, prime_7, by norm_num⟩
  · exact ⟨1373, 17, prime_1373, prime_17, by norm_num⟩
  · exact ⟨1381, 11, prime_1381, prime_11, by norm_num⟩
  · exact ⟨1381, 13, prime_1381, prime_13, by norm_num⟩
  · exact ⟨1373, 23, prime_1373, prime_23, by norm_num⟩
  · exact ⟨1381, 17, prime_1381, prime_17, by norm_num⟩
  · exact ⟨1381, 19, prime_1381, prime_19, by norm_num⟩
  · exact ⟨1399, 3, prime_1399, prime_3, by norm_num⟩

private theorem goldbach_chunk_7 : ∀ k : ℕ, 702 ≤ k → k ≤ 801 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1399, 5, prime_1399, prime_5, by norm_num⟩
  · exact ⟨1399, 7, prime_1399, prime_7, by norm_num⟩
  · exact ⟨1367, 41, prime_1367, prime_41, by norm_num⟩
  · exact ⟨1399, 11, prime_1399, prime_11, by norm_num⟩
  · exact ⟨1409, 3, prime_1409, prime_3, by norm_num⟩
  · exact ⟨1409, 5, prime_1409, prime_5, by norm_num⟩
  · exact ⟨1409, 7, prime_1409, prime_7, by norm_num⟩
  · exact ⟨1399, 19, prime_1399, prime_19, by norm_num⟩
  · exact ⟨1409, 11, prime_1409, prime_11, by norm_num⟩
  · exact ⟨1409, 13, prime_1409, prime_13, by norm_num⟩
  · exact ⟨1381, 43, prime_1381, prime_43, by norm_num⟩
  · exact ⟨1423, 3, prime_1423, prime_3, by norm_num⟩
  · exact ⟨1423, 5, prime_1423, prime_5, by norm_num⟩
  · exact ⟨1427, 3, prime_1427, prime_3, by norm_num⟩
  · exact ⟨1429, 3, prime_1429, prime_3, by norm_num⟩
  · exact ⟨1429, 5, prime_1429, prime_5, by norm_num⟩
  · exact ⟨1433, 3, prime_1433, prime_3, by norm_num⟩
  · exact ⟨1433, 5, prime_1433, prime_5, by norm_num⟩
  · exact ⟨1433, 7, prime_1433, prime_7, by norm_num⟩
  · exact ⟨1439, 3, prime_1439, prime_3, by norm_num⟩
  · exact ⟨1439, 5, prime_1439, prime_5, by norm_num⟩
  · exact ⟨1439, 7, prime_1439, prime_7, by norm_num⟩
  · exact ⟨1429, 19, prime_1429, prime_19, by norm_num⟩
  · exact ⟨1447, 3, prime_1447, prime_3, by norm_num⟩
  · exact ⟨1447, 5, prime_1447, prime_5, by norm_num⟩
  · exact ⟨1451, 3, prime_1451, prime_3, by norm_num⟩
  · exact ⟨1453, 3, prime_1453, prime_3, by norm_num⟩
  · exact ⟨1453, 5, prime_1453, prime_5, by norm_num⟩
  · exact ⟨1453, 7, prime_1453, prime_7, by norm_num⟩
  · exact ⟨1459, 3, prime_1459, prime_3, by norm_num⟩
  · exact ⟨1459, 5, prime_1459, prime_5, by norm_num⟩
  · exact ⟨1459, 7, prime_1459, prime_7, by norm_num⟩
  · exact ⟨1451, 17, prime_1451, prime_17, by norm_num⟩
  · exact ⟨1459, 11, prime_1459, prime_11, by norm_num⟩
  · exact ⟨1459, 13, prime_1459, prime_13, by norm_num⟩
  · exact ⟨1471, 3, prime_1471, prime_3, by norm_num⟩
  · exact ⟨1471, 5, prime_1471, prime_5, by norm_num⟩
  · exact ⟨1471, 7, prime_1471, prime_7, by norm_num⟩
  · exact ⟨1451, 29, prime_1451, prime_29, by norm_num⟩
  · exact ⟨1471, 11, prime_1471, prime_11, by norm_num⟩
  · exact ⟨1481, 3, prime_1481, prime_3, by norm_num⟩
  · exact ⟨1483, 3, prime_1483, prime_3, by norm_num⟩
  · exact ⟨1483, 5, prime_1483, prime_5, by norm_num⟩
  · exact ⟨1487, 3, prime_1487, prime_3, by norm_num⟩
  · exact ⟨1489, 3, prime_1489, prime_3, by norm_num⟩
  · exact ⟨1489, 5, prime_1489, prime_5, by norm_num⟩
  · exact ⟨1493, 3, prime_1493, prime_3, by norm_num⟩
  · exact ⟨1493, 5, prime_1493, prime_5, by norm_num⟩
  · exact ⟨1493, 7, prime_1493, prime_7, by norm_num⟩
  · exact ⟨1499, 3, prime_1499, prime_3, by norm_num⟩
  · exact ⟨1499, 5, prime_1499, prime_5, by norm_num⟩
  · exact ⟨1499, 7, prime_1499, prime_7, by norm_num⟩
  · exact ⟨1489, 19, prime_1489, prime_19, by norm_num⟩
  · exact ⟨1499, 11, prime_1499, prime_11, by norm_num⟩
  · exact ⟨1499, 13, prime_1499, prime_13, by norm_num⟩
  · exact ⟨1511, 3, prime_1511, prime_3, by norm_num⟩
  · exact ⟨1511, 5, prime_1511, prime_5, by norm_num⟩
  · exact ⟨1511, 7, prime_1511, prime_7, by norm_num⟩
  · exact ⟨1489, 31, prime_1489, prime_31, by norm_num⟩
  · exact ⟨1511, 11, prime_1511, prime_11, by norm_num⟩
  · exact ⟨1511, 13, prime_1511, prime_13, by norm_num⟩
  · exact ⟨1523, 3, prime_1523, prime_3, by norm_num⟩
  · exact ⟨1523, 5, prime_1523, prime_5, by norm_num⟩
  · exact ⟨1523, 7, prime_1523, prime_7, by norm_num⟩
  · exact ⟨1489, 43, prime_1489, prime_43, by norm_num⟩
  · exact ⟨1531, 3, prime_1531, prime_3, by norm_num⟩
  · exact ⟨1531, 5, prime_1531, prime_5, by norm_num⟩
  · exact ⟨1531, 7, prime_1531, prime_7, by norm_num⟩
  · exact ⟨1523, 17, prime_1523, prime_17, by norm_num⟩
  · exact ⟨1531, 11, prime_1531, prime_11, by norm_num⟩
  · exact ⟨1531, 13, prime_1531, prime_13, by norm_num⟩
  · exact ⟨1543, 3, prime_1543, prime_3, by norm_num⟩
  · exact ⟨1543, 5, prime_1543, prime_5, by norm_num⟩
  · exact ⟨1543, 7, prime_1543, prime_7, by norm_num⟩
  · exact ⟨1549, 3, prime_1549, prime_3, by norm_num⟩
  · exact ⟨1549, 5, prime_1549, prime_5, by norm_num⟩
  · exact ⟨1553, 3, prime_1553, prime_3, by norm_num⟩
  · exact ⟨1553, 5, prime_1553, prime_5, by norm_num⟩
  · exact ⟨1553, 7, prime_1553, prime_7, by norm_num⟩
  · exact ⟨1559, 3, prime_1559, prime_3, by norm_num⟩
  · exact ⟨1559, 5, prime_1559, prime_5, by norm_num⟩
  · exact ⟨1559, 7, prime_1559, prime_7, by norm_num⟩
  · exact ⟨1549, 19, prime_1549, prime_19, by norm_num⟩
  · exact ⟨1567, 3, prime_1567, prime_3, by norm_num⟩
  · exact ⟨1567, 5, prime_1567, prime_5, by norm_num⟩
  · exact ⟨1571, 3, prime_1571, prime_3, by norm_num⟩
  · exact ⟨1571, 5, prime_1571, prime_5, by norm_num⟩
  · exact ⟨1571, 7, prime_1571, prime_7, by norm_num⟩
  · exact ⟨1567, 13, prime_1567, prime_13, by norm_num⟩
  · exact ⟨1579, 3, prime_1579, prime_3, by norm_num⟩
  · exact ⟨1579, 5, prime_1579, prime_5, by norm_num⟩
  · exact ⟨1583, 3, prime_1583, prime_3, by norm_num⟩
  · exact ⟨1583, 5, prime_1583, prime_5, by norm_num⟩
  · exact ⟨1583, 7, prime_1583, prime_7, by norm_num⟩
  · exact ⟨1579, 13, prime_1579, prime_13, by norm_num⟩
  · exact ⟨1583, 11, prime_1583, prime_11, by norm_num⟩
  · exact ⟨1583, 13, prime_1583, prime_13, by norm_num⟩
  · exact ⟨1579, 19, prime_1579, prime_19, by norm_num⟩
  · exact ⟨1597, 3, prime_1597, prime_3, by norm_num⟩
  · exact ⟨1597, 5, prime_1597, prime_5, by norm_num⟩

private theorem goldbach_chunk_8 : ∀ k : ℕ, 802 ≤ k → k ≤ 901 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1601, 3, prime_1601, prime_3, by norm_num⟩
  · exact ⟨1601, 5, prime_1601, prime_5, by norm_num⟩
  · exact ⟨1601, 7, prime_1601, prime_7, by norm_num⟩
  · exact ⟨1607, 3, prime_1607, prime_3, by norm_num⟩
  · exact ⟨1609, 3, prime_1609, prime_3, by norm_num⟩
  · exact ⟨1609, 5, prime_1609, prime_5, by norm_num⟩
  · exact ⟨1613, 3, prime_1613, prime_3, by norm_num⟩
  · exact ⟨1613, 5, prime_1613, prime_5, by norm_num⟩
  · exact ⟨1613, 7, prime_1613, prime_7, by norm_num⟩
  · exact ⟨1619, 3, prime_1619, prime_3, by norm_num⟩
  · exact ⟨1621, 3, prime_1621, prime_3, by norm_num⟩
  · exact ⟨1621, 5, prime_1621, prime_5, by norm_num⟩
  · exact ⟨1621, 7, prime_1621, prime_7, by norm_num⟩
  · exact ⟨1627, 3, prime_1627, prime_3, by norm_num⟩
  · exact ⟨1627, 5, prime_1627, prime_5, by norm_num⟩
  · exact ⟨1627, 7, prime_1627, prime_7, by norm_num⟩
  · exact ⟨1619, 17, prime_1619, prime_17, by norm_num⟩
  · exact ⟨1627, 11, prime_1627, prime_11, by norm_num⟩
  · exact ⟨1637, 3, prime_1637, prime_3, by norm_num⟩
  · exact ⟨1637, 5, prime_1637, prime_5, by norm_num⟩
  · exact ⟨1637, 7, prime_1637, prime_7, by norm_num⟩
  · exact ⟨1627, 19, prime_1627, prime_19, by norm_num⟩
  · exact ⟨1637, 11, prime_1637, prime_11, by norm_num⟩
  · exact ⟨1637, 13, prime_1637, prime_13, by norm_num⟩
  · exact ⟨1621, 31, prime_1621, prime_31, by norm_num⟩
  · exact ⟨1637, 17, prime_1637, prime_17, by norm_num⟩
  · exact ⟨1637, 19, prime_1637, prime_19, by norm_num⟩
  · exact ⟨1627, 31, prime_1627, prime_31, by norm_num⟩
  · exact ⟨1657, 3, prime_1657, prime_3, by norm_num⟩
  · exact ⟨1657, 5, prime_1657, prime_5, by norm_num⟩
  · exact ⟨1657, 7, prime_1657, prime_7, by norm_num⟩
  · exact ⟨1663, 3, prime_1663, prime_3, by norm_num⟩
  · exact ⟨1663, 5, prime_1663, prime_5, by norm_num⟩
  · exact ⟨1667, 3, prime_1667, prime_3, by norm_num⟩
  · exact ⟨1669, 3, prime_1669, prime_3, by norm_num⟩
  · exact ⟨1669, 5, prime_1669, prime_5, by norm_num⟩
  · exact ⟨1669, 7, prime_1669, prime_7, by norm_num⟩
  · exact ⟨1667, 11, prime_1667, prime_11, by norm_num⟩
  · exact ⟨1669, 11, prime_1669, prime_11, by norm_num⟩
  · exact ⟨1669, 13, prime_1669, prime_13, by norm_num⟩
  · exact ⟨1667, 17, prime_1667, prime_17, by norm_num⟩
  · exact ⟨1669, 17, prime_1669, prime_17, by norm_num⟩
  · exact ⟨1669, 19, prime_1669, prime_19, by norm_num⟩
  · exact ⟨1667, 23, prime_1667, prime_23, by norm_num⟩
  · exact ⟨1669, 23, prime_1669, prime_23, by norm_num⟩
  · exact ⟨1663, 31, prime_1663, prime_31, by norm_num⟩
  · exact ⟨1693, 3, prime_1693, prime_3, by norm_num⟩
  · exact ⟨1693, 5, prime_1693, prime_5, by norm_num⟩
  · exact ⟨1697, 3, prime_1697, prime_3, by norm_num⟩
  · exact ⟨1699, 3, prime_1699, prime_3, by norm_num⟩
  · exact ⟨1699, 5, prime_1699, prime_5, by norm_num⟩
  · exact ⟨1699, 7, prime_1699, prime_7, by norm_num⟩
  · exact ⟨1697, 11, prime_1697, prime_11, by norm_num⟩
  · exact ⟨1699, 11, prime_1699, prime_11, by norm_num⟩
  · exact ⟨1709, 3, prime_1709, prime_3, by norm_num⟩
  · exact ⟨1709, 5, prime_1709, prime_5, by norm_num⟩
  · exact ⟨1709, 7, prime_1709, prime_7, by norm_num⟩
  · exact ⟨1699, 19, prime_1699, prime_19, by norm_num⟩
  · exact ⟨1709, 11, prime_1709, prime_11, by norm_num⟩
  · exact ⟨1709, 13, prime_1709, prime_13, by norm_num⟩
  · exact ⟨1721, 3, prime_1721, prime_3, by norm_num⟩
  · exact ⟨1723, 3, prime_1723, prime_3, by norm_num⟩
  · exact ⟨1723, 5, prime_1723, prime_5, by norm_num⟩
  · exact ⟨1723, 7, prime_1723, prime_7, by norm_num⟩
  · exact ⟨1721, 11, prime_1721, prime_11, by norm_num⟩
  · exact ⟨1723, 11, prime_1723, prime_11, by norm_num⟩
  · exact ⟨1733, 3, prime_1733, prime_3, by norm_num⟩
  · exact ⟨1733, 5, prime_1733, prime_5, by norm_num⟩
  · exact ⟨1733, 7, prime_1733, prime_7, by norm_num⟩
  · exact ⟨1723, 19, prime_1723, prime_19, by norm_num⟩
  · exact ⟨1741, 3, prime_1741, prime_3, by norm_num⟩
  · exact ⟨1741, 5, prime_1741, prime_5, by norm_num⟩
  · exact ⟨1741, 7, prime_1741, prime_7, by norm_num⟩
  · exact ⟨1747, 3, prime_1747, prime_3, by norm_num⟩
  · exact ⟨1747, 5, prime_1747, prime_5, by norm_num⟩
  · exact ⟨1747, 7, prime_1747, prime_7, by norm_num⟩
  · exact ⟨1753, 3, prime_1753, prime_3, by norm_num⟩
  · exact ⟨1753, 5, prime_1753, prime_5, by norm_num⟩
  · exact ⟨1753, 7, prime_1753, prime_7, by norm_num⟩
  · exact ⟨1759, 3, prime_1759, prime_3, by norm_num⟩
  · exact ⟨1759, 5, prime_1759, prime_5, by norm_num⟩
  · exact ⟨1759, 7, prime_1759, prime_7, by norm_num⟩
  · exact ⟨1721, 47, prime_1721, prime_47, by norm_num⟩
  · exact ⟨1759, 11, prime_1759, prime_11, by norm_num⟩
  · exact ⟨1759, 13, prime_1759, prime_13, by norm_num⟩
  · exact ⟨1733, 41, prime_1733, prime_41, by norm_num⟩
  · exact ⟨1759, 17, prime_1759, prime_17, by norm_num⟩
  · exact ⟨1759, 19, prime_1759, prime_19, by norm_num⟩
  · exact ⟨1777, 3, prime_1777, prime_3, by norm_num⟩
  · exact ⟨1777, 5, prime_1777, prime_5, by norm_num⟩
  · exact ⟨1777, 7, prime_1777, prime_7, by norm_num⟩
  · exact ⟨1783, 3, prime_1783, prime_3, by norm_num⟩
  · exact ⟨1783, 5, prime_1783, prime_5, by norm_num⟩
  · exact ⟨1787, 3, prime_1787, prime_3, by norm_num⟩
  · exact ⟨1789, 3, prime_1789, prime_3, by norm_num⟩
  · exact ⟨1789, 5, prime_1789, prime_5, by norm_num⟩
  · exact ⟨1789, 7, prime_1789, prime_7, by norm_num⟩
  · exact ⟨1787, 11, prime_1787, prime_11, by norm_num⟩
  · exact ⟨1789, 11, prime_1789, prime_11, by norm_num⟩
  · exact ⟨1789, 13, prime_1789, prime_13, by norm_num⟩

private theorem goldbach_chunk_9 : ∀ k : ℕ, 902 ≤ k → k ≤ 1001 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1801, 3, prime_1801, prime_3, by norm_num⟩
  · exact ⟨1801, 5, prime_1801, prime_5, by norm_num⟩
  · exact ⟨1801, 7, prime_1801, prime_7, by norm_num⟩
  · exact ⟨1787, 23, prime_1787, prime_23, by norm_num⟩
  · exact ⟨1801, 11, prime_1801, prime_11, by norm_num⟩
  · exact ⟨1811, 3, prime_1811, prime_3, by norm_num⟩
  · exact ⟨1811, 5, prime_1811, prime_5, by norm_num⟩
  · exact ⟨1811, 7, prime_1811, prime_7, by norm_num⟩
  · exact ⟨1801, 19, prime_1801, prime_19, by norm_num⟩
  · exact ⟨1811, 11, prime_1811, prime_11, by norm_num⟩
  · exact ⟨1811, 13, prime_1811, prime_13, by norm_num⟩
  · exact ⟨1823, 3, prime_1823, prime_3, by norm_num⟩
  · exact ⟨1823, 5, prime_1823, prime_5, by norm_num⟩
  · exact ⟨1823, 7, prime_1823, prime_7, by norm_num⟩
  · exact ⟨1801, 31, prime_1801, prime_31, by norm_num⟩
  · exact ⟨1831, 3, prime_1831, prime_3, by norm_num⟩
  · exact ⟨1831, 5, prime_1831, prime_5, by norm_num⟩
  · exact ⟨1831, 7, prime_1831, prime_7, by norm_num⟩
  · exact ⟨1823, 17, prime_1823, prime_17, by norm_num⟩
  · exact ⟨1831, 11, prime_1831, prime_11, by norm_num⟩
  · exact ⟨1831, 13, prime_1831, prime_13, by norm_num⟩
  · exact ⟨1823, 23, prime_1823, prime_23, by norm_num⟩
  · exact ⟨1831, 17, prime_1831, prime_17, by norm_num⟩
  · exact ⟨1847, 3, prime_1847, prime_3, by norm_num⟩
  · exact ⟨1847, 5, prime_1847, prime_5, by norm_num⟩
  · exact ⟨1847, 7, prime_1847, prime_7, by norm_num⟩
  · exact ⟨1789, 67, prime_1789, prime_67, by norm_num⟩
  · exact ⟨1847, 11, prime_1847, prime_11, by norm_num⟩
  · exact ⟨1847, 13, prime_1847, prime_13, by norm_num⟩
  · exact ⟨1831, 31, prime_1831, prime_31, by norm_num⟩
  · exact ⟨1861, 3, prime_1861, prime_3, by norm_num⟩
  · exact ⟨1861, 5, prime_1861, prime_5, by norm_num⟩
  · exact ⟨1861, 7, prime_1861, prime_7, by norm_num⟩
  · exact ⟨1867, 3, prime_1867, prime_3, by norm_num⟩
  · exact ⟨1867, 5, prime_1867, prime_5, by norm_num⟩
  · exact ⟨1871, 3, prime_1871, prime_3, by norm_num⟩
  · exact ⟨1873, 3, prime_1873, prime_3, by norm_num⟩
  · exact ⟨1873, 5, prime_1873, prime_5, by norm_num⟩
  · exact ⟨1877, 3, prime_1877, prime_3, by norm_num⟩
  · exact ⟨1879, 3, prime_1879, prime_3, by norm_num⟩
  · exact ⟨1879, 5, prime_1879, prime_5, by norm_num⟩
  · exact ⟨1879, 7, prime_1879, prime_7, by norm_num⟩
  · exact ⟨1877, 11, prime_1877, prime_11, by norm_num⟩
  · exact ⟨1879, 11, prime_1879, prime_11, by norm_num⟩
  · exact ⟨1889, 3, prime_1889, prime_3, by norm_num⟩
  · exact ⟨1889, 5, prime_1889, prime_5, by norm_num⟩
  · exact ⟨1889, 7, prime_1889, prime_7, by norm_num⟩
  · exact ⟨1879, 19, prime_1879, prime_19, by norm_num⟩
  · exact ⟨1889, 11, prime_1889, prime_11, by norm_num⟩
  · exact ⟨1889, 13, prime_1889, prime_13, by norm_num⟩
  · exact ⟨1901, 3, prime_1901, prime_3, by norm_num⟩
  · exact ⟨1901, 5, prime_1901, prime_5, by norm_num⟩
  · exact ⟨1901, 7, prime_1901, prime_7, by norm_num⟩
  · exact ⟨1907, 3, prime_1907, prime_3, by norm_num⟩
  · exact ⟨1907, 5, prime_1907, prime_5, by norm_num⟩
  · exact ⟨1907, 7, prime_1907, prime_7, by norm_num⟩
  · exact ⟨1913, 3, prime_1913, prime_3, by norm_num⟩
  · exact ⟨1913, 5, prime_1913, prime_5, by norm_num⟩
  · exact ⟨1913, 7, prime_1913, prime_7, by norm_num⟩
  · exact ⟨1879, 43, prime_1879, prime_43, by norm_num⟩
  · exact ⟨1913, 11, prime_1913, prime_11, by norm_num⟩
  · exact ⟨1913, 13, prime_1913, prime_13, by norm_num⟩
  · exact ⟨1867, 61, prime_1867, prime_61, by norm_num⟩
  · exact ⟨1913, 17, prime_1913, prime_17, by norm_num⟩
  · exact ⟨1913, 19, prime_1913, prime_19, by norm_num⟩
  · exact ⟨1931, 3, prime_1931, prime_3, by norm_num⟩
  · exact ⟨1933, 3, prime_1933, prime_3, by norm_num⟩
  · exact ⟨1933, 5, prime_1933, prime_5, by norm_num⟩
  · exact ⟨1933, 7, prime_1933, prime_7, by norm_num⟩
  · exact ⟨1931, 11, prime_1931, prime_11, by norm_num⟩
  · exact ⟨1933, 11, prime_1933, prime_11, by norm_num⟩
  · exact ⟨1933, 13, prime_1933, prime_13, by norm_num⟩
  · exact ⟨1931, 17, prime_1931, prime_17, by norm_num⟩
  · exact ⟨1933, 17, prime_1933, prime_17, by norm_num⟩
  · exact ⟨1949, 3, prime_1949, prime_3, by norm_num⟩
  · exact ⟨1951, 3, prime_1951, prime_3, by norm_num⟩
  · exact ⟨1951, 5, prime_1951, prime_5, by norm_num⟩
  · exact ⟨1951, 7, prime_1951, prime_7, by norm_num⟩
  · exact ⟨1949, 11, prime_1949, prime_11, by norm_num⟩
  · exact ⟨1951, 11, prime_1951, prime_11, by norm_num⟩
  · exact ⟨1951, 13, prime_1951, prime_13, by norm_num⟩
  · exact ⟨1949, 17, prime_1949, prime_17, by norm_num⟩
  · exact ⟨1951, 17, prime_1951, prime_17, by norm_num⟩
  · exact ⟨1951, 19, prime_1951, prime_19, by norm_num⟩
  · exact ⟨1949, 23, prime_1949, prime_23, by norm_num⟩
  · exact ⟨1951, 23, prime_1951, prime_23, by norm_num⟩
  · exact ⟨1973, 3, prime_1973, prime_3, by norm_num⟩
  · exact ⟨1973, 5, prime_1973, prime_5, by norm_num⟩
  · exact ⟨1973, 7, prime_1973, prime_7, by norm_num⟩
  · exact ⟨1979, 3, prime_1979, prime_3, by norm_num⟩
  · exact ⟨1979, 5, prime_1979, prime_5, by norm_num⟩
  · exact ⟨1979, 7, prime_1979, prime_7, by norm_num⟩
  · exact ⟨1951, 37, prime_1951, prime_37, by norm_num⟩
  · exact ⟨1987, 3, prime_1987, prime_3, by norm_num⟩
  · exact ⟨1987, 5, prime_1987, prime_5, by norm_num⟩
  · exact ⟨1987, 7, prime_1987, prime_7, by norm_num⟩
  · exact ⟨1993, 3, prime_1993, prime_3, by norm_num⟩
  · exact ⟨1993, 5, prime_1993, prime_5, by norm_num⟩
  · exact ⟨1997, 3, prime_1997, prime_3, by norm_num⟩
  · exact ⟨1999, 3, prime_1999, prime_3, by norm_num⟩

private theorem goldbach_chunk_10 : ∀ k : ℕ, 1002 ≤ k → k ≤ 1101 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1999, 5, prime_1999, prime_5, by norm_num⟩
  · exact ⟨2003, 3, prime_2003, prime_3, by norm_num⟩
  · exact ⟨2003, 5, prime_2003, prime_5, by norm_num⟩
  · exact ⟨2003, 7, prime_2003, prime_7, by norm_num⟩
  · exact ⟨1999, 13, prime_1999, prime_13, by norm_num⟩
  · exact ⟨2011, 3, prime_2011, prime_3, by norm_num⟩
  · exact ⟨2011, 5, prime_2011, prime_5, by norm_num⟩
  · exact ⟨2011, 7, prime_2011, prime_7, by norm_num⟩
  · exact ⟨2017, 3, prime_2017, prime_3, by norm_num⟩
  · exact ⟨2017, 5, prime_2017, prime_5, by norm_num⟩
  · exact ⟨2017, 7, prime_2017, prime_7, by norm_num⟩
  · exact ⟨2003, 23, prime_2003, prime_23, by norm_num⟩
  · exact ⟨2017, 11, prime_2017, prime_11, by norm_num⟩
  · exact ⟨2027, 3, prime_2027, prime_3, by norm_num⟩
  · exact ⟨2029, 3, prime_2029, prime_3, by norm_num⟩
  · exact ⟨2029, 5, prime_2029, prime_5, by norm_num⟩
  · exact ⟨2029, 7, prime_2029, prime_7, by norm_num⟩
  · exact ⟨2027, 11, prime_2027, prime_11, by norm_num⟩
  · exact ⟨2029, 11, prime_2029, prime_11, by norm_num⟩
  · exact ⟨2039, 3, prime_2039, prime_3, by norm_num⟩
  · exact ⟨2039, 5, prime_2039, prime_5, by norm_num⟩
  · exact ⟨2039, 7, prime_2039, prime_7, by norm_num⟩
  · exact ⟨2029, 19, prime_2029, prime_19, by norm_num⟩
  · exact ⟨2039, 11, prime_2039, prime_11, by norm_num⟩
  · exact ⟨2039, 13, prime_2039, prime_13, by norm_num⟩
  · exact ⟨2017, 37, prime_2017, prime_37, by norm_num⟩
  · exact ⟨2053, 3, prime_2053, prime_3, by norm_num⟩
  · exact ⟨2053, 5, prime_2053, prime_5, by norm_num⟩
  · exact ⟨2053, 7, prime_2053, prime_7, by norm_num⟩
  · exact ⟨2039, 23, prime_2039, prime_23, by norm_num⟩
  · exact ⟨2053, 11, prime_2053, prime_11, by norm_num⟩
  · exact ⟨2063, 3, prime_2063, prime_3, by norm_num⟩
  · exact ⟨2063, 5, prime_2063, prime_5, by norm_num⟩
  · exact ⟨2063, 7, prime_2063, prime_7, by norm_num⟩
  · exact ⟨2069, 3, prime_2069, prime_3, by norm_num⟩
  · exact ⟨2069, 5, prime_2069, prime_5, by norm_num⟩
  · exact ⟨2069, 7, prime_2069, prime_7, by norm_num⟩
  · exact ⟨2017, 61, prime_2017, prime_61, by norm_num⟩
  · exact ⟨2069, 11, prime_2069, prime_11, by norm_num⟩
  · exact ⟨2069, 13, prime_2069, prime_13, by norm_num⟩
  · exact ⟨2081, 3, prime_2081, prime_3, by norm_num⟩
  · exact ⟨2083, 3, prime_2083, prime_3, by norm_num⟩
  · exact ⟨2083, 5, prime_2083, prime_5, by norm_num⟩
  · exact ⟨2087, 3, prime_2087, prime_3, by norm_num⟩
  · exact ⟨2089, 3, prime_2089, prime_3, by norm_num⟩
  · exact ⟨2089, 5, prime_2089, prime_5, by norm_num⟩
  · exact ⟨2089, 7, prime_2089, prime_7, by norm_num⟩
  · exact ⟨2087, 11, prime_2087, prime_11, by norm_num⟩
  · exact ⟨2089, 11, prime_2089, prime_11, by norm_num⟩
  · exact ⟨2099, 3, prime_2099, prime_3, by norm_num⟩
  · exact ⟨2099, 5, prime_2099, prime_5, by norm_num⟩
  · exact ⟨2099, 7, prime_2099, prime_7, by norm_num⟩
  · exact ⟨2089, 19, prime_2089, prime_19, by norm_num⟩
  · exact ⟨2099, 11, prime_2099, prime_11, by norm_num⟩
  · exact ⟨2099, 13, prime_2099, prime_13, by norm_num⟩
  · exact ⟨2111, 3, prime_2111, prime_3, by norm_num⟩
  · exact ⟨2113, 3, prime_2113, prime_3, by norm_num⟩
  · exact ⟨2113, 5, prime_2113, prime_5, by norm_num⟩
  · exact ⟨2113, 7, prime_2113, prime_7, by norm_num⟩
  · exact ⟨2111, 11, prime_2111, prime_11, by norm_num⟩
  · exact ⟨2113, 11, prime_2113, prime_11, by norm_num⟩
  · exact ⟨2113, 13, prime_2113, prime_13, by norm_num⟩
  · exact ⟨2111, 17, prime_2111, prime_17, by norm_num⟩
  · exact ⟨2113, 17, prime_2113, prime_17, by norm_num⟩
  · exact ⟨2129, 3, prime_2129, prime_3, by norm_num⟩
  · exact ⟨2131, 3, prime_2131, prime_3, by norm_num⟩
  · exact ⟨2131, 5, prime_2131, prime_5, by norm_num⟩
  · exact ⟨2131, 7, prime_2131, prime_7, by norm_num⟩
  · exact ⟨2137, 3, prime_2137, prime_3, by norm_num⟩
  · exact ⟨2137, 5, prime_2137, prime_5, by norm_num⟩
  · exact ⟨2141, 3, prime_2141, prime_3, by norm_num⟩
  · exact ⟨2143, 3, prime_2143, prime_3, by norm_num⟩
  · exact ⟨2143, 5, prime_2143, prime_5, by norm_num⟩
  · exact ⟨2143, 7, prime_2143, prime_7, by norm_num⟩
  · exact ⟨2141, 11, prime_2141, prime_11, by norm_num⟩
  · exact ⟨2143, 11, prime_2143, prime_11, by norm_num⟩
  · exact ⟨2153, 3, prime_2153, prime_3, by norm_num⟩
  · exact ⟨2153, 5, prime_2153, prime_5, by norm_num⟩
  · exact ⟨2153, 7, prime_2153, prime_7, by norm_num⟩
  · exact ⟨2143, 19, prime_2143, prime_19, by norm_num⟩
  · exact ⟨2161, 3, prime_2161, prime_3, by norm_num⟩
  · exact ⟨2161, 5, prime_2161, prime_5, by norm_num⟩
  · exact ⟨2161, 7, prime_2161, prime_7, by norm_num⟩
  · exact ⟨2153, 17, prime_2153, prime_17, by norm_num⟩
  · exact ⟨2161, 11, prime_2161, prime_11, by norm_num⟩
  · exact ⟨2161, 13, prime_2161, prime_13, by norm_num⟩
  · exact ⟨2153, 23, prime_2153, prime_23, by norm_num⟩
  · exact ⟨2161, 17, prime_2161, prime_17, by norm_num⟩
  · exact ⟨2161, 19, prime_2161, prime_19, by norm_num⟩
  · exact ⟨2179, 3, prime_2179, prime_3, by norm_num⟩
  · exact ⟨2179, 5, prime_2179, prime_5, by norm_num⟩
  · exact ⟨2179, 7, prime_2179, prime_7, by norm_num⟩
  · exact ⟨2141, 47, prime_2141, prime_47, by norm_num⟩
  · exact ⟨2179, 11, prime_2179, prime_11, by norm_num⟩
  · exact ⟨2179, 13, prime_2179, prime_13, by norm_num⟩
  · exact ⟨2153, 41, prime_2153, prime_41, by norm_num⟩
  · exact ⟨2179, 17, prime_2179, prime_17, by norm_num⟩
  · exact ⟨2179, 19, prime_2179, prime_19, by norm_num⟩
  · exact ⟨2153, 47, prime_2153, prime_47, by norm_num⟩
  · exact ⟨2179, 23, prime_2179, prime_23, by norm_num⟩

private theorem goldbach_chunk_11 : ∀ k : ℕ, 1102 ≤ k → k ≤ 1201 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2161, 43, prime_2161, prime_43, by norm_num⟩
  · exact ⟨2203, 3, prime_2203, prime_3, by norm_num⟩
  · exact ⟨2203, 5, prime_2203, prime_5, by norm_num⟩
  · exact ⟨2207, 3, prime_2207, prime_3, by norm_num⟩
  · exact ⟨2207, 5, prime_2207, prime_5, by norm_num⟩
  · exact ⟨2207, 7, prime_2207, prime_7, by norm_num⟩
  · exact ⟨2213, 3, prime_2213, prime_3, by norm_num⟩
  · exact ⟨2213, 5, prime_2213, prime_5, by norm_num⟩
  · exact ⟨2213, 7, prime_2213, prime_7, by norm_num⟩
  · exact ⟨2203, 19, prime_2203, prime_19, by norm_num⟩
  · exact ⟨2221, 3, prime_2221, prime_3, by norm_num⟩
  · exact ⟨2221, 5, prime_2221, prime_5, by norm_num⟩
  · exact ⟨2221, 7, prime_2221, prime_7, by norm_num⟩
  · exact ⟨2213, 17, prime_2213, prime_17, by norm_num⟩
  · exact ⟨2221, 11, prime_2221, prime_11, by norm_num⟩
  · exact ⟨2221, 13, prime_2221, prime_13, by norm_num⟩
  · exact ⟨2213, 23, prime_2213, prime_23, by norm_num⟩
  · exact ⟨2221, 17, prime_2221, prime_17, by norm_num⟩
  · exact ⟨2237, 3, prime_2237, prime_3, by norm_num⟩
  · exact ⟨2239, 3, prime_2239, prime_3, by norm_num⟩
  · exact ⟨2239, 5, prime_2239, prime_5, by norm_num⟩
  · exact ⟨2243, 3, prime_2243, prime_3, by norm_num⟩
  · exact ⟨2243, 5, prime_2243, prime_5, by norm_num⟩
  · exact ⟨2243, 7, prime_2243, prime_7, by norm_num⟩
  · exact ⟨2239, 13, prime_2239, prime_13, by norm_num⟩
  · exact ⟨2251, 3, prime_2251, prime_3, by norm_num⟩
  · exact ⟨2251, 5, prime_2251, prime_5, by norm_num⟩
  · exact ⟨2251, 7, prime_2251, prime_7, by norm_num⟩
  · exact ⟨2243, 17, prime_2243, prime_17, by norm_num⟩
  · exact ⟨2251, 11, prime_2251, prime_11, by norm_num⟩
  · exact ⟨2251, 13, prime_2251, prime_13, by norm_num⟩
  · exact ⟨2243, 23, prime_2243, prime_23, by norm_num⟩
  · exact ⟨2251, 17, prime_2251, prime_17, by norm_num⟩
  · exact ⟨2267, 3, prime_2267, prime_3, by norm_num⟩
  · exact ⟨2269, 3, prime_2269, prime_3, by norm_num⟩
  · exact ⟨2269, 5, prime_2269, prime_5, by norm_num⟩
  · exact ⟨2273, 3, prime_2273, prime_3, by norm_num⟩
  · exact ⟨2273, 5, prime_2273, prime_5, by norm_num⟩
  · exact ⟨2273, 7, prime_2273, prime_7, by norm_num⟩
  · exact ⟨2269, 13, prime_2269, prime_13, by norm_num⟩
  · exact ⟨2281, 3, prime_2281, prime_3, by norm_num⟩
  · exact ⟨2281, 5, prime_2281, prime_5, by norm_num⟩
  · exact ⟨2281, 7, prime_2281, prime_7, by norm_num⟩
  · exact ⟨2287, 3, prime_2287, prime_3, by norm_num⟩
  · exact ⟨2287, 5, prime_2287, prime_5, by norm_num⟩
  · exact ⟨2287, 7, prime_2287, prime_7, by norm_num⟩
  · exact ⟨2293, 3, prime_2293, prime_3, by norm_num⟩
  · exact ⟨2293, 5, prime_2293, prime_5, by norm_num⟩
  · exact ⟨2297, 3, prime_2297, prime_3, by norm_num⟩
  · exact ⟨2297, 5, prime_2297, prime_5, by norm_num⟩
  · exact ⟨2297, 7, prime_2297, prime_7, by norm_num⟩
  · exact ⟨2293, 13, prime_2293, prime_13, by norm_num⟩
  · exact ⟨2297, 11, prime_2297, prime_11, by norm_num⟩
  · exact ⟨2297, 13, prime_2297, prime_13, by norm_num⟩
  · exact ⟨2309, 3, prime_2309, prime_3, by norm_num⟩
  · exact ⟨2311, 3, prime_2311, prime_3, by norm_num⟩
  · exact ⟨2311, 5, prime_2311, prime_5, by norm_num⟩
  · exact ⟨2311, 7, prime_2311, prime_7, by norm_num⟩
  · exact ⟨2309, 11, prime_2309, prime_11, by norm_num⟩
  · exact ⟨2311, 11, prime_2311, prime_11, by norm_num⟩
  · exact ⟨2311, 13, prime_2311, prime_13, by norm_num⟩
  · exact ⟨2309, 17, prime_2309, prime_17, by norm_num⟩
  · exact ⟨2311, 17, prime_2311, prime_17, by norm_num⟩
  · exact ⟨2311, 19, prime_2311, prime_19, by norm_num⟩
  · exact ⟨2309, 23, prime_2309, prime_23, by norm_num⟩
  · exact ⟨2311, 23, prime_2311, prime_23, by norm_num⟩
  · exact ⟨2333, 3, prime_2333, prime_3, by norm_num⟩
  · exact ⟨2333, 5, prime_2333, prime_5, by norm_num⟩
  · exact ⟨2333, 7, prime_2333, prime_7, by norm_num⟩
  · exact ⟨2339, 3, prime_2339, prime_3, by norm_num⟩
  · exact ⟨2341, 3, prime_2341, prime_3, by norm_num⟩
  · exact ⟨2341, 5, prime_2341, prime_5, by norm_num⟩
  · exact ⟨2341, 7, prime_2341, prime_7, by norm_num⟩
  · exact ⟨2347, 3, prime_2347, prime_3, by norm_num⟩
  · exact ⟨2347, 5, prime_2347, prime_5, by norm_num⟩
  · exact ⟨2351, 3, prime_2351, prime_3, by norm_num⟩
  · exact ⟨2351, 5, prime_2351, prime_5, by norm_num⟩
  · exact ⟨2351, 7, prime_2351, prime_7, by norm_num⟩
  · exact ⟨2357, 3, prime_2357, prime_3, by norm_num⟩
  · exact ⟨2357, 5, prime_2357, prime_5, by norm_num⟩
  · exact ⟨2357, 7, prime_2357, prime_7, by norm_num⟩
  · exact ⟨2347, 19, prime_2347, prime_19, by norm_num⟩
  · exact ⟨2357, 11, prime_2357, prime_11, by norm_num⟩
  · exact ⟨2357, 13, prime_2357, prime_13, by norm_num⟩
  · exact ⟨2341, 31, prime_2341, prime_31, by norm_num⟩
  · exact ⟨2371, 3, prime_2371, prime_3, by norm_num⟩
  · exact ⟨2371, 5, prime_2371, prime_5, by norm_num⟩
  · exact ⟨2371, 7, prime_2371, prime_7, by norm_num⟩
  · exact ⟨2377, 3, prime_2377, prime_3, by norm_num⟩
  · exact ⟨2377, 5, prime_2377, prime_5, by norm_num⟩
  · exact ⟨2381, 3, prime_2381, prime_3, by norm_num⟩
  · exact ⟨2383, 3, prime_2383, prime_3, by norm_num⟩
  · exact ⟨2383, 5, prime_2383, prime_5, by norm_num⟩
  · exact ⟨2383, 7, prime_2383, prime_7, by norm_num⟩
  · exact ⟨2389, 3, prime_2389, prime_3, by norm_num⟩
  · exact ⟨2389, 5, prime_2389, prime_5, by norm_num⟩
  · exact ⟨2393, 3, prime_2393, prime_3, by norm_num⟩
  · exact ⟨2393, 5, prime_2393, prime_5, by norm_num⟩
  · exact ⟨2393, 7, prime_2393, prime_7, by norm_num⟩
  · exact ⟨2399, 3, prime_2399, prime_3, by norm_num⟩

private theorem goldbach_chunk_12 : ∀ k : ℕ, 1202 ≤ k → k ≤ 1301 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2399, 5, prime_2399, prime_5, by norm_num⟩
  · exact ⟨2399, 7, prime_2399, prime_7, by norm_num⟩
  · exact ⟨2389, 19, prime_2389, prime_19, by norm_num⟩
  · exact ⟨2399, 11, prime_2399, prime_11, by norm_num⟩
  · exact ⟨2399, 13, prime_2399, prime_13, by norm_num⟩
  · exact ⟨2411, 3, prime_2411, prime_3, by norm_num⟩
  · exact ⟨2411, 5, prime_2411, prime_5, by norm_num⟩
  · exact ⟨2411, 7, prime_2411, prime_7, by norm_num⟩
  · exact ⟨2417, 3, prime_2417, prime_3, by norm_num⟩
  · exact ⟨2417, 5, prime_2417, prime_5, by norm_num⟩
  · exact ⟨2417, 7, prime_2417, prime_7, by norm_num⟩
  · exact ⟨2423, 3, prime_2423, prime_3, by norm_num⟩
  · exact ⟨2423, 5, prime_2423, prime_5, by norm_num⟩
  · exact ⟨2423, 7, prime_2423, prime_7, by norm_num⟩
  · exact ⟨2389, 43, prime_2389, prime_43, by norm_num⟩
  · exact ⟨2423, 11, prime_2423, prime_11, by norm_num⟩
  · exact ⟨2423, 13, prime_2423, prime_13, by norm_num⟩
  · exact ⟨2377, 61, prime_2377, prime_61, by norm_num⟩
  · exact ⟨2437, 3, prime_2437, prime_3, by norm_num⟩
  · exact ⟨2437, 5, prime_2437, prime_5, by norm_num⟩
  · exact ⟨2441, 3, prime_2441, prime_3, by norm_num⟩
  · exact ⟨2441, 5, prime_2441, prime_5, by norm_num⟩
  · exact ⟨2441, 7, prime_2441, prime_7, by norm_num⟩
  · exact ⟨2447, 3, prime_2447, prime_3, by norm_num⟩
  · exact ⟨2447, 5, prime_2447, prime_5, by norm_num⟩
  · exact ⟨2447, 7, prime_2447, prime_7, by norm_num⟩
  · exact ⟨2437, 19, prime_2437, prime_19, by norm_num⟩
  · exact ⟨2447, 11, prime_2447, prime_11, by norm_num⟩
  · exact ⟨2447, 13, prime_2447, prime_13, by norm_num⟩
  · exact ⟨2459, 3, prime_2459, prime_3, by norm_num⟩
  · exact ⟨2459, 5, prime_2459, prime_5, by norm_num⟩
  · exact ⟨2459, 7, prime_2459, prime_7, by norm_num⟩
  · exact ⟨2437, 31, prime_2437, prime_31, by norm_num⟩
  · exact ⟨2467, 3, prime_2467, prime_3, by norm_num⟩
  · exact ⟨2467, 5, prime_2467, prime_5, by norm_num⟩
  · exact ⟨2467, 7, prime_2467, prime_7, by norm_num⟩
  · exact ⟨2473, 3, prime_2473, prime_3, by norm_num⟩
  · exact ⟨2473, 5, prime_2473, prime_5, by norm_num⟩
  · exact ⟨2477, 3, prime_2477, prime_3, by norm_num⟩
  · exact ⟨2477, 5, prime_2477, prime_5, by norm_num⟩
  · exact ⟨2477, 7, prime_2477, prime_7, by norm_num⟩
  · exact ⟨2473, 13, prime_2473, prime_13, by norm_num⟩
  · exact ⟨2477, 11, prime_2477, prime_11, by norm_num⟩
  · exact ⟨2477, 13, prime_2477, prime_13, by norm_num⟩
  · exact ⟨2473, 19, prime_2473, prime_19, by norm_num⟩
  · exact ⟨2477, 17, prime_2477, prime_17, by norm_num⟩
  · exact ⟨2477, 19, prime_2477, prime_19, by norm_num⟩
  · exact ⟨2467, 31, prime_2467, prime_31, by norm_num⟩
  · exact ⟨2477, 23, prime_2477, prime_23, by norm_num⟩
  · exact ⟨2473, 29, prime_2473, prime_29, by norm_num⟩
  · exact ⟨2473, 31, prime_2473, prime_31, by norm_num⟩
  · exact ⟨2503, 3, prime_2503, prime_3, by norm_num⟩
  · exact ⟨2503, 5, prime_2503, prime_5, by norm_num⟩
  · exact ⟨2503, 7, prime_2503, prime_7, by norm_num⟩
  · exact ⟨2459, 53, prime_2459, prime_53, by norm_num⟩
  · exact ⟨2503, 11, prime_2503, prime_11, by norm_num⟩
  · exact ⟨2503, 13, prime_2503, prime_13, by norm_num⟩
  · exact ⟨2477, 41, prime_2477, prime_41, by norm_num⟩
  · exact ⟨2503, 17, prime_2503, prime_17, by norm_num⟩
  · exact ⟨2503, 19, prime_2503, prime_19, by norm_num⟩
  · exact ⟨2521, 3, prime_2521, prime_3, by norm_num⟩
  · exact ⟨2521, 5, prime_2521, prime_5, by norm_num⟩
  · exact ⟨2521, 7, prime_2521, prime_7, by norm_num⟩
  · exact ⟨2477, 53, prime_2477, prime_53, by norm_num⟩
  · exact ⟨2521, 11, prime_2521, prime_11, by norm_num⟩
  · exact ⟨2531, 3, prime_2531, prime_3, by norm_num⟩
  · exact ⟨2531, 5, prime_2531, prime_5, by norm_num⟩
  · exact ⟨2531, 7, prime_2531, prime_7, by norm_num⟩
  · exact ⟨2521, 19, prime_2521, prime_19, by norm_num⟩
  · exact ⟨2539, 3, prime_2539, prime_3, by norm_num⟩
  · exact ⟨2539, 5, prime_2539, prime_5, by norm_num⟩
  · exact ⟨2543, 3, prime_2543, prime_3, by norm_num⟩
  · exact ⟨2543, 5, prime_2543, prime_5, by norm_num⟩
  · exact ⟨2543, 7, prime_2543, prime_7, by norm_num⟩
  · exact ⟨2549, 3, prime_2549, prime_3, by norm_num⟩
  · exact ⟨2551, 3, prime_2551, prime_3, by norm_num⟩
  · exact ⟨2551, 5, prime_2551, prime_5, by norm_num⟩
  · exact ⟨2551, 7, prime_2551, prime_7, by norm_num⟩
  · exact ⟨2557, 3, prime_2557, prime_3, by norm_num⟩
  · exact ⟨2557, 5, prime_2557, prime_5, by norm_num⟩
  · exact ⟨2557, 7, prime_2557, prime_7, by norm_num⟩
  · exact ⟨2549, 17, prime_2549, prime_17, by norm_num⟩
  · exact ⟨2557, 11, prime_2557, prime_11, by norm_num⟩
  · exact ⟨2557, 13, prime_2557, prime_13, by norm_num⟩
  · exact ⟨2549, 23, prime_2549, prime_23, by norm_num⟩
  · exact ⟨2557, 17, prime_2557, prime_17, by norm_num⟩
  · exact ⟨2557, 19, prime_2557, prime_19, by norm_num⟩
  · exact ⟨2549, 29, prime_2549, prime_29, by norm_num⟩
  · exact ⟨2557, 23, prime_2557, prime_23, by norm_num⟩
  · exact ⟨2579, 3, prime_2579, prime_3, by norm_num⟩
  · exact ⟨2579, 5, prime_2579, prime_5, by norm_num⟩
  · exact ⟨2579, 7, prime_2579, prime_7, by norm_num⟩
  · exact ⟨2557, 31, prime_2557, prime_31, by norm_num⟩
  · exact ⟨2579, 11, prime_2579, prime_11, by norm_num⟩
  · exact ⟨2579, 13, prime_2579, prime_13, by norm_num⟩
  · exact ⟨2591, 3, prime_2591, prime_3, by norm_num⟩
  · exact ⟨2593, 3, prime_2593, prime_3, by norm_num⟩
  · exact ⟨2593, 5, prime_2593, prime_5, by norm_num⟩
  · exact ⟨2593, 7, prime_2593, prime_7, by norm_num⟩
  · exact ⟨2591, 11, prime_2591, prime_11, by norm_num⟩

private theorem goldbach_chunk_13 : ∀ k : ℕ, 1302 ≤ k → k ≤ 1401 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2593, 11, prime_2593, prime_11, by norm_num⟩
  · exact ⟨2593, 13, prime_2593, prime_13, by norm_num⟩
  · exact ⟨2591, 17, prime_2591, prime_17, by norm_num⟩
  · exact ⟨2593, 17, prime_2593, prime_17, by norm_num⟩
  · exact ⟨2609, 3, prime_2609, prime_3, by norm_num⟩
  · exact ⟨2609, 5, prime_2609, prime_5, by norm_num⟩
  · exact ⟨2609, 7, prime_2609, prime_7, by norm_num⟩
  · exact ⟨2557, 61, prime_2557, prime_61, by norm_num⟩
  · exact ⟨2617, 3, prime_2617, prime_3, by norm_num⟩
  · exact ⟨2617, 5, prime_2617, prime_5, by norm_num⟩
  · exact ⟨2621, 3, prime_2621, prime_3, by norm_num⟩
  · exact ⟨2621, 5, prime_2621, prime_5, by norm_num⟩
  · exact ⟨2621, 7, prime_2621, prime_7, by norm_num⟩
  · exact ⟨2617, 13, prime_2617, prime_13, by norm_num⟩
  · exact ⟨2621, 11, prime_2621, prime_11, by norm_num⟩
  · exact ⟨2621, 13, prime_2621, prime_13, by norm_num⟩
  · exact ⟨2633, 3, prime_2633, prime_3, by norm_num⟩
  · exact ⟨2633, 5, prime_2633, prime_5, by norm_num⟩
  · exact ⟨2633, 7, prime_2633, prime_7, by norm_num⟩
  · exact ⟨2539, 103, prime_2539, prime_103, by norm_num⟩
  · exact ⟨2633, 11, prime_2633, prime_11, by norm_num⟩
  · exact ⟨2633, 13, prime_2633, prime_13, by norm_num⟩
  · exact ⟨2617, 31, prime_2617, prime_31, by norm_num⟩
  · exact ⟨2647, 3, prime_2647, prime_3, by norm_num⟩
  · exact ⟨2647, 5, prime_2647, prime_5, by norm_num⟩
  · exact ⟨2647, 7, prime_2647, prime_7, by norm_num⟩
  · exact ⟨2633, 23, prime_2633, prime_23, by norm_num⟩
  · exact ⟨2647, 11, prime_2647, prime_11, by norm_num⟩
  · exact ⟨2657, 3, prime_2657, prime_3, by norm_num⟩
  · exact ⟨2659, 3, prime_2659, prime_3, by norm_num⟩
  · exact ⟨2659, 5, prime_2659, prime_5, by norm_num⟩
  · exact ⟨2663, 3, prime_2663, prime_3, by norm_num⟩
  · exact ⟨2663, 5, prime_2663, prime_5, by norm_num⟩
  · exact ⟨2663, 7, prime_2663, prime_7, by norm_num⟩
  · exact ⟨2659, 13, prime_2659, prime_13, by norm_num⟩
  · exact ⟨2671, 3, prime_2671, prime_3, by norm_num⟩
  · exact ⟨2671, 5, prime_2671, prime_5, by norm_num⟩
  · exact ⟨2671, 7, prime_2671, prime_7, by norm_num⟩
  · exact ⟨2677, 3, prime_2677, prime_3, by norm_num⟩
  · exact ⟨2677, 5, prime_2677, prime_5, by norm_num⟩
  · exact ⟨2677, 7, prime_2677, prime_7, by norm_num⟩
  · exact ⟨2683, 3, prime_2683, prime_3, by norm_num⟩
  · exact ⟨2683, 5, prime_2683, prime_5, by norm_num⟩
  · exact ⟨2687, 3, prime_2687, prime_3, by norm_num⟩
  · exact ⟨2689, 3, prime_2689, prime_3, by norm_num⟩
  · exact ⟨2689, 5, prime_2689, prime_5, by norm_num⟩
  · exact ⟨2693, 3, prime_2693, prime_3, by norm_num⟩
  · exact ⟨2693, 5, prime_2693, prime_5, by norm_num⟩
  · exact ⟨2693, 7, prime_2693, prime_7, by norm_num⟩
  · exact ⟨2699, 3, prime_2699, prime_3, by norm_num⟩
  · exact ⟨2699, 5, prime_2699, prime_5, by norm_num⟩
  · exact ⟨2699, 7, prime_2699, prime_7, by norm_num⟩
  · exact ⟨2689, 19, prime_2689, prime_19, by norm_num⟩
  · exact ⟨2707, 3, prime_2707, prime_3, by norm_num⟩
  · exact ⟨2707, 5, prime_2707, prime_5, by norm_num⟩
  · exact ⟨2711, 3, prime_2711, prime_3, by norm_num⟩
  · exact ⟨2713, 3, prime_2713, prime_3, by norm_num⟩
  · exact ⟨2713, 5, prime_2713, prime_5, by norm_num⟩
  · exact ⟨2713, 7, prime_2713, prime_7, by norm_num⟩
  · exact ⟨2719, 3, prime_2719, prime_3, by norm_num⟩
  · exact ⟨2719, 5, prime_2719, prime_5, by norm_num⟩
  · exact ⟨2719, 7, prime_2719, prime_7, by norm_num⟩
  · exact ⟨2711, 17, prime_2711, prime_17, by norm_num⟩
  · exact ⟨2719, 11, prime_2719, prime_11, by norm_num⟩
  · exact ⟨2729, 3, prime_2729, prime_3, by norm_num⟩
  · exact ⟨2731, 3, prime_2731, prime_3, by norm_num⟩
  · exact ⟨2731, 5, prime_2731, prime_5, by norm_num⟩
  · exact ⟨2731, 7, prime_2731, prime_7, by norm_num⟩
  · exact ⟨2729, 11, prime_2729, prime_11, by norm_num⟩
  · exact ⟨2731, 11, prime_2731, prime_11, by norm_num⟩
  · exact ⟨2741, 3, prime_2741, prime_3, by norm_num⟩
  · exact ⟨2741, 5, prime_2741, prime_5, by norm_num⟩
  · exact ⟨2741, 7, prime_2741, prime_7, by norm_num⟩
  · exact ⟨2731, 19, prime_2731, prime_19, by norm_num⟩
  · exact ⟨2749, 3, prime_2749, prime_3, by norm_num⟩
  · exact ⟨2749, 5, prime_2749, prime_5, by norm_num⟩
  · exact ⟨2753, 3, prime_2753, prime_3, by norm_num⟩
  · exact ⟨2753, 5, prime_2753, prime_5, by norm_num⟩
  · exact ⟨2753, 7, prime_2753, prime_7, by norm_num⟩
  · exact ⟨2749, 13, prime_2749, prime_13, by norm_num⟩
  · exact ⟨2753, 11, prime_2753, prime_11, by norm_num⟩
  · exact ⟨2753, 13, prime_2753, prime_13, by norm_num⟩
  · exact ⟨2749, 19, prime_2749, prime_19, by norm_num⟩
  · exact ⟨2767, 3, prime_2767, prime_3, by norm_num⟩
  · exact ⟨2767, 5, prime_2767, prime_5, by norm_num⟩
  · exact ⟨2767, 7, prime_2767, prime_7, by norm_num⟩
  · exact ⟨2753, 23, prime_2753, prime_23, by norm_num⟩
  · exact ⟨2767, 11, prime_2767, prime_11, by norm_num⟩
  · exact ⟨2777, 3, prime_2777, prime_3, by norm_num⟩
  · exact ⟨2777, 5, prime_2777, prime_5, by norm_num⟩
  · exact ⟨2777, 7, prime_2777, prime_7, by norm_num⟩
  · exact ⟨2767, 19, prime_2767, prime_19, by norm_num⟩
  · exact ⟨2777, 11, prime_2777, prime_11, by norm_num⟩
  · exact ⟨2777, 13, prime_2777, prime_13, by norm_num⟩
  · exact ⟨2789, 3, prime_2789, prime_3, by norm_num⟩
  · exact ⟨2791, 3, prime_2791, prime_3, by norm_num⟩
  · exact ⟨2791, 5, prime_2791, prime_5, by norm_num⟩
  · exact ⟨2791, 7, prime_2791, prime_7, by norm_num⟩
  · exact ⟨2797, 3, prime_2797, prime_3, by norm_num⟩
  · exact ⟨2797, 5, prime_2797, prime_5, by norm_num⟩

private theorem goldbach_chunk_14 : ∀ k : ℕ, 1402 ≤ k → k ≤ 1501 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2801, 3, prime_2801, prime_3, by norm_num⟩
  · exact ⟨2803, 3, prime_2803, prime_3, by norm_num⟩
  · exact ⟨2803, 5, prime_2803, prime_5, by norm_num⟩
  · exact ⟨2803, 7, prime_2803, prime_7, by norm_num⟩
  · exact ⟨2801, 11, prime_2801, prime_11, by norm_num⟩
  · exact ⟨2803, 11, prime_2803, prime_11, by norm_num⟩
  · exact ⟨2803, 13, prime_2803, prime_13, by norm_num⟩
  · exact ⟨2801, 17, prime_2801, prime_17, by norm_num⟩
  · exact ⟨2803, 17, prime_2803, prime_17, by norm_num⟩
  · exact ⟨2819, 3, prime_2819, prime_3, by norm_num⟩
  · exact ⟨2819, 5, prime_2819, prime_5, by norm_num⟩
  · exact ⟨2819, 7, prime_2819, prime_7, by norm_num⟩
  · exact ⟨2797, 31, prime_2797, prime_31, by norm_num⟩
  · exact ⟨2819, 11, prime_2819, prime_11, by norm_num⟩
  · exact ⟨2819, 13, prime_2819, prime_13, by norm_num⟩
  · exact ⟨2803, 31, prime_2803, prime_31, by norm_num⟩
  · exact ⟨2833, 3, prime_2833, prime_3, by norm_num⟩
  · exact ⟨2833, 5, prime_2833, prime_5, by norm_num⟩
  · exact ⟨2837, 3, prime_2837, prime_3, by norm_num⟩
  · exact ⟨2837, 5, prime_2837, prime_5, by norm_num⟩
  · exact ⟨2837, 7, prime_2837, prime_7, by norm_num⟩
  · exact ⟨2843, 3, prime_2843, prime_3, by norm_num⟩
  · exact ⟨2843, 5, prime_2843, prime_5, by norm_num⟩
  · exact ⟨2843, 7, prime_2843, prime_7, by norm_num⟩
  · exact ⟨2833, 19, prime_2833, prime_19, by norm_num⟩
  · exact ⟨2851, 3, prime_2851, prime_3, by norm_num⟩
  · exact ⟨2851, 5, prime_2851, prime_5, by norm_num⟩
  · exact ⟨2851, 7, prime_2851, prime_7, by norm_num⟩
  · exact ⟨2857, 3, prime_2857, prime_3, by norm_num⟩
  · exact ⟨2857, 5, prime_2857, prime_5, by norm_num⟩
  · exact ⟨2861, 3, prime_2861, prime_3, by norm_num⟩
  · exact ⟨2861, 5, prime_2861, prime_5, by norm_num⟩
  · exact ⟨2861, 7, prime_2861, prime_7, by norm_num⟩
  · exact ⟨2857, 13, prime_2857, prime_13, by norm_num⟩
  · exact ⟨2861, 11, prime_2861, prime_11, by norm_num⟩
  · exact ⟨2861, 13, prime_2861, prime_13, by norm_num⟩
  · exact ⟨2857, 19, prime_2857, prime_19, by norm_num⟩
  · exact ⟨2861, 17, prime_2861, prime_17, by norm_num⟩
  · exact ⟨2861, 19, prime_2861, prime_19, by norm_num⟩
  · exact ⟨2879, 3, prime_2879, prime_3, by norm_num⟩
  · exact ⟨2879, 5, prime_2879, prime_5, by norm_num⟩
  · exact ⟨2879, 7, prime_2879, prime_7, by norm_num⟩
  · exact ⟨2857, 31, prime_2857, prime_31, by norm_num⟩
  · exact ⟨2887, 3, prime_2887, prime_3, by norm_num⟩
  · exact ⟨2887, 5, prime_2887, prime_5, by norm_num⟩
  · exact ⟨2887, 7, prime_2887, prime_7, by norm_num⟩
  · exact ⟨2879, 17, prime_2879, prime_17, by norm_num⟩
  · exact ⟨2887, 11, prime_2887, prime_11, by norm_num⟩
  · exact ⟨2897, 3, prime_2897, prime_3, by norm_num⟩
  · exact ⟨2897, 5, prime_2897, prime_5, by norm_num⟩
  · exact ⟨2897, 7, prime_2897, prime_7, by norm_num⟩
  · exact ⟨2903, 3, prime_2903, prime_3, by norm_num⟩
  · exact ⟨2903, 5, prime_2903, prime_5, by norm_num⟩
  · exact ⟨2903, 7, prime_2903, prime_7, by norm_num⟩
  · exact ⟨2909, 3, prime_2909, prime_3, by norm_num⟩
  · exact ⟨2909, 5, prime_2909, prime_5, by norm_num⟩
  · exact ⟨2909, 7, prime_2909, prime_7, by norm_num⟩
  · exact ⟨2887, 31, prime_2887, prime_31, by norm_num⟩
  · exact ⟨2917, 3, prime_2917, prime_3, by norm_num⟩
  · exact ⟨2917, 5, prime_2917, prime_5, by norm_num⟩
  · exact ⟨2917, 7, prime_2917, prime_7, by norm_num⟩
  · exact ⟨2909, 17, prime_2909, prime_17, by norm_num⟩
  · exact ⟨2917, 11, prime_2917, prime_11, by norm_num⟩
  · exact ⟨2927, 3, prime_2927, prime_3, by norm_num⟩
  · exact ⟨2927, 5, prime_2927, prime_5, by norm_num⟩
  · exact ⟨2927, 7, prime_2927, prime_7, by norm_num⟩
  · exact ⟨2917, 19, prime_2917, prime_19, by norm_num⟩
  · exact ⟨2927, 11, prime_2927, prime_11, by norm_num⟩
  · exact ⟨2927, 13, prime_2927, prime_13, by norm_num⟩
  · exact ⟨2939, 3, prime_2939, prime_3, by norm_num⟩
  · exact ⟨2939, 5, prime_2939, prime_5, by norm_num⟩
  · exact ⟨2939, 7, prime_2939, prime_7, by norm_num⟩
  · exact ⟨2917, 31, prime_2917, prime_31, by norm_num⟩
  · exact ⟨2939, 11, prime_2939, prime_11, by norm_num⟩
  · exact ⟨2939, 13, prime_2939, prime_13, by norm_num⟩
  · exact ⟨2917, 37, prime_2917, prime_37, by norm_num⟩
  · exact ⟨2953, 3, prime_2953, prime_3, by norm_num⟩
  · exact ⟨2953, 5, prime_2953, prime_5, by norm_num⟩
  · exact ⟨2957, 3, prime_2957, prime_3, by norm_num⟩
  · exact ⟨2957, 5, prime_2957, prime_5, by norm_num⟩
  · exact ⟨2957, 7, prime_2957, prime_7, by norm_num⟩
  · exact ⟨2963, 3, prime_2963, prime_3, by norm_num⟩
  · exact ⟨2963, 5, prime_2963, prime_5, by norm_num⟩
  · exact ⟨2963, 7, prime_2963, prime_7, by norm_num⟩
  · exact ⟨2969, 3, prime_2969, prime_3, by norm_num⟩
  · exact ⟨2971, 3, prime_2971, prime_3, by norm_num⟩
  · exact ⟨2971, 5, prime_2971, prime_5, by norm_num⟩
  · exact ⟨2971, 7, prime_2971, prime_7, by norm_num⟩
  · exact ⟨2969, 11, prime_2969, prime_11, by norm_num⟩
  · exact ⟨2971, 11, prime_2971, prime_11, by norm_num⟩
  · exact ⟨2971, 13, prime_2971, prime_13, by norm_num⟩
  · exact ⟨2969, 17, prime_2969, prime_17, by norm_num⟩
  · exact ⟨2971, 17, prime_2971, prime_17, by norm_num⟩
  · exact ⟨2971, 19, prime_2971, prime_19, by norm_num⟩
  · exact ⟨2969, 23, prime_2969, prime_23, by norm_num⟩
  · exact ⟨2971, 23, prime_2971, prime_23, by norm_num⟩
  · exact ⟨2953, 43, prime_2953, prime_43, by norm_num⟩
  · exact ⟨2969, 29, prime_2969, prime_29, by norm_num⟩
  · exact ⟨2971, 29, prime_2971, prime_29, by norm_num⟩
  · exact ⟨2999, 3, prime_2999, prime_3, by norm_num⟩

private theorem goldbach_chunk_15 : ∀ k : ℕ, 1502 ≤ k → k ≤ 1601 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3001, 3, prime_3001, prime_3, by norm_num⟩
  · exact ⟨3001, 5, prime_3001, prime_5, by norm_num⟩
  · exact ⟨3001, 7, prime_3001, prime_7, by norm_num⟩
  · exact ⟨2999, 11, prime_2999, prime_11, by norm_num⟩
  · exact ⟨3001, 11, prime_3001, prime_11, by norm_num⟩
  · exact ⟨3011, 3, prime_3011, prime_3, by norm_num⟩
  · exact ⟨3011, 5, prime_3011, prime_5, by norm_num⟩
  · exact ⟨3011, 7, prime_3011, prime_7, by norm_num⟩
  · exact ⟨3001, 19, prime_3001, prime_19, by norm_num⟩
  · exact ⟨3019, 3, prime_3019, prime_3, by norm_num⟩
  · exact ⟨3019, 5, prime_3019, prime_5, by norm_num⟩
  · exact ⟨3023, 3, prime_3023, prime_3, by norm_num⟩
  · exact ⟨3023, 5, prime_3023, prime_5, by norm_num⟩
  · exact ⟨3023, 7, prime_3023, prime_7, by norm_num⟩
  · exact ⟨3019, 13, prime_3019, prime_13, by norm_num⟩
  · exact ⟨3023, 11, prime_3023, prime_11, by norm_num⟩
  · exact ⟨3023, 13, prime_3023, prime_13, by norm_num⟩
  · exact ⟨3019, 19, prime_3019, prime_19, by norm_num⟩
  · exact ⟨3037, 3, prime_3037, prime_3, by norm_num⟩
  · exact ⟨3037, 5, prime_3037, prime_5, by norm_num⟩
  · exact ⟨3041, 3, prime_3041, prime_3, by norm_num⟩
  · exact ⟨3041, 5, prime_3041, prime_5, by norm_num⟩
  · exact ⟨3041, 7, prime_3041, prime_7, by norm_num⟩
  · exact ⟨3037, 13, prime_3037, prime_13, by norm_num⟩
  · exact ⟨3049, 3, prime_3049, prime_3, by norm_num⟩
  · exact ⟨3049, 5, prime_3049, prime_5, by norm_num⟩
  · exact ⟨3049, 7, prime_3049, prime_7, by norm_num⟩
  · exact ⟨3041, 17, prime_3041, prime_17, by norm_num⟩
  · exact ⟨3049, 11, prime_3049, prime_11, by norm_num⟩
  · exact ⟨3049, 13, prime_3049, prime_13, by norm_num⟩
  · exact ⟨3061, 3, prime_3061, prime_3, by norm_num⟩
  · exact ⟨3061, 5, prime_3061, prime_5, by norm_num⟩
  · exact ⟨3061, 7, prime_3061, prime_7, by norm_num⟩
  · exact ⟨3067, 3, prime_3067, prime_3, by norm_num⟩
  · exact ⟨3067, 5, prime_3067, prime_5, by norm_num⟩
  · exact ⟨3067, 7, prime_3067, prime_7, by norm_num⟩
  · exact ⟨3023, 53, prime_3023, prime_53, by norm_num⟩
  · exact ⟨3067, 11, prime_3067, prime_11, by norm_num⟩
  · exact ⟨3067, 13, prime_3067, prime_13, by norm_num⟩
  · exact ⟨3079, 3, prime_3079, prime_3, by norm_num⟩
  · exact ⟨3079, 5, prime_3079, prime_5, by norm_num⟩
  · exact ⟨3083, 3, prime_3083, prime_3, by norm_num⟩
  · exact ⟨3083, 5, prime_3083, prime_5, by norm_num⟩
  · exact ⟨3083, 7, prime_3083, prime_7, by norm_num⟩
  · exact ⟨3089, 3, prime_3089, prime_3, by norm_num⟩
  · exact ⟨3089, 5, prime_3089, prime_5, by norm_num⟩
  · exact ⟨3089, 7, prime_3089, prime_7, by norm_num⟩
  · exact ⟨3079, 19, prime_3079, prime_19, by norm_num⟩
  · exact ⟨3089, 11, prime_3089, prime_11, by norm_num⟩
  · exact ⟨3089, 13, prime_3089, prime_13, by norm_num⟩
  · exact ⟨3067, 37, prime_3067, prime_37, by norm_num⟩
  · exact ⟨3089, 17, prime_3089, prime_17, by norm_num⟩
  · exact ⟨3089, 19, prime_3089, prime_19, by norm_num⟩
  · exact ⟨3079, 31, prime_3079, prime_31, by norm_num⟩
  · exact ⟨3109, 3, prime_3109, prime_3, by norm_num⟩
  · exact ⟨3109, 5, prime_3109, prime_5, by norm_num⟩
  · exact ⟨3109, 7, prime_3109, prime_7, by norm_num⟩
  · exact ⟨3089, 29, prime_3089, prime_29, by norm_num⟩
  · exact ⟨3109, 11, prime_3109, prime_11, by norm_num⟩
  · exact ⟨3119, 3, prime_3119, prime_3, by norm_num⟩
  · exact ⟨3121, 3, prime_3121, prime_3, by norm_num⟩
  · exact ⟨3121, 5, prime_3121, prime_5, by norm_num⟩
  · exact ⟨3121, 7, prime_3121, prime_7, by norm_num⟩
  · exact ⟨3119, 11, prime_3119, prime_11, by norm_num⟩
  · exact ⟨3121, 11, prime_3121, prime_11, by norm_num⟩
  · exact ⟨3121, 13, prime_3121, prime_13, by norm_num⟩
  · exact ⟨3119, 17, prime_3119, prime_17, by norm_num⟩
  · exact ⟨3121, 17, prime_3121, prime_17, by norm_num⟩
  · exact ⟨3137, 3, prime_3137, prime_3, by norm_num⟩
  · exact ⟨3137, 5, prime_3137, prime_5, by norm_num⟩
  · exact ⟨3137, 7, prime_3137, prime_7, by norm_num⟩
  · exact ⟨3109, 37, prime_3109, prime_37, by norm_num⟩
  · exact ⟨3137, 11, prime_3137, prime_11, by norm_num⟩
  · exact ⟨3137, 13, prime_3137, prime_13, by norm_num⟩
  · exact ⟨3121, 31, prime_3121, prime_31, by norm_num⟩
  · exact ⟨3137, 17, prime_3137, prime_17, by norm_num⟩
  · exact ⟨3137, 19, prime_3137, prime_19, by norm_num⟩
  · exact ⟨3121, 37, prime_3121, prime_37, by norm_num⟩
  · exact ⟨3137, 23, prime_3137, prime_23, by norm_num⟩
  · exact ⟨3121, 41, prime_3121, prime_41, by norm_num⟩
  · exact ⟨3121, 43, prime_3121, prime_43, by norm_num⟩
  · exact ⟨3163, 3, prime_3163, prime_3, by norm_num⟩
  · exact ⟨3163, 5, prime_3163, prime_5, by norm_num⟩
  · exact ⟨3167, 3, prime_3167, prime_3, by norm_num⟩
  · exact ⟨3169, 3, prime_3169, prime_3, by norm_num⟩
  · exact ⟨3169, 5, prime_3169, prime_5, by norm_num⟩
  · exact ⟨3169, 7, prime_3169, prime_7, by norm_num⟩
  · exact ⟨3167, 11, prime_3167, prime_11, by norm_num⟩
  · exact ⟨3169, 11, prime_3169, prime_11, by norm_num⟩
  · exact ⟨3169, 13, prime_3169, prime_13, by norm_num⟩
  · exact ⟨3181, 3, prime_3181, prime_3, by norm_num⟩
  · exact ⟨3181, 5, prime_3181, prime_5, by norm_num⟩
  · exact ⟨3181, 7, prime_3181, prime_7, by norm_num⟩
  · exact ⟨3187, 3, prime_3187, prime_3, by norm_num⟩
  · exact ⟨3187, 5, prime_3187, prime_5, by norm_num⟩
  · exact ⟨3191, 3, prime_3191, prime_3, by norm_num⟩
  · exact ⟨3191, 5, prime_3191, prime_5, by norm_num⟩
  · exact ⟨3191, 7, prime_3191, prime_7, by norm_num⟩
  · exact ⟨3187, 13, prime_3187, prime_13, by norm_num⟩
  · exact ⟨3191, 11, prime_3191, prime_11, by norm_num⟩

private theorem goldbach_chunk_16 : ∀ k : ℕ, 1602 ≤ k → k ≤ 1701 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3191, 13, prime_3191, prime_13, by norm_num⟩
  · exact ⟨3203, 3, prime_3203, prime_3, by norm_num⟩
  · exact ⟨3203, 5, prime_3203, prime_5, by norm_num⟩
  · exact ⟨3203, 7, prime_3203, prime_7, by norm_num⟩
  · exact ⟨3209, 3, prime_3209, prime_3, by norm_num⟩
  · exact ⟨3209, 5, prime_3209, prime_5, by norm_num⟩
  · exact ⟨3209, 7, prime_3209, prime_7, by norm_num⟩
  · exact ⟨3187, 31, prime_3187, prime_31, by norm_num⟩
  · exact ⟨3217, 3, prime_3217, prime_3, by norm_num⟩
  · exact ⟨3217, 5, prime_3217, prime_5, by norm_num⟩
  · exact ⟨3221, 3, prime_3221, prime_3, by norm_num⟩
  · exact ⟨3221, 5, prime_3221, prime_5, by norm_num⟩
  · exact ⟨3221, 7, prime_3221, prime_7, by norm_num⟩
  · exact ⟨3217, 13, prime_3217, prime_13, by norm_num⟩
  · exact ⟨3229, 3, prime_3229, prime_3, by norm_num⟩
  · exact ⟨3229, 5, prime_3229, prime_5, by norm_num⟩
  · exact ⟨3229, 7, prime_3229, prime_7, by norm_num⟩
  · exact ⟨3221, 17, prime_3221, prime_17, by norm_num⟩
  · exact ⟨3229, 11, prime_3229, prime_11, by norm_num⟩
  · exact ⟨3229, 13, prime_3229, prime_13, by norm_num⟩
  · exact ⟨3221, 23, prime_3221, prime_23, by norm_num⟩
  · exact ⟨3229, 17, prime_3229, prime_17, by norm_num⟩
  · exact ⟨3229, 19, prime_3229, prime_19, by norm_num⟩
  · exact ⟨3221, 29, prime_3221, prime_29, by norm_num⟩
  · exact ⟨3229, 23, prime_3229, prime_23, by norm_num⟩
  · exact ⟨3251, 3, prime_3251, prime_3, by norm_num⟩
  · exact ⟨3253, 3, prime_3253, prime_3, by norm_num⟩
  · exact ⟨3253, 5, prime_3253, prime_5, by norm_num⟩
  · exact ⟨3257, 3, prime_3257, prime_3, by norm_num⟩
  · exact ⟨3259, 3, prime_3259, prime_3, by norm_num⟩
  · exact ⟨3259, 5, prime_3259, prime_5, by norm_num⟩
  · exact ⟨3259, 7, prime_3259, prime_7, by norm_num⟩
  · exact ⟨3257, 11, prime_3257, prime_11, by norm_num⟩
  · exact ⟨3259, 11, prime_3259, prime_11, by norm_num⟩
  · exact ⟨3259, 13, prime_3259, prime_13, by norm_num⟩
  · exact ⟨3271, 3, prime_3271, prime_3, by norm_num⟩
  · exact ⟨3271, 5, prime_3271, prime_5, by norm_num⟩
  · exact ⟨3271, 7, prime_3271, prime_7, by norm_num⟩
  · exact ⟨3257, 23, prime_3257, prime_23, by norm_num⟩
  · exact ⟨3271, 11, prime_3271, prime_11, by norm_num⟩
  · exact ⟨3271, 13, prime_3271, prime_13, by norm_num⟩
  · exact ⟨3257, 29, prime_3257, prime_29, by norm_num⟩
  · exact ⟨3271, 17, prime_3271, prime_17, by norm_num⟩
  · exact ⟨3271, 19, prime_3271, prime_19, by norm_num⟩
  · exact ⟨3251, 41, prime_3251, prime_41, by norm_num⟩
  · exact ⟨3271, 23, prime_3271, prime_23, by norm_num⟩
  · exact ⟨3259, 37, prime_3259, prime_37, by norm_num⟩
  · exact ⟨3257, 41, prime_3257, prime_41, by norm_num⟩
  · exact ⟨3271, 29, prime_3271, prime_29, by norm_num⟩
  · exact ⟨3299, 3, prime_3299, prime_3, by norm_num⟩
  · exact ⟨3301, 3, prime_3301, prime_3, by norm_num⟩
  · exact ⟨3301, 5, prime_3301, prime_5, by norm_num⟩
  · exact ⟨3301, 7, prime_3301, prime_7, by norm_num⟩
  · exact ⟨3307, 3, prime_3307, prime_3, by norm_num⟩
  · exact ⟨3307, 5, prime_3307, prime_5, by norm_num⟩
  · exact ⟨3307, 7, prime_3307, prime_7, by norm_num⟩
  · exact ⟨3313, 3, prime_3313, prime_3, by norm_num⟩
  · exact ⟨3313, 5, prime_3313, prime_5, by norm_num⟩
  · exact ⟨3313, 7, prime_3313, prime_7, by norm_num⟩
  · exact ⟨3319, 3, prime_3319, prime_3, by norm_num⟩
  · exact ⟨3319, 5, prime_3319, prime_5, by norm_num⟩
  · exact ⟨3323, 3, prime_3323, prime_3, by norm_num⟩
  · exact ⟨3323, 5, prime_3323, prime_5, by norm_num⟩
  · exact ⟨3323, 7, prime_3323, prime_7, by norm_num⟩
  · exact ⟨3329, 3, prime_3329, prime_3, by norm_num⟩
  · exact ⟨3331, 3, prime_3331, prime_3, by norm_num⟩
  · exact ⟨3331, 5, prime_3331, prime_5, by norm_num⟩
  · exact ⟨3331, 7, prime_3331, prime_7, by norm_num⟩
  · exact ⟨3329, 11, prime_3329, prime_11, by norm_num⟩
  · exact ⟨3331, 11, prime_3331, prime_11, by norm_num⟩
  · exact ⟨3331, 13, prime_3331, prime_13, by norm_num⟩
  · exact ⟨3343, 3, prime_3343, prime_3, by norm_num⟩
  · exact ⟨3343, 5, prime_3343, prime_5, by norm_num⟩
  · exact ⟨3347, 3, prime_3347, prime_3, by norm_num⟩
  · exact ⟨3347, 5, prime_3347, prime_5, by norm_num⟩
  · exact ⟨3347, 7, prime_3347, prime_7, by norm_num⟩
  · exact ⟨3343, 13, prime_3343, prime_13, by norm_num⟩
  · exact ⟨3347, 11, prime_3347, prime_11, by norm_num⟩
  · exact ⟨3347, 13, prime_3347, prime_13, by norm_num⟩
  · exact ⟨3359, 3, prime_3359, prime_3, by norm_num⟩
  · exact ⟨3361, 3, prime_3361, prime_3, by norm_num⟩
  · exact ⟨3361, 5, prime_3361, prime_5, by norm_num⟩
  · exact ⟨3361, 7, prime_3361, prime_7, by norm_num⟩
  · exact ⟨3359, 11, prime_3359, prime_11, by norm_num⟩
  · exact ⟨3361, 11, prime_3361, prime_11, by norm_num⟩
  · exact ⟨3371, 3, prime_3371, prime_3, by norm_num⟩
  · exact ⟨3373, 3, prime_3373, prime_3, by norm_num⟩
  · exact ⟨3373, 5, prime_3373, prime_5, by norm_num⟩
  · exact ⟨3373, 7, prime_3373, prime_7, by norm_num⟩
  · exact ⟨3371, 11, prime_3371, prime_11, by norm_num⟩
  · exact ⟨3373, 11, prime_3373, prime_11, by norm_num⟩
  · exact ⟨3373, 13, prime_3373, prime_13, by norm_num⟩
  · exact ⟨3371, 17, prime_3371, prime_17, by norm_num⟩
  · exact ⟨3373, 17, prime_3373, prime_17, by norm_num⟩
  · exact ⟨3389, 3, prime_3389, prime_3, by norm_num⟩
  · exact ⟨3391, 3, prime_3391, prime_3, by norm_num⟩
  · exact ⟨3391, 5, prime_3391, prime_5, by norm_num⟩
  · exact ⟨3391, 7, prime_3391, prime_7, by norm_num⟩
  · exact ⟨3389, 11, prime_3389, prime_11, by norm_num⟩
  · exact ⟨3391, 11, prime_3391, prime_11, by norm_num⟩

private theorem goldbach_chunk_17 : ∀ k : ℕ, 1702 ≤ k → k ≤ 1801 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3391, 13, prime_3391, prime_13, by norm_num⟩
  · exact ⟨3389, 17, prime_3389, prime_17, by norm_num⟩
  · exact ⟨3391, 17, prime_3391, prime_17, by norm_num⟩
  · exact ⟨3407, 3, prime_3407, prime_3, by norm_num⟩
  · exact ⟨3407, 5, prime_3407, prime_5, by norm_num⟩
  · exact ⟨3407, 7, prime_3407, prime_7, by norm_num⟩
  · exact ⟨3413, 3, prime_3413, prime_3, by norm_num⟩
  · exact ⟨3413, 5, prime_3413, prime_5, by norm_num⟩
  · exact ⟨3413, 7, prime_3413, prime_7, by norm_num⟩
  · exact ⟨3391, 31, prime_3391, prime_31, by norm_num⟩
  · exact ⟨3413, 11, prime_3413, prime_11, by norm_num⟩
  · exact ⟨3413, 13, prime_3413, prime_13, by norm_num⟩
  · exact ⟨3391, 37, prime_3391, prime_37, by norm_num⟩
  · exact ⟨3413, 17, prime_3413, prime_17, by norm_num⟩
  · exact ⟨3413, 19, prime_3413, prime_19, by norm_num⟩
  · exact ⟨3391, 43, prime_3391, prime_43, by norm_num⟩
  · exact ⟨3433, 3, prime_3433, prime_3, by norm_num⟩
  · exact ⟨3433, 5, prime_3433, prime_5, by norm_num⟩
  · exact ⟨3433, 7, prime_3433, prime_7, by norm_num⟩
  · exact ⟨3413, 29, prime_3413, prime_29, by norm_num⟩
  · exact ⟨3433, 11, prime_3433, prime_11, by norm_num⟩
  · exact ⟨3433, 13, prime_3433, prime_13, by norm_num⟩
  · exact ⟨3407, 41, prime_3407, prime_41, by norm_num⟩
  · exact ⟨3433, 17, prime_3433, prime_17, by norm_num⟩
  · exact ⟨3449, 3, prime_3449, prime_3, by norm_num⟩
  · exact ⟨3449, 5, prime_3449, prime_5, by norm_num⟩
  · exact ⟨3449, 7, prime_3449, prime_7, by norm_num⟩
  · exact ⟨3391, 67, prime_3391, prime_67, by norm_num⟩
  · exact ⟨3457, 3, prime_3457, prime_3, by norm_num⟩
  · exact ⟨3457, 5, prime_3457, prime_5, by norm_num⟩
  · exact ⟨3461, 3, prime_3461, prime_3, by norm_num⟩
  · exact ⟨3463, 3, prime_3463, prime_3, by norm_num⟩
  · exact ⟨3463, 5, prime_3463, prime_5, by norm_num⟩
  · exact ⟨3467, 3, prime_3467, prime_3, by norm_num⟩
  · exact ⟨3469, 3, prime_3469, prime_3, by norm_num⟩
  · exact ⟨3469, 5, prime_3469, prime_5, by norm_num⟩
  · exact ⟨3469, 7, prime_3469, prime_7, by norm_num⟩
  · exact ⟨3467, 11, prime_3467, prime_11, by norm_num⟩
  · exact ⟨3469, 11, prime_3469, prime_11, by norm_num⟩
  · exact ⟨3469, 13, prime_3469, prime_13, by norm_num⟩
  · exact ⟨3467, 17, prime_3467, prime_17, by norm_num⟩
  · exact ⟨3469, 17, prime_3469, prime_17, by norm_num⟩
  · exact ⟨3469, 19, prime_3469, prime_19, by norm_num⟩
  · exact ⟨3467, 23, prime_3467, prime_23, by norm_num⟩
  · exact ⟨3469, 23, prime_3469, prime_23, by norm_num⟩
  · exact ⟨3491, 3, prime_3491, prime_3, by norm_num⟩
  · exact ⟨3491, 5, prime_3491, prime_5, by norm_num⟩
  · exact ⟨3491, 7, prime_3491, prime_7, by norm_num⟩
  · exact ⟨3469, 31, prime_3469, prime_31, by norm_num⟩
  · exact ⟨3499, 3, prime_3499, prime_3, by norm_num⟩
  · exact ⟨3499, 5, prime_3499, prime_5, by norm_num⟩
  · exact ⟨3499, 7, prime_3499, prime_7, by norm_num⟩
  · exact ⟨3491, 17, prime_3491, prime_17, by norm_num⟩
  · exact ⟨3499, 11, prime_3499, prime_11, by norm_num⟩
  · exact ⟨3499, 13, prime_3499, prime_13, by norm_num⟩
  · exact ⟨3511, 3, prime_3511, prime_3, by norm_num⟩
  · exact ⟨3511, 5, prime_3511, prime_5, by norm_num⟩
  · exact ⟨3511, 7, prime_3511, prime_7, by norm_num⟩
  · exact ⟨3517, 3, prime_3517, prime_3, by norm_num⟩
  · exact ⟨3517, 5, prime_3517, prime_5, by norm_num⟩
  · exact ⟨3517, 7, prime_3517, prime_7, by norm_num⟩
  · exact ⟨3467, 59, prime_3467, prime_59, by norm_num⟩
  · exact ⟨3517, 11, prime_3517, prime_11, by norm_num⟩
  · exact ⟨3527, 3, prime_3527, prime_3, by norm_num⟩
  · exact ⟨3529, 3, prime_3529, prime_3, by norm_num⟩
  · exact ⟨3529, 5, prime_3529, prime_5, by norm_num⟩
  · exact ⟨3533, 3, prime_3533, prime_3, by norm_num⟩
  · exact ⟨3533, 5, prime_3533, prime_5, by norm_num⟩
  · exact ⟨3533, 7, prime_3533, prime_7, by norm_num⟩
  · exact ⟨3539, 3, prime_3539, prime_3, by norm_num⟩
  · exact ⟨3541, 3, prime_3541, prime_3, by norm_num⟩
  · exact ⟨3541, 5, prime_3541, prime_5, by norm_num⟩
  · exact ⟨3541, 7, prime_3541, prime_7, by norm_num⟩
  · exact ⟨3547, 3, prime_3547, prime_3, by norm_num⟩
  · exact ⟨3547, 5, prime_3547, prime_5, by norm_num⟩
  · exact ⟨3547, 7, prime_3547, prime_7, by norm_num⟩
  · exact ⟨3539, 17, prime_3539, prime_17, by norm_num⟩
  · exact ⟨3547, 11, prime_3547, prime_11, by norm_num⟩
  · exact ⟨3557, 3, prime_3557, prime_3, by norm_num⟩
  · exact ⟨3559, 3, prime_3559, prime_3, by norm_num⟩
  · exact ⟨3559, 5, prime_3559, prime_5, by norm_num⟩
  · exact ⟨3559, 7, prime_3559, prime_7, by norm_num⟩
  · exact ⟨3557, 11, prime_3557, prime_11, by norm_num⟩
  · exact ⟨3559, 11, prime_3559, prime_11, by norm_num⟩
  · exact ⟨3559, 13, prime_3559, prime_13, by norm_num⟩
  · exact ⟨3571, 3, prime_3571, prime_3, by norm_num⟩
  · exact ⟨3571, 5, prime_3571, prime_5, by norm_num⟩
  · exact ⟨3571, 7, prime_3571, prime_7, by norm_num⟩
  · exact ⟨3557, 23, prime_3557, prime_23, by norm_num⟩
  · exact ⟨3571, 11, prime_3571, prime_11, by norm_num⟩
  · exact ⟨3581, 3, prime_3581, prime_3, by norm_num⟩
  · exact ⟨3583, 3, prime_3583, prime_3, by norm_num⟩
  · exact ⟨3583, 5, prime_3583, prime_5, by norm_num⟩
  · exact ⟨3583, 7, prime_3583, prime_7, by norm_num⟩
  · exact ⟨3581, 11, prime_3581, prime_11, by norm_num⟩
  · exact ⟨3583, 11, prime_3583, prime_11, by norm_num⟩
  · exact ⟨3593, 3, prime_3593, prime_3, by norm_num⟩
  · exact ⟨3593, 5, prime_3593, prime_5, by norm_num⟩
  · exact ⟨3593, 7, prime_3593, prime_7, by norm_num⟩
  · exact ⟨3583, 19, prime_3583, prime_19, by norm_num⟩

private theorem goldbach_chunk_18 : ∀ k : ℕ, 1802 ≤ k → k ≤ 1901 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3593, 11, prime_3593, prime_11, by norm_num⟩
  · exact ⟨3593, 13, prime_3593, prime_13, by norm_num⟩
  · exact ⟨3571, 37, prime_3571, prime_37, by norm_num⟩
  · exact ⟨3607, 3, prime_3607, prime_3, by norm_num⟩
  · exact ⟨3607, 5, prime_3607, prime_5, by norm_num⟩
  · exact ⟨3607, 7, prime_3607, prime_7, by norm_num⟩
  · exact ⟨3613, 3, prime_3613, prime_3, by norm_num⟩
  · exact ⟨3613, 5, prime_3613, prime_5, by norm_num⟩
  · exact ⟨3617, 3, prime_3617, prime_3, by norm_num⟩
  · exact ⟨3617, 5, prime_3617, prime_5, by norm_num⟩
  · exact ⟨3617, 7, prime_3617, prime_7, by norm_num⟩
  · exact ⟨3623, 3, prime_3623, prime_3, by norm_num⟩
  · exact ⟨3623, 5, prime_3623, prime_5, by norm_num⟩
  · exact ⟨3623, 7, prime_3623, prime_7, by norm_num⟩
  · exact ⟨3613, 19, prime_3613, prime_19, by norm_num⟩
  · exact ⟨3631, 3, prime_3631, prime_3, by norm_num⟩
  · exact ⟨3631, 5, prime_3631, prime_5, by norm_num⟩
  · exact ⟨3631, 7, prime_3631, prime_7, by norm_num⟩
  · exact ⟨3637, 3, prime_3637, prime_3, by norm_num⟩
  · exact ⟨3637, 5, prime_3637, prime_5, by norm_num⟩
  · exact ⟨3637, 7, prime_3637, prime_7, by norm_num⟩
  · exact ⟨3643, 3, prime_3643, prime_3, by norm_num⟩
  · exact ⟨3643, 5, prime_3643, prime_5, by norm_num⟩
  · exact ⟨3643, 7, prime_3643, prime_7, by norm_num⟩
  · exact ⟨3623, 29, prime_3623, prime_29, by norm_num⟩
  · exact ⟨3643, 11, prime_3643, prime_11, by norm_num⟩
  · exact ⟨3643, 13, prime_3643, prime_13, by norm_num⟩
  · exact ⟨3617, 41, prime_3617, prime_41, by norm_num⟩
  · exact ⟨3643, 17, prime_3643, prime_17, by norm_num⟩
  · exact ⟨3659, 3, prime_3659, prime_3, by norm_num⟩
  · exact ⟨3659, 5, prime_3659, prime_5, by norm_num⟩
  · exact ⟨3659, 7, prime_3659, prime_7, by norm_num⟩
  · exact ⟨3637, 31, prime_3637, prime_31, by norm_num⟩
  · exact ⟨3659, 11, prime_3659, prime_11, by norm_num⟩
  · exact ⟨3659, 13, prime_3659, prime_13, by norm_num⟩
  · exact ⟨3671, 3, prime_3671, prime_3, by norm_num⟩
  · exact ⟨3673, 3, prime_3673, prime_3, by norm_num⟩
  · exact ⟨3673, 5, prime_3673, prime_5, by norm_num⟩
  · exact ⟨3677, 3, prime_3677, prime_3, by norm_num⟩
  · exact ⟨3677, 5, prime_3677, prime_5, by norm_num⟩
  · exact ⟨3677, 7, prime_3677, prime_7, by norm_num⟩
  · exact ⟨3673, 13, prime_3673, prime_13, by norm_num⟩
  · exact ⟨3677, 11, prime_3677, prime_11, by norm_num⟩
  · exact ⟨3677, 13, prime_3677, prime_13, by norm_num⟩
  · exact ⟨3673, 19, prime_3673, prime_19, by norm_num⟩
  · exact ⟨3691, 3, prime_3691, prime_3, by norm_num⟩
  · exact ⟨3691, 5, prime_3691, prime_5, by norm_num⟩
  · exact ⟨3691, 7, prime_3691, prime_7, by norm_num⟩
  · exact ⟨3697, 3, prime_3697, prime_3, by norm_num⟩
  · exact ⟨3697, 5, prime_3697, prime_5, by norm_num⟩
  · exact ⟨3701, 3, prime_3701, prime_3, by norm_num⟩
  · exact ⟨3701, 5, prime_3701, prime_5, by norm_num⟩
  · exact ⟨3701, 7, prime_3701, prime_7, by norm_num⟩
  · exact ⟨3697, 13, prime_3697, prime_13, by norm_num⟩
  · exact ⟨3709, 3, prime_3709, prime_3, by norm_num⟩
  · exact ⟨3709, 5, prime_3709, prime_5, by norm_num⟩
  · exact ⟨3709, 7, prime_3709, prime_7, by norm_num⟩
  · exact ⟨3701, 17, prime_3701, prime_17, by norm_num⟩
  · exact ⟨3709, 11, prime_3709, prime_11, by norm_num⟩
  · exact ⟨3719, 3, prime_3719, prime_3, by norm_num⟩
  · exact ⟨3719, 5, prime_3719, prime_5, by norm_num⟩
  · exact ⟨3719, 7, prime_3719, prime_7, by norm_num⟩
  · exact ⟨3709, 19, prime_3709, prime_19, by norm_num⟩
  · exact ⟨3727, 3, prime_3727, prime_3, by norm_num⟩
  · exact ⟨3727, 5, prime_3727, prime_5, by norm_num⟩
  · exact ⟨3727, 7, prime_3727, prime_7, by norm_num⟩
  · exact ⟨3733, 3, prime_3733, prime_3, by norm_num⟩
  · exact ⟨3733, 5, prime_3733, prime_5, by norm_num⟩
  · exact ⟨3733, 7, prime_3733, prime_7, by norm_num⟩
  · exact ⟨3739, 3, prime_3739, prime_3, by norm_num⟩
  · exact ⟨3739, 5, prime_3739, prime_5, by norm_num⟩
  · exact ⟨3739, 7, prime_3739, prime_7, by norm_num⟩
  · exact ⟨3719, 29, prime_3719, prime_29, by norm_num⟩
  · exact ⟨3739, 11, prime_3739, prime_11, by norm_num⟩
  · exact ⟨3739, 13, prime_3739, prime_13, by norm_num⟩
  · exact ⟨3701, 53, prime_3701, prime_53, by norm_num⟩
  · exact ⟨3739, 17, prime_3739, prime_17, by norm_num⟩
  · exact ⟨3739, 19, prime_3739, prime_19, by norm_num⟩
  · exact ⟨3719, 41, prime_3719, prime_41, by norm_num⟩
  · exact ⟨3739, 23, prime_3739, prime_23, by norm_num⟩
  · exact ⟨3761, 3, prime_3761, prime_3, by norm_num⟩
  · exact ⟨3761, 5, prime_3761, prime_5, by norm_num⟩
  · exact ⟨3761, 7, prime_3761, prime_7, by norm_num⟩
  · exact ⟨3767, 3, prime_3767, prime_3, by norm_num⟩
  · exact ⟨3769, 3, prime_3769, prime_3, by norm_num⟩
  · exact ⟨3769, 5, prime_3769, prime_5, by norm_num⟩
  · exact ⟨3769, 7, prime_3769, prime_7, by norm_num⟩
  · exact ⟨3767, 11, prime_3767, prime_11, by norm_num⟩
  · exact ⟨3769, 11, prime_3769, prime_11, by norm_num⟩
  · exact ⟨3779, 3, prime_3779, prime_3, by norm_num⟩
  · exact ⟨3779, 5, prime_3779, prime_5, by norm_num⟩
  · exact ⟨3779, 7, prime_3779, prime_7, by norm_num⟩
  · exact ⟨3769, 19, prime_3769, prime_19, by norm_num⟩
  · exact ⟨3779, 11, prime_3779, prime_11, by norm_num⟩
  · exact ⟨3779, 13, prime_3779, prime_13, by norm_num⟩
  · exact ⟨3733, 61, prime_3733, prime_61, by norm_num⟩
  · exact ⟨3793, 3, prime_3793, prime_3, by norm_num⟩
  · exact ⟨3793, 5, prime_3793, prime_5, by norm_num⟩
  · exact ⟨3797, 3, prime_3797, prime_3, by norm_num⟩
  · exact ⟨3797, 5, prime_3797, prime_5, by norm_num⟩

private theorem goldbach_chunk_19 : ∀ k : ℕ, 1902 ≤ k → k ≤ 2001 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3797, 7, prime_3797, prime_7, by norm_num⟩
  · exact ⟨3803, 3, prime_3803, prime_3, by norm_num⟩
  · exact ⟨3803, 5, prime_3803, prime_5, by norm_num⟩
  · exact ⟨3803, 7, prime_3803, prime_7, by norm_num⟩
  · exact ⟨3793, 19, prime_3793, prime_19, by norm_num⟩
  · exact ⟨3803, 11, prime_3803, prime_11, by norm_num⟩
  · exact ⟨3803, 13, prime_3803, prime_13, by norm_num⟩
  · exact ⟨3739, 79, prime_3739, prime_79, by norm_num⟩
  · exact ⟨3803, 17, prime_3803, prime_17, by norm_num⟩
  · exact ⟨3803, 19, prime_3803, prime_19, by norm_num⟩
  · exact ⟨3821, 3, prime_3821, prime_3, by norm_num⟩
  · exact ⟨3823, 3, prime_3823, prime_3, by norm_num⟩
  · exact ⟨3823, 5, prime_3823, prime_5, by norm_num⟩
  · exact ⟨3823, 7, prime_3823, prime_7, by norm_num⟩
  · exact ⟨3821, 11, prime_3821, prime_11, by norm_num⟩
  · exact ⟨3823, 11, prime_3823, prime_11, by norm_num⟩
  · exact ⟨3833, 3, prime_3833, prime_3, by norm_num⟩
  · exact ⟨3833, 5, prime_3833, prime_5, by norm_num⟩
  · exact ⟨3833, 7, prime_3833, prime_7, by norm_num⟩
  · exact ⟨3823, 19, prime_3823, prime_19, by norm_num⟩
  · exact ⟨3833, 11, prime_3833, prime_11, by norm_num⟩
  · exact ⟨3833, 13, prime_3833, prime_13, by norm_num⟩
  · exact ⟨3769, 79, prime_3769, prime_79, by norm_num⟩
  · exact ⟨3847, 3, prime_3847, prime_3, by norm_num⟩
  · exact ⟨3847, 5, prime_3847, prime_5, by norm_num⟩
  · exact ⟨3851, 3, prime_3851, prime_3, by norm_num⟩
  · exact ⟨3853, 3, prime_3853, prime_3, by norm_num⟩
  · exact ⟨3853, 5, prime_3853, prime_5, by norm_num⟩
  · exact ⟨3853, 7, prime_3853, prime_7, by norm_num⟩
  · exact ⟨3851, 11, prime_3851, prime_11, by norm_num⟩
  · exact ⟨3853, 11, prime_3853, prime_11, by norm_num⟩
  · exact ⟨3863, 3, prime_3863, prime_3, by norm_num⟩
  · exact ⟨3863, 5, prime_3863, prime_5, by norm_num⟩
  · exact ⟨3863, 7, prime_3863, prime_7, by norm_num⟩
  · exact ⟨3853, 19, prime_3853, prime_19, by norm_num⟩
  · exact ⟨3863, 11, prime_3863, prime_11, by norm_num⟩
  · exact ⟨3863, 13, prime_3863, prime_13, by norm_num⟩
  · exact ⟨3847, 31, prime_3847, prime_31, by norm_num⟩
  · exact ⟨3877, 3, prime_3877, prime_3, by norm_num⟩
  · exact ⟨3877, 5, prime_3877, prime_5, by norm_num⟩
  · exact ⟨3881, 3, prime_3881, prime_3, by norm_num⟩
  · exact ⟨3881, 5, prime_3881, prime_5, by norm_num⟩
  · exact ⟨3881, 7, prime_3881, prime_7, by norm_num⟩
  · exact ⟨3877, 13, prime_3877, prime_13, by norm_num⟩
  · exact ⟨3889, 3, prime_3889, prime_3, by norm_num⟩
  · exact ⟨3889, 5, prime_3889, prime_5, by norm_num⟩
  · exact ⟨3889, 7, prime_3889, prime_7, by norm_num⟩
  · exact ⟨3881, 17, prime_3881, prime_17, by norm_num⟩
  · exact ⟨3889, 11, prime_3889, prime_11, by norm_num⟩
  · exact ⟨3889, 13, prime_3889, prime_13, by norm_num⟩
  · exact ⟨3881, 23, prime_3881, prime_23, by norm_num⟩
  · exact ⟨3889, 17, prime_3889, prime_17, by norm_num⟩
  · exact ⟨3889, 19, prime_3889, prime_19, by norm_num⟩
  · exact ⟨3907, 3, prime_3907, prime_3, by norm_num⟩
  · exact ⟨3907, 5, prime_3907, prime_5, by norm_num⟩
  · exact ⟨3911, 3, prime_3911, prime_3, by norm_num⟩
  · exact ⟨3911, 5, prime_3911, prime_5, by norm_num⟩
  · exact ⟨3911, 7, prime_3911, prime_7, by norm_num⟩
  · exact ⟨3917, 3, prime_3917, prime_3, by norm_num⟩
  · exact ⟨3919, 3, prime_3919, prime_3, by norm_num⟩
  · exact ⟨3919, 5, prime_3919, prime_5, by norm_num⟩
  · exact ⟨3923, 3, prime_3923, prime_3, by norm_num⟩
  · exact ⟨3923, 5, prime_3923, prime_5, by norm_num⟩
  · exact ⟨3923, 7, prime_3923, prime_7, by norm_num⟩
  · exact ⟨3929, 3, prime_3929, prime_3, by norm_num⟩
  · exact ⟨3931, 3, prime_3931, prime_3, by norm_num⟩
  · exact ⟨3931, 5, prime_3931, prime_5, by norm_num⟩
  · exact ⟨3931, 7, prime_3931, prime_7, by norm_num⟩
  · exact ⟨3929, 11, prime_3929, prime_11, by norm_num⟩
  · exact ⟨3931, 11, prime_3931, prime_11, by norm_num⟩
  · exact ⟨3931, 13, prime_3931, prime_13, by norm_num⟩
  · exact ⟨3943, 3, prime_3943, prime_3, by norm_num⟩
  · exact ⟨3943, 5, prime_3943, prime_5, by norm_num⟩
  · exact ⟨3947, 3, prime_3947, prime_3, by norm_num⟩
  · exact ⟨3947, 5, prime_3947, prime_5, by norm_num⟩
  · exact ⟨3947, 7, prime_3947, prime_7, by norm_num⟩
  · exact ⟨3943, 13, prime_3943, prime_13, by norm_num⟩
  · exact ⟨3947, 11, prime_3947, prime_11, by norm_num⟩
  · exact ⟨3947, 13, prime_3947, prime_13, by norm_num⟩
  · exact ⟨3943, 19, prime_3943, prime_19, by norm_num⟩
  · exact ⟨3947, 17, prime_3947, prime_17, by norm_num⟩
  · exact ⟨3947, 19, prime_3947, prime_19, by norm_num⟩
  · exact ⟨3931, 37, prime_3931, prime_37, by norm_num⟩
  · exact ⟨3967, 3, prime_3967, prime_3, by norm_num⟩
  · exact ⟨3967, 5, prime_3967, prime_5, by norm_num⟩
  · exact ⟨3967, 7, prime_3967, prime_7, by norm_num⟩
  · exact ⟨3947, 29, prime_3947, prime_29, by norm_num⟩
  · exact ⟨3967, 11, prime_3967, prime_11, by norm_num⟩
  · exact ⟨3967, 13, prime_3967, prime_13, by norm_num⟩
  · exact ⟨3929, 53, prime_3929, prime_53, by norm_num⟩
  · exact ⟨3967, 17, prime_3967, prime_17, by norm_num⟩
  · exact ⟨3967, 19, prime_3967, prime_19, by norm_num⟩
  · exact ⟨3947, 41, prime_3947, prime_41, by norm_num⟩
  · exact ⟨3967, 23, prime_3967, prime_23, by norm_num⟩
  · exact ⟨3989, 3, prime_3989, prime_3, by norm_num⟩
  · exact ⟨3989, 5, prime_3989, prime_5, by norm_num⟩
  · exact ⟨3989, 7, prime_3989, prime_7, by norm_num⟩
  · exact ⟨3967, 31, prime_3967, prime_31, by norm_num⟩
  · exact ⟨3989, 11, prime_3989, prime_11, by norm_num⟩
  · exact ⟨3989, 13, prime_3989, prime_13, by norm_num⟩

private theorem goldbach_chunk_20 : ∀ k : ℕ, 2002 ≤ k → k ≤ 2101 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4001, 3, prime_4001, prime_3, by norm_num⟩
  · exact ⟨4003, 3, prime_4003, prime_3, by norm_num⟩
  · exact ⟨4003, 5, prime_4003, prime_5, by norm_num⟩
  · exact ⟨4007, 3, prime_4007, prime_3, by norm_num⟩
  · exact ⟨4007, 5, prime_4007, prime_5, by norm_num⟩
  · exact ⟨4007, 7, prime_4007, prime_7, by norm_num⟩
  · exact ⟨4013, 3, prime_4013, prime_3, by norm_num⟩
  · exact ⟨4013, 5, prime_4013, prime_5, by norm_num⟩
  · exact ⟨4013, 7, prime_4013, prime_7, by norm_num⟩
  · exact ⟨4019, 3, prime_4019, prime_3, by norm_num⟩
  · exact ⟨4021, 3, prime_4021, prime_3, by norm_num⟩
  · exact ⟨4021, 5, prime_4021, prime_5, by norm_num⟩
  · exact ⟨4021, 7, prime_4021, prime_7, by norm_num⟩
  · exact ⟨4027, 3, prime_4027, prime_3, by norm_num⟩
  · exact ⟨4027, 5, prime_4027, prime_5, by norm_num⟩
  · exact ⟨4027, 7, prime_4027, prime_7, by norm_num⟩
  · exact ⟨4019, 17, prime_4019, prime_17, by norm_num⟩
  · exact ⟨4027, 11, prime_4027, prime_11, by norm_num⟩
  · exact ⟨4027, 13, prime_4027, prime_13, by norm_num⟩
  · exact ⟨4019, 23, prime_4019, prime_23, by norm_num⟩
  · exact ⟨4027, 17, prime_4027, prime_17, by norm_num⟩
  · exact ⟨4027, 19, prime_4027, prime_19, by norm_num⟩
  · exact ⟨4019, 29, prime_4019, prime_29, by norm_num⟩
  · exact ⟨4027, 23, prime_4027, prime_23, by norm_num⟩
  · exact ⟨4049, 3, prime_4049, prime_3, by norm_num⟩
  · exact ⟨4051, 3, prime_4051, prime_3, by norm_num⟩
  · exact ⟨4051, 5, prime_4051, prime_5, by norm_num⟩
  · exact ⟨4051, 7, prime_4051, prime_7, by norm_num⟩
  · exact ⟨4057, 3, prime_4057, prime_3, by norm_num⟩
  · exact ⟨4057, 5, prime_4057, prime_5, by norm_num⟩
  · exact ⟨4057, 7, prime_4057, prime_7, by norm_num⟩
  · exact ⟨4049, 17, prime_4049, prime_17, by norm_num⟩
  · exact ⟨4057, 11, prime_4057, prime_11, by norm_num⟩
  · exact ⟨4057, 13, prime_4057, prime_13, by norm_num⟩
  · exact ⟨4049, 23, prime_4049, prime_23, by norm_num⟩
  · exact ⟨4057, 17, prime_4057, prime_17, by norm_num⟩
  · exact ⟨4073, 3, prime_4073, prime_3, by norm_num⟩
  · exact ⟨4073, 5, prime_4073, prime_5, by norm_num⟩
  · exact ⟨4073, 7, prime_4073, prime_7, by norm_num⟩
  · exact ⟨4079, 3, prime_4079, prime_3, by norm_num⟩
  · exact ⟨4079, 5, prime_4079, prime_5, by norm_num⟩
  · exact ⟨4079, 7, prime_4079, prime_7, by norm_num⟩
  · exact ⟨4057, 31, prime_4057, prime_31, by norm_num⟩
  · exact ⟨4079, 11, prime_4079, prime_11, by norm_num⟩
  · exact ⟨4079, 13, prime_4079, prime_13, by norm_num⟩
  · exact ⟨4091, 3, prime_4091, prime_3, by norm_num⟩
  · exact ⟨4093, 3, prime_4093, prime_3, by norm_num⟩
  · exact ⟨4093, 5, prime_4093, prime_5, by norm_num⟩
  · exact ⟨4093, 7, prime_4093, prime_7, by norm_num⟩
  · exact ⟨4099, 3, prime_4099, prime_3, by norm_num⟩
  · exact ⟨4099, 5, prime_4099, prime_5, by norm_num⟩
  · exact ⟨4099, 7, prime_4099, prime_7, by norm_num⟩
  · exact ⟨4091, 17, prime_4091, prime_17, by norm_num⟩
  · exact ⟨4099, 11, prime_4099, prime_11, by norm_num⟩
  · exact ⟨4099, 13, prime_4099, prime_13, by norm_num⟩
  · exact ⟨4111, 3, prime_4111, prime_3, by norm_num⟩
  · exact ⟨4111, 5, prime_4111, prime_5, by norm_num⟩
  · exact ⟨4111, 7, prime_4111, prime_7, by norm_num⟩
  · exact ⟨4091, 29, prime_4091, prime_29, by norm_num⟩
  · exact ⟨4111, 11, prime_4111, prime_11, by norm_num⟩
  · exact ⟨4111, 13, prime_4111, prime_13, by norm_num⟩
  · exact ⟨4079, 47, prime_4079, prime_47, by norm_num⟩
  · exact ⟨4111, 17, prime_4111, prime_17, by norm_num⟩
  · exact ⟨4127, 3, prime_4127, prime_3, by norm_num⟩
  · exact ⟨4129, 3, prime_4129, prime_3, by norm_num⟩
  · exact ⟨4129, 5, prime_4129, prime_5, by norm_num⟩
  · exact ⟨4133, 3, prime_4133, prime_3, by norm_num⟩
  · exact ⟨4133, 5, prime_4133, prime_5, by norm_num⟩
  · exact ⟨4133, 7, prime_4133, prime_7, by norm_num⟩
  · exact ⟨4139, 3, prime_4139, prime_3, by norm_num⟩
  · exact ⟨4139, 5, prime_4139, prime_5, by norm_num⟩
  · exact ⟨4139, 7, prime_4139, prime_7, by norm_num⟩
  · exact ⟨4129, 19, prime_4129, prime_19, by norm_num⟩
  · exact ⟨4139, 11, prime_4139, prime_11, by norm_num⟩
  · exact ⟨4139, 13, prime_4139, prime_13, by norm_num⟩
  · exact ⟨4111, 43, prime_4111, prime_43, by norm_num⟩
  · exact ⟨4153, 3, prime_4153, prime_3, by norm_num⟩
  · exact ⟨4153, 5, prime_4153, prime_5, by norm_num⟩
  · exact ⟨4157, 3, prime_4157, prime_3, by norm_num⟩
  · exact ⟨4159, 3, prime_4159, prime_3, by norm_num⟩
  · exact ⟨4159, 5, prime_4159, prime_5, by norm_num⟩
  · exact ⟨4159, 7, prime_4159, prime_7, by norm_num⟩
  · exact ⟨4157, 11, prime_4157, prime_11, by norm_num⟩
  · exact ⟨4159, 11, prime_4159, prime_11, by norm_num⟩
  · exact ⟨4159, 13, prime_4159, prime_13, by norm_num⟩
  · exact ⟨4157, 17, prime_4157, prime_17, by norm_num⟩
  · exact ⟨4159, 17, prime_4159, prime_17, by norm_num⟩
  · exact ⟨4159, 19, prime_4159, prime_19, by norm_num⟩
  · exact ⟨4177, 3, prime_4177, prime_3, by norm_num⟩
  · exact ⟨4177, 5, prime_4177, prime_5, by norm_num⟩
  · exact ⟨4177, 7, prime_4177, prime_7, by norm_num⟩
  · exact ⟨4157, 29, prime_4157, prime_29, by norm_num⟩
  · exact ⟨4177, 11, prime_4177, prime_11, by norm_num⟩
  · exact ⟨4177, 13, prime_4177, prime_13, by norm_num⟩
  · exact ⟨4139, 53, prime_4139, prime_53, by norm_num⟩
  · exact ⟨4177, 17, prime_4177, prime_17, by norm_num⟩
  · exact ⟨4177, 19, prime_4177, prime_19, by norm_num⟩
  · exact ⟨4157, 41, prime_4157, prime_41, by norm_num⟩
  · exact ⟨4177, 23, prime_4177, prime_23, by norm_num⟩
  · exact ⟨4159, 43, prime_4159, prime_43, by norm_num⟩

private theorem goldbach_chunk_21 : ∀ k : ℕ, 2102 ≤ k → k ≤ 2201 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4201, 3, prime_4201, prime_3, by norm_num⟩
  · exact ⟨4201, 5, prime_4201, prime_5, by norm_num⟩
  · exact ⟨4201, 7, prime_4201, prime_7, by norm_num⟩
  · exact ⟨4157, 53, prime_4157, prime_53, by norm_num⟩
  · exact ⟨4201, 11, prime_4201, prime_11, by norm_num⟩
  · exact ⟨4211, 3, prime_4211, prime_3, by norm_num⟩
  · exact ⟨4211, 5, prime_4211, prime_5, by norm_num⟩
  · exact ⟨4211, 7, prime_4211, prime_7, by norm_num⟩
  · exact ⟨4217, 3, prime_4217, prime_3, by norm_num⟩
  · exact ⟨4219, 3, prime_4219, prime_3, by norm_num⟩
  · exact ⟨4219, 5, prime_4219, prime_5, by norm_num⟩
  · exact ⟨4219, 7, prime_4219, prime_7, by norm_num⟩
  · exact ⟨4217, 11, prime_4217, prime_11, by norm_num⟩
  · exact ⟨4219, 11, prime_4219, prime_11, by norm_num⟩
  · exact ⟨4229, 3, prime_4229, prime_3, by norm_num⟩
  · exact ⟨4231, 3, prime_4231, prime_3, by norm_num⟩
  · exact ⟨4231, 5, prime_4231, prime_5, by norm_num⟩
  · exact ⟨4231, 7, prime_4231, prime_7, by norm_num⟩
  · exact ⟨4229, 11, prime_4229, prime_11, by norm_num⟩
  · exact ⟨4231, 11, prime_4231, prime_11, by norm_num⟩
  · exact ⟨4241, 3, prime_4241, prime_3, by norm_num⟩
  · exact ⟨4243, 3, prime_4243, prime_3, by norm_num⟩
  · exact ⟨4243, 5, prime_4243, prime_5, by norm_num⟩
  · exact ⟨4243, 7, prime_4243, prime_7, by norm_num⟩
  · exact ⟨4241, 11, prime_4241, prime_11, by norm_num⟩
  · exact ⟨4243, 11, prime_4243, prime_11, by norm_num⟩
  · exact ⟨4253, 3, prime_4253, prime_3, by norm_num⟩
  · exact ⟨4253, 5, prime_4253, prime_5, by norm_num⟩
  · exact ⟨4253, 7, prime_4253, prime_7, by norm_num⟩
  · exact ⟨4259, 3, prime_4259, prime_3, by norm_num⟩
  · exact ⟨4261, 3, prime_4261, prime_3, by norm_num⟩
  · exact ⟨4261, 5, prime_4261, prime_5, by norm_num⟩
  · exact ⟨4261, 7, prime_4261, prime_7, by norm_num⟩
  · exact ⟨4259, 11, prime_4259, prime_11, by norm_num⟩
  · exact ⟨4261, 11, prime_4261, prime_11, by norm_num⟩
  · exact ⟨4271, 3, prime_4271, prime_3, by norm_num⟩
  · exact ⟨4273, 3, prime_4273, prime_3, by norm_num⟩
  · exact ⟨4273, 5, prime_4273, prime_5, by norm_num⟩
  · exact ⟨4273, 7, prime_4273, prime_7, by norm_num⟩
  · exact ⟨4271, 11, prime_4271, prime_11, by norm_num⟩
  · exact ⟨4273, 11, prime_4273, prime_11, by norm_num⟩
  · exact ⟨4283, 3, prime_4283, prime_3, by norm_num⟩
  · exact ⟨4283, 5, prime_4283, prime_5, by norm_num⟩
  · exact ⟨4283, 7, prime_4283, prime_7, by norm_num⟩
  · exact ⟨4289, 3, prime_4289, prime_3, by norm_num⟩
  · exact ⟨4289, 5, prime_4289, prime_5, by norm_num⟩
  · exact ⟨4289, 7, prime_4289, prime_7, by norm_num⟩
  · exact ⟨4261, 37, prime_4261, prime_37, by norm_num⟩
  · exact ⟨4297, 3, prime_4297, prime_3, by norm_num⟩
  · exact ⟨4297, 5, prime_4297, prime_5, by norm_num⟩
  · exact ⟨4297, 7, prime_4297, prime_7, by norm_num⟩
  · exact ⟨4289, 17, prime_4289, prime_17, by norm_num⟩
  · exact ⟨4297, 11, prime_4297, prime_11, by norm_num⟩
  · exact ⟨4297, 13, prime_4297, prime_13, by norm_num⟩
  · exact ⟨4289, 23, prime_4289, prime_23, by norm_num⟩
  · exact ⟨4297, 17, prime_4297, prime_17, by norm_num⟩
  · exact ⟨4297, 19, prime_4297, prime_19, by norm_num⟩
  · exact ⟨4289, 29, prime_4289, prime_29, by norm_num⟩
  · exact ⟨4297, 23, prime_4297, prime_23, by norm_num⟩
  · exact ⟨4261, 61, prime_4261, prime_61, by norm_num⟩
  · exact ⟨4283, 41, prime_4283, prime_41, by norm_num⟩
  · exact ⟨4297, 29, prime_4297, prime_29, by norm_num⟩
  · exact ⟨4297, 31, prime_4297, prime_31, by norm_num⟩
  · exact ⟨4327, 3, prime_4327, prime_3, by norm_num⟩
  · exact ⟨4327, 5, prime_4327, prime_5, by norm_num⟩
  · exact ⟨4327, 7, prime_4327, prime_7, by norm_num⟩
  · exact ⟨4289, 47, prime_4289, prime_47, by norm_num⟩
  · exact ⟨4327, 11, prime_4327, prime_11, by norm_num⟩
  · exact ⟨4337, 3, prime_4337, prime_3, by norm_num⟩
  · exact ⟨4339, 3, prime_4339, prime_3, by norm_num⟩
  · exact ⟨4339, 5, prime_4339, prime_5, by norm_num⟩
  · exact ⟨4339, 7, prime_4339, prime_7, by norm_num⟩
  · exact ⟨4337, 11, prime_4337, prime_11, by norm_num⟩
  · exact ⟨4339, 11, prime_4339, prime_11, by norm_num⟩
  · exact ⟨4349, 3, prime_4349, prime_3, by norm_num⟩
  · exact ⟨4349, 5, prime_4349, prime_5, by norm_num⟩
  · exact ⟨4349, 7, prime_4349, prime_7, by norm_num⟩
  · exact ⟨4339, 19, prime_4339, prime_19, by norm_num⟩
  · exact ⟨4357, 3, prime_4357, prime_3, by norm_num⟩
  · exact ⟨4357, 5, prime_4357, prime_5, by norm_num⟩
  · exact ⟨4357, 7, prime_4357, prime_7, by norm_num⟩
  · exact ⟨4363, 3, prime_4363, prime_3, by norm_num⟩
  · exact ⟨4363, 5, prime_4363, prime_5, by norm_num⟩
  · exact ⟨4363, 7, prime_4363, prime_7, by norm_num⟩
  · exact ⟨4349, 23, prime_4349, prime_23, by norm_num⟩
  · exact ⟨4363, 11, prime_4363, prime_11, by norm_num⟩
  · exact ⟨4373, 3, prime_4373, prime_3, by norm_num⟩
  · exact ⟨4373, 5, prime_4373, prime_5, by norm_num⟩
  · exact ⟨4373, 7, prime_4373, prime_7, by norm_num⟩
  · exact ⟨4363, 19, prime_4363, prime_19, by norm_num⟩
  · exact ⟨4373, 11, prime_4373, prime_11, by norm_num⟩
  · exact ⟨4373, 13, prime_4373, prime_13, by norm_num⟩
  · exact ⟨4357, 31, prime_4357, prime_31, by norm_num⟩
  · exact ⟨4373, 17, prime_4373, prime_17, by norm_num⟩
  · exact ⟨4373, 19, prime_4373, prime_19, by norm_num⟩
  · exact ⟨4391, 3, prime_4391, prime_3, by norm_num⟩
  · exact ⟨4391, 5, prime_4391, prime_5, by norm_num⟩
  · exact ⟨4391, 7, prime_4391, prime_7, by norm_num⟩
  · exact ⟨4397, 3, prime_4397, prime_3, by norm_num⟩
  · exact ⟨4397, 5, prime_4397, prime_5, by norm_num⟩

private theorem goldbach_chunk_22 : ∀ k : ℕ, 2202 ≤ k → k ≤ 2301 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4397, 7, prime_4397, prime_7, by norm_num⟩
  · exact ⟨4363, 43, prime_4363, prime_43, by norm_num⟩
  · exact ⟨4397, 11, prime_4397, prime_11, by norm_num⟩
  · exact ⟨4397, 13, prime_4397, prime_13, by norm_num⟩
  · exact ⟨4409, 3, prime_4409, prime_3, by norm_num⟩
  · exact ⟨4409, 5, prime_4409, prime_5, by norm_num⟩
  · exact ⟨4409, 7, prime_4409, prime_7, by norm_num⟩
  · exact ⟨4357, 61, prime_4357, prime_61, by norm_num⟩
  · exact ⟨4409, 11, prime_4409, prime_11, by norm_num⟩
  · exact ⟨4409, 13, prime_4409, prime_13, by norm_num⟩
  · exact ⟨4421, 3, prime_4421, prime_3, by norm_num⟩
  · exact ⟨4423, 3, prime_4423, prime_3, by norm_num⟩
  · exact ⟨4423, 5, prime_4423, prime_5, by norm_num⟩
  · exact ⟨4423, 7, prime_4423, prime_7, by norm_num⟩
  · exact ⟨4421, 11, prime_4421, prime_11, by norm_num⟩
  · exact ⟨4423, 11, prime_4423, prime_11, by norm_num⟩
  · exact ⟨4423, 13, prime_4423, prime_13, by norm_num⟩
  · exact ⟨4421, 17, prime_4421, prime_17, by norm_num⟩
  · exact ⟨4423, 17, prime_4423, prime_17, by norm_num⟩
  · exact ⟨4423, 19, prime_4423, prime_19, by norm_num⟩
  · exact ⟨4441, 3, prime_4441, prime_3, by norm_num⟩
  · exact ⟨4441, 5, prime_4441, prime_5, by norm_num⟩
  · exact ⟨4441, 7, prime_4441, prime_7, by norm_num⟩
  · exact ⟨4447, 3, prime_4447, prime_3, by norm_num⟩
  · exact ⟨4447, 5, prime_4447, prime_5, by norm_num⟩
  · exact ⟨4451, 3, prime_4451, prime_3, by norm_num⟩
  · exact ⟨4451, 5, prime_4451, prime_5, by norm_num⟩
  · exact ⟨4451, 7, prime_4451, prime_7, by norm_num⟩
  · exact ⟨4457, 3, prime_4457, prime_3, by norm_num⟩
  · exact ⟨4457, 5, prime_4457, prime_5, by norm_num⟩
  · exact ⟨4457, 7, prime_4457, prime_7, by norm_num⟩
  · exact ⟨4463, 3, prime_4463, prime_3, by norm_num⟩
  · exact ⟨4463, 5, prime_4463, prime_5, by norm_num⟩
  · exact ⟨4463, 7, prime_4463, prime_7, by norm_num⟩
  · exact ⟨4441, 31, prime_4441, prime_31, by norm_num⟩
  · exact ⟨4463, 11, prime_4463, prime_11, by norm_num⟩
  · exact ⟨4463, 13, prime_4463, prime_13, by norm_num⟩
  · exact ⟨4447, 31, prime_4447, prime_31, by norm_num⟩
  · exact ⟨4463, 17, prime_4463, prime_17, by norm_num⟩
  · exact ⟨4463, 19, prime_4463, prime_19, by norm_num⟩
  · exact ⟨4481, 3, prime_4481, prime_3, by norm_num⟩
  · exact ⟨4483, 3, prime_4483, prime_3, by norm_num⟩
  · exact ⟨4483, 5, prime_4483, prime_5, by norm_num⟩
  · exact ⟨4483, 7, prime_4483, prime_7, by norm_num⟩
  · exact ⟨4481, 11, prime_4481, prime_11, by norm_num⟩
  · exact ⟨4483, 11, prime_4483, prime_11, by norm_num⟩
  · exact ⟨4493, 3, prime_4493, prime_3, by norm_num⟩
  · exact ⟨4493, 5, prime_4493, prime_5, by norm_num⟩
  · exact ⟨4493, 7, prime_4493, prime_7, by norm_num⟩
  · exact ⟨4483, 19, prime_4483, prime_19, by norm_num⟩
  · exact ⟨4493, 11, prime_4493, prime_11, by norm_num⟩
  · exact ⟨4493, 13, prime_4493, prime_13, by norm_num⟩
  · exact ⟨4447, 61, prime_4447, prime_61, by norm_num⟩
  · exact ⟨4507, 3, prime_4507, prime_3, by norm_num⟩
  · exact ⟨4507, 5, prime_4507, prime_5, by norm_num⟩
  · exact ⟨4507, 7, prime_4507, prime_7, by norm_num⟩
  · exact ⟨4513, 3, prime_4513, prime_3, by norm_num⟩
  · exact ⟨4513, 5, prime_4513, prime_5, by norm_num⟩
  · exact ⟨4517, 3, prime_4517, prime_3, by norm_num⟩
  · exact ⟨4519, 3, prime_4519, prime_3, by norm_num⟩
  · exact ⟨4519, 5, prime_4519, prime_5, by norm_num⟩
  · exact ⟨4523, 3, prime_4523, prime_3, by norm_num⟩
  · exact ⟨4523, 5, prime_4523, prime_5, by norm_num⟩
  · exact ⟨4523, 7, prime_4523, prime_7, by norm_num⟩
  · exact ⟨4519, 13, prime_4519, prime_13, by norm_num⟩
  · exact ⟨4523, 11, prime_4523, prime_11, by norm_num⟩
  · exact ⟨4523, 13, prime_4523, prime_13, by norm_num⟩
  · exact ⟨4519, 19, prime_4519, prime_19, by norm_num⟩
  · exact ⟨4523, 17, prime_4523, prime_17, by norm_num⟩
  · exact ⟨4523, 19, prime_4523, prime_19, by norm_num⟩
  · exact ⟨4513, 31, prime_4513, prime_31, by norm_num⟩
  · exact ⟨4523, 23, prime_4523, prime_23, by norm_num⟩
  · exact ⟨4519, 29, prime_4519, prime_29, by norm_num⟩
  · exact ⟨4547, 3, prime_4547, prime_3, by norm_num⟩
  · exact ⟨4549, 3, prime_4549, prime_3, by norm_num⟩
  · exact ⟨4549, 5, prime_4549, prime_5, by norm_num⟩
  · exact ⟨4549, 7, prime_4549, prime_7, by norm_num⟩
  · exact ⟨4547, 11, prime_4547, prime_11, by norm_num⟩
  · exact ⟨4549, 11, prime_4549, prime_11, by norm_num⟩
  · exact ⟨4549, 13, prime_4549, prime_13, by norm_num⟩
  · exact ⟨4561, 3, prime_4561, prime_3, by norm_num⟩
  · exact ⟨4561, 5, prime_4561, prime_5, by norm_num⟩
  · exact ⟨4561, 7, prime_4561, prime_7, by norm_num⟩
  · exact ⟨4567, 3, prime_4567, prime_3, by norm_num⟩
  · exact ⟨4567, 5, prime_4567, prime_5, by norm_num⟩
  · exact ⟨4567, 7, prime_4567, prime_7, by norm_num⟩
  · exact ⟨4547, 29, prime_4547, prime_29, by norm_num⟩
  · exact ⟨4567, 11, prime_4567, prime_11, by norm_num⟩
  · exact ⟨4567, 13, prime_4567, prime_13, by norm_num⟩
  · exact ⟨4523, 59, prime_4523, prime_59, by norm_num⟩
  · exact ⟨4567, 17, prime_4567, prime_17, by norm_num⟩
  · exact ⟨4583, 3, prime_4583, prime_3, by norm_num⟩
  · exact ⟨4583, 5, prime_4583, prime_5, by norm_num⟩
  · exact ⟨4583, 7, prime_4583, prime_7, by norm_num⟩
  · exact ⟨4561, 31, prime_4561, prime_31, by norm_num⟩
  · exact ⟨4591, 3, prime_4591, prime_3, by norm_num⟩
  · exact ⟨4591, 5, prime_4591, prime_5, by norm_num⟩
  · exact ⟨4591, 7, prime_4591, prime_7, by norm_num⟩
  · exact ⟨4597, 3, prime_4597, prime_3, by norm_num⟩
  · exact ⟨4597, 5, prime_4597, prime_5, by norm_num⟩

private theorem goldbach_chunk_23 : ∀ k : ℕ, 2302 ≤ k → k ≤ 2401 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4597, 7, prime_4597, prime_7, by norm_num⟩
  · exact ⟨4603, 3, prime_4603, prime_3, by norm_num⟩
  · exact ⟨4603, 5, prime_4603, prime_5, by norm_num⟩
  · exact ⟨4603, 7, prime_4603, prime_7, by norm_num⟩
  · exact ⟨4583, 29, prime_4583, prime_29, by norm_num⟩
  · exact ⟨4603, 11, prime_4603, prime_11, by norm_num⟩
  · exact ⟨4603, 13, prime_4603, prime_13, by norm_num⟩
  · exact ⟨4547, 71, prime_4547, prime_71, by norm_num⟩
  · exact ⟨4603, 17, prime_4603, prime_17, by norm_num⟩
  · exact ⟨4603, 19, prime_4603, prime_19, by norm_num⟩
  · exact ⟨4621, 3, prime_4621, prime_3, by norm_num⟩
  · exact ⟨4621, 5, prime_4621, prime_5, by norm_num⟩
  · exact ⟨4621, 7, prime_4621, prime_7, by norm_num⟩
  · exact ⟨4583, 47, prime_4583, prime_47, by norm_num⟩
  · exact ⟨4621, 11, prime_4621, prime_11, by norm_num⟩
  · exact ⟨4621, 13, prime_4621, prime_13, by norm_num⟩
  · exact ⟨4583, 53, prime_4583, prime_53, by norm_num⟩
  · exact ⟨4621, 17, prime_4621, prime_17, by norm_num⟩
  · exact ⟨4637, 3, prime_4637, prime_3, by norm_num⟩
  · exact ⟨4639, 3, prime_4639, prime_3, by norm_num⟩
  · exact ⟨4639, 5, prime_4639, prime_5, by norm_num⟩
  · exact ⟨4643, 3, prime_4643, prime_3, by norm_num⟩
  · exact ⟨4643, 5, prime_4643, prime_5, by norm_num⟩
  · exact ⟨4643, 7, prime_4643, prime_7, by norm_num⟩
  · exact ⟨4649, 3, prime_4649, prime_3, by norm_num⟩
  · exact ⟨4651, 3, prime_4651, prime_3, by norm_num⟩
  · exact ⟨4651, 5, prime_4651, prime_5, by norm_num⟩
  · exact ⟨4651, 7, prime_4651, prime_7, by norm_num⟩
  · exact ⟨4657, 3, prime_4657, prime_3, by norm_num⟩
  · exact ⟨4657, 5, prime_4657, prime_5, by norm_num⟩
  · exact ⟨4657, 7, prime_4657, prime_7, by norm_num⟩
  · exact ⟨4663, 3, prime_4663, prime_3, by norm_num⟩
  · exact ⟨4663, 5, prime_4663, prime_5, by norm_num⟩
  · exact ⟨4663, 7, prime_4663, prime_7, by norm_num⟩
  · exact ⟨4649, 23, prime_4649, prime_23, by norm_num⟩
  · exact ⟨4663, 11, prime_4663, prime_11, by norm_num⟩
  · exact ⟨4673, 3, prime_4673, prime_3, by norm_num⟩
  · exact ⟨4673, 5, prime_4673, prime_5, by norm_num⟩
  · exact ⟨4673, 7, prime_4673, prime_7, by norm_num⟩
  · exact ⟨4679, 3, prime_4679, prime_3, by norm_num⟩
  · exact ⟨4679, 5, prime_4679, prime_5, by norm_num⟩
  · exact ⟨4679, 7, prime_4679, prime_7, by norm_num⟩
  · exact ⟨4657, 31, prime_4657, prime_31, by norm_num⟩
  · exact ⟨4679, 11, prime_4679, prime_11, by norm_num⟩
  · exact ⟨4679, 13, prime_4679, prime_13, by norm_num⟩
  · exact ⟨4691, 3, prime_4691, prime_3, by norm_num⟩
  · exact ⟨4691, 5, prime_4691, prime_5, by norm_num⟩
  · exact ⟨4691, 7, prime_4691, prime_7, by norm_num⟩
  · exact ⟨4663, 37, prime_4663, prime_37, by norm_num⟩
  · exact ⟨4691, 11, prime_4691, prime_11, by norm_num⟩
  · exact ⟨4691, 13, prime_4691, prime_13, by norm_num⟩
  · exact ⟨4703, 3, prime_4703, prime_3, by norm_num⟩
  · exact ⟨4703, 5, prime_4703, prime_5, by norm_num⟩
  · exact ⟨4703, 7, prime_4703, prime_7, by norm_num⟩
  · exact ⟨4651, 61, prime_4651, prime_61, by norm_num⟩
  · exact ⟨4703, 11, prime_4703, prime_11, by norm_num⟩
  · exact ⟨4703, 13, prime_4703, prime_13, by norm_num⟩
  · exact ⟨4657, 61, prime_4657, prime_61, by norm_num⟩
  · exact ⟨4703, 17, prime_4703, prime_17, by norm_num⟩
  · exact ⟨4703, 19, prime_4703, prime_19, by norm_num⟩
  · exact ⟨4721, 3, prime_4721, prime_3, by norm_num⟩
  · exact ⟨4723, 3, prime_4723, prime_3, by norm_num⟩
  · exact ⟨4723, 5, prime_4723, prime_5, by norm_num⟩
  · exact ⟨4723, 7, prime_4723, prime_7, by norm_num⟩
  · exact ⟨4729, 3, prime_4729, prime_3, by norm_num⟩
  · exact ⟨4729, 5, prime_4729, prime_5, by norm_num⟩
  · exact ⟨4733, 3, prime_4733, prime_3, by norm_num⟩
  · exact ⟨4733, 5, prime_4733, prime_5, by norm_num⟩
  · exact ⟨4733, 7, prime_4733, prime_7, by norm_num⟩
  · exact ⟨4729, 13, prime_4729, prime_13, by norm_num⟩
  · exact ⟨4733, 11, prime_4733, prime_11, by norm_num⟩
  · exact ⟨4733, 13, prime_4733, prime_13, by norm_num⟩
  · exact ⟨4729, 19, prime_4729, prime_19, by norm_num⟩
  · exact ⟨4733, 17, prime_4733, prime_17, by norm_num⟩
  · exact ⟨4733, 19, prime_4733, prime_19, by norm_num⟩
  · exact ⟨4751, 3, prime_4751, prime_3, by norm_num⟩
  · exact ⟨4751, 5, prime_4751, prime_5, by norm_num⟩
  · exact ⟨4751, 7, prime_4751, prime_7, by norm_num⟩
  · exact ⟨4729, 31, prime_4729, prime_31, by norm_num⟩
  · exact ⟨4759, 3, prime_4759, prime_3, by norm_num⟩
  · exact ⟨4759, 5, prime_4759, prime_5, by norm_num⟩
  · exact ⟨4759, 7, prime_4759, prime_7, by norm_num⟩
  · exact ⟨4751, 17, prime_4751, prime_17, by norm_num⟩
  · exact ⟨4759, 11, prime_4759, prime_11, by norm_num⟩
  · exact ⟨4759, 13, prime_4759, prime_13, by norm_num⟩
  · exact ⟨4751, 23, prime_4751, prime_23, by norm_num⟩
  · exact ⟨4759, 17, prime_4759, prime_17, by norm_num⟩
  · exact ⟨4759, 19, prime_4759, prime_19, by norm_num⟩
  · exact ⟨4751, 29, prime_4751, prime_29, by norm_num⟩
  · exact ⟨4759, 23, prime_4759, prime_23, by norm_num⟩
  · exact ⟨4723, 61, prime_4723, prime_61, by norm_num⟩
  · exact ⟨4783, 3, prime_4783, prime_3, by norm_num⟩
  · exact ⟨4783, 5, prime_4783, prime_5, by norm_num⟩
  · exact ⟨4787, 3, prime_4787, prime_3, by norm_num⟩
  · exact ⟨4789, 3, prime_4789, prime_3, by norm_num⟩
  · exact ⟨4789, 5, prime_4789, prime_5, by norm_num⟩
  · exact ⟨4793, 3, prime_4793, prime_3, by norm_num⟩
  · exact ⟨4793, 5, prime_4793, prime_5, by norm_num⟩
  · exact ⟨4793, 7, prime_4793, prime_7, by norm_num⟩
  · exact ⟨4799, 3, prime_4799, prime_3, by norm_num⟩

private theorem goldbach_chunk_24 : ∀ k : ℕ, 2402 ≤ k → k ≤ 2501 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4801, 3, prime_4801, prime_3, by norm_num⟩
  · exact ⟨4801, 5, prime_4801, prime_5, by norm_num⟩
  · exact ⟨4801, 7, prime_4801, prime_7, by norm_num⟩
  · exact ⟨4799, 11, prime_4799, prime_11, by norm_num⟩
  · exact ⟨4801, 11, prime_4801, prime_11, by norm_num⟩
  · exact ⟨4801, 13, prime_4801, prime_13, by norm_num⟩
  · exact ⟨4813, 3, prime_4813, prime_3, by norm_num⟩
  · exact ⟨4813, 5, prime_4813, prime_5, by norm_num⟩
  · exact ⟨4817, 3, prime_4817, prime_3, by norm_num⟩
  · exact ⟨4817, 5, prime_4817, prime_5, by norm_num⟩
  · exact ⟨4817, 7, prime_4817, prime_7, by norm_num⟩
  · exact ⟨4813, 13, prime_4813, prime_13, by norm_num⟩
  · exact ⟨4817, 11, prime_4817, prime_11, by norm_num⟩
  · exact ⟨4817, 13, prime_4817, prime_13, by norm_num⟩
  · exact ⟨4813, 19, prime_4813, prime_19, by norm_num⟩
  · exact ⟨4831, 3, prime_4831, prime_3, by norm_num⟩
  · exact ⟨4831, 5, prime_4831, prime_5, by norm_num⟩
  · exact ⟨4831, 7, prime_4831, prime_7, by norm_num⟩
  · exact ⟨4817, 23, prime_4817, prime_23, by norm_num⟩
  · exact ⟨4831, 11, prime_4831, prime_11, by norm_num⟩
  · exact ⟨4831, 13, prime_4831, prime_13, by norm_num⟩
  · exact ⟨4817, 29, prime_4817, prime_29, by norm_num⟩
  · exact ⟨4831, 17, prime_4831, prime_17, by norm_num⟩
  · exact ⟨4831, 19, prime_4831, prime_19, by norm_num⟩
  · exact ⟨4799, 53, prime_4799, prime_53, by norm_num⟩
  · exact ⟨4831, 23, prime_4831, prime_23, by norm_num⟩
  · exact ⟨4813, 43, prime_4813, prime_43, by norm_num⟩
  · exact ⟨4817, 41, prime_4817, prime_41, by norm_num⟩
  · exact ⟨4831, 29, prime_4831, prime_29, by norm_num⟩
  · exact ⟨4831, 31, prime_4831, prime_31, by norm_num⟩
  · exact ⟨4861, 3, prime_4861, prime_3, by norm_num⟩
  · exact ⟨4861, 5, prime_4861, prime_5, by norm_num⟩
  · exact ⟨4861, 7, prime_4861, prime_7, by norm_num⟩
  · exact ⟨4817, 53, prime_4817, prime_53, by norm_num⟩
  · exact ⟨4861, 11, prime_4861, prime_11, by norm_num⟩
  · exact ⟨4871, 3, prime_4871, prime_3, by norm_num⟩
  · exact ⟨4871, 5, prime_4871, prime_5, by norm_num⟩
  · exact ⟨4871, 7, prime_4871, prime_7, by norm_num⟩
  · exact ⟨4877, 3, prime_4877, prime_3, by norm_num⟩
  · exact ⟨4877, 5, prime_4877, prime_5, by norm_num⟩
  · exact ⟨4877, 7, prime_4877, prime_7, by norm_num⟩
  · exact ⟨4813, 73, prime_4813, prime_73, by norm_num⟩
  · exact ⟨4877, 11, prime_4877, prime_11, by norm_num⟩
  · exact ⟨4877, 13, prime_4877, prime_13, by norm_num⟩
  · exact ⟨4889, 3, prime_4889, prime_3, by norm_num⟩
  · exact ⟨4889, 5, prime_4889, prime_5, by norm_num⟩
  · exact ⟨4889, 7, prime_4889, prime_7, by norm_num⟩
  · exact ⟨4861, 37, prime_4861, prime_37, by norm_num⟩
  · exact ⟨4889, 11, prime_4889, prime_11, by norm_num⟩
  · exact ⟨4889, 13, prime_4889, prime_13, by norm_num⟩
  · exact ⟨4861, 43, prime_4861, prime_43, by norm_num⟩
  · exact ⟨4903, 3, prime_4903, prime_3, by norm_num⟩
  · exact ⟨4903, 5, prime_4903, prime_5, by norm_num⟩
  · exact ⟨4903, 7, prime_4903, prime_7, by norm_num⟩
  · exact ⟨4909, 3, prime_4909, prime_3, by norm_num⟩
  · exact ⟨4909, 5, prime_4909, prime_5, by norm_num⟩
  · exact ⟨4909, 7, prime_4909, prime_7, by norm_num⟩
  · exact ⟨4889, 29, prime_4889, prime_29, by norm_num⟩
  · exact ⟨4909, 11, prime_4909, prime_11, by norm_num⟩
  · exact ⟨4919, 3, prime_4919, prime_3, by norm_num⟩
  · exact ⟨4919, 5, prime_4919, prime_5, by norm_num⟩
  · exact ⟨4919, 7, prime_4919, prime_7, by norm_num⟩
  · exact ⟨4909, 19, prime_4909, prime_19, by norm_num⟩
  · exact ⟨4919, 11, prime_4919, prime_11, by norm_num⟩
  · exact ⟨4919, 13, prime_4919, prime_13, by norm_num⟩
  · exact ⟨4931, 3, prime_4931, prime_3, by norm_num⟩
  · exact ⟨4933, 3, prime_4933, prime_3, by norm_num⟩
  · exact ⟨4933, 5, prime_4933, prime_5, by norm_num⟩
  · exact ⟨4937, 3, prime_4937, prime_3, by norm_num⟩
  · exact ⟨4937, 5, prime_4937, prime_5, by norm_num⟩
  · exact ⟨4937, 7, prime_4937, prime_7, by norm_num⟩
  · exact ⟨4943, 3, prime_4943, prime_3, by norm_num⟩
  · exact ⟨4943, 5, prime_4943, prime_5, by norm_num⟩
  · exact ⟨4943, 7, prime_4943, prime_7, by norm_num⟩
  · exact ⟨4933, 19, prime_4933, prime_19, by norm_num⟩
  · exact ⟨4951, 3, prime_4951, prime_3, by norm_num⟩
  · exact ⟨4951, 5, prime_4951, prime_5, by norm_num⟩
  · exact ⟨4951, 7, prime_4951, prime_7, by norm_num⟩
  · exact ⟨4957, 3, prime_4957, prime_3, by norm_num⟩
  · exact ⟨4957, 5, prime_4957, prime_5, by norm_num⟩
  · exact ⟨4957, 7, prime_4957, prime_7, by norm_num⟩
  · exact ⟨4943, 23, prime_4943, prime_23, by norm_num⟩
  · exact ⟨4957, 11, prime_4957, prime_11, by norm_num⟩
  · exact ⟨4967, 3, prime_4967, prime_3, by norm_num⟩
  · exact ⟨4969, 3, prime_4969, prime_3, by norm_num⟩
  · exact ⟨4969, 5, prime_4969, prime_5, by norm_num⟩
  · exact ⟨4973, 3, prime_4973, prime_3, by norm_num⟩
  · exact ⟨4973, 5, prime_4973, prime_5, by norm_num⟩
  · exact ⟨4973, 7, prime_4973, prime_7, by norm_num⟩
  · exact ⟨4969, 13, prime_4969, prime_13, by norm_num⟩
  · exact ⟨4973, 11, prime_4973, prime_11, by norm_num⟩
  · exact ⟨4973, 13, prime_4973, prime_13, by norm_num⟩
  · exact ⟨4969, 19, prime_4969, prime_19, by norm_num⟩
  · exact ⟨4987, 3, prime_4987, prime_3, by norm_num⟩
  · exact ⟨4987, 5, prime_4987, prime_5, by norm_num⟩
  · exact ⟨4987, 7, prime_4987, prime_7, by norm_num⟩
  · exact ⟨4993, 3, prime_4993, prime_3, by norm_num⟩
  · exact ⟨4993, 5, prime_4993, prime_5, by norm_num⟩
  · exact ⟨4993, 7, prime_4993, prime_7, by norm_num⟩
  · exact ⟨4999, 3, prime_4999, prime_3, by norm_num⟩

private theorem goldbach_chunk_25 : ∀ k : ℕ, 2502 ≤ k → k ≤ 2601 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4999, 5, prime_4999, prime_5, by norm_num⟩
  · exact ⟨5003, 3, prime_5003, prime_3, by norm_num⟩
  · exact ⟨5003, 5, prime_5003, prime_5, by norm_num⟩
  · exact ⟨5003, 7, prime_5003, prime_7, by norm_num⟩
  · exact ⟨5009, 3, prime_5009, prime_3, by norm_num⟩
  · exact ⟨5011, 3, prime_5011, prime_3, by norm_num⟩
  · exact ⟨5011, 5, prime_5011, prime_5, by norm_num⟩
  · exact ⟨5011, 7, prime_5011, prime_7, by norm_num⟩
  · exact ⟨5009, 11, prime_5009, prime_11, by norm_num⟩
  · exact ⟨5011, 11, prime_5011, prime_11, by norm_num⟩
  · exact ⟨5021, 3, prime_5021, prime_3, by norm_num⟩
  · exact ⟨5023, 3, prime_5023, prime_3, by norm_num⟩
  · exact ⟨5023, 5, prime_5023, prime_5, by norm_num⟩
  · exact ⟨5023, 7, prime_5023, prime_7, by norm_num⟩
  · exact ⟨5021, 11, prime_5021, prime_11, by norm_num⟩
  · exact ⟨5023, 11, prime_5023, prime_11, by norm_num⟩
  · exact ⟨5023, 13, prime_5023, prime_13, by norm_num⟩
  · exact ⟨5021, 17, prime_5021, prime_17, by norm_num⟩
  · exact ⟨5023, 17, prime_5023, prime_17, by norm_num⟩
  · exact ⟨5039, 3, prime_5039, prime_3, by norm_num⟩
  · exact ⟨5039, 5, prime_5039, prime_5, by norm_num⟩
  · exact ⟨5039, 7, prime_5039, prime_7, by norm_num⟩
  · exact ⟨5011, 37, prime_5011, prime_37, by norm_num⟩
  · exact ⟨5039, 11, prime_5039, prime_11, by norm_num⟩
  · exact ⟨5039, 13, prime_5039, prime_13, by norm_num⟩
  · exact ⟨5051, 3, prime_5051, prime_3, by norm_num⟩
  · exact ⟨5051, 5, prime_5051, prime_5, by norm_num⟩
  · exact ⟨5051, 7, prime_5051, prime_7, by norm_num⟩
  · exact ⟨5023, 37, prime_5023, prime_37, by norm_num⟩
  · exact ⟨5059, 3, prime_5059, prime_3, by norm_num⟩
  · exact ⟨5059, 5, prime_5059, prime_5, by norm_num⟩
  · exact ⟨5059, 7, prime_5059, prime_7, by norm_num⟩
  · exact ⟨5051, 17, prime_5051, prime_17, by norm_num⟩
  · exact ⟨5059, 11, prime_5059, prime_11, by norm_num⟩
  · exact ⟨5059, 13, prime_5059, prime_13, by norm_num⟩
  · exact ⟨5051, 23, prime_5051, prime_23, by norm_num⟩
  · exact ⟨5059, 17, prime_5059, prime_17, by norm_num⟩
  · exact ⟨5059, 19, prime_5059, prime_19, by norm_num⟩
  · exact ⟨5077, 3, prime_5077, prime_3, by norm_num⟩
  · exact ⟨5077, 5, prime_5077, prime_5, by norm_num⟩
  · exact ⟨5081, 3, prime_5081, prime_3, by norm_num⟩
  · exact ⟨5081, 5, prime_5081, prime_5, by norm_num⟩
  · exact ⟨5081, 7, prime_5081, prime_7, by norm_num⟩
  · exact ⟨5087, 3, prime_5087, prime_3, by norm_num⟩
  · exact ⟨5087, 5, prime_5087, prime_5, by norm_num⟩
  · exact ⟨5087, 7, prime_5087, prime_7, by norm_num⟩
  · exact ⟨5077, 19, prime_5077, prime_19, by norm_num⟩
  · exact ⟨5087, 11, prime_5087, prime_11, by norm_num⟩
  · exact ⟨5087, 13, prime_5087, prime_13, by norm_num⟩
  · exact ⟨5099, 3, prime_5099, prime_3, by norm_num⟩
  · exact ⟨5101, 3, prime_5101, prime_3, by norm_num⟩
  · exact ⟨5101, 5, prime_5101, prime_5, by norm_num⟩
  · exact ⟨5101, 7, prime_5101, prime_7, by norm_num⟩
  · exact ⟨5107, 3, prime_5107, prime_3, by norm_num⟩
  · exact ⟨5107, 5, prime_5107, prime_5, by norm_num⟩
  · exact ⟨5107, 7, prime_5107, prime_7, by norm_num⟩
  · exact ⟨5113, 3, prime_5113, prime_3, by norm_num⟩
  · exact ⟨5113, 5, prime_5113, prime_5, by norm_num⟩
  · exact ⟨5113, 7, prime_5113, prime_7, by norm_num⟩
  · exact ⟨5119, 3, prime_5119, prime_3, by norm_num⟩
  · exact ⟨5119, 5, prime_5119, prime_5, by norm_num⟩
  · exact ⟨5119, 7, prime_5119, prime_7, by norm_num⟩
  · exact ⟨5099, 29, prime_5099, prime_29, by norm_num⟩
  · exact ⟨5119, 11, prime_5119, prime_11, by norm_num⟩
  · exact ⟨5119, 13, prime_5119, prime_13, by norm_num⟩
  · exact ⟨5087, 47, prime_5087, prime_47, by norm_num⟩
  · exact ⟨5119, 17, prime_5119, prime_17, by norm_num⟩
  · exact ⟨5119, 19, prime_5119, prime_19, by norm_num⟩
  · exact ⟨5099, 41, prime_5099, prime_41, by norm_num⟩
  · exact ⟨5119, 23, prime_5119, prime_23, by norm_num⟩
  · exact ⟨5113, 31, prime_5113, prime_31, by norm_num⟩
  · exact ⟨5099, 47, prime_5099, prime_47, by norm_num⟩
  · exact ⟨5119, 29, prime_5119, prime_29, by norm_num⟩
  · exact ⟨5147, 3, prime_5147, prime_3, by norm_num⟩
  · exact ⟨5147, 5, prime_5147, prime_5, by norm_num⟩
  · exact ⟨5147, 7, prime_5147, prime_7, by norm_num⟩
  · exact ⟨5153, 3, prime_5153, prime_3, by norm_num⟩
  · exact ⟨5153, 5, prime_5153, prime_5, by norm_num⟩
  · exact ⟨5153, 7, prime_5153, prime_7, by norm_num⟩
  · exact ⟨5119, 43, prime_5119, prime_43, by norm_num⟩
  · exact ⟨5153, 11, prime_5153, prime_11, by norm_num⟩
  · exact ⟨5153, 13, prime_5153, prime_13, by norm_num⟩
  · exact ⟨5107, 61, prime_5107, prime_61, by norm_num⟩
  · exact ⟨5167, 3, prime_5167, prime_3, by norm_num⟩
  · exact ⟨5167, 5, prime_5167, prime_5, by norm_num⟩
  · exact ⟨5171, 3, prime_5171, prime_3, by norm_num⟩
  · exact ⟨5171, 5, prime_5171, prime_5, by norm_num⟩
  · exact ⟨5171, 7, prime_5171, prime_7, by norm_num⟩
  · exact ⟨5167, 13, prime_5167, prime_13, by norm_num⟩
  · exact ⟨5179, 3, prime_5179, prime_3, by norm_num⟩
  · exact ⟨5179, 5, prime_5179, prime_5, by norm_num⟩
  · exact ⟨5179, 7, prime_5179, prime_7, by norm_num⟩
  · exact ⟨5171, 17, prime_5171, prime_17, by norm_num⟩
  · exact ⟨5179, 11, prime_5179, prime_11, by norm_num⟩
  · exact ⟨5189, 3, prime_5189, prime_3, by norm_num⟩
  · exact ⟨5189, 5, prime_5189, prime_5, by norm_num⟩
  · exact ⟨5189, 7, prime_5189, prime_7, by norm_num⟩
  · exact ⟨5179, 19, prime_5179, prime_19, by norm_num⟩
  · exact ⟨5197, 3, prime_5197, prime_3, by norm_num⟩
  · exact ⟨5197, 5, prime_5197, prime_5, by norm_num⟩

private theorem goldbach_chunk_26 : ∀ k : ℕ, 2602 ≤ k → k ≤ 2701 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5197, 7, prime_5197, prime_7, by norm_num⟩
  · exact ⟨5189, 17, prime_5189, prime_17, by norm_num⟩
  · exact ⟨5197, 11, prime_5197, prime_11, by norm_num⟩
  · exact ⟨5197, 13, prime_5197, prime_13, by norm_num⟩
  · exact ⟨5209, 3, prime_5209, prime_3, by norm_num⟩
  · exact ⟨5209, 5, prime_5209, prime_5, by norm_num⟩
  · exact ⟨5209, 7, prime_5209, prime_7, by norm_num⟩
  · exact ⟨5189, 29, prime_5189, prime_29, by norm_num⟩
  · exact ⟨5209, 11, prime_5209, prime_11, by norm_num⟩
  · exact ⟨5209, 13, prime_5209, prime_13, by norm_num⟩
  · exact ⟨5171, 53, prime_5171, prime_53, by norm_num⟩
  · exact ⟨5209, 17, prime_5209, prime_17, by norm_num⟩
  · exact ⟨5209, 19, prime_5209, prime_19, by norm_num⟩
  · exact ⟨5227, 3, prime_5227, prime_3, by norm_num⟩
  · exact ⟨5227, 5, prime_5227, prime_5, by norm_num⟩
  · exact ⟨5231, 3, prime_5231, prime_3, by norm_num⟩
  · exact ⟨5233, 3, prime_5233, prime_3, by norm_num⟩
  · exact ⟨5233, 5, prime_5233, prime_5, by norm_num⟩
  · exact ⟨5237, 3, prime_5237, prime_3, by norm_num⟩
  · exact ⟨5237, 5, prime_5237, prime_5, by norm_num⟩
  · exact ⟨5237, 7, prime_5237, prime_7, by norm_num⟩
  · exact ⟨5233, 13, prime_5233, prime_13, by norm_num⟩
  · exact ⟨5237, 11, prime_5237, prime_11, by norm_num⟩
  · exact ⟨5237, 13, prime_5237, prime_13, by norm_num⟩
  · exact ⟨5233, 19, prime_5233, prime_19, by norm_num⟩
  · exact ⟨5237, 17, prime_5237, prime_17, by norm_num⟩
  · exact ⟨5237, 19, prime_5237, prime_19, by norm_num⟩
  · exact ⟨5227, 31, prime_5227, prime_31, by norm_num⟩
  · exact ⟨5237, 23, prime_5237, prime_23, by norm_num⟩
  · exact ⟨5233, 29, prime_5233, prime_29, by norm_num⟩
  · exact ⟨5261, 3, prime_5261, prime_3, by norm_num⟩
  · exact ⟨5261, 5, prime_5261, prime_5, by norm_num⟩
  · exact ⟨5261, 7, prime_5261, prime_7, by norm_num⟩
  · exact ⟨5233, 37, prime_5233, prime_37, by norm_num⟩
  · exact ⟨5261, 11, prime_5261, prime_11, by norm_num⟩
  · exact ⟨5261, 13, prime_5261, prime_13, by norm_num⟩
  · exact ⟨5273, 3, prime_5273, prime_3, by norm_num⟩
  · exact ⟨5273, 5, prime_5273, prime_5, by norm_num⟩
  · exact ⟨5273, 7, prime_5273, prime_7, by norm_num⟩
  · exact ⟨5279, 3, prime_5279, prime_3, by norm_num⟩
  · exact ⟨5281, 3, prime_5281, prime_3, by norm_num⟩
  · exact ⟨5281, 5, prime_5281, prime_5, by norm_num⟩
  · exact ⟨5281, 7, prime_5281, prime_7, by norm_num⟩
  · exact ⟨5279, 11, prime_5279, prime_11, by norm_num⟩
  · exact ⟨5281, 11, prime_5281, prime_11, by norm_num⟩
  · exact ⟨5281, 13, prime_5281, prime_13, by norm_num⟩
  · exact ⟨5279, 17, prime_5279, prime_17, by norm_num⟩
  · exact ⟨5281, 17, prime_5281, prime_17, by norm_num⟩
  · exact ⟨5297, 3, prime_5297, prime_3, by norm_num⟩
  · exact ⟨5297, 5, prime_5297, prime_5, by norm_num⟩
  · exact ⟨5297, 7, prime_5297, prime_7, by norm_num⟩
  · exact ⟨5303, 3, prime_5303, prime_3, by norm_num⟩
  · exact ⟨5303, 5, prime_5303, prime_5, by norm_num⟩
  · exact ⟨5303, 7, prime_5303, prime_7, by norm_num⟩
  · exact ⟨5309, 3, prime_5309, prime_3, by norm_num⟩
  · exact ⟨5309, 5, prime_5309, prime_5, by norm_num⟩
  · exact ⟨5309, 7, prime_5309, prime_7, by norm_num⟩
  · exact ⟨5281, 37, prime_5281, prime_37, by norm_num⟩
  · exact ⟨5309, 11, prime_5309, prime_11, by norm_num⟩
  · exact ⟨5309, 13, prime_5309, prime_13, by norm_num⟩
  · exact ⟨5281, 43, prime_5281, prime_43, by norm_num⟩
  · exact ⟨5323, 3, prime_5323, prime_3, by norm_num⟩
  · exact ⟨5323, 5, prime_5323, prime_5, by norm_num⟩
  · exact ⟨5323, 7, prime_5323, prime_7, by norm_num⟩
  · exact ⟨5309, 23, prime_5309, prime_23, by norm_num⟩
  · exact ⟨5323, 11, prime_5323, prime_11, by norm_num⟩
  · exact ⟨5333, 3, prime_5333, prime_3, by norm_num⟩
  · exact ⟨5333, 5, prime_5333, prime_5, by norm_num⟩
  · exact ⟨5333, 7, prime_5333, prime_7, by norm_num⟩
  · exact ⟨5323, 19, prime_5323, prime_19, by norm_num⟩
  · exact ⟨5333, 11, prime_5333, prime_11, by norm_num⟩
  · exact ⟨5333, 13, prime_5333, prime_13, by norm_num⟩
  · exact ⟨5281, 67, prime_5281, prime_67, by norm_num⟩
  · exact ⟨5347, 3, prime_5347, prime_3, by norm_num⟩
  · exact ⟨5347, 5, prime_5347, prime_5, by norm_num⟩
  · exact ⟨5351, 3, prime_5351, prime_3, by norm_num⟩
  · exact ⟨5351, 5, prime_5351, prime_5, by norm_num⟩
  · exact ⟨5351, 7, prime_5351, prime_7, by norm_num⟩
  · exact ⟨5347, 13, prime_5347, prime_13, by norm_num⟩
  · exact ⟨5351, 11, prime_5351, prime_11, by norm_num⟩
  · exact ⟨5351, 13, prime_5351, prime_13, by norm_num⟩
  · exact ⟨5347, 19, prime_5347, prime_19, by norm_num⟩
  · exact ⟨5351, 17, prime_5351, prime_17, by norm_num⟩
  · exact ⟨5351, 19, prime_5351, prime_19, by norm_num⟩
  · exact ⟨5233, 139, prime_5233, prime_139, by norm_num⟩
  · exact ⟨5351, 23, prime_5351, prime_23, by norm_num⟩
  · exact ⟨5347, 29, prime_5347, prime_29, by norm_num⟩
  · exact ⟨5347, 31, prime_5347, prime_31, by norm_num⟩
  · exact ⟨5351, 29, prime_5351, prime_29, by norm_num⟩
  · exact ⟨5351, 31, prime_5351, prime_31, by norm_num⟩
  · exact ⟨5381, 3, prime_5381, prime_3, by norm_num⟩
  · exact ⟨5381, 5, prime_5381, prime_5, by norm_num⟩
  · exact ⟨5381, 7, prime_5381, prime_7, by norm_num⟩
  · exact ⟨5387, 3, prime_5387, prime_3, by norm_num⟩
  · exact ⟨5387, 5, prime_5387, prime_5, by norm_num⟩
  · exact ⟨5387, 7, prime_5387, prime_7, by norm_num⟩
  · exact ⟨5393, 3, prime_5393, prime_3, by norm_num⟩
  · exact ⟨5393, 5, prime_5393, prime_5, by norm_num⟩
  · exact ⟨5393, 7, prime_5393, prime_7, by norm_num⟩
  · exact ⟨5399, 3, prime_5399, prime_3, by norm_num⟩

private theorem goldbach_chunk_27 : ∀ k : ℕ, 2702 ≤ k → k ≤ 2801 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5399, 5, prime_5399, prime_5, by norm_num⟩
  · exact ⟨5399, 7, prime_5399, prime_7, by norm_num⟩
  · exact ⟨5347, 61, prime_5347, prime_61, by norm_num⟩
  · exact ⟨5407, 3, prime_5407, prime_3, by norm_num⟩
  · exact ⟨5407, 5, prime_5407, prime_5, by norm_num⟩
  · exact ⟨5407, 7, prime_5407, prime_7, by norm_num⟩
  · exact ⟨5413, 3, prime_5413, prime_3, by norm_num⟩
  · exact ⟨5413, 5, prime_5413, prime_5, by norm_num⟩
  · exact ⟨5417, 3, prime_5417, prime_3, by norm_num⟩
  · exact ⟨5419, 3, prime_5419, prime_3, by norm_num⟩
  · exact ⟨5419, 5, prime_5419, prime_5, by norm_num⟩
  · exact ⟨5419, 7, prime_5419, prime_7, by norm_num⟩
  · exact ⟨5417, 11, prime_5417, prime_11, by norm_num⟩
  · exact ⟨5419, 11, prime_5419, prime_11, by norm_num⟩
  · exact ⟨5419, 13, prime_5419, prime_13, by norm_num⟩
  · exact ⟨5431, 3, prime_5431, prime_3, by norm_num⟩
  · exact ⟨5431, 5, prime_5431, prime_5, by norm_num⟩
  · exact ⟨5431, 7, prime_5431, prime_7, by norm_num⟩
  · exact ⟨5437, 3, prime_5437, prime_3, by norm_num⟩
  · exact ⟨5437, 5, prime_5437, prime_5, by norm_num⟩
  · exact ⟨5441, 3, prime_5441, prime_3, by norm_num⟩
  · exact ⟨5443, 3, prime_5443, prime_3, by norm_num⟩
  · exact ⟨5443, 5, prime_5443, prime_5, by norm_num⟩
  · exact ⟨5443, 7, prime_5443, prime_7, by norm_num⟩
  · exact ⟨5449, 3, prime_5449, prime_3, by norm_num⟩
  · exact ⟨5449, 5, prime_5449, prime_5, by norm_num⟩
  · exact ⟨5449, 7, prime_5449, prime_7, by norm_num⟩
  · exact ⟨5441, 17, prime_5441, prime_17, by norm_num⟩
  · exact ⟨5449, 11, prime_5449, prime_11, by norm_num⟩
  · exact ⟨5449, 13, prime_5449, prime_13, by norm_num⟩
  · exact ⟨5441, 23, prime_5441, prime_23, by norm_num⟩
  · exact ⟨5449, 17, prime_5449, prime_17, by norm_num⟩
  · exact ⟨5449, 19, prime_5449, prime_19, by norm_num⟩
  · exact ⟨5441, 29, prime_5441, prime_29, by norm_num⟩
  · exact ⟨5449, 23, prime_5449, prime_23, by norm_num⟩
  · exact ⟨5471, 3, prime_5471, prime_3, by norm_num⟩
  · exact ⟨5471, 5, prime_5471, prime_5, by norm_num⟩
  · exact ⟨5471, 7, prime_5471, prime_7, by norm_num⟩
  · exact ⟨5477, 3, prime_5477, prime_3, by norm_num⟩
  · exact ⟨5479, 3, prime_5479, prime_3, by norm_num⟩
  · exact ⟨5479, 5, prime_5479, prime_5, by norm_num⟩
  · exact ⟨5483, 3, prime_5483, prime_3, by norm_num⟩
  · exact ⟨5483, 5, prime_5483, prime_5, by norm_num⟩
  · exact ⟨5483, 7, prime_5483, prime_7, by norm_num⟩
  · exact ⟨5479, 13, prime_5479, prime_13, by norm_num⟩
  · exact ⟨5483, 11, prime_5483, prime_11, by norm_num⟩
  · exact ⟨5483, 13, prime_5483, prime_13, by norm_num⟩
  · exact ⟨5479, 19, prime_5479, prime_19, by norm_num⟩
  · exact ⟨5483, 17, prime_5483, prime_17, by norm_num⟩
  · exact ⟨5483, 19, prime_5483, prime_19, by norm_num⟩
  · exact ⟨5501, 3, prime_5501, prime_3, by norm_num⟩
  · exact ⟨5503, 3, prime_5503, prime_3, by norm_num⟩
  · exact ⟨5503, 5, prime_5503, prime_5, by norm_num⟩
  · exact ⟨5507, 3, prime_5507, prime_3, by norm_num⟩
  · exact ⟨5507, 5, prime_5507, prime_5, by norm_num⟩
  · exact ⟨5507, 7, prime_5507, prime_7, by norm_num⟩
  · exact ⟨5503, 13, prime_5503, prime_13, by norm_num⟩
  · exact ⟨5507, 11, prime_5507, prime_11, by norm_num⟩
  · exact ⟨5507, 13, prime_5507, prime_13, by norm_num⟩
  · exact ⟨5519, 3, prime_5519, prime_3, by norm_num⟩
  · exact ⟨5521, 3, prime_5521, prime_3, by norm_num⟩
  · exact ⟨5521, 5, prime_5521, prime_5, by norm_num⟩
  · exact ⟨5521, 7, prime_5521, prime_7, by norm_num⟩
  · exact ⟨5527, 3, prime_5527, prime_3, by norm_num⟩
  · exact ⟨5527, 5, prime_5527, prime_5, by norm_num⟩
  · exact ⟨5531, 3, prime_5531, prime_3, by norm_num⟩
  · exact ⟨5531, 5, prime_5531, prime_5, by norm_num⟩
  · exact ⟨5531, 7, prime_5531, prime_7, by norm_num⟩
  · exact ⟨5527, 13, prime_5527, prime_13, by norm_num⟩
  · exact ⟨5531, 11, prime_5531, prime_11, by norm_num⟩
  · exact ⟨5531, 13, prime_5531, prime_13, by norm_num⟩
  · exact ⟨5527, 19, prime_5527, prime_19, by norm_num⟩
  · exact ⟨5531, 17, prime_5531, prime_17, by norm_num⟩
  · exact ⟨5531, 19, prime_5531, prime_19, by norm_num⟩
  · exact ⟨5521, 31, prime_5521, prime_31, by norm_num⟩
  · exact ⟨5531, 23, prime_5531, prime_23, by norm_num⟩
  · exact ⟨5527, 29, prime_5527, prime_29, by norm_num⟩
  · exact ⟨5527, 31, prime_5527, prime_31, by norm_num⟩
  · exact ⟨5557, 3, prime_5557, prime_3, by norm_num⟩
  · exact ⟨5557, 5, prime_5557, prime_5, by norm_num⟩
  · exact ⟨5557, 7, prime_5557, prime_7, by norm_num⟩
  · exact ⟨5563, 3, prime_5563, prime_3, by norm_num⟩
  · exact ⟨5563, 5, prime_5563, prime_5, by norm_num⟩
  · exact ⟨5563, 7, prime_5563, prime_7, by norm_num⟩
  · exact ⟨5569, 3, prime_5569, prime_3, by norm_num⟩
  · exact ⟨5569, 5, prime_5569, prime_5, by norm_num⟩
  · exact ⟨5573, 3, prime_5573, prime_3, by norm_num⟩
  · exact ⟨5573, 5, prime_5573, prime_5, by norm_num⟩
  · exact ⟨5573, 7, prime_5573, prime_7, by norm_num⟩
  · exact ⟨5569, 13, prime_5569, prime_13, by norm_num⟩
  · exact ⟨5581, 3, prime_5581, prime_3, by norm_num⟩
  · exact ⟨5581, 5, prime_5581, prime_5, by norm_num⟩
  · exact ⟨5581, 7, prime_5581, prime_7, by norm_num⟩
  · exact ⟨5573, 17, prime_5573, prime_17, by norm_num⟩
  · exact ⟨5581, 11, prime_5581, prime_11, by norm_num⟩
  · exact ⟨5591, 3, prime_5591, prime_3, by norm_num⟩
  · exact ⟨5591, 5, prime_5591, prime_5, by norm_num⟩
  · exact ⟨5591, 7, prime_5591, prime_7, by norm_num⟩
  · exact ⟨5581, 19, prime_5581, prime_19, by norm_num⟩
  · exact ⟨5591, 11, prime_5591, prime_11, by norm_num⟩

private theorem goldbach_chunk_28 : ∀ k : ℕ, 2802 ≤ k → k ≤ 2901 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5591, 13, prime_5591, prime_13, by norm_num⟩
  · exact ⟨5569, 37, prime_5569, prime_37, by norm_num⟩
  · exact ⟨5591, 17, prime_5591, prime_17, by norm_num⟩
  · exact ⟨5591, 19, prime_5591, prime_19, by norm_num⟩
  · exact ⟨5581, 31, prime_5581, prime_31, by norm_num⟩
  · exact ⟨5591, 23, prime_5591, prime_23, by norm_num⟩
  · exact ⟨5573, 43, prime_5573, prime_43, by norm_num⟩
  · exact ⟨5581, 37, prime_5581, prime_37, by norm_num⟩
  · exact ⟨5591, 29, prime_5591, prime_29, by norm_num⟩
  · exact ⟨5591, 31, prime_5591, prime_31, by norm_num⟩
  · exact ⟨5581, 43, prime_5581, prime_43, by norm_num⟩
  · exact ⟨5623, 3, prime_5623, prime_3, by norm_num⟩
  · exact ⟨5623, 5, prime_5623, prime_5, by norm_num⟩
  · exact ⟨5623, 7, prime_5623, prime_7, by norm_num⟩
  · exact ⟨5591, 41, prime_5591, prime_41, by norm_num⟩
  · exact ⟨5623, 11, prime_5623, prime_11, by norm_num⟩
  · exact ⟨5623, 13, prime_5623, prime_13, by norm_num⟩
  · exact ⟨5591, 47, prime_5591, prime_47, by norm_num⟩
  · exact ⟨5623, 17, prime_5623, prime_17, by norm_num⟩
  · exact ⟨5639, 3, prime_5639, prime_3, by norm_num⟩
  · exact ⟨5641, 3, prime_5641, prime_3, by norm_num⟩
  · exact ⟨5641, 5, prime_5641, prime_5, by norm_num⟩
  · exact ⟨5641, 7, prime_5641, prime_7, by norm_num⟩
  · exact ⟨5647, 3, prime_5647, prime_3, by norm_num⟩
  · exact ⟨5647, 5, prime_5647, prime_5, by norm_num⟩
  · exact ⟨5651, 3, prime_5651, prime_3, by norm_num⟩
  · exact ⟨5653, 3, prime_5653, prime_3, by norm_num⟩
  · exact ⟨5653, 5, prime_5653, prime_5, by norm_num⟩
  · exact ⟨5657, 3, prime_5657, prime_3, by norm_num⟩
  · exact ⟨5659, 3, prime_5659, prime_3, by norm_num⟩
  · exact ⟨5659, 5, prime_5659, prime_5, by norm_num⟩
  · exact ⟨5659, 7, prime_5659, prime_7, by norm_num⟩
  · exact ⟨5657, 11, prime_5657, prime_11, by norm_num⟩
  · exact ⟨5659, 11, prime_5659, prime_11, by norm_num⟩
  · exact ⟨5669, 3, prime_5669, prime_3, by norm_num⟩
  · exact ⟨5669, 5, prime_5669, prime_5, by norm_num⟩
  · exact ⟨5669, 7, prime_5669, prime_7, by norm_num⟩
  · exact ⟨5659, 19, prime_5659, prime_19, by norm_num⟩
  · exact ⟨5669, 11, prime_5669, prime_11, by norm_num⟩
  · exact ⟨5669, 13, prime_5669, prime_13, by norm_num⟩
  · exact ⟨5653, 31, prime_5653, prime_31, by norm_num⟩
  · exact ⟨5683, 3, prime_5683, prime_3, by norm_num⟩
  · exact ⟨5683, 5, prime_5683, prime_5, by norm_num⟩
  · exact ⟨5683, 7, prime_5683, prime_7, by norm_num⟩
  · exact ⟨5689, 3, prime_5689, prime_3, by norm_num⟩
  · exact ⟨5689, 5, prime_5689, prime_5, by norm_num⟩
  · exact ⟨5693, 3, prime_5693, prime_3, by norm_num⟩
  · exact ⟨5693, 5, prime_5693, prime_5, by norm_num⟩
  · exact ⟨5693, 7, prime_5693, prime_7, by norm_num⟩
  · exact ⟨5689, 13, prime_5689, prime_13, by norm_num⟩
  · exact ⟨5701, 3, prime_5701, prime_3, by norm_num⟩
  · exact ⟨5701, 5, prime_5701, prime_5, by norm_num⟩
  · exact ⟨5701, 7, prime_5701, prime_7, by norm_num⟩
  · exact ⟨5693, 17, prime_5693, prime_17, by norm_num⟩
  · exact ⟨5701, 11, prime_5701, prime_11, by norm_num⟩
  · exact ⟨5711, 3, prime_5711, prime_3, by norm_num⟩
  · exact ⟨5711, 5, prime_5711, prime_5, by norm_num⟩
  · exact ⟨5711, 7, prime_5711, prime_7, by norm_num⟩
  · exact ⟨5717, 3, prime_5717, prime_3, by norm_num⟩
  · exact ⟨5717, 5, prime_5717, prime_5, by norm_num⟩
  · exact ⟨5717, 7, prime_5717, prime_7, by norm_num⟩
  · exact ⟨5689, 37, prime_5689, prime_37, by norm_num⟩
  · exact ⟨5717, 11, prime_5717, prime_11, by norm_num⟩
  · exact ⟨5717, 13, prime_5717, prime_13, by norm_num⟩
  · exact ⟨5701, 31, prime_5701, prime_31, by norm_num⟩
  · exact ⟨5717, 17, prime_5717, prime_17, by norm_num⟩
  · exact ⟨5717, 19, prime_5717, prime_19, by norm_num⟩
  · exact ⟨5701, 37, prime_5701, prime_37, by norm_num⟩
  · exact ⟨5737, 3, prime_5737, prime_3, by norm_num⟩
  · exact ⟨5737, 5, prime_5737, prime_5, by norm_num⟩
  · exact ⟨5741, 3, prime_5741, prime_3, by norm_num⟩
  · exact ⟨5743, 3, prime_5743, prime_3, by norm_num⟩
  · exact ⟨5743, 5, prime_5743, prime_5, by norm_num⟩
  · exact ⟨5743, 7, prime_5743, prime_7, by norm_num⟩
  · exact ⟨5749, 3, prime_5749, prime_3, by norm_num⟩
  · exact ⟨5749, 5, prime_5749, prime_5, by norm_num⟩
  · exact ⟨5749, 7, prime_5749, prime_7, by norm_num⟩
  · exact ⟨5741, 17, prime_5741, prime_17, by norm_num⟩
  · exact ⟨5749, 11, prime_5749, prime_11, by norm_num⟩
  · exact ⟨5749, 13, prime_5749, prime_13, by norm_num⟩
  · exact ⟨5741, 23, prime_5741, prime_23, by norm_num⟩
  · exact ⟨5749, 17, prime_5749, prime_17, by norm_num⟩
  · exact ⟨5749, 19, prime_5749, prime_19, by norm_num⟩
  · exact ⟨5741, 29, prime_5741, prime_29, by norm_num⟩
  · exact ⟨5749, 23, prime_5749, prime_23, by norm_num⟩
  · exact ⟨5743, 31, prime_5743, prime_31, by norm_num⟩
  · exact ⟨5717, 59, prime_5717, prime_59, by norm_num⟩
  · exact ⟨5749, 29, prime_5749, prime_29, by norm_num⟩
  · exact ⟨5749, 31, prime_5749, prime_31, by norm_num⟩
  · exact ⟨5779, 3, prime_5779, prime_3, by norm_num⟩
  · exact ⟨5779, 5, prime_5779, prime_5, by norm_num⟩
  · exact ⟨5783, 3, prime_5783, prime_3, by norm_num⟩
  · exact ⟨5783, 5, prime_5783, prime_5, by norm_num⟩
  · exact ⟨5783, 7, prime_5783, prime_7, by norm_num⟩
  · exact ⟨5779, 13, prime_5779, prime_13, by norm_num⟩
  · exact ⟨5791, 3, prime_5791, prime_3, by norm_num⟩
  · exact ⟨5791, 5, prime_5791, prime_5, by norm_num⟩
  · exact ⟨5791, 7, prime_5791, prime_7, by norm_num⟩
  · exact ⟨5783, 17, prime_5783, prime_17, by norm_num⟩
  · exact ⟨5791, 11, prime_5791, prime_11, by norm_num⟩

private theorem goldbach_chunk_29 : ∀ k : ℕ, 2902 ≤ k → k ≤ 3001 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5801, 3, prime_5801, prime_3, by norm_num⟩
  · exact ⟨5801, 5, prime_5801, prime_5, by norm_num⟩
  · exact ⟨5801, 7, prime_5801, prime_7, by norm_num⟩
  · exact ⟨5807, 3, prime_5807, prime_3, by norm_num⟩
  · exact ⟨5807, 5, prime_5807, prime_5, by norm_num⟩
  · exact ⟨5807, 7, prime_5807, prime_7, by norm_num⟩
  · exact ⟨5813, 3, prime_5813, prime_3, by norm_num⟩
  · exact ⟨5813, 5, prime_5813, prime_5, by norm_num⟩
  · exact ⟨5813, 7, prime_5813, prime_7, by norm_num⟩
  · exact ⟨5791, 31, prime_5791, prime_31, by norm_num⟩
  · exact ⟨5821, 3, prime_5821, prime_3, by norm_num⟩
  · exact ⟨5821, 5, prime_5821, prime_5, by norm_num⟩
  · exact ⟨5821, 7, prime_5821, prime_7, by norm_num⟩
  · exact ⟨5827, 3, prime_5827, prime_3, by norm_num⟩
  · exact ⟨5827, 5, prime_5827, prime_5, by norm_num⟩
  · exact ⟨5827, 7, prime_5827, prime_7, by norm_num⟩
  · exact ⟨5813, 23, prime_5813, prime_23, by norm_num⟩
  · exact ⟨5827, 11, prime_5827, prime_11, by norm_num⟩
  · exact ⟨5827, 13, prime_5827, prime_13, by norm_num⟩
  · exact ⟨5839, 3, prime_5839, prime_3, by norm_num⟩
  · exact ⟨5839, 5, prime_5839, prime_5, by norm_num⟩
  · exact ⟨5843, 3, prime_5843, prime_3, by norm_num⟩
  · exact ⟨5843, 5, prime_5843, prime_5, by norm_num⟩
  · exact ⟨5843, 7, prime_5843, prime_7, by norm_num⟩
  · exact ⟨5849, 3, prime_5849, prime_3, by norm_num⟩
  · exact ⟨5851, 3, prime_5851, prime_3, by norm_num⟩
  · exact ⟨5851, 5, prime_5851, prime_5, by norm_num⟩
  · exact ⟨5851, 7, prime_5851, prime_7, by norm_num⟩
  · exact ⟨5857, 3, prime_5857, prime_3, by norm_num⟩
  · exact ⟨5857, 5, prime_5857, prime_5, by norm_num⟩
  · exact ⟨5861, 3, prime_5861, prime_3, by norm_num⟩
  · exact ⟨5861, 5, prime_5861, prime_5, by norm_num⟩
  · exact ⟨5861, 7, prime_5861, prime_7, by norm_num⟩
  · exact ⟨5867, 3, prime_5867, prime_3, by norm_num⟩
  · exact ⟨5869, 3, prime_5869, prime_3, by norm_num⟩
  · exact ⟨5869, 5, prime_5869, prime_5, by norm_num⟩
  · exact ⟨5869, 7, prime_5869, prime_7, by norm_num⟩
  · exact ⟨5867, 11, prime_5867, prime_11, by norm_num⟩
  · exact ⟨5869, 11, prime_5869, prime_11, by norm_num⟩
  · exact ⟨5879, 3, prime_5879, prime_3, by norm_num⟩
  · exact ⟨5881, 3, prime_5881, prime_3, by norm_num⟩
  · exact ⟨5881, 5, prime_5881, prime_5, by norm_num⟩
  · exact ⟨5881, 7, prime_5881, prime_7, by norm_num⟩
  · exact ⟨5879, 11, prime_5879, prime_11, by norm_num⟩
  · exact ⟨5881, 11, prime_5881, prime_11, by norm_num⟩
  · exact ⟨5881, 13, prime_5881, prime_13, by norm_num⟩
  · exact ⟨5879, 17, prime_5879, prime_17, by norm_num⟩
  · exact ⟨5881, 17, prime_5881, prime_17, by norm_num⟩
  · exact ⟨5897, 3, prime_5897, prime_3, by norm_num⟩
  · exact ⟨5897, 5, prime_5897, prime_5, by norm_num⟩
  · exact ⟨5897, 7, prime_5897, prime_7, by norm_num⟩
  · exact ⟨5903, 3, prime_5903, prime_3, by norm_num⟩
  · exact ⟨5903, 5, prime_5903, prime_5, by norm_num⟩
  · exact ⟨5903, 7, prime_5903, prime_7, by norm_num⟩
  · exact ⟨5881, 31, prime_5881, prime_31, by norm_num⟩
  · exact ⟨5903, 11, prime_5903, prime_11, by norm_num⟩
  · exact ⟨5903, 13, prime_5903, prime_13, by norm_num⟩
  · exact ⟨5881, 37, prime_5881, prime_37, by norm_num⟩
  · exact ⟨5903, 17, prime_5903, prime_17, by norm_num⟩
  · exact ⟨5903, 19, prime_5903, prime_19, by norm_num⟩
  · exact ⟨5881, 43, prime_5881, prime_43, by norm_num⟩
  · exact ⟨5923, 3, prime_5923, prime_3, by norm_num⟩
  · exact ⟨5923, 5, prime_5923, prime_5, by norm_num⟩
  · exact ⟨5927, 3, prime_5927, prime_3, by norm_num⟩
  · exact ⟨5927, 5, prime_5927, prime_5, by norm_num⟩
  · exact ⟨5927, 7, prime_5927, prime_7, by norm_num⟩
  · exact ⟨5923, 13, prime_5923, prime_13, by norm_num⟩
  · exact ⟨5927, 11, prime_5927, prime_11, by norm_num⟩
  · exact ⟨5927, 13, prime_5927, prime_13, by norm_num⟩
  · exact ⟨5939, 3, prime_5939, prime_3, by norm_num⟩
  · exact ⟨5939, 5, prime_5939, prime_5, by norm_num⟩
  · exact ⟨5939, 7, prime_5939, prime_7, by norm_num⟩
  · exact ⟨5881, 67, prime_5881, prime_67, by norm_num⟩
  · exact ⟨5939, 11, prime_5939, prime_11, by norm_num⟩
  · exact ⟨5939, 13, prime_5939, prime_13, by norm_num⟩
  · exact ⟨5923, 31, prime_5923, prime_31, by norm_num⟩
  · exact ⟨5953, 3, prime_5953, prime_3, by norm_num⟩
  · exact ⟨5953, 5, prime_5953, prime_5, by norm_num⟩
  · exact ⟨5953, 7, prime_5953, prime_7, by norm_num⟩
  · exact ⟨5939, 23, prime_5939, prime_23, by norm_num⟩
  · exact ⟨5953, 11, prime_5953, prime_11, by norm_num⟩
  · exact ⟨5953, 13, prime_5953, prime_13, by norm_num⟩
  · exact ⟨5939, 29, prime_5939, prime_29, by norm_num⟩
  · exact ⟨5953, 17, prime_5953, prime_17, by norm_num⟩
  · exact ⟨5953, 19, prime_5953, prime_19, by norm_num⟩
  · exact ⟨5927, 47, prime_5927, prime_47, by norm_num⟩
  · exact ⟨5953, 23, prime_5953, prime_23, by norm_num⟩
  · exact ⟨5881, 97, prime_5881, prime_97, by norm_num⟩
  · exact ⟨5939, 41, prime_5939, prime_41, by norm_num⟩
  · exact ⟨5953, 29, prime_5953, prime_29, by norm_num⟩
  · exact ⟨5981, 3, prime_5981, prime_3, by norm_num⟩
  · exact ⟨5981, 5, prime_5981, prime_5, by norm_num⟩
  · exact ⟨5981, 7, prime_5981, prime_7, by norm_num⟩
  · exact ⟨5987, 3, prime_5987, prime_3, by norm_num⟩
  · exact ⟨5987, 5, prime_5987, prime_5, by norm_num⟩
  · exact ⟨5987, 7, prime_5987, prime_7, by norm_num⟩
  · exact ⟨5953, 43, prime_5953, prime_43, by norm_num⟩
  · exact ⟨5987, 11, prime_5987, prime_11, by norm_num⟩
  · exact ⟨5987, 13, prime_5987, prime_13, by norm_num⟩
  · exact ⟨5923, 79, prime_5923, prime_79, by norm_num⟩

private theorem goldbach_chunk_30 : ∀ k : ℕ, 3002 ≤ k → k ≤ 3101 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5987, 17, prime_5987, prime_17, by norm_num⟩
  · exact ⟨5987, 19, prime_5987, prime_19, by norm_num⟩
  · exact ⟨5881, 127, prime_5881, prime_127, by norm_num⟩
  · exact ⟨6007, 3, prime_6007, prime_3, by norm_num⟩
  · exact ⟨6007, 5, prime_6007, prime_5, by norm_num⟩
  · exact ⟨6011, 3, prime_6011, prime_3, by norm_num⟩
  · exact ⟨6011, 5, prime_6011, prime_5, by norm_num⟩
  · exact ⟨6011, 7, prime_6011, prime_7, by norm_num⟩
  · exact ⟨6007, 13, prime_6007, prime_13, by norm_num⟩
  · exact ⟨6011, 11, prime_6011, prime_11, by norm_num⟩
  · exact ⟨6011, 13, prime_6011, prime_13, by norm_num⟩
  · exact ⟨6007, 19, prime_6007, prime_19, by norm_num⟩
  · exact ⟨6011, 17, prime_6011, prime_17, by norm_num⟩
  · exact ⟨6011, 19, prime_6011, prime_19, by norm_num⟩
  · exact ⟨6029, 3, prime_6029, prime_3, by norm_num⟩
  · exact ⟨6029, 5, prime_6029, prime_5, by norm_num⟩
  · exact ⟨6029, 7, prime_6029, prime_7, by norm_num⟩
  · exact ⟨6007, 31, prime_6007, prime_31, by norm_num⟩
  · exact ⟨6037, 3, prime_6037, prime_3, by norm_num⟩
  · exact ⟨6037, 5, prime_6037, prime_5, by norm_num⟩
  · exact ⟨6037, 7, prime_6037, prime_7, by norm_num⟩
  · exact ⟨6043, 3, prime_6043, prime_3, by norm_num⟩
  · exact ⟨6043, 5, prime_6043, prime_5, by norm_num⟩
  · exact ⟨6047, 3, prime_6047, prime_3, by norm_num⟩
  · exact ⟨6047, 5, prime_6047, prime_5, by norm_num⟩
  · exact ⟨6047, 7, prime_6047, prime_7, by norm_num⟩
  · exact ⟨6053, 3, prime_6053, prime_3, by norm_num⟩
  · exact ⟨6053, 5, prime_6053, prime_5, by norm_num⟩
  · exact ⟨6053, 7, prime_6053, prime_7, by norm_num⟩
  · exact ⟨6043, 19, prime_6043, prime_19, by norm_num⟩
  · exact ⟨6053, 11, prime_6053, prime_11, by norm_num⟩
  · exact ⟨6053, 13, prime_6053, prime_13, by norm_num⟩
  · exact ⟨6037, 31, prime_6037, prime_31, by norm_num⟩
  · exact ⟨6067, 3, prime_6067, prime_3, by norm_num⟩
  · exact ⟨6067, 5, prime_6067, prime_5, by norm_num⟩
  · exact ⟨6067, 7, prime_6067, prime_7, by norm_num⟩
  · exact ⟨6073, 3, prime_6073, prime_3, by norm_num⟩
  · exact ⟨6073, 5, prime_6073, prime_5, by norm_num⟩
  · exact ⟨6073, 7, prime_6073, prime_7, by norm_num⟩
  · exact ⟨6079, 3, prime_6079, prime_3, by norm_num⟩
  · exact ⟨6079, 5, prime_6079, prime_5, by norm_num⟩
  · exact ⟨6079, 7, prime_6079, prime_7, by norm_num⟩
  · exact ⟨6047, 41, prime_6047, prime_41, by norm_num⟩
  · exact ⟨6079, 11, prime_6079, prime_11, by norm_num⟩
  · exact ⟨6089, 3, prime_6089, prime_3, by norm_num⟩
  · exact ⟨6091, 3, prime_6091, prime_3, by norm_num⟩
  · exact ⟨6091, 5, prime_6091, prime_5, by norm_num⟩
  · exact ⟨6091, 7, prime_6091, prime_7, by norm_num⟩
  · exact ⟨6089, 11, prime_6089, prime_11, by norm_num⟩
  · exact ⟨6091, 11, prime_6091, prime_11, by norm_num⟩
  · exact ⟨6101, 3, prime_6101, prime_3, by norm_num⟩
  · exact ⟨6101, 5, prime_6101, prime_5, by norm_num⟩
  · exact ⟨6101, 7, prime_6101, prime_7, by norm_num⟩
  · exact ⟨6091, 19, prime_6091, prime_19, by norm_num⟩
  · exact ⟨6101, 11, prime_6101, prime_11, by norm_num⟩
  · exact ⟨6101, 13, prime_6101, prime_13, by norm_num⟩
  · exact ⟨6113, 3, prime_6113, prime_3, by norm_num⟩
  · exact ⟨6113, 5, prime_6113, prime_5, by norm_num⟩
  · exact ⟨6113, 7, prime_6113, prime_7, by norm_num⟩
  · exact ⟨6091, 31, prime_6091, prime_31, by norm_num⟩
  · exact ⟨6121, 3, prime_6121, prime_3, by norm_num⟩
  · exact ⟨6121, 5, prime_6121, prime_5, by norm_num⟩
  · exact ⟨6121, 7, prime_6121, prime_7, by norm_num⟩
  · exact ⟨6113, 17, prime_6113, prime_17, by norm_num⟩
  · exact ⟨6121, 11, prime_6121, prime_11, by norm_num⟩
  · exact ⟨6131, 3, prime_6131, prime_3, by norm_num⟩
  · exact ⟨6133, 3, prime_6133, prime_3, by norm_num⟩
  · exact ⟨6133, 5, prime_6133, prime_5, by norm_num⟩
  · exact ⟨6133, 7, prime_6133, prime_7, by norm_num⟩
  · exact ⟨6131, 11, prime_6131, prime_11, by norm_num⟩
  · exact ⟨6133, 11, prime_6133, prime_11, by norm_num⟩
  · exact ⟨6143, 3, prime_6143, prime_3, by norm_num⟩
  · exact ⟨6143, 5, prime_6143, prime_5, by norm_num⟩
  · exact ⟨6143, 7, prime_6143, prime_7, by norm_num⟩
  · exact ⟨6133, 19, prime_6133, prime_19, by norm_num⟩
  · exact ⟨6151, 3, prime_6151, prime_3, by norm_num⟩
  · exact ⟨6151, 5, prime_6151, prime_5, by norm_num⟩
  · exact ⟨6151, 7, prime_6151, prime_7, by norm_num⟩
  · exact ⟨6143, 17, prime_6143, prime_17, by norm_num⟩
  · exact ⟨6151, 11, prime_6151, prime_11, by norm_num⟩
  · exact ⟨6151, 13, prime_6151, prime_13, by norm_num⟩
  · exact ⟨6163, 3, prime_6163, prime_3, by norm_num⟩
  · exact ⟨6163, 5, prime_6163, prime_5, by norm_num⟩
  · exact ⟨6163, 7, prime_6163, prime_7, by norm_num⟩
  · exact ⟨6143, 29, prime_6143, prime_29, by norm_num⟩
  · exact ⟨6163, 11, prime_6163, prime_11, by norm_num⟩
  · exact ⟨6173, 3, prime_6173, prime_3, by norm_num⟩
  · exact ⟨6173, 5, prime_6173, prime_5, by norm_num⟩
  · exact ⟨6173, 7, prime_6173, prime_7, by norm_num⟩
  · exact ⟨6163, 19, prime_6163, prime_19, by norm_num⟩
  · exact ⟨6173, 11, prime_6173, prime_11, by norm_num⟩
  · exact ⟨6173, 13, prime_6173, prime_13, by norm_num⟩
  · exact ⟨6151, 37, prime_6151, prime_37, by norm_num⟩
  · exact ⟨6173, 17, prime_6173, prime_17, by norm_num⟩
  · exact ⟨6173, 19, prime_6173, prime_19, by norm_num⟩
  · exact ⟨6163, 31, prime_6163, prime_31, by norm_num⟩
  · exact ⟨6173, 23, prime_6173, prime_23, by norm_num⟩
  · exact ⟨6151, 47, prime_6151, prime_47, by norm_num⟩
  · exact ⟨6197, 3, prime_6197, prime_3, by norm_num⟩
  · exact ⟨6199, 3, prime_6199, prime_3, by norm_num⟩

private theorem goldbach_chunk_31 : ∀ k : ℕ, 3102 ≤ k → k ≤ 3201 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨6199, 5, prime_6199, prime_5, by norm_num⟩
  · exact ⟨6203, 3, prime_6203, prime_3, by norm_num⟩
  · exact ⟨6203, 5, prime_6203, prime_5, by norm_num⟩
  · exact ⟨6203, 7, prime_6203, prime_7, by norm_num⟩
  · exact ⟨6199, 13, prime_6199, prime_13, by norm_num⟩
  · exact ⟨6211, 3, prime_6211, prime_3, by norm_num⟩
  · exact ⟨6211, 5, prime_6211, prime_5, by norm_num⟩
  · exact ⟨6211, 7, prime_6211, prime_7, by norm_num⟩
  · exact ⟨6217, 3, prime_6217, prime_3, by norm_num⟩
  · exact ⟨6217, 5, prime_6217, prime_5, by norm_num⟩
  · exact ⟨6221, 3, prime_6221, prime_3, by norm_num⟩
  · exact ⟨6221, 5, prime_6221, prime_5, by norm_num⟩
  · exact ⟨6221, 7, prime_6221, prime_7, by norm_num⟩
  · exact ⟨6217, 13, prime_6217, prime_13, by norm_num⟩
  · exact ⟨6229, 3, prime_6229, prime_3, by norm_num⟩
  · exact ⟨6229, 5, prime_6229, prime_5, by norm_num⟩
  · exact ⟨6229, 7, prime_6229, prime_7, by norm_num⟩
  · exact ⟨6221, 17, prime_6221, prime_17, by norm_num⟩
  · exact ⟨6229, 11, prime_6229, prime_11, by norm_num⟩
  · exact ⟨6229, 13, prime_6229, prime_13, by norm_num⟩
  · exact ⟨6221, 23, prime_6221, prime_23, by norm_num⟩
  · exact ⟨6229, 17, prime_6229, prime_17, by norm_num⟩
  · exact ⟨6229, 19, prime_6229, prime_19, by norm_num⟩
  · exact ⟨6247, 3, prime_6247, prime_3, by norm_num⟩
  · exact ⟨6247, 5, prime_6247, prime_5, by norm_num⟩
  · exact ⟨6247, 7, prime_6247, prime_7, by norm_num⟩
  · exact ⟨6203, 53, prime_6203, prime_53, by norm_num⟩
  · exact ⟨6247, 11, prime_6247, prime_11, by norm_num⟩
  · exact ⟨6257, 3, prime_6257, prime_3, by norm_num⟩
  · exact ⟨6257, 5, prime_6257, prime_5, by norm_num⟩
  · exact ⟨6257, 7, prime_6257, prime_7, by norm_num⟩
  · exact ⟨6263, 3, prime_6263, prime_3, by norm_num⟩
  · exact ⟨6263, 5, prime_6263, prime_5, by norm_num⟩
  · exact ⟨6263, 7, prime_6263, prime_7, by norm_num⟩
  · exact ⟨6269, 3, prime_6269, prime_3, by norm_num⟩
  · exact ⟨6271, 3, prime_6271, prime_3, by norm_num⟩
  · exact ⟨6271, 5, prime_6271, prime_5, by norm_num⟩
  · exact ⟨6271, 7, prime_6271, prime_7, by norm_num⟩
  · exact ⟨6277, 3, prime_6277, prime_3, by norm_num⟩
  · exact ⟨6277, 5, prime_6277, prime_5, by norm_num⟩
  · exact ⟨6277, 7, prime_6277, prime_7, by norm_num⟩
  · exact ⟨6269, 17, prime_6269, prime_17, by norm_num⟩
  · exact ⟨6277, 11, prime_6277, prime_11, by norm_num⟩
  · exact ⟨6287, 3, prime_6287, prime_3, by norm_num⟩
  · exact ⟨6287, 5, prime_6287, prime_5, by norm_num⟩
  · exact ⟨6287, 7, prime_6287, prime_7, by norm_num⟩
  · exact ⟨6277, 19, prime_6277, prime_19, by norm_num⟩
  · exact ⟨6287, 11, prime_6287, prime_11, by norm_num⟩
  · exact ⟨6287, 13, prime_6287, prime_13, by norm_num⟩
  · exact ⟨6299, 3, prime_6299, prime_3, by norm_num⟩
  · exact ⟨6301, 3, prime_6301, prime_3, by norm_num⟩
  · exact ⟨6301, 5, prime_6301, prime_5, by norm_num⟩
  · exact ⟨6301, 7, prime_6301, prime_7, by norm_num⟩
  · exact ⟨6299, 11, prime_6299, prime_11, by norm_num⟩
  · exact ⟨6301, 11, prime_6301, prime_11, by norm_num⟩
  · exact ⟨6311, 3, prime_6311, prime_3, by norm_num⟩
  · exact ⟨6311, 5, prime_6311, prime_5, by norm_num⟩
  · exact ⟨6311, 7, prime_6311, prime_7, by norm_num⟩
  · exact ⟨6317, 3, prime_6317, prime_3, by norm_num⟩
  · exact ⟨6317, 5, prime_6317, prime_5, by norm_num⟩
  · exact ⟨6317, 7, prime_6317, prime_7, by norm_num⟩
  · exact ⟨6323, 3, prime_6323, prime_3, by norm_num⟩
  · exact ⟨6323, 5, prime_6323, prime_5, by norm_num⟩
  · exact ⟨6323, 7, prime_6323, prime_7, by norm_num⟩
  · exact ⟨6329, 3, prime_6329, prime_3, by norm_num⟩
  · exact ⟨6329, 5, prime_6329, prime_5, by norm_num⟩
  · exact ⟨6329, 7, prime_6329, prime_7, by norm_num⟩
  · exact ⟨6301, 37, prime_6301, prime_37, by norm_num⟩
  · exact ⟨6337, 3, prime_6337, prime_3, by norm_num⟩
  · exact ⟨6337, 5, prime_6337, prime_5, by norm_num⟩
  · exact ⟨6337, 7, prime_6337, prime_7, by norm_num⟩
  · exact ⟨6343, 3, prime_6343, prime_3, by norm_num⟩
  · exact ⟨6343, 5, prime_6343, prime_5, by norm_num⟩
  · exact ⟨6343, 7, prime_6343, prime_7, by norm_num⟩
  · exact ⟨6329, 23, prime_6329, prime_23, by norm_num⟩
  · exact ⟨6343, 11, prime_6343, prime_11, by norm_num⟩
  · exact ⟨6353, 3, prime_6353, prime_3, by norm_num⟩
  · exact ⟨6353, 5, prime_6353, prime_5, by norm_num⟩
  · exact ⟨6353, 7, prime_6353, prime_7, by norm_num⟩
  · exact ⟨6359, 3, prime_6359, prime_3, by norm_num⟩
  · exact ⟨6361, 3, prime_6361, prime_3, by norm_num⟩
  · exact ⟨6361, 5, prime_6361, prime_5, by norm_num⟩
  · exact ⟨6361, 7, prime_6361, prime_7, by norm_num⟩
  · exact ⟨6367, 3, prime_6367, prime_3, by norm_num⟩
  · exact ⟨6367, 5, prime_6367, prime_5, by norm_num⟩
  · exact ⟨6367, 7, prime_6367, prime_7, by norm_num⟩
  · exact ⟨6373, 3, prime_6373, prime_3, by norm_num⟩
  · exact ⟨6373, 5, prime_6373, prime_5, by norm_num⟩
  · exact ⟨6373, 7, prime_6373, prime_7, by norm_num⟩
  · exact ⟨6379, 3, prime_6379, prime_3, by norm_num⟩
  · exact ⟨6379, 5, prime_6379, prime_5, by norm_num⟩
  · exact ⟨6379, 7, prime_6379, prime_7, by norm_num⟩
  · exact ⟨6359, 29, prime_6359, prime_29, by norm_num⟩
  · exact ⟨6379, 11, prime_6379, prime_11, by norm_num⟩
  · exact ⟨6389, 3, prime_6389, prime_3, by norm_num⟩
  · exact ⟨6389, 5, prime_6389, prime_5, by norm_num⟩
  · exact ⟨6389, 7, prime_6389, prime_7, by norm_num⟩
  · exact ⟨6379, 19, prime_6379, prime_19, by norm_num⟩
  · exact ⟨6397, 3, prime_6397, prime_3, by norm_num⟩
  · exact ⟨6397, 5, prime_6397, prime_5, by norm_num⟩

private theorem goldbach_chunk_32 : ∀ k : ℕ, 3202 ≤ k → k ≤ 3301 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨6397, 7, prime_6397, prime_7, by norm_num⟩
  · exact ⟨6389, 17, prime_6389, prime_17, by norm_num⟩
  · exact ⟨6397, 11, prime_6397, prime_11, by norm_num⟩
  · exact ⟨6397, 13, prime_6397, prime_13, by norm_num⟩
  · exact ⟨6389, 23, prime_6389, prime_23, by norm_num⟩
  · exact ⟨6397, 17, prime_6397, prime_17, by norm_num⟩
  · exact ⟨6397, 19, prime_6397, prime_19, by norm_num⟩
  · exact ⟨6389, 29, prime_6389, prime_29, by norm_num⟩
  · exact ⟨6397, 23, prime_6397, prime_23, by norm_num⟩
  · exact ⟨6379, 43, prime_6379, prime_43, by norm_num⟩
  · exact ⟨6421, 3, prime_6421, prime_3, by norm_num⟩
  · exact ⟨6421, 5, prime_6421, prime_5, by norm_num⟩
  · exact ⟨6421, 7, prime_6421, prime_7, by norm_num⟩
  · exact ⟨6427, 3, prime_6427, prime_3, by norm_num⟩
  · exact ⟨6427, 5, prime_6427, prime_5, by norm_num⟩
  · exact ⟨6427, 7, prime_6427, prime_7, by norm_num⟩
  · exact ⟨6389, 47, prime_6389, prime_47, by norm_num⟩
  · exact ⟨6427, 11, prime_6427, prime_11, by norm_num⟩
  · exact ⟨6427, 13, prime_6427, prime_13, by norm_num⟩
  · exact ⟨6389, 53, prime_6389, prime_53, by norm_num⟩
  · exact ⟨6427, 17, prime_6427, prime_17, by norm_num⟩
  · exact ⟨6427, 19, prime_6427, prime_19, by norm_num⟩
  · exact ⟨6389, 59, prime_6389, prime_59, by norm_num⟩
  · exact ⟨6427, 23, prime_6427, prime_23, by norm_num⟩
  · exact ⟨6449, 3, prime_6449, prime_3, by norm_num⟩
  · exact ⟨6451, 3, prime_6451, prime_3, by norm_num⟩
  · exact ⟨6451, 5, prime_6451, prime_5, by norm_num⟩
  · exact ⟨6451, 7, prime_6451, prime_7, by norm_num⟩
  · exact ⟨6449, 11, prime_6449, prime_11, by norm_num⟩
  · exact ⟨6451, 11, prime_6451, prime_11, by norm_num⟩
  · exact ⟨6451, 13, prime_6451, prime_13, by norm_num⟩
  · exact ⟨6449, 17, prime_6449, prime_17, by norm_num⟩
  · exact ⟨6451, 17, prime_6451, prime_17, by norm_num⟩
  · exact ⟨6451, 19, prime_6451, prime_19, by norm_num⟩
  · exact ⟨6469, 3, prime_6469, prime_3, by norm_num⟩
  · exact ⟨6469, 5, prime_6469, prime_5, by norm_num⟩
  · exact ⟨6473, 3, prime_6473, prime_3, by norm_num⟩
  · exact ⟨6473, 5, prime_6473, prime_5, by norm_num⟩
  · exact ⟨6473, 7, prime_6473, prime_7, by norm_num⟩
  · exact ⟨6469, 13, prime_6469, prime_13, by norm_num⟩
  · exact ⟨6481, 3, prime_6481, prime_3, by norm_num⟩
  · exact ⟨6481, 5, prime_6481, prime_5, by norm_num⟩
  · exact ⟨6481, 7, prime_6481, prime_7, by norm_num⟩
  · exact ⟨6473, 17, prime_6473, prime_17, by norm_num⟩
  · exact ⟨6481, 11, prime_6481, prime_11, by norm_num⟩
  · exact ⟨6491, 3, prime_6491, prime_3, by norm_num⟩
  · exact ⟨6491, 5, prime_6491, prime_5, by norm_num⟩
  · exact ⟨6491, 7, prime_6491, prime_7, by norm_num⟩
  · exact ⟨6481, 19, prime_6481, prime_19, by norm_num⟩
  · exact ⟨6491, 11, prime_6491, prime_11, by norm_num⟩
  · exact ⟨6491, 13, prime_6491, prime_13, by norm_num⟩
  · exact ⟨6469, 37, prime_6469, prime_37, by norm_num⟩
  · exact ⟨6491, 17, prime_6491, prime_17, by norm_num⟩
  · exact ⟨6491, 19, prime_6491, prime_19, by norm_num⟩
  · exact ⟨6481, 31, prime_6481, prime_31, by norm_num⟩
  · exact ⟨6491, 23, prime_6491, prime_23, by norm_num⟩
  · exact ⟨6473, 43, prime_6473, prime_43, by norm_num⟩
  · exact ⟨6481, 37, prime_6481, prime_37, by norm_num⟩
  · exact ⟨6491, 29, prime_6491, prime_29, by norm_num⟩
  · exact ⟨6491, 31, prime_6491, prime_31, by norm_num⟩
  · exact ⟨6521, 3, prime_6521, prime_3, by norm_num⟩
  · exact ⟨6521, 5, prime_6521, prime_5, by norm_num⟩
  · exact ⟨6521, 7, prime_6521, prime_7, by norm_num⟩
  · exact ⟨6469, 61, prime_6469, prime_61, by norm_num⟩
  · exact ⟨6529, 3, prime_6529, prime_3, by norm_num⟩
  · exact ⟨6529, 5, prime_6529, prime_5, by norm_num⟩
  · exact ⟨6529, 7, prime_6529, prime_7, by norm_num⟩
  · exact ⟨6521, 17, prime_6521, prime_17, by norm_num⟩
  · exact ⟨6529, 11, prime_6529, prime_11, by norm_num⟩
  · exact ⟨6529, 13, prime_6529, prime_13, by norm_num⟩
  · exact ⟨6521, 23, prime_6521, prime_23, by norm_num⟩
  · exact ⟨6529, 17, prime_6529, prime_17, by norm_num⟩
  · exact ⟨6529, 19, prime_6529, prime_19, by norm_num⟩
  · exact ⟨6547, 3, prime_6547, prime_3, by norm_num⟩
  · exact ⟨6547, 5, prime_6547, prime_5, by norm_num⟩
  · exact ⟨6551, 3, prime_6551, prime_3, by norm_num⟩
  · exact ⟨6553, 3, prime_6553, prime_3, by norm_num⟩
  · exact ⟨6553, 5, prime_6553, prime_5, by norm_num⟩
  · exact ⟨6553, 7, prime_6553, prime_7, by norm_num⟩
  · exact ⟨6551, 11, prime_6551, prime_11, by norm_num⟩
  · exact ⟨6553, 11, prime_6553, prime_11, by norm_num⟩
  · exact ⟨6563, 3, prime_6563, prime_3, by norm_num⟩
  · exact ⟨6563, 5, prime_6563, prime_5, by norm_num⟩
  · exact ⟨6563, 7, prime_6563, prime_7, by norm_num⟩
  · exact ⟨6569, 3, prime_6569, prime_3, by norm_num⟩
  · exact ⟨6571, 3, prime_6571, prime_3, by norm_num⟩
  · exact ⟨6571, 5, prime_6571, prime_5, by norm_num⟩
  · exact ⟨6571, 7, prime_6571, prime_7, by norm_num⟩
  · exact ⟨6577, 3, prime_6577, prime_3, by norm_num⟩
  · exact ⟨6577, 5, prime_6577, prime_5, by norm_num⟩
  · exact ⟨6581, 3, prime_6581, prime_3, by norm_num⟩
  · exact ⟨6581, 5, prime_6581, prime_5, by norm_num⟩
  · exact ⟨6581, 7, prime_6581, prime_7, by norm_num⟩
  · exact ⟨6577, 13, prime_6577, prime_13, by norm_num⟩
  · exact ⟨6581, 11, prime_6581, prime_11, by norm_num⟩
  · exact ⟨6581, 13, prime_6581, prime_13, by norm_num⟩
  · exact ⟨6577, 19, prime_6577, prime_19, by norm_num⟩
  · exact ⟨6581, 17, prime_6581, prime_17, by norm_num⟩
  · exact ⟨6581, 19, prime_6581, prime_19, by norm_num⟩
  · exact ⟨6599, 3, prime_6599, prime_3, by norm_num⟩

private theorem goldbach_chunk_33 : ∀ k : ℕ, 3302 ≤ k → k ≤ 3401 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨6599, 5, prime_6599, prime_5, by norm_num⟩
  · exact ⟨6599, 7, prime_6599, prime_7, by norm_num⟩
  · exact ⟨6577, 31, prime_6577, prime_31, by norm_num⟩
  · exact ⟨6607, 3, prime_6607, prime_3, by norm_num⟩
  · exact ⟨6607, 5, prime_6607, prime_5, by norm_num⟩
  · exact ⟨6607, 7, prime_6607, prime_7, by norm_num⟩
  · exact ⟨6599, 17, prime_6599, prime_17, by norm_num⟩
  · exact ⟨6607, 11, prime_6607, prime_11, by norm_num⟩
  · exact ⟨6607, 13, prime_6607, prime_13, by norm_num⟩
  · exact ⟨6619, 3, prime_6619, prime_3, by norm_num⟩
  · exact ⟨6619, 5, prime_6619, prime_5, by norm_num⟩
  · exact ⟨6619, 7, prime_6619, prime_7, by norm_num⟩
  · exact ⟨6599, 29, prime_6599, prime_29, by norm_num⟩
  · exact ⟨6619, 11, prime_6619, prime_11, by norm_num⟩
  · exact ⟨6619, 13, prime_6619, prime_13, by norm_num⟩
  · exact ⟨6581, 53, prime_6581, prime_53, by norm_num⟩
  · exact ⟨6619, 17, prime_6619, prime_17, by norm_num⟩
  · exact ⟨6619, 19, prime_6619, prime_19, by norm_num⟩
  · exact ⟨6637, 3, prime_6637, prime_3, by norm_num⟩
  · exact ⟨6637, 5, prime_6637, prime_5, by norm_num⟩
  · exact ⟨6637, 7, prime_6637, prime_7, by norm_num⟩
  · exact ⟨6599, 47, prime_6599, prime_47, by norm_num⟩
  · exact ⟨6637, 11, prime_6637, prime_11, by norm_num⟩
  · exact ⟨6637, 13, prime_6637, prime_13, by norm_num⟩
  · exact ⟨6599, 53, prime_6599, prime_53, by norm_num⟩
  · exact ⟨6637, 17, prime_6637, prime_17, by norm_num⟩
  · exact ⟨6653, 3, prime_6653, prime_3, by norm_num⟩
  · exact ⟨6653, 5, prime_6653, prime_5, by norm_num⟩
  · exact ⟨6653, 7, prime_6653, prime_7, by norm_num⟩
  · exact ⟨6659, 3, prime_6659, prime_3, by norm_num⟩
  · exact ⟨6661, 3, prime_6661, prime_3, by norm_num⟩
  · exact ⟨6661, 5, prime_6661, prime_5, by norm_num⟩
  · exact ⟨6661, 7, prime_6661, prime_7, by norm_num⟩
  · exact ⟨6659, 11, prime_6659, prime_11, by norm_num⟩
  · exact ⟨6661, 11, prime_6661, prime_11, by norm_num⟩
  · exact ⟨6661, 13, prime_6661, prime_13, by norm_num⟩
  · exact ⟨6673, 3, prime_6673, prime_3, by norm_num⟩
  · exact ⟨6673, 5, prime_6673, prime_5, by norm_num⟩
  · exact ⟨6673, 7, prime_6673, prime_7, by norm_num⟩
  · exact ⟨6679, 3, prime_6679, prime_3, by norm_num⟩
  · exact ⟨6679, 5, prime_6679, prime_5, by norm_num⟩
  · exact ⟨6679, 7, prime_6679, prime_7, by norm_num⟩
  · exact ⟨6659, 29, prime_6659, prime_29, by norm_num⟩
  · exact ⟨6679, 11, prime_6679, prime_11, by norm_num⟩
  · exact ⟨6689, 3, prime_6689, prime_3, by norm_num⟩
  · exact ⟨6691, 3, prime_6691, prime_3, by norm_num⟩
  · exact ⟨6691, 5, prime_6691, prime_5, by norm_num⟩
  · exact ⟨6691, 7, prime_6691, prime_7, by norm_num⟩
  · exact ⟨6689, 11, prime_6689, prime_11, by norm_num⟩
  · exact ⟨6691, 11, prime_6691, prime_11, by norm_num⟩
  · exact ⟨6701, 3, prime_6701, prime_3, by norm_num⟩
  · exact ⟨6703, 3, prime_6703, prime_3, by norm_num⟩
  · exact ⟨6703, 5, prime_6703, prime_5, by norm_num⟩
  · exact ⟨6703, 7, prime_6703, prime_7, by norm_num⟩
  · exact ⟨6709, 3, prime_6709, prime_3, by norm_num⟩
  · exact ⟨6709, 5, prime_6709, prime_5, by norm_num⟩
  · exact ⟨6709, 7, prime_6709, prime_7, by norm_num⟩
  · exact ⟨6701, 17, prime_6701, prime_17, by norm_num⟩
  · exact ⟨6709, 11, prime_6709, prime_11, by norm_num⟩
  · exact ⟨6719, 3, prime_6719, prime_3, by norm_num⟩
  · exact ⟨6719, 5, prime_6719, prime_5, by norm_num⟩
  · exact ⟨6719, 7, prime_6719, prime_7, by norm_num⟩
  · exact ⟨6709, 19, prime_6709, prime_19, by norm_num⟩
  · exact ⟨6719, 11, prime_6719, prime_11, by norm_num⟩
  · exact ⟨6719, 13, prime_6719, prime_13, by norm_num⟩
  · exact ⟨6703, 31, prime_6703, prime_31, by norm_num⟩
  · exact ⟨6733, 3, prime_6733, prime_3, by norm_num⟩
  · exact ⟨6733, 5, prime_6733, prime_5, by norm_num⟩
  · exact ⟨6737, 3, prime_6737, prime_3, by norm_num⟩
  · exact ⟨6737, 5, prime_6737, prime_5, by norm_num⟩
  · exact ⟨6737, 7, prime_6737, prime_7, by norm_num⟩
  · exact ⟨6733, 13, prime_6733, prime_13, by norm_num⟩
  · exact ⟨6737, 11, prime_6737, prime_11, by norm_num⟩
  · exact ⟨6737, 13, prime_6737, prime_13, by norm_num⟩
  · exact ⟨6733, 19, prime_6733, prime_19, by norm_num⟩
  · exact ⟨6737, 17, prime_6737, prime_17, by norm_num⟩
  · exact ⟨6737, 19, prime_6737, prime_19, by norm_num⟩
  · exact ⟨6691, 67, prime_6691, prime_67, by norm_num⟩
  · exact ⟨6737, 23, prime_6737, prime_23, by norm_num⟩
  · exact ⟨6733, 29, prime_6733, prime_29, by norm_num⟩
  · exact ⟨6761, 3, prime_6761, prime_3, by norm_num⟩
  · exact ⟨6763, 3, prime_6763, prime_3, by norm_num⟩
  · exact ⟨6763, 5, prime_6763, prime_5, by norm_num⟩
  · exact ⟨6763, 7, prime_6763, prime_7, by norm_num⟩
  · exact ⟨6761, 11, prime_6761, prime_11, by norm_num⟩
  · exact ⟨6763, 11, prime_6763, prime_11, by norm_num⟩
  · exact ⟨6763, 13, prime_6763, prime_13, by norm_num⟩
  · exact ⟨6761, 17, prime_6761, prime_17, by norm_num⟩
  · exact ⟨6763, 17, prime_6763, prime_17, by norm_num⟩
  · exact ⟨6779, 3, prime_6779, prime_3, by norm_num⟩
  · exact ⟨6781, 3, prime_6781, prime_3, by norm_num⟩
  · exact ⟨6781, 5, prime_6781, prime_5, by norm_num⟩
  · exact ⟨6781, 7, prime_6781, prime_7, by norm_num⟩
  · exact ⟨6779, 11, prime_6779, prime_11, by norm_num⟩
  · exact ⟨6781, 11, prime_6781, prime_11, by norm_num⟩
  · exact ⟨6791, 3, prime_6791, prime_3, by norm_num⟩
  · exact ⟨6793, 3, prime_6793, prime_3, by norm_num⟩
  · exact ⟨6793, 5, prime_6793, prime_5, by norm_num⟩
  · exact ⟨6793, 7, prime_6793, prime_7, by norm_num⟩
  · exact ⟨6791, 11, prime_6791, prime_11, by norm_num⟩

private theorem goldbach_chunk_34 : ∀ k : ℕ, 3402 ≤ k → k ≤ 3501 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨6793, 11, prime_6793, prime_11, by norm_num⟩
  · exact ⟨6803, 3, prime_6803, prime_3, by norm_num⟩
  · exact ⟨6803, 5, prime_6803, prime_5, by norm_num⟩
  · exact ⟨6803, 7, prime_6803, prime_7, by norm_num⟩
  · exact ⟨6793, 19, prime_6793, prime_19, by norm_num⟩
  · exact ⟨6803, 11, prime_6803, prime_11, by norm_num⟩
  · exact ⟨6803, 13, prime_6803, prime_13, by norm_num⟩
  · exact ⟨6781, 37, prime_6781, prime_37, by norm_num⟩
  · exact ⟨6803, 17, prime_6803, prime_17, by norm_num⟩
  · exact ⟨6803, 19, prime_6803, prime_19, by norm_num⟩
  · exact ⟨6793, 31, prime_6793, prime_31, by norm_num⟩
  · exact ⟨6823, 3, prime_6823, prime_3, by norm_num⟩
  · exact ⟨6823, 5, prime_6823, prime_5, by norm_num⟩
  · exact ⟨6827, 3, prime_6827, prime_3, by norm_num⟩
  · exact ⟨6829, 3, prime_6829, prime_3, by norm_num⟩
  · exact ⟨6829, 5, prime_6829, prime_5, by norm_num⟩
  · exact ⟨6833, 3, prime_6833, prime_3, by norm_num⟩
  · exact ⟨6833, 5, prime_6833, prime_5, by norm_num⟩
  · exact ⟨6833, 7, prime_6833, prime_7, by norm_num⟩
  · exact ⟨6829, 13, prime_6829, prime_13, by norm_num⟩
  · exact ⟨6841, 3, prime_6841, prime_3, by norm_num⟩
  · exact ⟨6841, 5, prime_6841, prime_5, by norm_num⟩
  · exact ⟨6841, 7, prime_6841, prime_7, by norm_num⟩
  · exact ⟨6833, 17, prime_6833, prime_17, by norm_num⟩
  · exact ⟨6841, 11, prime_6841, prime_11, by norm_num⟩
  · exact ⟨6841, 13, prime_6841, prime_13, by norm_num⟩
  · exact ⟨6833, 23, prime_6833, prime_23, by norm_num⟩
  · exact ⟨6841, 17, prime_6841, prime_17, by norm_num⟩
  · exact ⟨6857, 3, prime_6857, prime_3, by norm_num⟩
  · exact ⟨6857, 5, prime_6857, prime_5, by norm_num⟩
  · exact ⟨6857, 7, prime_6857, prime_7, by norm_num⟩
  · exact ⟨6863, 3, prime_6863, prime_3, by norm_num⟩
  · exact ⟨6863, 5, prime_6863, prime_5, by norm_num⟩
  · exact ⟨6863, 7, prime_6863, prime_7, by norm_num⟩
  · exact ⟨6869, 3, prime_6869, prime_3, by norm_num⟩
  · exact ⟨6871, 3, prime_6871, prime_3, by norm_num⟩
  · exact ⟨6871, 5, prime_6871, prime_5, by norm_num⟩
  · exact ⟨6871, 7, prime_6871, prime_7, by norm_num⟩
  · exact ⟨6869, 11, prime_6869, prime_11, by norm_num⟩
  · exact ⟨6871, 11, prime_6871, prime_11, by norm_num⟩
  · exact ⟨6871, 13, prime_6871, prime_13, by norm_num⟩
  · exact ⟨6883, 3, prime_6883, prime_3, by norm_num⟩
  · exact ⟨6883, 5, prime_6883, prime_5, by norm_num⟩
  · exact ⟨6883, 7, prime_6883, prime_7, by norm_num⟩
  · exact ⟨6869, 23, prime_6869, prime_23, by norm_num⟩
  · exact ⟨6883, 11, prime_6883, prime_11, by norm_num⟩
  · exact ⟨6883, 13, prime_6883, prime_13, by norm_num⟩
  · exact ⟨6869, 29, prime_6869, prime_29, by norm_num⟩
  · exact ⟨6883, 17, prime_6883, prime_17, by norm_num⟩
  · exact ⟨6899, 3, prime_6899, prime_3, by norm_num⟩
  · exact ⟨6899, 5, prime_6899, prime_5, by norm_num⟩
  · exact ⟨6899, 7, prime_6899, prime_7, by norm_num⟩
  · exact ⟨6871, 37, prime_6871, prime_37, by norm_num⟩
  · exact ⟨6907, 3, prime_6907, prime_3, by norm_num⟩
  · exact ⟨6907, 5, prime_6907, prime_5, by norm_num⟩
  · exact ⟨6911, 3, prime_6911, prime_3, by norm_num⟩
  · exact ⟨6911, 5, prime_6911, prime_5, by norm_num⟩
  · exact ⟨6911, 7, prime_6911, prime_7, by norm_num⟩
  · exact ⟨6917, 3, prime_6917, prime_3, by norm_num⟩
  · exact ⟨6917, 5, prime_6917, prime_5, by norm_num⟩
  · exact ⟨6917, 7, prime_6917, prime_7, by norm_num⟩
  · exact ⟨6907, 19, prime_6907, prime_19, by norm_num⟩
  · exact ⟨6917, 11, prime_6917, prime_11, by norm_num⟩
  · exact ⟨6917, 13, prime_6917, prime_13, by norm_num⟩
  · exact ⟨6871, 61, prime_6871, prime_61, by norm_num⟩
  · exact ⟨6917, 17, prime_6917, prime_17, by norm_num⟩
  · exact ⟨6917, 19, prime_6917, prime_19, by norm_num⟩
  · exact ⟨6907, 31, prime_6907, prime_31, by norm_num⟩
  · exact ⟨6917, 23, prime_6917, prime_23, by norm_num⟩
  · exact ⟨6911, 31, prime_6911, prime_31, by norm_num⟩
  · exact ⟨6907, 37, prime_6907, prime_37, by norm_num⟩
  · exact ⟨6917, 29, prime_6917, prime_29, by norm_num⟩
  · exact ⟨6917, 31, prime_6917, prime_31, by norm_num⟩
  · exact ⟨6947, 3, prime_6947, prime_3, by norm_num⟩
  · exact ⟨6949, 3, prime_6949, prime_3, by norm_num⟩
  · exact ⟨6949, 5, prime_6949, prime_5, by norm_num⟩
  · exact ⟨6949, 7, prime_6949, prime_7, by norm_num⟩
  · exact ⟨6947, 11, prime_6947, prime_11, by norm_num⟩
  · exact ⟨6949, 11, prime_6949, prime_11, by norm_num⟩
  · exact ⟨6959, 3, prime_6959, prime_3, by norm_num⟩
  · exact ⟨6961, 3, prime_6961, prime_3, by norm_num⟩
  · exact ⟨6961, 5, prime_6961, prime_5, by norm_num⟩
  · exact ⟨6961, 7, prime_6961, prime_7, by norm_num⟩
  · exact ⟨6967, 3, prime_6967, prime_3, by norm_num⟩
  · exact ⟨6967, 5, prime_6967, prime_5, by norm_num⟩
  · exact ⟨6971, 3, prime_6971, prime_3, by norm_num⟩
  · exact ⟨6971, 5, prime_6971, prime_5, by norm_num⟩
  · exact ⟨6971, 7, prime_6971, prime_7, by norm_num⟩
  · exact ⟨6977, 3, prime_6977, prime_3, by norm_num⟩
  · exact ⟨6977, 5, prime_6977, prime_5, by norm_num⟩
  · exact ⟨6977, 7, prime_6977, prime_7, by norm_num⟩
  · exact ⟨6983, 3, prime_6983, prime_3, by norm_num⟩
  · exact ⟨6983, 5, prime_6983, prime_5, by norm_num⟩
  · exact ⟨6983, 7, prime_6983, prime_7, by norm_num⟩
  · exact ⟨6961, 31, prime_6961, prime_31, by norm_num⟩
  · exact ⟨6991, 3, prime_6991, prime_3, by norm_num⟩
  · exact ⟨6991, 5, prime_6991, prime_5, by norm_num⟩
  · exact ⟨6991, 7, prime_6991, prime_7, by norm_num⟩
  · exact ⟨6997, 3, prime_6997, prime_3, by norm_num⟩
  · exact ⟨6997, 5, prime_6997, prime_5, by norm_num⟩

private theorem goldbach_chunk_35 : ∀ k : ℕ, 3502 ≤ k → k ≤ 3601 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7001, 3, prime_7001, prime_3, by norm_num⟩
  · exact ⟨7001, 5, prime_7001, prime_5, by norm_num⟩
  · exact ⟨7001, 7, prime_7001, prime_7, by norm_num⟩
  · exact ⟨6997, 13, prime_6997, prime_13, by norm_num⟩
  · exact ⟨7001, 11, prime_7001, prime_11, by norm_num⟩
  · exact ⟨7001, 13, prime_7001, prime_13, by norm_num⟩
  · exact ⟨7013, 3, prime_7013, prime_3, by norm_num⟩
  · exact ⟨7013, 5, prime_7013, prime_5, by norm_num⟩
  · exact ⟨7013, 7, prime_7013, prime_7, by norm_num⟩
  · exact ⟨7019, 3, prime_7019, prime_3, by norm_num⟩
  · exact ⟨7019, 5, prime_7019, prime_5, by norm_num⟩
  · exact ⟨7019, 7, prime_7019, prime_7, by norm_num⟩
  · exact ⟨6997, 31, prime_6997, prime_31, by norm_num⟩
  · exact ⟨7027, 3, prime_7027, prime_3, by norm_num⟩
  · exact ⟨7027, 5, prime_7027, prime_5, by norm_num⟩
  · exact ⟨7027, 7, prime_7027, prime_7, by norm_num⟩
  · exact ⟨7019, 17, prime_7019, prime_17, by norm_num⟩
  · exact ⟨7027, 11, prime_7027, prime_11, by norm_num⟩
  · exact ⟨7027, 13, prime_7027, prime_13, by norm_num⟩
  · exact ⟨7039, 3, prime_7039, prime_3, by norm_num⟩
  · exact ⟨7039, 5, prime_7039, prime_5, by norm_num⟩
  · exact ⟨7043, 3, prime_7043, prime_3, by norm_num⟩
  · exact ⟨7043, 5, prime_7043, prime_5, by norm_num⟩
  · exact ⟨7043, 7, prime_7043, prime_7, by norm_num⟩
  · exact ⟨7039, 13, prime_7039, prime_13, by norm_num⟩
  · exact ⟨7043, 11, prime_7043, prime_11, by norm_num⟩
  · exact ⟨7043, 13, prime_7043, prime_13, by norm_num⟩
  · exact ⟨7039, 19, prime_7039, prime_19, by norm_num⟩
  · exact ⟨7057, 3, prime_7057, prime_3, by norm_num⟩
  · exact ⟨7057, 5, prime_7057, prime_5, by norm_num⟩
  · exact ⟨7057, 7, prime_7057, prime_7, by norm_num⟩
  · exact ⟨7043, 23, prime_7043, prime_23, by norm_num⟩
  · exact ⟨7057, 11, prime_7057, prime_11, by norm_num⟩
  · exact ⟨7057, 13, prime_7057, prime_13, by norm_num⟩
  · exact ⟨7069, 3, prime_7069, prime_3, by norm_num⟩
  · exact ⟨7069, 5, prime_7069, prime_5, by norm_num⟩
  · exact ⟨7069, 7, prime_7069, prime_7, by norm_num⟩
  · exact ⟨7019, 59, prime_7019, prime_59, by norm_num⟩
  · exact ⟨7069, 11, prime_7069, prime_11, by norm_num⟩
  · exact ⟨7079, 3, prime_7079, prime_3, by norm_num⟩
  · exact ⟨7079, 5, prime_7079, prime_5, by norm_num⟩
  · exact ⟨7079, 7, prime_7079, prime_7, by norm_num⟩
  · exact ⟨7069, 19, prime_7069, prime_19, by norm_num⟩
  · exact ⟨7079, 11, prime_7079, prime_11, by norm_num⟩
  · exact ⟨7079, 13, prime_7079, prime_13, by norm_num⟩
  · exact ⟨7057, 37, prime_7057, prime_37, by norm_num⟩
  · exact ⟨7079, 17, prime_7079, prime_17, by norm_num⟩
  · exact ⟨7079, 19, prime_7079, prime_19, by norm_num⟩
  · exact ⟨7069, 31, prime_7069, prime_31, by norm_num⟩
  · exact ⟨7079, 23, prime_7079, prime_23, by norm_num⟩
  · exact ⟨7057, 47, prime_7057, prime_47, by norm_num⟩
  · exact ⟨7103, 3, prime_7103, prime_3, by norm_num⟩
  · exact ⟨7103, 5, prime_7103, prime_5, by norm_num⟩
  · exact ⟨7103, 7, prime_7103, prime_7, by norm_num⟩
  · exact ⟨7109, 3, prime_7109, prime_3, by norm_num⟩
  · exact ⟨7109, 5, prime_7109, prime_5, by norm_num⟩
  · exact ⟨7109, 7, prime_7109, prime_7, by norm_num⟩
  · exact ⟨7057, 61, prime_7057, prime_61, by norm_num⟩
  · exact ⟨7109, 11, prime_7109, prime_11, by norm_num⟩
  · exact ⟨7109, 13, prime_7109, prime_13, by norm_num⟩
  · exact ⟨7121, 3, prime_7121, prime_3, by norm_num⟩
  · exact ⟨7121, 5, prime_7121, prime_5, by norm_num⟩
  · exact ⟨7121, 7, prime_7121, prime_7, by norm_num⟩
  · exact ⟨7127, 3, prime_7127, prime_3, by norm_num⟩
  · exact ⟨7129, 3, prime_7129, prime_3, by norm_num⟩
  · exact ⟨7129, 5, prime_7129, prime_5, by norm_num⟩
  · exact ⟨7129, 7, prime_7129, prime_7, by norm_num⟩
  · exact ⟨7127, 11, prime_7127, prime_11, by norm_num⟩
  · exact ⟨7129, 11, prime_7129, prime_11, by norm_num⟩
  · exact ⟨7129, 13, prime_7129, prime_13, by norm_num⟩
  · exact ⟨7127, 17, prime_7127, prime_17, by norm_num⟩
  · exact ⟨7129, 17, prime_7129, prime_17, by norm_num⟩
  · exact ⟨7129, 19, prime_7129, prime_19, by norm_num⟩
  · exact ⟨7127, 23, prime_7127, prime_23, by norm_num⟩
  · exact ⟨7129, 23, prime_7129, prime_23, by norm_num⟩
  · exact ⟨7151, 3, prime_7151, prime_3, by norm_num⟩
  · exact ⟨7151, 5, prime_7151, prime_5, by norm_num⟩
  · exact ⟨7151, 7, prime_7151, prime_7, by norm_num⟩
  · exact ⟨7129, 31, prime_7129, prime_31, by norm_num⟩
  · exact ⟨7159, 3, prime_7159, prime_3, by norm_num⟩
  · exact ⟨7159, 5, prime_7159, prime_5, by norm_num⟩
  · exact ⟨7159, 7, prime_7159, prime_7, by norm_num⟩
  · exact ⟨7151, 17, prime_7151, prime_17, by norm_num⟩
  · exact ⟨7159, 11, prime_7159, prime_11, by norm_num⟩
  · exact ⟨7159, 13, prime_7159, prime_13, by norm_num⟩
  · exact ⟨7151, 23, prime_7151, prime_23, by norm_num⟩
  · exact ⟨7159, 17, prime_7159, prime_17, by norm_num⟩
  · exact ⟨7159, 19, prime_7159, prime_19, by norm_num⟩
  · exact ⟨7177, 3, prime_7177, prime_3, by norm_num⟩
  · exact ⟨7177, 5, prime_7177, prime_5, by norm_num⟩
  · exact ⟨7177, 7, prime_7177, prime_7, by norm_num⟩
  · exact ⟨7127, 59, prime_7127, prime_59, by norm_num⟩
  · exact ⟨7177, 11, prime_7177, prime_11, by norm_num⟩
  · exact ⟨7187, 3, prime_7187, prime_3, by norm_num⟩
  · exact ⟨7187, 5, prime_7187, prime_5, by norm_num⟩
  · exact ⟨7187, 7, prime_7187, prime_7, by norm_num⟩
  · exact ⟨7193, 3, prime_7193, prime_3, by norm_num⟩
  · exact ⟨7193, 5, prime_7193, prime_5, by norm_num⟩
  · exact ⟨7193, 7, prime_7193, prime_7, by norm_num⟩
  · exact ⟨7159, 43, prime_7159, prime_43, by norm_num⟩

private theorem goldbach_chunk_36 : ∀ k : ℕ, 3602 ≤ k → k ≤ 3701 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7193, 11, prime_7193, prime_11, by norm_num⟩
  · exact ⟨7193, 13, prime_7193, prime_13, by norm_num⟩
  · exact ⟨7177, 31, prime_7177, prime_31, by norm_num⟩
  · exact ⟨7207, 3, prime_7207, prime_3, by norm_num⟩
  · exact ⟨7207, 5, prime_7207, prime_5, by norm_num⟩
  · exact ⟨7211, 3, prime_7211, prime_3, by norm_num⟩
  · exact ⟨7213, 3, prime_7213, prime_3, by norm_num⟩
  · exact ⟨7213, 5, prime_7213, prime_5, by norm_num⟩
  · exact ⟨7213, 7, prime_7213, prime_7, by norm_num⟩
  · exact ⟨7219, 3, prime_7219, prime_3, by norm_num⟩
  · exact ⟨7219, 5, prime_7219, prime_5, by norm_num⟩
  · exact ⟨7219, 7, prime_7219, prime_7, by norm_num⟩
  · exact ⟨7211, 17, prime_7211, prime_17, by norm_num⟩
  · exact ⟨7219, 11, prime_7219, prime_11, by norm_num⟩
  · exact ⟨7229, 3, prime_7229, prime_3, by norm_num⟩
  · exact ⟨7229, 5, prime_7229, prime_5, by norm_num⟩
  · exact ⟨7229, 7, prime_7229, prime_7, by norm_num⟩
  · exact ⟨7219, 19, prime_7219, prime_19, by norm_num⟩
  · exact ⟨7237, 3, prime_7237, prime_3, by norm_num⟩
  · exact ⟨7237, 5, prime_7237, prime_5, by norm_num⟩
  · exact ⟨7237, 7, prime_7237, prime_7, by norm_num⟩
  · exact ⟨7243, 3, prime_7243, prime_3, by norm_num⟩
  · exact ⟨7243, 5, prime_7243, prime_5, by norm_num⟩
  · exact ⟨7247, 3, prime_7247, prime_3, by norm_num⟩
  · exact ⟨7247, 5, prime_7247, prime_5, by norm_num⟩
  · exact ⟨7247, 7, prime_7247, prime_7, by norm_num⟩
  · exact ⟨7253, 3, prime_7253, prime_3, by norm_num⟩
  · exact ⟨7253, 5, prime_7253, prime_5, by norm_num⟩
  · exact ⟨7253, 7, prime_7253, prime_7, by norm_num⟩
  · exact ⟨7243, 19, prime_7243, prime_19, by norm_num⟩
  · exact ⟨7253, 11, prime_7253, prime_11, by norm_num⟩
  · exact ⟨7253, 13, prime_7253, prime_13, by norm_num⟩
  · exact ⟨7237, 31, prime_7237, prime_31, by norm_num⟩
  · exact ⟨7253, 17, prime_7253, prime_17, by norm_num⟩
  · exact ⟨7253, 19, prime_7253, prime_19, by norm_num⟩
  · exact ⟨7243, 31, prime_7243, prime_31, by norm_num⟩
  · exact ⟨7253, 23, prime_7253, prime_23, by norm_num⟩
  · exact ⟨7247, 31, prime_7247, prime_31, by norm_num⟩
  · exact ⟨7243, 37, prime_7243, prime_37, by norm_num⟩
  · exact ⟨7253, 29, prime_7253, prime_29, by norm_num⟩
  · exact ⟨7253, 31, prime_7253, prime_31, by norm_num⟩
  · exact ⟨7283, 3, prime_7283, prime_3, by norm_num⟩
  · exact ⟨7283, 5, prime_7283, prime_5, by norm_num⟩
  · exact ⟨7283, 7, prime_7283, prime_7, by norm_num⟩
  · exact ⟨7219, 73, prime_7219, prime_73, by norm_num⟩
  · exact ⟨7283, 11, prime_7283, prime_11, by norm_num⟩
  · exact ⟨7283, 13, prime_7283, prime_13, by norm_num⟩
  · exact ⟨7237, 61, prime_7237, prime_61, by norm_num⟩
  · exact ⟨7297, 3, prime_7297, prime_3, by norm_num⟩
  · exact ⟨7297, 5, prime_7297, prime_5, by norm_num⟩
  · exact ⟨7297, 7, prime_7297, prime_7, by norm_num⟩
  · exact ⟨7283, 23, prime_7283, prime_23, by norm_num⟩
  · exact ⟨7297, 11, prime_7297, prime_11, by norm_num⟩
  · exact ⟨7307, 3, prime_7307, prime_3, by norm_num⟩
  · exact ⟨7309, 3, prime_7309, prime_3, by norm_num⟩
  · exact ⟨7309, 5, prime_7309, prime_5, by norm_num⟩
  · exact ⟨7309, 7, prime_7309, prime_7, by norm_num⟩
  · exact ⟨7307, 11, prime_7307, prime_11, by norm_num⟩
  · exact ⟨7309, 11, prime_7309, prime_11, by norm_num⟩
  · exact ⟨7309, 13, prime_7309, prime_13, by norm_num⟩
  · exact ⟨7321, 3, prime_7321, prime_3, by norm_num⟩
  · exact ⟨7321, 5, prime_7321, prime_5, by norm_num⟩
  · exact ⟨7321, 7, prime_7321, prime_7, by norm_num⟩
  · exact ⟨7307, 23, prime_7307, prime_23, by norm_num⟩
  · exact ⟨7321, 11, prime_7321, prime_11, by norm_num⟩
  · exact ⟨7331, 3, prime_7331, prime_3, by norm_num⟩
  · exact ⟨7333, 3, prime_7333, prime_3, by norm_num⟩
  · exact ⟨7333, 5, prime_7333, prime_5, by norm_num⟩
  · exact ⟨7333, 7, prime_7333, prime_7, by norm_num⟩
  · exact ⟨7331, 11, prime_7331, prime_11, by norm_num⟩
  · exact ⟨7333, 11, prime_7333, prime_11, by norm_num⟩
  · exact ⟨7333, 13, prime_7333, prime_13, by norm_num⟩
  · exact ⟨7331, 17, prime_7331, prime_17, by norm_num⟩
  · exact ⟨7333, 17, prime_7333, prime_17, by norm_num⟩
  · exact ⟨7349, 3, prime_7349, prime_3, by norm_num⟩
  · exact ⟨7351, 3, prime_7351, prime_3, by norm_num⟩
  · exact ⟨7351, 5, prime_7351, prime_5, by norm_num⟩
  · exact ⟨7351, 7, prime_7351, prime_7, by norm_num⟩
  · exact ⟨7349, 11, prime_7349, prime_11, by norm_num⟩
  · exact ⟨7351, 11, prime_7351, prime_11, by norm_num⟩
  · exact ⟨7351, 13, prime_7351, prime_13, by norm_num⟩
  · exact ⟨7349, 17, prime_7349, prime_17, by norm_num⟩
  · exact ⟨7351, 17, prime_7351, prime_17, by norm_num⟩
  · exact ⟨7351, 19, prime_7351, prime_19, by norm_num⟩
  · exact ⟨7369, 3, prime_7369, prime_3, by norm_num⟩
  · exact ⟨7369, 5, prime_7369, prime_5, by norm_num⟩
  · exact ⟨7369, 7, prime_7369, prime_7, by norm_num⟩
  · exact ⟨7349, 29, prime_7349, prime_29, by norm_num⟩
  · exact ⟨7369, 11, prime_7369, prime_11, by norm_num⟩
  · exact ⟨7369, 13, prime_7369, prime_13, by norm_num⟩
  · exact ⟨7331, 53, prime_7331, prime_53, by norm_num⟩
  · exact ⟨7369, 17, prime_7369, prime_17, by norm_num⟩
  · exact ⟨7369, 19, prime_7369, prime_19, by norm_num⟩
  · exact ⟨7349, 41, prime_7349, prime_41, by norm_num⟩
  · exact ⟨7369, 23, prime_7369, prime_23, by norm_num⟩
  · exact ⟨7351, 43, prime_7351, prime_43, by norm_num⟩
  · exact ⟨7393, 3, prime_7393, prime_3, by norm_num⟩
  · exact ⟨7393, 5, prime_7393, prime_5, by norm_num⟩
  · exact ⟨7393, 7, prime_7393, prime_7, by norm_num⟩
  · exact ⟨7349, 53, prime_7349, prime_53, by norm_num⟩

private theorem goldbach_chunk_37 : ∀ k : ℕ, 3702 ≤ k → k ≤ 3801 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7393, 11, prime_7393, prime_11, by norm_num⟩
  · exact ⟨7393, 13, prime_7393, prime_13, by norm_num⟩
  · exact ⟨7349, 59, prime_7349, prime_59, by norm_num⟩
  · exact ⟨7393, 17, prime_7393, prime_17, by norm_num⟩
  · exact ⟨7393, 19, prime_7393, prime_19, by norm_num⟩
  · exact ⟨7411, 3, prime_7411, prime_3, by norm_num⟩
  · exact ⟨7411, 5, prime_7411, prime_5, by norm_num⟩
  · exact ⟨7411, 7, prime_7411, prime_7, by norm_num⟩
  · exact ⟨7417, 3, prime_7417, prime_3, by norm_num⟩
  · exact ⟨7417, 5, prime_7417, prime_5, by norm_num⟩
  · exact ⟨7417, 7, prime_7417, prime_7, by norm_num⟩
  · exact ⟨7253, 173, prime_7253, prime_173, by norm_num⟩
  · exact ⟨7417, 11, prime_7417, prime_11, by norm_num⟩
  · exact ⟨7417, 13, prime_7417, prime_13, by norm_num⟩
  · exact ⟨7349, 83, prime_7349, prime_83, by norm_num⟩
  · exact ⟨7417, 17, prime_7417, prime_17, by norm_num⟩
  · exact ⟨7433, 3, prime_7433, prime_3, by norm_num⟩
  · exact ⟨7433, 5, prime_7433, prime_5, by norm_num⟩
  · exact ⟨7433, 7, prime_7433, prime_7, by norm_num⟩
  · exact ⟨7411, 31, prime_7411, prime_31, by norm_num⟩
  · exact ⟨7433, 11, prime_7433, prime_11, by norm_num⟩
  · exact ⟨7433, 13, prime_7433, prime_13, by norm_num⟩
  · exact ⟨7417, 31, prime_7417, prime_31, by norm_num⟩
  · exact ⟨7433, 17, prime_7433, prime_17, by norm_num⟩
  · exact ⟨7433, 19, prime_7433, prime_19, by norm_num⟩
  · exact ⟨7451, 3, prime_7451, prime_3, by norm_num⟩
  · exact ⟨7451, 5, prime_7451, prime_5, by norm_num⟩
  · exact ⟨7451, 7, prime_7451, prime_7, by norm_num⟩
  · exact ⟨7457, 3, prime_7457, prime_3, by norm_num⟩
  · exact ⟨7459, 3, prime_7459, prime_3, by norm_num⟩
  · exact ⟨7459, 5, prime_7459, prime_5, by norm_num⟩
  · exact ⟨7459, 7, prime_7459, prime_7, by norm_num⟩
  · exact ⟨7457, 11, prime_7457, prime_11, by norm_num⟩
  · exact ⟨7459, 11, prime_7459, prime_11, by norm_num⟩
  · exact ⟨7459, 13, prime_7459, prime_13, by norm_num⟩
  · exact ⟨7457, 17, prime_7457, prime_17, by norm_num⟩
  · exact ⟨7459, 17, prime_7459, prime_17, by norm_num⟩
  · exact ⟨7459, 19, prime_7459, prime_19, by norm_num⟩
  · exact ⟨7477, 3, prime_7477, prime_3, by norm_num⟩
  · exact ⟨7477, 5, prime_7477, prime_5, by norm_num⟩
  · exact ⟨7481, 3, prime_7481, prime_3, by norm_num⟩
  · exact ⟨7481, 5, prime_7481, prime_5, by norm_num⟩
  · exact ⟨7481, 7, prime_7481, prime_7, by norm_num⟩
  · exact ⟨7487, 3, prime_7487, prime_3, by norm_num⟩
  · exact ⟨7489, 3, prime_7489, prime_3, by norm_num⟩
  · exact ⟨7489, 5, prime_7489, prime_5, by norm_num⟩
  · exact ⟨7489, 7, prime_7489, prime_7, by norm_num⟩
  · exact ⟨7487, 11, prime_7487, prime_11, by norm_num⟩
  · exact ⟨7489, 11, prime_7489, prime_11, by norm_num⟩
  · exact ⟨7499, 3, prime_7499, prime_3, by norm_num⟩
  · exact ⟨7499, 5, prime_7499, prime_5, by norm_num⟩
  · exact ⟨7499, 7, prime_7499, prime_7, by norm_num⟩
  · exact ⟨7489, 19, prime_7489, prime_19, by norm_num⟩
  · exact ⟨7507, 3, prime_7507, prime_3, by norm_num⟩
  · exact ⟨7507, 5, prime_7507, prime_5, by norm_num⟩
  · exact ⟨7507, 7, prime_7507, prime_7, by norm_num⟩
  · exact ⟨7499, 17, prime_7499, prime_17, by norm_num⟩
  · exact ⟨7507, 11, prime_7507, prime_11, by norm_num⟩
  · exact ⟨7517, 3, prime_7517, prime_3, by norm_num⟩
  · exact ⟨7517, 5, prime_7517, prime_5, by norm_num⟩
  · exact ⟨7517, 7, prime_7517, prime_7, by norm_num⟩
  · exact ⟨7523, 3, prime_7523, prime_3, by norm_num⟩
  · exact ⟨7523, 5, prime_7523, prime_5, by norm_num⟩
  · exact ⟨7523, 7, prime_7523, prime_7, by norm_num⟩
  · exact ⟨7529, 3, prime_7529, prime_3, by norm_num⟩
  · exact ⟨7529, 5, prime_7529, prime_5, by norm_num⟩
  · exact ⟨7529, 7, prime_7529, prime_7, by norm_num⟩
  · exact ⟨7507, 31, prime_7507, prime_31, by norm_num⟩
  · exact ⟨7537, 3, prime_7537, prime_3, by norm_num⟩
  · exact ⟨7537, 5, prime_7537, prime_5, by norm_num⟩
  · exact ⟨7541, 3, prime_7541, prime_3, by norm_num⟩
  · exact ⟨7541, 5, prime_7541, prime_5, by norm_num⟩
  · exact ⟨7541, 7, prime_7541, prime_7, by norm_num⟩
  · exact ⟨7547, 3, prime_7547, prime_3, by norm_num⟩
  · exact ⟨7549, 3, prime_7549, prime_3, by norm_num⟩
  · exact ⟨7549, 5, prime_7549, prime_5, by norm_num⟩
  · exact ⟨7549, 7, prime_7549, prime_7, by norm_num⟩
  · exact ⟨7547, 11, prime_7547, prime_11, by norm_num⟩
  · exact ⟨7549, 11, prime_7549, prime_11, by norm_num⟩
  · exact ⟨7559, 3, prime_7559, prime_3, by norm_num⟩
  · exact ⟨7561, 3, prime_7561, prime_3, by norm_num⟩
  · exact ⟨7561, 5, prime_7561, prime_5, by norm_num⟩
  · exact ⟨7561, 7, prime_7561, prime_7, by norm_num⟩
  · exact ⟨7559, 11, prime_7559, prime_11, by norm_num⟩
  · exact ⟨7561, 11, prime_7561, prime_11, by norm_num⟩
  · exact ⟨7561, 13, prime_7561, prime_13, by norm_num⟩
  · exact ⟨7573, 3, prime_7573, prime_3, by norm_num⟩
  · exact ⟨7573, 5, prime_7573, prime_5, by norm_num⟩
  · exact ⟨7577, 3, prime_7577, prime_3, by norm_num⟩
  · exact ⟨7577, 5, prime_7577, prime_5, by norm_num⟩
  · exact ⟨7577, 7, prime_7577, prime_7, by norm_num⟩
  · exact ⟨7583, 3, prime_7583, prime_3, by norm_num⟩
  · exact ⟨7583, 5, prime_7583, prime_5, by norm_num⟩
  · exact ⟨7583, 7, prime_7583, prime_7, by norm_num⟩
  · exact ⟨7589, 3, prime_7589, prime_3, by norm_num⟩
  · exact ⟨7591, 3, prime_7591, prime_3, by norm_num⟩
  · exact ⟨7591, 5, prime_7591, prime_5, by norm_num⟩
  · exact ⟨7591, 7, prime_7591, prime_7, by norm_num⟩
  · exact ⟨7589, 11, prime_7589, prime_11, by norm_num⟩
  · exact ⟨7591, 11, prime_7591, prime_11, by norm_num⟩

private theorem goldbach_chunk_38 : ∀ k : ℕ, 3802 ≤ k → k ≤ 3901 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7591, 13, prime_7591, prime_13, by norm_num⟩
  · exact ⟨7603, 3, prime_7603, prime_3, by norm_num⟩
  · exact ⟨7603, 5, prime_7603, prime_5, by norm_num⟩
  · exact ⟨7607, 3, prime_7607, prime_3, by norm_num⟩
  · exact ⟨7607, 5, prime_7607, prime_5, by norm_num⟩
  · exact ⟨7607, 7, prime_7607, prime_7, by norm_num⟩
  · exact ⟨7603, 13, prime_7603, prime_13, by norm_num⟩
  · exact ⟨7607, 11, prime_7607, prime_11, by norm_num⟩
  · exact ⟨7607, 13, prime_7607, prime_13, by norm_num⟩
  · exact ⟨7603, 19, prime_7603, prime_19, by norm_num⟩
  · exact ⟨7621, 3, prime_7621, prime_3, by norm_num⟩
  · exact ⟨7621, 5, prime_7621, prime_5, by norm_num⟩
  · exact ⟨7621, 7, prime_7621, prime_7, by norm_num⟩
  · exact ⟨7607, 23, prime_7607, prime_23, by norm_num⟩
  · exact ⟨7621, 11, prime_7621, prime_11, by norm_num⟩
  · exact ⟨7621, 13, prime_7621, prime_13, by norm_num⟩
  · exact ⟨7607, 29, prime_7607, prime_29, by norm_num⟩
  · exact ⟨7621, 17, prime_7621, prime_17, by norm_num⟩
  · exact ⟨7621, 19, prime_7621, prime_19, by norm_num⟩
  · exact ⟨7639, 3, prime_7639, prime_3, by norm_num⟩
  · exact ⟨7639, 5, prime_7639, prime_5, by norm_num⟩
  · exact ⟨7643, 3, prime_7643, prime_3, by norm_num⟩
  · exact ⟨7643, 5, prime_7643, prime_5, by norm_num⟩
  · exact ⟨7643, 7, prime_7643, prime_7, by norm_num⟩
  · exact ⟨7649, 3, prime_7649, prime_3, by norm_num⟩
  · exact ⟨7649, 5, prime_7649, prime_5, by norm_num⟩
  · exact ⟨7649, 7, prime_7649, prime_7, by norm_num⟩
  · exact ⟨7639, 19, prime_7639, prime_19, by norm_num⟩
  · exact ⟨7649, 11, prime_7649, prime_11, by norm_num⟩
  · exact ⟨7649, 13, prime_7649, prime_13, by norm_num⟩
  · exact ⟨7621, 43, prime_7621, prime_43, by norm_num⟩
  · exact ⟨7649, 17, prime_7649, prime_17, by norm_num⟩
  · exact ⟨7649, 19, prime_7649, prime_19, by norm_num⟩
  · exact ⟨7639, 31, prime_7639, prime_31, by norm_num⟩
  · exact ⟨7669, 3, prime_7669, prime_3, by norm_num⟩
  · exact ⟨7669, 5, prime_7669, prime_5, by norm_num⟩
  · exact ⟨7673, 3, prime_7673, prime_3, by norm_num⟩
  · exact ⟨7673, 5, prime_7673, prime_5, by norm_num⟩
  · exact ⟨7673, 7, prime_7673, prime_7, by norm_num⟩
  · exact ⟨7669, 13, prime_7669, prime_13, by norm_num⟩
  · exact ⟨7681, 3, prime_7681, prime_3, by norm_num⟩
  · exact ⟨7681, 5, prime_7681, prime_5, by norm_num⟩
  · exact ⟨7681, 7, prime_7681, prime_7, by norm_num⟩
  · exact ⟨7687, 3, prime_7687, prime_3, by norm_num⟩
  · exact ⟨7687, 5, prime_7687, prime_5, by norm_num⟩
  · exact ⟨7691, 3, prime_7691, prime_3, by norm_num⟩
  · exact ⟨7691, 5, prime_7691, prime_5, by norm_num⟩
  · exact ⟨7691, 7, prime_7691, prime_7, by norm_num⟩
  · exact ⟨7687, 13, prime_7687, prime_13, by norm_num⟩
  · exact ⟨7699, 3, prime_7699, prime_3, by norm_num⟩
  · exact ⟨7699, 5, prime_7699, prime_5, by norm_num⟩
  · exact ⟨7703, 3, prime_7703, prime_3, by norm_num⟩
  · exact ⟨7703, 5, prime_7703, prime_5, by norm_num⟩
  · exact ⟨7703, 7, prime_7703, prime_7, by norm_num⟩
  · exact ⟨7699, 13, prime_7699, prime_13, by norm_num⟩
  · exact ⟨7703, 11, prime_7703, prime_11, by norm_num⟩
  · exact ⟨7703, 13, prime_7703, prime_13, by norm_num⟩
  · exact ⟨7699, 19, prime_7699, prime_19, by norm_num⟩
  · exact ⟨7717, 3, prime_7717, prime_3, by norm_num⟩
  · exact ⟨7717, 5, prime_7717, prime_5, by norm_num⟩
  · exact ⟨7717, 7, prime_7717, prime_7, by norm_num⟩
  · exact ⟨7723, 3, prime_7723, prime_3, by norm_num⟩
  · exact ⟨7723, 5, prime_7723, prime_5, by norm_num⟩
  · exact ⟨7727, 3, prime_7727, prime_3, by norm_num⟩
  · exact ⟨7727, 5, prime_7727, prime_5, by norm_num⟩
  · exact ⟨7727, 7, prime_7727, prime_7, by norm_num⟩
  · exact ⟨7723, 13, prime_7723, prime_13, by norm_num⟩
  · exact ⟨7727, 11, prime_7727, prime_11, by norm_num⟩
  · exact ⟨7727, 13, prime_7727, prime_13, by norm_num⟩
  · exact ⟨7723, 19, prime_7723, prime_19, by norm_num⟩
  · exact ⟨7741, 3, prime_7741, prime_3, by norm_num⟩
  · exact ⟨7741, 5, prime_7741, prime_5, by norm_num⟩
  · exact ⟨7741, 7, prime_7741, prime_7, by norm_num⟩
  · exact ⟨7727, 23, prime_7727, prime_23, by norm_num⟩
  · exact ⟨7741, 11, prime_7741, prime_11, by norm_num⟩
  · exact ⟨7741, 13, prime_7741, prime_13, by norm_num⟩
  · exact ⟨7753, 3, prime_7753, prime_3, by norm_num⟩
  · exact ⟨7753, 5, prime_7753, prime_5, by norm_num⟩
  · exact ⟨7757, 3, prime_7757, prime_3, by norm_num⟩
  · exact ⟨7759, 3, prime_7759, prime_3, by norm_num⟩
  · exact ⟨7759, 5, prime_7759, prime_5, by norm_num⟩
  · exact ⟨7759, 7, prime_7759, prime_7, by norm_num⟩
  · exact ⟨7757, 11, prime_7757, prime_11, by norm_num⟩
  · exact ⟨7759, 11, prime_7759, prime_11, by norm_num⟩
  · exact ⟨7759, 13, prime_7759, prime_13, by norm_num⟩
  · exact ⟨7757, 17, prime_7757, prime_17, by norm_num⟩
  · exact ⟨7759, 17, prime_7759, prime_17, by norm_num⟩
  · exact ⟨7759, 19, prime_7759, prime_19, by norm_num⟩
  · exact ⟨7757, 23, prime_7757, prime_23, by norm_num⟩
  · exact ⟨7759, 23, prime_7759, prime_23, by norm_num⟩
  · exact ⟨7753, 31, prime_7753, prime_31, by norm_num⟩
  · exact ⟨7757, 29, prime_7757, prime_29, by norm_num⟩
  · exact ⟨7759, 29, prime_7759, prime_29, by norm_num⟩
  · exact ⟨7759, 31, prime_7759, prime_31, by norm_num⟩
  · exact ⟨7789, 3, prime_7789, prime_3, by norm_num⟩
  · exact ⟨7789, 5, prime_7789, prime_5, by norm_num⟩
  · exact ⟨7793, 3, prime_7793, prime_3, by norm_num⟩
  · exact ⟨7793, 5, prime_7793, prime_5, by norm_num⟩
  · exact ⟨7793, 7, prime_7793, prime_7, by norm_num⟩
  · exact ⟨7789, 13, prime_7789, prime_13, by norm_num⟩

private theorem goldbach_chunk_39 : ∀ k : ℕ, 3902 ≤ k → k ≤ 4001 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7793, 11, prime_7793, prime_11, by norm_num⟩
  · exact ⟨7793, 13, prime_7793, prime_13, by norm_num⟩
  · exact ⟨7789, 19, prime_7789, prime_19, by norm_num⟩
  · exact ⟨7793, 17, prime_7793, prime_17, by norm_num⟩
  · exact ⟨7793, 19, prime_7793, prime_19, by norm_num⟩
  · exact ⟨7753, 61, prime_7753, prime_61, by norm_num⟩
  · exact ⟨7793, 23, prime_7793, prime_23, by norm_num⟩
  · exact ⟨7789, 29, prime_7789, prime_29, by norm_num⟩
  · exact ⟨7817, 3, prime_7817, prime_3, by norm_num⟩
  · exact ⟨7817, 5, prime_7817, prime_5, by norm_num⟩
  · exact ⟨7817, 7, prime_7817, prime_7, by norm_num⟩
  · exact ⟨7823, 3, prime_7823, prime_3, by norm_num⟩
  · exact ⟨7823, 5, prime_7823, prime_5, by norm_num⟩
  · exact ⟨7823, 7, prime_7823, prime_7, by norm_num⟩
  · exact ⟨7829, 3, prime_7829, prime_3, by norm_num⟩
  · exact ⟨7829, 5, prime_7829, prime_5, by norm_num⟩
  · exact ⟨7829, 7, prime_7829, prime_7, by norm_num⟩
  · exact ⟨7759, 79, prime_7759, prime_79, by norm_num⟩
  · exact ⟨7829, 11, prime_7829, prime_11, by norm_num⟩
  · exact ⟨7829, 13, prime_7829, prime_13, by norm_num⟩
  · exact ⟨7841, 3, prime_7841, prime_3, by norm_num⟩
  · exact ⟨7841, 5, prime_7841, prime_5, by norm_num⟩
  · exact ⟨7841, 7, prime_7841, prime_7, by norm_num⟩
  · exact ⟨7789, 61, prime_7789, prime_61, by norm_num⟩
  · exact ⟨7841, 11, prime_7841, prime_11, by norm_num⟩
  · exact ⟨7841, 13, prime_7841, prime_13, by norm_num⟩
  · exact ⟨7853, 3, prime_7853, prime_3, by norm_num⟩
  · exact ⟨7853, 5, prime_7853, prime_5, by norm_num⟩
  · exact ⟨7853, 7, prime_7853, prime_7, by norm_num⟩
  · exact ⟨7789, 73, prime_7789, prime_73, by norm_num⟩
  · exact ⟨7853, 11, prime_7853, prime_11, by norm_num⟩
  · exact ⟨7853, 13, prime_7853, prime_13, by norm_num⟩
  · exact ⟨7789, 79, prime_7789, prime_79, by norm_num⟩
  · exact ⟨7867, 3, prime_7867, prime_3, by norm_num⟩
  · exact ⟨7867, 5, prime_7867, prime_5, by norm_num⟩
  · exact ⟨7867, 7, prime_7867, prime_7, by norm_num⟩
  · exact ⟨7873, 3, prime_7873, prime_3, by norm_num⟩
  · exact ⟨7873, 5, prime_7873, prime_5, by norm_num⟩
  · exact ⟨7877, 3, prime_7877, prime_3, by norm_num⟩
  · exact ⟨7879, 3, prime_7879, prime_3, by norm_num⟩
  · exact ⟨7879, 5, prime_7879, prime_5, by norm_num⟩
  · exact ⟨7883, 3, prime_7883, prime_3, by norm_num⟩
  · exact ⟨7883, 5, prime_7883, prime_5, by norm_num⟩
  · exact ⟨7883, 7, prime_7883, prime_7, by norm_num⟩
  · exact ⟨7879, 13, prime_7879, prime_13, by norm_num⟩
  · exact ⟨7883, 11, prime_7883, prime_11, by norm_num⟩
  · exact ⟨7883, 13, prime_7883, prime_13, by norm_num⟩
  · exact ⟨7879, 19, prime_7879, prime_19, by norm_num⟩
  · exact ⟨7883, 17, prime_7883, prime_17, by norm_num⟩
  · exact ⟨7883, 19, prime_7883, prime_19, by norm_num⟩
  · exact ⟨7901, 3, prime_7901, prime_3, by norm_num⟩
  · exact ⟨7901, 5, prime_7901, prime_5, by norm_num⟩
  · exact ⟨7901, 7, prime_7901, prime_7, by norm_num⟩
  · exact ⟨7907, 3, prime_7907, prime_3, by norm_num⟩
  · exact ⟨7907, 5, prime_7907, prime_5, by norm_num⟩
  · exact ⟨7907, 7, prime_7907, prime_7, by norm_num⟩
  · exact ⟨7879, 37, prime_7879, prime_37, by norm_num⟩
  · exact ⟨7907, 11, prime_7907, prime_11, by norm_num⟩
  · exact ⟨7907, 13, prime_7907, prime_13, by norm_num⟩
  · exact ⟨7919, 3, prime_7919, prime_3, by norm_num⟩
  · exact ⟨7919, 5, prime_7919, prime_5, by norm_num⟩
  · exact ⟨7919, 7, prime_7919, prime_7, by norm_num⟩
  · exact ⟨7867, 61, prime_7867, prime_61, by norm_num⟩
  · exact ⟨7927, 3, prime_7927, prime_3, by norm_num⟩
  · exact ⟨7927, 5, prime_7927, prime_5, by norm_num⟩
  · exact ⟨7927, 7, prime_7927, prime_7, by norm_num⟩
  · exact ⟨7933, 3, prime_7933, prime_3, by norm_num⟩
  · exact ⟨7933, 5, prime_7933, prime_5, by norm_num⟩
  · exact ⟨7937, 3, prime_7937, prime_3, by norm_num⟩
  · exact ⟨7937, 5, prime_7937, prime_5, by norm_num⟩
  · exact ⟨7937, 7, prime_7937, prime_7, by norm_num⟩
  · exact ⟨7933, 13, prime_7933, prime_13, by norm_num⟩
  · exact ⟨7937, 11, prime_7937, prime_11, by norm_num⟩
  · exact ⟨7937, 13, prime_7937, prime_13, by norm_num⟩
  · exact ⟨7949, 3, prime_7949, prime_3, by norm_num⟩
  · exact ⟨7951, 3, prime_7951, prime_3, by norm_num⟩
  · exact ⟨7951, 5, prime_7951, prime_5, by norm_num⟩
  · exact ⟨7951, 7, prime_7951, prime_7, by norm_num⟩
  · exact ⟨7949, 11, prime_7949, prime_11, by norm_num⟩
  · exact ⟨7951, 11, prime_7951, prime_11, by norm_num⟩
  · exact ⟨7951, 13, prime_7951, prime_13, by norm_num⟩
  · exact ⟨7963, 3, prime_7963, prime_3, by norm_num⟩
  · exact ⟨7963, 5, prime_7963, prime_5, by norm_num⟩
  · exact ⟨7963, 7, prime_7963, prime_7, by norm_num⟩
  · exact ⟨7949, 23, prime_7949, prime_23, by norm_num⟩
  · exact ⟨7963, 11, prime_7963, prime_11, by norm_num⟩
  · exact ⟨7963, 13, prime_7963, prime_13, by norm_num⟩
  · exact ⟨7949, 29, prime_7949, prime_29, by norm_num⟩
  · exact ⟨7963, 17, prime_7963, prime_17, by norm_num⟩
  · exact ⟨7963, 19, prime_7963, prime_19, by norm_num⟩
  · exact ⟨7937, 47, prime_7937, prime_47, by norm_num⟩
  · exact ⟨7963, 23, prime_7963, prime_23, by norm_num⟩
  · exact ⟨7951, 37, prime_7951, prime_37, by norm_num⟩
  · exact ⟨7949, 41, prime_7949, prime_41, by norm_num⟩
  · exact ⟨7963, 29, prime_7963, prime_29, by norm_num⟩
  · exact ⟨7963, 31, prime_7963, prime_31, by norm_num⟩
  · exact ⟨7993, 3, prime_7993, prime_3, by norm_num⟩
  · exact ⟨7993, 5, prime_7993, prime_5, by norm_num⟩
  · exact ⟨7993, 7, prime_7993, prime_7, by norm_num⟩
  · exact ⟨7949, 53, prime_7949, prime_53, by norm_num⟩

private theorem goldbach_chunk_40 : ∀ k : ℕ, 4002 ≤ k → k ≤ 4006 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k + k = p + q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7993, 11, prime_7993, prime_11, by norm_num⟩
  · exact ⟨7993, 13, prime_7993, prime_13, by norm_num⟩
  · exact ⟨7949, 59, prime_7949, prime_59, by norm_num⟩
  · exact ⟨7993, 17, prime_7993, prime_17, by norm_num⟩
  · exact ⟨8009, 3, prime_8009, prime_3, by norm_num⟩

private theorem goldbach_small : ∀ n : ℕ, 4 ≤ n → n ≤ 8012 → Even n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  intro n hn4 hnle hEven
  rcases hEven with ⟨k, hk⟩
  subst n
  have hklo : 2 ≤ k := by omega
  have hkle : k ≤ 4006 := by omega
  by_cases h0 : k ≤ 101
  · exact goldbach_chunk_0 k (by omega) h0
  by_cases h1 : k ≤ 201
  · exact goldbach_chunk_1 k (by omega) h1
  by_cases h2 : k ≤ 301
  · exact goldbach_chunk_2 k (by omega) h2
  by_cases h3 : k ≤ 401
  · exact goldbach_chunk_3 k (by omega) h3
  by_cases h4 : k ≤ 501
  · exact goldbach_chunk_4 k (by omega) h4
  by_cases h5 : k ≤ 601
  · exact goldbach_chunk_5 k (by omega) h5
  by_cases h6 : k ≤ 701
  · exact goldbach_chunk_6 k (by omega) h6
  by_cases h7 : k ≤ 801
  · exact goldbach_chunk_7 k (by omega) h7
  by_cases h8 : k ≤ 901
  · exact goldbach_chunk_8 k (by omega) h8
  by_cases h9 : k ≤ 1001
  · exact goldbach_chunk_9 k (by omega) h9
  by_cases h10 : k ≤ 1101
  · exact goldbach_chunk_10 k (by omega) h10
  by_cases h11 : k ≤ 1201
  · exact goldbach_chunk_11 k (by omega) h11
  by_cases h12 : k ≤ 1301
  · exact goldbach_chunk_12 k (by omega) h12
  by_cases h13 : k ≤ 1401
  · exact goldbach_chunk_13 k (by omega) h13
  by_cases h14 : k ≤ 1501
  · exact goldbach_chunk_14 k (by omega) h14
  by_cases h15 : k ≤ 1601
  · exact goldbach_chunk_15 k (by omega) h15
  by_cases h16 : k ≤ 1701
  · exact goldbach_chunk_16 k (by omega) h16
  by_cases h17 : k ≤ 1801
  · exact goldbach_chunk_17 k (by omega) h17
  by_cases h18 : k ≤ 1901
  · exact goldbach_chunk_18 k (by omega) h18
  by_cases h19 : k ≤ 2001
  · exact goldbach_chunk_19 k (by omega) h19
  by_cases h20 : k ≤ 2101
  · exact goldbach_chunk_20 k (by omega) h20
  by_cases h21 : k ≤ 2201
  · exact goldbach_chunk_21 k (by omega) h21
  by_cases h22 : k ≤ 2301
  · exact goldbach_chunk_22 k (by omega) h22
  by_cases h23 : k ≤ 2401
  · exact goldbach_chunk_23 k (by omega) h23
  by_cases h24 : k ≤ 2501
  · exact goldbach_chunk_24 k (by omega) h24
  by_cases h25 : k ≤ 2601
  · exact goldbach_chunk_25 k (by omega) h25
  by_cases h26 : k ≤ 2701
  · exact goldbach_chunk_26 k (by omega) h26
  by_cases h27 : k ≤ 2801
  · exact goldbach_chunk_27 k (by omega) h27
  by_cases h28 : k ≤ 2901
  · exact goldbach_chunk_28 k (by omega) h28
  by_cases h29 : k ≤ 3001
  · exact goldbach_chunk_29 k (by omega) h29
  by_cases h30 : k ≤ 3101
  · exact goldbach_chunk_30 k (by omega) h30
  by_cases h31 : k ≤ 3201
  · exact goldbach_chunk_31 k (by omega) h31
  by_cases h32 : k ≤ 3301
  · exact goldbach_chunk_32 k (by omega) h32
  by_cases h33 : k ≤ 3401
  · exact goldbach_chunk_33 k (by omega) h33
  by_cases h34 : k ≤ 3501
  · exact goldbach_chunk_34 k (by omega) h34
  by_cases h35 : k ≤ 3601
  · exact goldbach_chunk_35 k (by omega) h35
  by_cases h36 : k ≤ 3701
  · exact goldbach_chunk_36 k (by omega) h36
  by_cases h37 : k ≤ 3801
  · exact goldbach_chunk_37 k (by omega) h37
  by_cases h38 : k ≤ 3901
  · exact goldbach_chunk_38 k (by omega) h38
  by_cases h39 : k ≤ 4001
  · exact goldbach_chunk_39 k (by omega) h39
  · exact goldbach_chunk_40 k (by omega) (by omega)

private theorem lemoine_chunk_0 : ∀ k : ℕ, 3 ≤ k → k ≤ 102 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3, 2, prime_3, prime_2, by norm_num⟩
  · exact ⟨5, 2, prime_5, prime_2, by norm_num⟩
  · exact ⟨7, 2, prime_7, prime_2, by norm_num⟩
  · exact ⟨7, 3, prime_7, prime_3, by norm_num⟩
  · exact ⟨11, 2, prime_11, prime_2, by norm_num⟩
  · exact ⟨13, 2, prime_13, prime_2, by norm_num⟩
  · exact ⟨13, 3, prime_13, prime_3, by norm_num⟩
  · exact ⟨17, 2, prime_17, prime_2, by norm_num⟩
  · exact ⟨19, 2, prime_19, prime_2, by norm_num⟩
  · exact ⟨19, 3, prime_19, prime_3, by norm_num⟩
  · exact ⟨23, 2, prime_23, prime_2, by norm_num⟩
  · exact ⟨23, 3, prime_23, prime_3, by norm_num⟩
  · exact ⟨17, 7, prime_17, prime_7, by norm_num⟩
  · exact ⟨29, 2, prime_29, prime_2, by norm_num⟩
  · exact ⟨31, 2, prime_31, prime_2, by norm_num⟩
  · exact ⟨31, 3, prime_31, prime_3, by norm_num⟩
  · exact ⟨29, 5, prime_29, prime_5, by norm_num⟩
  · exact ⟨37, 2, prime_37, prime_2, by norm_num⟩
  · exact ⟨37, 3, prime_37, prime_3, by norm_num⟩
  · exact ⟨41, 2, prime_41, prime_2, by norm_num⟩
  · exact ⟨43, 2, prime_43, prime_2, by norm_num⟩
  · exact ⟨43, 3, prime_43, prime_3, by norm_num⟩
  · exact ⟨47, 2, prime_47, prime_2, by norm_num⟩
  · exact ⟨47, 3, prime_47, prime_3, by norm_num⟩
  · exact ⟨41, 7, prime_41, prime_7, by norm_num⟩
  · exact ⟨53, 2, prime_53, prime_2, by norm_num⟩
  · exact ⟨53, 3, prime_53, prime_3, by norm_num⟩
  · exact ⟨47, 7, prime_47, prime_7, by norm_num⟩
  · exact ⟨59, 2, prime_59, prime_2, by norm_num⟩
  · exact ⟨61, 2, prime_61, prime_2, by norm_num⟩
  · exact ⟨61, 3, prime_61, prime_3, by norm_num⟩
  · exact ⟨59, 5, prime_59, prime_5, by norm_num⟩
  · exact ⟨67, 2, prime_67, prime_2, by norm_num⟩
  · exact ⟨67, 3, prime_67, prime_3, by norm_num⟩
  · exact ⟨71, 2, prime_71, prime_2, by norm_num⟩
  · exact ⟨73, 2, prime_73, prime_2, by norm_num⟩
  · exact ⟨73, 3, prime_73, prime_3, by norm_num⟩
  · exact ⟨71, 5, prime_71, prime_5, by norm_num⟩
  · exact ⟨79, 2, prime_79, prime_2, by norm_num⟩
  · exact ⟨79, 3, prime_79, prime_3, by norm_num⟩
  · exact ⟨83, 2, prime_83, prime_2, by norm_num⟩
  · exact ⟨83, 3, prime_83, prime_3, by norm_num⟩
  · exact ⟨53, 19, prime_53, prime_19, by norm_num⟩
  · exact ⟨89, 2, prime_89, prime_2, by norm_num⟩
  · exact ⟨89, 3, prime_89, prime_3, by norm_num⟩
  · exact ⟨83, 7, prime_83, prime_7, by norm_num⟩
  · exact ⟨89, 5, prime_89, prime_5, by norm_num⟩
  · exact ⟨97, 2, prime_97, prime_2, by norm_num⟩
  · exact ⟨97, 3, prime_97, prime_3, by norm_num⟩
  · exact ⟨101, 2, prime_101, prime_2, by norm_num⟩
  · exact ⟨103, 2, prime_103, prime_2, by norm_num⟩
  · exact ⟨103, 3, prime_103, prime_3, by norm_num⟩
  · exact ⟨107, 2, prime_107, prime_2, by norm_num⟩
  · exact ⟨109, 2, prime_109, prime_2, by norm_num⟩
  · exact ⟨109, 3, prime_109, prime_3, by norm_num⟩
  · exact ⟨113, 2, prime_113, prime_2, by norm_num⟩
  · exact ⟨113, 3, prime_113, prime_3, by norm_num⟩
  · exact ⟨107, 7, prime_107, prime_7, by norm_num⟩
  · exact ⟨113, 5, prime_113, prime_5, by norm_num⟩
  · exact ⟨103, 11, prime_103, prime_11, by norm_num⟩
  · exact ⟨113, 7, prime_113, prime_7, by norm_num⟩
  · exact ⟨107, 11, prime_107, prime_11, by norm_num⟩
  · exact ⟨127, 2, prime_127, prime_2, by norm_num⟩
  · exact ⟨127, 3, prime_127, prime_3, by norm_num⟩
  · exact ⟨131, 2, prime_131, prime_2, by norm_num⟩
  · exact ⟨131, 3, prime_131, prime_3, by norm_num⟩
  · exact ⟨113, 13, prime_113, prime_13, by norm_num⟩
  · exact ⟨137, 2, prime_137, prime_2, by norm_num⟩
  · exact ⟨139, 2, prime_139, prime_2, by norm_num⟩
  · exact ⟨139, 3, prime_139, prime_3, by norm_num⟩
  · exact ⟨137, 5, prime_137, prime_5, by norm_num⟩
  · exact ⟨139, 5, prime_139, prime_5, by norm_num⟩
  · exact ⟨137, 7, prime_137, prime_7, by norm_num⟩
  · exact ⟨149, 2, prime_149, prime_2, by norm_num⟩
  · exact ⟨151, 2, prime_151, prime_2, by norm_num⟩
  · exact ⟨151, 3, prime_151, prime_3, by norm_num⟩
  · exact ⟨149, 5, prime_149, prime_5, by norm_num⟩
  · exact ⟨157, 2, prime_157, prime_2, by norm_num⟩
  · exact ⟨157, 3, prime_157, prime_3, by norm_num⟩
  · exact ⟨151, 7, prime_151, prime_7, by norm_num⟩
  · exact ⟨163, 2, prime_163, prime_2, by norm_num⟩
  · exact ⟨163, 3, prime_163, prime_3, by norm_num⟩
  · exact ⟨167, 2, prime_167, prime_2, by norm_num⟩
  · exact ⟨167, 3, prime_167, prime_3, by norm_num⟩
  · exact ⟨149, 13, prime_149, prime_13, by norm_num⟩
  · exact ⟨173, 2, prime_173, prime_2, by norm_num⟩
  · exact ⟨173, 3, prime_173, prime_3, by norm_num⟩
  · exact ⟨167, 7, prime_167, prime_7, by norm_num⟩
  · exact ⟨179, 2, prime_179, prime_2, by norm_num⟩
  · exact ⟨181, 2, prime_181, prime_2, by norm_num⟩
  · exact ⟨181, 3, prime_181, prime_3, by norm_num⟩
  · exact ⟨179, 5, prime_179, prime_5, by norm_num⟩
  · exact ⟨181, 5, prime_181, prime_5, by norm_num⟩
  · exact ⟨179, 7, prime_179, prime_7, by norm_num⟩
  · exact ⟨191, 2, prime_191, prime_2, by norm_num⟩
  · exact ⟨193, 2, prime_193, prime_2, by norm_num⟩
  · exact ⟨193, 3, prime_193, prime_3, by norm_num⟩
  · exact ⟨197, 2, prime_197, prime_2, by norm_num⟩
  · exact ⟨199, 2, prime_199, prime_2, by norm_num⟩
  · exact ⟨199, 3, prime_199, prime_3, by norm_num⟩

private theorem lemoine_chunk_1 : ∀ k : ℕ, 103 ≤ k → k ≤ 202 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨197, 5, prime_197, prime_5, by norm_num⟩
  · exact ⟨199, 5, prime_199, prime_5, by norm_num⟩
  · exact ⟨197, 7, prime_197, prime_7, by norm_num⟩
  · exact ⟨199, 7, prime_199, prime_7, by norm_num⟩
  · exact ⟨211, 2, prime_211, prime_2, by norm_num⟩
  · exact ⟨211, 3, prime_211, prime_3, by norm_num⟩
  · exact ⟨197, 11, prime_197, prime_11, by norm_num⟩
  · exact ⟨211, 5, prime_211, prime_5, by norm_num⟩
  · exact ⟨197, 13, prime_197, prime_13, by norm_num⟩
  · exact ⟨211, 7, prime_211, prime_7, by norm_num⟩
  · exact ⟨223, 2, prime_223, prime_2, by norm_num⟩
  · exact ⟨223, 3, prime_223, prime_3, by norm_num⟩
  · exact ⟨227, 2, prime_227, prime_2, by norm_num⟩
  · exact ⟨229, 2, prime_229, prime_2, by norm_num⟩
  · exact ⟨229, 3, prime_229, prime_3, by norm_num⟩
  · exact ⟨233, 2, prime_233, prime_2, by norm_num⟩
  · exact ⟨233, 3, prime_233, prime_3, by norm_num⟩
  · exact ⟨227, 7, prime_227, prime_7, by norm_num⟩
  · exact ⟨239, 2, prime_239, prime_2, by norm_num⟩
  · exact ⟨241, 2, prime_241, prime_2, by norm_num⟩
  · exact ⟨241, 3, prime_241, prime_3, by norm_num⟩
  · exact ⟨239, 5, prime_239, prime_5, by norm_num⟩
  · exact ⟨241, 5, prime_241, prime_5, by norm_num⟩
  · exact ⟨239, 7, prime_239, prime_7, by norm_num⟩
  · exact ⟨251, 2, prime_251, prime_2, by norm_num⟩
  · exact ⟨251, 3, prime_251, prime_3, by norm_num⟩
  · exact ⟨233, 13, prime_233, prime_13, by norm_num⟩
  · exact ⟨257, 2, prime_257, prime_2, by norm_num⟩
  · exact ⟨257, 3, prime_257, prime_3, by norm_num⟩
  · exact ⟨251, 7, prime_251, prime_7, by norm_num⟩
  · exact ⟨263, 2, prime_263, prime_2, by norm_num⟩
  · exact ⟨263, 3, prime_263, prime_3, by norm_num⟩
  · exact ⟨257, 7, prime_257, prime_7, by norm_num⟩
  · exact ⟨269, 2, prime_269, prime_2, by norm_num⟩
  · exact ⟨271, 2, prime_271, prime_2, by norm_num⟩
  · exact ⟨271, 3, prime_271, prime_3, by norm_num⟩
  · exact ⟨269, 5, prime_269, prime_5, by norm_num⟩
  · exact ⟨277, 2, prime_277, prime_2, by norm_num⟩
  · exact ⟨277, 3, prime_277, prime_3, by norm_num⟩
  · exact ⟨281, 2, prime_281, prime_2, by norm_num⟩
  · exact ⟨283, 2, prime_283, prime_2, by norm_num⟩
  · exact ⟨283, 3, prime_283, prime_3, by norm_num⟩
  · exact ⟨281, 5, prime_281, prime_5, by norm_num⟩
  · exact ⟨283, 5, prime_283, prime_5, by norm_num⟩
  · exact ⟨281, 7, prime_281, prime_7, by norm_num⟩
  · exact ⟨293, 2, prime_293, prime_2, by norm_num⟩
  · exact ⟨293, 3, prime_293, prime_3, by norm_num⟩
  · exact ⟨263, 19, prime_263, prime_19, by norm_num⟩
  · exact ⟨293, 5, prime_293, prime_5, by norm_num⟩
  · exact ⟨283, 11, prime_283, prime_11, by norm_num⟩
  · exact ⟨293, 7, prime_293, prime_7, by norm_num⟩
  · exact ⟨283, 13, prime_283, prime_13, by norm_num⟩
  · exact ⟨307, 2, prime_307, prime_2, by norm_num⟩
  · exact ⟨307, 3, prime_307, prime_3, by norm_num⟩
  · exact ⟨311, 2, prime_311, prime_2, by norm_num⟩
  · exact ⟨313, 2, prime_313, prime_2, by norm_num⟩
  · exact ⟨313, 3, prime_313, prime_3, by norm_num⟩
  · exact ⟨317, 2, prime_317, prime_2, by norm_num⟩
  · exact ⟨317, 3, prime_317, prime_3, by norm_num⟩
  · exact ⟨311, 7, prime_311, prime_7, by norm_num⟩
  · exact ⟨317, 5, prime_317, prime_5, by norm_num⟩
  · exact ⟨307, 11, prime_307, prime_11, by norm_num⟩
  · exact ⟨317, 7, prime_317, prime_7, by norm_num⟩
  · exact ⟨311, 11, prime_311, prime_11, by norm_num⟩
  · exact ⟨331, 2, prime_331, prime_2, by norm_num⟩
  · exact ⟨331, 3, prime_331, prime_3, by norm_num⟩
  · exact ⟨317, 11, prime_317, prime_11, by norm_num⟩
  · exact ⟨337, 2, prime_337, prime_2, by norm_num⟩
  · exact ⟨337, 3, prime_337, prime_3, by norm_num⟩
  · exact ⟨331, 7, prime_331, prime_7, by norm_num⟩
  · exact ⟨337, 5, prime_337, prime_5, by norm_num⟩
  · exact ⟨311, 19, prime_311, prime_19, by norm_num⟩
  · exact ⟨347, 2, prime_347, prime_2, by norm_num⟩
  · exact ⟨349, 2, prime_349, prime_2, by norm_num⟩
  · exact ⟨349, 3, prime_349, prime_3, by norm_num⟩
  · exact ⟨353, 2, prime_353, prime_2, by norm_num⟩
  · exact ⟨353, 3, prime_353, prime_3, by norm_num⟩
  · exact ⟨347, 7, prime_347, prime_7, by norm_num⟩
  · exact ⟨359, 2, prime_359, prime_2, by norm_num⟩
  · exact ⟨359, 3, prime_359, prime_3, by norm_num⟩
  · exact ⟨353, 7, prime_353, prime_7, by norm_num⟩
  · exact ⟨359, 5, prime_359, prime_5, by norm_num⟩
  · exact ⟨367, 2, prime_367, prime_2, by norm_num⟩
  · exact ⟨367, 3, prime_367, prime_3, by norm_num⟩
  · exact ⟨353, 11, prime_353, prime_11, by norm_num⟩
  · exact ⟨373, 2, prime_373, prime_2, by norm_num⟩
  · exact ⟨373, 3, prime_373, prime_3, by norm_num⟩
  · exact ⟨367, 7, prime_367, prime_7, by norm_num⟩
  · exact ⟨379, 2, prime_379, prime_2, by norm_num⟩
  · exact ⟨379, 3, prime_379, prime_3, by norm_num⟩
  · exact ⟨383, 2, prime_383, prime_2, by norm_num⟩
  · exact ⟨383, 3, prime_383, prime_3, by norm_num⟩
  · exact ⟨353, 19, prime_353, prime_19, by norm_num⟩
  · exact ⟨389, 2, prime_389, prime_2, by norm_num⟩
  · exact ⟨389, 3, prime_389, prime_3, by norm_num⟩
  · exact ⟨383, 7, prime_383, prime_7, by norm_num⟩
  · exact ⟨389, 5, prime_389, prime_5, by norm_num⟩
  · exact ⟨397, 2, prime_397, prime_2, by norm_num⟩
  · exact ⟨397, 3, prime_397, prime_3, by norm_num⟩
  · exact ⟨401, 2, prime_401, prime_2, by norm_num⟩

private theorem lemoine_chunk_2 : ∀ k : ℕ, 203 ≤ k → k ≤ 302 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨401, 3, prime_401, prime_3, by norm_num⟩
  · exact ⟨383, 13, prime_383, prime_13, by norm_num⟩
  · exact ⟨401, 5, prime_401, prime_5, by norm_num⟩
  · exact ⟨409, 2, prime_409, prime_2, by norm_num⟩
  · exact ⟨409, 3, prime_409, prime_3, by norm_num⟩
  · exact ⟨383, 17, prime_383, prime_17, by norm_num⟩
  · exact ⟨409, 5, prime_409, prime_5, by norm_num⟩
  · exact ⟨383, 19, prime_383, prime_19, by norm_num⟩
  · exact ⟨419, 2, prime_419, prime_2, by norm_num⟩
  · exact ⟨421, 2, prime_421, prime_2, by norm_num⟩
  · exact ⟨421, 3, prime_421, prime_3, by norm_num⟩
  · exact ⟨419, 5, prime_419, prime_5, by norm_num⟩
  · exact ⟨421, 5, prime_421, prime_5, by norm_num⟩
  · exact ⟨419, 7, prime_419, prime_7, by norm_num⟩
  · exact ⟨431, 2, prime_431, prime_2, by norm_num⟩
  · exact ⟨433, 2, prime_433, prime_2, by norm_num⟩
  · exact ⟨433, 3, prime_433, prime_3, by norm_num⟩
  · exact ⟨431, 5, prime_431, prime_5, by norm_num⟩
  · exact ⟨439, 2, prime_439, prime_2, by norm_num⟩
  · exact ⟨439, 3, prime_439, prime_3, by norm_num⟩
  · exact ⟨443, 2, prime_443, prime_2, by norm_num⟩
  · exact ⟨443, 3, prime_443, prime_3, by norm_num⟩
  · exact ⟨389, 31, prime_389, prime_31, by norm_num⟩
  · exact ⟨449, 2, prime_449, prime_2, by norm_num⟩
  · exact ⟨449, 3, prime_449, prime_3, by norm_num⟩
  · exact ⟨443, 7, prime_443, prime_7, by norm_num⟩
  · exact ⟨449, 5, prime_449, prime_5, by norm_num⟩
  · exact ⟨457, 2, prime_457, prime_2, by norm_num⟩
  · exact ⟨457, 3, prime_457, prime_3, by norm_num⟩
  · exact ⟨461, 2, prime_461, prime_2, by norm_num⟩
  · exact ⟨463, 2, prime_463, prime_2, by norm_num⟩
  · exact ⟨463, 3, prime_463, prime_3, by norm_num⟩
  · exact ⟨467, 2, prime_467, prime_2, by norm_num⟩
  · exact ⟨467, 3, prime_467, prime_3, by norm_num⟩
  · exact ⟨461, 7, prime_461, prime_7, by norm_num⟩
  · exact ⟨467, 5, prime_467, prime_5, by norm_num⟩
  · exact ⟨457, 11, prime_457, prime_11, by norm_num⟩
  · exact ⟨467, 7, prime_467, prime_7, by norm_num⟩
  · exact ⟨479, 2, prime_479, prime_2, by norm_num⟩
  · exact ⟨479, 3, prime_479, prime_3, by norm_num⟩
  · exact ⟨461, 13, prime_461, prime_13, by norm_num⟩
  · exact ⟨479, 5, prime_479, prime_5, by norm_num⟩
  · exact ⟨487, 2, prime_487, prime_2, by norm_num⟩
  · exact ⟨487, 3, prime_487, prime_3, by norm_num⟩
  · exact ⟨491, 2, prime_491, prime_2, by norm_num⟩
  · exact ⟨491, 3, prime_491, prime_3, by norm_num⟩
  · exact ⟨461, 19, prime_461, prime_19, by norm_num⟩
  · exact ⟨491, 5, prime_491, prime_5, by norm_num⟩
  · exact ⟨499, 2, prime_499, prime_2, by norm_num⟩
  · exact ⟨499, 3, prime_499, prime_3, by norm_num⟩
  · exact ⟨503, 2, prime_503, prime_2, by norm_num⟩
  · exact ⟨503, 3, prime_503, prime_3, by norm_num⟩
  · exact ⟨449, 31, prime_449, prime_31, by norm_num⟩
  · exact ⟨509, 2, prime_509, prime_2, by norm_num⟩
  · exact ⟨509, 3, prime_509, prime_3, by norm_num⟩
  · exact ⟨503, 7, prime_503, prime_7, by norm_num⟩
  · exact ⟨509, 5, prime_509, prime_5, by norm_num⟩
  · exact ⟨499, 11, prime_499, prime_11, by norm_num⟩
  · exact ⟨509, 7, prime_509, prime_7, by norm_num⟩
  · exact ⟨521, 2, prime_521, prime_2, by norm_num⟩
  · exact ⟨523, 2, prime_523, prime_2, by norm_num⟩
  · exact ⟨523, 3, prime_523, prime_3, by norm_num⟩
  · exact ⟨521, 5, prime_521, prime_5, by norm_num⟩
  · exact ⟨523, 5, prime_523, prime_5, by norm_num⟩
  · exact ⟨521, 7, prime_521, prime_7, by norm_num⟩
  · exact ⟨523, 7, prime_523, prime_7, by norm_num⟩
  · exact ⟨457, 41, prime_457, prime_41, by norm_num⟩
  · exact ⟨503, 19, prime_503, prime_19, by norm_num⟩
  · exact ⟨521, 11, prime_521, prime_11, by norm_num⟩
  · exact ⟨541, 2, prime_541, prime_2, by norm_num⟩
  · exact ⟨541, 3, prime_541, prime_3, by norm_num⟩
  · exact ⟨523, 13, prime_523, prime_13, by norm_num⟩
  · exact ⟨547, 2, prime_547, prime_2, by norm_num⟩
  · exact ⟨547, 3, prime_547, prime_3, by norm_num⟩
  · exact ⟨541, 7, prime_541, prime_7, by norm_num⟩
  · exact ⟨547, 5, prime_547, prime_5, by norm_num⟩
  · exact ⟨521, 19, prime_521, prime_19, by norm_num⟩
  · exact ⟨557, 2, prime_557, prime_2, by norm_num⟩
  · exact ⟨557, 3, prime_557, prime_3, by norm_num⟩
  · exact ⟨503, 31, prime_503, prime_31, by norm_num⟩
  · exact ⟨563, 2, prime_563, prime_2, by norm_num⟩
  · exact ⟨563, 3, prime_563, prime_3, by norm_num⟩
  · exact ⟨557, 7, prime_557, prime_7, by norm_num⟩
  · exact ⟨569, 2, prime_569, prime_2, by norm_num⟩
  · exact ⟨571, 2, prime_571, prime_2, by norm_num⟩
  · exact ⟨571, 3, prime_571, prime_3, by norm_num⟩
  · exact ⟨569, 5, prime_569, prime_5, by norm_num⟩
  · exact ⟨577, 2, prime_577, prime_2, by norm_num⟩
  · exact ⟨577, 3, prime_577, prime_3, by norm_num⟩
  · exact ⟨571, 7, prime_571, prime_7, by norm_num⟩
  · exact ⟨577, 5, prime_577, prime_5, by norm_num⟩
  · exact ⟨563, 13, prime_563, prime_13, by norm_num⟩
  · exact ⟨587, 2, prime_587, prime_2, by norm_num⟩
  · exact ⟨587, 3, prime_587, prime_3, by norm_num⟩
  · exact ⟨569, 13, prime_569, prime_13, by norm_num⟩
  · exact ⟨593, 2, prime_593, prime_2, by norm_num⟩
  · exact ⟨593, 3, prime_593, prime_3, by norm_num⟩
  · exact ⟨587, 7, prime_587, prime_7, by norm_num⟩
  · exact ⟨599, 2, prime_599, prime_2, by norm_num⟩
  · exact ⟨601, 2, prime_601, prime_2, by norm_num⟩

private theorem lemoine_chunk_3 : ∀ k : ℕ, 303 ≤ k → k ≤ 402 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨601, 3, prime_601, prime_3, by norm_num⟩
  · exact ⟨599, 5, prime_599, prime_5, by norm_num⟩
  · exact ⟨607, 2, prime_607, prime_2, by norm_num⟩
  · exact ⟨607, 3, prime_607, prime_3, by norm_num⟩
  · exact ⟨601, 7, prime_601, prime_7, by norm_num⟩
  · exact ⟨613, 2, prime_613, prime_2, by norm_num⟩
  · exact ⟨613, 3, prime_613, prime_3, by norm_num⟩
  · exact ⟨617, 2, prime_617, prime_2, by norm_num⟩
  · exact ⟨619, 2, prime_619, prime_2, by norm_num⟩
  · exact ⟨619, 3, prime_619, prime_3, by norm_num⟩
  · exact ⟨617, 5, prime_617, prime_5, by norm_num⟩
  · exact ⟨619, 5, prime_619, prime_5, by norm_num⟩
  · exact ⟨617, 7, prime_617, prime_7, by norm_num⟩
  · exact ⟨619, 7, prime_619, prime_7, by norm_num⟩
  · exact ⟨631, 2, prime_631, prime_2, by norm_num⟩
  · exact ⟨631, 3, prime_631, prime_3, by norm_num⟩
  · exact ⟨617, 11, prime_617, prime_11, by norm_num⟩
  · exact ⟨631, 5, prime_631, prime_5, by norm_num⟩
  · exact ⟨617, 13, prime_617, prime_13, by norm_num⟩
  · exact ⟨641, 2, prime_641, prime_2, by norm_num⟩
  · exact ⟨643, 2, prime_643, prime_2, by norm_num⟩
  · exact ⟨643, 3, prime_643, prime_3, by norm_num⟩
  · exact ⟨647, 2, prime_647, prime_2, by norm_num⟩
  · exact ⟨647, 3, prime_647, prime_3, by norm_num⟩
  · exact ⟨641, 7, prime_641, prime_7, by norm_num⟩
  · exact ⟨653, 2, prime_653, prime_2, by norm_num⟩
  · exact ⟨653, 3, prime_653, prime_3, by norm_num⟩
  · exact ⟨647, 7, prime_647, prime_7, by norm_num⟩
  · exact ⟨659, 2, prime_659, prime_2, by norm_num⟩
  · exact ⟨661, 2, prime_661, prime_2, by norm_num⟩
  · exact ⟨661, 3, prime_661, prime_3, by norm_num⟩
  · exact ⟨659, 5, prime_659, prime_5, by norm_num⟩
  · exact ⟨661, 5, prime_661, prime_5, by norm_num⟩
  · exact ⟨659, 7, prime_659, prime_7, by norm_num⟩
  · exact ⟨661, 7, prime_661, prime_7, by norm_num⟩
  · exact ⟨673, 2, prime_673, prime_2, by norm_num⟩
  · exact ⟨673, 3, prime_673, prime_3, by norm_num⟩
  · exact ⟨677, 2, prime_677, prime_2, by norm_num⟩
  · exact ⟨677, 3, prime_677, prime_3, by norm_num⟩
  · exact ⟨659, 13, prime_659, prime_13, by norm_num⟩
  · exact ⟨683, 2, prime_683, prime_2, by norm_num⟩
  · exact ⟨683, 3, prime_683, prime_3, by norm_num⟩
  · exact ⟨677, 7, prime_677, prime_7, by norm_num⟩
  · exact ⟨683, 5, prime_683, prime_5, by norm_num⟩
  · exact ⟨691, 2, prime_691, prime_2, by norm_num⟩
  · exact ⟨691, 3, prime_691, prime_3, by norm_num⟩
  · exact ⟨677, 11, prime_677, prime_11, by norm_num⟩
  · exact ⟨691, 5, prime_691, prime_5, by norm_num⟩
  · exact ⟨677, 13, prime_677, prime_13, by norm_num⟩
  · exact ⟨701, 2, prime_701, prime_2, by norm_num⟩
  · exact ⟨701, 3, prime_701, prime_3, by norm_num⟩
  · exact ⟨683, 13, prime_683, prime_13, by norm_num⟩
  · exact ⟨701, 5, prime_701, prime_5, by norm_num⟩
  · exact ⟨709, 2, prime_709, prime_2, by norm_num⟩
  · exact ⟨709, 3, prime_709, prime_3, by norm_num⟩
  · exact ⟨691, 13, prime_691, prime_13, by norm_num⟩
  · exact ⟨709, 5, prime_709, prime_5, by norm_num⟩
  · exact ⟨683, 19, prime_683, prime_19, by norm_num⟩
  · exact ⟨719, 2, prime_719, prime_2, by norm_num⟩
  · exact ⟨719, 3, prime_719, prime_3, by norm_num⟩
  · exact ⟨701, 13, prime_701, prime_13, by norm_num⟩
  · exact ⟨719, 5, prime_719, prime_5, by norm_num⟩
  · exact ⟨727, 2, prime_727, prime_2, by norm_num⟩
  · exact ⟨727, 3, prime_727, prime_3, by norm_num⟩
  · exact ⟨709, 13, prime_709, prime_13, by norm_num⟩
  · exact ⟨733, 2, prime_733, prime_2, by norm_num⟩
  · exact ⟨733, 3, prime_733, prime_3, by norm_num⟩
  · exact ⟨727, 7, prime_727, prime_7, by norm_num⟩
  · exact ⟨739, 2, prime_739, prime_2, by norm_num⟩
  · exact ⟨739, 3, prime_739, prime_3, by norm_num⟩
  · exact ⟨743, 2, prime_743, prime_2, by norm_num⟩
  · exact ⟨743, 3, prime_743, prime_3, by norm_num⟩
  · exact ⟨677, 37, prime_677, prime_37, by norm_num⟩
  · exact ⟨743, 5, prime_743, prime_5, by norm_num⟩
  · exact ⟨751, 2, prime_751, prime_2, by norm_num⟩
  · exact ⟨751, 3, prime_751, prime_3, by norm_num⟩
  · exact ⟨733, 13, prime_733, prime_13, by norm_num⟩
  · exact ⟨757, 2, prime_757, prime_2, by norm_num⟩
  · exact ⟨757, 3, prime_757, prime_3, by norm_num⟩
  · exact ⟨761, 2, prime_761, prime_2, by norm_num⟩
  · exact ⟨761, 3, prime_761, prime_3, by norm_num⟩
  · exact ⟨743, 13, prime_743, prime_13, by norm_num⟩
  · exact ⟨761, 5, prime_761, prime_5, by norm_num⟩
  · exact ⟨769, 2, prime_769, prime_2, by norm_num⟩
  · exact ⟨769, 3, prime_769, prime_3, by norm_num⟩
  · exact ⟨773, 2, prime_773, prime_2, by norm_num⟩
  · exact ⟨773, 3, prime_773, prime_3, by norm_num⟩
  · exact ⟨743, 19, prime_743, prime_19, by norm_num⟩
  · exact ⟨773, 5, prime_773, prime_5, by norm_num⟩
  · exact ⟨751, 17, prime_751, prime_17, by norm_num⟩
  · exact ⟨773, 7, prime_773, prime_7, by norm_num⟩
  · exact ⟨751, 19, prime_751, prime_19, by norm_num⟩
  · exact ⟨787, 2, prime_787, prime_2, by norm_num⟩
  · exact ⟨787, 3, prime_787, prime_3, by norm_num⟩
  · exact ⟨773, 11, prime_773, prime_11, by norm_num⟩
  · exact ⟨787, 5, prime_787, prime_5, by norm_num⟩
  · exact ⟨773, 13, prime_773, prime_13, by norm_num⟩
  · exact ⟨797, 2, prime_797, prime_2, by norm_num⟩
  · exact ⟨797, 3, prime_797, prime_3, by norm_num⟩
  · exact ⟨743, 31, prime_743, prime_31, by norm_num⟩

private theorem lemoine_chunk_4 : ∀ k : ℕ, 403 ≤ k → k ≤ 502 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨797, 5, prime_797, prime_5, by norm_num⟩
  · exact ⟨787, 11, prime_787, prime_11, by norm_num⟩
  · exact ⟨797, 7, prime_797, prime_7, by norm_num⟩
  · exact ⟨809, 2, prime_809, prime_2, by norm_num⟩
  · exact ⟨811, 2, prime_811, prime_2, by norm_num⟩
  · exact ⟨811, 3, prime_811, prime_3, by norm_num⟩
  · exact ⟨809, 5, prime_809, prime_5, by norm_num⟩
  · exact ⟨811, 5, prime_811, prime_5, by norm_num⟩
  · exact ⟨809, 7, prime_809, prime_7, by norm_num⟩
  · exact ⟨821, 2, prime_821, prime_2, by norm_num⟩
  · exact ⟨823, 2, prime_823, prime_2, by norm_num⟩
  · exact ⟨823, 3, prime_823, prime_3, by norm_num⟩
  · exact ⟨827, 2, prime_827, prime_2, by norm_num⟩
  · exact ⟨829, 2, prime_829, prime_2, by norm_num⟩
  · exact ⟨829, 3, prime_829, prime_3, by norm_num⟩
  · exact ⟨827, 5, prime_827, prime_5, by norm_num⟩
  · exact ⟨829, 5, prime_829, prime_5, by norm_num⟩
  · exact ⟨827, 7, prime_827, prime_7, by norm_num⟩
  · exact ⟨839, 2, prime_839, prime_2, by norm_num⟩
  · exact ⟨839, 3, prime_839, prime_3, by norm_num⟩
  · exact ⟨821, 13, prime_821, prime_13, by norm_num⟩
  · exact ⟨839, 5, prime_839, prime_5, by norm_num⟩
  · exact ⟨829, 11, prime_829, prime_11, by norm_num⟩
  · exact ⟨839, 7, prime_839, prime_7, by norm_num⟩
  · exact ⟨829, 13, prime_829, prime_13, by norm_num⟩
  · exact ⟨853, 2, prime_853, prime_2, by norm_num⟩
  · exact ⟨853, 3, prime_853, prime_3, by norm_num⟩
  · exact ⟨857, 2, prime_857, prime_2, by norm_num⟩
  · exact ⟨859, 2, prime_859, prime_2, by norm_num⟩
  · exact ⟨859, 3, prime_859, prime_3, by norm_num⟩
  · exact ⟨863, 2, prime_863, prime_2, by norm_num⟩
  · exact ⟨863, 3, prime_863, prime_3, by norm_num⟩
  · exact ⟨857, 7, prime_857, prime_7, by norm_num⟩
  · exact ⟨863, 5, prime_863, prime_5, by norm_num⟩
  · exact ⟨853, 11, prime_853, prime_11, by norm_num⟩
  · exact ⟨863, 7, prime_863, prime_7, by norm_num⟩
  · exact ⟨857, 11, prime_857, prime_11, by norm_num⟩
  · exact ⟨877, 2, prime_877, prime_2, by norm_num⟩
  · exact ⟨877, 3, prime_877, prime_3, by norm_num⟩
  · exact ⟨881, 2, prime_881, prime_2, by norm_num⟩
  · exact ⟨883, 2, prime_883, prime_2, by norm_num⟩
  · exact ⟨883, 3, prime_883, prime_3, by norm_num⟩
  · exact ⟨887, 2, prime_887, prime_2, by norm_num⟩
  · exact ⟨887, 3, prime_887, prime_3, by norm_num⟩
  · exact ⟨881, 7, prime_881, prime_7, by norm_num⟩
  · exact ⟨887, 5, prime_887, prime_5, by norm_num⟩
  · exact ⟨877, 11, prime_877, prime_11, by norm_num⟩
  · exact ⟨887, 7, prime_887, prime_7, by norm_num⟩
  · exact ⟨881, 11, prime_881, prime_11, by norm_num⟩
  · exact ⟨883, 11, prime_883, prime_11, by norm_num⟩
  · exact ⟨881, 13, prime_881, prime_13, by norm_num⟩
  · exact ⟨887, 11, prime_887, prime_11, by norm_num⟩
  · exact ⟨907, 2, prime_907, prime_2, by norm_num⟩
  · exact ⟨907, 3, prime_907, prime_3, by norm_num⟩
  · exact ⟨911, 2, prime_911, prime_2, by norm_num⟩
  · exact ⟨911, 3, prime_911, prime_3, by norm_num⟩
  · exact ⟨881, 19, prime_881, prime_19, by norm_num⟩
  · exact ⟨911, 5, prime_911, prime_5, by norm_num⟩
  · exact ⟨919, 2, prime_919, prime_2, by norm_num⟩
  · exact ⟨919, 3, prime_919, prime_3, by norm_num⟩
  · exact ⟨881, 23, prime_881, prime_23, by norm_num⟩
  · exact ⟨919, 5, prime_919, prime_5, by norm_num⟩
  · exact ⟨857, 37, prime_857, prime_37, by norm_num⟩
  · exact ⟨929, 2, prime_929, prime_2, by norm_num⟩
  · exact ⟨929, 3, prime_929, prime_3, by norm_num⟩
  · exact ⟨911, 13, prime_911, prime_13, by norm_num⟩
  · exact ⟨929, 5, prime_929, prime_5, by norm_num⟩
  · exact ⟨937, 2, prime_937, prime_2, by norm_num⟩
  · exact ⟨937, 3, prime_937, prime_3, by norm_num⟩
  · exact ⟨941, 2, prime_941, prime_2, by norm_num⟩
  · exact ⟨941, 3, prime_941, prime_3, by norm_num⟩
  · exact ⟨911, 19, prime_911, prime_19, by norm_num⟩
  · exact ⟨947, 2, prime_947, prime_2, by norm_num⟩
  · exact ⟨947, 3, prime_947, prime_3, by norm_num⟩
  · exact ⟨941, 7, prime_941, prime_7, by norm_num⟩
  · exact ⟨953, 2, prime_953, prime_2, by norm_num⟩
  · exact ⟨953, 3, prime_953, prime_3, by norm_num⟩
  · exact ⟨947, 7, prime_947, prime_7, by norm_num⟩
  · exact ⟨953, 5, prime_953, prime_5, by norm_num⟩
  · exact ⟨919, 23, prime_919, prime_23, by norm_num⟩
  · exact ⟨953, 7, prime_953, prime_7, by norm_num⟩
  · exact ⟨947, 11, prime_947, prime_11, by norm_num⟩
  · exact ⟨967, 2, prime_967, prime_2, by norm_num⟩
  · exact ⟨967, 3, prime_967, prime_3, by norm_num⟩
  · exact ⟨971, 2, prime_971, prime_2, by norm_num⟩
  · exact ⟨971, 3, prime_971, prime_3, by norm_num⟩
  · exact ⟨953, 13, prime_953, prime_13, by norm_num⟩
  · exact ⟨977, 2, prime_977, prime_2, by norm_num⟩
  · exact ⟨977, 3, prime_977, prime_3, by norm_num⟩
  · exact ⟨971, 7, prime_971, prime_7, by norm_num⟩
  · exact ⟨983, 2, prime_983, prime_2, by norm_num⟩
  · exact ⟨983, 3, prime_983, prime_3, by norm_num⟩
  · exact ⟨977, 7, prime_977, prime_7, by norm_num⟩
  · exact ⟨983, 5, prime_983, prime_5, by norm_num⟩
  · exact ⟨991, 2, prime_991, prime_2, by norm_num⟩
  · exact ⟨991, 3, prime_991, prime_3, by norm_num⟩
  · exact ⟨977, 11, prime_977, prime_11, by norm_num⟩
  · exact ⟨997, 2, prime_997, prime_2, by norm_num⟩
  · exact ⟨997, 3, prime_997, prime_3, by norm_num⟩
  · exact ⟨991, 7, prime_991, prime_7, by norm_num⟩

private theorem lemoine_chunk_5 : ∀ k : ℕ, 503 ≤ k → k ≤ 602 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨997, 5, prime_997, prime_5, by norm_num⟩
  · exact ⟨983, 13, prime_983, prime_13, by norm_num⟩
  · exact ⟨997, 7, prime_997, prime_7, by norm_num⟩
  · exact ⟨1009, 2, prime_1009, prime_2, by norm_num⟩
  · exact ⟨1009, 3, prime_1009, prime_3, by norm_num⟩
  · exact ⟨1013, 2, prime_1013, prime_2, by norm_num⟩
  · exact ⟨1013, 3, prime_1013, prime_3, by norm_num⟩
  · exact ⟨983, 19, prime_983, prime_19, by norm_num⟩
  · exact ⟨1019, 2, prime_1019, prime_2, by norm_num⟩
  · exact ⟨1021, 2, prime_1021, prime_2, by norm_num⟩
  · exact ⟨1021, 3, prime_1021, prime_3, by norm_num⟩
  · exact ⟨1019, 5, prime_1019, prime_5, by norm_num⟩
  · exact ⟨1021, 5, prime_1021, prime_5, by norm_num⟩
  · exact ⟨1019, 7, prime_1019, prime_7, by norm_num⟩
  · exact ⟨1031, 2, prime_1031, prime_2, by norm_num⟩
  · exact ⟨1033, 2, prime_1033, prime_2, by norm_num⟩
  · exact ⟨1033, 3, prime_1033, prime_3, by norm_num⟩
  · exact ⟨1031, 5, prime_1031, prime_5, by norm_num⟩
  · exact ⟨1039, 2, prime_1039, prime_2, by norm_num⟩
  · exact ⟨1039, 3, prime_1039, prime_3, by norm_num⟩
  · exact ⟨1033, 7, prime_1033, prime_7, by norm_num⟩
  · exact ⟨1039, 5, prime_1039, prime_5, by norm_num⟩
  · exact ⟨1013, 19, prime_1013, prime_19, by norm_num⟩
  · exact ⟨1049, 2, prime_1049, prime_2, by norm_num⟩
  · exact ⟨1051, 2, prime_1051, prime_2, by norm_num⟩
  · exact ⟨1051, 3, prime_1051, prime_3, by norm_num⟩
  · exact ⟨1049, 5, prime_1049, prime_5, by norm_num⟩
  · exact ⟨1051, 5, prime_1051, prime_5, by norm_num⟩
  · exact ⟨1049, 7, prime_1049, prime_7, by norm_num⟩
  · exact ⟨1061, 2, prime_1061, prime_2, by norm_num⟩
  · exact ⟨1063, 2, prime_1063, prime_2, by norm_num⟩
  · exact ⟨1063, 3, prime_1063, prime_3, by norm_num⟩
  · exact ⟨1061, 5, prime_1061, prime_5, by norm_num⟩
  · exact ⟨1069, 2, prime_1069, prime_2, by norm_num⟩
  · exact ⟨1069, 3, prime_1069, prime_3, by norm_num⟩
  · exact ⟨1063, 7, prime_1063, prime_7, by norm_num⟩
  · exact ⟨1069, 5, prime_1069, prime_5, by norm_num⟩
  · exact ⟨1019, 31, prime_1019, prime_31, by norm_num⟩
  · exact ⟨1069, 7, prime_1069, prime_7, by norm_num⟩
  · exact ⟨1063, 11, prime_1063, prime_11, by norm_num⟩
  · exact ⟨1061, 13, prime_1061, prime_13, by norm_num⟩
  · exact ⟨1063, 13, prime_1063, prime_13, by norm_num⟩
  · exact ⟨1087, 2, prime_1087, prime_2, by norm_num⟩
  · exact ⟨1087, 3, prime_1087, prime_3, by norm_num⟩
  · exact ⟨1091, 2, prime_1091, prime_2, by norm_num⟩
  · exact ⟨1093, 2, prime_1093, prime_2, by norm_num⟩
  · exact ⟨1093, 3, prime_1093, prime_3, by norm_num⟩
  · exact ⟨1097, 2, prime_1097, prime_2, by norm_num⟩
  · exact ⟨1097, 3, prime_1097, prime_3, by norm_num⟩
  · exact ⟨1091, 7, prime_1091, prime_7, by norm_num⟩
  · exact ⟨1103, 2, prime_1103, prime_2, by norm_num⟩
  · exact ⟨1103, 3, prime_1103, prime_3, by norm_num⟩
  · exact ⟨1097, 7, prime_1097, prime_7, by norm_num⟩
  · exact ⟨1109, 2, prime_1109, prime_2, by norm_num⟩
  · exact ⟨1109, 3, prime_1109, prime_3, by norm_num⟩
  · exact ⟨1103, 7, prime_1103, prime_7, by norm_num⟩
  · exact ⟨1109, 5, prime_1109, prime_5, by norm_num⟩
  · exact ⟨1117, 2, prime_1117, prime_2, by norm_num⟩
  · exact ⟨1117, 3, prime_1117, prime_3, by norm_num⟩
  · exact ⟨1103, 11, prime_1103, prime_11, by norm_num⟩
  · exact ⟨1123, 2, prime_1123, prime_2, by norm_num⟩
  · exact ⟨1123, 3, prime_1123, prime_3, by norm_num⟩
  · exact ⟨1117, 7, prime_1117, prime_7, by norm_num⟩
  · exact ⟨1129, 2, prime_1129, prime_2, by norm_num⟩
  · exact ⟨1129, 3, prime_1129, prime_3, by norm_num⟩
  · exact ⟨1123, 7, prime_1123, prime_7, by norm_num⟩
  · exact ⟨1129, 5, prime_1129, prime_5, by norm_num⟩
  · exact ⟨1103, 19, prime_1103, prime_19, by norm_num⟩
  · exact ⟨1129, 7, prime_1129, prime_7, by norm_num⟩
  · exact ⟨1123, 11, prime_1123, prime_11, by norm_num⟩
  · exact ⟨1109, 19, prime_1109, prime_19, by norm_num⟩
  · exact ⟨1123, 13, prime_1123, prime_13, by norm_num⟩
  · exact ⟨1129, 11, prime_1129, prime_11, by norm_num⟩
  · exact ⟨1091, 31, prime_1091, prime_31, by norm_num⟩
  · exact ⟨1151, 2, prime_1151, prime_2, by norm_num⟩
  · exact ⟨1153, 2, prime_1153, prime_2, by norm_num⟩
  · exact ⟨1153, 3, prime_1153, prime_3, by norm_num⟩
  · exact ⟨1151, 5, prime_1151, prime_5, by norm_num⟩
  · exact ⟨1153, 5, prime_1153, prime_5, by norm_num⟩
  · exact ⟨1151, 7, prime_1151, prime_7, by norm_num⟩
  · exact ⟨1163, 2, prime_1163, prime_2, by norm_num⟩
  · exact ⟨1163, 3, prime_1163, prime_3, by norm_num⟩
  · exact ⟨1109, 31, prime_1109, prime_31, by norm_num⟩
  · exact ⟨1163, 5, prime_1163, prime_5, by norm_num⟩
  · exact ⟨1171, 2, prime_1171, prime_2, by norm_num⟩
  · exact ⟨1171, 3, prime_1171, prime_3, by norm_num⟩
  · exact ⟨1153, 13, prime_1153, prime_13, by norm_num⟩
  · exact ⟨1171, 5, prime_1171, prime_5, by norm_num⟩
  · exact ⟨1109, 37, prime_1109, prime_37, by norm_num⟩
  · exact ⟨1181, 2, prime_1181, prime_2, by norm_num⟩
  · exact ⟨1181, 3, prime_1181, prime_3, by norm_num⟩
  · exact ⟨1163, 13, prime_1163, prime_13, by norm_num⟩
  · exact ⟨1187, 2, prime_1187, prime_2, by norm_num⟩
  · exact ⟨1187, 3, prime_1187, prime_3, by norm_num⟩
  · exact ⟨1181, 7, prime_1181, prime_7, by norm_num⟩
  · exact ⟨1193, 2, prime_1193, prime_2, by norm_num⟩
  · exact ⟨1193, 3, prime_1193, prime_3, by norm_num⟩
  · exact ⟨1187, 7, prime_1187, prime_7, by norm_num⟩
  · exact ⟨1193, 5, prime_1193, prime_5, by norm_num⟩
  · exact ⟨1201, 2, prime_1201, prime_2, by norm_num⟩

private theorem lemoine_chunk_6 : ∀ k : ℕ, 603 ≤ k → k ≤ 702 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1201, 3, prime_1201, prime_3, by norm_num⟩
  · exact ⟨1187, 11, prime_1187, prime_11, by norm_num⟩
  · exact ⟨1201, 5, prime_1201, prime_5, by norm_num⟩
  · exact ⟨1187, 13, prime_1187, prime_13, by norm_num⟩
  · exact ⟨1201, 7, prime_1201, prime_7, by norm_num⟩
  · exact ⟨1213, 2, prime_1213, prime_2, by norm_num⟩
  · exact ⟨1213, 3, prime_1213, prime_3, by norm_num⟩
  · exact ⟨1217, 2, prime_1217, prime_2, by norm_num⟩
  · exact ⟨1217, 3, prime_1217, prime_3, by norm_num⟩
  · exact ⟨1187, 19, prime_1187, prime_19, by norm_num⟩
  · exact ⟨1223, 2, prime_1223, prime_2, by norm_num⟩
  · exact ⟨1223, 3, prime_1223, prime_3, by norm_num⟩
  · exact ⟨1217, 7, prime_1217, prime_7, by norm_num⟩
  · exact ⟨1229, 2, prime_1229, prime_2, by norm_num⟩
  · exact ⟨1231, 2, prime_1231, prime_2, by norm_num⟩
  · exact ⟨1231, 3, prime_1231, prime_3, by norm_num⟩
  · exact ⟨1229, 5, prime_1229, prime_5, by norm_num⟩
  · exact ⟨1237, 2, prime_1237, prime_2, by norm_num⟩
  · exact ⟨1237, 3, prime_1237, prime_3, by norm_num⟩
  · exact ⟨1231, 7, prime_1231, prime_7, by norm_num⟩
  · exact ⟨1237, 5, prime_1237, prime_5, by norm_num⟩
  · exact ⟨1223, 13, prime_1223, prime_13, by norm_num⟩
  · exact ⟨1237, 7, prime_1237, prime_7, by norm_num⟩
  · exact ⟨1249, 2, prime_1249, prime_2, by norm_num⟩
  · exact ⟨1249, 3, prime_1249, prime_3, by norm_num⟩
  · exact ⟨1231, 13, prime_1231, prime_13, by norm_num⟩
  · exact ⟨1249, 5, prime_1249, prime_5, by norm_num⟩
  · exact ⟨1223, 19, prime_1223, prime_19, by norm_num⟩
  · exact ⟨1259, 2, prime_1259, prime_2, by norm_num⟩
  · exact ⟨1259, 3, prime_1259, prime_3, by norm_num⟩
  · exact ⟨1229, 19, prime_1229, prime_19, by norm_num⟩
  · exact ⟨1259, 5, prime_1259, prime_5, by norm_num⟩
  · exact ⟨1249, 11, prime_1249, prime_11, by norm_num⟩
  · exact ⟨1259, 7, prime_1259, prime_7, by norm_num⟩
  · exact ⟨1249, 13, prime_1249, prime_13, by norm_num⟩
  · exact ⟨1231, 23, prime_1231, prime_23, by norm_num⟩
  · exact ⟨1217, 31, prime_1217, prime_31, by norm_num⟩
  · exact ⟨1277, 2, prime_1277, prime_2, by norm_num⟩
  · exact ⟨1279, 2, prime_1279, prime_2, by norm_num⟩
  · exact ⟨1279, 3, prime_1279, prime_3, by norm_num⟩
  · exact ⟨1283, 2, prime_1283, prime_2, by norm_num⟩
  · exact ⟨1283, 3, prime_1283, prime_3, by norm_num⟩
  · exact ⟨1277, 7, prime_1277, prime_7, by norm_num⟩
  · exact ⟨1289, 2, prime_1289, prime_2, by norm_num⟩
  · exact ⟨1291, 2, prime_1291, prime_2, by norm_num⟩
  · exact ⟨1291, 3, prime_1291, prime_3, by norm_num⟩
  · exact ⟨1289, 5, prime_1289, prime_5, by norm_num⟩
  · exact ⟨1297, 2, prime_1297, prime_2, by norm_num⟩
  · exact ⟨1297, 3, prime_1297, prime_3, by norm_num⟩
  · exact ⟨1301, 2, prime_1301, prime_2, by norm_num⟩
  · exact ⟨1303, 2, prime_1303, prime_2, by norm_num⟩
  · exact ⟨1303, 3, prime_1303, prime_3, by norm_num⟩
  · exact ⟨1307, 2, prime_1307, prime_2, by norm_num⟩
  · exact ⟨1307, 3, prime_1307, prime_3, by norm_num⟩
  · exact ⟨1301, 7, prime_1301, prime_7, by norm_num⟩
  · exact ⟨1307, 5, prime_1307, prime_5, by norm_num⟩
  · exact ⟨1297, 11, prime_1297, prime_11, by norm_num⟩
  · exact ⟨1307, 7, prime_1307, prime_7, by norm_num⟩
  · exact ⟨1319, 2, prime_1319, prime_2, by norm_num⟩
  · exact ⟨1321, 2, prime_1321, prime_2, by norm_num⟩
  · exact ⟨1321, 3, prime_1321, prime_3, by norm_num⟩
  · exact ⟨1319, 5, prime_1319, prime_5, by norm_num⟩
  · exact ⟨1327, 2, prime_1327, prime_2, by norm_num⟩
  · exact ⟨1327, 3, prime_1327, prime_3, by norm_num⟩
  · exact ⟨1321, 7, prime_1321, prime_7, by norm_num⟩
  · exact ⟨1327, 5, prime_1327, prime_5, by norm_num⟩
  · exact ⟨1301, 19, prime_1301, prime_19, by norm_num⟩
  · exact ⟨1327, 7, prime_1327, prime_7, by norm_num⟩
  · exact ⟨1321, 11, prime_1321, prime_11, by norm_num⟩
  · exact ⟨1319, 13, prime_1319, prime_13, by norm_num⟩
  · exact ⟨1321, 13, prime_1321, prime_13, by norm_num⟩
  · exact ⟨1327, 11, prime_1327, prime_11, by norm_num⟩
  · exact ⟨1289, 31, prime_1289, prime_31, by norm_num⟩
  · exact ⟨1327, 13, prime_1327, prime_13, by norm_num⟩
  · exact ⟨1321, 17, prime_1321, prime_17, by norm_num⟩
  · exact ⟨1319, 19, prime_1319, prime_19, by norm_num⟩
  · exact ⟨1321, 19, prime_1321, prime_19, by norm_num⟩
  · exact ⟨1327, 17, prime_1327, prime_17, by norm_num⟩
  · exact ⟨1301, 31, prime_1301, prime_31, by norm_num⟩
  · exact ⟨1361, 2, prime_1361, prime_2, by norm_num⟩
  · exact ⟨1361, 3, prime_1361, prime_3, by norm_num⟩
  · exact ⟨1307, 31, prime_1307, prime_31, by norm_num⟩
  · exact ⟨1367, 2, prime_1367, prime_2, by norm_num⟩
  · exact ⟨1367, 3, prime_1367, prime_3, by norm_num⟩
  · exact ⟨1361, 7, prime_1361, prime_7, by norm_num⟩
  · exact ⟨1373, 2, prime_1373, prime_2, by norm_num⟩
  · exact ⟨1373, 3, prime_1373, prime_3, by norm_num⟩
  · exact ⟨1367, 7, prime_1367, prime_7, by norm_num⟩
  · exact ⟨1373, 5, prime_1373, prime_5, by norm_num⟩
  · exact ⟨1381, 2, prime_1381, prime_2, by norm_num⟩
  · exact ⟨1381, 3, prime_1381, prime_3, by norm_num⟩
  · exact ⟨1367, 11, prime_1367, prime_11, by norm_num⟩
  · exact ⟨1381, 5, prime_1381, prime_5, by norm_num⟩
  · exact ⟨1367, 13, prime_1367, prime_13, by norm_num⟩
  · exact ⟨1381, 7, prime_1381, prime_7, by norm_num⟩
  · exact ⟨1303, 47, prime_1303, prime_47, by norm_num⟩
  · exact ⟨1373, 13, prime_1373, prime_13, by norm_num⟩
  · exact ⟨1367, 17, prime_1367, prime_17, by norm_num⟩
  · exact ⟨1399, 2, prime_1399, prime_2, by norm_num⟩
  · exact ⟨1399, 3, prime_1399, prime_3, by norm_num⟩

private theorem lemoine_chunk_7 : ∀ k : ℕ, 703 ≤ k → k ≤ 802 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1381, 13, prime_1381, prime_13, by norm_num⟩
  · exact ⟨1399, 5, prime_1399, prime_5, by norm_num⟩
  · exact ⟨1373, 19, prime_1373, prime_19, by norm_num⟩
  · exact ⟨1409, 2, prime_1409, prime_2, by norm_num⟩
  · exact ⟨1409, 3, prime_1409, prime_3, by norm_num⟩
  · exact ⟨1283, 67, prime_1283, prime_67, by norm_num⟩
  · exact ⟨1409, 5, prime_1409, prime_5, by norm_num⟩
  · exact ⟨1399, 11, prime_1399, prime_11, by norm_num⟩
  · exact ⟨1409, 7, prime_1409, prime_7, by norm_num⟩
  · exact ⟨1399, 13, prime_1399, prime_13, by norm_num⟩
  · exact ⟨1423, 2, prime_1423, prime_2, by norm_num⟩
  · exact ⟨1423, 3, prime_1423, prime_3, by norm_num⟩
  · exact ⟨1427, 2, prime_1427, prime_2, by norm_num⟩
  · exact ⟨1429, 2, prime_1429, prime_2, by norm_num⟩
  · exact ⟨1429, 3, prime_1429, prime_3, by norm_num⟩
  · exact ⟨1433, 2, prime_1433, prime_2, by norm_num⟩
  · exact ⟨1433, 3, prime_1433, prime_3, by norm_num⟩
  · exact ⟨1427, 7, prime_1427, prime_7, by norm_num⟩
  · exact ⟨1439, 2, prime_1439, prime_2, by norm_num⟩
  · exact ⟨1439, 3, prime_1439, prime_3, by norm_num⟩
  · exact ⟨1433, 7, prime_1433, prime_7, by norm_num⟩
  · exact ⟨1439, 5, prime_1439, prime_5, by norm_num⟩
  · exact ⟨1447, 2, prime_1447, prime_2, by norm_num⟩
  · exact ⟨1447, 3, prime_1447, prime_3, by norm_num⟩
  · exact ⟨1451, 2, prime_1451, prime_2, by norm_num⟩
  · exact ⟨1453, 2, prime_1453, prime_2, by norm_num⟩
  · exact ⟨1453, 3, prime_1453, prime_3, by norm_num⟩
  · exact ⟨1451, 5, prime_1451, prime_5, by norm_num⟩
  · exact ⟨1459, 2, prime_1459, prime_2, by norm_num⟩
  · exact ⟨1459, 3, prime_1459, prime_3, by norm_num⟩
  · exact ⟨1453, 7, prime_1453, prime_7, by norm_num⟩
  · exact ⟨1459, 5, prime_1459, prime_5, by norm_num⟩
  · exact ⟨1433, 19, prime_1433, prime_19, by norm_num⟩
  · exact ⟨1459, 7, prime_1459, prime_7, by norm_num⟩
  · exact ⟨1471, 2, prime_1471, prime_2, by norm_num⟩
  · exact ⟨1471, 3, prime_1471, prime_3, by norm_num⟩
  · exact ⟨1453, 13, prime_1453, prime_13, by norm_num⟩
  · exact ⟨1471, 5, prime_1471, prime_5, by norm_num⟩
  · exact ⟨1409, 37, prime_1409, prime_37, by norm_num⟩
  · exact ⟨1481, 2, prime_1481, prime_2, by norm_num⟩
  · exact ⟨1483, 2, prime_1483, prime_2, by norm_num⟩
  · exact ⟨1483, 3, prime_1483, prime_3, by norm_num⟩
  · exact ⟨1487, 2, prime_1487, prime_2, by norm_num⟩
  · exact ⟨1489, 2, prime_1489, prime_2, by norm_num⟩
  · exact ⟨1489, 3, prime_1489, prime_3, by norm_num⟩
  · exact ⟨1493, 2, prime_1493, prime_2, by norm_num⟩
  · exact ⟨1493, 3, prime_1493, prime_3, by norm_num⟩
  · exact ⟨1487, 7, prime_1487, prime_7, by norm_num⟩
  · exact ⟨1499, 2, prime_1499, prime_2, by norm_num⟩
  · exact ⟨1499, 3, prime_1499, prime_3, by norm_num⟩
  · exact ⟨1493, 7, prime_1493, prime_7, by norm_num⟩
  · exact ⟨1499, 5, prime_1499, prime_5, by norm_num⟩
  · exact ⟨1489, 11, prime_1489, prime_11, by norm_num⟩
  · exact ⟨1499, 7, prime_1499, prime_7, by norm_num⟩
  · exact ⟨1511, 2, prime_1511, prime_2, by norm_num⟩
  · exact ⟨1511, 3, prime_1511, prime_3, by norm_num⟩
  · exact ⟨1493, 13, prime_1493, prime_13, by norm_num⟩
  · exact ⟨1511, 5, prime_1511, prime_5, by norm_num⟩
  · exact ⟨1489, 17, prime_1489, prime_17, by norm_num⟩
  · exact ⟨1511, 7, prime_1511, prime_7, by norm_num⟩
  · exact ⟨1523, 2, prime_1523, prime_2, by norm_num⟩
  · exact ⟨1523, 3, prime_1523, prime_3, by norm_num⟩
  · exact ⟨1493, 19, prime_1493, prime_19, by norm_num⟩
  · exact ⟨1523, 5, prime_1523, prime_5, by norm_num⟩
  · exact ⟨1531, 2, prime_1531, prime_2, by norm_num⟩
  · exact ⟨1531, 3, prime_1531, prime_3, by norm_num⟩
  · exact ⟨1493, 23, prime_1493, prime_23, by norm_num⟩
  · exact ⟨1531, 5, prime_1531, prime_5, by norm_num⟩
  · exact ⟨1481, 31, prime_1481, prime_31, by norm_num⟩
  · exact ⟨1531, 7, prime_1531, prime_7, by norm_num⟩
  · exact ⟨1543, 2, prime_1543, prime_2, by norm_num⟩
  · exact ⟨1543, 3, prime_1543, prime_3, by norm_num⟩
  · exact ⟨1493, 29, prime_1493, prime_29, by norm_num⟩
  · exact ⟨1549, 2, prime_1549, prime_2, by norm_num⟩
  · exact ⟨1549, 3, prime_1549, prime_3, by norm_num⟩
  · exact ⟨1553, 2, prime_1553, prime_2, by norm_num⟩
  · exact ⟨1553, 3, prime_1553, prime_3, by norm_num⟩
  · exact ⟨1523, 19, prime_1523, prime_19, by norm_num⟩
  · exact ⟨1559, 2, prime_1559, prime_2, by norm_num⟩
  · exact ⟨1559, 3, prime_1559, prime_3, by norm_num⟩
  · exact ⟨1553, 7, prime_1553, prime_7, by norm_num⟩
  · exact ⟨1559, 5, prime_1559, prime_5, by norm_num⟩
  · exact ⟨1567, 2, prime_1567, prime_2, by norm_num⟩
  · exact ⟨1567, 3, prime_1567, prime_3, by norm_num⟩
  · exact ⟨1571, 2, prime_1571, prime_2, by norm_num⟩
  · exact ⟨1571, 3, prime_1571, prime_3, by norm_num⟩
  · exact ⟨1553, 13, prime_1553, prime_13, by norm_num⟩
  · exact ⟨1571, 5, prime_1571, prime_5, by norm_num⟩
  · exact ⟨1579, 2, prime_1579, prime_2, by norm_num⟩
  · exact ⟨1579, 3, prime_1579, prime_3, by norm_num⟩
  · exact ⟨1583, 2, prime_1583, prime_2, by norm_num⟩
  · exact ⟨1583, 3, prime_1583, prime_3, by norm_num⟩
  · exact ⟨1553, 19, prime_1553, prime_19, by norm_num⟩
  · exact ⟨1583, 5, prime_1583, prime_5, by norm_num⟩
  · exact ⟨1549, 23, prime_1549, prime_23, by norm_num⟩
  · exact ⟨1583, 7, prime_1583, prime_7, by norm_num⟩
  · exact ⟨1553, 23, prime_1553, prime_23, by norm_num⟩
  · exact ⟨1597, 2, prime_1597, prime_2, by norm_num⟩
  · exact ⟨1597, 3, prime_1597, prime_3, by norm_num⟩
  · exact ⟨1601, 2, prime_1601, prime_2, by norm_num⟩

private theorem lemoine_chunk_8 : ∀ k : ℕ, 803 ≤ k → k ≤ 902 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1601, 3, prime_1601, prime_3, by norm_num⟩
  · exact ⟨1583, 13, prime_1583, prime_13, by norm_num⟩
  · exact ⟨1607, 2, prime_1607, prime_2, by norm_num⟩
  · exact ⟨1609, 2, prime_1609, prime_2, by norm_num⟩
  · exact ⟨1609, 3, prime_1609, prime_3, by norm_num⟩
  · exact ⟨1613, 2, prime_1613, prime_2, by norm_num⟩
  · exact ⟨1613, 3, prime_1613, prime_3, by norm_num⟩
  · exact ⟨1607, 7, prime_1607, prime_7, by norm_num⟩
  · exact ⟨1619, 2, prime_1619, prime_2, by norm_num⟩
  · exact ⟨1621, 2, prime_1621, prime_2, by norm_num⟩
  · exact ⟨1621, 3, prime_1621, prime_3, by norm_num⟩
  · exact ⟨1619, 5, prime_1619, prime_5, by norm_num⟩
  · exact ⟨1627, 2, prime_1627, prime_2, by norm_num⟩
  · exact ⟨1627, 3, prime_1627, prime_3, by norm_num⟩
  · exact ⟨1621, 7, prime_1621, prime_7, by norm_num⟩
  · exact ⟨1627, 5, prime_1627, prime_5, by norm_num⟩
  · exact ⟨1613, 13, prime_1613, prime_13, by norm_num⟩
  · exact ⟨1637, 2, prime_1637, prime_2, by norm_num⟩
  · exact ⟨1637, 3, prime_1637, prime_3, by norm_num⟩
  · exact ⟨1619, 13, prime_1619, prime_13, by norm_num⟩
  · exact ⟨1637, 5, prime_1637, prime_5, by norm_num⟩
  · exact ⟨1627, 11, prime_1627, prime_11, by norm_num⟩
  · exact ⟨1637, 7, prime_1637, prime_7, by norm_num⟩
  · exact ⟨1627, 13, prime_1627, prime_13, by norm_num⟩
  · exact ⟨1621, 17, prime_1621, prime_17, by norm_num⟩
  · exact ⟨1619, 19, prime_1619, prime_19, by norm_num⟩
  · exact ⟨1637, 11, prime_1637, prime_11, by norm_num⟩
  · exact ⟨1657, 2, prime_1657, prime_2, by norm_num⟩
  · exact ⟨1657, 3, prime_1657, prime_3, by norm_num⟩
  · exact ⟨1627, 19, prime_1627, prime_19, by norm_num⟩
  · exact ⟨1663, 2, prime_1663, prime_2, by norm_num⟩
  · exact ⟨1663, 3, prime_1663, prime_3, by norm_num⟩
  · exact ⟨1667, 2, prime_1667, prime_2, by norm_num⟩
  · exact ⟨1669, 2, prime_1669, prime_2, by norm_num⟩
  · exact ⟨1669, 3, prime_1669, prime_3, by norm_num⟩
  · exact ⟨1667, 5, prime_1667, prime_5, by norm_num⟩
  · exact ⟨1669, 5, prime_1669, prime_5, by norm_num⟩
  · exact ⟨1667, 7, prime_1667, prime_7, by norm_num⟩
  · exact ⟨1669, 7, prime_1669, prime_7, by norm_num⟩
  · exact ⟨1663, 11, prime_1663, prime_11, by norm_num⟩
  · exact ⟨1613, 37, prime_1613, prime_37, by norm_num⟩
  · exact ⟨1667, 11, prime_1667, prime_11, by norm_num⟩
  · exact ⟨1669, 11, prime_1669, prime_11, by norm_num⟩
  · exact ⟨1667, 13, prime_1667, prime_13, by norm_num⟩
  · exact ⟨1669, 13, prime_1669, prime_13, by norm_num⟩
  · exact ⟨1693, 2, prime_1693, prime_2, by norm_num⟩
  · exact ⟨1693, 3, prime_1693, prime_3, by norm_num⟩
  · exact ⟨1697, 2, prime_1697, prime_2, by norm_num⟩
  · exact ⟨1699, 2, prime_1699, prime_2, by norm_num⟩
  · exact ⟨1699, 3, prime_1699, prime_3, by norm_num⟩
  · exact ⟨1697, 5, prime_1697, prime_5, by norm_num⟩
  · exact ⟨1699, 5, prime_1699, prime_5, by norm_num⟩
  · exact ⟨1697, 7, prime_1697, prime_7, by norm_num⟩
  · exact ⟨1709, 2, prime_1709, prime_2, by norm_num⟩
  · exact ⟨1709, 3, prime_1709, prime_3, by norm_num⟩
  · exact ⟨1583, 67, prime_1583, prime_67, by norm_num⟩
  · exact ⟨1709, 5, prime_1709, prime_5, by norm_num⟩
  · exact ⟨1699, 11, prime_1699, prime_11, by norm_num⟩
  · exact ⟨1709, 7, prime_1709, prime_7, by norm_num⟩
  · exact ⟨1721, 2, prime_1721, prime_2, by norm_num⟩
  · exact ⟨1723, 2, prime_1723, prime_2, by norm_num⟩
  · exact ⟨1723, 3, prime_1723, prime_3, by norm_num⟩
  · exact ⟨1721, 5, prime_1721, prime_5, by norm_num⟩
  · exact ⟨1723, 5, prime_1723, prime_5, by norm_num⟩
  · exact ⟨1721, 7, prime_1721, prime_7, by norm_num⟩
  · exact ⟨1733, 2, prime_1733, prime_2, by norm_num⟩
  · exact ⟨1733, 3, prime_1733, prime_3, by norm_num⟩
  · exact ⟨1667, 37, prime_1667, prime_37, by norm_num⟩
  · exact ⟨1733, 5, prime_1733, prime_5, by norm_num⟩
  · exact ⟨1741, 2, prime_1741, prime_2, by norm_num⟩
  · exact ⟨1741, 3, prime_1741, prime_3, by norm_num⟩
  · exact ⟨1723, 13, prime_1723, prime_13, by norm_num⟩
  · exact ⟨1747, 2, prime_1747, prime_2, by norm_num⟩
  · exact ⟨1747, 3, prime_1747, prime_3, by norm_num⟩
  · exact ⟨1741, 7, prime_1741, prime_7, by norm_num⟩
  · exact ⟨1753, 2, prime_1753, prime_2, by norm_num⟩
  · exact ⟨1753, 3, prime_1753, prime_3, by norm_num⟩
  · exact ⟨1747, 7, prime_1747, prime_7, by norm_num⟩
  · exact ⟨1759, 2, prime_1759, prime_2, by norm_num⟩
  · exact ⟨1759, 3, prime_1759, prime_3, by norm_num⟩
  · exact ⟨1753, 7, prime_1753, prime_7, by norm_num⟩
  · exact ⟨1759, 5, prime_1759, prime_5, by norm_num⟩
  · exact ⟨1733, 19, prime_1733, prime_19, by norm_num⟩
  · exact ⟨1759, 7, prime_1759, prime_7, by norm_num⟩
  · exact ⟨1753, 11, prime_1753, prime_11, by norm_num⟩
  · exact ⟨1619, 79, prime_1619, prime_79, by norm_num⟩
  · exact ⟨1753, 13, prime_1753, prime_13, by norm_num⟩
  · exact ⟨1777, 2, prime_1777, prime_2, by norm_num⟩
  · exact ⟨1777, 3, prime_1777, prime_3, by norm_num⟩
  · exact ⟨1759, 13, prime_1759, prime_13, by norm_num⟩
  · exact ⟨1783, 2, prime_1783, prime_2, by norm_num⟩
  · exact ⟨1783, 3, prime_1783, prime_3, by norm_num⟩
  · exact ⟨1787, 2, prime_1787, prime_2, by norm_num⟩
  · exact ⟨1789, 2, prime_1789, prime_2, by norm_num⟩
  · exact ⟨1789, 3, prime_1789, prime_3, by norm_num⟩
  · exact ⟨1787, 5, prime_1787, prime_5, by norm_num⟩
  · exact ⟨1789, 5, prime_1789, prime_5, by norm_num⟩
  · exact ⟨1787, 7, prime_1787, prime_7, by norm_num⟩
  · exact ⟨1789, 7, prime_1789, prime_7, by norm_num⟩
  · exact ⟨1801, 2, prime_1801, prime_2, by norm_num⟩

private theorem lemoine_chunk_9 : ∀ k : ℕ, 903 ≤ k → k ≤ 1002 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨1801, 3, prime_1801, prime_3, by norm_num⟩
  · exact ⟨1787, 11, prime_1787, prime_11, by norm_num⟩
  · exact ⟨1801, 5, prime_1801, prime_5, by norm_num⟩
  · exact ⟨1787, 13, prime_1787, prime_13, by norm_num⟩
  · exact ⟨1811, 2, prime_1811, prime_2, by norm_num⟩
  · exact ⟨1811, 3, prime_1811, prime_3, by norm_num⟩
  · exact ⟨1733, 43, prime_1733, prime_43, by norm_num⟩
  · exact ⟨1811, 5, prime_1811, prime_5, by norm_num⟩
  · exact ⟨1801, 11, prime_1801, prime_11, by norm_num⟩
  · exact ⟨1811, 7, prime_1811, prime_7, by norm_num⟩
  · exact ⟨1823, 2, prime_1823, prime_2, by norm_num⟩
  · exact ⟨1823, 3, prime_1823, prime_3, by norm_num⟩
  · exact ⟨1709, 61, prime_1709, prime_61, by norm_num⟩
  · exact ⟨1823, 5, prime_1823, prime_5, by norm_num⟩
  · exact ⟨1831, 2, prime_1831, prime_2, by norm_num⟩
  · exact ⟨1831, 3, prime_1831, prime_3, by norm_num⟩
  · exact ⟨1801, 19, prime_1801, prime_19, by norm_num⟩
  · exact ⟨1831, 5, prime_1831, prime_5, by norm_num⟩
  · exact ⟨1721, 61, prime_1721, prime_61, by norm_num⟩
  · exact ⟨1831, 7, prime_1831, prime_7, by norm_num⟩
  · exact ⟨1801, 23, prime_1801, prime_23, by norm_num⟩
  · exact ⟨1823, 13, prime_1823, prime_13, by norm_num⟩
  · exact ⟨1847, 2, prime_1847, prime_2, by norm_num⟩
  · exact ⟨1847, 3, prime_1847, prime_3, by norm_num⟩
  · exact ⟨1733, 61, prime_1733, prime_61, by norm_num⟩
  · exact ⟨1847, 5, prime_1847, prime_5, by norm_num⟩
  · exact ⟨1801, 29, prime_1801, prime_29, by norm_num⟩
  · exact ⟨1847, 7, prime_1847, prime_7, by norm_num⟩
  · exact ⟨1801, 31, prime_1801, prime_31, by norm_num⟩
  · exact ⟨1861, 2, prime_1861, prime_2, by norm_num⟩
  · exact ⟨1861, 3, prime_1861, prime_3, by norm_num⟩
  · exact ⟨1847, 11, prime_1847, prime_11, by norm_num⟩
  · exact ⟨1867, 2, prime_1867, prime_2, by norm_num⟩
  · exact ⟨1867, 3, prime_1867, prime_3, by norm_num⟩
  · exact ⟨1871, 2, prime_1871, prime_2, by norm_num⟩
  · exact ⟨1873, 2, prime_1873, prime_2, by norm_num⟩
  · exact ⟨1873, 3, prime_1873, prime_3, by norm_num⟩
  · exact ⟨1877, 2, prime_1877, prime_2, by norm_num⟩
  · exact ⟨1879, 2, prime_1879, prime_2, by norm_num⟩
  · exact ⟨1879, 3, prime_1879, prime_3, by norm_num⟩
  · exact ⟨1877, 5, prime_1877, prime_5, by norm_num⟩
  · exact ⟨1879, 5, prime_1879, prime_5, by norm_num⟩
  · exact ⟨1877, 7, prime_1877, prime_7, by norm_num⟩
  · exact ⟨1889, 2, prime_1889, prime_2, by norm_num⟩
  · exact ⟨1889, 3, prime_1889, prime_3, by norm_num⟩
  · exact ⟨1871, 13, prime_1871, prime_13, by norm_num⟩
  · exact ⟨1889, 5, prime_1889, prime_5, by norm_num⟩
  · exact ⟨1879, 11, prime_1879, prime_11, by norm_num⟩
  · exact ⟨1889, 7, prime_1889, prime_7, by norm_num⟩
  · exact ⟨1901, 2, prime_1901, prime_2, by norm_num⟩
  · exact ⟨1901, 3, prime_1901, prime_3, by norm_num⟩
  · exact ⟨1871, 19, prime_1871, prime_19, by norm_num⟩
  · exact ⟨1907, 2, prime_1907, prime_2, by norm_num⟩
  · exact ⟨1907, 3, prime_1907, prime_3, by norm_num⟩
  · exact ⟨1901, 7, prime_1901, prime_7, by norm_num⟩
  · exact ⟨1913, 2, prime_1913, prime_2, by norm_num⟩
  · exact ⟨1913, 3, prime_1913, prime_3, by norm_num⟩
  · exact ⟨1907, 7, prime_1907, prime_7, by norm_num⟩
  · exact ⟨1913, 5, prime_1913, prime_5, by norm_num⟩
  · exact ⟨1879, 23, prime_1879, prime_23, by norm_num⟩
  · exact ⟨1913, 7, prime_1913, prime_7, by norm_num⟩
  · exact ⟨1907, 11, prime_1907, prime_11, by norm_num⟩
  · exact ⟨1873, 29, prime_1873, prime_29, by norm_num⟩
  · exact ⟨1907, 13, prime_1907, prime_13, by norm_num⟩
  · exact ⟨1931, 2, prime_1931, prime_2, by norm_num⟩
  · exact ⟨1933, 2, prime_1933, prime_2, by norm_num⟩
  · exact ⟨1933, 3, prime_1933, prime_3, by norm_num⟩
  · exact ⟨1931, 5, prime_1931, prime_5, by norm_num⟩
  · exact ⟨1933, 5, prime_1933, prime_5, by norm_num⟩
  · exact ⟨1931, 7, prime_1931, prime_7, by norm_num⟩
  · exact ⟨1933, 7, prime_1933, prime_7, by norm_num⟩
  · exact ⟨1867, 41, prime_1867, prime_41, by norm_num⟩
  · exact ⟨1913, 19, prime_1913, prime_19, by norm_num⟩
  · exact ⟨1949, 2, prime_1949, prime_2, by norm_num⟩
  · exact ⟨1951, 2, prime_1951, prime_2, by norm_num⟩
  · exact ⟨1951, 3, prime_1951, prime_3, by norm_num⟩
  · exact ⟨1949, 5, prime_1949, prime_5, by norm_num⟩
  · exact ⟨1951, 5, prime_1951, prime_5, by norm_num⟩
  · exact ⟨1949, 7, prime_1949, prime_7, by norm_num⟩
  · exact ⟨1951, 7, prime_1951, prime_7, by norm_num⟩
  · exact ⟨1933, 17, prime_1933, prime_17, by norm_num⟩
  · exact ⟨1931, 19, prime_1931, prime_19, by norm_num⟩
  · exact ⟨1949, 11, prime_1949, prime_11, by norm_num⟩
  · exact ⟨1951, 11, prime_1951, prime_11, by norm_num⟩
  · exact ⟨1949, 13, prime_1949, prime_13, by norm_num⟩
  · exact ⟨1973, 2, prime_1973, prime_2, by norm_num⟩
  · exact ⟨1973, 3, prime_1973, prime_3, by norm_num⟩
  · exact ⟨1907, 37, prime_1907, prime_37, by norm_num⟩
  · exact ⟨1979, 2, prime_1979, prime_2, by norm_num⟩
  · exact ⟨1979, 3, prime_1979, prime_3, by norm_num⟩
  · exact ⟨1973, 7, prime_1973, prime_7, by norm_num⟩
  · exact ⟨1979, 5, prime_1979, prime_5, by norm_num⟩
  · exact ⟨1987, 2, prime_1987, prime_2, by norm_num⟩
  · exact ⟨1987, 3, prime_1987, prime_3, by norm_num⟩
  · exact ⟨1973, 11, prime_1973, prime_11, by norm_num⟩
  · exact ⟨1993, 2, prime_1993, prime_2, by norm_num⟩
  · exact ⟨1993, 3, prime_1993, prime_3, by norm_num⟩
  · exact ⟨1997, 2, prime_1997, prime_2, by norm_num⟩
  · exact ⟨1999, 2, prime_1999, prime_2, by norm_num⟩
  · exact ⟨1999, 3, prime_1999, prime_3, by norm_num⟩

private theorem lemoine_chunk_10 : ∀ k : ℕ, 1003 ≤ k → k ≤ 1102 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2003, 2, prime_2003, prime_2, by norm_num⟩
  · exact ⟨2003, 3, prime_2003, prime_3, by norm_num⟩
  · exact ⟨1997, 7, prime_1997, prime_7, by norm_num⟩
  · exact ⟨2003, 5, prime_2003, prime_5, by norm_num⟩
  · exact ⟨2011, 2, prime_2011, prime_2, by norm_num⟩
  · exact ⟨2011, 3, prime_2011, prime_3, by norm_num⟩
  · exact ⟨1997, 11, prime_1997, prime_11, by norm_num⟩
  · exact ⟨2017, 2, prime_2017, prime_2, by norm_num⟩
  · exact ⟨2017, 3, prime_2017, prime_3, by norm_num⟩
  · exact ⟨2011, 7, prime_2011, prime_7, by norm_num⟩
  · exact ⟨2017, 5, prime_2017, prime_5, by norm_num⟩
  · exact ⟨2003, 13, prime_2003, prime_13, by norm_num⟩
  · exact ⟨2027, 2, prime_2027, prime_2, by norm_num⟩
  · exact ⟨2029, 2, prime_2029, prime_2, by norm_num⟩
  · exact ⟨2029, 3, prime_2029, prime_3, by norm_num⟩
  · exact ⟨2027, 5, prime_2027, prime_5, by norm_num⟩
  · exact ⟨2029, 5, prime_2029, prime_5, by norm_num⟩
  · exact ⟨2027, 7, prime_2027, prime_7, by norm_num⟩
  · exact ⟨2039, 2, prime_2039, prime_2, by norm_num⟩
  · exact ⟨2039, 3, prime_2039, prime_3, by norm_num⟩
  · exact ⟨1973, 37, prime_1973, prime_37, by norm_num⟩
  · exact ⟨2039, 5, prime_2039, prime_5, by norm_num⟩
  · exact ⟨2029, 11, prime_2029, prime_11, by norm_num⟩
  · exact ⟨2039, 7, prime_2039, prime_7, by norm_num⟩
  · exact ⟨2029, 13, prime_2029, prime_13, by norm_num⟩
  · exact ⟨2053, 2, prime_2053, prime_2, by norm_num⟩
  · exact ⟨2053, 3, prime_2053, prime_3, by norm_num⟩
  · exact ⟨2039, 11, prime_2039, prime_11, by norm_num⟩
  · exact ⟨2053, 5, prime_2053, prime_5, by norm_num⟩
  · exact ⟨2039, 13, prime_2039, prime_13, by norm_num⟩
  · exact ⟨2063, 2, prime_2063, prime_2, by norm_num⟩
  · exact ⟨2063, 3, prime_2063, prime_3, by norm_num⟩
  · exact ⟨1997, 37, prime_1997, prime_37, by norm_num⟩
  · exact ⟨2069, 2, prime_2069, prime_2, by norm_num⟩
  · exact ⟨2069, 3, prime_2069, prime_3, by norm_num⟩
  · exact ⟨2063, 7, prime_2063, prime_7, by norm_num⟩
  · exact ⟨2069, 5, prime_2069, prime_5, by norm_num⟩
  · exact ⟨1999, 41, prime_1999, prime_41, by norm_num⟩
  · exact ⟨2069, 7, prime_2069, prime_7, by norm_num⟩
  · exact ⟨2081, 2, prime_2081, prime_2, by norm_num⟩
  · exact ⟨2083, 2, prime_2083, prime_2, by norm_num⟩
  · exact ⟨2083, 3, prime_2083, prime_3, by norm_num⟩
  · exact ⟨2087, 2, prime_2087, prime_2, by norm_num⟩
  · exact ⟨2089, 2, prime_2089, prime_2, by norm_num⟩
  · exact ⟨2089, 3, prime_2089, prime_3, by norm_num⟩
  · exact ⟨2087, 5, prime_2087, prime_5, by norm_num⟩
  · exact ⟨2089, 5, prime_2089, prime_5, by norm_num⟩
  · exact ⟨2087, 7, prime_2087, prime_7, by norm_num⟩
  · exact ⟨2099, 2, prime_2099, prime_2, by norm_num⟩
  · exact ⟨2099, 3, prime_2099, prime_3, by norm_num⟩
  · exact ⟨2081, 13, prime_2081, prime_13, by norm_num⟩
  · exact ⟨2099, 5, prime_2099, prime_5, by norm_num⟩
  · exact ⟨2089, 11, prime_2089, prime_11, by norm_num⟩
  · exact ⟨2099, 7, prime_2099, prime_7, by norm_num⟩
  · exact ⟨2111, 2, prime_2111, prime_2, by norm_num⟩
  · exact ⟨2113, 2, prime_2113, prime_2, by norm_num⟩
  · exact ⟨2113, 3, prime_2113, prime_3, by norm_num⟩
  · exact ⟨2111, 5, prime_2111, prime_5, by norm_num⟩
  · exact ⟨2113, 5, prime_2113, prime_5, by norm_num⟩
  · exact ⟨2111, 7, prime_2111, prime_7, by norm_num⟩
  · exact ⟨2113, 7, prime_2113, prime_7, by norm_num⟩
  · exact ⟨2083, 23, prime_2083, prime_23, by norm_num⟩
  · exact ⟨2069, 31, prime_2069, prime_31, by norm_num⟩
  · exact ⟨2129, 2, prime_2129, prime_2, by norm_num⟩
  · exact ⟨2131, 2, prime_2131, prime_2, by norm_num⟩
  · exact ⟨2131, 3, prime_2131, prime_3, by norm_num⟩
  · exact ⟨2129, 5, prime_2129, prime_5, by norm_num⟩
  · exact ⟨2137, 2, prime_2137, prime_2, by norm_num⟩
  · exact ⟨2137, 3, prime_2137, prime_3, by norm_num⟩
  · exact ⟨2141, 2, prime_2141, prime_2, by norm_num⟩
  · exact ⟨2143, 2, prime_2143, prime_2, by norm_num⟩
  · exact ⟨2143, 3, prime_2143, prime_3, by norm_num⟩
  · exact ⟨2141, 5, prime_2141, prime_5, by norm_num⟩
  · exact ⟨2143, 5, prime_2143, prime_5, by norm_num⟩
  · exact ⟨2141, 7, prime_2141, prime_7, by norm_num⟩
  · exact ⟨2153, 2, prime_2153, prime_2, by norm_num⟩
  · exact ⟨2153, 3, prime_2153, prime_3, by norm_num⟩
  · exact ⟨2099, 31, prime_2099, prime_31, by norm_num⟩
  · exact ⟨2153, 5, prime_2153, prime_5, by norm_num⟩
  · exact ⟨2161, 2, prime_2161, prime_2, by norm_num⟩
  · exact ⟨2161, 3, prime_2161, prime_3, by norm_num⟩
  · exact ⟨2143, 13, prime_2143, prime_13, by norm_num⟩
  · exact ⟨2161, 5, prime_2161, prime_5, by norm_num⟩
  · exact ⟨2111, 31, prime_2111, prime_31, by norm_num⟩
  · exact ⟨2161, 7, prime_2161, prime_7, by norm_num⟩
  · exact ⟨2143, 17, prime_2143, prime_17, by norm_num⟩
  · exact ⟨2153, 13, prime_2153, prime_13, by norm_num⟩
  · exact ⟨2143, 19, prime_2143, prime_19, by norm_num⟩
  · exact ⟨2179, 2, prime_2179, prime_2, by norm_num⟩
  · exact ⟨2179, 3, prime_2179, prime_3, by norm_num⟩
  · exact ⟨2161, 13, prime_2161, prime_13, by norm_num⟩
  · exact ⟨2179, 5, prime_2179, prime_5, by norm_num⟩
  · exact ⟨2153, 19, prime_2153, prime_19, by norm_num⟩
  · exact ⟨2179, 7, prime_2179, prime_7, by norm_num⟩
  · exact ⟨2161, 17, prime_2161, prime_17, by norm_num⟩
  · exact ⟨2111, 43, prime_2111, prime_43, by norm_num⟩
  · exact ⟨2161, 19, prime_2161, prime_19, by norm_num⟩
  · exact ⟨2179, 11, prime_2179, prime_11, by norm_num⟩
  · exact ⟨2141, 31, prime_2141, prime_31, by norm_num⟩
  · exact ⟨2179, 13, prime_2179, prime_13, by norm_num⟩

private theorem lemoine_chunk_11 : ∀ k : ℕ, 1103 ≤ k → k ≤ 1202 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2203, 2, prime_2203, prime_2, by norm_num⟩
  · exact ⟨2203, 3, prime_2203, prime_3, by norm_num⟩
  · exact ⟨2207, 2, prime_2207, prime_2, by norm_num⟩
  · exact ⟨2207, 3, prime_2207, prime_3, by norm_num⟩
  · exact ⟨2153, 31, prime_2153, prime_31, by norm_num⟩
  · exact ⟨2213, 2, prime_2213, prime_2, by norm_num⟩
  · exact ⟨2213, 3, prime_2213, prime_3, by norm_num⟩
  · exact ⟨2207, 7, prime_2207, prime_7, by norm_num⟩
  · exact ⟨2213, 5, prime_2213, prime_5, by norm_num⟩
  · exact ⟨2221, 2, prime_2221, prime_2, by norm_num⟩
  · exact ⟨2221, 3, prime_2221, prime_3, by norm_num⟩
  · exact ⟨2207, 11, prime_2207, prime_11, by norm_num⟩
  · exact ⟨2221, 5, prime_2221, prime_5, by norm_num⟩
  · exact ⟨2207, 13, prime_2207, prime_13, by norm_num⟩
  · exact ⟨2221, 7, prime_2221, prime_7, by norm_num⟩
  · exact ⟨2203, 17, prime_2203, prime_17, by norm_num⟩
  · exact ⟨2213, 13, prime_2213, prime_13, by norm_num⟩
  · exact ⟨2237, 2, prime_2237, prime_2, by norm_num⟩
  · exact ⟨2239, 2, prime_2239, prime_2, by norm_num⟩
  · exact ⟨2239, 3, prime_2239, prime_3, by norm_num⟩
  · exact ⟨2243, 2, prime_2243, prime_2, by norm_num⟩
  · exact ⟨2243, 3, prime_2243, prime_3, by norm_num⟩
  · exact ⟨2237, 7, prime_2237, prime_7, by norm_num⟩
  · exact ⟨2243, 5, prime_2243, prime_5, by norm_num⟩
  · exact ⟨2251, 2, prime_2251, prime_2, by norm_num⟩
  · exact ⟨2251, 3, prime_2251, prime_3, by norm_num⟩
  · exact ⟨2237, 11, prime_2237, prime_11, by norm_num⟩
  · exact ⟨2251, 5, prime_2251, prime_5, by norm_num⟩
  · exact ⟨2237, 13, prime_2237, prime_13, by norm_num⟩
  · exact ⟨2251, 7, prime_2251, prime_7, by norm_num⟩
  · exact ⟨2221, 23, prime_2221, prime_23, by norm_num⟩
  · exact ⟨2243, 13, prime_2243, prime_13, by norm_num⟩
  · exact ⟨2267, 2, prime_2267, prime_2, by norm_num⟩
  · exact ⟨2269, 2, prime_2269, prime_2, by norm_num⟩
  · exact ⟨2269, 3, prime_2269, prime_3, by norm_num⟩
  · exact ⟨2273, 2, prime_2273, prime_2, by norm_num⟩
  · exact ⟨2273, 3, prime_2273, prime_3, by norm_num⟩
  · exact ⟨2267, 7, prime_2267, prime_7, by norm_num⟩
  · exact ⟨2273, 5, prime_2273, prime_5, by norm_num⟩
  · exact ⟨2281, 2, prime_2281, prime_2, by norm_num⟩
  · exact ⟨2281, 3, prime_2281, prime_3, by norm_num⟩
  · exact ⟨2267, 11, prime_2267, prime_11, by norm_num⟩
  · exact ⟨2287, 2, prime_2287, prime_2, by norm_num⟩
  · exact ⟨2287, 3, prime_2287, prime_3, by norm_num⟩
  · exact ⟨2281, 7, prime_2281, prime_7, by norm_num⟩
  · exact ⟨2293, 2, prime_2293, prime_2, by norm_num⟩
  · exact ⟨2293, 3, prime_2293, prime_3, by norm_num⟩
  · exact ⟨2297, 2, prime_2297, prime_2, by norm_num⟩
  · exact ⟨2297, 3, prime_2297, prime_3, by norm_num⟩
  · exact ⟨2267, 19, prime_2267, prime_19, by norm_num⟩
  · exact ⟨2297, 5, prime_2297, prime_5, by norm_num⟩
  · exact ⟨2287, 11, prime_2287, prime_11, by norm_num⟩
  · exact ⟨2297, 7, prime_2297, prime_7, by norm_num⟩
  · exact ⟨2309, 2, prime_2309, prime_2, by norm_num⟩
  · exact ⟨2311, 2, prime_2311, prime_2, by norm_num⟩
  · exact ⟨2311, 3, prime_2311, prime_3, by norm_num⟩
  · exact ⟨2309, 5, prime_2309, prime_5, by norm_num⟩
  · exact ⟨2311, 5, prime_2311, prime_5, by norm_num⟩
  · exact ⟨2309, 7, prime_2309, prime_7, by norm_num⟩
  · exact ⟨2311, 7, prime_2311, prime_7, by norm_num⟩
  · exact ⟨2293, 17, prime_2293, prime_17, by norm_num⟩
  · exact ⟨2267, 31, prime_2267, prime_31, by norm_num⟩
  · exact ⟨2309, 11, prime_2309, prime_11, by norm_num⟩
  · exact ⟨2311, 11, prime_2311, prime_11, by norm_num⟩
  · exact ⟨2309, 13, prime_2309, prime_13, by norm_num⟩
  · exact ⟨2333, 2, prime_2333, prime_2, by norm_num⟩
  · exact ⟨2333, 3, prime_2333, prime_3, by norm_num⟩
  · exact ⟨2267, 37, prime_2267, prime_37, by norm_num⟩
  · exact ⟨2339, 2, prime_2339, prime_2, by norm_num⟩
  · exact ⟨2341, 2, prime_2341, prime_2, by norm_num⟩
  · exact ⟨2341, 3, prime_2341, prime_3, by norm_num⟩
  · exact ⟨2339, 5, prime_2339, prime_5, by norm_num⟩
  · exact ⟨2347, 2, prime_2347, prime_2, by norm_num⟩
  · exact ⟨2347, 3, prime_2347, prime_3, by norm_num⟩
  · exact ⟨2351, 2, prime_2351, prime_2, by norm_num⟩
  · exact ⟨2351, 3, prime_2351, prime_3, by norm_num⟩
  · exact ⟨2333, 13, prime_2333, prime_13, by norm_num⟩
  · exact ⟨2357, 2, prime_2357, prime_2, by norm_num⟩
  · exact ⟨2357, 3, prime_2357, prime_3, by norm_num⟩
  · exact ⟨2351, 7, prime_2351, prime_7, by norm_num⟩
  · exact ⟨2357, 5, prime_2357, prime_5, by norm_num⟩
  · exact ⟨2347, 11, prime_2347, prime_11, by norm_num⟩
  · exact ⟨2357, 7, prime_2357, prime_7, by norm_num⟩
  · exact ⟨2351, 11, prime_2351, prime_11, by norm_num⟩
  · exact ⟨2371, 2, prime_2371, prime_2, by norm_num⟩
  · exact ⟨2371, 3, prime_2371, prime_3, by norm_num⟩
  · exact ⟨2357, 11, prime_2357, prime_11, by norm_num⟩
  · exact ⟨2377, 2, prime_2377, prime_2, by norm_num⟩
  · exact ⟨2377, 3, prime_2377, prime_3, by norm_num⟩
  · exact ⟨2381, 2, prime_2381, prime_2, by norm_num⟩
  · exact ⟨2383, 2, prime_2383, prime_2, by norm_num⟩
  · exact ⟨2383, 3, prime_2383, prime_3, by norm_num⟩
  · exact ⟨2381, 5, prime_2381, prime_5, by norm_num⟩
  · exact ⟨2389, 2, prime_2389, prime_2, by norm_num⟩
  · exact ⟨2389, 3, prime_2389, prime_3, by norm_num⟩
  · exact ⟨2393, 2, prime_2393, prime_2, by norm_num⟩
  · exact ⟨2393, 3, prime_2393, prime_3, by norm_num⟩
  · exact ⟨2339, 31, prime_2339, prime_31, by norm_num⟩
  · exact ⟨2399, 2, prime_2399, prime_2, by norm_num⟩
  · exact ⟨2399, 3, prime_2399, prime_3, by norm_num⟩

private theorem lemoine_chunk_12 : ∀ k : ℕ, 1203 ≤ k → k ≤ 1302 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2393, 7, prime_2393, prime_7, by norm_num⟩
  · exact ⟨2399, 5, prime_2399, prime_5, by norm_num⟩
  · exact ⟨2389, 11, prime_2389, prime_11, by norm_num⟩
  · exact ⟨2399, 7, prime_2399, prime_7, by norm_num⟩
  · exact ⟨2411, 2, prime_2411, prime_2, by norm_num⟩
  · exact ⟨2411, 3, prime_2411, prime_3, by norm_num⟩
  · exact ⟨2393, 13, prime_2393, prime_13, by norm_num⟩
  · exact ⟨2417, 2, prime_2417, prime_2, by norm_num⟩
  · exact ⟨2417, 3, prime_2417, prime_3, by norm_num⟩
  · exact ⟨2411, 7, prime_2411, prime_7, by norm_num⟩
  · exact ⟨2423, 2, prime_2423, prime_2, by norm_num⟩
  · exact ⟨2423, 3, prime_2423, prime_3, by norm_num⟩
  · exact ⟨2417, 7, prime_2417, prime_7, by norm_num⟩
  · exact ⟨2423, 5, prime_2423, prime_5, by norm_num⟩
  · exact ⟨2389, 23, prime_2389, prime_23, by norm_num⟩
  · exact ⟨2423, 7, prime_2423, prime_7, by norm_num⟩
  · exact ⟨2417, 11, prime_2417, prime_11, by norm_num⟩
  · exact ⟨2437, 2, prime_2437, prime_2, by norm_num⟩
  · exact ⟨2437, 3, prime_2437, prime_3, by norm_num⟩
  · exact ⟨2441, 2, prime_2441, prime_2, by norm_num⟩
  · exact ⟨2441, 3, prime_2441, prime_3, by norm_num⟩
  · exact ⟨2423, 13, prime_2423, prime_13, by norm_num⟩
  · exact ⟨2447, 2, prime_2447, prime_2, by norm_num⟩
  · exact ⟨2447, 3, prime_2447, prime_3, by norm_num⟩
  · exact ⟨2441, 7, prime_2441, prime_7, by norm_num⟩
  · exact ⟨2447, 5, prime_2447, prime_5, by norm_num⟩
  · exact ⟨2437, 11, prime_2437, prime_11, by norm_num⟩
  · exact ⟨2447, 7, prime_2447, prime_7, by norm_num⟩
  · exact ⟨2459, 2, prime_2459, prime_2, by norm_num⟩
  · exact ⟨2459, 3, prime_2459, prime_3, by norm_num⟩
  · exact ⟨2441, 13, prime_2441, prime_13, by norm_num⟩
  · exact ⟨2459, 5, prime_2459, prime_5, by norm_num⟩
  · exact ⟨2467, 2, prime_2467, prime_2, by norm_num⟩
  · exact ⟨2467, 3, prime_2467, prime_3, by norm_num⟩
  · exact ⟨2441, 17, prime_2441, prime_17, by norm_num⟩
  · exact ⟨2473, 2, prime_2473, prime_2, by norm_num⟩
  · exact ⟨2473, 3, prime_2473, prime_3, by norm_num⟩
  · exact ⟨2477, 2, prime_2477, prime_2, by norm_num⟩
  · exact ⟨2477, 3, prime_2477, prime_3, by norm_num⟩
  · exact ⟨2459, 13, prime_2459, prime_13, by norm_num⟩
  · exact ⟨2477, 5, prime_2477, prime_5, by norm_num⟩
  · exact ⟨2467, 11, prime_2467, prime_11, by norm_num⟩
  · exact ⟨2477, 7, prime_2477, prime_7, by norm_num⟩
  · exact ⟨2467, 13, prime_2467, prime_13, by norm_num⟩
  · exact ⟨2473, 11, prime_2473, prime_11, by norm_num⟩
  · exact ⟨2459, 19, prime_2459, prime_19, by norm_num⟩
  · exact ⟨2477, 11, prime_2477, prime_11, by norm_num⟩
  · exact ⟨2467, 17, prime_2467, prime_17, by norm_num⟩
  · exact ⟨2477, 13, prime_2477, prime_13, by norm_num⟩
  · exact ⟨2467, 19, prime_2467, prime_19, by norm_num⟩
  · exact ⟨2503, 2, prime_2503, prime_2, by norm_num⟩
  · exact ⟨2503, 3, prime_2503, prime_3, by norm_num⟩
  · exact ⟨2477, 17, prime_2477, prime_17, by norm_num⟩
  · exact ⟨2503, 5, prime_2503, prime_5, by norm_num⟩
  · exact ⟨2477, 19, prime_2477, prime_19, by norm_num⟩
  · exact ⟨2503, 7, prime_2503, prime_7, by norm_num⟩
  · exact ⟨2473, 23, prime_2473, prime_23, by norm_num⟩
  · exact ⟨2459, 31, prime_2459, prime_31, by norm_num⟩
  · exact ⟨2477, 23, prime_2477, prime_23, by norm_num⟩
  · exact ⟨2521, 2, prime_2521, prime_2, by norm_num⟩
  · exact ⟨2521, 3, prime_2521, prime_3, by norm_num⟩
  · exact ⟨2503, 13, prime_2503, prime_13, by norm_num⟩
  · exact ⟨2521, 5, prime_2521, prime_5, by norm_num⟩
  · exact ⟨2459, 37, prime_2459, prime_37, by norm_num⟩
  · exact ⟨2531, 2, prime_2531, prime_2, by norm_num⟩
  · exact ⟨2531, 3, prime_2531, prime_3, by norm_num⟩
  · exact ⟨2477, 31, prime_2477, prime_31, by norm_num⟩
  · exact ⟨2531, 5, prime_2531, prime_5, by norm_num⟩
  · exact ⟨2539, 2, prime_2539, prime_2, by norm_num⟩
  · exact ⟨2539, 3, prime_2539, prime_3, by norm_num⟩
  · exact ⟨2543, 2, prime_2543, prime_2, by norm_num⟩
  · exact ⟨2543, 3, prime_2543, prime_3, by norm_num⟩
  · exact ⟨2477, 37, prime_2477, prime_37, by norm_num⟩
  · exact ⟨2549, 2, prime_2549, prime_2, by norm_num⟩
  · exact ⟨2551, 2, prime_2551, prime_2, by norm_num⟩
  · exact ⟨2551, 3, prime_2551, prime_3, by norm_num⟩
  · exact ⟨2549, 5, prime_2549, prime_5, by norm_num⟩
  · exact ⟨2557, 2, prime_2557, prime_2, by norm_num⟩
  · exact ⟨2557, 3, prime_2557, prime_3, by norm_num⟩
  · exact ⟨2551, 7, prime_2551, prime_7, by norm_num⟩
  · exact ⟨2557, 5, prime_2557, prime_5, by norm_num⟩
  · exact ⟨2543, 13, prime_2543, prime_13, by norm_num⟩
  · exact ⟨2557, 7, prime_2557, prime_7, by norm_num⟩
  · exact ⟨2551, 11, prime_2551, prime_11, by norm_num⟩
  · exact ⟨2549, 13, prime_2549, prime_13, by norm_num⟩
  · exact ⟨2551, 13, prime_2551, prime_13, by norm_num⟩
  · exact ⟨2557, 11, prime_2557, prime_11, by norm_num⟩
  · exact ⟨2543, 19, prime_2543, prime_19, by norm_num⟩
  · exact ⟨2579, 2, prime_2579, prime_2, by norm_num⟩
  · exact ⟨2579, 3, prime_2579, prime_3, by norm_num⟩
  · exact ⟨2549, 19, prime_2549, prime_19, by norm_num⟩
  · exact ⟨2579, 5, prime_2579, prime_5, by norm_num⟩
  · exact ⟨2557, 17, prime_2557, prime_17, by norm_num⟩
  · exact ⟨2579, 7, prime_2579, prime_7, by norm_num⟩
  · exact ⟨2591, 2, prime_2591, prime_2, by norm_num⟩
  · exact ⟨2593, 2, prime_2593, prime_2, by norm_num⟩
  · exact ⟨2593, 3, prime_2593, prime_3, by norm_num⟩
  · exact ⟨2591, 5, prime_2591, prime_5, by norm_num⟩
  · exact ⟨2593, 5, prime_2593, prime_5, by norm_num⟩
  · exact ⟨2591, 7, prime_2591, prime_7, by norm_num⟩

private theorem lemoine_chunk_13 : ∀ k : ℕ, 1303 ≤ k → k ≤ 1402 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2593, 7, prime_2593, prime_7, by norm_num⟩
  · exact ⟨2551, 29, prime_2551, prime_29, by norm_num⟩
  · exact ⟨2549, 31, prime_2549, prime_31, by norm_num⟩
  · exact ⟨2609, 2, prime_2609, prime_2, by norm_num⟩
  · exact ⟨2609, 3, prime_2609, prime_3, by norm_num⟩
  · exact ⟨2591, 13, prime_2591, prime_13, by norm_num⟩
  · exact ⟨2609, 5, prime_2609, prime_5, by norm_num⟩
  · exact ⟨2617, 2, prime_2617, prime_2, by norm_num⟩
  · exact ⟨2617, 3, prime_2617, prime_3, by norm_num⟩
  · exact ⟨2621, 2, prime_2621, prime_2, by norm_num⟩
  · exact ⟨2621, 3, prime_2621, prime_3, by norm_num⟩
  · exact ⟨2591, 19, prime_2591, prime_19, by norm_num⟩
  · exact ⟨2621, 5, prime_2621, prime_5, by norm_num⟩
  · exact ⟨2551, 41, prime_2551, prime_41, by norm_num⟩
  · exact ⟨2621, 7, prime_2621, prime_7, by norm_num⟩
  · exact ⟨2633, 2, prime_2633, prime_2, by norm_num⟩
  · exact ⟨2633, 3, prime_2633, prime_3, by norm_num⟩
  · exact ⟨2579, 31, prime_2579, prime_31, by norm_num⟩
  · exact ⟨2633, 5, prime_2633, prime_5, by norm_num⟩
  · exact ⟨2551, 47, prime_2551, prime_47, by norm_num⟩
  · exact ⟨2633, 7, prime_2633, prime_7, by norm_num⟩
  · exact ⟨2591, 29, prime_2591, prime_29, by norm_num⟩
  · exact ⟨2647, 2, prime_2647, prime_2, by norm_num⟩
  · exact ⟨2647, 3, prime_2647, prime_3, by norm_num⟩
  · exact ⟨2633, 11, prime_2633, prime_11, by norm_num⟩
  · exact ⟨2647, 5, prime_2647, prime_5, by norm_num⟩
  · exact ⟨2633, 13, prime_2633, prime_13, by norm_num⟩
  · exact ⟨2657, 2, prime_2657, prime_2, by norm_num⟩
  · exact ⟨2659, 2, prime_2659, prime_2, by norm_num⟩
  · exact ⟨2659, 3, prime_2659, prime_3, by norm_num⟩
  · exact ⟨2663, 2, prime_2663, prime_2, by norm_num⟩
  · exact ⟨2663, 3, prime_2663, prime_3, by norm_num⟩
  · exact ⟨2657, 7, prime_2657, prime_7, by norm_num⟩
  · exact ⟨2663, 5, prime_2663, prime_5, by norm_num⟩
  · exact ⟨2671, 2, prime_2671, prime_2, by norm_num⟩
  · exact ⟨2671, 3, prime_2671, prime_3, by norm_num⟩
  · exact ⟨2657, 11, prime_2657, prime_11, by norm_num⟩
  · exact ⟨2677, 2, prime_2677, prime_2, by norm_num⟩
  · exact ⟨2677, 3, prime_2677, prime_3, by norm_num⟩
  · exact ⟨2671, 7, prime_2671, prime_7, by norm_num⟩
  · exact ⟨2683, 2, prime_2683, prime_2, by norm_num⟩
  · exact ⟨2683, 3, prime_2683, prime_3, by norm_num⟩
  · exact ⟨2687, 2, prime_2687, prime_2, by norm_num⟩
  · exact ⟨2689, 2, prime_2689, prime_2, by norm_num⟩
  · exact ⟨2689, 3, prime_2689, prime_3, by norm_num⟩
  · exact ⟨2693, 2, prime_2693, prime_2, by norm_num⟩
  · exact ⟨2693, 3, prime_2693, prime_3, by norm_num⟩
  · exact ⟨2687, 7, prime_2687, prime_7, by norm_num⟩
  · exact ⟨2699, 2, prime_2699, prime_2, by norm_num⟩
  · exact ⟨2699, 3, prime_2699, prime_3, by norm_num⟩
  · exact ⟨2693, 7, prime_2693, prime_7, by norm_num⟩
  · exact ⟨2699, 5, prime_2699, prime_5, by norm_num⟩
  · exact ⟨2707, 2, prime_2707, prime_2, by norm_num⟩
  · exact ⟨2707, 3, prime_2707, prime_3, by norm_num⟩
  · exact ⟨2711, 2, prime_2711, prime_2, by norm_num⟩
  · exact ⟨2713, 2, prime_2713, prime_2, by norm_num⟩
  · exact ⟨2713, 3, prime_2713, prime_3, by norm_num⟩
  · exact ⟨2711, 5, prime_2711, prime_5, by norm_num⟩
  · exact ⟨2719, 2, prime_2719, prime_2, by norm_num⟩
  · exact ⟨2719, 3, prime_2719, prime_3, by norm_num⟩
  · exact ⟨2713, 7, prime_2713, prime_7, by norm_num⟩
  · exact ⟨2719, 5, prime_2719, prime_5, by norm_num⟩
  · exact ⟨2693, 19, prime_2693, prime_19, by norm_num⟩
  · exact ⟨2729, 2, prime_2729, prime_2, by norm_num⟩
  · exact ⟨2731, 2, prime_2731, prime_2, by norm_num⟩
  · exact ⟨2731, 3, prime_2731, prime_3, by norm_num⟩
  · exact ⟨2729, 5, prime_2729, prime_5, by norm_num⟩
  · exact ⟨2731, 5, prime_2731, prime_5, by norm_num⟩
  · exact ⟨2729, 7, prime_2729, prime_7, by norm_num⟩
  · exact ⟨2741, 2, prime_2741, prime_2, by norm_num⟩
  · exact ⟨2741, 3, prime_2741, prime_3, by norm_num⟩
  · exact ⟨2711, 19, prime_2711, prime_19, by norm_num⟩
  · exact ⟨2741, 5, prime_2741, prime_5, by norm_num⟩
  · exact ⟨2749, 2, prime_2749, prime_2, by norm_num⟩
  · exact ⟨2749, 3, prime_2749, prime_3, by norm_num⟩
  · exact ⟨2753, 2, prime_2753, prime_2, by norm_num⟩
  · exact ⟨2753, 3, prime_2753, prime_3, by norm_num⟩
  · exact ⟨2699, 31, prime_2699, prime_31, by norm_num⟩
  · exact ⟨2753, 5, prime_2753, prime_5, by norm_num⟩
  · exact ⟨2731, 17, prime_2731, prime_17, by norm_num⟩
  · exact ⟨2753, 7, prime_2753, prime_7, by norm_num⟩
  · exact ⟨2731, 19, prime_2731, prime_19, by norm_num⟩
  · exact ⟨2767, 2, prime_2767, prime_2, by norm_num⟩
  · exact ⟨2767, 3, prime_2767, prime_3, by norm_num⟩
  · exact ⟨2753, 11, prime_2753, prime_11, by norm_num⟩
  · exact ⟨2767, 5, prime_2767, prime_5, by norm_num⟩
  · exact ⟨2753, 13, prime_2753, prime_13, by norm_num⟩
  · exact ⟨2777, 2, prime_2777, prime_2, by norm_num⟩
  · exact ⟨2777, 3, prime_2777, prime_3, by norm_num⟩
  · exact ⟨2711, 37, prime_2711, prime_37, by norm_num⟩
  · exact ⟨2777, 5, prime_2777, prime_5, by norm_num⟩
  · exact ⟨2767, 11, prime_2767, prime_11, by norm_num⟩
  · exact ⟨2777, 7, prime_2777, prime_7, by norm_num⟩
  · exact ⟨2789, 2, prime_2789, prime_2, by norm_num⟩
  · exact ⟨2791, 2, prime_2791, prime_2, by norm_num⟩
  · exact ⟨2791, 3, prime_2791, prime_3, by norm_num⟩
  · exact ⟨2789, 5, prime_2789, prime_5, by norm_num⟩
  · exact ⟨2797, 2, prime_2797, prime_2, by norm_num⟩
  · exact ⟨2797, 3, prime_2797, prime_3, by norm_num⟩
  · exact ⟨2801, 2, prime_2801, prime_2, by norm_num⟩

private theorem lemoine_chunk_14 : ∀ k : ℕ, 1403 ≤ k → k ≤ 1502 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨2803, 2, prime_2803, prime_2, by norm_num⟩
  · exact ⟨2803, 3, prime_2803, prime_3, by norm_num⟩
  · exact ⟨2801, 5, prime_2801, prime_5, by norm_num⟩
  · exact ⟨2803, 5, prime_2803, prime_5, by norm_num⟩
  · exact ⟨2801, 7, prime_2801, prime_7, by norm_num⟩
  · exact ⟨2803, 7, prime_2803, prime_7, by norm_num⟩
  · exact ⟨2797, 11, prime_2797, prime_11, by norm_num⟩
  · exact ⟨2699, 61, prime_2699, prime_61, by norm_num⟩
  · exact ⟨2819, 2, prime_2819, prime_2, by norm_num⟩
  · exact ⟨2819, 3, prime_2819, prime_3, by norm_num⟩
  · exact ⟨2801, 13, prime_2801, prime_13, by norm_num⟩
  · exact ⟨2819, 5, prime_2819, prime_5, by norm_num⟩
  · exact ⟨2797, 17, prime_2797, prime_17, by norm_num⟩
  · exact ⟨2819, 7, prime_2819, prime_7, by norm_num⟩
  · exact ⟨2801, 17, prime_2801, prime_17, by norm_num⟩
  · exact ⟨2833, 2, prime_2833, prime_2, by norm_num⟩
  · exact ⟨2833, 3, prime_2833, prime_3, by norm_num⟩
  · exact ⟨2837, 2, prime_2837, prime_2, by norm_num⟩
  · exact ⟨2837, 3, prime_2837, prime_3, by norm_num⟩
  · exact ⟨2819, 13, prime_2819, prime_13, by norm_num⟩
  · exact ⟨2843, 2, prime_2843, prime_2, by norm_num⟩
  · exact ⟨2843, 3, prime_2843, prime_3, by norm_num⟩
  · exact ⟨2837, 7, prime_2837, prime_7, by norm_num⟩
  · exact ⟨2843, 5, prime_2843, prime_5, by norm_num⟩
  · exact ⟨2851, 2, prime_2851, prime_2, by norm_num⟩
  · exact ⟨2851, 3, prime_2851, prime_3, by norm_num⟩
  · exact ⟨2837, 11, prime_2837, prime_11, by norm_num⟩
  · exact ⟨2857, 2, prime_2857, prime_2, by norm_num⟩
  · exact ⟨2857, 3, prime_2857, prime_3, by norm_num⟩
  · exact ⟨2861, 2, prime_2861, prime_2, by norm_num⟩
  · exact ⟨2861, 3, prime_2861, prime_3, by norm_num⟩
  · exact ⟨2843, 13, prime_2843, prime_13, by norm_num⟩
  · exact ⟨2861, 5, prime_2861, prime_5, by norm_num⟩
  · exact ⟨2851, 11, prime_2851, prime_11, by norm_num⟩
  · exact ⟨2861, 7, prime_2861, prime_7, by norm_num⟩
  · exact ⟨2851, 13, prime_2851, prime_13, by norm_num⟩
  · exact ⟨2857, 11, prime_2857, prime_11, by norm_num⟩
  · exact ⟨2843, 19, prime_2843, prime_19, by norm_num⟩
  · exact ⟨2879, 2, prime_2879, prime_2, by norm_num⟩
  · exact ⟨2879, 3, prime_2879, prime_3, by norm_num⟩
  · exact ⟨2861, 13, prime_2861, prime_13, by norm_num⟩
  · exact ⟨2879, 5, prime_2879, prime_5, by norm_num⟩
  · exact ⟨2887, 2, prime_2887, prime_2, by norm_num⟩
  · exact ⟨2887, 3, prime_2887, prime_3, by norm_num⟩
  · exact ⟨2861, 17, prime_2861, prime_17, by norm_num⟩
  · exact ⟨2887, 5, prime_2887, prime_5, by norm_num⟩
  · exact ⟨2861, 19, prime_2861, prime_19, by norm_num⟩
  · exact ⟨2897, 2, prime_2897, prime_2, by norm_num⟩
  · exact ⟨2897, 3, prime_2897, prime_3, by norm_num⟩
  · exact ⟨2879, 13, prime_2879, prime_13, by norm_num⟩
  · exact ⟨2903, 2, prime_2903, prime_2, by norm_num⟩
  · exact ⟨2903, 3, prime_2903, prime_3, by norm_num⟩
  · exact ⟨2897, 7, prime_2897, prime_7, by norm_num⟩
  · exact ⟨2909, 2, prime_2909, prime_2, by norm_num⟩
  · exact ⟨2909, 3, prime_2909, prime_3, by norm_num⟩
  · exact ⟨2903, 7, prime_2903, prime_7, by norm_num⟩
  · exact ⟨2909, 5, prime_2909, prime_5, by norm_num⟩
  · exact ⟨2917, 2, prime_2917, prime_2, by norm_num⟩
  · exact ⟨2917, 3, prime_2917, prime_3, by norm_num⟩
  · exact ⟨2903, 11, prime_2903, prime_11, by norm_num⟩
  · exact ⟨2917, 5, prime_2917, prime_5, by norm_num⟩
  · exact ⟨2903, 13, prime_2903, prime_13, by norm_num⟩
  · exact ⟨2927, 2, prime_2927, prime_2, by norm_num⟩
  · exact ⟨2927, 3, prime_2927, prime_3, by norm_num⟩
  · exact ⟨2909, 13, prime_2909, prime_13, by norm_num⟩
  · exact ⟨2927, 5, prime_2927, prime_5, by norm_num⟩
  · exact ⟨2917, 11, prime_2917, prime_11, by norm_num⟩
  · exact ⟨2927, 7, prime_2927, prime_7, by norm_num⟩
  · exact ⟨2939, 2, prime_2939, prime_2, by norm_num⟩
  · exact ⟨2939, 3, prime_2939, prime_3, by norm_num⟩
  · exact ⟨2909, 19, prime_2909, prime_19, by norm_num⟩
  · exact ⟨2939, 5, prime_2939, prime_5, by norm_num⟩
  · exact ⟨2917, 17, prime_2917, prime_17, by norm_num⟩
  · exact ⟨2939, 7, prime_2939, prime_7, by norm_num⟩
  · exact ⟨2917, 19, prime_2917, prime_19, by norm_num⟩
  · exact ⟨2953, 2, prime_2953, prime_2, by norm_num⟩
  · exact ⟨2953, 3, prime_2953, prime_3, by norm_num⟩
  · exact ⟨2957, 2, prime_2957, prime_2, by norm_num⟩
  · exact ⟨2957, 3, prime_2957, prime_3, by norm_num⟩
  · exact ⟨2939, 13, prime_2939, prime_13, by norm_num⟩
  · exact ⟨2963, 2, prime_2963, prime_2, by norm_num⟩
  · exact ⟨2963, 3, prime_2963, prime_3, by norm_num⟩
  · exact ⟨2957, 7, prime_2957, prime_7, by norm_num⟩
  · exact ⟨2969, 2, prime_2969, prime_2, by norm_num⟩
  · exact ⟨2971, 2, prime_2971, prime_2, by norm_num⟩
  · exact ⟨2971, 3, prime_2971, prime_3, by norm_num⟩
  · exact ⟨2969, 5, prime_2969, prime_5, by norm_num⟩
  · exact ⟨2971, 5, prime_2971, prime_5, by norm_num⟩
  · exact ⟨2969, 7, prime_2969, prime_7, by norm_num⟩
  · exact ⟨2971, 7, prime_2971, prime_7, by norm_num⟩
  · exact ⟨2953, 17, prime_2953, prime_17, by norm_num⟩
  · exact ⟨2963, 13, prime_2963, prime_13, by norm_num⟩
  · exact ⟨2969, 11, prime_2969, prime_11, by norm_num⟩
  · exact ⟨2971, 11, prime_2971, prime_11, by norm_num⟩
  · exact ⟨2969, 13, prime_2969, prime_13, by norm_num⟩
  · exact ⟨2971, 13, prime_2971, prime_13, by norm_num⟩
  · exact ⟨2953, 23, prime_2953, prime_23, by norm_num⟩
  · exact ⟨2963, 19, prime_2963, prime_19, by norm_num⟩
  · exact ⟨2999, 2, prime_2999, prime_2, by norm_num⟩
  · exact ⟨3001, 2, prime_3001, prime_2, by norm_num⟩

private theorem lemoine_chunk_15 : ∀ k : ℕ, 1503 ≤ k → k ≤ 1602 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3001, 3, prime_3001, prime_3, by norm_num⟩
  · exact ⟨2999, 5, prime_2999, prime_5, by norm_num⟩
  · exact ⟨3001, 5, prime_3001, prime_5, by norm_num⟩
  · exact ⟨2999, 7, prime_2999, prime_7, by norm_num⟩
  · exact ⟨3011, 2, prime_3011, prime_2, by norm_num⟩
  · exact ⟨3011, 3, prime_3011, prime_3, by norm_num⟩
  · exact ⟨2957, 31, prime_2957, prime_31, by norm_num⟩
  · exact ⟨3011, 5, prime_3011, prime_5, by norm_num⟩
  · exact ⟨3019, 2, prime_3019, prime_2, by norm_num⟩
  · exact ⟨3019, 3, prime_3019, prime_3, by norm_num⟩
  · exact ⟨3023, 2, prime_3023, prime_2, by norm_num⟩
  · exact ⟨3023, 3, prime_3023, prime_3, by norm_num⟩
  · exact ⟨2969, 31, prime_2969, prime_31, by norm_num⟩
  · exact ⟨3023, 5, prime_3023, prime_5, by norm_num⟩
  · exact ⟨3001, 17, prime_3001, prime_17, by norm_num⟩
  · exact ⟨3023, 7, prime_3023, prime_7, by norm_num⟩
  · exact ⟨3001, 19, prime_3001, prime_19, by norm_num⟩
  · exact ⟨3037, 2, prime_3037, prime_2, by norm_num⟩
  · exact ⟨3037, 3, prime_3037, prime_3, by norm_num⟩
  · exact ⟨3041, 2, prime_3041, prime_2, by norm_num⟩
  · exact ⟨3041, 3, prime_3041, prime_3, by norm_num⟩
  · exact ⟨3023, 13, prime_3023, prime_13, by norm_num⟩
  · exact ⟨3041, 5, prime_3041, prime_5, by norm_num⟩
  · exact ⟨3049, 2, prime_3049, prime_2, by norm_num⟩
  · exact ⟨3049, 3, prime_3049, prime_3, by norm_num⟩
  · exact ⟨3023, 17, prime_3023, prime_17, by norm_num⟩
  · exact ⟨3049, 5, prime_3049, prime_5, by norm_num⟩
  · exact ⟨3023, 19, prime_3023, prime_19, by norm_num⟩
  · exact ⟨3049, 7, prime_3049, prime_7, by norm_num⟩
  · exact ⟨3061, 2, prime_3061, prime_2, by norm_num⟩
  · exact ⟨3061, 3, prime_3061, prime_3, by norm_num⟩
  · exact ⟨3023, 23, prime_3023, prime_23, by norm_num⟩
  · exact ⟨3067, 2, prime_3067, prime_2, by norm_num⟩
  · exact ⟨3067, 3, prime_3067, prime_3, by norm_num⟩
  · exact ⟨3061, 7, prime_3061, prime_7, by norm_num⟩
  · exact ⟨3067, 5, prime_3067, prime_5, by norm_num⟩
  · exact ⟨3041, 19, prime_3041, prime_19, by norm_num⟩
  · exact ⟨3067, 7, prime_3067, prime_7, by norm_num⟩
  · exact ⟨3079, 2, prime_3079, prime_2, by norm_num⟩
  · exact ⟨3079, 3, prime_3079, prime_3, by norm_num⟩
  · exact ⟨3083, 2, prime_3083, prime_2, by norm_num⟩
  · exact ⟨3083, 3, prime_3083, prime_3, by norm_num⟩
  · exact ⟨2969, 61, prime_2969, prime_61, by norm_num⟩
  · exact ⟨3089, 2, prime_3089, prime_2, by norm_num⟩
  · exact ⟨3089, 3, prime_3089, prime_3, by norm_num⟩
  · exact ⟨3083, 7, prime_3083, prime_7, by norm_num⟩
  · exact ⟨3089, 5, prime_3089, prime_5, by norm_num⟩
  · exact ⟨3079, 11, prime_3079, prime_11, by norm_num⟩
  · exact ⟨3089, 7, prime_3089, prime_7, by norm_num⟩
  · exact ⟨3083, 11, prime_3083, prime_11, by norm_num⟩
  · exact ⟨3061, 23, prime_3061, prime_23, by norm_num⟩
  · exact ⟨3083, 13, prime_3083, prime_13, by norm_num⟩
  · exact ⟨3089, 11, prime_3089, prime_11, by norm_num⟩
  · exact ⟨3109, 2, prime_3109, prime_2, by norm_num⟩
  · exact ⟨3109, 3, prime_3109, prime_3, by norm_num⟩
  · exact ⟨3083, 17, prime_3083, prime_17, by norm_num⟩
  · exact ⟨3109, 5, prime_3109, prime_5, by norm_num⟩
  · exact ⟨3083, 19, prime_3083, prime_19, by norm_num⟩
  · exact ⟨3119, 2, prime_3119, prime_2, by norm_num⟩
  · exact ⟨3121, 2, prime_3121, prime_2, by norm_num⟩
  · exact ⟨3121, 3, prime_3121, prime_3, by norm_num⟩
  · exact ⟨3119, 5, prime_3119, prime_5, by norm_num⟩
  · exact ⟨3121, 5, prime_3121, prime_5, by norm_num⟩
  · exact ⟨3119, 7, prime_3119, prime_7, by norm_num⟩
  · exact ⟨3121, 7, prime_3121, prime_7, by norm_num⟩
  · exact ⟨3079, 29, prime_3079, prime_29, by norm_num⟩
  · exact ⟨2861, 139, prime_2861, prime_139, by norm_num⟩
  · exact ⟨3137, 2, prime_3137, prime_2, by norm_num⟩
  · exact ⟨3137, 3, prime_3137, prime_3, by norm_num⟩
  · exact ⟨3119, 13, prime_3119, prime_13, by norm_num⟩
  · exact ⟨3137, 5, prime_3137, prime_5, by norm_num⟩
  · exact ⟨3067, 41, prime_3067, prime_41, by norm_num⟩
  · exact ⟨3137, 7, prime_3137, prime_7, by norm_num⟩
  · exact ⟨3119, 17, prime_3119, prime_17, by norm_num⟩
  · exact ⟨3121, 17, prime_3121, prime_17, by norm_num⟩
  · exact ⟨3119, 19, prime_3119, prime_19, by norm_num⟩
  · exact ⟨3137, 11, prime_3137, prime_11, by norm_num⟩
  · exact ⟨3079, 41, prime_3079, prime_41, by norm_num⟩
  · exact ⟨3137, 13, prime_3137, prime_13, by norm_num⟩
  · exact ⟨3119, 23, prime_3119, prime_23, by norm_num⟩
  · exact ⟨3163, 2, prime_3163, prime_2, by norm_num⟩
  · exact ⟨3163, 3, prime_3163, prime_3, by norm_num⟩
  · exact ⟨3167, 2, prime_3167, prime_2, by norm_num⟩
  · exact ⟨3169, 2, prime_3169, prime_2, by norm_num⟩
  · exact ⟨3169, 3, prime_3169, prime_3, by norm_num⟩
  · exact ⟨3167, 5, prime_3167, prime_5, by norm_num⟩
  · exact ⟨3169, 5, prime_3169, prime_5, by norm_num⟩
  · exact ⟨3167, 7, prime_3167, prime_7, by norm_num⟩
  · exact ⟨3169, 7, prime_3169, prime_7, by norm_num⟩
  · exact ⟨3181, 2, prime_3181, prime_2, by norm_num⟩
  · exact ⟨3181, 3, prime_3181, prime_3, by norm_num⟩
  · exact ⟨3167, 11, prime_3167, prime_11, by norm_num⟩
  · exact ⟨3187, 2, prime_3187, prime_2, by norm_num⟩
  · exact ⟨3187, 3, prime_3187, prime_3, by norm_num⟩
  · exact ⟨3191, 2, prime_3191, prime_2, by norm_num⟩
  · exact ⟨3191, 3, prime_3191, prime_3, by norm_num⟩
  · exact ⟨3137, 31, prime_3137, prime_31, by norm_num⟩
  · exact ⟨3191, 5, prime_3191, prime_5, by norm_num⟩
  · exact ⟨3181, 11, prime_3181, prime_11, by norm_num⟩
  · exact ⟨3191, 7, prime_3191, prime_7, by norm_num⟩

private theorem lemoine_chunk_16 : ∀ k : ℕ, 1603 ≤ k → k ≤ 1702 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3203, 2, prime_3203, prime_2, by norm_num⟩
  · exact ⟨3203, 3, prime_3203, prime_3, by norm_num⟩
  · exact ⟨3137, 37, prime_3137, prime_37, by norm_num⟩
  · exact ⟨3209, 2, prime_3209, prime_2, by norm_num⟩
  · exact ⟨3209, 3, prime_3209, prime_3, by norm_num⟩
  · exact ⟨3203, 7, prime_3203, prime_7, by norm_num⟩
  · exact ⟨3209, 5, prime_3209, prime_5, by norm_num⟩
  · exact ⟨3217, 2, prime_3217, prime_2, by norm_num⟩
  · exact ⟨3217, 3, prime_3217, prime_3, by norm_num⟩
  · exact ⟨3221, 2, prime_3221, prime_2, by norm_num⟩
  · exact ⟨3221, 3, prime_3221, prime_3, by norm_num⟩
  · exact ⟨3203, 13, prime_3203, prime_13, by norm_num⟩
  · exact ⟨3221, 5, prime_3221, prime_5, by norm_num⟩
  · exact ⟨3229, 2, prime_3229, prime_2, by norm_num⟩
  · exact ⟨3229, 3, prime_3229, prime_3, by norm_num⟩
  · exact ⟨3203, 17, prime_3203, prime_17, by norm_num⟩
  · exact ⟨3229, 5, prime_3229, prime_5, by norm_num⟩
  · exact ⟨3203, 19, prime_3203, prime_19, by norm_num⟩
  · exact ⟨3229, 7, prime_3229, prime_7, by norm_num⟩
  · exact ⟨3187, 29, prime_3187, prime_29, by norm_num⟩
  · exact ⟨3221, 13, prime_3221, prime_13, by norm_num⟩
  · exact ⟨3203, 23, prime_3203, prime_23, by norm_num⟩
  · exact ⟨3229, 11, prime_3229, prime_11, by norm_num⟩
  · exact ⟨3191, 31, prime_3191, prime_31, by norm_num⟩
  · exact ⟨3251, 2, prime_3251, prime_2, by norm_num⟩
  · exact ⟨3253, 2, prime_3253, prime_2, by norm_num⟩
  · exact ⟨3253, 3, prime_3253, prime_3, by norm_num⟩
  · exact ⟨3257, 2, prime_3257, prime_2, by norm_num⟩
  · exact ⟨3259, 2, prime_3259, prime_2, by norm_num⟩
  · exact ⟨3259, 3, prime_3259, prime_3, by norm_num⟩
  · exact ⟨3257, 5, prime_3257, prime_5, by norm_num⟩
  · exact ⟨3259, 5, prime_3259, prime_5, by norm_num⟩
  · exact ⟨3257, 7, prime_3257, prime_7, by norm_num⟩
  · exact ⟨3259, 7, prime_3259, prime_7, by norm_num⟩
  · exact ⟨3271, 2, prime_3271, prime_2, by norm_num⟩
  · exact ⟨3271, 3, prime_3271, prime_3, by norm_num⟩
  · exact ⟨3257, 11, prime_3257, prime_11, by norm_num⟩
  · exact ⟨3271, 5, prime_3271, prime_5, by norm_num⟩
  · exact ⟨3257, 13, prime_3257, prime_13, by norm_num⟩
  · exact ⟨3271, 7, prime_3271, prime_7, by norm_num⟩
  · exact ⟨3253, 17, prime_3253, prime_17, by norm_num⟩
  · exact ⟨3251, 19, prime_3251, prime_19, by norm_num⟩
  · exact ⟨3257, 17, prime_3257, prime_17, by norm_num⟩
  · exact ⟨3271, 11, prime_3271, prime_11, by norm_num⟩
  · exact ⟨3257, 19, prime_3257, prime_19, by norm_num⟩
  · exact ⟨3271, 13, prime_3271, prime_13, by norm_num⟩
  · exact ⟨3253, 23, prime_3253, prime_23, by norm_num⟩
  · exact ⟨3167, 67, prime_3167, prime_67, by norm_num⟩
  · exact ⟨3299, 2, prime_3299, prime_2, by norm_num⟩
  · exact ⟨3301, 2, prime_3301, prime_2, by norm_num⟩
  · exact ⟨3301, 3, prime_3301, prime_3, by norm_num⟩
  · exact ⟨3299, 5, prime_3299, prime_5, by norm_num⟩
  · exact ⟨3307, 2, prime_3307, prime_2, by norm_num⟩
  · exact ⟨3307, 3, prime_3307, prime_3, by norm_num⟩
  · exact ⟨3301, 7, prime_3301, prime_7, by norm_num⟩
  · exact ⟨3313, 2, prime_3313, prime_2, by norm_num⟩
  · exact ⟨3313, 3, prime_3313, prime_3, by norm_num⟩
  · exact ⟨3307, 7, prime_3307, prime_7, by norm_num⟩
  · exact ⟨3319, 2, prime_3319, prime_2, by norm_num⟩
  · exact ⟨3319, 3, prime_3319, prime_3, by norm_num⟩
  · exact ⟨3323, 2, prime_3323, prime_2, by norm_num⟩
  · exact ⟨3323, 3, prime_3323, prime_3, by norm_num⟩
  · exact ⟨3257, 37, prime_3257, prime_37, by norm_num⟩
  · exact ⟨3329, 2, prime_3329, prime_2, by norm_num⟩
  · exact ⟨3331, 2, prime_3331, prime_2, by norm_num⟩
  · exact ⟨3331, 3, prime_3331, prime_3, by norm_num⟩
  · exact ⟨3329, 5, prime_3329, prime_5, by norm_num⟩
  · exact ⟨3331, 5, prime_3331, prime_5, by norm_num⟩
  · exact ⟨3329, 7, prime_3329, prime_7, by norm_num⟩
  · exact ⟨3331, 7, prime_3331, prime_7, by norm_num⟩
  · exact ⟨3343, 2, prime_3343, prime_2, by norm_num⟩
  · exact ⟨3343, 3, prime_3343, prime_3, by norm_num⟩
  · exact ⟨3347, 2, prime_3347, prime_2, by norm_num⟩
  · exact ⟨3347, 3, prime_3347, prime_3, by norm_num⟩
  · exact ⟨3329, 13, prime_3329, prime_13, by norm_num⟩
  · exact ⟨3347, 5, prime_3347, prime_5, by norm_num⟩
  · exact ⟨3313, 23, prime_3313, prime_23, by norm_num⟩
  · exact ⟨3347, 7, prime_3347, prime_7, by norm_num⟩
  · exact ⟨3359, 2, prime_3359, prime_2, by norm_num⟩
  · exact ⟨3361, 2, prime_3361, prime_2, by norm_num⟩
  · exact ⟨3361, 3, prime_3361, prime_3, by norm_num⟩
  · exact ⟨3359, 5, prime_3359, prime_5, by norm_num⟩
  · exact ⟨3361, 5, prime_3361, prime_5, by norm_num⟩
  · exact ⟨3359, 7, prime_3359, prime_7, by norm_num⟩
  · exact ⟨3371, 2, prime_3371, prime_2, by norm_num⟩
  · exact ⟨3373, 2, prime_3373, prime_2, by norm_num⟩
  · exact ⟨3373, 3, prime_3373, prime_3, by norm_num⟩
  · exact ⟨3371, 5, prime_3371, prime_5, by norm_num⟩
  · exact ⟨3373, 5, prime_3373, prime_5, by norm_num⟩
  · exact ⟨3371, 7, prime_3371, prime_7, by norm_num⟩
  · exact ⟨3373, 7, prime_3373, prime_7, by norm_num⟩
  · exact ⟨3343, 23, prime_3343, prime_23, by norm_num⟩
  · exact ⟨3329, 31, prime_3329, prime_31, by norm_num⟩
  · exact ⟨3389, 2, prime_3389, prime_2, by norm_num⟩
  · exact ⟨3391, 2, prime_3391, prime_2, by norm_num⟩
  · exact ⟨3391, 3, prime_3391, prime_3, by norm_num⟩
  · exact ⟨3389, 5, prime_3389, prime_5, by norm_num⟩
  · exact ⟨3391, 5, prime_3391, prime_5, by norm_num⟩
  · exact ⟨3389, 7, prime_3389, prime_7, by norm_num⟩
  · exact ⟨3391, 7, prime_3391, prime_7, by norm_num⟩

private theorem lemoine_chunk_17 : ∀ k : ℕ, 1703 ≤ k → k ≤ 1802 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3373, 17, prime_3373, prime_17, by norm_num⟩
  · exact ⟨3371, 19, prime_3371, prime_19, by norm_num⟩
  · exact ⟨3407, 2, prime_3407, prime_2, by norm_num⟩
  · exact ⟨3407, 3, prime_3407, prime_3, by norm_num⟩
  · exact ⟨3389, 13, prime_3389, prime_13, by norm_num⟩
  · exact ⟨3413, 2, prime_3413, prime_2, by norm_num⟩
  · exact ⟨3413, 3, prime_3413, prime_3, by norm_num⟩
  · exact ⟨3407, 7, prime_3407, prime_7, by norm_num⟩
  · exact ⟨3413, 5, prime_3413, prime_5, by norm_num⟩
  · exact ⟨3391, 17, prime_3391, prime_17, by norm_num⟩
  · exact ⟨3413, 7, prime_3413, prime_7, by norm_num⟩
  · exact ⟨3407, 11, prime_3407, prime_11, by norm_num⟩
  · exact ⟨3373, 29, prime_3373, prime_29, by norm_num⟩
  · exact ⟨3407, 13, prime_3407, prime_13, by norm_num⟩
  · exact ⟨3413, 11, prime_3413, prime_11, by norm_num⟩
  · exact ⟨3433, 2, prime_3433, prime_2, by norm_num⟩
  · exact ⟨3433, 3, prime_3433, prime_3, by norm_num⟩
  · exact ⟨3407, 17, prime_3407, prime_17, by norm_num⟩
  · exact ⟨3433, 5, prime_3433, prime_5, by norm_num⟩
  · exact ⟨3407, 19, prime_3407, prime_19, by norm_num⟩
  · exact ⟨3433, 7, prime_3433, prime_7, by norm_num⟩
  · exact ⟨3391, 29, prime_3391, prime_29, by norm_num⟩
  · exact ⟨3413, 19, prime_3413, prime_19, by norm_num⟩
  · exact ⟨3449, 2, prime_3449, prime_2, by norm_num⟩
  · exact ⟨3449, 3, prime_3449, prime_3, by norm_num⟩
  · exact ⟨3371, 43, prime_3371, prime_43, by norm_num⟩
  · exact ⟨3449, 5, prime_3449, prime_5, by norm_num⟩
  · exact ⟨3457, 2, prime_3457, prime_2, by norm_num⟩
  · exact ⟨3457, 3, prime_3457, prime_3, by norm_num⟩
  · exact ⟨3461, 2, prime_3461, prime_2, by norm_num⟩
  · exact ⟨3463, 2, prime_3463, prime_2, by norm_num⟩
  · exact ⟨3463, 3, prime_3463, prime_3, by norm_num⟩
  · exact ⟨3467, 2, prime_3467, prime_2, by norm_num⟩
  · exact ⟨3469, 2, prime_3469, prime_2, by norm_num⟩
  · exact ⟨3469, 3, prime_3469, prime_3, by norm_num⟩
  · exact ⟨3467, 5, prime_3467, prime_5, by norm_num⟩
  · exact ⟨3469, 5, prime_3469, prime_5, by norm_num⟩
  · exact ⟨3467, 7, prime_3467, prime_7, by norm_num⟩
  · exact ⟨3469, 7, prime_3469, prime_7, by norm_num⟩
  · exact ⟨3463, 11, prime_3463, prime_11, by norm_num⟩
  · exact ⟨3461, 13, prime_3461, prime_13, by norm_num⟩
  · exact ⟨3467, 11, prime_3467, prime_11, by norm_num⟩
  · exact ⟨3469, 11, prime_3469, prime_11, by norm_num⟩
  · exact ⟨3467, 13, prime_3467, prime_13, by norm_num⟩
  · exact ⟨3491, 2, prime_3491, prime_2, by norm_num⟩
  · exact ⟨3491, 3, prime_3491, prime_3, by norm_num⟩
  · exact ⟨3461, 19, prime_3461, prime_19, by norm_num⟩
  · exact ⟨3491, 5, prime_3491, prime_5, by norm_num⟩
  · exact ⟨3499, 2, prime_3499, prime_2, by norm_num⟩
  · exact ⟨3499, 3, prime_3499, prime_3, by norm_num⟩
  · exact ⟨3469, 19, prime_3469, prime_19, by norm_num⟩
  · exact ⟨3499, 5, prime_3499, prime_5, by norm_num⟩
  · exact ⟨3449, 31, prime_3449, prime_31, by norm_num⟩
  · exact ⟨3499, 7, prime_3499, prime_7, by norm_num⟩
  · exact ⟨3511, 2, prime_3511, prime_2, by norm_num⟩
  · exact ⟨3511, 3, prime_3511, prime_3, by norm_num⟩
  · exact ⟨3461, 29, prime_3461, prime_29, by norm_num⟩
  · exact ⟨3517, 2, prime_3517, prime_2, by norm_num⟩
  · exact ⟨3517, 3, prime_3517, prime_3, by norm_num⟩
  · exact ⟨3511, 7, prime_3511, prime_7, by norm_num⟩
  · exact ⟨3517, 5, prime_3517, prime_5, by norm_num⟩
  · exact ⟨3491, 19, prime_3491, prime_19, by norm_num⟩
  · exact ⟨3527, 2, prime_3527, prime_2, by norm_num⟩
  · exact ⟨3529, 2, prime_3529, prime_2, by norm_num⟩
  · exact ⟨3529, 3, prime_3529, prime_3, by norm_num⟩
  · exact ⟨3533, 2, prime_3533, prime_2, by norm_num⟩
  · exact ⟨3533, 3, prime_3533, prime_3, by norm_num⟩
  · exact ⟨3527, 7, prime_3527, prime_7, by norm_num⟩
  · exact ⟨3539, 2, prime_3539, prime_2, by norm_num⟩
  · exact ⟨3541, 2, prime_3541, prime_2, by norm_num⟩
  · exact ⟨3541, 3, prime_3541, prime_3, by norm_num⟩
  · exact ⟨3539, 5, prime_3539, prime_5, by norm_num⟩
  · exact ⟨3547, 2, prime_3547, prime_2, by norm_num⟩
  · exact ⟨3547, 3, prime_3547, prime_3, by norm_num⟩
  · exact ⟨3541, 7, prime_3541, prime_7, by norm_num⟩
  · exact ⟨3547, 5, prime_3547, prime_5, by norm_num⟩
  · exact ⟨3533, 13, prime_3533, prime_13, by norm_num⟩
  · exact ⟨3557, 2, prime_3557, prime_2, by norm_num⟩
  · exact ⟨3559, 2, prime_3559, prime_2, by norm_num⟩
  · exact ⟨3559, 3, prime_3559, prime_3, by norm_num⟩
  · exact ⟨3557, 5, prime_3557, prime_5, by norm_num⟩
  · exact ⟨3559, 5, prime_3559, prime_5, by norm_num⟩
  · exact ⟨3557, 7, prime_3557, prime_7, by norm_num⟩
  · exact ⟨3559, 7, prime_3559, prime_7, by norm_num⟩
  · exact ⟨3571, 2, prime_3571, prime_2, by norm_num⟩
  · exact ⟨3571, 3, prime_3571, prime_3, by norm_num⟩
  · exact ⟨3557, 11, prime_3557, prime_11, by norm_num⟩
  · exact ⟨3571, 5, prime_3571, prime_5, by norm_num⟩
  · exact ⟨3557, 13, prime_3557, prime_13, by norm_num⟩
  · exact ⟨3581, 2, prime_3581, prime_2, by norm_num⟩
  · exact ⟨3583, 2, prime_3583, prime_2, by norm_num⟩
  · exact ⟨3583, 3, prime_3583, prime_3, by norm_num⟩
  · exact ⟨3581, 5, prime_3581, prime_5, by norm_num⟩
  · exact ⟨3583, 5, prime_3583, prime_5, by norm_num⟩
  · exact ⟨3581, 7, prime_3581, prime_7, by norm_num⟩
  · exact ⟨3593, 2, prime_3593, prime_2, by norm_num⟩
  · exact ⟨3593, 3, prime_3593, prime_3, by norm_num⟩
  · exact ⟨3539, 31, prime_3539, prime_31, by norm_num⟩
  · exact ⟨3593, 5, prime_3593, prime_5, by norm_num⟩
  · exact ⟨3583, 11, prime_3583, prime_11, by norm_num⟩

private theorem lemoine_chunk_18 : ∀ k : ℕ, 1803 ≤ k → k ≤ 1902 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3593, 7, prime_3593, prime_7, by norm_num⟩
  · exact ⟨3583, 13, prime_3583, prime_13, by norm_num⟩
  · exact ⟨3607, 2, prime_3607, prime_2, by norm_num⟩
  · exact ⟨3607, 3, prime_3607, prime_3, by norm_num⟩
  · exact ⟨3593, 11, prime_3593, prime_11, by norm_num⟩
  · exact ⟨3613, 2, prime_3613, prime_2, by norm_num⟩
  · exact ⟨3613, 3, prime_3613, prime_3, by norm_num⟩
  · exact ⟨3617, 2, prime_3617, prime_2, by norm_num⟩
  · exact ⟨3617, 3, prime_3617, prime_3, by norm_num⟩
  · exact ⟨3539, 43, prime_3539, prime_43, by norm_num⟩
  · exact ⟨3623, 2, prime_3623, prime_2, by norm_num⟩
  · exact ⟨3623, 3, prime_3623, prime_3, by norm_num⟩
  · exact ⟨3617, 7, prime_3617, prime_7, by norm_num⟩
  · exact ⟨3623, 5, prime_3623, prime_5, by norm_num⟩
  · exact ⟨3631, 2, prime_3631, prime_2, by norm_num⟩
  · exact ⟨3631, 3, prime_3631, prime_3, by norm_num⟩
  · exact ⟨3617, 11, prime_3617, prime_11, by norm_num⟩
  · exact ⟨3637, 2, prime_3637, prime_2, by norm_num⟩
  · exact ⟨3637, 3, prime_3637, prime_3, by norm_num⟩
  · exact ⟨3631, 7, prime_3631, prime_7, by norm_num⟩
  · exact ⟨3643, 2, prime_3643, prime_2, by norm_num⟩
  · exact ⟨3643, 3, prime_3643, prime_3, by norm_num⟩
  · exact ⟨3637, 7, prime_3637, prime_7, by norm_num⟩
  · exact ⟨3643, 5, prime_3643, prime_5, by norm_num⟩
  · exact ⟨3617, 19, prime_3617, prime_19, by norm_num⟩
  · exact ⟨3643, 7, prime_3643, prime_7, by norm_num⟩
  · exact ⟨3637, 11, prime_3637, prime_11, by norm_num⟩
  · exact ⟨3623, 19, prime_3623, prime_19, by norm_num⟩
  · exact ⟨3659, 2, prime_3659, prime_2, by norm_num⟩
  · exact ⟨3659, 3, prime_3659, prime_3, by norm_num⟩
  · exact ⟨3593, 37, prime_3593, prime_37, by norm_num⟩
  · exact ⟨3659, 5, prime_3659, prime_5, by norm_num⟩
  · exact ⟨3637, 17, prime_3637, prime_17, by norm_num⟩
  · exact ⟨3659, 7, prime_3659, prime_7, by norm_num⟩
  · exact ⟨3671, 2, prime_3671, prime_2, by norm_num⟩
  · exact ⟨3673, 2, prime_3673, prime_2, by norm_num⟩
  · exact ⟨3673, 3, prime_3673, prime_3, by norm_num⟩
  · exact ⟨3677, 2, prime_3677, prime_2, by norm_num⟩
  · exact ⟨3677, 3, prime_3677, prime_3, by norm_num⟩
  · exact ⟨3671, 7, prime_3671, prime_7, by norm_num⟩
  · exact ⟨3677, 5, prime_3677, prime_5, by norm_num⟩
  · exact ⟨3643, 23, prime_3643, prime_23, by norm_num⟩
  · exact ⟨3677, 7, prime_3677, prime_7, by norm_num⟩
  · exact ⟨3671, 11, prime_3671, prime_11, by norm_num⟩
  · exact ⟨3691, 2, prime_3691, prime_2, by norm_num⟩
  · exact ⟨3691, 3, prime_3691, prime_3, by norm_num⟩
  · exact ⟨3677, 11, prime_3677, prime_11, by norm_num⟩
  · exact ⟨3697, 2, prime_3697, prime_2, by norm_num⟩
  · exact ⟨3697, 3, prime_3697, prime_3, by norm_num⟩
  · exact ⟨3701, 2, prime_3701, prime_2, by norm_num⟩
  · exact ⟨3701, 3, prime_3701, prime_3, by norm_num⟩
  · exact ⟨3671, 19, prime_3671, prime_19, by norm_num⟩
  · exact ⟨3701, 5, prime_3701, prime_5, by norm_num⟩
  · exact ⟨3709, 2, prime_3709, prime_2, by norm_num⟩
  · exact ⟨3709, 3, prime_3709, prime_3, by norm_num⟩
  · exact ⟨3691, 13, prime_3691, prime_13, by norm_num⟩
  · exact ⟨3709, 5, prime_3709, prime_5, by norm_num⟩
  · exact ⟨3659, 31, prime_3659, prime_31, by norm_num⟩
  · exact ⟨3719, 2, prime_3719, prime_2, by norm_num⟩
  · exact ⟨3719, 3, prime_3719, prime_3, by norm_num⟩
  · exact ⟨3701, 13, prime_3701, prime_13, by norm_num⟩
  · exact ⟨3719, 5, prime_3719, prime_5, by norm_num⟩
  · exact ⟨3727, 2, prime_3727, prime_2, by norm_num⟩
  · exact ⟨3727, 3, prime_3727, prime_3, by norm_num⟩
  · exact ⟨3709, 13, prime_3709, prime_13, by norm_num⟩
  · exact ⟨3733, 2, prime_3733, prime_2, by norm_num⟩
  · exact ⟨3733, 3, prime_3733, prime_3, by norm_num⟩
  · exact ⟨3727, 7, prime_3727, prime_7, by norm_num⟩
  · exact ⟨3739, 2, prime_3739, prime_2, by norm_num⟩
  · exact ⟨3739, 3, prime_3739, prime_3, by norm_num⟩
  · exact ⟨3733, 7, prime_3733, prime_7, by norm_num⟩
  · exact ⟨3739, 5, prime_3739, prime_5, by norm_num⟩
  · exact ⟨3677, 37, prime_3677, prime_37, by norm_num⟩
  · exact ⟨3739, 7, prime_3739, prime_7, by norm_num⟩
  · exact ⟨3733, 11, prime_3733, prime_11, by norm_num⟩
  · exact ⟨3719, 19, prime_3719, prime_19, by norm_num⟩
  · exact ⟨3733, 13, prime_3733, prime_13, by norm_num⟩
  · exact ⟨3739, 11, prime_3739, prime_11, by norm_num⟩
  · exact ⟨3701, 31, prime_3701, prime_31, by norm_num⟩
  · exact ⟨3761, 2, prime_3761, prime_2, by norm_num⟩
  · exact ⟨3761, 3, prime_3761, prime_3, by norm_num⟩
  · exact ⟨3623, 73, prime_3623, prime_73, by norm_num⟩
  · exact ⟨3767, 2, prime_3767, prime_2, by norm_num⟩
  · exact ⟨3769, 2, prime_3769, prime_2, by norm_num⟩
  · exact ⟨3769, 3, prime_3769, prime_3, by norm_num⟩
  · exact ⟨3767, 5, prime_3767, prime_5, by norm_num⟩
  · exact ⟨3769, 5, prime_3769, prime_5, by norm_num⟩
  · exact ⟨3767, 7, prime_3767, prime_7, by norm_num⟩
  · exact ⟨3779, 2, prime_3779, prime_2, by norm_num⟩
  · exact ⟨3779, 3, prime_3779, prime_3, by norm_num⟩
  · exact ⟨3761, 13, prime_3761, prime_13, by norm_num⟩
  · exact ⟨3779, 5, prime_3779, prime_5, by norm_num⟩
  · exact ⟨3769, 11, prime_3769, prime_11, by norm_num⟩
  · exact ⟨3779, 7, prime_3779, prime_7, by norm_num⟩
  · exact ⟨3769, 13, prime_3769, prime_13, by norm_num⟩
  · exact ⟨3793, 2, prime_3793, prime_2, by norm_num⟩
  · exact ⟨3793, 3, prime_3793, prime_3, by norm_num⟩
  · exact ⟨3797, 2, prime_3797, prime_2, by norm_num⟩
  · exact ⟨3797, 3, prime_3797, prime_3, by norm_num⟩
  · exact ⟨3779, 13, prime_3779, prime_13, by norm_num⟩

private theorem lemoine_chunk_19 : ∀ k : ℕ, 1903 ≤ k → k ≤ 2002 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨3803, 2, prime_3803, prime_2, by norm_num⟩
  · exact ⟨3803, 3, prime_3803, prime_3, by norm_num⟩
  · exact ⟨3797, 7, prime_3797, prime_7, by norm_num⟩
  · exact ⟨3803, 5, prime_3803, prime_5, by norm_num⟩
  · exact ⟨3793, 11, prime_3793, prime_11, by norm_num⟩
  · exact ⟨3803, 7, prime_3803, prime_7, by norm_num⟩
  · exact ⟨3797, 11, prime_3797, prime_11, by norm_num⟩
  · exact ⟨3739, 41, prime_3739, prime_41, by norm_num⟩
  · exact ⟨3797, 13, prime_3797, prime_13, by norm_num⟩
  · exact ⟨3821, 2, prime_3821, prime_2, by norm_num⟩
  · exact ⟨3823, 2, prime_3823, prime_2, by norm_num⟩
  · exact ⟨3823, 3, prime_3823, prime_3, by norm_num⟩
  · exact ⟨3821, 5, prime_3821, prime_5, by norm_num⟩
  · exact ⟨3823, 5, prime_3823, prime_5, by norm_num⟩
  · exact ⟨3821, 7, prime_3821, prime_7, by norm_num⟩
  · exact ⟨3833, 2, prime_3833, prime_2, by norm_num⟩
  · exact ⟨3833, 3, prime_3833, prime_3, by norm_num⟩
  · exact ⟨3803, 19, prime_3803, prime_19, by norm_num⟩
  · exact ⟨3833, 5, prime_3833, prime_5, by norm_num⟩
  · exact ⟨3823, 11, prime_3823, prime_11, by norm_num⟩
  · exact ⟨3833, 7, prime_3833, prime_7, by norm_num⟩
  · exact ⟨3823, 13, prime_3823, prime_13, by norm_num⟩
  · exact ⟨3847, 2, prime_3847, prime_2, by norm_num⟩
  · exact ⟨3847, 3, prime_3847, prime_3, by norm_num⟩
  · exact ⟨3851, 2, prime_3851, prime_2, by norm_num⟩
  · exact ⟨3853, 2, prime_3853, prime_2, by norm_num⟩
  · exact ⟨3853, 3, prime_3853, prime_3, by norm_num⟩
  · exact ⟨3851, 5, prime_3851, prime_5, by norm_num⟩
  · exact ⟨3853, 5, prime_3853, prime_5, by norm_num⟩
  · exact ⟨3851, 7, prime_3851, prime_7, by norm_num⟩
  · exact ⟨3863, 2, prime_3863, prime_2, by norm_num⟩
  · exact ⟨3863, 3, prime_3863, prime_3, by norm_num⟩
  · exact ⟨3833, 19, prime_3833, prime_19, by norm_num⟩
  · exact ⟨3863, 5, prime_3863, prime_5, by norm_num⟩
  · exact ⟨3853, 11, prime_3853, prime_11, by norm_num⟩
  · exact ⟨3863, 7, prime_3863, prime_7, by norm_num⟩
  · exact ⟨3853, 13, prime_3853, prime_13, by norm_num⟩
  · exact ⟨3877, 2, prime_3877, prime_2, by norm_num⟩
  · exact ⟨3877, 3, prime_3877, prime_3, by norm_num⟩
  · exact ⟨3881, 2, prime_3881, prime_2, by norm_num⟩
  · exact ⟨3881, 3, prime_3881, prime_3, by norm_num⟩
  · exact ⟨3863, 13, prime_3863, prime_13, by norm_num⟩
  · exact ⟨3881, 5, prime_3881, prime_5, by norm_num⟩
  · exact ⟨3889, 2, prime_3889, prime_2, by norm_num⟩
  · exact ⟨3889, 3, prime_3889, prime_3, by norm_num⟩
  · exact ⟨3863, 17, prime_3863, prime_17, by norm_num⟩
  · exact ⟨3889, 5, prime_3889, prime_5, by norm_num⟩
  · exact ⟨3863, 19, prime_3863, prime_19, by norm_num⟩
  · exact ⟨3889, 7, prime_3889, prime_7, by norm_num⟩
  · exact ⟨3847, 29, prime_3847, prime_29, by norm_num⟩
  · exact ⟨3881, 13, prime_3881, prime_13, by norm_num⟩
  · exact ⟨3863, 23, prime_3863, prime_23, by norm_num⟩
  · exact ⟨3907, 2, prime_3907, prime_2, by norm_num⟩
  · exact ⟨3907, 3, prime_3907, prime_3, by norm_num⟩
  · exact ⟨3911, 2, prime_3911, prime_2, by norm_num⟩
  · exact ⟨3911, 3, prime_3911, prime_3, by norm_num⟩
  · exact ⟨3881, 19, prime_3881, prime_19, by norm_num⟩
  · exact ⟨3917, 2, prime_3917, prime_2, by norm_num⟩
  · exact ⟨3919, 2, prime_3919, prime_2, by norm_num⟩
  · exact ⟨3919, 3, prime_3919, prime_3, by norm_num⟩
  · exact ⟨3923, 2, prime_3923, prime_2, by norm_num⟩
  · exact ⟨3923, 3, prime_3923, prime_3, by norm_num⟩
  · exact ⟨3917, 7, prime_3917, prime_7, by norm_num⟩
  · exact ⟨3929, 2, prime_3929, prime_2, by norm_num⟩
  · exact ⟨3931, 2, prime_3931, prime_2, by norm_num⟩
  · exact ⟨3931, 3, prime_3931, prime_3, by norm_num⟩
  · exact ⟨3929, 5, prime_3929, prime_5, by norm_num⟩
  · exact ⟨3931, 5, prime_3931, prime_5, by norm_num⟩
  · exact ⟨3929, 7, prime_3929, prime_7, by norm_num⟩
  · exact ⟨3931, 7, prime_3931, prime_7, by norm_num⟩
  · exact ⟨3943, 2, prime_3943, prime_2, by norm_num⟩
  · exact ⟨3943, 3, prime_3943, prime_3, by norm_num⟩
  · exact ⟨3947, 2, prime_3947, prime_2, by norm_num⟩
  · exact ⟨3947, 3, prime_3947, prime_3, by norm_num⟩
  · exact ⟨3929, 13, prime_3929, prime_13, by norm_num⟩
  · exact ⟨3947, 5, prime_3947, prime_5, by norm_num⟩
  · exact ⟨3877, 41, prime_3877, prime_41, by norm_num⟩
  · exact ⟨3947, 7, prime_3947, prime_7, by norm_num⟩
  · exact ⟨3929, 17, prime_3929, prime_17, by norm_num⟩
  · exact ⟨3943, 11, prime_3943, prime_11, by norm_num⟩
  · exact ⟨3929, 19, prime_3929, prime_19, by norm_num⟩
  · exact ⟨3947, 11, prime_3947, prime_11, by norm_num⟩
  · exact ⟨3967, 2, prime_3967, prime_2, by norm_num⟩
  · exact ⟨3967, 3, prime_3967, prime_3, by norm_num⟩
  · exact ⟨3929, 23, prime_3929, prime_23, by norm_num⟩
  · exact ⟨3967, 5, prime_3967, prime_5, by norm_num⟩
  · exact ⟨3917, 31, prime_3917, prime_31, by norm_num⟩
  · exact ⟨3967, 7, prime_3967, prime_7, by norm_num⟩
  · exact ⟨3889, 47, prime_3889, prime_47, by norm_num⟩
  · exact ⟨3947, 19, prime_3947, prime_19, by norm_num⟩
  · exact ⟨3929, 29, prime_3929, prime_29, by norm_num⟩
  · exact ⟨3967, 11, prime_3967, prime_11, by norm_num⟩
  · exact ⟨3929, 31, prime_3929, prime_31, by norm_num⟩
  · exact ⟨3989, 2, prime_3989, prime_2, by norm_num⟩
  · exact ⟨3989, 3, prime_3989, prime_3, by norm_num⟩
  · exact ⟨3923, 37, prime_3923, prime_37, by norm_num⟩
  · exact ⟨3989, 5, prime_3989, prime_5, by norm_num⟩
  · exact ⟨3967, 17, prime_3967, prime_17, by norm_num⟩
  · exact ⟨3989, 7, prime_3989, prime_7, by norm_num⟩
  · exact ⟨4001, 2, prime_4001, prime_2, by norm_num⟩

private theorem lemoine_chunk_20 : ∀ k : ℕ, 2003 ≤ k → k ≤ 2102 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4003, 2, prime_4003, prime_2, by norm_num⟩
  · exact ⟨4003, 3, prime_4003, prime_3, by norm_num⟩
  · exact ⟨4007, 2, prime_4007, prime_2, by norm_num⟩
  · exact ⟨4007, 3, prime_4007, prime_3, by norm_num⟩
  · exact ⟨4001, 7, prime_4001, prime_7, by norm_num⟩
  · exact ⟨4013, 2, prime_4013, prime_2, by norm_num⟩
  · exact ⟨4013, 3, prime_4013, prime_3, by norm_num⟩
  · exact ⟨4007, 7, prime_4007, prime_7, by norm_num⟩
  · exact ⟨4019, 2, prime_4019, prime_2, by norm_num⟩
  · exact ⟨4021, 2, prime_4021, prime_2, by norm_num⟩
  · exact ⟨4021, 3, prime_4021, prime_3, by norm_num⟩
  · exact ⟨4019, 5, prime_4019, prime_5, by norm_num⟩
  · exact ⟨4027, 2, prime_4027, prime_2, by norm_num⟩
  · exact ⟨4027, 3, prime_4027, prime_3, by norm_num⟩
  · exact ⟨4021, 7, prime_4021, prime_7, by norm_num⟩
  · exact ⟨4027, 5, prime_4027, prime_5, by norm_num⟩
  · exact ⟨4013, 13, prime_4013, prime_13, by norm_num⟩
  · exact ⟨4027, 7, prime_4027, prime_7, by norm_num⟩
  · exact ⟨4021, 11, prime_4021, prime_11, by norm_num⟩
  · exact ⟨4019, 13, prime_4019, prime_13, by norm_num⟩
  · exact ⟨4021, 13, prime_4021, prime_13, by norm_num⟩
  · exact ⟨4027, 11, prime_4027, prime_11, by norm_num⟩
  · exact ⟨4013, 19, prime_4013, prime_19, by norm_num⟩
  · exact ⟨4049, 2, prime_4049, prime_2, by norm_num⟩
  · exact ⟨4051, 2, prime_4051, prime_2, by norm_num⟩
  · exact ⟨4051, 3, prime_4051, prime_3, by norm_num⟩
  · exact ⟨4049, 5, prime_4049, prime_5, by norm_num⟩
  · exact ⟨4057, 2, prime_4057, prime_2, by norm_num⟩
  · exact ⟨4057, 3, prime_4057, prime_3, by norm_num⟩
  · exact ⟨4051, 7, prime_4051, prime_7, by norm_num⟩
  · exact ⟨4057, 5, prime_4057, prime_5, by norm_num⟩
  · exact ⟨4007, 31, prime_4007, prime_31, by norm_num⟩
  · exact ⟨4057, 7, prime_4057, prime_7, by norm_num⟩
  · exact ⟨4051, 11, prime_4051, prime_11, by norm_num⟩
  · exact ⟨4049, 13, prime_4049, prime_13, by norm_num⟩
  · exact ⟨4073, 2, prime_4073, prime_2, by norm_num⟩
  · exact ⟨4073, 3, prime_4073, prime_3, by norm_num⟩
  · exact ⟨4019, 31, prime_4019, prime_31, by norm_num⟩
  · exact ⟨4079, 2, prime_4079, prime_2, by norm_num⟩
  · exact ⟨4079, 3, prime_4079, prime_3, by norm_num⟩
  · exact ⟨4073, 7, prime_4073, prime_7, by norm_num⟩
  · exact ⟨4079, 5, prime_4079, prime_5, by norm_num⟩
  · exact ⟨4057, 17, prime_4057, prime_17, by norm_num⟩
  · exact ⟨4079, 7, prime_4079, prime_7, by norm_num⟩
  · exact ⟨4091, 2, prime_4091, prime_2, by norm_num⟩
  · exact ⟨4093, 2, prime_4093, prime_2, by norm_num⟩
  · exact ⟨4093, 3, prime_4093, prime_3, by norm_num⟩
  · exact ⟨4091, 5, prime_4091, prime_5, by norm_num⟩
  · exact ⟨4099, 2, prime_4099, prime_2, by norm_num⟩
  · exact ⟨4099, 3, prime_4099, prime_3, by norm_num⟩
  · exact ⟨4093, 7, prime_4093, prime_7, by norm_num⟩
  · exact ⟨4099, 5, prime_4099, prime_5, by norm_num⟩
  · exact ⟨4073, 19, prime_4073, prime_19, by norm_num⟩
  · exact ⟨4099, 7, prime_4099, prime_7, by norm_num⟩
  · exact ⟨4111, 2, prime_4111, prime_2, by norm_num⟩
  · exact ⟨4111, 3, prime_4111, prime_3, by norm_num⟩
  · exact ⟨4093, 13, prime_4093, prime_13, by norm_num⟩
  · exact ⟨4111, 5, prime_4111, prime_5, by norm_num⟩
  · exact ⟨4049, 37, prime_4049, prime_37, by norm_num⟩
  · exact ⟨4111, 7, prime_4111, prime_7, by norm_num⟩
  · exact ⟨4093, 17, prime_4093, prime_17, by norm_num⟩
  · exact ⟨4091, 19, prime_4091, prime_19, by norm_num⟩
  · exact ⟨4127, 2, prime_4127, prime_2, by norm_num⟩
  · exact ⟨4129, 2, prime_4129, prime_2, by norm_num⟩
  · exact ⟨4129, 3, prime_4129, prime_3, by norm_num⟩
  · exact ⟨4133, 2, prime_4133, prime_2, by norm_num⟩
  · exact ⟨4133, 3, prime_4133, prime_3, by norm_num⟩
  · exact ⟨4127, 7, prime_4127, prime_7, by norm_num⟩
  · exact ⟨4139, 2, prime_4139, prime_2, by norm_num⟩
  · exact ⟨4139, 3, prime_4139, prime_3, by norm_num⟩
  · exact ⟨4133, 7, prime_4133, prime_7, by norm_num⟩
  · exact ⟨4139, 5, prime_4139, prime_5, by norm_num⟩
  · exact ⟨4129, 11, prime_4129, prime_11, by norm_num⟩
  · exact ⟨4139, 7, prime_4139, prime_7, by norm_num⟩
  · exact ⟨4133, 11, prime_4133, prime_11, by norm_num⟩
  · exact ⟨4153, 2, prime_4153, prime_2, by norm_num⟩
  · exact ⟨4153, 3, prime_4153, prime_3, by norm_num⟩
  · exact ⟨4157, 2, prime_4157, prime_2, by norm_num⟩
  · exact ⟨4159, 2, prime_4159, prime_2, by norm_num⟩
  · exact ⟨4159, 3, prime_4159, prime_3, by norm_num⟩
  · exact ⟨4157, 5, prime_4157, prime_5, by norm_num⟩
  · exact ⟨4159, 5, prime_4159, prime_5, by norm_num⟩
  · exact ⟨4157, 7, prime_4157, prime_7, by norm_num⟩
  · exact ⟨4159, 7, prime_4159, prime_7, by norm_num⟩
  · exact ⟨4153, 11, prime_4153, prime_11, by norm_num⟩
  · exact ⟨4139, 19, prime_4139, prime_19, by norm_num⟩
  · exact ⟨4157, 11, prime_4157, prime_11, by norm_num⟩
  · exact ⟨4177, 2, prime_4177, prime_2, by norm_num⟩
  · exact ⟨4177, 3, prime_4177, prime_3, by norm_num⟩
  · exact ⟨4159, 13, prime_4159, prime_13, by norm_num⟩
  · exact ⟨4177, 5, prime_4177, prime_5, by norm_num⟩
  · exact ⟨4127, 31, prime_4127, prime_31, by norm_num⟩
  · exact ⟨4177, 7, prime_4177, prime_7, by norm_num⟩
  · exact ⟨4159, 17, prime_4159, prime_17, by norm_num⟩
  · exact ⟨4157, 19, prime_4157, prime_19, by norm_num⟩
  · exact ⟨4159, 19, prime_4159, prime_19, by norm_num⟩
  · exact ⟨4177, 11, prime_4177, prime_11, by norm_num⟩
  · exact ⟨4139, 31, prime_4139, prime_31, by norm_num⟩
  · exact ⟨4177, 13, prime_4177, prime_13, by norm_num⟩
  · exact ⟨4201, 2, prime_4201, prime_2, by norm_num⟩

private theorem lemoine_chunk_21 : ∀ k : ℕ, 2103 ≤ k → k ≤ 2202 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4201, 3, prime_4201, prime_3, by norm_num⟩
  · exact ⟨4127, 41, prime_4127, prime_41, by norm_num⟩
  · exact ⟨4201, 5, prime_4201, prime_5, by norm_num⟩
  · exact ⟨4139, 37, prime_4139, prime_37, by norm_num⟩
  · exact ⟨4211, 2, prime_4211, prime_2, by norm_num⟩
  · exact ⟨4211, 3, prime_4211, prime_3, by norm_num⟩
  · exact ⟨4157, 31, prime_4157, prime_31, by norm_num⟩
  · exact ⟨4217, 2, prime_4217, prime_2, by norm_num⟩
  · exact ⟨4219, 2, prime_4219, prime_2, by norm_num⟩
  · exact ⟨4219, 3, prime_4219, prime_3, by norm_num⟩
  · exact ⟨4217, 5, prime_4217, prime_5, by norm_num⟩
  · exact ⟨4219, 5, prime_4219, prime_5, by norm_num⟩
  · exact ⟨4217, 7, prime_4217, prime_7, by norm_num⟩
  · exact ⟨4229, 2, prime_4229, prime_2, by norm_num⟩
  · exact ⟨4231, 2, prime_4231, prime_2, by norm_num⟩
  · exact ⟨4231, 3, prime_4231, prime_3, by norm_num⟩
  · exact ⟨4229, 5, prime_4229, prime_5, by norm_num⟩
  · exact ⟨4231, 5, prime_4231, prime_5, by norm_num⟩
  · exact ⟨4229, 7, prime_4229, prime_7, by norm_num⟩
  · exact ⟨4241, 2, prime_4241, prime_2, by norm_num⟩
  · exact ⟨4243, 2, prime_4243, prime_2, by norm_num⟩
  · exact ⟨4243, 3, prime_4243, prime_3, by norm_num⟩
  · exact ⟨4241, 5, prime_4241, prime_5, by norm_num⟩
  · exact ⟨4243, 5, prime_4243, prime_5, by norm_num⟩
  · exact ⟨4241, 7, prime_4241, prime_7, by norm_num⟩
  · exact ⟨4253, 2, prime_4253, prime_2, by norm_num⟩
  · exact ⟨4253, 3, prime_4253, prime_3, by norm_num⟩
  · exact ⟨4139, 61, prime_4139, prime_61, by norm_num⟩
  · exact ⟨4259, 2, prime_4259, prime_2, by norm_num⟩
  · exact ⟨4261, 2, prime_4261, prime_2, by norm_num⟩
  · exact ⟨4261, 3, prime_4261, prime_3, by norm_num⟩
  · exact ⟨4259, 5, prime_4259, prime_5, by norm_num⟩
  · exact ⟨4261, 5, prime_4261, prime_5, by norm_num⟩
  · exact ⟨4259, 7, prime_4259, prime_7, by norm_num⟩
  · exact ⟨4271, 2, prime_4271, prime_2, by norm_num⟩
  · exact ⟨4273, 2, prime_4273, prime_2, by norm_num⟩
  · exact ⟨4273, 3, prime_4273, prime_3, by norm_num⟩
  · exact ⟨4271, 5, prime_4271, prime_5, by norm_num⟩
  · exact ⟨4273, 5, prime_4273, prime_5, by norm_num⟩
  · exact ⟨4271, 7, prime_4271, prime_7, by norm_num⟩
  · exact ⟨4283, 2, prime_4283, prime_2, by norm_num⟩
  · exact ⟨4283, 3, prime_4283, prime_3, by norm_num⟩
  · exact ⟨4253, 19, prime_4253, prime_19, by norm_num⟩
  · exact ⟨4289, 2, prime_4289, prime_2, by norm_num⟩
  · exact ⟨4289, 3, prime_4289, prime_3, by norm_num⟩
  · exact ⟨4283, 7, prime_4283, prime_7, by norm_num⟩
  · exact ⟨4289, 5, prime_4289, prime_5, by norm_num⟩
  · exact ⟨4297, 2, prime_4297, prime_2, by norm_num⟩
  · exact ⟨4297, 3, prime_4297, prime_3, by norm_num⟩
  · exact ⟨4283, 11, prime_4283, prime_11, by norm_num⟩
  · exact ⟨4297, 5, prime_4297, prime_5, by norm_num⟩
  · exact ⟨4283, 13, prime_4283, prime_13, by norm_num⟩
  · exact ⟨4297, 7, prime_4297, prime_7, by norm_num⟩
  · exact ⟨4231, 41, prime_4231, prime_41, by norm_num⟩
  · exact ⟨4289, 13, prime_4289, prime_13, by norm_num⟩
  · exact ⟨4283, 17, prime_4283, prime_17, by norm_num⟩
  · exact ⟨4297, 11, prime_4297, prime_11, by norm_num⟩
  · exact ⟨4283, 19, prime_4283, prime_19, by norm_num⟩
  · exact ⟨4297, 13, prime_4297, prime_13, by norm_num⟩
  · exact ⟨4243, 41, prime_4243, prime_41, by norm_num⟩
  · exact ⟨4289, 19, prime_4289, prime_19, by norm_num⟩
  · exact ⟨4283, 23, prime_4283, prime_23, by norm_num⟩
  · exact ⟨4327, 2, prime_4327, prime_2, by norm_num⟩
  · exact ⟨4327, 3, prime_4327, prime_3, by norm_num⟩
  · exact ⟨4297, 19, prime_4297, prime_19, by norm_num⟩
  · exact ⟨4327, 5, prime_4327, prime_5, by norm_num⟩
  · exact ⟨4253, 43, prime_4253, prime_43, by norm_num⟩
  · exact ⟨4337, 2, prime_4337, prime_2, by norm_num⟩
  · exact ⟨4339, 2, prime_4339, prime_2, by norm_num⟩
  · exact ⟨4339, 3, prime_4339, prime_3, by norm_num⟩
  · exact ⟨4337, 5, prime_4337, prime_5, by norm_num⟩
  · exact ⟨4339, 5, prime_4339, prime_5, by norm_num⟩
  · exact ⟨4337, 7, prime_4337, prime_7, by norm_num⟩
  · exact ⟨4349, 2, prime_4349, prime_2, by norm_num⟩
  · exact ⟨4349, 3, prime_4349, prime_3, by norm_num⟩
  · exact ⟨4283, 37, prime_4283, prime_37, by norm_num⟩
  · exact ⟨4349, 5, prime_4349, prime_5, by norm_num⟩
  · exact ⟨4357, 2, prime_4357, prime_2, by norm_num⟩
  · exact ⟨4357, 3, prime_4357, prime_3, by norm_num⟩
  · exact ⟨4339, 13, prime_4339, prime_13, by norm_num⟩
  · exact ⟨4363, 2, prime_4363, prime_2, by norm_num⟩
  · exact ⟨4363, 3, prime_4363, prime_3, by norm_num⟩
  · exact ⟨4357, 7, prime_4357, prime_7, by norm_num⟩
  · exact ⟨4363, 5, prime_4363, prime_5, by norm_num⟩
  · exact ⟨4349, 13, prime_4349, prime_13, by norm_num⟩
  · exact ⟨4373, 2, prime_4373, prime_2, by norm_num⟩
  · exact ⟨4373, 3, prime_4373, prime_3, by norm_num⟩
  · exact ⟨4259, 61, prime_4259, prime_61, by norm_num⟩
  · exact ⟨4373, 5, prime_4373, prime_5, by norm_num⟩
  · exact ⟨4363, 11, prime_4363, prime_11, by norm_num⟩
  · exact ⟨4373, 7, prime_4373, prime_7, by norm_num⟩
  · exact ⟨4363, 13, prime_4363, prime_13, by norm_num⟩
  · exact ⟨4357, 17, prime_4357, prime_17, by norm_num⟩
  · exact ⟨4271, 61, prime_4271, prime_61, by norm_num⟩
  · exact ⟨4391, 2, prime_4391, prime_2, by norm_num⟩
  · exact ⟨4391, 3, prime_4391, prime_3, by norm_num⟩
  · exact ⟨4373, 13, prime_4373, prime_13, by norm_num⟩
  · exact ⟨4397, 2, prime_4397, prime_2, by norm_num⟩
  · exact ⟨4397, 3, prime_4397, prime_3, by norm_num⟩
  · exact ⟨4391, 7, prime_4391, prime_7, by norm_num⟩

private theorem lemoine_chunk_22 : ∀ k : ℕ, 2203 ≤ k → k ≤ 2302 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4397, 5, prime_4397, prime_5, by norm_num⟩
  · exact ⟨4363, 23, prime_4363, prime_23, by norm_num⟩
  · exact ⟨4397, 7, prime_4397, prime_7, by norm_num⟩
  · exact ⟨4409, 2, prime_4409, prime_2, by norm_num⟩
  · exact ⟨4409, 3, prime_4409, prime_3, by norm_num⟩
  · exact ⟨4391, 13, prime_4391, prime_13, by norm_num⟩
  · exact ⟨4409, 5, prime_4409, prime_5, by norm_num⟩
  · exact ⟨4363, 29, prime_4363, prime_29, by norm_num⟩
  · exact ⟨4409, 7, prime_4409, prime_7, by norm_num⟩
  · exact ⟨4421, 2, prime_4421, prime_2, by norm_num⟩
  · exact ⟨4423, 2, prime_4423, prime_2, by norm_num⟩
  · exact ⟨4423, 3, prime_4423, prime_3, by norm_num⟩
  · exact ⟨4421, 5, prime_4421, prime_5, by norm_num⟩
  · exact ⟨4423, 5, prime_4423, prime_5, by norm_num⟩
  · exact ⟨4421, 7, prime_4421, prime_7, by norm_num⟩
  · exact ⟨4423, 7, prime_4423, prime_7, by norm_num⟩
  · exact ⟨4357, 41, prime_4357, prime_41, by norm_num⟩
  · exact ⟨4283, 79, prime_4283, prime_79, by norm_num⟩
  · exact ⟨4421, 11, prime_4421, prime_11, by norm_num⟩
  · exact ⟨4441, 2, prime_4441, prime_2, by norm_num⟩
  · exact ⟨4441, 3, prime_4441, prime_3, by norm_num⟩
  · exact ⟨4423, 13, prime_4423, prime_13, by norm_num⟩
  · exact ⟨4447, 2, prime_4447, prime_2, by norm_num⟩
  · exact ⟨4447, 3, prime_4447, prime_3, by norm_num⟩
  · exact ⟨4451, 2, prime_4451, prime_2, by norm_num⟩
  · exact ⟨4451, 3, prime_4451, prime_3, by norm_num⟩
  · exact ⟨4421, 19, prime_4421, prime_19, by norm_num⟩
  · exact ⟨4457, 2, prime_4457, prime_2, by norm_num⟩
  · exact ⟨4457, 3, prime_4457, prime_3, by norm_num⟩
  · exact ⟨4451, 7, prime_4451, prime_7, by norm_num⟩
  · exact ⟨4463, 2, prime_4463, prime_2, by norm_num⟩
  · exact ⟨4463, 3, prime_4463, prime_3, by norm_num⟩
  · exact ⟨4457, 7, prime_4457, prime_7, by norm_num⟩
  · exact ⟨4463, 5, prime_4463, prime_5, by norm_num⟩
  · exact ⟨4441, 17, prime_4441, prime_17, by norm_num⟩
  · exact ⟨4463, 7, prime_4463, prime_7, by norm_num⟩
  · exact ⟨4457, 11, prime_4457, prime_11, by norm_num⟩
  · exact ⟨4447, 17, prime_4447, prime_17, by norm_num⟩
  · exact ⟨4457, 13, prime_4457, prime_13, by norm_num⟩
  · exact ⟨4481, 2, prime_4481, prime_2, by norm_num⟩
  · exact ⟨4483, 2, prime_4483, prime_2, by norm_num⟩
  · exact ⟨4483, 3, prime_4483, prime_3, by norm_num⟩
  · exact ⟨4481, 5, prime_4481, prime_5, by norm_num⟩
  · exact ⟨4483, 5, prime_4483, prime_5, by norm_num⟩
  · exact ⟨4481, 7, prime_4481, prime_7, by norm_num⟩
  · exact ⟨4493, 2, prime_4493, prime_2, by norm_num⟩
  · exact ⟨4493, 3, prime_4493, prime_3, by norm_num⟩
  · exact ⟨4463, 19, prime_4463, prime_19, by norm_num⟩
  · exact ⟨4493, 5, prime_4493, prime_5, by norm_num⟩
  · exact ⟨4483, 11, prime_4483, prime_11, by norm_num⟩
  · exact ⟨4493, 7, prime_4493, prime_7, by norm_num⟩
  · exact ⟨4483, 13, prime_4483, prime_13, by norm_num⟩
  · exact ⟨4507, 2, prime_4507, prime_2, by norm_num⟩
  · exact ⟨4507, 3, prime_4507, prime_3, by norm_num⟩
  · exact ⟨4493, 11, prime_4493, prime_11, by norm_num⟩
  · exact ⟨4513, 2, prime_4513, prime_2, by norm_num⟩
  · exact ⟨4513, 3, prime_4513, prime_3, by norm_num⟩
  · exact ⟨4517, 2, prime_4517, prime_2, by norm_num⟩
  · exact ⟨4519, 2, prime_4519, prime_2, by norm_num⟩
  · exact ⟨4519, 3, prime_4519, prime_3, by norm_num⟩
  · exact ⟨4523, 2, prime_4523, prime_2, by norm_num⟩
  · exact ⟨4523, 3, prime_4523, prime_3, by norm_num⟩
  · exact ⟨4517, 7, prime_4517, prime_7, by norm_num⟩
  · exact ⟨4523, 5, prime_4523, prime_5, by norm_num⟩
  · exact ⟨4513, 11, prime_4513, prime_11, by norm_num⟩
  · exact ⟨4523, 7, prime_4523, prime_7, by norm_num⟩
  · exact ⟨4517, 11, prime_4517, prime_11, by norm_num⟩
  · exact ⟨4519, 11, prime_4519, prime_11, by norm_num⟩
  · exact ⟨4517, 13, prime_4517, prime_13, by norm_num⟩
  · exact ⟨4523, 11, prime_4523, prime_11, by norm_num⟩
  · exact ⟨4513, 17, prime_4513, prime_17, by norm_num⟩
  · exact ⟨4523, 13, prime_4523, prime_13, by norm_num⟩
  · exact ⟨4547, 2, prime_4547, prime_2, by norm_num⟩
  · exact ⟨4549, 2, prime_4549, prime_2, by norm_num⟩
  · exact ⟨4549, 3, prime_4549, prime_3, by norm_num⟩
  · exact ⟨4547, 5, prime_4547, prime_5, by norm_num⟩
  · exact ⟨4549, 5, prime_4549, prime_5, by norm_num⟩
  · exact ⟨4547, 7, prime_4547, prime_7, by norm_num⟩
  · exact ⟨4549, 7, prime_4549, prime_7, by norm_num⟩
  · exact ⟨4561, 2, prime_4561, prime_2, by norm_num⟩
  · exact ⟨4561, 3, prime_4561, prime_3, by norm_num⟩
  · exact ⟨4547, 11, prime_4547, prime_11, by norm_num⟩
  · exact ⟨4567, 2, prime_4567, prime_2, by norm_num⟩
  · exact ⟨4567, 3, prime_4567, prime_3, by norm_num⟩
  · exact ⟨4561, 7, prime_4561, prime_7, by norm_num⟩
  · exact ⟨4567, 5, prime_4567, prime_5, by norm_num⟩
  · exact ⟨4517, 31, prime_4517, prime_31, by norm_num⟩
  · exact ⟨4567, 7, prime_4567, prime_7, by norm_num⟩
  · exact ⟨4561, 11, prime_4561, prime_11, by norm_num⟩
  · exact ⟨4547, 19, prime_4547, prime_19, by norm_num⟩
  · exact ⟨4583, 2, prime_4583, prime_2, by norm_num⟩
  · exact ⟨4583, 3, prime_4583, prime_3, by norm_num⟩
  · exact ⟨4517, 37, prime_4517, prime_37, by norm_num⟩
  · exact ⟨4583, 5, prime_4583, prime_5, by norm_num⟩
  · exact ⟨4591, 2, prime_4591, prime_2, by norm_num⟩
  · exact ⟨4591, 3, prime_4591, prime_3, by norm_num⟩
  · exact ⟨4561, 19, prime_4561, prime_19, by norm_num⟩
  · exact ⟨4597, 2, prime_4597, prime_2, by norm_num⟩
  · exact ⟨4597, 3, prime_4597, prime_3, by norm_num⟩
  · exact ⟨4591, 7, prime_4591, prime_7, by norm_num⟩

private theorem lemoine_chunk_23 : ∀ k : ℕ, 2303 ≤ k → k ≤ 2402 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4603, 2, prime_4603, prime_2, by norm_num⟩
  · exact ⟨4603, 3, prime_4603, prime_3, by norm_num⟩
  · exact ⟨4597, 7, prime_4597, prime_7, by norm_num⟩
  · exact ⟨4603, 5, prime_4603, prime_5, by norm_num⟩
  · exact ⟨4493, 61, prime_4493, prime_61, by norm_num⟩
  · exact ⟨4603, 7, prime_4603, prime_7, by norm_num⟩
  · exact ⟨4597, 11, prime_4597, prime_11, by norm_num⟩
  · exact ⟨4583, 19, prime_4583, prime_19, by norm_num⟩
  · exact ⟨4597, 13, prime_4597, prime_13, by norm_num⟩
  · exact ⟨4621, 2, prime_4621, prime_2, by norm_num⟩
  · exact ⟨4621, 3, prime_4621, prime_3, by norm_num⟩
  · exact ⟨4603, 13, prime_4603, prime_13, by norm_num⟩
  · exact ⟨4621, 5, prime_4621, prime_5, by norm_num⟩
  · exact ⟨4547, 43, prime_4547, prime_43, by norm_num⟩
  · exact ⟨4621, 7, prime_4621, prime_7, by norm_num⟩
  · exact ⟨4603, 17, prime_4603, prime_17, by norm_num⟩
  · exact ⟨4517, 61, prime_4517, prime_61, by norm_num⟩
  · exact ⟨4637, 2, prime_4637, prime_2, by norm_num⟩
  · exact ⟨4639, 2, prime_4639, prime_2, by norm_num⟩
  · exact ⟨4639, 3, prime_4639, prime_3, by norm_num⟩
  · exact ⟨4643, 2, prime_4643, prime_2, by norm_num⟩
  · exact ⟨4643, 3, prime_4643, prime_3, by norm_num⟩
  · exact ⟨4637, 7, prime_4637, prime_7, by norm_num⟩
  · exact ⟨4649, 2, prime_4649, prime_2, by norm_num⟩
  · exact ⟨4651, 2, prime_4651, prime_2, by norm_num⟩
  · exact ⟨4651, 3, prime_4651, prime_3, by norm_num⟩
  · exact ⟨4649, 5, prime_4649, prime_5, by norm_num⟩
  · exact ⟨4657, 2, prime_4657, prime_2, by norm_num⟩
  · exact ⟨4657, 3, prime_4657, prime_3, by norm_num⟩
  · exact ⟨4651, 7, prime_4651, prime_7, by norm_num⟩
  · exact ⟨4663, 2, prime_4663, prime_2, by norm_num⟩
  · exact ⟨4663, 3, prime_4663, prime_3, by norm_num⟩
  · exact ⟨4657, 7, prime_4657, prime_7, by norm_num⟩
  · exact ⟨4663, 5, prime_4663, prime_5, by norm_num⟩
  · exact ⟨4649, 13, prime_4649, prime_13, by norm_num⟩
  · exact ⟨4673, 2, prime_4673, prime_2, by norm_num⟩
  · exact ⟨4673, 3, prime_4673, prime_3, by norm_num⟩
  · exact ⟨4643, 19, prime_4643, prime_19, by norm_num⟩
  · exact ⟨4679, 2, prime_4679, prime_2, by norm_num⟩
  · exact ⟨4679, 3, prime_4679, prime_3, by norm_num⟩
  · exact ⟨4673, 7, prime_4673, prime_7, by norm_num⟩
  · exact ⟨4679, 5, prime_4679, prime_5, by norm_num⟩
  · exact ⟨4657, 17, prime_4657, prime_17, by norm_num⟩
  · exact ⟨4679, 7, prime_4679, prime_7, by norm_num⟩
  · exact ⟨4691, 2, prime_4691, prime_2, by norm_num⟩
  · exact ⟨4691, 3, prime_4691, prime_3, by norm_num⟩
  · exact ⟨4673, 13, prime_4673, prime_13, by norm_num⟩
  · exact ⟨4691, 5, prime_4691, prime_5, by norm_num⟩
  · exact ⟨4657, 23, prime_4657, prime_23, by norm_num⟩
  · exact ⟨4691, 7, prime_4691, prime_7, by norm_num⟩
  · exact ⟨4703, 2, prime_4703, prime_2, by norm_num⟩
  · exact ⟨4703, 3, prime_4703, prime_3, by norm_num⟩
  · exact ⟨4673, 19, prime_4673, prime_19, by norm_num⟩
  · exact ⟨4703, 5, prime_4703, prime_5, by norm_num⟩
  · exact ⟨4657, 29, prime_4657, prime_29, by norm_num⟩
  · exact ⟨4703, 7, prime_4703, prime_7, by norm_num⟩
  · exact ⟨4673, 23, prime_4673, prime_23, by norm_num⟩
  · exact ⟨4663, 29, prime_4663, prime_29, by norm_num⟩
  · exact ⟨4649, 37, prime_4649, prime_37, by norm_num⟩
  · exact ⟨4721, 2, prime_4721, prime_2, by norm_num⟩
  · exact ⟨4723, 2, prime_4723, prime_2, by norm_num⟩
  · exact ⟨4723, 3, prime_4723, prime_3, by norm_num⟩
  · exact ⟨4721, 5, prime_4721, prime_5, by norm_num⟩
  · exact ⟨4729, 2, prime_4729, prime_2, by norm_num⟩
  · exact ⟨4729, 3, prime_4729, prime_3, by norm_num⟩
  · exact ⟨4733, 2, prime_4733, prime_2, by norm_num⟩
  · exact ⟨4733, 3, prime_4733, prime_3, by norm_num⟩
  · exact ⟨4703, 19, prime_4703, prime_19, by norm_num⟩
  · exact ⟨4733, 5, prime_4733, prime_5, by norm_num⟩
  · exact ⟨4723, 11, prime_4723, prime_11, by norm_num⟩
  · exact ⟨4733, 7, prime_4733, prime_7, by norm_num⟩
  · exact ⟨4723, 13, prime_4723, prime_13, by norm_num⟩
  · exact ⟨4729, 11, prime_4729, prime_11, by norm_num⟩
  · exact ⟨4691, 31, prime_4691, prime_31, by norm_num⟩
  · exact ⟨4751, 2, prime_4751, prime_2, by norm_num⟩
  · exact ⟨4751, 3, prime_4751, prime_3, by norm_num⟩
  · exact ⟨4733, 13, prime_4733, prime_13, by norm_num⟩
  · exact ⟨4751, 5, prime_4751, prime_5, by norm_num⟩
  · exact ⟨4759, 2, prime_4759, prime_2, by norm_num⟩
  · exact ⟨4759, 3, prime_4759, prime_3, by norm_num⟩
  · exact ⟨4733, 17, prime_4733, prime_17, by norm_num⟩
  · exact ⟨4759, 5, prime_4759, prime_5, by norm_num⟩
  · exact ⟨4733, 19, prime_4733, prime_19, by norm_num⟩
  · exact ⟨4759, 7, prime_4759, prime_7, by norm_num⟩
  · exact ⟨4729, 23, prime_4729, prime_23, by norm_num⟩
  · exact ⟨4751, 13, prime_4751, prime_13, by norm_num⟩
  · exact ⟨4733, 23, prime_4733, prime_23, by norm_num⟩
  · exact ⟨4759, 11, prime_4759, prime_11, by norm_num⟩
  · exact ⟨4721, 31, prime_4721, prime_31, by norm_num⟩
  · exact ⟨4759, 13, prime_4759, prime_13, by norm_num⟩
  · exact ⟨4783, 2, prime_4783, prime_2, by norm_num⟩
  · exact ⟨4783, 3, prime_4783, prime_3, by norm_num⟩
  · exact ⟨4787, 2, prime_4787, prime_2, by norm_num⟩
  · exact ⟨4789, 2, prime_4789, prime_2, by norm_num⟩
  · exact ⟨4789, 3, prime_4789, prime_3, by norm_num⟩
  · exact ⟨4793, 2, prime_4793, prime_2, by norm_num⟩
  · exact ⟨4793, 3, prime_4793, prime_3, by norm_num⟩
  · exact ⟨4787, 7, prime_4787, prime_7, by norm_num⟩
  · exact ⟨4799, 2, prime_4799, prime_2, by norm_num⟩
  · exact ⟨4801, 2, prime_4801, prime_2, by norm_num⟩

private theorem lemoine_chunk_24 : ∀ k : ℕ, 2403 ≤ k → k ≤ 2502 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨4801, 3, prime_4801, prime_3, by norm_num⟩
  · exact ⟨4799, 5, prime_4799, prime_5, by norm_num⟩
  · exact ⟨4801, 5, prime_4801, prime_5, by norm_num⟩
  · exact ⟨4799, 7, prime_4799, prime_7, by norm_num⟩
  · exact ⟨4801, 7, prime_4801, prime_7, by norm_num⟩
  · exact ⟨4813, 2, prime_4813, prime_2, by norm_num⟩
  · exact ⟨4813, 3, prime_4813, prime_3, by norm_num⟩
  · exact ⟨4817, 2, prime_4817, prime_2, by norm_num⟩
  · exact ⟨4817, 3, prime_4817, prime_3, by norm_num⟩
  · exact ⟨4799, 13, prime_4799, prime_13, by norm_num⟩
  · exact ⟨4817, 5, prime_4817, prime_5, by norm_num⟩
  · exact ⟨4783, 23, prime_4783, prime_23, by norm_num⟩
  · exact ⟨4817, 7, prime_4817, prime_7, by norm_num⟩
  · exact ⟨4799, 17, prime_4799, prime_17, by norm_num⟩
  · exact ⟨4831, 2, prime_4831, prime_2, by norm_num⟩
  · exact ⟨4831, 3, prime_4831, prime_3, by norm_num⟩
  · exact ⟨4817, 11, prime_4817, prime_11, by norm_num⟩
  · exact ⟨4831, 5, prime_4831, prime_5, by norm_num⟩
  · exact ⟨4817, 13, prime_4817, prime_13, by norm_num⟩
  · exact ⟨4831, 7, prime_4831, prime_7, by norm_num⟩
  · exact ⟨4813, 17, prime_4813, prime_17, by norm_num⟩
  · exact ⟨4787, 31, prime_4787, prime_31, by norm_num⟩
  · exact ⟨4817, 17, prime_4817, prime_17, by norm_num⟩
  · exact ⟨4831, 11, prime_4831, prime_11, by norm_num⟩
  · exact ⟨4817, 19, prime_4817, prime_19, by norm_num⟩
  · exact ⟨4831, 13, prime_4831, prime_13, by norm_num⟩
  · exact ⟨4813, 23, prime_4813, prime_23, by norm_num⟩
  · exact ⟨4799, 31, prime_4799, prime_31, by norm_num⟩
  · exact ⟨4817, 23, prime_4817, prime_23, by norm_num⟩
  · exact ⟨4861, 2, prime_4861, prime_2, by norm_num⟩
  · exact ⟨4861, 3, prime_4861, prime_3, by norm_num⟩
  · exact ⟨4831, 19, prime_4831, prime_19, by norm_num⟩
  · exact ⟨4861, 5, prime_4861, prime_5, by norm_num⟩
  · exact ⟨4799, 37, prime_4799, prime_37, by norm_num⟩
  · exact ⟨4871, 2, prime_4871, prime_2, by norm_num⟩
  · exact ⟨4871, 3, prime_4871, prime_3, by norm_num⟩
  · exact ⟨4817, 31, prime_4817, prime_31, by norm_num⟩
  · exact ⟨4877, 2, prime_4877, prime_2, by norm_num⟩
  · exact ⟨4877, 3, prime_4877, prime_3, by norm_num⟩
  · exact ⟨4871, 7, prime_4871, prime_7, by norm_num⟩
  · exact ⟨4877, 5, prime_4877, prime_5, by norm_num⟩
  · exact ⟨4831, 29, prime_4831, prime_29, by norm_num⟩
  · exact ⟨4877, 7, prime_4877, prime_7, by norm_num⟩
  · exact ⟨4889, 2, prime_4889, prime_2, by norm_num⟩
  · exact ⟨4889, 3, prime_4889, prime_3, by norm_num⟩
  · exact ⟨4871, 13, prime_4871, prime_13, by norm_num⟩
  · exact ⟨4889, 5, prime_4889, prime_5, by norm_num⟩
  · exact ⟨4783, 59, prime_4783, prime_59, by norm_num⟩
  · exact ⟨4889, 7, prime_4889, prime_7, by norm_num⟩
  · exact ⟨4871, 17, prime_4871, prime_17, by norm_num⟩
  · exact ⟨4903, 2, prime_4903, prime_2, by norm_num⟩
  · exact ⟨4903, 3, prime_4903, prime_3, by norm_num⟩
  · exact ⟨4889, 11, prime_4889, prime_11, by norm_num⟩
  · exact ⟨4909, 2, prime_4909, prime_2, by norm_num⟩
  · exact ⟨4909, 3, prime_4909, prime_3, by norm_num⟩
  · exact ⟨4903, 7, prime_4903, prime_7, by norm_num⟩
  · exact ⟨4909, 5, prime_4909, prime_5, by norm_num⟩
  · exact ⟨4799, 61, prime_4799, prime_61, by norm_num⟩
  · exact ⟨4919, 2, prime_4919, prime_2, by norm_num⟩
  · exact ⟨4919, 3, prime_4919, prime_3, by norm_num⟩
  · exact ⟨4889, 19, prime_4889, prime_19, by norm_num⟩
  · exact ⟨4919, 5, prime_4919, prime_5, by norm_num⟩
  · exact ⟨4909, 11, prime_4909, prime_11, by norm_num⟩
  · exact ⟨4919, 7, prime_4919, prime_7, by norm_num⟩
  · exact ⟨4931, 2, prime_4931, prime_2, by norm_num⟩
  · exact ⟨4933, 2, prime_4933, prime_2, by norm_num⟩
  · exact ⟨4933, 3, prime_4933, prime_3, by norm_num⟩
  · exact ⟨4937, 2, prime_4937, prime_2, by norm_num⟩
  · exact ⟨4937, 3, prime_4937, prime_3, by norm_num⟩
  · exact ⟨4931, 7, prime_4931, prime_7, by norm_num⟩
  · exact ⟨4943, 2, prime_4943, prime_2, by norm_num⟩
  · exact ⟨4943, 3, prime_4943, prime_3, by norm_num⟩
  · exact ⟨4937, 7, prime_4937, prime_7, by norm_num⟩
  · exact ⟨4943, 5, prime_4943, prime_5, by norm_num⟩
  · exact ⟨4951, 2, prime_4951, prime_2, by norm_num⟩
  · exact ⟨4951, 3, prime_4951, prime_3, by norm_num⟩
  · exact ⟨4937, 11, prime_4937, prime_11, by norm_num⟩
  · exact ⟨4957, 2, prime_4957, prime_2, by norm_num⟩
  · exact ⟨4957, 3, prime_4957, prime_3, by norm_num⟩
  · exact ⟨4951, 7, prime_4951, prime_7, by norm_num⟩
  · exact ⟨4957, 5, prime_4957, prime_5, by norm_num⟩
  · exact ⟨4943, 13, prime_4943, prime_13, by norm_num⟩
  · exact ⟨4967, 2, prime_4967, prime_2, by norm_num⟩
  · exact ⟨4969, 2, prime_4969, prime_2, by norm_num⟩
  · exact ⟨4969, 3, prime_4969, prime_3, by norm_num⟩
  · exact ⟨4973, 2, prime_4973, prime_2, by norm_num⟩
  · exact ⟨4973, 3, prime_4973, prime_3, by norm_num⟩
  · exact ⟨4967, 7, prime_4967, prime_7, by norm_num⟩
  · exact ⟨4973, 5, prime_4973, prime_5, by norm_num⟩
  · exact ⟨4951, 17, prime_4951, prime_17, by norm_num⟩
  · exact ⟨4973, 7, prime_4973, prime_7, by norm_num⟩
  · exact ⟨4967, 11, prime_4967, prime_11, by norm_num⟩
  · exact ⟨4987, 2, prime_4987, prime_2, by norm_num⟩
  · exact ⟨4987, 3, prime_4987, prime_3, by norm_num⟩
  · exact ⟨4973, 11, prime_4973, prime_11, by norm_num⟩
  · exact ⟨4993, 2, prime_4993, prime_2, by norm_num⟩
  · exact ⟨4993, 3, prime_4993, prime_3, by norm_num⟩
  · exact ⟨4987, 7, prime_4987, prime_7, by norm_num⟩
  · exact ⟨4999, 2, prime_4999, prime_2, by norm_num⟩
  · exact ⟨4999, 3, prime_4999, prime_3, by norm_num⟩

private theorem lemoine_chunk_25 : ∀ k : ℕ, 2503 ≤ k → k ≤ 2602 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5003, 2, prime_5003, prime_2, by norm_num⟩
  · exact ⟨5003, 3, prime_5003, prime_3, by norm_num⟩
  · exact ⟨4973, 19, prime_4973, prime_19, by norm_num⟩
  · exact ⟨5009, 2, prime_5009, prime_2, by norm_num⟩
  · exact ⟨5011, 2, prime_5011, prime_2, by norm_num⟩
  · exact ⟨5011, 3, prime_5011, prime_3, by norm_num⟩
  · exact ⟨5009, 5, prime_5009, prime_5, by norm_num⟩
  · exact ⟨5011, 5, prime_5011, prime_5, by norm_num⟩
  · exact ⟨5009, 7, prime_5009, prime_7, by norm_num⟩
  · exact ⟨5021, 2, prime_5021, prime_2, by norm_num⟩
  · exact ⟨5023, 2, prime_5023, prime_2, by norm_num⟩
  · exact ⟨5023, 3, prime_5023, prime_3, by norm_num⟩
  · exact ⟨5021, 5, prime_5021, prime_5, by norm_num⟩
  · exact ⟨5023, 5, prime_5023, prime_5, by norm_num⟩
  · exact ⟨5021, 7, prime_5021, prime_7, by norm_num⟩
  · exact ⟨5023, 7, prime_5023, prime_7, by norm_num⟩
  · exact ⟨4993, 23, prime_4993, prime_23, by norm_num⟩
  · exact ⟨5003, 19, prime_5003, prime_19, by norm_num⟩
  · exact ⟨5039, 2, prime_5039, prime_2, by norm_num⟩
  · exact ⟨5039, 3, prime_5039, prime_3, by norm_num⟩
  · exact ⟨5021, 13, prime_5021, prime_13, by norm_num⟩
  · exact ⟨5039, 5, prime_5039, prime_5, by norm_num⟩
  · exact ⟨4993, 29, prime_4993, prime_29, by norm_num⟩
  · exact ⟨5039, 7, prime_5039, prime_7, by norm_num⟩
  · exact ⟨5051, 2, prime_5051, prime_2, by norm_num⟩
  · exact ⟨5051, 3, prime_5051, prime_3, by norm_num⟩
  · exact ⟨5021, 19, prime_5021, prime_19, by norm_num⟩
  · exact ⟨5051, 5, prime_5051, prime_5, by norm_num⟩
  · exact ⟨5059, 2, prime_5059, prime_2, by norm_num⟩
  · exact ⟨5059, 3, prime_5059, prime_3, by norm_num⟩
  · exact ⟨5021, 23, prime_5021, prime_23, by norm_num⟩
  · exact ⟨5059, 5, prime_5059, prime_5, by norm_num⟩
  · exact ⟨5009, 31, prime_5009, prime_31, by norm_num⟩
  · exact ⟨5059, 7, prime_5059, prime_7, by norm_num⟩
  · exact ⟨4993, 41, prime_4993, prime_41, by norm_num⟩
  · exact ⟨5051, 13, prime_5051, prime_13, by norm_num⟩
  · exact ⟨5021, 29, prime_5021, prime_29, by norm_num⟩
  · exact ⟨5077, 2, prime_5077, prime_2, by norm_num⟩
  · exact ⟨5077, 3, prime_5077, prime_3, by norm_num⟩
  · exact ⟨5081, 2, prime_5081, prime_2, by norm_num⟩
  · exact ⟨5081, 3, prime_5081, prime_3, by norm_num⟩
  · exact ⟨5051, 19, prime_5051, prime_19, by norm_num⟩
  · exact ⟨5087, 2, prime_5087, prime_2, by norm_num⟩
  · exact ⟨5087, 3, prime_5087, prime_3, by norm_num⟩
  · exact ⟨5081, 7, prime_5081, prime_7, by norm_num⟩
  · exact ⟨5087, 5, prime_5087, prime_5, by norm_num⟩
  · exact ⟨5077, 11, prime_5077, prime_11, by norm_num⟩
  · exact ⟨5087, 7, prime_5087, prime_7, by norm_num⟩
  · exact ⟨5099, 2, prime_5099, prime_2, by norm_num⟩
  · exact ⟨5101, 2, prime_5101, prime_2, by norm_num⟩
  · exact ⟨5101, 3, prime_5101, prime_3, by norm_num⟩
  · exact ⟨5099, 5, prime_5099, prime_5, by norm_num⟩
  · exact ⟨5107, 2, prime_5107, prime_2, by norm_num⟩
  · exact ⟨5107, 3, prime_5107, prime_3, by norm_num⟩
  · exact ⟨5101, 7, prime_5101, prime_7, by norm_num⟩
  · exact ⟨5113, 2, prime_5113, prime_2, by norm_num⟩
  · exact ⟨5113, 3, prime_5113, prime_3, by norm_num⟩
  · exact ⟨5107, 7, prime_5107, prime_7, by norm_num⟩
  · exact ⟨5119, 2, prime_5119, prime_2, by norm_num⟩
  · exact ⟨5119, 3, prime_5119, prime_3, by norm_num⟩
  · exact ⟨5113, 7, prime_5113, prime_7, by norm_num⟩
  · exact ⟨5119, 5, prime_5119, prime_5, by norm_num⟩
  · exact ⟨5009, 61, prime_5009, prime_61, by norm_num⟩
  · exact ⟨5119, 7, prime_5119, prime_7, by norm_num⟩
  · exact ⟨5113, 11, prime_5113, prime_11, by norm_num⟩
  · exact ⟨5099, 19, prime_5099, prime_19, by norm_num⟩
  · exact ⟨5113, 13, prime_5113, prime_13, by norm_num⟩
  · exact ⟨5119, 11, prime_5119, prime_11, by norm_num⟩
  · exact ⟨5081, 31, prime_5081, prime_31, by norm_num⟩
  · exact ⟨5119, 13, prime_5119, prime_13, by norm_num⟩
  · exact ⟨5113, 17, prime_5113, prime_17, by norm_num⟩
  · exact ⟨5087, 31, prime_5087, prime_31, by norm_num⟩
  · exact ⟨5147, 2, prime_5147, prime_2, by norm_num⟩
  · exact ⟨5147, 3, prime_5147, prime_3, by norm_num⟩
  · exact ⟨5081, 37, prime_5081, prime_37, by norm_num⟩
  · exact ⟨5153, 2, prime_5153, prime_2, by norm_num⟩
  · exact ⟨5153, 3, prime_5153, prime_3, by norm_num⟩
  · exact ⟨5147, 7, prime_5147, prime_7, by norm_num⟩
  · exact ⟨5153, 5, prime_5153, prime_5, by norm_num⟩
  · exact ⟨5119, 23, prime_5119, prime_23, by norm_num⟩
  · exact ⟨5153, 7, prime_5153, prime_7, by norm_num⟩
  · exact ⟨5147, 11, prime_5147, prime_11, by norm_num⟩
  · exact ⟨5167, 2, prime_5167, prime_2, by norm_num⟩
  · exact ⟨5167, 3, prime_5167, prime_3, by norm_num⟩
  · exact ⟨5171, 2, prime_5171, prime_2, by norm_num⟩
  · exact ⟨5171, 3, prime_5171, prime_3, by norm_num⟩
  · exact ⟨5153, 13, prime_5153, prime_13, by norm_num⟩
  · exact ⟨5171, 5, prime_5171, prime_5, by norm_num⟩
  · exact ⟨5179, 2, prime_5179, prime_2, by norm_num⟩
  · exact ⟨5179, 3, prime_5179, prime_3, by norm_num⟩
  · exact ⟨5153, 17, prime_5153, prime_17, by norm_num⟩
  · exact ⟨5179, 5, prime_5179, prime_5, by norm_num⟩
  · exact ⟨5153, 19, prime_5153, prime_19, by norm_num⟩
  · exact ⟨5189, 2, prime_5189, prime_2, by norm_num⟩
  · exact ⟨5189, 3, prime_5189, prime_3, by norm_num⟩
  · exact ⟨5171, 13, prime_5171, prime_13, by norm_num⟩
  · exact ⟨5189, 5, prime_5189, prime_5, by norm_num⟩
  · exact ⟨5197, 2, prime_5197, prime_2, by norm_num⟩
  · exact ⟨5197, 3, prime_5197, prime_3, by norm_num⟩
  · exact ⟨5179, 13, prime_5179, prime_13, by norm_num⟩

private theorem lemoine_chunk_26 : ∀ k : ℕ, 2603 ≤ k → k ≤ 2702 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5197, 5, prime_5197, prime_5, by norm_num⟩
  · exact ⟨5171, 19, prime_5171, prime_19, by norm_num⟩
  · exact ⟨5197, 7, prime_5197, prime_7, by norm_num⟩
  · exact ⟨5209, 2, prime_5209, prime_2, by norm_num⟩
  · exact ⟨5209, 3, prime_5209, prime_3, by norm_num⟩
  · exact ⟨5179, 19, prime_5179, prime_19, by norm_num⟩
  · exact ⟨5209, 5, prime_5209, prime_5, by norm_num⟩
  · exact ⟨5147, 37, prime_5147, prime_37, by norm_num⟩
  · exact ⟨5209, 7, prime_5209, prime_7, by norm_num⟩
  · exact ⟨5179, 23, prime_5179, prime_23, by norm_num⟩
  · exact ⟨5189, 19, prime_5189, prime_19, by norm_num⟩
  · exact ⟨5171, 29, prime_5171, prime_29, by norm_num⟩
  · exact ⟨5227, 2, prime_5227, prime_2, by norm_num⟩
  · exact ⟨5227, 3, prime_5227, prime_3, by norm_num⟩
  · exact ⟨5231, 2, prime_5231, prime_2, by norm_num⟩
  · exact ⟨5233, 2, prime_5233, prime_2, by norm_num⟩
  · exact ⟨5233, 3, prime_5233, prime_3, by norm_num⟩
  · exact ⟨5237, 2, prime_5237, prime_2, by norm_num⟩
  · exact ⟨5237, 3, prime_5237, prime_3, by norm_num⟩
  · exact ⟨5231, 7, prime_5231, prime_7, by norm_num⟩
  · exact ⟨5237, 5, prime_5237, prime_5, by norm_num⟩
  · exact ⟨5227, 11, prime_5227, prime_11, by norm_num⟩
  · exact ⟨5237, 7, prime_5237, prime_7, by norm_num⟩
  · exact ⟨5231, 11, prime_5231, prime_11, by norm_num⟩
  · exact ⟨5233, 11, prime_5233, prime_11, by norm_num⟩
  · exact ⟨5231, 13, prime_5231, prime_13, by norm_num⟩
  · exact ⟨5237, 11, prime_5237, prime_11, by norm_num⟩
  · exact ⟨5227, 17, prime_5227, prime_17, by norm_num⟩
  · exact ⟨5237, 13, prime_5237, prime_13, by norm_num⟩
  · exact ⟨5261, 2, prime_5261, prime_2, by norm_num⟩
  · exact ⟨5261, 3, prime_5261, prime_3, by norm_num⟩
  · exact ⟨5231, 19, prime_5231, prime_19, by norm_num⟩
  · exact ⟨5261, 5, prime_5261, prime_5, by norm_num⟩
  · exact ⟨5227, 23, prime_5227, prime_23, by norm_num⟩
  · exact ⟨5261, 7, prime_5261, prime_7, by norm_num⟩
  · exact ⟨5273, 2, prime_5273, prime_2, by norm_num⟩
  · exact ⟨5273, 3, prime_5273, prime_3, by norm_num⟩
  · exact ⟨5147, 67, prime_5147, prime_67, by norm_num⟩
  · exact ⟨5279, 2, prime_5279, prime_2, by norm_num⟩
  · exact ⟨5281, 2, prime_5281, prime_2, by norm_num⟩
  · exact ⟨5281, 3, prime_5281, prime_3, by norm_num⟩
  · exact ⟨5279, 5, prime_5279, prime_5, by norm_num⟩
  · exact ⟨5281, 5, prime_5281, prime_5, by norm_num⟩
  · exact ⟨5279, 7, prime_5279, prime_7, by norm_num⟩
  · exact ⟨5281, 7, prime_5281, prime_7, by norm_num⟩
  · exact ⟨5179, 59, prime_5179, prime_59, by norm_num⟩
  · exact ⟨5273, 13, prime_5273, prime_13, by norm_num⟩
  · exact ⟨5297, 2, prime_5297, prime_2, by norm_num⟩
  · exact ⟨5297, 3, prime_5297, prime_3, by norm_num⟩
  · exact ⟨5279, 13, prime_5279, prime_13, by norm_num⟩
  · exact ⟨5303, 2, prime_5303, prime_2, by norm_num⟩
  · exact ⟨5303, 3, prime_5303, prime_3, by norm_num⟩
  · exact ⟨5297, 7, prime_5297, prime_7, by norm_num⟩
  · exact ⟨5309, 2, prime_5309, prime_2, by norm_num⟩
  · exact ⟨5309, 3, prime_5309, prime_3, by norm_num⟩
  · exact ⟨5303, 7, prime_5303, prime_7, by norm_num⟩
  · exact ⟨5309, 5, prime_5309, prime_5, by norm_num⟩
  · exact ⟨5227, 47, prime_5227, prime_47, by norm_num⟩
  · exact ⟨5309, 7, prime_5309, prime_7, by norm_num⟩
  · exact ⟨5303, 11, prime_5303, prime_11, by norm_num⟩
  · exact ⟨5323, 2, prime_5323, prime_2, by norm_num⟩
  · exact ⟨5323, 3, prime_5323, prime_3, by norm_num⟩
  · exact ⟨5309, 11, prime_5309, prime_11, by norm_num⟩
  · exact ⟨5323, 5, prime_5323, prime_5, by norm_num⟩
  · exact ⟨5309, 13, prime_5309, prime_13, by norm_num⟩
  · exact ⟨5333, 2, prime_5333, prime_2, by norm_num⟩
  · exact ⟨5333, 3, prime_5333, prime_3, by norm_num⟩
  · exact ⟨5303, 19, prime_5303, prime_19, by norm_num⟩
  · exact ⟨5333, 5, prime_5333, prime_5, by norm_num⟩
  · exact ⟨5323, 11, prime_5323, prime_11, by norm_num⟩
  · exact ⟨5333, 7, prime_5333, prime_7, by norm_num⟩
  · exact ⟨5323, 13, prime_5323, prime_13, by norm_num⟩
  · exact ⟨5347, 2, prime_5347, prime_2, by norm_num⟩
  · exact ⟨5347, 3, prime_5347, prime_3, by norm_num⟩
  · exact ⟨5351, 2, prime_5351, prime_2, by norm_num⟩
  · exact ⟨5351, 3, prime_5351, prime_3, by norm_num⟩
  · exact ⟨5333, 13, prime_5333, prime_13, by norm_num⟩
  · exact ⟨5351, 5, prime_5351, prime_5, by norm_num⟩
  · exact ⟨5281, 41, prime_5281, prime_41, by norm_num⟩
  · exact ⟨5351, 7, prime_5351, prime_7, by norm_num⟩
  · exact ⟨5333, 17, prime_5333, prime_17, by norm_num⟩
  · exact ⟨5347, 11, prime_5347, prime_11, by norm_num⟩
  · exact ⟨5333, 19, prime_5333, prime_19, by norm_num⟩
  · exact ⟨5351, 11, prime_5351, prime_11, by norm_num⟩
  · exact ⟨5281, 47, prime_5281, prime_47, by norm_num⟩
  · exact ⟨5351, 13, prime_5351, prime_13, by norm_num⟩
  · exact ⟨5333, 23, prime_5333, prime_23, by norm_num⟩
  · exact ⟨5347, 17, prime_5347, prime_17, by norm_num⟩
  · exact ⟨5309, 37, prime_5309, prime_37, by norm_num⟩
  · exact ⟨5381, 2, prime_5381, prime_2, by norm_num⟩
  · exact ⟨5381, 3, prime_5381, prime_3, by norm_num⟩
  · exact ⟨5351, 19, prime_5351, prime_19, by norm_num⟩
  · exact ⟨5387, 2, prime_5387, prime_2, by norm_num⟩
  · exact ⟨5387, 3, prime_5387, prime_3, by norm_num⟩
  · exact ⟨5381, 7, prime_5381, prime_7, by norm_num⟩
  · exact ⟨5393, 2, prime_5393, prime_2, by norm_num⟩
  · exact ⟨5393, 3, prime_5393, prime_3, by norm_num⟩
  · exact ⟨5387, 7, prime_5387, prime_7, by norm_num⟩
  · exact ⟨5399, 2, prime_5399, prime_2, by norm_num⟩
  · exact ⟨5399, 3, prime_5399, prime_3, by norm_num⟩

private theorem lemoine_chunk_27 : ∀ k : ℕ, 2703 ≤ k → k ≤ 2802 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5393, 7, prime_5393, prime_7, by norm_num⟩
  · exact ⟨5399, 5, prime_5399, prime_5, by norm_num⟩
  · exact ⟨5407, 2, prime_5407, prime_2, by norm_num⟩
  · exact ⟨5407, 3, prime_5407, prime_3, by norm_num⟩
  · exact ⟨5393, 11, prime_5393, prime_11, by norm_num⟩
  · exact ⟨5413, 2, prime_5413, prime_2, by norm_num⟩
  · exact ⟨5413, 3, prime_5413, prime_3, by norm_num⟩
  · exact ⟨5417, 2, prime_5417, prime_2, by norm_num⟩
  · exact ⟨5419, 2, prime_5419, prime_2, by norm_num⟩
  · exact ⟨5419, 3, prime_5419, prime_3, by norm_num⟩
  · exact ⟨5417, 5, prime_5417, prime_5, by norm_num⟩
  · exact ⟨5419, 5, prime_5419, prime_5, by norm_num⟩
  · exact ⟨5417, 7, prime_5417, prime_7, by norm_num⟩
  · exact ⟨5419, 7, prime_5419, prime_7, by norm_num⟩
  · exact ⟨5431, 2, prime_5431, prime_2, by norm_num⟩
  · exact ⟨5431, 3, prime_5431, prime_3, by norm_num⟩
  · exact ⟨5417, 11, prime_5417, prime_11, by norm_num⟩
  · exact ⟨5437, 2, prime_5437, prime_2, by norm_num⟩
  · exact ⟨5437, 3, prime_5437, prime_3, by norm_num⟩
  · exact ⟨5441, 2, prime_5441, prime_2, by norm_num⟩
  · exact ⟨5443, 2, prime_5443, prime_2, by norm_num⟩
  · exact ⟨5443, 3, prime_5443, prime_3, by norm_num⟩
  · exact ⟨5441, 5, prime_5441, prime_5, by norm_num⟩
  · exact ⟨5449, 2, prime_5449, prime_2, by norm_num⟩
  · exact ⟨5449, 3, prime_5449, prime_3, by norm_num⟩
  · exact ⟨5443, 7, prime_5443, prime_7, by norm_num⟩
  · exact ⟨5449, 5, prime_5449, prime_5, by norm_num⟩
  · exact ⟨5399, 31, prime_5399, prime_31, by norm_num⟩
  · exact ⟨5449, 7, prime_5449, prime_7, by norm_num⟩
  · exact ⟨5443, 11, prime_5443, prime_11, by norm_num⟩
  · exact ⟨5441, 13, prime_5441, prime_13, by norm_num⟩
  · exact ⟨5443, 13, prime_5443, prime_13, by norm_num⟩
  · exact ⟨5449, 11, prime_5449, prime_11, by norm_num⟩
  · exact ⟨5399, 37, prime_5399, prime_37, by norm_num⟩
  · exact ⟨5471, 2, prime_5471, prime_2, by norm_num⟩
  · exact ⟨5471, 3, prime_5471, prime_3, by norm_num⟩
  · exact ⟨5441, 19, prime_5441, prime_19, by norm_num⟩
  · exact ⟨5477, 2, prime_5477, prime_2, by norm_num⟩
  · exact ⟨5479, 2, prime_5479, prime_2, by norm_num⟩
  · exact ⟨5479, 3, prime_5479, prime_3, by norm_num⟩
  · exact ⟨5483, 2, prime_5483, prime_2, by norm_num⟩
  · exact ⟨5483, 3, prime_5483, prime_3, by norm_num⟩
  · exact ⟨5477, 7, prime_5477, prime_7, by norm_num⟩
  · exact ⟨5483, 5, prime_5483, prime_5, by norm_num⟩
  · exact ⟨5449, 23, prime_5449, prime_23, by norm_num⟩
  · exact ⟨5483, 7, prime_5483, prime_7, by norm_num⟩
  · exact ⟨5477, 11, prime_5477, prime_11, by norm_num⟩
  · exact ⟨5479, 11, prime_5479, prime_11, by norm_num⟩
  · exact ⟨5477, 13, prime_5477, prime_13, by norm_num⟩
  · exact ⟨5501, 2, prime_5501, prime_2, by norm_num⟩
  · exact ⟨5503, 2, prime_5503, prime_2, by norm_num⟩
  · exact ⟨5503, 3, prime_5503, prime_3, by norm_num⟩
  · exact ⟨5507, 2, prime_5507, prime_2, by norm_num⟩
  · exact ⟨5507, 3, prime_5507, prime_3, by norm_num⟩
  · exact ⟨5501, 7, prime_5501, prime_7, by norm_num⟩
  · exact ⟨5507, 5, prime_5507, prime_5, by norm_num⟩
  · exact ⟨5437, 41, prime_5437, prime_41, by norm_num⟩
  · exact ⟨5507, 7, prime_5507, prime_7, by norm_num⟩
  · exact ⟨5519, 2, prime_5519, prime_2, by norm_num⟩
  · exact ⟨5521, 2, prime_5521, prime_2, by norm_num⟩
  · exact ⟨5521, 3, prime_5521, prime_3, by norm_num⟩
  · exact ⟨5519, 5, prime_5519, prime_5, by norm_num⟩
  · exact ⟨5527, 2, prime_5527, prime_2, by norm_num⟩
  · exact ⟨5527, 3, prime_5527, prime_3, by norm_num⟩
  · exact ⟨5531, 2, prime_5531, prime_2, by norm_num⟩
  · exact ⟨5531, 3, prime_5531, prime_3, by norm_num⟩
  · exact ⟨5501, 19, prime_5501, prime_19, by norm_num⟩
  · exact ⟨5531, 5, prime_5531, prime_5, by norm_num⟩
  · exact ⟨5521, 11, prime_5521, prime_11, by norm_num⟩
  · exact ⟨5531, 7, prime_5531, prime_7, by norm_num⟩
  · exact ⟨5521, 13, prime_5521, prime_13, by norm_num⟩
  · exact ⟨5527, 11, prime_5527, prime_11, by norm_num⟩
  · exact ⟨5477, 37, prime_5477, prime_37, by norm_num⟩
  · exact ⟨5531, 11, prime_5531, prime_11, by norm_num⟩
  · exact ⟨5521, 17, prime_5521, prime_17, by norm_num⟩
  · exact ⟨5531, 13, prime_5531, prime_13, by norm_num⟩
  · exact ⟨5521, 19, prime_5521, prime_19, by norm_num⟩
  · exact ⟨5557, 2, prime_5557, prime_2, by norm_num⟩
  · exact ⟨5557, 3, prime_5557, prime_3, by norm_num⟩
  · exact ⟨5531, 17, prime_5531, prime_17, by norm_num⟩
  · exact ⟨5563, 2, prime_5563, prime_2, by norm_num⟩
  · exact ⟨5563, 3, prime_5563, prime_3, by norm_num⟩
  · exact ⟨5557, 7, prime_5557, prime_7, by norm_num⟩
  · exact ⟨5569, 2, prime_5569, prime_2, by norm_num⟩
  · exact ⟨5569, 3, prime_5569, prime_3, by norm_num⟩
  · exact ⟨5573, 2, prime_5573, prime_2, by norm_num⟩
  · exact ⟨5573, 3, prime_5573, prime_3, by norm_num⟩
  · exact ⟨5519, 31, prime_5519, prime_31, by norm_num⟩
  · exact ⟨5573, 5, prime_5573, prime_5, by norm_num⟩
  · exact ⟨5581, 2, prime_5581, prime_2, by norm_num⟩
  · exact ⟨5581, 3, prime_5581, prime_3, by norm_num⟩
  · exact ⟨5563, 13, prime_5563, prime_13, by norm_num⟩
  · exact ⟨5581, 5, prime_5581, prime_5, by norm_num⟩
  · exact ⟨5531, 31, prime_5531, prime_31, by norm_num⟩
  · exact ⟨5591, 2, prime_5591, prime_2, by norm_num⟩
  · exact ⟨5591, 3, prime_5591, prime_3, by norm_num⟩
  · exact ⟨5573, 13, prime_5573, prime_13, by norm_num⟩
  · exact ⟨5591, 5, prime_5591, prime_5, by norm_num⟩
  · exact ⟨5581, 11, prime_5581, prime_11, by norm_num⟩
  · exact ⟨5591, 7, prime_5591, prime_7, by norm_num⟩

private theorem lemoine_chunk_28 : ∀ k : ℕ, 2803 ≤ k → k ≤ 2902 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5581, 13, prime_5581, prime_13, by norm_num⟩
  · exact ⟨5563, 23, prime_5563, prime_23, by norm_num⟩
  · exact ⟨5573, 19, prime_5573, prime_19, by norm_num⟩
  · exact ⟨5591, 11, prime_5591, prime_11, by norm_num⟩
  · exact ⟨5581, 17, prime_5581, prime_17, by norm_num⟩
  · exact ⟨5591, 13, prime_5591, prime_13, by norm_num⟩
  · exact ⟨5581, 19, prime_5581, prime_19, by norm_num⟩
  · exact ⟨5563, 29, prime_5563, prime_29, by norm_num⟩
  · exact ⟨5501, 61, prime_5501, prime_61, by norm_num⟩
  · exact ⟨5591, 17, prime_5591, prime_17, by norm_num⟩
  · exact ⟨5623, 2, prime_5623, prime_2, by norm_num⟩
  · exact ⟨5623, 3, prime_5623, prime_3, by norm_num⟩
  · exact ⟨5573, 29, prime_5573, prime_29, by norm_num⟩
  · exact ⟨5623, 5, prime_5623, prime_5, by norm_num⟩
  · exact ⟨5573, 31, prime_5573, prime_31, by norm_num⟩
  · exact ⟨5623, 7, prime_5623, prime_7, by norm_num⟩
  · exact ⟨5581, 29, prime_5581, prime_29, by norm_num⟩
  · exact ⟨5519, 61, prime_5519, prime_61, by norm_num⟩
  · exact ⟨5639, 2, prime_5639, prime_2, by norm_num⟩
  · exact ⟨5641, 2, prime_5641, prime_2, by norm_num⟩
  · exact ⟨5641, 3, prime_5641, prime_3, by norm_num⟩
  · exact ⟨5639, 5, prime_5639, prime_5, by norm_num⟩
  · exact ⟨5647, 2, prime_5647, prime_2, by norm_num⟩
  · exact ⟨5647, 3, prime_5647, prime_3, by norm_num⟩
  · exact ⟨5651, 2, prime_5651, prime_2, by norm_num⟩
  · exact ⟨5653, 2, prime_5653, prime_2, by norm_num⟩
  · exact ⟨5653, 3, prime_5653, prime_3, by norm_num⟩
  · exact ⟨5657, 2, prime_5657, prime_2, by norm_num⟩
  · exact ⟨5659, 2, prime_5659, prime_2, by norm_num⟩
  · exact ⟨5659, 3, prime_5659, prime_3, by norm_num⟩
  · exact ⟨5657, 5, prime_5657, prime_5, by norm_num⟩
  · exact ⟨5659, 5, prime_5659, prime_5, by norm_num⟩
  · exact ⟨5657, 7, prime_5657, prime_7, by norm_num⟩
  · exact ⟨5669, 2, prime_5669, prime_2, by norm_num⟩
  · exact ⟨5669, 3, prime_5669, prime_3, by norm_num⟩
  · exact ⟨5651, 13, prime_5651, prime_13, by norm_num⟩
  · exact ⟨5669, 5, prime_5669, prime_5, by norm_num⟩
  · exact ⟨5659, 11, prime_5659, prime_11, by norm_num⟩
  · exact ⟨5669, 7, prime_5669, prime_7, by norm_num⟩
  · exact ⟨5659, 13, prime_5659, prime_13, by norm_num⟩
  · exact ⟨5683, 2, prime_5683, prime_2, by norm_num⟩
  · exact ⟨5683, 3, prime_5683, prime_3, by norm_num⟩
  · exact ⟨5669, 11, prime_5669, prime_11, by norm_num⟩
  · exact ⟨5689, 2, prime_5689, prime_2, by norm_num⟩
  · exact ⟨5689, 3, prime_5689, prime_3, by norm_num⟩
  · exact ⟨5693, 2, prime_5693, prime_2, by norm_num⟩
  · exact ⟨5693, 3, prime_5693, prime_3, by norm_num⟩
  · exact ⟨5639, 31, prime_5639, prime_31, by norm_num⟩
  · exact ⟨5693, 5, prime_5693, prime_5, by norm_num⟩
  · exact ⟨5701, 2, prime_5701, prime_2, by norm_num⟩
  · exact ⟨5701, 3, prime_5701, prime_3, by norm_num⟩
  · exact ⟨5683, 13, prime_5683, prime_13, by norm_num⟩
  · exact ⟨5701, 5, prime_5701, prime_5, by norm_num⟩
  · exact ⟨5651, 31, prime_5651, prime_31, by norm_num⟩
  · exact ⟨5711, 2, prime_5711, prime_2, by norm_num⟩
  · exact ⟨5711, 3, prime_5711, prime_3, by norm_num⟩
  · exact ⟨5693, 13, prime_5693, prime_13, by norm_num⟩
  · exact ⟨5717, 2, prime_5717, prime_2, by norm_num⟩
  · exact ⟨5717, 3, prime_5717, prime_3, by norm_num⟩
  · exact ⟨5711, 7, prime_5711, prime_7, by norm_num⟩
  · exact ⟨5717, 5, prime_5717, prime_5, by norm_num⟩
  · exact ⟨5683, 23, prime_5683, prime_23, by norm_num⟩
  · exact ⟨5717, 7, prime_5717, prime_7, by norm_num⟩
  · exact ⟨5711, 11, prime_5711, prime_11, by norm_num⟩
  · exact ⟨5701, 17, prime_5701, prime_17, by norm_num⟩
  · exact ⟨5711, 13, prime_5711, prime_13, by norm_num⟩
  · exact ⟨5717, 11, prime_5717, prime_11, by norm_num⟩
  · exact ⟨5737, 2, prime_5737, prime_2, by norm_num⟩
  · exact ⟨5737, 3, prime_5737, prime_3, by norm_num⟩
  · exact ⟨5741, 2, prime_5741, prime_2, by norm_num⟩
  · exact ⟨5743, 2, prime_5743, prime_2, by norm_num⟩
  · exact ⟨5743, 3, prime_5743, prime_3, by norm_num⟩
  · exact ⟨5741, 5, prime_5741, prime_5, by norm_num⟩
  · exact ⟨5749, 2, prime_5749, prime_2, by norm_num⟩
  · exact ⟨5749, 3, prime_5749, prime_3, by norm_num⟩
  · exact ⟨5743, 7, prime_5743, prime_7, by norm_num⟩
  · exact ⟨5749, 5, prime_5749, prime_5, by norm_num⟩
  · exact ⟨5639, 61, prime_5639, prime_61, by norm_num⟩
  · exact ⟨5749, 7, prime_5749, prime_7, by norm_num⟩
  · exact ⟨5743, 11, prime_5743, prime_11, by norm_num⟩
  · exact ⟨5741, 13, prime_5741, prime_13, by norm_num⟩
  · exact ⟨5743, 13, prime_5743, prime_13, by norm_num⟩
  · exact ⟨5749, 11, prime_5749, prime_11, by norm_num⟩
  · exact ⟨5711, 31, prime_5711, prime_31, by norm_num⟩
  · exact ⟨5749, 13, prime_5749, prime_13, by norm_num⟩
  · exact ⟨5743, 17, prime_5743, prime_17, by norm_num⟩
  · exact ⟨5741, 19, prime_5741, prime_19, by norm_num⟩
  · exact ⟨5743, 19, prime_5743, prime_19, by norm_num⟩
  · exact ⟨5779, 2, prime_5779, prime_2, by norm_num⟩
  · exact ⟨5779, 3, prime_5779, prime_3, by norm_num⟩
  · exact ⟨5783, 2, prime_5783, prime_2, by norm_num⟩
  · exact ⟨5783, 3, prime_5783, prime_3, by norm_num⟩
  · exact ⟨5717, 37, prime_5717, prime_37, by norm_num⟩
  · exact ⟨5783, 5, prime_5783, prime_5, by norm_num⟩
  · exact ⟨5791, 2, prime_5791, prime_2, by norm_num⟩
  · exact ⟨5791, 3, prime_5791, prime_3, by norm_num⟩
  · exact ⟨5741, 29, prime_5741, prime_29, by norm_num⟩
  · exact ⟨5791, 5, prime_5791, prime_5, by norm_num⟩
  · exact ⟨5741, 31, prime_5741, prime_31, by norm_num⟩
  · exact ⟨5801, 2, prime_5801, prime_2, by norm_num⟩

private theorem lemoine_chunk_29 : ∀ k : ℕ, 2903 ≤ k → k ≤ 3002 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5801, 3, prime_5801, prime_3, by norm_num⟩
  · exact ⟨5783, 13, prime_5783, prime_13, by norm_num⟩
  · exact ⟨5807, 2, prime_5807, prime_2, by norm_num⟩
  · exact ⟨5807, 3, prime_5807, prime_3, by norm_num⟩
  · exact ⟨5801, 7, prime_5801, prime_7, by norm_num⟩
  · exact ⟨5813, 2, prime_5813, prime_2, by norm_num⟩
  · exact ⟨5813, 3, prime_5813, prime_3, by norm_num⟩
  · exact ⟨5807, 7, prime_5807, prime_7, by norm_num⟩
  · exact ⟨5813, 5, prime_5813, prime_5, by norm_num⟩
  · exact ⟨5821, 2, prime_5821, prime_2, by norm_num⟩
  · exact ⟨5821, 3, prime_5821, prime_3, by norm_num⟩
  · exact ⟨5807, 11, prime_5807, prime_11, by norm_num⟩
  · exact ⟨5827, 2, prime_5827, prime_2, by norm_num⟩
  · exact ⟨5827, 3, prime_5827, prime_3, by norm_num⟩
  · exact ⟨5821, 7, prime_5821, prime_7, by norm_num⟩
  · exact ⟨5827, 5, prime_5827, prime_5, by norm_num⟩
  · exact ⟨5813, 13, prime_5813, prime_13, by norm_num⟩
  · exact ⟨5827, 7, prime_5827, prime_7, by norm_num⟩
  · exact ⟨5839, 2, prime_5839, prime_2, by norm_num⟩
  · exact ⟨5839, 3, prime_5839, prime_3, by norm_num⟩
  · exact ⟨5843, 2, prime_5843, prime_2, by norm_num⟩
  · exact ⟨5843, 3, prime_5843, prime_3, by norm_num⟩
  · exact ⟨5813, 19, prime_5813, prime_19, by norm_num⟩
  · exact ⟨5849, 2, prime_5849, prime_2, by norm_num⟩
  · exact ⟨5851, 2, prime_5851, prime_2, by norm_num⟩
  · exact ⟨5851, 3, prime_5851, prime_3, by norm_num⟩
  · exact ⟨5849, 5, prime_5849, prime_5, by norm_num⟩
  · exact ⟨5857, 2, prime_5857, prime_2, by norm_num⟩
  · exact ⟨5857, 3, prime_5857, prime_3, by norm_num⟩
  · exact ⟨5861, 2, prime_5861, prime_2, by norm_num⟩
  · exact ⟨5861, 3, prime_5861, prime_3, by norm_num⟩
  · exact ⟨5843, 13, prime_5843, prime_13, by norm_num⟩
  · exact ⟨5867, 2, prime_5867, prime_2, by norm_num⟩
  · exact ⟨5869, 2, prime_5869, prime_2, by norm_num⟩
  · exact ⟨5869, 3, prime_5869, prime_3, by norm_num⟩
  · exact ⟨5867, 5, prime_5867, prime_5, by norm_num⟩
  · exact ⟨5869, 5, prime_5869, prime_5, by norm_num⟩
  · exact ⟨5867, 7, prime_5867, prime_7, by norm_num⟩
  · exact ⟨5879, 2, prime_5879, prime_2, by norm_num⟩
  · exact ⟨5881, 2, prime_5881, prime_2, by norm_num⟩
  · exact ⟨5881, 3, prime_5881, prime_3, by norm_num⟩
  · exact ⟨5879, 5, prime_5879, prime_5, by norm_num⟩
  · exact ⟨5881, 5, prime_5881, prime_5, by norm_num⟩
  · exact ⟨5879, 7, prime_5879, prime_7, by norm_num⟩
  · exact ⟨5881, 7, prime_5881, prime_7, by norm_num⟩
  · exact ⟨5851, 23, prime_5851, prime_23, by norm_num⟩
  · exact ⟨5861, 19, prime_5861, prime_19, by norm_num⟩
  · exact ⟨5897, 2, prime_5897, prime_2, by norm_num⟩
  · exact ⟨5897, 3, prime_5897, prime_3, by norm_num⟩
  · exact ⟨5879, 13, prime_5879, prime_13, by norm_num⟩
  · exact ⟨5903, 2, prime_5903, prime_2, by norm_num⟩
  · exact ⟨5903, 3, prime_5903, prime_3, by norm_num⟩
  · exact ⟨5897, 7, prime_5897, prime_7, by norm_num⟩
  · exact ⟨5903, 5, prime_5903, prime_5, by norm_num⟩
  · exact ⟨5881, 17, prime_5881, prime_17, by norm_num⟩
  · exact ⟨5903, 7, prime_5903, prime_7, by norm_num⟩
  · exact ⟨5897, 11, prime_5897, prime_11, by norm_num⟩
  · exact ⟨5839, 41, prime_5839, prime_41, by norm_num⟩
  · exact ⟨5897, 13, prime_5897, prime_13, by norm_num⟩
  · exact ⟨5903, 11, prime_5903, prime_11, by norm_num⟩
  · exact ⟨5923, 2, prime_5923, prime_2, by norm_num⟩
  · exact ⟨5923, 3, prime_5923, prime_3, by norm_num⟩
  · exact ⟨5927, 2, prime_5927, prime_2, by norm_num⟩
  · exact ⟨5927, 3, prime_5927, prime_3, by norm_num⟩
  · exact ⟨5897, 19, prime_5897, prime_19, by norm_num⟩
  · exact ⟨5927, 5, prime_5927, prime_5, by norm_num⟩
  · exact ⟨5881, 29, prime_5881, prime_29, by norm_num⟩
  · exact ⟨5927, 7, prime_5927, prime_7, by norm_num⟩
  · exact ⟨5939, 2, prime_5939, prime_2, by norm_num⟩
  · exact ⟨5939, 3, prime_5939, prime_3, by norm_num⟩
  · exact ⟨5861, 43, prime_5861, prime_43, by norm_num⟩
  · exact ⟨5939, 5, prime_5939, prime_5, by norm_num⟩
  · exact ⟨5869, 41, prime_5869, prime_41, by norm_num⟩
  · exact ⟨5939, 7, prime_5939, prime_7, by norm_num⟩
  · exact ⟨5897, 29, prime_5897, prime_29, by norm_num⟩
  · exact ⟨5953, 2, prime_5953, prime_2, by norm_num⟩
  · exact ⟨5953, 3, prime_5953, prime_3, by norm_num⟩
  · exact ⟨5939, 11, prime_5939, prime_11, by norm_num⟩
  · exact ⟨5953, 5, prime_5953, prime_5, by norm_num⟩
  · exact ⟨5939, 13, prime_5939, prime_13, by norm_num⟩
  · exact ⟨5953, 7, prime_5953, prime_7, by norm_num⟩
  · exact ⟨5923, 23, prime_5923, prime_23, by norm_num⟩
  · exact ⟨5897, 37, prime_5897, prime_37, by norm_num⟩
  · exact ⟨5939, 17, prime_5939, prime_17, by norm_num⟩
  · exact ⟨5953, 11, prime_5953, prime_11, by norm_num⟩
  · exact ⟨5939, 19, prime_5939, prime_19, by norm_num⟩
  · exact ⟨5953, 13, prime_5953, prime_13, by norm_num⟩
  · exact ⟨5923, 29, prime_5923, prime_29, by norm_num⟩
  · exact ⟨5897, 43, prime_5897, prime_43, by norm_num⟩
  · exact ⟨5981, 2, prime_5981, prime_2, by norm_num⟩
  · exact ⟨5981, 3, prime_5981, prime_3, by norm_num⟩
  · exact ⟨5927, 31, prime_5927, prime_31, by norm_num⟩
  · exact ⟨5987, 2, prime_5987, prime_2, by norm_num⟩
  · exact ⟨5987, 3, prime_5987, prime_3, by norm_num⟩
  · exact ⟨5981, 7, prime_5981, prime_7, by norm_num⟩
  · exact ⟨5987, 5, prime_5987, prime_5, by norm_num⟩
  · exact ⟨5953, 23, prime_5953, prime_23, by norm_num⟩
  · exact ⟨5987, 7, prime_5987, prime_7, by norm_num⟩
  · exact ⟨5981, 11, prime_5981, prime_11, by norm_num⟩
  · exact ⟨5923, 41, prime_5923, prime_41, by norm_num⟩

private theorem lemoine_chunk_30 : ∀ k : ℕ, 3003 ≤ k → k ≤ 3102 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨5981, 13, prime_5981, prime_13, by norm_num⟩
  · exact ⟨5987, 11, prime_5987, prime_11, by norm_num⟩
  · exact ⟨6007, 2, prime_6007, prime_2, by norm_num⟩
  · exact ⟨6007, 3, prime_6007, prime_3, by norm_num⟩
  · exact ⟨6011, 2, prime_6011, prime_2, by norm_num⟩
  · exact ⟨6011, 3, prime_6011, prime_3, by norm_num⟩
  · exact ⟨5981, 19, prime_5981, prime_19, by norm_num⟩
  · exact ⟨6011, 5, prime_6011, prime_5, by norm_num⟩
  · exact ⟨5881, 71, prime_5881, prime_71, by norm_num⟩
  · exact ⟨6011, 7, prime_6011, prime_7, by norm_num⟩
  · exact ⟨5981, 23, prime_5981, prime_23, by norm_num⟩
  · exact ⟨6007, 11, prime_6007, prime_11, by norm_num⟩
  · exact ⟨5897, 67, prime_5897, prime_67, by norm_num⟩
  · exact ⟨6029, 2, prime_6029, prime_2, by norm_num⟩
  · exact ⟨6029, 3, prime_6029, prime_3, by norm_num⟩
  · exact ⟨6011, 13, prime_6011, prime_13, by norm_num⟩
  · exact ⟨6029, 5, prime_6029, prime_5, by norm_num⟩
  · exact ⟨6037, 2, prime_6037, prime_2, by norm_num⟩
  · exact ⟨6037, 3, prime_6037, prime_3, by norm_num⟩
  · exact ⟨6011, 17, prime_6011, prime_17, by norm_num⟩
  · exact ⟨6043, 2, prime_6043, prime_2, by norm_num⟩
  · exact ⟨6043, 3, prime_6043, prime_3, by norm_num⟩
  · exact ⟨6047, 2, prime_6047, prime_2, by norm_num⟩
  · exact ⟨6047, 3, prime_6047, prime_3, by norm_num⟩
  · exact ⟨6029, 13, prime_6029, prime_13, by norm_num⟩
  · exact ⟨6053, 2, prime_6053, prime_2, by norm_num⟩
  · exact ⟨6053, 3, prime_6053, prime_3, by norm_num⟩
  · exact ⟨6047, 7, prime_6047, prime_7, by norm_num⟩
  · exact ⟨6053, 5, prime_6053, prime_5, by norm_num⟩
  · exact ⟨6043, 11, prime_6043, prime_11, by norm_num⟩
  · exact ⟨6053, 7, prime_6053, prime_7, by norm_num⟩
  · exact ⟨6047, 11, prime_6047, prime_11, by norm_num⟩
  · exact ⟨6067, 2, prime_6067, prime_2, by norm_num⟩
  · exact ⟨6067, 3, prime_6067, prime_3, by norm_num⟩
  · exact ⟨6053, 11, prime_6053, prime_11, by norm_num⟩
  · exact ⟨6073, 2, prime_6073, prime_2, by norm_num⟩
  · exact ⟨6073, 3, prime_6073, prime_3, by norm_num⟩
  · exact ⟨6067, 7, prime_6067, prime_7, by norm_num⟩
  · exact ⟨6079, 2, prime_6079, prime_2, by norm_num⟩
  · exact ⟨6079, 3, prime_6079, prime_3, by norm_num⟩
  · exact ⟨6073, 7, prime_6073, prime_7, by norm_num⟩
  · exact ⟨6079, 5, prime_6079, prime_5, by norm_num⟩
  · exact ⟨6053, 19, prime_6053, prime_19, by norm_num⟩
  · exact ⟨6089, 2, prime_6089, prime_2, by norm_num⟩
  · exact ⟨6091, 2, prime_6091, prime_2, by norm_num⟩
  · exact ⟨6091, 3, prime_6091, prime_3, by norm_num⟩
  · exact ⟨6089, 5, prime_6089, prime_5, by norm_num⟩
  · exact ⟨6091, 5, prime_6091, prime_5, by norm_num⟩
  · exact ⟨6089, 7, prime_6089, prime_7, by norm_num⟩
  · exact ⟨6101, 2, prime_6101, prime_2, by norm_num⟩
  · exact ⟨6101, 3, prime_6101, prime_3, by norm_num⟩
  · exact ⟨6047, 31, prime_6047, prime_31, by norm_num⟩
  · exact ⟨6101, 5, prime_6101, prime_5, by norm_num⟩
  · exact ⟨6091, 11, prime_6091, prime_11, by norm_num⟩
  · exact ⟨6101, 7, prime_6101, prime_7, by norm_num⟩
  · exact ⟨6113, 2, prime_6113, prime_2, by norm_num⟩
  · exact ⟨6113, 3, prime_6113, prime_3, by norm_num⟩
  · exact ⟨6047, 37, prime_6047, prime_37, by norm_num⟩
  · exact ⟨6113, 5, prime_6113, prime_5, by norm_num⟩
  · exact ⟨6121, 2, prime_6121, prime_2, by norm_num⟩
  · exact ⟨6121, 3, prime_6121, prime_3, by norm_num⟩
  · exact ⟨6091, 19, prime_6091, prime_19, by norm_num⟩
  · exact ⟨6121, 5, prime_6121, prime_5, by norm_num⟩
  · exact ⟨6047, 43, prime_6047, prime_43, by norm_num⟩
  · exact ⟨6131, 2, prime_6131, prime_2, by norm_num⟩
  · exact ⟨6133, 2, prime_6133, prime_2, by norm_num⟩
  · exact ⟨6133, 3, prime_6133, prime_3, by norm_num⟩
  · exact ⟨6131, 5, prime_6131, prime_5, by norm_num⟩
  · exact ⟨6133, 5, prime_6133, prime_5, by norm_num⟩
  · exact ⟨6131, 7, prime_6131, prime_7, by norm_num⟩
  · exact ⟨6143, 2, prime_6143, prime_2, by norm_num⟩
  · exact ⟨6143, 3, prime_6143, prime_3, by norm_num⟩
  · exact ⟨6113, 19, prime_6113, prime_19, by norm_num⟩
  · exact ⟨6143, 5, prime_6143, prime_5, by norm_num⟩
  · exact ⟨6151, 2, prime_6151, prime_2, by norm_num⟩
  · exact ⟨6151, 3, prime_6151, prime_3, by norm_num⟩
  · exact ⟨6133, 13, prime_6133, prime_13, by norm_num⟩
  · exact ⟨6151, 5, prime_6151, prime_5, by norm_num⟩
  · exact ⟨6101, 31, prime_6101, prime_31, by norm_num⟩
  · exact ⟨6151, 7, prime_6151, prime_7, by norm_num⟩
  · exact ⟨6163, 2, prime_6163, prime_2, by norm_num⟩
  · exact ⟨6163, 3, prime_6163, prime_3, by norm_num⟩
  · exact ⟨6133, 19, prime_6133, prime_19, by norm_num⟩
  · exact ⟨6163, 5, prime_6163, prime_5, by norm_num⟩
  · exact ⟨6113, 31, prime_6113, prime_31, by norm_num⟩
  · exact ⟨6173, 2, prime_6173, prime_2, by norm_num⟩
  · exact ⟨6173, 3, prime_6173, prime_3, by norm_num⟩
  · exact ⟨6143, 19, prime_6143, prime_19, by norm_num⟩
  · exact ⟨6173, 5, prime_6173, prime_5, by norm_num⟩
  · exact ⟨6163, 11, prime_6163, prime_11, by norm_num⟩
  · exact ⟨6173, 7, prime_6173, prime_7, by norm_num⟩
  · exact ⟨6163, 13, prime_6163, prime_13, by norm_num⟩
  · exact ⟨6133, 29, prime_6133, prime_29, by norm_num⟩
  · exact ⟨6131, 31, prime_6131, prime_31, by norm_num⟩
  · exact ⟨6173, 11, prime_6173, prime_11, by norm_num⟩
  · exact ⟨6163, 17, prime_6163, prime_17, by norm_num⟩
  · exact ⟨6173, 13, prime_6173, prime_13, by norm_num⟩
  · exact ⟨6197, 2, prime_6197, prime_2, by norm_num⟩
  · exact ⟨6199, 2, prime_6199, prime_2, by norm_num⟩
  · exact ⟨6199, 3, prime_6199, prime_3, by norm_num⟩

private theorem lemoine_chunk_31 : ∀ k : ℕ, 3103 ≤ k → k ≤ 3202 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨6203, 2, prime_6203, prime_2, by norm_num⟩
  · exact ⟨6203, 3, prime_6203, prime_3, by norm_num⟩
  · exact ⟨6197, 7, prime_6197, prime_7, by norm_num⟩
  · exact ⟨6203, 5, prime_6203, prime_5, by norm_num⟩
  · exact ⟨6211, 2, prime_6211, prime_2, by norm_num⟩
  · exact ⟨6211, 3, prime_6211, prime_3, by norm_num⟩
  · exact ⟨6197, 11, prime_6197, prime_11, by norm_num⟩
  · exact ⟨6217, 2, prime_6217, prime_2, by norm_num⟩
  · exact ⟨6217, 3, prime_6217, prime_3, by norm_num⟩
  · exact ⟨6221, 2, prime_6221, prime_2, by norm_num⟩
  · exact ⟨6221, 3, prime_6221, prime_3, by norm_num⟩
  · exact ⟨6203, 13, prime_6203, prime_13, by norm_num⟩
  · exact ⟨6221, 5, prime_6221, prime_5, by norm_num⟩
  · exact ⟨6229, 2, prime_6229, prime_2, by norm_num⟩
  · exact ⟨6229, 3, prime_6229, prime_3, by norm_num⟩
  · exact ⟨6211, 13, prime_6211, prime_13, by norm_num⟩
  · exact ⟨6229, 5, prime_6229, prime_5, by norm_num⟩
  · exact ⟨6203, 19, prime_6203, prime_19, by norm_num⟩
  · exact ⟨6229, 7, prime_6229, prime_7, by norm_num⟩
  · exact ⟨6211, 17, prime_6211, prime_17, by norm_num⟩
  · exact ⟨6221, 13, prime_6221, prime_13, by norm_num⟩
  · exact ⟨6211, 19, prime_6211, prime_19, by norm_num⟩
  · exact ⟨6247, 2, prime_6247, prime_2, by norm_num⟩
  · exact ⟨6247, 3, prime_6247, prime_3, by norm_num⟩
  · exact ⟨6229, 13, prime_6229, prime_13, by norm_num⟩
  · exact ⟨6247, 5, prime_6247, prime_5, by norm_num⟩
  · exact ⟨6221, 19, prime_6221, prime_19, by norm_num⟩
  · exact ⟨6257, 2, prime_6257, prime_2, by norm_num⟩
  · exact ⟨6257, 3, prime_6257, prime_3, by norm_num⟩
  · exact ⟨6203, 31, prime_6203, prime_31, by norm_num⟩
  · exact ⟨6263, 2, prime_6263, prime_2, by norm_num⟩
  · exact ⟨6263, 3, prime_6263, prime_3, by norm_num⟩
  · exact ⟨6257, 7, prime_6257, prime_7, by norm_num⟩
  · exact ⟨6269, 2, prime_6269, prime_2, by norm_num⟩
  · exact ⟨6271, 2, prime_6271, prime_2, by norm_num⟩
  · exact ⟨6271, 3, prime_6271, prime_3, by norm_num⟩
  · exact ⟨6269, 5, prime_6269, prime_5, by norm_num⟩
  · exact ⟨6277, 2, prime_6277, prime_2, by norm_num⟩
  · exact ⟨6277, 3, prime_6277, prime_3, by norm_num⟩
  · exact ⟨6271, 7, prime_6271, prime_7, by norm_num⟩
  · exact ⟨6277, 5, prime_6277, prime_5, by norm_num⟩
  · exact ⟨6263, 13, prime_6263, prime_13, by norm_num⟩
  · exact ⟨6287, 2, prime_6287, prime_2, by norm_num⟩
  · exact ⟨6287, 3, prime_6287, prime_3, by norm_num⟩
  · exact ⟨6269, 13, prime_6269, prime_13, by norm_num⟩
  · exact ⟨6287, 5, prime_6287, prime_5, by norm_num⟩
  · exact ⟨6277, 11, prime_6277, prime_11, by norm_num⟩
  · exact ⟨6287, 7, prime_6287, prime_7, by norm_num⟩
  · exact ⟨6299, 2, prime_6299, prime_2, by norm_num⟩
  · exact ⟨6301, 2, prime_6301, prime_2, by norm_num⟩
  · exact ⟨6301, 3, prime_6301, prime_3, by norm_num⟩
  · exact ⟨6299, 5, prime_6299, prime_5, by norm_num⟩
  · exact ⟨6301, 5, prime_6301, prime_5, by norm_num⟩
  · exact ⟨6299, 7, prime_6299, prime_7, by norm_num⟩
  · exact ⟨6311, 2, prime_6311, prime_2, by norm_num⟩
  · exact ⟨6311, 3, prime_6311, prime_3, by norm_num⟩
  · exact ⟨6257, 31, prime_6257, prime_31, by norm_num⟩
  · exact ⟨6317, 2, prime_6317, prime_2, by norm_num⟩
  · exact ⟨6317, 3, prime_6317, prime_3, by norm_num⟩
  · exact ⟨6311, 7, prime_6311, prime_7, by norm_num⟩
  · exact ⟨6323, 2, prime_6323, prime_2, by norm_num⟩
  · exact ⟨6323, 3, prime_6323, prime_3, by norm_num⟩
  · exact ⟨6317, 7, prime_6317, prime_7, by norm_num⟩
  · exact ⟨6329, 2, prime_6329, prime_2, by norm_num⟩
  · exact ⟨6329, 3, prime_6329, prime_3, by norm_num⟩
  · exact ⟨6323, 7, prime_6323, prime_7, by norm_num⟩
  · exact ⟨6329, 5, prime_6329, prime_5, by norm_num⟩
  · exact ⟨6337, 2, prime_6337, prime_2, by norm_num⟩
  · exact ⟨6337, 3, prime_6337, prime_3, by norm_num⟩
  · exact ⟨6323, 11, prime_6323, prime_11, by norm_num⟩
  · exact ⟨6343, 2, prime_6343, prime_2, by norm_num⟩
  · exact ⟨6343, 3, prime_6343, prime_3, by norm_num⟩
  · exact ⟨6337, 7, prime_6337, prime_7, by norm_num⟩
  · exact ⟨6343, 5, prime_6343, prime_5, by norm_num⟩
  · exact ⟨6329, 13, prime_6329, prime_13, by norm_num⟩
  · exact ⟨6353, 2, prime_6353, prime_2, by norm_num⟩
  · exact ⟨6353, 3, prime_6353, prime_3, by norm_num⟩
  · exact ⟨6323, 19, prime_6323, prime_19, by norm_num⟩
  · exact ⟨6359, 2, prime_6359, prime_2, by norm_num⟩
  · exact ⟨6361, 2, prime_6361, prime_2, by norm_num⟩
  · exact ⟨6361, 3, prime_6361, prime_3, by norm_num⟩
  · exact ⟨6359, 5, prime_6359, prime_5, by norm_num⟩
  · exact ⟨6367, 2, prime_6367, prime_2, by norm_num⟩
  · exact ⟨6367, 3, prime_6367, prime_3, by norm_num⟩
  · exact ⟨6361, 7, prime_6361, prime_7, by norm_num⟩
  · exact ⟨6373, 2, prime_6373, prime_2, by norm_num⟩
  · exact ⟨6373, 3, prime_6373, prime_3, by norm_num⟩
  · exact ⟨6367, 7, prime_6367, prime_7, by norm_num⟩
  · exact ⟨6379, 2, prime_6379, prime_2, by norm_num⟩
  · exact ⟨6379, 3, prime_6379, prime_3, by norm_num⟩
  · exact ⟨6373, 7, prime_6373, prime_7, by norm_num⟩
  · exact ⟨6379, 5, prime_6379, prime_5, by norm_num⟩
  · exact ⟨6353, 19, prime_6353, prime_19, by norm_num⟩
  · exact ⟨6389, 2, prime_6389, prime_2, by norm_num⟩
  · exact ⟨6389, 3, prime_6389, prime_3, by norm_num⟩
  · exact ⟨6359, 19, prime_6359, prime_19, by norm_num⟩
  · exact ⟨6389, 5, prime_6389, prime_5, by norm_num⟩
  · exact ⟨6397, 2, prime_6397, prime_2, by norm_num⟩
  · exact ⟨6397, 3, prime_6397, prime_3, by norm_num⟩
  · exact ⟨6379, 13, prime_6379, prime_13, by norm_num⟩

private theorem lemoine_chunk_32 : ∀ k : ℕ, 3203 ≤ k → k ≤ 3302 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨6397, 5, prime_6397, prime_5, by norm_num⟩
  · exact ⟨6323, 43, prime_6323, prime_43, by norm_num⟩
  · exact ⟨6397, 7, prime_6397, prime_7, by norm_num⟩
  · exact ⟨6379, 17, prime_6379, prime_17, by norm_num⟩
  · exact ⟨6389, 13, prime_6389, prime_13, by norm_num⟩
  · exact ⟨6379, 19, prime_6379, prime_19, by norm_num⟩
  · exact ⟨6397, 11, prime_6397, prime_11, by norm_num⟩
  · exact ⟨6359, 31, prime_6359, prime_31, by norm_num⟩
  · exact ⟨6397, 13, prime_6397, prime_13, by norm_num⟩
  · exact ⟨6421, 2, prime_6421, prime_2, by norm_num⟩
  · exact ⟨6421, 3, prime_6421, prime_3, by norm_num⟩
  · exact ⟨6367, 31, prime_6367, prime_31, by norm_num⟩
  · exact ⟨6427, 2, prime_6427, prime_2, by norm_num⟩
  · exact ⟨6427, 3, prime_6427, prime_3, by norm_num⟩
  · exact ⟨6421, 7, prime_6421, prime_7, by norm_num⟩
  · exact ⟨6427, 5, prime_6427, prime_5, by norm_num⟩
  · exact ⟨6353, 43, prime_6353, prime_43, by norm_num⟩
  · exact ⟨6427, 7, prime_6427, prime_7, by norm_num⟩
  · exact ⟨6421, 11, prime_6421, prime_11, by norm_num⟩
  · exact ⟨6359, 43, prime_6359, prime_43, by norm_num⟩
  · exact ⟨6421, 13, prime_6421, prime_13, by norm_num⟩
  · exact ⟨6427, 11, prime_6427, prime_11, by norm_num⟩
  · exact ⟨6389, 31, prime_6389, prime_31, by norm_num⟩
  · exact ⟨6449, 2, prime_6449, prime_2, by norm_num⟩
  · exact ⟨6451, 2, prime_6451, prime_2, by norm_num⟩
  · exact ⟨6451, 3, prime_6451, prime_3, by norm_num⟩
  · exact ⟨6449, 5, prime_6449, prime_5, by norm_num⟩
  · exact ⟨6451, 5, prime_6451, prime_5, by norm_num⟩
  · exact ⟨6449, 7, prime_6449, prime_7, by norm_num⟩
  · exact ⟨6451, 7, prime_6451, prime_7, by norm_num⟩
  · exact ⟨6421, 23, prime_6421, prime_23, by norm_num⟩
  · exact ⟨6323, 73, prime_6323, prime_73, by norm_num⟩
  · exact ⟨6449, 11, prime_6449, prime_11, by norm_num⟩
  · exact ⟨6469, 2, prime_6469, prime_2, by norm_num⟩
  · exact ⟨6469, 3, prime_6469, prime_3, by norm_num⟩
  · exact ⟨6473, 2, prime_6473, prime_2, by norm_num⟩
  · exact ⟨6473, 3, prime_6473, prime_3, by norm_num⟩
  · exact ⟨6359, 61, prime_6359, prime_61, by norm_num⟩
  · exact ⟨6473, 5, prime_6473, prime_5, by norm_num⟩
  · exact ⟨6481, 2, prime_6481, prime_2, by norm_num⟩
  · exact ⟨6481, 3, prime_6481, prime_3, by norm_num⟩
  · exact ⟨6451, 19, prime_6451, prime_19, by norm_num⟩
  · exact ⟨6481, 5, prime_6481, prime_5, by norm_num⟩
  · exact ⟨6359, 67, prime_6359, prime_67, by norm_num⟩
  · exact ⟨6491, 2, prime_6491, prime_2, by norm_num⟩
  · exact ⟨6491, 3, prime_6491, prime_3, by norm_num⟩
  · exact ⟨6473, 13, prime_6473, prime_13, by norm_num⟩
  · exact ⟨6491, 5, prime_6491, prime_5, by norm_num⟩
  · exact ⟨6481, 11, prime_6481, prime_11, by norm_num⟩
  · exact ⟨6491, 7, prime_6491, prime_7, by norm_num⟩
  · exact ⟨6481, 13, prime_6481, prime_13, by norm_num⟩
  · exact ⟨6451, 29, prime_6451, prime_29, by norm_num⟩
  · exact ⟨6473, 19, prime_6473, prime_19, by norm_num⟩
  · exact ⟨6491, 11, prime_6491, prime_11, by norm_num⟩
  · exact ⟨6481, 17, prime_6481, prime_17, by norm_num⟩
  · exact ⟨6491, 13, prime_6491, prime_13, by norm_num⟩
  · exact ⟨6481, 19, prime_6481, prime_19, by norm_num⟩
  · exact ⟨6427, 47, prime_6427, prime_47, by norm_num⟩
  · exact ⟨6449, 37, prime_6449, prime_37, by norm_num⟩
  · exact ⟨6521, 2, prime_6521, prime_2, by norm_num⟩
  · exact ⟨6521, 3, prime_6521, prime_3, by norm_num⟩
  · exact ⟨6491, 19, prime_6491, prime_19, by norm_num⟩
  · exact ⟨6521, 5, prime_6521, prime_5, by norm_num⟩
  · exact ⟨6529, 2, prime_6529, prime_2, by norm_num⟩
  · exact ⟨6529, 3, prime_6529, prime_3, by norm_num⟩
  · exact ⟨6491, 23, prime_6491, prime_23, by norm_num⟩
  · exact ⟨6529, 5, prime_6529, prime_5, by norm_num⟩
  · exact ⟨6323, 109, prime_6323, prime_109, by norm_num⟩
  · exact ⟨6529, 7, prime_6529, prime_7, by norm_num⟩
  · exact ⟨6451, 47, prime_6451, prime_47, by norm_num⟩
  · exact ⟨6521, 13, prime_6521, prime_13, by norm_num⟩
  · exact ⟨6491, 29, prime_6491, prime_29, by norm_num⟩
  · exact ⟨6547, 2, prime_6547, prime_2, by norm_num⟩
  · exact ⟨6547, 3, prime_6547, prime_3, by norm_num⟩
  · exact ⟨6551, 2, prime_6551, prime_2, by norm_num⟩
  · exact ⟨6553, 2, prime_6553, prime_2, by norm_num⟩
  · exact ⟨6553, 3, prime_6553, prime_3, by norm_num⟩
  · exact ⟨6551, 5, prime_6551, prime_5, by norm_num⟩
  · exact ⟨6553, 5, prime_6553, prime_5, by norm_num⟩
  · exact ⟨6551, 7, prime_6551, prime_7, by norm_num⟩
  · exact ⟨6563, 2, prime_6563, prime_2, by norm_num⟩
  · exact ⟨6563, 3, prime_6563, prime_3, by norm_num⟩
  · exact ⟨6449, 61, prime_6449, prime_61, by norm_num⟩
  · exact ⟨6569, 2, prime_6569, prime_2, by norm_num⟩
  · exact ⟨6571, 2, prime_6571, prime_2, by norm_num⟩
  · exact ⟨6571, 3, prime_6571, prime_3, by norm_num⟩
  · exact ⟨6569, 5, prime_6569, prime_5, by norm_num⟩
  · exact ⟨6577, 2, prime_6577, prime_2, by norm_num⟩
  · exact ⟨6577, 3, prime_6577, prime_3, by norm_num⟩
  · exact ⟨6581, 2, prime_6581, prime_2, by norm_num⟩
  · exact ⟨6581, 3, prime_6581, prime_3, by norm_num⟩
  · exact ⟨6563, 13, prime_6563, prime_13, by norm_num⟩
  · exact ⟨6581, 5, prime_6581, prime_5, by norm_num⟩
  · exact ⟨6571, 11, prime_6571, prime_11, by norm_num⟩
  · exact ⟨6581, 7, prime_6581, prime_7, by norm_num⟩
  · exact ⟨6571, 13, prime_6571, prime_13, by norm_num⟩
  · exact ⟨6577, 11, prime_6577, prime_11, by norm_num⟩
  · exact ⟨6563, 19, prime_6563, prime_19, by norm_num⟩
  · exact ⟨6599, 2, prime_6599, prime_2, by norm_num⟩
  · exact ⟨6599, 3, prime_6599, prime_3, by norm_num⟩

private theorem lemoine_chunk_33 : ∀ k : ℕ, 3303 ≤ k → k ≤ 3402 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨6581, 13, prime_6581, prime_13, by norm_num⟩
  · exact ⟨6599, 5, prime_6599, prime_5, by norm_num⟩
  · exact ⟨6607, 2, prime_6607, prime_2, by norm_num⟩
  · exact ⟨6607, 3, prime_6607, prime_3, by norm_num⟩
  · exact ⟨6581, 17, prime_6581, prime_17, by norm_num⟩
  · exact ⟨6607, 5, prime_6607, prime_5, by norm_num⟩
  · exact ⟨6581, 19, prime_6581, prime_19, by norm_num⟩
  · exact ⟨6607, 7, prime_6607, prime_7, by norm_num⟩
  · exact ⟨6619, 2, prime_6619, prime_2, by norm_num⟩
  · exact ⟨6619, 3, prime_6619, prime_3, by norm_num⟩
  · exact ⟨6581, 23, prime_6581, prime_23, by norm_num⟩
  · exact ⟨6619, 5, prime_6619, prime_5, by norm_num⟩
  · exact ⟨6569, 31, prime_6569, prime_31, by norm_num⟩
  · exact ⟨6619, 7, prime_6619, prime_7, by norm_num⟩
  · exact ⟨6577, 29, prime_6577, prime_29, by norm_num⟩
  · exact ⟨6599, 19, prime_6599, prime_19, by norm_num⟩
  · exact ⟨6581, 29, prime_6581, prime_29, by norm_num⟩
  · exact ⟨6637, 2, prime_6637, prime_2, by norm_num⟩
  · exact ⟨6637, 3, prime_6637, prime_3, by norm_num⟩
  · exact ⟨6619, 13, prime_6619, prime_13, by norm_num⟩
  · exact ⟨6637, 5, prime_6637, prime_5, by norm_num⟩
  · exact ⟨6563, 43, prime_6563, prime_43, by norm_num⟩
  · exact ⟨6637, 7, prime_6637, prime_7, by norm_num⟩
  · exact ⟨6619, 17, prime_6619, prime_17, by norm_num⟩
  · exact ⟨6581, 37, prime_6581, prime_37, by norm_num⟩
  · exact ⟨6653, 2, prime_6653, prime_2, by norm_num⟩
  · exact ⟨6653, 3, prime_6653, prime_3, by norm_num⟩
  · exact ⟨6599, 31, prime_6599, prime_31, by norm_num⟩
  · exact ⟨6659, 2, prime_6659, prime_2, by norm_num⟩
  · exact ⟨6661, 2, prime_6661, prime_2, by norm_num⟩
  · exact ⟨6661, 3, prime_6661, prime_3, by norm_num⟩
  · exact ⟨6659, 5, prime_6659, prime_5, by norm_num⟩
  · exact ⟨6661, 5, prime_6661, prime_5, by norm_num⟩
  · exact ⟨6659, 7, prime_6659, prime_7, by norm_num⟩
  · exact ⟨6661, 7, prime_6661, prime_7, by norm_num⟩
  · exact ⟨6673, 2, prime_6673, prime_2, by norm_num⟩
  · exact ⟨6673, 3, prime_6673, prime_3, by norm_num⟩
  · exact ⟨6659, 11, prime_6659, prime_11, by norm_num⟩
  · exact ⟨6679, 2, prime_6679, prime_2, by norm_num⟩
  · exact ⟨6679, 3, prime_6679, prime_3, by norm_num⟩
  · exact ⟨6673, 7, prime_6673, prime_7, by norm_num⟩
  · exact ⟨6679, 5, prime_6679, prime_5, by norm_num⟩
  · exact ⟨6653, 19, prime_6653, prime_19, by norm_num⟩
  · exact ⟨6689, 2, prime_6689, prime_2, by norm_num⟩
  · exact ⟨6691, 2, prime_6691, prime_2, by norm_num⟩
  · exact ⟨6691, 3, prime_6691, prime_3, by norm_num⟩
  · exact ⟨6689, 5, prime_6689, prime_5, by norm_num⟩
  · exact ⟨6691, 5, prime_6691, prime_5, by norm_num⟩
  · exact ⟨6689, 7, prime_6689, prime_7, by norm_num⟩
  · exact ⟨6701, 2, prime_6701, prime_2, by norm_num⟩
  · exact ⟨6703, 2, prime_6703, prime_2, by norm_num⟩
  · exact ⟨6703, 3, prime_6703, prime_3, by norm_num⟩
  · exact ⟨6701, 5, prime_6701, prime_5, by norm_num⟩
  · exact ⟨6709, 2, prime_6709, prime_2, by norm_num⟩
  · exact ⟨6709, 3, prime_6709, prime_3, by norm_num⟩
  · exact ⟨6703, 7, prime_6703, prime_7, by norm_num⟩
  · exact ⟨6709, 5, prime_6709, prime_5, by norm_num⟩
  · exact ⟨6659, 31, prime_6659, prime_31, by norm_num⟩
  · exact ⟨6719, 2, prime_6719, prime_2, by norm_num⟩
  · exact ⟨6719, 3, prime_6719, prime_3, by norm_num⟩
  · exact ⟨6701, 13, prime_6701, prime_13, by norm_num⟩
  · exact ⟨6719, 5, prime_6719, prime_5, by norm_num⟩
  · exact ⟨6709, 11, prime_6709, prime_11, by norm_num⟩
  · exact ⟨6719, 7, prime_6719, prime_7, by norm_num⟩
  · exact ⟨6709, 13, prime_6709, prime_13, by norm_num⟩
  · exact ⟨6733, 2, prime_6733, prime_2, by norm_num⟩
  · exact ⟨6733, 3, prime_6733, prime_3, by norm_num⟩
  · exact ⟨6737, 2, prime_6737, prime_2, by norm_num⟩
  · exact ⟨6737, 3, prime_6737, prime_3, by norm_num⟩
  · exact ⟨6719, 13, prime_6719, prime_13, by norm_num⟩
  · exact ⟨6737, 5, prime_6737, prime_5, by norm_num⟩
  · exact ⟨6703, 23, prime_6703, prime_23, by norm_num⟩
  · exact ⟨6737, 7, prime_6737, prime_7, by norm_num⟩
  · exact ⟨6719, 17, prime_6719, prime_17, by norm_num⟩
  · exact ⟨6733, 11, prime_6733, prime_11, by norm_num⟩
  · exact ⟨6719, 19, prime_6719, prime_19, by norm_num⟩
  · exact ⟨6737, 11, prime_6737, prime_11, by norm_num⟩
  · exact ⟨6703, 29, prime_6703, prime_29, by norm_num⟩
  · exact ⟨6737, 13, prime_6737, prime_13, by norm_num⟩
  · exact ⟨6761, 2, prime_6761, prime_2, by norm_num⟩
  · exact ⟨6763, 2, prime_6763, prime_2, by norm_num⟩
  · exact ⟨6763, 3, prime_6763, prime_3, by norm_num⟩
  · exact ⟨6761, 5, prime_6761, prime_5, by norm_num⟩
  · exact ⟨6763, 5, prime_6763, prime_5, by norm_num⟩
  · exact ⟨6761, 7, prime_6761, prime_7, by norm_num⟩
  · exact ⟨6763, 7, prime_6763, prime_7, by norm_num⟩
  · exact ⟨6733, 23, prime_6733, prime_23, by norm_num⟩
  · exact ⟨6719, 31, prime_6719, prime_31, by norm_num⟩
  · exact ⟨6779, 2, prime_6779, prime_2, by norm_num⟩
  · exact ⟨6781, 2, prime_6781, prime_2, by norm_num⟩
  · exact ⟨6781, 3, prime_6781, prime_3, by norm_num⟩
  · exact ⟨6779, 5, prime_6779, prime_5, by norm_num⟩
  · exact ⟨6781, 5, prime_6781, prime_5, by norm_num⟩
  · exact ⟨6779, 7, prime_6779, prime_7, by norm_num⟩
  · exact ⟨6791, 2, prime_6791, prime_2, by norm_num⟩
  · exact ⟨6793, 2, prime_6793, prime_2, by norm_num⟩
  · exact ⟨6793, 3, prime_6793, prime_3, by norm_num⟩
  · exact ⟨6791, 5, prime_6791, prime_5, by norm_num⟩
  · exact ⟨6793, 5, prime_6793, prime_5, by norm_num⟩
  · exact ⟨6791, 7, prime_6791, prime_7, by norm_num⟩

private theorem lemoine_chunk_34 : ∀ k : ℕ, 3403 ≤ k → k ≤ 3502 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨6803, 2, prime_6803, prime_2, by norm_num⟩
  · exact ⟨6803, 3, prime_6803, prime_3, by norm_num⟩
  · exact ⟨6737, 37, prime_6737, prime_37, by norm_num⟩
  · exact ⟨6803, 5, prime_6803, prime_5, by norm_num⟩
  · exact ⟨6793, 11, prime_6793, prime_11, by norm_num⟩
  · exact ⟨6803, 7, prime_6803, prime_7, by norm_num⟩
  · exact ⟨6793, 13, prime_6793, prime_13, by norm_num⟩
  · exact ⟨6763, 29, prime_6763, prime_29, by norm_num⟩
  · exact ⟨6761, 31, prime_6761, prime_31, by norm_num⟩
  · exact ⟨6803, 11, prime_6803, prime_11, by norm_num⟩
  · exact ⟨6823, 2, prime_6823, prime_2, by norm_num⟩
  · exact ⟨6823, 3, prime_6823, prime_3, by norm_num⟩
  · exact ⟨6827, 2, prime_6827, prime_2, by norm_num⟩
  · exact ⟨6829, 2, prime_6829, prime_2, by norm_num⟩
  · exact ⟨6829, 3, prime_6829, prime_3, by norm_num⟩
  · exact ⟨6833, 2, prime_6833, prime_2, by norm_num⟩
  · exact ⟨6833, 3, prime_6833, prime_3, by norm_num⟩
  · exact ⟨6827, 7, prime_6827, prime_7, by norm_num⟩
  · exact ⟨6833, 5, prime_6833, prime_5, by norm_num⟩
  · exact ⟨6841, 2, prime_6841, prime_2, by norm_num⟩
  · exact ⟨6841, 3, prime_6841, prime_3, by norm_num⟩
  · exact ⟨6827, 11, prime_6827, prime_11, by norm_num⟩
  · exact ⟨6841, 5, prime_6841, prime_5, by norm_num⟩
  · exact ⟨6827, 13, prime_6827, prime_13, by norm_num⟩
  · exact ⟨6841, 7, prime_6841, prime_7, by norm_num⟩
  · exact ⟨6823, 17, prime_6823, prime_17, by norm_num⟩
  · exact ⟨6833, 13, prime_6833, prime_13, by norm_num⟩
  · exact ⟨6857, 2, prime_6857, prime_2, by norm_num⟩
  · exact ⟨6857, 3, prime_6857, prime_3, by norm_num⟩
  · exact ⟨6827, 19, prime_6827, prime_19, by norm_num⟩
  · exact ⟨6863, 2, prime_6863, prime_2, by norm_num⟩
  · exact ⟨6863, 3, prime_6863, prime_3, by norm_num⟩
  · exact ⟨6857, 7, prime_6857, prime_7, by norm_num⟩
  · exact ⟨6869, 2, prime_6869, prime_2, by norm_num⟩
  · exact ⟨6871, 2, prime_6871, prime_2, by norm_num⟩
  · exact ⟨6871, 3, prime_6871, prime_3, by norm_num⟩
  · exact ⟨6869, 5, prime_6869, prime_5, by norm_num⟩
  · exact ⟨6871, 5, prime_6871, prime_5, by norm_num⟩
  · exact ⟨6869, 7, prime_6869, prime_7, by norm_num⟩
  · exact ⟨6871, 7, prime_6871, prime_7, by norm_num⟩
  · exact ⟨6883, 2, prime_6883, prime_2, by norm_num⟩
  · exact ⟨6883, 3, prime_6883, prime_3, by norm_num⟩
  · exact ⟨6869, 11, prime_6869, prime_11, by norm_num⟩
  · exact ⟨6883, 5, prime_6883, prime_5, by norm_num⟩
  · exact ⟨6869, 13, prime_6869, prime_13, by norm_num⟩
  · exact ⟨6883, 7, prime_6883, prime_7, by norm_num⟩
  · exact ⟨6841, 29, prime_6841, prime_29, by norm_num⟩
  · exact ⟨6863, 19, prime_6863, prime_19, by norm_num⟩
  · exact ⟨6899, 2, prime_6899, prime_2, by norm_num⟩
  · exact ⟨6899, 3, prime_6899, prime_3, by norm_num⟩
  · exact ⟨6869, 19, prime_6869, prime_19, by norm_num⟩
  · exact ⟨6899, 5, prime_6899, prime_5, by norm_num⟩
  · exact ⟨6907, 2, prime_6907, prime_2, by norm_num⟩
  · exact ⟨6907, 3, prime_6907, prime_3, by norm_num⟩
  · exact ⟨6911, 2, prime_6911, prime_2, by norm_num⟩
  · exact ⟨6911, 3, prime_6911, prime_3, by norm_num⟩
  · exact ⟨6857, 31, prime_6857, prime_31, by norm_num⟩
  · exact ⟨6917, 2, prime_6917, prime_2, by norm_num⟩
  · exact ⟨6917, 3, prime_6917, prime_3, by norm_num⟩
  · exact ⟨6911, 7, prime_6911, prime_7, by norm_num⟩
  · exact ⟨6917, 5, prime_6917, prime_5, by norm_num⟩
  · exact ⟨6907, 11, prime_6907, prime_11, by norm_num⟩
  · exact ⟨6917, 7, prime_6917, prime_7, by norm_num⟩
  · exact ⟨6911, 11, prime_6911, prime_11, by norm_num⟩
  · exact ⟨6841, 47, prime_6841, prime_47, by norm_num⟩
  · exact ⟨6911, 13, prime_6911, prime_13, by norm_num⟩
  · exact ⟨6917, 11, prime_6917, prime_11, by norm_num⟩
  · exact ⟨6907, 17, prime_6907, prime_17, by norm_num⟩
  · exact ⟨6917, 13, prime_6917, prime_13, by norm_num⟩
  · exact ⟨6911, 17, prime_6911, prime_17, by norm_num⟩
  · exact ⟨6841, 53, prime_6841, prime_53, by norm_num⟩
  · exact ⟨6911, 19, prime_6911, prime_19, by norm_num⟩
  · exact ⟨6947, 2, prime_6947, prime_2, by norm_num⟩
  · exact ⟨6949, 2, prime_6949, prime_2, by norm_num⟩
  · exact ⟨6949, 3, prime_6949, prime_3, by norm_num⟩
  · exact ⟨6947, 5, prime_6947, prime_5, by norm_num⟩
  · exact ⟨6949, 5, prime_6949, prime_5, by norm_num⟩
  · exact ⟨6947, 7, prime_6947, prime_7, by norm_num⟩
  · exact ⟨6959, 2, prime_6959, prime_2, by norm_num⟩
  · exact ⟨6961, 2, prime_6961, prime_2, by norm_num⟩
  · exact ⟨6961, 3, prime_6961, prime_3, by norm_num⟩
  · exact ⟨6959, 5, prime_6959, prime_5, by norm_num⟩
  · exact ⟨6967, 2, prime_6967, prime_2, by norm_num⟩
  · exact ⟨6967, 3, prime_6967, prime_3, by norm_num⟩
  · exact ⟨6971, 2, prime_6971, prime_2, by norm_num⟩
  · exact ⟨6971, 3, prime_6971, prime_3, by norm_num⟩
  · exact ⟨6917, 31, prime_6917, prime_31, by norm_num⟩
  · exact ⟨6977, 2, prime_6977, prime_2, by norm_num⟩
  · exact ⟨6977, 3, prime_6977, prime_3, by norm_num⟩
  · exact ⟨6971, 7, prime_6971, prime_7, by norm_num⟩
  · exact ⟨6983, 2, prime_6983, prime_2, by norm_num⟩
  · exact ⟨6983, 3, prime_6983, prime_3, by norm_num⟩
  · exact ⟨6977, 7, prime_6977, prime_7, by norm_num⟩
  · exact ⟨6983, 5, prime_6983, prime_5, by norm_num⟩
  · exact ⟨6991, 2, prime_6991, prime_2, by norm_num⟩
  · exact ⟨6991, 3, prime_6991, prime_3, by norm_num⟩
  · exact ⟨6977, 11, prime_6977, prime_11, by norm_num⟩
  · exact ⟨6997, 2, prime_6997, prime_2, by norm_num⟩
  · exact ⟨6997, 3, prime_6997, prime_3, by norm_num⟩
  · exact ⟨7001, 2, prime_7001, prime_2, by norm_num⟩

private theorem lemoine_chunk_35 : ∀ k : ℕ, 3503 ≤ k → k ≤ 3602 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7001, 3, prime_7001, prime_3, by norm_num⟩
  · exact ⟨6983, 13, prime_6983, prime_13, by norm_num⟩
  · exact ⟨7001, 5, prime_7001, prime_5, by norm_num⟩
  · exact ⟨6991, 11, prime_6991, prime_11, by norm_num⟩
  · exact ⟨7001, 7, prime_7001, prime_7, by norm_num⟩
  · exact ⟨7013, 2, prime_7013, prime_2, by norm_num⟩
  · exact ⟨7013, 3, prime_7013, prime_3, by norm_num⟩
  · exact ⟨6983, 19, prime_6983, prime_19, by norm_num⟩
  · exact ⟨7019, 2, prime_7019, prime_2, by norm_num⟩
  · exact ⟨7019, 3, prime_7019, prime_3, by norm_num⟩
  · exact ⟨7013, 7, prime_7013, prime_7, by norm_num⟩
  · exact ⟨7019, 5, prime_7019, prime_5, by norm_num⟩
  · exact ⟨7027, 2, prime_7027, prime_2, by norm_num⟩
  · exact ⟨7027, 3, prime_7027, prime_3, by norm_num⟩
  · exact ⟨7013, 11, prime_7013, prime_11, by norm_num⟩
  · exact ⟨7027, 5, prime_7027, prime_5, by norm_num⟩
  · exact ⟨7013, 13, prime_7013, prime_13, by norm_num⟩
  · exact ⟨7027, 7, prime_7027, prime_7, by norm_num⟩
  · exact ⟨7039, 2, prime_7039, prime_2, by norm_num⟩
  · exact ⟨7039, 3, prime_7039, prime_3, by norm_num⟩
  · exact ⟨7043, 2, prime_7043, prime_2, by norm_num⟩
  · exact ⟨7043, 3, prime_7043, prime_3, by norm_num⟩
  · exact ⟨7013, 19, prime_7013, prime_19, by norm_num⟩
  · exact ⟨7043, 5, prime_7043, prime_5, by norm_num⟩
  · exact ⟨6997, 29, prime_6997, prime_29, by norm_num⟩
  · exact ⟨7043, 7, prime_7043, prime_7, by norm_num⟩
  · exact ⟨7013, 23, prime_7013, prime_23, by norm_num⟩
  · exact ⟨7057, 2, prime_7057, prime_2, by norm_num⟩
  · exact ⟨7057, 3, prime_7057, prime_3, by norm_num⟩
  · exact ⟨7043, 11, prime_7043, prime_11, by norm_num⟩
  · exact ⟨7057, 5, prime_7057, prime_5, by norm_num⟩
  · exact ⟨7043, 13, prime_7043, prime_13, by norm_num⟩
  · exact ⟨7057, 7, prime_7057, prime_7, by norm_num⟩
  · exact ⟨7069, 2, prime_7069, prime_2, by norm_num⟩
  · exact ⟨7069, 3, prime_7069, prime_3, by norm_num⟩
  · exact ⟨7043, 17, prime_7043, prime_17, by norm_num⟩
  · exact ⟨7069, 5, prime_7069, prime_5, by norm_num⟩
  · exact ⟨7043, 19, prime_7043, prime_19, by norm_num⟩
  · exact ⟨7079, 2, prime_7079, prime_2, by norm_num⟩
  · exact ⟨7079, 3, prime_7079, prime_3, by norm_num⟩
  · exact ⟨7013, 37, prime_7013, prime_37, by norm_num⟩
  · exact ⟨7079, 5, prime_7079, prime_5, by norm_num⟩
  · exact ⟨7069, 11, prime_7069, prime_11, by norm_num⟩
  · exact ⟨7079, 7, prime_7079, prime_7, by norm_num⟩
  · exact ⟨7069, 13, prime_7069, prime_13, by norm_num⟩
  · exact ⟨7039, 29, prime_7039, prime_29, by norm_num⟩
  · exact ⟨7013, 43, prime_7013, prime_43, by norm_num⟩
  · exact ⟨7079, 11, prime_7079, prime_11, by norm_num⟩
  · exact ⟨7069, 17, prime_7069, prime_17, by norm_num⟩
  · exact ⟨7079, 13, prime_7079, prime_13, by norm_num⟩
  · exact ⟨7103, 2, prime_7103, prime_2, by norm_num⟩
  · exact ⟨7103, 3, prime_7103, prime_3, by norm_num⟩
  · exact ⟨6977, 67, prime_6977, prime_67, by norm_num⟩
  · exact ⟨7109, 2, prime_7109, prime_2, by norm_num⟩
  · exact ⟨7109, 3, prime_7109, prime_3, by norm_num⟩
  · exact ⟨7103, 7, prime_7103, prime_7, by norm_num⟩
  · exact ⟨7109, 5, prime_7109, prime_5, by norm_num⟩
  · exact ⟨7039, 41, prime_7039, prime_41, by norm_num⟩
  · exact ⟨7109, 7, prime_7109, prime_7, by norm_num⟩
  · exact ⟨7121, 2, prime_7121, prime_2, by norm_num⟩
  · exact ⟨7121, 3, prime_7121, prime_3, by norm_num⟩
  · exact ⟨7103, 13, prime_7103, prime_13, by norm_num⟩
  · exact ⟨7127, 2, prime_7127, prime_2, by norm_num⟩
  · exact ⟨7129, 2, prime_7129, prime_2, by norm_num⟩
  · exact ⟨7129, 3, prime_7129, prime_3, by norm_num⟩
  · exact ⟨7127, 5, prime_7127, prime_5, by norm_num⟩
  · exact ⟨7129, 5, prime_7129, prime_5, by norm_num⟩
  · exact ⟨7127, 7, prime_7127, prime_7, by norm_num⟩
  · exact ⟨7129, 7, prime_7129, prime_7, by norm_num⟩
  · exact ⟨7039, 53, prime_7039, prime_53, by norm_num⟩
  · exact ⟨7121, 13, prime_7121, prime_13, by norm_num⟩
  · exact ⟨7127, 11, prime_7127, prime_11, by norm_num⟩
  · exact ⟨7129, 11, prime_7129, prime_11, by norm_num⟩
  · exact ⟨7127, 13, prime_7127, prime_13, by norm_num⟩
  · exact ⟨7151, 2, prime_7151, prime_2, by norm_num⟩
  · exact ⟨7151, 3, prime_7151, prime_3, by norm_num⟩
  · exact ⟨7121, 19, prime_7121, prime_19, by norm_num⟩
  · exact ⟨7151, 5, prime_7151, prime_5, by norm_num⟩
  · exact ⟨7159, 2, prime_7159, prime_2, by norm_num⟩
  · exact ⟨7159, 3, prime_7159, prime_3, by norm_num⟩
  · exact ⟨7129, 19, prime_7129, prime_19, by norm_num⟩
  · exact ⟨7159, 5, prime_7159, prime_5, by norm_num⟩
  · exact ⟨7109, 31, prime_7109, prime_31, by norm_num⟩
  · exact ⟨7159, 7, prime_7159, prime_7, by norm_num⟩
  · exact ⟨7129, 23, prime_7129, prime_23, by norm_num⟩
  · exact ⟨7151, 13, prime_7151, prime_13, by norm_num⟩
  · exact ⟨7121, 29, prime_7121, prime_29, by norm_num⟩
  · exact ⟨7177, 2, prime_7177, prime_2, by norm_num⟩
  · exact ⟨7177, 3, prime_7177, prime_3, by norm_num⟩
  · exact ⟨7159, 13, prime_7159, prime_13, by norm_num⟩
  · exact ⟨7177, 5, prime_7177, prime_5, by norm_num⟩
  · exact ⟨7151, 19, prime_7151, prime_19, by norm_num⟩
  · exact ⟨7187, 2, prime_7187, prime_2, by norm_num⟩
  · exact ⟨7187, 3, prime_7187, prime_3, by norm_num⟩
  · exact ⟨7121, 37, prime_7121, prime_37, by norm_num⟩
  · exact ⟨7193, 2, prime_7193, prime_2, by norm_num⟩
  · exact ⟨7193, 3, prime_7193, prime_3, by norm_num⟩
  · exact ⟨7187, 7, prime_7187, prime_7, by norm_num⟩
  · exact ⟨7193, 5, prime_7193, prime_5, by norm_num⟩
  · exact ⟨7159, 23, prime_7159, prime_23, by norm_num⟩

private theorem lemoine_chunk_36 : ∀ k : ℕ, 3603 ≤ k → k ≤ 3702 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7193, 7, prime_7193, prime_7, by norm_num⟩
  · exact ⟨7187, 11, prime_7187, prime_11, by norm_num⟩
  · exact ⟨7207, 2, prime_7207, prime_2, by norm_num⟩
  · exact ⟨7207, 3, prime_7207, prime_3, by norm_num⟩
  · exact ⟨7211, 2, prime_7211, prime_2, by norm_num⟩
  · exact ⟨7213, 2, prime_7213, prime_2, by norm_num⟩
  · exact ⟨7213, 3, prime_7213, prime_3, by norm_num⟩
  · exact ⟨7211, 5, prime_7211, prime_5, by norm_num⟩
  · exact ⟨7219, 2, prime_7219, prime_2, by norm_num⟩
  · exact ⟨7219, 3, prime_7219, prime_3, by norm_num⟩
  · exact ⟨7213, 7, prime_7213, prime_7, by norm_num⟩
  · exact ⟨7219, 5, prime_7219, prime_5, by norm_num⟩
  · exact ⟨7193, 19, prime_7193, prime_19, by norm_num⟩
  · exact ⟨7229, 2, prime_7229, prime_2, by norm_num⟩
  · exact ⟨7229, 3, prime_7229, prime_3, by norm_num⟩
  · exact ⟨7211, 13, prime_7211, prime_13, by norm_num⟩
  · exact ⟨7229, 5, prime_7229, prime_5, by norm_num⟩
  · exact ⟨7237, 2, prime_7237, prime_2, by norm_num⟩
  · exact ⟨7237, 3, prime_7237, prime_3, by norm_num⟩
  · exact ⟨7219, 13, prime_7219, prime_13, by norm_num⟩
  · exact ⟨7243, 2, prime_7243, prime_2, by norm_num⟩
  · exact ⟨7243, 3, prime_7243, prime_3, by norm_num⟩
  · exact ⟨7247, 2, prime_7247, prime_2, by norm_num⟩
  · exact ⟨7247, 3, prime_7247, prime_3, by norm_num⟩
  · exact ⟨7229, 13, prime_7229, prime_13, by norm_num⟩
  · exact ⟨7253, 2, prime_7253, prime_2, by norm_num⟩
  · exact ⟨7253, 3, prime_7253, prime_3, by norm_num⟩
  · exact ⟨7247, 7, prime_7247, prime_7, by norm_num⟩
  · exact ⟨7253, 5, prime_7253, prime_5, by norm_num⟩
  · exact ⟨7243, 11, prime_7243, prime_11, by norm_num⟩
  · exact ⟨7253, 7, prime_7253, prime_7, by norm_num⟩
  · exact ⟨7247, 11, prime_7247, prime_11, by norm_num⟩
  · exact ⟨7237, 17, prime_7237, prime_17, by norm_num⟩
  · exact ⟨7247, 13, prime_7247, prime_13, by norm_num⟩
  · exact ⟨7253, 11, prime_7253, prime_11, by norm_num⟩
  · exact ⟨7243, 17, prime_7243, prime_17, by norm_num⟩
  · exact ⟨7253, 13, prime_7253, prime_13, by norm_num⟩
  · exact ⟨7247, 17, prime_7247, prime_17, by norm_num⟩
  · exact ⟨7237, 23, prime_7237, prime_23, by norm_num⟩
  · exact ⟨7247, 19, prime_7247, prime_19, by norm_num⟩
  · exact ⟨7283, 2, prime_7283, prime_2, by norm_num⟩
  · exact ⟨7283, 3, prime_7283, prime_3, by norm_num⟩
  · exact ⟨7253, 19, prime_7253, prime_19, by norm_num⟩
  · exact ⟨7283, 5, prime_7283, prime_5, by norm_num⟩
  · exact ⟨7237, 29, prime_7237, prime_29, by norm_num⟩
  · exact ⟨7283, 7, prime_7283, prime_7, by norm_num⟩
  · exact ⟨7253, 23, prime_7253, prime_23, by norm_num⟩
  · exact ⟨7297, 2, prime_7297, prime_2, by norm_num⟩
  · exact ⟨7297, 3, prime_7297, prime_3, by norm_num⟩
  · exact ⟨7283, 11, prime_7283, prime_11, by norm_num⟩
  · exact ⟨7297, 5, prime_7297, prime_5, by norm_num⟩
  · exact ⟨7283, 13, prime_7283, prime_13, by norm_num⟩
  · exact ⟨7307, 2, prime_7307, prime_2, by norm_num⟩
  · exact ⟨7309, 2, prime_7309, prime_2, by norm_num⟩
  · exact ⟨7309, 3, prime_7309, prime_3, by norm_num⟩
  · exact ⟨7307, 5, prime_7307, prime_5, by norm_num⟩
  · exact ⟨7309, 5, prime_7309, prime_5, by norm_num⟩
  · exact ⟨7307, 7, prime_7307, prime_7, by norm_num⟩
  · exact ⟨7309, 7, prime_7309, prime_7, by norm_num⟩
  · exact ⟨7321, 2, prime_7321, prime_2, by norm_num⟩
  · exact ⟨7321, 3, prime_7321, prime_3, by norm_num⟩
  · exact ⟨7307, 11, prime_7307, prime_11, by norm_num⟩
  · exact ⟨7321, 5, prime_7321, prime_5, by norm_num⟩
  · exact ⟨7307, 13, prime_7307, prime_13, by norm_num⟩
  · exact ⟨7331, 2, prime_7331, prime_2, by norm_num⟩
  · exact ⟨7333, 2, prime_7333, prime_2, by norm_num⟩
  · exact ⟨7333, 3, prime_7333, prime_3, by norm_num⟩
  · exact ⟨7331, 5, prime_7331, prime_5, by norm_num⟩
  · exact ⟨7333, 5, prime_7333, prime_5, by norm_num⟩
  · exact ⟨7331, 7, prime_7331, prime_7, by norm_num⟩
  · exact ⟨7333, 7, prime_7333, prime_7, by norm_num⟩
  · exact ⟨7243, 53, prime_7243, prime_53, by norm_num⟩
  · exact ⟨7229, 61, prime_7229, prime_61, by norm_num⟩
  · exact ⟨7349, 2, prime_7349, prime_2, by norm_num⟩
  · exact ⟨7351, 2, prime_7351, prime_2, by norm_num⟩
  · exact ⟨7351, 3, prime_7351, prime_3, by norm_num⟩
  · exact ⟨7349, 5, prime_7349, prime_5, by norm_num⟩
  · exact ⟨7351, 5, prime_7351, prime_5, by norm_num⟩
  · exact ⟨7349, 7, prime_7349, prime_7, by norm_num⟩
  · exact ⟨7351, 7, prime_7351, prime_7, by norm_num⟩
  · exact ⟨7333, 17, prime_7333, prime_17, by norm_num⟩
  · exact ⟨7331, 19, prime_7331, prime_19, by norm_num⟩
  · exact ⟨7349, 11, prime_7349, prime_11, by norm_num⟩
  · exact ⟨7369, 2, prime_7369, prime_2, by norm_num⟩
  · exact ⟨7369, 3, prime_7369, prime_3, by norm_num⟩
  · exact ⟨7351, 13, prime_7351, prime_13, by norm_num⟩
  · exact ⟨7369, 5, prime_7369, prime_5, by norm_num⟩
  · exact ⟨7307, 37, prime_7307, prime_37, by norm_num⟩
  · exact ⟨7369, 7, prime_7369, prime_7, by norm_num⟩
  · exact ⟨7351, 17, prime_7351, prime_17, by norm_num⟩
  · exact ⟨7349, 19, prime_7349, prime_19, by norm_num⟩
  · exact ⟨7351, 19, prime_7351, prime_19, by norm_num⟩
  · exact ⟨7369, 11, prime_7369, prime_11, by norm_num⟩
  · exact ⟨7331, 31, prime_7331, prime_31, by norm_num⟩
  · exact ⟨7369, 13, prime_7369, prime_13, by norm_num⟩
  · exact ⟨7393, 2, prime_7393, prime_2, by norm_num⟩
  · exact ⟨7393, 3, prime_7393, prime_3, by norm_num⟩
  · exact ⟨7307, 47, prime_7307, prime_47, by norm_num⟩
  · exact ⟨7393, 5, prime_7393, prime_5, by norm_num⟩
  · exact ⟨7331, 37, prime_7331, prime_37, by norm_num⟩

private theorem lemoine_chunk_37 : ∀ k : ℕ, 3703 ≤ k → k ≤ 3802 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7393, 7, prime_7393, prime_7, by norm_num⟩
  · exact ⟨7351, 29, prime_7351, prime_29, by norm_num⟩
  · exact ⟨7349, 31, prime_7349, prime_31, by norm_num⟩
  · exact ⟨7351, 31, prime_7351, prime_31, by norm_num⟩
  · exact ⟨7411, 2, prime_7411, prime_2, by norm_num⟩
  · exact ⟨7411, 3, prime_7411, prime_3, by norm_num⟩
  · exact ⟨7393, 13, prime_7393, prime_13, by norm_num⟩
  · exact ⟨7417, 2, prime_7417, prime_2, by norm_num⟩
  · exact ⟨7417, 3, prime_7417, prime_3, by norm_num⟩
  · exact ⟨7411, 7, prime_7411, prime_7, by norm_num⟩
  · exact ⟨7417, 5, prime_7417, prime_5, by norm_num⟩
  · exact ⟨7307, 61, prime_7307, prime_61, by norm_num⟩
  · exact ⟨7417, 7, prime_7417, prime_7, by norm_num⟩
  · exact ⟨7411, 11, prime_7411, prime_11, by norm_num⟩
  · exact ⟨7349, 43, prime_7349, prime_43, by norm_num⟩
  · exact ⟨7433, 2, prime_7433, prime_2, by norm_num⟩
  · exact ⟨7433, 3, prime_7433, prime_3, by norm_num⟩
  · exact ⟨7307, 67, prime_7307, prime_67, by norm_num⟩
  · exact ⟨7433, 5, prime_7433, prime_5, by norm_num⟩
  · exact ⟨7411, 17, prime_7411, prime_17, by norm_num⟩
  · exact ⟨7433, 7, prime_7433, prime_7, by norm_num⟩
  · exact ⟨7411, 19, prime_7411, prime_19, by norm_num⟩
  · exact ⟨7417, 17, prime_7417, prime_17, by norm_num⟩
  · exact ⟨7331, 61, prime_7331, prime_61, by norm_num⟩
  · exact ⟨7451, 2, prime_7451, prime_2, by norm_num⟩
  · exact ⟨7451, 3, prime_7451, prime_3, by norm_num⟩
  · exact ⟨7433, 13, prime_7433, prime_13, by norm_num⟩
  · exact ⟨7457, 2, prime_7457, prime_2, by norm_num⟩
  · exact ⟨7459, 2, prime_7459, prime_2, by norm_num⟩
  · exact ⟨7459, 3, prime_7459, prime_3, by norm_num⟩
  · exact ⟨7457, 5, prime_7457, prime_5, by norm_num⟩
  · exact ⟨7459, 5, prime_7459, prime_5, by norm_num⟩
  · exact ⟨7457, 7, prime_7457, prime_7, by norm_num⟩
  · exact ⟨7459, 7, prime_7459, prime_7, by norm_num⟩
  · exact ⟨7417, 29, prime_7417, prime_29, by norm_num⟩
  · exact ⟨7451, 13, prime_7451, prime_13, by norm_num⟩
  · exact ⟨7457, 11, prime_7457, prime_11, by norm_num⟩
  · exact ⟨7477, 2, prime_7477, prime_2, by norm_num⟩
  · exact ⟨7477, 3, prime_7477, prime_3, by norm_num⟩
  · exact ⟨7481, 2, prime_7481, prime_2, by norm_num⟩
  · exact ⟨7481, 3, prime_7481, prime_3, by norm_num⟩
  · exact ⟨7451, 19, prime_7451, prime_19, by norm_num⟩
  · exact ⟨7487, 2, prime_7487, prime_2, by norm_num⟩
  · exact ⟨7489, 2, prime_7489, prime_2, by norm_num⟩
  · exact ⟨7489, 3, prime_7489, prime_3, by norm_num⟩
  · exact ⟨7487, 5, prime_7487, prime_5, by norm_num⟩
  · exact ⟨7489, 5, prime_7489, prime_5, by norm_num⟩
  · exact ⟨7487, 7, prime_7487, prime_7, by norm_num⟩
  · exact ⟨7499, 2, prime_7499, prime_2, by norm_num⟩
  · exact ⟨7499, 3, prime_7499, prime_3, by norm_num⟩
  · exact ⟨7481, 13, prime_7481, prime_13, by norm_num⟩
  · exact ⟨7499, 5, prime_7499, prime_5, by norm_num⟩
  · exact ⟨7507, 2, prime_7507, prime_2, by norm_num⟩
  · exact ⟨7507, 3, prime_7507, prime_3, by norm_num⟩
  · exact ⟨7489, 13, prime_7489, prime_13, by norm_num⟩
  · exact ⟨7507, 5, prime_7507, prime_5, by norm_num⟩
  · exact ⟨7481, 19, prime_7481, prime_19, by norm_num⟩
  · exact ⟨7517, 2, prime_7517, prime_2, by norm_num⟩
  · exact ⟨7517, 3, prime_7517, prime_3, by norm_num⟩
  · exact ⟨7499, 13, prime_7499, prime_13, by norm_num⟩
  · exact ⟨7523, 2, prime_7523, prime_2, by norm_num⟩
  · exact ⟨7523, 3, prime_7523, prime_3, by norm_num⟩
  · exact ⟨7517, 7, prime_7517, prime_7, by norm_num⟩
  · exact ⟨7529, 2, prime_7529, prime_2, by norm_num⟩
  · exact ⟨7529, 3, prime_7529, prime_3, by norm_num⟩
  · exact ⟨7523, 7, prime_7523, prime_7, by norm_num⟩
  · exact ⟨7529, 5, prime_7529, prime_5, by norm_num⟩
  · exact ⟨7537, 2, prime_7537, prime_2, by norm_num⟩
  · exact ⟨7537, 3, prime_7537, prime_3, by norm_num⟩
  · exact ⟨7541, 2, prime_7541, prime_2, by norm_num⟩
  · exact ⟨7541, 3, prime_7541, prime_3, by norm_num⟩
  · exact ⟨7523, 13, prime_7523, prime_13, by norm_num⟩
  · exact ⟨7547, 2, prime_7547, prime_2, by norm_num⟩
  · exact ⟨7549, 2, prime_7549, prime_2, by norm_num⟩
  · exact ⟨7549, 3, prime_7549, prime_3, by norm_num⟩
  · exact ⟨7547, 5, prime_7547, prime_5, by norm_num⟩
  · exact ⟨7549, 5, prime_7549, prime_5, by norm_num⟩
  · exact ⟨7547, 7, prime_7547, prime_7, by norm_num⟩
  · exact ⟨7559, 2, prime_7559, prime_2, by norm_num⟩
  · exact ⟨7561, 2, prime_7561, prime_2, by norm_num⟩
  · exact ⟨7561, 3, prime_7561, prime_3, by norm_num⟩
  · exact ⟨7559, 5, prime_7559, prime_5, by norm_num⟩
  · exact ⟨7561, 5, prime_7561, prime_5, by norm_num⟩
  · exact ⟨7559, 7, prime_7559, prime_7, by norm_num⟩
  · exact ⟨7561, 7, prime_7561, prime_7, by norm_num⟩
  · exact ⟨7573, 2, prime_7573, prime_2, by norm_num⟩
  · exact ⟨7573, 3, prime_7573, prime_3, by norm_num⟩
  · exact ⟨7577, 2, prime_7577, prime_2, by norm_num⟩
  · exact ⟨7577, 3, prime_7577, prime_3, by norm_num⟩
  · exact ⟨7559, 13, prime_7559, prime_13, by norm_num⟩
  · exact ⟨7583, 2, prime_7583, prime_2, by norm_num⟩
  · exact ⟨7583, 3, prime_7583, prime_3, by norm_num⟩
  · exact ⟨7577, 7, prime_7577, prime_7, by norm_num⟩
  · exact ⟨7589, 2, prime_7589, prime_2, by norm_num⟩
  · exact ⟨7591, 2, prime_7591, prime_2, by norm_num⟩
  · exact ⟨7591, 3, prime_7591, prime_3, by norm_num⟩
  · exact ⟨7589, 5, prime_7589, prime_5, by norm_num⟩
  · exact ⟨7591, 5, prime_7591, prime_5, by norm_num⟩
  · exact ⟨7589, 7, prime_7589, prime_7, by norm_num⟩
  · exact ⟨7591, 7, prime_7591, prime_7, by norm_num⟩

private theorem lemoine_chunk_38 : ∀ k : ℕ, 3803 ≤ k → k ≤ 3902 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7603, 2, prime_7603, prime_2, by norm_num⟩
  · exact ⟨7603, 3, prime_7603, prime_3, by norm_num⟩
  · exact ⟨7607, 2, prime_7607, prime_2, by norm_num⟩
  · exact ⟨7607, 3, prime_7607, prime_3, by norm_num⟩
  · exact ⟨7589, 13, prime_7589, prime_13, by norm_num⟩
  · exact ⟨7607, 5, prime_7607, prime_5, by norm_num⟩
  · exact ⟨7573, 23, prime_7573, prime_23, by norm_num⟩
  · exact ⟨7607, 7, prime_7607, prime_7, by norm_num⟩
  · exact ⟨7589, 17, prime_7589, prime_17, by norm_num⟩
  · exact ⟨7621, 2, prime_7621, prime_2, by norm_num⟩
  · exact ⟨7621, 3, prime_7621, prime_3, by norm_num⟩
  · exact ⟨7607, 11, prime_7607, prime_11, by norm_num⟩
  · exact ⟨7621, 5, prime_7621, prime_5, by norm_num⟩
  · exact ⟨7607, 13, prime_7607, prime_13, by norm_num⟩
  · exact ⟨7621, 7, prime_7621, prime_7, by norm_num⟩
  · exact ⟨7603, 17, prime_7603, prime_17, by norm_num⟩
  · exact ⟨7577, 31, prime_7577, prime_31, by norm_num⟩
  · exact ⟨7607, 17, prime_7607, prime_17, by norm_num⟩
  · exact ⟨7639, 2, prime_7639, prime_2, by norm_num⟩
  · exact ⟨7639, 3, prime_7639, prime_3, by norm_num⟩
  · exact ⟨7643, 2, prime_7643, prime_2, by norm_num⟩
  · exact ⟨7643, 3, prime_7643, prime_3, by norm_num⟩
  · exact ⟨7589, 31, prime_7589, prime_31, by norm_num⟩
  · exact ⟨7649, 2, prime_7649, prime_2, by norm_num⟩
  · exact ⟨7649, 3, prime_7649, prime_3, by norm_num⟩
  · exact ⟨7643, 7, prime_7643, prime_7, by norm_num⟩
  · exact ⟨7649, 5, prime_7649, prime_5, by norm_num⟩
  · exact ⟨7639, 11, prime_7639, prime_11, by norm_num⟩
  · exact ⟨7649, 7, prime_7649, prime_7, by norm_num⟩
  · exact ⟨7643, 11, prime_7643, prime_11, by norm_num⟩
  · exact ⟨7621, 23, prime_7621, prime_23, by norm_num⟩
  · exact ⟨7643, 13, prime_7643, prime_13, by norm_num⟩
  · exact ⟨7649, 11, prime_7649, prime_11, by norm_num⟩
  · exact ⟨7669, 2, prime_7669, prime_2, by norm_num⟩
  · exact ⟨7669, 3, prime_7669, prime_3, by norm_num⟩
  · exact ⟨7673, 2, prime_7673, prime_2, by norm_num⟩
  · exact ⟨7673, 3, prime_7673, prime_3, by norm_num⟩
  · exact ⟨7643, 19, prime_7643, prime_19, by norm_num⟩
  · exact ⟨7673, 5, prime_7673, prime_5, by norm_num⟩
  · exact ⟨7681, 2, prime_7681, prime_2, by norm_num⟩
  · exact ⟨7681, 3, prime_7681, prime_3, by norm_num⟩
  · exact ⟨7643, 23, prime_7643, prime_23, by norm_num⟩
  · exact ⟨7687, 2, prime_7687, prime_2, by norm_num⟩
  · exact ⟨7687, 3, prime_7687, prime_3, by norm_num⟩
  · exact ⟨7691, 2, prime_7691, prime_2, by norm_num⟩
  · exact ⟨7691, 3, prime_7691, prime_3, by norm_num⟩
  · exact ⟨7673, 13, prime_7673, prime_13, by norm_num⟩
  · exact ⟨7691, 5, prime_7691, prime_5, by norm_num⟩
  · exact ⟨7699, 2, prime_7699, prime_2, by norm_num⟩
  · exact ⟨7699, 3, prime_7699, prime_3, by norm_num⟩
  · exact ⟨7703, 2, prime_7703, prime_2, by norm_num⟩
  · exact ⟨7703, 3, prime_7703, prime_3, by norm_num⟩
  · exact ⟨7673, 19, prime_7673, prime_19, by norm_num⟩
  · exact ⟨7703, 5, prime_7703, prime_5, by norm_num⟩
  · exact ⟨7681, 17, prime_7681, prime_17, by norm_num⟩
  · exact ⟨7703, 7, prime_7703, prime_7, by norm_num⟩
  · exact ⟨7681, 19, prime_7681, prime_19, by norm_num⟩
  · exact ⟨7717, 2, prime_7717, prime_2, by norm_num⟩
  · exact ⟨7717, 3, prime_7717, prime_3, by norm_num⟩
  · exact ⟨7703, 11, prime_7703, prime_11, by norm_num⟩
  · exact ⟨7723, 2, prime_7723, prime_2, by norm_num⟩
  · exact ⟨7723, 3, prime_7723, prime_3, by norm_num⟩
  · exact ⟨7727, 2, prime_7727, prime_2, by norm_num⟩
  · exact ⟨7727, 3, prime_7727, prime_3, by norm_num⟩
  · exact ⟨7673, 31, prime_7673, prime_31, by norm_num⟩
  · exact ⟨7727, 5, prime_7727, prime_5, by norm_num⟩
  · exact ⟨7717, 11, prime_7717, prime_11, by norm_num⟩
  · exact ⟨7727, 7, prime_7727, prime_7, by norm_num⟩
  · exact ⟨7717, 13, prime_7717, prime_13, by norm_num⟩
  · exact ⟨7741, 2, prime_7741, prime_2, by norm_num⟩
  · exact ⟨7741, 3, prime_7741, prime_3, by norm_num⟩
  · exact ⟨7727, 11, prime_7727, prime_11, by norm_num⟩
  · exact ⟨7741, 5, prime_7741, prime_5, by norm_num⟩
  · exact ⟨7727, 13, prime_7727, prime_13, by norm_num⟩
  · exact ⟨7741, 7, prime_7741, prime_7, by norm_num⟩
  · exact ⟨7753, 2, prime_7753, prime_2, by norm_num⟩
  · exact ⟨7753, 3, prime_7753, prime_3, by norm_num⟩
  · exact ⟨7757, 2, prime_7757, prime_2, by norm_num⟩
  · exact ⟨7759, 2, prime_7759, prime_2, by norm_num⟩
  · exact ⟨7759, 3, prime_7759, prime_3, by norm_num⟩
  · exact ⟨7757, 5, prime_7757, prime_5, by norm_num⟩
  · exact ⟨7759, 5, prime_7759, prime_5, by norm_num⟩
  · exact ⟨7757, 7, prime_7757, prime_7, by norm_num⟩
  · exact ⟨7759, 7, prime_7759, prime_7, by norm_num⟩
  · exact ⟨7753, 11, prime_7753, prime_11, by norm_num⟩
  · exact ⟨7703, 37, prime_7703, prime_37, by norm_num⟩
  · exact ⟨7757, 11, prime_7757, prime_11, by norm_num⟩
  · exact ⟨7759, 11, prime_7759, prime_11, by norm_num⟩
  · exact ⟨7757, 13, prime_7757, prime_13, by norm_num⟩
  · exact ⟨7759, 13, prime_7759, prime_13, by norm_num⟩
  · exact ⟨7753, 17, prime_7753, prime_17, by norm_num⟩
  · exact ⟨7727, 31, prime_7727, prime_31, by norm_num⟩
  · exact ⟨7757, 17, prime_7757, prime_17, by norm_num⟩
  · exact ⟨7789, 2, prime_7789, prime_2, by norm_num⟩
  · exact ⟨7789, 3, prime_7789, prime_3, by norm_num⟩
  · exact ⟨7793, 2, prime_7793, prime_2, by norm_num⟩
  · exact ⟨7793, 3, prime_7793, prime_3, by norm_num⟩
  · exact ⟨7727, 37, prime_7727, prime_37, by norm_num⟩
  · exact ⟨7793, 5, prime_7793, prime_5, by norm_num⟩
  · exact ⟨7759, 23, prime_7759, prime_23, by norm_num⟩

private theorem lemoine_chunk_39 : ∀ k : ℕ, 3903 ≤ k → k ≤ 4002 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7793, 7, prime_7793, prime_7, by norm_num⟩
  · exact ⟨7727, 41, prime_7727, prime_41, by norm_num⟩
  · exact ⟨7789, 11, prime_7789, prime_11, by norm_num⟩
  · exact ⟨7727, 43, prime_7727, prime_43, by norm_num⟩
  · exact ⟨7793, 11, prime_7793, prime_11, by norm_num⟩
  · exact ⟨7759, 29, prime_7759, prime_29, by norm_num⟩
  · exact ⟨7793, 13, prime_7793, prime_13, by norm_num⟩
  · exact ⟨7817, 2, prime_7817, prime_2, by norm_num⟩
  · exact ⟨7817, 3, prime_7817, prime_3, by norm_num⟩
  · exact ⟨7703, 61, prime_7703, prime_61, by norm_num⟩
  · exact ⟨7823, 2, prime_7823, prime_2, by norm_num⟩
  · exact ⟨7823, 3, prime_7823, prime_3, by norm_num⟩
  · exact ⟨7817, 7, prime_7817, prime_7, by norm_num⟩
  · exact ⟨7829, 2, prime_7829, prime_2, by norm_num⟩
  · exact ⟨7829, 3, prime_7829, prime_3, by norm_num⟩
  · exact ⟨7823, 7, prime_7823, prime_7, by norm_num⟩
  · exact ⟨7829, 5, prime_7829, prime_5, by norm_num⟩
  · exact ⟨7759, 41, prime_7759, prime_41, by norm_num⟩
  · exact ⟨7829, 7, prime_7829, prime_7, by norm_num⟩
  · exact ⟨7841, 2, prime_7841, prime_2, by norm_num⟩
  · exact ⟨7841, 3, prime_7841, prime_3, by norm_num⟩
  · exact ⟨7823, 13, prime_7823, prime_13, by norm_num⟩
  · exact ⟨7841, 5, prime_7841, prime_5, by norm_num⟩
  · exact ⟨7759, 47, prime_7759, prime_47, by norm_num⟩
  · exact ⟨7841, 7, prime_7841, prime_7, by norm_num⟩
  · exact ⟨7853, 2, prime_7853, prime_2, by norm_num⟩
  · exact ⟨7853, 3, prime_7853, prime_3, by norm_num⟩
  · exact ⟨7823, 19, prime_7823, prime_19, by norm_num⟩
  · exact ⟨7853, 5, prime_7853, prime_5, by norm_num⟩
  · exact ⟨7759, 53, prime_7759, prime_53, by norm_num⟩
  · exact ⟨7853, 7, prime_7853, prime_7, by norm_num⟩
  · exact ⟨7823, 23, prime_7823, prime_23, by norm_num⟩
  · exact ⟨7867, 2, prime_7867, prime_2, by norm_num⟩
  · exact ⟨7867, 3, prime_7867, prime_3, by norm_num⟩
  · exact ⟨7853, 11, prime_7853, prime_11, by norm_num⟩
  · exact ⟨7873, 2, prime_7873, prime_2, by norm_num⟩
  · exact ⟨7873, 3, prime_7873, prime_3, by norm_num⟩
  · exact ⟨7877, 2, prime_7877, prime_2, by norm_num⟩
  · exact ⟨7879, 2, prime_7879, prime_2, by norm_num⟩
  · exact ⟨7879, 3, prime_7879, prime_3, by norm_num⟩
  · exact ⟨7883, 2, prime_7883, prime_2, by norm_num⟩
  · exact ⟨7883, 3, prime_7883, prime_3, by norm_num⟩
  · exact ⟨7877, 7, prime_7877, prime_7, by norm_num⟩
  · exact ⟨7883, 5, prime_7883, prime_5, by norm_num⟩
  · exact ⟨7873, 11, prime_7873, prime_11, by norm_num⟩
  · exact ⟨7883, 7, prime_7883, prime_7, by norm_num⟩
  · exact ⟨7877, 11, prime_7877, prime_11, by norm_num⟩
  · exact ⟨7879, 11, prime_7879, prime_11, by norm_num⟩
  · exact ⟨7877, 13, prime_7877, prime_13, by norm_num⟩
  · exact ⟨7901, 2, prime_7901, prime_2, by norm_num⟩
  · exact ⟨7901, 3, prime_7901, prime_3, by norm_num⟩
  · exact ⟨7883, 13, prime_7883, prime_13, by norm_num⟩
  · exact ⟨7907, 2, prime_7907, prime_2, by norm_num⟩
  · exact ⟨7907, 3, prime_7907, prime_3, by norm_num⟩
  · exact ⟨7901, 7, prime_7901, prime_7, by norm_num⟩
  · exact ⟨7907, 5, prime_7907, prime_5, by norm_num⟩
  · exact ⟨7873, 23, prime_7873, prime_23, by norm_num⟩
  · exact ⟨7907, 7, prime_7907, prime_7, by norm_num⟩
  · exact ⟨7919, 2, prime_7919, prime_2, by norm_num⟩
  · exact ⟨7919, 3, prime_7919, prime_3, by norm_num⟩
  · exact ⟨7901, 13, prime_7901, prime_13, by norm_num⟩
  · exact ⟨7919, 5, prime_7919, prime_5, by norm_num⟩
  · exact ⟨7927, 2, prime_7927, prime_2, by norm_num⟩
  · exact ⟨7927, 3, prime_7927, prime_3, by norm_num⟩
  · exact ⟨7901, 17, prime_7901, prime_17, by norm_num⟩
  · exact ⟨7933, 2, prime_7933, prime_2, by norm_num⟩
  · exact ⟨7933, 3, prime_7933, prime_3, by norm_num⟩
  · exact ⟨7937, 2, prime_7937, prime_2, by norm_num⟩
  · exact ⟨7937, 3, prime_7937, prime_3, by norm_num⟩
  · exact ⟨7919, 13, prime_7919, prime_13, by norm_num⟩
  · exact ⟨7937, 5, prime_7937, prime_5, by norm_num⟩
  · exact ⟨7927, 11, prime_7927, prime_11, by norm_num⟩
  · exact ⟨7937, 7, prime_7937, prime_7, by norm_num⟩
  · exact ⟨7949, 2, prime_7949, prime_2, by norm_num⟩
  · exact ⟨7951, 2, prime_7951, prime_2, by norm_num⟩
  · exact ⟨7951, 3, prime_7951, prime_3, by norm_num⟩
  · exact ⟨7949, 5, prime_7949, prime_5, by norm_num⟩
  · exact ⟨7951, 5, prime_7951, prime_5, by norm_num⟩
  · exact ⟨7949, 7, prime_7949, prime_7, by norm_num⟩
  · exact ⟨7951, 7, prime_7951, prime_7, by norm_num⟩
  · exact ⟨7963, 2, prime_7963, prime_2, by norm_num⟩
  · exact ⟨7963, 3, prime_7963, prime_3, by norm_num⟩
  · exact ⟨7949, 11, prime_7949, prime_11, by norm_num⟩
  · exact ⟨7963, 5, prime_7963, prime_5, by norm_num⟩
  · exact ⟨7949, 13, prime_7949, prime_13, by norm_num⟩
  · exact ⟨7963, 7, prime_7963, prime_7, by norm_num⟩
  · exact ⟨7933, 23, prime_7933, prime_23, by norm_num⟩
  · exact ⟨7919, 31, prime_7919, prime_31, by norm_num⟩
  · exact ⟨7949, 17, prime_7949, prime_17, by norm_num⟩
  · exact ⟨7963, 11, prime_7963, prime_11, by norm_num⟩
  · exact ⟨7949, 19, prime_7949, prime_19, by norm_num⟩
  · exact ⟨7963, 13, prime_7963, prime_13, by norm_num⟩
  · exact ⟨7933, 29, prime_7933, prime_29, by norm_num⟩
  · exact ⟨7919, 37, prime_7919, prime_37, by norm_num⟩
  · exact ⟨7949, 23, prime_7949, prime_23, by norm_num⟩
  · exact ⟨7993, 2, prime_7993, prime_2, by norm_num⟩
  · exact ⟨7993, 3, prime_7993, prime_3, by norm_num⟩
  · exact ⟨7963, 19, prime_7963, prime_19, by norm_num⟩
  · exact ⟨7993, 5, prime_7993, prime_5, by norm_num⟩
  · exact ⟨7919, 43, prime_7919, prime_43, by norm_num⟩

private theorem lemoine_chunk_40 : ∀ k : ℕ, 4003 ≤ k → k ≤ 4102 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨7993, 7, prime_7993, prime_7, by norm_num⟩
  · exact ⟨7963, 23, prime_7963, prime_23, by norm_num⟩
  · exact ⟨7949, 31, prime_7949, prime_31, by norm_num⟩
  · exact ⟨8009, 2, prime_8009, prime_2, by norm_num⟩
  · exact ⟨8011, 2, prime_8011, prime_2, by norm_num⟩
  · exact ⟨8011, 3, prime_8011, prime_3, by norm_num⟩
  · exact ⟨8009, 5, prime_8009, prime_5, by norm_num⟩
  · exact ⟨8017, 2, prime_8017, prime_2, by norm_num⟩
  · exact ⟨8017, 3, prime_8017, prime_3, by norm_num⟩
  · exact ⟨8011, 7, prime_8011, prime_7, by norm_num⟩
  · exact ⟨8017, 5, prime_8017, prime_5, by norm_num⟩
  · exact ⟨7907, 61, prime_7907, prime_61, by norm_num⟩
  · exact ⟨8017, 7, prime_8017, prime_7, by norm_num⟩
  · exact ⟨8011, 11, prime_8011, prime_11, by norm_num⟩
  · exact ⟨8009, 13, prime_8009, prime_13, by norm_num⟩
  · exact ⟨8011, 13, prime_8011, prime_13, by norm_num⟩
  · exact ⟨8017, 11, prime_8017, prime_11, by norm_num⟩
  · exact ⟨7919, 61, prime_7919, prime_61, by norm_num⟩
  · exact ⟨8039, 2, prime_8039, prime_2, by norm_num⟩
  · exact ⟨8039, 3, prime_8039, prime_3, by norm_num⟩
  · exact ⟨8009, 19, prime_8009, prime_19, by norm_num⟩
  · exact ⟨8039, 5, prime_8039, prime_5, by norm_num⟩
  · exact ⟨8017, 17, prime_8017, prime_17, by norm_num⟩
  · exact ⟨8039, 7, prime_8039, prime_7, by norm_num⟩
  · exact ⟨8017, 19, prime_8017, prime_19, by norm_num⟩
  · exact ⟨8053, 2, prime_8053, prime_2, by norm_num⟩
  · exact ⟨8053, 3, prime_8053, prime_3, by norm_num⟩
  · exact ⟨8039, 11, prime_8039, prime_11, by norm_num⟩
  · exact ⟨8059, 2, prime_8059, prime_2, by norm_num⟩
  · exact ⟨8059, 3, prime_8059, prime_3, by norm_num⟩
  · exact ⟨8053, 7, prime_8053, prime_7, by norm_num⟩
  · exact ⟨8059, 5, prime_8059, prime_5, by norm_num⟩
  · exact ⟨8009, 31, prime_8009, prime_31, by norm_num⟩
  · exact ⟨8069, 2, prime_8069, prime_2, by norm_num⟩
  · exact ⟨8069, 3, prime_8069, prime_3, by norm_num⟩
  · exact ⟨8039, 19, prime_8039, prime_19, by norm_num⟩
  · exact ⟨8069, 5, prime_8069, prime_5, by norm_num⟩
  · exact ⟨8059, 11, prime_8059, prime_11, by norm_num⟩
  · exact ⟨8069, 7, prime_8069, prime_7, by norm_num⟩
  · exact ⟨8081, 2, prime_8081, prime_2, by norm_num⟩
  · exact ⟨8081, 3, prime_8081, prime_3, by norm_num⟩
  · exact ⟨7883, 103, prime_7883, prime_103, by norm_num⟩
  · exact ⟨8087, 2, prime_8087, prime_2, by norm_num⟩
  · exact ⟨8089, 2, prime_8089, prime_2, by norm_num⟩
  · exact ⟨8089, 3, prime_8089, prime_3, by norm_num⟩
  · exact ⟨8093, 2, prime_8093, prime_2, by norm_num⟩
  · exact ⟨8093, 3, prime_8093, prime_3, by norm_num⟩
  · exact ⟨8087, 7, prime_8087, prime_7, by norm_num⟩
  · exact ⟨8093, 5, prime_8093, prime_5, by norm_num⟩
  · exact ⟨8101, 2, prime_8101, prime_2, by norm_num⟩
  · exact ⟨8101, 3, prime_8101, prime_3, by norm_num⟩
  · exact ⟨8087, 11, prime_8087, prime_11, by norm_num⟩
  · exact ⟨8101, 5, prime_8101, prime_5, by norm_num⟩
  · exact ⟨8087, 13, prime_8087, prime_13, by norm_num⟩
  · exact ⟨8111, 2, prime_8111, prime_2, by norm_num⟩
  · exact ⟨8111, 3, prime_8111, prime_3, by norm_num⟩
  · exact ⟨8093, 13, prime_8093, prime_13, by norm_num⟩
  · exact ⟨8117, 2, prime_8117, prime_2, by norm_num⟩
  · exact ⟨8117, 3, prime_8117, prime_3, by norm_num⟩
  · exact ⟨8111, 7, prime_8111, prime_7, by norm_num⟩
  · exact ⟨8123, 2, prime_8123, prime_2, by norm_num⟩
  · exact ⟨8123, 3, prime_8123, prime_3, by norm_num⟩
  · exact ⟨8117, 7, prime_8117, prime_7, by norm_num⟩
  · exact ⟨8123, 5, prime_8123, prime_5, by norm_num⟩
  · exact ⟨8101, 17, prime_8101, prime_17, by norm_num⟩
  · exact ⟨8123, 7, prime_8123, prime_7, by norm_num⟩
  · exact ⟨8117, 11, prime_8117, prime_11, by norm_num⟩
  · exact ⟨8059, 41, prime_8059, prime_41, by norm_num⟩
  · exact ⟨8117, 13, prime_8117, prime_13, by norm_num⟩
  · exact ⟨8123, 11, prime_8123, prime_11, by norm_num⟩
  · exact ⟨8101, 23, prime_8101, prime_23, by norm_num⟩
  · exact ⟨8123, 13, prime_8123, prime_13, by norm_num⟩
  · exact ⟨8147, 2, prime_8147, prime_2, by norm_num⟩
  · exact ⟨8147, 3, prime_8147, prime_3, by norm_num⟩
  · exact ⟨8117, 19, prime_8117, prime_19, by norm_num⟩
  · exact ⟨8147, 5, prime_8147, prime_5, by norm_num⟩
  · exact ⟨8101, 29, prime_8101, prime_29, by norm_num⟩
  · exact ⟨8147, 7, prime_8147, prime_7, by norm_num⟩
  · exact ⟨8117, 23, prime_8117, prime_23, by norm_num⟩
  · exact ⟨8161, 2, prime_8161, prime_2, by norm_num⟩
  · exact ⟨8161, 3, prime_8161, prime_3, by norm_num⟩
  · exact ⟨8147, 11, prime_8147, prime_11, by norm_num⟩
  · exact ⟨8167, 2, prime_8167, prime_2, by norm_num⟩
  · exact ⟨8167, 3, prime_8167, prime_3, by norm_num⟩
  · exact ⟨8171, 2, prime_8171, prime_2, by norm_num⟩
  · exact ⟨8171, 3, prime_8171, prime_3, by norm_num⟩
  · exact ⟨8117, 31, prime_8117, prime_31, by norm_num⟩
  · exact ⟨8171, 5, prime_8171, prime_5, by norm_num⟩
  · exact ⟨8179, 2, prime_8179, prime_2, by norm_num⟩
  · exact ⟨8179, 3, prime_8179, prime_3, by norm_num⟩
  · exact ⟨8161, 13, prime_8161, prime_13, by norm_num⟩
  · exact ⟨8179, 5, prime_8179, prime_5, by norm_num⟩
  · exact ⟨8117, 37, prime_8117, prime_37, by norm_num⟩
  · exact ⟨8179, 7, prime_8179, prime_7, by norm_num⟩
  · exact ⟨8191, 2, prime_8191, prime_2, by norm_num⟩
  · exact ⟨8191, 3, prime_8191, prime_3, by norm_num⟩
  · exact ⟨8161, 19, prime_8161, prime_19, by norm_num⟩
  · exact ⟨8191, 5, prime_8191, prime_5, by norm_num⟩
  · exact ⟨8117, 43, prime_8117, prime_43, by norm_num⟩
  · exact ⟨8191, 7, prime_8191, prime_7, by norm_num⟩

private theorem lemoine_chunk_41 : ∀ k : ℕ, 4103 ≤ k → k ≤ 4202 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨8161, 23, prime_8161, prime_23, by norm_num⟩
  · exact ⟨8171, 19, prime_8171, prime_19, by norm_num⟩
  · exact ⟨8117, 47, prime_8117, prime_47, by norm_num⟩
  · exact ⟨8209, 2, prime_8209, prime_2, by norm_num⟩
  · exact ⟨8209, 3, prime_8209, prime_3, by norm_num⟩
  · exact ⟨8191, 13, prime_8191, prime_13, by norm_num⟩
  · exact ⟨8209, 5, prime_8209, prime_5, by norm_num⟩
  · exact ⟨8147, 37, prime_8147, prime_37, by norm_num⟩
  · exact ⟨8219, 2, prime_8219, prime_2, by norm_num⟩
  · exact ⟨8221, 2, prime_8221, prime_2, by norm_num⟩
  · exact ⟨8221, 3, prime_8221, prime_3, by norm_num⟩
  · exact ⟨8219, 5, prime_8219, prime_5, by norm_num⟩
  · exact ⟨8221, 5, prime_8221, prime_5, by norm_num⟩
  · exact ⟨8219, 7, prime_8219, prime_7, by norm_num⟩
  · exact ⟨8231, 2, prime_8231, prime_2, by norm_num⟩
  · exact ⟨8233, 2, prime_8233, prime_2, by norm_num⟩
  · exact ⟨8233, 3, prime_8233, prime_3, by norm_num⟩
  · exact ⟨8237, 2, prime_8237, prime_2, by norm_num⟩
  · exact ⟨8237, 3, prime_8237, prime_3, by norm_num⟩
  · exact ⟨8231, 7, prime_8231, prime_7, by norm_num⟩
  · exact ⟨8243, 2, prime_8243, prime_2, by norm_num⟩
  · exact ⟨8243, 3, prime_8243, prime_3, by norm_num⟩
  · exact ⟨8237, 7, prime_8237, prime_7, by norm_num⟩
  · exact ⟨8243, 5, prime_8243, prime_5, by norm_num⟩
  · exact ⟨8233, 11, prime_8233, prime_11, by norm_num⟩
  · exact ⟨8243, 7, prime_8243, prime_7, by norm_num⟩
  · exact ⟨8237, 11, prime_8237, prime_11, by norm_num⟩
  · exact ⟨8179, 41, prime_8179, prime_41, by norm_num⟩
  · exact ⟨8237, 13, prime_8237, prime_13, by norm_num⟩
  · exact ⟨8243, 11, prime_8243, prime_11, by norm_num⟩
  · exact ⟨8263, 2, prime_8263, prime_2, by norm_num⟩
  · exact ⟨8263, 3, prime_8263, prime_3, by norm_num⟩
  · exact ⟨8237, 17, prime_8237, prime_17, by norm_num⟩
  · exact ⟨8269, 2, prime_8269, prime_2, by norm_num⟩
  · exact ⟨8269, 3, prime_8269, prime_3, by norm_num⟩
  · exact ⟨8273, 2, prime_8273, prime_2, by norm_num⟩
  · exact ⟨8273, 3, prime_8273, prime_3, by norm_num⟩
  · exact ⟨8243, 19, prime_8243, prime_19, by norm_num⟩
  · exact ⟨8273, 5, prime_8273, prime_5, by norm_num⟩
  · exact ⟨8263, 11, prime_8263, prime_11, by norm_num⟩
  · exact ⟨8273, 7, prime_8273, prime_7, by norm_num⟩
  · exact ⟨8263, 13, prime_8263, prime_13, by norm_num⟩
  · exact ⟨8287, 2, prime_8287, prime_2, by norm_num⟩
  · exact ⟨8287, 3, prime_8287, prime_3, by norm_num⟩
  · exact ⟨8291, 2, prime_8291, prime_2, by norm_num⟩
  · exact ⟨8293, 2, prime_8293, prime_2, by norm_num⟩
  · exact ⟨8293, 3, prime_8293, prime_3, by norm_num⟩
  · exact ⟨8297, 2, prime_8297, prime_2, by norm_num⟩
  · exact ⟨8297, 3, prime_8297, prime_3, by norm_num⟩
  · exact ⟨8291, 7, prime_8291, prime_7, by norm_num⟩
  · exact ⟨8297, 5, prime_8297, prime_5, by norm_num⟩
  · exact ⟨8287, 11, prime_8287, prime_11, by norm_num⟩
  · exact ⟨8297, 7, prime_8297, prime_7, by norm_num⟩
  · exact ⟨8291, 11, prime_8291, prime_11, by norm_num⟩
  · exact ⟨8311, 2, prime_8311, prime_2, by norm_num⟩
  · exact ⟨8311, 3, prime_8311, prime_3, by norm_num⟩
  · exact ⟨8297, 11, prime_8297, prime_11, by norm_num⟩
  · exact ⟨8317, 2, prime_8317, prime_2, by norm_num⟩
  · exact ⟨8317, 3, prime_8317, prime_3, by norm_num⟩
  · exact ⟨8311, 7, prime_8311, prime_7, by norm_num⟩
  · exact ⟨8317, 5, prime_8317, prime_5, by norm_num⟩
  · exact ⟨8291, 19, prime_8291, prime_19, by norm_num⟩
  · exact ⟨8317, 7, prime_8317, prime_7, by norm_num⟩
  · exact ⟨8329, 2, prime_8329, prime_2, by norm_num⟩
  · exact ⟨8329, 3, prime_8329, prime_3, by norm_num⟩
  · exact ⟨8311, 13, prime_8311, prime_13, by norm_num⟩
  · exact ⟨8329, 5, prime_8329, prime_5, by norm_num⟩
  · exact ⟨8219, 61, prime_8219, prime_61, by norm_num⟩
  · exact ⟨8329, 7, prime_8329, prime_7, by norm_num⟩
  · exact ⟨8311, 17, prime_8311, prime_17, by norm_num⟩
  · exact ⟨8273, 37, prime_8273, prime_37, by norm_num⟩
  · exact ⟨8311, 19, prime_8311, prime_19, by norm_num⟩
  · exact ⟨8329, 11, prime_8329, prime_11, by norm_num⟩
  · exact ⟨8291, 31, prime_8291, prime_31, by norm_num⟩
  · exact ⟨8329, 13, prime_8329, prime_13, by norm_num⟩
  · exact ⟨8353, 2, prime_8353, prime_2, by norm_num⟩
  · exact ⟨8353, 3, prime_8353, prime_3, by norm_num⟩
  · exact ⟨8287, 37, prime_8287, prime_37, by norm_num⟩
  · exact ⟨8353, 5, prime_8353, prime_5, by norm_num⟩
  · exact ⟨8291, 37, prime_8291, prime_37, by norm_num⟩
  · exact ⟨8363, 2, prime_8363, prime_2, by norm_num⟩
  · exact ⟨8363, 3, prime_8363, prime_3, by norm_num⟩
  · exact ⟨8297, 37, prime_8297, prime_37, by norm_num⟩
  · exact ⟨8369, 2, prime_8369, prime_2, by norm_num⟩
  · exact ⟨8369, 3, prime_8369, prime_3, by norm_num⟩
  · exact ⟨8363, 7, prime_8363, prime_7, by norm_num⟩
  · exact ⟨8369, 5, prime_8369, prime_5, by norm_num⟩
  · exact ⟨8377, 2, prime_8377, prime_2, by norm_num⟩
  · exact ⟨8377, 3, prime_8377, prime_3, by norm_num⟩
  · exact ⟨8363, 11, prime_8363, prime_11, by norm_num⟩
  · exact ⟨8377, 5, prime_8377, prime_5, by norm_num⟩
  · exact ⟨8363, 13, prime_8363, prime_13, by norm_num⟩
  · exact ⟨8387, 2, prime_8387, prime_2, by norm_num⟩
  · exact ⟨8389, 2, prime_8389, prime_2, by norm_num⟩
  · exact ⟨8389, 3, prime_8389, prime_3, by norm_num⟩
  · exact ⟨8387, 5, prime_8387, prime_5, by norm_num⟩
  · exact ⟨8389, 5, prime_8389, prime_5, by norm_num⟩
  · exact ⟨8387, 7, prime_8387, prime_7, by norm_num⟩
  · exact ⟨8389, 7, prime_8389, prime_7, by norm_num⟩
  · exact ⟨8311, 47, prime_8311, prime_47, by norm_num⟩

private theorem lemoine_chunk_42 : ∀ k : ℕ, 4203 ≤ k → k ≤ 4302 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨8369, 19, prime_8369, prime_19, by norm_num⟩
  · exact ⟨8387, 11, prime_8387, prime_11, by norm_num⟩
  · exact ⟨8389, 11, prime_8389, prime_11, by norm_num⟩
  · exact ⟨8387, 13, prime_8387, prime_13, by norm_num⟩
  · exact ⟨8389, 13, prime_8389, prime_13, by norm_num⟩
  · exact ⟨8311, 53, prime_8311, prime_53, by norm_num⟩
  · exact ⟨8297, 61, prime_8297, prime_61, by norm_num⟩
  · exact ⟨8387, 17, prime_8387, prime_17, by norm_num⟩
  · exact ⟨8419, 2, prime_8419, prime_2, by norm_num⟩
  · exact ⟨8419, 3, prime_8419, prime_3, by norm_num⟩
  · exact ⟨8423, 2, prime_8423, prime_2, by norm_num⟩
  · exact ⟨8423, 3, prime_8423, prime_3, by norm_num⟩
  · exact ⟨8369, 31, prime_8369, prime_31, by norm_num⟩
  · exact ⟨8429, 2, prime_8429, prime_2, by norm_num⟩
  · exact ⟨8431, 2, prime_8431, prime_2, by norm_num⟩
  · exact ⟨8431, 3, prime_8431, prime_3, by norm_num⟩
  · exact ⟨8429, 5, prime_8429, prime_5, by norm_num⟩
  · exact ⟨8431, 5, prime_8431, prime_5, by norm_num⟩
  · exact ⟨8429, 7, prime_8429, prime_7, by norm_num⟩
  · exact ⟨8431, 7, prime_8431, prime_7, by norm_num⟩
  · exact ⟨8443, 2, prime_8443, prime_2, by norm_num⟩
  · exact ⟨8443, 3, prime_8443, prime_3, by norm_num⟩
  · exact ⟨8447, 2, prime_8447, prime_2, by norm_num⟩
  · exact ⟨8447, 3, prime_8447, prime_3, by norm_num⟩
  · exact ⟨8429, 13, prime_8429, prime_13, by norm_num⟩
  · exact ⟨8447, 5, prime_8447, prime_5, by norm_num⟩
  · exact ⟨8377, 41, prime_8377, prime_41, by norm_num⟩
  · exact ⟨8447, 7, prime_8447, prime_7, by norm_num⟩
  · exact ⟨8429, 17, prime_8429, prime_17, by norm_num⟩
  · exact ⟨8461, 2, prime_8461, prime_2, by norm_num⟩
  · exact ⟨8461, 3, prime_8461, prime_3, by norm_num⟩
  · exact ⟨8447, 11, prime_8447, prime_11, by norm_num⟩
  · exact ⟨8467, 2, prime_8467, prime_2, by norm_num⟩
  · exact ⟨8467, 3, prime_8467, prime_3, by norm_num⟩
  · exact ⟨8461, 7, prime_8461, prime_7, by norm_num⟩
  · exact ⟨8467, 5, prime_8467, prime_5, by norm_num⟩
  · exact ⟨8273, 103, prime_8273, prime_103, by norm_num⟩
  · exact ⟨8467, 7, prime_8467, prime_7, by norm_num⟩
  · exact ⟨8461, 11, prime_8461, prime_11, by norm_num⟩
  · exact ⟨8447, 19, prime_8447, prime_19, by norm_num⟩
  · exact ⟨8461, 13, prime_8461, prime_13, by norm_num⟩
  · exact ⟨8467, 11, prime_8467, prime_11, by norm_num⟩
  · exact ⟨8429, 31, prime_8429, prime_31, by norm_num⟩
  · exact ⟨8467, 13, prime_8467, prime_13, by norm_num⟩
  · exact ⟨8461, 17, prime_8461, prime_17, by norm_num⟩
  · exact ⟨8423, 37, prime_8423, prime_37, by norm_num⟩
  · exact ⟨8461, 19, prime_8461, prime_19, by norm_num⟩
  · exact ⟨8467, 17, prime_8467, prime_17, by norm_num⟩
  · exact ⟨8429, 37, prime_8429, prime_37, by norm_num⟩
  · exact ⟨8501, 2, prime_8501, prime_2, by norm_num⟩
  · exact ⟨8501, 3, prime_8501, prime_3, by norm_num⟩
  · exact ⟨8447, 31, prime_8447, prime_31, by norm_num⟩
  · exact ⟨8501, 5, prime_8501, prime_5, by norm_num⟩
  · exact ⟨8467, 23, prime_8467, prime_23, by norm_num⟩
  · exact ⟨8501, 7, prime_8501, prime_7, by norm_num⟩
  · exact ⟨8513, 2, prime_8513, prime_2, by norm_num⟩
  · exact ⟨8513, 3, prime_8513, prime_3, by norm_num⟩
  · exact ⟨8447, 37, prime_8447, prime_37, by norm_num⟩
  · exact ⟨8513, 5, prime_8513, prime_5, by norm_num⟩
  · exact ⟨8521, 2, prime_8521, prime_2, by norm_num⟩
  · exact ⟨8521, 3, prime_8521, prime_3, by norm_num⟩
  · exact ⟨8467, 31, prime_8467, prime_31, by norm_num⟩
  · exact ⟨8527, 2, prime_8527, prime_2, by norm_num⟩
  · exact ⟨8527, 3, prime_8527, prime_3, by norm_num⟩
  · exact ⟨8521, 7, prime_8521, prime_7, by norm_num⟩
  · exact ⟨8527, 5, prime_8527, prime_5, by norm_num⟩
  · exact ⟨8513, 13, prime_8513, prime_13, by norm_num⟩
  · exact ⟨8537, 2, prime_8537, prime_2, by norm_num⟩
  · exact ⟨8539, 2, prime_8539, prime_2, by norm_num⟩
  · exact ⟨8539, 3, prime_8539, prime_3, by norm_num⟩
  · exact ⟨8543, 2, prime_8543, prime_2, by norm_num⟩
  · exact ⟨8543, 3, prime_8543, prime_3, by norm_num⟩
  · exact ⟨8537, 7, prime_8537, prime_7, by norm_num⟩
  · exact ⟨8543, 5, prime_8543, prime_5, by norm_num⟩
  · exact ⟨8521, 17, prime_8521, prime_17, by norm_num⟩
  · exact ⟨8543, 7, prime_8543, prime_7, by norm_num⟩
  · exact ⟨8537, 11, prime_8537, prime_11, by norm_num⟩
  · exact ⟨8539, 11, prime_8539, prime_11, by norm_num⟩
  · exact ⟨8537, 13, prime_8537, prime_13, by norm_num⟩
  · exact ⟨8543, 11, prime_8543, prime_11, by norm_num⟩
  · exact ⟨8563, 2, prime_8563, prime_2, by norm_num⟩
  · exact ⟨8563, 3, prime_8563, prime_3, by norm_num⟩
  · exact ⟨8537, 17, prime_8537, prime_17, by norm_num⟩
  · exact ⟨8563, 5, prime_8563, prime_5, by norm_num⟩
  · exact ⟨8537, 19, prime_8537, prime_19, by norm_num⟩
  · exact ⟨8573, 2, prime_8573, prime_2, by norm_num⟩
  · exact ⟨8573, 3, prime_8573, prime_3, by norm_num⟩
  · exact ⟨8543, 19, prime_8543, prime_19, by norm_num⟩
  · exact ⟨8573, 5, prime_8573, prime_5, by norm_num⟩
  · exact ⟨8581, 2, prime_8581, prime_2, by norm_num⟩
  · exact ⟨8581, 3, prime_8581, prime_3, by norm_num⟩
  · exact ⟨8563, 13, prime_8563, prime_13, by norm_num⟩
  · exact ⟨8581, 5, prime_8581, prime_5, by norm_num⟩
  · exact ⟨8447, 73, prime_8447, prime_73, by norm_num⟩
  · exact ⟨8581, 7, prime_8581, prime_7, by norm_num⟩
  · exact ⟨8563, 17, prime_8563, prime_17, by norm_num⟩
  · exact ⟨8573, 13, prime_8573, prime_13, by norm_num⟩
  · exact ⟨8597, 2, prime_8597, prime_2, by norm_num⟩
  · exact ⟨8599, 2, prime_8599, prime_2, by norm_num⟩
  · exact ⟨8599, 3, prime_8599, prime_3, by norm_num⟩

private theorem lemoine_chunk_43 : ∀ k : ℕ, 4303 ≤ k → k ≤ 4402 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨8597, 5, prime_8597, prime_5, by norm_num⟩
  · exact ⟨8599, 5, prime_8599, prime_5, by norm_num⟩
  · exact ⟨8597, 7, prime_8597, prime_7, by norm_num⟩
  · exact ⟨8609, 2, prime_8609, prime_2, by norm_num⟩
  · exact ⟨8609, 3, prime_8609, prime_3, by norm_num⟩
  · exact ⟨8543, 37, prime_8543, prime_37, by norm_num⟩
  · exact ⟨8609, 5, prime_8609, prime_5, by norm_num⟩
  · exact ⟨8599, 11, prime_8599, prime_11, by norm_num⟩
  · exact ⟨8609, 7, prime_8609, prime_7, by norm_num⟩
  · exact ⟨8599, 13, prime_8599, prime_13, by norm_num⟩
  · exact ⟨8623, 2, prime_8623, prime_2, by norm_num⟩
  · exact ⟨8623, 3, prime_8623, prime_3, by norm_num⟩
  · exact ⟨8627, 2, prime_8627, prime_2, by norm_num⟩
  · exact ⟨8629, 2, prime_8629, prime_2, by norm_num⟩
  · exact ⟨8629, 3, prime_8629, prime_3, by norm_num⟩
  · exact ⟨8627, 5, prime_8627, prime_5, by norm_num⟩
  · exact ⟨8629, 5, prime_8629, prime_5, by norm_num⟩
  · exact ⟨8627, 7, prime_8627, prime_7, by norm_num⟩
  · exact ⟨8629, 7, prime_8629, prime_7, by norm_num⟩
  · exact ⟨8641, 2, prime_8641, prime_2, by norm_num⟩
  · exact ⟨8641, 3, prime_8641, prime_3, by norm_num⟩
  · exact ⟨8627, 11, prime_8627, prime_11, by norm_num⟩
  · exact ⟨8647, 2, prime_8647, prime_2, by norm_num⟩
  · exact ⟨8647, 3, prime_8647, prime_3, by norm_num⟩
  · exact ⟨8641, 7, prime_8641, prime_7, by norm_num⟩
  · exact ⟨8647, 5, prime_8647, prime_5, by norm_num⟩
  · exact ⟨8597, 31, prime_8597, prime_31, by norm_num⟩
  · exact ⟨8647, 7, prime_8647, prime_7, by norm_num⟩
  · exact ⟨8641, 11, prime_8641, prime_11, by norm_num⟩
  · exact ⟨8627, 19, prime_8627, prime_19, by norm_num⟩
  · exact ⟨8663, 2, prime_8663, prime_2, by norm_num⟩
  · exact ⟨8663, 3, prime_8663, prime_3, by norm_num⟩
  · exact ⟨8609, 31, prime_8609, prime_31, by norm_num⟩
  · exact ⟨8669, 2, prime_8669, prime_2, by norm_num⟩
  · exact ⟨8669, 3, prime_8669, prime_3, by norm_num⟩
  · exact ⟨8663, 7, prime_8663, prime_7, by norm_num⟩
  · exact ⟨8669, 5, prime_8669, prime_5, by norm_num⟩
  · exact ⟨8677, 2, prime_8677, prime_2, by norm_num⟩
  · exact ⟨8677, 3, prime_8677, prime_3, by norm_num⟩
  · exact ⟨8681, 2, prime_8681, prime_2, by norm_num⟩
  · exact ⟨8681, 3, prime_8681, prime_3, by norm_num⟩
  · exact ⟨8663, 13, prime_8663, prime_13, by norm_num⟩
  · exact ⟨8681, 5, prime_8681, prime_5, by norm_num⟩
  · exact ⟨8689, 2, prime_8689, prime_2, by norm_num⟩
  · exact ⟨8689, 3, prime_8689, prime_3, by norm_num⟩
  · exact ⟨8693, 2, prime_8693, prime_2, by norm_num⟩
  · exact ⟨8693, 3, prime_8693, prime_3, by norm_num⟩
  · exact ⟨8663, 19, prime_8663, prime_19, by norm_num⟩
  · exact ⟨8699, 2, prime_8699, prime_2, by norm_num⟩
  · exact ⟨8699, 3, prime_8699, prime_3, by norm_num⟩
  · exact ⟨8693, 7, prime_8693, prime_7, by norm_num⟩
  · exact ⟨8699, 5, prime_8699, prime_5, by norm_num⟩
  · exact ⟨8707, 2, prime_8707, prime_2, by norm_num⟩
  · exact ⟨8707, 3, prime_8707, prime_3, by norm_num⟩
  · exact ⟨8693, 11, prime_8693, prime_11, by norm_num⟩
  · exact ⟨8713, 2, prime_8713, prime_2, by norm_num⟩
  · exact ⟨8713, 3, prime_8713, prime_3, by norm_num⟩
  · exact ⟨8707, 7, prime_8707, prime_7, by norm_num⟩
  · exact ⟨8719, 2, prime_8719, prime_2, by norm_num⟩
  · exact ⟨8719, 3, prime_8719, prime_3, by norm_num⟩
  · exact ⟨8713, 7, prime_8713, prime_7, by norm_num⟩
  · exact ⟨8719, 5, prime_8719, prime_5, by norm_num⟩
  · exact ⟨8693, 19, prime_8693, prime_19, by norm_num⟩
  · exact ⟨8719, 7, prime_8719, prime_7, by norm_num⟩
  · exact ⟨8731, 2, prime_8731, prime_2, by norm_num⟩
  · exact ⟨8731, 3, prime_8731, prime_3, by norm_num⟩
  · exact ⟨8713, 13, prime_8713, prime_13, by norm_num⟩
  · exact ⟨8737, 2, prime_8737, prime_2, by norm_num⟩
  · exact ⟨8737, 3, prime_8737, prime_3, by norm_num⟩
  · exact ⟨8741, 2, prime_8741, prime_2, by norm_num⟩
  · exact ⟨8741, 3, prime_8741, prime_3, by norm_num⟩
  · exact ⟨8663, 43, prime_8663, prime_43, by norm_num⟩
  · exact ⟨8747, 2, prime_8747, prime_2, by norm_num⟩
  · exact ⟨8747, 3, prime_8747, prime_3, by norm_num⟩
  · exact ⟨8741, 7, prime_8741, prime_7, by norm_num⟩
  · exact ⟨8753, 2, prime_8753, prime_2, by norm_num⟩
  · exact ⟨8753, 3, prime_8753, prime_3, by norm_num⟩
  · exact ⟨8747, 7, prime_8747, prime_7, by norm_num⟩
  · exact ⟨8753, 5, prime_8753, prime_5, by norm_num⟩
  · exact ⟨8761, 2, prime_8761, prime_2, by norm_num⟩
  · exact ⟨8761, 3, prime_8761, prime_3, by norm_num⟩
  · exact ⟨8747, 11, prime_8747, prime_11, by norm_num⟩
  · exact ⟨8761, 5, prime_8761, prime_5, by norm_num⟩
  · exact ⟨8747, 13, prime_8747, prime_13, by norm_num⟩
  · exact ⟨8761, 7, prime_8761, prime_7, by norm_num⟩
  · exact ⟨8731, 23, prime_8731, prime_23, by norm_num⟩
  · exact ⟨8753, 13, prime_8753, prime_13, by norm_num⟩
  · exact ⟨8747, 17, prime_8747, prime_17, by norm_num⟩
  · exact ⟨8779, 2, prime_8779, prime_2, by norm_num⟩
  · exact ⟨8779, 3, prime_8779, prime_3, by norm_num⟩
  · exact ⟨8783, 2, prime_8783, prime_2, by norm_num⟩
  · exact ⟨8783, 3, prime_8783, prime_3, by norm_num⟩
  · exact ⟨8753, 19, prime_8753, prime_19, by norm_num⟩
  · exact ⟨8783, 5, prime_8783, prime_5, by norm_num⟩
  · exact ⟨8761, 17, prime_8761, prime_17, by norm_num⟩
  · exact ⟨8783, 7, prime_8783, prime_7, by norm_num⟩
  · exact ⟨8761, 19, prime_8761, prime_19, by norm_num⟩
  · exact ⟨8779, 11, prime_8779, prime_11, by norm_num⟩
  · exact ⟨8741, 31, prime_8741, prime_31, by norm_num⟩
  · exact ⟨8783, 11, prime_8783, prime_11, by norm_num⟩

private theorem lemoine_chunk_44 : ∀ k : ℕ, 4403 ≤ k → k ≤ 4502 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨8803, 2, prime_8803, prime_2, by norm_num⟩
  · exact ⟨8803, 3, prime_8803, prime_3, by norm_num⟩
  · exact ⟨8807, 2, prime_8807, prime_2, by norm_num⟩
  · exact ⟨8807, 3, prime_8807, prime_3, by norm_num⟩
  · exact ⟨8753, 31, prime_8753, prime_31, by norm_num⟩
  · exact ⟨8807, 5, prime_8807, prime_5, by norm_num⟩
  · exact ⟨8761, 29, prime_8761, prime_29, by norm_num⟩
  · exact ⟨8807, 7, prime_8807, prime_7, by norm_num⟩
  · exact ⟨8819, 2, prime_8819, prime_2, by norm_num⟩
  · exact ⟨8821, 2, prime_8821, prime_2, by norm_num⟩
  · exact ⟨8821, 3, prime_8821, prime_3, by norm_num⟩
  · exact ⟨8819, 5, prime_8819, prime_5, by norm_num⟩
  · exact ⟨8821, 5, prime_8821, prime_5, by norm_num⟩
  · exact ⟨8819, 7, prime_8819, prime_7, by norm_num⟩
  · exact ⟨8831, 2, prime_8831, prime_2, by norm_num⟩
  · exact ⟨8831, 3, prime_8831, prime_3, by norm_num⟩
  · exact ⟨8753, 43, prime_8753, prime_43, by norm_num⟩
  · exact ⟨8837, 2, prime_8837, prime_2, by norm_num⟩
  · exact ⟨8839, 2, prime_8839, prime_2, by norm_num⟩
  · exact ⟨8839, 3, prime_8839, prime_3, by norm_num⟩
  · exact ⟨8837, 5, prime_8837, prime_5, by norm_num⟩
  · exact ⟨8839, 5, prime_8839, prime_5, by norm_num⟩
  · exact ⟨8837, 7, prime_8837, prime_7, by norm_num⟩
  · exact ⟨8849, 2, prime_8849, prime_2, by norm_num⟩
  · exact ⟨8849, 3, prime_8849, prime_3, by norm_num⟩
  · exact ⟨8831, 13, prime_8831, prime_13, by norm_num⟩
  · exact ⟨8849, 5, prime_8849, prime_5, by norm_num⟩
  · exact ⟨8839, 11, prime_8839, prime_11, by norm_num⟩
  · exact ⟨8849, 7, prime_8849, prime_7, by norm_num⟩
  · exact ⟨8861, 2, prime_8861, prime_2, by norm_num⟩
  · exact ⟨8863, 2, prime_8863, prime_2, by norm_num⟩
  · exact ⟨8863, 3, prime_8863, prime_3, by norm_num⟩
  · exact ⟨8867, 2, prime_8867, prime_2, by norm_num⟩
  · exact ⟨8867, 3, prime_8867, prime_3, by norm_num⟩
  · exact ⟨8861, 7, prime_8861, prime_7, by norm_num⟩
  · exact ⟨8867, 5, prime_8867, prime_5, by norm_num⟩
  · exact ⟨8821, 29, prime_8821, prime_29, by norm_num⟩
  · exact ⟨8867, 7, prime_8867, prime_7, by norm_num⟩
  · exact ⟨8861, 11, prime_8861, prime_11, by norm_num⟩
  · exact ⟨8863, 11, prime_8863, prime_11, by norm_num⟩
  · exact ⟨8861, 13, prime_8861, prime_13, by norm_num⟩
  · exact ⟨8867, 11, prime_8867, prime_11, by norm_num⟩
  · exact ⟨8887, 2, prime_8887, prime_2, by norm_num⟩
  · exact ⟨8887, 3, prime_8887, prime_3, by norm_num⟩
  · exact ⟨8861, 17, prime_8861, prime_17, by norm_num⟩
  · exact ⟨8893, 2, prime_8893, prime_2, by norm_num⟩
  · exact ⟨8893, 3, prime_8893, prime_3, by norm_num⟩
  · exact ⟨8887, 7, prime_8887, prime_7, by norm_num⟩
  · exact ⟨8893, 5, prime_8893, prime_5, by norm_num⟩
  · exact ⟨8867, 19, prime_8867, prime_19, by norm_num⟩
  · exact ⟨8893, 7, prime_8893, prime_7, by norm_num⟩
  · exact ⟨8887, 11, prime_8887, prime_11, by norm_num⟩
  · exact ⟨8849, 31, prime_8849, prime_31, by norm_num⟩
  · exact ⟨8887, 13, prime_8887, prime_13, by norm_num⟩
  · exact ⟨8893, 11, prime_8893, prime_11, by norm_num⟩
  · exact ⟨8831, 43, prime_8831, prime_43, by norm_num⟩
  · exact ⟨8893, 13, prime_8893, prime_13, by norm_num⟩
  · exact ⟨8887, 17, prime_8887, prime_17, by norm_num⟩
  · exact ⟨8861, 31, prime_8861, prime_31, by norm_num⟩
  · exact ⟨8887, 19, prime_8887, prime_19, by norm_num⟩
  · exact ⟨8923, 2, prime_8923, prime_2, by norm_num⟩
  · exact ⟨8923, 3, prime_8923, prime_3, by norm_num⟩
  · exact ⟨8893, 19, prime_8893, prime_19, by norm_num⟩
  · exact ⟨8929, 2, prime_8929, prime_2, by norm_num⟩
  · exact ⟨8929, 3, prime_8929, prime_3, by norm_num⟩
  · exact ⟨8933, 2, prime_8933, prime_2, by norm_num⟩
  · exact ⟨8933, 3, prime_8933, prime_3, by norm_num⟩
  · exact ⟨8867, 37, prime_8867, prime_37, by norm_num⟩
  · exact ⟨8933, 5, prime_8933, prime_5, by norm_num⟩
  · exact ⟨8941, 2, prime_8941, prime_2, by norm_num⟩
  · exact ⟨8941, 3, prime_8941, prime_3, by norm_num⟩
  · exact ⟨8923, 13, prime_8923, prime_13, by norm_num⟩
  · exact ⟨8941, 5, prime_8941, prime_5, by norm_num⟩
  · exact ⟨8867, 43, prime_8867, prime_43, by norm_num⟩
  · exact ⟨8951, 2, prime_8951, prime_2, by norm_num⟩
  · exact ⟨8951, 3, prime_8951, prime_3, by norm_num⟩
  · exact ⟨8933, 13, prime_8933, prime_13, by norm_num⟩
  · exact ⟨8951, 5, prime_8951, prime_5, by norm_num⟩
  · exact ⟨8941, 11, prime_8941, prime_11, by norm_num⟩
  · exact ⟨8951, 7, prime_8951, prime_7, by norm_num⟩
  · exact ⟨8963, 2, prime_8963, prime_2, by norm_num⟩
  · exact ⟨8963, 3, prime_8963, prime_3, by norm_num⟩
  · exact ⟨8933, 19, prime_8933, prime_19, by norm_num⟩
  · exact ⟨8969, 2, prime_8969, prime_2, by norm_num⟩
  · exact ⟨8971, 2, prime_8971, prime_2, by norm_num⟩
  · exact ⟨8971, 3, prime_8971, prime_3, by norm_num⟩
  · exact ⟨8969, 5, prime_8969, prime_5, by norm_num⟩
  · exact ⟨8971, 5, prime_8971, prime_5, by norm_num⟩
  · exact ⟨8969, 7, prime_8969, prime_7, by norm_num⟩
  · exact ⟨8971, 7, prime_8971, prime_7, by norm_num⟩
  · exact ⟨8941, 23, prime_8941, prime_23, by norm_num⟩
  · exact ⟨8963, 13, prime_8963, prime_13, by norm_num⟩
  · exact ⟨8969, 11, prime_8969, prime_11, by norm_num⟩
  · exact ⟨8971, 11, prime_8971, prime_11, by norm_num⟩
  · exact ⟨8969, 13, prime_8969, prime_13, by norm_num⟩
  · exact ⟨8971, 13, prime_8971, prime_13, by norm_num⟩
  · exact ⟨8941, 29, prime_8941, prime_29, by norm_num⟩
  · exact ⟨8963, 19, prime_8963, prime_19, by norm_num⟩
  · exact ⟨8999, 2, prime_8999, prime_2, by norm_num⟩
  · exact ⟨9001, 2, prime_9001, prime_2, by norm_num⟩

private theorem lemoine_chunk_45 : ∀ k : ℕ, 4503 ≤ k → k ≤ 4602 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨9001, 3, prime_9001, prime_3, by norm_num⟩
  · exact ⟨8999, 5, prime_8999, prime_5, by norm_num⟩
  · exact ⟨9007, 2, prime_9007, prime_2, by norm_num⟩
  · exact ⟨9007, 3, prime_9007, prime_3, by norm_num⟩
  · exact ⟨9011, 2, prime_9011, prime_2, by norm_num⟩
  · exact ⟨9013, 2, prime_9013, prime_2, by norm_num⟩
  · exact ⟨9013, 3, prime_9013, prime_3, by norm_num⟩
  · exact ⟨9011, 5, prime_9011, prime_5, by norm_num⟩
  · exact ⟨9013, 5, prime_9013, prime_5, by norm_num⟩
  · exact ⟨9011, 7, prime_9011, prime_7, by norm_num⟩
  · exact ⟨9013, 7, prime_9013, prime_7, by norm_num⟩
  · exact ⟨9007, 11, prime_9007, prime_11, by norm_num⟩
  · exact ⟨8969, 31, prime_8969, prime_31, by norm_num⟩
  · exact ⟨9029, 2, prime_9029, prime_2, by norm_num⟩
  · exact ⟨9029, 3, prime_9029, prime_3, by norm_num⟩
  · exact ⟨9011, 13, prime_9011, prime_13, by norm_num⟩
  · exact ⟨9029, 5, prime_9029, prime_5, by norm_num⟩
  · exact ⟨9007, 17, prime_9007, prime_17, by norm_num⟩
  · exact ⟨9029, 7, prime_9029, prime_7, by norm_num⟩
  · exact ⟨9041, 2, prime_9041, prime_2, by norm_num⟩
  · exact ⟨9043, 2, prime_9043, prime_2, by norm_num⟩
  · exact ⟨9043, 3, prime_9043, prime_3, by norm_num⟩
  · exact ⟨9041, 5, prime_9041, prime_5, by norm_num⟩
  · exact ⟨9049, 2, prime_9049, prime_2, by norm_num⟩
  · exact ⟨9049, 3, prime_9049, prime_3, by norm_num⟩
  · exact ⟨9043, 7, prime_9043, prime_7, by norm_num⟩
  · exact ⟨9049, 5, prime_9049, prime_5, by norm_num⟩
  · exact ⟨8999, 31, prime_8999, prime_31, by norm_num⟩
  · exact ⟨9059, 2, prime_9059, prime_2, by norm_num⟩
  · exact ⟨9059, 3, prime_9059, prime_3, by norm_num⟩
  · exact ⟨9041, 13, prime_9041, prime_13, by norm_num⟩
  · exact ⟨9059, 5, prime_9059, prime_5, by norm_num⟩
  · exact ⟨9067, 2, prime_9067, prime_2, by norm_num⟩
  · exact ⟨9067, 3, prime_9067, prime_3, by norm_num⟩
  · exact ⟨9049, 13, prime_9049, prime_13, by norm_num⟩
  · exact ⟨9067, 5, prime_9067, prime_5, by norm_num⟩
  · exact ⟨9041, 19, prime_9041, prime_19, by norm_num⟩
  · exact ⟨9067, 7, prime_9067, prime_7, by norm_num⟩
  · exact ⟨9049, 17, prime_9049, prime_17, by norm_num⟩
  · exact ⟨9059, 13, prime_9059, prime_13, by norm_num⟩
  · exact ⟨9049, 19, prime_9049, prime_19, by norm_num⟩
  · exact ⟨9067, 11, prime_9067, prime_11, by norm_num⟩
  · exact ⟨9029, 31, prime_9029, prime_31, by norm_num⟩
  · exact ⟨9067, 13, prime_9067, prime_13, by norm_num⟩
  · exact ⟨9091, 2, prime_9091, prime_2, by norm_num⟩
  · exact ⟨9091, 3, prime_9091, prime_3, by norm_num⟩
  · exact ⟨9041, 29, prime_9041, prime_29, by norm_num⟩
  · exact ⟨9091, 5, prime_9091, prime_5, by norm_num⟩
  · exact ⟨9041, 31, prime_9041, prime_31, by norm_num⟩
  · exact ⟨9091, 7, prime_9091, prime_7, by norm_num⟩
  · exact ⟨9103, 2, prime_9103, prime_2, by norm_num⟩
  · exact ⟨9103, 3, prime_9103, prime_3, by norm_num⟩
  · exact ⟨9049, 31, prime_9049, prime_31, by norm_num⟩
  · exact ⟨9109, 2, prime_9109, prime_2, by norm_num⟩
  · exact ⟨9109, 3, prime_9109, prime_3, by norm_num⟩
  · exact ⟨9103, 7, prime_9103, prime_7, by norm_num⟩
  · exact ⟨9109, 5, prime_9109, prime_5, by norm_num⟩
  · exact ⟨9059, 31, prime_9059, prime_31, by norm_num⟩
  · exact ⟨9109, 7, prime_9109, prime_7, by norm_num⟩
  · exact ⟨9103, 11, prime_9103, prime_11, by norm_num⟩
  · exact ⟨9041, 43, prime_9041, prime_43, by norm_num⟩
  · exact ⟨9103, 13, prime_9103, prime_13, by norm_num⟩
  · exact ⟨9127, 2, prime_9127, prime_2, by norm_num⟩
  · exact ⟨9127, 3, prime_9127, prime_3, by norm_num⟩
  · exact ⟨9109, 13, prime_9109, prime_13, by norm_num⟩
  · exact ⟨9133, 2, prime_9133, prime_2, by norm_num⟩
  · exact ⟨9133, 3, prime_9133, prime_3, by norm_num⟩
  · exact ⟨9137, 2, prime_9137, prime_2, by norm_num⟩
  · exact ⟨9137, 3, prime_9137, prime_3, by norm_num⟩
  · exact ⟨9059, 43, prime_9059, prime_43, by norm_num⟩
  · exact ⟨9137, 5, prime_9137, prime_5, by norm_num⟩
  · exact ⟨9127, 11, prime_9127, prime_11, by norm_num⟩
  · exact ⟨9137, 7, prime_9137, prime_7, by norm_num⟩
  · exact ⟨9127, 13, prime_9127, prime_13, by norm_num⟩
  · exact ⟨9151, 2, prime_9151, prime_2, by norm_num⟩
  · exact ⟨9151, 3, prime_9151, prime_3, by norm_num⟩
  · exact ⟨9137, 11, prime_9137, prime_11, by norm_num⟩
  · exact ⟨9157, 2, prime_9157, prime_2, by norm_num⟩
  · exact ⟨9157, 3, prime_9157, prime_3, by norm_num⟩
  · exact ⟨9161, 2, prime_9161, prime_2, by norm_num⟩
  · exact ⟨9161, 3, prime_9161, prime_3, by norm_num⟩
  · exact ⟨9011, 79, prime_9011, prime_79, by norm_num⟩
  · exact ⟨9161, 5, prime_9161, prime_5, by norm_num⟩
  · exact ⟨9151, 11, prime_9151, prime_11, by norm_num⟩
  · exact ⟨9161, 7, prime_9161, prime_7, by norm_num⟩
  · exact ⟨9173, 2, prime_9173, prime_2, by norm_num⟩
  · exact ⟨9173, 3, prime_9173, prime_3, by norm_num⟩
  · exact ⟨9059, 61, prime_9059, prime_61, by norm_num⟩
  · exact ⟨9173, 5, prime_9173, prime_5, by norm_num⟩
  · exact ⟨9181, 2, prime_9181, prime_2, by norm_num⟩
  · exact ⟨9181, 3, prime_9181, prime_3, by norm_num⟩
  · exact ⟨9151, 19, prime_9151, prime_19, by norm_num⟩
  · exact ⟨9187, 2, prime_9187, prime_2, by norm_num⟩
  · exact ⟨9187, 3, prime_9187, prime_3, by norm_num⟩
  · exact ⟨9181, 7, prime_9181, prime_7, by norm_num⟩
  · exact ⟨9187, 5, prime_9187, prime_5, by norm_num⟩
  · exact ⟨9173, 13, prime_9173, prime_13, by norm_num⟩
  · exact ⟨9187, 7, prime_9187, prime_7, by norm_num⟩
  · exact ⟨9199, 2, prime_9199, prime_2, by norm_num⟩
  · exact ⟨9199, 3, prime_9199, prime_3, by norm_num⟩

private theorem lemoine_chunk_46 : ∀ k : ℕ, 4603 ≤ k → k ≤ 4702 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨9203, 2, prime_9203, prime_2, by norm_num⟩
  · exact ⟨9203, 3, prime_9203, prime_3, by norm_num⟩
  · exact ⟨9173, 19, prime_9173, prime_19, by norm_num⟩
  · exact ⟨9209, 2, prime_9209, prime_2, by norm_num⟩
  · exact ⟨9209, 3, prime_9209, prime_3, by norm_num⟩
  · exact ⟨9203, 7, prime_9203, prime_7, by norm_num⟩
  · exact ⟨9209, 5, prime_9209, prime_5, by norm_num⟩
  · exact ⟨9199, 11, prime_9199, prime_11, by norm_num⟩
  · exact ⟨9209, 7, prime_9209, prime_7, by norm_num⟩
  · exact ⟨9221, 2, prime_9221, prime_2, by norm_num⟩
  · exact ⟨9221, 3, prime_9221, prime_3, by norm_num⟩
  · exact ⟨9203, 13, prime_9203, prime_13, by norm_num⟩
  · exact ⟨9227, 2, prime_9227, prime_2, by norm_num⟩
  · exact ⟨9227, 3, prime_9227, prime_3, by norm_num⟩
  · exact ⟨9221, 7, prime_9221, prime_7, by norm_num⟩
  · exact ⟨9227, 5, prime_9227, prime_5, by norm_num⟩
  · exact ⟨9181, 29, prime_9181, prime_29, by norm_num⟩
  · exact ⟨9227, 7, prime_9227, prime_7, by norm_num⟩
  · exact ⟨9239, 2, prime_9239, prime_2, by norm_num⟩
  · exact ⟨9241, 2, prime_9241, prime_2, by norm_num⟩
  · exact ⟨9241, 3, prime_9241, prime_3, by norm_num⟩
  · exact ⟨9239, 5, prime_9239, prime_5, by norm_num⟩
  · exact ⟨9241, 5, prime_9241, prime_5, by norm_num⟩
  · exact ⟨9239, 7, prime_9239, prime_7, by norm_num⟩
  · exact ⟨9241, 7, prime_9241, prime_7, by norm_num⟩
  · exact ⟨9199, 29, prime_9199, prime_29, by norm_num⟩
  · exact ⟨9221, 19, prime_9221, prime_19, by norm_num⟩
  · exact ⟨9257, 2, prime_9257, prime_2, by norm_num⟩
  · exact ⟨9257, 3, prime_9257, prime_3, by norm_num⟩
  · exact ⟨9239, 13, prime_9239, prime_13, by norm_num⟩
  · exact ⟨9257, 5, prime_9257, prime_5, by norm_num⟩
  · exact ⟨9187, 41, prime_9187, prime_41, by norm_num⟩
  · exact ⟨9257, 7, prime_9257, prime_7, by norm_num⟩
  · exact ⟨9239, 17, prime_9239, prime_17, by norm_num⟩
  · exact ⟨9241, 17, prime_9241, prime_17, by norm_num⟩
  · exact ⟨9239, 19, prime_9239, prime_19, by norm_num⟩
  · exact ⟨9257, 11, prime_9257, prime_11, by norm_num⟩
  · exact ⟨9277, 2, prime_9277, prime_2, by norm_num⟩
  · exact ⟨9277, 3, prime_9277, prime_3, by norm_num⟩
  · exact ⟨9281, 2, prime_9281, prime_2, by norm_num⟩
  · exact ⟨9283, 2, prime_9283, prime_2, by norm_num⟩
  · exact ⟨9283, 3, prime_9283, prime_3, by norm_num⟩
  · exact ⟨9281, 5, prime_9281, prime_5, by norm_num⟩
  · exact ⟨9283, 5, prime_9283, prime_5, by norm_num⟩
  · exact ⟨9281, 7, prime_9281, prime_7, by norm_num⟩
  · exact ⟨9293, 2, prime_9293, prime_2, by norm_num⟩
  · exact ⟨9293, 3, prime_9293, prime_3, by norm_num⟩
  · exact ⟨9239, 31, prime_9239, prime_31, by norm_num⟩
  · exact ⟨9293, 5, prime_9293, prime_5, by norm_num⟩
  · exact ⟨9283, 11, prime_9283, prime_11, by norm_num⟩
  · exact ⟨9293, 7, prime_9293, prime_7, by norm_num⟩
  · exact ⟨9283, 13, prime_9283, prime_13, by norm_num⟩
  · exact ⟨9277, 17, prime_9277, prime_17, by norm_num⟩
  · exact ⟨9239, 37, prime_9239, prime_37, by norm_num⟩
  · exact ⟨9311, 2, prime_9311, prime_2, by norm_num⟩
  · exact ⟨9311, 3, prime_9311, prime_3, by norm_num⟩
  · exact ⟨9293, 13, prime_9293, prime_13, by norm_num⟩
  · exact ⟨9311, 5, prime_9311, prime_5, by norm_num⟩
  · exact ⟨9319, 2, prime_9319, prime_2, by norm_num⟩
  · exact ⟨9319, 3, prime_9319, prime_3, by norm_num⟩
  · exact ⟨9323, 2, prime_9323, prime_2, by norm_num⟩
  · exact ⟨9323, 3, prime_9323, prime_3, by norm_num⟩
  · exact ⟨9293, 19, prime_9293, prime_19, by norm_num⟩
  · exact ⟨9323, 5, prime_9323, prime_5, by norm_num⟩
  · exact ⟨9277, 29, prime_9277, prime_29, by norm_num⟩
  · exact ⟨9323, 7, prime_9323, prime_7, by norm_num⟩
  · exact ⟨9293, 23, prime_9293, prime_23, by norm_num⟩
  · exact ⟨9337, 2, prime_9337, prime_2, by norm_num⟩
  · exact ⟨9337, 3, prime_9337, prime_3, by norm_num⟩
  · exact ⟨9341, 2, prime_9341, prime_2, by norm_num⟩
  · exact ⟨9343, 2, prime_9343, prime_2, by norm_num⟩
  · exact ⟨9343, 3, prime_9343, prime_3, by norm_num⟩
  · exact ⟨9341, 5, prime_9341, prime_5, by norm_num⟩
  · exact ⟨9349, 2, prime_9349, prime_2, by norm_num⟩
  · exact ⟨9349, 3, prime_9349, prime_3, by norm_num⟩
  · exact ⟨9343, 7, prime_9343, prime_7, by norm_num⟩
  · exact ⟨9349, 5, prime_9349, prime_5, by norm_num⟩
  · exact ⟨9323, 19, prime_9323, prime_19, by norm_num⟩
  · exact ⟨9349, 7, prime_9349, prime_7, by norm_num⟩
  · exact ⟨9343, 11, prime_9343, prime_11, by norm_num⟩
  · exact ⟨9341, 13, prime_9341, prime_13, by norm_num⟩
  · exact ⟨9343, 13, prime_9343, prime_13, by norm_num⟩
  · exact ⟨9349, 11, prime_9349, prime_11, by norm_num⟩
  · exact ⟨9311, 31, prime_9311, prime_31, by norm_num⟩
  · exact ⟨9371, 2, prime_9371, prime_2, by norm_num⟩
  · exact ⟨9371, 3, prime_9371, prime_3, by norm_num⟩
  · exact ⟨9341, 19, prime_9341, prime_19, by norm_num⟩
  · exact ⟨9377, 2, prime_9377, prime_2, by norm_num⟩
  · exact ⟨9377, 3, prime_9377, prime_3, by norm_num⟩
  · exact ⟨9371, 7, prime_9371, prime_7, by norm_num⟩
  · exact ⟨9377, 5, prime_9377, prime_5, by norm_num⟩
  · exact ⟨9343, 23, prime_9343, prime_23, by norm_num⟩
  · exact ⟨9377, 7, prime_9377, prime_7, by norm_num⟩
  · exact ⟨9371, 11, prime_9371, prime_11, by norm_num⟩
  · exact ⟨9391, 2, prime_9391, prime_2, by norm_num⟩
  · exact ⟨9391, 3, prime_9391, prime_3, by norm_num⟩
  · exact ⟨9377, 11, prime_9377, prime_11, by norm_num⟩
  · exact ⟨9397, 2, prime_9397, prime_2, by norm_num⟩
  · exact ⟨9397, 3, prime_9397, prime_3, by norm_num⟩
  · exact ⟨9391, 7, prime_9391, prime_7, by norm_num⟩

private theorem lemoine_chunk_47 : ∀ k : ℕ, 4703 ≤ k → k ≤ 4802 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨9403, 2, prime_9403, prime_2, by norm_num⟩
  · exact ⟨9403, 3, prime_9403, prime_3, by norm_num⟩
  · exact ⟨9397, 7, prime_9397, prime_7, by norm_num⟩
  · exact ⟨9403, 5, prime_9403, prime_5, by norm_num⟩
  · exact ⟨9377, 19, prime_9377, prime_19, by norm_num⟩
  · exact ⟨9413, 2, prime_9413, prime_2, by norm_num⟩
  · exact ⟨9413, 3, prime_9413, prime_3, by norm_num⟩
  · exact ⟨9227, 97, prime_9227, prime_97, by norm_num⟩
  · exact ⟨9419, 2, prime_9419, prime_2, by norm_num⟩
  · exact ⟨9421, 2, prime_9421, prime_2, by norm_num⟩
  · exact ⟨9421, 3, prime_9421, prime_3, by norm_num⟩
  · exact ⟨9419, 5, prime_9419, prime_5, by norm_num⟩
  · exact ⟨9421, 5, prime_9421, prime_5, by norm_num⟩
  · exact ⟨9419, 7, prime_9419, prime_7, by norm_num⟩
  · exact ⟨9431, 2, prime_9431, prime_2, by norm_num⟩
  · exact ⟨9433, 2, prime_9433, prime_2, by norm_num⟩
  · exact ⟨9433, 3, prime_9433, prime_3, by norm_num⟩
  · exact ⟨9437, 2, prime_9437, prime_2, by norm_num⟩
  · exact ⟨9439, 2, prime_9439, prime_2, by norm_num⟩
  · exact ⟨9439, 3, prime_9439, prime_3, by norm_num⟩
  · exact ⟨9437, 5, prime_9437, prime_5, by norm_num⟩
  · exact ⟨9439, 5, prime_9439, prime_5, by norm_num⟩
  · exact ⟨9437, 7, prime_9437, prime_7, by norm_num⟩
  · exact ⟨9439, 7, prime_9439, prime_7, by norm_num⟩
  · exact ⟨9433, 11, prime_9433, prime_11, by norm_num⟩
  · exact ⟨9431, 13, prime_9431, prime_13, by norm_num⟩
  · exact ⟨9437, 11, prime_9437, prime_11, by norm_num⟩
  · exact ⟨9439, 11, prime_9439, prime_11, by norm_num⟩
  · exact ⟨9437, 13, prime_9437, prime_13, by norm_num⟩
  · exact ⟨9461, 2, prime_9461, prime_2, by norm_num⟩
  · exact ⟨9463, 2, prime_9463, prime_2, by norm_num⟩
  · exact ⟨9463, 3, prime_9463, prime_3, by norm_num⟩
  · exact ⟨9467, 2, prime_9467, prime_2, by norm_num⟩
  · exact ⟨9467, 3, prime_9467, prime_3, by norm_num⟩
  · exact ⟨9461, 7, prime_9461, prime_7, by norm_num⟩
  · exact ⟨9473, 2, prime_9473, prime_2, by norm_num⟩
  · exact ⟨9473, 3, prime_9473, prime_3, by norm_num⟩
  · exact ⟨9467, 7, prime_9467, prime_7, by norm_num⟩
  · exact ⟨9479, 2, prime_9479, prime_2, by norm_num⟩
  · exact ⟨9479, 3, prime_9479, prime_3, by norm_num⟩
  · exact ⟨9473, 7, prime_9473, prime_7, by norm_num⟩
  · exact ⟨9479, 5, prime_9479, prime_5, by norm_num⟩
  · exact ⟨9433, 29, prime_9433, prime_29, by norm_num⟩
  · exact ⟨9479, 7, prime_9479, prime_7, by norm_num⟩
  · exact ⟨9491, 2, prime_9491, prime_2, by norm_num⟩
  · exact ⟨9491, 3, prime_9491, prime_3, by norm_num⟩
  · exact ⟨9473, 13, prime_9473, prime_13, by norm_num⟩
  · exact ⟨9497, 2, prime_9497, prime_2, by norm_num⟩
  · exact ⟨9497, 3, prime_9497, prime_3, by norm_num⟩
  · exact ⟨9491, 7, prime_9491, prime_7, by norm_num⟩
  · exact ⟨9497, 5, prime_9497, prime_5, by norm_num⟩
  · exact ⟨9463, 23, prime_9463, prime_23, by norm_num⟩
  · exact ⟨9497, 7, prime_9497, prime_7, by norm_num⟩
  · exact ⟨9491, 11, prime_9491, prime_11, by norm_num⟩
  · exact ⟨9511, 2, prime_9511, prime_2, by norm_num⟩
  · exact ⟨9511, 3, prime_9511, prime_3, by norm_num⟩
  · exact ⟨9497, 11, prime_9497, prime_11, by norm_num⟩
  · exact ⟨9511, 5, prime_9511, prime_5, by norm_num⟩
  · exact ⟨9497, 13, prime_9497, prime_13, by norm_num⟩
  · exact ⟨9521, 2, prime_9521, prime_2, by norm_num⟩
  · exact ⟨9521, 3, prime_9521, prime_3, by norm_num⟩
  · exact ⟨9491, 19, prime_9491, prime_19, by norm_num⟩
  · exact ⟨9521, 5, prime_9521, prime_5, by norm_num⟩
  · exact ⟨9511, 11, prime_9511, prime_11, by norm_num⟩
  · exact ⟨9521, 7, prime_9521, prime_7, by norm_num⟩
  · exact ⟨9533, 2, prime_9533, prime_2, by norm_num⟩
  · exact ⟨9533, 3, prime_9533, prime_3, by norm_num⟩
  · exact ⟨9479, 31, prime_9479, prime_31, by norm_num⟩
  · exact ⟨9539, 2, prime_9539, prime_2, by norm_num⟩
  · exact ⟨9539, 3, prime_9539, prime_3, by norm_num⟩
  · exact ⟨9533, 7, prime_9533, prime_7, by norm_num⟩
  · exact ⟨9539, 5, prime_9539, prime_5, by norm_num⟩
  · exact ⟨9547, 2, prime_9547, prime_2, by norm_num⟩
  · exact ⟨9547, 3, prime_9547, prime_3, by norm_num⟩
  · exact ⟨9551, 2, prime_9551, prime_2, by norm_num⟩
  · exact ⟨9551, 3, prime_9551, prime_3, by norm_num⟩
  · exact ⟨9533, 13, prime_9533, prime_13, by norm_num⟩
  · exact ⟨9551, 5, prime_9551, prime_5, by norm_num⟩
  · exact ⟨9421, 71, prime_9421, prime_71, by norm_num⟩
  · exact ⟨9551, 7, prime_9551, prime_7, by norm_num⟩
  · exact ⟨9533, 17, prime_9533, prime_17, by norm_num⟩
  · exact ⟨9547, 11, prime_9547, prime_11, by norm_num⟩
  · exact ⟨9533, 19, prime_9533, prime_19, by norm_num⟩
  · exact ⟨9551, 11, prime_9551, prime_11, by norm_num⟩
  · exact ⟨9433, 71, prime_9433, prime_71, by norm_num⟩
  · exact ⟨9551, 13, prime_9551, prime_13, by norm_num⟩
  · exact ⟨9533, 23, prime_9533, prime_23, by norm_num⟩
  · exact ⟨9547, 17, prime_9547, prime_17, by norm_num⟩
  · exact ⟨9521, 31, prime_9521, prime_31, by norm_num⟩
  · exact ⟨9551, 17, prime_9551, prime_17, by norm_num⟩
  · exact ⟨9421, 83, prime_9421, prime_83, by norm_num⟩
  · exact ⟨9551, 19, prime_9551, prime_19, by norm_num⟩
  · exact ⟨9587, 2, prime_9587, prime_2, by norm_num⟩
  · exact ⟨9587, 3, prime_9587, prime_3, by norm_num⟩
  · exact ⟨9533, 31, prime_9533, prime_31, by norm_num⟩
  · exact ⟨9587, 5, prime_9587, prime_5, by norm_num⟩
  · exact ⟨9433, 83, prime_9433, prime_83, by norm_num⟩
  · exact ⟨9587, 7, prime_9587, prime_7, by norm_num⟩
  · exact ⟨9521, 41, prime_9521, prime_41, by norm_num⟩
  · exact ⟨9601, 2, prime_9601, prime_2, by norm_num⟩

private theorem lemoine_chunk_48 : ∀ k : ℕ, 4803 ≤ k → k ≤ 4902 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨9601, 3, prime_9601, prime_3, by norm_num⟩
  · exact ⟨9587, 11, prime_9587, prime_11, by norm_num⟩
  · exact ⟨9601, 5, prime_9601, prime_5, by norm_num⟩
  · exact ⟨9587, 13, prime_9587, prime_13, by norm_num⟩
  · exact ⟨9601, 7, prime_9601, prime_7, by norm_num⟩
  · exact ⟨9613, 2, prime_9613, prime_2, by norm_num⟩
  · exact ⟨9613, 3, prime_9613, prime_3, by norm_num⟩
  · exact ⟨9587, 17, prime_9587, prime_17, by norm_num⟩
  · exact ⟨9619, 2, prime_9619, prime_2, by norm_num⟩
  · exact ⟨9619, 3, prime_9619, prime_3, by norm_num⟩
  · exact ⟨9623, 2, prime_9623, prime_2, by norm_num⟩
  · exact ⟨9623, 3, prime_9623, prime_3, by norm_num⟩
  · exact ⟨9497, 67, prime_9497, prime_67, by norm_num⟩
  · exact ⟨9629, 2, prime_9629, prime_2, by norm_num⟩
  · exact ⟨9631, 2, prime_9631, prime_2, by norm_num⟩
  · exact ⟨9631, 3, prime_9631, prime_3, by norm_num⟩
  · exact ⟨9629, 5, prime_9629, prime_5, by norm_num⟩
  · exact ⟨9631, 5, prime_9631, prime_5, by norm_num⟩
  · exact ⟨9629, 7, prime_9629, prime_7, by norm_num⟩
  · exact ⟨9631, 7, prime_9631, prime_7, by norm_num⟩
  · exact ⟨9643, 2, prime_9643, prime_2, by norm_num⟩
  · exact ⟨9643, 3, prime_9643, prime_3, by norm_num⟩
  · exact ⟨9629, 11, prime_9629, prime_11, by norm_num⟩
  · exact ⟨9649, 2, prime_9649, prime_2, by norm_num⟩
  · exact ⟨9649, 3, prime_9649, prime_3, by norm_num⟩
  · exact ⟨9643, 7, prime_9643, prime_7, by norm_num⟩
  · exact ⟨9649, 5, prime_9649, prime_5, by norm_num⟩
  · exact ⟨9623, 19, prime_9623, prime_19, by norm_num⟩
  · exact ⟨9649, 7, prime_9649, prime_7, by norm_num⟩
  · exact ⟨9661, 2, prime_9661, prime_2, by norm_num⟩
  · exact ⟨9661, 3, prime_9661, prime_3, by norm_num⟩
  · exact ⟨9643, 13, prime_9643, prime_13, by norm_num⟩
  · exact ⟨9661, 5, prime_9661, prime_5, by norm_num⟩
  · exact ⟨9587, 43, prime_9587, prime_43, by norm_num⟩
  · exact ⟨9661, 7, prime_9661, prime_7, by norm_num⟩
  · exact ⟨9643, 17, prime_9643, prime_17, by norm_num⟩
  · exact ⟨9533, 73, prime_9533, prime_73, by norm_num⟩
  · exact ⟨9677, 2, prime_9677, prime_2, by norm_num⟩
  · exact ⟨9679, 2, prime_9679, prime_2, by norm_num⟩
  · exact ⟨9679, 3, prime_9679, prime_3, by norm_num⟩
  · exact ⟨9677, 5, prime_9677, prime_5, by norm_num⟩
  · exact ⟨9679, 5, prime_9679, prime_5, by norm_num⟩
  · exact ⟨9677, 7, prime_9677, prime_7, by norm_num⟩
  · exact ⟨9689, 2, prime_9689, prime_2, by norm_num⟩
  · exact ⟨9689, 3, prime_9689, prime_3, by norm_num⟩
  · exact ⟨9623, 37, prime_9623, prime_37, by norm_num⟩
  · exact ⟨9689, 5, prime_9689, prime_5, by norm_num⟩
  · exact ⟨9697, 2, prime_9697, prime_2, by norm_num⟩
  · exact ⟨9697, 3, prime_9697, prime_3, by norm_num⟩
  · exact ⟨9679, 13, prime_9679, prime_13, by norm_num⟩
  · exact ⟨9697, 5, prime_9697, prime_5, by norm_num⟩
  · exact ⟨9623, 43, prime_9623, prime_43, by norm_num⟩
  · exact ⟨9697, 7, prime_9697, prime_7, by norm_num⟩
  · exact ⟨9679, 17, prime_9679, prime_17, by norm_num⟩
  · exact ⟨9689, 13, prime_9689, prime_13, by norm_num⟩
  · exact ⟨9679, 19, prime_9679, prime_19, by norm_num⟩
  · exact ⟨9697, 11, prime_9697, prime_11, by norm_num⟩
  · exact ⟨9587, 67, prime_9587, prime_67, by norm_num⟩
  · exact ⟨9719, 2, prime_9719, prime_2, by norm_num⟩
  · exact ⟨9721, 2, prime_9721, prime_2, by norm_num⟩
  · exact ⟨9721, 3, prime_9721, prime_3, by norm_num⟩
  · exact ⟨9719, 5, prime_9719, prime_5, by norm_num⟩
  · exact ⟨9721, 5, prime_9721, prime_5, by norm_num⟩
  · exact ⟨9719, 7, prime_9719, prime_7, by norm_num⟩
  · exact ⟨9721, 7, prime_9721, prime_7, by norm_num⟩
  · exact ⟨9733, 2, prime_9733, prime_2, by norm_num⟩
  · exact ⟨9733, 3, prime_9733, prime_3, by norm_num⟩
  · exact ⟨9719, 11, prime_9719, prime_11, by norm_num⟩
  · exact ⟨9739, 2, prime_9739, prime_2, by norm_num⟩
  · exact ⟨9739, 3, prime_9739, prime_3, by norm_num⟩
  · exact ⟨9743, 2, prime_9743, prime_2, by norm_num⟩
  · exact ⟨9743, 3, prime_9743, prime_3, by norm_num⟩
  · exact ⟨9689, 31, prime_9689, prime_31, by norm_num⟩
  · exact ⟨9749, 2, prime_9749, prime_2, by norm_num⟩
  · exact ⟨9749, 3, prime_9749, prime_3, by norm_num⟩
  · exact ⟨9743, 7, prime_9743, prime_7, by norm_num⟩
  · exact ⟨9749, 5, prime_9749, prime_5, by norm_num⟩
  · exact ⟨9739, 11, prime_9739, prime_11, by norm_num⟩
  · exact ⟨9749, 7, prime_9749, prime_7, by norm_num⟩
  · exact ⟨9743, 11, prime_9743, prime_11, by norm_num⟩
  · exact ⟨9733, 17, prime_9733, prime_17, by norm_num⟩
  · exact ⟨9743, 13, prime_9743, prime_13, by norm_num⟩
  · exact ⟨9767, 2, prime_9767, prime_2, by norm_num⟩
  · exact ⟨9769, 2, prime_9769, prime_2, by norm_num⟩
  · exact ⟨9769, 3, prime_9769, prime_3, by norm_num⟩
  · exact ⟨9767, 5, prime_9767, prime_5, by norm_num⟩
  · exact ⟨9769, 5, prime_9769, prime_5, by norm_num⟩
  · exact ⟨9767, 7, prime_9767, prime_7, by norm_num⟩
  · exact ⟨9769, 7, prime_9769, prime_7, by norm_num⟩
  · exact ⟨9781, 2, prime_9781, prime_2, by norm_num⟩
  · exact ⟨9781, 3, prime_9781, prime_3, by norm_num⟩
  · exact ⟨9767, 11, prime_9767, prime_11, by norm_num⟩
  · exact ⟨9787, 2, prime_9787, prime_2, by norm_num⟩
  · exact ⟨9787, 3, prime_9787, prime_3, by norm_num⟩
  · exact ⟨9791, 2, prime_9791, prime_2, by norm_num⟩
  · exact ⟨9791, 3, prime_9791, prime_3, by norm_num⟩
  · exact ⟨9677, 61, prime_9677, prime_61, by norm_num⟩
  · exact ⟨9791, 5, prime_9791, prime_5, by norm_num⟩
  · exact ⟨9781, 11, prime_9781, prime_11, by norm_num⟩
  · exact ⟨9791, 7, prime_9791, prime_7, by norm_num⟩

private theorem lemoine_chunk_49 : ∀ k : ℕ, 4903 ≤ k → k ≤ 5002 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨9803, 2, prime_9803, prime_2, by norm_num⟩
  · exact ⟨9803, 3, prime_9803, prime_3, by norm_num⟩
  · exact ⟨9749, 31, prime_9749, prime_31, by norm_num⟩
  · exact ⟨9803, 5, prime_9803, prime_5, by norm_num⟩
  · exact ⟨9811, 2, prime_9811, prime_2, by norm_num⟩
  · exact ⟨9811, 3, prime_9811, prime_3, by norm_num⟩
  · exact ⟨9781, 19, prime_9781, prime_19, by norm_num⟩
  · exact ⟨9817, 2, prime_9817, prime_2, by norm_num⟩
  · exact ⟨9817, 3, prime_9817, prime_3, by norm_num⟩
  · exact ⟨9811, 7, prime_9811, prime_7, by norm_num⟩
  · exact ⟨9817, 5, prime_9817, prime_5, by norm_num⟩
  · exact ⟨9803, 13, prime_9803, prime_13, by norm_num⟩
  · exact ⟨9817, 7, prime_9817, prime_7, by norm_num⟩
  · exact ⟨9829, 2, prime_9829, prime_2, by norm_num⟩
  · exact ⟨9829, 3, prime_9829, prime_3, by norm_num⟩
  · exact ⟨9833, 2, prime_9833, prime_2, by norm_num⟩
  · exact ⟨9833, 3, prime_9833, prime_3, by norm_num⟩
  · exact ⟨9803, 19, prime_9803, prime_19, by norm_num⟩
  · exact ⟨9839, 2, prime_9839, prime_2, by norm_num⟩
  · exact ⟨9839, 3, prime_9839, prime_3, by norm_num⟩
  · exact ⟨9833, 7, prime_9833, prime_7, by norm_num⟩
  · exact ⟨9839, 5, prime_9839, prime_5, by norm_num⟩
  · exact ⟨9829, 11, prime_9829, prime_11, by norm_num⟩
  · exact ⟨9839, 7, prime_9839, prime_7, by norm_num⟩
  · exact ⟨9851, 2, prime_9851, prime_2, by norm_num⟩
  · exact ⟨9851, 3, prime_9851, prime_3, by norm_num⟩
  · exact ⟨9833, 13, prime_9833, prime_13, by norm_num⟩
  · exact ⟨9857, 2, prime_9857, prime_2, by norm_num⟩
  · exact ⟨9859, 2, prime_9859, prime_2, by norm_num⟩
  · exact ⟨9859, 3, prime_9859, prime_3, by norm_num⟩
  · exact ⟨9857, 5, prime_9857, prime_5, by norm_num⟩
  · exact ⟨9859, 5, prime_9859, prime_5, by norm_num⟩
  · exact ⟨9857, 7, prime_9857, prime_7, by norm_num⟩
  · exact ⟨9859, 7, prime_9859, prime_7, by norm_num⟩
  · exact ⟨9871, 2, prime_9871, prime_2, by norm_num⟩
  · exact ⟨9871, 3, prime_9871, prime_3, by norm_num⟩
  · exact ⟨9857, 11, prime_9857, prime_11, by norm_num⟩
  · exact ⟨9871, 5, prime_9871, prime_5, by norm_num⟩
  · exact ⟨9857, 13, prime_9857, prime_13, by norm_num⟩
  · exact ⟨9871, 7, prime_9871, prime_7, by norm_num⟩
  · exact ⟨9883, 2, prime_9883, prime_2, by norm_num⟩
  · exact ⟨9883, 3, prime_9883, prime_3, by norm_num⟩
  · exact ⟨9887, 2, prime_9887, prime_2, by norm_num⟩
  · exact ⟨9887, 3, prime_9887, prime_3, by norm_num⟩
  · exact ⟨9857, 19, prime_9857, prime_19, by norm_num⟩
  · exact ⟨9887, 5, prime_9887, prime_5, by norm_num⟩
  · exact ⟨9817, 41, prime_9817, prime_41, by norm_num⟩
  · exact ⟨9887, 7, prime_9887, prime_7, by norm_num⟩
  · exact ⟨9857, 23, prime_9857, prime_23, by norm_num⟩
  · exact ⟨9901, 2, prime_9901, prime_2, by norm_num⟩
  · exact ⟨9901, 3, prime_9901, prime_3, by norm_num⟩
  · exact ⟨9887, 11, prime_9887, prime_11, by norm_num⟩
  · exact ⟨9907, 2, prime_9907, prime_2, by norm_num⟩
  · exact ⟨9907, 3, prime_9907, prime_3, by norm_num⟩
  · exact ⟨9901, 7, prime_9901, prime_7, by norm_num⟩
  · exact ⟨9907, 5, prime_9907, prime_5, by norm_num⟩
  · exact ⟨9857, 31, prime_9857, prime_31, by norm_num⟩
  · exact ⟨9907, 7, prime_9907, prime_7, by norm_num⟩
  · exact ⟨9901, 11, prime_9901, prime_11, by norm_num⟩
  · exact ⟨9887, 19, prime_9887, prime_19, by norm_num⟩
  · exact ⟨9923, 2, prime_9923, prime_2, by norm_num⟩
  · exact ⟨9923, 3, prime_9923, prime_3, by norm_num⟩
  · exact ⟨9857, 37, prime_9857, prime_37, by norm_num⟩
  · exact ⟨9929, 2, prime_9929, prime_2, by norm_num⟩
  · exact ⟨9931, 2, prime_9931, prime_2, by norm_num⟩
  · exact ⟨9931, 3, prime_9931, prime_3, by norm_num⟩
  · exact ⟨9929, 5, prime_9929, prime_5, by norm_num⟩
  · exact ⟨9931, 5, prime_9931, prime_5, by norm_num⟩
  · exact ⟨9929, 7, prime_9929, prime_7, by norm_num⟩
  · exact ⟨9941, 2, prime_9941, prime_2, by norm_num⟩
  · exact ⟨9941, 3, prime_9941, prime_3, by norm_num⟩
  · exact ⟨9923, 13, prime_9923, prime_13, by norm_num⟩
  · exact ⟨9941, 5, prime_9941, prime_5, by norm_num⟩
  · exact ⟨9949, 2, prime_9949, prime_2, by norm_num⟩
  · exact ⟨9949, 3, prime_9949, prime_3, by norm_num⟩
  · exact ⟨9931, 13, prime_9931, prime_13, by norm_num⟩
  · exact ⟨9949, 5, prime_9949, prime_5, by norm_num⟩
  · exact ⟨9923, 19, prime_9923, prime_19, by norm_num⟩
  · exact ⟨9949, 7, prime_9949, prime_7, by norm_num⟩
  · exact ⟨9931, 17, prime_9931, prime_17, by norm_num⟩
  · exact ⟨9941, 13, prime_9941, prime_13, by norm_num⟩
  · exact ⟨9931, 19, prime_9931, prime_19, by norm_num⟩
  · exact ⟨9967, 2, prime_9967, prime_2, by norm_num⟩
  · exact ⟨9967, 3, prime_9967, prime_3, by norm_num⟩
  · exact ⟨9949, 13, prime_9949, prime_13, by norm_num⟩
  · exact ⟨9973, 2, prime_9973, prime_2, by norm_num⟩
  · exact ⟨9973, 3, prime_9973, prime_3, by norm_num⟩
  · exact ⟨9967, 7, prime_9967, prime_7, by norm_num⟩
  · exact ⟨9973, 5, prime_9973, prime_5, by norm_num⟩
  · exact ⟨9923, 31, prime_9923, prime_31, by norm_num⟩
  · exact ⟨9973, 7, prime_9973, prime_7, by norm_num⟩
  · exact ⟨9967, 11, prime_9967, prime_11, by norm_num⟩
  · exact ⟨9929, 31, prime_9929, prime_31, by norm_num⟩
  · exact ⟨9967, 13, prime_9967, prime_13, by norm_num⟩
  · exact ⟨9973, 11, prime_9973, prime_11, by norm_num⟩
  · exact ⟨9923, 37, prime_9923, prime_37, by norm_num⟩
  · exact ⟨9973, 13, prime_9973, prime_13, by norm_num⟩
  · exact ⟨9967, 17, prime_9967, prime_17, by norm_num⟩
  · exact ⟨9941, 31, prime_9941, prime_31, by norm_num⟩
  · exact ⟨9967, 19, prime_9967, prime_19, by norm_num⟩

private theorem lemoine_chunk_50 : ∀ k : ℕ, 5003 ≤ k → k ≤ 5102 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨9973, 17, prime_9973, prime_17, by norm_num⟩
  · exact ⟨9923, 43, prime_9923, prime_43, by norm_num⟩
  · exact ⟨10007, 2, prime_10007, prime_2, by norm_num⟩
  · exact ⟨10009, 2, prime_10009, prime_2, by norm_num⟩
  · exact ⟨10009, 3, prime_10009, prime_3, by norm_num⟩
  · exact ⟨10007, 5, prime_10007, prime_5, by norm_num⟩
  · exact ⟨10009, 5, prime_10009, prime_5, by norm_num⟩
  · exact ⟨10007, 7, prime_10007, prime_7, by norm_num⟩
  · exact ⟨10009, 7, prime_10009, prime_7, by norm_num⟩
  · exact ⟨9967, 29, prime_9967, prime_29, by norm_num⟩
  · exact ⟨9941, 43, prime_9941, prime_43, by norm_num⟩
  · exact ⟨10007, 11, prime_10007, prime_11, by norm_num⟩
  · exact ⟨10009, 11, prime_10009, prime_11, by norm_num⟩
  · exact ⟨10007, 13, prime_10007, prime_13, by norm_num⟩
  · exact ⟨10009, 13, prime_10009, prime_13, by norm_num⟩
  · exact ⟨9931, 53, prime_9931, prime_53, by norm_num⟩
  · exact ⟨9833, 103, prime_9833, prime_103, by norm_num⟩
  · exact ⟨10037, 2, prime_10037, prime_2, by norm_num⟩
  · exact ⟨10039, 2, prime_10039, prime_2, by norm_num⟩
  · exact ⟨10039, 3, prime_10039, prime_3, by norm_num⟩
  · exact ⟨10037, 5, prime_10037, prime_5, by norm_num⟩
  · exact ⟨10039, 5, prime_10039, prime_5, by norm_num⟩
  · exact ⟨10037, 7, prime_10037, prime_7, by norm_num⟩
  · exact ⟨10039, 7, prime_10039, prime_7, by norm_num⟩
  · exact ⟨10009, 23, prime_10009, prime_23, by norm_num⟩
  · exact ⟨9923, 67, prime_9923, prime_67, by norm_num⟩
  · exact ⟨10037, 11, prime_10037, prime_11, by norm_num⟩
  · exact ⟨10039, 11, prime_10039, prime_11, by norm_num⟩
  · exact ⟨10037, 13, prime_10037, prime_13, by norm_num⟩
  · exact ⟨10061, 2, prime_10061, prime_2, by norm_num⟩
  · exact ⟨10061, 3, prime_10061, prime_3, by norm_num⟩
  · exact ⟨10007, 31, prime_10007, prime_31, by norm_num⟩
  · exact ⟨10067, 2, prime_10067, prime_2, by norm_num⟩
  · exact ⟨10069, 2, prime_10069, prime_2, by norm_num⟩
  · exact ⟨10069, 3, prime_10069, prime_3, by norm_num⟩
  · exact ⟨10067, 5, prime_10067, prime_5, by norm_num⟩
  · exact ⟨10069, 5, prime_10069, prime_5, by norm_num⟩
  · exact ⟨10067, 7, prime_10067, prime_7, by norm_num⟩
  · exact ⟨10079, 2, prime_10079, prime_2, by norm_num⟩
  · exact ⟨10079, 3, prime_10079, prime_3, by norm_num⟩
  · exact ⟨10061, 13, prime_10061, prime_13, by norm_num⟩
  · exact ⟨10079, 5, prime_10079, prime_5, by norm_num⟩
  · exact ⟨10069, 11, prime_10069, prime_11, by norm_num⟩
  · exact ⟨10079, 7, prime_10079, prime_7, by norm_num⟩
  · exact ⟨10091, 2, prime_10091, prime_2, by norm_num⟩
  · exact ⟨10093, 2, prime_10093, prime_2, by norm_num⟩
  · exact ⟨10093, 3, prime_10093, prime_3, by norm_num⟩
  · exact ⟨10091, 5, prime_10091, prime_5, by norm_num⟩
  · exact ⟨10099, 2, prime_10099, prime_2, by norm_num⟩
  · exact ⟨10099, 3, prime_10099, prime_3, by norm_num⟩
  · exact ⟨10103, 2, prime_10103, prime_2, by norm_num⟩
  · exact ⟨10103, 3, prime_10103, prime_3, by norm_num⟩
  · exact ⟨10037, 37, prime_10037, prime_37, by norm_num⟩
  · exact ⟨10103, 5, prime_10103, prime_5, by norm_num⟩
  · exact ⟨10111, 2, prime_10111, prime_2, by norm_num⟩
  · exact ⟨10111, 3, prime_10111, prime_3, by norm_num⟩
  · exact ⟨10093, 13, prime_10093, prime_13, by norm_num⟩
  · exact ⟨10111, 5, prime_10111, prime_5, by norm_num⟩
  · exact ⟨10061, 31, prime_10061, prime_31, by norm_num⟩
  · exact ⟨10111, 7, prime_10111, prime_7, by norm_num⟩
  · exact ⟨10093, 17, prime_10093, prime_17, by norm_num⟩
  · exact ⟨10103, 13, prime_10103, prime_13, by norm_num⟩
  · exact ⟨10093, 19, prime_10093, prime_19, by norm_num⟩
  · exact ⟨10111, 11, prime_10111, prime_11, by norm_num⟩
  · exact ⟨10061, 37, prime_10061, prime_37, by norm_num⟩
  · exact ⟨10133, 2, prime_10133, prime_2, by norm_num⟩
  · exact ⟨10133, 3, prime_10133, prime_3, by norm_num⟩
  · exact ⟨10103, 19, prime_10103, prime_19, by norm_num⟩
  · exact ⟨10139, 2, prime_10139, prime_2, by norm_num⟩
  · exact ⟨10141, 2, prime_10141, prime_2, by norm_num⟩
  · exact ⟨10141, 3, prime_10141, prime_3, by norm_num⟩
  · exact ⟨10139, 5, prime_10139, prime_5, by norm_num⟩
  · exact ⟨10141, 5, prime_10141, prime_5, by norm_num⟩
  · exact ⟨10139, 7, prime_10139, prime_7, by norm_num⟩
  · exact ⟨10151, 2, prime_10151, prime_2, by norm_num⟩
  · exact ⟨10151, 3, prime_10151, prime_3, by norm_num⟩
  · exact ⟨10133, 13, prime_10133, prime_13, by norm_num⟩
  · exact ⟨10151, 5, prime_10151, prime_5, by norm_num⟩
  · exact ⟨10159, 2, prime_10159, prime_2, by norm_num⟩
  · exact ⟨10159, 3, prime_10159, prime_3, by norm_num⟩
  · exact ⟨10163, 2, prime_10163, prime_2, by norm_num⟩
  · exact ⟨10163, 3, prime_10163, prime_3, by norm_num⟩
  · exact ⟨10133, 19, prime_10133, prime_19, by norm_num⟩
  · exact ⟨10169, 2, prime_10169, prime_2, by norm_num⟩
  · exact ⟨10169, 3, prime_10169, prime_3, by norm_num⟩
  · exact ⟨10163, 7, prime_10163, prime_7, by norm_num⟩
  · exact ⟨10169, 5, prime_10169, prime_5, by norm_num⟩
  · exact ⟨10177, 2, prime_10177, prime_2, by norm_num⟩
  · exact ⟨10177, 3, prime_10177, prime_3, by norm_num⟩
  · exact ⟨10181, 2, prime_10181, prime_2, by norm_num⟩
  · exact ⟨10181, 3, prime_10181, prime_3, by norm_num⟩
  · exact ⟨10163, 13, prime_10163, prime_13, by norm_num⟩
  · exact ⟨10181, 5, prime_10181, prime_5, by norm_num⟩
  · exact ⟨10159, 17, prime_10159, prime_17, by norm_num⟩
  · exact ⟨10181, 7, prime_10181, prime_7, by norm_num⟩
  · exact ⟨10193, 2, prime_10193, prime_2, by norm_num⟩
  · exact ⟨10193, 3, prime_10193, prime_3, by norm_num⟩
  · exact ⟨10163, 19, prime_10163, prime_19, by norm_num⟩
  · exact ⟨10193, 5, prime_10193, prime_5, by norm_num⟩
  · exact ⟨10159, 23, prime_10159, prime_23, by norm_num⟩

private theorem lemoine_chunk_51 : ∀ k : ℕ, 5103 ≤ k → k ≤ 5202 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨10193, 7, prime_10193, prime_7, by norm_num⟩
  · exact ⟨10163, 23, prime_10163, prime_23, by norm_num⟩
  · exact ⟨10177, 17, prime_10177, prime_17, by norm_num⟩
  · exact ⟨10151, 31, prime_10151, prime_31, by norm_num⟩
  · exact ⟨10211, 2, prime_10211, prime_2, by norm_num⟩
  · exact ⟨10211, 3, prime_10211, prime_3, by norm_num⟩
  · exact ⟨10193, 13, prime_10193, prime_13, by norm_num⟩
  · exact ⟨10211, 5, prime_10211, prime_5, by norm_num⟩
  · exact ⟨10177, 23, prime_10177, prime_23, by norm_num⟩
  · exact ⟨10211, 7, prime_10211, prime_7, by norm_num⟩
  · exact ⟨10223, 2, prime_10223, prime_2, by norm_num⟩
  · exact ⟨10223, 3, prime_10223, prime_3, by norm_num⟩
  · exact ⟨10193, 19, prime_10193, prime_19, by norm_num⟩
  · exact ⟨10223, 5, prime_10223, prime_5, by norm_num⟩
  · exact ⟨10177, 29, prime_10177, prime_29, by norm_num⟩
  · exact ⟨10223, 7, prime_10223, prime_7, by norm_num⟩
  · exact ⟨10193, 23, prime_10193, prime_23, by norm_num⟩
  · exact ⟨10159, 41, prime_10159, prime_41, by norm_num⟩
  · exact ⟨10181, 31, prime_10181, prime_31, by norm_num⟩
  · exact ⟨10223, 11, prime_10223, prime_11, by norm_num⟩
  · exact ⟨10243, 2, prime_10243, prime_2, by norm_num⟩
  · exact ⟨10243, 3, prime_10243, prime_3, by norm_num⟩
  · exact ⟨10247, 2, prime_10247, prime_2, by norm_num⟩
  · exact ⟨10247, 3, prime_10247, prime_3, by norm_num⟩
  · exact ⟨10193, 31, prime_10193, prime_31, by norm_num⟩
  · exact ⟨10253, 2, prime_10253, prime_2, by norm_num⟩
  · exact ⟨10253, 3, prime_10253, prime_3, by norm_num⟩
  · exact ⟨10247, 7, prime_10247, prime_7, by norm_num⟩
  · exact ⟨10259, 2, prime_10259, prime_2, by norm_num⟩
  · exact ⟨10259, 3, prime_10259, prime_3, by norm_num⟩
  · exact ⟨10253, 7, prime_10253, prime_7, by norm_num⟩
  · exact ⟨10259, 5, prime_10259, prime_5, by norm_num⟩
  · exact ⟨10267, 2, prime_10267, prime_2, by norm_num⟩
  · exact ⟨10267, 3, prime_10267, prime_3, by norm_num⟩
  · exact ⟨10271, 2, prime_10271, prime_2, by norm_num⟩
  · exact ⟨10273, 2, prime_10273, prime_2, by norm_num⟩
  · exact ⟨10273, 3, prime_10273, prime_3, by norm_num⟩
  · exact ⟨10271, 5, prime_10271, prime_5, by norm_num⟩
  · exact ⟨10273, 5, prime_10273, prime_5, by norm_num⟩
  · exact ⟨10271, 7, prime_10271, prime_7, by norm_num⟩
  · exact ⟨10273, 7, prime_10273, prime_7, by norm_num⟩
  · exact ⟨10267, 11, prime_10267, prime_11, by norm_num⟩
  · exact ⟨10253, 19, prime_10253, prime_19, by norm_num⟩
  · exact ⟨10289, 2, prime_10289, prime_2, by norm_num⟩
  · exact ⟨10289, 3, prime_10289, prime_3, by norm_num⟩
  · exact ⟨10271, 13, prime_10271, prime_13, by norm_num⟩
  · exact ⟨10289, 5, prime_10289, prime_5, by norm_num⟩
  · exact ⟨10267, 17, prime_10267, prime_17, by norm_num⟩
  · exact ⟨10289, 7, prime_10289, prime_7, by norm_num⟩
  · exact ⟨10301, 2, prime_10301, prime_2, by norm_num⟩
  · exact ⟨10303, 2, prime_10303, prime_2, by norm_num⟩
  · exact ⟨10303, 3, prime_10303, prime_3, by norm_num⟩
  · exact ⟨10301, 5, prime_10301, prime_5, by norm_num⟩
  · exact ⟨10303, 5, prime_10303, prime_5, by norm_num⟩
  · exact ⟨10301, 7, prime_10301, prime_7, by norm_num⟩
  · exact ⟨10313, 2, prime_10313, prime_2, by norm_num⟩
  · exact ⟨10313, 3, prime_10313, prime_3, by norm_num⟩
  · exact ⟨10259, 31, prime_10259, prime_31, by norm_num⟩
  · exact ⟨10313, 5, prime_10313, prime_5, by norm_num⟩
  · exact ⟨10321, 2, prime_10321, prime_2, by norm_num⟩
  · exact ⟨10321, 3, prime_10321, prime_3, by norm_num⟩
  · exact ⟨10303, 13, prime_10303, prime_13, by norm_num⟩
  · exact ⟨10321, 5, prime_10321, prime_5, by norm_num⟩
  · exact ⟨10271, 31, prime_10271, prime_31, by norm_num⟩
  · exact ⟨10331, 2, prime_10331, prime_2, by norm_num⟩
  · exact ⟨10333, 2, prime_10333, prime_2, by norm_num⟩
  · exact ⟨10333, 3, prime_10333, prime_3, by norm_num⟩
  · exact ⟨10337, 2, prime_10337, prime_2, by norm_num⟩
  · exact ⟨10337, 3, prime_10337, prime_3, by norm_num⟩
  · exact ⟨10331, 7, prime_10331, prime_7, by norm_num⟩
  · exact ⟨10343, 2, prime_10343, prime_2, by norm_num⟩
  · exact ⟨10343, 3, prime_10343, prime_3, by norm_num⟩
  · exact ⟨10337, 7, prime_10337, prime_7, by norm_num⟩
  · exact ⟨10343, 5, prime_10343, prime_5, by norm_num⟩
  · exact ⟨10333, 11, prime_10333, prime_11, by norm_num⟩
  · exact ⟨10343, 7, prime_10343, prime_7, by norm_num⟩
  · exact ⟨10337, 11, prime_10337, prime_11, by norm_num⟩
  · exact ⟨10357, 2, prime_10357, prime_2, by norm_num⟩
  · exact ⟨10357, 3, prime_10357, prime_3, by norm_num⟩
  · exact ⟨10343, 11, prime_10343, prime_11, by norm_num⟩
  · exact ⟨10357, 5, prime_10357, prime_5, by norm_num⟩
  · exact ⟨10343, 13, prime_10343, prime_13, by norm_num⟩
  · exact ⟨10357, 7, prime_10357, prime_7, by norm_num⟩
  · exact ⟨10369, 2, prime_10369, prime_2, by norm_num⟩
  · exact ⟨10369, 3, prime_10369, prime_3, by norm_num⟩
  · exact ⟨10343, 17, prime_10343, prime_17, by norm_num⟩
  · exact ⟨10369, 5, prime_10369, prime_5, by norm_num⟩
  · exact ⟨10343, 19, prime_10343, prime_19, by norm_num⟩
  · exact ⟨10369, 7, prime_10369, prime_7, by norm_num⟩
  · exact ⟨10303, 41, prime_10303, prime_41, by norm_num⟩
  · exact ⟨10313, 37, prime_10313, prime_37, by norm_num⟩
  · exact ⟨10343, 23, prime_10343, prime_23, by norm_num⟩
  · exact ⟨10369, 11, prime_10369, prime_11, by norm_num⟩
  · exact ⟨10331, 31, prime_10331, prime_31, by norm_num⟩
  · exact ⟨10391, 2, prime_10391, prime_2, by norm_num⟩
  · exact ⟨10391, 3, prime_10391, prime_3, by norm_num⟩
  · exact ⟨10337, 31, prime_10337, prime_31, by norm_num⟩
  · exact ⟨10391, 5, prime_10391, prime_5, by norm_num⟩
  · exact ⟨10399, 2, prime_10399, prime_2, by norm_num⟩
  · exact ⟨10399, 3, prime_10399, prime_3, by norm_num⟩

private theorem lemoine_chunk_52 : ∀ k : ℕ, 5203 ≤ k → k ≤ 5302 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨10369, 19, prime_10369, prime_19, by norm_num⟩
  · exact ⟨10399, 5, prime_10399, prime_5, by norm_num⟩
  · exact ⟨10337, 37, prime_10337, prime_37, by norm_num⟩
  · exact ⟨10399, 7, prime_10399, prime_7, by norm_num⟩
  · exact ⟨10369, 23, prime_10369, prime_23, by norm_num⟩
  · exact ⟨10391, 13, prime_10391, prime_13, by norm_num⟩
  · exact ⟨10357, 31, prime_10357, prime_31, by norm_num⟩
  · exact ⟨10399, 11, prime_10399, prime_11, by norm_num⟩
  · exact ⟨10337, 43, prime_10337, prime_43, by norm_num⟩
  · exact ⟨10399, 13, prime_10399, prime_13, by norm_num⟩
  · exact ⟨10369, 29, prime_10369, prime_29, by norm_num⟩
  · exact ⟨10391, 19, prime_10391, prime_19, by norm_num⟩
  · exact ⟨10427, 2, prime_10427, prime_2, by norm_num⟩
  · exact ⟨10429, 2, prime_10429, prime_2, by norm_num⟩
  · exact ⟨10429, 3, prime_10429, prime_3, by norm_num⟩
  · exact ⟨10433, 2, prime_10433, prime_2, by norm_num⟩
  · exact ⟨10433, 3, prime_10433, prime_3, by norm_num⟩
  · exact ⟨10427, 7, prime_10427, prime_7, by norm_num⟩
  · exact ⟨10433, 5, prime_10433, prime_5, by norm_num⟩
  · exact ⟨10399, 23, prime_10399, prime_23, by norm_num⟩
  · exact ⟨10433, 7, prime_10433, prime_7, by norm_num⟩
  · exact ⟨10427, 11, prime_10427, prime_11, by norm_num⟩
  · exact ⟨10429, 11, prime_10429, prime_11, by norm_num⟩
  · exact ⟨10427, 13, prime_10427, prime_13, by norm_num⟩
  · exact ⟨10433, 11, prime_10433, prime_11, by norm_num⟩
  · exact ⟨10453, 2, prime_10453, prime_2, by norm_num⟩
  · exact ⟨10453, 3, prime_10453, prime_3, by norm_num⟩
  · exact ⟨10457, 2, prime_10457, prime_2, by norm_num⟩
  · exact ⟨10459, 2, prime_10459, prime_2, by norm_num⟩
  · exact ⟨10459, 3, prime_10459, prime_3, by norm_num⟩
  · exact ⟨10463, 2, prime_10463, prime_2, by norm_num⟩
  · exact ⟨10463, 3, prime_10463, prime_3, by norm_num⟩
  · exact ⟨10457, 7, prime_10457, prime_7, by norm_num⟩
  · exact ⟨10463, 5, prime_10463, prime_5, by norm_num⟩
  · exact ⟨10453, 11, prime_10453, prime_11, by norm_num⟩
  · exact ⟨10463, 7, prime_10463, prime_7, by norm_num⟩
  · exact ⟨10457, 11, prime_10457, prime_11, by norm_num⟩
  · exact ⟨10477, 2, prime_10477, prime_2, by norm_num⟩
  · exact ⟨10477, 3, prime_10477, prime_3, by norm_num⟩
  · exact ⟨10463, 11, prime_10463, prime_11, by norm_num⟩
  · exact ⟨10477, 5, prime_10477, prime_5, by norm_num⟩
  · exact ⟨10463, 13, prime_10463, prime_13, by norm_num⟩
  · exact ⟨10487, 2, prime_10487, prime_2, by norm_num⟩
  · exact ⟨10487, 3, prime_10487, prime_3, by norm_num⟩
  · exact ⟨10457, 19, prime_10457, prime_19, by norm_num⟩
  · exact ⟨10487, 5, prime_10487, prime_5, by norm_num⟩
  · exact ⟨10477, 11, prime_10477, prime_11, by norm_num⟩
  · exact ⟨10487, 7, prime_10487, prime_7, by norm_num⟩
  · exact ⟨10499, 2, prime_10499, prime_2, by norm_num⟩
  · exact ⟨10501, 2, prime_10501, prime_2, by norm_num⟩
  · exact ⟨10501, 3, prime_10501, prime_3, by norm_num⟩
  · exact ⟨10499, 5, prime_10499, prime_5, by norm_num⟩
  · exact ⟨10501, 5, prime_10501, prime_5, by norm_num⟩
  · exact ⟨10499, 7, prime_10499, prime_7, by norm_num⟩
  · exact ⟨10501, 7, prime_10501, prime_7, by norm_num⟩
  · exact ⟨10513, 2, prime_10513, prime_2, by norm_num⟩
  · exact ⟨10513, 3, prime_10513, prime_3, by norm_num⟩
  · exact ⟨10499, 11, prime_10499, prime_11, by norm_num⟩
  · exact ⟨10513, 5, prime_10513, prime_5, by norm_num⟩
  · exact ⟨10499, 13, prime_10499, prime_13, by norm_num⟩
  · exact ⟨10513, 7, prime_10513, prime_7, by norm_num⟩
  · exact ⟨10303, 113, prime_10303, prime_113, by norm_num⟩
  · exact ⟨10457, 37, prime_10457, prime_37, by norm_num⟩
  · exact ⟨10529, 2, prime_10529, prime_2, by norm_num⟩
  · exact ⟨10531, 2, prime_10531, prime_2, by norm_num⟩
  · exact ⟨10531, 3, prime_10531, prime_3, by norm_num⟩
  · exact ⟨10529, 5, prime_10529, prime_5, by norm_num⟩
  · exact ⟨10531, 5, prime_10531, prime_5, by norm_num⟩
  · exact ⟨10529, 7, prime_10529, prime_7, by norm_num⟩
  · exact ⟨10531, 7, prime_10531, prime_7, by norm_num⟩
  · exact ⟨10513, 17, prime_10513, prime_17, by norm_num⟩
  · exact ⟨10487, 31, prime_10487, prime_31, by norm_num⟩
  · exact ⟨10529, 11, prime_10529, prime_11, by norm_num⟩
  · exact ⟨10531, 11, prime_10531, prime_11, by norm_num⟩
  · exact ⟨10529, 13, prime_10529, prime_13, by norm_num⟩
  · exact ⟨10531, 13, prime_10531, prime_13, by norm_num⟩
  · exact ⟨10513, 23, prime_10513, prime_23, by norm_num⟩
  · exact ⟨10499, 31, prime_10499, prime_31, by norm_num⟩
  · exact ⟨10559, 2, prime_10559, prime_2, by norm_num⟩
  · exact ⟨10559, 3, prime_10559, prime_3, by norm_num⟩
  · exact ⟨10529, 19, prime_10529, prime_19, by norm_num⟩
  · exact ⟨10559, 5, prime_10559, prime_5, by norm_num⟩
  · exact ⟨10567, 2, prime_10567, prime_2, by norm_num⟩
  · exact ⟨10567, 3, prime_10567, prime_3, by norm_num⟩
  · exact ⟨10529, 23, prime_10529, prime_23, by norm_num⟩
  · exact ⟨10567, 5, prime_10567, prime_5, by norm_num⟩
  · exact ⟨10457, 61, prime_10457, prime_61, by norm_num⟩
  · exact ⟨10567, 7, prime_10567, prime_7, by norm_num⟩
  · exact ⟨10501, 41, prime_10501, prime_41, by norm_num⟩
  · exact ⟨10559, 13, prime_10559, prime_13, by norm_num⟩
  · exact ⟨10529, 29, prime_10529, prime_29, by norm_num⟩
  · exact ⟨10567, 11, prime_10567, prime_11, by norm_num⟩
  · exact ⟨10529, 31, prime_10529, prime_31, by norm_num⟩
  · exact ⟨10589, 2, prime_10589, prime_2, by norm_num⟩
  · exact ⟨10589, 3, prime_10589, prime_3, by norm_num⟩
  · exact ⟨10559, 19, prime_10559, prime_19, by norm_num⟩
  · exact ⟨10589, 5, prime_10589, prime_5, by norm_num⟩
  · exact ⟨10597, 2, prime_10597, prime_2, by norm_num⟩
  · exact ⟨10597, 3, prime_10597, prime_3, by norm_num⟩
  · exact ⟨10601, 2, prime_10601, prime_2, by norm_num⟩

private theorem lemoine_chunk_53 : ∀ k : ℕ, 5303 ≤ k → k ≤ 5402 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨10601, 3, prime_10601, prime_3, by norm_num⟩
  · exact ⟨10487, 61, prime_10487, prime_61, by norm_num⟩
  · exact ⟨10607, 2, prime_10607, prime_2, by norm_num⟩
  · exact ⟨10607, 3, prime_10607, prime_3, by norm_num⟩
  · exact ⟨10601, 7, prime_10601, prime_7, by norm_num⟩
  · exact ⟨10613, 2, prime_10613, prime_2, by norm_num⟩
  · exact ⟨10613, 3, prime_10613, prime_3, by norm_num⟩
  · exact ⟨10607, 7, prime_10607, prime_7, by norm_num⟩
  · exact ⟨10613, 5, prime_10613, prime_5, by norm_num⟩
  · exact ⟨10567, 29, prime_10567, prime_29, by norm_num⟩
  · exact ⟨10613, 7, prime_10613, prime_7, by norm_num⟩
  · exact ⟨10607, 11, prime_10607, prime_11, by norm_num⟩
  · exact ⟨10627, 2, prime_10627, prime_2, by norm_num⟩
  · exact ⟨10627, 3, prime_10627, prime_3, by norm_num⟩
  · exact ⟨10631, 2, prime_10631, prime_2, by norm_num⟩
  · exact ⟨10631, 3, prime_10631, prime_3, by norm_num⟩
  · exact ⟨10613, 13, prime_10613, prime_13, by norm_num⟩
  · exact ⟨10631, 5, prime_10631, prime_5, by norm_num⟩
  · exact ⟨10639, 2, prime_10639, prime_2, by norm_num⟩
  · exact ⟨10639, 3, prime_10639, prime_3, by norm_num⟩
  · exact ⟨10613, 17, prime_10613, prime_17, by norm_num⟩
  · exact ⟨10639, 5, prime_10639, prime_5, by norm_num⟩
  · exact ⟨10613, 19, prime_10613, prime_19, by norm_num⟩
  · exact ⟨10639, 7, prime_10639, prime_7, by norm_num⟩
  · exact ⟨10651, 2, prime_10651, prime_2, by norm_num⟩
  · exact ⟨10651, 3, prime_10651, prime_3, by norm_num⟩
  · exact ⟨10613, 23, prime_10613, prime_23, by norm_num⟩
  · exact ⟨10657, 2, prime_10657, prime_2, by norm_num⟩
  · exact ⟨10657, 3, prime_10657, prime_3, by norm_num⟩
  · exact ⟨10651, 7, prime_10651, prime_7, by norm_num⟩
  · exact ⟨10663, 2, prime_10663, prime_2, by norm_num⟩
  · exact ⟨10663, 3, prime_10663, prime_3, by norm_num⟩
  · exact ⟨10667, 2, prime_10667, prime_2, by norm_num⟩
  · exact ⟨10667, 3, prime_10667, prime_3, by norm_num⟩
  · exact ⟨10613, 31, prime_10613, prime_31, by norm_num⟩
  · exact ⟨10667, 5, prime_10667, prime_5, by norm_num⟩
  · exact ⟨10657, 11, prime_10657, prime_11, by norm_num⟩
  · exact ⟨10667, 7, prime_10667, prime_7, by norm_num⟩
  · exact ⟨10657, 13, prime_10657, prime_13, by norm_num⟩
  · exact ⟨10663, 11, prime_10663, prime_11, by norm_num⟩
  · exact ⟨10613, 37, prime_10613, prime_37, by norm_num⟩
  · exact ⟨10667, 11, prime_10667, prime_11, by norm_num⟩
  · exact ⟨10687, 2, prime_10687, prime_2, by norm_num⟩
  · exact ⟨10687, 3, prime_10687, prime_3, by norm_num⟩
  · exact ⟨10691, 2, prime_10691, prime_2, by norm_num⟩
  · exact ⟨10691, 3, prime_10691, prime_3, by norm_num⟩
  · exact ⟨10613, 43, prime_10613, prime_43, by norm_num⟩
  · exact ⟨10691, 5, prime_10691, prime_5, by norm_num⟩
  · exact ⟨10657, 23, prime_10657, prime_23, by norm_num⟩
  · exact ⟨10691, 7, prime_10691, prime_7, by norm_num⟩
  · exact ⟨10613, 47, prime_10613, prime_47, by norm_num⟩
  · exact ⟨10687, 11, prime_10687, prime_11, by norm_num⟩
  · exact ⟨10589, 61, prime_10589, prime_61, by norm_num⟩
  · exact ⟨10709, 2, prime_10709, prime_2, by norm_num⟩
  · exact ⟨10711, 2, prime_10711, prime_2, by norm_num⟩
  · exact ⟨10711, 3, prime_10711, prime_3, by norm_num⟩
  · exact ⟨10709, 5, prime_10709, prime_5, by norm_num⟩
  · exact ⟨10711, 5, prime_10711, prime_5, by norm_num⟩
  · exact ⟨10709, 7, prime_10709, prime_7, by norm_num⟩
  · exact ⟨10711, 7, prime_10711, prime_7, by norm_num⟩
  · exact ⟨10723, 2, prime_10723, prime_2, by norm_num⟩
  · exact ⟨10723, 3, prime_10723, prime_3, by norm_num⟩
  · exact ⟨10709, 11, prime_10709, prime_11, by norm_num⟩
  · exact ⟨10729, 2, prime_10729, prime_2, by norm_num⟩
  · exact ⟨10729, 3, prime_10729, prime_3, by norm_num⟩
  · exact ⟨10733, 2, prime_10733, prime_2, by norm_num⟩
  · exact ⟨10733, 3, prime_10733, prime_3, by norm_num⟩
  · exact ⟨10667, 37, prime_10667, prime_37, by norm_num⟩
  · exact ⟨10739, 2, prime_10739, prime_2, by norm_num⟩
  · exact ⟨10739, 3, prime_10739, prime_3, by norm_num⟩
  · exact ⟨10733, 7, prime_10733, prime_7, by norm_num⟩
  · exact ⟨10739, 5, prime_10739, prime_5, by norm_num⟩
  · exact ⟨10729, 11, prime_10729, prime_11, by norm_num⟩
  · exact ⟨10739, 7, prime_10739, prime_7, by norm_num⟩
  · exact ⟨10733, 11, prime_10733, prime_11, by norm_num⟩
  · exact ⟨10753, 2, prime_10753, prime_2, by norm_num⟩
  · exact ⟨10753, 3, prime_10753, prime_3, by norm_num⟩
  · exact ⟨10739, 11, prime_10739, prime_11, by norm_num⟩
  · exact ⟨10753, 5, prime_10753, prime_5, by norm_num⟩
  · exact ⟨10739, 13, prime_10739, prime_13, by norm_num⟩
  · exact ⟨10753, 7, prime_10753, prime_7, by norm_num⟩
  · exact ⟨10723, 23, prime_10723, prime_23, by norm_num⟩
  · exact ⟨10733, 19, prime_10733, prime_19, by norm_num⟩
  · exact ⟨10739, 17, prime_10739, prime_17, by norm_num⟩
  · exact ⟨10771, 2, prime_10771, prime_2, by norm_num⟩
  · exact ⟨10771, 3, prime_10771, prime_3, by norm_num⟩
  · exact ⟨10753, 13, prime_10753, prime_13, by norm_num⟩
  · exact ⟨10771, 5, prime_10771, prime_5, by norm_num⟩
  · exact ⟨10709, 37, prime_10709, prime_37, by norm_num⟩
  · exact ⟨10781, 2, prime_10781, prime_2, by norm_num⟩
  · exact ⟨10781, 3, prime_10781, prime_3, by norm_num⟩
  · exact ⟨10667, 61, prime_10667, prime_61, by norm_num⟩
  · exact ⟨10781, 5, prime_10781, prime_5, by norm_num⟩
  · exact ⟨10789, 2, prime_10789, prime_2, by norm_num⟩
  · exact ⟨10789, 3, prime_10789, prime_3, by norm_num⟩
  · exact ⟨10771, 13, prime_10771, prime_13, by norm_num⟩
  · exact ⟨10789, 5, prime_10789, prime_5, by norm_num⟩
  · exact ⟨10739, 31, prime_10739, prime_31, by norm_num⟩
  · exact ⟨10799, 2, prime_10799, prime_2, by norm_num⟩
  · exact ⟨10799, 3, prime_10799, prime_3, by norm_num⟩

private theorem lemoine_chunk_54 : ∀ k : ℕ, 5403 ≤ k → k ≤ 5502 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨10781, 13, prime_10781, prime_13, by norm_num⟩
  · exact ⟨10799, 5, prime_10799, prime_5, by norm_num⟩
  · exact ⟨10789, 11, prime_10789, prime_11, by norm_num⟩
  · exact ⟨10799, 7, prime_10799, prime_7, by norm_num⟩
  · exact ⟨10789, 13, prime_10789, prime_13, by norm_num⟩
  · exact ⟨10771, 23, prime_10771, prime_23, by norm_num⟩
  · exact ⟨10781, 19, prime_10781, prime_19, by norm_num⟩
  · exact ⟨10799, 11, prime_10799, prime_11, by norm_num⟩
  · exact ⟨10789, 17, prime_10789, prime_17, by norm_num⟩
  · exact ⟨10799, 13, prime_10799, prime_13, by norm_num⟩
  · exact ⟨10789, 19, prime_10789, prime_19, by norm_num⟩
  · exact ⟨10771, 29, prime_10771, prime_29, by norm_num⟩
  · exact ⟨10709, 61, prime_10709, prime_61, by norm_num⟩
  · exact ⟨10799, 17, prime_10799, prime_17, by norm_num⟩
  · exact ⟨10831, 2, prime_10831, prime_2, by norm_num⟩
  · exact ⟨10831, 3, prime_10831, prime_3, by norm_num⟩
  · exact ⟨10781, 29, prime_10781, prime_29, by norm_num⟩
  · exact ⟨10837, 2, prime_10837, prime_2, by norm_num⟩
  · exact ⟨10837, 3, prime_10837, prime_3, by norm_num⟩
  · exact ⟨10831, 7, prime_10831, prime_7, by norm_num⟩
  · exact ⟨10837, 5, prime_10837, prime_5, by norm_num⟩
  · exact ⟨10691, 79, prime_10691, prime_79, by norm_num⟩
  · exact ⟨10847, 2, prime_10847, prime_2, by norm_num⟩
  · exact ⟨10847, 3, prime_10847, prime_3, by norm_num⟩
  · exact ⟨10781, 37, prime_10781, prime_37, by norm_num⟩
  · exact ⟨10853, 2, prime_10853, prime_2, by norm_num⟩
  · exact ⟨10853, 3, prime_10853, prime_3, by norm_num⟩
  · exact ⟨10847, 7, prime_10847, prime_7, by norm_num⟩
  · exact ⟨10859, 2, prime_10859, prime_2, by norm_num⟩
  · exact ⟨10861, 2, prime_10861, prime_2, by norm_num⟩
  · exact ⟨10861, 3, prime_10861, prime_3, by norm_num⟩
  · exact ⟨10859, 5, prime_10859, prime_5, by norm_num⟩
  · exact ⟨10867, 2, prime_10867, prime_2, by norm_num⟩
  · exact ⟨10867, 3, prime_10867, prime_3, by norm_num⟩
  · exact ⟨10861, 7, prime_10861, prime_7, by norm_num⟩
  · exact ⟨10867, 5, prime_10867, prime_5, by norm_num⟩
  · exact ⟨10853, 13, prime_10853, prime_13, by norm_num⟩
  · exact ⟨10867, 7, prime_10867, prime_7, by norm_num⟩
  · exact ⟨10861, 11, prime_10861, prime_11, by norm_num⟩
  · exact ⟨10859, 13, prime_10859, prime_13, by norm_num⟩
  · exact ⟨10883, 2, prime_10883, prime_2, by norm_num⟩
  · exact ⟨10883, 3, prime_10883, prime_3, by norm_num⟩
  · exact ⟨10853, 19, prime_10853, prime_19, by norm_num⟩
  · exact ⟨10889, 2, prime_10889, prime_2, by norm_num⟩
  · exact ⟨10891, 2, prime_10891, prime_2, by norm_num⟩
  · exact ⟨10891, 3, prime_10891, prime_3, by norm_num⟩
  · exact ⟨10889, 5, prime_10889, prime_5, by norm_num⟩
  · exact ⟨10891, 5, prime_10891, prime_5, by norm_num⟩
  · exact ⟨10889, 7, prime_10889, prime_7, by norm_num⟩
  · exact ⟨10891, 7, prime_10891, prime_7, by norm_num⟩
  · exact ⟨10903, 2, prime_10903, prime_2, by norm_num⟩
  · exact ⟨10903, 3, prime_10903, prime_3, by norm_num⟩
  · exact ⟨10889, 11, prime_10889, prime_11, by norm_num⟩
  · exact ⟨10909, 2, prime_10909, prime_2, by norm_num⟩
  · exact ⟨10909, 3, prime_10909, prime_3, by norm_num⟩
  · exact ⟨10903, 7, prime_10903, prime_7, by norm_num⟩
  · exact ⟨10909, 5, prime_10909, prime_5, by norm_num⟩
  · exact ⟨10883, 19, prime_10883, prime_19, by norm_num⟩
  · exact ⟨10909, 7, prime_10909, prime_7, by norm_num⟩
  · exact ⟨10903, 11, prime_10903, prime_11, by norm_num⟩
  · exact ⟨10889, 19, prime_10889, prime_19, by norm_num⟩
  · exact ⟨10903, 13, prime_10903, prime_13, by norm_num⟩
  · exact ⟨10909, 11, prime_10909, prime_11, by norm_num⟩
  · exact ⟨10859, 37, prime_10859, prime_37, by norm_num⟩
  · exact ⟨10909, 13, prime_10909, prime_13, by norm_num⟩
  · exact ⟨10903, 17, prime_10903, prime_17, by norm_num⟩
  · exact ⟨10853, 43, prime_10853, prime_43, by norm_num⟩
  · exact ⟨10937, 2, prime_10937, prime_2, by norm_num⟩
  · exact ⟨10939, 2, prime_10939, prime_2, by norm_num⟩
  · exact ⟨10939, 3, prime_10939, prime_3, by norm_num⟩
  · exact ⟨10937, 5, prime_10937, prime_5, by norm_num⟩
  · exact ⟨10939, 5, prime_10939, prime_5, by norm_num⟩
  · exact ⟨10937, 7, prime_10937, prime_7, by norm_num⟩
  · exact ⟨10949, 2, prime_10949, prime_2, by norm_num⟩
  · exact ⟨10949, 3, prime_10949, prime_3, by norm_num⟩
  · exact ⟨10883, 37, prime_10883, prime_37, by norm_num⟩
  · exact ⟨10949, 5, prime_10949, prime_5, by norm_num⟩
  · exact ⟨10957, 2, prime_10957, prime_2, by norm_num⟩
  · exact ⟨10957, 3, prime_10957, prime_3, by norm_num⟩
  · exact ⟨10939, 13, prime_10939, prime_13, by norm_num⟩
  · exact ⟨10957, 5, prime_10957, prime_5, by norm_num⟩
  · exact ⟨10883, 43, prime_10883, prime_43, by norm_num⟩
  · exact ⟨10957, 7, prime_10957, prime_7, by norm_num⟩
  · exact ⟨10939, 17, prime_10939, prime_17, by norm_num⟩
  · exact ⟨10949, 13, prime_10949, prime_13, by norm_num⟩
  · exact ⟨10973, 2, prime_10973, prime_2, by norm_num⟩
  · exact ⟨10973, 3, prime_10973, prime_3, by norm_num⟩
  · exact ⟨10859, 61, prime_10859, prime_61, by norm_num⟩
  · exact ⟨10979, 2, prime_10979, prime_2, by norm_num⟩
  · exact ⟨10979, 3, prime_10979, prime_3, by norm_num⟩
  · exact ⟨10973, 7, prime_10973, prime_7, by norm_num⟩
  · exact ⟨10979, 5, prime_10979, prime_5, by norm_num⟩
  · exact ⟨10987, 2, prime_10987, prime_2, by norm_num⟩
  · exact ⟨10987, 3, prime_10987, prime_3, by norm_num⟩
  · exact ⟨10973, 11, prime_10973, prime_11, by norm_num⟩
  · exact ⟨10993, 2, prime_10993, prime_2, by norm_num⟩
  · exact ⟨10993, 3, prime_10993, prime_3, by norm_num⟩
  · exact ⟨10987, 7, prime_10987, prime_7, by norm_num⟩
  · exact ⟨10993, 5, prime_10993, prime_5, by norm_num⟩
  · exact ⟨10979, 13, prime_10979, prime_13, by norm_num⟩

private theorem lemoine_chunk_55 : ∀ k : ℕ, 5503 ≤ k → k ≤ 5602 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨11003, 2, prime_11003, prime_2, by norm_num⟩
  · exact ⟨11003, 3, prime_11003, prime_3, by norm_num⟩
  · exact ⟨10973, 19, prime_10973, prime_19, by norm_num⟩
  · exact ⟨11003, 5, prime_11003, prime_5, by norm_num⟩
  · exact ⟨10993, 11, prime_10993, prime_11, by norm_num⟩
  · exact ⟨11003, 7, prime_11003, prime_7, by norm_num⟩
  · exact ⟨10993, 13, prime_10993, prime_13, by norm_num⟩
  · exact ⟨10987, 17, prime_10987, prime_17, by norm_num⟩
  · exact ⟨10949, 37, prime_10949, prime_37, by norm_num⟩
  · exact ⟨11003, 11, prime_11003, prime_11, by norm_num⟩
  · exact ⟨10993, 17, prime_10993, prime_17, by norm_num⟩
  · exact ⟨11003, 13, prime_11003, prime_13, by norm_num⟩
  · exact ⟨11027, 2, prime_11027, prime_2, by norm_num⟩
  · exact ⟨11027, 3, prime_11027, prime_3, by norm_num⟩
  · exact ⟨10973, 31, prime_10973, prime_31, by norm_num⟩
  · exact ⟨11027, 5, prime_11027, prime_5, by norm_num⟩
  · exact ⟨10993, 23, prime_10993, prime_23, by norm_num⟩
  · exact ⟨11027, 7, prime_11027, prime_7, by norm_num⟩
  · exact ⟨10957, 43, prime_10957, prime_43, by norm_num⟩
  · exact ⟨10987, 29, prime_10987, prime_29, by norm_num⟩
  · exact ⟨10973, 37, prime_10973, prime_37, by norm_num⟩
  · exact ⟨11027, 11, prime_11027, prime_11, by norm_num⟩
  · exact ⟨11047, 2, prime_11047, prime_2, by norm_num⟩
  · exact ⟨11047, 3, prime_11047, prime_3, by norm_num⟩
  · exact ⟨10993, 31, prime_10993, prime_31, by norm_num⟩
  · exact ⟨11047, 5, prime_11047, prime_5, by norm_num⟩
  · exact ⟨10973, 43, prime_10973, prime_43, by norm_num⟩
  · exact ⟨11057, 2, prime_11057, prime_2, by norm_num⟩
  · exact ⟨11059, 2, prime_11059, prime_2, by norm_num⟩
  · exact ⟨11059, 3, prime_11059, prime_3, by norm_num⟩
  · exact ⟨11057, 5, prime_11057, prime_5, by norm_num⟩
  · exact ⟨11059, 5, prime_11059, prime_5, by norm_num⟩
  · exact ⟨11057, 7, prime_11057, prime_7, by norm_num⟩
  · exact ⟨11069, 2, prime_11069, prime_2, by norm_num⟩
  · exact ⟨11071, 2, prime_11071, prime_2, by norm_num⟩
  · exact ⟨11071, 3, prime_11071, prime_3, by norm_num⟩
  · exact ⟨11069, 5, prime_11069, prime_5, by norm_num⟩
  · exact ⟨11071, 5, prime_11071, prime_5, by norm_num⟩
  · exact ⟨11069, 7, prime_11069, prime_7, by norm_num⟩
  · exact ⟨11071, 7, prime_11071, prime_7, by norm_num⟩
  · exact ⟨11083, 2, prime_11083, prime_2, by norm_num⟩
  · exact ⟨11083, 3, prime_11083, prime_3, by norm_num⟩
  · exact ⟨11087, 2, prime_11087, prime_2, by norm_num⟩
  · exact ⟨11087, 3, prime_11087, prime_3, by norm_num⟩
  · exact ⟨11069, 13, prime_11069, prime_13, by norm_num⟩
  · exact ⟨11093, 2, prime_11093, prime_2, by norm_num⟩
  · exact ⟨11093, 3, prime_11093, prime_3, by norm_num⟩
  · exact ⟨11087, 7, prime_11087, prime_7, by norm_num⟩
  · exact ⟨11093, 5, prime_11093, prime_5, by norm_num⟩
  · exact ⟨11083, 11, prime_11083, prime_11, by norm_num⟩
  · exact ⟨11093, 7, prime_11093, prime_7, by norm_num⟩
  · exact ⟨11087, 11, prime_11087, prime_11, by norm_num⟩
  · exact ⟨10993, 59, prime_10993, prime_59, by norm_num⟩
  · exact ⟨11087, 13, prime_11087, prime_13, by norm_num⟩
  · exact ⟨11093, 11, prime_11093, prime_11, by norm_num⟩
  · exact ⟨11113, 2, prime_11113, prime_2, by norm_num⟩
  · exact ⟨11113, 3, prime_11113, prime_3, by norm_num⟩
  · exact ⟨11117, 2, prime_11117, prime_2, by norm_num⟩
  · exact ⟨11119, 2, prime_11119, prime_2, by norm_num⟩
  · exact ⟨11119, 3, prime_11119, prime_3, by norm_num⟩
  · exact ⟨11117, 5, prime_11117, prime_5, by norm_num⟩
  · exact ⟨11119, 5, prime_11119, prime_5, by norm_num⟩
  · exact ⟨11117, 7, prime_11117, prime_7, by norm_num⟩
  · exact ⟨11119, 7, prime_11119, prime_7, by norm_num⟩
  · exact ⟨11131, 2, prime_11131, prime_2, by norm_num⟩
  · exact ⟨11131, 3, prime_11131, prime_3, by norm_num⟩
  · exact ⟨11117, 11, prime_11117, prime_11, by norm_num⟩
  · exact ⟨11131, 5, prime_11131, prime_5, by norm_num⟩
  · exact ⟨11117, 13, prime_11117, prime_13, by norm_num⟩
  · exact ⟨11131, 7, prime_11131, prime_7, by norm_num⟩
  · exact ⟨11113, 17, prime_11113, prime_17, by norm_num⟩
  · exact ⟨11087, 31, prime_11087, prime_31, by norm_num⟩
  · exact ⟨11117, 17, prime_11117, prime_17, by norm_num⟩
  · exact ⟨11149, 2, prime_11149, prime_2, by norm_num⟩
  · exact ⟨11149, 3, prime_11149, prime_3, by norm_num⟩
  · exact ⟨11131, 13, prime_11131, prime_13, by norm_num⟩
  · exact ⟨11149, 5, prime_11149, prime_5, by norm_num⟩
  · exact ⟨11087, 37, prime_11087, prime_37, by norm_num⟩
  · exact ⟨11159, 2, prime_11159, prime_2, by norm_num⟩
  · exact ⟨11161, 2, prime_11161, prime_2, by norm_num⟩
  · exact ⟨11161, 3, prime_11161, prime_3, by norm_num⟩
  · exact ⟨11159, 5, prime_11159, prime_5, by norm_num⟩
  · exact ⟨11161, 5, prime_11161, prime_5, by norm_num⟩
  · exact ⟨11159, 7, prime_11159, prime_7, by norm_num⟩
  · exact ⟨11171, 2, prime_11171, prime_2, by norm_num⟩
  · exact ⟨11173, 2, prime_11173, prime_2, by norm_num⟩
  · exact ⟨11173, 3, prime_11173, prime_3, by norm_num⟩
  · exact ⟨11177, 2, prime_11177, prime_2, by norm_num⟩
  · exact ⟨11177, 3, prime_11177, prime_3, by norm_num⟩
  · exact ⟨11171, 7, prime_11171, prime_7, by norm_num⟩
  · exact ⟨11177, 5, prime_11177, prime_5, by norm_num⟩
  · exact ⟨11131, 29, prime_11131, prime_29, by norm_num⟩
  · exact ⟨11177, 7, prime_11177, prime_7, by norm_num⟩
  · exact ⟨11171, 11, prime_11171, prime_11, by norm_num⟩
  · exact ⟨11173, 11, prime_11173, prime_11, by norm_num⟩
  · exact ⟨11171, 13, prime_11171, prime_13, by norm_num⟩
  · exact ⟨11177, 11, prime_11177, prime_11, by norm_num⟩
  · exact ⟨11197, 2, prime_11197, prime_2, by norm_num⟩
  · exact ⟨11197, 3, prime_11197, prime_3, by norm_num⟩
  · exact ⟨11171, 17, prime_11171, prime_17, by norm_num⟩

private theorem lemoine_chunk_56 : ∀ k : ℕ, 5603 ≤ k → k ≤ 5702 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨11197, 5, prime_11197, prime_5, by norm_num⟩
  · exact ⟨11171, 19, prime_11171, prime_19, by norm_num⟩
  · exact ⟨11197, 7, prime_11197, prime_7, by norm_num⟩
  · exact ⟨11131, 41, prime_11131, prime_41, by norm_num⟩
  · exact ⟨11177, 19, prime_11177, prime_19, by norm_num⟩
  · exact ⟨11213, 2, prime_11213, prime_2, by norm_num⟩
  · exact ⟨11213, 3, prime_11213, prime_3, by norm_num⟩
  · exact ⟨11159, 31, prime_11159, prime_31, by norm_num⟩
  · exact ⟨11213, 5, prime_11213, prime_5, by norm_num⟩
  · exact ⟨11131, 47, prime_11131, prime_47, by norm_num⟩
  · exact ⟨11213, 7, prime_11213, prime_7, by norm_num⟩
  · exact ⟨11171, 29, prime_11171, prime_29, by norm_num⟩
  · exact ⟨11197, 17, prime_11197, prime_17, by norm_num⟩
  · exact ⟨11171, 31, prime_11171, prime_31, by norm_num⟩
  · exact ⟨11213, 11, prime_11213, prime_11, by norm_num⟩
  · exact ⟨11131, 53, prime_11131, prime_53, by norm_num⟩
  · exact ⟨11213, 13, prime_11213, prime_13, by norm_num⟩
  · exact ⟨11159, 41, prime_11159, prime_41, by norm_num⟩
  · exact ⟨11239, 2, prime_11239, prime_2, by norm_num⟩
  · exact ⟨11239, 3, prime_11239, prime_3, by norm_num⟩
  · exact ⟨11243, 2, prime_11243, prime_2, by norm_num⟩
  · exact ⟨11243, 3, prime_11243, prime_3, by norm_num⟩
  · exact ⟨11213, 19, prime_11213, prime_19, by norm_num⟩
  · exact ⟨11243, 5, prime_11243, prime_5, by norm_num⟩
  · exact ⟨11251, 2, prime_11251, prime_2, by norm_num⟩
  · exact ⟨11251, 3, prime_11251, prime_3, by norm_num⟩
  · exact ⟨11213, 23, prime_11213, prime_23, by norm_num⟩
  · exact ⟨11257, 2, prime_11257, prime_2, by norm_num⟩
  · exact ⟨11257, 3, prime_11257, prime_3, by norm_num⟩
  · exact ⟨11261, 2, prime_11261, prime_2, by norm_num⟩
  · exact ⟨11261, 3, prime_11261, prime_3, by norm_num⟩
  · exact ⟨11243, 13, prime_11243, prime_13, by norm_num⟩
  · exact ⟨11261, 5, prime_11261, prime_5, by norm_num⟩
  · exact ⟨11251, 11, prime_11251, prime_11, by norm_num⟩
  · exact ⟨11261, 7, prime_11261, prime_7, by norm_num⟩
  · exact ⟨11273, 2, prime_11273, prime_2, by norm_num⟩
  · exact ⟨11273, 3, prime_11273, prime_3, by norm_num⟩
  · exact ⟨11243, 19, prime_11243, prime_19, by norm_num⟩
  · exact ⟨11279, 2, prime_11279, prime_2, by norm_num⟩
  · exact ⟨11279, 3, prime_11279, prime_3, by norm_num⟩
  · exact ⟨11273, 7, prime_11273, prime_7, by norm_num⟩
  · exact ⟨11279, 5, prime_11279, prime_5, by norm_num⟩
  · exact ⟨11287, 2, prime_11287, prime_2, by norm_num⟩
  · exact ⟨11287, 3, prime_11287, prime_3, by norm_num⟩
  · exact ⟨11273, 11, prime_11273, prime_11, by norm_num⟩
  · exact ⟨11287, 5, prime_11287, prime_5, by norm_num⟩
  · exact ⟨11273, 13, prime_11273, prime_13, by norm_num⟩
  · exact ⟨11287, 7, prime_11287, prime_7, by norm_num⟩
  · exact ⟨11299, 2, prime_11299, prime_2, by norm_num⟩
  · exact ⟨11299, 3, prime_11299, prime_3, by norm_num⟩
  · exact ⟨11273, 17, prime_11273, prime_17, by norm_num⟩
  · exact ⟨11299, 5, prime_11299, prime_5, by norm_num⟩
  · exact ⟨11273, 19, prime_11273, prime_19, by norm_num⟩
  · exact ⟨11299, 7, prime_11299, prime_7, by norm_num⟩
  · exact ⟨11311, 2, prime_11311, prime_2, by norm_num⟩
  · exact ⟨11311, 3, prime_11311, prime_3, by norm_num⟩
  · exact ⟨11273, 23, prime_11273, prime_23, by norm_num⟩
  · exact ⟨11317, 2, prime_11317, prime_2, by norm_num⟩
  · exact ⟨11317, 3, prime_11317, prime_3, by norm_num⟩
  · exact ⟨11321, 2, prime_11321, prime_2, by norm_num⟩
  · exact ⟨11321, 3, prime_11321, prime_3, by norm_num⟩
  · exact ⟨11243, 43, prime_11243, prime_43, by norm_num⟩
  · exact ⟨11321, 5, prime_11321, prime_5, by norm_num⟩
  · exact ⟨11329, 2, prime_11329, prime_2, by norm_num⟩
  · exact ⟨11329, 3, prime_11329, prime_3, by norm_num⟩
  · exact ⟨11311, 13, prime_11311, prime_13, by norm_num⟩
  · exact ⟨11329, 5, prime_11329, prime_5, by norm_num⟩
  · exact ⟨11279, 31, prime_11279, prime_31, by norm_num⟩
  · exact ⟨11329, 7, prime_11329, prime_7, by norm_num⟩
  · exact ⟨11311, 17, prime_11311, prime_17, by norm_num⟩
  · exact ⟨11321, 13, prime_11321, prime_13, by norm_num⟩
  · exact ⟨11311, 19, prime_11311, prime_19, by norm_num⟩
  · exact ⟨11329, 11, prime_11329, prime_11, by norm_num⟩
  · exact ⟨11279, 37, prime_11279, prime_37, by norm_num⟩
  · exact ⟨11351, 2, prime_11351, prime_2, by norm_num⟩
  · exact ⟨11353, 2, prime_11353, prime_2, by norm_num⟩
  · exact ⟨11353, 3, prime_11353, prime_3, by norm_num⟩
  · exact ⟨11351, 5, prime_11351, prime_5, by norm_num⟩
  · exact ⟨11353, 5, prime_11353, prime_5, by norm_num⟩
  · exact ⟨11351, 7, prime_11351, prime_7, by norm_num⟩
  · exact ⟨11353, 7, prime_11353, prime_7, by norm_num⟩
  · exact ⟨11311, 29, prime_11311, prime_29, by norm_num⟩
  · exact ⟨11213, 79, prime_11213, prime_79, by norm_num⟩
  · exact ⟨11369, 2, prime_11369, prime_2, by norm_num⟩
  · exact ⟨11369, 3, prime_11369, prime_3, by norm_num⟩
  · exact ⟨11351, 13, prime_11351, prime_13, by norm_num⟩
  · exact ⟨11369, 5, prime_11369, prime_5, by norm_num⟩
  · exact ⟨11299, 41, prime_11299, prime_41, by norm_num⟩
  · exact ⟨11369, 7, prime_11369, prime_7, by norm_num⟩
  · exact ⟨11351, 17, prime_11351, prime_17, by norm_num⟩
  · exact ⟨11383, 2, prime_11383, prime_2, by norm_num⟩
  · exact ⟨11383, 3, prime_11383, prime_3, by norm_num⟩
  · exact ⟨11369, 11, prime_11369, prime_11, by norm_num⟩
  · exact ⟨11383, 5, prime_11383, prime_5, by norm_num⟩
  · exact ⟨11369, 13, prime_11369, prime_13, by norm_num⟩
  · exact ⟨11393, 2, prime_11393, prime_2, by norm_num⟩
  · exact ⟨11393, 3, prime_11393, prime_3, by norm_num⟩
  · exact ⟨11279, 61, prime_11279, prime_61, by norm_num⟩
  · exact ⟨11399, 2, prime_11399, prime_2, by norm_num⟩
  · exact ⟨11399, 3, prime_11399, prime_3, by norm_num⟩

private theorem lemoine_chunk_57 : ∀ k : ℕ, 5703 ≤ k → k ≤ 5802 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨11393, 7, prime_11393, prime_7, by norm_num⟩
  · exact ⟨11399, 5, prime_11399, prime_5, by norm_num⟩
  · exact ⟨11353, 29, prime_11353, prime_29, by norm_num⟩
  · exact ⟨11399, 7, prime_11399, prime_7, by norm_num⟩
  · exact ⟨11411, 2, prime_11411, prime_2, by norm_num⟩
  · exact ⟨11411, 3, prime_11411, prime_3, by norm_num⟩
  · exact ⟨11393, 13, prime_11393, prime_13, by norm_num⟩
  · exact ⟨11411, 5, prime_11411, prime_5, by norm_num⟩
  · exact ⟨11329, 47, prime_11329, prime_47, by norm_num⟩
  · exact ⟨11411, 7, prime_11411, prime_7, by norm_num⟩
  · exact ⟨11423, 2, prime_11423, prime_2, by norm_num⟩
  · exact ⟨11423, 3, prime_11423, prime_3, by norm_num⟩
  · exact ⟨11393, 19, prime_11393, prime_19, by norm_num⟩
  · exact ⟨11423, 5, prime_11423, prime_5, by norm_num⟩
  · exact ⟨11353, 41, prime_11353, prime_41, by norm_num⟩
  · exact ⟨11423, 7, prime_11423, prime_7, by norm_num⟩
  · exact ⟨11393, 23, prime_11393, prime_23, by norm_num⟩
  · exact ⟨11437, 2, prime_11437, prime_2, by norm_num⟩
  · exact ⟨11437, 3, prime_11437, prime_3, by norm_num⟩
  · exact ⟨11423, 11, prime_11423, prime_11, by norm_num⟩
  · exact ⟨11443, 2, prime_11443, prime_2, by norm_num⟩
  · exact ⟨11443, 3, prime_11443, prime_3, by norm_num⟩
  · exact ⟨11447, 2, prime_11447, prime_2, by norm_num⟩
  · exact ⟨11447, 3, prime_11447, prime_3, by norm_num⟩
  · exact ⟨11393, 31, prime_11393, prime_31, by norm_num⟩
  · exact ⟨11447, 5, prime_11447, prime_5, by norm_num⟩
  · exact ⟨11437, 11, prime_11437, prime_11, by norm_num⟩
  · exact ⟨11447, 7, prime_11447, prime_7, by norm_num⟩
  · exact ⟨11437, 13, prime_11437, prime_13, by norm_num⟩
  · exact ⟨11443, 11, prime_11443, prime_11, by norm_num⟩
  · exact ⟨11393, 37, prime_11393, prime_37, by norm_num⟩
  · exact ⟨11447, 11, prime_11447, prime_11, by norm_num⟩
  · exact ⟨11467, 2, prime_11467, prime_2, by norm_num⟩
  · exact ⟨11467, 3, prime_11467, prime_3, by norm_num⟩
  · exact ⟨11471, 2, prime_11471, prime_2, by norm_num⟩
  · exact ⟨11471, 3, prime_11471, prime_3, by norm_num⟩
  · exact ⟨11393, 43, prime_11393, prime_43, by norm_num⟩
  · exact ⟨11471, 5, prime_11471, prime_5, by norm_num⟩
  · exact ⟨11437, 23, prime_11437, prime_23, by norm_num⟩
  · exact ⟨11471, 7, prime_11471, prime_7, by norm_num⟩
  · exact ⟨11483, 2, prime_11483, prime_2, by norm_num⟩
  · exact ⟨11483, 3, prime_11483, prime_3, by norm_num⟩
  · exact ⟨11369, 61, prime_11369, prime_61, by norm_num⟩
  · exact ⟨11489, 2, prime_11489, prime_2, by norm_num⟩
  · exact ⟨11491, 2, prime_11491, prime_2, by norm_num⟩
  · exact ⟨11491, 3, prime_11491, prime_3, by norm_num⟩
  · exact ⟨11489, 5, prime_11489, prime_5, by norm_num⟩
  · exact ⟨11497, 2, prime_11497, prime_2, by norm_num⟩
  · exact ⟨11497, 3, prime_11497, prime_3, by norm_num⟩
  · exact ⟨11491, 7, prime_11491, prime_7, by norm_num⟩
  · exact ⟨11503, 2, prime_11503, prime_2, by norm_num⟩
  · exact ⟨11503, 3, prime_11503, prime_3, by norm_num⟩
  · exact ⟨11497, 7, prime_11497, prime_7, by norm_num⟩
  · exact ⟨11503, 5, prime_11503, prime_5, by norm_num⟩
  · exact ⟨11489, 13, prime_11489, prime_13, by norm_num⟩
  · exact ⟨11503, 7, prime_11503, prime_7, by norm_num⟩
  · exact ⟨11497, 11, prime_11497, prime_11, by norm_num⟩
  · exact ⟨11483, 19, prime_11483, prime_19, by norm_num⟩
  · exact ⟨11519, 2, prime_11519, prime_2, by norm_num⟩
  · exact ⟨11519, 3, prime_11519, prime_3, by norm_num⟩
  · exact ⟨11489, 19, prime_11489, prime_19, by norm_num⟩
  · exact ⟨11519, 5, prime_11519, prime_5, by norm_num⟩
  · exact ⟨11527, 2, prime_11527, prime_2, by norm_num⟩
  · exact ⟨11527, 3, prime_11527, prime_3, by norm_num⟩
  · exact ⟨11497, 19, prime_11497, prime_19, by norm_num⟩
  · exact ⟨11527, 5, prime_11527, prime_5, by norm_num⟩
  · exact ⟨11393, 73, prime_11393, prime_73, by norm_num⟩
  · exact ⟨11527, 7, prime_11527, prime_7, by norm_num⟩
  · exact ⟨11497, 23, prime_11497, prime_23, by norm_num⟩
  · exact ⟨11519, 13, prime_11519, prime_13, by norm_num⟩
  · exact ⟨11489, 29, prime_11489, prime_29, by norm_num⟩
  · exact ⟨11527, 11, prime_11527, prime_11, by norm_num⟩
  · exact ⟨11489, 31, prime_11489, prime_31, by norm_num⟩
  · exact ⟨11549, 2, prime_11549, prime_2, by norm_num⟩
  · exact ⟨11551, 2, prime_11551, prime_2, by norm_num⟩
  · exact ⟨11551, 3, prime_11551, prime_3, by norm_num⟩
  · exact ⟨11549, 5, prime_11549, prime_5, by norm_num⟩
  · exact ⟨11551, 5, prime_11551, prime_5, by norm_num⟩
  · exact ⟨11549, 7, prime_11549, prime_7, by norm_num⟩
  · exact ⟨11551, 7, prime_11551, prime_7, by norm_num⟩
  · exact ⟨11353, 107, prime_11353, prime_107, by norm_num⟩
  · exact ⟨11483, 43, prime_11483, prime_43, by norm_num⟩
  · exact ⟨11549, 11, prime_11549, prime_11, by norm_num⟩
  · exact ⟨11551, 11, prime_11551, prime_11, by norm_num⟩
  · exact ⟨11549, 13, prime_11549, prime_13, by norm_num⟩
  · exact ⟨11551, 13, prime_11551, prime_13, by norm_num⟩
  · exact ⟨11497, 41, prime_11497, prime_41, by norm_num⟩
  · exact ⟨11519, 31, prime_11519, prime_31, by norm_num⟩
  · exact ⟨11579, 2, prime_11579, prime_2, by norm_num⟩
  · exact ⟨11579, 3, prime_11579, prime_3, by norm_num⟩
  · exact ⟨11549, 19, prime_11549, prime_19, by norm_num⟩
  · exact ⟨11579, 5, prime_11579, prime_5, by norm_num⟩
  · exact ⟨11587, 2, prime_11587, prime_2, by norm_num⟩
  · exact ⟨11587, 3, prime_11587, prime_3, by norm_num⟩
  · exact ⟨11549, 23, prime_11549, prime_23, by norm_num⟩
  · exact ⟨11593, 2, prime_11593, prime_2, by norm_num⟩
  · exact ⟨11593, 3, prime_11593, prime_3, by norm_num⟩
  · exact ⟨11597, 2, prime_11597, prime_2, by norm_num⟩
  · exact ⟨11597, 3, prime_11597, prime_3, by norm_num⟩
  · exact ⟨11579, 13, prime_11579, prime_13, by norm_num⟩

private theorem lemoine_chunk_58 : ∀ k : ℕ, 5803 ≤ k → k ≤ 5902 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨11597, 5, prime_11597, prime_5, by norm_num⟩
  · exact ⟨11587, 11, prime_11587, prime_11, by norm_num⟩
  · exact ⟨11597, 7, prime_11597, prime_7, by norm_num⟩
  · exact ⟨11587, 13, prime_11587, prime_13, by norm_num⟩
  · exact ⟨11593, 11, prime_11593, prime_11, by norm_num⟩
  · exact ⟨11579, 19, prime_11579, prime_19, by norm_num⟩
  · exact ⟨11597, 11, prime_11597, prime_11, by norm_num⟩
  · exact ⟨11617, 2, prime_11617, prime_2, by norm_num⟩
  · exact ⟨11617, 3, prime_11617, prime_3, by norm_num⟩
  · exact ⟨11621, 2, prime_11621, prime_2, by norm_num⟩
  · exact ⟨11621, 3, prime_11621, prime_3, by norm_num⟩
  · exact ⟨11483, 73, prime_11483, prime_73, by norm_num⟩
  · exact ⟨11621, 5, prime_11621, prime_5, by norm_num⟩
  · exact ⟨11587, 23, prime_11587, prime_23, by norm_num⟩
  · exact ⟨11621, 7, prime_11621, prime_7, by norm_num⟩
  · exact ⟨11633, 2, prime_11633, prime_2, by norm_num⟩
  · exact ⟨11633, 3, prime_11633, prime_3, by norm_num⟩
  · exact ⟨11579, 31, prime_11579, prime_31, by norm_num⟩
  · exact ⟨11633, 5, prime_11633, prime_5, by norm_num⟩
  · exact ⟨11587, 29, prime_11587, prime_29, by norm_num⟩
  · exact ⟨11633, 7, prime_11633, prime_7, by norm_num⟩
  · exact ⟨11587, 31, prime_11587, prime_31, by norm_num⟩
  · exact ⟨11617, 17, prime_11617, prime_17, by norm_num⟩
  · exact ⟨11579, 37, prime_11579, prime_37, by norm_num⟩
  · exact ⟨11633, 11, prime_11633, prime_11, by norm_num⟩
  · exact ⟨11551, 53, prime_11551, prime_53, by norm_num⟩
  · exact ⟨11633, 13, prime_11633, prime_13, by norm_num⟩
  · exact ⟨11657, 2, prime_11657, prime_2, by norm_num⟩
  · exact ⟨11657, 3, prime_11657, prime_3, by norm_num⟩
  · exact ⟨11579, 43, prime_11579, prime_43, by norm_num⟩
  · exact ⟨11657, 5, prime_11657, prime_5, by norm_num⟩
  · exact ⟨11587, 41, prime_11587, prime_41, by norm_num⟩
  · exact ⟨11657, 7, prime_11657, prime_7, by norm_num⟩
  · exact ⟨11587, 43, prime_11587, prime_43, by norm_num⟩
  · exact ⟨11617, 29, prime_11617, prime_29, by norm_num⟩
  · exact ⟨11519, 79, prime_11519, prime_79, by norm_num⟩
  · exact ⟨11657, 11, prime_11657, prime_11, by norm_num⟩
  · exact ⟨11677, 2, prime_11677, prime_2, by norm_num⟩
  · exact ⟨11677, 3, prime_11677, prime_3, by norm_num⟩
  · exact ⟨11681, 2, prime_11681, prime_2, by norm_num⟩
  · exact ⟨11681, 3, prime_11681, prime_3, by norm_num⟩
  · exact ⟨11483, 103, prime_11483, prime_103, by norm_num⟩
  · exact ⟨11681, 5, prime_11681, prime_5, by norm_num⟩
  · exact ⟨11689, 2, prime_11689, prime_2, by norm_num⟩
  · exact ⟨11689, 3, prime_11689, prime_3, by norm_num⟩
  · exact ⟨11579, 59, prime_11579, prime_59, by norm_num⟩
  · exact ⟨11689, 5, prime_11689, prime_5, by norm_num⟩
  · exact ⟨11579, 61, prime_11579, prime_61, by norm_num⟩
  · exact ⟨11699, 2, prime_11699, prime_2, by norm_num⟩
  · exact ⟨11701, 2, prime_11701, prime_2, by norm_num⟩
  · exact ⟨11701, 3, prime_11701, prime_3, by norm_num⟩
  · exact ⟨11699, 5, prime_11699, prime_5, by norm_num⟩
  · exact ⟨11701, 5, prime_11701, prime_5, by norm_num⟩
  · exact ⟨11699, 7, prime_11699, prime_7, by norm_num⟩
  · exact ⟨11701, 7, prime_11701, prime_7, by norm_num⟩
  · exact ⟨11551, 83, prime_11551, prime_83, by norm_num⟩
  · exact ⟨11681, 19, prime_11681, prime_19, by norm_num⟩
  · exact ⟨11717, 2, prime_11717, prime_2, by norm_num⟩
  · exact ⟨11719, 2, prime_11719, prime_2, by norm_num⟩
  · exact ⟨11719, 3, prime_11719, prime_3, by norm_num⟩
  · exact ⟨11717, 5, prime_11717, prime_5, by norm_num⟩
  · exact ⟨11719, 5, prime_11719, prime_5, by norm_num⟩
  · exact ⟨11717, 7, prime_11717, prime_7, by norm_num⟩
  · exact ⟨11719, 7, prime_11719, prime_7, by norm_num⟩
  · exact ⟨11731, 2, prime_11731, prime_2, by norm_num⟩
  · exact ⟨11731, 3, prime_11731, prime_3, by norm_num⟩
  · exact ⟨11717, 11, prime_11717, prime_11, by norm_num⟩
  · exact ⟨11731, 5, prime_11731, prime_5, by norm_num⟩
  · exact ⟨11717, 13, prime_11717, prime_13, by norm_num⟩
  · exact ⟨11731, 7, prime_11731, prime_7, by norm_num⟩
  · exact ⟨11743, 2, prime_11743, prime_2, by norm_num⟩
  · exact ⟨11743, 3, prime_11743, prime_3, by norm_num⟩
  · exact ⟨11717, 17, prime_11717, prime_17, by norm_num⟩
  · exact ⟨11743, 5, prime_11743, prime_5, by norm_num⟩
  · exact ⟨11717, 19, prime_11717, prime_19, by norm_num⟩
  · exact ⟨11743, 7, prime_11743, prime_7, by norm_num⟩
  · exact ⟨11701, 29, prime_11701, prime_29, by norm_num⟩
  · exact ⟨11699, 31, prime_11699, prime_31, by norm_num⟩
  · exact ⟨11717, 23, prime_11717, prime_23, by norm_num⟩
  · exact ⟨11743, 11, prime_11743, prime_11, by norm_num⟩
  · exact ⟨11681, 43, prime_11681, prime_43, by norm_num⟩
  · exact ⟨11743, 13, prime_11743, prime_13, by norm_num⟩
  · exact ⟨11689, 41, prime_11689, prime_41, by norm_num⟩
  · exact ⟨11699, 37, prime_11699, prime_37, by norm_num⟩
  · exact ⟨11717, 29, prime_11717, prime_29, by norm_num⟩
  · exact ⟨11743, 17, prime_11743, prime_17, by norm_num⟩
  · exact ⟨11717, 31, prime_11717, prime_31, by norm_num⟩
  · exact ⟨11777, 2, prime_11777, prime_2, by norm_num⟩
  · exact ⟨11779, 2, prime_11779, prime_2, by norm_num⟩
  · exact ⟨11779, 3, prime_11779, prime_3, by norm_num⟩
  · exact ⟨11783, 2, prime_11783, prime_2, by norm_num⟩
  · exact ⟨11783, 3, prime_11783, prime_3, by norm_num⟩
  · exact ⟨11777, 7, prime_11777, prime_7, by norm_num⟩
  · exact ⟨11789, 2, prime_11789, prime_2, by norm_num⟩
  · exact ⟨11789, 3, prime_11789, prime_3, by norm_num⟩
  · exact ⟨11783, 7, prime_11783, prime_7, by norm_num⟩
  · exact ⟨11789, 5, prime_11789, prime_5, by norm_num⟩
  · exact ⟨11779, 11, prime_11779, prime_11, by norm_num⟩
  · exact ⟨11789, 7, prime_11789, prime_7, by norm_num⟩
  · exact ⟨11801, 2, prime_11801, prime_2, by norm_num⟩

private theorem lemoine_chunk_59 : ∀ k : ℕ, 5903 ≤ k → k ≤ 6002 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨11801, 3, prime_11801, prime_3, by norm_num⟩
  · exact ⟨11783, 13, prime_11783, prime_13, by norm_num⟩
  · exact ⟨11807, 2, prime_11807, prime_2, by norm_num⟩
  · exact ⟨11807, 3, prime_11807, prime_3, by norm_num⟩
  · exact ⟨11801, 7, prime_11801, prime_7, by norm_num⟩
  · exact ⟨11813, 2, prime_11813, prime_2, by norm_num⟩
  · exact ⟨11813, 3, prime_11813, prime_3, by norm_num⟩
  · exact ⟨11807, 7, prime_11807, prime_7, by norm_num⟩
  · exact ⟨11813, 5, prime_11813, prime_5, by norm_num⟩
  · exact ⟨11821, 2, prime_11821, prime_2, by norm_num⟩
  · exact ⟨11821, 3, prime_11821, prime_3, by norm_num⟩
  · exact ⟨11807, 11, prime_11807, prime_11, by norm_num⟩
  · exact ⟨11827, 2, prime_11827, prime_2, by norm_num⟩
  · exact ⟨11827, 3, prime_11827, prime_3, by norm_num⟩
  · exact ⟨11831, 2, prime_11831, prime_2, by norm_num⟩
  · exact ⟨11833, 2, prime_11833, prime_2, by norm_num⟩
  · exact ⟨11833, 3, prime_11833, prime_3, by norm_num⟩
  · exact ⟨11831, 5, prime_11831, prime_5, by norm_num⟩
  · exact ⟨11839, 2, prime_11839, prime_2, by norm_num⟩
  · exact ⟨11839, 3, prime_11839, prime_3, by norm_num⟩
  · exact ⟨11833, 7, prime_11833, prime_7, by norm_num⟩
  · exact ⟨11839, 5, prime_11839, prime_5, by norm_num⟩
  · exact ⟨11813, 19, prime_11813, prime_19, by norm_num⟩
  · exact ⟨11839, 7, prime_11839, prime_7, by norm_num⟩
  · exact ⟨11833, 11, prime_11833, prime_11, by norm_num⟩
  · exact ⟨11831, 13, prime_11831, prime_13, by norm_num⟩
  · exact ⟨11833, 13, prime_11833, prime_13, by norm_num⟩
  · exact ⟨11839, 11, prime_11839, prime_11, by norm_num⟩
  · exact ⟨11801, 31, prime_11801, prime_31, by norm_num⟩
  · exact ⟨11839, 13, prime_11839, prime_13, by norm_num⟩
  · exact ⟨11863, 2, prime_11863, prime_2, by norm_num⟩
  · exact ⟨11863, 3, prime_11863, prime_3, by norm_num⟩
  · exact ⟨11867, 2, prime_11867, prime_2, by norm_num⟩
  · exact ⟨11867, 3, prime_11867, prime_3, by norm_num⟩
  · exact ⟨11813, 31, prime_11813, prime_31, by norm_num⟩
  · exact ⟨11867, 5, prime_11867, prime_5, by norm_num⟩
  · exact ⟨11833, 23, prime_11833, prime_23, by norm_num⟩
  · exact ⟨11867, 7, prime_11867, prime_7, by norm_num⟩
  · exact ⟨11821, 31, prime_11821, prime_31, by norm_num⟩
  · exact ⟨11863, 11, prime_11863, prime_11, by norm_num⟩
  · exact ⟨11813, 37, prime_11813, prime_37, by norm_num⟩
  · exact ⟨11867, 11, prime_11867, prime_11, by norm_num⟩
  · exact ⟨11887, 2, prime_11887, prime_2, by norm_num⟩
  · exact ⟨11887, 3, prime_11887, prime_3, by norm_num⟩
  · exact ⟨11833, 31, prime_11833, prime_31, by norm_num⟩
  · exact ⟨11887, 5, prime_11887, prime_5, by norm_num⟩
  · exact ⟨11813, 43, prime_11813, prime_43, by norm_num⟩
  · exact ⟨11897, 2, prime_11897, prime_2, by norm_num⟩
  · exact ⟨11897, 3, prime_11897, prime_3, by norm_num⟩
  · exact ⟨11867, 19, prime_11867, prime_19, by norm_num⟩
  · exact ⟨11903, 2, prime_11903, prime_2, by norm_num⟩
  · exact ⟨11903, 3, prime_11903, prime_3, by norm_num⟩
  · exact ⟨11897, 7, prime_11897, prime_7, by norm_num⟩
  · exact ⟨11909, 2, prime_11909, prime_2, by norm_num⟩
  · exact ⟨11909, 3, prime_11909, prime_3, by norm_num⟩
  · exact ⟨11903, 7, prime_11903, prime_7, by norm_num⟩
  · exact ⟨11909, 5, prime_11909, prime_5, by norm_num⟩
  · exact ⟨11887, 17, prime_11887, prime_17, by norm_num⟩
  · exact ⟨11909, 7, prime_11909, prime_7, by norm_num⟩
  · exact ⟨11903, 11, prime_11903, prime_11, by norm_num⟩
  · exact ⟨11923, 2, prime_11923, prime_2, by norm_num⟩
  · exact ⟨11923, 3, prime_11923, prime_3, by norm_num⟩
  · exact ⟨11927, 2, prime_11927, prime_2, by norm_num⟩
  · exact ⟨11927, 3, prime_11927, prime_3, by norm_num⟩
  · exact ⟨11909, 13, prime_11909, prime_13, by norm_num⟩
  · exact ⟨11933, 2, prime_11933, prime_2, by norm_num⟩
  · exact ⟨11933, 3, prime_11933, prime_3, by norm_num⟩
  · exact ⟨11927, 7, prime_11927, prime_7, by norm_num⟩
  · exact ⟨11939, 2, prime_11939, prime_2, by norm_num⟩
  · exact ⟨11941, 2, prime_11941, prime_2, by norm_num⟩
  · exact ⟨11941, 3, prime_11941, prime_3, by norm_num⟩
  · exact ⟨11939, 5, prime_11939, prime_5, by norm_num⟩
  · exact ⟨11941, 5, prime_11941, prime_5, by norm_num⟩
  · exact ⟨11939, 7, prime_11939, prime_7, by norm_num⟩
  · exact ⟨11941, 7, prime_11941, prime_7, by norm_num⟩
  · exact ⟨11953, 2, prime_11953, prime_2, by norm_num⟩
  · exact ⟨11953, 3, prime_11953, prime_3, by norm_num⟩
  · exact ⟨11939, 11, prime_11939, prime_11, by norm_num⟩
  · exact ⟨11959, 2, prime_11959, prime_2, by norm_num⟩
  · exact ⟨11959, 3, prime_11959, prime_3, by norm_num⟩
  · exact ⟨11953, 7, prime_11953, prime_7, by norm_num⟩
  · exact ⟨11959, 5, prime_11959, prime_5, by norm_num⟩
  · exact ⟨11933, 19, prime_11933, prime_19, by norm_num⟩
  · exact ⟨11969, 2, prime_11969, prime_2, by norm_num⟩
  · exact ⟨11971, 2, prime_11971, prime_2, by norm_num⟩
  · exact ⟨11971, 3, prime_11971, prime_3, by norm_num⟩
  · exact ⟨11969, 5, prime_11969, prime_5, by norm_num⟩
  · exact ⟨11971, 5, prime_11971, prime_5, by norm_num⟩
  · exact ⟨11969, 7, prime_11969, prime_7, by norm_num⟩
  · exact ⟨11981, 2, prime_11981, prime_2, by norm_num⟩
  · exact ⟨11981, 3, prime_11981, prime_3, by norm_num⟩
  · exact ⟨11927, 31, prime_11927, prime_31, by norm_num⟩
  · exact ⟨11987, 2, prime_11987, prime_2, by norm_num⟩
  · exact ⟨11987, 3, prime_11987, prime_3, by norm_num⟩
  · exact ⟨11981, 7, prime_11981, prime_7, by norm_num⟩
  · exact ⟨11987, 5, prime_11987, prime_5, by norm_num⟩
  · exact ⟨11953, 23, prime_11953, prime_23, by norm_num⟩
  · exact ⟨11987, 7, prime_11987, prime_7, by norm_num⟩
  · exact ⟨11981, 11, prime_11981, prime_11, by norm_num⟩
  · exact ⟨11971, 17, prime_11971, prime_17, by norm_num⟩

private theorem lemoine_chunk_60 : ∀ k : ℕ, 6003 ≤ k → k ≤ 6102 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨11981, 13, prime_11981, prime_13, by norm_num⟩
  · exact ⟨11987, 11, prime_11987, prime_11, by norm_num⟩
  · exact ⟨12007, 2, prime_12007, prime_2, by norm_num⟩
  · exact ⟨12007, 3, prime_12007, prime_3, by norm_num⟩
  · exact ⟨12011, 2, prime_12011, prime_2, by norm_num⟩
  · exact ⟨12011, 3, prime_12011, prime_3, by norm_num⟩
  · exact ⟨11981, 19, prime_11981, prime_19, by norm_num⟩
  · exact ⟨12011, 5, prime_12011, prime_5, by norm_num⟩
  · exact ⟨11941, 41, prime_11941, prime_41, by norm_num⟩
  · exact ⟨12011, 7, prime_12011, prime_7, by norm_num⟩
  · exact ⟨11981, 23, prime_11981, prime_23, by norm_num⟩
  · exact ⟨12007, 11, prime_12007, prime_11, by norm_num⟩
  · exact ⟨11969, 31, prime_11969, prime_31, by norm_num⟩
  · exact ⟨12011, 11, prime_12011, prime_11, by norm_num⟩
  · exact ⟨11953, 41, prime_11953, prime_41, by norm_num⟩
  · exact ⟨12011, 13, prime_12011, prime_13, by norm_num⟩
  · exact ⟨11981, 29, prime_11981, prime_29, by norm_num⟩
  · exact ⟨12037, 2, prime_12037, prime_2, by norm_num⟩
  · exact ⟨12037, 3, prime_12037, prime_3, by norm_num⟩
  · exact ⟨12041, 2, prime_12041, prime_2, by norm_num⟩
  · exact ⟨12043, 2, prime_12043, prime_2, by norm_num⟩
  · exact ⟨12043, 3, prime_12043, prime_3, by norm_num⟩
  · exact ⟨12041, 5, prime_12041, prime_5, by norm_num⟩
  · exact ⟨12049, 2, prime_12049, prime_2, by norm_num⟩
  · exact ⟨12049, 3, prime_12049, prime_3, by norm_num⟩
  · exact ⟨12043, 7, prime_12043, prime_7, by norm_num⟩
  · exact ⟨12049, 5, prime_12049, prime_5, by norm_num⟩
  · exact ⟨11987, 37, prime_11987, prime_37, by norm_num⟩
  · exact ⟨12049, 7, prime_12049, prime_7, by norm_num⟩
  · exact ⟨12043, 11, prime_12043, prime_11, by norm_num⟩
  · exact ⟨12041, 13, prime_12041, prime_13, by norm_num⟩
  · exact ⟨12043, 13, prime_12043, prime_13, by norm_num⟩
  · exact ⟨12049, 11, prime_12049, prime_11, by norm_num⟩
  · exact ⟨12011, 31, prime_12011, prime_31, by norm_num⟩
  · exact ⟨12071, 2, prime_12071, prime_2, by norm_num⟩
  · exact ⟨12073, 2, prime_12073, prime_2, by norm_num⟩
  · exact ⟨12073, 3, prime_12073, prime_3, by norm_num⟩
  · exact ⟨12071, 5, prime_12071, prime_5, by norm_num⟩
  · exact ⟨12073, 5, prime_12073, prime_5, by norm_num⟩
  · exact ⟨12071, 7, prime_12071, prime_7, by norm_num⟩
  · exact ⟨12073, 7, prime_12073, prime_7, by norm_num⟩
  · exact ⟨12043, 23, prime_12043, prime_23, by norm_num⟩
  · exact ⟨11969, 61, prime_11969, prime_61, by norm_num⟩
  · exact ⟨12071, 11, prime_12071, prime_11, by norm_num⟩
  · exact ⟨12073, 11, prime_12073, prime_11, by norm_num⟩
  · exact ⟨12071, 13, prime_12071, prime_13, by norm_num⟩
  · exact ⟨12073, 13, prime_12073, prime_13, by norm_num⟩
  · exact ⟨12097, 2, prime_12097, prime_2, by norm_num⟩
  · exact ⟨12097, 3, prime_12097, prime_3, by norm_num⟩
  · exact ⟨12101, 2, prime_12101, prime_2, by norm_num⟩
  · exact ⟨12101, 3, prime_12101, prime_3, by norm_num⟩
  · exact ⟨12071, 19, prime_12071, prime_19, by norm_num⟩
  · exact ⟨12107, 2, prime_12107, prime_2, by norm_num⟩
  · exact ⟨12109, 2, prime_12109, prime_2, by norm_num⟩
  · exact ⟨12109, 3, prime_12109, prime_3, by norm_num⟩
  · exact ⟨12113, 2, prime_12113, prime_2, by norm_num⟩
  · exact ⟨12113, 3, prime_12113, prime_3, by norm_num⟩
  · exact ⟨12107, 7, prime_12107, prime_7, by norm_num⟩
  · exact ⟨12119, 2, prime_12119, prime_2, by norm_num⟩
  · exact ⟨12119, 3, prime_12119, prime_3, by norm_num⟩
  · exact ⟨12113, 7, prime_12113, prime_7, by norm_num⟩
  · exact ⟨12119, 5, prime_12119, prime_5, by norm_num⟩
  · exact ⟨12109, 11, prime_12109, prime_11, by norm_num⟩
  · exact ⟨12119, 7, prime_12119, prime_7, by norm_num⟩
  · exact ⟨12113, 11, prime_12113, prime_11, by norm_num⟩
  · exact ⟨12043, 47, prime_12043, prime_47, by norm_num⟩
  · exact ⟨12113, 13, prime_12113, prime_13, by norm_num⟩
  · exact ⟨12119, 11, prime_12119, prime_11, by norm_num⟩
  · exact ⟨12109, 17, prime_12109, prime_17, by norm_num⟩
  · exact ⟨12119, 13, prime_12119, prime_13, by norm_num⟩
  · exact ⟨12143, 2, prime_12143, prime_2, by norm_num⟩
  · exact ⟨12143, 3, prime_12143, prime_3, by norm_num⟩
  · exact ⟨12113, 19, prime_12113, prime_19, by norm_num⟩
  · exact ⟨12149, 2, prime_12149, prime_2, by norm_num⟩
  · exact ⟨12149, 3, prime_12149, prime_3, by norm_num⟩
  · exact ⟨12143, 7, prime_12143, prime_7, by norm_num⟩
  · exact ⟨12149, 5, prime_12149, prime_5, by norm_num⟩
  · exact ⟨12157, 2, prime_12157, prime_2, by norm_num⟩
  · exact ⟨12157, 3, prime_12157, prime_3, by norm_num⟩
  · exact ⟨12161, 2, prime_12161, prime_2, by norm_num⟩
  · exact ⟨12163, 2, prime_12163, prime_2, by norm_num⟩
  · exact ⟨12163, 3, prime_12163, prime_3, by norm_num⟩
  · exact ⟨12161, 5, prime_12161, prime_5, by norm_num⟩
  · exact ⟨12163, 5, prime_12163, prime_5, by norm_num⟩
  · exact ⟨12161, 7, prime_12161, prime_7, by norm_num⟩
  · exact ⟨12163, 7, prime_12163, prime_7, by norm_num⟩
  · exact ⟨12157, 11, prime_12157, prime_11, by norm_num⟩
  · exact ⟨12143, 19, prime_12143, prime_19, by norm_num⟩
  · exact ⟨12161, 11, prime_12161, prime_11, by norm_num⟩
  · exact ⟨12163, 11, prime_12163, prime_11, by norm_num⟩
  · exact ⟨12161, 13, prime_12161, prime_13, by norm_num⟩
  · exact ⟨12163, 13, prime_12163, prime_13, by norm_num⟩
  · exact ⟨12157, 17, prime_12157, prime_17, by norm_num⟩
  · exact ⟨12119, 37, prime_12119, prime_37, by norm_num⟩
  · exact ⟨12161, 17, prime_12161, prime_17, by norm_num⟩
  · exact ⟨12163, 17, prime_12163, prime_17, by norm_num⟩
  · exact ⟨12161, 19, prime_12161, prime_19, by norm_num⟩
  · exact ⟨12197, 2, prime_12197, prime_2, by norm_num⟩
  · exact ⟨12197, 3, prime_12197, prime_3, by norm_num⟩
  · exact ⟨12143, 31, prime_12143, prime_31, by norm_num⟩

private theorem lemoine_chunk_61 : ∀ k : ℕ, 6103 ≤ k → k ≤ 6202 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨12203, 2, prime_12203, prime_2, by norm_num⟩
  · exact ⟨12203, 3, prime_12203, prime_3, by norm_num⟩
  · exact ⟨12197, 7, prime_12197, prime_7, by norm_num⟩
  · exact ⟨12203, 5, prime_12203, prime_5, by norm_num⟩
  · exact ⟨12211, 2, prime_12211, prime_2, by norm_num⟩
  · exact ⟨12211, 3, prime_12211, prime_3, by norm_num⟩
  · exact ⟨12197, 11, prime_12197, prime_11, by norm_num⟩
  · exact ⟨12211, 5, prime_12211, prime_5, by norm_num⟩
  · exact ⟨12197, 13, prime_12197, prime_13, by norm_num⟩
  · exact ⟨12211, 7, prime_12211, prime_7, by norm_num⟩
  · exact ⟨12109, 59, prime_12109, prime_59, by norm_num⟩
  · exact ⟨12203, 13, prime_12203, prime_13, by norm_num⟩
  · exact ⟨12227, 2, prime_12227, prime_2, by norm_num⟩
  · exact ⟨12227, 3, prime_12227, prime_3, by norm_num⟩
  · exact ⟨12197, 19, prime_12197, prime_19, by norm_num⟩
  · exact ⟨12227, 5, prime_12227, prime_5, by norm_num⟩
  · exact ⟨12157, 41, prime_12157, prime_41, by norm_num⟩
  · exact ⟨12227, 7, prime_12227, prime_7, by norm_num⟩
  · exact ⟨12239, 2, prime_12239, prime_2, by norm_num⟩
  · exact ⟨12241, 2, prime_12241, prime_2, by norm_num⟩
  · exact ⟨12241, 3, prime_12241, prime_3, by norm_num⟩
  · exact ⟨12239, 5, prime_12239, prime_5, by norm_num⟩
  · exact ⟨12241, 5, prime_12241, prime_5, by norm_num⟩
  · exact ⟨12239, 7, prime_12239, prime_7, by norm_num⟩
  · exact ⟨12251, 2, prime_12251, prime_2, by norm_num⟩
  · exact ⟨12253, 2, prime_12253, prime_2, by norm_num⟩
  · exact ⟨12253, 3, prime_12253, prime_3, by norm_num⟩
  · exact ⟨12251, 5, prime_12251, prime_5, by norm_num⟩
  · exact ⟨12253, 5, prime_12253, prime_5, by norm_num⟩
  · exact ⟨12251, 7, prime_12251, prime_7, by norm_num⟩
  · exact ⟨12263, 2, prime_12263, prime_2, by norm_num⟩
  · exact ⟨12263, 3, prime_12263, prime_3, by norm_num⟩
  · exact ⟨12197, 37, prime_12197, prime_37, by norm_num⟩
  · exact ⟨12269, 2, prime_12269, prime_2, by norm_num⟩
  · exact ⟨12269, 3, prime_12269, prime_3, by norm_num⟩
  · exact ⟨12263, 7, prime_12263, prime_7, by norm_num⟩
  · exact ⟨12269, 5, prime_12269, prime_5, by norm_num⟩
  · exact ⟨12277, 2, prime_12277, prime_2, by norm_num⟩
  · exact ⟨12277, 3, prime_12277, prime_3, by norm_num⟩
  · exact ⟨12281, 2, prime_12281, prime_2, by norm_num⟩
  · exact ⟨12281, 3, prime_12281, prime_3, by norm_num⟩
  · exact ⟨12263, 13, prime_12263, prime_13, by norm_num⟩
  · exact ⟨12281, 5, prime_12281, prime_5, by norm_num⟩
  · exact ⟨12289, 2, prime_12289, prime_2, by norm_num⟩
  · exact ⟨12289, 3, prime_12289, prime_3, by norm_num⟩
  · exact ⟨12263, 17, prime_12263, prime_17, by norm_num⟩
  · exact ⟨12289, 5, prime_12289, prime_5, by norm_num⟩
  · exact ⟨12263, 19, prime_12263, prime_19, by norm_num⟩
  · exact ⟨12289, 7, prime_12289, prime_7, by norm_num⟩
  · exact ⟨12301, 2, prime_12301, prime_2, by norm_num⟩
  · exact ⟨12301, 3, prime_12301, prime_3, by norm_num⟩
  · exact ⟨12263, 23, prime_12263, prime_23, by norm_num⟩
  · exact ⟨12301, 5, prime_12301, prime_5, by norm_num⟩
  · exact ⟨12251, 31, prime_12251, prime_31, by norm_num⟩
  · exact ⟨12301, 7, prime_12301, prime_7, by norm_num⟩
  · exact ⟨12211, 53, prime_12211, prime_53, by norm_num⟩
  · exact ⟨12281, 19, prime_12281, prime_19, by norm_num⟩
  · exact ⟨12263, 29, prime_12263, prime_29, by norm_num⟩
  · exact ⟨12301, 11, prime_12301, prime_11, by norm_num⟩
  · exact ⟨12263, 31, prime_12263, prime_31, by norm_num⟩
  · exact ⟨12323, 2, prime_12323, prime_2, by norm_num⟩
  · exact ⟨12323, 3, prime_12323, prime_3, by norm_num⟩
  · exact ⟨12269, 31, prime_12269, prime_31, by norm_num⟩
  · exact ⟨12329, 2, prime_12329, prime_2, by norm_num⟩
  · exact ⟨12329, 3, prime_12329, prime_3, by norm_num⟩
  · exact ⟨12323, 7, prime_12323, prime_7, by norm_num⟩
  · exact ⟨12329, 5, prime_12329, prime_5, by norm_num⟩
  · exact ⟨12163, 89, prime_12163, prime_89, by norm_num⟩
  · exact ⟨12329, 7, prime_12329, prime_7, by norm_num⟩
  · exact ⟨12323, 11, prime_12323, prime_11, by norm_num⟩
  · exact ⟨12343, 2, prime_12343, prime_2, by norm_num⟩
  · exact ⟨12343, 3, prime_12343, prime_3, by norm_num⟩
  · exact ⟨12347, 2, prime_12347, prime_2, by norm_num⟩
  · exact ⟨12347, 3, prime_12347, prime_3, by norm_num⟩
  · exact ⟨12329, 13, prime_12329, prime_13, by norm_num⟩
  · exact ⟨12347, 5, prime_12347, prime_5, by norm_num⟩
  · exact ⟨12301, 29, prime_12301, prime_29, by norm_num⟩
  · exact ⟨12347, 7, prime_12347, prime_7, by norm_num⟩
  · exact ⟨12329, 17, prime_12329, prime_17, by norm_num⟩
  · exact ⟨12343, 11, prime_12343, prime_11, by norm_num⟩
  · exact ⟨12329, 19, prime_12329, prime_19, by norm_num⟩
  · exact ⟨12347, 11, prime_12347, prime_11, by norm_num⟩
  · exact ⟨12289, 41, prime_12289, prime_41, by norm_num⟩
  · exact ⟨12347, 13, prime_12347, prime_13, by norm_num⟩
  · exact ⟨12329, 23, prime_12329, prime_23, by norm_num⟩
  · exact ⟨12373, 2, prime_12373, prime_2, by norm_num⟩
  · exact ⟨12373, 3, prime_12373, prime_3, by norm_num⟩
  · exact ⟨12377, 2, prime_12377, prime_2, by norm_num⟩
  · exact ⟨12379, 2, prime_12379, prime_2, by norm_num⟩
  · exact ⟨12379, 3, prime_12379, prime_3, by norm_num⟩
  · exact ⟨12377, 5, prime_12377, prime_5, by norm_num⟩
  · exact ⟨12379, 5, prime_12379, prime_5, by norm_num⟩
  · exact ⟨12377, 7, prime_12377, prime_7, by norm_num⟩
  · exact ⟨12379, 7, prime_12379, prime_7, by norm_num⟩
  · exact ⟨12391, 2, prime_12391, prime_2, by norm_num⟩
  · exact ⟨12391, 3, prime_12391, prime_3, by norm_num⟩
  · exact ⟨12377, 11, prime_12377, prime_11, by norm_num⟩
  · exact ⟨12391, 5, prime_12391, prime_5, by norm_num⟩
  · exact ⟨12377, 13, prime_12377, prime_13, by norm_num⟩
  · exact ⟨12401, 2, prime_12401, prime_2, by norm_num⟩

private theorem lemoine_chunk_62 : ∀ k : ℕ, 6203 ≤ k → k ≤ 6302 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨12401, 3, prime_12401, prime_3, by norm_num⟩
  · exact ⟨12347, 31, prime_12347, prime_31, by norm_num⟩
  · exact ⟨12401, 5, prime_12401, prime_5, by norm_num⟩
  · exact ⟨12409, 2, prime_12409, prime_2, by norm_num⟩
  · exact ⟨12409, 3, prime_12409, prime_3, by norm_num⟩
  · exact ⟨12413, 2, prime_12413, prime_2, by norm_num⟩
  · exact ⟨12413, 3, prime_12413, prime_3, by norm_num⟩
  · exact ⟨12347, 37, prime_12347, prime_37, by norm_num⟩
  · exact ⟨12413, 5, prime_12413, prime_5, by norm_num⟩
  · exact ⟨12421, 2, prime_12421, prime_2, by norm_num⟩
  · exact ⟨12421, 3, prime_12421, prime_3, by norm_num⟩
  · exact ⟨12391, 19, prime_12391, prime_19, by norm_num⟩
  · exact ⟨12421, 5, prime_12421, prime_5, by norm_num⟩
  · exact ⟨12347, 43, prime_12347, prime_43, by norm_num⟩
  · exact ⟨12421, 7, prime_12421, prime_7, by norm_num⟩
  · exact ⟨12433, 2, prime_12433, prime_2, by norm_num⟩
  · exact ⟨12433, 3, prime_12433, prime_3, by norm_num⟩
  · exact ⟨12437, 2, prime_12437, prime_2, by norm_num⟩
  · exact ⟨12437, 3, prime_12437, prime_3, by norm_num⟩
  · exact ⟨12323, 61, prime_12323, prime_61, by norm_num⟩
  · exact ⟨12437, 5, prime_12437, prime_5, by norm_num⟩
  · exact ⟨12391, 29, prime_12391, prime_29, by norm_num⟩
  · exact ⟨12437, 7, prime_12437, prime_7, by norm_num⟩
  · exact ⟨12391, 31, prime_12391, prime_31, by norm_num⟩
  · exact ⟨12451, 2, prime_12451, prime_2, by norm_num⟩
  · exact ⟨12451, 3, prime_12451, prime_3, by norm_num⟩
  · exact ⟨12437, 11, prime_12437, prime_11, by norm_num⟩
  · exact ⟨12457, 2, prime_12457, prime_2, by norm_num⟩
  · exact ⟨12457, 3, prime_12457, prime_3, by norm_num⟩
  · exact ⟨12451, 7, prime_12451, prime_7, by norm_num⟩
  · exact ⟨12457, 5, prime_12457, prime_5, by norm_num⟩
  · exact ⟨12347, 61, prime_12347, prime_61, by norm_num⟩
  · exact ⟨12457, 7, prime_12457, prime_7, by norm_num⟩
  · exact ⟨12451, 11, prime_12451, prime_11, by norm_num⟩
  · exact ⟨12437, 19, prime_12437, prime_19, by norm_num⟩
  · exact ⟨12473, 2, prime_12473, prime_2, by norm_num⟩
  · exact ⟨12473, 3, prime_12473, prime_3, by norm_num⟩
  · exact ⟨12347, 67, prime_12347, prime_67, by norm_num⟩
  · exact ⟨12479, 2, prime_12479, prime_2, by norm_num⟩
  · exact ⟨12479, 3, prime_12479, prime_3, by norm_num⟩
  · exact ⟨12473, 7, prime_12473, prime_7, by norm_num⟩
  · exact ⟨12479, 5, prime_12479, prime_5, by norm_num⟩
  · exact ⟨12487, 2, prime_12487, prime_2, by norm_num⟩
  · exact ⟨12487, 3, prime_12487, prime_3, by norm_num⟩
  · exact ⟨12491, 2, prime_12491, prime_2, by norm_num⟩
  · exact ⟨12491, 3, prime_12491, prime_3, by norm_num⟩
  · exact ⟨12473, 13, prime_12473, prime_13, by norm_num⟩
  · exact ⟨12497, 2, prime_12497, prime_2, by norm_num⟩
  · exact ⟨12497, 3, prime_12497, prime_3, by norm_num⟩
  · exact ⟨12491, 7, prime_12491, prime_7, by norm_num⟩
  · exact ⟨12503, 2, prime_12503, prime_2, by norm_num⟩
  · exact ⟨12503, 3, prime_12503, prime_3, by norm_num⟩
  · exact ⟨12497, 7, prime_12497, prime_7, by norm_num⟩
  · exact ⟨12503, 5, prime_12503, prime_5, by norm_num⟩
  · exact ⟨12511, 2, prime_12511, prime_2, by norm_num⟩
  · exact ⟨12511, 3, prime_12511, prime_3, by norm_num⟩
  · exact ⟨12497, 11, prime_12497, prime_11, by norm_num⟩
  · exact ⟨12517, 2, prime_12517, prime_2, by norm_num⟩
  · exact ⟨12517, 3, prime_12517, prime_3, by norm_num⟩
  · exact ⟨12511, 7, prime_12511, prime_7, by norm_num⟩
  · exact ⟨12517, 5, prime_12517, prime_5, by norm_num⟩
  · exact ⟨12503, 13, prime_12503, prime_13, by norm_num⟩
  · exact ⟨12527, 2, prime_12527, prime_2, by norm_num⟩
  · exact ⟨12527, 3, prime_12527, prime_3, by norm_num⟩
  · exact ⟨12497, 19, prime_12497, prime_19, by norm_num⟩
  · exact ⟨12527, 5, prime_12527, prime_5, by norm_num⟩
  · exact ⟨12517, 11, prime_12517, prime_11, by norm_num⟩
  · exact ⟨12527, 7, prime_12527, prime_7, by norm_num⟩
  · exact ⟨12539, 2, prime_12539, prime_2, by norm_num⟩
  · exact ⟨12541, 2, prime_12541, prime_2, by norm_num⟩
  · exact ⟨12541, 3, prime_12541, prime_3, by norm_num⟩
  · exact ⟨12539, 5, prime_12539, prime_5, by norm_num⟩
  · exact ⟨12547, 2, prime_12547, prime_2, by norm_num⟩
  · exact ⟨12547, 3, prime_12547, prime_3, by norm_num⟩
  · exact ⟨12541, 7, prime_12541, prime_7, by norm_num⟩
  · exact ⟨12553, 2, prime_12553, prime_2, by norm_num⟩
  · exact ⟨12553, 3, prime_12553, prime_3, by norm_num⟩
  · exact ⟨12547, 7, prime_12547, prime_7, by norm_num⟩
  · exact ⟨12553, 5, prime_12553, prime_5, by norm_num⟩
  · exact ⟨12539, 13, prime_12539, prime_13, by norm_num⟩
  · exact ⟨12553, 7, prime_12553, prime_7, by norm_num⟩
  · exact ⟨12547, 11, prime_12547, prime_11, by norm_num⟩
  · exact ⟨12497, 37, prime_12497, prime_37, by norm_num⟩
  · exact ⟨12569, 2, prime_12569, prime_2, by norm_num⟩
  · exact ⟨12569, 3, prime_12569, prime_3, by norm_num⟩
  · exact ⟨12539, 19, prime_12539, prime_19, by norm_num⟩
  · exact ⟨12569, 5, prime_12569, prime_5, by norm_num⟩
  · exact ⟨12577, 2, prime_12577, prime_2, by norm_num⟩
  · exact ⟨12577, 3, prime_12577, prime_3, by norm_num⟩
  · exact ⟨12547, 19, prime_12547, prime_19, by norm_num⟩
  · exact ⟨12583, 2, prime_12583, prime_2, by norm_num⟩
  · exact ⟨12583, 3, prime_12583, prime_3, by norm_num⟩
  · exact ⟨12577, 7, prime_12577, prime_7, by norm_num⟩
  · exact ⟨12589, 2, prime_12589, prime_2, by norm_num⟩
  · exact ⟨12589, 3, prime_12589, prime_3, by norm_num⟩
  · exact ⟨12583, 7, prime_12583, prime_7, by norm_num⟩
  · exact ⟨12589, 5, prime_12589, prime_5, by norm_num⟩
  · exact ⟨12539, 31, prime_12539, prime_31, by norm_num⟩
  · exact ⟨12589, 7, prime_12589, prime_7, by norm_num⟩
  · exact ⟨12601, 2, prime_12601, prime_2, by norm_num⟩

private theorem lemoine_chunk_63 : ∀ k : ℕ, 6303 ≤ k → k ≤ 6402 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨12601, 3, prime_12601, prime_3, by norm_num⟩
  · exact ⟨12583, 13, prime_12583, prime_13, by norm_num⟩
  · exact ⟨12601, 5, prime_12601, prime_5, by norm_num⟩
  · exact ⟨12539, 37, prime_12539, prime_37, by norm_num⟩
  · exact ⟨12611, 2, prime_12611, prime_2, by norm_num⟩
  · exact ⟨12613, 2, prime_12613, prime_2, by norm_num⟩
  · exact ⟨12613, 3, prime_12613, prime_3, by norm_num⟩
  · exact ⟨12611, 5, prime_12611, prime_5, by norm_num⟩
  · exact ⟨12619, 2, prime_12619, prime_2, by norm_num⟩
  · exact ⟨12619, 3, prime_12619, prime_3, by norm_num⟩
  · exact ⟨12613, 7, prime_12613, prime_7, by norm_num⟩
  · exact ⟨12619, 5, prime_12619, prime_5, by norm_num⟩
  · exact ⟨12569, 31, prime_12569, prime_31, by norm_num⟩
  · exact ⟨12619, 7, prime_12619, prime_7, by norm_num⟩
  · exact ⟨12613, 11, prime_12613, prime_11, by norm_num⟩
  · exact ⟨12611, 13, prime_12611, prime_13, by norm_num⟩
  · exact ⟨12613, 13, prime_12613, prime_13, by norm_num⟩
  · exact ⟨12637, 2, prime_12637, prime_2, by norm_num⟩
  · exact ⟨12637, 3, prime_12637, prime_3, by norm_num⟩
  · exact ⟨12641, 2, prime_12641, prime_2, by norm_num⟩
  · exact ⟨12641, 3, prime_12641, prime_3, by norm_num⟩
  · exact ⟨12611, 19, prime_12611, prime_19, by norm_num⟩
  · exact ⟨12647, 2, prime_12647, prime_2, by norm_num⟩
  · exact ⟨12647, 3, prime_12647, prime_3, by norm_num⟩
  · exact ⟨12641, 7, prime_12641, prime_7, by norm_num⟩
  · exact ⟨12653, 2, prime_12653, prime_2, by norm_num⟩
  · exact ⟨12653, 3, prime_12653, prime_3, by norm_num⟩
  · exact ⟨12647, 7, prime_12647, prime_7, by norm_num⟩
  · exact ⟨12659, 2, prime_12659, prime_2, by norm_num⟩
  · exact ⟨12659, 3, prime_12659, prime_3, by norm_num⟩
  · exact ⟨12653, 7, prime_12653, prime_7, by norm_num⟩
  · exact ⟨12659, 5, prime_12659, prime_5, by norm_num⟩
  · exact ⟨12637, 17, prime_12637, prime_17, by norm_num⟩
  · exact ⟨12659, 7, prime_12659, prime_7, by norm_num⟩
  · exact ⟨12671, 2, prime_12671, prime_2, by norm_num⟩
  · exact ⟨12671, 3, prime_12671, prime_3, by norm_num⟩
  · exact ⟨12653, 13, prime_12653, prime_13, by norm_num⟩
  · exact ⟨12671, 5, prime_12671, prime_5, by norm_num⟩
  · exact ⟨12637, 23, prime_12637, prime_23, by norm_num⟩
  · exact ⟨12671, 7, prime_12671, prime_7, by norm_num⟩
  · exact ⟨12653, 17, prime_12653, prime_17, by norm_num⟩
  · exact ⟨12583, 53, prime_12583, prime_53, by norm_num⟩
  · exact ⟨12653, 19, prime_12653, prime_19, by norm_num⟩
  · exact ⟨12689, 2, prime_12689, prime_2, by norm_num⟩
  · exact ⟨12689, 3, prime_12689, prime_3, by norm_num⟩
  · exact ⟨12671, 13, prime_12671, prime_13, by norm_num⟩
  · exact ⟨12689, 5, prime_12689, prime_5, by norm_num⟩
  · exact ⟨12697, 2, prime_12697, prime_2, by norm_num⟩
  · exact ⟨12697, 3, prime_12697, prime_3, by norm_num⟩
  · exact ⟨12671, 17, prime_12671, prime_17, by norm_num⟩
  · exact ⟨12703, 2, prime_12703, prime_2, by norm_num⟩
  · exact ⟨12703, 3, prime_12703, prime_3, by norm_num⟩
  · exact ⟨12697, 7, prime_12697, prime_7, by norm_num⟩
  · exact ⟨12703, 5, prime_12703, prime_5, by norm_num⟩
  · exact ⟨12689, 13, prime_12689, prime_13, by norm_num⟩
  · exact ⟨12713, 2, prime_12713, prime_2, by norm_num⟩
  · exact ⟨12713, 3, prime_12713, prime_3, by norm_num⟩
  · exact ⟨12659, 31, prime_12659, prime_31, by norm_num⟩
  · exact ⟨12713, 5, prime_12713, prime_5, by norm_num⟩
  · exact ⟨12721, 2, prime_12721, prime_2, by norm_num⟩
  · exact ⟨12721, 3, prime_12721, prime_3, by norm_num⟩
  · exact ⟨12703, 13, prime_12703, prime_13, by norm_num⟩
  · exact ⟨12721, 5, prime_12721, prime_5, by norm_num⟩
  · exact ⟨12671, 31, prime_12671, prime_31, by norm_num⟩
  · exact ⟨12721, 7, prime_12721, prime_7, by norm_num⟩
  · exact ⟨12703, 17, prime_12703, prime_17, by norm_num⟩
  · exact ⟨12713, 13, prime_12713, prime_13, by norm_num⟩
  · exact ⟨12703, 19, prime_12703, prime_19, by norm_num⟩
  · exact ⟨12739, 2, prime_12739, prime_2, by norm_num⟩
  · exact ⟨12739, 3, prime_12739, prime_3, by norm_num⟩
  · exact ⟨12743, 2, prime_12743, prime_2, by norm_num⟩
  · exact ⟨12743, 3, prime_12743, prime_3, by norm_num⟩
  · exact ⟨12713, 19, prime_12713, prime_19, by norm_num⟩
  · exact ⟨12743, 5, prime_12743, prime_5, by norm_num⟩
  · exact ⟨12721, 17, prime_12721, prime_17, by norm_num⟩
  · exact ⟨12743, 7, prime_12743, prime_7, by norm_num⟩
  · exact ⟨12721, 19, prime_12721, prime_19, by norm_num⟩
  · exact ⟨12757, 2, prime_12757, prime_2, by norm_num⟩
  · exact ⟨12757, 3, prime_12757, prime_3, by norm_num⟩
  · exact ⟨12743, 11, prime_12743, prime_11, by norm_num⟩
  · exact ⟨12763, 2, prime_12763, prime_2, by norm_num⟩
  · exact ⟨12763, 3, prime_12763, prime_3, by norm_num⟩
  · exact ⟨12757, 7, prime_12757, prime_7, by norm_num⟩
  · exact ⟨12763, 5, prime_12763, prime_5, by norm_num⟩
  · exact ⟨12713, 31, prime_12713, prime_31, by norm_num⟩
  · exact ⟨12763, 7, prime_12763, prime_7, by norm_num⟩
  · exact ⟨12757, 11, prime_12757, prime_11, by norm_num⟩
  · exact ⟨12743, 19, prime_12743, prime_19, by norm_num⟩
  · exact ⟨12757, 13, prime_12757, prime_13, by norm_num⟩
  · exact ⟨12781, 2, prime_12781, prime_2, by norm_num⟩
  · exact ⟨12781, 3, prime_12781, prime_3, by norm_num⟩
  · exact ⟨12763, 13, prime_12763, prime_13, by norm_num⟩
  · exact ⟨12781, 5, prime_12781, prime_5, by norm_num⟩
  · exact ⟨12671, 61, prime_12671, prime_61, by norm_num⟩
  · exact ⟨12791, 2, prime_12791, prime_2, by norm_num⟩
  · exact ⟨12791, 3, prime_12791, prime_3, by norm_num⟩
  · exact ⟨12713, 43, prime_12713, prime_43, by norm_num⟩
  · exact ⟨12791, 5, prime_12791, prime_5, by norm_num⟩
  · exact ⟨12799, 2, prime_12799, prime_2, by norm_num⟩
  · exact ⟨12799, 3, prime_12799, prime_3, by norm_num⟩

private theorem lemoine_chunk_64 : ∀ k : ℕ, 6403 ≤ k → k ≤ 6502 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨12781, 13, prime_12781, prime_13, by norm_num⟩
  · exact ⟨12799, 5, prime_12799, prime_5, by norm_num⟩
  · exact ⟨12689, 61, prime_12689, prime_61, by norm_num⟩
  · exact ⟨12809, 2, prime_12809, prime_2, by norm_num⟩
  · exact ⟨12809, 3, prime_12809, prime_3, by norm_num⟩
  · exact ⟨12791, 13, prime_12791, prime_13, by norm_num⟩
  · exact ⟨12809, 5, prime_12809, prime_5, by norm_num⟩
  · exact ⟨12799, 11, prime_12799, prime_11, by norm_num⟩
  · exact ⟨12809, 7, prime_12809, prime_7, by norm_num⟩
  · exact ⟨12821, 2, prime_12821, prime_2, by norm_num⟩
  · exact ⟨12823, 2, prime_12823, prime_2, by norm_num⟩
  · exact ⟨12823, 3, prime_12823, prime_3, by norm_num⟩
  · exact ⟨12821, 5, prime_12821, prime_5, by norm_num⟩
  · exact ⟨12829, 2, prime_12829, prime_2, by norm_num⟩
  · exact ⟨12829, 3, prime_12829, prime_3, by norm_num⟩
  · exact ⟨12823, 7, prime_12823, prime_7, by norm_num⟩
  · exact ⟨12829, 5, prime_12829, prime_5, by norm_num⟩
  · exact ⟨12647, 97, prime_12647, prime_97, by norm_num⟩
  · exact ⟨12829, 7, prime_12829, prime_7, by norm_num⟩
  · exact ⟨12841, 2, prime_12841, prime_2, by norm_num⟩
  · exact ⟨12841, 3, prime_12841, prime_3, by norm_num⟩
  · exact ⟨12823, 13, prime_12823, prime_13, by norm_num⟩
  · exact ⟨12841, 5, prime_12841, prime_5, by norm_num⟩
  · exact ⟨12791, 31, prime_12791, prime_31, by norm_num⟩
  · exact ⟨12841, 7, prime_12841, prime_7, by norm_num⟩
  · exact ⟨12853, 2, prime_12853, prime_2, by norm_num⟩
  · exact ⟨12853, 3, prime_12853, prime_3, by norm_num⟩
  · exact ⟨12823, 19, prime_12823, prime_19, by norm_num⟩
  · exact ⟨12853, 5, prime_12853, prime_5, by norm_num⟩
  · exact ⟨12791, 37, prime_12791, prime_37, by norm_num⟩
  · exact ⟨12853, 7, prime_12853, prime_7, by norm_num⟩
  · exact ⟨12823, 23, prime_12823, prime_23, by norm_num⟩
  · exact ⟨12809, 31, prime_12809, prime_31, by norm_num⟩
  · exact ⟨12799, 37, prime_12799, prime_37, by norm_num⟩
  · exact ⟨12853, 11, prime_12853, prime_11, by norm_num⟩
  · exact ⟨12791, 43, prime_12791, prime_43, by norm_num⟩
  · exact ⟨12853, 13, prime_12853, prime_13, by norm_num⟩
  · exact ⟨12823, 29, prime_12823, prime_29, by norm_num⟩
  · exact ⟨12821, 31, prime_12821, prime_31, by norm_num⟩
  · exact ⟨12823, 31, prime_12823, prime_31, by norm_num⟩
  · exact ⟨12853, 17, prime_12853, prime_17, by norm_num⟩
  · exact ⟨12743, 73, prime_12743, prime_73, by norm_num⟩
  · exact ⟨12853, 19, prime_12853, prime_19, by norm_num⟩
  · exact ⟨12889, 2, prime_12889, prime_2, by norm_num⟩
  · exact ⟨12889, 3, prime_12889, prime_3, by norm_num⟩
  · exact ⟨12893, 2, prime_12893, prime_2, by norm_num⟩
  · exact ⟨12893, 3, prime_12893, prime_3, by norm_num⟩
  · exact ⟨12743, 79, prime_12743, prime_79, by norm_num⟩
  · exact ⟨12899, 2, prime_12899, prime_2, by norm_num⟩
  · exact ⟨12899, 3, prime_12899, prime_3, by norm_num⟩
  · exact ⟨12893, 7, prime_12893, prime_7, by norm_num⟩
  · exact ⟨12899, 5, prime_12899, prime_5, by norm_num⟩
  · exact ⟨12907, 2, prime_12907, prime_2, by norm_num⟩
  · exact ⟨12907, 3, prime_12907, prime_3, by norm_num⟩
  · exact ⟨12911, 2, prime_12911, prime_2, by norm_num⟩
  · exact ⟨12911, 3, prime_12911, prime_3, by norm_num⟩
  · exact ⟨12893, 13, prime_12893, prime_13, by norm_num⟩
  · exact ⟨12917, 2, prime_12917, prime_2, by norm_num⟩
  · exact ⟨12919, 2, prime_12919, prime_2, by norm_num⟩
  · exact ⟨12919, 3, prime_12919, prime_3, by norm_num⟩
  · exact ⟨12923, 2, prime_12923, prime_2, by norm_num⟩
  · exact ⟨12923, 3, prime_12923, prime_3, by norm_num⟩
  · exact ⟨12917, 7, prime_12917, prime_7, by norm_num⟩
  · exact ⟨12923, 5, prime_12923, prime_5, by norm_num⟩
  · exact ⟨12889, 23, prime_12889, prime_23, by norm_num⟩
  · exact ⟨12923, 7, prime_12923, prime_7, by norm_num⟩
  · exact ⟨12917, 11, prime_12917, prime_11, by norm_num⟩
  · exact ⟨12919, 11, prime_12919, prime_11, by norm_num⟩
  · exact ⟨12917, 13, prime_12917, prime_13, by norm_num⟩
  · exact ⟨12941, 2, prime_12941, prime_2, by norm_num⟩
  · exact ⟨12941, 3, prime_12941, prime_3, by norm_num⟩
  · exact ⟨12923, 13, prime_12923, prime_13, by norm_num⟩
  · exact ⟨12941, 5, prime_12941, prime_5, by norm_num⟩
  · exact ⟨12919, 17, prime_12919, prime_17, by norm_num⟩
  · exact ⟨12941, 7, prime_12941, prime_7, by norm_num⟩
  · exact ⟨12953, 2, prime_12953, prime_2, by norm_num⟩
  · exact ⟨12953, 3, prime_12953, prime_3, by norm_num⟩
  · exact ⟨12923, 19, prime_12923, prime_19, by norm_num⟩
  · exact ⟨12959, 2, prime_12959, prime_2, by norm_num⟩
  · exact ⟨12959, 3, prime_12959, prime_3, by norm_num⟩
  · exact ⟨12953, 7, prime_12953, prime_7, by norm_num⟩
  · exact ⟨12959, 5, prime_12959, prime_5, by norm_num⟩
  · exact ⟨12967, 2, prime_12967, prime_2, by norm_num⟩
  · exact ⟨12967, 3, prime_12967, prime_3, by norm_num⟩
  · exact ⟨12953, 11, prime_12953, prime_11, by norm_num⟩
  · exact ⟨12973, 2, prime_12973, prime_2, by norm_num⟩
  · exact ⟨12973, 3, prime_12973, prime_3, by norm_num⟩
  · exact ⟨12967, 7, prime_12967, prime_7, by norm_num⟩
  · exact ⟨12979, 2, prime_12979, prime_2, by norm_num⟩
  · exact ⟨12979, 3, prime_12979, prime_3, by norm_num⟩
  · exact ⟨12983, 2, prime_12983, prime_2, by norm_num⟩
  · exact ⟨12983, 3, prime_12983, prime_3, by norm_num⟩
  · exact ⟨12953, 19, prime_12953, prime_19, by norm_num⟩
  · exact ⟨12983, 5, prime_12983, prime_5, by norm_num⟩
  · exact ⟨12973, 11, prime_12973, prime_11, by norm_num⟩
  · exact ⟨12983, 7, prime_12983, prime_7, by norm_num⟩
  · exact ⟨12973, 13, prime_12973, prime_13, by norm_num⟩
  · exact ⟨12979, 11, prime_12979, prime_11, by norm_num⟩
  · exact ⟨12941, 31, prime_12941, prime_31, by norm_num⟩
  · exact ⟨13001, 2, prime_13001, prime_2, by norm_num⟩

private theorem lemoine_chunk_65 : ∀ k : ℕ, 6503 ≤ k → k ≤ 6602 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨13003, 2, prime_13003, prime_2, by norm_num⟩
  · exact ⟨13003, 3, prime_13003, prime_3, by norm_num⟩
  · exact ⟨13007, 2, prime_13007, prime_2, by norm_num⟩
  · exact ⟨13009, 2, prime_13009, prime_2, by norm_num⟩
  · exact ⟨13009, 3, prime_13009, prime_3, by norm_num⟩
  · exact ⟨13007, 5, prime_13007, prime_5, by norm_num⟩
  · exact ⟨13009, 5, prime_13009, prime_5, by norm_num⟩
  · exact ⟨13007, 7, prime_13007, prime_7, by norm_num⟩
  · exact ⟨13009, 7, prime_13009, prime_7, by norm_num⟩
  · exact ⟨13003, 11, prime_13003, prime_11, by norm_num⟩
  · exact ⟨13001, 13, prime_13001, prime_13, by norm_num⟩
  · exact ⟨13007, 11, prime_13007, prime_11, by norm_num⟩
  · exact ⟨13009, 11, prime_13009, prime_11, by norm_num⟩
  · exact ⟨13007, 13, prime_13007, prime_13, by norm_num⟩
  · exact ⟨13009, 13, prime_13009, prime_13, by norm_num⟩
  · exact ⟨13033, 2, prime_13033, prime_2, by norm_num⟩
  · exact ⟨13033, 3, prime_13033, prime_3, by norm_num⟩
  · exact ⟨13037, 2, prime_13037, prime_2, by norm_num⟩
  · exact ⟨13037, 3, prime_13037, prime_3, by norm_num⟩
  · exact ⟨13007, 19, prime_13007, prime_19, by norm_num⟩
  · exact ⟨13043, 2, prime_13043, prime_2, by norm_num⟩
  · exact ⟨13043, 3, prime_13043, prime_3, by norm_num⟩
  · exact ⟨13037, 7, prime_13037, prime_7, by norm_num⟩
  · exact ⟨13049, 2, prime_13049, prime_2, by norm_num⟩
  · exact ⟨13049, 3, prime_13049, prime_3, by norm_num⟩
  · exact ⟨13043, 7, prime_13043, prime_7, by norm_num⟩
  · exact ⟨13049, 5, prime_13049, prime_5, by norm_num⟩
  · exact ⟨13003, 29, prime_13003, prime_29, by norm_num⟩
  · exact ⟨13049, 7, prime_13049, prime_7, by norm_num⟩
  · exact ⟨13043, 11, prime_13043, prime_11, by norm_num⟩
  · exact ⟨13063, 2, prime_13063, prime_2, by norm_num⟩
  · exact ⟨13063, 3, prime_13063, prime_3, by norm_num⟩
  · exact ⟨13049, 11, prime_13049, prime_11, by norm_num⟩
  · exact ⟨13063, 5, prime_13063, prime_5, by norm_num⟩
  · exact ⟨13049, 13, prime_13049, prime_13, by norm_num⟩
  · exact ⟨13063, 7, prime_13063, prime_7, by norm_num⟩
  · exact ⟨13033, 23, prime_13033, prime_23, by norm_num⟩
  · exact ⟨13043, 19, prime_13043, prime_19, by norm_num⟩
  · exact ⟨13049, 17, prime_13049, prime_17, by norm_num⟩
  · exact ⟨13063, 11, prime_13063, prime_11, by norm_num⟩
  · exact ⟨13049, 19, prime_13049, prime_19, by norm_num⟩
  · exact ⟨13063, 13, prime_13063, prime_13, by norm_num⟩
  · exact ⟨13033, 29, prime_13033, prime_29, by norm_num⟩
  · exact ⟨13007, 43, prime_13007, prime_43, by norm_num⟩
  · exact ⟨13049, 23, prime_13049, prime_23, by norm_num⟩
  · exact ⟨13093, 2, prime_13093, prime_2, by norm_num⟩
  · exact ⟨13093, 3, prime_13093, prime_3, by norm_num⟩
  · exact ⟨13063, 19, prime_13063, prime_19, by norm_num⟩
  · exact ⟨13099, 2, prime_13099, prime_2, by norm_num⟩
  · exact ⟨13099, 3, prime_13099, prime_3, by norm_num⟩
  · exact ⟨13103, 2, prime_13103, prime_2, by norm_num⟩
  · exact ⟨13103, 3, prime_13103, prime_3, by norm_num⟩
  · exact ⟨13049, 31, prime_13049, prime_31, by norm_num⟩
  · exact ⟨13109, 2, prime_13109, prime_2, by norm_num⟩
  · exact ⟨13109, 3, prime_13109, prime_3, by norm_num⟩
  · exact ⟨13103, 7, prime_13103, prime_7, by norm_num⟩
  · exact ⟨13109, 5, prime_13109, prime_5, by norm_num⟩
  · exact ⟨13099, 11, prime_13099, prime_11, by norm_num⟩
  · exact ⟨13109, 7, prime_13109, prime_7, by norm_num⟩
  · exact ⟨13121, 2, prime_13121, prime_2, by norm_num⟩
  · exact ⟨13121, 3, prime_13121, prime_3, by norm_num⟩
  · exact ⟨13103, 13, prime_13103, prime_13, by norm_num⟩
  · exact ⟨13127, 2, prime_13127, prime_2, by norm_num⟩
  · exact ⟨13127, 3, prime_13127, prime_3, by norm_num⟩
  · exact ⟨13121, 7, prime_13121, prime_7, by norm_num⟩
  · exact ⟨13127, 5, prime_13127, prime_5, by norm_num⟩
  · exact ⟨13093, 23, prime_13093, prime_23, by norm_num⟩
  · exact ⟨13127, 7, prime_13127, prime_7, by norm_num⟩
  · exact ⟨13121, 11, prime_13121, prime_11, by norm_num⟩
  · exact ⟨13099, 23, prime_13099, prime_23, by norm_num⟩
  · exact ⟨13121, 13, prime_13121, prime_13, by norm_num⟩
  · exact ⟨13127, 11, prime_13127, prime_11, by norm_num⟩
  · exact ⟨13147, 2, prime_13147, prime_2, by norm_num⟩
  · exact ⟨13147, 3, prime_13147, prime_3, by norm_num⟩
  · exact ⟨13151, 2, prime_13151, prime_2, by norm_num⟩
  · exact ⟨13151, 3, prime_13151, prime_3, by norm_num⟩
  · exact ⟨13121, 19, prime_13121, prime_19, by norm_num⟩
  · exact ⟨13151, 5, prime_13151, prime_5, by norm_num⟩
  · exact ⟨13159, 2, prime_13159, prime_2, by norm_num⟩
  · exact ⟨13159, 3, prime_13159, prime_3, by norm_num⟩
  · exact ⟨13163, 2, prime_13163, prime_2, by norm_num⟩
  · exact ⟨13163, 3, prime_13163, prime_3, by norm_num⟩
  · exact ⟨13109, 31, prime_13109, prime_31, by norm_num⟩
  · exact ⟨13163, 5, prime_13163, prime_5, by norm_num⟩
  · exact ⟨13171, 2, prime_13171, prime_2, by norm_num⟩
  · exact ⟨13171, 3, prime_13171, prime_3, by norm_num⟩
  · exact ⟨13121, 29, prime_13121, prime_29, by norm_num⟩
  · exact ⟨13177, 2, prime_13177, prime_2, by norm_num⟩
  · exact ⟨13177, 3, prime_13177, prime_3, by norm_num⟩
  · exact ⟨13171, 7, prime_13171, prime_7, by norm_num⟩
  · exact ⟨13183, 2, prime_13183, prime_2, by norm_num⟩
  · exact ⟨13183, 3, prime_13183, prime_3, by norm_num⟩
  · exact ⟨13187, 2, prime_13187, prime_2, by norm_num⟩
  · exact ⟨13187, 3, prime_13187, prime_3, by norm_num⟩
  · exact ⟨13121, 37, prime_13121, prime_37, by norm_num⟩
  · exact ⟨13187, 5, prime_13187, prime_5, by norm_num⟩
  · exact ⟨13177, 11, prime_13177, prime_11, by norm_num⟩
  · exact ⟨13187, 7, prime_13187, prime_7, by norm_num⟩
  · exact ⟨13177, 13, prime_13177, prime_13, by norm_num⟩
  · exact ⟨13183, 11, prime_13183, prime_11, by norm_num⟩

private theorem lemoine_chunk_66 : ∀ k : ℕ, 6603 ≤ k → k ≤ 6702 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨13121, 43, prime_13121, prime_43, by norm_num⟩
  · exact ⟨13187, 11, prime_13187, prime_11, by norm_num⟩
  · exact ⟨13177, 17, prime_13177, prime_17, by norm_num⟩
  · exact ⟨13187, 13, prime_13187, prime_13, by norm_num⟩
  · exact ⟨13177, 19, prime_13177, prime_19, by norm_num⟩
  · exact ⟨13183, 17, prime_13183, prime_17, by norm_num⟩
  · exact ⟨13001, 109, prime_13001, prime_109, by norm_num⟩
  · exact ⟨13217, 2, prime_13217, prime_2, by norm_num⟩
  · exact ⟨13219, 2, prime_13219, prime_2, by norm_num⟩
  · exact ⟨13219, 3, prime_13219, prime_3, by norm_num⟩
  · exact ⟨13217, 5, prime_13217, prime_5, by norm_num⟩
  · exact ⟨13219, 5, prime_13219, prime_5, by norm_num⟩
  · exact ⟨13217, 7, prime_13217, prime_7, by norm_num⟩
  · exact ⟨13229, 2, prime_13229, prime_2, by norm_num⟩
  · exact ⟨13229, 3, prime_13229, prime_3, by norm_num⟩
  · exact ⟨13163, 37, prime_13163, prime_37, by norm_num⟩
  · exact ⟨13229, 5, prime_13229, prime_5, by norm_num⟩
  · exact ⟨13219, 11, prime_13219, prime_11, by norm_num⟩
  · exact ⟨13229, 7, prime_13229, prime_7, by norm_num⟩
  · exact ⟨13241, 2, prime_13241, prime_2, by norm_num⟩
  · exact ⟨13241, 3, prime_13241, prime_3, by norm_num⟩
  · exact ⟨13187, 31, prime_13187, prime_31, by norm_num⟩
  · exact ⟨13241, 5, prime_13241, prime_5, by norm_num⟩
  · exact ⟨13249, 2, prime_13249, prime_2, by norm_num⟩
  · exact ⟨13249, 3, prime_13249, prime_3, by norm_num⟩
  · exact ⟨13219, 19, prime_13219, prime_19, by norm_num⟩
  · exact ⟨13249, 5, prime_13249, prime_5, by norm_num⟩
  · exact ⟨13187, 37, prime_13187, prime_37, by norm_num⟩
  · exact ⟨13259, 2, prime_13259, prime_2, by norm_num⟩
  · exact ⟨13259, 3, prime_13259, prime_3, by norm_num⟩
  · exact ⟨13241, 13, prime_13241, prime_13, by norm_num⟩
  · exact ⟨13259, 5, prime_13259, prime_5, by norm_num⟩
  · exact ⟨13267, 2, prime_13267, prime_2, by norm_num⟩
  · exact ⟨13267, 3, prime_13267, prime_3, by norm_num⟩
  · exact ⟨13249, 13, prime_13249, prime_13, by norm_num⟩
  · exact ⟨13267, 5, prime_13267, prime_5, by norm_num⟩
  · exact ⟨13241, 19, prime_13241, prime_19, by norm_num⟩
  · exact ⟨13267, 7, prime_13267, prime_7, by norm_num⟩
  · exact ⟨13249, 17, prime_13249, prime_17, by norm_num⟩
  · exact ⟨13259, 13, prime_13259, prime_13, by norm_num⟩
  · exact ⟨13249, 19, prime_13249, prime_19, by norm_num⟩
  · exact ⟨13267, 11, prime_13267, prime_11, by norm_num⟩
  · exact ⟨13229, 31, prime_13229, prime_31, by norm_num⟩
  · exact ⟨13267, 13, prime_13267, prime_13, by norm_num⟩
  · exact ⟨13291, 2, prime_13291, prime_2, by norm_num⟩
  · exact ⟨13291, 3, prime_13291, prime_3, by norm_num⟩
  · exact ⟨13241, 29, prime_13241, prime_29, by norm_num⟩
  · exact ⟨13297, 2, prime_13297, prime_2, by norm_num⟩
  · exact ⟨13297, 3, prime_13297, prime_3, by norm_num⟩
  · exact ⟨13291, 7, prime_13291, prime_7, by norm_num⟩
  · exact ⟨13297, 5, prime_13297, prime_5, by norm_num⟩
  · exact ⟨13187, 61, prime_13187, prime_61, by norm_num⟩
  · exact ⟨13297, 7, prime_13297, prime_7, by norm_num⟩
  · exact ⟨13309, 2, prime_13309, prime_2, by norm_num⟩
  · exact ⟨13309, 3, prime_13309, prime_3, by norm_num⟩
  · exact ⟨13313, 2, prime_13313, prime_2, by norm_num⟩
  · exact ⟨13313, 3, prime_13313, prime_3, by norm_num⟩
  · exact ⟨13259, 31, prime_13259, prime_31, by norm_num⟩
  · exact ⟨13313, 5, prime_13313, prime_5, by norm_num⟩
  · exact ⟨13291, 17, prime_13291, prime_17, by norm_num⟩
  · exact ⟨13313, 7, prime_13313, prime_7, by norm_num⟩
  · exact ⟨13291, 19, prime_13291, prime_19, by norm_num⟩
  · exact ⟨13327, 2, prime_13327, prime_2, by norm_num⟩
  · exact ⟨13327, 3, prime_13327, prime_3, by norm_num⟩
  · exact ⟨13331, 2, prime_13331, prime_2, by norm_num⟩
  · exact ⟨13331, 3, prime_13331, prime_3, by norm_num⟩
  · exact ⟨13313, 13, prime_13313, prime_13, by norm_num⟩
  · exact ⟨13337, 2, prime_13337, prime_2, by norm_num⟩
  · exact ⟨13339, 2, prime_13339, prime_2, by norm_num⟩
  · exact ⟨13339, 3, prime_13339, prime_3, by norm_num⟩
  · exact ⟨13337, 5, prime_13337, prime_5, by norm_num⟩
  · exact ⟨13339, 5, prime_13339, prime_5, by norm_num⟩
  · exact ⟨13337, 7, prime_13337, prime_7, by norm_num⟩
  · exact ⟨13339, 7, prime_13339, prime_7, by norm_num⟩
  · exact ⟨13309, 23, prime_13309, prime_23, by norm_num⟩
  · exact ⟨13331, 13, prime_13331, prime_13, by norm_num⟩
  · exact ⟨13337, 11, prime_13337, prime_11, by norm_num⟩
  · exact ⟨13339, 11, prime_13339, prime_11, by norm_num⟩
  · exact ⟨13337, 13, prime_13337, prime_13, by norm_num⟩
  · exact ⟨13339, 13, prime_13339, prime_13, by norm_num⟩
  · exact ⟨13309, 29, prime_13309, prime_29, by norm_num⟩
  · exact ⟨13331, 19, prime_13331, prime_19, by norm_num⟩
  · exact ⟨13367, 2, prime_13367, prime_2, by norm_num⟩
  · exact ⟨13367, 3, prime_13367, prime_3, by norm_num⟩
  · exact ⟨13337, 19, prime_13337, prime_19, by norm_num⟩
  · exact ⟨13367, 5, prime_13367, prime_5, by norm_num⟩
  · exact ⟨13297, 41, prime_13297, prime_41, by norm_num⟩
  · exact ⟨13367, 7, prime_13367, prime_7, by norm_num⟩
  · exact ⟨13337, 23, prime_13337, prime_23, by norm_num⟩
  · exact ⟨13381, 2, prime_13381, prime_2, by norm_num⟩
  · exact ⟨13381, 3, prime_13381, prime_3, by norm_num⟩
  · exact ⟨13367, 11, prime_13367, prime_11, by norm_num⟩
  · exact ⟨13381, 5, prime_13381, prime_5, by norm_num⟩
  · exact ⟨13367, 13, prime_13367, prime_13, by norm_num⟩
  · exact ⟨13381, 7, prime_13381, prime_7, by norm_num⟩
  · exact ⟨13339, 29, prime_13339, prime_29, by norm_num⟩
  · exact ⟨13337, 31, prime_13337, prime_31, by norm_num⟩
  · exact ⟨13397, 2, prime_13397, prime_2, by norm_num⟩
  · exact ⟨13399, 2, prime_13399, prime_2, by norm_num⟩
  · exact ⟨13399, 3, prime_13399, prime_3, by norm_num⟩

private theorem lemoine_chunk_67 : ∀ k : ℕ, 6703 ≤ k → k ≤ 6802 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨13397, 5, prime_13397, prime_5, by norm_num⟩
  · exact ⟨13399, 5, prime_13399, prime_5, by norm_num⟩
  · exact ⟨13397, 7, prime_13397, prime_7, by norm_num⟩
  · exact ⟨13399, 7, prime_13399, prime_7, by norm_num⟩
  · exact ⟨13411, 2, prime_13411, prime_2, by norm_num⟩
  · exact ⟨13411, 3, prime_13411, prime_3, by norm_num⟩
  · exact ⟨13397, 11, prime_13397, prime_11, by norm_num⟩
  · exact ⟨13417, 2, prime_13417, prime_2, by norm_num⟩
  · exact ⟨13417, 3, prime_13417, prime_3, by norm_num⟩
  · exact ⟨13421, 2, prime_13421, prime_2, by norm_num⟩
  · exact ⟨13421, 3, prime_13421, prime_3, by norm_num⟩
  · exact ⟨13367, 31, prime_13367, prime_31, by norm_num⟩
  · exact ⟨13421, 5, prime_13421, prime_5, by norm_num⟩
  · exact ⟨13411, 11, prime_13411, prime_11, by norm_num⟩
  · exact ⟨13421, 7, prime_13421, prime_7, by norm_num⟩
  · exact ⟨13411, 13, prime_13411, prime_13, by norm_num⟩
  · exact ⟨13417, 11, prime_13417, prime_11, by norm_num⟩
  · exact ⟨13367, 37, prime_13367, prime_37, by norm_num⟩
  · exact ⟨13421, 11, prime_13421, prime_11, by norm_num⟩
  · exact ⟨13441, 2, prime_13441, prime_2, by norm_num⟩
  · exact ⟨13441, 3, prime_13441, prime_3, by norm_num⟩
  · exact ⟨13411, 19, prime_13411, prime_19, by norm_num⟩
  · exact ⟨13441, 5, prime_13441, prime_5, by norm_num⟩
  · exact ⟨13367, 43, prime_13367, prime_43, by norm_num⟩
  · exact ⟨13451, 2, prime_13451, prime_2, by norm_num⟩
  · exact ⟨13451, 3, prime_13451, prime_3, by norm_num⟩
  · exact ⟨13421, 19, prime_13421, prime_19, by norm_num⟩
  · exact ⟨13457, 2, prime_13457, prime_2, by norm_num⟩
  · exact ⟨13457, 3, prime_13457, prime_3, by norm_num⟩
  · exact ⟨13451, 7, prime_13451, prime_7, by norm_num⟩
  · exact ⟨13463, 2, prime_13463, prime_2, by norm_num⟩
  · exact ⟨13463, 3, prime_13463, prime_3, by norm_num⟩
  · exact ⟨13457, 7, prime_13457, prime_7, by norm_num⟩
  · exact ⟨13469, 2, prime_13469, prime_2, by norm_num⟩
  · exact ⟨13469, 3, prime_13469, prime_3, by norm_num⟩
  · exact ⟨13463, 7, prime_13463, prime_7, by norm_num⟩
  · exact ⟨13469, 5, prime_13469, prime_5, by norm_num⟩
  · exact ⟨13477, 2, prime_13477, prime_2, by norm_num⟩
  · exact ⟨13477, 3, prime_13477, prime_3, by norm_num⟩
  · exact ⟨13463, 11, prime_13463, prime_11, by norm_num⟩
  · exact ⟨13477, 5, prime_13477, prime_5, by norm_num⟩
  · exact ⟨13463, 13, prime_13463, prime_13, by norm_num⟩
  · exact ⟨13487, 2, prime_13487, prime_2, by norm_num⟩
  · exact ⟨13487, 3, prime_13487, prime_3, by norm_num⟩
  · exact ⟨13469, 13, prime_13469, prime_13, by norm_num⟩
  · exact ⟨13487, 5, prime_13487, prime_5, by norm_num⟩
  · exact ⟨13477, 11, prime_13477, prime_11, by norm_num⟩
  · exact ⟨13487, 7, prime_13487, prime_7, by norm_num⟩
  · exact ⟨13499, 2, prime_13499, prime_2, by norm_num⟩
  · exact ⟨13499, 3, prime_13499, prime_3, by norm_num⟩
  · exact ⟨13469, 19, prime_13469, prime_19, by norm_num⟩
  · exact ⟨13499, 5, prime_13499, prime_5, by norm_num⟩
  · exact ⟨13477, 17, prime_13477, prime_17, by norm_num⟩
  · exact ⟨13499, 7, prime_13499, prime_7, by norm_num⟩
  · exact ⟨13477, 19, prime_13477, prime_19, by norm_num⟩
  · exact ⟨13513, 2, prime_13513, prime_2, by norm_num⟩
  · exact ⟨13513, 3, prime_13513, prime_3, by norm_num⟩
  · exact ⟨13499, 11, prime_13499, prime_11, by norm_num⟩
  · exact ⟨13513, 5, prime_13513, prime_5, by norm_num⟩
  · exact ⟨13499, 13, prime_13499, prime_13, by norm_num⟩
  · exact ⟨13523, 2, prime_13523, prime_2, by norm_num⟩
  · exact ⟨13523, 3, prime_13523, prime_3, by norm_num⟩
  · exact ⟨13469, 31, prime_13469, prime_31, by norm_num⟩
  · exact ⟨13523, 5, prime_13523, prime_5, by norm_num⟩
  · exact ⟨13513, 11, prime_13513, prime_11, by norm_num⟩
  · exact ⟨13523, 7, prime_13523, prime_7, by norm_num⟩
  · exact ⟨13513, 13, prime_13513, prime_13, by norm_num⟩
  · exact ⟨13537, 2, prime_13537, prime_2, by norm_num⟩
  · exact ⟨13537, 3, prime_13537, prime_3, by norm_num⟩
  · exact ⟨13523, 11, prime_13523, prime_11, by norm_num⟩
  · exact ⟨13537, 5, prime_13537, prime_5, by norm_num⟩
  · exact ⟨13523, 13, prime_13523, prime_13, by norm_num⟩
  · exact ⟨13537, 7, prime_13537, prime_7, by norm_num⟩
  · exact ⟨13411, 71, prime_13411, prime_71, by norm_num⟩
  · exact ⟨13469, 43, prime_13469, prime_43, by norm_num⟩
  · exact ⟨13553, 2, prime_13553, prime_2, by norm_num⟩
  · exact ⟨13553, 3, prime_13553, prime_3, by norm_num⟩
  · exact ⟨13523, 19, prime_13523, prime_19, by norm_num⟩
  · exact ⟨13553, 5, prime_13553, prime_5, by norm_num⟩
  · exact ⟨13399, 83, prime_13399, prime_83, by norm_num⟩
  · exact ⟨13553, 7, prime_13553, prime_7, by norm_num⟩
  · exact ⟨13523, 23, prime_13523, prime_23, by norm_num⟩
  · exact ⟨13567, 2, prime_13567, prime_2, by norm_num⟩
  · exact ⟨13567, 3, prime_13567, prime_3, by norm_num⟩
  · exact ⟨13553, 11, prime_13553, prime_11, by norm_num⟩
  · exact ⟨13567, 5, prime_13567, prime_5, by norm_num⟩
  · exact ⟨13553, 13, prime_13553, prime_13, by norm_num⟩
  · exact ⟨13577, 2, prime_13577, prime_2, by norm_num⟩
  · exact ⟨13577, 3, prime_13577, prime_3, by norm_num⟩
  · exact ⟨13523, 31, prime_13523, prime_31, by norm_num⟩
  · exact ⟨13577, 5, prime_13577, prime_5, by norm_num⟩
  · exact ⟨13567, 11, prime_13567, prime_11, by norm_num⟩
  · exact ⟨13577, 7, prime_13577, prime_7, by norm_num⟩
  · exact ⟨13567, 13, prime_13567, prime_13, by norm_num⟩
  · exact ⟨13591, 2, prime_13591, prime_2, by norm_num⟩
  · exact ⟨13591, 3, prime_13591, prime_3, by norm_num⟩
  · exact ⟨13577, 11, prime_13577, prime_11, by norm_num⟩
  · exact ⟨13597, 2, prime_13597, prime_2, by norm_num⟩
  · exact ⟨13597, 3, prime_13597, prime_3, by norm_num⟩
  · exact ⟨13591, 7, prime_13591, prime_7, by norm_num⟩

private theorem lemoine_chunk_68 : ∀ k : ℕ, 6803 ≤ k → k ≤ 6902 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨13597, 5, prime_13597, prime_5, by norm_num⟩
  · exact ⟨13523, 43, prime_13523, prime_43, by norm_num⟩
  · exact ⟨13597, 7, prime_13597, prime_7, by norm_num⟩
  · exact ⟨13591, 11, prime_13591, prime_11, by norm_num⟩
  · exact ⟨13577, 19, prime_13577, prime_19, by norm_num⟩
  · exact ⟨13613, 2, prime_13613, prime_2, by norm_num⟩
  · exact ⟨13613, 3, prime_13613, prime_3, by norm_num⟩
  · exact ⟨13499, 61, prime_13499, prime_61, by norm_num⟩
  · exact ⟨13619, 2, prime_13619, prime_2, by norm_num⟩
  · exact ⟨13619, 3, prime_13619, prime_3, by norm_num⟩
  · exact ⟨13613, 7, prime_13613, prime_7, by norm_num⟩
  · exact ⟨13619, 5, prime_13619, prime_5, by norm_num⟩
  · exact ⟨13627, 2, prime_13627, prime_2, by norm_num⟩
  · exact ⟨13627, 3, prime_13627, prime_3, by norm_num⟩
  · exact ⟨13613, 11, prime_13613, prime_11, by norm_num⟩
  · exact ⟨13633, 2, prime_13633, prime_2, by norm_num⟩
  · exact ⟨13633, 3, prime_13633, prime_3, by norm_num⟩
  · exact ⟨13627, 7, prime_13627, prime_7, by norm_num⟩
  · exact ⟨13633, 5, prime_13633, prime_5, by norm_num⟩
  · exact ⟨13619, 13, prime_13619, prime_13, by norm_num⟩
  · exact ⟨13633, 7, prime_13633, prime_7, by norm_num⟩
  · exact ⟨13627, 11, prime_13627, prime_11, by norm_num⟩
  · exact ⟨13613, 19, prime_13613, prime_19, by norm_num⟩
  · exact ⟨13649, 2, prime_13649, prime_2, by norm_num⟩
  · exact ⟨13649, 3, prime_13649, prime_3, by norm_num⟩
  · exact ⟨13619, 19, prime_13619, prime_19, by norm_num⟩
  · exact ⟨13649, 5, prime_13649, prime_5, by norm_num⟩
  · exact ⟨13627, 17, prime_13627, prime_17, by norm_num⟩
  · exact ⟨13649, 7, prime_13649, prime_7, by norm_num⟩
  · exact ⟨13627, 19, prime_13627, prime_19, by norm_num⟩
  · exact ⟨13633, 17, prime_13633, prime_17, by norm_num⟩
  · exact ⟨13523, 73, prime_13523, prime_73, by norm_num⟩
  · exact ⟨13649, 11, prime_13649, prime_11, by norm_num⟩
  · exact ⟨13669, 2, prime_13669, prime_2, by norm_num⟩
  · exact ⟨13669, 3, prime_13669, prime_3, by norm_num⟩
  · exact ⟨13619, 29, prime_13619, prime_29, by norm_num⟩
  · exact ⟨13669, 5, prime_13669, prime_5, by norm_num⟩
  · exact ⟨13619, 31, prime_13619, prime_31, by norm_num⟩
  · exact ⟨13679, 2, prime_13679, prime_2, by norm_num⟩
  · exact ⟨13681, 2, prime_13681, prime_2, by norm_num⟩
  · exact ⟨13681, 3, prime_13681, prime_3, by norm_num⟩
  · exact ⟨13679, 5, prime_13679, prime_5, by norm_num⟩
  · exact ⟨13687, 2, prime_13687, prime_2, by norm_num⟩
  · exact ⟨13687, 3, prime_13687, prime_3, by norm_num⟩
  · exact ⟨13691, 2, prime_13691, prime_2, by norm_num⟩
  · exact ⟨13693, 2, prime_13693, prime_2, by norm_num⟩
  · exact ⟨13693, 3, prime_13693, prime_3, by norm_num⟩
  · exact ⟨13697, 2, prime_13697, prime_2, by norm_num⟩
  · exact ⟨13697, 3, prime_13697, prime_3, by norm_num⟩
  · exact ⟨13691, 7, prime_13691, prime_7, by norm_num⟩
  · exact ⟨13697, 5, prime_13697, prime_5, by norm_num⟩
  · exact ⟨13687, 11, prime_13687, prime_11, by norm_num⟩
  · exact ⟨13697, 7, prime_13697, prime_7, by norm_num⟩
  · exact ⟨13709, 2, prime_13709, prime_2, by norm_num⟩
  · exact ⟨13711, 2, prime_13711, prime_2, by norm_num⟩
  · exact ⟨13711, 3, prime_13711, prime_3, by norm_num⟩
  · exact ⟨13709, 5, prime_13709, prime_5, by norm_num⟩
  · exact ⟨13711, 5, prime_13711, prime_5, by norm_num⟩
  · exact ⟨13709, 7, prime_13709, prime_7, by norm_num⟩
  · exact ⟨13721, 2, prime_13721, prime_2, by norm_num⟩
  · exact ⟨13723, 2, prime_13723, prime_2, by norm_num⟩
  · exact ⟨13723, 3, prime_13723, prime_3, by norm_num⟩
  · exact ⟨13721, 5, prime_13721, prime_5, by norm_num⟩
  · exact ⟨13729, 2, prime_13729, prime_2, by norm_num⟩
  · exact ⟨13729, 3, prime_13729, prime_3, by norm_num⟩
  · exact ⟨13723, 7, prime_13723, prime_7, by norm_num⟩
  · exact ⟨13729, 5, prime_13729, prime_5, by norm_num⟩
  · exact ⟨13679, 31, prime_13679, prime_31, by norm_num⟩
  · exact ⟨13729, 7, prime_13729, prime_7, by norm_num⟩
  · exact ⟨13723, 11, prime_13723, prime_11, by norm_num⟩
  · exact ⟨13721, 13, prime_13721, prime_13, by norm_num⟩
  · exact ⟨13723, 13, prime_13723, prime_13, by norm_num⟩
  · exact ⟨13729, 11, prime_13729, prime_11, by norm_num⟩
  · exact ⟨13691, 31, prime_13691, prime_31, by norm_num⟩
  · exact ⟨13751, 2, prime_13751, prime_2, by norm_num⟩
  · exact ⟨13751, 3, prime_13751, prime_3, by norm_num⟩
  · exact ⟨13721, 19, prime_13721, prime_19, by norm_num⟩
  · exact ⟨13757, 2, prime_13757, prime_2, by norm_num⟩
  · exact ⟨13759, 2, prime_13759, prime_2, by norm_num⟩
  · exact ⟨13759, 3, prime_13759, prime_3, by norm_num⟩
  · exact ⟨13763, 2, prime_13763, prime_2, by norm_num⟩
  · exact ⟨13763, 3, prime_13763, prime_3, by norm_num⟩
  · exact ⟨13757, 7, prime_13757, prime_7, by norm_num⟩
  · exact ⟨13763, 5, prime_13763, prime_5, by norm_num⟩
  · exact ⟨13729, 23, prime_13729, prime_23, by norm_num⟩
  · exact ⟨13763, 7, prime_13763, prime_7, by norm_num⟩
  · exact ⟨13757, 11, prime_13757, prime_11, by norm_num⟩
  · exact ⟨13759, 11, prime_13759, prime_11, by norm_num⟩
  · exact ⟨13757, 13, prime_13757, prime_13, by norm_num⟩
  · exact ⟨13781, 2, prime_13781, prime_2, by norm_num⟩
  · exact ⟨13781, 3, prime_13781, prime_3, by norm_num⟩
  · exact ⟨13763, 13, prime_13763, prime_13, by norm_num⟩
  · exact ⟨13781, 5, prime_13781, prime_5, by norm_num⟩
  · exact ⟨13789, 2, prime_13789, prime_2, by norm_num⟩
  · exact ⟨13789, 3, prime_13789, prime_3, by norm_num⟩
  · exact ⟨13763, 17, prime_13763, prime_17, by norm_num⟩
  · exact ⟨13789, 5, prime_13789, prime_5, by norm_num⟩
  · exact ⟨13763, 19, prime_13763, prime_19, by norm_num⟩
  · exact ⟨13799, 2, prime_13799, prime_2, by norm_num⟩
  · exact ⟨13799, 3, prime_13799, prime_3, by norm_num⟩

private theorem lemoine_chunk_69 : ∀ k : ℕ, 6903 ≤ k → k ≤ 7002 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨13781, 13, prime_13781, prime_13, by norm_num⟩
  · exact ⟨13799, 5, prime_13799, prime_5, by norm_num⟩
  · exact ⟨13807, 2, prime_13807, prime_2, by norm_num⟩
  · exact ⟨13807, 3, prime_13807, prime_3, by norm_num⟩
  · exact ⟨13789, 13, prime_13789, prime_13, by norm_num⟩
  · exact ⟨13807, 5, prime_13807, prime_5, by norm_num⟩
  · exact ⟨13781, 19, prime_13781, prime_19, by norm_num⟩
  · exact ⟨13807, 7, prime_13807, prime_7, by norm_num⟩
  · exact ⟨13789, 17, prime_13789, prime_17, by norm_num⟩
  · exact ⟨13799, 13, prime_13799, prime_13, by norm_num⟩
  · exact ⟨13789, 19, prime_13789, prime_19, by norm_num⟩
  · exact ⟨13807, 11, prime_13807, prime_11, by norm_num⟩
  · exact ⟨13757, 37, prime_13757, prime_37, by norm_num⟩
  · exact ⟨13829, 2, prime_13829, prime_2, by norm_num⟩
  · exact ⟨13831, 2, prime_13831, prime_2, by norm_num⟩
  · exact ⟨13831, 3, prime_13831, prime_3, by norm_num⟩
  · exact ⟨13829, 5, prime_13829, prime_5, by norm_num⟩
  · exact ⟨13831, 5, prime_13831, prime_5, by norm_num⟩
  · exact ⟨13829, 7, prime_13829, prime_7, by norm_num⟩
  · exact ⟨13841, 2, prime_13841, prime_2, by norm_num⟩
  · exact ⟨13841, 3, prime_13841, prime_3, by norm_num⟩
  · exact ⟨13763, 43, prime_13763, prime_43, by norm_num⟩
  · exact ⟨13841, 5, prime_13841, prime_5, by norm_num⟩
  · exact ⟨13831, 11, prime_13831, prime_11, by norm_num⟩
  · exact ⟨13841, 7, prime_13841, prime_7, by norm_num⟩
  · exact ⟨13831, 13, prime_13831, prime_13, by norm_num⟩
  · exact ⟨13693, 83, prime_13693, prime_83, by norm_num⟩
  · exact ⟨13799, 31, prime_13799, prime_31, by norm_num⟩
  · exact ⟨13859, 2, prime_13859, prime_2, by norm_num⟩
  · exact ⟨13859, 3, prime_13859, prime_3, by norm_num⟩
  · exact ⟨13841, 13, prime_13841, prime_13, by norm_num⟩
  · exact ⟨13859, 5, prime_13859, prime_5, by norm_num⟩
  · exact ⟨13789, 41, prime_13789, prime_41, by norm_num⟩
  · exact ⟨13859, 7, prime_13859, prime_7, by norm_num⟩
  · exact ⟨13841, 17, prime_13841, prime_17, by norm_num⟩
  · exact ⟨13873, 2, prime_13873, prime_2, by norm_num⟩
  · exact ⟨13873, 3, prime_13873, prime_3, by norm_num⟩
  · exact ⟨13877, 2, prime_13877, prime_2, by norm_num⟩
  · exact ⟨13879, 2, prime_13879, prime_2, by norm_num⟩
  · exact ⟨13879, 3, prime_13879, prime_3, by norm_num⟩
  · exact ⟨13883, 2, prime_13883, prime_2, by norm_num⟩
  · exact ⟨13883, 3, prime_13883, prime_3, by norm_num⟩
  · exact ⟨13877, 7, prime_13877, prime_7, by norm_num⟩
  · exact ⟨13883, 5, prime_13883, prime_5, by norm_num⟩
  · exact ⟨13873, 11, prime_13873, prime_11, by norm_num⟩
  · exact ⟨13883, 7, prime_13883, prime_7, by norm_num⟩
  · exact ⟨13877, 11, prime_13877, prime_11, by norm_num⟩
  · exact ⟨13879, 11, prime_13879, prime_11, by norm_num⟩
  · exact ⟨13877, 13, prime_13877, prime_13, by norm_num⟩
  · exact ⟨13901, 2, prime_13901, prime_2, by norm_num⟩
  · exact ⟨13903, 2, prime_13903, prime_2, by norm_num⟩
  · exact ⟨13903, 3, prime_13903, prime_3, by norm_num⟩
  · exact ⟨13907, 2, prime_13907, prime_2, by norm_num⟩
  · exact ⟨13907, 3, prime_13907, prime_3, by norm_num⟩
  · exact ⟨13901, 7, prime_13901, prime_7, by norm_num⟩
  · exact ⟨13913, 2, prime_13913, prime_2, by norm_num⟩
  · exact ⟨13913, 3, prime_13913, prime_3, by norm_num⟩
  · exact ⟨13907, 7, prime_13907, prime_7, by norm_num⟩
  · exact ⟨13913, 5, prime_13913, prime_5, by norm_num⟩
  · exact ⟨13921, 2, prime_13921, prime_2, by norm_num⟩
  · exact ⟨13921, 3, prime_13921, prime_3, by norm_num⟩
  · exact ⟨13907, 11, prime_13907, prime_11, by norm_num⟩
  · exact ⟨13921, 5, prime_13921, prime_5, by norm_num⟩
  · exact ⟨13907, 13, prime_13907, prime_13, by norm_num⟩
  · exact ⟨13931, 2, prime_13931, prime_2, by norm_num⟩
  · exact ⟨13933, 2, prime_13933, prime_2, by norm_num⟩
  · exact ⟨13933, 3, prime_13933, prime_3, by norm_num⟩
  · exact ⟨13931, 5, prime_13931, prime_5, by norm_num⟩
  · exact ⟨13933, 5, prime_13933, prime_5, by norm_num⟩
  · exact ⟨13931, 7, prime_13931, prime_7, by norm_num⟩
  · exact ⟨13933, 7, prime_13933, prime_7, by norm_num⟩
  · exact ⟨13903, 23, prime_13903, prime_23, by norm_num⟩
  · exact ⟨13913, 19, prime_13913, prime_19, by norm_num⟩
  · exact ⟨13931, 11, prime_13931, prime_11, by norm_num⟩
  · exact ⟨13933, 11, prime_13933, prime_11, by norm_num⟩
  · exact ⟨13931, 13, prime_13931, prime_13, by norm_num⟩
  · exact ⟨13933, 13, prime_13933, prime_13, by norm_num⟩
  · exact ⟨13903, 29, prime_13903, prime_29, by norm_num⟩
  · exact ⟨13901, 31, prime_13901, prime_31, by norm_num⟩
  · exact ⟨13931, 17, prime_13931, prime_17, by norm_num⟩
  · exact ⟨13963, 2, prime_13963, prime_2, by norm_num⟩
  · exact ⟨13963, 3, prime_13963, prime_3, by norm_num⟩
  · exact ⟨13967, 2, prime_13967, prime_2, by norm_num⟩
  · exact ⟨13967, 3, prime_13967, prime_3, by norm_num⟩
  · exact ⟨13913, 31, prime_13913, prime_31, by norm_num⟩
  · exact ⟨13967, 5, prime_13967, prime_5, by norm_num⟩
  · exact ⟨13933, 23, prime_13933, prime_23, by norm_num⟩
  · exact ⟨13967, 7, prime_13967, prime_7, by norm_num⟩
  · exact ⟨13921, 31, prime_13921, prime_31, by norm_num⟩
  · exact ⟨13963, 11, prime_13963, prime_11, by norm_num⟩
  · exact ⟨13913, 37, prime_13913, prime_37, by norm_num⟩
  · exact ⟨13967, 11, prime_13967, prime_11, by norm_num⟩
  · exact ⟨13933, 29, prime_13933, prime_29, by norm_num⟩
  · exact ⟨13967, 13, prime_13967, prime_13, by norm_num⟩
  · exact ⟨13933, 31, prime_13933, prime_31, by norm_num⟩
  · exact ⟨13963, 17, prime_13963, prime_17, by norm_num⟩
  · exact ⟨13913, 43, prime_13913, prime_43, by norm_num⟩
  · exact ⟨13997, 2, prime_13997, prime_2, by norm_num⟩
  · exact ⟨13999, 2, prime_13999, prime_2, by norm_num⟩
  · exact ⟨13999, 3, prime_13999, prime_3, by norm_num⟩

private theorem lemoine_chunk_70 : ∀ k : ℕ, 7003 ≤ k → k ≤ 7102 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨13997, 5, prime_13997, prime_5, by norm_num⟩
  · exact ⟨13999, 5, prime_13999, prime_5, by norm_num⟩
  · exact ⟨13997, 7, prime_13997, prime_7, by norm_num⟩
  · exact ⟨14009, 2, prime_14009, prime_2, by norm_num⟩
  · exact ⟨14011, 2, prime_14011, prime_2, by norm_num⟩
  · exact ⟨14011, 3, prime_14011, prime_3, by norm_num⟩
  · exact ⟨14009, 5, prime_14009, prime_5, by norm_num⟩
  · exact ⟨14011, 5, prime_14011, prime_5, by norm_num⟩
  · exact ⟨14009, 7, prime_14009, prime_7, by norm_num⟩
  · exact ⟨14011, 7, prime_14011, prime_7, by norm_num⟩
  · exact ⟨13933, 47, prime_13933, prime_47, by norm_num⟩
  · exact ⟨13967, 31, prime_13967, prime_31, by norm_num⟩
  · exact ⟨14009, 11, prime_14009, prime_11, by norm_num⟩
  · exact ⟨14029, 2, prime_14029, prime_2, by norm_num⟩
  · exact ⟨14029, 3, prime_14029, prime_3, by norm_num⟩
  · exact ⟨14033, 2, prime_14033, prime_2, by norm_num⟩
  · exact ⟨14033, 3, prime_14033, prime_3, by norm_num⟩
  · exact ⟨13967, 37, prime_13967, prime_37, by norm_num⟩
  · exact ⟨14033, 5, prime_14033, prime_5, by norm_num⟩
  · exact ⟨14011, 17, prime_14011, prime_17, by norm_num⟩
  · exact ⟨14033, 7, prime_14033, prime_7, by norm_num⟩
  · exact ⟨14011, 19, prime_14011, prime_19, by norm_num⟩
  · exact ⟨14029, 11, prime_14029, prime_11, by norm_num⟩
  · exact ⟨13967, 43, prime_13967, prime_43, by norm_num⟩
  · exact ⟨14051, 2, prime_14051, prime_2, by norm_num⟩
  · exact ⟨14051, 3, prime_14051, prime_3, by norm_num⟩
  · exact ⟨14033, 13, prime_14033, prime_13, by norm_num⟩
  · exact ⟨14057, 2, prime_14057, prime_2, by norm_num⟩
  · exact ⟨14057, 3, prime_14057, prime_3, by norm_num⟩
  · exact ⟨14051, 7, prime_14051, prime_7, by norm_num⟩
  · exact ⟨14057, 5, prime_14057, prime_5, by norm_num⟩
  · exact ⟨14011, 29, prime_14011, prime_29, by norm_num⟩
  · exact ⟨14057, 7, prime_14057, prime_7, by norm_num⟩
  · exact ⟨14051, 11, prime_14051, prime_11, by norm_num⟩
  · exact ⟨14071, 2, prime_14071, prime_2, by norm_num⟩
  · exact ⟨14071, 3, prime_14071, prime_3, by norm_num⟩
  · exact ⟨14057, 11, prime_14057, prime_11, by norm_num⟩
  · exact ⟨14071, 5, prime_14071, prime_5, by norm_num⟩
  · exact ⟨14057, 13, prime_14057, prime_13, by norm_num⟩
  · exact ⟨14081, 2, prime_14081, prime_2, by norm_num⟩
  · exact ⟨14083, 2, prime_14083, prime_2, by norm_num⟩
  · exact ⟨14083, 3, prime_14083, prime_3, by norm_num⟩
  · exact ⟨14087, 2, prime_14087, prime_2, by norm_num⟩
  · exact ⟨14087, 3, prime_14087, prime_3, by norm_num⟩
  · exact ⟨14081, 7, prime_14081, prime_7, by norm_num⟩
  · exact ⟨14087, 5, prime_14087, prime_5, by norm_num⟩
  · exact ⟨13933, 83, prime_13933, prime_83, by norm_num⟩
  · exact ⟨14087, 7, prime_14087, prime_7, by norm_num⟩
  · exact ⟨14081, 11, prime_14081, prime_11, by norm_num⟩
  · exact ⟨14083, 11, prime_14083, prime_11, by norm_num⟩
  · exact ⟨14081, 13, prime_14081, prime_13, by norm_num⟩
  · exact ⟨14087, 11, prime_14087, prime_11, by norm_num⟩
  · exact ⟨14107, 2, prime_14107, prime_2, by norm_num⟩
  · exact ⟨14107, 3, prime_14107, prime_3, by norm_num⟩
  · exact ⟨14081, 17, prime_14081, prime_17, by norm_num⟩
  · exact ⟨14107, 5, prime_14107, prime_5, by norm_num⟩
  · exact ⟨14081, 19, prime_14081, prime_19, by norm_num⟩
  · exact ⟨14107, 7, prime_14107, prime_7, by norm_num⟩
  · exact ⟨14029, 47, prime_14029, prime_47, by norm_num⟩
  · exact ⟨14087, 19, prime_14087, prime_19, by norm_num⟩
  · exact ⟨14081, 23, prime_14081, prime_23, by norm_num⟩
  · exact ⟨14107, 11, prime_14107, prime_11, by norm_num⟩
  · exact ⟨14057, 37, prime_14057, prime_37, by norm_num⟩
  · exact ⟨14107, 13, prime_14107, prime_13, by norm_num⟩
  · exact ⟨14029, 53, prime_14029, prime_53, by norm_num⟩
  · exact ⟨14051, 43, prime_14051, prime_43, by norm_num⟩
  · exact ⟨14081, 29, prime_14081, prime_29, by norm_num⟩
  · exact ⟨14107, 17, prime_14107, prime_17, by norm_num⟩
  · exact ⟨14081, 31, prime_14081, prime_31, by norm_num⟩
  · exact ⟨14107, 19, prime_14107, prime_19, by norm_num⟩
  · exact ⟨14143, 2, prime_14143, prime_2, by norm_num⟩
  · exact ⟨14143, 3, prime_14143, prime_3, by norm_num⟩
  · exact ⟨14057, 47, prime_14057, prime_47, by norm_num⟩
  · exact ⟨14149, 2, prime_14149, prime_2, by norm_num⟩
  · exact ⟨14149, 3, prime_14149, prime_3, by norm_num⟩
  · exact ⟨14153, 2, prime_14153, prime_2, by norm_num⟩
  · exact ⟨14153, 3, prime_14153, prime_3, by norm_num⟩
  · exact ⟨14087, 37, prime_14087, prime_37, by norm_num⟩
  · exact ⟨14159, 2, prime_14159, prime_2, by norm_num⟩
  · exact ⟨14159, 3, prime_14159, prime_3, by norm_num⟩
  · exact ⟨14153, 7, prime_14153, prime_7, by norm_num⟩
  · exact ⟨14159, 5, prime_14159, prime_5, by norm_num⟩
  · exact ⟨14149, 11, prime_14149, prime_11, by norm_num⟩
  · exact ⟨14159, 7, prime_14159, prime_7, by norm_num⟩
  · exact ⟨14153, 11, prime_14153, prime_11, by norm_num⟩
  · exact ⟨14173, 2, prime_14173, prime_2, by norm_num⟩
  · exact ⟨14173, 3, prime_14173, prime_3, by norm_num⟩
  · exact ⟨14177, 2, prime_14177, prime_2, by norm_num⟩
  · exact ⟨14177, 3, prime_14177, prime_3, by norm_num⟩
  · exact ⟨14159, 13, prime_14159, prime_13, by norm_num⟩
  · exact ⟨14177, 5, prime_14177, prime_5, by norm_num⟩
  · exact ⟨14143, 23, prime_14143, prime_23, by norm_num⟩
  · exact ⟨14177, 7, prime_14177, prime_7, by norm_num⟩
  · exact ⟨14159, 17, prime_14159, prime_17, by norm_num⟩
  · exact ⟨14173, 11, prime_14173, prime_11, by norm_num⟩
  · exact ⟨14159, 19, prime_14159, prime_19, by norm_num⟩
  · exact ⟨14177, 11, prime_14177, prime_11, by norm_num⟩
  · exact ⟨14197, 2, prime_14197, prime_2, by norm_num⟩
  · exact ⟨14197, 3, prime_14197, prime_3, by norm_num⟩
  · exact ⟨14159, 23, prime_14159, prime_23, by norm_num⟩

private theorem lemoine_chunk_71 : ∀ k : ℕ, 7103 ≤ k → k ≤ 7202 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨14197, 5, prime_14197, prime_5, by norm_num⟩
  · exact ⟨14087, 61, prime_14087, prime_61, by norm_num⟩
  · exact ⟨14207, 2, prime_14207, prime_2, by norm_num⟩
  · exact ⟨14207, 3, prime_14207, prime_3, by norm_num⟩
  · exact ⟨14177, 19, prime_14177, prime_19, by norm_num⟩
  · exact ⟨14207, 5, prime_14207, prime_5, by norm_num⟩
  · exact ⟨14197, 11, prime_14197, prime_11, by norm_num⟩
  · exact ⟨14207, 7, prime_14207, prime_7, by norm_num⟩
  · exact ⟨14197, 13, prime_14197, prime_13, by norm_num⟩
  · exact ⟨14221, 2, prime_14221, prime_2, by norm_num⟩
  · exact ⟨14221, 3, prime_14221, prime_3, by norm_num⟩
  · exact ⟨14207, 11, prime_14207, prime_11, by norm_num⟩
  · exact ⟨14221, 5, prime_14221, prime_5, by norm_num⟩
  · exact ⟨14207, 13, prime_14207, prime_13, by norm_num⟩
  · exact ⟨14221, 7, prime_14221, prime_7, by norm_num⟩
  · exact ⟨14143, 47, prime_14143, prime_47, by norm_num⟩
  · exact ⟨14177, 31, prime_14177, prime_31, by norm_num⟩
  · exact ⟨14207, 17, prime_14207, prime_17, by norm_num⟩
  · exact ⟨14221, 11, prime_14221, prime_11, by norm_num⟩
  · exact ⟨14207, 19, prime_14207, prime_19, by norm_num⟩
  · exact ⟨14243, 2, prime_14243, prime_2, by norm_num⟩
  · exact ⟨14243, 3, prime_14243, prime_3, by norm_num⟩
  · exact ⟨14177, 37, prime_14177, prime_37, by norm_num⟩
  · exact ⟨14249, 2, prime_14249, prime_2, by norm_num⟩
  · exact ⟨14251, 2, prime_14251, prime_2, by norm_num⟩
  · exact ⟨14251, 3, prime_14251, prime_3, by norm_num⟩
  · exact ⟨14249, 5, prime_14249, prime_5, by norm_num⟩
  · exact ⟨14251, 5, prime_14251, prime_5, by norm_num⟩
  · exact ⟨14249, 7, prime_14249, prime_7, by norm_num⟩
  · exact ⟨14251, 7, prime_14251, prime_7, by norm_num⟩
  · exact ⟨14221, 23, prime_14221, prime_23, by norm_num⟩
  · exact ⟨14243, 13, prime_14243, prime_13, by norm_num⟩
  · exact ⟨14249, 11, prime_14249, prime_11, by norm_num⟩
  · exact ⟨14251, 11, prime_14251, prime_11, by norm_num⟩
  · exact ⟨14249, 13, prime_14249, prime_13, by norm_num⟩
  · exact ⟨14251, 13, prime_14251, prime_13, by norm_num⟩
  · exact ⟨14221, 29, prime_14221, prime_29, by norm_num⟩
  · exact ⟨14243, 19, prime_14243, prime_19, by norm_num⟩
  · exact ⟨14249, 17, prime_14249, prime_17, by norm_num⟩
  · exact ⟨14281, 2, prime_14281, prime_2, by norm_num⟩
  · exact ⟨14281, 3, prime_14281, prime_3, by norm_num⟩
  · exact ⟨14251, 19, prime_14251, prime_19, by norm_num⟩
  · exact ⟨14281, 5, prime_14281, prime_5, by norm_num⟩
  · exact ⟨14207, 43, prime_14207, prime_43, by norm_num⟩
  · exact ⟨14281, 7, prime_14281, prime_7, by norm_num⟩
  · exact ⟨14293, 2, prime_14293, prime_2, by norm_num⟩
  · exact ⟨14293, 3, prime_14293, prime_3, by norm_num⟩
  · exact ⟨14243, 29, prime_14243, prime_29, by norm_num⟩
  · exact ⟨14293, 5, prime_14293, prime_5, by norm_num⟩
  · exact ⟨14243, 31, prime_14243, prime_31, by norm_num⟩
  · exact ⟨14303, 2, prime_14303, prime_2, by norm_num⟩
  · exact ⟨14303, 3, prime_14303, prime_3, by norm_num⟩
  · exact ⟨14249, 31, prime_14249, prime_31, by norm_num⟩
  · exact ⟨14303, 5, prime_14303, prime_5, by norm_num⟩
  · exact ⟨14293, 11, prime_14293, prime_11, by norm_num⟩
  · exact ⟨14303, 7, prime_14303, prime_7, by norm_num⟩
  · exact ⟨14293, 13, prime_14293, prime_13, by norm_num⟩
  · exact ⟨14143, 89, prime_14143, prime_89, by norm_num⟩
  · exact ⟨14249, 37, prime_14249, prime_37, by norm_num⟩
  · exact ⟨14321, 2, prime_14321, prime_2, by norm_num⟩
  · exact ⟨14323, 2, prime_14323, prime_2, by norm_num⟩
  · exact ⟨14323, 3, prime_14323, prime_3, by norm_num⟩
  · exact ⟨14327, 2, prime_14327, prime_2, by norm_num⟩
  · exact ⟨14327, 3, prime_14327, prime_3, by norm_num⟩
  · exact ⟨14321, 7, prime_14321, prime_7, by norm_num⟩
  · exact ⟨14327, 5, prime_14327, prime_5, by norm_num⟩
  · exact ⟨14293, 23, prime_14293, prime_23, by norm_num⟩
  · exact ⟨14327, 7, prime_14327, prime_7, by norm_num⟩
  · exact ⟨14321, 11, prime_14321, prime_11, by norm_num⟩
  · exact ⟨14341, 2, prime_14341, prime_2, by norm_num⟩
  · exact ⟨14341, 3, prime_14341, prime_3, by norm_num⟩
  · exact ⟨14327, 11, prime_14327, prime_11, by norm_num⟩
  · exact ⟨14347, 2, prime_14347, prime_2, by norm_num⟩
  · exact ⟨14347, 3, prime_14347, prime_3, by norm_num⟩
  · exact ⟨14341, 7, prime_14341, prime_7, by norm_num⟩
  · exact ⟨14347, 5, prime_14347, prime_5, by norm_num⟩
  · exact ⟨14321, 19, prime_14321, prime_19, by norm_num⟩
  · exact ⟨14347, 7, prime_14347, prime_7, by norm_num⟩
  · exact ⟨14341, 11, prime_14341, prime_11, by norm_num⟩
  · exact ⟨14327, 19, prime_14327, prime_19, by norm_num⟩
  · exact ⟨14341, 13, prime_14341, prime_13, by norm_num⟩
  · exact ⟨14347, 11, prime_14347, prime_11, by norm_num⟩
  · exact ⟨14249, 61, prime_14249, prime_61, by norm_num⟩
  · exact ⟨14369, 2, prime_14369, prime_2, by norm_num⟩
  · exact ⟨14369, 3, prime_14369, prime_3, by norm_num⟩
  · exact ⟨14303, 37, prime_14303, prime_37, by norm_num⟩
  · exact ⟨14369, 5, prime_14369, prime_5, by norm_num⟩
  · exact ⟨14347, 17, prime_14347, prime_17, by norm_num⟩
  · exact ⟨14369, 7, prime_14369, prime_7, by norm_num⟩
  · exact ⟨14347, 19, prime_14347, prime_19, by norm_num⟩
  · exact ⟨14341, 23, prime_14341, prime_23, by norm_num⟩
  · exact ⟨14327, 31, prime_14327, prime_31, by norm_num⟩
  · exact ⟨14387, 2, prime_14387, prime_2, by norm_num⟩
  · exact ⟨14389, 2, prime_14389, prime_2, by norm_num⟩
  · exact ⟨14389, 3, prime_14389, prime_3, by norm_num⟩
  · exact ⟨14387, 5, prime_14387, prime_5, by norm_num⟩
  · exact ⟨14389, 5, prime_14389, prime_5, by norm_num⟩
  · exact ⟨14387, 7, prime_14387, prime_7, by norm_num⟩
  · exact ⟨14389, 7, prime_14389, prime_7, by norm_num⟩
  · exact ⟨14401, 2, prime_14401, prime_2, by norm_num⟩

private theorem lemoine_chunk_72 : ∀ k : ℕ, 7203 ≤ k → k ≤ 7302 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨14401, 3, prime_14401, prime_3, by norm_num⟩
  · exact ⟨14387, 11, prime_14387, prime_11, by norm_num⟩
  · exact ⟨14407, 2, prime_14407, prime_2, by norm_num⟩
  · exact ⟨14407, 3, prime_14407, prime_3, by norm_num⟩
  · exact ⟨14411, 2, prime_14411, prime_2, by norm_num⟩
  · exact ⟨14411, 3, prime_14411, prime_3, by norm_num⟩
  · exact ⟨14057, 181, prime_14057, prime_181, by norm_num⟩
  · exact ⟨14411, 5, prime_14411, prime_5, by norm_num⟩
  · exact ⟨14419, 2, prime_14419, prime_2, by norm_num⟩
  · exact ⟨14419, 3, prime_14419, prime_3, by norm_num⟩
  · exact ⟨14423, 2, prime_14423, prime_2, by norm_num⟩
  · exact ⟨14423, 3, prime_14423, prime_3, by norm_num⟩
  · exact ⟨14369, 31, prime_14369, prime_31, by norm_num⟩
  · exact ⟨14423, 5, prime_14423, prime_5, by norm_num⟩
  · exact ⟨14431, 2, prime_14431, prime_2, by norm_num⟩
  · exact ⟨14431, 3, prime_14431, prime_3, by norm_num⟩
  · exact ⟨14401, 19, prime_14401, prime_19, by norm_num⟩
  · exact ⟨14437, 2, prime_14437, prime_2, by norm_num⟩
  · exact ⟨14437, 3, prime_14437, prime_3, by norm_num⟩
  · exact ⟨14431, 7, prime_14431, prime_7, by norm_num⟩
  · exact ⟨14437, 5, prime_14437, prime_5, by norm_num⟩
  · exact ⟨14423, 13, prime_14423, prime_13, by norm_num⟩
  · exact ⟨14447, 2, prime_14447, prime_2, by norm_num⟩
  · exact ⟨14449, 2, prime_14449, prime_2, by norm_num⟩
  · exact ⟨14449, 3, prime_14449, prime_3, by norm_num⟩
  · exact ⟨14447, 5, prime_14447, prime_5, by norm_num⟩
  · exact ⟨14449, 5, prime_14449, prime_5, by norm_num⟩
  · exact ⟨14447, 7, prime_14447, prime_7, by norm_num⟩
  · exact ⟨14449, 7, prime_14449, prime_7, by norm_num⟩
  · exact ⟨14461, 2, prime_14461, prime_2, by norm_num⟩
  · exact ⟨14461, 3, prime_14461, prime_3, by norm_num⟩
  · exact ⟨14447, 11, prime_14447, prime_11, by norm_num⟩
  · exact ⟨14461, 5, prime_14461, prime_5, by norm_num⟩
  · exact ⟨14447, 13, prime_14447, prime_13, by norm_num⟩
  · exact ⟨14461, 7, prime_14461, prime_7, by norm_num⟩
  · exact ⟨14431, 23, prime_14431, prime_23, by norm_num⟩
  · exact ⟨14321, 79, prime_14321, prime_79, by norm_num⟩
  · exact ⟨14447, 17, prime_14447, prime_17, by norm_num⟩
  · exact ⟨14479, 2, prime_14479, prime_2, by norm_num⟩
  · exact ⟨14479, 3, prime_14479, prime_3, by norm_num⟩
  · exact ⟨14461, 13, prime_14461, prime_13, by norm_num⟩
  · exact ⟨14479, 5, prime_14479, prime_5, by norm_num⟩
  · exact ⟨14369, 61, prime_14369, prime_61, by norm_num⟩
  · exact ⟨14489, 2, prime_14489, prime_2, by norm_num⟩
  · exact ⟨14489, 3, prime_14489, prime_3, by norm_num⟩
  · exact ⟨14423, 37, prime_14423, prime_37, by norm_num⟩
  · exact ⟨14489, 5, prime_14489, prime_5, by norm_num⟩
  · exact ⟨14479, 11, prime_14479, prime_11, by norm_num⟩
  · exact ⟨14489, 7, prime_14489, prime_7, by norm_num⟩
  · exact ⟨14479, 13, prime_14479, prime_13, by norm_num⟩
  · exact ⟨14503, 2, prime_14503, prime_2, by norm_num⟩
  · exact ⟨14503, 3, prime_14503, prime_3, by norm_num⟩
  · exact ⟨14489, 11, prime_14489, prime_11, by norm_num⟩
  · exact ⟨14503, 5, prime_14503, prime_5, by norm_num⟩
  · exact ⟨14489, 13, prime_14489, prime_13, by norm_num⟩
  · exact ⟨14503, 7, prime_14503, prime_7, by norm_num⟩
  · exact ⟨14461, 29, prime_14461, prime_29, by norm_num⟩
  · exact ⟨14447, 37, prime_14447, prime_37, by norm_num⟩
  · exact ⟨14519, 2, prime_14519, prime_2, by norm_num⟩
  · exact ⟨14519, 3, prime_14519, prime_3, by norm_num⟩
  · exact ⟨14489, 19, prime_14489, prime_19, by norm_num⟩
  · exact ⟨14519, 5, prime_14519, prime_5, by norm_num⟩
  · exact ⟨14449, 41, prime_14449, prime_41, by norm_num⟩
  · exact ⟨14519, 7, prime_14519, prime_7, by norm_num⟩
  · exact ⟨14489, 23, prime_14489, prime_23, by norm_num⟩
  · exact ⟨14533, 2, prime_14533, prime_2, by norm_num⟩
  · exact ⟨14533, 3, prime_14533, prime_3, by norm_num⟩
  · exact ⟨14537, 2, prime_14537, prime_2, by norm_num⟩
  · exact ⟨14537, 3, prime_14537, prime_3, by norm_num⟩
  · exact ⟨14519, 13, prime_14519, prime_13, by norm_num⟩
  · exact ⟨14543, 2, prime_14543, prime_2, by norm_num⟩
  · exact ⟨14543, 3, prime_14543, prime_3, by norm_num⟩
  · exact ⟨14537, 7, prime_14537, prime_7, by norm_num⟩
  · exact ⟨14549, 2, prime_14549, prime_2, by norm_num⟩
  · exact ⟨14551, 2, prime_14551, prime_2, by norm_num⟩
  · exact ⟨14551, 3, prime_14551, prime_3, by norm_num⟩
  · exact ⟨14549, 5, prime_14549, prime_5, by norm_num⟩
  · exact ⟨14557, 2, prime_14557, prime_2, by norm_num⟩
  · exact ⟨14557, 3, prime_14557, prime_3, by norm_num⟩
  · exact ⟨14561, 2, prime_14561, prime_2, by norm_num⟩
  · exact ⟨14563, 2, prime_14563, prime_2, by norm_num⟩
  · exact ⟨14563, 3, prime_14563, prime_3, by norm_num⟩
  · exact ⟨14561, 5, prime_14561, prime_5, by norm_num⟩
  · exact ⟨14563, 5, prime_14563, prime_5, by norm_num⟩
  · exact ⟨14561, 7, prime_14561, prime_7, by norm_num⟩
  · exact ⟨14563, 7, prime_14563, prime_7, by norm_num⟩
  · exact ⟨14557, 11, prime_14557, prime_11, by norm_num⟩
  · exact ⟨14543, 19, prime_14543, prime_19, by norm_num⟩
  · exact ⟨14561, 11, prime_14561, prime_11, by norm_num⟩
  · exact ⟨14563, 11, prime_14563, prime_11, by norm_num⟩
  · exact ⟨14561, 13, prime_14561, prime_13, by norm_num⟩
  · exact ⟨14563, 13, prime_14563, prime_13, by norm_num⟩
  · exact ⟨14557, 17, prime_14557, prime_17, by norm_num⟩
  · exact ⟨14519, 37, prime_14519, prime_37, by norm_num⟩
  · exact ⟨14591, 2, prime_14591, prime_2, by norm_num⟩
  · exact ⟨14593, 2, prime_14593, prime_2, by norm_num⟩
  · exact ⟨14593, 3, prime_14593, prime_3, by norm_num⟩
  · exact ⟨14591, 5, prime_14591, prime_5, by norm_num⟩
  · exact ⟨14593, 5, prime_14593, prime_5, by norm_num⟩
  · exact ⟨14591, 7, prime_14591, prime_7, by norm_num⟩

private theorem lemoine_chunk_73 : ∀ k : ℕ, 7303 ≤ k → k ≤ 7402 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨14593, 7, prime_14593, prime_7, by norm_num⟩
  · exact ⟨14563, 23, prime_14563, prime_23, by norm_num⟩
  · exact ⟨14549, 31, prime_14549, prime_31, by norm_num⟩
  · exact ⟨14591, 11, prime_14591, prime_11, by norm_num⟩
  · exact ⟨14593, 11, prime_14593, prime_11, by norm_num⟩
  · exact ⟨14591, 13, prime_14591, prime_13, by norm_num⟩
  · exact ⟨14593, 13, prime_14593, prime_13, by norm_num⟩
  · exact ⟨14563, 29, prime_14563, prime_29, by norm_num⟩
  · exact ⟨14561, 31, prime_14561, prime_31, by norm_num⟩
  · exact ⟨14621, 2, prime_14621, prime_2, by norm_num⟩
  · exact ⟨14621, 3, prime_14621, prime_3, by norm_num⟩
  · exact ⟨14591, 19, prime_14591, prime_19, by norm_num⟩
  · exact ⟨14627, 2, prime_14627, prime_2, by norm_num⟩
  · exact ⟨14629, 2, prime_14629, prime_2, by norm_num⟩
  · exact ⟨14629, 3, prime_14629, prime_3, by norm_num⟩
  · exact ⟨14633, 2, prime_14633, prime_2, by norm_num⟩
  · exact ⟨14633, 3, prime_14633, prime_3, by norm_num⟩
  · exact ⟨14627, 7, prime_14627, prime_7, by norm_num⟩
  · exact ⟨14639, 2, prime_14639, prime_2, by norm_num⟩
  · exact ⟨14639, 3, prime_14639, prime_3, by norm_num⟩
  · exact ⟨14633, 7, prime_14633, prime_7, by norm_num⟩
  · exact ⟨14639, 5, prime_14639, prime_5, by norm_num⟩
  · exact ⟨14629, 11, prime_14629, prime_11, by norm_num⟩
  · exact ⟨14639, 7, prime_14639, prime_7, by norm_num⟩
  · exact ⟨14633, 11, prime_14633, prime_11, by norm_num⟩
  · exact ⟨14653, 2, prime_14653, prime_2, by norm_num⟩
  · exact ⟨14653, 3, prime_14653, prime_3, by norm_num⟩
  · exact ⟨14657, 2, prime_14657, prime_2, by norm_num⟩
  · exact ⟨14657, 3, prime_14657, prime_3, by norm_num⟩
  · exact ⟨14639, 13, prime_14639, prime_13, by norm_num⟩
  · exact ⟨14657, 5, prime_14657, prime_5, by norm_num⟩
  · exact ⟨14563, 53, prime_14563, prime_53, by norm_num⟩
  · exact ⟨14657, 7, prime_14657, prime_7, by norm_num⟩
  · exact ⟨14669, 2, prime_14669, prime_2, by norm_num⟩
  · exact ⟨14669, 3, prime_14669, prime_3, by norm_num⟩
  · exact ⟨14639, 19, prime_14639, prime_19, by norm_num⟩
  · exact ⟨14669, 5, prime_14669, prime_5, by norm_num⟩
  · exact ⟨14563, 59, prime_14563, prime_59, by norm_num⟩
  · exact ⟨14669, 7, prime_14669, prime_7, by norm_num⟩
  · exact ⟨14639, 23, prime_14639, prime_23, by norm_num⟩
  · exact ⟨14683, 2, prime_14683, prime_2, by norm_num⟩
  · exact ⟨14683, 3, prime_14683, prime_3, by norm_num⟩
  · exact ⟨14669, 11, prime_14669, prime_11, by norm_num⟩
  · exact ⟨14683, 5, prime_14683, prime_5, by norm_num⟩
  · exact ⟨14669, 13, prime_14669, prime_13, by norm_num⟩
  · exact ⟨14683, 7, prime_14683, prime_7, by norm_num⟩
  · exact ⟨14653, 23, prime_14653, prime_23, by norm_num⟩
  · exact ⟨14639, 31, prime_14639, prime_31, by norm_num⟩
  · exact ⟨14699, 2, prime_14699, prime_2, by norm_num⟩
  · exact ⟨14699, 3, prime_14699, prime_3, by norm_num⟩
  · exact ⟨14669, 19, prime_14669, prime_19, by norm_num⟩
  · exact ⟨14699, 5, prime_14699, prime_5, by norm_num⟩
  · exact ⟨14653, 29, prime_14653, prime_29, by norm_num⟩
  · exact ⟨14699, 7, prime_14699, prime_7, by norm_num⟩
  · exact ⟨14669, 23, prime_14669, prime_23, by norm_num⟩
  · exact ⟨14713, 2, prime_14713, prime_2, by norm_num⟩
  · exact ⟨14713, 3, prime_14713, prime_3, by norm_num⟩
  · exact ⟨14717, 2, prime_14717, prime_2, by norm_num⟩
  · exact ⟨14717, 3, prime_14717, prime_3, by norm_num⟩
  · exact ⟨14699, 13, prime_14699, prime_13, by norm_num⟩
  · exact ⟨14723, 2, prime_14723, prime_2, by norm_num⟩
  · exact ⟨14723, 3, prime_14723, prime_3, by norm_num⟩
  · exact ⟨14717, 7, prime_14717, prime_7, by norm_num⟩
  · exact ⟨14723, 5, prime_14723, prime_5, by norm_num⟩
  · exact ⟨14731, 2, prime_14731, prime_2, by norm_num⟩
  · exact ⟨14731, 3, prime_14731, prime_3, by norm_num⟩
  · exact ⟨14717, 11, prime_14717, prime_11, by norm_num⟩
  · exact ⟨14737, 2, prime_14737, prime_2, by norm_num⟩
  · exact ⟨14737, 3, prime_14737, prime_3, by norm_num⟩
  · exact ⟨14741, 2, prime_14741, prime_2, by norm_num⟩
  · exact ⟨14741, 3, prime_14741, prime_3, by norm_num⟩
  · exact ⟨14723, 13, prime_14723, prime_13, by norm_num⟩
  · exact ⟨14747, 2, prime_14747, prime_2, by norm_num⟩
  · exact ⟨14747, 3, prime_14747, prime_3, by norm_num⟩
  · exact ⟨14741, 7, prime_14741, prime_7, by norm_num⟩
  · exact ⟨14753, 2, prime_14753, prime_2, by norm_num⟩
  · exact ⟨14753, 3, prime_14753, prime_3, by norm_num⟩
  · exact ⟨14747, 7, prime_14747, prime_7, by norm_num⟩
  · exact ⟨14759, 2, prime_14759, prime_2, by norm_num⟩
  · exact ⟨14759, 3, prime_14759, prime_3, by norm_num⟩
  · exact ⟨14753, 7, prime_14753, prime_7, by norm_num⟩
  · exact ⟨14759, 5, prime_14759, prime_5, by norm_num⟩
  · exact ⟨14767, 2, prime_14767, prime_2, by norm_num⟩
  · exact ⟨14767, 3, prime_14767, prime_3, by norm_num⟩
  · exact ⟨14771, 2, prime_14771, prime_2, by norm_num⟩
  · exact ⟨14771, 3, prime_14771, prime_3, by norm_num⟩
  · exact ⟨14753, 13, prime_14753, prime_13, by norm_num⟩
  · exact ⟨14771, 5, prime_14771, prime_5, by norm_num⟩
  · exact ⟨14779, 2, prime_14779, prime_2, by norm_num⟩
  · exact ⟨14779, 3, prime_14779, prime_3, by norm_num⟩
  · exact ⟨14783, 2, prime_14783, prime_2, by norm_num⟩
  · exact ⟨14783, 3, prime_14783, prime_3, by norm_num⟩
  · exact ⟨14753, 19, prime_14753, prime_19, by norm_num⟩
  · exact ⟨14783, 5, prime_14783, prime_5, by norm_num⟩
  · exact ⟨14737, 29, prime_14737, prime_29, by norm_num⟩
  · exact ⟨14783, 7, prime_14783, prime_7, by norm_num⟩
  · exact ⟨14753, 23, prime_14753, prime_23, by norm_num⟩
  · exact ⟨14797, 2, prime_14797, prime_2, by norm_num⟩
  · exact ⟨14797, 3, prime_14797, prime_3, by norm_num⟩
  · exact ⟨14783, 11, prime_14783, prime_11, by norm_num⟩

private theorem lemoine_chunk_74 : ∀ k : ℕ, 7403 ≤ k → k ≤ 7502 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨14797, 5, prime_14797, prime_5, by norm_num⟩
  · exact ⟨14783, 13, prime_14783, prime_13, by norm_num⟩
  · exact ⟨14797, 7, prime_14797, prime_7, by norm_num⟩
  · exact ⟨14779, 17, prime_14779, prime_17, by norm_num⟩
  · exact ⟨14753, 31, prime_14753, prime_31, by norm_num⟩
  · exact ⟨14813, 2, prime_14813, prime_2, by norm_num⟩
  · exact ⟨14813, 3, prime_14813, prime_3, by norm_num⟩
  · exact ⟨14783, 19, prime_14783, prime_19, by norm_num⟩
  · exact ⟨14813, 5, prime_14813, prime_5, by norm_num⟩
  · exact ⟨14821, 2, prime_14821, prime_2, by norm_num⟩
  · exact ⟨14821, 3, prime_14821, prime_3, by norm_num⟩
  · exact ⟨14783, 23, prime_14783, prime_23, by norm_num⟩
  · exact ⟨14827, 2, prime_14827, prime_2, by norm_num⟩
  · exact ⟨14827, 3, prime_14827, prime_3, by norm_num⟩
  · exact ⟨14831, 2, prime_14831, prime_2, by norm_num⟩
  · exact ⟨14831, 3, prime_14831, prime_3, by norm_num⟩
  · exact ⟨14813, 13, prime_14813, prime_13, by norm_num⟩
  · exact ⟨14831, 5, prime_14831, prime_5, by norm_num⟩
  · exact ⟨14821, 11, prime_14821, prime_11, by norm_num⟩
  · exact ⟨14831, 7, prime_14831, prime_7, by norm_num⟩
  · exact ⟨14843, 2, prime_14843, prime_2, by norm_num⟩
  · exact ⟨14843, 3, prime_14843, prime_3, by norm_num⟩
  · exact ⟨14813, 19, prime_14813, prime_19, by norm_num⟩
  · exact ⟨14843, 5, prime_14843, prime_5, by norm_num⟩
  · exact ⟨14851, 2, prime_14851, prime_2, by norm_num⟩
  · exact ⟨14851, 3, prime_14851, prime_3, by norm_num⟩
  · exact ⟨14821, 19, prime_14821, prime_19, by norm_num⟩
  · exact ⟨14851, 5, prime_14851, prime_5, by norm_num⟩
  · exact ⟨14741, 61, prime_14741, prime_61, by norm_num⟩
  · exact ⟨14851, 7, prime_14851, prime_7, by norm_num⟩
  · exact ⟨14821, 23, prime_14821, prime_23, by norm_num⟩
  · exact ⟨14843, 13, prime_14843, prime_13, by norm_num⟩
  · exact ⟨14867, 2, prime_14867, prime_2, by norm_num⟩
  · exact ⟨14869, 2, prime_14869, prime_2, by norm_num⟩
  · exact ⟨14869, 3, prime_14869, prime_3, by norm_num⟩
  · exact ⟨14867, 5, prime_14867, prime_5, by norm_num⟩
  · exact ⟨14869, 5, prime_14869, prime_5, by norm_num⟩
  · exact ⟨14867, 7, prime_14867, prime_7, by norm_num⟩
  · exact ⟨14879, 2, prime_14879, prime_2, by norm_num⟩
  · exact ⟨14879, 3, prime_14879, prime_3, by norm_num⟩
  · exact ⟨14813, 37, prime_14813, prime_37, by norm_num⟩
  · exact ⟨14879, 5, prime_14879, prime_5, by norm_num⟩
  · exact ⟨14887, 2, prime_14887, prime_2, by norm_num⟩
  · exact ⟨14887, 3, prime_14887, prime_3, by norm_num⟩
  · exact ⟨14891, 2, prime_14891, prime_2, by norm_num⟩
  · exact ⟨14891, 3, prime_14891, prime_3, by norm_num⟩
  · exact ⟨14813, 43, prime_14813, prime_43, by norm_num⟩
  · exact ⟨14897, 2, prime_14897, prime_2, by norm_num⟩
  · exact ⟨14897, 3, prime_14897, prime_3, by norm_num⟩
  · exact ⟨14891, 7, prime_14891, prime_7, by norm_num⟩
  · exact ⟨14897, 5, prime_14897, prime_5, by norm_num⟩
  · exact ⟨14887, 11, prime_14887, prime_11, by norm_num⟩
  · exact ⟨14897, 7, prime_14897, prime_7, by norm_num⟩
  · exact ⟨14891, 11, prime_14891, prime_11, by norm_num⟩
  · exact ⟨14869, 23, prime_14869, prime_23, by norm_num⟩
  · exact ⟨14891, 13, prime_14891, prime_13, by norm_num⟩
  · exact ⟨14897, 11, prime_14897, prime_11, by norm_num⟩
  · exact ⟨14887, 17, prime_14887, prime_17, by norm_num⟩
  · exact ⟨14897, 13, prime_14897, prime_13, by norm_num⟩
  · exact ⟨14891, 17, prime_14891, prime_17, by norm_num⟩
  · exact ⟨14923, 2, prime_14923, prime_2, by norm_num⟩
  · exact ⟨14923, 3, prime_14923, prime_3, by norm_num⟩
  · exact ⟨14897, 17, prime_14897, prime_17, by norm_num⟩
  · exact ⟨14929, 2, prime_14929, prime_2, by norm_num⟩
  · exact ⟨14929, 3, prime_14929, prime_3, by norm_num⟩
  · exact ⟨14923, 7, prime_14923, prime_7, by norm_num⟩
  · exact ⟨14929, 5, prime_14929, prime_5, by norm_num⟩
  · exact ⟨14879, 31, prime_14879, prime_31, by norm_num⟩
  · exact ⟨14939, 2, prime_14939, prime_2, by norm_num⟩
  · exact ⟨14939, 3, prime_14939, prime_3, by norm_num⟩
  · exact ⟨14813, 67, prime_14813, prime_67, by norm_num⟩
  · exact ⟨14939, 5, prime_14939, prime_5, by norm_num⟩
  · exact ⟨14947, 2, prime_14947, prime_2, by norm_num⟩
  · exact ⟨14947, 3, prime_14947, prime_3, by norm_num⟩
  · exact ⟨14951, 2, prime_14951, prime_2, by norm_num⟩
  · exact ⟨14951, 3, prime_14951, prime_3, by norm_num⟩
  · exact ⟨14897, 31, prime_14897, prime_31, by norm_num⟩
  · exact ⟨14957, 2, prime_14957, prime_2, by norm_num⟩
  · exact ⟨14957, 3, prime_14957, prime_3, by norm_num⟩
  · exact ⟨14951, 7, prime_14951, prime_7, by norm_num⟩
  · exact ⟨14957, 5, prime_14957, prime_5, by norm_num⟩
  · exact ⟨14947, 11, prime_14947, prime_11, by norm_num⟩
  · exact ⟨14957, 7, prime_14957, prime_7, by norm_num⟩
  · exact ⟨14969, 2, prime_14969, prime_2, by norm_num⟩
  · exact ⟨14969, 3, prime_14969, prime_3, by norm_num⟩
  · exact ⟨14951, 13, prime_14951, prime_13, by norm_num⟩
  · exact ⟨14969, 5, prime_14969, prime_5, by norm_num⟩
  · exact ⟨14947, 17, prime_14947, prime_17, by norm_num⟩
  · exact ⟨14969, 7, prime_14969, prime_7, by norm_num⟩
  · exact ⟨14951, 17, prime_14951, prime_17, by norm_num⟩
  · exact ⟨14983, 2, prime_14983, prime_2, by norm_num⟩
  · exact ⟨14983, 3, prime_14983, prime_3, by norm_num⟩
  · exact ⟨14969, 11, prime_14969, prime_11, by norm_num⟩
  · exact ⟨14983, 5, prime_14983, prime_5, by norm_num⟩
  · exact ⟨14969, 13, prime_14969, prime_13, by norm_num⟩
  · exact ⟨14983, 7, prime_14983, prime_7, by norm_num⟩
  · exact ⟨14821, 89, prime_14821, prime_89, by norm_num⟩
  · exact ⟨14939, 31, prime_14939, prime_31, by norm_num⟩
  · exact ⟨14969, 17, prime_14969, prime_17, by norm_num⟩
  · exact ⟨14983, 11, prime_14983, prime_11, by norm_num⟩

private theorem lemoine_chunk_75 : ∀ k : ℕ, 7503 ≤ k → k ≤ 7602 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨14969, 19, prime_14969, prime_19, by norm_num⟩
  · exact ⟨14983, 13, prime_14983, prime_13, by norm_num⟩
  · exact ⟨14929, 41, prime_14929, prime_41, by norm_num⟩
  · exact ⟨14951, 31, prime_14951, prime_31, by norm_num⟩
  · exact ⟨14969, 23, prime_14969, prime_23, by norm_num⟩
  · exact ⟨15013, 2, prime_15013, prime_2, by norm_num⟩
  · exact ⟨15013, 3, prime_15013, prime_3, by norm_num⟩
  · exact ⟨15017, 2, prime_15017, prime_2, by norm_num⟩
  · exact ⟨15017, 3, prime_15017, prime_3, by norm_num⟩
  · exact ⟨14951, 37, prime_14951, prime_37, by norm_num⟩
  · exact ⟨15017, 5, prime_15017, prime_5, by norm_num⟩
  · exact ⟨14983, 23, prime_14983, prime_23, by norm_num⟩
  · exact ⟨15017, 7, prime_15017, prime_7, by norm_num⟩
  · exact ⟨14951, 41, prime_14951, prime_41, by norm_num⟩
  · exact ⟨15031, 2, prime_15031, prime_2, by norm_num⟩
  · exact ⟨15031, 3, prime_15031, prime_3, by norm_num⟩
  · exact ⟨15017, 11, prime_15017, prime_11, by norm_num⟩
  · exact ⟨15031, 5, prime_15031, prime_5, by norm_num⟩
  · exact ⟨15017, 13, prime_15017, prime_13, by norm_num⟩
  · exact ⟨15031, 7, prime_15031, prime_7, by norm_num⟩
  · exact ⟨15013, 17, prime_15013, prime_17, by norm_num⟩
  · exact ⟨14891, 79, prime_14891, prime_79, by norm_num⟩
  · exact ⟨15017, 17, prime_15017, prime_17, by norm_num⟩
  · exact ⟨15031, 11, prime_15031, prime_11, by norm_num⟩
  · exact ⟨15017, 19, prime_15017, prime_19, by norm_num⟩
  · exact ⟨15053, 2, prime_15053, prime_2, by norm_num⟩
  · exact ⟨15053, 3, prime_15053, prime_3, by norm_num⟩
  · exact ⟨14939, 61, prime_14939, prime_61, by norm_num⟩
  · exact ⟨15053, 5, prime_15053, prime_5, by norm_num⟩
  · exact ⟨15061, 2, prime_15061, prime_2, by norm_num⟩
  · exact ⟨15061, 3, prime_15061, prime_3, by norm_num⟩
  · exact ⟨15031, 19, prime_15031, prime_19, by norm_num⟩
  · exact ⟨15061, 5, prime_15061, prime_5, by norm_num⟩
  · exact ⟨14951, 61, prime_14951, prime_61, by norm_num⟩
  · exact ⟨15061, 7, prime_15061, prime_7, by norm_num⟩
  · exact ⟨15073, 2, prime_15073, prime_2, by norm_num⟩
  · exact ⟨15073, 3, prime_15073, prime_3, by norm_num⟩
  · exact ⟨15077, 2, prime_15077, prime_2, by norm_num⟩
  · exact ⟨15077, 3, prime_15077, prime_3, by norm_num⟩
  · exact ⟨14951, 67, prime_14951, prime_67, by norm_num⟩
  · exact ⟨15083, 2, prime_15083, prime_2, by norm_num⟩
  · exact ⟨15083, 3, prime_15083, prime_3, by norm_num⟩
  · exact ⟨15077, 7, prime_15077, prime_7, by norm_num⟩
  · exact ⟨15083, 5, prime_15083, prime_5, by norm_num⟩
  · exact ⟨15091, 2, prime_15091, prime_2, by norm_num⟩
  · exact ⟨15091, 3, prime_15091, prime_3, by norm_num⟩
  · exact ⟨15077, 11, prime_15077, prime_11, by norm_num⟩
  · exact ⟨15091, 5, prime_15091, prime_5, by norm_num⟩
  · exact ⟨15077, 13, prime_15077, prime_13, by norm_num⟩
  · exact ⟨15101, 2, prime_15101, prime_2, by norm_num⟩
  · exact ⟨15101, 3, prime_15101, prime_3, by norm_num⟩
  · exact ⟨15083, 13, prime_15083, prime_13, by norm_num⟩
  · exact ⟨15107, 2, prime_15107, prime_2, by norm_num⟩
  · exact ⟨15107, 3, prime_15107, prime_3, by norm_num⟩
  · exact ⟨15101, 7, prime_15101, prime_7, by norm_num⟩
  · exact ⟨15107, 5, prime_15107, prime_5, by norm_num⟩
  · exact ⟨15073, 23, prime_15073, prime_23, by norm_num⟩
  · exact ⟨15107, 7, prime_15107, prime_7, by norm_num⟩
  · exact ⟨15101, 11, prime_15101, prime_11, by norm_num⟩
  · exact ⟨15121, 2, prime_15121, prime_2, by norm_num⟩
  · exact ⟨15121, 3, prime_15121, prime_3, by norm_num⟩
  · exact ⟨15107, 11, prime_15107, prime_11, by norm_num⟩
  · exact ⟨15121, 5, prime_15121, prime_5, by norm_num⟩
  · exact ⟨15107, 13, prime_15107, prime_13, by norm_num⟩
  · exact ⟨15131, 2, prime_15131, prime_2, by norm_num⟩
  · exact ⟨15131, 3, prime_15131, prime_3, by norm_num⟩
  · exact ⟨15101, 19, prime_15101, prime_19, by norm_num⟩
  · exact ⟨15137, 2, prime_15137, prime_2, by norm_num⟩
  · exact ⟨15139, 2, prime_15139, prime_2, by norm_num⟩
  · exact ⟨15139, 3, prime_15139, prime_3, by norm_num⟩
  · exact ⟨15137, 5, prime_15137, prime_5, by norm_num⟩
  · exact ⟨15139, 5, prime_15139, prime_5, by norm_num⟩
  · exact ⟨15137, 7, prime_15137, prime_7, by norm_num⟩
  · exact ⟨15149, 2, prime_15149, prime_2, by norm_num⟩
  · exact ⟨15149, 3, prime_15149, prime_3, by norm_num⟩
  · exact ⟨15131, 13, prime_15131, prime_13, by norm_num⟩
  · exact ⟨15149, 5, prime_15149, prime_5, by norm_num⟩
  · exact ⟨15139, 11, prime_15139, prime_11, by norm_num⟩
  · exact ⟨15149, 7, prime_15149, prime_7, by norm_num⟩
  · exact ⟨15161, 2, prime_15161, prime_2, by norm_num⟩
  · exact ⟨15161, 3, prime_15161, prime_3, by norm_num⟩
  · exact ⟨15131, 19, prime_15131, prime_19, by norm_num⟩
  · exact ⟨15161, 5, prime_15161, prime_5, by norm_num⟩
  · exact ⟨15139, 17, prime_15139, prime_17, by norm_num⟩
  · exact ⟨15161, 7, prime_15161, prime_7, by norm_num⟩
  · exact ⟨15173, 2, prime_15173, prime_2, by norm_num⟩
  · exact ⟨15173, 3, prime_15173, prime_3, by norm_num⟩
  · exact ⟨15107, 37, prime_15107, prime_37, by norm_num⟩
  · exact ⟨15173, 5, prime_15173, prime_5, by norm_num⟩
  · exact ⟨15139, 23, prime_15139, prime_23, by norm_num⟩
  · exact ⟨15173, 7, prime_15173, prime_7, by norm_num⟩
  · exact ⟨15131, 29, prime_15131, prime_29, by norm_num⟩
  · exact ⟨15187, 2, prime_15187, prime_2, by norm_num⟩
  · exact ⟨15187, 3, prime_15187, prime_3, by norm_num⟩
  · exact ⟨15173, 11, prime_15173, prime_11, by norm_num⟩
  · exact ⟨15193, 2, prime_15193, prime_2, by norm_num⟩
  · exact ⟨15193, 3, prime_15193, prime_3, by norm_num⟩
  · exact ⟨15187, 7, prime_15187, prime_7, by norm_num⟩
  · exact ⟨15199, 2, prime_15199, prime_2, by norm_num⟩
  · exact ⟨15199, 3, prime_15199, prime_3, by norm_num⟩

private theorem lemoine_chunk_76 : ∀ k : ℕ, 7603 ≤ k → k ≤ 7702 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨15193, 7, prime_15193, prime_7, by norm_num⟩
  · exact ⟨15199, 5, prime_15199, prime_5, by norm_num⟩
  · exact ⟨15173, 19, prime_15173, prime_19, by norm_num⟩
  · exact ⟨15199, 7, prime_15199, prime_7, by norm_num⟩
  · exact ⟨15193, 11, prime_15193, prime_11, by norm_num⟩
  · exact ⟨15131, 43, prime_15131, prime_43, by norm_num⟩
  · exact ⟨15193, 13, prime_15193, prime_13, by norm_num⟩
  · exact ⟨15217, 2, prime_15217, prime_2, by norm_num⟩
  · exact ⟨15217, 3, prime_15217, prime_3, by norm_num⟩
  · exact ⟨15199, 13, prime_15199, prime_13, by norm_num⟩
  · exact ⟨15217, 5, prime_15217, prime_5, by norm_num⟩
  · exact ⟨15107, 61, prime_15107, prime_61, by norm_num⟩
  · exact ⟨15227, 2, prime_15227, prime_2, by norm_num⟩
  · exact ⟨15227, 3, prime_15227, prime_3, by norm_num⟩
  · exact ⟨15173, 31, prime_15173, prime_31, by norm_num⟩
  · exact ⟨15233, 2, prime_15233, prime_2, by norm_num⟩
  · exact ⟨15233, 3, prime_15233, prime_3, by norm_num⟩
  · exact ⟨15227, 7, prime_15227, prime_7, by norm_num⟩
  · exact ⟨15233, 5, prime_15233, prime_5, by norm_num⟩
  · exact ⟨15241, 2, prime_15241, prime_2, by norm_num⟩
  · exact ⟨15241, 3, prime_15241, prime_3, by norm_num⟩
  · exact ⟨15227, 11, prime_15227, prime_11, by norm_num⟩
  · exact ⟨15241, 5, prime_15241, prime_5, by norm_num⟩
  · exact ⟨15227, 13, prime_15227, prime_13, by norm_num⟩
  · exact ⟨15241, 7, prime_15241, prime_7, by norm_num⟩
  · exact ⟨15199, 29, prime_15199, prime_29, by norm_num⟩
  · exact ⟨15233, 13, prime_15233, prime_13, by norm_num⟩
  · exact ⟨15227, 17, prime_15227, prime_17, by norm_num⟩
  · exact ⟨15259, 2, prime_15259, prime_2, by norm_num⟩
  · exact ⟨15259, 3, prime_15259, prime_3, by norm_num⟩
  · exact ⟨15263, 2, prime_15263, prime_2, by norm_num⟩
  · exact ⟨15263, 3, prime_15263, prime_3, by norm_num⟩
  · exact ⟨15233, 19, prime_15233, prime_19, by norm_num⟩
  · exact ⟨15269, 2, prime_15269, prime_2, by norm_num⟩
  · exact ⟨15271, 2, prime_15271, prime_2, by norm_num⟩
  · exact ⟨15271, 3, prime_15271, prime_3, by norm_num⟩
  · exact ⟨15269, 5, prime_15269, prime_5, by norm_num⟩
  · exact ⟨15277, 2, prime_15277, prime_2, by norm_num⟩
  · exact ⟨15277, 3, prime_15277, prime_3, by norm_num⟩
  · exact ⟨15271, 7, prime_15271, prime_7, by norm_num⟩
  · exact ⟨15277, 5, prime_15277, prime_5, by norm_num⟩
  · exact ⟨15263, 13, prime_15263, prime_13, by norm_num⟩
  · exact ⟨15287, 2, prime_15287, prime_2, by norm_num⟩
  · exact ⟨15289, 2, prime_15289, prime_2, by norm_num⟩
  · exact ⟨15289, 3, prime_15289, prime_3, by norm_num⟩
  · exact ⟨15287, 5, prime_15287, prime_5, by norm_num⟩
  · exact ⟨15289, 5, prime_15289, prime_5, by norm_num⟩
  · exact ⟨15287, 7, prime_15287, prime_7, by norm_num⟩
  · exact ⟨15299, 2, prime_15299, prime_2, by norm_num⟩
  · exact ⟨15299, 3, prime_15299, prime_3, by norm_num⟩
  · exact ⟨15269, 19, prime_15269, prime_19, by norm_num⟩
  · exact ⟨15299, 5, prime_15299, prime_5, by norm_num⟩
  · exact ⟨15307, 2, prime_15307, prime_2, by norm_num⟩
  · exact ⟨15307, 3, prime_15307, prime_3, by norm_num⟩
  · exact ⟨15289, 13, prime_15289, prime_13, by norm_num⟩
  · exact ⟨15313, 2, prime_15313, prime_2, by norm_num⟩
  · exact ⟨15313, 3, prime_15313, prime_3, by norm_num⟩
  · exact ⟨15307, 7, prime_15307, prime_7, by norm_num⟩
  · exact ⟨15319, 2, prime_15319, prime_2, by norm_num⟩
  · exact ⟨15319, 3, prime_15319, prime_3, by norm_num⟩
  · exact ⟨15313, 7, prime_15313, prime_7, by norm_num⟩
  · exact ⟨15319, 5, prime_15319, prime_5, by norm_num⟩
  · exact ⟨15269, 31, prime_15269, prime_31, by norm_num⟩
  · exact ⟨15329, 2, prime_15329, prime_2, by norm_num⟩
  · exact ⟨15331, 2, prime_15331, prime_2, by norm_num⟩
  · exact ⟨15331, 3, prime_15331, prime_3, by norm_num⟩
  · exact ⟨15329, 5, prime_15329, prime_5, by norm_num⟩
  · exact ⟨15331, 5, prime_15331, prime_5, by norm_num⟩
  · exact ⟨15329, 7, prime_15329, prime_7, by norm_num⟩
  · exact ⟨15331, 7, prime_15331, prime_7, by norm_num⟩
  · exact ⟨15313, 17, prime_15313, prime_17, by norm_num⟩
  · exact ⟨15287, 31, prime_15287, prime_31, by norm_num⟩
  · exact ⟨15329, 11, prime_15329, prime_11, by norm_num⟩
  · exact ⟨15349, 2, prime_15349, prime_2, by norm_num⟩
  · exact ⟨15349, 3, prime_15349, prime_3, by norm_num⟩
  · exact ⟨15331, 13, prime_15331, prime_13, by norm_num⟩
  · exact ⟨15349, 5, prime_15349, prime_5, by norm_num⟩
  · exact ⟨15299, 31, prime_15299, prime_31, by norm_num⟩
  · exact ⟨15359, 2, prime_15359, prime_2, by norm_num⟩
  · exact ⟨15361, 2, prime_15361, prime_2, by norm_num⟩
  · exact ⟨15361, 3, prime_15361, prime_3, by norm_num⟩
  · exact ⟨15359, 5, prime_15359, prime_5, by norm_num⟩
  · exact ⟨15361, 5, prime_15361, prime_5, by norm_num⟩
  · exact ⟨15359, 7, prime_15359, prime_7, by norm_num⟩
  · exact ⟨15361, 7, prime_15361, prime_7, by norm_num⟩
  · exact ⟨15373, 2, prime_15373, prime_2, by norm_num⟩
  · exact ⟨15373, 3, prime_15373, prime_3, by norm_num⟩
  · exact ⟨15377, 2, prime_15377, prime_2, by norm_num⟩
  · exact ⟨15377, 3, prime_15377, prime_3, by norm_num⟩
  · exact ⟨15359, 13, prime_15359, prime_13, by norm_num⟩
  · exact ⟨15383, 2, prime_15383, prime_2, by norm_num⟩
  · exact ⟨15383, 3, prime_15383, prime_3, by norm_num⟩
  · exact ⟨15377, 7, prime_15377, prime_7, by norm_num⟩
  · exact ⟨15383, 5, prime_15383, prime_5, by norm_num⟩
  · exact ⟨15391, 2, prime_15391, prime_2, by norm_num⟩
  · exact ⟨15391, 3, prime_15391, prime_3, by norm_num⟩
  · exact ⟨15377, 11, prime_15377, prime_11, by norm_num⟩
  · exact ⟨15391, 5, prime_15391, prime_5, by norm_num⟩
  · exact ⟨15377, 13, prime_15377, prime_13, by norm_num⟩
  · exact ⟨15401, 2, prime_15401, prime_2, by norm_num⟩

private theorem lemoine_chunk_77 : ∀ k : ℕ, 7703 ≤ k → k ≤ 7802 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨15401, 3, prime_15401, prime_3, by norm_num⟩
  · exact ⟨15383, 13, prime_15383, prime_13, by norm_num⟩
  · exact ⟨15401, 5, prime_15401, prime_5, by norm_num⟩
  · exact ⟨15391, 11, prime_15391, prime_11, by norm_num⟩
  · exact ⟨15401, 7, prime_15401, prime_7, by norm_num⟩
  · exact ⟨15413, 2, prime_15413, prime_2, by norm_num⟩
  · exact ⟨15413, 3, prime_15413, prime_3, by norm_num⟩
  · exact ⟨15383, 19, prime_15383, prime_19, by norm_num⟩
  · exact ⟨15413, 5, prime_15413, prime_5, by norm_num⟩
  · exact ⟨15391, 17, prime_15391, prime_17, by norm_num⟩
  · exact ⟨15413, 7, prime_15413, prime_7, by norm_num⟩
  · exact ⟨15391, 19, prime_15391, prime_19, by norm_num⟩
  · exact ⟨15427, 2, prime_15427, prime_2, by norm_num⟩
  · exact ⟨15427, 3, prime_15427, prime_3, by norm_num⟩
  · exact ⟨15413, 11, prime_15413, prime_11, by norm_num⟩
  · exact ⟨15427, 5, prime_15427, prime_5, by norm_num⟩
  · exact ⟨15413, 13, prime_15413, prime_13, by norm_num⟩
  · exact ⟨15427, 7, prime_15427, prime_7, by norm_num⟩
  · exact ⟨15439, 2, prime_15439, prime_2, by norm_num⟩
  · exact ⟨15439, 3, prime_15439, prime_3, by norm_num⟩
  · exact ⟨15443, 2, prime_15443, prime_2, by norm_num⟩
  · exact ⟨15443, 3, prime_15443, prime_3, by norm_num⟩
  · exact ⟨15413, 19, prime_15413, prime_19, by norm_num⟩
  · exact ⟨15443, 5, prime_15443, prime_5, by norm_num⟩
  · exact ⟨15451, 2, prime_15451, prime_2, by norm_num⟩
  · exact ⟨15451, 3, prime_15451, prime_3, by norm_num⟩
  · exact ⟨15413, 23, prime_15413, prime_23, by norm_num⟩
  · exact ⟨15451, 5, prime_15451, prime_5, by norm_num⟩
  · exact ⟨15401, 31, prime_15401, prime_31, by norm_num⟩
  · exact ⟨15461, 2, prime_15461, prime_2, by norm_num⟩
  · exact ⟨15461, 3, prime_15461, prime_3, by norm_num⟩
  · exact ⟨15443, 13, prime_15443, prime_13, by norm_num⟩
  · exact ⟨15467, 2, prime_15467, prime_2, by norm_num⟩
  · exact ⟨15467, 3, prime_15467, prime_3, by norm_num⟩
  · exact ⟨15461, 7, prime_15461, prime_7, by norm_num⟩
  · exact ⟨15473, 2, prime_15473, prime_2, by norm_num⟩
  · exact ⟨15473, 3, prime_15473, prime_3, by norm_num⟩
  · exact ⟨15467, 7, prime_15467, prime_7, by norm_num⟩
  · exact ⟨15473, 5, prime_15473, prime_5, by norm_num⟩
  · exact ⟨15451, 17, prime_15451, prime_17, by norm_num⟩
  · exact ⟨15473, 7, prime_15473, prime_7, by norm_num⟩
  · exact ⟨15467, 11, prime_15467, prime_11, by norm_num⟩
  · exact ⟨15373, 59, prime_15373, prime_59, by norm_num⟩
  · exact ⟨15467, 13, prime_15467, prime_13, by norm_num⟩
  · exact ⟨15473, 11, prime_15473, prime_11, by norm_num⟩
  · exact ⟨15493, 2, prime_15493, prime_2, by norm_num⟩
  · exact ⟨15493, 3, prime_15493, prime_3, by norm_num⟩
  · exact ⟨15497, 2, prime_15497, prime_2, by norm_num⟩
  · exact ⟨15497, 3, prime_15497, prime_3, by norm_num⟩
  · exact ⟨15467, 19, prime_15467, prime_19, by norm_num⟩
  · exact ⟨15497, 5, prime_15497, prime_5, by norm_num⟩
  · exact ⟨15451, 29, prime_15451, prime_29, by norm_num⟩
  · exact ⟨15497, 7, prime_15497, prime_7, by norm_num⟩
  · exact ⟨15467, 23, prime_15467, prime_23, by norm_num⟩
  · exact ⟨15511, 2, prime_15511, prime_2, by norm_num⟩
  · exact ⟨15511, 3, prime_15511, prime_3, by norm_num⟩
  · exact ⟨15497, 11, prime_15497, prime_11, by norm_num⟩
  · exact ⟨15511, 5, prime_15511, prime_5, by norm_num⟩
  · exact ⟨15497, 13, prime_15497, prime_13, by norm_num⟩
  · exact ⟨15511, 7, prime_15511, prime_7, by norm_num⟩
  · exact ⟨15493, 17, prime_15493, prime_17, by norm_num⟩
  · exact ⟨15467, 31, prime_15467, prime_31, by norm_num⟩
  · exact ⟨15527, 2, prime_15527, prime_2, by norm_num⟩
  · exact ⟨15527, 3, prime_15527, prime_3, by norm_num⟩
  · exact ⟨15497, 19, prime_15497, prime_19, by norm_num⟩
  · exact ⟨15527, 5, prime_15527, prime_5, by norm_num⟩
  · exact ⟨15493, 23, prime_15493, prime_23, by norm_num⟩
  · exact ⟨15527, 7, prime_15527, prime_7, by norm_num⟩
  · exact ⟨15497, 23, prime_15497, prime_23, by norm_num⟩
  · exact ⟨15541, 2, prime_15541, prime_2, by norm_num⟩
  · exact ⟨15541, 3, prime_15541, prime_3, by norm_num⟩
  · exact ⟨15527, 11, prime_15527, prime_11, by norm_num⟩
  · exact ⟨15541, 5, prime_15541, prime_5, by norm_num⟩
  · exact ⟨15527, 13, prime_15527, prime_13, by norm_num⟩
  · exact ⟨15551, 2, prime_15551, prime_2, by norm_num⟩
  · exact ⟨15551, 3, prime_15551, prime_3, by norm_num⟩
  · exact ⟨15497, 31, prime_15497, prime_31, by norm_num⟩
  · exact ⟨15551, 5, prime_15551, prime_5, by norm_num⟩
  · exact ⟨15559, 2, prime_15559, prime_2, by norm_num⟩
  · exact ⟨15559, 3, prime_15559, prime_3, by norm_num⟩
  · exact ⟨15541, 13, prime_15541, prime_13, by norm_num⟩
  · exact ⟨15559, 5, prime_15559, prime_5, by norm_num⟩
  · exact ⟨15497, 37, prime_15497, prime_37, by norm_num⟩
  · exact ⟨15569, 2, prime_15569, prime_2, by norm_num⟩
  · exact ⟨15569, 3, prime_15569, prime_3, by norm_num⟩
  · exact ⟨15551, 13, prime_15551, prime_13, by norm_num⟩
  · exact ⟨15569, 5, prime_15569, prime_5, by norm_num⟩
  · exact ⟨15559, 11, prime_15559, prime_11, by norm_num⟩
  · exact ⟨15569, 7, prime_15569, prime_7, by norm_num⟩
  · exact ⟨15581, 2, prime_15581, prime_2, by norm_num⟩
  · exact ⟨15583, 2, prime_15583, prime_2, by norm_num⟩
  · exact ⟨15583, 3, prime_15583, prime_3, by norm_num⟩
  · exact ⟨15581, 5, prime_15581, prime_5, by norm_num⟩
  · exact ⟨15583, 5, prime_15583, prime_5, by norm_num⟩
  · exact ⟨15581, 7, prime_15581, prime_7, by norm_num⟩
  · exact ⟨15583, 7, prime_15583, prime_7, by norm_num⟩
  · exact ⟨15541, 29, prime_15541, prime_29, by norm_num⟩
  · exact ⟨15527, 37, prime_15527, prime_37, by norm_num⟩
  · exact ⟨15581, 11, prime_15581, prime_11, by norm_num⟩
  · exact ⟨15601, 2, prime_15601, prime_2, by norm_num⟩

private theorem lemoine_chunk_78 : ∀ k : ℕ, 7803 ≤ k → k ≤ 7863 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * k + 1 = p + 2 * q := by
  intro k hlo hhi
  interval_cases k
  · exact ⟨15601, 3, prime_15601, prime_3, by norm_num⟩
  · exact ⟨15583, 13, prime_15583, prime_13, by norm_num⟩
  · exact ⟨15607, 2, prime_15607, prime_2, by norm_num⟩
  · exact ⟨15607, 3, prime_15607, prime_3, by norm_num⟩
  · exact ⟨15601, 7, prime_15601, prime_7, by norm_num⟩
  · exact ⟨15607, 5, prime_15607, prime_5, by norm_num⟩
  · exact ⟨15581, 19, prime_15581, prime_19, by norm_num⟩
  · exact ⟨15607, 7, prime_15607, prime_7, by norm_num⟩
  · exact ⟨15619, 2, prime_15619, prime_2, by norm_num⟩
  · exact ⟨15619, 3, prime_15619, prime_3, by norm_num⟩
  · exact ⟨15601, 13, prime_15601, prime_13, by norm_num⟩
  · exact ⟨15619, 5, prime_15619, prime_5, by norm_num⟩
  · exact ⟨15569, 31, prime_15569, prime_31, by norm_num⟩
  · exact ⟨15629, 2, prime_15629, prime_2, by norm_num⟩
  · exact ⟨15629, 3, prime_15629, prime_3, by norm_num⟩
  · exact ⟨15551, 43, prime_15551, prime_43, by norm_num⟩
  · exact ⟨15629, 5, prime_15629, prime_5, by norm_num⟩
  · exact ⟨15619, 11, prime_15619, prime_11, by norm_num⟩
  · exact ⟨15629, 7, prime_15629, prime_7, by norm_num⟩
  · exact ⟨15641, 2, prime_15641, prime_2, by norm_num⟩
  · exact ⟨15643, 2, prime_15643, prime_2, by norm_num⟩
  · exact ⟨15643, 3, prime_15643, prime_3, by norm_num⟩
  · exact ⟨15647, 2, prime_15647, prime_2, by norm_num⟩
  · exact ⟨15649, 2, prime_15649, prime_2, by norm_num⟩
  · exact ⟨15649, 3, prime_15649, prime_3, by norm_num⟩
  · exact ⟨15647, 5, prime_15647, prime_5, by norm_num⟩
  · exact ⟨15649, 5, prime_15649, prime_5, by norm_num⟩
  · exact ⟨15647, 7, prime_15647, prime_7, by norm_num⟩
  · exact ⟨15649, 7, prime_15649, prime_7, by norm_num⟩
  · exact ⟨15661, 2, prime_15661, prime_2, by norm_num⟩
  · exact ⟨15661, 3, prime_15661, prime_3, by norm_num⟩
  · exact ⟨15647, 11, prime_15647, prime_11, by norm_num⟩
  · exact ⟨15667, 2, prime_15667, prime_2, by norm_num⟩
  · exact ⟨15667, 3, prime_15667, prime_3, by norm_num⟩
  · exact ⟨15671, 2, prime_15671, prime_2, by norm_num⟩
  · exact ⟨15671, 3, prime_15671, prime_3, by norm_num⟩
  · exact ⟨15641, 19, prime_15641, prime_19, by norm_num⟩
  · exact ⟨15671, 5, prime_15671, prime_5, by norm_num⟩
  · exact ⟨15679, 2, prime_15679, prime_2, by norm_num⟩
  · exact ⟨15679, 3, prime_15679, prime_3, by norm_num⟩
  · exact ⟨15683, 2, prime_15683, prime_2, by norm_num⟩
  · exact ⟨15683, 3, prime_15683, prime_3, by norm_num⟩
  · exact ⟨15629, 31, prime_15629, prime_31, by norm_num⟩
  · exact ⟨15683, 5, prime_15683, prime_5, by norm_num⟩
  · exact ⟨15661, 17, prime_15661, prime_17, by norm_num⟩
  · exact ⟨15683, 7, prime_15683, prime_7, by norm_num⟩
  · exact ⟨15661, 19, prime_15661, prime_19, by norm_num⟩
  · exact ⟨15679, 11, prime_15679, prime_11, by norm_num⟩
  · exact ⟨15641, 31, prime_15641, prime_31, by norm_num⟩
  · exact ⟨15683, 11, prime_15683, prime_11, by norm_num⟩
  · exact ⟨15661, 23, prime_15661, prime_23, by norm_num⟩
  · exact ⟨15683, 13, prime_15683, prime_13, by norm_num⟩
  · exact ⟨15649, 31, prime_15649, prime_31, by norm_num⟩
  · exact ⟨15679, 17, prime_15679, prime_17, by norm_num⟩
  · exact ⟨15641, 37, prime_15641, prime_37, by norm_num⟩
  · exact ⟨15683, 17, prime_15683, prime_17, by norm_num⟩
  · exact ⟨15661, 29, prime_15661, prime_29, by norm_num⟩
  · exact ⟨15683, 19, prime_15683, prime_19, by norm_num⟩
  · exact ⟨15661, 31, prime_15661, prime_31, by norm_num⟩
  · exact ⟨15679, 23, prime_15679, prime_23, by norm_num⟩
  · exact ⟨15641, 43, prime_15641, prime_43, by norm_num⟩

private theorem lemoine_small : ∀ n : ℕ, 7 ≤ n → n ≤ 15727 → Odd n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  intro n hn7 hnle hOdd
  rcases hOdd with ⟨k, hk⟩
  subst n
  have hklo : 3 ≤ k := by omega
  have hkle : k ≤ 7863 := by omega
  by_cases h0 : k ≤ 102
  · exact lemoine_chunk_0 k (by omega) h0
  by_cases h1 : k ≤ 202
  · exact lemoine_chunk_1 k (by omega) h1
  by_cases h2 : k ≤ 302
  · exact lemoine_chunk_2 k (by omega) h2
  by_cases h3 : k ≤ 402
  · exact lemoine_chunk_3 k (by omega) h3
  by_cases h4 : k ≤ 502
  · exact lemoine_chunk_4 k (by omega) h4
  by_cases h5 : k ≤ 602
  · exact lemoine_chunk_5 k (by omega) h5
  by_cases h6 : k ≤ 702
  · exact lemoine_chunk_6 k (by omega) h6
  by_cases h7 : k ≤ 802
  · exact lemoine_chunk_7 k (by omega) h7
  by_cases h8 : k ≤ 902
  · exact lemoine_chunk_8 k (by omega) h8
  by_cases h9 : k ≤ 1002
  · exact lemoine_chunk_9 k (by omega) h9
  by_cases h10 : k ≤ 1102
  · exact lemoine_chunk_10 k (by omega) h10
  by_cases h11 : k ≤ 1202
  · exact lemoine_chunk_11 k (by omega) h11
  by_cases h12 : k ≤ 1302
  · exact lemoine_chunk_12 k (by omega) h12
  by_cases h13 : k ≤ 1402
  · exact lemoine_chunk_13 k (by omega) h13
  by_cases h14 : k ≤ 1502
  · exact lemoine_chunk_14 k (by omega) h14
  by_cases h15 : k ≤ 1602
  · exact lemoine_chunk_15 k (by omega) h15
  by_cases h16 : k ≤ 1702
  · exact lemoine_chunk_16 k (by omega) h16
  by_cases h17 : k ≤ 1802
  · exact lemoine_chunk_17 k (by omega) h17
  by_cases h18 : k ≤ 1902
  · exact lemoine_chunk_18 k (by omega) h18
  by_cases h19 : k ≤ 2002
  · exact lemoine_chunk_19 k (by omega) h19
  by_cases h20 : k ≤ 2102
  · exact lemoine_chunk_20 k (by omega) h20
  by_cases h21 : k ≤ 2202
  · exact lemoine_chunk_21 k (by omega) h21
  by_cases h22 : k ≤ 2302
  · exact lemoine_chunk_22 k (by omega) h22
  by_cases h23 : k ≤ 2402
  · exact lemoine_chunk_23 k (by omega) h23
  by_cases h24 : k ≤ 2502
  · exact lemoine_chunk_24 k (by omega) h24
  by_cases h25 : k ≤ 2602
  · exact lemoine_chunk_25 k (by omega) h25
  by_cases h26 : k ≤ 2702
  · exact lemoine_chunk_26 k (by omega) h26
  by_cases h27 : k ≤ 2802
  · exact lemoine_chunk_27 k (by omega) h27
  by_cases h28 : k ≤ 2902
  · exact lemoine_chunk_28 k (by omega) h28
  by_cases h29 : k ≤ 3002
  · exact lemoine_chunk_29 k (by omega) h29
  by_cases h30 : k ≤ 3102
  · exact lemoine_chunk_30 k (by omega) h30
  by_cases h31 : k ≤ 3202
  · exact lemoine_chunk_31 k (by omega) h31
  by_cases h32 : k ≤ 3302
  · exact lemoine_chunk_32 k (by omega) h32
  by_cases h33 : k ≤ 3402
  · exact lemoine_chunk_33 k (by omega) h33
  by_cases h34 : k ≤ 3502
  · exact lemoine_chunk_34 k (by omega) h34
  by_cases h35 : k ≤ 3602
  · exact lemoine_chunk_35 k (by omega) h35
  by_cases h36 : k ≤ 3702
  · exact lemoine_chunk_36 k (by omega) h36
  by_cases h37 : k ≤ 3802
  · exact lemoine_chunk_37 k (by omega) h37
  by_cases h38 : k ≤ 3902
  · exact lemoine_chunk_38 k (by omega) h38
  by_cases h39 : k ≤ 4002
  · exact lemoine_chunk_39 k (by omega) h39
  by_cases h40 : k ≤ 4102
  · exact lemoine_chunk_40 k (by omega) h40
  by_cases h41 : k ≤ 4202
  · exact lemoine_chunk_41 k (by omega) h41
  by_cases h42 : k ≤ 4302
  · exact lemoine_chunk_42 k (by omega) h42
  by_cases h43 : k ≤ 4402
  · exact lemoine_chunk_43 k (by omega) h43
  by_cases h44 : k ≤ 4502
  · exact lemoine_chunk_44 k (by omega) h44
  by_cases h45 : k ≤ 4602
  · exact lemoine_chunk_45 k (by omega) h45
  by_cases h46 : k ≤ 4702
  · exact lemoine_chunk_46 k (by omega) h46
  by_cases h47 : k ≤ 4802
  · exact lemoine_chunk_47 k (by omega) h47
  by_cases h48 : k ≤ 4902
  · exact lemoine_chunk_48 k (by omega) h48
  by_cases h49 : k ≤ 5002
  · exact lemoine_chunk_49 k (by omega) h49
  by_cases h50 : k ≤ 5102
  · exact lemoine_chunk_50 k (by omega) h50
  by_cases h51 : k ≤ 5202
  · exact lemoine_chunk_51 k (by omega) h51
  by_cases h52 : k ≤ 5302
  · exact lemoine_chunk_52 k (by omega) h52
  by_cases h53 : k ≤ 5402
  · exact lemoine_chunk_53 k (by omega) h53
  by_cases h54 : k ≤ 5502
  · exact lemoine_chunk_54 k (by omega) h54
  by_cases h55 : k ≤ 5602
  · exact lemoine_chunk_55 k (by omega) h55
  by_cases h56 : k ≤ 5702
  · exact lemoine_chunk_56 k (by omega) h56
  by_cases h57 : k ≤ 5802
  · exact lemoine_chunk_57 k (by omega) h57
  by_cases h58 : k ≤ 5902
  · exact lemoine_chunk_58 k (by omega) h58
  by_cases h59 : k ≤ 6002
  · exact lemoine_chunk_59 k (by omega) h59
  by_cases h60 : k ≤ 6102
  · exact lemoine_chunk_60 k (by omega) h60
  by_cases h61 : k ≤ 6202
  · exact lemoine_chunk_61 k (by omega) h61
  by_cases h62 : k ≤ 6302
  · exact lemoine_chunk_62 k (by omega) h62
  by_cases h63 : k ≤ 6402
  · exact lemoine_chunk_63 k (by omega) h63
  by_cases h64 : k ≤ 6502
  · exact lemoine_chunk_64 k (by omega) h64
  by_cases h65 : k ≤ 6602
  · exact lemoine_chunk_65 k (by omega) h65
  by_cases h66 : k ≤ 6702
  · exact lemoine_chunk_66 k (by omega) h66
  by_cases h67 : k ≤ 6802
  · exact lemoine_chunk_67 k (by omega) h67
  by_cases h68 : k ≤ 6902
  · exact lemoine_chunk_68 k (by omega) h68
  by_cases h69 : k ≤ 7002
  · exact lemoine_chunk_69 k (by omega) h69
  by_cases h70 : k ≤ 7102
  · exact lemoine_chunk_70 k (by omega) h70
  by_cases h71 : k ≤ 7202
  · exact lemoine_chunk_71 k (by omega) h71
  by_cases h72 : k ≤ 7302
  · exact lemoine_chunk_72 k (by omega) h72
  by_cases h73 : k ≤ 7402
  · exact lemoine_chunk_73 k (by omega) h73
  by_cases h74 : k ≤ 7502
  · exact lemoine_chunk_74 k (by omega) h74
  by_cases h75 : k ≤ 7602
  · exact lemoine_chunk_75 k (by omega) h75
  by_cases h76 : k ≤ 7702
  · exact lemoine_chunk_76 k (by omega) h76
  by_cases h77 : k ≤ 7802
  · exact lemoine_chunk_77 k (by omega) h77
  · exact lemoine_chunk_78 k (by omega) (by omega)

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture := by
  intro hcore
  constructor
  · intro n hn4 hEven
    by_cases hlarge : 8012 < n
    · have hpos : A219055 n > 0 := hcore n (Or.inl ⟨hEven, hlarge⟩)
      rw [A219055] at hpos
      rcases Finset.card_pos.mp hpos with ⟨q, hq⟩
      simp only [Finset.mem_filter, Finset.mem_range] at hq
      rcases hq with ⟨hqrange, hlt, hqprime, hq6prime, hpprime, hp6prime⟩
      have hmod : n % 2 = 0 := Nat.even_iff.mp hEven
      rw [hmod] at hpprime
      norm_num at hpprime
      refine ⟨n - q, q, hpprime, hqprime, ?_⟩
      omega
    · exact goldbach_small n hn4 (by omega) hEven
  constructor
  · intro n hn7 hOdd
    by_cases hlarge : 15727 < n
    · have hpos : A219055 n > 0 := hcore n (Or.inr ⟨hOdd, hlarge⟩)
      rw [A219055] at hpos
      rcases Finset.card_pos.mp hpos with ⟨q, hq⟩
      simp only [Finset.mem_filter, Finset.mem_range] at hq
      rcases hq with ⟨hqrange, hlt, hqprime, hq6prime, hpprime, hp6prime⟩
      have hmod : n % 2 = 1 := Nat.odd_iff.mp hOdd
      rw [hmod] at hpprime hlt
      norm_num at hpprime hlt
      refine ⟨n - 2 * q, q, hpprime, hqprime, ?_⟩
      omega
    · exact lemoine_small n hn7 (by omega) hOdd
  · change Set.Infinite {p : ℕ | p.Prime ∧ (p + 6).Prime}
    refine Set.infinite_of_forall_exists_gt ?_
    intro B
    let n := 2 * (B + 8013)
    have hnEven : Even n := by
      use B + 8013
      omega
    have hnLarge : 8012 < n := by
      dsimp [n]
      omega
    have hpos : A219055 n > 0 := hcore n (Or.inl ⟨hnEven, hnLarge⟩)
    rw [A219055] at hpos
    rcases Finset.card_pos.mp hpos with ⟨q, hq⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    rcases hq with ⟨hqrange, hlt, hqprime, hq6prime, hpprime, hp6prime⟩
    have hmod : n % 2 = 0 := Nat.even_iff.mp hnEven
    rw [hmod] at hlt hpprime hp6prime
    norm_num at hlt hpprime hp6prime
    by_cases hqgt : B < q
    · exact ⟨q, ⟨hqprime, hq6prime⟩, hqgt⟩
    · refine ⟨n - q - 6, ⟨hp6prime, ?_⟩, ?_⟩
      · have hposp : 0 < n - q - 6 := Nat.Prime.pos hp6prime
        have heq : n - q - 6 + 6 = n - q := by omega
        rw [heq]
        exact hpprime
      · dsimp [n] at hlt ⊢
        omega
