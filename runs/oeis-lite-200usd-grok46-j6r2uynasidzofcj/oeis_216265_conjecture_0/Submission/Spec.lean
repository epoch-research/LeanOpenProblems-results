import FormalConjectures.Util.ProblemImports

open Nat
open Finset

/--
A216265: Number of primes between $n^3 - n$ and $n^3$.
Expressed as $a(n) = \pi(n^3) - \pi(n^3-n)$, where $\pi(x)$ is the prime-counting function.
-/
def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

/-- If there is a prime in `(a, b]` then `π(b) > π(a)`. -/
lemma primeCounting_lt_of_exists_prime {a b p : ℕ} (hp : p.Prime) (h1 : a < p)
    (h2 : p ≤ b) : primeCounting a < primeCounting b := by
  have hmono : primeCounting a ≤ primeCounting (p - 1) :=
    monotone_primeCounting (Nat.le_sub_one_of_lt h1)
  have hsucc : primeCounting (p - 1) < primeCounting p := by
    have hppos : 0 < p := hp.pos
    simp only [primeCounting]
    have : p - 1 + 1 = p := Nat.sub_add_cancel hppos
    rw [this, primeCounting']
    rw [Nat.count_lt_count_succ_iff]
    exact hp
  have hmono2 : primeCounting p ≤ primeCounting b := monotone_primeCounting h2
  exact lt_of_le_of_lt hmono (lt_of_lt_of_le hsucc hmono2)

lemma A216265_pos_of_prime {n p : ℕ} (hp : p.Prime) (h1 : n ^ 3 - n < p)
    (h2 : p ≤ n ^ 3) : A216265 n > 0 := by
  simpa [A216265, gt_iff_lt, Nat.sub_pos_iff_lt] using
    primeCounting_lt_of_exists_prime hp h1 h2

lemma A216265_pos_iff (n : ℕ) :
    A216265 n > 0 ↔ ∃ p, p.Prime ∧ n ^ 3 - n < p ∧ p ≤ n ^ 3 := by
  constructor
  · intro h
    have hlt : primeCounting (n ^ 3 - n) < primeCounting (n ^ 3) := by
      simpa [A216265, gt_iff_lt, Nat.sub_pos_iff_lt] using h
    -- π(b) > π(a) ⇒ some prime in (a, b]
    have : primeCounting' (n ^ 3 - n + 1) < primeCounting' (n ^ 3 + 1) := by
      simpa [primeCounting] using hlt
    obtain ⟨p, hpI, hpP⟩ := exists_of_count_lt_count this
    refine ⟨p, hpP, ?_, ?_⟩
    · have : n ^ 3 - n + 1 ≤ p := (Set.mem_Ico.mp hpI).1
      omega
    · have : p < n ^ 3 + 1 := (Set.mem_Ico.mp hpI).2
      omega
  · rintro ⟨p, hp, h1, h2⟩
    exact A216265_pos_of_prime hp h1 h2

lemma A216265_pos_of_le_600 (n : ℕ) (h1 : 14 ≤ n) (h2 : n ≤ 600) : A216265 n > 0 := by
  interval_cases n
  · exact A216265_pos_of_prime (p := 2741) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3373) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4093) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4909) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5827) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6857) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7993) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 9257) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 10639) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 12163) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 13807) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 15619) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 17573) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 19681) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 21943) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 24379) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 26993) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 29789) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 32749) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 35933) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 39301) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 42863) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 46649) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 50651) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 54869) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 59281) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 63997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 68917) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 74077) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 79493) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 85159) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 91121) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 97327) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 103813) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 110587) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 117643) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 124991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 132647) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 140603) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 148873) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 157457) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 166363) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 175601) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 185189) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 195103) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 205357) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 215983) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 226943) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 238321) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 250043) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 262139) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 274609) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 287491) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 300761) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 314423) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 328481) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 342989) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 357883) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 373231) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 389003) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 405221) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 421847) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 438967) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 456529) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 474547) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 493027) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 511997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 531383) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 551363) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 571783) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 592693) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 614113) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 636043) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 658487) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 681451) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 704947) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 728993) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 753569) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 778681) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 804341) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 830579) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 857369) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 884717) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 912649) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 941179) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 970297) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 999983) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1030297) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1061189) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1092713) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1124833) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1157621) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1191013) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1225019) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1259701) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1295027) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1330997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1367617) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1404919) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1442887) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1481539) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1520851) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1560893) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1601609) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1643027) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1685153) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1727989) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1771559) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1815841) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1860857) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1906621) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 1953109) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2000371) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2048369) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2097143) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2146687) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2196979) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2248087) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2299963) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2352631) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2406097) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2460373) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2515453) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2571337) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2628053) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2685607) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2743991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2803201) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2863283) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2924191) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 2985979) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3048623) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3112129) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3176519) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3241783) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3307939) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3374983) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3442949) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3511799) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3581551) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3652223) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3723871) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3796399) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3869881) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 3944309) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4019663) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4095991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4173277) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4251523) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4330717) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4410937) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4492123) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4574287) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4657453) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4741613) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4826797) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 4912991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5000201) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5088443) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5177701) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5268017) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5359357) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5451769) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5545229) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5639749) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5735291) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5831983) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 5929723) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6028537) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6128477) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6229501) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6331609) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6434849) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6539201) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6644647) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6751267) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6858997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 6967861) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7077883) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7189037) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7301369) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7414853) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7529519) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7645343) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7762373) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7880557) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 7999993) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 8120599) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 8242363) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 8365421) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 8489659) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 8615099) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 8741813) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 8869741) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 8998901) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 9129301) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 9260963) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 9393929) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 9528119) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 9663587) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 9800327) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 9938347) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 10077689) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 10218311) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 10360219) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 10503443) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 10647983) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 10793851) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 10941043) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 11089553) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 11239421) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 11390593) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 11543167) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 11697079) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 11852341) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 12008963) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 12166997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 12326371) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 12487147) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 12649319) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 12812893) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 12977869) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 13144249) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 13312043) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 13481269) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 13651909) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 13823987) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 13997519) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 14172479) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 14348891) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 14526779) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 14706119) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 14886919) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 15069211) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 15252973) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 15438233) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 15624979) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 15813241) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 16002991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 16194263) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 16387039) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 16581371) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 16777213) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 16974589) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 17173493) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 17373977) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 17575981) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 17779577) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 17984723) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 18191443) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 18399737) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 18609623) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 18821083) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 19034161) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 19248773) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 19465093) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 19682987) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 19902499) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 20123633) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 20346407) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 20570821) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 20796871) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 21024569) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 21253931) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 21484937) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 21717637) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 21951997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 22188007) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 22425763) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 22665163) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 22906291) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 23149111) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 23393651) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 23639897) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 23887849) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 24137567) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 24388979) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 24642161) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 24897083) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 25153699) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 25412141) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 25672349) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 25934303) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 26198063) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 26463587) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 26730889) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 26999981) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 27270889) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 27543601) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 27818101) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 28094459) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 28372621) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 28652593) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 28934413) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 29218103) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 29503613) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 29790983) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 30080227) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 30371311) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 30664259) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 30959107) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 31255841) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 31554493) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 31855007) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 32157409) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 32461757) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 32767997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 33076151) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 33386233) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 33698257) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 34012219) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 34328093) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 34645969) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 34965779) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 35287547) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 35611273) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 35936969) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 36264677) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 36594359) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 36925997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 37259687) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 37595359) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 37933043) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 38272739) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 38614469) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 38958193) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 39303997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 39651817) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 40001657) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 40353601) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 40707577) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 41063611) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 41421727) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 41781913) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 42144161) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 42508537) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 42874991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 43243537) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 43614199) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 43986941) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 44361847) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 44738873) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 45118009) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 45499291) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 45882703) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 46268273) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 46655981) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 47045849) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 47437921) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 47832131) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 48228461) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 48627091) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 49027871) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 49430861) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 49836023) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 50243407) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 50652989) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 51064789) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 51478837) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 51895093) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 52313617) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 52734343) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 53157367) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 53582609) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 54010147) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 54439871) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 54871969) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 55306331) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 55742933) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 56181883) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 56623093) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 57066619) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 57512453) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 57960601) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 58411063) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 58863863) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 59318993) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 59776469) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 60236237) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 60698447) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 61162973) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 61629859) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 62099123) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 62570747) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 63044783) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 63521179) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 63999979) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 64481191) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 64964777) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 65450821) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 65939239) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 66430121) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 66923411) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 67419139) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 67917293) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 68417891) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 68920997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 69426529) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 69934523) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 70444981) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 70957919) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 71473333) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 71991289) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 72511711) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 73034617) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 73560043) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 74087983) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 74618449) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 75151411) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 75686957) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 76225007) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 76765597) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 77308769) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 77854481) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 78402749) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 78953579) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 79506979) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 80062981) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 80621561) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 81182723) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 81746491) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 82312873) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 82881847) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 83453449) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 84027653) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 84604517) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 85183981) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 85766053) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 86350843) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 86938301) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 87528379) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 88121123) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 88716533) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 89314609) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 89915383) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 90518837) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 91124983) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 91733839) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 92345401) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 92959673) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 93576599) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 94196369) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 94818793) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 95443991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 96071909) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 96702577) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 97335989) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 97972169) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 98611103) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 99252823) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 99897341) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 100544611) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 101194673) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 101847509) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 102503227) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 103161679) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 103822997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 104487077) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 105154043) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 105823807) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 106496413) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 107171863) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 107850163) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 108531331) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 109215347) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 109902217) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 110591959) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 111284627) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 111980161) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 112678561) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 113379901) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 114084121) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 114791231) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 115501283) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 116214253) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 116930167) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 117648929) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 118370767) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 119095469) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 119823113) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 120553753) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 121287329) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 122023933) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 122763469) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 123505979) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 124251493) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 124999991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 125751487) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 126505991) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 127263523) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 128024047) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 128787613) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 129554171) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 130323839) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 131096491) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 131872199) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 132650971) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 133432829) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 134217689) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 135005683) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 135796723) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 136590871) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 137388091) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 138188389) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 138991757) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 139798349) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 140607977) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 141420757) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 142236613) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 143055623) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 143877803) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 144703123) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 145531537) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 146363179) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 147197903) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 148035863) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 148876997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 149721281) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 150568753) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 151419431) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 152273299) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 153130363) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 153990593) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 154854149) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 155720857) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 156590809) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 157463989) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 158340407) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 159220069) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 160102981) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 160989181) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 161878603) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 162771283) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 163667303) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 164566573) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 165469147) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 166374997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 167284111) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 168196601) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 169112357) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 170031443) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 170953873) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 171879613) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 172808681) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 173741107) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 174676807) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 175615987) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 176558479) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 177504311) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 178453523) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 179406131) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 180362111) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 181321453) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 182284231) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 183250411) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 184219993) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 185192993) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 186169381) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 187149241) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 188132507) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 189119209) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 190109363) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 191102971) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 192100009) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 193100543) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 194104523) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 195111979) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 196122923) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 197137361) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 198155273) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 199176697) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 200201621) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 201229997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 202261999) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 203297447) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 204336463) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 205378997) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 206425039) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 207474677) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 208527853) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 209584577) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 210644869) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 211708699) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 212776163) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 213847187) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 214921793) (by norm_num) (by norm_num) (by norm_num)
  · exact A216265_pos_of_prime (p := 215999989) (by norm_num) (by norm_num) (by norm_num)

/-! Clean development of elementary lemmas for A216265. -/

/-- The number of odd elements of `range n` is `n / 2`. -/
lemma card_filter_odd_range (n : ℕ) :
    ((range n).filter Odd).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_add_one, filter_insert]
    by_cases h : Odd n
    · rw [if_pos h, card_insert_of_notMem, ih]
      · have : n % 2 = 1 := Nat.odd_iff.mp h
        omega
      · simp [mem_filter]
    · rw [if_neg h, ih]
      have : n % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h)
      omega

/-- `π(n) ≤ (n + 1) / 2`. -/
lemma primeCounting_le_succ_div_two (n : ℕ) :
    primeCounting n ≤ (n + 1) / 2 := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> decide
  have heq : primeCounting n = ((range (n + 1)).filter Nat.Prime).card := by
    simp [primeCounting, primeCounting', Nat.count_eq_card_filter_range]
  rw [heq]
  have hsub :
      ((range (n + 1)).filter Nat.Prime) ⊆
        insert 2 (((range (n + 1)).filter Odd).erase 1) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    rcases hp.2.eq_two_or_odd' with h2 | hodd
    · simp [h2]
    · have hp1 : p ≠ 1 := hp.2.ne_one
      have : p ∈ (range (n + 1)).filter Odd := by
        simp [hp.1, hodd]
      simp [mem_erase, this, hp1]
  refine (card_le_card hsub).trans ?_
  have h2n : 2 ∉ ((range (n + 1)).filter Odd).erase 1 := by
    simp [mem_erase, mem_filter]
  rw [card_insert_of_notMem h2n]
  have h1 : 1 ∈ (range (n + 1)).filter Odd := by
    simp; omega
  have herase : (((range (n + 1)).filter Odd).erase 1).card + 1 =
      ((range (n + 1)).filter Odd).card := card_erase_add_one h1
  have hodd := card_filter_odd_range (n + 1)
  omega

lemma n_le_n3 (n : ℕ) (hn : 2 ≤ n) : n ≤ n ^ 3 := by
  calc
    n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
    _ = n ^ 2 := (pow_two n).symm
    _ ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)

lemma descFactorial_eq_prod_Ioc {N K : ℕ} (h : K ≤ N) :
    N.descFactorial K = ∏ i ∈ Ioc (N - K) N, i := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hK : K ≤ N := Nat.le_of_succ_le h
    rw [descFactorial_succ, ih hK]
    have hinsert : Ioc (N - (K + 1)) N = insert (N - K) (Ioc (N - K) N) := by
      ext x
      simp only [mem_Ioc, mem_insert]
      constructor
      · intro ⟨hx1, hx2⟩; omega
      · intro hx
        rcases hx with rfl | ⟨_, _⟩ <;> omega
    have hnotin : N - K ∉ Ioc (N - K) N := by
      simp [mem_Ioc]
    rw [hinsert, prod_insert hnotin]

lemma choose_mul_factorial_eq_prod (n : ℕ) (hn : 2 ≤ n) :
    (n ^ 3).choose n * n.factorial = ∏ i ∈ Ioc (n ^ 3 - n) (n ^ 3), i := by
  have hle := n_le_n3 n hn
  rw [choose_eq_descFactorial_div_factorial]
  rw [Nat.div_mul_cancel (factorial_dvd_descFactorial _ _)]
  exact descFactorial_eq_prod_Ioc hle

lemma prod_Ioc_ge (n : ℕ) (hn : 2 ≤ n) :
    ∏ i ∈ Ioc (n ^ 3 - n) (n ^ 3), i ≥ (n ^ 3 - n + 1) ^ n := by
  have hcard : (Ioc (n ^ 3 - n) (n ^ 3)).card = n := by
    rw [Nat.card_Ioc]
    have := n_le_n3 n hn
    omega
  have hmin : ∀ i ∈ Ioc (n ^ 3 - n) (n ^ 3), n ^ 3 - n + 1 ≤ i := by
    intro i hi; simp at hi; omega
  calc
    ∏ i ∈ Ioc (n ^ 3 - n) (n ^ 3), i
        ≥ ∏ _i ∈ Ioc (n ^ 3 - n) (n ^ 3), (n ^ 3 - n + 1) :=
      prod_le_prod' (fun i hi => hmin i hi)
    _ = (n ^ 3 - n + 1) ^ (Ioc (n ^ 3 - n) (n ^ 3)).card := by simp
    _ = (n ^ 3 - n + 1) ^ n := by rw [hcard]

lemma choose_n3_n_ge (n : ℕ) (hn : 2 ≤ n) :
    (n ^ 3).choose n ≥ (n ^ 2 - 1) ^ n := by
  have hprod := choose_mul_factorial_eq_prod n hn
  have hge := prod_Ioc_ge n hn
  have hmul : (n ^ 3).choose n * n.factorial ≥ (n ^ 3 - n + 1) ^ n := by
    rwa [hprod]
  have hnfac : n.factorial ≤ n ^ n := factorial_le_pow n
  have h1 : (n ^ 3).choose n * n ^ n ≥ (n ^ 3 - n + 1) ^ n :=
    hmul.trans (Nat.mul_le_mul_left _ hnfac)
  have hmuln : n * (n ^ 2 - 1) = n ^ 3 - n := by
    have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega)
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_three, pow_two]
  have h2 : n * (n ^ 2 - 1) ≤ n ^ 3 - n + 1 := by
    rw [hmuln]; exact Nat.le_succ _
  have h3 : (n * (n ^ 2 - 1)) ^ n ≤ (n ^ 3 - n + 1) ^ n :=
    Nat.pow_le_pow_left h2 n
  have h4 : (n * (n ^ 2 - 1)) ^ n = n ^ n * (n ^ 2 - 1) ^ n := mul_pow _ _ n
  have h5 : n ^ n * (n ^ 2 - 1) ^ n ≤ (n ^ 3).choose n * n ^ n := by
    rw [← h4]; exact h3.trans h1
  have hnpos : 0 < n ^ n := Nat.pow_pos (by omega)
  have : n ^ n * (n ^ 2 - 1) ^ n ≤ n ^ n * (n ^ 3).choose n := by
    simpa [Nat.mul_comm] using h5
  exact Nat.le_of_mul_le_mul_left this hnpos



/-- `(n - 1) ^ 4 > n ^ 3` for `n ≥ 6`. -/
lemma pred_pow_four_gt_n_pow_three (n : ℕ) (hn : 6 ≤ n) : n ^ 3 < (n - 1) ^ 4 := by
  have h1 : 1 ≤ n := by omega
  zify [h1]
  have hm : (6 : ℤ) ≤ n := by exact_mod_cast hn
  have hexp : ((n : ℤ) - 1) ^ 4 = n ^ 4 - 4 * n ^ 3 + 6 * n ^ 2 - 4 * n + 1 := by ring
  have hdiff : ((n : ℤ) - 1) ^ 4 - n ^ 3 = n ^ 2 * (n - 2) * (n - 3) - 4 * n + 1 := by
    rw [hexp]; ring
  have hpos : (0 : ℤ) < n ^ 2 * (n - 2) * (n - 3) - 4 * n + 1 := by
    have ha : (n : ℤ) - 2 ≥ 4 := by nlinarith
    have hb : (n : ℤ) - 3 ≥ 3 := by nlinarith
    have hd : (n : ℤ) ^ 2 * (n - 2) ≥ 4 * n ^ 2 := by nlinarith
    have he : (n : ℤ) ^ 2 * (n - 2) * (n - 3) ≥ 4 * n ^ 2 * 3 := by nlinarith
    nlinarith
  linarith

/-- `(n - 1) ^ n > n ^ 3` for `n ≥ 14`. -/
lemma pred_pow_n_gt_n_pow_three (n : ℕ) (hn : 14 ≤ n) : n ^ 3 < (n - 1) ^ n := by
  have h4 : n ^ 3 < (n - 1) ^ 4 := pred_pow_four_gt_n_pow_three n (by omega)
  have hle : (n - 1) ^ 4 ≤ (n - 1) ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact h4.trans_le hle

/-- `(n ^ 2 - 1) ^ 2 ≥ n ^ 3 * (n - 1)` for `n ≥ 2`. -/
lemma sq_pred_sq_ge (n : ℕ) (hn : 2 ≤ n) :
    n ^ 3 * (n - 1) ≤ (n ^ 2 - 1) ^ 2 := by
  have h1 : 1 ≤ n := by omega
  have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega)
  zify [h1, hsq]
  nlinarith

/-- For `n ≥ 14`, `(n ^ 3) ^ ((n + 1) / 2) < (n ^ 2 - 1) ^ n`. -/
lemma pow_pred_sq_pow_gt (n : ℕ) (hn : 14 ≤ n) :
    (n ^ 3) ^ ((n + 1) / 2) < (n ^ 2 - 1) ^ n := by
  have hn2 : 2 ≤ n := by omega
  have hmain : (n ^ 3) ^ (n + 1) < (n ^ 2 - 1) ^ (2 * n) := by
    have hA := sq_pred_sq_ge n hn2
    have hB : (n ^ 3 * (n - 1)) ^ n ≤ ((n ^ 2 - 1) ^ 2) ^ n :=
      Nat.pow_le_pow_left hA n
    have hC : (n ^ 3 * (n - 1)) ^ n = (n ^ 3) ^ n * (n - 1) ^ n := mul_pow _ _ n
    have hD := pred_pow_n_gt_n_pow_three n hn
    have hE : (n ^ 3) ^ n * n ^ 3 < (n ^ 3) ^ n * (n - 1) ^ n :=
      Nat.mul_lt_mul_of_pos_left hD (by positivity)
    have hF : (n ^ 3) ^ n * n ^ 3 = (n ^ 3) ^ (n + 1) := (pow_succ _ _).symm
    have hG : (n ^ 2 - 1) ^ (2 * n) = ((n ^ 2 - 1) ^ 2) ^ n := by
      rw [← pow_mul, Nat.mul_comm]
    calc
      (n ^ 3) ^ (n + 1) = (n ^ 3) ^ n * n ^ 3 := hF.symm
      _ < (n ^ 3) ^ n * (n - 1) ^ n := hE
      _ = (n ^ 3 * (n - 1)) ^ n := hC.symm
      _ ≤ ((n ^ 2 - 1) ^ 2) ^ n := hB
      _ = (n ^ 2 - 1) ^ (2 * n) := hG.symm
  have hhalf : ((n + 1) / 2) * 2 ≤ n + 1 := by omega
  have hpow2 : ((n ^ 3) ^ ((n + 1) / 2)) ^ 2 ≤ (n ^ 3) ^ (n + 1) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by positivity) hhalf
  have : ((n ^ 3) ^ ((n + 1) / 2)) ^ 2 < ((n ^ 2 - 1) ^ n) ^ 2 := by
    calc
      ((n ^ 3) ^ ((n + 1) / 2)) ^ 2 ≤ (n ^ 3) ^ (n + 1) := hpow2
      _ < (n ^ 2 - 1) ^ (2 * n) := hmain
      _ = ((n ^ 2 - 1) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  exact (Nat.pow_lt_pow_iff_left (by omega)).mp this

/-- If `C(n^3, n)` is `n`-smooth then it is `≤ (n^3) ^ π(n)`. -/
lemma choose_n3_le_of_smooth (n : ℕ) (hn : 2 ≤ n)
    (hs : ∀ p, p.Prime → p ∣ (n ^ 3).choose n → p ≤ n) :
    (n ^ 3).choose n ≤ (n ^ 3) ^ n.primeCounting := by
  have hle := n_le_n3 n hn
  have hpos : 0 < (n ^ 3).choose n := Nat.choose_pos hle
  have hn3pos : 0 < n ^ 3 := by omega
  classical
  let S := ((n ^ 3).choose n).primeFactors
  have hdecomp : (n ^ 3).choose n =
      ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p :=
    (factorization_prod_pow_eq_self hpos.ne').symm
  rw [hdecomp]
  have hss : S ⊆ (range (n + 1)).filter Nat.Prime := by
    intro p hp
    have hpP : p.Prime := prime_of_mem_primeFactors hp
    have hdvd : p ∣ (n ^ 3).choose n := dvd_of_mem_primeFactors hp
    have hple : p ≤ n := hs p hpP hdvd
    simp [mem_filter, mem_range, hpP]
    omega
  have hpt : ∀ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤ n ^ 3 :=
    fun p _ => pow_factorization_choose_le hn3pos
  have hprod : ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤
      ∏ _p ∈ S, n ^ 3 := prod_le_prod' hpt
  have hconst : ∏ _p ∈ S, n ^ 3 = (n ^ 3) ^ S.card := by simp
  have hcard : S.card ≤ n.primeCounting := by
    have : n.primeCounting = ((range (n + 1)).filter Nat.Prime).card := by
      simp [primeCounting, primeCounting', Nat.count_eq_card_filter_range]
    rw [this]
    exact card_le_card hss
  calc
    ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤ ∏ _p ∈ S, n ^ 3 := hprod
    _ = (n ^ 3) ^ S.card := hconst
    _ ≤ (n ^ 3) ^ n.primeCounting := Nat.pow_le_pow_right (by positivity) hcard

/-- There is a number in `(n^3 - n, n^3]` with a prime factor `> n`, for `n ≥ 14`. -/
lemma exists_large_prime_factor (n : ℕ) (hn : 14 ≤ n) :
    ∃ m p, n ^ 3 - n < m ∧ m ≤ n ^ 3 ∧ p.Prime ∧ p ∣ m ∧ n < p := by
  by_contra h
  push_neg at h
  have hn2 : 2 ≤ n := by omega
  have hsmooth : ∀ p, p.Prime → p ∣ (n ^ 3).choose n → p ≤ n := by
    intro p hp hdvd
    by_contra hgt
    push_neg at hgt
    have hprod := choose_mul_factorial_eq_prod n hn2
    have hdiv : p ∣ (n ^ 3).choose n * n.factorial := dvd_mul_of_dvd_left hdvd _
    rw [hprod] at hdiv
    rw [Prime.dvd_finset_prod_iff hp.prime] at hdiv
    obtain ⟨m, hm, hpm⟩ := hdiv
    simp only [mem_Ioc] at hm
    have := h m p hm.1 hm.2 hp hpm
    omega
  have hupper : (n ^ 3).choose n ≤ (n ^ 3) ^ ((n + 1) / 2) := by
    have := choose_n3_le_of_smooth n hn2 hsmooth
    have hπ := primeCounting_le_succ_div_two n
    exact this.trans (Nat.pow_le_pow_right (by positivity) hπ)
  have hlower := choose_n3_n_ge n hn2
  have hgt := pow_pred_sq_pow_gt n hn
  have : (n ^ 2 - 1) ^ n ≤ (n ^ 3) ^ ((n + 1) / 2) := hlower.trans hupper
  exact (this.trans_lt hgt).false

/-- `(n - 1) ^ n > n ^ 9` for `n ≥ 14`. -/
lemma pred_pow_n_gt_n_pow_nine (n : ℕ) (hn : 14 ≤ n) : n ^ 9 < (n - 1) ^ n := by
  have hle : (n - 1) ^ 14 ≤ (n - 1) ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  refine lt_of_lt_of_le ?_ hle
  -- Reduce to `n ^ 9 < (n - 1) ^ 14`.
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn _ih =>
    -- `(n + 1) ^ 9 < n ^ 14` since `(n + 1) ^ 9 ≤ (2 n) ^ 9 = 512 * n ^ 9` and `512 < n ^ 5`.
    have h2n : n + 1 ≤ 2 * n := by omega
    have hle2 : (n + 1) ^ 9 ≤ (2 * n) ^ 9 := Nat.pow_le_pow_left h2n 9
    have hmul : (2 * n) ^ 9 = 2 ^ 9 * n ^ 9 := mul_pow 2 n 9
    have h512 : 2 ^ 9 < n ^ 5 := by
      have : 14 ^ 5 ≤ n ^ 5 := Nat.pow_le_pow_left hn 5
      have : 2 ^ 9 < 14 ^ 5 := by norm_num
      omega
    have : 2 ^ 9 * n ^ 9 < n ^ 5 * n ^ 9 :=
      Nat.mul_lt_mul_of_pos_right h512 (by positivity)
    have h14 : n ^ 5 * n ^ 9 = n ^ 14 := by ring
    calc
      (n + 1) ^ 9 ≤ (2 * n) ^ 9 := hle2
      _ = 2 ^ 9 * n ^ 9 := hmul
      _ < n ^ 5 * n ^ 9 := this
      _ = n ^ 14 := h14

/-- For `n ≥ 14`, `(n ^ 3) ^ ((n + 3) / 2) < (n ^ 2 - 1) ^ n`. -/
lemma pow_pred_sq_pow_gt_two (n : ℕ) (hn : 14 ≤ n) :
    (n ^ 3) ^ ((n + 3) / 2) < (n ^ 2 - 1) ^ n := by
  have hn2 : 2 ≤ n := by omega
  have hmain : (n ^ 3) ^ (n + 3) < (n ^ 2 - 1) ^ (2 * n) := by
    have hA := sq_pred_sq_ge n hn2
    have hB : (n ^ 3 * (n - 1)) ^ n ≤ ((n ^ 2 - 1) ^ 2) ^ n :=
      Nat.pow_le_pow_left hA n
    have hC : (n ^ 3 * (n - 1)) ^ n = (n ^ 3) ^ n * (n - 1) ^ n := mul_pow _ _ n
    have h9 := pred_pow_n_gt_n_pow_nine n hn
    have hG : (n ^ 2 - 1) ^ (2 * n) = ((n ^ 2 - 1) ^ 2) ^ n := by
      rw [← pow_mul, Nat.mul_comm]
    have hpow : (n ^ 3) ^ (n + 3) = (n ^ 3) ^ n * n ^ 9 := by
      rw [pow_add]
      congr 1
      rw [← pow_mul n 3 3]
    calc
      (n ^ 3) ^ (n + 3) = (n ^ 3) ^ n * n ^ 9 := hpow
      _ < (n ^ 3) ^ n * (n - 1) ^ n := Nat.mul_lt_mul_of_pos_left h9 (by positivity)
      _ = (n ^ 3 * (n - 1)) ^ n := hC.symm
      _ ≤ ((n ^ 2 - 1) ^ 2) ^ n := hB
      _ = (n ^ 2 - 1) ^ (2 * n) := hG.symm
  have hhalf : ((n + 3) / 2) * 2 ≤ n + 3 := by omega
  have hpow2 : ((n ^ 3) ^ ((n + 3) / 2)) ^ 2 ≤ (n ^ 3) ^ (n + 3) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by positivity) hhalf
  have : ((n ^ 3) ^ ((n + 3) / 2)) ^ 2 < ((n ^ 2 - 1) ^ n) ^ 2 := by
    calc
      ((n ^ 3) ^ ((n + 3) / 2)) ^ 2 ≤ (n ^ 3) ^ (n + 3) := hpow2
      _ < (n ^ 2 - 1) ^ (2 * n) := hmain
      _ = ((n ^ 2 - 1) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  exact (Nat.pow_lt_pow_iff_left (by omega)).mp this

/-- If `C(n^3, n)` has at most `k` prime factors `> n` then it is
`≤ (n ^ 3) ^ (π(n) + k)`. -/
lemma choose_n3_le_of_few_large (n k : ℕ) (hn : 2 ≤ n)
    (hs : #{p ∈ ((n ^ 3).choose n).primeFactors | n < p} ≤ k) :
    (n ^ 3).choose n ≤ (n ^ 3) ^ (n.primeCounting + k) := by
  have hle := n_le_n3 n hn
  have hpos : 0 < (n ^ 3).choose n := Nat.choose_pos hle
  have hn3pos : 0 < n ^ 3 := by omega
  classical
  let S := ((n ^ 3).choose n).primeFactors
  have hdecomp : (n ^ 3).choose n =
      ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p :=
    (factorization_prod_pow_eq_self hpos.ne').symm
  rw [hdecomp]
  have hpt : ∀ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤ n ^ 3 :=
    fun p _ => pow_factorization_choose_le hn3pos
  have hprod : ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤
      ∏ _p ∈ S, n ^ 3 := prod_le_prod' hpt
  have hconst : ∏ _p ∈ S, n ^ 3 = (n ^ 3) ^ S.card := by simp
  have hsplit : S.card =
      #{p ∈ S | p ≤ n} + #{p ∈ S | n < p} := by
    have h := card_filter_add_card_filter_not (s := S) (p := fun p => p ≤ n)
    have h' : {p ∈ S | ¬ p ≤ n} = {p ∈ S | n < p} := by
      ext p
      simp only [mem_filter, not_le]
    rw [h'] at h
    exact h.symm
  have hsmall : #{p ∈ S | p ≤ n} ≤ n.primeCounting := by
    have hss : {p ∈ S | p ≤ n} ⊆ (range (n + 1)).filter Nat.Prime := by
      intro p hp
      simp only [mem_filter] at hp ⊢
      have hpP : p.Prime := prime_of_mem_primeFactors hp.1
      simp [mem_range, hpP]
      omega
    have : n.primeCounting = ((range (n + 1)).filter Nat.Prime).card := by
      simp [primeCounting, primeCounting', Nat.count_eq_card_filter_range]
    rw [this]
    exact card_le_card hss
  have hcard : S.card ≤ n.primeCounting + k := by
    rw [hsplit]
    have : #{p ∈ S | n < p} ≤ k := by
      simpa [S] using hs
    omega
  calc
    ∏ p ∈ S, p ^ ((n ^ 3).choose n).factorization p ≤ ∏ _p ∈ S, n ^ 3 := hprod
    _ = (n ^ 3) ^ S.card := hconst
    _ ≤ (n ^ 3) ^ (n.primeCounting + k) := Nat.pow_le_pow_right (by positivity) hcard

/-- `C(n^3, n)` has at least two distinct prime factors `> n`, for `n ≥ 14`. -/
lemma exists_two_large_prime_factors (n : ℕ) (hn : 14 ≤ n) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n < p ∧ n < q ∧ p ≠ q ∧
      p ∣ (n ^ 3).choose n ∧ q ∣ (n ^ 3).choose n := by
  have hn2 : 2 ≤ n := by omega
  have hpos : 0 < (n ^ 3).choose n := Nat.choose_pos (n_le_n3 n hn2)
  classical
  let S := ((n ^ 3).choose n).primeFactors
  let L := {p ∈ S | n < p}
  have hge : 2 ≤ L.card := by
    by_contra h
    have hk : L.card ≤ 1 := by omega
    have hle := choose_n3_le_of_few_large n 1 hn2 (by simpa [L, S] using hk)
    have hπ := primeCounting_le_succ_div_two n
    have hupper : (n ^ 3).choose n ≤ (n ^ 3) ^ ((n + 1) / 2 + 1) :=
      hle.trans (Nat.pow_le_pow_right (by positivity) (by omega))
    have hhalf : (n + 1) / 2 + 1 = (n + 3) / 2 := by omega
    rw [hhalf] at hupper
    have hlower := choose_n3_n_ge n hn2
    have hgt := pow_pred_sq_pow_gt_two n hn
    exact (hlower.trans hupper).not_gt hgt
  have h1lt : 1 < L.card := Nat.succ_le_iff.mp hge
  obtain ⟨p, q, hpL, hqL, hpq⟩ := one_lt_card_iff.mp h1lt
  simp only [L, mem_filter, S] at hpL hqL
  exact ⟨p, q, prime_of_mem_primeFactors hpL.1, prime_of_mem_primeFactors hqL.1,
    hpL.2, hqL.2, hpq,
    dvd_of_mem_primeFactors hpL.1, dvd_of_mem_primeFactors hqL.1⟩

/-- If `q` is composite and `n`-rough then `q ≥ (n + 1) ^ 2`. -/
lemma composite_rough_ge_sq {n q : ℕ} (hqpos : 0 < q) (hqP : ¬ q.Prime)
    (hmin : n < q.minFac) : (n + 1) ^ 2 ≤ q := by
  have hsq : q.minFac ^ 2 ≤ q := minFac_sq_le_self hqpos hqP
  have hle : n + 1 ≤ q.minFac := Nat.succ_le_of_lt hmin
  exact (Nat.pow_le_pow_left hle 2).trans hsq

/-- A number `≤ n^3` cannot be a product `p * q` with `p > n` and `q` composite and `n`-rough. -/
lemma not_mul_of_prime_and_rough_composite {n m p q : ℕ} (hn : 2 ≤ n)
    (hm2 : m ≤ n ^ 3) (hpn : n < p) (hq : m = p * q)
    (hqpos : 0 < q) (hqP : ¬ q.Prime) (hmin : n < q.minFac) : False := by
  have hqge := composite_rough_ge_sq hqpos hqP hmin
  have hn2 : n ^ 2 < q :=
    (Nat.pow_lt_pow_left n.lt_succ_self (by decide)).trans_le hqge
  have hmul : n * n ^ 2 < p * q :=
    Nat.mul_lt_mul_of_lt_of_le' hpn hn2.le (Nat.pow_pos (by omega))
  have heq : n * n ^ 2 = n ^ 3 := by simp [pow_three, pow_two]
  have : n ^ 3 < p * q := heq ▸ hmul
  rw [hq] at hm2
  exact (not_le_of_gt this) hm2

/-- In the mixed case `m = p * q` with `q ≤ n`, one has `p ≥ n ^ 2 - 1`. -/
lemma mixed_prime_factor_large {n m p q : ℕ} (hn : 2 ≤ n) (hm1 : n ^ 3 - n < m)
    (hq : m = p * q) (hqle : q ≤ n) : n ^ 2 - 1 ≤ p := by
  have hlt : n ^ 3 - n < p * n := by
    have : n ^ 3 - n < p * q := by rwa [← hq]
    exact this.trans_le (Nat.mul_le_mul_left p hqle)
  have h2 : n * (n ^ 2 - 1) = n ^ 3 - n := by
    have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega)
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_three, pow_two]
  have : n * (n ^ 2 - 1) < n * p := by
    have := h2.symm ▸ hlt
    simpa [Nat.mul_comm p n] using this
  have hnpos : 0 < n := by omega
  exact Nat.lt_of_mul_lt_mul_left this |>.le

/-- If `p` is prime then the mixed cofactor cannot be `n`: that would force `p = n ^ 2`. -/
lemma mixed_cofactor_ne_n {n m p q : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (hm1 : n ^ 3 - n < m) (hm2 : m ≤ n ^ 3) (hq : m = p * q) (hqle : q ≤ n) :
    q ≤ n - 1 := by
  by_contra h
  have hqeq : q = n := by omega
  have hsq : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega)
  have h2 : n * (n ^ 2 - 1) = n ^ 3 - n := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_three, pow_two]
  have hp_gt : n ^ 2 - 1 < p := by
    have hlt : n ^ 3 - n < p * n := by
      have : n ^ 3 - n < p * q := by rwa [← hq]
      rwa [hqeq] at this
    have : n * (n ^ 2 - 1) < n * p := by
      have := h2.symm ▸ hlt
      simpa [Nat.mul_comm p n] using this
    exact Nat.lt_of_mul_lt_mul_left this
  have hp_le : p ≤ n ^ 2 := by
    have : p * n ≤ n ^ 3 := by
      have : p * q ≤ n ^ 3 := by rwa [← hq]
      rwa [hqeq] at this
    have hn3 : n ^ 2 * n = n ^ 3 := by ring
    rw [← hn3] at this
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have heq : p = n ^ 2 := by omega
  have : ¬ (n ^ 2).Prime := Nat.Prime.not_prime_pow (x := n) (n := 2) (by omega)
  exact this (heq ▸ hp)

/-- In the mixed case with `q ≤ n - 1`, one has `p ≥ n ^ 2 + n + 1`. -/
lemma mixed_prime_factor_very_large {n m p q : ℕ} (hn : 2 ≤ n) (hm1 : n ^ 3 - n < m)
    (hq : m = p * q) (hqle : q ≤ n - 1) : n ^ 2 + n + 1 ≤ p := by
  have hlt : n ^ 3 - n < p * (n - 1) := by
    have : n ^ 3 - n < p * q := by rwa [← hq]
    exact this.trans_le (Nat.mul_le_mul_left p hqle)
  have hn1 : 1 ≤ n := by omega
  have hle : n ≤ n ^ 3 := by
    calc
      n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
      _ = n ^ 2 := (pow_two n).symm
      _ ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have heq : n * (n + 1) * (n - 1) = n ^ 3 - n := by
    zify [hn1, hle]
    ring
  have : n * (n + 1) * (n - 1) < p * (n - 1) := heq ▸ hlt
  have hpgt : n * (n + 1) < p := Nat.lt_of_mul_lt_mul_right this
  have : n * (n + 1) = n ^ 2 + n := by ring
  omega

lemma sq_sub_sq_of_le {a b : ℕ} (h : a ≤ b) :
    b ^ 2 - a ^ 2 = (b - a) * (b + a) := by
  have hab : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h 2
  zify [hab, h]
  ring

/-- The interval `(n^3 - n, n^3]` contains at most one square. -/
lemma at_most_one_square_in_interval {n a b : ℕ} (hn : 2 ≤ n)
    (ha1 : n ^ 3 - n < a ^ 2) (_ha2 : a ^ 2 ≤ n ^ 3)
    (_hb1 : n ^ 3 - n < b ^ 2) (hb2 : b ^ 2 ≤ n ^ 3)
    (hlt : a < b) : False := by
  have hle : n ≤ n ^ 3 := n_le_n3 n hn
  have hdiff : b ^ 2 - a ^ 2 ≤ n - 1 := by omega
  have hfac := sq_sub_sq_of_le hlt.le
  have hba : 1 ≤ b - a := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
  have hsum : 2 * a + 1 ≤ b + a := by omega
  have hge : 2 * a + 1 ≤ b ^ 2 - a ^ 2 := by
    rw [hfac]
    exact le_trans hsum (Nat.le_mul_of_pos_left (b + a) hba)
  have h_n2 : n ^ 2 ≤ n ^ 3 - n := by
    have h1 : 1 ≤ n := by omega
    zify [h1, hle]
    nlinarith
  have ha_gt : n ^ 2 < a ^ 2 := by omega
  have : n < a := lt_of_pow_lt_pow_left' 2 ha_gt
  omega

/-- A prime power `p ^ k` with `k ≥ 3` and `p > n` exceeds `n^3`. -/
lemma prime_pow_ge_three_gt {n p k : ℕ} (_hn : 2 ≤ n) (hp : n < p) (hk : 3 ≤ k) :
    n ^ 3 < p ^ k := by
  have h3 : n ^ 3 < p ^ 3 := Nat.pow_lt_pow_left hp (by decide)
  have hle : p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  exact h3.trans_le hle

/-- The cofactor of a large prime factor of a number `≤ n^3` is `< n^2`. -/
lemma cofactor_lt_sq {n m p : ℕ} (hn : 2 ≤ n) (hm2 : m ≤ n ^ 3)
    (hp : n < p) : m / p < n ^ 2 := by
  have h2 : n * n * n < n * n * p :=
    Nat.mul_lt_mul_of_pos_left hp (Nat.mul_pos (by omega) (by omega))
  have h3 : n * n * n = n ^ 3 := by ring
  have h4 : n * n = n ^ 2 := (pow_two n).symm
  have : m < n ^ 2 * p := by
    rw [← h4]
    exact hm2.trans_lt (h3 ▸ h2)
  exact Nat.div_lt_of_lt_mul (mul_comm p (n ^ 2) ▸ this)

/-- A prime square in the interval is not itself the desired prime, but the
interval still contains at most one square, so this is never the only
obstruction once a second large-prime-factor witness is known. -/
lemma not_prime_pow_three_of_mem_interval {n p k : ℕ} (hn : 2 ≤ n)
    (hp : n < p) (hk : 3 ≤ k) (hm2 : p ^ k ≤ n ^ 3) : False := by
  exact (prime_pow_ge_three_gt (n := n) (p := p) (k := k) hn hp hk).not_ge hm2

/-- Lower bound companion to `Ico_filter_coprime_le`. -/
lemma Ico_filter_coprime_ge {a : ℕ} (k n : ℕ) (_ha : 0 < a) :
    a.totient * (n / a) ≤ #{x ∈ Ico k (k + n) | a.Coprime x} := by
  have hsub :
      Ico k (k + a * (n / a)) ⊆ Ico k (k + n) := by
    intro x hx
    simp only [mem_Ico] at hx ⊢
    have : a * (n / a) ≤ n := Nat.mul_div_le n a
    omega
  have hfilter :
      {x ∈ Ico k (k + a * (n / a)) | a.Coprime x} ⊆
        {x ∈ Ico k (k + n) | a.Coprime x} := by
    intro x hx
    simp only [mem_filter] at hx ⊢
    exact ⟨hsub hx.1, hx.2⟩
  refine le_trans ?_ (card_le_card hfilter)
  have hblock : ∀ i : ℕ,
      #{x ∈ Ico (k + a * i) (k + a * i + a) | a.Coprime x} = a.totient :=
    fun i => filter_coprime_Ico_eq_totient a (k + a * i)
  have hpack : ∀ t : ℕ,
      #{x ∈ Ico k (k + a * t) | a.Coprime x} = a.totient * t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hdisj :
          Disjoint (Ico k (k + a * t)) (Ico (k + a * t) (k + a * t + a)) :=
        Ico_disjoint_Ico_consecutive _ _ _
      have hsum : k + a * (t + 1) = k + a * t + a := by
        rw [Nat.mul_succ, Nat.add_assoc]
      rw [hsum]
      rw [← Ico_union_Ico_eq_Ico (Nat.le_add_right k (a * t)) (Nat.le_add_right _ _)]
      rw [filter_union, card_union_of_disjoint (hdisj.mono (filter_subset _ _) (filter_subset _ _))]
      rw [ih, hblock t, mul_add, mul_one]
  rw [hpack (n / a)]

lemma totient_30030 : totient 30030 = 5760 := by
  have h : 30030 = 2 * 3 * 5 * 7 * 11 * 13 := by decide
  rw [h]
  have c23 : Coprime (2 * 3) 5 := by decide
  have c235 : Coprime (2 * 3 * 5) 7 := by decide
  have c2357 : Coprime (2 * 3 * 5 * 7) 11 := by decide
  have c235711 : Coprime (2 * 3 * 5 * 7 * 11) 13 := by decide
  have c2_3 : Coprime 2 3 := by decide
  rw [totient_mul c235711, totient_mul c2357, totient_mul c235, totient_mul c23, totient_mul c2_3]
  rw [totient_prime (by decide : Nat.Prime 2)]
  rw [totient_prime (by decide : Nat.Prime 3)]
  rw [totient_prime (by decide : Nat.Prime 5)]
  rw [totient_prime (by decide : Nat.Prime 7)]
  rw [totient_prime (by decide : Nat.Prime 11)]
  rw [totient_prime (by decide : Nat.Prime 13)]

/-- Any interval of length `n ≥ 30030` contains at least `5760` integers coprime to
`30030 = 2*3*5*7*11*13`. -/
lemma many_thirteen_rough {k n : ℕ} (hn : 30030 ≤ n) :
    5760 ≤ #{x ∈ Ico k (k + n) | Nat.Coprime 30030 x} := by
  have h := Ico_filter_coprime_ge (a := 30030) k n (by decide)
  have hdiv : 1 ≤ n / 30030 := Nat.div_pos hn (by decide)
  have : 5760 * (n / 30030) ≤ #{x ∈ Ico k (k + n) | Nat.Coprime 30030 x} := by
    simpa [totient_30030] using h
  exact le_trans (Nat.le_mul_of_pos_right 5760 hdiv) this

/-- For `n > 600` there is a prime in `(n^3 - n, n^3]`. -/
lemma A216265_pos_of_gt_600 (n : ℕ) (hn : n > 600) : A216265 n > 0 := by
  have hn14 : 14 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨m, p, hm1, hm2, hp, hpm, hpn⟩ := exists_large_prime_factor n hn14
  by_cases hmP : m.Prime
  · exact A216265_pos_of_prime hmP hm1 hm2
  -- `m` is composite and has a prime factor `p > n`. Write `m = p * q`.
  obtain ⟨q, hq⟩ : ∃ q, m = p * q := ⟨m / p, (Nat.mul_div_cancel' hpm).symm⟩
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm1
  have hqpos : 0 < q := by
    have : 0 < p * q := by rwa [← hq]
    exact Nat.pos_of_mul_pos_left this
  -- `q > 1` because `m` is composite.
  have hq1 : 1 < q := by
    by_contra h
    have : q = 1 := by omega
    subst this
    rw [hq, mul_one] at hmP
    exact hmP hp
  by_cases hqP : q.Prime
  · -- `m = p * q` is an `n`-rough semiprime (or mixed if we mis-ordered).
    -- A prime in `(n^3 - n, n^3]` is still required.
    sorry
  · -- `q` is composite.
    have hqminP : q.minFac.Prime := minFac_prime (by omega)
    by_cases hmin : n < q.minFac
    · -- `q` is composite and `n`-rough, so `q ≥ (n+1)^2` and `m > n^3`.
      exact (not_mul_of_prime_and_rough_composite hn2 hm2 hpn hq hqpos hqP hmin).elim
    · -- Mixed case: `q` has a prime factor `≤ n`.
      have hminle : q.minFac ≤ n := le_of_not_gt hmin
      have hq_eq : q = m / p := by
        rw [hq, Nat.mul_div_cancel_left _ hp.pos]
      have hq_lt : q < n ^ 2 := by
        have := cofactor_lt_sq (n := n) (m := m) (p := p) hn2 hm2 hpn
        omega
      rcases le_or_gt q n with hqle | hqgt
      · -- `m = p * q` with `q ≤ n`. The cofactor cannot be `n` (that would force
        -- `p = n^2`, which is composite), so `q ≤ n-1` and `p ≥ n^2 + n + 1`.
        have hqle' : q ≤ n - 1 := mixed_cofactor_ne_n hn2 hp hm1 hm2 hq hqle
        have hp_large : n ^ 2 + n + 1 ≤ p := mixed_prime_factor_very_large hn2 hm1 hq hqle'
        -- `p` lies in `[n^2 + n + 1, n^3 / 2]`, strictly below `I`. The mixed
        -- witness is composite, so a different prime in `I` is still required.
        sorry
      · -- `q > n` is composite with a prime factor `≤ n`. Rewrite
        -- `m = s * (p * q')` with small factor `s = q.minFac ≤ n`.
        set s := q.minFac with hs
        have hfac : s ∣ q := minFac_dvd q
        obtain ⟨q', hq'⟩ := hfac
        have hm' : m = s * (p * q') := by
          calc
            m = p * q := hq
            _ = p * (s * q') := by rw [hq']
            _ = s * (p * q') := by ring
        have hmin1 : 1 < s := hqminP.one_lt
        have hsle : s ≤ n := hminle
        -- This is a mixed factorization with small factor `s ≤ n`.
        sorry

/-- %C A216265 Conjecture: a(n) > 0 for n > 13. -/
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  rcases le_or_gt n 600 with hle | hgt
  · exact A216265_pos_of_le_600 n (Nat.succ_le_of_lt h) hle
  · exact A216265_pos_of_gt_600 n hgt
