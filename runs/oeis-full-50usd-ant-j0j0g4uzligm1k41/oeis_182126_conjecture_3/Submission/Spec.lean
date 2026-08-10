import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 8000

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0 -- Handle the 0 case for the otherwise 1-indexed sequence
  else (p_n n * p_n (n + 1)) % p_n (n + 2)

/-- For `n > 0`, `a n` is `prime(n)*prime(n+1) mod prime(n+2)` with 0-indexed `Nat.nth`. -/
theorem a_eq (n : ℕ) (hn : 0 < n) :
    a n = (Nat.nth Nat.Prime (n-1) * Nat.nth Nat.Prime n) % Nat.nth Nat.Prime (n+1) := by
  unfold a; simp only [hn.ne', if_false]; congr 1

/-- Key modular identity: `p*p' ≡ (p''-p')*(p''-p)  (mod p'')`. -/
theorem mod_id (p p' p'' : ℕ) (h1 : p ≤ p'') (h2 : p' ≤ p'') :
    (p * p') % p'' = ((p'' - p') * (p'' - p)) % p'' := by
  have ha : p'' - p' + p' = p'' := Nat.sub_add_cancel h2
  have hb : p'' - p + p = p'' := Nat.sub_add_cancel h1
  have key : (p'' - p') * (p'' - p) + p'' * (p + p') = p'' * p'' + p * p' := by nlinarith [ha, hb]
  have : ((p'' - p') * (p'' - p)) % p'' = (p'' * p'' + p * p') % p'' := by
    conv_rhs => rw [← key]; simp [Nat.add_mul_mod_self_left]
  rw [this, Nat.add_mod, Nat.mul_mod_right]; simp

theorem nthp_lt {k m : ℕ} (h : k < m) : Nat.nth Nat.Prime k < Nat.nth Nat.Prime m :=
  Nat.nth_strictMono Nat.infinite_setOf_prime h

/-- Consecutive primes with index `≥ 1` (value `≥ 3`) differ by at least 2. -/
theorem gap_ge_two {k : ℕ} (hk : 1 ≤ k) :
    2 ≤ Nat.nth Nat.Prime (k+1) - Nat.nth Nat.Prime k := by
  have hlt : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k+1) := nthp_lt (by omega)
  have h3 : 3 ≤ Nat.nth Nat.Prime k := by
    calc 3 = Nat.nth Nat.Prime 1 := by simp
    _ ≤ Nat.nth Nat.Prime k := Nat.nth_monotone Nat.infinite_setOf_prime hk
  by_contra hc; push_neg at hc
  have hd : Nat.nth Nat.Prime (k+1) = Nat.nth Nat.Prime k + 1 := by omega
  have hpk : Nat.Prime (Nat.nth Nat.Prime k) := Nat.prime_nth_prime k
  have hpk1 : Nat.Prime (Nat.nth Nat.Prime (k+1)) := Nat.prime_nth_prime (k+1)
  rcases Nat.even_or_odd (Nat.nth Nat.Prime k) with he | ho
  · have := (Nat.Prime.even_iff hpk).mp he; omega
  · have hev : Even (Nat.nth Nat.Prime (k+1)) := by rw [hd]; exact Odd.add_one ho
    have := (Nat.Prime.even_iff hpk1).mp hev; omega

/-- If the product `(p''-p')*(p''-p)` is below `p''` (no wraparound), then `a n` equals
that product, a product of two factors `≥ 2`, hence composite. -/
theorem not_prime_of_no_overflow (p p' p'' : ℕ)
    (h1 : p ≤ p'') (h2 : p' ≤ p'')
    (hf1 : 2 ≤ p'' - p') (hf2 : 2 ≤ p'' - p)
    (hlt : (p'' - p') * (p'' - p) < p'') :
    ¬ Nat.Prime ((p * p') % p'') := by
  rw [mod_id p p' p'' h1 h2, Nat.mod_eq_of_lt hlt]
  intro hp
  rcases (Nat.prime_mul_iff.mp hp) with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

-- Explicit values of the first 63 primes (0-indexed `Nat.nth Nat.Prime`).
theorem nthp_val (k v : ℕ) (hv : Nat.Prime v) (hc : Nat.count Nat.Prime v = k) :
    Nat.nth Nat.Prime k = v := by
  have := Nat.nth_count hv; rwa [hc] at this
theorem nv0 : Nat.nth Nat.Prime 0 = 2 := nthp_val 0 2 (by norm_num) (by decide)
theorem nv1 : Nat.nth Nat.Prime 1 = 3 := nthp_val 1 3 (by norm_num) (by decide)
theorem nv2 : Nat.nth Nat.Prime 2 = 5 := nthp_val 2 5 (by norm_num) (by decide)
theorem nv3 : Nat.nth Nat.Prime 3 = 7 := nthp_val 3 7 (by norm_num) (by decide)
theorem nv4 : Nat.nth Nat.Prime 4 = 11 := nthp_val 4 11 (by norm_num) (by decide)
theorem nv5 : Nat.nth Nat.Prime 5 = 13 := nthp_val 5 13 (by norm_num) (by decide)
theorem nv6 : Nat.nth Nat.Prime 6 = 17 := nthp_val 6 17 (by norm_num) (by decide)
theorem nv7 : Nat.nth Nat.Prime 7 = 19 := nthp_val 7 19 (by norm_num) (by decide)
theorem nv8 : Nat.nth Nat.Prime 8 = 23 := nthp_val 8 23 (by norm_num) (by decide)
theorem nv9 : Nat.nth Nat.Prime 9 = 29 := nthp_val 9 29 (by norm_num) (by decide)
theorem nv10 : Nat.nth Nat.Prime 10 = 31 := nthp_val 10 31 (by norm_num) (by decide)
theorem nv11 : Nat.nth Nat.Prime 11 = 37 := nthp_val 11 37 (by norm_num) (by decide)
theorem nv12 : Nat.nth Nat.Prime 12 = 41 := nthp_val 12 41 (by norm_num) (by decide)
theorem nv13 : Nat.nth Nat.Prime 13 = 43 := nthp_val 13 43 (by norm_num) (by decide)
theorem nv14 : Nat.nth Nat.Prime 14 = 47 := nthp_val 14 47 (by norm_num) (by decide)
theorem nv15 : Nat.nth Nat.Prime 15 = 53 := nthp_val 15 53 (by norm_num) (by decide)
theorem nv16 : Nat.nth Nat.Prime 16 = 59 := nthp_val 16 59 (by norm_num) (by decide)
theorem nv17 : Nat.nth Nat.Prime 17 = 61 := nthp_val 17 61 (by norm_num) (by decide)
theorem nv18 : Nat.nth Nat.Prime 18 = 67 := nthp_val 18 67 (by norm_num) (by decide)
theorem nv19 : Nat.nth Nat.Prime 19 = 71 := nthp_val 19 71 (by norm_num) (by decide)
theorem nv20 : Nat.nth Nat.Prime 20 = 73 := nthp_val 20 73 (by norm_num) (by decide)
theorem nv21 : Nat.nth Nat.Prime 21 = 79 := nthp_val 21 79 (by norm_num) (by decide)
theorem nv22 : Nat.nth Nat.Prime 22 = 83 := nthp_val 22 83 (by norm_num) (by decide)
theorem nv23 : Nat.nth Nat.Prime 23 = 89 := nthp_val 23 89 (by norm_num) (by decide)
theorem nv24 : Nat.nth Nat.Prime 24 = 97 := nthp_val 24 97 (by norm_num) (by decide)
theorem nv25 : Nat.nth Nat.Prime 25 = 101 := nthp_val 25 101 (by norm_num) (by decide)
theorem nv26 : Nat.nth Nat.Prime 26 = 103 := nthp_val 26 103 (by norm_num) (by decide)
theorem nv27 : Nat.nth Nat.Prime 27 = 107 := nthp_val 27 107 (by norm_num) (by decide)
theorem nv28 : Nat.nth Nat.Prime 28 = 109 := nthp_val 28 109 (by norm_num) (by decide)
theorem nv29 : Nat.nth Nat.Prime 29 = 113 := nthp_val 29 113 (by norm_num) (by decide)
theorem nv30 : Nat.nth Nat.Prime 30 = 127 := nthp_val 30 127 (by norm_num) (by decide)
theorem nv31 : Nat.nth Nat.Prime 31 = 131 := nthp_val 31 131 (by norm_num) (by decide)
theorem nv32 : Nat.nth Nat.Prime 32 = 137 := nthp_val 32 137 (by norm_num) (by decide)
theorem nv33 : Nat.nth Nat.Prime 33 = 139 := nthp_val 33 139 (by norm_num) (by decide)
theorem nv34 : Nat.nth Nat.Prime 34 = 149 := nthp_val 34 149 (by norm_num) (by decide)
theorem nv35 : Nat.nth Nat.Prime 35 = 151 := nthp_val 35 151 (by norm_num) (by decide)
theorem nv36 : Nat.nth Nat.Prime 36 = 157 := nthp_val 36 157 (by norm_num) (by decide)
theorem nv37 : Nat.nth Nat.Prime 37 = 163 := nthp_val 37 163 (by norm_num) (by decide)
theorem nv38 : Nat.nth Nat.Prime 38 = 167 := nthp_val 38 167 (by norm_num) (by decide)
theorem nv39 : Nat.nth Nat.Prime 39 = 173 := nthp_val 39 173 (by norm_num) (by decide)
theorem nv40 : Nat.nth Nat.Prime 40 = 179 := nthp_val 40 179 (by norm_num) (by decide)
theorem nv41 : Nat.nth Nat.Prime 41 = 181 := nthp_val 41 181 (by norm_num) (by decide)
theorem nv42 : Nat.nth Nat.Prime 42 = 191 := nthp_val 42 191 (by norm_num) (by decide)
theorem nv43 : Nat.nth Nat.Prime 43 = 193 := nthp_val 43 193 (by norm_num) (by decide)
theorem nv44 : Nat.nth Nat.Prime 44 = 197 := nthp_val 44 197 (by norm_num) (by decide)
theorem nv45 : Nat.nth Nat.Prime 45 = 199 := nthp_val 45 199 (by norm_num) (by decide)
theorem nv46 : Nat.nth Nat.Prime 46 = 211 := nthp_val 46 211 (by norm_num) (by decide)
theorem nv47 : Nat.nth Nat.Prime 47 = 223 := nthp_val 47 223 (by norm_num) (by decide)
theorem nv48 : Nat.nth Nat.Prime 48 = 227 := nthp_val 48 227 (by norm_num) (by decide)
theorem nv49 : Nat.nth Nat.Prime 49 = 229 := nthp_val 49 229 (by norm_num) (by decide)
theorem nv50 : Nat.nth Nat.Prime 50 = 233 := nthp_val 50 233 (by norm_num) (by decide)
theorem nv51 : Nat.nth Nat.Prime 51 = 239 := nthp_val 51 239 (by norm_num) (by decide)
theorem nv52 : Nat.nth Nat.Prime 52 = 241 := nthp_val 52 241 (by norm_num) (by decide)
theorem nv53 : Nat.nth Nat.Prime 53 = 251 := nthp_val 53 251 (by norm_num) (by decide)
theorem nv54 : Nat.nth Nat.Prime 54 = 257 := nthp_val 54 257 (by norm_num) (by decide)
theorem nv55 : Nat.nth Nat.Prime 55 = 263 := nthp_val 55 263 (by norm_num) (by decide)
theorem nv56 : Nat.nth Nat.Prime 56 = 269 := nthp_val 56 269 (by norm_num) (by decide)
theorem nv57 : Nat.nth Nat.Prime 57 = 271 := nthp_val 57 271 (by norm_num) (by decide)
theorem nv58 : Nat.nth Nat.Prime 58 = 277 := nthp_val 58 277 (by norm_num) (by decide)
theorem nv59 : Nat.nth Nat.Prime 59 = 281 := nthp_val 59 281 (by norm_num) (by decide)
theorem nv60 : Nat.nth Nat.Prime 60 = 283 := nthp_val 60 283 (by norm_num) (by decide)
theorem nv61 : Nat.nth Nat.Prime 61 = 293 := nthp_val 61 293 (by norm_num) (by decide)
theorem nv62 : Nat.nth Nat.Prime 62 = 307 := nthp_val 62 307 (by norm_num) (by decide)

/-- Finite verification for `1 ≤ n ≤ 61` (i.e. `prime(n+2) ≤ 307`): in this range the only
prime values of `a n` are `2, 7, 11, 13, 29`. -/
theorem finite_check (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 61)
    (hp : Nat.Prime (Nat.nth Nat.Prime (n-1) * Nat.nth Nat.Prime n % Nat.nth Nat.Prime (n+1))) :
    (Nat.nth Nat.Prime (n-1) * Nat.nth Nat.Prime n % Nat.nth Nat.Prime (n+1)) ∈ ([2,7,11,13,29] : List ℕ) := by
  interval_cases n <;>
    simp only [Nat.reduceSub, Nat.reduceAdd, nv0, nv1, nv2, nv3, nv4, nv5, nv6, nv7, nv8, nv9, nv10, nv11, nv12, nv13, nv14, nv15, nv16, nv17, nv18, nv19, nv20, nv21, nv22, nv23, nv24, nv25, nv26, nv27, nv28, nv29, nv30, nv31, nv32, nv33, nv34, nv35, nv36, nv37, nv38, nv39, nv40, nv41, nv42, nv43, nv44, nv45, nv46, nv47, nv48, nv49, nv50, nv51, nv52, nv53, nv54, nv55, nv56, nv57, nv58, nv59, nv60, nv61, nv62] at hp ⊢ <;>
    revert hp <;> decide

/-- **Reduction to Oppermann's conjecture.**  If `a n` is prime then the product
`(p''-p')*(p''-p) ≥ p''` (no other way to be prime, see `not_prime_of_no_overflow`),
which forces a prime gap of size `≥ √(p''/2)`.  Empirically (verified to `10^10`) this
happens only for `p'' = prime(n+2) ≤ 307`, i.e. `n ≤ 61`.  Proving it for all `n` is
equivalent to ruling out prime gaps `≥ √q` for `q > 307` — a strengthening of
Oppermann's/Legendre's conjecture, OPEN since 1882.  The strongest unconditional bound
known is `gap ≪ p^{0.525}` (Baker–Harman–Pintz); even RH gives only `√p · log p`.
Mathlib provides only Bertrand's postulate (`gap < p`), which is far too weak. -/
theorem overflow_implies_small (n : ℕ) (hn : 1 ≤ n)
    (hov : Nat.nth Nat.Prime (n+1) ≤
      (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n) *
      (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime (n-1))) :
    n ≤ 61 := by
  sorry

/-- Conjecture: Are 2, 7, 11, 13, 29 the only primes in this sequence? -/
theorem oeis_182126_conjecture_3 :
  ∀ n : ℕ, n > 0 → (Nat.Prime (a n) ↔ a n ∈ ([2, 7, 11, 13, 29] : List ℕ)) :=
by
  intro n hn
  rw [a_eq n hn]
  constructor
  · intro hp
    have h01 : Nat.nth Nat.Prime (n-1) < Nat.nth Nat.Prime n := nthp_lt (by omega)
    have h12 : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n+1) := nthp_lt (by omega)
    have hf1 : 2 ≤ Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n := gap_ge_two (by omega)
    have hf2 : 2 ≤ Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime (n-1) := by omega
    by_cases hov : (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n) * (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime (n-1)) < Nat.nth Nat.Prime (n+1)
    · exact absurd hp (not_prime_of_no_overflow _ _ _ (le_of_lt (h01.trans h12)) (le_of_lt h12) hf1 hf2 hov)
    · push_neg at hov
      exact finite_check n (by omega) (overflow_implies_small n (by omega) hov) hp
  · intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h|h|h|h|h <;> rw [h] <;> norm_num