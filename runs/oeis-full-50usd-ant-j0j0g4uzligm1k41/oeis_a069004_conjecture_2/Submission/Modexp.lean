import Mathlib

/-!
Prototype: fast modular exponentiation with a kernel-reducible (structural) definition,
plus a correctness lemma, and a bridge to `ZMod`.
-/

namespace Cert

/-- `mulMod a b m = a * b % m`, but computed so that no intermediate product exceeds
`2^63` when `a, b < m ≤ 2^40`.  This keeps all values as *small* (unboxed) `Nat`s in the
kernel, avoiding GMP bignum allocations (and the associated heap fragmentation) during
`decide +kernel` reduction. -/
def mulMod (a b m : ℕ) : ℕ :=
  let D : ℕ := 1048576  -- 2^20
  (((a * (b / D)) % m) * D + a * (b % D)) % m

theorem mulMod_eq (a b m : ℕ) : mulMod a b m = a * b % m := by
  show (((a * (b / 1048576)) % m) * 1048576 + a * (b % 1048576)) % m = a * b % m
  have hb : b = 1048576 * (b / 1048576) + b % 1048576 := (Nat.div_add_mod b 1048576).symm
  have key : ((a * (b / 1048576)) % m) * 1048576 + a * (b % 1048576)
      ≡ (a * (b / 1048576)) * 1048576 + a * (b % 1048576) [MOD m] := by
    apply Nat.ModEq.add_right
    apply Nat.ModEq.mul_right
    exact Nat.mod_modEq _ _
  rw [Nat.ModEq] at key
  rw [key]
  congr 1
  conv_rhs => rw [hb]
  ring

/-- `powModAux fuel b e m = b^e % m` provided `e < 2^fuel`.  Structural recursion on `fuel`
so it reduces in the kernel. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | (fuel+1), b, e, m =>
    if e = 0 then 1 % m
    else
      let h := powModAux fuel b (e/2) m
      let h2 := mulMod h h m
      if e % 2 = 1 then mulMod h2 b m else h2

theorem powModAux_correct (fuel : ℕ) :
    ∀ (b e m : ℕ), e < 2^fuel → powModAux fuel b e m = b^e % m := by
  induction fuel with
  | zero =>
    intro b e m he
    simp only [pow_zero, Nat.lt_one_iff] at he
    subst he
    simp [powModAux]
  | succ fuel ih =>
    intro b e m he
    unfold powModAux
    simp only [mulMod_eq]
    by_cases he0 : e = 0
    · subst he0; simp
    · simp only [he0, if_false]
      have hhalf : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he
        omega
      have hih := ih b (e/2) m hhalf
      rw [hih]
      -- key: (b^(e/2) % m) * (b^(e/2) % m) % m = b^(2*(e/2)) % m
      have hsq : (b^(e/2) % m) * (b^(e/2) % m) % m = b^(2*(e/2)) % m := by
        rw [← Nat.mul_mod, ← pow_add]
        ring_nf
      by_cases hpar : e % 2 = 1
      · simp only [hpar, if_true]
        have he2 : e = 2 * (e/2) + 1 := by omega
        rw [hsq]
        conv_rhs => rw [he2]
        rw [pow_add, pow_one, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      · simp only [hpar, if_false]
        have he2 : e = 2 * (e/2) := by omega
        rw [hsq]
        conv_rhs => rw [he2]

/-- `powMod b e m = b^e % m`. -/
def powMod (b e m : ℕ) : ℕ := powModAux e b e m

theorem powMod_correct (b e m : ℕ) : powMod b e m = b^e % m := by
  apply powModAux_correct
  exact Nat.lt_two_pow_self

/-- Bridge to `ZMod`: `(b : ZMod m)^e = powMod b e m`. -/
theorem powMod_zmod (b e m : ℕ) [NeZero m] :
    ((powMod b e m : ℕ) : ZMod m) = (b : ZMod m)^e := by
  rw [powMod_correct]
  push_cast
  rw [ZMod.natCast_mod]
  push_cast
  ring

theorem powMod_lt (b e m : ℕ) (hm : 0 < m) : powMod b e m < m := by
  rw [powMod_correct]; exact Nat.mod_lt _ hm

/-- Structural trial division: checks that no `m ∈ [d, d+fuel)` with `m*m ≤ n` divides `n`.
Kernel-reducible (structural on `fuel`, exits when `n < d*d`). -/
def noFactorLoop : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel+1, n, d =>
    if n < d*d then true
    else if n % d == 0 then false
    else noFactorLoop fuel n (d+1)

theorem noFactorLoop_spec : ∀ (fuel n d : ℕ), noFactorLoop fuel n d = true →
    ∀ m, d ≤ m → m < d + fuel → m ∣ n → n < m * m := by
  intro fuel
  induction fuel with
  | zero => intro n d _ m hdm hm _; omega
  | succ fuel ih =>
    intro n d h m hdm hm hmd
    unfold noFactorLoop at h
    split at h
    · -- n < d*d ≤ m*m
      rename_i hlt
      have : d*d ≤ m*m := Nat.mul_le_mul hdm hdm
      omega
    · split at h
      · exact absurd h (by simp)
      · rename_i hlt hdvd
        -- d ∤ n
        have hdn : ¬ d ∣ n := by
          intro hc
          rw [Nat.dvd_iff_mod_eq_zero] at hc
          rw [hc] at hdvd; simp at hdvd
        rcases Nat.lt_or_ge m (d+1) with hm1 | hm1
        · have hmeq : m = d := by omega
          rw [hmeq] at hmd; exact absurd hmd hdn
        · exact ih n (d+1) h m hm1 (by omega) hmd

/-- Trial-division primality test (correct for the `= true` direction). -/
def trialPrimeB (n : ℕ) : Bool := (2 ≤ n) && noFactorLoop n n 2

theorem trialPrimeB_prime {n : ℕ} (h : trialPrimeB n = true) : Nat.Prime n := by
  rw [trialPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hloop⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm2 hms hmd => ?_⟩
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  have hmn : m ≤ n := le_trans (Nat.le_mul_of_pos_left m (by omega)) hmm
  have := noFactorLoop_spec n n 2 hloop m hm2 (by omega) hmd
  omega

/-- A Pratt/Lucas certificate tree. `node p a smalls bigs`:
  * `p` is the (claimed prime) number,
  * `a` is the Lucas witness,
  * `smalls : List (ℕ × ℕ)` are `(q, e)` where `q` is a prime factor of `p-1` (checked by
    trial division) with multiplicity `e`,
  * `bigs : List (ℕ × ℕ × PC)` are `(q, e, cert)` big prime factors, `q` proven prime by `cert`. -/
inductive PC where
  | node : ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ × PC) → PC

namespace PC

def pp : PC → ℕ | node p _ _ _ => p

mutual
/-- Validity of a certificate. -/
def ok : PC → Bool
  | node p a smalls bigs =>
      (2 ≤ p) &&
      smalls.all (fun x => trialPrimeB x.1) &&
      okBigs bigs &&
      (let prodS := (smalls.map (fun x => x.1 ^ x.2)).prod;
       let prodB := (bigs.map (fun x => x.1 ^ x.2.1)).prod;
       prodS * prodB == p - 1) &&
      (powMod a (p-1) p == 1) &&
      (smalls.all (fun x => powMod a ((p-1)/x.1) p != 1)) &&
      (bigs.all (fun x => powMod a ((p-1)/x.1) p != 1))
def okBigs : List (ℕ × ℕ × PC) → Bool
  | [] => true
  | (q, _, c) :: rest => (c.pp == q) && ok c && okBigs rest
end

end PC

/-- If `r < p` and `1 < p` and `r ≠ 1` then `(r : ZMod p) ≠ 1`. -/
theorem natCast_ne_one_of_lt {p r : ℕ} (hp : 1 < p) (hr : r < p) (h1 : r ≠ 1) :
    (r : ZMod p) ≠ (1 : ZMod p) := by
  haveI : NeZero p := ⟨by omega⟩
  intro hcontra
  have hval : (r : ZMod p).val = (1 : ZMod p).val := by rw [hcontra]
  rw [ZMod.val_natCast_of_lt hr] at hval
  haveI : Fact (1 < p) := ⟨hp⟩
  rw [ZMod.val_one] at hval
  exact h1 hval

/-- Core Lucas primality from the arithmetic conditions. -/
theorem lucas_of_conditions (p a : ℕ) (qs : List ℕ)
    (hp : 2 ≤ p)
    (hqp : ∀ q ∈ qs, Nat.Prime q)
    (hfact : ∀ r : ℕ, r.Prime → r ∣ (p-1) → r ∈ qs)
    (h1 : powMod a (p-1) p = 1)
    (hne : ∀ q ∈ qs, powMod a ((p-1)/q) p ≠ 1) :
    Nat.Prime p := by
  haveI : NeZero p := ⟨by omega⟩
  have hp1 : 1 < p := by omega
  apply lucas_primality p (a : ZMod p)
  · -- (a)^(p-1) = 1
    rw [← powMod_zmod a (p-1) p, h1]
    simp
  · intro q hq hqd
    -- (a)^((p-1)/q) ≠ 1
    rw [← powMod_zmod a ((p-1)/q) p]
    have hmem := hfact q hq hqd
    have hlt := powMod_lt a ((p-1)/q) p (by omega)
    exact natCast_ne_one_of_lt hp1 hlt (hne q hmem)

/-- Every prime factor of `∏ x.1 ^ x.2` is among `facs.map (·.1)` when all `x.1` are prime. -/
theorem prime_factor_mem (facs : List (ℕ × ℕ))
    (hqp : ∀ x ∈ facs, Nat.Prime x.1)
    (r : ℕ) (hr : r.Prime) :
    r ∣ (facs.map (fun x => x.1 ^ x.2)).prod → r ∈ facs.map (fun x => x.1) := by
  induction facs with
  | nil => intro hd; simp at hd; exact absurd hd hr.ne_one
  | cons x xs ih =>
    intro hd
    simp only [List.map_cons, List.prod_cons] at hd
    rcases (Nat.Prime.prime hr).dvd_mul.mp hd with h | h
    · -- r ∣ x.1 ^ x.2
      have hrx : r ∣ x.1 := hr.prime.dvd_of_dvd_pow h
      have hmemx : x ∈ x :: xs := by simp
      have : r = x.1 := ((Nat.prime_dvd_prime_iff_eq hr (hqp x hmemx)).mp hrx)
      simp [this]
    · right
      exact ih (fun y hy => hqp y (List.mem_cons_of_mem _ hy)) h

namespace PC

mutual
theorem ok_prime : ∀ (c : PC), PC.ok c = true → Nat.Prime c.pp
  | node p a smalls bigs, h => by
    rw [PC.ok] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hp, hsm⟩, hbg⟩, hprod⟩, h1⟩, hnesm⟩, hnebg⟩ := h
    show Nat.Prime p
    -- combined factor list
    set allFacs : List (ℕ × ℕ) := smalls ++ bigs.map (fun x => (x.1, x.2.1)) with hAF
    have hbgprime := okBigs_prime bigs hbg
    -- product identity
    have hprodAF : (allFacs.map (fun y => y.1 ^ y.2)).prod = p - 1 := by
      rw [hAF]
      simp only [List.map_append, List.prod_append, List.map_map]
      have : (bigs.map (fun x => x.1 ^ x.2.1)) =
          (List.map ((fun y => y.1 ^ y.2) ∘ (fun x => (x.1, x.2.1))) bigs) := by
        simp [Function.comp]
      rw [← this]; exact hprod
    -- all first components prime
    have hqp : ∀ y ∈ allFacs, Nat.Prime y.1 := by
      intro y hy
      rw [hAF, List.mem_append] at hy
      rcases hy with hy | hy
      · exact trialPrimeB_prime (hsm y hy)
      · rw [List.mem_map] at hy
        obtain ⟨x, hxmem, rfl⟩ := hy
        exact hbgprime x hxmem
    -- qs and hfact
    set qs : List ℕ := allFacs.map (fun y => y.1) with hqs
    have hfact : ∀ r : ℕ, r.Prime → r ∣ (p-1) → r ∈ qs := by
      intro r hr hrd
      rw [hqs]
      exact prime_factor_mem allFacs hqp r hr (hprodAF ▸ hrd)
    have hne : ∀ q ∈ qs, powMod a ((p-1)/q) p ≠ 1 := by
      intro q hq
      rw [hqs, hAF] at hq
      simp only [List.map_append, List.mem_append, List.map_map, List.mem_map] at hq
      rcases hq with hq | hq
      · obtain ⟨x, hxmem, rfl⟩ := hq
        exact hnesm x hxmem
      · obtain ⟨x, hxmem, hxeq⟩ := hq
        simp only [Function.comp] at hxeq
        rw [← hxeq]
        exact hnebg x hxmem
    have hqprime : ∀ q ∈ qs, Nat.Prime q := by
      intro q hq; rw [hqs, List.mem_map] at hq
      obtain ⟨y, hy, rfl⟩ := hq; exact hqp y hy
    exact lucas_of_conditions p a qs hp hqprime hfact h1 hne

theorem okBigs_prime : ∀ (bigs : List (ℕ × ℕ × PC)), PC.okBigs bigs = true →
    ∀ x ∈ bigs, Nat.Prime x.1
  | [], _ => by intro x hx; simp at hx
  | (q, e, c) :: rest, h => by
    rw [PC.okBigs] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hcp, hcok⟩, hrest⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxr
    · -- x = (q,e,c); x.1 = q = c.pp
      show Nat.Prime q
      rw [← hcp]
      exact ok_prime c hcok
    · exact okBigs_prime rest hrest x hxr
end

/-- Convenience: if `ok c = true` then `c.pp` is prime. -/
theorem prime_of_ok {c : PC} (h : ok c = true) : Nat.Prime c.pp := ok_prime c h

end PC

/-! ### Prime counting via trial division -/

theorem noFactorLoop_true : ∀ (fuel n d : ℕ),
    (∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n) → noFactorLoop fuel n d = true := by
  intro fuel
  induction fuel with
  | zero => intro n d _; rfl
  | succ fuel ih =>
    intro n d hcond
    unfold noFactorLoop
    split
    · rfl
    · rename_i hlt
      have hdd : d * d ≤ n := by omega
      have hdn : ¬ d ∣ n := hcond d le_rfl hdd
      split
      · rename_i hdvd
        exfalso; apply hdn
        rw [Nat.dvd_iff_mod_eq_zero]; simpa using hdvd
      · exact ih n (d+1) (fun m hm hmm => hcond m (by omega) hmm)

theorem trialPrimeB_iff (n : ℕ) : trialPrimeB n = true ↔ Nat.Prime n := by
  constructor
  · exact trialPrimeB_prime
  · intro hp
    rw [trialPrimeB, Bool.and_eq_true]
    refine ⟨by simpa using hp.two_le, ?_⟩
    apply noFactorLoop_true
    intro m hm hmm hmd
    have hmn : m ≤ n := le_trans (Nat.le_mul_of_pos_left m (by omega)) hmm
    -- m ∣ n, 2 ≤ m, m ≤ n; if m = n then m*m = n*n > n (n≥2), contradiction with m*m ≤ n
    have hmlt : m < n := by
      rcases eq_or_lt_of_le hmn with heq | h
      · exfalso; rw [heq] at hmm; nlinarith [hp.two_le]
      · exact h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp m hmd) with h1 | h1 <;> omega
theorem trialPrimeB_eq_decide (n : ℕ) : trialPrimeB n = decide (Nat.Prime n) := by
  rw [Bool.eq_iff_iff, trialPrimeB_iff, decide_eq_true_iff]

/-- Count `n ∈ [lo, lo+len)` with `trialPrimeB n`. Depth `≤ len`. -/
def countRange (lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | len+1 => (if trialPrimeB (lo+len) then 1 else 0) + countRange lo len

/-- Count primes in `[0, bsize*blocks)` block by block. Depth `≤ max blocks bsize`. -/
def blockCount (bsize : ℕ) : ℕ → ℕ
  | 0 => 0
  | b+1 => blockCount bsize b + countRange (bsize*b) bsize

theorem countRange_count (lo L : ℕ) :
    countRange lo L + Nat.count (fun n => trialPrimeB n = true) lo
      = Nat.count (fun n => trialPrimeB n = true) (lo+L) := by
  induction L with
  | zero => simp [countRange]
  | succ L ih =>
    rw [countRange, Nat.add_succ, Nat.count_succ]
    have e1 : (if trialPrimeB (lo+L) then (1:ℕ) else 0)
        = (if (trialPrimeB (lo+L) = true) then (1:ℕ) else 0) := by
      cases trialPrimeB (lo+L) <;> simp
    rw [e1]
    omega

theorem blockCount_count (bsize B : ℕ) :
    blockCount bsize B = Nat.count (fun n => trialPrimeB n = true) (bsize*B) := by
  induction B with
  | zero => simp [blockCount]
  | succ B ih =>
    rw [blockCount, ih]
    have h := countRange_count (bsize*B) bsize
    have hmul : bsize * B + bsize = bsize * (B+1) := by ring
    rw [hmul] at h
    omega

theorem count_trialPrimeB_eq_count_prime (k : ℕ) :
    Nat.count (fun n => trialPrimeB n = true) k = Nat.count Nat.Prime k := by
  induction k with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ, ih]
    congr 1
    by_cases hp : Nat.Prime k
    · rw [if_pos hp, if_pos ((trialPrimeB_iff k).mpr hp)]
    · rw [if_neg hp, if_neg (fun h => hp ((trialPrimeB_iff k).mp h))]

/-- Blockwise prime counting equals `Nat.primeCounting` (for `bsize*B = N+1`). -/
theorem blockCount_eq_primeCounting (bsize B N : ℕ) (h : bsize * B = N + 1) :
    blockCount bsize B = Nat.primeCounting N := by
  rw [blockCount_count, count_trialPrimeB_eq_count_prime, h]
  rfl

/-- One step of a telescoping block-count over `[0, hi)`, split as `[0, lo) ∪ [lo, hi)`. -/
theorem count_step (lo len hi c prev tot : ℕ) (hlen : lo + len = hi)
    (htot : c + prev = tot)
    (hc : countRange lo len = c)
    (hprev : Nat.count (fun n => trialPrimeB n = true) lo = prev) :
    Nat.count (fun n => trialPrimeB n = true) hi = tot := by
  have h := countRange_count lo len
  rw [hc, hprev, hlen] at h
  rw [← h]; exact htot

/-- `Nat.primeCounting N` in terms of `Nat.count` of the (kernel-computable) trial-division
predicate.  Lets us count primes `≤ N` block by block. -/
theorem primeCounting_eq_count (N : ℕ) :
    Nat.primeCounting N = Nat.count (fun n => trialPrimeB n = true) (N + 1) := by
  have h : Nat.count (fun n => trialPrimeB n = true) (N + 1) = Nat.primeCounting N := by
    rw [count_trialPrimeB_eq_count_prime]; rfl
  omega

/-! ### Lower bound for `a N` via a chain of certificates -/

/-- Check a chunk of `(s, cert)` pairs: strictly increasing `s` (above `lastS`), `s < N`,
`cert.pp = N^2 + s^2`, and `cert` valid. Structural on the list. -/
def okChain (N : ℕ) : ℕ → List (ℕ × PC) → Bool
  | _, [] => true
  | lastS, (s, c) :: rest =>
      (lastS < s) && (s < N) && (c.pp == N^2 + s^2) && PC.ok c && okChain N s rest

/-- Final `lastS` after scanning a list. -/
def finalS : ℕ → List (ℕ × PC) → ℕ
  | lastS, [] => lastS
  | _, (s, _) :: rest => finalS s rest

theorem okChain_append (N : ℕ) : ∀ (lastS : ℕ) (l1 l2 : List (ℕ × PC)),
    okChain N lastS (l1 ++ l2) =
      (okChain N lastS l1 && okChain N (finalS lastS l1) l2) := by
  intro lastS l1
  induction l1 generalizing lastS with
  | nil => intro l2; simp [okChain, finalS]
  | cons hd tl ih =>
    intro l2
    obtain ⟨s, c⟩ := hd
    simp only [List.cons_append, okChain, finalS]
    rw [ih s l2]
    simp only [Bool.and_assoc]

theorem okChain_sound (N : ℕ) : ∀ (lastS : ℕ) (l : List (ℕ × PC)), okChain N lastS l = true →
    List.Sorted (· < ·) (lastS :: l.map Prod.fst) ∧
    (∀ s ∈ l.map Prod.fst, s < N ∧ Nat.Prime (N^2 + s^2)) := by
  intro lastS l
  induction l generalizing lastS with
  | nil => intro _; refine ⟨?_, by simp⟩; simp [List.Sorted]
  | cons hd tl ih =>
    intro h
    obtain ⟨s, c⟩ := hd
    rw [okChain] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hlt, hsN⟩, hpp⟩, hok⟩, hrest⟩ := h
    obtain ⟨hsorted, hprops⟩ := ih s hrest
    have hcp : Nat.Prime (N^2 + s^2) := by
      have := PC.prime_of_ok hok; rwa [hpp] at this
    refine ⟨?_, ?_⟩
    · -- Sorted (lastS :: s :: tl.map fst)
      simp only [List.map_cons, List.sorted_cons]
      simp only [List.map_cons, List.sorted_cons] at hsorted
      refine ⟨?_, hsorted⟩
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hlt
      · exact lt_trans hlt (hsorted.1 b hb)
    · intro s' hs'
      simp only [List.map_cons, List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · exact ⟨hsN, hcp⟩
      · exact hprops s' hs'

/-- Threaded validity of a list of chunks. -/
def okChunks (N : ℕ) : ℕ → List (List (ℕ × PC)) → Bool
  | _, [] => true
  | lastS, c :: rest => okChain N lastS c && okChunks N (finalS lastS c) rest

theorem okChunks_cons (N lastS b : ℕ) (c : List (ℕ × PC)) (rest : List (List (ℕ × PC)))
    (h1 : okChain N lastS c = true) (hb : finalS lastS c = b)
    (h2 : okChunks N b rest = true) : okChunks N lastS (c :: rest) = true := by
  rw [okChunks, h1, hb, h2, Bool.and_self]

theorem finalS_append (lastS : ℕ) (l1 l2 : List (ℕ × PC)) :
    finalS lastS (l1 ++ l2) = finalS (finalS lastS l1) l2 := by
  induction l1 generalizing lastS with
  | nil => simp [finalS]
  | cons hd tl ih => obtain ⟨s, c⟩ := hd; simp only [List.cons_append, finalS]; exact ih s

theorem okChunks_flatten (N : ℕ) : ∀ (chunks : List (List (ℕ × PC))) (lastS : ℕ),
    okChunks N lastS chunks = true → okChain N lastS chunks.flatten = true := by
  intro chunks
  induction chunks with
  | nil => intro lastS _; simp [okChain]
  | cons c rest ih =>
    intro lastS h
    rw [okChunks, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.flatten_cons, okChain_append, h1, Bool.true_and]
    exact ih (finalS lastS c) h2

/-- The counting function from the problem. -/
def aCount (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun s => if Nat.Prime (n^2 + s^2) then 1 else 0

theorem aCount_ge (N : ℕ) (l : List (ℕ × PC)) (h : okChain N 0 l = true) :
    l.length ≤ aCount N := by
  obtain ⟨hsorted, hprops⟩ := okChain_sound N 0 l h
  set sList := l.map Prod.fst with hsl
  rw [List.sorted_cons] at hsorted
  obtain ⟨hpos, hsortedT⟩ := hsorted
  have hnodup : sList.Nodup := hsortedT.imp (fun h => ne_of_lt h)
  set S : Finset ℕ := sList.toFinset with hS
  have hcard : S.card = l.length := by
    rw [hS, List.toFinset_card_of_nodup hnodup, hsl, List.length_map]
  have hsub : S ⊆ Finset.Ico 1 N := by
    intro s hs
    rw [hS, List.mem_toFinset] at hs
    have h1 : 0 < s := hpos s hs
    have h2 : s < N := (hprops s hs).1
    rw [Finset.mem_Ico]; omega
  have hf1 : ∀ s ∈ S, (if Nat.Prime (N^2 + s^2) then 1 else 0) = 1 := by
    intro s hs
    rw [hS, List.mem_toFinset] at hs
    rw [if_pos (hprops s hs).2]
  calc l.length = S.card := hcard.symm
    _ = ∑ _s ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
    _ = ∑ s ∈ S, (if Nat.Prime (N^2 + s^2) then 1 else 0) :=
        (Finset.sum_congr rfl (fun s hs => (hf1 s hs).symm))
    _ ≤ ∑ s ∈ Finset.Ico 1 N, (if Nat.Prime (N^2 + s^2) then 1 else 0) :=
        Finset.sum_le_sum_of_subset hsub
    _ = aCount N := rfl

/-- Chain checker over plain `s`-values (no certificates): strictly increasing above
`lastS`, and `< N`.  Primality is supplied separately. -/
def okChainS (N : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | lastS, s :: rest => (lastS < s) && (s < N) && okChainS N s rest

def finalSS : ℕ → List ℕ → ℕ
  | lastS, [] => lastS
  | _, s :: rest => finalSS s rest

theorem okChainS_append (N : ℕ) : ∀ (lastS : ℕ) (l1 l2 : List ℕ),
    okChainS N lastS (l1 ++ l2) = (okChainS N lastS l1 && okChainS N (finalSS lastS l1) l2) := by
  intro lastS l1 l2
  induction l1 generalizing lastS with
  | nil => simp [okChainS, finalSS]
  | cons s tl ih =>
    simp only [List.cons_append, okChainS, finalSS]
    rw [ih s]
    simp only [Bool.and_assoc]

theorem finalSS_append (lastS : ℕ) (l1 l2 : List ℕ) :
    finalSS lastS (l1 ++ l2) = finalSS (finalSS lastS l1) l2 := by
  induction l1 generalizing lastS with
  | nil => simp [finalSS]
  | cons s tl ih => simp only [List.cons_append, finalSS]; exact ih s

def okChunksS (N : ℕ) : ℕ → List (List ℕ) → Bool
  | _, [] => true
  | lastS, c :: rest => okChainS N lastS c && okChunksS N (finalSS lastS c) rest

theorem okChunksS_cons (N lastS b : ℕ) (c : List ℕ) (rest : List (List ℕ))
    (h1 : okChainS N lastS c = true) (hb : finalSS lastS c = b)
    (h2 : okChunksS N b rest = true) : okChunksS N lastS (c :: rest) = true := by
  rw [okChunksS, h1, hb, h2, Bool.and_self]

theorem okChunksS_flatten (N : ℕ) : ∀ (chunks : List (List ℕ)) (lastS : ℕ),
    okChunksS N lastS chunks = true → okChainS N lastS chunks.flatten = true := by
  intro chunks
  induction chunks with
  | nil => intro lastS _; simp [okChainS]
  | cons c rest ih =>
    intro lastS h
    rw [okChunksS, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.flatten_cons, okChainS_append, h1, Bool.true_and]
    exact ih (finalSS lastS c) h2

theorem okChainS_sound (N : ℕ) : ∀ (lastS : ℕ) (l : List ℕ), okChainS N lastS l = true →
    List.Sorted (· < ·) (lastS :: l) ∧ (∀ s ∈ l, s < N) := by
  intro lastS l
  induction l generalizing lastS with
  | nil => intro _; exact ⟨by simp [List.Sorted], by simp⟩
  | cons s tl ih =>
    intro h
    rw [okChainS] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlt, hsN⟩, hrest⟩ := h
    obtain ⟨hsorted, hrange⟩ := ih s hrest
    refine ⟨?_, ?_⟩
    · simp only [List.sorted_cons] at hsorted ⊢
      refine ⟨?_, hsorted⟩
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hlt
      · exact lt_trans hlt (hsorted.1 b hb)
    · intro s' hs'
      simp only [List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · exact hsN
      · exact hrange s' hs'

/-- Lower bound for `aCount N` from a strictly increasing list of `s`-values in `(0, N)`
whose squares give primes. -/
theorem aCount_ge_svals (N : ℕ) (l : List ℕ) (h : okChainS N 0 l = true)
    (hp : ∀ s ∈ l, Nat.Prime (N ^ 2 + s ^ 2)) :
    l.length ≤ aCount N := by
  obtain ⟨hsorted, hrange⟩ := okChainS_sound N 0 l h
  rw [List.sorted_cons] at hsorted
  obtain ⟨hpos, hsortedT⟩ := hsorted
  have hnodup : l.Nodup := hsortedT.imp (fun hh => ne_of_lt hh)
  set S : Finset ℕ := l.toFinset with hS
  have hcard : S.card = l.length := by
    rw [hS, List.toFinset_card_of_nodup hnodup]
  have hsub : S ⊆ Finset.Ico 1 N := by
    intro s hs
    rw [hS, List.mem_toFinset] at hs
    rw [Finset.mem_Ico]; exact ⟨hpos s hs, hrange s hs⟩
  have hf1 : ∀ s ∈ S, (if Nat.Prime (N ^ 2 + s ^ 2) then 1 else 0) = 1 := by
    intro s hs
    rw [hS, List.mem_toFinset] at hs
    rw [if_pos (hp s hs)]
  calc l.length = S.card := hcard.symm
    _ = ∑ _s ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
    _ = ∑ s ∈ S, (if Nat.Prime (N ^ 2 + s ^ 2) then 1 else 0) :=
        (Finset.sum_congr rfl (fun s hs => (hf1 s hs).symm))
    _ ≤ ∑ s ∈ Finset.Ico 1 N, (if Nat.Prime (N ^ 2 + s ^ 2) then 1 else 0) :=
        Finset.sum_le_sum_of_subset hsub
    _ = aCount N := rfl

end Cert

-- quick tests
open Cert in
example : powMod 2 10 1000 = 24 := by decide
