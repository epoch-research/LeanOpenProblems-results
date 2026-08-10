import FormalConjectures.Util.ProblemImports

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Nat Finset

/--
A069004: Number of times $n^2 + s^2$ is prime for positive integers $s < n$.
-/
def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun s => if Nat.Prime (n^2 + s^2) then 1 else 0

open scoped Nat.Prime


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


open Cert

theorem hp_21 : Nat.Prime (512720 ^ 2 + 21 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881798841 19 [(2, 3), (3, 3), (5, 1)] [(243409073, 1, (PC.node 243409073 3 [(2, 4), (53, 1), (239, 1), (1201, 1)] []))])) (by decide +kernel)
theorem hp_27 : Nat.Prime (512720 ^ 2 + 27 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881799129 7 [(2, 3), (3, 2), (13, 1), (73, 1)] [(3847351, 1, (PC.node 3847351 3 [(2, 1), (3, 1), (5, 2), (13, 1), (1973, 1)] []))])) (by decide +kernel)
theorem hp_41 : Nat.Prime (512720 ^ 2 + 41 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881800081 3 [(2, 4), (5, 1), (577, 1)] [(5695013, 1, (PC.node 5695013 2 [(2, 2)] [(1423753, 1, (PC.node 1423753 10 [(2, 3), (3, 1), (11, 1), (5393, 1)] []))]))])) (by decide +kernel)
theorem hp_47 : Nat.Prime (512720 ^ 2 + 47 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881800609 3 [(2, 5), (7, 1), (113, 1)] [(10385659, 1, (PC.node 10385659 3 [(2, 1), (3, 4), (64109, 1)] []))])) (by decide +kernel)
theorem hp_59 : Nat.Prime (512720 ^ 2 + 59 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881801881 6 [(2, 3), (5, 1), (23, 1), (29, 1)] [(9853141, 1, (PC.node 9853141 10 [(2, 2), (3, 1), (5, 1), (11, 1), (14929, 1)] []))])) (by decide +kernel)
theorem hp_63 : Nat.Prime (512720 ^ 2 + 63 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881802369 11 [(2, 7), (3, 2)] [(228196009, 1, (PC.node 228196009 7 [(2, 3), (3, 3)] [(1056463, 1, (PC.node 1056463 3 [(2, 1), (3, 1), (11, 1), (16007, 1)] []))]))])) (by decide +kernel)
theorem hp_109 : Nat.Prime (512720 ^ 2 + 109 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881810281 3 [(2, 3), (5, 1)] [(6572045257, 1, (PC.node 6572045257 5 [(2, 3), (3, 1), (7, 1)] [(39119317, 1, (PC.node 39119317 2 [(2, 2), (3, 1), (503, 1), (6481, 1)] []))]))])) (by decide +kernel)
theorem hp_127 : Nat.Prime (512720 ^ 2 + 127 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881814529 3 [(2, 11), (71, 1)] [(1807891, 1, (PC.node 1807891 2 [(2, 1), (3, 1), (5, 1), (7, 1), (8609, 1)] []))])) (by decide +kernel)
theorem hp_129 : Nat.Prime (512720 ^ 2 + 129 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881815041 7 [(2, 9), (3, 3), (5, 1), (13, 1), (37, 1), (7907, 1)] [])) (by decide +kernel)
theorem hp_147 : Nat.Prime (512720 ^ 2 + 147 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881820009 22 [(2, 3), (3, 4)] [(405681821, 1, (PC.node 405681821 2 [(2, 2), (5, 1), (23, 1), (881917, 1)] []))])) (by decide +kernel)
theorem hp_151 : Nat.Prime (512720 ^ 2 + 151 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881821201 6 [(2, 4), (5, 2), (23, 1), (127, 1), (224993, 1)] [])) (by decide +kernel)
theorem hp_159 : Nat.Prime (512720 ^ 2 + 159 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881823681 31 [(2, 6), (3, 3), (5, 1), (7, 1), (569, 1), (7639, 1)] [])) (by decide +kernel)
theorem hp_167 : Nat.Prime (512720 ^ 2 + 167 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881826289 3 [(2, 4), (37, 1)] [(444057139, 1, (PC.node 444057139 3 [(2, 1), (3, 2), (7, 1), (83, 1), (42461, 1)] []))])) (by decide +kernel)
theorem hp_173 : Nat.Prime (512720 ^ 2 + 173 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881828329 3 [(2, 3), (7, 2), (29, 1), (73, 1), (316777, 1)] [])) (by decide +kernel)
theorem hp_179 : Nat.Prime (512720 ^ 2 + 179 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881830441 3 [(2, 3), (5, 1), (113, 1)] [(58159697, 1, (PC.node 58159697 3 [(2, 4), (7, 1), (519283, 1)] []))])) (by decide +kernel)
theorem hp_189 : Nat.Prime (512720 ^ 2 + 189 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881834121 43 [(2, 3), (3, 2), (5, 1), (4177, 1), (174821, 1)] [])) (by decide +kernel)
theorem hp_199 : Nat.Prime (512720 ^ 2 + 199 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881838001 7 [(2, 4), (5, 3), (251, 1), (523669, 1)] [])) (by decide +kernel)
theorem hp_211 : Nat.Prime (512720 ^ 2 + 211 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881842921 6 [(2, 3), (5, 1), (139, 1), (2377, 1), (19891, 1)] [])) (by decide +kernel)
theorem hp_233 : Nat.Prime (512720 ^ 2 + 233 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881852689 6 [(2, 4), (7, 1), (13, 1), (29, 1), (1709, 1), (3643, 1)] [])) (by decide +kernel)
theorem hp_253 : Nat.Prime (512720 ^ 2 + 253 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881862409 3 [(2, 3), (11, 1), (61, 1), (1621, 1), (30211, 1)] [])) (by decide +kernel)
theorem hp_259 : Nat.Prime (512720 ^ 2 + 259 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881865481 3 [(2, 3), (5, 1), (13, 1)] [(505542049, 1, (PC.node 505542049 7 [(2, 5), (3, 1), (11, 1), (31, 1), (15443, 1)] []))])) (by decide +kernel)
theorem hp_269 : Nat.Prime (512720 ^ 2 + 269 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881870761 7 [(2, 3), (5, 1), (71, 1)] [(92564039, 1, (PC.node 92564039 7 [(2, 1), (7, 3), (59, 1), (2287, 1)] []))])) (by decide +kernel)
theorem hp_277 : Nat.Prime (512720 ^ 2 + 277 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881875129 3 [(2, 3), (31, 1), (37, 1), (97, 1), (263, 1), (1123, 1)] [])) (by decide +kernel)
theorem hp_279 : Nat.Prime (512720 ^ 2 + 279 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881876241 7 [(2, 4), (3, 2), (5, 1)] [(365113717, 1, (PC.node 365113717 2 [(2, 2), (3, 1), (11, 1)] [(2766013, 1, (PC.node 2766013 2 [(2, 2), (3, 1), (230501, 1)] []))]))])) (by decide +kernel)
theorem hp_281 : Nat.Prime (512720 ^ 2 + 281 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881877361 3 [(2, 4), (5, 1), (31, 1), (59, 1), (179, 1), (10037, 1)] [])) (by decide +kernel)
theorem hp_297 : Nat.Prime (512720 ^ 2 + 297 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881886609 14 [(2, 4), (3, 2), (11, 1), (12589, 1), (13183, 1)] [])) (by decide +kernel)
theorem hp_303 : Nat.Prime (512720 ^ 2 + 303 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881890209 31 [(2, 5), (3, 3), (7, 1), (157, 1), (251, 1), (1103, 1)] [])) (by decide +kernel)
theorem hp_307 : Nat.Prime (512720 ^ 2 + 307 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881892649 3 [(2, 3), (17, 1), (643, 1)] [(3006151, 1, (PC.node 3006151 3 [(2, 1), (3, 1), (5, 2), (7, 2), (409, 1)] []))])) (by decide +kernel)
theorem hp_309 : Nat.Prime (512720 ^ 2 + 309 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881893881 7 [(2, 3), (3, 4), (5, 1), (23, 1), (59, 1), (59791, 1)] [])) (by decide +kernel)
theorem hp_321 : Nat.Prime (512720 ^ 2 + 321 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881901441 19 [(2, 7), (3, 3), (5, 1), (457, 1), (33289, 1)] [])) (by decide +kernel)
theorem hp_327 : Nat.Prime (512720 ^ 2 + 327 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881905329 11 [(2, 4), (3, 3), (7, 1)] [(86931847, 1, (PC.node 86931847 3 [(2, 1), (3, 3), (17, 1), (281, 1), (337, 1)] []))])) (by decide +kernel)
theorem hp_369 : Nat.Prime (512720 ^ 2 + 369 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881934561 19 [(2, 5), (3, 2), (5, 1), (7, 2)] [(3725651, 1, (PC.node 3725651 6 [(2, 1), (5, 2), (269, 1), (277, 1)] []))])) (by decide +kernel)
theorem hp_379 : Nat.Prime (512720 ^ 2 + 379 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881942041 3 [(2, 3), (5, 1), (241, 1)] [(27269911, 1, (PC.node 27269911 3 [(2, 1), (3, 2), (5, 1), (302999, 1)] []))])) (by decide +kernel)
theorem hp_383 : Nat.Prime (512720 ^ 2 + 383 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881945089 3 [(2, 9), (7, 1)] [(73348757, 1, (PC.node 73348757 2 [(2, 2), (13, 1)] [(1410553, 1, (PC.node 1410553 5 [(2, 3), (3, 2), (11, 1), (13, 1), (137, 1)] []))]))])) (by decide +kernel)
theorem hp_397 : Nat.Prime (512720 ^ 2 + 397 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881956009 3 [(2, 3), (7, 1)] [(4694320643, 1, (PC.node 4694320643 2 [(2, 1), (11, 1), (6353, 1), (33587, 1)] []))])) (by decide +kernel)
theorem hp_447 : Nat.Prime (512720 ^ 2 + 447 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262881998209 11 [(2, 7), (3, 4), (23, 1)] [(1102397, 1, (PC.node 1102397 2 [(2, 2), (275599, 1)] []))])) (by decide +kernel)
theorem hp_449 : Nat.Prime (512720 ^ 2 + 449 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882000001 6 [(2, 7), (5, 6), (131441, 1)] [])) (by decide +kernel)
theorem hp_461 : Nat.Prime (512720 ^ 2 + 461 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882010921 3 [(2, 3), (5, 1)] [(6572050273, 1, (PC.node 6572050273 5 [(2, 5), (3, 2)] [(22819619, 1, (PC.node 22819619 2 [(2, 1), (337, 1), (33857, 1)] []))]))])) (by decide +kernel)
theorem hp_467 : Nat.Prime (512720 ^ 2 + 467 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882016489 3 [(2, 3), (7, 2), (13, 1), (31, 1)] [(1664063, 1, (PC.node 1664063 5 [(2, 1), (17, 2), (2879, 1)] []))])) (by decide +kernel)
theorem hp_479 : Nat.Prime (512720 ^ 2 + 479 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882027841 3 [(2, 6), (5, 1), (61, 1), (599, 1), (22483, 1)] [])) (by decide +kernel)
theorem hp_497 : Nat.Prime (512720 ^ 2 + 497 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882045409 3 [(2, 5), (61, 1), (271, 1), (496949, 1)] [])) (by decide +kernel)
theorem hp_509 : Nat.Prime (512720 ^ 2 + 509 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882057481 3 [(2, 3), (5, 1), (7, 1), (17, 1), (1759, 1), (31397, 1)] [])) (by decide +kernel)
theorem hp_513 : Nat.Prime (512720 ^ 2 + 513 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882061569 11 [(2, 8), (3, 2), (7, 2)] [(2328533, 1, (PC.node 2328533 2 [(2, 2), (757, 1), (769, 1)] []))])) (by decide +kernel)
theorem hp_517 : Nat.Prime (512720 ^ 2 + 517 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882065689 3 [(2, 3), (11, 1), (59, 1), (373, 1), (135743, 1)] [])) (by decide +kernel)
theorem hp_529 : Nat.Prime (512720 ^ 2 + 529 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882078241 3 [(2, 5), (5, 1), (31, 1), (743, 1), (71333, 1)] [])) (by decide +kernel)
theorem hp_543 : Nat.Prime (512720 ^ 2 + 543 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882093249 7 [(2, 6), (3, 3), (17, 1), (503, 1), (17791, 1)] [])) (by decide +kernel)
theorem hp_553 : Nat.Prime (512720 ^ 2 + 553 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882104209 3 [(2, 4), (71, 1), (1289, 1), (179527, 1)] [])) (by decide +kernel)
theorem hp_557 : Nat.Prime (512720 ^ 2 + 557 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882108649 3 [(2, 3), (73, 1), (1171, 1), (384407, 1)] [])) (by decide +kernel)
theorem hp_569 : Nat.Prime (512720 ^ 2 + 569 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882122161 6 [(2, 4), (5, 1), (7, 1), (701, 1), (669661, 1)] [])) (by decide +kernel)
theorem hp_571 : Nat.Prime (512720 ^ 2 + 571 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882124441 3 [(2, 3), (5, 1), (13, 1), (149, 1), (1699, 1), (1997, 1)] [])) (by decide +kernel)
theorem hp_577 : Nat.Prime (512720 ^ 2 + 577 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882131329 3 [(2, 7), (17, 3), (418027, 1)] [])) (by decide +kernel)
theorem hp_579 : Nat.Prime (512720 ^ 2 + 579 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882133641 22 [(2, 3), (3, 5), (5, 1), (7, 1), (17, 2), (29, 1), (461, 1)] [])) (by decide +kernel)
theorem hp_601 : Nat.Prime (512720 ^ 2 + 601 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882159601 3 [(2, 4), (5, 2), (61, 1)] [(10773859, 1, (PC.node 10773859 2 [(2, 1), (3, 1), (307, 1), (5849, 1)] []))])) (by decide +kernel)
theorem hp_623 : Nat.Prime (512720 ^ 2 + 623 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882186529 3 [(2, 5), (13, 1), (139, 1)] [(4546247, 1, (PC.node 4546247 5 [(2, 1), (521, 1), (4363, 1)] []))])) (by decide +kernel)
theorem hp_631 : Nat.Prime (512720 ^ 2 + 631 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882196561 3 [(2, 4), (5, 1), (23, 1), (113, 1), (193, 1), (6551, 1)] [])) (by decide +kernel)
theorem hp_639 : Nat.Prime (512720 ^ 2 + 639 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882206721 31 [(2, 10), (3, 2), (5, 1), (7, 1), (29, 1), (157, 1), (179, 1)] [])) (by decide +kernel)
theorem hp_647 : Nat.Prime (512720 ^ 2 + 647 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882217009 3 [(2, 4), (17, 1), (37, 1)] [(26121047, 1, (PC.node 26121047 10 [(2, 1), (7, 1), (1019, 1), (1831, 1)] []))])) (by decide +kernel)
theorem hp_649 : Nat.Prime (512720 ^ 2 + 649 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882219601 15 [(2, 4), (5, 2), (7, 1), (11, 1), (13, 1), (31, 1), (21179, 1)] [])) (by decide +kernel)
theorem hp_651 : Nat.Prime (512720 ^ 2 + 651 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882222201 19 [(2, 3), (3, 3), (5, 2), (13, 1)] [(3744761, 1, (PC.node 3744761 3 [(2, 3), (5, 1), (17, 1), (5507, 1)] []))])) (by decide +kernel)
theorem hp_657 : Nat.Prime (512720 ^ 2 + 657 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882230049 11 [(2, 5), (3, 2), (23, 1)] [(39686327, 1, (PC.node 39686327 5 [(2, 1), (19, 1), (29, 1), (36013, 1)] []))])) (by decide +kernel)
theorem hp_677 : Nat.Prime (512720 ^ 2 + 677 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882256729 3 [(2, 3), (7, 1), (13, 2), (23, 1)] [(1207699, 1, (PC.node 1207699 3 [(2, 1), (3, 1), (31, 1), (43, 1), (151, 1)] []))])) (by decide +kernel)
theorem hp_683 : Nat.Prime (512720 ^ 2 + 683 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882264889 3 [(2, 3), (349, 1)] [(94155539, 1, (PC.node 94155539 2 [(2, 1)] [(47077769, 1, (PC.node 47077769 3 [(2, 3)] [(5884721, 1, (PC.node 5884721 3 [(2, 4), (5, 1), (17, 1), (4327, 1)] []))]))]))])) (by decide +kernel)
theorem hp_727 : Nat.Prime (512720 ^ 2 + 727 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882326929 3 [(2, 4), (13, 1), (283, 1), (1531, 1), (2917, 1)] [])) (by decide +kernel)
theorem hp_733 : Nat.Prime (512720 ^ 2 + 733 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882335689 3 [(2, 3), (7, 1)] [(4694327423, 1, (PC.node 4694327423 5 [(2, 1), (18379, 1), (127709, 1)] []))])) (by decide +kernel)
theorem hp_747 : Nat.Prime (512720 ^ 2 + 747 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882356409 11 [(2, 3), (3, 2), (7, 1), (17, 1), (101, 1), (303781, 1)] [])) (by decide +kernel)
theorem hp_753 : Nat.Prime (512720 ^ 2 + 753 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882365409 7 [(2, 5), (3, 3), (13, 1), (29, 1), (59, 1), (13679, 1)] [])) (by decide +kernel)
theorem hp_759 : Nat.Prime (512720 ^ 2 + 759 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882374481 21 [(2, 4), (3, 3), (5, 1), (11, 1), (37, 1), (299029, 1)] [])) (by decide +kernel)
theorem hp_787 : Nat.Prime (512720 ^ 2 + 787 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882417769 3 [(2, 3)] [(32860302221, 1, (PC.node 32860302221 2 [(2, 2), (5, 1), (233, 1)] [(7051567, 1, (PC.node 7051567 3 [(2, 1), (3, 1), (17, 1), (257, 1), (269, 1)] []))]))])) (by decide +kernel)
theorem hp_789 : Nat.Prime (512720 ^ 2 + 789 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882420921 11 [(2, 3), (3, 3), (5, 1), (7, 1), (2621, 1), (13267, 1)] [])) (by decide +kernel)
theorem hp_813 : Nat.Prime (512720 ^ 2 + 813 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882459369 21 [(2, 3), (3, 3), (29, 1)] [(41967187, 1, (PC.node 41967187 5 [(2, 1), (3, 1), (17, 1), (411443, 1)] []))])) (by decide +kernel)
theorem hp_817 : Nat.Prime (512720 ^ 2 + 817 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882465889 3 [(2, 5), (7, 1), (17, 1)] [(69034261, 1, (PC.node 69034261 6 [(2, 2), (3, 1), (5, 1), (107, 1), (10753, 1)] []))])) (by decide +kernel)
theorem hp_829 : Nat.Prime (512720 ^ 2 + 829 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882485641 6 [(2, 3), (5, 1), (5651, 1)] [(1162991, 1, (PC.node 1162991 11 [(2, 1), (5, 1), (19, 1), (6121, 1)] []))])) (by decide +kernel)
theorem hp_839 : Nat.Prime (512720 ^ 2 + 839 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882502321 3 [(2, 4), (5, 1), (31, 1)] [(106001009, 1, (PC.node 106001009 3 [(2, 4), (103, 1), (131, 1), (491, 1)] []))])) (by decide +kernel)
theorem hp_861 : Nat.Prime (512720 ^ 2 + 861 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882539721 22 [(2, 3), (3, 3), (5, 1), (23, 1), (241, 1), (43913, 1)] [])) (by decide +kernel)
theorem hp_863 : Nat.Prime (512720 ^ 2 + 863 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882543169 15 [(2, 6), (7, 1), (61, 1)] [(9619531, 1, (PC.node 9619531 31 [(2, 1), (3, 1), (5, 1), (43, 1), (7457, 1)] []))])) (by decide +kernel)
theorem hp_869 : Nat.Prime (512720 ^ 2 + 869 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882553561 3 [(2, 3), (5, 1), (11, 1), (29, 1), (37, 2), (101, 1), (149, 1)] [])) (by decide +kernel)
theorem hp_879 : Nat.Prime (512720 ^ 2 + 879 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882571041 7 [(2, 5), (3, 5), (5, 1), (1559, 1), (4337, 1)] [])) (by decide +kernel)
theorem hp_881 : Nat.Prime (512720 ^ 2 + 881 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882574561 3 [(2, 5), (5, 1)] [(1643016091, 1, (PC.node 1643016091 2 [(2, 1), (3, 1), (5, 1), (61, 1), (271, 1), (3313, 1)] []))])) (by decide +kernel)
theorem hp_883 : Nat.Prime (512720 ^ 2 + 883 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882578089 3 [(2, 3), (13, 1), (17, 1)] [(148689241, 1, (PC.node 148689241 11 [(2, 3), (3, 1), (5, 1), (7, 1), (177011, 1)] []))])) (by decide +kernel)
theorem hp_891 : Nat.Prime (512720 ^ 2 + 891 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882592281 19 [(2, 3), (3, 2), (5, 1), (7, 1), (11, 1)] [(9483499, 1, (PC.node 9483499 2 [(2, 1), (3, 2), (23, 1), (22907, 1)] []))])) (by decide +kernel)
theorem hp_893 : Nat.Prime (512720 ^ 2 + 893 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882595849 3 [(2, 3), (89, 1)] [(369217129, 1, (PC.node 369217129 11 [(2, 3), (3, 1), (7, 1), (727, 1), (3023, 1)] []))])) (by decide +kernel)
theorem hp_911 : Nat.Prime (512720 ^ 2 + 911 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882628321 15 [(2, 5), (5, 1), (13, 1)] [(126385879, 1, (PC.node 126385879 11 [(2, 1), (3, 1)] [(21064313, 1, (PC.node 21064313 3 [(2, 3), (19, 1), (138581, 1)] []))]))])) (by decide +kernel)
theorem hp_919 : Nat.Prime (512720 ^ 2 + 919 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882642961 6 [(2, 4), (5, 1), (7, 1), (17, 1), (149, 1), (185327, 1)] [])) (by decide +kernel)
theorem hp_921 : Nat.Prime (512720 ^ 2 + 921 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882646641 14 [(2, 4), (3, 3), (5, 1), (6827, 1), (17827, 1)] [])) (by decide +kernel)
theorem hp_927 : Nat.Prime (512720 ^ 2 + 927 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882657729 7 [(2, 6), (3, 2), (29, 1)] [(15737707, 1, (PC.node 15737707 2 [(2, 1), (3, 3), (291439, 1)] []))])) (by decide +kernel)
theorem hp_939 : Nat.Prime (512720 ^ 2 + 939 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882680121 11 [(2, 3), (3, 3), (5, 1)] [(243409889, 1, (PC.node 243409889 3 [(2, 5)] [(7606559, 1, (PC.node 7606559 7 [(2, 1), (163, 1), (23333, 1)] []))]))])) (by decide +kernel)
theorem hp_943 : Nat.Prime (512720 ^ 2 + 943 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882687649 6 [(2, 5), (7, 1), (37, 1)] [(31718471, 1, (PC.node 31718471 11 [(2, 1), (5, 1), (7, 1), (67, 1), (6763, 1)] []))])) (by decide +kernel)
theorem hp_967 : Nat.Prime (512720 ^ 2 + 967 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882733489 3 [(2, 4), (61, 1)] [(269347063, 1, (PC.node 269347063 3 [(2, 1), (3, 1), (577, 1), (77801, 1)] []))])) (by decide +kernel)
theorem hp_979 : Nat.Prime (512720 ^ 2 + 979 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882756841 3 [(2, 3), (5, 1), (11, 1), (23, 1), (71, 1), (569, 1), (643, 1)] [])) (by decide +kernel)
theorem hp_989 : Nat.Prime (512720 ^ 2 + 989 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882776521 3 [(2, 3), (5, 1), (7, 1), (13, 1), (59, 1)] [(1224077, 1, (PC.node 1224077 2 [(2, 2), (7, 1), (43717, 1)] []))])) (by decide +kernel)
theorem hp_993 : Nat.Prime (512720 ^ 2 + 993 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882784449 11 [(2, 6), (3, 3), (331, 1), (459611, 1)] [])) (by decide +kernel)
theorem hp_1009 : Nat.Prime (512720 ^ 2 + 1009 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882816481 3 [(2, 5), (5, 1), (71, 1), (3793, 1), (6101, 1)] [])) (by decide +kernel)
theorem hp_1017 : Nat.Prime (512720 ^ 2 + 1017 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882832689 106 [(2, 4), (3, 2), (7, 1), (37, 1), (59, 1), (193, 1), (619, 1)] [])) (by decide +kernel)
theorem hp_1057 : Nat.Prime (512720 ^ 2 + 1057 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882915649 3 [(2, 6)] [(4107545557, 1, (PC.node 4107545557 5 [(2, 2), (3, 1)] [(342295463, 1, (PC.node 342295463 5 [(2, 1), (59, 1)] [(2900809, 1, (PC.node 2900809 11 [(2, 3), (3, 2), (40289, 1)] []))]))]))])) (by decide +kernel)
theorem hp_1061 : Nat.Prime (512720 ^ 2 + 1061 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882924121 3 [(2, 3), (5, 1), (480169, 1), (13687, 1)] [])) (by decide +kernel)
theorem hp_1089 : Nat.Prime (512720 ^ 2 + 1089 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882984321 14 [(2, 7), (3, 2), (5, 1), (11, 1), (17, 1), (61, 1), (4001, 1)] [])) (by decide +kernel)
theorem hp_1091 : Nat.Prime (512720 ^ 2 + 1091 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262882988681 3 [(2, 3), (5, 1), (13, 1), (23, 1), (37, 1), (227, 1), (2617, 1)] [])) (by decide +kernel)
theorem hp_1103 : Nat.Prime (512720 ^ 2 + 1103 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883015009 3 [(2, 5), (29, 1)] [(283279111, 1, (PC.node 283279111 6 [(2, 1), (3, 1), (5, 1)] [(9442637, 1, (PC.node 9442637 3 [(2, 2), (7, 1), (563, 1), (599, 1)] []))]))])) (by decide +kernel)
theorem hp_1121 : Nat.Prime (512720 ^ 2 + 1121 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883055041 6 [(2, 6), (5, 1), (17, 1), (71, 1), (823, 1), (827, 1)] [])) (by decide +kernel)
theorem hp_1143 : Nat.Prime (512720 ^ 2 + 1143 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883104849 19 [(2, 4), (3, 2), (7, 1), (13, 1), (797, 1), (25171, 1)] [])) (by decide +kernel)
theorem hp_1151 : Nat.Prime (512720 ^ 2 + 1151 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883123201 3 [(2, 13), (5, 2), (71, 1), (101, 1), (179, 1)] [])) (by decide +kernel)
theorem hp_1167 : Nat.Prime (512720 ^ 2 + 1167 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883160289 19 [(2, 5), (3, 3), (7, 1), (127, 1), (149, 1), (2297, 1)] [])) (by decide +kernel)
theorem hp_1181 : Nat.Prime (512720 ^ 2 + 1181 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883193161 3 [(2, 3), (5, 1), (7, 1), (1097, 1), (855851, 1)] [])) (by decide +kernel)
theorem hp_1187 : Nat.Prime (512720 ^ 2 + 1187 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883207369 3 [(2, 3)] [(32860400921, 1, (PC.node 32860400921 3 [(2, 3), (5, 1), (17, 1)] [(48324119, 1, (PC.node 48324119 7 [(2, 1)] [(24162059, 1, (PC.node 24162059 2 [(2, 1)] [(12081029, 1, (PC.node 12081029 2 [(2, 2), (193, 1), (15649, 1)] []))]))]))]))])) (by decide +kernel)
theorem hp_1197 : Nat.Prime (512720 ^ 2 + 1197 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883231209 23 [(2, 3), (3, 2), (13, 1)] [(280858153, 1, (PC.node 280858153 10 [(2, 3), (3, 1), (19, 1), (23, 1), (61, 1), (439, 1)] []))])) (by decide +kernel)
theorem hp_1217 : Nat.Prime (512720 ^ 2 + 1217 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883279489 3 [(2, 7), (29, 1), (149, 1), (475301, 1)] [])) (by decide +kernel)
theorem hp_1221 : Nat.Prime (512720 ^ 2 + 1221 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883289241 19 [(2, 3), (3, 3), (5, 1), (11, 1), (13, 1)] [(1702171, 1, (PC.node 1702171 2 [(2, 1), (3, 2), (5, 1), (18913, 1)] []))])) (by decide +kernel)
theorem hp_1227 : Nat.Prime (512720 ^ 2 + 1227 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883303929 23 [(2, 3), (3, 5), (7, 1)] [(19318291, 1, (PC.node 19318291 3 [(2, 1), (3, 1), (5, 1), (17, 1), (37879, 1)] []))])) (by decide +kernel)
theorem hp_1239 : Nat.Prime (512720 ^ 2 + 1239 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883333521 11 [(2, 4), (3, 3), (5, 1), (37, 1)] [(3289331, 1, (PC.node 3289331 2 [(2, 1), (5, 1), (11, 1), (17, 1), (1759, 1)] []))])) (by decide +kernel)
theorem hp_1249 : Nat.Prime (512720 ^ 2 + 1249 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883358401 3 [(2, 6), (5, 2), (13, 1), (89, 1), (142007, 1)] [])) (by decide +kernel)
theorem hp_1271 : Nat.Prime (512720 ^ 2 + 1271 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883413841 3 [(2, 4), (5, 1), (163, 1)] [(20159771, 1, (PC.node 20159771 2 [(2, 1), (5, 1)] [(2015977, 1, (PC.node 2015977 5 [(2, 3), (3, 1), (19, 1), (4421, 1)] []))]))])) (by decide +kernel)
theorem hp_1273 : Nat.Prime (512720 ^ 2 + 1273 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883418929 3 [(2, 4), (13, 1), (31, 1), (101, 1), (403661, 1)] [])) (by decide +kernel)
theorem hp_1289 : Nat.Prime (512720 ^ 2 + 1289 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883459921 3 [(2, 4), (5, 1)] [(3286043249, 1, (PC.node 3286043249 3 [(2, 4), (53, 1)] [(3875051, 1, (PC.node 3875051 10 [(2, 1), (5, 2), (19, 1), (4079, 1)] []))]))])) (by decide +kernel)
theorem hp_1297 : Nat.Prime (512720 ^ 2 + 1297 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883480609 3 [(2, 5), (7, 2), (569, 1), (294649, 1)] [])) (by decide +kernel)
theorem hp_1317 : Nat.Prime (512720 ^ 2 + 1317 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883532889 7 [(2, 3), (3, 3), (13487, 1), (90239, 1)] [])) (by decide +kernel)
theorem hp_1329 : Nat.Prime (512720 ^ 2 + 1329 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883564641 21 [(2, 5), (3, 3), (5, 1), (263, 1), (231379, 1)] [])) (by decide +kernel)
theorem hp_1331 : Nat.Prime (512720 ^ 2 + 1331 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883569961 3 [(2, 3), (5, 1), (11, 1), (31, 1), (2549, 1), (7561, 1)] [])) (by decide +kernel)
theorem hp_1337 : Nat.Prime (512720 ^ 2 + 1337 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883585969 3 [(2, 4), (163, 1)] [(100798921, 1, (PC.node 100798921 14 [(2, 3), (3, 2), (5, 1), (211, 1), (1327, 1)] []))])) (by decide +kernel)
theorem hp_1351 : Nat.Prime (512720 ^ 2 + 1351 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883623601 3 [(2, 4), (5, 2), (13, 2), (37, 1), (61, 1), (1723, 1)] [])) (by decide +kernel)
theorem hp_1373 : Nat.Prime (512720 ^ 2 + 1373 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883683529 3 [(2, 3), (127, 1)] [(258743783, 1, (PC.node 258743783 5 [(2, 1), (11, 1)] [(11761081, 1, (PC.node 11761081 11 [(2, 3), (3, 1), (5, 1), (98009, 1)] []))]))])) (by decide +kernel)
theorem hp_1383 : Nat.Prime (512720 ^ 2 + 1383 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883711089 11 [(2, 4), (3, 3)] [(608527109, 1, (PC.node 608527109 3 [(2, 2), (7, 1), (419, 1), (51869, 1)] []))])) (by decide +kernel)
theorem hp_1387 : Nat.Prime (512720 ^ 2 + 1387 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883722169 3 [(2, 3), (37, 1)] [(888120683, 1, (PC.node 888120683 2 [(2, 1), (53, 1), (71, 1), (199, 1), (593, 1)] []))])) (by decide +kernel)
theorem hp_1397 : Nat.Prime (512720 ^ 2 + 1397 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883750009 3 [(2, 3), (11, 1), (31, 1)] [(96365011, 1, (PC.node 96365011 2 [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (26993, 1)] []))])) (by decide +kernel)
theorem hp_1403 : Nat.Prime (512720 ^ 2 + 1403 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883766809 3 [(2, 3), (13, 1), (113, 1), (193, 1), (115903, 1)] [])) (by decide +kernel)
theorem hp_1409 : Nat.Prime (512720 ^ 2 + 1409 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883783681 6 [(2, 10), (5, 1), (7, 1), (479, 1), (15313, 1)] [])) (by decide +kernel)
theorem hp_1413 : Nat.Prime (512720 ^ 2 + 1413 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883794969 28 [(2, 3), (3, 2), (23, 2)] [(6902011, 1, (PC.node 6902011 2 [(2, 1), (3, 4), (5, 1), (8521, 1)] []))])) (by decide +kernel)
theorem hp_1429 : Nat.Prime (512720 ^ 2 + 1429 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883840441 6 [(2, 3), (5, 1), (13, 1), (17, 1), (1511, 1), (19681, 1)] [])) (by decide +kernel)
theorem hp_1439 : Nat.Prime (512720 ^ 2 + 1439 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883869121 3 [(2, 6), (5, 1), (23, 1)] [(35717917, 1, (PC.node 35717917 2 [(2, 2), (3, 1), (13, 1), (228961, 1)] []))])) (by decide +kernel)
theorem hp_1457 : Nat.Prime (512720 ^ 2 + 1457 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883921249 3 [(2, 5), (13, 1), (139, 1)] [(4546277, 1, (PC.node 4546277 3 [(2, 2), (7, 1), (17, 1), (9551, 1)] []))])) (by decide +kernel)
theorem hp_1473 : Nat.Prime (512720 ^ 2 + 1473 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883968129 7 [(2, 7), (3, 4), (61, 1), (415661, 1)] [])) (by decide +kernel)
theorem hp_1481 : Nat.Prime (512720 ^ 2 + 1481 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262883991761 7 [(2, 4), (5, 1), (13, 1)] [(252773069, 1, (PC.node 252773069 2 [(2, 2), (17, 1), (173, 1), (21487, 1)] []))])) (by decide +kernel)
theorem hp_1487 : Nat.Prime (512720 ^ 2 + 1487 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884009569 3 [(2, 5), (73, 1), (7529, 1), (14947, 1)] [])) (by decide +kernel)
theorem hp_1499 : Nat.Prime (512720 ^ 2 + 1499 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884045401 3 [(2, 3), (5, 2), (37, 1)] [(35524871, 1, (PC.node 35524871 7 [(2, 1), (5, 1), (19, 1), (181, 1), (1033, 1)] []))])) (by decide +kernel)
theorem hp_1511 : Nat.Prime (512720 ^ 2 + 1511 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884081521 3 [(2, 4), (5, 1)] [(3286051019, 1, (PC.node 3286051019 2 [(2, 1), (181, 1)] [(9077489, 1, (PC.node 9077489 3 [(2, 4), (7, 1), (81049, 1)] []))]))])) (by decide +kernel)
theorem hp_1517 : Nat.Prime (512720 ^ 2 + 1517 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884099689 3 [(2, 3), (7, 1), (31, 1), (547, 1), (276839, 1)] [])) (by decide +kernel)
theorem hp_1533 : Nat.Prime (512720 ^ 2 + 1533 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884148489 11 [(2, 3), (3, 3), (13, 1)] [(93619711, 1, (PC.node 93619711 11 [(2, 1), (3, 2), (5, 1)] [(1040219, 1, (PC.node 1040219 2 [(2, 1), (37, 1), (14057, 1)] []))]))])) (by decide +kernel)
theorem hp_1559 : Nat.Prime (512720 ^ 2 + 1559 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884228881 3 [(2, 4), (5, 1), (7, 1), (13, 1), (157, 1), (230003, 1)] [])) (by decide +kernel)
theorem hp_1569 : Nat.Prime (512720 ^ 2 + 1569 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884260161 14 [(2, 6), (3, 3), (5, 1)] [(30426419, 1, (PC.node 30426419 2 [(2, 1), (11, 2), (59, 1), (2131, 1)] []))])) (by decide +kernel)
theorem hp_1603 : Nat.Prime (512720 ^ 2 + 1603 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884368009 3 [(2, 3)] [(32860546001, 1, (PC.node 32860546001 3 [(2, 4), (5, 3), (137, 1), (119929, 1)] []))])) (by decide +kernel)
theorem hp_1613 : Nat.Prime (512720 ^ 2 + 1613 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884400169 3 [(2, 3), (13, 1)] [(2527734617, 1, (PC.node 2527734617 3 [(2, 3), (11, 1), (19, 1), (71, 1), (107, 1), (199, 1)] []))])) (by decide +kernel)
theorem hp_1617 : Nat.Prime (512720 ^ 2 + 1617 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884413089 23 [(2, 5), (3, 3), (11, 1)] [(27660397, 1, (PC.node 27660397 5 [(2, 2), (3, 1), (257, 1), (8969, 1)] []))])) (by decide +kernel)
theorem hp_1627 : Nat.Prime (512720 ^ 2 + 1627 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884445529 3 [(2, 3), (127, 1), (1409, 1), (183637, 1)] [])) (by decide +kernel)
theorem hp_1639 : Nat.Prime (512720 ^ 2 + 1639 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884484721 3 [(2, 4), (5, 1), (11, 1), (13, 1)] [(22979413, 1, (PC.node 22979413 2 [(2, 2), (3, 2), (638317, 1)] []))])) (by decide +kernel)
theorem hp_1659 : Nat.Prime (512720 ^ 2 + 1659 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884550681 41 [(2, 3), (3, 4), (5, 1)] [(81137207, 1, (PC.node 81137207 5 [(2, 1), (89, 1), (455827, 1)] []))])) (by decide +kernel)
theorem hp_1671 : Nat.Prime (512720 ^ 2 + 1671 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884590641 11 [(2, 4), (3, 3), (5, 1), (7, 1), (271, 1), (64157, 1)] [])) (by decide +kernel)
theorem hp_1701 : Nat.Prime (512720 ^ 2 + 1701 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884691801 11 [(2, 3), (3, 2), (5, 2), (17, 1), (1153, 1), (7451, 1)] [])) (by decide +kernel)
theorem hp_1707 : Nat.Prime (512720 ^ 2 + 1707 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884712249 14 [(2, 3), (3, 3), (31, 1)] [(39259963, 1, (PC.node 39259963 2 [(2, 1), (3, 2), (7, 1), (53, 1), (5879, 1)] []))])) (by decide +kernel)
theorem hp_1721 : Nat.Prime (512720 ^ 2 + 1721 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884760241 3 [(2, 4), (5, 1), (37, 1), (373, 1), (238103, 1)] [])) (by decide +kernel)
theorem hp_1733 : Nat.Prime (512720 ^ 2 + 1733 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884801689 3 [(2, 3), (17, 2)] [(113704499, 1, (PC.node 113704499 2 [(2, 1)] [(56852249, 1, (PC.node 56852249 3 [(2, 3)] [(7106531, 1, (PC.node 7106531 2 [(2, 1), (5, 1), (41, 1), (17333, 1)] []))]))]))])) (by decide +kernel)
theorem hp_1749 : Nat.Prime (512720 ^ 2 + 1749 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884857401 7 [(2, 3), (3, 3), (5, 2), (11, 1)] [(4425671, 1, (PC.node 4425671 17 [(2, 1), (5, 1), (19, 1), (23293, 1)] []))])) (by decide +kernel)
theorem hp_1763 : Nat.Prime (512720 ^ 2 + 1763 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884906569 3 [(2, 3), (149, 1), (277, 1), (796177, 1)] [])) (by decide +kernel)
theorem hp_1767 : Nat.Prime (512720 ^ 2 + 1767 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884920689 11 [(2, 4), (3, 4), (13, 1), (17, 1), (917843, 1)] [])) (by decide +kernel)
theorem hp_1777 : Nat.Prime (512720 ^ 2 + 1777 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262884956129 3 [(2, 5), (89, 1), (311, 1), (296801, 1)] [])) (by decide +kernel)
theorem hp_1793 : Nat.Prime (512720 ^ 2 + 1793 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885013249 3 [(2, 8), (11, 1), (13, 1)] [(7181081, 1, (PC.node 7181081 6 [(2, 3), (5, 1), (179527, 1)] []))])) (by decide +kernel)
theorem hp_1803 : Nat.Prime (512720 ^ 2 + 1803 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885049209 7 [(2, 3), (3, 3), (17, 1)] [(71591789, 1, (PC.node 71591789 2 [(2, 2)] [(17897947, 1, (PC.node 17897947 2 [(2, 1), (3, 1), (11, 1), (271181, 1)] []))]))])) (by decide +kernel)
theorem hp_1823 : Nat.Prime (512720 ^ 2 + 1823 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885121729 3 [(2, 6)] [(4107580027, 1, (PC.node 4107580027 2 [(2, 1), (3, 1), (11, 1)] [(62236061, 1, (PC.node 62236061 3 [(2, 2), (5, 1)] [(3111803, 1, (PC.node 3111803 2 [(2, 1)] [(1555901, 1, (PC.node 1555901 2 [(2, 2), (5, 2), (15559, 1)] []))]))]))]))])) (by decide +kernel)
theorem hp_1831 : Nat.Prime (512720 ^ 2 + 1831 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885150961 7 [(2, 4), (5, 1), (31, 1), (37, 1), (71, 1), (40351, 1)] [])) (by decide +kernel)
theorem hp_1841 : Nat.Prime (512720 ^ 2 + 1841 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885187681 3 [(2, 5), (5, 1)] [(1643032423, 1, (PC.node 1643032423 6 [(2, 1), (3, 2), (17, 1)] [(5369387, 1, (PC.node 5369387 2 [(2, 1), (11, 1), (31, 1), (7873, 1)] []))]))])) (by decide +kernel)
theorem hp_1843 : Nat.Prime (512720 ^ 2 + 1843 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885195049 3 [(2, 3), (7, 1), (59, 1)] [(79565737, 1, (PC.node 79565737 23 [(2, 3), (3, 1), (47, 1), (70537, 1)] []))])) (by decide +kernel)
theorem hp_1849 : Nat.Prime (512720 ^ 2 + 1849 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885217201 6 [(2, 4), (5, 2), (359, 1)] [(1830677, 1, (PC.node 1830677 2 [(2, 2), (457669, 1)] []))])) (by decide +kernel)
theorem hp_1861 : Nat.Prime (512720 ^ 2 + 1861 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885261721 3 [(2, 3), (5, 1), (71, 1)] [(92565233, 1, (PC.node 92565233 3 [(2, 4), (257, 1), (22511, 1)] []))])) (by decide +kernel)
theorem hp_1863 : Nat.Prime (512720 ^ 2 + 1863 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885269169 14 [(2, 4), (3, 2)] [(1825592147, 1, (PC.node 1825592147 2 [(2, 1), (7, 1)] [(130399439, 1, (PC.node 130399439 7 [(2, 1), (13, 1), (1013, 1), (4951, 1)] []))]))])) (by decide +kernel)
theorem hp_1877 : Nat.Prime (512720 ^ 2 + 1877 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885321529 3 [(2, 3), (1861, 1), (2161, 1), (8171, 1)] [])) (by decide +kernel)
theorem hp_1881 : Nat.Prime (512720 ^ 2 + 1881 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885336561 43 [(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (127, 1), (37337, 1)] [])) (by decide +kernel)
theorem hp_1891 : Nat.Prime (512720 ^ 2 + 1891 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885374281 3 [(2, 3), (5, 1)] [(6572134357, 1, (PC.node 6572134357 2 [(2, 2), (3, 1), (23, 1), (569, 1), (41849, 1)] []))])) (by decide +kernel)
theorem hp_1893 : Nat.Prime (512720 ^ 2 + 1893 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885381849 14 [(2, 3), (3, 3), (31, 1)] [(39260063, 1, (PC.node 39260063 5 [(2, 1)] [(19630031, 1, (PC.node 19630031 11 [(2, 1), (5, 1), (7, 1), (193, 1), (1453, 1)] []))]))])) (by decide +kernel)
theorem hp_1897 : Nat.Prime (512720 ^ 2 + 1897 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885397009 3 [(2, 4), (13, 1), (2273, 1), (556037, 1)] [])) (by decide +kernel)
theorem hp_1903 : Nat.Prime (512720 ^ 2 + 1903 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885419809 3 [(2, 5), (11, 1), (17, 1), (1103, 1), (39829, 1)] [])) (by decide +kernel)
theorem hp_1913 : Nat.Prime (512720 ^ 2 + 1913 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885457969 3 [(2, 4), (7, 1), (29, 1)] [(80937641, 1, (PC.node 80937641 3 [(2, 3), (5, 1), (7, 1), (289063, 1)] []))])) (by decide +kernel)
theorem hp_1917 : Nat.Prime (512720 ^ 2 + 1917 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885473289 7 [(2, 3), (3, 2), (599, 1), (1129, 1), (5399, 1)] [])) (by decide +kernel)
theorem hp_1923 : Nat.Prime (512720 ^ 2 + 1923 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885496329 31 [(2, 3), (3, 3), (7, 1), (13, 1), (163, 1), (82051, 1)] [])) (by decide +kernel)
theorem hp_1927 : Nat.Prime (512720 ^ 2 + 1927 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885511729 3 [(2, 4), (7, 1)] [(2347192069, 1, (PC.node 2347192069 7 [(2, 2), (3, 1), (13, 1), (73, 1), (79, 1), (2609, 1)] []))])) (by decide +kernel)
theorem hp_1933 : Nat.Prime (512720 ^ 2 + 1933 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885534889 3 [(2, 3), (59, 1)] [(556960879, 1, (PC.node 556960879 13 [(2, 1), (3, 2)] [(30942271, 1, (PC.node 30942271 37 [(2, 1), (3, 3), (5, 1), (114601, 1)] []))]))])) (by decide +kernel)
theorem hp_1951 : Nat.Prime (512720 ^ 2 + 1951 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885604801 3 [(2, 6), (5, 2), (7, 1), (13, 1), (31, 1), (58243, 1)] [])) (by decide +kernel)
theorem hp_1957 : Nat.Prime (512720 ^ 2 + 1957 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885628249 3 [(2, 3), (303959, 1), (108109, 1)] [])) (by decide +kernel)
theorem hp_1971 : Nat.Prime (512720 ^ 2 + 1971 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885683241 14 [(2, 3), (3, 2), (5, 1), (17, 1), (29, 1), (701, 1), (2113, 1)] [])) (by decide +kernel)
theorem hp_1973 : Nat.Prime (512720 ^ 2 + 1973 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885691129 3 [(2, 3), (17, 1), (29, 1), (71, 1), (647, 1), (1451, 1)] [])) (by decide +kernel)
theorem hp_1999 : Nat.Prime (512720 ^ 2 + 1999 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885794401 3 [(2, 5), (5, 2), (227, 1)] [(1447609, 1, (PC.node 1447609 19 [(2, 3), (3, 1), (60317, 1)] []))])) (by decide +kernel)
theorem hp_2003 : Nat.Prime (512720 ^ 2 + 2003 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885810409 3 [(2, 3), (13, 1), (71, 1)] [(35602087, 1, (PC.node 35602087 3 [(2, 1), (3, 1), (13, 1), (19, 1), (24023, 1)] []))])) (by decide +kernel)
theorem hp_2011 : Nat.Prime (512720 ^ 2 + 2011 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885842521 3 [(2, 3), (5, 1), (7, 1), (23, 1)] [(40820783, 1, (PC.node 40820783 5 [(2, 1), (509, 1), (40099, 1)] []))])) (by decide +kernel)
theorem hp_2019 : Nat.Prime (512720 ^ 2 + 2019 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885874761 7 [(2, 3), (3, 3), (5, 1), (30941, 1), (7867, 1)] [])) (by decide +kernel)
theorem hp_2037 : Nat.Prime (512720 ^ 2 + 2037 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885947769 19 [(2, 3), (3, 5), (23, 1)] [(5879539, 1, (PC.node 5879539 2 [(2, 1), (3, 2), (7, 1), (46663, 1)] []))])) (by decide +kernel)
theorem hp_2039 : Nat.Prime (512720 ^ 2 + 2039 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885955921 3 [(2, 4), (5, 1), (7, 1), (17, 1)] [(27614071, 1, (PC.node 27614071 7 [(2, 1), (3, 2), (5, 1), (11, 1), (27893, 1)] []))])) (by decide +kernel)
theorem hp_2047 : Nat.Prime (512720 ^ 2 + 2047 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262885988609 3 [(2, 8), (3457, 1), (297049, 1)] [])) (by decide +kernel)
theorem hp_2081 : Nat.Prime (512720 ^ 2 + 2081 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886128961 3 [(2, 6), (5, 1), (7, 2), (13, 1), (101, 1), (113, 2)] [])) (by decide +kernel)
theorem hp_2083 : Nat.Prime (512720 ^ 2 + 2083 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886137289 3 [(2, 3), (23, 1), (61, 1)] [(23421787, 1, (PC.node 23421787 2 [(2, 1), (3, 1)] [(3903631, 1, (PC.node 3903631 3 [(2, 1), (3, 1), (5, 1), (130121, 1)] []))]))])) (by decide +kernel)
theorem hp_2109 : Nat.Prime (512720 ^ 2 + 2109 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886246281 11 [(2, 3), (3, 3), (5, 1), (7, 1), (17, 1), (349, 1), (5861, 1)] [])) (by decide +kernel)
theorem hp_2139 : Nat.Prime (512720 ^ 2 + 2139 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886373721 7 [(2, 3), (3, 3), (5, 1), (89, 1)] [(2734981, 1, (PC.node 2734981 10 [(2, 2), (3, 1), (5, 1), (79, 1), (577, 1)] []))])) (by decide +kernel)
theorem hp_2141 : Nat.Prime (512720 ^ 2 + 2141 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886382281 3 [(2, 3), (5, 1), (17, 1), (31, 1)] [(12470891, 1, (PC.node 12470891 2 [(2, 1), (5, 1)] [(1247089, 1, (PC.node 1247089 11 [(2, 4), (3, 1), (25981, 1)] []))]))])) (by decide +kernel)
theorem hp_2147 : Nat.Prime (512720 ^ 2 + 2147 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886408009 3 [(2, 3), (7, 1), (29, 1), (6151, 1), (26317, 1)] [])) (by decide +kernel)
theorem hp_2149 : Nat.Prime (512720 ^ 2 + 2149 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886416601 3 [(2, 3), (5, 2), (23, 1), (457, 1), (125053, 1)] [])) (by decide +kernel)
theorem hp_2151 : Nat.Prime (512720 ^ 2 + 2151 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886425201 23 [(2, 4), (3, 2), (5, 2), (7, 1)] [(10432001, 1, (PC.node 10432001 6 [(2, 9), (5, 3), (163, 1)] []))])) (by decide +kernel)
theorem hp_2173 : Nat.Prime (512720 ^ 2 + 2173 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886520329 3 [(2, 3)] [(32860815041, 1, (PC.node 32860815041 11 [(2, 6), (5, 1), (17, 1), (971, 1), (6221, 1)] []))])) (by decide +kernel)
theorem hp_2177 : Nat.Prime (512720 ^ 2 + 2177 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886537729 3 [(2, 9), (17, 1), (829, 1), (36433, 1)] [])) (by decide +kernel)
theorem hp_2181 : Nat.Prime (512720 ^ 2 + 2181 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886555161 11 [(2, 3), (3, 3), (5, 1)] [(243413477, 1, (PC.node 243413477 2 [(2, 2), (467, 1), (130307, 1)] []))])) (by decide +kernel)
theorem hp_2183 : Nat.Prime (512720 ^ 2 + 2183 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886563889 3 [(2, 4), (13, 1), (127, 1)] [(9951793, 1, (PC.node 9951793 5 [(2, 4), (3, 1), (207329, 1)] []))])) (by decide +kernel)
theorem hp_2187 : Nat.Prime (512720 ^ 2 + 2187 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886581369 7 [(2, 3), (3, 2), (61, 1), (157, 1), (461, 1), (827, 1)] [])) (by decide +kernel)
theorem hp_2189 : Nat.Prime (512720 ^ 2 + 2189 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886590121 3 [(2, 3), (5, 1), (7, 1), (11, 1)] [(85352789, 1, (PC.node 85352789 2 [(2, 2), (19, 1), (131, 1), (8573, 1)] []))])) (by decide +kernel)
theorem hp_2211 : Nat.Prime (512720 ^ 2 + 2211 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886686921 7 [(2, 3), (3, 3), (5, 1), (11, 1), (13, 1), (17, 1), (100129, 1)] [])) (by decide +kernel)
theorem hp_2229 : Nat.Prime (512720 ^ 2 + 2229 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886766841 14 [(2, 3), (3, 4), (5, 1), (1667, 1), (48673, 1)] [])) (by decide +kernel)
theorem hp_2253 : Nat.Prime (512720 ^ 2 + 2253 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886874409 7 [(2, 3), (3, 4), (6607, 1), (61403, 1)] [])) (by decide +kernel)
theorem hp_2259 : Nat.Prime (512720 ^ 2 + 2259 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886901481 22 [(2, 3), (3, 2), (5, 1), (7, 1), (3967, 1), (26297, 1)] [])) (by decide +kernel)
theorem hp_2269 : Nat.Prime (512720 ^ 2 + 2269 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886946761 3 [(2, 3), (5, 1)] [(6572173669, 1, (PC.node 6572173669 2 [(2, 2), (3, 1), (457, 1)] [(1198427, 1, (PC.node 1198427 2 [(2, 1), (599213, 1)] []))]))])) (by decide +kernel)
theorem hp_2271 : Nat.Prime (512720 ^ 2 + 2271 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886955841 7 [(2, 6), (3, 3), (5, 1), (6163, 1), (4937, 1)] [])) (by decide +kernel)
theorem hp_2273 : Nat.Prime (512720 ^ 2 + 2273 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886964929 3 [(2, 6), (7, 1)] [(586801261, 1, (PC.node 586801261 10 [(2, 2), (3, 6), (5, 1), (167, 1), (241, 1)] []))])) (by decide +kernel)
theorem hp_2277 : Nat.Prime (512720 ^ 2 + 2277 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262886983129 19 [(2, 3), (3, 2), (7, 2), (11, 1), (17, 1), (398473, 1)] [])) (by decide +kernel)
theorem hp_2283 : Nat.Prime (512720 ^ 2 + 2283 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887010489 7 [(2, 3), (3, 4), (101, 1)] [(4016731, 1, (PC.node 4016731 3 [(2, 1), (3, 1), (5, 1), (191, 1), (701, 1)] []))])) (by decide +kernel)
theorem hp_2293 : Nat.Prime (512720 ^ 2 + 2293 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887056249 3 [(2, 3), (1213, 1)] [(27090587, 1, (PC.node 27090587 2 [(2, 1), (37, 1), (41, 1), (8929, 1)] []))])) (by decide +kernel)
theorem hp_2297 : Nat.Prime (512720 ^ 2 + 2297 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887074609 3 [(2, 4)] [(16430442163, 1, (PC.node 16430442163 2 [(2, 1), (3, 1), (1289, 1)] [(2124443, 1, (PC.node 2124443 2 [(2, 1), (149, 1), (7129, 1)] []))]))])) (by decide +kernel)
theorem hp_2309 : Nat.Prime (512720 ^ 2 + 2309 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887129881 3 [(2, 3), (5, 1), (61, 1), (73, 1)] [(1475899, 1, (PC.node 1475899 2 [(2, 1), (3, 1), (245983, 1)] []))])) (by decide +kernel)
theorem hp_2311 : Nat.Prime (512720 ^ 2 + 2311 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887139121 3 [(2, 4), (5, 1), (17, 2), (89, 1), (251, 1), (509, 1)] [])) (by decide +kernel)
theorem hp_2331 : Nat.Prime (512720 ^ 2 + 2331 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887231961 11 [(2, 3), (3, 2), (5, 1)] [(730242311, 1, (PC.node 730242311 13 [(2, 1), (5, 1), (7, 1), (17, 2), (36097, 1)] []))])) (by decide +kernel)
theorem hp_2333 : Nat.Prime (512720 ^ 2 + 2333 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887241289 3 [(2, 3), (7, 1), (23, 1), (2239, 1), (91159, 1)] [])) (by decide +kernel)
theorem hp_2337 : Nat.Prime (512720 ^ 2 + 2337 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887259969 7 [(2, 6), (3, 5), (907, 1), (18637, 1)] [])) (by decide +kernel)
theorem hp_2343 : Nat.Prime (512720 ^ 2 + 2343 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887288049 31 [(2, 4), (3, 3), (7, 1), (11, 1)] [(7903057, 1, (PC.node 7903057 5 [(2, 4), (3, 1), (7, 1), (43, 1), (547, 1)] []))])) (by decide +kernel)
theorem hp_2351 : Nat.Prime (512720 ^ 2 + 2351 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887325601 7 [(2, 5), (5, 2), (463, 1), (709739, 1)] [])) (by decide +kernel)
theorem hp_2357 : Nat.Prime (512720 ^ 2 + 2357 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887353849 3 [(2, 3), (7, 1), (1567, 1)] [(2995799, 1, (PC.node 2995799 7 [(2, 1), (13, 1), (115223, 1)] []))])) (by decide +kernel)
theorem hp_2367 : Nat.Prime (512720 ^ 2 + 2367 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887401089 7 [(2, 7), (3, 2), (13, 2), (479, 1), (2819, 1)] [])) (by decide +kernel)
theorem hp_2369 : Nat.Prime (512720 ^ 2 + 2369 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887410561 3 [(2, 7), (5, 1)] [(410761579, 1, (PC.node 410761579 2 [(2, 1), (3, 1), (2399, 1), (28537, 1)] []))])) (by decide +kernel)
theorem hp_2383 : Nat.Prime (512720 ^ 2 + 2383 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887477089 3 [(2, 5), (10639, 1), (772181, 1)] [])) (by decide +kernel)
theorem hp_2391 : Nat.Prime (512720 ^ 2 + 2391 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887515281 7 [(2, 4), (3, 4), (5, 1), (13, 1)] [(3120697, 1, (PC.node 3120697 10 [(2, 3), (3, 2), (89, 1), (487, 1)] []))])) (by decide +kernel)
theorem hp_2411 : Nat.Prime (512720 ^ 2 + 2411 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887611321 3 [(2, 3), (5, 1), (97, 1), (4217, 1), (16067, 1)] [])) (by decide +kernel)
theorem hp_2427 : Nat.Prime (512720 ^ 2 + 2427 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887688729 11 [(2, 3), (3, 3), (7, 2), (491, 1), (50587, 1)] [])) (by decide +kernel)
theorem hp_2429 : Nat.Prime (512720 ^ 2 + 2429 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887698441 3 [(2, 3), (5, 1), (71, 1), (179, 1), (517129, 1)] [])) (by decide +kernel)
theorem hp_2441 : Nat.Prime (512720 ^ 2 + 2441 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887756881 3 [(2, 4), (5, 1), (7, 1)] [(469442423, 1, (PC.node 469442423 5 [(2, 1)] [(234721211, 1, (PC.node 234721211 2 [(2, 1), (5, 1), (17, 1), (23, 1), (173, 1), (347, 1)] []))]))])) (by decide +kernel)
theorem hp_2447 : Nat.Prime (512720 ^ 2 + 2447 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887786209 6 [(2, 5), (17, 1), (31, 1)] [(15588697, 1, (PC.node 15588697 5 [(2, 3), (3, 1), (649529, 1)] []))])) (by decide +kernel)
theorem hp_2449 : Nat.Prime (512720 ^ 2 + 2449 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887796001 3 [(2, 5), (5, 3), (17, 1), (61, 1), (63377, 1)] [])) (by decide +kernel)
theorem hp_2451 : Nat.Prime (512720 ^ 2 + 2451 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887805801 7 [(2, 3), (3, 3), (5, 2), (23, 1), (31, 1), (68279, 1)] [])) (by decide +kernel)
theorem hp_2473 : Nat.Prime (512720 ^ 2 + 2473 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887914129 3 [(2, 4), (7, 2)] [(335316217, 1, (PC.node 335316217 7 [(2, 3), (3, 1), (1019, 1), (13711, 1)] []))])) (by decide +kernel)
theorem hp_2479 : Nat.Prime (512720 ^ 2 + 2479 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887943841 3 [(2, 5), (5, 1)] [(1643049649, 1, (PC.node 1643049649 7 [(2, 4), (3, 2), (89, 1), (128203, 1)] []))])) (by decide +kernel)
theorem hp_2481 : Nat.Prime (512720 ^ 2 + 2481 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262887953761 14 [(2, 5), (3, 3), (5, 1), (17, 1)] [(3579629, 1, (PC.node 3579629 2 [(2, 2), (13, 1), (23, 1), (41, 1), (73, 1)] []))])) (by decide +kernel)
theorem hp_2493 : Nat.Prime (512720 ^ 2 + 2493 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888013449 7 [(2, 3), (3, 2), (29, 1), (10267, 1), (12263, 1)] [])) (by decide +kernel)
theorem hp_2497 : Nat.Prime (512720 ^ 2 + 2497 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888033409 6 [(2, 7), (7, 1), (11, 1), (13, 1), (23, 1), (37, 1), (2411, 1)] [])) (by decide +kernel)
theorem hp_2507 : Nat.Prime (512720 ^ 2 + 2507 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888083449 3 [(2, 3), (53197, 1), (617723, 1)] [])) (by decide +kernel)
theorem hp_2511 : Nat.Prime (512720 ^ 2 + 2511 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888103521 19 [(2, 5), (3, 2), (5, 1), (7, 1)] [(26080169, 1, (PC.node 26080169 3 [(2, 3)] [(3260021, 1, (PC.node 3260021 2 [(2, 2), (5, 1), (19, 1), (23, 1), (373, 1)] []))]))])) (by decide +kernel)
theorem hp_2517 : Nat.Prime (512720 ^ 2 + 2517 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888133689 35 [(2, 3), (3, 3), (17, 1), (23, 1), (631, 1), (4933, 1)] [])) (by decide +kernel)
theorem hp_2577 : Nat.Prime (512720 ^ 2 + 2577 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888439329 11 [(2, 5), (3, 4), (311, 1), (326119, 1)] [])) (by decide +kernel)
theorem hp_2591 : Nat.Prime (512720 ^ 2 + 2591 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888511681 6 [(2, 6), (5, 1)] [(821526599, 1, (PC.node 821526599 11 [(2, 1), (17, 1), (19, 1), (31, 1), (41023, 1)] []))])) (by decide +kernel)
theorem hp_2597 : Nat.Prime (512720 ^ 2 + 2597 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888542809 3 [(2, 3)] [(32861067851, 1, (PC.node 32861067851 2 [(2, 1), (5, 2), (13, 1)] [(50555489, 1, (PC.node 50555489 3 [(2, 5), (757, 1), (2087, 1)] []))]))])) (by decide +kernel)
theorem hp_2607 : Nat.Prime (512720 ^ 2 + 2607 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888594849 7 [(2, 5), (3, 4), (11, 1)] [(9220279, 1, (PC.node 9220279 6 [(2, 1), (3, 1), (211, 1), (7283, 1)] []))])) (by decide +kernel)
theorem hp_2611 : Nat.Prime (512720 ^ 2 + 2611 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888615721 3 [(2, 3), (5, 1), (29, 1), (547, 1), (414311, 1)] [])) (by decide +kernel)
theorem hp_2617 : Nat.Prime (512720 ^ 2 + 2617 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888647089 3 [(2, 4), (17, 1), (128473, 1), (7523, 1)] [])) (by decide +kernel)
theorem hp_2647 : Nat.Prime (512720 ^ 2 + 2647 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888805009 3 [(2, 4), (317, 1), (3727, 1), (13907, 1)] [])) (by decide +kernel)
theorem hp_2659 : Nat.Prime (512720 ^ 2 + 2659 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888868681 7 [(2, 3), (5, 1)] [(6572221717, 1, (PC.node 6572221717 5 [(2, 2), (3, 1), (641, 1), (854423, 1)] []))])) (by decide +kernel)
theorem hp_2661 : Nat.Prime (512720 ^ 2 + 2661 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888879321 21 [(2, 3), (3, 5), (5, 1)] [(27046181, 1, (PC.node 27046181 2 [(2, 2), (5, 1), (7, 1), (61, 1), (3167, 1)] []))])) (by decide +kernel)
theorem hp_2671 : Nat.Prime (512720 ^ 2 + 2671 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262888932641 3 [(2, 5), (5, 1), (383, 1)] [(4289963, 1, (PC.node 4289963 2 [(2, 1), (71, 1), (30211, 1)] []))])) (by decide +kernel)
theorem hp_2687 : Nat.Prime (512720 ^ 2 + 2687 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889018369 3 [(2, 10), (17, 1), (101, 1), (149521, 1)] [])) (by decide +kernel)
theorem hp_2699 : Nat.Prime (512720 ^ 2 + 2699 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889083001 3 [(2, 3), (5, 3), (31, 1)] [(8480293, 1, (PC.node 8480293 2 [(2, 2), (3, 1), (751, 1), (941, 1)] []))])) (by decide +kernel)
theorem hp_2711 : Nat.Prime (512720 ^ 2 + 2711 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889147921 6 [(2, 4), (5, 1), (7, 1), (4673, 1), (100459, 1)] [])) (by decide +kernel)
theorem hp_2721 : Nat.Prime (512720 ^ 2 + 2721 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889202241 22 [(2, 6), (3, 3), (5, 1), (7, 2), (17, 1), (36527, 1)] [])) (by decide +kernel)
theorem hp_2729 : Nat.Prime (512720 ^ 2 + 2729 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889245841 3 [(2, 4), (5, 1), (13, 1)] [(252778121, 1, (PC.node 252778121 3 [(2, 3), (5, 1), (7, 1), (41, 1), (97, 1), (227, 1)] []))])) (by decide +kernel)
theorem hp_2731 : Nat.Prime (512720 ^ 2 + 2731 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889256761 3 [(2, 3), (5, 1), (13, 1)] [(505556263, 1, (PC.node 505556263 3 [(2, 1), (3, 3)] [(9362153, 1, (PC.node 9362153 3 [(2, 3), (787, 1), (1487, 1)] []))]))])) (by decide +kernel)
theorem hp_2753 : Nat.Prime (512720 ^ 2 + 2753 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889377409 3 [(2, 7), (7, 1), (17, 1)] [(17259019, 1, (PC.node 17259019 3 [(2, 1), (3, 1), (7, 1), (410929, 1)] []))])) (by decide +kernel)
theorem hp_2773 : Nat.Prime (512720 ^ 2 + 2773 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889487929 3 [(2, 3), (23, 1)] [(1428747217, 1, (PC.node 1428747217 5 [(2, 4), (3, 1), (13, 1)] [(2289659, 1, (PC.node 2289659 6 [(2, 1), (7, 1), (67, 1), (2441, 1)] []))]))])) (by decide +kernel)
theorem hp_2777 : Nat.Prime (512720 ^ 2 + 2777 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889510129 3 [(2, 4), (7, 1), (349, 1), (1319, 1), (5099, 1)] [])) (by decide +kernel)
theorem hp_2781 : Nat.Prime (512720 ^ 2 + 2781 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889532361 23 [(2, 3), (3, 2), (5, 1), (7, 1), (13, 1)] [(8024711, 1, (PC.node 8024711 7 [(2, 1), (5, 1), (802471, 1)] []))])) (by decide +kernel)
theorem hp_2791 : Nat.Prime (512720 ^ 2 + 2791 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889588081 3 [(2, 4), (5, 1), (7, 1), (2909, 1), (161377, 1)] [])) (by decide +kernel)
theorem hp_2797 : Nat.Prime (512720 ^ 2 + 2797 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889621609 3 [(2, 3), (61, 1), (829, 1), (649829, 1)] [])) (by decide +kernel)
theorem hp_2803 : Nat.Prime (512720 ^ 2 + 2803 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889655209 3 [(2, 3)] [(32861206901, 1, (PC.node 32861206901 2 [(2, 2), (5, 2), (71, 1), (1181, 1), (3919, 1)] []))])) (by decide +kernel)
theorem hp_2811 : Nat.Prime (512720 ^ 2 + 2811 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889700121 7 [(2, 3), (3, 3), (5, 1)] [(243416389, 1, (PC.node 243416389 2 [(2, 2), (3, 1)] [(20284699, 1, (PC.node 20284699 15 [(2, 1), (3, 1), (7, 1), (163, 1), (2963, 1)] []))]))])) (by decide +kernel)
theorem hp_2819 : Nat.Prime (512720 ^ 2 + 2819 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889745161 3 [(2, 3), (5, 1), (7, 2), (23, 2), (31, 1), (8179, 1)] [])) (by decide +kernel)
theorem hp_2829 : Nat.Prime (512720 ^ 2 + 2829 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889801641 14 [(2, 3), (3, 3), (5, 1), (4463, 1), (54541, 1)] [])) (by decide +kernel)
theorem hp_2843 : Nat.Prime (512720 ^ 2 + 2843 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262889881049 3 [(2, 3), (29, 1), (193, 1)] [(5871223, 1, (PC.node 5871223 3 [(2, 1), (3, 2), (7, 1), (17, 1), (2741, 1)] []))])) (by decide +kernel)
theorem hp_2891 : Nat.Prime (512720 ^ 2 + 2891 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890156281 3 [(2, 3), (5, 1), (17, 2), (113, 1), (201251, 1)] [])) (by decide +kernel)
theorem hp_2897 : Nat.Prime (512720 ^ 2 + 2897 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890191009 3 [(2, 5), (127, 1)] [(64687547, 1, (PC.node 64687547 2 [(2, 1), (7, 2), (11, 1), (23, 1), (2609, 1)] []))])) (by decide +kernel)
theorem hp_2917 : Nat.Prime (512720 ^ 2 + 2917 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890307289 3 [(2, 3), (7, 2), (1831, 1), (366269, 1)] [])) (by decide +kernel)
theorem hp_2937 : Nat.Prime (512720 ^ 2 + 2937 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890424369 7 [(2, 4), (3, 3), (11, 1), (13, 1), (61, 1), (69763, 1)] [])) (by decide +kernel)
theorem hp_2957 : Nat.Prime (512720 ^ 2 + 2957 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890542249 3 [(2, 3), (17, 1), (23, 1), (29, 1)] [(2898079, 1, (PC.node 2898079 6 [(2, 1), (3, 1), (71, 1), (6803, 1)] []))])) (by decide +kernel)
theorem hp_2959 : Nat.Prime (512720 ^ 2 + 2959 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890554081 3 [(2, 5), (5, 1), (7, 1), (11, 1), (17, 1), (29, 1), (43283, 1)] [])) (by decide +kernel)
theorem hp_2993 : Nat.Prime (512720 ^ 2 + 2993 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890756449 3 [(2, 5), (17, 1), (97, 1)] [(4982011, 1, (PC.node 4982011 10 [(2, 1), (3, 1), (5, 1), (11, 1), (31, 1), (487, 1)] []))])) (by decide +kernel)
theorem hp_2997 : Nat.Prime (512720 ^ 2 + 2997 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890780409 7 [(2, 3), (3, 2), (71, 1)] [(51426209, 1, (PC.node 51426209 3 [(2, 5)] [(1607069, 1, (PC.node 1607069 2 [(2, 2), (383, 1), (1049, 1)] []))]))])) (by decide +kernel)
theorem hp_2999 : Nat.Prime (512720 ^ 2 + 2999 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890792401 3 [(2, 4), (5, 2)] [(657226981, 1, (PC.node 657226981 6 [(2, 2), (3, 3), (5, 1), (331, 1), (3677, 1)] []))])) (by decide +kernel)
theorem hp_3019 : Nat.Prime (512720 ^ 2 + 3019 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890912761 3 [(2, 3), (5, 1), (7, 1)] [(938896117, 1, (PC.node 938896117 2 [(2, 2), (3, 1)] [(78241343, 1, (PC.node 78241343 5 [(2, 1)] [(39120671, 1, (PC.node 39120671 13 [(2, 1), (5, 1), (269, 1), (14543, 1)] []))]))]))])) (by decide +kernel)
theorem hp_3021 : Nat.Prime (512720 ^ 2 + 3021 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262890924841 7 [(2, 3), (3, 3), (5, 1), (97, 1), (311, 1), (8069, 1)] [])) (by decide +kernel)
theorem hp_3037 : Nat.Prime (512720 ^ 2 + 3037 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891021769 3 [(2, 3)] [(32861377721, 1, (PC.node 32861377721 3 [(2, 3), (5, 1)] [(821534443, 1, (PC.node 821534443 2 [(2, 1), (3, 1), (173, 1), (659, 1), (1201, 1)] []))]))])) (by decide +kernel)
theorem hp_3053 : Nat.Prime (512720 ^ 2 + 3053 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891119209 3 [(2, 3), (37, 1)] [(888145673, 1, (PC.node 888145673 3 [(2, 3), (227, 1), (233, 1), (2099, 1)] []))])) (by decide +kernel)
theorem hp_3059 : Nat.Prime (512720 ^ 2 + 3059 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891155881 3 [(2, 3), (5, 1), (17, 1), (61, 1), (317, 1), (19993, 1)] [])) (by decide +kernel)
theorem hp_3061 : Nat.Prime (512720 ^ 2 + 3061 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891168121 3 [(2, 3), (5, 1), (7, 2), (17, 1)] [(7889891, 1, (PC.node 7889891 2 [(2, 1), (5, 1), (47, 1), (16787, 1)] []))])) (by decide +kernel)
theorem hp_3073 : Nat.Prime (512720 ^ 2 + 3073 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891241729 3 [(2, 8), (29, 1)] [(35410997, 1, (PC.node 35410997 2 [(2, 2), (53, 1), (167033, 1)] []))])) (by decide +kernel)
theorem hp_3083 : Nat.Prime (512720 ^ 2 + 3083 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891303289 3 [(2, 3), (5189, 1)] [(6332899, 1, (PC.node 6332899 2 [(2, 1), (3, 1), (11, 3), (13, 1), (61, 1)] []))])) (by decide +kernel)
theorem hp_3123 : Nat.Prime (512720 ^ 2 + 3123 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891551529 14 [(2, 3), (3, 2), (4817, 1), (757997, 1)] [])) (by decide +kernel)
theorem hp_3139 : Nat.Prime (512720 ^ 2 + 3139 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891651721 3 [(2, 3), (5, 1), (71, 1)] [(92567483, 1, (PC.node 92567483 2 [(2, 1), (7, 1), (17, 1), (131, 1), (2969, 1)] []))])) (by decide +kernel)
theorem hp_3157 : Nat.Prime (512720 ^ 2 + 3157 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891765049 3 [(2, 3), (11, 1), (16339, 1), (182839, 1)] [])) (by decide +kernel)
theorem hp_3177 : Nat.Prime (512720 ^ 2 + 3177 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891891729 14 [(2, 4), (3, 2), (359, 1)] [(5085343, 1, (PC.node 5085343 3 [(2, 1), (3, 4), (31391, 1)] []))])) (by decide +kernel)
theorem hp_3183 : Nat.Prime (512720 ^ 2 + 3183 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891929889 11 [(2, 5), (3, 3), (7, 1)] [(43467581, 1, (PC.node 43467581 2 [(2, 2), (5, 1), (13, 1), (31, 1), (5393, 1)] []))])) (by decide +kernel)
theorem hp_3189 : Nat.Prime (512720 ^ 2 + 3189 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262891968121 11 [(2, 3), (3, 3), (5, 1), (29, 1)] [(8393741, 1, (PC.node 8393741 2 [(2, 2), (5, 1), (419687, 1)] []))])) (by decide +kernel)
theorem hp_3197 : Nat.Prime (512720 ^ 2 + 3197 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892019209 3 [(2, 3), (7, 1), (13, 1), (17, 1), (3877, 1), (5479, 1)] [])) (by decide +kernel)
theorem hp_3199 : Nat.Prime (512720 ^ 2 + 3199 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892032001 3 [(2, 12), (5, 3), (13, 1), (127, 1), (311, 1)] [])) (by decide +kernel)
theorem hp_3203 : Nat.Prime (512720 ^ 2 + 3203 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892057609 3 [(2, 3), (647, 1)] [(50790583, 1, (PC.node 50790583 3 [(2, 1), (3, 2)] [(2821699, 1, (PC.node 2821699 3 [(2, 1), (3, 2), (11, 1), (14251, 1)] []))]))])) (by decide +kernel)
theorem hp_3207 : Nat.Prime (512720 ^ 2 + 3207 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892083249 7 [(2, 4), (3, 3), (23, 1), (89, 1), (271, 1), (1097, 1)] [])) (by decide +kernel)
theorem hp_3231 : Nat.Prime (512720 ^ 2 + 3231 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892237761 21 [(2, 6), (3, 2), (5, 1), (17, 1), (59, 1), (91009, 1)] [])) (by decide +kernel)
theorem hp_3233 : Nat.Prime (512720 ^ 2 + 3233 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892250689 3 [(2, 6), (23, 1)] [(178595279, 1, (PC.node 178595279 7 [(2, 1), (31, 1)] [(2880569, 1, (PC.node 2880569 3 [(2, 3), (360071, 1)] []))]))])) (by decide +kernel)
theorem hp_3259 : Nat.Prime (512720 ^ 2 + 3259 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892419481 3 [(2, 3), (5, 1), (59, 1)] [(111395093, 1, (PC.node 111395093 2 [(2, 2), (271, 1), (102763, 1)] []))])) (by decide +kernel)
theorem hp_3267 : Nat.Prime (512720 ^ 2 + 3267 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892471689 23 [(2, 3), (3, 2), (7, 1), (11, 1), (647, 1), (73291, 1)] [])) (by decide +kernel)
theorem hp_3271 : Nat.Prime (512720 ^ 2 + 3271 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892497841 3 [(2, 4), (5, 1), (7, 1), (241, 1), (691, 1), (2819, 1)] [])) (by decide +kernel)
theorem hp_3307 : Nat.Prime (512720 ^ 2 + 3307 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892734649 3 [(2, 3), (29, 1)] [(1133158339, 1, (PC.node 1133158339 10 [(2, 1), (3, 2), (13, 1), (53, 1), (91369, 1)] []))])) (by decide +kernel)
theorem hp_3313 : Nat.Prime (512720 ^ 2 + 3313 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892774369 3 [(2, 5), (7, 1)] [(1173628457, 1, (PC.node 1173628457 3 [(2, 3), (7, 1), (11, 1), (13, 1), (17, 1), (37, 1), (233, 1)] []))])) (by decide +kernel)
theorem hp_3323 : Nat.Prime (512720 ^ 2 + 3323 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262892840729 3 [(2, 3), (7, 1)] [(4694515013, 1, (PC.node 4694515013 2 [(2, 2), (11, 1), (29, 1)] [(3679087, 1, (PC.node 3679087 3 [(2, 1), (3, 1), (613181, 1)] []))]))])) (by decide +kernel)
theorem hp_3347 : Nat.Prime (512720 ^ 2 + 3347 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893000809 3 [(2, 3), (45841, 1), (716861, 1)] [])) (by decide +kernel)
theorem hp_3357 : Nat.Prime (512720 ^ 2 + 3357 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893067849 7 [(2, 3), (3, 2), (24547, 1), (148747, 1)] [])) (by decide +kernel)
theorem hp_3363 : Nat.Prime (512720 ^ 2 + 3363 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893108169 7 [(2, 3), (3, 4), (29, 2), (482401, 1)] [])) (by decide +kernel)
theorem hp_3387 : Nat.Prime (512720 ^ 2 + 3387 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893270169 7 [(2, 3), (3, 4)] [(405699491, 1, (PC.node 405699491 2 [(2, 1), (5, 1), (7, 1), (103, 1), (56269, 1)] []))])) (by decide +kernel)
theorem hp_3407 : Nat.Prime (512720 ^ 2 + 3407 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893406049 3 [(2, 5), (7, 2), (13, 1), (61, 1), (211427, 1)] [])) (by decide +kernel)
theorem hp_3411 : Nat.Prime (512720 ^ 2 + 3411 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893433321 22 [(2, 3), (3, 2), (5, 1), (7, 1), (6263, 1), (16657, 1)] [])) (by decide +kernel)
theorem hp_3431 : Nat.Prime (512720 ^ 2 + 3431 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893570161 3 [(2, 4), (5, 1), (13, 1)] [(252782279, 1, (PC.node 252782279 7 [(2, 1), (7, 2)] [(2579411, 1, (PC.node 2579411 2 [(2, 1), (5, 1), (17, 1), (15173, 1)] []))]))])) (by decide +kernel)
theorem hp_3441 : Nat.Prime (512720 ^ 2 + 3441 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893638881 14 [(2, 5), (3, 4), (5, 1)] [(20285003, 1, (PC.node 20285003 2 [(2, 1)] [(10142501, 1, (PC.node 10142501 2 [(2, 2), (5, 4), (4057, 1)] []))]))])) (by decide +kernel)
theorem hp_3453 : Nat.Prime (512720 ^ 2 + 3453 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893721609 11 [(2, 3), (3, 3), (7, 2), (127, 1), (195581, 1)] [])) (by decide +kernel)
theorem hp_3463 : Nat.Prime (512720 ^ 2 + 3463 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893790769 3 [(2, 4), (7, 1), (23, 1), (521, 1), (195883, 1)] [])) (by decide +kernel)
theorem hp_3477 : Nat.Prime (512720 ^ 2 + 3477 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893887929 22 [(2, 3), (3, 3), (7, 1), (73, 1), (241, 1), (9883, 1)] [])) (by decide +kernel)
theorem hp_3481 : Nat.Prime (512720 ^ 2 + 3481 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893915761 3 [(2, 4), (5, 1), (7, 1), (29, 1), (503, 1), (32183, 1)] [])) (by decide +kernel)
theorem hp_3489 : Nat.Prime (512720 ^ 2 + 3489 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262893971521 53 [(2, 6), (3, 3), (5, 1), (6619, 1), (4597, 1)] [])) (by decide +kernel)
theorem hp_3503 : Nat.Prime (512720 ^ 2 + 3503 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894069409 3 [(2, 5), (17, 1), (179, 1), (577, 1), (4679, 1)] [])) (by decide +kernel)
theorem hp_3513 : Nat.Prime (512720 ^ 2 + 3513 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894139569 7 [(2, 4), (3, 3)] [(608551249, 1, (PC.node 608551249 7 [(2, 4), (3, 1)] [(12678151, 1, (PC.node 12678151 3 [(2, 1), (3, 1), (5, 2), (84521, 1)] []))]))])) (by decide +kernel)
theorem hp_3517 : Nat.Prime (512720 ^ 2 + 3517 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894167689 3 [(2, 3), (23531, 1)] [(1396531, 1, (PC.node 1396531 2 [(2, 1), (3, 2), (5, 1), (59, 1), (263, 1)] []))])) (by decide +kernel)
theorem hp_3527 : Nat.Prime (512720 ^ 2 + 3527 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894238129 3 [(2, 4), (45433, 1), (361651, 1)] [])) (by decide +kernel)
theorem hp_3529 : Nat.Prime (512720 ^ 2 + 3529 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894252241 3 [(2, 4), (5, 1), (23, 2), (61, 1), (101837, 1)] [])) (by decide +kernel)
theorem hp_3557 : Nat.Prime (512720 ^ 2 + 3557 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894450649 3 [(2, 3), (89, 1), (283, 1)] [(1304713, 1, (PC.node 1304713 5 [(2, 3), (3, 2), (18121, 1)] []))])) (by decide +kernel)
theorem hp_3569 : Nat.Prime (512720 ^ 2 + 3569 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894536161 3 [(2, 5), (5, 1), (17, 1), (113, 1), (855331, 1)] [])) (by decide +kernel)
theorem hp_3591 : Nat.Prime (512720 ^ 2 + 3591 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894693681 31 [(2, 4), (3, 2), (5, 1)] [(365131519, 1, (PC.node 365131519 6 [(2, 1), (3, 1), (29, 1), (383, 1), (5479, 1)] []))])) (by decide +kernel)
theorem hp_3593 : Nat.Prime (512720 ^ 2 + 3593 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894708049 3 [(2, 4), (7, 1)] [(2347274179, 1, (PC.node 2347274179 2 [(2, 1), (3, 2), (167, 1), (277, 1), (2819, 1)] []))])) (by decide +kernel)
theorem hp_3603 : Nat.Prime (512720 ^ 2 + 3603 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894780009 23 [(2, 3), (3, 4), (7, 2), (17, 1), (97, 1), (5021, 1)] [])) (by decide +kernel)
theorem hp_3607 : Nat.Prime (512720 ^ 2 + 3607 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894808849 3 [(2, 4), (7, 1), (37, 2)] [(1714591, 1, (PC.node 1714591 6 [(2, 1), (3, 2), (5, 1), (19051, 1)] []))])) (by decide +kernel)
theorem hp_3609 : Nat.Prime (512720 ^ 2 + 3609 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894823281 7 [(2, 4), (3, 2), (5, 1)] [(365131699, 1, (PC.node 365131699 3 [(2, 1), (3, 1)] [(60855283, 1, (PC.node 60855283 5 [(2, 1), (3, 2), (29, 1), (73, 1), (1597, 1)] []))]))])) (by decide +kernel)
theorem hp_3619 : Nat.Prime (512720 ^ 2 + 3619 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894895561 3 [(2, 3), (5, 1), (11, 1), (163, 1)] [(3665573, 1, (PC.node 3665573 2 [(2, 2), (137, 1), (6689, 1)] []))])) (by decide +kernel)
theorem hp_3629 : Nat.Prime (512720 ^ 2 + 3629 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894968041 6 [(2, 3), (5, 1), (31, 1)] [(212012071, 1, (PC.node 212012071 17 [(2, 1), (3, 1), (5, 1), (19, 1), (371951, 1)] []))])) (by decide +kernel)
theorem hp_3631 : Nat.Prime (512720 ^ 2 + 3631 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894982561 3 [(2, 5), (5, 1), (7, 1), (9397, 1), (24979, 1)] [])) (by decide +kernel)
theorem hp_3633 : Nat.Prime (512720 ^ 2 + 3633 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262894997089 11 [(2, 5), (3, 5)] [(33808513, 1, (PC.node 33808513 5 [(2, 7), (3, 1), (17, 1), (5179, 1)] []))])) (by decide +kernel)
theorem hp_3639 : Nat.Prime (512720 ^ 2 + 3639 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895040721 7 [(2, 4), (3, 3), (5, 1), (13, 1), (17, 1), (691, 1), (797, 1)] [])) (by decide +kernel)
theorem hp_3647 : Nat.Prime (512720 ^ 2 + 3647 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895099009 3 [(2, 7), (23, 1)] [(89298607, 1, (PC.node 89298607 3 [(2, 1), (3, 1), (409, 1), (36389, 1)] []))])) (by decide +kernel)
theorem hp_3657 : Nat.Prime (512720 ^ 2 + 3657 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895172049 7 [(2, 4), (3, 5), (179, 1), (377749, 1)] [])) (by decide +kernel)
theorem hp_3659 : Nat.Prime (512720 ^ 2 + 3659 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895186681 3 [(2, 3), (5, 1), (7, 1), (127, 1)] [(7393003, 1, (PC.node 7393003 3 [(2, 1), (3, 1), (73, 1), (16879, 1)] []))])) (by decide +kernel)
theorem hp_3667 : Nat.Prime (512720 ^ 2 + 3667 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895245289 6 [(2, 3), (13, 1), (23, 1), (3881, 1), (28319, 1)] [])) (by decide +kernel)
theorem hp_3669 : Nat.Prime (512720 ^ 2 + 3669 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895259961 14 [(2, 3), (3, 3), (5, 1), (61, 1), (1151, 1), (3467, 1)] [])) (by decide +kernel)
theorem hp_3713 : Nat.Prime (512720 ^ 2 + 3713 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895584769 3 [(2, 9), (23, 1), (29, 1), (251, 1), (3067, 1)] [])) (by decide +kernel)
theorem hp_3733 : Nat.Prime (512720 ^ 2 + 3733 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895733689 3 [(2, 3), (7, 1), (197641, 1), (23753, 1)] [])) (by decide +kernel)
theorem hp_3747 : Nat.Prime (512720 ^ 2 + 3747 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262895838409 11 [(2, 3), (3, 3), (7, 2)] [(24838987, 1, (PC.node 24838987 2 [(2, 1), (3, 1)] [(4139831, 1, (PC.node 4139831 11 [(2, 1), (5, 1), (53, 1), (73, 1), (107, 1)] []))]))])) (by decide +kernel)
theorem hp_3779 : Nat.Prime (512720 ^ 2 + 3779 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896079241 6 [(2, 3), (5, 1), (157, 1), (631, 1), (66343, 1)] [])) (by decide +kernel)
theorem hp_3789 : Nat.Prime (512720 ^ 2 + 3789 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896154921 31 [(2, 3), (3, 2), (5, 1), (7, 1), (1531, 1), (68141, 1)] [])) (by decide +kernel)
theorem hp_3793 : Nat.Prime (512720 ^ 2 + 3793 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896185249 3 [(2, 5), (37, 1), (631, 1), (351887, 1)] [])) (by decide +kernel)
theorem hp_3807 : Nat.Prime (512720 ^ 2 + 3807 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896291649 11 [(2, 6), (3, 2), (17, 1)] [(26848069, 1, (PC.node 26848069 2 [(2, 2), (3, 1), (13, 1), (59, 1), (2917, 1)] []))])) (by decide +kernel)
theorem hp_3813 : Nat.Prime (512720 ^ 2 + 3813 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896337369 11 [(2, 3), (3, 3), (7, 1)] [(173873239, 1, (PC.node 173873239 3 [(2, 1), (3, 1), (7, 1), (11, 1), (23, 1), (16363, 1)] []))])) (by decide +kernel)
theorem hp_3833 : Nat.Prime (512720 ^ 2 + 3833 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896490289 3 [(2, 4), (2609, 1)] [(6297827, 1, (PC.node 6297827 2 [(2, 1)] [(3148913, 1, (PC.node 3148913 3 [(2, 4), (13, 1), (15139, 1)] []))]))])) (by decide +kernel)
theorem hp_3841 : Nat.Prime (512720 ^ 2 + 3841 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896551681 3 [(2, 8), (5, 1), (7, 1), (17, 1), (827, 1), (2087, 1)] [])) (by decide +kernel)
theorem hp_3851 : Nat.Prime (512720 ^ 2 + 3851 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896628601 3 [(2, 3), (5, 2), (23, 1)] [(57151441, 1, (PC.node 57151441 22 [(2, 4), (3, 3), (5, 1), (26459, 1)] []))])) (by decide +kernel)
theorem hp_3869 : Nat.Prime (512720 ^ 2 + 3869 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896767561 21 [(2, 3), (5, 1), (7, 1)] [(938917027, 1, (PC.node 938917027 3 [(2, 1), (3, 2), (31, 1), (47, 1), (35801, 1)] []))])) (by decide +kernel)
theorem hp_3873 : Nat.Prime (512720 ^ 2 + 3873 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896798529 11 [(2, 6), (3, 4), (7, 1), (13, 1), (31, 1), (17977, 1)] [])) (by decide +kernel)
theorem hp_3897 : Nat.Prime (512720 ^ 2 + 3897 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262896985009 11 [(2, 4), (3, 2), (7, 2), (23, 1)] [(1619941, 1, (PC.node 1619941 2 [(2, 2), (3, 1), (5, 1), (7, 2), (19, 1), (29, 1)] []))])) (by decide +kernel)
theorem hp_3899 : Nat.Prime (512720 ^ 2 + 3899 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897000601 6 [(2, 3), (5, 2), (13, 1), (101, 1), (149, 1), (6719, 1)] [])) (by decide +kernel)
theorem hp_3901 : Nat.Prime (512720 ^ 2 + 3901 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897016201 3 [(2, 3), (5, 2), (7, 1), (13, 1), (563, 1), (25657, 1)] [])) (by decide +kernel)
theorem hp_3919 : Nat.Prime (512720 ^ 2 + 3919 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897156961 3 [(2, 5), (5, 1), (89, 1)] [(18461879, 1, (PC.node 18461879 7 [(2, 1), (43, 1), (214673, 1)] []))])) (by decide +kernel)
theorem hp_3933 : Nat.Prime (512720 ^ 2 + 3933 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897266889 14 [(2, 3), (3, 2), (16979, 1), (215051, 1)] [])) (by decide +kernel)
theorem hp_3937 : Nat.Prime (512720 ^ 2 + 3937 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897298369 3 [(2, 6), (2099, 1)] [(1957013, 1, (PC.node 1957013 2 [(2, 2), (41, 1), (11933, 1)] []))])) (by decide +kernel)
theorem hp_3943 : Nat.Prime (512720 ^ 2 + 3943 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897345649 3 [(2, 4), (7, 2), (17, 1), (23, 1), (29, 1), (29573, 1)] [])) (by decide +kernel)
theorem hp_3953 : Nat.Prime (512720 ^ 2 + 3953 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897424609 6 [(2, 5), (7, 1), (13, 1), (547, 1), (165047, 1)] [])) (by decide +kernel)
theorem hp_3957 : Nat.Prime (512720 ^ 2 + 3957 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897456249 11 [(2, 3), (3, 6), (7, 1)] [(6439777, 1, (PC.node 6439777 13 [(2, 5), (3, 1), (7, 2), (37, 2)] []))])) (by decide +kernel)
theorem hp_3963 : Nat.Prime (512720 ^ 2 + 3963 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897503769 11 [(2, 3), (3, 3), (97, 1)] [(12547609, 1, (PC.node 12547609 11 [(2, 3), (3, 1), (83, 1), (6299, 1)] []))])) (by decide +kernel)
theorem hp_3969 : Nat.Prime (512720 ^ 2 + 3969 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897551361 38 [(2, 11), (3, 2), (5, 1), (23, 1), (73, 1), (1699, 1)] [])) (by decide +kernel)
theorem hp_3979 : Nat.Prime (512720 ^ 2 + 3979 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897630841 6 [(2, 3), (5, 1), (13, 1), (17, 1), (101, 1), (277, 1), (1063, 1)] [])) (by decide +kernel)
theorem hp_4009 : Nat.Prime (512720 ^ 2 + 4009 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897870481 3 [(2, 4), (5, 1), (7, 1), (1409, 1), (333187, 1)] [])) (by decide +kernel)
theorem hp_4013 : Nat.Prime (512720 ^ 2 + 4013 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262897902569 6 [(2, 3), (7, 1), (17, 1), (4493, 1), (61463, 1)] [])) (by decide +kernel)
theorem hp_4057 : Nat.Prime (512720 ^ 2 + 4057 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898257649 3 [(2, 4), (13, 3), (59, 1), (126761, 1)] [])) (by decide +kernel)
theorem hp_4077 : Nat.Prime (512720 ^ 2 + 4077 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898420329 7 [(2, 3), (3, 2), (16763, 1), (217823, 1)] [])) (by decide +kernel)
theorem hp_4079 : Nat.Prime (512720 ^ 2 + 4079 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898436641 12 [(2, 5), (5, 1), (7, 1), (17, 1)] [(13807691, 1, (PC.node 13807691 2 [(2, 1), (5, 1), (13, 1), (106213, 1)] []))])) (by decide +kernel)
theorem hp_4091 : Nat.Prime (512720 ^ 2 + 4091 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898534681 3 [(2, 3), (5, 1), (89, 1), (1627, 1), (45389, 1)] [])) (by decide +kernel)
theorem hp_4101 : Nat.Prime (512720 ^ 2 + 4101 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898616601 35 [(2, 3), (3, 3), (5, 2), (101, 1), (482029, 1)] [])) (by decide +kernel)
theorem hp_4103 : Nat.Prime (512720 ^ 2 + 4103 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898633009 3 [(2, 4), (11, 1), (71, 1), (139, 1), (151357, 1)] [])) (by decide +kernel)
theorem hp_4113 : Nat.Prime (512720 ^ 2 + 4113 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898715169 7 [(2, 5), (3, 2), (17, 1)] [(53696633, 1, (PC.node 53696633 3 [(2, 3), (11, 1), (29, 1), (53, 1), (397, 1)] []))])) (by decide +kernel)
theorem hp_4123 : Nat.Prime (512720 ^ 2 + 4123 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898797529 3 [(2, 3), (283, 1)] [(116121377, 1, (PC.node 116121377 5 [(2, 5), (7, 2), (103, 1), (719, 1)] []))])) (by decide +kernel)
theorem hp_4143 : Nat.Prime (512720 ^ 2 + 4143 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262898962849 7 [(2, 5), (3, 5), (2617, 1), (12919, 1)] [])) (by decide +kernel)
theorem hp_4167 : Nat.Prime (512720 ^ 2 + 4167 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899162289 53 [(2, 4), (3, 2), (7, 1), (127, 1)] [(2053643, 1, (PC.node 2053643 2 [(2, 1), (439, 1), (2339, 1)] []))])) (by decide +kernel)
theorem hp_4169 : Nat.Prime (512720 ^ 2 + 4169 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899178961 3 [(2, 4), (5, 1), (11, 1), (1447, 1), (206461, 1)] [])) (by decide +kernel)
theorem hp_4179 : Nat.Prime (512720 ^ 2 + 4179 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899262441 11 [(2, 3), (3, 3), (5, 1), (3253, 1), (74831, 1)] [])) (by decide +kernel)
theorem hp_4183 : Nat.Prime (512720 ^ 2 + 4183 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899295889 6 [(2, 4), (17, 1), (31, 1)] [(31178759, 1, (PC.node 31178759 17 [(2, 1), (13, 1)] [(1199183, 1, (PC.node 1199183 5 [(2, 1), (599591, 1)] []))]))])) (by decide +kernel)
theorem hp_4187 : Nat.Prime (512720 ^ 2 + 4187 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899329369 3 [(2, 3), (13, 1), (31, 1), (2437, 1), (33461, 1)] [])) (by decide +kernel)
theorem hp_4193 : Nat.Prime (512720 ^ 2 + 4193 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899379649 3 [(2, 6), (3709, 1)] [(1107523, 1, (PC.node 1107523 2 [(2, 1), (3, 2), (13, 1), (4733, 1)] []))])) (by decide +kernel)
theorem hp_4203 : Nat.Prime (512720 ^ 2 + 4203 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899463609 7 [(2, 3), (3, 2), (59, 1), (349, 1), (383, 1), (463, 1)] [])) (by decide +kernel)
theorem hp_4237 : Nat.Prime (512720 ^ 2 + 4237 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899750569 3 [(2, 3), (7, 3), (13, 1), (37, 1), (139, 1), (1433, 1)] [])) (by decide +kernel)
theorem hp_4239 : Nat.Prime (512720 ^ 2 + 4239 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899767521 7 [(2, 5), (3, 2), (5, 1), (13, 1), (859, 1), (16349, 1)] [])) (by decide +kernel)
theorem hp_4241 : Nat.Prime (512720 ^ 2 + 4241 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899784481 3 [(2, 5), (5, 1), (2309, 1), (711617, 1)] [])) (by decide +kernel)
theorem hp_4243 : Nat.Prime (512720 ^ 2 + 4243 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899801449 3 [(2, 3)] [(32862475181, 1, (PC.node 32862475181 2 [(2, 2), (5, 1), (349, 1), (479, 1), (9829, 1)] []))])) (by decide +kernel)
theorem hp_4253 : Nat.Prime (512720 ^ 2 + 4253 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899886409 3 [(2, 3), (4639, 1)] [(7083959, 1, (PC.node 7083959 7 [(2, 1), (7, 1), (311, 1), (1627, 1)] []))])) (by decide +kernel)
theorem hp_4259 : Nat.Prime (512720 ^ 2 + 4259 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262899937481 3 [(2, 3), (5, 1), (1787, 1)] [(3677951, 1, (PC.node 3677951 7 [(2, 1), (5, 2), (17, 1), (4327, 1)] []))])) (by decide +kernel)
theorem hp_4273 : Nat.Prime (512720 ^ 2 + 4273 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262900056929 3 [(2, 5), (37, 1), (1613, 1), (137659, 1)] [])) (by decide +kernel)
theorem hp_4323 : Nat.Prime (512720 ^ 2 + 4323 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262900486729 23 [(2, 3), (3, 3), (11, 1)] [(110648353, 1, (PC.node 110648353 10 [(2, 5), (3, 1), (37, 1), (31151, 1)] []))])) (by decide +kernel)
theorem hp_4327 : Nat.Prime (512720 ^ 2 + 4327 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262900521329 3 [(2, 4), (317, 1)] [(51833699, 1, (PC.node 51833699 2 [(2, 1), (7, 1), (1667, 1), (2221, 1)] []))])) (by decide +kernel)
theorem hp_4331 : Nat.Prime (512720 ^ 2 + 4331 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262900555961 3 [(2, 3), (5, 1), (7, 1), (277, 1), (797, 1), (4253, 1)] [])) (by decide +kernel)
theorem hp_4341 : Nat.Prime (512720 ^ 2 + 4341 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262900642681 7 [(2, 3), (3, 3), (5, 1), (13, 1), (113, 1), (165709, 1)] [])) (by decide +kernel)
theorem hp_4347 : Nat.Prime (512720 ^ 2 + 4347 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262900694809 19 [(2, 3), (3, 2), (37, 1), (509, 1), (193883, 1)] [])) (by decide +kernel)
theorem hp_4367 : Nat.Prime (512720 ^ 2 + 4367 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262900869089 3 [(2, 5), (11, 1), (13, 1), (283, 1), (203011, 1)] [])) (by decide +kernel)
theorem hp_4391 : Nat.Prime (512720 ^ 2 + 4391 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262901079281 3 [(2, 4), (5, 1), (7, 1), (491, 1), (956143, 1)] [])) (by decide +kernel)
theorem hp_4413 : Nat.Prime (512720 ^ 2 + 4413 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262901272969 7 [(2, 3), (3, 4), (823, 1), (492967, 1)] [])) (by decide +kernel)
theorem hp_4419 : Nat.Prime (512720 ^ 2 + 4419 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262901325961 11 [(2, 3), (3, 2), (5, 1), (7, 1), (13, 1), (17, 1), (472063, 1)] [])) (by decide +kernel)
theorem hp_4431 : Nat.Prime (512720 ^ 2 + 4431 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262901432161 23 [(2, 5), (3, 3), (5, 1), (31, 1), (421, 1), (4663, 1)] [])) (by decide +kernel)
theorem hp_4453 : Nat.Prime (512720 ^ 2 + 4453 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262901627609 3 [(2, 3), (17, 1), (89, 1), (2621, 1), (8287, 1)] [])) (by decide +kernel)
theorem hp_4477 : Nat.Prime (512720 ^ 2 + 4477 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262901841929 3 [(2, 3), (11, 1)] [(2987520931, 1, (PC.node 2987520931 2 [(2, 1), (3, 2), (5, 1)] [(33194677, 1, (PC.node 33194677 5 [(2, 2), (3, 1), (17, 1), (29, 1), (31, 1), (181, 1)] []))]))])) (by decide +kernel)
theorem hp_4479 : Nat.Prime (512720 ^ 2 + 4479 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262901859841 7 [(2, 9), (3, 3), (5, 1)] [(3803557, 1, (PC.node 3803557 5 [(2, 2), (3, 1), (23, 1), (13781, 1)] []))])) (by decide +kernel)
theorem hp_4491 : Nat.Prime (512720 ^ 2 + 4491 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262901967481 7 [(2, 3), (3, 2), (5, 1), (193, 1)] [(3783851, 1, (PC.node 3783851 2 [(2, 1), (5, 2), (7, 1), (19, 1), (569, 1)] []))])) (by decide +kernel)
theorem hp_4503 : Nat.Prime (512720 ^ 2 + 4503 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262902075409 11 [(2, 4), (3, 3), (7, 1), (1091, 1), (79687, 1)] [])) (by decide +kernel)
theorem hp_4517 : Nat.Prime (512720 ^ 2 + 4517 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262902201689 6 [(2, 3), (7, 1), (8677, 1), (541049, 1)] [])) (by decide +kernel)
theorem hp_4519 : Nat.Prime (512720 ^ 2 + 4519 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262902219761 3 [(2, 4), (5, 1)] [(3286277747, 1, (PC.node 3286277747 2 [(2, 1)] [(1643138873, 1, (PC.node 1643138873 3 [(2, 3), (97, 1)] [(2117447, 1, (PC.node 2117447 5 [(2, 1)] [(1058723, 1, (PC.node 1058723 2 [(2, 1), (7, 1), (47, 1), (1609, 1)] []))]))]))]))])) (by decide +kernel)
theorem hp_4567 : Nat.Prime (512720 ^ 2 + 4567 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262902655889 3 [(2, 4), (23, 1), (113, 1), (503, 1), (12569, 1)] [])) (by decide +kernel)
theorem hp_4571 : Nat.Prime (512720 ^ 2 + 4571 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262902692441 3 [(2, 3), (5, 1)] [(6572567311, 1, (PC.node 6572567311 3 [(2, 1), (3, 1), (5, 1), (149, 1)] [(1470373, 1, (PC.node 1470373 2 [(2, 2), (3, 1), (19, 1), (6449, 1)] []))]))])) (by decide +kernel)
theorem hp_4579 : Nat.Prime (512720 ^ 2 + 4579 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262902765641 3 [(2, 3), (5, 1)] [(6572569141, 1, (PC.node 6572569141 6 [(2, 2), (3, 2), (5, 1), (83, 1), (307, 1), (1433, 1)] []))])) (by decide +kernel)
theorem hp_4583 : Nat.Prime (512720 ^ 2 + 4583 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262902802289 3 [(2, 4), (7, 2), (29, 1)] [(11563283, 1, (PC.node 11563283 2 [(2, 1), (61, 1), (94781, 1)] []))])) (by decide +kernel)
theorem hp_4601 : Nat.Prime (512720 ^ 2 + 4601 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262902967601 3 [(2, 4), (5, 2), (7, 1), (13, 1)] [(7222609, 1, (PC.node 7222609 29 [(2, 4), (3, 4), (5573, 1)] []))])) (by decide +kernel)
theorem hp_4609 : Nat.Prime (512720 ^ 2 + 4609 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262903041281 3 [(2, 8), (5, 1), (11, 1), (1697, 1), (11003, 1)] [])) (by decide +kernel)
theorem hp_4643 : Nat.Prime (512720 ^ 2 + 4643 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262903355849 3 [(2, 3), (7, 1), (37, 1), (1987, 1), (63857, 1)] [])) (by decide +kernel)
theorem hp_4689 : Nat.Prime (512720 ^ 2 + 4689 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262903785121 11 [(2, 5), (3, 2), (5, 1), (283, 1), (645131, 1)] [])) (by decide +kernel)
theorem hp_4697 : Nat.Prime (512720 ^ 2 + 4697 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262903860209 3 [(2, 4), (11, 1), (29, 1)] [(51509377, 1, (PC.node 51509377 5 [(2, 7), (3, 2), (61, 1), (733, 1)] []))])) (by decide +kernel)
theorem hp_4721 : Nat.Prime (512720 ^ 2 + 4721 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262904086241 3 [(2, 5), (5, 1), (157, 1), (359, 1), (29153, 1)] [])) (by decide +kernel)
theorem hp_4723 : Nat.Prime (512720 ^ 2 + 4723 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262904105129 3 [(2, 3), (7, 1), (127, 1), (227, 1), (162847, 1)] [])) (by decide +kernel)
theorem hp_4739 : Nat.Prime (512720 ^ 2 + 4739 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262904256521 3 [(2, 3), (5, 1), (97, 1)] [(67758829, 1, (PC.node 67758829 11 [(2, 2), (3, 1), (23, 1), (383, 1), (641, 1)] []))])) (by decide +kernel)
theorem hp_4741 : Nat.Prime (512720 ^ 2 + 4741 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262904275481 3 [(2, 3), (5, 1), (7, 1), (11, 1), (31, 1)] [(2753501, 1, (PC.node 2753501 2 [(2, 2), (5, 3), (5507, 1)] []))])) (by decide +kernel)
theorem hp_4749 : Nat.Prime (512720 ^ 2 + 4749 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262904351401 11 [(2, 3), (3, 3), (5, 2), (61, 1), (798131, 1)] [])) (by decide +kernel)
theorem hp_4759 : Nat.Prime (512720 ^ 2 + 4759 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262904446481 3 [(2, 4), (5, 1), (13, 1), (17, 1)] [(14870161, 1, (PC.node 14870161 13 [(2, 4), (3, 2), (5, 1), (19, 1), (1087, 1)] []))])) (by decide +kernel)
theorem hp_4789 : Nat.Prime (512720 ^ 2 + 4789 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262904732921 3 [(2, 3), (5, 1)] [(6572618323, 1, (PC.node 6572618323 13 [(2, 1), (3, 1), (23, 1), (751, 1), (63419, 1)] []))])) (by decide +kernel)
theorem hp_4829 : Nat.Prime (512720 ^ 2 + 4829 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905117641 3 [(2, 3), (5, 1), (11, 1), (17, 1), (37, 1), (949939, 1)] [])) (by decide +kernel)
theorem hp_4833 : Nat.Prime (512720 ^ 2 + 4833 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905156289 7 [(2, 6), (3, 2), (271, 1), (313, 1), (5381, 1)] [])) (by decide +kernel)
theorem hp_4853 : Nat.Prime (512720 ^ 2 + 4853 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905350009 15 [(2, 3), (7, 1)] [(4694738393, 1, (PC.node 4694738393 3 [(2, 3), (971, 1), (604369, 1)] []))])) (by decide +kernel)
theorem hp_4857 : Nat.Prime (512720 ^ 2 + 4857 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905388849 7 [(2, 4), (3, 3), (163, 1), (1129, 1), (3307, 1)] [])) (by decide +kernel)
theorem hp_4887 : Nat.Prime (512720 ^ 2 + 4887 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905681169 11 [(2, 4), (3, 2), (13, 1), (311, 1), (451579, 1)] [])) (by decide +kernel)
theorem hp_4889 : Nat.Prime (512720 ^ 2 + 4889 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905700721 3 [(2, 4), (5, 1), (13, 1), (23, 1), (61, 1), (180181, 1)] [])) (by decide +kernel)
theorem hp_4909 : Nat.Prime (512720 ^ 2 + 4909 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905896681 15 [(2, 3), (5, 1), (7, 1), (23, 1), (101, 1), (404197, 1)] [])) (by decide +kernel)
theorem hp_4911 : Nat.Prime (512720 ^ 2 + 4911 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905916321 23 [(2, 5), (3, 3), (5, 1), (59, 1)] [(1031489, 1, (PC.node 1031489 3 [(2, 6), (71, 1), (227, 1)] []))])) (by decide +kernel)
theorem hp_4919 : Nat.Prime (512720 ^ 2 + 4919 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262905994961 3 [(2, 4), (5, 1), (7, 1), (907, 1), (517613, 1)] [])) (by decide +kernel)
theorem hp_4933 : Nat.Prime (512720 ^ 2 + 4933 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262906132889 3 [(2, 3), (7, 1), (97, 1), (283, 1), (171023, 1)] [])) (by decide +kernel)
theorem hp_4951 : Nat.Prime (512720 ^ 2 + 4951 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262906310801 3 [(2, 4), (5, 2), (7, 1)] [(93895111, 1, (PC.node 93895111 7 [(2, 1), (3, 2), (5, 1)] [(1043279, 1, (PC.node 1043279 17 [(2, 1), (467, 1), (1117, 1)] []))]))])) (by decide +kernel)
theorem hp_4967 : Nat.Prime (512720 ^ 2 + 4967 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262906469489 3 [(2, 4), (13, 1)] [(1263973411, 1, (PC.node 1263973411 2 [(2, 1), (3, 4), (5, 1), (7, 1), (29, 1), (7687, 1)] []))])) (by decide +kernel)
theorem hp_4993 : Nat.Prime (512720 ^ 2 + 4993 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262906728449 3 [(2, 12), (7, 1), (13, 1), (31, 1), (61, 1), (373, 1)] [])) (by decide +kernel)
theorem hp_4999 : Nat.Prime (512720 ^ 2 + 4999 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262906788401 6 [(2, 4), (5, 2), (17, 1)] [(38662763, 1, (PC.node 38662763 2 [(2, 1), (43, 1), (449567, 1)] []))])) (by decide +kernel)
theorem hp_5011 : Nat.Prime (512720 ^ 2 + 5011 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262906908521 3 [(2, 3), (5, 1), (61, 1), (263, 1), (409691, 1)] [])) (by decide +kernel)
theorem hp_5021 : Nat.Prime (512720 ^ 2 + 5021 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262907008841 3 [(2, 3), (5, 1), (7, 2), (691, 1), (194119, 1)] [])) (by decide +kernel)
theorem hp_5033 : Nat.Prime (512720 ^ 2 + 5033 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262907129489 3 [(2, 4), (17, 1)] [(966570329, 1, (PC.node 966570329 6 [(2, 3), (31, 1), (53, 1), (151, 1), (487, 1)] []))])) (by decide +kernel)
theorem hp_5041 : Nat.Prime (512720 ^ 2 + 5041 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262907210081 3 [(2, 5), (5, 1), (149, 1), (631, 1), (17477, 1)] [])) (by decide +kernel)
theorem hp_5047 : Nat.Prime (512720 ^ 2 + 5047 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262907270609 6 [(2, 4), (23, 1), (29, 2), (547, 1), (1553, 1)] [])) (by decide +kernel)
theorem hp_5079 : Nat.Prime (512720 ^ 2 + 5079 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262907594641 21 [(2, 4), (3, 3), (5, 1), (7019, 1), (17341, 1)] [])) (by decide +kernel)
theorem hp_5089 : Nat.Prime (512720 ^ 2 + 5089 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262907696321 3 [(2, 6), (5, 1), (179, 1)] [(4589869, 1, (PC.node 4589869 6 [(2, 2), (3, 1), (19, 1), (41, 1), (491, 1)] []))])) (by decide +kernel)
theorem hp_5097 : Nat.Prime (512720 ^ 2 + 5097 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262907777809 11 [(2, 4), (3, 3), (13, 1), (71, 1), (659353, 1)] [])) (by decide +kernel)
theorem hp_5121 : Nat.Prime (512720 ^ 2 + 5121 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908023041 7 [(2, 8), (3, 2), (5, 1), (13, 1), (1013, 1), (1733, 1)] [])) (by decide +kernel)
theorem hp_5127 : Nat.Prime (512720 ^ 2 + 5127 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908084529 7 [(2, 4), (3, 3), (71, 1), (97, 2), (911, 1)] [])) (by decide +kernel)
theorem hp_5149 : Nat.Prime (512720 ^ 2 + 5149 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908310601 3 [(2, 3), (5, 2), (13, 1)] [(101118581, 1, (PC.node 101118581 2 [(2, 2), (5, 1), (23, 1), (219823, 1)] []))])) (by decide +kernel)
theorem hp_5159 : Nat.Prime (512720 ^ 2 + 5159 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908413681 3 [(2, 4), (5, 1), (11, 1), (89, 1), (193, 1), (17393, 1)] [])) (by decide +kernel)
theorem hp_5169 : Nat.Prime (512720 ^ 2 + 5169 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908516961 11 [(2, 5), (3, 4), (5, 1), (17, 1)] [(1193303, 1, (PC.node 1193303 5 [(2, 1), (11, 2), (4931, 1)] []))])) (by decide +kernel)
theorem hp_5173 : Nat.Prime (512720 ^ 2 + 5173 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908558329 3 [(2, 3), (13, 1), (619, 1)] [(4083953, 1, (PC.node 4083953 3 [(2, 4), (255247, 1)] []))])) (by decide +kernel)
theorem hp_5179 : Nat.Prime (512720 ^ 2 + 5179 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908620441 3 [(2, 3), (5, 1), (31, 1), (5179, 1), (40939, 1)] [])) (by decide +kernel)
theorem hp_5183 : Nat.Prime (512720 ^ 2 + 5183 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908661889 3 [(2, 7), (127, 1), (163, 1), (313, 1), (317, 1)] [])) (by decide +kernel)
theorem hp_5189 : Nat.Prime (512720 ^ 2 + 5189 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908724121 3 [(2, 3), (5, 1), (7, 1), (461, 1), (601, 1), (3389, 1)] [])) (by decide +kernel)
theorem hp_5193 : Nat.Prime (512720 ^ 2 + 5193 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908765649 11 [(2, 4), (3, 2)] [(1825755317, 1, (PC.node 1825755317 2 [(2, 2), (7, 1), (11, 1), (83, 1), (71419, 1)] []))])) (by decide +kernel)
theorem hp_5207 : Nat.Prime (512720 ^ 2 + 5207 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908911249 3 [(2, 4), (9941, 1)] [(1652933, 1, (PC.node 1652933 2 [(2, 2), (413233, 1)] []))])) (by decide +kernel)
theorem hp_5211 : Nat.Prime (512720 ^ 2 + 5211 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262908952921 7 [(2, 3), (3, 2), (5, 1), (23, 1)] [(31752289, 1, (PC.node 31752289 11 [(2, 5), (3, 2), (110251, 1)] []))])) (by decide +kernel)
theorem hp_5217 : Nat.Prime (512720 ^ 2 + 5217 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909015489 11 [(2, 6), (3, 3), (7, 2), (1153, 1), (2693, 1)] [])) (by decide +kernel)
theorem hp_5227 : Nat.Prime (512720 ^ 2 + 5227 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909119929 3 [(2, 3), (7, 1), (13, 1), (1423, 1), (253787, 1)] [])) (by decide +kernel)
theorem hp_5229 : Nat.Prime (512720 ^ 2 + 5229 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909140841 22 [(2, 3), (3, 2), (5, 1), (73, 1)] [(10004153, 1, (PC.node 10004153 3 [(2, 3)] [(1250519, 1, (PC.node 1250519 7 [(2, 1), (331, 1), (1889, 1)] []))]))])) (by decide +kernel)
theorem hp_5233 : Nat.Prime (512720 ^ 2 + 5233 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909182689 3 [(2, 5), (797, 1), (1367, 1), (7541, 1)] [])) (by decide +kernel)
theorem hp_5247 : Nat.Prime (512720 ^ 2 + 5247 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909329409 7 [(2, 17), (3, 2), (11, 1), (20261, 1)] [])) (by decide +kernel)
theorem hp_5257 : Nat.Prime (512720 ^ 2 + 5257 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909434449 3 [(2, 4), (23, 1), (7411, 1), (96401, 1)] [])) (by decide +kernel)
theorem hp_5259 : Nat.Prime (512720 ^ 2 + 5259 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909455481 22 [(2, 3), (3, 3), (5, 1), (7, 1), (4517, 1), (7699, 1)] [])) (by decide +kernel)
theorem hp_5271 : Nat.Prime (512720 ^ 2 + 5271 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909581841 31 [(2, 4), (3, 3), (5, 1), (17, 1), (599, 1), (11953, 1)] [])) (by decide +kernel)
theorem hp_5273 : Nat.Prime (512720 ^ 2 + 5273 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262909602929 3 [(2, 4), (7, 1), (37, 1), (421, 1), (150697, 1)] [])) (by decide +kernel)
theorem hp_5313 : Nat.Prime (512720 ^ 2 + 5313 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262910026369 31 [(2, 7), (3, 3), (11, 1), (101, 1), (68473, 1)] [])) (by decide +kernel)
theorem hp_5323 : Nat.Prime (512720 ^ 2 + 5323 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262910132729 3 [(2, 3), (23, 1), (251, 1)] [(5692667, 1, (PC.node 5692667 2 [(2, 1), (7, 1), (19, 1), (21401, 1)] []))])) (by decide +kernel)
theorem hp_5337 : Nat.Prime (512720 ^ 2 + 5337 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262910281969 7 [(2, 4), (3, 2), (17, 1), (29, 1), (89, 1), (41611, 1)] [])) (by decide +kernel)
theorem hp_5347 : Nat.Prime (512720 ^ 2 + 5347 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262910388809 3 [(2, 3), (37, 1)] [(888210773, 1, (PC.node 888210773 2 [(2, 2), (4651, 1), (47743, 1)] []))])) (by decide +kernel)
theorem hp_5391 : Nat.Prime (512720 ^ 2 + 5391 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262910861281 11 [(2, 5), (3, 2), (5, 1), (5303, 1), (34429, 1)] [])) (by decide +kernel)
theorem hp_5409 : Nat.Prime (512720 ^ 2 + 5409 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262911055681 11 [(2, 6), (3, 2), (5, 1), (7, 1), (13, 2), (77167, 1)] [])) (by decide +kernel)
theorem hp_5427 : Nat.Prime (512720 ^ 2 + 5427 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262911250729 11 [(2, 3), (3, 2), (7, 1), (31, 1)] [(16827397, 1, (PC.node 16827397 2 [(2, 2), (3, 1)] [(1402283, 1, (PC.node 1402283 2 [(2, 1), (7, 2), (41, 1), (349, 1)] []))]))])) (by decide +kernel)
theorem hp_5437 : Nat.Prime (512720 ^ 2 + 5437 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262911359369 3 [(2, 3), (7, 1), (127, 1)] [(36967289, 1, (PC.node 36967289 3 [(2, 3), (53, 1), (87187, 1)] []))])) (by decide +kernel)
theorem hp_5439 : Nat.Prime (512720 ^ 2 + 5439 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262911381121 23 [(2, 7), (3, 5), (5, 1), (17, 1), (277, 1), (359, 1)] [])) (by decide +kernel)
theorem hp_5449 : Nat.Prime (512720 ^ 2 + 5449 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262911490001 3 [(2, 4), (5, 4), (347, 1), (75767, 1)] [])) (by decide +kernel)
theorem hp_5451 : Nat.Prime (512720 ^ 2 + 5451 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262911511801 31 [(2, 3), (3, 3), (5, 2), (7, 1), (29, 1), (373, 1), (643, 1)] [])) (by decide +kernel)
theorem hp_5461 : Nat.Prime (512720 ^ 2 + 5461 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262911620921 3 [(2, 3), (5, 1), (13, 1), (23, 1)] [(21982577, 1, (PC.node 21982577 3 [(2, 4), (7, 2), (11, 1), (2549, 1)] []))])) (by decide +kernel)
theorem hp_5513 : Nat.Prime (512720 ^ 2 + 5513 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262912191569 6 [(2, 4), (13, 1)] [(1264000921, 1, (PC.node 1264000921 11 [(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (115751, 1)] []))])) (by decide +kernel)
theorem hp_5543 : Nat.Prime (512720 ^ 2 + 5543 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262912523249 3 [(2, 4), (17, 1), (97, 1)] [(9964847, 1, (PC.node 9964847 5 [(2, 1), (47, 1), (227, 1), (467, 1)] []))])) (by decide +kernel)
theorem hp_5549 : Nat.Prime (512720 ^ 2 + 5549 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262912589801 3 [(2, 3), (5, 2), (7, 1)] [(187794707, 1, (PC.node 187794707 2 [(2, 1), (11, 1), (1741, 1), (4903, 1)] []))])) (by decide +kernel)
theorem hp_5563 : Nat.Prime (512720 ^ 2 + 5563 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262912745369 3 [(2, 3), (7, 2), (13, 1), (1667, 1), (30949, 1)] [])) (by decide +kernel)
theorem hp_5567 : Nat.Prime (512720 ^ 2 + 5567 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262912789889 3 [(2, 7), (7, 1), (29, 1), (1861, 1), (5437, 1)] [])) (by decide +kernel)
theorem hp_5573 : Nat.Prime (512720 ^ 2 + 5573 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262912856729 3 [(2, 3), (503, 1), (1697, 1), (38501, 1)] [])) (by decide +kernel)
theorem hp_5587 : Nat.Prime (512720 ^ 2 + 5587 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913012969 3 [(2, 3), (4703, 1)] [(6987907, 1, (PC.node 6987907 2 [(2, 1), (3, 2), (23, 1), (16879, 1)] []))])) (by decide +kernel)
theorem hp_5613 : Nat.Prime (512720 ^ 2 + 5613 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913304169 14 [(2, 3), (3, 3), (31, 1)] [(39264233, 1, (PC.node 39264233 3 [(2, 3), (7, 1), (701147, 1)] []))])) (by decide +kernel)
theorem hp_5617 : Nat.Prime (512720 ^ 2 + 5617 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913349089 3 [(2, 5), (13, 1), (389, 1)] [(1624687, 1, (PC.node 1624687 5 [(2, 1), (3, 1), (7, 1), (101, 1), (383, 1)] []))])) (by decide +kernel)
theorem hp_5621 : Nat.Prime (512720 ^ 2 + 5621 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913394041 3 [(2, 3), (5, 1), (11, 1), (61, 1), (2011, 1), (4871, 1)] [])) (by decide +kernel)
theorem hp_5639 : Nat.Prime (512720 ^ 2 + 5639 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913596721 6 [(2, 4), (5, 1), (12739, 1), (257981, 1)] [])) (by decide +kernel)
theorem hp_5643 : Nat.Prime (512720 ^ 2 + 5643 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913641849 21 [(2, 3), (3, 2), (11, 1), (13, 1), (17, 1), (37, 1), (40597, 1)] [])) (by decide +kernel)
theorem hp_5659 : Nat.Prime (512720 ^ 2 + 5659 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913822681 3 [(2, 3), (5, 1)] [(6572845567, 1, (PC.node 6572845567 3 [(2, 1), (3, 2), (7, 1), (47, 1)] [(1109903, 1, (PC.node 1109903 5 [(2, 1), (554951, 1)] []))]))])) (by decide +kernel)
theorem hp_5663 : Nat.Prime (512720 ^ 2 + 5663 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913867969 3 [(2, 6), (157, 1)] [(26165791, 1, (PC.node 26165791 3 [(2, 1), (3, 2), (5, 1), (7, 1), (41, 1), (1013, 1)] []))])) (by decide +kernel)
theorem hp_5667 : Nat.Prime (512720 ^ 2 + 5667 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262913913289 7 [(2, 3), (3, 3), (13, 1), (73, 1)] [(1282607, 1, (PC.node 1282607 7 [(2, 1), (13, 1), (49331, 1)] []))])) (by decide +kernel)
theorem hp_5709 : Nat.Prime (512720 ^ 2 + 5709 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262914391081 21 [(2, 3), (3, 4), (5, 1), (11, 1), (59, 1), (97, 1), (1289, 1)] [])) (by decide +kernel)
theorem hp_5719 : Nat.Prime (512720 ^ 2 + 5719 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262914505361 3 [(2, 4), (5, 1), (13, 1), (227, 1)] [(1113667, 1, (PC.node 1113667 3 [(2, 1), (3, 1), (19, 1), (9769, 1)] []))])) (by decide +kernel)
theorem hp_5737 : Nat.Prime (512720 ^ 2 + 5737 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262914711569 3 [(2, 4), (23, 1), (31, 1), (59, 1), (97, 1), (4027, 1)] [])) (by decide +kernel)
theorem hp_5761 : Nat.Prime (512720 ^ 2 + 5761 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262914987521 3 [(2, 9), (5, 1), (2297, 1), (44711, 1)] [])) (by decide +kernel)
theorem hp_5767 : Nat.Prime (512720 ^ 2 + 5767 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262915056689 3 [(2, 4)] [(16432191043, 1, (PC.node 16432191043 2 [(2, 1), (3, 1), (47, 1)] [(58270181, 1, (PC.node 58270181 2 [(2, 2), (5, 1)] [(2913509, 1, (PC.node 2913509 2 [(2, 2), (13, 1), (43, 1), (1303, 1)] []))]))]))])) (by decide +kernel)
theorem hp_5781 : Nat.Prime (512720 ^ 2 + 5781 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262915218361 14 [(2, 3), (3, 3), (5, 1), (17, 2), (842353, 1)] [])) (by decide +kernel)
theorem hp_5799 : Nat.Prime (512720 ^ 2 + 5799 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262915426801 7 [(2, 4), (3, 3), (5, 2), (13, 1), (29, 1), (31, 1), (2083, 1)] [])) (by decide +kernel)
theorem hp_5857 : Nat.Prime (512720 ^ 2 + 5857 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916102849 3 [(2, 6), (7, 2), (29, 1), (31, 1), (93257, 1)] [])) (by decide +kernel)
theorem hp_5877 : Nat.Prime (512720 ^ 2 + 5877 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916337529 7 [(2, 3), (3, 2), (13, 1), (89, 1)] [(3156107, 1, (PC.node 3156107 2 [(2, 1), (23, 1), (68611, 1)] []))])) (by decide +kernel)
theorem hp_5879 : Nat.Prime (512720 ^ 2 + 5879 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916361041 3 [(2, 4), (5, 1), (9733, 1), (337661, 1)] [])) (by decide +kernel)
theorem hp_5881 : Nat.Prime (512720 ^ 2 + 5881 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916384561 6 [(2, 4), (5, 1), (17, 1), (3733, 1), (51787, 1)] [])) (by decide +kernel)
theorem hp_5893 : Nat.Prime (512720 ^ 2 + 5893 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916525849 3 [(2, 3), (547, 1)] [(60081473, 1, (PC.node 60081473 3 [(2, 6), (11, 1), (31, 1), (2753, 1)] []))])) (by decide +kernel)
theorem hp_5911 : Nat.Prime (512720 ^ 2 + 5911 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916738321 6 [(2, 4), (5, 1)] [(3286459229, 1, (PC.node 3286459229 2 [(2, 2), (13, 1), (3137, 1), (20147, 1)] []))])) (by decide +kernel)
theorem hp_5917 : Nat.Prime (512720 ^ 2 + 5917 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916809289 3 [(2, 3), (7, 1), (17, 1), (29, 1), (271, 1), (35141, 1)] [])) (by decide +kernel)
def S0 : List ℕ := [21,27,41,47,59,63,109,127,129,147,151,159,167,173,179,189,199,211,233,253,259,269,277,279,281,297,303,307,309,321,327,369,379,383,397,447,449,461,467,479,497,509,513,517,529,543,553,557,569,571,577,579,601,623,631,639,647,649,651,657,677,683,727,733,747,753,759,787,789,813,817,829,839,861,863,869,879,881,883,891,893,911,919,921,927,939,943,967,979,989,993,1009,1017,1057,1061,1089,1091,1103,1121,1143,1151,1167,1181,1187,1197,1217,1221,1227,1239,1249,1271,1273,1289,1297,1317,1329,1331,1337,1351,1373,1383,1387,1397,1403,1409,1413,1429,1439,1457,1473,1481,1487,1499,1511,1517,1533,1559,1569,1603,1613,1617,1627,1639,1659,1671,1701,1707,1721,1733,1749,1763,1767,1777,1793,1803,1823,1831,1841,1843,1849,1861,1863,1877,1881,1891,1893,1897,1903,1913,1917,1923,1927,1933,1951,1957,1971,1973,1999,2003,2011,2019,2037,2039,2047,2081,2083,2109,2139,2141,2147,2149,2151,2173,2177,2181,2183,2187,2189,2211,2229,2253,2259,2269,2271,2273,2277,2283,2293,2297,2309,2311,2331,2333,2337,2343,2351,2357,2367,2369,2383,2391,2411,2427,2429,2441,2447,2449,2451,2473,2479,2481,2493,2497,2507,2511,2517,2577,2591,2597,2607,2611,2617,2647,2659,2661,2671,2687,2699,2711,2721,2729,2731,2753,2773,2777,2781,2791,2797,2803,2811,2819,2829,2843,2891,2897,2917,2937,2957,2959,2993,2997,2999,3019,3021,3037,3053,3059,3061,3073,3083,3123,3139,3157,3177,3183,3189,3197,3199,3203,3207,3231,3233,3259,3267,3271,3307,3313,3323,3347,3357,3363,3387,3407,3411,3431,3441,3453,3463,3477,3481,3489,3503,3513,3517,3527,3529,3557,3569,3591,3593,3603,3607,3609,3619,3629,3631,3633,3639,3647,3657,3659,3667,3669,3713,3733,3747,3779,3789,3793,3807,3813,3833,3841,3851,3869,3873,3897,3899,3901,3919,3933,3937,3943,3953,3957,3963,3969,3979,4009,4013,4057,4077,4079,4091,4101,4103,4113,4123,4143,4167,4169,4179,4183,4187,4193,4203,4237,4239,4241,4243,4253,4259,4273,4323,4327,4331,4341,4347,4367,4391,4413,4419,4431,4453,4477,4479,4491,4503,4517,4519,4567,4571,4579,4583,4601,4609,4643,4689,4697,4721,4723,4739,4741,4749,4759,4789,4829,4833,4853,4857,4887,4889,4909,4911,4919,4933,4951,4967,4993,4999,5011,5021,5033,5041,5047,5079,5089,5097,5121,5127,5149,5159,5169,5173,5179,5183,5189,5193,5207,5211,5217,5227,5229,5233,5247,5257,5259,5271,5273,5313,5323,5337,5347,5391,5409,5427,5437,5439,5449,5451,5461,5513,5543,5549,5563,5567,5573,5587,5613,5617,5621,5639,5643,5659,5663,5667,5709,5719,5737,5761,5767,5781,5799,5857,5877,5879,5881,5893,5911,5917]
theorem hsc0 : Cert.okChainS 512720 0 S0 = true := by decide +kernel
theorem hff0 : Cert.finalSS 0 S0 = 5917 := by decide
theorem hpS0 : ∀ s ∈ S0, Nat.Prime (512720 ^ 2 + s ^ 2) := by
  intro s hs
  simp only [S0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp_21
  · exact hp_27
  · exact hp_41
  · exact hp_47
  · exact hp_59
  · exact hp_63
  · exact hp_109
  · exact hp_127
  · exact hp_129
  · exact hp_147
  · exact hp_151
  · exact hp_159
  · exact hp_167
  · exact hp_173
  · exact hp_179
  · exact hp_189
  · exact hp_199
  · exact hp_211
  · exact hp_233
  · exact hp_253
  · exact hp_259
  · exact hp_269
  · exact hp_277
  · exact hp_279
  · exact hp_281
  · exact hp_297
  · exact hp_303
  · exact hp_307
  · exact hp_309
  · exact hp_321
  · exact hp_327
  · exact hp_369
  · exact hp_379
  · exact hp_383
  · exact hp_397
  · exact hp_447
  · exact hp_449
  · exact hp_461
  · exact hp_467
  · exact hp_479
  · exact hp_497
  · exact hp_509
  · exact hp_513
  · exact hp_517
  · exact hp_529
  · exact hp_543
  · exact hp_553
  · exact hp_557
  · exact hp_569
  · exact hp_571
  · exact hp_577
  · exact hp_579
  · exact hp_601
  · exact hp_623
  · exact hp_631
  · exact hp_639
  · exact hp_647
  · exact hp_649
  · exact hp_651
  · exact hp_657
  · exact hp_677
  · exact hp_683
  · exact hp_727
  · exact hp_733
  · exact hp_747
  · exact hp_753
  · exact hp_759
  · exact hp_787
  · exact hp_789
  · exact hp_813
  · exact hp_817
  · exact hp_829
  · exact hp_839
  · exact hp_861
  · exact hp_863
  · exact hp_869
  · exact hp_879
  · exact hp_881
  · exact hp_883
  · exact hp_891
  · exact hp_893
  · exact hp_911
  · exact hp_919
  · exact hp_921
  · exact hp_927
  · exact hp_939
  · exact hp_943
  · exact hp_967
  · exact hp_979
  · exact hp_989
  · exact hp_993
  · exact hp_1009
  · exact hp_1017
  · exact hp_1057
  · exact hp_1061
  · exact hp_1089
  · exact hp_1091
  · exact hp_1103
  · exact hp_1121
  · exact hp_1143
  · exact hp_1151
  · exact hp_1167
  · exact hp_1181
  · exact hp_1187
  · exact hp_1197
  · exact hp_1217
  · exact hp_1221
  · exact hp_1227
  · exact hp_1239
  · exact hp_1249
  · exact hp_1271
  · exact hp_1273
  · exact hp_1289
  · exact hp_1297
  · exact hp_1317
  · exact hp_1329
  · exact hp_1331
  · exact hp_1337
  · exact hp_1351
  · exact hp_1373
  · exact hp_1383
  · exact hp_1387
  · exact hp_1397
  · exact hp_1403
  · exact hp_1409
  · exact hp_1413
  · exact hp_1429
  · exact hp_1439
  · exact hp_1457
  · exact hp_1473
  · exact hp_1481
  · exact hp_1487
  · exact hp_1499
  · exact hp_1511
  · exact hp_1517
  · exact hp_1533
  · exact hp_1559
  · exact hp_1569
  · exact hp_1603
  · exact hp_1613
  · exact hp_1617
  · exact hp_1627
  · exact hp_1639
  · exact hp_1659
  · exact hp_1671
  · exact hp_1701
  · exact hp_1707
  · exact hp_1721
  · exact hp_1733
  · exact hp_1749
  · exact hp_1763
  · exact hp_1767
  · exact hp_1777
  · exact hp_1793
  · exact hp_1803
  · exact hp_1823
  · exact hp_1831
  · exact hp_1841
  · exact hp_1843
  · exact hp_1849
  · exact hp_1861
  · exact hp_1863
  · exact hp_1877
  · exact hp_1881
  · exact hp_1891
  · exact hp_1893
  · exact hp_1897
  · exact hp_1903
  · exact hp_1913
  · exact hp_1917
  · exact hp_1923
  · exact hp_1927
  · exact hp_1933
  · exact hp_1951
  · exact hp_1957
  · exact hp_1971
  · exact hp_1973
  · exact hp_1999
  · exact hp_2003
  · exact hp_2011
  · exact hp_2019
  · exact hp_2037
  · exact hp_2039
  · exact hp_2047
  · exact hp_2081
  · exact hp_2083
  · exact hp_2109
  · exact hp_2139
  · exact hp_2141
  · exact hp_2147
  · exact hp_2149
  · exact hp_2151
  · exact hp_2173
  · exact hp_2177
  · exact hp_2181
  · exact hp_2183
  · exact hp_2187
  · exact hp_2189
  · exact hp_2211
  · exact hp_2229
  · exact hp_2253
  · exact hp_2259
  · exact hp_2269
  · exact hp_2271
  · exact hp_2273
  · exact hp_2277
  · exact hp_2283
  · exact hp_2293
  · exact hp_2297
  · exact hp_2309
  · exact hp_2311
  · exact hp_2331
  · exact hp_2333
  · exact hp_2337
  · exact hp_2343
  · exact hp_2351
  · exact hp_2357
  · exact hp_2367
  · exact hp_2369
  · exact hp_2383
  · exact hp_2391
  · exact hp_2411
  · exact hp_2427
  · exact hp_2429
  · exact hp_2441
  · exact hp_2447
  · exact hp_2449
  · exact hp_2451
  · exact hp_2473
  · exact hp_2479
  · exact hp_2481
  · exact hp_2493
  · exact hp_2497
  · exact hp_2507
  · exact hp_2511
  · exact hp_2517
  · exact hp_2577
  · exact hp_2591
  · exact hp_2597
  · exact hp_2607
  · exact hp_2611
  · exact hp_2617
  · exact hp_2647
  · exact hp_2659
  · exact hp_2661
  · exact hp_2671
  · exact hp_2687
  · exact hp_2699
  · exact hp_2711
  · exact hp_2721
  · exact hp_2729
  · exact hp_2731
  · exact hp_2753
  · exact hp_2773
  · exact hp_2777
  · exact hp_2781
  · exact hp_2791
  · exact hp_2797
  · exact hp_2803
  · exact hp_2811
  · exact hp_2819
  · exact hp_2829
  · exact hp_2843
  · exact hp_2891
  · exact hp_2897
  · exact hp_2917
  · exact hp_2937
  · exact hp_2957
  · exact hp_2959
  · exact hp_2993
  · exact hp_2997
  · exact hp_2999
  · exact hp_3019
  · exact hp_3021
  · exact hp_3037
  · exact hp_3053
  · exact hp_3059
  · exact hp_3061
  · exact hp_3073
  · exact hp_3083
  · exact hp_3123
  · exact hp_3139
  · exact hp_3157
  · exact hp_3177
  · exact hp_3183
  · exact hp_3189
  · exact hp_3197
  · exact hp_3199
  · exact hp_3203
  · exact hp_3207
  · exact hp_3231
  · exact hp_3233
  · exact hp_3259
  · exact hp_3267
  · exact hp_3271
  · exact hp_3307
  · exact hp_3313
  · exact hp_3323
  · exact hp_3347
  · exact hp_3357
  · exact hp_3363
  · exact hp_3387
  · exact hp_3407
  · exact hp_3411
  · exact hp_3431
  · exact hp_3441
  · exact hp_3453
  · exact hp_3463
  · exact hp_3477
  · exact hp_3481
  · exact hp_3489
  · exact hp_3503
  · exact hp_3513
  · exact hp_3517
  · exact hp_3527
  · exact hp_3529
  · exact hp_3557
  · exact hp_3569
  · exact hp_3591
  · exact hp_3593
  · exact hp_3603
  · exact hp_3607
  · exact hp_3609
  · exact hp_3619
  · exact hp_3629
  · exact hp_3631
  · exact hp_3633
  · exact hp_3639
  · exact hp_3647
  · exact hp_3657
  · exact hp_3659
  · exact hp_3667
  · exact hp_3669
  · exact hp_3713
  · exact hp_3733
  · exact hp_3747
  · exact hp_3779
  · exact hp_3789
  · exact hp_3793
  · exact hp_3807
  · exact hp_3813
  · exact hp_3833
  · exact hp_3841
  · exact hp_3851
  · exact hp_3869
  · exact hp_3873
  · exact hp_3897
  · exact hp_3899
  · exact hp_3901
  · exact hp_3919
  · exact hp_3933
  · exact hp_3937
  · exact hp_3943
  · exact hp_3953
  · exact hp_3957
  · exact hp_3963
  · exact hp_3969
  · exact hp_3979
  · exact hp_4009
  · exact hp_4013
  · exact hp_4057
  · exact hp_4077
  · exact hp_4079
  · exact hp_4091
  · exact hp_4101
  · exact hp_4103
  · exact hp_4113
  · exact hp_4123
  · exact hp_4143
  · exact hp_4167
  · exact hp_4169
  · exact hp_4179
  · exact hp_4183
  · exact hp_4187
  · exact hp_4193
  · exact hp_4203
  · exact hp_4237
  · exact hp_4239
  · exact hp_4241
  · exact hp_4243
  · exact hp_4253
  · exact hp_4259
  · exact hp_4273
  · exact hp_4323
  · exact hp_4327
  · exact hp_4331
  · exact hp_4341
  · exact hp_4347
  · exact hp_4367
  · exact hp_4391
  · exact hp_4413
  · exact hp_4419
  · exact hp_4431
  · exact hp_4453
  · exact hp_4477
  · exact hp_4479
  · exact hp_4491
  · exact hp_4503
  · exact hp_4517
  · exact hp_4519
  · exact hp_4567
  · exact hp_4571
  · exact hp_4579
  · exact hp_4583
  · exact hp_4601
  · exact hp_4609
  · exact hp_4643
  · exact hp_4689
  · exact hp_4697
  · exact hp_4721
  · exact hp_4723
  · exact hp_4739
  · exact hp_4741
  · exact hp_4749
  · exact hp_4759
  · exact hp_4789
  · exact hp_4829
  · exact hp_4833
  · exact hp_4853
  · exact hp_4857
  · exact hp_4887
  · exact hp_4889
  · exact hp_4909
  · exact hp_4911
  · exact hp_4919
  · exact hp_4933
  · exact hp_4951
  · exact hp_4967
  · exact hp_4993
  · exact hp_4999
  · exact hp_5011
  · exact hp_5021
  · exact hp_5033
  · exact hp_5041
  · exact hp_5047
  · exact hp_5079
  · exact hp_5089
  · exact hp_5097
  · exact hp_5121
  · exact hp_5127
  · exact hp_5149
  · exact hp_5159
  · exact hp_5169
  · exact hp_5173
  · exact hp_5179
  · exact hp_5183
  · exact hp_5189
  · exact hp_5193
  · exact hp_5207
  · exact hp_5211
  · exact hp_5217
  · exact hp_5227
  · exact hp_5229
  · exact hp_5233
  · exact hp_5247
  · exact hp_5257
  · exact hp_5259
  · exact hp_5271
  · exact hp_5273
  · exact hp_5313
  · exact hp_5323
  · exact hp_5337
  · exact hp_5347
  · exact hp_5391
  · exact hp_5409
  · exact hp_5427
  · exact hp_5437
  · exact hp_5439
  · exact hp_5449
  · exact hp_5451
  · exact hp_5461
  · exact hp_5513
  · exact hp_5543
  · exact hp_5549
  · exact hp_5563
  · exact hp_5567
  · exact hp_5573
  · exact hp_5587
  · exact hp_5613
  · exact hp_5617
  · exact hp_5621
  · exact hp_5639
  · exact hp_5643
  · exact hp_5659
  · exact hp_5663
  · exact hp_5667
  · exact hp_5709
  · exact hp_5719
  · exact hp_5737
  · exact hp_5761
  · exact hp_5767
  · exact hp_5781
  · exact hp_5799
  · exact hp_5857
  · exact hp_5877
  · exact hp_5879
  · exact hp_5881
  · exact hp_5893
  · exact hp_5911
  · exact hp_5917

theorem hp_5921 : Nat.Prime (512720 ^ 2 + 5921 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916856641 6 [(2, 6), (5, 1), (23, 1)] [(35722399, 1, (PC.node 35722399 3 [(2, 1), (3, 1), (41, 1), (145213, 1)] []))])) (by decide +kernel)
theorem hp_5931 : Nat.Prime (512720 ^ 2 + 5931 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262916975161 38 [(2, 3), (3, 2), (5, 1), (7, 1), (97, 1), (193, 1), (5573, 1)] [])) (by decide +kernel)
theorem hp_5939 : Nat.Prime (512720 ^ 2 + 5939 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262917070121 3 [(2, 3), (5, 1), (37, 1), (2251, 1), (78919, 1)] [])) (by decide +kernel)
theorem hp_5947 : Nat.Prime (512720 ^ 2 + 5947 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262917165209 3 [(2, 3), (23, 1), (14081, 1), (101477, 1)] [])) (by decide +kernel)
theorem hp_5959 : Nat.Prime (512720 ^ 2 + 5959 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262917308081 11 [(2, 4), (5, 1), (7, 1), (73, 1)] [(6431441, 1, (PC.node 6431441 6 [(2, 4), (5, 1), (17, 1), (4729, 1)] []))])) (by decide +kernel)
theorem hp_5961 : Nat.Prime (512720 ^ 2 + 5961 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262917331921 7 [(2, 4), (3, 3), (5, 1), (3463, 1), (35149, 1)] [])) (by decide +kernel)
theorem hp_5973 : Nat.Prime (512720 ^ 2 + 5973 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262917475129 46 [(2, 3), (3, 3), (7, 1), (11, 1), (29, 1), (59, 1), (9239, 1)] [])) (by decide +kernel)
theorem hp_5977 : Nat.Prime (512720 ^ 2 + 5977 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262917522929 3 [(2, 4), (157, 1), (6323, 1), (16553, 1)] [])) (by decide +kernel)
theorem hp_5981 : Nat.Prime (512720 ^ 2 + 5981 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262917570761 3 [(2, 3), (5, 1), (13, 1), (31, 1)] [(16310023, 1, (PC.node 16310023 3 [(2, 1), (3, 1)] [(2718337, 1, (PC.node 2718337 5 [(2, 7), (3, 1), (7079, 1)] []))]))])) (by decide +kernel)
theorem hp_6011 : Nat.Prime (512720 ^ 2 + 6011 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262917930521 3 [(2, 3), (5, 1), (7, 1), (56747, 1), (16547, 1)] [])) (by decide +kernel)
theorem hp_6033 : Nat.Prime (512720 ^ 2 + 6033 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262918195489 14 [(2, 5), (3, 4), (13, 1), (29, 1), (269057, 1)] [])) (by decide +kernel)
theorem hp_6037 : Nat.Prime (512720 ^ 2 + 6037 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262918243769 3 [(2, 3), (23327, 1)] [(1408873, 1, (PC.node 1408873 5 [(2, 3), (3, 1), (47, 1), (1249, 1)] []))])) (by decide +kernel)
theorem hp_6051 : Nat.Prime (512720 ^ 2 + 6051 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262918413001 7 [(2, 3), (3, 3), (5, 3), (17, 1), (572807, 1)] [])) (by decide +kernel)
theorem hp_6053 : Nat.Prime (512720 ^ 2 + 6053 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262918437209 6 [(2, 3), (7, 3), (17, 1), (389, 1), (14489, 1)] [])) (by decide +kernel)
theorem hp_6059 : Nat.Prime (512720 ^ 2 + 6059 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262918509881 3 [(2, 3), (5, 1), (13, 1), (23, 1), (823, 1), (26711, 1)] [])) (by decide +kernel)
theorem hp_6081 : Nat.Prime (512720 ^ 2 + 6081 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262918776961 23 [(2, 7), (3, 3), (5, 1), (7, 1)] [(2173601, 1, (PC.node 2173601 3 [(2, 5), (5, 2), (11, 1), (13, 1), (19, 1)] []))])) (by decide +kernel)
theorem hp_6083 : Nat.Prime (512720 ^ 2 + 6083 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262918801289 6 [(2, 3), (11, 1), (13, 2), (827, 1), (21377, 1)] [])) (by decide +kernel)
theorem hp_6109 : Nat.Prime (512720 ^ 2 + 6109 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919118281 6 [(2, 3), (5, 1), (7, 1), (13, 1), (31, 1), (61, 1), (38197, 1)] [])) (by decide +kernel)
theorem hp_6111 : Nat.Prime (512720 ^ 2 + 6111 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919142721 46 [(2, 6), (3, 2), (5, 1), (13, 1), (461, 1), (15233, 1)] [])) (by decide +kernel)
theorem hp_6129 : Nat.Prime (512720 ^ 2 + 6129 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919363041 28 [(2, 5), (3, 2), (5, 1), (10211, 1), (17881, 1)] [])) (by decide +kernel)
theorem hp_6131 : Nat.Prime (512720 ^ 2 + 6131 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919387561 3 [(2, 3), (5, 1), (23, 1), (311, 1), (918913, 1)] [])) (by decide +kernel)
theorem hp_6139 : Nat.Prime (512720 ^ 2 + 6139 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919485721 3 [(2, 3), (5, 1)] [(6572987143, 1, (PC.node 6572987143 7 [(2, 1), (3, 1)] [(1095497857, 1, (PC.node 1095497857 10 [(2, 7), (3, 2), (950953, 1)] []))]))])) (by decide +kernel)
theorem hp_6147 : Nat.Prime (512720 ^ 2 + 6147 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919584009 7 [(2, 3), (3, 2), (29, 1)] [(125919341, 1, (PC.node 125919341 2 [(2, 2), (5, 1), (17, 1), (179, 1), (2069, 1)] []))])) (by decide +kernel)
theorem hp_6159 : Nat.Prime (512720 ^ 2 + 6159 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919731681 7 [(2, 5), (3, 3), (5, 1), (73, 1), (833713, 1)] [])) (by decide +kernel)
theorem hp_6161 : Nat.Prime (512720 ^ 2 + 6161 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919756321 6 [(2, 5), (5, 1), (13, 1), (37, 1), (163, 1), (20959, 1)] [])) (by decide +kernel)
theorem hp_6163 : Nat.Prime (512720 ^ 2 + 6163 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262919780969 3 [(2, 3), (13, 1), (179, 1), (241, 1), (58603, 1)] [])) (by decide +kernel)
theorem hp_6181 : Nat.Prime (512720 ^ 2 + 6181 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262920003161 3 [(2, 3), (5, 1), (59, 1), (2417, 1), (46093, 1)] [])) (by decide +kernel)
theorem hp_6211 : Nat.Prime (512720 ^ 2 + 6211 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262920374921 3 [(2, 3), (5, 1), (7, 1)] [(939001339, 1, (PC.node 939001339 3 [(2, 1), (3, 2), (11, 1)] [(4742431, 1, (PC.node 4742431 11 [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (2053, 1)] []))]))])) (by decide +kernel)
theorem hp_6219 : Nat.Prime (512720 ^ 2 + 6219 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262920474361 14 [(2, 3), (3, 2), (5, 1)] [(730334651, 1, (PC.node 730334651 2 [(2, 1), (5, 2), (1999, 1), (7307, 1)] []))])) (by decide +kernel)
theorem hp_6241 : Nat.Prime (512720 ^ 2 + 6241 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262920748481 3 [(2, 6), (5, 1), (13, 1), (673, 1), (93911, 1)] [])) (by decide +kernel)
theorem hp_6243 : Nat.Prime (512720 ^ 2 + 6243 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262920773449 7 [(2, 3), (3, 3), (23, 1)] [(52922861, 1, (PC.node 52922861 2 [(2, 2), (5, 1), (139, 1), (19037, 1)] []))])) (by decide +kernel)
theorem hp_6249 : Nat.Prime (512720 ^ 2 + 6249 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262920848401 19 [(2, 4), (3, 6), (5, 2), (7, 2), (18401, 1)] [])) (by decide +kernel)
theorem hp_6281 : Nat.Prime (512720 ^ 2 + 6281 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921249361 19 [(2, 4), (5, 1), (7, 1), (11, 1), (113, 1), (377717, 1)] [])) (by decide +kernel)
theorem hp_6287 : Nat.Prime (512720 ^ 2 + 6287 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921324769 3 [(2, 5)] [(8216291399, 1, (PC.node 8216291399 7 [(2, 1), (7, 1), (31, 1), (53, 1), (357199, 1)] []))])) (by decide +kernel)
theorem hp_6289 : Nat.Prime (512720 ^ 2 + 6289 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921349921 3 [(2, 5), (5, 1), (17, 1), (23, 1), (331, 1), (12697, 1)] [])) (by decide +kernel)
theorem hp_6291 : Nat.Prime (512720 ^ 2 + 6291 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921375081 11 [(2, 3), (3, 2), (5, 1), (7, 1), (13, 1), (17, 1), (31, 1), (97, 1), (157, 1)] [])) (by decide +kernel)
theorem hp_6297 : Nat.Prime (512720 ^ 2 + 6297 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921450609 19 [(2, 4), (3, 3), (349, 1)] [(1743881, 1, (PC.node 1743881 3 [(2, 3), (5, 1), (43597, 1)] []))])) (by decide +kernel)
theorem hp_6299 : Nat.Prime (512720 ^ 2 + 6299 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921475801 3 [(2, 3), (5, 2), (59, 1)] [(22281481, 1, (PC.node 22281481 11 [(2, 3), (3, 4), (5, 1), (13, 1), (23, 2)] []))])) (by decide +kernel)
theorem hp_6303 : Nat.Prime (512720 ^ 2 + 6303 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921526209 19 [(2, 6), (3, 4), (11, 1), (631, 1), (7307, 1)] [])) (by decide +kernel)
theorem hp_6309 : Nat.Prime (512720 ^ 2 + 6309 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921601881 23 [(2, 3), (3, 2), (5, 1), (7, 1), (37, 1), (311, 1), (9067, 1)] [])) (by decide +kernel)
theorem hp_6311 : Nat.Prime (512720 ^ 2 + 6311 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921627121 3 [(2, 4), (5, 1)] [(3286520339, 1, (PC.node 3286520339 2 [(2, 1), (37, 1)] [(44412437, 1, (PC.node 44412437 2 [(2, 2)] [(11103109, 1, (PC.node 11103109 2 [(2, 2), (3, 1), (17, 1), (37, 1), (1471, 1)] []))]))]))])) (by decide +kernel)
theorem hp_6337 : Nat.Prime (512720 ^ 2 + 6337 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262921955969 3 [(2, 7), (7, 1)] [(293439683, 1, (PC.node 293439683 2 [(2, 1)] [(146719841, 1, (PC.node 146719841 6 [(2, 5), (5, 1), (916999, 1)] []))]))])) (by decide +kernel)
theorem hp_6377 : Nat.Prime (512720 ^ 2 + 6377 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262922464529 3 [(2, 4), (338197, 1), (48589, 1)] [])) (by decide +kernel)
theorem hp_6389 : Nat.Prime (512720 ^ 2 + 6389 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262922617721 3 [(2, 3), (5, 1), (7, 1), (5413, 1), (173473, 1)] [])) (by decide +kernel)
theorem hp_6391 : Nat.Prime (512720 ^ 2 + 6391 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262922643281 6 [(2, 4), (5, 1), (11, 1), (17, 1), (601, 1), (29243, 1)] [])) (by decide +kernel)
theorem hp_6397 : Nat.Prime (512720 ^ 2 + 6397 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262922720009 3 [(2, 3), (13, 1), (73, 1)] [(34631549, 1, (PC.node 34631549 2 [(2, 2), (7, 1), (151, 1), (8191, 1)] []))])) (by decide +kernel)
theorem hp_6407 : Nat.Prime (512720 ^ 2 + 6407 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262922848049 3 [(2, 4), (7, 1), (23, 1), (1091, 1), (93553, 1)] [])) (by decide +kernel)
theorem hp_6411 : Nat.Prime (512720 ^ 2 + 6411 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262922899321 7 [(2, 3), (3, 5), (5, 1), (89, 1), (491, 1), (619, 1)] [])) (by decide +kernel)
theorem hp_6417 : Nat.Prime (512720 ^ 2 + 6417 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262922976289 11 [(2, 5), (3, 2), (7, 1), (59, 1)] [(2210477, 1, (PC.node 2210477 2 [(2, 2), (17, 1), (32507, 1)] []))])) (by decide +kernel)
theorem hp_6433 : Nat.Prime (512720 ^ 2 + 6433 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923181889 3 [(2, 6), (1129, 1)] [(3638773, 1, (PC.node 3638773 2 [(2, 2), (3, 2), (61, 1), (1657, 1)] []))])) (by decide +kernel)
theorem hp_6439 : Nat.Prime (512720 ^ 2 + 6439 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923259121 3 [(2, 4), (5, 1), (29, 1), (5021, 1), (22571, 1)] [])) (by decide +kernel)
theorem hp_6441 : Nat.Prime (512720 ^ 2 + 6441 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923284881 7 [(2, 4), (3, 4), (5, 1), (701, 1), (57881, 1)] [])) (by decide +kernel)
theorem hp_6453 : Nat.Prime (512720 ^ 2 + 6453 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923439609 11 [(2, 3), (3, 2), (23, 1), (127, 1), (467, 1), (2677, 1)] [])) (by decide +kernel)
theorem hp_6457 : Nat.Prime (512720 ^ 2 + 6457 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923491249 3 [(2, 4), (11, 1), (37, 1), (61, 1), (661889, 1)] [])) (by decide +kernel)
theorem hp_6469 : Nat.Prime (512720 ^ 2 + 6469 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923646361 3 [(2, 3), (5, 1), (599, 1), (1171, 1), (9371, 1)] [])) (by decide +kernel)
theorem hp_6481 : Nat.Prime (512720 ^ 2 + 6481 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923801761 3 [(2, 5), (5, 1), (31, 1), (2113, 1), (25087, 1)] [])) (by decide +kernel)
theorem hp_6489 : Nat.Prime (512720 ^ 2 + 6489 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923905521 11 [(2, 4), (3, 2), (5, 1), (15809, 1), (23099, 1)] [])) (by decide +kernel)
theorem hp_6491 : Nat.Prime (512720 ^ 2 + 6491 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923931481 6 [(2, 3), (5, 1), (7, 2), (5591, 1), (23993, 1)] [])) (by decide +kernel)
theorem hp_6493 : Nat.Prime (512720 ^ 2 + 6493 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262923957449 3 [(2, 3), (17, 1), (37, 1), (6379, 1), (8191, 1)] [])) (by decide +kernel)
theorem hp_6499 : Nat.Prime (512720 ^ 2 + 6499 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262924035401 6 [(2, 3), (5, 2), (13, 1), (23, 1), (503, 1), (8741, 1)] [])) (by decide +kernel)
theorem hp_6503 : Nat.Prime (512720 ^ 2 + 6503 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262924087409 3 [(2, 4)] [(16432755463, 1, (PC.node 16432755463 5 [(2, 1), (3, 2), (37, 1), (311, 1), (79337, 1)] []))])) (by decide +kernel)
theorem hp_6521 : Nat.Prime (512720 ^ 2 + 6521 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262924321841 3 [(2, 4), (5, 1), (179, 1), (383, 1), (47939, 1)] [])) (by decide +kernel)
theorem hp_6533 : Nat.Prime (512720 ^ 2 + 6533 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262924478489 3 [(2, 3), (7, 1), (18397, 1), (255209, 1)] [])) (by decide +kernel)
theorem hp_6543 : Nat.Prime (512720 ^ 2 + 6543 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262924609249 69 [(2, 5), (3, 2), (7, 2), (31, 1), (73, 1), (8233, 1)] [])) (by decide +kernel)
theorem hp_6567 : Nat.Prime (512720 ^ 2 + 6567 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262924923889 14 [(2, 4), (3, 3), (11, 1), (37, 1)] [(1495387, 1, (PC.node 1495387 3 [(2, 1), (3, 2), (83077, 1)] []))])) (by decide +kernel)
theorem hp_6569 : Nat.Prime (512720 ^ 2 + 6569 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262924950161 3 [(2, 4), (5, 1)] [(3286561877, 1, (PC.node 3286561877 3 [(2, 2), (13, 1), (10069, 1), (6277, 1)] []))])) (by decide +kernel)
theorem hp_6571 : Nat.Prime (512720 ^ 2 + 6571 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262924976441 3 [(2, 3), (5, 1), (7, 1), (2063, 1), (455171, 1)] [])) (by decide +kernel)
theorem hp_6577 : Nat.Prime (512720 ^ 2 + 6577 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262925055329 3 [(2, 5), (13, 1), (3793, 1), (166631, 1)] [])) (by decide +kernel)
theorem hp_6599 : Nat.Prime (512720 ^ 2 + 6599 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262925345201 3 [(2, 4), (5, 2), (7, 1)] [(93901909, 1, (PC.node 93901909 2 [(2, 2), (3, 1), (229, 1), (34171, 1)] []))])) (by decide +kernel)
theorem hp_6611 : Nat.Prime (512720 ^ 2 + 6611 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262925503721 3 [(2, 3), (5, 1), (11, 1), (23, 1), (29, 1), (895889, 1)] [])) (by decide +kernel)
theorem hp_6623 : Nat.Prime (512720 ^ 2 + 6623 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262925662529 3 [(2, 6), (467, 1), (2239, 1), (3929, 1)] [])) (by decide +kernel)
theorem hp_6637 : Nat.Prime (512720 ^ 2 + 6637 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262925848169 3 [(2, 3), (23, 1)] [(1428944827, 1, (PC.node 1428944827 2 [(2, 1), (3, 1), (17, 1)] [(14009263, 1, (PC.node 14009263 3 [(2, 1), (3, 1), (29, 1), (80513, 1)] []))]))])) (by decide +kernel)
theorem hp_6649 : Nat.Prime (512720 ^ 2 + 6649 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262926007601 3 [(2, 4), (5, 2), (5393, 1), (121883, 1)] [])) (by decide +kernel)
theorem hp_6653 : Nat.Prime (512720 ^ 2 + 6653 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262926060809 3 [(2, 3), (59, 1), (8221, 1), (67759, 1)] [])) (by decide +kernel)
theorem hp_6657 : Nat.Prime (512720 ^ 2 + 6657 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262926114049 31 [(2, 8), (3, 4), (13, 1), (23, 1), (42407, 1)] [])) (by decide +kernel)
theorem hp_6659 : Nat.Prime (512720 ^ 2 + 6659 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262926140681 15 [(2, 3), (5, 1), (7, 1), (71, 1), (1249, 1), (10589, 1)] [])) (by decide +kernel)
theorem hp_6661 : Nat.Prime (512720 ^ 2 + 6661 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262926167321 3 [(2, 3), (5, 1), (2857, 1)] [(2300719, 1, (PC.node 2300719 3 [(2, 1), (3, 1), (7, 1), (54779, 1)] []))])) (by decide +kernel)
theorem hp_6693 : Nat.Prime (512720 ^ 2 + 6693 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262926594649 7 [(2, 3), (3, 3)] [(1217252753, 1, (PC.node 1217252753 3 [(2, 4), (199, 1), (382303, 1)] []))])) (by decide +kernel)
theorem hp_6711 : Nat.Prime (512720 ^ 2 + 6711 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262926835921 19 [(2, 4), (3, 5), (5, 1), (7, 1), (313, 1), (6173, 1)] [])) (by decide +kernel)
theorem hp_6723 : Nat.Prime (512720 ^ 2 + 6723 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262926997129 14 [(2, 3), (3, 2), (3001, 1)] [(1216849, 1, (PC.node 1216849 17 [(2, 4), (3, 1), (101, 1), (251, 1)] []))])) (by decide +kernel)
theorem hp_6751 : Nat.Prime (512720 ^ 2 + 6751 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262927374401 3 [(2, 6), (5, 2)] [(164329609, 1, (PC.node 164329609 13 [(2, 3), (3, 1), (61, 1), (112247, 1)] []))])) (by decide +kernel)
theorem hp_6809 : Nat.Prime (512720 ^ 2 + 6809 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262928160881 3 [(2, 4), (5, 1), (7, 1), (11, 1)] [(42683143, 1, (PC.node 42683143 3 [(2, 1), (3, 1)] [(7113857, 1, (PC.node 7113857 3 [(2, 7), (149, 1), (373, 1)] []))]))])) (by decide +kernel)
theorem hp_6811 : Nat.Prime (512720 ^ 2 + 6811 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262928188121 3 [(2, 3), (5, 1), (13, 1), (2239, 1), (225829, 1)] [])) (by decide +kernel)
theorem hp_6813 : Nat.Prime (512720 ^ 2 + 6813 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262928215369 19 [(2, 3), (3, 2), (7, 1), (13, 1), (163, 1), (246193, 1)] [])) (by decide +kernel)
theorem hp_6823 : Nat.Prime (512720 ^ 2 + 6823 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262928351729 6 [(2, 4), (7, 1), (61, 1), (571, 1), (67399, 1)] [])) (by decide +kernel)
theorem hp_6829 : Nat.Prime (512720 ^ 2 + 6829 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262928433641 7 [(2, 3), (5, 1), (149, 1), (251, 1), (175759, 1)] [])) (by decide +kernel)
theorem hp_6839 : Nat.Prime (512720 ^ 2 + 6839 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262928570321 3 [(2, 4), (5, 1), (13, 1)] [(252815933, 1, (PC.node 252815933 2 [(2, 2)] [(63203983, 1, (PC.node 63203983 5 [(2, 1), (3, 1), (101, 1), (104297, 1)] []))]))])) (by decide +kernel)
theorem hp_6847 : Nat.Prime (512720 ^ 2 + 6847 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262928679809 3 [(2, 7), (3677, 1), (558643, 1)] [])) (by decide +kernel)
theorem hp_6863 : Nat.Prime (512720 ^ 2 + 6863 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262928899169 3 [(2, 5), (13, 1), (37, 1), (317, 1), (53887, 1)] [])) (by decide +kernel)
theorem hp_6871 : Nat.Prime (512720 ^ 2 + 6871 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262929009041 7 [(2, 4), (5, 1)] [(3286612613, 1, (PC.node 3286612613 2 [(2, 2)] [(821653153, 1, (PC.node 821653153 7 [(2, 5), (3, 1)] [(8558887, 1, (PC.node 8558887 3 [(2, 1), (3, 1), (7, 1), (29, 1), (7027, 1)] []))]))]))])) (by decide +kernel)
theorem hp_6881 : Nat.Prime (512720 ^ 2 + 6881 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262929146561 6 [(2, 6), (5, 1), (571, 1)] [(1438973, 1, (PC.node 1438973 2 [(2, 2), (23, 1), (15641, 1)] []))])) (by decide +kernel)
theorem hp_6887 : Nat.Prime (512720 ^ 2 + 6887 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262929229169 3 [(2, 4), (23, 1)] [(714481601, 1, (PC.node 714481601 3 [(2, 6), (5, 2), (7, 1), (63793, 1)] []))])) (by decide +kernel)
theorem hp_6899 : Nat.Prime (512720 ^ 2 + 6899 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262929394601 15 [(2, 3), (5, 2), (2243, 1), (586111, 1)] [])) (by decide +kernel)
theorem hp_6907 : Nat.Prime (512720 ^ 2 + 6907 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262929505049 3 [(2, 3), (7, 1), (50227, 1), (93479, 1)] [])) (by decide +kernel)
theorem hp_6951 : Nat.Prime (512720 ^ 2 + 6951 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262930114801 31 [(2, 4), (3, 4), (5, 2), (331, 1), (24517, 1)] [])) (by decide +kernel)
theorem hp_6971 : Nat.Prime (512720 ^ 2 + 6971 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262930393241 6 [(2, 3), (5, 1), (17, 1)] [(386662343, 1, (PC.node 386662343 5 [(2, 1), (11, 1), (337, 1), (52153, 1)] []))])) (by decide +kernel)
theorem hp_6973 : Nat.Prime (512720 ^ 2 + 6973 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262930421129 3 [(2, 3), (31, 1), (71, 1)] [(14932441, 1, (PC.node 14932441 7 [(2, 3), (3, 2), (5, 1), (41479, 1)] []))])) (by decide +kernel)
theorem hp_7013 : Nat.Prime (512720 ^ 2 + 7013 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262930980569 3 [(2, 3), (13933, 1)] [(2358887, 1, (PC.node 2358887 5 [(2, 1), (17, 1), (69379, 1)] []))])) (by decide +kernel)
theorem hp_7029 : Nat.Prime (512720 ^ 2 + 7029 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262931205241 7 [(2, 3), (3, 2), (5, 1), (11, 1)] [(66396769, 1, (PC.node 66396769 7 [(2, 5), (3, 1), (23, 1), (30071, 1)] []))])) (by decide +kernel)
theorem hp_7039 : Nat.Prime (512720 ^ 2 + 7039 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262931345921 6 [(2, 9), (5, 1), (17, 1), (31, 1), (194891, 1)] [])) (by decide +kernel)
theorem hp_7041 : Nat.Prime (512720 ^ 2 + 7041 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262931374081 7 [(2, 13), (3, 3), (5, 1), (237749, 1)] [])) (by decide +kernel)
theorem hp_7051 : Nat.Prime (512720 ^ 2 + 7051 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262931515001 6 [(2, 3), (5, 4), (7, 1), (11, 1), (23, 2), (1291, 1)] [])) (by decide +kernel)
theorem hp_7061 : Nat.Prime (512720 ^ 2 + 7061 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262931656121 3 [(2, 3), (5, 1), (7, 1), (313, 1)] [(3000133, 1, (PC.node 3000133 2 [(2, 2), (3, 3), (27779, 1)] []))])) (by decide +kernel)
theorem hp_7063 : Nat.Prime (512720 ^ 2 + 7063 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262931684369 3 [(2, 4), (1447, 1), (1571, 1), (7229, 1)] [])) (by decide +kernel)
theorem hp_7079 : Nat.Prime (512720 ^ 2 + 7079 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262931910641 3 [(2, 4), (5, 1), (7, 2)] [(67074467, 1, (PC.node 67074467 2 [(2, 1)] [(33537233, 1, (PC.node 33537233 3 [(2, 4), (907, 1), (2311, 1)] []))]))])) (by decide +kernel)
theorem hp_7113 : Nat.Prime (512720 ^ 2 + 7113 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262932393169 11 [(2, 4), (3, 4), (2069, 1), (98057, 1)] [])) (by decide +kernel)
theorem hp_7117 : Nat.Prime (512720 ^ 2 + 7117 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262932450089 6 [(2, 3), (7, 1), (11, 1), (23, 1), (89, 1), (208519, 1)] [])) (by decide +kernel)
theorem hp_7121 : Nat.Prime (512720 ^ 2 + 7121 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262932507041 3 [(2, 5), (5, 1), (7, 1), (4721, 1), (49727, 1)] [])) (by decide +kernel)
theorem hp_7141 : Nat.Prime (512720 ^ 2 + 7141 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262932792281 7 [(2, 3), (5, 1), (17, 1), (12611, 1), (30661, 1)] [])) (by decide +kernel)
theorem hp_7147 : Nat.Prime (512720 ^ 2 + 7147 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262932878009 3 [(2, 3), (1013, 1), (2411, 1), (13457, 1)] [])) (by decide +kernel)
theorem hp_7167 : Nat.Prime (512720 ^ 2 + 7167 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262933164289 14 [(2, 8), (3, 4), (2731, 1), (4643, 1)] [])) (by decide +kernel)
theorem hp_7181 : Nat.Prime (512720 ^ 2 + 7181 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262933365161 3 [(2, 3), (5, 1), (73, 1), (1289, 1), (69857, 1)] [])) (by decide +kernel)
theorem hp_7183 : Nat.Prime (512720 ^ 2 + 7183 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262933393889 6 [(2, 5), (11, 1)] [(746969869, 1, (PC.node 746969869 6 [(2, 2), (3, 2), (17, 1), (67, 1), (18217, 1)] []))])) (by decide +kernel)
theorem hp_7193 : Nat.Prime (512720 ^ 2 + 7193 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262933537649 3 [(2, 4), (29, 1), (193, 1)] [(2936099, 1, (PC.node 2936099 2 [(2, 1), (11, 1), (37, 1), (3607, 1)] []))])) (by decide +kernel)
theorem hp_7197 : Nat.Prime (512720 ^ 2 + 7197 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262933595209 7 [(2, 3), (3, 5), (37, 1), (283, 1), (12917, 1)] [])) (by decide +kernel)
theorem hp_7253 : Nat.Prime (512720 ^ 2 + 7253 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262934404409 6 [(2, 3), (13, 1)] [(2528215427, 1, (PC.node 2528215427 2 [(2, 1), (11, 1), (173, 1), (664271, 1)] []))])) (by decide +kernel)
theorem hp_7257 : Nat.Prime (512720 ^ 2 + 7257 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262934462449 11 [(2, 4), (3, 3), (7, 1), (71, 1)] [(1224637, 1, (PC.node 1224637 2 [(2, 2), (3, 1), (7, 1), (61, 1), (239, 1)] []))])) (by decide +kernel)
theorem hp_7263 : Nat.Prime (512720 ^ 2 + 7263 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262934549569 7 [(2, 6), (3, 2), (127, 1), (1409, 1), (2551, 1)] [])) (by decide +kernel)
theorem hp_7273 : Nat.Prime (512720 ^ 2 + 7273 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262934694929 3 [(2, 4), (73, 1), (1663, 1), (135367, 1)] [])) (by decide +kernel)
theorem hp_7283 : Nat.Prime (512720 ^ 2 + 7283 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262934840489 3 [(2, 3), (31, 1), (1303, 1), (813677, 1)] [])) (by decide +kernel)
theorem hp_7291 : Nat.Prime (512720 ^ 2 + 7291 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262934957081 3 [(2, 3), (5, 1)] [(6573373927, 1, (PC.node 6573373927 5 [(2, 1), (3, 1), (7, 1), (89, 1)] [(1758527, 1, (PC.node 1758527 5 [(2, 1), (7, 1), (11, 1), (19, 1), (601, 1)] []))]))])) (by decide +kernel)
theorem hp_7311 : Nat.Prime (512720 ^ 2 + 7311 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262935249121 11 [(2, 5), (3, 3), (5, 1), (17, 1), (61, 1), (58693, 1)] [])) (by decide +kernel)
theorem hp_7317 : Nat.Prime (512720 ^ 2 + 7317 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262935336889 31 [(2, 3), (3, 2), (7, 1), (1301, 1), (400997, 1)] [])) (by decide +kernel)
theorem hp_7339 : Nat.Prime (512720 ^ 2 + 7339 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262935659321 3 [(2, 3), (5, 1), (39929, 1), (164627, 1)] [])) (by decide +kernel)
theorem hp_7341 : Nat.Prime (512720 ^ 2 + 7341 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262935688681 11 [(2, 3), (3, 3), (5, 1), (7, 1)] [(34779853, 1, (PC.node 34779853 2 [(2, 2), (3, 2), (37, 1), (26111, 1)] []))])) (by decide +kernel)
theorem hp_7343 : Nat.Prime (512720 ^ 2 + 7343 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262935718049 3 [(2, 5), (17, 1), (641, 1), (754037, 1)] [])) (by decide +kernel)
theorem hp_7349 : Nat.Prime (512720 ^ 2 + 7349 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262935806201 7 [(2, 3), (5, 2), (31, 1), (8597, 1), (4933, 1)] [])) (by decide +kernel)
theorem hp_7357 : Nat.Prime (512720 ^ 2 + 7357 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262935923849 3 [(2, 3), (13, 1), (421, 1)] [(6005297, 1, (PC.node 6005297 3 [(2, 4), (11, 1), (149, 1), (229, 1)] []))])) (by decide +kernel)
theorem hp_7367 : Nat.Prime (512720 ^ 2 + 7367 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262936071089 3 [(2, 4), (29, 1), (1699, 1), (333533, 1)] [])) (by decide +kernel)
theorem hp_7369 : Nat.Prime (512720 ^ 2 + 7369 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262936100561 3 [(2, 4), (5, 1), (7, 1), (71, 1)] [(6613081, 1, (PC.node 6613081 7 [(2, 3), (3, 1), (5, 1), (55109, 1)] []))])) (by decide +kernel)
theorem hp_7381 : Nat.Prime (512720 ^ 2 + 7381 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262936277561 6 [(2, 3), (5, 1), (11, 1), (37, 1)] [(16150877, 1, (PC.node 16150877 2 [(2, 2), (7, 1), (23, 1), (31, 1), (809, 1)] []))])) (by decide +kernel)
theorem hp_7393 : Nat.Prime (512720 ^ 2 + 7393 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262936454849 3 [(2, 6), (23, 1), (491, 1), (363799, 1)] [])) (by decide +kernel)
theorem hp_7401 : Nat.Prime (512720 ^ 2 + 7401 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262936573201 47 [(2, 4), (3, 3), (5, 2), (7, 1), (509, 1), (6833, 1)] [])) (by decide +kernel)
theorem hp_7407 : Nat.Prime (512720 ^ 2 + 7407 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262936662049 7 [(2, 5), (3, 2), (31, 1), (1447, 1), (20353, 1)] [])) (by decide +kernel)
theorem hp_7411 : Nat.Prime (512720 ^ 2 + 7411 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262936721321 6 [(2, 3), (5, 1), (7, 1), (13, 1), (17, 1), (31, 1), (113, 1), (1213, 1)] [])) (by decide +kernel)
theorem hp_7421 : Nat.Prime (512720 ^ 2 + 7421 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262936869641 3 [(2, 3), (5, 1), (5099, 1)] [(1289159, 1, (PC.node 1289159 7 [(2, 1), (13, 1), (179, 1), (277, 1)] []))])) (by decide +kernel)
theorem hp_7439 : Nat.Prime (512720 ^ 2 + 7439 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262937137121 3 [(2, 5), (5, 1), (7, 1), (23, 1), (139, 1), (73433, 1)] [])) (by decide +kernel)
theorem hp_7441 : Nat.Prime (512720 ^ 2 + 7441 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262937166881 3 [(2, 5), (5, 1), (179, 1)] [(9180767, 1, (PC.node 9180767 5 [(2, 1), (7, 1), (53, 1), (12373, 1)] []))])) (by decide +kernel)
theorem hp_7457 : Nat.Prime (512720 ^ 2 + 7457 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262937405249 3 [(2, 6), (7, 1)] [(586913851, 1, (PC.node 586913851 2 [(2, 1), (3, 4), (5, 2), (144917, 1)] []))])) (by decide +kernel)
theorem hp_7461 : Nat.Prime (512720 ^ 2 + 7461 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262937464921 7 [(2, 3), (3, 2), (5, 1), (13, 1)] [(56183219, 1, (PC.node 56183219 2 [(2, 1), (7, 1), (13, 1), (197, 1), (1567, 1)] []))])) (by decide +kernel)
theorem hp_7489 : Nat.Prime (512720 ^ 2 + 7489 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262937883521 3 [(2, 7), (5, 1), (13, 1)] [(31603111, 1, (PC.node 31603111 12 [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (13681, 1)] []))])) (by decide +kernel)
theorem hp_7509 : Nat.Prime (512720 ^ 2 + 7509 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262938183481 19 [(2, 3), (3, 3), (5, 1), (7, 1)] [(34780183, 1, (PC.node 34780183 6 [(2, 1), (3, 1)] [(5796697, 1, (PC.node 5796697 5 [(2, 3), (3, 1), (149, 1), (1621, 1)] []))]))])) (by decide +kernel)
theorem hp_7513 : Nat.Prime (512720 ^ 2 + 7513 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262938243569 3 [(2, 4), (7, 1), (11, 1), (13, 1), (17, 2), (56807, 1)] [])) (by decide +kernel)
theorem hp_7543 : Nat.Prime (512720 ^ 2 + 7543 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262938695249 3 [(2, 4), (271, 1)] [(60640843, 1, (PC.node 60640843 2 [(2, 1), (3, 1), (109, 1), (92723, 1)] []))])) (by decide +kernel)
theorem hp_7561 : Nat.Prime (512720 ^ 2 + 7561 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262938967121 3 [(2, 4), (5, 1), (4159, 1), (790271, 1)] [])) (by decide +kernel)
theorem hp_7583 : Nat.Prime (512720 ^ 2 + 7583 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262939300289 3 [(2, 6), (7, 1), (17, 1), (1171, 1), (29483, 1)] [])) (by decide +kernel)
theorem hp_7587 : Nat.Prime (512720 ^ 2 + 7587 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262939360969 7 [(2, 3), (3, 2), (673, 1)] [(5426353, 1, (PC.node 5426353 19 [(2, 4), (3, 4), (53, 1), (79, 1)] []))])) (by decide +kernel)
theorem hp_7601 : Nat.Prime (512720 ^ 2 + 7601 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262939573601 3 [(2, 5), (5, 2), (11, 1)] [(29879497, 1, (PC.node 29879497 10 [(2, 3), (3, 3), (43, 1), (3217, 1)] []))])) (by decide +kernel)
theorem hp_7603 : Nat.Prime (512720 ^ 2 + 7603 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262939604009 3 [(2, 3), (23, 1), (37, 1), (4937, 1), (7823, 1)] [])) (by decide +kernel)
theorem hp_7617 : Nat.Prime (512720 ^ 2 + 7617 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262939817089 7 [(2, 7), (3, 3), (13, 1), (17, 1), (344263, 1)] [])) (by decide +kernel)
theorem hp_7623 : Nat.Prime (512720 ^ 2 + 7623 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262939908529 19 [(2, 4), (3, 2), (11, 1), (23, 1)] [(7217279, 1, (PC.node 7217279 11 [(2, 1)] [(3608639, 1, (PC.node 3608639 11 [(2, 1), (11, 1), (61, 1), (2689, 1)] []))]))])) (by decide +kernel)
theorem hp_7637 : Nat.Prime (512720 ^ 2 + 7637 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262940122169 3 [(2, 3), (113, 1), (1511, 1), (192497, 1)] [])) (by decide +kernel)
theorem hp_7659 : Nat.Prime (512720 ^ 2 + 7659 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262940458681 7 [(2, 3), (3, 2), (5, 1), (31, 1)] [(23560973, 1, (PC.node 23560973 2 [(2, 2), (107, 1), (55049, 1)] []))])) (by decide +kernel)
theorem hp_7663 : Nat.Prime (512720 ^ 2 + 7663 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262940519969 6 [(2, 5), (7, 1), (349, 1)] [(3363443, 1, (PC.node 3363443 2 [(2, 1)] [(1681721, 1, (PC.node 1681721 6 [(2, 3), (5, 1), (42043, 1)] []))]))])) (by decide +kernel)
theorem hp_7671 : Nat.Prime (512720 ^ 2 + 7671 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262940642641 14 [(2, 4), (3, 3), (5, 1), (13, 1), (1693, 1), (5531, 1)] [])) (by decide +kernel)
theorem hp_7673 : Nat.Prime (512720 ^ 2 + 7673 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262940673329 3 [(2, 4)] [(16433792083, 1, (PC.node 16433792083 2 [(2, 1), (3, 5)] [(33814387, 1, (PC.node 33814387 14 [(2, 1), (3, 2)] [(1878577, 1, (PC.node 1878577 10 [(2, 4), (3, 1), (7, 1), (5591, 1)] []))]))]))])) (by decide +kernel)
theorem hp_7687 : Nat.Prime (512720 ^ 2 + 7687 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262940888369 3 [(2, 4), (313, 1), (991, 1), (52981, 1)] [])) (by decide +kernel)
theorem hp_7697 : Nat.Prime (512720 ^ 2 + 7697 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262941042209 3 [(2, 5), (13, 1), (10859, 1), (58207, 1)] [])) (by decide +kernel)
theorem hp_7699 : Nat.Prime (512720 ^ 2 + 7699 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262941073001 3 [(2, 3), (5, 3)] [(262941073, 1, (PC.node 262941073 5 [(2, 4), (3, 1), (79, 1), (69341, 1)] []))])) (by decide +kernel)
theorem hp_7707 : Nat.Prime (512720 ^ 2 + 7707 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262941196249 22 [(2, 3), (3, 6)] [(45085939, 1, (PC.node 45085939 2 [(2, 1), (3, 1), (17, 1), (442019, 1)] []))])) (by decide +kernel)
theorem hp_7713 : Nat.Prime (512720 ^ 2 + 7713 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262941288769 7 [(2, 6), (3, 2), (29, 1)] [(15741217, 1, (PC.node 15741217 5 [(2, 5), (3, 4), (6073, 1)] []))])) (by decide +kernel)
theorem hp_7717 : Nat.Prime (512720 ^ 2 + 7717 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262941350489 3 [(2, 3), (17, 1), (31, 1), (139, 1), (448687, 1)] [])) (by decide +kernel)
theorem hp_7733 : Nat.Prime (512720 ^ 2 + 7733 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262941597689 3 [(2, 3), (7, 1), (11, 1)] [(426853243, 1, (PC.node 426853243 2 [(2, 1), (3, 2), (6203, 1), (3823, 1)] []))])) (by decide +kernel)
theorem hp_7757 : Nat.Prime (512720 ^ 2 + 7757 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262941969449 3 [(2, 3)] [(32867746181, 1, (PC.node 32867746181 3 [(2, 2), (5, 1), (79, 1)] [(20802371, 1, (PC.node 20802371 7 [(2, 1), (5, 1)] [(2080237, 1, (PC.node 2080237 2 [(2, 2), (3, 1), (229, 1), (757, 1)] []))]))]))])) (by decide +kernel)
theorem hp_7779 : Nat.Prime (512720 ^ 2 + 7779 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262942311241 37 [(2, 3), (3, 3), (5, 1), (7, 1), (31, 1), (907, 1), (1237, 1)] [])) (by decide +kernel)
theorem hp_7783 : Nat.Prime (512720 ^ 2 + 7783 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262942373489 3 [(2, 4), (31, 1), (46703, 1), (11351, 1)] [])) (by decide +kernel)
theorem hp_7789 : Nat.Prime (512720 ^ 2 + 7789 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262942466921 3 [(2, 3), (5, 1), (7, 1), (37, 1), (947, 1), (26801, 1)] [])) (by decide +kernel)
theorem hp_7791 : Nat.Prime (512720 ^ 2 + 7791 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262942498081 22 [(2, 5), (3, 4), (5, 1), (163, 1), (124471, 1)] [])) (by decide +kernel)
theorem hp_7821 : Nat.Prime (512720 ^ 2 + 7821 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262942966441 46 [(2, 3), (3, 2), (5, 1), (7, 1), (11, 1), (17, 1), (557981, 1)] [])) (by decide +kernel)
theorem hp_7827 : Nat.Prime (512720 ^ 2 + 7827 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262943060329 14 [(2, 3), (3, 3), (13, 1)] [(93640691, 1, (PC.node 93640691 2 [(2, 1), (5, 1), (11, 2), (13, 1), (5953, 1)] []))])) (by decide +kernel)
theorem hp_7829 : Nat.Prime (512720 ^ 2 + 7829 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262943091641 3 [(2, 3), (5, 1), (29, 1), (89, 1)] [(2546911, 1, (PC.node 2546911 11 [(2, 1), (3, 3), (5, 1), (9433, 1)] []))])) (by decide +kernel)
theorem hp_7853 : Nat.Prime (512720 ^ 2 + 7853 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262943468009 3 [(2, 3), (13, 1), (17, 1), (23, 1)] [(6466247, 1, (PC.node 6466247 5 [(2, 1), (29, 1), (111487, 1)] []))])) (by decide +kernel)
theorem hp_7857 : Nat.Prime (512720 ^ 2 + 7857 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262943530849 7 [(2, 5), (3, 2), (73, 1), (163, 1), (277, 2)] [])) (by decide +kernel)
theorem hp_7861 : Nat.Prime (512720 ^ 2 + 7861 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262943593721 3 [(2, 3), (5, 1), (59, 1), (157, 1), (193, 1), (3677, 1)] [])) (by decide +kernel)
theorem hp_7867 : Nat.Prime (512720 ^ 2 + 7867 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262943688089 3 [(2, 3)] [(32867961011, 1, (PC.node 32867961011 2 [(2, 1), (5, 1)] [(3286796101, 1, (PC.node 3286796101 10 [(2, 2), (3, 1), (5, 2), (7, 1)] [(1565141, 1, (PC.node 1565141 2 [(2, 2), (5, 1), (139, 1), (563, 1)] []))]))]))])) (by decide +kernel)
theorem hp_7869 : Nat.Prime (512720 ^ 2 + 7869 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262943719561 22 [(2, 3), (3, 5), (5, 1), (509, 1), (53147, 1)] [])) (by decide +kernel)
theorem hp_7893 : Nat.Prime (512720 ^ 2 + 7893 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262944097849 7 [(2, 3), (3, 2), (16427, 1), (222317, 1)] [])) (by decide +kernel)
theorem hp_7907 : Nat.Prime (512720 ^ 2 + 7907 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262944319049 3 [(2, 3), (31, 1), (463, 1), (599, 1), (3823, 1)] [])) (by decide +kernel)
theorem hp_7909 : Nat.Prime (512720 ^ 2 + 7909 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262944350681 3 [(2, 3), (5, 1), (11, 1), (937, 1), (637781, 1)] [])) (by decide +kernel)
theorem hp_7913 : Nat.Prime (512720 ^ 2 + 7913 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262944413969 3 [(2, 4)] [(16434025873, 1, (PC.node 16434025873 7 [(2, 4), (3, 1), (11, 1), (23, 1), (947, 1), (1429, 1)] []))])) (by decide +kernel)
theorem hp_7919 : Nat.Prime (512720 ^ 2 + 7919 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262944508961 3 [(2, 5), (5, 1), (7, 1), (6427, 1), (36529, 1)] [])) (by decide +kernel)
theorem hp_7921 : Nat.Prime (512720 ^ 2 + 7921 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262944540641 3 [(2, 5), (5, 1), (17, 1), (61, 1)] [(1584767, 1, (PC.node 1584767 5 [(2, 1), (792383, 1)] []))])) (by decide +kernel)
theorem hp_7941 : Nat.Prime (512720 ^ 2 + 7941 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262944857881 11 [(2, 3), (3, 3), (5, 1)] [(243467461, 1, (PC.node 243467461 2 [(2, 2), (3, 2), (5, 1)] [(1352597, 1, (PC.node 1352597 3 [(2, 2), (7, 2), (67, 1), (103, 1)] []))]))])) (by decide +kernel)
theorem hp_7967 : Nat.Prime (512720 ^ 2 + 7967 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262945271489 3 [(2, 6), (71, 1), (1367, 1), (42331, 1)] [])) (by decide +kernel)
theorem hp_7979 : Nat.Prime (512720 ^ 2 + 7979 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262945462841 6 [(2, 3), (5, 1), (59, 1)] [(111417569, 1, (PC.node 111417569 3 [(2, 5)] [(3481799, 1, (PC.node 3481799 17 [(2, 1), (29, 1), (173, 1), (347, 1)] []))]))])) (by decide +kernel)
theorem hp_7981 : Nat.Prime (512720 ^ 2 + 7981 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262945494761 3 [(2, 3), (5, 1), (13, 1)] [(505664413, 1, (PC.node 505664413 2 [(2, 2), (3, 1), (11, 1)] [(3830791, 1, (PC.node 3830791 3 [(2, 1), (3, 1), (5, 1), (149, 1), (857, 1)] []))]))])) (by decide +kernel)
theorem hp_7989 : Nat.Prime (512720 ^ 2 + 7989 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262945622521 11 [(2, 3), (3, 3), (5, 1), (7, 1), (17, 1), (227, 1), (9013, 1)] [])) (by decide +kernel)
theorem hp_7991 : Nat.Prime (512720 ^ 2 + 7991 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262945654481 6 [(2, 4), (5, 1), (17, 1), (23, 1)] [(8406191, 1, (PC.node 8406191 23 [(2, 1), (5, 1), (13, 1), (64663, 1)] []))])) (by decide +kernel)
theorem hp_8023 : Nat.Prime (512720 ^ 2 + 8023 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262946166929 3 [(2, 4), (17, 1), (571, 1), (643, 1), (2633, 1)] [])) (by decide +kernel)
theorem hp_8029 : Nat.Prime (512720 ^ 2 + 8029 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262946263241 3 [(2, 3), (5, 1), (187193, 1), (35117, 1)] [])) (by decide +kernel)
theorem hp_8039 : Nat.Prime (512720 ^ 2 + 8039 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262946423921 3 [(2, 4), (5, 1)] [(3286830299, 1, (PC.node 3286830299 2 [(2, 1), (53, 1), (1321, 1), (23473, 1)] []))])) (by decide +kernel)
theorem hp_8051 : Nat.Prime (512720 ^ 2 + 8051 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262946617001 3 [(2, 3), (5, 3)] [(262946617, 1, (PC.node 262946617 5 [(2, 3), (3, 1), (17, 1), (521, 1), (1237, 1)] []))])) (by decide +kernel)
theorem hp_8067 : Nat.Prime (512720 ^ 2 + 8067 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262946874889 7 [(2, 3), (3, 3), (6247, 1), (194869, 1)] [])) (by decide +kernel)
theorem hp_8071 : Nat.Prime (512720 ^ 2 + 8071 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262946939441 3 [(2, 4), (5, 1), (149, 1)] [(22059307, 1, (PC.node 22059307 5 [(2, 1), (3, 2)] [(1225517, 1, (PC.node 1225517 2 [(2, 2), (151, 1), (2029, 1)] []))]))])) (by decide +kernel)
theorem hp_8093 : Nat.Prime (512720 ^ 2 + 8093 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262947295049 3 [(2, 3), (17, 2), (31, 1)] [(3668759, 1, (PC.node 3668759 17 [(2, 1), (89, 1), (20611, 1)] []))])) (by decide +kernel)
theorem hp_8097 : Nat.Prime (512720 ^ 2 + 8097 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262947359809 11 [(2, 6), (3, 3), (7, 1), (59, 1), (368447, 1)] [])) (by decide +kernel)
theorem hp_8119 : Nat.Prime (512720 ^ 2 + 8119 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262947716561 3 [(2, 4), (5, 1), (29, 1), (577, 1), (196429, 1)] [])) (by decide +kernel)
theorem hp_8137 : Nat.Prime (512720 ^ 2 + 8137 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262948009169 3 [(2, 4), (13, 1)] [(1264173121, 1, (PC.node 1264173121 19 [(2, 6), (3, 2), (5, 1), (7, 1), (73, 1), (859, 1)] []))])) (by decide +kernel)
theorem hp_8157 : Nat.Prime (512720 ^ 2 + 8157 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262948335049 31 [(2, 3), (3, 3), (7, 2), (179, 1), (138793, 1)] [])) (by decide +kernel)
theorem hp_8161 : Nat.Prime (512720 ^ 2 + 8161 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262948400321 6 [(2, 6), (5, 1), (17, 1), (4603, 1), (10501, 1)] [])) (by decide +kernel)
theorem hp_8183 : Nat.Prime (512720 ^ 2 + 8183 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262948759889 3 [(2, 4), (61, 1), (113, 1), (163, 1), (14627, 1)] [])) (by decide +kernel)
theorem hp_8187 : Nat.Prime (512720 ^ 2 + 8187 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262948825369 7 [(2, 3), (3, 3), (59, 1)] [(20633147, 1, (PC.node 20633147 2 [(2, 1)] [(10316573, 1, (PC.node 10316573 3 [(2, 2), (7, 1), (607, 2)] []))]))])) (by decide +kernel)
theorem hp_8191 : Nat.Prime (512720 ^ 2 + 8191 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262948890881 6 [(2, 8), (5, 1), (13, 1), (89, 1), (177553, 1)] [])) (by decide +kernel)
theorem hp_8209 : Nat.Prime (512720 ^ 2 + 8209 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262949186081 3 [(2, 5), (5, 1), (7, 2), (277, 1), (121081, 1)] [])) (by decide +kernel)
theorem hp_8221 : Nat.Prime (512720 ^ 2 + 8221 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262949383241 7 [(2, 3), (5, 1), (23, 1), (71, 1), (101, 1), (39857, 1)] [])) (by decide +kernel)
theorem hp_8233 : Nat.Prime (512720 ^ 2 + 8233 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262949580689 3 [(2, 4), (37, 1)] [(444171589, 1, (PC.node 444171589 2 [(2, 2), (3, 1), (7, 1), (19, 1), (53, 1), (59, 1), (89, 1)] []))])) (by decide +kernel)
theorem hp_8239 : Nat.Prime (512720 ^ 2 + 8239 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262949679521 12 [(2, 5), (5, 1), (11, 1)] [(149403227, 1, (PC.node 149403227 2 [(2, 1), (7, 1)] [(10671659, 1, (PC.node 10671659 2 [(2, 1)] [(5335829, 1, (PC.node 5335829 2 [(2, 2), (53, 1), (25169, 1)] []))]))]))])) (by decide +kernel)
theorem hp_8251 : Nat.Prime (512720 ^ 2 + 8251 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262949877401 3 [(2, 3), (5, 2), (7, 1), (71, 1)] [(2645371, 1, (PC.node 2645371 7 [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1)] []))])) (by decide +kernel)
theorem hp_8257 : Nat.Prime (512720 ^ 2 + 8257 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262949976449 3 [(2, 7), (3919, 1), (524189, 1)] [])) (by decide +kernel)
theorem hp_8299 : Nat.Prime (512720 ^ 2 + 8299 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262950671801 3 [(2, 3), (5, 2)] [(1314753359, 1, (PC.node 1314753359 19 [(2, 1), (6607, 1), (99497, 1)] []))])) (by decide +kernel)
theorem hp_8331 : Nat.Prime (512720 ^ 2 + 8331 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262951203961 7 [(2, 3), (3, 6), (5, 1), (17, 1), (530443, 1)] [])) (by decide +kernel)
theorem hp_8349 : Nat.Prime (512720 ^ 2 + 8349 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262951504201 19 [(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (73, 1), (8663, 1)] [])) (by decide +kernel)
theorem hp_8357 : Nat.Prime (512720 ^ 2 + 8357 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262951637849 3 [(2, 3), (2671, 1)] [(12305861, 1, (PC.node 12305861 2 [(2, 2), (5, 1), (7, 2), (29, 1), (433, 1)] []))])) (by decide +kernel)
theorem hp_8363 : Nat.Prime (512720 ^ 2 + 8363 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262951738169 3 [(2, 3), (7, 1), (17, 1), (71, 1), (89, 1), (43711, 1)] [])) (by decide +kernel)
theorem hp_8371 : Nat.Prime (512720 ^ 2 + 8371 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262951872041 3 [(2, 3), (5, 1), (11, 1), (13, 1), (3307, 1), (13901, 1)] [])) (by decide +kernel)
theorem hp_8377 : Nat.Prime (512720 ^ 2 + 8377 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262951972529 6 [(2, 4), (7, 1)] [(2347785469, 1, (PC.node 2347785469 2 [(2, 2), (3, 2), (7, 1), (89, 1), (104681, 1)] []))])) (by decide +kernel)
theorem hp_8379 : Nat.Prime (512720 ^ 2 + 8379 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262952006041 22 [(2, 3), (3, 2), (5, 1), (647, 1)] [(1128937, 1, (PC.node 1128937 11 [(2, 3), (3, 1), (17, 1), (2767, 1)] []))])) (by decide +kernel)
theorem hp_8387 : Nat.Prime (512720 ^ 2 + 8387 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262952140169 3 [(2, 3), (389, 1), (743, 1), (113723, 1)] [])) (by decide +kernel)
theorem hp_8389 : Nat.Prime (512720 ^ 2 + 8389 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262952173721 3 [(2, 3), (5, 1), (1753, 1)] [(3750031, 1, (PC.node 3750031 3 [(2, 1), (3, 3), (5, 1), (17, 1), (19, 1), (43, 1)] []))])) (by decide +kernel)
theorem hp_8399 : Nat.Prime (512720 ^ 2 + 8399 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262952341601 3 [(2, 5), (5, 2), (13, 1), (17, 1), (31, 1), (47977, 1)] [])) (by decide +kernel)
theorem hp_8413 : Nat.Prime (512720 ^ 2 + 8413 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262952576969 3 [(2, 3)] [(32869072121, 1, (PC.node 32869072121 11 [(2, 3), (5, 1), (29, 2), (47, 1), (20789, 1)] []))])) (by decide +kernel)
theorem hp_8423 : Nat.Prime (512720 ^ 2 + 8423 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262952745329 6 [(2, 4), (7, 1), (13, 1), (59, 1), (101, 1), (30307, 1)] [])) (by decide +kernel)
theorem hp_8431 : Nat.Prime (512720 ^ 2 + 8431 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262952880161 3 [(2, 5), (5, 1), (17, 1), (23, 1), (347, 1), (12113, 1)] [])) (by decide +kernel)
theorem hp_8447 : Nat.Prime (512720 ^ 2 + 8447 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262953150209 3 [(2, 8), (7, 1)] [(146737249, 1, (PC.node 146737249 33 [(2, 5), (3, 1), (7, 1), (59, 1), (3701, 1)] []))])) (by decide +kernel)
theorem hp_8467 : Nat.Prime (512720 ^ 2 + 8467 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262953488489 3 [(2, 3), (17, 1), (29, 1), (157, 1), (424661, 1)] [])) (by decide +kernel)
theorem hp_8479 : Nat.Prime (512720 ^ 2 + 8479 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262953691841 3 [(2, 6), (5, 1), (7, 1)] [(117390041, 1, (PC.node 117390041 6 [(2, 3), (5, 1)] [(2934751, 1, (PC.node 2934751 3 [(2, 1), (3, 1), (5, 3), (7, 1), (13, 1), (43, 1)] []))]))])) (by decide +kernel)
theorem hp_8503 : Nat.Prime (512720 ^ 2 + 8503 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262954099409 3 [(2, 4), (7, 2), (11, 1), (13, 1)] [(2345459, 1, (PC.node 2345459 2 [(2, 1), (563, 1), (2083, 1)] []))])) (by decide +kernel)
theorem hp_8513 : Nat.Prime (512720 ^ 2 + 8513 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262954269569 3 [(2, 7)] [(2054330231, 1, (PC.node 2054330231 7 [(2, 1), (5, 1), (73, 1)] [(2814151, 1, (PC.node 2814151 3 [(2, 1), (3, 1), (5, 2), (73, 1), (257, 1)] []))]))])) (by decide +kernel)
theorem hp_8521 : Nat.Prime (512720 ^ 2 + 8521 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262954405841 3 [(2, 4), (5, 1), (7, 1), (1103, 1), (425713, 1)] [])) (by decide +kernel)
theorem hp_8523 : Nat.Prime (512720 ^ 2 + 8523 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262954439929 7 [(2, 3), (3, 2), (23, 1), (31, 2), (165233, 1)] [])) (by decide +kernel)
theorem hp_8533 : Nat.Prime (512720 ^ 2 + 8533 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262954610489 3 [(2, 3), (17, 1), (127, 1)] [(15224329, 1, (PC.node 15224329 22 [(2, 3), (3, 3), (7, 1), (10069, 1)] []))])) (by decide +kernel)
theorem hp_8543 : Nat.Prime (512720 ^ 2 + 8543 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262954781249 3 [(2, 6), (23, 1), (4177, 1), (42767, 1)] [])) (by decide +kernel)
theorem hp_8547 : Nat.Prime (512720 ^ 2 + 8547 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262954849609 38 [(2, 3), (3, 4), (11, 1), (89, 1), (457, 1), (907, 1)] [])) (by decide +kernel)
theorem hp_8559 : Nat.Prime (512720 ^ 2 + 8559 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262955054881 11 [(2, 5), (3, 2), (5, 1), (7, 1), (1997, 1), (13063, 1)] [])) (by decide +kernel)
theorem hp_8569 : Nat.Prime (512720 ^ 2 + 8569 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262955226161 6 [(2, 4), (5, 1), (11, 1), (17, 1), (23, 1), (59, 1), (12953, 1)] [])) (by decide +kernel)
theorem hp_8589 : Nat.Prime (512720 ^ 2 + 8589 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262955569321 67 [(2, 3), (3, 3), (5, 1), (23, 1), (31, 1), (313, 1), (1091, 1)] [])) (by decide +kernel)
theorem hp_8603 : Nat.Prime (512720 ^ 2 + 8603 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262955810009 3 [(2, 3), (17, 1), (37, 1)] [(52256719, 1, (PC.node 52256719 3 [(2, 1), (3, 3), (887, 1), (1091, 1)] []))])) (by decide +kernel)
theorem hp_8611 : Nat.Prime (512720 ^ 2 + 8611 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262955947721 6 [(2, 3), (5, 1)] [(6573898693, 1, (PC.node 6573898693 5 [(2, 2), (3, 2), (19, 1), (283, 1), (33961, 1)] []))])) (by decide +kernel)
theorem hp_8637 : Nat.Prime (512720 ^ 2 + 8637 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262956396169 7 [(2, 3), (3, 3), (17, 1)] [(71611219, 1, (PC.node 71611219 3 [(2, 1), (3, 2), (7, 1), (263, 1), (2161, 1)] []))])) (by decide +kernel)
theorem hp_8647 : Nat.Prime (512720 ^ 2 + 8647 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262956569009 3 [(2, 4), (7, 2), (31, 1), (71, 1), (97, 1), (1571, 1)] [])) (by decide +kernel)
theorem hp_8657 : Nat.Prime (512720 ^ 2 + 8657 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262956742049 3 [(2, 5), (7, 1), (11, 1), (13, 1), (2099, 1), (3911, 1)] [])) (by decide +kernel)
theorem hp_8667 : Nat.Prime (512720 ^ 2 + 8667 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262956915289 7 [(2, 3), (3, 2), (149, 1)] [(24511271, 1, (PC.node 24511271 11 [(2, 1), (5, 1), (7, 2), (50023, 1)] []))])) (by decide +kernel)
theorem hp_8673 : Nat.Prime (512720 ^ 2 + 8673 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262957019329 23 [(2, 6), (3, 3), (521, 1), (292081, 1)] [])) (by decide +kernel)
theorem hp_8689 : Nat.Prime (512720 ^ 2 + 8689 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262957297121 3 [(2, 5), (5, 1), (7, 1)] [(234783301, 1, (PC.node 234783301 2 [(2, 2), (3, 1), (5, 2), (782611, 1)] []))])) (by decide +kernel)
theorem hp_8693 : Nat.Prime (512720 ^ 2 + 8693 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262957366649 3 [(2, 3), (263, 1), (1231, 1), (101527, 1)] [])) (by decide +kernel)
theorem hp_8711 : Nat.Prime (512720 ^ 2 + 8711 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262957679921 3 [(2, 4), (5, 1), (13, 1), (6491, 1), (38953, 1)] [])) (by decide +kernel)
theorem hp_8717 : Nat.Prime (512720 ^ 2 + 8717 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262957784489 3 [(2, 3), (7, 1), (271, 1)] [(17327213, 1, (PC.node 17327213 2 [(2, 2), (7, 1), (137, 1), (4517, 1)] []))])) (by decide +kernel)
theorem hp_8719 : Nat.Prime (512720 ^ 2 + 8719 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262957819361 6 [(2, 5), (5, 1), (89, 1)] [(18466139, 1, (PC.node 18466139 2 [(2, 1), (19, 1), (67, 1), (7253, 1)] []))])) (by decide +kernel)
theorem hp_8727 : Nat.Prime (512720 ^ 2 + 8727 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262957958929 22 [(2, 4), (3, 3), (7, 1), (23, 1)] [(3780739, 1, (PC.node 3780739 2 [(2, 1), (3, 2), (13, 1), (107, 1), (151, 1)] []))])) (by decide +kernel)
theorem hp_8739 : Nat.Prime (512720 ^ 2 + 8739 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262958168521 7 [(2, 3), (3, 2), (5, 1), (17, 1), (127, 1), (338323, 1)] [])) (by decide +kernel)
theorem hp_8757 : Nat.Prime (512720 ^ 2 + 8757 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262958483449 11 [(2, 3), (3, 2), (29, 1)] [(125937971, 1, (PC.node 125937971 2 [(2, 1), (5, 1), (43, 1), (292879, 1)] []))])) (by decide +kernel)
theorem hp_8759 : Nat.Prime (512720 ^ 2 + 8759 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262958518481 3 [(2, 4), (5, 1), (7, 1), (29, 1)] [(16192027, 1, (PC.node 16192027 2 [(2, 1), (3, 2), (643, 1), (1399, 1)] []))])) (by decide +kernel)
theorem hp_8771 : Nat.Prime (512720 ^ 2 + 8771 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262958728841 3 [(2, 3), (5, 1), (17, 1), (31, 1), (911, 1), (13693, 1)] [])) (by decide +kernel)
theorem hp_8781 : Nat.Prime (512720 ^ 2 + 8781 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262958904361 7 [(2, 3), (3, 3), (5, 1), (157, 1)] [(1550831, 1, (PC.node 1550831 14 [(2, 1), (5, 1), (155083, 1)] []))])) (by decide +kernel)
theorem hp_8783 : Nat.Prime (512720 ^ 2 + 8783 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262958939489 6 [(2, 5), (7, 1), (115783, 1), (10139, 1)] [])) (by decide +kernel)
theorem hp_8793 : Nat.Prime (512720 ^ 2 + 8793 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262959115249 7 [(2, 4), (3, 2), (61, 1), (3637, 1), (8231, 1)] [])) (by decide +kernel)
theorem hp_8817 : Nat.Prime (512720 ^ 2 + 8817 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262959537889 7 [(2, 5), (3, 6), (29, 1), (388699, 1)] [])) (by decide +kernel)
theorem hp_8837 : Nat.Prime (512720 ^ 2 + 8837 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262959890969 3 [(2, 3), (31, 1), (251, 1)] [(4224391, 1, (PC.node 4224391 3 [(2, 1), (3, 1), (5, 1), (140813, 1)] []))])) (by decide +kernel)
theorem hp_8849 : Nat.Prime (512720 ^ 2 + 8849 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262960103201 6 [(2, 5), (5, 2)] [(328700129, 1, (PC.node 328700129 3 [(2, 5)] [(10271879, 1, (PC.node 10271879 7 [(2, 1), (1381, 1), (3719, 1)] []))]))])) (by decide +kernel)
theorem hp_8859 : Nat.Prime (512720 ^ 2 + 8859 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262960280281 14 [(2, 3), (3, 3), (5, 1), (2309, 1), (105449, 1)] [])) (by decide +kernel)
theorem hp_8867 : Nat.Prime (512720 ^ 2 + 8867 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262960422089 3 [(2, 3), (7, 1), (13, 1), (1091, 1), (331081, 1)] [])) (by decide +kernel)
theorem hp_8873 : Nat.Prime (512720 ^ 2 + 8873 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262960528529 3 [(2, 4), (17, 1), (29, 1), (179, 1), (186239, 1)] [])) (by decide +kernel)
theorem hp_8893 : Nat.Prime (512720 ^ 2 + 8893 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262960883849 3 [(2, 3), (13, 1), (176779, 1), (14303, 1)] [])) (by decide +kernel)
theorem hp_8917 : Nat.Prime (512720 ^ 2 + 8917 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262961311289 3 [(2, 3), (13, 1), (5281, 1), (478787, 1)] [])) (by decide +kernel)
theorem hp_8973 : Nat.Prime (512720 ^ 2 + 8973 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262962313129 7 [(2, 3), (3, 2), (37, 1), (11329, 1), (8713, 1)] [])) (by decide +kernel)
theorem hp_8989 : Nat.Prime (512720 ^ 2 + 8989 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262962600521 6 [(2, 3), (5, 1), (29, 1)] [(226691897, 1, (PC.node 226691897 3 [(2, 3), (37, 1), (765851, 1)] []))])) (by decide +kernel)
theorem hp_9011 : Nat.Prime (512720 ^ 2 + 9011 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262962996521 3 [(2, 3), (5, 1), (7, 1), (17, 1), (2803, 1), (19709, 1)] [])) (by decide +kernel)
theorem hp_9013 : Nat.Prime (512720 ^ 2 + 9013 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262963032569 3 [(2, 3), (59, 1), (1471, 1), (378739, 1)] [])) (by decide +kernel)
theorem hp_9021 : Nat.Prime (512720 ^ 2 + 9021 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262963176841 11 [(2, 3), (3, 3), (5, 1), (7, 1), (13, 1)] [(2675653, 1, (PC.node 2675653 5 [(2, 2), (3, 1), (7, 1), (53, 1), (601, 1)] []))])) (by decide +kernel)
theorem hp_9031 : Nat.Prime (512720 ^ 2 + 9031 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262963357361 3 [(2, 4), (5, 1), (11, 1)] [(298821997, 1, (PC.node 298821997 2 [(2, 2), (3, 2), (11, 1), (73, 1), (10337, 1)] []))])) (by decide +kernel)
theorem hp_9041 : Nat.Prime (512720 ^ 2 + 9041 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262963538081 6 [(2, 5), (5, 1), (59, 1), (127, 1), (421, 1), (521, 1)] [])) (by decide +kernel)
theorem hp_9043 : Nat.Prime (512720 ^ 2 + 9043 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262963574249 3 [(2, 3), (17, 1)] [(1933555693, 1, (PC.node 1933555693 2 [(2, 2), (3, 1), (1151, 1), (139991, 1)] []))])) (by decide +kernel)
theorem hp_9063 : Nat.Prime (512720 ^ 2 + 9063 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262963936369 11 [(2, 4), (3, 2), (7, 1)] [(260876921, 1, (PC.node 260876921 3 [(2, 3), (5, 1)] [(6521923, 1, (PC.node 6521923 3 [(2, 1), (3, 2), (11, 1), (32939, 1)] []))]))])) (by decide +kernel)
theorem hp_9079 : Nat.Prime (512720 ^ 2 + 9079 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262964226641 3 [(2, 4), (5, 1), (17, 1), (73, 1)] [(2648713, 1, (PC.node 2648713 10 [(2, 3), (3, 1), (11, 1), (79, 1), (127, 1)] []))])) (by decide +kernel)
theorem hp_9081 : Nat.Prime (512720 ^ 2 + 9081 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262964262961 79 [(2, 4), (3, 2), (5, 1), (7, 1), (31, 1), (89, 1), (18911, 1)] [])) (by decide +kernel)
theorem hp_9083 : Nat.Prime (512720 ^ 2 + 9083 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262964299289 3 [(2, 3), (37, 2)] [(24010619, 1, (PC.node 24010619 2 [(2, 1)] [(12005309, 1, (PC.node 12005309 2 [(2, 2), (7, 1), (31, 1), (13831, 1)] []))]))])) (by decide +kernel)
theorem hp_9091 : Nat.Prime (512720 ^ 2 + 9091 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262964444681 3 [(2, 3), (5, 1), (7, 2), (33533, 1), (4001, 1)] [])) (by decide +kernel)
theorem hp_9093 : Nat.Prime (512720 ^ 2 + 9093 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262964481049 22 [(2, 3), (3, 3), (3929, 1), (309857, 1)] [])) (by decide +kernel)
theorem hp_9097 : Nat.Prime (512720 ^ 2 + 9097 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262964553809 3 [(2, 4), (11, 1)] [(1494116783, 1, (PC.node 1494116783 5 [(2, 1), (1487, 1), (502393, 1)] []))])) (by decide +kernel)
theorem hp_9111 : Nat.Prime (512720 ^ 2 + 9111 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262964808721 14 [(2, 4), (3, 4), (5, 1), (17, 1)] [(2387117, 1, (PC.node 2387117 2 [(2, 2), (596779, 1)] []))])) (by decide +kernel)
theorem hp_9151 : Nat.Prime (512720 ^ 2 + 9151 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262965539201 3 [(2, 7), (5, 2), (7, 1), (13, 1), (101, 1), (8941, 1)] [])) (by decide +kernel)
theorem hp_9153 : Nat.Prime (512720 ^ 2 + 9153 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262965575809 7 [(2, 7), (3, 2), (13, 1)] [(17559133, 1, (PC.node 17559133 2 [(2, 2), (3, 1)] [(1463261, 1, (PC.node 1463261 2 [(2, 2), (5, 1), (23, 1), (3181, 1)] []))]))])) (by decide +kernel)
theorem hp_9157 : Nat.Prime (512720 ^ 2 + 9157 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262965649049 3 [(2, 3), (37, 1), (1249, 1), (711287, 1)] [])) (by decide +kernel)
theorem hp_9159 : Nat.Prime (512720 ^ 2 + 9159 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262965685681 7 [(2, 4), (3, 3), (5, 1), (59, 1), (61, 1), (33827, 1)] [])) (by decide +kernel)
theorem hp_9167 : Nat.Prime (512720 ^ 2 + 9167 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262965832289 3 [(2, 5), (23, 2), (691, 1), (22481, 1)] [])) (by decide +kernel)
theorem hp_9171 : Nat.Prime (512720 ^ 2 + 9171 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262965905641 22 [(2, 3), (3, 2), (5, 1), (73, 1)] [(10006313, 1, (PC.node 10006313 3 [(2, 3), (19, 1), (65831, 1)] []))])) (by decide +kernel)
theorem hp_9179 : Nat.Prime (512720 ^ 2 + 9179 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262966052441 3 [(2, 3), (5, 1), (7, 1), (13, 1), (17, 1)] [(4249613, 1, (PC.node 4249613 2 [(2, 2), (107, 1), (9929, 1)] []))])) (by decide +kernel)
theorem hp_9209 : Nat.Prime (512720 ^ 2 + 9209 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262966604081 3 [(2, 4), (5, 1), (31, 1), (1907, 1), (55603, 1)] [])) (by decide +kernel)
theorem hp_9219 : Nat.Prime (512720 ^ 2 + 9219 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262966788361 19 [(2, 3), (3, 4), (5, 1), (113, 1), (263, 1), (2731, 1)] [])) (by decide +kernel)
theorem hp_9241 : Nat.Prime (512720 ^ 2 + 9241 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262967194481 3 [(2, 4), (5, 1), (139, 1), (311, 1), (76039, 1)] [])) (by decide +kernel)
theorem hp_9247 : Nat.Prime (512720 ^ 2 + 9247 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262967305409 3 [(2, 6), (17, 2), (127, 1), (111949, 1)] [])) (by decide +kernel)
theorem hp_9249 : Nat.Prime (512720 ^ 2 + 9249 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262967342401 41 [(2, 6), (3, 4), (5, 2), (7, 1), (17, 3), (59, 1)] [])) (by decide +kernel)
theorem hp_9253 : Nat.Prime (512720 ^ 2 + 9253 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262967416409 3 [(2, 3), (89, 1)] [(369336259, 1, (PC.node 369336259 2 [(2, 1), (3, 2), (379, 1), (54139, 1)] []))])) (by decide +kernel)
theorem hp_9257 : Nat.Prime (512720 ^ 2 + 9257 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262967490449 3 [(2, 4), (13, 1), (947, 1)] [(1335023, 1, (PC.node 1335023 5 [(2, 1), (13, 1), (51347, 1)] []))])) (by decide +kernel)
theorem hp_9277 : Nat.Prime (512720 ^ 2 + 9277 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262967861129 3 [(2, 3), (7, 1), (59, 1)] [(79590757, 1, (PC.node 79590757 6 [(2, 2), (3, 1), (7, 1), (947509, 1)] []))])) (by decide +kernel)
theorem hp_9293 : Nat.Prime (512720 ^ 2 + 9293 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262968158249 3 [(2, 3)] [(32871019781, 1, (PC.node 32871019781 2 [(2, 2), (5, 1), (37, 1), (191, 1), (232567, 1)] []))])) (by decide +kernel)
theorem hp_9297 : Nat.Prime (512720 ^ 2 + 9297 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262968232609 7 [(2, 5), (3, 2), (2377, 1), (384133, 1)] [])) (by decide +kernel)
theorem hp_9307 : Nat.Prime (512720 ^ 2 + 9307 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262968418649 3 [(2, 3), (13, 1), (14717, 1), (171811, 1)] [])) (by decide +kernel)
theorem hp_9329 : Nat.Prime (512720 ^ 2 + 9329 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262968828641 3 [(2, 5), (5, 1), (7, 1), (31, 1)] [(7573987, 1, (PC.node 7573987 2 [(2, 1), (3, 4), (7, 1), (6679, 1)] []))])) (by decide +kernel)
theorem hp_9339 : Nat.Prime (512720 ^ 2 + 9339 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262969015321 28 [(2, 3), (3, 3), (5, 1), (11, 1), (29, 1), (251, 1), (3041, 1)] [])) (by decide +kernel)
theorem hp_9363 : Nat.Prime (512720 ^ 2 + 9363 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262969464169 7 [(2, 3), (3, 3), (34871, 1), (34913, 1)] [])) (by decide +kernel)
theorem hp_9371 : Nat.Prime (512720 ^ 2 + 9371 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262969614041 3 [(2, 3), (5, 1), (7, 1), (23, 1), (73, 1), (559367, 1)] [])) (by decide +kernel)
theorem hp_9381 : Nat.Prime (512720 ^ 2 + 9381 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262969801561 21 [(2, 3), (3, 4), (5, 1)] [(81163519, 1, (PC.node 81163519 3 [(2, 1), (3, 1), (29, 1), (31, 1), (41, 1), (367, 1)] []))])) (by decide +kernel)
theorem hp_9387 : Nat.Prime (512720 ^ 2 + 9387 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262969914169 22 [(2, 3), (3, 2), (13, 1), (71, 1)] [(3957053, 1, (PC.node 3957053 2 [(2, 2), (11, 1), (139, 1), (647, 1)] []))])) (by decide +kernel)
theorem hp_9393 : Nat.Prime (512720 ^ 2 + 9393 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262970026849 11 [(2, 5), (3, 3), (859, 1), (354323, 1)] [])) (by decide +kernel)
theorem hp_9403 : Nat.Prime (512720 ^ 2 + 9403 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262970214809 6 [(2, 3), (7, 1), (61, 1)] [(76981913, 1, (PC.node 76981913 3 [(2, 3), (7, 1)] [(1374677, 1, (PC.node 1374677 2 [(2, 2), (557, 1), (617, 1)] []))]))])) (by decide +kernel)
theorem hp_9411 : Nat.Prime (512720 ^ 2 + 9411 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262970365321 7 [(2, 3), (3, 4), (5, 1), (13, 1)] [(6243361, 1, (PC.node 6243361 7 [(2, 5), (3, 1), (5, 1), (13007, 1)] []))])) (by decide +kernel)
theorem hp_9417 : Nat.Prime (512720 ^ 2 + 9417 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262970478289 33 [(2, 4), (3, 3), (7, 1), (17, 1), (23, 1), (37, 1), (6011, 1)] [])) (by decide +kernel)
theorem hp_9453 : Nat.Prime (512720 ^ 2 + 9453 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262971157609 11 [(2, 3), (3, 3), (17, 1), (29, 1), (31, 1), (37, 1), (2153, 1)] [])) (by decide +kernel)
theorem hp_9467 : Nat.Prime (512720 ^ 2 + 9467 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262971422489 3 [(2, 3)] [(32871427811, 1, (PC.node 32871427811 2 [(2, 1), (5, 1), (13, 2), (1601, 1), (12149, 1)] []))])) (by decide +kernel)
theorem hp_9471 : Nat.Prime (512720 ^ 2 + 9471 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262971498241 53 [(2, 8), (3, 3), (5, 1), (11, 1), (691739, 1)] [])) (by decide +kernel)
theorem hp_9487 : Nat.Prime (512720 ^ 2 + 9487 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262971801569 6 [(2, 5), (7, 1), (17, 1), (163, 1), (423667, 1)] [])) (by decide +kernel)
theorem hp_9489 : Nat.Prime (512720 ^ 2 + 9489 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262971839521 7 [(2, 5), (3, 5), (5, 1), (13, 1), (23, 1), (22621, 1)] [])) (by decide +kernel)
theorem hp_9511 : Nat.Prime (512720 ^ 2 + 9511 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262972257521 6 [(2, 4), (5, 1), (7, 1), (29, 1), (149, 1), (108677, 1)] [])) (by decide +kernel)
theorem hp_9519 : Nat.Prime (512720 ^ 2 + 9519 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262972409761 11 [(2, 5), (3, 4), (5, 1), (17, 1), (31, 1), (139, 1), (277, 1)] [])) (by decide +kernel)
theorem hp_9539 : Nat.Prime (512720 ^ 2 + 9539 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262972790921 3 [(2, 3), (5, 1), (7, 1), (113, 1), (1237, 1), (6719, 1)] [])) (by decide +kernel)
theorem hp_9549 : Nat.Prime (512720 ^ 2 + 9549 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262972981801 14 [(2, 3), (3, 2), (5, 2), (127, 1)] [(1150363, 1, (PC.node 1150363 5 [(2, 1), (3, 7), (263, 1)] []))])) (by decide +kernel)
theorem hp_9563 : Nat.Prime (512720 ^ 2 + 9563 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262973249369 3 [(2, 3), (461, 1)] [(71305111, 1, (PC.node 71305111 3 [(2, 1), (3, 4), (5, 1), (47, 1), (1873, 1)] []))])) (by decide +kernel)
theorem hp_9569 : Nat.Prime (512720 ^ 2 + 9569 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262973364161 6 [(2, 6), (5, 1), (13, 1), (29, 1)] [(2179819, 1, (PC.node 2179819 3 [(2, 1), (3, 3), (37, 1), (1091, 1)] []))])) (by decide +kernel)
theorem hp_9587 : Nat.Prime (512720 ^ 2 + 9587 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262973708969 3 [(2, 3), (17, 1)] [(1933630213, 1, (PC.node 1933630213 2 [(2, 2), (3, 1), (37, 1), (157, 1), (27739, 1)] []))])) (by decide +kernel)
theorem hp_9593 : Nat.Prime (512720 ^ 2 + 9593 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262973824049 3 [(2, 4), (13, 1), (907, 1)] [(1393933, 1, (PC.node 1393933 14 [(2, 2), (3, 1), (17, 1), (6833, 1)] []))])) (by decide +kernel)
theorem hp_9601 : Nat.Prime (512720 ^ 2 + 9601 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262973977601 6 [(2, 10), (5, 2), (23, 1), (37, 1), (12071, 1)] [])) (by decide +kernel)
theorem hp_9619 : Nat.Prime (512720 ^ 2 + 9619 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262974323561 3 [(2, 3), (5, 1), (13, 1)] [(505719853, 1, (PC.node 505719853 2 [(2, 2), (3, 1), (11, 1), (53, 1), (72287, 1)] []))])) (by decide +kernel)
theorem hp_9621 : Nat.Prime (512720 ^ 2 + 9621 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262974362041 11 [(2, 3), (3, 2), (5, 1), (13, 1), (17, 1), (317, 1), (10427, 1)] [])) (by decide +kernel)
theorem hp_9627 : Nat.Prime (512720 ^ 2 + 9627 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262974477529 47 [(2, 3), (3, 5), (7, 2), (23, 1), (29, 1), (4139, 1)] [])) (by decide +kernel)
theorem hp_9629 : Nat.Prime (512720 ^ 2 + 9629 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262974516041 7 [(2, 3), (5, 1), (29, 1), (61, 1)] [(3716429, 1, (PC.node 3716429 2 [(2, 2), (37, 1), (25111, 1)] []))])) (by decide +kernel)
theorem hp_9641 : Nat.Prime (512720 ^ 2 + 9641 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262974747281 3 [(2, 4), (5, 1), (7, 1), (71, 1)] [(6614053, 1, (PC.node 6614053 2 [(2, 2), (3, 1), (19, 1), (29009, 1)] []))])) (by decide +kernel)
theorem hp_9661 : Nat.Prime (512720 ^ 2 + 9661 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975133321 3 [(2, 3), (5, 1)] [(6574378333, 1, (PC.node 6574378333 2 [(2, 2), (3, 1), (449, 1), (709, 1), (1721, 1)] []))])) (by decide +kernel)
theorem hp_9663 : Nat.Prime (512720 ^ 2 + 9663 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975171969 7 [(2, 7), (3, 3), (73, 1), (139, 1), (7499, 1)] [])) (by decide +kernel)
theorem hp_9667 : Nat.Prime (512720 ^ 2 + 9667 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975249289 3 [(2, 3)] [(32871906161, 1, (PC.node 32871906161 3 [(2, 4), (5, 1), (103, 1), (811, 1), (4919, 1)] []))])) (by decide +kernel)
theorem hp_9669 : Nat.Prime (512720 ^ 2 + 9669 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975287961 31 [(2, 3), (3, 3), (5, 1), (7, 1), (11, 1), (991, 1), (3191, 1)] [])) (by decide +kernel)
theorem hp_9671 : Nat.Prime (512720 ^ 2 + 9671 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975326641 3 [(2, 4), (5, 1), (13, 1), (71, 1), (113, 1), (31517, 1)] [])) (by decide +kernel)
theorem hp_9677 : Nat.Prime (512720 ^ 2 + 9677 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975442729 3 [(2, 3)] [(32871930341, 1, (PC.node 32871930341 2 [(2, 2), (5, 1), (337, 1)] [(4877141, 1, (PC.node 4877141 2 [(2, 2), (5, 1), (243857, 1)] []))]))])) (by decide +kernel)
theorem hp_9683 : Nat.Prime (512720 ^ 2 + 9683 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975558889 3 [(2, 3), (7, 1), (619, 1), (947, 1), (8011, 1)] [])) (by decide +kernel)
theorem hp_9687 : Nat.Prime (512720 ^ 2 + 9687 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975636369 7 [(2, 4), (3, 3), (29, 1), (463, 1), (45337, 1)] [])) (by decide +kernel)
theorem hp_9691 : Nat.Prime (512720 ^ 2 + 9691 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262975713881 3 [(2, 3), (5, 1), (11, 1), (17, 1)] [(35157181, 1, (PC.node 35157181 6 [(2, 2), (3, 1), (5, 1), (585953, 1)] []))])) (by decide +kernel)
theorem hp_9709 : Nat.Prime (512720 ^ 2 + 9709 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262976063081 3 [(2, 3), (5, 1)] [(6574401577, 1, (PC.node 6574401577 5 [(2, 3), (3, 2), (163, 1), (560191, 1)] []))])) (by decide +kernel)
theorem hp_9731 : Nat.Prime (512720 ^ 2 + 9731 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262976490761 3 [(2, 3), (5, 1), (22153, 1), (296773, 1)] [])) (by decide +kernel)
theorem hp_9747 : Nat.Prime (512720 ^ 2 + 9747 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262976802409 7 [(2, 3), (3, 2), (163, 1), (359, 1), (62417, 1)] [])) (by decide +kernel)
theorem hp_9749 : Nat.Prime (512720 ^ 2 + 9749 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262976841401 6 [(2, 3), (5, 2), (7, 1), (13, 1), (37, 1), (59, 1), (6619, 1)] [])) (by decide +kernel)
theorem hp_9781 : Nat.Prime (512720 ^ 2 + 9781 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262977466361 6 [(2, 3), (5, 1), (7, 1)] [(939205237, 1, (PC.node 939205237 5 [(2, 2), (3, 1), (173, 1), (227, 1), (1993, 1)] []))])) (by decide +kernel)
theorem hp_9791 : Nat.Prime (512720 ^ 2 + 9791 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262977662081 3 [(2, 7), (5, 1), (7, 1), (17, 1), (193, 1), (17891, 1)] [])) (by decide +kernel)
theorem hp_9807 : Nat.Prime (512720 ^ 2 + 9807 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262977975649 23 [(2, 5), (3, 3)] [(304372657, 1, (PC.node 304372657 5 [(2, 4), (3, 2), (7, 1), (37, 1), (8161, 1)] []))])) (by decide +kernel)
theorem hp_9817 : Nat.Prime (512720 ^ 2 + 9817 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262978171889 3 [(2, 4)] [(16436135743, 1, (PC.node 16436135743 5 [(2, 1), (3, 1), (13, 1)] [(210719689, 1, (PC.node 210719689 7 [(2, 3), (3, 1), (113, 1), (77699, 1)] []))]))])) (by decide +kernel)
theorem hp_9821 : Nat.Prime (512720 ^ 2 + 9821 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262978250441 3 [(2, 3), (5, 1)] [(6574456261, 1, (PC.node 6574456261 2 [(2, 2), (3, 3), (5, 1)] [(12174919, 1, (PC.node 12174919 3 [(2, 1), (3, 1), (7, 1), (227, 1), (1277, 1)] []))]))])) (by decide +kernel)
theorem hp_9823 : Nat.Prime (512720 ^ 2 + 9823 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262978289729 3 [(2, 6), (7, 2), (11, 1), (37, 1), (206039, 1)] [])) (by decide +kernel)
theorem hp_9837 : Nat.Prime (512720 ^ 2 + 9837 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262978564969 11 [(2, 3), (3, 2), (7, 1), (101, 1), (1213, 1), (4259, 1)] [])) (by decide +kernel)
theorem hp_9847 : Nat.Prime (512720 ^ 2 + 9847 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262978761809 3 [(2, 4), (7, 1), (3067, 1), (765577, 1)] [])) (by decide +kernel)
theorem hp_9857 : Nat.Prime (512720 ^ 2 + 9857 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262978958849 3 [(2, 9), (23, 1)] [(22331773, 1, (PC.node 22331773 5 [(2, 2), (3, 2), (71, 1), (8737, 1)] []))])) (by decide +kernel)
theorem hp_9863 : Nat.Prime (512720 ^ 2 + 9863 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262979077169 3 [(2, 4), (311, 1)] [(52849493, 1, (PC.node 52849493 2 [(2, 2), (23, 1), (41, 1), (14011, 1)] []))])) (by decide +kernel)
theorem hp_9899 : Nat.Prime (512720 ^ 2 + 9899 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262979788601 3 [(2, 3), (5, 2), (5147, 1), (255469, 1)] [])) (by decide +kernel)
theorem hp_9903 : Nat.Prime (512720 ^ 2 + 9903 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262979867809 11 [(2, 5), (3, 3), (7, 1), (23, 1)] [(1890527, 1, (PC.node 1890527 5 [(2, 1), (11, 1), (85933, 1)] []))])) (by decide +kernel)
theorem hp_9913 : Nat.Prime (512720 ^ 2 + 9913 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262980065969 3 [(2, 4), (1531, 1)] [(10735633, 1, (PC.node 10735633 11 [(2, 4), (3, 3), (24851, 1)] []))])) (by decide +kernel)
theorem hp_9917 : Nat.Prime (512720 ^ 2 + 9917 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262980145289 3 [(2, 3), (7, 1), (29, 1), (2389, 1), (67783, 1)] [])) (by decide +kernel)
theorem hp_9931 : Nat.Prime (512720 ^ 2 + 9931 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262980423161 3 [(2, 3), (5, 1), (7, 1), (13, 1)] [(72247369, 1, (PC.node 72247369 7 [(2, 3), (3, 1), (401, 1), (7507, 1)] []))])) (by decide +kernel)
theorem hp_9933 : Nat.Prime (512720 ^ 2 + 9933 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262980462889 31 [(2, 3), (3, 3), (11, 1), (13, 1), (2063, 1), (4127, 1)] [])) (by decide +kernel)
theorem hp_9941 : Nat.Prime (512720 ^ 2 + 9941 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262980621881 3 [(2, 3), (5, 1), (139, 1), (3019, 1), (15667, 1)] [])) (by decide +kernel)
theorem hp_9949 : Nat.Prime (512720 ^ 2 + 9949 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262980781001 3 [(2, 3), (5, 3), (7, 1), (23, 1), (31, 1), (52691, 1)] [])) (by decide +kernel)
theorem hp_9959 : Nat.Prime (512720 ^ 2 + 9959 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262980980081 15 [(2, 4), (5, 1), (7, 1), (13, 1), (101, 1), (357661, 1)] [])) (by decide +kernel)
theorem hp_9967 : Nat.Prime (512720 ^ 2 + 9967 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262981139489 3 [(2, 5), (59663, 1), (137743, 1)] [])) (by decide +kernel)
theorem hp_9973 : Nat.Prime (512720 ^ 2 + 9973 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262981259129 3 [(2, 3), (7, 2), (12983, 1), (51673, 1)] [])) (by decide +kernel)
theorem hp_9993 : Nat.Prime (512720 ^ 2 + 9993 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262981658449 7 [(2, 4), (3, 3), (12437, 1), (48947, 1)] [])) (by decide +kernel)
theorem hp_10017 : Nat.Prime (512720 ^ 2 + 10017 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262982138689 19 [(2, 6), (3, 2)] [(456566213, 1, (PC.node 456566213 3 [(2, 2), (17, 1), (61, 1), (110069, 1)] []))])) (by decide +kernel)
theorem hp_10021 : Nat.Prime (512720 ^ 2 + 10021 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262982218841 6 [(2, 3), (5, 1), (11, 1), (1709, 1), (349729, 1)] [])) (by decide +kernel)
theorem hp_10029 : Nat.Prime (512720 ^ 2 + 10029 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262982379241 19 [(2, 3), (3, 4), (5, 1), (7, 1), (17, 1), (682079, 1)] [])) (by decide +kernel)
theorem hp_10031 : Nat.Prime (512720 ^ 2 + 10031 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262982419361 3 [(2, 5), (5, 1), (17, 1), (479, 1), (201847, 1)] [])) (by decide +kernel)
theorem hp_10069 : Nat.Prime (512720 ^ 2 + 10069 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262983183161 3 [(2, 3), (5, 1), (6781, 1), (969559, 1)] [])) (by decide +kernel)
theorem hp_10091 : Nat.Prime (512720 ^ 2 + 10091 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262983626681 3 [(2, 3), (5, 1), (29, 2)] [(7817587, 1, (PC.node 7817587 5 [(2, 1), (3, 1), (7, 1), (17, 1), (10949, 1)] []))])) (by decide +kernel)
theorem hp_10097 : Nat.Prime (512720 ^ 2 + 10097 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262983747809 3 [(2, 5), (17, 1), (71, 1)] [(6808817, 1, (PC.node 6808817 3 [(2, 4), (7, 1), (60793, 1)] []))])) (by decide +kernel)
theorem hp_10099 : Nat.Prime (512720 ^ 2 + 10099 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262983788201 3 [(2, 3), (5, 2), (7, 1), (17, 1)] [(11049739, 1, (PC.node 11049739 2 [(2, 1), (3, 1), (7, 1), (263089, 1)] []))])) (by decide +kernel)
theorem hp_10119 : Nat.Prime (512720 ^ 2 + 10119 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262984192561 11 [(2, 4), (3, 3), (5, 1), (37, 1)] [(3290593, 1, (PC.node 3290593 7 [(2, 5), (3, 1), (151, 1), (227, 1)] []))])) (by decide +kernel)
theorem hp_10143 : Nat.Prime (512720 ^ 2 + 10143 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262984678849 11 [(2, 6), (3, 2), (89, 1), (1151, 1), (4457, 1)] [])) (by decide +kernel)
theorem hp_10151 : Nat.Prime (512720 ^ 2 + 10151 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262984841201 3 [(2, 4), (5, 2), (29, 1), (991, 1), (22877, 1)] [])) (by decide +kernel)
theorem hp_10181 : Nat.Prime (512720 ^ 2 + 10181 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262985451161 3 [(2, 3), (5, 1), (691, 1)] [(9514669, 1, (PC.node 9514669 2 [(2, 2), (3, 1), (19, 1), (29, 1), (1439, 1)] []))])) (by decide +kernel)
theorem hp_10189 : Nat.Prime (512720 ^ 2 + 10189 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262985614121 3 [(2, 3), (5, 1), (467, 1)] [(14078459, 1, (PC.node 14078459 2 [(2, 1), (43, 1), (127, 1), (1289, 1)] []))])) (by decide +kernel)
theorem hp_10191 : Nat.Prime (512720 ^ 2 + 10191 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262985654881 7 [(2, 5), (3, 4), (5, 1), (13, 1), (313, 1), (4987, 1)] [])) (by decide +kernel)
theorem hp_10193 : Nat.Prime (512720 ^ 2 + 10193 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262985695649 3 [(2, 5), (13, 1), (37, 1), (59, 1), (73, 1), (3967, 1)] [])) (by decide +kernel)
theorem hp_10201 : Nat.Prime (512720 ^ 2 + 10201 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262985858801 3 [(2, 4), (5, 2), (7, 1), (17, 1), (31, 1), (178223, 1)] [])) (by decide +kernel)
theorem hp_10211 : Nat.Prime (512720 ^ 2 + 10211 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262986062921 3 [(2, 3), (5, 1), (7, 1)] [(939235939, 1, (PC.node 939235939 2 [(2, 1), (3, 1)] [(156539323, 1, (PC.node 156539323 2 [(2, 1), (3, 2)] [(8696629, 1, (PC.node 8696629 2 [(2, 2), (3, 2), (37, 1), (6529, 1)] []))]))]))])) (by decide +kernel)
theorem hp_10213 : Nat.Prime (512720 ^ 2 + 10213 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262986103769 3 [(2, 3)] [(32873262971, 1, (PC.node 32873262971 2 [(2, 1), (5, 1)] [(3287326297, 1, (PC.node 3287326297 7 [(2, 3), (3, 1), (421, 1), (325349, 1)] []))]))])) (by decide +kernel)
theorem hp_10227 : Nat.Prime (512720 ^ 2 + 10227 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262986389929 19 [(2, 3), (3, 3), (2789, 1), (436547, 1)] [])) (by decide +kernel)
theorem hp_10233 : Nat.Prime (512720 ^ 2 + 10233 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262986512689 7 [(2, 4), (3, 2), (17, 1), (1559, 1), (68909, 1)] [])) (by decide +kernel)
theorem hp_10259 : Nat.Prime (512720 ^ 2 + 10259 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262987045481 3 [(2, 3), (5, 1), (31, 1), (227, 1), (934301, 1)] [])) (by decide +kernel)
theorem hp_10269 : Nat.Prime (512720 ^ 2 + 10269 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262987250761 31 [(2, 3), (3, 2), (5, 1), (13, 1), (17, 1), (547, 1), (6043, 1)] [])) (by decide +kernel)
theorem hp_10271 : Nat.Prime (512720 ^ 2 + 10271 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262987291841 11 [(2, 6), (5, 1), (7, 1), (13, 1), (23, 1), (263, 1), (1493, 1)] [])) (by decide +kernel)
theorem hp_10313 : Nat.Prime (512720 ^ 2 + 10313 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262988156369 3 [(2, 4), (7, 2)] [(335444077, 1, (PC.node 335444077 5 [(2, 2), (3, 2), (11, 1), (47, 1), (67, 1), (269, 1)] []))])) (by decide +kernel)
theorem hp_10317 : Nat.Prime (512720 ^ 2 + 10317 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262988238889 11 [(2, 3), (3, 3), (23, 1)] [(52936441, 1, (PC.node 52936441 22 [(2, 3), (3, 1), (5, 1), (43, 1), (10259, 1)] []))])) (by decide +kernel)
theorem hp_10323 : Nat.Prime (512720 ^ 2 + 10323 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262988362729 41 [(2, 3), (3, 2), (7, 1), (13, 1), (29, 1)] [(1384091, 1, (PC.node 1384091 2 [(2, 1), (5, 1), (61, 1), (2269, 1)] []))])) (by decide +kernel)
theorem hp_10333 : Nat.Prime (512720 ^ 2 + 10333 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262988569289 3 [(2, 3)] [(32873571161, 1, (PC.node 32873571161 3 [(2, 3), (5, 1), (17, 1)] [(48343487, 1, (PC.node 48343487 5 [(2, 1), (19, 1), (239, 1), (5323, 1)] []))]))])) (by decide +kernel)
theorem hp_10343 : Nat.Prime (512720 ^ 2 + 10343 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262988776049 3 [(2, 4), (251, 1), (271, 1), (241643, 1)] [])) (by decide +kernel)
theorem hp_10349 : Nat.Prime (512720 ^ 2 + 10349 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262988900201 6 [(2, 3), (5, 2), (13, 1), (113, 1), (283, 1), (3163, 1)] [])) (by decide +kernel)
theorem hp_10357 : Nat.Prime (512720 ^ 2 + 10357 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262989065849 3 [(2, 3), (359, 1), (1063, 1), (86143, 1)] [])) (by decide +kernel)
theorem hp_10371 : Nat.Prime (512720 ^ 2 + 10371 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262989356041 41 [(2, 3), (3, 3), (5, 1), (17, 1), (3557, 1), (4027, 1)] [])) (by decide +kernel)
theorem hp_10373 : Nat.Prime (512720 ^ 2 + 10373 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262989397529 3 [(2, 3), (11, 1), (13, 1), (157, 1)] [(1464241, 1, (PC.node 1464241 17 [(2, 4), (3, 1), (5, 1), (6101, 1)] []))])) (by decide +kernel)
theorem hp_10377 : Nat.Prime (512720 ^ 2 + 10377 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262989480529 11 [(2, 4), (3, 2), (235441, 1), (7757, 1)] [])) (by decide +kernel)
theorem hp_10379 : Nat.Prime (512720 ^ 2 + 10379 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262989522041 3 [(2, 3), (5, 1), (7, 1), (37, 1), (61, 1), (416149, 1)] [])) (by decide +kernel)
theorem hp_10391 : Nat.Prime (512720 ^ 2 + 10391 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262989771281 3 [(2, 4), (5, 1)] [(3287372141, 1, (PC.node 3287372141 3 [(2, 2), (5, 1), (13, 1), (29, 1), (127, 1), (3433, 1)] []))])) (by decide +kernel)
theorem hp_10407 : Nat.Prime (512720 ^ 2 + 10407 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262990104049 19 [(2, 4), (3, 4), (7, 1)] [(28989209, 1, (PC.node 28989209 3 [(2, 3), (79, 1), (45869, 1)] []))])) (by decide +kernel)
theorem hp_10429 : Nat.Prime (512720 ^ 2 + 10429 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262990562441 3 [(2, 3), (5, 1), (23, 1), (59, 1)] [(4845073, 1, (PC.node 4845073 10 [(2, 4), (3, 1), (193, 1), (523, 1)] []))])) (by decide +kernel)
theorem hp_10431 : Nat.Prime (512720 ^ 2 + 10431 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262990604161 7 [(2, 7), (3, 2), (5, 1)] [(45658091, 1, (PC.node 45658091 2 [(2, 1), (5, 1), (17, 1), (491, 1), (547, 1)] []))])) (by decide +kernel)
theorem hp_10433 : Nat.Prime (512720 ^ 2 + 10433 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262990645889 3 [(2, 7)] [(2054614421, 1, (PC.node 2054614421 2 [(2, 2), (5, 1)] [(102730721, 1, (PC.node 102730721 13 [(2, 5), (5, 1), (19, 1), (47, 1), (719, 1)] []))]))])) (by decide +kernel)
theorem hp_10453 : Nat.Prime (512720 ^ 2 + 10453 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262991063609 3 [(2, 3), (7, 1), (13, 1), (37, 1)] [(9763553, 1, (PC.node 9763553 3 [(2, 5), (305111, 1)] []))])) (by decide +kernel)
theorem hp_10473 : Nat.Prime (512720 ^ 2 + 10473 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262991482129 7 [(2, 4), (3, 3), (17, 1), (6337, 1), (5651, 1)] [])) (by decide +kernel)
theorem hp_10483 : Nat.Prime (512720 ^ 2 + 10483 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262991691689 3 [(2, 3), (11, 1), (61, 1), (1553, 1), (31547, 1)] [])) (by decide +kernel)
theorem hp_10499 : Nat.Prime (512720 ^ 2 + 10499 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262992027401 3 [(2, 3), (5, 2), (29, 1), (89, 1), (509477, 1)] [])) (by decide +kernel)
theorem hp_10503 : Nat.Prime (512720 ^ 2 + 10503 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262992111409 7 [(2, 4), (3, 2), (13, 1)] [(140487239, 1, (PC.node 140487239 7 [(2, 1), (41, 1), (569, 1), (3011, 1)] []))])) (by decide +kernel)
theorem hp_10511 : Nat.Prime (512720 ^ 2 + 10511 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262992279521 3 [(2, 5), (5, 1), (31, 1)] [(53022637, 1, (PC.node 53022637 2 [(2, 2), (3, 2), (23, 1), (64037, 1)] []))])) (by decide +kernel)
theorem hp_10519 : Nat.Prime (512720 ^ 2 + 10519 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262992447761 6 [(2, 4), (5, 1), (7, 1)] [(469629371, 1, (PC.node 469629371 2 [(2, 1), (5, 1), (7, 1), (1021, 1), (6571, 1)] []))])) (by decide +kernel)
theorem hp_10521 : Nat.Prime (512720 ^ 2 + 10521 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262992489841 31 [(2, 4), (3, 2), (5, 1), (23, 1), (2161, 1), (7349, 1)] [])) (by decide +kernel)
theorem hp_10531 : Nat.Prime (512720 ^ 2 + 10531 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262992700361 3 [(2, 3), (5, 1), (13, 1), (1889, 1), (267737, 1)] [])) (by decide +kernel)
theorem hp_10563 : Nat.Prime (512720 ^ 2 + 10563 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262993375369 11 [(2, 3), (3, 3), (37, 1), (193, 1), (170503, 1)] [])) (by decide +kernel)
theorem hp_10579 : Nat.Prime (512720 ^ 2 + 10579 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262993713641 6 [(2, 3), (5, 1), (7, 1), (18719, 1), (50177, 1)] [])) (by decide +kernel)
theorem hp_10603 : Nat.Prime (512720 ^ 2 + 10603 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262994222009 3 [(2, 3), (7, 1), (503, 1), (2693, 1), (3467, 1)] [])) (by decide +kernel)
theorem hp_10619 : Nat.Prime (512720 ^ 2 + 10619 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262994561561 3 [(2, 3), (5, 1)] [(6574864039, 1, (PC.node 6574864039 7 [(2, 1), (3, 1)] [(1095810673, 1, (PC.node 1095810673 10 [(2, 4), (3, 1), (11, 1), (317, 1), (6547, 1)] []))]))])) (by decide +kernel)
theorem hp_10637 : Nat.Prime (512720 ^ 2 + 10637 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262994944169 3 [(2, 3), (11, 1), (37, 1)] [(80772403, 1, (PC.node 80772403 2 [(2, 1), (3, 1), (383, 1), (35149, 1)] []))])) (by decide +kernel)
theorem hp_10649 : Nat.Prime (512720 ^ 2 + 10649 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262995199601 11 [(2, 4), (5, 2), (7, 1)] [(93926857, 1, (PC.node 93926857 5 [(2, 3), (3, 1), (941, 1), (4159, 1)] []))])) (by decide +kernel)
theorem hp_10653 : Nat.Prime (512720 ^ 2 + 10653 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262995284809 7 [(2, 3), (3, 4)] [(405856921, 1, (PC.node 405856921 22 [(2, 3), (3, 1), (5, 1), (7, 1), (483163, 1)] []))])) (by decide +kernel)
theorem hp_10661 : Nat.Prime (512720 ^ 2 + 10661 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262995455321 3 [(2, 3), (5, 1), (13, 1)] [(505760491, 1, (PC.node 505760491 3 [(2, 1), (3, 3), (5, 1), (199, 1), (9413, 1)] []))])) (by decide +kernel)
theorem hp_10667 : Nat.Prime (512720 ^ 2 + 10667 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262995583289 3 [(2, 3), (193, 1), (317, 1), (537331, 1)] [])) (by decide +kernel)
theorem hp_10697 : Nat.Prime (512720 ^ 2 + 10697 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262996224209 3 [(2, 4), (31, 2), (2063, 1), (8291, 1)] [])) (by decide +kernel)
theorem hp_10703 : Nat.Prime (512720 ^ 2 + 10703 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262996352609 3 [(2, 5), (11, 1), (149, 1)] [(5014421, 1, (PC.node 5014421 2 [(2, 2), (5, 1), (250721, 1)] []))])) (by decide +kernel)
theorem hp_10709 : Nat.Prime (512720 ^ 2 + 10709 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262996481081 3 [(2, 3), (5, 1), (17, 1), (50053, 1), (7727, 1)] [])) (by decide +kernel)
theorem hp_10711 : Nat.Prime (512720 ^ 2 + 10711 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262996523921 3 [(2, 4), (5, 1), (13, 1), (17, 1), (37, 1), (402037, 1)] [])) (by decide +kernel)
theorem hp_10721 : Nat.Prime (512720 ^ 2 + 10721 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262996738241 3 [(2, 6), (5, 1), (389, 1), (461, 1), (4583, 1)] [])) (by decide +kernel)
theorem hp_10729 : Nat.Prime (512720 ^ 2 + 10729 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262996909841 3 [(2, 4), (5, 1), (7, 1), (29, 1)] [(16194391, 1, (PC.node 16194391 6 [(2, 1), (3, 1), (5, 1), (71, 1), (7603, 1)] []))])) (by decide +kernel)
theorem hp_10739 : Nat.Prime (512720 ^ 2 + 10739 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262997124521 3 [(2, 3), (5, 1), (13, 1)] [(505763701, 1, (PC.node 505763701 2 [(2, 2), (3, 1), (5, 2), (13, 1), (41, 1), (3163, 1)] []))])) (by decide +kernel)
theorem hp_10741 : Nat.Prime (512720 ^ 2 + 10741 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262997167481 3 [(2, 3), (5, 1), (251, 1)] [(26194937, 1, (PC.node 26194937 3 [(2, 3)] [(3274367, 1, (PC.node 3274367 5 [(2, 1)] [(1637183, 1, (PC.node 1637183 5 [(2, 1), (43, 1), (19037, 1)] []))]))]))])) (by decide +kernel)
theorem hp_10789 : Nat.Prime (512720 ^ 2 + 10789 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262998200921 3 [(2, 3), (5, 1), (7, 1), (13, 1), (29, 1)] [(2491457, 1, (PC.node 2491457 3 [(2, 6), (11, 1), (3539, 1)] []))])) (by decide +kernel)
theorem hp_10791 : Nat.Prime (512720 ^ 2 + 10791 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262998244081 14 [(2, 4), (3, 2), (5, 1), (11, 1), (13, 1), (163, 1), (15671, 1)] [])) (by decide +kernel)
theorem hp_10793 : Nat.Prime (512720 ^ 2 + 10793 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262998287249 3 [(2, 4)] [(16437392953, 1, (PC.node 16437392953 5 [(2, 3), (3, 1), (3769, 1), (181717, 1)] []))])) (by decide +kernel)
theorem hp_10801 : Nat.Prime (512720 ^ 2 + 10801 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262998460001 3 [(2, 5), (5, 4), (113, 1), (116371, 1)] [])) (by decide +kernel)
theorem hp_10811 : Nat.Prime (512720 ^ 2 + 10811 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262998676121 6 [(2, 3), (5, 1), (17, 1), (59, 1)] [(6555301, 1, (PC.node 6555301 2 [(2, 2), (3, 1), (5, 2), (21851, 1)] []))])) (by decide +kernel)
theorem hp_10827 : Nat.Prime (512720 ^ 2 + 10827 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262999022329 22 [(2, 3), (3, 2), (7, 1), (1249, 1), (417793, 1)] [])) (by decide +kernel)
theorem hp_10837 : Nat.Prime (512720 ^ 2 + 10837 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262999238969 3 [(2, 3)] [(32874904871, 1, (PC.node 32874904871 7 [(2, 1), (5, 1), (23, 1)] [(142934369, 1, (PC.node 142934369 6 [(2, 5), (17, 1), (262747, 1)] []))]))])) (by decide +kernel)
theorem hp_10869 : Nat.Prime (512720 ^ 2 + 10869 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262999933561 11 [(2, 3), (3, 4), (5, 1), (7, 1), (13, 1), (23, 1), (38783, 1)] [])) (by decide +kernel)
theorem hp_10871 : Nat.Prime (512720 ^ 2 + 10871 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 262999977041 6 [(2, 4), (5, 1)] [(3287499713, 1, (PC.node 3287499713 3 [(2, 6), (7, 1), (17, 1), (431657, 1)] []))])) (by decide +kernel)
theorem hp_10903 : Nat.Prime (512720 ^ 2 + 10903 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263000673809 3 [(2, 4), (29, 1), (1063, 1), (533219, 1)] [])) (by decide +kernel)
theorem hp_10929 : Nat.Prime (512720 ^ 2 + 10929 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263001241441 19 [(2, 5), (3, 3), (5, 1), (7, 1), (59, 1), (147409, 1)] [])) (by decide +kernel)
theorem hp_10943 : Nat.Prime (512720 ^ 2 + 10943 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263001547649 3 [(2, 7), (7, 1)] [(293528513, 1, (PC.node 293528513 3 [(2, 6), (41, 1), (111863, 1)] []))])) (by decide +kernel)
theorem hp_10947 : Nat.Prime (512720 ^ 2 + 10947 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263001635209 7 [(2, 3), (3, 5), (13, 1), (17, 1), (97, 1), (6311, 1)] [])) (by decide +kernel)
theorem hp_10949 : Nat.Prime (512720 ^ 2 + 10949 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263001679001 3 [(2, 3), (5, 3), (17, 1), (71, 1), (193, 1), (1129, 1)] [])) (by decide +kernel)
theorem hp_10951 : Nat.Prime (512720 ^ 2 + 10951 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263001722801 3 [(2, 4), (5, 2), (3877, 1), (169591, 1)] [])) (by decide +kernel)
theorem hp_10953 : Nat.Prime (512720 ^ 2 + 10953 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263001766609 11 [(2, 4), (3, 2), (7, 2), (1123, 1), (33191, 1)] [])) (by decide +kernel)
theorem hp_10957 : Nat.Prime (512720 ^ 2 + 10957 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263001854249 3 [(2, 3), (7, 1)] [(4696461683, 1, (PC.node 4696461683 2 [(2, 1), (11, 1)] [(213475531, 1, (PC.node 213475531 2 [(2, 1), (3, 1), (5, 1), (701, 1), (10151, 1)] []))]))])) (by decide +kernel)
theorem hp_10961 : Nat.Prime (512720 ^ 2 + 10961 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263001941921 3 [(2, 5), (5, 1), (23, 1), (29, 1), (373, 1), (6607, 1)] [])) (by decide +kernel)
theorem hp_10987 : Nat.Prime (512720 ^ 2 + 10987 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263002512569 3 [(2, 3)] [(32875314071, 1, (PC.node 32875314071 17 [(2, 1), (5, 1), (257, 1)] [(12791951, 1, (PC.node 12791951 7 [(2, 1), (5, 2), (255839, 1)] []))]))])) (by decide +kernel)
theorem hp_11001 : Nat.Prime (512720 ^ 2 + 11001 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263002820401 14 [(2, 4), (3, 4), (5, 2), (149, 1), (157, 1), (347, 1)] [])) (by decide +kernel)
theorem hp_11029 : Nat.Prime (512720 ^ 2 + 11029 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263003437241 3 [(2, 3), (5, 1)] [(6575085931, 1, (PC.node 6575085931 7 [(2, 1), (3, 1), (5, 1), (7, 1), (89, 1), (351797, 1)] []))])) (by decide +kernel)
theorem hp_11043 : Nat.Prime (512720 ^ 2 + 11043 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263003746249 7 [(2, 3), (3, 2), (31267, 1), (116827, 1)] [])) (by decide +kernel)
theorem hp_11069 : Nat.Prime (512720 ^ 2 + 11069 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263004321161 3 [(2, 3), (5, 1), (7, 1), (31, 1), (73, 1), (415069, 1)] [])) (by decide +kernel)
theorem hp_11081 : Nat.Prime (512720 ^ 2 + 11081 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263004586961 3 [(2, 4), (5, 1), (37, 1), (10691, 1), (8311, 1)] [])) (by decide +kernel)
theorem hp_11087 : Nat.Prime (512720 ^ 2 + 11087 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263004719969 3 [(2, 5), (829, 1), (1013, 1), (9787, 1)] [])) (by decide +kernel)
theorem hp_11093 : Nat.Prime (512720 ^ 2 + 11093 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263004853049 3 [(2, 3), (7, 1), (61, 1), (313, 1), (245981, 1)] [])) (by decide +kernel)
theorem hp_11097 : Nat.Prime (512720 ^ 2 + 11097 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263004941809 31 [(2, 4), (3, 2), (7, 3), (383, 1), (13903, 1)] [])) (by decide +kernel)
theorem hp_11111 : Nat.Prime (512720 ^ 2 + 11111 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263005252721 3 [(2, 4), (5, 1), (7, 1), (61, 1), (859, 1), (8963, 1)] [])) (by decide +kernel)
theorem hp_11117 : Nat.Prime (512720 ^ 2 + 11117 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263005386089 3 [(2, 3), (17, 1), (163, 1), (383, 1), (30977, 1)] [])) (by decide +kernel)
theorem hp_11119 : Nat.Prime (512720 ^ 2 + 11119 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263005430561 6 [(2, 5), (5, 1), (17, 1), (23, 1), (37, 1), (113623, 1)] [])) (by decide +kernel)
theorem hp_11147 : Nat.Prime (512720 ^ 2 + 11147 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006054009 3 [(2, 3), (44797, 1), (733883, 1)] [])) (by decide +kernel)
theorem hp_11149 : Nat.Prime (512720 ^ 2 + 11149 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006098601 6 [(2, 3), (5, 2), (7, 2)] [(26837357, 1, (PC.node 26837357 3 [(2, 2), (7, 1), (13, 1), (17, 1), (4337, 1)] []))])) (by decide +kernel)
theorem hp_11153 : Nat.Prime (512720 ^ 2 + 11153 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006187809 3 [(2, 5), (7, 1), (13, 2), (17, 1), (349, 1), (1171, 1)] [])) (by decide +kernel)
theorem hp_11159 : Nat.Prime (512720 ^ 2 + 11159 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006321681 3 [(2, 4), (5, 1), (283, 1)] [(11616887, 1, (PC.node 11616887 5 [(2, 1), (23, 1), (252541, 1)] []))])) (by decide +kernel)
theorem hp_11161 : Nat.Prime (512720 ^ 2 + 11161 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006366321 3 [(2, 4), (5, 1)] [(3287579579, 1, (PC.node 3287579579 2 [(2, 1), (17, 1), (2293, 1), (42169, 1)] []))])) (by decide +kernel)
theorem hp_11163 : Nat.Prime (512720 ^ 2 + 11163 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006410969 37 [(2, 3), (3, 4), (7, 1)] [(57982013, 1, (PC.node 57982013 2 [(2, 2), (11, 1)] [(1317773, 1, (PC.node 1317773 3 [(2, 2), (17, 1), (19379, 1)] []))]))])) (by decide +kernel)
theorem hp_11171 : Nat.Prime (512720 ^ 2 + 11171 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006589641 3 [(2, 3), (5, 1), (101, 1), (1367, 1), (47623, 1)] [])) (by decide +kernel)
theorem hp_11177 : Nat.Prime (512720 ^ 2 + 11177 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006723729 3 [(2, 4), (7, 1)] [(2348274319, 1, (PC.node 2348274319 3 [(2, 1), (3, 1), (13, 1), (409, 1), (73609, 1)] []))])) (by decide +kernel)
theorem hp_11183 : Nat.Prime (512720 ^ 2 + 11183 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263006857889 3 [(2, 5), (349, 1), (359, 1), (65599, 1)] [])) (by decide +kernel)
theorem hp_11199 : Nat.Prime (512720 ^ 2 + 11199 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263007216001 14 [(2, 7), (3, 3), (5, 3), (601, 1), (1013, 1)] [])) (by decide +kernel)
theorem hp_11209 : Nat.Prime (512720 ^ 2 + 11209 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263007440081 3 [(2, 4), (5, 1), (7, 1), (11, 1), (3257, 1), (13109, 1)] [])) (by decide +kernel)
theorem hp_11213 : Nat.Prime (512720 ^ 2 + 11213 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263007529769 3 [(2, 3), (106703, 1), (308107, 1)] [])) (by decide +kernel)
theorem hp_11221 : Nat.Prime (512720 ^ 2 + 11221 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263007709241 3 [(2, 3), (5, 1), (17, 1), (569, 1), (679747, 1)] [])) (by decide +kernel)
theorem hp_11233 : Nat.Prime (512720 ^ 2 + 11233 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263007978689 3 [(2, 6), (7, 1), (13, 1), (61, 1), (71, 1), (10427, 1)] [])) (by decide +kernel)
theorem hp_11259 : Nat.Prime (512720 ^ 2 + 11259 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263008563481 19 [(2, 3), (3, 2), (5, 1), (13, 1), (1553, 1), (36187, 1)] [])) (by decide +kernel)
theorem hp_11261 : Nat.Prime (512720 ^ 2 + 11261 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263008608521 3 [(2, 3), (5, 1), (7, 1), (599, 1)] [(1568141, 1, (PC.node 1568141 10 [(2, 2), (5, 1), (7, 1), (23, 1), (487, 1)] []))])) (by decide +kernel)
theorem hp_11273 : Nat.Prime (512720 ^ 2 + 11273 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263008878929 3 [(2, 4), (2621, 1)] [(6271673, 1, (PC.node 6271673 5 [(2, 3), (11, 3), (19, 1), (31, 1)] []))])) (by decide +kernel)
theorem hp_11283 : Nat.Prime (512720 ^ 2 + 11283 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263009104489 7 [(2, 3), (3, 3), (13, 1), (23, 2), (59, 1), (3001, 1)] [])) (by decide +kernel)
theorem hp_11289 : Nat.Prime (512720 ^ 2 + 11289 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263009239921 11 [(2, 4), (3, 3), (5, 1), (7, 1), (17, 1), (457, 1), (2239, 1)] [])) (by decide +kernel)
theorem hp_11291 : Nat.Prime (512720 ^ 2 + 11291 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263009285081 3 [(2, 3), (5, 1), (883, 1)] [(7446469, 1, (PC.node 7446469 10 [(2, 2), (3, 1), (419, 1), (1481, 1)] []))])) (by decide +kernel)
theorem hp_11299 : Nat.Prime (512720 ^ 2 + 11299 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263009465801 6 [(2, 3), (5, 2), (149, 1)] [(8825821, 1, (PC.node 8825821 2 [(2, 2), (3, 1), (5, 1), (147097, 1)] []))])) (by decide +kernel)
theorem hp_11313 : Nat.Prime (512720 ^ 2 + 11313 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263009782369 7 [(2, 5), (3, 2), (31, 1)] [(29458981, 1, (PC.node 29458981 2 [(2, 2), (3, 2), (5, 1), (163661, 1)] []))])) (by decide +kernel)
theorem hp_11321 : Nat.Prime (512720 ^ 2 + 11321 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263009963441 3 [(2, 4), (5, 1), (7, 1), (17, 1), (491, 1), (56267, 1)] [])) (by decide +kernel)
theorem hp_11331 : Nat.Prime (512720 ^ 2 + 11331 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263010189961 33 [(2, 3), (3, 2), (5, 1), (7, 1), (139, 1), (750857, 1)] [])) (by decide +kernel)
theorem hp_11387 : Nat.Prime (512720 ^ 2 + 11387 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263011462169 3 [(2, 3), (7, 1), (13, 1), (2383, 1), (151607, 1)] [])) (by decide +kernel)
theorem hp_11411 : Nat.Prime (512720 ^ 2 + 11411 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263012009321 3 [(2, 3), (5, 1), (1997, 1)] [(3292589, 1, (PC.node 3292589 2 [(2, 2), (13, 1), (23, 1), (2753, 1)] []))])) (by decide +kernel)
theorem hp_11443 : Nat.Prime (512720 ^ 2 + 11443 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263012740649 3 [(2, 3), (7, 2), (163, 1), (313, 1), (13151, 1)] [])) (by decide +kernel)
theorem hp_11467 : Nat.Prime (512720 ^ 2 + 11467 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263013290489 3 [(2, 3), (13, 1), (23, 1), (1669, 1), (65881, 1)] [])) (by decide +kernel)
theorem hp_11469 : Nat.Prime (512720 ^ 2 + 11469 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263013336361 14 [(2, 3), (3, 3), (5, 1)] [(243530867, 1, (PC.node 243530867 2 [(2, 1), (19, 1), (53, 1), (120919, 1)] []))])) (by decide +kernel)
theorem hp_11481 : Nat.Prime (512720 ^ 2 + 11481 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263013611761 11 [(2, 4), (3, 3), (5, 1), (283, 1), (430267, 1)] [])) (by decide +kernel)
theorem hp_11487 : Nat.Prime (512720 ^ 2 + 11487 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263013749569 22 [(2, 6), (3, 4), (23, 1), (71, 1), (31069, 1)] [])) (by decide +kernel)
theorem hp_11489 : Nat.Prime (512720 ^ 2 + 11489 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263013795521 3 [(2, 6), (5, 1), (7, 2), (37, 1), (453347, 1)] [])) (by decide +kernel)
theorem hp_11503 : Nat.Prime (512720 ^ 2 + 11503 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263014117409 3 [(2, 5), (7, 1), (31, 1)] [(37876457, 1, (PC.node 37876457 3 [(2, 3), (37, 1), (41, 1), (3121, 1)] []))])) (by decide +kernel)
theorem hp_11507 : Nat.Prime (512720 ^ 2 + 11507 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263014209449 3 [(2, 3), (73, 1), (1123, 1), (401039, 1)] [])) (by decide +kernel)
theorem hp_11517 : Nat.Prime (512720 ^ 2 + 11517 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263014439689 76 [(2, 3), (3, 4), (7, 1), (11, 1), (13, 1), (71, 1), (5711, 1)] [])) (by decide +kernel)
theorem hp_11523 : Nat.Prime (512720 ^ 2 + 11523 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263014577929 7 [(2, 3), (3, 3), (317, 1)] [(3841199, 1, (PC.node 3841199 13 [(2, 1)] [(1920599, 1, (PC.node 1920599 7 [(2, 1), (960299, 1)] []))]))])) (by decide +kernel)
theorem hp_11527 : Nat.Prime (512720 ^ 2 + 11527 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263014670129 3 [(2, 4), (7, 1), (17, 1), (2549, 1), (54193, 1)] [])) (by decide +kernel)
theorem hp_11529 : Nat.Prime (512720 ^ 2 + 11529 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263014716241 19 [(2, 4), (3, 2), (5, 1), (97, 1), (503, 1), (7487, 1)] [])) (by decide +kernel)
theorem hp_11553 : Nat.Prime (512720 ^ 2 + 11553 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263015270209 11 [(2, 6), (3, 3)] [(152207911, 1, (PC.node 152207911 3 [(2, 1), (3, 6), (5, 1), (20879, 1)] []))])) (by decide +kernel)
theorem hp_11563 : Nat.Prime (512720 ^ 2 + 11563 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263015501369 3 [(2, 3), (37, 1), (691, 1)] [(1285913, 1, (PC.node 1285913 3 [(2, 3), (160739, 1)] []))])) (by decide +kernel)
theorem hp_11631 : Nat.Prime (512720 ^ 2 + 11631 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263017078561 7 [(2, 5), (3, 3), (5, 1), (1129, 1), (53927, 1)] [])) (by decide +kernel)
theorem hp_11637 : Nat.Prime (512720 ^ 2 + 11637 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263017218169 7 [(2, 3), (3, 2), (37, 1), (59, 1)] [(1673393, 1, (PC.node 1673393 3 [(2, 4), (7, 1), (67, 1), (223, 1)] []))])) (by decide +kernel)
theorem hp_11649 : Nat.Prime (512720 ^ 2 + 11649 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263017497601 7 [(2, 10), (3, 4), (5, 2), (11, 1), (13, 1), (887, 1)] [])) (by decide +kernel)
def S1 : List ℕ := [5921,5931,5939,5947,5959,5961,5973,5977,5981,6011,6033,6037,6051,6053,6059,6081,6083,6109,6111,6129,6131,6139,6147,6159,6161,6163,6181,6211,6219,6241,6243,6249,6281,6287,6289,6291,6297,6299,6303,6309,6311,6337,6377,6389,6391,6397,6407,6411,6417,6433,6439,6441,6453,6457,6469,6481,6489,6491,6493,6499,6503,6521,6533,6543,6567,6569,6571,6577,6599,6611,6623,6637,6649,6653,6657,6659,6661,6693,6711,6723,6751,6809,6811,6813,6823,6829,6839,6847,6863,6871,6881,6887,6899,6907,6951,6971,6973,7013,7029,7039,7041,7051,7061,7063,7079,7113,7117,7121,7141,7147,7167,7181,7183,7193,7197,7253,7257,7263,7273,7283,7291,7311,7317,7339,7341,7343,7349,7357,7367,7369,7381,7393,7401,7407,7411,7421,7439,7441,7457,7461,7489,7509,7513,7543,7561,7583,7587,7601,7603,7617,7623,7637,7659,7663,7671,7673,7687,7697,7699,7707,7713,7717,7733,7757,7779,7783,7789,7791,7821,7827,7829,7853,7857,7861,7867,7869,7893,7907,7909,7913,7919,7921,7941,7967,7979,7981,7989,7991,8023,8029,8039,8051,8067,8071,8093,8097,8119,8137,8157,8161,8183,8187,8191,8209,8221,8233,8239,8251,8257,8299,8331,8349,8357,8363,8371,8377,8379,8387,8389,8399,8413,8423,8431,8447,8467,8479,8503,8513,8521,8523,8533,8543,8547,8559,8569,8589,8603,8611,8637,8647,8657,8667,8673,8689,8693,8711,8717,8719,8727,8739,8757,8759,8771,8781,8783,8793,8817,8837,8849,8859,8867,8873,8893,8917,8973,8989,9011,9013,9021,9031,9041,9043,9063,9079,9081,9083,9091,9093,9097,9111,9151,9153,9157,9159,9167,9171,9179,9209,9219,9241,9247,9249,9253,9257,9277,9293,9297,9307,9329,9339,9363,9371,9381,9387,9393,9403,9411,9417,9453,9467,9471,9487,9489,9511,9519,9539,9549,9563,9569,9587,9593,9601,9619,9621,9627,9629,9641,9661,9663,9667,9669,9671,9677,9683,9687,9691,9709,9731,9747,9749,9781,9791,9807,9817,9821,9823,9837,9847,9857,9863,9899,9903,9913,9917,9931,9933,9941,9949,9959,9967,9973,9993,10017,10021,10029,10031,10069,10091,10097,10099,10119,10143,10151,10181,10189,10191,10193,10201,10211,10213,10227,10233,10259,10269,10271,10313,10317,10323,10333,10343,10349,10357,10371,10373,10377,10379,10391,10407,10429,10431,10433,10453,10473,10483,10499,10503,10511,10519,10521,10531,10563,10579,10603,10619,10637,10649,10653,10661,10667,10697,10703,10709,10711,10721,10729,10739,10741,10789,10791,10793,10801,10811,10827,10837,10869,10871,10903,10929,10943,10947,10949,10951,10953,10957,10961,10987,11001,11029,11043,11069,11081,11087,11093,11097,11111,11117,11119,11147,11149,11153,11159,11161,11163,11171,11177,11183,11199,11209,11213,11221,11233,11259,11261,11273,11283,11289,11291,11299,11313,11321,11331,11387,11411,11443,11467,11469,11481,11487,11489,11503,11507,11517,11523,11527,11529,11553,11563,11631,11637,11649]
theorem hsc1 : Cert.okChainS 512720 5917 S1 = true := by decide +kernel
theorem hff1 : Cert.finalSS 5917 S1 = 11649 := by decide
theorem hpS1 : ∀ s ∈ S1, Nat.Prime (512720 ^ 2 + s ^ 2) := by
  intro s hs
  simp only [S1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp_5921
  · exact hp_5931
  · exact hp_5939
  · exact hp_5947
  · exact hp_5959
  · exact hp_5961
  · exact hp_5973
  · exact hp_5977
  · exact hp_5981
  · exact hp_6011
  · exact hp_6033
  · exact hp_6037
  · exact hp_6051
  · exact hp_6053
  · exact hp_6059
  · exact hp_6081
  · exact hp_6083
  · exact hp_6109
  · exact hp_6111
  · exact hp_6129
  · exact hp_6131
  · exact hp_6139
  · exact hp_6147
  · exact hp_6159
  · exact hp_6161
  · exact hp_6163
  · exact hp_6181
  · exact hp_6211
  · exact hp_6219
  · exact hp_6241
  · exact hp_6243
  · exact hp_6249
  · exact hp_6281
  · exact hp_6287
  · exact hp_6289
  · exact hp_6291
  · exact hp_6297
  · exact hp_6299
  · exact hp_6303
  · exact hp_6309
  · exact hp_6311
  · exact hp_6337
  · exact hp_6377
  · exact hp_6389
  · exact hp_6391
  · exact hp_6397
  · exact hp_6407
  · exact hp_6411
  · exact hp_6417
  · exact hp_6433
  · exact hp_6439
  · exact hp_6441
  · exact hp_6453
  · exact hp_6457
  · exact hp_6469
  · exact hp_6481
  · exact hp_6489
  · exact hp_6491
  · exact hp_6493
  · exact hp_6499
  · exact hp_6503
  · exact hp_6521
  · exact hp_6533
  · exact hp_6543
  · exact hp_6567
  · exact hp_6569
  · exact hp_6571
  · exact hp_6577
  · exact hp_6599
  · exact hp_6611
  · exact hp_6623
  · exact hp_6637
  · exact hp_6649
  · exact hp_6653
  · exact hp_6657
  · exact hp_6659
  · exact hp_6661
  · exact hp_6693
  · exact hp_6711
  · exact hp_6723
  · exact hp_6751
  · exact hp_6809
  · exact hp_6811
  · exact hp_6813
  · exact hp_6823
  · exact hp_6829
  · exact hp_6839
  · exact hp_6847
  · exact hp_6863
  · exact hp_6871
  · exact hp_6881
  · exact hp_6887
  · exact hp_6899
  · exact hp_6907
  · exact hp_6951
  · exact hp_6971
  · exact hp_6973
  · exact hp_7013
  · exact hp_7029
  · exact hp_7039
  · exact hp_7041
  · exact hp_7051
  · exact hp_7061
  · exact hp_7063
  · exact hp_7079
  · exact hp_7113
  · exact hp_7117
  · exact hp_7121
  · exact hp_7141
  · exact hp_7147
  · exact hp_7167
  · exact hp_7181
  · exact hp_7183
  · exact hp_7193
  · exact hp_7197
  · exact hp_7253
  · exact hp_7257
  · exact hp_7263
  · exact hp_7273
  · exact hp_7283
  · exact hp_7291
  · exact hp_7311
  · exact hp_7317
  · exact hp_7339
  · exact hp_7341
  · exact hp_7343
  · exact hp_7349
  · exact hp_7357
  · exact hp_7367
  · exact hp_7369
  · exact hp_7381
  · exact hp_7393
  · exact hp_7401
  · exact hp_7407
  · exact hp_7411
  · exact hp_7421
  · exact hp_7439
  · exact hp_7441
  · exact hp_7457
  · exact hp_7461
  · exact hp_7489
  · exact hp_7509
  · exact hp_7513
  · exact hp_7543
  · exact hp_7561
  · exact hp_7583
  · exact hp_7587
  · exact hp_7601
  · exact hp_7603
  · exact hp_7617
  · exact hp_7623
  · exact hp_7637
  · exact hp_7659
  · exact hp_7663
  · exact hp_7671
  · exact hp_7673
  · exact hp_7687
  · exact hp_7697
  · exact hp_7699
  · exact hp_7707
  · exact hp_7713
  · exact hp_7717
  · exact hp_7733
  · exact hp_7757
  · exact hp_7779
  · exact hp_7783
  · exact hp_7789
  · exact hp_7791
  · exact hp_7821
  · exact hp_7827
  · exact hp_7829
  · exact hp_7853
  · exact hp_7857
  · exact hp_7861
  · exact hp_7867
  · exact hp_7869
  · exact hp_7893
  · exact hp_7907
  · exact hp_7909
  · exact hp_7913
  · exact hp_7919
  · exact hp_7921
  · exact hp_7941
  · exact hp_7967
  · exact hp_7979
  · exact hp_7981
  · exact hp_7989
  · exact hp_7991
  · exact hp_8023
  · exact hp_8029
  · exact hp_8039
  · exact hp_8051
  · exact hp_8067
  · exact hp_8071
  · exact hp_8093
  · exact hp_8097
  · exact hp_8119
  · exact hp_8137
  · exact hp_8157
  · exact hp_8161
  · exact hp_8183
  · exact hp_8187
  · exact hp_8191
  · exact hp_8209
  · exact hp_8221
  · exact hp_8233
  · exact hp_8239
  · exact hp_8251
  · exact hp_8257
  · exact hp_8299
  · exact hp_8331
  · exact hp_8349
  · exact hp_8357
  · exact hp_8363
  · exact hp_8371
  · exact hp_8377
  · exact hp_8379
  · exact hp_8387
  · exact hp_8389
  · exact hp_8399
  · exact hp_8413
  · exact hp_8423
  · exact hp_8431
  · exact hp_8447
  · exact hp_8467
  · exact hp_8479
  · exact hp_8503
  · exact hp_8513
  · exact hp_8521
  · exact hp_8523
  · exact hp_8533
  · exact hp_8543
  · exact hp_8547
  · exact hp_8559
  · exact hp_8569
  · exact hp_8589
  · exact hp_8603
  · exact hp_8611
  · exact hp_8637
  · exact hp_8647
  · exact hp_8657
  · exact hp_8667
  · exact hp_8673
  · exact hp_8689
  · exact hp_8693
  · exact hp_8711
  · exact hp_8717
  · exact hp_8719
  · exact hp_8727
  · exact hp_8739
  · exact hp_8757
  · exact hp_8759
  · exact hp_8771
  · exact hp_8781
  · exact hp_8783
  · exact hp_8793
  · exact hp_8817
  · exact hp_8837
  · exact hp_8849
  · exact hp_8859
  · exact hp_8867
  · exact hp_8873
  · exact hp_8893
  · exact hp_8917
  · exact hp_8973
  · exact hp_8989
  · exact hp_9011
  · exact hp_9013
  · exact hp_9021
  · exact hp_9031
  · exact hp_9041
  · exact hp_9043
  · exact hp_9063
  · exact hp_9079
  · exact hp_9081
  · exact hp_9083
  · exact hp_9091
  · exact hp_9093
  · exact hp_9097
  · exact hp_9111
  · exact hp_9151
  · exact hp_9153
  · exact hp_9157
  · exact hp_9159
  · exact hp_9167
  · exact hp_9171
  · exact hp_9179
  · exact hp_9209
  · exact hp_9219
  · exact hp_9241
  · exact hp_9247
  · exact hp_9249
  · exact hp_9253
  · exact hp_9257
  · exact hp_9277
  · exact hp_9293
  · exact hp_9297
  · exact hp_9307
  · exact hp_9329
  · exact hp_9339
  · exact hp_9363
  · exact hp_9371
  · exact hp_9381
  · exact hp_9387
  · exact hp_9393
  · exact hp_9403
  · exact hp_9411
  · exact hp_9417
  · exact hp_9453
  · exact hp_9467
  · exact hp_9471
  · exact hp_9487
  · exact hp_9489
  · exact hp_9511
  · exact hp_9519
  · exact hp_9539
  · exact hp_9549
  · exact hp_9563
  · exact hp_9569
  · exact hp_9587
  · exact hp_9593
  · exact hp_9601
  · exact hp_9619
  · exact hp_9621
  · exact hp_9627
  · exact hp_9629
  · exact hp_9641
  · exact hp_9661
  · exact hp_9663
  · exact hp_9667
  · exact hp_9669
  · exact hp_9671
  · exact hp_9677
  · exact hp_9683
  · exact hp_9687
  · exact hp_9691
  · exact hp_9709
  · exact hp_9731
  · exact hp_9747
  · exact hp_9749
  · exact hp_9781
  · exact hp_9791
  · exact hp_9807
  · exact hp_9817
  · exact hp_9821
  · exact hp_9823
  · exact hp_9837
  · exact hp_9847
  · exact hp_9857
  · exact hp_9863
  · exact hp_9899
  · exact hp_9903
  · exact hp_9913
  · exact hp_9917
  · exact hp_9931
  · exact hp_9933
  · exact hp_9941
  · exact hp_9949
  · exact hp_9959
  · exact hp_9967
  · exact hp_9973
  · exact hp_9993
  · exact hp_10017
  · exact hp_10021
  · exact hp_10029
  · exact hp_10031
  · exact hp_10069
  · exact hp_10091
  · exact hp_10097
  · exact hp_10099
  · exact hp_10119
  · exact hp_10143
  · exact hp_10151
  · exact hp_10181
  · exact hp_10189
  · exact hp_10191
  · exact hp_10193
  · exact hp_10201
  · exact hp_10211
  · exact hp_10213
  · exact hp_10227
  · exact hp_10233
  · exact hp_10259
  · exact hp_10269
  · exact hp_10271
  · exact hp_10313
  · exact hp_10317
  · exact hp_10323
  · exact hp_10333
  · exact hp_10343
  · exact hp_10349
  · exact hp_10357
  · exact hp_10371
  · exact hp_10373
  · exact hp_10377
  · exact hp_10379
  · exact hp_10391
  · exact hp_10407
  · exact hp_10429
  · exact hp_10431
  · exact hp_10433
  · exact hp_10453
  · exact hp_10473
  · exact hp_10483
  · exact hp_10499
  · exact hp_10503
  · exact hp_10511
  · exact hp_10519
  · exact hp_10521
  · exact hp_10531
  · exact hp_10563
  · exact hp_10579
  · exact hp_10603
  · exact hp_10619
  · exact hp_10637
  · exact hp_10649
  · exact hp_10653
  · exact hp_10661
  · exact hp_10667
  · exact hp_10697
  · exact hp_10703
  · exact hp_10709
  · exact hp_10711
  · exact hp_10721
  · exact hp_10729
  · exact hp_10739
  · exact hp_10741
  · exact hp_10789
  · exact hp_10791
  · exact hp_10793
  · exact hp_10801
  · exact hp_10811
  · exact hp_10827
  · exact hp_10837
  · exact hp_10869
  · exact hp_10871
  · exact hp_10903
  · exact hp_10929
  · exact hp_10943
  · exact hp_10947
  · exact hp_10949
  · exact hp_10951
  · exact hp_10953
  · exact hp_10957
  · exact hp_10961
  · exact hp_10987
  · exact hp_11001
  · exact hp_11029
  · exact hp_11043
  · exact hp_11069
  · exact hp_11081
  · exact hp_11087
  · exact hp_11093
  · exact hp_11097
  · exact hp_11111
  · exact hp_11117
  · exact hp_11119
  · exact hp_11147
  · exact hp_11149
  · exact hp_11153
  · exact hp_11159
  · exact hp_11161
  · exact hp_11163
  · exact hp_11171
  · exact hp_11177
  · exact hp_11183
  · exact hp_11199
  · exact hp_11209
  · exact hp_11213
  · exact hp_11221
  · exact hp_11233
  · exact hp_11259
  · exact hp_11261
  · exact hp_11273
  · exact hp_11283
  · exact hp_11289
  · exact hp_11291
  · exact hp_11299
  · exact hp_11313
  · exact hp_11321
  · exact hp_11331
  · exact hp_11387
  · exact hp_11411
  · exact hp_11443
  · exact hp_11467
  · exact hp_11469
  · exact hp_11481
  · exact hp_11487
  · exact hp_11489
  · exact hp_11503
  · exact hp_11507
  · exact hp_11517
  · exact hp_11523
  · exact hp_11527
  · exact hp_11529
  · exact hp_11553
  · exact hp_11563
  · exact hp_11631
  · exact hp_11637
  · exact hp_11649

theorem hp_11691 : Nat.Prime (512720 ^ 2 + 11691 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263018477881 21 [(2, 3), (3, 2), (5, 1), (6367, 1), (114749, 1)] [])) (by decide +kernel)
theorem hp_11701 : Nat.Prime (512720 ^ 2 + 11701 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263018711801 3 [(2, 3), (5, 2), (13, 1)] [(101161043, 1, (PC.node 101161043 2 [(2, 1)] [(50580521, 1, (PC.node 50580521 3 [(2, 3), (5, 1), (317, 1), (3989, 1)] []))]))])) (by decide +kernel)
theorem hp_11707 : Nat.Prime (512720 ^ 2 + 11707 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263018852249 3 [(2, 3), (73, 1), (373, 1)] [(1207439, 1, (PC.node 1207439 7 [(2, 1), (603719, 1)] []))])) (by decide +kernel)
theorem hp_11717 : Nat.Prime (512720 ^ 2 + 11717 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263019086489 6 [(2, 3), (23, 1), (29, 1)] [(49291433, 1, (PC.node 49291433 3 [(2, 3), (17, 1), (59, 1), (6143, 1)] []))])) (by decide +kernel)
theorem hp_11719 : Nat.Prime (512720 ^ 2 + 11719 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263019133361 3 [(2, 4), (5, 1), (313, 1)] [(10503959, 1, (PC.node 10503959 7 [(2, 1), (89, 1), (59011, 1)] []))])) (by decide +kernel)
theorem hp_11753 : Nat.Prime (512720 ^ 2 + 11753 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263019931409 3 [(2, 4), (13, 1)] [(1264518901, 1, (PC.node 1264518901 2 [(2, 2), (3, 2), (5, 2), (29, 1), (48449, 1)] []))])) (by decide +kernel)
theorem hp_11757 : Nat.Prime (512720 ^ 2 + 11757 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263020025449 7 [(2, 3), (3, 5)] [(135298367, 1, (PC.node 135298367 5 [(2, 1), (7, 1), (61, 1), (158429, 1)] []))])) (by decide +kernel)
theorem hp_11761 : Nat.Prime (512720 ^ 2 + 11761 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263020119521 3 [(2, 5), (5, 1), (80107, 1), (20521, 1)] [])) (by decide +kernel)
theorem hp_11767 : Nat.Prime (512720 ^ 2 + 11767 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263020260689 3 [(2, 4), (52807, 1), (311299, 1)] [])) (by decide +kernel)
theorem hp_11769 : Nat.Prime (512720 ^ 2 + 11769 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263020307761 23 [(2, 4), (3, 3), (5, 1), (7, 1), (163, 1), (106721, 1)] [])) (by decide +kernel)
theorem hp_11813 : Nat.Prime (512720 ^ 2 + 11813 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263021345369 3 [(2, 3), (31, 1)] [(1060569941, 1, (PC.node 1060569941 2 [(2, 2), (5, 1)] [(53028497, 1, (PC.node 53028497 3 [(2, 4)] [(3314281, 1, (PC.node 3314281 14 [(2, 3), (3, 1), (5, 1), (71, 1), (389, 1)] []))]))]))])) (by decide +kernel)
theorem hp_11827 : Nat.Prime (512720 ^ 2 + 11827 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263021676329 3 [(2, 3)] [(32877709541, 1, (PC.node 32877709541 2 [(2, 2), (5, 1), (13, 4), (57557, 1)] []))])) (by decide +kernel)
theorem hp_11863 : Nat.Prime (512720 ^ 2 + 11863 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263022529169 3 [(2, 4), (7, 1), (383, 1), (563, 1), (10891, 1)] [])) (by decide +kernel)
theorem hp_11871 : Nat.Prime (512720 ^ 2 + 11871 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263022719041 7 [(2, 6), (3, 2), (5, 1), (31, 1)] [(2946043, 1, (PC.node 2946043 5 [(2, 1), (3, 2), (11, 1), (14879, 1)] []))])) (by decide +kernel)
theorem hp_11889 : Nat.Prime (512720 ^ 2 + 11889 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263023146721 14 [(2, 5), (3, 2), (5, 1), (29, 1)] [(6298447, 1, (PC.node 6298447 3 [(2, 1), (3, 1), (7, 1), (11, 1), (13633, 1)] []))])) (by decide +kernel)
theorem hp_11897 : Nat.Prime (512720 ^ 2 + 11897 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263023337009 3 [(2, 4)] [(16438958563, 1, (PC.node 16438958563 3 [(2, 1), (3, 1), (13, 1)] [(210755879, 1, (PC.node 210755879 11 [(2, 1), (53, 1)] [(1988263, 1, (PC.node 1988263 5 [(2, 1), (3, 2), (110459, 1)] []))]))]))])) (by decide +kernel)
theorem hp_11901 : Nat.Prime (512720 ^ 2 + 11901 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263023432201 11 [(2, 3), (3, 3), (5, 2), (17, 1), (23, 1), (347, 1), (359, 1)] [])) (by decide +kernel)
theorem hp_11931 : Nat.Prime (512720 ^ 2 + 11931 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263024147161 11 [(2, 3), (3, 3), (5, 1), (113, 1), (691, 1), (3119, 1)] [])) (by decide +kernel)
theorem hp_11941 : Nat.Prime (512720 ^ 2 + 11941 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263024385881 3 [(2, 3), (5, 1), (509, 1)] [(12918683, 1, (PC.node 12918683 2 [(2, 1), (7, 1), (199, 1), (4637, 1)] []))])) (by decide +kernel)
theorem hp_11949 : Nat.Prime (512720 ^ 2 + 11949 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263024577001 19 [(2, 3), (3, 4), (5, 3), (29, 1), (111973, 1)] [])) (by decide +kernel)
theorem hp_11953 : Nat.Prime (512720 ^ 2 + 11953 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263024672609 3 [(2, 5), (8669, 1), (948151, 1)] [])) (by decide +kernel)
theorem hp_11987 : Nat.Prime (512720 ^ 2 + 11987 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263025486569 3 [(2, 3), (13, 1), (227, 1)] [(11141371, 1, (PC.node 11141371 31 [(2, 1), (3, 2), (5, 1), (79, 1), (1567, 1)] []))])) (by decide +kernel)
theorem hp_11993 : Nat.Prime (512720 ^ 2 + 11993 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263025630449 3 [(2, 4), (7, 1), (23, 2)] [(4439401, 1, (PC.node 4439401 19 [(2, 3), (3, 1), (5, 2), (7, 2), (151, 1)] []))])) (by decide +kernel)
theorem hp_12003 : Nat.Prime (512720 ^ 2 + 12003 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263025870409 43 [(2, 3), (3, 4), (7, 1), (17, 1), (479, 1), (7121, 1)] [])) (by decide +kernel)
theorem hp_12031 : Nat.Prime (512720 ^ 2 + 12031 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263026543361 15 [(2, 8), (5, 1), (7, 2)] [(4193663, 1, (PC.node 4193663 5 [(2, 1), (11, 1), (17, 1), (11213, 1)] []))])) (by decide +kernel)
theorem hp_12037 : Nat.Prime (512720 ^ 2 + 12037 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263026687769 3 [(2, 3), (13, 1), (17, 1)] [(148770751, 1, (PC.node 148770751 3 [(2, 1), (3, 1), (5, 3), (293, 1), (677, 1)] []))])) (by decide +kernel)
theorem hp_12039 : Nat.Prime (512720 ^ 2 + 12039 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263026735921 7 [(2, 4), (3, 3), (5, 1), (13, 1), (23, 1), (407263, 1)] [])) (by decide +kernel)
theorem hp_12041 : Nat.Prime (512720 ^ 2 + 12041 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263026784081 6 [(2, 4), (5, 1), (127, 1)] [(25888463, 1, (PC.node 25888463 5 [(2, 1)] [(12944231, 1, (PC.node 12944231 11 [(2, 1), (5, 1), (13, 1), (99571, 1)] []))]))])) (by decide +kernel)
theorem hp_12047 : Nat.Prime (512720 ^ 2 + 12047 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263026928609 3 [(2, 5), (283, 1), (823, 1), (35291, 1)] [])) (by decide +kernel)
theorem hp_12049 : Nat.Prime (512720 ^ 2 + 12049 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263026976801 3 [(2, 5), (5, 2), (7, 1), (701, 1), (67003, 1)] [])) (by decide +kernel)
theorem hp_12063 : Nat.Prime (512720 ^ 2 + 12063 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263027314369 11 [(2, 6), (3, 3), (7, 1), (13, 1), (29, 1), (57679, 1)] [])) (by decide +kernel)
theorem hp_12069 : Nat.Prime (512720 ^ 2 + 12069 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263027459161 7 [(2, 3), (3, 2), (5, 1), (17, 1), (61, 1), (313, 1), (2251, 1)] [])) (by decide +kernel)
theorem hp_12073 : Nat.Prime (512720 ^ 2 + 12073 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263027555729 3 [(2, 4), (7, 1)] [(2348460319, 1, (PC.node 2348460319 6 [(2, 1), (3, 1), (131, 1)] [(2987863, 1, (PC.node 2987863 3 [(2, 1), (3, 1), (497977, 1)] []))]))])) (by decide +kernel)
theorem hp_12089 : Nat.Prime (512720 ^ 2 + 12089 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263027942321 6 [(2, 4), (5, 1), (11, 1), (13, 1), (127, 1), (181039, 1)] [])) (by decide +kernel)
theorem hp_12113 : Nat.Prime (512720 ^ 2 + 12113 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263028523169 3 [(2, 5)] [(8219641349, 1, (PC.node 8219641349 2 [(2, 2)] [(2054910337, 1, (PC.node 2054910337 5 [(2, 7), (3, 1)] [(5351329, 1, (PC.node 5351329 23 [(2, 5), (3, 2), (17, 1), (1093, 1)] []))]))]))])) (by decide +kernel)
theorem hp_12119 : Nat.Prime (512720 ^ 2 + 12119 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263028668561 6 [(2, 4), (5, 1), (7, 1), (31, 1)] [(15151421, 1, (PC.node 15151421 3 [(2, 2), (5, 1), (17, 1), (44563, 1)] []))])) (by decide +kernel)
theorem hp_12127 : Nat.Prime (512720 ^ 2 + 12127 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263028862529 3 [(2, 6), (347143, 1), (11839, 1)] [])) (by decide +kernel)
theorem hp_12131 : Nat.Prime (512720 ^ 2 + 12131 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263028959561 3 [(2, 3), (5, 1), (23, 1), (5651, 1), (50593, 1)] [])) (by decide +kernel)
theorem hp_12133 : Nat.Prime (512720 ^ 2 + 12133 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263029008089 3 [(2, 3), (7, 1), (11, 1), (991, 1), (430873, 1)] [])) (by decide +kernel)
theorem hp_12139 : Nat.Prime (512720 ^ 2 + 12139 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263029153721 3 [(2, 3), (5, 1), (17, 2), (97, 1), (234571, 1)] [])) (by decide +kernel)
theorem hp_12147 : Nat.Prime (512720 ^ 2 + 12147 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263029348009 31 [(2, 3), (3, 3), (7, 1)] [(173961209, 1, (PC.node 173961209 3 [(2, 3)] [(21745151, 1, (PC.node 21745151 7 [(2, 1), (5, 2), (7, 1), (62129, 1)] []))]))])) (by decide +kernel)
theorem hp_12149 : Nat.Prime (512720 ^ 2 + 12149 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263029396601 6 [(2, 3), (5, 2)] [(1315146983, 1, (PC.node 1315146983 5 [(2, 1), (53, 1)] [(12407047, 1, (PC.node 12407047 6 [(2, 1), (3, 1), (769, 1), (2689, 1)] []))]))])) (by decide +kernel)
theorem hp_12153 : Nat.Prime (512720 ^ 2 + 12153 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263029493809 7 [(2, 4), (3, 3), (241, 1)] [(2526409, 1, (PC.node 2526409 11 [(2, 3), (3, 2), (35089, 1)] []))])) (by decide +kernel)
theorem hp_12167 : Nat.Prime (512720 ^ 2 + 12167 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263029834289 3 [(2, 4), (13, 2), (521, 1), (186707, 1)] [])) (by decide +kernel)
theorem hp_12173 : Nat.Prime (512720 ^ 2 + 12173 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263029980329 3 [(2, 3), (17, 1)] [(1934043973, 1, (PC.node 1934043973 6 [(2, 2), (3, 1), (7, 1), (19, 1)] [(1211807, 1, (PC.node 1211807 5 [(2, 1), (283, 1), (2141, 1)] []))]))])) (by decide +kernel)
theorem hp_12187 : Nat.Prime (512720 ^ 2 + 12187 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263030321369 3 [(2, 3)] [(32878790171, 1, (PC.node 32878790171 2 [(2, 1), (5, 1), (59, 1)] [(55726763, 1, (PC.node 55726763 5 [(2, 1), (7, 1), (13, 1), (306191, 1)] []))]))])) (by decide +kernel)
theorem hp_12227 : Nat.Prime (512720 ^ 2 + 12227 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263031297929 3 [(2, 3), (7, 5), (59, 1), (71, 1), (467, 1)] [])) (by decide +kernel)
theorem hp_12249 : Nat.Prime (512720 ^ 2 + 12249 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263031836401 7 [(2, 4), (3, 2), (5, 2), (23, 1), (179, 1), (17747, 1)] [])) (by decide +kernel)
theorem hp_12251 : Nat.Prime (512720 ^ 2 + 12251 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263031885401 3 [(2, 3), (5, 2), (113, 1)] [(11638579, 1, (PC.node 11638579 2 [(2, 1), (3, 1), (7, 2), (31, 1), (1277, 1)] []))])) (by decide +kernel)
theorem hp_12253 : Nat.Prime (512720 ^ 2 + 12253 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263031934409 3 [(2, 3)] [(32878991801, 1, (PC.node 32878991801 6 [(2, 3), (5, 2), (37, 1)] [(4443107, 1, (PC.node 4443107 2 [(2, 1), (31, 1), (71663, 1)] []))]))])) (by decide +kernel)
theorem hp_12277 : Nat.Prime (512720 ^ 2 + 12277 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263032523129 3 [(2, 3), (389, 1)] [(84522019, 1, (PC.node 84522019 2 [(2, 1), (3, 1), (7, 1)] [(2012429, 1, (PC.node 2012429 2 [(2, 2), (11, 1), (45737, 1)] []))]))])) (by decide +kernel)
theorem hp_12283 : Nat.Prime (512720 ^ 2 + 12283 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263032670489 3 [(2, 3), (7, 1)] [(4697011973, 1, (PC.node 4697011973 2 [(2, 2)] [(1174252993, 1, (PC.node 1174252993 5 [(2, 6), (3, 1), (11, 1), (613, 1), (907, 1)] []))]))])) (by decide +kernel)
theorem hp_12287 : Nat.Prime (512720 ^ 2 + 12287 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263032768769 3 [(2, 8), (7, 1), (11, 1)] [(13343789, 1, (PC.node 13343789 2 [(2, 2)] [(3335947, 1, (PC.node 3335947 2 [(2, 1), (3, 1), (613, 1), (907, 1)] []))]))])) (by decide +kernel)
theorem hp_12307 : Nat.Prime (512720 ^ 2 + 12307 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263033260649 3 [(2, 3), (17, 1)] [(1934068093, 1, (PC.node 1934068093 6 [(2, 2), (3, 1), (11, 1), (2801, 1), (5231, 1)] []))])) (by decide +kernel)
theorem hp_12327 : Nat.Prime (512720 ^ 2 + 12327 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263033753329 11 [(2, 4), (3, 4)] [(202958143, 1, (PC.node 202958143 3 [(2, 1), (3, 1), (67, 1), (504871, 1)] []))])) (by decide +kernel)
theorem hp_12347 : Nat.Prime (512720 ^ 2 + 12347 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263034246809 3 [(2, 3), (263, 1)] [(125016277, 1, (PC.node 125016277 2 [(2, 2), (3, 1), (7, 1), (11, 1), (19, 1), (7121, 1)] []))])) (by decide +kernel)
theorem hp_12367 : Nat.Prime (512720 ^ 2 + 12367 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263034741089 3 [(2, 5), (7, 1), (31, 2)] [(1221917, 1, (PC.node 1221917 2 [(2, 2), (305479, 1)] []))])) (by decide +kernel)
theorem hp_12371 : Nat.Prime (512720 ^ 2 + 12371 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263034840041 11 [(2, 3), (5, 1), (7, 2), (31, 1)] [(4329079, 1, (PC.node 4329079 3 [(2, 1), (3, 1), (13, 1), (55501, 1)] []))])) (by decide +kernel)
theorem hp_12379 : Nat.Prime (512720 ^ 2 + 12379 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263035038041 6 [(2, 3), (5, 1), (11159, 1), (589289, 1)] [])) (by decide +kernel)
theorem hp_12381 : Nat.Prime (512720 ^ 2 + 12381 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263035087561 46 [(2, 3), (3, 5), (5, 1), (7, 1)] [(3865889, 1, (PC.node 3865889 6 [(2, 5), (13, 1), (9293, 1)] []))])) (by decide +kernel)
theorem hp_12391 : Nat.Prime (512720 ^ 2 + 12391 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263035335281 3 [(2, 4), (5, 1)] [(3287941691, 1, (PC.node 3287941691 6 [(2, 1), (5, 1), (11, 1), (449, 1), (66571, 1)] []))])) (by decide +kernel)
theorem hp_12397 : Nat.Prime (512720 ^ 2 + 12397 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263035484009 3 [(2, 3), (11, 1)] [(2989039591, 1, (PC.node 2989039591 6 [(2, 1), (3, 3), (5, 1)] [(11070517, 1, (PC.node 11070517 2 [(2, 2), (3, 1), (139, 1), (6637, 1)] []))]))])) (by decide +kernel)
theorem hp_12399 : Nat.Prime (512720 ^ 2 + 12399 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263035533601 19 [(2, 5), (3, 3), (5, 2), (7, 1)] [(1739653, 1, (PC.node 1739653 2 [(2, 2), (3, 1), (29, 1), (4999, 1)] []))])) (by decide +kernel)
theorem hp_12407 : Nat.Prime (512720 ^ 2 + 12407 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263035732049 3 [(2, 4), (23, 1)] [(714771011, 1, (PC.node 714771011 6 [(2, 1), (5, 1)] [(71477101, 1, (PC.node 71477101 2 [(2, 2), (3, 3), (5, 2), (23, 1), (1151, 1)] []))]))])) (by decide +kernel)
theorem hp_12423 : Nat.Prime (512720 ^ 2 + 12423 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263036129329 11 [(2, 4), (3, 3), (7, 2)] [(12426121, 1, (PC.node 12426121 13 [(2, 3), (3, 2), (5, 1), (7, 1), (4931, 1)] []))])) (by decide +kernel)
theorem hp_12437 : Nat.Prime (512720 ^ 2 + 12437 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263036477369 3 [(2, 3), (7, 1), (73, 1)] [(64343561, 1, (PC.node 64343561 3 [(2, 3), (5, 1), (857, 1), (1877, 1)] []))])) (by decide +kernel)
theorem hp_12447 : Nat.Prime (512720 ^ 2 + 12447 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263036726209 7 [(2, 6), (3, 2)] [(456660983, 1, (PC.node 456660983 5 [(2, 1)] [(228330491, 1, (PC.node 228330491 2 [(2, 1), (5, 1)] [(22833049, 1, (PC.node 22833049 19 [(2, 3), (3, 1), (7, 1), (135911, 1)] []))]))]))])) (by decide +kernel)
theorem hp_12457 : Nat.Prime (512720 ^ 2 + 12457 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263036975249 3 [(2, 4), (89, 1), (547, 1), (337691, 1)] [])) (by decide +kernel)
theorem hp_12503 : Nat.Prime (512720 ^ 2 + 12503 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263038123409 3 [(2, 4)] [(16439882713, 1, (PC.node 16439882713 5 [(2, 3), (3, 1), (11, 1)] [(62272283, 1, (PC.node 62272283 2 [(2, 1)] [(31136141, 1, (PC.node 31136141 12 [(2, 2), (5, 1), (7, 1), (29, 1), (7669, 1)] []))]))]))])) (by decide +kernel)
theorem hp_12507 : Nat.Prime (512720 ^ 2 + 12507 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263038223449 19 [(2, 3), (3, 3), (7, 1), (11, 1), (13, 2), (93581, 1)] [])) (by decide +kernel)
theorem hp_12533 : Nat.Prime (512720 ^ 2 + 12533 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263038874489 3 [(2, 3), (13, 1), (571, 1)] [(4429457, 1, (PC.node 4429457 3 [(2, 4), (101, 1), (2741, 1)] []))])) (by decide +kernel)
theorem hp_12537 : Nat.Prime (512720 ^ 2 + 12537 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263038974769 19 [(2, 4), (3, 2), (463, 1), (1451, 1), (2719, 1)] [])) (by decide +kernel)
theorem hp_12541 : Nat.Prime (512720 ^ 2 + 12541 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263039075081 3 [(2, 3), (5, 1), (149, 1)] [(44134073, 1, (PC.node 44134073 3 [(2, 3)] [(5516759, 1, (PC.node 5516759 23 [(2, 1), (13, 1), (212183, 1)] []))]))])) (by decide +kernel)
theorem hp_12543 : Nat.Prime (512720 ^ 2 + 12543 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263039125249 11 [(2, 8), (3, 5)] [(4228381, 1, (PC.node 4228381 2 [(2, 2), (3, 2), (5, 1), (13, 2), (139, 1)] []))])) (by decide +kernel)
theorem hp_12547 : Nat.Prime (512720 ^ 2 + 12547 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263039225609 3 [(2, 3), (17, 1), (10973, 1), (176261, 1)] [])) (by decide +kernel)
theorem hp_12559 : Nat.Prime (512720 ^ 2 + 12559 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263039526881 3 [(2, 5), (5, 1), (13, 1)] [(126461311, 1, (PC.node 126461311 3 [(2, 1), (3, 1), (5, 1), (1277, 1), (3301, 1)] []))])) (by decide +kernel)
theorem hp_12569 : Nat.Prime (512720 ^ 2 + 12569 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263039778161 3 [(2, 4), (5, 1), (317, 1)] [(10372231, 1, (PC.node 10372231 3 [(2, 1), (3, 2), (5, 1), (11, 1), (10477, 1)] []))])) (by decide +kernel)
theorem hp_12587 : Nat.Prime (512720 ^ 2 + 12587 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263040230969 3 [(2, 3), (29, 1), (3037, 1), (373327, 1)] [])) (by decide +kernel)
theorem hp_12593 : Nat.Prime (512720 ^ 2 + 12593 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263040382049 3 [(2, 5)] [(8220011939, 1, (PC.node 8220011939 2 [(2, 1), (17, 1), (1999, 1), (120943, 1)] []))])) (by decide +kernel)
theorem hp_12603 : Nat.Prime (512720 ^ 2 + 12603 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263040634009 11 [(2, 3), (3, 3), (673, 1)] [(1809481, 1, (PC.node 1809481 13 [(2, 3), (3, 1), (5, 1), (17, 1), (887, 1)] []))])) (by decide +kernel)
theorem hp_12613 : Nat.Prime (512720 ^ 2 + 12613 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263040886169 3 [(2, 3), (17, 1), (283, 1), (631, 1), (10831, 1)] [])) (by decide +kernel)
theorem hp_12629 : Nat.Prime (512720 ^ 2 + 12629 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263041290041 3 [(2, 3), (5, 1), (383, 1), (2731, 1), (6287, 1)] [])) (by decide +kernel)
theorem hp_12643 : Nat.Prime (512720 ^ 2 + 12643 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263041643849 3 [(2, 3), (29, 1), (823, 1)] [(1377643, 1, (PC.node 1377643 3 [(2, 1), (3, 1), (7, 1), (32801, 1)] []))])) (by decide +kernel)
theorem hp_12647 : Nat.Prime (512720 ^ 2 + 12647 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263041745009 3 [(2, 4), (7, 1), (17, 1), (1753, 1), (78809, 1)] [])) (by decide +kernel)
theorem hp_12651 : Nat.Prime (512720 ^ 2 + 12651 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263041846201 11 [(2, 3), (3, 4), (5, 2), (7, 1)] [(2319593, 1, (PC.node 2319593 3 [(2, 3), (11, 1), (43, 1), (613, 1)] []))])) (by decide +kernel)
theorem hp_12659 : Nat.Prime (512720 ^ 2 + 12659 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263042048681 3 [(2, 3), (5, 1), (20983, 1), (313399, 1)] [])) (by decide +kernel)
theorem hp_12669 : Nat.Prime (512720 ^ 2 + 12669 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263042301961 7 [(2, 3), (3, 3), (5, 1), (4729, 1), (51503, 1)] [])) (by decide +kernel)
theorem hp_12691 : Nat.Prime (512720 ^ 2 + 12691 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263042859881 3 [(2, 3), (5, 1), (48121, 1), (136657, 1)] [])) (by decide +kernel)
theorem hp_12707 : Nat.Prime (512720 ^ 2 + 12707 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263043266249 3 [(2, 3), (7, 1)] [(4697201183, 1, (PC.node 4697201183 5 [(2, 1), (16097, 1), (145903, 1)] []))])) (by decide +kernel)
theorem hp_12711 : Nat.Prime (512720 ^ 2 + 12711 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263043367921 7 [(2, 4), (3, 3), (5, 1), (1033, 1), (117889, 1)] [])) (by decide +kernel)
theorem hp_12723 : Nat.Prime (512720 ^ 2 + 12723 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263043673129 11 [(2, 3), (3, 3)] [(1217794783, 1, (PC.node 1217794783 3 [(2, 1), (3, 1)] [(202965797, 1, (PC.node 202965797 2 [(2, 2), (11, 1)] [(4612859, 1, (PC.node 4612859 2 [(2, 1), (19, 2), (6389, 1)] []))]))]))])) (by decide +kernel)
theorem hp_12747 : Nat.Prime (512720 ^ 2 + 12747 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263044284409 38 [(2, 3), (3, 3), (37, 1), (163, 1), (201923, 1)] [])) (by decide +kernel)
theorem hp_12759 : Nat.Prime (512720 ^ 2 + 12759 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263044590481 11 [(2, 4), (3, 4), (5, 1), (7, 1), (29, 1), (199967, 1)] [])) (by decide +kernel)
theorem hp_12761 : Nat.Prime (512720 ^ 2 + 12761 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263044641521 6 [(2, 4), (5, 1), (29, 1)] [(113381311, 1, (PC.node 113381311 3 [(2, 1), (3, 1), (5, 1), (7, 1), (53, 1), (61, 1), (167, 1)] []))])) (by decide +kernel)
theorem hp_12769 : Nat.Prime (512720 ^ 2 + 12769 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263044845761 3 [(2, 6), (5, 1)] [(822015143, 1, (PC.node 822015143 5 [(2, 1), (13, 1), (139, 1), (227453, 1)] []))])) (by decide +kernel)
theorem hp_12781 : Nat.Prime (512720 ^ 2 + 12781 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263045152361 3 [(2, 3), (5, 1)] [(6576128809, 1, (PC.node 6576128809 7 [(2, 3), (3, 1), (1447, 1), (189361, 1)] []))])) (by decide +kernel)
theorem hp_12793 : Nat.Prime (512720 ^ 2 + 12793 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263045459249 3 [(2, 4), (11, 1), (13, 1)] [(114967421, 1, (PC.node 114967421 2 [(2, 2), (5, 1)] [(5748371, 1, (PC.node 5748371 2 [(2, 1), (5, 1), (59, 1), (9743, 1)] []))]))])) (by decide +kernel)
theorem hp_12799 : Nat.Prime (512720 ^ 2 + 12799 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263045612801 3 [(2, 8), (5, 2), (2683, 1), (15319, 1)] [])) (by decide +kernel)
theorem hp_12817 : Nat.Prime (512720 ^ 2 + 12817 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263046073889 3 [(2, 5), (13, 1), (17, 1), (29, 1), (59, 1), (21739, 1)] [])) (by decide +kernel)
theorem hp_12823 : Nat.Prime (512720 ^ 2 + 12823 ^ 2) := Cert.PC.prime_of_ok (c := (PC.node 263046227729 3 [(2, 4), (23743, 1), (692431, 1)] [])) (by decide +kernel)
def S2 : List ℕ := [11691,11701,11707,11717,11719,11753,11757,11761,11767,11769,11813,11827,11863,11871,11889,11897,11901,11931,11941,11949,11953,11987,11993,12003,12031,12037,12039,12041,12047,12049,12063,12069,12073,12089,12113,12119,12127,12131,12133,12139,12147,12149,12153,12167,12173,12187,12227,12249,12251,12253,12277,12283,12287,12307,12327,12347,12367,12371,12379,12381,12391,12397,12399,12407,12423,12437,12447,12457,12503,12507,12533,12537,12541,12543,12547,12559,12569,12587,12593,12603,12613,12629,12643,12647,12651,12659,12669,12691,12707,12711,12723,12747,12759,12761,12769,12781,12793,12799,12817,12823]
theorem hsc2 : Cert.okChainS 512720 11649 S2 = true := by decide +kernel
theorem hff2 : Cert.finalSS 11649 S2 = 12823 := by decide
theorem hpS2 : ∀ s ∈ S2, Nat.Prime (512720 ^ 2 + s ^ 2) := by
  intro s hs
  simp only [S2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp_11691
  · exact hp_11701
  · exact hp_11707
  · exact hp_11717
  · exact hp_11719
  · exact hp_11753
  · exact hp_11757
  · exact hp_11761
  · exact hp_11767
  · exact hp_11769
  · exact hp_11813
  · exact hp_11827
  · exact hp_11863
  · exact hp_11871
  · exact hp_11889
  · exact hp_11897
  · exact hp_11901
  · exact hp_11931
  · exact hp_11941
  · exact hp_11949
  · exact hp_11953
  · exact hp_11987
  · exact hp_11993
  · exact hp_12003
  · exact hp_12031
  · exact hp_12037
  · exact hp_12039
  · exact hp_12041
  · exact hp_12047
  · exact hp_12049
  · exact hp_12063
  · exact hp_12069
  · exact hp_12073
  · exact hp_12089
  · exact hp_12113
  · exact hp_12119
  · exact hp_12127
  · exact hp_12131
  · exact hp_12133
  · exact hp_12139
  · exact hp_12147
  · exact hp_12149
  · exact hp_12153
  · exact hp_12167
  · exact hp_12173
  · exact hp_12187
  · exact hp_12227
  · exact hp_12249
  · exact hp_12251
  · exact hp_12253
  · exact hp_12277
  · exact hp_12283
  · exact hp_12287
  · exact hp_12307
  · exact hp_12327
  · exact hp_12347
  · exact hp_12367
  · exact hp_12371
  · exact hp_12379
  · exact hp_12381
  · exact hp_12391
  · exact hp_12397
  · exact hp_12399
  · exact hp_12407
  · exact hp_12423
  · exact hp_12437
  · exact hp_12447
  · exact hp_12457
  · exact hp_12503
  · exact hp_12507
  · exact hp_12533
  · exact hp_12537
  · exact hp_12541
  · exact hp_12543
  · exact hp_12547
  · exact hp_12559
  · exact hp_12569
  · exact hp_12587
  · exact hp_12593
  · exact hp_12603
  · exact hp_12613
  · exact hp_12629
  · exact hp_12643
  · exact hp_12647
  · exact hp_12651
  · exact hp_12659
  · exact hp_12669
  · exact hp_12691
  · exact hp_12707
  · exact hp_12711
  · exact hp_12723
  · exact hp_12747
  · exact hp_12759
  · exact hp_12761
  · exact hp_12769
  · exact hp_12781
  · exact hp_12793
  · exact hp_12799
  · exact hp_12817
  · exact hp_12823

def svals : List (List ℕ) := [S0,S1,S2]

theorem hchunks : Cert.okChunksS 512720 0 svals = true := by
  show Cert.okChunksS 512720 0 [S0,S1,S2] = true
  apply Cert.okChunksS_cons 512720 0 5917 S0 [S1,S2] hsc0 hff0
  apply Cert.okChunksS_cons 512720 5917 11649 S1 [S2] hsc1 hff1
  apply Cert.okChunksS_cons 512720 11649 12823 S2 [] hsc2 hff2
  rfl

theorem hflat : Cert.okChainS 512720 0 svals.flatten = true :=
  Cert.okChunksS_flatten 512720 svals 0 hchunks

theorem hpAll : ∀ s ∈ svals.flatten, Nat.Prime (512720 ^ 2 + s ^ 2) := by
  intro s hs
  rw [List.mem_flatten] at hs
  obtain ⟨l, hl, hsl⟩ := hs
  simp only [svals, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact hpS0 s hsl
  · exact hpS1 s hsl
  · exact hpS2 s hsl

theorem hlen : svals.flatten.length = 1100 := by
  rw [List.length_flatten]; decide

example : svals.flatten.length = 1100 := hlen
#check @hflat
#check @hpAll
#print axioms hpAll
#print axioms hflat
#print axioms hlen
