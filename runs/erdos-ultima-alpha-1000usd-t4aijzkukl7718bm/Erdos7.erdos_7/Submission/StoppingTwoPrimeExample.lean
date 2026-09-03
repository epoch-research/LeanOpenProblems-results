import Submission.StoppingPolicyArithmetic

/-! An exact two-prime partial family with private points. Both prime
coordinates have terminal full stopping closures and common collision fibers.
This is NOT a cover: integer2 misses every class. -/
namespace Erdos7StoppingTwoPrimeExample
open Erdos7Digits Erdos7AllDigits
open Erdos7StoppingDigitRestriction Erdos7StoppingPrefixClosure
open Erdos7StoppingPrefixArithmetic Erdos7StoppingPolicyArithmetic
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
def modulus : Fin 24 → ℕ := ![5,25,125,625,3,15,75,375,1875,9,45,225,1125,5625,27,135,675,3375,16875,81,405,2025,10125,50625]
def residueN : Fin 24 → ℕ := ![0,4,19,69,0,1,59,169,1444,1,22,214,1069,319,4,13,319,94,4819,13,364,1849,5494,31819]
def privatePoint : Fin 24 → ℤ := ![5,29,269,1319,3,16,59,169,1444,28,22,214,1069,11569,58,148,994,3469,21694,499,364,1849,5494,31819]
def residue (i : Fin 24) : ℤ := residueN i
def primes : Fin 2 → ℕ := ![3,5]
abbrev caps (_ : Fin 2) : ℕ := 4
instance (i : Fin 2) : NeZero (primes i) := ⟨by fin_cases i <;> decide⟩
def exponents : Fin 24 → Fin 2 → ℕ := ![![0,1],![0,2],![0,3],![0,4],![1,0],![1,1],![1,2],![1,3],![1,4],![2,0],![2,1],![2,2],![2,3],![2,4],![3,0],![3,1],![3,2],![3,3],![3,4],![4,0],![4,1],![4,2],![4,3],![4,4]]

lemma arithmetic_data :
    Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 50625) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i, ¬ (modulus i : ℤ) ∣ 2-residue i) ∧
    (∀ i, modulus i = ∏ j, primes j ^ exponents i j) := by
  decide +kernel

lemma comparable_separation : ∀ k l : Fin 24, l ≠ k → modulus l ∣ modulus k →
    ¬ (modulus l : ℤ) ∣ residue k-residue l := by
  decide +kernel

lemma divisor_data : ∀ i : Fin 24, ∀ d : ↥(modulus i).divisors,
    1 < d.val → ∃ j, modulus j=d.val := by
  decide +kernel

theorem divisor_closed (i : Fin 24) (d : ℕ) (hd : d ∣ modulus i) (h1 : 1<d) :
    ∃ j, modulus j=d := by
  have hp : 0 < modulus i := lt_trans (by omega : 0<1) (arithmetic_data.2.1 i).1
  exact divisor_data i ⟨d,Nat.mem_divisors.mpr ⟨hd,hp.ne'⟩⟩ h1

def centerN : Fin 2 → ℕ := ![40,69]
def center (i : Fin 2) := zmodDigits (primes i) 4 (centerN i)
def digits (i : Fin 2) (k : Fin 24) := zmodDigits (primes i) 4 (residue k)

def upper (i : Fin 2) (t : Fin 4) (r : Fin (primes i)) : Fin 24 :=
  ⟨if i.val=0 then 4+5*t.val+r.val else 5*r.val+t.val,by
    have hr := r.isLt
    fin_cases i <;> norm_num [primes] at hr ⊢ <;> omega⟩

def lower (i : Fin 2) (t : Fin 4) (r : Fin (primes i)) : Fin 24 :=
  ⟨if i.val=0 then 5*t.val+r.val-1 else 5*r.val+t.val-1,by
    have hr := r.isLt
    fin_cases i <;> norm_num [primes] at hr ⊢ <;> omega⟩

/-- Every level has all its required colors. The lower companions' prefixes
are children of the preceding forced node, rather than arbitrary frozen nodes. -/
lemma forcing_data : ∀ i : Fin 2, ∀ t : Fin 4, ∀ r : Fin (primes i),
    exponents (upper i t r) i=t.val+1 ∧
    Agree t.val (digits i (upper i t r)) (center i) ∧
    digits i (upper i t r) t=r ∧
    (t.val=0 ∧ r.val=0 → ∀ j,
      eraseExponent i t.val (exponents (upper i t r)) j=0) ∧
    (¬ (t.val=0 ∧ r.val=0) →
      exponents (lower i t r) i=t.val ∧
      (∀ j, j ≠ i → exponents (upper i t r) j=exponents (lower i t r) j) ∧
      Agree (t.val-1) (digits i (lower i t r)) (center i)) := by
  unfold Agree
  decide +kernel

abbrev Mark (i : Fin 2) := Block primes caps i exponents residue
abbrev F (i : Fin 2) := Frozen (show 0 < caps i by exact Nat.zero_lt_succ 3) (Mark i)

/-- All four central forcing nodes belong to the least closure and have no
unblocked color. The proof starts at the root, with no cyclic assumptions. -/
theorem central_forced (i : Fin 2) : ∀ n, ∀ hn : n < 4,
    node (center i) ⟨n,hn⟩ ∈ F i ∧
    ∀ r, Mark i (F i) (node (center i) ⟨n,hn⟩) r := by
  have hc := frozen_closed (show 0 < caps i by exact Nat.zero_lt_succ 3) (Mark i)
    (fun hBC => block_mono primes caps i exponents residue hBC)
  intro n
  induction n with
  | zero =>
    intro hn
    have hroot : node (center i) ⟨0,hn⟩ ∈ F i := by rw [node_zero]; exact hc.1
    refine ⟨hroot,fun r => ?_⟩
    obtain ⟨he,ha,hr,hu,hl⟩ := forcing_data i ⟨0,hn⟩ r
    refine ⟨upper i ⟨0,hn⟩ r,by change 0 < exponents _ i; rw [he]; exact Nat.zero_lt_succ _,node_agree _ _ _ ha,hr,?_⟩
    by_cases hz : r.val=0
    · exact Or.inl (hu ⟨rfl,hz⟩)
    · obtain ⟨hel,ho,ha⟩ := hl (fun h => hz h.2)
      refine Or.inr ⟨lower i ⟨0,hn⟩ r,by rw [he,hel],ho,by rw [hel]; exact Nat.zero_lt_succ 3,?_⟩
      have hnode : node (digits i (lower i ⟨0,hn⟩ r))
          ⟨exponents (lower i ⟨0,hn⟩ r) i,by rw [hel]; exact Nat.zero_lt_succ 3⟩ = root (by decide) := by
        have ht : (⟨exponents (lower i ⟨0,hn⟩ r) i,by rw [hel]; exact Nat.zero_lt_succ 3⟩ : Fin 4) =
            ⟨0,by decide⟩ := Fin.ext hel
        rw [ht]
        exact node_zero _ _
      change node (digits i (lower i ⟨0,hn⟩ r)) _ ∈ F i
      rw [hnode]
      exact hc.1
  | succ n ih =>
    intro hn
    obtain ⟨hprev,hblock⟩ := ih (by omega)
    have hmem := hc.2 (center i) ⟨n,by change n < 4; omega⟩ hn hprev hblock
    refine ⟨hmem,fun r => ?_⟩
    obtain ⟨he,ha,hr,hu,hl⟩ := forcing_data i ⟨n+1,hn⟩ r
    obtain ⟨hel,ho,hal⟩ := hl (by simp)
    refine ⟨upper i ⟨n+1,hn⟩ r,by change n+1 < exponents _ i; rw [he]; exact Nat.lt_succ_self _,node_agree _ _ _ ha,hr,
      Or.inr ⟨lower i ⟨n+1,hn⟩ r,by rw [he,hel],ho,by rw [hel]; exact hn,?_⟩⟩
    have hsame : node (digits i (lower i ⟨n+1,hn⟩ r)) ⟨n,by change n < 4; omega⟩ =
        node (center i) ⟨n,by change n < 4; omega⟩ := node_agree _ _ _ (by simpa using hal)
    have hlmem := hc.2 (digits i (lower i ⟨n+1,hn⟩ r)) ⟨n,by change n < 4; omega⟩ hn
      (by rw [hsame]; exact hprev) (fun r => by rw [hsame]; exact hblock r)
    have ht : (⟨exponents (lower i ⟨n+1,hn⟩ r) i,by rw [hel]; exact hn⟩ : Fin 4) =
        ⟨n+1,hn⟩ := Fin.ext hel
    change node (digits i (lower i ⟨n+1,hn⟩ r)) _ ∈ F i
    rw [ht]
    exact hlmem

theorem both_frozen_terminal (i : Fin 2) :
    Terminal (show 0 < caps i by exact Nat.zero_lt_succ 3) (Mark i) (F i) := by
  exact ⟨center i,central_forced i 3 (by decide)⟩

theorem no_safe_stopping (i : Fin 2) (T : (Fin 4 → Fin (primes i)) → Fin 4)
    (V : (Fin 4 → Fin (primes i)) → Fin (primes i))
    (hT : Predictable T) (hV : PredictableValue T V) :
    ¬ StrictImage primes caps i exponents residue T V := by
  intro hS
  have hei : Function.Injective exponents := by
    intro k l hkl
    apply arithmetic_data.1
    rw [arithmetic_data.2.2.2.2 k,arithmetic_data.2.2.2.2 l,hkl]
  have he0 : ∀ k, ∃ i, exponents k i ≠ 0 := by decide +kernel
  exact (exists_strict_image_iff primes caps i exponents residue hei he0 (by exact Nat.zero_lt_succ 3)).mp
    ⟨T,V,hT,hV,hS⟩ (both_frozen_terminal i)

def fiberPoint : Fin 2 → ℤ := ![499,1444]

/-- Each coordinate obstruction separately has one exact common arithmetic
fiber with all top colors; the two fibers need not be the same integer. -/
theorem common_fiber_data : ∀ i : Fin 2, ∀ r : Fin (primes i),
    exponents (upper i 3 r) i = 4 ∧ exponents (lower i 3 r) i = 3 ∧
    modulus (upper i 3 r) = primes i*modulus (lower i 3 r) ∧
    digits i (upper i 3 r) 3 = r ∧
    (modulus (lower i 3 r) : ℤ) ∣ fiberPoint i-residue (upper i 3 r) ∧
    ¬ (modulus (lower i 3 r) : ℤ) ∣ fiberPoint i-residue (lower i 3 r) := by
  decide +kernel

lemma fiber_prefix_data : ∀ i : Fin 2,
    Agree 3 (zmodDigits (primes i) 4 (fiberPoint i)) (center i) := by
  unfold Agree
  decide +kernel

/-- The actual common fiber and every one of its lower companions lie at
reached top prefixes of the least closure, as in the necessary fiber theorem. -/
theorem fiber_nodes (i : Fin 2) :
    node (zmodDigits (primes i) 4 (fiberPoint i)) (3 : Fin 4) ∈ F i ∧
    ∀ r : Fin (primes i), node (digits i (lower i 3 r)) (3 : Fin 4) ∈ F i := by
  constructor
  · rw [node_agree _ _ _ (fiber_prefix_data i)]
    exact (central_forced i 3 (by decide)).1
  · intro r
    have hc := frozen_closed (show 0 < caps i by exact Nat.zero_lt_succ 3) (Mark i)
      (fun hBC => block_mono primes caps i exponents residue hBC)
    obtain ⟨_,_,_,_,hl⟩ := forcing_data i 3 r
    have ha : Agree 2 (digits i (lower i 3 r)) (center i) := (hl (by simp)).2.2
    have hnode : node (digits i (lower i 3 r)) (2 : Fin 4) =
        node (center i) (2 : Fin 4) := node_agree _ _ _ ha
    obtain ⟨hmem,hblock⟩ := central_forced i 2 (by decide)
    exact hc.2 (digits i (lower i 3 r)) (2 : Fin 4) (by exact Nat.lt_succ_self 3)
      (by rw [hnode]; exact hmem) (fun r => by rw [hnode]; exact hblock r)

#print axioms fiber_nodes

theorem not_cover : ¬ ∀ x : ℤ, ∃ i, (modulus i : ℤ) ∣ x-residue i := by
  intro hc
  obtain ⟨i,hi⟩ := hc 2
  exact arithmetic_data.2.2.2.1 i hi

#print axioms comparable_separation
#print axioms arithmetic_data
#print axioms divisor_closed
#print axioms central_forced
#print axioms both_frozen_terminal
#print axioms no_safe_stopping
#print axioms common_fiber_data
#print axioms not_cover
end Erdos7StoppingTwoPrimeExample
