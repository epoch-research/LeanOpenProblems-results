import FormalConjecturesUtil

/-! A local-to-global lemma for sums of periodic functions, and a restriction
on covers whose hit multiplicity is odd at every position. No parity
hypothesis is imposed on the original Jacobsthal conjecture. -/
namespace Erdos970.OddCoverPeriod
open Finset
set_option maxHeartbeats 0

/-- A sum of periodic functions is determined to be zero by an initial
zero block whose length is the sum of the periods. No field is needed. -/
theorem periodic_sum_zero_of_block {ι A : Type*} [AddCommGroup A]
    (S : Finset ι) (p : ι → ℕ) (f : ι → ℕ → A)
    (hp : ∀ i ∈ S, 0 < p i)
    (hf : ∀ i ∈ S, ∀ n, f i (n+p i) = f i n)
    (hzero : ∀ n < ∑ i ∈ S, p i, ∑ i ∈ S, f i n = 0) :
    ∀ n, ∑ i ∈ S, f i n = 0 := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp
  | @insert a S ha ih =>
    let g : ι → ℕ → A := fun i n => f i (n+p a)-f i n
    have hgp : ∀ i ∈ S, ∀ n, g i (n+p i) = g i n := by
      intro i hi n
      dsimp only [g]
      rw [show n+p i+p a = n+p a+p i by omega,
        hf i (mem_insert_of_mem hi) (n+p a), hf i (mem_insert_of_mem hi) n]
    have hgz : ∀ n < ∑ i ∈ S, p i, ∑ i ∈ S, g i n = 0 := by
      intro n hn
      have hn0 : n < ∑ i ∈ insert a S, p i := by rw [sum_insert ha]; omega
      have hn1 : n+p a < ∑ i ∈ insert a S, p i := by rw [sum_insert ha]; omega
      have h0 := hzero n hn0
      have h1 := hzero (n+p a) hn1
      rw [sum_insert ha] at h0 h1
      rw [hf a (mem_insert_self _ _) n] at h1
      change (∑ i ∈ S, (f i (n+p a)-f i n)) = 0
      rw [sum_sub_distrib]
      have he : (∑ i ∈ S, f i (n+p a)) = ∑ i ∈ S, f i n :=
        add_left_cancel (h1.trans h0.symm)
      exact sub_eq_zero.mpr he
    have hg := ih g (fun i hi => hp i (mem_insert_of_mem hi)) hgp hgz
    have hshift (n : ℕ) :
        (∑ i ∈ insert a S, f i (n+p a)) = ∑ i ∈ insert a S, f i n := by
      rw [sum_insert ha, sum_insert ha, hf a (mem_insert_self _ _) n]
      apply congrArg (fun x => f a n+x)
      exact sub_eq_zero.mp (by simpa only [g, sum_sub_distrib] using hg n)
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      by_cases hn : n < ∑ i ∈ insert a S, p i
      · exact hzero n hn
      · have hpa := hp a (mem_insert_self _ _)
        have hpan : p a ≤ n := by
          have hh : p a ≤ ∑ i ∈ insert a S, p i := by rw [sum_insert ha]; omega
          omega
        have hsmall : n-p a < n := Nat.sub_lt (by omega) hpa
        have he := ihn (n-p a) hsmall
        have hs := hshift (n-p a)
        rw [Nat.sub_add_cancel hpan] at hs
        exact hs.trans he

/-- A nonempty sum of periodic functions is constant globally if it is
constant on a block whose length is the sum of their periods. -/
theorem periodic_sum_constant_of_block {ι A : Type*} [AddCommGroup A]
    (S : Finset ι) (hS : S.Nonempty) (p : ι → ℕ) (f : ι → ℕ → A) (c : A)
    (hp : ∀ i ∈ S, 0 < p i)
    (hf : ∀ i ∈ S, ∀ n, f i (n+p i) = f i n)
    (hconst : ∀ n < ∑ i ∈ S, p i, ∑ i ∈ S, f i n = c) :
    ∀ n, ∑ i ∈ S, f i n = c := by
  classical
  obtain ⟨a, ha⟩ := hS
  let g : ι → ℕ → A := fun i n => f i n - if i = a then c else 0
  have hsum (n : ℕ) : (∑ i ∈ S, g i n) = (∑ i ∈ S, f i n)-c := by
    simp only [g, sum_sub_distrib]
    rw [sum_ite_eq' S a (fun _ => c), if_pos ha]
  have hh := periodic_sum_zero_of_block S p g hp
    (fun i hi n => by dsimp only [g]; rw [hf i hi n]) (by
      intro n hn
      rw [hsum, hconst n hn, sub_self])
  intro n
  exact sub_eq_zero.mp (by simpa only [hsum] using hh n)

/-- The difference of consecutive length-L windows telescopes. -/
lemma window_shift {A : Type*} [AddCommGroup A] (f : ℕ → A) (L n : ℕ) :
    (∑ j ∈ range L, f (n+1+j)) + f n =
      (∑ j ∈ range L, f (n+j)) + f (n+L) := by
  have h := sum_range_succ' (fun j => f (n+j)) L
  rw [sum_range_succ] at h
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_zero] using h.symm

lemma period_window_constant {A : Type*} [AddCommGroup A]
    (f : ℕ → A) (p : ℕ) (hf : ∀ n, f (n+p) = f n) (n : ℕ) :
    (∑ j ∈ range p, f (n+j)) = ∑ j ∈ range p, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := window_shift f p n
    rw [hf n] at hh
    exact (add_right_cancel hh).trans ih

/-- Sharing the constant component reduces the block length to
1 + the sum of (period - 1). This holds over any additive commutative group. -/
theorem periodic_sum_constant_of_short_block {ι A : Type*} [AddCommGroup A]
    (S : Finset ι) (p : ι → ℕ) (f : ι → ℕ → A) (c : A)
    (hp : ∀ i ∈ S, 0 < p i)
    (hf : ∀ i ∈ S, ∀ n, f i (n+p i) = f i n)
    (hconst : ∀ n < 1+∑ i ∈ S, (p i-1), ∑ i ∈ S, f i n = c) :
    ∀ n, ∑ i ∈ S, f i n = c := by
  classical
  induction S using Finset.induction_on generalizing f c with
  | empty =>
    have hh := hconst 0 (by simp)
    simpa using hh
  | @insert a S ha ih =>
    let g : ι → ℕ → A := fun i n => ∑ j ∈ range (p a), f i (n+j)
    let d : A := (p a) • c - ∑ j ∈ range (p a), f a j
    have hpa : 0 < p a := hp a (mem_insert_self _ _)
    have hgp : ∀ i ∈ S, ∀ n, g i (n+p i) = g i n := by
      intro i hi n
      dsimp only [g]
      apply sum_congr rfl
      intro j hj
      rw [show n+p i+j = n+j+p i by omega, hf i (mem_insert_of_mem hi) (n+j)]
    have hgc : ∀ n < 1+∑ i ∈ S, (p i-1), ∑ i ∈ S, g i n = d := by
      intro n hn
      have hw : (∑ j ∈ range (p a), ∑ i ∈ insert a S, f i (n+j)) = (p a) • c := by
        calc
          _ = ∑ j ∈ range (p a), c := by
            apply sum_congr rfl
            intro j hj
            apply hconst
            rw [sum_insert ha]
            have hj' := mem_range.mp hj
            omega
          _ = _ := by simp
      rw [sum_comm, sum_insert ha,
        period_window_constant (f a) (p a) (hf a (mem_insert_self _ _)) n] at hw
      change (∑ j ∈ range (p a), f a j) + ∑ i ∈ S, g i n = (p a) • c at hw
      dsimp only [d]
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hw)
    have hg := ih g d (fun i hi => hp i (mem_insert_of_mem hi)) hgp hgc
    have hw (n : ℕ) :
        (∑ j ∈ range (p a), ∑ i ∈ insert a S, f i (n+j)) = (p a) • c := by
      rw [sum_comm, sum_insert ha,
        period_window_constant (f a) (p a) (hf a (mem_insert_self _ _)) n]
      change (∑ j ∈ range (p a), f a j) + ∑ i ∈ S, g i n = (p a) • c
      rw [hg]
      dsimp only [d]
      abel
    have hshift (n : ℕ) :
        (∑ i ∈ insert a S, f i (n+p a)) = ∑ i ∈ insert a S, f i n := by
      have hh := window_shift (fun n => ∑ i ∈ insert a S, f i n) (p a) n
      rw [hw (n+1), hw n] at hh
      exact (add_left_cancel hh).symm
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      by_cases hn : n < 1+∑ i ∈ insert a S, (p i-1)
      · exact hconst n hn
      · have hpan : p a ≤ n := by
          have hh : p a ≤ 1+∑ i ∈ insert a S, (p i-1) := by rw [sum_insert ha]; omega
          omega
        have he := ihn (n-p a) (Nat.sub_lt (by omega) hpa)
        have hs := hshift (n-p a)
        rw [Nat.sub_add_cancel hpan] at hs
        exact hs.trans he

/-- The multiplicity of the chosen prime residue classes at an offset. -/
def hitMultiplicity (P : Finset ℕ) (r : ℕ → ℕ) (n : ℕ) : ℕ :=
  (P.filter (fun p => n ≡ r p [MOD p])).card

lemma multiplicity_cast (P : Finset ℕ) (r : ℕ → ℕ) (n : ℕ) :
    (hitMultiplicity P r n : ZMod 2) =
      ∑ p ∈ P, if n ≡ r p [MOD p] then (1 : ZMod 2) else 0 := by
  classical
  simp only [hitMultiplicity, sum_boole]

/-- An odd-multiplicity cover cannot contain a full shared-constant period block.
This is a bound in terms of the moduli, not a quadratic prime-count bound. -/
theorem odd_cover_length_le_sum_pred (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hodd : ∀ n < m, Odd (hitMultiplicity P r n)) :
    m ≤ ∑ p ∈ P, (p-1) := by
  classical
  by_contra hbad
  have hlen : 1+(∑ p ∈ P, (p-1)) ≤ m := by omega
  let f : ℕ → ℕ → ZMod 2 := fun p n => if n ≡ r p [MOD p] then 1 else 0
  have hf : ∀ p ∈ P, ∀ n, f p (n+p) = f p n := by
    intro p hp n
    dsimp only [f]
    have he : (n+p) ≡ r p [MOD p] ↔ n ≡ r p [MOD p] := by
      simp only [Nat.ModEq, Nat.add_mod_right]
    simp only [he]
  have hc : ∀ n < 1+∑ p ∈ P, (p-1), ∑ p ∈ P, f p n = 1 := by
    intro n hn
    rw [← multiplicity_cast]
    obtain ⟨t, ht⟩ := hodd n (hn.trans_le hlen)
    rw [ht]
    push_cast
    have hz2 : (2 : ZMod 2) = 0 := by decide
    rw [hz2]
    simp
  have hall := periodic_sum_constant_of_short_block P id f (1 : ZMod 2)
    (fun p hp => (hP p hp).pos) hf hc
  have hco : (↑P : Set ℕ).Pairwise (fun p q => Nat.Coprime p q) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  let b := Nat.chineseRemainderOfFinset (fun p => r p+1) id P
    (fun p hp => (hP p hp).ne_zero) hco
  have hav (p : ℕ) (hp : p ∈ P) : ¬b.val ≡ r p [MOD p] := by
    intro hhit
    have hb : b.val ≡ r p+1 [MOD p] := b.property p hp
    have hh : r p+1 ≡ r p [MOD p] := hb.symm.trans hhit
    have hdiv : p ∣ 1 := by
      have h : (p : ℤ) ∣ 1 := by simpa using Nat.ModEq.dvd hh
      exact_mod_cast h
    exact (hP p hp).not_dvd_one hdiv
  have hz : (∑ p ∈ P, f p b.val) = 0 := by
    apply sum_eq_zero
    intro p hp
    exact if_neg (hav p hp)
  have hh := hall b.val
  rw [hz] at hh
  exact zero_ne_one hh

#print axioms periodic_sum_zero_of_block
#print axioms periodic_sum_constant_of_short_block
#print axioms odd_cover_length_le_sum_pred
end Erdos970.OddCoverPeriod
