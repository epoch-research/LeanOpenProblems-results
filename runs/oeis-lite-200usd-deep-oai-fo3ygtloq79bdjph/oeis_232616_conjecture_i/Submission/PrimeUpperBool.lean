import FormalConjectures.Util.ProblemImports

namespace PrimeUpperBool

def noDivFrom (n d : Nat) : Nat → Bool
| 0 => true
| k+1 => (n % d != 0) && noDivFrom n (d+1) k

def isPrimeOver (n : Nat) : Bool := (2 <= n) && noDivFrom n 2 194

def countSmall (s : Nat) : Nat → Nat
| 0 => 0
| k+1 => countSmall s k + if isPrimeOver (s+k) then 1 else 0

lemma countSmall_add (s a b : Nat) :
    countSmall s (a + b) = countSmall s a + countSmall (s + a) b := by
  induction b with
  | zero => simp [countSmall]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      simp only [countSmall]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma noDivFrom_of_prime_ge_aux {n : Nat} (hp : Nat.Prime n) :
    ∀ k d : Nat, 2 ≤ d → d + k < n → noDivFrom n d k = true
| 0, d, hd2, hlt => by simp [noDivFrom]
| k+1, d, hd2, hlt => by
    simp only [noDivFrom]
    have hdn : d < n := by omega
    have hnotdvd : ¬ d ∣ n := by
      intro hdvd
      rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
      · omega
      · omega
    have hmod : n % d ≠ 0 := by
      intro hzero
      exact hnotdvd (Nat.dvd_of_mod_eq_zero hzero)
    have hrec : noDivFrom n (d + 1) k = true := by
      exact noDivFrom_of_prime_ge_aux hp k (d+1) (by omega) (by omega)
    simp [hmod, hrec]

lemma isPrimeOver_of_prime_ge {n : Nat} (hp : Nat.Prime n) (hge : 227 ≤ n) :
    isPrimeOver n = true := by
  have hn2 : 2 ≤ n := by omega
  have hno : noDivFrom n 2 194 = true := by
    exact noDivFrom_of_prime_ge_aux hp 194 2 (by omega) (by omega)
  simp [isPrimeOver, hn2, hno]

lemma countSmall_eq_count (s len : Nat) :
    countSmall s len = Nat.count (fun k => isPrimeOver (s + k) = true) len := by
  induction len with
  | zero => simp [countSmall]
  | succ len ih =>
      rw [Nat.count_succ]
      simp [countSmall, ih]

lemma card_primes_Ico_eq_count (s len : Nat) :
    ((Finset.Ico s (s + len)).filter Nat.Prime).card =
      Nat.count (fun k => Nat.Prime (s + k)) len := by
  induction len with
  | zero => simp
  | succ len ih =>
      rw [Nat.count_succ]
      have hle : s ≤ s + len := by omega
      have hnot : s + len ∉ Finset.Ico s (s + len) := by simp
      rw [show s + (len + 1) = (s + len).succ by omega]
      rw [Nat.Ico_succ_right_eq_insert_Ico hle]
      rw [Finset.filter_insert]

      by_cases hp : Nat.Prime (s + len)
      · simp [hp, hnot, ih]
      · simp [hp, ih]

lemma card_primes_Ico_le_countSmall (s len : Nat) (hs : 227 ≤ s) :
    ((Finset.Ico s (s + len)).filter Nat.Prime).card ≤ countSmall s len := by
  rw [card_primes_Ico_eq_count, countSmall_eq_count]
  apply Nat.count_mono_left
  intro k hk hp
  exact isPrimeOver_of_prime_ge hp (by omega)

end PrimeUpperBool
