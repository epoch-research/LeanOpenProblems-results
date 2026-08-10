import FormalConjectures.Util.ProblemImports

open Int

/--
A182510: $a(0)=0, a(1)=1, a(n)=(a(n-1) \text{ XOR } n) - a(n-2)$, where $\text{XOR}$ is the bitwise exclusive-or operator.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

open Filter Set

lemma xor_zero_right (x : ℤ) : Int.xor x (0 : ℤ) = x := by
  cases x <;> simp [Int.xor, Nat.xor_zero]

lemma div2_lt_self_of_pos {m : ℕ} (hm : 0 < m) : Nat.div2 m < m := by
  rw [Nat.div2_val]
  exact Nat.div_lt_self hm (by norm_num)

lemma xor_perturb_bound : ∀ (m : ℕ) (x : ℤ),
    - (m : ℤ) ≤ Int.xor x (m : ℤ) - x ∧ Int.xor x (m : ℤ) - x ≤ (m : ℤ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro x
    by_cases hm0 : m = 0
    · subst m
      simp [xor_zero_right]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmdec : Int.bit (Nat.bodd m) ((Nat.div2 m : ℕ) : ℤ) = (m : ℤ) := by
        simpa [Int.bit_coe_nat] using congrArg (fun t : ℕ => (t : ℤ)) (Nat.bit_decomp m)
      rw [← Int.bit_decomp x, ← hmdec, Int.lxor_bit]
      set d : ℤ := Int.xor (Int.div2 x) ↑(Nat.div2 m) - Int.div2 x
      have hd := ih (Nat.div2 m) (div2_lt_self_of_pos hmpos) (Int.div2 x)
      have hdl : -((Nat.div2 m : ℕ) : ℤ) ≤ d := by simpa [d] using hd.1
      have hdr : d ≤ ((Nat.div2 m : ℕ) : ℤ) := by simpa [d] using hd.2
      have hmb := Nat.bodd_add_div2 m
      cases hx : Int.bodd x <;> cases hmbit : Nat.bodd m <;>
        simp [Int.bit_val, Bool.xor, hx, hmbit, d] at * <;> omega

lemma a_three_bound (n : ℕ) :
    -((2 * n + 5 : ℕ) : ℤ) ≤ a (n + 3) + a n ∧
      a (n + 3) + a n ≤ ((2 * n + 5 : ℕ) : ℤ) := by
  have h1 := xor_perturb_bound (n + 2) (a (n + 1))
  have h2 := xor_perturb_bound (n + 3) (a (n + 2))
  have hz : a (n + 2) = Int.xor (a (n + 1)) ((n + 2 : ℕ) : ℤ) - a n := by rfl
  have htarget : a (n + 3) + a n =
      (Int.xor (a (n + 2)) ((n + 3 : ℕ) : ℤ) - a (n + 2)) +
        (Int.xor (a (n + 1)) ((n + 2 : ℕ) : ℤ) - a (n + 1)) := by
    rw [show a (n + 3) = Int.xor (a (n + 2)) ((n + 3 : ℕ) : ℤ) - a (n + 1) by rfl]
    rw [hz]
    ring
  rw [htarget]
  constructor <;> omega

lemma a_three_neg_of_pos_large {n : ℕ} (h : ((2 * n + 5 : ℕ) : ℤ) < a n) : a (n + 3) < 0 := by
  have hb := (a_three_bound n).2
  linarith

lemma a_three_pos_of_neg_large {n : ℕ} (h : a n < -((2 * n + 5 : ℕ) : ℤ)) : 0 < a (n + 3) := by
  have hb := (a_three_bound n).1
  linarith




/-- oeis_182510_conjecture_1: A182510 Conjectures: more positive terms than negative.
This is formalized as the asymptotic (natural) density of positive terms being strictly greater
than the asymptotic density of negative terms, assuming both densities exist.
The set of positive indices is $P = \{n \mid a(n) > 0\}$, and the set of negative indices is $N_{neg} = \{n \mid a(n) < 0\}$.
The natural density of a set $S \subseteq \mathbb{N}$ is defined in Mathlib as `S.HasDensity d`.
-/
theorem oeis_a182510_conjecture_density :
  ∃ d_pos d_neg : ℝ,
    ({n : ℕ | a n > 0}).HasDensity d_pos ∧
    ({n : ℕ | a n < 0}).HasDensity d_neg ∧
    d_pos > d_neg :=
by sorry
