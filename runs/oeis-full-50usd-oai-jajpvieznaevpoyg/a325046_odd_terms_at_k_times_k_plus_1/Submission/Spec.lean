import FormalConjectures.Util.ProblemImports

open Nat
open Finset

/--
A325046: G.f.: $\sum_{n \ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 - x^{n+1})^{n+1}}$.

The term $a(N)$ is the coefficient of $x^N$ in the generating function.
Expanding the terms, we get a formula for $a(N)$:
$$a(N) = \sum_{n=0}^N \sum_{k=0}^n \mathbf{1}_{n + nk + (n+1)j = N} \binom{n}{k} \binom{n+j}{j}$$
where $j = \frac{N - n(k+1)}{n+1}$.
-/
def a (N : ℕ) : ℕ :=
  -- The outer sum runs over $n$ from $0$ to $N$.
  (range (N + 1)).sum (fun n =>
    -- The inner sum runs over $k$ from $0$ to $n$.
    (range (n + 1)).sum (fun k =>
      let R : ℕ := N - n * (k + 1)
      let m : ℕ := n + 1
      -- We require $R = N - n(k+1) \ge 0$ and $m = n+1$ must divide $R$.
      if n * (k + 1) ≤ N ∧ R % m = 0 then
        -- $j = R / m$.
        let j : ℕ := R / m
        -- The summand is $\binom{n}{k} \binom{n+j}{j}$.
        n.choose k * (n + j).choose j
      else
        0
    )
  )

namespace A325046Proof

abbrev P := Sigma (fun _ : ℕ => ℕ)

def S (N : ℕ) : Finset P := (range (N + 1)).sigma (fun n => range (n + 1))

def jval (N n k : ℕ) : ℕ := (N - n * (k + 1)) / (n + 1)

def term (N : ℕ) (p : P) : ZMod 2 :=
  let n := p.1
  let k := p.2
  if n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0 then
    ((n.choose k * (n + jval N n k).choose (jval N n k) : ℕ) : ZMod 2)
  else 0

def flipCore (N : ℕ) (p : P) : P :=
  let n := p.1
  let k := p.2
  let j := jval N n k
  ⟨j + k, k⟩

def flip (N : ℕ) (p : P) : P := if term N p = 0 then p else flipCore N p

lemma memS_iff {N : ℕ} {p : P} : p ∈ S N ↔ p.1 ≤ N ∧ p.2 ≤ p.1 := by
  rcases p with ⟨n,k⟩
  simp [S, Nat.lt_succ_iff]

lemma cast_a_eq_sum_term (N : ℕ) :
    ((a N : ℕ) : ZMod 2) = ∑ p ∈ S N, term N p := by
  simp only [S, Finset.sum_sigma]
  simp [a, term, jval]

lemma valid_eq {N n k : ℕ}
    (h : n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0) :
    N = n * (k + 1) + (n + 1) * jval N n k := by
  unfold jval
  have hdvd : n + 1 ∣ N - n * (k + 1) := Nat.dvd_of_mod_eq_zero h.2
  have hmul : (n + 1) * ((N - n * (k + 1)) / (n + 1)) = N - n * (k + 1) := by
    rw [mul_comm, Nat.div_mul_cancel hdvd]
  rw [hmul]
  omega

lemma choose_flip_identity (n k j : ℕ) (hk : k ≤ n) :
    n.choose k * (n + j).choose j =
      (j + k).choose k * (j + k + (n - k)).choose (n - k) := by
  have hL := Nat.choose_mul (n := n + j) (k := n) (s := k) hk
  have hR := Nat.choose_mul (n := n + j) (k := j + k) (s := k) (Nat.le_add_left k j)
  have hnj : (n + j).choose n = (n + j).choose j := by
    simpa [add_comm] using (Nat.choose_symm_add (a := n) (b := j))
  have hnkj : n + j = j + k + (n - k) := by omega
  have htop : (n + j).choose (j + k) = (n + j).choose (n - k) := by
    exact Nat.choose_symm_of_eq_add (by omega)
  have hsub1 : n + j - k = j + (n - k) := by omega
  have hsub2 : n + j - (j + k) = n - k := by omega
  calc
    n.choose k * (n + j).choose j = (n + j).choose n * n.choose k := by rw [hnj, mul_comm]
    _ = (n + j).choose k * (n + j - k).choose (n - k) := by simpa [mul_comm] using hL
    _ = (n + j).choose k * (j + (n - k)).choose (n - k) := by rw [hsub1]
    _ = (n + j).choose k * (n + j - k).choose j := by
      rw [hsub1]
      congr 1
      exact Nat.choose_symm_of_eq_add (by omega)
    _ = (n + j).choose (j + k) * (j + k).choose k := by simpa [hsub2, mul_comm, mul_left_comm, mul_assoc] using hR.symm
    _ = (n + j).choose (n - k) * (j + k).choose k := by rw [htop]
    _ = (j + k).choose k * (j + k + (n - k)).choose (n - k) := by rw [mul_comm, hnkj]

lemma central_even_zmod {r : ℕ} (hr : 0 < r) : ((Nat.choose (2 * r) r : ℕ) : ZMod 2) = 0 := by
  have h := Nat.choose_mul_right (m := 2) (n := r) (by omega : r ≠ 0)
  rw [h, Nat.cast_mul]
  change ((2 : ZMod 2) * (((2 * r - 1).choose (r - 1) : ℕ) : ZMod 2)) = 0
  rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2, zero_mul]

lemma fixed_even {n k j : ℕ} (hk : k ≤ n) (hlt : k < n) (hj : j = n - k) :
    ((n.choose k * (n + j).choose j : ℕ) : ZMod 2) = 0 := by
  subst j
  have hsym : (n + (n - k)).choose (n - k) = (n + (n - k)).choose n := by
    exact Nat.choose_symm_of_eq_add (by omega)
  have hmul := Nat.choose_mul (n := n + (n - k)) (k := n) (s := k) hk
  have hprod : n.choose k * (n + (n - k)).choose (n - k) =
      (n + (n - k)).choose k * (2 * (n - k)).choose (n - k) := by
    calc
      n.choose k * (n + (n - k)).choose (n - k)
          = (n + (n - k)).choose n * n.choose k := by rw [hsym, mul_comm]
      _ = (n + (n - k)).choose k * (n + (n - k) - k).choose (n - k) := by
            simpa [mul_comm] using hmul
      _ = (n + (n - k)).choose k * (2 * (n - k)).choose (n - k) := by
            have harg : n + (n - k) - k = 2 * (n - k) := by omega
            rw [harg]
  rw [hprod]
  rw [show ((2 * (n - k)).choose (n - k) : ℕ) = Nat.choose (2 * (n - k)) (n - k) by rfl]
  have hc := central_even_zmod (r := n - k) (by omega)
  rw [Nat.cast_mul, hc, mul_zero]

lemma term_flipCore_pack {N : ℕ} {p : P}
    (hp : p ∈ S N) (ht : term N p ≠ 0) :
    term N (flipCore N p) = term N p ∧ flipCore N p ∈ S N ∧ flipCore N (flipCore N p) = p := by
  rcases p with ⟨n,k⟩
  have hp' := (memS_iff (N := N) (p := (⟨n,k⟩ : P))).mp hp
  have hnN : n ≤ N := hp'.1
  have hk : k ≤ n := hp'.2
  simp only [term, flipCore, jval] at ht ⊢
  by_cases hv : n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0
  · simp only [hv, if_true] at ht
    let j := (N - n * (k + 1)) / (n + 1)
    have hN : N = n * (k + 1) + (n + 1) * j := valid_eq hv
    have hv' : (j + k) * (k + 1) ≤ N ∧ (N - (j + k) * (k + 1)) % (j + k + 1) = 0 := by
      have hsub : N - (j + k) * (k + 1) = (j + k + 1) * (n - k) := by
        have hnk : n = k + (n - k) := (Nat.add_sub_of_le hk).symm
        have hsum : N = (j + k + 1) * (n - k) + (j + k) * (k + 1) := by nlinarith [hN, hnk]
        exact Nat.sub_eq_of_eq_add hsum
      constructor
      ·
        have hnk : n = k + (n - k) := (Nat.add_sub_of_le hk).symm
        nlinarith [hN, hnk]
      · rw [hsub]
        exact Nat.mod_eq_zero_of_dvd ⟨n - k, rfl⟩
    have hdiv' : (N - (j + k) * (k + 1)) / (j + k + 1) = n - k := by
      have hsub : N - (j + k) * (k + 1) = (j + k + 1) * (n - k) := by
        have hnk : n = k + (n - k) := (Nat.add_sub_of_le hk).symm
        have hsum : N = (j + k + 1) * (n - k) + (j + k) * (k + 1) := by nlinarith [hN, hnk]
        exact Nat.sub_eq_of_eq_add hsum
      rw [hsub]
      exact Nat.mul_div_right (n - k) (Nat.succ_pos (j + k))
    have hval : (( (j + k).choose k * ((j + k) + (n - k)).choose (n - k) : ℕ) : ZMod 2) =
        ((n.choose k * (n + j).choose j : ℕ) : ZMod 2) := by
      rw [← choose_flip_identity n k j hk]
    have hmem : (⟨j + k, k⟩ : P) ∈ S N := by
      rw [memS_iff]
      constructor
      ·
        have hnk : n = k + (n - k) := (Nat.add_sub_of_le hk).symm
        nlinarith [hN, hnk]
      · exact Nat.le_add_left k j
    have hcore : flipCore N (⟨j + k,k⟩ : P) = (⟨n,k⟩ : P) := by
      simp [flipCore, jval, hdiv', Nat.sub_add_cancel hk]
    constructor
    · have hleft : term N (flipCore N (⟨n,k⟩ : P)) =
          (((j + k).choose k * ((j + k) + (n - k)).choose (n - k) : ℕ) : ZMod 2) := by
        simp [term, flipCore, jval, j, hv', hdiv']
      have hright : term N (⟨n,k⟩ : P) =
          ((n.choose k * (n + j).choose j : ℕ) : ZMod 2) := by
        simp [term, jval, j, hv]
      change term N (flipCore N (⟨n,k⟩ : P)) = term N (⟨n,k⟩ : P)
      rw [hleft, hright]
      exact hval
    constructor
    · simpa [flipCore, jval] using hmem
    · simpa [flipCore, jval] using hcore
  · simp [hv] at ht

lemma fixed_pronic {N : ℕ} {p : P} (hp : p ∈ S N) (ht : term N p ≠ 0) (hfix : flipCore N p = p) :
    ∃ k : ℕ, N = k * (k + 1) := by
  rcases p with ⟨n,k⟩
  have hp' := (memS_iff (N := N) (p := (⟨n,k⟩ : P))).mp hp
  have hk : k ≤ n := hp'.2
  simp only [term, flipCore, jval] at ht hfix
  by_cases hv : n * (k + 1) ≤ N ∧ (N - n * (k + 1)) % (n + 1) = 0
  · simp only [hv, if_true] at ht
    let j := (N - n * (k + 1)) / (n + 1)
    have hN : N = n * (k + 1) + (n + 1) * j := valid_eq hv
    have hjk : j + k = n := by
      have hfix' : (⟨j + k, k⟩ : P) = ⟨n,k⟩ := by simpa [j] using hfix
      exact (Sigma.mk.inj_iff.mp hfix').1
    by_cases hkn : k = n
    · subst k
      have hj0 : j = 0 := by omega
      use n
      nlinarith [hN, hj0]
    · have hlt : k < n := lt_of_le_of_ne hk hkn
      have hj : j = n - k := by omega
      have hz := fixed_even hk hlt hj
      exact False.elim (ht (by simpa [j, hv] using hz))
  · simp [hv] at ht

end A325046Proof

open A325046Proof

/-- oeis_325046_conjecture_0: Odd terms occur only at positions n*(n+1) for n >= 0 (conjecture). -/
theorem a325046_odd_terms_at_k_times_k_plus_1 (N : ℕ) :
  a N % 2 = 1 → ∃ k : ℕ, N = k * (k + 1) :=
by
  classical
  intro hodd
  by_contra hno
  let s := S N
  have hsum0 : ∑ p ∈ s, term N p = 0 := by
    refine Finset.sum_involution (s := s) (f := term N) (g := fun p _ => A325046Proof.flip N p) ?_ ?_ ?_ ?_
    · intro p hp
      by_cases ht : term N p = 0
      · simp [A325046Proof.flip, ht]
      · have hlem := term_flipCore_pack (N := N) (p := p) hp ht
        simp [A325046Proof.flip, ht, hlem.1]
        rw [← two_mul (term N p)]
        rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2, zero_mul]
    · intro p hp ht hfp
      have hcore : flipCore N p = p := by simpa [A325046Proof.flip, ht] using hfp
      exact hno (fixed_pronic (N := N) (p := p) hp ht hcore)
    · intro p hp
      by_cases ht : term N p = 0
      · simpa [A325046Proof.flip, ht] using hp
      · simpa [A325046Proof.flip, ht] using (term_flipCore_pack (N := N) (p := p) hp ht).2.1
    · intro p hp
      by_cases ht : term N p = 0
      · simp [A325046Proof.flip, ht]
      · have hlem := term_flipCore_pack (N := N) (p := p) hp ht
        have ht' : term N (flipCore N p) ≠ 0 := by simpa [hlem.1] using ht
        simp [A325046Proof.flip, ht, ht', hlem.2.2]
  have hcast0 : ((a N : ℕ) : ZMod 2) = 0 := by
    rw [cast_a_eq_sum_term]
    simpa [s] using hsum0
  have hmod0 : a N % 2 = 0 := by
    have hdvd : 2 ∣ a N := (CharP.cast_eq_zero_iff (ZMod 2) 2 (a N)).mp hcast0
    exact Nat.mod_eq_zero_of_dvd hdvd
  omega
