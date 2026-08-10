import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

/--
A282459: Number of composite numbers of the form $2n - 2^k + 1$ ($k > 0, 2^k < 2n + 1$).
-/
def A282459 (n : ℕ) : ℕ :=
  -- The upper bound for k is $\lfloor \log_2(2n+1) \rfloor$.
  let upper_k : ℕ := log 2 (2 * n + 1)
  -- The set of $k$ values is $1 \le k \le \lfloor \log_2(2n+1) \rfloor$.
  let s := Finset.Icc 1 upper_k

  -- A natural number $m$ is composite if $m > 1$ and $m$ is not a prime.
  -- We must use Nat.Prime explicitly in this context.
  let is_composite (m : ℕ) : Prop := 1 < m ∧ ¬ Nat.Prime m

  -- The value we are checking for compositeness. The subtraction is safe since $2^k \le 2n+1$.
  -- The subtraction is safe because $k \le \log_2(2n+1)$, which implies $2^k \le 2n+1$.
  let seq_val (k : ℕ) : ℕ := 2 * n + 1 - 2 ^ k

  -- We count how many $k$ in the set $s$ make `seq_val k` composite.
  Finset.card (Finset.filter (fun k : ℕ => is_composite (seq_val k)) s)

lemma A282459_pos_of_exists (n : ℕ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)))
    (h_comp : 1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k)) : A282459 n > 0 := by
  have h_comp' : (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k)) := h_comp
  unfold A282459
  dsimp
  have hk_filter : k ∈ Finset.filter (fun k => (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k))) (Finset.Icc 1 (log 2 (2 * n + 1))) := by
    rw [Finset.mem_filter]
    exact ⟨hk, h_comp'⟩
  have h_nonempty : (Finset.filter (fun k => (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k))) (Finset.Icc 1 (log 2 (2 * n + 1)))).Nonempty := by
    exact ⟨k, hk_filter⟩
  exact Finset.card_pos.mpr h_nonempty

lemma k_in_Icc (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2*n+1) : k ∈ Finset.Icc 1 (log 2 (2*n+1)) := by
  rw [Finset.mem_Icc]
  refine ⟨hk1, ?_⟩
  exact Nat.le_log_of_pow_le Nat.one_lt_two hk2

lemma dvd_of_mod_eq (N k p : ℕ) (hN : N % p = 2^k % p) (hk : 2^k ≤ N) : p ∣ N - 2^k := by
  have h_modeq : 2^k ≡ N [MOD p] := by
    exact hN.symm
  exact (Nat.modEq_iff_dvd' hk).mp h_modeq

lemma composite_of_dvd (N : ℕ) (k : ℕ) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ N - 2^k) (hgt : p < N - 2^k) (h1 : 1 < N - 2^k) :
    1 < N - 2^k ∧ ¬ Nat.Prime (N - 2^k) := by
  refine ⟨h1, ?_⟩
  intro h_prime
  have h_dvd_eq : p = N - 2^k := by
    exact ((Nat.Prime.dvd_iff_eq h_prime hp.ne_one).mp hdvd).symm
  omega

def certificate : ℕ → ℕ
  | 53 => 1
  | 54 => 2
  | 55 => 4
  | 56 => 1
  | 57 => 2
  | 58 => 1
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 1
  | 63 => 1
  | 64 => 2
  | 65 => 1
  | 66 => 2
  | 67 => 1
  | 68 => 1
  | 69 => 2
  | 70 => 3
  | 71 => 1
  | 72 => 1
  | 73 => 1
  | 74 => 1
  | 75 => 2
  | 76 => 3
  | 77 => 1
  | 78 => 1
  | 79 => 2
  | 80 => 1
  | 81 => 1
  | 82 => 2
  | 83 => 1
  | 84 => 2
  | 85 => 1
  | 86 => 1
  | 87 => 2
  | 88 => 1
  | 89 => 1
  | 90 => 2
  | 91 => 3
  | 92 => 1
  | 93 => 1
  | 94 => 1
  | 95 => 1
  | 96 => 2
  | 97 => 3
  | 98 => 1
  | 99 => 2
  | 100 => 4
  | 101 => 1
  | 102 => 1
  | 103 => 1
  | 104 => 1
  | 105 => 1
  | 106 => 2
  | 107 => 1
  | 108 => 1
  | 109 => 1
  | 110 => 1
  | 111 => 1
  | 112 => 2
  | 113 => 1
  | 114 => 2
  | 115 => 4
  | 116 => 1
  | 117 => 2
  | 118 => 1
  | 119 => 1
  | 120 => 2
  | 121 => 3
  | 122 => 1
  | 123 => 1
  | 124 => 1
  | 125 => 1
  | 126 => 2
  | 127 => 1
  | 128 => 1
  | 129 => 2
  | 130 => 1
  | 131 => 1
  | 132 => 2
  | 133 => 1
  | 134 => 1
  | 135 => 2
  | 136 => 3
  | 137 => 1
  | 138 => 1
  | 139 => 2
  | 140 => 1
  | 141 => 2
  | 142 => 5
  | 143 => 1
  | 144 => 1
  | 145 => 1
  | 146 => 1
  | 147 => 2
  | 148 => 1
  | 149 => 1
  | 150 => 1
  | 151 => 1
  | 152 => 1
  | 153 => 1
  | 154 => 2
  | 155 => 1
  | 156 => 2
  | 157 => 4
  | 158 => 1
  | 159 => 2
  | 160 => 1
  | 161 => 1
  | 162 => 1
  | 163 => 1
  | 164 => 1
  | 165 => 1
  | 166 => 2
  | 167 => 1
  | 168 => 1
  | 169 => 2
  | 170 => 1
  | 171 => 1
  | 172 => 1
  | 173 => 1
  | 174 => 2
  | 175 => 3
  | 176 => 1
  | 177 => 2
  | 178 => 1
  | 179 => 1
  | 180 => 2
  | 181 => 1
  | 182 => 1
  | 183 => 1
  | 184 => 2
  | 185 => 1
  | 186 => 1
  | 187 => 2
  | 188 => 1
  | 189 => 1
  | 190 => 2
  | 191 => 1
  | 192 => 2
  | 193 => 1
  | 194 => 1
