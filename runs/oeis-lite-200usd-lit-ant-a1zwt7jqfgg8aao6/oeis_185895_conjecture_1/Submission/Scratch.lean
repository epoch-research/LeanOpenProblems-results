import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

/-- triangular number -/
def Tn (e : ℕ) : ℕ := e * (e+1) / 2

/-- `tri n` = the largest `e` with `Tn e ≤ n`. -/
def tri (n : ℕ) : ℕ := Nat.findGreatest (fun e => Tn e ≤ n) n

def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

lemma two_Tn (e : ℕ) : 2 * Tn e = e * (e + 1) := by
  unfold Tn
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self e).two_dvd

lemma Tn_succ (e : ℕ) : Tn (e+1) = Tn e + (e+1) := by
  have h1 := two_Tn e
  have h2 := two_Tn (e+1)
  have h3 : (e+1) * ((e+1)+1) = e * (e+1) + 2*(e+1) := by ring
  omega

lemma Tn_mono : Monotone Tn :=
  monotone_nat_of_le_succ (fun n => by rw [Tn_succ]; omega)

lemma k_le_Tn (k : ℕ) : k ≤ Tn k := by
  have h := two_Tn k
  nlinarith [h, Nat.zero_le k]

lemma tri_spec (n : ℕ) : Tn (tri n) ≤ n :=
  Nat.findGreatest_spec (P := fun e => Tn e ≤ n) (m := 0) (Nat.zero_le n)
    (Nat.zero_le n)

lemma tri_le (n : ℕ) : tri n ≤ n := Nat.findGreatest_le n

lemma tri_lt (n : ℕ) : n < Tn (tri n + 1) := by
  by_contra h
  push_neg at h
  have hge : tri n + 1 ≤ Tn (tri n + 1) := by rw [Tn_succ]; omega
  have hb : tri n + 1 ≤ n := le_trans hge h
  have hg : ¬ (Tn (tri n + 1) ≤ n) :=
    Nat.findGreatest_is_greatest (P := fun e => Tn e ≤ n) (Nat.lt_succ_self _) hb
  exact hg h

lemma tri_mono : Monotone tri := by
  intro a b hab
  unfold tri
  exact Nat.findGreatest_mono (fun e he => le_trans he hab) hab

lemma is_tri_iff (n : ℕ) : is_triangular n ↔ Tn (tri n) = n := by
  constructor
  · rintro ⟨k, hk⟩
    have hnk : n = Tn k := hk
    have hkn : k ≤ n := by rw [hnk]; exact k_le_Tn k
    have h1 : k ≤ tri n := Nat.le_findGreatest hkn (by show Tn k ≤ n; omega)
    have h2 : Tn k ≤ Tn (tri n) := Tn_mono h1
    have h3 : Tn (tri n) ≤ n := tri_spec n
    omega
  · intro h; exact ⟨tri n, h.symm⟩

lemma tri_succ_le (n : ℕ) (hn : 1 ≤ n) : tri n ≤ tri (n-1) + 1 := by
  by_contra h
  push_neg at h
  have h2 : tri (n-1) + 1 + 1 ≤ tri n := by omega
  have hmono : Tn (tri (n-1) + 1 + 1) ≤ Tn (tri n) := Tn_mono h2
  have hspec : Tn (tri n) ≤ n := tri_spec n
  have hlt : n - 1 < Tn (tri (n-1) + 1) := tri_lt (n-1)
  have hsucc := Tn_succ (tri (n-1) + 1)
  omega

lemma tri_succ_cases (n : ℕ) (hn : 1 ≤ n) :
    tri n = tri (n-1) ∨ tri n = tri (n-1) + 1 := by
  have h1 : tri (n-1) ≤ tri n := tri_mono (by omega)
  have h2 : tri n ≤ tri (n-1) + 1 := tri_succ_le n hn
  omega

lemma tri_jump_iff (n : ℕ) (hn : 1 ≤ n) :
    tri n = tri (n-1) + 1 ↔ is_triangular n := by
  rw [is_tri_iff]
  constructor
  · intro hj
    rw [hj]
    have hlt : n - 1 < Tn (tri (n-1) + 1) := tri_lt (n-1)
    have hspec : Tn (tri n) ≤ n := tri_spec n
    rw [hj] at hspec
    omega
  · intro heq
    rcases tri_succ_cases n hn with hc | hc
    · exfalso
      have hspec : Tn (tri (n-1)) ≤ n - 1 := tri_spec (n-1)
      rw [← hc] at hspec
      omega
    · exact hc

-- ====== A185895 (exact copy of the conjecture's definition) ======
noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)
  let coeff_n : ℚ := Polynomial.coeff Px n
  let a_n_q : ℚ := coeff_n * n.factorial.cast
  a_n_q.floor

/-- `(-1)^(tri m) * A185895 m`, conjecturally always positive. -/
noncomputable def psign (m : ℕ) : ℤ := (-1)^(tri m) * A185895 m

/-- THE HARD KERNEL: equivalent (via the combinatorial reduction) to
    log-concavity/monotonicity of the count of set partitions into distinct
    block sizes by number of blocks. -/
lemma psign_pos (m : ℕ) : 0 < psign m := by sorry

lemma A185895_eq (m : ℕ) : A185895 m = (-1)^(tri m) * psign m := by
  unfold psign
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem final (n : ℕ) (hn : 0 < n) :
    A185895 n * A185895 (n-1) < 0 ↔ is_triangular n := by
  have pn : 0 < psign n := psign_pos n
  have pm : 0 < psign (n-1) := psign_pos (n-1)
  have prod_pos : 0 < psign n * psign (n-1) := mul_pos pn pm
  rw [A185895_eq n, A185895_eq (n-1)]
  have hrw : ((-1:ℤ)^(tri n) * psign n) * ((-1)^(tri (n-1)) * psign (n-1))
      = (-1)^(tri n + tri (n-1)) * (psign n * psign (n-1)) := by
    rw [pow_add]; ring
  rw [hrw, ← tri_jump_iff n hn]
  set C := psign n * psign (n-1) with hC
  rcases tri_succ_cases n hn with hc | hc
  · have hpow : (-1:ℤ)^(tri n + tri (n-1)) = 1 := by
      rw [hc, ← two_mul, pow_mul]; norm_num
    rw [hpow]; constructor <;> intro h <;> omega
  · have hpow : (-1:ℤ)^(tri n + tri (n-1)) = -1 := by
      rw [hc]
      have h2 : (tri (n-1) + 1) + tri (n-1) = 2 * tri (n-1) + 1 := by ring
      rw [h2, pow_succ, pow_mul]; norm_num
    rw [hpow]; constructor <;> intro h <;> omega
