import FormalConjectures.Util.ProblemImports
open Finset
namespace A374605test
set_option maxHeartbeats 2000000

def T (n k : ℕ) : ℤ :=
  ((n.choose k) ^ 2 * ((n + k).choose k) * ((3 * n + 2 * k).choose n) : ℕ)

-- cast helper: nat cleared identity choose_mul_succ_eq m j : m.choose j*(m+1)=(m+1).choose j*(m+1-j)
lemma cms (m j : ℤ) (hm : True) : True := trivial

lemma T_n1_ratio (n k : ℕ) (hk : k ≤ n) :
    (((n:ℤ) + 1 - k) ^ 2 * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2)) * T (n+1) k
      = ((n:ℤ) + 1 + k) * (3 * n + 2 * k + 1) * (3 * n + 2 * k + 2) * (3 * n + 2 * k + 3) * T n k := by
  -- (1) C(n+1,k)*(n+1-k) = C(n,k)*(n+1)
  have hD0 : ((n+1).choose k : ℤ) * ((n:ℤ) + 1 - k) = (n.choose k : ℤ) * ((n:ℤ) + 1) := by
    have := Nat.choose_mul_succ_eq n k
    have h2 : ((n.choose k * (n+1) : ℕ):ℤ) = (((n+1).choose k * (n+1-k) : ℕ):ℤ) := by exact_mod_cast this
    have hsub : (n+1-k : ℕ) = n + 1 - k := rfl
    push_cast [Nat.cast_sub (by omega : k ≤ n+1)] at h2
    linarith [h2]
  have hA2 : ((n+1).choose k : ℤ)^2 * ((n:ℤ)+1-k)^2 = (n.choose k:ℤ)^2 * ((n:ℤ)+1)^2 := by
    have h : (((n+1).choose k : ℤ)*((n:ℤ)+1-k))^2 = ((n.choose k:ℤ)*((n:ℤ)+1))^2 := by rw [hD0]
    linear_combination h
  -- (2) C(n+k+1,k)*(n+1) = C(n+k,k)*(n+k+1)
  have hB : (((n+k+1).choose k : ℤ)) * ((n:ℤ)+1) = ((n+k).choose k:ℤ) * ((n:ℤ)+k+1) := by
    have := Nat.choose_mul_succ_eq (n+k) k
    have h2 : (((n+k).choose k * (n+k+1) : ℕ):ℤ) = (((n+k+1).choose k * (n+k+1-k) : ℕ):ℤ) := by exact_mod_cast this
    have hsub : (n+k+1-k : ℕ) = n+1 := by omega
    rw [hsub] at h2
    push_cast at h2
    linarith [h2]
  -- (3) three top increments -> hTop
  have ht1 : ((3*n+2*k).choose n : ℤ) * (3*n+2*k+1) = ((3*n+2*k+1).choose n:ℤ)*(2*n+2*k+1) := by
    have := Nat.choose_mul_succ_eq (3*n+2*k) n
    have h2 : (((3*n+2*k).choose n * (3*n+2*k+1):ℕ):ℤ) = (((3*n+2*k+1).choose n * (3*n+2*k+1-n):ℕ):ℤ) := by exact_mod_cast this
    have hsub : (3*n+2*k+1-n:ℕ) = 2*n+2*k+1 := by omega
    rw [hsub] at h2; push_cast at h2; linarith [h2]
  have ht2 : ((3*n+2*k+1).choose n : ℤ) * (3*n+2*k+2) = ((3*n+2*k+2).choose n:ℤ)*(2*n+2*k+2) := by
    have := Nat.choose_mul_succ_eq (3*n+2*k+1) n
    have h2 : (((3*n+2*k+1).choose n * (3*n+2*k+1+1):ℕ):ℤ) = (((3*n+2*k+1+1).choose n * (3*n+2*k+1+1-n):ℕ):ℤ) := by exact_mod_cast this
    have hsub : (3*n+2*k+1+1-n:ℕ) = 2*n+2*k+2 := by omega
    have hidx : 3*n+2*k+1+1 = 3*n+2*k+2 := by omega
    rw [hidx, hsub] at h2; push_cast at h2; linarith [h2]
  have ht3 : ((3*n+2*k+2).choose n : ℤ) * (3*n+2*k+3) = ((3*n+2*k+3).choose n:ℤ)*(2*n+2*k+3) := by
    have := Nat.choose_mul_succ_eq (3*n+2*k+2) n
    have h2 : (((3*n+2*k+2).choose n * (3*n+2*k+2+1):ℕ):ℤ) = (((3*n+2*k+2+1).choose n * (3*n+2*k+2+1-n):ℕ):ℤ) := by exact_mod_cast this
    have hsub : (3*n+2*k+2+1-n:ℕ) = 2*n+2*k+3 := by omega
    have hidx : 3*n+2*k+2+1 = 3*n+2*k+3 := by omega
    rw [hidx, hsub] at h2; push_cast at h2; linarith [h2]
  have hTop : ((3*n+2*k).choose n:ℤ)*((3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3))
      = ((3*n+2*k+3).choose n:ℤ)*((2*n+2*k+1)*(2*n+2*k+2)*(2*n+2*k+3)) := by
    have e1 : ((3*n+2*k).choose n:ℤ)*((3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3))
        = (((3*n+2*k).choose n:ℤ)*(3*n+2*k+1))*((3*n+2*k+2)*(3*n+2*k+3)) := by ring
    rw [e1, ht1]
    have e2 : ((3*n+2*k+1).choose n:ℤ)*(2*n+2*k+1)*((3*n+2*k+2)*(3*n+2*k+3))
        = (((3*n+2*k+1).choose n:ℤ)*(3*n+2*k+2))*((2*n+2*k+1)*(3*n+2*k+3)) := by ring
    rw [e2, ht2]
    have e3 : ((3*n+2*k+2).choose n:ℤ)*(2*n+2*k+2)*((2*n+2*k+1)*(3*n+2*k+3))
        = (((3*n+2*k+2).choose n:ℤ)*(3*n+2*k+3))*((2*n+2*k+1)*(2*n+2*k+2)) := by ring
    rw [e3, ht3]; ring
  -- (4) bottom: C(3n+2k+3,n+1)*(n+1)=C(3n+2k+3,n)*(2n+2k+3)
  have hBot : ((3*n+2*k+3).choose (n+1):ℤ)*((n:ℤ)+1) = ((3*n+2*k+3).choose n:ℤ)*(2*n+2*k+3) := by
    have := Nat.choose_succ_right_eq (3*n+2*k+3) n
    have h2 : (((3*n+2*k+3).choose (n+1) * (n+1):ℕ):ℤ) = (((3*n+2*k+3).choose n * (3*n+2*k+3-n):ℕ):ℤ) := by exact_mod_cast this
    have hsub : (3*n+2*k+3-n:ℕ) = 2*n+2*k+3 := by omega
    rw [hsub] at h2; push_cast at h2; linarith [h2]
  -- hC : C(3n+2k+3,n+1)*(n+1)(2n+2k+1)(2n+2k+2) = C(3n+2k,n)*(3n+2k+1)(3n+2k+2)(3n+2k+3)
  have hC : ((3*n+2*k+3).choose (n+1):ℤ)*((n:ℤ)+1)*((2*n+2*k+1)*(2*n+2*k+2))
      = ((3*n+2*k).choose n:ℤ)*((3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3)) := by
    linear_combination (2*(n:ℤ)+2*k+1)*(2*(n:ℤ)+2*k+2)*hBot - hTop
  -- expand T
  have hTn1 : T (n+1) k = ((n+1).choose k:ℤ)^2 * ((n+k+1).choose k:ℤ) * ((3*n+2*k+3).choose (n+1):ℤ) := by
    unfold T
    have i1 : (n+1+k) = n+k+1 := by omega
    have i2 : 3*(n+1)+2*k = 3*n+2*k+3 := by omega
    rw [i1, i2]; push_cast; ring
  have hTn : T n k = (n.choose k:ℤ)^2 * ((n+k).choose k:ℤ) * ((3*n+2*k).choose n:ℤ) := by
    unfold T; push_cast; ring
  rw [hTn1, hTn]
  -- product key with surplus (n+1)^2
  have key : ((n:ℤ)+1)^2 * ((((n:ℤ)+1-k)^2 * (2*n+2*k+1) * (2*n+2*k+2)) *
        (((n+1).choose k:ℤ)^2 * ((n+k+1).choose k:ℤ) * ((3*n+2*k+3).choose (n+1):ℤ)))
      = ((n:ℤ)+1)^2 * (((n:ℤ)+1+k) * (3*n+2*k+1) * (3*n+2*k+2) * (3*n+2*k+3) *
        ((n.choose k:ℤ)^2 * ((n+k).choose k:ℤ) * ((3*n+2*k).choose n:ℤ))) := by
    linear_combination
      ( ((n+k+1).choose k:ℤ) * ((3*n+2*k+3).choose (n+1):ℤ) * ((n:ℤ)+1)^2 * (2*(n:ℤ)+2*k+1)*(2*(n:ℤ)+2*k+2) ) * hA2
      + ( (n.choose k:ℤ)^2 * ((3*n+2*k+3).choose (n+1):ℤ) * ((n:ℤ)+1)^3 * (2*(n:ℤ)+2*k+1)*(2*(n:ℤ)+2*k+2) ) * hB
      + ( (n.choose k:ℤ)^2 * ((n+k).choose k:ℤ) * ((n:ℤ)+1)^2 * ((n:ℤ)+1+k) ) * hC
  have hne : ((n:ℤ)+1)^2 ≠ 0 := by positivity
  exact mul_left_cancel₀ hne key

lemma T_pos (m k : ℕ) (hk : k ≤ m) : 0 < T m k := by
  unfold T
  have h1 : 0 < m.choose k := Nat.choose_pos hk
  have h2 : 0 < (m+k).choose k := Nat.choose_pos (by omega)
  have h3 : 0 < (3*m+2*k).choose m := Nat.choose_pos (by omega)
  have : 0 < m.choose k ^2 * ((m+k).choose k) * ((3*m+2*k).choose m) := by positivity
  exact_mod_cast this

lemma T_n2_ratio (n k : ℕ) (hk : k ≤ n) :
    (((n:ℤ)+2-k)^2*((n:ℤ)+1-k)^2*(2*n+2*k+3)*(2*n+2*k+4)*(2*n+2*k+1)*(2*n+2*k+2))*T (n+2) k
      = ((n:ℤ)+2+k)*((n:ℤ)+1+k)*(3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3)*(3*n+2*k+4)*(3*n+2*k+5)*(3*n+2*k+6)*T n k := by
  have h1 := T_n1_ratio n k hk
  have h2 := T_n1_ratio (n+1) k (by omega)
  push_cast at h2
  have hpos : T (n+1) k ≠ 0 := ne_of_gt (T_pos (n+1) k (by omega))
  -- product identity, then cancel T(n+1) k
  have key : T (n+1) k * ((((n:ℤ)+2-k)^2*((n:ℤ)+1-k)^2*(2*n+2*k+3)*(2*n+2*k+4)*(2*n+2*k+1)*(2*n+2*k+2))*T (n+2) k)
      = T (n+1) k * (((n:ℤ)+2+k)*((n:ℤ)+1+k)*(3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3)*(3*n+2*k+4)*(3*n+2*k+5)*(3*n+2*k+6)*T n k) := by
    linear_combination (((n:ℤ)+2-k)^2 * (2*(n:ℤ)+2*k+3)*(2*(n:ℤ)+2*k+4) * T (n+2) k) * h1
      + (((n:ℤ)+1+k)*(3*(n:ℤ)+2*k+1)*(3*(n:ℤ)+2*k+2)*(3*(n:ℤ)+2*k+3) * T n k) * h2
  exact mul_left_cancel₀ hpos key

end A374605test
