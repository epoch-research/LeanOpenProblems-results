import FormalConjectures.Util.ProblemImports

open Finset

namespace A374605

/-- The summand `T(n,k) = C(n,k)^2 * C(n+k,k) * C(3n+2k,n)`. -/
def T (n k : ℕ) : ℤ :=
  ((n.choose k) ^ 2 * ((n + k).choose k) * ((3 * n + 2 * k).choose n) : ℕ)

/-- `a(n) = ∑_{k=0}^n T(n,k)`. -/
def aSeq (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), T n k

/-- k-shift ratio for the summand, valid for `k ≤ n`. -/
lemma T_k_ratio (n k : ℕ) (hk : k ≤ n) :
    ((k + 1) ^ 3 * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2) : ℤ) * T n (k + 1)
      = ((n - k : ℤ)) ^ 2 * (n + k + 1) * (3 * n + 2 * k + 1) * (3 * n + 2 * k + 2) * T n k := by
  -- The three cleared binomial ratio facts, as ℤ-equations.
  have hA : (n.choose (k + 1) : ℤ) * (k + 1) = (n.choose k : ℤ) * ((n : ℤ) - k) := by
    have := Nat.choose_succ_right_eq n k
    have h2 : ((n.choose (k + 1) * (k + 1) : ℕ) : ℤ) = ((n.choose k * (n - k) : ℕ) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) this
    push_cast [Nat.cast_sub hk] at h2
    linarith [h2]
  have hB : ((n + k + 1).choose (k + 1) : ℤ) * (k + 1)
      = ((n : ℤ) + k + 1) * ((n + k).choose k : ℤ) := by
    have := Nat.succ_mul_choose_eq (n + k) k
    have h2 : (((n + k).succ * (n + k).choose k : ℕ) : ℤ)
        = (((n + k).succ.choose (k + 1) * (k + 1) : ℕ) : ℤ) := by exact_mod_cast this
    have hidx : (n + k).succ.choose (k + 1) = (n + k + 1).choose (k + 1) := by
      congr 1
    push_cast [hidx] at h2 ⊢
    linarith [h2]
  -- top-increment facts for C(3n+2k+·, n)
  have hC1 : ((3 * n + 2 * k).choose n : ℤ) * (3 * n + 2 * k + 1)
      = ((3 * n + 2 * k + 1).choose n : ℤ) * (2 * n + 2 * k + 1) := by
    have := Nat.choose_mul_succ_eq (3 * n + 2 * k) n
    have h2 : (((3 * n + 2 * k).choose n * (3 * n + 2 * k + 1) : ℕ) : ℤ)
        = (((3 * n + 2 * k + 1).choose n * (3 * n + 2 * k + 1 - n) : ℕ) : ℤ) := by
      exact_mod_cast this
    have hsub : 3 * n + 2 * k + 1 - n = 2 * n + 2 * k + 1 := by omega
    push_cast [hsub] at h2
    linarith [h2]
  have hC2 : ((3 * n + 2 * k + 1).choose n : ℤ) * (3 * n + 2 * k + 2)
      = ((3 * n + 2 * k + 2).choose n : ℤ) * (2 * n + 2 * k + 2) := by
    have := Nat.choose_mul_succ_eq (3 * n + 2 * k + 1) n
    have h2 : (((3 * n + 2 * k + 1).choose n * (3 * n + 2 * k + 1 + 1) : ℕ) : ℤ)
        = (((3 * n + 2 * k + 1 + 1).choose n * (3 * n + 2 * k + 1 + 1 - n) : ℕ) : ℤ) := by
      exact_mod_cast this
    have hsub : 3 * n + 2 * k + 1 + 1 - n = 2 * n + 2 * k + 2 := by omega
    have hidx : 3 * n + 2 * k + 1 + 1 = 3 * n + 2 * k + 2 := by omega
    rw [hidx] at h2
    push_cast [hsub] at h2
    linarith [h2]
  -- combine hC1, hC2 into C(3n+2k+2,n)*(2n+2k+1)*(2n+2k+2) = C(3n+2k,n)*(3n+2k+1)*(3n+2k+2)
  have hC : ((3 * n + 2 * k + 2).choose n : ℤ) * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2)
      = ((3 * n + 2 * k).choose n : ℤ) * (3 * n + 2 * k + 1) * (3 * n + 2 * k + 2) := by
    nlinarith [hC1, hC2]
  -- Unfold T into ℤ binomials.
  have hTk1 : T n (k + 1) = (n.choose (k + 1) : ℤ) ^ 2 * ((n + (k + 1)).choose (k + 1) : ℤ)
      * ((3 * n + 2 * (k + 1)).choose n : ℤ) := by
    unfold T; push_cast; ring
  have hTk : T n k = (n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)
      * ((3 * n + 2 * k).choose n : ℤ) := by
    unfold T; push_cast; ring
  have hidx1 : (n + (k + 1)).choose (k + 1) = (n + k + 1).choose (k + 1) := by
    congr 1
  have hidx2 : (3 * n + 2 * (k + 1)).choose n = (3 * n + 2 * k + 2).choose n := by
    congr 1
  rw [hTk1, hTk, hidx1, hidx2]
  -- Now the goal is a product identity; combine hA (squared), hB, hC.
  have hA2 : (n.choose (k + 1) : ℤ) ^ 2 * (k + 1) ^ 2
      = (n.choose k : ℤ) ^ 2 * ((n : ℤ) - k) ^ 2 := by
    have h : ((n.choose (k + 1) : ℤ) * (k + 1)) ^ 2 = ((n.choose k : ℤ) * ((n : ℤ) - k)) ^ 2 := by
      rw [hA]
    linear_combination h
  have key : ((n.choose (k + 1) : ℤ) ^ 2 * (k + 1) ^ 2)
        * ((n + k + 1).choose (k + 1) * (k + 1))
        * ((3 * n + 2 * k + 2).choose n * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2))
      = ((n.choose k : ℤ) ^ 2 * ((n : ℤ) - k) ^ 2)
        * (((n : ℤ) + k + 1) * ((n + k).choose k))
        * ((3 * n + 2 * k).choose n * (3 * n + 2 * k + 1) * (3 * n + 2 * k + 2)) := by
    rw [hA2, hB, hC]
  linear_combination key

set_option maxHeartbeats 2000000 in
lemma T_n1_ratio (n k : ℕ) (hk : k ≤ n) :
    (((n:ℤ) + 1 - k) ^ 2 * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2)) * T (n+1) k
      = ((n:ℤ) + 1 + k) * (3 * n + 2 * k + 1) * (3 * n + 2 * k + 2) * (3 * n + 2 * k + 3) * T n k := by
  have hD0 : ((n+1).choose k : ℤ) * ((n:ℤ) + 1 - k) = (n.choose k : ℤ) * ((n:ℤ) + 1) := by
    have := Nat.choose_mul_succ_eq n k
    have h2 : ((n.choose k * (n+1) : ℕ):ℤ) = (((n+1).choose k * (n+1-k) : ℕ):ℤ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (by omega : k ≤ n+1)] at h2
    linarith [h2]
  have hA2 : ((n+1).choose k : ℤ)^2 * ((n:ℤ)+1-k)^2 = (n.choose k:ℤ)^2 * ((n:ℤ)+1)^2 := by
    have h : (((n+1).choose k : ℤ)*((n:ℤ)+1-k))^2 = ((n.choose k:ℤ)*((n:ℤ)+1))^2 := by rw [hD0]
    linear_combination h
  have hB : (((n+k+1).choose k : ℤ)) * ((n:ℤ)+1) = ((n+k).choose k:ℤ) * ((n:ℤ)+k+1) := by
    have := Nat.choose_mul_succ_eq (n+k) k
    have h2 : (((n+k).choose k * (n+k+1) : ℕ):ℤ) = (((n+k+1).choose k * (n+k+1-k) : ℕ):ℤ) := by exact_mod_cast this
    have hsub : (n+k+1-k : ℕ) = n+1 := by omega
    rw [hsub] at h2
    push_cast at h2
    linarith [h2]
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
  have hBot : ((3*n+2*k+3).choose (n+1):ℤ)*((n:ℤ)+1) = ((3*n+2*k+3).choose n:ℤ)*(2*n+2*k+3) := by
    have := Nat.choose_succ_right_eq (3*n+2*k+3) n
    have h2 : (((3*n+2*k+3).choose (n+1) * (n+1):ℕ):ℤ) = (((3*n+2*k+3).choose n * (3*n+2*k+3-n):ℕ):ℤ) := by exact_mod_cast this
    have hsub : (3*n+2*k+3-n:ℕ) = 2*n+2*k+3 := by omega
    rw [hsub] at h2; push_cast at h2; linarith [h2]
  have hC : ((3*n+2*k+3).choose (n+1):ℤ)*((n:ℤ)+1)*((2*n+2*k+1)*(2*n+2*k+2))
      = ((3*n+2*k).choose n:ℤ)*((3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3)) := by
    linear_combination (2*(n:ℤ)+2*k+1)*(2*(n:ℤ)+2*k+2)*hBot - hTop
  have hTn1 : T (n+1) k = ((n+1).choose k:ℤ)^2 * ((n+k+1).choose k:ℤ) * ((3*n+2*k+3).choose (n+1):ℤ) := by
    unfold T
    have i1 : (n+1+k) = n+k+1 := by omega
    have i2 : 3*(n+1)+2*k = 3*n+2*k+3 := by omega
    rw [i1, i2]; push_cast; ring
  have hTn : T n k = (n.choose k:ℤ)^2 * ((n+k).choose k:ℤ) * ((3*n+2*k).choose n:ℤ) := by
    unfold T; push_cast; ring
  rw [hTn1, hTn]
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

set_option maxHeartbeats 2000000 in
lemma T_n2_ratio (n k : ℕ) (hk : k ≤ n) :
    (((n:ℤ)+2-k)^2*((n:ℤ)+1-k)^2*(2*n+2*k+3)*(2*n+2*k+4)*(2*n+2*k+1)*(2*n+2*k+2))*T (n+2) k
      = ((n:ℤ)+2+k)*((n:ℤ)+1+k)*(3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3)*(3*n+2*k+4)*(3*n+2*k+5)*(3*n+2*k+6)*T n k := by
  have h1 := T_n1_ratio n k hk
  have h2 := T_n1_ratio (n+1) k (by omega)
  push_cast at h2
  have hpos : T (n+1) k ≠ 0 := ne_of_gt (T_pos (n+1) k (by omega))
  have key : T (n+1) k * ((((n:ℤ)+2-k)^2*((n:ℤ)+1-k)^2*(2*n+2*k+3)*(2*n+2*k+4)*(2*n+2*k+1)*(2*n+2*k+2))*T (n+2) k)
      = T (n+1) k * (((n:ℤ)+2+k)*((n:ℤ)+1+k)*(3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3)*(3*n+2*k+4)*(3*n+2*k+5)*(3*n+2*k+6)*T n k) := by
    linear_combination (((n:ℤ)+2-k)^2 * (2*(n:ℤ)+2*k+3)*(2*(n:ℤ)+2*k+4) * T (n+2) k) * h1
      + (((n:ℤ)+1+k)*(3*(n:ℤ)+2*k+1)*(3*(n:ℤ)+2*k+2)*(3*(n:ℤ)+2*k+3) * T n k) * h2
  exact mul_left_cancel₀ hpos key

set_option maxHeartbeats 8000000 in
lemma CERT (n k : ℕ) (hk : k ≤ n) :
    ((((k:ℤ)+1)^3*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+2-(k:ℤ))^2*((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+3)*(2*(n:ℤ)+2*(k:ℤ)+4)*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2)))*((((k:ℤ)-(n:ℤ)-2)^2*((k:ℤ)-(n:ℤ)-1)^2*(2*(k:ℤ)+2*(n:ℤ)+1)*(2*(k:ℤ)+2*(n:ℤ)+3))*((((k:ℤ)+1)-(n:ℤ)-2)^2*(((k:ℤ)+1)-(n:ℤ)-1)^2*(2*((k:ℤ)+1)+2*(n:ℤ)+1)*(2*((k:ℤ)+1)+2*(n:ℤ)+3))*((-27*((n:ℤ)+2)*(3*(n:ℤ)+1)^3*(3*(n:ℤ)+2)^3*(5616*(n:ℤ)^4+36504*(n:ℤ)^3+88731*(n:ℤ)^2+95597*(n:ℤ)+38524))*T n k + (-36*(72783360*(n:ℤ)^11+946183680*(n:ℤ)^10+5506947648*(n:ℤ)^9+18919626192*(n:ℤ)^8+42578365230*(n:ℤ)^7+65816429067*(n:ℤ)^6+71201437287*(n:ℤ)^5+53826632241*(n:ℤ)^4+27825371259*(n:ℤ)^3+9355168720*(n:ℤ)^2+1839302884*(n:ℤ)+160171824))*T (n+1) k + (16*((n:ℤ)+2)^3*(4*(n:ℤ)+5)^2*(4*(n:ℤ)+7)^2*(5616*(n:ℤ)^4+14040*(n:ℤ)^3+12915*(n:ℤ)^2+5183*(n:ℤ)+770))*T (n+2) k))
      = ((((k:ℤ)+1)^3*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+2-(k:ℤ))^2*((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+3)*(2*(n:ℤ)+2*(k:ℤ)+4)*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2)))*(((-2*((n:ℤ) + 2)*(2*(n:ℤ) + 3)*(7443918144*(n:ℤ)^12 + 89116249248*(n:ℤ)^11 + 477840074580*(n:ℤ)^10 + 1516263919164*(n:ℤ)^9 + 3169124935875*(n:ℤ)^8 + 4594117665555*(n:ℤ)^7 + 4735175091369*(n:ℤ)^6 + 3496319453673*(n:ℤ)^5 + 1835935007068*(n:ℤ)^4 + 668997560020*(n:ℤ)^3 + 160713656664*(n:ℤ)^2 + 22879883456*(n:ℤ) + 1461816416))*((k:ℤ)+1)^3+(-4*(18305621568*(n:ℤ)^13 + 273105304992*(n:ℤ)^12 + 1842407135748*(n:ℤ)^11 + 7437061820052*(n:ℤ)^10 + 20028491704269*(n:ℤ)^9 + 37975813201446*(n:ℤ)^8 + 52123803673807*(n:ℤ)^7 + 52405603615060*(n:ℤ)^6 + 38576280206275*(n:ℤ)^5 + 20526676991678*(n:ℤ)^4 + 7673131778065*(n:ℤ)^3 + 1908366092756*(n:ℤ)^2 + 283149068988*(n:ℤ) + 18942724912))*((k:ℤ)+1)^4+(-2*(21890808576*(n:ℤ)^12 + 339833594880*(n:ℤ)^11 + 2321104646736*(n:ℤ)^10 + 9265255782552*(n:ℤ)^9 + 24140882338866*(n:ℤ)^8 + 43328406576355*(n:ℤ)^7 + 54990507929117*(n:ℤ)^6 + 49762169872427*(n:ℤ)^5 + 31883705838225*(n:ℤ)^4 + 14113298198830*(n:ℤ)^3 + 4099193857060*(n:ℤ)^2 + 701980041656*(n:ℤ) + 53658128736))*((k:ℤ)+1)^5+(4*(5161283712*(n:ℤ)^11 + 43526313792*(n:ℤ)^10 + 129024803448*(n:ℤ)^9 + 62506209504*(n:ℤ)^8 - 610076329415*(n:ℤ)^7 - 1940763038281*(n:ℤ)^6 - 3009256822395*(n:ℤ)^5 - 2842821940351*(n:ℤ)^4 - 1707155168938*(n:ℤ)^3 - 637385936508*(n:ℤ)^2 - 135052337544*(n:ℤ) - 12414205600))*((k:ℤ)+1)^6+(8*(3578661216*(n:ℤ)^10 + 37524719232*(n:ℤ)^9 + 171994706550*(n:ℤ)^8 + 452639126431*(n:ℤ)^7 + 755370436273*(n:ℤ)^6 + 832865889191*(n:ℤ)^5 + 612665563417*(n:ℤ)^4 + 296016335294*(n:ℤ)^3 + 89615097604*(n:ℤ)^2 + 15289391032*(n:ℤ) + 1109552736))*((k:ℤ)+1)^7+(16*(478084464*(n:ℤ)^9 + 4884878232*(n:ℤ)^8 + 21665145987*(n:ℤ)^7 + 54638336225*(n:ℤ)^6 + 86179658227*(n:ℤ)^5 + 87993309183*(n:ℤ)^4 + 58065207134*(n:ℤ)^3 + 23852127404*(n:ℤ)^2 + 5533215480*(n:ℤ) + 552935264))*((k:ℤ)+1)^8)*(((k:ℤ)-(n:ℤ)-2)^2*((k:ℤ)-(n:ℤ)-1)^2*(2*(k:ℤ)+2*(n:ℤ)+1)*(2*(k:ℤ)+2*(n:ℤ)+3))*T n (k+1) - ((-2*((n:ℤ) + 2)*(2*(n:ℤ) + 3)*(7443918144*(n:ℤ)^12 + 89116249248*(n:ℤ)^11 + 477840074580*(n:ℤ)^10 + 1516263919164*(n:ℤ)^9 + 3169124935875*(n:ℤ)^8 + 4594117665555*(n:ℤ)^7 + 4735175091369*(n:ℤ)^6 + 3496319453673*(n:ℤ)^5 + 1835935007068*(n:ℤ)^4 + 668997560020*(n:ℤ)^3 + 160713656664*(n:ℤ)^2 + 22879883456*(n:ℤ) + 1461816416))*(k:ℤ)^3+(-4*(18305621568*(n:ℤ)^13 + 273105304992*(n:ℤ)^12 + 1842407135748*(n:ℤ)^11 + 7437061820052*(n:ℤ)^10 + 20028491704269*(n:ℤ)^9 + 37975813201446*(n:ℤ)^8 + 52123803673807*(n:ℤ)^7 + 52405603615060*(n:ℤ)^6 + 38576280206275*(n:ℤ)^5 + 20526676991678*(n:ℤ)^4 + 7673131778065*(n:ℤ)^3 + 1908366092756*(n:ℤ)^2 + 283149068988*(n:ℤ) + 18942724912))*(k:ℤ)^4+(-2*(21890808576*(n:ℤ)^12 + 339833594880*(n:ℤ)^11 + 2321104646736*(n:ℤ)^10 + 9265255782552*(n:ℤ)^9 + 24140882338866*(n:ℤ)^8 + 43328406576355*(n:ℤ)^7 + 54990507929117*(n:ℤ)^6 + 49762169872427*(n:ℤ)^5 + 31883705838225*(n:ℤ)^4 + 14113298198830*(n:ℤ)^3 + 4099193857060*(n:ℤ)^2 + 701980041656*(n:ℤ) + 53658128736))*(k:ℤ)^5+(4*(5161283712*(n:ℤ)^11 + 43526313792*(n:ℤ)^10 + 129024803448*(n:ℤ)^9 + 62506209504*(n:ℤ)^8 - 610076329415*(n:ℤ)^7 - 1940763038281*(n:ℤ)^6 - 3009256822395*(n:ℤ)^5 - 2842821940351*(n:ℤ)^4 - 1707155168938*(n:ℤ)^3 - 637385936508*(n:ℤ)^2 - 135052337544*(n:ℤ) - 12414205600))*(k:ℤ)^6+(8*(3578661216*(n:ℤ)^10 + 37524719232*(n:ℤ)^9 + 171994706550*(n:ℤ)^8 + 452639126431*(n:ℤ)^7 + 755370436273*(n:ℤ)^6 + 832865889191*(n:ℤ)^5 + 612665563417*(n:ℤ)^4 + 296016335294*(n:ℤ)^3 + 89615097604*(n:ℤ)^2 + 15289391032*(n:ℤ) + 1109552736))*(k:ℤ)^7+(16*(478084464*(n:ℤ)^9 + 4884878232*(n:ℤ)^8 + 21665145987*(n:ℤ)^7 + 54638336225*(n:ℤ)^6 + 86179658227*(n:ℤ)^5 + 87993309183*(n:ℤ)^4 + 58065207134*(n:ℤ)^3 + 23852127404*(n:ℤ)^2 + 5533215480*(n:ℤ) + 552935264))*(k:ℤ)^8)*((((k:ℤ)+1)-(n:ℤ)-2)^2*(((k:ℤ)+1)-(n:ℤ)-1)^2*(2*((k:ℤ)+1)+2*(n:ℤ)+1)*(2*((k:ℤ)+1)+2*(n:ℤ)+3))*T n k) := by
  have hkr := T_k_ratio n k hk
  have h1 := T_n1_ratio n k hk
  have h2 := T_n2_ratio n k hk
  linear_combination ((-((((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+2-(k:ℤ))^2*((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+3)*(2*(n:ℤ)+2*(k:ℤ)+4)*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2)))*((-2*((n:ℤ) + 2)*(2*(n:ℤ) + 3)*(7443918144*(n:ℤ)^12 + 89116249248*(n:ℤ)^11 + 477840074580*(n:ℤ)^10 + 1516263919164*(n:ℤ)^9 + 3169124935875*(n:ℤ)^8 + 4594117665555*(n:ℤ)^7 + 4735175091369*(n:ℤ)^6 + 3496319453673*(n:ℤ)^5 + 1835935007068*(n:ℤ)^4 + 668997560020*(n:ℤ)^3 + 160713656664*(n:ℤ)^2 + 22879883456*(n:ℤ) + 1461816416))*((k:ℤ)+1)^3+(-4*(18305621568*(n:ℤ)^13 + 273105304992*(n:ℤ)^12 + 1842407135748*(n:ℤ)^11 + 7437061820052*(n:ℤ)^10 + 20028491704269*(n:ℤ)^9 + 37975813201446*(n:ℤ)^8 + 52123803673807*(n:ℤ)^7 + 52405603615060*(n:ℤ)^6 + 38576280206275*(n:ℤ)^5 + 20526676991678*(n:ℤ)^4 + 7673131778065*(n:ℤ)^3 + 1908366092756*(n:ℤ)^2 + 283149068988*(n:ℤ) + 18942724912))*((k:ℤ)+1)^4+(-2*(21890808576*(n:ℤ)^12 + 339833594880*(n:ℤ)^11 + 2321104646736*(n:ℤ)^10 + 9265255782552*(n:ℤ)^9 + 24140882338866*(n:ℤ)^8 + 43328406576355*(n:ℤ)^7 + 54990507929117*(n:ℤ)^6 + 49762169872427*(n:ℤ)^5 + 31883705838225*(n:ℤ)^4 + 14113298198830*(n:ℤ)^3 + 4099193857060*(n:ℤ)^2 + 701980041656*(n:ℤ) + 53658128736))*((k:ℤ)+1)^5+(4*(5161283712*(n:ℤ)^11 + 43526313792*(n:ℤ)^10 + 129024803448*(n:ℤ)^9 + 62506209504*(n:ℤ)^8 - 610076329415*(n:ℤ)^7 - 1940763038281*(n:ℤ)^6 - 3009256822395*(n:ℤ)^5 - 2842821940351*(n:ℤ)^4 - 1707155168938*(n:ℤ)^3 - 637385936508*(n:ℤ)^2 - 135052337544*(n:ℤ) - 12414205600))*((k:ℤ)+1)^6+(8*(3578661216*(n:ℤ)^10 + 37524719232*(n:ℤ)^9 + 171994706550*(n:ℤ)^8 + 452639126431*(n:ℤ)^7 + 755370436273*(n:ℤ)^6 + 832865889191*(n:ℤ)^5 + 612665563417*(n:ℤ)^4 + 296016335294*(n:ℤ)^3 + 89615097604*(n:ℤ)^2 + 15289391032*(n:ℤ) + 1109552736))*((k:ℤ)+1)^7+(16*(478084464*(n:ℤ)^9 + 4884878232*(n:ℤ)^8 + 21665145987*(n:ℤ)^7 + 54638336225*(n:ℤ)^6 + 86179658227*(n:ℤ)^5 + 87993309183*(n:ℤ)^4 + 58065207134*(n:ℤ)^3 + 23852127404*(n:ℤ)^2 + 5533215480*(n:ℤ) + 552935264))*((k:ℤ)+1)^8)*(((k:ℤ)-(n:ℤ)-2)^2*((k:ℤ)-(n:ℤ)-1)^2*(2*(k:ℤ)+2*(n:ℤ)+1)*(2*(k:ℤ)+2*(n:ℤ)+3))))*hkr + ((((((k:ℤ)+1)^3*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+2-(k:ℤ))^2*((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+3)*(2*(n:ℤ)+2*(k:ℤ)+4)*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2)))*(((k:ℤ)-(n:ℤ)-2)^2*((k:ℤ)-(n:ℤ)-1)^2*(2*(k:ℤ)+2*(n:ℤ)+1)*(2*(k:ℤ)+2*(n:ℤ)+3))*((((k:ℤ)+1)-(n:ℤ)-2)^2*(((k:ℤ)+1)-(n:ℤ)-1)^2*(2*((k:ℤ)+1)+2*(n:ℤ)+1)*(2*((k:ℤ)+1)+2*(n:ℤ)+3))*(-36*(72783360*(n:ℤ)^11+946183680*(n:ℤ)^10+5506947648*(n:ℤ)^9+18919626192*(n:ℤ)^8+42578365230*(n:ℤ)^7+65816429067*(n:ℤ)^6+71201437287*(n:ℤ)^5+53826632241*(n:ℤ)^4+27825371259*(n:ℤ)^3+9355168720*(n:ℤ)^2+1839302884*(n:ℤ)+160171824))))*h1 + ((((((k:ℤ)+1)^3*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2)))*(((k:ℤ)-(n:ℤ)-2)^2*((k:ℤ)-(n:ℤ)-1)^2*(2*(k:ℤ)+2*(n:ℤ)+1)*(2*(k:ℤ)+2*(n:ℤ)+3))*((((k:ℤ)+1)-(n:ℤ)-2)^2*(((k:ℤ)+1)-(n:ℤ)-1)^2*(2*((k:ℤ)+1)+2*(n:ℤ)+1)*(2*((k:ℤ)+1)+2*(n:ℤ)+3))*(16*((n:ℤ)+2)^3*(4*(n:ℤ)+5)^2*(4*(n:ℤ)+7)^2*(5616*(n:ℤ)^4+14040*(n:ℤ)^3+12915*(n:ℤ)^2+5183*(n:ℤ)+770))))*h2


-- ===================== Recurrence section =====================
def P0 (n : ℤ) : ℤ := -27*(n+2)*(3*n+1)^3*(3*n+2)^3*(5616*n^4+36504*n^3+88731*n^2+95597*n+38524)
def P1 (n : ℤ) : ℤ := -36*(72783360*n^11+946183680*n^10+5506947648*n^9+18919626192*n^8+42578365230*n^7+65816429067*n^6+71201437287*n^5+53826632241*n^4+27825371259*n^3+9355168720*n^2+1839302884*n+160171824)
def P2 (n : ℤ) : ℤ := 16*(n+2)^3*(4*n+5)^2*(4*n+7)^2*(5616*n^4+14040*n^3+12915*n^2+5183*n+770)
def Npol (n k : ℤ) : ℤ := (-2*(n + 2)*(2*n + 3)*(7443918144*n^12 + 89116249248*n^11 + 477840074580*n^10 + 1516263919164*n^9 + 3169124935875*n^8 + 4594117665555*n^7 + 4735175091369*n^6 + 3496319453673*n^5 + 1835935007068*n^4 + 668997560020*n^3 + 160713656664*n^2 + 22879883456*n + 1461816416))*k^3+(-4*(18305621568*n^13 + 273105304992*n^12 + 1842407135748*n^11 + 7437061820052*n^10 + 20028491704269*n^9 + 37975813201446*n^8 + 52123803673807*n^7 + 52405603615060*n^6 + 38576280206275*n^5 + 20526676991678*n^4 + 7673131778065*n^3 + 1908366092756*n^2 + 283149068988*n + 18942724912))*k^4+(-2*(21890808576*n^12 + 339833594880*n^11 + 2321104646736*n^10 + 9265255782552*n^9 + 24140882338866*n^8 + 43328406576355*n^7 + 54990507929117*n^6 + 49762169872427*n^5 + 31883705838225*n^4 + 14113298198830*n^3 + 4099193857060*n^2 + 701980041656*n + 53658128736))*k^5+(4*(5161283712*n^11 + 43526313792*n^10 + 129024803448*n^9 + 62506209504*n^8 - 610076329415*n^7 - 1940763038281*n^6 - 3009256822395*n^5 - 2842821940351*n^4 - 1707155168938*n^3 - 637385936508*n^2 - 135052337544*n - 12414205600))*k^6+(8*(3578661216*n^10 + 37524719232*n^9 + 171994706550*n^8 + 452639126431*n^7 + 755370436273*n^6 + 832865889191*n^5 + 612665563417*n^4 + 296016335294*n^3 + 89615097604*n^2 + 15289391032*n + 1109552736))*k^7+(16*(478084464*n^9 + 4884878232*n^8 + 21665145987*n^7 + 54638336225*n^6 + 86179658227*n^5 + 87993309183*n^4 + 58065207134*n^3 + 23852127404*n^2 + 5533215480*n + 552935264))*k^8
def Dpol (n k : ℤ) : ℤ := (k-n-2)^2*(k-n-1)^2*(2*k+2*n+1)*(2*k+2*n+3)
def Fpol (n k : ℕ) : ℤ := P0 n * T n k + P1 n * T (n+1) k + P2 n * T (n+2) k
noncomputable def Gq (n k : ℕ) : ℚ := (Npol n k : ℚ) * (T n k : ℚ) / (Dpol n k : ℚ)

lemma T_vanish (m k : ℕ) (h : m < k) : T m k = 0 := by
  unfold T; rw [Nat.choose_eq_zero_of_lt h]; push_cast; ring

lemma Dpol_ne (n k : ℕ) (hk : k ≤ n) : (Dpol n k : ℚ) ≠ 0 := by
  have hkn : (k:ℤ) ≤ n := by exact_mod_cast hk
  have hz : Dpol n k ≠ 0 := by
    unfold Dpol
    have a1 : ((k:ℤ)-n-2) ≠ 0 := by omega
    have a2 : ((k:ℤ)-n-1) ≠ 0 := by omega
    have a3 : (2*(k:ℤ)+2*n+1) ≠ 0 := by positivity
    have a4 : (2*(k:ℤ)+2*n+3) ≠ 0 := by positivity
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 a1) (pow_ne_zero 2 a2)) a3) a4
  exact_mod_cast hz

lemma Gq_zero (n : ℕ) : Gq n 0 = 0 := by
  have hN : Npol n 0 = 0 := by unfold Npol; ring
  unfold Gq; rw [hN]; simp

set_option maxHeartbeats 8000000 in
lemma CERT2 (n k : ℕ) (hk : k ≤ n) :
    Dpol n k * Dpol n (k+1) * Fpol n k
      = Npol n (k+1) * Dpol n k * T n (k+1) - Npol n k * Dpol n (k+1) * T n k := by
  have hDDD : ((((k:ℤ)+1)^3*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2))*(((n:ℤ)+2-(k:ℤ))^2*((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+3)*(2*(n:ℤ)+2*(k:ℤ)+4)*(2*(n:ℤ)+2*(k:ℤ)+1)*(2*(n:ℤ)+2*(k:ℤ)+2)) : ℤ) ≠ 0 := by
    have hkn : (k:ℤ) ≤ n := by exact_mod_cast hk
    have b1 : ((n:ℤ)+1-k) ≠ 0 := by omega
    have b2 : ((n:ℤ)+2-k) ≠ 0 := by omega
    apply mul_ne_zero
    apply mul_ne_zero
    · positivity
    · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 b1) (by positivity)) (by positivity)
    · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 b2) (pow_ne_zero 2 b1)) (by positivity)) (by positivity)) (by positivity)) (by positivity)
  have hc := mul_left_cancel₀ hDDD (CERT n k hk)
  unfold Fpol Dpol Npol P0 P1 P2
  linear_combination hc

lemma F_eq_dG (n k : ℕ) (hk : k + 1 ≤ n) : Gq n (k+1) - Gq n k = (Fpol n k : ℚ) := by
  have hd1 : (Dpol n k : ℚ) ≠ 0 := Dpol_ne n k (by omega)
  have hd2 : (Dpol n (k+1) : ℚ) ≠ 0 := Dpol_ne n (k+1) (by omega)
  have hcq : (Dpol n k : ℚ) * Dpol n (k+1) * Fpol n k
      = Npol n (k+1) * Dpol n k * T n (k+1) - Npol n k * Dpol n (k+1) * T n k := by
    exact_mod_cast CERT2 n k (by omega)
  rw [Gq, Gq]; push_cast
  rw [div_sub_div _ _ hd2 hd1, div_eq_iff (mul_ne_zero hd2 hd1)]
  linear_combination -hcq

set_option maxHeartbeats 8000000 in
lemma star_int (n : ℕ) :
    Npol n n * T n n + Dpol n n * (Fpol n n + Fpol n (n+1) + Fpol n (n+2)) = 0 := by
  have rela := T_n1_ratio n n (le_refl n)
  have relb := T_n2_ratio n n (le_refl n)
  have relc := T_k_ratio (n+1) n (by omega)
  have reld := T_n1_ratio (n+1) (n+1) (le_refl (n+1))
  have rele := T_k_ratio (n+2) (n+1) (by omega)
  have v1 : T n (n+1) = 0 := T_vanish n (n+1) (by omega)
  have v2 : T n (n+2) = 0 := T_vanish n (n+2) (by omega)
  have v3 : T (n+1) (n+2) = 0 := T_vanish (n+1) (n+2) (by omega)
  have hL : ((4*(n:ℤ)^5 + 24*(n:ℤ)^4 + 55*(n:ℤ)^3 + 60*(n:ℤ)^2 + 31*(n:ℤ) + 6) : ℤ) ≠ 0 := by positivity
  have hLE : ((4*(n:ℤ)^5 + 24*(n:ℤ)^4 + 55*(n:ℤ)^3 + 60*(n:ℤ)^2 + 31*(n:ℤ) + 6) : ℤ) * (Npol n n * T n n + Dpol n n * (Fpol n n + Fpol n (n+1) + Fpol n (n+2))) = 0 := by
    unfold Fpol Npol Dpol P0 P1 P2
    rw [v1, v2, v3]
    linear_combination (-23952015360*(n:ℤ)^16 - 416148295680*(n:ℤ)^15 - 3343652333568*(n:ℤ)^14 - 16491433390592*(n:ℤ)^13 - 55888952116416*(n:ℤ)^12 - 138025813839248*(n:ℤ)^11 - 257043935939936*(n:ℤ)^10 - 368388218249332*(n:ℤ)^9 - 410885778152048*(n:ℤ)^8 - 358127298486904*(n:ℤ)^7 - 243333245560272*(n:ℤ)^6 - 127656384480964*(n:ℤ)^5 - 50739102071392*(n:ℤ)^4 - 14782923784448*(n:ℤ)^3 - 2979232012864*(n:ℤ)^2 - 371162446272*(n:ℤ) - 21532771584)*rela + (11501568*(n:ℤ)^16/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 235782144*(n:ℤ)^15/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 2236188672*(n:ℤ)^14/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 13016952832*(n:ℤ)^13/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 52022667904*(n:ℤ)^12/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 151269338816*(n:ℤ)^11/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 330843195448*(n:ℤ)^10/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 554840886248*(n:ℤ)^9/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 720624997930*(n:ℤ)^8/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 726808202358*(n:ℤ)^7/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 567010881890*(n:ℤ)^6/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 338361603490*(n:ℤ)^5/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 151330086668*(n:ℤ)^4/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 49013960752*(n:ℤ)^3/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 10838226560*(n:ℤ)^2/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 1461572000*(n:ℤ)/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1) + 90552000/(2*(n:ℤ)^2 + 3*(n:ℤ) + 1))*relb + (5750784000*(n:ℤ)^15 + 113290444800*(n:ℤ)^14 + 1000347033600*(n:ℤ)^13 + 5273938399232*(n:ℤ)^12 + 18611562469888*(n:ℤ)^11 + 46632192246016*(n:ℤ)^10 + 85752512984608*(n:ℤ)^9 + 117868899196656*(n:ℤ)^8 + 122071294284920*(n:ℤ)^7 + 95211057192932*(n:ℤ)^6 + 55432998441400*(n:ℤ)^5 + 23638014950196*(n:ℤ)^4 + 7138677321592*(n:ℤ)^3 + 1439364788752*(n:ℤ)^2 + 172916671392*(n:ℤ) + 9302495616)*relc + (368050176*(n:ℤ)^16 + 6900940800*(n:ℤ)^15 + 60654551040*(n:ℤ)^14 + 329961193472*(n:ℤ)^13 + 1236771311616*(n:ℤ)^12 + 3370197142528*(n:ℤ)^11 + 6877930082560*(n:ℤ)^10 + 10687664992448*(n:ℤ)^9 + 12746872275392*(n:ℤ)^8 + 11684565373136*(n:ℤ)^7 + 8192329216992*(n:ℤ)^6 + 4341753208160*(n:ℤ)^5 + 1703262104576*(n:ℤ)^4 + 477609103696*(n:ℤ)^3 + 90161337568*(n:ℤ)^2 + 10219590080*(n:ℤ) + 522614400)*reld + (368050176*(n:ℤ)^13 + 4324589568*(n:ℤ)^12 + 23021420544*(n:ℤ)^11 + 73486254080*(n:ℤ)^10 + 156860796928*(n:ℤ)^9 + 236314532864*(n:ℤ)^8 + 258346536192*(n:ℤ)^7 + 207366628800*(n:ℤ)^6 + 122106535296*(n:ℤ)^5 + 52044754768*(n:ℤ)^4 + 15587926064*(n:ℤ)^3 + 3101887120*(n:ℤ)^2 + 366786000*(n:ℤ) + 19404000)*rele
  rcases mul_eq_zero.mp hLE with h | h
  · exact absurd h hL
  · exact h

lemma star (n : ℕ) :
    Gq n n + (Fpol n n : ℚ) + (Fpol n (n+1) : ℚ) + (Fpol n (n+2) : ℚ) = 0 := by
  have hd : (Dpol n n : ℚ) ≠ 0 := Dpol_ne n n (le_refl n)
  have hs : (Npol n n : ℚ) * T n n + Dpol n n * (Fpol n n + Fpol n (n+1) + Fpol n (n+2)) = 0 := by
    exact_mod_cast star_int n
  rw [Gq]
  field_simp
  linear_combination hs

lemma tele (n : ℕ) : (∑ k ∈ range n, (Fpol n k : ℚ)) = Gq n n := by
  have h : ∑ k ∈ range n, (Fpol n k : ℚ) = ∑ k ∈ range n, (Gq n (k+1) - Gq n k) := by
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_range] at hk
    exact (F_eq_dG n k (by omega)).symm
  rw [h, Finset.sum_range_sub (fun k => Gq n k) n, Gq_zero]; ring

lemma ha (n : ℕ) : ∑ k ∈ range (n+3), (T n k : ℚ) = (aSeq n : ℚ) := by
  unfold aSeq; push_cast
  rw [show n+3 = (n+1)+1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show ((T n (n+1) : ℤ) : ℚ) = 0 by rw [T_vanish n (n+1) (by omega)]; norm_num,
      show ((T n ((n+1)+1) : ℤ) : ℚ) = 0 by rw [T_vanish n ((n+1)+1) (by omega)]; norm_num]
  ring

lemma ha1 (n : ℕ) : ∑ k ∈ range (n+3), (T (n+1) k : ℚ) = (aSeq (n+1) : ℚ) := by
  unfold aSeq; push_cast
  rw [show n+3 = (n+1+1)+1 from rfl, Finset.sum_range_succ]
  rw [show ((T (n+1) (n+1+1) : ℤ) : ℚ) = 0 by rw [T_vanish (n+1) (n+1+1) (by omega)]; norm_num]
  ring

lemma ha2 (n : ℕ) : ∑ k ∈ range (n+3), (T (n+2) k : ℚ) = (aSeq (n+2) : ℚ) := by
  unfold aSeq; push_cast; rw [show n+3 = n+2+1 from rfl]

theorem aSeq_rec (n : ℕ) :
    P0 n * aSeq n + P1 n * aSeq (n+1) + P2 n * aSeq (n+2) = 0 := by
  have key : (∑ k ∈ range (n+3), (Fpol n k : ℚ)) = 0 := by
    rw [show n+3 = n+1+1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, tele]
    linear_combination star n
  have expand : (∑ k ∈ range (n+3), (Fpol n k : ℚ))
      = (P0 n : ℚ) * aSeq n + (P1 n : ℚ) * aSeq (n+1) + (P2 n : ℚ) * aSeq (n+2) := by
    have hfp : ∀ k, (Fpol n k : ℚ) = (P0 n : ℚ) * (T n k : ℚ) + (P1 n : ℚ) * (T (n+1) k : ℚ)
        + (P2 n : ℚ) * (T (n+2) k : ℚ) := by intro k; unfold Fpol; push_cast; ring
    rw [Finset.sum_congr rfl (fun k _ => hfp k), Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ha n, ha1 n, ha2 n]
  rw [← @Int.cast_inj ℚ]; push_cast; rw [← expand, key]

end A374605

