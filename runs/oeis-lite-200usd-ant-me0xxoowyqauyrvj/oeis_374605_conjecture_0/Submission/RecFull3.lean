import FormalConjectures.Util.ProblemImports

open Finset

set_option maxRecDepth 100000

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
  unfold Gq
  norm_num [Npol]


-- ===== Auxiliary multiplier polynomials =====
def Mp (n k : ℤ) : ℤ := (k+1)^3*(n+2-k)^2*(n+1-k)^2*(2*n+2*k+3)*(2*n+2*k+4)*(2*n+2*k+1)*(2*n+2*k+2)
def MB1 (n k : ℤ) : ℤ := ((k+1)^3*(n+2-k)^2*(2*n+2*k+3)*(2*n+2*k+4))*((n+1+k)*(3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3))
def MB2 (n k : ℤ) : ℤ := ((k+1)^3)*((n+2+k)*(n+1+k)*(3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3)*(3*n+2*k+4)*(3*n+2*k+5)*(3*n+2*k+6))
def MBk (n k : ℤ) : ℤ := ((n+2-k)^2*(n+1-k)^2*(2*n+2*k+3)*(2*n+2*k+4))*((n-k)^2*(n+k+1)*(3*n+2*k+1)*(3*n+2*k+2))

lemma sub1 (n k : ℕ) (hk : k ≤ n) : Mp n k * T (n+1) k = MB1 n k * T n k := by
  have h1 := T_n1_ratio n k hk
  unfold Mp MB1; push_cast
  linear_combination (((k:ℤ)+1)^3*((n:ℤ)+2-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+3)*(2*(n:ℤ)+2*(k:ℤ)+4)) * h1

lemma sub2 (n k : ℕ) (hk : k ≤ n) : Mp n k * T (n+2) k = MB2 n k * T n k := by
  have h2 := T_n2_ratio n k hk
  unfold Mp MB2; push_cast
  linear_combination (((k:ℤ)+1)^3) * h2

lemma subk (n k : ℕ) (hk : k ≤ n) : Mp n k * T n (k+1) = MBk n k * T n k := by
  have hkr := T_k_ratio n k hk
  unfold Mp MBk; push_cast
  linear_combination (((n:ℤ)+2-(k:ℤ))^2*((n:ℤ)+1-(k:ℤ))^2*(2*(n:ℤ)+2*(k:ℤ)+3)*(2*(n:ℤ)+2*(k:ℤ)+4)) * hkr

lemma factL (n k : ℕ) (hk : k ≤ n) :
    Mp n k * (Dpol n k * Dpol n (k+1) * Fpol n k)
      = (Dpol n k * Dpol n (k+1) * (P0 n * Mp n k + P1 n * MB1 n k + P2 n * MB2 n k)) * T n k := by
  have e1 := sub1 n k hk
  have e2 := sub2 n k hk
  unfold Fpol
  linear_combination (Dpol n k * Dpol n (k+1) * P1 n) * e1 + (Dpol n k * Dpol n (k+1) * P2 n) * e2

lemma factR (n k : ℕ) (hk : k ≤ n) :
    Mp n k * (Npol n (k+1) * Dpol n k * T n (k+1) - Npol n k * Dpol n (k+1) * T n k)
      = (Npol n (k+1) * Dpol n k * MBk n k - Npol n k * Dpol n (k+1) * Mp n k) * T n k := by
  have ek := subk n k hk
  linear_combination (Npol n (k+1) * Dpol n k) * ek

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma POLYIDfull (n k : ℕ) :
    Dpol n k * Dpol n (k+1) * (P0 n * Mp n k + P1 n * MB1 n k + P2 n * MB2 n k)
      = Npol n (k+1) * Dpol n k * MBk n k - Npol n k * Dpol n (k+1) * Mp n k := by
  unfold Dpol P0 P1 P2 Npol Mp MB1 MB2 MBk
  push_cast
  ring

lemma Mp_ne (n k : ℕ) (hk : k ≤ n) : Mp n k ≠ 0 := by
  have hkn : (k:ℤ) ≤ n := by exact_mod_cast hk
  unfold Mp
  have a1 : ((k:ℤ)+1) ≠ 0 := by positivity
  have a2 : ((n:ℤ)+2-(k:ℤ)) ≠ 0 := by omega
  have a3 : ((n:ℤ)+1-(k:ℤ)) ≠ 0 := by omega
  have a4 : (2*(n:ℤ)+2*(k:ℤ)+3) ≠ 0 := by positivity
  have a5 : (2*(n:ℤ)+2*(k:ℤ)+4) ≠ 0 := by positivity
  have a6 : (2*(n:ℤ)+2*(k:ℤ)+1) ≠ 0 := by positivity
  have a7 : (2*(n:ℤ)+2*(k:ℤ)+2) ≠ 0 := by positivity
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 a1) (pow_ne_zero 2 a2)) (pow_ne_zero 2 a3)) a4) a5) a6) a7

lemma CERT2 (n k : ℕ) (hk : k ≤ n) :
    Dpol n k * Dpol n (k+1) * Fpol n k
      = Npol n (k+1) * Dpol n k * T n (k+1) - Npol n k * Dpol n (k+1) * T n k := by
  have key : Mp n k * (Dpol n k * Dpol n (k+1) * Fpol n k)
      = Mp n k * (Npol n (k+1) * Dpol n k * T n (k+1) - Npol n k * Dpol n (k+1) * T n k) := by
    rw [factL n k hk, factR n k hk, POLYIDfull n k]
  exact mul_left_cancel₀ (Mp_ne n k hk) key

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
  have hMS : (64*((n:ℤ)+1)^4*((n:ℤ)+2)^4*(2*(n:ℤ)+1)*(2*(n:ℤ)+3)*(4*(n:ℤ)+1)*(4*(n:ℤ)+3)*(4*(n:ℤ)+5)*(4*(n:ℤ)+7)) ≠ 0 := by positivity
  have key : (64*((n:ℤ)+1)^4*((n:ℤ)+2)^4*(2*(n:ℤ)+1)*(2*(n:ℤ)+3)*(4*(n:ℤ)+1)*(4*(n:ℤ)+3)*(4*(n:ℤ)+5)*(4*(n:ℤ)+7)) * (Npol n n * T n n + Dpol n n * (Fpol n n + Fpol n (n+1) + Fpol n (n+2))) = 0 := by
    push_cast at relc reld rele
    unfold Fpol Npol Dpol P0 P1 P2
    rw [v1, v2, v3]
    linear_combination ((((((((((((((((((((((((((((0:ℤ)*(n:ℤ)+(-392429819658240))*(n:ℤ)+(-11527331512320000))*(n:ℤ)+(-161078293951414272))*(n:ℤ)+(-1424977005098565632))*(n:ℤ)+(-8960088468300496896))*(n:ℤ)+(-42621121603799875584))*(n:ℤ)+(-159381127927001513984))*(n:ℤ)+(-480672423929767460864))*(n:ℤ)+(-1190065899048451485696))*(n:ℤ)+(-2449425897133169468416))*(n:ℤ)+(-4228536105321935644672))*(n:ℤ)+(-6160140340224460409088))*(n:ℤ)+(-7601834969744074462208))*(n:ℤ)+(-7960960444212233579264))*(n:ℤ)+(-7074902218269687651840))*(n:ℤ)+(-5325560896562572552960))*(n:ℤ)+(-3382288153770855030784))*(n:ℤ)+(-1801179635896719921408))*(n:ℤ)+(-796997624488940338688))*(n:ℤ)+(-289280728423115463680))*(n:ℤ)+(-84576193777801181184))*(n:ℤ)+(-19403393079832383488))*(n:ℤ)+(-3358544679842258944))*(n:ℤ)+(-411619960443518976))*(n:ℤ)+(-31766743864737792))*(n:ℤ)+(-1157601800355840)))*rela + ((((((((((((((((((((((((((0:ℤ)*(n:ℤ)+(94220845056))*(n:ℤ)+(2920846196736))*(n:ℤ)+(42945830977536))*(n:ℤ)+(398374096338944))*(n:ℤ)+(2616043237277696))*(n:ℤ)+(12935271125352448))*(n:ℤ)+(50009168643227648))*(n:ℤ)+(154950153477750784))*(n:ℤ)+(391267691812302848))*(n:ℤ)+(814412832949645312))*(n:ℤ)+(1407860458723534592))*(n:ℤ)+(2030211146831272576))*(n:ℤ)+(2446673196555414272))*(n:ℤ)+(2462642877822189568))*(n:ℤ)+(2063963455784887808))*(n:ℤ)+(1432232754202940800))*(n:ℤ)+(815673374045462528))*(n:ℤ)+(376411756432807936))*(n:ℤ)+(138209325776470016))*(n:ℤ)+(39327999127146496))*(n:ℤ)+(8336523449139200))*(n:ℤ)+(1234970528153600))*(n:ℤ)+(113647435776000))*(n:ℤ)+(4868075520000)))*relb + (((((((((((((((((((((((((((0:ℤ)*(n:ℤ)+(94220845056000))*(n:ℤ)+(2986800788275200))*(n:ℤ)+(44540518780108800))*(n:ℤ)+(416174913238335488))*(n:ℤ)+(2736936835505717248))*(n:ℤ)+(13486982512416653312))*(n:ℤ)+(51754230807864016896))*(n:ℤ)+(158638331390259101696))*(n:ℤ)+(395263139822516273152))*(n:ℤ)+(810299407387314339840))*(n:ℤ)+(1378082964574196893696))*(n:ℤ)+(1954640315193634651136))*(n:ℤ)+(2318629849155238196736))*(n:ℤ)+(2301524682010678377728))*(n:ℤ)+(1908694856311313468416))*(n:ℤ)+(1317482307783231668736))*(n:ℤ)+(752157939272883581440))*(n:ℤ)+(351880656794123346176))*(n:ℤ)+(133134272184622519296))*(n:ℤ)+(39990252719992042496))*(n:ℤ)+(9287115897254539264))*(n:ℤ)+(1602851429902495744))*(n:ℤ)+(192908656163536896))*(n:ℤ)+(14399423768936448))*(n:ℤ)+(500102164316160)))*relc + ((((((((((((((((((((((((((((0:ℤ)*(n:ℤ)+(6030134083584))*(n:ℤ)+(185426623070208))*(n:ℤ)+(2726673946509312))*(n:ℤ)+(25491721555017728))*(n:ℤ)+(169928867224485888))*(n:ℤ)+(858653358288797696))*(n:ℤ)+(3413867657684844544))*(n:ℤ)+(10943842364617129984))*(n:ℤ)+(28762847909302239232))*(n:ℤ)+(62698125410536849408))*(n:ℤ)+(114257252071330299904))*(n:ℤ)+(174972838458397437952))*(n:ℤ)+(225837981027854430208))*(n:ℤ)+(245924112382983734272))*(n:ℤ)+(225751940252018599936))*(n:ℤ)+(174236946408158620672))*(n:ℤ)+(112542531420359028736))*(n:ℤ)+(60415625432090364928))*(n:ℤ)+(26692484749158246400))*(n:ℤ)+(9575442317395846144))*(n:ℤ)+(2737156478057009152))*(n:ℤ)+(607040240875532288))*(n:ℤ)+(100386943514312704))*(n:ℤ)+(11614578915000320))*(n:ℤ)+(836115603456000))*(n:ℤ)+(28095750144000)))*reld + (((((((((((((((((((((((((0:ℤ)*(n:ℤ)+(6030134083584))*(n:ℤ)+(143215684485120))*(n:ℤ)+(1603561473441792))*(n:ℤ)+(11257754333216768))*(n:ℤ)+(55595075526197248))*(n:ℤ)+(205370886985875456))*(n:ℤ)+(589133302225436672))*(n:ℤ)+(1344770145135886336))*(n:ℤ)+(2482817662358126592))*(n:ℤ)+(3748375478990077952))*(n:ℤ)+(4659456744065155072))*(n:ℤ)+(4786407534543335424))*(n:ℤ)+(4066529157071937536))*(n:ℤ)+(2852042431506408448))*(n:ℤ)+(1643411016904707072))*(n:ℤ)+(771820042102863872))*(n:ℤ)+(291889230957475840))*(n:ℤ)+(87339584394753024))*(n:ℤ)+(20152551001275392))*(n:ℤ)+(3449021602201600))*(n:ℤ)+(411084007219200))*(n:ℤ)+(30363604992000))*(n:ℤ)+(1043159040000)))*rele
  exact (mul_eq_zero.mp key).resolve_left hMS

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


namespace A374605

def Q0val (n : ℤ) : ℤ := 5616*n^4+36504*n^3+88731*n^2+95597*n+38524
def Udes (n : ℤ) : ℤ := -27*(n+2)*(3*n+1)^3*(3*n+2)^3
def Bqdes (n : ℤ) : ℤ := (((((((((((((((((((-1222933730623488:ℤ)*n+(-37299478784016384))*n+(-531088957699928064))*n+(-4688296177944526848))*n+(-28738771884172373760))*n+(-129829270546345468032))*n+(-447679480821047289936))*n+(-1203976537547014049616))*n+(-2558216443492678176432))*n+(-4323305000482460676720))*n+(-5819807344005236621808))*n+(-6219800016923461419504))*n+(-5232874713583069028304))*n+(-3415026350120493723408))*n+(-1688778623662239504960))*n+(-609876744541947479232))*n+(-151280799698780591616))*n+(-22975514059488915456))*n+(-1606541932977426432))
def Cqdes (n : ℤ) : ℤ := (((((((((((((((((((-10732343132160:ℤ)*n+(-343434980229120))*n+(-5119726697054208))*n+(-47218562061041664))*n+(-301759455681773568))*n+(-1418197295976136704))*n+(-5076703301675802624))*n+(-14143865064847469568))*n+(-31068197774784634752))*n+(-54166023763453182528))*n+(-75070219065903795456))*n+(-82435161668259010752))*n+(-71120797517905944192))*n+(-47503837762289733312))*n+(-23997151771949182464))*n+(-8836347312364919616))*n+(-2230848878409923328))*n+(-344227552843527936))*n+(-24414214619317248))

lemma Q0val_ne (n : ℕ) : Q0val (n:ℤ) ≠ 0 := by
  have hn : (0:ℤ) ≤ (n:ℤ) := Int.natCast_nonneg n
  unfold Q0val
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem aSeq_desing (n : ℕ) :
    Udes (n:ℤ) * P0 ((n:ℤ)+1) * aSeq n + Bqdes (n:ℤ) * aSeq (n+2) - Cqdes (n:ℤ) * aSeq (n+3) = 0 := by
  have hbig : Q0val (n:ℤ) * (Udes (n:ℤ) * P0 ((n:ℤ)+1) * aSeq n + Bqdes (n:ℤ) * aSeq (n+2) - Cqdes (n:ℤ) * aSeq (n+3))
      = P0 ((n:ℤ)+1) * (P0 (n:ℤ) * aSeq n + P1 (n:ℤ) * aSeq (n+1) + P2 (n:ℤ) * aSeq (n+2))
        - P1 (n:ℤ) * (P0 ((n:ℤ)+1) * aSeq (n+1) + P1 ((n:ℤ)+1) * aSeq (n+2) + P2 ((n:ℤ)+1) * aSeq (n+3)) := by
    unfold Q0val Udes Bqdes Cqdes P0 P1 P2
    ring
  have h1 := aSeq_rec n
  have h2 := aSeq_rec (n+1)
  rw [show ((n:ℤ)+1) = ((n+1:ℕ):ℤ) from by push_cast; ring] at hbig
  rw [h1, h2, mul_zero, mul_zero, sub_zero] at hbig
  exact (mul_eq_zero.mp hbig).resolve_left (Q0val_ne n)

end A374605
