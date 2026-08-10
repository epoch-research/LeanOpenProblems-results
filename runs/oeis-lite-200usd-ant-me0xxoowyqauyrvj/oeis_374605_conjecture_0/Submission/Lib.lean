import FormalConjectures.Util.ProblemImports

open Finset

set_option maxRecDepth 100000

namespace Rec374605

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

end Rec374605


namespace Rec374605

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

end Rec374605

-- ===== full S1 (own A374605 defs) =====

open Finset

variable {p : ℕ}

theorem p_mul_of_castHom_zero (hp : Nat.Prime p) (x : ZMod (p^2))
    (h : (ZMod.castHom (⟨p, by ring⟩ : p ∣ p^2) (ZMod p)) x = 0) :
    (p : ZMod (p^2)) * x = 0 := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hxval : ((x.val : ℕ) : ZMod (p^2)) = x := ZMod.natCast_zmod_val x
  have h2 : ((x.val : ℕ) : ZMod p) = 0 := by
    have := h; rw [← hxval, map_natCast] at this; exact this
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨m, hm⟩ := h2
  rw [← hxval, hm]; push_cast
  rw [show (p:ZMod (p^2)) * ((p:ZMod (p^2)) * (m:ZMod (p^2))) = ((p^2 : ℕ) : ZMod (p^2)) * (m:ZMod (p^2)) by push_cast; ring, ZMod.natCast_self, zero_mul]

-- general: if x : ZMod (p^3) reduces to 0 mod p^k (k ≤ 3) then p^k ∣ x
theorem pow_dvd_of_castHom_zero (hp : Nat.Prime p) {k : ℕ} (hk : k ≤ 3) (x : ZMod (p^3))
    (h : (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p^k))) x = 0) :
    (p^k : ZMod (p^3)) ∣ x := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hxval : ((x.val : ℕ) : ZMod (p^3)) = x := ZMod.natCast_zmod_val x
  have h2 : ((x.val : ℕ) : ZMod (p^k)) = 0 := by
    have := h; rw [← hxval, map_natCast] at this; exact this
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨m, hm⟩ := h2
  refine ⟨(m : ZMod (p^3)), ?_⟩
  rw [← hxval, hm]; push_cast; ring

-- ring hom preserves inverse of coprime element
theorem castHom_inv {a b : ℕ} (hp : Nat.Prime p) (hab : p^b ∣ p^a) (hba : b ≤ a) (i : ℕ)
    (hcop : ¬ p ∣ i) :
    (ZMod.castHom hab (ZMod (p^b))) ((i:ZMod (p^a))⁻¹) = ((i:ZMod (p^b)))⁻¹ := by
  have hca : Nat.Coprime i (p^a) := Nat.Coprime.pow_right a ((hp.coprime_iff_not_dvd.mpr hcop).symm)
  have hcb : Nat.Coprime i (p^b) := Nat.Coprime.pow_right b ((hp.coprime_iff_not_dvd.mpr hcop).symm)
  have hua : IsUnit ((i:ℕ):ZMod (p^a)) := (ZMod.isUnit_iff_coprime i (p^a)).mpr hca
  have hub : IsUnit ((i:ℕ):ZMod (p^b)) := (ZMod.isUnit_iff_coprime i (p^b)).mpr hcb
  set φ := ZMod.castHom hab (ZMod (p^b))
  have h1 : φ ((i:ZMod (p^a))⁻¹) * ((i:ℕ):ZMod (p^b)) = 1 := by
    have : φ ((i:ZMod (p^a))⁻¹) * φ ((i:ℕ):ZMod (p^a)) = 1 := by
      rw [← map_mul, ZMod.inv_mul_of_unit _ hua, map_one]
    rwa [map_natCast] at this
  have h2 : ((i:ℕ):ZMod (p^b)) * ((i:ℕ):ZMod (p^b))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hub
  calc φ ((i:ZMod (p^a))⁻¹) = φ ((i:ZMod (p^a))⁻¹) * (((i:ℕ):ZMod (p^b)) * ((i:ℕ):ZMod (p^b))⁻¹) := by rw [h2, mul_one]
    _ = (φ ((i:ZMod (p^a))⁻¹) * ((i:ℕ):ZMod (p^b))) * ((i:ℕ):ZMod (p^b))⁻¹ := by ring
    _ = ((i:ℕ):ZMod (p^b))⁻¹ := by rw [h1, one_mul]

theorem sum_range_eq_univ [NeZero p] (f : ZMod p → ZMod p) :
    ∑ i ∈ Finset.range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_bij' (fun a _ => (a : ZMod p)) (fun x _ => x.val)
    (fun a _ => Finset.mem_univ _) (fun x _ => ?_) (fun a ha => ?_)
    (fun x _ => ZMod.natCast_zmod_val x) (fun a _ => rfl)
  · rw [Finset.mem_range]; exact ZMod.val_lt x
  · rw [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha

theorem sum_inv_sq_field [Fact (Nat.Prime p)] (hp3 : 3 < p) :
    ∑ x : ZMod p, (x⁻¹)^2 = 0 := by
  let e : ZMod p ≃ ZMod p := ⟨Inv.inv, Inv.inv, inv_inv, inv_inv⟩
  have h1 : ∑ x : ZMod p, (e x)^2 = ∑ x : ZMod p, x^2 := Equiv.sum_comp e (·^2)
  have h2 : ∑ x : ZMod p, x ^ 2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 2 (by rw [ZMod.card]; omega)
  have h3 : ∑ x : ZMod p, (e x)^2 = ∑ x : ZMod p, (x⁻¹)^2 := rfl
  rw [← h3, h1, h2]

theorem sum_inv_sq_range [Fact (Nat.Prime p)] (hp3 : 3 < p) :
    ∑ i ∈ Finset.range p, ((i : ZMod p)⁻¹)^2 = 0 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  rw [sum_range_eq_univ (fun x => (x⁻¹)^2)]
  exact sum_inv_sq_field hp3

theorem sum_inv_sq_Icc [Fact (Nat.Prime p)] (hp3 : 3 < p) :
    ∑ i ∈ Finset.Icc 1 (p-1), ((i : ZMod p)⁻¹)^2 = 0 := by
  have hp := Fact.out (p := Nat.Prime p)
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rw [← sum_inv_sq_range hp3]
  have hset : Finset.Icc 1 (p-1) = (Finset.range p).erase 0 := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
  rw [hset, Finset.sum_erase _ (by simp)]

-- coprimality helper
theorem coprime_of_mem_Icc (hp : Nat.Prime p) {i : ℕ} (hi : i ∈ Finset.Icc 1 (p-1)) :
    Nat.Coprime i (p^2) := by
  rw [Finset.mem_Icc] at hi
  have hip : i < p := by omega
  have : ¬ p ∣ i := by
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  exact (Nat.Coprime.pow_right 2 ((hp.coprime_iff_not_dvd.mpr this).symm))

theorem isUnit_p2 (hp : Nat.Prime p) {i : ℕ} (hi : i ∈ Finset.Icc 1 (p-1)) :
    IsUnit ((i : ℕ) : ZMod (p^2)) :=
  (ZMod.isUnit_iff_coprime i (p^2)).mpr (coprime_of_mem_Icc hp hi)

-- reindex by i ↦ p - i on Icc 1 (p-1)
theorem sum_reflect {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 (p-1), g (p - i) = ∑ i ∈ Finset.Icc 1 (p-1), g i := by
  refine Finset.sum_nbij' (fun i => p - i) (fun i => p - i) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; rfl

-- Wolstenholme's theorem mod p^2
theorem wolstenholme (hp : Nat.Prime p) (hp3 : 3 < p) :
    ∑ i ∈ Finset.Icc 1 (p-1), ((i : ℕ) : ZMod (p^2))⁻¹ = 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  set R := ZMod (p^2)
  set H := ∑ i ∈ Finset.Icc 1 (p-1), ((i : ℕ) : R)⁻¹ with hH
  -- pairing identity
  have hpair : ∀ i ∈ Finset.Icc 1 (p-1),
      ((i : ℕ) : R)⁻¹ + ((p - i : ℕ) : R)⁻¹ = (p : R) * (((i:ℕ):R)⁻¹ * ((p-i:ℕ):R)⁻¹) := by
    intro i hi
    have hmem := hi
    rw [Finset.mem_Icc] at hi
    have hu : ((i:ℕ):R) * ((i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_p2 hp hmem)
    have hvmem : (p - i) ∈ Finset.Icc 1 (p-1) := by rw [Finset.mem_Icc]; omega
    have hv : ((p-i:ℕ):R) * ((p-i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_p2 hp hvmem)
    have hsum : ((i:ℕ):R) + ((p-i:ℕ):R) = (p : R) := by
      rw [← Nat.cast_add]; congr 1; omega
    set a := ((i:ℕ):R); set b := ((p-i:ℕ):R)
    have key : a⁻¹ + b⁻¹ = (a + b) * (a⁻¹ * b⁻¹) := by
      calc a⁻¹ + b⁻¹ = (b * b⁻¹) * a⁻¹ + (a * a⁻¹) * b⁻¹ := by rw [hu, hv]; ring
        _ = (a + b) * (a⁻¹ * b⁻¹) := by ring
    rw [key, hsum]
  -- T and the 2H = p T identity
  set T := ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):R)⁻¹ * ((p-i:ℕ):R)⁻¹) with hT
  have hrefl : ∑ i ∈ Finset.Icc 1 (p-1), ((p - i : ℕ) : R)⁻¹ = H :=
    sum_reflect (fun j => ((j:ℕ):R)⁻¹)
  have h2H : H + H = (p : R) * T := by
    have e1 : ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):R)⁻¹ + ((p-i:ℕ):R)⁻¹)
        = (p : R) * T := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hpair
    rw [Finset.sum_add_distrib, hrefl, ← hH] at e1
    exact e1
  -- castHom T = 0
  set φ := ZMod.castHom (⟨p, by ring⟩ : p ∣ p^2) (ZMod p) with hφ
  have hφT : φ T = 0 := by
    rw [hT, map_sum]
    rw [show (0 : ZMod p) = ∑ i ∈ Finset.Icc 1 (p-1), -(((i:ℕ):ZMod p)⁻¹)^2 by
      rw [Finset.sum_neg_distrib, sum_inv_sq_Icc hp3, neg_zero]]
    apply Finset.sum_congr rfl
    intro i hi
    have hmem := hi
    rw [Finset.mem_Icc] at hi
    have hu : ((i:ℕ):R) * ((i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_p2 hp hmem)
    have hvmem : (p - i) ∈ Finset.Icc 1 (p-1) := by rw [Finset.mem_Icc]; omega
    have hv : ((p-i:ℕ):R) * ((p-i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_p2 hp hvmem)
    have hφa : φ (((i:ℕ):R)⁻¹) = ((i:ℕ):ZMod p)⁻¹ := by
      have : φ ((i:ℕ):R) * φ (((i:ℕ):R)⁻¹) = 1 := by rw [← map_mul, hu, map_one]
      rw [map_natCast] at this
      exact eq_inv_of_mul_eq_one_right this
    have hφb : φ (((p-i:ℕ):R)⁻¹) = ((p-i:ℕ):ZMod p)⁻¹ := by
      have : φ ((p-i:ℕ):R) * φ (((p-i:ℕ):R)⁻¹) = 1 := by rw [← map_mul, hv, map_one]
      rw [map_natCast] at this
      exact eq_inv_of_mul_eq_one_right this
    have hcast : ((p-i:ℕ):ZMod p) = -((i:ℕ):ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [map_mul, hφa, hφb, hcast, inv_neg]
    ring
  have hpT : (p : R) * T = 0 := p_mul_of_castHom_zero hp T hφT
  have h2H0 : H + H = 0 := by rw [h2H, hpT]
  -- 2 is a unit in R
  have h2unit : IsUnit (2 : R) := by
    have : ((2:ℕ):R) = (2:R) := by norm_num
    rw [← this]
    refine (ZMod.isUnit_iff_coprime 2 (p^2)).mpr ?_
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    exact Nat.Coprime.pow_right 2 this
  have : (2 : R) * H = 0 := by rw [two_mul]; exact h2H0
  exact (h2unit.mul_right_eq_zero).mp this

-- Truncated product expansion: if all uᵢ divisible by b and b³=0, the product of (1+uᵢ)
-- equals 1 + ∑u + e₂, with e₂ = ((∑u)²-∑u²)/2.
theorem prod_one_add_truncate (b : ZMod (p^3)) (hb3 : b^3 = 0)
    (u : ℕ → ZMod (p^3)) (inv2 : ZMod (p^3)) (hinv2 : (2:ZMod (p^3)) * inv2 = 1)
    (s : Finset ℕ) (hu : ∀ i ∈ s, b ∣ u i) :
    ∏ i ∈ s, (1 + u i)
      = 1 + (∑ i ∈ s, u i) + ((∑ i ∈ s, u i)^2 - ∑ i ∈ s, (u i)^2) * inv2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert x t hx ih =>
    have hut : ∀ i ∈ t, b ∣ u i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hbx : b ∣ u x := hu x (Finset.mem_insert_self x t)
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.sum_insert hx, ih hut]
    -- b² ∣ E2(t)
    have hbSum : b ∣ ∑ i ∈ t, u i := Finset.dvd_sum hut
    have hbQ : b^2 ∣ ∑ i ∈ t, (u i)^2 := by
      apply Finset.dvd_sum; intro i hi; obtain ⟨v, hv⟩ := hut i hi; exact ⟨v^2, by rw [hv]; ring⟩
    have hbSum2 : b^2 ∣ (∑ i ∈ t, u i)^2 := by obtain ⟨w, hw⟩ := hbSum; exact ⟨w^2, by rw [hw]; ring⟩
    have hbE2 : b^2 ∣ ((∑ i ∈ t, u i)^2 - ∑ i ∈ t, (u i)^2) * inv2 := by
      exact Dvd.dvd.mul_right (dvd_sub hbSum2 hbQ) inv2
    have hkill : u x * (((∑ i ∈ t, u i)^2 - ∑ i ∈ t, (u i)^2) * inv2) = 0 := by
      obtain ⟨vx, hvx⟩ := hbx; obtain ⟨w2, hw2⟩ := hbE2
      rw [hvx, hw2]; rw [show b * vx * (b^2 * w2) = b^3 * (vx * w2) by ring, hb3, zero_mul]
    linear_combination (-(u x * ∑ i ∈ t, u i)) * hinv2 + hkill

theorem H1div (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (p^2 : ZMod (p^3)) ∣ ∑ i ∈ Finset.Icc 1 (p-1), ((i:ℕ):ZMod (p^3))⁻¹ := by
  have hp3 : 3 < p := by omega
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  apply pow_dvd_of_castHom_zero hp (show (2:ℕ) ≤ 3 by norm_num)
  rw [map_sum, show (0:ZMod (p^2)) = ∑ i ∈ Finset.Icc 1 (p-1), ((i:ℕ):ZMod (p^2))⁻¹ from
    (wolstenholme hp hp3).symm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact castHom_inv hp (pow_dvd_pow p (show (2:ℕ)≤3 by norm_num)) (show (2:ℕ)≤3 by norm_num) i
    (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)

theorem H2div (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (p : ZMod (p^3)) ∣ ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):ZMod (p^3))⁻¹)^2 := by
  have hp3 : 3 < p := by omega
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have : (p:ZMod (p^3)) = (p^1 : ZMod (p^3)) := by ring
  rw [this]
  apply pow_dvd_of_castHom_zero hp (show (1:ℕ) ≤ 3 by norm_num)
  rw [map_sum, show (0:ZMod (p^1)) = ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):ZMod (p^1))⁻¹)^2 from by
    rw [pow_one]; exact (sum_inv_sq_Icc hp3).symm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [map_pow]
  congr 1
  exact castHom_inv hp (pow_dvd_pow p (show (1:ℕ)≤3 by norm_num)) (show (1:ℕ)≤3 by norm_num) i
    (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)

theorem prod_Icc_cast (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, ((i:ℕ):ZMod (p^3)) = ((Nat.factorial n : ℕ) : ZMod (p^3)) := by
  have h : Finset.Icc 1 n = Finset.Ico 1 (n+1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [← Nat.cast_prod, h, Finset.prod_Ico_id_eq_factorial]

theorem full_block (hp : Nat.Prime p) (hp5 : 5 ≤ p) (j : ℕ) :
    ∏ i ∈ Finset.Icc 1 (p-1), ((j*p+i : ℕ) : ZMod (p^3)) = ((Nat.factorial (p-1) : ℕ) : ZMod (p^3)) := by
  have hp3 : 3 < p := by omega
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  set b : ZMod (p^3) := ((j*p : ℕ) : ZMod (p^3)) with hb
  have hb3 : b^3 = 0 := by
    rw [hb, ← Nat.cast_pow, show (j*p)^3 = (j^3) * p^3 by ring, Nat.cast_mul, Nat.cast_pow,
      ZMod.natCast_self, mul_zero]
  -- 2 is a unit
  have h2u : IsUnit ((2:ℕ):ZMod (p^3)) :=
    (ZMod.isUnit_iff_coprime 2 (p^3)).mpr (Nat.Coprime.pow_right 3 ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)))
  set inv2 : ZMod (p^3) := ((2:ℕ):ZMod (p^3))⁻¹ with hinv2def
  have hinv2 : (2:ZMod (p^3)) * inv2 = 1 := by
    rw [show (2:ZMod (p^3)) = ((2:ℕ):ZMod (p^3)) by norm_num]
    exact ZMod.mul_inv_of_unit _ h2u
  -- u i and divisibility
  set u : ℕ → ZMod (p^3) := fun i => b * ((i:ℕ):ZMod (p^3))⁻¹ with hu
  have hudvd : ∀ i ∈ Finset.Icc 1 (p-1), b ∣ u i := fun i _ => ⟨((i:ℕ):ZMod (p^3))⁻¹, rfl⟩
  -- each factor (j*p+i) = c_i * (1 + u i)
  have hfac : ∀ i ∈ Finset.Icc 1 (p-1),
      ((j*p+i : ℕ) : ZMod (p^3)) = ((i:ℕ):ZMod (p^3)) * (1 + u i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hci : IsUnit ((i:ℕ):ZMod (p^3)) :=
      (ZMod.isUnit_iff_coprime i (p^3)).mpr (Nat.Coprime.pow_right 3 ((hp.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm))
    have key : ((i:ℕ):ZMod (p^3)) * (1 + u i) = ((i:ℕ):ZMod (p^3)) + b := by
      show ((i:ℕ):ZMod (p^3)) * (1 + b * ((i:ℕ):ZMod (p^3))⁻¹) = ((i:ℕ):ZMod (p^3)) + b
      rw [mul_add, mul_one, show ((i:ℕ):ZMod (p^3)) * (b * ((i:ℕ):ZMod (p^3))⁻¹)
        = b * (((i:ℕ):ZMod (p^3)) * ((i:ℕ):ZMod (p^3))⁻¹) by ring, ZMod.mul_inv_of_unit _ hci, mul_one]
    rw [key, hb, ← Nat.cast_add]; congr 1; omega
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_Icc_cast]
  -- ∏(1+u) = 1
  rw [prod_one_add_truncate b hb3 u inv2 hinv2 _ hudvd]
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsumu : (∑ i ∈ Finset.Icc 1 (p-1), u i) = 0 := by
    simp only [hu, ← Finset.mul_sum]
    obtain ⟨y, hy⟩ := H1div hp hp5
    rw [hy, hb, show ((j*p:ℕ):ZMod (p^3)) * ((p:ZMod (p^3))^2 * y)
      = (j:ZMod (p^3)) * ((p:ZMod (p^3))^3) * y by push_cast; ring, hp30]; ring
  have hsumu2 : (∑ i ∈ Finset.Icc 1 (p-1), (u i)^2) = 0 := by
    simp only [hu, mul_pow, ← Finset.mul_sum]
    obtain ⟨z, hz⟩ := H2div hp hp5
    rw [hz, hb, show ((j*p:ℕ):ZMod (p^3))^2 * ((p:ZMod (p^3)) * z)
      = (j:ZMod (p^3))^2 * ((p:ZMod (p^3))^3) * z by push_cast; ring, hp30]; ring
  rw [hsumu, hsumu2]; ring

-- Partial block: ∏_{i=1}^r (q*p+i) ≡ r! · (1 + qp·H1 + (qp)²·(H1²-Q)·inv2) mod p³
-- where H1 = ∑ i⁻¹, Q = ∑ i⁻², inv2 = 1/2.
theorem partial_block (hp : Nat.Prime p) (hp5 : 5 ≤ p) (q r : ℕ) (hr : r ≤ p-1)
    (inv2 : ZMod (p^3)) (hinv2 : (2:ZMod (p^3)) * inv2 = 1) :
    ∏ i ∈ Finset.Icc 1 r, ((q*p+i : ℕ) : ZMod (p^3))
      = ((Nat.factorial r : ℕ) : ZMod (p^3)) *
        (1 + ((q*p:ℕ):ZMod (p^3)) * (∑ i ∈ Finset.Icc 1 r, ((i:ℕ):ZMod (p^3))⁻¹)
          + (((q*p:ℕ):ZMod (p^3))^2)
            * (((∑ i ∈ Finset.Icc 1 r, ((i:ℕ):ZMod (p^3))⁻¹)^2
                - ∑ i ∈ Finset.Icc 1 r, (((i:ℕ):ZMod (p^3))⁻¹)^2)) * inv2) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  set b : ZMod (p^3) := ((q*p : ℕ) : ZMod (p^3)) with hb
  have hb3 : b^3 = 0 := by
    rw [hb, ← Nat.cast_pow, show (q*p)^3 = (q^3) * p^3 by ring, Nat.cast_mul, Nat.cast_pow,
      ZMod.natCast_self, mul_zero]
  set u : ℕ → ZMod (p^3) := fun i => b * ((i:ℕ):ZMod (p^3))⁻¹ with hu
  have hudvd : ∀ i ∈ Finset.Icc 1 r, b ∣ u i := fun i _ => ⟨((i:ℕ):ZMod (p^3))⁻¹, rfl⟩
  have hfac : ∀ i ∈ Finset.Icc 1 r,
      ((q*p+i : ℕ) : ZMod (p^3)) = ((i:ℕ):ZMod (p^3)) * (1 + u i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hci : IsUnit ((i:ℕ):ZMod (p^3)) :=
      (ZMod.isUnit_iff_coprime i (p^3)).mpr (Nat.Coprime.pow_right 3 ((hp.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm))
    have key : ((i:ℕ):ZMod (p^3)) * (1 + u i) = ((i:ℕ):ZMod (p^3)) + b := by
      show ((i:ℕ):ZMod (p^3)) * (1 + b * ((i:ℕ):ZMod (p^3))⁻¹) = ((i:ℕ):ZMod (p^3)) + b
      rw [mul_add, mul_one, show ((i:ℕ):ZMod (p^3)) * (b * ((i:ℕ):ZMod (p^3))⁻¹)
        = b * (((i:ℕ):ZMod (p^3)) * ((i:ℕ):ZMod (p^3))⁻¹) by ring, ZMod.mul_inv_of_unit _ hci, mul_one]
    rw [key, hb, ← Nat.cast_add]; congr 1; omega
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_Icc_cast,
    prod_one_add_truncate b hb3 u inv2 hinv2 _ hudvd]
  congr 1
  simp only [hu, ← Finset.mul_sum, mul_pow]
  ring

-- product of multiples of p up to m = p^q * q! where q = m/p
theorem prod_multiples (hp : Nat.Prime p) (m : ℕ) :
    ∏ t ∈ (Finset.Icc 1 m).filter (fun t => p ∣ t), (t : ZMod (p^3))
      = (p : ZMod (p^3))^(m/p) * ((Nat.factorial (m/p) : ℕ) : ZMod (p^3)) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hbij : (Finset.Icc 1 m).filter (fun t => p ∣ t) = (Finset.Icc 1 (m/p)).image (fun j => p * j) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩
      have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at h1)
      exact ⟨j, ⟨hj1, (Nat.le_div_iff_mul_le hp.pos).mpr (by rw [mul_comm]; exact h2)⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨j, rfl⟩⟩
      · have := hp.two_le; nlinarith
      · calc p * j ≤ p * (m/p) := Nat.mul_le_mul_left p hj2
          _ = (m/p) * p := by ring
          _ ≤ m := Nat.div_mul_le_self m p
  rw [hbij, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp.pos h)]
  push_cast
  rw [Finset.prod_mul_distrib, Finset.prod_const, prod_Icc_cast, Nat.card_Icc, Nat.add_sub_cancel]

-- factorial of a multiple of p, mod p^3
theorem fact_round (hp : Nat.Prime p) (hp5 : 5 ≤ p) (q : ℕ) :
    ((Nat.factorial (q*p) : ℕ) : ZMod (p^3))
      = (p:ZMod (p^3))^q * ((Nat.factorial q : ℕ) : ZMod (p^3)) * ((Nat.factorial (p-1) : ℕ) : ZMod (p^3))^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q+1)*p = q*p+p from by ring]
    have hpp := hp.pos
    have hsplit : ((Nat.factorial (q*p+p) : ℕ) : ZMod (p^3))
        = ((Nat.factorial (q*p):ℕ):ZMod (p^3)) * ∏ i ∈ Finset.Icc (q*p+1) (q*p+p), ((i:ℕ):ZMod (p^3)) := by
      rw [← prod_Icc_cast, ← prod_Icc_cast, ← Finset.prod_union]
      · congr 1
        ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      · rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_Icc] at hx hy; omega
    have hblock : ∏ i ∈ Finset.Icc (q*p+1) (q*p+p), ((i:ℕ):ZMod (p^3))
        = ((Nat.factorial (p-1):ℕ):ZMod (p^3)) * ((q*p+p : ℕ) : ZMod (p^3)) := by
      have htop : q*p+p = (q*p+p-1)+1 := by omega
      rw [htop, Finset.prod_Icc_succ_top (by omega)]
      have hmap : Finset.Icc (q*p+1) (q*p+p-1) = Finset.map (addLeftEmbedding (q*p)) (Finset.Icc 1 (p-1)) := by
        rw [Finset.map_add_left_Icc]; congr 1 <;> omega
      rw [hmap, Finset.prod_map]
      have hfb : ∏ i ∈ Finset.Icc 1 (p-1), ((addLeftEmbedding (q*p) i : ℕ):ZMod (p^3))
          = ((Nat.factorial (p-1):ℕ):ZMod (p^3)) := by
        rw [← full_block hp hp5 q]; apply Finset.prod_congr rfl
        intro i _; simp [addLeftEmbedding_apply]
      rw [hfb, show (q*p+p-1)+1 = q*p+p from by omega]
    rw [hsplit, ih, hblock, Nat.factorial_succ]
    push_cast; ring

theorem factmod (hp : Nat.Prime p) (hp5 : 5 ≤ p) (m : ℕ)
    (inv2 : ZMod (p^3)) (hinv2 : (2:ZMod (p^3)) * inv2 = 1) :
    ((Nat.factorial m : ℕ) : ZMod (p^3))
      = (p:ZMod (p^3))^(m/p) * ((Nat.factorial (m/p) : ℕ) : ZMod (p^3))
        * ((Nat.factorial (p-1) : ℕ) : ZMod (p^3))^(m/p)
        * (((Nat.factorial (m%p) : ℕ) : ZMod (p^3))
          * (1 + (((m/p)*p : ℕ) : ZMod (p^3)) * (∑ i ∈ Finset.Icc 1 (m%p), ((i:ℕ):ZMod (p^3))⁻¹)
            + (((m/p)*p : ℕ) : ZMod (p^3))^2
              * (((∑ i ∈ Finset.Icc 1 (m%p), ((i:ℕ):ZMod (p^3))⁻¹)^2
                  - ∑ i ∈ Finset.Icc 1 (m%p), (((i:ℕ):ZMod (p^3))⁻¹)^2)) * inv2)) := by
  set q := m/p with hq
  set r := m%p with hrr
  have hr : r ≤ p-1 := by have := Nat.mod_lt m hp.pos; omega
  have hm : m = q*p + r := by rw [hq, hrr, Nat.div_add_mod' m p]
  have hsplit : ((Nat.factorial m : ℕ) : ZMod (p^3))
      = ((Nat.factorial (q*p) : ℕ) : ZMod (p^3)) * ∏ i ∈ Finset.Icc 1 r, ((q*p+i : ℕ):ZMod (p^3)) := by
    rw [hm, ← prod_Icc_cast, ← prod_Icc_cast]
    have hmap : Finset.Icc (q*p+1) (q*p+r) = Finset.map (addLeftEmbedding (q*p)) (Finset.Icc 1 r) := by
      rw [Finset.map_add_left_Icc]
    have hpr : ∏ i ∈ Finset.Icc 1 r, ((q*p+i : ℕ):ZMod (p^3))
        = ∏ i ∈ Finset.Icc (q*p+1) (q*p+r), ((i:ℕ):ZMod (p^3)) := by
      rw [hmap, Finset.prod_map]; apply Finset.prod_congr rfl; intro i _; simp [addLeftEmbedding_apply]
    rw [hpr, ← Finset.prod_union (by rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_Icc] at hx hy; omega)]
    congr 1; ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  rw [hsplit, fact_round hp hp5 q, partial_block hp hp5 q r hr inv2 hinv2]


-- ============ s=1 base case development ============
open Finset in
theorem inv_pm1 (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((p:ZMod (p^3)) - 1)⁻¹ = -(1 + p + p^2) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hu : ((p:ZMod (p^3)) - 1) * (-(1 + (p:ZMod (p^3)) + p^2)) = 1 := by
    linear_combination (-(1:ZMod (p^3))) * hp30
  have hunit : IsUnit ((p:ZMod (p^3)) - 1) := (Units.mkOfMulEqOne _ _ hu).isUnit
  calc ((p:ZMod (p^3)) - 1)⁻¹
      = ((p:ZMod (p^3)) - 1)⁻¹ * (((p:ZMod (p^3)) - 1) * (-(1 + (p:ZMod (p^3)) + p^2))) := by rw [hu, mul_one]
    _ = (((p:ZMod (p^3)) - 1)⁻¹ * ((p:ZMod (p^3)) - 1)) * (-(1 + (p:ZMod (p^3)) + p^2)) := by ring
    _ = -(1 + (p:ZMod (p^3)) + p^2) := by rw [ZMod.inv_mul_of_unit _ hunit, one_mul]

theorem inv_pm2 (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (inv2 : ZMod (p^3)) (hinv2 : (2:ZMod (p^3)) * inv2 = 1) :
    ((p:ZMod (p^3)) - 2)⁻¹ = -(inv2 + (p:ZMod (p^3))*inv2^2 + (p:ZMod (p^3))^2*inv2^3) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hu : ((p:ZMod (p^3)) - 2) * (-(inv2 + (p:ZMod (p^3))*inv2^2 + (p:ZMod (p^3))^2*inv2^3)) = 1 := by
    linear_combination (1 + (p:ZMod (p^3))*inv2 + p^2*inv2^2)*hinv2 - inv2^3*hp30
  have hunit : IsUnit ((p:ZMod (p^3)) - 2) := (Units.mkOfMulEqOne _ _ hu).isUnit
  calc ((p:ZMod (p^3)) - 2)⁻¹
      = ((p:ZMod (p^3)) - 2)⁻¹ * (((p:ZMod (p^3)) - 2) * (-(inv2 + (p:ZMod (p^3))*inv2^2 + (p:ZMod (p^3))^2*inv2^3))) := by rw [hu, mul_one]
    _ = (((p:ZMod (p^3)) - 2)⁻¹ * ((p:ZMod (p^3)) - 2)) * (-(inv2 + (p:ZMod (p^3))*inv2^2 + (p:ZMod (p^3))^2*inv2^3)) := by ring
    _ = -(inv2 + (p:ZMod (p^3))*inv2^2 + (p:ZMod (p^3))^2*inv2^3) := by rw [ZMod.inv_mul_of_unit _ hunit, one_mul]

open Finset Nat in
theorem itemI_nat (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (3*p-3).choose (p-1) * (p-1)! = ∏ i ∈ Finset.Icc (2*p-1) (3*p-3), i := by
  have hk : p-1 ≤ 3*p-3 := by omega
  have hchoose := Nat.choose_mul_factorial_mul_factorial hk
  have hsub : 3*p-3-(p-1) = 2*p-2 := by omega
  rw [hsub] at hchoose
  have hIcceq : Finset.Icc (2*p-1) (3*p-3) = Finset.Ico (2*p-1) (3*p-2) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hf1 : (3*p-3)! = ∏ i ∈ Finset.Ico 1 (3*p-2), i := by
    rw [show 3*p-2 = (3*p-3)+1 by omega, Finset.prod_Ico_id_eq_factorial]
  have hf2 : (2*p-2)! = ∏ i ∈ Finset.Ico 1 (2*p-1), i := by
    rw [show 2*p-1 = (2*p-2)+1 by omega, Finset.prod_Ico_id_eq_factorial]
  have hsplit : (3*p-3)! = (2*p-2)! * ∏ i ∈ Finset.Icc (2*p-1) (3*p-3), i := by
    rw [hf1, hf2, hIcceq, Finset.prod_Ico_consecutive _ (by omega) (by omega)]
  have hcancel : ((3*p-3).choose (p-1) * (p-1)!) * (2*p-2)! = (∏ i ∈ Finset.Icc (2*p-1) (3*p-3), i) * (2*p-2)! := by
    rw [mul_comm ((∏ i ∈ Finset.Icc (2*p-1) (3*p-3), i)) _, ← hsplit]
    rw [mul_assoc, mul_comm ((p-1)!) ((2*p-2)!), ← mul_assoc] at hchoose ⊢
    linarith [hchoose]
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) hcancel

open Finset in
theorem cast_sub_one (hp : Nat.Prime p) (j : ℕ) (hj : j ≤ p) :
    ((p - j : ℕ) : ZMod (p^3)) = (p:ZMod (p^3)) - j := by
  rw [Nat.cast_sub hj]

open Finset in
-- S := ∑_{i=1}^{p-3} i⁻¹ ≡ 3·inv2 mod p
theorem hSdiv (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (inv2 : ZMod (p^3)) (hinv2 : (2:ZMod (p^3)) * inv2 = 1) :
    (p:ZMod (p^3)) ∣ ((∑ i ∈ Finset.Icc 1 (p-3), ((i:ℕ):ZMod (p^3))⁻¹) - 3*inv2) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsplit : (∑ i ∈ Finset.Icc 1 (p-1), ((i:ℕ):ZMod (p^3))⁻¹)
      = (∑ i ∈ Finset.Icc 1 (p-3), ((i:ℕ):ZMod (p^3))⁻¹)
        + ((p-2:ℕ):ZMod (p^3))⁻¹ + ((p-1:ℕ):ZMod (p^3))⁻¹ := by
    have e1 : Finset.Icc 1 (p-1) = Finset.Icc 1 ((p-2)+1) := by congr 1; omega
    have e2 : Finset.Icc 1 (p-2) = Finset.Icc 1 ((p-3)+1) := by congr 1; omega
    rw [e1, Finset.sum_Icc_succ_top (by omega), e2, Finset.sum_Icc_succ_top (by omega),
      show p-2+1 = p-1 from by omega, show p-3+1 = p-2 from by omega]
  obtain ⟨Y, hY⟩ := H1div hp hp5
  have hi1 : ((p-1:ℕ):ZMod (p^3))⁻¹ = -(1 + (p:ZMod (p^3)) + p^2) := by
    rw [cast_sub_one hp 1 (by omega)]; push_cast; rw [inv_pm1 hp hp5]
  have hi2 : ((p-2:ℕ):ZMod (p^3))⁻¹ = -(inv2 + (p:ZMod (p^3))*inv2^2 + (p:ZMod (p^3))^2*inv2^3) := by
    rw [cast_sub_one hp 2 (by omega)]; push_cast; rw [inv_pm2 hp hp5 inv2 hinv2]
  have hS : (∑ i ∈ Finset.Icc 1 (p-3), ((i:ℕ):ZMod (p^3))⁻¹)
      = (p:ZMod (p^3))^2 * Y - ((p-2:ℕ):ZMod (p^3))⁻¹ - ((p-1:ℕ):ZMod (p^3))⁻¹ := by
    rw [hY] at hsplit; linear_combination -hsplit
  refine ⟨(p:ZMod (p^3))*Y + inv2^2 + 1 + (p:ZMod (p^3))*(inv2^3+1), ?_⟩
  rw [hS, hi1, hi2]
  linear_combination (-1 : ZMod (p^3)) * hinv2

open Finset in
theorem itemI_prodsplit (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∏ i ∈ Finset.Icc (2*p-1) (3*p-3), ((i:ℕ):ZMod (p^3)))
      = ((2*p-1:ℕ):ZMod (p^3)) * ((2*p:ℕ):ZMod (p^3))
        * (∏ i ∈ Finset.Icc 1 (p-3), ((2*p+i:ℕ):ZMod (p^3))) := by
  have hins1 : Finset.Icc (2*p-1) (3*p-3) = insert (2*p-1) (Finset.Icc (2*p) (3*p-3)) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hins2 : Finset.Icc (2*p) (3*p-3) = insert (2*p) (Finset.Icc (2*p+1) (3*p-3)) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hnm1 : (2*p-1) ∉ Finset.Icc (2*p) (3*p-3) := by simp only [Finset.mem_Icc]; omega
  have hnm2 : (2*p) ∉ Finset.Icc (2*p+1) (3*p-3) := by simp only [Finset.mem_Icc]; omega
  have hmap : Finset.Icc (2*p+1) (3*p-3) = Finset.map (addLeftEmbedding (2*p)) (Finset.Icc 1 (p-3)) := by
    rw [Finset.map_add_left_Icc]; congr 1 <;> omega
  rw [hins1, Finset.prod_insert hnm1, hins2, Finset.prod_insert hnm2, hmap, Finset.prod_map]
  have : ∏ i ∈ Finset.Icc 1 (p-3), ((addLeftEmbedding (2*p) i : ℕ):ZMod (p^3))
      = ∏ i ∈ Finset.Icc 1 (p-3), ((2*p+i:ℕ):ZMod (p^3)) := by
    apply Finset.prod_congr rfl; intro i _; simp [addLeftEmbedding_apply]
  rw [this]; ring

theorem mulu_cancel {R : Type*} [CommRing R] {u a b : R} (hu : IsUnit u) (h : a * u = b * u) :
    a = b := by
  obtain ⟨w, rfl⟩ := hu
  have h2 : a * (w:R) * (↑w⁻¹) = b * (w:R) * ↑w⁻¹ := by rw [h]
  simpa [mul_assoc, Units.mul_inv] using h2

open Finset in
theorem itemI (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (inv2 : ZMod (p^3)) (hinv2 : (2:ZMod (p^3)) * inv2 = 1) :
    2 * ((Nat.choose (3*p-3) (p-1):ℕ):ZMod (p^3))
      = -2*(p:ZMod (p^3)) + (p:ZMod (p^3))^2*((p:ZMod (p^3))-5) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  set CC := ((Nat.choose (3*p-3) (p-1):ℕ):ZMod (p^3)) with hCC
  -- cast nat identity
  have hcast : CC * ((Nat.factorial (p-1):ℕ):ZMod (p^3))
      = ∏ i ∈ Finset.Icc (2*p-1) (3*p-3), ((i:ℕ):ZMod (p^3)) := by
    have h := itemI_nat hp hp5
    rw [hCC, ← Nat.cast_mul, h, Nat.cast_prod]
  -- product split + partial block
  set S := ∑ i ∈ Finset.Icc 1 (p-3), ((i:ℕ):ZMod (p^3))⁻¹ with hSdef
  set S2 := ∑ i ∈ Finset.Icc 1 (p-3), (((i:ℕ):ZMod (p^3))⁻¹)^2 with hS2def
  have hpb : ∏ i ∈ Finset.Icc 1 (p-3), ((2*p+i:ℕ):ZMod (p^3))
      = ((Nat.factorial (p-3):ℕ):ZMod (p^3)) * (1 + ((2*p:ℕ):ZMod (p^3))*S
          + ((2*p:ℕ):ZMod (p^3))^2*(S^2 - S2)*inv2) := by
    have := partial_block hp hp5 2 (p-3) (by omega) inv2 hinv2
    simpa [hSdef, hS2def] using this
  -- (p-1)! = (p-1)*(p-2)*(p-3)!  in ZMod
  have hfact : ((Nat.factorial (p-1):ℕ):ZMod (p^3))
      = ((p-1:ℕ):ZMod (p^3)) * ((p-2:ℕ):ZMod (p^3)) * ((Nat.factorial (p-3):ℕ):ZMod (p^3)) := by
    have e : Nat.factorial (p-1) = (p-1) * ((p-2) * Nat.factorial (p-3)) := by
      rw [show p-1 = (p-2)+1 from by omega, Nat.factorial_succ, show p-2 = (p-3)+1 from by omega,
        Nat.factorial_succ]
    rw [e]; push_cast; ring
  -- u3 unit
  have hu3 : IsUnit ((Nat.factorial (p-3):ℕ):ZMod (p^3)) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    apply hp.coprime_iff_not_dvd.mpr
    rw [Nat.Prime.dvd_factorial hp]; omega
  -- combine to cancel (p-3)!
  have hbig : (CC * ((p-1:ℕ):ZMod (p^3)) * ((p-2:ℕ):ZMod (p^3))) * ((Nat.factorial (p-3):ℕ):ZMod (p^3))
      = ((2*p-1:ℕ):ZMod (p^3)) * ((2*p:ℕ):ZMod (p^3)) * (1 + ((2*p:ℕ):ZMod (p^3))*S
          + ((2*p:ℕ):ZMod (p^3))^2*(S^2 - S2)*inv2) * ((Nat.factorial (p-3):ℕ):ZMod (p^3)) := by
    have := hcast
    rw [hfact, itemI_prodsplit hp hp5, hpb] at this
    linear_combination this
  have hmid : CC * ((p-1:ℕ):ZMod (p^3)) * ((p-2:ℕ):ZMod (p^3))
      = ((2*p-1:ℕ):ZMod (p^3)) * ((2*p:ℕ):ZMod (p^3)) * (1 + ((2*p:ℕ):ZMod (p^3))*S
          + ((2*p:ℕ):ZMod (p^3))^2*(S^2 - S2)*inv2) := mulu_cancel hu3 hbig
  -- simplify RHS = -2p - 2p^2
  obtain ⟨w, hw⟩ := hSdiv hp hp5 inv2 hinv2
  have hSeq : S = 3*inv2 + (p:ZMod (p^3))*w := by rw [← hSdef] at hw; linear_combination hw
  have h2p1 : ((2*p-1:ℕ):ZMod (p^3)) = 2*(p:ZMod (p^3)) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2p : ((2*p:ℕ):ZMod (p^3)) = 2*(p:ZMod (p^3)) := by push_cast; ring
  have hRHS : CC * ((p-1:ℕ):ZMod (p^3)) * ((p-2:ℕ):ZMod (p^3)) = -2*(p:ZMod (p^3)) - 2*(p:ZMod (p^3))^2 := by
    rw [hmid, h2p1, h2p, hSeq]
    linear_combination (-16*S2*inv2*(p:ZMod (p^3)) + 8*S2*inv2 + 144*inv2^3*(p:ZMod (p^3))
      - 72*inv2^3 + 96*inv2^2*(p:ZMod (p^3))^2*w - 48*inv2^2*(p:ZMod (p^3))*w
      + 16*inv2*(p:ZMod (p^3))^3*w^2 - 8*inv2*(p:ZMod (p^3))^2*w^2 + 24*inv2
      + 8*(p:ZMod (p^3))*w - 4*w)*hp30 + (-6*(p:ZMod (p^3))^2)*hinv2
  -- now derive 2*CC = -2p + p^2(p-5)
  have hcp1 : ((p-1:ℕ):ZMod (p^3)) = (p:ZMod (p^3)) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcp2 : ((p-2:ℕ):ZMod (p^3)) = (p:ZMod (p^3)) - 2 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcp1, hcp2] at hRHS
  -- (p-1)(p-2) is a unit
  have huu : IsUnit (((p:ZMod (p^3)) - 1) * ((p:ZMod (p^3)) - 2)) := by
    rw [← hcp1, ← hcp2, ← Nat.cast_mul, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    apply (hp.coprime_iff_not_dvd).mpr
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h <;>
      · have := Nat.le_of_dvd (by omega) h; omega
  apply mulu_cancel huu
  rw [show (2*CC)*(((p:ZMod (p^3))-1)*((p:ZMod (p^3))-2))
      = 2*(CC*((p:ZMod (p^3))-1)*((p:ZMod (p^3))-2)) from by ring, hRHS]
  linear_combination (-(p:ZMod (p^3))^2 + 8*(p:ZMod (p^3)) - 15)*hp30

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


end A374605

-- ===== imported choose-congruence lemmas =====
section CCblock
open Finset Nat
lemma pmul_congr (p : ℕ) [NeZero (p^2)] (a b : ℕ) (h : a % p = b % p) :
    (p : ZMod (p^2)) * (a : ZMod (p^2)) = (p : ZMod (p^2)) * (b : ZMod (p^2)) := by
  have hp20 : ((p:ZMod (p^2)))*p = 0 := by
    have e : ((p:ZMod (p^2)))*p = ((p^2:ℕ):ZMod (p^2)) := by push_cast; ring
    rw [e, ZMod.natCast_self]
  have ha : (a:ZMod (p^2)) = (p:ZMod (p^2)) * ((a/p:ℕ):ZMod (p^2)) + ((a%p:ℕ):ZMod (p^2)) := by
    conv_lhs => rw [← Nat.div_add_mod a p]
    push_cast; ring
  have hb : (b:ZMod (p^2)) = (p:ZMod (p^2)) * ((b/p:ℕ):ZMod (p^2)) + ((b%p:ℕ):ZMod (p^2)) := by
    conv_lhs => rw [← Nat.div_add_mod b p]
    push_cast; ring
  rw [ha, hb, h]
  linear_combination (((a/p:ℕ):ZMod (p^2)) - ((b/p:ℕ):ZMod (p^2))) * hp20

-- ∏_{i=p+1}^{2p-2} i ≡ (p-2)! mod p
lemma block_mod (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∏ i ∈ Finset.Icc (p+1) (2*p-2), i) % p = (Nat.factorial (p-2)) % p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]
  push_cast [Nat.cast_prod]
  have hmap : Finset.Icc (p+1) (2*p-2) = Finset.map (addLeftEmbedding p) (Finset.Icc 1 (p-2)) := by
    rw [Finset.map_add_left_Icc]; congr 1 <;> omega
  rw [hmap, Finset.prod_map]
  have e1 : ∏ i ∈ Finset.Icc 1 (p-2), ((addLeftEmbedding p i : ℕ) : ZMod p)
      = ∏ i ∈ Finset.Icc 1 (p-2), ((i:ℕ):ZMod p) := by
    apply Finset.prod_congr rfl; intro i _
    simp [addLeftEmbedding_apply]
  rw [e1, ← Nat.cast_prod]
  congr 1
  rw [show Finset.Icc 1 (p-2) = Finset.Ico 1 ((p-2)+1) from by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  exact Finset.prod_Ico_id_eq_factorial (p-2)

lemma C2pm2 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((Nat.choose (2*p-2) (p-1) : ℕ) : ZMod (p^2)) = -(p : ZMod (p^2)) := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hp20 : ((p:ZMod (p^2)))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hch : Nat.choose (2*p-2) (p-1) * (p-1)! * (p-1)! = (2*p-2)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p-1 ≤ 2*p-2 from by omega)
    rwa [show 2*p-2-(p-1) = p-1 from by omega] at h
  -- factorial split
  have hfact : (2*p-2)! = (p-1)! * (p * ∏ i ∈ Finset.Icc (p+1) (2*p-2), i) := by
    have d1 : (2*p-2)! = ∏ i ∈ Finset.Icc 1 (2*p-2), i := by
      rw [show Finset.Icc 1 (2*p-2) = Finset.Ico 1 ((2*p-2)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.prod_Ico_id_eq_factorial]
    have d2 : (p-1)! = ∏ i ∈ Finset.Icc 1 (p-1), i := by
      rw [show Finset.Icc 1 (p-1) = Finset.Ico 1 ((p-1)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
      exact (Finset.prod_Ico_id_eq_factorial (p-1)).symm
    have hu1 : Finset.Icc 1 (2*p-2) = Finset.Icc 1 (p-1) ∪ Finset.Icc p (2*p-2) := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hd1 : Disjoint (Finset.Icc 1 (p-1)) (Finset.Icc p (2*p-2)) := by
      rw [Finset.disjoint_left]; intro x hx hy
      simp only [Finset.mem_Icc] at hx hy; omega
    have hu2 : Finset.Icc p (2*p-2) = insert p (Finset.Icc (p+1) (2*p-2)) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnm : p ∉ Finset.Icc (p+1) (2*p-2) := by simp only [Finset.mem_Icc]; omega
    rw [d1, hu1, Finset.prod_union hd1, hu2, Finset.prod_insert hnm, ← d2]
  -- cast
  have hcZ : (Nat.choose (2*p-2) (p-1) : ZMod (p^2)) * ((p-1)! : ZMod (p^2)) * ((p-1)! : ZMod (p^2))
      = (p:ZMod (p^2)) * ((p-1)! : ZMod (p^2)) * ((p-2)! : ZMod (p^2)) := by
    have e := congrArg (fun z : ℕ => (z : ZMod (p^2))) hch
    simp only [Nat.cast_mul] at e
    rw [e, hfact]
    push_cast
    have hpc := pmul_congr p (∏ i ∈ Finset.Icc (p+1) (2*p-2), i) (Nat.factorial (p-2))
      (block_mod p hp hp5)
    push_cast at hpc
    rw [hpc]; ring
  -- (p-1)! = (p-1)*(p-2)!
  have hfac21 : ((p-1)! : ZMod (p^2)) = ((p:ZMod (p^2))-1) * ((p-2)! : ZMod (p^2)) := by
    have : (p-1)! = (p-1) * (p-2)! := by
      rw [show p-1 = (p-2)+1 from by omega, Nat.factorial_succ, show (p-2)+1 = p-1 from by omega]
    rw [this]; push_cast [show (1:ℕ) ≤ p from by omega]; ring
  -- (p-2)! is a unit, (p-1) ... combine
  have hu2 : IsUnit (((p-2)! : ℕ) : ZMod (p^2)) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
    rw [Nat.Prime.dvd_factorial hp]; omega
  rw [hfac21] at hcZ
  have key : (Nat.choose (2*p-2) (p-1) : ZMod (p^2))*((p:ZMod (p^2))-1)^2
      = (p:ZMod (p^2))*((p:ZMod (p^2))-1) := by
    have h0 : ((Nat.choose (2*p-2) (p-1) : ZMod (p^2))*((p:ZMod (p^2))-1)^2
        - (p:ZMod (p^2))*((p:ZMod (p^2))-1)) * ((p-2)!:ZMod (p^2))^2 = 0 := by
      linear_combination hcZ
    have hk := (hu2.pow 2).mul_left_eq_zero.mp h0
    linear_combination hk
  have hunitb : IsUnit ((p:ZMod (p^2))-1) := by
    have he : ((p-1:ℕ):ZMod (p^2)) = (p:ZMod (p^2))-1 := by
      push_cast [show (1:ℕ)≤p from by omega]; ring
    rw [← he]
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    apply Nat.Coprime.pow_right
    rw [show p = (p-1)+1 from by omega]
    exact Nat.coprime_self_add_right.mpr (by simp [Nat.Coprime])
  have hzero : ((Nat.choose (2*p-2) (p-1) : ZMod (p^2)) + (p:ZMod (p^2)))*((p:ZMod (p^2))-1)^2 = 0 := by
    linear_combination key + ((p:ZMod (p^2))-1)*hp20
  have hfin := (hunitb.pow 2).mul_left_eq_zero.mp hzero
  exact eq_neg_of_add_eq_zero_left hfin

lemma C5pm5 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((Nat.choose (5*p-5) (p-1) : ℕ) : ZMod (p^2)) = -(p : ZMod (p^2)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hch : Nat.choose (5*p-5) (p-1) * (p-1)! * (4*p-4)! = (5*p-5)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p-1 ≤ 5*p-5 from by omega)
    rwa [show 5*p-5-(p-1) = 4*p-4 from by omega] at h
  have hsplit : (5*p-5)! = (4*p-4)! * ∏ i ∈ Finset.Icc (4*p-3) (5*p-5), i := by
    have d1 : (5*p-5)! = ∏ i ∈ Finset.Icc 1 (5*p-5), i := by
      rw [show Finset.Icc 1 (5*p-5) = Finset.Ico 1 ((5*p-5)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.prod_Ico_id_eq_factorial]
    have d2 : (4*p-4)! = ∏ i ∈ Finset.Icc 1 (4*p-4), i := by
      rw [show Finset.Icc 1 (4*p-4) = Finset.Ico 1 ((4*p-4)+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
      exact (Finset.prod_Ico_id_eq_factorial (4*p-4)).symm
    have hu1 : Finset.Icc 1 (5*p-5) = Finset.Icc 1 (4*p-4) ∪ Finset.Icc (4*p-3) (5*p-5) := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hd1 : Disjoint (Finset.Icc 1 (4*p-4)) (Finset.Icc (4*p-3) (5*p-5)) := by
      rw [Finset.disjoint_left]; intro x hx hy
      simp only [Finset.mem_Icc] at hx hy; omega
    rw [d1, hu1, Finset.prod_union hd1, ← d2]
  have hC : Nat.choose (5*p-5) (p-1) * (p-1)! = ∏ i ∈ Finset.Icc (4*p-3) (5*p-5), i := by
    have heq : Nat.choose (5*p-5) (p-1) * (p-1)! * (4*p-4)!
        = (∏ i ∈ Finset.Icc (4*p-3) (5*p-5), i) * (4*p-4)! := by
      rw [hch, hsplit]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) heq
  have hprodsplit : ∏ i ∈ Finset.Icc (4*p-3) (5*p-5), i
      = (∏ i ∈ Finset.Icc (4*p-3) (4*p-1), i) * ((4*p) * ∏ i ∈ Finset.Icc (4*p+1) (5*p-5), i) := by
    have hu1 : Finset.Icc (4*p-3) (5*p-5) = Finset.Icc (4*p-3) (4*p-1) ∪ Finset.Icc (4*p) (5*p-5) := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hd1 : Disjoint (Finset.Icc (4*p-3) (4*p-1)) (Finset.Icc (4*p) (5*p-5)) := by
      rw [Finset.disjoint_left]; intro x hx hy
      simp only [Finset.mem_Icc] at hx hy; omega
    have hu2 : Finset.Icc (4*p) (5*p-5) = insert (4*p) (Finset.Icc (4*p+1) (5*p-5)) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnm : (4*p) ∉ Finset.Icc (4*p+1) (5*p-5) := by simp only [Finset.mem_Icc]; omega
    rw [hu1, Finset.prod_union hd1, hu2, Finset.prod_insert hnm]
  rw [hprodsplit] at hC
  set Q1 := ∏ i ∈ Finset.Icc (4*p-3) (4*p-1), i with hQ1def
  set Q2 := ∏ i ∈ Finset.Icc (4*p+1) (5*p-5), i with hQ2def
  -- mod p sub-facts
  have hQ1p : (Q1 : ZMod p) = (-3)*(-2)*(-1) := by
    rw [hQ1def]
    have hset : Finset.Icc (4*p-3) (4*p-1) = {4*p-3, 4*p-2, 4*p-1} := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hset, Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
    push_cast [Nat.cast_sub (show (3:ℕ) ≤ 4*p by omega), Nat.cast_sub (show (2:ℕ) ≤ 4*p by omega),
      Nat.cast_sub (show (1:ℕ) ≤ 4*p by omega)]
    rw [ZMod.natCast_self]; ring
  have hQ2p : (Q2 : ZMod p) = ((p-5)! : ZMod p) := by
    rw [hQ2def, show Finset.Icc (4*p+1) (5*p-5) = Finset.map (addLeftEmbedding (4*p)) (Finset.Icc 1 (p-5)) from by
      rw [Finset.map_add_left_Icc]; congr 1 <;> omega, Nat.cast_prod, Finset.prod_map]
    have e1 : ∏ i ∈ Finset.Icc 1 (p-5), ((addLeftEmbedding (4*p) i : ℕ) : ZMod p)
        = ∏ i ∈ Finset.Icc 1 (p-5), ((i:ℕ):ZMod p) := by
      apply Finset.prod_congr rfl; intro i _
      simp only [addLeftEmbedding_apply]
      push_cast; rw [ZMod.natCast_self]; ring
    rw [e1, ← Nat.cast_prod]
    congr 1
    rw [show Finset.Icc 1 (p-5) = Finset.Ico 1 ((p-5)+1) from by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    exact Finset.prod_Ico_id_eq_factorial (p-5)
  have hfacp : ((p-1)! : ZMod p) = 24 * ((p-5)! : ZMod p) := by
    have hf : (p-1)! = (p-1)*(p-2)*(p-3)*(p-4)*(p-5)! := by
      have e1 : (p-1)! = (p-1)*(p-2)! := by
        rw [show p-1=(p-2)+1 from by omega, Nat.factorial_succ, show (p-2)+1=p-1 from by omega]
      have e2 : (p-2)! = (p-2)*(p-3)! := by
        rw [show p-2=(p-3)+1 from by omega, Nat.factorial_succ, show (p-3)+1=p-2 from by omega]
      have e3 : (p-3)! = (p-3)*(p-4)! := by
        rw [show p-3=(p-4)+1 from by omega, Nat.factorial_succ, show (p-4)+1=p-3 from by omega]
      have e4 : (p-4)! = (p-4)*(p-5)! := by
        rw [show p-4=(p-5)+1 from by omega, Nat.factorial_succ, show (p-5)+1=p-4 from by omega]
      rw [e1, e2, e3, e4]; ring
    rw [hf]
    push_cast [Nat.cast_sub (show (1:ℕ)≤p by omega), Nat.cast_sub (show (2:ℕ)≤p by omega),
      Nat.cast_sub (show (3:ℕ)≤p by omega), Nat.cast_sub (show (4:ℕ)≤p by omega)]
    rw [ZMod.natCast_self]; ring
  have hmodp : p ∣ (4 * Q1 * Q2 + (p-1)!) := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hcast : ((4*Q1*Q2 + (p-1)! : ℕ) : ZMod p)
        = 4 * (Q1:ZMod p) * (Q2:ZMod p) + ((p-1)!:ZMod p) := by push_cast; ring
    rw [hcast, hQ1p, hQ2p, hfacp]; ring
  obtain ⟨m, hm⟩ := hmodp
  have hzero2 : (p:ZMod (p^2)) * ((4*Q1*Q2:ℕ):ZMod (p^2)) + (p:ZMod (p^2)) * (((p-1)!:ℕ):ZMod (p^2)) = 0 := by
    have hcomb : (p:ZMod (p^2)) * ((4*Q1*Q2:ℕ):ZMod (p^2)) + (p:ZMod (p^2)) * (((p-1)!:ℕ):ZMod (p^2))
        = ((p * (4*Q1*Q2 + (p-1)!) : ℕ):ZMod (p^2)) := by push_cast; ring
    have hpm : (p * (4*Q1*Q2 + (p-1)!) : ℕ) = p^2 * m := by rw [hm]; ring
    rw [hcomb, hpm, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have eqA : (Nat.choose (5*p-5) (p-1) : ZMod (p^2)) * ((p-1)!:ZMod (p^2))
      = (p:ZMod (p^2)) * ((4*Q1*Q2:ℕ):ZMod (p^2)) := by
    have h := congrArg (fun z:ℕ => (z:ZMod (p^2))) hC
    simp only at h
    push_cast at h ⊢
    linear_combination h
  have eqB : (Nat.choose (5*p-5) (p-1) : ZMod (p^2)) * ((p-1)!:ZMod (p^2))
      = -(p:ZMod (p^2)) * ((p-1)!:ZMod (p^2)) := by
    rw [eqA]; linear_combination hzero2
  have hunit : IsUnit (((p-1)! : ℕ):ZMod (p^2)) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
    rw [Nat.Prime.dvd_factorial hp]; omega
  have hsub : ((Nat.choose (5*p-5) (p-1):ZMod (p^2)) - (-(p:ZMod (p^2)))) * ((p-1)!:ZMod (p^2)) = 0 := by
    linear_combination eqB
  exact sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hsub)

/-- If `C ≡ -p (mod p²)` then in `ZMod (p^3)`, `C = p²·a - p` for some natural `a`. -/
lemma lift_negp (p C : ℕ) (h : ((C:ℕ):ZMod (p^2)) = -(p:ZMod (p^2))) :
    ∃ a : ℕ, (C : ZMod (p^3)) = (p:ZMod (p^3))^2 * (a:ZMod (p^3)) - (p:ZMod (p^3)) := by
  have hdvd : p^2 ∣ (C + p) := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [h]; ring
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨a, ?_⟩
  have hcast : ((C + p : ℕ) : ZMod (p^3)) = ((p^2 * a : ℕ) : ZMod (p^3)) := by rw [ha]
  push_cast at hcast
  linear_combination hcast

lemma cc_pm1_raw (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (Nat.choose (2*p-2) (p-1) : ZMod (p^3)) * (Nat.choose (5*p-5) (p-1) : ZMod (p^3))
      = (p:ZMod (p^3))^2 := by
  obtain ⟨a, ha⟩ := lift_negp p _ (C2pm2 p hp hp5)
  obtain ⟨b, hb⟩ := lift_negp p _ (C5pm5 p hp hp5)
  have hp3 : (p:ZMod (p^3))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [ha, hb]
  linear_combination ((p:ZMod (p^3)) * (a:ZMod (p^3)) * (b:ZMod (p^3)) - (a:ZMod (p^3)) - (b:ZMod (p^3))) * hp3

lemma cc_pm1_conn (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ((( ((p-1).choose (p-1))^2 * (((p-1)+(p-1)).choose (p-1)) * ((3*(p-1)+2*(p-1)).choose (p-1)) : ℕ) : ℤ) : ZMod (p^3)) = (p:ZMod (p^3))^2 := by
  have h1 : (p-1).choose (p-1) = 1 := Nat.choose_self _
  have h2 : (p-1)+(p-1) = 2*p-2 := by omega
  have h3 : 3*(p-1)+2*(p-1) = 5*p-5 := by omega
  rw [h1, h2, h3]
  push_cast
  rw [← cc_pm1_raw p hp hp5]
  ring

end CCblock

namespace A374605
open Finset

-- T(p-1,0) = C(3p-3,p-1)
lemma T0_eq (p : ℕ) (hp5 : 5 ≤ p) : T (p-1) 0 = ((Nat.choose (3*p-3) (p-1) : ℕ) : ℤ) := by
  unfold T
  have : 3*(p-1)+2*0 = 3*p-3 := by omega
  rw [this]; simp

-- ℤ identity from T_k_ratio at k=0, after cancelling p:  2(2p-1) T_1 = (p-1)^2 (3p-2)(3p-1) T_0
lemma TII_int (p : ℕ) (hp5 : 5 ≤ p) :
    2*(2*(p:ℤ)-1) * T (p-1) 1 = ((p:ℤ)-1)^2*(3*(p:ℤ)-2)*(3*(p:ℤ)-1) * T (p-1) 0 := by
  have hr := T_k_ratio (p-1) 0 (by omega)
  have hcast : ((p-1:ℕ):ℤ) = (p:ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hr
  have hpne : (p:ℤ) ≠ 0 := by exact_mod_cast hp5.trans_lt' (by norm_num) |>.ne' ; 
  apply mul_left_cancel₀ hpne
  linear_combination hr

-- c k := T(p-1,k) cast to ZMod p^3
noncomputable def cc (p k : ℕ) : ZMod (p^3) := ((T (p-1) k : ℤ) : ZMod (p^3))

-- cast of T_k_ratio at n = p-1
lemma ratioZ (p : ℕ) (hp5 : 5 ≤ p) (k : ℕ) (hk : k ≤ p-1) :
    (((k:ZMod (p^3))+1)^3*(2*(p:ZMod (p^3))+2*k-1)*(2*(p:ZMod (p^3))+2*k)) * cc p (k+1)
      = (((p:ZMod (p^3))-1-k)^2*((p:ZMod (p^3))+k)*(3*(p:ZMod (p^3))+2*k-2)*(3*(p:ZMod (p^3))+2*k-1)) * cc p k := by
  have hr := T_k_ratio (p-1) k hk
  have hc : ((p-1:ℕ):ℤ) = (p:ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hc] at hr
  have := congrArg (fun z : ℤ => (z : ZMod (p^3))) hr
  simp only [cc]
  push_cast at this ⊢
  linear_combination this

lemma c0_eq (p : ℕ) (hp5 : 5 ≤ p) :
    cc p 0 = ((Nat.choose (3*p-3) (p-1) : ℕ) : ZMod (p^3)) := by
  simp only [cc]; rw [T0_eq p hp5]; push_cast; ring
lemma c1_val (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    cc p 1 = (p:ZMod (p^3))*((p:ZMod (p^3))-1)^2 := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have h2u : IsUnit ((2:ℕ):ZMod (p^3)) :=
    (ZMod.isUnit_iff_coprime 2 (p^3)).mpr (Nat.Coprime.pow_right 3 ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)))
  obtain ⟨inv2, hinv2'⟩ : ∃ z : ZMod (p^3), (2:ZMod (p^3))*z = 1 := by
    refine ⟨((2:ℕ):ZMod (p^3))⁻¹, ?_⟩
    rw [show (2:ZMod (p^3)) = ((2:ℕ):ZMod (p^3)) by norm_num]; exact ZMod.mul_inv_of_unit _ h2u
  have hI := itemI hp hp5 inv2 hinv2'
  have hTII : 2*(2*(p:ZMod (p^3))-1) * cc p 1
      = ((p:ZMod (p^3))-1)^2*(3*(p:ZMod (p^3))-2)*(3*(p:ZMod (p^3))-1) * cc p 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod (p^3))) (TII_int p hp5)
    simp only [cc]; push_cast at this ⊢; linear_combination this
  rw [c0_eq p hp5] at hTII
  -- 4(2p-1) is a unit
  have huu : IsUnit (4*(2*(p:ZMod (p^3))-1)) := by
    have hmul : (4*(2*(p:ZMod (p^3))-1)) * (-inv2^2*(1+2*(p:ZMod (p^3))+4*(p:ZMod (p^3))^2)) = 1 := by
      linear_combination (-32*inv2^2)*hp30 + (2*inv2+1)*hinv2'
    exact (Units.mkOfMulEqOne _ _ hmul).isUnit
  apply mulu_cancel huu
  have h2 : 4*(2*(p:ZMod (p^3))-1) * cc p 1
      = ((p:ZMod (p^3))-1)^2*(3*(p:ZMod (p^3))-2)*(3*(p:ZMod (p^3))-1)*(-2*(p:ZMod (p^3))+(p:ZMod (p^3))^2*((p:ZMod (p^3))-5)) := by
    linear_combination 2*hTII + ((p:ZMod (p^3))-1)^2*(3*(p:ZMod (p^3))-2)*(3*(p:ZMod (p^3))-1)*hI
  rw [mul_comm (cc p 1) (4*(2*(p:ZMod (p^3))-1)), h2]
  linear_combination (9*(p:ZMod (p^3))^4 - 72*(p:ZMod (p^3))^3 + 146*(p:ZMod (p^3))^2 - 112*(p:ZMod (p^3)) + 29)*hp30

-- ===== s=1 region invariants =====
lemma huni3 (p m : ℕ) (hp : Nat.Prime p) (h : ¬ p ∣ m) : IsUnit ((m:ℕ):ZMod (p^3)) :=
  (ZMod.isUnit_iff_coprime m (p^3)).mpr
    (Nat.Coprime.pow_right 3 (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr h)))

set_option maxHeartbeats 1600000 in
lemma invA (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (k : ℕ) (hk2 : 2 ≤ k) :
    k ≤ (p+1)/2 →
    2*(k:ZMod (p^3))*((k:ZMod (p^3))-1)*cc p k = 3*(p:ZMod (p^3))^2 := by
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  induction k, hk2 using Nat.le_induction with
  | base =>
    intro _
    have hc1 := c1_val p hp hp5
    have hr1 := ratioZ p hp5 1 (by omega)
    have hA1u : IsUnit ((32*(p:ZMod (p^3))^2 + 48*(p:ZMod (p^3)) + 16) : ZMod (p^3)) := by
      have e1 : (32*(p:ZMod (p^3))^2 + 48*(p:ZMod (p^3)) + 16)
          = (((32*p^2+48*p+16 : ℕ)):ZMod (p^3)) := by push_cast; ring
      rw [e1]; apply huni3 p _ hp
      intro hd
      rw [show (32*p^2+48*p+16) = 16*((2*p+1)*(p+1)) by ring] at hd
      rcases (hp.dvd_mul.mp hd) with h | h
      · have h2 : p ∣ 2 := by
          have h16 : (16:ℕ) = 2^4 := by norm_num
          rw [h16] at h; exact hp.dvd_of_dvd_pow h
        have := Nat.le_of_dvd (by norm_num) h2; omega
      · rcases (hp.dvd_mul.mp h) with h | h
        · have h1 : p ∣ 1 := (Nat.dvd_add_right ⟨2, by ring⟩).mp h
          have := Nat.le_of_dvd (by norm_num) h1; omega
        · have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h
          have := Nat.le_of_dvd (by norm_num) h1; omega
    apply mulu_cancel hA1u
    push_cast at hr1 hc1 ⊢
    linear_combination 4*hr1 + (4*(9*(p:ZMod (p^3))^5 - 24*(p:ZMod (p^3))^4 - 9*(p:ZMod (p^3))^3 + 36*(p:ZMod (p^3))^2 + 12*(p:ZMod (p^3))))*hc1 + (36*(p:ZMod (p^3))^5 - 168*(p:ZMod (p^3))^4 + 192*(p:ZMod (p^3))^3 + 120*(p:ZMod (p^3))^2 - 372*(p:ZMod (p^3)) - 96)*hp30
  | succ k hk2 IH =>
    intro hub
    have hubk : k ≤ (p+1)/2 := by omega
    have IHk := IH hubk
    have hkp : k ≤ p - 1 := by omega
    have hr := ratioZ p hp5 k hkp
    have hUu : IsUnit (((k:ZMod (p^3))-1)*((k:ZMod (p^3))+1)^3*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3))-1)*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3)))) := by
      have e1 : ((k:ZMod (p^3))-1)*((k:ZMod (p^3))+1)^3*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3))-1)*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3)))
          = ((( (k-1)*(k+1)^3*(2*p+2*k-1)*(2*p+2*k) : ℕ)):ZMod (p^3)) := by
        have hk1 : (1:ℕ) ≤ k := by omega
        push_cast [Nat.cast_sub hk1, Nat.cast_sub (show (1:ℕ) ≤ 2*p+2*k by omega)]
        ring
      rw [e1]; apply huni3 p _ hp
      have hb1 : k+1 ≤ (p+1)/2 := hub
      have hkup : 2*k ≤ p - 1 := by omega
      intro hd
      rw [Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp] at hd
      rcases hd with (((h|h)|h)|h)
      · have := Nat.le_of_dvd (by omega) h; omega
      · have h1 : p ∣ (k+1) := hp.dvd_of_dvd_pow h
        have := Nat.le_of_dvd (by omega) h1; omega
      · have h1 : p ∣ (2*k-1) := by
          have he : 2*p+2*k-1 = 2*p + (2*k-1) := by omega
          rw [he] at h
          exact (Nat.dvd_add_right ⟨2, by ring⟩).mp h
        have := Nat.le_of_dvd (by omega) h1; omega
      · have h1 : p ∣ (2*k) := (Nat.dvd_add_right ⟨2, by ring⟩).mp h
        have := Nat.le_of_dvd (by omega) h1; omega
    apply mulu_cancel hUu
    push_cast at hr IHk ⊢
    linear_combination (2*((k:ZMod (p^3))+1)*(k:ZMod (p^3))*((k:ZMod (p^3))-1))*hr + (((k:ZMod (p^3))+1)*(4*(k:ZMod (p^3))^5 + 8*(k:ZMod (p^3))^4*(p:ZMod (p^3)) + 2*(k:ZMod (p^3))^4 - 7*(k:ZMod (p^3))^3*(p:ZMod (p^3))^2 + 21*(k:ZMod (p^3))^3*(p:ZMod (p^3)) - 6*(k:ZMod (p^3))^3 - 17*(k:ZMod (p^3))^2*(p:ZMod (p^3))^3 + 25*(k:ZMod (p^3))^2*(p:ZMod (p^3))^2 - 4*(k:ZMod (p^3))^2*(p:ZMod (p^3)) - 2*(k:ZMod (p^3))^2 + 3*(k:ZMod (p^3))*(p:ZMod (p^3))^4 - 21*(k:ZMod (p^3))*(p:ZMod (p^3))^3 + 31*(k:ZMod (p^3))*(p:ZMod (p^3))^2 - 15*(k:ZMod (p^3))*(p:ZMod (p^3)) + 2*(k:ZMod (p^3)) + 9*(p:ZMod (p^3))^5 - 27*(p:ZMod (p^3))^4 + 29*(p:ZMod (p^3))^3 - 13*(p:ZMod (p^3))^2 + 2*(p:ZMod (p^3))))*IHk + (3*(-11*(k:ZMod (p^3))^4*(p:ZMod (p^3)) + 15*(k:ZMod (p^3))^4 - 17*(k:ZMod (p^3))^3*(p:ZMod (p^3))^2 + 10*(k:ZMod (p^3))^3*(p:ZMod (p^3)) + 21*(k:ZMod (p^3))^3 + 3*(k:ZMod (p^3))^2*(p:ZMod (p^3))^3 - 38*(k:ZMod (p^3))^2*(p:ZMod (p^3))^2 + 56*(k:ZMod (p^3))^2*(p:ZMod (p^3)) - 3*(k:ZMod (p^3))^2 + 9*(k:ZMod (p^3))*(p:ZMod (p^3))^4 - 24*(k:ZMod (p^3))*(p:ZMod (p^3))^3 + 8*(k:ZMod (p^3))*(p:ZMod (p^3))^2 + 26*(k:ZMod (p^3))*(p:ZMod (p^3)) - 9*(k:ZMod (p^3)) + 9*(p:ZMod (p^3))^4 - 27*(p:ZMod (p^3))^3 + 29*(p:ZMod (p^3))^2 - 9*(p:ZMod (p^3))))*hp30

-- ===== cc(p-1) = p^2 and region-B invariant =====

lemma cc_pm1 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    cc p (p-1) = (p:ZMod (p^3))^2 := by
  show ((T (p-1) (p-1) : ℤ) : ZMod (p^3)) = (p:ZMod (p^3))^2
  exact cc_pm1_conn p hp hp5

set_option maxHeartbeats 1600000 in
lemma invB (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (k : ℕ)
    (hklo : (p+1)/2 + 1 ≤ k) (hkhi : k ≤ p-1) :
    (k:ZMod (p^3))*((k:ZMod (p^3))-1)*cc p k = 2*(p:ZMod (p^3))^2 := by
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have key : ∀ j k, k + j = p-1 → (p+1)/2 + 1 ≤ k →
      (k:ZMod (p^3))*((k:ZMod (p^3))-1)*cc p k = 2*(p:ZMod (p^3))^2 := by
    intro j
    induction j with
    | zero =>
      intro k hk hlo
      have hkp : k = p-1 := by omega
      subst hkp
      have hcc := cc_pm1 p hp hp5
      have hcast : ((p-1:ℕ):ZMod (p^3)) = (p:ZMod (p^3)) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast, hcc]
      linear_combination ((p:ZMod (p^3)) - 3) * hp30
    | succ j IH =>
      intro k hk hlo
      have hk1 : (k+1) + j = p-1 := by omega
      have hlo1 : (p+1)/2 + 1 ≤ k+1 := by omega
      have IHk := IH (k+1) hk1 hlo1
      have hkp : k ≤ p - 1 := by omega
      have hr := ratioZ p hp5 k hkp
      have hRu : IsUnit (((p:ZMod (p^3))-1-(k:ZMod (p^3)))^2*((p:ZMod (p^3))+(k:ZMod (p^3)))*(3*(p:ZMod (p^3))+2*(k:ZMod (p^3))-2)*(3*(p:ZMod (p^3))+2*(k:ZMod (p^3))-1)) := by
        have e1 : ((p:ZMod (p^3))-1-(k:ZMod (p^3)))^2*((p:ZMod (p^3))+(k:ZMod (p^3)))*(3*(p:ZMod (p^3))+2*(k:ZMod (p^3))-2)*(3*(p:ZMod (p^3))+2*(k:ZMod (p^3))-1)
            = ((( (p-1-k)^2*(p+k)*(3*p+2*k-2)*(3*p+2*k-1) : ℕ)):ZMod (p^3)) := by
          push_cast [Nat.cast_sub (show (1:ℕ) ≤ p by omega), Nat.cast_sub (show k ≤ p-1 by omega),
            Nat.cast_sub (show (2:ℕ) ≤ 3*p+2*k by omega), Nat.cast_sub (show (1:ℕ) ≤ 3*p+2*k by omega)]
          ring
        rw [e1]; apply huni3 p _ hp
        intro hd
        rw [Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp] at hd
        rcases hd with (((h|h)|h)|h)
        · have hh := hp.dvd_of_dvd_pow h
          have := Nat.le_of_dvd (by omega) hh; omega
        · have hk0 : p ∣ k := (Nat.dvd_add_right (dvd_refl p)).mp h
          have := Nat.le_of_dvd (by omega) hk0; omega
        · have he : 3*p+2*k-2 = 3*p + (2*k-2) := by omega
          rw [he] at h
          have h2 : p ∣ (2*k-2) := (Nat.dvd_add_right (dvd_mul_left p 3)).mp h
          have h3 : p ∣ (2*k-2-p) := Nat.dvd_sub h2 (dvd_refl p)
          have := Nat.le_of_dvd (by omega) h3; omega
        · have he : 3*p+2*k-1 = 3*p + (2*k-1) := by omega
          rw [he] at h
          have h2 : p ∣ (2*k-1) := (Nat.dvd_add_right (dvd_mul_left p 3)).mp h
          have h3 : p ∣ (2*k-1-p) := Nat.dvd_sub h2 (dvd_refl p)
          have := Nat.le_of_dvd (by omega) h3; omega
      apply mulu_cancel hRu
      push_cast at hr IHk ⊢
      linear_combination (-(k:ZMod (p^3))*((k:ZMod (p^3))-1))*hr
        + (((k:ZMod (p^3))-1)*((k:ZMod (p^3))+1)^2*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3))-1)*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3))))*IHk
        + (22*(k:ZMod (p^3))^3*(p:ZMod (p^3)) - 30*(k:ZMod (p^3))^3 + 34*(k:ZMod (p^3))^2*(p:ZMod (p^3))^2 - 42*(k:ZMod (p^3))^2*(p:ZMod (p^3)) - 12*(k:ZMod (p^3))^2 - 6*(k:ZMod (p^3))*(p:ZMod (p^3))^3 + 42*(k:ZMod (p^3))*(p:ZMod (p^3))^2 - 70*(k:ZMod (p^3))*(p:ZMod (p^3)) + 18*(k:ZMod (p^3)) - 18*(p:ZMod (p^3))^4 + 54*(p:ZMod (p^3))^3 - 58*(p:ZMod (p^3))^2 + 18*(p:ZMod (p^3)))*hp30
  exact key (p-1-k) k (by omega) hklo

-- ===== s=1 telescoping sum =====

lemma ccA_tele (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (k : ℕ)
    (hk2 : 2 ≤ k) (hkM : k ≤ (p+1)/2) :
    cc p k = 3*(p:ZMod (p^3))^2 * (2:ZMod (p^3))⁻¹ *
      (((k-1:ℕ):ZMod (p^3))⁻¹ - ((k:ℕ):ZMod (p^3))⁻¹) := by
  have hkp1 : k ≤ p - 1 := by omega
  have hpk : ¬ p ∣ k := by intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hpk1 : ¬ p ∣ (k-1) := by intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hp2 : ¬ p ∣ 2 := by intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have huk : IsUnit ((k:ZMod (p^3))) := huni3 p k hp hpk
  have huk1 : IsUnit (((k-1:ℕ)):ZMod (p^3)) := huni3 p (k-1) hp hpk1
  have hu2 : IsUnit ((2:ZMod (p^3))) := by have := huni3 p 2 hp hp2; simpa using this
  have m_k : (k:ZMod (p^3)) * (k:ZMod (p^3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have m_k1 : ((k-1:ℕ):ZMod (p^3)) * ((k-1:ℕ):ZMod (p^3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk1
  have m_2 : (2:ZMod (p^3)) * (2:ZMod (p^3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu2
  have hk1cast : ((k-1:ℕ):ZMod (p^3)) = (k:ZMod (p^3)) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hA := invA p hp hp5 k hk2 hkM
  have hKK : (k:ZMod (p^3)) * ((k-1:ℕ):ZMod (p^3)) *
      (((k-1:ℕ):ZMod (p^3))⁻¹ - (k:ZMod (p^3))⁻¹) = 1 := by
    have expand : (k:ZMod (p^3)) * ((k-1:ℕ):ZMod (p^3)) *
        (((k-1:ℕ):ZMod (p^3))⁻¹ - (k:ZMod (p^3))⁻¹)
        = (k:ZMod (p^3)) * (((k-1:ℕ):ZMod (p^3)) * ((k-1:ℕ):ZMod (p^3))⁻¹)
          - ((k-1:ℕ):ZMod (p^3)) * ((k:ZMod (p^3)) * (k:ZMod (p^3))⁻¹) := by ring
    rw [expand, m_k, m_k1, hk1cast]; ring
  have hUu : IsUnit (2*(k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3))) := (hu2.mul huk).mul huk1
  apply mulu_cancel hUu
  have hL : cc p k * (2*(k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3))) = 3*(p:ZMod (p^3))^2 := by
    have e : cc p k * (2*(k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3)))
        = 2*(k:ZMod (p^3))*((k:ZMod (p^3))-1)*cc p k := by rw [hk1cast]; ring
    rw [e]; exact hA
  have hR : (3*(p:ZMod (p^3))^2 * (2:ZMod (p^3))⁻¹ *
      (((k-1:ℕ):ZMod (p^3))⁻¹ - ((k:ℕ):ZMod (p^3))⁻¹)) * (2*(k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3)))
      = 3*(p:ZMod (p^3))^2 := by
    have e : (3*(p:ZMod (p^3))^2 * (2:ZMod (p^3))⁻¹ *
        (((k-1:ℕ):ZMod (p^3))⁻¹ - ((k:ℕ):ZMod (p^3))⁻¹)) * (2*(k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3)))
        = 3*(p:ZMod (p^3))^2 * ((2:ZMod (p^3))*(2:ZMod (p^3))⁻¹) *
          ((k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3))*(((k-1:ℕ):ZMod (p^3))⁻¹ - (k:ZMod (p^3))⁻¹)) := by ring
    rw [e, m_2, hKK]; ring
  rw [hL, hR]

lemma ccB_tele (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (k : ℕ)
    (hklo : (p+1)/2+1 ≤ k) (hkhi : k ≤ p-1) :
    cc p k = 2*(p:ZMod (p^3))^2 * (((k-1:ℕ):ZMod (p^3))⁻¹ - ((k:ℕ):ZMod (p^3))⁻¹) := by
  have hpk : ¬ p ∣ k := by intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hpk1 : ¬ p ∣ (k-1) := by intro h; have := Nat.le_of_dvd (by omega) h; omega
  have huk : IsUnit ((k:ZMod (p^3))) := huni3 p k hp hpk
  have huk1 : IsUnit (((k-1:ℕ)):ZMod (p^3)) := huni3 p (k-1) hp hpk1
  have m_k : (k:ZMod (p^3)) * (k:ZMod (p^3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
  have m_k1 : ((k-1:ℕ):ZMod (p^3)) * ((k-1:ℕ):ZMod (p^3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk1
  have hk1cast : ((k-1:ℕ):ZMod (p^3)) = (k:ZMod (p^3)) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hB := invB p hp hp5 k hklo hkhi
  have hKK : (k:ZMod (p^3)) * ((k-1:ℕ):ZMod (p^3)) *
      (((k-1:ℕ):ZMod (p^3))⁻¹ - (k:ZMod (p^3))⁻¹) = 1 := by
    have expand : (k:ZMod (p^3)) * ((k-1:ℕ):ZMod (p^3)) *
        (((k-1:ℕ):ZMod (p^3))⁻¹ - (k:ZMod (p^3))⁻¹)
        = (k:ZMod (p^3)) * (((k-1:ℕ):ZMod (p^3)) * ((k-1:ℕ):ZMod (p^3))⁻¹)
          - ((k-1:ℕ):ZMod (p^3)) * ((k:ZMod (p^3)) * (k:ZMod (p^3))⁻¹) := by ring
    rw [expand, m_k, m_k1, hk1cast]; ring
  have hUu : IsUnit ((k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3))) := huk.mul huk1
  apply mulu_cancel hUu
  have hL : cc p k * ((k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3))) = 2*(p:ZMod (p^3))^2 := by
    have e : cc p k * ((k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3)))
        = (k:ZMod (p^3))*((k:ZMod (p^3))-1)*cc p k := by rw [hk1cast]; ring
    rw [e]; exact hB
  have hR : (2*(p:ZMod (p^3))^2 * (((k-1:ℕ):ZMod (p^3))⁻¹ - ((k:ℕ):ZMod (p^3))⁻¹)) * ((k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3)))
      = 2*(p:ZMod (p^3))^2 := by
    have e : (2*(p:ZMod (p^3))^2 * (((k-1:ℕ):ZMod (p^3))⁻¹ - ((k:ℕ):ZMod (p^3))⁻¹)) * ((k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3)))
        = 2*(p:ZMod (p^3))^2 * ((k:ZMod (p^3))*((k-1:ℕ):ZMod (p^3))*(((k-1:ℕ):ZMod (p^3))⁻¹ - (k:ZMod (p^3))⁻¹)) := by ring
    rw [e, hKK]; ring
  rw [hL, hR]

lemma sumA (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (m : ℕ) (hm2 : 2 ≤ m) :
    m ≤ (p+1)/2 →
    ∑ k ∈ Finset.Icc 2 m, cc p k
      = 3*(p:ZMod (p^3))^2*(2:ZMod (p^3))⁻¹*(1 - ((m:ℕ):ZMod (p^3))⁻¹) := by
  induction m, hm2 using Nat.le_induction with
  | base =>
    intro hmM
    rw [show Finset.Icc 2 2 = {2} from by ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega,
      Finset.sum_singleton, ccA_tele p hp hp5 2 (le_refl 2) hmM]
    norm_num
  | succ m hm IH =>
    intro hmM
    have IHm := IH (by omega)
    rw [show Finset.Icc 2 (m+1) = insert (m+1) (Finset.Icc 2 m) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), IHm,
      ccA_tele p hp hp5 (m+1) (by omega) hmM, show (m+1-1) = m from by omega]
    ring

lemma sumB (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (m : ℕ) (hmlo : (p+1)/2+1 ≤ m) :
    m ≤ p-1 →
    ∑ k ∈ Finset.Icc ((p+1)/2+1) m, cc p k
      = 2*(p:ZMod (p^3))^2*((((p+1)/2:ℕ):ZMod (p^3))⁻¹ - ((m:ℕ):ZMod (p^3))⁻¹) := by
  induction m, hmlo using Nat.le_induction with
  | base =>
    intro hmhi
    rw [show Finset.Icc ((p+1)/2+1) ((p+1)/2+1) = {(p+1)/2+1} from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega,
      Finset.sum_singleton, ccB_tele p hp hp5 ((p+1)/2+1) (le_refl _) hmhi,
      show ((p+1)/2+1-1) = (p+1)/2 from by omega]
  | succ m hm IH =>
    intro hmhi
    have IHm := IH (by omega)
    rw [show Finset.Icc ((p+1)/2+1) (m+1) = insert (m+1) (Finset.Icc ((p+1)/2+1) m) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), IHm,
      ccB_tele p hp hp5 (m+1) (by omega) hmhi, show (m+1-1) = m from by omega]
    ring

set_option maxHeartbeats 1000000 in
lemma sum_zero (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.range p, cc p k = 0 := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  -- decomposition
  have hdecomp : ∑ k ∈ Finset.range p, cc p k
      = cc p 0 + cc p 1 + (∑ k ∈ Finset.Icc 2 ((p+1)/2), cc p k)
        + (∑ k ∈ Finset.Icc ((p+1)/2+1) (p-1), cc p k) := by
    have e1 : Finset.range p = (Finset.Icc 0 1 ∪ Finset.Icc 2 ((p+1)/2)) ∪ Finset.Icc ((p+1)/2+1) (p-1) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
    have hdAB : Disjoint (Finset.Icc 0 1) (Finset.Icc 2 ((p+1)/2)) := by
      rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_Icc] at hx hy; omega
    have hdC : Disjoint (Finset.Icc 0 1 ∪ Finset.Icc 2 ((p+1)/2)) (Finset.Icc ((p+1)/2+1) (p-1)) := by
      rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_union, Finset.mem_Icc] at hx hy; omega
    rw [e1, Finset.sum_union hdC, Finset.sum_union hdAB,
      show Finset.Icc 0 1 = ({0, 1} : Finset ℕ) from by ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega,
      Finset.sum_pair (by norm_num)]
  have hSA := sumA p hp hp5 ((p+1)/2) (by omega) (le_refl _)
  have hSB := sumB p hp hp5 (p-1) (by omega) (le_refl _)
  -- mod p facts
  have hp2 : ¬ p ∣ 2 := by intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have h2u : IsUnit (2:ZMod (p^3)) := by have := huni3 p 2 hp hp2; simpa using this
  have hinv2 : (2:ZMod (p^3)) * (2:ZMod (p^3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2u
  have hc1 := c1_val p hp hp5
  have hI : 2 * cc p 0 = -2*(p:ZMod (p^3))+(p:ZMod (p^3))^2*((p:ZMod (p^3))-5) := by
    rw [c0_eq p hp5]; exact itemI hp hp5 _ hinv2
  -- hii
  have hMu : IsUnit (((p+1)/2 : ℕ):ZMod (p^3)) := huni3 p ((p+1)/2) hp (by
    intro h; have := Nat.le_of_dvd (by omega) h; omega)
  have hMinv : (((p+1)/2:ℕ):ZMod (p^3)) * (((p+1)/2:ℕ):ZMod (p^3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hMu
  have hM2 : (2:ZMod (p^3)) * (((p+1)/2:ℕ):ZMod (p^3)) = (p:ZMod (p^3))+1 := by
    have h2M : 2*((p+1)/2) = p+1 := by omega
    have hc := congrArg (fun z:ℕ => (z:ZMod (p^3))) h2M
    push_cast at hc; linear_combination hc
  have hii : (p:ZMod (p^3))^2 * (((p+1)/2:ℕ):ZMod (p^3))⁻¹ = 2*(p:ZMod (p^3))^2 := by
    linear_combination (-(p:ZMod (p^3))^2 * (((p+1)/2:ℕ):ZMod (p^3))⁻¹)*hM2
      + (2*(p:ZMod (p^3))^2)*hMinv + (-(((p+1)/2:ℕ):ZMod (p^3))⁻¹)*hp30
  -- hiii
  have hp1u : IsUnit (((p-1:ℕ)):ZMod (p^3)) := huni3 p (p-1) hp (by
    intro h; have := Nat.le_of_dvd (by omega) h; omega)
  have hp1inv : ((p-1:ℕ):ZMod (p^3)) * ((p-1:ℕ):ZMod (p^3))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hp1u
  have hp1cast : ((p-1:ℕ):ZMod (p^3)) = (p:ZMod (p^3)) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hgp1 : ((p-1:ℕ):ZMod (p^3))⁻¹ = -(1+(p:ZMod (p^3))+(p:ZMod (p^3))^2) := by
    have h2 : ((p-1:ℕ):ZMod (p^3)) * (-(1+(p:ZMod (p^3))+(p:ZMod (p^3))^2)) = 1 := by
      rw [hp1cast]; linear_combination -hp30
    apply mulu_cancel hp1u
    rw [mul_comm (((p-1:ℕ):ZMod (p^3))⁻¹) (((p-1:ℕ):ZMod (p^3))), hp1inv,
      mul_comm (-(1+(p:ZMod (p^3))+(p:ZMod (p^3))^2)) (((p-1:ℕ):ZMod (p^3))), h2]
  have hiii : (p:ZMod (p^3))^2 * ((p-1:ℕ):ZMod (p^3))⁻¹ = -(p:ZMod (p^3))^2 := by
    rw [hgp1]; linear_combination (-(1+(p:ZMod (p^3))))*hp30
  -- conclude
  apply mulu_cancel h2u
  rw [hdecomp, hSA, hSB]
  linear_combination hI + 2*hc1
    + (3*(p:ZMod (p^3))^2*(1-(((p+1)/2:ℕ):ZMod (p^3))⁻¹))*hinv2
    + hii + (-4)*hiii + 3*hp30

lemma aSeq_dvd_pm1 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (p^3:ℤ) ∣ aSeq (p-1) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have h0 : ((aSeq (p-1):ℤ):ZMod (p^3)) = 0 := by
    have heq : ((aSeq (p-1):ℤ):ZMod (p^3)) = ∑ k ∈ Finset.range p, cc p k := by
      rw [aSeq, show (p-1)+1 = p from by omega, Int.cast_sum]
      rfl
    rw [heq]; exact sum_zero p hp hp5
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
