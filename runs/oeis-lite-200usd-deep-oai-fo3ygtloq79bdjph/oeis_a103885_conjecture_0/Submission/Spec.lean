import FormalConjectures.Util.ProblemImports
open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate
def A103885 (n:ℕ):ℕ :=
  if n = 0 then 1
  else
    let r:ℕ:= n - 1
    (range (n + 1)).sum (fun k=> (n.choose k) * ((2 * n + k - 1).choose r))
noncomputable def A103885_subsequence_real (m n:ℕ):ℝ :=
  (A103885 (m * n):ℝ)
open BigOperators
def a0 (m:ℕ):Finset ℕ :=
  Finset.Ioc 0 (2 * m)
noncomputable def prod_factor_plus (m n:ℕ):ℝ :=
  (a0 m).prod fun k =>
    ((2 * m * n:ℝ) + (k:ℝ))
noncomputable def prod_factor_minus (m n:ℕ):ℝ :=
  (a0 m).prod fun k =>
    ((2 * m * n:ℝ) - (k:ℝ))
namespace N0
opaque a1 (n:ℕ) :
    (2*n+1)*(2*n+2)*((3*n+2).choose n) =
    (3*n+1)*(3*n+2)*((3*n).choose n):= by
  have h1:= Nat.choose_mul_succ_eq (3*n) n
  have h1':(3*n).choose n * (3*n+1) = (3*n+1).choose n * (2*n+1):= by
    convert h1 using 2 <;> omega
  have h2:= Nat.choose_mul_succ_eq (3*n+1) n
  have h2':(3*n+1).choose n * (3*n+2) = (3*n+2).choose n * (2*n+2):= by
    convert h2 using 2 <;> omega
  calc
    (2*n+1)*(2*n+2)*((3*n+2).choose n)
        = (2*n+1)*(((3*n+2).choose n)*(2*n+2)):= by ring
    _ = (2*n+1)*(((3*n+1).choose n)*(3*n+2)):= by rw [← h2']
    _ = (((3*n+1).choose n)*(2*n+1))*(3*n+2):= by ring
    _ = (((3*n).choose n)*(3*n+1))*(3*n+2):= by rw [← h1']
    _ = (3*n+1)*(3*n+2)*((3*n).choose n):= by ring
opaque a2 (n:ℕ) :
    (2*n+1)*(2*n+2)*(5*n^2-5*n+1)*((3*n+2).choose n) =
    (3*n+1)*(3*n+2)*(5*n^2-5*n+1)*((3*n).choose n):= by
  have h:= a1 n
  calc
    (2*n+1)*(2*n+2)*(5*n^2-5*n+1)*((3*n+2).choose n)
        = ((2*n+1)*(2*n+2)*((3*n+2).choose n))*(5*n^2-5*n+1):= by ring
    _ = ((3*n+1)*(3*n+2)*((3*n).choose n))*(5*n^2-5*n+1):= by rw [h]
    _ = (3*n+1)*(3*n+2)*(5*n^2-5*n+1)*((3*n).choose n):= by ring
def F (n k:ℕ):ℕ :=
  n.choose k * ((2 * n + k - 1).choose (n - 1))
opaque a3 (n:ℕ) :
    (2*n+1)*(2*n+2)*(5*n^2-5*n+1) * F (n+1) (n+1) =
    (3*n+1)*(3*n+2)*(5*n^2-5*n+1) * ((3*n).choose n):= by
  unfold F
  rw [Nat.choose_self]
  have hchoose:(2 * (n + 1) + (n + 1) - 1).choose (n + 1 - 1) = (3*n+2).choose n:= by
    congr <;> omega
  rw [hchoose]
  simp only [one_mul]
  exact a2 n
opaque a4 (n k:ℕ) (h:n < k):F n k = 0:= by
  unfold F
  rw [Nat.choose_eq_zero_of_lt h,zero_mul]
opaque a5 (n k:ℕ) (hn:1 ≤ n) (hk:k ≤ n) :
    (F (n+1) k:ℚ) * ((n+1-k:ℕ):ℚ) * (n:ℚ) * ((n+k+1:ℕ):ℚ) =
    (F n k:ℚ) * ((n+1:ℕ):ℚ) * ((2*n+k:ℕ):ℚ) * ((2*n+k+1:ℕ):ℚ):= by
  unfold F
  have hchoose1:= Nat.choose_mul_succ_eq n k
  have hchoose1q:((n.choose k:ℕ):ℚ) * (n+1:ℚ) =
      (((n+1).choose k:ℕ):ℚ) * ((n+1-k:ℕ):ℚ):= by
    exact_mod_cast hchoose1
  have hA:= Nat.choose_mul_succ_eq (2*n+k-1) (n-1)
  have hAq:((((2*n+k-1).choose (n-1):ℕ):ℚ) * ((2*n+k:ℕ):ℚ)) =
      (((2*n+k).choose (n-1):ℕ):ℚ) * ((n+k+1:ℕ):ℚ):= by
    have hN:2*n+k-1 + 1 = 2*n+k:= by omega
    have hsub:2*n+k - (n-1) = n+k+1:= by omega
    exact_mod_cast (by simpa [hN,hsub] using hA)
  have hB:= Nat.choose_succ_right_eq (2*n+k) (n-1)
  have hBq:((((2*n+k).choose n:ℕ):ℚ) * (n:ℚ)) =
      (((2*n+k).choose (n-1):ℕ):ℚ) * ((n+k+1:ℕ):ℚ):= by
    have hn1:n - 1 + 1 = n:= by omega
    have hsub:2*n+k - (n-1) = n+k+1:= by omega
    exact_mod_cast (by simpa [hn1,hsub] using hB)
  have hD:= Nat.choose_mul_succ_eq (2*n+k) n
  have hDq:((((2*n+k).choose n:ℕ):ℚ) * ((2*n+k+1:ℕ):ℚ)) =
      (((2*n+k+1).choose n:ℕ):ℚ) * ((n+k+1:ℕ):ℚ):= by
    have hsub:2*n+k+1 - n = n+k+1:= by omega
    exact_mod_cast (by simpa [hsub] using hD)
  have hCq:((((2*(n+1)+k-1).choose ((n+1)-1):ℕ):ℚ) * (n:ℚ) * ((n+k+1:ℕ):ℚ)) =
      (((2*n+k-1).choose (n-1):ℕ):ℚ) * ((2*n+k:ℕ):ℚ) * ((2*n+k+1:ℕ):ℚ):= by
    have hidx1:2*(n+1)+k-1 = 2*n+k+1:= by omega
    have hidx2:(n+1)-1 = n:= by omega
    rw [hidx1,hidx2]
    rw [show (↑((2 * n + k + 1).choose n) * ↑n * ↑(n + k + 1):ℚ) =
      (↑((2 * n + k + 1).choose n) * ↑(n + k + 1)) * ↑n by ring]
    rw [← hDq]
    rw [show (↑((2 * n + k).choose n) * ↑(2 * n + k + 1) * ↑n:ℚ) =
      (↑((2 * n + k).choose n) * ↑n) * ↑(2 * n + k + 1) by ring]
    rw [hBq]
    rw [← hAq]
  norm_num [Nat.cast_mul]
  rw [show ↑((n + 1).choose k) * ↑((2 * (n + 1) + k - 1).choose n) * ↑(n + 1 - k) * ↑n * (↑n + ↑k + 1:ℚ)
      = (↑((n + 1).choose k) * ↑(n + 1 - k)) *
        (↑((2 * (n + 1) + k - 1).choose n) * ↑n * (↑n + ↑k + 1)) by ring]
  rw [← hchoose1q]
  have hCq':(↑((2 * (n + 1) + k - 1).choose n) * ↑n * (↑n + ↑k + 1):ℚ) =
      ↑((2 * n + k - 1).choose (n - 1)) * (2 * ↑n + ↑k) * (2 * ↑n + ↑k + 1):= by
    simpa [Nat.cast_add,Nat.cast_mul] using hCq
  rw [hCq']
  ring
opaque a6 (n k:ℕ) (hn:2 ≤ n) (hk:k ≤ n-1) :
    (F (n-1) k:ℚ) * (n:ℚ) * ((2*n+k-1:ℕ):ℚ) * ((2*n+k-2:ℕ):ℚ) =
    (F n k:ℚ) * ((n-k:ℕ):ℚ) * ((n-1:ℕ):ℚ) * ((n+k:ℕ):ℚ):= by
  unfold F
  have hchoose1:= Nat.choose_mul_succ_eq (n-1) k
  have hchoose1q:((((n-1).choose k:ℕ):ℚ) * (n:ℚ)) = (((n).choose k:ℕ):ℚ) * ((n-k:ℕ):ℚ):= by
    have hn1:n - 1 + 1 = n:= by omega
    have hsub:n - k = n - 1 + 1 - k:= by omega
    exact_mod_cast (by simpa [hn1,hsub] using hchoose1)
  have hA:= Nat.choose_mul_succ_eq (2*n+k-3) (n-2)
  have hAq:((((2*n+k-3).choose (n-2):ℕ):ℚ) * ((2*n+k-2:ℕ):ℚ)) =
      (((2*n+k-2).choose (n-2):ℕ):ℚ) * ((n+k:ℕ):ℚ):= by
    have hN:2*n+k-3 + 1 = 2*n+k-2:= by omega
    have hsub:2*n+k-2 - (n-2) = n+k:= by omega
    exact_mod_cast (by simpa [hN,hsub] using hA)
  have hB:= Nat.choose_succ_right_eq (2*n+k-2) (n-2)
  have hBq:((((2*n+k-2).choose (n-1):ℕ):ℚ) * ((n-1:ℕ):ℚ)) =
      (((2*n+k-2).choose (n-2):ℕ):ℚ) * ((n+k:ℕ):ℚ):= by
    have hn1:n - 2 + 1 = n - 1:= by omega
    have hsub:2*n+k-2 - (n-2) = n+k:= by omega
    exact_mod_cast (by simpa [hn1,hsub] using hB)
  have hD:= Nat.choose_mul_succ_eq (2*n+k-2) (n-1)
  have hDq:((((2*n+k-2).choose (n-1):ℕ):ℚ) * ((2*n+k-1:ℕ):ℚ)) =
      (((2*n+k-1).choose (n-1):ℕ):ℚ) * ((n+k:ℕ):ℚ):= by
    have hN:2*n+k-2 + 1 = 2*n+k-1:= by omega
    have hsub:2*n+k-1 - (n-1) = n+k:= by omega
    rw [hN] at hD
    exact_mod_cast (by simpa [hsub] using hD)
  have hCq:((((2*(n-1)+k-1).choose ((n-1)-1):ℕ):ℚ) * ((2*n+k-1:ℕ):ℚ) * ((2*n+k-2:ℕ):ℚ)) =
      (((2*n+k-1).choose (n-1):ℕ):ℚ) * ((n-1:ℕ):ℚ) * ((n+k:ℕ):ℚ):= by
    have hidx1:2*(n-1)+k-1 = 2*n+k-3:= by omega
    have hidx2:(n-1)-1 = n-2:= by omega
    rw [hidx1,hidx2]
    rw [show (↑((2 * n + k - 1).choose (n - 1)) * ↑(n - 1) * ↑(n + k):ℚ) =
      (↑((2 * n + k - 1).choose (n - 1)) * ↑(n + k)) * ↑(n - 1) by ring]
    rw [← hDq]
    rw [show (↑((2 * n + k - 2).choose (n - 1)) * ↑(2 * n + k - 1) * ↑(n - 1):ℚ) =
      (↑((2 * n + k - 2).choose (n - 1)) * ↑(n - 1)) * ↑(2 * n + k - 1) by ring]
    rw [hBq]
    rw [← hAq]
    ring
  norm_num [Nat.cast_mul]
  rw [show (↑((n - 1).choose k) * ↑((2 * (n - 1) + k - 1).choose (n - 1 - 1)) * ↑n * ↑(2 * n + k - 1) * ↑(2 * n + k - 2):ℚ)
      = (↑((n - 1).choose k) * ↑n) * (↑((2 * (n - 1) + k - 1).choose (n - 1 - 1)) * ↑(2 * n + k - 1) * ↑(2 * n + k - 2)) by ring]
  rw [hchoose1q]
  have hCq':(↑((2 * (n - 1) + k - 1).choose (n - 1 - 1)) * ↑(2 * n + k - 1) * ↑(2 * n + k - 2):ℚ) =
      ↑((2 * n + k - 1).choose (n - 1)) * ↑(n - 1) * ↑(n + k):= by
    simpa [Nat.cast_add,Nat.cast_mul] using hCq
  rw [hCq']
  rw [Nat.cast_add]
  ring
opaque a7 (n k:ℕ) (hn:1 ≤ n) (hk:k < n) :
    (F n (k+1):ℚ) * (((k+1:ℕ):ℚ)) * (((n+k+1:ℕ):ℚ)) =
    (F n k:ℚ) * (((n-k:ℕ):ℚ)) * (((2*n+k:ℕ):ℚ)):= by
  unfold F
  have hchoose1:= Nat.choose_succ_right_eq n k
  have hchoose1q:(((n.choose (k+1):ℕ):ℚ) * (((k+1:ℕ):ℚ))) =
      (((n.choose k:ℕ):ℚ) * (((n-k:ℕ):ℚ))):= by
    exact_mod_cast hchoose1
  have hchoose2:= Nat.choose_mul_succ_eq (2*n+k-1) (n-1)
  have hchoose2q:((((2*n+k-1).choose (n-1):ℕ):ℚ) * (((2*n+k:ℕ):ℚ))) =
      ((((2*n+k).choose (n-1):ℕ):ℚ) * (((n+k+1:ℕ):ℚ))):= by
    have hN:2*n+k-1 + 1 = 2*n+k:= by omega
    have hsub:2*n+k - (n-1) = n+k+1:= by omega
    exact_mod_cast (by simpa [hN,hsub] using hchoose2)
  have hidx:2*n+(k+1)-1 = 2*n+k:= by omega
  norm_num [Nat.cast_mul]
  rw [show (↑(n.choose (k + 1)) * ↑((2 * n + k).choose (n - 1)) * (↑k + 1) * (↑n + ↑k + 1):ℚ)
      = (↑(n.choose (k + 1)) * ↑(k + 1)) * (↑((2 * n + k).choose (n - 1)) * (↑n + ↑k + 1)) by simp only [Nat.cast_add,Nat.cast_one]; ring]
  rw [show (↑(n.choose k) * ↑((2 * n + k - 1).choose (n - 1)) * ↑(n - k) * (2 * ↑n + ↑k):ℚ)
      = (↑(n.choose k) * ↑(n - k)) * (↑((2 * n + k - 1).choose (n - 1)) * (2 * ↑n + ↑k)) by ring]
  rw [hchoose1q]
  have hchoose2q':(↑((2 * n + k).choose (n - 1)) * (↑n + ↑k + 1):ℚ) =
      ↑((2 * n + k - 1).choose (n - 1)) * (2 * ↑n + ↑k):= by
    simpa [Nat.cast_add,Nat.cast_mul] using hchoose2q.symm
  rw [hchoose2q']
def A (n:ℚ):ℚ :=
  (2 * n + 1) * (2 * n + 2) * (5 * n^2 - 5 * n + 1)
def B (n:ℚ):ℚ :=
  4 * (55 * n^4 - 34 * n^2 + 3)
def D (n:ℚ):ℚ :=
  (2 * n - 1) * (2 * n - 2) * (5 * n^2 + 5 * n + 1)
def a8 (n k:ℚ):ℚ :=
  k^2 * (110*n^5 + 30*n^4 - 68*n^3 - 20*n^2 + 6*n + 2)
  + k * (410*n^6 - 260*n^5 - 258*n^4 + 150*n^3 + 30*n^2 - 10*n - 2)
  + (290*n^7 - 265*n^6 - 187*n^5 + 138*n^4 + 33*n^3 - 5*n^2 - 4*n)
def R (n k:ℚ):ℚ :=
  k * a8 n k /
    (n * (k - n - 1) * (k + 2*n - 2) * (k + 2*n - 1))
def a9 (n k:ℚ):ℚ :=
  ((n + 1) * (2*n + k) * (2*n + k + 1)) /
    ((n + 1 - k) * n * (n + k + 1))
def a10 (n k:ℚ):ℚ :=
  ((n - k) * (n - 1) * (n + k)) /
    (n * (2*n + k - 1) * (2*n + k - 2))
def a11 (n k:ℚ):ℚ :=
  ((n - k) * (2*n + k)) / ((k + 1) * (n + k + 1))
opaque a12 (n k:ℕ) (hn:1 ≤ n) (hk:k < n) :
    (F n (k+1):ℚ) = (F n k:ℚ) * a11 (n:ℚ) (k:ℚ):= by
  have hcross:= a7 n k hn hk
  have hden:(((k + 1:ℕ):ℚ) * (((n + k + 1:ℕ):ℚ))) ≠ 0:= by
    positivity
  apply (mul_right_inj' hden).mp
  unfold a11
  field_simp [hden]
  rw [Nat.cast_sub hk.le] at hcross
  norm_num [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hcross ⊢
  ring_nf at hcross ⊢
  exact hcross
opaque a13 (n k:ℕ) (hn:1 ≤ n) (hk:k ≤ n) :
    (F (n+1) k:ℚ) = (F n k:ℚ) * a9 (n:ℚ) (k:ℚ):= by
  have hcross:= a5 n k hn hk
  have hnq:(1:ℚ) ≤ n:= by exact_mod_cast hn
  have hkq:(k:ℚ) ≤ n:= by exact_mod_cast hk
  have hk0q:(0:ℚ) ≤ k:= by positivity
  have h1pos:(0:ℚ) < (n:ℚ) + 1 - k:= by linarith
  have h1:((n:ℚ) + 1 - k) ≠ 0:= ne_of_gt h1pos
  have h2:(n:ℚ) ≠ 0:= by positivity
  have h3:((n:ℚ) + k + 1) ≠ 0:= by positivity
  have hden:(((n:ℚ) + 1 - k) * (n:ℚ) * ((n:ℚ) + k + 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h1 h2) h3
  apply (mul_right_inj' hden).mp
  unfold a9
  field_simp [h1,h2,h3,hden]
  rw [Nat.cast_sub (by omega:k ≤ n + 1)] at hcross
  norm_num [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hcross ⊢
  ring_nf at hcross ⊢
  exact hcross
opaque a14 (n k:ℕ) (hn:2 ≤ n) (hk:k < n) :
    (F (n-1) k:ℚ) = (F n k:ℚ) * a10 (n:ℚ) (k:ℚ):= by
  have hcross:= a6 n k hn (by omega:k ≤ n - 1)
  have hnq:(2:ℚ) ≤ n:= by exact_mod_cast hn
  have hk0q:(0:ℚ) ≤ k:= by positivity
  have h1:(n:ℚ) ≠ 0:= by positivity
  have h2pos:(0:ℚ) < 2 * (n:ℚ) + k - 1:= by linarith
  have h2:(2 * (n:ℚ) + k - 1) ≠ 0:= ne_of_gt h2pos
  have h3pos:(0:ℚ) < 2 * (n:ℚ) + k - 2:= by linarith
  have h3:(2 * (n:ℚ) + k - 2) ≠ 0:= ne_of_gt h3pos
  have hden:((n:ℚ) * (2 * (n:ℚ) + k - 1) * (2 * (n:ℚ) + k - 2)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h1 h2) h3
  unfold a10
  rw [← mul_div_assoc]
  apply (eq_div_iff_mul_eq hden).2
  rw [Nat.cast_sub (by omega:k ≤ n)] at hcross
  rw [Nat.cast_sub (by omega:1 ≤ n)] at hcross
  rw [Nat.cast_sub (by omega:1 ≤ 2 * n + k)] at hcross
  rw [Nat.cast_sub (by omega:2 ≤ 2 * n + k)] at hcross
  norm_num [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hcross ⊢
  ring_nf at hcross ⊢
  exact hcross
def a15 (n k:ℚ):ℚ :=
  A n * a9 n k - B n - D n * a10 n k
def a16 (n k:ℚ):ℚ :=
  R n (k + 1) * a11 n k - R n k
def a17 (n k:ℚ):ℚ:= (n + 1) * (2*n + k) * (2*n + k + 1)
def a18 (n k:ℚ):ℚ:= (n + 1 - k) * n * (n + k + 1)
def a19 (n k:ℚ):ℚ:= (n - k) * (n - 1) * (n + k)
def a20 (n k:ℚ):ℚ:= n * (2*n + k - 1) * (2*n + k - 2)
def a21 (n k:ℚ):ℚ:= (n - k) * (2*n + k)
def a22 (n k:ℚ):ℚ:= (k + 1) * (n + k + 1)
def a23 (n k:ℚ):ℚ:= k * a8 n k
def a24 (n k:ℚ):ℚ:= n * (k - n - 1) * (k + 2*n - 2) * (k + 2*n - 1)
def a25 (n k:ℚ):ℚ :=
  a18 n k * a20 n k * a22 n k * a24 n k * a24 n (k + 1)
opaque a26 (n k:ℚ) :
    A n * a17 n k * a20 n k * a22 n k * a24 n k * a24 n (k + 1)
      - B n * a18 n k * a20 n k * a22 n k * a24 n k * a24 n (k + 1)
      - D n * a19 n k * a18 n k * a22 n k * a24 n k * a24 n (k + 1)
    = a23 n (k + 1) * a21 n k * a18 n k * a20 n k * a24 n k
      - a23 n k * a18 n k * a20 n k * a22 n k * a24 n (k + 1):= by
  let C:ℚ:= a8 n (k + 1) * (k - n - 1) * (k + 2*n - 2)
        + k * a8 n k * (n + k + 1)
  have hLbr :
      A n * a17 n k * a20 n k
        - B n * a18 n k * a20 n k
        - D n * a19 n k * a18 n k = n*C:= by
    dsimp [C,A,B,D,a17,a18,a19,a20,a8]
    ring_nf
  have hRbr :
      a23 n (k + 1) * a21 n k * a24 n k
        - a23 n k * a22 n k * a24 n (k + 1)
        = -n*(k+1)*(k-n)*(k+2*n)*(k+2*n-1)*C:= by
    dsimp [C,a23,a24,a21,a22]
    ring_nf
  calc
    A n * a17 n k * a20 n k * a22 n k * a24 n k * a24 n (k + 1)
      - B n * a18 n k * a20 n k * a22 n k * a24 n k * a24 n (k + 1)
      - D n * a19 n k * a18 n k * a22 n k * a24 n k * a24 n (k + 1)
        = (A n * a17 n k * a20 n k
          - B n * a18 n k * a20 n k
          - D n * a19 n k * a18 n k) * a22 n k * a24 n k * a24 n (k + 1):= by ring_nf
    _ = (n*C) * a22 n k * a24 n k * a24 n (k + 1):= by rw [hLbr]
    _ = a18 n k * a20 n k * (-n*(k+1)*(k-n)*(k+2*n)*(k+2*n-1)*C):= by
      dsimp [a18,a20,a22,a24]
      ring_nf
    _ = a18 n k * a20 n k * (a23 n (k + 1) * a21 n k * a24 n k
          - a23 n k * a22 n k * a24 n (k + 1)):= by rw [hRbr]
    _ = a23 n (k + 1) * a21 n k * a18 n k * a20 n k * a24 n k
      - a23 n k * a18 n k * a20 n k * a22 n k * a24 n (k + 1):= by ring_nf
opaque a27 (n:ℚ):R n 0 = 0:= by
  simp [R]
opaque a28 (n:ℚ):R n (n + 1) = 0:= by
  simp [R]
opaque a29 (n k:ℕ) (hn:2 ≤ n) (hk:k < n) :
    a25 (n:ℚ) (k:ℚ) ≠ 0:= by
  have hnq:(2:ℚ) ≤ n:= by exact_mod_cast hn
  have hkq:(k:ℚ) < n:= by exact_mod_cast hk
  have hk0q:(0:ℚ) ≤ k:= by positivity
  unfold a25 a18 a20 a22 a24
  repeat' apply mul_ne_zero
  all_goals nlinarith [hnq,hkq,hk0q]
opaque a30 (n k:ℚ)
    (hden:a25 n k ≠ 0):a15 n k = a16 n k:= by
  have hd_np1:a18 n k ≠ 0:= by
    intro h
    apply hden
    simp [a25,h]
  have hd_nm1:a20 n k ≠ 0:= by
    intro h
    apply hden
    simp [a25,h]
  have hd_kp1:a22 n k ≠ 0:= by
    intro h
    apply hden
    simp [a25,h]
  have hR_k:a24 n k ≠ 0:= by
    intro h
    apply hden
    simp [a25,h]
  have hR_k1:a24 n (k + 1) ≠ 0:= by
    intro h
    apply hden
    simp [a25,h]
  have hratio_np1:a9 n k = a17 n k / a18 n k:= by
    rfl
  have hratio_nm1:a10 n k = a19 n k / a20 n k:= by
    rfl
  have hratio_kp1:a11 n k = a21 n k / a22 n k:= by
    rfl
  have hR_eq (x:ℚ):R n x = a23 n x / a24 n x:= by
    rfl
  apply (mul_left_inj' hden).mp
  calc
    a15 n k * a25 n k
        = A n * a17 n k * a20 n k * a22 n k * a24 n k * a24 n (k + 1)
          - B n * a18 n k * a20 n k * a22 n k * a24 n k * a24 n (k + 1)
          - D n * a19 n k * a18 n k * a22 n k * a24 n k * a24 n (k + 1):= by
            simp only [a15,hratio_np1,hratio_nm1,a25]
            field_simp [hd_np1,hd_nm1]
    _ = a23 n (k + 1) * a21 n k * a18 n k * a20 n k * a24 n k
          - a23 n k * a18 n k * a20 n k * a22 n k * a24 n (k + 1):= by
            exact a26 n k
    _ = a16 n k * a25 n k:= by
            simp only [a16,hR_eq,hratio_kp1,a25]
            field_simp [hd_kp1,hR_k,hR_k1]
opaque a31 (n k:ℕ) (hn:2 ≤ n) (hk:k < n) :
    A (n:ℚ) * (F (n+1) k:ℚ) - B (n:ℚ) * (F n k:ℚ) - D (n:ℚ) * (F (n-1) k:ℚ)
      = R (n:ℚ) ((k:ℚ) + 1) * (F n (k+1):ℚ) - R (n:ℚ) (k:ℚ) * (F n k:ℚ):= by
  have hnorm:= a30 (n:ℚ) (k:ℚ)
    (a29 n k hn hk)
  have hm:= congrArg (fun x:ℚ=> (F n k:ℚ) * x) hnorm
  rw [a15,a16] at hm
  have hnp1:= a13 n k (by omega:1 ≤ n) hk.le
  have hnm1:= a14 n k hn hk
  have hkp1:= a12 n k (by omega:1 ≤ n) hk
  calc
    A (n:ℚ) * (F (n+1) k:ℚ) - B (n:ℚ) * (F n k:ℚ) - D (n:ℚ) * (F (n-1) k:ℚ)
        = (F n k:ℚ) * (A (n:ℚ) * a9 (n:ℚ) (k:ℚ) - B (n:ℚ) - D (n:ℚ) * a10 (n:ℚ) (k:ℚ)):= by
          rw [hnp1,hnm1]
          ring
    _ = (F n k:ℚ) * (R (n:ℚ) ((k:ℚ) + 1) * a11 (n:ℚ) (k:ℚ) - R (n:ℚ) (k:ℚ)):= by
          exact hm
    _ = R (n:ℚ) ((k:ℚ) + 1) * (F n (k+1):ℚ) - R (n:ℚ) (k:ℚ) * (F n k:ℚ):= by
          rw [hkp1]
          ring
opaque a32 (n:ℕ) (hn:1 ≤ n) :
    (((3 * n).choose n:ℕ):ℚ) = 3 * (F n n:ℚ):= by
  have hA:= Nat.choose_mul_succ_eq (3 * n - 1) (n - 1)
  have hAq:((((3 * n - 1).choose (n - 1):ℕ):ℚ) * ((3 * n:ℕ):ℚ)) =
      ((((3 * n).choose (n - 1):ℕ):ℚ) * ((2 * n + 1:ℕ):ℚ)):= by
    have hN:3 * n - 1 + 1 = 3 * n:= by omega
    have hsub:3 * n - (n - 1) = 2 * n + 1:= by omega
    exact_mod_cast (by simpa [hN,hsub] using hA)
  have hB:= Nat.choose_succ_right_eq (3 * n) (n - 1)
  have hBq:((((3 * n).choose n:ℕ):ℚ) * (n:ℚ)) =
      ((((3 * n).choose (n - 1):ℕ):ℚ) * ((2 * n + 1:ℕ):ℚ)):= by
    have hn1:n - 1 + 1 = n:= by omega
    have hsub:3 * n - (n - 1) = 2 * n + 1:= by omega
    exact_mod_cast (by simpa [hn1,hsub] using hB)
  have hmain:((((3 * n).choose n:ℕ):ℚ) * (n:ℚ)) =
      ((((3 * n - 1).choose (n - 1):ℕ):ℚ) * (3 * n:ℚ)):= by
    rw [hBq,← hAq]
    norm_num [Nat.cast_mul]
  have hF:(F n n:ℚ) = (((3 * n - 1).choose (n - 1):ℕ):ℚ):= by
    unfold F
    have hidx:2 * n + n - 1 = 3 * n - 1:= by omega
    rw [Nat.choose_self,hidx]
    norm_num
  have hnq:(n:ℚ) ≠ 0:= by
    have:(0:ℚ) < n:= by exact_mod_cast (by omega:0 < n)
    positivity
  apply (mul_right_inj' hnq).mp
  calc
    (n:ℚ) * (((3 * n).choose n:ℕ):ℚ)
        = (((3 * n).choose n:ℕ):ℚ) * (n:ℚ):= by ring
    _ = (((3 * n - 1).choose (n - 1):ℕ):ℚ) * (3 * (n:ℚ)):= hmain
    _ = (n:ℚ) * (3 * (F n n:ℚ)):= by
      rw [hF]
      ring
opaque a33 (n:ℕ) (hn:1 ≤ n) :
    A (n:ℚ) * (F (n + 1) (n + 1):ℚ) =
      3 * (3 * (n:ℚ) + 1) * (3 * (n:ℚ) + 2) *
        (5 * (n:ℚ)^2 - 5 * (n:ℚ) + 1) * (F n n:ℚ):= by
  have hub_nat:= a3 n
  have hub:(((2*n+1)*(2*n+2)*(5*n^2-5*n+1) * F (n+1) (n+1):ℕ):ℚ) =
      (((3*n+1)*(3*n+2)*(5*n^2-5*n+1) * ((3*n).choose n):ℕ):ℚ):= by
    exact_mod_cast hub_nat
  have hchoose:= a32 n hn
  unfold A
  norm_num [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] at hub ⊢
  rw [hchoose] at hub
  nlinarith [hub]
opaque a34 (n:ℕ) (hn:2 ≤ n) :
  (A (n:ℚ) * (F (n+1) n:ℚ) - B (n:ℚ)*(F n n:ℚ) - D (n:ℚ)*(F (n-1) n:ℚ)) +
  (A (n:ℚ) * (F (n+1) (n+1):ℚ) - B (n:ℚ)*(F n (n+1):ℚ) - D (n:ℚ)*(F (n-1) (n+1):ℚ))
 = R (n:ℚ) ((n:ℚ)+1) * (F n (n+1):ℚ) - R (n:ℚ) (n:ℚ)*(F n n:ℚ):= by
  have hnp1n:= a13 n n (by omega:1 ≤ n) (le_rfl:n ≤ n)
  have hupper:= a33 n (by omega:1 ≤ n)
  have hFn_succ:(F n (n + 1):ℚ) = 0:= by
    rw [a4 n (n + 1) (by omega)]
    norm_num
  have hFnm1_n:(F (n - 1) n:ℚ) = 0:= by
    rw [a4 (n - 1) n (by omega)]
    norm_num
  have hFnm1_succ:(F (n - 1) (n + 1):ℚ) = 0:= by
    rw [a4 (n - 1) (n + 1) (by omega)]
    norm_num
  rw [hnp1n,hupper,hFn_succ,hFnm1_n,hFnm1_succ,a28]
  unfold A B D R a9 a8
  have hnq:(n:ℚ) ≠ 0:= by
    have:(0:ℚ) < n:= by exact_mod_cast (by omega:0 < n)
    positivity
  have hnpos:(0:ℚ) < n:= by exact_mod_cast (by omega:0 < n)
  have hnq2:(2:ℚ) ≤ n:= by exact_mod_cast hn
  have hden1:(2 * (n:ℚ) + 1) ≠ 0:= by nlinarith [hnpos]
  have hden2:(3 * (n:ℚ) - 2) ≠ 0:= by nlinarith [hnq2]
  have hden3:(3 * (n:ℚ) - 1) ≠ 0:= by nlinarith [hnq2]
  have hdenR:(2 - (n:ℚ) * 9 + (n:ℚ)^2 * 9) ≠ 0:= by
    rw [show 2 - (n:ℚ) * 9 + (n:ℚ)^2 * 9 = (3 * (n:ℚ) - 1) * (3 * (n:ℚ) - 2) by ring]
    exact mul_ne_zero hden3 hden2
  field_simp [hnq,hden1,hden2,hden3,hdenR]
  ring_nf
  field_simp [hdenR]
  ring_nf
def a35 (n k:ℕ):ℚ :=
  A (n:ℚ) * (F (n+1) k:ℚ) - B (n:ℚ) * (F n k:ℚ) - D (n:ℚ) * (F (n-1) k:ℚ)
def a36 (n k:ℕ):ℚ:= R (n:ℚ) (k:ℚ) * (F n k:ℚ)
opaque a37 (f:ℕ → ℚ) :
    ∀ n,(Finset.range n).sum (fun k=> f (k+1) - f k) = f n - f 0:= by
  intro n
  induction n with
  | zero=> simp
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      ring
opaque a38 (n k:ℕ) (hn:2 ≤ n) (hk:k < n) :
    a35 n k = a36 n (k+1) - a36 n k:= by
  unfold a35 a36
  simpa [Nat.cast_add,Nat.cast_one] using a31 n k hn hk
opaque a39 (n:ℕ) (hn:2 ≤ n) :
    a35 n n + a35 n (n+1) = a36 n (n+1) - a36 n n:= by
  unfold a35 a36
  simpa [Nat.cast_add,Nat.cast_one] using a34 n hn
opaque a40 (n:ℕ) (hn:2 ≤ n) :
    (Finset.range (n+2)).sum (fun k=> a35 n k) = 0:= by
  have hsplit:(Finset.range (n+2)).sum (fun k=> a35 n k)
      = (Finset.range n).sum (fun k=> a35 n k) + a35 n n + a35 n (n+1):= by
    rw [show n + 2 = (n + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
  rw [hsplit]
  have hinterior:(Finset.range n).sum (fun k=> a35 n k) = a36 n n - a36 n 0:= by
    calc
      (Finset.range n).sum (fun k=> a35 n k)
          = (Finset.range n).sum (fun k=> a36 n (k+1) - a36 n k):= by
            apply Finset.sum_congr rfl
            intro k hk
            exact a38 n k hn (by simpa using hk)
      _ = a36 n n - a36 n 0:= a37 (a36 n) n
  have hboundary:= a39 n hn
  have hG0:a36 n 0 = 0:= by
    simp [a36,a27]
  rw [hinterior]
  calc
    a36 n n - a36 n 0 + a35 n n + a35 n (n+1)
        = a36 n n - a36 n 0 + (a35 n n + a35 n (n+1)):= by ring
    _ = a36 n n - a36 n 0 + (a36 n (n+1) - a36 n n):= by rw [hboundary]
    _ = 0:= by
      rw [hG0]
      simp [a36,a28]
opaque a41 (n:ℕ) (hn:2 ≤ n) :
    A (n:ℚ) * (Finset.range (n+2)).sum (fun k=> (F (n+1) k:ℚ))
      - B (n:ℚ) * (Finset.range (n+2)).sum (fun k=> (F n k:ℚ))
      - D (n:ℚ) * (Finset.range (n+2)).sum (fun k=> (F (n-1) k:ℚ)) = 0:= by
  have htotal:= a40 n hn
  rw [← htotal]
  simp [a35,Finset.mul_sum,Finset.sum_sub_distrib]
opaque a42 (n:ℕ) (hn:2 ≤ n) :
    A (n:ℚ) * (Finset.range (n+2)).sum (fun k=> (F (n+1) k:ℚ))
      - B (n:ℚ) * (Finset.range (n+1)).sum (fun k=> (F n k:ℚ))
      - D (n:ℚ) * (Finset.range n).sum (fun k=> (F (n-1) k:ℚ)) = 0:= by
  have hbase:= a41 n hn
  have hFn_succ:(F n (n+1):ℚ) = 0:= by
    rw [a4 n (n+1) (by omega)]
    norm_num
  have hFnm1_n:(F (n-1) n:ℚ) = 0:= by
    rw [a4 (n-1) n (by omega)]
    norm_num
  have hFnm1_succ:(F (n-1) (n+1):ℚ) = 0:= by
    rw [a4 (n-1) (n+1) (by omega)]
    norm_num
  rw [show (Finset.range (n+2)).sum (fun k=> (F n k:ℚ)) =
      (Finset.range (n+1)).sum (fun k=> (F n k:ℚ)) by
        rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ]
        simp [hFn_succ]] at hbase
  rw [show (Finset.range (n+2)).sum (fun k=> (F (n-1) k:ℚ)) =
      (Finset.range n).sum (fun k=> (F (n-1) k:ℚ)) by
        rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ]
        rw [show n+1=n+1 by rfl,Finset.sum_range_succ]
        simp [hFnm1_n,hFnm1_succ]] at hbase
  exact hbase
def aQ (n:ℕ):ℚ :=
  if n = 0 then 1 else (Finset.range (n+1)).sum (fun k=> (F n k:ℚ))
opaque a43 (n:ℕ) (hn:2 ≤ n) :
    A (n:ℚ) * aQ (n+1) - B (n:ℚ) * aQ n - D (n:ℚ) * aQ (n-1) = 0:= by
  have h:= a42 n hn
  have hn0:n ≠ 0:= by omega
  have hnp1:n + 1 ≠ 0:= by omega
  have hnm1:n - 1 ≠ 0:= by omega
  simp [aQ,hn0,hnp1,hnm1] at h ⊢
  simpa [show n - 1 + 1 = n by omega] using h
opaque a44:aQ 0 = 1:= by simp [aQ]
opaque a45:aQ 1 = 2:= by
  norm_num [aQ,F,Finset.sum_range_succ]
opaque a46:aQ 2 = 16:= by
  norm_num [aQ,F,Finset.sum_range_succ]
opaque a47 :
    A (1:ℚ) * aQ 2 - B (1:ℚ) * aQ 1 - D (1:ℚ) * aQ 0 = 0:= by
  norm_num [A,B,D,a44,a45,a46]
opaque a48 (n:ℕ) (hn:1 ≤ n) :
    A (n:ℚ) * aQ (n+1) - B (n:ℚ) * aQ n - D (n:ℚ) * aQ (n-1) = 0:= by
  rcases Nat.eq_or_lt_of_le hn with rfl | hgt
  · simpa using a47
  · exact a43 n (by omega)
opaque a49 (n:ℕ) (hn:1 ≤ n):0 < A (n:ℚ):= by
  unfold A
  have hnq:(1:ℚ) ≤ n:= by exact_mod_cast hn
  have h1:0 < 2 * (n:ℚ) + 1:= by nlinarith
  have h2:0 < 2 * (n:ℚ) + 2:= by nlinarith
  have hquad:0 < 5 * (n:ℚ)^2 - 5 * (n:ℚ) + 1:= by
    have hs:0 ≤ ((n:ℚ) - 1)^2:= sq_nonneg _
    nlinarith
  positivity
opaque a50 (n:ℕ) (hn:1 ≤ n):A (n:ℚ) ≠ 0:= by
  exact ne_of_gt (a49 n hn)
opaque a51 (N:ℕ) :
    aQ (N+2) = D ((N+1:ℕ):ℚ) / A ((N+1:ℕ):ℚ) * aQ N
      + B ((N+1:ℕ):ℚ) / A ((N+1:ℕ):ℚ) * aQ (N+1):= by
  have hrec:= a48 (N+1) (by omega:1 ≤ N+1)
  have hA:A ((N+1:ℕ):ℚ) ≠ 0:= a50 (N+1) (by omega)
  have hrec':A ((N+1:ℕ):ℚ) * aQ (N+2) - B ((N+1:ℕ):ℚ) * aQ (N+1) - D ((N+1:ℕ):ℚ) * aQ N = 0:= by
    simpa [show N + 1 + 1 = N + 2 by omega,show N + 1 - 1 = N by omega] using hrec
  apply (mul_left_inj' hA).mp
  field_simp [hA]
  nlinarith [hrec']
noncomputable def a52 (N:ℕ):Matrix (Fin 2) (Fin 2) ℚ :=
  ![![0,1],
    ![D ((N+1:ℕ):ℚ) / A ((N+1:ℕ):ℚ),B ((N+1:ℕ):ℚ) / A ((N+1:ℕ):ℚ)]]
opaque a53 (N:ℕ) :
    ![aQ (N+1),aQ (N+2)] = (a52 N).mulVec ![aQ N,aQ (N+1)]:= by
  ext i
  fin_cases i
  · simp [a52,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · simp [a52,Matrix.mulVec,dotProduct,Fin.sum_univ_two,a51 N]
def a54 (N:ℕ):Fin 2 → ℚ:= ![aQ N,aQ (N+1)]
opaque a55 (N:ℕ) :
    a54 (N+1) = (a52 N).mulVec (a54 N):= by
  simpa [a54] using a53 N
noncomputable def a56:ℕ → ℕ → Matrix (Fin 2) (Fin 2) ℚ
  | 0,_start=> 1
  | length + 1,start=> a52 (start + length) * a56 length start
opaque a57 (start length:ℕ) :
    a54 (start + length) = (a56 length start).mulVec (a54 start):= by
  induction length with
  | zero=> simp [a56]
  | succ length ih =>
      calc
        a54 (start + (length + 1)) = a54 ((start + length) + 1):= by rw [Nat.add_succ]
        _ = (a52 (start + length)).mulVec (a54 (start + length)):= a55 (start + length)
        _ = (a52 (start + length)).mulVec ((a56 length start).mulVec (a54 start)):= by rw [ih]
        _ = (a56 (length + 1) start).mulVec (a54 start):= by
          simp [a56,Matrix.mulVec_mulVec]
noncomputable def a58 (m n:ℕ):Matrix (Fin 2) (Fin 2) ℚ :=
  a56 m (m*n)
opaque a59 (m n:ℕ) :
    a54 (m*(n+1)) = (a58 m n).mulVec (a54 (m*n)):= by
  rw [Nat.mul_succ]
  simpa [a58] using a57 (m*n) m
def a60 (M:Matrix (Fin 2) (Fin 2) ℚ):ℚ:= M 0 0 * M 1 1 - M 0 1 * M 1 0
opaque a61
    (M:ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (x:ℕ → Fin 2 → ℚ)
    (hx:∀ n,x (n + 1) = (M n).mulVec (x n))
    (n:ℕ) :
    M n 0 1 * x (n + 2) 0
      - (M (n + 1) 0 0 * M n 0 1 + M (n + 1) 0 1 * M n 1 1) * x (n + 1) 0
      + M (n + 1) 0 1 * a60 (M n) * x n 0 = 0:= by
  let p:ℕ → ℚ:= fun k=> M k 0 0
  let q:ℕ → ℚ:= fun k=> M k 0 1
  let r:ℕ → ℚ:= fun k=> M k 1 0
  let s:ℕ → ℚ:= fun k=> M k 1 1
  let b:ℕ → ℚ:= fun k=> x k 0
  let h:ℕ → ℚ:= fun k=> x k 1
  have hb:∀ k,b (k + 1) = p k * b k + q k * h k:= by
    intro k
    change x (k + 1) 0 = M k 0 0 * x k 0 + M k 0 1 * x k 1
    rw [hx k]
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  have hh:∀ k,h (k + 1) = r k * b k + s k * h k:= by
    intro k
    change x (k + 1) 1 = M k 1 0 * x k 0 + M k 1 1 * x k 1
    rw [hx k]
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  change q n * b (n + 2) - (p (n + 1) * q n + q (n + 1) * s n) * b (n + 1)
      + q (n + 1) * (p n * s n - q n * r n) * b n = 0
  rw [hb (n + 1),hh n,hb n]
  simp [p,q,r,s,b,h,a60]
  ring
opaque a62 (m n:ℕ) :
    a58 m n 0 1 * aQ (m * (n + 2))
      - (a58 m (n + 1) 0 0 * a58 m n 0 1 + a58 m (n + 1) 0 1 * a58 m n 1 1) * aQ (m * (n + 1))
      + a58 m (n + 1) 0 1 * a60 (a58 m n) * aQ (m * n) = 0:= by
  let y:ℕ → Fin 2 → ℚ:= fun k=> a54 (m*k)
  have hy:∀ k,y (k+1) = (a58 m k).mulVec (y k):= by
    intro k
    change a54 (m * (k + 1)) = (a58 m k).mulVec (a54 (m * k))
    exact a59 m k
  have h:= a61 (fun k=> a58 m k) y hy n
  simpa [y,a54] using h
def a63 (n:ℕ):ℕ :=
  if n = 0 then 1 else (Finset.range (n+1)).sum (fun k=> F n k)
opaque a64 (n:ℕ):(a63 n:ℚ) = aQ n:= by
  by_cases hn:n = 0
  · subst hn
    simp [a63,aQ]
  · simp [a63,aQ,hn,Nat.cast_sum]
end N0
open Polynomial
namespace N1
noncomputable section
def a65:Polynomial ℚ:= (2 * X + 1) * (2 * X + 2) * (5 * X^2 - 5 * X + 1)
def a66:Polynomial ℚ:= 4 * (55 * X^4 - 34 * X^2 + 3)
def a67:Polynomial ℚ:= (2 * X - 1) * (2 * X - 2) * (5 * X^2 + 5 * X + 1)
def a68:Polynomial ℚ:= 5 * X^2 + 5 * X + 1
def a69 (p s:Polynomial ℚ):Polynomial ℚ:= p.comp s
def a70 (z:Polynomial ℚ):Polynomial ℚ:= a69 a68 z
opaque a71 (z:Polynomial ℚ) :
    a69 a67 z = (2 * z - 1) * (2 * z - 2) * a70 z:= by
  simp [a69,a67,a70,a68]
opaque a72 (z:Polynomial ℚ) :
    a70 z ∣ 5 * z * a69 a66 z + 4:= by
  refine ⟨4 + 20 * z * (11 * z^2 - 11 * z + 2),?_⟩
  simp [a70,a69,a66,a68]
  ring
opaque a73 (z:Polynomial ℚ) :
    a70 z ∣ a69 a66 (z + 1) + 4 * z:= by
  refine ⟨4 * (11 * (z + 1)^2 + 11 * (z + 1) + 2),?_⟩
  simp [a70,a69,a66,a68]
  ring
opaque a74 (z:Polynomial ℚ) :
    a69 a65 z = (2 * z + 1) * (2 * z + 2) * a70 (z - 1):= by
  unfold a69 a65 a70 a68
  simp [a69,Polynomial.add_comp,Polynomial.sub_comp,Polynomial.mul_comp,Polynomial.pow_comp]
  left
  ring
opaque a75 (z:Polynomial ℚ) :
    a70 z ∣ 5 * (a69 a67 (z + 1) * a69 a65 z) + 16:= by
  let Y:Polynomial ℚ:= z * (z + 1)
  refine ⟨400 * Y^3 - 620 * Y^2 + 140 * Y + 16,?_⟩
  simp [a70,a69,a67,a65,a68,Y]
  ring
def a76 (s:Polynomial ℚ) (r:ℕ):Polynomial ℚ:= s + (r:Polynomial ℚ)
def a77 (s:Polynomial ℚ):ℕ → Polynomial ℚ
  | 0=> 1
  | 1=> a69 a66 s
  | r + 2=> a69 a66 (s + (r+1:Polynomial ℚ)) * a77 s (r+1)
      + (a69 a67 (s + (r+1:Polynomial ℚ)) * a69 a65 (s + (r:Polynomial ℚ))) * a77 s r
opaque a78 (s:Polynomial ℚ) (r:ℕ) :
    a77 s (r + 2) = a69 a66 (a76 s (r+1)) * a77 s (r+1)
      + (a69 a67 (a76 s (r+1)) * a69 a65 (a76 s r)) * a77 s r:= by
  simp [a77,a76]
opaque a79 (s:Polynomial ℚ) (r:ℕ) :
    a70 (a76 s r) ∣ 5 * a76 s r * a77 s (r+1) + 4 * a77 s r:= by
  rcases r with _ | r
  · simpa [a76,a77] using a72 s
  · let u:Polynomial ℚ:= a76 s (r+1)
    have hD:a70 u ∣ a69 a67 u:= by
      rw [a71]
      exact dvd_mul_left (a70 u) ((2 * u - 1) * (2 * u - 2))
    have h1:a70 u ∣ (5 * u * a69 a66 u + 4) * a77 s (r+1) :=
      dvd_mul_of_dvd_left (a72 u) _
    have h2:a70 u ∣ (5 * u * a69 a67 u * a69 a65 (a76 s r)) * a77 s r:= by
      rcases hD with ⟨w,hw⟩
      refine ⟨(5 * u * w * a69 a65 (a76 s r)) * a77 s r,?_⟩
      rw [hw]
      ring
    have hsum:= dvd_add h1 h2
    convert hsum using 1 <;> simp [a78,a76,u] <;> ring
opaque a80 (s:Polynomial ℚ) (r:ℕ) :
    a70 (a76 s r) ∣ a77 s (r+2):= by
  let t:Polynomial ℚ:= a76 s r
  have hB:a70 t ∣ 5 * (a69 a66 (t+1) + 4*t) * a77 s (r+1) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (a73 t) (5:Polynomial ℚ)) _
  have hDA:a70 t ∣ (5 * (a69 a67 (t+1) * a69 a65 t) + 16) * a77 s r :=
    dvd_mul_of_dvd_left (a75 t) _
  have hrel:a70 t ∣ (-4:Polynomial ℚ) * (5 * t * a77 s (r+1) + 4 * a77 s r) :=
    dvd_mul_of_dvd_right (a79 s r) _
  have hsum:a70 t ∣
      5 * (a69 a66 (t+1) + 4*t) * a77 s (r+1) +
      (5 * (a69 a67 (t+1) * a69 a65 t) + 16) * a77 s r +
      (-4:Polynomial ℚ) * (5 * t * a77 s (r+1) + 4 * a77 s r) :=
    dvd_add (dvd_add hB hDA) hrel
  have h5:a70 t ∣ (5:Polynomial ℚ) * a77 s (r+2):= by
    convert hsum using 1 <;> simp [a78,a76,t] <;> ring_nf
  have hc:(5:Polynomial ℚ) = Polynomial.C (5:ℚ):= by
    exact (Polynomial.C_eq_natCast (R:= ℚ) 5).symm
  rw [hc] at h5
  exact (Polynomial.dvd_C_mul (p:= a70 t) (q:= a77 s (r+2)) (a:= (5:ℚ)) (by norm_num)).1 h5
opaque a81 (s:Polynomial ℚ) (i:ℕ) :
    a70 (a76 s i) ∣ a69 a65 (a76 s (i+1)):= by
  rw [a74]
  have ht:a76 s (i+1) - 1 = a76 s i:= by
    unfold a76
    norm_num
    ring
  rw [ht]
  exact dvd_mul_left (a70 (a76 s i)) ((2 * a76 s (i+1) + 1) * (2 * a76 s (i+1) + 2))
opaque a82 (d:ℚ) :
    (2 * X + Polynomial.C (3 * d + 1)) * a70 X +
      (-2 * X + Polynomial.C (d - 1)) * a70 (X + Polynomial.C d)
        = Polynomial.C (5 * d^3 - d):= by
  simp [a70,a69,a68]
  ring_nf
  ext n
  have hcoeff:((Polynomial.C (3:ℚ) * Polynomial.C d * X^2:Polynomial ℚ).coeff n)
      = if n = 2 then 3*d else 0:= by
    rw [← Polynomial.C_mul,Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_C,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,hcoeff]
  split_ifs <;> ring_nf
opaque a83 (y:Polynomial ℚ) (d:ℚ) :
    (2 * y + Polynomial.C (3 * d + 1)) * a70 y +
      (-2 * y + Polynomial.C (d - 1)) * a70 (y + Polynomial.C d)
        = Polynomial.C (5 * d^3 - d):= by
  have h:= congrArg (fun p:Polynomial ℚ=> p.comp y) (a82 d)
  simpa [a70,a69,a68] using h
opaque a84 (s:Polynomial ℚ) {i j:ℕ} (hij:i < j) :
    IsCoprime (a70 (a76 s i)) (a70 (a76 s j)):= by
  let n:ℕ:= j - i
  let d:ℚ:= n
  let y:Polynomial ℚ:= a76 s i
  have hn_pos:0 < n:= by
    dsimp [n]
    exact Nat.sub_pos_of_lt hij
  have hj:j = i + n:= by
    dsimp [n]
    omega
  have hTj:a76 s j = y + Polynomial.C d:= by
    dsimp [y,d,n]
    unfold a76
    rw [hj]
    norm_num
    ring
  have hd_ge_one:(1:ℚ) ≤ d:= by
    dsimp [d]
    exact_mod_cast hn_pos
  have hc_pos:0 < 5 * d^3 - d:= by
    nlinarith [sq_nonneg d]
  have hden_ne:5 * d^2 - 1 ≠ 0:= by
    have hden_pos:0 < 5 * d^2 - 1:= by
      nlinarith [sq_nonneg d]
    exact ne_of_gt hden_pos
  have hc_ne:5 * d^3 - d ≠ 0:= ne_of_gt hc_pos
  let A:Polynomial ℚ:= 2 * y + Polynomial.C (3 * d + 1)
  let B:Polynomial ℚ:= -2 * y + Polynomial.C (d - 1)
  have hBez:A * a70 y + B * a70 (a76 s j) = Polynomial.C (5 * d^3 - d):= by
    dsimp [A,B]
    rw [hTj]
    exact a83 y d
  refine ⟨Polynomial.C ((5 * d^3 - d)⁻¹) * A,Polynomial.C ((5 * d^3 - d)⁻¹) * B,?_⟩
  calc
    (Polynomial.C ((5 * d^3 - d)⁻¹) * A) * a70 (a76 s i) +
        (Polynomial.C ((5 * d^3 - d)⁻¹) * B) * a70 (a76 s j)
        = Polynomial.C ((5 * d^3 - d)⁻¹) * (A * a70 y + B * a70 (a76 s j)):= by
          dsimp [y]
          ring
    _ = Polynomial.C ((5 * d^3 - d)⁻¹) * Polynomial.C (5 * d^3 - d):= by
          rw [hBez]
    _ = 1:= by
          rw [← Polynomial.C_mul]
          change Polynomial.C (((5 * d^3 - d)⁻¹) * (5 * d^3 - d)) = Polynomial.C (1:ℚ)
          congr
          field_simp [hden_ne]
opaque a85 (s:Polynomial ℚ):∀ n i:ℕ,i + 2 ≤ n → a70 (a76 s i) ∣ a77 s n:= by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro i hi
      rcases n with _ | n1
      · omega
      rcases n1 with _ | r
      · omega
      by_cases hir:i = r
      · simpa [hir] using a80 s r
      · have hi_le:i + 2 ≤ r + 1:= by omega
        rw [a78]
        apply dvd_add
        · exact dvd_mul_of_dvd_right (ih (r+1) (by omega) i hi_le) _
        · by_cases hi2r:i + 2 ≤ r
          · exact dvd_mul_of_dvd_right (ih r (by omega) i hi2r) _
          · have hir1:i + 1 = r:= by omega
            have hA:a70 (a76 s i) ∣ a69 a65 (a76 s r):= by
              simpa [hir1] using a81 s i
            rcases hA with ⟨w,hw⟩
            refine ⟨(a69 a67 (a76 s (r+1)) * w) * a77 s r,?_⟩
            rw [hw]
            ring
def a86 (s:Polynomial ℚ) (n:ℕ):Polynomial ℚ :=
  (Finset.range n).prod (fun i=> a70 (a76 s i))
opaque a87 (s:Polynomial ℚ) {i j:ℕ} (hij:i ≠ j) :
    IsCoprime (a70 (a76 s i)) (a70 (a76 s j)):= by
  wlog hlt:i < j generalizing i j with H
  · have hji:j < i:= by omega
    simpa [isCoprime_comm] using H (Ne.symm hij) hji
  exact a84 s hlt
opaque a88 (s:Polynomial ℚ) (n:ℕ) :
    a86 s (n - 1) ∣ a77 s n:= by
  unfold a86
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact a87 s hij
  · intro i hi
    rw [Finset.mem_range] at hi
    exact a85 s n i (by omega)
opaque a89 (s:Polynomial ℚ) (n:ℕ) :
    a86 s (n+1) = a70 s * a86 (s+1) n:= by
  unfold a86
  induction n with
  | zero=> simp [a76]
  | succ n ih =>
      rw [Finset.prod_range_succ,ih,Finset.prod_range_succ]
      simp [a76]
      ring_nf
opaque a90 (n:ℕ) :
    a86 X n ∣ a70 X * a77 (X+1) n:= by
  rcases n with _ | n
  · simp [a86]
  · rw [a89]
    exact mul_dvd_mul_left (a70 X) (a88 (X+1) (n+1))
opaque a91 (i:ℕ):a70 (a76 X i) ≠ 0:= by
  intro h
  have hev:= congrArg (fun p:Polynomial ℚ=> p.eval 0) h
  unfold a70 a69 a68 a76 at hev
  simp [Polynomial.eval_comp] at hev
  nlinarith
opaque a92 (n:ℕ):a86 X n ≠ 0:= by
  unfold a86
  exact Finset.prod_ne_zero_iff.mpr (by
    intro i hi
    exact a91 i)
def a93 (n:ℕ):Polynomial ℚ :=
  (a70 X * a77 (X+1) n) / a86 X n
opaque a94 (n:ℕ) :
    a86 X n * a93 n = a70 X * a77 (X+1) n:= by
  unfold a93
  exact EuclideanDomain.mul_div_cancel' (a92 n) (a90 n)
opaque a95:a65.natDegree ≤ 4:= by
  unfold a65
  compute_degree!
opaque a96:a66.natDegree ≤ 4:= by
  unfold a66
  compute_degree!
opaque a97:a67.natDegree ≤ 4:= by
  unfold a67
  compute_degree!
opaque a98 (r:ℕ):(a76 (X+1) r).natDegree ≤ 1:= by
  unfold a76
  compute_degree!
opaque a99 (r:ℕ):(a69 a65 (a76 (X+1) r)).natDegree ≤ 4:= by
  calc
    (a69 a65 (a76 (X+1) r)).natDegree ≤ a65.natDegree * (a76 (X+1) r).natDegree:= by
      exact Polynomial.natDegree_comp_le
    _ ≤ 4 * 1:= Nat.mul_le_mul a95 (a98 r)
    _ = 4:= by norm_num
opaque a100 (r:ℕ):(a69 a66 (a76 (X+1) r)).natDegree ≤ 4:= by
  calc
    (a69 a66 (a76 (X+1) r)).natDegree ≤ a66.natDegree * (a76 (X+1) r).natDegree:= by
      exact Polynomial.natDegree_comp_le
    _ ≤ 4 * 1:= Nat.mul_le_mul a96 (a98 r)
    _ = 4:= by norm_num
opaque a101 (r:ℕ):(a69 a67 (a76 (X+1) r)).natDegree ≤ 4:= by
  calc
    (a69 a67 (a76 (X+1) r)).natDegree ≤ a67.natDegree * (a76 (X+1) r).natDegree:= by
      exact Polynomial.natDegree_comp_le
    _ ≤ 4 * 1:= Nat.mul_le_mul a97 (a98 r)
    _ = 4:= by norm_num
lemma a102:∀ n:ℕ,(a77 (X+1) n).natDegree ≤ 4*n
  | 0=> by simp [a77]
  | 1=> by
      simpa [a77,a76] using a100 0
  | n+2=> by
      rw [a78]
      calc
        (a69 a66 (a76 (X + 1) (n + 1)) * a77 (X + 1) (n + 1) +
            a69 a67 (a76 (X + 1) (n + 1)) * a69 a65 (a76 (X + 1) n) * a77 (X + 1) n).natDegree
            ≤ max ((a69 a66 (a76 (X + 1) (n + 1)) * a77 (X + 1) (n + 1)).natDegree)
                ((a69 a67 (a76 (X + 1) (n + 1)) * a69 a65 (a76 (X + 1) n) * a77 (X + 1) n).natDegree):= Polynomial.natDegree_add_le _ _
        _ ≤ 4 * (n+2):= by
          apply max_le
          · calc
              (a69 a66 (a76 (X + 1) (n + 1)) * a77 (X + 1) (n + 1)).natDegree
                  ≤ (a69 a66 (a76 (X + 1) (n + 1))).natDegree + (a77 (X+1) (n+1)).natDegree:= Polynomial.natDegree_mul_le
              _ ≤ 4 + 4*(n+1):= Nat.add_le_add (a100 _) (a102 (n+1))
              _ ≤ 4 * (n+2):= by omega
          · calc
              (a69 a67 (a76 (X + 1) (n + 1)) * a69 a65 (a76 (X + 1) n) * a77 (X + 1) n).natDegree
                  ≤ (a69 a67 (a76 (X + 1) (n + 1)) * a69 a65 (a76 (X + 1) n)).natDegree + (a77 (X+1) n).natDegree:= Polynomial.natDegree_mul_le
              _ ≤ ((a69 a67 (a76 (X + 1) (n + 1))).natDegree + (a69 a65 (a76 (X + 1) n)).natDegree) + (a77 (X+1) n).natDegree:= Nat.add_le_add_right (Polynomial.natDegree_mul_le) _
              _ ≤ (4 + 4) + 4*n:= Nat.add_le_add (Nat.add_le_add (a101 _) (a99 _)) (a102 n)
              _ ≤ 4 * (n+2):= by omega
opaque a103 (i:ℕ):(a70 (a76 X i)).natDegree = 2:= by
  unfold a70 a69 a68 a76
  simp [Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp]
  compute_degree!
opaque a104 (n:ℕ):(a86 X n).natDegree = 2*n:= by
  induction n with
  | zero=> simp [a86]
  | succ n ih =>
      unfold a86
      rw [Finset.prod_range_succ]
      rw [Polynomial.natDegree_mul]
      · change (a86 X n).natDegree + (a70 (a76 X n)).natDegree = 2 * (n + 1)
        rw [ih]
        rw [a103]
        omega
      · unfold a86 at *
        exact a92 n
      · exact a91 n
opaque a105:(a70 X).natDegree ≤ 2:= by
  simpa [a76] using (le_of_eq (a103 0))
opaque a106 (n:ℕ):(a70 X * a77 (X+1) n).natDegree ≤ 4*n + 2:= by
  calc
    (a70 X * a77 (X+1) n).natDegree ≤ (a70 X).natDegree + (a77 (X+1) n).natDegree:= Polynomial.natDegree_mul_le
    _ ≤ 2 + 4*n:= Nat.add_le_add a105 (a102 n)
    _ = 4*n + 2:= by omega
opaque a107 (n:ℕ):(a93 n).natDegree ≤ 2*n + 2:= by
  by_cases hp:a93 n = 0
  · simp [hp]
  · have hmul:= congrArg Polynomial.natDegree (a94 n)
    rw [Polynomial.natDegree_mul (a92 n) hp] at hmul
    rw [a104 n] at hmul
    have hle:= a106 n
    rw [← hmul] at hle
    omega
end
end N1
namespace N2
def a108 (j:ℤ):ℤ:= 55*j^4 - 136*j^2 + 48
def a109 (j:ℤ):ℤ:= (j + 1) * (j + 2) * (5*j^2 - 10*j + 4)
def a110 (j:ℤ):ℤ:= (j - 1) * (j - 2) * (5*j^2 + 10*j + 4)
opaque a111 (j:ℤ):a108 j < 0 ↔ j = 1 ∨ j = -1:= by
  unfold a108
  constructor
  · intro h
    by_contra hcases
    push_neg at hcases
    have hj_abs:j^2 = 0 ∨ 4 ≤ j^2:= by
      have hj0:j = 0 ∨ 2 ≤ j ∨ 2 ≤ -j:= by omega
      rcases hj0 with rfl | hp | hn
      · left; norm_num
      · right; nlinarith [sq_nonneg (j - 2)]
      · right; nlinarith [sq_nonneg (j + 2)]
    rcases hj_abs with h0 | h4
    · nlinarith
    · have:0 ≤ 55 * (j^2 - 4)^2 + 304 * (j^2 - 4) + 384:= by nlinarith [sq_nonneg (j^2 - 4)]
      nlinarith
  · intro h
    rcases h with rfl | rfl <;> norm_num
opaque a112 (j:ℤ) (h1:j ≠ 1) (hm1:j ≠ -1):0 < a108 j:= by
  unfold a108
  have hj_abs:j^2 = 0 ∨ 4 ≤ j^2:= by
    have hj0:j = 0 ∨ 2 ≤ j ∨ 2 ≤ -j:= by omega
    rcases hj0 with rfl | hp | hn
    · left; norm_num
    · right; nlinarith [sq_nonneg (j - 2)]
    · right; nlinarith [sq_nonneg (j + 2)]
  rcases hj_abs with h0 | h4
  · nlinarith
  · have:0 ≤ 55 * (j^2 - 4)^2 + 304 * (j^2 - 4):= by
      have hsq:= sq_nonneg (j^2 - 4)
      nlinarith
    nlinarith
opaque a113 (j:ℤ) (h:j ≠ 1):0 < 5*j^2 - 10*j + 4:= by
  have hj:j ≤ 0 ∨ 2 ≤ j:= by omega
  rcases hj with hj | hj
  · have hs:= sq_nonneg j
    nlinarith
  · have hs:= sq_nonneg (j - 2)
    nlinarith
opaque a114 (j:ℤ) (h:j ≠ -1):0 < 5*j^2 + 10*j + 4:= by
  have hj:j ≤ -2 ∨ 0 ≤ j:= by omega
  rcases hj with hj | hj
  · have hs:= sq_nonneg (j + 2)
    nlinarith
  · have hs:= sq_nonneg j
    nlinarith
opaque a115 (j:ℤ):a109 j < 0 ↔ j = 1:= by
  unfold a109
  constructor
  · intro h
    by_contra hj
    have hq:0 < 5*j^2 - 10*j + 4:= a113 j hj
    have hlin:0 ≤ (j + 1) * (j + 2):= by
      have hcases:j ≤ -2 ∨ -1 ≤ j:= by omega
      rcases hcases with hle | hge
      · have h1:j + 1 ≤ 0:= by omega
        have h2:j + 2 ≤ 0:= by omega
        exact mul_nonneg_of_nonpos_of_nonpos h1 h2
      · have h1:0 ≤ j + 1:= by omega
        have h2:0 ≤ j + 2:= by omega
        exact mul_nonneg h1 h2
    nlinarith [mul_nonneg hlin hq.le]
  · intro h; subst h; norm_num
opaque a116 (j:ℤ):a110 j = 0 ↔ j = 1 ∨ j = 2:= by
  unfold a110
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h12 | hq
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · left; omega
      · right; omega
    · have hnot:j ≠ -1:= by
        intro hj; subst hj; norm_num at hq
      have hpos:= a114 j hnot
      nlinarith
  · intro h; rcases h with rfl | rfl <;> norm_num
opaque a117 (j:ℤ):a110 j < 0 ↔ j = -1:= by
  unfold a110
  constructor
  · intro h
    by_contra hj
    have hq:0 < 5*j^2 + 10*j + 4:= a114 j hj
    have hlin:0 ≤ (j - 1) * (j - 2):= by
      have hcases:j ≤ 1 ∨ 2 ≤ j:= by omega
      rcases hcases with hle | hge
      · have h1:j - 1 ≤ 0:= by omega
        have h2:j - 2 ≤ 0:= by omega
        exact mul_nonneg_of_nonpos_of_nonpos h1 h2
      · have h1:0 ≤ j - 1:= by omega
        have h2:0 ≤ j - 2:= by omega
        exact mul_nonneg h1 h2
    nlinarith [mul_nonneg hlin hq.le]
  · intro h; subst h; norm_num
section RationalScaled
def Cq (j:ℤ):ℚ:= 4 * (55 * ((j:ℚ)/2)^4 - 34 * ((j:ℚ)/2)^2 + 3)
def Aq (j:ℤ):ℚ:= ((j:ℚ) + 1) * ((j:ℚ) + 2) * (5*((j:ℚ)/2)^2 - 5*((j:ℚ)/2) + 1)
def Dq (j:ℤ):ℚ:= ((j:ℚ) - 1) * ((j:ℚ) - 2) * (5*((j:ℚ)/2)^2 + 5*((j:ℚ)/2) + 1)
opaque a118 (j:ℤ):Cq j = (a108 j:ℚ) / 4:= by
  unfold Cq a108
  norm_num
  ring
opaque a119 (j:ℤ):Aq j = (a109 j:ℚ) / 4:= by
  unfold Aq a109
  norm_num
  ring
opaque a120 (j:ℤ):Dq j = (a110 j:ℚ) / 4:= by
  unfold Dq a110
  norm_num
  ring
opaque a121 (j:ℤ):Cq j < 0 ↔ j = 1 ∨ j = -1:= by
  rw [a118]
  constructor
  · intro h
    have hcq:((a108 j:ℤ):ℚ) < 0:= by nlinarith
    have hc:a108 j < 0:= by exact_mod_cast hcq
    exact (a111 j).mp hc
  · intro h
    have hc:a108 j < 0:= (a111 j).mpr h
    exact div_neg_of_neg_of_pos (by exact_mod_cast hc) (by norm_num)
opaque a122 (j:ℤ) (h1:j ≠ 1) (hm1:j ≠ -1):0 < Cq j:= by
  rw [a118]
  exact div_pos (by exact_mod_cast a112 j h1 hm1) (by norm_num)
opaque a123 (j:ℤ):Aq j < 0 ↔ j = 1:= by
  rw [a119]
  constructor
  · intro h
    have haq:((a109 j:ℤ):ℚ) < 0:= by nlinarith
    have ha:a109 j < 0:= by exact_mod_cast haq
    exact (a115 j).mp ha
  · intro h
    have ha:a109 j < 0:= (a115 j).mpr h
    exact div_neg_of_neg_of_pos (by exact_mod_cast ha) (by norm_num)
opaque a124 (j:ℤ):Dq j = 0 ↔ j = 1 ∨ j = 2:= by
  rw [a120]
  norm_num
  exact_mod_cast a116 j
opaque a125 (j:ℤ):Dq j < 0 ↔ j = -1:= by
  rw [a120]
  constructor
  · intro h
    have hdq:((a110 j:ℤ):ℚ) < 0:= by nlinarith
    have hd:a110 j < 0:= by exact_mod_cast hdq
    exact (a117 j).mp hd
  · intro h
    have hd:a110 j < 0:= (a117 j).mpr h
    exact div_neg_of_neg_of_pos (by exact_mod_cast hd) (by norm_num)
opaque a126 (j:ℤ) (h:j ≠ 1):0 ≤ Aq j:= by
  by_contra hneg
  have hlt:Aq j < 0:= lt_of_not_ge hneg
  exact h ((a123 j).mp hlt)
opaque a127 (j:ℤ) (h:j ≠ -1):0 ≤ Dq j:= by
  by_contra hneg
  have hlt:Dq j < 0:= lt_of_not_ge hneg
  exact h ((a125 j).mp hlt)
opaque a128 (j:ℤ) (hneg:j ≠ -1) (hz1:j ≠ 1) (hz2:j ≠ 2):0 < Dq j:= by
  have hnonneg:= a127 j hneg
  have hnez:Dq j ≠ 0:= by
    intro h
    have hz:= (a124 j).mp h
    rcases hz with hz | hz <;> omega
  exact lt_of_le_of_ne' hnonneg hnez
opaque a129 (t:ℤ):0 < Cq (2 * t):= by
  apply a122
  · intro h
    omega
  · intro h
    omega
opaque a130 (t:ℤ):0 ≤ Aq (2 * t):= by
  apply a126
  intro h
  omega
opaque a131 (t:ℤ):0 ≤ Dq (2 * t):= by
  apply a127
  intro h
  omega
def a132 (j:ℤ):ℚ:= 5*((j:ℚ)/2)^2 + 5*((j:ℚ)/2) + 1
opaque a133 (j:ℤ):a132 j = ((5*j^2 + 10*j + 4:ℤ):ℚ) / 4:= by
  unfold a132
  norm_num
  ring
opaque a134 (j:ℤ):a132 j < 0 ↔ j = -1:= by
  rw [a133]
  constructor
  · intro h
    have hq:(((5*j^2 + 10*j + 4:ℤ):ℚ) < 0):= by nlinarith
    have hi:(5*j^2 + 10*j + 4:ℤ) < 0:= by exact_mod_cast hq
    by_contra hj
    have hp:= a114 j hj
    nlinarith
  · intro h
    subst h
    norm_num [a132]
opaque a135 (j:ℤ) (h:j ≠ -1):0 < a132 j:= by
  rw [a133]
  exact div_pos (by exact_mod_cast a114 j h) (by norm_num)
def a136 (start:ℤ):ℕ → ℚ
  | 0=> 1
  | n + 1=> a132 (start + 2 * (n:ℤ)) * a136 start n
@[simp] lemma DquadProd_zero (s:ℤ):a136 s 0 = 1:= rfl
@[simp] lemma DquadProd_succ (s:ℤ) (n:ℕ) :
    a136 s (n+1) = a132 (s + 2 * (n:ℤ)) * a136 s n:= rfl
opaque a137 (s:ℤ):∀ n:ℕ,(∀ r:ℕ,r < n → 0 < a132 (s + 2 * (r:ℤ))) → 0 < a136 s n:= by
  intro n
  induction n with
  | zero=> intro _; simp [a136]
  | succ n ih =>
      intro h
      simp [a136]
      exact mul_pos (h n (by omega)) (ih (fun r hr=> h r (by omega)))
opaque a138 (s:ℤ) (n:ℕ)
    (h:∀ r,r < n → s + 2 * (r:ℤ) ≠ -1) :
    0 < a136 s n:= by
  apply a137
  intro r hr
  exact a135 _ (h r hr)
opaque a139 (t:ℤ) (n:ℕ):0 < a136 (2*t) n:= by
  apply a138
  intro r hr h
  omega
opaque a140 (s:ℤ) (m n:ℕ) :
    a136 s (m + n) = a136 (s + 2 * (m:ℤ)) n * a136 s m:= by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_succ,DquadProd_succ,ih,DquadProd_succ]
      have harg:s + 2 * ((m + n:ℕ):ℤ) = s + 2 * (m:ℤ) + 2 * (n:ℤ):= by
        omega
      rw [harg]
      ring
opaque a141 (p:ℕ) :
    0 < a136 (1 - 2 * (p:ℤ)) (p - 1):= by
  apply a138
  intro r hr h
  omega
opaque a142 (n:ℕ):0 < a136 1 n:= by
  apply a138
  intro r hr h
  omega
opaque a143 (p:ℕ) (hp:1 ≤ p) :
    a136 (1 - 2 * (p:ℤ) + 2 * ((p - 1:ℕ):ℤ)) 1 < 0:= by
  have harg:1 - 2 * (p:ℤ) + 2 * ((p - 1:ℕ):ℤ) = -1:= by
    omega
  simpa [a136,harg] using (a134 (-1)).mpr rfl
opaque a144 (p q:ℕ) (hp:1 ≤ p) :
    a136 (1 - 2 * (p:ℤ)) (p + q) < 0:= by
  let s:ℤ:= 1 - 2 * (p:ℤ)
  have hsplit_last :
      a136 s p = a136 (s + 2 * ((p - 1:ℕ):ℤ)) 1 * a136 s (p - 1):= by
    have hp_eq:p = (p - 1) + 1:= by omega
    rw [hp_eq]
    exact a140 s (p - 1) 1
  have hsuf_start:s + 2 * (p:ℤ) = 1:= by
    dsimp [s]
    omega
  have hsuf_pos:0 < a136 (s + 2 * (p:ℤ)) q:= by
    rw [hsuf_start]
    exact a142 q
  have hneg_factor:a136 (s + 2 * ((p - 1:ℕ):ℤ)) 1 < 0:= by
    dsimp [s]
    exact a143 p hp
  have hprefix_pos:0 < a136 s (p - 1):= by
    dsimp [s]
    exact a141 p
  have hpblock_neg:a136 s p < 0:= by
    rw [hsplit_last]
    exact mul_neg_of_neg_of_pos hneg_factor hprefix_pos
  rw [a140 s p q]
  exact mul_neg_of_pos_of_neg hsuf_pos hpblock_neg
opaque a145 (j:ℤ):Cq (-j) = Cq j:= by
  unfold Cq
  norm_num [Int.cast_neg]
  ring
opaque a146 (j:ℤ):Aq (-j) = Dq j:= by
  unfold Aq Dq
  norm_num [Int.cast_neg]
  ring
opaque a147 (j:ℤ):Dq (-j) = Aq j:= by
  unfold Aq Dq
  norm_num [Int.cast_neg]
  ring
section a148
def a148 (start:ℤ):ℕ → ℚ
  | 0=> 1
  | 1=> Cq start
  | n + 2 =>
      Cq (start + 2 * ((n + 1:ℕ):ℤ)) * a148 start (n + 1) +
      (Dq (start + 2 * ((n + 1:ℕ):ℤ)) * Aq (start + 2 * (n:ℤ))) * a148 start n
@[simp] lemma Kgrid_zero (s:ℤ):a148 s 0 = 1:= rfl
@[simp] lemma Kgrid_one (s:ℤ):a148 s 1 = Cq s:= rfl
@[simp] lemma Kgrid_succ_succ (s:ℤ) (n:ℕ) :
    a148 s (n+2) =
      Cq (s + 2 * ((n + 1:ℕ):ℤ)) * a148 s (n + 1) +
      (Dq (s + 2 * ((n + 1:ℕ):ℤ)) * Aq (s + 2 * (n:ℤ))) * a148 s n:= rfl
opaque a149 (s:ℤ):∀ n:ℕ,
    a148 s (n+2) =
      Cq s * a148 (s + 2) (n + 1) +
      (Dq (s + 2) * Aq s) * a148 (s + 4) n:= by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simp [a148]
        ring_nf
      rcases n with _ | n
      · simp [a148]
        ring_nf
      rw [Kgrid_succ_succ]
      have ih1:a148 s (n + 3) =
          Cq s * a148 (s + 2) (n + 2) +
          (Dq (s + 2) * Aq s) * a148 (s + 4) (n + 1):= by
        simpa [show n + 3 = (n + 1) + 2 by omega] using ih (n + 1) (by omega)
      have ih0:a148 s (n + 2) =
          Cq s * a148 (s + 2) (n + 1) +
          (Dq (s + 2) * Aq s) * a148 (s + 4) n:= by
        simpa [show n + 2 = n + 2 by rfl] using ih n (by omega)
      rw [ih1,ih0]
      rw [show n + 1 + 1 + 1 = n + 3 by omega]
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [Kgrid_succ_succ (s + 2) (n + 1)]
      rw [Kgrid_succ_succ (s + 4) n]
      have hC2:(s + 2) + 2 * (((n + 1) + 1:ℕ):ℤ) =
          s + 2 * ((n + 2 + 1:ℕ):ℤ):= by omega
      have hA2:(s + 2) + 2 * ((n + 1:ℕ):ℤ) =
          s + 2 * ((n + 2:ℕ):ℤ):= by omega
      have hC4:(s + 4) + 2 * ((n + 1:ℕ):ℤ) =
          s + 2 * ((n + 2 + 1:ℕ):ℤ):= by omega
      have hA4:(s + 4) + 2 * (n:ℤ) =
          s + 2 * ((n + 2:ℕ):ℤ):= by omega
      rw [hC2,hA2,hC4,hA4]
      ring_nf
opaque a150 (s:ℤ) (n:ℕ) :
    a148 s (n+1) = a148 (-(s + 2 * (n:ℤ))) (n+1):= by
  revert s
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro s
      rcases n with _ | n
      · simp [a148,a145]
      rw [show n.succ + 1 = n + 2 by omega]
      rw [a149]
      rw [Kgrid_succ_succ]
      have ih1:a148 (s + 2) (n + 1) =
          a148 (-(s + 2 * ((n + 1:ℕ):ℤ))) (n + 1):= by
        simpa [show (s + 2) + 2 * (n:ℤ) = s + 2 * ((n + 1:ℕ):ℤ) by omega]
          using ih n (by omega) (s + 2)
      have ih0:a148 (s + 4) n =
          a148 (-(s + 2 * ((n + 1:ℕ):ℤ))) n:= by
        rcases n with _ | n
        · simp
        · simpa [show (s + 4) + 2 * (n:ℤ) = s + 2 * (((n + 1) + 1:ℕ):ℤ) by omega]
            using ih n (by omega) (s + 4)
      rw [ih1,ih0]
      have hCD:-(s + 2 * ((n + 1:ℕ):ℤ)) + 2 * ((n + 1:ℕ):ℤ) = -s:= by omega
      have hA:-(s + 2 * ((n + 1:ℕ):ℤ)) + 2 * (n:ℤ) = -(s + 2):= by omega
      rw [hCD,hA]
      rw [a145 s,a147 s,a146 (s + 2)]
      ring_nf
opaque a151 (t:ℤ) (n:ℕ) :
    2 * t + 2 * (n:ℤ) = 2 * (t + (n:ℤ)):= by ring
opaque a152 (t:ℤ):∀ n,0 < a148 (2 * t) n:= by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simp [a148]
      rcases n with _ | n
      · change 0 < Cq (2 * t)
        exact a129 t
      rw [Kgrid_succ_succ]
      have hprev1:0 < a148 (2 * t) (n + 1):= ih (n + 1) (by omega)
      have hprev0:0 < a148 (2 * t) n:= ih n (by omega)
      have hc:0 < Cq (2 * (t + ((n + 1:ℕ):ℤ))):= a129 (t + ((n + 1:ℕ):ℤ))
      have hc':0 < Cq (2 * t + 2 * ((n + 1:ℕ):ℤ)):= by
        convert hc using 2
        ring
      have hd:0 ≤ Dq (2 * (t + ((n + 1:ℕ):ℤ))):= a131 (t + ((n + 1:ℕ):ℤ))
      have hd':0 ≤ Dq (2 * t + 2 * ((n + 1:ℕ):ℤ)):= by
        convert hd using 2
        ring
      have ha:0 ≤ Aq (2 * (t + (n:ℤ))):= a130 (t + (n:ℤ))
      have ha':0 ≤ Aq (2 * t + 2 * (n:ℤ)):= by
        simpa [a151] using ha
      exact add_pos_of_pos_of_nonneg (mul_pos hc' hprev1) (mul_nonneg (mul_nonneg hd' ha') hprev0.le)
opaque a153:Cq 1 < 0:= by
  exact (a121 1).mpr (by left; rfl)
opaque a154:Dq 1 = 0:= by
  exact (a124 1).mpr (by left; rfl)
opaque a155:Aq 1 < 0:= by
  exact (a123 1).mpr rfl
opaque a156:0 < Cq 3:= by
  apply a122 <;> omega
opaque a157:0 < Dq 3:= by
  have hnonneg:= a127 3 (by omega)
  have hnez:Dq 3 ≠ 0:= by
    intro h
    have hz:= (a124 3).mp h
    omega
  exact lt_of_le_of_ne' hnonneg hnez
opaque a158:a148 1 1 < 0:= by
  simpa [a148] using a153
opaque a159:a148 1 2 < 0:= by
  simp [a148]
  have hterm1:Cq 3 * Cq 1 < 0:= mul_neg_of_pos_of_neg a156 a153
  have hterm2:Dq 3 * Aq 1 ≤ 0:= (mul_neg_of_pos_of_neg a157 a155).le
  exact add_neg_of_neg_of_nonpos hterm1 hterm2
opaque a160:∀ q,a148 1 (q + 1) < 0:= by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      rcases q with _ | q
      · simpa using a158
      rcases q with _ | q
      · simpa using a159
      rw [show q.succ.succ + 1 = q + 3 by omega]
      rw [show q + 3 = (q + 1) + 2 by omega,Kgrid_succ_succ]
      have hprev1:a148 1 (q + 2) < 0:= by
        simpa [show q + 2 = (q + 1) + 1 by omega] using ih (q + 1) (by omega)
      have hprev0:a148 1 (q + 1) < 0:= ih q (by omega)
      have hc:0 < Cq (1 + 2 * (((q + 1) + 1:ℕ):ℤ)):= by
        apply a122 <;> intro h <;> omega
      have hd:0 ≤ Dq (1 + 2 * (((q + 1) + 1:ℕ):ℤ)):= by
        apply a127
        intro h; omega
      have ha:0 ≤ Aq (1 + 2 * ((q + 1:ℕ):ℤ)):= by
        apply a126
        intro h; omega
      exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hc hprev1)
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hd ha) hprev0.le)
opaque a161 (s:ℤ) (p q:ℕ) (hp:1 ≤ p)
    (hzero:Dq (s + 2 * (p:ℤ)) * Aq (s + 2 * ((p - 1:ℕ):ℤ)) = 0) :
    a148 s (p + q) = a148 s p * a148 (s + 2 * (p:ℤ)) q:= by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      rcases q with _ | q
      · simp
      rcases q with _ | q
      · rw [show p + 1 = (p - 1) + 2 by omega,Kgrid_succ_succ]
        have hp_sub:(p - 1 + 1:ℕ) = p:= by omega
        simp [a148,hp_sub,hzero]
        ring
      rw [show p + q.succ.succ = (p + q) + 2 by omega,Kgrid_succ_succ]
      have ih1:a148 s (p + (q + 1)) =
          a148 s p * a148 (s + 2 * (p:ℤ)) (q + 1):= ih (q + 1) (by omega)
      have ih0:a148 s (p + q) =
          a148 s p * a148 (s + 2 * (p:ℤ)) q:= ih q (by omega)
      have ih1':a148 s (p + q + 1) =
          a148 s p * a148 (s + 2 * (p:ℤ)) (q + 1):= by
        simpa [Nat.add_assoc] using ih1
      rw [ih1',ih0]
      rw [show q + 1 + 1 = q + 2 by omega,Kgrid_succ_succ]
      have hC:s + 2 * ((p + q + 1:ℕ):ℤ) =
          (s + 2 * (p:ℤ)) + 2 * ((q + 1:ℕ):ℤ):= by omega
      have hA:s + 2 * ((p + q:ℕ):ℤ) =
          (s + 2 * (p:ℤ)) + 2 * (q:ℤ):= by omega
      rw [hC,hA]
      ring
opaque a162 (p:ℕ) (hp:1 ≤ p) :
    a148 (1 - 2 * (p:ℤ)) p < 0:= by
  rcases p with _ | q
  · omega
  have href:= a150 (1 - 2 * ((q + 1:ℕ):ℤ)) q
  have hstart:-((1 - 2 * ((q + 1:ℕ):ℤ)) + 2 * (q:ℤ)) = 1:= by omega
  have hneg:a148 (-(1 - 2 * ((q + 1:ℕ):ℤ) + 2 * (q:ℤ))) (q + 1) < 0:= by
    convert a160 q using 2
  rw [href]
  exact hneg
opaque a163 (p q:ℕ) (hp:1 ≤ p) (hq:1 ≤ q) :
    0 < a148 (1 - 2 * (p:ℤ)) (p + q):= by
  have hzero:Dq ((1 - 2 * (p:ℤ)) + 2 * (p:ℤ)) *
        Aq ((1 - 2 * (p:ℤ)) + 2 * ((p - 1:ℕ):ℤ)) = 0:= by
    have h1:(1 - 2 * (p:ℤ)) + 2 * (p:ℤ) = 1:= by ring
    have h2:(1 - 2 * (p:ℤ)) + 2 * ((p - 1:ℕ):ℤ) = -1:= by omega
    rw [h1,h2,a154]
    ring
  rw [a161 (1 - 2 * (p:ℤ)) p q hp hzero]
  have hleft:a148 (1 - 2 * (p:ℤ)) p < 0:= a162 p hp
  rcases q with _ | q'
  · omega
  have hright:a148 ((1 - 2 * (p:ℤ)) + 2 * (p:ℤ)) (q' + 1) < 0:= by
    have hstart:(1 - 2 * (p:ℤ)) + 2 * (p:ℤ) = 1:= by ring
    simpa [hstart] using a160 q'
  exact mul_pos_of_neg_of_neg hleft hright
opaque a164 (m a:ℕ) :
    0 < a148 (2 * (a:ℤ) - 2 * (m:ℤ) + 2) (m - 1):= by
  have h:= a152 ((a:ℤ) - (m:ℤ) + 1) (m - 1)
  convert h using 2 <;> ring
opaque a165 (m:ℕ) (hm:2 ≤ m) :
    a148 (3 - 2 * (m:ℤ)) (m - 1) < 0:= by
  have h:= a162 (m - 1) (by omega)
  convert h using 2
  · have hcast:((m - 1:ℕ):ℤ) = (m:ℤ) - 1:= by omega
    rw [hcast]
    ring
opaque a166 (m:ℕ) (hm:2 ≤ m) :
    a148 1 (m - 1) < 0:= by
  have h:= a160 (m - 2)
  convert h using 2 <;> omega
opaque a167 (m a:ℕ) (ha1:1 ≤ a) (ha2:a + 2 ≤ m) :
    0 < a148 (2 * (a:ℤ) + 3 - 2 * (m:ℤ)) (m - 1):= by
  have h:= a163 (m - a - 1) a (by omega) ha1
  convert h using 2
  · have hcast:((m - a - 1:ℕ):ℤ) = (m:ℤ) - (a:ℤ) - 1:= by omega
    rw [hcast]
    ring
  · omega
opaque a168 (m a:ℕ) :
    0 < a148 ((2 * a:ℕ) - 2 * (m:ℤ) + 2) (m - 1):= by
  have h:= a164 m a
  convert h using 2
opaque a169 (m:ℕ) (hm:2 ≤ m) :
    a148 ((1:ℕ) - 2 * (m:ℤ) + 2) (m - 1) < 0:= by
  have h:= a165 m hm
  convert h using 2
  norm_num
  ring
def a170 (m k:ℕ):ℚ :=
  let j:ℤ:= (k:ℤ) - 2 * (m:ℤ)
  (((j - 1:ℤ):ℚ) * ((j - 2:ℤ):ℚ)) * a136 j (m - 1)
opaque a171 (m k:ℕ) (hk:k ≤ 2*m) :
    0 < (((((k:ℤ) - 2 * (m:ℤ)) - 1:ℤ):ℚ) * ((((k:ℤ) - 2 * (m:ℤ)) - 2:ℤ):ℚ)):= by
  have h1:(((k:ℤ) - 2 * (m:ℤ)) - 1:ℤ) < 0:= by omega
  have h2:(((k:ℤ) - 2 * (m:ℤ)) - 2:ℤ) < 0:= by omega
  exact mul_pos_of_neg_of_neg (by exact_mod_cast h1) (by exact_mod_cast h2)
opaque a172 (m a:ℕ) (ha:a ≤ m):0 < a170 m (2*a):= by
  unfold a170
  have hlin:= a171 m (2*a) (by omega)
  have hprod:0 < a136 (((2*a:ℕ):ℤ) - 2 * (m:ℤ)) (m - 1):= by
    have h:= a139 ((a:ℤ) - (m:ℤ)) (m - 1)
    convert h using 2
    norm_num [Nat.cast_mul]
    ring
  exact mul_pos hlin hprod
opaque a173 (m:ℕ) (hm:2 ≤ m):0 < a170 m 1:= by
  unfold a170
  have hlin:= a171 m 1 (by omega)
  have hprod:0 < a136 ((1:ℤ) - 2 * (m:ℤ)) (m - 1):= by
    have h:= a141 m
    convert h using 2 <;> ring
  exact mul_pos hlin hprod
opaque a174 (m a:ℕ) (ha1:1 ≤ a) (ha2:a + 1 ≤ m) :
    a170 m (2*a + 1) < 0:= by
  unfold a170
  have hlin:= a171 m (2*a+1) (by omega)
  have hprod:a136 (((2*a + 1:ℕ):ℤ) - 2 * (m:ℤ)) (m - 1) < 0:= by
    have h:= a144 (m - a) (a - 1) (by omega)
    convert h using 2
    · have hcast:((m - a:ℕ):ℤ) = (m:ℤ) - (a:ℤ):= by omega
      rw [hcast]
      norm_num [Nat.cast_add,Nat.cast_mul]
      ring
    · omega
  exact mul_neg_of_pos_of_neg hlin hprod
opaque a175 (m:ℕ) (hm:2 ≤ m) :
    a148 (((2 * m - 1:ℕ):ℤ) - 2 * (m:ℤ) + 2) (m - 1) < 0:= by
  have h:= a166 m hm
  convert h using 2
  have hcast:((2 * m - 1:ℕ):ℤ) = 2 * (m:ℤ) - 1:= by omega
  rw [hcast]
  ring
opaque a176 (m a:ℕ) (ha1:1 ≤ a) (ha2:a + 2 ≤ m) :
    0 < a148 (((2 * a + 1:ℕ):ℤ) - 2 * (m:ℤ) + 2) (m - 1):= by
  have h:= a167 m a ha1 ha2
  convert h using 2
  norm_num [Nat.cast_add,Nat.cast_mul]
  ring
def a177 (m k:ℕ):ℚ :=
  Dq ((k:ℤ) - 2 * (m:ℤ)) * a148 ((k:ℤ) - 2 * (m:ℤ) + 2) (m - 1)
opaque a178 (m a:ℕ) (ha:a ≤ m):0 < a177 m (2*a):= by
  unfold a177
  have hd:0 < Dq (((2*a:ℕ):ℤ) - 2 * (m:ℤ)):= by
    apply a128 <;> intro h <;> omega
  have hk:= a168 m a
  exact mul_pos hd hk
opaque a179 (m:ℕ) (hm:2 ≤ m):a177 m 1 < 0:= by
  unfold a177
  have hd:0 < Dq ((1:ℤ) - 2 * (m:ℤ)):= by
    apply a128 <;> intro h <;> omega
  have hk:= a169 m hm
  exact mul_neg_of_pos_of_neg hd hk
opaque a180 (m:ℕ) (hm:2 ≤ m):a177 m (2*m - 1) > 0:= by
  unfold a177
  have hd:Dq (((2*m - 1:ℕ):ℤ) - 2 * (m:ℤ)) < 0:= by
    have hcast:((2*m - 1:ℕ):ℤ) = 2 * (m:ℤ) - 1:= by omega
    rw [hcast]
    convert (a125 (-1)).mpr rfl using 2
    ring
  have hk:= a175 m hm
  exact mul_pos_of_neg_of_neg hd hk
opaque a181 (m a:ℕ) (ha1:1 ≤ a) (ha2:a + 2 ≤ m) :
    0 < a177 m (2*a + 1):= by
  unfold a177
  have hd:0 < Dq (((2*a + 1:ℕ):ℤ) - 2 * (m:ℤ)):= by
    apply a128 <;> intro h <;> omega
  have hk:= a176 m a ha1 ha2
  exact mul_pos hd hk
end a148
def a182 (m k:ℕ):ℚ:= a177 m k / a170 m k
opaque a183 (m a:ℕ) (ha:a ≤ m):0 < a182 m (2*a):= by
  unfold a182
  exact div_pos (a178 m a ha) (a172 m a ha)
opaque a184 (m:ℕ) (hm:2 ≤ m):a182 m 1 < 0:= by
  unfold a182
  exact div_neg_of_neg_of_pos (a179 m hm) (a173 m hm)
opaque a185 (m:ℕ) (hm:2 ≤ m):a182 m (2*m - 1) < 0:= by
  unfold a182
  have hE':= a174 m (m - 1) (by omega) (by omega)
  have hE:a170 m (2*m - 1) < 0:= by
    convert hE' using 2 <;> omega
  exact div_neg_of_pos_of_neg (a180 m hm) hE
opaque a186 (m a:ℕ) (ha1:1 ≤ a) (ha2:a + 2 ≤ m) :
    a182 m (2*a + 1) < 0:= by
  unfold a182
  have hE:= a174 m a ha1 (by omega)
  exact div_neg_of_pos_of_neg (a181 m a ha1 ha2) hE
opaque a187:a182 1 1 < 0:= by
  unfold a182 a177 a170
  norm_num [a148,a136]
  have hd:Dq (-1) < 0:= (a125 (-1)).mpr rfl
  exact div_neg_of_neg_of_pos (by simpa using hd) (by norm_num:(0:ℚ) < 6)
theorem a188 (m a:ℕ) (ha:a ≤ m) :
    0 < a182 m (2*a):= a183 m a ha
opaque a189 (m a:ℕ) (hm:1 ≤ m) (hbound:2*a + 1 ≤ 2*m) :
    a182 m (2*a + 1) < 0:= by
  by_cases ha0:a = 0
  · subst a
    by_cases hm1:m = 1
    · subst m
      simpa using a187
    · have hm2:2 ≤ m:= by omega
      simpa using a184 m hm2
  · have ha1:1 ≤ a:= by omega
    by_cases hright:a + 1 = m
    · have hm2:2 ≤ m:= by omega
      have hk:2*a + 1 = 2*m - 1:= by omega
      rw [hk]
      exact a185 m hm2
    · have ha2:a + 2 ≤ m:= by omega
      exact a186 m a ha1 ha2
opaque a190 (m a:ℕ) (hm:1 ≤ m) (hbound:2*a + 1 ≤ 2*m) :
    a182 m (2*a) * a182 m (2*a + 1) < 0:= by
  have ha:a ≤ m:= by omega
  exact mul_neg_of_pos_of_neg (a188 m a ha) (a189 m a hm hbound)
opaque a191 (m a:ℕ) (hm:1 ≤ m) (hbound:2*a + 2 ≤ 2*m) :
    a182 m (2*a + 1) * a182 m (2*(a+1)) < 0:= by
  have hodd:2*a + 1 ≤ 2*m:= by omega
  have ha:a + 1 ≤ m:= by omega
  exact mul_neg_of_neg_of_pos (a189 m a hm hodd) (a188 m (a+1) ha)
opaque a192 (m i:ℕ) (hm:1 ≤ m) (hi:i < 2*m) :
    a182 m i * a182 m (i+1) < 0:= by
  rcases Nat.even_or_odd i with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · simpa [two_mul] using a190 m a hm (by omega)
  · have h:2*a + 2 ≤ 2*m:= by omega
    simpa [two_mul,show a + a + 1 + 1 = (a + 1) + (a + 1) by omega] using a191 m a hm h
end RationalScaled
end N2
open Polynomial
open scoped BigOperators
namespace N4
noncomputable section
open N1
opaque a193 (j:ℤ) :
    a65.eval ((j:ℚ) / 2) = N2.Aq j:= by
  simp [a65,N2.Aq]
  ring_nf
  left
  trivial
opaque a194 (j:ℤ) :
    a66.eval ((j:ℚ) / 2) = N2.Cq j:= by
  simp [a66,N2.Cq]
opaque a195 (j:ℤ) :
    a67.eval ((j:ℚ) / 2) = N2.Dq j:= by
  simp [a67,N2.Dq]
  ring_nf
  left
  trivial
opaque a196 (j:ℤ) :
    (a70 X).eval ((j:ℚ) / 2) = N2.a132 j:= by
  simp [a70,a69,a68,N2.a132]
opaque a197 (j:ℤ) :
    a68.eval ((j:ℚ) / 2) = N2.a132 j:= by
  simpa [a70,a69] using a196 j
opaque a198 (m k:ℕ) :
    (a86 X (m-1)).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2) =
      N2.a136 ((k:ℤ) - 2*(m:ℤ)) (m-1):= by
  unfold a86
  induction (m-1) with
  | zero=> simp [N2.a136]
  | succ n ih =>
      rw [Finset.prod_range_succ,N2.DquadProd_succ]
      simp only [eval_mul]
      rw [ih]
      have harg:(a76 X n).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2)
          = (((k:ℤ) - 2*(m:ℤ) + 2*(n:ℤ):ℤ):ℚ) / 2:= by
        unfold a76
        simp
        norm_num [Int.cast_add,Int.cast_mul]
        ring
      unfold a70 a69
      rw [Polynomial.eval_comp,harg,a197]
      ring
lemma a199 (m k:ℕ):∀ n:ℕ,
    (a77 (X+1) n).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2) =
      N2.a148 ((k:ℤ) - 2*(m:ℤ) + 2) n
  | 0=> by simp [a77,N2.a148]
  | 1=> by
      simp [a77]
      have harg:(X + 1:Polynomial ℚ).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2)
          = (((k:ℤ) - 2*(m:ℤ) + 2:ℤ):ℚ) / 2:= by
        simp
        norm_num [Int.cast_add]
        ring
      unfold a69
      rw [Polynomial.eval_comp]
      simp only [eval_add,eval_X,eval_one]
      have harg2:(((k:ℚ) - 2*(m:ℚ)) / 2 + 1) =
          (((k:ℤ) - 2*(m:ℤ) + 2:ℤ):ℚ) / 2:= by
        norm_num [Int.cast_add]
        ring
      rw [harg2]
      exact a194 ((k:ℤ) - 2*(m:ℤ) + 2)
  | n+2=> by
      rw [a78,N2.Kgrid_succ_succ]
      simp only [eval_add,eval_mul]
      rw [a199 m k (n+1),a199 m k n]
      have hBarg:(a76 (X + 1) (n + 1)).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2)
          = (((k:ℤ) - 2*(m:ℤ) + 2 + 2*((n+1:ℕ):ℤ):ℤ):ℚ) / 2:= by
        unfold a76
        simp
        norm_num [Int.cast_add,Int.cast_mul]
        ring
      have hAarg:(a76 (X + 1) n).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2)
          = (((k:ℤ) - 2*(m:ℤ) + 2 + 2*(n:ℤ):ℤ):ℚ) / 2:= by
        unfold a76
        simp
        norm_num [Int.cast_add,Int.cast_mul]
        ring
      unfold a69
      rw [Polynomial.eval_comp,hBarg,a194]
      rw [Polynomial.eval_comp,hBarg,a195]
      rw [Polynomial.eval_comp,hAarg,a193]
opaque a200 (j:ℤ) :
    N2.Dq j =
      (((j-1:ℤ):ℚ) * ((j-2:ℤ):ℚ)) * N2.a132 j:= by
  unfold N2.Dq N2.a132
  norm_num [Int.cast_sub]
opaque a201 (m k:ℕ) (hk:k ≤ 2*m) :
    N2.a182 m k =
      ((a70 X * a77 (X+1) (m-1)).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2)) /
        (a86 X (m-1)).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2):= by
  unfold N2.a182 N2.a177 N2.a170
  simp only [eval_mul]
  rw [a196,a199,a198]
  rw [a200]
  let lin:ℚ:= (((((k:ℤ) - 2 * (m:ℤ)) - 1:ℤ):ℚ) *
    ((((k:ℤ) - 2 * (m:ℤ)) - 2:ℤ):ℚ))
  change (lin * N2.a132 ((k:ℤ) - 2 * (m:ℤ)) *
      N2.a148 ((k:ℤ) - 2 * (m:ℤ) + 2) (m - 1)) /
      (lin * N2.a136 ((k:ℤ) - 2 * (m:ℤ)) (m - 1)) =
    (N2.a132 ((k:ℤ) - 2 * (m:ℤ)) *
      N2.a148 ((k:ℤ) - 2 * (m:ℤ) + 2) (m - 1)) /
      N2.a136 ((k:ℤ) - 2 * (m:ℤ)) (m - 1)
  by_cases hlin:lin = 0
  · unfold lin at hlin
    have h1:(((k:ℤ) - 2 * (m:ℤ)) - 1:ℤ) ≠ 0:= by omega
    have h2:(((k:ℤ) - 2 * (m:ℤ)) - 2:ℤ) ≠ 0:= by omega
    norm_num at hlin
    rcases hlin with hlin | hlin
    · have hz:(((k:ℤ) - 2 * (m:ℤ)) - 1:ℤ) = 0:= by exact_mod_cast hlin
      exact (h1 hz).elim
    · have hz:(((k:ℤ) - 2 * (m:ℤ)) - 2:ℤ) = 0:= by exact_mod_cast hlin
      exact (h2 hz).elim
  · field_simp [hlin]
opaque a202 (m k:ℕ) (hk:k ≤ 2*m)
    (hden:(a86 X (m-1)).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2) ≠ 0) :
    (a93 (m-1)).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2) =
      N2.a182 m k:= by
  have hmul:= congrArg (fun p:Polynomial ℚ=> p.eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2))
    (a94 (m-1))
  simp only [eval_mul] at hmul
  rw [a201 m k hk]
  exact (eq_div_iff_mul_eq hden).2 (by simpa [mul_comm] using hmul)
opaque a203 (j:ℤ):N2.a132 j ≠ 0:= by
  by_cases h:j = -1
  · subst h
    exact ne_of_lt ((N2.a134 (-1)).mpr rfl)
  · exact ne_of_gt (N2.a135 j h)
lemma a204 (s:ℤ):∀ n:ℕ,N2.a136 s n ≠ 0
  | 0=> by simp [N2.a136]
  | n+1=> by
      rw [N2.DquadProd_succ]
      exact mul_ne_zero (a203 _) (a204 s n)
opaque a205 (m k:ℕ) :
    (a86 X (m-1)).eval ((((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2) ≠ 0:= by
  rw [a198]
  exact a204 _ _
def PmQ (m:ℕ):Polynomial ℚ :=
  (a93 (m-1)).comp ((m:Polynomial ℚ) * (X - 1))
opaque a206 (m k:ℕ) (hm:1 ≤ m) (hk:k ≤ 2*m) :
    (PmQ m).eval ((k:ℚ) / (2*m:ℚ)) = N2.a182 m k:= by
  unfold PmQ
  rw [Polynomial.eval_comp]
  have harg:((m:Polynomial ℚ) * (X - 1)).eval ((k:ℚ) / (2*m:ℚ)) =
      (((k:ℤ) - 2*(m:ℤ):ℤ):ℚ) / 2:= by
    simp
    have hmne:(m:ℚ) ≠ 0:= by exact_mod_cast (ne_of_gt hm)
    field_simp [hmne]
  rw [harg]
  exact a202 m k hk (a205 m k)
opaque a207 (m i:ℕ) (hm:1 ≤ m) (hi:i < 2*m) :
    (PmQ m).eval ((i:ℚ)/(2*m:ℚ)) *
      (PmQ m).eval (((i+1:ℕ):ℚ)/(2*m:ℚ)) < 0:= by
  rw [a206 m i hm (by omega)]
  rw [a206 m (i+1) hm (by omega)]
  exact N2.a192 m i hm hi
opaque a208 (m:ℕ):(((m:Polynomial ℚ) * (X - 1))).natDegree ≤ 1:= by
  by_cases hm:m = 0
  · subst hm
    simp
  · compute_degree!
opaque a209 (m:ℕ) (hm:1 ≤ m):(PmQ m).natDegree ≤ 2*m:= by
  unfold PmQ
  calc
    ((a93 (m - 1)).comp ((m:Polynomial ℚ) * (X - 1))).natDegree
        ≤ (a93 (m-1)).natDegree * (((m:Polynomial ℚ) * (X - 1))).natDegree:= Polynomial.natDegree_comp_le
    _ ≤ (2*(m-1)+2) * 1:= Nat.mul_le_mul (a107 (m-1)) (a208 m)
    _ ≤ 2*m:= by omega
end
end N4
open Polynomial
open scoped BigOperators
namespace N4
noncomputable section
open N1
opaque a210 (j:ℤ) :
    N2.a132 (-j - 2) = N2.a132 j:= by
  unfold N2.a132
  norm_num [Int.cast_sub,Int.cast_neg]
  ring
opaque a211 (s:ℤ) (n:ℕ) :
    N2.a136 s (n + 1) =
      N2.a136 (s + 2) n * N2.a132 s:= by
  have h:= N2.a140 s 1 n
  have hone:N2.a136 s 1 = N2.a132 s:= by
    simp [N2.a136]
  simpa [Nat.add_comm,hone,mul_comm] using h
lemma a212 (s:ℤ):∀ n:ℕ,
    N2.a132 s *
        N2.a136 (-(s + 2 * ((n + 1:ℕ):ℤ))) n =
      N2.a132 (-(s + 2 * ((n + 1:ℕ):ℤ))) *
        N2.a136 s n
  | 0=> by
      simp [N2.a136]
      simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using (a210 s).symm
  | n + 1=> by
      rw [N2.DquadProd_succ]
      have htop:-(s + 2 * (((n + 1) + 1:ℕ):ℤ)) + 2 * (n:ℤ) = -((s + 2) + 2):= by
        omega
      rw [htop]
      have hqtop:N2.a132 (-((s + 2) + 2)) =
          N2.a132 (s + 2):= by
        simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using a210 (s + 2)
      rw [hqtop]
      have ih:= a212 (s + 2) n
      have hstart:-((s + 2) + 2 * ((n + 1:ℕ):ℤ)) =
          -(s + 2 * (((n + 1) + 1:ℕ):ℤ)):= by
        omega
      rw [hstart] at ih
      rw [N2.DquadProd_succ]
      have hsnoc:N2.a136 (s + 2) n *
            N2.a132 s =
          N2.a132 (s + 2 * (n:ℤ)) *
            N2.a136 s n:= by
        rw [← a211 s n,N2.DquadProd_succ]
      calc
        N2.a132 s *
            (N2.a132 (s + 2) *
              N2.a136 (-(s + 2 * (((n + 1) + 1:ℕ):ℤ))) n)
            = N2.a132 s *
              (N2.a132 (-(s + 2 * (((n + 1) + 1:ℕ):ℤ))) *
                N2.a136 (s + 2) n):= by
                rw [ih]
        _ = N2.a132 (-(s + 2 * (((n + 1) + 1:ℕ):ℤ))) *
              (N2.a132 (s + 2 * (n:ℤ)) *
                N2.a136 s n):= by
                rw [← hsnoc]
                ring
opaque a213 (m k:ℕ) (hk:k ≤ 2*m) :
    N2.a182 m k =
      (N2.a132 ((k:ℤ) - 2 * (m:ℤ)) *
        N2.a148 ((k:ℤ) - 2 * (m:ℤ) + 2) (m - 1)) /
        N2.a136 ((k:ℤ) - 2 * (m:ℤ)) (m - 1):= by
  rw [a201 m k hk]
  simp only [eval_mul]
  rw [a196,a199,a198]
opaque a214 (m k:ℕ) (hk:k ≤ 2*m) :
    N2.a182 m k =
      N2.a182 m (2*m - k):= by
  by_cases hm0:m = 0
  · subst hm0
    have hk0:k = 0:= by omega
    subst hk0
    simp
  by_cases hm1:m = 1
  · subst hm1
    have hkcases:k = 0 ∨ k = 1 ∨ k = 2:= by omega
    rcases hkcases with rfl | rfl | rfl <;>
      norm_num [N2.a182,
        N2.a177,N2.a170,
        N2.a148,N2.a136,
        N2.Dq,N2.a132,
        N2.Cq]
  · have hm2:2 ≤ m:= by omega
    let s:ℤ:= (k:ℤ) - 2 * (m:ℤ)
    let t:ℤ:= ((2*m - k:ℕ):ℤ) - 2 * (m:ℤ)
    have ht:t = -(s + 2 * (m:ℤ)):= by
      dsimp [s,t]
      have hcast:((2 * m - k:ℕ):ℤ) = 2 * (m:ℤ) - (k:ℤ):= by omega
      rw [hcast]
      ring
    have hm1eq:m - 1 = (m - 2) + 1:= by omega
    rw [a213 m k hk]
    rw [a213 m (2*m-k) (by omega)]
    change (N2.a132 s *
        N2.a148 (s + 2) (m - 1)) /
        N2.a136 s (m - 1) =
      (N2.a132 t *
        N2.a148 (t + 2) (m - 1)) /
        N2.a136 t (m - 1)
    rw [hm1eq]
    have hK:N2.a148 (s + 2) ((m - 2) + 1) =
        N2.a148 (t + 2) ((m - 2) + 1):= by
      have h:= N2.a150 (s + 2) (m - 2)
      have harg:-(s + 2 + 2 * ((m - 2:ℕ):ℤ)) = t + 2:= by
        rw [ht]
        omega
      simpa [harg] using h
    rw [hK]
    have hprod:N2.a132 s *
          N2.a136 t ((m - 2) + 1) =
        N2.a132 t *
          N2.a136 s ((m - 2) + 1):= by
      have h:= a212 s ((m - 2) + 1)
      have harg:-(s + 2 * ((((m - 2) + 1) + 1:ℕ):ℤ)) = t:= by
        rw [ht]
        omega
      rw [harg] at h
      simpa using h
    have hDs:N2.a136 s ((m - 2) + 1) ≠ 0:= a204 _ _
    have hDt:N2.a136 t ((m - 2) + 1) ≠ 0:= a204 _ _
    field_simp [hDs,hDt]
    calc
      N2.a132 s * N2.a148 (t + 2) ((m - 2) + 1) *
          N2.a136 t ((m - 2) + 1)
          = (N2.a132 s *
              N2.a136 t ((m - 2) + 1)) *
              N2.a148 (t + 2) ((m - 2) + 1):= by ring
      _ = (N2.a132 t *
              N2.a136 s ((m - 2) + 1)) *
              N2.a148 (t + 2) ((m - 2) + 1):= by rw [hprod]
      _ = N2.a148 (t + 2) ((m - 2) + 1) *
          N2.a136 s ((m - 2) + 1) *
          N2.a132 t:= by ring
opaque a215 (m k:ℕ) (hm:1 ≤ m) (hk:k ≤ 2*m) :
    (PmQ m).eval ((k:ℚ) / (2*m:ℚ)) =
      (PmQ m).eval (((2*m - k:ℕ):ℚ) / (2*m:ℚ)):= by
  rw [a206 m k hm hk]
  rw [a206 m (2*m-k) hm (by omega)]
  exact a214 m k hk
opaque a216:((1:Polynomial ℚ) - X).natDegree ≤ 1:= by
  compute_degree!
opaque a217 (m:ℕ) (hm:1 ≤ m) :
    ((PmQ m).comp ((1:Polynomial ℚ) - X)).natDegree ≤ 2*m:= by
  calc
    ((PmQ m).comp ((1:Polynomial ℚ) - X)).natDegree ≤ (PmQ m).natDegree * (((1:Polynomial ℚ) - X).natDegree):= Polynomial.natDegree_comp_le
    _ ≤ (2*m) * 1:= Nat.mul_le_mul (a209 m hm) a216
    _ = 2*m:= by omega
opaque a218 (N:ℕ) (hN:1 ≤ N) :
    Function.Injective (fun i:Fin (N+1)=> ((i:ℕ):ℚ) / (N:ℚ)):= by
  intro i j hij
  apply Fin.ext
  have hNq:(N:ℚ) ≠ 0:= by positivity
  have hmul:= congrArg (fun x:ℚ=> x * (N:ℚ)) hij
  field_simp [hNq] at hmul
  exact_mod_cast hmul
opaque a219 (m:ℕ) (hm:1 ≤ m) :
    PmQ m = (PmQ m).comp ((1:Polynomial ℚ) - X):= by
  let N:ℕ:= 2*m
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f:= fun i:Fin (N+1)=> ((i:ℕ):ℚ) / (N:ℚ))
  · exact a218 N (by omega)
  · intro i
    dsimp [N]
    rw [Polynomial.eval_comp]
    simp only [eval_sub,eval_one,eval_X]
    have harg:(1 - ((i:ℕ):ℚ)/(((2*m:ℕ):ℚ))) = (((2*m - (i:ℕ):ℕ):ℚ)/(((2*m:ℕ):ℚ))):= by
      have hmne:(((2*m:ℕ):ℚ)) ≠ 0:= by positivity
      field_simp [hmne]
      have hi:(i:ℕ) ≤ 2*m:= by omega
      have hcast:(((2 * m - (i:ℕ):ℕ):ℚ)) = ((2*m:ℕ):ℚ) - (i:ℚ):= by
        exact_mod_cast (Nat.cast_sub hi:(((2*m - (i:ℕ):ℕ):ℚ)) = ((2*m:ℕ):ℚ) - (i:ℚ))
      rw [hcast]
    rw [harg]
    simpa using a215 m (i:ℕ) hm (by omega)
  · rw [Fintype.card_fin]
    have h1:= a209 m hm
    have h2:= a217 m hm
    omega
opaque a220 (m:ℕ) (hm:1 ≤ m) (x:ℚ) :
    (PmQ m).eval x = (PmQ m).eval (1 - x):= by
  have h:= congrArg (fun p:Polynomial ℚ=> p.eval x) (a219 m hm)
  simpa [Polynomial.eval_comp] using h
end
end N4
open Polynomial
open scoped ComplexConjugate
noncomputable section
namespace N5
abbrev leftIndex {n:ℕ} (i:Fin n):Fin (n + 1) :=
  Fin.castSucc i
opaque a221
    (p:Polynomial ℝ) {a b:ℝ} (hab:a < b)
    (h:p.eval a * p.eval b < 0) :
    ∃ r ∈ Set.Ioo a b,p.eval r = 0:= by
  have hcont:ContinuousOn (fun x:ℝ=> p.eval x) (Set.Icc a b):= by
    exact p.continuous.continuousOn
  have hcases:(0 < p.eval a ∧ p.eval b < 0) ∨ (p.eval a < 0 ∧ 0 < p.eval b):= by
    exact mul_neg_iff.mp h
  rcases hcases with hcase | hcase
  · rcases hcase with ⟨ha,hb⟩
    have hzmem:0 ∈ Set.Icc (p.eval b) (p.eval a):= ⟨hb.le,ha.le⟩
    rcases intermediate_value_Icc' hab.le hcont hzmem with ⟨r,hrI,hr0⟩
    refine ⟨r,?_,hr0⟩
    have hne_a:r ≠ a:= by intro hra; subst r; linarith
    have hne_b:r ≠ b:= by intro hrb; subst r; linarith
    exact ⟨lt_of_le_of_ne hrI.1 (Ne.symm hne_a),lt_of_le_of_ne hrI.2 hne_b⟩
  · rcases hcase with ⟨ha,hb⟩
    have hzmem:0 ∈ Set.Icc (p.eval a) (p.eval b):= ⟨ha.le,hb.le⟩
    rcases intermediate_value_Icc hab.le hcont hzmem with ⟨r,hrI,hr0⟩
    refine ⟨r,?_,hr0⟩
    have hne_a:r ≠ a:= by intro hra; subst r; linarith
    have hne_b:r ≠ b:= by intro hrb; subst r; linarith
    exact ⟨lt_of_le_of_ne hrI.1 (Ne.symm hne_a),lt_of_le_of_ne hrI.2 hne_b⟩
opaque a222
    {n:ℕ} {a b:ℝ} {p:Polynomial ℝ}
    (hp_ne:p ≠ 0) (hp_natDegree:p.natDegree = n)
    (r:Fin n → ℝ)
    (hroot:∀ i:Fin n,p.eval (r i) = 0)
    (hr_inj:Function.Injective r)
    (hr_bounds:∀ i:Fin n,r i ∈ Set.Icc a b)
    {z:ℂ}
    (hz:(p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc a b:= by
  classical
  let q:Polynomial ℂ:= p.map (algebraMap ℝ ℂ)
  let S:Finset ℂ:= Finset.univ.image (fun i:Fin n=> (r i:ℂ))
  have h_alg_inj:Function.Injective (algebraMap ℝ ℂ) :=
    FaithfulSMul.algebraMap_injective ℝ ℂ
  have hq_ne:q ≠ 0:= by
    dsimp [q]
    exact (Polynomial.map_ne_zero_iff h_alg_inj).2 hp_ne
  have hz_mem_roots:z ∈ q.roots:= by
    rw [Polynomial.mem_roots hq_ne]
    exact hz
  have hS_card:S.card = n:= by
    have hcomp:Function.Injective (fun i:Fin n=> (r i:ℂ)):= by
      intro i j hij
      apply hr_inj
      exact h_alg_inj hij
    dsimp [S]
    simpa using (Finset.card_image_of_injective (Finset.univ:Finset (Fin n)) hcomp)
  have hz_mem_S:z ∈ S:= by
    by_contra hz_notMem_S
    have hsubset:(insert z S).val ⊆ q.roots:= by
      intro w hw
      rw [Finset.mem_val] at hw
      rw [Finset.mem_insert,Finset.mem_image] at hw
      rcases hw with rfl | ⟨i,_hi,rfl⟩
      · exact hz_mem_roots
      · rw [Polynomial.mem_roots hq_ne]
        rw [Polynomial.IsRoot]
        dsimp [q]
        simpa [hroot i] using
          (Polynomial.eval_map_apply (p:= p) (f:= algebraMap ℝ ℂ) (x:= r i))
    have hcard_le_q:(insert z S).card ≤ q.natDegree :=
      Polynomial.card_le_degree_of_subset_roots hsubset
    have hq_natDegree:q.natDegree = p.natDegree:= by
      dsimp [q]
      exact Polynomial.natDegree_map_eq_of_injective h_alg_inj p
    have hcard_insert:(insert z S).card = n + 1:= by
      rw [Finset.card_insert_of_notMem hz_notMem_S,hS_card]
    have:n + 1 ≤ n:= by
      rw [hcard_insert,hq_natDegree,hp_natDegree] at hcard_le_q
      exact hcard_le_q
    omega
  rcases Finset.mem_image.mp hz_mem_S with ⟨i,_hi,hzi⟩
  have hz_eq:z = (r i:ℂ):= hzi.symm
  constructor
  · rw [hz_eq]
    simp
  · rw [hz_eq]
    simpa using hr_bounds i
opaque a223
    {n:ℕ} {a b:ℝ} {p:Polynomial ℝ}
    (hp_ne:p ≠ 0) (hp_natDegree:p.natDegree = n)
    (x:Fin (n + 1) → ℝ) (r:Fin n → ℝ)
    (hroot:∀ i:Fin n,p.eval (r i) = 0)
    (hr_between:∀ i:Fin n,
      r i ∈ Set.Icc (x (leftIndex i)) (x (Fin.succ i)))
    (hx_bounds:∀ j:Fin (n + 1),x j ∈ Set.Icc a b)
    (hr_inj:Function.Injective r)
    {z:ℂ}
    (hz:(p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc a b:= by
  refine a222
    hp_ne hp_natDegree r hroot hr_inj ?_ hz
  intro i
  have hri:= hr_between i
  have hleft:= hx_bounds (leftIndex i)
  have hright:= hx_bounds (Fin.succ i)
  exact ⟨le_trans hleft.1 hri.1,le_trans hri.2 hright.2⟩
opaque a224
    {n:ℕ} {a b:ℝ} {p:Polynomial ℝ}
    (hp_ne:p ≠ 0) (hp_natDegree:p.natDegree = n)
    (x:Fin (n + 1) → ℝ)
    (hx_mono:StrictMono x)
    (hx_bounds:∀ j:Fin (n + 1),x j ∈ Set.Icc a b)
    (r:Fin n → ℝ)
    (hroot:∀ i:Fin n,p.eval (r i) = 0)
    (hr_between_open:∀ i:Fin n,
      r i ∈ Set.Ioo (x (leftIndex i)) (x (Fin.succ i)))
    {z:ℂ}
    (hz:(p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc a b:= by
  have hr_inj:Function.Injective r:= by
    intro i j hij
    by_contra hne
    have no_lt:∀ {i j:Fin n},r i = r j → i < j → False:= by
      intro i j hij hij_lt
      have hi_open:= hr_between_open i
      have hj_open:= hr_between_open j
      have hsucc_le_j:Fin.succ i ≤ leftIndex j:= by
        rw [leftIndex,Fin.succ_le_castSucc_iff]
        exact hij_lt
      have hx_le:x (Fin.succ i) ≤ x (leftIndex j) :=
        hx_mono.monotone hsucc_le_j
      have h1:r i < x (Fin.succ i):= hi_open.2
      have h2:x (leftIndex j) < r j:= hj_open.1
      linarith
    rcases lt_or_gt_of_ne hne with hij_lt | hji_lt
    · exact no_lt hij hij_lt
    · exact no_lt hij.symm hji_lt
  have hr_between_closed:∀ i:Fin n,
      r i ∈ Set.Icc (x (leftIndex i)) (x (Fin.succ i)):= by
    intro i
    exact ⟨(hr_between_open i).1.le,(hr_between_open i).2.le⟩
  exact a223
    hp_ne hp_natDegree x r hroot hr_between_closed hx_bounds hr_inj hz
opaque a225
    {n:ℕ} {a b:ℝ} {p:Polynomial ℝ}
    (hp_ne:p ≠ 0) (hp_natDegree:p.natDegree = n)
    (x:Fin (n + 1) → ℝ)
    (hx_mono:StrictMono x)
    (hx_bounds:∀ j:Fin (n + 1),x j ∈ Set.Icc a b)
    (hx_alt:∀ i:Fin n,
      p.eval (x (leftIndex i)) * p.eval (x (Fin.succ i)) < 0)
    {z:ℂ}
    (hz:(p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc a b:= by
  classical
  have hroot_exists:∀ i:Fin n,
      ∃ r ∈ Set.Ioo (x (leftIndex i)) (x (Fin.succ i)),p.eval r = 0:= by
    intro i
    have hlt:x (leftIndex i) < x (Fin.succ i):= hx_mono (by
      rw [leftIndex,Fin.castSucc_lt_succ_iff])
    exact a221 p hlt (hx_alt i)
  let r:Fin n → ℝ:= fun i=> Classical.choose (hroot_exists i)
  have hroot:∀ i:Fin n,p.eval (r i) = 0:= by
    intro i
    exact (Classical.choose_spec (hroot_exists i)).2
  have hr_between_open:∀ i:Fin n,
      r i ∈ Set.Ioo (x (leftIndex i)) (x (Fin.succ i)):= by
    intro i
    exact (Classical.choose_spec (hroot_exists i)).1
  exact a224
    hp_ne hp_natDegree x hx_mono hx_bounds r hroot hr_between_open hz
noncomputable def a226 (N:ℕ) (j:Fin (N + 1)):ℝ:= (j:ℕ) / (N:ℝ)
opaque a227 (N:ℕ) (hN:1 ≤ N):StrictMono (a226 N):= by
  intro i j hij
  unfold a226
  have hden:(0:ℝ) < N:= by exact_mod_cast (Nat.pos_of_ne_zero (by omega:N ≠ 0))
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) hden
opaque a228 (N:ℕ) (hN:1 ≤ N) (j:Fin (N + 1)):a226 N j ∈ Set.Icc (0:ℝ) 1:= by
  unfold a226
  have hden:(0:ℝ) < N:= by exact_mod_cast (Nat.pos_of_ne_zero (by omega:N ≠ 0))
  constructor
  · positivity
  · have hj:(j:ℕ) ≤ N:= by omega
    have hjr:(j:ℝ) ≤ (N:ℝ):= by exact_mod_cast hj
    exact (div_le_one hden).2 hjr
opaque a229 (N:ℕ) (hN:1 ≤ N) (i:Fin N) :
    a226 N (leftIndex i) = (i:ℝ) / (N:ℝ):= by rfl
opaque a230 (N:ℕ) (hN:1 ≤ N) (i:Fin N) :
    a226 N (Fin.succ i) = ((i:ℕ) + 1:ℝ) / (N:ℝ):= by
  simp [a226,Fin.val_succ]
opaque a231
    {N:ℕ} (hN:1 ≤ N) {p:Polynomial ℝ}
    (hp_ne:p ≠ 0) (hp_natDegree:p.natDegree = N)
    (hgrid:∀ i:Fin N,
      p.eval ((i:ℝ) / (N:ℝ)) * p.eval (((i:ℕ) + 1:ℝ) / (N:ℝ)) < 0)
    {z:ℂ} (hz:(p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (0:ℝ) 1:= by
  refine a225 hp_ne hp_natDegree (a226 N)
    (a227 N hN) (a228 N hN) ?_ hz
  intro i
  rw [a229 N hN i,a230 N hN i]
  exact hgrid i
end N5
open Polynomial
open scoped BigOperators
namespace N6
noncomputable section
open N4
opaque a232
    {N:ℕ} (hN:1 ≤ N) {p:Polynomial ℝ}
    (hp_le:p.natDegree ≤ N)
    (hgrid:∀ i:Fin N,
      p.eval ((i:ℝ) / (N:ℝ)) * p.eval (((i:ℕ) + 1:ℝ) / (N:ℝ)) < 0) :
    p.natDegree = N:= by
  classical
  have hp_ne:p ≠ 0:= by
    intro hp
    have h:= hgrid ⟨0,hN⟩
    simp [hp] at h
  have hroot_exists:∀ i:Fin N,
      ∃ r ∈ Set.Ioo ((i:ℝ) / (N:ℝ)) (((i:ℕ) + 1:ℝ) / (N:ℝ)),p.eval r = 0:= by
    intro i
    have hlt:(i:ℝ) / (N:ℝ) < (((i:ℕ) + 1:ℝ) / (N:ℝ)):= by
      have hNpos:(0:ℝ) < N:= by exact_mod_cast hN
      gcongr
      norm_num
    exact N5.a221 p hlt (hgrid i)
  let r:Fin N → ℝ:= fun i=> Classical.choose (hroot_exists i)
  have hroot:∀ i:Fin N,p.eval (r i) = 0:= by
    intro i
    exact (Classical.choose_spec (hroot_exists i)).2
  have hr_between:∀ i:Fin N,
      r i ∈ Set.Ioo ((i:ℝ) / (N:ℝ)) (((i:ℕ) + 1:ℝ) / (N:ℝ)):= by
    intro i
    exact (Classical.choose_spec (hroot_exists i)).1
  have hr_inj:Function.Injective r:= by
    intro i j hij
    by_contra hne
    wlog hijlt:i < j generalizing i j with H
    · have hjilt:j < i:= by exact lt_of_le_of_ne (le_of_not_gt hijlt) (Ne.symm hne)
      exact H hij.symm (Ne.symm hne) hjilt
    have hi:= hr_between i
    have hj:= hr_between j
    have hsucc_le:((i:ℕ)+1:ℝ) / (N:ℝ) ≤ (j:ℝ) / (N:ℝ):= by
      have hNpos:(0:ℝ) < N:= by exact_mod_cast hN
      gcongr
      exact_mod_cast (Fin.val_add_one_le_of_lt hijlt)
    have h1:r i < ((i:ℕ)+1:ℝ) / (N:ℝ):= hi.2
    have h2:(j:ℝ) / (N:ℝ) < r i:= by simpa [hij] using hj.1
    linarith
  let S:Finset ℝ:= Finset.univ.image r
  have hS_card:S.card = N:= by
    dsimp [S]
    simpa using (Finset.card_image_of_injective (Finset.univ:Finset (Fin N)) hr_inj)
  have hsubset:S.val ⊆ p.roots:= by
    intro x hx
    rw [Finset.mem_val,Finset.mem_image] at hx
    rcases hx with ⟨i,_,rfl⟩
    rw [Polynomial.mem_roots hp_ne]
    exact hroot i
  have hcard_le:S.card ≤ p.natDegree:= Polynomial.card_le_degree_of_subset_roots hsubset
  omega
def PmR (m:ℕ):Polynomial ℝ:= (N4.PmQ m).map (algebraMap ℚ ℝ)
opaque a233 (m:ℕ) (x:ℚ) :
    (PmR m).eval (x:ℝ) = (N4.PmQ m).eval x:= by
  unfold PmR
  exact Polynomial.eval_map_apply (f:= algebraMap ℚ ℝ) (p:= N4.PmQ m) (x:= x)
opaque a234 (m i:ℕ) (hm:1 ≤ m) (hi:i < 2*m) :
    (PmR m).eval ((i:ℝ)/(2*m:ℝ)) *
      (PmR m).eval (((i+1:ℕ):ℝ)/(2*m:ℝ)) < 0:= by
  have hq:= N4.a207 m i hm hi
  have hden:(2 * (m:ℚ)) ≠ 0:= by positivity
  have hleft:((i:ℝ)/(2*m:ℝ)) = (((i:ℚ)/(2*m:ℚ):ℚ):ℝ):= by norm_num
  have hright:(((i+1:ℕ):ℝ)/(2*m:ℝ)) = (((((i+1:ℕ):ℚ)/(2*m:ℚ)):ℚ):ℝ):= by norm_num
  rw [hleft,hright,a233,a233]
  exact_mod_cast hq
opaque a235 (m:ℕ) (hm:1 ≤ m):(PmR m).natDegree = 2*m:= by
  apply a232 (N:= 2*m) (by omega)
  · unfold PmR
    rw [Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective ℚ ℝ)]
    exact N4.a209 m hm
  · intro i
    simpa using a234 m i hm i.2
opaque a236 (m:ℕ) (hm:1 ≤ m):(PmR m).degree = ((2*m:ℕ):WithBot ℕ):= by
  have hnat:= a235 m hm
  have hpne:PmR m ≠ 0:= by
    intro hp
    simp [hp] at hnat
    omega
  exact (Polynomial.degree_eq_iff_natDegree_eq hpne).2 hnat
opaque a237 (m:ℕ) (hm:1 ≤ m) :
    PmR m = (PmR m).comp ((1:Polynomial ℝ) - X):= by
  have hq:= congrArg (fun p:Polynomial ℚ=> p.map (algebraMap ℚ ℝ)) (N4.a219 m hm)
  unfold PmR
  simpa [Polynomial.map_comp] using hq
opaque a238 (m:ℕ) (hm:1 ≤ m) (x:ℝ) :
    (PmR m).eval x = (PmR m).eval (1 - x):= by
  have h:= congrArg (fun p:Polynomial ℝ=> p.eval x) (a237 m hm)
  simpa [Polynomial.eval_comp] using h
opaque a239 (m:ℕ) (hm:1 ≤ m) :
    ∀ z:ℂ,((PmR m).map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (0:ℝ) 1:= by
  intro z hz
  exact N5.a231
    (N:= 2*m) (by omega) (by
      intro hp
      have hdeg:= a235 m hm
      simp [hp] at hdeg
      omega) (a235 m hm)
    (fun i=> by simpa using a234 m i hm i.2) hz
end
end N6
open Polynomial
open scoped BigOperators
namespace N7
noncomputable section
opaque a240 {α:Type*} (s:Finset α) (f:α → Polynomial ℝ) (n:ℕ) :
    (s.sum f).coeff n = s.sum (fun a=> (f a).coeff n):= by
  classical
  induction s using Finset.induction_on with
  | empty=> simp
  | insert a s has ih=> simp [has,ih,Polynomial.coeff_add]
def a241:Polynomial ℝ:= Polynomial.C (1/2) * ((1:Polynomial ℝ) + X)
def RmR (m:ℕ):Polynomial ℝ :=
  (N6.PmR (2*m)).comp a241
def QmR (m:ℕ):Polynomial ℝ :=
  (Finset.range (2*m + 1)).sum
    (fun i=> Polynomial.C ((RmR m).coeff (2*i)) * X^i)
opaque a242:a241.natDegree = 1:= by
  unfold a241
  compute_degree!
opaque a243:a241.leadingCoeff ≠ 0:= by
  rw [Polynomial.leadingCoeff,a242]
  unfold a241
  norm_num [Polynomial.coeff_C_mul,Polynomial.coeff_add,Polynomial.coeff_one]
opaque a244 (m:ℕ) (hm:1 ≤ m):(RmR m).natDegree = 4*m:= by
  unfold RmR
  have hpdeg:(N6.PmR (2*m)).natDegree = 2*(2*m) :=
    N6.a235 (2*m) (by omega)
  rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
  · rw [hpdeg,a242]
    omega
  · apply mul_ne_zero
    · exact Polynomial.leadingCoeff_ne_zero.mpr (by
        intro hp
        have hnat:= hpdeg
        simp [hp] at hnat
        omega)
    · exact pow_ne_zero _ a243
opaque a245 (m:ℕ):(QmR m).natDegree ≤ 2*m:= by
  classical
  unfold QmR
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s:= Finset.range (2*m + 1))
    (f:= fun i=> Polynomial.C ((RmR m).coeff (2*i)) * X^i) ?_
  intro i hi
  rw [Finset.mem_range] at hi
  calc
    (Polynomial.C ((RmR m).coeff (2 * i)) * X ^ i).natDegree ≤ i :=
      Polynomial.natDegree_C_mul_X_pow_le _ _
    _ ≤ 2*m:= by omega
opaque a246 (m i:ℕ) (hi:i < 2*m + 1) :
    (QmR m).coeff i = (RmR m).coeff (2*i):= by
  classical
  unfold QmR
  change ((Finset.range (2*m + 1)).sum
      (fun x=> Polynomial.C ((RmR m).coeff (2*x)) * X^x:ℕ → Polynomial ℝ)).coeff i =
    (RmR m).coeff (2*i)
  rw [a240]
  have hsingle :
      (Finset.range (2*m + 1)).sum
        (fun x=> (Polynomial.C ((RmR m).coeff (2*x)) * X^x:Polynomial ℝ).coeff i)
        = (Polynomial.C ((RmR m).coeff (2*i)) * X^i:Polynomial ℝ).coeff i:= by
    rw [Finset.sum_eq_single i]
    · intro b hb hbi
      rw [Polynomial.coeff_C_mul]
      simp [Polynomial.coeff_X_pow,Ne.symm hbi]
    · intro hi_not
      exact (hi_not (Finset.mem_range.mpr hi)).elim
  rw [hsingle]
  simp
opaque a247 (m:ℕ) :
    (QmR m).coeff (2*m) = (RmR m).coeff (4*m):= by
  simpa [mul_assoc,show 2 * (2*m) = 4*m by omega] using
    a246 m (2*m) (by omega)
opaque a248 (m:ℕ) (hm:1 ≤ m):(QmR m).natDegree = 2*m:= by
  apply le_antisymm (a245 m)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [a247]
  have hnatR:= a244 m hm
  have hRne:RmR m ≠ 0:= by
    intro hR
    simp [hR] at hnatR
    omega
  rw [← hnatR]
  exact Polynomial.leadingCoeff_ne_zero.mpr hRne
opaque a249 (m:ℕ) (hm:1 ≤ m) :
    (QmR m).degree = ((2*m:ℕ):WithBot ℕ):= by
  have hnat:= a248 m hm
  have hpne:QmR m ≠ 0:= by
    intro hp
    simp [hp] at hnat
    omega
  exact (Polynomial.degree_eq_iff_natDegree_eq hpne).2 hnat
opaque a250:a241.comp (-(X:Polynomial ℝ)) = (1:Polynomial ℝ) - a241:= by
  ext n
  unfold a241
  simp [Polynomial.mul_comp,Polynomial.coeff_C_mul,Polynomial.coeff_sub,
    Polynomial.coeff_add,Polynomial.coeff_one]
  by_cases hn0:n = 0
  · subst hn0
    norm_num
  · by_cases hn1:n = 1
    · subst hn1
      norm_num
    · simp [Polynomial.coeff_X,hn0]
opaque a251 (m:ℕ) (hm:1 ≤ m) :
    RmR m = (RmR m).comp (-(X:Polynomial ℝ)):= by
  unfold RmR
  let P:= N6.PmR (2*m)
  have hsymm:P = P.comp ((1:Polynomial ℝ) - X) :=
    N6.a237 (2*m) (by omega)
  calc
    P.comp a241 = (P.comp ((1:Polynomial ℝ) - X)).comp a241:= by rw [← hsymm]
    _ = P.comp (((1:Polynomial ℝ) - X).comp a241):= by rw [Polynomial.comp_assoc]
    _ = P.comp ((1:Polynomial ℝ) - a241):= by simp [Polynomial.sub_comp]
    _ = P.comp (a241.comp (-(X:Polynomial ℝ))):= by rw [a250]
    _ = (P.comp a241).comp (-(X:Polynomial ℝ)):= by rw [Polynomial.comp_assoc]
opaque a252 (k n:ℕ):((-(X:Polynomial ℝ))^k).coeff n = if n = k then (-1:ℝ)^k else 0:= by
  have hp:(-(X:Polynomial ℝ))^k = Polynomial.C ((-1:ℝ)^k) * X^k:= by
    induction k with
    | zero=> simp
    | succ k ih =>
        rw [pow_succ,ih]
        simp [pow_succ]
        ring
  rw [hp,Polynomial.C_mul']
  by_cases h:n = k
  · subst n
    simp
  · simp [Polynomial.coeff_X_pow,h]
opaque a253 (p:Polynomial ℝ) (n:ℕ) :
    (p.comp (-(X:Polynomial ℝ))).coeff n = (-1:ℝ)^n * p.coeff n:= by
  induction p using Polynomial.induction_on' with
  | monomial k a =>
      by_cases hnk:n = k
      · subst n
        simp [Polynomial.monomial_comp,a252,mul_comm]
      · have hkn:k ≠ n:= by omega
        simp [Polynomial.monomial_comp,a252,Polynomial.coeff_monomial,hnk,hkn]
  | add p q hp hq =>
      simp [Polynomial.add_comp,Polynomial.coeff_add,hp,hq,mul_add]
opaque a254 (m:ℕ) (hm:1 ≤ m) (i:ℕ) :
    (RmR m).coeff (2*i+1) = 0:= by
  have h:= congrArg (fun p:Polynomial ℝ=> p.coeff (2*i+1)) (a251 m hm)
  change (RmR m).coeff (2*i+1) = ((RmR m).comp (-(X:Polynomial ℝ))).coeff (2*i+1) at h
  rw [a253] at h
  have hpow:(-1:ℝ)^(2*i+1) = -1:= by
    exact (show Odd (2*i+1) from ⟨i,rfl⟩).neg_one_pow
  rw [hpow] at h
  linarith
opaque a255 (i n:ℕ) :
    (((X:Polynomial ℝ)^2)^i).coeff n = if n = 2*i then 1 else 0:= by
  have hp:((X:Polynomial ℝ)^2)^i = X^(2*i):= by
    rw [← pow_mul]
  rw [hp]
  by_cases h:n = 2*i
  · subst n
    simp
  · simp [Polynomial.coeff_X_pow,h]
opaque a256 (m n:ℕ) :
    ((QmR m).comp (X^2)).coeff n = if ∃ i,i < 2*m+1 ∧ n = 2*i then (RmR m).coeff n else 0:= by
  classical
  unfold QmR
  rw [Polynomial.sum_comp]
  rw [a240]
  by_cases hex:∃ i,i < 2*m+1 ∧ n = 2*i
  · rcases hex with ⟨i,hi,rfl⟩
    rw [if_pos ⟨i,hi,rfl⟩]
    rw [Finset.sum_eq_single i]
    · simp [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.coeff_C_mul,
        a255]
    · intro b hb hbi
      rw [Finset.mem_range] at hb
      have hne:2*i ≠ 2*b:= by omega
      simp [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.coeff_C_mul,
        a255,hne]
    · intro hi_not
      exact (hi_not (Finset.mem_range.mpr hi)).elim
  · rw [if_neg hex]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have hne:n ≠ 2*i:= by
      intro hn
      exact hex ⟨i,hi,hn⟩
    simp [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.coeff_C_mul,
      a255,hne]
opaque a257 (m:ℕ) (hm:1 ≤ m) :
    (QmR m).comp (X^2) = RmR m:= by
  ext n
  rw [a256]
  by_cases heven:∃ i,n = 2*i
  · rcases heven with ⟨i,rfl⟩
    by_cases hi:i < 2*m+1
    · rw [if_pos ⟨i,hi,rfl⟩]
    · rw [if_neg]
      · rw [coeff_eq_zero_of_natDegree_lt]
        rw [a244 m hm]
        omega
      · intro h
        rcases h with ⟨j,hj,hji⟩
        omega
  · have hodd:∃ i,n = 2*i+1:= by
      rcases Nat.even_or_odd n with ⟨i,hi⟩ | ⟨i,hi⟩
      · exact (heven ⟨i,by omega⟩).elim
      · exact ⟨i,by omega⟩
    rcases hodd with ⟨i,rfl⟩
    rw [if_neg]
    · exact (a254 m hm i).symm
    · intro h
      rcases h with ⟨j,hj,hbad⟩
      omega
opaque a258 (m:ℕ) (hm:1 ≤ m) (z:ℂ) :
    ((QmR m).map (algebraMap ℝ ℂ)).eval (z^2) = ((RmR m).map (algebraMap ℝ ℂ)).eval z:= by
  have hpoly:= congrArg (fun p:Polynomial ℝ=> p.map (algebraMap ℝ ℂ)) (a257 m hm)
  have hpoly':((QmR m).map (algebraMap ℝ ℂ)).comp (X^2) = (RmR m).map (algebraMap ℝ ℂ):= by
    simpa [Polynomial.map_comp] using hpoly
  have heval:= congrArg (fun p:Polynomial ℂ=> p.eval z) hpoly'
  simpa [Polynomial.eval_comp] using heval
opaque a259 (m:ℕ) (hm:1 ≤ m) :
    ∀ z:ℂ,((RmR m).map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (-1:ℝ) 1:= by
  intro z hz
  unfold RmR at hz
  rw [Polynomial.map_comp,Polynomial.eval_comp] at hz
  have harg :
      ((a241.map (algebraMap ℝ ℂ)).eval z) = ((1 + z) / 2:ℂ):= by
    unfold a241
    simp
    ring
  rw [harg] at hz
  have hroot:= N6.a239 (2*m) (by omega) ((1 + z) / 2) hz
  rcases hroot with ⟨him,hI⟩
  have hz_im:z.im = 0:= by
    have him_calc:(((1 + z) / 2:ℂ).im) = z.im / 2:= by simp
    linarith
  refine ⟨hz_im,?_⟩
  have hre_calc:(((1 + z) / 2:ℂ).re) = (1 + z.re) / 2:= by simp
  constructor <;> nlinarith [hI.1,hI.2,hre_calc]
opaque a260 (m:ℕ) (hm:1 ≤ m)
    (h_eval:∀ z:ℂ,
      ((QmR m).map (algebraMap ℝ ℂ)).eval (z^2) =
        ((RmR m).map (algebraMap ℝ ℂ)).eval z) :
    ∀ z:ℂ,((QmR m).map (algebraMap ℝ ℂ)).eval (z^2) = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (-1:ℝ) 1:= by
  intro z hz
  apply a259 m hm z
  rw [← h_eval z]
  exact hz
opaque a261 (m:ℕ) (hm:1 ≤ m) :
    ∀ z:ℂ,((QmR m).map (algebraMap ℝ ℂ)).eval (z^2) = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (-1:ℝ) 1:= by
  exact a260 m hm (a258 m hm)
end
end N7
open Polynomial
open scoped BigOperators
namespace N8
noncomputable section
def a262 (start len:ℕ):ℚ :=
  (Finset.range len).prod (fun i=> N0.A ((start + i:ℕ):ℚ))
def Kq (s:ℚ) (len:ℕ):ℚ :=
  (N1.a77 (Polynomial.C s) len).eval 0
opaque a263 (x:ℚ):(N1.a69 N1.a66 (Polynomial.C x)).eval 0 = N0.B x:= by
  simp [N1.a69,N1.a66,N0.B]
opaque a264 (s:ℚ):Kq s 0 = 1:= by simp [Kq,N1.a77]
opaque a265 (s:ℚ):Kq s 1 = N0.B s:= by simp [Kq,N1.a77,a263]
opaque a266 (s:ℚ) (r:ℕ) :
    Kq s (r+2) = N0.B (s + (r+1:ℚ)) * Kq s (r+1)
      + N0.D (s + (r+1:ℚ)) * N0.A (s + (r:ℚ)) * Kq s r:= by
  unfold Kq
  rw [N1.a78]
  simp [N1.a76,N1.a69,N1.a65,
    N1.a66,N1.a67,N0.A,
    N0.B,N0.D]
opaque a267 (start len:ℕ) :
    a262 start (len+1) = a262 start len * N0.A ((start + len:ℕ):ℚ):= by
  unfold a262
  rw [Finset.prod_range_succ]
opaque a268 (start len:ℕ) (hstart:1 ≤ start):a262 start len ≠ 0:= by
  unfold a262
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [Finset.mem_range] at hi
  exact N0.a50 (start+i) (by omega)
opaque a269 (P A0 A1 B D K0 K1:ℚ)
    (hP:P ≠ 0) (hA0:A0 ≠ 0) (hA1:A1 ≠ 0) :
    D / A1 * (K0 / P) + B / A1 * (K1 / (P * A0)) =
      (B * K1 + D * A0 * K0) / ((P * A0) * A1):= by
  field_simp [hP,hA0,hA1]
  ring
opaque a270 (start len:ℕ) :
    let M:= N0.a56 (len+1) start
    M 0 1 = Kq ((start + 1:ℕ):ℚ) len / a262 (start+1) len ∧
    M 1 1 = Kq ((start + 1:ℕ):ℚ) (len+1) / a262 (start+1) (len+1):= by
  induction len with
  | zero =>
      constructor
      · simp [N0.a56,N0.a52,
          Matrix.mul_apply,Fin.sum_univ_two,a262,a264]
      · simp [N0.a56,N0.a52,
          Matrix.mul_apply,Fin.sum_univ_two,a262,a265]
  | succ len ih =>
      rcases ih with ⟨h01,h11⟩
      change
        let M:= N0.a52 (start + (len + 1)) * N0.a56 (len + 1) start
        M 0 1 = Kq ((start + 1:ℕ):ℚ) (len + 1) / a262 (start + 1) (len + 1) ∧
        M 1 1 = Kq ((start + 1:ℕ):ℚ) (len + 1 + 1) / a262 (start + 1) (len + 1 + 1)
      constructor
      · simp [N0.a52,Matrix.mul_apply,Fin.sum_univ_two,h11]
      · simp [N0.a52,Matrix.mul_apply,Fin.sum_univ_two,h01,h11]
        have hP0:a262 (start+1) len ≠ 0:= a268 (start+1) len (by omega)
        have hAprev:N0.A (((start + 1) + len:ℕ):ℚ) ≠ 0 :=
          N0.a50 ((start + 1) + len) (by omega)
        have hAnew:N0.A (((start + (len + 1)) + 1:ℕ):ℚ) ≠ 0 :=
          N0.a50 ((start + (len + 1)) + 1) (by omega)
        have hAnew_q:N0.A (2 + (start:ℚ) + (len:ℚ)) ≠ 0:= by
          convert (N0.a50 (2 + start + len) (by omega)) using 2
          norm_num [Nat.cast_add]
        have hAnew_nat_comm:N0.A (((2 + len + start):ℕ):ℚ) ≠ 0 :=
          N0.a50 (2 + len + start) (by omega)
        have hAnew_nat_start:N0.A (((2 + start + len):ℕ):ℚ) ≠ 0 :=
          N0.a50 (2 + start + len) (by omega)
        rw [a266]
        rw [a267 (start+1) (len+1),a267 (start+1) len]
        convert
          a269 (a262 (start+1) len)
            (N0.A (((start + 1) + len:ℕ):ℚ))
            (N0.A (((start + (len + 1)) + 1:ℕ):ℚ))
            (N0.B (((start + (len + 1)) + 1:ℕ):ℚ))
            (N0.D (((start + (len + 1)) + 1:ℕ):ℚ))
            (Kq ((start + 1:ℕ):ℚ) len)
            (Kq ((start + 1:ℕ):ℚ) (len+1)) hP0 hAprev hAnew using 1 <;>
          norm_num [Nat.cast_add] <;>
          field_simp [hP0,hAprev,hAnew,hAnew_q,hAnew_nat_comm,hAnew_nat_start] <;>
          ring_nf
opaque a271 (start m:ℕ) (hm:1 ≤ m) :
    N0.a56 m start 0 1 =
      Kq ((start + 1:ℕ):ℚ) (m-1) / a262 (start+1) (m-1):= by
  rcases m with _ | l
  · omega
  · simpa using (a270 start l).1
opaque a272 (x:ℚ) (len:ℕ) :
    Kq (x + 1) len = (N1.a77 (X + 1) len).eval x:= by
  induction len using Nat.strong_induction_on with
  | h len ih =>
      rcases len with _ | _ | r
      · simp [Kq,N1.a77]
      · simp [Kq,N1.a77,N1.a69]
      · rw [a266,N1.a78]
        rw [ih (r+1) (by omega),ih r (by omega)]
        simp [N1.a76,N1.a69,N1.a65,
          N1.a66,N1.a67,N0.A,
          N0.B,N0.D]
opaque a273 (m j:ℕ) (hm:1 ≤ m) :
    N0.a58 m j 0 1 =
      Kq (((m*j) + 1:ℕ):ℚ) (m-1) / a262 (m*j+1) (m-1):= by
  unfold N0.a58
  simpa [Nat.mul_comm,Nat.mul_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    (a271 (m*j) m hm)
opaque a274 (m n:ℕ) (hn:1 ≤ n) :
    (N4.PmQ m).eval (n:ℚ) =
      (N1.a93 (m-1)).eval ((m * (n-1):ℕ):ℚ):= by
  unfold N4.PmQ
  rw [Polynomial.eval_comp]
  congr 1
  simp only [Polynomial.eval_mul,Polynomial.eval_natCast,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_one]
  rw [Nat.cast_mul,Nat.cast_sub hn]
  ring
opaque a275 (m n:ℕ) (hn:1 ≤ n) :
    ((N1.a86 X (m-1)).eval ((m * (n-1):ℕ):ℚ)) *
        (N4.PmQ m).eval (n:ℚ) =
      ((N1.a70 X).eval ((m * (n-1):ℕ):ℚ)) *
        Kq (((m * (n-1)) + 1:ℕ):ℚ) (m-1):= by
  have hmul:= congrArg
    (fun p:Polynomial ℚ=> p.eval ((m * (n-1):ℕ):ℚ))
    (N1.a94 (m-1))
  simp only [Polynomial.eval_mul] at hmul
  rw [a274 m n hn]
  rw [show (((m * (n-1)) + 1:ℕ):ℚ) = (((m * (n-1):ℕ):ℚ) + 1) by norm_num]
  rw [a272]
  exact hmul
opaque a276 (x:ℚ) :
    N1.a65.eval x = N0.A x:= by
  simp [N1.a65,N0.A]
opaque a277 (x:ℚ) :
    N0.A (x + 1) =
      ((2 * (x + 1) + 1) * (2 * (x + 1) + 2)) *
        (N1.a70 X).eval x:= by
  have h:= congrArg (fun p:Polynomial ℚ=> p.eval (x + 1))
    (N1.a74 X)
  simp [N1.a69,a276] at h
  rw [h]
  congr 1
  simp [N1.a70,N1.a69,N1.a68]
def a278 (x:ℚ) (i:ℕ):ℚ :=
  (2 * (x + 1 + (i:ℚ)) + 1) * (2 * (x + 1 + (i:ℚ)) + 2)
def a279 (x:ℚ) (L:ℕ):ℚ :=
  (Finset.range L).prod (fun i=> a278 x i)
def a280 (m n L:ℕ):ℚ :=
  a279 (((m * (n - 1):ℕ):ℚ)) L
def a281 (m n:ℕ):ℚ :=
  let x:ℚ:= ((m * (n - 1):ℕ):ℚ)
  (Finset.range m).prod (fun i=> a278 x (m - 1 + i))
def a282 (m n:ℕ):ℚ :=
  (Finset.Ioc 0 (2*m)).prod (fun k=> ((2*m*n:ℚ) - (k:ℚ)))
def a283 (m n:ℕ):ℚ :=
  (Finset.Ioc 0 (2*m)).prod (fun k=> ((2*m*n:ℚ) + (k:ℚ)))
def a284 (m n:ℕ):ℚ :=
  a281 m n * (N1.a70 X).eval (((m * (n - 1):ℕ):ℚ)) *
    a280 m n (m - 1)
opaque a285 (m n:ℕ) :
    a281 m n * a280 m n (m-1) = a280 m n (2*m-1):= by
  unfold a281 a280 a279 a278
  let x:ℚ:= ((m * (n - 1):ℕ):ℚ)
  change
    ((Finset.range m).prod (fun i =>
        (2 * (x + 1 + ((m - 1 + i:ℕ):ℚ)) + 1) *
          (2 * (x + 1 + ((m - 1 + i:ℕ):ℚ)) + 2))) *
      ((Finset.range (m - 1)).prod (fun i =>
        (2 * (x + 1 + (i:ℚ)) + 1) * (2 * (x + 1 + (i:ℚ)) + 2))) =
      ((Finset.range (2*m - 1)).prod (fun i =>
        (2 * (x + 1 + (i:ℚ)) + 1) * (2 * (x + 1 + (i:ℚ)) + 2)))
  have hsplit:= (Finset.prod_range_add (fun i =>
    (2 * (x + 1 + (i:ℚ)) + 1) * (2 * (x + 1 + (i:ℚ)) + 2)) (m-1) m).symm
  have hlen:(m - 1) + m = 2*m - 1:= by omega
  rw [← hlen,← hsplit]
  ring
opaque a286 (x:ℚ) (len:ℕ) :
    (Finset.range len).prod
        (fun i=> N0.A (x + 1 + (i:ℚ))) =
      ((Finset.range len).prod
          (fun i=> (2 * (x + 1 + (i:ℚ)) + 1) * (2 * (x + 1 + (i:ℚ)) + 2))) *
        (N1.a86 X len).eval x:= by
  unfold N1.a86
  rw [Polynomial.eval_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [show x + 1 + (i:ℚ) = x + i + 1 by ring]
  rw [a277 (x + i)]
  have hq:(N1.a70 X).eval (x + i) =
      (N1.a70 (N1.a76 X i)).eval x:= by
    simp [N1.a70,N1.a69,N1.a68,
      N1.a76]
  rw [← hq]
opaque a287 (start len:ℕ) :
    a262 (start+1) len =
      ((Finset.range len).prod
          (fun i=> (2 * (((start:ℕ):ℚ) + 1 + (i:ℚ)) + 1) *
            (2 * (((start:ℕ):ℚ) + 1 + (i:ℚ)) + 2))) *
        (N1.a86 X len).eval (start:ℚ):= by
  unfold a262
  calc
    (Finset.range len).prod (fun i=> N0.A (((start + 1) + i:ℕ):ℚ))
        = (Finset.range len).prod (fun i=> N0.A ((start:ℚ) + 1 + (i:ℚ))):= by
          apply Finset.prod_congr rfl
          intro i hi
          congr 1
          norm_num [Nat.cast_add]
    _ = ((Finset.range len).prod
          (fun i=> (2 * (((start:ℕ):ℚ) + 1 + (i:ℚ)) + 1) *
            (2 * (((start:ℕ):ℚ) + 1 + (i:ℚ)) + 2))) *
        (N1.a86 X len).eval (start:ℚ) :=
          a286 (start:ℚ) len
opaque a288 (start len:ℕ) :
    a262 (start+1) len =
      a279 (start:ℚ) len * (N1.a86 X len).eval (start:ℚ):= by
  simpa [a279,a278] using a287 start len
opaque a289
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    ((N1.a70 X).eval ((m * (n-1):ℕ):ℚ)) *
        N0.a58 m (n-1) 0 1 *
          a262 (m*(n-1)+1) (m-1) =
      ((N1.a86 X (m-1)).eval ((m * (n-1):ℕ):ℚ)) *
        (N4.PmQ m).eval (n:ℚ):= by
  have hblock:= a273 m (n-1) hm
  have hA:a262 (m*(n-1)+1) (m-1) ≠ 0 :=
    a268 (m*(n-1)+1) (m-1) (by omega)
  have hclear:= a275 m n hn
  rw [hblock]
  field_simp [hA]
  rw [hclear]
opaque a290
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    ((N1.a70 X).eval ((m * (n-1):ℕ):ℚ)) *
        a280 m n (m-1) * N0.a58 m (n-1) 0 1 =
      (N4.PmQ m).eval (n:ℚ):= by
  let x:ℚ:= ((m * (n-1):ℕ):ℚ)
  let Q:ℚ:= (N1.a86 X (m-1)).eval x
  let L:ℚ:= a280 m n (m-1)
  let q:ℚ:= (N1.a70 X).eval x
  let b:ℚ:= N0.a58 m (n-1) 0 1
  let P:ℚ:= (N4.PmQ m).eval (n:ℚ)
  have hclear:q * b * a262 (m*(n-1)+1) (m-1) = Q * P:= by
    simpa [x,Q,q,b,P] using
      a289 m n hm hn
  have hAfac:a262 (m*(n-1)+1) (m-1) = L * Q:= by
    simpa [x,Q,L,a280] using
      a288 (m*(n-1)) (m-1)
  have hAne:a262 (m*(n-1)+1) (m-1) ≠ 0 :=
    a268 (m*(n-1)+1) (m-1) (by omega)
  have hLQne:L * Q ≠ 0:= by
    rw [← hAfac]
    exact hAne
  have hQne:Q ≠ 0:= (mul_ne_zero_iff.mp hLQne).2
  have hmul:(q * L * b) * Q = P * Q:= by
    calc
      (q * L * b) * Q = q * b * (L * Q):= by ring
      _ = q * b * a262 (m*(n-1)+1) (m-1):= by rw [hAfac]
      _ = Q * P:= hclear
      _ = P * Q:= by ring
  have hmain:q * L * b = P:= by
    exact mul_right_cancel₀ hQne hmul
  simpa [x,q,L,b,P] using hmain
opaque a291
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    a284 m n * N0.a58 m (n-1) 0 1 =
      a281 m n * (N4.PmQ m).eval (n:ℚ):= by
  have h:= a290 m n hm hn
  unfold a284
  calc
    (a281 m n * (N1.a70 X).eval ↑(m * (n - 1)) * a280 m n (m - 1)) *
        N0.a58 m (n - 1) 0 1
        = a281 m n *
            (((N1.a70 X).eval ↑(m * (n - 1)) * a280 m n (m - 1) *
              N0.a58 m (n - 1) 0 1)):= by ring
    _ = a281 m n * (N4.PmQ m).eval (n:ℚ):= by rw [h]
opaque a292 (m n:ℕ) (hn:1 ≤ n) :
    (N4.PmQ (2*m)).eval (((n:ℚ) + 1) / 2) =
      (N1.a93 (2*m-1)).eval ((m * (n-1):ℕ):ℚ):= by
  unfold N4.PmQ
  rw [Polynomial.eval_comp]
  congr 1
  simp only [Polynomial.eval_mul,Polynomial.eval_natCast,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_one]
  rw [show (((2*m:ℕ):ℚ)) = (2:ℚ) * (m:ℚ) by norm_num [Nat.cast_mul]]
  rw [show (((m * (n-1):ℕ):ℚ)) = (m:ℚ) * (((n-1:ℕ):ℚ)) by norm_num [Nat.cast_mul]]
  rw [Nat.cast_sub hn]
  ring
opaque a293
    (m n:ℕ) (hn:1 ≤ n) :
    ((N1.a86 X (2*m-1)).eval ((m * (n-1):ℕ):ℚ)) *
        (N4.PmQ (2*m)).eval (((n:ℚ) + 1) / 2) =
      ((N1.a70 X).eval ((m * (n-1):ℕ):ℚ)) *
        Kq (((m * (n-1)) + 1:ℕ):ℚ) (2*m-1):= by
  let x:ℚ:= ((m * (n-1):ℕ):ℚ)
  have hmul:= congrArg (fun p:Polynomial ℚ=> p.eval x)
    (N1.a94 (2*m-1))
  simp only [Polynomial.eval_mul] at hmul
  rw [a292 m n hn]
  rw [show (((m * (n-1)) + 1:ℕ):ℚ) = x + 1 by
    simp [x,Nat.cast_add]]
  rw [a272]
  exact hmul
opaque a294 (M N:Matrix (Fin 2) (Fin 2) ℚ) :
    N0.a60 (M * N) =
      N0.a60 M * N0.a60 N:= by
  simp [N0.a60,Matrix.mul_apply,Fin.sum_univ_two]
  ring
opaque a295 (N:ℕ) :
    N0.a60 (N0.a52 N) =
      - N0.D (((N+1:ℕ):ℚ)) /
        N0.A (((N+1:ℕ):ℚ)):= by
  simp [N0.a60,N0.a52]
  ring
opaque a296 (start len:ℕ) :
    N0.a60 (N0.a56 len start) =
      (Finset.range len).prod (fun i =>
        - N0.D (((start+i+1:ℕ):ℚ)) /
          N0.A (((start+i+1:ℕ):ℚ))):= by
  induction len with
  | zero=> simp [N0.a56,N0.a60]
  | succ len ih =>
      rw [N0.a56,a294,ih,a295,
        Finset.prod_range_succ]
      ring_nf
opaque a297 (m n:ℕ) :
    N0.a60 (N0.a58 m n) =
      (Finset.range m).prod (fun i =>
        - N0.D (((m*n+i+1:ℕ):ℚ)) /
          N0.A (((m*n+i+1:ℕ):ℚ))):= by
  unfold N0.a58
  simpa using a296 (m*n) m
opaque a298 (m n:ℕ) :
    N0.a60 (N0.a58 m n) =
      (-1:ℚ)^m * (Finset.range m).prod (fun i =>
        N0.D (((m*n+i+1:ℕ):ℚ)) /
          N0.A (((m*n+i+1:ℕ):ℚ))):= by
  rw [a297]
  rw [show (fun i =>
        - N0.D (((m*n+i+1:ℕ):ℚ)) /
          N0.A (((m*n+i+1:ℕ):ℚ))
      ) = (fun i=> (-1:ℚ) *
        (N0.D (((m*n+i+1:ℕ):ℚ)) /
          N0.A (((m*n+i+1:ℕ):ℚ)))) by
    funext i
    ring]
  rw [Finset.prod_mul_distrib]
  simp
opaque a299 (x:ℚ) :
    N0.D x =
      (2 * x - 1) * (2 * x - 2) * (N1.a70 X).eval x:= by
  have h:= congrArg (fun p:Polynomial ℚ=> p.eval x)
    (N1.a71 X)
  simpa [N1.a69,N1.a67,
    N0.D] using h
opaque a300 (m:ℕ) (f:ℕ → ℚ) :
    (Finset.range (2*m)).prod f =
      (Finset.range m).prod (fun i=> f (2*i) * f (2*i+1)):= by
  induction m with
  | zero=> simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2*m + 2 by omega]
      rw [Finset.prod_range_succ]
      rw [Finset.prod_range_succ]
      rw [ih]
      rw [Finset.prod_range_succ]
      ring
opaque a301 (N:ℕ) (f:ℕ → ℚ) :
    (Finset.Ioc 0 N).prod f = (Finset.range N).prod (fun j=> f (j+1)):= by
  induction N with
  | zero=> simp
  | succ N ih =>
      rw [Finset.prod_Ioc_succ_top (Nat.zero_le N),Finset.prod_range_succ,ih]
opaque a302 (m n:ℕ) (_hn:1 ≤ n) :
    a283 m n =
      (Finset.range m).prod (fun i =>
        (2 * (((m * n:ℕ):ℚ)) + (2*(i:ℚ) + 1)) *
          (2 * (((m * n:ℕ):ℚ)) + (2*(i:ℚ) + 2))):= by
  unfold a283
  let f:ℕ → ℚ:= fun k=> ((2*m*n:ℚ) + (k:ℚ))
  have hshift:(Finset.Ioc 0 (2*m)).prod f =
      (Finset.range (2*m)).prod (fun j=> f (j+1)) :=
    a301 (2*m) f
  rw [hshift]
  rw [a300]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [f]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring
opaque a303 (m n:ℕ) (hn:1 ≤ n) :
    a281 m n = a283 m n:= by
  rw [a302 m n hn]
  unfold a281 a278
  let x:ℚ:= ((m * (n - 1):ℕ):ℚ)
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hmi:1 ≤ m:= by omega
  simp only [Nat.cast_add]
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hn,Nat.cast_sub hmi]
  ring
opaque a304 (m n:ℕ) (hn:1 ≤ n) :
    a282 m n =
      (Finset.range m).prod (fun i =>
        (2 * (((m * (n-1):ℕ):ℚ)) + 2*(i:ℚ)) *
          (2 * (((m * (n-1):ℕ):ℚ)) + 2*(i:ℚ) + 1)):= by
  unfold a282
  let f:ℕ → ℚ:= fun k=> ((2*m*n:ℚ) - (k:ℚ))
  have hreflect:(Finset.Ioc 0 (2*m)).prod f =
      (Finset.range (2*m)).prod (fun j=> f (2*m - j)):= by
    refine Finset.prod_nbij' (fun k=> 2*m - k) (fun j=> 2*m - j) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Ioc] at hk
      rw [Finset.mem_range]
      change 2*m - k < 2*m
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Ioc]
      change 0 < 2*m - j ∧ 2*m - j ≤ 2*m
      omega
    · intro k hk
      rw [Finset.mem_Ioc] at hk
      change 2*m - (2*m - k) = k
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      change 2*m - (2*m - j) = j
      omega
    · intro k hk
      rw [Finset.mem_Ioc] at hk
      change f k = f (2*m - (2*m - k))
      congr
      omega
  rw [hreflect]
  rw [a300]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [f]
  rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [Nat.cast_sub hn]
  ring
opaque a305 (x:ℚ) (hx:0 ≤ x) :
    (N1.a70 X).eval x ≠ 0:= by
  intro h
  have hpos:(0:ℚ) < 5*x^2 + 5*x + 1:= by
    nlinarith [sq_nonneg x,hx]
  have hq:(N1.a70 X).eval x = 5*x^2 + 5*x + 1:= by
    simp [N1.a70,N1.a69,N1.a68]
  rw [hq] at h
  nlinarith
opaque a306 (x i:ℕ):a278 (x:ℚ) i ≠ 0:= by
  unfold a278
  apply mul_ne_zero
  · nlinarith [show (0:ℚ) ≤ (x:ℚ) by norm_num,show (0:ℚ) ≤ (i:ℚ) by norm_num]
  · nlinarith [show (0:ℚ) ≤ (x:ℚ) by norm_num,show (0:ℚ) ≤ (i:ℚ) by norm_num]
opaque a307 (x L:ℕ):a279 (x:ℚ) L ≠ 0:= by
  unfold a279
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact a306 x i
opaque a308 (x:ℚ) (m:ℕ) (hm:1 ≤ m) :
    a279 x (2*m-1) = a279 x m * a279 (x + (m:ℚ)) (m-1):= by
  unfold a279 a278
  have hlen:m + (m-1) = 2*m-1:= by omega
  rw [← hlen]
  rw [Finset.prod_range_add]
  apply congrArg₂ HMul.hMul rfl
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Nat.cast_add]
  ring
opaque a309 (x m:ℕ) :
    (N1.a70 X).eval (x:ℚ) *
        (Finset.range m).prod (fun i =>
          (N1.a70 X).eval ((x + i + 1:ℕ):ℚ) /
            (N1.a70 X).eval ((x + i:ℕ):ℚ)) =
      (N1.a70 X).eval ((x + m:ℕ):ℚ):= by
  induction m with
  | zero=> simp
  | succ m ih =>
      rw [Finset.prod_range_succ]
      have hnonneg:(0:ℚ) ≤ ((x + m:ℕ):ℚ):= by exact_mod_cast Nat.zero_le (x + m)
      have hq:(N1.a70 X).eval ((x + m:ℕ):ℚ) ≠ 0 :=
        a305 _ hnonneg
      calc
        (N1.a70 X).eval (x:ℚ) *
            ((Finset.range m).prod (fun i =>
              (N1.a70 X).eval ((x + i + 1:ℕ):ℚ) /
                (N1.a70 X).eval ((x + i:ℕ):ℚ)) *
              ((N1.a70 X).eval ((x + m + 1:ℕ):ℚ) /
                (N1.a70 X).eval ((x + m:ℕ):ℚ)))
            = ((N1.a70 X).eval (x:ℚ) *
                (Finset.range m).prod (fun i =>
                  (N1.a70 X).eval ((x + i + 1:ℕ):ℚ) /
                    (N1.a70 X).eval ((x + i:ℕ):ℚ))) *
                ((N1.a70 X).eval ((x + m + 1:ℕ):ℚ) /
                  (N1.a70 X).eval ((x + m:ℕ):ℚ)):= by ring
        _ = (N1.a70 X).eval ((x + m:ℕ):ℚ) *
                ((N1.a70 X).eval ((x + m + 1:ℕ):ℚ) /
                  (N1.a70 X).eval ((x + m:ℕ):ℚ)):= by rw [ih]
        _ = (N1.a70 X).eval ((x + (m+1):ℕ):ℚ):= by
              field_simp [hq]
              congr 1
opaque a310 (m n:ℕ) (hn:1 ≤ n) :
    N0.a60 (N0.a58 m (n-1)) =
      (-1:ℚ)^m *
        (a282 m n *
          (Finset.range m).prod (fun i =>
            (N1.a70 X).eval (((m*(n-1) + i + 1:ℕ):ℚ)) /
              (N1.a70 X).eval (((m*(n-1) + i:ℕ):ℚ))) /
          a279 (((m*(n-1):ℕ):ℚ)) m):= by
  rw [a298]
  congr 1
  let xN:ℕ:= m*(n-1)
  let q:ℕ → ℚ:= fun r=> (N1.a70 X).eval ((r:ℕ):ℚ)
  have hterm:(Finset.range m).prod (fun i =>
        N0.D (((m * (n - 1) + i + 1:ℕ):ℚ)) /
          N0.A (((m * (n - 1) + i + 1:ℕ):ℚ))) =
      (Finset.range m).prod (fun i =>
        ((2 * (((xN:ℕ):ℚ)) + 2*(i:ℚ)) *
          (2 * (((xN:ℕ):ℚ)) + 2*(i:ℚ) + 1)) *
          (q (xN+i+1) / q (xN+i)) / a278 (xN:ℚ) i):= by
    apply Finset.prod_congr rfl
    intro i hi
    rw [show (((m * (n - 1) + i + 1:ℕ):ℚ)) = (((xN + i:ℕ):ℚ) + 1) by
      simp [xN,Nat.cast_add]]
    rw [a299]
    rw [a277]
    have hq:q (xN + i) ≠ 0:= by
      dsimp [q]
      apply a305
      exact_mod_cast Nat.zero_le (xN + i)
    have hlin:a278 (xN:ℚ) i ≠ 0:= a306 xN i
    have hqeval:(N1.a70 X).eval (((xN + i:ℕ):ℚ)) ≠ 0:= by
      simpa [q] using hq
    field_simp [hlin,hqeval]
    simp [q,a278,xN,Nat.cast_add,Nat.cast_mul]
    ring
  rw [hterm]
  rw [show (Finset.range m).prod (fun i =>
        ((2 * (((xN:ℕ):ℚ)) + 2*(i:ℚ)) *
          (2 * (((xN:ℕ):ℚ)) + 2*(i:ℚ) + 1)) *
          (q (xN+i+1) / q (xN+i)) / a278 (xN:ℚ) i)
      = ((Finset.range m).prod (fun i =>
          (2 * (((xN:ℕ):ℚ)) + 2*(i:ℚ)) *
            (2 * (((xN:ℕ):ℚ)) + 2*(i:ℚ) + 1))) *
          ((Finset.range m).prod (fun i=> q (xN+i+1) / q (xN+i))) /
          a279 (xN:ℚ) m by
    unfold a279 a278
    rw [← Finset.prod_mul_distrib]
    simp only [div_eq_mul_inv]
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_inv_distrib]]
  rw [← a304 m n hn]
opaque a311
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    a284 m n * N0.a60 (N0.a58 m (n-1)) =
      (-1:ℚ)^m * a282 m n *
        ((N1.a70 X).eval ((m*n:ℕ):ℚ) * a280 m (n+1) (m-1)):= by
  let xN:ℕ:= m*(n-1)
  let R:ℚ:= (Finset.range m).prod (fun i =>
    (N1.a70 X).eval (((m*(n-1) + i + 1:ℕ):ℚ)) /
      (N1.a70 X).eval (((m*(n-1) + i:ℕ):ℚ)))
  have hdet:= a310 m n hn
  have hplus:= a285 m n
  have htail:a280 m n (2*m-1) =
      a279 (xN:ℚ) m * a279 (((m*n:ℕ):ℚ)) (m-1):= by
    have h:= a308 (xN:ℚ) m hm
    simp [a280,xN] at h ⊢
    convert h using 2
    · simp [Nat.cast_sub hn]
      ring_nf
  have htel:(N1.a70 X).eval (xN:ℚ) * R =
      (N1.a70 X).eval ((m*n:ℕ):ℚ):= by
    have h:= a309 xN m
    simp [R,xN] at h ⊢
    convert h using 2
    · simp [Nat.cast_sub hn]
      ring_nf
  have hlin_ne:a279 (xN:ℚ) m ≠ 0:= a307 xN m
  rw [hdet]
  unfold a284
  calc
    (a281 m n * (N1.a70 X).eval ↑(m * (n - 1)) * a280 m n (m - 1)) *
        ((-1:ℚ)^m * (a282 m n * R / a279 ↑(m * (n - 1)) m))
        = (-1:ℚ)^m * a282 m n *
            (((a281 m n * a280 m n (m-1)) *
                (N1.a70 X).eval (xN:ℚ) * R) /
              a279 (xN:ℚ) m):= by simp [R,xN]; ring
    _ = (-1:ℚ)^m * a282 m n *
            ((a280 m n (2*m-1) * (N1.a70 X).eval (xN:ℚ) * R) /
              a279 (xN:ℚ) m):= by rw [hplus]
    _ = (-1:ℚ)^m * a282 m n *
            (((a279 (xN:ℚ) m * a279 (((m*n:ℕ):ℚ)) (m-1)) *
                (N1.a70 X).eval (xN:ℚ) * R) /
              a279 (xN:ℚ) m):= by rw [htail]
    _ = (-1:ℚ)^m * a282 m n *
            (a279 (((m*n:ℕ):ℚ)) (m-1) *
              ((N1.a70 X).eval (xN:ℚ) * R)):= by
              field_simp [hlin_ne]
    _ = (-1:ℚ)^m * a282 m n *
            ((N1.a70 X).eval ((m*n:ℕ):ℚ) * a280 m (n+1) (m-1)):= by
              rw [htel]
              unfold a280
              rw [show (n + 1 - 1) = n by omega]
              ring
opaque a312 (m n:ℕ) (hm:1 ≤ m) :
    (N4.PmQ m).eval ((n:ℚ) + 1) =
      (N4.PmQ m).eval (-(n:ℚ)):= by
  have h:= N4.a220 m hm ((n:ℚ) + 1)
  simpa [show (1 - ((n:ℚ) + 1)) = -(n:ℚ) by ring] using h
opaque a313
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    a284 m n * N0.a58 m n 0 1 *
        N0.a60 (N0.a58 m (n-1)) =
      (-1:ℚ)^m * a282 m n * (N4.PmQ m).eval (-(n:ℚ)):= by
  have hcd:= a311 m n hm hn
  have hbase:(N1.a70 X).eval ((m*n:ℕ):ℚ) *
        a280 m (n+1) (m-1) * N0.a58 m n 0 1 =
      (N4.PmQ m).eval ((n:ℚ) + 1):= by
    have h:= a290 m (n+1) hm (by omega)
    simpa [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] using h
  have hsym:= a312 m n hm
  calc
    a284 m n * N0.a58 m n 0 1 *
        N0.a60 (N0.a58 m (n-1))
        = (a284 m n * N0.a60 (N0.a58 m (n-1))) *
            N0.a58 m n 0 1:= by ring
    _ = ((-1:ℚ)^m * a282 m n *
          ((N1.a70 X).eval ((m*n:ℕ):ℚ) * a280 m (n+1) (m-1))) *
            N0.a58 m n 0 1:= by rw [hcd]
    _ = (-1:ℚ)^m * a282 m n *
          ((N1.a70 X).eval ((m*n:ℕ):ℚ) *
            a280 m (n+1) (m-1) * N0.a58 m n 0 1):= by ring
    _ = (-1:ℚ)^m * a282 m n * (N4.PmQ m).eval ((n:ℚ) + 1):= by rw [hbase]
    _ = (-1:ℚ)^m * a282 m n * (N4.PmQ m).eval (-(n:ℚ)):= by rw [hsym]
opaque a314 (m n:ℕ) :
    N0.a58 m (n+1) 0 0 *
        N0.a58 m n 0 1 +
      N0.a58 m (n+1) 0 1 *
        N0.a58 m n 1 1 =
      (N0.a58 m (n+1) *
        N0.a58 m n) 0 1:= by
  simp [Matrix.mul_apply,Fin.sum_univ_two]
opaque a315 (start a b:ℕ) :
    N0.a56 (a+b) start =
      N0.a56 b (start+a) *
        N0.a56 a start:= by
  induction b with
  | zero=> simp [N0.a56]
  | succ b ih =>
      rw [show a + (b+1) = (a+b)+1 by omega]
      rw [N0.a56,ih]
      rw [N0.a56]
      simp only [Matrix.mul_assoc]
      rw [show start + (a + b) = start + a + b by omega]
opaque a316 (m n:ℕ) :
    N0.a58 m (n+1) * N0.a58 m n =
      N0.a56 (2*m) (m*n):= by
  unfold N0.a58
  rw [Nat.mul_succ]
  rw [← a315 (m*n) m m]
  congr 1
  omega
opaque a317 (m n:ℕ) (hm:1 ≤ m) :
    N0.a58 m (n+1) 0 0 *
        N0.a58 m n 0 1 +
      N0.a58 m (n+1) 0 1 *
        N0.a58 m n 1 1 =
      Kq (((m*n) + 1:ℕ):ℚ) (2*m-1) / a262 (m*n+1) (2*m-1):= by
  rw [a314,a316]
  simpa using a271 (m*n) (2*m) (by omega)
opaque a318
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    ((N1.a70 X).eval ((m * (n-1):ℕ):ℚ)) *
        a280 m n (2*m-1) *
          (N0.a58 m n 0 0 *
              N0.a58 m (n-1) 0 1 +
            N0.a58 m n 0 1 *
              N0.a58 m (n-1) 1 1) =
      (N4.PmQ (2*m)).eval (((n:ℚ) + 1) / 2):= by
  let x:ℚ:= ((m * (n-1):ℕ):ℚ)
  let Q:ℚ:= (N1.a86 X (2*m-1)).eval x
  let L:ℚ:= a280 m n (2*m-1)
  let q:ℚ:= (N1.a70 X).eval x
  let T:ℚ :=
    N0.a58 m n 0 0 *
        N0.a58 m (n-1) 0 1 +
      N0.a58 m n 0 1 *
        N0.a58 m (n-1) 1 1
  let K:ℚ:= Kq (((m * (n-1)) + 1:ℕ):ℚ) (2*m-1)
  let A:ℚ:= a262 (m*(n-1)+1) (2*m-1)
  let P:ℚ:= (N4.PmQ (2*m)).eval (((n:ℚ) + 1) / 2)
  have htwo:T = K / A:= by
    have h:= a317 m (n-1) hm
    simpa [T,K,A,Nat.sub_add_cancel hn] using h
  have hclear:Q * P = q * K:= by
    simpa [x,Q,q,K,P] using
      a293 m n hn
  have hAfac:A = L * Q:= by
    simpa [x,Q,L,A,a280] using
      a288 (m*(n-1)) (2*m-1)
  have hAne:A ≠ 0:= by
    simpa [A] using a268 (m*(n-1)+1) (2*m-1) (by omega)
  change q * L * T = P
  rw [htwo]
  field_simp [hAne]
  calc
    q * L * K = L * (q * K):= by ring
    _ = L * (Q * P):= by rw [← hclear]
    _ = A * P:= by rw [hAfac]; ring
opaque a319
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    a284 m n *
        (N0.a58 m n 0 0 *
            N0.a58 m (n-1) 0 1 +
          N0.a58 m n 0 1 *
            N0.a58 m (n-1) 1 1) =
      (N4.PmQ (2*m)).eval (((n:ℚ) + 1) / 2):= by
  have htwo:= a318 m n hm hn
  have hratio:= a285 m n
  unfold a284
  calc
    (a281 m n * (N1.a70 X).eval ↑(m * (n - 1)) * a280 m n (m - 1)) *
        (N0.a58 m n 0 0 *
            N0.a58 m (n - 1) 0 1 +
          N0.a58 m n 0 1 *
            N0.a58 m (n - 1) 1 1)
        = (N1.a70 X).eval ↑(m * (n - 1)) *
            (a281 m n * a280 m n (m - 1)) *
              (N0.a58 m n 0 0 *
                  N0.a58 m (n - 1) 0 1 +
                N0.a58 m n 0 1 *
                  N0.a58 m (n - 1) 1 1):= by ring
    _ = (N1.a70 X).eval ↑(m * (n - 1)) * a280 m n (2*m-1) *
              (N0.a58 m n 0 0 *
                  N0.a58 m (n - 1) 0 1 +
                N0.a58 m n 0 1 *
                  N0.a58 m (n - 1) 1 1):= by rw [hratio]
    _ = (N4.PmQ (2*m)).eval (((n:ℚ) + 1) / 2):= htwo
opaque a320
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    a283 m n * (N4.PmQ m).eval (n:ℚ) *
        N0.aQ (m*(n+1)) +
      (((-1:ℚ)^m * a282 m n * (N4.PmQ m).eval (-(n:ℚ))) *
        N0.aQ (m*(n-1))) =
      (N4.PmQ (2*m)).eval (((n:ℚ)+1)/2) *
        N0.aQ (m*n):= by
  let C:ℚ:= a284 m n
  let qprev:ℚ:= N0.a58 m (n-1) 0 1
  let mid:ℚ :=
    N0.a58 m n 0 0 *
        N0.a58 m (n-1) 0 1 +
      N0.a58 m n 0 1 *
        N0.a58 m (n-1) 1 1
  let detterm:ℚ :=
    N0.a58 m n 0 1 *
      N0.a60 (N0.a58 m (n-1))
  let anext:ℚ:= N0.aQ (m*(n+1))
  let acur:ℚ:= N0.aQ (m*n)
  let aprev:ℚ:= N0.aQ (m*(n-1))
  let fp:ℚ:= a283 m n * (N4.PmQ m).eval (n:ℚ)
  let fm:ℚ:= (-1:ℚ)^m * a282 m n * (N4.PmQ m).eval (-(n:ℚ))
  let gm:ℚ:= (N4.PmQ (2*m)).eval (((n:ℚ)+1)/2)
  have hqprev:C * qprev = fp:= by
    have h:= a291 m n hm hn
    calc
      C * qprev = a281 m n * (N4.PmQ m).eval (n:ℚ):= by simpa [C,qprev] using h
      _ = fp:= by simp [fp,a303 m n hn]
  have hmid:C * mid = gm:= by
    have h:= a319 m n hm hn
    simpa [C,mid,gm] using h
  have hdet:C * detterm = fm:= by
    have h:= a313 m n hm hn
    calc
      C * detterm = a284 m n * N0.a58 m n 0 1 *
          N0.a60 (N0.a58 m (n-1)):= by
            simp [C,detterm]
            ring
      _ = fm:= by simpa [fm] using h
  have hbase0:= N0.a62 m (n-1)
  have hbase:qprev * anext - mid * acur + detterm * aprev = 0:= by
    have hnp1:n - 1 + 1 = n:= by omega
    have hnp2:n - 1 + 2 = n + 1:= by omega
    simpa [qprev,mid,detterm,anext,acur,aprev,hnp1,hnp2] using hbase0
  have hzero:fp * anext - gm * acur + fm * aprev = 0:= by
    calc
      fp * anext - gm * acur + fm * aprev =
          (C * qprev) * anext - (C * mid) * acur + (C * detterm) * aprev:= by
            rw [hqprev,hmid,hdet]
      _ = C * (qprev * anext - mid * acur + detterm * aprev):= by ring
      _ = 0:= by rw [hbase]; ring
  calc
    fp * anext + fm * aprev = gm * acur + (fp * anext - gm * acur + fm * aprev):= by ring
    _ = gm * acur:= by rw [hzero]; ring
def a321 (m n:ℕ):ℝ :=
  (Finset.Ioc 0 (2*m)).prod (fun k=> ((2*m*n:ℝ) + (k:ℝ)))
def a322 (m n:ℕ):ℝ :=
  (Finset.Ioc 0 (2*m)).prod (fun k=> ((2*m*n:ℝ) - (k:ℝ)))
opaque a323 (m n:ℕ) :
    ((a283 m n:ℚ):ℝ) = a321 m n:= by
  unfold a283 a321
  norm_num [Nat.cast_mul]
opaque a324 (m n:ℕ) :
    ((a282 m n:ℚ):ℝ) = a322 m n:= by
  unfold a282 a322
  norm_num [Nat.cast_mul]
opaque a325
    (m n:ℕ) (hm:1 ≤ m) :
    (N7.QmR m).eval ((n:ℝ)^2) =
      (↑((N4.PmQ (2*m)).eval (((n:ℚ)+1)/2)):ℝ):= by
  have hpoly:= congrArg (fun p:Polynomial ℝ=> p.eval (n:ℝ))
    (N7.a257 m hm)
  have hQR:(N7.QmR m).eval ((n:ℝ)^2) = (N7.RmR m).eval (n:ℝ):= by
    simpa [Polynomial.eval_comp] using hpoly
  have hshift:(N7.RmR m).eval (n:ℝ) =
      (N6.PmR (2*m)).eval (((n:ℝ)+1)/2):= by
    unfold N7.RmR N7.a241
    simp [Polynomial.eval_comp]
    ring_nf
  have hrat:= N6.a233 (2*m) (((n:ℚ)+1)/2)
  have harg:(((((n:ℚ)+1)/2:ℚ):ℝ)) = ((n:ℝ)+1)/2:= by norm_num
  calc
    (N7.QmR m).eval ((n:ℝ)^2) = (N7.RmR m).eval (n:ℝ):= hQR
    _ = (N6.PmR (2*m)).eval (((n:ℝ)+1)/2):= hshift
    _ = (↑((N4.PmQ (2*m)).eval (((n:ℚ)+1)/2)):ℝ):= by
      rw [← harg]
      exact hrat
opaque a326
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    a321 m n * (N6.PmR m).eval (n:ℝ) *
        (N0.aQ (m*(n+1)):ℝ) +
      (((-1:ℝ)^m * a322 m n * (N6.PmR m).eval (-(n:ℝ))) *
        (N0.aQ (m*(n-1)):ℝ)) =
      (N7.QmR m).eval ((n:ℝ)^2) *
        (N0.aQ (m*n):ℝ):= by
  have hq:= a320 m n hm hn
  have hp_pos:(N6.PmR m).eval (n:ℝ) =
      (↑((N4.PmQ m).eval (n:ℚ)):ℝ):= by
    simpa using N6.a233 m (n:ℚ)
  have hp_neg0:= N6.a233 m (-(n:ℚ))
  have hmid:= a325 m n hm
  have hnegarg:(((-(n:ℚ):ℚ):ℝ)) = -(n:ℝ):= by norm_num
  have hp_neg:(N6.PmR m).eval (-(n:ℝ)) =
      (↑((N4.PmQ m).eval (-(n:ℚ))):ℝ):= by
    rw [← hnegarg]
    exact hp_neg0
  calc
    a321 m n * (N6.PmR m).eval (n:ℝ) *
        (N0.aQ (m*(n+1)):ℝ) +
      (((-1:ℝ)^m * a322 m n * (N6.PmR m).eval (-(n:ℝ))) *
        (N0.aQ (m*(n-1)):ℝ))
        = ((a283 m n * (N4.PmQ m).eval (n:ℚ) *
              N0.aQ (m*(n+1)) +
            (((-1:ℚ)^m * a282 m n * (N4.PmQ m).eval (-(n:ℚ))) *
              N0.aQ (m*(n-1)))):ℚ):= by
          rw [← a323,← a324]
          rw [hp_pos,hp_neg]
          norm_num
    _ = ((N4.PmQ (2*m)).eval (((n:ℚ)+1)/2) *
          N0.aQ (m*n):ℚ):= by rw [hq]
    _ = (N7.QmR m).eval ((n:ℝ)^2) *
        (N0.aQ (m*n):ℝ):= by
          rw [hmid]
          norm_num
opaque a327
    (m n:ℕ) (hm:1 ≤ m) (hn:1 ≤ n) :
    a321 m n * (N6.PmR m).eval (n:ℝ) *
        (N0.a63 (m*(n+1)):ℝ) +
      (((-1:ℝ)^m * a322 m n * (N6.PmR m).eval (-(n:ℝ))) *
        (N0.a63 (m*(n-1)):ℝ)) =
      (N7.QmR m).eval ((n:ℝ)^2) *
        (N0.a63 (m*n):ℝ):= by
  have h:= a326 m n hm hn
  have hcast:∀ N:ℕ,(N0.aQ N:ℝ) =
      (N0.a63 N:ℝ):= by
    intro N
    have hq:= N0.a64 N
    exact (congrArg (fun x:ℚ=> (x:ℝ)) hq).symm
  simpa [hcast] using h
end
end N8
namespace N9
opaque a328 (N:ℕ) :
    A103885 N = N0.a63 N:= by
  unfold A103885 N0.a63 N0.F
  by_cases h:N = 0
  · simp [h]
  · simp [h]
opaque a329 (m n:ℕ) :
    A103885_subsequence_real m n =
      (N0.a63 (m*n):ℝ):= by
  unfold A103885_subsequence_real
  rw [a328]
opaque a330 (m n:ℕ) :
    prod_factor_plus m n = N8.a321 m n:= by
  unfold prod_factor_plus N8.a321 a0
  rfl
opaque a331 (m n:ℕ) :
    prod_factor_minus m n = N8.a322 m n:= by
  unfold prod_factor_minus N8.a322 a0
  rfl
end N9
theorem oeis_a103885_conjecture_0 (m:ℕ) (hm:1 ≤ m) :
    ∃ (P Q:Polynomial ℝ),
      P.degree = (2 * m:ℕ) ∧ Q.degree = (2 * m:ℕ) ∧
      (∀ (n:ℕ) (hn:1 ≤ n),
        (prod_factor_plus m n * P.eval (n:ℝ)) * (A103885_subsequence_real m (n + 1)) +
        ((-1:ℝ) ^ m * prod_factor_minus m n * P.eval (-(n:ℝ))) * (A103885_subsequence_real m (n - 1)) =
        (Q.eval ((n:ℝ)^2)) * (A103885_subsequence_real m n)) ∧
      (∀ x:ℝ,P.eval x = P.eval (1 - x)) ∧
      (∀ z:ℂ,(P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧
      (∀ z:ℂ,(Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)):= by
  refine ⟨N6.PmR m,N7.QmR m,?_,?_,?_,?_,?_,?_⟩
  · exact N6.a236 m hm
  · exact N7.a249 m hm
  · intro n hn
    have h:= N8.a327 m n hm hn
    simpa [N9.a330,N9.a331,
      N9.a329,mul_assoc] using h
  · intro x
    exact N6.a238 m hm x
  · exact N6.a239 m hm
  · exact N7.a261 m hm
