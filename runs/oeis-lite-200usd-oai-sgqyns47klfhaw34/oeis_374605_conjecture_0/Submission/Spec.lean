import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option linter.all false


/-- A374605. -/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

noncomputable section

def P0q (n : ℚ) : ℚ := 27*(n+2)*(3*n+1)^3*(3*n+2)^3*(5616*n^4+36504*n^3+88731*n^2+95597*n+38524)
def P1q (n : ℚ) : ℚ := 36*(72783360*n^11+946183680*n^10+5506947648*n^9+18919626192*n^8+42578365230*n^7+65816429067*n^6+71201437287*n^5+53826632241*n^4+27825371259*n^3+9355168720*n^2+1839302884*n+160171824)
def P2q (n : ℚ) : ℚ := -16*(4*n+5)^2*(4*n+7)^2*(n+2)^3*(5616*n^4+14040*n^3+12915*n^2+5183*n+770)
def RnNum (n k : ℚ) : ℚ := (2*k + 3*n + 1)*(2*k + 3*n + 2)*(2*k + 3*n + 3)
def RnDen (n k : ℚ) : ℚ := 2*(k - n - 1)^2*(2*k + 2*n + 1)
def RkNum (n k : ℚ) : ℚ := (k - n)^2*(2*k + 3*n + 1)*(2*k + 3*n + 2)
def RkDen (n k : ℚ) : ℚ := 2*(k + 1)^3*(2*k + 2*n + 1)
def Rnq (n k : ℚ) : ℚ := RnNum n k / RnDen n k
def Rkq (n k : ℚ) : ℚ := RkNum n k / RkDen n k
def Uden (n k : ℚ) : ℚ := (k - n - 2)^2*(k - n - 1)^2*(2*k + 2*n + 1)
def Unum (n k : ℚ) : ℚ := -2*k^3*(2211741056*k^4 - 1098506112*k^3 - 10766446432*k^2 - 10679394720*k + n*(22132861920*k^4 - 4832251872*k^3 - 126705453624*k^2 - 150165393960*k + n*(95408509616*k^4 + 13984568864*k^3 - 653530537932*k^2 - 942595668008*k + n*(232260828536*k^4 + 148232918168*k^3 - 1943489115054*k^2 - 3487884888902*k + n*(351973236732*k^4 + 465110443200*k^3 - 3688720523319*k^2 - 8465283019080*k + n*(344718632908*k^4 + 796680592288*k^3 - 4669388154027*k^2 - 14188282181854*k + n*(218553344900*k^4 + 838192222288*k^3 - 3994731964001*k^2 - 16833767864530*k + n*(86660583948*k^4 + 556734032040*k^3 - 2283369599763*k^2 - 14244416924532*k + n*(19539512928*k^4 + 228019559760*k^3 - 836257162176*k^2 - 8532685826406*k + n*(1912337856*k^4 + 52641418752*k^3 - 177956884440*k^2 - 3529435402440*k + n*(5244984576*k^3 - 16982581824*k^2 - 957121566192*k + n*(-83700864*k^2 - 152808664320*k + n*(-10861703424*k - 7443918144*n - 104004085536) - 656072573076) - 2471944068324) - 6201652774203) - 10932367537305) - 13923410422479) - 12966669636411) - 8828573914414) - 4340867574156) - 1498708776704) - 344307196784) - 47221583328) - 2923632832)
def Uq (n k : ℚ) : ℚ := Unum n k / Uden n k

opaque U_cert_identity (n k : ℚ)
  (h0 : k - n ≠ 0) (h2 : k - n - 2 ≠ 0) (h3 : k - n - 1 ≠ 0)
  (h4 : 2*k + 2*n + 1 ≠ 0) (h5 : 2*k + 2*n + 3 ≠ 0) (h6 : k + 1 ≠ 0) :
  Uq n (k+1) * Rkq n k - Uq n k = P0q n + P1q n * Rnq n k + P2q n * Rnq n k * Rnq (n+1) k := by
  have hU0 : Uden n k ≠ 0 := by
    unfold Uden
    repeat' apply mul_ne_zero
    · exact pow_ne_zero 2 h2
    · exact pow_ne_zero 2 h3
    · exact h4
  have hU1 : Uden n (k+1) ≠ 0 := by
    unfold Uden
    repeat' apply mul_ne_zero
    · have : k + 1 - n - 2 = k - n - 1 := by ring
      rw [this]; exact pow_ne_zero 2 h3
    · have : k + 1 - n - 1 = k - n := by ring
      rw [this]; exact pow_ne_zero 2 h0
    · have : 2 * (k+1) + 2*n + 1 = 2*k + 2*n + 3 := by ring
      rw [this]; exact h5
  have hRk : RkDen n k ≠ 0 := by
    unfold RkDen
    repeat' apply mul_ne_zero
    · norm_num
    · exact pow_ne_zero 3 h6
    · exact h4
  have hRn0 : RnDen n k ≠ 0 := by
    unfold RnDen
    repeat' apply mul_ne_zero
    · norm_num
    · exact pow_ne_zero 2 h3
    · exact h4
  have hRn1 : RnDen (n+1) k ≠ 0 := by
    unfold RnDen
    repeat' apply mul_ne_zero
    · norm_num
    · have : k - (n+1) - 1 = k - n - 2 := by ring
      rw [this]; exact pow_ne_zero 2 h2
    · have : 2*k + 2*(n+1) + 1 = 2*k + 2*n + 3 := by ring
      rw [this]; exact h5
  unfold Uq Rkq Rnq
  field_simp [hU0,hU1,hRk,hRn0,hRn1]
  unfold Unum Uden RkNum RkDen RnNum RnDen P0q P1q P2q
  ring


def Fq (n k : ℕ) : ℚ :=
  ((Nat.factorial (n+k) : ℕ) : ℚ) * ((Nat.factorial (3*n+2*k) : ℕ) : ℚ) /
    ((((Nat.factorial k : ℕ) : ℚ)^3) * (((Nat.factorial (n-k) : ℕ) : ℚ)^2) * ((Nat.factorial (2*n+2*k) : ℕ) : ℚ))


opaque fac_cast_ne (n : ℕ) : ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := by positivity

opaque Fq_k_ratio {n k : ℕ} (hk : k < n) : Fq n (k+1) = Fq n k * Rkq n k := by
  unfold Fq Rkq RkNum RkDen
  have hkfac : ((Nat.factorial k : ℕ) : ℚ) ≠ 0 := fac_cast_ne k
  have hk1fac : ((Nat.factorial (k+1) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (k+1)
  have hnkfac : ((Nat.factorial (n-k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n-k)
  have hnk1fac : ((Nat.factorial (n-(k+1)) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n-(k+1))
  have h2fac : ((Nat.factorial (2*n+2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n+2*k)
  have h2fac' : ((Nat.factorial (2*n+2*(k+1)) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n+2*(k+1))
  have hnkpos : ((n-k:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n-k))
  have hk1pos : ((k+1:ℕ):ℚ) ≠ 0 := by positivity
  have hnkQ : ((n:ℚ) - (k:ℚ)) ≠ 0 := by
    have : (k:ℚ) < n := by exact_mod_cast hk
    linarith
  have hnkQ' : ((k:ℚ) - (n:ℚ)) ≠ 0 := by
    intro h0
    apply hnkQ
    linarith
  have hlin : (2*(k:ℚ)+2*(n:ℚ)+1) ≠ 0 := by positivity
  rw [show n+(k+1)=n+k+1 by omega, Nat.factorial_succ]
  rw [show 3*n+2*(k+1)=3*n+2*k+2 by omega]
  rw [show 3*n+2*k+2=(3*n+2*k+1)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ (3*n+2*k)]
  rw [Nat.factorial_succ k]
  have hfacsub : ((Nat.factorial (n-k) : ℕ) : ℚ) = ((n-k:ℕ):ℚ) * ((Nat.factorial (n-(k+1)) : ℕ) : ℚ) := by
    have hsub : n-k = n-(k+1)+1 := by omega
    rw [hsub, Nat.factorial_succ]
    norm_num [Nat.cast_mul]
  rw [hfacsub]
  rw [show 2*n+2*(k+1)=2*n+2*k+2 by omega]
  rw [show 2*n+2*k+2=(2*n+2*k+1)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ (2*n+2*k)]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hk.le]
  field_simp [hkfac,hk1fac,hnkfac,hnk1fac,h2fac,h2fac',hnkpos,hk1pos,hnkQ,hnkQ',hlin]
  ring_nf

opaque Fq_n_ratio {n k : ℕ} (hk : k ≤ n) : Fq (n+1) k = Fq n k * Rnq n k := by
  unfold Fq Rnq RnNum RnDen
  have h1 : ((Nat.factorial (n+k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n+k)
  have h2 : ((Nat.factorial (3*n+2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (3*n+2*k)
  have h3 : ((Nat.factorial (n-k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n-k)
  have h4 : ((Nat.factorial (2*n+2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n+2*k)
  have hd : (((n+1-k:ℕ):ℚ)) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n+1-k))
  rw [show (n+1)+k = n+k+1 by omega, Nat.factorial_succ]
  rw [show 3*(n+1)+2*k = 3*n+2*k+3 by omega]
  rw [show 3*n+2*k+3=(3*n+2*k+2)+1 by omega, Nat.factorial_succ]
  rw [show 3*n+2*k+2=(3*n+2*k+1)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ (3*n+2*k)]
  have hsub : n+1-k = n-k+1 := by omega
  rw [hsub, Nat.factorial_succ]
  rw [show 2*(n+1)+2*k = 2*n+2*k+2 by omega]
  rw [show 2*n+2*k+2=(2*n+2*k+1)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ (2*n+2*k)]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hk]
  field_simp [h1,h2,h3,h4,hd]
  ring_nf



def br10 (n : ℚ) : ℚ := (5*n+1)*(5*n+2)*(5*n+3)/(2*(4*n+1))
def br20 (n : ℚ) : ℚ := 5*(n+1)*(5*n+1)*(5*n+2)*(5*n+3)*(5*n+4)*(5*n+6)/(16*(4*n+1)*(4*n+3))
def br11 (n : ℚ) : ℚ := 5*(5*n+1)*(5*n+2)*(5*n+3)*(5*n+4)/(4*(n+1)^2*(4*n+1)*(4*n+3))
def br21 (n : ℚ) : ℚ := 5*(5*n+1)*(5*n+2)*(5*n+3)*(5*n+4)*(5*n+6)*(5*n+7)*(5*n+8)/(8*(n+1)^2*(4*n+1)*(4*n+3)*(4*n+5))
def br22 (n : ℚ) : ℚ := 25*(5*n+1)*(5*n+2)*(5*n+3)*(5*n+4)*(5*n+6)*(5*n+7)*(5*n+8)*(5*n+9)/(16*(n+1)^2*(n+2)^2*(4*n+1)*(4*n+3)*(4*n+5)*(4*n+7))

opaque br10_id (n : ℕ) : Rnq n n = br10 n := by
  unfold Rnq RnNum RnDen br10
  have h1 : (4*(n:ℚ)+1) ≠ 0 := by positivity
  field_simp [h1]
  ring

opaque br20_id (n : ℕ) : br10 n * Rnq (n+1) n = br20 n := by
  unfold br10 br20 Rnq RnNum RnDen
  have h1 : (4*(n:ℚ)+1) ≠ 0 := by positivity
  have h3 : (4*(n:ℚ)+3) ≠ 0 := by positivity
  have hd : ((n:ℚ) - ↑(n+1) - 1) ≠ 0 := by norm_num [Nat.cast_add]
  field_simp [h1,h3,hd]
  ring

opaque br11_id (n : ℕ) : br10 n * Rkq (n+1) n = br11 n := by
  unfold br10 br11 Rkq RkNum RkDen
  have h1 : (4*(n:ℚ)+1) ≠ 0 := by positivity
  have h3 : (4*(n:ℚ)+3) ≠ 0 := by positivity
  have hn1 : ((n:ℚ)+1) ≠ 0 := by positivity
  have hk : ((n:ℚ) - ↑(n+1)) ≠ 0 := by norm_num [Nat.cast_add]
  field_simp [h1,h3,hn1,hk]
  ring

opaque br21_id (n : ℕ) : br11 n * Rnq (n+1) (n+1) = br21 n := by
  unfold br11 br21 Rnq RnNum RnDen
  have h1 : (4*(n:ℚ)+1) ≠ 0 := by positivity
  have h3 : (4*(n:ℚ)+3) ≠ 0 := by positivity
  have h5 : (4*(n:ℚ)+5) ≠ 0 := by positivity
  have hn1 : ((n:ℚ)+1) ≠ 0 := by positivity
  have hd : (↑(n+1) - ↑(n+1) - 1 : ℚ) ≠ 0 := by norm_num
  field_simp [h1,h3,h5,hn1,hd]
  ring

opaque br22_id (n : ℕ) : br21 n * Rkq (n+2) (n+1) = br22 n := by
  unfold br21 br22 Rkq RkNum RkDen
  have h1 : (4*(n:ℚ)+1) ≠ 0 := by positivity
  have h3 : (4*(n:ℚ)+3) ≠ 0 := by positivity
  have h5 : (4*(n:ℚ)+5) ≠ 0 := by positivity
  have h7 : (4*(n:ℚ)+7) ≠ 0 := by positivity
  have hn1 : ((n:ℚ)+1) ≠ 0 := by positivity
  have hn2 : ((n:ℚ)+2) ≠ 0 := by positivity
  have hk : (↑(n+1) - ↑(n+2) : ℚ) ≠ 0 := by norm_num [Nat.cast_add]
  field_simp [h1,h3,h5,h7,hn1,hn2,hk]
  ring


opaque Fq_boundary_10 (n : ℕ) : Fq (n+1) n = Fq n n * br10 n := by
  rw [Fq_n_ratio (n := n) (k := n) le_rfl, br10_id]

opaque Fq_boundary_20 (n : ℕ) : Fq (n+2) n = Fq n n * br20 n := by
  rw [Fq_n_ratio (n := n+1) (k := n) (by omega), Fq_boundary_10]
  norm_num [Nat.cast_add]
  rw [mul_assoc, br20_id]

opaque Fq_boundary_11 (n : ℕ) : Fq (n+1) (n+1) = Fq n n * br11 n := by
  rw [Fq_k_ratio (n := n+1) (k := n) (by omega), Fq_boundary_10]
  norm_num [Nat.cast_add]
  rw [mul_assoc, br11_id]

opaque Fq_boundary_21 (n : ℕ) : Fq (n+2) (n+1) = Fq n n * br21 n := by
  rw [Fq_n_ratio (n := n+1) (k := n+1) le_rfl, Fq_boundary_11]
  norm_num [Nat.cast_add]
  rw [mul_assoc, br21_id]

opaque Fq_boundary_22 (n : ℕ) : Fq (n+2) (n+2) = Fq n n * br22 n := by
  rw [Fq_k_ratio (n := n+2) (k := n+1) (by omega), Fq_boundary_21]
  norm_num [Nat.cast_add]
  rw [mul_assoc, br22_id]


noncomputable def Cq (n k : ℕ) : ℚ :=
  P0q n * Fq n k + P1q n * Fq (n+1) k + P2q n * Fq (n+2) k

opaque Uq_zero_right (n : ℕ) : Uq n 0 = 0 := by
  unfold Uq Unum
  norm_num

opaque interior_Cq_eq_tel {n k : ℕ} (hk : k < n) :
    Cq n k = Uq n (k+1) * Fq n (k+1) - Uq n k * Fq n k := by
  unfold Cq
  have hRn0 := Fq_n_ratio (n := n) (k := k) (by omega : k ≤ n)
  have hRn1 := Fq_n_ratio (n := n+1) (k := k) (by omega : k ≤ n+1)
  have hRk := Fq_k_ratio (n := n) (k := k) hk
  rw [hRn1]
  rw [hRn0]
  have hk_ne_n : (k:ℚ) - (n:ℚ) ≠ 0 := by
    have : (k:ℚ) < n := by exact_mod_cast hk
    linarith
  have hk_ne_n2 : (k:ℚ) - (n:ℚ) - 2 ≠ 0 := by
    have : (k:ℚ) < n := by exact_mod_cast hk
    linarith
  have hk_ne_n1 : (k:ℚ) - (n:ℚ) - 1 ≠ 0 := by
    have : (k:ℚ) < n := by exact_mod_cast hk
    linarith
  have hlin : 2*(k:ℚ)+2*(n:ℚ)+1 ≠ 0 := by positivity
  have hlin3 : 2*(k:ℚ)+2*(n:ℚ)+3 ≠ 0 := by positivity
  have hk1 : (k:ℚ)+1 ≠ 0 := by positivity
  have hcert := U_cert_identity (n:ℚ) (k:ℚ) hk_ne_n hk_ne_n2 hk_ne_n1 hlin hlin3 hk1
  norm_num [Nat.cast_add] at hcert ⊢
  calc
    P0q ↑n * Fq n k + P1q ↑n * (Fq n k * Rnq ↑n ↑k) + P2q ↑n * ((Fq n k * Rnq ↑n ↑k) * Rnq (↑n + 1) ↑k)
        = Fq n k * (P0q ↑n + P1q ↑n * Rnq ↑n ↑k + P2q ↑n * Rnq ↑n ↑k * Rnq (↑n+1) ↑k) := by ring
    _ = Fq n k * (Uq ↑n (↑k+1) * Rkq ↑n ↑k - Uq ↑n ↑k) := by rw [← hcert]
    _ = Uq ↑n (↑k+1) * (Fq n k * Rkq ↑n ↑k) - Uq ↑n ↑k * Fq n k := by ring
    _ = Uq ↑n (↑k+1) * Fq n (k+1) - Uq ↑n ↑k * Fq n k := by
      simpa [hRk]


def Fz (n k : ℕ) : ℚ := if k ≤ n then Fq n k else 0
noncomputable def Dz (n k : ℕ) : ℚ :=
  P0q n * Fz n k + P1q n * Fz (n+1) k + P2q n * Fz (n+2) k

opaque Fz_of_le {n k : ℕ} (h : k ≤ n) : Fz n k = Fq n k := by simp [Fz, h]
opaque Fz_of_gt {n k : ℕ} (h : n < k) : Fz n k = 0 := by simp [Fz, not_le.mpr h]

opaque Dz_interior_eq_Cq {n k : ℕ} (hk : k < n) : Dz n k = Cq n k := by
  unfold Dz Cq
  rw [Fz_of_le (show k ≤ n by omega), Fz_of_le (show k ≤ n+1 by omega), Fz_of_le (show k ≤ n+2 by omega)]

opaque Dz_boundary_sum (n : ℕ) :
    Dz n n + Dz n (n+1) + Dz n (n+2) = - Uq n n * Fq n n := by
  unfold Dz
  rw [Fz_of_le (show n ≤ n by omega), Fz_of_le (show n ≤ n+1 by omega), Fz_of_le (show n ≤ n+2 by omega)]
  rw [Fz_of_gt (show n < n+1 by omega), Fz_of_le (show n+1 ≤ n+1 by omega), Fz_of_le (show n+1 ≤ n+2 by omega)]
  rw [Fz_of_gt (show n < n+2 by omega), Fz_of_gt (show n+1 < n+2 by omega), Fz_of_le (show n+2 ≤ n+2 by omega)]
  rw [Fq_boundary_10, Fq_boundary_20, Fq_boundary_11, Fq_boundary_21, Fq_boundary_22]
  -- Now factor out the final summand and use the rational boundary identity.
  ring_nf
  have hbid : Uq ↑n ↑n + P0q ↑n + P1q ↑n * br10 ↑n + P2q ↑n * br20 ↑n + P1q ↑n * br11 ↑n + P2q ↑n * br21 ↑n + P2q ↑n * br22 ↑n = 0 := by
    -- same proof as original_boundary_identity
    have h1 : (4*(n:ℚ)+1) ≠ 0 := by positivity
    have h3 : (4*(n:ℚ)+3) ≠ 0 := by positivity
    have h5 : (4*(n:ℚ)+5) ≠ 0 := by positivity
    have h7 : (4*(n:ℚ)+7) ≠ 0 := by positivity
    have hn1 : ((n:ℚ)+1) ≠ 0 := by positivity
    have hn2 : ((n:ℚ)+2) ≠ 0 := by positivity
    have hU : Uden n n ≠ 0 := by
      unfold Uden
      repeat' apply mul_ne_zero
      · norm_num
      · norm_num
      · positivity
    unfold Uq br10 br20 br11 br21 br22 P0q P1q P2q
    field_simp [hU,h1,h3,h5,h7,hn1,hn2]
    unfold Unum Uden
    ring
  linear_combination (Fq n n) * hbid


opaque sum_range_telescoping_Q (H : ℕ → ℚ) (n : ℕ) :
    Finset.sum (Finset.range n) (fun k => H (k+1) - H k) = H n - H 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

opaque sum_Dz_eq_zero (n : ℕ) : Finset.sum (Finset.range (n+3)) (fun k => Dz n k) = 0 := by
  have hsplit : Finset.sum (Finset.range (n+3)) (fun k => Dz n k) =
      Finset.sum (Finset.range n) (fun k => Dz n k) + Dz n n + Dz n (n+1) + Dz n (n+2) := by
    rw [show n+3 = (n+2)+1 by omega, Finset.sum_range_succ]
    rw [show n+2 = (n+1)+1 by omega, Finset.sum_range_succ]
    rw [show n+1 = n+1 by rfl, Finset.sum_range_succ]
  rw [hsplit]
  have hinterior : Finset.sum (Finset.range n) (fun k => Dz n k) = Uq n n * Fq n n := by
    calc
      Finset.sum (Finset.range n) (fun k => Dz n k)
          = Finset.sum (Finset.range n) (fun k => Uq n (k+1) * Fq n (k+1) - Uq n k * Fq n k) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hklt : k < n := by simpa using Finset.mem_range.mp hk
              rw [Dz_interior_eq_Cq hklt, interior_Cq_eq_tel hklt]
      _ = Uq n n * Fq n n - Uq n 0 * Fq n 0 := by
              simpa [Nat.cast_add] using sum_range_telescoping_Q (fun k => Uq n k * Fq n k) n
      _ = Uq n n * Fq n n := by rw [Uq_zero_right]; ring
  rw [hinterior]
  have hb := Dz_boundary_sum n
  linear_combination hb


noncomputable def Oq (n k : ℕ) : ℚ :=
  ((Nat.choose n k) : ℚ)^2 * (Nat.choose (n+k) k : ℚ) * (Nat.choose (3*n+2*k) n : ℚ)

opaque choose_cast_factorial_ratio {n k : ℕ} (hk : k ≤ n) :
    (Nat.choose n k : ℚ) = ((Nat.factorial n : ℕ) : ℚ) /
      (((Nat.factorial k : ℕ) : ℚ) * ((Nat.factorial (n-k) : ℕ) : ℚ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hkf : ((Nat.factorial k : ℕ) : ℚ) ≠ 0 := by positivity
  have hnf : ((Nat.factorial (n-k) : ℕ) : ℚ) ≠ 0 := by positivity
  have hq := congrArg (fun x : ℕ => (x : ℚ)) h
  norm_num [Nat.cast_mul] at hq
  field_simp [hkf,hnf]
  simpa [mul_assoc] using hq

opaque Oq_eq_Fq {n k : ℕ} (hk : k ≤ n) : Oq n k = Fq n k := by
  unfold Oq Fq
  have h1 := choose_cast_factorial_ratio (n := n) (k := k) hk
  have h2 := choose_cast_factorial_ratio (n := n+k) (k := k) (by omega)
  have h3 := choose_cast_factorial_ratio (n := 3*n+2*k) (k := n) (by omega)
  have hkf : ((Nat.factorial k : ℕ) : ℚ) ≠ 0 := by positivity
  have hnkf : ((Nat.factorial (n-k) : ℕ) : ℚ) ≠ 0 := by positivity
  have hnf : ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := by positivity
  rw [h1,h2,h3]
  have hs1 : n+k-k = n := by omega
  have hs2 : 3*n+2*k-n = 2*n+2*k := by omega
  rw [hs1, hs2]
  field_simp [hkf,hnkf,hnf]

opaque cast_a_eq_sum_Fq (n : ℕ) :
    ((a n : ℕ) : ℚ) = Finset.sum (Finset.range (n+1)) (fun k => Fq n k) := by
  unfold a
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk
  have hO := Oq_eq_Fq (n := n) (k := k) hkle
  unfold Oq at hO
  norm_num [Nat.cast_mul, Nat.cast_pow]
  exact hO

opaque cast_a_eq_sum_Fz_range (n : ℕ) :
    ((a n : ℕ) : ℚ) = Finset.sum (Finset.range (n+3)) (fun k => Fz n k) := by
  rw [cast_a_eq_sum_Fq]
  rw [← Finset.sum_subset (s₁ := Finset.range (n+1)) (s₂ := Finset.range (n+3))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkle : k ≤ n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk
    simp [Fz, hkle]
  · intro k hk
    simp at hk ⊢
    omega
  · intro k hkbig hksmall
    have hkgt : n < k := by
      have hkge : n+1 ≤ k := by simpa [Nat.lt_succ_iff] using hksmall
      omega
    simp [Fz, not_le.mpr hkgt]

opaque original_recurrence_a (n : ℕ) :
    P0q n * ((a n : ℕ) : ℚ) + P1q n * ((a (n+1) : ℕ) : ℚ) + P2q n * ((a (n+2) : ℕ) : ℚ) = 0 := by
  have h := sum_Dz_eq_zero n
  unfold Dz at h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at h
  have ha0 : ((a n : ℕ) : ℚ) = Finset.sum (Finset.range (n+3)) (fun k => Fz n k) := cast_a_eq_sum_Fz_range n
  have ha1 : ((a (n+1) : ℕ) : ℚ) = Finset.sum (Finset.range (n+3)) (fun k => Fz (n+1) k) := by
    rw [cast_a_eq_sum_Fq]
    rw [← Finset.sum_subset (s₁ := Finset.range (n+2)) (s₂ := Finset.range (n+3))]
    · apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n+1 := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk
      simp [Fz, hkle]
    · intro k hk
      simp at hk ⊢
      omega
    · intro k hkbig hksmall
      have hkgt : n+1 < k := by
        have hkge : n+2 ≤ k := by simpa [Nat.lt_succ_iff] using hksmall
        omega
      simp [Fz, not_le.mpr hkgt]
  have ha2 : ((a (n+2) : ℕ) : ℚ) = Finset.sum (Finset.range (n+3)) (fun k => Fz (n+2) k) := by
    rw [cast_a_eq_sum_Fq]
    apply Finset.sum_congr rfl
    intro k hk
    have hkle : k ≤ n+2 := by simpa using hk
    simp [Fz, hkle]
  rw [← ha0, ← ha1, ← ha2] at h
  simpa [Nat.cast_add] using h

end

noncomputable section

noncomputable def Gq (n k : ℕ) : ℚ :=
  ((n+1 : ℕ) : ℚ) * ((Nat.factorial (3*n) : ℕ) : ℚ) *
    (((Nat.factorial (2*n-k) : ℕ) : ℚ)^2) * (((Nat.factorial (n+k) : ℕ) : ℚ)) /
  ((((Nat.factorial k : ℕ) : ℚ) * (((Nat.factorial n : ℕ) : ℚ)^3) *
    ((Nat.factorial (n+1-2*k) : ℕ) : ℚ) * (((Nat.factorial (n-k) : ℕ) : ℚ)^2) *
    ((Nat.factorial (2*n+2*k) : ℕ) : ℚ)))

def TGk (n k : ℚ) : ℚ :=
  (n+k+1)*(n+1-2*k)*(n-2*k)*(n-k)^2 /
    ((k+1)*(2*n-k)^2*(2*n+2*k+1)*(2*n+2*k+2))

def TGn1 (n k : ℚ) : ℚ :=
  (n+2)/(n+1) * (3*n+1)*(3*n+2)*(3*n+3) * ((2*n-k+1)*(2*n-k+2))^2 * (n+k+1) /
    ((n+1)^3 * (n+2-2*k) * (n+1-k)^2 * (2*n+2*k+1)*(2*n+2*k+2))


lemma Gq_k_ratio {n k : ℕ} (h2 : 2*(k+1) ≤ n+1) (hk : k < n) :
    Gq n (k+1) = Gq n k * TGk n k := by
  unfold Gq TGk
  have hkfac : ((Nat.factorial k : ℕ) : ℚ) ≠ 0 := fac_cast_ne k
  have hk1fac : ((Nat.factorial (k+1) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (k+1)
  have hnfac : ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := fac_cast_ne n
  have h3nfac : ((Nat.factorial (3*n) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (3*n)
  have h2nkfac : ((Nat.factorial (2*n-k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n-k)
  have h2nk1fac : ((Nat.factorial (2*n-(k+1)) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n-(k+1))
  have hnkkfac : ((Nat.factorial (n+k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n+k)
  have hnk1kfac : ((Nat.factorial (n+(k+1)) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n+(k+1))
  have hn12kfac : ((Nat.factorial (n+1-2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n+1-2*k)
  have hn12k1fac : ((Nat.factorial (n+1-2*(k+1)) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n+1-2*(k+1))
  have hnkfac : ((Nat.factorial (n-k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n-k)
  have hnk1fac : ((Nat.factorial (n-(k+1)) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n-(k+1))
  have h2n2kfac : ((Nat.factorial (2*n+2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n+2*k)
  have h2n2k1fac : ((Nat.factorial (2*n+2*(k+1)) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n+2*(k+1))
  have hk1pos : ((k+1:ℕ):ℚ) ≠ 0 := by positivity
  have h2nkpos : ((2*n-k:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < 2*n-k))
  have h2nkQ : (2*(n:ℚ) - (k:ℚ)) ≠ 0 := by
    have : (k:ℚ) < 2*n := by exact_mod_cast (by omega : k < 2*n)
    linarith
  have h2nkQ' : ((2*n:ℕ):ℚ) - (k:ℚ) ≠ 0 := by
    norm_num [Nat.cast_mul]
    exact h2nkQ
  have h2nkQ'' : (↑n * 2 - ↑k : ℚ) ≠ 0 := by
    intro h0
    apply h2nkQ
    linarith
  have hApos : ((n+1-2*k:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n+1-2*k))
  have hBpos : ((n-2*k:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n-2*k))
  have hnkpos : ((n-k:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n-k))
  rw [show n+(k+1)=n+k+1 by omega, Nat.factorial_succ]
  have h2nksub : 2*n-k = (2*n-(k+1))+1 := by omega
  -- use manual factorial relation for decreasing (2n-k)
  have h2nk_rel : ((Nat.factorial (2*n-k) : ℕ) : ℚ) = ((2*n-k:ℕ):ℚ) * ((Nat.factorial (2*n-(k+1)) : ℕ) : ℚ) := by
    rw [h2nksub, Nat.factorial_succ]
    norm_num [Nat.cast_mul]
  rw [h2nk_rel]
  have hn1rel : ((Nat.factorial (n+1-2*k) : ℕ) : ℚ) =
      ((n+1-2*k:ℕ):ℚ) * ((n-2*k:ℕ):ℚ) * ((Nat.factorial (n+1-2*(k+1)) : ℕ) : ℚ) := by
    have hstep1 : n+1-2*k = (n-2*k)+1 := by omega
    have hstep2 : n-2*k = (n+1-2*(k+1))+1 := by omega
    rw [hstep1, Nat.factorial_succ, hstep2, Nat.factorial_succ]
    norm_num [Nat.cast_mul]
    ring
  rw [hn1rel]
  have hnkrel : ((Nat.factorial (n-k) : ℕ) : ℚ) = ((n-k:ℕ):ℚ) * ((Nat.factorial (n-(k+1)) : ℕ) : ℚ) := by
    have hstep : n-k = n-(k+1)+1 := by omega
    rw [hstep, Nat.factorial_succ]
    norm_num [Nat.cast_mul]
  rw [hnkrel]
  rw [Nat.factorial_succ k]
  rw [show 2*n+2*(k+1)=2*n+2*k+2 by omega]
  rw [show 2*n+2*k+2=(2*n+2*k+1)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ (2*n+2*k)]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : k ≤ 2*n)]
  field_simp [hkfac,hk1fac,hnfac,h3nfac,h2nkfac,h2nk1fac,hnkkfac,hnk1kfac,hn12kfac,hn12k1fac,hnkfac,hnk1fac,h2n2kfac,h2n2k1fac,hk1pos,h2nkpos,h2nkQ,h2nkQ',h2nkQ'',hApos,hBpos,hnkpos]
  · norm_num [Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub (by omega : k ≤ 2*n), Nat.cast_sub (by omega : k+1 ≤ 2*n),
      Nat.cast_sub (by omega : 2*k ≤ n+1), Nat.cast_sub (by omega : 2*k ≤ n),
      Nat.cast_sub (by omega : k ≤ n)] <;> (left; ring_nf)


lemma Gq_n_ratio {n k : ℕ} (h2 : 2*k ≤ n+1) :
    Gq (n+1) k = Gq n k * TGn1 n k := by
  unfold Gq TGn1
  have hA : ((Nat.factorial (3*n) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (3*n)
  have hB : ((Nat.factorial (2*n-k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n-k)
  have hC : ((Nat.factorial (n+k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n+k)
  have hD : ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := fac_cast_ne n
  have hE : ((Nat.factorial (n+1-2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n+1-2*k)
  have hF : ((Nat.factorial (n-k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n-k)
  have hG : ((Nat.factorial (2*n+2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*n+2*k)
  have hD1 : ((Nat.factorial (n+1) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (n+1)
  have hE1 : ((Nat.factorial ((n+1)+1-2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne ((n+1)+1-2*k)
  have hF1 : ((Nat.factorial ((n+1)-k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne ((n+1)-k)
  have hG1 : ((Nat.factorial (2*(n+1)+2*k) : ℕ) : ℚ) ≠ 0 := fac_cast_ne (2*(n+1)+2*k)
  have hn1pos : ((n+1:ℕ):ℚ) ≠ 0 := by positivity
  have hn2m2kpos : (((n+1)+1-2*k:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < (n+1)+1-2*k))
  have hn1mkpos : (((n+1)-k:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < (n+1)-k))
  have hlin1 : ((n:ℚ)+1) ≠ 0 := by positivity
  have hlin2 : ((n:ℚ)+2-2*(k:ℚ)) ≠ 0 := by
    have : (2*(k:ℚ)) < (n:ℚ)+2 := by exact_mod_cast (by omega : 2*k < n+2)
    linarith
  have hlin3 : ((n:ℚ)+1-(k:ℚ)) ≠ 0 := by
    have : (k:ℚ) < (n:ℚ)+1 := by exact_mod_cast (by omega : k < n+1)
    linarith
  have hlin4 : (2*(n:ℚ)+2*(k:ℚ)+1) ≠ 0 := by positivity
  have hlin5 : (2*(n:ℚ)+2*(k:ℚ)+2) ≠ 0 := by positivity
  have hdenT : (((n:ℚ)+1)^3 * ((n:ℚ)+2-2*(k:ℚ)) * ((n:ℚ)+1-(k:ℚ))^2 *
      (2*(n:ℚ)+2*(k:ℚ)+1) * (2*(n:ℚ)+2*(k:ℚ)+2)) ≠ 0 := by
    repeat' apply mul_ne_zero
    · exact pow_ne_zero 3 hlin1
    · exact hlin2
    · exact pow_ne_zero 2 hlin3
    · exact hlin4
    · exact hlin5
  have hdenSub : (((n:ℚ)+2-2*(k:ℚ)) * ((n:ℚ)+1-(k:ℚ))^2) ≠ 0 := by
    apply mul_ne_zero
    · exact hlin2
    · exact pow_ne_zero 2 hlin3
  have hdenGoal : (((n:ℚ)+1-2*(k:ℚ)+1) * ((n:ℚ)-(k:ℚ)+1)^2) ≠ 0 := by
    apply mul_ne_zero
    · have hx : ((n:ℚ)+2-2*(k:ℚ)) ≠ 0 := hlin2
      convert hx using 1 <;> ring_nf
    · have hx : ((n:ℚ)+1-(k:ℚ)) ≠ 0 := hlin3
      apply pow_ne_zero
      convert hx using 1 <;> ring_nf



  rw [show 3*(n+1)=3*n+3 by omega]
  rw [show 3*n+3=(3*n+2)+1 by omega, Nat.factorial_succ]
  rw [show 3*n+2=(3*n+1)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ (3*n)]
  rw [show 2*(n+1)-k = 2*n-k+2 by omega]
  rw [show 2*n-k+2=(2*n-k+1)+1 by omega, Nat.factorial_succ]
  rw [show 2*n-k+1=(2*n-k)+1 by omega, Nat.factorial_succ]
  rw [show (n+1)+k=n+k+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ n]
  have hsub1 : (n+1)+1-2*k = (n+1-2*k)+1 := by omega
  rw [hsub1, Nat.factorial_succ]
  have hsub2 : (n+1)-k = (n-k)+1 := by omega
  rw [hsub2, Nat.factorial_succ]
  rw [show 2*(n+1)+2*k=2*n+2*k+2 by omega]
  rw [show 2*n+2*k+2=(2*n+2*k+1)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ (2*n+2*k)]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : k ≤ 2*n), Nat.cast_sub (by omega : 2*k ≤ n+1), Nat.cast_sub (by omega : k ≤ n)]
  field_simp [hA,hB,hC,hD,hE,hF,hG,hD1,hE1,hF1,hG1,hn1pos,hn2m2kpos,hn1mkpos,hlin1,hlin2,hlin3,hlin4,hlin5,hdenT,hdenSub]
  rw [div_eq_iff hdenGoal]
  ring_nf



def TGn2 (n k : ℚ) : ℚ := TGn1 n k * TGn1 (n+1) k
def Rtransq (n k : ℚ) : ℚ := -18*k*(3*n + 1)*(3*n + 2)*(k - 2*n - 1)^2*(367759776*k^6 - 4421992128*k^5 + 21417410496*k^4 - 53071096224*k^3 + 69827200800*k^2 - 44663291136*k + n*(3831009096*k^6 - 49106375120*k^5 + 252071799616*k^4 - 657964895416*k^3 + 904837990568*k^2 - 596828084544*k + n*(17383908508*k^6 - 240618864488*k^5 + 1322729845252*k^4 - 3667179616584*k^3 + 5303148867852*k^2 - 3616092223904*k + n*(45210903800*k^6 - 686590229376*k^5 + 4092720849790*k^4 - 12169020851574*k^3 + 18632398302974*k^2 - 13163134811880*k + n*(74663265980*k^6 - 1268661787492*k^5 + 8323567246342*k^4 - 26843324456702*k^3 + 43855819859707*k^2 - 32152883458528*k + n*(81906499864*k^6 - 1595962145560*k^5 + 11735867654926*k^4 - 41604826580204*k^3 + 73178015927160*k^2 - 55716686061494*k + n*(60541519824*k^6 - 1396878000900*k^5 + 11778530599498*k^4 - 46659166223700*k^3 + 89287337635185*k^2 - 70539513479272*k + n*(29825069040*k^6 - 851995539792*k^5 + 8489687386572*k^4 - 38372024383770*k^3 + 80925702669224*k^2 - 66099184948814*k + n*(9388811952*k^6 - 355428804168*k^5 + 4367014280784*k^4 - 23159723961574*k^3 + 54729124674863*k^2 - 45812518412288*k + n*(1708387200*k^6 - 96725564208*k^5 + 1565249663736*k^4 - 10138885654788*k^3 + 27458399414154*k^2 - 23103861642482*k + n*(136670976*k^6 - 15474551040*k^5 + 371454287724*k^4 - 3130877820888*k^3 + 10043670039273*k^2 - 8126145254520*k + n*(-1103880960*k^5 + 52451227296*k^4 - 645982070544*k^3 + 2589907523112*k^2 - 1788771271554*k + n*(3335297472*k^4 - 79821510912*k^3 + 443001438360*k^2 - 155451342240*k + n*(-4460002560*k^3 + 44639045568*k^2 + 30254417568*k + n*(1971216000*k^2 + 9899345664*k + n*(844286976*k - 730057536*n - 13620293856) - 115674763284) - 589884159888) - 2001733440651) - 4712236675238) - 7696904553275) - 8175765516242) - 3942010332777) + 3368952090822) + 8899867202595) + 9418443728786) + 6231966864944) + 2737982166512) + 780309315504) + 131093997984) + 9875103360)/((n + 1)^3*(k - n - 2)^2*(k - n - 1)^2*(2*k - n - 3)*(2*k - n - 2)*(2*k + 2*n + 1))
opaque even_boundary_alg_nat (m : ℕ) :
  Rtransq (2*(m:ℚ)) (m:ℚ) + P0q (2*(m:ℚ)) + P1q (2*(m:ℚ))*TGn1 (2*(m:ℚ)) (m:ℚ) + P2q (2*(m:ℚ))*TGn2 (2*(m:ℚ)) (m:ℚ)
    + TGn1 (2*(m:ℚ)) (m:ℚ) * TGk (2*(m:ℚ)+1) (m:ℚ) * (P1q (2*(m:ℚ)) + P2q (2*(m:ℚ))*TGn1 (2*(m:ℚ)+1) ((m:ℚ)+1)) = 0 := by
  unfold Rtransq P0q P1q P2q TGn2
  unfold TGn1 TGk
  field_simp (discharger := positivity)
  ring_nf
  have hD1 : (1 + (m:ℚ)*2 + (m:ℚ)^2) ≠ 0 := by positivity
  have hD2 : (8 + (m:ℚ)*24 + (m:ℚ)^2*26 + (m:ℚ)^3*12 + (m:ℚ)^4*2) ≠ 0 := by positivity
  field_simp [hD1,hD2]
  ring_nf

opaque odd_boundary_alg_nat (m : ℕ) :
  Rtransq (2*(m:ℚ)+1) ((m:ℚ)+1) + P0q (2*(m:ℚ)+1) + P1q (2*(m:ℚ)+1) * TGn1 (2*(m:ℚ)+1) ((m:ℚ)+1) + P2q (2*(m:ℚ)+1) * TGn2 (2*(m:ℚ)+1) ((m:ℚ)+1)
    + P2q (2*(m:ℚ)+1) * TGn1 (2*(m:ℚ)+1) ((m:ℚ)+1) * TGn1 (2*(m:ℚ)+2) ((m:ℚ)+1) * TGk (2*(m:ℚ)+3) ((m:ℚ)+1) = 0 := by
  unfold Rtransq P0q P1q P2q TGn2
  unfold TGn1 TGk
  field_simp (discharger := positivity)
  ring_nf
  have hD1 : (1 + (m:ℚ)*2 + (m:ℚ)^2) ≠ 0 := by positivity
  have hD2 : (8 + (m:ℚ)*24 + (m:ℚ)^2*26 + (m:ℚ)^3*12 + (m:ℚ)^4*2) ≠ 0 := by positivity
  field_simp [hD1,hD2]
  ring_nf


lemma Rtransq_zero (n : ℚ) : Rtransq n 0 = 0 := by
  unfold Rtransq
  simp


opaque cert_nat_direct {n k : ℕ} (h2 : 2*(k+1) ≤ n+1) (hk : k < n) :
  Rtransq (n:ℚ) ((k:ℚ)+1) * TGk (n:ℚ) (k:ℚ) - Rtransq (n:ℚ) (k:ℚ)
    = P0q (n:ℚ) + P1q (n:ℚ)*TGn1 (n:ℚ) (k:ℚ) + P2q (n:ℚ)*TGn2 (n:ℚ) (k:ℚ) := by
  have hkq : (k:ℚ) < n := by exact_mod_cast hk
  have h2q : 2*(k:ℚ)+2 ≤ (n:ℚ)+1 := by exact_mod_cast h2
  unfold Rtransq TGn2 P0q P1q P2q
  unfold TGk TGn1
  field_simp (discharger := first | positivity | linarith)
  ring


lemma sum_range_tel_Q (H : ℕ → ℚ) (n : ℕ) :
    Finset.sum (Finset.range n) (fun k => H (k+1) - H k) = H n - H 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

def gsum (n : ℕ) : ℚ := Finset.sum (Finset.range ((n+1)/2 + 1)) (fun k => Gq n k)

opaque trans_interior {n k : ℕ} (h2 : 2*(k+1) ≤ n+1) (hk : k < n) :
    P0q n * Gq n k + P1q n * Gq (n+1) k + P2q n * Gq (n+2) k
    = Rtransq n (k+1) * Gq n (k+1) - Rtransq n k * Gq n k := by
  rw [Gq_k_ratio h2 hk, Gq_n_ratio (by omega : 2*k ≤ n+1)]
  rw [Gq_n_ratio (n:=n+1) (k:=k) (by omega : 2*k ≤ n+2)]
  rw [Gq_n_ratio (n:=n) (k:=k) (by omega : 2*k ≤ n+1)]
  have hc := cert_nat_direct h2 hk
  have hcmul := congrArg (fun x : ℚ => x * Gq n k) hc
  unfold TGn2 at hcmul
  ring_nf at hcmul ⊢
  simpa [Nat.cast_add] using hcmul.symm


def fullTerm (n k : ℕ) : ℚ := P0q n * Gq n k + P1q n * Gq (n+1) k + P2q n * Gq (n+2) k

def Hterm (n k : ℕ) : ℚ := Rtransq n k * Gq n k

opaque even_recurrence_gsum (m : ℕ) :
    P0q (2*m:ℕ) * gsum (2*m) + P1q (2*m:ℕ) * gsum (2*m+1) + P2q (2*m:ℕ) * gsum (2*m+2) = 0 := by
  have hr0 : Rtransq ((2*m:ℕ):ℚ) 0 = 0 := Rtransq_zero _
  unfold gsum
  have hA : ((2*m + 1)/2 + 1) = m+1 := by omega
  have hB : (((2*m+1) + 1)/2 + 1) = m+2 := by omega
  have hC : (((2*m+2) + 1)/2 + 1) = m+2 := by omega
  rw [hA, hB, hC]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  -- split common ranges
  rw [Finset.sum_range_succ (fun k => P0q ↑(2*m) * Gq (2*m) k) m]
  rw [Finset.sum_range_succ (fun k => P1q ↑(2*m) * Gq (2*m+1) k) (m+1)]
  rw [Finset.sum_range_succ (fun k => P2q ↑(2*m) * Gq (2*m+2) k) (m+1)]
  rw [Finset.sum_range_succ (fun k => P1q ↑(2*m) * Gq (2*m+1) k) m]
  rw [Finset.sum_range_succ (fun k => P2q ↑(2*m) * Gq (2*m+2) k) m]
  -- now interior sum over range m plus two boundary groups
  have hint : Finset.sum (Finset.range m) (fun k => P0q ↑(2*m) * Gq (2*m) k + P1q ↑(2*m) * Gq (2*m+1) k + P2q ↑(2*m) * Gq (2*m+2) k)
      = Hterm (2*m) m - Hterm (2*m) 0 := by
    calc
      Finset.sum (Finset.range m) (fun k => P0q ↑(2*m) * Gq (2*m) k + P1q ↑(2*m) * Gq (2*m+1) k + P2q ↑(2*m) * Gq (2*m+2) k)
          = Finset.sum (Finset.range m) (fun k => Hterm (2*m) (k+1) - Hterm (2*m) k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hklt : k < m := by simpa using hk
            unfold Hterm
            simpa [fullTerm, Nat.cast_mul] using (trans_interior (n:=2*m) (k:=k) (by omega) (by omega))
      _ = Hterm (2*m) m - Hterm (2*m) 0 := sum_range_tel_Q (fun k => Hterm (2*m) k) m
  have hint_sep :
      (Finset.sum (Finset.range m) (fun k => P0q ↑(2*m) * Gq (2*m) k)) +
      (Finset.sum (Finset.range m) (fun k => P1q ↑(2*m) * Gq (2*m+1) k)) +
      (Finset.sum (Finset.range m) (fun k => P2q ↑(2*m) * Gq (2*m+2) k))
      = Hterm (2*m) m - Hterm (2*m) 0 := by
    rw [← hint]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  unfold Hterm at hr0
  -- Boundary algebra should close with ratio lemmas and even_boundary_alg_nat
  have hg1 : Gq (2*m+1) m = Gq (2*m) m * TGn1 (2*(m:ℚ)) (m:ℚ) := by
    simpa [Nat.cast_mul] using (Gq_n_ratio (n:=2*m) (k:=m) (by omega))
  have hg2 : Gq (2*m+2) m = Gq (2*m) m * TGn2 (2*(m:ℚ)) (m:ℚ) := by
    rw [Gq_n_ratio (n:=2*m+1) (k:=m) (by omega)]
    rw [Gq_n_ratio (n:=2*m) (k:=m) (by omega)]
    simp [TGn2, Nat.cast_mul, Nat.cast_add]
    ring
  have hgb1 : Gq (2*m+1) (m+1) = Gq (2*m) m * TGn1 (2*(m:ℚ)) (m:ℚ) * TGk (2*(m:ℚ)+1) (m:ℚ) := by
    rw [Gq_k_ratio (n:=2*m+1) (k:=m) (by omega) (by omega)]
    rw [Gq_n_ratio (n:=2*m) (k:=m) (by omega)]
    simp [Nat.cast_mul, Nat.cast_add]
  have hgb2 : Gq (2*m+2) (m+1) = Gq (2*m) m * TGn1 (2*(m:ℚ)) (m:ℚ) * TGk (2*(m:ℚ)+1) (m:ℚ) * TGn1 (2*(m:ℚ)+1) ((m:ℚ)+1) := by
    rw [Gq_n_ratio (n:=2*m+1) (k:=m+1) (by omega)]
    rw [hgb1]
    simp [Nat.cast_mul, Nat.cast_add]
  have hb := even_boundary_alg_nat m
  -- pure algebra using boundary identity times Gq(2m,m)
  rw [hg1, hg2, hgb1, hgb2]
  unfold Hterm at hint_sep
  norm_num at hint_sep
  have hr0' : Rtransq (2*(m:ℚ)) 0 = 0 := by simpa [Nat.cast_mul] using hr0
  rw [hr0'] at hint_sep
  norm_num [Nat.cast_mul, Nat.cast_add] at hb hint_sep ⊢
  ring_nf at hb hint_sep ⊢
  linear_combination (norm := ring_nf) hint_sep + (Gq (2*m) m) * hb


opaque odd_recurrence_gsum (m : ℕ) :
    P0q (2*m+1:ℕ) * gsum (2*m+1) + P1q (2*m+1:ℕ) * gsum (2*m+2) + P2q (2*m+1:ℕ) * gsum (2*m+3) = 0 := by
  have hr0 : Rtransq ((2*m+1:ℕ):ℚ) 0 = 0 := Rtransq_zero _
  unfold gsum
  have hA : (((2*m+1) + 1)/2 + 1) = m+2 := by omega
  have hB : (((2*m+2) + 1)/2 + 1) = m+2 := by omega
  have hC : (((2*m+3) + 1)/2 + 1) = m+3 := by omega
  rw [hA, hB, hC]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  -- split ranges: first two to m+1, third to m+2
  rw [Finset.sum_range_succ (fun k => P0q ↑(2*m+1) * Gq (2*m+1) k) (m+1)]
  rw [Finset.sum_range_succ (fun k => P1q ↑(2*m+1) * Gq (2*m+2) k) (m+1)]
  rw [Finset.sum_range_succ (fun k => P2q ↑(2*m+1) * Gq (2*m+3) k) (m+2)]
  rw [Finset.sum_range_succ (fun k => P2q ↑(2*m+1) * Gq (2*m+3) k) (m+1)]
  have hint : Finset.sum (Finset.range (m+1)) (fun k => P0q ↑(2*m+1) * Gq (2*m+1) k + P1q ↑(2*m+1) * Gq (2*m+2) k + P2q ↑(2*m+1) * Gq (2*m+3) k)
      = Hterm (2*m+1) (m+1) - Hterm (2*m+1) 0 := by
    calc
      Finset.sum (Finset.range (m+1)) (fun k => P0q ↑(2*m+1) * Gq (2*m+1) k + P1q ↑(2*m+1) * Gq (2*m+2) k + P2q ↑(2*m+1) * Gq (2*m+3) k)
          = Finset.sum (Finset.range (m+1)) (fun k => Hterm (2*m+1) (k+1) - Hterm (2*m+1) k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hklt : k < m+1 := by simpa using hk
            unfold Hterm
            simpa [fullTerm, Nat.cast_mul, Nat.cast_add] using (trans_interior (n:=2*m+1) (k:=k) (by omega) (by omega))
      _ = Hterm (2*m+1) (m+1) - Hterm (2*m+1) 0 := sum_range_tel_Q (fun k => Hterm (2*m+1) k) (m+1)
  have hint_sep :
      (Finset.sum (Finset.range (m+1)) (fun k => P0q ↑(2*m+1) * Gq (2*m+1) k)) +
      (Finset.sum (Finset.range (m+1)) (fun k => P1q ↑(2*m+1) * Gq (2*m+2) k)) +
      (Finset.sum (Finset.range (m+1)) (fun k => P2q ↑(2*m+1) * Gq (2*m+3) k))
      = Hterm (2*m+1) (m+1) - Hterm (2*m+1) 0 := by
    rw [← hint]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  unfold Hterm at hint_sep
  norm_num [Nat.cast_mul, Nat.cast_add] at hint_sep
  have hr0' : Rtransq (2*(m:ℚ)+1) 0 = 0 := by simpa [Nat.cast_mul, Nat.cast_add] using hr0
  rw [hr0'] at hint_sep
  have b0 : Gq (2*m+2) (m+1) = Gq (2*m+1) (m+1) * TGn1 (2*(m:ℚ)+1) ((m:ℚ)+1) := by
    simpa [Nat.cast_mul, Nat.cast_add] using (Gq_n_ratio (n:=2*m+1) (k:=m+1) (by omega))
  have b1 : Gq (2*m+3) (m+1) = Gq (2*m+1) (m+1) * TGn2 (2*(m:ℚ)+1) ((m:ℚ)+1) := by
    rw [Gq_n_ratio (n:=2*m+2) (k:=m+1) (by omega)]
    rw [Gq_n_ratio (n:=2*m+1) (k:=m+1) (by omega)]
    simp [TGn2, Nat.cast_mul, Nat.cast_add]
    ring
  have b2 : Gq (2*m+3) (m+2) = Gq (2*m+1) (m+1) * TGn1 (2*(m:ℚ)+1) ((m:ℚ)+1) * TGn1 (2*(m:ℚ)+2) ((m:ℚ)+1) * TGk (2*(m:ℚ)+3) ((m:ℚ)+1) := by
    rw [Gq_k_ratio (n:=2*m+3) (k:=m+1) (by omega) (by omega)]
    rw [Gq_n_ratio (n:=2*m+2) (k:=m+1) (by omega)]
    rw [Gq_n_ratio (n:=2*m+1) (k:=m+1) (by omega)]
    simp [Nat.cast_mul, Nat.cast_add]
  have hb := odd_boundary_alg_nat m
  rw [b0, b1, b2]
  norm_num [Nat.cast_mul, Nat.cast_add] at hb hint_sep ⊢
  ring_nf at hb hint_sep ⊢
  linear_combination (norm := ring_nf) hint_sep + (Gq (2*m+1) (m+1)) * hb


opaque transformed_recurrence_gsum (n : ℕ) :
    P0q (n:ℚ) * gsum n + P1q (n:ℚ) * gsum (n+1) + P2q (n:ℚ) * gsum (n+2) = 0 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · convert even_recurrence_gsum m using 1 <;> ring_nf
  · convert odd_recurrence_gsum m using 1 <;> ring_nf

end

noncomputable section

lemma P2q_nat_ne_zero (n : ℕ) : P2q n ≠ 0 := by
  unfold P2q
  have h1 : (4*(n:ℚ)+5) ≠ 0 := by positivity
  have h2 : (4*(n:ℚ)+7) ≠ 0 := by positivity
  have h3 : ((n:ℚ)+2) ≠ 0 := by positivity
  have h4 : (5616*(n:ℚ)^4+14040*(n:ℚ)^3+12915*(n:ℚ)^2+5183*(n:ℚ)+770) ≠ 0 := by positivity
  repeat' apply mul_ne_zero
  · norm_num
  · exact pow_ne_zero 2 h1
  · exact pow_ne_zero 2 h2
  · exact pow_ne_zero 3 h3
  · exact h4

lemma a0_g0 : ((a 0 : ℕ) : ℚ) = gsum 0 := by
  norm_num [a, gsum, Gq]

lemma a1_g1 : ((a 1 : ℕ) : ℚ) = gsum 1 := by
  norm_num [a, gsum, Gq, Finset.sum_range_succ]

lemma equal_of_same_recurrence
    (A B : ℕ → ℚ)
    (h0 : A 0 = B 0) (h1 : A 1 = B 1)
    (hA : ∀ n : ℕ, P0q (n:ℚ) * A n + P1q (n:ℚ) * A (n+1) + P2q (n:ℚ) * A (n+2) = 0)
    (hB : ∀ n : ℕ, P0q (n:ℚ) * B n + P1q (n:ℚ) * B (n+1) + P2q (n:ℚ) * B (n+2) = 0) :
    ∀ n, A n = B n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => exact h0
      | 1 => exact h1
      | m+2 =>
          have hm0 := ih m (by omega)
          have hm1 := ih (m+1) (by omega)
          have hrecA := hA m
          have hrecB := hB m
          rw [hm0, hm1] at hrecA
          have hsub : P2q (m:ℚ) * A (m+2) = P2q (m:ℚ) * B (m+2) := by
            linear_combination hrecA - hrecB
          exact mul_left_cancel₀ (P2q_nat_ne_zero m) hsub

lemma cast_a_eq_gsum (n : ℕ) : ((a n : ℕ) : ℚ) = gsum n := by
  exact equal_of_same_recurrence (fun n => ((a n : ℕ) : ℚ)) gsum a0_g0 a1_g1 original_recurrence_a transformed_recurrence_gsum n

end


open Nat Finset


lemma factorial_factorization_eq_div_of_lt_sq {p m : ℕ} (hp : Nat.Prime p) (hm : m < p^2) :
    (m !).factorization p = m / p := by
  by_cases hm0 : m = 0
  · simp [hm0]
  · have hlog : Nat.log p m < 2 := by
      rw [Nat.log_lt_iff_lt_pow hp.one_lt hm0]
      simpa using hm
    rw [Nat.factorization_factorial hp hlog]
    rw [Finset.sum_Ico_succ_top]
    · simp
    · norm_num

lemma arith1 {A B C : ℕ} (hA : 1 ≤ A) (hC : C ≤ 1) : 1 + C ≤ 2*A + B := by omega
lemma arith2 {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) : 1 + 2 ≤ 2*A + B := by omega

lemma floorineq {p n k : ℕ} (hp5 : 5 ≤ p) (hnp : n < p) (h2p : 2*p < 3*n) (hk : 2*k ≤ n+1) :
    3 ≤ (3*n)/p + 2*((2*n-k)/p) + ((n+k)/p) - ((2*n+2*k)/p) := by
  have hp0 : 0 < p := by omega
  have h3lt : 3*n < 3*p := by omega
  have h3div : (3*n)/p = 2 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · simpa [Nat.succ_eq_add_one, mul_comm, mul_left_comm, mul_assoc] using h3lt
  have hA1 : 1 ≤ (2*n-k)/p := by
    rw [Nat.le_div_iff_mul_le hp0]
    omega
  have hC2 : (2*n+2*k)/p ≤ 2 := by
    rw [Nat.div_le_iff_le_mul_add_pred hp0]
    omega
  have hmain : 1 ≤ 2*((2*n-k)/p) + ((n+k)/p) - ((2*n+2*k)/p) := by
    by_cases hC : (2*n+2*k)/p ≤ 1
    · apply Nat.le_sub_of_add_le
      exact arith1 (A := (2*n-k)/p) (B := (n+k)/p) (C := (2*n+2*k)/p) hA1 hC
    · have hCeq : (2*n+2*k)/p = 2 := by omega
      have hB1 : 1 ≤ (n+k)/p := by
        rw [Nat.le_div_iff_mul_le hp0]
        have : 2*p ≤ 2*n+2*k := by
          have := (Nat.le_div_iff_mul_le hp0).mp (by omega : 2 ≤ (2*n+2*k)/p)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        omega
      apply Nat.le_sub_of_add_le
      rw [hCeq]
      exact arith2 (A := (2*n-k)/p) (B := (n+k)/p) hA1 hB1
  rw [h3div]
  apply Nat.le_sub_of_add_le
  omega

lemma factorial_padicValRat_eq_div {p m : ℕ} (hp : Nat.Prime p) (hm : m < p^2) :
    padicValRat p (((m ! : ℕ) : ℚ)) = ((m / p : ℕ) : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.of_nat]
  rw [← Nat.factorization_def (m !) hp, factorial_factorization_eq_div_of_lt_sq hp hm]


lemma fact_ne (m : ℕ) : (((m ! : ℕ) : ℚ) ≠ 0) := by exact_mod_cast Nat.factorial_ne_zero m

lemma factorial_sq_padicValRat_eq {p m : ℕ} (hp : Nat.Prime p) (hm : m < p^2) :
    padicValRat p ((((m ! : ℕ) : ℚ)^2)) = ((2 * (m / p) : ℕ) : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.pow (fact_ne m)]
  rw [factorial_padicValRat_eq_div hp hm]
  norm_num

lemma factorial_cube_padicValRat_eq {p m : ℕ} (hp : Nat.Prime p) (hm : m < p^2) :
    padicValRat p ((((m ! : ℕ) : ℚ)^3)) = ((3 * (m / p) : ℕ) : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.pow (fact_ne m)]
  rw [factorial_padicValRat_eq_div hp hm]
  norm_num

lemma div_le_padicVal_nsucc {p n k : ℕ} (hp : Nat.Prime p) (hnp : n < p) (hk : 2*k ≤ n+1) :
    (((n+1-2*k)/p : ℕ) : ℤ) ≤ padicValRat p ((↑(n+1) : ℚ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : n+1-2*k ≤ p := by omega
  have hdivle : (n+1-2*k)/p ≤ 1 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [Nat.div_le_iff_le_mul_add_pred (Nat.pos_of_ne_zero hp0)]
      omega
  by_cases h0 : (n+1-2*k)/p = 0
  · rw [h0]; simpa [Nat.cast_add] using zero_le_padicValRat_of_nat (p:=p) (n+1)
  · have hq1 : (n+1-2*k)/p = 1 := by
      have hpos : 0 < (n+1-2*k)/p := Nat.pos_of_ne_zero h0
      omega
    have hp_le : p ≤ n+1-2*k := by
      have := (Nat.le_div_iff_mul_le hp.pos).mp (by omega : 1 ≤ (n+1-2*k)/p)
      simpa using this
    have hn1eq : n+1 = p := by omega
    rw [hq1, hn1eq]
    rw [padicValRat.of_nat]
    rw [padicValNat_self]

lemma Gq_val_ge_three {p n k : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnp : n < p) (h2p : 2*p < 3*n) (hk : 2*k ≤ n+1) (hkn : k ≤ n) :
    3 ≤ padicValRat p (Gq n k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3n : 3*n < p^2 := by nlinarith [hp5, hnp]
  have h2nk : 2*n-k < p^2 := by omega
  have hnk : n+k < p^2 := by nlinarith [hp5, hnp, hkn]
  have h2n2k : 2*n+2*k < p^2 := by nlinarith [hp5, hnp, hkn]
  have hklt : k < p^2 := by nlinarith [hp5, hnp, hkn]
  have hnlt2 : n < p^2 := by nlinarith [hp5, hnp]
  have hn12k : n+1-2*k < p^2 := by omega
  have hnk2 : n-k < p^2 := by omega
  have hn1nonneg : 0 ≤ padicValRat p ((↑(n + 1) : ℚ)) := zero_le_padicValRat_of_nat (p:=p) (n+1)
  have hn1comp := div_le_padicVal_nsucc hp hnp hk
  have hkdiv : k / p = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt hkn hnp)
  have hndiv : n / p = 0 := Nat.div_eq_of_lt hnp
  have hnkdiv : (n-k) / p = 0 := Nat.div_eq_of_lt (by omega)
  have hfloor := floorineq hp5 hnp h2p hk
  have hfloorZ : (3:ℤ) ≤ (((3*n)/p + 2*((2*n-k)/p) + ((n+k)/p) - ((2*n+2*k)/p) : ℕ) : ℤ) := by exact_mod_cast hfloor
  unfold Gq
  rw [padicValRat.div]
  · rw [padicValRat.mul]
    · rw [padicValRat.mul]
      · rw [padicValRat.mul]
        · rw [padicValRat.mul]
          · rw [padicValRat.mul]
            · rw [padicValRat.mul]
              · rw [padicValRat.mul]
                · rw [factorial_padicValRat_eq_div hp h3n,
                    factorial_sq_padicValRat_eq hp h2nk,
                    factorial_padicValRat_eq_div hp hnk,
                    factorial_padicValRat_eq_div hp hklt,
                    factorial_cube_padicValRat_eq hp hnlt2,
                    factorial_padicValRat_eq_div hp hn12k,
                    factorial_sq_padicValRat_eq hp hnk2,
                    factorial_padicValRat_eq_div hp h2n2k]
                  rw [hkdiv, hndiv, hnkdiv]
                  have hfloorZ' : (3:ℤ) ≤ (3*(n:ℤ))/(p:ℤ) + 2*(((2*n-k:ℕ):ℤ)/(p:ℤ)) + (((n:ℤ)+(k:ℤ))/(p:ℤ)) - ((2*(n:ℤ)+2*(k:ℤ))/(p:ℤ)) := by
                    let A := (3*n)/p + 2*((2*n-k)/p) + ((n+k)/p)
                    let B := (2*n+2*k)/p
                    have hAB : B ≤ A := by omega
                    have hInt : (3:ℤ) ≤ (A:ℤ) - (B:ℤ) := by exact_mod_cast hfloor
                    simpa [A, B, Nat.cast_add, Nat.cast_mul] using hInt
                  norm_num [Nat.cast_add, Nat.cast_mul] at hn1nonneg hn1comp hfloorZ' ⊢
                  omega
                all_goals first | positivity | simp [fact_ne, pow_ne_zero]
              all_goals first | positivity | simp [fact_ne, pow_ne_zero]
            all_goals first | positivity | simp [fact_ne, pow_ne_zero]
          all_goals first | positivity | simp [fact_ne, pow_ne_zero]
        all_goals first | positivity | simp [fact_ne, pow_ne_zero]
      all_goals first | positivity | simp [fact_ne, pow_ne_zero]
    all_goals first | positivity | simp [fact_ne, pow_ne_zero]
  · first | positivity | simp [fact_ne, pow_ne_zero]
  · first | positivity | simp [fact_ne, pow_ne_zero]

lemma padicValRat_sum_ge_of_forall_ge {p : ℕ} [Fact p.Prime] {c : ℤ} {s : Finset ℕ} {F : ℕ → ℚ}
    (hF : ∀ i ∈ s, c ≤ padicValRat p (F i)) :
    (Finset.sum s F = 0) ∨ c ≤ padicValRat p (Finset.sum s F) := by
  classical
  revert hF
  refine Finset.induction_on s ?base ?step
  · intro hF; simp
  · intro a s has ih hF
    have hFa : c ≤ padicValRat p (F a) := hF a (Finset.mem_insert_self a s)
    have hFs : ∀ i ∈ s, c ≤ padicValRat p (F i) := by
      intro i hi; exact hF i (Finset.mem_insert_of_mem hi)
    rcases ih hFs with hsum0 | hsumge
    · by_cases hzero : F a + Finset.sum s F = 0
      · left; simpa [Finset.sum_insert has, add_comm] using hzero
      · right
        rw [Finset.sum_insert has]
        rw [hsum0]
        simpa using hFa
    · by_cases hzero : F a + Finset.sum s F = 0
      · left; simpa [Finset.sum_insert has, add_comm] using hzero
      · right
        have hmin := padicValRat.min_le_padicValRat_add (p:=p) hzero
        have hcmin : c ≤ min (padicValRat p (F a)) (padicValRat p (Finset.sum s F)) := le_min hFa hsumge
        rw [Finset.sum_insert has]
        exact le_trans hcmin hmin

lemma dvd_nat_of_padicValRat_cast_ge {p m : ℕ} (hp : Nat.Prime p) (c : ℕ)
    (h : (c : ℤ) ≤ padicValRat p ((m : ℚ))) : p^c ∣ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← padicValRat_of_nat] at h
  have hnat : c ≤ padicValNat p m := by exact_mod_cast h
  exact (padicValNat_dvd_iff c m).mpr (Or.inr hnat)

lemma sum_Gq_divisible {p n : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnp : n < p) (h2p : 2*p < 3*n) :
    let S : ℚ := Finset.sum (Finset.range ((n+1)/2 + 1)) (fun k => Gq n k)
    S = 0 ∨ (3:ℤ) ≤ padicValRat p S := by
  intro S
  haveI : Fact p.Prime := ⟨hp⟩
  apply padicValRat_sum_ge_of_forall_ge
  intro k hk
  have hklt : k < (n+1)/2 + 1 := by simpa using hk
  have hk2 : 2*k ≤ n+1 := by omega
  have hkn : k ≤ n := by omega
  exact Gq_val_ge_three hp hp5 hnp h2p hk2 hkn



/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval $[\lceilrac{2p + 1}{3}
ceil, p - 1]$.
The lower bound $\lceilrac{2p + 1}{3}
ceil$ for $p \in \mathbb{N}$ is expressed using natural number division as $(2 * p + 1 + 2) / 3 = (2 * p + 3) / 3$.
-/


theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hL hU
  have hnp : n < p := by omega
  have h2p : 2*p < 3*n := by omega
  have hEq := cast_a_eq_gsum n
  rcases sum_Gq_divisible hp hp5 hnp h2p with hzero | hval
  · have hzero' : gsum n = 0 := by simpa [gsum] using hzero
    have ha0q : ((a n : ℕ) : ℚ) = 0 := by rw [hEq, hzero']
    have ha0 : a n = 0 := by exact_mod_cast ha0q
    rw [ha0]
    exact dvd_zero _
  · apply dvd_nat_of_padicValRat_cast_ge hp 3
    rwa [hEq]
