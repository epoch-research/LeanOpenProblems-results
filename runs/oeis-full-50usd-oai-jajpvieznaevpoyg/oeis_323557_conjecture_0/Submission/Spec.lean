import FormalConjectures.Util.ProblemImports

open Nat

/--
A323557: G.f.: $\sum_{n\ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 + x^{n+1})^{n+1}}$.
The $m$-th term $a(m)$ is the coefficient of $x^m$, which is explicitly given by the sum:
$$ a(m) = \sum_{n=0}^m \sum_{k=0}^n \binom{n}{k} (-1)^j \binom{n+j}{j},$$
where $j = \frac{m - n(k+1)}{n+1}$, and the term is zero unless $j$ is a natural number.
-/
def a (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) fun n =>
    Finset.sum (Finset.range (n + 1)) fun k =>
      let exp_x_num := n * (k + 1)
      if exp_x_num ≤ m then
        let remainder := m - exp_x_num
        if (n + 1) ∣ remainder then
          let j : ℕ := remainder / (n + 1)
          let c₁ : ℤ := (n.choose k)
          let c₂ : ℤ := (choose (n + j) j)
          let sign : ℤ := if Even j then 1 else -1
          sign * c₁ * c₂
        else
          0
      else
        0


noncomputable section

namespace oeis323557

open Finset
attribute [local instance] Classical.propDecidable


private def termInt (m : ℕ) (x : Sigma fun n : ℕ => ℕ) : ℤ :=
  let n := x.1
  let k := x.2
  let exp_x_num := n * (k + 1)
  if exp_x_num ≤ m then
    let remainder := m - exp_x_num
    if (n + 1) ∣ remainder then
      let j : ℕ := remainder / (n + 1)
      let c₁ : ℤ := (n.choose k)
      let c₂ : ℤ := (choose (n + j) j)
      let sign : ℤ := if Even j then 1 else -1
      sign * c₁ * c₂
    else
      0
  else
    0

private def termZ (m : ℕ) (x : Sigma fun n : ℕ => ℕ) : ZMod 2 :=
  (termInt m x : ZMod 2)

private def idx (m : ℕ) : Finset (Sigma fun n : ℕ => ℕ) :=
  (Finset.range (m + 1)).sigma fun n => Finset.range (n + 1)

private def valid (m n k : ℕ) : Prop :=
  k ≤ n ∧ n * (k + 1) ≤ m ∧ (n + 1) ∣ m - n * (k + 1)

private def J (m n k : ℕ) : ℕ :=
  (m - n * (k + 1)) / (n + 1)

private theorem choose_prod_involution (n k j : ℕ) (hk : k ≤ n) :
    n.choose k * (n + j).choose j = (k + j).choose k * (n + j).choose (n - k) := by
  have hNj : (n + j).choose j = (n + j).choose n := by
    rw [← Nat.choose_symm (n := n + j) (k := j) (by omega)]
    congr 1
    omega
  have hnk : n.choose (n - k) = n.choose k := Nat.choose_symm hk
  have hmul := Nat.choose_mul (n := n + j) (k := n) (s := n - k) (by omega)
  rw [hnk] at hmul
  have hsub1 : n + j - (n - k) = k + j := by omega
  have hsub2 : n - (n - k) = k := by omega
  rw [hsub1, hsub2] at hmul
  rw [hNj]
  nlinarith [hmul]

private theorem valid_eq (h : valid m n k) :
    m = n * (k + 1) + (n + 1) * J m n k := by
  unfold valid at h
  unfold J
  rcases h with ⟨hk, hle, hdvd⟩
  have hdiv := Nat.div_mul_cancel hdvd
  rw [mul_comm (n + 1) ((m - n * (k + 1)) / (n + 1))]
  rw [hdiv]
  exact (Nat.add_sub_of_le hle).symm

private def pairMap (m : ℕ) (x : Sigma fun n : ℕ => ℕ) : Sigma fun n : ℕ => ℕ :=
  let n := x.1
  let k := x.2
  if h : valid m n k then
    ⟨k + J m n k, k⟩
  else
    x

private theorem termZ_zero_of_not_valid {m n k : ℕ} (h : ¬ valid m n k) :
    termZ m ⟨n,k⟩ = 0 := by
  unfold termZ termInt valid at *
  simp only
  by_cases hk : k ≤ n
  · by_cases he : n * (k + 1) ≤ m
    · by_cases hd : (n + 1) ∣ m - n * (k + 1)
      · exact False.elim (h ⟨hk, he, hd⟩)
      · simp [he, hd]
    · simp [he]
  · -- in the actual index set this case will not occur; nevertheless choose is zero.
    by_cases he : n * (k + 1) ≤ m
    · by_cases hd : (n + 1) ∣ m - n * (k + 1)
      · have hc : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
        simp [he, hd, hc]
      · simp [he, hd]
    · simp [he]

private theorem termZ_valid {m n k : ℕ} (h : valid m n k) :
    termZ m ⟨n,k⟩ = ((n.choose k * (n + J m n k).choose (J m n k) : ℕ) : ZMod 2) := by
  unfold termZ termInt valid at *
  rcases h with ⟨hk, he, hd⟩
  by_cases hs : Even ((m - n * (k + 1)) / (n + 1)) <;> simp [he, hd, J, hs]

private theorem valid_pairMap {m n k : ℕ} (h : valid m n k) :
    valid m (k + J m n k) k := by
  rcases h with ⟨hk, he, hd⟩
  have hm := valid_eq (m:=m) (n:=n) (k:=k) ⟨hk, he, hd⟩
  have hcalc : m = (k + J m n k) * (k + 1) + (k + J m n k + 1) * (n - k) := by
    conv_lhs => rw [hm]
    nlinarith [Nat.sub_add_cancel hk]
  refine ⟨by omega, by omega, ?_⟩
  use n - k
  have hrem : m - (k + J m n k) * (k + 1) = (k + J m n k + 1) * (n - k) := by
    nth_rewrite 1 [hcalc]
    omega
  exact hrem

private theorem J_pairMap {m n k : ℕ} (h : valid m n k) :
    J m (k + J m n k) k = n - k := by
  have hv := valid_pairMap (m:=m) (n:=n) (k:=k) h
  rcases h with ⟨hk, he, hd⟩
  have hm := valid_eq (m:=m) (n:=n) (k:=k) ⟨hk, he, hd⟩
  have hcalc : m = (k + J m n k) * (k + 1) + (k + J m n k + 1) * (n - k) := by
    conv_lhs => rw [hm]
    nlinarith [Nat.sub_add_cancel hk]
  change (m - (k + J m n k) * (k + 1)) / (k + J m n k + 1) = n - k
  have hrem : m - (k + J m n k) * (k + 1) = (k + J m n k + 1) * (n - k) := by
    nth_rewrite 1 [hcalc]
    omega
  rw [hrem]
  exact Nat.mul_div_right (n - k) (by omega)

private theorem pairMap_involutive {m : ℕ} {x : Sigma fun n : ℕ => ℕ} (hx : x ∈ idx m) :
    pairMap m (pairMap m x) = x := by
  rcases x with ⟨n,k⟩
  unfold pairMap
  by_cases h : valid m n k
  · simp [h]
    have hv := valid_pairMap (m:=m) (n:=n) (k:=k) h
    have hj := J_pairMap (m:=m) (n:=n) (k:=k) h
    simp [hv, hj]
    rcases h with ⟨hk,_,_⟩
    omega
  · simp [h]

private theorem pairMap_mem {m : ℕ} {x : Sigma fun n : ℕ => ℕ} (hx : x ∈ idx m) :
    pairMap m x ∈ idx m := by
  rcases x with ⟨n,k⟩
  simp [idx] at hx ⊢
  rcases hx with ⟨hnm, hkn⟩
  unfold pairMap
  by_cases h : valid m n k
  · simp [h]
    rcases h with ⟨hk, he, hd⟩
    have hm := valid_eq (m:=m) (n:=n) (k:=k) ⟨hk, he, hd⟩
    have hcalc : m = (k + J m n k) * (k + 1) + (k + J m n k + 1) * (n - k) := by
      conv_lhs => rw [hm]
      nlinarith [Nat.sub_add_cancel hk]
    have hle1 : k + J m n k ≤ (k + J m n k) * (k + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
    have hle2' : (k + J m n k) * (k + 1) ≤
        (k + J m n k) * (k + 1) + (k + J m n k + 1) * (n - k) := Nat.le_add_right _ _
    have hle2 : (k + J m n k) * (k + 1) ≤ m := by
      calc
        (k + J m n k) * (k + 1) ≤
            (k + J m n k) * (k + 1) + (k + J m n k + 1) * (n - k) := hle2'
        _ = m := hcalc.symm
    exact le_trans hle1 hle2
  · simp [h, hnm, hkn]

private theorem term_pair_add_zero {m : ℕ} (hnp : ¬ ∃ r : ℕ, m = r * (r + 1))
    (x : Sigma fun n : ℕ => ℕ) (hx : x ∈ idx m) :
    termZ m x + termZ m (pairMap m x) = 0 := by
  rcases x with ⟨n,k⟩
  by_cases h : valid m n k
  · have hv := valid_pairMap (m:=m) (n:=n) (k:=k) h
    have hj := J_pairMap (m:=m) (n:=n) (k:=k) h
    rw [termZ_valid h]
    simp [pairMap, h]
    rw [termZ_valid hv]
    simp [hj]
    have hp := choose_prod_involution n k (J m n k) h.1
    have hk : k ≤ n := h.1
    have hsum : k + J m n k + (n - k) = n + J m n k := by
      omega
    rw [hsum]
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    rw [hp]
    rw [← two_mul]
    rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2]
    simp
  · simp [pairMap, h, termZ_zero_of_not_valid h]


private theorem central_choose_even {j : ℕ} (hj : 0 < j) : Even ((2*j).choose j) := by
  rcases j with _|r
  · omega
  · have hsym : (2 * (r+1) - 1).choose (r+1) = (2 * (r+1) - 1).choose r := by
      rw [← Nat.choose_symm (n := 2 * (r+1) - 1) (k := r) (by omega)]
      congr 1
      omega
    have hpas := Nat.choose_succ_left (2*(r+1)-1) (r+1) (by omega)
    have hN : 2*(r+1)-1 + 1 = 2*(r+1) := by omega
    rw [hN, hsym] at hpas
    rw [hpas]
    exact Even.add_self _

private theorem fixed_product_zmod_zero (k j : ℕ) (hj : 0 < j) :
    (((k+j).choose k * (k + 2*j).choose j : ℕ) : ZMod 2) = 0 := by
  have hc : Even ((2*j).choose j) := central_choose_even hj
  rcases hc with ⟨t, ht⟩
  have hmul := Nat.choose_mul (n := k + 2*j) (k := k + j) (s := k) (by omega)
  have hsym : (k + 2*j).choose (k+j) = (k + 2*j).choose j := by
    rw [← Nat.choose_symm (n := k + 2*j) (k := j) (by omega)]
    congr 1
    omega
  rw [hsym] at hmul
  have hsub1 : k + 2*j - k = 2*j := by omega
  have hsub2 : k + j - k = j := by omega
  rw [hsub1, hsub2] at hmul
  rw [mul_comm ((k + 2 * j).choose j) ((k+j).choose k)] at hmul
  rw [hmul, ht]
  change (((k + 2 * j).choose k * (t + t) : ℕ) : ZMod 2) = 0
  rw [Nat.mul_add, Nat.cast_add, ← two_mul]
  rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2]
  simp

private theorem pairMap_ne_of_nonzero {m : ℕ} (hnp : ¬ ∃ r : ℕ, m = r * (r + 1))
    (x : Sigma fun n : ℕ => ℕ) (hx : x ∈ idx m) :
    termZ m x ≠ 0 → pairMap m x ≠ x := by
  rcases x with ⟨n,k⟩
  intro hnz hfix
  by_cases h : valid m n k
  · unfold pairMap at hfix
    simp [h] at hfix
    -- now `hfix` says `k + J m n k = n`
    by_cases hj0 : J m n k = 0
    · apply hnp
      use n
      have hm := valid_eq (m:=m) (n:=n) (k:=k) h
      rw [hj0] at hfix hm
      have hk : k = n := by omega
      subst k
      rw [hm]
      omega
    · have hjpos : 0 < J m n k := by omega
      have hz : termZ m ⟨n,k⟩ = 0 := by
        rw [termZ_valid h]
        have hchoose1 : n.choose k = (k + J m n k).choose k := congrArg (fun q => q.choose k) hfix.symm
        have hchoose2 : (n + J m n k).choose (J m n k) = (k + 2 * J m n k).choose (J m n k) := by
          congr 1
          omega
        rw [hchoose1, hchoose2]
        exact fixed_product_zmod_zero k (J m n k) hjpos
      exact hnz hz
  · exact False.elim (hnz (termZ_zero_of_not_valid h))

private theorem a_cast_eq_sum (m : ℕ) :
    (a m : ZMod 2) = ∑ x ∈ idx m, termZ m x := by
  unfold a idx termZ termInt
  simp [Finset.sum_sigma]

end oeis323557

/-- oeis_323557_conjecture_0: Odd terms occur only at positions n*(n+1) for n >= 0 (conjecture; verified for initial 32600 terms). -/
theorem oeis_323557_conjecture_0 (m : ℕ) : Odd (a m) → ∃ n : ℕ, m = n * (n + 1) := by
  intro hodd
  by_contra hnp
  have hcast : (a m : ZMod 2) = 1 := by
    rcases hodd with ⟨z, hz⟩
    rw [hz]
    rw [Int.cast_add, Int.cast_mul]
    change (2 : ZMod 2) * (z : ZMod 2) + 1 = 1
    rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2]
    simp
  have hsum : (∑ x ∈ oeis323557.idx m, oeis323557.termZ m x) = 0 := by
    exact Finset.sum_involution
      (fun x hx => oeis323557.pairMap m x)
      (oeis323557.term_pair_add_zero hnp)
      (oeis323557.pairMap_ne_of_nonzero hnp)
      (fun x hx => oeis323557.pairMap_mem hx)
      (fun x hx => oeis323557.pairMap_involutive hx)
  have ha := oeis323557.a_cast_eq_sum m
  rw [ha, hsum] at hcast
  norm_num at hcast
