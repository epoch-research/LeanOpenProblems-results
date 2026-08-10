import Submission.Build
import Submission.Fac

open Nat Finset BigOperators

namespace Wolst

variable {p : ℕ} [Fact p.Prime]

/-- Fermat quotient: `i^(p-1) = 1 + p·q` for `i ∈ [1,p)`. -/
lemma fermat_quot (i : ℕ) (hi : 0 < i) (hip : i < p) :
    ∃ q : ZMod (p^5), (i : ZMod (p^5))^(p-1) = 1 + (p:ZMod (p^5)) * q := by
  have hproj : proj (p := p) ((i : ZMod (p^5))^(p-1) - 1) = 0 := by
    rw [map_sub, map_pow, proj_natCast, map_one]
    have hne : ((i : ZMod p)) ≠ 0 := cast_ne_zero i hi hip
    rw [ZMod.pow_card_sub_one_eq_one hne, sub_self]
  obtain ⟨z, hz⟩ := dvd_p_of_proj_zero _ hproj
  exact ⟨z, by linear_combination hz⟩

/-- Inverse expansion mod p²: `i⁻¹ = (2 i^(p-2) - i^(2p-3)) + p²·c`. -/
lemma inv_exp1 (i : ℕ) (hi : 0 < i) (hip : i < p) :
    ∃ c : ZMod (p^5),
      (i : ZMod (p^5))⁻¹ = (2 * (i:ZMod (p^5))^(p-2) - (i:ZMod (p^5))^(2*p-3))
        + (p:ZMod (p^5))^2 * c := by
  obtain ⟨q, hq⟩ := fermat_quot i hi hip
  have hu : IsUnit ((i : ZMod (p^5))) := isUnit_cast i hi hip
  have hiinv : (i : ZMod (p^5))⁻¹ * (i:ZMod (p^5)) = 1 := ZMod.inv_mul_of_unit _ hu
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have h1 : (i:ZMod (p^5))^(p-1) = (i:ZMod (p^5))*(i:ZMod (p^5))^(p-2) := by
    conv_lhs => rw [show p-1 = (p-2)+1 from by omega]
    rw [pow_succ]; ring
  have h2 : (i:ZMod (p^5))^(2*p-2) = (i:ZMod (p^5))*(i:ZMod (p^5))^(2*p-3) := by
    conv_lhs => rw [show 2*p-2 = (2*p-3)+1 from by omega]
    rw [pow_succ]; ring
  have h2b : (i:ZMod (p^5))^(2*p-2) = ((i:ZMod (p^5))^(p-1))^2 := by
    rw [← pow_mul]; congr 1; omega
  have e1 : (i:ZMod (p^5))^(p-2) = (i:ZMod (p^5))⁻¹*(i:ZMod (p^5))^(p-1) := by
    rw [h1, ← mul_assoc, hiinv, one_mul]
  have e2 : (i:ZMod (p^5))^(2*p-3) = (i:ZMod (p^5))⁻¹*((i:ZMod (p^5))^(p-1))^2 := by
    rw [← h2b, h2, ← mul_assoc, hiinv, one_mul]
  refine ⟨(i:ZMod (p^5))⁻¹ * q^2, ?_⟩
  rw [e1, e2, hq]; ring

/-- Inverse expansion mod p³: `i⁻² = (3 i^(p-3) - 3 i^(2p-4) + i^(3p-5)) + p³·c`. -/
lemma inv_exp2 (hp5 : 5 ≤ p) (i : ℕ) (hi : 0 < i) (hip : i < p) :
    ∃ c : ZMod (p^5),
      (i : ZMod (p^5))⁻¹^2
        = (3 * (i:ZMod (p^5))^(p-3) - 3*(i:ZMod (p^5))^(2*p-4) + (i:ZMod (p^5))^(3*p-5))
          + (p:ZMod (p^5))^3 * c := by
  obtain ⟨q, hq⟩ := fermat_quot i hi hip
  have hu : IsUnit ((i : ZMod (p^5))) := isUnit_cast i hi hip
  have hiinv : (i : ZMod (p^5))⁻¹ * (i:ZMod (p^5)) = 1 := ZMod.inv_mul_of_unit _ hu
  -- set x = i^(p-1) = 1+p q.  Then 3x - 3x² + x³ = 1 + p³ q³.
  have hx : (i:ZMod (p^5))^(p-1) = 1 + (p:ZMod (p^5))*q := hq
  have e3 : (i:ZMod (p^5))^(p-3) = (i:ZMod (p^5))⁻¹^2 * (i:ZMod (p^5))^(p-1) := by
    have h : (i:ZMod (p^5))^(p-1) = (i:ZMod (p^5))^2 * (i:ZMod (p^5))^(p-3) := by
      rw [← pow_add]; congr 1; omega
    rw [h, ← mul_assoc, show (i:ZMod (p^5))⁻¹^2 * (i:ZMod (p^5))^2 = 1 from by
      rw [← mul_pow, hiinv, one_pow], one_mul]
  have e4 : (i:ZMod (p^5))^(2*p-4) = (i:ZMod (p^5))⁻¹^2 * ((i:ZMod (p^5))^(p-1))^2 := by
    have h : ((i:ZMod (p^5))^(p-1))^2 = (i:ZMod (p^5))^2 * (i:ZMod (p^5))^(2*p-4) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [h, ← mul_assoc, show (i:ZMod (p^5))⁻¹^2 * (i:ZMod (p^5))^2 = 1 from by
      rw [← mul_pow, hiinv, one_pow], one_mul]
  have e5 : (i:ZMod (p^5))^(3*p-5) = (i:ZMod (p^5))⁻¹^2 * ((i:ZMod (p^5))^(p-1))^3 := by
    have h : ((i:ZMod (p^5))^(p-1))^3 = (i:ZMod (p^5))^2 * (i:ZMod (p^5))^(3*p-5) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [h, ← mul_assoc, show (i:ZMod (p^5))⁻¹^2 * (i:ZMod (p^5))^2 = 1 from by
      rw [← mul_pow, hiinv, one_pow], one_mul]
  refine ⟨- ((i:ZMod (p^5))⁻¹^2 * q^3), ?_⟩
  rw [e3, e4, e5, hx]; ring

/-- Power sum `SP c = ∑_{i=1}^{p-1} i^c` in `ZMod (p^5)`. -/
noncomputable def SP (c : ℕ) : ZMod (p^5) := ∑ i ∈ Finset.Ico 1 p, (i:ZMod (p^5))^c

/-- `3·S2` reduces to power sums mod `p³`. -/
lemma three_S2_reduce (hp5 : 5 ≤ p) :
    ∃ c : ZMod (p^5),
      3 * S 2 = (9 * SP (p-3) - 9 * SP (2*p-4) + 3 * SP (3*p-5)) + (p:ZMod (p^5))^3 * c := by
  have hdvd : ((p:ZMod (p^5))^3) ∣
      (S 2 - (3 * SP (p-3) - 3 * SP (2*p-4) + SP (3*p-5))) := by
    have hS2 : S 2 = ∑ i ∈ Finset.Ico 1 p, ((i:ZMod (p^5))⁻¹)^2 := by
      unfold S; rfl
    have hSP : 3 * SP (p-3) - 3 * SP (2*p-4) + SP (3*p-5)
        = ∑ i ∈ Finset.Ico 1 p, (3*(i:ZMod (p^5))^(p-3) - 3*(i:ZMod (p^5))^(2*p-4)
            + (i:ZMod (p^5))^(3*p-5)) := by
      unfold SP
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hS2, hSP, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro i hi; rw [Finset.mem_Ico] at hi
    obtain ⟨ci, hci⟩ := inv_exp2 hp5 i (by omega) (by omega)
    exact ⟨ci, by rw [hci]; ring⟩
  obtain ⟨R, hR⟩ := hdvd
  refine ⟨3 * R, ?_⟩
  have : S 2 = (3 * SP (p-3) - 3 * SP (2*p-4) + SP (3*p-5)) + (p:ZMod (p^5))^3 * R := by
    linear_combination hR
  rw [this]; ring

/-- Partial power sum `Fp a k = ∑_{i=0}^{k-1} i^a` in `ZMod (p^5)`. -/
noncomputable def Fp (a k : ℕ) : ZMod (p^5) := ∑ i ∈ Finset.range k, (i:ZMod (p^5))^a

/-- Ordered double power sum `Tp a b = ∑_k k^b (∑_{i<k} i^a)`. (For `a ≥ 1` equals `∑_{1≤i<k≤p-1} i^a k^b`.) -/
noncomputable def Tp (a b : ℕ) : ZMod (p^5) := ∑ k ∈ Finset.Ico 1 p, (k:ZMod (p^5))^b * Fp a k

/-- Telescoping: `k^(a+1) = ∑_{l=0}^a C(a+1,l) Fp l k`. -/
lemma pow_eq_sum_Fp (a : ℕ) (k : ℕ) :
    (k:ZMod (p^5))^(a+1) = ∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * Fp l k := by
  induction k with
  | zero => simp [Fp]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    have hFp : ∀ l, Fp l (n+1) = Fp l n + (n:ZMod (p^5))^l := by
      intro l; unfold Fp; rw [Finset.sum_range_succ]
    have hbin : ((n:ZMod (p^5))+1)^(a+1)
        = ∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * (n:ZMod (p^5))^l
          + (n:ZMod (p^5))^(a+1) := by
      rw [add_pow, Finset.sum_range_succ]
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one, one_pow]
      congr 1
      refine Finset.sum_congr rfl (fun l hl => ?_); ring
    calc ((n:ZMod (p^5))+1)^(a+1)
        = (((n:ZMod (p^5))+1)^(a+1) - (n:ZMod (p^5))^(a+1)) + (n:ZMod (p^5))^(a+1) := by ring
      _ = (∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * (n:ZMod (p^5))^l)
            + ∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * Fp l n := by
          linear_combination hbin + ih
      _ = ∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * Fp l (n+1) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_); rw [hFp]; ring

/-- The double-sum recurrence: `SP(a+b+1) = ∑_{l=0}^a C(a+1,l) Tp l b`. -/
lemma Tp_rec (a b : ℕ) :
    SP (a+b+1) = ∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * Tp l b := by
  have key : ∀ k ∈ Finset.Ico 1 p,
      (k:ZMod (p^5))^b * (k:ZMod (p^5))^(a+1)
        = ∑ l ∈ Finset.range (a+1), (Nat.choose (a+1) l : ZMod (p^5)) * ((k:ZMod (p^5))^b * Fp l k) := by
    intro k hk
    rw [pow_eq_sum_Fp a k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_); ring
  have hlhs : ∑ k ∈ Finset.Ico 1 p, (k:ZMod (p^5))^b * (k:ZMod (p^5))^(a+1) = SP (a+b+1) := by
    unfold SP
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← pow_add]; congr 1; omega
  rw [← hlhs, Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Tp, Finset.mul_sum]

/-- Bernoulli numbers realized in `ZMod (p^5)` via the standard recurrence. -/
noncomputable def Bn : ℕ → ZMod (p^5)
  | 0 => 1
  | (m+1) => -(((m+2 : ℕ) : ZMod (p^5))⁻¹) *
      ∑ l : Fin (m+1), (Nat.choose (m+2) (l:ℕ) : ZMod (p^5)) * Bn (l:ℕ)

lemma Bn_zero : (Bn 0 : ZMod (p^5)) = 1 := by rw [Bn]

lemma Bn_succ (m : ℕ) : (Bn (m+1) : ZMod (p^5)) = -(((m+2 : ℕ) : ZMod (p^5))⁻¹) *
      ∑ l ∈ Finset.range (m+1), (Nat.choose (m+2) l : ZMod (p^5)) * Bn l := by
  rw [Bn]; rw [Fin.sum_univ_eq_sum_range (fun l => (Nat.choose (m+2) l : ZMod (p^5)) * Bn l)]

/-- The Bernoulli recurrence: for `n ≥ 1` with `n+1` a unit, `∑_{l=0}^n C(n+1,l) Bn l = 0`. -/
lemma Bn_spec (n : ℕ) (hn : 1 ≤ n) (hu : IsUnit (((n+1 : ℕ)) : ZMod (p^5))) :
    ∑ l ∈ Finset.range (n+1), (Nat.choose (n+1) l : ZMod (p^5)) * (Bn l : ZMod (p^5)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  rw [Finset.sum_range_succ]
  have hc : (Nat.choose (m+1+1) (m+1) : ZMod (p^5)) = ((m+2 : ℕ) : ZMod (p^5)) := by
    rw [Nat.choose_succ_self_right]
  rw [hc, Bn_succ m]
  have hinv : ((m+2 : ℕ) : ZMod (p^5))⁻¹ * ((m+2 : ℕ) : ZMod (p^5)) = 1 :=
    ZMod.inv_mul_of_unit _ hu
  have hsum : ∑ l ∈ Finset.range (m+1), (Nat.choose (m+1+1) l : ZMod (p^5)) * (Bn l : ZMod (p^5))
      = ∑ l ∈ Finset.range (m+1), (Nat.choose (m+2) l : ZMod (p^5)) * (Bn l : ZMod (p^5)) := rfl
  rw [hsum]
  set S := ∑ l ∈ Finset.range (m+1), (Nat.choose (m+2) l : ZMod (p^5)) * (Bn l : ZMod (p^5))
  calc S + ((m+2:ℕ):ZMod (p^5)) * (-(((m+2:ℕ):ZMod (p^5))⁻¹) * S)
      = S - (((m+2:ℕ):ZMod (p^5)) * ((m+2:ℕ):ZMod (p^5))⁻¹) * S := by ring
    _ = S - 1 * S := by rw [mul_comm (((m+2:ℕ):ZMod (p^5))) _, hinv]
    _ = 0 := by ring

/-- Trinomial symmetry: `C(n,j)·C(n-j,i) = C(n,i)·C(n-i,j)` when `i+j ≤ n`. -/
lemma trinom (n i j : ℕ) (h : i + j ≤ n) :
    Nat.choose n j * Nat.choose (n-j) i = Nat.choose n i * Nat.choose (n-i) j := by
  have hjn : j ≤ n := by omega
  have hin : i ≤ n := by omega
  have hi' : i ≤ n - j := by omega
  have hj' : j ≤ n - i := by omega
  have e1 : Nat.choose n j * Nat.choose (n-j) i * (j ! * i ! * (n-i-j)!) = n ! := by
    have h1 : Nat.choose n j * j ! * (n-j)! = n ! := Nat.choose_mul_factorial_mul_factorial hjn
    have h2 : Nat.choose (n-j) i * i ! * (n-j-i)! = (n-j)! := Nat.choose_mul_factorial_mul_factorial hi'
    have he : (n-j-i)! = (n-i-j)! := by congr 1; omega
    calc Nat.choose n j * Nat.choose (n-j) i * (j ! * i ! * (n-i-j)!)
        = (Nat.choose n j * j !) * (Nat.choose (n-j) i * i ! * (n-j-i)!) := by rw [he]; ring
      _ = (Nat.choose n j * j !) * (n-j)! := by rw [h2]
      _ = n ! := by rw [← h1]
  have e2 : Nat.choose n i * Nat.choose (n-i) j * (j ! * i ! * (n-i-j)!) = n ! := by
    have h1 : Nat.choose n i * i ! * (n-i)! = n ! := Nat.choose_mul_factorial_mul_factorial hin
    have h2 : Nat.choose (n-i) j * j ! * (n-i-j)! = (n-i)! := Nat.choose_mul_factorial_mul_factorial hj'
    calc Nat.choose n i * Nat.choose (n-i) j * (j ! * i ! * (n-i-j)!)
        = (Nat.choose n i * i !) * (Nat.choose (n-i) j * j ! * (n-i-j)!) := by ring
      _ = (Nat.choose n i * i !) * (n-i)! := by rw [h2]
      _ = n ! := by rw [← h1]
  have hpos : 0 < j ! * i ! * (n-i-j)! := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [e1, e2])

/-- Binomial difference: `(k+1)^n - k^n = ∑_{i<n} C(n,i) k^i`. -/
lemma add_one_pow_sub (n k : ℕ) :
    ((k:ZMod (p^5))+1)^n - (k:ZMod (p^5))^n
      = ∑ i ∈ Finset.range n, (Nat.choose n i : ZMod (p^5)) * (k:ZMod (p^5))^i := by
  rw [add_pow]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero, one_mul]
    rw [add_sub_cancel_right]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [one_pow, mul_one]; ring

/-- The per-step difference for the Faulhaber closed form. -/
lemma Gstep (a : ℕ) (ha : a < p - 1) (k : ℕ) :
    ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j
        * (((k:ZMod (p^5))+1)^(a+1-j) - (k:ZMod (p^5))^(a+1-j))
      = ((a+1:ℕ):ZMod (p^5)) * (k:ZMod (p^5))^a := by
  have step1 : ∀ j ∈ Finset.range (a+1),
      (Nat.choose (a+1) j : ZMod (p^5)) * Bn j
          * (((k:ZMod (p^5))+1)^(a+1-j) - (k:ZMod (p^5))^(a+1-j))
        = ∑ i ∈ Finset.range (a+1-j),
            (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (Nat.choose (a+1-j) i : ZMod (p^5)) * (k:ZMod (p^5))^i := by
    intro j hj
    rw [add_one_pow_sub, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (s := Finset.range (a+1)) (t := fun j => Finset.range (a+1-j))
      (t' := Finset.range (a+1)) (s' := fun i => Finset.range (a+1-i))
      (by intro x y; simp only [Finset.mem_range]; omega)]
  have step2 : ∀ i ∈ Finset.range (a+1),
      ∑ j ∈ Finset.range (a+1-i),
          (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (Nat.choose (a+1-j) i : ZMod (p^5)) * (k:ZMod (p^5))^i
        = (k:ZMod (p^5))^i * (Nat.choose (a+1) i : ZMod (p^5))
            * ∑ j ∈ Finset.range (a+1-i), (Nat.choose (a+1-i) j : ZMod (p^5)) * Bn j := by
    intro i hi; rw [Finset.mem_range] at hi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have ht : (Nat.choose (a+1) j) * (Nat.choose (a+1-j) i) = (Nat.choose (a+1) i) * (Nat.choose (a+1-i) j) :=
      trinom (a+1) i j (by omega)
    have htc : (Nat.choose (a+1) j : ZMod (p^5)) * (Nat.choose (a+1-j) i : ZMod (p^5))
        = (Nat.choose (a+1) i : ZMod (p^5)) * (Nat.choose (a+1-i) j : ZMod (p^5)) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, ht]
    calc (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (Nat.choose (a+1-j) i : ZMod (p^5)) * (k:ZMod (p^5))^i
        = ((Nat.choose (a+1) j : ZMod (p^5)) * (Nat.choose (a+1-j) i : ZMod (p^5))) * Bn j * (k:ZMod (p^5))^i := by ring
      _ = ((Nat.choose (a+1) i : ZMod (p^5)) * (Nat.choose (a+1-i) j : ZMod (p^5))) * Bn j * (k:ZMod (p^5))^i := by rw [htc]
      _ = (k:ZMod (p^5))^i * (Nat.choose (a+1) i : ZMod (p^5)) * ((Nat.choose (a+1-i) j : ZMod (p^5)) * Bn j) := by ring
  rw [Finset.sum_congr rfl step2]
  have step3 : ∀ i ∈ Finset.range (a+1),
      (k:ZMod (p^5))^i * (Nat.choose (a+1) i : ZMod (p^5))
          * ∑ j ∈ Finset.range (a+1-i), (Nat.choose (a+1-i) j : ZMod (p^5)) * Bn j
        = if i = a then ((a+1:ℕ):ZMod (p^5)) * (k:ZMod (p^5))^a else 0 := by
    intro i hi; rw [Finset.mem_range] at hi
    by_cases hia : i = a
    · rw [if_pos hia]
      have h0 : a + 1 - i = 1 := by omega
      rw [h0]
      simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul, Bn_zero]
      have hcc : (Nat.choose (a+1) i : ZMod (p^5)) = ((a+1:ℕ):ZMod (p^5)) := by
        rw [hia, Nat.choose_succ_self_right]
      rw [hcc, hia]; ring
    · rw [if_neg hia]
      have hge : 1 ≤ a - i := by omega
      have hlt : a - i + 1 < p := by omega
      have hpos : 0 < a - i + 1 := by omega
      have hu : IsUnit (((a-i+1 : ℕ)) : ZMod (p^5)) := by
        have := isUnit_cast (k := 5) (a-i+1) hpos hlt
        simpa using this
      have hbs : ∑ j ∈ Finset.range ((a-i)+1), (Nat.choose ((a-i)+1) j : ZMod (p^5)) * Bn j = 0 :=
        Bn_spec (a-i) hge hu
      have heq : a + 1 - i = (a-i)+1 := by omega
      rw [heq, hbs]; ring
  rw [Finset.sum_congr rfl step3, Finset.sum_ite_eq' (Finset.range (a+1)) a]
  rw [if_pos (Finset.mem_range.mpr (by omega))]

/-- Faulhaber closed form (per `k`): `(a+1)·Fp a k = ∑_j C(a+1,j) Bn_j k^{a+1-j}`. -/
lemma Faul (a : ℕ) (ha : a < p - 1) (k : ℕ) :
    ((a+1:ℕ):ZMod (p^5)) * Fp a k
      = ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (k:ZMod (p^5))^(a+1-j) := by
  induction k with
  | zero =>
    rw [show Fp a 0 = 0 from by simp [Fp], mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j hj; rw [Finset.mem_range] at hj
    rw [Nat.cast_zero, zero_pow (by omega), mul_zero]
  | succ n ih =>
    have hFp : Fp a (n+1) = Fp a n + (n:ZMod (p^5))^a := by
      unfold Fp; rw [Finset.sum_range_succ]
    have hG := Gstep a ha n
    have hcast : ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * ((n+1:ℕ):ZMod (p^5))^(a+1-j)
        = ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (((n:ZMod (p^5))+1))^(a+1-j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_); push_cast; ring
    have hsplit : ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (((n:ZMod (p^5))+1))^(a+1-j)
        = (∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (n:ZMod (p^5))^(a+1-j))
          + ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j
              * (((n:ZMod (p^5))+1)^(a+1-j) - (n:ZMod (p^5))^(a+1-j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
    rw [hcast, hsplit, hG, hFp]
    linear_combination ih

/-- Faulhaber closed form for the ordered double sum (`a < p-1`):
`(a+1)·Tp a b = ∑_j C(a+1,j) Bn_j SP(a+1-j+b)`. -/
lemma Tp_closed (a : ℕ) (ha : a < p - 1) (b : ℕ) :
    ((a+1:ℕ):ZMod (p^5)) * Tp a b
      = ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * SP (a+1-j+b) := by
  unfold Tp
  rw [Finset.mul_sum]
  have hk : ∀ k ∈ Finset.Ico 1 p, ((a+1:ℕ):ZMod (p^5)) * ((k:ZMod (p^5))^b * Fp a k)
      = ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (k:ZMod (p^5))^(a+1-j+b) := by
    intro k _
    rw [show ((a+1:ℕ):ZMod (p^5)) * ((k:ZMod (p^5))^b * Fp a k)
        = (k:ZMod (p^5))^b * (((a+1:ℕ):ZMod (p^5)) * Fp a k) from by ring, Faul a ha k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show a+1-j+b = (a+1-j)+b from rfl, pow_add]; ring
  rw [Finset.sum_congr rfl hk, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SP, Finset.mul_sum]


/-- The Bernoulli pole residue constant `ρ = ∑_{j<p} C(p,j) Bn_j`. -/
noncomputable def rho : ZMod (p^5) := ∑ j ∈ Finset.range p, (Nat.choose p j : ZMod (p^5)) * Bn j

/-- A natural number not divisible by `p` casts to a unit in `ZMod (p^5)`. -/
lemma isUnit_of_not_dvd (m : ℕ) (hm : ¬ (p ∣ m)) : IsUnit ((m : ℕ) : ZMod (p^5)) := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (p^5) := ⟨pow_ne_zero 5 hp.pos.ne'⟩
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff (by norm_num)]
  exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hm)

/-- Pole-extended per-step difference: for `p-1 ≤ a ≤ 2p-2`. -/
lemma Gstep_pole (a : ℕ) (hlo : p ≤ a + 1) (hhi : a + 1 ≤ 2*p - 1) (k : ℕ) :
    ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j
        * (((k:ZMod (p^5))+1)^(a+1-j) - (k:ZMod (p^5))^(a+1-j))
      = ((a+1:ℕ):ZMod (p^5)) * (k:ZMod (p^5))^a
        + (Nat.choose (a+1) (a+1-p) : ZMod (p^5)) * rho * (k:ZMod (p^5))^(a+1-p) := by
  have hp := (Fact.out : p.Prime)
  have hp2 : 2 ≤ p := hp.two_le
  have step1 : ∀ j ∈ Finset.range (a+1),
      (Nat.choose (a+1) j : ZMod (p^5)) * Bn j
          * (((k:ZMod (p^5))+1)^(a+1-j) - (k:ZMod (p^5))^(a+1-j))
        = ∑ i ∈ Finset.range (a+1-j),
            (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (Nat.choose (a+1-j) i : ZMod (p^5)) * (k:ZMod (p^5))^i := by
    intro j hj
    rw [add_one_pow_sub, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (s := Finset.range (a+1)) (t := fun j => Finset.range (a+1-j))
      (t' := Finset.range (a+1)) (s' := fun i => Finset.range (a+1-i))
      (by intro x y; simp only [Finset.mem_range]; omega)]
  have step2 : ∀ i ∈ Finset.range (a+1),
      ∑ j ∈ Finset.range (a+1-i),
          (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (Nat.choose (a+1-j) i : ZMod (p^5)) * (k:ZMod (p^5))^i
        = (k:ZMod (p^5))^i * (Nat.choose (a+1) i : ZMod (p^5))
            * ∑ j ∈ Finset.range (a+1-i), (Nat.choose (a+1-i) j : ZMod (p^5)) * Bn j := by
    intro i hi; rw [Finset.mem_range] at hi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have ht : (Nat.choose (a+1) j) * (Nat.choose (a+1-j) i) = (Nat.choose (a+1) i) * (Nat.choose (a+1-i) j) :=
      trinom (a+1) i j (by omega)
    have htc : (Nat.choose (a+1) j : ZMod (p^5)) * (Nat.choose (a+1-j) i : ZMod (p^5))
        = (Nat.choose (a+1) i : ZMod (p^5)) * (Nat.choose (a+1-i) j : ZMod (p^5)) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, ht]
    calc (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (Nat.choose (a+1-j) i : ZMod (p^5)) * (k:ZMod (p^5))^i
        = ((Nat.choose (a+1) j : ZMod (p^5)) * (Nat.choose (a+1-j) i : ZMod (p^5))) * Bn j * (k:ZMod (p^5))^i := by ring
      _ = ((Nat.choose (a+1) i : ZMod (p^5)) * (Nat.choose (a+1-i) j : ZMod (p^5))) * Bn j * (k:ZMod (p^5))^i := by rw [htc]
      _ = (k:ZMod (p^5))^i * (Nat.choose (a+1) i : ZMod (p^5)) * ((Nat.choose (a+1-i) j : ZMod (p^5)) * Bn j) := by ring
  rw [Finset.sum_congr rfl step2]
  have step3 : ∀ i ∈ Finset.range (a+1),
      (k:ZMod (p^5))^i * (Nat.choose (a+1) i : ZMod (p^5))
          * ∑ j ∈ Finset.range (a+1-i), (Nat.choose (a+1-i) j : ZMod (p^5)) * Bn j
        = (if i = a then ((a+1:ℕ):ZMod (p^5)) * (k:ZMod (p^5))^a else 0)
          + (if i = a+1-p then (Nat.choose (a+1) (a+1-p) : ZMod (p^5)) * rho * (k:ZMod (p^5))^(a+1-p) else 0) := by
    intro i hi; rw [Finset.mem_range] at hi
    by_cases hia : i = a
    · rw [if_pos hia, if_neg (by omega : ¬ i = a+1-p)]
      have h0 : a + 1 - i = 1 := by omega
      rw [h0]
      simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul, Bn_zero]
      have hcc : (Nat.choose (a+1) i : ZMod (p^5)) = ((a+1:ℕ):ZMod (p^5)) := by
        rw [hia, Nat.choose_succ_self_right]
      rw [hcc, hia]; ring
    · by_cases hip : i = a+1-p
      · rw [if_neg hia, if_pos hip]
        have hpp : a + 1 - i = p := by omega
        rw [hpp]
        have hrho : ∑ j ∈ Finset.range p, (Nat.choose p j : ZMod (p^5)) * Bn j = rho := rfl
        rw [hrho, hip]; ring
      · rw [if_neg hia, if_neg hip]
        have hnd : ¬ p ∣ (a+1-i) := by
          rintro ⟨c, hc⟩
          have hb1 : 2 ≤ a+1-i := by omega
          have hb2 : a+1-i ≤ 2*p-1 := by omega
          rcases Nat.lt_or_ge c 1 with h|h
          · have : c = 0 := by omega
            rw [this, mul_zero] at hc; omega
          rcases Nat.lt_or_ge c 2 with h2|h2
          · have : c = 1 := by omega
            rw [this, mul_one] at hc; omega
          · have hge : 2*p ≤ p*c := by
              calc 2*p = p*2 := by ring
                _ ≤ p*c := Nat.mul_le_mul_left p h2
            omega
        have hu : IsUnit (((a-i+1 : ℕ)) : ZMod (p^5)) := by
          rw [show a-i+1 = a+1-i from by omega]; exact isUnit_of_not_dvd (a+1-i) hnd
        have hge : 1 ≤ a - i := by omega
        have hbs : ∑ j ∈ Finset.range ((a-i)+1), (Nat.choose ((a-i)+1) j : ZMod (p^5)) * Bn j = 0 :=
          Bn_spec (a-i) hge hu
        have heq : a + 1 - i = (a-i)+1 := by omega
        rw [heq, hbs]; ring
  rw [Finset.sum_congr rfl step3, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' (Finset.range (a+1)) a, Finset.sum_ite_eq' (Finset.range (a+1)) (a+1-p)]
  rw [if_pos (Finset.mem_range.mpr (by omega)), if_pos (Finset.mem_range.mpr (by omega))]

/-- Pole-extended Faulhaber (per `k`) for `p-1 ≤ a ≤ 2p-2`. -/
lemma Faul_pole (a : ℕ) (hlo : p ≤ a + 1) (hhi : a + 1 ≤ 2*p - 1) (k : ℕ) :
    ((a+1:ℕ):ZMod (p^5)) * Fp a k
      = (∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (k:ZMod (p^5))^(a+1-j))
        - (Nat.choose (a+1) (a+1-p) : ZMod (p^5)) * rho * Fp (a+1-p) k := by
  induction k with
  | zero =>
    rw [show Fp a 0 = 0 from by simp [Fp], show Fp (a+1-p) 0 = 0 from by simp [Fp], mul_zero, mul_zero, sub_zero]
    symm
    apply Finset.sum_eq_zero
    intro j hj; rw [Finset.mem_range] at hj
    rw [Nat.cast_zero, zero_pow (by omega), mul_zero]
  | succ n ih =>
    have hFp : Fp a (n+1) = Fp a n + (n:ZMod (p^5))^a := by
      unfold Fp; rw [Finset.sum_range_succ]
    have hFp2 : Fp (a+1-p) (n+1) = Fp (a+1-p) n + (n:ZMod (p^5))^(a+1-p) := by
      unfold Fp; rw [Finset.sum_range_succ]
    have hG := Gstep_pole a hlo hhi n
    have hcast : ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * ((n+1:ℕ):ZMod (p^5))^(a+1-j)
        = ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (((n:ZMod (p^5))+1))^(a+1-j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_); push_cast; ring
    have hsplit : ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (((n:ZMod (p^5))+1))^(a+1-j)
        = (∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (n:ZMod (p^5))^(a+1-j))
          + ∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j
              * (((n:ZMod (p^5))+1)^(a+1-j) - (n:ZMod (p^5))^(a+1-j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
    rw [hcast, hsplit, hG, hFp, hFp2]
    linear_combination ih

/-- Pole-extended closed form for the ordered double sum, `p-1 ≤ a ≤ 2p-2`. -/
lemma Tp_pole (a : ℕ) (hlo : p ≤ a + 1) (hhi : a + 1 ≤ 2*p - 1) (b : ℕ) :
    ((a+1:ℕ):ZMod (p^5)) * Tp a b
      = (∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * SP (a+1-j+b))
        - (Nat.choose (a+1) (a+1-p) : ZMod (p^5)) * rho * Tp (a+1-p) b := by
  unfold Tp
  rw [Finset.mul_sum]
  have hk : ∀ k ∈ Finset.Ico 1 p, ((a+1:ℕ):ZMod (p^5)) * ((k:ZMod (p^5))^b * Fp a k)
      = (∑ j ∈ Finset.range (a+1), (Nat.choose (a+1) j : ZMod (p^5)) * Bn j * (k:ZMod (p^5))^(a+1-j+b))
        - (Nat.choose (a+1) (a+1-p) : ZMod (p^5)) * rho * ((k:ZMod (p^5))^b * Fp (a+1-p) k) := by
    intro k _
    rw [show ((a+1:ℕ):ZMod (p^5)) * ((k:ZMod (p^5))^b * Fp a k)
        = (k:ZMod (p^5))^b * (((a+1:ℕ):ZMod (p^5)) * Fp a k) from by ring, Faul_pole a hlo hhi k,
        mul_sub, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show a+1-j+b = (a+1-j)+b from rfl, pow_add]; ring
    · ring
  rw [Finset.sum_congr rfl hk, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [SP, Finset.mul_sum]
  · rw [← Finset.mul_sum]
