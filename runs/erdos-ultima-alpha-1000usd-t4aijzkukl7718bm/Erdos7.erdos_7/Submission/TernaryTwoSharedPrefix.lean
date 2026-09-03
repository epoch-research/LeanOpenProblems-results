import FormalConjecturesUtil

/-!
# Shared-prefixCount comparison on the five-cell ternary root

The same first slice occurs in every cumulative prefixCount. Retaining it improves
the root comparison for ternary exponent at most two. These finite comparison
lemmas are not an arithmetic noncoverage theorem or a settlement of Erdos7.
-/
namespace Erdos7TernaryTwoSharedPrefix
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

def count : Fin 10 → Fin 5 → ℕ :=
  ![![3,2,1,1,1], ![2,3,1,1,1], ![2,2,2,1,1], ![2,2,1,2,1], ![2,2,1,1,2],
    ![2,1,2,2,2], ![1,2,2,2,2], ![1,1,3,2,2], ![1,1,2,3,2], ![1,1,2,2,3]]
def weightNum (c : Fin 10) (x : Fin 5) : ℕ := 16-5*count c x
def lowNum (c : Fin 10) : Fin 3 → ℕ := if c.val<5 then ![7,22,11] else ![13,15,7]
def meanNum (a : Fin 10) : ℕ := ∑ x,count a x
def firstNum (c a : Fin 10) (t : ℕ) : ℕ := ∑ x,weightNum c x*(count a x-t)
def baseNum (c : Fin 10) (t : ℕ) : ℕ := ∑ n,lowNum c n*(n.val+1-t)
def starNum (d t : ℕ) : ℕ := 2*(d-t)+2*(2*d-t)+(3*d-t)
def prefixCount (a : ℕ → Fin 10) (d : ℕ) (x : Fin 5) : ℕ := ∑ j ∈ Finset.range d,count (a j) x
noncomputable def mean (a : Fin 10) : ℝ := (meanNum a : ℝ)/5
noncomputable def first (c a : Fin 10) (t : ℕ) : ℝ := (firstNum c a t : ℝ)/100
noncomputable def base (c : Fin 10) (t : ℕ) : ℝ := (baseNum c t : ℝ)/100
noncomputable def star (d t : ℕ) : ℝ := (starNum d t : ℝ)/5
noncomputable def prefixHinge (a : ℕ → Fin 10) (d t : ℕ) : ℝ :=
  (∑ x,((prefixCount a d x-t : ℕ) : ℝ))/5

lemma data :
    (∀ a x, 1 ≤ count a x ∧ count a x ≤ 3) ∧
    (∀ a, meanNum a ≤ 9) ∧
    (∀ c a (t : Fin 3), firstNum c a t.val+4*meanNum a ≤ baseNum c t.val+36) ∧
    (∀ c, (∑ x,weightNum c x) = ∑ n,lowNum c n) := by
  decide +kernel

lemma uniform_hinge (a : Fin 10) (d t : ℕ) :
    (∑ x,(count a x*d-t)) ≤ starNum d t := by
  fin_cases a <;> simp [count,starNum,Fin.sum_univ_succ] <;> omega

lemma sum_hinge_jensen (U : ℕ → ℕ) (d t : ℕ) :
    d*((∑ j ∈ Finset.range d,U j)-t) ≤
      ∑ j ∈ Finset.range d,(d*U j-t) := by
  have hh : d*(∑ j ∈ Finset.range d,U j) ≤
      (∑ j ∈ Finset.range d,(d*U j-t))+d*t := by
    calc
      _ = ∑ j ∈ Finset.range d,d*U j := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.range d,((d*U j-t)+t) :=
        Finset.sum_le_sum (fun j _ => by omega)
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [Nat.mul_sub_left_distrib]
  omega

lemma prefix_hinge_nat (a : ℕ → Fin 10) (d t : ℕ) (hd : 0<d) :
    (∑ x,(prefixCount a d x-t)) ≤ starNum d t := by
  have hh : d*(∑ x,(prefixCount a d x-t)) ≤ d*starNum d t := by
    calc
      _ = ∑ x,d*(prefixCount a d x-t) := Finset.mul_sum _ _ _
      _ ≤ ∑ x,∑ j ∈ Finset.range d,(d*count (a j) x-t) :=
        Finset.sum_le_sum (fun x _ => sum_hinge_jensen (fun j => count (a j) x) d t)
      _ = ∑ j ∈ Finset.range d,∑ x,(d*count (a j) x-t) := Finset.sum_comm
      _ ≤ ∑ j ∈ Finset.range d,starNum d t := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Nat.mul_comm] using uniform_hinge (a j) d t
      _ = _ := by simp
  exact Nat.le_of_mul_le_mul_left hh hd

lemma prefix_hinge_le (a : ℕ → Fin 10) (d t : ℕ) (hd : 0<d) :
    prefixHinge a d t ≤ star d t := by
  unfold prefixHinge star
  rw [← Nat.cast_sum]
  exact div_le_div_of_nonneg_right (by exact_mod_cast prefix_hinge_nat a d t hd) (by norm_num)

lemma prefix_lower (a : ℕ → Fin 10) (d : ℕ) (x : Fin 5) : d ≤ prefixCount a d x := by
  calc
    d = ∑ _j ∈ Finset.range d,1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ => (data.1 (a j) x).1)

lemma prefix_mean_num (a : ℕ → Fin 10) (d : ℕ) (hd : 0<d) :
    (∑ x,prefixCount a d x) ≤ meanNum (a 0)+9*(d-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  unfold prefixCount
  rw [Finset.sum_comm]
  change (∑ j ∈ Finset.range n.succ,meanNum (a j)) ≤ meanNum (a 0)+9*(n.succ-1)
  rw [Finset.sum_range_succ']
  have hh : (∑ j ∈ Finset.range n, meanNum (a (j+1))) ≤ n*9 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range n,9 := Finset.sum_le_sum (fun j _ => data.2.1 _)
      _ = _ := by simp
  omega

lemma star_low (d t : ℕ) (hd : 2≤d) (ht : t≤2) :
    star d t = 9/5*(d : ℝ)-(t : ℝ) := by
  unfold star starNum
  rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,
    Nat.cast_sub (by omega : t≤d),Nat.cast_sub (by omega : t≤2*d),
    Nat.cast_sub (by omega : t≤3*d)]
  push_cast
  ring

lemma prefix_low (a : ℕ → Fin 10) (d t : ℕ) (hd : 2≤d) (ht : t≤2) :
    prefixHinge a d t ≤ mean (a 0)-9/5+star d t := by
  have hsub (x : Fin 5) : t ≤ prefixCount a d x := ht.trans (hd.trans (prefix_lower a d x))
  have hmean : ((∑ x,prefixCount a d x : ℕ) : ℝ) ≤
      (meanNum (a 0) : ℝ)+9*((d : ℝ)-1) := by
    have hh := prefix_mean_num a d (by omega)
    have hh' : ((∑ x,prefixCount a d x : ℕ) : ℝ) ≤
        (meanNum (a 0)+9*(d-1) : ℕ) := by exact_mod_cast hh
    push_cast at hh'
    rw [Nat.cast_sub (by omega : 1≤d)] at hh'
    norm_num at hh'
    simpa only [Nat.cast_sum] using hh'
  unfold prefixHinge
  simp_rw [Nat.cast_sub (hsub _)]
  rw [Finset.sum_sub_distrib,← Nat.cast_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [star_low d t hd ht]
  unfold mean
  linarith

lemma low_table (c a : Fin 10) (t : ℕ) (ht : t≤2) :
    first c a t+(1/5 : ℝ)*mean a ≤ base c t+9/25 := by
  have hh := data.2.2.1 c a ⟨t,by omega⟩
  have h : (firstNum c a t : ℝ)+4*(meanNum a : ℝ) ≤ (baseNum c t : ℝ)+36 := by
    exact_mod_cast hh
  unfold first mean base
  linarith

lemma high_zero (c a : Fin 10) (t : ℕ) (ht : 3≤t) :
    first c a t=0 ∧ base c t=0 := by
  have hfirst : firstNum c a t=0 := by
    unfold firstNum
    apply Finset.sum_eq_zero
    intro x _
    rw [Nat.sub_eq_zero_of_le ((data.1 a x).2.trans ht),Nat.mul_zero]
  have hbase : baseNum c t=0 := by
    unfold baseNum
    apply Finset.sum_eq_zero
    intro n _
    rw [Nat.sub_eq_zero_of_le (by omega : n.val+1≤t),Nat.mul_zero]
  simp [first,base,hfirst,hbase]

/-- Exact shared-first-slice comparison. The prefixCount lengths and their weights
are arbitrary, subject only to lengths>=2, nonnegative weights and mass1/5.
In particular no infinite geometric tail is omitted. -/
theorem shared_prefix_hinge {J : Type*} [Fintype J]
    (c : Fin 10) (a : ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ)
    (hr : ∀ j,0≤r j) (hd : ∀ j,2≤d j) (hmass : (∑ j,r j)=1/5)
    (t : ℕ) :
    first c (a 0) t+(∑ j,r j*prefixHinge a (d j) t) ≤
      base c t+(∑ j,r j*star (d j) t) := by
  by_cases ht : t≤2
  · have hh := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset J)) =>
      mul_le_mul_of_nonneg_left (prefix_low a (d j) t (hd j) ht) (hr j))
    have he : (∑ j,r j*(mean (a 0)-9/5+star (d j) t)) =
        (1/5)*(mean (a 0)-9/5)+(∑ j,r j*star (d j) t) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,hmass]
    rw [he] at hh
    have hlo := low_table c (a 0) t ht
    linarith
  · obtain ⟨hf,hb⟩ := high_zero c (a 0) t (by omega)
    rw [hf,hb,zero_add,zero_add]
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (prefix_hinge_le a (d j) t (by have := hd j; omega)) (hr j))

#print axioms data
#print axioms uniform_hinge
#print axioms shared_prefix_hinge
end Erdos7TernaryTwoSharedPrefix
