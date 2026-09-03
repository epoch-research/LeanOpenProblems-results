import FormalConjecturesUtil
import Submission.BinaryReversalHeight
import Submission.AffinePrimeOccurrenceExcess
import Submission.ResidueSieve

/-! Dyadic separation properties of the bounded digit-reversal model.
This is not a theorem about largest prime factors. -/

namespace Erdos371BinaryReversalSeparation

open Finset Filter Erdos371BinaryReversalHeight Erdos371CoreGraphReversal
open scoped Topology

lemma rev_injective : Function.Injective rev := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m he
    by_cases hn : n=0
    · subst n
      by_contra hm
      have hh := rev_pos (Nat.pos_of_ne_zero (Ne.symm hm))
      simp only [rev_zero] at he
      linarith
    obtain ⟨a, ha | ha⟩ := n.even_or_odd'
    · subst n
      have han : a<2*a := by omega
      obtain ⟨b, hb | hb⟩ := m.even_or_odd'
      · subst m
        rw [rev_even,rev_even] at he
        have hab := ih a han (show rev a=rev b by linarith)
        omega
      · subst m
        rw [rev_even,rev_odd] at he
        linarith [(rev_bounds a).2,(rev_bounds b).1]
    · subst n
      obtain ⟨b, hb | hb⟩ := m.even_or_odd'
      · subst m
        rw [rev_odd,rev_even] at he
        linarith [(rev_bounds a).1,(rev_bounds b).2]
      · subst m
        rw [rev_odd,rev_odd] at he
        have hab := ih a (by omega) (show rev a=rev b by linarith)
        omega

lemma rev_block (k n r : ℕ) (hr : r<2^k) :
    rev (2^k*n+r)=rev r+rev n/(2:ℚ)^k := by
  induction k generalizing n r with
  | zero =>
    have he : r=0 := by simpa using hr
    subst r
    simp
  | succ k ih =>
    rw [pow_succ'] at hr ⊢
    obtain ⟨s, hs | hs⟩ := r.even_or_odd'
    · subst r
      have hs : s<2^k := by omega
      rw [show 2*2^k*n+2*s=2*(2^k*n+s) by ring,rev_even,rev_even,ih n s hs]
      ring
    · subst r
      have hs : s<2^k := by omega
      rw [show 2*2^k*n+(2*s+1)=2*(2^k*n+s)+1 by ring,rev_odd,rev_odd,ih n s hs]
      ring

lemma rev_split (k n : ℕ) :
    rev n=rev (n%2^k)+rev (n/2^k)/(2:ℚ)^k := by
  have hh := rev_block k (n/2^k) (n%2^k) (Nat.mod_lt _ (by positivity))
  simpa only [Nat.div_add_mod] using hh

lemma rev_grid {k r : ℕ} (hr : r<2^k) :
    ∃ a : ℕ, rev r=(a:ℚ)/(2:ℚ)^k := by
  induction k generalizing r with
  | zero =>
    have he : r=0 := by simpa using hr
    subst r
    exact ⟨0,by simp⟩
  | succ k ih =>
    rw [pow_succ'] at hr ⊢
    obtain ⟨s, hs | hs⟩ := r.even_or_odd'
    · subst r
      obtain ⟨a,ha⟩ := ih (show s<2^k by omega)
      refine ⟨a,?_⟩
      rw [rev_even,ha]
      ring
    · subst r
      obtain ⟨a,ha⟩ := ih (show s<2^k by omega)
      refine ⟨2^k+a,?_⟩
      rw [rev_odd,ha]
      push_cast
      have hp : (2:ℚ)^k ≠ 0 := by positivity
      field_simp

lemma rev_grid_separation {k r s : ℕ} (hr : r<2^k) (hs : s<2^k)
    (hne : r≠s) : 1/(2:ℚ)^k ≤ |rev r-rev s| := by
  obtain ⟨a,ha⟩ := rev_grid hr
  obtain ⟨b,hb⟩ := rev_grid hs
  have hab : a≠b := by
    intro he
    apply hne
    apply rev_injective
    rw [ha,hb,he]
  have hh : (1:ℚ) ≤ |(a:ℚ)-b| := by
    rcases lt_or_gt_of_ne hab with h | h
    · have hab' : (a:ℚ)+1≤b := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hab' : (b:ℚ)+1≤a := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [ha,hb,← sub_div,abs_div,abs_of_pos (by positivity : (0:ℚ)<2^k)]
  exact div_le_div_of_nonneg_right hh (by positivity)

lemma rev_small_mod {k n : ℕ} (h : rev n<1/(2:ℚ)^k) : n%2^k=0 := by
  by_contra hn
  have hh := rev_grid_separation (Nat.mod_lt n (by positivity : 0<2^k))
    (show 0<2^k by positivity) hn
  rw [rev_zero,sub_zero,abs_of_nonneg (rev_bounds _).1] at hh
  have hd := rev_split k n
  have ht : 0≤rev (n/2^k)/(2:ℚ)^k := div_nonneg (rev_bounds _).1 (by positivity)
  linarith

/-- A small gap either preserves the first `k` reversed digits, or forces
one endpoint to have a block of `k` zero digits immediately after them. -/
lemma close_reversals_cover (k u v : ℕ)
    (h : |rev u-rev v| ≤ 1/(2:ℚ)^(2*k+1)) :
    u%2^k=v%2^k ∨ (u/2^k)%2^k=0 ∨ (v/2^k)%2^k=0 := by
  by_cases he : u%2^k=v%2^k
  · exact Or.inl he
  right
  have hs := rev_grid_separation (Nat.mod_lt u (by positivity : 0<2^k))
    (Nat.mod_lt v (by positivity : 0<2^k)) he
  have hu := rev_split k u
  have hv := rev_split k v
  have hp : (0:ℚ)<2^k := by positivity
  have heps : (1/(2:ℚ)^(2*k+1))*(2:ℚ)^k < 1/(2:ℚ)^k := by
    have he : (2:ℚ)^(2*k+1)=2*((2:ℚ)^k)^2 := by
      rw [show 2*k+1=k+k+1 by omega,pow_add,pow_add]
      norm_num
      ring
    rw [he]
    field_simp
    nlinarith [sq_pos_of_pos hp]
  obtain ⟨hl,hh⟩ := abs_le.mp h
  by_cases horder : rev (u%2^k)≤rev (v%2^k)
  · right
    apply rev_small_mod
    rw [abs_of_nonpos (by linarith)] at hs
    have ht := (rev_bounds (u/2^k)).2
    have hdiff : rev (v/2^k) < (1/(2:ℚ)^(2*k+1))*(2:ℚ)^k := by
      have hmul := mul_le_mul_of_nonneg_right hl hp.le
      have hgrid := (div_le_iff₀ hp).mp hs
      have heu : rev (u/2^k)/(2:ℚ)^k*(2:ℚ)^k=rev (u/2^k) := div_mul_cancel₀ _ hp.ne'
      have hev : rev (v/2^k)/(2:ℚ)^k*(2:ℚ)^k=rev (v/2^k) := div_mul_cancel₀ _ hp.ne'
      nlinarith
    exact hdiff.trans heps
  · left
    apply rev_small_mod
    rw [abs_of_nonneg (by linarith)] at hs
    have ht := (rev_bounds (v/2^k)).2
    have hdiff : rev (u/2^k) < (1/(2:ℚ)^(2*k+1))*(2:ℚ)^k := by
      have hmul := mul_le_mul_of_nonneg_right hh hp.le
      have hgrid := (div_le_iff₀ hp).mp hs
      have heu : rev (u/2^k)/(2:ℚ)^k*(2:ℚ)^k=rev (u/2^k) := div_mul_cancel₀ _ hp.ne'
      have hev : rev (v/2^k)/(2:ℚ)^k*(2:ℚ)^k=rev (v/2^k) := div_mul_cancel₀ _ hp.ne'
      nlinarith
    exact hdiff.trans heps


attribute [local instance] Classical.propDecidable

noncomputable def count (p : ℕ → Prop) (N : ℕ) : ℝ :=
  ((range N).filter p).card

attribute [local instance] Classical.propDecidable

lemma count_eq (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    count p N=(((range N).filter p).card:ℝ) := by
  unfold count
  apply congrArg (fun s : Finset ℕ => (s.card:ℝ))
  ext n
  simp only [mem_filter]

lemma count_nonneg (p : ℕ → Prop) (N : ℕ) : 0≤count p N := Nat.cast_nonneg _

lemma count_mono {p q : ℕ → Prop} (hpq : ∀ n, p n → q n) (N : ℕ) :
    count p N≤count q N := by
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hnN,hnp⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hnN,hpq n hnp⟩

lemma count_or_le (p q : ℕ → Prop) (N : ℕ) :
    count (fun n => p n ∨ q n) N≤count p N+count q N := by
  simp only [count_eq]
  rw [filter_or]
  exact_mod_cast card_union_le _ _

lemma count_exists_le (s : Finset ℕ) (p : ℕ → ℕ → Prop) (N : ℕ) :
    count (fun n => ∃ v∈s, p v n) N≤∑ v∈s, count (p v) N := by
  have he : (range N).filter (fun n => ∃ v∈s, p v n) =
      s.biUnion (fun v => (range N).filter (p v)) := by
    ext n
    simp only [mem_filter,mem_biUnion]
    aesop
  simp only [count_eq]
  rw [he]
  exact_mod_cast card_biUnion_le

lemma count_shift_le (p : ℕ → Prop) (N : ℕ) :
    count (fun n => p (n+1)) N≤count p (N+1) := by
  simp only [count_eq]
  apply Nat.cast_le.mpr
  apply card_le_card_of_injOn (fun n : ℕ => n+1)
  · intro n hn
    change n∈(range N).filter (fun n => p (n+1)) at hn
    obtain ⟨hnN,hp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hnN; omega),hp⟩
  · intro n _ m _ he
    change n+1=m+1 at he
    omega

lemma periodic_count_upper {p : ℕ → Prop} {Q : ℕ} (hQ : 0<Q)
    (hp : ∀ n, p (n+Q) ↔ p n) {C : ℝ}
    (hC : count p Q≤C) (N : ℕ) : count p N≤(N:ℝ)/Q*C+C := by
  have hh := (abs_le.mp (Erdos371ResidueSieve.periodic_count_error p hQ hp N)).2
  change count p N-(N:ℝ)/Q*count p Q≤count p Q at hh
  have hm := mul_le_mul_of_nonneg_left hC (by positivity : (0:ℝ)≤(N:ℝ)/Q)
  linarith

lemma divide_count_le {d : ℕ} (hd : 0<d) (p : ℕ → Prop) (N : ℕ) :
    count (fun n => d∣n ∧ p (n/d)) N≤count p (N/d+1) := by
  simp only [count_eq]
  apply Nat.cast_le.mpr
  apply card_le_card_of_injOn (fun n : ℕ => n/d)
  · intro n hn
    change n∈(range N).filter (fun n => d∣n ∧ p (n/d)) at hn
    obtain ⟨hnN,_,hp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (mem_range.mp hnN).le)),hp⟩
  · intro n hn m hm he
    change n∈(range N).filter (fun n => d∣n ∧ p (n/d)) at hn
    change m∈(range N).filter (fun n => d∣n ∧ p (n/d)) at hm
    have hn' := Nat.div_mul_cancel (mem_filter.mp hn).2.1
    have hm' := Nat.div_mul_cancel (mem_filter.mp hm).2.1
    change n/d=m/d at he
    rw [he] at hn'
    omega

lemma lift_periodic_count {d Q : ℕ} (hd : 0<d) (hQ : 0<Q)
    (p : ℕ → Prop) (hp : ∀ n, p (n+Q) ↔ p n) {C : ℝ}
    (hC0 : 0≤C) (hC : count p Q≤C) (N : ℕ) :
    count (fun n => d∣n ∧ p (n/d)) N≤(N:ℝ)*C/((d:ℝ)*Q)+C/Q+C := by
  have hh := (divide_count_le hd p N).trans (periodic_count_upper hQ hp hC _)
  have hf : ((N/d:ℕ):ℝ)≤(N:ℝ)/d := Nat.cast_div_le
  have hm := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (add_le_add_right hf 1) (Nat.cast_nonneg Q)) hC0
  have he : (((N:ℝ)/d+1)/Q)*C+C=(N:ℝ)*C/((d:ℝ)*Q)+C/Q+C := by ring
  push_cast at hh
  calc
    _ ≤ _ := hh
    _ ≤ (((N:ℝ)/d+1)/Q)*C+C := by
      convert add_le_add_right hm C using 1 <;> ring
    _ = _ := he

lemma affine_lift_count {d q c : ℕ} (hd : 0<d) (hq : 0<q)
    (hc : c.Coprime q) (b N : ℕ) :
    count (fun n => d∣n ∧ q∣c*(n/d)+b) N≤(N:ℝ)/((d:ℝ)*q)+2 := by
  have hp (n : ℕ) : (q∣c*(n+q)+b) ↔ q∣c*n+b := by
    simp [Nat.dvd_iff_mod_eq_zero,Nat.mul_add,Nat.add_mod]
  have hroot : count (fun n => q∣c*n+b) q≤1 := by
    simp only [count_eq]
    rw [Erdos371AffinePrimeOccurrenceExcess.progression_one_root hq hc b]
    norm_num
  have hh := lift_periodic_count hd hq (fun n => q∣c*n+b) hp (by norm_num) hroot N
  have hqr : (1:ℝ)≤q := by exact_mod_cast hq
  have hrec : (1:ℝ)/q≤1 := (div_le_one (by positivity)).mpr hqr
  simp only [mul_one] at hh
  linarith

lemma block_lift_count {d q : ℕ} (hd : 0<d) (hq : 0<q) (N : ℕ) :
    count (fun n => d∣n ∧ (n/d)%(q*q)<q) N≤(N:ℝ)/((d:ℝ)*q)+q+1 := by
  have hqq : q≤q*q := by nlinarith
  have hp (n : ℕ) : ((n+q*q)%(q*q)<q) ↔ (n%(q*q)<q) := by simp
  have hroot : count (fun n => n%(q*q)<q) (q*q)≤(q:ℝ) := by
    have he : (range (q*q)).filter (fun n => n%(q*q)<q)=range q := by
      ext n
      simp only [mem_filter,mem_range]
      constructor
      · rintro ⟨hn,hh⟩
        simpa only [Nat.mod_eq_of_lt hn] using hh
      · intro hn
        have hh := hn.trans_le hqq
        exact ⟨hh,by simpa only [Nat.mod_eq_of_lt hh] using hn⟩
    rw [count_eq,he,card_range]
  have hh := lift_periodic_count hd (by positivity : 0<q*q)
    (fun n => n%(q*q)<q) hp (Nat.cast_nonneg q) hroot N
  have hd' : (d:ℝ)≠0 := Nat.cast_ne_zero.mpr hd.ne'
  have hq' : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr hq.ne'
  have he : (N:ℝ)*q/((d:ℝ)*(q*q:ℕ))+(q:ℝ)/(q*q:ℕ)+q=
      (N:ℝ)/((d:ℝ)*q)+1/(q:ℝ)+q := by push_cast; field_simp
  rw [he] at hh
  have hqr : (1:ℝ)≤q := by exact_mod_cast hq
  have hrec : (1:ℝ)/q≤1 := (div_le_one (by positivity)).mpr hqr
  linarith

lemma multiples_count_le {q : ℕ} (hq : 0<q) (N : ℕ) :
    count (fun n => q∣n) N≤(N:ℝ)/q+1 := by
  have hp (n : ℕ) : (q∣n+q) ↔ q∣n := by simp
  have hc : count (fun n => q∣n) q≤1 := by
    rw [count_eq]
    have hh := Erdos371AffinePrimeOccurrenceExcess.progression_one_root hq
      (Nat.coprime_one_left q) 0
    simp only [Nat.one_mul,Nat.add_zero] at hh
    rw [hh]
    norm_num
  simpa using periodic_count_upper hq hp hc N

lemma reciprocal_two_sum (k : ℕ) : (∑ v∈range k,1/(2:ℝ)^v)≤2 := by
  have he : (∑ v∈range k,1/(2:ℝ)^v)=2-2/(2:ℝ)^k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [sum_range_succ,ih,pow_succ]
      ring
  rw [he]
  have hh : (0:ℝ)≤2/(2:ℝ)^k := by positivity
  linarith

lemma reciprocal_two_sum_shift (k : ℕ) : (∑ v∈range k,1/(2:ℝ)^(v+1))≤1 := by
  have he : (∑ v∈range k,1/(2:ℝ)^(v+1))=
      (∑ v∈range k,1/(2:ℝ)^v)/2 := by
    rw [sum_div]
    apply sum_congr rfl
    intro v _
    rw [pow_succ]
    ring
  rw [he]
  linarith [reciprocal_two_sum k]

def coreBlock (k n : ℕ) : Prop := (oddCore n/2^k)%2^k=0

def blockEvent (k v n : ℕ) : Prop :=
  2^v∣n ∧ (n/2^v)%(2^k*2^k)<2^k

lemma coreBlock_cover (k n : ℕ) (h : coreBlock k n) :
    2^k∣n ∨ ∃ v∈range k, blockEvent k v n := by
  by_cases hn : 2^k∣n
  · exact Or.inl hn
  right
  have hn0 : n≠0 := by intro he; subst n; simp at hn
  have hv : n.factorization 2<k := by
    have hh := Nat.prime_two.pow_dvd_iff_le_factorization hn0 (k := k)
    omega
  refine ⟨n.factorization 2,mem_range.mpr hv,?_⟩
  have he : 2^(n.factorization 2)*oddCore n=n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hd : 2^(n.factorization 2)∣n := ⟨oddCore n,he.symm⟩
  have hdiv : n/2^(n.factorization 2)=oddCore n := rfl
  refine ⟨hd,?_⟩
  rw [hdiv,Nat.mod_mul,show (oddCore n/2^k)%2^k=0 from h]
  simpa using Nat.mod_lt (oddCore n) (show 0<2^k by positivity)

lemma coreBlock_count_le (k N : ℕ) :
    count (coreBlock k) N≤3*(N:ℝ)/(2:ℝ)^k+k*((2:ℝ)^k+1)+1 := by
  have hc := (count_mono (coreBlock_cover k) N).trans
    (count_or_le (fun n => 2^k∣n) (fun n => ∃ v∈range k,blockEvent k v n) N)
  have ht := multiples_count_le (show 0<2^k by positivity) N
  have hv := count_exists_le (range k) (blockEvent k) N
  have hs : (∑ v∈range k,count (blockEvent k v) N)≤
      2*(N:ℝ)/(2:ℝ)^k+k*((2:ℝ)^k+1) := by
    calc
      _ ≤ ∑ v∈range k, ((N:ℝ)/((2:ℝ)^v*(2:ℝ)^k)+(2:ℝ)^k+1) := by
        apply sum_le_sum
        intro v _
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using
          block_lift_count (d := 2^v) (q := 2^k) (by positivity) (by positivity) N
      _ = (N:ℝ)/(2:ℝ)^k*(∑ v∈range k,1/(2:ℝ)^v)+k*((2:ℝ)^k+1) := by
        rw [mul_sum]
        simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul]
        have he : (∑ v∈range k,(N:ℝ)/((2:ℝ)^v*(2:ℝ)^k))=
            ∑ v∈range k,(N:ℝ)/(2:ℝ)^k*(1/(2:ℝ)^v) := by
          apply sum_congr rfl
          intro v _
          ring
        rw [he]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (reciprocal_two_sum k)
          (by positivity : (0:ℝ)≤(N:ℝ)/(2:ℝ)^k)
        simp only [mul_div_assoc] at *
        nlinarith
  push_cast at ht
  simp only [mul_div_assoc] at *
  linarith

lemma two_pow_sub_one_coprime (v k : ℕ) : (2^(v+1)-1).Coprime (2^k) := by
  apply Nat.Coprime.pow_right
  apply Nat.coprime_two_right.mpr
  refine ⟨2^v-1,?_⟩
  rw [pow_succ']
  have hp : 0<2^v := by positivity
  omega

def plusEvent (k v n : ℕ) : Prop :=
  2^(v+1)∣n ∧ 2^k∣(2^(v+1)-1)*(n/2^(v+1))+1

def minusEvent (k v n : ℕ) : Prop :=
  2^(v+1)∣n ∧ 2^k∣(2^(v+1)-1)*(n/2^(v+1))+(2^k-1)

lemma affine_event_sum_le (k b N : ℕ) :
    (∑ v∈range k,count (fun n => 2^(v+1)∣n ∧
      2^k∣(2^(v+1)-1)*(n/2^(v+1))+b) N)≤(N:ℝ)/(2:ℝ)^k+2*k := by
  calc
    _ ≤ ∑ v∈range k, ((N:ℝ)/((2:ℝ)^(v+1)*(2:ℝ)^k)+2) := by
      apply sum_le_sum
      intro v _
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using affine_lift_count
        (d := 2^(v+1)) (q := 2^k) (by positivity) (by positivity)
        (two_pow_sub_one_coprime v k) b N
    _ = (N:ℝ)/(2:ℝ)^k*(∑ v∈range k,1/(2:ℝ)^(v+1))+2*k := by
      rw [mul_sum]
      simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul]
      congr 1
      · apply sum_congr rfl
        intro v _
        ring
      · ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (reciprocal_two_sum_shift k)
        (by positivity : (0:ℝ)≤(N:ℝ)/(2:ℝ)^k)
      nlinarith

def coreCollision (k n : ℕ) : Prop := oddCore n%2^k=oddCore (n+1)%2^k

lemma coreCollision_cover (k n : ℕ) (h : coreCollision k n) :
    (2^k∣n ∨ 2^k∣n+1) ∨
      ((∃ v∈range k, plusEvent k v n) ∨ (∃ v∈range k, minusEvent k v (n+1))) := by
  by_cases hn : 2^k∣n
  · exact Or.inl (Or.inl hn)
  by_cases hn' : 2^k∣n+1
  · exact Or.inl (Or.inr hn')
  right
  have hn0 : n≠0 := by intro he; subst n; simp at hn
  have hq : 0<2^k := by positivity
  unfold coreCollision at h
  by_cases heven : 2∣n
  · left
    let v := n.factorization 2
    have hv : v<k := by
      have hh := Nat.prime_two.pow_dvd_iff_le_factorization hn0 (k := k)
      dsimp [v]
      omega
    have hv1 : 1≤v := by
      apply (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mp
      simpa using heven
    have he : 2^v*oddCore n=n := Nat.ordProj_mul_ordCompl_eq_self n 2
    have hdiv : n/2^v=oddCore n := rfl
    have ho : oddCore (n+1)=n+1 := oddCore_eq_of_odd (by
      intro hh
      exact Nat.prime_two.not_dvd_one ((Nat.dvd_add_iff_right heven).mpr hh))
    rw [ho] at h
    have hm : Nat.ModEq (2^k) (n+1) (oddCore n) := h.symm
    have hdpos : 0<2^v := by positivity
    have hsub : 2^v-1+1=2^v := by omega
    have halg : (2^v-1)*oddCore n+1+oddCore n=n+1 := by nlinarith
    have hm' : Nat.ModEq (2^k) ((2^v-1)*oddCore n+1+oddCore n) (0+oddCore n) := by
      simpa only [halg,Nat.zero_add] using hm
    have hroot : 2^k∣(2^v-1)*oddCore n+1 :=
      Nat.modEq_zero_iff_dvd.mp (hm'.add_right_cancel' (oddCore n))
    refine ⟨v-1,mem_range.mpr (by omega),?_⟩
    unfold plusEvent
    rw [show v-1+1=v by omega,hdiv]
    exact ⟨⟨oddCore n,he.symm⟩,hroot⟩
  · right
    have hneven : 2∣n+1 := by
      simp only [Nat.dvd_iff_mod_eq_zero] at heven ⊢
      omega
    let v := (n+1).factorization 2
    have hn10 : n+1≠0 := by omega
    have hv : v<k := by
      have hh := Nat.prime_two.pow_dvd_iff_le_factorization hn10 (k := k)
      dsimp [v]
      omega
    have hv1 : 1≤v := by
      apply (Nat.prime_two.pow_dvd_iff_le_factorization hn10).mp
      simpa using hneven
    have he : 2^v*oddCore (n+1)=n+1 := Nat.ordProj_mul_ordCompl_eq_self (n+1) 2
    have hdiv : (n+1)/2^v=oddCore (n+1) := rfl
    have ho : oddCore n=n := oddCore_eq_of_odd heven
    rw [ho] at h
    have hm : Nat.ModEq (2^k) (n+1) (oddCore (n+1)+1) :=
      (show Nat.ModEq (2^k) n (oddCore (n+1)) from h).add_right 1
    have hdpos : 0<2^v := by positivity
    have hsub : 2^v-1+1=2^v := by omega
    have halg : (2^v-1)*oddCore (n+1)+oddCore (n+1)=n+1 := by nlinarith
    have hm' : Nat.ModEq (2^k) ((2^v-1)*oddCore (n+1)+oddCore (n+1))
        (1+oddCore (n+1)) := by simpa only [halg,Nat.add_comm 1] using hm
    have hh := (hm'.add_right_cancel' (oddCore (n+1))).add_right (2^k-1)
    have hqeq : 1+(2^k-1)=2^k := by omega
    rw [hqeq] at hh
    have hroot : 2^k∣(2^v-1)*oddCore (n+1)+(2^k-1) :=
      Nat.modEq_zero_iff_dvd.mp (hh.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
    refine ⟨v-1,mem_range.mpr (by omega),?_⟩
    unfold minusEvent
    rw [show v-1+1=v by omega,hdiv]
    exact ⟨⟨oddCore (n+1),he.symm⟩,hroot⟩

lemma coreCollision_count_le (k N : ℕ) :
    count (coreCollision k) N≤4*(N:ℝ)/(2:ℝ)^k+4*k+4 := by
  have h0 := count_mono (coreCollision_cover k) N
  have h1 := count_or_le (fun n => 2^k∣n ∨ 2^k∣n+1)
    (fun n => (∃ v∈range k,plusEvent k v n) ∨ (∃ v∈range k,minusEvent k v (n+1))) N
  have h2 := count_or_le (fun n => 2^k∣n) (fun n => 2^k∣n+1) N
  have h3 := count_or_le (fun n => ∃ v∈range k,plusEvent k v n)
    (fun n => ∃ v∈range k,minusEvent k v (n+1)) N
  have htail := multiples_count_le (show 0<2^k by positivity) N
  have htail' := (count_shift_le (fun n => 2^k∣n) N).trans
    (multiples_count_le (show 0<2^k by positivity) (N+1))
  have hp := (count_exists_le (range k) (plusEvent k) N).trans (affine_event_sum_le k 1 N)
  have hm := (count_shift_le (fun n => ∃ v∈range k,minusEvent k v n) N).trans
    ((count_exists_le (range k) (minusEvent k) (N+1)).trans
      (affine_event_sum_le k (2^k-1) (N+1)))
  have hrec : (1:ℝ)/(2:ℝ)^k≤1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  push_cast at htail htail' hp hm
  simp only [add_div,mul_div_assoc] at *
  linarith

lemma close_height_count_le (k N : ℕ) :
    count (fun n => |height n-height (n+1)|≤1/(2:ℚ)^(2*k+1)) N≤
      10*(N:ℝ)/(2:ℝ)^k+2*k*((2:ℝ)^k+1)+4*k+9 := by
  have hcover (n : ℕ) (h : |height n-height (n+1)|≤1/(2:ℚ)^(2*k+1)) :
      coreCollision k n ∨ coreBlock k n ∨ coreBlock k (n+1) :=
    close_reversals_cover k (oddCore n) (oddCore (n+1)) h
  have h0 := count_mono hcover N
  have h1 := count_or_le (coreCollision k) (fun n => coreBlock k n ∨ coreBlock k (n+1)) N
  have h2 := count_or_le (coreBlock k) (fun n => coreBlock k (n+1)) N
  have hc := coreCollision_count_le k N
  have hb := coreBlock_count_le k N
  have hb' := (count_shift_le (coreBlock k) N).trans (coreBlock_count_le k (N+1))
  have hrec : (1:ℝ)/(2:ℝ)^k≤1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  push_cast at hb'
  simp only [add_div,mul_div_assoc] at *
  linarith

lemma height_adjacent_ne {n : ℕ} (hn : 2≤n) : height n≠height (n+1) := by
  intro h
  have hc : oddCore n=oddCore (n+1) := rev_injective h
  have hd := oddCore_dvd n
  have hd' : oddCore n∣n+1 := hc ▸ oddCore_dvd (n+1)
  have h1 : oddCore n=1 := Nat.dvd_one.mp ((Nat.dvd_add_iff_right hd).mpr hd')
  rcases oddCore_edge_endpoint n with he | he <;> omega

noncomputable def realHeight (n : ℕ) : ℝ := height n

lemma realHeight_bounds (n : ℕ) : 0≤realHeight n ∧ realHeight n<1 := by
  unfold realHeight
  exact_mod_cast height_bounds n

lemma realHeight_even (n : ℕ) : realHeight (2*n)=realHeight n := by
  unfold realHeight
  rw [height_even]

lemma realHeight_adjacent_ne {n : ℕ} (hn : 2≤n) : realHeight n≠realHeight (n+1) := by
  unfold realHeight
  exact_mod_cast height_adjacent_ne hn

lemma realHeight_not_density_half :
    ¬{n | realHeight n<realHeight (n+1)}.HasDensity (1/2) := by
  simpa only [realHeight,Rat.cast_lt] using height_not_density_half

lemma close_real_count_le (k N : ℕ) :
    count (fun n => |realHeight n-realHeight (n+1)|≤1/(2:ℝ)^(2*k+1)) N≤
      10*(N:ℝ)/(2:ℝ)^k+2*k*((2:ℝ)^k+1)+4*k+9 := by
  have hc : count (fun n => |realHeight n-realHeight (n+1)|≤1/(2:ℝ)^(2*k+1)) N=
      count (fun n => |height n-height (n+1)|≤1/(2:ℚ)^(2*k+1)) N := by
    congr 1
    funext n
    apply propext
    unfold realHeight
    have hcast : ((1/(2:ℚ)^(2*k+1):ℚ):ℝ)=1/(2:ℝ)^(2*k+1) := by push_cast; rfl
    rw [← Rat.cast_sub,← Rat.cast_abs,← hcast,Rat.cast_le]
  rw [hc]
  exact close_height_count_le k N

/-- The bounded doubling-invariant model also has uniform anti-concentration
of adjacent gaps. Thus that property does not repair the doubling-only argument. -/
theorem realHeight_anti_concentration :
    ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop,
      count (fun n => |realHeight n-realHeight (n+1)|≤δ) N/N<ε := by
  intro ε hε
  have ht : Tendsto (fun k : ℕ => (10:ℝ)/(2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨k,hk⟩ := (ht.eventually_lt_const (half_pos hε)).exists
  refine ⟨1/(2:ℝ)^(2*k+1),by positivity,?_⟩
  let C : ℝ := 2*k*((2:ℝ)^k+1)+4*k+9
  have hC : Tendsto (fun N : ℕ => C/N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  filter_upwards [hC.eventually_lt_const (half_pos hε),eventually_gt_atTop 0]
    with N hsmall hN
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hb := div_le_div_of_nonneg_right (close_real_count_le k N) (Nat.cast_nonneg (α := ℝ) N)
  have he : (10*(N:ℝ)/(2:ℝ)^k+2*k*((2:ℝ)^k+1)+4*k+9)/(N:ℝ)=
      10/(2:ℝ)^k+C/N := by dsimp [C]; field_simp; ring
  rw [he] at hb
  linarith

/-- A moving uniform gap cutoff tending to zero captures a vanishing fraction
of adjacent pairs, despite the strictly biased ascent count of this model. -/
theorem moving_gap_count_tendsto_zero (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => count
      (fun n => |realHeight n-realHeight (n+1)|≤δ N) N/N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η,hη,hbound⟩ := realHeight_anti_concentration ε hε
  filter_upwards [hδ.eventually_lt_const hη,hbound] with N hN hB
  have hc := count_mono (fun n (hn : |realHeight n-realHeight (n+1)|≤δ N) =>
    hn.trans hN.le) N
  have hh := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) N)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (count_nonneg _ _) (Nat.cast_nonneg _))]
  exact hh.trans_lt hB

/-- All these hypotheses concern a model, not `Nat.maxPrimeFac`. Invariance
under general integer dilations is deliberately not asserted. -/
theorem bounded_doubling_and_anti_concentration_are_insufficient :
    ∃ f : ℕ → ℝ,
      (∀ n, 0≤f n ∧ f n<1) ∧
      (∀ n, f (2*n)=f n) ∧
      (∀ n≥2, f n≠f (n+1)) ∧
      (∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop,
        count (fun n => |f n-f (n+1)|≤δ) N/N<ε) ∧
      ¬{n | f n<f (n+1)}.HasDensity (1/2) :=
  ⟨realHeight,realHeight_bounds,realHeight_even,fun _ hn => realHeight_adjacent_ne hn,
    realHeight_anti_concentration,realHeight_not_density_half⟩

end Erdos371BinaryReversalSeparation

#print axioms Erdos371BinaryReversalSeparation.close_height_count_le
#print axioms Erdos371BinaryReversalSeparation.moving_gap_count_tendsto_zero
#print axioms Erdos371BinaryReversalSeparation.bounded_doubling_and_anti_concentration_are_insufficient
