import FormalConjecturesUtil

/-!
Primitive gap parameters for four distinct positive roots with equal square
sums. This is a counting tool, not a settlement of Erdős 773.
-/
namespace Erdos773.PrimitiveSquareCollisions
open Finset
set_option maxHeartbeats 1000000

abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)

/-- Increasing positive roots; every support has just one such ordering. -/
def ordered (N : ℕ) : Finset Quad :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ ((Icc 1 N) ×ˢ (Icc 1 N))).filter
    (fun q => q.1.1 < q.1.2 ∧ q.1.2 < q.2.1 ∧ q.2.1 < q.2.2 ∧
      q.1.1 ^ 2 + q.2.2 ^ 2 = q.1.2 ^ 2 + q.2.1 ^ 2)

/-- The parameters are `((u,v),(g,w))`. The first two are the coprime
parts of the left and right gaps. -/
def Represents (p q : Quad) : Prop :=
  2 * q.1.1 + p.1.1 * p.2.1 = p.1.2 * p.2.2 ∧
  2 * q.1.2 = p.1.2 * p.2.2 + p.1.1 * p.2.1 ∧
  2 * q.2.1 + p.1.2 * p.2.1 = p.1.1 * p.2.2 ∧
  2 * q.2.2 = p.1.1 * p.2.2 + p.1.2 * p.2.1

/-- Exact constraints, including positivity, ordering, height and parity. -/
def Valid (N : ℕ) (p : Quad) : Prop :=
  0 < p.1.2 ∧ p.1.2 < p.1.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
  p.1.1.Coprime p.1.2 ∧
  p.1.1 * p.2.1 < p.1.2 * p.2.2 ∧
  (p.1.1 + p.1.2) * p.2.1 < (p.1.1 - p.1.2) * p.2.2 ∧
  p.1.1 * p.2.2 + p.1.2 * p.2.1 ≤ 2 * N ∧
  (p.1.2 * p.2.2 + p.1.1 * p.2.1) % 2 = 0 ∧
  (p.1.1 * p.2.2 + p.1.2 * p.2.1) % 2 = 0

instance (N : ℕ) (p : Quad) : Decidable (Valid N p) := inferInstanceAs
  (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Every increasing collision has primitive gap parameters. -/
theorem exists_parameters {N : ℕ} {q : Quad} (hq : q ∈ ordered N) :
    ∃ p : Quad, Valid N p ∧ Represents p q := by
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  obtain ⟨hm,hab,hbc,hcd,he⟩ := mem_filter.mp hq
  simp only [mem_product,mem_Icc] at hm
  dsimp only at hab hbc hcd he
  have hleft : 0 < b - a := Nat.sub_pos_of_lt hab
  have hright : 0 < d - c := Nat.sub_pos_of_lt hcd
  obtain ⟨g,u,v,hg,huv,hug,hvg⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left (d-c) hleft)
  have hu : 0 < u := by
    by_contra! hh
    have : u = 0 := by omega
    simp [this] at hug
    omega
  have hv : 0 < v := by
    by_contra! hh
    have : v = 0 := by omega
    simp [this] at hvg
    omega
  have hb : b = a + u*g := by omega
  have hd : d = c + v*g := by omega
  have hprod : u * (a+b) = v * (c+d) := by
    apply Nat.eq_of_mul_eq_mul_right hg
    nlinarith only [he,hb,hd]
  have hvsum : v ∣ a+b := huv.symm.dvd_of_dvd_mul_left ⟨c+d,hprod⟩
  obtain ⟨w,hw⟩ := hvsum
  have hwpos : 0 < w := by
    by_contra! hh
    have : w = 0 := by omega
    simp [this] at hw
    omega
  have hw' : c+d = u*w := by
    apply Nat.eq_of_mul_eq_mul_left hv
    rw [hw] at hprod
    nlinarith only [hprod]
  have hvu : v < u := by
    by_contra! hh
    have hm1 := Nat.mul_le_mul_right w hh
    rw [← hw, ← hw'] at hm1
    omega
  have huvs : u - v + v = u := Nat.sub_add_cancel hvu.le
  refine ⟨((u,v),(g,w)), ?_, ?_⟩
  · change 0 < v ∧ v < u ∧ 0 < g ∧ 0 < w ∧ u.Coprime v ∧ _
    refine ⟨hv,hvu,hg,hwpos,huv,?_,?_,?_,?_,?_⟩
    · nlinarith only [hw,hb,hm]
    · nlinarith only [hbc,hb,hd,hw,hw',huvs]
    · nlinarith only [hw',hd,hm]
    · have hh : v*w+u*g = 2*b := by omega
      rw [hh]
      omega
    · have hh : u*w+v*g = 2*d := by omega
      rw [hh]
      omega
  · change 2*a+u*g=v*w ∧ 2*b=v*w+u*g ∧ 2*c+v*g=u*w ∧ 2*d=u*w+v*g
    omega

/-- The four roots recovered from primitive parameters. -/
def decode (p : Quad) : Quad :=
  (((p.1.2*p.2.2-p.1.1*p.2.1)/2, (p.1.2*p.2.2+p.1.1*p.2.1)/2),
    ((p.1.1*p.2.2-p.1.2*p.2.1)/2, (p.1.1*p.2.2+p.1.2*p.2.1)/2))

lemma decode_of_represents {p q : Quad} (h : Represents p q) : decode p = q := by
  rcases p with ⟨⟨u,v⟩,⟨g,w⟩⟩
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  change 2*a+u*g=v*w ∧ 2*b=v*w+u*g ∧ 2*c+v*g=u*w ∧ 2*d=u*w+v*g at h
  dsimp [decode]
  congr 2 <;> omega

lemma valid_represents_decode {N : ℕ} {p : Quad} (h : Valid N p) :
    Represents p (decode p) := by
  rcases p with ⟨⟨u,v⟩,⟨g,w⟩⟩
  obtain ⟨hv,hvu,hg,hw,hcop,ha,hbc,hN,hpar,hpar'⟩ := h
  dsimp only at hv hvu hg hw hcop ha hbc hN hpar hpar'
  have hsub : u-v+v=u := Nat.sub_add_cancel hvu.le
  have hc : v*g ≤ u*w := by nlinarith only [hbc,hsub,ha]
  dsimp [Represents,decode]
  omega

lemma valid_decode_mem {N : ℕ} {p : Quad} (h : Valid N p) :
    decode p ∈ ordered N := by
  have hr := valid_represents_decode h
  generalize hq : decode p = q at hr ⊢
  rcases p with ⟨⟨u,v⟩,⟨g,w⟩⟩
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  obtain ⟨hv,hvu,hg,hw,hcop,ha,hbc,hN,hpar,hpar'⟩ := h
  dsimp only at hv hvu hg hw hcop ha hbc hN hpar hpar'
  change 2*a+u*g=v*w ∧ 2*b=v*w+u*g ∧ 2*c+v*g=u*w ∧ 2*d=u*w+v*g at hr
  have hu : 0 < u := by omega
  have hug : 0 < u*g := Nat.mul_pos hu hg
  have hvg : 0 < v*g := Nat.mul_pos hv hg
  have hsub : u-v+v=u := Nat.sub_add_cancel hvu.le
  have hab : a < b := by omega
  have hbc' : b < c := by nlinarith only [hr.1,hr.2.1,hr.2.2.1,hbc,hsub]
  have hcd : c < d := by omega
  apply mem_filter.mpr
  refine ⟨?_,hab,hbc',hcd,?_⟩
  · simp only [mem_product,mem_Icc]
    omega
  · dsimp only
    nlinarith only [sq_nonneg (u*g), sq_nonneg (v*g), hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2, mul_comm u v]

/-- The common scale of the two gaps really is their gcd. -/
lemma gap_gcd {p q : Quad} (hcop : p.1.1.Coprime p.1.2)
    (h : Represents p q) : Nat.gcd (q.1.2-q.1.1) (q.2.2-q.2.1) = p.2.1 := by
  rcases p with ⟨⟨u,v⟩,⟨g,w⟩⟩
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  change 2*a+u*g=v*w ∧ 2*b=v*w+u*g ∧ 2*c+v*g=u*w ∧ 2*d=u*w+v*g at h
  have hb : b-a=u*g := by omega
  have hd : d-c=v*g := by omega
  change Nat.gcd (b-a) (d-c) = g
  rw [hb,hd,Nat.gcd_mul_right,hcop.gcd_eq_one,one_mul]

/-- There is no overcount from the parameterization. -/
lemma parameters_unique {N : ℕ} {p r q : Quad} (hp : Valid N p) (hr : Valid N r)
    (hpq : Represents p q) (hrq : Represents r q) : p = r := by
  have hg := (gap_gcd hp.2.2.2.2.1 hpq).symm.trans
    (gap_gcd hr.2.2.2.2.1 hrq)
  rcases p with ⟨⟨u,v⟩,⟨g,w⟩⟩
  rcases r with ⟨⟨u',v'⟩,⟨g',w'⟩⟩
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  dsimp only at hg
  subst g'
  obtain ⟨hv,hvu,hgpos,hw,_,_⟩ := hp
  dsimp only at hv hvu hgpos hw
  change 2*a+u*g=v*w ∧ 2*b=v*w+u*g ∧ 2*c+v*g=u*w ∧ 2*d=u*w+v*g at hpq
  change 2*a+u'*g=v'*w' ∧ 2*b=v'*w'+u'*g ∧ 2*c+v'*g=u'*w' ∧ 2*d=u'*w'+v'*g at hrq
  have huu : u=u' := Nat.eq_of_mul_eq_mul_right hgpos (by omega)
  have hvv : v=v' := Nat.eq_of_mul_eq_mul_right hgpos (by omega)
  subst u'
  subst v'
  have hww : w=w' := Nat.eq_of_mul_eq_mul_left hv (by omega)
  simp [hww]

/-- Every parameter is bounded by twice the root height. -/
lemma valid_bounds {N : ℕ} {p : Quad} (h : Valid N p) :
    p.1.1 ∈ Icc 1 (2*N) ∧ p.1.2 ∈ Icc 1 (2*N) ∧
      p.2.1 ∈ Icc 1 (2*N) ∧ p.2.2 ∈ Icc 1 (2*N) := by
  rcases p with ⟨⟨u,v⟩,⟨g,w⟩⟩
  obtain ⟨hv,hvu,hg,hw,_,_,_,hN,_⟩ := h
  dsimp only at hv hvu hg hw hN
  have hu : 0 < u := by omega
  have h1 := Nat.mul_le_mul_left u hw
  have h2 := Nat.mul_le_mul_right w hu
  have h3 := Nat.mul_le_mul_right g hv
  simp only [mem_Icc]
  omega

/-- The finite parameter space, with no duplicate presentations. -/
def parameters (N : ℕ) : Finset Quad :=
  (((Icc 1 (2*N)) ×ˢ (Icc 1 (2*N))) ×ˢ
    ((Icc 1 (2*N)) ×ˢ (Icc 1 (2*N)))).filter (Valid N)

@[simp] lemma mem_parameters {N : ℕ} {p : Quad} :
    p ∈ parameters N ↔ Valid N p := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    obtain ⟨hu,hv,hg,hw⟩ := valid_bounds h
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hu,hv⟩,
      mem_product.mpr ⟨hg,hw⟩⟩,h⟩

/-- Exact equality, rather than a many-to-one counting estimate. -/
theorem parameters_card (N : ℕ) : (parameters N).card = (ordered N).card := by
  apply card_nbij decode
  · intro p hp
    exact valid_decode_mem (mem_parameters.mp hp)
  · intro p hp r hr he
    have hpr := valid_represents_decode (mem_parameters.mp hp)
    have hrr := valid_represents_decode (mem_parameters.mp hr)
    rw [he] at hpr
    exact parameters_unique (mem_parameters.mp hp) (mem_parameters.mp hr) hpr hrr
  · intro q hq
    obtain ⟨p,hp,hpq⟩ := exists_parameters hq
    exact ⟨p,mem_parameters.mpr hp,decode_of_represents hpq⟩

/-- The two parity constraints have exactly these possibilities. -/
lemma parity_classification {u v g w : ℕ} (hc : u.Coprime v) :
    ((v*w+u*g)%2=0 ∧ (u*w+v*g)%2=0) ↔
      ((u%2=1 ∧ v%2=1 ∧ g%2=w%2) ∨
       (u%2 ≠ v%2 ∧ g%2=0 ∧ w%2=0)) := by
  have hnot : ¬ (u%2=0 ∧ v%2=0) := by
    rintro ⟨hu,hv⟩
    have hh := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu) (Nat.dvd_of_mod_eq_zero hv)
    rw [hc.gcd_eq_one] at hh
    norm_num at hh
  have hu := Nat.mod_lt u (by decide : 0 < 2)
  have hv := Nat.mod_lt v (by decide : 0 < 2)
  have hg := Nat.mod_lt g (by decide : 0 < 2)
  have hw := Nat.mod_lt w (by decide : 0 < 2)
  rw [Nat.add_mod (v*w) (u*g) 2, Nat.add_mod (u*w) (v*g) 2,
    Nat.mul_mod v w 2,Nat.mul_mod u g 2,Nat.mul_mod u w 2,Nat.mul_mod v g 2]
  interval_cases hu' : u%2 <;> interval_cases hv' : v%2 <;>
    interval_cases hg' : g%2 <;> interval_cases hw' : w%2 <;> simp_all

/-- The number of allowed pairs of parity residues. A value of one means
both scales are even; two means their parities match. -/
def parityWeight (u v : ℕ) : ℕ :=
  if u%2=0 ∧ v%2=0 then 0 else if u%2=1 ∧ v%2=1 then 2 else 1

/-- A small, explicit relaxation of coprimality, sufficient to preserve
useful leading constants in the collision count. -/
def sieveWeight (u v : ℕ) : ℕ :=
  if (u%3=0 ∧ v%3=0) ∨ (u%5=0 ∧ v%5=0) then 0 else parityWeight u v

lemma sieveWeight_of_coprime {u v : ℕ} (h : u.Coprime v) :
    sieveWeight u v = parityWeight u v := by
  have h3 : ¬ (u%3=0 ∧ v%3=0) := by
    rintro ⟨hu,hv⟩
    have hh := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu) (Nat.dvd_of_mod_eq_zero hv)
    rw [h.gcd_eq_one] at hh
    norm_num at hh
  have h5 : ¬ (u%5=0 ∧ v%5=0) := by
    rintro ⟨hu,hv⟩
    have hh := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu) (Nat.dvd_of_mod_eq_zero hv)
    rw [h.gcd_eq_one] at hh
    norm_num at hh
  simp [sieveWeight,h3,h5]

lemma sieveWeight_le_two (u v : ℕ) : sieveWeight u v ≤ 2 := by
  unfold sieveWeight parityWeight
  split_ifs <;> norm_num

lemma sieveWeight_mod (u v : ℕ) : sieveWeight u v = sieveWeight (u%30) (v%30) := by
  have h2 : 2 ∣ 30 := by norm_num
  have h3 : 3 ∣ 30 := by norm_num
  have h5 : 5 ∣ 30 := by norm_num
  simp only [sieveWeight,parityWeight,Nat.mod_mod_of_dvd _ h2,
    Nat.mod_mod_of_dvd _ h3,Nat.mod_mod_of_dvd _ h5]

lemma sieveWeight_mod_right (u v : ℕ) : sieveWeight u v = sieveWeight u (v%30) := by
  have h2 : 2 ∣ 30 := by norm_num
  have h3 : 3 ∣ 30 := by norm_num
  have h5 : 5 ∣ 30 := by norm_num
  simp only [sieveWeight,parityWeight,Nat.mod_mod_of_dvd _ h2,
    Nat.mod_mod_of_dvd _ h3,Nat.mod_mod_of_dvd _ h5]

/-- Average parity multiplicity after excluding common factors 2, 3 and 5.
The finite calculation is reduced by the kernel, not by native evaluation. -/
lemma sieveWeight_sum :
    ∑ u ∈ range 30, ∑ v ∈ range 30, sieveWeight u v = 768 := by decide

#print axioms exists_parameters
#print axioms valid_decode_mem
#print axioms parameters_unique
#print axioms parameters_card
#print axioms parity_classification
#print axioms sieveWeight_sum
end Erdos773.PrimitiveSquareCollisions
