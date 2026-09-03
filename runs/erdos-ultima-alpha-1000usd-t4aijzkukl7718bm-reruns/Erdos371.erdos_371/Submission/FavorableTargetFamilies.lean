import FormalConjecturesUtil

/-! Multiplicative families of favorable affine comparisons sharing a fixed
prime divisor. These results do not give a uniform finite-range Hall bound. -/

namespace Erdos371FavorableTargetFamilies

open Finset
abbrev P := Nat.maxPrimeFac

lemma inverse_residue {r M : ℕ} (hM : 0 < M) (hrM : r.Coprime M) :
    ∃ c : ℕ, c.Coprime M ∧ r*c ≡ 1 [MOD M] := by
  let c := r^(M.totient-1)
  refine ⟨c, hrM.pow_left _, ?_⟩
  have he : r*c = r^M.totient := by
    dsimp [c]
    rw [← pow_succ', Nat.sub_add_cancel (Nat.totient_pos.mpr hM)]
  rw [he]
  exact Nat.ModEq.pow_totient hrM

/-- An arbitrarily large prime `q` can be paired with the prescribed prime `r`
in the affine value of a `q`-smooth favorable target. -/
theorem plus_seed {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime)
    (hrp : r.Coprime p) (B : ℕ) :
    ∃ b q : ℕ, 0 < b ∧ B < q ∧ r < q ∧ q.Prime ∧
      P b < q ∧ p*b+1 = r*q := by
  let t := r+1
  let M := p*t
  have ht : 0 < t := by dsimp [t]; omega
  have hM : 0 < M := Nat.mul_pos (by omega) ht
  have hrM : r.Coprime M := hrp.mul_right
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right r))
  obtain ⟨c, hc, hrc⟩ := inverse_residue hM hrM
  obtain ⟨q, hqbig, hq, hqmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max B M)
    (q := M) (a := c) hM.ne' hc
  have hMq : M < q := (le_max_right _ _).trans_lt hqbig
  have htM : t ≤ M := by dsimp [M]; nlinarith
  have hrMlt : r < M := by dsimp [t] at htM; omega
  have hd : M ∣ r*q-1 := (Nat.modEq_iff_dvd' (by nlinarith [hr.two_le] : 1 ≤ r*q)).mp
    ((hqmod.mul_left r).trans hrc).symm
  let k := (r*q-1)/M
  have hqr : q ≤ r*q := by nlinarith [hr.two_le]
  have hprod : 1 ≤ r*q := by omega
  have hk : 0 < k := Nat.div_pos (by omega) hM
  have hkq : k < q := (Nat.div_lt_iff_lt_mul hM).mpr <|
    (Nat.sub_le _ _).trans_lt (by nlinarith)
  have hfac : M*k = r*q-1 := by
    simpa only [k, Nat.mul_comm] using Nat.div_mul_cancel hd
  refine ⟨t*k, q, Nat.mul_pos ht hk, (le_max_left _ _).trans_lt hqbig,
    hrMlt.trans hMq, hq, ?_, ?_⟩
  · rw [P, Nat.maxPrimeFac_mul ht.ne' hk.ne']
    exact max_lt (Nat.maxPrimeFac_le.trans_lt (htM.trans_lt hMq))
      (Nat.maxPrimeFac_le.trans_lt hkq)
  · have he : p*(t*k) = M*k := by dsimp [M]; ring
    rw [he, hfac, Nat.sub_add_cancel hprod]

/-- The corresponding seed for the minus affine comparison. -/
theorem minus_seed {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime)
    (hrp : r.Coprime p) (B : ℕ) :
    ∃ b q : ℕ, 0 < b ∧ B < q ∧ r < q ∧ q.Prime ∧
      P b < q ∧ p*b-1 = r*q := by
  let t := r+1
  let M := p*t
  have ht : 0 < t := by dsimp [t]; omega
  have hM : 0 < M := Nat.mul_pos (by omega) ht
  have hrM : r.Coprime M := hrp.mul_right
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right r))
  obtain ⟨c, hc, hrc⟩ := inverse_residue hM hrM
  have hMc : (M-1).Coprime M :=
    (Nat.coprime_self_sub_left hM).mpr (Nat.coprime_one_left M)
  obtain ⟨q, hqbig, hq, hqmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max B M)
    (q := M) (a := c*(M-1)) hM.ne' (hc.mul_left hMc)
  have hMq : M < q := (le_max_right _ _).trans_lt hqbig
  have htM : t ≤ M := by dsimp [M]; nlinarith
  have hrMlt : r < M := by dsimp [t] at htM; omega
  have hrc' : r*(c*(M-1)) ≡ M-1 [MOD M] := by
    simpa only [Nat.mul_assoc, one_mul] using hrc.mul_right (M-1)
  have hh := ((hqmod.mul_left r).trans hrc').add_right 1
  rw [Nat.sub_add_cancel hM] at hh
  have hd : M ∣ r*q+1 := Nat.modEq_zero_iff_dvd.mp
    (hh.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl M)))
  let k := (r*q+1)/M
  have hk : 0 < k := Nat.div_pos (by nlinarith [hr.two_le]) hM
  have hkq : k < q := (Nat.div_lt_iff_lt_mul hM).mpr (by nlinarith [hq.one_lt])
  have hfac : M*k = r*q+1 := by
    simpa only [k, Nat.mul_comm] using Nat.div_mul_cancel hd
  refine ⟨t*k, q, Nat.mul_pos ht hk, (le_max_left _ _).trans_lt hqbig,
    hrMlt.trans hMq, hq, ?_, ?_⟩
  · rw [P, Nat.maxPrimeFac_mul ht.ne' hk.ne']
    exact max_lt (Nat.maxPrimeFac_le.trans_lt (htM.trans_lt hMq))
      (Nat.maxPrimeFac_le.trans_lt hkq)
  · have he : p*(t*k) = M*k := by dsimp [M]; ring
    rw [he, hfac]
    omega

lemma plus_multiply {p b r q u : ℕ} (hb : 0 < b) (hq : q.Prime)
    (hPb : P b < q) (hseed : p*b+1 = r*q)
    (hu : 0 < u) (hPu : P u < q) (hmod : u ≡ 1 [MOD r*q]) :
    0 < b*u ∧ r ∣ p*(b*u)+1 ∧ P (b*u) < P (p*(b*u)+1) := by
  have hd : r*q ∣ p*(b*u)+1 := by
    apply Nat.modEq_zero_iff_dvd.mp
    have hh := (hmod.mul_left (p*b)).add_right 1
    simp only [mul_one, hseed, Nat.mul_assoc] at hh
    exact hh.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _))
  have hP : P (b*u) < q := by
    rw [P, Nat.maxPrimeFac_mul hb.ne' hu.ne']
    exact max_lt hPb hPu
  exact ⟨Nat.mul_pos hb hu, (dvd_mul_right r q).trans hd,
    hP.trans_le (Nat.le_maxPrimeFac (by omega) hq ((dvd_mul_left q r).trans hd))⟩

lemma minus_multiply {p b r q u : ℕ} (hp : 2 ≤ p) (hb : 0 < b) (hq : q.Prime)
    (hPb : P b < q) (hseed : p*b-1 = r*q)
    (hu : 0 < u) (hPu : P u < q) (hmod : u ≡ 1 [MOD r*q]) :
    0 < b*u ∧ r ∣ p*(b*u)-1 ∧ P (b*u) < P (p*(b*u)-1) := by
  have hpb : 1 ≤ p*b := by nlinarith
  have hpbu : 1 < p*(b*u) := by nlinarith [Nat.mul_pos hb hu]
  have hsmod : p*b ≡ 1 [MOD r*q] :=
    ((Nat.modEq_iff_dvd' hpb).mpr (hseed.symm ▸ dvd_refl (r*q))).symm
  have hd : r*q ∣ p*(b*u)-1 := by
    apply (Nat.modEq_iff_dvd' hpbu.le).mp
    have hh := hmod.mul_left (p*b)
    simp only [mul_one] at hh
    simpa only [mul_one, Nat.mul_assoc] using (hh.trans hsmod).symm
  have hP : P (b*u) < q := by
    rw [P, Nat.maxPrimeFac_mul hb.ne' hu.ne']
    exact max_lt hPb hPu
  exact ⟨Nat.mul_pos hb hu, (dvd_mul_right r q).trans hd,
    hP.trans_le (Nat.le_maxPrimeFac (by omega) hq ((dvd_mul_left q r).trans hd))⟩

/-- A product over distinct prime generators, with a common exponent step. -/
def monomial {ι : Type*} [Fintype ι] (g : ι → ℕ) (e : ℕ) (k : ι → ℕ) : ℕ :=
  ∏ i, g i ^ (e*k i)

lemma monomial_pos {ι : Type*} [Fintype ι] {g : ι → ℕ}
    (hg : ∀ i, (g i).Prime) (e : ℕ) (k : ι → ℕ) :
    0 < monomial g e k :=
  Finset.prod_pos (fun i _ => pow_pos (hg i).pos _)

lemma maxPrimeFac_prod_lt {ι : Type*} {s : Finset ι} {g : ι → ℕ} {q : ℕ}
    (hq : 1 < q) (hg : ∀ i ∈ s, g i ≠ 0 ∧ P (g i) < q) :
    P (∏ i ∈ s, g i) < q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hq
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, P, Nat.maxPrimeFac_mul
      (hg a (mem_insert_self _ _)).1
      (Finset.prod_ne_zero_iff.mpr (fun i hi => (hg i (mem_insert_of_mem hi)).1))]
    exact max_lt (hg a (mem_insert_self _ _)).2
      (ih (fun i hi => hg i (mem_insert_of_mem hi)))

lemma monomial_small {ι : Type*} [Fintype ι] {g : ι → ℕ} {q : ℕ}
    (hq : 1 < q) (hg : ∀ i, (g i).Prime ∧ g i < q) (e : ℕ) (k : ι → ℕ) :
    P (monomial g e k) < q := by
  apply maxPrimeFac_prod_lt hq
  intro i _
  refine ⟨pow_ne_zero _ (hg i).1.ne_zero, ?_⟩
  by_cases he : e*k i = 0
  · simpa [he] using hq
  · rw [P, Nat.maxPrimeFac_pow he, (hg i).1.maxPrimeFac_eq_self]
    exact (hg i).2

lemma monomial_mod {ι : Type*} [Fintype ι] {g : ι → ℕ} {M : ℕ}
    (hg : ∀ i, (g i).Coprime M) (k : ι → ℕ) :
    monomial g M.totient k ≡ 1 [MOD M] := by
  have hh : ∀ i ∈ (univ : Finset ι),
      g i ^ (M.totient*k i) ≡ 1 [MOD M] := by
    intro i _
    simpa only [pow_mul, one_pow] using (Nat.ModEq.pow_totient (hg i)).pow (k i)
  simpa only [monomial, Finset.prod_const_one] using Nat.ModEq.prod hh

lemma monomial_factorization {ι : Type*} [Fintype ι] {g : ι → ℕ}
    (hg : ∀ i, (g i).Prime) (hinj : Function.Injective g) (e : ℕ) (k : ι → ℕ) (i : ι) :
    (monomial g e k).factorization (g i) = e*k i := by
  classical
  rw [monomial, Nat.factorization_prod_apply (fun j _ => pow_ne_zero _ (hg j).ne_zero)]
  rw [Finset.sum_eq_single i]
  · simp [(hg i).factorization_pow]
  · intro j _ hji
    simp only [(hg j).factorization_pow, Finsupp.single_apply]
    exact if_neg (fun h => hji (hinj h))
  · simp

lemma monomial_injective {ι : Type*} [Fintype ι] {g : ι → ℕ}
    (hg : ∀ i, (g i).Prime) (hinj : Function.Injective g) {e : ℕ} (he : 0 < e) :
    Function.Injective (monomial g e) := by
  intro k l h
  funext i
  have hh := congrArg (fun n : ℕ => n.factorization (g i)) h
  dsimp only at hh
  rw [monomial_factorization hg hinj, monomial_factorization hg hinj] at hh
  exact Nat.eq_of_mul_eq_mul_left he hh

lemma monomial_le {ι : Type*} [Fintype ι] {g : ι → ℕ}
    (hg : ∀ i, 0 < g i) (e L : ℕ) {k : ι → ℕ} (hk : ∀ i, k i ≤ L) :
    monomial g e k ≤ (∏ i, g i ^ e)^L := by
  rw [monomial, ← Finset.prod_pow]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro i _
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (hg i) (Nat.mul_le_mul_left e (hk i))

/-- A finite cube of exponent vectors gives exactly `(L+1)^card ι` distinct
favorable targets. The constants `b,q` and the exponential size bound are fixed
before choosing the cube side length. -/
theorem plus_family {ι : Type*} [Fintype ι] {g : ι → ℕ}
    (hg : ∀ i, (g i).Prime) (hinj : Function.Injective g)
    {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime) (hrp : r.Coprime p)
    (hgr : ∀ i, g i ≠ r) :
    ∃ b C : ℕ, 0 < b ∧ 0 < C ∧ ∀ L : ℕ,
      (L+1)^Fintype.card ι ≤
        ((Icc 1 (b*C^L)).filter (fun a =>
          r ∣ p*a+1 ∧ P a < P (p*a+1))).card := by
  classical
  obtain ⟨b, q, hb, hqbig, hrq, hq, hPb, hseed⟩ :=
    plus_seed hp hr hrp (univ.sup g)
  have hgq (i : ι) : g i < q := (Finset.le_sup (mem_univ i)).trans_lt hqbig
  have hgM (i : ι) : (g i).Coprime (r*q) :=
    ((Nat.coprime_primes (hg i) hr).mpr (hgr i)).mul_right
      ((Nat.coprime_primes (hg i) hq).mpr (hgq i).ne)
  let e := (r*q).totient
  have he : 0 < e := Nat.totient_pos.mpr (Nat.mul_pos hr.pos hq.pos)
  let C := ∏ i, g i ^ e
  have hC : 0 < C := Finset.prod_pos (fun i _ => pow_pos (hg i).pos _)
  refine ⟨b, C, hb, hC, ?_⟩
  intro L
  let f : (ι → Fin (L+1)) → ℕ := fun k => b*monomial g e (fun i => (k i).val)
  have hf : Function.Injective f := by
    intro k l h
    have hm := Nat.eq_of_mul_eq_mul_left hb h
    have hkl := monomial_injective hg hinj he hm
    funext i
    exact Fin.ext (congrFun hkl i)
  have hsub : univ.image f ⊆ (Icc 1 (b*C^L)).filter
      (fun a => r ∣ p*a+1 ∧ P a < P (p*a+1)) := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := mem_image.mp ha
    have hgood := plus_multiply hb hq hPb hseed (monomial_pos hg e (fun i => (k i).val))
      (monomial_small hq.one_lt (fun i => ⟨hg i, hgq i⟩) e (fun i => (k i).val))
      (monomial_mod hgM (fun i => (k i).val))
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hgood.1, ?_⟩, hgood.2⟩
    exact Nat.mul_le_mul_left b (monomial_le (fun i => (hg i).pos) e L
      (fun i => Nat.le_of_lt_succ (k i).isLt))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hf.injOn] at hc
  simpa using hc

/-- The same multiplicative cube construction for minus comparisons. -/
theorem minus_family {ι : Type*} [Fintype ι] {g : ι → ℕ}
    (hg : ∀ i, (g i).Prime) (hinj : Function.Injective g)
    {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime) (hrp : r.Coprime p)
    (hgr : ∀ i, g i ≠ r) :
    ∃ b C : ℕ, 0 < b ∧ 0 < C ∧ ∀ L : ℕ,
      (L+1)^Fintype.card ι ≤
        ((Icc 1 (b*C^L)).filter (fun a =>
          r ∣ p*a-1 ∧ P a < P (p*a-1))).card := by
  classical
  obtain ⟨b, q, hb, hqbig, hrq, hq, hPb, hseed⟩ :=
    minus_seed hp hr hrp (univ.sup g)
  have hgq (i : ι) : g i < q := (Finset.le_sup (mem_univ i)).trans_lt hqbig
  have hgM (i : ι) : (g i).Coprime (r*q) :=
    ((Nat.coprime_primes (hg i) hr).mpr (hgr i)).mul_right
      ((Nat.coprime_primes (hg i) hq).mpr (hgq i).ne)
  let e := (r*q).totient
  have he : 0 < e := Nat.totient_pos.mpr (Nat.mul_pos hr.pos hq.pos)
  let C := ∏ i, g i ^ e
  have hC : 0 < C := Finset.prod_pos (fun i _ => pow_pos (hg i).pos _)
  refine ⟨b, C, hb, hC, ?_⟩
  intro L
  let f : (ι → Fin (L+1)) → ℕ := fun k => b*monomial g e (fun i => (k i).val)
  have hf : Function.Injective f := by
    intro k l h
    have hm := Nat.eq_of_mul_eq_mul_left hb h
    have hkl := monomial_injective hg hinj he hm
    funext i
    exact Fin.ext (congrFun hkl i)
  have hsub : univ.image f ⊆ (Icc 1 (b*C^L)).filter
      (fun a => r ∣ p*a-1 ∧ P a < P (p*a-1)) := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := mem_image.mp ha
    have hgood := minus_multiply hp hb hq hPb hseed (monomial_pos hg e (fun i => (k i).val))
      (monomial_small hq.one_lt (fun i => ⟨hg i, hgq i⟩) e (fun i => (k i).val))
      (monomial_mod hgM (fun i => (k i).val))
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hgood.1, ?_⟩, hgood.2⟩
    exact Nat.mul_le_mul_left b (monomial_le (fun i => (hg i).pos) e L
      (fun i => Nat.le_of_lt_succ (k i).isLt))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hf.injOn] at hc
  simpa using hc

end Erdos371FavorableTargetFamilies

#print axioms Erdos371FavorableTargetFamilies.plus_seed
#print axioms Erdos371FavorableTargetFamilies.minus_seed
#print axioms Erdos371FavorableTargetFamilies.plus_multiply
#print axioms Erdos371FavorableTargetFamilies.minus_multiply

#print axioms Erdos371FavorableTargetFamilies.plus_family
#print axioms Erdos371FavorableTargetFamilies.minus_family
