import Submission.UpperHalfPlaneFusion

/-! Shared two-point profiles obstruct dense norm-minus-one fusions of finite
upper-half-plane graphs. This is a construction obstruction, not Erdős 714. -/

set_option maxHeartbeats 4000000
noncomputable section
open Classical SimpleGraph Polynomial
open Erdos714UpperHalfPlane

namespace Erdos714UpperHalfPlaneCircle
variable {K : Type*} [Field K]

def quadraticNorm (τ : K →+* K) (x : K) : K := x*τ x

def cayley (x : K) : K := (x-1)/(x+1)
def pull (β x : K) : K := (1+x)/(β*(1-x))
def parameter (β : K) : K := 1/(4*(1-β^2))

lemma norm_eq_pow (q : ℕ) (τ : K →+* K) (hτ : ∀ x, τ x=x^q) (x : K) :
    quadraticNorm τ x=x^(q+1) := by rw [quadraticNorm,hτ,pow_succ]; ring

lemma norm_ne_zero (τ : K →+* K) {x n : K} (hx : quadraticNorm τ x=n) (hn : n ≠ 0) : x ≠ 0 := by
  intro hz
  simp [quadraticNorm,hz] at hx
  exact hn hx.symm

lemma conjugate_eq_div (τ : K →+* K) {x n : K} (hx : quadraticNorm τ x=n) (hx0 : x ≠ 0) :
    τ x=n/x := by apply (eq_div_iff hx0).mpr; simpa [quadraticNorm,mul_comm] using hx

lemma unit_neq_minus (h₂ : (2 : K) ≠ 0) (τ : K →+* K) {v β : K}
    (hv : quadraticNorm τ v=1) (hb : quadraticNorm τ β = -1) : v^2 ≠ β^2 := by
  intro he
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · rw [he,hb] at hv
    apply h₂
    linear_combination -hv
  · rw [he] at hv
    have hnorm : quadraticNorm τ (-β)=quadraticNorm τ β := by simp [quadraticNorm]
    rw [hnorm,hb] at hv
    apply h₂
    linear_combination -hv

lemma beta_ne_one_sq (h₂ : (2 : K) ≠ 0) (τ : K →+* K) {β : K}
    (hb : quadraticNorm τ β = -1) : 1-β^2 ≠ 0 := by
  apply sub_ne_zero.mpr
  simpa using unit_neq_minus h₂ τ (v := 1) (by simp [quadraticNorm]) hb

lemma parameter_ne_zero (h₂ : (2 : K) ≠ 0) (τ : K →+* K) {β : K}
    (hb : quadraticNorm τ β = -1) : parameter β ≠ 0 := by
  have h4 : (4 : K) ≠ 0 := by
    have hh : (4 : K)=2*2 := by ring
    rw [hh]
    exact mul_ne_zero h₂ h₂
  exact div_ne_zero one_ne_zero (mul_ne_zero h4 (beta_ne_one_sq h₂ τ hb))

private def signed (a : K) (b : Bool) : K := if b then a else -a

private lemma signed_sq (a : K) (b : Bool) : (signed a b)^2=a^2 := by
  cases b <;> simp [signed]

private lemma signed_injective (h₂ : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    Function.Injective (signed a) := by
  intro b c he
  cases b <;> cases c <;> try rfl
  all_goals
    exfalso
    have hh : 2*a=0 := by
      simp [signed] at he
      first | linear_combination he | linear_combination -he
    exact (mul_ne_zero h₂ ha) hh

private def rowPoint (v a : Fin 2 → K) (i : Fin 2 × Bool) : K × K :=
  (v i.1,signed (a i.1) i.2)

private def colPoint (β : K) (u h : Fin 2 → K) (i : Fin 2 × Bool) : K × K :=
  (β*(u i.1+signed (h i.1) i.2),0)

private lemma colPoint_equation (β : K) (u h : Fin 2 → K)
    (hh : ∀ i, (h i)^2=(u i)^2-1) (i : Fin 2 × Bool) :
    (colPoint β u h i).1^2-2*β*u i.1*(colPoint β u h i).1+β^2=0 := by
  have he : (signed (h i.1) i.2)^2=(u i.1)^2-1 := by rw [signed_sq,hh]
  dsimp [colPoint]
  linear_combination β^2*he

private lemma colPoint_ne_zero {β : K} (hb : β ≠ 0) (u h : Fin 2 → K)
    (hh : ∀ i, (h i)^2=(u i)^2-1) (i : Fin 2 × Bool) :
    (colPoint β u h i).1 ≠ 0 := by
  intro hz
  have he := colPoint_equation β u h hh i
  simp only [hz,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,sub_zero,zero_add] at he
  exact pow_ne_zero 2 hb he

private lemma rowPoint_injective (h₂ : (2 : K) ≠ 0) (v a : Fin 2 → K)
    (hv : Function.Injective v) (ha : ∀ i, a i ≠ 0) : Function.Injective (rowPoint v a) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  have hij : i=j := hv (congrArg Prod.fst he)
  subst j
  have hbc : b=c := signed_injective h₂ (ha i) (congrArg Prod.snd he)
  cases hbc
  rfl

private lemma colPoint_injective (h₂ : (2 : K) ≠ 0) {β : K} (hb : β ≠ 0)
    (u h : Fin 2 → K) (hu : Function.Injective u) (hh0 : ∀ i, h i ≠ 0)
    (hh : ∀ i, (h i)^2=(u i)^2-1) : Function.Injective (colPoint β u h) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  have hw := congrArg Prod.fst he
  have hw0 := colPoint_ne_zero hb u h hh (i,b)
  have hi := colPoint_equation β u h hh (i,b)
  have hj := colPoint_equation β u h hh (j,c)
  rw [←hw] at hj
  have hz : 2*β*(colPoint β u h (i,b)).1*(u i-u j)=0 := by
    linear_combination hj-hi
  have hij : i=j := hu (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (mul_ne_zero h₂ hb) hw0)))
  subst j
  have hbc : b=c := by
    apply signed_injective h₂ (hh0 i)
    have ht := mul_left_cancel₀ hb hw
    exact add_left_cancel ht
  cases hbc
  rfl

/-- Every vertex of a two-by-two profile rectangle lifts to two distinct
vertices. The graph uses the original rational cross-ratio equation. -/
def rectangleCopy (h₂ : (2 : K) ≠ 0) (δ β : K) (hδ : δ ≠ 0) (hb : β ≠ 0)
    (S : Set K) (v u a h : Fin 2 → K)
    (hv : Function.Injective v) (hu : Function.Injective u)
    (hv0 : ∀ i, v i ≠ 0) (ha0 : ∀ i, a i ≠ 0) (hh0 : ∀ i, h i ≠ 0)
    (ha : ∀ i, (a i)^2=δ*((v i)^2-β^2))
    (hh : ∀ i, (h i)^2=(u i)^2-1)
    (hplus : ∀ i j, β*u j+v i ≠ 0) (hminus : ∀ i j, β*u j-v i ≠ 0)
    (hS : ∀ i j, (β*u j-v i)/(β*u j+v i) ∈ S) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph δ 0 S) := by
  have he (i j : Fin 2 × Bool) :
      (graph δ 0 S).Adj (.inl (rowPoint v a i)) (.inr (colPoint β u h j)) := by
    have hr := colPoint_equation β u h hh j
    have ha' : (signed (a i.1) i.2)^2=δ*((v i.1)^2-β^2) := by rw [signed_sq,ha]
    let w := (colPoint β u h j).1
    have hw : w ≠ 0 := colPoint_ne_zero hb u h hh j
    have hn : numerator δ (rowPoint v a i) (colPoint β u h j)=
        -2*δ*w*(β*u j.1-v i.1) := by
      dsimp [numerator,rowPoint]
      change (0-signed (a i.1) i.2)^2-δ*(w-v i.1)^2= _
      linear_combination ha'-δ*hr
    have hd : denominator δ (rowPoint v a i) (colPoint β u h j)=
        -2*δ*w*(β*u j.1+v i.1) := by
      dsimp [denominator]
      rw [hn]
      change -2*δ*w*(β*u j.1-v i.1)-4*δ*v i.1*w= _
      ring
    have hfac : -2*δ*w ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h₂) hδ) hw
    have hdn : denominator δ (rowPoint v a i) (colPoint β u h j) ≠ 0 := by
      rw [hd]
      exact mul_ne_zero hfac (hplus i.1 j.1)
    have ht0 : (β*u j.1-v i.1)/(β*u j.1+v i.1) ≠ 0 :=
      div_ne_zero (hminus i.1 j.1) (hplus i.1 j.1)
    have ht1 : (β*u j.1-v i.1)/(β*u j.1+v i.1) ≠ 1 := by
      intro ht
      have ht' := (div_eq_one_iff_eq (hplus i.1 j.1)).mp ht
      have hz : 2*v i.1=0 := by linear_combination -ht'
      exact (mul_ne_zero h₂ (hv0 i.1)) hz
    refine ⟨hv0 i.1,hw,hdn,(β*u j.1-v i.1)/(β*u j.1+v i.1),hS i.1 j.1,
      ht0,?_,?_,?_⟩
    · simpa only [level,zero_mul,add_zero] using ht0
    · simpa only [level,zero_mul,add_zero] using ht1
    · simp only [level,zero_mul,add_zero]
      rw [hn,hd,mul_div_mul_left _ _ hfac]
  let e : Fin 4 ≃ Fin 2 × Bool :=
    (finCongr (by simp : 4=Fintype.card (Fin 2 × Bool))).trans (Fintype.equivFin _).symm
  let L : Fin 4 ↪ K × K := e.toEmbedding.trans ⟨rowPoint v a,rowPoint_injective h₂ v a hv ha0⟩
  let R : Fin 4 ↪ K × K := e.toEmbedding.trans ⟨colPoint β u h,colPoint_injective h₂ hb u h hu hh0 hh⟩
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro p q hpq
  cases p with
  | inl i =>
    cases q with
    | inl j => simp at hpq
    | inr j => exact he (e i) (e j)
  | inr j =>
    cases q with
    | inr i => simp at hpq
    | inl i => exact he (e i) (e j)

lemma norm_mul (τ : K →+* K) (x y : K) :
    quadraticNorm τ (x*y)=quadraticNorm τ x*quadraticNorm τ y := by
  dsimp [quadraticNorm]
  rw [map_mul]
  ring

lemma norm_div (τ : K →+* K) (x y : K) :
    quadraticNorm τ (x/y)=quadraticNorm τ x/quadraticNorm τ y := by
  simp only [quadraticNorm,map_div₀]
  rw [div_mul_div_comm]

lemma minus_not_one (h₂ : (2 : K) ≠ 0) (τ : K →+* K) {x : K}
    (hx : quadraticNorm τ x = -1) : x ≠ 1 ∧ x ≠ -1 := by
  constructor <;> intro he
  · rw [he] at hx
    simp only [quadraticNorm,map_one,mul_one] at hx
    apply h₂
    linear_combination hx
  · rw [he] at hx
    simp only [quadraticNorm,map_neg,map_one,neg_mul_neg,mul_one] at hx
    apply h₂
    linear_combination hx

lemma pull_norm (h₂ : (2 : K) ≠ 0) (τ : K →+* K) {β x : K}
    (hb : quadraticNorm τ β = -1) (hx : quadraticNorm τ x = -1) :
    quadraticNorm τ (pull β x)=1 := by
  have hb0 := norm_ne_zero τ hb (neg_ne_zero.mpr one_ne_zero)
  have hx0 := norm_ne_zero τ hx (neg_ne_zero.mpr one_ne_zero)
  have hx₁ := (minus_not_one h₂ τ hx).1
  have hx₂ := (minus_not_one h₂ τ hx).2
  have h1x : 1-x ≠ 0 := sub_ne_zero.mpr hx₁.symm
  have hxp : x+1 ≠ 0 := by
    intro h
    apply hx₂
    linear_combination h
  simp only [quadraticNorm,pull,map_div₀,map_add,map_mul,map_sub,map_one,
    conjugate_eq_div τ hb hb0,conjugate_eq_div τ hx hx0]
  field_simp [hb0,hx0,h1x,hxp,hx₁,hx₂]
  ring

lemma cayley_pull (h₂ : (2 : K) ≠ 0) {β x : K} (hb : β ≠ 0) (hx : x ≠ 1) :
    cayley (β*pull β x)=x := by
  have h1x : 1-x ≠ 0 := sub_ne_zero.mpr hx.symm
  have he : β*pull β x=(1+x)/(1-x) := by dsimp [pull]; field_simp
  have hp : (1+x)/(1-x)+1=2/(1-x) := by field_simp; ring
  dsimp [cayley]
  rw [he,hp]
  field_simp
  ring

lemma pull_injective (h₂ : (2 : K) ≠ 0) {β : K} (hb : β ≠ 0) {x y : K}
    (hx : x ≠ 1) (hy : y ≠ 1) (he : pull β x=pull β y) : x=y := by
  have hh := congrArg (fun t => cayley (β*t)) he
  simpa only [cayley_pull h₂ hb hx,cayley_pull h₂ hb hy] using hh

lemma profile_plus_minus (h₂ : (2 : K) ≠ 0) (τ : K →+* K) {β u v : K}
    (hb : quadraticNorm τ β = -1) (hu : quadraticNorm τ u=1)
    (hv : quadraticNorm τ v=1) : β*u+v ≠ 0 ∧ β*u-v ≠ 0 := by
  have hbu : quadraticNorm τ (β*u) = -1 := by rw [norm_mul,hb,hu,mul_one]
  constructor
  · intro he
    have hz : β*u = -v := by linear_combination he
    rw [hz] at hbu
    have hn : quadraticNorm τ (-v)=1 := by simpa [quadraticNorm] using hv
    rw [hn] at hbu
    apply h₂
    linear_combination hbu
  · intro he
    rw [sub_eq_zero.mp he,hv] at hbu
    apply h₂
    linear_combination hbu

lemma ratio_cayley {β u v : K} (hv : v ≠ 0) (hp : β*u+v ≠ 0) :
    (β*u-v)/(β*u+v)=cayley (β*(u/v)) := by
  dsimp [cayley]
  field_simp

variable [Fintype K]

lemma oddChar {q : ℕ} (hcard : Fintype.card K=q^2) (hmod : q%4=3) : ringChar K ≠ 2 := by
  intro he
  have hh := FiniteField.even_card_of_char_two he
  rw [hcard,Nat.pow_mod] at hh
  have hq : q%2=1 := by omega
  norm_num [hq] at hh

/-- Euler's criterion for the two twists that arise in the profiles. -/
lemma twisted_euler {q : ℕ} (hcard : Fintype.card K=q^2) (hmod : q%4=3)
    (τ : K →+* K) (hτ : ∀ x, τ x=x^q) {x c ε : K}
    (hx : x ≠ 0) (hε : ε^2=1) (he : τ x=ε*x/c^2) :
    x^(Fintype.card K/2)=1/c^(q+1) := by
  have hq : 1 ≤ q := by omega
  have hodd : q=2*(q/2)+1 := by omega
  have heven : (q+1)/2=2*((q+1)/4) := by omega
  have htwice : 2*((q+1)/2)=q+1 := by omega
  have hhalf : Fintype.card K/2=(q-1)*((q+1)/2) := by
    have hh : q^2=2*((q-1)*((q+1)/2))+1 := by
      have hh' : (q-1)*((q+1)/2)*2=(q-1)*(q+1) := by nlinarith [htwice]
      have hsub : q-1+1=q := by omega
      nlinarith
    rw [hcard]
    omega
  have hp : x^(q-1)=ε/c^2 := by
    apply mul_right_cancel₀ hx
    calc
      _ = x^q := by rw [←pow_succ]; congr 1; omega
      _ = ε*x/c^2 := by rw [←hτ x]; exact he
      _ = _ := by ring
  rw [hhalf,pow_mul,hp,div_pow,←pow_mul,htwice]
  have hep : ε^((q+1)/2)=1 := by rw [heven,pow_mul,hε,one_pow]
  rw [hep]

lemma row_square {q : ℕ} (hcard : Fintype.card K=q^2) (hmod : q%4=3)
    (τ : K →+* K) (hτ : ∀ x, τ x=x^q) {β v : K}
    (hb : quadraticNorm τ β = -1) (hv : quadraticNorm τ v=1) :
    IsSquare (parameter β*(v^2-β^2)) ∧ parameter β*(v^2-β^2) ≠ 0 := by
  have hc := oddChar hcard hmod
  have h₂ := Ring.two_ne_zero hc
  have hb0 := norm_ne_zero τ hb (neg_ne_zero.mpr one_ne_zero)
  have hv0 := norm_ne_zero τ hv one_ne_zero
  have hden := beta_ne_one_sq h₂ τ hb
  have h4 : (4 : K) ≠ 0 := by
    have hh : (4 : K)=2*2 := by ring
    rw [hh]
    exact mul_ne_zero h₂ h₂
  have hden' : β^2-1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hden))
  have hz : parameter β*(v^2-β^2) ≠ 0 :=
    mul_ne_zero (parameter_ne_zero h₂ τ hb) (sub_ne_zero.mpr (unit_neq_minus h₂ τ hv hb))
  refine ⟨(FiniteField.isSquare_iff hc hz).mpr ?_,hz⟩
  have he : τ (parameter β*(v^2-β^2))=1*(parameter β*(v^2-β^2))/v^2 := by
    simp only [parameter,map_mul,map_div₀,map_one,map_ofNat,map_sub,map_pow,
      conjugate_eq_div τ hb hb0,conjugate_eq_div τ hv hv0]
    field_simp [hb0,hv0,hden,hden',h4]
    ring
  rw [twisted_euler hcard hmod τ hτ hz (by simp : (1 : K)^2=1) he]
  rw [←norm_eq_pow q τ hτ,hv]
  simp

lemma column_square {q : ℕ} (hcard : Fintype.card K=q^2) (hmod : q%4=3)
    (τ : K →+* K) (hτ : ∀ x, τ x=x^q) {u : K}
    (hu : quadraticNorm τ u=1) (hu₁ : u ≠ 1) (hu₂ : u ≠ -1) :
    IsSquare (u^2-1) ∧ u^2-1 ≠ 0 := by
  have hu0 := norm_ne_zero τ hu one_ne_zero
  have hz : u^2-1 ≠ 0 := by simpa [sub_eq_zero,sq_eq_one_iff] using And.intro hu₁ hu₂
  refine ⟨(FiniteField.isSquare_iff (oddChar hcard hmod) hz).mpr ?_,hz⟩
  have he : τ (u^2-1)=(-1)*(u^2-1)/u^2 := by
    simp only [map_sub,map_pow,map_one,conjugate_eq_div τ hu hu0]
    field_simp
    ring
  rw [twisted_euler hcard hmod τ hτ hz (by ring : (-1 : K)^2=1) he,
    ←norm_eq_pow q τ hτ,hu]
  simp

lemma parameter_nonsquare {q : ℕ} (hcard : Fintype.card K=q^2) (hmod : q%4=3)
    (τ : K →+* K) (hτ : ∀ x, τ x=x^q) {β : K}
    (hb : quadraticNorm τ β = -1) : ¬ IsSquare (parameter β) := by
  have hc := oddChar hcard hmod
  have h₂ := Ring.two_ne_zero hc
  have hb0 := norm_ne_zero τ hb (neg_ne_zero.mpr one_ne_zero)
  have hden := beta_ne_one_sq h₂ τ hb
  have he : τ (1-β^2)=(-1)*(1-β^2)/β^2 := by
    simp only [map_sub,map_pow,map_one,conjugate_eq_div τ hb hb0]
    field_simp
    ring
  have hp := twisted_euler hcard hmod τ hτ hden (by ring : (-1 : K)^2=1) he
  rw [←norm_eq_pow q τ hτ,hb] at hp
  have h4 : (4 : K) ≠ 0 := by
    have hh : (4 : K)=2*2 := by ring
    rw [hh]
    exact mul_ne_zero h₂ h₂
  have h4p : (4 : K)^(Fintype.card K/2)=1 :=
    (FiniteField.isSquare_iff hc h4).mp ⟨2,by ring⟩
  intro hs
  have hh := (FiniteField.isSquare_iff hc (parameter_ne_zero h₂ τ hb)).mp hs
  simp only [parameter,div_pow,one_pow,mul_pow,h4p,hp] at hh
  have hh' : (-1 : K)=1 := by simpa using hh
  exact Ring.neg_one_ne_one_of_char_ne_two hc hh'

def circle (τ : K →+* K) : Finset K := Finset.univ.filter (quadraticNorm τ · = 1)

@[simp] lemma mem_circle (τ : K →+* K) (x : K) : x ∈ circle τ ↔ quadraticNorm τ x=1 := by
  simp [circle]

lemma card_circle_le (q : ℕ) (τ : K →+* K) (hτ : ∀ x, τ x=x^q) :
    (circle τ).card ≤ q+1 := by
  have hp : (X^(q+1)-C (1 : K) : K[X]) ≠ 0 := X_pow_sub_C_ne_zero (by omega) 1
  have hh : (circle τ).val ⊆ (X^(q+1)-C (1 : K) : K[X]).roots := by
    intro x hx
    apply (Polynomial.mem_roots hp).mpr
    have hx' := (mem_circle τ x).mp hx
    simpa [Polynomial.IsRoot, norm_eq_pow q τ hτ, sub_eq_zero] using hx'
  simpa only [Polynomial.natDegree_X_pow_sub_C] using card_le_degree_of_subset_roots hh

structure TorusRectangle (τ : K →+* K) (A : Finset K) where
  v : Fin 2 → K
  u : Fin 2 → K
  v_injective : Function.Injective v
  u_injective : Function.Injective u
  v_norm : ∀ i, quadraticNorm τ (v i) = 1
  u_norm : ∀ i, quadraticNorm τ (u i) = 1
  u_ne_one : ∀ i, u i ≠ 1
  u_ne_neg_one : ∀ i, u i ≠ -1
  quotient_mem : ∀ i j, u j / v i ∈ A

lemma rectangle_exists (q : ℕ) (hq : 12 ≤ q) (τ : K →+* K) (hτ : ∀ x, τ x=x^q)
    (A : Finset K) (hA : ∀ x ∈ A, quadraticNorm τ x=1)
    (hsize : q < A.card*(A.card-1)) : Nonempty (TorusRectangle τ A) := by
  have hA5 : 4 < A.card := by
    by_contra hh
    have hh' : A.card ≤ 4 := by omega
    have ht : A.card*(A.card-1) ≤ 4*3 := Nat.mul_le_mul hh' (by omega)
    omega
  have hcircle1 : (1 : K) ∈ circle τ := by simp [quadraticNorm]
  have hbound : ((circle τ).erase 1).card ≤ q := by
    rw [Finset.card_erase_of_mem hcircle1]
    have := card_circle_le q τ hτ
    omega
  have hlt : ((circle τ).erase 1).card < A.offDiag.card := by
    rw [Finset.offDiag_card]
    have hh : A.card*(A.card-1)=A.card*A.card-A.card := by rw [Nat.mul_sub_left_distrib,mul_one]
    omega
  have hmap : Set.MapsTo (fun p : K × K => p.1/p.2) (↑A.offDiag) (↑((circle τ).erase 1)) := by
    intro p hp
    obtain ⟨ha,hb,hab⟩ := Finset.mem_offDiag.mp hp
    have hb0 := norm_ne_zero τ (hA _ hb) one_ne_zero
    apply Finset.mem_erase.mpr
    refine ⟨?_,?_⟩
    · exact fun he => hab ((div_eq_one_iff_eq hb0).mp he)
    · simp only [mem_circle,norm_div,hA _ ha,hA _ hb,div_self one_ne_zero]
  obtain ⟨⟨a,b⟩,hab,⟨c,d⟩,hcd,hne,he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmap
  obtain ⟨ha,hb,hab⟩ := Finset.mem_offDiag.mp hab
  obtain ⟨hc,hd,hcd⟩ := Finset.mem_offDiag.mp hcd
  have ha0 := norm_ne_zero τ (hA _ ha) one_ne_zero
  have hb0 := norm_ne_zero τ (hA _ hb) one_ne_zero
  have hc0 := norm_ne_zero τ (hA _ hc) one_ne_zero
  have hd0 := norm_ne_zero τ (hA _ hd) one_ne_zero
  change a/b=c/d at he
  have hcross : a*d=c*b := (div_eq_div_iff hb0 hd0).mp he
  have hac : a ≠ c := by
    intro hh
    have hbd : d=b := mul_left_cancel₀ ha0 (by simpa [←hh] using hcross)
    exact hne (by simp [hh,hbd])
  let bad : Finset K := {a⁻¹,-a⁻¹,b⁻¹,-b⁻¹}
  have hbad : bad.card < A.card := lt_of_le_of_lt Finset.card_le_four hA5
  obtain ⟨z,hz,hzbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  have hz0 := norm_ne_zero τ (hA _ hz) one_ne_zero
  have havoid : z*a ≠ 1 ∧ z*a ≠ -1 ∧ z*b ≠ 1 ∧ z*b ≠ -1 := by
    have hz' : z ≠ a⁻¹ ∧ z ≠ -a⁻¹ ∧ z ≠ b⁻¹ ∧ z ≠ -b⁻¹ := by simpa [bad] using hzbad
    refine ⟨?_,?_,?_,?_⟩
    · intro hh; apply hz'.1; apply mul_right_cancel₀ ha0; simpa [ha0] using hh
    · intro hh; apply hz'.2.1; apply mul_right_cancel₀ ha0; simpa [ha0] using hh
    · intro hh; apply hz'.2.2.1; apply mul_right_cancel₀ hb0; simpa [hb0] using hh
    · intro hh; apply hz'.2.2.2; apply mul_right_cancel₀ hb0; simpa [hb0] using hh
  let v : Fin 2 → K := ![z,z*(a/c)]
  let u : Fin 2 → K := ![z*a,z*b]
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      exfalso
      apply hac
      have hh : a/c=1 := by
        apply mul_left_cancel₀ hz0
        first | simpa [v] using hij.symm | simpa [v] using hij
      exact (div_eq_one_iff_eq hc0).mp hh
  have hu : Function.Injective u := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      exfalso
      apply hab
      apply mul_left_cancel₀ hz0
      first | simpa [u] using hij | simpa [u] using hij.symm
  refine ⟨⟨v,u,hv,hu,?_,?_,?_,?_,?_⟩⟩
  · intro i; fin_cases i <;> simp [v,norm_mul,norm_div,hA _ hz,hA _ ha,hA _ hc]
  · intro j; fin_cases j <;> simp [u,norm_mul,hA _ hz,hA _ ha,hA _ hb]
  · intro j; fin_cases j
    · exact havoid.1
    · exact havoid.2.2.1
  · intro j; fin_cases j
    · exact havoid.2.1
    · exact havoid.2.2.2
  · intro i j; fin_cases i <;> fin_cases j
    · simpa [u,v,hz0] using ha
    · simpa [u,v,hz0] using hb
    · have hh : z*a/(z*(a/c))=c := by field_simp
      simpa [u,v,hh] using hc
    · have hh : z*b/(z*(a/c))=d := by field_simp; linear_combination -hcross
      simpa [u,v,hh] using hd

lemma dense_circle_copy {q : ℕ} (hcard : Fintype.card K=q^2) (hmod : q%4=3)
    (hq : 12 ≤ q) (τ : K →+* K) (hτ : ∀ x, τ x=x^q) (S : Finset K)
    (hS : ∀ x ∈ S, quadraticNorm τ x = -1) (hsize : q < S.card*(S.card-1))
    {β : K} (hb : quadraticNorm τ β = -1) :
    Nonempty (Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (parameter β) 0 (↑S))) := by
  have h₂ := Ring.two_ne_zero (oddChar hcard hmod)
  have hb0 := norm_ne_zero τ hb (neg_ne_zero.mpr one_ne_zero)
  let A := S.image (pull β)
  have hA : ∀ x ∈ A, quadraticNorm τ x=1 := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    exact pull_norm h₂ τ hb (hS t ht)
  have hcardA : A.card=S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    exact pull_injective h₂ hb0 (minus_not_one h₂ τ (hS x hx)).1
      (minus_not_one h₂ τ (hS y hy)).1 he
  obtain ⟨R⟩ := rectangle_exists q hq τ hτ A hA (by simpa [hcardA] using hsize)
  choose a ha using fun i => (row_square hcard hmod τ hτ hb (R.v_norm i)).1
  choose h hh using fun i => (column_square hcard hmod τ hτ (R.u_norm i)
    (R.u_ne_one i) (R.u_ne_neg_one i)).1
  have ha' (i) : (a i)^2=parameter β*((R.v i)^2-β^2) := by rw [ha i]; ring
  have hh' (i) : (h i)^2=(R.u i)^2-1 := by rw [hh i]; ring
  have ha0 (i) : a i ≠ 0 := by
    intro hz
    have he := ha' i
    rw [hz,zero_pow (by decide : 2 ≠ 0)] at he
    exact (row_square hcard hmod τ hτ hb (R.v_norm i)).2 he.symm
  have hh0 (i) : h i ≠ 0 := by
    intro hz
    have he := hh' i
    rw [hz,zero_pow (by decide : 2 ≠ 0)] at he
    exact (column_square hcard hmod τ hτ (R.u_norm i) (R.u_ne_one i) (R.u_ne_neg_one i)).2 he.symm
  have hv0 (i) := norm_ne_zero τ (R.v_norm i) one_ne_zero
  have hp (i j) := profile_plus_minus h₂ τ hb (R.u_norm j) (R.v_norm i)
  refine ⟨rectangleCopy h₂ (parameter β) β (parameter_ne_zero h₂ τ hb) hb0 (↑S)
    R.v R.u a h R.v_injective R.u_injective hv0 ha0 hh0 ha' hh'
    (fun i j => (hp i j).1) (fun i j => (hp i j).2) ?_⟩
  intro i j
  obtain ⟨t,ht,he⟩ := Finset.mem_image.mp (R.quotient_mem i j)
  rw [ratio_cayley (hv0 i) (hp i j).1,←he,cayley_pull h₂ hb0 (minus_not_one h₂ τ (hS t ht)).1]
  exact ht

lemma square_ratio_odd (hc : ringChar K ≠ 2) {a b : K} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a/b) := by
  have ha0 : a ≠ 0 := by intro hz; subst a; exact ha IsSquare.zero
  have hb0 : b ≠ 0 := by intro hz; subst b; exact hb IsSquare.zero
  have hea : a^(Fintype.card K/2) = -1 := (FiniteField.pow_dichotomy hc ha0).resolve_left
    (fun h => ha ((FiniteField.isSquare_iff hc ha0).mpr h))
  have heb : b^(Fintype.card K/2) = -1 := (FiniteField.pow_dichotomy hc hb0).resolve_left
    (fun h => hb ((FiniteField.isSquare_iff hc hb0).mpr h))
  apply (FiniteField.isSquare_iff hc (div_ne_zero ha0 hb0)).mpr
  rw [div_pow,hea,heb]
  simp

/-- A uniform obstruction, valid for every subset of the norm-minus-one circle
and every nonsquare defining the upper half-plane. Freeness forces a Sidon-scale
bound on the number of fused levels, rather than the linear number needed for
the proposed extremal construction. -/
theorem norm_circle_obstruction {q : ℕ} (hcard : Fintype.card K=q^2) (hmod : q%4=3)
    (hq : 12 ≤ q) (τ : K →+* K) (hτ : ∀ x, τ x=x^q) (S : Finset K)
    (hS : ∀ x ∈ S, quadraticNorm τ x = -1) (δ : K) (hδ : ¬ IsSquare δ)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph δ 0 (↑S))) :
    S.card*(S.card-1) ≤ q := by
  by_contra hh
  have hsize : q < S.card*(S.card-1) := by omega
  have hpos : 0 < S.card := by
    by_contra hz
    have he : S.card=0 := by omega
    simp [he] at hsize
  obtain ⟨β,hβ⟩ := Finset.card_pos.mp hpos
  have hb := hS β hβ
  have h₂ := Ring.two_ne_zero (oddChar hcard hmod)
  have hp0 := parameter_ne_zero h₂ τ hb
  have hδ0 : δ ≠ 0 := by intro hz; subst δ; exact hδ IsSquare.zero
  obtain ⟨d,hd⟩ := square_ratio_odd (oddChar hcard hmod) hδ
    (parameter_nonsquare hcard hmod τ hτ hb)
  have hd0 : d ≠ 0 := by
    intro hz
    have he : δ/parameter β=0 := by simpa [hz] using hd
    exact div_ne_zero hδ0 hp0 he
  have hscale : d^2*parameter β=δ := by
    calc
      _ = (δ/parameter β)*parameter β := by rw [hd]; ring
      _ = _ := div_mul_cancel₀ _ hp0
  obtain ⟨C⟩ := dense_circle_copy hcard hmod hq τ hτ S hS hsize hb
  rw [←hscale] at hfree
  exact hfree ⟨(scaleCopy (parameter β) 0 d hd0 (↑S)).comp C⟩

end Erdos714UpperHalfPlaneCircle

#print axioms Erdos714UpperHalfPlaneCircle.rectangle_exists
#print axioms Erdos714UpperHalfPlaneCircle.dense_circle_copy
#print axioms Erdos714UpperHalfPlaneCircle.norm_circle_obstruction
