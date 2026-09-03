import Submission.RationalGeometricBudget

/-!
# A finite scalar certificate for a proposed no-3 exceptional-box sieve

The finite table bounds the geometric hinge cost through prime53, uniformly
in all exponent caps. It is not itself a covering-system nonexistence proof.
-/
namespace Erdos7ExceptionalScalar
open scoped BigOperators
open Erdos7RationalGeometricBudget
open Erdos7CompressionSieve Erdos7Distortion
open Erdos7BinarySieve (expect expect_add expect_le)
open Erdos7ExponentLaw
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

structure State where
  values : Fin 11 → ℚ
  slope : ℚ
  intercept : ℚ

def State.eval (s : State) (x : ℕ) : ℚ :=
  if h : x<11 then s.values ⟨x,h⟩ else s.slope*x+s.intercept

def State.Good (s : State) : Prop :=
  0 ≤ s.slope ∧
  (∀ i : Fin 10, s.values i.castSucc ≤ s.values i.succ) ∧
  s.values 10 ≤ s.slope*11+s.intercept

lemma State.eval_affine (s : State) (x : ℕ) (hx : 11 ≤ x) :
    s.eval x=s.slope*x+s.intercept := by simp [State.eval,not_lt.mpr hx]

lemma State.monotone (s : State) (hs : s.Good) : Monotone s.eval := by
  apply monotone_nat_of_le_succ
  intro x
  by_cases hlt : x<10
  · simpa only [State.eval,dif_pos (show x<11 by omega),
      dif_pos (show x+1<11 by omega)] using hs.2.1 ⟨x,hlt⟩
  · by_cases heq : x=10
    · subst x
      simpa [State.eval] using hs.2.2
    · have hx : 11 ≤ x := by omega
      rw [s.eval_affine x hx,s.eval_affine (x+1) (by omega)]
      push_cast
      nlinarith [hs.1]

def primes : Fin 14 → ℕ := ![5,7,11,13,17,19,23,29,31,37,41,43,47,53]

def states : Fin 15 → State := ![
  ⟨![0/1000000000000,278462010459/1000000000000,1504630550873/1000000000000,3125565098732/1000000000000,4912955695725/1000000000000,6804214721291/1000000000000,8741557115432/1000000000000,10709202276785/1000000000000,12687152084602/1000000000000,14685084612087/1000000000000,16694489010555/1000000000000], 2019133101790/1000000000000, (-7)/2⟩,
  ⟨![0/1000000000000,42760953474/1000000000000,513176661919/1000000000000,1362443974556/1000000000000,2387612014743/1000000000000,3528402210012/1000000000000,4720762662058/1000000000000,5952403961887/1000000000000,7197784790334/1000000000000,8469809245006/1000000000000,9757129527655/1000000000000], 1300291887078/1000000000000, (-13)/4⟩,
  ⟨![0/1000000000000,9798727100/1000000000000,119936640101/1000000000000,538430722532/1000000000000,1135773099166/1000000000000,1854641755076/1000000000000,2627891960646/1000000000000,3448007170272/1000000000000,4284848762564/1000000000000,5154126073740/1000000000000,6042024392886/1000000000000], 903689837581/1000000000000, (-3)/1⟩,
  ⟨![0/1000000000000,2659167714/1000000000000,44989402079/1000000000000,232634392746/1000000000000,599209876573/1000000000000,1089463868440/1000000000000,1635143983690/1000000000000,2233023404360/1000000000000,2849773615729/1000000000000,3503117971481/1000000000000,4177470643918/1000000000000], 692168744516/1000000000000, (-11)/4⟩,
  ⟨![0/1000000000000,691860061/1000000000000,15294852149/1000000000000,74697829657/1000000000000,265632556331/1000000000000,580921479350/1000000000000,952007461061/1000000000000,1380217541795/1000000000000,1829305944154/1000000000000,2318881484978/1000000000000,2831700269795/1000000000000], 532530183712/1000000000000, (-5)/2⟩,
  ⟨![0/1000000000000,197297495/1000000000000,5037013460/1000000000000,31391797201/1000000000000,116290042650/1000000000000,308337123660/1000000000000,556073034230/1000000000000,864950829849/1000000000000,1196363956746/1000000000000,1571477487065/1000000000000,1971678963281/1000000000000], 421477271848/1000000000000, (-9)/4⟩,
  ⟨![0/1000000000000,51964393/1000000000000,1645586640/1000000000000,11593931266/1000000000000,39665676190/1000000000000,128082419648/1000000000000,271772509477/1000000000000,480417045565/1000000000000,713183908092/1000000000000,992728667240/1000000000000,1299128129038/1000000000000], 329173552896/1000000000000, (-2)/1⟩,
  ⟨![0/1000000000000,13676821/1000000000000,513856502/1000000000000,4623073855/1000000000000,16699888271/1000000000000,48061441511/1000000000000,110060364040/1000000000000,240317001435/1000000000000,396082305869/1000000000000,601313891787/1000000000000,834943554071/1000000000000], 257712609191/1000000000000, (-7)/4⟩,
  ⟨![0/1000000000000,3560560/1000000000000,169949246/1000000000000,1977263094/1000000000000,6371368553/1000000000000,23922220837/1000000000000,51704397773/1000000000000,122471373076/1000000000000,219896054472/1000000000000,369015228231/1000000000000,547811670985/1000000000000], 203964207088/1000000000000, (-3)/2⟩,
  ⟨![0/1000000000000,661133/1000000000000,49478563/1000000000000,708508983/1000000000000,2179299083/1000000000000,10546589497/1000000000000,26531103838/1000000000000,43542988514/1000000000000,88332650967/1000000000000,186988843277/1000000000000,316569248658/1000000000000], 155805638804/1000000000000, (-5)/4⟩,
  ⟨![0/1000000000000,75052/1000000000000,11543022/1000000000000,210655240/1000000000000,797663586/1000000000000,4096213411/1000000000000,12642473017/1000000000000,21952291042/1000000000000,31262109067/1000000000000,89134644861/1000000000000,179012659917/1000000000000], 117020214683/1000000000000, (-1)/1⟩,
  ⟨![0/1000000000000,711/1000000000000,1450025/1000000000000,37153376/1000000000000,213170077/1000000000000,1049758252/1000000000000,4847296860/1000000000000,9153602481/1000000000000,13459908102/1000000000000,35623356579/1000000000000,90798745930/1000000000000], 83171117268/1000000000000, (-3)/4⟩,
  ⟨![0/1000000000000,1/1000000000000,216/1000000000000,481942/1000000000000,22946945/1000000000000,64050362/1000000000000,1106302925/1000000000000,2398842774/1000000000000,3691382624/1000000000000,4983922473/1000000000000,28015592757/1000000000000], 51865593647/1000000000000, (-1)/2⟩,
  ⟨![0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000], 24038461539/1000000000000, (-1)/4⟩,
  ⟨![0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000,0/1000000000000], 0/1000000000000, (0)/1⟩]

def loss (p x : ℕ) : ℚ := max 0 ((5/4 : ℚ)*x/(p-1)-(1/4 : ℚ))

def Row (p : ℕ) (s t : State) : Prop :=
  s.Good ∧ t.Good ∧
  (∀ x : Fin 12, loss p x.val + budget p (5/4) t.eval t.slope 10 x.val ≤ s.eval x.val) ∧
  (5/4 : ℚ)/(p-1)+(1+(5/4 : ℚ)/(p-1))*t.slope ≤ s.slope

/-- Only finite rational arithmetic is used in checking the supersolution. -/
lemma certificate :
    (∀ i : Fin 14, 5 ≤ primes i ∧ primes i ≤ 53 ∧
      Row (primes i) (states i.castSucc) (states i.succ)) ∧
    (∀ x : Fin 11, (states 14).values x=0) ∧
    (states 14).slope=0 ∧ (states 14).intercept=0 := by
  unfold Row State.Good
  decide +kernel

lemma loss_affine (p x : ℕ) (hp : 5 ≤ p) (hp53 : p ≤ 53) (hx : 11 ≤ x) :
    loss p x=(5/4 : ℚ)/(p-1)*x-1/4 := by
  have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have hpQ53 : (p : ℚ) ≤ 53 := by exact_mod_cast hp53
  have hxQ : (11 : ℚ) ≤ x := by exact_mod_cast hx
  have hp1 : (0 : ℚ)<p-1 := by linarith
  unfold loss
  rw [max_eq_right]
  · ring
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hp1).mpr
    nlinarith

lemma row_budget (p : ℕ) (hp : 5 ≤ p) (hp53 : p ≤ 53)
    (s t : State) (hr : Row p s t) (x : ℕ) :
    loss p x+budget p (5/4) t.eval t.slope 10 x ≤ s.eval x := by
  by_cases hx : x<12
  · exact hr.2.2.1 ⟨x,hx⟩
  · have h11 : 11 ≤ x := by omega
    have hpQ : (1 : ℚ)<p := by exact_mod_cast (show 1<p by omega)
    have hrow := hr.2.2.1 (11 : Fin 12)
    change loss p 11+budget p (5/4) t.eval t.slope 10 11 ≤ s.eval 11 at hrow
    rw [loss_affine p 11 hp hp53 (by omega),
      budget_affine p (5/4) hpQ t.eval 11 t.slope t.intercept
        (fun x hx => t.eval_affine x hx) 10 11 (by omega),
      s.eval_affine 11 (by omega)] at hrow
    rw [loss_affine p x hp hp53 h11,
      budget_affine p (5/4) hpQ t.eval 11 t.slope t.intercept
        (fun x hx => t.eval_affine x hx) 10 x h11,
      s.eval_affine x h11]
    have hxQ : (11 : ℚ) ≤ x := by exact_mod_cast h11
    nlinarith [hr.2.2.2]

/-- A certified row bounds every finite exponent cap, not just the ten explicit
geometric terms used in checking it. -/
theorem row_op (i : Fin 14) (E x : ℕ) :
    loss (primes i) x + op (primes i) (5/4) (states i.succ).eval E x ≤
      (states i.castSucc).eval x := by
  obtain ⟨hp,hp53,hr⟩ := certificate.1 i
  have hh := row_budget (primes i) hp hp53 _ _ hr x
  apply (add_le_add (le_refl (loss (primes i) x)) ?_).trans hh
  by_cases hx : x=0
  · subst x
    rw [op_zero,budget_zero]
  · apply op_le_budget (primes i) (5/4) (by exact_mod_cast (show 1<primes i by omega))
      (by norm_num) _ (State.monotone _ hr.2.1) 11 _ _ hr.2.1.1
      (fun x hx => State.eval_affine _ x hx) 10 E x
    omega

lemma terminal_eval (x : ℕ) : (states 14).eval x=0 := by
  unfold State.eval
  split
  · exact certificate.2.1 _
  · rw [certificate.2.2.1,certificate.2.2.2]
    ring

/-- The certified prefix saving is strictly greater than one quarter. -/
lemma saving_certificate :
    (states 0).eval 1 + (1/4 : ℚ) <
      Erdos7No23Sieve.budgetCost (Finset.univ.image primes) := by
  decide +kernel

def tails (E : Fin 14 → ℕ) (i : Fin 14) := powerTail (primes i) (5/4) (E i)

noncomputable def lossAt (E : Fin 14 → ℕ) (t : ℕ) : ℚ :=
  if h : t<14 then expect (prefixLaw E (tails E) t) (loss (primes ⟨t,h⟩)) else 0

lemma law_nonneg (E : Fin 14 → ℕ) (t x : ℕ) : 0 ≤ prefixLaw E (tails E) t x := by
  apply prefix_nonneg E (tails E)
  · intro i
    have hp := (certificate.1 i).1
    exact powerTail_zero_le_one (primes i) (by omega) (5/4)
      (by
        have hpQ : (5 : ℚ) ≤ primes i := by exact_mod_cast hp
        linarith) (E i)
  · intro i g hg
    exact powerTail_decreasing (primes i) (by have := (certificate.1 i).1; omega)
      (5/4) (by norm_num) (E i) g

lemma prefix_potential (E : Fin 14 → ℕ) (t : ℕ) (ht : t ≤ 14) :
    (∑ j ∈ Finset.range t, lossAt E j) +
      expect (prefixLaw E (tails E) t) (states ⟨t,by omega⟩).eval ≤ (states 0).eval 1 := by
  induction t with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,zero_add,prefixLaw,expect_initial]; exact le_rfl
  | succ t ih =>
    have ht14 : t<14 := by omega
    let i : Fin 14 := ⟨t,ht14⟩
    have hstep := expect_le (prefixLaw E (tails E) t) (law_nonneg E t)
      (fun x => loss (primes i) x + op (primes i) (5/4) (states i.succ).eval (E i) x)
      (states i.castSucc).eval (row_op i (E i))
    rw [expect_add,expect_op] at hstep
    have hrec : prefixLaw E (tails E) (t+1) =
        step (E i) (tails E i) (prefixLaw E (tails E) t) := by
      simp only [prefixLaw,ht14,dif_pos,i]
    rw [Finset.sum_range_succ,hrec]
    have hi := ih (by omega)
    have he : lossAt E t=expect (prefixLaw E (tails E) t) (loss (primes i)) := by
      simp only [lossAt,ht14,dif_pos,i]
    rw [he]
    change (∑ j ∈ Finset.range t, lossAt E j) +
      expect (prefixLaw E (tails E) t) (loss (primes i)) +
      expect (step (E i) (tails E i) (prefixLaw E (tails E) t)) (states i.succ).eval ≤ _
    change (∑ j ∈ Finset.range t, lossAt E j) +
      expect (prefixLaw E (tails E) t) (states i.castSucc).eval ≤ _ at hi
    change expect (prefixLaw E (tails E) t) (loss (primes i)) +
      expect (step (E i) (tails E i) (prefixLaw E (tails E) t)) (states i.succ).eval ≤ _ at hstep
    linarith

/-- The complete fourteen-prime finite-exponent hinge budget is below the
certified initial value, independently of all fourteen exponent bounds. -/
theorem prefix_cost_bound (E : Fin 14 → ℕ) :
    exponentCost E (tails E) (fun _ => 5/4) (fun i => 1/(primes i-1 : ℚ)) ≤
      (states 0).eval 1 := by
  have hh := prefix_potential E 14 le_rfl
  have hz : expect (prefixLaw E (tails E) 14) (states 14).eval=0 := by
    simp only [expect,Finsupp.sum,terminal_eval,mul_zero,Finset.sum_const_zero]
  change (∑ j ∈ Finset.range 14, lossAt E j) +
    expect (prefixLaw E (tails E) 14) (states 14).eval ≤ _ at hh
  rw [hz,add_zero] at hh
  apply le_trans (le_of_eq ?_) hh
  unfold exponentCost
  rw [← Fin.sum_univ_eq_sum_range (lossAt E) 14]
  apply Finset.sum_congr rfl
  intro i hi
  rw [exponentEnvelope_eq_expect]
  simp only [lossAt,i.isLt,dif_pos,Nat.cast_one,one_mul]
  apply Erdos7BinarySieve.expect_congr
  intro k
  unfold loss Erdos7Distortion.residual
  congr 1
  ring

#print axioms prefix_cost_bound
#print axioms certificate
#print axioms row_op
#print axioms saving_certificate
end Erdos7ExceptionalScalar
