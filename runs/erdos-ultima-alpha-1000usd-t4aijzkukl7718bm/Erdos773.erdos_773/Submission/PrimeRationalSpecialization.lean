import Submission.SmallRationalGaussianSpecialization

/-! Prime denominators, even inert primes, do not repair rational specialization.
This is a counterexample to a proposed construction, NOT to Erdős 773. -/
namespace Erdos773.PrimeRationalSpecialization
open Finset Polynomial
noncomputable section
set_option maxHeartbeats 30000000
set_option maxRecDepth 32000

def denominator : ℕ := 468182477601170824986000000000000000000000000000000000000
def start : ℕ := 524783238475
def coefficient : Fin 4 → Fin 42 → ℕ := ![![9935301624737524450287601170824986000000000000000000,4681824776011708249860000000000000000000000000000000,40091750825173084970177450370847165732190000000000000,4635974397255806772476479311253568678900000000000000,4680067244360197220148356675695285542000000000000000,4691093398265679479798451076414202094600000000000000,4689185591346869890091823384876374317950000000000000,4685207933724413555073258620121947848840000000000000,4682663720183793933873893640302985756250000000000000,4681673087797789175729781907437895010460000000000000,4681517229467091741181258467230388575640000000000000,4681629026306313160217051681934576155640000000000000,4681748905974681466822806670562470628810000000000000,4681813045836819779945292094179800468000000000000000,4681833493294377996886645167278115267390000000000000,4681834025923894480181886234157455903300000000000000,4681829704019237840657565695828039734800000000000000,4681826337962090454136522943130919967800000000000000,4681824810126605100962206895067401823550000000000000,4681824440936552352519718751496162305640000000000000,4681824516700805924410128041196768344250000000000000,4681824658803395424892960765440916314060000000000000,4681824747939252782995790108291825995640000000000000,4681824782011622748031403712360092605640000000000000,4681824786996205531494974335952777115210000000000000,4681824782868786842028446249005139640000000000000000,4681824778620655101956964609487954930590000000000000,4681824776386020136755403550355149847700000000000000,4681824775690144915119847819060988071600000000000000,4681824775683980514169153836692875185000000000000000,4681824775840041341080505429265520449150000000000000,4681824775958569534040107810089049690440000000000000,4681824776011474135331835987196360036250000000000000,4681824776023802898377632382519590673660000000000000,192068984698640578082095778654782812503640000000000000,191896333482779394532305099304178797503640000000000000,4681824776012566518856721949015225501960000000000000,4681824776011786256863809648412289750700000000000000,4681824776010771880222972882338241719727066471529169,4681824776011786280272933528470831000000000000000000,4681824776011552189034132943058338000000000000000000,0],
  ![9935301624736588085332398829175014000000000000000000,4681824776011708249860000000000000000000000000000000,40036800469108429126362549629152834267810000000000000,4727675154767609727243520688746431321100000000000000,4683582307663219279571643324304714458000000000000000,4672556153757737019921548923585797905400000000000000,4674463960676546609628176615123625682050000000000000,4678441618299002944646741379878052151160000000000000,4680985831839622565846106359697014243750000000000000,4681976464225627323990218092562104989540000000000000,4682132322556324758538741532769611424360000000000000,4682020525717103339502948318065423844360000000000000,4681900646048735032897193329437529371190000000000000,4681836506186596719774707905820199532000000000000000,4681816058729038502833354832721884732610000000000000,4681815526099522019538113765842544096700000000000000,4681819848004178659062434304171960265200000000000000,4681823214061326045583477056869080032200000000000000,4681824741896811398757793104932598176450000000000000,4681825111086864147200281248503837694360000000000000,4681825035322610575309871958803231655750000000000000,4681824893220021074827039234559083685940000000000000,4681824804084163716724209891708174004360000000000000,4681824770011793751688596287639907394360000000000000,4681824765027210968225025664047222884790000000000000,4681824769154629657691553750994860360000000000000000,4681824773402761397763035390512045069410000000000000,4681824775637396362964596449644850152300000000000000,4681824776333271584600152180939011928400000000000000,4681824776339435985550846163307124815000000000000000,4681824776183375158639494570734479550850000000000000,4681824776064846965679892189910950309560000000000000,4681824776011942364388164012803639963750000000000000,4681824775999613601342367617480409326340000000000000,192068984698622319208924221345217187496360000000000000,191896333482771279612814900695821202496360000000000000,4681824776010849980863278050984774498040000000000000,4681824776011630242856190351587710249300000000000000,4681824776012644619497027117661602219447066471529169,4681824776011630219447066471529169000000000000000000,4681824776011864310685867056941662000000000000000000,0],
  ![9935301624736588085332398829175014000000000000000000,4681824776011708249860000000000000000000000000000000,40036800469108429126362549629152834267810000000000000,4727675154767609727243520688746431321100000000000000,4683582307663219279571643324304714458000000000000000,4672556153757737019921548923585797905400000000000000,4674463960676546609628176615123625682050000000000000,4678441618299002944646741379878052151160000000000000,4680985831839622565846106359697014243750000000000000,4681976464225627323990218092562104989540000000000000,4682132322556324758538741532769611424360000000000000,4682020525717103339502948318065423844360000000000000,4681900646048735032897193329437529371190000000000000,4681836506186596719774707905820199532000000000000000,4681816058729038502833354832721884732610000000000000,4681815526099522019538113765842544096700000000000000,4681819848004178659062434304171960265200000000000000,4681823214061326045583477056869080032200000000000000,4681824741896811398757793104932598176450000000000000,4681825111086864147200281248503837694360000000000000,4681825035322610575309871958803231655750000000000000,4681824893220021074827039234559083685940000000000000,4681824804084163716724209891708174004360000000000000,4681824770011793751688596287639907394360000000000000,4681824765027210968225025664047222884790000000000000,4681824769154629657691553750994860360000000000000000,4681824773402761397763035390512045069410000000000000,4681824775637396362964596449644850152300000000000000,4681824776333271584600152180939011928400000000000000,4681824776339435985550846163307124815000000000000000,4681824776183375158639494570734479550850000000000000,4681824776064846965679892189910950309560000000000000,4681824776011942364388164012803639963750000000000000,4681824775999613601342367617480409326340000000000000,192068984698622319208924221345217187496360000000000000,191896333482771279612814900695821202496360000000000000,4681824776010693920037410994043112498040000000000000,4681824776012254486159658579354358249300000000000000,4681824776011552193715957719070124280272933528470831,4681824776012254462750534699295817000000000000000000,4681824776011708249860000000000000000000000000000000,0],
  ![9935301624737524450287601170824986000000000000000000,4681824776011708249860000000000000000000000000000000,40091750825173084970177450370847165732190000000000000,4635974397255806772476479311253568678900000000000000,4680067244360197220148356675695285542000000000000000,4691093398265679479798451076414202094600000000000000,4689185591346869890091823384876374317950000000000000,4685207933724413555073258620121947848840000000000000,4682663720183793933873893640302985756250000000000000,4681673087797789175729781907437895010460000000000000,4681517229467091741181258467230388575640000000000000,4681629026306313160217051681934576155640000000000000,4681748905974681466822806670562470628810000000000000,4681813045836819779945292094179800468000000000000000,4681833493294377996886645167278115267390000000000000,4681834025923894480181886234157455903300000000000000,4681829704019237840657565695828039734800000000000000,4681826337962090454136522943130919967800000000000000,4681824810126605100962206895067401823550000000000000,4681824440936552352519718751496162305640000000000000,4681824516700805924410128041196768344250000000000000,4681824658803395424892960765440916314060000000000000,4681824747939252782995790108291825995640000000000000,4681824782011622748031403712360092605640000000000000,4681824786996205531494974335952777115210000000000000,4681824782868786842028446249005139640000000000000000,4681824778620655101956964609487954930590000000000000,4681824776386020136755403550355149847700000000000000,4681824775690144915119847819060988071600000000000000,4681824775683980514169153836692875185000000000000000,4681824775840041341080505429265520449150000000000000,4681824775958569534040107810089049690440000000000000,4681824776011474135331835987196360036250000000000000,4681824776023802898377632382519590673660000000000000,192068984698640578082095778654782812503640000000000000,191896333482779394532305099304178797503640000000000000,4681824776012722579682589005956887501960000000000000,4681824776011162013560341420645641750700000000000000,4681824776011864306004042280930031780552933528470831,4681824776011162036969465300704183000000000000000000,4681824776011708249860000000000000000000000000000000,0]]
def shift : Fin 42 → ℤ := ![-3,58684763631,-273987000774,524783238375,-360671972774,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

lemma shift_bound : ∀ j, Int.natAbs (shift j)<start := by decide +kernel
lemma offset_nonneg : ∀ i j, 0 ≤ (coefficient i j:ℤ)*start+shift j := by decide +kernel
lemma coefficient_budget : ∀ i j, 600*(coefficient i j+1)+2 ≤ denominator := by decide +kernel
lemma sum_budget : ∀ i, 9+6*∑ j : Fin 42, (coefficient i j+1) ≤ denominator := by decide +kernel
lemma start_large : 2 ≤ start := by norm_num [start]
lemma denominator_large : 2 ≤ denominator := by norm_num [denominator]

def q (t : ℕ) : ℕ := denominator*(t+start)-1
def p (t : ℕ) : ℕ := q t+1

lemma q_add_one (t : ℕ) : q t+1=denominator*(t+start) := by
  have hs := start_large
  have hL := denominator_large
  unfold q
  have hh : 1 ≤ denominator*(t+start) := by nlinarith
  omega
lemma q_pos (t : ℕ) : 0<q t := by
  have hs := start_large
  have hL := denominator_large
  have hh := q_add_one t
  nlinarith
lemma p_pos (t : ℕ) : 0<p t := by unfold p; omega
lemma coprime (t : ℕ) : Nat.Coprime (p t) (q t) :=
  Nat.coprime_self_add_left.mpr (Nat.coprime_one_left (q t))

def digit (t : ℕ) (i : Fin 4) (j : Fin 42) : ℕ :=
  coefficient i j*t+((coefficient i j:ℤ)*start+shift j).toNat

lemma digit_int (t : ℕ) (i : Fin 4) (j : Fin 42) :
    (digit t i j:ℤ)=(coefficient i j:ℤ)*(t+start)+shift j := by
  unfold digit
  rw [Nat.cast_add,Nat.cast_mul,Int.toNat_of_nonneg (offset_nonneg i j)]
  ring
lemma digit_cast (t : ℕ) (i : Fin 4) (j : Fin 42) :
    (digit t i j:ℚ)=(coefficient i j:ℚ)*(t+start)+shift j := by
  exact_mod_cast digit_int t i j

def cleared (t : ℕ) (i : Fin 4) : ℕ :=
  (p t)^43+6*(q t)^43+
    6*∑ j : Fin 42, digit t i j*(p t)^(j.val+1)*(q t)^(42-j.val)

def raw (z : ℚ) (i : Fin 4) : ℚ :=
  (z+1)^43+6*z^43+6*∑ j : Fin 42,
    ((coefficient i j:ℚ)/denominator*(z+1)+shift j)*(z+1)^(j.val+1)*z^(42-j.val)

def F (z : ℚ) : ℚ := SmallRationalGaussianSpecialization.F z
def U (z : ℚ) : ℚ := SmallRationalGaussianSpecialization.U z
def G (z : ℚ) : ℚ := (z+1)*SmallRationalGaussianSpecialization.G z+6*z^39
def V (z : ℚ) : ℚ := (z+1)*SmallRationalGaussianSpecialization.V z

def factored (z : ℚ) : Fin 4 → ℚ :=
  ![F z*G z-U z*V z-F z*V z-G z*U z,
    F z*G z-U z*V z+F z*V z+G z*U z,
    F z*G z+U z*V z-F z*V z+G z*U z,
    F z*G z+U z*V z+F z*V z-G z*U z]

/-- The new certificate is an exact algebraic transformation of the old one. -/
lemma raw_shift (z : ℚ) (i : Fin 4) :
    raw z i=(z+1)*SmallRationalGaussianSpecialization.raw z i+
      6*z^39*(F z+(if i=0 ∨ i=3 then -1 else 1)*U z) := by
  fin_cases i <;>
    norm_num [raw,coefficient,shift,denominator,F,U,
      SmallRationalGaussianSpecialization.raw,SmallRationalGaussianSpecialization.coefficient,
      SmallRationalGaussianSpecialization.shift,SmallRationalGaussianSpecialization.denominator,
      SmallRationalGaussianSpecialization.F,SmallRationalGaussianSpecialization.U,
      Fin.sum_univ_succ,Fin.ext_iff] <;> ring

lemma raw_factor (z : ℚ) (i : Fin 4) : raw z i=factored z i := by
  rw [raw_shift,SmallRationalGaussianSpecialization.raw_factor]
  fin_cases i <;>
    simp [factored,SmallRationalGaussianSpecialization.factored,F,G,U,V,Fin.ext_iff] <;> ring

lemma cleared_cast (t : ℕ) (i : Fin 4) : (cleared t i:ℚ)=raw (q t) i := by
  unfold cleared raw
  simp only [p,Nat.cast_add]
  push_cast
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [digit_cast]
  have hq : (q t:ℚ)+1=(denominator:ℚ)*(t+start) := by exact_mod_cast q_add_one t
  have he : (coefficient i j:ℚ)*(t+start)=
      (coefficient i j:ℚ)/denominator*((q t:ℚ)+1) := by
    rw [hq]
    norm_num [denominator]
    ring
  rw [he]

lemma cleared_pos (t : ℕ) (i : Fin 4) : 0<cleared t i := by
  have hp := pow_pos (p_pos t) 43
  unfold cleared
  omega

lemma raw_collision (z : ℚ) : (raw z 0)^2+(raw z 1)^2=(raw z 2)^2+(raw z 3)^2 := by
  simp only [raw_factor]
  change (F z*G z-U z*V z-F z*V z-G z*U z)^2+
      (F z*G z-U z*V z+F z*V z+G z*U z)^2=
      (F z*G z+U z*V z-F z*V z+G z*U z)^2+
      (F z*G z+U z*V z+F z*V z-G z*U z)^2
  ring

lemma collision (t : ℕ) : (cleared t 0)^2+(cleared t 1)^2=
    (cleared t 2)^2+(cleared t 3)^2 := by
  have hh := raw_collision (q t)
  simp only [← cleared_cast] at hh
  exact_mod_cast hh

lemma G_positive {z : ℚ} (hz : 0<z) (hr : 0<raw z 0) : 0<G z := by
  have hu : 0<U z := by unfold U SmallRationalGaussianSpecialization.U; positivity
  have hv : 0<V z := by unfold V SmallRationalGaussianSpecialization.V; positivity
  have hf : 0<F z := by unfold F SmallRationalGaussianSpecialization.F; positivity
  have hfu : U z<F z := SmallRationalGaussianSpecialization.F_gt_U z
  rw [raw_factor] at hr
  change 0<F z*G z-U z*V z-F z*V z-G z*U z at hr
  by_contra! hg
  have hm := mul_nonpos_of_nonpos_of_nonneg hg (sub_pos.mpr hfu).le
  have hn := mul_pos hv (add_pos hf hu)
  nlinarith only [hm,hn,hr]

lemma raw_nontrivial {z : ℚ} (hz : 0<z) (hr : 0<raw z 0) :
    raw z 0<raw z 2 ∧ raw z 0<raw z 3 := by
  have hf : 0<F z := by unfold F SmallRationalGaussianSpecialization.F; positivity
  have hg := G_positive hz hr
  have hu : 0<U z := by unfold U SmallRationalGaussianSpecialization.U; positivity
  have hv : 0<V z := by unfold V SmallRationalGaussianSpecialization.V; positivity
  simp only [raw_factor]
  change F z*G z-U z*V z-F z*V z-G z*U z < F z*G z+U z*V z-F z*V z+G z*U z ∧
    F z*G z-U z*V z-F z*V z-G z*U z < F z*G z+U z*V z+F z*V z-G z*U z
  constructor
  · nlinarith only [mul_pos hu (add_pos hv hg)]
  · nlinarith only [mul_pos hv (add_pos hu hf)]

lemma nontrivial (t : ℕ) : cleared t 0<cleared t 2 ∧ cleared t 0<cleared t 3 := by
  have hr : (0:ℚ)<raw (q t) 0 := by rw [← cleared_cast]; exact_mod_cast cleared_pos t 0
  have hh := raw_nontrivial (show (0:ℚ)<q t by exact_mod_cast q_pos t) hr
  simp only [← cleared_cast] at hh
  exact_mod_cast hh

theorem not_sidon (t : ℕ) : ¬IsSidon ((fun i : Fin 4 => (cleared t i)^2) '' Set.univ) := by
  intro hs
  have hm (i : Fin 4) : (cleared t i)^2 ∈ (fun i : Fin 4 => (cleared t i)^2) '' Set.univ :=
    ⟨i,Set.mem_univ i,rfl⟩
  have h := hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t)
  have hn := nontrivial t
  rcases h with h | h
  · exact (Nat.pow_lt_pow_left hn.1 (by decide : (2:ℕ) ≠ 0)).ne h.1
  · exact (Nat.pow_lt_pow_left hn.2 (by decide : (2:ℕ) ≠ 0)).ne h.1

lemma digit_upper (t : ℕ) (i : Fin 4) (j : Fin 42) :
    digit t i j ≤ (coefficient i j+1)*(t+start) := by
  have hs : shift j < (start:ℤ) := by
    have hh : Int.natAbs (shift j) < (start:ℤ) := by exact_mod_cast shift_bound j
    rw [Int.natCast_natAbs] at hh
    exact (abs_lt.mp hh).2
  have hd := digit_int t i j
  have ht : (0:ℤ) ≤ t := Int.natCast_nonneg t
  have hh : (digit t i j:ℤ) ≤ (coefficient i j+1)*(t+start) := by
    rw [hd]
    nlinarith only [hs,ht]
  exact_mod_cast hh

/-- Every nonconstant lower encoding coefficient is less than q/100. -/
theorem small_digits (t : ℕ) (i : Fin 4) (j : Fin 42) : 100*(6*digit t i j)<q t := by
  have hs := start_large
  have hb := Nat.mul_le_mul_right (t+start) (coefficient_budget i j)
  have hd := Nat.mul_le_mul_left 600 (digit_upper t i j)
  have hq := q_add_one t
  nlinarith only [hb,hd,hq,hs]

/-- The sum of all encoding coefficients, including both end digits, is below q. -/
theorem small_total (t : ℕ) (i : Fin 4) : 7+6*∑ j : Fin 42, digit t i j < q t := by
  have ht : 1≤t+start := by have hh := start_large; omega
  have hs : ∑ j : Fin 42, digit t i j ≤ (∑ j : Fin 42, (coefficient i j+1))*(t+start) := by
    calc
      _ ≤ ∑ j : Fin 42, (coefficient i j+1)*(t+start) := sum_le_sum (fun j hj => digit_upper t i j)
      _ = _ := by rw [sum_mul]
  have hb := Nat.mul_le_mul_right (t+start) (sum_budget i)
  have hq := q_add_one t
  nlinarith only [hs,hb,ht,hq]

def parameter (t : ℕ) (i : Fin 4) : ℤ[X] :=
  C 1+∑ j : Fin 42, C (digit t i j:ℤ)*X^(j.val+1)
def poly (t : ℕ) (i : Fin 4) : ℤ[X] := FormalGaussianSidon.encoding 43 (parameter t i)

lemma parameter_constant (t : ℕ) (i : Fin 4) : (parameter t i).coeff 0=1 := by simp [parameter]
lemma parameter_degree (t : ℕ) (i : Fin 4) : (parameter t i).natDegree<43 := by
  have hh : (parameter t i).natDegree ≤ 42 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have he (j : Fin 42) : n ≠ j.val+1 := by have hj := j.isLt; omega
    simp [parameter,coeff_one,he,show n ≠ 0 by omega]
  omega
lemma admissible (t : ℕ) (i : Fin 4) : FormalGaussianSidon.Admissible 43 (parameter t i) := by
  exact ⟨parameter_degree t i,by rw [parameter_constant]; norm_num⟩

theorem formal_sidon (t : ℕ) : IsSidon ((fun i : Fin 4 => (poly t i)^2) '' Set.univ) := by
  have hm {x : ℤ[X]} (hx : x ∈ (fun i : Fin 4 => (poly t i)^2) '' Set.univ) :
      x ∈ (fun P : ℤ[X] => (FormalGaussianSidon.encoding 43 P)^2) ''
        {P | FormalGaussianSidon.Admissible 43 P} := by
    obtain ⟨i,hi,rfl⟩ := hx
    exact ⟨parameter t i,admissible t i,rfl⟩
  intro a ha b hb c hc d hd he
  exact FormalGaussianSidon.formal_sidon 43 a (hm ha) b (hm hb) c (hm hc) d (hm hd) he

lemma evaluation (t : ℕ) (i : Fin 4) :
    (q t:ℚ)^43 * (poly t i).eval₂ (Int.castRingHom ℚ) ((p t:ℚ)/q t)=cleared t i := by
  have hq : (q t:ℚ) ≠ 0 := by exact_mod_cast (q_pos t).ne'
  unfold poly FormalGaussianSidon.encoding parameter cleared
  simp only [eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
  push_cast
  simp only [Fin.sum_univ_succ]
  norm_num [Fin.val_succ]
  field_simp
  ring

lemma coefficient_nonneg (t : ℕ) (i : Fin 4) (n : ℕ) : 0 ≤ (poly t i).coeff n := by
  have hp : 0 ≤ (parameter t i).coeff n := by
    simp only [parameter,coeff_add,finset_sum_coeff,coeff_C_mul,coeff_X_pow,coeff_C]
    apply add_nonneg
    · split_ifs <;> norm_num
    · apply sum_nonneg
      intro j hj
      split_ifs <;> positivity
  simp only [poly,FormalGaussianSidon.encoding,coeff_add,coeff_X_pow,coeff_C_mul]
  positivity

lemma eval_one (t : ℕ) (i : Fin 4) :
    (poly t i).eval 1=(7+6*∑ j : Fin 42, digit t i j:ℕ) := by
  unfold poly FormalGaussianSidon.encoding parameter
  simp only [eval_add,eval_mul,eval_pow,eval_X,eval_C,eval_finset_sum,one_pow,mul_one]
  push_cast
  ring

lemma coefficient_small (t : ℕ) (i : Fin 4) (n : ℕ) : (poly t i).coeff n<(q t:ℤ) := by
  have hh := RationalDigitInjection.coeff_le_value_one (coefficient_nonneg t i) n
  rw [eval_one] at hh
  exact hh.trans_lt (by exact_mod_cast small_total t i)

lemma distinguished_coefficient (t : ℕ) (i : Fin 4) :
    (poly t i).coeff 37=6*(digit t i 36:ℤ) := by
  have he (j : Fin 42) : (37=j.val+1) ↔ j=36 := by
    constructor
    · intro h
      apply Fin.ext
      change j.val=36
      omega
    · rintro rfl
      decide
  simp [poly,FormalGaussianSidon.encoding,parameter,finset_sum_coeff,
    coeff_X_pow,coeff_one,he]

lemma distinguished_injective : Function.Injective (fun i : Fin 4 => coefficient i 36) := by
  decide +kernel

lemma poly_injective (t : ℕ) : Function.Injective (poly t) := by
  intro i k he
  have hd := congrArg (fun P : ℤ[X] => P.coeff 37) he
  simp only [distinguished_coefficient,digit_int] at hd
  have hs : (coefficient i 36:ℤ)*(t+start)=(coefficient k 36:ℤ)*(t+start) := by omega
  have ht : (0:ℤ)<t+start := by have hh := start_large; exact_mod_cast (show 0<t+start by omega)
  have hc := mul_right_cancel₀ ht.ne' hs
  exact distinguished_injective (by exact_mod_cast hc)

lemma cleared_injective (t : ℕ) : Function.Injective (cleared t) := by
  intro i k he
  apply poly_injective t
  have hq : (q t:ℚ) ≠ 0 := by exact_mod_cast (q_pos t).ne'
  apply RationalDigitInjection.eval_injective (q_pos t) (coprime t)
  · intro n
    apply abs_lt.mpr
    have hi := coefficient_small t i n
    have hk := coefficient_small t k n
    have hi0 := coefficient_nonneg t i n
    have hk0 := coefficient_nonneg t k n
    constructor <;> linarith only [hi,hk,hi0,hk0]
  · apply mul_left_cancel₀ (pow_ne_zero 43 hq)
    rw [evaluation,evaluation,he]

lemma denominator_mod_four (t : ℕ) : q t % 4=3 := by
  have hh : (q t+1)%4=0 := by
    rw [q_add_one,Nat.mul_mod]
    norm_num [denominator]
  omega

/-- Dirichlet's theorem supplies arbitrarily large prime denominators in
this exact family. The denominator is not just allowed to be prime. -/
lemma arbitrarily_large_prime (B : ℕ) : ∃ t, B<q t ∧ Nat.Prime (q t) := by
  have hL : denominator ≠ 0 := by have hh := denominator_large; omega
  have hc : Nat.Coprime (denominator-1) denominator := by norm_num [denominator]
  obtain ⟨Q,hQ,hprime,hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max B (denominator*start)) hL hc
  have hmod' := hmod.add_right 1
  have hdiv : denominator ∣ Q+1 := by
    apply Nat.dvd_of_mod_eq_zero
    have hL1 : denominator-1+1=denominator := by have hh := denominator_large; omega
    simpa only [Nat.ModEq,hL1,Nat.mod_self] using hmod'
  obtain ⟨k,hk⟩ := hdiv
  have hQstart : denominator*start<Q := (le_max_right _ _).trans_lt hQ
  have hks : start≤k := by
    by_contra! hn
    have hh := Nat.mul_le_mul_left denominator hn.le
    omega
  have he : q (k-start)=Q := by
    unfold q
    rw [Nat.sub_add_cancel hks,← hk]
    omega
  exact ⟨k-start,by rw [he]; exact (le_max_left _ _).trans_lt hQ,by rwa [he]⟩

/-- The original formal Gaussian family fails at arbitrarily large prime
rational denominators congruent to three modulo four, despite nonnegative
small digits, a small total coefficient sum, and injective evaluation. -/
theorem arbitrarily_large_prime_obstruction (B : ℕ) :
    ∃ t, B<q t ∧ Nat.Prime (q t) ∧ q t%4=3 ∧ Nat.Coprime (p t) (q t) ∧
      IsSidon ((fun i : Fin 4 => (poly t i)^2) '' Set.univ) ∧
      (∀ i n, 0 ≤ (poly t i).coeff n) ∧
      (∀ i j, 100*(6*digit t i j)<q t) ∧
      (∀ i, 7+6*∑ j : Fin 42, digit t i j<q t) ∧
      (∀ i, (q t:ℚ)^43*(poly t i).eval₂ (Int.castRingHom ℚ) ((p t:ℚ)/q t)=cleared t i) ∧
      (∀ i, 0<cleared t i) ∧ Function.Injective (cleared t) ∧
      ¬IsSidon ((fun i : Fin 4 => (cleared t i)^2) '' Set.univ) := by
  obtain ⟨t,ht,hprime⟩ := arbitrarily_large_prime B
  exact ⟨t,ht,hprime,denominator_mod_four t,coprime t,formal_sidon t,
    coefficient_nonneg t,small_digits t,small_total t,evaluation t,
    cleared_pos t,cleared_injective t,not_sidon t⟩

#print axioms raw_shift
#print axioms raw_factor
#print axioms collision
#print axioms formal_sidon
#print axioms small_digits
#print axioms small_total
#print axioms evaluation
#print axioms cleared_injective
#print axioms arbitrarily_large_prime
#print axioms arbitrarily_large_prime_obstruction

end
end Erdos773.PrimeRationalSpecialization
