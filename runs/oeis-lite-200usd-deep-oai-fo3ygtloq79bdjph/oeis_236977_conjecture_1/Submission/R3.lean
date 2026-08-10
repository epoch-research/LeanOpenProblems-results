import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option linter.unusedVariables false

open Nat Finset

/--
A236998: a(n) = |{0 < k < n/2: phi(k)*phi(n-k) is a square}|, where phi(.) is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

abbrev BOUND : Nat := 2 * 10^6

def phiRec : Nat -> Nat
| 0 => 0
| 1 => 1
| n+2 =>
  let p := Nat.minFac (n+2)
  let m := (n+2) / p
  if p ∣ m then p * phiRec m else (p-1) * phiRec m
termination_by x => x
decreasing_by
  · have hp : 2 ≤ (n+2).minFac := (Nat.minFac_prime (by omega : n+2 ≠ 1)).two_le
    have hpos : 0 < n+2 := by omega
    have hlt : (n+2) / (n+2).minFac < n+2 := Nat.div_lt_self hpos (by omega)
    omega
  · have hp : 2 ≤ (n+2).minFac := (Nat.minFac_prime (by omega : n+2 ≠ 1)).two_le
    have hpos : 0 < n+2 := by omega
    have hlt : (n+2) / (n+2).minFac < n+2 := Nat.div_lt_self hpos (by omega)
    omega

theorem phiRec_eq_totient (n : Nat) : phiRec n = Nat.totient n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [phiRec]
    · simp [phiRec]
    · let p := Nat.minFac (n+2)
      let m := (n+2) / p
      have hp : Nat.Prime p := by
        dsimp [p]
        exact Nat.minFac_prime (by omega : n+2 ≠ 1)
      have hpdvd : p ∣ n+2 := by dsimp [p]; exact Nat.minFac_dvd _
      have hm_lt : m < n+2 := by
        dsimp [m]
        exact Nat.div_lt_self (by omega) (by exact hp.two_le)
      have hpm : p * m = n+2 := by
        dsimp [m]
        rw [Nat.mul_comm]
        exact Nat.div_mul_cancel hpdvd
      by_cases hdiv : p ∣ m
      · simp [phiRec, p, m, hdiv]
        rw [ih m hm_lt]
        change p * Nat.totient m = Nat.totient (n+2)
        rw [← hpm]
        exact (Nat.totient_mul_of_prime_of_dvd hp hdiv).symm
      · simp [phiRec, p, m, hdiv]
        rw [ih m hm_lt]
        change (p-1) * Nat.totient m = Nat.totient (n+2)
        rw [← hpm]
        exact (Nat.totient_mul_of_prime_of_not_dvd hp hdiv).symm

theorem family_sound (a0 b x r : Nat) (ha0 : 0 < a0) (hpos : 0 < x) (hab : a0 < b)
    (hcop : x.Coprime (a0*b)) (hsq : Nat.totient a0 * Nat.totient b = r*r) :
    a ((a0+b)*x) > 0 := by
  rw [a]
  apply Finset.sum_pos'
  · intro i hi; exact Nat.zero_le _
  · refine ⟨a0*x, ?_, ?_⟩
    · simp [mem_Ico]
      constructor
      · nlinarith [ha0, hpos]
      · have hlt : 2*(a0*x) < (a0+b)*x := by nlinarith [hab, hpos]
        omega
    · have hcop_a : a0.Coprime x := by exact (Nat.Coprime.coprime_dvd_right (by exact dvd_mul_right a0 b) hcop).symm
      have hcop_b : b.Coprime x := by exact (Nat.Coprime.coprime_dvd_right (by exact dvd_mul_left b a0) hcop).symm
      have hsub : (a0 + b) * x - a0 * x = b*x := by rw [Nat.add_mul]; omega
      have hphi1 : Nat.totient (a0*x) = Nat.totient a0 * Nat.totient x := Nat.totient_mul hcop_a
      have hphi2 : Nat.totient (((a0+b)*x) - a0*x) = Nat.totient b * Nat.totient x := by rw [hsub, Nat.totient_mul hcop_b]
      rw [hphi1, hphi2]
      have hsq2 : (r * Nat.totient x)^2 = (Nat.totient a0 * Nat.totient x) * (Nat.totient b * Nat.totient x) := by
        rw [pow_two]
        calc
          r * Nat.totient x * (r * Nat.totient x) = (r*r) * (Nat.totient x * Nat.totient x) := by ring
          _ = (Nat.totient a0 * Nat.totient b) * (Nat.totient x * Nat.totient x) := by rw [← hsq]
          _ = (Nat.totient a0 * Nat.totient x) * (Nat.totient b * Nat.totient x) := by ring
      have hsqrt : sqrt ((Nat.totient a0 * Nat.totient x) * (Nat.totient b * Nat.totient x)) ^ 2 = (Nat.totient a0 * Nat.totient x) * (Nat.totient b * Nat.totient x) := by
        rw [← hsq2]
        simp [Nat.sqrt_eq, pow_two]
      simp [hsqrt]

def famCond (s c n : Nat) : Bool := decide (n % s = 0 ∧ (n/s).Coprime c)

abbrev FBASE : Nat := 2000003
def fa (code : Nat) := code % FBASE
def fb (code : Nat) := (code / FBASE) % FBASE
def fr (code : Nat) := (code / (FBASE*FBASE)) % FBASE
def famCodeCond (code n : Nat) : Bool := famCond (fa code + fb code) (fa code * fb code) n
def famCodeValid (code : Nat) : Bool := decide (0 < fa code ∧ fa code < fb code ∧ phiRec (fa code) * phiRec (fb code) = fr code * fr code)
def fams : List Nat := [4000016000016,8000034000034,8000040000044,8000032000033,24000090000088,16000080000088,8000048000055,24000110000114,8000044000049,8000048000056,16000080000087,24000146000166,32000160000176,48000182000180,16000072000077,24000110000117,24000110000115,72000270000262,16000096000112,32000130000135,16000088000102,24000126000139,80000322000314,24000186000226,48000258000284,24000148000171,176000706000686,48000198000205,32000160000173,96000366000368,48000196000207,48000222000239,32000192000224,32000266000328,48000228000247,24000186000227,144000546000532,48000248000273,32000224000267,96000470000504,48000270000305,24000126000138,72000324000343,160000682000680,144000650000664,48000290000333,96000416000427,96000434000451,224000898000872,48000292000338,48000300000349,144000698000736,48000326000387,120000662000730,40000322000395,72000542000654,96000470000505,24000288000379,288001058001020,192000814000834,144000584000589,48000334000399,24000324000433,96000678000808,192000962001024,96000516000575,224001066001112,32000368000481,144000584000615,288001134001144,48000436000549,144000650000693,96000576000661,16000082000088,144000926001072,144000684000739,48000396000494,72000542000655,216001134001234,144000724000789,48000690000928,80000790001008,144000758000829,96000624000733,192000832000879,288001382001464,32000480000649,192001146001304,144000774000863,56000562000719,384001542001568,144000950001110,624002210002068,432001782001792,240001022001065,384001662001720,48000508000657,96000726000881,224001066001127,144001134001384,96000736000897,240001402001584,32000480000650,144000868000999,144000876001009,336001694001824,288001566001736,192001014001121,240001470001684,192001018001131,192000828000895,480002050002088,192001024001143,128000724000846,128000898001071,144000936001099,384001866002000,144000950001119,96000834001043,192001088001227,480002210002296,48000728000985,336001694001830,576002246002268,96001198001584,240001626001912,192001122001285,120000964001185,288001782002044,96000900001141,288001774002040,192001158001331,288001826002112,288001382001497,144001080001309,72001242001702,432002274002476,144001098001337,288001448001581,216001300001491,528002522002664,480002450002632,336001610001717,240001806002180,240001402001589,480002450002652,576002698002832,384001664001749,288001518001681,192001290001529,192001734002176,288001530001703,240001452001669,192001352001609,384002310002636,160001282001571,864003510003484,960003650003556,384001798001929,192001834002324,264001588001811,336001796001975,48001008001405,240002022002504,48001020001423,144001304001639,864003570003596,192001440001745,48001056001477,1104004146004012,192001472001789,384002478002888,96001206001597,240001588001875,144001838002436,256001448001692,288002270002772,240001626001925,528002380002471,480002826003200,72001194001631,480002870003256,320001862002121,144001420001815,960003946003984,288001826002119,960003930003976,144001458001871,400002706003184,288001842002149,480002950003384,1152004478004416,48001152001621,144001496001929,48001236001747,144002062002772,288001900002241,192001668002087,864003998004188,320002610003212,72001350001865,240001818002209,384002180002469,480003090003592,576003358003792,96001456001971,192001734002183,192002322003056,288001998002381,1152004786004808,288001998002383,224001854002293,720003834004192,432002360002649,240001928002365,480003190003744,240001922002361,1152004782004840,800004050004376,96001546002105,1152004998005068,192001834002331,384002336002691,480002532002819,72001520002119,288002762003504,144001740002293,384002368002739,144001764002329,192002514003344,192001902002435,288002178002645,1344005322005296,144001800002383,576002896003165,960004626004904,144001838002439,480003390004036,288002270002773,192002004002587,432003294003988,480002742003115,480002742003121,672003986004524,216002106002687,1152005354005536,624003226003509,432002702003135,576003042003371,64001728002449,1248005434005580,960004430004582,576003036003377,864004590005036,256002310002905,384002690003199,1104005258005544,80001856002605,384002696003219,1104005286005584,480002998003461,480002928003389,1152005346005620,576003254003649,672003478003803,1440006170006232,1152005394005684,192002240002935,384002784003349,1632006630006580,576003280003705,480003044003543,528003172003639,1536006538006572,1440005946006064,480003112003629,1440006130006252,192002322003059,288002592003259,168002270003031,1728006642006560,1536006546006620,288002640003331,336002772003431,240002532003271,2080007550007228,768003968004321,288002700003421,2112008078007756,672003640004077,672003782004225,768003846004223,1728007082007068,1440006210006416,288002762003513,96002226003125,2016007454007236,192002514003347,216002596003417,1920007690007556,384003056003759,1728006710006732,288002826003607,864004540005126,1728007182007208,288002840003633,432003244003933,432003258003953,576003626004215,1728007146007196,528003516004153,1008004790005065,1728007082007140,720003972004471,576003690004307,1728006894006964,864004368004771,576003726004357,648003892004461,1008004802005107,40000322000394,1056004770005047,1920007410007372,1120005324005866,1152005188005411,1152005120005347,1920007690007668,864004568005017,864004540004985,1920007310007308,960004784005167,928004648005061,1728007182007340,960004698005095,1920007570007596,1920007710007772,1104005004005299,1920007630007668,1920007610007656,864004554005035,2688009646009152,864004590005093,1280005840006394,1248005096005313,2016007854007880,864004554005069,2304008850008668,960004818005269,864004590005123,3024010706010012,960004848005321,1152005354005677,960004848005329,2304008842008736,1152005184005914,1152005224005577,1440006064006197,1152005412006166,960004864005367,2448009186008992,1152005400005765,2496009426009200,1152005120005487,2640009906009580,2400009010008868,1152005418005791,2208008570008592,1584006454006515,2640009906009632,1152005328005723,2304008810008796,2880010490010048,2400009150009076,1152005432005847,1248005622005963,2592009774009592,1152005224005643,1344005840006123,1440006264006958,1680006602006631,2592009774009644,1296005836006165,3360011926011228,1440006244006467,1440005936006153,1296005850006185,2688010034009876,1152005380005835,1680006838006899,1680007028007606,1680006712006779,3024011070010684,1440006264007058,1440006296007110,1344006004006363,1440005926006207,2688010034009972,1344006004006369,1680006724006845,1440006036006355,48000290000330,1680007004007153,144000758000828,1344006004006423,1440006264006607,1440006276006625,1728007088007231,1728007160007363,1536006546006875,1536006546006877,1680007004007275,1728007128007381,1728007132007389,1728007182007469,1440006036006403,1584006500006783,1920007424007417,1680006806007035,1728007182007493,1440005994006367,1584006628006999,1680007004007353,1728007128007433,1680006932007251,1680007028007395,1728007082007383,1440005992006399,1728007122007447,1920007366007385,1728006916007143,1728007108007431,1728007132007473,1920007552007679,1664006624006869,1728007140007501,1920007298007309,1920007388007459,1632006540006859,1920007712007971,1760007166007515,1728007146007559,1728006952007269,2016007682007741,2304008810008803,1680006804007207,2016008046008321,1920007728008065,1728007082007533,1920007578007879,2016007814008061,2016007884008173,1920007698008129,1920007664008085,2304008816008989,96001646002254,2112008276008389,1792007346007755,1728007020007457,1920007630007979,1728007074007589,2304008842008945,1920007760008193,1920007728008177,1920007700008139,1920007744008211,2208008570008827,1728007160007797,1920007712008223]
def famAt (i : Nat) : Nat := fams.getD i 0
def checkFams : List Nat -> Bool
| [] => true
| c::cs => famCodeValid c && checkFams cs
theorem famCode_sound {code n : Nat} (hv : famCodeValid code = true) (h : famCodeCond code n = true) (hn : 9 ≤ n) : a n > 0 := by
  dsimp [famCodeValid] at hv
  rcases (of_decide_eq_true hv) with ⟨ha,hlt,hsq⟩
  dsimp [famCodeCond, famCond] at h
  rcases (of_decide_eq_true h) with ⟨hmod,hcop⟩
  let a0 := fa code; let b0 := fb code; let r0 := fr code; let x := n/(a0+b0)
  have hdvd:a0+b0∣n:=Nat.dvd_of_mod_eq_zero hmod
  have hxpos:0<x:=by dsimp [x]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hn_eq:n=(a0+b0)*x:=by dsimp [x]; rw [Nat.mul_comm]; exact (Nat.div_mul_cancel hdvd).symm
  rw [hn_eq]; apply family_sound a0 b0 x r0 ha hxpos hlt
  · simpa [a0,b0,x] using hcop
  · rw [← phiRec_eq_totient a0, ← phiRec_eq_totient b0]; simpa [a0,b0,r0] using hsq
theorem checkFams_getD_valid {l : List Nat} {i : Nat} (hc : checkFams l = true) (hi : i < l.length) : famCodeValid (l.getD i 0)=true := by
  induction l generalizing i with
  | nil => simp at hi
  | cons c cs ih => cases i with | zero => simp [checkFams] at hc; exact hc.1 | succ i => simp [checkFams] at hc; simp at hi; exact ih hc.2 hi
theorem famAt_valid {i:Nat} (hi:i<fams.length) : famCodeValid (famAt i)=true := by dsimp [famAt]; have hc:checkFams fams=true:=by decide +kernel; exact checkFams_getD_valid hc hi
def covered (n:Nat):Bool:=false
theorem covered_sound_fams {n:Nat} (h:covered n=true) (hn:9≤n): a n>0 := by simp [covered] at h
def tailCondQ (q n : Nat) : Bool := let aa:=n%q; let bb:=n/q; decide (0<aa ∧ 0<bb ∧ n=aa+bb*q ∧ bb.Coprime q ∧ 2*aa<n ∧ phiRec q=q-1 ∧ sqrt (phiRec aa*phiRec bb*(q-1))^2=phiRec aa*phiRec bb*(q-1))
theorem tailCondQ_sound {q n:Nat} (h:tailCondQ q n=true): a n>0 := by
  dsimp [tailCondQ] at h; rcases (of_decide_eq_true h) with ⟨ha,hb,hn,hcop,halt,hq,hsqQ⟩; let aa:=n%q; let bb:=n/q; rw [a]; apply Finset.sum_pos'
  · intro i hi; exact Nat.zero_le _
  · refine ⟨aa, ?_, ?_⟩
    · simp [mem_Ico]; constructor; exact ha; omega
    · have hn' : n=aa+bb*q:=by exact hn; have hsub:n-aa=bb*q:=by omega; have hphi:Nat.totient (n-aa)=Nat.totient bb*Nat.totient q:=by rw [hsub,Nat.totient_mul hcop]; have hqtot:Nat.totient q=q-1:=by rw [← phiRec_eq_totient q,hq]; have hsq:sqrt (totient aa*totient (n-aa))^2=totient aa*totient (n-aa):=by rw [hphi,hqtot,←phiRec_eq_totient aa,←phiRec_eq_totient bb]; simpa [Nat.mul_assoc] using hsqQ; simpa [hsq]
abbrev CBASE:Nat:=90
def valChar(c:Char):Nat:=if c.toNat≤91 then c.toNat-35 else c.toNat-36
def takeNat:Nat->List Char->Nat×List Char|0,cs=>(0,cs)|_+1,[]=>(0,[])|k+1,c::cs=>let p:=takeNat k cs;(valChar c+CBASE*p.1,p.2)
def headVal:List Char->Nat|[]=>0|c::_=>valChar c
def tailList:List Char->List Char|[]=>[]|_::cs=>cs
def validFAt(n:Nat)(cs:List Char):Bool:=let p:=takeNat 2 cs; decide (p.1 < fams.length ∧ famCodeCond (famAt p.1) n=true)
def restF(cs:List Char):List Char:=(takeNat 2 cs).2
def validQAt(n:Nat)(cs:List Char):Bool:=let p:=takeNat 4 cs; tailCondQ p.1 n
def restQ(cs:List Char):List Char:=(takeNat 4 cs).2
def validDAt(n:Nat)(cs:List Char):Bool:=let p1:=takeNat 2 cs; let k:=p1.1; let p2:=takeNat 3 p1.2; let r:=p2.1; decide (k∈Ico 1 ((n-1)/2+1) ∧ r*r=phiRec k*phiRec(n-k))
def restD(cs:List Char):List Char:=(takeNat 3 (takeNat 2 cs).2).2
def validAt(n:Nat)(cs:List Char):Bool:=let t:=headVal cs; let rs:=tailList cs; if t=0 then validFAt n rs else if t=1 then validQAt n rs else validDAt n rs
def restAt(cs:List Char):List Char:=let t:=headVal cs; let rs:=tailList cs; if t=0 then restF rs else if t=1 then restQ rs else restD rs
def checkCode:Nat->Nat->List Char->Bool|lo,0,cs=>validAt lo cs|lo,d+1,cs=>validAt lo cs && checkCode (lo+1) d (restAt cs)
theorem validFAt_sound {n:Nat}{cs:List Char}(hn:9≤n)(hv:validFAt n cs=true):a n>0:=by dsimp [validFAt] at hv; rcases (of_decide_eq_true hv) with ⟨hi,hc⟩; let p:=takeNat 2 cs; exact famCode_sound (famAt_valid hi) hc hn
theorem validDAt_sound {n:Nat}{cs:List Char}(hnB:9≤n∧n≤BOUND)(hv:validDAt n cs=true):a n>0:=by dsimp [validDAt] at hv; rcases (of_decide_eq_true hv) with ⟨hk,hr⟩; let p1:=takeNat 2 cs; let k:=p1.1; let p2:=takeNat 3 p1.2; let r:=p2.1; rw [a]; apply Finset.sum_pos'; · intro i hi; exact Nat.zero_le _; · refine ⟨k,hk,?_⟩; have hsq:sqrt(totient k*totient(n-k))^2=totient k*totient(n-k):=by rw [←phiRec_eq_totient k,←phiRec_eq_totient(n-k),←hr]; simp [Nat.sqrt_eq,pow_two]; simpa [hsq]
theorem validAt_sound {n:Nat}{cs:List Char}(hnB:9≤n∧n≤BOUND)(hv:validAt n cs=true):a n>0:=by dsimp [validAt] at hv; by_cases h0:headVal cs=0; · simp [h0] at hv; exact validFAt_sound hnB.1 hv; · simp [h0] at hv; by_cases h1:headVal cs=1; · simp [h1] at hv; exact tailCondQ_sound hv; · simp [h1] at hv; exact validDAt_sound hnB hv
theorem checkCode_sound {lo d n:Nat}{cs:List Char}(hc:checkCode lo d cs=true)(hnB:9≤n∧n≤BOUND)(hlo:lo≤n)(hhi:n<lo+d+1):a n>0:=by induction d generalizing lo cs with | zero => have hn:n=lo:=by omega; subst n; simp [checkCode] at hc; exact validAt_sound hnB hc | succ d ih => by_cases hnlo:n=lo; · subst n; simp [checkCode] at hc; exact validAt_sound hnB hc.1; · have hnnext:lo+1≤n:=by omega; have hhiNext:n<(lo+1)+d+1:=by omega; simp [checkCode] at hc; exact ih hc.2 hnnext hhiNext
def code_0:String:="####%##+##$##)##,#####'##1##$##-##(#####*##3##$##2##7#####5##6##%##8##'#####0##&##$##?##.#####/##<##$##>##*#####4##A##$##&##%#####9##B##$##E##C#####:##F##(##H##;#####'##)##$##I##0#####%##K##$##M##@#####.##&##$##P##'#####T##Q##$##U##D#####*##R##%##&##4#####G##-##$##W##,#####(##a##$##Y##9#####J##[##$##]##%#####=##`##$##3##:#####N##&##/##+##O#####;##2##$##b##'#####%##e##$##&##p#####0##g##$##h##(#####S##)##$##6##V#####@##j##%##k##.#####*##8##$##l##X#####'##&##$##o##_#####Z##q##$##)##%#####D##s##$##&##'#####^##v##(##w##,#####4##)$#$##+##G#####%##x##$##z##/$####5##|##$##}##/#####c##&##$##<##d#####'##+##%##7$#J#####f##>##$##&##:$####(##)##$##'$#=#####i##*$#$##+$#%#####:##-$#$##A##N#####,##0$#L##1$#*#####O##&##$##)##;#####%##4$#$##+##n#####'##6$#$##&##(#####r##9$#$#"
theorem range_0(n:Nat)(hnB:9≤n∧n≤BOUND)(hlo:9≤n)(hhi:n<265):a n>0:=by
  have hc:checkCode 9 255 code_0.toList=true:=by decide +kernel
  exact checkCode_sound hc hnB hlo (by omega)

def code_1:String:="#B##,#####$$#;$#%##<$#'#####t##2##$##>$#u#####/##?$#$##@$#S#####*##&##$##1##%#####V##B$#$##F##@#####y##)##(##&##{#####'##H##$##G$#*#####%##H$#$##J$##$####X##L$#$##+##'#####,##-##$##)##%$####_##&##%##N$#Z#####&$#I##$##O$#7#####(##+##$##&##D#####($#R$#$##S$#%#####'##T$#$##K##^#####,$#W$#/##-##.$####5##M##$##Y$#'#####%##&##$##]$#*#####G##)##$##^$#(#####2$#_$#$##&##3$####C$#a$#%##1##C#####5$#P##$##b$#8$####'##c$#$##)##c#####,##+##$##e$#%#####d##&##$##Q##'#####.##h$#(##j$#=$####J##2##$##&##f#####%##k$#$##l$#,#####y$#-##$##n$#*#####0##o$#$##R##A$####=##q$#%##+##i#####D$#&##$##r$#E$####(##t$#$##v$#'#####F$#w$#$##&##%#####N##+##$##-##0#####I$#{$#L##)##K$####*##W##$##|$#O#####%###%#$##1##.#####'##&##$##%%#(#####M$#&%#$##/%#*#####n##(%#%##&##'#####P$#Y##$##+##,#####/#"
theorem range_1(n:Nat)(hnB:9≤n∧n≤BOUND)(hlo:265≤n)(hhi:n<521):a n>0:=by
  have hc:checkCode 265 255 code_1.toList=true:=by decide +kernel
  exact checkCode_sound hc hnB hlo (by omega)

def code_2:String:="#*%#$##,%#r#####Q$#1##$##3##%#####.##)##$##[##$$####U$#&##(##0%#V$####'##]##$##1%#t#####%##-##$##&##X$####u##3%#$##)##=#####Z$#4%#$##`##[$####S##7%#%##8%#*#####,##2##$##9%#0#####(##&##$##+##V#####`$#<%#$##-##%#####'##=%#$##&##y#####4##?%#/##A%#,#####{##E##$##B%#'#####%##)##$##D%#d$####*##E%#$##G%#(#####f$#&##$##2##g$#####$#1##%##J%#X#####i$#b##$##&##*#####'##L%#$##M%#4#####.##N%#$##+##%#####%$#O%#$##e##'#####,##R%#(##Q%#m$####Z##&##$##3##&$####%##+##$##S%#p$####9##U%#$##&##/#####*##V%#$##g##,#####'##)##%##X%#($####s$#h##$##1##u$####(##Y%#$##-##'#####x$#&##$##[%#%#####^##3##$##)##,$####z$#^%#m##&##.#####.$#2##$##_%#9#####%##1##$##a%#}$####'##+##$##b%#(#####,##d%#$##j##$%####*##&##%##f%#'#####7##k##$##g%#'%####.##h%#$##&##2$####)%#)##$##i%#%#####3$#l%#$##2##C$"
theorem range_2(n:Nat)(hnB:9≤n∧n≤BOUND)(hlo:521≤n)(hhi:n<777):a n>0:=by
  have hc:checkCode 521 255 code_2.toList=true:=by decide +kernel
  exact checkCode_sound hc hnB hlo (by omega)

def code_3:String:="####+%#-##(##+##0#####=##l##$##n%#5$####%##&##$##)##-%####8$#o%#$##1##'#####.%#+##$##&##7#####c##q%#%##r%#5#####*##o##$##-##2%####(##u%#$##t%#d#####,##w%#$##x%#%#####'##&##$##q##.#####5%#{%#/##6##6%####=$#)##$##&##'#####%##3##$##|%#,#####f###&#$##$&#(#####:%#%&#$##s##;%####5##+##%##)##k%####.##&##$##(&#>%####'##*&#$##+&#0#####@%#,&#$##&##%#####A$#-##$##v##=#####C%#6##(##1##*#####i##w##$##/&#D$####%##0&#$##+##F%####E$#&##$##1&#/#####H%#)##$##2##I%####'##3&#%##&##F$####K%#E##$##4&#,#####(##6&#$##3##'#####*##7&#$##)##%#####0##8&#$##x##I$####P%#&##L##8##7#####K$#z##$##;&#*#####%##<&#$##&##T%####'##>&#$##+##(#####W%#?&#$##|##0#####.##3##%##A&#'#####,##}##$##C&#Z%####/##&##$##1##M$####]%#-##$##F&#%#####*##G&#$##&##n#####`%#H&#(##I&#,#####'##2##$##)##P$####%##L&#$#"
theorem range_3(n:Nat)(hnB:9≤n∧n≤BOUND)(hlo:777≤n)(hhi:n<1033):a n>0:=by
  have hc:checkCode 777 255 code_3.toList=true:=by decide +kernel
  exact checkCode_sound hc hnB hlo (by omega)

def code_4:String:="#K&#*#####5##1##$##N&#'#####c%#&##$##-##e%####r##O&#%##Q&#Q$####0##S&#$##&##4#####(##T&#$##R&#.#####7##+##$##V&#%#####'##6##$##2##U$####*##)##/##3##j%####V$#&##$##Y&#'#####%##Z&#$##^&#m%####t##]&#$##&##(#####.##`&#$##)##,#####X$#a&#%##+##u#####p%#'$#$##c&#7#####=##-##$##f&#Z$####s%#&##$##i&#%#####[$#+##$##*$#'#####v%#1##(##&##y%####*##+$#$##8##5#####%##k&#$##m&#z%####0##)##$##-##/#####,##o&#$##-$#*#####'##&##%##q&#`$####}%#2##$##+##.#####(##r&#$##&##'#####&&#u&#$##6##%#####y##t&#$##0$#4#####'&#+##L##v&#)&####5##1$#$##1##{#####%##&##$##z&#-&####'##y&#$##3##(#####7##|&#$##&##.&####d$##'#%##%'#*#####D&#)##$##('#2&####/##1##$##+##f$####,##6##$##*'#%#####g$#&##$##4$##$####0##,'#(##)##5&####'##3##$##&##i$####%##8##$##-##,#####*##1'#$##0'#'#####9&#3'#$##6$#:&####4#"
theorem range_4(n:Nat)(hnB:9≤n∧n≤BOUND)(hlo:1033≤n)(hhi:n<1289):a n>0:=by
  have hc:checkCode 1033 255 code_4.toList=true:=by decide +kernel
  exact checkCode_sound hc hnB hlo (by omega)

def code_5:String:="#6'#%##4'#.#####=&#&##$##;'#*#####(##8'#$##:'#%$####@&#<'#$##&##%#####'##)##$##9$#5#####B&#>'#/##?'#E&####m$#2##$##A'#'#####%##+##$##8##4#####&$#&##$##)##(#####*##1##$##;$#J&####p$#-##%##&##9#####M&#<$#$##3##,#####'##F'#$##6##*#####P&#E'#$##?##%#####5##H'#$##2##'#####7##&##(##I'#X&####($#>$#$##-##s$####%##)##$##&##0#####u$#+##$##J'#/#####W&#3##$##?$#@#####'##L'#%##1##x$####,##@$#$##)##[&####(##&##$##O'#'#####4##N'#$##P'#%#####,$#['#$##&##z$####_&#Q'#m##+##,#####.##U##$##Y'#.$####%##o'#$##_'#b&####9##8##$##h'#(#####0##&##$##B$#d&####}$#)##%##Z'#'#####*##2##$##&##g&####/##S'#$##T'#5#####h&#f'#$##]'#%#####$%#m'#$##)##*#####,##R'#(##-##e&####'##&##$##+##9#####%##p'#$##1##l&####'%#<##$##&##'#####j&#i'#$##2##,#####2$#+##%##U'#)%####7##G$#$##6##n&####(##3##$##q'#3$"
