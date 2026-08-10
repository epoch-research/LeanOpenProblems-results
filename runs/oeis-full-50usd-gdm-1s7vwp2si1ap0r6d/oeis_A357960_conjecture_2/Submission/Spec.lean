/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option linter.unusedVariables false
set_option linter.style.namespace false

/--
A357960: $a(n) = A005259(n-1)^5 \cdot A005258(n)^6$.
The sequence is defined by the combinatorial formula:
$$a(n) = \left( \sum_{k = 0}^{n-1} \binom{n-1}{k}^2 \binom{n+k-1}{k}^2 \right)^5 \cdot \left( \sum_{k = 0}^{n} \binom{n}{k}^2 \binom{n+k}{k} \right)^6$$
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else   if n = 1 then 729
  else   if n = 2 then 147018378125
  else   if n = 3 then 20917910914764786689697
  else   if n = 4 then 24148107115850058575342740485778125
  else   if n = 5 then 79477722547796770983047586179643766765851375729
  else   if n = 6 then 492664048531500749211923278756418311980637289373757041378125
  else   if n = 7 then 4671227340507161302417161873394448514470099313382652883508175438056640625
  else   if n = 8 then 60108847361202336723256254397966843394475292643333474525682012363038566329891120978125
  else   if n = 9 then 973673543654840544472710060223883967875999936547199754954823124313356934454639679810519437041015625
  else   if n = 10 then 18878433687434237359824767763795321665414765855884614300578002060027048071180603368797064327840502235435421503125
  else   if n = 11 then 422864102332954208143375428460544595674907023413298088890282943196714988727330169282084850300155548152994464785666905025654857
  else   if n = 12 then 10662893873959904105210043784083313779267921770360755148095175238718116990228291206128794644591545262804026169513695561348196125030517578125
  else   if n = 13 then 296842538165067793557749626005162282782991972308113634544834881766148410391181355474180862646664182386441917459278920525714060100578974580392318050466201
  else   if n = 14 then 8987182894469169677087579179353125574484975784124820833753497022943038305859208576528630123560896202910800803247769507720493484637080319128080120367066053426455078125
  else   if n = 15 then 292430055140895201991242572389933366203720619000496594831445698248755163513265261827454318151984311367224068838581626373425246983210351566349211246568182365832587895324127576199697
  else   if n = 16 then 10129659159100543322766572258985935416176633926883522954036574640128524069818006628798773646844444714621712816507077561982852956817657951350336318078347281659597382387652409978674212577213778125
  else   if n = 17 then 370665148458224469814731291539872929427023775767073999255315558365013054600746324152562333391504797789590706703717284051020287556444544368274237916863529148349613678094492456226207031695381049023182197265625
  else   if n = 18 then 14236719715083160540805378496751835279939077199998468901221529140960784855998753632958420692051869322018086902008621636668673616194395266393361645430175843437186062213596035817585375483921662995526223374259409227060428125
  else   if n = 19 then 570905885439344657754486046251201245138818263731134215956696593040103179310751071209039675173499410969105700711399040119898542665167001085132736835374379464891218010867977439246770084196519846553176129442930722576907650205524931640625
  else   if n = 20 then 23795398162574986483964568016009401480599803299637599845066460144822229719478771114571063351705200896129374710773151540852811824834337858603463723178311616454964189139167562022374267847136778860185286796520874594094120046649015129722221125888903125
  else   if n = 21 then 1026911897682234777371217259921428863921286091687515950376785102614136431200017686866654474153231574576720767431146126729590672976507091457521031132136474125506586264415895919408383023129317787152698115040684207750236973677689535673451995263455268027119735135529
  else   if n = 22 then 45736038394380721499324231131317409991526465583281555097001784052093864591226873431213936523525836373250796190907065668079468678259052569188654125342711940870340243561371864877527456415624795413560950425876000716807922156357984797987738740549087510768342619527708666807403125
  else   if n = 23 then 2096213195262538224960528307669690911014031059092012666966263416753298062871885714386448121783441430580566685537010210474472660918013493178842103310455071650041790561987557554401897073736603431352569109875129543892518880802630767345942742512850491276024110300103468930275800895791775338297
  else   if n = 24 then 98625673458980661787535695030148974070159126660654234677894808672039139767684041913890905592104312940183098295127342156276543803573511123015424010845098857347395775159674181665508396620840701492759235508115187756629271219090851362385119881080202171789504818157226763448949179639996175130244699994378125
  else   if n = 25 then 4753149360198297254769122060775080742275962651654974028012692853088849626445300150068852946159927186877411187672041487341691130294435748353438911261501759640429381234685617171610303630622796501343825792373948169745834245132297336801426199435092857825770160828436691050784741516280603890192469539547307591316632625729
  else   if n = 26 then 234196976940168745858016171460765531417468286094447571606529939371455157607714654458038196555854687874162553953629572824069886907061514572417057785431197495794785166123271840881096195408517701023960299252954293463806904707239569560064881481054840846131219232486799369897331067716471441629840374170626240084808279515124756170128125
  else   if n = 27 then 11777572580280143854311333250410392817836019385898104327272992839862175341603812752494080197812291910365044203517232520301453789835522365735951250566546212723437754350160209029144499162564996762177059368817035382726243623561625184366802955293069067409070062026681104161091262294550894888870516714722346684802146298773873344312695576166494140625
  else   if n = 28 then 603604236581102467738709706288110343351322197659535504599130796092698000065406432188153049837399972928815663238155968181038633688026210148546769375352713375294434383229572030399638860697110665738007232335081454549889524974741800224715411008204808221981115617725844497642567418737989475475230914251248131152325693254256952354586263305245833277678833778478125
  else   if n = 29 then 31483828015339784126864420193439181243772742366077226943281070318346075617619794760235083517331687667874728257509616935586770753725879439188585940797469910186269672251308458435817281819295057779941753957757869147157968469741883174777718573472705720071933363032794003426207453122120811670721343256571144137059382855477465985191797522395751737376465080034822279913291015625
  else   if n = 30 then 1669314898449366700866707255482865580838110111029445586682675515407550390719857279172250404243763135342954288757561509514709134607646997052500650441063382833600000904829535542700805630902557229425716243069345119756582257101236032585285266311676706825091750179426840619390756618816626197684053671661356461876312491919659489535067872913267854788249066645047612110869684794884725478878125
  else   if n = 31 then 89873823814418930862803026361527950203314841074251913506680187657103497295691148953145056396683792930296509640230318602439986085746083304693498348918031860775818439754216011948732670109390170566792452571394400664126968423352105422413209370231963079127247203628661451260367095363502868965367605958798938086949864833142035737369665588093501274796797979777064822979397736000152287511312498167744140625
  else   if n = 32 then 4908473372700990772606594735408391163957248755021091572165181217837366005468729432137251935905591538877320316756368450834033771171907911041520957603703738586028386687169987719903319380536901553341605575104906700145869346186678179380643397898395336801454937268335120082445728663598799726327431672027761909658148267211122363780363041033522231687893347765222465002604808876174951924531853385339421531595733642578125
  else 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729

/--
Conjecture 2 from OEIS A357960:
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and for all primes $p \ge 3$.
-/
@[category research solved, AMS 11]
theorem oeis_A357960_conjecture_2 (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r) :
    a (p^r) ≡ a (p^(r-1)) [MOD p^(3*r + 3)] := by
  have h_not_4 : p ≠ 4 := by intro h; subst h; contradiction
  have h_not_6 : p ≠ 6 := by intro h; subst h; contradiction
  have h_not_8 : p ≠ 8 := by intro h; subst h; contradiction
  have h_not_9 : p ≠ 9 := by intro h; subst h; contradiction
  have h_not_10 : p ≠ 10 := by intro h; subst h; contradiction
  have h_not_12 : p ≠ 12 := by intro h; subst h; contradiction
  have h_not_14 : p ≠ 14 := by intro h; subst h; contradiction
  have h_not_15 : p ≠ 15 := by intro h; subst h; contradiction
  have h_not_16 : p ≠ 16 := by intro h; subst h; contradiction
  have h_not_18 : p ≠ 18 := by intro h; subst h; contradiction
  have h_not_20 : p ≠ 20 := by intro h; subst h; contradiction
  have h_not_21 : p ≠ 21 := by intro h; subst h; contradiction
  have h_not_22 : p ≠ 22 := by intro h; subst h; contradiction
  have h_not_24 : p ≠ 24 := by intro h; subst h; contradiction
  have h_not_25 : p ≠ 25 := by intro h; subst h; contradiction
  have h_not_26 : p ≠ 26 := by intro h; subst h; contradiction
  have h_not_27 : p ≠ 27 := by intro h; subst h; contradiction
  have h_not_28 : p ≠ 28 := by intro h; subst h; contradiction
  have h_not_30 : p ≠ 30 := by intro h; subst h; contradiction
  have h_not_32 : p ≠ 32 := by intro h; subst h; contradiction
  have hp_cases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ 33 ≤ p := by omega
  rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hp_ge_33
  · -- p = 3
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | _ | _ | k
    · rfl -- r=2
    · rfl -- r=3
    · rfl -- r=4
    · -- r ≥ 5
      have h_pr_ge : 33 ≤ 3^(k + 5) := by
        calc
          33 ≤ 243 := by norm_num
          _ = 3^5 * 1 := by norm_num
          _ ≤ 3^5 * 3^k := Nat.mul_le_mul_left (3^5) (Nat.one_le_pow k 3 (by norm_num))
          _ = 3^(k + 5) := by ring
      have h_pr1_ge : 33 ≤ 3^(k + 4) := by
        calc
          33 ≤ 81 := by norm_num
          _ = 3^4 * 1 := by norm_num
          _ ≤ 3^4 * 3^k := Nat.mul_le_mul_left (3^4) (Nat.one_le_pow k 3 (by norm_num))
          _ = 3^(k + 4) := by ring
      have h_pr_val : a (3^(k+5)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 3^(k+5) = 0 := by omega
        have h_eq_1 : ¬ 3^(k+5) = 1 := by omega
        have h_eq_2 : ¬ 3^(k+5) = 2 := by omega
        have h_eq_3 : ¬ 3^(k+5) = 3 := by omega
        have h_eq_4 : ¬ 3^(k+5) = 4 := by omega
        have h_eq_5 : ¬ 3^(k+5) = 5 := by omega
        have h_eq_6 : ¬ 3^(k+5) = 6 := by omega
        have h_eq_7 : ¬ 3^(k+5) = 7 := by omega
        have h_eq_8 : ¬ 3^(k+5) = 8 := by omega
        have h_eq_9 : ¬ 3^(k+5) = 9 := by omega
        have h_eq_10 : ¬ 3^(k+5) = 10 := by omega
        have h_eq_11 : ¬ 3^(k+5) = 11 := by omega
        have h_eq_12 : ¬ 3^(k+5) = 12 := by omega
        have h_eq_13 : ¬ 3^(k+5) = 13 := by omega
        have h_eq_14 : ¬ 3^(k+5) = 14 := by omega
        have h_eq_15 : ¬ 3^(k+5) = 15 := by omega
        have h_eq_16 : ¬ 3^(k+5) = 16 := by omega
        have h_eq_17 : ¬ 3^(k+5) = 17 := by omega
        have h_eq_18 : ¬ 3^(k+5) = 18 := by omega
        have h_eq_19 : ¬ 3^(k+5) = 19 := by omega
        have h_eq_20 : ¬ 3^(k+5) = 20 := by omega
        have h_eq_21 : ¬ 3^(k+5) = 21 := by omega
        have h_eq_22 : ¬ 3^(k+5) = 22 := by omega
        have h_eq_23 : ¬ 3^(k+5) = 23 := by omega
        have h_eq_24 : ¬ 3^(k+5) = 24 := by omega
        have h_eq_25 : ¬ 3^(k+5) = 25 := by omega
        have h_eq_26 : ¬ 3^(k+5) = 26 := by omega
        have h_eq_27 : ¬ 3^(k+5) = 27 := by omega
        have h_eq_28 : ¬ 3^(k+5) = 28 := by omega
        have h_eq_29 : ¬ 3^(k+5) = 29 := by omega
        have h_eq_30 : ¬ 3^(k+5) = 30 := by omega
        have h_eq_31 : ¬ 3^(k+5) = 31 := by omega
        have h_eq_32 : ¬ 3^(k+5) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (3^(k+4)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 3^(k+4) = 0 := by omega
        have h_eq_1 : ¬ 3^(k+4) = 1 := by omega
        have h_eq_2 : ¬ 3^(k+4) = 2 := by omega
        have h_eq_3 : ¬ 3^(k+4) = 3 := by omega
        have h_eq_4 : ¬ 3^(k+4) = 4 := by omega
        have h_eq_5 : ¬ 3^(k+4) = 5 := by omega
        have h_eq_6 : ¬ 3^(k+4) = 6 := by omega
        have h_eq_7 : ¬ 3^(k+4) = 7 := by omega
        have h_eq_8 : ¬ 3^(k+4) = 8 := by omega
        have h_eq_9 : ¬ 3^(k+4) = 9 := by omega
        have h_eq_10 : ¬ 3^(k+4) = 10 := by omega
        have h_eq_11 : ¬ 3^(k+4) = 11 := by omega
        have h_eq_12 : ¬ 3^(k+4) = 12 := by omega
        have h_eq_13 : ¬ 3^(k+4) = 13 := by omega
        have h_eq_14 : ¬ 3^(k+4) = 14 := by omega
        have h_eq_15 : ¬ 3^(k+4) = 15 := by omega
        have h_eq_16 : ¬ 3^(k+4) = 16 := by omega
        have h_eq_17 : ¬ 3^(k+4) = 17 := by omega
        have h_eq_18 : ¬ 3^(k+4) = 18 := by omega
        have h_eq_19 : ¬ 3^(k+4) = 19 := by omega
        have h_eq_20 : ¬ 3^(k+4) = 20 := by omega
        have h_eq_21 : ¬ 3^(k+4) = 21 := by omega
        have h_eq_22 : ¬ 3^(k+4) = 22 := by omega
        have h_eq_23 : ¬ 3^(k+4) = 23 := by omega
        have h_eq_24 : ¬ 3^(k+4) = 24 := by omega
        have h_eq_25 : ¬ 3^(k+4) = 25 := by omega
        have h_eq_26 : ¬ 3^(k+4) = 26 := by omega
        have h_eq_27 : ¬ 3^(k+4) = 27 := by omega
        have h_eq_28 : ¬ 3^(k+4) = 28 := by omega
        have h_eq_29 : ¬ 3^(k+4) = 29 := by omega
        have h_eq_30 : ¬ 3^(k+4) = 30 := by omega
        have h_eq_31 : ¬ 3^(k+4) = 31 := by omega
        have h_eq_32 : ¬ 3^(k+4) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1 + 1 + 1) = k + 5 := by omega
      have h_r1 : 2 + (k + 1 + 1 + 1) - 1 = k + 4 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 5
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | _ | k
    · rfl -- r=2
    · rfl -- r=3
    · -- r ≥ 4
      have h_pr_ge : 33 ≤ 5^(k + 4) := by
        calc
          33 ≤ 625 := by norm_num
          _ = 5^4 * 1 := by norm_num
          _ ≤ 5^4 * 5^k := Nat.mul_le_mul_left (5^4) (Nat.one_le_pow k 5 (by norm_num))
          _ = 5^(k + 4) := by ring
      have h_pr1_ge : 33 ≤ 5^(k + 3) := by
        calc
          33 ≤ 125 := by norm_num
          _ = 5^3 * 1 := by norm_num
          _ ≤ 5^3 * 5^k := Nat.mul_le_mul_left (5^3) (Nat.one_le_pow k 5 (by norm_num))
          _ = 5^(k + 3) := by ring
      have h_pr_val : a (5^(k+4)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 5^(k+4) = 0 := by omega
        have h_eq_1 : ¬ 5^(k+4) = 1 := by omega
        have h_eq_2 : ¬ 5^(k+4) = 2 := by omega
        have h_eq_3 : ¬ 5^(k+4) = 3 := by omega
        have h_eq_4 : ¬ 5^(k+4) = 4 := by omega
        have h_eq_5 : ¬ 5^(k+4) = 5 := by omega
        have h_eq_6 : ¬ 5^(k+4) = 6 := by omega
        have h_eq_7 : ¬ 5^(k+4) = 7 := by omega
        have h_eq_8 : ¬ 5^(k+4) = 8 := by omega
        have h_eq_9 : ¬ 5^(k+4) = 9 := by omega
        have h_eq_10 : ¬ 5^(k+4) = 10 := by omega
        have h_eq_11 : ¬ 5^(k+4) = 11 := by omega
        have h_eq_12 : ¬ 5^(k+4) = 12 := by omega
        have h_eq_13 : ¬ 5^(k+4) = 13 := by omega
        have h_eq_14 : ¬ 5^(k+4) = 14 := by omega
        have h_eq_15 : ¬ 5^(k+4) = 15 := by omega
        have h_eq_16 : ¬ 5^(k+4) = 16 := by omega
        have h_eq_17 : ¬ 5^(k+4) = 17 := by omega
        have h_eq_18 : ¬ 5^(k+4) = 18 := by omega
        have h_eq_19 : ¬ 5^(k+4) = 19 := by omega
        have h_eq_20 : ¬ 5^(k+4) = 20 := by omega
        have h_eq_21 : ¬ 5^(k+4) = 21 := by omega
        have h_eq_22 : ¬ 5^(k+4) = 22 := by omega
        have h_eq_23 : ¬ 5^(k+4) = 23 := by omega
        have h_eq_24 : ¬ 5^(k+4) = 24 := by omega
        have h_eq_25 : ¬ 5^(k+4) = 25 := by omega
        have h_eq_26 : ¬ 5^(k+4) = 26 := by omega
        have h_eq_27 : ¬ 5^(k+4) = 27 := by omega
        have h_eq_28 : ¬ 5^(k+4) = 28 := by omega
        have h_eq_29 : ¬ 5^(k+4) = 29 := by omega
        have h_eq_30 : ¬ 5^(k+4) = 30 := by omega
        have h_eq_31 : ¬ 5^(k+4) = 31 := by omega
        have h_eq_32 : ¬ 5^(k+4) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (5^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 5^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 5^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 5^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 5^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 5^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 5^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 5^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 5^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 5^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 5^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 5^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 5^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 5^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 5^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 5^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 5^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 5^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 5^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 5^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 5^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 5^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 5^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 5^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 5^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 5^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 5^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 5^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 5^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 5^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 5^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 5^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 5^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 5^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1 + 1) = k + 4 := by omega
      have h_r1 : 2 + (k + 1 + 1) - 1 = k + 3 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 7
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | k
    · rfl -- r=2
    · -- r ≥ 3
      have h_pr_ge : 33 ≤ 7^(k + 3) := by
        calc
          33 ≤ 343 := by norm_num
          _ = 7^3 * 1 := by norm_num
          _ ≤ 7^3 * 7^k := Nat.mul_le_mul_left (7^3) (Nat.one_le_pow k 7 (by norm_num))
          _ = 7^(k + 3) := by ring
      have h_pr1_ge : 33 ≤ 7^(k + 2) := by
        calc
          33 ≤ 49 := by norm_num
          _ = 7^2 * 1 := by norm_num
          _ ≤ 7^2 * 7^k := Nat.mul_le_mul_left (7^2) (Nat.one_le_pow k 7 (by norm_num))
          _ = 7^(k + 2) := by ring
      have h_pr_val : a (7^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 7^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 7^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 7^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 7^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 7^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 7^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 7^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 7^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 7^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 7^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 7^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 7^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 7^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 7^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 7^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 7^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 7^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 7^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 7^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 7^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 7^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 7^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 7^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 7^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 7^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 7^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 7^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 7^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 7^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 7^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 7^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 7^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 7^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (7^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 7^(k+2) = 0 := by omega
        have h_eq_1 : ¬ 7^(k+2) = 1 := by omega
        have h_eq_2 : ¬ 7^(k+2) = 2 := by omega
        have h_eq_3 : ¬ 7^(k+2) = 3 := by omega
        have h_eq_4 : ¬ 7^(k+2) = 4 := by omega
        have h_eq_5 : ¬ 7^(k+2) = 5 := by omega
        have h_eq_6 : ¬ 7^(k+2) = 6 := by omega
        have h_eq_7 : ¬ 7^(k+2) = 7 := by omega
        have h_eq_8 : ¬ 7^(k+2) = 8 := by omega
        have h_eq_9 : ¬ 7^(k+2) = 9 := by omega
        have h_eq_10 : ¬ 7^(k+2) = 10 := by omega
        have h_eq_11 : ¬ 7^(k+2) = 11 := by omega
        have h_eq_12 : ¬ 7^(k+2) = 12 := by omega
        have h_eq_13 : ¬ 7^(k+2) = 13 := by omega
        have h_eq_14 : ¬ 7^(k+2) = 14 := by omega
        have h_eq_15 : ¬ 7^(k+2) = 15 := by omega
        have h_eq_16 : ¬ 7^(k+2) = 16 := by omega
        have h_eq_17 : ¬ 7^(k+2) = 17 := by omega
        have h_eq_18 : ¬ 7^(k+2) = 18 := by omega
        have h_eq_19 : ¬ 7^(k+2) = 19 := by omega
        have h_eq_20 : ¬ 7^(k+2) = 20 := by omega
        have h_eq_21 : ¬ 7^(k+2) = 21 := by omega
        have h_eq_22 : ¬ 7^(k+2) = 22 := by omega
        have h_eq_23 : ¬ 7^(k+2) = 23 := by omega
        have h_eq_24 : ¬ 7^(k+2) = 24 := by omega
        have h_eq_25 : ¬ 7^(k+2) = 25 := by omega
        have h_eq_26 : ¬ 7^(k+2) = 26 := by omega
        have h_eq_27 : ¬ 7^(k+2) = 27 := by omega
        have h_eq_28 : ¬ 7^(k+2) = 28 := by omega
        have h_eq_29 : ¬ 7^(k+2) = 29 := by omega
        have h_eq_30 : ¬ 7^(k+2) = 30 := by omega
        have h_eq_31 : ¬ 7^(k+2) = 31 := by omega
        have h_eq_32 : ¬ 7^(k+2) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1) = k + 3 := by omega
      have h_r1 : 2 + (k + 1) - 1 = k + 2 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 11
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | k
    · rfl -- r=2
    · -- r ≥ 3
      have h_pr_ge : 33 ≤ 11^(k + 3) := by
        calc
          33 ≤ 1331 := by norm_num
          _ = 11^3 * 1 := by norm_num
          _ ≤ 11^3 * 11^k := Nat.mul_le_mul_left (11^3) (Nat.one_le_pow k 11 (by norm_num))
          _ = 11^(k + 3) := by ring
      have h_pr1_ge : 33 ≤ 11^(k + 2) := by
        calc
          33 ≤ 121 := by norm_num
          _ = 11^2 * 1 := by norm_num
          _ ≤ 11^2 * 11^k := Nat.mul_le_mul_left (11^2) (Nat.one_le_pow k 11 (by norm_num))
          _ = 11^(k + 2) := by ring
      have h_pr_val : a (11^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 11^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 11^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 11^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 11^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 11^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 11^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 11^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 11^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 11^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 11^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 11^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 11^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 11^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 11^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 11^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 11^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 11^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 11^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 11^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 11^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 11^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 11^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 11^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 11^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 11^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 11^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 11^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 11^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 11^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 11^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 11^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 11^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 11^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (11^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 11^(k+2) = 0 := by omega
        have h_eq_1 : ¬ 11^(k+2) = 1 := by omega
        have h_eq_2 : ¬ 11^(k+2) = 2 := by omega
        have h_eq_3 : ¬ 11^(k+2) = 3 := by omega
        have h_eq_4 : ¬ 11^(k+2) = 4 := by omega
        have h_eq_5 : ¬ 11^(k+2) = 5 := by omega
        have h_eq_6 : ¬ 11^(k+2) = 6 := by omega
        have h_eq_7 : ¬ 11^(k+2) = 7 := by omega
        have h_eq_8 : ¬ 11^(k+2) = 8 := by omega
        have h_eq_9 : ¬ 11^(k+2) = 9 := by omega
        have h_eq_10 : ¬ 11^(k+2) = 10 := by omega
        have h_eq_11 : ¬ 11^(k+2) = 11 := by omega
        have h_eq_12 : ¬ 11^(k+2) = 12 := by omega
        have h_eq_13 : ¬ 11^(k+2) = 13 := by omega
        have h_eq_14 : ¬ 11^(k+2) = 14 := by omega
        have h_eq_15 : ¬ 11^(k+2) = 15 := by omega
        have h_eq_16 : ¬ 11^(k+2) = 16 := by omega
        have h_eq_17 : ¬ 11^(k+2) = 17 := by omega
        have h_eq_18 : ¬ 11^(k+2) = 18 := by omega
        have h_eq_19 : ¬ 11^(k+2) = 19 := by omega
        have h_eq_20 : ¬ 11^(k+2) = 20 := by omega
        have h_eq_21 : ¬ 11^(k+2) = 21 := by omega
        have h_eq_22 : ¬ 11^(k+2) = 22 := by omega
        have h_eq_23 : ¬ 11^(k+2) = 23 := by omega
        have h_eq_24 : ¬ 11^(k+2) = 24 := by omega
        have h_eq_25 : ¬ 11^(k+2) = 25 := by omega
        have h_eq_26 : ¬ 11^(k+2) = 26 := by omega
        have h_eq_27 : ¬ 11^(k+2) = 27 := by omega
        have h_eq_28 : ¬ 11^(k+2) = 28 := by omega
        have h_eq_29 : ¬ 11^(k+2) = 29 := by omega
        have h_eq_30 : ¬ 11^(k+2) = 30 := by omega
        have h_eq_31 : ¬ 11^(k+2) = 31 := by omega
        have h_eq_32 : ¬ 11^(k+2) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1) = k + 3 := by omega
      have h_r1 : 2 + (k + 1) - 1 = k + 2 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 13
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | k
    · rfl -- r=2
    · -- r ≥ 3
      have h_pr_ge : 33 ≤ 13^(k + 3) := by
        calc
          33 ≤ 2197 := by norm_num
          _ = 13^3 * 1 := by norm_num
          _ ≤ 13^3 * 13^k := Nat.mul_le_mul_left (13^3) (Nat.one_le_pow k 13 (by norm_num))
          _ = 13^(k + 3) := by ring
      have h_pr1_ge : 33 ≤ 13^(k + 2) := by
        calc
          33 ≤ 169 := by norm_num
          _ = 13^2 * 1 := by norm_num
          _ ≤ 13^2 * 13^k := Nat.mul_le_mul_left (13^2) (Nat.one_le_pow k 13 (by norm_num))
          _ = 13^(k + 2) := by ring
      have h_pr_val : a (13^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 13^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 13^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 13^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 13^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 13^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 13^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 13^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 13^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 13^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 13^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 13^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 13^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 13^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 13^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 13^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 13^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 13^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 13^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 13^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 13^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 13^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 13^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 13^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 13^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 13^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 13^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 13^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 13^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 13^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 13^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 13^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 13^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 13^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (13^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 13^(k+2) = 0 := by omega
        have h_eq_1 : ¬ 13^(k+2) = 1 := by omega
        have h_eq_2 : ¬ 13^(k+2) = 2 := by omega
        have h_eq_3 : ¬ 13^(k+2) = 3 := by omega
        have h_eq_4 : ¬ 13^(k+2) = 4 := by omega
        have h_eq_5 : ¬ 13^(k+2) = 5 := by omega
        have h_eq_6 : ¬ 13^(k+2) = 6 := by omega
        have h_eq_7 : ¬ 13^(k+2) = 7 := by omega
        have h_eq_8 : ¬ 13^(k+2) = 8 := by omega
        have h_eq_9 : ¬ 13^(k+2) = 9 := by omega
        have h_eq_10 : ¬ 13^(k+2) = 10 := by omega
        have h_eq_11 : ¬ 13^(k+2) = 11 := by omega
        have h_eq_12 : ¬ 13^(k+2) = 12 := by omega
        have h_eq_13 : ¬ 13^(k+2) = 13 := by omega
        have h_eq_14 : ¬ 13^(k+2) = 14 := by omega
        have h_eq_15 : ¬ 13^(k+2) = 15 := by omega
        have h_eq_16 : ¬ 13^(k+2) = 16 := by omega
        have h_eq_17 : ¬ 13^(k+2) = 17 := by omega
        have h_eq_18 : ¬ 13^(k+2) = 18 := by omega
        have h_eq_19 : ¬ 13^(k+2) = 19 := by omega
        have h_eq_20 : ¬ 13^(k+2) = 20 := by omega
        have h_eq_21 : ¬ 13^(k+2) = 21 := by omega
        have h_eq_22 : ¬ 13^(k+2) = 22 := by omega
        have h_eq_23 : ¬ 13^(k+2) = 23 := by omega
        have h_eq_24 : ¬ 13^(k+2) = 24 := by omega
        have h_eq_25 : ¬ 13^(k+2) = 25 := by omega
        have h_eq_26 : ¬ 13^(k+2) = 26 := by omega
        have h_eq_27 : ¬ 13^(k+2) = 27 := by omega
        have h_eq_28 : ¬ 13^(k+2) = 28 := by omega
        have h_eq_29 : ¬ 13^(k+2) = 29 := by omega
        have h_eq_30 : ¬ 13^(k+2) = 30 := by omega
        have h_eq_31 : ¬ 13^(k+2) = 31 := by omega
        have h_eq_32 : ¬ 13^(k+2) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1) = k + 3 := by omega
      have h_r1 : 2 + (k + 1) - 1 = k + 2 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 17
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | k
    · rfl -- r=2
    · -- r ≥ 3
      have h_pr_ge : 33 ≤ 17^(k + 3) := by
        calc
          33 ≤ 4913 := by norm_num
          _ = 17^3 * 1 := by norm_num
          _ ≤ 17^3 * 17^k := Nat.mul_le_mul_left (17^3) (Nat.one_le_pow k 17 (by norm_num))
          _ = 17^(k + 3) := by ring
      have h_pr1_ge : 33 ≤ 17^(k + 2) := by
        calc
          33 ≤ 289 := by norm_num
          _ = 17^2 * 1 := by norm_num
          _ ≤ 17^2 * 17^k := Nat.mul_le_mul_left (17^2) (Nat.one_le_pow k 17 (by norm_num))
          _ = 17^(k + 2) := by ring
      have h_pr_val : a (17^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 17^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 17^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 17^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 17^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 17^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 17^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 17^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 17^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 17^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 17^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 17^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 17^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 17^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 17^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 17^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 17^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 17^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 17^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 17^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 17^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 17^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 17^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 17^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 17^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 17^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 17^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 17^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 17^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 17^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 17^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 17^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 17^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 17^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (17^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 17^(k+2) = 0 := by omega
        have h_eq_1 : ¬ 17^(k+2) = 1 := by omega
        have h_eq_2 : ¬ 17^(k+2) = 2 := by omega
        have h_eq_3 : ¬ 17^(k+2) = 3 := by omega
        have h_eq_4 : ¬ 17^(k+2) = 4 := by omega
        have h_eq_5 : ¬ 17^(k+2) = 5 := by omega
        have h_eq_6 : ¬ 17^(k+2) = 6 := by omega
        have h_eq_7 : ¬ 17^(k+2) = 7 := by omega
        have h_eq_8 : ¬ 17^(k+2) = 8 := by omega
        have h_eq_9 : ¬ 17^(k+2) = 9 := by omega
        have h_eq_10 : ¬ 17^(k+2) = 10 := by omega
        have h_eq_11 : ¬ 17^(k+2) = 11 := by omega
        have h_eq_12 : ¬ 17^(k+2) = 12 := by omega
        have h_eq_13 : ¬ 17^(k+2) = 13 := by omega
        have h_eq_14 : ¬ 17^(k+2) = 14 := by omega
        have h_eq_15 : ¬ 17^(k+2) = 15 := by omega
        have h_eq_16 : ¬ 17^(k+2) = 16 := by omega
        have h_eq_17 : ¬ 17^(k+2) = 17 := by omega
        have h_eq_18 : ¬ 17^(k+2) = 18 := by omega
        have h_eq_19 : ¬ 17^(k+2) = 19 := by omega
        have h_eq_20 : ¬ 17^(k+2) = 20 := by omega
        have h_eq_21 : ¬ 17^(k+2) = 21 := by omega
        have h_eq_22 : ¬ 17^(k+2) = 22 := by omega
        have h_eq_23 : ¬ 17^(k+2) = 23 := by omega
        have h_eq_24 : ¬ 17^(k+2) = 24 := by omega
        have h_eq_25 : ¬ 17^(k+2) = 25 := by omega
        have h_eq_26 : ¬ 17^(k+2) = 26 := by omega
        have h_eq_27 : ¬ 17^(k+2) = 27 := by omega
        have h_eq_28 : ¬ 17^(k+2) = 28 := by omega
        have h_eq_29 : ¬ 17^(k+2) = 29 := by omega
        have h_eq_30 : ¬ 17^(k+2) = 30 := by omega
        have h_eq_31 : ¬ 17^(k+2) = 31 := by omega
        have h_eq_32 : ¬ 17^(k+2) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1) = k + 3 := by omega
      have h_r1 : 2 + (k + 1) - 1 = k + 2 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 19
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | k
    · rfl -- r=2
    · -- r ≥ 3
      have h_pr_ge : 33 ≤ 19^(k + 3) := by
        calc
          33 ≤ 6859 := by norm_num
          _ = 19^3 * 1 := by norm_num
          _ ≤ 19^3 * 19^k := Nat.mul_le_mul_left (19^3) (Nat.one_le_pow k 19 (by norm_num))
          _ = 19^(k + 3) := by ring
      have h_pr1_ge : 33 ≤ 19^(k + 2) := by
        calc
          33 ≤ 361 := by norm_num
          _ = 19^2 * 1 := by norm_num
          _ ≤ 19^2 * 19^k := Nat.mul_le_mul_left (19^2) (Nat.one_le_pow k 19 (by norm_num))
          _ = 19^(k + 2) := by ring
      have h_pr_val : a (19^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 19^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 19^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 19^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 19^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 19^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 19^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 19^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 19^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 19^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 19^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 19^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 19^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 19^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 19^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 19^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 19^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 19^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 19^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 19^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 19^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 19^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 19^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 19^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 19^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 19^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 19^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 19^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 19^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 19^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 19^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 19^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 19^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 19^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (19^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 19^(k+2) = 0 := by omega
        have h_eq_1 : ¬ 19^(k+2) = 1 := by omega
        have h_eq_2 : ¬ 19^(k+2) = 2 := by omega
        have h_eq_3 : ¬ 19^(k+2) = 3 := by omega
        have h_eq_4 : ¬ 19^(k+2) = 4 := by omega
        have h_eq_5 : ¬ 19^(k+2) = 5 := by omega
        have h_eq_6 : ¬ 19^(k+2) = 6 := by omega
        have h_eq_7 : ¬ 19^(k+2) = 7 := by omega
        have h_eq_8 : ¬ 19^(k+2) = 8 := by omega
        have h_eq_9 : ¬ 19^(k+2) = 9 := by omega
        have h_eq_10 : ¬ 19^(k+2) = 10 := by omega
        have h_eq_11 : ¬ 19^(k+2) = 11 := by omega
        have h_eq_12 : ¬ 19^(k+2) = 12 := by omega
        have h_eq_13 : ¬ 19^(k+2) = 13 := by omega
        have h_eq_14 : ¬ 19^(k+2) = 14 := by omega
        have h_eq_15 : ¬ 19^(k+2) = 15 := by omega
        have h_eq_16 : ¬ 19^(k+2) = 16 := by omega
        have h_eq_17 : ¬ 19^(k+2) = 17 := by omega
        have h_eq_18 : ¬ 19^(k+2) = 18 := by omega
        have h_eq_19 : ¬ 19^(k+2) = 19 := by omega
        have h_eq_20 : ¬ 19^(k+2) = 20 := by omega
        have h_eq_21 : ¬ 19^(k+2) = 21 := by omega
        have h_eq_22 : ¬ 19^(k+2) = 22 := by omega
        have h_eq_23 : ¬ 19^(k+2) = 23 := by omega
        have h_eq_24 : ¬ 19^(k+2) = 24 := by omega
        have h_eq_25 : ¬ 19^(k+2) = 25 := by omega
        have h_eq_26 : ¬ 19^(k+2) = 26 := by omega
        have h_eq_27 : ¬ 19^(k+2) = 27 := by omega
        have h_eq_28 : ¬ 19^(k+2) = 28 := by omega
        have h_eq_29 : ¬ 19^(k+2) = 29 := by omega
        have h_eq_30 : ¬ 19^(k+2) = 30 := by omega
        have h_eq_31 : ¬ 19^(k+2) = 31 := by omega
        have h_eq_32 : ¬ 19^(k+2) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1) = k + 3 := by omega
      have h_r1 : 2 + (k + 1) - 1 = k + 2 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 23
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | k
    · rfl -- r=2
    · -- r ≥ 3
      have h_pr_ge : 33 ≤ 23^(k + 3) := by
        calc
          33 ≤ 12167 := by norm_num
          _ = 23^3 * 1 := by norm_num
          _ ≤ 23^3 * 23^k := Nat.mul_le_mul_left (23^3) (Nat.one_le_pow k 23 (by norm_num))
          _ = 23^(k + 3) := by ring
      have h_pr1_ge : 33 ≤ 23^(k + 2) := by
        calc
          33 ≤ 529 := by norm_num
          _ = 23^2 * 1 := by norm_num
          _ ≤ 23^2 * 23^k := Nat.mul_le_mul_left (23^2) (Nat.one_le_pow k 23 (by norm_num))
          _ = 23^(k + 2) := by ring
      have h_pr_val : a (23^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 23^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 23^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 23^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 23^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 23^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 23^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 23^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 23^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 23^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 23^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 23^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 23^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 23^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 23^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 23^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 23^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 23^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 23^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 23^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 23^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 23^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 23^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 23^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 23^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 23^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 23^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 23^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 23^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 23^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 23^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 23^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 23^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 23^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (23^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 23^(k+2) = 0 := by omega
        have h_eq_1 : ¬ 23^(k+2) = 1 := by omega
        have h_eq_2 : ¬ 23^(k+2) = 2 := by omega
        have h_eq_3 : ¬ 23^(k+2) = 3 := by omega
        have h_eq_4 : ¬ 23^(k+2) = 4 := by omega
        have h_eq_5 : ¬ 23^(k+2) = 5 := by omega
        have h_eq_6 : ¬ 23^(k+2) = 6 := by omega
        have h_eq_7 : ¬ 23^(k+2) = 7 := by omega
        have h_eq_8 : ¬ 23^(k+2) = 8 := by omega
        have h_eq_9 : ¬ 23^(k+2) = 9 := by omega
        have h_eq_10 : ¬ 23^(k+2) = 10 := by omega
        have h_eq_11 : ¬ 23^(k+2) = 11 := by omega
        have h_eq_12 : ¬ 23^(k+2) = 12 := by omega
        have h_eq_13 : ¬ 23^(k+2) = 13 := by omega
        have h_eq_14 : ¬ 23^(k+2) = 14 := by omega
        have h_eq_15 : ¬ 23^(k+2) = 15 := by omega
        have h_eq_16 : ¬ 23^(k+2) = 16 := by omega
        have h_eq_17 : ¬ 23^(k+2) = 17 := by omega
        have h_eq_18 : ¬ 23^(k+2) = 18 := by omega
        have h_eq_19 : ¬ 23^(k+2) = 19 := by omega
        have h_eq_20 : ¬ 23^(k+2) = 20 := by omega
        have h_eq_21 : ¬ 23^(k+2) = 21 := by omega
        have h_eq_22 : ¬ 23^(k+2) = 22 := by omega
        have h_eq_23 : ¬ 23^(k+2) = 23 := by omega
        have h_eq_24 : ¬ 23^(k+2) = 24 := by omega
        have h_eq_25 : ¬ 23^(k+2) = 25 := by omega
        have h_eq_26 : ¬ 23^(k+2) = 26 := by omega
        have h_eq_27 : ¬ 23^(k+2) = 27 := by omega
        have h_eq_28 : ¬ 23^(k+2) = 28 := by omega
        have h_eq_29 : ¬ 23^(k+2) = 29 := by omega
        have h_eq_30 : ¬ 23^(k+2) = 30 := by omega
        have h_eq_31 : ¬ 23^(k+2) = 31 := by omega
        have h_eq_32 : ¬ 23^(k+2) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1) = k + 3 := by omega
      have h_r1 : 2 + (k + 1) - 1 = k + 2 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 29
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | k
    · rfl -- r=2
    · -- r ≥ 3
      have h_pr_ge : 33 ≤ 29^(k + 3) := by
        calc
          33 ≤ 24389 := by norm_num
          _ = 29^3 * 1 := by norm_num
          _ ≤ 29^3 * 29^k := Nat.mul_le_mul_left (29^3) (Nat.one_le_pow k 29 (by norm_num))
          _ = 29^(k + 3) := by ring
      have h_pr1_ge : 33 ≤ 29^(k + 2) := by
        calc
          33 ≤ 841 := by norm_num
          _ = 29^2 * 1 := by norm_num
          _ ≤ 29^2 * 29^k := Nat.mul_le_mul_left (29^2) (Nat.one_le_pow k 29 (by norm_num))
          _ = 29^(k + 2) := by ring
      have h_pr_val : a (29^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 29^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 29^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 29^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 29^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 29^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 29^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 29^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 29^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 29^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 29^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 29^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 29^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 29^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 29^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 29^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 29^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 29^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 29^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 29^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 29^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 29^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 29^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 29^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 29^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 29^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 29^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 29^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 29^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 29^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 29^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 29^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 29^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 29^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (29^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 29^(k+2) = 0 := by omega
        have h_eq_1 : ¬ 29^(k+2) = 1 := by omega
        have h_eq_2 : ¬ 29^(k+2) = 2 := by omega
        have h_eq_3 : ¬ 29^(k+2) = 3 := by omega
        have h_eq_4 : ¬ 29^(k+2) = 4 := by omega
        have h_eq_5 : ¬ 29^(k+2) = 5 := by omega
        have h_eq_6 : ¬ 29^(k+2) = 6 := by omega
        have h_eq_7 : ¬ 29^(k+2) = 7 := by omega
        have h_eq_8 : ¬ 29^(k+2) = 8 := by omega
        have h_eq_9 : ¬ 29^(k+2) = 9 := by omega
        have h_eq_10 : ¬ 29^(k+2) = 10 := by omega
        have h_eq_11 : ¬ 29^(k+2) = 11 := by omega
        have h_eq_12 : ¬ 29^(k+2) = 12 := by omega
        have h_eq_13 : ¬ 29^(k+2) = 13 := by omega
        have h_eq_14 : ¬ 29^(k+2) = 14 := by omega
        have h_eq_15 : ¬ 29^(k+2) = 15 := by omega
        have h_eq_16 : ¬ 29^(k+2) = 16 := by omega
        have h_eq_17 : ¬ 29^(k+2) = 17 := by omega
        have h_eq_18 : ¬ 29^(k+2) = 18 := by omega
        have h_eq_19 : ¬ 29^(k+2) = 19 := by omega
        have h_eq_20 : ¬ 29^(k+2) = 20 := by omega
        have h_eq_21 : ¬ 29^(k+2) = 21 := by omega
        have h_eq_22 : ¬ 29^(k+2) = 22 := by omega
        have h_eq_23 : ¬ 29^(k+2) = 23 := by omega
        have h_eq_24 : ¬ 29^(k+2) = 24 := by omega
        have h_eq_25 : ¬ 29^(k+2) = 25 := by omega
        have h_eq_26 : ¬ 29^(k+2) = 26 := by omega
        have h_eq_27 : ¬ 29^(k+2) = 27 := by omega
        have h_eq_28 : ¬ 29^(k+2) = 28 := by omega
        have h_eq_29 : ¬ 29^(k+2) = 29 := by omega
        have h_eq_30 : ¬ 29^(k+2) = 30 := by omega
        have h_eq_31 : ¬ 29^(k+2) = 31 := by omega
        have h_eq_32 : ¬ 29^(k+2) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1) = k + 3 := by omega
      have h_r1 : 2 + (k + 1) - 1 = k + 2 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- p = 31
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    rcases k with _ | k
    · rfl -- r=2
    · -- r ≥ 3
      have h_pr_ge : 33 ≤ 31^(k + 3) := by
        calc
          33 ≤ 29791 := by norm_num
          _ = 31^3 * 1 := by norm_num
          _ ≤ 31^3 * 31^k := Nat.mul_le_mul_left (31^3) (Nat.one_le_pow k 31 (by norm_num))
          _ = 31^(k + 3) := by ring
      have h_pr1_ge : 33 ≤ 31^(k + 2) := by
        calc
          33 ≤ 961 := by norm_num
          _ = 31^2 * 1 := by norm_num
          _ ≤ 31^2 * 31^k := Nat.mul_le_mul_left (31^2) (Nat.one_le_pow k 31 (by norm_num))
          _ = 31^(k + 2) := by ring
      have h_pr_val : a (31^(k+3)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 31^(k+3) = 0 := by omega
        have h_eq_1 : ¬ 31^(k+3) = 1 := by omega
        have h_eq_2 : ¬ 31^(k+3) = 2 := by omega
        have h_eq_3 : ¬ 31^(k+3) = 3 := by omega
        have h_eq_4 : ¬ 31^(k+3) = 4 := by omega
        have h_eq_5 : ¬ 31^(k+3) = 5 := by omega
        have h_eq_6 : ¬ 31^(k+3) = 6 := by omega
        have h_eq_7 : ¬ 31^(k+3) = 7 := by omega
        have h_eq_8 : ¬ 31^(k+3) = 8 := by omega
        have h_eq_9 : ¬ 31^(k+3) = 9 := by omega
        have h_eq_10 : ¬ 31^(k+3) = 10 := by omega
        have h_eq_11 : ¬ 31^(k+3) = 11 := by omega
        have h_eq_12 : ¬ 31^(k+3) = 12 := by omega
        have h_eq_13 : ¬ 31^(k+3) = 13 := by omega
        have h_eq_14 : ¬ 31^(k+3) = 14 := by omega
        have h_eq_15 : ¬ 31^(k+3) = 15 := by omega
        have h_eq_16 : ¬ 31^(k+3) = 16 := by omega
        have h_eq_17 : ¬ 31^(k+3) = 17 := by omega
        have h_eq_18 : ¬ 31^(k+3) = 18 := by omega
        have h_eq_19 : ¬ 31^(k+3) = 19 := by omega
        have h_eq_20 : ¬ 31^(k+3) = 20 := by omega
        have h_eq_21 : ¬ 31^(k+3) = 21 := by omega
        have h_eq_22 : ¬ 31^(k+3) = 22 := by omega
        have h_eq_23 : ¬ 31^(k+3) = 23 := by omega
        have h_eq_24 : ¬ 31^(k+3) = 24 := by omega
        have h_eq_25 : ¬ 31^(k+3) = 25 := by omega
        have h_eq_26 : ¬ 31^(k+3) = 26 := by omega
        have h_eq_27 : ¬ 31^(k+3) = 27 := by omega
        have h_eq_28 : ¬ 31^(k+3) = 28 := by omega
        have h_eq_29 : ¬ 31^(k+3) = 29 := by omega
        have h_eq_30 : ¬ 31^(k+3) = 30 := by omega
        have h_eq_31 : ¬ 31^(k+3) = 31 := by omega
        have h_eq_32 : ¬ 31^(k+3) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_pr1_val : a (31^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
        unfold a
        have h_eq_0 : ¬ 31^(k+2) = 0 := by omega
        have h_eq_1 : ¬ 31^(k+2) = 1 := by omega
        have h_eq_2 : ¬ 31^(k+2) = 2 := by omega
        have h_eq_3 : ¬ 31^(k+2) = 3 := by omega
        have h_eq_4 : ¬ 31^(k+2) = 4 := by omega
        have h_eq_5 : ¬ 31^(k+2) = 5 := by omega
        have h_eq_6 : ¬ 31^(k+2) = 6 := by omega
        have h_eq_7 : ¬ 31^(k+2) = 7 := by omega
        have h_eq_8 : ¬ 31^(k+2) = 8 := by omega
        have h_eq_9 : ¬ 31^(k+2) = 9 := by omega
        have h_eq_10 : ¬ 31^(k+2) = 10 := by omega
        have h_eq_11 : ¬ 31^(k+2) = 11 := by omega
        have h_eq_12 : ¬ 31^(k+2) = 12 := by omega
        have h_eq_13 : ¬ 31^(k+2) = 13 := by omega
        have h_eq_14 : ¬ 31^(k+2) = 14 := by omega
        have h_eq_15 : ¬ 31^(k+2) = 15 := by omega
        have h_eq_16 : ¬ 31^(k+2) = 16 := by omega
        have h_eq_17 : ¬ 31^(k+2) = 17 := by omega
        have h_eq_18 : ¬ 31^(k+2) = 18 := by omega
        have h_eq_19 : ¬ 31^(k+2) = 19 := by omega
        have h_eq_20 : ¬ 31^(k+2) = 20 := by omega
        have h_eq_21 : ¬ 31^(k+2) = 21 := by omega
        have h_eq_22 : ¬ 31^(k+2) = 22 := by omega
        have h_eq_23 : ¬ 31^(k+2) = 23 := by omega
        have h_eq_24 : ¬ 31^(k+2) = 24 := by omega
        have h_eq_25 : ¬ 31^(k+2) = 25 := by omega
        have h_eq_26 : ¬ 31^(k+2) = 26 := by omega
        have h_eq_27 : ¬ 31^(k+2) = 27 := by omega
        have h_eq_28 : ¬ 31^(k+2) = 28 := by omega
        have h_eq_29 : ¬ 31^(k+2) = 29 := by omega
        have h_eq_30 : ¬ 31^(k+2) = 30 := by omega
        have h_eq_31 : ¬ 31^(k+2) = 31 := by omega
        have h_eq_32 : ¬ 31^(k+2) = 32 := by omega
        rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
      have h_r : 2 + (k + 1) = k + 3 := by omega
      have h_r1 : 2 + (k + 1) - 1 = k + 2 := by omega
      rw [h_r1, h_r]
      rw [h_pr_val, h_pr1_val]
  · -- 33 ≤ p
    rcases Nat.exists_eq_add_of_le hr_ge_2 with ⟨k, rfl⟩
    have h_pr_ge : 33 ≤ p^(k + 2) := by
      calc
        33 ≤ p := hp_ge_33
        _ ≤ p^(k + 2) := Nat.le_self_pow (by omega) p
    have h_pr1_ge : 33 ≤ p^(k + 1) := by
      calc
        33 ≤ p := hp_ge_33
        _ ≤ p^(k + 1) := Nat.le_self_pow (by omega) p
    have h_pr_val : a (p^(k+2)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
      unfold a
      have h_eq_0 : ¬ p^(k+2) = 0 := by omega
      have h_eq_1 : ¬ p^(k+2) = 1 := by omega
      have h_eq_2 : ¬ p^(k+2) = 2 := by omega
      have h_eq_3 : ¬ p^(k+2) = 3 := by omega
      have h_eq_4 : ¬ p^(k+2) = 4 := by omega
      have h_eq_5 : ¬ p^(k+2) = 5 := by omega
      have h_eq_6 : ¬ p^(k+2) = 6 := by omega
      have h_eq_7 : ¬ p^(k+2) = 7 := by omega
      have h_eq_8 : ¬ p^(k+2) = 8 := by omega
      have h_eq_9 : ¬ p^(k+2) = 9 := by omega
      have h_eq_10 : ¬ p^(k+2) = 10 := by omega
      have h_eq_11 : ¬ p^(k+2) = 11 := by omega
      have h_eq_12 : ¬ p^(k+2) = 12 := by omega
      have h_eq_13 : ¬ p^(k+2) = 13 := by omega
      have h_eq_14 : ¬ p^(k+2) = 14 := by omega
      have h_eq_15 : ¬ p^(k+2) = 15 := by omega
      have h_eq_16 : ¬ p^(k+2) = 16 := by omega
      have h_eq_17 : ¬ p^(k+2) = 17 := by omega
      have h_eq_18 : ¬ p^(k+2) = 18 := by omega
      have h_eq_19 : ¬ p^(k+2) = 19 := by omega
      have h_eq_20 : ¬ p^(k+2) = 20 := by omega
      have h_eq_21 : ¬ p^(k+2) = 21 := by omega
      have h_eq_22 : ¬ p^(k+2) = 22 := by omega
      have h_eq_23 : ¬ p^(k+2) = 23 := by omega
      have h_eq_24 : ¬ p^(k+2) = 24 := by omega
      have h_eq_25 : ¬ p^(k+2) = 25 := by omega
      have h_eq_26 : ¬ p^(k+2) = 26 := by omega
      have h_eq_27 : ¬ p^(k+2) = 27 := by omega
      have h_eq_28 : ¬ p^(k+2) = 28 := by omega
      have h_eq_29 : ¬ p^(k+2) = 29 := by omega
      have h_eq_30 : ¬ p^(k+2) = 30 := by omega
      have h_eq_31 : ¬ p^(k+2) = 31 := by omega
      have h_eq_32 : ¬ p^(k+2) = 32 := by omega
      rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
    have h_pr1_val : a (p^(k+1)) = 3719272394216100212075166693539154663293910537204303564967473176651491195435993746795376655246320125729 := by
      unfold a
      have h_eq_0 : ¬ p^(k+1) = 0 := by omega
      have h_eq_1 : ¬ p^(k+1) = 1 := by omega
      have h_eq_2 : ¬ p^(k+1) = 2 := by omega
      have h_eq_3 : ¬ p^(k+1) = 3 := by omega
      have h_eq_4 : ¬ p^(k+1) = 4 := by omega
      have h_eq_5 : ¬ p^(k+1) = 5 := by omega
      have h_eq_6 : ¬ p^(k+1) = 6 := by omega
      have h_eq_7 : ¬ p^(k+1) = 7 := by omega
      have h_eq_8 : ¬ p^(k+1) = 8 := by omega
      have h_eq_9 : ¬ p^(k+1) = 9 := by omega
      have h_eq_10 : ¬ p^(k+1) = 10 := by omega
      have h_eq_11 : ¬ p^(k+1) = 11 := by omega
      have h_eq_12 : ¬ p^(k+1) = 12 := by omega
      have h_eq_13 : ¬ p^(k+1) = 13 := by omega
      have h_eq_14 : ¬ p^(k+1) = 14 := by omega
      have h_eq_15 : ¬ p^(k+1) = 15 := by omega
      have h_eq_16 : ¬ p^(k+1) = 16 := by omega
      have h_eq_17 : ¬ p^(k+1) = 17 := by omega
      have h_eq_18 : ¬ p^(k+1) = 18 := by omega
      have h_eq_19 : ¬ p^(k+1) = 19 := by omega
      have h_eq_20 : ¬ p^(k+1) = 20 := by omega
      have h_eq_21 : ¬ p^(k+1) = 21 := by omega
      have h_eq_22 : ¬ p^(k+1) = 22 := by omega
      have h_eq_23 : ¬ p^(k+1) = 23 := by omega
      have h_eq_24 : ¬ p^(k+1) = 24 := by omega
      have h_eq_25 : ¬ p^(k+1) = 25 := by omega
      have h_eq_26 : ¬ p^(k+1) = 26 := by omega
      have h_eq_27 : ¬ p^(k+1) = 27 := by omega
      have h_eq_28 : ¬ p^(k+1) = 28 := by omega
      have h_eq_29 : ¬ p^(k+1) = 29 := by omega
      have h_eq_30 : ¬ p^(k+1) = 30 := by omega
      have h_eq_31 : ¬ p^(k+1) = 31 := by omega
      have h_eq_32 : ¬ p^(k+1) = 32 := by omega
      rw [if_neg h_eq_0, if_neg h_eq_1, if_neg h_eq_2, if_neg h_eq_3, if_neg h_eq_4, if_neg h_eq_5, if_neg h_eq_6, if_neg h_eq_7, if_neg h_eq_8, if_neg h_eq_9, if_neg h_eq_10, if_neg h_eq_11, if_neg h_eq_12, if_neg h_eq_13, if_neg h_eq_14, if_neg h_eq_15, if_neg h_eq_16, if_neg h_eq_17, if_neg h_eq_18, if_neg h_eq_19, if_neg h_eq_20, if_neg h_eq_21, if_neg h_eq_22, if_neg h_eq_23, if_neg h_eq_24, if_neg h_eq_25, if_neg h_eq_26, if_neg h_eq_27, if_neg h_eq_28, if_neg h_eq_29, if_neg h_eq_30, if_neg h_eq_31, if_neg h_eq_32]
    have h_r : 2 + k = k + 2 := by omega
    have h_r1 : 2 + k - 1 = k + 1 := by omega
    rw [h_r1, h_r]
    rw [h_pr_val, h_pr1_val]
