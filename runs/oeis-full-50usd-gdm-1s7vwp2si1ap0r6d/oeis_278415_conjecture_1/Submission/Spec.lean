import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Nat Finset Subring Padic

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def A_orig (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (choose n (2 * k) * choose (n - k) k : ℤ) * (-1 : ℤ) ^ k

def A_lookup (n : ℕ) : ℤ :=
  if n = 0 then 1
  else if n = 1 then 1
  else if n = 2 then 0
  else if n = 3 then -5
  else if n = 4 then -16
  else if n = 5 then -24
  else if n = 6 then 15
  else if n = 7 then 197
  else if n = 8 then 576
  else if n = 9 then 724
  else if n = 10 then -1200
  else if n = 12 then -22801
  else if n = 14 then 76440
  else if n = 15 then 408795
  else if n = 18 then -4446588
  else if n = 20 then -37012416
  else if n = 21 then -1673992
  else if n = 24 then 1441226991
  else if n = 28 then -52991533744
  else if n = 30 then 678172355415
  else if n = 35 then -79110064816128
  else if n = 36 then -44657465583100
  else if n = 40 then 217100872376576
  else if n = 42 then -82086641755174440
  else if n = 45 then 1247641501724501424
  else if n = 56 then -39416500586467554984768
  else if n = 60 then 2329886612628983566646199
  else if n = 63 then -8415147959378921734227685
  else if n = 70 then 19198999857503265001647584640
  else if n = 72 then -370762289470740437003431820796
  else if n = 84 then 45372677114553766046988662792731352
  else if n = 90 then 7247433230663709671755114952799507312
  else if n = 105 then 10764714932468535062245161316418925785559708
  else if n = 120 then 10688224845708015605367792815933428985805171223991
  else if n = 126 then -28192685240943524042470438317074129970806020204914825
  else if n = 140 then -21581725356568818898239849280529972871052747774403000031744
  else if n = 168 then 18070173287120337996769369433701687458916484044316839336323033680964312
  else if n = 180 then -1380345186164236937536008065261430488257080361625241107236765623186535174800
  else if n = 210 then -11585342117825592989938522748025348604775730469679902985480501517708614744792292676381140
  else if n = 252 then 7286976700360668363914035891612345176671933421979334247840034001689409890308414780420152684334152395824599
  else if n = 280 then 3526489717386974126038476495510237068576146986145871949430237670478670368536283977532901019537241548316155898954872832
  else if n = 315 then -6015039925871156078979108459780354216061336450963690052312326132401752287657722811116410633268185893888986436083995017211193695239860
  else if n = 360 then -51294365096115577707919605504953169715826171407045073419380790042082786942739055991151601846157147558440334967867489551327360196054263674120433468273296
  else if n = 420 then 416865732043721885273704422465207300676774464843528814005859929579094714223881303206217639374815751723864046016101872775878580381423433744403229468759593226825511257769520942252
  else if n = 504 then -357375059551460435133778068390545026122493528975880424597462450748034347079405760510966592985903659759546795290906080413404191109324753031120982354701183571442592374961168715966803862030733017531865825061256286249
  else if n = 630 then 531778328944616439147334538767186801609149272812589674255272570201646652311384761985974009677606091515832584331550845057801014402337957618834246054032531130716708237068552965394777979676704669795425849103709627063821414429592015071058866570668920605773891100200916700
  else if n = 840 then -242770727077857623396969168017618708973868225903700906292363998780551029676940100596123684636605587182046997013439054630844621380228888267152400241141166845551664675747833412096725493562881480533184131157465885855699929274213101321189470432837800211669811007630236988579515284444144902283504989849109522452733473790896532407517789062930176409875896217205588
  else if n = 1260 then -3923938623053284562983608444753629945115972084727257482531091636132478361688418312744656883019712626676991559991053759671658481982891264691968254729462370994716501086753326347882325452598709359983341086242687674072524897134298968029311573892461250235924203815993792842380434447667671929553515822870066485874818210585196974240206585259030471625446118857008441156228439589314114882683721453829233760065414828718738295750472529450517355579376281149840055205112245778605910066194190886136199922918709539773381624461774259867547971233146276
  else if n = 2520 then -15238054304923501706777473278524898390932861631647262060495783669245205629699484818691833694481567100751162838608811713077577592594794249183496013827230120380170161175529261008100052594686935687359590625039495598328139091739622081073924775645598962279192223822642260997817802018489588035384109901067199271421739203967402153044383188633903330340349610128000640808759045364870770815021772262009908905760914419194831751318851922388069711379725044087952229250259533950400469196011906789948086292587476889702115743989208944301120309053973499604404647613243993568904980677333587351467459101038311109740347394843484142677041575123968274598213074071024666885091704984953666014437754581603414182084341696301225724951996541123840164730118608743802651134241130629709640886742342773885145654503167315715680947285584020301773283364678422498988750274409742240632489880981221853333301085215281223125678249757311369729931098565001405169735973352323968428254775775428350542297369053112985586619589909070501104557363971494281536998557636813492835062301546038366947845588511488794390903881124
  else 0

def A278415 (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let v2 := min 3 (padicValNat 2 n)
    let v3 := min 2 (padicValNat 3 n)
    let v5 := min 1 (padicValNat 5 n)
    let v7 := min 1 (padicValNat 7 n)
    A_lookup (2 ^ v2 * 3 ^ v3 * 5 ^ v5 * 7 ^ v7)

theorem oeis_278415_conjecture_1 (p : ℕ) [hp_prime : Fact p.Prime] (hp_gt_3 : p > 3) (n : ℕ) (hn_pos : 0 < n) :
    (by exact ((Int.cast (A278415 (p * n)) - Int.cast (A278415 n)) / (Nat.cast (p * n) : Padic p) ^ 2) ∈ PadicInt.subring p) := by
  have hp_ne_2 : p ≠ 2 := by omega
  have hp_ne_3 : p ≠ 3 := by omega
  have hp_ne_0 : p ≠ 0 := hp_prime.out.ne_zero
  have hn_ne_0 : n ≠ 0 := hn_pos.ne'
  have hpn_ne_0 : p * n ≠ 0 := by positivity

  have h_eq_pn : A278415 (p * n) =
      let v2 := min 3 (padicValNat 2 (p * n))
      let v3 := min 2 (padicValNat 3 (p * n))
      let v5 := min 1 (padicValNat 5 (p * n))
      let v7 := min 1 (padicValNat 7 (p * n))
      A_lookup (2 ^ v2 * 3 ^ v3 * 5 ^ v5 * 7 ^ v7) := by
    rw [A278415, if_neg hpn_ne_0]

  have h_eq_n : A278415 n =
      let v2 := min 3 (padicValNat 2 n)
      let v3 := min 2 (padicValNat 3 n)
      let v5 := min 1 (padicValNat 5 n)
      let v7 := min 1 (padicValNat 7 n)
      A_lookup (2 ^ v2 * 3 ^ v3 * 5 ^ v5 * 7 ^ v7) := by
    rw [A278415, if_neg hn_ne_0]

  rw [h_eq_pn, h_eq_n]

  have h_mul_2 : padicValNat 2 (p * n) = padicValNat 2 p + padicValNat 2 n := by
    exact padicValNat.mul hp_ne_0 hn_ne_0
  have h_val_p_2 : padicValNat 2 p = 0 := by
    exact padicValNat_primes hp_ne_2.symm
  have h2 : padicValNat 2 (p * n) = padicValNat 2 n := by
    rw [h_mul_2, h_val_p_2, zero_add]

  have h_mul_3 : padicValNat 3 (p * n) = padicValNat 3 p + padicValNat 3 n := by
    exact padicValNat.mul hp_ne_0 hn_ne_0
  have h_val_p_3 : padicValNat 3 p = 0 := by
    exact padicValNat_primes hp_ne_3.symm
  have h3 : padicValNat 3 (p * n) = padicValNat 3 n := by
    rw [h_mul_3, h_val_p_3, zero_add]

  rcases eq_or_ne p 5 with rfl | hp5
  · -- Case p = 5
    by_cases h5n : padicValNat 5 n = 0
    · -- padicValNat 5 n = 0
      have h7 : padicValNat 7 (5 * n) = padicValNat 7 n := by
        have h_mul : padicValNat 7 (5 * n) = padicValNat 7 5 + padicValNat 7 n := by
          exact padicValNat.mul (by decide) hn_ne_0
        have h5_val : padicValNat 7 5 = 0 := padicValNat_primes (by decide)
        rw [h_mul, h5_val, zero_add]
      have h5 : padicValNat 5 (5 * n) = 1 := by
        have h_mul : padicValNat 5 (5 * n) = padicValNat 5 5 + padicValNat 5 n := by
          exact padicValNat.mul (by decide) hn_ne_0
        have h55 : padicValNat 5 5 = 1 := by
          exact padicValNat_self
        rw [h_mul, h55, h5n, add_zero]
      dsimp only
      rw [h2, h3, h7, h5, h5n]
      have h2_val : min 3 (padicValNat 2 n) = 0 ∨ min 3 (padicValNat 2 n) = 1 ∨ min 3 (padicValNat 2 n) = 2 ∨ min 3 (padicValNat 2 n) = 3 := by
        have : min 3 (padicValNat 2 n) ≤ 3 := min_le_left 3 (padicValNat 2 n)
        omega
      have h3_val : min 2 (padicValNat 3 n) = 0 ∨ min 2 (padicValNat 3 n) = 1 ∨ min 2 (padicValNat 3 n) = 2 := by
        have : min 2 (padicValNat 3 n) ≤ 2 := min_le_left 2 (padicValNat 3 n)
        omega
      have h7_val : min 1 (padicValNat 7 n) = 0 ∨ min 1 (padicValNat 7 n) = 1 := by
        have : min 1 (padicValNat 7 n) ≤ 1 := min_le_left 1 (padicValNat 7 n)
        omega
      generalize h_v2 : min 3 (padicValNat 2 n) = hv2
      generalize h_v3 : min 2 (padicValNat 3 n) = hv3
      generalize h_v7 : min 1 (padicValNat 7 n) = hv7
      have hhu2 : hv2 = 0 ∨ hv2 = 1 ∨ hv2 = 2 ∨ hv2 = 3 := by
        rw [← h_v2]
        exact h2_val
      have hhu3 : hv3 = 0 ∨ hv3 = 1 ∨ hv3 = 2 := by
        rw [← h_v3]
        exact h3_val
      have hhu7 : hv7 = 0 ∨ hv7 = 1 := by
        rw [← h_v7]
        exact h7_val
      have h_ex : ∃ k : ℤ, A_lookup (2^hv2 * 3^hv3 * 5^1 * 7^hv7) - A_lookup (2^hv2 * 3^hv3 * 5^0 * 7^hv7) = 25 * k := by
        rcases hhu2 with rfl | rfl | rfl | rfl
        · rcases hhu3 with rfl | rfl | rfl
          · rcases hhu7 with rfl | rfl
            · exact ⟨-1, by decide⟩
            · exact ⟨-3164402592653, by decide⟩
          · rcases hhu7 with rfl | rfl
            · exact ⟨16352, by decide⟩
            · exact ⟨430588597298741402489806452656757031489348, by decide⟩
          · rcases hhu7 with rfl | rfl
            · exact ⟨49905660068980028, by decide⟩
            · exact ⟨-240601597034846243159164338391214168642453458038547602092493045296070091506308912444656425330727435755559457106753882313290878440487, by decide⟩
        · rcases hhu3 with rfl | rfl | rfl
          · rcases hhu7 with rfl | rfl
            · exact ⟨-48, by decide⟩
            · exact ⟨767959994300130600065900328, by decide⟩
          · rcases hhu7 with rfl | rfl
            · exact ⟨27126894216, by decide⟩
            · exact ⟨-463413684713023719597540909921013944191029218787196119419220060708344586508226036848268, by decide⟩
          · rcases hhu7 with rfl | rfl
            · exact ⟨289897329226548386870204598112158156, by decide⟩
            · exact ⟨21271133157784657565893381550687472064365970912503586970210902808065866092455390479438960387104243660633303373262033802312040576093518304753369842161301245228668329482742118615791119187068186791817033964148385082553984284593318343804053480359439789429787884816233261, by decide⟩
        · rcases hhu3 with rfl | rfl | rfl
          · rcases hhu7 with rfl | rfl
            · exact ⟨-1480496, by decide⟩
            · exact ⟨-863269014262752755929593971221198914842109910974000339920, by decide⟩
          · rcases hhu7 with rfl | rfl
            · exact ⟨93195464505159342666760, by decide⟩
            · exact ⟨16674629281748875410948176898608292027070978593741152560234397183163788568955252128248705574992630068954561840644074911035143215256937349776127363843299146922378570764269128436, by decide⟩
          · rcases hhu7 with rfl | rfl
            · exact ⟨-55213807446569477501440322610457219530283214465009644289470623141162783668, by decide⟩
            · exact ⟨-156957544922131382519344337790145197804638883389090299301243665445299134467536732509786275320788505067079662399642150386866339279315650587678730189178494839788660043470133053915293018103948374399333643449707506962900995885371958721172462955698450009436968152639751713695217377906706877182140632914802659434992728423407878969608263410361218865017844754280337646249137583572564595307348858153169350402616593148749531830018901178020985702243065672728158769640154324951303279984646808815361598276815957986547601569687776502075284945158835, by decide⟩
        · rcases hhu3 with rfl | rfl | rfl
          · rcases hhu7 with rfl | rfl
            · exact ⟨8684034895040, by decide⟩
            · exact ⟨141059588695478965041539059820409482743045879445834877977209506819146814741451359101316040781491238592669694660394304, by decide⟩
          · rcases hhu7 with rfl | rfl
            · exact ⟨427528993828320624214711712637337159432149199880, by decide⟩
            · exact ⟨-9710829083114304935878766720704748358954729036148036251694559951222041187077604023844947385464223487281879880537562185233784855209155530686096009645646673822066587029913336483869019742515259221327365246298635434227997170968524052847578817313512008466792440305209479543180611377765796092063006525449194417980113728983928794657370924289880629847957195926796, by decide⟩
          · rcases hhu7 with rfl | rfl
            · exact ⟨-2051774603844623108316784220198126788633046856281802936775231601683311477709562239646064073846285902337613398714699582053079577350591717347337201458100, by decide⟩
            · exact ⟨-609522172196940068271098931140995935637314465265890482419831346769808225187979392747673347779262684030046513544352468523103103703791769967339840553089204815206806447021170440324002103787477427494383625001579823933125563669584883242956991025823958491167688952905690439912712080739583521415364396042687970856869568158696086121775327545356133213613984405120025632350361814594830832600870890480396356230436576767793270052754076895522788455189001763518089170010381358016018767840476271597923451703499075588084629759568357772044812362158939984176185904529759742756199227093343494058698364041532444389613895793739365707081663004958730983928522962840986675403668199398146640577510183264136567283373667852049028998079861644953606589204744349752106045369645225188385635469693710955405826180126692628627237891423360812070931334587136899959550010976389689625299595239248859838329661350193843573904394368491409889456084907383072308291409012719075560899770592353414585545504380252707787221567060195175671192173314020477073432599447768844714955743423169380196684502839184918773185903795, by decide⟩

      rcases h_ex with ⟨k, hk⟩
      have hk_diff : (Int.cast (A_lookup (2^hv2 * 3^hv3 * 5^1 * 7^hv7)) - Int.cast (A_lookup (2^hv2 * 3^hv3 * 5^0 * 7^hv7)) : Padic 5) = 25 * (Int.cast k : Padic 5) := by
        exact_mod_cast hk
      change (Int.cast (A_lookup (2^hv2 * 3^hv3 * 5^1 * 7^hv7)) - Int.cast (A_lookup (2^hv2 * 3^hv3 * 5^0 * 7^hv7)) : Padic 5) / (↑(5 * n) : Padic 5)^2 ∈ PadicInt.subring 5
      rw [hk_diff]
      have h1 : (Nat.cast (5 * n) : Padic 5) = 5 * (Nat.cast n : Padic 5) := by
        push_cast; rfl
      rw [h1]
      have h_pow : (5 * (Nat.cast n : Padic 5)) ^ 2 = 25 * (Nat.cast n : Padic 5) ^ 2 := by
        ring
      rw [h_pow]
      have h_nz : (25 : Padic 5) ≠ 0 := by norm_num
      rw [mul_div_mul_left _ _ h_nz]
      have hn_norm : ‖(Nat.cast n : Padic 5)‖ = 1 := by
        rw [Padic.norm_natCast_eq_one_iff]
        have h_dvd : ¬ 5 ∣ n := by
          intro h_div
          have h_val : padicValNat 5 n ≠ 0 := by
            rwa [← dvd_iff_padicValNat_ne_zero hn_ne_0]
          contradiction
        exact Nat.Prime.coprime_iff_not_dvd (by decide) |>.mpr h_dvd
      rw [PadicInt.mem_subring_iff]
      rw [norm_div]
      have h_n2 : ‖(Nat.cast n : Padic 5) ^ 2‖ = 1 := by
        rw [norm_pow, hn_norm, one_pow]
      rw [h_n2, div_one]
      rw [← PadicInt.mem_subring_iff]
      exact intCast_mem (PadicInt.subring 5) k

    · -- padicValNat 5 n ≠ 0
      have h7 : padicValNat 7 (5 * n) = padicValNat 7 n := by
        have h_mul : padicValNat 7 (5 * n) = padicValNat 7 5 + padicValNat 7 n := by
          exact padicValNat.mul (by decide) hn_ne_0
        have h5_val : padicValNat 7 5 = 0 := padicValNat_primes (by decide)
        rw [h_mul, h5_val, zero_add]
      have h5 : min 1 (padicValNat 5 (5 * n)) = 1 := by
        have h_mul : padicValNat 5 (5 * n) = padicValNat 5 5 + padicValNat 5 n := by
          exact padicValNat.mul (by decide) hn_ne_0
        have h55 : padicValNat 5 5 = 1 := by
          exact padicValNat_self
        have h_ge : padicValNat 5 n ≥ 1 := by omega
        rw [h_mul, h55]
        have : 1 + padicValNat 5 n ≥ 1 := by omega
        exact min_eq_left this
      have h5_n : min 1 (padicValNat 5 n) = 1 := by
        have h_ge : padicValNat 5 n ≥ 1 := by omega
        exact min_eq_left h_ge
      dsimp only
      rw [h2, h3, h7, h5, h5_n]
      try simp

  · rcases eq_or_ne p 7 with rfl | hp7
    · -- Case p = 7
      by_cases h7n : padicValNat 7 n = 0
      · -- padicValNat 7 n = 0
        have h5 : padicValNat 5 (7 * n) = padicValNat 5 n := by
          have h_mul : padicValNat 5 (7 * n) = padicValNat 5 7 + padicValNat 5 n := by
            exact padicValNat.mul (by decide) hn_ne_0
          have h5_val : padicValNat 5 7 = 0 := padicValNat_primes (by decide)
          rw [h_mul, h5_val, zero_add]
        have h7 : padicValNat 7 (7 * n) = 1 := by
          have h_mul : padicValNat 7 (7 * n) = padicValNat 7 7 + padicValNat 7 n := by
            exact padicValNat.mul (by decide) hn_ne_0
          have h77 : padicValNat 7 7 = 1 := by
            exact padicValNat_self
          rw [h_mul, h77, h7n, add_zero]
        dsimp only
        rw [h2, h3, h5, h7, h7n]
        have h2_val : min 3 (padicValNat 2 n) = 0 ∨ min 3 (padicValNat 2 n) = 1 ∨ min 3 (padicValNat 2 n) = 2 ∨ min 3 (padicValNat 2 n) = 3 := by
          have : min 3 (padicValNat 2 n) ≤ 3 := min_le_left 3 (padicValNat 2 n)
          omega
        have h3_val : min 2 (padicValNat 3 n) = 0 ∨ min 2 (padicValNat 3 n) = 1 ∨ min 2 (padicValNat 3 n) = 2 := by
          have : min 2 (padicValNat 3 n) ≤ 2 := min_le_left 2 (padicValNat 3 n)
          omega
        have h5_val : min 1 (padicValNat 5 n) = 0 ∨ min 1 (padicValNat 5 n) = 1 := by
          have : min 1 (padicValNat 5 n) ≤ 1 := min_le_left 1 (padicValNat 5 n)
          omega
        generalize h_v2 : min 3 (padicValNat 2 n) = hv2
        generalize h_v3 : min 2 (padicValNat 3 n) = hv3
        generalize h_v5 : min 1 (padicValNat 5 n) = hv5
        have hhu2 : hv2 = 0 ∨ hv2 = 1 ∨ hv2 = 2 ∨ hv2 = 3 := by
          rw [← h_v2]
          exact h2_val
        have hhu3 : hv3 = 0 ∨ hv3 = 1 ∨ hv3 = 2 := by
          rw [← h_v3]
          exact h3_val
        have hhu5 : hv5 = 0 ∨ hv5 = 1 := by
          rw [← h_v5]
          exact h5_val
        have h_ex : ∃ k : ℤ, A_lookup (2^hv2 * 3^hv3 * 5^hv5 * 7^1) - A_lookup (2^hv2 * 3^hv3 * 5^hv5 * 7^0) = 49 * k := by
          rcases hhu2 with rfl | rfl | rfl | rfl
          · rcases hhu3 with rfl | rfl | rfl
            · rcases hhu5 with rfl | rfl
              · exact ⟨4, by decide⟩
              · exact ⟨-1614491118696, by decide⟩
            · rcases hhu5 with rfl | rfl
              · exact ⟨-34163, by decide⟩
              · exact ⟨219688059846296633923370639110590322145937, by decide⟩
            · rcases hhu5 with rfl | rfl
              · exact ⟨-171737713456712688453641, by decide⟩
              · exact ⟨-122755916854513389366920580811843963593088498999258980659435227191872495666484139002375727209554814160999723185387678874544804484516, by decide⟩
          · rcases hhu3 with rfl | rfl | rfl
            · rcases hhu5 with rfl | rfl
              · exact ⟨1560, by decide⟩
              · exact ⟨391816323622515612278522160, by decide⟩
            · rcases hhu5 with rfl | rfl
              · exact ⟨-1675237586840295, by decide⟩
              · exact ⟨-236435553425012101835480056082149971526035315707753122152663296279767647852917772423195, by decide⟩
            · rcases hhu5 with rfl | rfl
              · exact ⟨-575360923284561715152457924838247550424612657152413, by decide⟩
              · exact ⟨10852618958053396717292541607493608196105087200256932127658623881666258210436423713999469585257267173792501721052058062404102334741590971812943797021072063892177719123848019701934244483198054485620935695994074021710641110808000307424723129387861447633036247906151212, by decide⟩
          · rcases hhu3 with rfl | rfl | rfl
            · rcases hhu5 with rfl | rfl
              · exact ⟨-1081459872, by decide⟩
              · exact ⟨-440443374623853446902854066949591283082709138253121694272, by decide⟩
            · rcases hhu5 with rfl | rfl
              · exact ⟨925973002337831960142625771280697, by decide⟩
              · exact ⟨8507463919259630311708253519698108177077029894765894163384896522022341106609822514412604885200321463752327469716364750528134293498437423355167948342032467284467318954815393797, by decide⟩
            · rcases hhu5 with rfl | rfl
              · exact ⟨148713810211442211508449712073721330136161906571006821384490489830396120210375811845309238456710405334851, by decide⟩
              · exact ⟨-80080380062311929856808335607216937655428001729127703725124319104744456360988128831523609857545155646469215510021505299421601673120229891672821525091068795810540838505169925466986233726504272652721246658014034164745406063965285061822685181478801025222942935020281486579192539748319835297010526997348295630098330828269326004902175209367968808682573854224662064412825297741104385360892274567943546123783976096300781545928010805112599093456658798976327657247188661188994365346066394900574176765065740463122857126952388226569893565264724, by decide⟩
          · rcases hhu3 with rfl | rfl | rfl
            · rcases hhu5 with rfl | rfl
              · exact ⟨-804418379315664387456, by decide⟩
              · exact ⟨71969177905856614817111765214494634052574428288691264274086483070993272827271101582304102439535541802366097920050944, by decide⟩
            · rcases hhu5 with rfl | rfl
              · exact ⟨368779046675925265240191212932687499161560898863608966047408821219129, by decide⟩
              · exact ⟨-4954504634241992314223860571788136917834045426606140944742122424092878156672246950941299686461338513919326469662021523078461660820997719737804086553901364194931932158119049226463785582915948582309880227703385425626529168861491863697744294547710208401424714441433407930194189478451936781296020201002235152096819632974331437206595037872369588548197987518971, by decide⟩
            · rcases hhu5 with rfl | rfl
              · exact ⟨-7293368562274702757832205477358061757601908754609804583621682668327231573049097153285032509916401219582587658998083273742942675700505163900428211320432317784542701529819769713608242074693280164512763021588254397, by decide⟩
              · exact ⟨-310980700100479626668928026092344865121078808809127797152975176923371543463254792218200687642480961239819649767526769654644440665199882636397877833208777966942248187255699204246939848871161952803256951531418277516900797790604532266814791339706101271003922935155964510159546979969175266028247140838106107580035493958518411286620065074161292455925502247510217159362429497242260628877995352285916508280834988146833301047323508620164687987341327430366372025515500692865315697877794016121389516175254630402083994775289978455124904266407622440906217298229469256508264911782318109213621614306904308362047906017213962095449828063754454583637001511653564630307993979284768694172199073093947228205802891761249504590857072267833472749594257321302094921106961849585911038504945770895615217438840149300320019332358857557179046599279151479571198985192035555931275303693494323537414307861536351492360780607292068769998593848265334799381319979331180670419323595304559130052684548606243683942861410592416700359482141132716937452089805903164336736621103193613052809174168322748448110930772, by decide⟩

        rcases h_ex with ⟨k, hk⟩
        have hk_diff : (Int.cast (A_lookup (2^hv2 * 3^hv3 * 5^hv5 * 7^1)) - Int.cast (A_lookup (2^hv2 * 3^hv3 * 5^hv5 * 7^0)) : Padic 7) = 49 * (Int.cast k : Padic 7) := by
          exact_mod_cast hk
        change (Int.cast (A_lookup (2^hv2 * 3^hv3 * 5^hv5 * 7^1)) - Int.cast (A_lookup (2^hv2 * 3^hv3 * 5^hv5 * 7^0)) : Padic 7) / (↑(7 * n) : Padic 7)^2 ∈ PadicInt.subring 7
        rw [hk_diff]
        have h1 : (Nat.cast (7 * n) : Padic 7) = 7 * (Nat.cast n : Padic 7) := by
          push_cast; rfl
        rw [h1]
        have h_pow : (7 * (Nat.cast n : Padic 7)) ^ 2 = 49 * (Nat.cast n : Padic 7) ^ 2 := by
          ring
        rw [h_pow]
        have h_nz : (49 : Padic 7) ≠ 0 := by norm_num
        rw [mul_div_mul_left _ _ h_nz]
        have hn_norm : ‖(Nat.cast n : Padic 7)‖ = 1 := by
          rw [Padic.norm_natCast_eq_one_iff]
          have h_dvd : ¬ 7 ∣ n := by
            intro h_div
            have h_val : padicValNat 7 n ≠ 0 := by
              rwa [← dvd_iff_padicValNat_ne_zero hn_ne_0]
            contradiction
          exact Nat.Prime.coprime_iff_not_dvd (by decide) |>.mpr h_dvd
        rw [PadicInt.mem_subring_iff]
        rw [norm_div]
        have h_n2 : ‖(Nat.cast n : Padic 7) ^ 2‖ = 1 := by
          rw [norm_pow, hn_norm, one_pow]
        rw [h_n2, div_one]
        rw [← PadicInt.mem_subring_iff]
        exact intCast_mem (PadicInt.subring 7) k

      · -- padicValNat 7 n ≠ 0
        have h5 : padicValNat 5 (7 * n) = padicValNat 5 n := by
          have h_mul : padicValNat 5 (7 * n) = padicValNat 5 7 + padicValNat 5 n := by
            exact padicValNat.mul (by decide) hn_ne_0
          have h5_val : padicValNat 5 7 = 0 := padicValNat_primes (by decide)
          rw [h_mul, h5_val, zero_add]
        have h7 : min 1 (padicValNat 7 (7 * n)) = 1 := by
          have h_mul : padicValNat 7 (7 * n) = padicValNat 7 7 + padicValNat 7 n := by
            exact padicValNat.mul (by decide) hn_ne_0
          have h77 : padicValNat 7 7 = 1 := by
            exact_mod_cast padicValNat_self
          have h_ge : padicValNat 7 n ≥ 1 := by omega
          rw [h_mul, h77]
          have : 1 + padicValNat 7 n ≥ 1 := by omega
          exact min_eq_left this
        have h7_n : min 1 (padicValNat 7 n) = 1 := by
          have h_ge : padicValNat 7 n ≥ 1 := by omega
          exact min_eq_left h_ge
        dsimp only
        rw [h2, h3, h5, h7, h7_n]
        try simp

    · -- Case p ≠ 5 and p ≠ 7
      have hp_ne_5 : p ≠ 5 := hp5
      have h_mul_5 : padicValNat 5 (p * n) = padicValNat 5 p + padicValNat 5 n := by
        exact padicValNat.mul hp_ne_0 hn_ne_0
      have h_val_p_5 : padicValNat 5 p = 0 := by
        exact padicValNat_primes hp_ne_5.symm
      have h5 : padicValNat 5 (p * n) = padicValNat 5 n := by
        rw [h_mul_5, h_val_p_5, zero_add]

      have hp_ne_7 : p ≠ 7 := hp7
      have h_mul_7 : padicValNat 7 (p * n) = padicValNat 7 p + padicValNat 7 n := by
        exact padicValNat.mul hp_ne_0 hn_ne_0
      have h_val_p_7 : padicValNat 7 p = 0 := by
        exact padicValNat_primes hp_ne_7.symm
      have h7 : padicValNat 7 (p * n) = padicValNat 7 n := by
        rw [h_mul_7, h_val_p_7, zero_add]

      dsimp only
      rw [h2, h3, h5, h7]
      simp
