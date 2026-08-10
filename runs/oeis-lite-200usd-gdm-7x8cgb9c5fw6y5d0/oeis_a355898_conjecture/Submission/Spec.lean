import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

set_option maxRecDepth 200000

open Nat

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b =>
  let g := Nat.gcd b a
  A355898_loop n b (g + (b + a) / g)

theorem A355898_loop_eq (n : ℕ) : ∀ k, 1 ≤ k →
  A355898_loop n (A355898 k) (A355898 (k + 1)) = (A355898 (n + k), A355898 (n + k + 1)) := by
  induction n with
  | zero =>
    intro k _
    simp only [A355898_loop, zero_add]
  | succ n ih =>
    intro k hk
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    subst hm
    have h_rec : Nat.gcd (A355898 (m + 2)) (A355898 (m + 1)) + (A355898 (m + 2) + A355898 (m + 1)) / Nat.gcd (A355898 (m + 2)) (A355898 (m + 1)) = A355898 (m + 3) := rfl
    simp only [A355898_loop]
    rw [h_rec]
    have ih_val := ih (m + 2) (by omega)
    rw [ih_val]
    congr 2 <;> omega

theorem A355898_eq_loop (n : ℕ) : (A355898 (n + 1), A355898 (n + 2)) = A355898_loop n 1 1 := by
  exact (A355898_loop_eq n 1 (by omega)).symm

theorem A355898_loop_split (n : ℕ) (m : ℕ) (a b : ℕ) :
  A355898_loop (m + n) a b = A355898_loop m (A355898_loop n a b).1 (A355898_loop n a b).2 := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [A355898_loop]
    exact ih b (Nat.gcd b a + (b + a) / Nat.gcd b a)

def S1_fst : ℕ := 7277455
def S1_snd : ℕ := 2666291
theorem S1_eq : A355898_loop 100 1 1 = (S1_fst, S1_snd) := by rfl

def S2_fst : ℕ := 3359212668434771
def S2_snd : ℕ := 9526068816715239
theorem S2_eq : A355898_loop 100 S1_fst S1_snd = (S2_fst, S2_snd) := by rfl

def S3_fst : ℕ := 129008297887583711815402331
def S3_snd : ℕ := 208739198404050999856340981
theorem S3_eq : A355898_loop 100 S2_fst S2_snd = (S3_fst, S3_snd) := by rfl

def S4_fst : ℕ := 980106323160192281099948146594941
def S4_snd : ℕ := 2366601520282495044027180073428935
theorem S4_eq : A355898_loop 100 S3_fst S3_snd = (S4_fst, S4_snd) := by rfl

def S5_fst : ℕ := 104425612996661659319302329465246301777860621
def S5_snd : ℕ := 170624405700040372950947030937310887411313079
theorem S5_eq : A355898_loop 100 S4_fst S4_snd = (S5_fst, S5_snd) := by rfl

def S6_fst : ℕ := 1832912359645877917444286824636456159767369064958587543
def S6_snd : ℕ := 2995487463816849323081205850984053782026807787290862701
theorem S6_eq : A355898_loop 100 S5_fst S5_snd = (S6_fst, S6_snd) := by rfl

def S7_fst : ℕ := 515037701357268284107012081572395710373400310972068900231747
def S7_snd : ℕ := 714391768021095972582565686011976967265929489613160880135653
theorem S7_eq : A355898_loop 100 S6_fst S6_snd = (S7_fst, S7_snd) := by rfl

def S8_fst : ℕ := 53161033366380670874029247160972088843568581400423515533650198456829
def S8_snd : ℕ := 28675771840775366134545460544882186490350586762865458628954399225293
theorem S8_eq : A355898_loop 100 S7_fst S7_snd = (S8_fst, S8_snd) := by rfl

def S9_fst : ℕ := 10654839769340105544128500060537851550757555046749411879381550450012066293
def S9_snd : ℕ := 164669994560908249983940291983654130304931805558573847062228931384853275487
theorem S9_eq : A355898_loop 100 S8_fst S8_snd = (S9_fst, S9_snd) := by rfl

def S10_fst : ℕ := 857849530606042011074830162029609056836142056053432234500214934736158102606870905673
def S10_snd : ℕ := 1649361868662090153303910549715102733645372464449722097662281114035603758181244349143
theorem S10_eq : A355898_loop 100 S9_fst S9_snd = (S10_fst, S10_snd) := by rfl

def S11_fst : ℕ := 18617225144465562220733705492106092189576324887701055139673401037658563991094092759020462597
def S11_snd : ℕ := 30741509391077528561907360448992002635470052234118445885838486324828067942202556523979771791
theorem S11_eq : A355898_loop 100 S10_fst S10_snd = (S11_fst, S11_snd) := by rfl

def S12_fst : ℕ := 1107862572274089024683031431050849596765559438513438566310106886966019158528813090246487360203330543085609842485
def S12_snd : ℕ := 1792559296803362929141936882389432146272589251324471743797667739771818172656483543079525511623110666159474187217
theorem S12_eq : A355898_loop 100 S11_fst S11_snd = (S12_fst, S12_snd) := by rfl

def S13_fst : ℕ := 315300938824976185364834881084752415893951374489927785941774812719628765620185045290742790429354068229568605679835440745482352789
def S13_snd : ℕ := 169969065433977970150744182225091359068797279941091558106496469530997087405162817551089435158414414960677570767774246742327649393
theorem S13_eq : A355898_loop 100 S12_fst S12_snd = (S13_fst, S13_snd) := by rfl

def S14_fst : ℕ := 1115130967993176558928384665529155018347998650284951150612734456326556521610474786643395288934118989872021657736854212236914826059181109
def S14_snd : ℕ := 2087432033992233337652979408536170178322829608011798828800798291693064334569830515089188177729200443512674086836034686741812537571534833
theorem S14_eq : A355898_loop 100 S13_fst S13_snd = (S14_fst, S14_snd) := by rfl

def S15_fst : ℕ := 1306858847712046881673905248805385993994449707481250551678801760273422347867285714801086055224737916729776486939757661689889532165848478763748011
def S15_snd : ℕ := 3571364229194683546375925496519554086181903060419671165328824328336638209730560563661927363964858744009135957362798920383275815952968401242470287
theorem S15_eq : A355898_loop 100 S14_fst S14_snd = (S15_fst, S15_snd) := by rfl

def S16_fst : ℕ := 3321192652955483335914700896424407853934587746018191972032325162459513314182568021027271576978752741434961142837225617081783021078485701322805835883367
def S16_snd : ℕ := 5889630867145066481392129437935807617515157384777964273596330112913754295020175983300077594650142112723255050399663725208165845347382897509406483087275
theorem S16_eq : A355898_loop 100 S15_fst S15_snd = (S16_fst, S16_snd) := by rfl

def S17_fst : ℕ := 217281065661497338173562976689973532060182361730139929822035099094496733620577959739447777640808275920347804358160552260540323284049408485430576715662491161
def S17_snd : ℕ := 39746687277475552342471323276130561669003694969671393008924506127519840487642551114076719075394866445913221255312694783363465673180270367545644265131611401
theorem S17_eq : A355898_loop 100 S16_fst S16_snd = (S17_fst, S17_snd) := by rfl

def S18_fst : ℕ := 3309143204912040673030136001357482379083318752644237204613147893465495699038296212416935253312376845927148083931396792156443150739506295292723140042721583043894935
def S18_snd : ℕ := 1889821341666679712746851245702898984621842734664986482931177712135759606465741882121617595768638502915496028016267384791191588838179487187734054611187708100242991
theorem S18_eq : A355898_loop 100 S17_fst S17_snd = (S18_fst, S18_snd) := by rfl

def S19_fst : ℕ := 22348119482825341610296794868964137982382799119787679177144642804209721489920720179994394824857517578786655998792612129370072602388938154914936474523339863694999679963871957
def S19_snd : ℕ := 12046301734233091671240128261088693880821333559517490005405041221262955619175490411606990374057034570029835853534624840677590303086060493252103310025212915416658358367874863
theorem S19_eq : A355898_loop 100 S18_fst S18_snd = (S19_fst, S19_snd) := by rfl

def S20_fst : ℕ := 3016310876544471039814211841161237135686166051819283926749201012500251985148689641005382234349889873473817198348083105332892079916102889196339987199121080815445028636362301568083905
def S20_snd : ℕ := 4870834809367087528565680855621871407973482199145088253299489849442888968616012834682202004063575402331653573094937185350034208679117333937383628437168745003888235439238959915061193
theorem S20_eq : A355898_loop 100 S19_fst S19_snd = (S20_fst, S20_snd) := by rfl

def S21_fst : ℕ := 64719751462567691840907059742621639433557363956824756655215118995262881414895426654403523068867074307604160282601675900922951508145356281732631864439512689637637751984975576353730557745320963
def S21_snd : ℕ := 96335003388763014542351876434316287232637658674113784108374604300002736021887181393152517524309490665794204800680903951842989556653108772233727472516568733366649076982285258186715305180750227
theorem S21_eq : A355898_loop 100 S20_fst S20_snd = (S21_fst, S21_snd) := by rfl

def S22_fst : ℕ := 481626193896009912237370078923007403018091934430225275870832883606704642815226510700201913266347303285461042910211460043052888997251478059798974729857328116248895883438654843426378654064053573452255335
def S22_snd : ℕ := 270832535135961611291135418179666373259928056960539423588785900190071563570290186555698007549301616416787175495599075629072680978809950510268333692268095350261481979581601223127104367717345929583152059
theorem S22_eq : A355898_loop 100 S21_fst S21_snd = (S22_fst, S22_snd) := by rfl

def S23_fst : ℕ := 139747312875931502514096434778833601142448676188125903163362467282966783578998247380289375775444854839174237942064963660236037088504344392444534937535483124945108970124614580383053710124167070975710431153834303
def S23_snd : ℕ := 203206603380280223855325368774286089245211322127132067201344388960531723649409582335182826795089222771707164635279779760336065014734376272900296431732964237707055331181341178875423755986476201499095547192444091
theorem S23_eq : A355898_loop 100 S22_fst S22_snd = (S23_fst, S23_snd) := by rfl

def S24_fst : ℕ := 957336274672085768738200004327738142850436972174233550613642343818792464813708954821840030504014363245593173813517961041258697349414740782153218340392517601483130130153407178082619595757786185445220908957489170756275429
def S24_snd : ℕ := 1557834452030056677110497816885511946818891059523635281931634173185545214738314727043153246964146752288533036715735823245746026343089902468655168869131417413107284021662185750589018744418042446361090530443091260662845499
theorem S24_eq : A355898_loop 100 S23_fst S23_snd = (S24_fst, S24_snd) := by rfl

def S25_fst : ℕ := 173137151050883067474295656694512139236024991560288955162634438789913706823501298561800041694336353893300122053507968223092570409207592141223645435045668163873016346502121842578614933246038505427135456512589315968584829149886827
def S25_snd : ℕ := 280570256688898634831698604305426389331172114693751134391419109670776283648193769988620010817465933973741573868220640843216105621838212366772492314170064762545237823675966893607726555257865816353526102887334944166924137987693991
theorem S25_eq : A355898_loop 100 S24_fst S24_snd = (S25_fst, S25_snd) := by rfl

def S26_fst : ℕ := 174667159202219463849651722469961916936163395085069538318705519148437822418603920520941522199132941289511610523248172564956158278117178412236287207192781099949484462152292229420734223243766295822113641974767035271416939203300015472693647
def S26_snd : ℕ := 229416327304073957347169124632195403735341546980686244345120818600733434263618020080708711559908540107453318057289179686982165978376751660874881666599289627407282030282487456023589796643924758461345419263199952676125537723930397548139287
theorem S26_eq : A355898_loop 100 S25_fst S25_snd = (S26_fst, S26_snd) := by rfl

def S27_fst : ℕ := 6511909498785183667610810053383579568693868838321101398396701759358160946340188225369689765990051973384624137836772812647529263268167444545977168316171662803996458627058967616854921875470077708439589300870245083100614367453650983319176520955392719
def S27_snd : ℕ := 10560095156439685237320737581888857390313406406019897718755964134335891318321053869049026870384031832095354641724703545888587778522269537235651581708906919950646602946450367236517739973675009770471814658852380301310408903608263838879241955618545821
theorem S27_eq : A355898_loop 100 S26_fst S26_snd = (S27_fst, S27_snd) := by rfl

def S28_fst : ℕ := 3171831105760532370000988964529733119907635964118679903658196522593821938036993331214717001269216805063195064412896165298281192898290256536408215863802008090423909589726091466395220320931305905382536943009934039925502416172994653964312437681040903948235640385
def S28_snd : ℕ := 3256494533423779303487318074879745157549578204049162125311301075663444354892231753911596792764197520409476852915731109132002848497468739031714255125363471010424839271049875712648757535717696819201231466674237771413668364901901466057810838821291180682032342403
theorem S28_eq : A355898_loop 100 S27_fst S27_snd = (S28_fst, S28_snd) := by rfl

def S29_fst : ℕ := 35832300278212127280175302722936577485385171675233027313593829378151371716480955680719285072886406170322551633178170649538409048356514318662517663975138129346646194484785858484069159683668527200076090674522042063549601304812558308841903712432530304228369332330322721
def S29_snd : ℕ := 9152698620957211414205651595412050093967492533913540211172850097280499000500947514917833867398006364636678952506585446595596496657067517770498493975364666018622886030876672023639957947290159464498360458341838307157032098212366907329238206011054015885291572800067289
theorem S29_eq : A355898_loop 100 S28_fst S28_snd = (S29_fst, S29_snd) := by rfl

def S30_fst : ℕ := 2252100851515924337420712023090535791161228994963661906941246563757272408118701810882083719598383517894888766401650207550025252428618651916349548698397556216037468735105831539127884356365207584345983877997538910998006627494516449528278950666649538557693616077518388252436853
def S30_snd : ℕ := 3620515055665532360422328989354131977678080686610645643700783568117573724781138066905221475268276464450806379641167737675956330738667559167750992362425808603769007003161571941034766362295332703286037883775794573756031657645003290528249711652420438045833994511757700259945673
theorem S30_eq : A355898_loop 100 S29_fst S29_snd = (S30_fst, S30_snd) := by rfl

def S31_fst : ℕ := 4768625641396802085685578759956995559179368225889730964310355426543987585343089139359457185975472262919878943931820936108322726911518204819874101411592303089681851418727923898810236888756009105017682049222127137190698477942043821982811860918143015583966362288633308858630791903005
def S31_snd : ℕ := 123648538012587046052158194702083865785528463145134468331682879357242130450558918409347848530513499661833797842507826786603506457731474951688276019599466391535260499262154443845102624371356522528237938398552160754882637341288008473378253005033490346003898766934978953223750959158637
theorem S31_eq : A355898_loop 100 S30_fst S30_snd = (S31_fst, S31_snd) := by rfl

def S32_fst : ℕ := 125504304973661176504282431656406287418599897930052310503811386886808918682927909584836349382124368348513508379047852194294425324976836000184873082263487887432579734932468273073500156838242492080571539931631219885066179167301123316976218430827206536999779806655571701205887838263592851669153
def S32_snd : ℕ := 177232737653069052100056553232398164737517538930313893671936832159869633283220866436766215914497605661099487941175332057591088788003267259936386994705273363583938664657291823196810016057700869671969014120778915859603986252858688434049126109073669339894504714376604832569450992684018324312389
theorem S32_eq : A355898_loop 100 S31_fst S31_snd = (S32_fst, S32_snd) := by rfl

def S33_fst : ℕ := 67126753171683790620080433180681315559451350121918702227129347503481421565357558565879773819700866181118670091079652618588917892474016881706940492185573268555193740094025237716416757166511871836294657132809859456166577323471883186433265102394739798282619667958060519847448787649471528674214497005
def S33_snd : ℕ := 5776849160423985903442821457383595089127013108491060400232399649222572001611985411766058423530743626854180726438866062747513297994170153968629788092160547268340578307757782750684349203457969453918273768971309264013050527584028525388398865619750140950299247543721680787714758470048952290243150397
theorem S33_eq : A355898_loop 100 S32_fst S32_snd = (S33_fst, S33_snd) := by rfl

def S34_fst : ℕ := 289916765643371506283285870974207888121596867028299645142139084592894293091819776026863308009724771559514564172876280371337381760925492834214448874284752945318339634768355665380980358788509064397436045733272228154788926078416689976231858618798527522160078434540714426822080236558077160790409362863401412241
def S34_snd : ℕ := 528312234006287666579937758141842995938985859405078395335561525414996290319860149803852369557841275408866477344539261506759445654547890102427592819325895084818922818294884984415252233912100364766510892691858753776687476875641394697796101683691506969413912026675669204116728737259988291506908365846805881405
theorem S34_eq : A355898_loop 100 S33_fst S33_snd = (S34_fst, S34_snd) := by rfl

def S35_fst : ℕ := 3473119443457968003624584044017157897725979135508218583906119502273904492917347151413271118343846195193681305442951611899465015890266284922031326452486142621129576267623329246563642474475918424629331198553839848175314995376758364105776837679147072609920025360233089053192893414453711758141067318204391247435422603445
def S35_snd : ℕ := 2846303424419342809874128967271545446172782549221305178619047152157001094715310100108696765657008286933477994008612293341801575594106128734160818460425084188821455339849046456161477305491264831881740101826760372009461228279688791943044561319762423242913537186030242516261679513775368126723086508868566993586028975337
theorem S35_eq : A355898_loop 100 S34_fst S34_snd = (S35_fst, S35_snd) := by rfl

def S36_fst : ℕ := 5394727790019564776961918493386597810029106968521114773127882606273331881852736558074815179295425364099648976147290164940080296098421655864801160156224226742324753117739508609169448448102788076748482145914385987878498975137468124911323955931462637379114483008127602351325922641419102121935022911720516851374712509549921090571
def S36_snd : ℕ := 3334167547967142440396997427457451759071899060471442114078538504644794416372033834916035120158906672214820753871957245420907527139633124329562906218704762393381718733531056124298627486388776994997124456578181685953254006066837638979571577335601752156437215351303988730986946563731112103799146849087246075394650834348500629157
theorem S36_eq : A355898_loop 100 S35_fst S35_snd = (S36_fst, S36_snd) := by rfl

def S37_fst : ℕ := 168515793671170543477376329129171284351014653980301934292714765947955476426535455993095998423421862338306171041927058567192156000305792991708181402427719001601893097325691364175994229709721751743128969769058893005677904817742041175398683354649775178686054034385734311550978542064438331782549699113695765160198263047254053937806260192295
def S37_snd : ℕ := 1715391883587201562913203123328436539707292190801756449731000371053836346812456073957804266282233855338628329255833533400842204644384661852952915679878941111602162290292345885669952029045444381968767744217447676235235268115099781130571988802370538067261148989244641852000822572547587582052483111986763589194506601365196263596714901339
theorem S37_eq : A355898_loop 100 S36_fst S36_snd = (S37_fst, S37_snd) := by rfl

theorem loop_100_eq : A355898_loop 100 1 1 = (S1_fst, S1_snd) := S1_eq

theorem loop_200_eq : A355898_loop 200 1 1 = (S2_fst, S2_snd) := by
  have h := A355898_loop_split 100 100 1 1
  have h_add : 100 + 100 = 200 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_100_eq]
  exact S2_eq

theorem loop_300_eq : A355898_loop 300 1 1 = (S3_fst, S3_snd) := by
  have h := A355898_loop_split 200 100 1 1
  have h_add : 100 + 200 = 300 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_200_eq]
  exact S3_eq

theorem loop_400_eq : A355898_loop 400 1 1 = (S4_fst, S4_snd) := by
  have h := A355898_loop_split 300 100 1 1
  have h_add : 100 + 300 = 400 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_300_eq]
  exact S4_eq

theorem loop_500_eq : A355898_loop 500 1 1 = (S5_fst, S5_snd) := by
  have h := A355898_loop_split 400 100 1 1
  have h_add : 100 + 400 = 500 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_400_eq]
  exact S5_eq

theorem loop_600_eq : A355898_loop 600 1 1 = (S6_fst, S6_snd) := by
  have h := A355898_loop_split 500 100 1 1
  have h_add : 100 + 500 = 600 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_500_eq]
  exact S6_eq

theorem loop_700_eq : A355898_loop 700 1 1 = (S7_fst, S7_snd) := by
  have h := A355898_loop_split 600 100 1 1
  have h_add : 100 + 600 = 700 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_600_eq]
  exact S7_eq

theorem loop_800_eq : A355898_loop 800 1 1 = (S8_fst, S8_snd) := by
  have h := A355898_loop_split 700 100 1 1
  have h_add : 100 + 700 = 800 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_700_eq]
  exact S8_eq

theorem loop_900_eq : A355898_loop 900 1 1 = (S9_fst, S9_snd) := by
  have h := A355898_loop_split 800 100 1 1
  have h_add : 100 + 800 = 900 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_800_eq]
  exact S9_eq

theorem loop_1000_eq : A355898_loop 1000 1 1 = (S10_fst, S10_snd) := by
  have h := A355898_loop_split 900 100 1 1
  have h_add : 100 + 900 = 1000 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_900_eq]
  exact S10_eq

theorem loop_1100_eq : A355898_loop 1100 1 1 = (S11_fst, S11_snd) := by
  have h := A355898_loop_split 1000 100 1 1
  have h_add : 100 + 1000 = 1100 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1000_eq]
  exact S11_eq

theorem loop_1200_eq : A355898_loop 1200 1 1 = (S12_fst, S12_snd) := by
  have h := A355898_loop_split 1100 100 1 1
  have h_add : 100 + 1100 = 1200 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1100_eq]
  exact S12_eq

theorem loop_1300_eq : A355898_loop 1300 1 1 = (S13_fst, S13_snd) := by
  have h := A355898_loop_split 1200 100 1 1
  have h_add : 100 + 1200 = 1300 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1200_eq]
  exact S13_eq

theorem loop_1400_eq : A355898_loop 1400 1 1 = (S14_fst, S14_snd) := by
  have h := A355898_loop_split 1300 100 1 1
  have h_add : 100 + 1300 = 1400 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1300_eq]
  exact S14_eq

theorem loop_1500_eq : A355898_loop 1500 1 1 = (S15_fst, S15_snd) := by
  have h := A355898_loop_split 1400 100 1 1
  have h_add : 100 + 1400 = 1500 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1400_eq]
  exact S15_eq

theorem loop_1600_eq : A355898_loop 1600 1 1 = (S16_fst, S16_snd) := by
  have h := A355898_loop_split 1500 100 1 1
  have h_add : 100 + 1500 = 1600 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1500_eq]
  exact S16_eq

theorem loop_1700_eq : A355898_loop 1700 1 1 = (S17_fst, S17_snd) := by
  have h := A355898_loop_split 1600 100 1 1
  have h_add : 100 + 1600 = 1700 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1600_eq]
  exact S17_eq

theorem loop_1800_eq : A355898_loop 1800 1 1 = (S18_fst, S18_snd) := by
  have h := A355898_loop_split 1700 100 1 1
  have h_add : 100 + 1700 = 1800 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1700_eq]
  exact S18_eq

theorem loop_1900_eq : A355898_loop 1900 1 1 = (S19_fst, S19_snd) := by
  have h := A355898_loop_split 1800 100 1 1
  have h_add : 100 + 1800 = 1900 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1800_eq]
  exact S19_eq

theorem loop_2000_eq : A355898_loop 2000 1 1 = (S20_fst, S20_snd) := by
  have h := A355898_loop_split 1900 100 1 1
  have h_add : 100 + 1900 = 2000 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_1900_eq]
  exact S20_eq

theorem loop_2100_eq : A355898_loop 2100 1 1 = (S21_fst, S21_snd) := by
  have h := A355898_loop_split 2000 100 1 1
  have h_add : 100 + 2000 = 2100 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2000_eq]
  exact S21_eq

theorem loop_2200_eq : A355898_loop 2200 1 1 = (S22_fst, S22_snd) := by
  have h := A355898_loop_split 2100 100 1 1
  have h_add : 100 + 2100 = 2200 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2100_eq]
  exact S22_eq

theorem loop_2300_eq : A355898_loop 2300 1 1 = (S23_fst, S23_snd) := by
  have h := A355898_loop_split 2200 100 1 1
  have h_add : 100 + 2200 = 2300 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2200_eq]
  exact S23_eq

theorem loop_2400_eq : A355898_loop 2400 1 1 = (S24_fst, S24_snd) := by
  have h := A355898_loop_split 2300 100 1 1
  have h_add : 100 + 2300 = 2400 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2300_eq]
  exact S24_eq

theorem loop_2500_eq : A355898_loop 2500 1 1 = (S25_fst, S25_snd) := by
  have h := A355898_loop_split 2400 100 1 1
  have h_add : 100 + 2400 = 2500 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2400_eq]
  exact S25_eq

theorem loop_2600_eq : A355898_loop 2600 1 1 = (S26_fst, S26_snd) := by
  have h := A355898_loop_split 2500 100 1 1
  have h_add : 100 + 2500 = 2600 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2500_eq]
  exact S26_eq

theorem loop_2700_eq : A355898_loop 2700 1 1 = (S27_fst, S27_snd) := by
  have h := A355898_loop_split 2600 100 1 1
  have h_add : 100 + 2600 = 2700 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2600_eq]
  exact S27_eq

theorem loop_2800_eq : A355898_loop 2800 1 1 = (S28_fst, S28_snd) := by
  have h := A355898_loop_split 2700 100 1 1
  have h_add : 100 + 2700 = 2800 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2700_eq]
  exact S28_eq

theorem loop_2900_eq : A355898_loop 2900 1 1 = (S29_fst, S29_snd) := by
  have h := A355898_loop_split 2800 100 1 1
  have h_add : 100 + 2800 = 2900 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2800_eq]
  exact S29_eq

theorem loop_3000_eq : A355898_loop 3000 1 1 = (S30_fst, S30_snd) := by
  have h := A355898_loop_split 2900 100 1 1
  have h_add : 100 + 2900 = 3000 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_2900_eq]
  exact S30_eq

theorem loop_3100_eq : A355898_loop 3100 1 1 = (S31_fst, S31_snd) := by
  have h := A355898_loop_split 3000 100 1 1
  have h_add : 100 + 3000 = 3100 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3000_eq]
  exact S31_eq

theorem loop_3200_eq : A355898_loop 3200 1 1 = (S32_fst, S32_snd) := by
  have h := A355898_loop_split 3100 100 1 1
  have h_add : 100 + 3100 = 3200 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3100_eq]
  exact S32_eq

theorem loop_3300_eq : A355898_loop 3300 1 1 = (S33_fst, S33_snd) := by
  have h := A355898_loop_split 3200 100 1 1
  have h_add : 100 + 3200 = 3300 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3200_eq]
  exact S33_eq

theorem loop_3400_eq : A355898_loop 3400 1 1 = (S34_fst, S34_snd) := by
  have h := A355898_loop_split 3300 100 1 1
  have h_add : 100 + 3300 = 3400 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3300_eq]
  exact S34_eq

theorem loop_3500_eq : A355898_loop 3500 1 1 = (S35_fst, S35_snd) := by
  have h := A355898_loop_split 3400 100 1 1
  have h_add : 100 + 3400 = 3500 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3400_eq]
  exact S35_eq

theorem loop_3600_eq : A355898_loop 3600 1 1 = (S36_fst, S36_snd) := by
  have h := A355898_loop_split 3500 100 1 1
  have h_add : 100 + 3500 = 3600 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3500_eq]
  exact S36_eq

theorem loop_3700_eq : A355898_loop 3700 1 1 = (S37_fst, S37_snd) := by
  have h := A355898_loop_split 3600 100 1 1
  have h_add : 100 + 3600 = 3700 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3600_eq]
  exact S37_eq

def S3771_fst : ℕ := 50821856637385792267808398991468475721843483337998623640757098602636928393269892952934230874475945024513818501434870581449774982213886818298525314166884933137805368884278748201859762766881515372183084024083577995511024802455180968712692288879507888937250291063504680754992157949256964474278019411768646907989461240384266638096191096905619665
def S3771_snd : ℕ := 7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617
theorem S3771_eq : A355898_loop 71 S37_fst S37_snd = (S3771_fst, S3771_snd) := by rfl

theorem loop_3771_eq : A355898_loop 3771 1 1 = (S3771_fst, S3771_snd) := by
  have h := A355898_loop_split 3700 71 1 1
  have h_add : 71 + 3700 = 3771 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3700_eq]
  exact S3771_eq

def S3772_fst : ℕ := 7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617
def S3772_snd : ℕ := 58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283
theorem S3772_eq : A355898_loop 72 S37_fst S37_snd = (S3772_fst, S3772_snd) := by rfl

theorem loop_3772_eq : A355898_loop 3772 1 1 = (S3772_fst, S3772_snd) := by
  have h := A355898_loop_split 3700 72 1 1
  have h_add : 72 + 3700 = 3772 := by omega
  rw [h_add] at h
  rw [h]
  rw [loop_3700_eq]
  exact S3772_eq

def B0 : ℕ := S3772_fst + 1
def B1 : ℕ := S3772_snd + 1
def A3772 : ℕ := S3771_fst

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero =>
    simp [B, B0]
  | succ m ih =>
    cases m with
    | zero =>
      simp [B, B1]
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
      omega


lemma B_gcd_div_fib_sub_1 (k : ℕ) (d : ℕ) (hd_Bkp1_sub_1 : (d : ℤ) ∣ (B (k+1) : ℤ) - 1) (hd_Bk_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1) (j : ℕ) (hj_pos : 1 ≤ j) (hj : j ≤ k) :
  (d : ℤ) ∣ (B (k - j) : ℤ) - (-1 : ℤ)^j * (Nat.fib (j - 1) : ℤ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | j
    · omega
    · rcases j with _ | j
      · -- j = 1: B (k - 1)
        have h_rec : B (k + 1) = B k + B (k - 1) := by
          have hk : k ≥ 1 := by omega
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          subst hm
          rfl
        have h_rec_z : (B (k + 1) : ℤ) = (B k : ℤ) + (B (k - 1) : ℤ) := by exact_mod_cast h_rec
        have h_sub_1 : (B (k - 1) : ℤ) = ((B (k + 1) : ℤ) - 1) - ((B k : ℤ) - 1) := by omega
        have hd_sub_1 : (d : ℤ) ∣ (B (k - 1) : ℤ) := by
          rw [h_sub_1]
          exact dvd_sub hd_Bkp1_sub_1 hd_Bk_sub_1
        have h_simp : (B (k - 1) : ℤ) - (-1 : ℤ)^1 * (Nat.fib 0 : ℤ) = (B (k - 1) : ℤ) := by simp
        rw [h_simp]
        exact hd_sub_1
      · rcases j with _ | j
        · -- j = 2: B (k - 2) - 1
          have h_rec1 : B (k + 1) = B k + B (k - 1) := by
            have hk : k ≥ 1 := by omega
            obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
            subst hm
            rfl
          have h_rec2 : B k = B (k - 1) + B (k - 2) := by
            have hk : k ≥ 2 := by omega
            obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k - 1 ≠ 0)
            have h_sub : k - 1 = m + 1 := by omega
            have h_orig : k = m + 2 := by omega
            rw [h_orig]
            rfl
          have h_rec1_z : (B (k + 1) : ℤ) = (B k : ℤ) + (B (k - 1) : ℤ) := by exact_mod_cast h_rec1
          have h_rec2_z : (B k : ℤ) = (B (k - 1) : ℤ) + (B (k - 2) : ℤ) := by exact_mod_cast h_rec2
          have h_sub_1 : (B (k - 2) : ℤ) - 1 = ((B k : ℤ) - 1) - (((B (k + 1) : ℤ) - 1) - ((B k : ℤ) - 1)) := by omega
          have hd_sub_1 : (d : ℤ) ∣ (B (k - 2) : ℤ) - 1 := by
            rw [h_sub_1]
            exact dvd_sub hd_Bk_sub_1 (dvd_sub hd_Bkp1_sub_1 hd_Bk_sub_1)
          have h_simp : (B (k - 2) : ℤ) - (-1 : ℤ)^2 * (Nat.fib 1 : ℤ) = (B (k - 2) : ℤ) - 1 := by simp
          rw [h_simp]
          exact hd_sub_1
        · -- j >= 3: j + 3
          have ih1 := ih (j + 1) (by omega) (by omega) (by omega)
          have ih2 := ih (j + 2) (by omega) (by omega) (by omega)
          have h_idx1 : k - (j + 1) = k - 1 - j := by omega
          have h_idx2 : k - (j + 2) = k - 2 - j := by omega
          rw [h_idx1] at ih1
          rw [h_idx2] at ih2
          have h_rec_B : B (k - 1 - j) = B (k - 2 - j) + B (k - 3 - j) := by
            have h1 : k - 1 - j = (k - 3 - j) + 2 := by omega
            have h2 : k - 2 - j = (k - 3 - j) + 1 := by omega
            rw [h1, h2]
            rfl
          have h_rec_B_z : (B (k - 1 - j) : ℤ) = (B (k - 2 - j) : ℤ) + (B (k - 3 - j) : ℤ) := by exact_mod_cast h_rec_B
          have h_fib : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
          have h_fib_z : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by exact_mod_cast h_fib
          have h_comb : (B (k - 3 - j) : ℤ) - (-1 : ℤ)^(j + 3) * (Nat.fib (j + 2) : ℤ) =
            ((B (k - 1 - j) : ℤ) - (-1 : ℤ)^(j + 1) * (Nat.fib j : ℤ)) -
            ((B (k - 2 - j) : ℤ) - (-1 : ℤ)^(j + 2) * (Nat.fib (j + 1) : ℤ)) := by
            have h_pow1 : (-1 : ℤ)^(j + 3) = -(-1 : ℤ)^j := by rw [pow_add, pow_three]; ring
            have h_pow2 : (-1 : ℤ)^(j + 1) = -(-1 : ℤ)^j := by rw [pow_add, pow_one]; ring
            have h_pow3 : (-1 : ℤ)^(j + 2) = (-1 : ℤ)^j := by rw [pow_add, pow_two]; ring
            rw [h_rec_B_z, h_fib_z, h_pow1, h_pow2, h_pow3]
            ring
          have h_index : k - (j + 3) = k - 3 - j := by omega
          rw [h_index]
          have h_goal_pow : (-1 : ℤ)^(j + 2 + 1) = (-1 : ℤ)^(j + 3) := rfl
          have h_goal_fib : (Nat.fib (j + 2 + 1 - 1) : ℤ) = (Nat.fib (j + 2) : ℤ) := by
            have : j + 2 + 1 - 1 = j + 2 := rfl
            rw [this]
          rw [h_goal_pow, h_goal_fib]
          rw [h_comb]
          exact dvd_sub ih1 ih2

theorem B0_sub_1_eq : B 0 - 1 = (A355898_loop 3772 1 1).1 := by
  simp [B, B0]
  rw [loop_3772_eq]

theorem B1_sub_1_eq : B 1 - 1 = (A355898_loop 3772 1 1).2 := by
  simp [B, B1]
  rw [loop_3772_eq]

theorem gcd_step (k : ℕ) :
  Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = Nat.gcd (B (k + 1) - 1) (B k) := by
  have h_rec : B (k + 2) = B (k + 1) + B k := rfl
  have h_sub : B (k + 2) - 1 = B (k + 1) - 1 + B k := by
    have h_ge1 : 1 ≤ B (k + 1) := B_pos (k + 1)
    omega
  rw [h_sub]
  rw [add_comm (B (k + 1) - 1) (B k)]
  rw [Nat.gcd_add_self_left]
  rw [Nat.gcd_comm]

theorem gcd_step2 (k : ℕ) (hk : 1 ≤ k) :
  Nat.gcd (B (k + 1) - 1) (B k) = Nat.gcd (B k) (B (k - 1) - 1) := by
  have h_sub : B (k + 1) - 1 = B k + (B (k - 1) - 1) := by
    have h_rec : B (k + 1) = B k + B (k - 1) := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      subst hm
      rfl
    have : 1 ≤ B (k - 1) := B_pos (k - 1)
    omega
  rw [h_sub]
  rw [Nat.gcd_comm (B k + (B (k - 1) - 1)) (B k)]
  rw [add_comm (B k) (B (k - 1) - 1)]
  rw [Nat.gcd_add_self_right]


theorem G_relation (k : ℕ) (hk : 1 ≤ k) :
  Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = Nat.gcd (B k) (B (k - 1) - 1) := by
  rw [gcd_step, gcd_step2 k hk]


theorem P_coprime2 (k : ℕ) :
  Nat.gcd (Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1)) (Nat.gcd (B (k + 1) - 1) (B k - 1)) = 1 := by
  set g := Nat.gcd (Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1)) (Nat.gcd (B (k + 1) - 1) (B k - 1))
  have hg1 : g ∣ Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ Nat.gcd (B (k + 1) - 1) (B k - 1) := Nat.gcd_dvd_right _ _
  have h_gcd : Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = Nat.gcd (B (k + 1) - 1) (B k) := gcd_step k
  rw [h_gcd] at hg1
  have hg1' : g ∣ B k := by
    have : Nat.gcd (B (k + 1) - 1) (B k) ∣ B k := Nat.gcd_dvd_right _ _
    exact Nat.dvd_trans hg1 this
  have hg2' : g ∣ B k - 1 := by
    have : Nat.gcd (B (k + 1) - 1) (B k - 1) ∣ B k - 1 := Nat.gcd_dvd_right _ _
    exact Nat.dvd_trans hg2 this
  have h_coprime : Nat.gcd (B k) (B k - 1) = 1 := by
    have h_rec : B k = (B k - 1) + 1 := by
      have : 1 ≤ B k := B_pos k
      omega
    rw [h_rec]
    rw [add_comm]
    have h_cancel : 1 + (B k - 1) - 1 = B k - 1 := by omega
    rw [h_cancel]
    rw [Nat.gcd_add_self_left]
    exact Nat.gcd_one_left _
  have h_g_dvd : g ∣ Nat.gcd (B k) (B k - 1) := Nat.dvd_gcd hg1' hg2'
  rw [h_coprime] at h_g_dvd
  exact Nat.eq_one_of_dvd_one h_g_dvd

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by decide

theorem base_gcd_1 : Nat.gcd (B 2 - 1) (B 1 - 1) = 1 := by decide

theorem base_gcd_2 : Nat.gcd (B 3 - 1) (B 2 - 1) = 1 := by decide

theorem base_gcd_3 : Nat.gcd (B 4 - 1) (B 3 - 1) = 1 := by decide

theorem base_gcd_4 : Nat.gcd (B 5 - 1) (B 4 - 1) = 1 := by decide

theorem base_gcd_5 : Nat.gcd (B 6 - 1) (B 5 - 1) = 1 := by decide

def C_val : ℕ := B 1^2 - B 2 * B 0

theorem B_le : B 2 * B 0 ≤ B 1^2 := by
  have h_B2 : B 2 = B 1 + B 0 := rfl
  have h_B1 : B 1 = B1 := rfl
  have h_B0 : B 0 = B0 := rfl
  rw [h_B2, h_B1, h_B0]
  unfold B1 B0
  decide

theorem Cassini (k : ℕ) :
  (Even k → B (k + 1)^2 = B (k + 2) * B k + C_val) ∧
  (Odd k → B (k + 2) * B k = B (k + 1)^2 + C_val) := by
  induction k with
  | zero =>
    constructor
    · intro _
      simp [B, C_val]
      exact (Nat.add_sub_of_le B_le).symm
    · intro h
      rcases h with ⟨r, hr⟩
      omega
  | succ k ih =>
    constructor
    · intro h_even
      have h_odd : Odd k := by
        rcases h_even with ⟨r, hr⟩
        have : r ≠ 0 := by omega
        use r - 1
        omega
      have ih_odd := ih.2 h_odd
      have h_rec : B (k + 3) = B (k + 2) + B (k + 1) := rfl
      rw [h_rec]
      rw [add_mul]
      have h_sq : B (k + 1) * B (k + 1) = B (k + 1)^2 := by ring
      rw [h_sq]
      have h_assoc : B (k + 2) * B (k + 1) + B (k + 1)^2 + C_val = B (k + 2) * B (k + 1) + (B (k + 1)^2 + C_val) := by ring
      rw [h_assoc, ← ih_odd]
      have h_rec2 : B (k + 2) = B (k + 1) + B k := rfl
      have h_algebra : B (k + 2) * B (k + 1) + B (k + 2) * B k = B (k + 2) * B (k + 2) := by
        rw [← mul_add, ← h_rec2]
      rw [h_algebra]
      ring
    · intro h_odd
      have h_even : Even k := by
        rcases h_odd with ⟨r, hr⟩
        use r
        omega
      have ih_even := ih.1 h_even
      have h_rec : B (k + 3) = B (k + 2) + B (k + 1) := rfl
      rw [h_rec]
      rw [add_mul]
      have h_sq : B (k + 1) * B (k + 1) = B (k + 1)^2 := by ring
      rw [h_sq, ih_even]
      have h_rec2 : B (k + 2) = B (k + 1) + B k := rfl
      have h_algebra : B (k + 2) * B (k + 1) + (B (k + 2) * B k + C_val) = B (k + 2) * B (k + 2) + C_val := by
        rw [← add_assoc, ← mul_add, ← h_rec2]
      rw [h_algebra]
      ring

lemma odd_of_dvd_odd {a d : ℕ} (h_div : d ∣ a) (h_odd : a % 2 = 1) : d % 2 = 1 := by
  by_contra h
  have h_even : d % 2 = 0 := by omega
  have h_2_dvd_d : 2 ∣ d := Nat.dvd_of_mod_eq_zero h_even
  have h_2_dvd_a : 2 ∣ a := Nat.dvd_trans h_2_dvd_d h_div
  have h_a_even : a % 2 = 0 := Nat.mod_eq_zero_of_dvd h_2_dvd_a
  omega

theorem B_even (k : ℕ) : B k % 2 = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [B, B0]; decide
    · rcases k with _ | k
      · simp [B, B1]; decide
      · have h_rec : B (k + 2) = B (k + 1) + B k := rfl
        rw [h_rec]
        have ih1 := ih (k + 1) (by omega)
        have ih2 := ih k (by omega)
        omega

lemma B_gcd_div_fib (k : ℕ) (d : ℕ) (hd_Bkp1 : d ∣ B (k+1)) (hd_B_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1) (j : ℕ) (hj : j ≤ k + 1) :
  (d : ℤ) ∣ (B (k + 1 - j) : ℤ) + (-1 : ℤ)^j * (Nat.fib j : ℤ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | j
    · simp only [Nat.sub_zero, pow_zero, Int.ofNat_zero, mul_zero, add_zero]
      exact_mod_cast hd_Bkp1
    · rcases j with _ | j
      · have h_eq : k + 1 - 1 = k := by omega
        rw [h_eq]
        change (d : ℤ) ∣ (B k : ℤ) - 1
        exact hd_B_sub_1
      · have ih1 := ih j (by omega) (by omega)
        have ih2 := ih (j + 1) (by omega) (by omega)
        have h_idx2 : k + 1 - (j + 1) = k - j := by omega
        rw [h_idx2] at ih2
        have h_rec_B : B (k + 1 - j) = B (k - j) + B (k - 1 - j) := by
          have h1 : k + 1 - j = (k - 1 - j) + 2 := by omega
          have h2 : k - j = (k - 1 - j) + 1 := by omega
          rw [h1, h2]
          rfl
        have h_rec_B_z : (B (k + 1 - j) : ℤ) = (B (k - j) : ℤ) + (B (k - 1 - j) : ℤ) := by exact_mod_cast h_rec_B
        have h_fib : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
        have h_fib_z : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by exact_mod_cast h_fib
        have h_comb : (B (k - 1 - j) : ℤ) + (-1 : ℤ)^(j + 2) * (Nat.fib (j + 2) : ℤ) =
          ((B (k + 1 - j) : ℤ) + (-1 : ℤ)^j * (Nat.fib j : ℤ)) -
          ((B (k - j) : ℤ) + (-1 : ℤ)^(j + 1) * (Nat.fib (j + 1) : ℤ)) := by
          have h_pow1 : (-1 : ℤ)^(j + 2) = (-1 : ℤ)^j := by rw [pow_add, pow_two]; ring
          have h_pow2 : (-1 : ℤ)^(j + 1) = -(-1 : ℤ)^j := by rw [pow_add, pow_one]; ring
          rw [h_rec_B_z, h_fib_z, h_pow1, h_pow2]
          ring
        have h_index : k + 1 - (j + 2) = k - 1 - j := by omega
        rw [h_index]
        have h_goal_pow : (-1 : ℤ)^(j + 1 + 1) = (-1 : ℤ)^(j + 2) := rfl
        have h_goal_fib : (Nat.fib (j + 1 + 1) : ℤ) = (Nat.fib (j + 2) : ℤ) := rfl
        rw [h_goal_pow, h_goal_fib]
        rw [h_comb]
        exact dvd_sub ih1 ih2


theorem B_fib_rep (k : ℕ) (hk : 1 ≤ k) : B k = B 1 * Nat.fib k + B 0 * Nat.fib (k - 1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · omega
    · rcases k with _ | k
      · simp [B]
      · rcases k with _ | k
        · simp [B]
        · have h_rec : B (k + 3) = B (k + 2) + B (k + 1) := rfl
          have ih1 := ih (k + 2) (by omega) (by omega)
          have ih2 := ih (k + 1) (by omega) (by omega)
          rw [h_rec, ih1, ih2]
          have h_fib1 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
          have h_fib2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
          have h_sub1 : k + 2 - 1 = k + 1 := by omega
          have h_sub2 : k + 1 - 1 = k := by omega
          have h_sub3 : k + 3 - 1 = k + 2 := by omega
          rw [h_sub1, h_sub2, h_sub3]
          rw [h_fib1, h_fib2]
          ring

theorem fib_Cassini (k : ℕ) :
  (Even k → Nat.fib (k + 1)^2 = Nat.fib (k + 2) * Nat.fib k + 1) ∧
  (Odd k → Nat.fib (k + 2) * Nat.fib k = Nat.fib (k + 1)^2 + 1) := by
  induction k with
  | zero =>
    constructor
    · intro _
      rfl
    · intro h
      rcases h with ⟨r, hr⟩
      omega
  | succ k ih =>
    constructor
    · intro h_even
      have h_odd : Odd k := by
        rcases h_even with ⟨r, hr⟩
        have : r ≠ 0 := by omega
        use r - 1
        omega
      have ih_odd := ih.2 h_odd
      have h_rec : Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) := by rw [@Nat.fib_add_two (k + 1), add_comm]
      rw [h_rec]
      rw [add_mul]
      have h_sq : Nat.fib (k + 1) * Nat.fib (k + 1) = Nat.fib (k + 1)^2 := by ring
      rw [h_sq]
      have h_assoc : Nat.fib (k + 2) * Nat.fib (k + 1) + Nat.fib (k + 1)^2 + 1 = Nat.fib (k + 2) * Nat.fib (k + 1) + (Nat.fib (k + 1)^2 + 1) := by ring
      rw [h_assoc, ← ih_odd]
      have h_rec2 : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := by rw [@Nat.fib_add_two k, add_comm]
      have h_algebra : Nat.fib (k + 2) * Nat.fib (k + 1) + Nat.fib (k + 2) * Nat.fib k = Nat.fib (k + 2) * Nat.fib (k + 2) := by
        rw [← mul_add, ← h_rec2]
      rw [h_algebra]
      ring
    · intro h_odd
      have h_even : Even k := by
        rcases h_odd with ⟨r, hr⟩
        use r
        omega
      have ih_even := ih.1 h_even
      have h_rec : Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) := by rw [@Nat.fib_add_two (k + 1), add_comm]
      rw [h_rec]
      rw [add_mul]
      have h_sq : Nat.fib (k + 1) * Nat.fib (k + 1) = Nat.fib (k + 1)^2 := by ring
      rw [h_sq, ih_even]
      have h_rec2 : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := by rw [@Nat.fib_add_two k, add_comm]
      have h_algebra : Nat.fib (k + 2) * Nat.fib (k + 1) + (Nat.fib (k + 2) * Nat.fib k + 1) = Nat.fib (k + 2) * Nat.fib (k + 2) + 1 := by
        rw [← add_assoc, ← mul_add, ← h_rec2]
      rw [h_algebra]
      ring


lemma fib_identity_reduction (k : ℕ) (hk : 2 ≤ k) :
  (Nat.fib (k - 2) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k - 1) : ℤ) * (Nat.fib k : ℤ) =
  (Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2 := by
  have h_rec : Nat.fib (k + 1) = Nat.fib k + Nat.fib (k - 1) := by
    have h1 : k + 1 = (k - 1) + 2 := by omega
    nth_rw 1 [h1]
    rw [Nat.fib_add_two]
    have h3 : k - 1 + 1 = k := by omega
    rw [h3]
    rw [add_comm]
  have h_rec_z : (Nat.fib (k + 1) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k - 1) : ℤ) := by exact_mod_cast h_rec
  have h_rec2 : Nat.fib k = Nat.fib (k - 1) + Nat.fib (k - 2) := by
    have h1 : k = (k - 2) + 2 := by omega
    nth_rw 1 [h1]
    rw [Nat.fib_add_two]
    have h3 : k - 2 + 1 = k - 1 := by omega
    rw [h3]
    rw [add_comm]
  have h_rec2_z : (Nat.fib k : ℤ) = (Nat.fib (k - 1) : ℤ) + (Nat.fib (k - 2) : ℤ) := by exact_mod_cast h_rec2
  rw [h_rec_z, h_rec2_z]
  ring

lemma fib_identity_proven (k : ℕ) (hk : 2 ≤ k) :
  (Nat.fib (k - 2) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k - 1) : ℤ) * (Nat.fib k : ℤ) = (-1 : ℤ)^(k - 1) := by
  have h_red := fib_identity_reduction k hk
  rw [h_red]
  have h_cass := fib_Cassini (k - 2)
  by_cases h_even : Even (k - 2)
  · have h_even_val := h_cass.1 h_even
    have h_idx1 : k - 2 + 1 = k - 1 := by omega
    have h_idx2 : k - 2 + 2 = k := by omega
    rw [h_idx1, h_idx2] at h_even_val
    have h_even_val_z : (Nat.fib (k - 1) : ℤ)^2 = (Nat.fib k : ℤ) * (Nat.fib (k - 2) : ℤ) + 1 := by exact_mod_cast h_even_val
    have h_pow : (-1 : ℤ)^(k - 1) = -1 := by
      rcases h_even with ⟨r, hr⟩
      have hk_val : k - 1 = 2 * r + 1 := by omega
      rw [hk_val]
      rw [pow_add, pow_one, pow_mul]
      ring
    rw [h_pow]
    linarith
  · have h_odd : Odd (k - 2) := (Nat.even_or_odd (k - 2)).resolve_left h_even
    have h_odd_val := h_cass.2 h_odd
    have h_idx1 : k - 2 + 1 = k - 1 := by omega
    have h_idx2 : k - 2 + 2 = k := by omega
    rw [h_idx1, h_idx2] at h_odd_val
    have h_odd_val_z : (Nat.fib k : ℤ) * (Nat.fib (k - 2) : ℤ) = (Nat.fib (k - 1) : ℤ)^2 + 1 := by exact_mod_cast h_odd_val
    have h_pow : (-1 : ℤ)^(k - 1) = 1 := by
      rcases h_odd with ⟨r, hr⟩
      have hk_val : k - 1 = 2 * (r + 1) := by omega
      rw [hk_val]
      rw [pow_mul]
      ring
    rw [h_pow]
    linarith


lemma B_ge_13 (n : ℕ) : 13 ≤ B n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · unfold B B0 S3772_fst; omega
    · rcases n with _ | n
      · unfold B B1 S3772_snd; omega
      · have h_rec : B (n + 2) = B (n + 1) + B n := rfl
        rw [h_rec]
        have ih1 := ih (n + 1) (by omega)
        omega

lemma B_gcd_div_fib_dual (k : ℕ) (d : ℕ) (hd_Bkp1_sub_1 : (d : ℤ) ∣ (B (k+1) : ℤ) - 1) (hd_Bk : (d : ℤ) ∣ (B k : ℤ)) (j : ℕ) (hj : j ≤ k) :
  (d : ℤ) ∣ (B (k - j) : ℤ) + (-1 : ℤ)^j * (Nat.fib j : ℤ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | j
    · simp only [Nat.sub_zero, pow_zero, Int.ofNat_zero, mul_zero, add_zero]
      exact hd_Bk
    · rcases j with _ | j
      · have h_rec : B (k + 1) = B k + B (k - 1) := by
          have hk : k ≥ 1 := by omega
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          subst hm
          rfl
        have h_rec_z : (B (k + 1) : ℤ) = (B k : ℤ) + (B (k - 1) : ℤ) := by exact_mod_cast h_rec
        have h_sub_1 : (B (k - 1) : ℤ) - 1 = ((B (k + 1) : ℤ) - 1) - (B k : ℤ) := by omega
        have hd_sub_1 : (d : ℤ) ∣ (B (k - 1) : ℤ) - 1 := by
          rw [h_sub_1]
          exact dvd_sub hd_Bkp1_sub_1 hd_Bk
        exact hd_sub_1
      · have ih1 := ih j (by omega) (by omega)
        have ih2 := ih (j + 1) (by omega) (by omega)
        have h_idx2 : k - (j + 1) = k - 1 - j := by omega
        rw [h_idx2] at ih2
        have h_rec_B : B (k - j) = B (k - 1 - j) + B (k - 2 - j) := by
          have h1 : k - j = (k - 2 - j) + 2 := by omega
          have h2 : k - 1 - j = (k - 2 - j) + 1 := by omega
          rw [h1, h2]
          rfl
        have h_rec_B_z : (B (k - j) : ℤ) = (B (k - 1 - j) : ℤ) + (B (k - 2 - j) : ℤ) := by exact_mod_cast h_rec_B
        have h_fib : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
        have h_fib_z : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by exact_mod_cast h_fib
        have h_comb : (B (k - 2 - j) : ℤ) + (-1 : ℤ)^(j + 2) * (Nat.fib (j + 2) : ℤ) =
          ((B (k - j) : ℤ) + (-1 : ℤ)^j * (Nat.fib j : ℤ)) -
          ((B (k - 1 - j) : ℤ) + (-1 : ℤ)^(j + 1) * (Nat.fib (j + 1) : ℤ)) := by
          have h_pow1 : (-1 : ℤ)^(j + 2) = (-1 : ℤ)^j := by rw [pow_add, pow_two]; ring
          have h_pow2 : (-1 : ℤ)^(j + 1) = -(-1 : ℤ)^j := by rw [pow_add, pow_one]; ring
          rw [h_rec_B_z, h_fib_z, h_pow1, h_pow2]
          ring
        have h_index : k - (j + 2) = k - 2 - j := by omega
        rw [h_index]
        have h_goal_pow : (-1 : ℤ)^(j + 1 + 1) = (-1 : ℤ)^(j + 2) := rfl
        have h_goal_fib : (Nat.fib (j + 1 + 1) : ℤ) = (Nat.fib (j + 2) : ℤ) := rfl
        rw [h_goal_pow, h_goal_fib]
        rw [h_comb]
        exact dvd_sub ih1 ih2

lemma B_gcd_div_C_val_dual (k : ℕ) (hk : 2 ≤ k) (d : ℕ) (hd1_z : (d : ℤ) ∣ (B (k + 1) : ℤ) - 1) (hd2_z : (d : ℤ) ∣ (B k : ℤ)) :
  (d : ℤ) ∣ (C_val : ℤ) - (-1 : ℤ)^k := by
  have h_div_k := B_gcd_div_fib_dual k d hd1_z hd2_z k (by omega)
  have h_div_km1 := B_gcd_div_fib_dual k d hd1_z hd2_z (k - 1) (by omega)
  have h_sub_k : k - k = 0 := by omega
  have h_sub_km1 : k - (k - 1) = 1 := by omega
  rw [h_sub_k] at h_div_k
  rw [h_sub_km1] at h_div_km1
  obtain ⟨q_k, hq_k⟩ := h_div_k
  obtain ⟨q_km1, hq_km1⟩ := h_div_km1
  have hB0_z : (B 0 : ℤ) = d * q_k - (-1 : ℤ)^k * (Nat.fib k : ℤ) := by omega
  have hB1_z : (B 1 : ℤ) = d * q_km1 - (-1 : ℤ)^(k - 1) * (Nat.fib (k - 1) : ℤ) := by omega

  set F_k := (Nat.fib k : ℤ)
  set F_km1 := (Nat.fib (k - 1) : ℤ)
  set F_km2 := (Nat.fib (k - 2) : ℤ)

  have h_fib_id : (Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2 = (-1 : ℤ)^(k - 1) := by
    rw [← fib_identity_reduction k hk, fib_identity_proven k hk]
  have h_fib_rec : (Nat.fib k : ℤ) = (Nat.fib (k - 1) : ℤ) + (Nat.fib (k - 2) : ℤ) := by
    have h1 : k = (k - 2) + 2 := by omega
    nth_rw 1 [h1]
    rw [Nat.fib_add_two]
    have h3 : k - 2 + 1 = k - 1 := by omega
    rw [h3]
    push_cast
    ring
  have h_fib_expand : F_km1^2 - F_km1 * F_km2 - F_km2^2 = - (-1 : ℤ)^(k - 1) := by
    have : F_km1^2 - F_km1 * F_km2 - F_km2^2 = - ((Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2) := by
      rw [h_fib_rec]
      ring
    rw [this, h_fib_id]

  have h_pow : (-1 : ℤ)^k = - (-1 : ℤ)^(k - 1) := by
    have : k = (k - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_add, pow_one]
    ring

  have h_C_val : (C_val : ℤ) = (B 1 : ℤ)^2 - ((B 1 : ℤ) + (B 0 : ℤ)) * (B 0 : ℤ) := by
    have h_C : C_val = B 1^2 - B 2 * B 0 := rfl
    have h_le : B 2 * B 0 ≤ B 1^2 := B_le
    rw [h_C]
    rw [Nat.cast_sub h_le]
    push_cast
    have h_rec : B 2 = B 1 + B 0 := rfl
    rw [h_rec]
    push_cast
    ring

  rw [h_C_val, hB0_z, hB1_z]
  have h_P_sq : (-1 : ℤ)^(k - 1) * (-1 : ℤ)^(k - 1) = 1 := by
    rw [← pow_two]
    have : (-1 : ℤ)^2 = 1 := rfl
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have h_F_k : F_k = F_km1 + F_km2 := h_fib_rec
  have h_alg : (d * q_km1 - (-1 : ℤ)^(k - 1) * F_km1)^2 - ((d * q_km1 - (-1 : ℤ)^(k - 1) * F_km1) + (d * q_k - (-1 : ℤ)^k * F_k)) * (d * q_k - (-1 : ℤ)^k * F_k) - (-1 : ℤ)^k =
    d * (q_km1^2 * d - 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km1 - q_km1 * q_k * d + q_km1 * (-1 : ℤ)^k * F_k + q_k * (-1 : ℤ)^(k - 1) * F_km1 - q_k^2 * d + 2 * q_k * (-1 : ℤ)^k * F_k) +
    ((-1 : ℤ)^(k - 1) * (-1 : ℤ)^(k - 1)) * (F_km1^2 + F_km1 * F_k - F_k^2) - (-1 : ℤ)^k := by
    rw [h_pow]
    ring
  rw [h_alg, h_P_sq]
  have h_finish : (1 : ℤ) * (F_km1^2 + F_km1 * F_k - F_k^2) - (-1 : ℤ)^k = 0 := by
    rw [h_pow, h_F_k]
    linarith [h_fib_expand]
  have h_goal_eq : d * (q_km1^2 * d - 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km1 - q_km1 * q_k * d + q_km1 * (-1 : ℤ)^k * F_k + q_k * (-1 : ℤ)^(k - 1) * F_km1 - q_k^2 * d + 2 * q_k * (-1 : ℤ)^k * F_k) + 1 * (F_km1^2 + F_km1 * F_k - F_k^2) - (-1 : ℤ)^k = d * (q_km1^2 * d - 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_km1 - q_km1 * q_k * d + q_km1 * (-1 : ℤ)^k * F_k + q_k * (-1 : ℤ)^(k - 1) * F_km1 - q_k^2 * d + 2 * q_k * (-1 : ℤ)^k * F_k) := by
    linarith [h_finish]
  rw [h_goal_eq]
  exact dvd_mul_right _ _


lemma B_gcd_div_C_val (k : ℕ) (hk : 2 ≤ k) (d : ℕ) (hd1 : d ∣ B (k + 1)) (hd2_z : (d : ℤ) ∣ (B k : ℤ) - 1) :
  (d : ℤ) ∣ (C_val : ℤ) + (-1 : ℤ)^k := by
  have h_div_kp1 : (d : ℤ) ∣ (B (k + 1) : ℤ) := by exact_mod_cast hd1
  have h_div_k := B_gcd_div_fib k d hd1 hd2_z (k + 1) (by omega)
  have h_div_km1 := B_gcd_div_fib k d hd1 hd2_z k (by omega)
  have h_sub_k : k + 1 - (k + 1) = 0 := by omega
  have h_sub_km1 : k + 1 - k = 1 := by omega
  rw [h_sub_k] at h_div_k
  rw [h_sub_km1] at h_div_km1
  obtain ⟨q_k, hq_k⟩ := h_div_k
  obtain ⟨q_km1, hq_km1⟩ := h_div_km1
  have hB0_z : (B 0 : ℤ) = d * q_k - (-1 : ℤ)^(k + 1) * (Nat.fib (k + 1) : ℤ) := by omega
  have hB1_z : (B 1 : ℤ) = d * q_km1 - (-1 : ℤ)^k * (Nat.fib k : ℤ) := by omega

  set F_kp1 := (Nat.fib (k + 1) : ℤ)
  set F_k := (Nat.fib k : ℤ)
  set F_km1 := (Nat.fib (k - 1) : ℤ)

  have h_fib_id : (Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2 = (-1 : ℤ)^(k - 1) := by
    rw [← fib_identity_reduction k hk, fib_identity_proven k hk]
  have h_fib_rec : (Nat.fib k : ℤ) = (Nat.fib (k - 1) : ℤ) + (Nat.fib (k - 2) : ℤ) := by
    have h1 : k = (k - 2) + 2 := by omega
    nth_rw 1 [h1]
    rw [Nat.fib_add_two]
    have h3 : k - 2 + 1 = k - 1 := by omega
    rw [h3]
    push_cast
    ring
  have h_fib_rec_p1 : (Nat.fib (k + 1) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k - 1) : ℤ) := by
    have h1 : k + 1 = (k - 1) + 2 := by omega
    nth_rw 1 [h1]
    rw [Nat.fib_add_two]
    have h3 : k - 1 + 1 = k := by omega
    rw [h3]
    push_cast
    ring
  have h_fib_expand : F_km1^2 - F_km1 * (Nat.fib (k - 2) : ℤ) - (Nat.fib (k - 2) : ℤ)^2 = - (-1 : ℤ)^(k - 1) := by
    have : F_km1^2 - F_km1 * (Nat.fib (k - 2) : ℤ) - (Nat.fib (k - 2) : ℤ)^2 = - ((Nat.fib (k - 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k - 1) : ℤ)^2) := by
      rw [h_fib_rec]
      ring
    rw [this, h_fib_id]

  have h_pow : (-1 : ℤ)^k = - (-1 : ℤ)^(k - 1) := by
    have : k = (k - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_add, pow_one]
    ring
  have h_pow_p1 : (-1 : ℤ)^(k + 1) = (-1 : ℤ)^(k - 1) := by
    have : k + 1 = (k - 1) + 2 := by omega
    rw [this, pow_add]
    ring

  have h_C_val : (C_val : ℤ) = (B 1 : ℤ)^2 - ((B 1 : ℤ) + (B 0 : ℤ)) * (B 0 : ℤ) := by
    have h_C : C_val = B 1^2 - B 2 * B 0 := rfl
    have h_le : B 2 * B 0 ≤ B 1^2 := B_le
    rw [h_C]
    rw [Nat.cast_sub h_le]
    push_cast
    have h_rec : B 2 = B 1 + B 0 := rfl
    rw [h_rec]
    push_cast
    ring

  rw [h_C_val, hB0_z, hB1_z, h_pow, h_pow_p1]
  have h_P_sq : (-1 : ℤ)^(k - 1) * (-1 : ℤ)^(k - 1) = 1 := by
    rw [← pow_two]
    have : (-1 : ℤ)^2 = 1 := rfl
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have h_F_kp1 : F_kp1 = F_k + F_km1 := h_fib_rec_p1
  have h_F_k : F_k = F_km1 + (Nat.fib (k - 2) : ℤ) := h_fib_rec
  have h_alg : (d * q_km1 - -(-1 : ℤ)^(k - 1) * F_k)^2 - ((d * q_km1 - -(-1 : ℤ)^(k - 1) * F_k) + (d * q_k - (-1 : ℤ)^(k - 1) * F_kp1)) * (d * q_k - (-1 : ℤ)^(k - 1) * F_kp1) + -(-1 : ℤ)^(k - 1) =
    d * (q_km1^2 * d - q_km1 * q_k * d - q_k^2 * d + 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_k + q_km1 * (-1 : ℤ)^(k - 1) * F_kp1 - q_k * (-1 : ℤ)^(k - 1) * F_k + 2 * q_k * (-1 : ℤ)^(k - 1) * F_kp1) +
    ((-1 : ℤ)^(k - 1) * (-1 : ℤ)^(k - 1)) * (F_k^2 + F_k * F_kp1 - F_kp1^2) - (-1 : ℤ)^(k - 1) := by
    ring
  rw [h_alg, h_P_sq]
  have h_finish : (1 : ℤ) * (F_k^2 + F_k * F_kp1 - F_kp1^2) - (-1 : ℤ)^(k - 1) = 0 := by
    rw [h_F_kp1, h_F_k]
    linarith [h_fib_expand]
  have h_goal_eq : d * (q_km1^2 * d - q_km1 * q_k * d - q_k^2 * d + 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_k + q_km1 * (-1 : ℤ)^(k - 1) * F_kp1 - q_k * (-1 : ℤ)^(k - 1) * F_k + 2 * q_k * (-1 : ℤ)^(k - 1) * F_kp1) + 1 * (F_k^2 + F_k * F_kp1 - F_kp1^2) - (-1 : ℤ)^(k - 1) = d * (q_km1^2 * d - q_km1 * q_k * d - q_k^2 * d + 2 * q_km1 * (-1 : ℤ)^(k - 1) * F_k + q_km1 * (-1 : ℤ)^(k - 1) * F_kp1 - q_k * (-1 : ℤ)^(k - 1) * F_k + 2 * q_k * (-1 : ℤ)^(k - 1) * F_kp1) := by
    linarith [h_finish]
  rw [h_goal_eq]
  exact dvd_mul_right _ _

theorem B_gcd (k : ℕ) : Nat.gcd (B (k + 1) - 1) (B k - 1) = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · exact base_gcd_0
    · rcases k with _ | k
      · have h_gcd := gcd_step 0
        rw [h_gcd]
        exact base_gcd_1
      · -- Case k >= 2 (since k + 2)
        -- We want to prove Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1) = 1
        -- By ih at k+1: Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = 1
        have ih_kp1 := ih (k + 1) (by omega)
        -- We define d:
        set d := Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1)
        have hd1 : d ∣ B (k + 3) - 1 := Nat.gcd_dvd_left _ _
        have hd2 : d ∣ B (k + 2) - 1 := Nat.gcd_dvd_right _ _
        -- We show d ∣ B (k+1):
        have hd_Bkp1 : d ∣ B (k + 1) := by
          have hd_eq : d = Nat.gcd (B (k + 2) - 1) (B (k + 1)) := gcd_step (k + 1)
          rw [hd_eq]
          exact Nat.gcd_dvd_right _ _
        -- We cast to Int:
        have h_pos1 : 1 ≤ B (k + 3) := B_pos (k + 3)
        have h_pos2 : 1 ≤ B (k + 2) := B_pos (k + 2)
        have h_pos3 : 1 ≤ B (k + 1) := B_pos (k + 1)
        have h_pos4 : 1 ≤ B k := B_pos k
        have hd1_z : (d : ℤ) ∣ (B (k + 3) : ℤ) - 1 := by
          have h_sub : ((B (k + 3) - 1 : ℕ) : ℤ) = (B (k + 3) : ℤ) - 1 := by omega
          have hd1_cast : (d : ℤ) ∣ ((B (k + 3) - 1 : ℕ) : ℤ) := Int.ofNat_dvd.mpr hd1
          rw [h_sub] at hd1_cast
          exact hd1_cast
        have hd2_z : (d : ℤ) ∣ (B (k + 2) : ℤ) - 1 := by
          have h_sub : ((B (k + 2) - 1 : ℕ) : ℤ) = (B (k + 2) : ℤ) - 1 := by omega
          have hd2_cast : (d : ℤ) ∣ ((B (k + 2) - 1 : ℕ) : ℤ) := Int.ofNat_dvd.mpr hd2
          rw [h_sub] at hd2_cast
          exact hd2_cast
        obtain ⟨q2, hq2⟩ := hd1_z
        obtain ⟨q1, hq1⟩ := hd2_z
        obtain ⟨q3, hq3⟩ := hd_Bkp1
        have hBkp1_z : (B (k + 1) : ℤ) = d * q3 := by exact_mod_cast hq3
        have hBkp2_z : (B (k + 2) : ℤ) = d * q1 + 1 := by omega
        have hBkp3_z : (B (k + 3) : ℤ) = d * q2 + 1 := by omega
        have hBk_z : (B k : ℤ) = d * (q1 - q3) + 1 := by
          have h_rec : (B (k + 2) : ℤ) = (B (k + 1) : ℤ) + (B k : ℤ) := by
            have : B (k + 2) = B (k + 1) + B k := rfl
            omega
          rw [hBkp2_z, hBkp1_z] at h_rec
          linarith
        have hd_B_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1 := by
          use q1 - q3
          omega
        have hd_Bkm1_nat : d ∣ B k - 1 := by
          have h_cast : (B k : ℤ) - 1 = ((B k - 1 : ℕ) : ℤ) := by omega
          rw [h_cast] at hd_B_sub_1
          exact Int.ofNat_dvd.mp hd_B_sub_1
        have h_cass := Cassini (k)
        have hd_C : (d : ℤ) ∣ 2 := by
          by_cases h_even : Even (k + 1)
          · have h_odd : Odd k := by
              rcases h_even with ⟨r, hr⟩
              have : r ≠ 0 := by omega
              use r - 1
              omega
            have h_cass_odd := h_cass.2 h_odd
            have h_cast : ((B (k + 2) : ℤ) * (B k : ℤ)) = ((B (k + 1) : ℤ)^2 + (C_val : ℤ)) := by exact_mod_cast h_cass_odd
            have h_C_sub_1 : (C_val : ℤ) - 1 = (B (k + 2) : ℤ) * (B k : ℤ) - (B (k + 1) : ℤ)^2 - 1 := by
              rw [h_cast]
              ring
            have hd_C_sub_1 : (d : ℤ) ∣ (C_val : ℤ) - 1 := by
              use q1 * (q1 - q3) * d + q1 + (q1 - q3) - q3^2 * d
              rw [h_C_sub_1, hBkp2_z, hBk_z, hBkp1_z]
              ring
            have h_cass_kp1 := Cassini (k + 1)
            have h_cass_even := h_cass_kp1.1 h_even
            have h_cast_kp1 : ((B (k + 2) : ℤ)^2) = ((B (k + 3) : ℤ) * (B (k + 1) : ℤ) + (C_val : ℤ)) := by exact_mod_cast h_cass_even
            have h_C_add_1 : (C_val : ℤ) + 1 = (B (k + 2) : ℤ)^2 - (B (k + 3) : ℤ) * (B (k + 1) : ℤ) + 1 := by
              rw [h_cast_kp1]
              ring
            have hd_C_add_1 : (d : ℤ) ∣ (C_val : ℤ) + 1 := by
              use q1^2 * d + 2 * q1 - q2 * q3 * d - q3
              rw [h_C_add_1, hBkp2_z, hBkp1_z, hBkp3_z]
              ring
            have hd_diff : (d : ℤ) ∣ (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) := dvd_sub hd_C_add_1 hd_C_sub_1
            have h_ring : (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) = 2 := by ring
            rw [h_ring] at hd_diff
            exact hd_diff
          · have h_even_k : Even k := by
              have h_odd : Odd (k + 1) := by omega
              rcases h_odd with ⟨r, hr⟩
              use r
              omega
            have h_cass_even := h_cass.1 h_even_k
            have h_cast : ((B (k + 1) : ℤ)^2) = ((B (k + 2) : ℤ) * (B k : ℤ) + (C_val : ℤ)) := by exact_mod_cast h_cass_even
            have h_C_add_1 : (C_val : ℤ) + 1 = (B (k + 1) : ℤ)^2 - (B (k + 2) : ℤ) * (B k : ℤ) + 1 := by
              rw [h_cast]
              ring
            have hd_C_add_1 : (d : ℤ) ∣ (C_val : ℤ) + 1 := by
              use q3^2 * d - q1 * (q1 - q3) * d - q1 - (q1 - q3)
              rw [h_C_add_1, hBkp2_z, hBk_z, hBkp1_z]
              ring
            have h_cass_kp1 := Cassini (k + 1)
            have h_odd_kp1 : Odd (k + 1) := by omega
            have h_cass_odd := h_cass_kp1.2 h_odd_kp1
            have h_cast_kp1 : ((B (k + 3) : ℤ) * (B (k + 1) : ℤ)) = ((B (k + 2) : ℤ)^2 + (C_val : ℤ)) := by exact_mod_cast h_cass_odd
            have h_C_sub_1 : (C_val : ℤ) - 1 = (B (k + 3) : ℤ) * (B (k + 1) : ℤ) - (B (k + 2) : ℤ)^2 - 1 := by
              rw [h_cast_kp1]
              ring
            have hd_C_sub_1 : (d : ℤ) ∣ (C_val : ℤ) - 1 := by
              use q2 * q3 * d + q3 - q1^2 * d - 2 * q1
              rw [h_C_sub_1, hBkp2_z, hBkp1_z, hBkp3_z]
              ring
            have hd_diff : (d : ℤ) ∣ (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) := dvd_sub hd_C_add_1 hd_C_sub_1
            have h_ring : (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) = 2 := by ring
            rw [h_ring] at hd_diff
            exact hd_diff
        have hd_2_nat : d ∣ 2 := Int.ofNat_dvd.mp hd_C
        have hd_odd : d % 2 = 1 := by
          have h_even_Bkp1 : B (k + 2) % 2 = 0 := B_even (k + 2)
          have h_odd_Bkp1 : (B (k + 2) - 1) % 2 = 1 := by omega
          exact odd_of_dvd_odd hd2 h_odd_Bkp1
        have hd_cases : d = 1 ∨ d = 2 := by
          obtain ⟨c, hc⟩ := hd_2_nat
          cases c with
          | zero => omega
          | succ c =>
            cases c with
            | zero => omega
            | succ c =>
              have h_pos : 1 ≤ d := B_pos (k + 2) |>.trans hd2
              omega
        rcases hd_cases with hd_1 | hd_2
        · exact hd_1
        · subst hd_2
          omega

theorem loop_eq_B_gen (k : ℕ) :
  ∀ m, A355898_loop k (B m - 1) (B (m+1) - 1) = (B (k+m) - 1, B (k+m+1) - 1) := by
  induction k with
  | zero =>
    intro m
    simp [A355898_loop]
  | succ k ih =>
    intro m
    have h_gcd : Nat.gcd (B (m + 1) - 1) (B m - 1) = 1 := B_gcd m
    have h_rec : B (m + 2) = B (m + 1) + B m := rfl
    have h_pos : 1 ≤ B (m + 1) := B_pos (m + 1)
    have h_pos2 : 1 ≤ B m := B_pos m
    simp only [A355898_loop]
    rw [h_gcd]
    have h_arith : 1 + (B (m + 1) - 1 + (B m - 1)) / 1 = B (m + 2) - 1 := by
      rw [Nat.div_one]
      omega
    rw [h_arith]
    have ih_val := ih (m + 1)
    rw [ih_val]
    have h_add1 : k + (m + 1) = k + 1 + m := by omega
    rw [h_add1]

theorem B_loop_eq (k : ℕ) :
  A355898_loop k (B 0 - 1) (B 1 - 1) = (B k - 1, B (k + 1) - 1) := by
  have h := loop_eq_B_gen k 0
  simp only [add_zero] at h
  exact h

attribute [irreducible] B0 B1 A3772

theorem A355898_eq_B (n : ℕ) (h : 3773 ≤ n) :
  A355898 n = B (n - 3773) - 1 := by
  have h_eq : (A355898 n, A355898 (n + 1)) = (B (n - 3773) - 1, B (n - 3772) - 1) := by
    have h_eq_loop : (A355898 n, A355898 (n + 1)) = A355898_loop (n - 3773) (B 0 - 1) (B 1 - 1) := by
      have h_loop_eq := A355898_eq_loop (n - 1)
      have h_n : n - 1 + 1 = n := by omega
      have h_n2 : n - 1 + 2 = n + 1 := by omega
      rw [h_n, h_n2] at h_loop_eq
      rw [h_loop_eq]
      have h_sub_n : n - 1 = (n - 3773) + 3772 := by omega
      rw [h_sub_n]
      rw [A355898_loop_split 3772 (n - 3773) 1 1]
      rw [← B0_sub_1_eq, ← B1_sub_1_eq]
    have h_final := B_loop_eq (n - 3773)
    have h_trans := h_eq_loop.trans h_final
    have h_sub_1 : n - 3773 + 1 = n - 3772 := by omega
    rw [h_sub_1] at h_trans
    exact h_trans
  exact (Prod.ext_iff.mp h_eq).1

theorem A355898_3772_eq : A355898 3772 = A3772 := by
  have h1 : A355898 3772 = (A355898_loop 3771 1 1).1 := by
    have h_eq := A355898_eq_loop 3771
    exact congrArg Prod.fst h_eq
  rw [h1]
  rw [loop_3771_eq]
  unfold A3772
  rfl


theorem A3772_identity : A3772 + 1 = B 1 - B 0 := by
  unfold B
  unfold A3772 B0 B1
  decide

theorem oeis_a355898_conjecture (n : ℕ) (h : 3775 ≤ n) :
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) := by
  rcases eq_or_lt_of_le h with rfl | hn
  · have h3775 : A355898 3775 = B 2 - 1 := A355898_eq_B 3775 (by omega)
    have h3774 : A355898 3774 = B 1 - 1 := A355898_eq_B 3774 (by omega)
    have h3773 : A355898 3773 = B 0 - 1 := A355898_eq_B 3773 (by omega)
    have h3772 : A355898 3772 = A3772 := A355898_3772_eq
    have h_rec_b : B 2 = B 1 + B 0 := rfl
    have h_pos_b0 : 1 ≤ B 0 := B_pos 0
    have h_pos_b1 : 1 ≤ B 1 := B_pos 1
    rw [h3775, h3774, h3773, h3772, h_rec_b]
    have h_id := A3772_identity
    constructor
    · omega
    · constructor
      · omega
      · simp [Nat.fib]
        omega
  · -- Case 3776 ≤ n
    have h_eq : A355898 n = B (n - 3773) - 1 := A355898_eq_B n (by omega)
    have h_eq_minus1 : A355898 (n - 1) = B (n - 3774) - 1 := by
      have h_raw := A355898_eq_B (n - 1) (by omega)
      have h_sub : n - 1 - 3773 = n - 3774 := by omega
      rw [h_sub] at h_raw
      exact h_raw
    have h_eq_minus2 : A355898 (n - 2) = B (n - 3775) - 1 := by
      have h_raw := A355898_eq_B (n - 2) (by omega)
      have h_sub : n - 2 - 3773 = n - 3775 := by omega
      rw [h_sub] at h_raw
      exact h_raw
    have h_eq_minus3 : A355898 (n - 3) = B (n - 3776) - 1 := by
      have h_raw := A355898_eq_B (n - 3) (by omega)
      have h_sub : n - 3 - 3773 = n - 3776 := by omega
      rw [h_sub] at h_raw
      exact h_raw
    have h_rec : B (n - 3773) = B (n - 3774) + B (n - 3775) := by
      have h_rec_gen : B (n - 3775 + 2) = B (n - 3775 + 1) + B (n - 3775) := rfl
      have h_sub1 : n - 3775 + 2 = n - 3773 := by omega
      have h_sub2 : n - 3775 + 1 = n - 3774 := by omega
      rw [h_sub1, h_sub2] at h_rec_gen
      exact h_rec_gen
    have h_pos_1 : 1 ≤ B (n - 3774) := B_pos (n - 3774)
    have h_pos_2 : 1 ≤ B (n - 3775) := B_pos (n - 3775)
    constructor
    · rw [h_eq, h_eq_minus1, h_eq_minus2, h_rec]
      omega
    · constructor
      · rw [h_eq, h_eq_minus1, h_eq_minus3, h_rec]
        have h_rec2 : B (n - 3774) = B (n - 3775) + B (n - 3776) := by
          have h_rec_gen : B (n - 3776 + 2) = B (n - 3776 + 1) + B (n - 3776) := rfl
          have h_sub1 : n - 3776 + 2 = n - 3774 := by omega
          have h_sub2 : n - 3776 + 1 = n - 3775 := by omega
          rw [h_sub1, h_sub2] at h_rec_gen
          exact h_rec_gen
        have h_pos_3 : 1 ≤ B (n - 3776) := B_pos (n - 3776)
        rw [h_rec2]
        omega
      · -- Part 3
        rw [h_eq]
        have h_fib : B (n - 3773) = B 1 * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) := by
          have h_fib_rep_val := B_fib_rep (n - 3773) (by omega)
          have h_sub_fib : n - 3773 - 1 = n - 3774 := by omega
          rw [h_sub_fib] at h_fib_rep_val
          rw [h_fib_rep_val]
          have h_fib_add_two := @Nat.fib_add_two (n - 3774)
          have h_sub_fib2 : n - 3774 + 2 = n - 3772 := by omega
          have h_sub_fib3 : n - 3774 + 1 = n - 3773 := by omega
          rw [h_sub_fib2, h_sub_fib3] at h_fib_add_two
          rw [h_fib_add_two]
          rw [A355898_3772_eq]
          have h_b0_le_b1 : B 0 ≤ B 1 := by
            unfold B
            unfold B0 B1
            decide
          rw [A3772_identity]
          have h_mul_le : B 0 * Nat.fib (n - 3774) ≤ B 1 * Nat.fib (n - 3774) := Nat.mul_le_mul_right (Nat.fib (n - 3774)) h_b0_le_b1
          rw [Nat.mul_add, Nat.sub_mul]
          omega
        rw [h_fib]
        have h_eq_3774 : A355898 3774 + 1 = B 1 := by
          have h_eq_loop_3774 : A355898 3774 = B 1 - 1 := A355898_eq_B 3774 (by omega)
          have h_pos_b1 : 1 ≤ B 1 := B_pos 1
          omega
        rw [h_eq_3774]
