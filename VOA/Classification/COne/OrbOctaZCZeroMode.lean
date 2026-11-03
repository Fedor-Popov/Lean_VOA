import VOA.Classification.COne.OrbOctaZCResult

/-! A zero-fiber consequence of the same intrinsic mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu OrbOctaZ Polynomial

/-- The positive polynomial isolates the zero conformal fiber. -/
def q24L : Module.End ℂ (A W) := aeval (omegaL W) positivePolynomial

theorem q24L_omega (a : A W) : q24L (omegaL W a) = 0 := by
  have h := congrArg (fun f : Module.End ℂ (A W) => f a) conformal_annihilator
  rw [candidatePolynomial, mul_comm X positivePolynomial] at h
  simpa only [map_mul, aeval_X, Module.End.mul_apply, LinearMap.zero_apply] using h

def constantRel (r : ModeRel) : ModeRel :=
  r.map fun p => (p.1, [p.2.headD 0])

theorem q24L_zp (p : PL) (a : A W) :
    q24L (aeval (omegaL W) (zp p) a) = (p.headD 0 : ℂ) • q24L a := by
  cases p with
  | nil => simp [zp]
  | cons c p =>
    simp only [zp, map_add, map_mul, aeval_C, aeval_X, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, q24L_omega,
      add_zero, List.headD_cons]

theorem constantRel_sound (r : ModeRel) :
    evalRel W (fun k => q24L (selfMode k)) (constantRel r) =
      q24L (evalRel W selfMode r) := by
  induction r with
  | nil => simp [constantRel, evalRel]
  | cons p r ih =>
    simp only [constantRel, List.map_cons, evalRel, map_add, q24L_zp] at ih ⊢
    rw [ih]
    simp [zp]

/-- Exact constant-term combination of the first circle and singular-mode rows. -/
def zeroModeWitness : ModeRel :=
  scaleRel [mkRat (-4596311479386627) 279539405] (constantRel circle1) ++
  scaleRel [mkRat (33716331649) 251585464500000] (constantRel sing6) ++
  scaleRel [mkRat (-95665822802277) 3578104384] (constantRel skew6) ++
  scaleRel [mkRat (-8681743498144814460202879) 77501029573038790656000000] (constantRel sing16) ++
  scaleRel [mkRat (46721281287069367132664438564714558785188979)
      54529488868643194165530585444767047680000000] (constantRel sing25) ++
  scaleRel [mkRat (-3437563947080323160387279040387582012222784063227037393267)
      2379851406741920411313369204390709784776618848829440000000] (constantRel sing34) ++
  scaleRel [mkRat (-2598587148598690678644150455431)
      131207099807990260454400] (constantRel skew30) ++
  scaleRel [mkRat (1094697662530282320828540397059046471869853503121279923523766599697873)
      23428605091230772515265389207922643685253709352549791409192960000000] (constantRel sing38) ++
  scaleRel [mkRat (-1094697662530282320828540397059046471869853503121279923523766599697873)
      607035208318787868762747656488773785086437997317120000000] (constantRel high38) ++
  scaleRel [mkRat (-954523265866951413120151044329002564572033576525542583767270415115948766497001)
      84669703773580597950576449093257853454360769343823650926080000000] (constantRel high37) ++
  scaleRel [mkRat (-311874089457134796749278132077563448177369297159968238352123337513467639540841)
      10592720386992636509561479163156514432162581356206022711603200000] (constantRel high36) ++
  scaleRel [mkRat
    (-15995028436351172694689212688847282496310056078724381705997804992687406157900541)
      388951451709885871835460563022153264305969784173189896441680000000] (constantRel high35) ++
  scaleRel [mkRat (-2203512391302534918735736646110542916243753674384765653128942355999052794839499)
      68013368605007365566856491894584177364978322915530473694720000000] (constantRel high34) ++
  scaleRel [mkRat
    (-169824962800883971395031054138030088167744850471107626051394994664839512112296637)
      12446446454716347898734738016708904457791033093542076686133760000000] (constantRel high33) ++
  scaleRel [mkRat (-403486669878017156873200118618526036998401771695978509846983496463286015099)
      168337399218479768706471520090737507459557505914347613675520000] (constantRel high32) ++
  scaleRel [mkRat (-41054526966313779171564405830052112527184887315326416086316079047657)
      2032072890565934350813834778238188482904658464251767622225920000000] (constantRel sing37) ++
  scaleRel [mkRat (11031501321059566827071) 86213694215206958400] (constantRel low4) ++
  scaleRel [mkRat (103565635293200183864701136916545914296094010953076930168066669)
      23940115226120348377606837511568345079960397309799751680000000] (constantRel sing35) ++
  scaleRel [mkRat (6846097565260763869880268874571966816940323239544407892351)
      7139554220225761233940107613172129354329856546488320000000] (constantRel sing33) ++
  scaleRel [mkRat (28115496394352013132599810935094014181851940419)
      4004785881198818404872991845140549954027520000000] (constantRel sing32) ++
  scaleRel [mkRat (109623827743016162254098675911) 614976756750988262400] (constantRel skew22) ++
  scaleRel [mkRat (35938099279405494764153924856899269001275087933973)
      1335544081173556602721183390849891064863580160000000] (constantRel sing30) ++
  scaleRel [mkRat (2554335936502153236404853364696454678790526621639)
      18545438566251862866234211315050404163072000000000] (constantRel sing29) ++
  scaleRel [mkRat (-1802811035058714544222416113939962238096159839471)
      23499483227941784525635405797422359197696000000000] (constantRel sing28) ++
  scaleRel [mkRat (1723542991934835794532725387689630201859826660349)
      5422957667986565659762016722482082891776000000000] (constantRel sing27) ++
  scaleRel [mkRat (1805694705467497080293671034184689682599827973)
      1541050772374698965547603501699938304000000000] (constantRel sing26) ++
  scaleRel [mkRat (-136785398420954064232117756031494973311)
      827418985436502096202873111265280000000] (constantRel sing23) ++
  scaleRel [mkRat (-440993512374082968314209494384567557)
      4594198360719659828674034165760000000] (constantRel sing22) ++
  scaleRel [mkRat (-20829750858878402667551088016367897)
      94617357543425488462394296320000000] (constantRel sing21) ++
  scaleRel [mkRat (-80400036003229048885403661050659)
      156664905736390786996557004800000] (constantRel sing20) ++
  scaleRel [mkRat (-84328183579827239866888696965263)
      111903504097421990711826432000000] (constantRel sing19) ++
  scaleRel [mkRat (-31564545886798493973869301889739)
      46242771818433774337087488000000] (constantRel sing18) ++
  scaleRel [mkRat (-8359394040133815035204155697611)
      22265038282949595051190272000000] (constantRel sing17) ++
  scaleRel [mkRat (758042455985101311364639) 19375257393259697664000000] (constantRel sing14) ++
  scaleRel [mkRat (35514806265203466983821) 509875194559465728000000] (constantRel sing13) ++
  scaleRel [mkRat (3160937942159906764427) 35435341706835456000000] (constantRel sing12) ++
  scaleRel [mkRat (27381868469662502608241) 330729855930464256000000] (constantRel sing11) ++
  scaleRel [mkRat (944832272006232467) 17069928048023961600] (constantRel sing10) ++
  scaleRel [mkRat (217126038696208010369) 8337727460431872000000] (constantRel sing9) ++
  scaleRel [mkRat (2531646749135252749) 308804720756736000000] (constantRel sing8) ++
  scaleRel [mkRat (239773119344225467) 154402360378368000000] (constantRel sing7)

set_option maxHeartbeats 1000000 in
-- The finite rational elimination uses only constant polynomial coefficients.
theorem zeroModeWitness_check :
    equalRelCheck zeroModeWitness [(15, [1])] = true := by
  decide +kernel

theorem q24_selfMode15 : q24L (selfMode 15) = 0 := by
  have h : evalRel W (fun k => q24L (selfMode k)) zeroModeWitness = 0 := by
    simp only [zeroModeWitness, evalRel_append, evalRel_scalar, constantRel_sound,
      circle1_holds, sing6_holds, skew6_holds, sing16_holds,
      sing25_holds, sing34_holds, skew30_holds, sing38_holds,
      high38_holds, high37_holds, high36_holds, high35_holds,
      high34_holds, high33_holds, high32_holds, sing37_holds,
      low4_holds, sing35_holds, sing33_holds, sing32_holds,
      skew22_holds, sing30_holds, sing29_holds, sing28_holds,
      sing27_holds, sing26_holds, sing23_holds, sing22_holds,
      sing21_holds, sing20_holds, sing19_holds, sing18_holds,
      sing17_holds, sing14_holds, sing13_holds, sing12_holds,
      sing11_holds, sing10_holds, sing9_holds, sing8_holds,
      sing7_holds, map_zero, smul_zero, add_zero]
  have he := equalRelCheck_sound W (fun k => q24L (selfMode k)) zeroModeWitness_check
  rw [he] at h
  simpa [evalRel, zp] using h

end VOA.Classification.COne.OrbOctaZC
