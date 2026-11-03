import VOA.Classification.COne.OrbOctaZCTop
import VOA.Classification.COne.OrbOctaZCandidate

/-! Exact elimination for two proposed circle-mode identities.

The external rational calculation keeps [X_(31) X] and [X_(15) X] as
independent vectors. It only uses the low-weight identity
[X_(27) X] = (96 omega^2 + 48 omega) [X_(31) X]. No weight-sixteen
primary projection, lattice expansion, or self-coupling normalization is needed.
The two circle identities themselves are NOT proved in this file.

The first identity uses sum binom(16,j) [X_(j-3) X]; the second uses
sum binom(16,j) [X_(j-7) X], after eliminating [X_(-5) X] using its circle
relation. Factoring the common cubic in the coefficients before choosing
the multipliers gives P25, without dividing any Zhu class or operator.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu OrbOctaZ Polynomial

def circle1Top : PL := [
  mkRat (0) 1,
  mkRat (13779889061802808391) 94336556110844359207896,
  mkRat (-104195017778753920438372781) 28142814371538068689579092000,
  mkRat (222974880834645552178293577) 7999085519543867933424240000,
  mkRat (-1490140401039813742977920446139) 13653611490255912507051720000000,
  mkRat (170366684997781473654556012015721) 798736272179970881662525620000000,
  mkRat (-160465832746095698205157670267153) 898578306202467241870341322500000,
  mkRat (-3043009801188450962292369924709) 7188626449619737934962730580000000,
  mkRat (317051322288365251826805265648499) 2875450579847895173985092232000000,
  mkRat (-374030172071786473565328807442531) 4073554988117851496478880662000000,
  mkRat (2923616046265470829232057354341) 59905220413497816124689421500000,
  mkRat (-52519667986241424868605659873) 2139472157624922004453193625000,
  mkRat (37186089349638547283139652043) 3744076275843613507793088843750,
  mkRat (-254584307464920072067988818) 110119890465988632582149671875,
  mkRat (1799198182369092264664471832) 9360190689609033769482722109375,
  mkRat (14596250495989639259186982944) 814336589995985937944996823515625,
  mkRat (-10708176283477616955823885312) 3606347755696509153756414504140625,
  mkRat (-9929377855324697378946818048) 429155382927884589297013325992734375]

def circle1Middle : PL := [
  mkRat (-279539405) 4596311479386627,
  mkRat (1738727595061) 1351315574939668338,
  mkRat (-6266405952417197) 1105621834041546822000,
  mkRat (456427833966410147) 41046210588792425766750,
  mkRat (-1307591268715983821) 109456561570113135378000,
  mkRat (12298231016238283) 1609655317207546108500,
  mkRat (-61285507713429317) 20523105294396212883375,
  mkRat (4783879786062596) 6841035098132070961125,
  mkRat (-12573519571328) 139612961186368795125,
  mkRat (100588156570624) 20523105294396212883375]

def circle5Top : PL := [
  mkRat (0) 1,
  mkRat (-6408294866575637077608293383) 31191427686439401738019987700376,
  mkRat (50771539950009793075261710824329) 9783370988420893432764448489236000,
  mkRat (-477741944239167502173798581306284669) 12327047445410325725283205096437360000,
  mkRat (640602150681570310885941699575563897949) 4267054884949728135674955610305240000000,
  mkRat (-4619912122212400486214032479701009975077) 16104691017390909415289348593732680000000,
  mkRat (2338378672511389618315899542880972088111) 10353015654037013195543152667399580000000,
  mkRat (66090760804238057560924935415617878779) 3150917807750395320382698637904220000000,
  mkRat (-1715331270544470234333253672360383530377) 11149401473578321902892625949507240000000,
  mkRat (5589544791142956412752441754650137161333) 48314073052172728245868045781198040000000,
  mkRat (-1601901831414048008070825913687637841539) 27539021639738455100144786095282882800000,
  mkRat (37099004102236631469939237612745571) 1271422975057177059101790678452580000,
  mkRat (-155056331529661327481280271318995289) 13725588935276343251667058460567625000,
  mkRat (342066377282984590398611496998333) 155330738979464789885121031961156250,
  mkRat (-268100537018098903508260661271398) 4966495996317097887116369837705390625,
  mkRat (-9444863438329102346304691810977496) 283090271790074579565633080749207265625,
  mkRat (6288782917226906061158618623167328) 8775798425492311966534625503225425234375,
  mkRat (2424175958446119347784568750949888) 8775798425492311966534625503225425234375,
  mkRat (21918932204633218878165269880832) 975088713943590218503847278136158359375,
  mkRat (944872542195036970364908180209664) 6169386293121095312473841728767473939765625]

def circle5Middle : PL := [
  mkRat (3963725405780705) 46337056906894727812839,
  mkRat (-24553160692931168671) 13623094730627049976974666,
  mkRat (73707453276401966167999) 9431373275049496137905538000,
  mkRat (-3808762453893419768891437) 254647078426336395723449526000,
  mkRat (10251015852601654173199159) 662082403908474628880968767600,
  mkRat (-1239674496312687983967791) 132416480781694925776193753520,
  mkRat (395689801485648400836227) 118229000697941898014458708500,
  mkRat (-7293060487468737830851) 10889513222178859027647512625,
  mkRat (12642100655227899466252) 206900751221398321525302739875,
  mkRat (-6481406505656193344) 12170632424788136560311925875,
  mkRat (-36518213820511232) 18809159201945301956845703625,
  mkRat (-6712727617771323392) 206900751221398321525302739875]

def multiplier1 : PL := [
  mkRat (-253678425969965120) 417033512162052550315551,
  mkRat (340296520453676997136) 183911778863465174689157991,
  mkRat (-3439496459516159857168) 1555644746025551289663930375,
  mkRat (18224851377562687763216) 13793383414759888101686849325,
  mkRat (-84237657888107452163824) 206900751221398321525302739875,
  mkRat (627114464798188096) 11168731509927034900151295,
  mkRat (-5302520012187176192) 4597794471586629367228949775,
  mkRat (-6289613116843598848) 41380150244279664305060547975,
  mkRat (-6712727617771323392) 206900751221398321525302739875]

def multiplier5 : PL := [
  mkRat (17890521920) 41366803314479643,
  mkRat (-24683727231376) 18242760261685522563,
  mkRat (34629096639085504) 20523105294396212883375,
  mkRat (-4430638604032304) 4104621058879242576675,
  mkRat (197432168781248) 526233469087082381625,
  mkRat (-25147039142656) 373147368989022052425,
  mkRat (100588156570624) 20523105294396212883375]

def eliminationScale : ℚ :=
  mkRat (4835703278458516698824704) 297917697438309625068591060768684404896878984375

/-- P25 as a computable product of rational linear factors. -/
def p25List : PL :=
  pmulL [mkRat (0) 1, 1] (
    pmulL [mkRat (-4) 1, 1] (
    pmulL [mkRat (-9) 4, 1] (
    pmulL [mkRat (-1) 36, 1] (
    pmulL [mkRat (-25) 36, 1] (
    pmulL [mkRat (-49) 36, 1] (
    pmulL [mkRat (-1) 9, 1] (
    pmulL [mkRat (-4) 9, 1] (
    pmulL [mkRat (-16) 9, 1] (
    pmulL [mkRat (-1) 1, 1] (
    pmulL [mkRat (-1) 4, 1] (
    pmulL [mkRat (-1) 16, 1] (
    pmulL [mkRat (-9) 16, 1] (
    pmulL [mkRat (-9) 1, 1] (
    pmulL [mkRat (-25) 4, 1] (
    pmulL [mkRat (-25) 16, 1] (
    pmulL [mkRat (-49) 16, 1] (
    pmulL [mkRat (-1) 64, 1] (
    pmulL [mkRat (-9) 64, 1] (
    pmulL [mkRat (-25) 64, 1] (
    pmulL [mkRat (-49) 64, 1] (
    pmulL [mkRat (-81) 64, 1] (
    pmulL [mkRat (-121) 64, 1] (
    pmulL [mkRat (-169) 64, 1] (
    pmulL [mkRat (-225) 64, 1] (
    [1])))))))))))))))))))))))))

set_option maxHeartbeats 2000000 in
-- Exact convolution of the two degree-at-most-nineteen coefficient lists.
theorem elimination_check :
    ptrim (paddL (pmulL multiplier1 circle1Top)
      (pscaleL (-1) (pmulL multiplier5 circle5Top))) =
    ptrim (pscaleL eliminationScale p25List) := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Exact cancellation of the coefficient of the weight-sixteen seed.
theorem primary_cancellation_check :
    ptrim (paddL (pmulL multiplier1 circle1Middle)
      (pscaleL (-1) (pmulL multiplier5 circle5Middle))) = [] := by decide +kernel

private theorem zp_linear (q : ℚ) : zp [-q, 1] = X - Polynomial.C (q : ℂ) := by
  simp [zp, sub_eq_add_neg, add_comm]

private theorem factor_eq (q r : ℚ) (h : q = -r) :
    zp [q, 1] = X - Polynomial.C (r : ℂ) := by rw [h, zp_linear]

theorem p25List_spec : zp p25List = candidatePolynomial := by
  simp only [p25List, zp_pmulL, candidatePolynomial, positivePolynomial,
    Fin.prod_univ_succ]
  repeat' apply congrArg₂ (fun a b : ℂ[X] => a * b)
  all_goals first
    | (apply factor_eq; decide +kernel)
    | norm_num [zp, mkRat]

theorem elimination_identity :
    zp multiplier1 * zp circle1Top - zp multiplier5 * zp circle5Top =
      Polynomial.C (eliminationScale : ℂ) * candidatePolynomial := by
  have h := congrArg zp elimination_check
  simpa only [zp_ptrim, zp_paddL, zp_pmulL, zp_pscaleL, Rat.cast_neg, Rat.cast_one,
    map_neg, map_one, neg_one_mul, ← sub_eq_add_neg, p25List_spec] using h

theorem primary_cancellation :
    zp multiplier1 * zp circle1Middle - zp multiplier5 * zp circle5Middle = 0 := by
  have h := congrArg zp primary_cancellation_check
  simpa only [zp_ptrim, zp_paddL, zp_pmulL, zp_pscaleL, Rat.cast_neg, Rat.cast_one,
    map_neg, map_one, neg_one_mul, ← sub_eq_add_neg, zp] using h

theorem eliminationScale_ne_zero : (eliminationScale : ℂ) ≠ 0 := by
  norm_num [eliminationScale, mkRat]

/-- Two explicit circle identities force P25 on the top self-product mode.
The hypotheses remain state-to-Zhu certificate obligations. -/
theorem p25_of_two_circle_relations (top middle : A W)
    (h1 : aeval (omegaL W) (zp circle1Top) top +
      aeval (omegaL W) (zp circle1Middle) middle = 0)
    (h5 : aeval (omegaL W) (zp circle5Top) top +
      aeval (omegaL W) (zp circle5Middle) middle = 0) :
    aeval (omegaL W) candidatePolynomial top = 0 := by
  have h : aeval (omegaL W)
      (zp multiplier1 * zp circle1Top - zp multiplier5 * zp circle5Top)
        top +
      aeval (omegaL W)
      (zp multiplier1 * zp circle1Middle - zp multiplier5 * zp circle5Middle)
        middle = 0 := by
    have h1' := congrArg (aeval (omegaL W) (zp multiplier1)) h1
    have h5' := congrArg (aeval (omegaL W) (zp multiplier5)) h5
    simp only [map_add, map_zero] at h1' h5'
    simp only [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply]
    rw [show ∀ a b c d : A W, a - b + (c - d) = (a + c) - (b + d) from
      fun _ _ _ _ => by abel, h1', h5', sub_self]
  rw [elimination_identity, primary_cancellation, map_zero, LinearMap.zero_apply,
    add_zero] at h
  simp only [map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply] at h
  exact (smul_eq_zero.mp h).resolve_left eliminationScale_ne_zero

/-- Final transfer from the top self-product to the vacuum. The two
hypotheses specify the remaining certificate inputs; neither is assumed globally. -/
theorem conformalRelation_of_mode_inputs
    (h1 : aeval (omegaL W) (zp circle1Top) (selfMode 31) +
      aeval (omegaL W) (zp circle1Middle) (selfMode 15) = 0)
    (h5 : aeval (omegaL W) (zp circle5Top) (selfMode 31) +
      aeval (omegaL W) (zp circle5Middle) (selfMode 15) = 0) :
    OctahedralConformalZhuRelation := by
  have h := p25_of_two_circle_relations (selfMode 31) (selfMode 15) h1 h5
  obtain ⟨c, hc, ht⟩ := self_top_nonzero
  rw [ht, map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hc

end VOA.Classification.COne.OrbOctaZC
