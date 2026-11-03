import VOA.Classification.COne.OrbC2hSeed16

/-!
# OrbSgl (6): the weight-16 primary `v' = v_num − x₀` of `V₈⁺`

`v_num = J₍₋₉₎J + 27E₍₋₉₎E` (`weightSixteen`), `x₀ = Σ c_w L(-w)𝟙` (`x0Words`, 55 words; computed
externally and checked here by `cert_x0`).

* `primeData`: `v'` as a sector vector (charge `±2`: `27 e^{±2β}`; charge `0`: `primeFock`), with
  `evaluate primeData = v_num − x₀` (`cert_x0`, kernel).
* `wsP_primary`: `L(n) v' = 0` for `n ≥ 1` (`L(1)`, `L(2)` certificates).
* `wsP_fixed`: `v'` is fixed by the cubic automorphism (`v_num` is, and `x₀ ∈ Vir·𝟙`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational
  OrbC2g OrbC2h OrbC2c OrbC2e OrbC2f PlusC2 PlusC2Eval PlusUnitary

local notation "V8" => V2m 4 four_ge_one
local notation "P8" => V2mPlus 4 four_ge_one

def primeFock_0 : RawPoly ℕ := [(36/175, [0, 2, 4, 6]), (-1/5, [0, 2, 5, 5]), (-27/140, [0, 3, 3, 6]), (9/25, [0, 3, 4, 5]), (-108/625, [0, 4, 4, 4]), (-27/175, [1, 1, 4, 6]), (3/20, [1, 1, 5, 5]), (9/35, [1, 2, 3, 6]), (-6/25, [1, 2, 4, 5]), (-9/40, [1, 3, 3, 5]), (27/125, [1, 3, 4, 4]), (-4/35, [2, 2, 2, 6]), (1/5, [2, 2, 3, 5]), (12/125, [2, 2, 4, 4]), (-27/100, [2, 3, 3, 4]), (27/320, [3, 3, 3, 3]), (-18/175, [0, 0, 0, 0, 4, 6]), (1/10, [0, 0, 0, 0, 5, 5]), (9/35, [0, 0, 0, 1, 3, 6]), (-6/25, [0, 0, 0, 1, 4, 5])]

def primeFock_1 : RawPoly ℕ := [(-1/5, [0, 0, 0, 2, 3, 5]), (24/125, [0, 0, 0, 2, 4, 4]), (-9/35, [0, 0, 1, 1, 2, 6]), (27/125, [0, 0, 1, 1, 4, 4]), (2/5, [0, 0, 1, 2, 2, 5]), (-9/25, [0, 0, 1, 2, 3, 4]), (-4/25, [0, 0, 2, 2, 2, 4]), (3/20, [0, 0, 2, 2, 3, 3]), (27/280, [0, 1, 1, 1, 1, 6]), (-1/10, [0, 1, 1, 1, 2, 5]), (-9/50, [0, 1, 1, 1, 3, 4]), (3/25, [0, 1, 1, 2, 2, 4]), (9/40, [0, 1, 1, 2, 3, 3]), (-1/5, [0, 1, 2, 2, 2, 3]), (2/45, [0, 2, 2, 2, 2, 2]), (-3/80, [1, 1, 1, 1, 1, 5]), (3/40, [1, 1, 1, 1, 2, 4]), (9/320, [1, 1, 1, 1, 3, 3]), (-1/10, [1, 1, 1, 2, 2, 3]), (1/30, [1, 1, 2, 2, 2, 2])]

def primeFock_2 : RawPoly ℕ := [(6/175, [0, 0, 0, 0, 0, 0, 2, 6]), (-1/25, [0, 0, 0, 0, 0, 0, 3, 5]), (6/625, [0, 0, 0, 0, 0, 0, 4, 4]), (-9/350, [0, 0, 0, 0, 0, 1, 1, 6]), (-1/25, [0, 0, 0, 0, 0, 1, 2, 5]), (9/125, [0, 0, 0, 0, 0, 1, 3, 4]), (-6/125, [0, 0, 0, 0, 0, 2, 2, 4]), (3/100, [0, 0, 0, 0, 0, 2, 3, 3]), (1/20, [0, 0, 0, 0, 1, 1, 1, 5]), (3/50, [0, 0, 0, 0, 1, 1, 2, 4]), (-9/80, [0, 0, 0, 0, 1, 1, 3, 3]), (1/45, [0, 0, 0, 0, 2, 2, 2, 2]), (-3/50, [0, 0, 0, 1, 1, 1, 1, 4]), (1/10, [0, 0, 0, 1, 1, 1, 2, 3]), (-1/15, [0, 0, 0, 1, 1, 2, 2, 2]), (1/40, [0, 0, 1, 1, 1, 1, 2, 2]), (-1/80, [0, 1, 1, 1, 1, 1, 1, 2]), (3/1280, [1, 1, 1, 1, 1, 1, 1, 1]), (-1/350, [0, 0, 0, 0, 0, 0, 0, 0, 0, 6]), (1/100, [0, 0, 0, 0, 0, 0, 0, 0, 1, 5])]

def primeFock_3 : RawPoly ℕ := [(-3/1750, [0, 0, 0, 0, 0, 0, 0, 0, 2, 4]), (3/560, [0, 0, 0, 0, 0, 0, 0, 0, 3, 3]), (-12/875, [0, 0, 0, 0, 0, 0, 0, 1, 1, 4]), (-3/175, [0, 0, 0, 0, 0, 0, 0, 1, 2, 3]), (-2/1575, [0, 0, 0, 0, 0, 0, 0, 2, 2, 2]), (1/50, [0, 0, 0, 0, 0, 0, 1, 1, 1, 3]), (1/50, [0, 0, 0, 0, 0, 0, 1, 1, 2, 2]), (-1/40, [0, 0, 0, 0, 0, 1, 1, 1, 1, 2]), (1/160, [0, 0, 0, 0, 1, 1, 1, 1, 1, 1]), (2/4375, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]), (-1/875, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3]), (1/2250, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2]), (1/2100, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]), (-1/5600, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]), (-1/15750, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (1/21000, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (1/630000, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]

/-- The charge-`0` part of `v_num − x₀` (oscillator words, `i ↔ h(-i-1)`). -/
def primeFock : RawPoly ℕ := [primeFock_0, primeFock_1, primeFock_2, primeFock_3].flatten

def x0Words_0 : List (ℚ × List ℕ) := [(-123552503164/39414375, [15]), (-1296132029/404250, [13, 1]), (-698019781/1501500, [12, 2]), (-7256226577/31531500, [11, 3]), (-53607442351/118243125, [11, 1, 1]), (11163409883/945945000, [10, 4]), (-119542065719/236486250, [10, 2, 1]), (2597271889/78828750, [9, 5]), (-1062454408/1876875, [9, 3, 1]), (7692491363/157657500, [9, 2, 2]), (426900704/118243125, [9, 1, 1, 1])]

def x0Words_1 : List (ℚ × List ℕ) := [(166238473/1010625, [8, 6]), (-15826771111/157657500, [8, 4, 1]), (-6005029967/315315000, [8, 3, 2]), (-767461694/5630625, [8, 2, 1, 1]), (9972897941/145530000, [7, 7]), (590299877/3753750, [7, 5, 1]), (-51071851/2047500, [7, 4, 2]), (6704169113/315315000, [7, 3, 3]), (-2575865018/39414375, [7, 3, 1, 1]), (-31010036821/472972500, [7, 2, 2, 1]), (-441268342/39414375, [7, 1, 1, 1, 1])]

def x0Words_2 : List (ℚ × List ℕ) := [(3364195489/31531500, [6, 6, 1]), (1232015177/52552500, [6, 5, 2]), (713753493/35035000, [6, 4, 3]), (-104346482/9095625, [6, 4, 1, 1]), (-420800069/39414375, [6, 3, 2, 1]), (-1988964277/157657500, [6, 2, 2, 2]), (-3788209384/118243125, [6, 2, 1, 1, 1]), (65404301/3031875, [5, 5, 3]), (323336339/16891875, [5, 5, 1, 1]), (1988523991/157657500, [5, 4, 4]), (135629839/9459450, [5, 4, 2, 1])]

def x0Words_3 : List (ℚ × List ℕ) := [(2506833853/78828750, [5, 3, 3, 1]), (-18094033/1576575, [5, 3, 2, 2]), (-144520744/13138125, [5, 3, 1, 1, 1]), (-2933705321/118243125, [5, 2, 2, 1, 1]), (-32753528/16891875, [5, 1, 1, 1, 1, 1]), (4142094464/118243125, [4, 4, 3, 1]), (-2569197557/630630000, [4, 4, 2, 2]), (-82148372/23648625, [4, 4, 1, 1, 1]), (1268795887/315315000, [4, 3, 3, 2]), (142803662/23648625, [4, 3, 2, 1, 1]), (927908353/472972500, [4, 2, 2, 2, 1])]

def x0Words_4 : List (ℚ × List ℕ) := [(-14861162/16891875, [4, 2, 1, 1, 1, 1]), (171/560, [3, 3, 3, 3]), (143104622/39414375, [3, 3, 3, 1, 1]), (105995401/14332500, [3, 3, 2, 2, 1]), (19562/2413125, [3, 3, 1, 1, 1, 1]), (25038539/22522500, [3, 2, 2, 2, 2]), (65494724/16891875, [3, 2, 2, 1, 1, 1]), (1571552/16891875, [3, 1, 1, 1, 1, 1, 1]), (36324661/13513500, [2, 2, 2, 2, 1, 1]), (15555772/16891875, [2, 2, 1, 1, 1, 1, 1]), (1262672/118243125, [1, 1, 1, 1, 1, 1, 1, 1])]

/-- `x₀ = Σ c_w L(-w)𝟙`: the vacuum-module part of `v_num` (letter `k ↔ L(-k-1)`). -/
def x0Words : List (ℚ × List ℕ) := [x0Words_0, x0Words_1, x0Words_2, x0Words_3, x0Words_4].flatten

def primeData : SectorVector := [(-2, [(27, [])]), (0, liftR primeFock), (2, [(27, [])])]

set_option maxHeartbeats 4000000 in
theorem cert_x0 :
    VectorCertificate (sixteenData ++ scaleVector (-1) (wordSumS x0Words vacuumData)) primeData := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem cert_L1 : VectorCertificate (neutralBoundS omR 2 primeData) [] := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem cert_L2 : VectorCertificate (neutralBoundS omR 3 primeData) [] := by decide +kernel

/-- `x₀ ∈ V₈⁺`. -/
def x0P : VP 4 four_ge_one := wordSum P8 (P8).vacuum x0Words

/-- The weight-sixteen primary `v' = v_num − x₀`. -/
def wsP : VP 4 four_ge_one := weightSixteen - x0P

theorem wsP_coe : (wsP : LatModuleGen (latP 4)) = evaluate primeData := by
  have h := vector_eq_of_certificate _ _ cert_x0
  rw [evaluate_append, evaluate_scaleVector, sixteen_value, evaluate_wordSumS,
    vacuumData_value] at h
  rw [← h, wsP, x0P, Submodule.coe_sub, coe_wordSum]
  push_cast
  rw [neg_one_smul, sub_eq_add_neg]
  rfl

theorem coe_L (n : ℤ) (x : VP 4 four_ge_one) :
    (((P8).L n x : VP 4 four_ge_one) : LatModuleGen (latP 4)) = (V8).L n x := by
  rw [VertexOperatorAlgebra.L_def, VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def,
    ← PreVertexAlgebra.smul_def, V2mPlus_smul_coe, omega_coe, omega_V2m]

theorem L_eq_smul (n : ℤ) (y : LatModuleGen (latP 4)) :
    (V8).L n y = (V8).smul (ls 4 omR) (n + 1) y := by
  rw [← omega_V2m 4 four_ge_one, VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]

theorem wsP_L1 : (P8).L 1 wsP = 0 := by
  apply Subtype.ext
  rw [coe_L, wsP_coe, L_eq_smul, show (1 : ℤ) + 1 = 2 by norm_num, ← evaluate_neutralBoundS,
    vector_eq_of_certificate _ _ cert_L1]
  rfl

theorem wsP_L2 : (P8).L 2 wsP = 0 := by
  apply Subtype.ext
  rw [coe_L, wsP_coe, L_eq_smul, show (2 : ℤ) + 1 = 3 by norm_num, ← evaluate_neutralBoundS,
    vector_eq_of_certificate _ _ cert_L2]
  rfl

/-! ## Grading and cubic fixedness -/

theorem virWord_mem {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    {x : V} {d : ℤ} (hx : x ∈ W.grading d) :
    ∀ ks : List ℕ, virWord W ks x ∈ W.grading (d + (wWt ks : ℤ))
  | [] => by simpa using hx
  | k :: ks => by
    have h := virWord_mem W hx ks
    have h2 := W.grading_mode W.conformalVector W.conformal_mem _ h (-(k : ℤ) - 1 + 1)
    rw [virWord, VertexOperatorAlgebra.L_def]
    convert h2 using 2
    simp only [wWt]; push_cast; ring

set_option maxHeartbeats 4000000 in
theorem x0Words_wt : ∀ t ∈ x0Words, wWt t.2 = 16 := by decide +kernel

theorem wordSum_mem {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    (ts : List (ℚ × List ℕ)) (hts : ∀ t ∈ ts, wWt t.2 = 16) :
    wordSum W W.vacuum ts ∈ W.grading 16 := by
  induction ts with
  | nil => exact Submodule.zero_mem _
  | cons t ts ih =>
    rw [wordSum, List.map_cons, List.sum_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (ih fun s hs => hts s (by simp [hs]))
    have := virWord_mem W W.vacuum_mem t.2
    rwa [hts t (by simp), show (0 : ℤ) + ((16 : ℕ) : ℤ) = 16 by norm_num] at this

theorem wsP_mem : wsP ∈ (P8).grading 16 :=
  Submodule.sub_mem _ weightSixteen_mem_grading (wordSum_mem _ _ x0Words_wt)

theorem aut_L {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
    (g : Aut W) (n : ℤ) (v : V) : g (W.L n v) = W.L n (g v) := by
  change g (W.smul W.conformalVector (n + 1) v) = W.smul W.conformalVector (n + 1) (g v)
  rw [g.map_smul', g.map_omega]

theorem aut_virWord {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
    (g : Aut W) (x : V) : ∀ ks : List ℕ, g (virWord W ks x) = virWord W ks (g x)
  | [] => rfl
  | k :: ks => by
    rw [virWord, virWord, ← aut_virWord g x ks, aut_L]

theorem aut_wordSum {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
    (g : Aut W) (ts : List (ℚ × List ℕ)) : g (wordSum W W.vacuum ts) = wordSum W W.vacuum ts := by
  induction ts with
  | nil => exact g.toLinearEquiv.map_zero
  | cons t ts ih =>
    rw [wordSum, List.map_cons, List.sum_cons]
    change g.toLinearEquiv (_ + _) = _
    rw [map_add, map_smul]
    change (t.1 : ℂ) • g (virWord W t.2 W.vacuum) + g (wordSum W W.vacuum ts) = _
    rw [aut_virWord, g.map_vacuum, ih]
    rfl

theorem wsP_fixed : plusCubic wsP = wsP := by
  change plusCubic.toLinearEquiv (weightSixteen - x0P) = _
  rw [map_sub]
  change plusCubic weightSixteen - plusCubic x0P = _
  rw [weightSixteen_fixed, x0P, aut_wordSum]
  rfl

end VOA.Classification.COne.OrbSgl
