import VOA.Classification.COne.PlusRat3Charged

/-! # Certified Dong--Jiang generator calculations

The neutral generator is exactly J = h(-1)^4 - 2 h(-3)h(-1)
+ (3/2) h(-2)^2, with (h,h)=1. These are equalities of actual
lattice-plus VOA states, not numerical evidence or quotient assumptions.
Reference: Dong--Jiang, arXiv:1209.1168v2, Lemma 3.4.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2c
open VOA VOA.LatGen VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusRat3

def JR : RawPoly ℕ := [(1, [0,0,0,0]), (-2, [2,0]), (3/2, [1,1])]

def J (m : ℕ) (hm : 1 ≤ m) : VP m hm := nP m hm JR

theorem hasN_J (m : ℕ) (hm : 1 ≤ m) : HasN m hm (J m hm) JR :=
  hasN_nP m hm JR (by decide)

/-- A small expression language whose evaluation certificate preserves every mode. -/
inductive NeutralExpr where
  | vac | omega | j
  | add : NeutralExpr → NeutralExpr → NeutralExpr
  | scale : ℚ → NeutralExpr → NeutralExpr
  | prod : ℤ → NeutralExpr → NeutralExpr → NeutralExpr

namespace NeutralExpr

def poly : NeutralExpr → RawPoly ℕ
  | .vac => vacR
  | .omega => omR
  | .j => JR
  | .add a b => a.poly ++ b.poly
  | .scale c a => scaleR c a.poly
  | .prod n a b => normR (polyActW a.poly (-n-1) b.poly)

def state (m : ℕ) (hm : 1 ≤ m) : NeutralExpr → VP m hm
  | .vac => (V2mPlus m hm).vacuum
  | .omega => (V2mPlus m hm).conformalVector
  | .j => J m hm
  | .add a b => a.state m hm + b.state m hm
  | .scale c a => (c : ℂ) • a.state m hm
  | .prod n a b => (V2mPlus m hm).smul (a.state m hm) n (b.state m hm)

theorem hasN_state (m : ℕ) (hm : 1 ≤ m) :
    ∀ a : NeutralExpr, HasN m hm (a.state m hm) a.poly
  | .vac => hasPoly_vacuum m hm
  | .omega => hasN_omega m hm
  | .j => hasN_J m hm
  | .add a b => hasN_add m hm (hasN_state m hm a) (hasN_state m hm b)
  | .scale c a => hasN_smul m hm (hasN_state m hm a) c
  | .prod n a b => by
    have h := hasN_smul_left m hm (hasN_state m hm a) (hasN_state m hm b) n
    change HasN m hm _ (normR _)
    simpa only [HasN, ls_normR] using h

theorem state_eq_of_cert (m : ℕ) (hm : 1 ≤ m) (a b : NeutralExpr)
    (h : normR a.poly = normR b.poly) : a.state m hm = b.state m hm :=
  eq_of_hasN m hm (hasN_state m hm a) (hasN_state m hm b) h

/-- L(n) as a conformal-vector mode. -/
def vir (n : ℤ) (a : NeutralExpr) : NeutralExpr := .prod (n+1) .omega a

def u0 : NeutralExpr := .add (.scale (-8/3) (vir (-4) .vac))
  (.scale (112/9) (vir (-2) (vir (-2) .vac)))
def u1 : NeutralExpr := .add (.scale (-16/9) (vir (-5) .vac))
  (.scale (112/9) (vir (-3) (vir (-2) .vac)))
def u2 : NeutralExpr := .add (.add (.add
  (.scale (-1856/135) (vir (-6) .vac))
  (.scale (-2384/135) (vir (-4) (vir (-2) .vac))))
  (.scale (1316/135) (vir (-3) (vir (-3) .vac))))
  (.scale (1088/135) (vir (-2) (vir (-2) (vir (-2) .vac))))
def u3 : NeutralExpr := .add (.add (.add
  (.scale (-464/45) (vir (-7) .vac))
  (.scale (-928/45) (vir (-5) (vir (-2) .vac))))
  (.scale (40/9) (vir (-4) (vir (-3) .vac))))
  (.scale (544/45) (vir (-3) (vir (-2) (vir (-2) .vac))))
def v2 : NeutralExpr := .add (.scale (28/75) (vir (-2) .j))
  (.scale (23/300) (vir (-1) (vir (-1) .j)))
def v3 : NeutralExpr := .add (.add (.scale (14/75) (vir (-3) .j))
  (.scale (14/75) (vir (-2) (vir (-1) .j))))
  (.scale (-1/300) (vir (-1) (vir (-1) (vir (-1) .j))))

def jj : Fin 4 → NeutralExpr
  | ⟨0, _⟩ => .add (.scale 27 u3) (.scale (-60) v3)
  | ⟨1, _⟩ => .add (.scale 27 u2) (.scale (-60) v2)
  | ⟨2, _⟩ => .add (.scale 27 u1) (.scale (-30) (vir (-1) .j))
  | ⟨3, _⟩ => .add (.scale 27 u0) (.scale (-60) .j)

set_option maxHeartbeats 1600000 in
-- The four exact normal-ordering certificates require additional reduction time.
theorem jj_cert (n : Fin 4) :
    normR (NeutralExpr.prod (n : ℤ) .j .j).poly = normR (jj n).poly := by
  fin_cases n <;> decide +kernel

end NeutralExpr

/-- The four neutral OPE identities of Dong--Jiang Lemma 3.4, for every rank-one lattice. -/
theorem J_modes_J (m : ℕ) (hm : 1 ≤ m) (n : Fin 4) :
    (V2mPlus m hm).smul (J m hm) (n : ℤ) (J m hm) =
      (NeutralExpr.jj n).state m hm :=
  NeutralExpr.state_eq_of_cert m hm _ _ (NeutralExpr.jj_cert n)

/-- Normalization of the J-J vacuum coefficient. -/
theorem J_seven_J (m : ℕ) (hm : 1 ≤ m) :
    (V2mPlus m hm).smul (J m hm) 7 (J m hm) =
      (54 : ℂ) • (V2mPlus m hm).vacuum := by
  exact NeutralExpr.state_eq_of_cert m hm (.prod 7 .j .j) (.scale 54 .vac)
    (by decide +kernel)

/-- The neutral generator has the primary-vector low-mode identities. -/
theorem J_primary_low_modes (m : ℕ) (hm : 1 ≤ m) :
    (V2mPlus m hm).L 0 (J m hm) = (4 : ℂ) • J m hm ∧
    ∀ n : Fin 4, (V2mPlus m hm).L (n.val + 1) (J m hm) = 0 := by
  constructor
  · exact NeutralExpr.state_eq_of_cert m hm (.vir 0 .j) (.scale 4 .j)
      (by decide +kernel)
  · intro n
    have h := NeutralExpr.state_eq_of_cert m hm (.vir (n.val + 1) .j) (.scale 0 .vac)
      (by fin_cases n <;> decide +kernel)
    simpa only [NeutralExpr.state, NeutralExpr.vir, Rat.cast_zero, zero_smul] using h

/-- Symbolic charged computation, retaining the charge parameter before specializing m. -/
theorem J_three_E (m : ℕ) (hm : 1 ≤ m) :
    (V2mPlus m hm).smul (J m hm) 3 (EP m hm) =
      ((2 * (m : ℂ)) ^ 2 - (m : ℂ)) • EP m hm := by
  have hy := hasC_y0 m hm
  have h := eq_of_hasC m hm (hasC_smul_left m hm (hasN_J m hm) hy 3)
    (hasC_add m hm (hasC_cc2 m hm (hasC_cc2 m hm hy))
      (hasC_smul m hm (hasC_cc2 m hm hy) (-1/2))) (by decide +kernel)
  have hc := cα_sq m hm
  have hs : cα m * cα m * cα m * cα m = (2 * (m : ℂ)) ^ 2 := by
    rw [mul_assoc (cα m * cα m), hc]; ring
  have h' : (V2mPlus m hm).smul (J m hm) 3 (y0 m hm) =
      ((2 * (m : ℂ)) ^ 2 - (m : ℂ)) • y0 m hm := by
    push_cast at h
    simp only [smul_smul] at h
    linear_combination (norm := module) h + hs • y0 m hm - (1/2 * hc) • y0 m hm
  rw [EP_eq_y0, PreVertexAlgebra.smul_smul_right, h', smul_comm]

/-- The charged coefficient used in Dong--Jiang's norm-eight calculation. -/
theorem J_three_E_four : (V2mPlus 4 (by norm_num)).smul (J 4 (by norm_num)) 3
    (EP 4 (by norm_num)) = (60 : ℂ) • EP 4 (by norm_num) := by
  convert J_three_E 4 (by norm_num) using 1
  norm_num

end VOA.Classification.COne.OrbC2c
