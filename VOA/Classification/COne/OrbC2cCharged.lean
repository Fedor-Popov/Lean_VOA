import VOA.Classification.COne.OrbC2cGenerator

/-! # Charged J-mode certificates at norm eight

All four identities are in the actual `V2mPlus 4`. The symbolic computation
is reduced using the proved charge relation c² = 8. No numerical evaluation
is used in any proof. Reference: Dong--Jiang 1209.1168v2, Lemma 3.4.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2c
open VOA VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusRat3

/-- Certificate modulo the norm-eight charge relation. -/
theorem charged_eq_of_cert {y z : VP 4 (by norm_num)} {P Q : RawPoly ℕ}
    (hy : HasC 4 (by norm_num) y P) (hz : HasC 4 (by norm_num) z Q)
    (R : RawPoly ℕ)
    (h : normR (P ++ scaleR (-1) Q) = normR (cc2 R ++ scaleR (-8) R)) : y = z := by
  have hR := hasC_stP 4 (by norm_num) R
  have he := eq_of_hasC 4 (by norm_num)
    (hasC_add _ _ hy (hasC_smul _ _ hz (-1)))
    (hasC_add _ _ (hasC_cc2 _ _ hR) (hasC_smul _ _ hR (-8))) h
  have hc : cα 4 * cα 4 = (8 : ℂ) := by
    convert cα_sq 4 (by norm_num) using 1
    norm_num
  push_cast at he
  simp only [smul_smul, hc] at he
  linear_combination (norm := module) he

inductive ChargedExpr where
  | seed
  | add : ChargedExpr → ChargedExpr → ChargedExpr
  | scale : ℚ → ChargedExpr → ChargedExpr
  | vir : ℤ → ChargedExpr → ChargedExpr

namespace ChargedExpr

def poly : ChargedExpr → RawPoly ℕ
  | .seed => P0
  | .add a b => a.poly ++ b.poly
  | .scale c a => scaleR c a.poly
  | .vir n a => normR (polyActWC omR (-n-2) a.poly)

def state (m : ℕ) (hm : 1 ≤ m) : ChargedExpr → VP m hm
  | .seed => y0 m hm
  | .add a b => a.state m hm + b.state m hm
  | .scale c a => (c : ℂ) • a.state m hm
  | .vir n a => (V2mPlus m hm).L n (a.state m hm)

theorem hasC_state (m : ℕ) (hm : 1 ≤ m) :
    ∀ a : ChargedExpr, HasC m hm (a.state m hm) a.poly
  | .seed => hasC_y0 m hm
  | .add a b => hasC_add m hm (hasC_state m hm a) (hasC_state m hm b)
  | .scale c a => hasC_smul m hm (hasC_state m hm a) c
  | .vir n a => by
    have h := hasC_normR m hm (hasC_om m hm (n+1) (hasC_state m hm a))
    change HasC m hm ((V2mPlus m hm).smul (V2mPlus m hm).conformalVector (n+1) _) _
    simpa only [show -(n+1)-1 = -n-2 by omega] using h

/-- The same expression on an arbitrary charged seed; useful to state the result on E. -/
def apply (m : ℕ) (hm : 1 ≤ m) (x : VP m hm) : ChargedExpr → VP m hm
  | .seed => x
  | .add a b => a.apply m hm x + b.apply m hm x
  | .scale c a => (c : ℂ) • a.apply m hm x
  | .vir n a => (V2mPlus m hm).L n (a.apply m hm x)

theorem apply_two (m : ℕ) (hm : 1 ≤ m) :
    ∀ a : ChargedExpr, a.apply m hm (EP m hm) = (2 : ℂ) • a.state m hm
  | .seed => EP_eq_y0 m hm
  | .add a b => by simp only [apply, state, apply_two m hm a, apply_two m hm b, smul_add]
  | .scale c a => by simp only [apply, state, apply_two m hm a]; exact smul_comm _ _ _
  | .vir n a => by simp only [apply, state, apply_two m hm a, map_smul]

def jE : Fin 4 → ChargedExpr
  | ⟨0, _⟩ => .add (.add (.scale (56/5) (.vir (-3) .seed))
      (.scale (56/5) (.vir (-2) (.vir (-1) .seed))))
      (.scale (-1/5) (.vir (-1) (.vir (-1) (.vir (-1) .seed))))
  | ⟨1, _⟩ => .add (.scale (112/5) (.vir (-2) .seed))
      (.scale (23/5) (.vir (-1) (.vir (-1) .seed)))
  | ⟨2, _⟩ => .scale 30 (.vir (-1) .seed)
  | ⟨3, _⟩ => .scale 60 .seed

def correction : Fin 4 → RawPoly ℕ
  | ⟨0, _⟩ => [(1/5, [0,1,1,1]), (4, [0,3]), (7/5, [1,2])]
  | ⟨1, _⟩ => [(4, [0,2]), (7/5, [1,1])]
  | ⟨2, _⟩ => [(4, [0,1])]
  | ⟨3, _⟩ => [(1, [0,0]), (15/2, [])]

theorem jE_cert (n : Fin 4) :
    normR (polyActWC JR (-(n : ℤ)-1) P0 ++ scaleR (-1) (jE n).poly) =
      normR (cc2 (correction n) ++ scaleR (-8) (correction n)) := by
  fin_cases n <;> decide +kernel

end ChargedExpr

/-- All four charged J-mode identities in Dong--Jiang Lemma 3.4. -/
theorem J_modes_E_four (n : Fin 4) :
    (V2mPlus 4 (by norm_num)).smul (J 4 (by norm_num)) (n : ℤ) (EP 4 (by norm_num)) =
      (ChargedExpr.jE n).apply 4 (by norm_num) (EP 4 (by norm_num)) := by
  have h := charged_eq_of_cert
    (hasC_smul_left _ _ (hasN_J _ _) (hasC_y0 _ _) (n : ℤ))
    (ChargedExpr.hasC_state _ _ (ChargedExpr.jE n)) _ (ChargedExpr.jE_cert n)
  rw [ChargedExpr.apply_two, EP_eq_y0, PreVertexAlgebra.smul_smul_right, h]

end VOA.Classification.COne.OrbC2c
