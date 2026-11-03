import VOA.Classification.COne.OrbIcoZSymbolBackend

/-! Exact specialization of the pure symbolic coefficient lists at every integer mode. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

theorem qp_mapCast : ∀ p : PL, (qp p).map (Rat.castHom ℂ) = zp p
  | [] => by simp [qp, zp]
  | x :: p => by
    simp only [qp, zp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul,
      Polynomial.map_X, qp_mapCast]
    rfl

def evalBP (k : ℤ) : BP → PL
  | [] => []
  | p :: r => paddL p (pscaleL (k : ℚ) (evalBP k r))

theorem evalBP_sound (k : ℤ) : ∀ p : BP, zp (evalBP k p) = bivarEval k (bp p)
  | [] => by simp [evalBP, zp, bp]
  | p :: r => by
    rw [evalBP, zp_paddL, zp_pscaleL, evalBP_sound k r]
    simp only [bp, map_add, map_mul, bivarEval_C, bivarEval_X, qp_mapCast]
    norm_num only [Rat.cast_intCast]

def specialize (k : ℤ) (r : RawSym) : ModeRel :=
  r.map fun p => (k - p.1, evalBP k p.2)

section
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem evalSpecialize (k : ℤ) (a : ℤ → A W) (r : RawSym) :
    evalRel W a (specialize k r) = evalSym W k a (symMap r) := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    simp only [specialize, symMap] at ih
    simp only [specialize, symMap, List.map_cons, evalRel, evalSym, evalBP_sound, ih]

end
end VOA.Classification.COne.OrbIcoZ
