import VOA.Classification.COne.OrbIcoZSymbolBackend

/-! One exact symbolic coefficient certificate for every A5 integer mode. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

def bzero (p : BP) : Bool := p.all fun q => ptrim q == []
def equalRawCheck (r s : RawSym) : Bool :=
  (rawNorm (r ++ rawScale [[-1]] s)).all fun p => bzero p.2

private theorem bp_zero_of_check {p : BP} (h : bzero p = true) : bp p = 0 := by
  induction p with
  | nil => rfl
  | cons q p ih =>
    simp only [bzero, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have hq : qp q = 0 := by rw [← qp_trim, h.1]; rfl
    simp only [bp, hq, ih h.2, Polynomial.C_0, mul_zero, add_zero]

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem evalRaw_zero_of_check (k : ℤ) (a : ℤ → A W) {r : RawSym}
    (h : r.all (fun p => bzero p.2) = true) : evalSym W k a (symMap r) = 0 := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [symMap, List.map_cons, evalSym, bp_zero_of_check h.1,
      map_zero, LinearMap.zero_apply]
    change 0 + evalSym W k a (symMap r) = 0
    rw [ih h.2, add_zero]

theorem equalRawCheck_sound (k : ℤ) (a : ℤ → A W) {r s : RawSym}
    (h : equalRawCheck r s = true) :
    evalSym W k a (symMap r) = evalSym W k a (symMap s) := by
  have hh := evalRaw_zero_of_check W k a h
  rw [symMap_norm, symMap_append, symMap_scale, evalSym_normalize,
    evalSym_append, evalSym_scale] at hh
  have hm : bp [[-1]] = (-1 : Biv) := by simp [bp, qp]
  rw [hm] at hh
  simpa only [map_neg, map_one, LinearMap.neg_apply, Module.End.one_apply,
    add_neg_eq_zero] using hh

end General

theorem evalSym_vector_append {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) (v w : OrbOdd.VVec) :
    evalSym W k a (symVector (v ++ w)) =
      evalSym W k a (symVector v) + evalSym W k a (symVector w) := by
  induction v with
  | nil => simp [symVector, evalSym]
  | cons p v ih =>
    simp only [List.cons_append, symVector, evalSym_normalize,
      evalSym_append, evalSym_scale, ih]
    abel

end VOA.Classification.COne.OrbIcoZ
