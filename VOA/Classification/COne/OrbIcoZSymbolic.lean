import VOA.Classification.COne.OrbIcoZNormal
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! One symbolic two-variable mixed-mode recursion for every integer mode.
The inner variable is the conformal class and the outer variable is the mode index. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

abbrev Biv := Polynomial (Polynomial ℚ)
abbrev SymRel := List (ℕ × Biv)

def bivarEval (k : ℤ) : Biv →+* ℂ[X] :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom (Rat.castHom ℂ)) (Polynomial.C (k : ℂ))

def shiftB (n : ℕ) (p : Biv) : Biv :=
  p.comp (Polynomial.X - Polynomial.C (Polynomial.C (n : ℚ)))

@[simp] theorem bivarEval_C (k : ℤ) (p : ℚ[X]) :
    bivarEval k (Polynomial.C p) = p.map (Rat.castHom ℂ) := by
  simp [bivarEval]

@[simp] theorem bivarEval_X (k : ℤ) :
    bivarEval k Polynomial.X = Polynomial.C (k : ℂ) := by
  simp [bivarEval]

theorem bivarEval_shift (k : ℤ) (n : ℕ) (p : Biv) :
    bivarEval k (shiftB n p) = bivarEval (k - n) p := by
  change Polynomial.eval₂ _ _ (p.comp _) = Polynomial.eval₂ _ _ p
  rw [Polynomial.eval₂_comp]
  congr 1
  simp [bivarEval, shiftB]

def symFactor (n : ℕ) (d : ℚ) : Biv :=
  Polynomial.C (Polynomial.C ((-1)^n * d) +
      Polynomial.C ((-1)^n * ((n : ℚ) - 1)) * Polynomial.X) -
    Polynomial.C (Polynomial.C ((-1)^n)) * Polynomial.X

def symSecond (n : ℕ) : Biv :=
  Polynomial.C (Polynomial.C (35 * ((n : ℚ) - 1))) + Polynomial.X

theorem bivarEval_factor (k : ℤ) (n : ℕ) (d : ℚ) :
    bivarEval k (symFactor n d) = zp (zfac n (d - k)) := by
  simp [symFactor, zfac, zp, pscaleL, bivarEval]
  push_cast
  ring

theorem bivarEval_second (k : ℤ) (n : ℕ) :
    bivarEval k (symSecond n) = Polynomial.C (35 * ((n : ℂ) - 1) + k) := by
  simp [symSecond, bivarEval]

def scaleSym (p : Biv) (r : SymRel) : SymRel := r.map fun q => (q.1, p * q.2)

def shiftSym (n : ℕ) (r : SymRel) : SymRel :=
  r.map fun q => (n + q.1, shiftB n q.2)

def insertSym (p : ℕ × Biv) : SymRel → SymRel
  | [] => [p]
  | q :: r => if p.1 = q.1 then (q.1, p.2 + q.2) :: r else q :: insertSym p r

def normalizeSym : SymRel → SymRel
  | [] => []
  | p :: r => insertSym p (normalizeSym r)

def symWord : List ℕ → SymRel
  | [] => [(0, 1)]
  | n :: w => normalizeSym
      (scaleSym (symFactor n (71 + w.sum)) (symWord w) ++
        scaleSym (symSecond n) (shiftSym n (symWord w)))

def symVector : VVec → SymRel
  | [] => []
  | p :: v => normalizeSym
      (scaleSym (Polynomial.C (Polynomial.C p.1)) (symWord p.2) ++ symVector v)

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

def evalSym (k : ℤ) (a : ℤ → A W) : SymRel → A W
  | [] => 0
  | p :: r => aeval (omegaL W) (bivarEval k p.2) (a (k - p.1)) + evalSym k a r

theorem evalSym_append (k : ℤ) (a : ℤ → A W) (r s : SymRel) :
    evalSym W k a (r ++ s) = evalSym W k a r + evalSym W k a s := by
  induction r with
  | nil => simp [evalSym]
  | cons p r ih => simp only [List.cons_append, evalSym, ih, add_assoc]

theorem evalSym_scale (k : ℤ) (a : ℤ → A W) (p : Biv) (r : SymRel) :
    evalSym W k a (scaleSym p r) =
      aeval (omegaL W) (bivarEval k p) (evalSym W k a r) := by
  induction r with
  | nil => simp [evalSym, scaleSym]
  | cons q r ih =>
    simp only [scaleSym] at ih
    simp only [scaleSym, List.map_cons, evalSym, map_mul, Module.End.mul_apply,
      map_add, ih]

theorem evalSym_shift (k : ℤ) (a : ℤ → A W) (n : ℕ) (r : SymRel) :
    evalSym W k a (shiftSym n r) = evalSym W (k - n) a r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    simp only [shiftSym] at ih
    simp only [shiftSym, List.map_cons, evalSym, bivarEval_shift, ih]
    congr 2
    push_cast
    ring

theorem evalSym_insert (k : ℤ) (a : ℤ → A W) (p : ℕ × Biv) (r : SymRel) :
    evalSym W k a (insertSym p r) =
      aeval (omegaL W) (bivarEval k p.2) (a (k - p.1)) + evalSym W k a r := by
  induction r with
  | nil => rfl
  | cons q r ih =>
    unfold insertSym
    split_ifs with h
    · simp only [evalSym, map_add, LinearMap.add_apply, h]
      abel
    · simp only [evalSym, ih]
      abel

theorem evalSym_normalize (k : ℤ) (a : ℤ → A W) (r : SymRel) :
    evalSym W k a (normalizeSym r) = evalSym W k a r := by
  induction r with
  | nil => rfl
  | cons p r ih => rw [normalizeSym, evalSym_insert, ih, evalSym]


theorem symWord_sound {a x : V}
    (ha : a ∈ W.grading 36) (hx : x ∈ W.grading 36)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) :
    ∀ w : List ℕ, posW w = true → ∀ k : ℤ,
      mk W (W.smul a k (evW W x w)) =
        evalSym W k (fun j => mk W (W.smul a j x)) (symWord w)
  | [], _, k => by simp [evW, symWord, evalSym]
  | n :: w, hw, k => by
    simp only [posW, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    rw [evW, mk_primary_Lneg W ha (evW_mem_grading W hx w) hp n hw.1 k,
      symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
      evalSym_shift, ← symWord_sound ha hx hp w hw.2 k,
      ← symWord_sound ha hx hp w hw.2 (k - n),
      bivarEval_factor, bivarEval_second, aeval_C, Module.algebraMap_end_apply]
    congr 2
    · congr 3
      simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
      ring
    · push_cast; ring

theorem symVector_sound {a x : V}
    (ha : a ∈ W.grading 36) (hx : x ∈ W.grading 36)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) :
    ∀ v : VVec, posV v = true → ∀ k : ℤ,
      mk W (W.smul a k (evV W x v)) =
        evalSym W k (fun j => mk W (W.smul a j x)) (symVector v)
  | [], _, k => by simp [evV, symVector, evalSym, PreVertexAlgebra.smul_zero_right]
  | p :: v, hv, k => by
    simp only [posV, List.all_cons, Bool.and_eq_true] at hv
    rw [evV_cons, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      map_add, map_smul, symWord_sound W ha hx hp p.2 hv.1,
      symVector_sound ha hx hp v hv.2, symVector, evalSym_normalize,
      evalSym_append, evalSym_scale]
    simp [bivarEval, Module.algebraMap_end_apply]

end General
end VOA.Classification.COne.OrbIcoZ
