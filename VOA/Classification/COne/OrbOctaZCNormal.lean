import VOA.Classification.COne.OrbOctaZCModes

/-! Small rational certificates for equality of polynomial mode relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOdd OrbZhu Polynomial

def insertRel (p : ℤ × PL) : ModeRel → ModeRel
  | [] => [p]
  | q :: r => if p.1 = q.1 then (q.1, paddL p.2 q.2) :: r else q :: insertRel p r

def normalizeRel : ModeRel → ModeRel
  | [] => []
  | p :: r => insertRel p (normalizeRel r)

def zeroRel (r : ModeRel) : Bool := r.all fun p => ptrim p.2 == []

def equalRelCheck (r s : ModeRel) : Bool :=
  zeroRel (normalizeRel (r ++ scaleRel [-1] s))

/-- Merge equal indices after each recursion step to keep kernel checks small. -/
def modeWordN : List ℕ → ℤ → ModeRel
  | [], k => [(k, [1])]
  | n :: w, k => normalizeRel
    (scaleRel (zfac n (31 + (w.sum : ℚ) - k)) (modeWordN w k) ++
      scaleRel [15 * ((n : ℚ) - 1) + k] (modeWordN w (k - n)))

def modeVectorN : VVec → ℤ → ModeRel
  | [], _ => []
  | p :: v, k => normalizeRel
    (scaleRel [p.1] (modeWordN p.2 k) ++ modeVectorN v k)

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem evalRel_insert (a : ℤ → A W) (p : ℤ × PL) (r : ModeRel) :
    evalRel W a (insertRel p r) =
      aeval (omegaL W) (zp p.2) (a p.1) + evalRel W a r := by
  induction r with
  | nil => rfl
  | cons q r ih =>
    unfold insertRel
    split_ifs with h
    · simp only [evalRel, zp_paddL, map_add, LinearMap.add_apply, h]
      abel
    · simp only [evalRel, ih]
      abel

theorem evalRel_normalize (a : ℤ → A W) (r : ModeRel) :
    evalRel W a (normalizeRel r) = evalRel W a r := by
  induction r with
  | nil => rfl
  | cons p r ih => rw [normalizeRel, evalRel_insert, ih, evalRel]

theorem modeWordN_eval (a : ℤ → A W) : ∀ (w : List ℕ) (k : ℤ),
    evalRel W a (modeWordN w k) = evalRel W a (modeWord w k)
  | [], _ => rfl
  | n :: w, k => by
    simp only [modeWordN, modeWord, evalRel_normalize, evalRel_append, evalRel_scale,
      modeWordN_eval a w]

theorem modeVectorN_eval (a : ℤ → A W) : ∀ (v : VVec) (k : ℤ),
    evalRel W a (modeVectorN v k) = evalRel W a (modeVector v k)
  | [], _ => rfl
  | p :: v, k => by
    simp only [modeVectorN, modeVector, evalRel_normalize, evalRel_append, evalRel_scale,
      modeWordN_eval, modeVectorN_eval a v]

theorem evalRel_zero_of_check (a : ℤ → A W) {r : ModeRel} (h : zeroRel r = true) :
    evalRel W a r = 0 := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    simp only [zeroRel, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have hp : zp p.2 = 0 := by rw [← zp_ptrim, h.1]; rfl
    rw [evalRel, hp, map_zero, LinearMap.zero_apply, zero_add, ih h.2]

theorem equalRelCheck_sound (a : ℤ → A W) {r s : ModeRel}
    (h : equalRelCheck r s = true) : evalRel W a r = evalRel W a s := by
  have h' := evalRel_zero_of_check W a h
  rw [evalRel_normalize, evalRel_append, evalRel_scalar] at h'
  simpa only [Rat.cast_neg, Rat.cast_one, neg_one_smul, add_neg_eq_zero] using h'
end General
end VOA.Classification.COne.OrbOctaZC
