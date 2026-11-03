import VOA.Classification.COne.OrbIcoZNormal

/-! Mixed-mode identities after quotienting by the conformal class.
Every identity is proved for the actual Zhu algebra and its actual quotient. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial OrbIco

/-- Scalar mode relations, represented by constant polynomial lists. -/
def constScale (c : ℚ) (r : ModeRel) : ModeRel :=
  r.map fun q => (q.1, pscaleL c q.2)

/-- The mixed-mode recursion evaluated at the zero conformal fiber. -/
def constWord : List ℕ → ℤ → ModeRel
  | [], k => [(k, [1])]
  | n :: w, k => normalizeRel
      (constScale ((-1)^n * (71 + (w.sum : ℚ) - k)) (constWord w k) ++
        constScale (35 * ((n : ℚ) - 1) + k) (constWord w (k - n)))

def constVector : VVec → ℤ → ModeRel
  | [], _ => []
  | p :: v, k => normalizeRel
      (constScale p.1 (constWord p.2 k) ++ constVector v k)

section General
variable {V T : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup T] [Module ℂ T] (W : VertexOperatorAlgebra V)

/-- Evaluation through a linear map whose kernel contains the conformal image. -/
def evalConst (f : A W →ₗ[ℂ] T) (a : ℤ → A W) : ModeRel → T
  | [] => 0
  | p :: r => (p.2.headD 0 : ℂ) • f (a p.1) + evalConst f a r

theorem evalConst_append (f : A W →ₗ[ℂ] T) (a : ℤ → A W) (r s : ModeRel) :
    evalConst W f a (r ++ s) = evalConst W f a r + evalConst W f a s := by
  induction r with
  | nil => simp [evalConst]
  | cons p r ih => simp only [List.cons_append, evalConst, ih, add_assoc]

private theorem constTerm_padd (p q : PL) :
    (paddL p q).headD 0 = p.headD 0 + q.headD 0 := by
  cases p <;> cases q <;> simp [paddL]

private theorem constTerm_scale (c : ℚ) (p : PL) :
    (pscaleL c p).headD 0 = c * p.headD 0 := by
  cases p <;> simp [pscaleL]

theorem evalConst_scale (f : A W →ₗ[ℂ] T) (a : ℤ → A W) (c : ℚ) (r : ModeRel) :
    evalConst W f a (constScale c r) = (c : ℂ) • evalConst W f a r := by
  induction r with
  | nil => simp [evalConst, constScale]
  | cons p r ih =>
    simp only [constScale] at ih
    simp only [constScale, List.map_cons, evalConst, constTerm_scale, Rat.cast_mul,
      mul_smul, ih, smul_add]

theorem evalConst_insert (f : A W →ₗ[ℂ] T) (a : ℤ → A W)
    (p : ℤ × PL) (r : ModeRel) :
    evalConst W f a (insertRel p r) =
      (p.2.headD 0 : ℂ) • f (a p.1) + evalConst W f a r := by
  induction r with
  | nil => rfl
  | cons q r ih =>
    unfold insertRel
    split_ifs with h
    · simp only [evalConst, constTerm_padd, Rat.cast_add, add_smul, h]
      abel
    · simp only [evalConst, ih]
      abel

theorem evalConst_normalize (f : A W →ₗ[ℂ] T) (a : ℤ → A W) (r : ModeRel) :
    evalConst W f a (normalizeRel r) = evalConst W f a r := by
  induction r with
  | nil => rfl
  | cons p r ih => rw [normalizeRel, evalConst_insert, ih, evalConst]

theorem project_aeval (f : A W →ₗ[ℂ] T)
    (hf : ∀ z, f (omegaL W z) = 0) (p : PL) (z : A W) :
    f (aeval (omegaL W) (zp p) z) = (p.headD 0 : ℂ) • f z := by
  cases p with
  | nil => simp [zp]
  | cons c p =>
    rw [zp, map_add, LinearMap.add_apply, map_add, aeval_C, map_mul, aeval_X,
      Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hf, add_zero]
    rfl

theorem project_evalRel (f : A W →ₗ[ℂ] T)
    (hf : ∀ z, f (omegaL W z) = 0) (a : ℤ → A W) (r : ModeRel) :
    f (evalRel W a r) = evalConst W f a r := by
  induction r with
  | nil => simp [evalRel, evalConst]
  | cons p r ih => rw [evalRel, map_add, project_aeval W f hf, ih, evalConst]

theorem equalConstCheck_sound (f : A W →ₗ[ℂ] T)
    (hf : ∀ z, f (omegaL W z) = 0) (a : ℤ → A W) {r s : ModeRel}
    (h : equalRelCheck r s = true) : evalConst W f a r = evalConst W f a s := by
  have hh := congrArg f (equalRelCheck_sound W a h)
  simpa only [project_evalRel W f hf] using hh

/-- Constant mixed-mode recursion agrees with the actual mixed modes after projection. -/
theorem constWord_sound (f : A W →ₗ[ℂ] T)
    (hf : ∀ z, f (omegaL W z) = 0) (a x : V)
    (ha : a ∈ W.grading 36) (hx : x ∈ W.grading 36)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) :
    ∀ w : List ℕ, posW w = true → ∀ k : ℤ,
      f (mk W (W.smul a k (evW W x w))) =
        evalConst W f (fun j => mk W (W.smul a j x)) (constWord w k)
  | [], _, k => by simp [evW, constWord, evalConst]
  | n :: w, hw, k => by
    simp only [posW, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    rw [evW, mk_primary_Lneg W ha (evW_mem_grading W hx w) hp n hw.1 k,
      map_add, project_aeval W f hf, map_smul,
      constWord, evalConst_normalize, evalConst_append, evalConst_scale,
      evalConst_scale, ← constWord_sound f hf a x ha hx hp w hw.2 k,
      ← constWord_sound f hf a x ha hx hp w hw.2 (k - n)]
    simp only [zfac, pscaleL, List.map_cons, List.headD_cons, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_add, Rat.cast_sub,
      Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_intCast, Int.cast_mul,
      Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast]
    congr 2 <;> push_cast <;> ring

theorem constVector_sound (f : A W →ₗ[ℂ] T)
    (hf : ∀ z, f (omegaL W z) = 0) (a x : V)
    (ha : a ∈ W.grading 36) (hx : x ∈ W.grading 36)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) :
    ∀ v : VVec, posV v = true → ∀ k : ℤ,
      f (mk W (W.smul a k (evV W x v))) =
        evalConst W f (fun j => mk W (W.smul a j x)) (constVector v k)
  | [], _, k => by simp [evV, constVector, evalConst, PreVertexAlgebra.smul_zero_right]
  | p :: v, hv, k => by
    simp only [posV, List.all_cons, Bool.and_eq_true] at hv
    rw [evV_cons, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      map_add, map_smul, map_add, map_smul,
      constWord_sound W f hf a x ha hx hp p.2 hv.1,
      constVector_sound f hf a x ha hx hp v hv.2,
      constVector, evalConst_normalize, evalConst_append, evalConst_scale]

end General

theorem const_singular_relation {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) (k : ℤ) :
    evalConst Wi f selfMode (constVector s13v k) = 0 := by
  have hp : ∀ m : ℕ, 1 ≤ m → Wi.L (m : ℤ) Xico = 0 := by
    intro m hm
    have h := ((OrbSpan.mem_prim _).mp X_primary).2 (m - 1)
    rwa [show ((m - 1 : ℕ) : ℤ) + 1 = m by omega] at h
  have hs : posV s13v = true := by
    simp only [posV, List.all_eq_true]
    intro p hp
    exact (s13v_spec p hp).2.2
  rw [← constVector_sound Wi f hf Xico Xico Xico_grading Xico_grading hp s13v hs,
    s13_zero, PreVertexAlgebra.smul_zero_right, map_zero, map_zero]

end VOA.Classification.COne.OrbIcoZ
