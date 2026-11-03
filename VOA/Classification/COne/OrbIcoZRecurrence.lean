import VOA.Classification.COne.OrbIcoZSingular

/-! Polynomial recurrences for the mixed modes of the weight-thirty-six primary.
Unlike the direct Zhu image of the singular vector, its mixed modes give
nontrivial relations. All polynomials are exact rational coefficient lists.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3

noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial

/-- An indexed finite polynomial linear combination of mode classes. -/
abbrev ModeRel := List (ℤ × PL)

def scaleRel (p : PL) (r : ModeRel) : ModeRel :=
  r.map fun q => (q.1, pmulL p q.2)

/-- Move Virasoro operators from the second input to the output. -/
def modeWord : List ℕ → ℤ → ModeRel
  | [], k => [(k, [1])]
  | n :: w, k =>
    scaleRel (zfac n (71 + (w.sum : ℚ) - k)) (modeWord w k) ++
    scaleRel [35 * ((n : ℚ) - 1) + k] (modeWord w (k - n))

def modeVector : VVec → ℤ → ModeRel
  | [], _ => []
  | p :: v, k => scaleRel [p.1] (modeWord p.2 k) ++ modeVector v k

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

def evalRel (a : ℤ → A W) : ModeRel → A W
  | [] => 0
  | p :: r => aeval (omegaL W) (zp p.2) (a p.1) + evalRel a r

theorem evalRel_append (a : ℤ → A W) (r s : ModeRel) :
    evalRel W a (r ++ s) = evalRel W a r + evalRel W a s := by
  induction r with
  | nil => simp [evalRel]
  | cons p r ih => simp only [List.cons_append, evalRel, ih, add_assoc]

theorem evalRel_scale (a : ℤ → A W) (p : PL) (r : ModeRel) :
    evalRel W a (scaleRel p r) = aeval (omegaL W) (zp p) (evalRel W a r) := by
  induction r with
  | nil => simp [evalRel, scaleRel]
  | cons q r ih =>
    simp only [scaleRel, List.map_cons, evalRel, zp_pmulL, map_mul,
      Module.End.mul_apply, map_add] at ih ⊢
    rw [ih]

theorem evalRel_scalar (a : ℤ → A W) (c : ℚ) (r : ModeRel) :
    evalRel W a (scaleRel [c] r) = (c : ℂ) • evalRel W a r := by
  rw [evalRel_scale]
  simp [zp]

/-- One step of the mixed-mode recursion, including its grading term. -/
theorem mk_primary_Lneg {a y : V} {d : ℤ}
    (ha : a ∈ W.grading 36) (hy : y ∈ W.grading d)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    mk W (W.smul a k (W.L (-(n : ℤ)) y)) =
      aeval (omegaL W) (zp (zfac n (35 + (d : ℚ) - k)))
        (mk W (W.smul a k y)) +
      ((35 * ((n : ℤ) - 1) + k : ℤ) : ℂ) • mk W (W.smul a (k - n) y) := by
  have hg : W.smul a k y ∈ W.grading (35 + d - k) := by
    convert W.grading_mode a ha y hy k using 2; ring
  have he := L_smul_primary ha hp (-(n : ℤ)) k y
  have he' := congrArg (mk W) he
  rw [map_add, map_smul, mk_L_neg W hg n hn] at he'
  rw [aeval_zfac]
  have hi : -(n : ℤ) + k = k - n := by omega
  rw [hi] at he'
  have hh := eq_sub_of_add_eq he'.symm
  rw [hh]
  push_cast
  module

/-- Soundness of the rational word recursion. -/
theorem modeWord_sound {a x : V}
    (ha : a ∈ W.grading 36) (hx : x ∈ W.grading 36)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) :
    ∀ w : List ℕ, posW w = true → ∀ k : ℤ,
      mk W (W.smul a k (evW W x w)) =
        evalRel W (fun j => mk W (W.smul a j x)) (modeWord w k)
  | [], _, k => by simp [evW, modeWord, evalRel, zp]
  | n :: w, hw, k => by
    simp only [posW, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    rw [evW, mk_primary_Lneg W ha (evW_mem_grading W hx w) hp n hw.1 k,
      modeWord, evalRel_append, evalRel_scale, evalRel_scalar,
      ← modeWord_sound ha hx hp w hw.2 k, ← modeWord_sound ha hx hp w hw.2 (k - n)]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Int.cast_ofNat, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_intCast, Rat.cast_ofNat]
    rw [show (35 : ℚ) + (36 + w.sum) - k = 71 + w.sum - k by ring]
    norm_num

/-- Soundness for a rational linear combination of words. -/
theorem modeVector_sound {a x : V}
    (ha : a ∈ W.grading 36) (hx : x ∈ W.grading 36)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) :
    ∀ v : VVec, posV v = true → ∀ k : ℤ,
      mk W (W.smul a k (evV W x v)) =
        evalRel W (fun j => mk W (W.smul a j x)) (modeVector v k)
  | [], _, k => by simp [evV, modeVector, evalRel, PreVertexAlgebra.smul_zero_right]
  | p :: v, hv, k => by
    simp only [posV, List.all_cons, Bool.and_eq_true] at hv
    rw [evV_cons, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      map_add, map_smul, modeWord_sound W ha hx hp p.2 hv.1,
      modeVector_sound ha hx hp v hv.2, modeVector, evalRel_append, evalRel_scalar]
end General

/-- Every mode of the certified singular vector gives a Zhu relation. -/
theorem s13_mode_relation (k : ℤ) :
    evalRel OrbIco.Wi (fun j => mk OrbIco.Wi (OrbIco.Wi.smul OrbIco.Xico j OrbIco.Xico))
      (modeVector s13v k) = 0 := by
  have hp : ∀ m : ℕ, 1 ≤ m → OrbIco.Wi.L (m : ℤ) OrbIco.Xico = 0 := by
    intro m hm
    have h := ((OrbSpan.mem_prim _).mp X_primary).2 (m - 1)
    rwa [show ((m - 1 : ℕ) : ℤ) + 1 = m by omega] at h
  have hs : posV s13v = true := by
    simp only [posV, List.all_eq_true]
    intro p hp
    exact (s13v_spec p hp).2.2
  rw [← modeVector_sound OrbIco.Wi OrbIco.Xico_grading OrbIco.Xico_grading hp s13v hs,
    s13_zero, PreVertexAlgebra.smul_zero_right, map_zero]

end VOA.Classification.COne.OrbIcoZ
