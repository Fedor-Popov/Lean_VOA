import VOA.Classification.COne.OrbIcoZSpecialize

/-! Exact substitution and nonzero constant pivot cancellation for actual Zhu modes. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial OrbIco

/-- Substitute already proved polynomial mode expressions into a finite row. -/
def substRel (f : ℤ → ModeRel) : ModeRel → ModeRel
  | [] => []
  | p :: r => scaleRel p.2 (f p.1) ++ substRel f r

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem evalRel_subst (a : ℤ → A W) (f : ℤ → ModeRel)
    (hf : ∀ k, a k = evalRel W a (f k)) (r : ModeRel) :
    evalRel W a (substRel f r) = evalRel W a r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    rw [substRel, evalRel_append, evalRel_scale, ← hf p.1, ih, evalRel]

theorem constant_pivot (a : ℤ → A W) (f : ℤ → ModeRel)
    (hf : ∀ k, a k = evalRel W a (f k)) (r e : ModeRel) (j : ℤ) (c : ℚ)
    (hc : c ≠ 0) (hr : evalRel W a r = 0)
    (hcheck : equalRelCheck (substRel f r) ([(j, [c])] ++ scaleRel [-c] e) = true) :
    a j = evalRel W a e := by
  have hh := equalRelCheck_sound W a hcheck
  rw [evalRel_subst W a f hf r, hr, evalRel_append, evalRel_scalar] at hh
  have hz : (c : ℂ) • (a j - evalRel W a e) = 0 := by
    simpa [evalRel, zp, smul_sub, sub_eq_add_neg] using hh.symm
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hcc)

end General

/-- The initial table only removes the genuinely vanishing high modes. -/
def modeInterpInitial (k : ℤ) : ModeRel := if 71 < k then [] else [(k, [1])]

theorem modeInterpInitial_correct (k : ℤ) :
    selfMode k = evalRel Wi selfMode (modeInterpInitial k) := by
  unfold modeInterpInitial
  split_ifs with h
  · simp only [evalRel, selfMode_high k h]
  · simp [evalRel, zp]

/-- One certified pivot updates a table that is valid for every integer mode. -/
theorem modeInterp_update (f : ℤ → ModeRel)
    (hf : ∀ k, selfMode k = evalRel Wi selfMode (f k))
    (r e : ModeRel) (j : ℤ) (c : ℚ) (hc : c ≠ 0)
    (hr : evalRel Wi selfMode r = 0)
    (hcheck : equalRelCheck (substRel f r) ([(j, [c])] ++ scaleRel [-c] e) = true) :
    ∀ k, selfMode k = evalRel Wi selfMode (if k = j then e else f k) := by
  intro k
  split_ifs with h
  · subst k
    exact constant_pivot Wi selfMode f hf r e j c hc hr hcheck
  · exact hf k

end VOA.Classification.COne.OrbIcoZ
