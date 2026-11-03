import VOA.DeligneAudit.DeligneFusionCVRectPolynomial

/-!
# The actual cyclic representation and its finite two-color currents

Restriction to the cyclic submodule makes high first/highest-root modes
zero as operators, not just on the generator. This is the bridge between
the full CV coefficient relations and finite reversed current polynomials.
-/

namespace VOA.DeligneAudit.A2.CVRectPolynomial

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVUniv
open VOA.DeligneAudit.CLNormal
open scoped IsMulCommutative

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def cyclicRep (R : CurrentModule bracketTable V) (w : V) :
    CurrentModule bracketTable (CVRectSingle.cyclicSpan R w) where
  op c s := (R.op c s).restrict (fun _ hx => cyclicSpan_inv R w c s hx)
  comm a b r s v := by
    apply Subtype.ext
    simpa using R.comm a b r s (v : V)

def cyclicVector (R : CurrentModule bracketTable V) (w : V) :
    CVRectSingle.cyclicSpan R w := ⟨w, word_mem R w []⟩

@[simp] theorem cyclicRep_op_coe (R : CurrentModule bracketTable V) (w : V)
    (c : Fin 8) (s : ℕ) (v : CVRectSingle.cyclicSpan R w) :
    ((cyclicRep R w).op c s v : V) = R.op c s (v : V) := rfl

@[simp] theorem cyclicVector_coe (R : CurrentModule bracketTable V) (w : V) :
    (cyclicVector R w : V) = w := rfl

theorem cyclic_word_coe (R : CurrentModule bracketTable V) (w : V)
    (l : List (Fin 8 × ℕ)) (v : CVRectSingle.cyclicSpan R w) :
    (↑(wordOp (cyclicRep R w) l v) : V) = wordOp R l (v : V) := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa only [wordOp, cyclicRep_op_coe] using congrArg (R.op x.1 x.2) ih

/-- Every source CV relation holds in the actual restricted representation. -/
theorem cyclic_rel (R : CurrentModule bracketTable V) (w : V)
    {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j) :
    CV3Rel (cyclicRep R w) (cyclicVector R w) ε ν ϱ j := by
  apply sat_cvSpec_iff.mp
  have hs := sat_cvSpec_iff.mpr h
  constructor
  · intro t ht
    apply Subtype.ext
    simpa only [cyclic_word_coe, cyclicVector_coe, Submodule.coe_zero] using hs.tail t ht
  · intro p hp
    apply Subtype.ext
    simpa only [cyclicRep_op_coe, cyclicVector_coe, Submodule.coe_smul] using hs.eig p hp

def currentMode (R : CurrentModule bracketTable V) (b : Bool) (s : ℕ) : Module.End ℂ V :=
  if b then R.op 5 s else R.op 3 s

theorem currentMode_commute (R : CurrentModule bracketTable V) (b c : Bool) (s t : ℕ) :
    Commute (currentMode R b s) (currentMode R c t) := by
  cases b <;> cases c
  · exact (CVRoots.sl2_first R).hFF s t
  · exact c_f1f5 R s t
  · exact (c_f1f5 R t s).symm
  · exact (CVRoots.sl2_highest R).hFF s t

theorem currentMode_operatorEval_commute (R : CurrentModule bracketTable V)
    (b : Bool) (s N : ℕ) (p : MvPolynomial (Variables N) ℂ) :
    Commute (currentMode R b s) (operatorEval R N p) := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute
    (R := ℂ) (s := Set.range (colorOp R (N := N)))
  · exact (MvPolynomial.aeval (colorIn R) p).property
  · rintro _ ⟨x, rfl⟩
    exact currentMode_commute R b x.1 s x.2.val

/-- The high modes vanish on the whole actual cyclic submodule because
they commute with every polynomial generator and kill the cyclic vector. -/
theorem high_currentMode_zero (R : CurrentModule bracketTable V) (w : V)
    {e n r : ℕ} (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0)
    (b : Bool) (s : ℕ) (hs : r + n + e ≤ s) :
    currentMode (cyclicRep R w) b s = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have hv : (v : V) ∈ LinearMap.range (vectorEval R w (r + n + e)) := by
    rw [vectorEval_range R w h]
    exact v.property
  obtain ⟨p, hp⟩ := hv
  have ht : currentMode R b s w = 0 := by
    cases b
    · exact CVRectCommutative.first_trunc h s hs
    · exact CVRectCommutative.theta_trunc h s hs
  have hc := currentMode_operatorEval_commute R b s (r + n + e) p
  have he : currentMode R b s (v : V) = 0 := by
    rw [← hp]
    change currentMode R b s (operatorEval R (r + n + e) p w) = 0
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, ht, map_zero]
  cases b <;> simpa only [currentMode, Bool.false_eq_true, ↓reduceIte,
    cyclicRep_op_coe, LinearMap.zero_apply, Submodule.coe_zero] using he

end

end VOA.DeligneAudit.A2.CVRectPolynomial

#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.cyclic_rel
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.high_currentMode_zero
