import VOA.DeligneAudit.DeligneFusionCVRectCommutative
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Polynomial action of the actual one-orientation CV currents

The first and highest-root currents generate a commutative subalgebra of
endomorphisms. Evaluation in that subalgebra gives a genuine polynomial
action on the cyclic vector. Its range is the actual cyclic submodule,
by the proved two-color PBW reduction.

No dimension bound, tensor product realization or fusion presentation is
an assumption of this construction.
-/

namespace VOA.DeligneAudit.A2.CVRectPolynomial

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CLNormal VOA.DeligneAudit.A2.CVFamily
open scoped IsMulCommutative

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Two colors, at the common finite truncation length. -/
abbrev Variables (N : ℕ) := Bool × Fin N

def colorOp (R : CurrentModule bracketTable V) {N : ℕ} (x : Variables N) :
    Module.End ℂ V := if x.1 then R.op 5 x.2.val else R.op 3 x.2.val

theorem colorOp_commute (R : CurrentModule bracketTable V) {N : ℕ}
    (x y : Variables N) : colorOp R x * colorOp R y = colorOp R y * colorOp R x := by
  rcases x with ⟨b, i⟩
  rcases y with ⟨c, j⟩
  cases b <;> cases c
  · exact (CVRoots.sl2_first R).hFF i j
  · exact c_f1f5 R i j
  · exact (c_f1f5 R j i).symm
  · exact (CVRoots.sl2_highest R).hFF i j

def OpAlgebra (R : CurrentModule bracketTable V) (N : ℕ) :
    Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range (colorOp R (N := N)))

instance opAlgebra_commutative (R : CurrentModule bracketTable V) (N : ℕ) :
    IsMulCommutative (OpAlgebra R N) := by
  apply Algebra.isMulCommutative_adjoin
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact colorOp_commute R x y

def colorIn (R : CurrentModule bracketTable V) {N : ℕ} (x : Variables N) :
    OpAlgebra R N := ⟨colorOp R x, Algebra.subset_adjoin ⟨x, rfl⟩⟩

/-- Evaluation in an actual commutative algebra of current operators. -/
def operatorEval (R : CurrentModule bracketTable V) (N : ℕ) :
    MvPolynomial (Variables N) ℂ →ₐ[ℂ] Module.End ℂ V :=
  (OpAlgebra R N).val.comp (MvPolynomial.aeval (colorIn R))

@[simp] theorem operatorEval_X (R : CurrentModule bracketTable V) {N : ℕ}
    (x : Variables N) : operatorEval R N (MvPolynomial.X x) = colorOp R x := by
  simp [operatorEval, colorIn]

/-- Apply the polynomial current operator to the actual cyclic vector. -/
def vectorEval (R : CurrentModule bracketTable V) (w : V) (N : ℕ) :
    MvPolynomial (Variables N) ℂ →ₗ[ℂ] V where
  toFun p := operatorEval R N p w
  map_add' p q := by simp
  map_smul' c p := by simp

@[simp] theorem vectorEval_one (R : CurrentModule bracketTable V) (w : V) (N : ℕ) :
    vectorEval R w N 1 = w := by simp [vectorEval]

@[simp] theorem vectorEval_X_mul (R : CurrentModule bracketTable V) (w : V) {N : ℕ}
    (x : Variables N) (p : MvPolynomial (Variables N) ℂ) :
    vectorEval R w N (MvPolynomial.X x * p) = colorOp R x (vectorEval R w N p) := by
  simp [vectorEval, Module.End.mul_apply]

theorem word_mem (R : CurrentModule bracketTable V) (w : V)
    (l : List (Fin 8 × ℕ)) : wordOp R l w ∈ CVRectSingle.cyclicSpan R w :=
  Submodule.subset_span ⟨l, rfl⟩

theorem cyclicSpan_inv (R : CurrentModule bracketTable V) (w : V) (c : Fin 8) (s : ℕ) :
    CVRectSingle.cyclicSpan R w ≤ (CVRectSingle.cyclicSpan R w).comap (R.op c s) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact word_mem R w ((c, s) :: l)

theorem vectorEval_mem (R : CurrentModule bracketTable V) (w : V) (N : ℕ)
    (p : MvPolynomial (Variables N) ℂ) :
    vectorEval R w N p ∈ CVRectSingle.cyclicSpan R w := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      change operatorEval R N (MvPolynomial.C c) w ∈ CVRectSingle.cyclicSpan R w
      simpa using (CVRectSingle.cyclicSpan R w).smul_mem c (word_mem R w [])
  | add p q hp hq =>
      change vectorEval R w N (p + q) ∈ _
      rw [map_add]
      exact (CVRectSingle.cyclicSpan R w).add_mem hp hq
  | mul_X p x hp =>
      rw [mul_comm, vectorEval_X_mul]
      rcases x with ⟨b, i⟩
      cases b
      · exact cyclicSpan_inv R w 3 i hp
      · exact cyclicSpan_inv R w 5 i hp

theorem first_block_mem_range (R : CurrentModule bracketTable V) (w : V) {N : ℕ}
    (a b : List ℕ) (ha : ∀ s ∈ a, s < N) (hb : ∀ s ∈ b, s < N) :
    Fx R 3 a (Fx R 5 b w) ∈ LinearMap.range (vectorEval R w N) := by
  have htheta : Fx R 5 b w ∈ LinearMap.range (vectorEval R w N) := by
    induction b with
    | nil => exact ⟨1, vectorEval_one R w N⟩
    | cons s b ih =>
        obtain ⟨p, hp⟩ := ih (fun t ht => hb t (List.mem_cons_of_mem s ht))
        refine ⟨MvPolynomial.X (true, ⟨s, hb s List.mem_cons_self⟩) * p, ?_⟩
        simpa [colorOp, hp] using vectorEval_X_mul R w (true, ⟨s, hb s List.mem_cons_self⟩) p
  induction a with
  | nil => exact htheta
  | cons s a ih =>
      obtain ⟨p, hp⟩ := ih (fun t ht => ha t (List.mem_cons_of_mem s ht))
      refine ⟨MvPolynomial.X (false, ⟨s, ha s List.mem_cons_self⟩) * p, ?_⟩
      simpa [colorOp, hp] using vectorEval_X_mul R w (false, ⟨s, ha s List.mem_cons_self⟩) p

/-- The polynomial action reaches the whole actual one-orientation cyclic
submodule; no identification with an evaluation fusion model is used. -/
theorem vectorEval_range (R : CurrentModule bracketTable V) (w : V) {e n r : ℕ}
    (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) :
    LinearMap.range (vectorEval R w (r + n + e)) = CVRectSingle.cyclicSpan R w := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    exact vectorEval_mem R w _ p
  · change CVRectSingle.cyclicSpan R w ≤ _
    rw [CVRectCommutative.cyclicSpan_eq_colorSpan h]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, ha, hb, rfl⟩
    exact first_block_mem_range R w a b ha hb

/-- Commutative current polynomials annihilating the generator form an
actual ideal. Multiples are handled by multiplication of evaluated
operators; no invariance of a merely linear shift image is used. -/
def annihilatorIdeal (R : CurrentModule bracketTable V) (w : V) (N : ℕ) :
    Ideal (MvPolynomial (Variables N) ℂ) where
  carrier := {p | vectorEval R w N p = 0}
  zero_mem' := map_zero _
  add_mem' := by
    intro p q hp hq
    change vectorEval R w N (p + q) = 0
    rw [map_add, hp, hq, add_zero]
  smul_mem' := by
    intro p q hq
    change operatorEval R N (p * q) w = 0
    rw [map_mul, Module.End.mul_apply]
    change operatorEval R N p (vectorEval R w N q) = 0
    rw [hq, map_zero]

/-- Any actual coefficient ideal contained in the annihilator gives a
linear map from its quotient onto the cyclic image. -/
def quotientVectorEval (R : CurrentModule bracketTable V) (w : V) (N : ℕ)
    (J : Ideal (MvPolynomial (Variables N) ℂ)) (hJ : J ≤ annihilatorIdeal R w N) :
    (MvPolynomial (Variables N) ℂ ⧸ J.restrictScalars ℂ) →ₗ[ℂ] V :=
  (J.restrictScalars ℂ).liftQ (vectorEval R w N) (by
    intro p hp
    exact hJ hp)

theorem quotientVectorEval_range (R : CurrentModule bracketTable V) (w : V)
    {e n r : ℕ} (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0)
    (J : Ideal (MvPolynomial (Variables (r + n + e)) ℂ))
    (hJ : J ≤ annihilatorIdeal R w (r + n + e)) :
    LinearMap.range (quotientVectorEval R w (r + n + e) J hJ) =
      CVRectSingle.cyclicSpan R w := by
  rw [quotientVectorEval, Submodule.range_liftQ]
  exact vectorEval_range R w h

/-- A finite polynomial quotient upper bound transfers to the actual CV
cyclic module. The separate relation theorem must prove the displayed
ideal inclusion; this result assumes neither a fusion isomorphism nor an
upper bound on the actual module. -/
theorem cyclicSpan_bound_of_ideal (R : CurrentModule bracketTable V) (w : V)
    {e n r : ℕ} (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0)
    (J : Ideal (MvPolynomial (Variables (r + n + e)) ℂ))
    (hJ : J ≤ annihilatorIdeal R w (r + n + e))
    [FiniteDimensional ℂ (MvPolynomial (Variables (r + n + e)) ℂ ⧸ J.restrictScalars ℂ)] :
    FiniteDimensional ℂ (CVRectSingle.cyclicSpan R w) ∧
      Module.finrank ℂ (CVRectSingle.cyclicSpan R w) ≤
        Module.finrank ℂ (MvPolynomial (Variables (r + n + e)) ℂ ⧸ J.restrictScalars ℂ) := by
  have he := quotientVectorEval_range R w h J hJ
  haveI : FiniteDimensional ℂ (CVRectSingle.cyclicSpan R w) := by
    rw [← he]
    infer_instance
  refine ⟨inferInstance, ?_⟩
  have hb := LinearMap.finrank_range_le (quotientVectorEval R w (r + n + e) J hJ)
  rwa [he] at hb

end

end VOA.DeligneAudit.A2.CVRectPolynomial

#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.operatorEval
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.vectorEval_range
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.quotientVectorEval_range
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.cyclicSpan_bound_of_ideal
