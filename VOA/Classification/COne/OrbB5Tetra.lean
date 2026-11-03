import VOA.Classification.COne.OrbZhuParity
import VOA.Classification.COne.OrbPosLowest

/-! # Tetrahedral weight positivity reduced to the zero-weight case

The proved degree-13 Zhu relation controls every realized lowest weight, not
only the constructed character table. No DRX premise, Zhu dimension bound,
odd annihilator, rationality, or twisted-sector exhaustion is used here.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbB5
open VOA Polynomial OrbZhu OrbPos

section General
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Evaluating a conformal Zhu polynomial on an actual nonzero bottom space
evaluates the scalar polynomial at its lowest weight. -/
theorem conformalPolynomial_bottom (N : OrdVModule W M) {h : ℂ}
    (hl : IsLowestWeight N h) (P : ℂ[X]) :
    actA N hl ((aeval (omegaL W) P) (mk W W.vacuum)) =
      P.eval h • (1 : Module.End ℂ (N.weight h)) := by
  have hw : actA N hl (mk W W.conformalVector) =
      h • (1 : Module.End ℂ (N.weight h)) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((actA N hl (mk W W.conformalVector) x : N.weight h) : M) = h • x.val
    rw [actA_mk_apply_coe, oMod_homogeneous N W.conformalVector_mem_grading_two]
    exact N.L0_weight h x.val x.property
  have hp (n : ℕ) : actA N hl ((omegaL W ^ n) (mk W W.vacuum)) =
      h ^ n • (1 : Module.End ℂ (N.weight h)) := by
    induction n with
    | zero => simpa only [pow_zero, Module.End.one_apply, one_smul] using actA_one N hl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change actA N hl (Amul (zhuRingData_holds W) (mk W W.conformalVector) _) = _
      rw [show actA N hl (Amul (zhuRingData_holds W) (mk W W.conformalVector)
          ((omegaL W ^ n) (mk W W.vacuum))) =
          actA N hl (mk W W.conformalVector) *
            actA N hl ((omegaL W ^ n) (mk W W.vacuum)) from
          actA_mul (zhuRingData_holds W) hl _ _, hw, ih, smul_mul_smul, one_mul,
        ← pow_succ']
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, LinearMap.add_apply, map_add, hP, hQ, eval_add, add_smul]
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hp, smul_smul, eval_monomial]

/-- A conformal Zhu relation constrains all realized lowest weights. -/
theorem lowestWeight_root_of_conformalPolynomial (N : OrdVModule W M) {h : ℂ}
    (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) (P : ℂ[X])
    (hP : (aeval (omegaL W) P) (mk W W.vacuum) = 0) : P.eval h = 0 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have he := congrArg (fun f : Module.End ℂ (N.weight h) => (f ⟨x, hx⟩).val)
    (conformalPolynomial_bottom N hl P)
  rw [hP, map_zero] at he
  have he' : P.eval h • x = 0 := he.symm
  exact (smul_eq_zero.mp he').resolve_right hx0

end General

/-- The explicit 13-root table is exhaustive for realized tetrahedral bottoms. -/
theorem tetra_lowestWeight_table {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wt M) {h : ℂ} (hl : IsLowestWeight N h)
    (hne : N.weight h ≠ ⊥) :
    (∃ i : Fin 8, h = (dblQ i : ℂ)) ∨ (∃ i : Fin 5, h = (sglQ i : ℂ)) := by
  have hp := lowestWeight_root_of_conformalPolynomial N hl hne (P8 * P5)
    q13_omega_eq_zero
  rw [eval_mul, P8, P5, eval_prod, eval_prod] at hp
  simp only [eval_sub, eval_X, eval_C] at hp
  rcases mul_eq_zero.mp hp with hp | hp
  · obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
    exact Or.inl ⟨i, sub_eq_zero.mp hi⟩
  · obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
    exact Or.inr ⟨i, sub_eq_zero.mp hi⟩

/-- Every realized bottom is zero or has the sharp table gap `1/36`. -/
theorem tetra_lowestWeight_zero_or_gap {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wt M) {h : ℂ} (hl : IsLowestWeight N h)
    (hne : N.weight h ≠ ⊥) : h = 0 ∨ (1 : ℝ) / 36 ≤ h.re := by
  rcases tetra_lowestWeight_table N hl hne with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · right
    fin_cases i <;> norm_num [dblQ]
  · fin_cases i <;> norm_num [sglQ]

/-- All weights of all irreducible tetrahedral modules are real and nonnegative. -/
theorem tetra_irreducible_weights_nonnegative {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wt M) (hi : N.IsIrreducible) {α : ℂ} (hα : N.weight α ≠ ⊥) :
    α.im = 0 ∧ 0 ≤ α.re := by
  obtain ⟨h, hl, hne⟩ := N.exists_isLowestWeight_of_irreducible hi
  obtain ⟨n, rfl⟩ := hl α hα
  have him : h.im = 0 := by
    rcases tetra_lowestWeight_table N hl hne with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp
  have hpos : 0 ≤ h.re := by
    rcases tetra_lowestWeight_zero_or_gap N hl hne with rfl | hh
    · simp
    · linarith
  simp only [Complex.add_im, Complex.natCast_im, him, add_zero, Complex.add_re,
    Complex.natCast_re, true_and]
  exact add_nonneg hpos n.cast_nonneg

/-- The remaining tetrahedral obligation concerns only realized weight zero. -/
def TetrahedralZeroWeightVacuum : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule Wt M),
    N.IsIrreducible → N.weight 0 ≠ ⊥ → Nonempty (ModuleEquiv Wt N (adjointModule Wt))

/-- The tetrahedral part of B5 is exactly vacuum uniqueness at zero. -/
theorem tetra_pseudoUnitary_iff_zeroWeightVacuum :
    PseudoUnitary Wt ↔ TetrahedralZeroWeightVacuum := by
  constructor
  · intro hp M _ _ N hi h0
    by_contra hn
    have hh := hp M N hi ⟨fun e => hn ⟨e⟩⟩ 0 h0
    norm_num at hh
  · intro hz
    apply (pseudoUnitary_iff_positiveLowestWeights Wt).mpr
    intro M _ _ N hi hn h hl hne
    rcases tetra_lowestWeight_zero_or_gap N hl hne with rfl | hh
    · obtain ⟨e⟩ := hz M N hi hne
      exact (hn.false e).elim
    · linarith

end VOA.Classification.COne.OrbB5
