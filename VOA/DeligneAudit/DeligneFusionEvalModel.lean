import VOA.DeligneAudit.DeligneFusionGrFilt

/-!
# The evaluation model and `DemazureRealization N` (U7) without CL-V

`T_N = (Site → Fin 3) → ℂ` with `Site = Fin N ⊕ Fin N`: `N` sites carry the standard representation `ω₁`
(the generator matrices `matT`, brackets = `bracketTable` by `matT_bracket`), `N` sites carry its dual `ω₂`
(`x ↦ −xᵀ`).  The current `x ⊗ tᵏ` acts by `Σᵢ zᵢᵏ x⁽ⁱ⁾` at the distinct points `zᵢ` (`evalRep`).  The tensor
product `w₀` of the highest-weight vectors satisfies the filtered relations of `M_{N,0}` (`filtRel_w0`):
truncations by the vanishing polynomial `∏(t − zᵢ)` (`vand`), `f^{N+1}` by `sl₂` theory and nilpotency.
Lagrange interpolation isolates single sites, so `w₀` is cyclic in bounded degree (`Fle_top`) and
`dim = 3^{2N} = 9^N`.  With `demazureRealization_of_filt`:

**`demazureRealization_all : ∀ N, A2.DemazureRealization N`**, i.e. U7, with no appeal to CL-V.
-/

namespace VOA.DeligneAudit.EvalModel

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.GrFilt

noncomputable section

/-! ## The generator matrices -/

/-- Explicit generator matrices (`e₁, e₂, e_θ, f₁, f₂, f_θ, h₁, h₂`). -/
def matT : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![Matrix.single 0 1 1, Matrix.single 1 2 1, Matrix.single 0 2 1, Matrix.single 1 0 1,
    Matrix.single 2 1 1, Matrix.single 2 0 1, Matrix.single 0 0 1 - Matrix.single 1 1 1,
    Matrix.single 1 1 1 - Matrix.single 2 2 1]

theorem mat_eq (c : Fin 8) : (generator c).val = matT c := by
  fin_cases c <;> rfl

theorem matT_bracket (a b : Fin 8) :
    matT a * matT b - matT b * matT a = ∑ e, bracketTable a b e • matT e := by
  have h := congrArg Subtype.val (generator_bracket a b)
  simp only [LieSubalgebra.coe_bracket, Ring.lie_def] at h
  simp only [← mat_eq]
  rw [h]
  simp [structureConstant_eq_table]

/-! ## Sites, the local action, and the model -/

variable (N : ℕ)

abbrev Site := Fin N ⊕ Fin N
abbrev Cfg := Site N → Fin 3
abbrev TT := Cfg N → ℂ

/-- The representation matrix at a site (`ω₁` on the left sites, `ω₂ = ω₁*` on the right ones). -/
def R : Site N → Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | .inl _, c => matT c
  | .inr _, c => -(Matrix.transpose (matT c))

theorem R_bracket (i : Site N) (a b : Fin 8) :
    R N i a * R N i b - R N i b * R N i a = ∑ e, bracketTable a b e • R N i e := by
  rcases i with i | i
  · exact matT_bracket a b
  · simp only [R, neg_mul_neg]
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_sub,
      show matT b * matT a - matT a * matT b = -(matT a * matT b - matT b * matT a) by abel,
      matT_bracket, Matrix.transpose_neg, Matrix.transpose_sum]
    simp [Finset.sum_neg_distrib, Matrix.transpose_smul]

/-- The evaluation points. -/
def z : Site N → ℂ
  | .inl i => ((i : ℕ) : ℂ)
  | .inr i => ((N + i : ℕ) : ℂ)

theorem z_injective : Function.Injective (z N) := by
  rintro (i | i) (j | j) h <;> simp only [z, Nat.cast_inj] at h
  · exact congrArg _ (Fin.ext h)
  · have := i.isLt; omega
  · have := j.isLt; omega
  · exact congrArg _ (Fin.ext (by omega))

variable {N}

/-- The action of a matrix at site `i`. -/
def loc (i : Site N) (X : Matrix (Fin 3) (Fin 3) ℂ) : Module.End ℂ (TT N) where
  toFun f γ := ∑ k, X (γ i) k * f (Function.update γ i k)
  map_add' f g := by ext γ; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext γ; simp [Finset.mul_sum, mul_left_comm]

theorem loc_apply (i : Site N) (X : Matrix (Fin 3) (Fin 3) ℂ) (f : TT N) (γ : Cfg N) :
    loc i X f γ = ∑ k, X (γ i) k * f (Function.update γ i k) := rfl

theorem loc_mul (i : Site N) (X Y : Matrix (Fin 3) (Fin 3) ℂ) : loc i X * loc i Y = loc i (X * Y) := by
  refine LinearMap.ext fun f => funext fun γ => ?_
  simp only [Module.End.mul_apply, loc_apply, Function.update_self, Function.update_idem,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem loc_comm {i j : Site N} (hij : i ≠ j) (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    loc i X * loc j Y = loc j Y * loc i X := by
  refine LinearMap.ext fun f => funext fun γ => ?_
  simp only [Module.End.mul_apply, loc_apply, Function.update_of_ne hij.symm,
    Function.update_of_ne hij, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Function.update_comm hij]; ring

theorem loc_sub (i : Site N) (X Y : Matrix (Fin 3) (Fin 3) ℂ) : loc i (X - Y) = loc i X - loc i Y := by
  refine LinearMap.ext fun f => funext fun γ => ?_; simp [loc_apply, sub_mul, Finset.sum_sub_distrib]

theorem loc_sum_smul (i : Site N) (c : Fin 8 → ℂ) (X : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) :
    loc i (∑ e, c e • X e) = ∑ e, c e • loc i (X e) := by
  refine LinearMap.ext fun f => funext fun γ => ?_
  simp only [loc_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun k _ => by ring

theorem loc_zero (i : Site N) : loc i (0 : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
  refine LinearMap.ext fun f => funext fun γ => ?_; simp [loc_apply]

variable (N)

/-- The current operator `x_c ⊗ tᵏ`. -/
def op (c : Fin 8) (k : ℕ) : Module.End ℂ (TT N) := ∑ i, (z N i) ^ k • loc i (R N i c)

theorem op_comm (a b : Fin 8) (r s : ℕ) :
    op N a r * op N b s - op N b s * op N a r = ∑ e, bracketTable a b e • op N e (r + s) := by
  have key : ∀ i j : Site N, (z N i ^ r • loc i (R N i a)) * (z N j ^ s • loc j (R N j b)) -
      (z N j ^ s • loc j (R N j b)) * (z N i ^ r • loc i (R N i a)) =
      if i = j then z N i ^ (r + s) • ∑ e, bracketTable a b e • loc i (R N i e) else 0 := by
    intro i j
    rw [smul_mul_smul_comm, smul_mul_smul_comm]
    split_ifs with hij
    · subst hij
      rw [loc_mul, loc_mul, mul_comm (z N i ^ s), ← smul_sub, ← loc_sub, R_bracket, loc_sum_smul,
        pow_add]
    · rw [loc_comm hij, mul_comm (z N j ^ s), sub_self]
  have e1 : op N a r * op N b s - op N b s * op N a r = ∑ i, ∑ j,
      ((z N i ^ r • loc i (R N i a)) * (z N j ^ s • loc j (R N j b)) -
        (z N j ^ s • loc j (R N j b)) * (z N i ^ r • loc i (R N i a))) := by
    simp only [op, Finset.sum_mul_sum, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  rw [e1]
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [op, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => by rw [mul_comm]

/-- The evaluation model. -/
def evalRep : CurrentModule (bracketTable) (TT N) where
  op := op N
  comm a b r s v := by
    have := congrArg (fun T => T v) (op_comm N a b r s)
    simpa [Module.End.mul_apply, LinearMap.sub_apply] using this

@[simp] theorem evalRep_op (c : Fin 8) (k : ℕ) : (evalRep N).op c k = op N c k := rfl

/-! ## Basis vectors and the highest-weight vector -/

/-- The basis vector of a configuration. -/
def δ (β : Cfg N) : TT N := fun γ => if γ = β then 1 else 0

variable {N}

theorem loc_delta (i : Site N) (X : Matrix (Fin 3) (Fin 3) ℂ) (β : Cfg N) :
    loc i X (δ N β) = ∑ a, X a (β i) • δ N (Function.update β i a) := by
  funext γ
  simp only [loc_apply, δ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have h1 : ∀ k, (Function.update γ i k = β) ↔ (k = β i ∧ ∀ j ≠ i, γ j = β j) := fun k =>
    Function.update_eq_iff
  have h2 : ∀ a, (γ = Function.update β i a) ↔ (γ i = a ∧ ∀ j ≠ i, γ j = β j) := fun a =>
    Function.eq_update_iff
  simp only [h1, h2]
  by_cases hγ : ∀ j ≠ i, γ j = β j
  · simp only [iff_true_intro hγ, and_true]; rw [Finset.sum_ite_eq', Finset.sum_ite_eq]; simp
  · simp only [iff_false_intro hγ, and_false, if_false, Finset.sum_const_zero]

variable (N)

/-- The highest-weight configuration. -/
def β0 : Cfg N
  | .inl _ => 0
  | .inr _ => 2

/-- The highest-weight vector `w₀ = ⊗ (highest-weight vectors)`. -/
abbrev w0 : TT N := δ N (β0 N)

variable {N}

/-- The column of `R i c` at the highest-weight index. -/
theorem loc_w0 (i : Site N) (c : Fin 8) :
    loc i (R N i c) (w0 N) = ∑ a, R N i c a (β0 N i) • δ N (Function.update (β0 N) i a) :=
  loc_delta i _ _

theorem raise_col (i : Site N) (c : Fin 8) (hc : c.val < 3) (a : Fin 3) : R N i c a (β0 N i) = 0 := by
  have : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases i with i | i <;> rcases this with rfl | rfl | rfl <;> fin_cases a <;>
    simp [R, β0, matT]

theorem loc_raise (i : Site N) (c : Fin 8) (hc : c.val < 3) : loc i (R N i c) (w0 N) = 0 := by
  rw [loc_w0]; simp [raise_col i c hc]

/-- The Cartan eigenvalue at a site. -/
def dg (c : Fin 8) : Site N → ℂ
  | .inl _ => if c = 6 then 1 else 0
  | .inr _ => if c = 7 then 1 else 0

theorem loc_cartan (i : Site N) (c : Fin 8) (hc : 6 ≤ c.val) :
    loc i (R N i c) (w0 N) = dg c i • w0 N := by
  rw [loc_w0, Fin.sum_univ_three]
  have : c = 6 ∨ c = 7 := by omega
  rcases i with i | i <;> rcases this with rfl | rfl <;>
    simp [R, β0, matT, dg]
  all_goals exact congrArg (δ N) (Function.update_eq_self _ _)

variable (N)

theorem op_w0 (c : Fin 8) (k : ℕ) : op N c k (w0 N) = ∑ i, z N i ^ k • loc i (R N i c) (w0 N) := by
  simp [op, LinearMap.coe_sum, Finset.sum_apply]

/-! ## The truncations: the vanishing polynomial -/

/-- `Σᵢ xᵢⁿ uᵢ` (`n = |ι|`) lies in the span of `Σᵢ xᵢᵏ uᵢ`, `k < n`. -/
theorem vand {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V] (x : ι → ℂ) (u : ι → V) :
    ∑ i, x i ^ Fintype.card ι • u i ∈
      Submodule.span ℂ {v | ∃ k < Fintype.card ι, v = ∑ i, x i ^ k • u i} := by
  set n := Fintype.card ι
  rcases Nat.eq_zero_or_pos n with hn | hn
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp
  set Q : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (x i))
  have hQm : Q.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hQd : Q.natDegree = n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp [n]
  set P : Polynomial ℂ := Polynomial.X ^ n - Q
  have hdeg : P.degree < n := by
    have := Polynomial.degree_sub_lt (p := Polynomial.X ^ n) (q := Q) ?_ ?_ ?_
    · rwa [Polynomial.degree_X_pow] at this
    · rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hQm.ne_zero, hQd]
    · exact pow_ne_zero _ Polynomial.X_ne_zero
    · rw [Polynomial.leadingCoeff_X_pow, hQm.leadingCoeff]
  have hPd : P.natDegree < n := by
    by_cases hP : P = 0
    · rw [hP, Polynomial.natDegree_zero]; exact hn
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP).mpr hdeg
  have hev : ∀ i, x i ^ n = ∑ k ∈ Finset.range n, P.coeff k * x i ^ k := by
    intro i
    have h0 : Q.eval (x i) = 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have := Polynomial.eval_eq_sum_range' hPd (x i)
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, h0, sub_zero] at this
    exact this
  have : ∑ i, x i ^ n • u i = ∑ k ∈ Finset.range n, P.coeff k • ∑ i, x i ^ k • u i := by
    simp only [hev, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  rw [this]
  exact Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨k, Finset.mem_range.mp hk, rfl⟩)

/-! ## The filtered relations -/

theorem loc_col_zero (i : Site N) (c : Fin 8) (h : ∀ a, R N i c a (β0 N i) = 0) :
    loc i (R N i c) (w0 N) = 0 := by
  rw [loc_w0]; simp [h]

theorem opw_mem (c : Fin 8) {k d : ℕ} (hk : k < d) :
    op N c k (w0 N) ∈ Fbelow (evalRep N) (w0 N) d :=
  Submodule.subset_span ⟨[(c, k)], by simp [SectorGraded.wordDeg]; omega, rfl⟩

/-- A truncation from the vanishing polynomial. -/
theorem trunc_gen {ι : Type} [Fintype ι] (c : Fin 8) (x : ι → ℂ) (u : ι → TT N)
    (h : ∀ k, op N c k (w0 N) = ∑ i, x i ^ k • u i) :
    op N c (Fintype.card ι) (w0 N) ∈ Fbelow (evalRep N) (w0 N) (Fintype.card ι) := by
  rw [h]
  refine (Submodule.span_le.mpr ?_) (vand x u)
  rintro _ ⟨k, hk, rfl⟩
  rw [← h]
  exact opw_mem N c hk

theorem op_w0_left (c : Fin 8) (hc : ∀ j : Fin N, ∀ a, R N (.inr j) c a (β0 N (.inr j)) = 0) (k : ℕ) :
    op N c k (w0 N) = ∑ j : Fin N, z N (.inl j) ^ k • loc (.inl j) (R N (.inl j) c) (w0 N) := by
  rw [op_w0, Fintype.sum_sum_type]
  simp [loc_col_zero N _ _ (hc _)]

theorem op_w0_right (c : Fin 8) (hc : ∀ j : Fin N, ∀ a, R N (.inl j) c a (β0 N (.inl j)) = 0) (k : ℕ) :
    op N c k (w0 N) = ∑ j : Fin N, z N (.inr j) ^ k • loc (.inr j) (R N (.inr j) c) (w0 N) := by
  rw [op_w0, Fintype.sum_sum_type]
  simp [loc_col_zero N _ _ (hc _)]

theorem loc_sq_zero (i : Site N) (c : Fin 8) (hc : matT c * matT c = 0) :
    loc i (R N i c) ^ 2 = 0 := by
  rw [pow_two, loc_mul]
  rcases i with i | i
  · simp [R, hc, loc_zero]
  · simp only [R, neg_mul_neg, ← Matrix.transpose_mul, hc, Matrix.transpose_zero, loc_zero]

theorem op_nilpotent (c : Fin 8) (hc : matT c * matT c = 0) : IsNilpotent (op N c 0) := by
  simp only [op, pow_zero, one_smul]
  refine Commute.isNilpotent_sum (fun i _ => ⟨2, loc_sq_zero N i c hc⟩) fun i j _ _ => ?_
  by_cases hij : i = j
  · subst hij; exact Commute.refl _
  · exact loc_comm hij _ _

theorem op_cartan_w0 (c : Fin 8) (hc : 6 ≤ c.val) (k : ℕ) :
    op N c k (w0 N) = (∑ i, z N i ^ k * dg c i) • w0 N := by
  rw [op_w0, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [loc_cartan i c hc, smul_smul]

theorem sum_dg (c : Fin 8) (hc : 6 ≤ c.val) : ∑ i : Site N, dg c i = (N : ℂ) := by
  rw [Fintype.sum_sum_type]
  have : c = 6 ∨ c = 7 := by omega
  rcases this with rfl | rfl <;> simp [dg]

theorem hw_low (E F H : Fin 8) (hEF : ∀ x, op N E 0 (op N F 0 x) - op N F 0 (op N E 0 x) = op N H 0 x)
    (hHF : ∀ x, op N H 0 (op N F 0 x) - op N F 0 (op N H 0 x) = (-2 : ℂ) • op N F 0 x)
    (hE : op N E 0 (w0 N) = 0) (hH : op N H 0 (w0 N) = ((N : ℤ) : ℂ) • w0 N)
    (hF : matT F * matT F = 0) : (op N F 0)^[N + 1] (w0 N) = 0 := by
  obtain ⟨K, hK⟩ := op_nilpotent N F hF
  have hKw : (op N F 0)^[K] (w0 N) = 0 := by
    rw [← Module.End.pow_apply, hK, LinearMap.zero_apply]
  have := (CLFilt.hw_pow (op N E 0) (op N F 0) (op N H 0) hEF hHF hE hH K hKw).2 (by positivity)
  simpa using this

theorem comm0 (a b : Fin 8) (x : TT N) :
    op N a 0 (op N b 0 x) - op N b 0 (op N a 0 x) = ∑ e, bracketTable a b e • op N e 0 x := by
  have := congrArg (fun T => T x) (op_comm N a b 0 0)
  simpa [Module.End.mul_apply, LinearMap.sub_apply] using this

/-- **The filtered relations of `M_{N,0}`** for `w₀` in the evaluation model. -/
theorem filtRel_w0 : FiltRel (evalRep N) (w0 N) N where
  raising e he r := by
    simp only [evalRep_op, op_w0, loc_raise _ e he, smul_zero, Finset.sum_const_zero]
  cartan h h6 r := by
    simp only [evalRep_op]; rw [op_cartan_w0 N h h6 r]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  cartan_zero h h6 := by
    simp only [evalRep_op]; rw [op_cartan_w0 N h h6 0]; simp [sum_dg N h h6]
  lowering_f1 := by
    simp only [evalRep_op]
    refine hw_low N 0 3 6 (fun x => ?_) (fun x => ?_) ?_ ?_ (by simp [matT])
    · rw [comm0]; simp [Fin.sum_univ_eight, bracketTable]
    · rw [comm0]; simp [Fin.sum_univ_eight, bracketTable]
    · simp only [op_w0, loc_raise _ 0 (by decide), smul_zero, Finset.sum_const_zero]
    · rw [op_cartan_w0 N 6 (by decide) 0]; simp [sum_dg N 6 (by decide)]
  lowering_f2 := by
    simp only [evalRep_op]
    refine hw_low N 1 4 7 (fun x => ?_) (fun x => ?_) ?_ ?_ (by simp [matT])
    · rw [comm0]; simp [Fin.sum_univ_eight, bracketTable]
    · rw [comm0]; simp [Fin.sum_univ_eight, bracketTable]
    · simp only [op_w0, loc_raise _ 1 (by decide), smul_zero, Finset.sum_const_zero]
    · rw [op_cartan_w0 N 7 (by decide) 0]; simp [sum_dg N 7 (by decide)]
  trunc_f1 := by
    have := trunc_gen N 3 _ _ (op_w0_left N 3 (fun j a => by fin_cases a <;> simp [R, β0, matT]))
    simpa using this
  trunc_f2 := by
    have := trunc_gen N 4 _ _ (op_w0_right N 4 (fun j a => by fin_cases a <;> simp [R, β0, matT]))
    simpa using this
  trunc_theta := by
    have := trunc_gen N 5 (z N) (fun i => loc i (R N i 5) (w0 N)) (op_w0 N 5)
    simpa [two_mul] using this

/-! ## Cyclicity: Lagrange interpolation isolates a site -/

theorem card_site : Fintype.card (Site N) = N + N := by simp

/-- `x⁽ʲ⁾` at a single site is a combination of the currents `x ⊗ tᵏ`, `k < 2N`. -/
theorem loc_eq_sum (j : Site N) (c : Fin 8) :
    loc j (R N j c) = ∑ k ∈ Finset.range (N + N),
      (Lagrange.basis Finset.univ (z N) j).coeff k • op N c k := by
  set P := Lagrange.basis Finset.univ (z N) j
  have hinj : Set.InjOn (z N) (Finset.univ : Finset (Site N)) := (z_injective N).injOn
  have hPd : P.natDegree < N + N := by
    rw [Lagrange.natDegree_basis hinj (Finset.mem_univ j), Finset.card_univ, card_site]
    have : 0 < N + N := by
      rcases j with j | j <;> have := j.isLt <;> omega
    omega
  have hev : ∀ i, P.eval (z N i) = if i = j then 1 else 0 := by
    intro i
    split_ifs with h
    · subst h; exact Lagrange.eval_basis_self hinj (Finset.mem_univ _)
    · exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)
  simp only [op, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ k ∈ Finset.range (N + N), (P.coeff k * z N i ^ k) • loc i (R N i c) =
      (if i = j then (1 : ℂ) else 0) • loc i (R N i c) := by
    intro i
    rw [← Finset.sum_smul, ← hev i, Polynomial.eval_eq_sum_range' hPd]
  simp only [this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem Fle_op (c : Fin 8) {k d : ℕ} (hk : k < N + N) {v : TT N}
    (hv : v ∈ Fle (evalRep N) (w0 N) d) : op N c k v ∈ Fle (evalRep N) (w0 N) (d + (N + N)) := by
  have := Fbelow_op (evalRep N) (w0 N) c k (d + 1) hv
  exact Fbelow_mono (evalRep N) (w0 N) (by omega) this

theorem Fle_loc (j : Site N) (c : Fin 8) {d : ℕ} {v : TT N} (hv : v ∈ Fle (evalRep N) (w0 N) d) :
    loc j (R N j c) v ∈ Fle (evalRep N) (w0 N) (d + (N + N)) := by
  rw [loc_eq_sum, LinearMap.coe_sum, Finset.sum_apply]
  exact Submodule.sum_mem _ fun k hk => by
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Fle_op N c (Finset.mem_range.mp hk) hv)

/-- One lowering step at a site. -/
theorem step_vec (j : Site N) (b : Fin 3) (β' : Cfg N) (hβ' : β' j = β0 N j) (hb : b ≠ β0 N j) :
    ∃ c, ∃ sgn : ℂ, sgn ≠ 0 ∧ loc j (R N j c) (δ N β') = sgn • δ N (Function.update β' j b) := by
  rcases j with i | i
  · fin_cases b
    · exact absurd rfl hb
    · refine ⟨3, 1, one_ne_zero, ?_⟩
      rw [loc_delta, hβ', Fin.sum_univ_three]; simp [R, matT, β0]
    · refine ⟨5, 1, one_ne_zero, ?_⟩
      rw [loc_delta, hβ', Fin.sum_univ_three]; simp [R, matT, β0]
  · fin_cases b
    · refine ⟨5, -1, by norm_num, ?_⟩
      rw [loc_delta, hβ', Fin.sum_univ_three]; simp [R, matT, β0]
    · refine ⟨4, -1, by norm_num, ?_⟩
      rw [loc_delta, hβ', Fin.sum_univ_three]; simp [R, matT, β0]
    · exact absurd rfl hb

theorem w0_mem : w0 N ∈ Fle (evalRep N) (w0 N) 0 :=
  Submodule.subset_span ⟨[], by simp [SectorGraded.wordDeg], rfl⟩

/-- Every basis vector is reached in bounded degree. -/
theorem reach (β : Cfg N) : ∀ T : Finset (Site N),
    δ N (fun i => if i ∈ T then β i else β0 N i) ∈ Fle (evalRep N) (w0 N) (T.card * (N + N)) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.card_empty, zero_mul]
      exact w0_mem N
  | insert j T hj ih =>
      set β' : Cfg N := fun i => if i ∈ T then β i else β0 N i
      have hnew : (fun i => if i ∈ insert j T then β i else β0 N i) = Function.update β' j (β j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [Finset.mem_insert, hij, β', Function.update_of_ne hij]
      have hβ' : β' j = β0 N j := by simp [β', hj]
      rw [hnew, Finset.card_insert_of_notMem hj, add_mul, one_mul]
      by_cases hb : β j = β0 N j
      · rw [hb, ← hβ', Function.update_eq_self]
        exact Fbelow_mono (evalRep N) (w0 N) (by omega) ih
      · obtain ⟨c, sgn, hs, he⟩ := step_vec N j (β j) β' hβ' hb
        have : δ N (Function.update β' j (β j)) = sgn⁻¹ • loc j (R N j c) (δ N β') := by
          rw [he, smul_smul, inv_mul_cancel₀ hs, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Fle_loc N j c ih)

theorem Fle_top : Fle (evalRep N) (w0 N) (Fintype.card (Site N) * (N + N)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hf : f = ∑ β : Cfg N, f β • δ N β := by
    funext γ
    simp [δ, Finset.sum_apply]
  rw [hf]
  refine Submodule.sum_mem _ fun β _ => Submodule.smul_mem _ _ ?_
  have := reach N β Finset.univ
  simpa using this

/-- **U7 without CL-V**: `DemazureRealization N` for every `N`. -/
theorem demazureRealization_all (N : ℕ) : A2.DemazureRealization N := by
  refine demazureRealization_of_filt (evalRep N) (w0 N) (filtRel_w0 N)
    (Fintype.card (Site N) * (N + N)) ?_
  rw [Fle_top, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fun, card_site,
    Fintype.card_fin, ← two_mul, pow_mul]
  norm_num

end

end VOA.DeligneAudit.EvalModel

section AxiomAudit
#print axioms VOA.DeligneAudit.EvalModel.filtRel_w0
#print axioms VOA.DeligneAudit.EvalModel.demazureRealization_all
end AxiomAudit
