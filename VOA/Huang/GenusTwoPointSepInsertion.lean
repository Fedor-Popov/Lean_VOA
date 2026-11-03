import VOA.Huang.GenusTwoPointSepDescent

/-!
# Inserting a vertex mode into an actual two-intertwiner trace

The Jacobi iterate formula is passed through a finite-dimensional trace using
a cutoff uniform on the traced weight space. This supplies the raw insertion
side of the Ward calculation, including the minus-two mode. It does not
identify plane-coordinate modes with geometrically modified insertion modes.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA Module
open scoped BigOperators
universe u
variable {V E₁ E₂ M K : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E₁] [Module ℂ E₁] [AddCommGroup E₂] [Module ℂ E₂]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup K] [Module ℂ K]
  {W : VertexOperatorAlgebra V}
  {A₁ : OrdVModule W E₁} {A₂ : OrdVModule W E₂}
  {N : OrdVModule W M} {Q : OrdVModule W K}

/-- Rectangular intertwiner truncation uniformly on one source weight space.
Boundedness below of the target is sufficient. -/
theorem rectangular_eventually_zero_on_weight
    (Y : IntertwiningOperator A₁ Q N) {α : ℂ} {w : E₁}
    (hw : w ∈ A₁.weight α) (β b : ℂ) :
    ∃ I : ℤ, ∀ i : ℤ, I ≤ i → ∀ x ∈ Q.weight β, Y.val (b + i) w x = 0 := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  obtain ⟨I, hI⟩ := exists_int_gt (α.re + β.re - b.re - 1 - B)
  refine ⟨I, fun i hi x hx => ?_⟩
  have hm := FusionTop.mem_weight Y.property hw hx (b + i)
  have hb : N.weight (α + β - (b + i) - 1) = ⊥ := by
    by_contra hn
    have h := hB _ hn
    have hi' : (I : ℝ) ≤ i := by exact_mod_cast hi
    simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at h
    linarith
  simpa only [hb, Submodule.mem_bot] using hm

/-- Agreement only on the traced weight space is enough; the operators need
not agree on the whole ordinary module. -/
theorem gradedTraceOp_congr_on_weight (N : OrdVModule W M)
    (S T : Module.End ℂ M) (e : ℂ)
    (h : ∀ x ∈ N.weight (e + W.centralCharge / 24), S x = T x) :
    gradedTraceOp N S e = gradedTraceOp N T e := by
  have he : weightBlock N S (e + W.centralCharge / 24) =
      weightBlock N T (e + W.centralCharge / 24) := by
    ext x
    change ((internalProjTo N.isInternal _) (S x) : M) =
      ((internalProjTo N.isInternal _) (T x) : M)
    rw [h x x.property]
  change LinearMap.trace ℂ _ (weightBlock N S _) = LinearMap.trace ℂ _ (weightBlock N T _)
  rw [he]

/-- Both normal-order tails truncate at one bound for the entire traced
weight space. The bound may depend on that weight; no joint estimate is inferred. -/
theorem product_insertion_cutoff
    (Y₁ : IntertwiningOperator A₁ Q N) (Y₂ : IntertwiningOperator A₂ N Q)
    {α₁ α₂ : ℂ} {w₁ : E₁} {w₂ : E₂}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (a : V) (n₁ n₂ β : ℂ) :
    ∃ I : ℕ, ∀ i : ℤ, I ≤ i → ∀ x ∈ N.weight β,
      Y₁.val (n₁ + i) w₁ (Y₂.val n₂ w₂ x) = 0 ∧
        mode (Q.YM a) i (Y₂.val n₂ w₂ x) = 0 := by
  obtain ⟨I, hI⟩ := rectangular_eventually_zero_on_weight Y₁ h₁
    (α₂ + β - n₂ - 1) n₁
  obtain ⟨J, hJ⟩ := mode_eventually_zero_on_weight Q a (α₂ + β - n₂ - 1)
  refine ⟨(max I J).toNat, fun i hi x hx => ?_⟩
  have hm := FusionTop.mem_weight Y₂.property h₂ hx n₂
  exact ⟨hI i (by omega) _ hm, hJ i (by omega) _ hm⟩

/-- Jacobi insertion inside the actual trace, for every integer mode ell.
In particular ell=-2 is the left-hand insertion of the desired descent law.
The right-hand side still contains raw three-mode traces awaiting geometric
conjugation, q-transport, and elliptic coefficient collection. -/
theorem trace_product_mode_iterate
    (Y₁ : IntertwiningOperator A₁ Q N) (Y₂ : IntertwiningOperator A₂ N Q)
    {α₁ α₂ : ℂ} {w₁ : E₁} {w₂ : E₂}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (a : V) (ell : ℤ) (n₁ n₂ e : ℂ) :
    ∃ I : ℕ, productModeTrace Y₁ Y₂ (mode (A₁.YM a) ell w₁) w₂ n₁ n₂ e =
      ∑ i ∈ Finset.range I, (negOnePow i * cbz ell i) *
        (gradedTraceOp N
            (mode (N.YM a) (ell - i) * ((Y₁.val (n₁ + i) w₁).comp (Y₂.val n₂ w₂))) e -
          negOnePow ell * gradedTraceOp N
            ((Y₁.val (ell + n₁ - i) w₁).comp
              ((mode (Q.YM a) i).comp (Y₂.val n₂ w₂))) e) := by
  obtain ⟨I, hI⟩ := product_insertion_cutoff Y₁ Y₂ h₁ h₂ a n₁ n₂
    (e + W.centralCharge / 24)
  let T : ℕ → Module.End ℂ M := fun i =>
    (negOnePow i * cbz ell i) •
      (mode (N.YM a) (ell - i) * ((Y₁.val (n₁ + i) w₁).comp (Y₂.val n₂ w₂)) -
        negOnePow ell • (Y₁.val (ell + n₁ - i) w₁).comp
          ((mode (Q.YM a) i).comp (Y₂.val n₂ w₂)))
  have he : gradedTraceOp N
      ((Y₁.val n₁ (mode (A₁.YM a) ell w₁)).comp (Y₂.val n₂ w₂)) e =
        gradedTraceOp N (∑ i ∈ Finset.range I, T i) e := by
    apply gradedTraceOp_congr_on_weight
    intro x hx
    have h := HuangODEModes.iterate_range Y₁.property a w₁ (Y₂.val n₂ w₂ x) ell n₁ I
      (fun i hi => hI i hi x hx)
    simpa only [T, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.mul_apply] using h
  refine ⟨I, ?_⟩
  change gradedTraceOp N _ e = _
  rw [he, ← gradedTraceAt_apply, map_sum]
  simp only [T, map_smul, map_sub, gradedTraceAt_apply, smul_eq_mul]

end VOA.Huang.GenusTwoPoint.Separate
