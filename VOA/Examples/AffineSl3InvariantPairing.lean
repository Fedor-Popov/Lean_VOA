import VOA.Examples.AffineSl3BracketTable

/-!
# Uniqueness of the actual sl3 invariant pairing

Both Cartan weights eliminate pairings of nonopposite roots. Nine explicit
invariance equations identify the surviving root and Cartan entries with
one value. The codomain may be any complex vector space, and symmetry is
a conclusion rather than an assumption.
-/
namespace VOA.AffineSl3
noncomputable section
set_option maxHeartbeats 2000000
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Cartan invariance forces a pairing to vanish whenever the sum of
one of its two Cartan weights is nonzero. -/
theorem invariant_pairing_weight_zero (B : Sl3 →ₗ[ℂ] Sl3 →ₗ[ℂ] V)
    (hinv : ∀ (a x y : Sl3), B ⁅a,x⁆ y+B x ⁅a,y⁆=0) (i j : Fin 8)
    (hw : weight1 i+weight1 j≠0 ∨ weight2 i+weight2 j≠0) :
    B (generator i) (generator j)=0 := by
  have w1 := hinv h1 (generator i) (generator j)
  have w2 := hinv h2 (generator i) (generator j)
  simp only [h1_generator,h2_generator,map_smul,LinearMap.smul_apply,
    ← add_smul] at w1 w2
  rcases hw with hw | hw
  · exact (smul_eq_zero.mp w1).resolve_left (by exact_mod_cast hw)
  · exact (smul_eq_zero.mp w2).resolve_left (by exact_mod_cast hw)

/-- The complete matrix of an invariant vector-valued pairing is the
actual trace matrix times its value on the first opposite-root pair. -/
theorem invariant_pairing_basis (B : Sl3 →ₗ[ℂ] Sl3 →ₗ[ℂ] V)
    (hinv : ∀ (a x y : Sl3), B ⁅a,x⁆ y+B x ⁅a,y⁆=0) (i j : Fin 8) :
    B (generator i) (generator j)=formTable i j • B (generator 0) (generator 3) := by
  have h063 := hinv (generator 0) (generator 6) (generator 3)
  have h036 := hinv (generator 0) (generator 3) (generator 6)
  have h037 := hinv (generator 0) (generator 3) (generator 7)
  have h073 := hinv (generator 0) (generator 7) (generator 3)
  have h164 := hinv (generator 1) (generator 6) (generator 4)
  have h146 := hinv (generator 1) (generator 4) (generator 6)
  have h174 := hinv (generator 1) (generator 7) (generator 4)
  have h265 := hinv (generator 2) (generator 6) (generator 5)
  have h256 := hinv (generator 2) (generator 5) (generator 6)
  simp only [generator_bracket,structureConstant_eq_table,
    show bracketTable 0 6 = ![-2,0,0,0,0,0,0,0] from rfl,
    show bracketTable 0 3 = ![0,0,0,0,0,0,1,0] from rfl,
    show bracketTable 0 7 = ![1,0,0,0,0,0,0,0] from rfl,
    show bracketTable 1 6 = ![0,1,0,0,0,0,0,0] from rfl,
    show bracketTable 1 4 = ![0,0,0,0,0,0,0,1] from rfl,
    show bracketTable 1 7 = ![0,-2,0,0,0,0,0,0] from rfl,
    show bracketTable 2 6 = ![0,0,-1,0,0,0,0,0] from rfl,
    show bracketTable 2 5 = ![0,0,0,0,0,0,1,1] from rfl] at h063 h036 h037 h073 h164 h146 h174 h265 h256
  norm_num only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
    Fin.reduceFinMk,Fin.sum_univ_zero,zero_smul,one_smul,neg_smul,add_zero,zero_add,
    map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,map_neg,
    LinearMap.neg_apply] at h063 h036 h037 h073 h164 h146 h174 h265 h256
  change -((2:ℂ) • B (generator 0) (generator 3))+B (generator 6) (generator 6)=0 at h063
  change B (generator 6) (generator 6)+-((2:ℂ) • B (generator 3) (generator 0))=0 at h036
  change B (generator 6) (generator 7)+B (generator 3) (generator 0)=0 at h037
  change B (generator 0) (generator 3)+B (generator 7) (generator 6)=0 at h073
  change B (generator 1) (generator 4)+B (generator 6) (generator 7)=0 at h164
  change B (generator 7) (generator 6)+B (generator 4) (generator 1)=0 at h146
  change -((2:ℂ) • B (generator 1) (generator 4))+B (generator 7) (generator 7)=0 at h174
  change -B (generator 2) (generator 5)+(B (generator 6) (generator 6)+B (generator 6) (generator 7))=0 at h265
  change B (generator 6) (generator 6)+B (generator 7) (generator 6)+-B (generator 5) (generator 2)=0 at h256
  have b66 : B (generator 6) (generator 6)=(2:ℂ) • B (generator 0) (generator 3) := by
    linear_combination (norm := module) h063
  have b30 : B (generator 3) (generator 0)=B (generator 0) (generator 3) := by
    linear_combination (norm := module) (1/2:ℂ) • h063 - (1/2:ℂ) • h036
  have b67 : B (generator 6) (generator 7)=-(B (generator 0) (generator 3)) := by
    linear_combination (norm := module) h037-b30
  have b76 : B (generator 7) (generator 6)=-(B (generator 0) (generator 3)) := by
    linear_combination (norm := module) h073
  have b14 : B (generator 1) (generator 4)=B (generator 0) (generator 3) := by
    linear_combination (norm := module) h164-b67
  have b41 : B (generator 4) (generator 1)=B (generator 0) (generator 3) := by
    linear_combination (norm := module) h146-b76
  have b77 : B (generator 7) (generator 7)=(2:ℂ) • B (generator 0) (generator 3) := by
    linear_combination (norm := module) h174+(2:ℂ) • b14
  have b25 : B (generator 2) (generator 5)=B (generator 0) (generator 3) := by
    linear_combination (norm := module) -h265+b66+b67
  have b52 : B (generator 5) (generator 2)=B (generator 0) (generator 3) := by
    linear_combination (norm := module) -h256+b66+b76
  fin_cases i <;> fin_cases j <;>
    norm_num [formTable] <;>
    first
    | exact invariant_pairing_weight_zero B hinv _ _ (by norm_num [weight1,weight2])
    | assumption
    | rfl

/-- The coordinate basis consists of the specified Chevalley generators,
so its abstract basis extensionality can be applied to the finite matrix table. -/
theorem chevalleyBasis_apply (i : Fin 8) : chevalleyBasis i=generator i := by
  apply coordinateEquiv.injective
  simp only [chevalleyBasis,Module.Basis.coe_ofEquivFun,LinearEquiv.apply_symm_apply]
  change Pi.single i (1:ℂ)=coordinates (generator i)
  rw [coordinates_generator]


/-- Bilinearity extends the finite matrix calculation to every pair of
actual trace-zero matrices. The unique coefficient is B(e1,f1). -/
theorem invariant_pairing (B : Sl3 →ₗ[ℂ] Sl3 →ₗ[ℂ] V)
    (hinv : ∀ (a x y : Sl3), B ⁅a,x⁆ y+B x ⁅a,y⁆=0) (x y : Sl3) :
    B x y=form x y • B (generator 0) (generator 3) := by
  let C := form.compr₂ (LinearMap.toSpanSingleton ℂ V (B (generator 0) (generator 3)))
  have heq : B=C := by
    apply chevalleyBasis.ext
    intro i
    apply chevalleyBasis.ext
    intro j
    change B (chevalleyBasis i) (chevalleyBasis j)=
      form (chevalleyBasis i) (chevalleyBasis j) • B (generator 0) (generator 3)
    simpa only [chevalleyBasis_apply,form_generator_eq_table] using
      invariant_pairing_basis B hinv i j
  exact congrArg (fun F : Sl3 →ₗ[ℂ] Sl3 →ₗ[ℂ] V => F x y) heq

end
end VOA.AffineSl3
