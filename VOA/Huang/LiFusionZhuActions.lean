import VOA.Huang.LiFusionVacuum

/-! # Testing raw Zhu operations against every top datum

The left and right identities of `fzSpace` extend from homogeneous states to
linear state actions. `TopDataSeparate` isolates a remaining annihilator
statement: the common kernel of all top data is exactly `O(M)`. For a complete
irredundant simple family of a rational VOA this is a consequence of the
Frenkel–Zhu bimodule theorem and semisimplicity. It is not proved here.
-/
namespace VOA.Huang.LiFusion
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {P₂ P₃ : LWModule W}

/-- The homogeneous left operation, bundled in both variables. -/
noncomputable def leftAt (A : OrdVModule W M) (p : ℕ) : V →ₗ[ℂ] Module.End ℂ M :=
  ∑ i ∈ Finset.range (p + 1), cbz p i • (modeLinear ((i : ℤ) - 1)).comp A.YM

/-- The homogeneous right operation, including the vacuum-weight convention. -/
noncomputable def rightAt (A : OrdVModule W M) (p : ℕ) : V →ₗ[ℂ] Module.End ℂ M :=
  ∑ i ∈ Finset.range (p + 1), cbz ((p : ℤ) - 1) i •
    (modeLinear ((i : ℤ) - 1)).comp A.YM

@[simp] theorem leftAt_apply (p : ℕ) (a : V) (w : M) :
    leftAt A p a w = fzLeft A.toWeakModule p a w := by
  simp [leftAt, fzLeft, modeLinear]

@[simp] theorem rightAt_apply (p : ℕ) (a : V) (w : M) :
    rightAt A p a w = fzRight A.toWeakModule p a w := by
  simp [rightAt, fzRight, modeLinear]

noncomputable def rawLeft (A : OrdVModule W M) : V →ₗ[ℂ] Module.End ℂ M :=
  gradedExt W fun k => leftAt A k.toNat

noncomputable def rawRight (A : OrdVModule W M) : V →ₗ[ℂ] Module.End ℂ M :=
  gradedExt W fun k => rightAt A k.toNat

theorem rawLeft_homogeneous {p : ℕ} {a : V} (ha : a ∈ W.grading (p : ℤ)) (w : M) :
    rawLeft A a w = fzLeft A.toWeakModule p a w := by
  simp only [rawLeft, gradedExt_of_mem W _ ha, Int.toNat_natCast, leftAt_apply]

theorem rawRight_homogeneous {p : ℕ} {a : V} (ha : a ∈ W.grading (p : ℤ)) (w : M) :
    rawRight A a w = fzRight A.toWeakModule p a w := by
  simp only [rawRight, gradedExt_of_mem W _ ha, Int.toNat_natCast, rightAt_apply]

theorem fzSpace_left (T : fzSpace A P₂ P₃) {p : ℕ} {a : V}
    (ha : a ∈ W.grading (p : ℤ)) (w : M) :
    T.val (fzLeft A.toWeakModule p a w) =
      (rhoLW P₃.isMod P₃.h a).comp (T.val w) := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  rw [LinearMap.comp_apply, rhoLW_apply_coe, oMod_homogeneous _ ha]
  exact T.property.2.1 p a ha w y

/-- The right identity also holds at weight zero, by `V₀ = ℂ𝟙`. -/
theorem fzSpace_right (T : fzSpace A P₂ P₃) {p : ℕ} {a : V}
    (ha : a ∈ W.grading (p : ℤ)) (w : M) :
    T.val (fzRight A.toWeakModule p a w) =
      (T.val w).comp (rhoLW P₂.isMod P₂.h a) := by
  by_cases hp : 1 ≤ p
  · apply LinearMap.ext
    intro y
    exact T.property.2.2 p hp a ha w y (rhoLW P₂.isMod P₂.h a y)
      (by rw [rhoLW_apply_coe, oMod_homogeneous _ ha])
  · have hp0 : p = 0 := by omega
    subst p
    simp only [Nat.cast_zero] at ha
    rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    apply LinearMap.ext
    intro y
    have hv : fzRight A.toWeakModule 0 (c • W.vacuum) w = c • w := by
      simp only [fzRight, Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
        zero_sub, cbz_zero, one_smul, map_smul, mode_smul, LinearMap.smul_apply]
      rw [← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]
    rw [hv]
    simp [rhoLW_vacuum]

theorem fzSpace_rawLeft (T : fzSpace A P₂ P₃) (a : V) (w : M) :
    T.val (rawLeft A a w) = (rhoLW P₃.isMod P₃.h a).comp (T.val w) := by
  refine state_induction W (P := fun a =>
    T.val (rawLeft A a w) = (rhoLW P₃.isMod P₃.h a).comp (T.val w)) ?_ ?_ ?_ a
  · intro k a ha
    by_cases hk : k < 0
    · rw [W.positivity k hk, Submodule.mem_bot] at ha
      simp [ha]
    · have ha' : a ∈ W.grading (k.toNat : ℤ) := by rwa [Int.toNat_of_nonneg (by omega)]
      rw [rawLeft_homogeneous ha']
      exact fzSpace_left T ha' w
  · simp
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply, LinearMap.add_comp, ha, hb]

theorem fzSpace_rawRight (T : fzSpace A P₂ P₃) (a : V) (w : M) :
    T.val (rawRight A a w) = (T.val w).comp (rhoLW P₂.isMod P₂.h a) := by
  refine state_induction W (P := fun a =>
    T.val (rawRight A a w) = (T.val w).comp (rhoLW P₂.isMod P₂.h a)) ?_ ?_ ?_ a
  · intro k a ha
    by_cases hk : k < 0
    · rw [W.positivity k hk, Submodule.mem_bot] at ha
      simp [ha]
    · have ha' : a ∈ W.grading (k.toNat : ℤ) := by rwa [Int.toNat_of_nonneg (by omega)]
      rw [rawRight_homogeneous ha']
      exact fzSpace_right T ha' w
  · simp
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply, LinearMap.comp_add, ha, hb]

/-- Separation of the actual Zhu quotient by all matrix-valued top data.
This is intended for a complete simple family; no assertion for arbitrary
families is made. The reverse inclusion follows from `fzSpace` by definition. -/
def TopDataSeparate {ι : Type u} (A : OrdVModule W M) (P : ι → LWModule W) : Prop :=
  ∀ w : M, (∀ i j (T : fzSpace A (P i) (P j)), T.val w = 0) → w ∈ fzO A.toWeakModule

/-- Every top datum factors through the original `O(M)` quotient. -/
noncomputable def topQuot (T : fzSpace A P₂ P₃) :
    (M ⧸ fzO A.toWeakModule) →ₗ[ℂ] (bot P₂ →ₗ[ℂ] bot P₃) :=
  (fzO A.toWeakModule).liftQ T.val T.property.1

@[simp] theorem topQuot_mk (T : fzSpace A P₂ P₃) (w : M) :
    topQuot T ((fzO A.toWeakModule).mkQ w) = T.val w := rfl

theorem quotient_ext_of_topDataSeparate {ι : Type u} {P : ι → LWModule W}
    (hsep : TopDataSeparate A P) {x y : M ⧸ fzO A.toWeakModule}
    (he : ∀ i j (T : fzSpace A (P i) (P j)), topQuot T x = topQuot T y) : x = y := by
  obtain ⟨x, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective y
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact hsep (x - y) fun i j T => by
    rw [map_sub]
    exact sub_eq_zero.mpr (he i j T)

theorem rawLeft_preserves_fzO {ι : Type u} {P : ι → LWModule W}
    (hsep : TopDataSeparate A P) (a : V) {w : M} (hw : w ∈ fzO A.toWeakModule) :
    rawLeft A a w ∈ fzO A.toWeakModule :=
  hsep _ fun _ _ T => by rw [fzSpace_rawLeft, T.property.1 w hw, LinearMap.comp_zero]

theorem rawRight_preserves_fzO {ι : Type u} {P : ι → LWModule W}
    (hsep : TopDataSeparate A P) (a : V) {w : M} (hw : w ∈ fzO A.toWeakModule) :
    rawRight A a w ∈ fzO A.toWeakModule :=
  hsep _ fun _ _ T => by rw [fzSpace_rawRight, T.property.1 w hw, LinearMap.zero_comp]

end VOA.Huang.LiFusion
