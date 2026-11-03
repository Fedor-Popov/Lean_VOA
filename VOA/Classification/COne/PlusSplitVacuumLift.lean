import VOA.Classification.COne.PlusUnitaryVacuum
import VOA.Classification.COne.PlusSplitTransport

/-! Li's vacuum-like vector construction for arbitrary weak modules, and
splitting of an actual adjoint quotient from a translation-annihilated lift.
No identification of a numerical bottom with an adjoint quotient is assumed. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational PlusUnitary VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Module translation, as an actual linear operator. -/
def translation (A : WeakModule W M) : Module.End ℂ M :=
  mode (A.YM W.conformalVector) 0

/-- Truncation and the translation commutator imply Li's vacuum-like condition. -/
theorem nonnegative_modes_zero_of_translation_zero (A : WeakModule W M)
    {x : M} (hx : translation A x = 0) :
    ∀ (a : V) (n : ℤ), 0 ≤ n → mode (A.YM a) n x = 0 := by
  intro a
  obtain ⟨T, hT⟩ := A.truncation a x
  suffices H : ∀ k : ℕ, ∀ n : ℤ, 0 ≤ n → T - n ≤ k → mode (A.YM a) n x = 0 from
    fun n hn => H (T - n).toNat n hn (by omega)
  intro k
  induction k with
  | zero => intro n _ hn; exact hT n (by omega)
  | succ k ih =>
    intro n hn0 hn
    have h := ih (n + 1) (by omega) (by omega)
    have hc := L_neg_one_comm A a (n + 1) x
    change translation A _ - mode (A.YM a) (n + 1) (translation A x) = _ at hc
    rw [h, map_zero, hx, map_zero, sub_zero] at hc
    have hne : (-(((n + 1 : ℤ)) : ℂ)) ≠ 0 := by
      have : ((n + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
      exact neg_ne_zero.mpr this
    simpa using (smul_eq_zero.mp hc.symm).resolve_left hne

theorem translation_zero_iff_nonnegative_modes_zero (A : WeakModule W M) (x : M) :
    translation A x = 0 ↔ ∀ (a : V) (n : ℤ), 0 ≤ n → mode (A.YM a) n x = 0 :=
  ⟨nonnegative_modes_zero_of_translation_zero A, fun h => h W.conformalVector 0 le_rfl⟩

/-- The map `a ↦ a₋₁ x` intertwines every mode, with no ordinariness hypothesis. -/
def vacuumLiftHom (A : WeakModule W M) (x : M) (hx : translation A x = 0) :
    (adjointWeakModule W).Hom A where
  toLinearMap := ((modeLinear (-1)).comp A.YM).flip x
  map_act b p a := by
    change mode (A.YM (W.smul b p a)) (-1) x =
      mode (A.YM b) p (mode (A.YM a) (-1) x)
    have hn := nonnegative_modes_zero_of_translation_zero A hx
    rw [mode_iterate A b a x p (-1)]
    rw [finsum_eq_single _ (0 : ℤ)]
    · rw [cbz_apply_nonneg _ le_rfl, hn b 0 le_rfl, map_zero, smul_zero, sub_zero]
      simp [negOnePow, gBinom]
    · intro i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · rw [cbz_apply_neg _ hi, mul_zero, zero_smul]
      · rw [hn a (-1 + i) (by omega), map_zero, hn b i hi.le, map_zero,
          smul_zero, sub_zero, smul_zero]

@[simp] theorem vacuumLiftHom_vacuum (A : WeakModule W M) (x : M)
    (hx : translation A x = 0) : (vacuumLiftHom A x hx).toLinearMap W.vacuum = x := by
  change mode (A.YM W.vacuum) (-1) x = x
  rw [A.vacuum_YM]; simp

/-- Simplicity makes the vacuum-generated map injective. -/
theorem vacuumLiftHom_injective (hW : W.IsSimple) (A : WeakModule W M)
    {x : M} (hx : translation A x = 0) (hx0 : x ≠ 0) :
    Function.Injective (vacuumLiftHom A x hx).toLinearMap := by
  let f := vacuumLiftHom A x hx
  have hi : W.IsIdeal (LinearMap.ker f.toLinearMap) := by
    intro a b n hb
    change f.toLinearMap (W.smul a n b) = 0
    change f.toLinearMap b = 0 at hb
    rw [show f.toLinearMap (W.smul a n b) = A.act a n (f.toLinearMap b)
      from f.map_act a n b, hb]
    exact map_zero _
  rcases hW.2 _ hi with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · have hv : W.vacuum ∈ LinearMap.ker f.toLinearMap := h ▸ Submodule.mem_top
    exact (hx0 (by simpa [f] using hv)).elim

/-- Sending the lifted vacuum to the vacuum makes the constructed map a section. -/
theorem vacuumLiftHom_section (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) {x : M}
    (hx : translation A x = 0) (hπ : π.toLinearMap x = W.vacuum) (a : V) :
    π.toLinearMap ((vacuumLiftHom A x hx).toLinearMap a) = a := by
  change π.toLinearMap (A.act a (-1) x) = a
  rw [π.map_act, hπ]
  exact W.toPreVertexAlgebra.smul_vacuum_neg_one a

/-- Any weak-module section gives a complement over the full mode algebra. -/
theorem isCompl_kernel_range_of_section (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) (s : (adjointWeakModule W).Hom A)
    (hs : ∀ a, π.toLinearMap (s.toLinearMap a) = a) :
    IsCompl (modeComap π ⊥) (modeMap s ⊤) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    rintro y hy ⟨a, _, rfl⟩
    change π.toLinearMap (s.toLinearMap a) = 0 at hy
    rw [hs] at hy
    rw [hy, map_zero]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro y _
    apply Submodule.mem_sup.mpr
    refine ⟨y - s.toLinearMap (π.toLinearMap y), ?_, s.toLinearMap (π.toLinearMap y),
      ⟨π.toLinearMap y, Submodule.mem_top, rfl⟩, sub_add_cancel _ _⟩
    change π.toLinearMap (y - s.toLinearMap (π.toLinearMap y)) = 0
    rw [map_sub, hs, sub_self]

/-- A translation-annihilated vacuum lift splits an actual adjoint quotient. -/
theorem complement_of_vacuum_lift (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) {x : M}
    (hx : translation A x = 0) (hπ : π.toLinearMap x = W.vacuum) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl (modeComap π ⊥) Q :=
  ⟨modeMap (vacuumLiftHom A x hx) ⊤,
    isCompl_kernel_range_of_section A π _ (vacuumLiftHom_section A π hx hπ)⟩

end VOA.Classification.COne.PlusSplitting
