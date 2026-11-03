import VOA.Classification.COne.McRaeM2LocalInjective

/-! # Essential socles of arbitrary weak modules under C₂-cofiniteness

Finite length of every cyclic weak module implies that every nonzero weak
submodule contains a simple submodule. Thus the actual sum of all simple
submodules is essential, even before proving that this sum is finite-length.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne
open VOA.Classification.COne.PlusRational
open VOA.Classification.COne.PlusFiniteLength

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The genuine socle: the sum of all simple mode-algebra submodules. -/
def socle (B : WeakModule W M) : Submodule (modeAlg B) M :=
  sSup {P | IsAtom P}

/-- Every nonzero weak submodule contains an actual simple submodule. -/
theorem exists_atom_le (hC2 : C2Cofinite W) (B : WeakModule W M)
    (N : Submodule (modeAlg B) M) (hN : N ≠ ⊥) :
    ∃ A : Submodule (modeAlg B) M, IsAtom A ∧ A ≤ N := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let P := cyclic B x
  have hP := cyclicFiniteLength_of_c2Cofinite hC2 B x
  haveI : IsArtinian (modeAlg B) P :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hP).2
  haveI : Nontrivial P := by
    refine ⟨⟨⟨x,Submodule.mem_span_singleton_self x⟩,0,?_⟩⟩
    intro h
    exact hx0 (congrArg Subtype.val h)
  obtain ⟨Q,hQ⟩ := IsAtomic.exists_atom (Submodule (modeAlg B) P)
  let A := (Submodule.mapIic P Q).val
  have hA : IsAtom A :=
    IsAtom.of_isAtom_coe_Iic (((Submodule.mapIic P).isAtom_iff Q).mpr hQ)
  refine ⟨A,hA,le_trans (Submodule.mapIic P Q).property ?_⟩
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)

/-- C₂-cofiniteness makes the weak-submodule lattice atomic. -/
theorem isAtomic_of_c2 (hC2 : C2Cofinite W) (B : WeakModule W M) :
    IsAtomic (Submodule (modeAlg B) M) where
  eq_bot_or_exists_atom_le N := by
    by_cases hN : N = ⊥
    · exact Or.inl hN
    · exact Or.inr (exists_atom_le hC2 B N hN)

/-- The socle has zero intersection only with the zero submodule. -/
theorem socle_essential (hC2 : C2Cofinite W) (B : WeakModule W M)
    (N : Submodule (modeAlg B) M) (h : socle B ⊓ N = ⊥) : N = ⊥ := by
  by_contra hN
  obtain ⟨A,hA,hAN⟩ := exists_atom_le hC2 B N hN
  have hAS : A ≤ socle B := le_sSup hA
  have hAB : A ≤ ⊥ := h ▸ le_inf hAS hAN
  exact hA.ne_bot (le_bot_iff.mp hAB)

/-- The same essentiality statement with the actual weak-submodule interface. -/
theorem socle_essential_weak (hC2 : C2Cofinite W) (B : WeakModule W M)
    (R : WeakModule.Submodule' B)
    (h : (ofR B (socle B)).carrier ⊓ R.carrier = ⊥) : R.carrier = ⊥ := by
  have hr : socle B ⊓ toR B R = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hz : x ∈ (⊥ : Submodule ℂ M) := h ▸ hx
    exact hz
  have he := socle_essential hC2 B (toR B R) hr
  apply eq_bot_iff.mpr
  intro x hx
  have hz : x ∈ (⊥ : Submodule (modeAlg B) M) := he ▸ hx
  exact hz

/-- Bounding the genuine socle by a finite-length injective object bounds the
entire weak module; this specializes to the maximal P(z)-compatible module. -/
theorem finiteLength_of_socle_embedding (hC2 : C2Cofinite W) (B : WeakModule W M)
    {I : Type u} [AddCommGroup I] [Module ℂ I] (BI : WeakModule W I)
    (hI : IsInjFL BI) (hfl : IsFiniteLength (modeAlg BI) I)
    (f : (WeakModule.submodule B (ofR B (socle B))).Hom BI)
    (hf : Function.Injective f.toLinearMap) : IsFiniteLength (modeAlg B) M :=
  finiteLength_of_essential_embedding hC2 B BI hI hfl (ofR B (socle B)) f hf
    (socle_essential_weak hC2 B)

end VOA.C2Rigid.LocalInjective
