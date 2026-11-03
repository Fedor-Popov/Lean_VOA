import VOA.Classification.COne.OrbPosExceptional
import VOA.Classification.COne.OrbPosTwisted
import VOA.Modules.ModuleRestrictOrd
import VOA.Huang.FusionUnit

/-!
# Vacuum identification inside the actual untwisted vacuum sector

An irreducible module embedded in the ambient adjoint module and containing
weight zero is the subalgebra's vacuum module. Thus, for this sector, vacuum
identification needs no twisted-module classification or quantum dimensions.
-/

namespace VOA.Classification.COne.OrbPos
open VOA VOA.Huang.FusionUnit VOA.LatGen.Triplet

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Any sector embedded in the restriction of a non-vacuum irreducible of a
pseudo-unitary ambient VOA has positive weights. -/
theorem nonvacuum_weights_of_restricted_embedding (hp : PseudoUnitary W)
    (S : VOASubalgebra W) {T : Type u} [AddCommGroup T] [Module ℂ T]
    (P : OrdVModule W T) (hi : P.IsIrreducible)
    (hn : IsEmpty (ModuleEquiv W P (adjointModule W)))
    (N : OrdVModule S.toVOA M) (f : M →ₗ[ℂ] T)
    (hf : f ∈ homSpace N (S.restrictOrdVModule P)) (hfi : Function.Injective f) :
    ∀ α, N.weight α ≠ ⊥ → 0 < α.re :=
  positive_weights_of_injective N P.weight f hfi
    (fun _ _ hx => hom_mem_weight hf hx) (hp T P hi hn)

/-- The preceding result for the actual untwisted V₂ sectors. It does not
assert that these sectors exhaust the exceptional orbifold modules. -/
theorem untwisted_nonvacuum_weights_positive
    (G : Subgroup (Aut (V2m 1 le_rfl)))
    {T M : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup M] [Module ℂ M]
    (P : OrdVModule (V2m 1 le_rfl) T) (hi : P.IsIrreducible)
    (hn : IsEmpty (ModuleEquiv (V2m 1 le_rfl) P (adjointModule (V2m 1 le_rfl))))
    (N : OrdVModule (orbifoldVOA G) M) (f : M →ₗ[ℂ] T)
    (hf : f ∈ homSpace N ((orbifold G).restrictOrdVModule P))
    (hfi : Function.Injective f) : ∀ α, N.weight α ≠ ⊥ → 0 < α.re :=
  nonvacuum_weights_of_restricted_embedding (V2m_pseudoUnitary 1 le_rfl)
    (orbifold G) P hi hn N f hf hfi

theorem vacuum_equiv_of_adjoint_embedding (S : VOASubalgebra W)
    (hS : S.toVOA.IsSimple) (N : OrdVModule S.toVOA M) (hi : N.IsIrreducible)
    (f : M →ₗ[ℂ] V) (hf : f ∈ homSpace N S.adjointRestrictOrd)
    (hfi : Function.Injective f) (h0 : N.weight 0 ≠ ⊥) :
    Nonempty (ModuleEquiv S.toVOA N (adjointModule S.toVOA)) := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ N.weight 0, x ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 ((Submodule.eq_bot_iff _).mpr h)
  have hfx : f x ∈ W.grading 0 := by
    have ht := hom_mem_weight hf hx
    change f x ∈ adjWeight W 0 at ht
    have hw : adjWeight W 0 = W.grading 0 := by
      simpa only [Int.cast_zero] using adjWeight_cast W 0
    rwa [hw] at ht
  have hxs : f x ∈ S.carrier := by
    rw [W.vacuum_grade] at hfx
    exact (Submodule.span_le.mpr (by
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact S.vacuum_mem)) hfx
  let P : WeakModule.Submodule' N.toWeakModule := {
    carrier := S.carrier.comap f
    act_mem := by
      intro u n y hy
      change f (N.act u n y) ∈ S.carrier
      rw [show f (N.act u n y) = W.smul (u : V) n (f y) from hf u n y]
      exact S.smul_mem (u : V) u.property n (f y) hy }
  have htop : P.carrier = ⊤ := by
    rcases hi.2 P with hb | ht
    · have hxp : x ∈ P.carrier := hxs
      rw [hb, Submodule.mem_bot] at hxp
      exact (hx0 hxp).elim
    · exact ht
  have hall (y : M) : f y ∈ S.carrier := by
    change y ∈ P.carrier
    rw [htop]
    exact Submodule.mem_top
  let g : M →ₗ[ℂ] S.carrier := f.codRestrict S.carrier hall
  have hg : g ∈ homSpace N (adjointModule S.toVOA) := by
    intro u n y
    apply Subtype.ext
    exact hf u n y
  have hg0 : g ≠ 0 := by
    intro he
    have hfx0 : f x = 0 := congrArg Subtype.val (LinearMap.congr_fun he x)
    exact hx0 (hfi (hfx0.trans (map_zero f).symm))
  exact ⟨⟨LinearEquiv.ofBijective g (bijective_of_hom hi
    ((isSimple_iff_adjointModule_isIrreducible S.toVOA).mp hS) hg hg0), hg⟩⟩

/-- The remaining untwisted case: a non-vacuum irreducible embedded in the
ambient vacuum sector has integral weights at least one. -/
theorem vacuum_sector_nonvacuum_weight_gap (S : VOASubalgebra W)
    (hS : S.toVOA.IsSimple) (N : OrdVModule S.toVOA M) (hi : N.IsIrreducible)
    (hn : IsEmpty (ModuleEquiv S.toVOA N (adjointModule S.toVOA)))
    (f : M →ₗ[ℂ] V) (hf : f ∈ homSpace N S.adjointRestrictOrd)
    (hfi : Function.Injective f) (α : ℂ) (hα : N.weight α ≠ ⊥) : 1 ≤ α.re := by
  have ha : adjWeight W α ≠ ⊥ := by
    intro hz
    apply hα
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have ht := hom_mem_weight hf hx
    change f x ∈ adjWeight W α at ht
    rw [hz, Submodule.mem_bot] at ht
    exact hfi (ht.trans (map_zero f).symm)
  have hex : ∃ n : ℤ, (n : ℂ) = α := by
    by_contra he
    exact ha (adjWeight_eq_bot W (not_exists.mp he))
  obtain ⟨n, rfl⟩ := hex
  rw [adjWeight_cast] at ha
  have hn0 : 0 ≤ n := by
    by_contra h
    exact ha (W.positivity n (lt_of_not_ge h))
  have hnne : n ≠ 0 := by
    intro hz
    subst n
    have h0 : N.weight 0 ≠ ⊥ := by simpa only [Int.cast_zero] using hα
    obtain ⟨e⟩ := vacuum_equiv_of_adjoint_embedding S hS N hi f hf hfi h0
    exact hn.false e
  simp only [Complex.intCast_re]
  exact_mod_cast (show (1 : ℤ) ≤ n by omega)

/-- A concrete remaining embedding obligation for the zero-weight part of DRX
completeness. It only concerns zero-weight irreducibles and the *untwisted*
vacuum carrier V₂. It remains unproved. -/
def ExceptionalZeroWeightEmbedding : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    StronglyRational (orbifoldVOA G) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (orbifoldVOA G) M),
      N.IsIrreducible → N.weight 0 ≠ ⊥ →
      ∃ f : M →ₗ[ℂ] VOA.LatGen.LatModuleGen (latP 1),
        f ∈ homSpace N (orbifold G).adjointRestrictOrd ∧ Function.Injective f

theorem exceptionalZeroWeightVacuum_of_embedding
    (he : ExceptionalZeroWeightEmbedding) : ExceptionalZeroWeightVacuum := by
  intro G hG hSR M _ _ N hi h0
  obtain ⟨f, hf, hfi⟩ := he G hG hSR M N hi h0
  exact vacuum_equiv_of_adjoint_embedding (orbifold G) hSR.simple N hi f hf hfi h0

theorem exceptionalOrbifoldPositiveWeightsFact_of_spectrum_embedding
    (hs : ExceptionalLowestWeightSpectrum) (he : ExceptionalZeroWeightEmbedding) :
    ExceptionalOrbifoldPositiveWeightsFact :=
  exceptionalOrbifoldPositiveWeightsFact_of_residuals hs
    (exceptionalZeroWeightVacuum_of_embedding he)

end VOA.Classification.COne.OrbPos
