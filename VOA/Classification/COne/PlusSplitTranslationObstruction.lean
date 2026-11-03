import VOA.Classification.COne.PlusSplitVacuumLift
import Mathlib.LinearAlgebra.Projection

/-! An explicit cokernel obstruction to correcting a vector lift, and its
application to a weak-module epimorphism onto the adjoint module. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {W : VertexOperatorAlgebra V}

/-- The class of a failed relation in the cokernel of the allowed corrections.
The map may encode a simultaneous family of linear relations. -/
def liftObstruction (D : M →ₗ[ℂ] N) (K : Submodule ℂ M) (x : M) : N ⧸ K.map D :=
  Submodule.Quotient.mk (D x)

theorem liftObstruction_eq_zero_iff (D : M →ₗ[ℂ] N) (K : Submodule ℂ M) (x : M) :
    liftObstruction D K x = 0 ↔ ∃ y ∈ K, D (x - y) = 0 := by
  rw [liftObstruction, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, by rw [map_sub, he, sub_self]⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, (sub_eq_zero.mp (by simpa only [map_sub] using he)).symm⟩

/-- The obstruction does not change when the lift changes by a kernel vector. -/
theorem liftObstruction_add (D : M →ₗ[ℂ] N) (K : Submodule ℂ M)
    (x : M) {y : M} (hy : y ∈ K) :
    liftObstruction D K (x + y) = liftObstruction D K x := by
  change (K.map D).mkQ (D (x + y)) = (K.map D).mkQ (D x)
  have hz : (K.map D).mkQ (D y) = 0 :=
    (Submodule.Quotient.mk_eq_zero (K.map D)).mpr ⟨y, hy, rfl⟩
  rw [map_add, map_add, hz, add_zero]

/-- For an actual vacuum quotient, the translation obstruction suffices. -/
theorem complement_of_translation_obstruction (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) {x : M} (hx : π.toLinearMap x = W.vacuum)
    (ho : liftObstruction (translation A) (LinearMap.ker π.toLinearMap) x = 0) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl (modeComap π ⊥) Q := by
  obtain ⟨y, hy, hD⟩ := (liftObstruction_eq_zero_iff _ _ _).mp ho
  apply complement_of_vacuum_lift A π hD
  change π.toLinearMap y = 0 at hy
  rw [map_sub, hx, hy, sub_zero]

/-- Conversely, a complement kills the translation obstruction of every
vacuum lift. Thus this is an exact obstruction, not only a sufficient test. -/
theorem translation_obstruction_eq_zero_of_complement (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) (Q : Submodule (modeAlg A) M)
    (hQ : IsCompl (modeComap π ⊥) Q) {x : M} (hx : π.toLinearMap x = W.vacuum) :
    liftObstruction (translation A) (LinearMap.ker π.toLinearMap) x = 0 := by
  let K := modeComap π ⊥
  have hsum : K ⊔ Q = ⊤ := hQ.sup_eq_top
  obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (hsum ▸ (Submodule.mem_top : x ∈ ⊤))
  have hπy : π.toLinearMap y = 0 := hy
  have hπz : π.toLinearMap z = W.vacuum := by
    rw [← he, map_add, hπy, zero_add] at hx
    exact hx
  have hDzK : translation A z ∈ K := by
    change π.toLinearMap (A.act W.conformalVector 0 z) = 0
    rw [π.map_act, hπz]
    exact (W.creation W.conformalVector).2 0 le_rfl
  have hDzQ : translation A z ∈ Q := (ofR A Q).act_mem _ _ hz
  have hDz : translation A z = 0 := Submodule.disjoint_def.mp hQ.disjoint _ hDzK hDzQ
  apply (liftObstruction_eq_zero_iff _ _ _).mpr
  refine ⟨y, hπy, ?_⟩
  rw [← he, add_sub_cancel_left, hDz]

theorem complement_iff_translation_obstruction (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) {x : M} (hx : π.toLinearMap x = W.vacuum) :
    (∃ Q : Submodule (modeAlg A) M, IsCompl (modeComap π ⊥) Q) ↔
      liftObstruction (translation A) (LinearMap.ker π.toLinearMap) x = 0 :=
  ⟨fun ⟨Q, hQ⟩ => translation_obstruction_eq_zero_of_complement A π Q hQ hx,
    complement_of_translation_obstruction A π hx⟩

/-- Local finiteness lifts the actual vacuum into generalized weight zero. -/
theorem exists_generalized_vacuum_lift (hC2 : C2Cofinite W) (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) (hπ : Function.Surjective π.toLinearMap) :
    ∃ x : M, x ∈ (L0 A).maxGenEigenspace 0 ∧ π.toLinearMap x = W.vacuum := by
  have hv : W.vacuum ∈ (L0 (adjointWeakModule W)).maxGenEigenspace 0 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    exact (adjointModule W).L0_weight 0 _ (PlusUnitary.vacuum_mem_adjoint_weight W)
  have hs := map_inf_maxGenEigenspace (L0 A) (L0 (adjointWeakModule W)) π.toLinearMap
    (π.map_act W.conformalVector 1) (weakL0LocallyFinite hC2 A) ⊤
    (fun _ _ => Submodule.mem_top) 0
  have hm : W.vacuum ∈ (⊤ : Submodule ℂ M).map π.toLinearMap ⊓
      (L0 (adjointWeakModule W)).maxGenEigenspace 0 := by
    obtain ⟨x, hx⟩ := hπ W.vacuum
    exact ⟨⟨x, Submodule.mem_top, hx⟩, hv⟩
  rw [← hs] at hm
  obtain ⟨x, hx, he⟩ := hm
  exact ⟨x, hx.2, he⟩

/-- A vacuum quotient splits if the kernel has no generalized weight one.
The middle weak module need not be ordinary, and the kernel need not be simple. -/
theorem complement_of_vacuum_quotient_no_weight_one (hC2 : C2Cofinite W)
    (A : WeakModule W M) (π : A.Hom (adjointWeakModule W))
    (hπ : Function.Surjective π.toLinearMap)
    (h1 : LinearMap.ker π.toLinearMap ⊓ (L0 A).maxGenEigenspace 1 = ⊥) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl (modeComap π ⊥) Q := by
  obtain ⟨x, hx, he⟩ := exists_generalized_vacuum_lift hC2 A π hπ
  apply complement_of_vacuum_lift A π (x := x) _ he
  have hw : translation A x ∈ (L0 A).maxGenEigenspace 1 := by
    simpa only [sub_zero, show (2 : ℤ) - 1 = 1 from rfl, Int.cast_one, zero_add]
      using mode_mem_maxGenEigenspace A W.conformal_mem 0 hx
  have hk : translation A x ∈ LinearMap.ker π.toLinearMap := by
    change π.toLinearMap (A.act W.conformalVector 0 x) = 0
    rw [π.map_act, he]
    exact (W.creation W.conformalVector).2 0 le_rfl
  have hz : translation A x ∈ LinearMap.ker π.toLinearMap ⊓
      (L0 A).maxGenEigenspace 1 := ⟨hk, hw⟩
  rwa [h1, Submodule.mem_bot] at hz

/-- In particular, every actual vacuum quotient with kernel bottom above one splits. -/
theorem complement_of_vacuum_quotient_bottom_gt_one (hC2 : C2Cofinite W)
    (A : WeakModule W M) (π : A.Hom (adjointWeakModule W))
    (hπ : Function.Surjective π.toLinearMap) (h : ℂ)
    (hb : FactorBottom A ⊥ (modeComap π ⊥) h) (hh : 1 < h.re) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl (modeComap π ⊥) Q := by
  apply complement_of_vacuum_quotient_no_weight_one hC2 A π hπ
  apply bot_unique
  intro y hy
  by_contra hn
  have hw : FactorWeight A ⊥ (modeComap π ⊥) 1 := fun ht => hn (ht hy)
  have := hb.2 1 hw
  simp only [Complex.one_re] at this
  exact (not_le_of_gt hh) this

/-- A positive kernel bottom makes the zero-weight vacuum lift unique. In
particular there is no weight-zero correction available in the sign case. -/
theorem generalized_vacuum_lift_unique (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) (h : ℂ)
    (hb : FactorBottom A ⊥ (modeComap π ⊥) h) (hh : 0 < h.re)
    {x y : M} (hx : x ∈ (L0 A).maxGenEigenspace 0)
    (hy : y ∈ (L0 A).maxGenEigenspace 0)
    (he : π.toLinearMap x = π.toLinearMap y) : x = y := by
  apply sub_eq_zero.mp
  by_contra hn
  have hk : x - y ∈ modeComap π ⊥ := by
    change π.toLinearMap (x - y) = 0
    rw [map_sub, he, sub_self]
  have hw : FactorWeight A ⊥ (modeComap π ⊥) 0 :=
    fun ht => hn (ht ⟨hk, (L0 A).maxGenEigenspace 0 |>.sub_mem hx hy⟩)
  have hl := hb.2 0 hw
  simp only [Complex.zero_re] at hl
  exact (not_le_of_gt hh) hl

/-- For a positive-bottom kernel and a fixed generalized vacuum lift, the
obstruction is literally its translation: splitting cannot be obtained by
adjusting that lift in weight zero. This isolates the unsolved weight-one case. -/
theorem complement_iff_translation_zero_of_positive_bottom (A : WeakModule W M)
    (π : A.Hom (adjointWeakModule W)) (h : ℂ)
    (hb : FactorBottom A ⊥ (modeComap π ⊥) h) (hh : 0 < h.re)
    {x : M} (hx : x ∈ (L0 A).maxGenEigenspace 0)
    (he : π.toLinearMap x = W.vacuum) :
    (∃ Q : Submodule (modeAlg A) M, IsCompl (modeComap π ⊥) Q) ↔ translation A x = 0 := by
  constructor
  · intro hc
    have ho := (complement_iff_translation_obstruction A π he).mp hc
    obtain ⟨y, hy, hz⟩ := (liftObstruction_eq_zero_iff _ _ _).mp ho
    have hgen : x - y ∈ (L0 A).maxGenEigenspace 0 := by
      apply Module.End.eigenspace_le_maxGenEigenspace
      apply Module.End.mem_eigenspace_iff.mpr
      have hv := nonnegative_modes_zero_of_translation_zero A hz W.conformalVector 1 (by norm_num)
      simpa only [zero_smul] using hv
    have heq : x = x - y := generalized_vacuum_lift_unique A π h hb hh hx hgen (by
      change π.toLinearMap y = 0 at hy
      rw [map_sub, hy, sub_zero])
    rwa [← heq] at hz
  · intro hz
    exact complement_of_vacuum_lift A π hz he

end VOA.Classification.COne.PlusSplitting
