import VOA.Huang.GenusOneC2Convergence
import VOA.Huang.MatrixCoeffODE

/-!
# Two-insertion C₂ reduction

The two slots interact: a minus-two mode at either insertion is reduced to
nonnegative modes at BOTH insertions. This is the weight-lowering part of
Huang, math/0303049, Proposition 3.3. The coefficient ring is arbitrary.
The trace identity giving this reduction is a separate obligation.
-/
namespace VOA.Huang.GenusTwoPoint.QEquation
open VOA VOA.Huang.FusionC2 VOA.Huang.LWBottomRecovery VOA.Huang.BottomRecovery
open scoped BigOperators

universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}
  {R E : Type*} [CommRing R] [Algebra ℂ R]
  [AddCommGroup E] [Module ℂ E] [Module R E] [IsScalarTower ℂ R E]

/-- Only the nonnegative modes at the two insertions occur in the reduction. -/
def lowerSpan (A : WeakModule W M₁) (B : WeakModule W M₂)
    (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] E) (a : V) (x : M₁) (y : M₂) : Submodule R E :=
  Submodule.span R (Set.range fun m : ℕ => S (mode (A.YM a) m x) y) ⊔
    Submodule.span R (Set.range fun m : ℕ => S x (mode (B.YM a) m y))

/-- The algebraic consequence of the two genus-one minus-two Ward identities.
No finiteness or analytic conclusion is included in this predicate. -/
structure C2Reduction (A : WeakModule W M₁) (B : WeakModule W M₂)
    (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] E) : Prop where
  left : ∀ a x y, S (mode (A.YM a) (-2) x) y ∈ lowerSpan (R := R) A B S a x y
  right : ∀ a x y, S x (mode (B.YM a) (-2) y) ∈ lowerSpan (R := R) A B S a x y

/-- Project a C₂ decomposition to one level before applying a linear map. -/
theorem homogeneous_mem_of_C2 (A : AdmissibleModule W M₁)
    (S : M₁ →ₗ[ℂ] E) (T : Submodule R E) {U : Set M₁}
    (hU : ∀ u ∈ U, ∃ n, u ∈ A.lev n)
    (htop : (⊤ : Submodule ℂ M₁) = Submodule.span ℂ U ⊔ C2M A.toWeakModule)
    (n : ℤ) (hrep : ∀ u ∈ U, u ∈ A.lev n → S u ∈ T)
    (hmode : ∀ (a : V) (p j : ℤ) (x : M₁), a ∈ W.grading p → x ∈ A.lev j →
      j + p + 1 = n → S (mode (A.toWeakModule.YM a) (-2) x) ∈ T)
    {x : M₁} (hx : x ∈ A.lev n) : S x ∈ T := by
  let P : Submodule ℂ M₁ := (T.restrictScalars ℂ).comap S
  have hproj : ∀ u ∈ Submodule.span ℂ U, levProj A n u ∈ P := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨d, hd⟩ := hU u hu
      by_cases he : n = d
      · subst d
        rw [levProj_of_mem A hd]
        exact hrep u hu hd
      · rw [levProj_of_mem_ne A hd he]
        exact P.zero_mem
    | zero => rw [map_zero]; exact P.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact P.smul_mem c hx
  have hxS : x ∈ Submodule.span ℂ U ⊔ C2M A.toWeakModule := by rw [← htop]; trivial
  obtain ⟨s, hs, c, hc, he⟩ := Submodule.mem_sup.mp hxS
  have hcP : levProj A n c ∈ P := by
    refine (Submodule.span_le.mpr ?_) (levProj_C2M A n hc)
    rintro _ ⟨a, p, j, m, ha, hm, hjk, rfl⟩
    exact hmode a p j m ha hm (by omega)
  have h := P.add_mem (hproj s hs) hcP
  rw [← map_add, he, levProj_of_mem A hx] at h
  exact h

/-- Huang's two-slot induction: homogeneous C₂ representatives in the two
insertions generate every value, including all cross-insertion reductions. -/
theorem mem_span_pairs (A : AdmissibleModule W M₁) (B : AdmissibleModule W M₂)
    (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] E) (hS : C2Reduction (R := R) A.toWeakModule B.toWeakModule S)
    {U : Set M₁} {Z : Set M₂}
    (hU : ∀ u ∈ U, ∃ n, u ∈ A.lev n) (hZ : ∀ z ∈ Z, ∃ n, z ∈ B.lev n)
    (htopA : (⊤ : Submodule ℂ M₁) = Submodule.span ℂ U ⊔ C2M A.toWeakModule)
    (htopB : (⊤ : Submodule ℂ M₂) = Submodule.span ℂ Z ⊔ C2M B.toWeakModule)
    (x : M₁) (y : M₂) :
    S x y ∈ Submodule.span R {v | ∃ u ∈ U, ∃ z ∈ Z, S u z = v} := by
  let T : Submodule R E := Submodule.span R {v | ∃ u ∈ U, ∃ z ∈ Z, S u z = v}
  have hlev : ∀ K : ℕ, ∀ (n m : ℤ), n + m = K → ∀ x ∈ A.lev n, ∀ y ∈ B.lev m,
      S x y ∈ T := by
    intro K
    induction K using Nat.strong_induction_on with
    | _ K ih =>
      intro n m hnm x hx y hy
      have hlow : ∀ (n' m' : ℤ), n' + m' < K → ∀ x' ∈ A.lev n', ∀ y' ∈ B.lev m',
          S x' y' ∈ T := by
        intro n' m' hlt x' hx' y' hy'
        by_cases hn : n' < 0
        · rw [A.lev_eq_bot_of_neg n' hn, Submodule.mem_bot] at hx'
          simp only [hx', map_zero, LinearMap.zero_apply]
          exact T.zero_mem
        by_cases hm : m' < 0
        · rw [B.lev_eq_bot_of_neg m' hm, Submodule.mem_bot] at hy'
          simp only [hy', map_zero]
          exact T.zero_mem
        exact ih (n' + m').toNat (by omega) n' m' (by omega) x' hx' y' hy'
      have hlower (a : V) (p i j : ℤ) (u : M₁) (v : M₂)
          (ha : a ∈ W.grading p) (hu : u ∈ A.lev i) (hv : v ∈ B.lev j)
          (hij : i + j + p + 1 = K) :
          lowerSpan (R := R) A.toWeakModule B.toWeakModule S a u v ≤ T := by
        apply sup_le
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨r, rfl⟩
          exact hlow (i + (p - r - 1)) j (by omega) _ (A.act_lev ha hu) v hv
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨r, rfl⟩
          exact hlow i (j + (p - r - 1)) (by omega) u hu _ (B.act_lev ha hv)
      apply homogeneous_mem_of_C2 A (S.flip y) T hU htopA n ?_ ?_ hx
      · intro u hu hun
        apply homogeneous_mem_of_C2 B (S u) T hZ htopB m ?_ ?_ hy
        · intro z hz _
          exact Submodule.subset_span ⟨u, hu, z, hz, rfl⟩
        · intro a p j v ha hv hj
          exact hlower a p n j u v ha hun hv (by omega) (hS.right a u v)
      · intro a p i u ha hu hi
        exact hlower a p i m u y ha hu hy (by omega) (hS.left a u y)
  have hall : ∀ (n m : ℤ), ∀ x ∈ A.lev n, ∀ y ∈ B.lev m, S x y ∈ T := by
    intro n m x hx y hy
    by_cases hn : n < 0
    · rw [A.lev_eq_bot_of_neg n hn, Submodule.mem_bot] at hx
      simp only [hx, map_zero, LinearMap.zero_apply]; exact T.zero_mem
    by_cases hm : m < 0
    · rw [B.lev_eq_bot_of_neg m hm, Submodule.mem_bot] at hy
      simp only [hy, map_zero]; exact T.zero_mem
    exact hlev (n + m).toNat n m (by omega) x hx y hy
  refine induction_lev A (motive := fun x => ∀ y, S x y ∈ T) x ?_ ?_ ?_ y
  · intro y; simp only [map_zero, LinearMap.zero_apply]; exact T.zero_mem
  · intro x x' hx hx' y
    simpa only [map_add, LinearMap.add_apply] using T.add_mem (hx y) (hx' y)
  · intro n x hx y
    refine induction_lev B (motive := fun y => S x y ∈ T) y ?_ ?_ ?_
    · simpa only [map_zero] using T.zero_mem
    · intro y y' hy hy'; simpa only [map_add] using T.add_mem hy hy'
    · intro m y hy; exact hall n m x hx y hy

/-- A finite product of homogeneous C₂ complements suffices. The finite sets
are chosen before the two-point block. -/
theorem exists_generators_of_C2 (A : AdmissibleModule W M₁) (B : AdmissibleModule W M₂)
    (hA : ModuleC2Cofinite A.toWeakModule) (hB : ModuleC2Cofinite B.toWeakModule) :
    ∃ (U : Finset M₁) (Z : Finset M₂), ∀ S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] E,
      C2Reduction (R := R) A.toWeakModule B.toWeakModule S →
      ∀ x y, ∃ c : U × Z → R, S x y = ∑ k : U × Z, c k • S k.1.val k.2.val := by
  classical
  obtain ⟨U, hU, htopU⟩ := exists_finset_homog (N := A) hA
  obtain ⟨Z, hZ, htopZ⟩ := exists_finset_homog (N := B) hB
  refine ⟨U, Z, fun S hS x y => ?_⟩
  have h := mem_span_pairs A B S hS hU hZ htopU htopZ x y
  have he : {v | ∃ u ∈ (U : Set M₁), ∃ z ∈ (Z : Set M₂), S u z = v} =
      Set.range (fun k : U × Z => S k.1.val k.2.val) := by
    ext v
    constructor
    · rintro ⟨u, hu, z, hz, rfl⟩; exact ⟨(⟨u, hu⟩, ⟨z, hz⟩), rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k.1.val, k.1.property, k.2.val, k.2.property, rfl⟩
  rw [he] at h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp h
  exact ⟨c, hc.symm⟩

end VOA.Huang.GenusTwoPoint.QEquation
