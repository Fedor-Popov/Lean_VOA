import VOA.Classification.COne.OrbC2Quotient

/-!
# Averaged mixed products generate the obstruction

For a finite automorphism group, the kernel of the inclusion-induced map on
C₂ quotients is spanned by the Reynolds averages of ambient (-2)-products.
If one input is fixed, its class is zero. Hence only pairs of vectors with
zero Reynolds average need to be controlled.
-/

noncomputable section
namespace VOA.Classification.COne.OrbC2
open VOA VertexOperatorAlgebra
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V}

/-- Normalized averaging into the actual fixed-point carrier. -/
def average (G : Subgroup (Aut W)) [Fintype G] : V →ₗ[ℂ] (orbifold G).carrier :=
  (((Fintype.card G : ℂ)⁻¹) •
    ∑ g : G, g.1.toLinearEquiv.toLinearMap).codRestrict _ (by
      intro x g hg
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearEquiv.coe_coe]
      rw [map_smul, map_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : G)) _ _ (fun h => rfl))

@[simp] theorem average_val (G : Subgroup (Aut W)) [Fintype G] (x : V) :
    (average G x : V) = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, g.1 x := by
  classical
  simp [average]

@[simp] theorem average_fixed (G : Subgroup (Aut W)) [Fintype G]
    (x : (orbifold G).carrier) : average G x.val = x := by
  apply Subtype.ext
  rw [average_val]
  have hfix : ∀ g : G, g.1 x.val = x.val := fun g => x.2 g.1 g.2
  simp only [hfix, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

theorem aut_preserves_c2 (g : Aut W) {x : V} (hx : x ∈ O₂ W) : g x ∈ O₂ W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    rw [g.map_smul']
    exact Submodule.subset_span ⟨g a, g b, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using (O₂ W).add_mem hx hy
  | smul a x _ hx => simpa using (O₂ W).smul_mem a hx

theorem average_preserves_c2 (G : Subgroup (Aut W)) [Fintype G]
    {x : V} (hx : x ∈ O₂ W) : (average G x : V) ∈ O₂ W := by
  rw [average_val]
  exact (O₂ W).smul_mem _ ((O₂ W).sum_mem fun g _ => aut_preserves_c2 g.val hx)

/-- The obstruction is the image of ambient C₂ under averaging and intrinsic projection. -/
theorem ker_inclusion_eq_average_image (G : Subgroup (Aut W)) [Fintype G] :
    LinearMap.ker (inclusionC2 (orbifold G)) =
      (O₂ W).map ((mk₂ (orbifoldVOA G)).comp (average G)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨v, rfl⟩ := mk₂_surjective (orbifoldVOA G) x
    refine ⟨v.val, (mk_mem_ker_inclusionC2 (orbifold G) v).mp hx, ?_⟩
    simp
  · rintro _ ⟨x, hx, rfl⟩
    exact (mk_mem_ker_inclusionC2 (orbifold G) (average G x)).mpr
      (average_preserves_c2 G hx)

/-- Class of a Reynolds-averaged ambient (-2)-product in the intrinsic quotient. -/
def averagedPair (G : Subgroup (Aut W)) [Fintype G] (a b : V) : A₂ (orbifoldVOA G) :=
  mk₂ (orbifoldVOA G) (average G (W.smul a (-2) b))

/-- All of the kernel, with no unproved invariant-theory identification. -/
theorem ker_inclusion_eq_span_pairs (G : Subgroup (Aut W)) [Fintype G] :
    LinearMap.ker (inclusionC2 (orbifold G)) =
      Submodule.span ℂ (Set.range (fun ab : V × V => averagedPair G ab.1 ab.2)) := by
  rw [ker_inclusion_eq_average_image]
  change (Submodule.span ℂ {x | ∃ a b : V, x = W.smul a (-2) b}).map _ = _
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, b, rfl⟩, rfl⟩
    exact ⟨(a, b), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨W.smul a (-2) b, ⟨a, b, rfl⟩, rfl⟩

theorem average_mode_left (G : Subgroup (Aut W)) [Fintype G]
    (a : (orbifold G).carrier) (b : V) (n : ℤ) :
    average G (W.smul a.val n b) = (orbifoldVOA G).smul a n (average G b) := by
  apply Subtype.ext
  change (average G (W.smul a.val n b) : V) = W.smul a.val n (average G b : V)
  rw [average_val, average_val]
  simp only [PreVertexAlgebra.smul, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact (g.1.map_smul' a.val n b).trans (by rw [a.2 g.1 g.2]; rfl)

/-- Linearity in the first input of a fixed mode. -/
def modeLeft (n : ℤ) (b : V) : V →ₗ[ℂ] V where
  toFun a := W.smul a n b
  map_add' a a' := W.smul_add_left a a' n b
  map_smul' c a := W.smul_smul_left c a n b

theorem average_mode_right (G : Subgroup (Aut W)) [Fintype G]
    (a : V) (b : (orbifold G).carrier) (n : ℤ) :
    average G (W.smul a n b.val) = (orbifoldVOA G).smul (average G a) n b := by
  apply Subtype.ext
  change (average G (W.smul a n b.val) : V) = W.smul (average G a : V) n b.val
  rw [average_val, average_val]
  change _ = modeLeft (W := W) n b.val (_ • ∑ g : G, g.val a)
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact (g.1.map_smul' a n b.val).trans (by rw [b.2 g.1 g.2]; rfl)

@[simp] theorem averagedPair_fixed_left (G : Subgroup (Aut W)) [Fintype G]
    (a : (orbifold G).carrier) (b : V) : averagedPair G a.val b = 0 := by
  rw [averagedPair, average_mode_left, mk₂_eq_zero_iff]
  exact Submodule.subset_span ⟨a, average G b, rfl⟩

@[simp] theorem averagedPair_fixed_right (G : Subgroup (Aut W)) [Fintype G]
    (a : V) (b : (orbifold G).carrier) : averagedPair G a b.val = 0 := by
  rw [averagedPair, average_mode_right, mk₂_eq_zero_iff]
  exact Submodule.subset_span ⟨average G a, b, rfl⟩

/-- Remove the fixed component of a vector. -/
def moving (G : Subgroup (Aut W)) [Fintype G] (a : V) : V := a - (average G a : V)

@[simp] theorem average_moving (G : Subgroup (Aut W)) [Fintype G] (a : V) :
    average G (moving G a) = 0 := by
  rw [moving, map_sub, average_fixed, sub_self]

/-- Only products of two nonfixed components contribute to the obstruction. -/
theorem averagedPair_moving (G : Subgroup (Aut W)) [Fintype G] (a b : V) :
    averagedPair G (moving G a) (moving G b) = averagedPair G a b := by
  have h (x y z t : V) : averagedPair G (x - y) (z - t) =
      averagedPair G x z - averagedPair G x t -
        (averagedPair G y z - averagedPair G y t) := by
    have hl (r s v : V) : W.smul (r - s) (-2) v = W.smul r (-2) v - W.smul s (-2) v :=
      (modeLeft (W := W) (-2) v).map_sub r s
    have hr (r s v : V) : W.smul r (-2) (s - v) = W.smul r (-2) s - W.smul r (-2) v :=
      (mode (W.Y r) (-2)).map_sub s v
    simp only [averagedPair, hl, hr, map_sub]
  rw [moving, moving, h, averagedPair_fixed_right, averagedPair_fixed_left,
    averagedPair_fixed_left, sub_zero, sub_self, sub_zero]

/-- A finite spanning bound only on zero-average pairs suffices for C₂-cofiniteness. -/
theorem c2Cofinite_of_moving_pairs (G : Subgroup (Aut W)) [Fintype G]
    (hW : C2Cofinite W) (s : Finset (A₂ (orbifoldVOA G)))
    (hspan : ∀ a b : V, average G a = 0 → average G b = 0 →
      averagedPair G a b ∈ Submodule.span ℂ (s : Set (A₂ (orbifoldVOA G)))) :
    C2Cofinite (orbifoldVOA G) := by
  apply c2Cofinite_of_ambient_c2_span (orbifold G) hW s
  intro v hv
  have hx := (mk_mem_ker_inclusionC2 (orbifold G) v).mpr hv
  rw [ker_inclusion_eq_span_pairs] at hx
  have hle : Submodule.span ℂ (Set.range (fun ab : V × V => averagedPair G ab.1 ab.2)) ≤
      Submodule.span ℂ (s : Set (A₂ (orbifoldVOA G))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change averagedPair G a b ∈ _
    rw [← averagedPair_moving G a b]
    exact hspan _ _ (average_moving G a) (average_moving G b)
  exact hle hx

/-- The explicit finite-span input left by the averaging reduction. -/
def MovingPairSpanFinite (G : Subgroup (Aut W)) [Fintype G] : Prop :=
  ∃ s : Finset (A₂ (orbifoldVOA G)), ∀ a b : V,
    average G a = 0 → average G b = 0 →
      averagedPair G a b ∈ Submodule.span ℂ (s : Set (A₂ (orbifoldVOA G)))

/-- The finite-span input holds whenever intrinsic C₂-cofiniteness is known. -/
theorem movingPairSpanFinite_of_c2Cofinite (G : Subgroup (Aut W)) [Fintype G]
    (h : C2Cofinite (orbifoldVOA G)) : MovingPairSpanFinite G := by
  letI : FiniteDimensional ℂ (A₂ (orbifoldVOA G)) := h
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℂ (A₂ (orbifoldVOA G))).FG)
  refine ⟨s, fun a b _ _ => ?_⟩
  rw [hs]
  exact Submodule.mem_top

/-- The reduction is lossless, not a claim that finite ambient invariants suffice. -/
theorem movingPairSpanFinite_iff_c2Cofinite (G : Subgroup (Aut W)) [Fintype G]
    (hW : C2Cofinite W) : MovingPairSpanFinite G ↔ C2Cofinite (orbifoldVOA G) := by
  constructor
  · rintro ⟨s, hs⟩
    exact c2Cofinite_of_moving_pairs G hW s hs
  · exact movingPairSpanFinite_of_c2Cofinite G

end VOA.Classification.COne.OrbC2
