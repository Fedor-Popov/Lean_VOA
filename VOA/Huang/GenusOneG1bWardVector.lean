import VOA.Huang.GenusOneG1bRational

/-!
# Vector-valued Ward bilinear maps: one Euler system for a family of channels

The product channels `Phi (Y₁ʲ) (Y₂ʲ)` attached to an iterate by
`coefficientAssociativityConverse_of_stronglyRational_pbw` have DIFFERENT
intermediate modules, hence different conformal prefactors `t^{h_j}` after
evaluation; they can only be recombined into the iterate if they satisfy one
Euler system with the SAME kernel matrix. Summing them first (`WardBilinear.finset_sum`)
loses this. Here the family is kept as a vector `S : P₁ → P₂ → (ι → ℂ⟦u⟧⟦t⟧)`
whose components are Ward bilinear (`WardBilinearV`); the C₂ induction and the
mixed-omega closure are rerun for submodules of the vector space, so the
coefficients produced are common to all components.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.FusionC2 VOA.Huang.BottomRecovery
open VOA.Huang.GenusOne (sqAct sqActDefect sqAct_neg_two_eq sqAct_mem_lower
  sqActDefect_mem_lower)
open VOA.Huang.GenusOne.SquareModule (shiftedOmega)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ : LWModule W}
variable {ι : Type*} [Fintype ι]

/-- Component `j` of a vector-valued bilinear map. -/
def compV (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (ι → R2)) (j : ι) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2 :=
  S.compr₂ (LinearMap.proj j)

@[simp] theorem compV_apply (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (ι → R2)) (j : ι)
    (x : P₁.carrier) (y : P₂.carrier) : compV S j x y = S x y j := rfl

/-- Every component satisfies the three formal Ward identities with parameter `lam`. -/
def WardBilinearV (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (ι → R2)) (lam : ℂ) : Prop :=
  ∀ j, WardBilinear (compV S j) lam

/-- The componentwise twisted Euler operator. -/
def thetaV (lam : ℂ) (F : ι → R2) : ι → R2 := fun j => thetaR2 lam (F j)

section Eq
variable (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (ι → R2)) {lam : ℂ}

theorem exists_common_K {F : ι → ℕ → R2} (h : ∀ j, EvZero (F j)) :
    ∃ K, ∀ j, F j K = 0 := by
  classical
  choose K₀ hK₀ using h
  exact ⟨Finset.univ.sup K₀, fun j => hK₀ j _ (Finset.le_sup (Finset.mem_univ j))⟩

theorem wardV_left_eq (hS : WardBilinearV S lam) (b : V) (x : P₁.carrier) (y : P₂.carrier) :
    ∃ K, S (GenusOne.SquareModule.sqMode P₁.isMod (-2) b x) y =
      -(∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
        (eis (m + 2) • S (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 2 : ℕ) : ℤ) b x) y)) -
      ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) - if m = 0 then eis 1 else 0) •
        S x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) b y) := by
  obtain ⟨K, hK⟩ := exists_common_K (fun j => (hS j).1 b x y)
  refine ⟨K, funext fun j => ?_⟩
  have h0 := hK j
  simp only [leftExpr, compV_apply] at h0
  simp only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h0

theorem wardV_right_eq (hS : WardBilinearV S lam) (b : V) (x : P₁.carrier) (y : P₂.carrier) :
    ∃ K, S x (GenusOne.SquareModule.sqMode P₂.isMod (-2) b y) =
      -(∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
        (eis (m + 2) • S x (GenusOne.SquareModule.sqMode P₂.isMod ((2 * m + 2 : ℕ) : ℤ) b y))) -
      ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
          if m = 0 then eis 1 else 0) •
        S (GenusOne.SquareModule.sqMode P₁.isMod (m : ℤ) b x) y := by
  obtain ⟨K, hK⟩ := exists_common_K (fun j => (hS j).2.1 b x y)
  refine ⟨K, funext fun j => ?_⟩
  have h0 := hK j
  simp only [rightExpr, compV_apply] at h0
  simp only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h0

theorem wardV_mixed_eq (hS : WardBilinearV S lam) (x : P₁.carrier) (y : P₂.carrier) :
    ∃ K, thetaV lam (S x y) =
      S (GenusOne.SquareModule.sqMode P₁.isMod (-1) (shiftedOmega W) x) y -
        ∑ m ∈ Finset.range K, eis (m + 1) •
          S (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 1 : ℕ) : ℤ)
            (shiftedOmega W) x) y -
        ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) •
          S x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) (shiftedOmega W) y) := by
  obtain ⟨K, hK⟩ := exists_common_K (fun j => (hS j).2.2 x y)
  refine ⟨K, funext fun j => ?_⟩
  have h0 := hK j
  simp only [mixedExpr, compV_apply] at h0
  simp only [thetaV, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -h0

end Eq

/-! ## C₂ reduction over a kernel subalgebra, vector version -/

section Span
variable (R : Subalgebra ℂ R2) (hRe : ∀ j, eis j ∈ R) (hRp : ∀ m, piK m ∈ R)
  (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (ι → R2))

theorem smul_mem_spanV {T : Submodule (↥R) (ι → R2)} {c : R2} (hc : c ∈ R) {v : ι → R2}
    (hv : v ∈ T) : c • v ∈ T := by
  have h := T.smul_mem (⟨c, hc⟩ : ↥R) hv
  convert h using 1

include hRe hRp in
theorem wardV_negTwo_left_mem {lam : ℂ} (hS : WardBilinearV S lam)
    (T : Submodule (↥R) (ι → R2)) {a : V} {p i j : ℤ}
    (ha : a ∈ W.grading p) {x : P₁.carrier} (hx : x ∈ P₁.isMod.toAdmissible.lev i)
    {y : P₂.carrier} (hy : y ∈ P₂.isMod.toAdmissible.lev j)
    (hlow : ∀ n' m' : ℤ, n' + m' < i + p + 1 + j → ∀ x' ∈ P₁.isMod.toAdmissible.lev n',
      ∀ y' ∈ P₂.isMod.toAdmissible.lev m', S x' y' ∈ T) :
    S (mode (P₁.isMod.YM a) (-2) x) y ∈ T := by
  let T₁ : Submodule ℂ P₁.carrier := (T.restrictScalars ℂ).comap (S.flip y)
  let T₂ : Submodule ℂ P₂.carrier := (T.restrictScalars ℂ).comap (S x)
  have hT₁ : ∀ d : ℤ, d < i + p + 1 → P₁.isMod.toAdmissible.lev d ≤ T₁ :=
    fun d hd x' hx' => hlow d j (by omega) x' hx' y hy
  have hT₂ : ∀ d : ℤ, d < j + p + 1 → P₂.isMod.toAdmissible.lev d ≤ T₂ :=
    fun d hd y' hy' => hlow i d (by omega) x hx y' hy'
  obtain ⟨K, h0⟩ := wardV_left_eq S hS a x y
  simp only [GenusOne.SquareModule.sqMode_of_mem_grading _ ha] at h0
  have hS1 : ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) • S (sqAct P₁.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) x) y) ∈ T := by
    refine T.sum_mem fun m _ => T.smul_of_tower_mem _
      (smul_mem_spanV R (hRe _) ?_)
    exact sqAct_mem_lower (A := P₁.isMod) P₁.isMod.toAdmissible rfl ha hx (by omega) T₁ hT₁
  have hS2 : ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
      if m = 0 then eis 1 else 0) •
        S x (sqAct P₂.isMod a p.toNat (m : ℤ) y) ∈ T := by
    refine T.sum_mem fun m _ => smul_mem_spanV R ?_ ?_
    · refine sub_mem (Subalgebra.smul_mem _ (hRp _) _) ?_
      split_ifs
      · exact hRe 1
      · exact zero_mem _
    · exact sqAct_mem_lower (A := P₂.isMod) P₂.isMod.toAdmissible rfl ha hy (by omega) T₂ hT₂
  have hsq : S (sqAct P₁.isMod a p.toNat (-2) x) y ∈ T := by
    rw [h0]
    exact T.sub_mem (T.neg_mem hS1) hS2
  have hdef : S (sqActDefect P₁.isMod a p.toNat x) y ∈ T :=
    sqActDefect_mem_lower (A := P₁.isMod) P₁.isMod.toAdmissible rfl ha hx T₁ hT₁
  have heq := sqAct_neg_two_eq P₁.isMod a p.toNat x
  have : mode (P₁.isMod.YM a) (-2) x =
      sqAct P₁.isMod a p.toNat (-2) x - sqActDefect P₁.isMod a p.toNat x := by
    rw [heq]; abel
  rw [this, map_sub, LinearMap.sub_apply]
  exact T.sub_mem hsq hdef

include hRe hRp in
theorem wardV_negTwo_right_mem {lam : ℂ} (hS : WardBilinearV S lam)
    (T : Submodule (↥R) (ι → R2)) {a : V} {p i j : ℤ}
    (ha : a ∈ W.grading p) {x : P₁.carrier} (hx : x ∈ P₁.isMod.toAdmissible.lev i)
    {y : P₂.carrier} (hy : y ∈ P₂.isMod.toAdmissible.lev j)
    (hlow : ∀ n' m' : ℤ, n' + m' < i + (j + p + 1) → ∀ x' ∈ P₁.isMod.toAdmissible.lev n',
      ∀ y' ∈ P₂.isMod.toAdmissible.lev m', S x' y' ∈ T) :
    S x (mode (P₂.isMod.YM a) (-2) y) ∈ T := by
  let T₁ : Submodule ℂ P₁.carrier := (T.restrictScalars ℂ).comap (S.flip y)
  let T₂ : Submodule ℂ P₂.carrier := (T.restrictScalars ℂ).comap (S x)
  have hT₁ : ∀ d : ℤ, d < i + p + 1 → P₁.isMod.toAdmissible.lev d ≤ T₁ :=
    fun d hd x' hx' => hlow d j (by omega) x' hx' y hy
  have hT₂ : ∀ d : ℤ, d < j + p + 1 → P₂.isMod.toAdmissible.lev d ≤ T₂ :=
    fun d hd y' hy' => hlow i d (by omega) x hx y' hy'
  obtain ⟨K, h0⟩ := wardV_right_eq S hS a x y
  simp only [GenusOne.SquareModule.sqMode_of_mem_grading _ ha] at h0
  have hS1 : ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) • S x (sqAct P₂.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) y)) ∈ T := by
    refine T.sum_mem fun m _ => T.smul_of_tower_mem _
      (smul_mem_spanV R (hRe _) ?_)
    exact sqAct_mem_lower (A := P₂.isMod) P₂.isMod.toAdmissible rfl ha hy (by omega) T₂ hT₂
  have hS2 : ∑ m ∈ Finset.range K,
      (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
        if m = 0 then eis 1 else 0) •
        S (sqAct P₁.isMod a p.toNat (m : ℤ) x) y ∈ T := by
    refine T.sum_mem fun m _ => smul_mem_spanV R ?_ ?_
    · refine sub_mem (Subalgebra.smul_mem _ (Subalgebra.smul_mem _ (hRp _) _) _) ?_
      split_ifs
      · exact hRe 1
      · exact zero_mem _
    · exact sqAct_mem_lower (A := P₁.isMod) P₁.isMod.toAdmissible rfl ha hx (by omega) T₁ hT₁
  have hsq : S x (sqAct P₂.isMod a p.toNat (-2) y) ∈ T := by
    rw [h0]
    exact T.sub_mem (T.neg_mem hS1) hS2
  have hdef : S x (sqActDefect P₂.isMod a p.toNat y) ∈ T :=
    sqActDefect_mem_lower (A := P₂.isMod) P₂.isMod.toAdmissible rfl ha hy T₂ hT₂
  have heq := sqAct_neg_two_eq P₂.isMod a p.toNat y
  have : mode (P₂.isMod.YM a) (-2) y =
      sqAct P₂.isMod a p.toNat (-2) y - sqActDefect P₂.isMod a p.toNat y := by
    rw [heq]; abel
  rw [this, map_sub]
  exact T.sub_mem hsq hdef

include hRe hRp in
/-- **Two-slot C₂ induction for a vector of Ward bilinear maps** (common coefficients). -/
theorem wardV_mem_span_pairs {lam : ℂ} (hS : WardBilinearV S lam)
    {U : Set P₁.carrier} {Z : Set P₂.carrier}
    (hU : ∀ u ∈ U, ∃ n, u ∈ P₁.isMod.toAdmissible.lev n)
    (hZ : ∀ z ∈ Z, ∃ n, z ∈ P₂.isMod.toAdmissible.lev n)
    (htopA : (⊤ : Submodule ℂ P₁.carrier) =
      Submodule.span ℂ U ⊔ C2M P₁.isMod.toAdmissible.toWeakModule)
    (htopB : (⊤ : Submodule ℂ P₂.carrier) =
      Submodule.span ℂ Z ⊔ C2M P₂.isMod.toAdmissible.toWeakModule)
    (x : P₁.carrier) (y : P₂.carrier) :
    S x y ∈ Submodule.span (↥R) {v | ∃ u ∈ U, ∃ z ∈ Z, S u z = v} := by
  set A := P₁.isMod.toAdmissible
  set B := P₂.isMod.toAdmissible
  set T : Submodule (↥R) (ι → R2) := Submodule.span (↥R) {v | ∃ u ∈ U, ∃ z ∈ Z, S u z = v}
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
      apply VOA.Huang.GenusTwoPoint.QEquation.homogeneous_mem_of_C2 A (S.flip y) T
        hU htopA n ?_ ?_ hx
      · intro u hu hun
        apply VOA.Huang.GenusTwoPoint.QEquation.homogeneous_mem_of_C2 B (S u) T
          hZ htopB m ?_ ?_ hy
        · intro z hz _
          exact Submodule.subset_span ⟨u, hu, z, hz, rfl⟩
        · intro a p j v ha hv hj
          exact wardV_negTwo_right_mem R hRe hRp S hS T ha hun hv
            (fun n' m' h x' hx' y' hy' => hlow n' m' (by omega) x' hx' y' hy')
      · intro a p i u ha hu hi
        exact wardV_negTwo_left_mem R hRe hRp S hS T ha hu hy
          (fun n' m' h x' hx' y' hy' => hlow n' m' (by omega) x' hx' y' hy')
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

include hRe hRp in
/-- Finitely many generators over the kernel subalgebra, common to all components. -/
theorem wardV_exists_generators {lam : ℂ} (hS : WardBilinearV S lam) (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) :
    ∃ (U : Finset P₁.carrier) (Z : Finset P₂.carrier), ∀ x y,
      S x y ∈ Submodule.span (↥R) {v | ∃ u ∈ (U : Set P₁.carrier),
        ∃ z ∈ (Z : Set P₂.carrier), S u z = v} := by
  classical
  obtain ⟨U, hU, htopU⟩ := exists_finset_homog (N := P₁.isMod.toAdmissible)
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₁)
  obtain ⟨Z, hZ, htopZ⟩ := exists_finset_homog (N := P₂.isMod.toAdmissible)
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₂)
  exact ⟨U, Z, fun x y => wardV_mem_span_pairs R hRe hRp S hS hU hZ htopU htopZ x y⟩

include hRe hRp in
/-- The span of all values is closed under `Θ_lam` (componentwise). -/
theorem wardV_theta_mem {lam : ℂ} (hS : WardBilinearV S lam) (T : Submodule (↥R) (ι → R2))
    (hT : ∀ x y, S x y ∈ T) (x : P₁.carrier) (y : P₂.carrier) :
    thetaV lam (S x y) ∈ T := by
  obtain ⟨K, he⟩ := wardV_mixed_eq S hS x y
  rw [he]
  refine T.sub_mem (T.sub_mem (hT _ _) ?_) ?_
  · exact T.sum_mem fun m _ => smul_mem_spanV R (hRe _) (hT _ _)
  · refine T.sum_mem fun m _ => smul_mem_spanV R ?_ (hT _ _)
    refine add_mem (hRp m) ?_
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact zero_mem _

end Span

end VOA.Huang.GenusOneWard
