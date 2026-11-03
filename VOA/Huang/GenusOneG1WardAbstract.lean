import VOA.Huang.GenusOneG1ProductGrowth

/-!
# Abstract Ward bilinear maps: C₂ reduction and Euler closure over any kernel subalgebra

`WardBilinear S lam` says that a bilinear map `S : P₁ → P₂ → ℂ⟦u⟧⟦t⟧` satisfies the
three formal genus-one Ward identities (collected minus-two in both slots, mixed
omega with Euler parameter `lam`), exactly as the two-point series `Phi Y₁ Y₂` does
(`wardBilinear_Phi`). The identities are linear with universal kernels, so finite sums
of product channels with the same insertion modules and the same traced module are
again Ward bilinear (`WardBilinear.add`, `WardBilinear.finset_sum`) — e.g. the
product-channel sum attached to an iterate by
`coefficientAssociativityConverse_of_stronglyRational_pbw`.

For ANY subalgebra `R ⊆ ℂ⟦u⟧⟦t⟧` containing the kernels `eis j`, `piK m`, the C₂
induction puts every value of `S` in the `R`-span of finitely many
(`ward_exists_generators`), and that span is closed under `Θ_lam`
(`ward_theta_mem`). With `R = Sub2` and fixed-level row bounds this gives
`ward_mem_Sub2`. This is the interface for step 2 of the iterate-transport argument
(a smaller subalgebra of `t`-rational kernels).
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
  {P₁ P₂ N Q : LWModule W}

section Abstract
variable (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2)

/-- The left minus-two Ward expression of `S`. -/
def leftExpr (b : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) : R2 :=
  S (GenusOne.SquareModule.sqMode P₁.isMod (-2) b x) y +
    ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) * S (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 2 : ℕ) : ℤ) b x) y) +
    ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) - if m = 0 then eis 1 else 0) *
      S x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) b y)

/-- The right minus-two Ward expression of `S`. -/
def rightExpr (b : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) : R2 :=
  S x (GenusOne.SquareModule.sqMode P₂.isMod (-2) b y) +
    ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) * S x (GenusOne.SquareModule.sqMode P₂.isMod ((2 * m + 2 : ℕ) : ℤ) b y)) +
    ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
        if m = 0 then eis 1 else 0) *
      S (GenusOne.SquareModule.sqMode P₁.isMod (m : ℤ) b x) y

/-- The mixed omega expression of `S` with Euler parameter `lam`. -/
def mixedExpr (lam : ℂ) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) : R2 :=
  S (GenusOne.SquareModule.sqMode P₁.isMod (-1) (shiftedOmega W) x) y -
    (thetaR2 lam (S x y) +
      ∑ m ∈ Finset.range K, eis (m + 1) *
        S (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 1 : ℕ) : ℤ) (shiftedOmega W) x) y +
      ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
        S x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) (shiftedOmega W) y))

/-- The three formal genus-one Ward identities. -/
def WardBilinear (lam : ℂ) : Prop :=
  (∀ b x y, EvZero (leftExpr S b x y)) ∧ (∀ b x y, EvZero (rightExpr S b x y)) ∧
    ∀ x y, EvZero (mixedExpr S lam x y)

end Abstract

/-- The genus-one two-point series is Ward bilinear. -/
theorem wardBilinear_Phi (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) :
    WardBilinear (Phi Y₁ Y₂) (N.h - W.centralCharge / 24) :=
  ⟨leftLHS_evZero Y₁ Y₂, rightLHS_evZero Y₁ Y₂, mixedLHS_evZero Y₁ Y₂⟩

theorem leftExpr_add (S T : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2) (b : V) (x : P₁.carrier)
    (y : P₂.carrier) (K : ℕ) :
    leftExpr (S + T) b x y K = leftExpr S b x y K + leftExpr T b x y K := by
  simp only [leftExpr, LinearMap.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  abel

theorem rightExpr_add (S T : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2) (b : V) (x : P₁.carrier)
    (y : P₂.carrier) (K : ℕ) :
    rightExpr (S + T) b x y K = rightExpr S b x y K + rightExpr T b x y K := by
  simp only [rightExpr, LinearMap.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  abel

theorem mixedExpr_add (S T : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2) (lam : ℂ) (x : P₁.carrier)
    (y : P₂.carrier) (K : ℕ) :
    mixedExpr (S + T) lam x y K = mixedExpr S lam x y K + mixedExpr T lam x y K := by
  simp only [mixedExpr, LinearMap.add_apply, mul_add, Finset.sum_add_distrib, thetaR2_add]
  abel

theorem WardBilinear.add {S T : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2} {lam : ℂ}
    (hS : WardBilinear S lam) (hT : WardBilinear T lam) : WardBilinear (S + T) lam := by
  refine ⟨fun b x y => ?_, fun b x y => ?_, fun x y => ?_⟩
  · rw [show leftExpr (S + T) b x y = fun K => leftExpr S b x y K + leftExpr T b x y K
      from funext fun K => leftExpr_add S T b x y K]
    exact (hS.1 b x y).add (hT.1 b x y)
  · rw [show rightExpr (S + T) b x y = fun K => rightExpr S b x y K + rightExpr T b x y K
      from funext fun K => rightExpr_add S T b x y K]
    exact (hS.2.1 b x y).add (hT.2.1 b x y)
  · rw [show mixedExpr (S + T) lam x y = fun K => mixedExpr S lam x y K + mixedExpr T lam x y K
      from funext fun K => mixedExpr_add S T lam x y K]
    exact (hS.2.2 x y).add (hT.2.2 x y)

theorem wardBilinear_zero (lam : ℂ) :
    WardBilinear (0 : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2) lam := by
  have ht : thetaR2 lam 0 = 0 := ext2 fun n k => by simp [thetaR2]
  refine ⟨fun b x y => evZero_of_eq_zero fun K => ?_, fun b x y => evZero_of_eq_zero fun K => ?_,
    fun x y => evZero_of_eq_zero fun K => ?_⟩
  · simp [leftExpr]
  · simp [rightExpr]
  · simp [mixedExpr, ht]

/-- Finite sums of Ward bilinear maps with a common Euler parameter. -/
theorem WardBilinear.finset_sum {ι : Type*} (s : Finset ι)
    {S : ι → P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2} {lam : ℂ}
    (h : ∀ j ∈ s, WardBilinear (S j) lam) : WardBilinear (∑ j ∈ s, S j) lam := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wardBilinear_zero (P₁ := P₁) (P₂ := P₂) lam
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## C₂ reduction over a kernel subalgebra -/

section Span
variable (R : Subalgebra ℂ R2) (hRe : ∀ j, eis j ∈ R) (hRp : ∀ m, piK m ∈ R)
  (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2)

theorem Subalgebra.mul_mem_span' {T : Submodule (↥R) R2} {c : R2} (hc : c ∈ R) {v : R2}
    (hv : v ∈ T) : c * v ∈ T := by
  have h := T.smul_mem (⟨c, hc⟩ : ↥R) hv
  rwa [Subalgebra.smul_def, smul_eq_mul] at h

include hRe hRp in
/-- Left minus-two reduction step for a Ward bilinear map. -/
theorem ward_negTwo_left_mem {lam : ℂ} (hS : WardBilinear S lam) (T : Submodule (↥R) R2)
    {a : V} {p i j : ℤ}
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
  obtain ⟨K, hK⟩ := hS.1 a x y
  have h0 := hK K le_rfl
  simp only [leftExpr, GenusOne.SquareModule.sqMode_of_mem_grading _ ha] at h0
  have hS1 : ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) * S (sqAct P₁.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) x) y) ∈ T := by
    refine T.sum_mem fun m _ => T.smul_of_tower_mem _
      (Subalgebra.mul_mem_span' R (hRe _) ?_)
    exact sqAct_mem_lower (A := P₁.isMod) P₁.isMod.toAdmissible rfl ha hx (by omega) T₁ hT₁
  have hS2 : ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
      if m = 0 then eis 1 else 0) *
        S x (sqAct P₂.isMod a p.toNat (m : ℤ) y) ∈ T := by
    refine T.sum_mem fun m _ => Subalgebra.mul_mem_span' R ?_ ?_
    · refine sub_mem (Subalgebra.smul_mem _ (hRp _) _) ?_
      split_ifs
      · exact hRe 1
      · exact zero_mem _
    · exact sqAct_mem_lower (A := P₂.isMod) P₂.isMod.toAdmissible rfl ha hy (by omega) T₂ hT₂
  have hsq : S (sqAct P₁.isMod a p.toNat (-2) x) y ∈ T := by
    have he : S (sqAct P₁.isMod a p.toNat (-2) x) y =
        -(∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
          (eis (m + 2) * S (sqAct P₁.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) x) y)) -
        ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
          if m = 0 then eis 1 else 0) *
            S x (sqAct P₂.isMod a p.toNat (m : ℤ) y) := by
      linear_combination h0
    rw [he]
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
/-- Right minus-two reduction step for a Ward bilinear map. -/
theorem ward_negTwo_right_mem {lam : ℂ} (hS : WardBilinear S lam) (T : Submodule (↥R) R2)
    {a : V} {p i j : ℤ}
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
  obtain ⟨K, hK⟩ := hS.2.1 a x y
  have h0 := hK K le_rfl
  simp only [rightExpr, GenusOne.SquareModule.sqMode_of_mem_grading _ ha] at h0
  have hS1 : ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) * S x (sqAct P₂.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) y)) ∈ T := by
    refine T.sum_mem fun m _ => T.smul_of_tower_mem _
      (Subalgebra.mul_mem_span' R (hRe _) ?_)
    exact sqAct_mem_lower (A := P₂.isMod) P₂.isMod.toAdmissible rfl ha hy (by omega) T₂ hT₂
  have hS2 : ∑ m ∈ Finset.range K,
      (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
        if m = 0 then eis 1 else 0) *
        S (sqAct P₁.isMod a p.toNat (m : ℤ) x) y ∈ T := by
    refine T.sum_mem fun m _ => Subalgebra.mul_mem_span' R ?_ ?_
    · refine sub_mem (Subalgebra.smul_mem _ (Subalgebra.smul_mem _ (hRp _) _) _) ?_
      split_ifs
      · exact hRe 1
      · exact zero_mem _
    · exact sqAct_mem_lower (A := P₁.isMod) P₁.isMod.toAdmissible rfl ha hx (by omega) T₁ hT₁
  have hsq : S x (sqAct P₂.isMod a p.toNat (-2) y) ∈ T := by
    have he : S x (sqAct P₂.isMod a p.toNat (-2) y) =
        -(∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
          (eis (m + 2) * S x (sqAct P₂.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) y))) -
        ∑ m ∈ Finset.range K,
          (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
            if m = 0 then eis 1 else 0) *
            S (sqAct P₁.isMod a p.toNat (m : ℤ) x) y := by
      linear_combination h0
    rw [he]
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
/-- **Two-slot C₂ induction for any Ward bilinear map over any kernel subalgebra.** -/
theorem ward_mem_span_pairs {lam : ℂ} (hS : WardBilinear S lam)
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
  set T : Submodule (↥R) R2 := Submodule.span (↥R) {v | ∃ u ∈ U, ∃ z ∈ Z, S u z = v}
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
          exact ward_negTwo_right_mem R hRe hRp S hS T ha hun hv
            (fun n' m' h x' hx' y' hy' => hlow n' m' (by omega) x' hx' y' hy')
      · intro a p i u ha hu hi
        exact ward_negTwo_left_mem R hRe hRp S hS T ha hu hy
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
/-- Finitely many generators over the kernel subalgebra. -/
theorem ward_exists_generators {lam : ℂ} (hS : WardBilinear S lam) (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) :
    ∃ (U : Finset P₁.carrier) (Z : Finset P₂.carrier), ∀ x y,
      S x y ∈ Submodule.span (↥R) (Set.range fun k : U × Z => S k.1.val k.2.val) := by
  classical
  obtain ⟨U, hU, htopU⟩ := exists_finset_homog (N := P₁.isMod.toAdmissible)
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₁)
  obtain ⟨Z, hZ, htopZ⟩ := exists_finset_homog (N := P₂.isMod.toAdmissible)
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₂)
  refine ⟨U, Z, fun x y => ?_⟩
  have h := ward_mem_span_pairs R hRe hRp S hS hU hZ htopU htopZ x y
  have he : {v | ∃ u ∈ (U : Set P₁.carrier), ∃ z ∈ (Z : Set P₂.carrier), S u z = v} =
      Set.range (fun k : U × Z => S k.1.val k.2.val) := by
    ext v
    constructor
    · rintro ⟨u, hu, z, hz, rfl⟩; exact ⟨(⟨u, hu⟩, ⟨z, hz⟩), rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k.1.val, k.1.property, k.2.val, k.2.property, rfl⟩
  rwa [he] at h

include hRe hRp in
/-- The span of all values is closed under `Θ_lam`. -/
theorem ward_theta_mem {lam : ℂ} (hS : WardBilinear S lam) (T : Submodule (↥R) R2)
    (hT : ∀ x y, S x y ∈ T) (x : P₁.carrier) (y : P₂.carrier) :
    thetaR2 lam (S x y) ∈ T := by
  obtain ⟨K, hK⟩ := hS.2.2 x y
  have h0 := hK K le_rfl
  unfold mixedExpr at h0
  have he : thetaR2 lam (S x y) =
      S (GenusOne.SquareModule.sqMode P₁.isMod (-1) (shiftedOmega W) x) y -
        ∑ m ∈ Finset.range K, eis (m + 1) *
          S (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 1 : ℕ) : ℤ)
            (shiftedOmega W) x) y -
        ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
          S x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) (shiftedOmega W) y) := by
    linear_combination -h0
  rw [he]
  refine T.sub_mem (T.sub_mem (hT _ _) ?_) ?_
  · exact T.sum_mem fun m _ => Subalgebra.mul_mem_span' R (hRe _) (hT _ _)
  · refine T.sum_mem fun m _ => Subalgebra.mul_mem_span' R ?_ (hT _ _)
    refine add_mem (hRp m) ?_
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact zero_mem _

end Span

/-- **Every Ward bilinear map with genus-zero row bounds is two-variable
subexponential** (generalizes `phi_mem_Sub2` to sums of channels). -/
theorem ward_mem_Sub2 {S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] R2} {lam : ℂ}
    (hS : WardBilinear S lam) (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (hrow : ∀ x y n, ∀ b : ℝ, 1 < b → ∃ B : ℝ, ∀ k, ‖c2 (S x y) n k‖ ≤ B * b ^ k)
    (x : P₁.carrier) (y : P₂.carrier) : S x y ∈ Sub2 := by
  classical
  obtain ⟨U, Z, hUZ⟩ := ward_exists_generators Sub2 eis_mem_Sub2 piK_mem_Sub2 S hS hV i₁ i₂
  set T := Submodule.span (↥Sub2) (Set.range fun k : U × Z => S k.1.val k.2.val)
  have hθ : ∀ k : U × Z, ∃ c : U × Z → ↥Sub2,
      ∑ l, c l • S l.1.val l.2.val = thetaR2 lam (S k.1.val k.2.val) := fun k =>
    (Submodule.mem_span_range_iff_exists_fun (↥Sub2)).mp
      (ward_theta_mem Sub2 eis_mem_Sub2 piK_mem_Sub2 S hS T hUZ k.1.val k.2.val)
  choose c hc using hθ
  have hgen : ∀ k : U × Z, S k.1.val k.2.val ∈ Sub2 := by
    refine geo2_of_euler_system (lam := lam) (f := fun k : U × Z => S k.1.val k.2.val)
      (Cm := fun k l => ((c k l : ↥Sub2) : R2)) (fun k l => (c k l).property) ?_ ?_
    · intro k
      rw [← hc k]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
    · intro k n b hb
      exact hrow _ _ n b hb
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Sub2)).mp (hUZ x y)
  rw [← hd]
  refine Subalgebra.sum_mem _ fun l _ => ?_
  rw [Subalgebra.smul_def, smul_eq_mul]
  exact Subalgebra.mul_mem _ (d l).property (hgen l)

end VOA.Huang.GenusOneWard
