import VOA.Huang.GenusOneG1Growth
import VOA.Huang.GenusOneWardGeneral
import VOA.Huang.GenusTwoPointC2Reduction
import VOA.Huang.GenusOneFinite

/-!
# Formal two-slot C₂ reduction of the genus-one two-point series over `Sub2`

The collected minus-two Ward identities `leftLHS_evZero`, `rightLHS_evZero` hold
in `ℂ⟦u⟧⟦t⟧` with coefficients `eis`, `piK` in the subalgebra `Sub2` of
two-variable subexponential series. Huang's two-slot C₂ induction (on the total
level of the two insertions), run with Zhu's square-bracket modes and their
triangularity `a[−2] = a₍₋₂₎ + (lower)`, shows that the bilinear series
`Phi Y₁ Y₂ x y` all lie in the `Sub2`-span of finitely many of them. The mixed
omega identity `mixedLHS_evZero` then closes this span under `Θ_{h−c/24}`.

Everything here is formal: no evaluation, no convergence, no branch.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.FusionC2 VOA.Huang.BottomRecovery
open VOA.Huang.GenusOne (sqAct sqActDefect sqAct_neg_two_eq sqAct_mem_lower
  sqActDefect_mem_lower)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

theorem Sub2.mul_mem_span {T : Submodule (↥Sub2) R2} {c : R2} (hc : c ∈ Sub2) {v : R2}
    (hv : v ∈ T) : c * v ∈ T := by
  have h := T.smul_mem (⟨c, hc⟩ : ↥Sub2) hv
  rwa [Subalgebra.smul_def, smul_eq_mul] at h

section Reduction
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

/-- Left minus-two reduction step. -/
theorem phi_negTwo_left_mem (T : Submodule (↥Sub2) R2) {a : V} {p i j : ℤ}
    (ha : a ∈ W.grading p) {x : P₁.carrier} (hx : x ∈ P₁.isMod.toAdmissible.lev i)
    {y : P₂.carrier} (hy : y ∈ P₂.isMod.toAdmissible.lev j)
    (hlow : ∀ n' m' : ℤ, n' + m' < i + p + 1 + j → ∀ x' ∈ P₁.isMod.toAdmissible.lev n',
      ∀ y' ∈ P₂.isMod.toAdmissible.lev m', Phi Y₁ Y₂ x' y' ∈ T) :
    Phi Y₁ Y₂ (mode (P₁.isMod.YM a) (-2) x) y ∈ T := by
  let T₁ : Submodule ℂ P₁.carrier := (T.restrictScalars ℂ).comap ((Phi Y₁ Y₂).flip y)
  let T₂ : Submodule ℂ P₂.carrier := (T.restrictScalars ℂ).comap (Phi Y₁ Y₂ x)
  have hT₁ : ∀ d : ℤ, d < i + p + 1 → P₁.isMod.toAdmissible.lev d ≤ T₁ :=
    fun d hd x' hx' => hlow d j (by omega) x' hx' y hy
  have hT₂ : ∀ d : ℤ, d < j + p + 1 → P₂.isMod.toAdmissible.lev d ≤ T₂ :=
    fun d hd y' hy' => hlow i d (by omega) x hx y' hy'
  obtain ⟨K, hK⟩ := leftLHS_evZero Y₁ Y₂ a x y
  have h0 := hK K le_rfl
  simp only [leftLHS, GenusOne.SquareModule.sqMode_of_mem_grading _ ha] at h0
  have hS1 : ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) * Phi Y₁ Y₂ (sqAct P₁.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) x) y) ∈ T := by
    refine T.sum_mem fun m _ => T.smul_of_tower_mem _ (Sub2.mul_mem_span (eis_mem_Sub2 _) ?_)
    exact sqAct_mem_lower (A := P₁.isMod) P₁.isMod.toAdmissible rfl ha hx (by omega) T₁ hT₁
  have hS2 : ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
      if m = 0 then eis 1 else 0) *
        Phi Y₁ Y₂ x (sqAct P₂.isMod a p.toNat (m : ℤ) y) ∈ T := by
    refine T.sum_mem fun m _ => Sub2.mul_mem_span ?_ ?_
    · refine Sub2.sub_mem (Sub2.smul_mem (piK_mem_Sub2 _) _) ?_
      split_ifs
      · exact eis_mem_Sub2 1
      · exact Sub2.zero_mem
    · exact sqAct_mem_lower (A := P₂.isMod) P₂.isMod.toAdmissible rfl ha hy (by omega) T₂ hT₂
  have hsq : Phi Y₁ Y₂ (sqAct P₁.isMod a p.toNat (-2) x) y ∈ T := by
    have he : Phi Y₁ Y₂ (sqAct P₁.isMod a p.toNat (-2) x) y =
        -(∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
          (eis (m + 2) * Phi Y₁ Y₂ (sqAct P₁.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) x) y)) -
        ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
          if m = 0 then eis 1 else 0) *
            Phi Y₁ Y₂ x (sqAct P₂.isMod a p.toNat (m : ℤ) y) := by
      linear_combination h0
    rw [he]
    exact T.sub_mem (T.neg_mem hS1) hS2
  have hdef : Phi Y₁ Y₂ (sqActDefect P₁.isMod a p.toNat x) y ∈ T :=
    sqActDefect_mem_lower (A := P₁.isMod) P₁.isMod.toAdmissible rfl ha hx T₁ hT₁
  have heq := sqAct_neg_two_eq P₁.isMod a p.toNat x
  have : mode (P₁.isMod.YM a) (-2) x =
      sqAct P₁.isMod a p.toNat (-2) x - sqActDefect P₁.isMod a p.toNat x := by
    rw [heq]; abel
  rw [this, map_sub, LinearMap.sub_apply]
  exact T.sub_mem hsq hdef

/-- Right minus-two reduction step. -/
theorem phi_negTwo_right_mem (T : Submodule (↥Sub2) R2) {a : V} {p i j : ℤ}
    (ha : a ∈ W.grading p) {x : P₁.carrier} (hx : x ∈ P₁.isMod.toAdmissible.lev i)
    {y : P₂.carrier} (hy : y ∈ P₂.isMod.toAdmissible.lev j)
    (hlow : ∀ n' m' : ℤ, n' + m' < i + (j + p + 1) → ∀ x' ∈ P₁.isMod.toAdmissible.lev n',
      ∀ y' ∈ P₂.isMod.toAdmissible.lev m', Phi Y₁ Y₂ x' y' ∈ T) :
    Phi Y₁ Y₂ x (mode (P₂.isMod.YM a) (-2) y) ∈ T := by
  let T₁ : Submodule ℂ P₁.carrier := (T.restrictScalars ℂ).comap ((Phi Y₁ Y₂).flip y)
  let T₂ : Submodule ℂ P₂.carrier := (T.restrictScalars ℂ).comap (Phi Y₁ Y₂ x)
  have hT₁ : ∀ d : ℤ, d < i + p + 1 → P₁.isMod.toAdmissible.lev d ≤ T₁ :=
    fun d hd x' hx' => hlow d j (by omega) x' hx' y hy
  have hT₂ : ∀ d : ℤ, d < j + p + 1 → P₂.isMod.toAdmissible.lev d ≤ T₂ :=
    fun d hd y' hy' => hlow i d (by omega) x hx y' hy'
  obtain ⟨K, hK⟩ := rightLHS_evZero Y₁ Y₂ a x y
  have h0 := hK K le_rfl
  simp only [rightLHS, GenusOne.SquareModule.sqMode_of_mem_grading _ ha] at h0
  have hS1 : ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
      (eis (m + 2) * Phi Y₁ Y₂ x (sqAct P₂.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) y)) ∈ T := by
    refine T.sum_mem fun m _ => T.smul_of_tower_mem _ (Sub2.mul_mem_span (eis_mem_Sub2 _) ?_)
    exact sqAct_mem_lower (A := P₂.isMod) P₂.isMod.toAdmissible rfl ha hy (by omega) T₂ hT₂
  have hS2 : ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
      if m = 0 then eis 1 else 0) *
        Phi Y₁ Y₂ (sqAct P₁.isMod a p.toNat (m : ℤ) x) y ∈ T := by
    refine T.sum_mem fun m _ => Sub2.mul_mem_span ?_ ?_
    · refine Sub2.sub_mem (Sub2.smul_mem (Sub2.smul_mem (piK_mem_Sub2 _) _) _) ?_
      split_ifs
      · exact eis_mem_Sub2 1
      · exact Sub2.zero_mem
    · exact sqAct_mem_lower (A := P₁.isMod) P₁.isMod.toAdmissible rfl ha hx (by omega) T₁ hT₁
  have hsq : Phi Y₁ Y₂ x (sqAct P₂.isMod a p.toNat (-2) y) ∈ T := by
    have he : Phi Y₁ Y₂ x (sqAct P₂.isMod a p.toNat (-2) y) =
        -(∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) •
          (eis (m + 2) * Phi Y₁ Y₂ x (sqAct P₂.isMod a p.toNat ((2 * m + 2 : ℕ) : ℤ) y))) -
        ∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
          if m = 0 then eis 1 else 0) *
            Phi Y₁ Y₂ (sqAct P₁.isMod a p.toNat (m : ℤ) x) y := by
      linear_combination h0
    rw [he]
    exact T.sub_mem (T.neg_mem hS1) hS2
  have hdef : Phi Y₁ Y₂ x (sqActDefect P₂.isMod a p.toNat y) ∈ T :=
    sqActDefect_mem_lower (A := P₂.isMod) P₂.isMod.toAdmissible rfl ha hy T₂ hT₂
  have heq := sqAct_neg_two_eq P₂.isMod a p.toNat y
  have : mode (P₂.isMod.YM a) (-2) y =
      sqAct P₂.isMod a p.toNat (-2) y - sqActDefect P₂.isMod a p.toNat y := by
    rw [heq]; abel
  rw [this, map_sub]
  exact T.sub_mem hsq hdef

/-- **Huang's two-slot C₂ induction, square-bracket form, over `Sub2`.** -/
theorem phi_mem_span_pairs {U : Set P₁.carrier} {Z : Set P₂.carrier}
    (hU : ∀ u ∈ U, ∃ n, u ∈ P₁.isMod.toAdmissible.lev n)
    (hZ : ∀ z ∈ Z, ∃ n, z ∈ P₂.isMod.toAdmissible.lev n)
    (htopA : (⊤ : Submodule ℂ P₁.carrier) =
      Submodule.span ℂ U ⊔ C2M P₁.isMod.toAdmissible.toWeakModule)
    (htopB : (⊤ : Submodule ℂ P₂.carrier) =
      Submodule.span ℂ Z ⊔ C2M P₂.isMod.toAdmissible.toWeakModule)
    (x : P₁.carrier) (y : P₂.carrier) :
    Phi Y₁ Y₂ x y ∈ Submodule.span (↥Sub2) {v | ∃ u ∈ U, ∃ z ∈ Z, Phi Y₁ Y₂ u z = v} := by
  set A := P₁.isMod.toAdmissible
  set B := P₂.isMod.toAdmissible
  set T : Submodule (↥Sub2) R2 :=
    Submodule.span (↥Sub2) {v | ∃ u ∈ U, ∃ z ∈ Z, Phi Y₁ Y₂ u z = v}
  have hlev : ∀ K : ℕ, ∀ (n m : ℤ), n + m = K → ∀ x ∈ A.lev n, ∀ y ∈ B.lev m,
      Phi Y₁ Y₂ x y ∈ T := by
    intro K
    induction K using Nat.strong_induction_on with
    | _ K ih =>
      intro n m hnm x hx y hy
      have hlow : ∀ (n' m' : ℤ), n' + m' < K → ∀ x' ∈ A.lev n', ∀ y' ∈ B.lev m',
          Phi Y₁ Y₂ x' y' ∈ T := by
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
      apply VOA.Huang.GenusTwoPoint.QEquation.homogeneous_mem_of_C2 A ((Phi Y₁ Y₂).flip y) T
        hU htopA n ?_ ?_ hx
      · intro u hu hun
        apply VOA.Huang.GenusTwoPoint.QEquation.homogeneous_mem_of_C2 B (Phi Y₁ Y₂ u) T
          hZ htopB m ?_ ?_ hy
        · intro z hz _
          exact Submodule.subset_span ⟨u, hu, z, hz, rfl⟩
        · intro a p j v ha hv hj
          exact phi_negTwo_right_mem Y₁ Y₂ T ha hun hv
            (fun n' m' h x' hx' y' hy' => hlow n' m' (by omega) x' hx' y' hy')
      · intro a p i u ha hu hi
        exact phi_negTwo_left_mem Y₁ Y₂ T ha hu hy
          (fun n' m' h x' hx' y' hy' => hlow n' m' (by omega) x' hx' y' hy')
  have hall : ∀ (n m : ℤ), ∀ x ∈ A.lev n, ∀ y ∈ B.lev m, Phi Y₁ Y₂ x y ∈ T := by
    intro n m x hx y hy
    by_cases hn : n < 0
    · rw [A.lev_eq_bot_of_neg n hn, Submodule.mem_bot] at hx
      simp only [hx, map_zero, LinearMap.zero_apply]; exact T.zero_mem
    by_cases hm : m < 0
    · rw [B.lev_eq_bot_of_neg m hm, Submodule.mem_bot] at hy
      simp only [hy, map_zero]; exact T.zero_mem
    exact hlev (n + m).toNat n m (by omega) x hx y hy
  refine induction_lev A (motive := fun x => ∀ y, Phi Y₁ Y₂ x y ∈ T) x ?_ ?_ ?_ y
  · intro y; simp only [map_zero, LinearMap.zero_apply]; exact T.zero_mem
  · intro x x' hx hx' y
    simpa only [map_add, LinearMap.add_apply] using T.add_mem (hx y) (hx' y)
  · intro n x hx y
    refine induction_lev B (motive := fun y => Phi Y₁ Y₂ x y ∈ T) y ?_ ?_ ?_
    · simpa only [map_zero] using T.zero_mem
    · intro y y' hy hy'; simpa only [map_add] using T.add_mem hy hy'
    · intro m y hy; exact hall n m x hx y hy

end Reduction

end VOA.Huang.GenusOneWard
