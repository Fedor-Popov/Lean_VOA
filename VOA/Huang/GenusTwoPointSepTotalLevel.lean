import VOA.Huang.GenusTwoPointSepSpatialFinite
import VOA.Huang.GenusTwoPointSepFlowTruncation

/-!
# Formal collection at fixed total sewing level

The two nonnegative levels are the traced and intermediate levels. Their sum
has finite fibers. This proves local finiteness of the joint level/mode family
and telescoping in its formal completion, without analytic convergence.
The spatial translation law is not the elliptic square minus-two Ward law.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators

/-- Local finiteness in total traced-plus-intermediate level. Fixing only the
traced level would not give this condition. -/
def TotalLevelFinite (f : ℕ → ℕ → ℤ → ℂ) : Prop :=
  ∀ d : ℕ, (Function.support (fun p : (ℕ × ℕ) × ℤ =>
    if p.1.1 + p.1.2 = d then f p.1.1 p.1.2 p.2 else 0)).Finite

/-- Finitely many level pairs in each total degree turn rowwise finite mode
support into joint finite support. No uniform cutoff over all levels is used. -/
theorem totalLevelFinite_of_rows (f : ℕ → ℕ → ℤ → ℂ)
    (hf : ∀ n k, (Function.support (f n k)).Finite) : TotalLevelFinite f := by
  intro d
  refine ((Finset.antidiagonal d).finite_toSet.biUnion fun p _ =>
    (hf p.1 p.2).image (fun j => (p, j))).subset ?_
  intro p hp
  have hd : p.1.1 + p.1.2 = d := by
    by_contra hd
    exact hp (if_neg hd)
  have hj : p.2 ∈ Function.support (f p.1.1 p.1.2) := by
    simpa only [Function.mem_support, if_pos hd] using hp
  exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr
    ⟨Finset.mem_antidiagonal.mpr hd, ⟨p.2, hj, rfl⟩⟩⟩

theorem TotalLevelFinite.row {f : ℕ → ℕ → ℤ → ℂ} (hf : TotalLevelFinite f)
    (n k : ℕ) : (Function.support (f n k)).Finite := by
  have hi : Function.Injective (fun j : ℤ => ((n, k), j)) :=
    fun _ _ h => (Prod.mk.inj h).2
  refine ((hf (n + k)).preimage hi.injOn).subset ?_
  intro j hj
  simpa only [Set.mem_preimage, Function.mem_support, if_pos rfl] using hj

/-- Formal collection retaining both independent levels. The total-level
filtration justifies collection; it does not identify the two formal variables. -/
def modeBiseries (f : ℕ → ℕ → ℤ → ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun n => PowerSeries.mk fun k => ∑' j, f n k j

@[simp] theorem coeff_modeBiseries (f : ℕ → ℕ → ℤ → ℂ) (n k : ℕ) :
    PowerSeries.coeff k (PowerSeries.coeff n (modeBiseries f)) = ∑' j, f n k j := by
  simp [modeBiseries]

/-- Telescoping in the completed bigraded coefficient algebra, with both
variables retained. The finite-support proof precedes every reindexing. -/
theorem modeBiseries_mode_difference (b : ℕ → ℕ → ℂ)
    (f : ℕ → ℕ → ℤ → ℂ) (hf : TotalLevelFinite f) :
    modeBiseries (fun n k j =>
      (b n k + j + 1) * f n k j - (b n k + j) * f n k (j - 1)) = 0 := by
  ext n k
  rw [coeff_modeBiseries, map_zero, map_zero]
  apply tsum_mode_difference
  apply summable_of_hasFiniteSupport
  exact (hf.row n k).subset fun j hj hz => hj (by simp only [hz, mul_zero])

/-- The complete spatial coefficient identity after bigraded collection. -/
theorem modeBiseries_spatial_law (b : ℕ → ℕ → ℂ) (c : ℂ)
    (f d l : ℕ → ℕ → ℤ → ℂ) (hf : TotalLevelFinite f) (hd : TotalLevelFinite d)
    (hl : ∀ n k j, l n k j = c *
      (d n k j + (b n k + j + 1) * f n k j - (b n k + j) * f n k (j - 1))) :
    modeBiseries l = c • modeBiseries d := by
  ext n k
  simp only [PowerSeries.coeff_smul, coeff_modeBiseries, smul_eq_mul]
  exact (sum_spatial_law (b n k) c (f n k) (d n k) (l n k)
    (summable_of_hasFiniteSupport ((hf.row n k).subset
      fun j hj hz => hj (by simp only [hz, mul_zero])))
    (summable_of_hasFiniteSupport (hd.row n k)) (hl n k)).2

/-- The formal sum after giving both sewing levels positive degree. The mode
sum is certified finite whenever `TotalLevelFinite` is supplied. -/
def totalLevelSeries (f : ℕ → ℕ → ℤ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun d => ∑ p ∈ Finset.antidiagonal d, ∑' j, f p.1 p.2 j

@[simp] theorem coeff_totalLevelSeries (f : ℕ → ℕ → ℤ → ℂ) (d : ℕ) :
    PowerSeries.coeff d (totalLevelSeries f) =
      ∑ p ∈ Finset.antidiagonal d, ∑' j, f p.1 p.2 j := by
  simp [totalLevelSeries]

/-- The shifted-mode boundary cancels in every formal coefficient. -/
theorem totalLevelSeries_mode_difference (b : ℕ → ℕ → ℂ)
    (f : ℕ → ℕ → ℤ → ℂ) (hf : TotalLevelFinite f) :
    totalLevelSeries (fun n k j =>
      (b n k + j + 1) * f n k j - (b n k + j) * f n k (j - 1)) = 0 := by
  ext d
  rw [coeff_totalLevelSeries, map_zero]
  apply Finset.sum_eq_zero
  intro p _
  apply tsum_mode_difference
  apply summable_of_hasFiniteSupport
  exact (hf.row p.1 p.2).subset fun j hj hz => hj (by simp only [hz, mul_zero])

/-- Coefficientwise spatial identities survive formal joint collection. -/
theorem totalLevelSeries_spatial_law (b : ℕ → ℕ → ℂ) (c : ℂ)
    (f d l : ℕ → ℕ → ℤ → ℂ) (hf : TotalLevelFinite f) (hd : TotalLevelFinite d)
    (hl : ∀ n k j, l n k j = c *
      (d n k j + (b n k + j + 1) * f n k j - (b n k + j) * f n k (j - 1))) :
    totalLevelSeries l = c • totalLevelSeries d := by
  ext m
  simp only [coeff_totalLevelSeries, PowerSeries.coeff_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply (sum_spatial_law (b p.1 p.2) c (f p.1 p.2) (d p.1 p.2) (l p.1 p.2)
    (summable_of_hasFiniteSupport ((hf.row p.1 p.2).subset
      fun j hj hz => hj (by simp only [hz, mul_zero])))
    (summable_of_hasFiniteSupport (hd.row p.1 p.2)) (hl p.1 p.2)).2

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ Q N : LWModule W}

/-- Joint local finiteness for the actual modified trace, with arbitrary choices
of the fixed second mode and traced grade at each level pair. -/
theorem huangModifiedModeTrace_totalLevelFinite_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (b m e : ℕ → ℕ → ℂ) (t₁ t₂ : ℂ) :
    TotalLevelFinite (fun n k j =>
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b n k + j) (m n k) t₁ t₂ (e n k)) := by
  apply totalLevelFinite_of_rows
  intro n k
  obtain ⟨S, hS⟩ := huangModifiedModeTrace_support_left Y₁ Y₂ w₁ w₂
    (b n k) (m n k) t₂ (e n k)
  exact S.finite_toSet.subset fun j hj => by
    by_contra hn
    exact hj (hS j hn t₁)

/-- The opposite orientation has the same genuinely joint finiteness. -/
theorem huangModifiedModeTrace_totalLevelFinite_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (m b e : ℕ → ℕ → ℂ) (t₁ t₂ : ℂ) :
    TotalLevelFinite (fun n k j =>
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (m n k) (b n k + j) t₁ t₂ (e n k)) := by
  apply totalLevelFinite_of_rows
  intro n k
  obtain ⟨S, hS⟩ := huangModifiedModeTrace_support_right Y₁ Y₂ w₁ w₂
    (m n k) (b n k) t₁ (e n k)
  exact S.finite_toSet.subset fun j hj => by
    by_contra hn
    exact hj (hS j hn t₂)

/-- The spatial law on the actual trace in the bigraded formal completion.
The derivative is taken separately on each finite coefficient, and both
independent level indices remain in the conclusion. -/
theorem huangModifiedTrace_biseries_Lm1_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (b m e : ℕ → ℕ → ℂ) (t₁ t₂ : ℂ) :
    modeBiseries (fun n k j => huangModifiedModeTrace Y₁ Y₂
      (P₁.isMod.Lm1 w₁) w₂ (b n k + j) (m n k) t₁ t₂ (e n k)) =
      Complex.exp logTwoPiI • modeBiseries (fun n k j => _root_.deriv (fun s =>
        huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b n k + j) (m n k) s t₂ (e n k)) t₁) := by
  apply modeBiseries_spatial_law b (Complex.exp logTwoPiI)
    (fun n k j => huangModifiedModeTrace Y₁ Y₂ w₁ w₂
      (b n k + j) (m n k) t₁ t₂ (e n k))
  · exact huangModifiedModeTrace_totalLevelFinite_left Y₁ Y₂ w₁ w₂ b m e t₁ t₂
  · apply totalLevelFinite_of_rows
    intro n k
    obtain ⟨S, hS⟩ := huangModifiedModeTrace_support_left Y₁ Y₂ w₁ w₂
      (b n k) (m n k) t₂ (e n k)
    refine S.finite_toSet.subset fun j hj => ?_
    by_contra hn
    have hz : (fun s => huangModifiedModeTrace Y₁ Y₂ w₁ w₂
      (b n k + j) (m n k) s t₂ (e n k)) = 0 := funext (hS j hn)
    exact hj (by dsimp only; rw [hz]; simp)
  · intro n k j
    have h := huangModifiedModeTrace_Lm1_left Y₁ Y₂ w₁ w₂
      (b n k + j) (m n k) t₁ t₂ (e n k)
    simpa only [Int.cast_sub, Int.cast_one, add_sub_assoc] using h

theorem huangModifiedTrace_biseries_Lm1_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (m b e : ℕ → ℕ → ℂ) (t₁ t₂ : ℂ) :
    modeBiseries (fun n k j => huangModifiedModeTrace Y₁ Y₂
      w₁ (P₂.isMod.Lm1 w₂) (m n k) (b n k + j) t₁ t₂ (e n k)) =
      Complex.exp logTwoPiI • modeBiseries (fun n k j => _root_.deriv (fun s =>
        huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (m n k) (b n k + j) t₁ s (e n k)) t₂) := by
  apply modeBiseries_spatial_law b (Complex.exp logTwoPiI)
    (fun n k j => huangModifiedModeTrace Y₁ Y₂ w₁ w₂
      (m n k) (b n k + j) t₁ t₂ (e n k))
  · exact huangModifiedModeTrace_totalLevelFinite_right Y₁ Y₂ w₁ w₂ m b e t₁ t₂
  · apply totalLevelFinite_of_rows
    intro n k
    obtain ⟨S, hS⟩ := huangModifiedModeTrace_support_right Y₁ Y₂ w₁ w₂
      (m n k) (b n k) t₁ (e n k)
    refine S.finite_toSet.subset fun j hj => ?_
    by_contra hn
    have hz : (fun s => huangModifiedModeTrace Y₁ Y₂ w₁ w₂
      (m n k) (b n k + j) t₁ s (e n k)) = 0 := funext (hS j hn)
    exact hj (by dsimp only; rw [hz]; simp)
  · intro n k j
    have h := huangModifiedModeTrace_Lm1_right Y₁ Y₂ w₁ w₂
      (m n k) (b n k + j) t₁ t₂ (e n k)
    simpa only [Int.cast_sub, Int.cast_one, add_sub_assoc] using h

/-- Differentiation of each total-level coefficient of the actual trace.
Every sum being differentiated is finite, including the level pair. -/
theorem hasDerivAt_totalLevelTrace_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (b m e : ℕ → ℕ → ℂ) (t₁ t₂ : ℂ) (d : ℕ) :
    HasDerivAt
      (fun s => PowerSeries.coeff d (totalLevelSeries (fun n k j =>
        huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b n k + j) (m n k) s t₂ (e n k))))
      ((Complex.exp logTwoPiI)⁻¹ * PowerSeries.coeff d
        (totalLevelSeries (fun n k j => huangModifiedModeTrace Y₁ Y₂
          (P₁.isMod.Lm1 w₁) w₂ (b n k + j) (m n k) t₁ t₂ (e n k)))) t₁ := by
  simp only [coeff_totalLevelSeries, Finset.mul_sum]
  exact HasDerivAt.fun_sum fun p _ => hasDerivAt_huangModifiedModeTrace_sum_left
    Y₁ Y₂ w₁ w₂ (b p.1 p.2) (m p.1 p.2) t₁ t₂ (e p.1 p.2)

theorem hasDerivAt_totalLevelTrace_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (m b e : ℕ → ℕ → ℂ) (t₁ t₂ : ℂ) (d : ℕ) :
    HasDerivAt
      (fun s => PowerSeries.coeff d (totalLevelSeries (fun n k j =>
        huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (m n k) (b n k + j) t₁ s (e n k))))
      ((Complex.exp logTwoPiI)⁻¹ * PowerSeries.coeff d
        (totalLevelSeries (fun n k j => huangModifiedModeTrace Y₁ Y₂
          w₁ (P₂.isMod.Lm1 w₂) (m n k) (b n k + j) t₁ t₂ (e n k)))) t₂ := by
  simp only [coeff_totalLevelSeries, Finset.mul_sum]
  exact HasDerivAt.fun_sum fun p _ => hasDerivAt_huangModifiedModeTrace_sum_right
    Y₁ Y₂ w₁ w₂ (m p.1 p.2) (b p.1 p.2) t₁ t₂ (e p.1 p.2)

end VOA.Huang.GenusTwoPoint.Separate
