import VOA.Huang.GenusOneScaleModes

/-! # The insertion connection and its G₂ correction under S

The equality is an identity of module vectors, before evaluating any block.
This is condition C4 in Miyamoto, math/0010180, Theorem 5.1.
-/
namespace VOA.Huang.GenusOne
open VOA Complex SquareModule
open scoped BigOperators MatrixGroups
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

theorem finsum_nat_peel_module {E : Type*} [AddCommGroup E] {f : ℕ → E} {K : ℕ}
    (hK : ∀ m : ℕ, K ≤ m → f m = 0) :
    ∑ᶠ m : ℕ, f m = f 0 + ∑ᶠ m : ℕ, f (m + 1) := by
  classical
  have hs1 : Function.support f ⊆ (Finset.range (K + 1) : Finset ℕ) := by
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hm (hK m (by omega))
  have hs2 : Function.support (fun m : ℕ => f (m + 1)) ⊆ (Finset.range (K + 1) : Finset ℕ) := by
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hm (hK (m + 1) (by omega))
  rw [finsum_eq_finsetSum_of_support_subset _ hs1, finsum_eq_finsetSum_of_support_subset _ hs2]
  have hstep : ∑ i ∈ Finset.range (K + 1 + 1), f i
      = (∑ i ∈ Finset.range (K + 1), f (i + 1)) + f 0 := Finset.sum_range_succ' f (K + 1)
  rw [Finset.sum_range_succ f (K + 1), hK (K + 1) (by omega), add_zero] at hstep
  rw [hstep]
  abel


theorem zhuGC_S {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ imGT 0) :
    zhuGC k (mobiusC ModularGroup.S z) = z ^ (2 * k) * zhuGC k z := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl (0 : ℝ)) hz
  have he := slashC_zhuGC hk ModularGroup.S hz
  have hd : denomC ModularGroup.S z = z := by simp [denomC, ModularGroup.S]
  rw [slashC, hd] at he
  rw [show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast] at he
  field_simp at he
  linear_combination he

theorem zhuGC_one_S {z : ℂ} (hz : z ∈ imGT 0) :
    zhuGC 1 (mobiusC ModularGroup.S z) =
      z ^ (2 : ℕ) * zhuGC 1 z - z / (2 * (Real.pi : ℂ) * I) := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl (0 : ℝ)) hz
  have hG := slashC_G2C ModularGroup.S hz
  have hd : denomC ModularGroup.S z = z := by simp [denomC, ModularGroup.S]
  have hc : (ModularGroup.S 1 0 : ℂ) = 1 := by norm_num [ModularGroup.S]
  rw [slashC, hd, hc, mul_one, zpow_neg, zpow_ofNat] at hG
  rw [zhuGC_one hz, zhuGC_one (mobiusC_mem_imGT ModularGroup.S hz)]
  have hi := two_pi_I_ne_zero
  field_simp at hG ⊢
  linear_combination hG

theorem insertionConnection_peel (z : ℂ) (w : M) :
    insertionConnection A z w = sqL A (-2) w - zhuGC 1 z • sqL A 0 w -
      ∑ᶠ m : ℕ, zhuGC (m + 2) z • sqL A (2 * (m + 2) - 2 : ℤ) w := by
  obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A w
  have hp := finsum_nat_peel_module (K := K) (f := fun m : ℕ =>
    zhuGC (m + 1) z • sqL A (2 * (m + 1) - 2 : ℤ) w)
    (fun m hm => by dsimp only; rw [hK m hm, smul_zero])
  change sqL A (-2) w - _ = _
  rw [hp]
  norm_num only at *
  have ht : (∑ᶠ m : ℕ, zhuGC (m + 1 + 1) z •
      sqL A (2 * ((m + 1 : ℕ) + 1) - 2 : ℤ) w) =
      ∑ᶠ m : ℕ, zhuGC (m + 2) z • sqL A (2 * (m + 2) - 2 : ℤ) w := by
    apply finsum_congr
    intro m
    congr 2
  rw [ht]
  abel

theorem insertion_connection_tail_support (z : ℂ) (w : M) :
    (Function.support fun m : ℕ =>
      zhuGC (m + 2) z • sqL A (2 * (m + 2) - 2 : ℤ) w).Finite := by
  obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A w
  refine (Set.finite_Iio K).subset fun m hm => ?_
  simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
  by_contra hn
  apply hm
  convert (show zhuGC (m + 2) z • sqL A (2 * ((m + 1 : ℕ) + 1) - 2 : ℤ) w = 0 by
    rw [hK (m + 1) (by omega), smul_zero]) using 1

/-- The connection field of `InsertionCoordinateCovariance`, with no analytic
block hypothesis and with the quasimodular anomaly explicit. -/
theorem insertionConnection_S (D : DirectSum.IsInternal (insertionSqWeight A))
    {z : ℂ} (hz : z ∈ imGT 0) (w : M) :
    insertionConnection A (mobiusC ModularGroup.S z) (insertionScale D z w) =
      z ^ (2 : ℕ) • insertionScale D z (insertionConnection A z w) +
        (z / (2 * (Real.pi : ℂ) * I)) • insertionScale D z (sqL A 0 w) := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl (0 : ℝ)) hz
  have hlead : z ^ (2 : ℕ) • insertionScale D z (sqL A (-2) w) =
      sqL A (-2) (insertionScale D z w) := by
    rw [insertionScale_sqL D _ hz0, smul_smul]
    simp only [zpow_neg, zpow_ofNat]
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hz0), one_smul]
  have hzero : insertionScale D z (sqL A 0 w) = sqL A 0 (insertionScale D z w) := by
    rw [insertionScale_sqL D _ hz0, zpow_zero, one_smul]
  have hterm (m : ℕ) : z ^ (2 : ℕ) • insertionScale D z
      (zhuGC (m + 2) z • sqL A (2 * (m + 2) - 2 : ℤ) w) =
      zhuGC (m + 2) (mobiusC ModularGroup.S z) •
        sqL A (2 * (m + 2) - 2 : ℤ) (insertionScale D z w) := by
    rw [map_smul, insertionScale_sqL D _ hz0, zhuGC_S (by omega) hz]
    simp only [smul_smul]
    congr 1
    have hp : z ^ (2 : ℕ) * z ^ (2 * (m + 2) - 2 : ℤ) = z ^ (2 * (m + 2) : ℕ) := by
      have he : (2 : ℤ) + (2 * ((m : ℤ) + 2) - 2) = ((2 * (m + 2) : ℕ) : ℤ) := by
        push_cast
        ring
      rw [← zpow_natCast z 2, ← zpow_add₀ hz0]
      norm_num only [Nat.cast_ofNat]
      rw [he, zpow_natCast]
    calc
      z ^ (2 : ℕ) * (zhuGC (m + 2) z * z ^ (2 * (m + 2) - 2 : ℤ)) =
        (z ^ (2 : ℕ) * z ^ (2 * (m + 2) - 2 : ℤ)) * zhuGC (m + 2) z := by ring
      _ = _ := by rw [hp]
  rw [insertionConnection_peel, insertionConnection_peel, map_sub, map_sub,
    map_smul, map_finsum _ (insertion_connection_tail_support z w), smul_sub, smul_sub,
    hlead, hzero, zhuGC_one_S hz]
  rw [smul_finsum' _ (by
    apply (insertion_connection_tail_support (A := A) z w).subset
    intro m hm
    simp only [Function.mem_support] at hm ⊢
    intro he; exact hm (by rw [he, map_zero])), finsum_congr hterm]
  module

end VOA.Huang.GenusOne
