import VOA.Moonshine.TwistedPlusModule

/-! # Restriction of an order-two twisted module to the fixed-point VOA
On fixed states, the integral mode indexed by `n` is the fractional mode
indexed by `2*n`. The Jacobi proof specializes the twisted identity to class
zero and reindexes its natural-number sum as an integer sum. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open TwistedPlus
open Module (End)
open scoped BigOperators

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} {g : Aut W}
  (T : TwistedModule g 2 M)

noncomputable def fixedFields :
    (orbifold (Subgroup.zpowers g)).carrier →ₗ[ℂ] FormalDist (End ℂ M) where
  toFun u k := T.YM u.1 (2 * (-k - 1))
  map_add' u v := by funext k; exact congrFun (map_add T.YM u.1 v.1) _
  map_smul' c u := by funext k; exact congrFun (map_smul T.YM c u.1) _

@[simp] theorem mode_fixedFields (u : (orbifold (Subgroup.zpowers g)).carrier) (n : ℤ) :
    mode (fixedFields T u) n = T.YM u.1 (2 * n) := by
  change T.YM u.1 (2 * (-(-n - 1) - 1)) = _
  congr 1
  ring

/-- The whole twisted carrier is an untwisted weak module for the fixed-point VOA. -/
noncomputable def fixedWeakModule : WeakModule (fixedVOA g) M where
  YM := fixedFields T
  vacuum_YM := by
    funext k
    change T.YM W.vacuum (2 * (-k - 1)) = _
    rw [T.vacuum_YM, FormalDist.one_apply]
    by_cases hk : k = 0
    · rw [if_pos (by subst hk; norm_num), if_pos hk]
    · rw [if_neg (by push_cast; omega), if_neg hk]
  truncation u x := by
    obtain ⟨K, hK⟩ := T.truncation u.1 x
    exact ⟨K.natAbs, fun n hn => by rw [mode_fixedFields, hK _ (by omega)]⟩
  jacobi u v x ℓ m n := by
    have hJ := T.jacobi 0 u.1 (mem_twistedEigenspace_zero (fixed_of_mem u.2))
      v.1 x ℓ (2 * m) (2 * n) (by omega)
    simp only [mode_fixedFields]
    have hR : (∑ᶠ i : ℤ, cbz m i •
        T.YM (((fixedVOA g).smul u (ℓ + i) v).1) (2 * (m + n - i)) x) =
        ∑ᶠ i : ℕ, cbinom (((2 * m : ℤ) : ℂ) / ((2 : ℕ) : ℂ)) i •
          T.YM (W.smul u.1 (ℓ + i) v.1) (2 * m + 2 * n - i * ((2 : ℕ) : ℤ)) x := by
      rw [← finsum_mem_univ,
        finsum_mem_inter_support_eq' _ Set.univ (Set.range (Nat.cast : ℕ → ℤ)) ?_,
        finsum_mem_range Nat.cast_injective]
      · refine finsum_congr fun i => ?_
        rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast,
          show (((2 * m : ℤ) : ℂ) / ((2 : ℕ) : ℂ)) = (m : ℂ) by push_cast; ring,
          show 2 * (m + n - (i : ℤ)) = 2 * m + 2 * n - (i : ℤ) * ((2 : ℕ) : ℤ) by
            push_cast; ring]
        rfl
      · intro i hi
        simp only [Set.mem_univ, Set.mem_range, true_iff]
        rw [Function.mem_support] at hi
        by_cases h0 : 0 ≤ i
        · exact ⟨i.toNat, by omega⟩
        · exact absurd (by rw [cbz_apply_neg _ (not_le.mp h0), zero_smul]) hi
    rw [hR]
    convert hJ using 1 <;> congr 1 <;> funext i <;> push_cast <;> ring_nf

/-- Restriction preserves the ordinary weight decomposition. -/
noncomputable def fixedOrdModule : OrdVModule (fixedVOA g) M where
  toWeakModule := fixedWeakModule T
  weight := T.weight
  isInternal := T.isInternal
  L0_weight α x hx := by
    change mode (fixedFields T (fixedVOA g).conformalVector) 1 x = _
    rw [mode_fixedFields]
    exact T.L0_weight α x hx
  finrank := T.finrank
  boundedBelow := T.boundedBelow

end VOA.Moonshine.LatticeTwistedGeneral
