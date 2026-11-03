import VOA.Modularity.Twisted
import VOA.Modules.WeakModule

/-!
# Restriction of arbitrary-order twisted modules

The construction uses the existing fractional-mode Jacobi identity at class
zero. It works for every positive denominator and every conformal subalgebra
fixed pointwise by the twisting automorphism, including an entire orbifold.
No existence or completeness of twisted sectors is assumed here.
-/

namespace VOA.Classification.COne.OrbPos2
open VOA
open Module (End)
open scoped BigOperators

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {g : Aut W} {d : ℕ}

theorem mem_twistedEigenspace_zero {v : V} (hv : g v = v) :
    v ∈ g.twistedEigenspace d 0 := by
  simp only [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff,
    Nat.cast_zero, mul_zero, neg_zero, zero_div, Complex.exp_zero, one_smul]
  exact hv

noncomputable def restrictedFields (T : TwistedModule g d M) (S : VOASubalgebra W) :
    S.carrier →ₗ[ℂ] FormalDist (End ℂ M) where
  toFun v k := T.YM v.1 ((d : ℤ) * (-k - 1))
  map_add' v w := by funext k; exact congrFun (map_add T.YM v.1 w.1) _
  map_smul' c v := by funext k; exact congrFun (map_smul T.YM c v.1) _

@[simp] theorem mode_restrictedFields (T : TwistedModule g d M) (S : VOASubalgebra W)
    (v : S.carrier) (k : ℤ) :
    mode (restrictedFields T S v) k = T.YM v.1 ((d : ℤ) * k) := by
  change T.YM v.1 ((d : ℤ) * (-(-k - 1) - 1)) = _
  rw [show -(-k - 1) - 1 = k by ring]

/-- Restrict fractional modes to a subalgebra fixed pointwise by `g`. -/
noncomputable def restrictedWeakModule (T : TwistedModule g d M) (hd : 0 < d)
    (S : VOASubalgebra W) (hS : ∀ v : S.carrier, g v.1 = v.1) :
    WeakModule S.toVOA M where
  YM := restrictedFields T S
  vacuum_YM := by
    funext k
    change T.YM W.vacuum ((d : ℤ) * (-k - 1)) = _
    rw [T.vacuum_YM, FormalDist.one_apply]
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    have he : (d : ℤ) * (-k - 1) = -(d : ℤ) ↔ k = 0 := by
      constructor
      · intro h
        have h' : (d : ℤ) * (-k - 1) = (d : ℤ) * (-1) := by simpa using h
        have := mul_left_cancel₀ hd0 h'
        omega
      · rintro rfl; ring
    simp only [he]
  truncation v x := by
    obtain ⟨K, hK⟩ := T.truncation v.1 x
    refine ⟨max K 0, fun k hk => ?_⟩
    rw [mode_restrictedFields]
    apply hK
    have hk0 : 0 ≤ k := le_trans (le_max_right _ _) hk
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hmul : k ≤ (d : ℤ) * k := by nlinarith
    exact (le_trans (le_max_left _ _) hk).trans hmul
  jacobi v w x ℓ m n := by
    have hJ := T.jacobi 0 v.1 (mem_twistedEigenspace_zero (hS v)) w.1 x ℓ
      ((d : ℤ) * m) ((d : ℤ) * n) (by simp)
    simp only [mode_restrictedFields]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    have hR : (∑ᶠ i : ℤ, cbz m i •
        T.YM ((S.toVOA.smul v (ℓ + i) w).1) ((d : ℤ) * (m + n - i)) x) =
        ∑ᶠ i : ℕ, cbinom ((((d : ℤ) * m : ℤ) : ℂ) / d) i •
          T.YM (W.smul v.1 (ℓ + i) w.1)
            ((d : ℤ) * m + (d : ℤ) * n - i * d) x := by
      rw [← finsum_mem_univ,
        finsum_mem_inter_support_eq' _ Set.univ (Set.range (Nat.cast : ℕ → ℤ)) ?_,
        finsum_mem_range Nat.cast_injective]
      · refine finsum_congr fun i => ?_
        rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast,
          show ((((d : ℤ) * m : ℤ) : ℂ) / d) = (m : ℂ) by
            push_cast; field_simp,
          show (d : ℤ) * (m + n - (i : ℤ)) =
            (d : ℤ) * m + (d : ℤ) * n - (i : ℤ) * d by ring]
        rfl
      · intro i hi
        simp only [Set.mem_univ, Set.mem_range, true_iff]
        rw [Function.mem_support] at hi
        by_cases h0 : 0 ≤ i
        · exact ⟨i.toNat, by omega⟩
        · exact absurd (by rw [cbz_apply_neg _ (not_le.mp h0), zero_smul]) hi
    rw [hR]
    convert hJ using 1
    congr 1
    funext i
    ring_nf

/-- Ordinary restriction keeps the same actual `L₀` weight spaces. -/
noncomputable def restrictedOrdModule (T : TwistedModule g d M) (hd : 0 < d)
    (S : VOASubalgebra W) (hS : ∀ v : S.carrier, g v.1 = v.1) :
    OrdVModule S.toVOA M where
  toWeakModule := restrictedWeakModule T hd S hS
  weight := T.weight
  isInternal := T.isInternal
  L0_weight α x hx := by
    change mode (restrictedFields T S S.toVOA.conformalVector) 1 x = _
    rw [mode_restrictedFields, mul_one]
    exact T.L0_weight α x hx
  finrank := T.finrank
  boundedBelow := T.boundedBelow

@[simp] theorem restrictedOrdModule_weight (T : TwistedModule g d M) (hd : 0 < d)
    (S : VOASubalgebra W) (hS : ∀ v : S.carrier, g v.1 = v.1) (α : ℂ) :
    (restrictedOrdModule T hd S hS).weight α = T.weight α := rfl

/-- An actual ordinary module for `W^G` from any `g`-twisted module, `g ∈ G`. -/
noncomputable def orbifoldRestriction (G : Subgroup (Aut W)) (g : G)
    (T : TwistedModule g.1 d M) (hd : 0 < d) : OrdVModule (orbifoldVOA G) M :=
  restrictedOrdModule T hd (orbifold G) (fun v => v.2 g.1 g.2)

/-- Irreducibility under all fractional modes, with nonzero carrier required. -/
def TwistedIrreducible (T : TwistedModule g d M) : Prop :=
  Nontrivial M ∧ ∀ P : Submodule ℂ M,
    (∀ (v : V) (k : ℤ) (x : M), x ∈ P → T.YM v k x ∈ P) → P = ⊥ ∨ P = ⊤

/-- The fractional-mode definition specializes to the library's ordinary irreducibility. -/
theorem twistedIrreducible_toTwisted_iff (N : OrdVModule W M) :
    TwistedIrreducible N.toTwisted ↔ N.IsIrreducible := by
  constructor
  · rintro ⟨hne, hi⟩
    exact ⟨hne, fun P => hi P.carrier (fun v k x hx => P.act_mem v k hx)⟩
  · rintro ⟨hne, hi⟩
    exact ⟨hne, fun P hP => hi ⟨P, fun v k x hx => hP v k x hx⟩⟩

end VOA.Classification.COne.OrbPos2
