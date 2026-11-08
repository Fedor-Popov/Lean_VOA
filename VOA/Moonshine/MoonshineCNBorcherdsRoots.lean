import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Rank-two root arithmetic in Borcherds coordinates, independent of any vertex algebra. -/

namespace VOA.Moonshine.ConwayNorton

def borcherdsRealRoot : ℤ × ℤ := (1, -1)

def borcherdsImaginaryRoot (j : ℤ) : ℤ × ℤ := (1, j)

def borcherdsPositiveCone (γ : ℤ × ℤ) : Prop := 1 ≤ γ.1 ∧ 1 ≤ γ.2

def borcherdsPositiveRoot (γ : ℤ × ℤ) : Prop :=
  γ = borcherdsRealRoot ∨ borcherdsPositiveCone γ

def borcherdsRootSupport (γ : ℤ × ℤ) : Prop :=
  γ = 0 ∨ borcherdsPositiveRoot γ ∨ borcherdsPositiveRoot (-γ)

def borcherdsSimpleRoot (γ : ℤ × ℤ) : Prop :=
  γ = borcherdsRealRoot ∨ ∃ j : ℤ, 1 ≤ j ∧ γ = borcherdsImaginaryRoot j

def borcherdsRootHeight (γ : ℤ × ℤ) : ℤ := γ.1 + γ.2

def borcherdsWeightVector (γ : ℤ × ℤ) : ℂ × ℂ := (γ.1, γ.2)

/-- The complex bilinear extension of the negative hyperbolic lattice form. -/
def borcherdsCartanPairing (ξ μ : ℂ × ℂ) : ℂ := -(ξ.1 * μ.2 + μ.1 * ξ.2)

/-- The lowest-weight Casimir scalar for the Weyl vector `(1,0)`. -/
def borcherdsCasimirScalar (γ : ℤ × ℤ) : ℂ :=
  borcherdsCartanPairing (borcherdsWeightVector γ) (borcherdsWeightVector γ) -
    2 * borcherdsCartanPairing (1, 0) (borcherdsWeightVector γ)

theorem borcherdsPositiveCone_add {α β : ℤ × ℤ}
    (hα : borcherdsPositiveCone α) (hβ : borcherdsPositiveCone β) :
    borcherdsPositiveCone (α + β) := by
  simp only [borcherdsPositiveCone, Prod.fst_add, Prod.snd_add] at *
  omega

theorem borcherdsRootSupport_neg (γ : ℤ × ℤ) :
    borcherdsRootSupport (-γ) ↔ borcherdsRootSupport γ := by
  simp only [borcherdsRootSupport, neg_eq_zero, neg_neg]
  tauto

theorem borcherdsRootSupport_axis {γ : ℤ × ℤ}
    (hs : borcherdsRootSupport γ) (ha : γ.1 = 0 ∨ γ.2 = 0) : γ = 0 := by
  simp only [borcherdsRootSupport, borcherdsPositiveRoot, borcherdsPositiveCone,
    borcherdsRealRoot, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero,
    Prod.fst_neg, Prod.snd_neg] at *
  omega

/-- A simple root minus a positive root is never positive. -/
theorem borcherdsSimpleRoot_sub_not_positive {α β : ℤ × ℤ}
    (hα : borcherdsSimpleRoot α) (hβ : borcherdsPositiveRoot β) :
    ¬ borcherdsPositiveRoot (α - β) := by
  rcases hα with rfl | ⟨j, hj, rfl⟩ <;>
    simp only [borcherdsPositiveRoot, borcherdsPositiveCone, borcherdsRealRoot,
      borcherdsImaginaryRoot, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at * <;> omega

/-- Adding a simple root to a positive root remains positive whenever it remains supported. -/
theorem borcherdsPositiveRoot_add_simple {α β : ℤ × ℤ}
    (hα : borcherdsSimpleRoot α) (hβ : borcherdsPositiveRoot β)
    (hs : borcherdsRootSupport (β + α)) : borcherdsPositiveRoot (β + α) := by
  rcases hα with rfl | ⟨j, hj, rfl⟩ <;>
    simp only [borcherdsRootSupport, borcherdsPositiveRoot, borcherdsPositiveCone,
      borcherdsRealRoot, borcherdsImaginaryRoot, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg] at * <;> omega

theorem borcherdsPositiveCone_height_finite (h : ℤ) :
    {γ : ℤ × ℤ | borcherdsPositiveCone γ ∧ borcherdsRootHeight γ = h}.Finite := by
  apply (Set.finite_Icc (1, 1) (h, h)).subset
  intro γ hγ
  simp only [Set.mem_setOf_eq, borcherdsPositiveCone, borcherdsRootHeight] at hγ
  change (1 ≤ γ.1 ∧ 1 ≤ γ.2) ∧ γ.1 ≤ h ∧ γ.2 ≤ h
  omega

theorem borcherdsCasimirScalar_eq (γ : ℤ × ℤ) :
    borcherdsCasimirScalar γ = -2 * (γ.2 : ℂ) * ((γ.1 : ℂ) - 1) := by
  simp only [borcherdsCasimirScalar, borcherdsCartanPairing, borcherdsWeightVector]
  ring

/-- The Casimir argument can force only the first-coordinate-one line in the positive cone. -/
theorem borcherdsCasimirScalar_zero_iff {γ : ℤ × ℤ} (hγ : borcherdsPositiveCone γ) :
    borcherdsCasimirScalar γ = 0 ↔ γ.1 = 1 := by
  rw [borcherdsCasimirScalar_eq]
  have hn : (γ.2 : ℂ) ≠ 0 := by exact_mod_cast (show γ.2 ≠ 0 by have := hγ.2; omega)
  constructor
  · intro h
    have hz := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hn)
    exact_mod_cast (sub_eq_zero.mp hz)
  · intro h
    simp [h]

end VOA.Moonshine.ConwayNorton
