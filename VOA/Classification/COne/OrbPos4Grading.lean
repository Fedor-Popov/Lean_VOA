import VOA.Classification.COne.OrbPos3Untwist

/-!
# Ordinary energy grading for rationally shifted lattice charges

This constructs the grading of the proposed fractional-charge Fock model,
not its twisted vertex operators. No integral ambient gluing lattice is used.
-/

namespace VOA.Classification.COne.OrbPos4
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 LatMod

def energyFiber (n : ℕ) (a j : ℤ) (α : ℂ) : Set (ℤ × ℤ) :=
  {p | 0 ≤ p.1 ∧ (innerEnergy n a j p.2 p.1.toNat : ℂ) = α}

/-- A rational shift still has only finitely many oscillator/charge pairs at
each energy. This does not assume the shift is in the dual lattice. -/
theorem energyFiber_finite {n : ℕ} (hn : 0 < n) (a j : ℤ) (α : ℂ) :
    (energyFiber n a j α).Finite := by
  let C : ℤ := ⌈4 * (n : ℝ) ^ 2 * α.re⌉
  let B : ℤ := C + |(n : ℤ) * j - a|
  refine Set.Finite.subset ((Set.finite_Icc (0 : ℤ) B).prod
    (Set.finite_Icc (-B) B)) ?_
  rintro ⟨w, k⟩ ⟨hw, hE⟩
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hnZ : (1 : ℤ) ≤ n := by omega
  have hwR : (w.toNat : ℝ) = w := by exact_mod_cast Int.toNat_of_nonneg hw
  have hre := congrArg Complex.re hE
  simp only [Complex.ratCast_re, innerEnergy] at hre
  push_cast at hre
  rw [hwR] at hre
  have hZ : ((4 * (n : ℤ)^2 * w + ((n : ℤ) * (2*k+j)-a)^2 : ℤ) : ℝ)
      = 4 * (n : ℝ)^2 * α.re := by
    rw [← hre]
    push_cast
    field_simp
    ring
  have hC : 4 * (n : ℤ)^2 * w + ((n : ℤ) * (2*k+j)-a)^2 ≤ C := by
    have h : ((4 * (n : ℤ)^2 * w + ((n : ℤ) * (2*k+j)-a)^2 : ℤ) : ℝ)
        ≤ (C : ℝ) := by rw [hZ]; exact Int.le_ceil _
    exact_mod_cast h
  let y : ℤ := (n : ℤ) * (2*k+j)-a
  have hy : y ≤ y^2 ∧ -y ≤ y^2 := by
    rcases le_or_gt y 0 with h | h <;> constructor <;> nlinarith
  have hs : 0 ≤ y^2 := sq_nonneg y
  have hc1 := le_abs_self ((n : ℤ)*j-a)
  have hc2 := neg_le_abs ((n : ℤ)*j-a)
  have hn2 : 1 ≤ (n : ℤ)^2 := by nlinarith
  change 4 * (n : ℤ)^2 * w + y^2 ≤ C at hC
  have hwy : w + y^2 ≤ C := by nlinarith
  have hb : C ≤ B := by dsimp [B]; omega
  refine ⟨⟨hw, by nlinarith⟩, ?_, ?_⟩
  · dsimp [y] at hy
    dsimp [B]
    rcases le_or_gt 0 k with hk | hk <;> nlinarith
  · dsimp [y] at hy
    dsimp [B]
    rcases le_or_gt 0 k with hk | hk <;> nlinarith

noncomputable def energyGrade (n : ℕ) (a j : ℤ) (α : ℂ) : Submodule ℂ Space :=
  ⨆ p ∈ energyFiber n a j α, bigradα (latP 1) p

theorem energyGrade_le_eigenspace (n : ℕ) (a j : ℤ) (α : ℂ) :
    energyGrade n a j α ≤ Module.End.eigenspace (energyOperator n a j) α := by
  refine iSup_le fun p => iSup_le fun hp => ?_
  rintro x ⟨q, hq, rfl⟩
  rw [gradingZN_of_nonneg hp.1] at hq
  rw [Module.End.mem_eigenspace_iff, ← hp.2]
  exact energyOperator_latState n a j p.2 hq

theorem energyGrade_iSup_eq_top (n : ℕ) (a j : ℤ) :
    iSup (energyGrade n a j) = ⊤ := by
  rw [eq_top_iff, ← bigradα_iSup_eq_top (latP 1)]
  refine iSup_le fun p => ?_
  by_cases hp : 0 ≤ p.1
  · exact le_trans (le_biSup (bigradα (latP 1))
      (show p ∈ energyFiber n a j (innerEnergy n a j p.2 p.1.toNat : ℂ)
        from ⟨hp, rfl⟩))
      (le_iSup (energyGrade n a j) (innerEnergy n a j p.2 p.1.toNat : ℂ))
  · rw [show p = (p.1, p.2) from rfl, bigradα_eq_bot_of_neg (latP 1) p.2 (by omega)]
    exact bot_le

theorem energyGrade_isInternal (n : ℕ) (a j : ℤ) :
    DirectSum.IsInternal (energyGrade n a j) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ((Module.End.eigenspaces_iSupIndep (energyOperator n a j)).mono
      (energyGrade_le_eigenspace n a j)) (energyGrade_iSup_eq_top n a j)

theorem energyGrade_eq_eigenspace (n : ℕ) (a j : ℤ) (α : ℂ) :
    energyGrade n a j α = Module.End.eigenspace (energyOperator n a j) α :=
  congrFun ((iSupIndep.le_iff_eq_of_iSup_eq_top
    (Module.End.eigenspaces_iSupIndep (energyOperator n a j))
    (energyGrade_iSup_eq_top n a j)).mp
      (energyGrade_le_eigenspace n a j)) α

theorem energyGrade_finiteDimensional {n : ℕ} (hn : 0 < n) (a j : ℤ) (α : ℂ) :
    FiniteDimensional ℂ (energyGrade n a j α) := by
  rw [energyGrade, ← iSup_subtype'']
  have : Finite (energyFiber n a j α) := energyFiber_finite hn a j α
  infer_instance

theorem energyOperator_finiteDimensional_eigenspace {n : ℕ} (hn : 0 < n)
    (a j : ℤ) (α : ℂ) :
    FiniteDimensional ℂ (Module.End.eigenspace (energyOperator n a j) α) := by
  rw [← energyGrade_eq_eigenspace]
  exact energyGrade_finiteDimensional hn a j α

theorem energyGrade_nonneg (n : ℕ) (a j : ℤ) {α : ℂ}
    (hα : energyGrade n a j α ≠ ⊥) : 0 ≤ α.re := by
  have he : Module.End.eigenspace (energyOperator n a j) α ≠ ⊥ := by
    intro h
    exact hα (le_bot_iff.mp (h ▸ energyGrade_le_eigenspace n a j α))
  obtain ⟨k, r, rfl⟩ := energyOperator_spectrum n a j he
  simp only [Complex.ratCast_re, innerEnergy]
  push_cast
  positivity

/-- All ordinary-grading obligations for the shifted energy are discharged.
The field axioms and the classification of arbitrary twisted modules are separate. -/
theorem shiftedLattice_ordinaryGrading {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    DirectSum.IsInternal (energyGrade n a j) ∧
    (∀ α, FiniteDimensional ℂ (energyGrade n a j α)) ∧
    (∀ α x, x ∈ energyGrade n a j α → energyOperator n a j x = α • x) ∧
    (∀ α, energyGrade n a j α ≠ ⊥ → 0 ≤ α.re) :=
  ⟨energyGrade_isInternal n a j, energyGrade_finiteDimensional hn a j,
    fun α _ hx => Module.End.mem_eigenspace_iff.mp
      (energyGrade_le_eigenspace n a j α hx), fun _ => energyGrade_nonneg n a j⟩

end VOA.Classification.COne.OrbPos4
