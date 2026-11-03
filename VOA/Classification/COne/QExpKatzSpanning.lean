/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpKatzAlgebra

/-!
# A cyclotomic spanning-family reduction

`CyclotomicSpanning24 k` isolates the classical arithmetic existence statement:
there is a finite complex spanning family of modular forms whose coefficients lie
in `ℤ[1/N, ζ_N]`. No linear independence is required. This is a sufficient input,
not a theorem proved in this file. For positive weights it follows from the
arithmetic theory cited by the task: Katz, *p-adic properties of modular schemes
and modular forms* (1973), §§1.6–1.7 (q-expansion and base change), together with
the comparison with analytic modular forms; Diamond–Im, §12.3. In particular,
Katz's Corollary 1.6.2 alone is a descent statement, not the analytic comparison.
Source: https://web.math.princeton.edu/~nmk/old/padicpropMFMS.pdf

The implication to `QExpPrinciple24OverZInvN`, and hence to the requested
`QExpPrinciple24Away`, is proved here for every weight. The proof absorbs the
arbitrary complex coordinates of a form into a finite coefficient module; it
does not assert that an arbitrary complex modular form has algebraic coefficients.
-/

open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- The concrete cyclotomic coefficient algebra `ℤ[1/N, ζ]` inside `ℂ`. -/
abbrev cyclotomicAway (N : ℕ) (ζ : ℂ) : Subalgebra (zInv N) ℂ :=
  Algebra.adjoin (zInv N) {ζ}

theorem cyclotomicAway_fg {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) : (cyclotomicAway N ζ).toSubmodule.FG :=
  (isIntegral_of_pow_eq_one_R hN hζ.pow_eq_one).fg_adjoin_singleton

/-- Classical arithmetic input: a finite cyclotomic spanning family at each level.
For `k ≥ 1`, its mathematical source is Katz §§1.6–1.7 / Diamond–Im §12.3,
including the comparison with analytic forms. Its existence remains open here. -/
def CyclotomicSpanning24 (k : ℤ) : Prop :=
  ∀ (N : ℕ), 0 < N → 24 ∣ N →
    ∃ ζ : ℂ, IsPrimitiveRoot ζ N ∧
      ∃ (d : ℕ) (f : Fin d →
        ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k),
        (∀ i n, PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (f i)) ∈
          cyclotomicAway N ζ) ∧
        ∀ F, ∃ c : Fin d → ℂ, F = ∑ i, c i • f i

/-- Coefficients of a finite complex combination of `A`-series lie in a finite `A`-module. -/
theorem finite_combination_coeff_mem {R : Type*} [CommRing R] [Algebra R ℂ]
    {d : ℕ} (c : Fin d → ℂ) (g : Fin d → PowerSeries ℂ)
    (hg : ∀ i n, ∃ r : R, algebraMap R ℂ r = PowerSeries.coeff n (g i)) (n : ℕ) :
    PowerSeries.coeff n (∑ i, c i • g i) ∈ Submodule.span R (Set.range c) := by
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [PowerSeries.coeff_smul, smul_eq_mul]
  obtain ⟨r, hr⟩ := hg i n
  rw [← hr, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)

/-- The `q`-expansion commutes with a finite linear combination of `Γ₁(N)` forms. -/
theorem qExpansion_sum_Gamma1 {N : ℕ} {k : ℤ} {d : ℕ}
    (c : Fin d → ℂ)
    (f : Fin d → ModularForm
      (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    UpperHalfPlane.qExpansion 1 (∑ i, c i • f i : ModularForm
      (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) =
      ∑ i, c i • UpperHalfPlane.qExpansion 1 (f i) := by
  let Q := ModularForm.qExpansionAddHom one_pos (one_mem_strictPeriods_Gamma1 N) k
  change Q (∑ i, c i • f i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1 N) (c i) (f i)

/-- The classical finite spanning-family input gives Katz's bounded-coefficient conclusion. -/
theorem qExpPrinciple24OverZInvN_of_cyclotomicSpanning {k : ℤ}
    (h : CyclotomicSpanning24 k) : QExpPrinciple24OverZInvN k := by
  intro N hN h24 F
  obtain ⟨ζ, hζ, d, f, hf, hspan⟩ := h N hN h24
  obtain ⟨c, rfl⟩ := hspan F
  let L := Submodule.span (cyclotomicAway N ζ) (Set.range c)
  have hL : L.FG := Submodule.fg_span (Set.finite_range c)
  obtain ⟨K, hK, hmem⟩ := fg_extension_exists_lattice hN.ne'
    (cyclotomicAway N ζ) (cyclotomicAway_fg hN hζ) hL
  refine ⟨K, hK, fun n => hmem _ ?_⟩
  rw [qExpansion_sum_Gamma1]
  exact finite_combination_coeff_mem c _
    (fun i n => ⟨⟨_, hf i n⟩, rfl⟩) n

/-- Weight-two reduction to a finite cyclotomic spanning family. -/
theorem qExpPrinciple24Away_two_of_cyclotomicSpanning
    (h : CyclotomicSpanning24 2) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_of_overZInvN (qExpPrinciple24OverZInvN_of_cyclotomicSpanning h)

end VOA.Classification.COne.SSHecke
