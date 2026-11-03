/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3MixedLowering

/-!
# Partial ghost charge and gamma normalizers

The charge H1(0)+2 H2(0) involves only the second and highest ghost pairs.
It detects the negative Serre operators after their commutators with
those two beta colours vanish. Stability of the gamma commutant supplies
the remaining hypotheses without constructing quartic gamma products.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- The common commutant of all gamma modes inside actual endomorphisms. -/
def GammaCentral (D : Module.End ℂ Fock) : Prop := ∀ i n, ⁅D,gamma i n⁆=0

/-- An operator whose adjoint action preserves the gamma commutant. -/
def GammaNormalizer (D : Module.End ℂ Fock) : Prop :=
  ∀ A, GammaCentral A → GammaCentral ⁅D,A⁆

/-- Commuting with every gamma implies commuting with every gamma-pair product. -/
theorem commuting_GG (D : Module.End ℂ Fock) (hg : GammaCentral D)
    (i j : Fin 3) (n : ℤ) : ⁅D,GG i j n⁆=0 := by
  have hf : (fun p => ⁅D,ggFam i j n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p; simp [ggFam_eq,lie_mul_right,hg i p,hg j (n-p)]
  change ⁅D,opSum (ggFam i j n)⁆=0
  rw [lie_opSum (ggFam_locFin i j n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- Each gamma mode belongs to the common gamma commutant. -/
theorem gamma_central (i : Fin 3) (n : ℤ) : GammaCentral (gamma i n) :=
  fun j m => gamma_gamma i j n m

/-- The gamma commutant is closed under subtraction. -/
theorem GammaCentral.sub {A B : Module.End ℂ Fock} (ha : GammaCentral A)
    (hb : GammaCentral B) : GammaCentral (A-B) := by
  intro i n; rw [sub_lie,ha,hb,sub_self]

/-- Normalizers of the gamma commutant are closed under Lie brackets. -/
theorem GammaNormalizer.lie {A B : Module.End ℂ Fock} (ha : GammaNormalizer A)
    (hb : GammaNormalizer B) : GammaNormalizer ⁅A,B⁆ := by
  intro C hc
  rw [lie_lie]
  exact (ha _ (hb _ hc)).sub (hb _ (ha _ hc))

/-- The actual first lowering current preserves the common gamma commutant. -/
theorem F1_gammaNormalizer (k : ℂ) (m : ℤ) : GammaNormalizer (F1 k m) := by
  intro A ha i n
  rw [lie_lie,ha,F1_gamma]
  fin_cases i <;> simp [lie_neg,ha 2 (m+n),commuting_GG A ha]

/-- The actual second lowering current preserves the common gamma commutant. -/
theorem F2_gammaNormalizer (k : ℂ) (m : ℤ) : GammaNormalizer (F2 k m) := by
  intro A ha i n
  rw [lie_lie,ha,F2_gamma]
  fin_cases i <;> simp only [Fin.mk.injEq] <;>
    simp [lie_add,lie_neg,ha 2 (m+n),commuting_GG A ha]

/-- The highest lowering current preserves the gamma commutant by Jacobi. -/
theorem F12_gammaNormalizer (k : ℂ) (m : ℤ) : GammaNormalizer (F12 k m) :=
  (F2_gammaNormalizer k m).lie (F1_gammaNormalizer k 0)

/-- Partial charge supported on the second and highest ghost colours. -/
def partialCharge : Module.End ℂ Fock := (-3 : ℂ) • (BG 1 1 0+BG 2 2 0)

/-- This partial ghost charge equals H1(0)+2 H2(0). -/
theorem partialCharge_eq (k : ℂ) : partialCharge=H1 k 0+(2 : ℂ) • H2 k 0 := by
  simp [partialCharge,H1,H2,boson] <;> module

/-- Both relevant gamma colours carry partial charge minus three. -/
theorem partialCharge_gamma (i : Fin 3) (hi : i=1 ∨ i=2) (n : ℤ) :
    ⁅partialCharge,gamma i n⁆=(-3 : ℂ) • gamma i n := by
  rcases hi with rfl | rfl <;>
    simp [partialCharge,comm_smul_left,add_lie,D_gamma,colourDelta] <;> module

/-- The first simple lowering has partial charge zero. -/
theorem partialCharge_F1 (k : ℂ) (n : ℤ) : ⁅partialCharge,F1 k n⁆=0 := by
  rw [partialCharge_eq k,add_lie,comm_smul_left,H1_F1,H2_F1]
  simp only [zero_add]; module

/-- The second simple lowering has partial charge minus three. -/
theorem partialCharge_F2 (k : ℂ) (n : ℤ) :
    ⁅partialCharge,F2 k n⁆=(-3 : ℂ) • F2 k n := by
  rw [partialCharge_eq k,add_lie,comm_smul_left,H1_F2,H2_F2]
  simp only [zero_add]; module

/-- The highest lowering has partial charge minus three. -/
theorem partialCharge_F12 (k : ℂ) (n : ℤ) :
    ⁅partialCharge,F12 k n⁆=(-3 : ℂ) • F12 k n := by
  rw [partialCharge_eq k,add_lie,comm_smul_left,H1_F12,H2_F12]
  simp only [zero_add]; module

/-- Commuting with both ghosts of colours one and two forces partial
charge zero; a nonzero charge therefore detects the zero operator. -/
theorem zero_of_partial_commuting_weight (D : Module.End ℂ Fock) (c : ℂ)
    (hb : ∀ i, i=1 ∨ i=2 → ∀ n, ⁅D,beta i n⁆=0)
    (hg : ∀ i, i=1 ∨ i=2 → ∀ n, ⁅D,gamma i n⁆=0)
    (hc : c≠0) (hw : ⁅partialCharge,D⁆=c • D) : D=0 := by
  have hd : ⁅D,partialCharge⁆=0 := by
    simp only [partialCharge,comm_smul_right,lie_add,
      commuting_BG D 1 1 0 (hb 1 (Or.inl rfl)) (hg 1 (Or.inl rfl)),
      commuting_BG D 2 2 0 (hb 2 (Or.inr rfl)) (hg 2 (Or.inr rfl)),add_zero,smul_zero]
  have hz : c • D=0 := by rw [← hw,← lie_skew,hd,neg_zero]
  exact (smul_eq_zero.mp hz).resolve_left hc

/-- A gamma normalizer commuting with the second and highest beta modes
cannot have partial charge different from both zero and three. Applying
partial-charge detection first to its gamma commutators proves this
without assumptions on the first ghost colour or the bosons. -/
theorem zero_of_normalizer_partial_weight (D : Module.End ℂ Fock) (c : ℂ)
    (hn : GammaNormalizer D)
    (hb : ∀ i, i=1 ∨ i=2 → ∀ n, ⁅D,beta i n⁆=0)
    (hc : c≠0) (hc3 : c-3≠0) (hw : ⁅partialCharge,D⁆=c • D) : D=0 := by
  have hg : ∀ i, i=1 ∨ i=2 → ∀ n, ⁅D,gamma i n⁆=0 := by
    intro i hi n
    apply zero_of_partial_commuting_weight _ (c-3)
    · intro j hj r
      rw [lie_lie,gamma_beta,hb j hj r,lie_zero,sub_zero]
      by_cases h : j=i ∧ r+n=0 <;>
        simp [h,lie_neg,comm_one]
    · intro j hj r; exact hn _ (gamma_central i n) j r
    · exact hc3
    · rw [leibniz_lie,hw,partialCharge_gamma i hi n,comm_smul_left,comm_smul_right]
      module
  exact zero_of_partial_commuting_weight D c hb hg hc hw

end
end VOA.AffineSl3.FreeField
