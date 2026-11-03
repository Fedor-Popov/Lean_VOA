/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangSugawaraReduction

/-!
# Heterotypic order-two locality for the Lee--Yang Fock exponential

The momentum-zero omission in the polynomial Heisenberg carrier makes the unshifted
current/exponential bracket look exceptional.  Between the momentum-`0` source and momentum-`c`
target, however, the shifted currents have the complete delta bracket.  This file packages those
currents as fields and proves the key normal-order telescope: one `(z-w)` difference of the
heterotypic Sugawara bracket is the double contraction, and a second difference is zero.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangHeterotypicLocality

open Module (End)
open LeeYangFockExponential LeeYangFockVirasoro LeeYangFockWard
open LeeYangSugawaraReduction
open LatExp

noncomputable section

/-! ## A two-sided algebraic telescope -/

/-- If an integer-indexed family is eventually `A` on the left and eventually `C` on the right,
the algebraic sum of its first differences is its jump `C-A`. -/
theorem finsum_succ_sub_eq_of_tails {M : Type*} [AddCommGroup M]
    (F : ℤ → M) (A C : M) (L R : ℤ) (hLR : L ≤ R)
    (hleft : ∀ k, k < L → F k = A) (hright : ∀ k, R ≤ k → F k = C) :
    (∑ᶠ k : ℤ, (F (k + 1) - F k)) = C - A := by
  let S : ℤ → M := fun k => if R ≤ k then C else A
  let H : ℤ → M := fun k => F k - S k
  have hHfin : (Function.support H).Finite := by
    apply Set.Finite.subset (Set.finite_Icc L (R - 1))
    intro k hk
    change H k ≠ 0 at hk
    change L ≤ k ∧ k ≤ R - 1
    constructor
    · by_contra hnot
      have hkL : k < L := by omega
      have hkR : ¬ R ≤ k := by omega
      exact hk (by simp only [H, S, if_neg hkR, hleft k hkL, sub_self])
    · by_contra hnot
      have hRk : R ≤ k := by omega
      exact hk (by simp only [H, S, if_pos hRk, hright k hRk, sub_self])
  have hDHfin : (Function.support (fun k : ℤ => H (k + 1) - H k)).Finite := by
    have hpre : ((fun k : ℤ => k + 1) ⁻¹' Function.support H).Finite :=
      Set.Finite.preimage (fun _ _ _ _ h => by omega) hHfin
    apply Set.Finite.subset
      (hpre.union hHfin)
    intro k hk
    change H (k + 1) - H k ≠ 0 at hk
    change k ∈ (fun k : ℤ => k + 1) ⁻¹' Function.support H ∪ Function.support H
    simp only [Set.mem_union, Set.mem_preimage, Function.mem_support]
    by_contra hcon
    push_neg at hcon
    exact hk (by rw [hcon.1, hcon.2, sub_zero])
  have hDSfin : (Function.support (fun k : ℤ => S (k + 1) - S k)).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (R - 1))
    intro k hk
    change S (k + 1) - S k ≠ 0 at hk
    change k = R - 1
    by_contra hne
    apply hk
    by_cases hkR : R ≤ k
    · have hk1R : R ≤ k + 1 := by omega
      simp only [S, if_pos hkR, if_pos hk1R, sub_self]
    · have hk1R : ¬ R ≤ k + 1 := by omega
      simp only [S, if_neg hkR, if_neg hk1R, sub_self]
  have hdecomp : ∀ k : ℤ,
      F (k + 1) - F k = (H (k + 1) - H k) + (S (k + 1) - S k) := by
    intro k
    simp only [H]
    abel
  rw [finsum_congr hdecomp, finsum_add_distrib hDHfin hDSfin]
  have hHsum : (∑ᶠ k : ℤ, (H (k + 1) - H k)) = 0 := by
    have hpre : ((fun k : ℤ => k + 1) ⁻¹' Function.support H).Finite :=
      Set.Finite.preimage (fun _ _ _ _ h => by omega) hHfin
    rw [finsum_sub_distrib
      hpre hHfin, finsum_int_succ_shift, sub_self]
  rw [hHsum, zero_add]
  rw [finsum_eq_single (fun k : ℤ => S (k + 1) - S k) (R - 1) (fun k hk => by
    have hkne : k ≠ R - 1 := hk
    by_cases hkR : R ≤ k
    · have hk1R : R ≤ k + 1 := by omega
      simp only [S, if_pos hkR, if_pos hk1R, sub_self]
    · have hk1R : ¬ R ≤ k + 1 := by omega
      simp only [S, if_neg hkR, if_neg hk1R, sub_self])]
  simp only [S, if_pos (by omega : R ≤ R - 1 + 1),
    if_neg (by omega : ¬ R ≤ R - 1)]

/-! ## Momentum-sector current fields -/

/-- The current distribution in momentum sector `p`, in field-coefficient indexing. -/
noncomputable def sectorCurrentDist (p : ℂ) : FormalDist (End ℂ LeeYangFock) :=
  fun j => sectorCurrent p (-j - 1)

@[simp] theorem sectorCurrentDist_apply (p : ℂ) (j : ℤ) :
    sectorCurrentDist p j = sectorCurrent p (-j - 1) := rfl

/-- A momentum-sector current is still a field: it differs from the oscillator current only at
the single coefficient `j=-1`. -/
theorem sectorCurrentDist_isField (p : ℂ) : IsField (sectorCurrentDist p) := by
  intro x
  obtain ⟨B, hB⟩ := HeisenbergN.currentN_isField 1 2 0 x
  refine ⟨min B (-1), fun j hj => ?_⟩
  rw [sectorCurrentDist_apply, sectorCurrent]
  have hj0 : -j - 1 ≠ 0 := by omega
  simp only [if_neg hj0, zero_smul, add_zero, alphaMode]
  exact hB j (lt_of_lt_of_le hj (min_le_left _ _))

/-- The heterotypic current bracket is the complete delta bracket; in particular the momentum
shift restores the missing zero-mode row. -/
theorem sectorCurrentDist_heterotypic_EEC (c : ℂ) (j s : ℤ) :
    sectorCurrentDist c j * EEC c s - EEC c s * sectorCurrentDist 0 j =
      (2 * c) • EEC c (s + j + 1) := by
  have h := sectorCurrent_heterotypic_EEC c (-j - 1) s
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp] at h
  simpa only [sectorCurrentDist_apply, show s - (-j - 1) = s + j + 1 by ring] using h

/-- The current-current bracket is independent of the momentum sector. -/
theorem sectorCurrentDist_comm_independent (p : ℂ) (j l : ℤ) :
    sectorCurrentDist p j * sectorCurrentDist p l -
        sectorCurrentDist p l * sectorCurrentDist p j =
      sectorCurrentDist 0 j * sectorCurrentDist 0 l -
        sectorCurrentDist 0 l * sectorCurrentDist 0 j := by
  rw [sectorCurrentDist_apply, sectorCurrentDist_apply, sectorCurrent_comm,
    sectorCurrentDist_apply, sectorCurrentDist_apply, sectorCurrent_comm]

/-! ## The normal-order double-contraction telescope -/

/-- The heterotypic bracket of one normal-ordered current pair with the exponential can be written
uniformly, independently of the normal-order gate.  Equality of the source and target current
central terms is exactly what removes the gate. -/
theorem normalOrdered_sectorCurrentDist_EEC (c : ℂ) (j l s : ℤ) :
    normalOrdered (sectorCurrentDist c) (sectorCurrentDist c) j l * EEC c s -
        EEC c s * normalOrdered (sectorCurrentDist 0) (sectorCurrentDist 0) j l =
      (2 * c) •
        (sectorCurrentDist c j * EEC c (s + l + 1) +
          EEC c (s + j + 1) * sectorCurrentDist 0 l) := by
  have hj := sectorCurrentDist_heterotypic_EEC c j s
  have hl := sectorCurrentDist_heterotypic_EEC c l s
  rw [normalOrdered_apply, normalOrdered_apply]
  by_cases hgate : 0 ≤ j
  · rw [if_pos hgate, if_pos hgate]
    rw [show
        sectorCurrentDist c j * sectorCurrentDist c l * EEC c s -
            EEC c s * (sectorCurrentDist 0 j * sectorCurrentDist 0 l) =
          sectorCurrentDist c j *
              (sectorCurrentDist c l * EEC c s - EEC c s * sectorCurrentDist 0 l) +
            (sectorCurrentDist c j * EEC c s - EEC c s * sectorCurrentDist 0 j) *
              sectorCurrentDist 0 l by
                simp only [mul_sub, sub_mul, mul_assoc]
                abel,
      hl, hj, mul_smul_comm, smul_mul_assoc, ← smul_add]
  · rw [if_neg hgate, if_neg hgate]
    have hcomm := sectorCurrentDist_comm_independent c j l
    have hcentral :
        (sectorCurrentDist c j * sectorCurrentDist c l -
            sectorCurrentDist c l * sectorCurrentDist c j) * EEC c s =
          EEC c s * (sectorCurrentDist 0 j * sectorCurrentDist 0 l -
            sectorCurrentDist 0 l * sectorCurrentDist 0 j) := by
      rw [hcomm, sectorCurrentDist_apply, sectorCurrentDist_apply,
        sectorCurrent_comm]
      by_cases hzero : (-j - 1) + (-l - 1) = 0
      · simp only [if_pos hzero, smul_mul_assoc, mul_smul_comm]
        congr 1
      · simp only [if_neg hzero, zero_smul, zero_mul, mul_zero]
    have hreorder :
        sectorCurrentDist c l * sectorCurrentDist c j * EEC c s -
            EEC c s * (sectorCurrentDist 0 l * sectorCurrentDist 0 j) =
          sectorCurrentDist c j * sectorCurrentDist c l * EEC c s -
            EEC c s * (sectorCurrentDist 0 j * sectorCurrentDist 0 l) := by
      calc
        _ = (sectorCurrentDist c j * sectorCurrentDist c l * EEC c s -
              EEC c s * (sectorCurrentDist 0 j * sectorCurrentDist 0 l)) -
            ((sectorCurrentDist c j * sectorCurrentDist c l -
              sectorCurrentDist c l * sectorCurrentDist c j) * EEC c s) +
            EEC c s * (sectorCurrentDist 0 j * sectorCurrentDist 0 l -
              sectorCurrentDist 0 l * sectorCurrentDist 0 j) := by
                simp only [sub_mul, mul_sub, mul_assoc]
                abel
        _ = _ := by rw [hcentral]; abel
    rw [hreorder]
    rw [show
        sectorCurrentDist c j * sectorCurrentDist c l * EEC c s -
            EEC c s * (sectorCurrentDist 0 j * sectorCurrentDist 0 l) =
          sectorCurrentDist c j *
              (sectorCurrentDist c l * EEC c s - EEC c s * sectorCurrentDist 0 l) +
            (sectorCurrentDist c j * EEC c s - EEC c s * sectorCurrentDist 0 j) *
              sectorCurrentDist 0 l by
                simp only [mul_sub, sub_mul, mul_assoc]
                abel,
      hl, hj, mul_smul_comm, smul_mul_assoc, ← smul_add]

/-- The unscaled heterotypic normal-product bracket. -/
noncomputable def currentNprodEECBracket (c : ℂ) (a s : ℤ) : End ℂ LeeYangFock :=
  nprod (sectorCurrentDist_isField c) (sectorCurrentDist_isField c) a * EEC c s -
    EEC c s * nprod (sectorCurrentDist_isField 0) (sectorCurrentDist_isField 0) a

/-- A diagonal normal-product bracket is a finite family on each vector. -/
theorem currentNprodEECBracket_family_finite (c : ℂ) (a s : ℤ) (x : LeeYangFock) :
    (Function.support (fun j : ℤ =>
      (normalOrdered (sectorCurrentDist c) (sectorCurrentDist c) j (a - j) * EEC c s -
        EEC c s * normalOrdered (sectorCurrentDist 0) (sectorCurrentDist 0) j (a - j)) x)).Finite := by
  apply Set.Finite.subset
    ((normalOrdered_diag_support_finite (sectorCurrentDist_isField c)
      (sectorCurrentDist_isField c) a (EEC c s x)).union
      (normalOrdered_diag_support_finite (sectorCurrentDist_isField 0)
        (sectorCurrentDist_isField 0) a x))
  intro j hj
  change _ ≠ 0 at hj
  change j ∈ Function.support (fun m =>
      normalOrdered (sectorCurrentDist c) (sectorCurrentDist c) m (a - m) (EEC c s x)) ∪
    Function.support (fun m =>
      normalOrdered (sectorCurrentDist 0) (sectorCurrentDist 0) m (a - m) x)
  simp only [Set.mem_union, Function.mem_support]
  by_contra hcon
  push_neg at hcon
  exact hj (by
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    rw [hcon.1, hcon.2, map_zero, sub_zero])

/-- Coefficientwise expansion of the heterotypic normal-product bracket as one finite diagonal
sum. -/
theorem currentNprodEECBracket_apply (c : ℂ) (a s : ℤ) (x : LeeYangFock) :
    currentNprodEECBracket c a s x =
      ∑ᶠ j : ℤ,
        (normalOrdered (sectorCurrentDist c) (sectorCurrentDist c) j (a - j) * EEC c s -
          EEC c s * normalOrdered (sectorCurrentDist 0) (sectorCurrentDist 0) j (a - j)) x := by
  rw [currentNprodEECBracket, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    nprod_apply, nprod_apply,
    map_finsum (EEC c s)
      (normalOrdered_diag_support_finite (sectorCurrentDist_isField 0)
        (sectorCurrentDist_isField 0) a x),
    ← finsum_sub_distrib
      (normalOrdered_diag_support_finite (sectorCurrentDist_isField c)
        (sectorCurrentDist_isField c) a (EEC c s x))
      ((normalOrdered_diag_support_finite (sectorCurrentDist_isField 0)
        (sectorCurrentDist_isField 0) a x).subset (fun j hj => by
          rw [Function.mem_support] at hj ⊢
          exact fun h => hj (by rw [h, map_zero])))]
  exact finsum_congr fun j => by
    simp only [LinearMap.sub_apply, Module.End.mul_apply]

/-- One field-index difference of the heterotypic current normal product is exactly its double
contraction. -/
theorem currentNprodEECBracket_firstDifference (c : ℂ) (a s : ℤ) :
    currentNprodEECBracket c (a - 1) s - currentNprodEECBracket c a (s - 1) =
      (2 * c) • ((2 * c) • EEC c (s + a + 1)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  obtain ⟨BE, hBE⟩ := EEC_isField c x
  obtain ⟨BJ, hBJ⟩ := sectorCurrentDist_isField (0 : ℂ) x
  let L : ℤ := BE - s
  let R₀ : ℤ := a - BJ + 1
  let R : ℤ := max L R₀
  let F : ℤ → LeeYangFock := fun j =>
    (2 * c) • (EEC c (s + j) (sectorCurrentDist 0 (a - j) x))
  have hLR : L ≤ R := le_max_left _ _
  have hleft : ∀ j, j < L → F j =
      -((2 * c) • ((2 * c) • EEC c (s + a + 1) x)) := by
    intro j hj
    have hEzero : EEC c (s + j) x = 0 := hBE (s + j) (by simp only [L] at hj; omega)
    have hcur := congrArg (fun T : End ℂ LeeYangFock => T x)
      (sectorCurrentDist_heterotypic_EEC c (a - j) (s + j))
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hcur
    rw [hEzero, map_zero, zero_sub,
      show s + j + (a - j) + 1 = s + a + 1 by ring] at hcur
    simp only [F]
    have hEJ : EEC c (s + j) (sectorCurrentDist 0 (a - j) x) =
        -((2 * c) • EEC c (s + a + 1) x) := by
      calc
        _ = -(-(EEC c (s + j) (sectorCurrentDist 0 (a - j) x))) := by abel
        _ = _ := by rw [hcur]
    rw [hEJ]
    module
  have hright : ∀ j, R ≤ j → F j =
      0 := by
    intro j hj
    have hjR₀ : R₀ ≤ j := le_trans (le_max_right _ _) hj
    have hJzero : sectorCurrentDist 0 (a - j) x = 0 :=
      hBJ (a - j) (by simp only [R₀] at hjR₀; omega)
    simp only [F, hJzero, map_zero, smul_zero]
  have htel := finsum_succ_sub_eq_of_tails F
    (-((2 * c) • ((2 * c) • EEC c (s + a + 1) x))) 0 L R hLR hleft hright
  rw [currentNprodEECBracket_apply, currentNprodEECBracket_apply,
    ← finsum_sub_distrib
      (currentNprodEECBracket_family_finite c (a - 1) s x)
      (currentNprodEECBracket_family_finite c a (s - 1) x)]
  rw [show (∑ᶠ j : ℤ,
      ((normalOrdered (sectorCurrentDist c) (sectorCurrentDist c) j (a - 1 - j) * EEC c s -
          EEC c s * normalOrdered (sectorCurrentDist 0) (sectorCurrentDist 0) j (a - 1 - j)) x -
        (normalOrdered (sectorCurrentDist c) (sectorCurrentDist c) j (a - j) * EEC c (s - 1) -
          EEC c (s - 1) * normalOrdered (sectorCurrentDist 0) (sectorCurrentDist 0) j (a - j)) x)) =
      ∑ᶠ j : ℤ, (F (j + 1) - F j) from finsum_congr fun j => by
        rw [normalOrdered_sectorCurrentDist_EEC c j (a - 1 - j) s,
          normalOrdered_sectorCurrentDist_EEC c j (a - j) (s - 1)]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
          Module.End.mul_apply, F]
        rw [show s + (a - 1 - j) + 1 = s + a - j by ring,
          show s - 1 + (a - j) + 1 = s + a - j by ring,
          show a - (j + 1) = a - 1 - j by ring,
          show s + (j + 1) = s + j + 1 by ring,
          show s - 1 + j + 1 = s + j by ring]
        module]
  rw [htel, zero_sub, neg_neg]

/-- The second field-index difference vanishes: the heterotypic Sugawara bracket has exact
locality order two. -/
theorem currentNprodEECBracket_secondDifference (c : ℂ) (a s : ℤ) :
    currentNprodEECBracket c (a - 2) s -
        (2 : ℂ) • currentNprodEECBracket c (a - 1) (s - 1) +
        currentNprodEECBracket c a (s - 2) = 0 := by
  have h₁ := currentNprodEECBracket_firstDifference c (a - 1) s
  have h₂ := currentNprodEECBracket_firstDifference c a (s - 1)
  rw [show a - 1 - 1 = a - 2 by ring,
    show s + (a - 1) + 1 = s + a by ring] at h₁
  rw [show s - 1 + a + 1 = s + a by ring] at h₂
  rw [show s - 1 - 1 = s - 2 by ring] at h₂
  rw [two_smul]
  calc
    currentNprodEECBracket c (a - 2) s -
          (currentNprodEECBracket c (a - 1) (s - 1) +
            currentNprodEECBracket c (a - 1) (s - 1)) +
          currentNprodEECBracket c a (s - 2) =
        (currentNprodEECBracket c (a - 2) s -
          currentNprodEECBracket c (a - 1) (s - 1)) -
        (currentNprodEECBracket c (a - 1) (s - 1) -
          currentNprodEECBracket c a (s - 2)) := by abel
    _ = 0 := by rw [h₁, h₂, sub_self]

end
end LeeYangHeterotypicLocality
end InverseDS
end VOA
