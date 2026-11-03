/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3Oscillators
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.Interval

/-!
# Finite normal products in the sl3 polynomial representation

Locally finite operator sums construct the coloured beta-gamma, gamma-gamma
and boson-gamma products. The cutoff bounds justify these sums on each
polynomial, without an analytic convergence premise. The bilinear ghost
products have the expected elementary commutators and give the three
raising currents and their positive-root bracket. These results do not
yet assemble the lowering currents or the full affine representation.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open scoped BigOperators
open Classical

/-- A `ℤ`-indexed family of operators is **locally finite** when, on each vector, only finitely
many members are nonzero. -/
def LocFin (T : ℤ → Module.End ℂ Fock) : Prop :=
  ∀ P : Fock, (Function.support fun p : ℤ => T p P).Finite

open Classical in
/-- The operator sum `∑ᶠ p, T p` of a locally finite family (junk value `0` otherwise). -/
noncomputable def opSum (T : ℤ → Module.End ℂ Fock) : Module.End ℂ Fock :=
  if h : LocFin T then
    { toFun := fun P => ∑ᶠ p : ℤ, T p P
      map_add' := fun P Q => by
        rw [← finsum_add_distrib (h P) (h Q)]
        exact finsum_congr fun p => map_add _ P Q
      map_smul' := fun c P => by
        rw [RingHom.id_apply, smul_finsum' c (h P)]
        exact finsum_congr fun p => map_smul _ c P }
  else 0

/-- Evaluate the locally finite operator sum on a polynomial. -/
theorem opSum_apply {T : ℤ → Module.End ℂ Fock} (h : LocFin T) (P : Fock) :
    opSum T P = ∑ᶠ p : ℤ, T p P := by
  rw [opSum, dif_pos h]; rfl

/-- Local finiteness from an explicit two-sided index bound. -/
theorem locFin_of_bounds {T : ℤ → Module.End ℂ Fock}
    (H : ∀ P : Fock, ∃ A B : ℤ, ∀ p : ℤ, (p < A ∨ B < p) → T p P = 0) : LocFin T := by
  intro P
  obtain ⟨A, B, hAB⟩ := H P
  refine Set.Finite.subset (Set.finite_Icc A B) ?_
  intro p hp
  simp only [Function.mem_support] at hp
  rw [Set.mem_Icc]
  by_contra hc
  exact hp (hAB p (by omega))

/-- A family supported at a single index is locally finite. -/
theorem locFin_ite (p₀ : ℤ) (A : Module.End ℂ Fock) :
    LocFin (fun p => if p = p₀ then A else 0) := by
  refine locFin_of_bounds fun P => ⟨p₀, p₀, fun p hp => ?_⟩
  rw [if_neg (show ¬ p = p₀ by omega)]
  simp

/-- The operator sum of a family supported at a single index. -/
theorem opSum_ite (p₀ : ℤ) (A : Module.End ℂ Fock) :
    opSum (fun p => if p = p₀ then A else 0) = A := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (locFin_ite p₀ A) P,
    finsum_eq_single _ p₀ (fun x hx => by rw [if_neg hx]; rfl), if_pos rfl]

/-- Local finiteness is preserved by pointwise addition. -/
theorem LocFin.add {T U : ℤ → Module.End ℂ Fock} (hT : LocFin T) (hU : LocFin U) :
    LocFin (fun p => T p + U p) := by
  intro P
  refine Set.Finite.subset ((hT P).union (hU P)) ?_
  intro p hp
  simp only [Function.mem_support, LinearMap.add_apply] at hp
  by_contra hc
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
  exact hp (by rw [hc.1, hc.2, add_zero])

/-- Local finiteness is preserved by scaling. -/
theorem LocFin.smul (c : ℂ) {T : ℤ → Module.End ℂ Fock} (hT : LocFin T) :
    LocFin (fun p => c • T p) := by
  intro P
  refine Set.Finite.subset (hT P) ?_
  intro p hp
  simp only [Function.mem_support, LinearMap.smul_apply] at hp ⊢
  intro hz; exact hp (by rw [hz, smul_zero])

/-- Operator sums are additive. -/
theorem opSum_add {T U : ℤ → Module.End ℂ Fock} (hT : LocFin T) (hU : LocFin U) :
    opSum (fun p => T p + U p) = opSum T + opSum U := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (hT.add hU) P]
  simp only [LinearMap.add_apply]
  rw [opSum_apply hT P, opSum_apply hU P, ← finsum_add_distrib (hT P) (hU P)]

/-- Operator sums commute with scaling. -/
theorem opSum_smul (c : ℂ) {T : ℤ → Module.End ℂ Fock} (hT : LocFin T) :
    opSum (fun p => c • T p) = c • opSum T := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (hT.smul c) P, LinearMap.smul_apply, opSum_apply hT P,
    smul_finsum' c (hT P)]
  exact finsum_congr fun p => rfl

/-- **The commutator passes through an operator sum.** -/
theorem opSum_lie {T : ℤ → Module.End ℂ Fock} (hT : LocFin T) (S : Module.End ℂ Fock)
    (h' : LocFin fun p => ⁅T p, S⁆) : ⁅opSum T, S⁆ = opSum (fun p => ⁅T p, S⁆) := by
  refine LinearMap.ext fun P => ?_
  have hs : (Function.support fun p : ℤ => S (T p P)).Finite := by
    refine Set.Finite.subset (hT P) ?_
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    intro hz; exact hp (by rw [hz, map_zero])
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [opSum_apply hT (S P), opSum_apply hT P, opSum_apply h' P, map_finsum S (hT P),
    ← finsum_sub_distrib (hT (S P)) hs]
  refine finsum_congr fun p => ?_
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]

/-- Leibniz rule for the commutator in the left slot. -/
theorem lie_mul_left (A B C : Module.End ℂ Fock) :
    ⁅A * B, C⁆ = A * ⁅B, C⁆ + ⁅A, C⁆ * B := by
  simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc]; abel

/-- Leibniz rule for the commutator in the right slot. -/
theorem lie_mul_right (A B C : Module.End ℂ Fock) :
    ⁅A, B * C⁆ = ⁅A, B⁆ * C + B * ⁅A, C⁆ := by
  simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc]; abel

/-- The summands of the coloured product :beta_i gamma_j:, with beta
creation modes on the left and its annihilation modes on the right. -/
def bgFam (i j : Fin 3) (n p : ℤ) : Module.End ℂ Fock :=
  if p ≤ -1 then beta i p * gamma j (n-p) else gamma j (n-p) * beta i p

/-- Every beta-gamma coefficient has finite support on each polynomial. -/
theorem bgFam_locFin (i j : Fin 3) (n : ℤ) : LocFin (bgFam i j n) := by
  refine locFin_of_bounds fun P => ⟨min (n-cutoff P+1) 0, cutoff P-1, fun p hp => ?_⟩
  have h2 := two_le_cutoff P
  rcases hp with hp | hp
  · rw [bgFam, if_pos (by omega), Module.End.mul_apply, gamma_above (P := P) _ (by omega), map_zero]
  · rw [bgFam, if_neg (by omega), Module.End.mul_apply, beta_above _ (by omega), map_zero]

/-- The actual coloured beta-gamma normal product. -/
def BG (i j : Fin 3) (n : ℤ) : Module.End ℂ Fock := opSum (bgFam i j n)

/-- The gamma-gamma product keeps the nonpositive first gamma modes on the left. -/
def ggFam (i j : Fin 3) (n p : ℤ) : Module.End ℂ Fock :=
  if p ≤ 0 then gamma i p * gamma j (n-p) else gamma j (n-p) * gamma i p

/-- Gamma-gamma coefficients are locally finite, including both zero modes. -/
theorem ggFam_locFin (i j : Fin 3) (n : ℤ) : LocFin (ggFam i j n) := by
  refine locFin_of_bounds fun P => ⟨min (n-cutoff P+1) 0, cutoff P-1, fun p hp => ?_⟩
  have h2 := two_le_cutoff P
  rcases hp with hp | hp
  · rw [ggFam, if_pos (by omega), Module.End.mul_apply, gamma_above (P := P) _ (by omega), map_zero]
  · rw [ggFam, if_neg (by omega), Module.End.mul_apply, gamma_above (P := P) _ (by omega), map_zero]

/-- The actual product of two gamma fields, used inside higher composites. -/
def GG (i j : Fin 3) (n : ℤ) : Module.End ℂ Fock := opSum (ggFam i j n)

/-- Boson-gamma normal ordering at arbitrary level. -/
def agFam (k : ℂ) (i : Fin 2) (j : Fin 3) (n p : ℤ) : Module.End ℂ Fock :=
  if p ≤ -1 then boson k i p * gamma j (n-p) else gamma j (n-p) * boson k i p

/-- The Cartan coupling does not obstruct local finiteness of the mixed product. -/
theorem agFam_locFin (k : ℂ) (i : Fin 2) (j : Fin 3) (n : ℤ) :
    LocFin (agFam k i j n) := by
  refine locFin_of_bounds fun P => ⟨min (n-cutoff P+1) 0, cutoff P-1, fun p hp => ?_⟩
  have h2 := two_le_cutoff P
  rcases hp with hp | hp
  · rw [agFam, if_pos (by omega), Module.End.mul_apply, gamma_above (P := P) _ (by omega), map_zero]
  · rw [agFam, if_neg (by omega), Module.End.mul_apply, boson_above k _ (by omega), map_zero]

/-- The actual mixed boson-gamma normal product. -/
def AG (k : ℂ) (i : Fin 2) (j : Fin 3) (n : ℤ) : Module.End ℂ Fock :=
  opSum (agFam k i j n)

/-- The zero family is locally finite. -/
theorem locFin_zero : LocFin (fun _ : ℤ => (0 : Module.End ℂ Fock)) :=
  locFin_of_bounds fun _ => ⟨0,0,fun _ _ => rfl⟩

/-- Its operator sum is zero. -/
theorem opSum_zero : opSum (fun _ : ℤ => (0 : Module.End ℂ Fock)) = 0 := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply locFin_zero P]
  simp

/-- Reversing the beta-gamma commutator changes its sign. -/
theorem gamma_beta (i j : Fin 3) (m n : ℤ) :
    ⁅gamma j n, beta i m⁆ = -(if i=j ∧ m+n=0 then (1 : Module.End ℂ Fock) else 0) := by
  rw [← lie_skew, beta_gamma]

/-- Commutation with beta contracts only the matching gamma colour and
produces minus the surviving beta mode at the sum of indices. -/
theorem BG_lie_beta (i j l : Fin 3) (n r : ℤ) : ⁅BG i j n, beta l r⁆ = if l=j then -beta i (n+r) else 0 := by
  by_cases hj : l=j
  swap
  · have hf : (fun p => ⁅bgFam i j n p, beta l r⁆) = fun _ => (0 : Module.End ℂ Fock) := by
      funext p; unfold bgFam; split_ifs <;> simp [lie_mul_left, beta_beta, gamma_beta, hj]
    rw [BG, opSum_lie (bgFam_locFin i j n) _ (by rw [hf]; exact locFin_zero), hf, opSum_zero, if_neg hj]
  rw [if_pos hj]

  have hfam : (fun p => ⁅bgFam i j n p, beta l r⁆)
      = fun p => if p = n + r then -beta i (n + r) else 0 := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, lie_mul_left, beta_beta, zero_mul, add_zero, gamma_beta]
      simp only [hj, true_and]
      by_cases h : p = n + r
      · rw [if_pos (show r + (n - p) = 0 by omega), if_pos h]
        subst p
        refine LinearMap.ext fun P => ?_
        simp [Module.End.mul_apply]
      · rw [if_neg (show ¬ (r + (n - p) = 0) by omega), if_neg h, neg_zero, mul_zero]
    · rw [bgFam, if_neg hp, lie_mul_left, beta_beta, mul_zero, zero_add, gamma_beta]
      simp only [hj, true_and]
      by_cases h : p = n + r
      · rw [if_pos (show r + (n - p) = 0 by omega), if_pos h]
        subst p
        refine LinearMap.ext fun P => ?_
        simp [Module.End.mul_apply]
      · rw [if_neg (show ¬ (r + (n - p) = 0) by omega), if_neg h, neg_zero, zero_mul]
  rw [BG, opSum_lie (bgFam_locFin i j n) (beta l r) (by rw [hfam]; exact locFin_ite _ _), hfam,
    opSum_ite]

/-- Commutation with gamma contracts only the matching beta colour and
produces the surviving gamma mode at the sum of indices. -/
theorem BG_lie_gamma (i j l : Fin 3) (n u : ℤ) : ⁅BG i j n, gamma l u⁆ = if i=l then gamma j (n+u) else 0 := by
  by_cases hi : i=l
  swap
  · have hf : (fun p => ⁅bgFam i j n p, gamma l u⁆) = fun _ => (0 : Module.End ℂ Fock) := by
      funext p; unfold bgFam; split_ifs <;> simp [lie_mul_left, gamma_gamma, beta_gamma, hi]
    rw [BG, opSum_lie (bgFam_locFin i j n) _ (by rw [hf]; exact locFin_zero), hf, opSum_zero, if_neg hi]
  rw [if_pos hi]

  have hfam : (fun p => ⁅bgFam i j n p, gamma l u⁆)
      = fun p => if p = -u then gamma j (n + u) else 0 := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, lie_mul_left, gamma_gamma, mul_zero, zero_add, beta_gamma]
      simp only [hi, true_and]
      by_cases h : p = -u
      · rw [if_pos (show p + u = 0 by omega), if_pos h, one_mul,
          show n - p = n + u by omega]
      · rw [if_neg (show ¬ (p + u = 0) by omega), if_neg h, zero_mul]
    · rw [bgFam, if_neg hp, lie_mul_left, gamma_gamma, zero_mul, add_zero, beta_gamma]
      simp only [hi, true_and]
      by_cases h : p = -u
      · rw [if_pos (show p + u = 0 by omega), if_pos h, mul_one,
          show n - p = n + u by omega]
      · rw [if_neg (show ¬ (p + u = 0) by omega), if_neg h, mul_zero]
  rw [BG, opSum_lie (bgFam_locFin i j n) (gamma l u) (by rw [hfam]; exact locFin_ite _ _), hfam,
    opSum_ite]


/-- Nonnegative beta-gamma modes annihilate the polynomial vacuum. -/
theorem BG_vacuum (i j : Fin 3) {n : ℤ} (hn : 0 ≤ n) : BG i j n 1 = 0 := by
  rw [BG, opSum_apply (bgFam_locFin i j n)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : p ≤ -1
  · rw [bgFam, if_pos hp, Module.End.mul_apply, gamma_vacuum _ _ (by omega), map_zero]
  · rw [bgFam, if_neg hp, Module.End.mul_apply, beta_vacuum _ _ (by omega), map_zero]

/-- Nonnegative boson-gamma modes also annihilate the vacuum. -/
theorem AG_vacuum (k : ℂ) (i : Fin 2) (j : Fin 3) {n : ℤ} (hn : 0 ≤ n) :
    AG k i j n 1 = 0 := by
  rw [AG, opSum_apply (agFam_locFin k i j n)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : p ≤ -1
  · rw [agFam, if_pos hp, Module.End.mul_apply, gamma_vacuum _ _ (by omega), map_zero]
  · rw [agFam, if_neg hp, Module.End.mul_apply, boson_vacuum _ _ _ (by omega), map_zero]

/-- A gamma-gamma product kills the vacuum at strictly positive total index;
its zero mode need not vanish. -/
theorem GG_vacuum (i j : Fin 3) {n : ℤ} (hn : 0 < n) : GG i j n 1 = 0 := by
  rw [GG, opSum_apply (ggFam_locFin i j n)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : p ≤ 0
  · rw [ggFam, if_pos hp, Module.End.mul_apply, gamma_vacuum _ _ (by omega), map_zero]
  · rw [ggFam, if_neg hp, Module.End.mul_apply, gamma_vacuum _ _ (by omega), map_zero]

/-- Commuting gamma modes can be reordered across colours. -/
theorem gamma_comm (i j : Fin 3) (m n : ℤ) :
    gamma i m * gamma j n = gamma j n * gamma i m := by
  have h := gamma_gamma i j m n
  rwa [Ring.lie_def, sub_eq_zero] at h

/-- At nonzero total index, beta and gamma commute even for matching colours. -/
theorem beta_gamma_comm (i j : Fin 3) (m n : ℤ) (h : m+n ≠ 0) :
    beta i m * gamma j n = gamma j n * beta i m := by
  have he := beta_gamma i j m n
  simpa [Ring.lie_def, h, sub_eq_zero] using he

/-- Gamma-gamma truncation holds at twice the input polynomial cutoff. -/
theorem GG_above (i j : Fin 3) {P : Fock} {n : ℤ} (hn : 2*cutoff P ≤ n) :
    GG i j n P = 0 := by
  have h2 := two_le_cutoff P
  rw [GG, opSum_apply (ggFam_locFin i j n)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : p ≤ 0
  · rw [ggFam, if_pos hp, Module.End.mul_apply,
      gamma_above (P := P) _ (by omega), map_zero]
  · by_cases hp2 : cutoff P ≤ p
    · rw [ggFam, if_neg hp, Module.End.mul_apply,
        gamma_above (P := P) _ hp2, map_zero]
    · rw [ggFam, if_neg hp, gamma_comm, Module.End.mul_apply,
        gamma_above (P := P) _ (by omega), map_zero]

/-- Beta-gamma truncation follows by reordering the middle range, where
the total positive index excludes the scalar commutator. -/
theorem BG_above (i j : Fin 3) {P : Fock} {n : ℤ} (hn : 2*cutoff P ≤ n) :
    BG i j n P = 0 := by
  have h2 := two_le_cutoff P
  rw [BG, opSum_apply (bgFam_locFin i j n)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : p ≤ -1
  · rw [bgFam, if_pos hp, Module.End.mul_apply,
      gamma_above (P := P) _ (by omega), map_zero]
  · by_cases hp2 : cutoff P ≤ p
    · rw [bgFam, if_neg hp, Module.End.mul_apply, beta_above _ hp2, map_zero]
    · rw [bgFam, if_neg hp, ← beta_gamma_comm i j p (n-p) (by omega),
        Module.End.mul_apply, gamma_above (P := P) _ (by omega), map_zero]

/-- Simple-root raising current E1=beta1-:beta3 gamma2:. -/
def E1 (n : ℤ) : Module.End ℂ Fock := beta 0 n - BG 2 1 n

/-- Simple-root raising current E2=beta2. -/
def E2 (n : ℤ) : Module.End ℂ Fock := beta 1 n

/-- Highest-root raising current E12=beta3. -/
def E12 (n : ℤ) : Module.End ℂ Fock := beta 2 n

/-- The actual two simple raising currents bracket to the highest-root current,
with the sign fixed by E12=[E1,E2] in the matrix Chevalley basis. -/
theorem E1_E2 (m n : ℤ) : ⁅E1 m, E2 n⁆ = E12 (m+n) := by
  simp [E1, E2, E12, sub_lie, beta_beta, BG_lie_beta]

/-- E1 commutes with the highest-root raising current. -/
theorem E1_E12 (m n : ℤ) : ⁅E1 m, E12 n⁆ = 0 := by
  simp [E1, E12, sub_lie, beta_beta, BG_lie_beta]

/-- E2 commutes with the highest-root raising current. -/
theorem E2_E12 (m n : ℤ) : ⁅E2 m, E12 n⁆ = 0 := beta_beta _ _ _ _

/-- Nonnegative E1 modes kill the polynomial vacuum. -/
theorem E1_vacuum {n : ℤ} (hn : 0 ≤ n) : E1 n 1 = 0 := by
  simp [E1, beta_vacuum _ _ hn, BG_vacuum _ _ hn]

/-- Nonnegative E2 modes kill the polynomial vacuum. -/
theorem E2_vacuum {n : ℤ} (hn : 0 ≤ n) : E2 n 1 = 0 := beta_vacuum _ _ hn

/-- Nonnegative highest-root raising modes kill the polynomial vacuum. -/
theorem E12_vacuum {n : ℤ} (hn : 0 ≤ n) : E12 n 1 = 0 := beta_vacuum _ _ hn

/-- The composite raising current has a proved cutoff on each polynomial. -/
theorem E1_above {P : Fock} {n : ℤ} (hn : 2*cutoff P ≤ n) : E1 n P = 0 := by
  have h2 := two_le_cutoff P
  simp [E1, beta_above _ (P := P) (m := n) (by omega), BG_above _ _ hn]

/-- Off-diagonal beta-gamma currents commute with themselves at all indices:
both possible colour contractions vanish. This does not assert the
corresponding statement for diagonal ghost currents. -/
theorem BG_self_offdiagonal (i j : Fin 3) (hij : i ≠ j) (m n : ℤ) :
    ⁅BG i j m, BG i j n⁆ = 0 := by
  have hb (p : ℤ) : ⁅beta i p, BG i j n⁆ = 0 := by
    rw [← lie_skew, BG_lie_beta, if_neg hij, neg_zero]
  have hg (p : ℤ) : ⁅gamma j p, BG i j n⁆ = 0 := by
    rw [← lie_skew, BG_lie_gamma, if_neg hij, neg_zero]
  have hf : (fun p => ⁅bgFam i j m p, BG i j n⁆) =
      fun _ => (0 : Module.End ℂ Fock) := by
    funext p
    unfold bgFam
    split_ifs <;> simp [lie_mul_left, hb, hg]
  rw [BG, opSum_lie (bgFam_locFin i j m) _ (by rw [hf]; exact locFin_zero),
    hf, opSum_zero]

/-- E1 has no self-commutator, including its composite ghost contribution. -/
theorem E1_E1 (m n : ℤ) : ⁅E1 m, E1 n⁆ = 0 := by
  have hb : ⁅beta 0 m, BG 2 1 n⁆ = 0 := by
    rw [← lie_skew, BG_lie_beta]
    norm_num
  simp [E1, sub_lie, lie_sub, beta_beta, hb, BG_lie_beta,
    BG_self_offdiagonal 2 1 (by decide)]

/-- E2 has no self-commutator. -/
theorem E2_E2 (m n : ℤ) : ⁅E2 m, E2 n⁆ = 0 := beta_beta _ _ _ _

/-- The highest-root raising current has no self-commutator. -/
theorem E12_E12 (m n : ℤ) : ⁅E12 m, E12 n⁆ = 0 := beta_beta _ _ _ _

end
end VOA.AffineSl3.FreeField
