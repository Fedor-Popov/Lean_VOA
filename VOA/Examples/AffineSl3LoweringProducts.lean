/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3GhostCentral

/-!
# Cubic ghost products for the simple lowering currents

All colours are retained in the gamma-pair contraction, so repeated
colours contribute twice. Locally finite beta-gamma-gamma sums then give
actual polynomial operators, rather than formal infinite expressions.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- Gamma-gamma summands can be written without their ordering split,
because all gamma modes commute, even between different colours. -/
theorem ggFam_eq (i j : Fin 3) (n p : ℤ) :
    ggFam i j n p = gamma i p * gamma j (n-p) := by
  unfold ggFam
  split_ifs
  · rfl
  · exact (gamma_comm i j p (n-p)).symm

/-- Contracting beta against a gamma pair has two contributions; when
the colours coincide these add rather than representing distinct modes. -/
theorem GG_beta (i j l : Fin 3) (n r : ℤ) :
    ⁅GG i j n,beta l r⁆ =
      (if l=j then (-1 : ℂ) else 0) • gamma i (n+r) +
      (if l=i then (-1 : ℂ) else 0) • gamma j (n+r) := by
  let A : Module.End ℂ Fock := (if l=j then (-1 : ℂ) else 0) • gamma i (n+r)
  let B : Module.End ℂ Fock := (if l=i then (-1 : ℂ) else 0) • gamma j (n+r)
  have hf : (fun p => ⁅ggFam i j n p,beta l r⁆) =
      fun p => (if p=n+r then A else 0)+(if p= -r then B else 0) := by
    funext p
    rw [ggFam_eq,lie_mul_left,gamma_beta,gamma_beta]
    have h1 : r+(n-p)=0 ↔ p=n+r := by omega
    have h2 : r+p=0 ↔ p= -r := by omega
    by_cases ha : l=j <;> by_cases hb : l=i <;>
      by_cases hp : p=n+r <;> by_cases hq : p= -r
    all_goals
      try have ht : n-p=n+r := by omega
      simp_all only [A,B,h1,h2,true_and,false_and,ite_true,ite_false]
      refine LinearMap.ext fun P => ?_
      simp_all [Module.End.mul_apply]
      all_goals module
  change ⁅opSum (ggFam i j n),beta l r⁆ = A+B
  rw [opSum_lie (ggFam_locFin i j n) _ (by rw [hf]; exact (locFin_ite _ _).add (locFin_ite _ _)),
    hf,opSum_add (locFin_ite _ _) (locFin_ite _ _),opSum_ite,opSum_ite]

/-- Every gamma-pair product commutes with every gamma mode. -/
theorem GG_gamma (i j l : Fin 3) (n r : ℤ) : ⁅GG i j n,gamma l r⁆ = 0 := by
  have hf : (fun p => ⁅ggFam i j n p,gamma l r⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p; simp [ggFam_eq,lie_mul_left,gamma_gamma]
  rw [GG,opSum_lie (ggFam_locFin i j n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- Cubic beta-gamma-gamma summands, with the beta creation modes on the left. -/
def bggFam (a i j : Fin 3) (n p : ℤ) : Module.End ℂ Fock :=
  if p ≤ -1 then beta a p * GG i j (n-p) else GG i j (n-p) * beta a p

/-- The gamma-pair cutoff proves actual local finiteness of the cubic product. -/
theorem bggFam_locFin (a i j : Fin 3) (n : ℤ) : LocFin (bggFam a i j n) := by
  refine locFin_of_bounds fun P => ⟨min (n-2*cutoff P+1) 0,cutoff P-1,fun p hp => ?_⟩
  have h2 := two_le_cutoff P
  rcases hp with hp | hp
  · rw [bggFam,if_pos (by omega),Module.End.mul_apply,GG_above _ _ (by omega),map_zero]
  · rw [bggFam,if_neg (by omega),Module.End.mul_apply,beta_above _ (by omega),map_zero]

/-- The actual cubic normal product :beta_a gamma_i gamma_j:. -/
def BGG (a i j : Fin 3) (n : ℤ) : Module.End ℂ Fock := opSum (bggFam a i j n)

/-- A cubic product has the expected two beta contractions, including
multiplicity two when both gamma colours match. -/
theorem BGG_beta (a i j l : Fin 3) (n r : ℤ) :
    ⁅BGG a i j n,beta l r⁆ =
      (if l=j then (-1 : ℂ) else 0) • BG a i (n+r) +
      (if l=i then (-1 : ℂ) else 0) • BG a j (n+r) := by
  let c : ℂ := if l=j then -1 else 0
  let d : ℂ := if l=i then -1 else 0
  have hf : (fun p => ⁅bggFam a i j n p,beta l r⁆) =
      fun p => c • bgFam a i (n+r) p + d • bgFam a j (n+r) p := by
    funext p
    by_cases hp : p ≤ -1
    all_goals
      simp only [bggFam,hp,ite_true,ite_false,lie_mul_left,beta_beta,
        zero_mul,mul_zero,zero_add,add_zero,GG_beta,bgFam]
      simp only [hp,ite_true,ite_false,show n-p+r=n+r-p by ring,c,d,
        mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  change ⁅opSum (bggFam a i j n),beta l r⁆ = _
  rw [opSum_lie (bggFam_locFin a i j n) _
      (by rw [hf]; exact ((bgFam_locFin a i (n+r)).smul c).add ((bgFam_locFin a j (n+r)).smul d)),
    hf,opSum_add ((bgFam_locFin a i (n+r)).smul c) ((bgFam_locFin a j (n+r)).smul d),
    opSum_smul c (bgFam_locFin a i (n+r)),opSum_smul d (bgFam_locFin a j (n+r))]
  rfl

/-- Nonnegative cubic modes annihilate the polynomial vacuum. -/
theorem BGG_vacuum (a i j : Fin 3) {n : ℤ} (hn : 0 ≤ n) : BGG a i j n 1 = 0 := by
  rw [BGG,opSum_apply (bggFam_locFin a i j n)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : p ≤ -1
  · rw [bggFam,if_pos hp,Module.End.mul_apply,GG_vacuum _ _ (by omega),map_zero]
  · rw [bggFam,if_neg hp,Module.End.mul_apply,beta_vacuum _ _ (by omega),map_zero]

/-- The mixed boson-gamma product contracts only its gamma colour against beta. -/
theorem AG_beta (k : ℂ) (a : Fin 2) (j l : Fin 3) (n r : ℤ) :
    ⁅AG k a j n,beta l r⁆ = (if l=j then (-1 : ℂ) else 0) • boson k a (n+r) := by
  let A : Module.End ℂ Fock := (if l=j then (-1 : ℂ) else 0) • boson k a (n+r)
  have hf : (fun p => ⁅agFam k a j n p,beta l r⁆) = fun p => if p=n+r then A else 0 := by
    funext p
    have h1 : r+(n-p)=0 ↔ p=n+r := by omega
    by_cases hp : p ≤ -1 <;> by_cases hj : l=j <;> by_cases hq : p=n+r
    all_goals
      simp only [agFam,hp,ite_true,ite_false,lie_mul_left,boson_beta,
        mul_zero,zero_mul,add_zero,zero_add,gamma_beta]
      simp_all only [A,h1,true_and,false_and,ite_true,ite_false]
      refine LinearMap.ext fun P => ?_
      simp_all [Module.End.mul_apply]
  change ⁅opSum (agFam k a j n),beta l r⁆ = A
  rw [opSum_lie (agFam_locFin k a j n) _ (by rw [hf]; exact locFin_ite _ _),hf,opSum_ite]

/-- Contracting gamma against the beta of a cubic product leaves the gamma pair. -/
theorem BGG_gamma (a i j l : Fin 3) (n r : ℤ) :
    ⁅BGG a i j n,gamma l r⁆ = if a=l then GG i j (n+r) else 0 := by
  have hf : (fun p => ⁅bggFam a i j n p,gamma l r⁆) =
      fun p => if p= -r then (if a=l then GG i j (n+r) else 0) else 0 := by
    funext p
    have h1 : p+r=0 ↔ p= -r := by omega
    by_cases hp : p ≤ -1 <;> by_cases ha : a=l <;> by_cases hq : p= -r
    all_goals
      simp only [bggFam,hp,ite_true,ite_false,lie_mul_left,GG_gamma,
        mul_zero,zero_mul,add_zero,zero_add,beta_gamma]
      simp_all [h1,show n-(-r)=n+r by ring]
  rw [BGG,opSum_lie (bggFam_locFin a i j n) _ (by rw [hf]; exact locFin_ite _ _),hf,opSum_ite]

/-- First simple lowering current, including its k+1 derivative correction. -/
def F1 (k : ℂ) (n : ℤ) : Module.End ℂ Fock :=
  -BGG 0 0 0 n-BG 1 2 n-((k+1)*(n : ℂ)) • gamma 0 n+AG k 0 0 n

/-- Second simple lowering current. Its derivative correction is k, not k+1. -/
def F2 (k : ℂ) (n : ℤ) : Module.End ℂ Fock :=
  BGG 0 0 1 n+BG 0 2 n-BGG 1 1 1 n-BGG 2 1 2 n-
    (k*(n : ℂ)) • gamma 1 n+AG k 1 1 n

/-- Every nonnegative first lowering mode kills the polynomial vacuum;
the derivative coefficient cancels the gamma zero mode. -/
theorem F1_vacuum (k : ℂ) {n : ℤ} (hn : 0 ≤ n) : F1 k n 1 = 0 := by
  by_cases hz : n=0
  · subst n; simp [F1,BGG_vacuum _ _ _ (by omega),BG_vacuum _ _ (by omega),AG_vacuum _ _ _ (by omega)]
  · simp [F1,BGG_vacuum _ _ _ hn,BG_vacuum _ _ hn,AG_vacuum _ _ _ hn,gamma_vacuum _ n (by omega)]

/-- The second lowering modes obey the same vacuum annihilation condition. -/
theorem F2_vacuum (k : ℂ) {n : ℤ} (hn : 0 ≤ n) : F2 k n 1 = 0 := by
  by_cases hz : n=0
  · subst n; simp [F2,BGG_vacuum _ _ _ (by omega),BG_vacuum _ _ (by omega),AG_vacuum _ _ _ (by omega)]
  · simp [F2,BGG_vacuum _ _ _ hn,BG_vacuum _ _ hn,AG_vacuum _ _ _ hn,gamma_vacuum _ n (by omega)]

/-- The second raising current commutes with the first lowering current. -/
theorem E2_F1 (k : ℂ) (m n : ℤ) : ⁅E2 m,F1 k n⁆ = 0 := by
  rw [← lie_skew]
  simp [E2,F1,add_lie,sub_lie,neg_lie,comm_smul_left,BGG_beta,BG_lie_beta,AG_beta,gamma_beta]

/-- The highest-root raising current contracts F1 to minus E2. -/
theorem E12_F1 (k : ℂ) (m n : ℤ) : ⁅E12 m,F1 k n⁆ = -E2 (m+n) := by
  rw [← lie_skew]
  simp [E12,E2,F1,add_lie,sub_lie,neg_lie,comm_smul_left,BGG_beta,BG_lie_beta,AG_beta,gamma_beta,add_comm]

/-- The highest-root raising current contracts F2 to E1. -/
theorem E12_F2 (k : ℂ) (m n : ℤ) : ⁅E12 m,F2 k n⁆ = E1 (m+n) := by
  rw [← lie_skew]
  simp [E12,E1,F2,add_lie,sub_lie,neg_lie,comm_smul_left,BGG_beta,BG_lie_beta,AG_beta,gamma_beta,add_comm] <;> module

/-- The second simple raising/lowering bracket has the actual level k
central term, as well as the second Cartan current. -/
theorem E2_F2 (k : ℂ) (m n : ℤ) : ⁅E2 m,F2 k n⁆ =
    H2 k (m+n)+(if m+n=0 then (k*(m : ℂ)) • (1 : Module.End ℂ Fock) else 0) := by
  rw [← lie_skew]
  by_cases hz : m+n=0
  · have hc : (n : ℂ) = -(m : ℂ) := by exact_mod_cast (show n= -m by omega)
    simp [E2,F2,H2,add_lie,sub_lie,comm_smul_left,BGG_beta,BG_lie_beta,AG_beta,gamma_beta,
      hz,show n+m=0 by omega,add_comm,hc] <;> module
  · simp [E2,F2,H2,add_lie,sub_lie,comm_smul_left,BGG_beta,BG_lie_beta,AG_beta,gamma_beta,
      hz,show n+m≠0 by omega,add_comm] <;> module

end
end VOA.AffineSl3.FreeField
