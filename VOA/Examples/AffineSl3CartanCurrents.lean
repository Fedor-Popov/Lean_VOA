/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3NormalProducts

/-!
# Actual Cartan currents and their raising-root actions

The two Cartan currents combine diagonal ghost normal products with the
Cartan bosons. Their actions on free oscillators and the three raising
currents have the A2 weights. Local finiteness, vacuum annihilation and
truncation are proved for these operators. The Cartan-Cartan central
anomaly and all lowering-current relations remain separate obligations.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- Shifting the integer summation index preserves local finiteness. -/
theorem LocFin.shift (c : ℤ) {T : ℤ → Module.End ℂ Fock} (hT : LocFin T) :
    LocFin (fun p => T (c+p)) := by
  intro P
  exact Set.Finite.preimage (add_right_injective c).injOn (hT P)

/-- A locally finite operator sum is unchanged by an integer shift. -/
theorem opSum_shift (c : ℤ) {T : ℤ → Module.End ℂ Fock} (hT : LocFin T) :
    opSum (fun p => T (c+p)) = opSum T := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (hT.shift c), opSum_apply hT]
  exact finsum_comp_equiv (Equiv.addLeft c) (f := fun p : ℤ => T p P)

/-- A commutator also passes through a locally finite sum in its second slot. -/
theorem lie_opSum {T : ℤ → Module.End ℂ Fock} (hT : LocFin T)
    (S : Module.End ℂ Fock) (h' : LocFin fun p => ⁅S,T p⁆) :
    ⁅S,opSum T⁆ = opSum (fun p => ⁅S,T p⁆) := by
  refine LinearMap.ext fun P => ?_
  have hs : (Function.support fun p : ℤ => S (T p P)).Finite := by
    refine Set.Finite.subset (hT P) ?_
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    intro hz; exact hp (by rw [hz,map_zero])
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [opSum_apply hT P, opSum_apply hT (S P), opSum_apply h' P,
    map_finsum S (hT P), ← finsum_sub_distrib hs (hT (S P))]
  exact finsum_congr fun p => rfl

/-- Ghost normal products commute with either Cartan boson at every level. -/
theorem BG_boson (i j : Fin 3) (k : ℂ) (a : Fin 2) (m n : ℤ) :
    ⁅BG i j m,boson k a n⁆ = 0 := by
  have hb (p : ℤ) : ⁅beta i p,boson k a n⁆ = 0 := by
    rw [← lie_skew,boson_beta,neg_zero]
  have hg (p : ℤ) : ⁅gamma j p,boson k a n⁆ = 0 := by
    rw [← lie_skew,boson_gamma,neg_zero]
  have hf : (fun p => ⁅bgFam i j m p,boson k a n⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p
    unfold bgFam
    split_ifs <;> simp [lie_mul_left,hb,hg]
  rw [BG,opSum_lie (bgFam_locFin i j m) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- At distinct colours, normal ordering does not change an individual
beta-gamma summand, even when the total mode index is zero. -/
theorem bgFam_offdiagonal (i j : Fin 3) (hij : i ≠ j) (n p : ℤ) :
    bgFam i j n p = beta i p * gamma j (n-p) := by
  have h := beta_gamma i j p (n-p)
  have hc : beta i p * gamma j (n-p) = gamma j (n-p) * beta i p := by
    simpa [Ring.lie_def,hij,sub_eq_zero] using h
  unfold bgFam
  split_ifs
  · rfl
  · exact hc.symm

/-- A diagonal ghost current acts with weight minus one on an off-diagonal
product whose beta has the same colour. The index shift is justified by
local finiteness, without a formal rearrangement of divergent sums. -/
theorem BG_diagonal_left (i j : Fin 3) (hij : i ≠ j) (m n : ℤ) :
    ⁅BG i i m,BG i j n⁆ = -BG i j (m+n) := by
  have hf : (fun p => ⁅BG i i m,bgFam i j n p⁆) =
      fun p => (-1 : ℂ) • bgFam i j (m+n) (m+p) := by
    funext p
    rw [bgFam_offdiagonal i j hij,lie_mul_right,BG_lie_beta,BG_lie_gamma]
    simp only [if_pos rfl,if_neg hij,mul_zero,add_zero]
    rw [bgFam_offdiagonal i j hij,show m+n-(m+p)=n-p by ring]
    simp only [ite_true]
    refine LinearMap.ext fun P => ?_
    simp [Module.End.mul_apply]
  change ⁅BG i i m,opSum (bgFam i j n)⁆ = _
  rw [lie_opSum (bgFam_locFin i j n) _ (by rw [hf]; exact ((bgFam_locFin i j (m+n)).shift m).smul (-1)),
    hf,opSum_smul (-1) ((bgFam_locFin i j (m+n)).shift m),
    opSum_shift m (bgFam_locFin i j (m+n))]
  change (-1 : ℂ) • BG i j (m+n) = -BG i j (m+n)
  module

/-- The matching gamma colour contributes weight plus one. -/
theorem BG_diagonal_right (i j : Fin 3) (hij : i ≠ j) (m n : ℤ) :
    ⁅BG j j m,BG i j n⁆ = BG i j (m+n) := by
  have hf : (fun p => ⁅BG j j m,bgFam i j n p⁆) = fun p => bgFam i j (m+n) p := by
    funext p
    rw [bgFam_offdiagonal i j hij,lie_mul_right,BG_lie_beta,BG_lie_gamma]
    simp only [if_neg hij,if_pos rfl,zero_mul,zero_add]
    rw [bgFam_offdiagonal i j hij,show m+n-p=m+(n-p) by ring]
    simp
  change ⁅BG j j m,opSum (bgFam i j n)⁆ = _
  rw [lie_opSum (bgFam_locFin i j n) _ (by rw [hf]; exact bgFam_locFin i j (m+n)),hf]
  rfl

/-- A third diagonal ghost colour acts trivially on the off-diagonal product. -/
theorem BG_diagonal_other (a i j : Fin 3) (hai : i ≠ a) (haj : a ≠ j) (m n : ℤ) :
    ⁅BG a a m,BG i j n⁆ = 0 := by
  have hf : (fun p => ⁅BG a a m,bgFam i j n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p
    unfold bgFam
    split_ifs <;> simp [lie_mul_right,BG_lie_beta,BG_lie_gamma,hai,haj]
  change ⁅BG a a m,opSum (bgFam i j n)⁆ = _
  rw [lie_opSum (bgFam_locFin i j n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- First simple Cartan current in the trace-normalized Wakimoto convention. -/
def H1 (k : ℂ) (n : ℤ) : Module.End ℂ Fock :=
  (-2 : ℂ) • BG 0 0 n + BG 1 1 n - BG 2 2 n + boson k 0 n

/-- Second simple Cartan current; the mixed Cartan pairing is carried by
the actual two-boson representation. -/
def H2 (k : ℂ) (n : ℤ) : Module.End ℂ Fock :=
  BG 0 0 n - (2 : ℂ) • BG 1 1 n - BG 2 2 n + boson k 1 n

/-- The first Cartan acts on beta colours with weights (2,-1,1). -/
theorem H1_beta (k : ℂ) (i : Fin 3) (m n : ℤ) :
    ⁅H1 k m,beta i n⁆ = (![2,-1,1] i : ℂ) • beta i (m+n) := by
  fin_cases i <;> simp [H1,add_lie,sub_lie,comm_smul_left,BG_lie_beta,boson_beta] <;> module

/-- The second Cartan acts on beta colours with weights (-1,2,1). -/
theorem H2_beta (k : ℂ) (i : Fin 3) (m n : ℤ) :
    ⁅H2 k m,beta i n⁆ = (![-1,2,1] i : ℂ) • beta i (m+n) := by
  fin_cases i <;> simp [H2,add_lie,sub_lie,comm_smul_left,BG_lie_beta,boson_beta] <;> module

/-- Gamma has the opposite first Cartan weights. -/
theorem H1_gamma (k : ℂ) (i : Fin 3) (m n : ℤ) :
    ⁅H1 k m,gamma i n⁆ = (![-2,1,-1] i : ℂ) • gamma i (m+n) := by
  fin_cases i <;> simp [H1,add_lie,sub_lie,comm_smul_left,BG_lie_gamma,boson_gamma] <;> module

/-- Gamma has the opposite second Cartan weights. -/
theorem H2_gamma (k : ℂ) (i : Fin 3) (m n : ℤ) :
    ⁅H2 k m,gamma i n⁆ = (![1,-2,-1] i : ℂ) • gamma i (m+n) := by
  fin_cases i <;> simp [H2,add_lie,sub_lie,comm_smul_left,BG_lie_gamma,boson_gamma] <;> module

/-- The composite beta3-gamma2 term has first Cartan weight two. -/
theorem H1_BG21 (k : ℂ) (m n : ℤ) : ⁅H1 k m,BG 2 1 n⁆ = (2 : ℂ) • BG 2 1 (m+n) := by
  have hb : ⁅boson k 0 m,BG 2 1 n⁆ = 0 := by rw [← lie_skew,BG_boson,neg_zero]
  simp [H1,add_lie,sub_lie,comm_smul_left,BG_diagonal_other 0 2 1 (by decide) (by decide),
    BG_diagonal_left 2 1 (by decide),BG_diagonal_right 2 1 (by decide),hb]
  module

/-- The same composite has second Cartan weight minus one. -/
theorem H2_BG21 (k : ℂ) (m n : ℤ) : ⁅H2 k m,BG 2 1 n⁆ = -BG 2 1 (m+n) := by
  have hb : ⁅boson k 1 m,BG 2 1 n⁆ = 0 := by rw [← lie_skew,BG_boson,neg_zero]
  simp [H2,add_lie,sub_lie,comm_smul_left,BG_diagonal_other 0 2 1 (by decide) (by decide),
    BG_diagonal_left 2 1 (by decide),BG_diagonal_right 2 1 (by decide),hb]
  module

/-- The first simple raising current has the A2 weight (2,-1). -/
theorem H1_E1 (k : ℂ) (m n : ℤ) : ⁅H1 k m,E1 n⁆ = (2 : ℂ) • E1 (m+n) := by
  simp [E1,lie_sub,H1_beta,H1_BG21,smul_sub]

/-- The second coordinate of the first simple root is minus one. -/
theorem H2_E1 (k : ℂ) (m n : ℤ) : ⁅H2 k m,E1 n⁆ = -E1 (m+n) := by
  simp [E1,lie_sub,H2_beta]; rw [H2_BG21]; module

/-- The second simple raising current has first coordinate minus one. -/
theorem H1_E2 (k : ℂ) (m n : ℤ) : ⁅H1 k m,E2 n⁆ = -E2 (m+n) := by
  change ⁅H1 k m,beta 1 n⁆ = -beta 1 (m+n)
  rw [H1_beta]
  norm_num <;> module

/-- Its second coordinate is two. -/
theorem H2_E2 (k : ℂ) (m n : ℤ) : ⁅H2 k m,E2 n⁆ = (2 : ℂ) • E2 (m+n) := by
  simpa [E2] using H2_beta k 1 m n

/-- The highest root has first coordinate one. -/
theorem H1_E12 (k : ℂ) (m n : ℤ) : ⁅H1 k m,E12 n⁆ = E12 (m+n) := by
  simpa [E12] using H1_beta k 2 m n

/-- The highest root has second coordinate one. -/
theorem H2_E12 (k : ℂ) (m n : ℤ) : ⁅H2 k m,E12 n⁆ = E12 (m+n) := by
  simpa [E12] using H2_beta k 2 m n

/-- Nonnegative first Cartan modes annihilate the actual polynomial vacuum. -/
theorem H1_vacuum (k : ℂ) {n : ℤ} (hn : 0 ≤ n) : H1 k n 1 = 0 := by
  simp [H1,BG_vacuum _ _ hn,boson_vacuum _ _ _ hn]

/-- Nonnegative second Cartan modes annihilate the actual polynomial vacuum. -/
theorem H2_vacuum (k : ℂ) {n : ℤ} (hn : 0 ≤ n) : H2 k n 1 = 0 := by
  simp [H2,BG_vacuum _ _ hn,boson_vacuum _ _ _ hn]

/-- The first Cartan has twice-cutoff truncation. -/
theorem H1_above (k : ℂ) {P : Fock} {n : ℤ} (hn : 2*cutoff P ≤ n) : H1 k n P = 0 := by
  have h2 := two_le_cutoff P
  simp [H1,BG_above _ _ hn,boson_above k _ (P := P) (m := n) (by omega)]

/-- The second Cartan has the same truncation bound. -/
theorem H2_above (k : ℂ) {P : Fock} {n : ℤ} (hn : 2*cutoff P ≤ n) : H2 k n P = 0 := by
  have h2 := two_le_cutoff P
  simp [H2,BG_above _ _ hn,boson_above k _ (P := P) (m := n) (by omega)]

/-- Only the first boson contributes to the first Cartan-boson commutator. -/
theorem H1_boson (k : ℂ) (a : Fin 2) (m n : ℤ) :
    ⁅H1 k m,boson k a n⁆ =
      if m+n=0 then ((k+3)*(m : ℂ)*cartan 0 a) • (1 : Module.End ℂ Fock) else 0 := by
  simp [H1,add_lie,sub_lie,comm_smul_left,BG_boson,boson_boson]

/-- Only the second boson contributes to the second Cartan-boson commutator. -/
theorem H2_boson (k : ℂ) (a : Fin 2) (m n : ℤ) :
    ⁅H2 k m,boson k a n⁆ =
      if m+n=0 then ((k+3)*(m : ℂ)*cartan 1 a) • (1 : Module.End ℂ Fock) else 0 := by
  simp [H2,add_lie,sub_lie,comm_smul_left,BG_boson,boson_boson]

end
end VOA.AffineSl3.FreeField
