/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3LoweringProducts

/-!
# The first simple raising-lowering bracket

The opposite ghost-current anomaly is essential: its contribution lowers
the k+1 derivative correction to the affine level k.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- A ghost current commutes with a gamma pair when neither gamma colour
can contract against its beta. -/
theorem BG_GG_disjoint (i j a b : Fin 3) (hia : i ≠ a) (hib : i ≠ b) (m n : ℤ) :
    ⁅BG i j m,GG a b n⁆ = 0 := by
  have hf : (fun p => ⁅BG i j m,ggFam a b n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p
    simp [ggFam_eq,lie_mul_right,BG_lie_gamma,hia,hib]
  rw [GG,lie_opSum (ggFam_locFin a b n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- A cubic ghost product commutes with a ghost current when all three
possible elementary contractions vanish by their colours. -/
theorem BG_BGG_disjoint (i j a b c : Fin 3) (haj : a ≠ j) (hib : i ≠ b) (hic : i ≠ c)
    (m n : ℤ) : ⁅BG i j m,BGG a b c n⁆ = 0 := by
  have hf : (fun p => ⁅BG i j m,bggFam a b c n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p
    unfold bggFam
    split_ifs <;> simp [lie_mul_right,BG_lie_beta,haj,BG_GG_disjoint i j b c hib hic]
  rw [BGG,lie_opSum (bggFam_locFin a b c n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- A boson-gamma product has no ghost-current contraction when the gamma
colour differs from the ghost beta colour. -/
theorem BG_AG_disjoint (i j : Fin 3) (k : ℂ) (a : Fin 2) (b : Fin 3) (hib : i ≠ b)
    (m n : ℤ) : ⁅BG i j m,AG k a b n⁆ = 0 := by
  have hf : (fun p => ⁅BG i j m,agFam k a b n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p
    unfold agFam
    split_ifs <;> simp [lie_mul_right,BG_lie_gamma,hib,BG_boson]
  rw [AG,lie_opSum (agFam_locFin k a b n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- The off-diagonal piece of E1 detects exactly the opposite ghost pair
inside F1, including its central anomaly. -/
theorem BG21_F1 (k : ℂ) (m n : ℤ) : ⁅BG 2 1 m,F1 k n⁆ =
    -(BG 1 1 (m+n)-BG 2 2 (m+n)+
      (if m+n=0 then (-(m : ℂ)) • (1 : Module.End ℂ Fock) else 0)) := by
  simp [F1,lie_add,lie_sub,lie_neg,comm_smul_right,
    BG_BGG_disjoint 2 1 0 0 0 (by decide) (by decide) (by decide),
    BG_AG_disjoint 2 1 k 0 0 (by decide),BG_lie_gamma,BG_opposite]

/-- The first simple raising-lowering bracket has the actual level-k
central term. The k+1 derivative and the ghost anomaly are both retained. -/
theorem E1_F1 (k : ℂ) (m n : ℤ) : ⁅E1 m,F1 k n⁆ =
    H1 k (m+n)+(if m+n=0 then (k*(m : ℂ)) • (1 : Module.End ℂ Fock) else 0) := by
  rw [E1,sub_lie,BG21_F1,← lie_skew (beta 0 m) (F1 k n)]
  by_cases hz : m+n=0
  · have hc : (n : ℂ) = -(m : ℂ) := by exact_mod_cast (show n= -m by omega)
    simp [F1,H1,add_lie,sub_lie,neg_lie,comm_smul_left,BGG_beta,BG_lie_beta,AG_beta,gamma_beta,
      hz,show n+m=0 by omega,add_comm,hc] <;> module
  · simp [F1,H1,add_lie,sub_lie,neg_lie,comm_smul_left,BGG_beta,BG_lie_beta,AG_beta,gamma_beta,
      hz,show n+m≠0 by omega,add_comm] <;> module

/-- The gamma pair with colours 1 and 2 transforms into a double colour-1
pair under the off-diagonal ghost current appearing in E1 (zero-based indices). -/
theorem BG21_GG12 (m n : ℤ) : ⁅BG 2 1 m,GG 1 2 n⁆ = GG 1 1 (m+n) := by
  have hf : (fun p => ⁅BG 2 1 m,ggFam 1 2 n p⁆) = fun p => ggFam 1 1 (m+n) p := by
    funext p
    simp [ggFam_eq,lie_mul_right,BG_lie_gamma,show m+n-p=m+(n-p) by ring]
  rw [GG,lie_opSum (ggFam_locFin 1 2 n) _ (by rw [hf]; exact ggFam_locFin 1 1 (m+n)),hf]
  rfl

/-- No beta-gamma contraction is present in the colour-(2,1,1) cubic summand,
so its ordering split can be removed. -/
theorem bggFam211_eq (n p : ℤ) : bggFam 2 1 1 n p = beta 2 p * GG 1 1 (n-p) := by
  have hc : GG 1 1 (n-p)*beta 2 p = beta 2 p*GG 1 1 (n-p) := by
    have h := GG_beta 1 1 2 (n-p) p
    simpa [Ring.lie_def,sub_eq_zero] using h
  unfold bggFam
  split_ifs
  · rfl
  · exact hc

/-- The beta contraction in the double colour-1 cubic term shifts its
summation index; no hidden boundary anomaly occurs because the target
beta colour commutes with both gamma factors. -/
theorem BG21_BGG111 (m n : ℤ) : ⁅BG 2 1 m,BGG 1 1 1 n⁆ = -BGG 2 1 1 (m+n) := by
  have hf : (fun p => ⁅BG 2 1 m,bggFam 1 1 1 n p⁆) =
      fun p => (-1 : ℂ) • bggFam 2 1 1 (m+n) (m+p) := by
    funext p
    have hc : GG 1 1 (n-p)*beta 2 (m+p) = beta 2 (m+p)*GG 1 1 (n-p) := by
      have h := GG_beta 1 1 2 (n-p) (m+p)
      simpa [Ring.lie_def,sub_eq_zero] using h
    rw [bggFam211_eq]
    by_cases hp : p ≤ -1
    all_goals
      simp only [bggFam,hp,ite_true,ite_false,lie_mul_right,BG_lie_beta,
        BG_GG_disjoint 2 1 1 1 (by decide) (by decide),mul_zero,zero_mul,add_zero,zero_add]
      simp only [show m+n-(m+p)=n-p by ring]
      refine LinearMap.ext fun P => ?_
      have hh := congrArg (fun S : Module.End ℂ Fock => S P) hc
      simp only [Module.End.mul_apply] at hh
      simp [Module.End.mul_apply,show m+n-(m+p)=n-p by ring]
      try rw [hh]
      all_goals module
  change ⁅BG 2 1 m,opSum (bggFam 1 1 1 n)⁆ = _
  rw [lie_opSum (bggFam_locFin 1 1 1 n) _ (by rw [hf]; exact ((bggFam_locFin 2 1 1 (m+n)).shift m).smul (-1)),
    hf,opSum_smul (-1) ((bggFam_locFin 2 1 1 (m+n)).shift m),opSum_shift m (bggFam_locFin 2 1 1 (m+n))]
  change (-1 : ℂ) • BGG 2 1 1 (m+n) = -BGG 2 1 1 (m+n)
  module

/-- The gamma contraction in the mixed cubic term gives the same target
as the beta contraction, allowing the two contributions to cancel in F2. -/
theorem BG21_BGG212 (m n : ℤ) : ⁅BG 2 1 m,BGG 2 1 2 n⁆ = BGG 2 1 1 (m+n) := by
  have hf : (fun p => ⁅BG 2 1 m,bggFam 2 1 2 n p⁆) = fun p => bggFam 2 1 1 (m+n) p := by
    funext p
    unfold bggFam
    split_ifs <;> simp [lie_mul_right,BG_lie_beta,BG21_GG12,show m+n-p=m+(n-p) by ring]
  change ⁅BG 2 1 m,opSum (bggFam 2 1 2 n)⁆ = _
  rw [lie_opSum (bggFam_locFin 2 1 2 n) _ (by rw [hf]; exact bggFam_locFin 2 1 1 (m+n)),hf]
  rfl

/-- The linear gamma contraction in F2. -/
theorem BG21_BG02 (m n : ℤ) : ⁅BG 2 1 m,BG 0 2 n⁆ = BG 0 1 (m+n) := by
  have hf : (fun p => ⁅BG 2 1 m,bgFam 0 2 n p⁆) = fun p => bgFam 0 1 (m+n) p := by
    funext p
    unfold bgFam
    split_ifs <;> simp [lie_mul_right,BG_lie_beta,BG_lie_gamma,show m+n-p=m+(n-p) by ring]
  change ⁅BG 2 1 m,opSum (bgFam 0 2 n)⁆ = _
  rw [lie_opSum (bgFam_locFin 0 2 n) _ (by rw [hf]; exact bgFam_locFin 0 1 (m+n)),hf]
  rfl

/-- All higher terms cancel in the off-diagonal ghost action on F2. -/
theorem BG21_F2 (k : ℂ) (m n : ℤ) : ⁅BG 2 1 m,F2 k n⁆ = BG 0 1 (m+n) := by
  simp [F2,lie_add,lie_sub,comm_smul_right,BG_lie_gamma,
    BG_BGG_disjoint 2 1 0 0 1 (by decide) (by decide) (by decide),
    BG_AG_disjoint 2 1 k 1 1 (by decide),BG21_BGG111,BG21_BGG212,BG21_BG02]

/-- The first simple raising current commutes with the second lowering current. -/
theorem E1_F2 (k : ℂ) (m n : ℤ) : ⁅E1 m,F2 k n⁆ = 0 := by
  rw [E1,sub_lie,BG21_F2,← lie_skew (beta 0 m) (F2 k n)]
  simp [F2,add_lie,sub_lie,comm_smul_left,BGG_beta,BG_lie_beta,AG_beta,gamma_beta,add_comm] <;> module

end
end VOA.AffineSl3.FreeField
