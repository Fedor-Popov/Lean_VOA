/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3FirstLowering

/-!
# Diagonal ghost action on composite fields

Colour deltas retain multiplicities in the gamma pair. A second finite
normal-ordering boundary gives the linear gamma correction in the cubic
product, needed for the Cartan-lowering relations.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- Complex-valued colour Kronecker delta. -/
def colourDelta (i j : Fin 3) : ℂ := if i=j then 1 else 0

/-- Scalar form of the diagonal ghost action on beta. -/
theorem D_beta (i a : Fin 3) (m n : ℤ) :
    ⁅BG i i m,beta a n⁆ = -(colourDelta i a) • beta a (m+n) := by
  by_cases h : i=a
  · subst a; simp [colourDelta,BG_lie_beta] <;> module
  · simp [colourDelta,h,Ne.symm h,BG_lie_beta]

/-- Scalar form of the diagonal ghost action on gamma. -/
theorem D_gamma (i a : Fin 3) (m n : ℤ) :
    ⁅BG i i m,gamma a n⁆ = colourDelta i a • gamma a (m+n) := by
  by_cases h : i=a
  · subst a; simp [colourDelta,BG_lie_gamma]
  · simp [colourDelta,h,BG_lie_gamma]

/-- A diagonal ghost current counts each gamma colour, with both
contributions present when the gamma pair has repeated colour. -/
theorem D_GG (i b c : Fin 3) (m n : ℤ) :
    ⁅BG i i m,GG b c n⁆ = (colourDelta i b+colourDelta i c) • GG b c (m+n) := by
  have hf : (fun p => ⁅BG i i m,ggFam b c n p⁆) =
      fun p => colourDelta i c • ggFam b c (m+n) p +
        colourDelta i b • ggFam b c (m+n) (m+p) := by
    funext p
    simp only [ggFam_eq,lie_mul_right,D_gamma,mul_smul_comm,smul_mul_assoc,
      show m+n-p=m+(n-p) by ring,show m+n-(m+p)=n-p by ring]
    module
  have ht := ggFam_locFin b c (m+n)
  change ⁅BG i i m,opSum (ggFam b c n)⁆ = _
  rw [lie_opSum (ggFam_locFin b c n) _ (by rw [hf]; exact (ht.smul _).add ((ht.shift m).smul _)),
    hf,opSum_add (ht.smul _) ((ht.shift m).smul _),opSum_smul _ ht,
    opSum_smul _ (ht.shift m),opSum_shift m ht]
  change _ = (colourDelta i b+colourDelta i c) • opSum (ggFam b c (m+n))
  module

/-- The beta contraction with a gamma pair, in scalar delta notation. -/
theorem beta_GG (a b c : Fin 3) (m n : ℤ) :
    ⁅beta a m,GG b c n⁆ = colourDelta a b • gamma c (m+n)+colourDelta a c • gamma b (m+n) := by
  rw [← lie_skew,GG_beta]
  by_cases hb : a=b <;> by_cases hc : a=c <;>
    simp_all [colourDelta,add_comm] <;> module

/-- The two possible contractions of a beta with the gamma pair. -/
def pairContraction (a b c : Fin 3) (n : ℤ) : Module.End ℂ Fock :=
  colourDelta a b • gamma c n+colourDelta a c • gamma b n

/-- The actual cubic summand identity retains the normal-ordering
boundary; dropping this gamma correction would give incorrect currents. -/
theorem D_bgg_summand (i a b c : Fin 3) (m n p : ℤ) :
    ⁅BG i i m,bggFam a b c n p⁆ =
      (colourDelta i b+colourDelta i c) • bggFam a b c (m+n) p -
      colourDelta i a • bggFam a b c (m+n) (m+p) +
      cutoffJump m p • (colourDelta i a • pairContraction a b c (m+n)) := by
  have hb := beta_GG a b c (m+p) (n-p)
  rw [Ring.lie_def] at hb
  have he : m+p+(n-p)=m+n := by ring
  rw [he] at hb
  change beta a (m+p)*GG b c (n-p)-GG b c (n-p)*beta a (m+p) = pairContraction a b c (m+n) at hb
  by_cases hp : p ≤ -1 <;> by_cases hq : m+p ≤ -1
  all_goals
    simp only [bggFam,hp,hq,ite_true,ite_false,lie_mul_right,D_beta,D_GG,
      show m+n-(m+p)=n-p by ring,show m+(n-p)=m+n-p by ring,
      cutoffJump]
    try simp only [hp,hq,ite_true,ite_false]
    refine LinearMap.ext fun P => ?_
    have hh := congrArg (fun S : Module.End ℂ Fock => S P) hb
    simp only [LinearMap.sub_apply,Module.End.mul_apply] at hh
    simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,
      LinearMap.smul_apply,map_smul]
    try rw [sub_eq_iff_eq_add.mp hh]
    module

/-- The boundary family for the cubic commutator is locally finite. -/
theorem cubicBoundary_locFin (i a b c : Fin 3) (m n : ℤ) :
    LocFin (fun p => cutoffJump m p • (colourDelta i a • pairContraction a b c (m+n))) := by
  refine locFin_of_bounds fun P => ⟨min (-m) 0,max (-m) 0-1,fun p hp => ?_⟩
  simp [cutoffJump_bounds m p (by omega)]

/-- Summing the cubic boundary multiplies the contraction by minus m. -/
theorem cubicBoundary_sum (i a b c : Fin 3) (m n : ℤ) :
    opSum (fun p => cutoffJump m p • (colourDelta i a • pairContraction a b c (m+n))) =
      (-(m : ℂ)) • (colourDelta i a • pairContraction a b c (m+n)) := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (cubicBoundary_locFin i a b c m n)]
  simp only [LinearMap.smul_apply]
  rw [← finsum_smul' (cutoffJump_finite m),cutoffJump_sum]

/-- Full diagonal ghost action on the cubic normal product, including
its finite gamma-valued anomaly. -/
theorem D_BGG (i a b c : Fin 3) (m n : ℤ) :
    ⁅BG i i m,BGG a b c n⁆ =
      (colourDelta i b+colourDelta i c-colourDelta i a) • BGG a b c (m+n) -
      (m : ℂ) • (colourDelta i a • pairContraction a b c (m+n)) := by
  have hf : (fun p => ⁅BG i i m,bggFam a b c n p⁆) =
      fun p => (colourDelta i b+colourDelta i c) • bggFam a b c (m+n) p -
        colourDelta i a • bggFam a b c (m+n) (m+p) +
        cutoffJump m p • (colourDelta i a • pairContraction a b c (m+n)) := by
    funext p; exact D_bgg_summand i a b c m n p
  have ht := bggFam_locFin a b c (m+n)
  have hb := cubicBoundary_locFin i a b c m n
  change ⁅BG i i m,opSum (bggFam a b c n)⁆ = _
  rw [lie_opSum (bggFam_locFin a b c n) _ (by rw [hf]; exact ((ht.smul _).sub ((ht.shift m).smul _)).add hb),
    hf,opSum_add ((ht.smul _).sub ((ht.shift m).smul _)) hb,
    opSum_sub (ht.smul _) ((ht.shift m).smul _),opSum_smul _ ht,
    opSum_smul _ (ht.shift m),opSum_shift m ht,cubicBoundary_sum]
  change _ = (colourDelta i b+colourDelta i c-colourDelta i a) • opSum (bggFam a b c (m+n)) - _
  module

/-- Diagonal ghost action on a general beta-gamma product, including the
scalar anomaly when all three colours match. -/
theorem D_BG (i a b : Fin 3) (m n : ℤ) :
    ⁅BG i i m,BG a b n⁆ = (colourDelta i b-colourDelta i a) • BG a b (m+n)+
      (if m+n=0 then (-(m : ℂ)*colourDelta i a*colourDelta i b) • (1 : Module.End ℂ Fock) else 0) := by
  by_cases hab : a=b
  · subst b
    by_cases h : i=a <;> by_cases hz : m+n=0 <;> simp_all [colourDelta,BG_diagonal_bracket]
  · by_cases hi : i=a
    · subst i
      rw [BG_diagonal_left a b hab]
      simp [colourDelta,hab] <;> module
    · by_cases hj : i=b
      · subst i
        rw [BG_diagonal_right a b hab]
        simp [colourDelta,Ne.symm hab]
      · rw [BG_diagonal_other i a b (Ne.symm hi) hj]
        simp [colourDelta,hi,hj]

/-- Only the gamma factor contributes to the diagonal ghost action on AG. -/
theorem D_AG (i : Fin 3) (k : ℂ) (a : Fin 2) (b : Fin 3) (m n : ℤ) :
    ⁅BG i i m,AG k a b n⁆ = colourDelta i b • AG k a b (m+n) := by
  have hf : (fun p => ⁅BG i i m,agFam k a b n p⁆) =
      fun p => colourDelta i b • agFam k a b (m+n) p := by
    funext p
    unfold agFam
    split_ifs <;> simp [lie_mul_right,BG_boson,D_gamma,mul_smul_comm,smul_mul_assoc,
      show m+(n-p)=m+n-p by ring]
  rw [AG,lie_opSum (agFam_locFin k a b n) _ (by rw [hf]; exact (agFam_locFin k a b (m+n)).smul _),
    hf,opSum_smul _ (agFam_locFin k a b (m+n))]
  rfl

/-- Cartan bosons commute with all gamma-pair products. -/
theorem boson_GG (k : ℂ) (a : Fin 2) (b c : Fin 3) (m n : ℤ) :
    ⁅boson k a m,GG b c n⁆ = 0 := by
  have hf : (fun p => ⁅boson k a m,ggFam b c n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p; simp [ggFam_eq,lie_mul_right,boson_gamma]
  rw [GG,lie_opSum (ggFam_locFin b c n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- Cartan bosons commute with cubic ghost products as well. -/
theorem boson_BGG (k : ℂ) (a : Fin 2) (b c d : Fin 3) (m n : ℤ) :
    ⁅boson k a m,BGG b c d n⁆ = 0 := by
  have hf : (fun p => ⁅boson k a m,bggFam b c d n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p; unfold bggFam; split_ifs <;> simp [lie_mul_right,boson_beta,boson_GG]
  rw [BGG,lie_opSum (bggFam_locFin b c d n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- A boson contracts the boson in AG, leaving the gamma field with the
exact Cartan-matrix coefficient and the shifted level k+3. -/
theorem boson_AG (k : ℂ) (a b : Fin 2) (c : Fin 3) (m n : ℤ) :
    ⁅boson k a m,AG k b c n⁆ = ((k+3)*(m : ℂ)*cartan a b) • gamma c (m+n) := by
  let S : Module.End ℂ Fock := ((k+3)*(m : ℂ)*cartan a b) • gamma c (m+n)
  have hf : (fun p => ⁅boson k a m,agFam k b c n p⁆) =
      fun p => if p= -m then S else 0 := by
    funext p
    have h1 : m+p=0 ↔ p= -m := by omega
    by_cases hp : p ≤ -1 <;> by_cases hq : p= -m
    all_goals
      simp only [agFam,hp,ite_true,ite_false,lie_mul_right,boson_gamma,boson_boson,
        mul_zero,zero_mul,add_zero,zero_add]
      simp_all [S,h1,show n-(-m)=m+n by ring,smul_mul_assoc,mul_smul_comm]
  rw [AG,lie_opSum (agFam_locFin k b c n) _ (by rw [hf]; exact locFin_ite _ _),hf,opSum_ite]

/-- The actual H1 action on F1 has the negative simple-root weight -2.
The cubic ghost anomaly and boson-gamma contraction cancel the extra
mode-dependent derivative terms. -/
theorem H1_F1 (k : ℂ) (m n : ℤ) : ⁅H1 k m,F1 k n⁆ = (-2 : ℂ) • F1 k (m+n) := by
  simp [H1,F1,add_lie,sub_lie,lie_add,lie_sub,lie_neg,neg_lie,
    comm_smul_left,comm_smul_right,D_BGG,D_BG,D_AG,D_gamma,
    boson_BGG,boson_BG,boson_gamma,boson_AG,colourDelta,pairContraction,cartan,Int.cast_add] <;> module

/-- The actual H2 action on F1 has the negative simple-root weight 1.
The cubic ghost anomaly and boson-gamma contraction cancel the extra
mode-dependent derivative terms. -/
theorem H2_F1 (k : ℂ) (m n : ℤ) : ⁅H2 k m,F1 k n⁆ = (1 : ℂ) • F1 k (m+n) := by
  simp [H2,F1,add_lie,sub_lie,lie_add,lie_sub,lie_neg,neg_lie,
    comm_smul_left,comm_smul_right,D_BGG,D_BG,D_AG,D_gamma,
    boson_BGG,boson_BG,boson_gamma,boson_AG,colourDelta,pairContraction,cartan,Int.cast_add] <;> module

/-- The actual H1 action on F2 has the negative simple-root weight 1.
The cubic ghost anomaly and boson-gamma contraction cancel the extra
mode-dependent derivative terms. -/
theorem H1_F2 (k : ℂ) (m n : ℤ) : ⁅H1 k m,F2 k n⁆ = (1 : ℂ) • F2 k (m+n) := by
  simp [H1,F2,add_lie,sub_lie,lie_add,lie_sub,lie_neg,neg_lie,
    comm_smul_left,comm_smul_right,D_BGG,D_BG,D_AG,D_gamma,
    boson_BGG,boson_BG,boson_gamma,boson_AG,colourDelta,pairContraction,cartan,Int.cast_add] <;> module

/-- The actual H2 action on F2 has the negative simple-root weight -2.
The cubic ghost anomaly and boson-gamma contraction cancel the extra
mode-dependent derivative terms. -/
theorem H2_F2 (k : ℂ) (m n : ℤ) : ⁅H2 k m,F2 k n⁆ = (-2 : ℂ) • F2 k (m+n) := by
  simp [H2,F2,add_lie,sub_lie,lie_add,lie_sub,lie_neg,neg_lie,
    comm_smul_left,comm_smul_right,D_BGG,D_BG,D_AG,D_gamma,
    boson_BGG,boson_BG,boson_gamma,boson_AG,colourDelta,pairContraction,cartan,Int.cast_add] <;> module

end
end VOA.AffineSl3.FreeField
