/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3CartanCurrents

/-!
# Finite boundary anomaly of diagonal ghost currents

The normal-ordering boundary changes under an integer shift. Its signed
finite interval has total weight minus the shift, giving the central
commutator of the actual diagonal beta-gamma currents.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- The difference of the two creation cutoffs; only this difference is
summable, not either of the separate half-line indicators. -/
def cutoffJump (m p : ℤ) : ℂ :=
  (if m+p ≤ -1 then 1 else 0) - (if p ≤ -1 then 1 else 0)

/-- Normal ordering changes only in the finite interval between zero and -m. -/
theorem cutoffJump_bounds (m p : ℤ)
    (h : p < min (-m) 0 ∨ max (-m) 0 ≤ p) : cutoffJump m p = 0 := by
  rcases h with h | h
  · simp [cutoffJump,show m+p ≤ -1 by omega,show p ≤ -1 by omega]
  · simp [cutoffJump,show ¬m+p ≤ -1 by omega,show ¬p ≤ -1 by omega]

/-- For a nonnegative shift the boundary is the negatively signed interval. -/
theorem cutoffJump_nonneg (m p : ℤ) (hm : 0 ≤ m) :
    cutoffJump m p = if -m ≤ p ∧ p ≤ -1 then -1 else 0 := by
  unfold cutoffJump
  split_ifs <;> norm_num at * <;> omega

/-- For a nonpositive shift it is the positively signed interval. -/
theorem cutoffJump_nonpos (m p : ℤ) (hm : m ≤ 0) :
    cutoffJump m p = if 0 ≤ p ∧ p ≤ -m-1 then 1 else 0 := by
  unfold cutoffJump
  split_ifs <;> norm_num at * <;> omega

/-- The scalar central summand produced by the normal-ordering boundary. -/
def boundary (m n p : ℤ) : Module.End ℂ Fock :=
  if m+n=0 then cutoffJump m p • (1 : Module.End ℂ Fock) else 0

/-- The boundary summands have genuine finite support on every polynomial. -/
theorem boundary_locFin (m n : ℤ) : LocFin (boundary m n) := by
  refine locFin_of_bounds fun P => ⟨min (-m) 0,max (-m) 0-1,fun p hp => ?_⟩
  simp [boundary,cutoffJump_bounds m p (by omega)]

/-- The exact commutator with one normal-ordered summand is a shifted
finite difference plus the boundary correction. -/
theorem diagonal_summand (i : Fin 3) (m n p : ℤ) :
    ⁅BG i i m,bgFam i i n p⁆ =
      bgFam i i (m+n) p - bgFam i i (m+n) (m+p) + boundary m n p := by
  have hb := beta_gamma i i (m+p) (n-p)
  rw [Ring.lie_def] at hb
  have he : m+p+(n-p)=m+n := by ring
  simp only [he,eq_self_iff_true,true_and] at hb
  have hr : m+n-(m+p)=n-p := by ring
  have hs : m+(n-p)=m+n-p := by ring
  by_cases hp : p ≤ -1 <;> by_cases hq : m+p ≤ -1 <;> by_cases hz : m+n=0
  all_goals
    simp only [bgFam,hp,hq,ite_true,ite_false,lie_mul_right,
      BG_lie_beta,BG_lie_gamma,hr,hs]
    simp only [boundary,cutoffJump,hp,hq,hz,ite_true,ite_false]
    simp only [hz,ite_true,ite_false] at hb
    refine LinearMap.ext fun P => ?_
    have hh := congrArg (fun S : Module.End ℂ Fock => S P) hb
    simp only [LinearMap.sub_apply,Module.End.mul_apply,Module.End.one_apply,
      LinearMap.zero_apply] at hh
    simp only [ite_true,LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,
      LinearMap.neg_apply,LinearMap.smul_apply,Module.End.one_apply,
      LinearMap.zero_apply,map_neg]
    try simp only [sub_self,zero_smul,zero_sub,one_smul,sub_zero]
    try rw [sub_eq_iff_eq_add.mp hh]
    module

/-- The cutoff jump has finite scalar support. -/
theorem cutoffJump_finite (m : ℤ) : (Function.support (cutoffJump m)).Finite := by
  refine Set.Finite.subset (Set.finite_Icc (min (-m) 0) (max (-m) 0-1)) ?_
  intro p hp
  simp only [Function.mem_support] at hp
  by_contra h
  apply hp
  exact cutoffJump_bounds m p (by simp only [Set.mem_Icc] at h; omega)

/-- A scalar interval indicator sums to its finite cardinality. -/
theorem scalar_interval_sum (a b : ℤ) (c : ℂ) :
    (∑ᶠ p : ℤ, if a ≤ p ∧ p ≤ b then c else 0) = (Finset.Icc a b).card • c := by
  have hs : (Function.support fun p : ℤ => if a ≤ p ∧ p ≤ b then c else 0) ⊆
      ↑(Finset.Icc a b) := by
    intro p hp
    simp only [Function.mem_support] at hp
    by_contra hn
    apply hp
    exact if_neg (by simpa using hn)
  rw [finsum_eq_finsetSum_of_support_subset _ hs]
  rw [Finset.sum_congr rfl (fun p hp => if_pos (by simpa using hp)),Finset.sum_const]

/-- Counting the signed boundary interval gives minus the integer shift. -/
theorem cutoffJump_sum (m : ℤ) : (∑ᶠ p, cutoffJump m p) = -(m : ℂ) := by
  by_cases hm : 0 ≤ m
  · rw [finsum_congr (fun p => cutoffJump_nonneg m p hm),scalar_interval_sum]
    have hc : (Finset.Icc (-m) (-1)).card = m.toNat := by rw [Int.card_Icc]; congr 1; omega
    rw [hc,nsmul_eq_mul]
    have he : (m.toNat : ℂ) = (m : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hm
    rw [he]; ring
  · rw [finsum_congr (fun p => cutoffJump_nonpos m p (by omega)),scalar_interval_sum]
    have hc : (Finset.Icc 0 (-m-1)).card = (-m).toNat := by rw [Int.card_Icc]; congr 1; omega
    rw [hc,nsmul_eq_mul,mul_one]
    have he : ((-m).toNat : ℂ) = ((-m : ℤ) : ℂ) := by exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -m)
    simpa using he

/-- The summed scalar boundary gives the diagonal ghost central anomaly. -/
theorem boundary_sum (m n : ℤ) : opSum (boundary m n) =
    if m+n=0 then (-(m : ℂ)) • (1 : Module.End ℂ Fock) else 0 := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (boundary_locFin m n)]
  by_cases hz : m+n=0
  · simp only [boundary,if_pos hz,LinearMap.smul_apply,Module.End.one_apply]
    rw [← finsum_smul' (cutoffJump_finite m) P,cutoffJump_sum]
  · simp [boundary,hz]

/-- Local finiteness is closed under subtraction. -/
theorem LocFin.sub {T U : ℤ → Module.End ℂ Fock} (hT : LocFin T) (hU : LocFin U) :
    LocFin (fun p => T p-U p) := by
  intro P
  refine Set.Finite.subset ((hT P).union (hU P)) ?_
  intro p hp
  simp only [Function.mem_support,LinearMap.sub_apply] at hp
  by_contra hn
  simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
  exact hp (by rw [hn.1,hn.2,sub_self])

/-- Operator summation respects a difference of locally finite families. -/
theorem opSum_sub {T U : ℤ → Module.End ℂ Fock} (hT : LocFin T) (hU : LocFin U) :
    opSum (fun p => T p-U p) = opSum T-opSum U := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (hT.sub hU),LinearMap.sub_apply,opSum_apply hT,opSum_apply hU,
    ← finsum_sub_distrib (hT P) (hU P)]
  exact finsum_congr fun p => rfl

/-- The exact diagonal ghost-current commutator at all integer indices. -/
theorem BG_diagonal_central (i : Fin 3) (m n : ℤ) :
    ⁅BG i i m,BG i i n⁆ =
      if m+n=0 then (-(m : ℂ)) • (1 : Module.End ℂ Fock) else 0 := by
  have hf : (fun p => ⁅BG i i m,bgFam i i n p⁆) =
      fun p => bgFam i i (m+n) p-bgFam i i (m+n) (m+p)+boundary m n p := by
    funext p; exact diagonal_summand i m n p
  have ht := bgFam_locFin i i (m+n)
  change ⁅BG i i m,opSum (bgFam i i n)⁆ = _
  rw [lie_opSum (bgFam_locFin i i n) _ (by rw [hf]; exact (ht.sub (ht.shift m)).add (boundary_locFin m n)),
    hf,opSum_add (ht.sub (ht.shift m)) (boundary_locFin m n),opSum_sub ht (ht.shift m),
    opSum_shift m ht,sub_self,zero_add,boundary_sum]

/-- Diagonal ghost currents from different colours commute. -/
theorem BG_diagonal_distinct (i j : Fin 3) (hij : i ≠ j) (m n : ℤ) :
    ⁅BG i i m,BG j j n⁆ = 0 :=
  BG_diagonal_other i j j (Ne.symm hij) hij m n

/-- Uniform colour-delta version of the diagonal ghost commutator. -/
theorem BG_diagonal_bracket (i j : Fin 3) (m n : ℤ) :
    ⁅BG i i m,BG j j n⁆ =
      if i=j ∧ m+n=0 then (-(m : ℂ)) • (1 : Module.End ℂ Fock) else 0 := by
  by_cases h : i=j
  · subst j; simpa using BG_diagonal_central i m n
  · simp [BG_diagonal_distinct i j h,h]

/-- The reversed boson-ghost commutator also vanishes. -/
theorem boson_BG (k : ℂ) (a : Fin 2) (i j : Fin 3) (m n : ℤ) :
    ⁅boson k a m,BG i j n⁆ = 0 := by rw [← lie_skew,BG_boson,neg_zero]

/-- The first Cartan current has central term 2km: the ghost anomaly
cancels the shift by the dual Coxeter number three. -/
theorem H1_H1 (k : ℂ) (m n : ℤ) : ⁅H1 k m,H1 k n⁆ =
    if m+n=0 then (2*k*(m : ℂ)) • (1 : Module.End ℂ Fock) else 0 := by
  by_cases h : m+n=0 <;>
    simp [H1,add_lie,sub_lie,lie_add,lie_sub,comm_smul_left,comm_smul_right,
      BG_diagonal_bracket,BG_boson,boson_BG,boson_boson,h,cartan] <;> module

/-- The second Cartan current has the same normalized diagonal central term. -/
theorem H2_H2 (k : ℂ) (m n : ℤ) : ⁅H2 k m,H2 k n⁆ =
    if m+n=0 then (2*k*(m : ℂ)) • (1 : Module.End ℂ Fock) else 0 := by
  by_cases h : m+n=0 <;>
    simp [H2,add_lie,sub_lie,lie_add,lie_sub,comm_smul_left,comm_smul_right,
      BG_diagonal_bracket,BG_boson,boson_BG,boson_boson,h,cartan] <;> module

/-- The off-diagonal Cartan central term is -km, matching tr(h1*h2)=-1. -/
theorem H1_H2 (k : ℂ) (m n : ℤ) : ⁅H1 k m,H2 k n⁆ =
    if m+n=0 then (-k*(m : ℂ)) • (1 : Module.End ℂ Fock) else 0 := by
  by_cases h : m+n=0 <;>
    simp [H1,H2,add_lie,sub_lie,lie_add,lie_sub,comm_smul_left,comm_smul_right,
      BG_diagonal_bracket,BG_boson,boson_BG,boson_boson,h,cartan] <;> module

/-- Opposite off-diagonal ghost currents have the same finite boundary
anomaly, with the two distinct diagonal products as the bulk difference. -/
theorem opposite_summand (a b : Fin 3) (m n p : ℤ) :
    ⁅BG a b m,bgFam b a n p⁆ =
      bgFam b b (m+n) p - bgFam a a (m+n) (m+p) + boundary m n p := by
  have hb := beta_gamma a a (m+p) (n-p)
  rw [Ring.lie_def] at hb
  have he : m+p+(n-p)=m+n := by ring
  simp only [he,eq_self_iff_true,true_and] at hb
  have hr : m+n-(m+p)=n-p := by ring
  have hs : m+(n-p)=m+n-p := by ring
  by_cases hp : p ≤ -1 <;> by_cases hq : m+p ≤ -1 <;> by_cases hz : m+n=0
  all_goals
    simp only [bgFam,hp,hq,ite_true,ite_false,lie_mul_right,
      BG_lie_beta,BG_lie_gamma,hr,hs]
    simp only [boundary,cutoffJump,hp,hq,hz,ite_true,ite_false]
    simp only [hz,ite_true,ite_false] at hb
    refine LinearMap.ext fun P => ?_
    have hh := congrArg (fun S : Module.End ℂ Fock => S P) hb
    simp only [LinearMap.sub_apply,Module.End.mul_apply,Module.End.one_apply,
      LinearMap.zero_apply] at hh
    simp only [ite_true,LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,
      LinearMap.neg_apply,LinearMap.smul_apply,Module.End.one_apply,
      LinearMap.zero_apply,map_neg]
    try simp only [sub_self,zero_smul,zero_sub,one_smul,sub_zero]
    try rw [sub_eq_iff_eq_add.mp hh]
    module

/-- The opposite ghost-current bracket, including its exact central term. -/
theorem BG_opposite (a b : Fin 3) (m n : ℤ) :
    ⁅BG a b m,BG b a n⁆ = BG b b (m+n)-BG a a (m+n)+
      (if m+n=0 then (-(m : ℂ)) • (1 : Module.End ℂ Fock) else 0) := by
  have hf : (fun p => ⁅BG a b m,bgFam b a n p⁆) =
      fun p => bgFam b b (m+n) p-bgFam a a (m+n) (m+p)+boundary m n p := by
    funext p; exact opposite_summand a b m n p
  have ht := bgFam_locFin b b (m+n)
  have hu := bgFam_locFin a a (m+n)
  change ⁅BG a b m,opSum (bgFam b a n)⁆ = _
  rw [lie_opSum (bgFam_locFin b a n) _ (by rw [hf]; exact (ht.sub (hu.shift m)).add (boundary_locFin m n)),
    hf,opSum_add (ht.sub (hu.shift m)) (boundary_locFin m n),opSum_sub ht (hu.shift m),
    opSum_shift m hu,boundary_sum]
  rfl

end
end VOA.AffineSl3.FreeField
