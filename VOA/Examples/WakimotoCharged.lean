/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoFree
import VOA.Examples.AffineSl2CentralCurrentRealization

/-!
# Wakimoto currents with arbitrary highest weight

The existing polynomial Fock space permits a nonzero boson zero mode.
Adding lambda to h_0 and lambda gamma_n to f_n gives the actual affine
current algebra at every highest weight, with the same noncritical level.
This constructs a representation, not its singular states or a Kac formula.
-/
namespace VOA.Wak.Charged
open AffineVOA

/-- The Cartan current with boson zero-mode eigenvalue lambda. -/
noncomputable def H (k lam : ℂ) (n : ℤ) : Module.End ℂ WakFock :=
  Hcur k n + if n=0 then lam • (1 : Module.End ℂ WakFock) else 0

/-- The lowering current acquires the corresponding lambda gamma term. -/
noncomputable def F (k lam : ℂ) (n : ℤ) : Module.End ℂ WakFock :=
  Fcur k n + lam • Gam n

/-- Bilinearity of the actual endomorphism commutator in its right factor. -/
private theorem comm_smul (a : ℂ) (S T : Module.End ℂ WakFock) :
    ⁅S,a • T⁆=a • ⁅S,T⁆ := by
  rw [Ring.lie_def, Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Bilinearity of the actual endomorphism commutator in its left factor. -/
private theorem smul_comm (a : ℂ) (S T : Module.End ℂ WakFock) :
    ⁅a • S,T⁆=a • ⁅S,T⁆ := by
  rw [Ring.lie_def, Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Scalar identity operators commute with every endomorphism. -/
theorem scalar_lie (a : ℂ) (T : Module.End ℂ WakFock) :
    ⁅a • (1 : Module.End ℂ WakFock),T⁆=0 := by
  exact central_lie a T

/-- The charge shift in the Cartan mode is central as an operator. -/
theorem H_lie (k lam : ℂ) (n : ℤ) (T : Module.End ℂ WakFock) :
    ⁅H k lam n,T⁆=⁅Hcur k n,T⁆ := by
  simp only [H, add_lie]
  split_ifs
  · rw [scalar_lie, add_zero]
  · rw [zero_lie, add_zero]

/-- The raising-lowering commutator has the shifted Cartan mode and unchanged level. -/
theorem ef (k lam : ℂ) (m n : ℤ) :
    ⁅Ecur m,F k lam n⁆ = H k lam (m+n) +
      if m+n=0 then ((m : ℂ)*k) • (1 : Module.End ℂ WakFock) else 0 := by
  rw [F, lie_add, comm_smul, rel_ef, Ecur_lie_Gam, H]
  split_ifs <;> module

/-- The Cartan-raising relation is unchanged by the scalar zero-mode shift. -/
theorem he (k lam : ℂ) (m n : ℤ) :
    ⁅H k lam m,Ecur n⁆ = (2 : ℂ) • Ecur (m+n) := by
  rw [H_lie, rel_he]

/-- The shifted lowering current still has Cartan charge minus two. -/
theorem hf (k lam : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅H k lam m,F k lam n⁆ = (-2 : ℂ) • F k lam (m+n) := by
  rw [H_lie, F, lie_add, comm_smul, rel_hf k hk, Hcur_lie_Gam, F]
  module

/-- Opposite gamma cross terms cancel, so two charged lowering modes commute. -/
theorem ff (k lam : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅F k lam m,F k lam n⁆=0 := by
  have hg : ⁅Gam m,Fcur k n⁆=GG (m+n) := by
    rw [lie_swap, Fcur_lie_Gam, neg_neg, add_comm]
  simp only [F, add_lie, lie_add, comm_smul, smul_comm, rel_ff k hk,
    Fcur_lie_Gam, hg, Gam_Gam_lie, smul_zero, smul_neg]
  module

/-- The Cartan central term is independent of the highest weight. -/
theorem hh (k lam : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅H k lam m,H k lam n⁆ =
      if m+n=0 then ((2 : ℂ)*k*(m : ℂ)) • (1 : Module.End ℂ WakFock) else 0 := by
  rw [H_lie, lie_swap, H_lie, lie_swap, neg_neg, rel_hh k hk]

/-- Colour-indexed currents in the charged polynomial representation. -/
noncomputable def J (k lam : ℂ) (a : Fin 3) (n : ℤ) : Module.End ℂ WakFock :=
  if a=0 then Ecur n else if a=1 then F k lam n else H k lam n

/-- Colour zero is the unmodified beta current. -/
theorem J_E (k lam : ℂ) (n : ℤ) : J k lam 0 n=Ecur n := by simp [J]

/-- Colour one is the charged lowering current. -/
theorem J_F (k lam : ℂ) (n : ℤ) : J k lam 1 n=F k lam n := by norm_num [J]

/-- Colour two is the charged Cartan current. -/
theorem J_H (k lam : ℂ) (n : ℤ) : J k lam 2 n=H k lam n := by
  rw [J,if_neg (by decide : (2 : Fin 3) ≠ 0),if_neg (by decide : (2 : Fin 3) ≠ 1)]

set_option maxHeartbeats 1000000 in
/-- All affine commutators hold on the actual polynomial carrier at every
highest weight, with no representation or singular-vector premise. -/
theorem J_comm (k lam : ℂ) (hk : k + 2 ≠ 0) (a b : Fin 3) (m n : ℤ) :
    ⁅J k lam a m,J k lam b n⁆ =
      (∑ c, fabc a b c • J k lam c (m+n)) +
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : Module.End ℂ WakFock) else 0 := by
  have eh : ⁅Ecur m,H k lam n⁆=(-2 : ℂ) • Ecur (m+n) := by
    rw [lie_swap, he, add_comm]; module
  have fh : ⁅F k lam m,H k lam n⁆=(2 : ℂ) • F k lam (m+n) := by
    rw [lie_swap, hf k lam hk, add_comm]; module
  have fe : ⁅F k lam m,Ecur n⁆=(-1 : ℂ) • H k lam (m+n) +
      if m+n=0 then ((m : ℂ)*k) • (1 : Module.End ℂ WakFock) else 0 := by
    rw [lie_swap, ef, show n+m=m+n by omega]
    by_cases hz : m+n=0
    · have hn : (n : ℂ)=-(m : ℂ) := by exact_mod_cast (show n= -m by omega)
      simp only [if_pos hz, hn]; module
    · simp only [if_neg hz]; module
  rcases fin3_cases a with rfl | rfl | rfl <;> rcases fin3_cases b with rfl | rfl | rfl <;>
    simp only [J_E,J_F,J_H,Fin.sum_univ_three,fabc,kappa]
  · rw [rel_ee]; simp
  · rw [ef]; split_ifs <;> module
  · rw [eh]; simp
  · rw [fe]; split_ifs <;> module
  · rw [ff k lam hk]; simp
  · rw [fh]; simp
  · rw [he]; simp
  · rw [hf k lam hk]; simp
  · rw [hh k lam hk]; split_ifs <;> module

/-- Charged currents still lower oscillator energy by their mode index. -/
theorem degree_J (k lam : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅Dwt,J k lam a n⁆=(-(n : ℂ)) • J k lam a n := by
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [J_E,Dwt_lie_Ecur]
  · rw [J_F,F,lie_add,comm_smul,Dwt_lie_Fcur,Dwt_lie_Gam]; module
  · rw [J_H,H,lie_add,Dwt_lie_Hcur]
    by_cases hn : n=0
    · subst n; simp [comm_smul,lie_one']
    · simp [hn]

/-- The polynomial one is killed by every positive current mode. -/
theorem J_one_positive (k lam : ℂ) (a : Fin 3) (n : ℤ) (hn : 0<n) :
    J k lam a n (1 : WakFock)=0 := by
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [J_E,Ecur_one (by omega)]
  · simp [J_F,F,Fcur_one k (show 0≤n by omega),Gam_one (show 1≤n by omega)]
  · simp [J_H,H,Hcur_one k (show 0≤n by omega),ne_of_gt hn]

/-- The horizontal raising operator kills the highest polynomial. -/
theorem E_one : Ecur 0 (1 : WakFock)=0 := Ecur_one (by omega)

/-- The horizontal Cartan eigenvalue is exactly the chosen highest weight. -/
theorem H_one (k lam : ℂ) : H k lam 0 (1 : WakFock)=lam • (1 : WakFock) := by
  simp [H,Hcur_one k (show (0 : ℤ)≤0 by omega)]

/-- The first horizontal lowering vector is lambda times the gamma zero-mode
variable; at weight zero this reduces to the original vacuum relation. -/
theorem F_one (k lam : ℂ) : F k lam 0 (1 : WakFock)=lam • cV 0 := by
  simp [F,Fcur_one k (show (0 : ℤ)≤0 by omega),Gam_one_nonpos (show (0 : ℤ)≤0 by omega)]

/-- Extend the three explicit charged currents linearly in their sl2 colour. -/
noncomputable def loop (k lam : ℂ) (n : ℤ) : Sl2 →ₗ[ℂ] Module.End ℂ WakFock where
  toFun x := ∑ a, x a • J k lam a n
  map_add' x y := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r x := by simp [Pi.smul_apply,Finset.smul_sum,smul_smul]

/-- Evaluation of the colour-linear action is its defining finite sum. -/
@[simp] theorem loop_apply (k lam : ℂ) (n : ℤ) (x : Sl2) :
    loop k lam n x = ∑ a, x a • J k lam a n := rfl

set_option maxHeartbeats 2000000 in
/-- The actual charged loop action has the standard affine cocycle. -/
theorem loop_comm (k lam : ℂ) (hk : k + 2 ≠ 0) (x y : Sl2) (m n : ℤ) :
    ⁅loop k lam m x,loop k lam n y⁆ = loop k lam (m+n) ⁅x,y⁆ +
      if m+n=0 then ((m : ℂ)*kappaForm x y) •
        (k • (1 : Module.End ℂ WakFock)) else 0 := by
  simp only [loop_apply,bracket_apply,kappaForm_apply,Fin.sum_univ_three,
    add_lie,lie_add,comm_smul,smul_comm,J_comm k lam hk,smul_add,fabc,kappa]
  by_cases hz : m+n=0
  · simp only [if_pos hz,smul_smul]; module
  · simp only [if_neg hz,smul_zero,add_zero]; module

/-- The negative oscillator-energy operator supplies the affine derivation. -/
theorem degree_loop (k lam : ℂ) (x : Sl2) (n : ℤ) :
    ⁅-Dwt,loop k lam n x⁆=(n : ℂ) • loop k lam n x := by
  simp only [loop_apply,Fin.sum_univ_three,neg_lie,lie_add,comm_smul,degree_J]
  module

/-- Fully verified current data for the charged polynomial module. Only the
noncritical-level condition is needed; all current identities are proved above. -/
noncomputable def currentData (k lam : ℂ) (hk : k + 2 ≠ 0) :
    AffineCentralCurrentData WakFock where
  loopMode := loop k lam
  degree := -Dwt
  central := k • 1
  loop_comm := loop_comm k lam hk
  degree_comm := degree_loop k lam
  central_comm x n := scalar_lie k _
  central_degree := scalar_lie k _

/-- The actual full affine Lie algebra representation at independent level
and horizontal highest weight. -/
noncomputable def rho (k lam : ℂ) (hk : k + 2 ≠ 0) :
    AffSl2 →ₗ⁅ℂ⁆ Module.End ℂ WakFock := (currentData k lam hk).rho

/-- The Lie representation acts by the specified charged current on each loop. -/
theorem rho_loop (k lam : ℂ) (hk : k + 2 ≠ 0) (x : Sl2) (n : ℤ) :
    rho k lam hk (AffineLie.ofLoop kappaForm kappaForm_isInvariant x n) =
      loop k lam n x := (currentData k lam hk).rho_ofLoop x n

/-- The central Lie generator acts by the fixed scalar level. -/
theorem rho_central (k lam : ℂ) (hk : k + 2 ≠ 0) :
    rho k lam hk (AffineLie.C kappaForm kappaForm_isInvariant) =
      k • (1 : Module.End ℂ WakFock) := (currentData k lam hk).rho_C

/-- The affine degree generator acts by negative oscillator energy. -/
theorem rho_degree (k lam : ℂ) (hk : k + 2 ≠ 0) :
    rho k lam hk (AffineLie.ell0 kappaForm kappaForm_isInvariant) = -Dwt :=
  (currentData k lam hk).rho_ell0

end VOA.Wak.Charged
