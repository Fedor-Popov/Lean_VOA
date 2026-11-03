import VOA.Classification.COne.PlusRat6TwJac

/-! # `o(H⁴)`, `o(H⁶)` on the twisted lattice modules: commutators with the twisted current

`Tw m hm t = PlusTwistLattice.twistedModule m hm t` is the FLM `θ`-twisted `V_{2m}`-module
`M(1)(θ) ⊗ T` on `FockT 1 ⊗ ℂ`.  Its current modes are the twisted oscillators
`h(k/2) = modeT k ⊗ 1` (`YM_h`), and the zero modes of the charge-zero states are
`YT(p) k ⊗ 1` (`YM_ls`).  Here:

* `tw_deriv_iter`: `Y(L(-1)^p u, k) = Π_{i<p} (-(k-2i)/2) · Y(u, k-2p)` for `θ u = -u`, `k` odd;
* `comm_H4`: `[o(H⁴), h(k/2)] = -(k/2)³ h(k/2)`, `comm_H6`: `[o(H⁶), h(k/2)] = -(k/2)⁵ h(k/2)`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat6
open VOA

section Generic
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {g : Aut W} (T : TwistedModule g 2 M)

theorem aut_L_neg_one (g : Aut W) (u : V) : g (W.L (-1) u) = W.L (-1) (g u) := by
  have h := g.map_smul W.conformalVector 0 u
  rw [g.map_omega] at h
  exact h

theorem aut_L_iter_neg (u : V) (hu : g u = -u) (p : ℕ) :
    g ((W.L (-1))^[p] u) = -((W.L (-1))^[p] u) := by
  induction p with
  | zero => simpa using hu
  | succ p ih => rw [Function.iterate_succ_apply', aut_L_neg_one, ih, map_neg]

theorem mem_eig_one {u : V} (hu : g u = -u) : u ∈ g.twistedEigenspace 2 1 := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff, HeisenbergN.exp_twisted_two]
  simpa using hu

/-- Iterated derivative property on the `-1`-eigenspace. -/
theorem tw_deriv_iter (u : V) (hu : g u = -u) (p : ℕ) (k : ℤ) (hk : Odd k) (x : M) :
    T.YM ((W.L (-1))^[p] u) k x =
      (∏ i ∈ Finset.range p, (-((k : ℂ) - 2 * i) / 2)) • T.YM u (k - 2 * p) x := by
  induction p generalizing k with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    have hmem := mem_eig_one (aut_L_iter_neg u hu p)
    have h1 := tw_deriv T 1 _ hmem (k + 2) (by obtain ⟨c, rfl⟩ := hk; push_cast; omega) x
    rw [show k + 2 - 2 = k by ring, show k + 2 - 4 = k - 2 by ring] at h1
    rw [h1, ih (k - 2) (by obtain ⟨c, rfl⟩ := hk; exact ⟨c - 1, by ring⟩), smul_smul,
      Finset.prod_range_succ']
    congr 1
    · push_cast
      rw [mul_comm]
      congr 1
      · refine Finset.prod_congr rfl (fun i _ => ?_)
        push_cast; ring
      · ring
    · congr 1; push_cast; ring

end Generic

open VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusRat3 PlusRat5
open VOA.Moonshine.LatticeTwistedGeneral VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwisted
open scoped TensorProduct

variable (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2)

/-- The twisted module. -/
abbrev Tw : TwistedModule (thetaV2m m hm) 2 (FockT (rank (latP m)) ⊗[ℂ] ℂ) :=
  PlusTwistLattice.twistedModule m hm t

theorem ls_eq (P : RawPoly ℕ) : ls m P = (evR (a0 m) P) ⊗ₜ[ℂ] eGen (latP m) 0 := rfl

/-- Charge-zero states act through the twisted Heisenberg vertex operator. -/
theorem YM_ls (P : RawPoly ℕ) (k : ℤ) :
    (Tw m hm t).YM (ls m P) k = (Moonshine.YT _ (evR (a0 m) P) k).rTensor ℂ := by
  change YML (latP m) (latP_even m) (PlusTwistLattice.charge m t) (ls m P) k = _
  rw [VOA.Moonshine.LatticeTwistedGeneral.YML_apply, ls_eq, VOA.Moonshine.LatticeTwistedGeneral.FL_charge_zero _ _ _ (latP_posDef m hm),
    mode_rTFld, Moonshine.FT_val, TwistedReduction.mode_resc]
  rw [show ((2 : ℕ) : ℤ) * 0 + k = k by ring]
  rfl

theorem evR_hR : evR (a0 m) hR = (X (0, a0 m) : FockN (rank (latP m))) := by
  simp [hR, evR_cons, evR_nil, evalWord_cons, evalWord_nil]

/-- The current acts by the twisted oscillators. -/
theorem YM_h (k : ℤ) : (Tw m hm t).YM (ls m hR) k = (modeT _ (a0 m) k).rTensor ℂ := by
  rw [YM_ls, evR_hR, Moonshine.YT_X]

theorem theta_h : thetaV2m m hm (ls m hR) = -ls m hR := by
  change thetaLat (latP m) (evR (a0 m) hR ⊗ₜ[ℂ] eGen (latP m) 0) = -(evR (a0 m) hR ⊗ₜ[ℂ] eGen (latP m) 0)
  rw [thetaLat_tmul, evR_hR, sigmaN_X, neg_zero, TensorProduct.neg_tmul]

theorem theta_HP (s : ℕ) (hs : 1 ≤ s) (hs4 : s ≤ 4) :
    thetaV2m m hm (ls m (HR s)) = ls m (HR s) := by
  have h := hasN_HP m hm s hs hs4
  rw [HasN] at h
  rw [← h]
  exact (mem_VP_iff m hm _).mp (HP m hm s).2

theorem YM_h_pos (k : ℤ) (hk : 0 < k) : (Tw m hm t).YM (ls m hR) k ((1 : FockT _) ⊗ₜ[ℂ] (1 : ℂ)) = 0 := by
  rw [YM_h, LinearMap.rTensor_tmul]
  by_cases he : k % 2 = 0
  · rw [modeT_even _ _ he]; simp
  · rw [modeT_apply_pos _ _ (Int.odd_iff.mpr (by omega)) hk]; simp

/-- `[o(H⁴), h(k/2)] = -(k/2)³ h(k/2)` on the twisted module. -/
theorem comm_H4 (k : ℤ) (hk : Odd k) (x : FockT (rank (latP m)) ⊗[ℂ] ℂ) :
    (Tw m hm t).YM (ls m H4R) 6 ((Tw m hm t).YM (ls m hR) k x) =
      (Tw m hm t).YM (ls m hR) k ((Tw m hm t).YM (ls m H4R) 6 x) +
        (-((k : ℂ) / 2) ^ 3) • (Tw m hm t).YM (ls m hR) k x := by
  have hc := tw_comm (Tw m hm t) (ls m H4R) (theta_HP m hm 2 (by norm_num) (by norm_num)) 3
    (ls m hR) x k
  rw [show ((2 : ℤ) * ((3 : ℕ) : ℤ)) = 6 by norm_num] at hc
  rw [← sub_eq_iff_eq_add', hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H4_h m hm 0 1 3 certH4h_0, H4_h m hm 1 2 2 certH4h_1, H4_h m hm 2 (7/3) 1 certH4h_2,
    H4_h m hm 3 1 0 certH4h_3]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
  have hθ := theta_h m hm
  rw [tw_deriv_iter (Tw m hm t) _ hθ 3 _ (by obtain ⟨c, rfl⟩ := hk; exact ⟨c + 3, by push_cast; ring⟩),
    tw_deriv_iter (Tw m hm t) _ hθ 2 _ (by obtain ⟨c, rfl⟩ := hk; exact ⟨c + 2, by push_cast; ring⟩),
    tw_deriv_iter (Tw m hm t) _ hθ 1 _ (by obtain ⟨c, rfl⟩ := hk; exact ⟨c + 1, by push_cast; ring⟩),
    tw_deriv_iter (Tw m hm t) _ hθ 0 _ (by obtain ⟨c, rfl⟩ := hk; exact ⟨c, by push_cast; ring⟩)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, smul_smul]
  have e : ∀ i : ℕ, i ≤ 3 → 6 + k - 2 * (i : ℤ) - 2 * ((3 - i : ℕ) : ℤ) = k := by
    intro i hi; push_cast [Nat.cast_sub hi]; ring
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
  rw [← add_smul, ← add_smul, ← add_smul]
  congr 1
  simp only [show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl, show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl]
  push_cast
  ring

/-- `[o(H⁶), h(k/2)] = -(k/2)⁵ h(k/2)` on the twisted module. -/
theorem comm_H6 (k : ℤ) (hk : Odd k) (x : FockT (rank (latP m)) ⊗[ℂ] ℂ) :
    (Tw m hm t).YM (ls m H6R) 10 ((Tw m hm t).YM (ls m hR) k x) =
      (Tw m hm t).YM (ls m hR) k ((Tw m hm t).YM (ls m H6R) 10 x) +
        (-((k : ℂ) / 2) ^ 5) • (Tw m hm t).YM (ls m hR) k x := by
  have hc := tw_comm (Tw m hm t) (ls m H6R) (theta_HP m hm 3 (by norm_num) (by norm_num)) 5
    (ls m hR) x k
  rw [show ((2 : ℤ) * ((5 : ℕ) : ℤ)) = 10 by norm_num] at hc
  rw [← sub_eq_iff_eq_add', hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H6_h m hm 0 1 5 certH6h_0, H6_h m hm 1 3 4 certH6h_1, H6_h m hm 2 (13/2) 3 certH6h_2,
    H6_h m hm 3 9 2 certH6h_3, H6_h m hm 4 (31/5) 1 certH6h_4, H6_h m hm 5 1 0 certH6h_5]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
  have hθ := theta_h m hm
  have hodd : ∀ j : ℕ, Odd (10 + k - 2 * (j : ℤ)) := by
    intro j; obtain ⟨c, rfl⟩ := hk; exact ⟨c + 5 - j, by ring⟩
  rw [tw_deriv_iter (Tw m hm t) _ hθ 5 _ (hodd 0), tw_deriv_iter (Tw m hm t) _ hθ 4 _ (hodd 1),
    tw_deriv_iter (Tw m hm t) _ hθ 3 _ (hodd 2), tw_deriv_iter (Tw m hm t) _ hθ 2 _ (hodd 3),
    tw_deriv_iter (Tw m hm t) _ hθ 1 _ (hodd 4), tw_deriv_iter (Tw m hm t) _ hθ 0 _ (hodd 5)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, smul_smul]
  have e : ∀ i : ℕ, i ≤ 5 → 10 + k - 2 * (i : ℤ) - 2 * ((5 - i : ℕ) : ℤ) = k := by
    intro i hi; push_cast [Nat.cast_sub hi]; ring
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num),
    e 5 (by norm_num)]
  rw [← add_smul, ← add_smul, ← add_smul, ← add_smul, ← add_smul]
  congr 1
  simp only [show Nat.choose 5 0 = 1 from rfl, show Nat.choose 5 1 = 5 from rfl, show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl, show Nat.choose 5 4 = 5 from rfl, show Nat.choose 5 5 = 1 from rfl]
  push_cast
  ring

end VOA.Classification.COne.PlusRat6
