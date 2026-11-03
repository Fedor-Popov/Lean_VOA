/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArPairing
import VOA.Modules.LogTensorPzHomogeneous

/-! # Genuine zeroth A-transform Jacobi for logarithmic modules

The actual contragredient pairings transpose the proved opposite Jacobi
identity of the Jordan-prepared genuine logarithmic operator. All finite sums
are justified, and actual homogeneous decompositions extend the result globally.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- Actual weak opposite modes are lower truncated for every homogeneous state. -/
theorem oppB_truncated_homogeneous (N : WeakModule W M₂) {d : ℤ} {u : V}
    (hu : u ∈ W.grading d) (y : M₂) :
    ∃ K : ℤ, ∀ p : ℤ, p ≤ K → oppB N u p y = 0 := by
  classical
  choose K hK using fun j : ℕ => N.truncation ((W.L 1 ^ j) u) y
  let s := Finset.range (d.toNat+1)
  have hs : s.Nonempty := ⟨0,by simp [s]⟩
  let B : ℤ := s.sup' hs (fun j : ℕ => (j:ℤ)+K j)
  refine ⟨2*d-2-B,fun p hp => ?_⟩
  rw [oppB_homog N hu p]
  simp only [LinearMap.smul_apply,LinearMap.coe_sum,Finset.sum_apply]
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro j hj
  have hjB : (j:ℤ)+K j ≤ B := Finset.le_sup' (fun j : ℕ => (j:ℤ)+K j) hj
  rw [hK j _ (by omega),smul_zero]

/-- The actual opposite coefficient family is truncated towards negative exponents. -/
theorem twI_negative_truncated (A₁ : C2Rigid.GWModule W M₁)
    {F : IntertwiningModes M₁ M₂ M₃} (hF : ModeTruncated F)
    (a : ℂ) (x : M₁) (y : M₂) (c : ℂ) :
    ∃ K : ℤ, ∀ i : ℤ, K ≤ i → twI A₁ F a (c-i) x y = 0 := by
  classical
  obtain ⟨J,hJ⟩ := L1w_pow_eventually A₁ x
  choose Nf hNf using fun j : ℕ => hF ((L1w A₁.toWeakModule ^ j) x) y (2*a-c-2-j)
  refine ⟨∑ j ∈ Finset.range J, ((Nf j).natAbs:ℤ),fun i hi => ?_⟩
  rw [twI_apply_eq_sum A₁ F a _ hJ y]
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro j hj
  have hle : ((Nf j).natAbs:ℤ) ≤ ∑ j ∈ Finset.range J, ((Nf j).natAbs:ℤ) :=
    Finset.single_le_sum (f := fun j => ((Nf j).natAbs:ℤ)) (fun _ _ => by positivity) hj
  have hz := hNf j i (by have := Int.le_natAbs (a := Nf j); omega)
  rw [show 2*a-(c-i)-2-j = 2*a-c-2-j+i by ring,hz,smul_zero]

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- The actual zeroth A-transform Jacobi identity on genuine homogeneous inputs. -/
theorem modes_zero_jacobi_homogeneous {d : ℤ} {u : V} (hu : u ∈ W.grading d)
    {a c : ℂ} {x : M₁} {t : C2Rigid.RestrictedDual N₃.toGW}
    (hx : x ∈ N₁.weight a) (ht : t ∈ (contraLog N₃).weight c)
    (ell m : ℤ) (n : ℂ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode ((contraLog N₂).YM u) (ell+m-i) (modes N₁ N₂ N₃ Y 0 (n+i) 0 x t) -
        negOnePow ell • modes N₁ N₂ N₃ Y 0 (ell+n-i) 0 x (mode ((contraLog N₃).YM u) (m+i) t))) =
      ∑ᶠ i : ℤ, cbz m i • modes N₁ N₂ N₃ Y 0 (m+n-i) 0 (mode (N₁.YM u) (ell+i) x) t := by
  apply C2Rigid.restrictedDual_ext_of_pairing N₂.toGW
  intro b y hy
  let F := zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)
  have hF : IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule F :=
    zeroFamily_isJacobi N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)
  have htr := modes_truncated N₁ N₂ N₃ Y 0
  change C2Rigid.dualPairing N₂.toGW y (∑ᶠ i,
      IsLogIntertwining.jacL (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule
        (modes N₁ N₂ N₃ Y 0) u x t ell m n 0 i) =
    C2Rigid.dualPairing N₂.toGW y (∑ᶠ i,
      IsLogIntertwining.jacR N₁.toWeakModule (modes N₁ N₂ N₃ Y 0) u x t ell m n 0 i)
  rw [map_finsum _ (IsLogIntertwining.jacL_support_finite htr u x t ell m n 0),
    map_finsum _ (IsLogIntertwining.jacR_support_finite (modes N₁ N₂ N₃ Y 0) u x t ell m n 0)]
  let OJL : ℤ → M₃ := fun i => (negOnePow i * cbz ell i) •
    (twI N₁.toGW F a (n+i) x (oppB N₂.toWeakModule u (ell+m-i) y) -
      negOnePow ell • oppB N₃.toWeakModule u (m+i) (twI N₁.toGW F a (ell+n-i) x y))
  let OJR : ℤ → M₃ := fun i => cbz m i •
    twI N₁.toGW F (a+d-((ell+i:ℤ):ℂ)-1) (m+n-i) (mode (N₁.YM u) (ell+i) x) y
  have hL : ∀ i, C2Rigid.dualPairing N₂.toGW y
      (IsLogIntertwining.jacL (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule
        (modes N₁ N₂ N₃ Y 0) u x t ell m n 0 i) = C2Rigid.dualPairingFlip N₃.toGW t (OJL i) := by
    intro i
    simp only [IsLogIntertwining.jacL,OJL,map_smul,map_sub,C2Rigid.dualPairingFlip_apply]
    rw [pair_contra_opposite N₂ hu (ell+m-i),pair_modes_zero N₁ N₂ N₃ Y (n+i) hx,
      pair_modes_zero N₁ N₂ N₃ Y (ell+n-i) hx,pair_contra_opposite N₃ hu (m+i)]
  have hR : ∀ i, C2Rigid.dualPairing N₂.toGW y
      (IsLogIntertwining.jacR N₁.toWeakModule (modes N₁ N₂ N₃ Y 0) u x t ell m n 0 i) =
      C2Rigid.dualPairingFlip N₃.toGW t (OJR i) := by
    intro i
    simp only [IsLogIntertwining.jacR,OJR,map_smul,C2Rigid.dualPairingFlip_apply]
    rw [pair_modes_zero N₁ N₂ N₃ Y (m+n-i) (N₁.mode_mem_weight hu hx (ell+i))]
  have hfinL : (Function.support OJL).Finite := by
    obtain ⟨K,hK⟩ := oppB_truncated_homogeneous N₂.toWeakModule hu y
    obtain ⟨L,hL⟩ := twI_negative_truncated N₁.toGW hF.truncation a x y (ell+n)
    refine (Set.finite_Icc 0 (max (ell+m-K) L)).subset (fun i hi => ?_)
    rw [Function.mem_support] at hi
    rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_,not_lt.mp fun h => hi ?_⟩
    · simp only [OJL,cbz_apply_neg ell h,mul_zero,zero_smul]
    · simp only [OJL]
      rw [hK _ (by omega),hL i (by omega)]
      simp only [map_zero,smul_zero,sub_zero]
  have hfinR : (Function.support OJR).Finite := by
    obtain ⟨K,hK⟩ := N₁.truncation u x
    refine (Set.finite_Icc 0 (K-ell)).subset (fun i hi => ?_)
    rw [Function.mem_support] at hi
    rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_,not_lt.mp fun h => hi ?_⟩
    · simp only [OJR,cbz_apply_neg m h,zero_smul]
    · simp only [OJR]
      rw [hK (ell+i) (by omega)]
      simp only [map_zero,LinearMap.zero_apply,smul_zero]
  rw [finsum_congr hL,finsum_congr hR,← map_finsum _ hfinL,← map_finsum _ hfinR]
  apply congrArg (C2Rigid.dualPairingFlip N₃.toGW t)
  simpa only [OJL,OJR,Int.cast_add] using opp_jacobi (A₁ := N₁.toGW) (A₂ := N₂.toWeakModule) (A₃ := N₃.toWeakModule)
    (Y := F) hF hu a x y ell m n

/-- Genuine homogeneous decomposition gives actual zeroth A-Jacobi on all vectors. -/
theorem modes_zero_isJacobi : IsJacobiFamily N₁.toWeakModule (contraLog N₃).toWeakModule
    (contraLog N₂).toWeakModule (fun n => modes N₁ N₂ N₃ Y 0 n 0) where
  truncation x t n := by
    obtain ⟨K,hK⟩ := modes_truncated N₁ N₂ N₃ Y 0 x t n
    exact ⟨K,fun j hj => hK j hj 0⟩
  jacobi := modeJacobi_of_homogeneous N₁ (contraLog N₃) (contraLog N₂).toWeakModule
    (fun x t n => by obtain ⟨K,hK⟩ := modes_truncated N₁ N₂ N₃ Y 0 x t n; exact ⟨K,fun j hj => hK j hj 0⟩)
    (fun d u hu a c x t hx ht ell m n => modes_zero_jacobi_homogeneous N₁ N₂ N₃ Y hu hx ht ell m n)

/-- The genuine A_0 logarithmic operator reconstructed from its actual zeroth modes.
Its derivative and every higher-log Jacobi coefficient are proved. -/
noncomputable def transform : LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule
    (contraLog N₂).toWeakModule :=
  ⟨logLift N₁ (contraLog N₃) (contraLog N₂) (fun n => modes N₁ N₂ N₃ Y 0 n 0),
    isLogIntertwining_logLift_of_jacobi_weight N₁ (contraLog N₃) (contraLog N₂)
      (modes_zero_isJacobi N₁ N₂ N₃ Y) (fun n => modes_weight N₁ N₂ N₃ Y 0 n 0)⟩

/-- The genuine reconstructed A_0 has the exact actual FHL zeroth coefficients. -/
theorem transform_logZero (n : ℂ) : (transform N₁ N₂ N₃ Y).1 n 0 = modes N₁ N₂ N₃ Y 0 n 0 :=
by
  change logLift N₁ (contraLog N₃) (contraLog N₂) (fun q => modes N₁ N₂ N₃ Y 0 q 0) n 0 = _
  exact logLift_zero N₁ (contraLog N₃) (contraLog N₂) (fun q => modes N₁ N₂ N₃ Y 0 q 0) n

end VOA.LogTensor.Ar
