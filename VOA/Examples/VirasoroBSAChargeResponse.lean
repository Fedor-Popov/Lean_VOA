/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSANonvanishing

/-!
# The charge response of the explicit BSA states

The intermediate L₂ equations cease to hold away from the singular charge.
We keep their errors and propagate them through the actual source sums.
The resulting recursively defined response factors the error by c-c_N.
This describes motion of the fixed BSA formula, not the norm derivative:
a correction to the singular vector itself can also change its L₂ image.
-/
namespace VOA.VirModule

/-- Telescoping the L₂ equation while retaining an arbitrary common scalar
error gives the old source identity plus the negative-mode propagation of
that error. The vacuum boundary terms are still zero. -/
theorem bsaSource_L2_step_with_error (c : ℂ) (N r : ℕ) (b d : ℂ) (v : ℕ → VirUniv c)
    (h1 : Lop c 1 (bsaState c N (r+1)) = (r:ℂ) • bsaState c N r)
    (h2 : ∀ j : Fin r, Lop c 2 (bsaState c N (j+2)) =
      ((j:ℂ)+2+b) • bsaState c N j + d • v j) :
    Lop c 2 (bsaSource c N (r+2)) =
      ((r:ℂ)+6+b) • bsaSource c N r + (7*(r:ℂ)+c/2) • bsaState c N r +
        d • ∑ j : Fin r, Lop c ((j:ℤ)-(r:ℤ)) (v j) := by
  classical
  have hcomm (j : Fin (r+2)) :
      Lop c 2 (Lop c ((j:ℤ)-((r:ℤ)+2)) (bsaState c N j)) =
        Lop c ((j:ℤ)-((r:ℤ)+2)) (Lop c 2 (bsaState c N j)) +
          ((r:ℂ)+4-(j:ℂ)) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) +
          (if j.val=r then c/2 else 0) • bsaState c N j := by
    have hh := Lop_apply_bracket c 2 ((j:ℤ)-((r:ℤ)+2)) (bsaState c N j)
    have he : (2:ℤ)+((j:ℤ)-((r:ℤ)+2)) = (j:ℤ)-(r:ℤ) := by ring
    rw [he] at hh
    have hi : ((j:ℤ)-(r:ℤ)=0) ↔ j.val=r := by omega
    simp only [hi] at hh
    convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+2), Lop c ((j:ℤ)-((r:ℤ)+2)) (Lop c 2 (bsaState c N j))) =
      ∑ j : Fin r, (((j:ℂ)+2+b) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) +
        d • Lop c ((j:ℤ)-(r:ℤ)) (v j)) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.cast_zero,
      bsaState_zero, bsaState_one, Lop_vacuum c (by norm_num : (-1:ℤ) ≤ 2),
      map_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show j.val+1+1=j.val+2 by omega, h2 j, map_add, map_smul, map_smul]
    rw [show ((j.val+2:ℕ):ℤ)-((r:ℤ)+2)=(j:ℤ)-(r:ℤ) by omega]
  have hB : (∑ j : Fin (r+2), ((r:ℂ)+4-(j:ℂ)) •
      Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j)) =
      (∑ j : Fin r, ((r:ℂ)+4-(j:ℂ)) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j)) +
        (7*(r:ℂ)) • bsaState c N r := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one, sub_self,
      show (r:ℤ)+1-(r:ℤ)=1 by ring, h1,
      L0_grading_gen c _ (bsaState_mem_grading c N r), smul_smul]
    push_cast
    module
  have hC : (∑ j : Fin (r+2), (if j.val=r then c/2 else 0) • bsaState c N j) =
      (c/2) • bsaState c N r := by
    rw [Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+2))]
    · simp
    · intro j hj hjr
      have he : j.val ≠ r := fun he => hjr (Fin.ext he)
      simp [he]
    · simp
  simp only [bsaSource, Nat.cast_add, Nat.cast_ofNat, map_sum, hcomm,
    Finset.sum_add_distrib]
  rw [hA,hB,hC, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [show ∀ a b x d : VirUniv c, (a+b)+(x+d) = (a+x)+d+b by intros; abel]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  have hs : (∑ j : Fin r, (((j:ℂ)+2+b) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) +
      ((r:ℂ)+4-(j:ℂ)) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j))) =
      ∑ j : Fin r, ((r:ℂ)+6+b) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← add_smul]
    congr 1
    ring
  rw [hs]
  simp only [Finset.smul_sum]
  module


/-- The coefficient of the charge error in the intermediate L₂ equation.
Its recursion has the same nonterminal denominator as the BSA state two
levels higher. It is defined at all indices, but only indices r+2<N are
used in the intermediate Ward theorem. -/
noncomputable def bsaL2Response (c : ℂ) (N : ℕ) : ℕ → VirUniv c
  | r => (-bsaParameter N / (((r:ℂ)+2)*((N:ℂ)-((r:ℂ)+2)))) •
      ((1/2:ℂ) • bsaState c N r +
        ∑ j : Fin r, Lop c ((j:ℤ)-(r:ℤ)) (bsaL2Response c N j))
termination_by r => r

/-- The undivided response of a source two levels higher. In particular,
the terminal source uses this expression without a terminal division. -/
noncomputable def bsaL2SourceResponse (c : ℂ) (N r : ℕ) : VirUniv c :=
  (1/2:ℂ) • bsaState c N r +
    ∑ j : Fin r, Lop c ((j:ℤ)-(r:ℤ)) (bsaL2Response c N j)

/-- The intermediate response is its undivided source times the recursion
coefficient at level r+2. -/
theorem bsaL2Response_eq_source (c : ℂ) (N r : ℕ) :
    bsaL2Response c N r =
      (-bsaParameter N / (((r:ℂ)+2)*((N:ℂ)-((r:ℂ)+2)))) •
        bsaL2SourceResponse c N r := by
  rw [bsaL2Response, bsaL2SourceResponse]

/-- The scalar identity that cancels the charge-independent part of the
L₂ Ward equation at any positive intermediate index. -/
theorem bsaL2_scalar_cancellation (N r : ℕ) (hr : 0<r) (hrN : r+2<N) :
    (-bsaParameter N / (((r:ℂ)+2)*((N:ℂ)-((r:ℂ)+2)))) *
      (((r:ℂ)+6+bsaL2Offset N) + (7*(r:ℂ)+bsaCharge N/2)*
        (-bsaParameter N / ((r:ℂ)*((N:ℂ)-(r:ℂ))))) =
      ((r:ℂ)+2+bsaL2Offset N)*
        (-bsaParameter N / ((r:ℂ)*((N:ℂ)-(r:ℂ)))) := by
  have hn : (N:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero N
  have hd := bsa_denominator_ne_zero N r hr (by omega)
  have hd' := bsa_denominator_ne_zero N (r+2) (by omega) hrN
  unfold bsaParameter bsaCharge bsaL2Offset
  push_cast at hd' ⊢
  field_simp [hn, hd, hd', (mul_ne_zero_iff.mp hd).1,
    (mul_ne_zero_iff.mp hd).2, (mul_ne_zero_iff.mp hd').1,
    (mul_ne_zero_iff.mp hd').2]
  <;> ring

/-- At every intermediate level the actual L₂ error is exactly c-c_N times
the recursively constructed response. This is an identity at arbitrary c,
not merely the vanishing equation at the special charge. -/
theorem bsaState_L2_response (c : ℂ) (N r : ℕ) (hr : r+2<N) :
    Lop c 2 (bsaState c N (r+2)) =
      ((r:ℂ)+2+bsaL2Offset N) • bsaState c N r +
        (c-bsaCharge N) • bsaL2Response c N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hs := bsaSource_L2_step_with_error c N r (bsaL2Offset N)
      (c-bsaCharge N) (bsaL2Response c N)
      (bsaState_L1 c N r (by omega)) (fun j => ih j j.isLt (by omega))
    rw [bsaState_eq_source c N (r+2) (by omega), map_smul, hs,
      bsaL2Response_eq_source, bsaL2SourceResponse]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    by_cases hz : r=0
    · subst r
      simp only [bsaSource, Fin.sum_univ_zero, smul_zero, zero_add, add_zero,
        Nat.cast_zero, zero_add, smul_smul, ← add_smul]
      congr 1
      have hn : (N:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero N
      have hd := bsa_denominator_ne_zero N 2 (by omega) hr
      unfold bsaParameter bsaCharge bsaL2Offset
      norm_num at hd ⊢
      field_simp [hn, hd]
      <;> ring
    · rw [bsaState_eq_source c N r (by omega)]
      have he := bsaL2_scalar_cancellation N r (by omega) hr
      simp only [smul_add, smul_smul]
      linear_combination (norm := module) he • bsaSource c N r

/-- The L₂ image of the terminal explicit vector factors by the charge
difference, with no division at the terminal level. This is the starting
point for a norm-derivative calculation; nonzero response alone does not
exclude a compensating first-order change of the vector. -/
theorem bsaSource_L2_terminal_response (c : ℂ) (N r : ℕ)
    (hN : N=r+2) (hr : 0<r) :
    Lop c 2 (bsaSource c N N) =
      (c-bsaCharge N) • bsaL2SourceResponse c N r := by
  subst N
  rw [bsaSource_L2_step_with_error c (r+2) r (bsaL2Offset (r+2))
    (c-bsaCharge (r+2)) (bsaL2Response c (r+2))
    (bsaState_L1 c (r+2) r (by omega))
    (fun j => bsaState_L2_response c (r+2) j (by omega)),
    bsaL2SourceResponse, bsaState_eq_source c (r+2) r hr]
  have hd : (r:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hn : (r:ℂ)+3 ≠ 0 := by exact_mod_cast (show r+3 ≠ 0 by omega)
  have he : ((r:ℂ)+6+bsaL2Offset (r+2)) + (7*(r:ℂ)+bsaCharge (r+2)/2) *
      (-bsaParameter (r+2) / ((r:ℂ)*(((r+2:ℕ):ℂ)-(r:ℂ)))) = 0 := by
    unfold bsaParameter bsaCharge bsaL2Offset
    push_cast
    field_simp [hd, hn]
    <;> ring_nf
    <;> field_simp [show (3:ℂ)+(r:ℂ) ≠ 0 by simpa [add_comm] using hn]
    <;> ring
  simp only [smul_add, smul_smul]
  linear_combination (norm := module) he • bsaSource c (r+2) r


/-- Each response is homogeneous of the level left after applying L₂.
All terms in its recursion have that same level. -/
theorem bsaL2Response_mem_grading (c : ℂ) (N r : ℕ) :
    bsaL2Response c N r ∈ gradingVir c (r:ℤ) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [bsaL2Response_eq_source, bsaL2SourceResponse]
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (bsaState_mem_grading c N r)
    · apply Submodule.sum_mem
      intro j hj
      have hh := Lop_maps_grading c ((j:ℤ)-(r:ℤ)) (ih j j.isLt)
      simpa using hh

/-- In the Fock realization, a response has oscillator degree at most its
level. Translation costs no polynomial degree, as in the original recursion. -/
theorem fockMap_bsaL2Response_mem {c lam : ℂ} (hlam : 1-12*lam^2=c) (N r : ℕ) :
    fockMap hlam (bsaL2Response c N r) ∈ FDeg r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [bsaL2Response_eq_source, bsaL2SourceResponse, map_smul, map_add, map_smul,
      map_sum]
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (fockMap_bsaState_mem hlam N r)
    · apply Submodule.sum_mem
      intro j hj
      rw [fockMap_Lop]
      have hp := ih j j.isLt
      by_cases he : j.val+1=r
      · rw [show (j:ℤ)-(r:ℤ) = -1 by omega]
        exact FDeg_mono (by omega) (Lld_neg_one_mem_FDeg lam hp)
      · have hle : j.val+2 ≤ r := by omega
        rw [show (j:ℤ)-(r:ℤ) = -((r-j.val-2:ℕ):ℤ)-2 by omega]
        exact FDeg_mono hle (Lld_mem_FDeg lam (r-j.val-2) hp)

/-- In the propagated error sum only the response two levels below can
contribute to the top oscillator degree. The estimate keeps all other terms. -/
theorem fockMap_bsaL2_propagation_error {c lam : ℂ}
    (hlam : 1-12*lam^2=c) (N k : ℕ) :
    (∑ j : Fin (k+2), Lld lam ((j:ℤ)-((k+2:ℕ):ℤ))
      (fockMap hlam (bsaL2Response c N j))) -
      creationPoly 0 * fockMap hlam (bsaL2Response c N k) ∈ FDeg (k+1) := by
  classical
  let j0 : Fin (k+2) := ⟨k,by omega⟩
  have hj0 : j0 ∈ (Finset.univ : Finset (Fin (k+2))) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hj0]
  have he : Lld lam ((j0:ℤ)-((k+2:ℕ):ℤ)) (fockMap hlam (bsaL2Response c N j0)) =
      Lld lam (-2) (fockMap hlam (bsaL2Response c N k)) := by simp [j0]
  rw [he]
  have hs : ∀ a b d : Fock, a+b-d=(a-d)+b := by intros; ring
  rw [hs]
  apply Submodule.add_mem
  · simpa using errLd_mem lam 0 (fockMap_bsaL2Response_mem hlam N k)
  · apply Submodule.sum_mem
    intro j hj
    have hjn : j.val ≠ k := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (Fin.ext he)
    have hp := fockMap_bsaL2Response_mem hlam N j
    by_cases he : j.val=k+1
    · rw [show (j:ℤ)-((k+2:ℕ):ℤ) = -1 by omega]
      exact FDeg_mono (by omega) (Lld_neg_one_mem_FDeg lam hp)
    · have hle : j.val+2 ≤ k+1 := by have := j.isLt; omega
      rw [show (j:ℤ)-((k+2:ℕ):ℤ) = -((k-j.val:ℕ):ℤ)-2 by have := j.isLt; omega]
      exact FDeg_mono hle (Lld_mem_FDeg lam (k-j.val) hp)

/-- The source response has top coefficient (k+1)/2 times the old BSA
coefficient, while the intermediate response acquires the next recursion
factor. These simultaneous estimates sum all contributions to the top degree. -/
theorem fockMap_bsaL2Response_top {c lam : ℂ} (hlam : 1-12*lam^2=c) (N k : ℕ) :
    (fockMap hlam (bsaL2SourceResponse c N (2*k)) -
      ((((k:ℂ)+1)/2)*bsaTopCoefficient N k) • (creationPoly 0)^k ∈ FDeg (2*k-1)) ∧
    (fockMap hlam (bsaL2Response c N (2*k)) -
      ((((k:ℂ)+1)/2)*bsaTopCoefficient N (k+1)) • (creationPoly 0)^k ∈ FDeg (2*k-1)) := by
  induction k with
  | zero =>
    constructor
    · simp [bsaL2SourceResponse, bsaState_zero, vacVec, fockMap_mk, vacuum,
        bsaTopCoefficient]
    · rw [bsaL2Response_eq_source]
      simp [bsaL2SourceResponse, bsaState_zero,
        vacVec, fockMap_mk, vacuum, bsaTopCoefficient, smul_smul]
      ring_nf
      exact (FDeg _).zero_mem
  | succ k ih =>
    have hsource : fockMap hlam (bsaL2SourceResponse c N (2*(k+1))) -
        ((((k+1:ℕ):ℂ)+1)/2*bsaTopCoefficient N (k+1)) • (creationPoly 0)^(k+1)
        ∈ FDeg (2*(k+1)-1) := by
      have hf := (FDeg _).smul_mem (1/2:ℂ) (fockMap_bsaState_top hlam N (k+1))
      have he := fockMap_bsaL2_propagation_error hlam N (2*k)
      have hi : creationPoly 0 * (fockMap hlam (bsaL2Response c N (2*k)) -
          ((((k:ℂ)+1)/2)*bsaTopCoefficient N (k+1)) • (creationPoly 0)^k)
          ∈ FDeg (2*k+1) := by
        cases k with
        | zero =>
          rw [bsaL2Response_eq_source]
          simp [bsaL2SourceResponse, bsaState_zero,
            vacVec, fockMap_mk, vacuum, bsaTopCoefficient, smul_smul]
          have he : -bsaParameter N / (2*((N:ℂ)-2)) * (1/2:ℂ) =
              (1/2:ℂ) * (-bsaParameter N / (2*((N:ℂ)-2))) := by ring
          simp only [one_div] at he
          rw [he, sub_self, mul_zero]
          exact (FDeg _).zero_mem
        | succ k => exact FDeg_mono (by omega) (creationPoly_mul_mem 0 ih.2)
      have hf' : (1/2:ℂ) • (fockMap hlam (bsaState c N (2*(k+1))) -
          bsaTopCoefficient N (k+1) • (creationPoly 0)^(k+1)) ∈ FDeg (2*k+1) := by
        simpa only [show 2*(k+1)-1=2*k+1 by omega] using hf
      have hsum := (FDeg (2*k+1)).add_mem ((FDeg _).add_mem hf' he) hi
      convert hsum using 1
      · simp only [bsaL2SourceResponse, map_add, map_smul, map_sum, fockMap_Lop,
          show 2*(k+1)=2*k+2 by omega, Nat.cast_add, Nat.cast_one,
          mul_sub, mul_smul_comm, ← pow_succ']
        module
    refine ⟨hsource, ?_⟩
    rw [bsaL2Response_eq_source, map_smul, bsaTopCoefficient]
    have hh := (FDeg _).smul_mem
      (-bsaParameter N / ((((2*(k+1):ℕ):ℂ)+2)*((N:ℂ)-(((2*(k+1):ℕ):ℂ)+2)))) hsource
    convert hh using 1 <;> simp only [smul_sub, smul_smul, Nat.cast_mul,
      Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] <;> congr 1 <;> ring

/-- The terminal source response is nonzero at every even level and every
charge. Its top coefficient is (k+1)/2 times a nonzero intermediate product.
This does not yet evaluate the scalar norm derivative. -/
theorem bsaL2SourceResponse_even_ne_zero (c : ℂ) (k : ℕ) :
    bsaL2SourceResponse c (2*(k+1)) (2*k) ≠ 0 := by
  obtain ⟨lam,hlam⟩ := exists_lam c
  have hh := (fockMap_bsaL2Response_top hlam (2*(k+1)) k).1
  have ha : (((k:ℂ)+1)/2)*bsaTopCoefficient (2*(k+1)) k ≠ 0 :=
    mul_ne_zero (div_ne_zero (Nat.cast_add_one_ne_zero k) (by norm_num))
      (bsaTopCoefficient_ne_zero (2*(k+1)) k (by omega))
  have hp : creationPoly 0 ≠ 0 := by
    intro hz
    have hn := tSub_creationPoly_ne_zero 2 0 (by omega)
    simpa [hz] using hn
  have hn : ((((k:ℂ)+1)/2)*bsaTopCoefficient (2*(k+1)) k) • (creationPoly 0)^k ≠ 0 :=
    smul_ne_zero ha (pow_ne_zero _ hp)
  have hom : (((((k:ℂ)+1)/2)*bsaTopCoefficient (2*(k+1)) k) • (creationPoly 0)^k).IsHomogeneous
      (2*k) := by
    change _ ∈ MvPolynomial.homogeneousSubmodule ℕ ℂ (2*k)
    exact Submodule.smul_mem _ _ ((creationPoly_isHomogeneous 0).pow k)
  intro hz
  cases k with
  | zero =>
    have hv := vacVec_ne_zero c
    apply hv
    simpa [bsaL2SourceResponse, bsaState_zero] using hz
  | succ k =>
    rw [hz, map_zero, zero_sub] at hh
    have hd := FDeg_totalDegree ((FDeg _).neg_mem hh)
    rw [neg_neg, hom.totalDegree hn] at hd
    omega

/-- At even levels N>=4 the fixed explicit BSA formula satisfies the L₂
singular equation exactly at c_N. Other vectors could correct its charge
response, so this equivalence alone is not a rigidity theorem. -/
theorem bsaSource_L2_eq_zero_iff (c : ℂ) (k : ℕ) (hk : 1≤k) :
    Lop c 2 (bsaSource c (2*(k+1)) (2*(k+1))) = 0 ↔
      c = bsaCharge (2*(k+1)) := by
  rw [bsaSource_L2_terminal_response c (2*(k+1)) (2*k) (by omega) (by omega)]
  simp only [smul_eq_zero, bsaL2SourceResponse_even_ne_zero, or_false, sub_eq_zero]

end VOA.VirModule
