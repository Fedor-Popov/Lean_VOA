/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroKacCollisionStates
import VOA.Examples.VirasoroKacProduct
import VOA.Examples.VirasoroFusionThreeSpecialization

/-!
# Actual Kac states with a label at most two

The complete BSA axis and the existing two-label fusion family combine under
parameter inversion. They supply every Kac factor through level eight.
This is a finite-level determinant theorem, not unrestricted Kac existence
or minimal-model vacuum rigidity. The first uncovered pair is (3,3).
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule
open scoped Classical

/-- Inverting the nonzero Kac parameter leaves its central charge unchanged. -/
theorem vermaBSACharge_inv (t : ℂ) : vermaBSACharge t⁻¹=vermaBSACharge t := by
  unfold vermaBSACharge
  simp only [div_eq_mul_inv,inv_inv]
  ring

/-- Swapping the two Kac labels is exactly inversion of the nonzero
parameter. This transports actual modules without changing their charge. -/
theorem fusionKacWeight_swap_inv (r s t : ℂ) (ht : t≠0) :
    fusionKacWeight s r t⁻¹=fusionKacWeight r s t := by
  unfold fusionKacWeight
  field_simp
  <;> ring

/-- The BSA highest-weight convention is precisely the first Kac axis,
with the normalization used by the actual Gram polynomial. -/
theorem vermaBSAWeight_eq_kac (s : ℕ) (t : ℂ) (ht : t≠0) :
    vermaBSAWeight s t=fusionKacWeight 1 s t := by
  unfold vermaBSAWeight fusionKacWeight
  field_simp
  <;> ring

/-- Every positive first-axis label gives a genuine nonzero actual Kac
singular state at every nonzero parameter. -/
theorem hasNonzeroSingular_kac_one (s : ℕ) (hs : 0<s) (t : ℂ) (ht : t≠0) :
    HasNonzeroSingular (vermaBSACharge t) (fusionKacWeight 1 s t) s := by
  rw [← vermaBSAWeight_eq_kac s t ht]
  exact hasNonzeroSingular_bsa t s ht hs

/-- The constructed and specialized fusion-three state supplies
the entire second Kac axis, with its actual level and both positive modes. -/
theorem hasNonzeroSingular_kac_two (r : ℕ) (hr : 0<r) (t : ℂ) (ht : t≠0) :
    HasNonzeroSingular (vermaBSACharge t) (fusionKacWeight r 2 t) (r*2) := by
  have hex := fusionThree_highest_all_parameters r hr t ht
  rw [show (((3:ℕ):ℂ)-1)=(2:ℂ) by norm_num, show (3:ℕ)-1=2 by omega] at hex
  obtain ⟨v,hv,hlev,hhigh⟩ := hex
  exact ⟨v,hv,hlev,hhigh.pos_annihilate 1 (by norm_num),
    hhigh.pos_annihilate 2 (by norm_num)⟩

/-- At every nonzero complex parameter all Kac pairs having at least one
label at most two have actual nonzero singular states. Symmetry transfers
the proved families; no determinant degeneracy is assumed to obtain them. -/
theorem hasNonzeroSingular_kac_small (r s : ℕ) (hr : 0<r) (hs : 0<s)
    (hsmall : r≤2 ∨ s≤2) (t : ℂ) (ht : t≠0) :
    HasNonzeroSingular (vermaBSACharge t) (fusionKacWeight r s t) (r*s) := by
  have hswap : ∀ a b : ℕ, HasNonzeroSingular (vermaBSACharge t⁻¹)
      (fusionKacWeight b a t⁻¹) (b*a) →
      HasNonzeroSingular (vermaBSACharge t) (fusionKacWeight a b t) (a*b) := by
    intro a b hh
    simpa only [vermaBSACharge_inv,fusionKacWeight_swap_inv _ _ t ht,Nat.mul_comm] using hh
  rcases hsmall with h | h
  · rcases (show r=1 ∨ r=2 by omega) with rfl | rfl
    · simpa using hasNonzeroSingular_kac_one s hs t ht
    · exact hswap 2 s (hasNonzeroSingular_kac_two s hs t⁻¹ (inv_ne_zero ht))
  · rcases (show s=1 ∨ s=2 by omega) with rfl | rfl
    · apply hswap r 1
      simpa using hasNonzeroSingular_kac_one r hr t⁻¹ (inv_ne_zero ht)
    · exact hasNonzeroSingular_kac_two r hr t ht

/-- All positive label pairs contributing below level nine have a label
at most two. Thus actual singular existence discharges every premise in
the degree-exhaustion theorem at those levels, for nonreal parameters. -/
theorem vermaWeightDeterminant_kac_below_nine (t : ℂ) (ht : t.im≠0)
    (n : ℕ) (hn : n<9) :
    (vermaWeightGramPolynomial (vermaBSACharge t) n).det=
      Polynomial.C (∏ w : VermaPartitions n, vermaDiagonalContraction w.val)*kacWeightProduct t n := by
  have ht0 : t≠0 := by intro hz; apply ht; simp [hz]
  apply vermaWeightDeterminant_eq_kac_of_singular _ t n ht
  intro i hi
  have hle := (Finset.mem_filter.mp hi).2
  have hsmall : i.1.val+1≤2 ∨ i.2.val+1≤2 := by
    by_contra hz
    push_neg at hz
    nlinarith
  have hx := hasNonzeroSingular_kac_small
    (i.1.val+1) (i.2.val+1) (by omega) (by omega) hsmall t ht0
  simp only [Nat.cast_add,Nat.cast_one] at hx
  obtain ⟨v,hv,hlev,h1,h2⟩ := hx
  exact ⟨⟨v,hlev⟩,(fun hz => hv (congrArg Subtype.val hz)),h1,h2⟩

/-- The evaluated expected product is continuous away from parameter zero.
Only a finite product of rational Kac weights occurs; coincident roots cause
no singularity in the product itself. -/
theorem kacWeightProduct_eval_continuousAt (n : ℕ) (h t : ℂ) (ht : t≠0) :
    ContinuousAt (fun z => (kacWeightProduct z n).eval h) t := by
  simp only [kacWeightProduct,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  unfold fusionKacWeight
  fun_prop (disch := exact mul_ne_zero (by norm_num) ht)

/-- Actual scalar Gram determinants vary continuously along the Kac charge
curve. The proof uses evaluation of the already proved two-variable Gram
polynomial and does not assume any determinant factorization. -/
theorem vermaKacGramDet_continuousAt (n : ℕ) (h t : ℂ) (ht : t≠0) :
    ContinuousAt (fun z => (vermaGramMatrix (vermaBSACharge z) h n).det) t := by
  have he : (fun z => (vermaGramMatrix (vermaBSACharge z) h n).det)=
      (fun z => MvPolynomial.eval (fun i : Fin 2 => if i=0 then vermaBSACharge z else h)
        (vermaGramPolynomial n).det) := by
    funext z
    simpa using (vermaGramPolynomial_det_eval (vermaBSACharge z) h n).symm
  rw [he]
  apply (MvPolynomial.continuous_eval _).continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  split_ifs
  · unfold vermaBSACharge
    fun_prop (disch := assumption)
  · exact continuousAt_const

/-- Through level eight the FULL normalized actual Verma determinant
formula holds at EVERY nonzero complex parameter, including collisions.
Nonreal parameters supply actual singular states and degree exhaustion;
continuity extends the polynomial identity, without adding multiplicities
of colliding nullspaces. This remains a finite-level theorem. -/
theorem vermaWeightDeterminant_kac_below_nine_all (t : ℂ) (ht : t≠0)
    (n : ℕ) (hn : n<9) :
    (vermaWeightGramPolynomial (vermaBSACharge t) n).det=
      Polynomial.C (∏ w : VermaPartitions n, vermaDiagonalContraction w.val)*kacWeightProduct t n := by
  apply Polynomial.funext
  intro h
  rw [vermaWeightDeterminant_eval,Polynomial.eval_mul,Polynomial.eval_C]
  haveI := mem_closure_iff_nhdsWithin_neBot.mp (VirasoroWardTopology.nonreal_dense t)
  apply tendsto_nhds_unique_of_eventuallyEq (l := nhdsWithin t {z : ℂ | z.im≠0})
    ((vermaKacGramDet_continuousAt n h t ht).tendsto.mono_left nhdsWithin_le_nhds)
    (((continuousAt_const.mul (kacWeightProduct_eval_continuousAt n h t ht))).tendsto.mono_left
      nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := congrArg (Polynomial.eval h) (vermaWeightDeterminant_kac_below_nine z hz n hn)
  simpa only [vermaWeightDeterminant_eval,Polynomial.eval_mul,Polynomial.eval_C] using he

end VOA.InverseDS.VirasoroVerma
