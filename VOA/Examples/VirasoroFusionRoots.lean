/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionDifferential

/-!
# Necessary roots and nonvanishing of the actual fusion diagonal

The finite gauged recurrence propagates nonzero coefficients to the terminal
resonance. If no displayed factor vanishes, its terminal source is nonzero.
No infinite hypergeometric series or division at the terminal index is used.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- When none of the finite resonance factors vanish, the undivided source
is nonzero. The proof never divides by the zero terminal denominator. -/
theorem fusionSum_ne_zero_of_no_resonance (b t y ell : ℂ) (N : ℕ) (hN : 0<N)
    (hell : ell^2+(t-1)*ell-t*b=0)
    (hfac : ∀ i : ℕ, i<N → (i:ℂ)*((i:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N≠0) :
    fusionSum b y (fusionCoeff b t y N) N≠0 := by
  intro hs
  let F := bsaGaugeSeries ell*PowerSeries.mk (fusionCoeff b t y N)
  have h0 : coeff 0 F=1 := by
    simp [F,bsaGaugeSeries,bsaGaugeCoefficient,fusionCoeff]
  have hF := fusionHyper_vanish_through b t y ell N hell hs
  have hnz : ∀ n : ℕ, n<N → coeff n F≠0 := by
    intro n
    induction n with
    | zero => intro _; rw [h0]; exact one_ne_zero
    | succ n ih =>
      intro hn hz
      have hh := hF (n+1) (by omega)
      change coeff (n+1) (fusionHyperOperator b t y ell N F)=0 at hh
      rw [fusionHyperOperator_coeff,hz,mul_zero,zero_sub,neg_eq_zero] at hh
      exact (mul_ne_zero (hfac n (by omega)) (ih (by omega))) hh
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  have hh := hF (n+1) (by omega)
  change coeff (n+1) (fusionHyperOperator b t y ell (n+1) F)=0 at hh
  rw [fusionHyperOperator_coeff] at hh
  simp only [Nat.cast_add,Nat.cast_one,sub_self,mul_zero,zero_mul,zero_sub,neg_eq_zero] at hh
  apply (mul_ne_zero (hfac n (by omega)) (hnz n (by omega)))
  simpa only [Nat.cast_succ] using hh

/-- Every zero of the terminal scalar must kill one of the finitely many
explicit resonance factors. This is a necessary root classification. -/
theorem fusionSum_zero_has_resonance (b t y ell : ℂ) (N : ℕ) (hN : 0<N)
    (hell : ell^2+(t-1)*ell-t*b=0)
    (hs : fusionSum b y (fusionCoeff b t y N) N=0) :
    ∃ i : ℕ, i<N ∧ (i:ℂ)*((i:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N=0 := by
  by_contra hn
  push_neg at hn
  exact fusionSum_ne_zero_of_no_resonance b t y ell N hN hell hn hs

/-- The possible exponent at resonance index i, written explicitly for
nonzero t. The later VirasoroFusionProduct module proves completeness. -/
noncomputable def fusionRoot (b t ell : ℂ) (N i : ℕ) : ℂ :=
  b+((i:ℂ)*((i:ℂ)-(N:ℂ)+t+2*ell)-ell*((N:ℂ)-1))/t

/-- For nonzero t, the resonance equation is precisely equality with the
displayed candidate root; the quadratic gauge condition is not needed here. -/
theorem fusionFactor_eq_zero_iff (b t y ell : ℂ) (N i : ℕ) (ht : t≠0) :
    (i:ℂ)*((i:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N=0 ↔
      y=fusionRoot b t ell N i := by
  unfold fusionConstant fusionRoot
  field_simp
  constructor <;> intro hh <;> linear_combination -hh

/-- A zero of the actual source diagonal lies in the explicit finite root
list. All operator-to-scalar and sign identifications are discharged. -/
theorem wardBSASourceDiagonal_zero_has_root (h b t a ell : ℂ) (N r : ℕ)
    (hN : 0<N) (ht : t≠0) (hell : ell^2+(t-1)*ell-t*b=0)
    (hs : wardBSASourceDiagonal h b t N r N (a+(N:ℂ))=0) :
    ∃ i : ℕ, i<N ∧ h+(r:ℂ)-a=fusionRoot b t ell N i := by
  rw [wardBSASourceDiagonal_normalized] at hs
  have hz := (mul_eq_zero.mp hs).resolve_left (pow_ne_zero _ (by norm_num : (-1:ℂ)≠0))
  obtain ⟨i,hi,he⟩ := fusionSum_zero_has_resonance b t (h+(r:ℂ)-a) ell N hN hell hz
  exact ⟨i,hi,(fusionFactor_eq_zero_iff b t _ ell N i ht).mp he⟩

/-- Avoiding the finite list proves nonvanishing of the actual diagonal.
This is an ordinary scalar criterion and introduces no rigidity assumption. -/
theorem wardBSASourceDiagonal_ne_zero_of_avoid_roots (h b t a ell : ℂ) (N r : ℕ)
    (hN : 0<N) (ht : t≠0) (hell : ell^2+(t-1)*ell-t*b=0)
    (havoid : ∀ i : ℕ, i<N → h+(r:ℂ)-a≠fusionRoot b t ell N i) :
    wardBSASourceDiagonal h b t N r N (a+(N:ℂ))≠0 := by
  intro hs
  obtain ⟨i,hi,he⟩ := wardBSASourceDiagonal_zero_has_root h b t a ell N r hN ht hell hs
  exact havoid i hi he
end VOA.InverseDS.VirasoroVerma
