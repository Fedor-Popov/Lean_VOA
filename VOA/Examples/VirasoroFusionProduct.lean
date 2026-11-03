/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionLabelRoots

/-!
# A finite product for the actual scalar obstruction

Only coefficients strictly before the resonance are propagated. The terminal
coefficient is retained as the actual source, so no infinite hypergeometric
solution or division by the terminal zero is involved.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- The scalar differential equation holds before the resonance without
any assumption that the terminal source vanishes. -/
theorem fusionOperator_vanish_before (b t y : ℂ) (N n : ℕ) (hn : n<N) :
    coeff n (fusionOperator b t y N (PowerSeries.mk (fusionCoeff b t y N)))=0 := by
  have hw := fusionCoeff_ward b t y N
  cases n with
  | zero =>
    rw [fusionOperator_expand]
    simp only [map_add,map_sub,sub_mul,add_mul,one_mul,coeff_C_mul,mul_assoc,
      coeff_zero_X_mul,two_mul,bsaEuler_coeff,coeff_mk,Nat.cast_zero,zero_mul,
      sub_zero,zero_add,mul_zero]
  | succ n =>
    cases n with
    | zero =>
      have hw1 := hw 1 hn
      simp only [fusionSum,Fin.sum_univ_one,Fin.val_zero,Nat.cast_zero,Nat.cast_one,
        sub_zero,zero_add,show fusionCoeff b t y N 0=1 by rw [fusionCoeff],mul_one] at hw1
      rw [fusionOperator_expand]
      simp only [map_add,map_sub,sub_mul,add_mul,one_mul,coeff_C_mul,mul_assoc,
        coeff_succ_X_mul,coeff_zero_X_mul,two_mul,bsaEuler_coeff,coeff_mk,
        Nat.cast_zero,Nat.cast_one,zero_mul,sub_zero,zero_add,
        show fusionCoeff b t y N 0=1 by rw [fusionCoeff]]
      linear_combination hw1
    | succ n =>
      rw [show n+1+1=n+2 by omega,fusionOperator_coeff]
      have h0 := hw n (by omega)
      have h1 := hw (n+1) (by omega)
      have h2 := hw (n+2) (by omega)
      push_cast at h1 h2
      linear_combination h2-2*h1+h0

/-- The terminal coefficient of the polynomial differential equation is
exactly the undivided source, with its sign and parameter factor. -/
theorem fusionOperator_terminal (b t y : ℂ) (N : ℕ) (hN : 2≤N) :
    coeff N (fusionOperator b t y N (PowerSeries.mk (fusionCoeff b t y N)))=
      -t*fusionSum b y (fusionCoeff b t y N) N := by
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, N=n+2 := ⟨N-2,by omega⟩
  rw [fusionOperator_coeff]
  have h0 := fusionCoeff_ward b t y (n+2) n (by omega)
  have h1 := fusionCoeff_ward b t y (n+2) (n+1) (by omega)
  push_cast at h0 h1 ⊢
  linear_combination -2*h1+h0

/-- When the second factor vanishes below N, its product's Nth coefficient
uses only the first factor's constant coefficient. -/
theorem fusion_mul_first_coefficient (F G : PowerSeries ℂ) (N : ℕ)
    (hG : ∀ n<N, coeff n G=0) : coeff N (F*G)=coeff 0 F*coeff N G := by
  rw [coeff_mul,Finset.sum_eq_single (0,N)]
  · intro p hp hne
    have hp' := Finset.mem_antidiagonal.mp hp
    have hlt : p.2<N := by
      by_contra hn
      have hp0 : p.1=0 := by omega
      have hpN : p.2=N := by omega
      exact hne (Prod.ext hp0 hpN)
    rw [hG p.2 hlt,mul_zero]
  · intro hnot
    exact False.elim (hnot (by simp))

/-- The gauged equation vanishes strictly before the resonance, regardless
of the value of the actual terminal obstruction. -/
theorem fusionHyper_vanish_before (b t y ell : ℂ) (N : ℕ)
    (hell : ell^2+(t-1)*ell-t*b=0) (n : ℕ) (hn : n<N) :
    coeff n (fusionHyperOperator b t y ell N
      (bsaGaugeSeries ell*PowerSeries.mk (fusionCoeff b t y N)))=0 := by
  apply bsaSeries_remove_one_sub _ n
  · rw [fusionOperator_gauge b t y ell N hell]
    apply bsaSeries_mul_vanish
    intro j hj
    exact fusionOperator_vanish_before b t y N j (by omega)
  · rfl

/-- The gauge preserves the first nonzero differential coefficient. At the
terminal index this is precisely the original scalar source obstruction. -/
theorem fusionHyper_terminal (b t y ell : ℂ) (N : ℕ) (hN : 2≤N)
    (hell : ell^2+(t-1)*ell-t*b=0) :
    coeff N (fusionHyperOperator b t y ell N
      (bsaGaugeSeries ell*PowerSeries.mk (fusionCoeff b t y N)))=
      -t*fusionSum b y (fusionCoeff b t y N) N := by
  have hh := congrArg (coeff N) (fusionOperator_gauge b t y ell N hell
    (PowerSeries.mk (fusionCoeff b t y N)))
  rw [fusion_mul_first_coefficient _ _ N (fusionOperator_vanish_before b t y N),
    fusionOperator_terminal b t y N hN] at hh
  have hg : coeff 0 (bsaGaugeSeries ell)=1 := by simp [bsaGaugeSeries,bsaGaugeCoefficient]
  rw [hg,one_mul] at hh
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  rw [sub_mul,one_mul,map_sub,coeff_succ_X_mul,
    fusionHyper_vanish_before b t y ell (n+1) hell n (by omega),sub_zero] at hh
  exact hh

/-- The product of the nonresonant coefficient denominators. All its
factors are strictly before N; its optional factorial rewrite is unnecessary. -/
noncomputable def fusionDenominator (N n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, ((j:ℂ)+1)*((j:ℂ)+1-(N:ℂ))

/-- None of the denominator factors vanish below the terminal index. -/
theorem fusionDenominator_ne_zero (N n : ℕ) (hn : n<N) : fusionDenominator N n≠0 := by
  unfold fusionDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjn := Finset.mem_range.mp hj
  apply mul_ne_zero (Nat.cast_add_one_ne_zero j)
  have he : (j:ℤ)+1-(N:ℤ)≠0 := by omega
  exact_mod_cast he

/-- Multiplying the adjacent recurrence yields a finite coefficient product
identity, without introducing a hypergeometric solution past resonance. -/
theorem fusionGauge_coefficient_product (b t y ell : ℂ) (N n : ℕ)
    (hell : ell^2+(t-1)*ell-t*b=0) (hn : n<N) :
    coeff n (bsaGaugeSeries ell*PowerSeries.mk (fusionCoeff b t y N))*fusionDenominator N n=
      ∏ i ∈ Finset.range n, ((i:ℂ)*((i:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N) := by
  induction n with
  | zero => simp [fusionDenominator,bsaGaugeSeries,bsaGaugeCoefficient,fusionCoeff]
  | succ n ih =>
    have hh := fusionHyper_vanish_before b t y ell N hell (n+1) hn
    rw [fusionHyperOperator_coeff,sub_eq_zero] at hh
    have ih' := ih (by omega)
    simp only [fusionDenominator,Finset.prod_range_succ] at ih' ⊢
    linear_combination hh* (∏ j ∈ Finset.range n, ((j:ℂ)+1)*((j:ℂ)+1-(N:ℂ))) +
      ((n:ℂ)*((n:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N)*ih'

/-- The actual terminal source satisfies an exact finite product identity.
The only denominator product consists of nonzero intermediate factors. -/
theorem fusionSum_product (b t y ell : ℂ) (N : ℕ) (hN : 2≤N)
    (hell : ell^2+(t-1)*ell-t*b=0) :
    t*fusionSum b y (fusionCoeff b t y N) N*fusionDenominator N (N-1)=
      ∏ i ∈ Finset.range N, ((i:ℂ)*((i:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  have ht := fusionHyper_terminal b t y ell (n+1) hN hell
  rw [fusionHyperOperator_coeff] at ht
  have hp := fusionGauge_coefficient_product b t y ell (n+1) n hell (by omega)
  simp only [Nat.succ_sub_one,Finset.prod_range_succ]
  have he : (n:ℂ)+1-((n+1:ℕ):ℂ)=0 := by push_cast; ring
  rw [he,mul_zero,zero_mul,zero_sub] at ht
  linear_combination fusionDenominator (n+1) n*ht+
    ((n:ℂ)*((n:ℂ)-((n+1:ℕ):ℂ)+t+2*ell)-fusionConstant b t y ell (n+1))*hp
/-- The finite product gives both directions of the resonance criterion:
a zero factor is sufficient as well as necessary for the source to vanish. -/
theorem fusionSum_zero_iff_resonance (b t y ell : ℂ) (N : ℕ) (hN : 2≤N)
    (ht : t≠0) (hell : ell^2+(t-1)*ell-t*b=0) :
    fusionSum b y (fusionCoeff b t y N) N=0 ↔
      ∃ i : ℕ, i<N ∧ (i:ℂ)*((i:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N=0 := by
  constructor
  · exact fusionSum_zero_has_resonance b t y ell N (by omega) hell
  · rintro ⟨i,hi,he⟩
    have hp := fusionSum_product b t y ell N hN hell
    have hz : (∏ j ∈ Finset.range N,
        ((j:ℂ)*((j:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N))=0 :=
      Finset.prod_eq_zero_iff.mpr ⟨i,Finset.mem_range.mpr hi,he⟩
    rw [hz] at hp
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right
      (fusionDenominator_ne_zero N (N-1) (by omega)))).resolve_left ht

/-- The actual operator diagonal vanishes exactly on the explicit finite
root list. All signs, intermediate factors and field-weight shifts are included. -/
theorem wardBSASourceDiagonal_zero_iff_root (h b t a ell : ℂ) (N r : ℕ)
    (hN : 2≤N) (ht : t≠0) (hell : ell^2+(t-1)*ell-t*b=0) :
    wardBSASourceDiagonal h b t N r N (a+(N:ℂ))=0 ↔
      ∃ i : ℕ, i<N ∧ h+(r:ℂ)-a=fusionRoot b t ell N i := by
  rw [wardBSASourceDiagonal_normalized,mul_eq_zero]
  have hn : (-1:ℂ)^N≠0 := pow_ne_zero _ (by norm_num)
  simp only [hn,false_or]
  rw [fusionSum_zero_iff_resonance b t _ ell N hN ht hell]
  simp only [fusionFactor_eq_zero_iff b t _ ell N _ ht]

/-- On the intended label curves, the actual diagonal is zero precisely
when an integer index satisfies the explicit linear parameter equation. -/
theorem wardBSASourceDiagonal_label_zero_iff (A N r : ℕ) (t : ℂ)
    (hN : 2≤N) (ht : t≠0) :
    wardBSASourceDiagonal (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N r N (vermaBSAWeight N t+(N:ℂ))=0 ↔
      ∃ i : ℕ, i<N ∧ ((i:ℂ)*(A:ℂ)-(r:ℂ))*t=(i:ℂ)*((N:ℂ)-1-(i:ℂ)) := by
  rw [wardBSASourceDiagonal_zero_iff_root _ _ _ _ (fusionLabelGauge (A:ℂ) t) N r hN ht
    (fusionLabelGauge_quadratic (A:ℂ) t ht)]
  simp only [fusionLabel_root_iff (A:ℂ) t N _ r ht]

/-- The initial diagonal vanishes: the triangular equation allows a free
leading coefficient. This statement does not construct the kernel sequence. -/
theorem wardBSASourceDiagonal_label_initial (A N : ℕ) (t : ℂ)
    (hN : 2≤N) (ht : t≠0) :
    wardBSASourceDiagonal (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N 0 N (vermaBSAWeight N t+(N:ℂ))=0 := by
  apply (wardBSASourceDiagonal_label_zero_iff A N 0 t hN ht).mpr
  exact ⟨0,by omega,by simp⟩

/-- The terminal diagonal vanishes at level A(N-1), where a singular source
is expected. Vanishing of this scalar alone does not prove a nonzero state. -/
theorem wardBSASourceDiagonal_label_terminal (A N : ℕ) (t : ℂ)
    (hN : 2≤N) (ht : t≠0) :
    wardBSASourceDiagonal (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N (A*(N-1)) N (vermaBSAWeight N t+(N:ℂ))=0 := by
  apply (wardBSASourceDiagonal_label_zero_iff A N (A*(N-1)) t hN ht).mpr
  refine ⟨N-1,by omega,?_⟩
  rw [Nat.cast_mul,Nat.cast_sub (by omega : 1≤N),Nat.cast_one]
  ring
end VOA.InverseDS.VirasoroVerma
