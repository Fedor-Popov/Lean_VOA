/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionTopGauge

/-!
# A nearest-neighbor array for the actual fusion obstruction

The gauged scalar coefficients obey an undivided recurrence with adjacent
stage indices and one preceding coefficient. On the Kac label curves its
coefficient is exactly t(iA-r)-i(N-1-i). The actual terminal obstruction
will therefore be accessible through an interior array coefficient, without
an unproved normalization product.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- The full normalized scalar coefficient after the formal binomial gauge.
The two indices are BSA stage n and Verma coefficient r. -/
noncomputable def fusionGaugedTop (b t y ell : ℂ) (N : ℕ) (u : ℕ → ℂ) (n r : ℕ) : ℂ :=
  coeff n (bsaGaugeSeries ell*PowerSeries.mk (fun j => fusionTopCoeff b t y N u j r))

/-- The gauge has constant coefficient one, so it preserves the input
sequence at stage zero. -/
@[simp] theorem fusionGaugedTop_zero (b t y ell : ℂ) (N : ℕ) (u : ℕ → ℂ) (r : ℕ) :
    fusionGaugedTop b t y ell N u 0 r=u r := by
  simp [fusionGaugedTop,bsaGaugeSeries,bsaGaugeCoefficient,fusionTopCoeff]

/-- The preceding-coefficient term is the preceding gauged array entry;
there is no such entry at coefficient zero. -/
theorem fusionGaugedTop_previous (b t y ell : ℂ) (N : ℕ) (u : ℕ → ℂ) (n r : ℕ) :
    coeff n (bsaGaugeSeries ell*PowerSeries.mk
      (fusionTopPrevious (fusionTopCoeff b t y N u) r))=
      if 0<r then fusionGaugedTop b t y ell N u n (r-1) else 0 := by
  unfold fusionTopPrevious
  split_ifs
  · rfl
  · have hz : PowerSeries.mk (fun _ : ℕ => (0:ℂ))=0 := by ext; simp
    rw [hz,mul_zero,map_zero]

/-- Every intermediate gauged coefficient satisfies the full undivided
nearest-neighbor equation. No terminal source equation is assumed. -/
theorem fusionGaugedTop_ward (b t y ell : ℂ) (N : ℕ) (u : ℕ → ℂ)
    (hell : ell^2+(t-1)*ell-t*b=0) (n r : ℕ) (hn : n+2<N) :
    ((n:ℂ)+2)*((n:ℂ)+2-(N:ℂ))*fusionGaugedTop b t y ell N u (n+2) r=
      (((n:ℂ)+1)*((n:ℂ)+1-(N:ℂ)+t+2*ell)-fusionConstant b t (y+(r:ℂ)) ell N)*
        fusionGaugedTop b t y ell N u (n+1) r+
      t*(if 0<r then fusionGaugedTop b t y ell N u n (r-1) else 0) := by
  have hh := fusionTopHyper_before b t y ell N u hell (n+2) r hn
  rw [fusionTopHyperOperator_coeff,fusionGaugedTop_previous] at hh
  change (_ : ℂ)-_-_=0 at hh
  change (_ : ℂ)=_+_
  simp only [fusionGaugedTop] at *
  linear_combination hh

/-- The terminal gauged equation retains the exact full scalar source on
the right. It never divides by N(N-N). -/
theorem fusionGaugedTop_terminal (b t y ell : ℂ) (N : ℕ) (u : ℕ → ℂ)
    (hell : ell^2+(t-1)*ell-t*b=0) (hN : 2≤N) (r : ℕ) :
    (((N:ℂ)-1)*(-1+t+2*ell)-fusionConstant b t (y+(r:ℂ)) ell N)*
        fusionGaugedTop b t y ell N u (N-1) r+
      t*(if 0<r then fusionGaugedTop b t y ell N u (N-2) (r-1) else 0)=
      t*fusionTopSum b y (fusionTopCoeff b t y N u) N r := by
  have hh := fusionTopHyper_terminal b t y ell N (by omega) u hell r
  have he : N=(N-2)+2 := by omega
  rw [he,fusionTopHyperOperator_coeff,fusionGaugedTop_previous] at hh
  have hc : ((N-2:ℕ):ℂ)=(N:ℂ)-2 := by exact_mod_cast (Int.ofNat_sub hN)
  have hi : N-2+1=N-1 := by omega
  simp only [← he,hi,hc] at hh
  change (_ : ℂ)=_
  change (_ : ℂ)-_-_=_ at hh
  simp only [fusionGaugedTop] at *
  linear_combination -hh

/-- The gauged coefficient on the label curves is the explicit resonance
factor, with its sign proved from the definitions. -/
theorem fusionLabel_array_coefficient (A N i r : ℕ) (t : ℂ) (ht : t≠0) :
    (i:ℂ)*((i:ℂ)-(N:ℂ)+t+2*fusionLabelGauge (A:ℂ) t)-
      fusionConstant (fusionKacWeight (A:ℂ) 0 t) t
        (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t+(r:ℂ))
        (fusionLabelGauge (A:ℂ) t) N=
      t*((i:ℂ)*(A:ℂ)-(r:ℂ))-(i:ℂ)*((N:ℂ)-1-(i:ℂ)) := by
  unfold fusionLabelGauge fusionConstant fusionKacWeight vermaBSAWeight
  field_simp
  ring


/-- The first gauged stage has no preceding-coefficient coupling. This
supplies the boundary row of the uniform nearest-neighbor recurrence. -/
theorem fusionGaugedTop_first (b t y ell : ℂ) (N : ℕ) (u : ℕ → ℂ)
    (hell : ell^2+(t-1)*ell-t*b=0) (hN : 2≤N) (r : ℕ) :
    (1-(N:ℂ))*fusionGaugedTop b t y ell N u 1 r+
      fusionConstant b t (y+(r:ℂ)) ell N*u r=0 := by
  have hh := fusionTopHyper_before b t y ell N u hell 1 r (by omega)
  unfold fusionTopHyperOperator at hh
  rw [map_sub,fusionHyperOperator_coeff b t (y+(r:ℂ)) ell N 0] at hh
  simp only [mul_assoc,coeff_C_mul,coeff_succ_X_mul,coeff_zero_X_mul,
    mul_zero,sub_zero,Nat.cast_zero,zero_add,zero_mul,zero_sub,one_mul] at hh
  change (1-(N:ℂ))*fusionGaugedTop b t y ell N u 1 r-
    (-fusionConstant b t (y+(r:ℂ)) ell N)*fusionGaugedTop b t y ell N u 0 r=0 at hh
  rw [fusionGaugedTop_zero] at hh
  linear_combination hh

/-- The actual kernel's gauged array. Its initial scalar input is the
proved PBW coordinate sequence of the actual preterminal solution. -/
noncomputable def fusionKernelArray (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N)
    (n r : ℕ) : ℂ :=
  fusionGaugedTop (fusionKacWeight (A:ℂ) 0 t) t
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t)
    (fusionLabelGauge (A:ℂ) t) N (fusionKernelTop A N t him hN) n r

/-- The array begins with the actual input coordinates, so the corner
entry is one. This is a proved normalization, not an assumed seed. -/
@[simp] theorem fusionKernelArray_corner (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    fusionKernelArray A N t him hN 0 0=1 := by
  simp [fusionKernelArray]

/-- The normalized full source vanishes at every actual preterminal
coefficient. The alternating stage sign is nonzero and cancels internally. -/
theorem fusionKernelArray_source_below (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N)
    (r : ℕ) (hr : r<A*(N-1)) :
    fusionTopSum (fusionKacWeight (A:ℂ) 0 t)
      (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t)
      (fusionTopCoeff (fusionKacWeight (A:ℂ) 0 t) t
        (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t) N
        (fusionKernelTop A N t him hN)) N r=0 := by
  have hh := fusionKernelTop_source_below A N t him hN r hr
  rw [wardBSATopSource_normalized] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero N (by norm_num))

/-- The actual top coordinate of the terminal state is a single interior
entry of the gauged array, up to its known alternating stage sign. This
is an exact reduction of nonvanishing, not a nonvanishing assumption. -/
theorem fusionTerminalState_top_eq_array (A N : ℕ) (t : ℂ) (him : t.im≠0)
    (hA : 0<A) (hN : 2≤N) :
    vermaTopCoordinate (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (A*(N-1)) (fusionTerminalState A N t him hN).val=
      (-1:ℂ)^N*fusionKernelArray A N t him hN (N-2) (A*(N-1)-1) := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  rw [fusionTerminalState_top,wardBSATopSource_normalized]
  have hh := fusionGaugedTop_terminal (fusionKacWeight (A:ℂ) 0 t) t
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t)
    (fusionLabelGauge (A:ℂ) t) N (fusionKernelTop A N t him hN)
    (fusionLabelGauge_quadratic (A:ℂ) t ht) hN (A*(N-1))
  have hz : ((N:ℂ)-1)*(-1+t+2*fusionLabelGauge (A:ℂ) t)-
      fusionConstant (fusionKacWeight (A:ℂ) 0 t) t
        (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t+((A*(N-1):ℕ):ℂ))
        (fusionLabelGauge (A:ℂ) t) N=0 := by
    have he := fusionLabel_array_coefficient A N (N-1) (A*(N-1)) t ht
    have hn : ((N-1:ℕ):ℂ)=(N:ℂ)-1 := by exact_mod_cast (Int.ofNat_sub (by omega : 1≤N))
    simp only [hn,Nat.cast_mul] at he ⊢
    linear_combination he
  rw [hz,zero_mul,zero_add,if_pos (Nat.mul_pos hA (by omega : 0<N-1))] at hh
  exact congrArg (fun z : ℂ => (-1:ℂ)^N*z) ((mul_left_cancel₀ ht hh).symm)


/-- The first actual array row is fixed by its input coordinate, with
coefficient t*r. It is valid for every coefficient index. -/
theorem fusionKernelArray_first (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) (r : ℕ) :
    ((N:ℂ)-1)*fusionKernelArray A N t him hN 1 r=
      t*(r:ℂ)*fusionKernelArray A N t him hN 0 r := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  have hh := fusionGaugedTop_first (fusionKacWeight (A:ℂ) 0 t) t
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t)
    (fusionLabelGauge (A:ℂ) t) N (fusionKernelTop A N t him hN)
    (fusionLabelGauge_quadratic (A:ℂ) t ht) hN r
  have hc := fusionLabel_array_coefficient A N 0 r t ht
  norm_num only [Nat.cast_zero,zero_mul,zero_sub,mul_zero,sub_zero] at hc
  unfold fusionKernelArray
  rw [fusionGaugedTop_zero]
  linear_combination -hh-hc*fusionKernelTop A N t him hN r

/-- The interior actual array equations have the explicit Kac resonance
coefficient. Only adjacent stages and the preceding coefficient occur. -/
theorem fusionKernelArray_ward (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N)
    (n r : ℕ) (hn : n+2<N) :
    ((n:ℂ)+2)*((n:ℂ)+2-(N:ℂ))*fusionKernelArray A N t him hN (n+2) r=
      (t*(((n:ℂ)+1)*(A:ℂ)-(r:ℂ))-((n:ℂ)+1)*((N:ℂ)-2-(n:ℂ)))*
        fusionKernelArray A N t him hN (n+1) r+
      t*(if 0<r then fusionKernelArray A N t him hN n (r-1) else 0) := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  have hh := fusionGaugedTop_ward (fusionKacWeight (A:ℂ) 0 t) t
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t)
    (fusionLabelGauge (A:ℂ) t) N (fusionKernelTop A N t him hN)
    (fusionLabelGauge_quadratic (A:ℂ) t ht) n r hn
  have hc := fusionLabel_array_coefficient A N (n+1) r t ht
  push_cast at hc
  unfold fusionKernelArray
  linear_combination hh+hc*fusionGaugedTop (fusionKacWeight (A:ℂ) 0 t) t
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t)
    (fusionLabelGauge (A:ℂ) t) N (fusionKernelTop A N t him hN) (n+1) r

/-- At every preterminal coefficient, the last array row is an exact
compatibility equation. The actual zero source supplies its right-hand side. -/
theorem fusionKernelArray_last_before (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N)
    (r : ℕ) (hr : r<A*(N-1)) :
    (((A*(N-1):ℕ):ℂ)-(r:ℂ))*fusionKernelArray A N t him hN (N-1) r+
      (if 0<r then fusionKernelArray A N t him hN (N-2) (r-1) else 0)=0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  have hh := fusionGaugedTop_terminal (fusionKacWeight (A:ℂ) 0 t) t
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t)
    (fusionLabelGauge (A:ℂ) t) N (fusionKernelTop A N t him hN)
    (fusionLabelGauge_quadratic (A:ℂ) t ht) hN r
  rw [fusionKernelArray_source_below A N t him hN r hr,mul_zero] at hh
  have hc := fusionLabel_array_coefficient A N (N-1) r t ht
  have hn : ((N-1:ℕ):ℂ)=(N:ℂ)-1 := by exact_mod_cast (Int.ofNat_sub (by omega : 1≤N))
  simp only [hn] at hc
  apply (mul_eq_zero.mp (show t*(_)=0 from ?_)).resolve_left ht
  unfold fusionKernelArray
  simp only [Nat.cast_mul,hn]
  linear_combination hh-hc*fusionGaugedTop (fusionKacWeight (A:ℂ) 0 t) t
    (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t-vermaBSAWeight N t)
    (fusionLabelGauge (A:ℂ) t) N (fusionKernelTop A N t him hN) (N-1) r

/-- Along coefficient zero, the gauged actual input is the first basis
vector: the corner is one and all positive stages before N vanish. -/
theorem fusionKernelArray_initial_column (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N)
    (n : ℕ) (hn : n<N) : fusionKernelArray A N t him hN n 0=if n=0 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_ne_zero,if_false]
      cases n with
      | zero =>
        have hh := fusionKernelArray_first A N t him hN 0
        simp only [Nat.cast_zero,mul_zero,zero_mul] at hh
        exact (mul_eq_zero.mp hh).resolve_left (by
          intro hz
          have he : (N:ℤ)-1=0 := by exact_mod_cast hz
          omega)
      | succ n =>
        have hh := fusionKernelArray_ward A N t him hN n 0 (by omega)
        rw [ih (n+1) (by omega) (by omega)] at hh
        simp only [Nat.succ_ne_zero,if_false,mul_zero,show ¬0<(0:ℕ) by omega,add_zero] at hh
        apply (mul_eq_zero.mp hh).resolve_left
        apply mul_ne_zero
        · exact_mod_cast (by omega : n+2≠0)
        · intro hz
          have he : (n:ℤ)+2-(N:ℤ)=0 := by exact_mod_cast hz
          omega

end VOA.InverseDS.VirasoroVerma
