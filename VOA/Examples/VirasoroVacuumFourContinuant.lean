/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumFusionFour

/-!
# Clearing the quartic vacuum recurrence

At the vacuum specialization t=4/p, both incoming and field weights are
15p/16-3/2. The actual source has an explicit quartic diagonal and quadratic
middle coefficient. Clearing the denominators gives a finite continuant
with integer coefficients when p is an integer. The terminal source is
exactly a scaled continuant, not merely an experimentally related scalar.
Nonvanishing of that continuant at the minimal-model terminal index remains
an ordinary algebraic problem; nothing here assumes or proves it.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The common incoming and field weight for the seed-four vacuum
specialization. The parameter is written as p so that t=4/p. -/
noncomputable def vacuumFourWeight (p : ℂ) : ℂ := 15*p/16-3/2

/-- The quartic numerator of the actual source diagonal. Its four roots
are the exact resonances, including zero and the terminal level 3(p-1). -/
noncomputable def vacuumFourDiagonalNumerator (p r : ℂ) : ℂ :=
  -4*r*(2*r-p+2)*(2*r-3*p+4)*(r-3*p+3)

/-- The quadratic numerator of the two-level-earlier coefficient after
multiplication by 9p squared. It can cancel against the other source terms. -/
noncomputable def vacuumFourMiddleNumerator (p r : ℂ) : ℂ :=
  20*r^2+(20-66*p)*r+45*p^2-15*p

set_option maxHeartbeats 2000000 in
/-- The finite BSA diagonal is exactly the displayed quartic polynomial
with denominator 9p cubed. No root classification is assumed in this calculation. -/
theorem vacuumFour_diagonal_closed (p : ℂ) (hp : p≠0) (r : ℕ) :
    9*p^3*wardBSASourceDiagonal 0 (vacuumFourWeight p) (4/p) 4 r 4
      (vacuumFourWeight p+4)=vacuumFourDiagonalNumerator p r := by
  simp only [wardBSASourceDiagonal,Fin.sum_univ_four]
  iterate 5
    norm_num [wardCreationDiagonal,wardBSADiagonal]
    try simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  unfold vacuumFourWeight vacuumFourDiagonalNumerator
  field_simp
  <;> ring

/-- The actual middle coefficient has the explicit quadratic numerator.
This and the diagonal formula remove every hidden finite BSA sum. -/
theorem vacuumFour_middle_closed (p : ℂ) (hp : p≠0) (r : ℕ) :
    9*p^2*vacuumFourSubdiagonal (vacuumFourWeight p) (4/p) (vacuumFourWeight p) r=
      vacuumFourMiddleNumerator p r := by
  unfold vacuumFourSubdiagonal vacuumFourWeight vacuumFourMiddleNumerator
  field_simp
  <;> ring

/-- The whole actual scalar source, with its common denominator cleared.
The equality retains both earlier coefficients, so no cancellation is lost. -/
theorem vacuumFour_source_cleared (p : ℂ) (hp : p≠0) (u : ℕ → ℂ) (r : ℕ) :
    9*p^2*wardBSAVacuumSource (vacuumFourWeight p) (4/p) (vacuumFourWeight p) 4 4 u (r+4)=
      (vacuumFourDiagonalNumerator p (r+4)/p)*u (r+4)+
      vacuumFourMiddleNumerator p (r+4)*u (r+2)-(9*p/4)*u r := by
  have hd := vacuumFour_diagonal_closed p hp (r+4)
  have he := vacuumFour_middle_closed p hp (r+4)
  have hd' : 9*p^2*wardBSASourceDiagonal 0 (vacuumFourWeight p) (4/p) 4 (r+4) 4
      (vacuumFourWeight p+4)=vacuumFourDiagonalNumerator p (r+4)/p := by
    apply (eq_div_iff hp).mpr
    push_cast at hd
    linear_combination hd
  push_cast at he
  rw [wardBSAVacuumSource_four]
  calc
    _ = (9*p^2*wardBSASourceDiagonal 0 (vacuumFourWeight p) (4/p) 4 (r+4) 4
        (vacuumFourWeight p+4))*u (r+4)+
        (9*p^2*vacuumFourSubdiagonal (vacuumFourWeight p) (4/p) (vacuumFourWeight p) (r+4))*u (r+2)-
        (9*p/4)*u r := by field_simp; ring
    _ = _ := by rw [hd',he]

/-- The initial even equation has only one earlier coefficient. Together
with the full recurrence it fixes the normalized finite scalar sequence. -/
theorem vacuumFour_source_two_cleared (p : ℂ) (hp : p≠0) (u : ℕ → ℂ) :
    9*p^2*wardBSAVacuumSource (vacuumFourWeight p) (4/p) (vacuumFourWeight p) 4 4 u 2=
      (vacuumFourDiagonalNumerator p 2/p)*u 2+vacuumFourMiddleNumerator p 2*u 0 := by
  have hd := vacuumFour_diagonal_closed p hp 2
  have he := vacuumFour_middle_closed p hp 2
  norm_num only [Nat.cast_ofNat] at hd he
  have hd' : 9*p^2*wardBSASourceDiagonal 0 (vacuumFourWeight p) (4/p) 4 2 4
      (vacuumFourWeight p+4)=vacuumFourDiagonalNumerator p 2/p := by
    apply (eq_div_iff hp).mpr
    linear_combination hd
  rw [wardBSAVacuumSource_four_two]
  linear_combination u 2*hd'+u 0*he

/-- A single even-level diagonal after multiplying the source by 9p
squared. Products of these factors clear the earlier recursion divisions. -/
noncomputable def vacuumFourStep (p : ℂ) (k : ℕ) : ℂ :=
  vacuumFourDiagonalNumerator p (2*(k:ℂ))/p

/-- The product of the first k cleared diagonal factors. It is defined
without assuming any factor is nonzero. -/
noncomputable def vacuumFourScale (p : ℂ) : ℕ → ℂ
  | 0 => 1
  | k+1 => vacuumFourScale p k*vacuumFourStep p (k+1)

/-- The division-free continuant for the even vacuum coefficients.
Its coefficients are integer polynomials in p; only earlier values occur. -/
noncomputable def vacuumFourContinuant (p : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => -vacuumFourMiddleNumerator p 2
  | k+2 => -vacuumFourMiddleNumerator p (2*((k:ℂ)+2))*vacuumFourContinuant p (k+1)+
      (9/4)*vacuumFourDiagonalNumerator p (2*((k:ℂ)+1))*vacuumFourContinuant p k

/-- Although written with 9/4, the lower continuant multiplier is an
integer polynomial: its apparent denominator cancels the diagonal's factor four. -/
theorem vacuumFour_continuant_lower (p : ℂ) (k : ℕ) :
    (9/4)*vacuumFourDiagonalNumerator p (2*(k:ℂ))=
      -18*(k:ℂ)*(4*(k:ℂ)-p+2)*(4*(k:ℂ)-3*p+4)*(2*(k:ℂ)-3*p+3) := by
  unfold vacuumFourDiagonalNumerator
  ring

/-- Multiplying a sequence satisfying the actual cleared recurrence by
its diagonal product gives the continuant. The proof uses no division by
an intermediate diagonal and remains valid even when one vanishes. -/
theorem vacuumFourContinuant_eq_scaled (p : ℂ) (hp : p≠0) (u : ℕ → ℂ)
    (M : ℕ) (h0 : u 0=1)
    (h1 : 1<M → vacuumFourStep p 1*u 1+vacuumFourMiddleNumerator p 2*u 0=0)
    (hs : ∀ k : ℕ, k+2<M →
      vacuumFourStep p (k+2)*u (k+2)+
      vacuumFourMiddleNumerator p (2*((k:ℂ)+2))*u (k+1)-(9*p/4)*u k=0)
    (k : ℕ) (hk : k<M) :
    vacuumFourContinuant p k=vacuumFourScale p k*u k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [vacuumFourContinuant,vacuumFourScale,h0]
  | one =>
    have hh := h1 hk
    simp only [vacuumFourContinuant,vacuumFourScale,one_mul,h0,mul_one] at *
    linear_combination -hh
  | more k ih0 ih1 =>
    rw [vacuumFourContinuant,ih0 (by omega),ih1 (by omega)]
    have hh := hs k hk
    have hd : (9*p/4)*vacuumFourStep p (k+1)=
        (9/4)*vacuumFourDiagonalNumerator p (2*((k:ℂ)+1)) := by
      unfold vacuumFourStep
      push_cast
      field_simp
    simp only [vacuumFourScale]
    linear_combination -(vacuumFourScale p k*vacuumFourStep p (k+1))*hh-
      vacuumFourScale p k*u k*hd

/-- At the last equation the undivided source, multiplied by all earlier
cleared diagonals, is the negative continuant. This is the precise finite
scalar obstruction; its nonvanishing is not inferred from the recurrence. -/
theorem vacuumFourContinuant_terminal (p : ℂ) (hp : p≠0) (u : ℕ → ℂ) (k : ℕ)
    (h0 : u 0=1)
    (h1 : 1<k+2 → vacuumFourStep p 1*u 1+vacuumFourMiddleNumerator p 2*u 0=0)
    (hs : ∀ j : ℕ, j+2<k+2 →
      vacuumFourStep p (j+2)*u (j+2)+
      vacuumFourMiddleNumerator p (2*((j:ℂ)+2))*u (j+1)-(9*p/4)*u j=0) :
    vacuumFourScale p (k+1)*
      (vacuumFourMiddleNumerator p (2*((k:ℂ)+2))*u (k+1)-(9*p/4)*u k)=
      -vacuumFourContinuant p (k+2) := by
  have hka := vacuumFourContinuant_eq_scaled p hp u (k+2) h0 h1 hs k (by omega)
  have hkb := vacuumFourContinuant_eq_scaled p hp u (k+2) h0 h1 hs (k+1) (by omega)
  rw [vacuumFourContinuant,hka,hkb]
  have hd : (9*p/4)*vacuumFourStep p (k+1)=
      (9/4)*vacuumFourDiagonalNumerator p (2*((k:ℂ)+1)) := by
    unfold vacuumFourStep
    push_cast
    field_simp
  simp only [vacuumFourScale]
  linear_combination -(vacuumFourScale p k*u k)*hd

/-- An entirely integer version of the continuant. At integer labels it
can be computed with exact arithmetic without forming any rational coefficients. -/
def vacuumFourIntegerContinuant (p : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => -(80+(40-132*p)+45*p^2-15*p)
  | k+2 => -(80*((k:ℤ)+2)^2+(40-132*p)*((k:ℤ)+2)+45*p^2-15*p)*
      vacuumFourIntegerContinuant p (k+1)-
      18*((k:ℤ)+1)*(4*((k:ℤ)+1)-p+2)*(4*((k:ℤ)+1)-3*p+4)*
        (2*((k:ℤ)+1)-3*p+3)*vacuumFourIntegerContinuant p k

/-- The integer recurrence is exactly the complex continuant, not a
numerical approximation to it. This allows arithmetic certificates to target
ordinary integers while retaining the actual source interpretation. -/
theorem vacuumFourIntegerContinuant_cast (p : ℤ) (k : ℕ) :
    (vacuumFourIntegerContinuant p k : ℂ)=vacuumFourContinuant p k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [vacuumFourIntegerContinuant,vacuumFourContinuant]
  | one => simp only [vacuumFourIntegerContinuant,vacuumFourContinuant]
           push_cast
           unfold vacuumFourMiddleNumerator
           ring
  | more k ih0 ih1 =>
    simp only [vacuumFourIntegerContinuant,vacuumFourContinuant]
    push_cast
    rw [ih0,ih1]
    unfold vacuumFourMiddleNumerator vacuumFourDiagonalNumerator
    ring

/-- At its terminal vacuum level the quartic diagonal is zero for every
parameter. This identity records resonance without dividing by that factor. -/
theorem vacuumFourDiagonalNumerator_terminal (p : ℂ) :
    vacuumFourDiagonalNumerator p (3*(p-1))=0 := by
  unfold vacuumFourDiagonalNumerator
  ring

/-- The normalized actual even source at terminal resonance is exactly
controlled by the continuant. Only the earlier source equations are used;
no terminal nonvanishing, singular-vector normalization, or norm assertion
is added as a hypothesis. -/
theorem vacuumFourContinuant_actual_terminal (p : ℂ) (hp : p≠0) (u : ℕ → ℂ) (k : ℕ)
    (hterm : 2*((k:ℂ)+2)=3*(p-1)) (h0 : u 0=1)
    (hbelow : ∀ j : ℕ, 0<j → j<k+2 →
      wardBSAVacuumSource (vacuumFourWeight p) (4/p) (vacuumFourWeight p) 4 4 u (2*j)=0) :
    (9*p^2)*vacuumFourScale p (k+1)*
      wardBSAVacuumSource (vacuumFourWeight p) (4/p) (vacuumFourWeight p) 4 4 u (2*(k+2))=
      -vacuumFourContinuant p (k+2) := by
  let v : ℕ → ℂ := fun j => u (2*j)
  have hv0 : v 0=1 := by simpa [v] using h0
  have hv1 : 1<k+2 → vacuumFourStep p 1*v 1+vacuumFourMiddleNumerator p 2*v 0=0 := by
    intro hk
    have hh := vacuumFour_source_two_cleared p hp u
    rw [hbelow 1 (by omega) hk] at hh
    simpa [v,vacuumFourStep] using hh.symm
  have hvs : ∀ j : ℕ, j+2<k+2 →
      vacuumFourStep p (j+2)*v (j+2)+
      vacuumFourMiddleNumerator p (2*((j:ℂ)+2))*v (j+1)-(9*p/4)*v j=0 := by
    intro j hj
    have hh := vacuumFour_source_cleared p hp u (2*j)
    have hi : 2*j+4=2*(j+2) := by omega
    have hi' : 2*j+2=2*(j+1) := by omega
    rw [hi,hbelow (j+2) (by omega) hj] at hh
    simp only [mul_zero] at hh
    have hjc : (2:ℂ)*(j:ℂ)+4=2*((j:ℂ)+2) := by ring
    simpa only [v,vacuumFourStep,hi',Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hjc] using hh.symm
  have hc := vacuumFourContinuant_terminal p hp v k hv0 hv1 hvs
  have hh := vacuumFour_source_cleared p hp u (2*k)
  have hi : 2*k+4=2*(k+2) := by omega
  have hi' : 2*k+2=2*(k+1) := by omega
  have hz : vacuumFourDiagonalNumerator p ((2*k:ℕ)+4)=0 := by
    have he : ((2*k:ℕ):ℂ)+4=3*(p-1) := by push_cast; linear_combination hterm
    rw [he,vacuumFourDiagonalNumerator_terminal]
  rw [hz,zero_div,zero_mul,zero_add,hi,hi'] at hh
  change vacuumFourScale p (k+1)*
    (vacuumFourMiddleNumerator p (2*((k:ℂ)+2))*u (2*(k+1))-(9*p/4)*u (2*k))=_ at hc
  have he : ((2*k:ℕ):ℂ)+4=2*((k:ℂ)+2) := by push_cast; ring
  rw [he] at hh
  linear_combination vacuumFourScale p (k+1)*hh+hc

/-- The same terminal identity for an actual Verma level sequence, after
applying the genuine vacuum survival functional. Earlier vector equations
imply the required scalar equations by linearity. -/
theorem vacuumFourContinuant_operator_terminal (c p : ℂ) (hp : p≠0)
    (f : wardSequenceSpace c 0) (k : ℕ) (hterm : 2*((k:ℂ)+2)=3*(p-1))
    (h0 : vermaVacuumSurvival c (f.val 0)=1)
    (hbelow : ∀ j : ℕ, 0<j → j<k+2 →
      (wardSourceAt c 0 (vacuumFourWeight p) (4/p) (vacuumFourWeight p) 4 f).val (2*j)=0) :
    (9*p^2)*vacuumFourScale p (k+1)*
      vermaVacuumSurvival c
        ((wardSourceAt c 0 (vacuumFourWeight p) (4/p) (vacuumFourWeight p) 4 f).val (2*(k+2)))=
      -vacuumFourContinuant p (k+2) := by
  rw [wardSourceAt_vacuum]
  apply vacuumFourContinuant_actual_terminal p hp _ k hterm h0
  intro j hj hjk
  have hh := congrArg (vermaVacuumSurvival c) (hbelow j hj hjk)
  simpa only [wardSourceAt_vacuum,map_zero] using hh

/-- A nonzero integer continuant certifies survival of the actual terminal
source in the vacuum module. This criterion still requires that explicit
integer to be proved nonzero; it makes no assertion about a norm derivative. -/
theorem vacuumFour_terminal_ne_zero_of_integer (c : ℂ) (p : ℤ)
    (hp : (p:ℂ)≠0) (f : wardSequenceSpace c 0) (k : ℕ)
    (hterm : 2*((k:ℂ)+2)=3*((p:ℂ)-1))
    (h0 : vermaVacuumSurvival c (f.val 0)=1)
    (hbelow : ∀ j : ℕ, 0<j → j<k+2 →
      (wardSourceAt c 0 (vacuumFourWeight p) (4/(p:ℂ)) (vacuumFourWeight p) 4 f).val (2*j)=0)
    (hz : vacuumFourIntegerContinuant p (k+2)≠0) :
    vermaVacuumSurvival c
      ((wardSourceAt c 0 (vacuumFourWeight p) (4/(p:ℂ)) (vacuumFourWeight p) 4 f).val (2*(k+2)))≠0 := by
  intro he
  have hh := vacuumFourContinuant_operator_terminal c p hp f k hterm h0 hbelow
  rw [he,mul_zero,← vacuumFourIntegerContinuant_cast] at hh
  apply hz
  have hz' : (vacuumFourIntegerContinuant p (k+2):ℂ)=0 := by linear_combination hh
  exact_mod_cast hz'

end VOA.InverseDS.VirasoroVerma
