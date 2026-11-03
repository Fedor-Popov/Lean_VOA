/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeIntermediateNorm

/-!
# The normalized scalar Ward recurrence for q=3

After a scalar change of parameter a=2/t-1, the actual intermediate norms
satisfy a cubic-denominator recurrence with a quadratic convolution kernel.
The terminal residual is defined separately, without dividing by its zero
diagonal. Its nonvanishing and its comparison to the actual norm derivative
are not asserted here.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The normalized quadratic convolution kernel in the intermediate norm
recurrence. Both factors come from actual source and Ward multipliers. -/
noncomputable def minimalThreeWardKernel (a : ℂ) (r j : ℕ) : ℂ :=
  (a*((r:ℂ)+2)-(a+2)*(j:ℂ))*(a*((r:ℂ)-1)-(a-1)*(j:ℂ))

/-- The cubic diagonal has roots zero, a, and 3a+1 in the level index.
This is exact algebra in the actual diagonal, with t nonzero. -/
theorem threeStateDiagonal_vacuum_factor (t : ℂ) (ht : t≠0) (r : ℕ) :
    threeStateDiagonal 0 (vermaBSAWeight 3 t) t (vermaBSAWeight 3 t) r =
      (t^2/4)*(r:ℂ)*((r:ℂ)-vermaBSAWeight 3 t)*((r:ℂ)-3*vermaBSAWeight 3 t-1) := by
  unfold threeStateDiagonal vermaBSAWeight
  norm_num
  field_simp
  ring

/-- The actual source coefficient multiplied by its adjoint Ward scalar
is exactly the normalized kernel times t/2. -/
theorem threeStateCoefficient_ward_factor (t : ℂ) (ht : t≠0) (r j : ℕ) :
    threeStateCoefficient 0 (vermaBSAWeight 3 t) t (vermaBSAWeight 3 t) r j *
      ((j:ℂ)+((r:ℂ)-(j:ℂ)-1)*vermaBSAWeight 3 t) =
      (t/2)*minimalThreeWardKernel (vermaBSAWeight 3 t) r j := by
  unfold threeStateCoefficient minimalThreeWardKernel vermaBSAWeight
  norm_num
  field_simp
  ring

/-- The field weight is 2p/3-1 at the q=3 rational parameter. -/
theorem minimalThree_field_weight (p : ℕ) (hp : 2≤p) :
    vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))=2*(p:ℂ)/3-1 := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  unfold vermaBSAWeight
  norm_num
  field_simp
  ring

/-- The terminal zero of the cubic is the actual first singular level. -/
theorem minimalThree_terminal_index (p : ℕ) (hp : 2≤p) :
    3*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+1=(((p-1)*2:ℕ):ℂ) := by
  rw [minimalThree_field_weight p hp]
  have hs : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by exact_mod_cast Int.ofNat_sub (by omega : 1≤p)
  push_cast
  rw [hs]
  ring

/-- The proved ACTUAL norms satisfy the normalized scalar recurrence at
every preterminal index. This is the finite recurrence needed for a
subsequent generating-function calculation. -/
theorem minimalThreeNormCoefficient_scaled_recursion (p : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) (r : ℕ) (hr : r<(p-1)*2) :
    (r:ℂ)*((r:ℂ)-vermaBSAWeight 3 ((3:ℂ)/(p:ℂ)))*
      ((r:ℂ)-3*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))-1)*minimalThreeNormCoefficient p r+
    (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+1)*
      ∑ j : Fin r, minimalThreeWardKernel (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) r j *
        minimalThreeNormCoefficient p j=0 := by
  have hh := minimalThree_actual_norm_recursion p hp hcop r hr
  rw [← minimalThreeNormCoefficient_eq_norm p hp hcop r hr] at hh
  have hi (j : Fin r) := (minimalThreeNormCoefficient_eq_norm p hp hcop j (by omega)).symm
  simp only [hi] at hh
  have ht := minimal_three_parameter_ne_zero p (by omega)
  rw [threeStateDiagonal_vacuum_factor _ ht] at hh
  simp_rw [threeStateCoefficient_ward_factor _ ht] at hh
  simp only [mul_assoc] at hh
  rw [← Finset.mul_sum] at hh
  have hc : (((3:ℂ)/(p:ℂ))^2/4)*(vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+1)=
      ((3:ℂ)/(p:ℂ))/2 := by
    unfold vermaBSAWeight
    norm_num
    field_simp
    ring
  have he : (((3:ℂ)/(p:ℂ))^2/4)*
      ((r:ℂ)*((r:ℂ)-vermaBSAWeight 3 ((3:ℂ)/(p:ℂ)))*
        ((r:ℂ)-3*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))-1)*minimalThreeNormCoefficient p r+
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+1)*
        ∑ j : Fin r, minimalThreeWardKernel (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) r j *
          minimalThreeNormCoefficient p j)=0 := by
    rw [mul_add,← mul_assoc _ (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+1),hc]
    simpa only [mul_assoc] using hh
  exact (mul_eq_zero.mp he).resolve_left (div_ne_zero (pow_ne_zero _ ht) (by norm_num))

/-- Reindexing by the mode distance k exposes the kernel's quadratic
convolution form, useful for deriving its finite differential equation. -/
theorem minimalThreeWardKernel_distance (a : ℂ) (j k : ℕ) :
    minimalThreeWardKernel a (j+k) j =
      a^2*((k:ℂ)^2+(k:ℂ)-2)+a*(4-(k:ℂ))*(j:ℂ)-2*(j:ℂ)^2 := by
  unfold minimalThreeWardKernel
  push_cast
  ring

/-- The undivided terminal residual of the normalized scalar recurrence.
Its diagonal vanishes, so it is kept as a finite sum rather than defining
an invalid terminal coefficient. This is not yet the norm derivative. -/
noncomputable def minimalThreeNormResidual (p : ℕ) : ℂ :=
  (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+1)*
    ∑ j : Fin ((p-1)*2), minimalThreeWardKernel (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) ((p-1)*2) j *
      minimalThreeNormCoefficient p j

end VOA.InverseDS.VirasoroVerma
