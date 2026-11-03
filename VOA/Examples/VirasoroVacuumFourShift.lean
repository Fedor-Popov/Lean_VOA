/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumFourContinuant

/-!
# A finite polynomial certificate for the quartic parameter shift

Two explicit polynomials intertwine the integer continuant recurrences
at p and p+4, with an index shift of six. All certificate identities are
checked by ring normalization in Lean. The coefficient search is not a
trusted input to any theorem.
-/
set_option maxRecDepth 5000

namespace VOA.InverseDS.VirasoroVerma

/-- The quadratic coefficient in the even integer recurrence. -/
noncomputable def fourE (p n : ℂ) : ℂ := 80*n^2+(40-132*p)*n+45*p^2-15*p

/-- The lower quartic coefficient, including its sign. Its terminal zero
occurs one step after the desired singular level. -/
noncomputable def fourC (p n : ℂ) : ℂ :=
  -18*(n-1)*(4*n-p-2)*(4*n-3*p)*(2*n-3*p+1)

/-- The current-coefficient polynomial in the finite parameter-shift
certificate. Its role is specified by the two intertwining identities below. -/
noncomputable def fourA (p n : ℂ) : ℂ :=
  1926211829760 +
  628624834560*p^1 +
  (-2371709030400*p^2) +
  (-747012775680*p^3) +
  803097659520*p^4 +
  175309453440*p^5 +
  (-96761365560*p^6) +
  (-7145749125*p^7) +
  4428675000*p^8 +
  (-307546875*p^9) +
  5334104604672*n^1 +
  4187999379456*n^1*p^1 +
  (-4174961412096*n^1*p^2) +
  (-3446908743168*n^1*p^3) +
  625154474880*n^1*p^4 +
  571802569056*n^1*p^5 +
  (-46172328912*n^1*p^6) +
  (-26109827550*n^1*p^7) +
  2829431250*n^1*p^8 +
  5597412950016*n^2 +
  6735598276608*n^2*p^1 +
  (-1003284596736*n^2*p^2) +
  (-3327563752704*n^2*p^3) +
  (-509826006144*n^2*p^4) +
  318593551968*n^2*p^5 +
  43170750144*n^2*p^6 +
  (-10082944800*n^2*p^7) +
  2813149315072*n^3 +
  4338503516160*n^3*p^1 +
  1299583512576*n^3*p^2 +
  (-887277182976*n^3*p^3) +
  (-446701340160*n^3*p^4) +
  6347408832*n^3*p^5 +
  17243637696*n^3*p^6 +
  702993825792*n^4 +
  1216224866304*n^4*p^1 +
  712874594304*n^4*p^2 +
  59687476992*n^4*p^3 +
  (-63894707712*n^4*p^4) +
  (-13941745920*n^4*p^5) +
  85462941696*n^5 +
  125952712704*n^5*p^1 +
  96995708928*n^5*p^2 +
  33200534016*n^5*p^3 +
  4137951744*n^5*p^4 +
  6933970944*n^6 +
  1070825472*n^6*p^1 +
  110813184*n^6*p^2 +
  4644864*n^6*p^3 +
  899678208*n^7 +
  76677120*n^7*p^1 +
  3538944*n^7*p^2 +
  66060288*n^8 +
  2359296*n^8*p^1 +
  2097152*n^9

/-- The previous-coefficient polynomial in the finite parameter-shift
certificate. Its role is specified by the two intertwining identities below. -/
noncomputable def fourB (p n : ℂ) : ℂ :=
  9159947845632*n^1 +
  (-6012975513600*n^1*p^1) +
  (-11950676361216*n^1*p^2) +
  5592062997504*n^1*p^3 +
  6067520483328*n^1*p^4 +
  (-2169275385600*n^1*p^5) +
  (-1033369817184*n^1*p^6) +
  318839904396*n^1*p^7 +
  44031461490*n^1*p^8 +
  (-17212783500*n^1*p^9) +
  1107168750*n^1*p^10 +
  44842546888704*n^2 +
  (-7131864858624*n^2*p^1) +
  (-55108399030272*n^2*p^2) +
  (-2840684027904*n^2*p^3) +
  24228203632128*n^2*p^4 +
  1536850972800*n^2*p^5 +
  (-3350792069568*n^2*p^6) +
  (-27713664*n^2*p^7) +
  154079704980*n^2*p^8 +
  (-13669843500*n^2*p^9) +
  83195863105536*n^3 +
  24060927688704*n^3*p^1 +
  (-72169741615104*n^3*p^2) +
  (-38532943807488*n^3*p^3) +
  18533800387584*n^3*p^4 +
  8663450276736*n^3*p^5 +
  (-1579375257408*n^3*p^6) +
  (-457449611184*n^3*p^7) +
  66561607440*n^3*p^8 +
  77986055061504*n^4 +
  48610380644352*n^4*p^1 +
  (-26729101688832*n^4*p^2) +
  (-38558505904128*n^4*p^3) +
  (-1850394627072*n^4*p^4) +
  4869470670336*n^4*p^5 +
  419175326592*n^4*p^6 +
  (-163420758144*n^4*p^7) +
  41452303417344*n^5 +
  31635601145856*n^5*p^1 +
  6307117719552*n^5*p^2 +
  (-11181404353536*n^5*p^3) +
  (-4318261009920*n^5*p^4) +
  314247568896*n^5*p^5 +
  212173572096*n^5*p^6 +
  13569769340928*n^6 +
  8411675295744*n^6*p^1 +
  5385257091072*n^6*p^2 +
  20238999552*n^6*p^3 +
  (-694879534080*n^6*p^4) +
  (-136428862464*n^6*p^5) +
  3059417088000*n^7 +
  685286424576*n^7*p^1 +
  780261064704*n^7*p^2 +
  264478887936*n^7*p^3 +
  33047875584*n^7*p^4 +
  531634323456*n^8 +
  (-35311583232*n^8*p^1) +
  1488125952*n^8*p^2 +
  5308416*n^8*p^3 +
  67155001344*n^9 +
  (-2774532096*n^9*p^1) +
  56623104*n^9*p^2 +
  4831838208*n^10 +
  (-94371840*n^10*p^1) +
  150994944*n^11

/-- The harmless quadratic denominator in the parameter-shift formula. -/
noncomputable def fourF (p : ℂ) : ℂ := (3*p+8)*(3*p+4)

/-- The normalization multiplier determined by the two initial equations. -/
noncomputable def fourG (p : ℂ) : ℂ := -3*p*(3*p+7)*(3*p+5)*(3*p+1)*(3*p-1)

/-- The terminal four-step multiplier, factored so its nonvanishing at
positive integer labels can be proved without evaluating any continuant. -/
noncomputable def fourK (p : ℂ) : ℂ :=
  -248832*p^2*(3*p+8)*(3*p+7)^2*(3*p+5)^2*(3*p+4)*(3*p+1)^2*(3*p-1)^2

set_option maxHeartbeats 8000000 in
/-- The first exact polynomial intertwining equation. It matches the
coefficient of the current sequence value in the shifted recurrence. -/
theorem four_intertwine_first (p n : ℂ) :
    fourC p n*(-fourA p (n+1)*fourE p (n+1)+fourB p (n+1)+fourE (p+4) (n+7)*fourA p n)-
      fourC (p+4) (n+7)*fourB p (n-1)=0 := by
  unfold fourA fourB fourC fourE
  ring

set_option maxHeartbeats 8000000 in
/-- The second intertwining equation matches the preceding sequence
value. Together the two equations transport every solution of the recurrence. -/
theorem four_intertwine_second (p n : ℂ) :
    fourC p n*(fourA p (n+1)*fourC p (n+1)+fourE (p+4) (n+7)*fourB p n-
      fourC (p+4) (n+7)*fourA p (n-1))-
      fourC (p+4) (n+7)*fourE p n*fourB p (n-1)=0 := by
  unfold fourA fourB fourC fourE
  ring

/-- The original complex continuant obeys the recurrence with the
quadratic and quartic coefficients just defined. -/
theorem four_Z_step (p : ℂ) (k : ℕ) :
    vacuumFourContinuant p (k+2)=
      -fourE p ((k:ℂ)+2)*vacuumFourContinuant p (k+1)+
      fourC p ((k:ℂ)+2)*vacuumFourContinuant p k := by
  rw [vacuumFourContinuant]
  unfold fourE fourC vacuumFourMiddleNumerator vacuumFourDiagonalNumerator
  ring

set_option maxHeartbeats 8000000 in
/-- The first initial equality fixes the normalization of the shifted
solution at its seventh coefficient. -/
theorem four_shift_base_one (p : ℂ) :
    fourF p*vacuumFourContinuant (p+4) 7=
      fourG p*(fourA p 1*vacuumFourContinuant p 1+fourB p 1*vacuumFourContinuant p 0) := by
  norm_num [vacuumFourContinuant]
  unfold fourF fourG fourA fourB vacuumFourMiddleNumerator vacuumFourDiagonalNumerator
  ring

set_option maxHeartbeats 8000000 in
/-- The second initial equality fixes the next coefficient, completing
the data required to identify two solutions of a second-order recurrence. -/
theorem four_shift_base_two (p : ℂ) :
    fourF p*vacuumFourContinuant (p+4) 8=
      fourG p*(fourA p 2*vacuumFourContinuant p 2+fourB p 2*vacuumFourContinuant p 1) := by
  norm_num [vacuumFourContinuant]
  unfold fourF fourG fourA fourB vacuumFourMiddleNumerator vacuumFourDiagonalNumerator
  ring

set_option maxHeartbeats 8000000 in
/-- At the terminal index the current coefficient factors explicitly. -/
theorem four_A_terminal (p : ℂ) :
    fourA p (3*(p-1)/2)=
      82944*p*(3*p+8)^2*(3*p+7)*(3*p+5)*(3*p+4)^2*(3*p+1)*(3*p-1) := by
  unfold fourA
  ring

set_option maxHeartbeats 8000000 in
/-- The preceding coefficient disappears exactly at terminal resonance.
This is what makes the terminal shift a single product rather than a sum. -/
theorem four_B_terminal (p : ℂ) : fourB p (3*(p-1)/2)=0 := by
  unfold fourB
  ring

/-- Combining the normalization and terminal coefficient gives the
claimed degree-twelve multiplier, with no remaining denominator. -/
theorem four_terminal_multiplier (p : ℂ) :
    fourG p*fourA p (3*(p-1)/2)=fourF p*fourK p := by
  rw [four_A_terminal]
  unfold fourF fourG fourK
  ring

attribute [local irreducible] fourA fourB vacuumFourContinuant

/-- The two polynomial identities transport any four consecutive values
satisfying the original second-order recurrence. The lower coefficient
is retained as a factor so the algebraic statement needs no division. -/
theorem four_intertwine_values (p n x0 x1 x2 x3 : ℂ)
    (hrec : x2= -fourE p n*x1+fourC p n*x0)
    (hnext : x3= -fourE p (n+1)*x2+fourC p (n+1)*x1) :
    fourC p n*(fourA p (n+1)*x3+fourB p (n+1)*x2+
      fourE (p+4) (n+7)*(fourA p n*x2+fourB p n*x1)-
      fourC (p+4) (n+7)*(fourA p (n-1)*x1+fourB p (n-1)*x0))=0 := by
  have h1 := four_intertwine_first p n
  have h2 := four_intertwine_second p n
  linear_combination x2*h1+x1*h2+fourC (p+4) (n+7)*fourB p (n-1)*hrec+
    fourC p n*fourA p (n+1)*hnext

/-- The transformed solution, indexed so its first two values correspond
to indices one and two of the original continuant. -/
noncomputable def fourTransform (p : ℂ) (k : ℕ) : ℂ :=
  fourA p ((k:ℂ)+1)*vacuumFourContinuant p (k+1)+
  fourB p ((k:ℂ)+1)*vacuumFourContinuant p k

/-- The transformed continuant satisfies the shifted recurrence after
multiplication by its explicitly retained lower coefficient. -/
theorem fourTransform_recurrence (p : ℂ) (k : ℕ) :
    fourC p ((k:ℂ)+2)*(fourTransform p (k+2)+
      fourE (p+4) ((k:ℂ)+9)*fourTransform p (k+1)-
      fourC (p+4) ((k:ℂ)+9)*fourTransform p k)=0 := by
  have hn := four_Z_step p (k+1)
  simp only [Nat.cast_add,Nat.cast_one] at hn
  have hh := four_intertwine_values p ((k:ℂ)+2)
    (vacuumFourContinuant p k) (vacuumFourContinuant p (k+1))
    (vacuumFourContinuant p (k+2)) (vacuumFourContinuant p (k+3))
    (four_Z_step p k) (by convert hn using 1 <;> congr 2 <;> ring)
  simpa only [fourTransform,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,
    show k+2+1=k+3 by omega,show k+1+1=k+2 by omega,
    show (k:ℂ)+2+1=(k:ℂ)+3 by ring,
    show (k:ℂ)+1+1=(k:ℂ)+2 by ring,
    show (k:ℂ)+2+7=(k:ℂ)+9 by ring,
    show (k:ℂ)+2-1=(k:ℂ)+1 by ring] using hh

/-- The two initial identities and the recurrence determine every shifted
coefficient up to any index where the lower factors are nonzero. -/
theorem four_shift_scaled (p : ℂ) (M : ℕ)
    (hC : ∀ n : ℕ, 2≤n → n≤M → fourC p n≠0)
    (k : ℕ) (hk : k+1≤M) :
    fourF p*vacuumFourContinuant (p+4) (k+7)=fourG p*fourTransform p k := by
  induction k using Nat.twoStepInduction with
  | zero => simpa [fourTransform] using four_shift_base_one p
  | one => simpa only [fourTransform,Nat.cast_one,show (1:ℂ)+1=2 by norm_num] using four_shift_base_two p
  | more k ih0 ih1 =>
    have ht := fourTransform_recurrence p k
    have hn : fourC p ((k:ℂ)+2)≠0 := by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hC (k+2) (by omega) (by omega)
    have ht' := (mul_eq_zero.mp ht).resolve_left hn
    have hz := four_Z_step (p+4) (k+7)
    simp only [Nat.cast_add,Nat.cast_ofNat,show (k:ℂ)+7+2=(k:ℂ)+9 by ring] at hz
    have ha := ih0 (by omega)
    have hb := ih1 (by omega)
    linear_combination fourF p*hz-fourG p*ht'-fourE (p+4) ((k:ℂ)+9)*hb+
      fourC (p+4) ((k:ℂ)+9)*ha

/-- At resonance the preceding coefficient vanishes, so the general
contiguous identity becomes the factored four-step terminal formula. -/
theorem four_terminal_shift_complex (p : ℂ) (M : ℕ) (hM : 2≤M)
    (hterm : 2*(M:ℂ)=3*(p-1)) (hF : fourF p≠0)
    (hC : ∀ n : ℕ, 2≤n → n≤M → fourC p n≠0) :
    vacuumFourContinuant (p+4) (M+6)=fourK p*vacuumFourContinuant p M := by
  have hh := four_shift_scaled p M hC (M-1) (by omega)
  have hi : M-1+7=M+6 := by omega
  have hj : M-1+1=M := by omega
  have hc : ((M-1:ℕ):ℂ)+1=(M:ℂ) := by exact_mod_cast hj
  simp only [fourTransform,hi,hj,hc] at hh
  have hm : (M:ℂ)=3*(p-1)/2 := by linear_combination hterm/2
  rw [hm,four_B_terminal,zero_mul,add_zero] at hh
  apply (mul_left_cancel₀ hF)
  calc
    _ = fourG p*(fourA p (3*(p-1)/2)*vacuumFourContinuant p M) := hh
    _ = (fourG p*fourA p (3*(p-1)/2))*vacuumFourContinuant p M := by ring
    _ = _ := by rw [four_terminal_multiplier]; ring

/-- For odd positive labels, every lower coefficient needed by the shift
is nonzero before the terminal index. The two odd factors cannot vanish,
and the final factor is strictly negative at these indices. -/
theorem fourC_ne_zero (p M n : ℕ) (hp : 3≤p) (ho : Odd p)
    (hM : 2*M=3*(p-1)) (hn : 2≤n) (hnM : n≤M) : fourC (p:ℂ) (n:ℂ)≠0 := by
  obtain ⟨a,ha⟩ := ho
  have h1 : (n:ℂ)-1≠0 := by
    intro hz
    have he : (n:ℤ)-1=0 := by exact_mod_cast hz
    omega
  have h2 : 4*(n:ℂ)-(p:ℂ)-2≠0 := by
    intro hz
    have he : 4*(n:ℤ)-(p:ℤ)-2=0 := by exact_mod_cast hz
    omega
  have h3 : 4*(n:ℂ)-3*(p:ℂ)≠0 := by
    intro hz
    have he : 4*(n:ℤ)-3*(p:ℤ)=0 := by exact_mod_cast hz
    omega
  have h4 : 2*(n:ℂ)-3*(p:ℂ)+1≠0 := by
    intro hz
    have he : 2*(n:ℤ)-3*(p:ℤ)+1=0 := by exact_mod_cast hz
    omega
  unfold fourC
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) h2) h3) h4

/-- The terminal even index at a natural label. Oddness guarantees that
three times (p minus one) is even, as proved separately below. -/
def fourTerminalIndex (p : ℕ) : ℕ := 3*(p-1)/2

/-- The terminal integer whose nonvanishing controls actual vacuum survival. -/
def fourTerminalInteger (p : ℕ) : ℤ :=
  vacuumFourIntegerContinuant (p:ℤ) (fourTerminalIndex p)

/-- At odd labels the floor division in the terminal index is exact. -/
theorem fourTerminalIndex_eq (p : ℕ) (hp : 3≤p) (ho : Odd p) :
    2*fourTerminalIndex p=3*(p-1) := by
  obtain ⟨a,ha⟩ := ho
  unfold fourTerminalIndex
  omega

/-- Increasing an odd label by four increases its terminal index by six. -/
theorem fourTerminalIndex_step (p : ℕ) (hp : 3≤p) :
    fourTerminalIndex (p+4)=fourTerminalIndex p+6 := by
  unfold fourTerminalIndex
  omega

/-- The exact four-step relation for the actual terminal integers.
All the lower-factor and denominator conditions are discharged arithmetically. -/
theorem fourTerminalInteger_step (p : ℕ) (hp : 3≤p) (ho : Odd p) :
    (fourTerminalInteger (p+4):ℂ)=fourK (p:ℂ)*(fourTerminalInteger p:ℂ) := by
  have hM := fourTerminalIndex_eq p hp ho
  have hM2 : 2≤fourTerminalIndex p := by omega
  have hterm : 2*((fourTerminalIndex p):ℂ)=3*((p:ℂ)-1) := by
    have he : 2*fourTerminalIndex p+3=3*p := by omega
    have he' : 2*((fourTerminalIndex p):ℂ)+3=3*(p:ℂ) := by exact_mod_cast he
    linear_combination he'
  have hF : fourF (p:ℂ)≠0 := by
    unfold fourF
    apply mul_ne_zero
    · exact_mod_cast (by omega : 3*p+8≠0)
    · exact_mod_cast (by omega : 3*p+4≠0)
  have hh := four_terminal_shift_complex p (fourTerminalIndex p) hM2 hterm hF
    (fun n hn hnM => fourC_ne_zero p _ n hp ho hM hn hnM)
  simpa only [fourTerminalInteger,vacuumFourIntegerContinuant_cast,Int.cast_natCast,
    Nat.cast_add,Nat.cast_ofNat,Int.cast_add,Int.cast_ofNat,Int.cast_natCast,fourTerminalIndex_step p hp] using hh

/-- Every factor in the terminal shift multiplier is nonzero at labels
at least three. Its sign is irrelevant to the nonvanishing induction. -/
theorem fourK_ne_zero (p : ℕ) (hp : 3≤p) : fourK (p:ℂ)≠0 := by
  have h0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have h1 : 3*(p:ℂ)+8≠0 := by exact_mod_cast (by omega : 3*p+8≠0)
  have h2 : 3*(p:ℂ)+7≠0 := by exact_mod_cast (by omega : 3*p+7≠0)
  have h3 : 3*(p:ℂ)+5≠0 := by exact_mod_cast (by omega : 3*p+5≠0)
  have h4 : 3*(p:ℂ)+4≠0 := by exact_mod_cast (by omega : 3*p+4≠0)
  have h5 : 3*(p:ℂ)+1≠0 := by exact_mod_cast (by omega : 3*p+1≠0)
  have h6 : 3*(p:ℂ)-1≠0 := by
    intro hz
    have he : 3*(p:ℤ)-1=0 := by exact_mod_cast hz
    omega
  unfold fourK
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h0)) h1)
    (pow_ne_zero 2 h2)) (pow_ne_zero 2 h3)) h4) (pow_ne_zero 2 h5)) (pow_ne_zero 2 h6)

/-- The terminal integer is nonzero for EVERY odd label at least three.
The two base values and the proved four-step product cover both odd residue
classes; no experimental product or finite-testing assumption remains. -/
theorem fourTerminalInteger_ne_zero (p : ℕ) (hp : 3≤p) (ho : Odd p) :
    fourTerminalInteger p≠0 := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases h3 : p=3
    · subst p
      norm_num [fourTerminalInteger,fourTerminalIndex,vacuumFourIntegerContinuant]
    by_cases h5 : p=5
    · subst p
      norm_num [fourTerminalInteger,fourTerminalIndex,vacuumFourIntegerContinuant]
    have hp7 : 7≤p := by obtain ⟨a,ha⟩ := ho; omega
    have ho' : Odd (p-4) := by
      obtain ⟨a,ha⟩ := ho
      exact ⟨a-2,by omega⟩
    have hi := ih (p-4) (by omega) (by omega) ho'
    have hh := fourTerminalInteger_step (p-4) (by omega) ho'
    rw [show p-4+4=p by omega] at hh
    intro hz
    rw [hz,Int.cast_zero] at hh
    have hn : (fourTerminalInteger (p-4):ℂ)≠0 := by exact_mod_cast hi
    exact (mul_ne_zero (fourK_ne_zero (p-4) (by omega)) hn) hh.symm


end VOA.InverseDS.VirasoroVerma
