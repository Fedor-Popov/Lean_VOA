/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningPolynomial

/-!
# Coefficient gradings of the actual finite screening vector

Auxiliary Laurent exponents keep track of oscillator energy. Multiplication
adds the discrepancy between these two gradings. A second grading counts
beta minus gamma variables. All assertions concern finite polynomials.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Coefficients are Euler eigenvectors with weight given by an additive
auxiliary weight plus a fixed offset. Zero coefficients satisfy every weight. -/
def CoeffGrade {G : Type*} [AddCommGroup G] (w : Fin 3 × ℕ → ℂ)
    (L : G →+ ℂ) (a : ℂ) (P : AddMonoidAlgebra WakFock G) : Prop :=
  ∀ g, Eul w (P g) = (L g+a) • P g

/-- The zero expression has every coefficient grading. -/
theorem CoeffGrade.zero {G : Type*} [AddCommGroup G] (w : Fin 3 × ℕ → ℂ)
    (L : G →+ ℂ) (a : ℂ) : CoeffGrade w L a 0 := by
  intro g
  change Eul w 0 = (L g+a) • (0 : WakFock)
  rw [map_zero,smul_zero]

/-- Adding two expressions with the same grading preserves that grading. -/
theorem CoeffGrade.add {G : Type*} [AddCommGroup G] {w : Fin 3 × ℕ → ℂ}
    {L : G →+ ℂ} {a : ℂ} {P Q : AddMonoidAlgebra WakFock G}
    (hP : CoeffGrade w L a P) (hQ : CoeffGrade w L a Q) :
    CoeffGrade w L a (P+Q) := by
  intro g
  change Eul w (P g+Q g) = (L g+a) • (P g+Q g)
  rw [map_add,hP g,hQ g,smul_add]

/-- A finite sum preserves a common coefficient grading. -/
theorem CoeffGrade.sum {G I : Type*} [AddCommGroup G] {w : Fin 3 × ℕ → ℂ}
    {L : G →+ ℂ} {a : ℂ} (S : Finset I) (P : I → AddMonoidAlgebra WakFock G)
    (h : ∀ i∈S, CoeffGrade w L a (P i)) : CoeffGrade w L a (∑ i∈S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using CoeffGrade.zero w L a
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

/-- A single auxiliary monomial has the grading of its actual oscillator coefficient. -/
theorem CoeffGrade.single {G : Type*} [AddCommGroup G] {w : Fin 3 × ℕ → ℂ}
    {L : G →+ ℂ} {a : ℂ} (g : G) (p : WakFock)
    (h : Eul w p=(L g+a) • p) : CoeffGrade w L a (single g p) := by
  classical
  intro x
  by_cases hx : g=x
  · subst x; simpa using h
  · simp [AddMonoidAlgebra.single_apply,hx]

/-- Multiplication adds offsets, by the actual Euler derivation rule and
finite Laurent convolution. This does not assume any screening Ward equation. -/
theorem CoeffGrade.mul {G : Type*} [AddCommGroup G] {w : Fin 3 × ℕ → ℂ}
    {L : G →+ ℂ} {a b : ℂ} {P Q : AddMonoidAlgebra WakFock G}
    (hP : CoeffGrade w L a P) (hQ : CoeffGrade w L b Q) :
    CoeffGrade w L (a+b) (P*Q) := by
  classical
  intro g
  rw [AddMonoidAlgebra.mul_apply]
  simp only [Finsupp.sum,map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs with hxy
  · rw [Eul_mul,hP x,hQ y,← hxy,map_add]
    simp only [smul_eq_C_mul,map_add]
    ring
  · simp

/-- The multiplicative unit has zero grading offset. -/
theorem CoeffGrade.one {G : Type*} [AddCommGroup G] (w : Fin 3 × ℕ → ℂ)
    (L : G →+ ℂ) : CoeffGrade w L 0 1 := by
  rw [AddMonoidAlgebra.one_def]
  apply CoeffGrade.single
  simp [Eul_one']

/-- A finite product has the sum of its factors' offsets. -/
theorem CoeffGrade.prod {G I : Type*} [AddCommGroup G] {w : Fin 3 × ℕ → ℂ}
    {L : G →+ ℂ} (S : Finset I) (a : I → ℂ) (P : I → AddMonoidAlgebra WakFock G)
    (h : ∀ i∈S, CoeffGrade w L (a i) (P i)) :
    CoeffGrade w L (∑ i∈S, a i) (∏ i∈S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using CoeffGrade.one w L
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi]
      exact (h i (by simp)).mul (ih (fun j hj => h j (by simp [hj])))

/-- Taking a natural power multiplies the offset by that exponent. -/
theorem CoeffGrade.pow {G : Type*} [AddCommGroup G] {w : Fin 3 × ℕ → ℂ}
    {L : G →+ ℂ} {a : ℂ} {P : AddMonoidAlgebra WakFock G}
    (h : CoeffGrade w L a P) (n : ℕ) : CoeffGrade w L (n*a) (P^n) := by
  induction n with
  | zero => simpa using CoeffGrade.one w L
  | succ n ih =>
      convert ih.mul h using 1 <;> simp [pow_succ,Nat.cast_add,add_mul]

/-- Total auxiliary Laurent degree as an additive complex-valued weight. -/
def auxiliaryDegree (r : ℕ) : (Fin r → ℤ) →+ ℂ where
  toFun g := ∑ i, (g i : ℂ)
  map_zero' := by simp
  map_add' g h := by simp [Finset.sum_add_distrib]

/-- A single auxiliary variable has total degree one. -/
theorem auxiliaryDegree_unit (r : ℕ) (i : Fin r) :
    auxiliaryDegree r (unitExponent r i)=1 := by
  classical
  simp [auxiliaryDegree,unitExponent,Pi.single_apply]

/-- Integer multiples of an auxiliary unit have their expected total degree. -/
theorem auxiliaryDegree_smul_unit (r : ℕ) (i : Fin r) (n : ℤ) :
    auxiliaryDegree r (n • unitExponent r i)=n := by
  rw [map_zsmul,auxiliaryDegree_unit]
  simp

/-- A beta creation series has oscillator energy one greater than its
auxiliary degree, term by term. -/
theorem betaFactor_energy (r D : ℕ) (i : Fin r) :
    CoeffGrade wtFn (auxiliaryDegree r) 1 (betaFactor r D i) := by
  apply CoeffGrade.sum
  intro j hj
  apply CoeffGrade.single
  rw [Eul_X,auxiliaryDegree_smul_unit]
  simp [wtFn,show (0 : Fin 3)≠1 by decide]

/-- Each beta series has beta-minus-gamma charge one. -/
theorem betaFactor_charge (r D : ℕ) (i : Fin r) :
    CoeffGrade chFn 0 1 (betaFactor r D i) := by
  apply CoeffGrade.sum
  intro j hj
  apply CoeffGrade.single
  simp [Eul_X,chFn]

/-- The m-th boson power sum has equal oscillator and auxiliary energy. -/
theorem bosonPower_energy (r m : ℕ) (hm : 0<m) :
    CoeffGrade wtFn (auxiliaryDegree r) 0 (bosonPower r m) := by
  apply CoeffGrade.sum
  intro i hi
  apply CoeffGrade.single
  rw [Eul_X,auxiliaryDegree_smul_unit]
  have hm' : ((m-1 : ℕ) : ℂ)+1=m := by exact_mod_cast (Nat.sub_add_cancel hm)
  simp [wtFn,show (2 : Fin 3)≠1 by decide,hm']

/-- Boson creation variables have no beta-minus-gamma charge. -/
theorem bosonPower_charge (r m : ℕ) : CoeffGrade chFn 0 0 (bosonPower r m) := by
  apply CoeffGrade.sum
  intro i hi
  apply CoeffGrade.single
  simp [Eul_X,chFn,show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide]

/-- A constant oscillator coefficient at auxiliary exponent zero has zero offset. -/
theorem constant_grade {G : Type*} [AddCommGroup G] (w : Fin 3 × ℕ → ℂ)
    (L : G →+ ℂ) (z : ℂ) : CoeffGrade w L 0 (single 0 (MvPolynomial.C z)) := by
  apply CoeffGrade.single
  simp [Eul_C']

/-- Finite exponential factors preserve matching oscillator and auxiliary energies. -/
theorem exponentialFactor_energy (r D M m : ℕ) (hm : 0<m) :
    CoeffGrade wtFn (auxiliaryDegree r) 0 (exponentialFactor r D M m) := by
  apply CoeffGrade.sum
  intro ell hell
  convert (constant_grade wtFn (auxiliaryDegree r) _).mul ((bosonPower_energy r m hm).pow ell) using 1 <;> simp

/-- The finite boson exponential has beta-minus-gamma charge zero. -/
theorem exponentialFactor_charge (r D M m : ℕ) :
    CoeffGrade chFn 0 0 (exponentialFactor r D M m) := by
  apply CoeffGrade.sum
  intro ell hell
  convert (constant_grade chFn 0 _).mul ((bosonPower_charge r m).pow ell) using 1 <;> simp

/-- Differences of equally graded expressions preserve the grading. -/
theorem CoeffGrade.sub {G : Type*} [AddCommGroup G] {w : Fin 3 × ℕ → ℂ}
    {L : G →+ ℂ} {a : ℂ} {P Q : AddMonoidAlgebra WakFock G}
    (hP : CoeffGrade w L a P) (hQ : CoeffGrade w L a Q) :
    CoeffGrade w L a (P-Q) := by
  intro g
  change Eul w (P g-Q g) = (L g+a) • (P g-Q g)
  rw [map_sub,hP g,hQ g,smul_sub]

/-- The lifted Vandermonde is the product of ordinary auxiliary differences
with constant oscillator coefficients. -/
theorem delta_product (r : ℕ) : delta r =
    ∏ ij ∈ variablePairs r,
      (single (unitExponent r ij.1) (1 : WakFock) - single (unitExponent r ij.2) 1) := by
  classical
  simp [delta,vandermondeLaurent,map_prod,map_sub]

/-- The auxiliary Vandermonde has degree equal to its number of pairs and
zero oscillator energy, hence the negative pair-count offset. -/
theorem delta_energy (r : ℕ) :
    CoeffGrade wtFn (auxiliaryDegree r) (-(variablePairs r).card : ℂ) (delta r) := by
  rw [delta_product]
  have h := CoeffGrade.prod (variablePairs r) (fun _ => (-1 : ℂ))
    (fun ij => (single (unitExponent r ij.1) (1 : WakFock) - single (unitExponent r ij.2) 1))
    (w := wtFn) (L := auxiliaryDegree r) (by
      intro ij hij
      apply CoeffGrade.sub <;> apply CoeffGrade.single <;>
        simp [Eul_one',auxiliaryDegree_unit])
  simpa using h

/-- The Vandermonde carries no beta-minus-gamma charge. -/
theorem delta_charge (r : ℕ) : CoeffGrade chFn 0 0 (delta r) := by
  rw [delta_product]
  have h := CoeffGrade.prod (variablePairs r) (fun _ => (0 : ℂ))
    (fun ij => (single (unitExponent r ij.1) (1 : WakFock) - single (unitExponent r ij.2) 1))
    (w := chFn) (L := 0) (by
      intro ij hij
      apply CoeffGrade.sub <;> apply CoeffGrade.single <;> simp [Eul_one'])
  simpa using h

/-- Counting both endpoints of each pair gives r(r-1), including ranks
zero and one. This is the degree of the squared Vandermonde. -/
theorem twice_pair_card (r : ℕ) :
    (2 : ℂ)*(variablePairs r).card = (r : ℂ)*((r-1 : ℕ) : ℂ) := by
  have h := congrArg (auxiliaryDegree r) (variablePairs_exponent_sum r)
  simp only [map_sum,map_add,auxiliaryDegree_unit] at h
  simpa [auxiliaryDegree,mul_comm,two_mul] using h

/-- The full integrand's oscillator energy differs from its total auxiliary
degree by r minus the Vandermonde degree. -/
theorem integrand_energy (r q M : ℕ) :
    CoeffGrade wtFn (auxiliaryDegree r)
      ((r : ℂ) - (2*M : ℂ)*(variablePairs r).card) (integrand r q M) := by
  have hb := CoeffGrade.prod Finset.univ (fun _ : Fin r => (1 : ℂ))
    (betaFactor r (r*(q-1))) (fun i _ => betaFactor_energy r _ i)
  have he := CoeffGrade.prod (Finset.range (r*(q-1))) (fun _ => (0 : ℂ))
    (fun m => exponentialFactor r (r*(q-1)) M (m+1))
    (fun m _ => exponentialFactor_energy r _ M _ (by omega))
  have h := ((delta_energy r).pow (2*M)).mul hb |>.mul he
  convert h using 1 <;> simp [integrand,Nat.cast_mul] <;> ring

/-- The r beta factors give the full integrand beta-minus-gamma charge r. -/
theorem integrand_charge (r q M : ℕ) : CoeffGrade chFn 0 (r : ℂ) (integrand r q M) := by
  have hb := CoeffGrade.prod Finset.univ (fun _ : Fin r => (1 : ℂ))
    (betaFactor r (r*(q-1))) (fun i _ => betaFactor_charge r _ i)
  have he := CoeffGrade.prod (Finset.range (r*(q-1))) (fun _ => (0 : ℂ))
    (fun m => exponentialFactor r (r*(q-1)) M (m+1))
    (fun m _ => exponentialFactor_charge r _ M _)
  have h := ((delta_charge r).pow (2*M)).mul hb |>.mul he
  simpa [integrand] using h

/-- The actual finite screening vector has oscillator energy rq. The
positive index assumption is needed to undo the natural subtractions. -/
theorem state_energy (r q M : ℕ) (hq : 0 < q) :
    Dwt (state r q M) = (r*q : ℂ) • state r q M := by
  have h := integrand_energy r q M (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))
  have hn : (r-1)*M+q-1 = (r-1)*M+(q-1) := by omega
  have hc := twice_pair_card r
  have hq' : ((q-1 : ℕ) : ℂ) = (q : ℂ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hs : auxiliaryDegree r (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) +
      ((r : ℂ) - (2*M : ℂ)*(variablePairs r).card) = (r*q : ℂ) := by
    simp only [auxiliaryDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hn,
      Int.cast_natCast,Nat.cast_add,Nat.cast_mul,hq',Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    rw [hq']
    linear_combination -(M : ℂ)*hc
  simpa only [hs] using h

/-- The actual screening vector has beta-minus-gamma charge r. -/
theorem state_charge (r q M : ℕ) :
    Dch (state r q M) = (r : ℂ) • state r q M := by
  simpa only [AddMonoidHom.zero_apply,zero_add] using
    integrand_charge r q M (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))

end
end VOA.Wak.Screening
