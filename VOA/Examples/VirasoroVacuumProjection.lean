/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.InverseDSVirasoroVerma
import VOA.Examples.VirasoroFockConjugation

/-!
# The actual Verma-to-vacuum map and a vacuum survival functional

The highest-weight-zero Verma module maps onto the universal vacuum module.
A Fock evaluation retaining only the first oscillator gives a linear test
for survival: L minus two multiplies this functional by one half, and all
other negative modes kill it. This is not a singular-vector or rigidity
assumption, and says nothing by itself about survival in the simple quotient.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The universal vacuum is an actual highest-weight-zero vector. -/
theorem vacuum_highest (c : ℂ) :
    IsHighestWeightVector (virVacRep c) (vacVec c) c 0 where
  centralCharge := rfl
  pos_annihilate n hn := Lop_vacuum c (by omega)
  zero_acts := by simpa using Lop_vacuum c (n:=0) (by omega)

/-- The canonical representation map M(c,0) to V(c,0), normalized on the
highest vector. It imposes the additional translation-vacuum relation. -/
noncomputable def vacuumProjection (c : ℂ) : Verma c 0 →ₗ[ℂ] VirUniv c :=
  universalMap (virVacRep c) (vacVec c) (vacuum_highest c)

/-- The Verma highest vector maps to the genuine vacuum. -/
@[simp] theorem vacuumProjection_highest (c : ℂ) :
    vacuumProjection c (highestVector c 0)=vacVec c :=
  universalMap_highestVector _ _ _

/-- Projection commutes with every actual Virasoro mode, including the
positive modes used to test a singular state. -/
theorem vacuumProjection_mode (c : ℂ) (n : ℤ) (v : Verma c 0) :
    vacuumProjection c (vermaMode c 0 n v)=Lop c n (vacuumProjection c v) :=
  universalMap_intertwines _ _ _ _ _

/-- The oscillator evaluation sends X0 to one and every higher variable
to zero. As a ring homomorphism it also preserves products and sums. -/
noncomputable def firstOscillatorEval : Fock →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (fun i : ℕ => if i=0 then (1:ℂ) else 0)

/-- The chosen oscillator values are explicit. -/
@[simp] theorem firstOscillatorEval_X (i : ℕ) :
    firstOscillatorEval (MvPolynomial.X i)=if i=0 then 1 else 0 :=
  MvPolynomial.aeval_X _ _

/-- Only the first creation quadratic survives the oscillator evaluation. -/
theorem firstOscillatorEval_creation (i : ℕ) :
    firstOscillatorEval (creationPoly i)=if i=0 then (2:ℂ)⁻¹ else 0 := by
  classical
  by_cases hi : i=0
  · subst i; simp [creationPoly_zero]
  · rw [creationPoly,map_smul,map_sum,if_neg hi]
    have hz : ∑ p ∈ Finset.range (i+1),
        firstOscillatorEval ((MvPolynomial.X p : Fock)*MvPolynomial.X (i-p))=0 := by
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hp0 : p=0
      · subst p; simp [hi]
      · simp [hp0]
    rw [hz,smul_zero]

/-- Every negative Sugawara mode becomes multiplication by its evaluated
vacuum value. The commutator error contains a higher oscillator and vanishes. -/
theorem firstOscillatorEval_Lvir (n : ℕ) (v : Fock) :
    firstOscillatorEval (Lvir 1 (-(n:ℤ)-1) v)=
      firstOscillatorEval (Lvir 1 (-(n:ℤ)-1) 1)*firstOscillatorEval v := by
  induction v using MvPolynomial.induction_on with
  | C a =>
    rw [show MvPolynomial.C a=(a:ℂ) • (1:Fock) by rw [MvPolynomial.smul_eq_C_mul,mul_one],map_smul,map_smul,map_smul]
    simp [smul_eq_mul,mul_comm]
  | add p q hp hq => simp only [map_add,hp,hq,mul_add]
  | mul_X p i hp =>
    rw [mul_comm p, Lvir_neg_X, map_add, map_smul, map_mul, map_mul]
    simp only [firstOscillatorEval_X,show i+n+1≠0 by omega,if_false,zero_mul,smul_zero,zero_add,hp]
    rw [map_mul,firstOscillatorEval_X]
    ring

/-- Background-charge terms also contain higher oscillators, except at
translation where their scalar coefficient is zero. Thus only L minus two
survives, independently of the central charge. -/
theorem firstOscillatorEval_Lld (lam : ℂ) (n : ℕ) (v : Fock) :
    firstOscillatorEval (Lld lam (-(n:ℤ)-1) v)=
      (if n=1 then (2:ℂ)⁻¹ else 0)*firstOscillatorEval v := by
  rw [Lld,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,
    firstOscillatorEval_Lvir,osc_apply_neg 1 (by omega),map_mul]
  have he : (-(-(n:ℤ)-1)-1).toNat=n := by simp
  rw [he,firstOscillatorEval_X]
  cases n with
  | zero => simp [Lvir_one_vacuum]
  | succ n =>
    rw [show (-((n+1:ℕ):ℤ)-1)=-(n:ℤ)-2 by push_cast; ring,
      Lvir_creation_vacuum,firstOscillatorEval_creation]
    simp

/-- A linear scalar test on the ACTUAL universal vacuum module, obtained
by its Fock realization and the first-oscillator evaluation. -/
noncomputable def vacuumSurvival (c : ℂ) : VirUniv c →ₗ[ℂ] ℂ :=
  firstOscillatorEval.toLinearMap.comp (fockMap (exists_lam c).choose_spec)

/-- The survival functional is normalized to one on the vacuum. -/
@[simp] theorem vacuumSurvival_vacuum (c : ℂ) : vacuumSurvival c (vacVec c)=1 := by
  change firstOscillatorEval (fockMap (exists_lam c).choose_spec (negWordVir c []))=1
  rw [fockMap_negWordVir]
  simp [fockWordVir,vacuum]

/-- The survival functional kills translation and every negative mode
other than L minus two, which multiplies it by one half. -/
theorem vacuumSurvival_mode (c : ℂ) (n : ℕ) (v : VirUniv c) :
    vacuumSurvival c (Lop c (-(n:ℤ)-1) v)=
      (if n=1 then (2:ℂ)⁻¹ else 0)*vacuumSurvival c v := by
  unfold vacuumSurvival
  simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,fockMap_Lop]
  exact firstOscillatorEval_Lld _ _ _

/-- Compose the actual quotient map and survival test. A nonzero value
therefore certifies survival in the universal vacuum quotient. -/
noncomputable def vermaVacuumSurvival (c : ℂ) : Verma c 0 →ₗ[ℂ] ℂ :=
  (vacuumSurvival c).comp (vacuumProjection c)

/-- The scalar normalization is already one before quotienting. -/
@[simp] theorem vermaVacuumSurvival_highest (c : ℂ) :
    vermaVacuumSurvival c (highestVector c 0)=1 := by
  simp [vermaVacuumSurvival]

/-- The composed functional obeys the actual mode rule on Verma states. -/
theorem vermaVacuumSurvival_mode (c : ℂ) (n : ℕ) (v : Verma c 0) :
    vermaVacuumSurvival c (vermaMode c 0 (-(n:ℤ)-1) v)=
      (if n=1 then (2:ℂ)⁻¹ else 0)*vermaVacuumSurvival c v := by
  simp only [vermaVacuumSurvival,LinearMap.comp_apply,vacuumProjection_mode,vacuumSurvival_mode]

/-- A nonzero scalar test forces the actual vacuum projection nonzero. -/
theorem vacuumProjection_ne_zero_of_survival (c : ℂ) (v : Verma c 0)
    (hv : vermaVacuumSurvival c v≠0) : vacuumProjection c v≠0 := by
  intro hz
  apply hv
  simp [vermaVacuumSurvival,hz]

end VOA.InverseDS.VirasoroVerma
