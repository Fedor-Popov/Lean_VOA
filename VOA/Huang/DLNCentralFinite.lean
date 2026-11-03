import VOA.Huang.DLNCommutatorBridge
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Finiteness of the relative central quotient

Schur's theorem replaces induced representations: a central-by-finite group
has finite derived subgroup. The level-12 character theorem then makes the
entire relative central quotient finite. No congruence of that quotient is
asserted here.
-/

namespace VOA.Huang.DLNLifting

open VOA.Huang.DLN CongruenceSubgroup
open scoped commutatorElement

private theorem commutator_eq_of_center_coset {G : Type*} [Group G]
    {a b : G} (h : (QuotientGroup.mk a : G ⧸ Subgroup.center G) =
      QuotientGroup.mk b) (c : G) : ⁅a, c⁆ = ⁅b, c⁆ := by
  have hz : a⁻¹ * b ∈ Subgroup.center G := QuotientGroup.leftRel_apply.mp (Quotient.exact h)
  have hc : Commute (a⁻¹ * b) c :=
    (Subgroup.mem_center_iff.mp hz c).symm
  have hb : b = a * (a⁻¹ * b) := by group
  rw [hb, commutatorElement_mul_left_eq_conj_mul, hc.commutator_eq]
  simp

/-- A group with finite quotient by its center has finitely many commutators. -/
theorem finite_commutatorSet_of_finiteIndex_center {G : Type*} [Group G]
    [(Subgroup.center G).FiniteIndex] : Finite (commutatorSet G) := by
  classical
  let f : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) → commutatorSet G :=
    fun p => ⟨⁅p.1.out, p.2.out⁆, commutator_mem_commutatorSet _ _⟩
  apply Finite.of_surjective f
  rintro ⟨x, a, b, rfl⟩
  refine ⟨(QuotientGroup.mk a, QuotientGroup.mk b), Subtype.ext ?_⟩
  change ⁅_, _⁆ = ⁅a, b⁆
  rw [commutator_eq_of_center_coset (Quotient.out_eq _) _]
  apply inv_injective
  simp only [commutatorElement_inv]
  exact commutator_eq_of_center_coset (Quotient.out_eq _) _

/-- Schur's theorem plus finite abelianization implies finiteness. -/
theorem finite_of_finiteIndex_center_and_commutator {G : Type*} [Group G]
    [(Subgroup.center G).FiniteIndex] [(commutator G).FiniteIndex] : Finite G := by
  letI : Finite (commutatorSet G) := finite_commutatorSet_of_finiteIndex_center
  exact Finite.of_subgroup_quotient (commutator G)

/-- The subgroup killed by every quotient central on `Γ(N)`. -/
abbrev relativeCommutator (N : ℕ) : Subgroup SL2Z := ⁅(⊤ : Subgroup SL2Z), Gamma N⁆

instance relativeCommutator_normal (N : ℕ) : (relativeCommutator N).Normal := by
  letI := Gamma_normal (N := N)
  exact Subgroup.commutator_normal _ _

/-- The relative commutator lies in the principal subgroup. -/
theorem relativeCommutator_le_gamma (N : ℕ) : relativeCommutator N ≤ Gamma N := by
  letI := Gamma_normal (N := N)
  exact Subgroup.commutator_le_right _ _

/-- The universal quotient in which the image of `Γ(N)` is central. -/
abbrev CentralQuotient (N : ℕ) := SL2Z ⧸ relativeCommutator N

/-- Centrality of the principal subgroup image is exactly the commutator condition. -/
theorem gamma_image_le_center_iff {E : Type*} [Group E]
    (f : SL2Z →* E) (hf : Function.Surjective f) (N : ℕ) :
    (Gamma N).map f ≤ Subgroup.center E ↔ relativeCommutator N ≤ f.ker := by
  rw [Subgroup.commutator_le]
  constructor
  · intro h g _ n hn
    change f ⁅g, n⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (h (Subgroup.mem_map_of_mem f hn)) (f g)
  · intro h x hx
    obtain ⟨n, hn, rfl⟩ := hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := hf y
    have hc : f ⁅g, n⁆ = 1 := h g (Subgroup.mem_top _) n hn
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc

/-- The principal subgroup has central image in the universal relative quotient. -/
theorem gamma_image_le_center (N : ℕ) :
    (Gamma N).map (QuotientGroup.mk' (relativeCommutator N)) ≤
      Subgroup.center (CentralQuotient N) := by
  apply (gamma_image_le_center_iff _ QuotientGroup.mk_surjective N).mpr
  rw [QuotientGroup.ker_mk']

/-- The quotient by the relative commutator is finite for every positive level. -/
theorem centralQuotient_finite (N : ℕ) (hN : 0 < N) : Finite (CentralQuotient N) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let f := QuotientGroup.mk' (relativeCommutator N)
  have hf : Function.Surjective f := QuotientGroup.mk_surjective
  haveI : ((Gamma N).map f).FiniteIndex :=
    ⟨ne_zero_of_dvd_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := Gamma N))
      ((Gamma N).index_map_dvd hf)⟩
  haveI : (Subgroup.center (CentralQuotient N)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (gamma_image_le_center N)
  haveI : ((Gamma 12).map f).FiniteIndex :=
    ⟨ne_zero_of_dvd_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := Gamma 12))
      ((Gamma 12).index_map_dvd hf)⟩
  have hcomm : (commutator SL2Z).map f = commutator (CentralQuotient N) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf, commutator_def]
  haveI : (commutator (CentralQuotient N)).FiniteIndex :=
    Subgroup.finiteIndex_of_le
      ((Subgroup.map_mono gamma_twelve_le_commutator).trans_eq hcomm)
  exact finite_of_finiteIndex_center_and_commutator

/-- Unconditional finite index of `[SL₂(ℤ), Γ(N)]`. -/
theorem relativeCommutator_finiteIndex (N : ℕ) (hN : 0 < N) :
    (relativeCommutator N).FiniteIndex := by
  letI := centralQuotient_finite N hN
  exact Subgroup.finiteIndex_of_finite_quotient

/-- In particular, the relative abelian quotient `Γ(N)/[SL₂(ℤ), Γ(N)]` is finite. -/
theorem gamma_relativeQuotient_finite (N : ℕ) (hN : 0 < N) :
    Finite (Gamma N ⧸ (relativeCommutator N).subgroupOf (Gamma N)) := by
  letI := relativeCommutator_finiteIndex N hN
  infer_instance

/-- Transfer gives a uniform exponent bound without complex characters or induction. -/
theorem centralQuotient_pow_index (N : ℕ) (hN : 0 < N) (x : CentralQuotient N) :
    x ^ (12 * (Gamma N).index) = 1 := by
  letI := centralQuotient_finite N hN
  letI : CommGroup (Subgroup.center (CentralQuotient N)) :=
    { (inferInstance : Group (Subgroup.center (CentralQuotient N))) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.property a) }
  let f := QuotientGroup.mk' (relativeCommutator N)
  obtain ⟨g, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective f) x
  change f g ^ (12 * (Gamma N).index) = 1
  have hp := character_pow_twelve
    ((MonoidHom.transferCenterPow (CentralQuotient N)).comp f) g
  have hp' : f g ^ ((Subgroup.center (CentralQuotient N)).index * 12) = 1 := by
    simpa only [MonoidHom.comp_apply, ← pow_mul, Subgroup.coe_pow,
      MonoidHom.transferCenterPow_apply, Subgroup.coe_one] using
      congrArg (fun z : Subgroup.center (CentralQuotient N) => (z : CentralQuotient N)) hp
  have hd : (Subgroup.center (CentralQuotient N)).index ∣ (Gamma N).index :=
    (Subgroup.index_dvd_of_le (gamma_image_le_center N)).trans
      ((Gamma N).index_map_dvd QuotientGroup.mk_surjective)
  obtain ⟨k, hk⟩ := hd
  rw [hk, show 12 * ((Subgroup.center (CentralQuotient N)).index * k) =
    ((Subgroup.center (CentralQuotient N)).index * 12) * k by ac_rfl, pow_mul, hp', one_pow]

/-- Every modular-group element has a uniformly bounded power in the relative commutator. -/
theorem pow_index_mem_relativeCommutator (N : ℕ) (hN : 0 < N) (g : SL2Z) :
    g ^ (12 * (Gamma N).index) ∈ relativeCommutator N := by
  apply (QuotientGroup.eq_one_iff _).mp
  simpa only [← map_pow] using
    centralQuotient_pow_index N hN (QuotientGroup.mk' (relativeCommutator N) g)

/-- Characters of the principal subgroup killing the relative commutator have
the claimed exponent bound; the codomain need not even be commutative. -/
theorem gamma_character_pow_index {A : Type*} [Group A]
    (N : ℕ) (hN : 0 < N) (χ : Gamma N →* A)
    (hχ : (relativeCommutator N).subgroupOf (Gamma N) ≤ χ.ker) (g : Gamma N) :
    χ g ^ (12 * (Gamma N).index) = 1 := by
  rw [← map_pow]
  exact hχ (pow_index_mem_relativeCommutator N hN g)

/-- Every homomorphism killing the relative commutator has finite image. -/
theorem finite_range_of_relativeCommutator_le_ker {A : Type*} [Group A]
    (N : ℕ) (hN : 0 < N) (f : SL2Z →* A) (hf : relativeCommutator N ≤ f.ker) :
    Finite f.range := by
  letI := relativeCommutator_finiteIndex N hN
  letI := Subgroup.finiteIndex_of_le hf
  exact Finite.of_equiv (SL2Z ⧸ f.ker) (QuotientGroup.quotientKerEquivRange f).toEquiv

/-- Projective congruence unconditionally gives a finite matrix image.
This does not assert a genuine congruence level. -/
theorem matrix_units_range_finite_of_projectiveCongruence
    {κ : Type*} [Fintype κ] [DecidableEq κ] (ρ : SL2Z →* Matrix κ κ ℂ)
    {N : ℕ} (hN : 0 < N) (hp : DLNBridge.MatrixProjectiveCongruence ρ N) :
    Finite ρ.toHomUnits.range :=
  finite_range_of_relativeCommutator_le_ker N hN ρ.toHomUnits (relativeCommutator_le_ker ρ hp)

end VOA.Huang.DLNLifting
