import VOA.Huang.DLNSchur2Roots

/-! # Cyclic root subgroups in arbitrary central extensions -/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

variable {E Q : Type*} [Group E] [Group Q]

/-- Two lifts of powers of one lifted element commute in a central extension. -/
theorem commute_of_images_powers (π : E →* Q) (hc : π.ker ≤ Subgroup.center E)
    (a b c : E) (i j : ℕ) (ha : π a = π c ^ i) (hb : π b = π c ^ j) :
    Commute a b := by
  let z := a * (c ^ i)⁻¹
  let w := b * (c ^ j)⁻¹
  have hz : z ∈ Subgroup.center E := hc (by simp [z, MonoidHom.mem_ker, ha])
  have hw : w ∈ Subgroup.center E := hc (by simp [w, MonoidHom.mem_ker, hb])
  have heqa : a = z * c ^ i := by simp [z]
  have heqb : b = w * c ^ j := by simp [w]
  rw [heqa, heqb]
  exact ((show Commute z w from (Subgroup.mem_center_iff.mp hz w).symm).mul_right
    (show Commute z (c ^ j) from (Subgroup.mem_center_iff.mp hz _).symm)).mul_left
    ((show Commute (c ^ i) w from Subgroup.mem_center_iff.mp hw _).mul_right
      ((Commute.refl c).pow_pow i j))

/-- A conjugation commutator has bounded order when the conjugated lifts commute. -/
theorem commutator_pow_eq_one_of_commute (h b : E) (n : ℕ)
    (hcomm : Commute (h * b * h⁻¹) b) (hbn : b ^ n ∈ Subgroup.center E) :
    ⁅h, b⁆ ^ n = 1 := by
  calc
    ⁅h, b⁆ ^ n = (h * b * h⁻¹) ^ n * (b⁻¹) ^ n := hcomm.inv_right.mul_pow n
    _ = (h * b ^ n * h⁻¹) * (b ^ n)⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply, inv_pow]
    _ = 1 := by rw [Subgroup.mem_center_iff.mp hbn h]; group

/-- The upper root preimage in a central extension is abelian, for every modulus. -/
theorem upper_lifts_commute {n : ℕ} [NeZero n]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    {a b : E} {s t : ZMod n} (ha : π a = upperRoot s) (hb : π b = upperRoot t) :
    Commute a b := by
  obtain ⟨c, hc'⟩ := hs (upperRoot 1)
  apply commute_of_images_powers π hc a b c s.val t.val
  · simp [ha, hc']
  · simp [hb, hc']

/-- The lower root preimage is abelian as well. -/
theorem lower_lifts_commute {n : ℕ} [NeZero n]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    {a b : E} {s t : ZMod n} (ha : π a = lowerRoot s) (hb : π b = lowerRoot t) :
    Commute a b := by
  obtain ⟨c, hc'⟩ := hs (lowerRoot 1)
  apply commute_of_images_powers π hc a b c s.val t.val
  · simp [ha, hc']
  · simp [hb, hc']

/-- A torsion element defines a homomorphism from the additive cyclic group. -/
def cyclicLift {n : ℕ} [NeZero n] (a : E) (ha : a ^ n = 1) :
    Multiplicative (ZMod n) →* E where
  toFun t := a ^ t.toAdd.val
  map_one' := by simp
  map_mul' s t := by
    change a ^ (s.toAdd + t.toAdd).val = a ^ s.toAdd.val * a ^ t.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    rw [← pow_mod_orderOf a (s.toAdd.val + t.toAdd.val),
      ← Nat.mod_mod_of_dvd _ (orderOf_dvd_of_pow_eq_one ha), pow_mod_orderOf]

/-- The homomorphism sends a natural residue to the corresponding power. -/
theorem cyclicLift_natCast {n : ℕ} [NeZero n] (a : E) (ha : a ^ n = 1) (m : ℕ) :
    cyclicLift a ha (Multiplicative.ofAdd (m : ZMod n)) = a ^ m := by
  change a ^ (m : ZMod n).val = a ^ m
  rw [ZMod.val_natCast]
  rw [← pow_mod_orderOf a m, ← Nat.mod_mod_of_dvd _ (orderOf_dvd_of_pow_eq_one ha),
    pow_mod_orderOf]

/-- A lift of the upper generator with the correct torsion gives a whole root homomorphism. -/
theorem cyclicLift_upper {n : ℕ} [NeZero n]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (a : E) (ha : a ^ n = 1) (hπa : π a = upperRoot 1) (t : Multiplicative (ZMod n)) :
    π (cyclicLift a ha t) = upperRoot t.toAdd := by
  simp [cyclicLift, hπa]

/-- Lower-root version of `cyclicLift_upper`. -/
theorem cyclicLift_lower {n : ℕ} [NeZero n]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (a : E) (ha : a ^ n = 1) (hπa : π a = lowerRoot 1) (t : Multiplicative (ZMod n)) :
    π (cyclicLift a ha t) = lowerRoot t.toAdd := by
  simp [cyclicLift, hπa]

end VOA.Huang.DLNSchur
