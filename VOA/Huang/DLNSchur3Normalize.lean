import VOA.Huang.DLNSchur2Relations
import VOA.Huang.DLNSchur3Matrices

/-! # Canonical normalization of root lifts

Commutators in a central extension depend only on the two images. This permits a
normalization with exact torus covariance, without assuming that the kernel meets
the derived group trivially.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

section Groups

variable {E Q : Type*} [Group E] [Group Q]

/-- Changing either lift by a central kernel element does not change a commutator. -/
theorem commutator_eq_of_images_eq (π : E →* Q)
    (hc : π.ker ≤ Subgroup.center E) {a b a' b' : E}
    (ha : π a = π a') (hb : π b = π b') : ⁅a, b⁆ = ⁅a', b'⁆ := by
  let z := a * a'⁻¹
  let w := b * b'⁻¹
  have hz : z ∈ Subgroup.center E := hc (by simp [z, MonoidHom.mem_ker, ha])
  have hw : w ∈ Subgroup.center E := hc (by simp [w, MonoidHom.mem_ker, hb])
  have ea : a = z * a' := by simp [z]
  have eb : b = w * b' := by simp [w]
  rw [ea, eb, commutator_mul_mul_of_commute
    ((Subgroup.mem_center_iff.mp hz a').symm)
    ((Subgroup.mem_center_iff.mp hz b').symm)
    ((Subgroup.mem_center_iff.mp hw a').symm)
    ((Subgroup.mem_center_iff.mp hw b').symm)]
  rw [(show Commute z w from (Subgroup.mem_center_iff.mp hz w).symm).commutator_eq,
    one_mul]

/-- Commutators with a fixed element multiply on an abelian normalized subgroup. -/
theorem commutator_mul_right_of_root_commute (h a b : E)
    (hab : Commute a b) (hconj : Commute a (h * b * h⁻¹)) :
    ⁅h, a * b⁆ = ⁅h, a⁆ * ⁅h, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hc : Commute a ⁅h, b⁆ := hconj.mul_right hab.inv_right
  rw [mul_assoc ⁅h, a⁆ a ⁅h, b⁆, hc.eq]
  group

end Groups

section Roots

variable {n : ℕ} {E : Type*} [Group E]

/-- Normalize a root homomorphism by a commutator and a scalar change of parameter. -/
def correctedRootHom (X : Multiplicative (ZMod n) →* E) (h : E) (d : ZMod n)
    (hcomm : ∀ s t, Commute (X (Multiplicative.ofAdd s))
      (h * X (Multiplicative.ofAdd t) * h⁻¹)) : Multiplicative (ZMod n) →* E where
  toFun t := ⁅h, X (Multiplicative.ofAdd (d * t.toAdd))⁆
  map_one' := by simp
  map_mul' s t := by
    change ⁅h, X (Multiplicative.ofAdd (d * (s.toAdd + t.toAdd)))⁆ = _
    rw [mul_add]
    change ⁅h, X (Multiplicative.ofAdd (d * s.toAdd) *
      Multiplicative.ofAdd (d * t.toAdd))⁆ = _
    rw [map_mul]
    apply commutator_mul_right_of_root_commute
    · exact (Commute.all _ _).map X
    · exact hcomm _ _

/-- The normalization always takes values in the derived subgroup. -/
theorem correctedRootHom_mem_commutator (X : Multiplicative (ZMod n) →* E)
    (h : E) (d : ZMod n) (hcomm) (t) :
    correctedRootHom X h d hcomm t ∈ commutator E :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end Roots

section Normalization

variable {n : ℕ} [NeZero n] {E : Type*} [Group E]

/-- A canonical normalization of the two roots, expressed using arbitrary lifts.
The lower root uses the inverse diagonal, so both parameter changes are multiplication by 3. -/
def RootNormalization (h2 : Nat.Coprime 2 n)
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (X Y : Multiplicative (ZMod n) →* E) : Prop :=
  (∀ h b t, π h = torus (ZMod.unitOfCoprime 2 h2) → π b = upperRoot t →
    ⁅h, b⁆ = X (Multiplicative.ofAdd (3 * t))) ∧
  (∀ h b t, π h = torus (ZMod.unitOfCoprime 2 h2)⁻¹ → π b = lowerRoot t →
    ⁅h, b⁆ = Y (Multiplicative.ofAdd (3 * t)))

/-- Canonical root homomorphisms exist, and still generate exactly the derived subgroup. -/
theorem exists_normalized_root_homs
    (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) :
    ∃ X Y : Multiplicative (ZMod n) →* E,
      (∀ t, π (X t) = upperRoot t.toAdd) ∧
      (∀ t, π (Y t) = lowerRoot t.toAdd) ∧
      X.range ⊔ Y.range = commutator E ∧ RootNormalization h2 π X Y := by
  obtain ⟨X₀, Y₀, hX₀, hY₀, _⟩ := exists_root_homs h2 h3 π hs hc
  let u := ZMod.unitOfCoprime 2 h2
  let v := ZMod.unitOfCoprime 3 h3
  let d : ZMod n := ↑v⁻¹
  have hu : (u : ZMod n) = 2 := by simp [u]
  have hd : (3 : ZMod n) * d = 1 := by
    have hv : (v : ZMod n) = 3 := by simp [v]
    rw [← hv]; exact Units.mul_inv v
  have hd' : ∀ t : ZMod n, d * (3 * t) = t := by
    intro t; calc
      d * (3 * t) = (3 * d) * t := by ring
      _ = t := by rw [hd, one_mul]
  obtain ⟨h, hh⟩ := hs (torus u)
  have hh' : π h⁻¹ = torus u⁻¹ := by simp [hh]
  have hXu : ∀ s t, Commute (X₀ (Multiplicative.ofAdd s))
      (h * X₀ (Multiplicative.ofAdd t) * h⁻¹) := by
    intro s t
    apply upper_lifts_commute π hs hc (t := (u : ZMod n) ^ 2 * t) (hX₀ _)
    simpa only [map_mul, map_inv, hh, hX₀] using torus_upper_conj u t
  have hYl : ∀ s t, Commute (Y₀ (Multiplicative.ofAdd s))
      (h⁻¹ * Y₀ (Multiplicative.ofAdd t) * (h⁻¹)⁻¹) := by
    intro s t
    apply lower_lifts_commute π hs hc (t := (u : ZMod n) ^ 2 * t) (hY₀ _)
    simpa only [map_mul, map_inv, hh, hY₀, torus_inv, inv_inv] using
      torus_lower_conj u⁻¹ t
  let X := correctedRootHom X₀ h d hXu
  let Y := correctedRootHom Y₀ h⁻¹ d hYl
  have hX : ∀ t, π (X t) = upperRoot t.toAdd := by
    intro t
    change π ⁅h, X₀ (Multiplicative.ofAdd (d * t.toAdd))⁆ = _
    rw [map_commutatorElement, hh, hX₀, torus_upper_commutator, hu]
    congr 1
    change (2 ^ 2 - 1) * (d * t.toAdd) = t.toAdd
    calc
      (2 ^ 2 - 1) * (d * t.toAdd) = (3 * d) * t.toAdd := by ring
      _ = t.toAdd := by rw [hd, one_mul]
  have hY : ∀ t, π (Y t) = lowerRoot t.toAdd := by
    intro t
    change π ⁅h⁻¹, Y₀ (Multiplicative.ofAdd (d * t.toAdd))⁆ = _
    rw [map_commutatorElement, hh', hY₀, torus_lower_commutator, inv_inv, hu]
    congr 1
    change (2 ^ 2 - 1) * (d * t.toAdd) = t.toAdd
    calc
      (2 ^ 2 - 1) * (d * t.toAdd) = (3 * d) * t.toAdd := by ring
      _ = t.toAdd := by rw [hd, one_mul]
  refine ⟨X, Y, hX, hY, ?_, ?_⟩
  · apply le_antisymm
    · apply sup_le
      · rintro _ ⟨t, rfl⟩; exact correctedRootHom_mem_commutator _ _ _ _ _
      · rintro _ ⟨t, rfl⟩; exact correctedRootHom_mem_commutator _ _ _ _ _
    · apply commutator_le_of_central_map_top π hc
      apply top_unique
      rw [← root_generators n, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact ⟨X (Multiplicative.ofAdd 1),
          (show X.range ≤ X.range ⊔ Y.range from le_sup_left) ⟨_, rfl⟩, hX _⟩
      · exact ⟨Y (Multiplicative.ofAdd 1),
          (show Y.range ≤ X.range ⊔ Y.range from le_sup_right) ⟨_, rfl⟩, hY _⟩
  · constructor
    · intro h' b t hh' hb
      change ⁅h', b⁆ = ⁅h, X₀ (Multiplicative.ofAdd (d * (3 * t)))⁆
      rw [hd']
      exact commutator_eq_of_images_eq π hc (hh'.trans hh.symm) (hb.trans (hX₀ _).symm)
    · intro h' b t hh'' hb
      change ⁅h', b⁆ = ⁅h⁻¹, Y₀ (Multiplicative.ofAdd (d * (3 * t)))⁆
      rw [hd']
      exact commutator_eq_of_images_eq π hc (hh''.trans hh'.symm) (hb.trans (hY₀ _).symm)

end Normalization

end VOA.Huang.DLNSchur
