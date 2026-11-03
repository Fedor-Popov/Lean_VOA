import VOA.Huang.DLNSchur3Normalize

/-! # Exact torus and Weyl conjugation for normalized roots

These are unconditional mixed-root conjugation identities. They do not assert that
every relation among the matrices holds among their lifts.
-/

namespace VOA.Huang.DLNSchur

open scoped commutatorElement

section Transport

variable {n : ℕ} {E Q : Type*} [Group E] [Group Q]

/-- Transport commutator-normalized parameters through a quotient conjugation. -/
theorem conj_of_commutator_normalization (h3 : Nat.Coprime 3 n)
    (π : E →* Q) (hs : Function.Surjective π)
    (T T' : Q) (U V : ZMod n → Q) (X Y : Multiplicative (ZMod n) →* E)
    (hX : ∀ h b t, π h = T → π b = U t → ⁅h, b⁆ = X (Multiplicative.ofAdd (3 * t)))
    (hY : ∀ h b t, π h = T' → π b = V t → ⁅h, b⁆ = Y (Multiplicative.ofAdd (3 * t)))
    (g : E) (c : ZMod n)
    (hT : π g * T * (π g)⁻¹ = T')
    (hU : ∀ t, π g * U t * (π g)⁻¹ = V (c * t)) (t : ZMod n) :
    g * X (Multiplicative.ofAdd t) * g⁻¹ = Y (Multiplicative.ofAdd (c * t)) := by
  let v := ZMod.unitOfCoprime 3 h3
  let s : ZMod n := ↑v⁻¹ * t
  have hv : (v : ZMod n) = 3 := by simp [v]
  have hst : 3 * s = t := by
    change 3 * ((↑v⁻¹ : ZMod n) * t) = t
    rw [← hv, ← mul_assoc, Units.mul_inv, one_mul]
  obtain ⟨h, hh⟩ := hs T
  obtain ⟨b, hb⟩ := hs (U s)
  have hx := hX h b s hh hb
  rw [hst] at hx
  rw [← hx, conjugate_commutatorElement]
  have ht' : π (g * h * g⁻¹) = T' := by simpa [hh] using hT
  have hu' : π (g * b * g⁻¹) = V (c * s) := by simpa [hb] using hU s
  rw [hY _ _ _ ht' hu']
  congr 2
  calc
    3 * (c * s) = c * (3 * s) := by ring
    _ = c * t := by rw [hst]

end Transport

section Covariance

variable {n : ℕ} {E : Type*} [Group E]
variable (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
variable (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
variable (hs : Function.Surjective π)
variable (X Y : Multiplicative (ZMod n) →* E) (hn : RootNormalization h2 π X Y)

include h3 hs hn

/-- Every lift of a diagonal matrix acts by the exact square character. -/
theorem normalized_torus_upper_conj (g : E) (u : (ZMod n)ˣ)
    (hg : π g = torus u) (t : ZMod n) :
    g * X (Multiplicative.ofAdd t) * g⁻¹ =
      X (Multiplicative.ofAdd ((u : ZMod n) ^ 2 * t)) := by
  apply conj_of_commutator_normalization h3 π hs _ _ _ _ X X hn.1 hn.1 g
  · rw [hg, (torus_commute _ _).eq]; group
  · intro s; rw [hg, torus_upper_conj]

/-- The lower root has the exact inverse-square character. -/
theorem normalized_torus_lower_conj (g : E) (u : (ZMod n)ˣ)
    (hg : π g = torus u) (t : ZMod n) :
    g * Y (Multiplicative.ofAdd t) * g⁻¹ =
      Y (Multiplicative.ofAdd ((↑u⁻¹ : ZMod n) ^ 2 * t)) := by
  apply conj_of_commutator_normalization h3 π hs _ _ _ _ Y Y hn.2 hn.2 g
  · rw [hg, (torus_commute _ _).eq]; group
  · intro s; rw [hg, torus_lower_conj]

/-- Every lift of a Weyl matrix interchanges the normalized roots exactly. -/
theorem normalized_weyl_upper_conj (g : E) (u : (ZMod n)ˣ)
    (hg : π g = weyl u) (t : ZMod n) :
    g * X (Multiplicative.ofAdd t) * g⁻¹ =
      Y (Multiplicative.ofAdd (-((↑u⁻¹ : ZMod n) ^ 2 * t))) := by
  have h := conj_of_commutator_normalization h3 π hs _ _ _ _ X Y hn.1 hn.2 g
    (-((↑u⁻¹ : ZMod n) ^ 2)) (by rw [hg, weyl_torus_conj])
    (by intro s; rw [hg, weyl_upper_conj, neg_mul]) t
  simpa only [neg_mul] using h

/-- The reverse Weyl conjugation identity. -/
theorem normalized_weyl_lower_conj (g : E) (u : (ZMod n)ˣ)
    (hg : π g = weyl u) (t : ZMod n) :
    g * Y (Multiplicative.ofAdd t) * g⁻¹ =
      X (Multiplicative.ofAdd (-((u : ZMod n) ^ 2 * t))) := by
  have h := conj_of_commutator_normalization h3 π hs _ _ _ _ Y X hn.2 hn.1 g
    (-((u : ZMod n) ^ 2)) (by rw [hg, weyl_torus_conj, inv_inv])
    (by intro s; rw [hg, weyl_lower_conj, neg_mul]) t
  simpa only [neg_mul] using h

end Covariance

end VOA.Huang.DLNSchur
