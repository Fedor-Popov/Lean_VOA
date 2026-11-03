import VOA.Huang.DLNSchur3Words

/-! # Weyl words and the remaining central torus symbol

Exact conjugation relations hold for the canonical root lifts. The torus defect is
central and satisfies a cocycle identity. Its vanishing is not asserted.
-/

namespace VOA.Huang.DLNSchur

section Defect

variable {R E : Type*} [CommRing R] [Group E]

/-- Failure of multiplicativity of the standard torus word. -/
def torusDefect (X Y : Multiplicative R →* E) (u v : Rˣ) : E :=
  torusWord X Y u * torusWord X Y v * (torusWord X Y (u * v))⁻¹

theorem torusDefect_mem_ker (π : E →* Matrix.SpecialLinearGroup (Fin 2) R)
    (X Y : Multiplicative R →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd) (u v : Rˣ) :
    torusDefect X Y u v ∈ π.ker := by
  simp only [torusDefect, MonoidHom.mem_ker, map_mul, map_inv,
    map_torusWord π X Y hX hY, ← torus_mul, mul_inv_cancel]

theorem torusDefect_mem_center (π : E →* Matrix.SpecialLinearGroup (Fin 2) R)
    (hc : π.ker ≤ Subgroup.center E) (X Y : Multiplicative R →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd) (u v : Rˣ) :
    torusDefect X Y u v ∈ Subgroup.center E :=
  hc (torusDefect_mem_ker π X Y hX hY u v)

/-- The central torus defect obeys the usual cocycle identity. This does not kill it. -/
theorem torusDefect_cocycle (π : E →* Matrix.SpecialLinearGroup (Fin 2) R)
    (hc : π.ker ≤ Subgroup.center E) (X Y : Multiplicative R →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd) (u v w : Rˣ) :
    torusDefect X Y u v * torusDefect X Y (u * v) w =
      torusDefect X Y v w * torusDefect X Y u (v * w) := by
  have hcomm : Commute (torusWord X Y u) (torusDefect X Y v w) :=
    Subgroup.mem_center_iff.mp (torusDefect_mem_center π hc X Y hX hY v w) _
  calc
    _ = torusWord X Y u * torusDefect X Y v w * torusWord X Y (v * w) *
        (torusWord X Y (u * (v * w)))⁻¹ := by
      simp only [torusDefect, mul_assoc u v w]
      group
    _ = _ := by rw [hcomm.eq]; simp only [torusDefect]; group

end Defect

section Conjugation

variable {n : ℕ} {E : Type*} [Group E]
variable (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
variable (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
variable (hs : Function.Surjective π)
variable (X Y : Multiplicative (ZMod n) →* E)
variable (hX : ∀ t, π (X t) = upperRoot t.toAdd)
variable (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
variable (hn : RootNormalization h2 π X Y)

include h3 hs hX hY hn

/-- The standard Weyl word satisfies the exact mixed upper-root relation. -/
theorem weylWord_upper_conj (u : (ZMod n)ˣ) (t : ZMod n) :
    weylWord X Y u * X (Multiplicative.ofAdd t) * (weylWord X Y u)⁻¹ =
      Y (Multiplicative.ofAdd (-((↑u⁻¹ : ZMod n) ^ 2 * t))) :=
  normalized_weyl_upper_conj h2 h3 π hs X Y hn _ u (map_weylWord π X Y hX hY u) t

/-- The standard Weyl word satisfies the exact mixed lower-root relation. -/
theorem weylWord_lower_conj (u : (ZMod n)ˣ) (t : ZMod n) :
    weylWord X Y u * Y (Multiplicative.ofAdd t) * (weylWord X Y u)⁻¹ =
      X (Multiplicative.ofAdd (-((u : ZMod n) ^ 2 * t))) :=
  normalized_weyl_lower_conj h2 h3 π hs X Y hn _ u (map_weylWord π X Y hX hY u) t

/-- Exact square-character action holds for the standard torus word too. -/
theorem torusWord_upper_conj (u : (ZMod n)ˣ) (t : ZMod n) :
    torusWord X Y u * X (Multiplicative.ofAdd t) * (torusWord X Y u)⁻¹ =
      X (Multiplicative.ofAdd ((u : ZMod n) ^ 2 * t)) :=
  normalized_torus_upper_conj h2 h3 π hs X Y hn _ u (map_torusWord π X Y hX hY u) t

end Conjugation

end VOA.Huang.DLNSchur
