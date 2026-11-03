import VOA.Huang.DLNSchur3Relations
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! # Torus words on square units

Cyclicity of the unit group makes the preimage of the diagonal torus abelian.
Exact root conjugation then proves multiplicativity on square parameters.
No vanishing assertion for arbitrary torus defects is assumed here.
-/

namespace VOA.Huang.DLNSchur

section Cyclic

variable {R E : Type*} [CommRing R] [Group E]

/-- Central extensions have abelian preimages of cyclic diagonal tori. -/
theorem torus_lifts_commute [IsCyclic Rˣ]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) R)
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    {a b : E} {u v : Rˣ} (ha : π a = torus u) (hb : π b = torus v) :
    Commute a b := by
  let T : Rˣ →* Matrix.SpecialLinearGroup (Fin 2) R :=
    { toFun := torus, map_one' := torus_one, map_mul' := torus_mul }
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Rˣ)
  obtain ⟨i, hi⟩ := hw u
  obtain ⟨j, hj⟩ := hw v
  obtain ⟨c, hpc⟩ := hs (torus w)
  have ha' : π a = π c ^ i := by
    rw [ha, hpc, ← hi]
    exact T.map_zpow w i
  have hb' : π b = π c ^ j := by
    rw [hb, hpc, ← hj]
    exact T.map_zpow w j
  have hz : a * (c ^ i)⁻¹ ∈ Subgroup.center E := hc (by
    simp [MonoidHom.mem_ker, ha'])
  have hw' : b * (c ^ j)⁻¹ ∈ Subgroup.center E := hc (by
    simp [MonoidHom.mem_ker, hb'])
  have H := ((show Commute (a * (c ^ i)⁻¹) (b * (c ^ j)⁻¹) from
    (Subgroup.mem_center_iff.mp hz _).symm).mul_right
    (show Commute (a * (c ^ i)⁻¹) (c ^ j) from
      (Subgroup.mem_center_iff.mp hz _).symm)).mul_left
    ((show Commute (c ^ i) (b * (c ^ j)⁻¹) from
      Subgroup.mem_center_iff.mp hw' _).mul_right ((Commute.refl c).zpow_zpow i j))
  simpa using H

end Cyclic

section Squares

variable {n : ℕ} {E : Type*} [Group E]
variable (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
variable (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
variable (hs : Function.Surjective π)
variable (X Y : Multiplicative (ZMod n) →* E)
variable (hX : ∀ t, π (X t) = upperRoot t.toAdd)
variable (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
variable (hn : RootNormalization h2 π X Y)

include h3 hs hn

/-- Conjugating a Weyl word by a torus lift squares its parameter. -/
theorem normalized_torus_weylWord_conj (g : E) (u v : (ZMod n)ˣ)
    (hg : π g = torus u) :
    g * weylWord X Y v * g⁻¹ = weylWord X Y (u ^ 2 * v) := by
  have hx := normalized_torus_upper_conj h2 h3 π hs X Y hn g u hg (v : ZMod n)
  have hy := normalized_torus_lower_conj h2 h3 π hs X Y hn g u hg
    (-(↑v⁻¹ : ZMod n))
  calc
    _ = (g * X (Multiplicative.ofAdd (v : ZMod n)) * g⁻¹) *
        (g * Y (Multiplicative.ofAdd (-(↑v⁻¹ : ZMod n))) * g⁻¹) *
        (g * X (Multiplicative.ofAdd (v : ZMod n)) * g⁻¹) := by
          unfold weylWord; group
    _ = _ := by
      rw [hx, hy]
      simp [weylWord, mul_comm, neg_mul]

include hX hY

/-- If the diagonal preimage is abelian, square parameters have zero defect. -/
theorem torusWord_mul_square [IsCyclic (ZMod n)ˣ]
    (hc : π.ker ≤ Subgroup.center E) (u v : (ZMod n)ˣ) :
    torusWord X Y (u ^ 2 * v) = torusWord X Y (u ^ 2) * torusWord X Y v := by
  let g := torusWord X Y u
  have hg : π g = torus u := map_torusWord π X Y hX hY u
  have hv := normalized_torus_weylWord_conj h2 h3 π hs X Y hn g u v hg
  have h1 := normalized_torus_weylWord_conj h2 h3 π hs X Y hn g u 1 hg
  simp only [mul_one] at h1
  have hcomm : Commute g (torusWord X Y v) :=
    torus_lifts_commute π hs hc hg (map_torusWord π X Y hX hY v)
  have he : torusWord X Y v =
      weylWord X Y (u ^ 2 * v) * (weylWord X Y (u ^ 2))⁻¹ := by
    calc
      _ = g * torusWord X Y v * g⁻¹ := by rw [hcomm.eq]; group
      _ = (g * weylWord X Y v * g⁻¹) *
          (g * weylWord X Y 1 * g⁻¹)⁻¹ := by unfold torusWord; group
      _ = _ := by rw [hv, h1]
  have hcomm' : Commute (torusWord X Y v) (torusWord X Y (u ^ 2)) :=
    torus_lifts_commute π hs hc (map_torusWord π X Y hX hY v)
      (map_torusWord π X Y hX hY (u ^ 2))
  calc
    _ = torusWord X Y v * torusWord X Y (u ^ 2) := by
      rw [he]; unfold torusWord; group
    _ = _ := hcomm'.eq

omit h3 hn in
/-- Symmetry uses cyclicity of the diagonal torus, not just centrality of its defect. -/
theorem torusDefect_symm [IsCyclic (ZMod n)ˣ]
    (hc : π.ker ≤ Subgroup.center E) (u v : (ZMod n)ˣ) :
    torusDefect X Y u v = torusDefect X Y v u := by
  have h := torus_lifts_commute π hs hc (map_torusWord π X Y hX hY u)
    (map_torusWord π X Y hX hY v)
  simp only [torusDefect, h.eq, mul_comm u v]

/-- Multiplying either parameter by a square does not change the symbol. -/
theorem torusDefect_mul_squares [IsCyclic (ZMod n)ˣ]
    (hc : π.ker ≤ Subgroup.center E) (u v a b : (ZMod n)ˣ) :
    torusDefect X Y (u ^ 2 * a) (v ^ 2 * b) = torusDefect X Y a b := by
  have hleft : ∀ u a b : (ZMod n)ˣ,
      torusDefect X Y (u ^ 2 * a) b = torusDefect X Y a b := by
    intro u a b
    have hcomm : Commute (torusWord X Y (u ^ 2)) (torusDefect X Y a b) :=
      Subgroup.mem_center_iff.mp (torusDefect_mem_center π hc X Y hX hY a b) _
    calc
      _ = torusWord X Y (u ^ 2) * torusDefect X Y a b *
          (torusWord X Y (u ^ 2))⁻¹ := by
        simp only [torusDefect, mul_assoc (u ^ 2) a b,
          torusWord_mul_square h2 h3 π hs X Y hX hY hn hc]
        group
      _ = _ := by rw [hcomm.eq]; group
  rw [hleft, torusDefect_symm π hs X Y hX hY hc,
    hleft, torusDefect_symm π hs X Y hX hY hc]

/-- For a generator of the finite cyclic unit group, only its self-defect remains. -/
theorem torusDefect_eq_one_or_generator [IsCyclic (ZMod n)ˣ]
    (hc : π.ker ≤ Subgroup.center E) (w : (ZMod n)ˣ)
    (hw : ∀ u : (ZMod n)ˣ, u ∈ Submonoid.powers w) (u v : (ZMod n)ˣ) :
    torusDefect X Y u v = 1 ∨ torusDefect X Y u v = torusDefect X Y w w := by
  obtain ⟨i, rfl⟩ := hw u
  obtain ⟨j, rfl⟩ := hw v
  have hi : w ^ i = (w ^ (i / 2)) ^ 2 * w ^ (i % 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1; omega
  have hj : w ^ j = (w ^ (j / 2)) ^ 2 * w ^ (j % 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1; omega
  dsimp only
  rw [hi, hj, torusDefect_mul_squares h2 h3 π hs X Y hX hY hn hc]
  have hi' : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have hj' : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;>
    simp [hi', hj', torusDefect]

end Squares

/-- The square-parameter defect vanishes at every odd prime power away from three. -/
theorem torusDefect_square_primePower {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E : Type*} [Group E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k)))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (X Y : Multiplicative (ZMod (p ^ k)) →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
    (hn : RootNormalization (primePower_coprime_two_three hp hp5).1 π X Y)
    (u v : (ZMod (p ^ k))ˣ) : torusDefect X Y (u ^ 2) v = 1 := by
  haveI := ZMod.isCyclic_units_of_prime_pow p hp (by omega) k
  rw [torusDefect, torusWord_mul_square
    (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
    π hs X Y hX hY hn hc u v, mul_inv_cancel]

end VOA.Huang.DLNSchur
