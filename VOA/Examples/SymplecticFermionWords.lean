/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionT
import VOA.Core.SuperCovariant

/-!
# Symplectic fermions: generator fields and word fields

The spanning family that `reconstructε` consumes.  Structure follows the Virasoro build
(`Examples/VirasoroWordFields`), with the Koszul signs threaded through: a word of length `n` has
parity `n`, so two word fields are `ε`-local at `koszul n m`, and the product defining a word of
length `n+1` is taken at `koszul 1 n`.
-/

namespace VOA.SympFerm

open CliffordAlgebra
open VOA.Reconstruction

/-- The **scaled generator field** `(k!)⁻¹ ∂_z^k χᵃ(z)`, whose `z⁰`-coefficient is the creation
mode `χᵃ_{-k-1}`. -/
noncomputable def sfGenField (a : Fin 2) (k : ℕ) : FormalDist (Module.End ℂ FockSF) :=
  (k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (chi a))

theorem sfGenField_isField (a : Fin 2) (k : ℕ) : IsField (sfGenField a k) := by
  intro x
  obtain ⟨B, hB⟩ := (chi_isField a).deriv_iterate k x
  exact ⟨B, fun n hn => by
    change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (chi a)) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- Generator fields are pairwise `ε`-local at `ε = -1`: derivatives and scalars preserve
`Localε`. -/
theorem sfGenField_localε (a b : Fin 2) (j k : ℕ) :
    Localε (-1) (sfGenField a j) (sfGenField b k) := by
  have h : Localε (-1) ((VOA.deriv^[j]) (chi a)) ((VOA.deriv^[k]) (chi b)) :=
    ((chi_localε a b).deriv_iterate_left j).deriv_iterate_right k
  exact Localε.smul_right (by norm_num) _ (Localε.smul_left _ _ h)

theorem sfGenField_DCovariant (a : Fin 2) (k : ℕ) : DCovariant T (sfGenField a k) :=
  Reconstruction.DCovariant.smul ((k.factorial : ℂ)⁻¹)
    (Reconstruction.DCovariant.deriv_iterate (chi_DCovariant a) k)

/-- The generator field annihilates the vacuum below degree `0`. -/
theorem sfGenField_vacuum_neg (a : Fin 2) (k : ℕ) {q : ℤ} (hq : q < 0) :
    sfGenField a k q vacSF = 0 := by
  change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (chi a)) q) vacSF = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range k, (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + (k : ℤ) < 0
  · rw [chi_neg_vac a (q + (k : ℤ)) hqi, smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]

/-- The generator field's `z⁰`-coefficient is `χᵃ` at index `k` — i.e. the creation mode
`χᵃ_{-k-1}`.  The factorial cancels against the falling factorial from `∂^k`. -/
theorem sfGenField_zero (a : Fin 2) (k : ℕ) : (sfGenField a k) 0 = chi a (k : ℤ) := by
  change (k.factorial : ℂ)⁻¹ • ((VOA.deriv^[k] (chi a)) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range k, ((0 : ℤ) + 1 + (m : ℤ))) = (k.factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ (k.factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul,
    show (0 : ℤ) + (k : ℤ) = (k : ℤ) from by ring]

/-- **The generator field creates its generator**: `(genᵃₖ)₀|0⟩ = χᵃ_{-k-1}|0⟩`. -/
theorem sfGenField_zero_vac (a : Fin 2) (k : ℕ) :
    sfGenField a k 0 vacSF = ι QSF (Finsupp.single ((k, a) : ℕ × Fin 2) (1 : ℂ)) := by
  rw [sfGenField_zero, chi, if_pos (by positivity)]
  change creBase ((k : ℤ).toNat, a) vacSF = _
  rw [creBase, Int.toNat_natCast]
  change ι QSF (Finsupp.single ((k, a) : ℕ × Fin 2) (1 : ℂ)) * (1 : FockSF) = _
  rw [mul_one]

/-! ## Word fields

A word of length `n` has parity `n`, so two word fields are `ε`-local at `koszul n m`, and the
product forming a word of length `n+1` is taken at `koszul 1 n`.  Dong's lemma delivers exactly
the composite sign `εac * εbc`, which is `koszul (1+n) m` — this is why the induction closes. -/

/-- Koszul signs are multiplicative in the left slot: `koszul (p+q) r = koszul p r * koszul q r`. -/
theorem koszul_add_left (p q r : ZMod 2) : koszul (p + q) r = koszul p r * koszul q r := by
  rw [koszul, koszul, koszul, ← parSign_add, add_mul]

/-- A word of generator indices. -/
abbrev SFWord : Type := List (ℕ × Fin 2)

/-- The iterated super normal-ordered product over a word, with its field witness. -/
noncomputable def YwordSFF : SFWord → { f : FormalDist (Module.End ℂ FockSF) // IsField f }
  | [] => ⟨idField, idField_isField⟩
  | (p :: rest) =>
      let q := YwordSFF rest
      ⟨nprodε (koszul 1 (rest.length : ZMod 2)) (sfGenField_isField p.2 p.1) q.2,
       IsField.nprodε _ (sfGenField_isField p.2 p.1) q.2⟩

/-- The word field. -/
noncomputable def YwordSF (l : SFWord) : FormalDist (Module.End ℂ FockSF) := (YwordSFF l).1

theorem YwordSF_isField (l : SFWord) : IsField (YwordSF l) := (YwordSFF l).2

@[simp] theorem YwordSF_nil : YwordSF [] = idField := rfl

theorem YwordSF_cons (p : ℕ × Fin 2) (rest : SFWord) :
    YwordSF (p :: rest)
      = nprodε (koszul 1 (rest.length : ZMod 2)) (sfGenField_isField p.2 p.1)
        (YwordSF_isField rest) := rfl

/-- The creation monomial a word field creates from the vacuum. -/
noncomputable def stWordSF : SFWord → FockSF
  | [] => 1
  | (p :: rest) => ι QSF (Finsupp.single p (1 : ℂ)) * stWordSF rest

@[simp] theorem stWordSF_nil : stWordSF [] = (1 : FockSF) := rfl

theorem stWordSF_cons (p : ℕ × Fin 2) (rest : SFWord) :
    stWordSF (p :: rest) = ι QSF (Finsupp.single p (1 : ℂ)) * stWordSF rest := rfl

/-- A generator field is `koszul 1 (len l)`-local with every word field. -/
theorem sfGenField_localε_Yword (a : Fin 2) (k : ℕ) :
    ∀ l : SFWord, Localε (koszul 1 (l.length : ZMod 2)) (sfGenField a k) (YwordSF l)
  | [] => by
      rw [YwordSF_nil]
      simpa using (localε_one_iff _ _).mpr (Local_idField_right (sfGenField a k))
  | (p :: rest) => by
      have ih := sfGenField_localε_Yword a k rest
      have hstep :
          Localε (koszul 1 1 * koszul (rest.length : ZMod 2) 1)
            (YwordSF (p :: rest)) (sfGenField a k) := by
        rw [YwordSF_cons]
        exact dong_negε (koszul_mul_self 1 (rest.length : ZMod 2))
          (sfGenField_isField p.2 p.1) (YwordSF_isField rest)
          (sfGenField_localε_Yword p.2 p.1 rest)
          (by simpa using sfGenField_localε p.2 a p.1 k)
          (by rw [koszul_comm]; exact Localε.symm (koszul_mul_self 1 _) ih)
      have hsign : koszul 1 1 * koszul (rest.length : ZMod 2) 1
          = koszul 1 (((p :: rest).length : ℕ) : ZMod 2) := by
        rw [← koszul_add_left, koszul_comm]
        congr 1
        push_cast [List.length_cons]
        ring
      rw [hsign] at hstep
      exact Localε.symm (koszul_mul_self _ _) hstep

/-- **Word fields are pairwise `ε`-local at the Koszul sign of their lengths.** -/
theorem YwordSF_localε : ∀ l₁ l₂ : SFWord,
    Localε (koszul (l₁.length : ZMod 2) (l₂.length : ZMod 2)) (YwordSF l₁) (YwordSF l₂)
  | [], l₂ => by
      rw [YwordSF_nil]
      simpa using (localε_one_iff _ _).mpr (Local_idField_left (YwordSF l₂))
  | (p :: rest), l₂ => by
      have hstep :
          Localε (koszul 1 (l₂.length : ZMod 2) * koszul (rest.length : ZMod 2)
              (l₂.length : ZMod 2)) (YwordSF (p :: rest)) (YwordSF l₂) := by
        rw [YwordSF_cons]
        exact dong_negε (koszul_mul_self 1 (rest.length : ZMod 2))
          (sfGenField_isField p.2 p.1) (YwordSF_isField rest)
          (sfGenField_localε_Yword p.2 p.1 rest)
          (sfGenField_localε_Yword p.2 p.1 l₂)
          (YwordSF_localε rest l₂)
      have hsign : koszul 1 (l₂.length : ZMod 2)
            * koszul (rest.length : ZMod 2) (l₂.length : ZMod 2)
          = koszul (((p :: rest).length : ℕ) : ZMod 2) (l₂.length : ZMod 2) := by
        rw [← koszul_add_left]
        congr 1
        push_cast [List.length_cons]
        ring
      rw [hsign] at hstep
      exact hstep

/-- The identity field is `T`-covariant for any `T`: at `m = 0` both sides vanish because `T`
cancels against itself, and elsewhere because `idField` does. -/
theorem DCovariant_idField (S : Module.End ℂ FockSF) :
    DCovariant S (idField : FormalDist (Module.End ℂ FockSF)) := by
  intro m
  by_cases h0 : m = 0
  · subst h0
    have e1 : (idField : FormalDist (Module.End ℂ FockSF)) 0 = 1 := by
      rw [idField_apply, if_pos rfl]; rfl
    have e2 : (idField : FormalDist (Module.End ℂ FockSF)) ((0 : ℤ) + 1) = 0 := by
      rw [idField_apply, if_neg (by norm_num)]
    rw [e1, e2, mul_one, one_mul, sub_self, smul_zero]
  · have e1 : (idField : FormalDist (Module.End ℂ FockSF)) m = 0 := by
      rw [idField_apply, if_neg h0]
    by_cases h1 : m + 1 = 0
    · rw [e1, mul_zero, zero_mul, sub_zero, h1, zero_smul]
    · have e2 : (idField : FormalDist (Module.End ℂ FockSF)) (m + 1) = 0 := by
        rw [idField_apply, if_neg h1]
      rw [e1, e2, mul_zero, zero_mul, sub_zero, smul_zero]

/-- Word fields are `T`-covariant. -/
theorem YwordSF_DCovariant : ∀ l : SFWord, DCovariant T (YwordSF l)
  | [] => by rw [YwordSF_nil]; exact DCovariant_idField T
  | (p :: rest) => by
      rw [YwordSF_cons]
      exact DCovariant.nprodε _ (sfGenField_isField p.2 p.1) (YwordSF_isField rest)
        (sfGenField_DCovariant p.2 p.1) (YwordSF_DCovariant rest)

/-! ## The creation tower -/

/-- **Creation tower (power-series part)**: `(YwordSF l)_q |0⟩ = 0` for `q < 0`. -/
theorem YwordSF_vacuum_neg (l : SFWord) : ∀ {q : ℤ}, q < 0 → (YwordSF l) q vacSF = 0 := by
  induction l with
  | nil =>
      intro q hq
      rw [YwordSF_nil]
      change (if q = 0 then (LinearMap.id : Module.End ℂ FockSF) else 0) vacSF = 0
      rw [if_neg (by omega : ¬ q = 0)]; rfl
  | cons p rest ih =>
      intro q hq
      rw [YwordSF_cons]
      exact nprodε_vacuum_neg_gen _ (sfGenField_isField p.2 p.1) (YwordSF_isField rest)
        vacSF (fun s hs => sfGenField_vacuum_neg p.2 p.1 hs) (fun s hs => ih hs) hq

/-- **Creation tower (base)**: the word field creates its monomial from the vacuum. -/
theorem YwordSF_vacuum_base (l : SFWord) : (YwordSF l) 0 vacSF = stWordSF l := by
  induction l with
  | nil =>
      rw [YwordSF_nil]
      change (if (0 : ℤ) = 0 then (LinearMap.id : Module.End ℂ FockSF) else 0) vacSF
        = stWordSF []
      rw [if_pos rfl]; rfl
  | cons p rest ih =>
      rw [YwordSF_cons,
        nprodε_vacuum_base_gen _ (sfGenField_isField p.2 p.1) (YwordSF_isField rest)
          vacSF (fun s hs => sfGenField_vacuum_neg p.2 p.1 hs)
          (fun s hs => YwordSF_vacuum_neg rest hs),
        ih, sfGenField_zero, stWordSF_cons, chi, if_pos (by positivity)]
      change creBase (((p.1 : ℕ) : ℤ).toNat, p.2) (stWordSF rest)
        = ι QSF (Finsupp.single p (1 : ℂ)) * stWordSF rest
      rw [creBase, Int.toNat_natCast]
      rfl

end VOA.SympFerm
