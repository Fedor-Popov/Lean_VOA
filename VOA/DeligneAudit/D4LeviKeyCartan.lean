import VOA.DeligneAudit.D4LeviKeyCartanTable

/-! Cartan eigenvalues of six-letter radical words and key layers. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

theorem keyLabel_cons (m : ℕ) (i : Fin 3) (j : Fin 6)
    (s : ℕ) (l : List (Fin 6 × ℕ)) :
    keyLabel m i (wordKey ((j, s) :: l)) =
      keyLabel m i (wordKey l) + letterWeight i j := by
  fin_cases i <;> fin_cases j <;>
    simp [keyLabel, letterWeight, wordKey] <;> ring

theorem cartan_radical_coefficient (i : Fin 3) (j : Fin 6) :
    VOA.DeligneAudit.DeligneSector.D4.fD4
      (leviColour (VOA.DeligneAudit.A3Sector.simpleH i))
      (radicalColour j) (radicalColour j) = (letterWeight i j : ℂ) := by
  by_cases hzero : letterWeight i j = 0
  · simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ,
      cartan_radical_bracket, sget, hzero]
  · simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ,
      cartan_radical_bracket, sget, hzero]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

theorem cartan_radical_comm (i : Fin 3) (j : Fin 6) (r s : ℕ) (v : V) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r
        (ρ.op (radicalColour j) s v) -
      ρ.op (radicalColour j) s
        (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) r v) =
      (letterWeight i j : ℂ) • ρ.op (radicalColour j) (r + s) v := by
  rw [ρ.comm]
  have hcoeff : ∀ z : Fin 28,
      D4sector.f (leviColour (VOA.DeligneAudit.A3Sector.simpleH i))
        (radicalColour j) z =
          if z = radicalColour j then (letterWeight i j : ℂ) else 0 := by
    intro z
    by_cases hz : z = radicalColour j
    · subst z
      simpa using cartan_radical_coefficient i j
    · simp only [hz, ↓reduceIte]
      exact cartan_radical_support i j z hz
  simp_rw [hcoeff]
  simp only [ite_smul, zero_smul]
  change (Finset.univ : Finset (Fin 28)).sum
    (fun x => if x = radicalColour j then
      (letterWeight i j : ℂ) • ρ.op x (r + s) v else 0) = _
  rw [Finset.sum_ite_eq']
  simp

/-- The source vector has sl4 highest weight (0,m,0) in the raw D4 Cartan colours. -/
theorem source_cartan (m : ℕ)
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) 0 w =
      ((if i = 1 then m else 0 : ℕ) : ℂ) • w := by
  have h' := (source_localWeyl ρ w m h).cartan_zero i
  fin_cases i <;>
    simpa [leviCurrent, leviSign, leviColour,
      VOA.DeligneAudit.A3Sector.simpleH,
      VOA.DeligneAudit.A3Sector.weightABC] using h'

/-- Every radical word has the integer Cartan labels recorded by its key. -/
theorem cartan_weight_word (m : ℕ)
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) (l : List (Fin 6 × ℕ)) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) 0
        (radicalWord ρ w l) =
      (keyLabel m i (wordKey l) : ℂ) • radicalWord ρ w l := by
  induction l with
  | nil =>
      have hs := source_cartan ρ w m h i
      fin_cases i <;> simpa [radicalWord, wordKey, keyLabel] using hs
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      have hc := cartan_radical_comm ρ i j 0 s (radicalWord ρ w l)
      have heq : radicalWord ρ w ((j, s) :: l) =
          ρ.op (radicalColour j) s (radicalWord ρ w l) := rfl
      rw [heq, sub_eq_iff_eq_add.mp hc, ih, keyLabel_cons]
      simp only [Int.cast_add, add_smul, map_smul, zero_add]
      abel

/-- The entire exact key layer is a simultaneous sl4 Cartan eigenspace. -/
theorem cartan_weight_key (m : ℕ)
    (h : VOA.DeligneAudit.UnivG.Sat D4sector.f ρ w
      (VOA.DeligneAudit.UnivG.ravFam D4sector m 0))
    (i : Fin 3) (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH i)) 0 v =
      (keyLabel m i k : ℂ) • v := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hk, rfl⟩ := hz
      simpa [← hk] using cartan_weight_word ρ w m h i l
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy, smul_add]
  | smul c x _ hx =>
      rw [map_smul, hx]
      exact smul_comm c (keyLabel m i k : ℂ) x

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyLabel_cons
#print axioms VOA.DeligneAudit.D4Levi.cartan_radical_coefficient
#print axioms VOA.DeligneAudit.D4Levi.cartan_radical_comm
#print axioms VOA.DeligneAudit.D4Levi.source_cartan
#print axioms VOA.DeligneAudit.D4Levi.cartan_weight_word
#print axioms VOA.DeligneAudit.D4Levi.cartan_weight_key
