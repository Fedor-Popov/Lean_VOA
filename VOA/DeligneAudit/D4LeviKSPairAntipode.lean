import VOA.DeligneAudit.D4LeviKSIndependent

/-! Iterated antipode transfer for f3 modes modulo a higher-key orbit. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The right-to-left word of current modes. -/
noncomputable def pairModeWord (F : ℕ → Module.End ℂ V)
    (rs : List ℕ) : Module.End ℂ V :=
  (rs.map F).prod

/-- Moving one mode from the right of an operator to its left changes the
    commutator sign. Iteration retains the order of the input modes. -/
noncomputable def pairAntipode (F : ℕ → Module.End ℂ V) :
    List ℕ → Module.End ℂ V → Module.End ℂ V
  | [], A => A
  | r :: rs, A => pairAntipode F rs (A * F r - F r * A)

/-- Iterated ordinary commutator action of the modes on a word operator. -/
noncomputable def pairAdjoint (F : ℕ → Module.End ℂ V) :
    List ℕ → Module.End ℂ V → Module.End ℂ V
  | [], A => A
  | r :: rs, A => pairAdjoint F rs (F r * A - A * F r)

theorem pairAdjoint_neg (F : ℕ → Module.End ℂ V)
    (rs : List ℕ) (A : Module.End ℂ V) :
    pairAdjoint F rs (-A) = -pairAdjoint F rs A := by
  induction rs generalizing A with
  | nil => rfl
  | cons r rs ih =>
      simp only [pairAdjoint]
      have h : F r * -A - -A * F r = -(F r * A - A * F r) := by
        simp only [mul_neg, neg_mul]
        abel
      rw [h, ih]

/-- The antipode sign is exactly one minus sign per transferred mode. -/
theorem pairAntipode_eq_sign (F : ℕ → Module.End ℂ V)
    (rs : List ℕ) (A : Module.End ℂ V) :
    pairAntipode F rs A =
      (-1 : ℂ) ^ rs.length • pairAdjoint F rs A := by
  induction rs generalizing A with
  | nil => simp [pairAntipode, pairAdjoint]
  | cons r rs ih =>
      rw [pairAntipode, ih]
      have h : A * F r - F r * A = -(F r * A - A * F r) := by abel
      rw [h, pairAdjoint_neg]
      simp only [pairAdjoint, List.length_cons, pow_succ]
      simp [smul_neg, neg_smul]

/-- Each intermediate source needed by the iterated transfer lies in N.
    In the D4 application these are strictly higher radical keys. -/
def pairTransferSources (N : Submodule ℂ V)
    (F : ℕ → Module.End ℂ V) (v : V) :
    List ℕ → Module.End ℂ V → Prop
  | [], _ => True
  | r :: rs, A =>
      A (pairModeWord F rs v) ∈ N ∧
        pairTransferSources N F v rs (A * F r - F r * A)

/-- The iterated antipode identity in any current-module quotient stable
    under the chosen modes. -/
theorem pairAntipode_mod (N : Submodule ℂ V)
    (F : ℕ → Module.End ℂ V) (v : V)
    (hInv : ∀ r x, x ∈ N → F r x ∈ N)
    (rs : List ℕ) (A : Module.End ℂ V)
    (hSources : pairTransferSources N F v rs A) :
    A (pairModeWord F rs v) - pairAntipode F rs A v ∈ N := by
  induction rs generalizing A with
  | nil =>
      simp [pairModeWord, pairAntipode]
  | cons r rs ih =>
      rcases hSources with ⟨hSource, hRest⟩
      let B : Module.End ℂ V := A * F r - F r * A
      have hMove :
          A (pairModeWord F (r :: rs) v) -
            B (pairModeWord F rs v) ∈ N := by
        have heq :
            A (pairModeWord F (r :: rs) v) -
              B (pairModeWord F rs v) =
                F r (A (pairModeWord F rs v)) := by
          simp only [pairModeWord, List.map_cons, List.prod_cons,
            Module.End.mul_apply, B, LinearMap.sub_apply]
          abel
        rw [heq]
        exact hInv r _ hSource
      have hTail :
          B (pairModeWord F rs v) - pairAntipode F rs B v ∈ N :=
        ih B hRest
      have hsum := N.add_mem hMove hTail
      change A (pairModeWord F (r :: rs) v) -
        pairAntipode F (r :: rs) A v ∈ N
      rw [pairAntipode]
      change A (pairModeWord F (r :: rs) v) -
        pairAntipode F rs B v ∈ N
      convert hsum using 1; abel

/-- The f3 current specialization of the iterated transfer at a D4 key. -/
theorem fThree_antipode_iterated_higher
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (k : RadicalKey) (rs : List ℕ) (A : Module.End ℂ V) (v : V)
    (hSources : pairTransferSources (higherOrbit ρ w m k)
      (ρ.op (17 : Fin 28)) v rs A) :
    A (pairModeWord (ρ.op (17 : Fin 28)) rs v) -
      pairAntipode (ρ.op (17 : Fin 28)) rs A v ∈
        higherOrbit ρ w m k := by
  apply pairAntipode_mod (higherOrbit ρ w m k)
    (ρ.op (17 : Fin 28)) v
  · intro r x hx
    exact higherOrbit_full_levi_inv ρ w m k (17 : Fin 28)
      ⟨7, rfl⟩ r hx
  · exact hSources

/-- Signed form of the f3 transfer identity used in the PAIR argument. -/
theorem fThree_antipode_signed_higher
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (k : RadicalKey) (rs : List ℕ) (A : Module.End ℂ V) (v : V)
    (hSources : pairTransferSources (higherOrbit ρ w m k)
      (ρ.op (17 : Fin 28)) v rs A) :
    A (pairModeWord (ρ.op (17 : Fin 28)) rs v) -
      (-1 : ℂ) ^ rs.length •
        pairAdjoint (ρ.op (17 : Fin 28)) rs A v ∈
          higherOrbit ρ w m k := by
  simpa only [pairAntipode_eq_sign, LinearMap.smul_apply] using
    fThree_antipode_iterated_higher ρ w m k rs A v hSources

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairAntipode_mod
#print axioms VOA.DeligneAudit.D4Levi.fThree_antipode_iterated_higher
#print axioms VOA.DeligneAudit.D4Levi.pairAdjoint_neg
#print axioms VOA.DeligneAudit.D4Levi.pairAntipode_eq_sign
#print axioms VOA.DeligneAudit.D4Levi.fThree_antipode_signed_higher
