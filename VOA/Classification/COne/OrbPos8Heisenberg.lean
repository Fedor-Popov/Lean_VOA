import VOA.Classification.COne.OrbPos3Conjugate
import VOA.Classification.COne.DongMasonCOne

/-!
# Heisenberg decomposition of arbitrary inner-twisted modules

Unlike the explicit shifted construction, the input here is an arbitrary
ordinary twisted module. Restriction to the cyclic fixed algebra supplies
positive-energy Heisenberg modes. No classification hypothesis is used.
-/

namespace VOA.Classification.COne.OrbPos8
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN
open OrbPos2 DMCOne

section Admissible
variable {V M : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Positive-energy Heisenberg restriction works for any admissible module
and any unit-normalized weight-one Heisenberg vector. -/
noncomputable def heisenbergOfAdmissible (N : AdmissibleModule W M)
    {h : V} (hh : IsHeisVector W h) : HeisSvN.HeisRep M where
  a n := mode (N.YM h) n
  κ := 1
  κ_ne := one_ne_zero
  comm p q := by
    ext x
    have hc := heis_comm_of N.toWeakModule hh p q x
    simpa only [WeakModule.act_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, mul_one] using hc
  bdd x := by
    obtain ⟨K, hK⟩ := N.truncation h x
    exact ⟨K.toNat, fun n hn => hK n (by omega)⟩
  nilp x n hn := by
    have hx : x ∈ ⨆ k, N.lev k := by rw [N.lev_iSup_eq_top]; trivial
    induction hx using Submodule.iSup_induction' with
    | mem k y hy =>
      have hlev : ∀ J : ℕ, (mode (N.YM h) n ^ J) y ∈ N.lev (k - n * J) := by
        intro J
        induction J with
        | zero => simpa using hy
        | succ J ih =>
          rw [pow_succ', Module.End.mul_apply]
          have hl := N.act_lev hh.mem ih (p := n)
          convert hl using 2
          push_cast; ring
      refine ⟨k.toNat + 1, ?_⟩
      have hl := hlev (k.toNat + 1)
      have hle : ((k.toNat + 1 : ℕ) : ℤ) ≤ n * ((k.toNat + 1 : ℕ) : ℤ) :=
        le_mul_of_one_le_left (by positivity) (by omega)
      rw [N.lev_eq_bot_of_neg _ (by push_cast at hle ⊢; omega), Submodule.mem_bot] at hl
      exact hl
    | zero => exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨Jy, hJy⟩ := hy
      obtain ⟨Jz, hJz⟩ := hz
      refine ⟨Jy + Jz, ?_⟩
      have e1 : (mode (N.YM h) n ^ (Jy + Jz)) y = 0 := by
        rw [add_comm, pow_add, Module.End.mul_apply, hJy, map_zero]
      have e2 : (mode (N.YM h) n ^ (Jy + Jz)) z = 0 := by
        rw [pow_add, Module.End.mul_apply, hJz, map_zero]
      rw [map_add, e1, e2, add_zero]

end Admissible

section Twisted
variable {V M : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {g : Aut W} {n : ℕ}

/-- Restriction to the actual cyclic fixed algebra, with the original weights. -/
noncomputable def cyclicRestriction (P : TwistedModule g n M) (hn : 0 < n) :
    OrdVModule (orbifoldVOA (Subgroup.zpowers g)) M :=
  restrictedOrdModule P hn (orbifold (Subgroup.zpowers g))
    (fun v => (mem_orbifold_zpowers_iff g v.1).mp v.2)

/-- A fixed Heisenberg current remains a unit Heisenberg vector in the fixed algebra. -/
theorem fixed_isHeisVector {h : V} (hh : IsHeisVector W h) (hg : g h = h) :
    IsHeisVector (orbifoldVOA (Subgroup.zpowers g))
      ⟨h, (mem_orbifold_zpowers_iff g h).mpr hg⟩ := by
  refine ⟨hh.mem, ?_⟩
  apply Subtype.ext
  exact hh.one

/-- The Heisenberg operators of an arbitrary twisted module, when the
automorphism fixes the current. -/
noncomputable def twistedHeisenberg (P : TwistedModule g n M) (hn : 0 < n)
    {h : V} (hh : IsHeisVector W h) (hg : g h = h) : HeisSvN.HeisRep M :=
  heisenbergOfAdmissible (cyclicRestriction P hn).toAdmissible (fixed_isHeisVector hh hg)

@[simp] theorem twistedHeisenberg_a (P : TwistedModule g n M) (hn : 0 < n)
    {h : V} (hh : IsHeisVector W h) (hg : g h = h) (k : ℤ) :
    (twistedHeisenberg P hn hh hg).a k = P.YM h ((n : ℤ) * k) := by
  exact mode_restrictedFields P _ _ k

/-- Every such twisted module is the full oscillator Fock space over its
Heisenberg vacuum space. This does not yet identify the charge orbit in that space. -/
theorem twisted_fock_decomposition (P : TwistedModule g n M) (hn : 0 < n)
    {h : V} (hh : IsHeisVector W h) (hg : g h = h) :
    Function.Bijective (twistedHeisenberg P hn hh hg).fockMap ∧
      ∀ f, (twistedHeisenberg P hn hh hg).fockMap
        (Finsupp.mapRange.linearMap (twistedHeisenberg P hn hh hg).vacZero f) =
        P.YM h 0 ((twistedHeisenberg P hn hh hg).fockMap f) := by
  refine ⟨⟨(twistedHeisenberg P hn hh hg).fockMap_injective,
    (twistedHeisenberg P hn hh hg).fockMap_surjective⟩, ?_⟩
  intro f
  simpa using (twistedHeisenberg P hn hh hg).fockMap_vacZero f

/-- The Heisenberg vacuum space of a nonzero twisted module is nonzero. -/
theorem twisted_vac_ne_bot (P : TwistedModule g n M) (hn : 0 < n)
    {h : V} (hh : IsHeisVector W h) (hg : g h = h) [Nontrivial M] :
    (twistedHeisenberg P hn hh hg).vac ≠ ⊥ := by
  intro hz
  have ht := (twistedHeisenberg P hn hh hg).eq_top_of_vac_le ⊥ (le_of_eq hz)
    (fun k _ x hx => by rw [(Submodule.mem_bot ℂ).mp hx, map_zero]; exact Submodule.zero_mem _)
  exact bot_ne_top ht

end Twisted

/-- Torus automorphisms fix the unit-normalized lattice current. -/
theorem charU_hb (u : ℂˣ) : charU 1 le_rfl u (hb 1) = hb 1 := by
  change charU 1 le_rfl u (latStateGen (latP 1) _ 0) = _
  rw [charU_latStateGen, show ci 1 (0 : (latP 1).carrier) = 0 from rfl,
    zpow_zero, Units.val_one, one_smul]
  rfl

section Torus
variable {M : Type} [AddCommGroup M] [Module ℂ M] {u : ℂˣ} {n : ℕ}

/-- Canonical Heisenberg representation of an arbitrary torus-twisted V₂-module. -/
noncomputable def torusHeisenberg (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) : HeisSvN.HeisRep M :=
  twistedHeisenberg P hn (V2m_isHeisVector 1 le_rfl) (charU_hb u)

@[simp] theorem torusHeisenberg_a (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) (k : ℤ) :
    (torusHeisenberg P hn).a k = P.YM (hb 1) ((n : ℤ) * k) :=
  twistedHeisenberg_a P hn _ _ k

/-- Unconditional Fock decomposition for arbitrary torus-twisted V₂-modules,
at every positive period. Irreducibility and exact order are unnecessary here. -/
theorem torus_fock_decomposition (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) : Function.Bijective (torusHeisenberg P hn).fockMap ∧
      ∀ f, (torusHeisenberg P hn).fockMap
        (Finsupp.mapRange.linearMap (torusHeisenberg P hn).vacZero f) =
        P.YM (hb 1) 0 ((torusHeisenberg P hn).fockMap f) :=
  twisted_fock_decomposition P hn _ _

end Torus
end VOA.Classification.COne.OrbPos8
