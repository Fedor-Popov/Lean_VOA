/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.NonlinearMR

/-!
# Presentations of vertex algebras: generators, OPEs, and strong relations

The L3 layer of the presentation doctrine (2026-08): a vertex algebra is *introduced* by

* a set of strong generators with weights and parities and a singular-OPE table
  (`OPEData`, the L1/L2 datum), and
* a **finite list of strong relations** — the null fields whose vanishing makes the OPE
  associative (Gaberdiel–Kausch's `N^a`, `N^{ab}` for the triplet; Linshaw's null fields
  for degenerate nonlinear conformal algebras, arXiv:1710.02275 §3.1).

`VAPresentation` packages both.  ⚠ **Anti-circularity discipline** (the `MVir = ker Φ`
lesson): `relVal` is *literal data* — rational-coefficient combinations of explicit
words — never the kernel of a map to a model.  This file's import chain contains no
lattice or model file, and concrete presentation data must keep it that way.

## The relation ideal

Listed relations must be closed under everything the vertex structure can do to them:
`T`, left multiplication (creation modes), and the extended `N`/`P` actions **on both
sides** — Linshaw's `M′(A)`-closure.  Since `N` and `P` on composites exist only through
the `NPExtension` interface, the closure is the inductive predicate `InRelIdeal`
(constructors `of`/`zero`/`add`/`smul`/`tstab`/`nLeft`/`nRight`/`pLeft`/`pRight`), and
`RelIdeal` is the resulting submodule.  Left multiplication by arbitrary elements is a
*theorem* (`RelIdeal_left`): a word acts one letter at a time through `N_gv`.

The full presentation ideal is `MPresCar = MRfullCar ⊔ RelIdeal`, an `NMIdeal`
(`MPres`), and the presented object is the quotient `UPres = T(R)/MPres` — with the
whole `Core.NonlinearConformal` quotient machinery available through
`NMIdeal.toMIdeal`.  **L2 recovery is a theorem** (`MPres_empty`): with no listed
relations the closure collapses to `0` and `MPres = MRfull`, De Sole–Kac exactly; over
a linear datum it collapses further to `MRtwoCar` (`MPres_empty_linear`) — the precise
sense in which L1 data feeds L2 automatically.

## ⚠ The vacuum-survival guard needs a third hypothesis

A natural **model-free** guard would be: `IsConformal` + homogeneous
positive-weight relations ⟹ `1 ∉ MPres`, possibly with the `NPGraded`
hypothesis added.  **Neither is enough**: the `pLeft`/`pRight` closure can reach
weight `0`.  Counterexample (`one_mem_relIdeal_omegaRel`): over `virasoroOPE c` with
`c ≠ 0`, the presentation listing the conformal vector itself as its one relation
(`omegaRelPresentation` — homogeneous of positive weight `2`, conformal datum) has
`P(L, L)(3) = (c/2)·1` in its relation ideal, so `1 ∈ RelIdeal` and the vacuum dies —
as it must: setting `ω = 0` at `c ≠ 0` kills the algebra.

⚠ **Read the modality exactly.**  `RelIdeal` is not even definable without an
interface term, so the refutation is stated *for every* `NP : NPExtension (virasoroOPE c)`
and is therefore a **conditional** refutation: it refutes the model-free guard *given
any* interface term, hence unconditionally once one is constructed.  Since no
`NPExtension` is inhabited anywhere in the library, these three theorems are — as Lean
propositions — vacuously true, and on their own they refute nothing.  What is
unconditional is the underlying mathematics (`ω = 0` at `c ≠ 0` kills the algebra) and
the design consequence: do **not** rely on a model-free vacuum guard.

The guard therefore carries one more named hypothesis,
`RelBracketVacuumFree` — the λ-bracket slices of relation-ideal elements stay in
positive weight — which holds whenever the relations are genuinely null in some model
(a model discharges it through `hRel`), and which `not_relBracketVacuumFree_omegaRel`
shows is not derivable from `IsConformal + NPGraded` (again, given an interface term).
With it, the guard is a theorem: `vacU_ne_zero_MPres`.

No `sorry`, no `admit`, no `native_decide`, no new axiom; `VOA.pbw` is not used.
-/

namespace VOA.NonlinearConformal

open Module (End)
open NPExtension

set_option maxRecDepth 4000

universe u

variable {ι : Type u}

/-! ## §1  The presentation datum -/

/-- **A vertex algebra presentation**: an OPE datum together with a finite list of
strong relations, each a *literal* element of `T(R)` (⚠ never `ker` of anything — the
anti-circularity discipline), homogeneous of a declared positive weight.

In the quotient `UPres` the word states are iterated creation modes on the vacuum
(`wstU`, `creHalf`), so a null state such as `L₋₃W₋₃|0⟩` is literally the word
`gv (L,1) * gv (W,0)` — no separate encoding of states is needed. -/
structure VAPresentation (ι : Type u) extends OPEData ι where
  /-- the index type of the listed strong relations -/
  relIdx : Type
  /-- the relation list is finite.  ⚠ Carried for the intended reading ("a finite list
  of strong relations") and for the finite check in a model; **no theorem in the
  library uses it**, so finiteness is not established content of anything proved here. -/
  relFin : Fintype relIdx
  /-- the listed relations, as literal elements of `T(R)` -/
  relVal : relIdx → TR ι
  /-- the conformal weight of each relation -/
  relWt : relIdx → ℕ
  /-- relation weights are positive -/
  relWt_pos : ∀ r, 0 < relWt r
  /-- each relation is homogeneous of its declared weight -/
  relVal_homog : ∀ r, relVal r ∈ gr wt (relWt r)

/-! ## §2  The relation ideal -/

/-- **The inductive closure of the listed relations** under everything the vertex
structure can do to them: the submodule operations, `T`, and the extended `N`/`P`
actions on both sides — Linshaw's `M′(A)`-closure (arXiv:1710.02275 §3.1), with `N` and
`P` supplied by the `NPExtension` interface.  Left multiplication is subsumed:
`N(a, X) = a·X` for a letter `a` (`N_gv`), so `nLeft` acting letter by letter gives
arbitrary left multiples (`RelIdeal_left`). -/
inductive InRelIdeal (P : VAPresentation ι) (NP : NPExtension P.toOPEData) : TR ι → Prop
  | of (r : P.relIdx) : InRelIdeal P NP (P.relVal r)
  | zero : InRelIdeal P NP 0
  | add {x y : TR ι} : InRelIdeal P NP x → InRelIdeal P NP y → InRelIdeal P NP (x + y)
  | smul (c : ℂ) {x : TR ι} : InRelIdeal P NP x → InRelIdeal P NP (c • x)
  | tstab {x : TR ι} : InRelIdeal P NP x → InRelIdeal P NP (Ttr x)
  | nLeft (A : TR ι) {x : TR ι} : InRelIdeal P NP x → InRelIdeal P NP (NP.N A x)
  | nRight (A : TR ι) {x : TR ι} : InRelIdeal P NP x → InRelIdeal P NP (NP.N x A)
  | pLeft (A : TR ι) (n : ℕ) {x : TR ι} : InRelIdeal P NP x → InRelIdeal P NP (NP.P A x n)
  | pRight (A : TR ι) (n : ℕ) {x : TR ι} : InRelIdeal P NP x → InRelIdeal P NP (NP.P x A n)

variable (P : VAPresentation ι) (NP : NPExtension P.toOPEData)

/-- The relation ideal as a submodule: the closure is already `ℂ`-linear. -/
noncomputable def RelIdeal : Submodule ℂ (TR ι) where
  carrier := {x | InRelIdeal P NP x}
  add_mem' := InRelIdeal.add
  zero_mem' := InRelIdeal.zero
  smul_mem' := fun c _ hx => InRelIdeal.smul c hx

theorem mem_RelIdeal {x : TR ι} : x ∈ RelIdeal P NP ↔ InRelIdeal P NP x := Iff.rfl

theorem relVal_mem_RelIdeal (r : P.relIdx) : P.relVal r ∈ RelIdeal P NP :=
  InRelIdeal.of r

/-- A basis word acts on the relation ideal one letter at a time, through `N_gv`. -/
theorem wbasis_mul_mem_RelIdeal (l : List (GenIdx ι)) {x : TR ι}
    (hx : InRelIdeal P NP x) :
    InRelIdeal P NP (wbasis ι (FreeMonoid.ofList l) * x) := by
  induction l with
  | nil =>
      rw [show FreeMonoid.ofList ([] : List (GenIdx ι)) = 1 from rfl, wbasis_one, one_mul]
      exact hx
  | cons a l ih =>
      have hsplit : wbasis ι (FreeMonoid.ofList (a :: l))
          = gv a * wbasis ι (FreeMonoid.ofList l) := by
        rw [show FreeMonoid.ofList (a :: l) = FreeMonoid.of a * FreeMonoid.ofList l from rfl,
          wbasis_mul, gv]
      rw [hsplit, mul_assoc, ← NP.N_gv]
      exact InRelIdeal.nLeft (gv a) ih

/-- **The relation ideal is closed under arbitrary left multiplication** — a theorem,
not a constructor: `nLeft` with single letters (through `N_gv`) generates it. -/
theorem RelIdeal_left (A x : TR ι) (hx : x ∈ RelIdeal P NP) : A * x ∈ RelIdeal P NP := by
  have hA : A ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
    rw [(wbasis ι).span_eq]; trivial
  induction hA using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      have h := wbasis_mul_mem_RelIdeal P NP (FreeMonoid.toList w) hx
      rwa [show FreeMonoid.ofList (FreeMonoid.toList w) = w from rfl] at h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

theorem RelIdeal_Tstable (x : TR ι) (hx : x ∈ RelIdeal P NP) : Ttr x ∈ RelIdeal P NP :=
  InRelIdeal.tstab hx

/-! ## §3  The presentation ideal and the presented object -/

/-- **The presentation ideal**: the full De Sole–Kac ideal joined with the relation
ideal. -/
noncomputable def MPresCar : Submodule ℂ (TR ι) := MRfullCar NP ⊔ RelIdeal P NP

theorem MRfullCar_le_MPresCar : MRfullCar NP ≤ MPresCar P NP := le_sup_left

theorem RelIdeal_le_MPresCar : RelIdeal P NP ≤ MPresCar P NP := le_sup_right

/-- **The presentation ideal is an admissible full-relation ideal**, so the entire
quotient machinery of `Core.NonlinearConformal` applies to the presented object through
`NMIdeal.toMIdeal`. -/
noncomputable def MPres : NMIdeal P.toOPEData NP where
  car := MPresCar P NP
  left := fun A x hx => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [mul_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (MRfullCar_left NP A y hy))
      (Submodule.mem_sup_right (RelIdeal_left P NP A z hz))
  Tstable := fun x hx => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Ttr_mem_MRfullCar NP y hy))
      (Submodule.mem_sup_right (RelIdeal_Tstable P NP z hz))
  relD_mem := fun p q w =>
    Submodule.mem_sup_left (relDF_mem_MRfullCar NP p q (wbasis ι w))

/-- **The presented object**: the quotient of `T(R)` by the presentation ideal.  For
`relIdx = Empty` this is De Sole–Kac's `U(R)` (over the interface); with relations it is
the L3 object whose simple quotient is *the* VOA of the presentation
(`Core.PresentationDoctrine`). -/
noncomputable abbrev UPres : Type u := UR (MPres P NP).toMIdeal

/-! ## §4  L2 recovery at the empty relation list -/

/-- With no listed relations the inductive closure collapses to `0`: every constructor
is linear and there is nothing to start from. -/
theorem InRelIdeal.eq_zero (h : IsEmpty P.relIdx) {x : TR ι}
    (hx : InRelIdeal P NP x) : x = 0 := by
  induction hx with
  | of r => exact h.elim r
  | zero => rfl
  | add _ _ ihx ihy => rw [ihx, ihy, add_zero]
  | smul c _ ih => rw [ih, smul_zero]
  | tstab _ ih => rw [ih, map_zero]
  | nLeft A _ ih => rw [ih, map_zero]
  | nRight A _ ih => rw [ih, map_zero]; exact LinearMap.zero_apply A
  | pLeft A n _ ih => rw [ih, map_zero]; exact Pi.zero_apply n
  | pRight A n _ ih => rw [ih, map_zero, LinearMap.zero_apply]; exact Pi.zero_apply n

theorem RelIdeal_eq_bot (h : IsEmpty P.relIdx) : RelIdeal P NP = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  exact InRelIdeal.eq_zero P NP h hx

/-- **L2 recovery**: with no listed relations the presentation ideal is exactly De
Sole–Kac's `M(R)` — the L3 layer degenerates to the L2 layer definitionally. -/
theorem MPres_empty (h : IsEmpty P.relIdx) : MPresCar P NP = MRfullCar NP := by
  rw [MPresCar, RelIdeal_eq_bot P NP h, sup_bot_eq]

/-- L2 recovery over a **linear** datum: the presentation ideal is the two-sided ideal
of `Core.NonlinearVirasoro` §4 — the precise sense in which L1 data feeds the L2/L3
machinery automatically.  ⚠ Parametric in `NP` (no instance is constructed). -/
theorem MPres_empty_linear (h : IsEmpty P.relIdx) (hD : P.toOPEData.IsLinear) :
    MPresCar P NP = MRtwoCar P.toOPEData := by
  rw [MPres_empty P NP h, MRfullCar_eq_MRtwoCar hD NP]

/-! ## §5  The vacuum-survival guard, with its honest hypothesis

See the module docstring: the guard is **not** model-free.  `RelBracketVacuumFree` is
the missing named hypothesis, refutable without a model (`omegaRelPresentation` below)
and dischargeable from nullity in any model. -/

/-- **The guard hypothesis**: every λ-bracket slice of a relation-ideal
element stays in positive weight.  This is what nullity in a model buys structurally
(a null field's brackets are null, hence have no vacuum component), and it is exactly
what the `pLeft`/`pRight` closure needs for the augmentation argument.
⚠ NOT derivable from `IsConformal + NPGraded` — see
`not_relBracketVacuumFree_omegaRel`. -/
def RelBracketVacuumFree : Prop :=
  ∀ (A x : TR ι) (n : ℕ), InRelIdeal P NP x →
    NP.P A x n ∈ grPos P.wt ∧ NP.P x A n ∈ grPos P.wt

/-- Under `NPGraded` and the corrected guard hypothesis, the relation ideal lies in
the positive-weight span.  (`IsConformal` is not needed for this half: homogeneity of
the listed relations is a field of the presentation.) -/
theorem RelIdeal_le_grPos (hg : NPGraded NP) (hvf : RelBracketVacuumFree P NP) :
    RelIdeal P NP ≤ grPos P.wt := by
  intro x hx
  induction hx with
  | of r => exact gr_le_grPos (P.relWt_pos r) (P.relVal_homog r)
  | zero => exact Submodule.zero_mem _
  | add _ _ ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul c _ ih => exact Submodule.smul_mem _ c ih
  | tstab _ ih => exact Ttr_mem_grPos P.wt _
  | nLeft A hx ih => exact N_mem_grPos_right hg A ih
  | nRight A hx ih => exact N_mem_grPos_left hg A ih
  | pLeft A n hx _ => exact (hvf A _ n hx).1
  | pRight A n hx _ => exact (hvf A _ n hx).2

/-- The presentation ideal lies in the positive-weight span. -/
theorem MPres_le_grPos (hC : P.toOPEData.IsConformal) (hg : NPGraded NP)
    (hvf : RelBracketVacuumFree P NP) : MPresCar P NP ≤ grPos P.wt :=
  sup_le (MRfull_le_grPos NP hC hg) (RelIdeal_le_grPos P NP hg hvf)

/-- The augmentation kills the presentation ideal. -/
theorem aug_MPres (hC : P.toOPEData.IsConformal) (hg : NPGraded NP)
    (hvf : RelBracketVacuumFree P NP) : ∀ x ∈ MPresCar P NP, aug x = 0 :=
  fun x hx => aug_grPos x (MPres_le_grPos P NP hC hg hvf hx)

/-- **The vacuum survives the presented quotient** — the vacuum-survival
guard, with every hypothesis named and visible: exact conformal weight (`hC`), graded
interface (`hg`, dischargeable only by the [DK] recursion), and vacuum-free relation
brackets (`hvf`, dischargeable by nullity in a model).  No PBW anywhere. -/
theorem vacU_ne_zero_MPres (hC : P.toOPEData.IsConformal) (hg : NPGraded NP)
    (hvf : RelBracketVacuumFree P NP) : vacU (MPres P NP).toMIdeal ≠ 0 :=
  vacU_ne_zero_of_aug (MPres P NP).toMIdeal (aug_MPres P NP hC hg hvf)

/-! ## §6  ⚠ The model-free guard is CONDITIONALLY FALSE: the ω-counterexample

The presentation over `virasoroOPE c` whose single listed relation is the conformal
vector itself.  It satisfies every hypothesis of the naive model-free guard —
conformal datum, one homogeneous relation of positive weight `2` — yet for `c ≠ 0` its
relation ideal contains `1`: the closure constructor `pLeft` reaches
`P(L, L)(3) = (c/2)·1` through `P_bot`.  Mathematically this is as it must be:
imposing `ω = 0` at central charge `c ≠ 0` kills the vertex algebra.  The
"model-free" guard, with or without `NPGraded`, is therefore insufficient; the honest guard is
§5's, with `RelBracketVacuumFree` as a third named hypothesis.

⚠ **Modality.**  All three theorems below take `NP : NPExtension (virasoroOPE c)` as a
hypothesis — `RelIdeal` cannot be written without one.  No `NPExtension` is inhabited
in the library, so as Lean propositions these are conditionals with an antecedent nobody
has supplied: they are vacuously true and refute nothing by themselves.  They
become genuine refutations as soon as an interface term is constructed, and the
mathematical content (and hence the design lesson) does not depend on that. -/

/-- The presentation listing the Virasoro conformal vector itself as its one strong
relation — the counterexample datum. -/
noncomputable def omegaRelPresentation (c : ℂ) : VAPresentation Unit :=
  { virasoroOPE c with
    relIdx := Unit
    relFin := inferInstanceAs (Fintype Unit)
    relVal := fun _ => gv ((), 0)
    relWt := fun _ => 2
    relWt_pos := fun _ => by norm_num
    relVal_homog := fun _ => gv_mem_gr (virasoroOPE c).wt ((), 0) }

/-- **`1` lies in the relation ideal of the ω-presentation** at every `c ≠ 0`, *given
any* interface term `NP`: `pLeft` produces `P(L,L)(3) = (c/2)·1`, and a scalar clears the
constant.  ⚠ Conditional on `NP` (see §6 header): vacuous until an instance is constructed. -/
theorem one_mem_relIdeal_omegaRel (c : ℂ) (hc : c ≠ 0)
    (NP : NPExtension (virasoroOPE c)) :
    (1 : TR Unit) ∈ RelIdeal (omegaRelPresentation c) NP := by
  have h0 : InRelIdeal (omegaRelPresentation c) NP (gv (((), 0) : GenIdx Unit)) :=
    InRelIdeal.of ()
  have h3 := InRelIdeal.pLeft (P := omegaRelPresentation c)
    (gv (((), 0) : GenIdx Unit)) 3 h0
  have hP : NP.P (gv (((), 0) : GenIdx Unit)) (gv ((), 0)) 3 = (c / 2) • (1 : TR Unit) := by
    rw [NP.P_bot]
    exact virasoro_ope_three c
  rw [hP] at h3
  have h1 := InRelIdeal.smul (P := omegaRelPresentation c) (2 / c) h3
  rw [smul_smul, div_mul_div_comm, mul_comm (2 : ℂ) c, div_self (by
    intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact hc h'
    · norm_num at h'), one_smul] at h1
  exact h1

/-- **The augmentation does not kill the ω-relation ideal**: the naive model-free
vacuum guard is refuted — ⚠ given any interface term `NP`, hence conditionally until
an instance is constructed (see §6 header). -/
theorem aug_ne_zero_relIdeal_omegaRel (c : ℂ) (hc : c ≠ 0)
    (NP : NPExtension (virasoroOPE c)) :
    ∃ x ∈ RelIdeal (omegaRelPresentation c) NP, aug x ≠ 0 :=
  ⟨1, one_mem_relIdeal_omegaRel c hc NP, by rw [map_one]; exact one_ne_zero⟩

/-- **`RelBracketVacuumFree` is not derivable from `IsConformal + NPGraded`**: the
ω-presentation satisfies both (`virasoroOPE_isConformal`, and any graded interface
term), yet its guard hypothesis fails at every `c ≠ 0`.  This is why §5 carries `hvf`
as a separate named hypothesis.  ⚠ Conditional on `NP` (see §6 header). -/
theorem not_relBracketVacuumFree_omegaRel (c : ℂ) (hc : c ≠ 0)
    (NP : NPExtension (virasoroOPE c)) (hg : NPGraded NP) :
    ¬ RelBracketVacuumFree (omegaRelPresentation c) NP := by
  intro hvf
  have h1 : (1 : TR Unit) ∈ grPos (omegaRelPresentation c).wt :=
    RelIdeal_le_grPos (omegaRelPresentation c) NP hg hvf
      (one_mem_relIdeal_omegaRel c hc NP)
  have h0 := aug_grPos _ h1
  rw [map_one] at h0
  exact one_ne_zero h0

end VOA.NonlinearConformal
