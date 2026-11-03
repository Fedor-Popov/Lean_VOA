/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSSMoveC4Assembly
import VOA.Huang.DLNSmallMain
import VOA.Huang.DLNSmallTwoPower
import VOA.Huang.DLNSchur6Relations
import VOA.Huang.DLNBeylInflation
import VOA.Huang.NSCongruenceBridge
import VOA.Huang.ZhuRepInput

/-!
# The congruence property of nice VOAs, as named hypothesis-free theorems

Before this file the congruence property was discharged only inside proof terms
(e.g. `gannonRayhaun_forward`); every named declaration concluding `DLNCongruenceInput`,
`ZhuCongruenceInput` or `GaloisSymmetryNontrivialInput` took hypotheses. Here those statements are
stated with no hypotheses, assembled from proved pieces only.

* `dlnCongruenceInput_holds : DLNCongruenceInput` — **characters only**: for every nice VOA `V`
  (`Nice V := StronglyRational V ∧ PseudoUnitary V`), every modular datum `D` of `V`
  (`D.IsModularData`) and every level `N` of `D` (`D.IsLevel N`: `0 < N` and
  `N (h_a - c/24) ∈ ℤ` for all `a`), every character satisfies `ch_a (γ τ) = ch_a τ` for
  `γ ∈ Γ(N)`, `Im τ > 0`.
* `galoisSymmetryNontrivialInput_holds` — the Galois-symmetry clause for nontrivial `ℓ`
  (characters transform by a signed permutation under `γ ≡ diag(ℓ, ℓ⁻¹) mod N`).
* `zhuCongruenceInput_holds : ZhuCongruenceInput` — **kernel form**: for every nice `V`, every
  modular datum `D` and every Zhu datum `D'` on its labels (`IsZhuDatum D hD D'`), there is
  `L > 0` with `Γ(L) ⊆ ker D'.rep` (`KernelContainsGamma D'.rep L`), `D'.rep` being the genuine
  (not projective) matrix representation of `SL(2, ℤ)` from Zhu's modular invariance.
* `zhu_kernelContainsGamma_at_level` — the same kernel containment at **every** level `N` of `D`.

**Scope.** The categorical input is only the *kernel half* of Ng–Schauenburg CMP 300 (2010),
Theorem 6.8 (`DLNBridge.nsProjectiveKernelAll_holds`: for every modular category some `Γ(N)` acts
by scalars). The other half — that the level equals the Frobenius–Schur exponent and is
minimal (`NgSchauenburg.ProjectiveCongruenceTheorem`, `NSProjectiveCongruenceAll`) — is **not**
proved and is not used.
-/

namespace VOA.Huang.CongruenceNamed

open VOA.Huang

universe u

/-- **Dong–Lin–Ng congruence property, character form, together with the nontrivial
Galois-symmetry clause** — hypothesis-free. For every nice VOA (strongly rational and
pseudo-unitary), every modular datum `D` and every level `N` of `D`, the characters are
`Γ(N)`-invariant; and for `ℓ` invertible mod `N`, `ℓ ≢ ±1`, `γ ≡ diag(ℓ, ℓ⁻¹) (mod N)` acts on
characters by a signed permutation. Only the kernel half of Ng–Schauenburg 6.8 is used. -/
theorem dlnCongruence_and_galois_holds :
    CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  NSGaloisCore.dln_inputs_of_beyl
    (DLNSchur.oddPrimePowerSchur_iff_largePrimeGaussLowerRelations.mpr
      DLNSchur.largePrimeGaussLowerRelations)
    DLNSchur.twoPowerInflationFromTwo_holds

/-- **Dong–Lin–Ng congruence property (characters only)** — hypothesis-free. For every nice
VOA `V` (`StronglyRational V ∧ PseudoUnitary V`), every modular datum `D` with
`D.IsModularData`, every level `N` (`D.IsLevel N`), every `γ ∈ Γ(N)`, every label `a` and every
`τ` with `0 < τ.im`: `D.ch a (mobius γ τ) = D.ch a τ`. This is a statement about characters; the
kernel form is `zhuCongruenceInput_holds`. Only the kernel half of Ng–Schauenburg 6.8 is used
(not level = Frobenius–Schur exponent). -/
theorem dlnCongruenceInput_holds : CongruenceGaloisSplit.DLNCongruenceInput.{u} :=
  dlnCongruence_and_galois_holds.1

/-- **Galois symmetry for nontrivial `ℓ`** (Coste–Gannon; DLN Theorem II), for every nice
VOA — hypothesis-free. -/
theorem galoisSymmetryNontrivialInput_holds :
    CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dlnCongruence_and_galois_holds.2

/-- **Dong–Lin–Ng congruence property, kernel form** — hypothesis-free. For every nice VOA
`V` (`StronglyRational V ∧ PseudoUnitary V`), every modular datum `D` (`D.IsModularData`) and
every Zhu datum `D'` on its labels (`IsZhuDatum D hD D'`), Zhu's modular representation
`D'.rep : SL(2, ℤ) →* Matrix D.ι D.ι ℂ` satisfies `Γ(L) ⊆ ker D'.rep` for some `L > 0`.
Uses only the kernel half of Ng–Schauenburg 6.8 (`nsProjectiveKernelAll_holds`), not the
statement that the level is the Frobenius–Schur exponent. -/
theorem zhuCongruenceInput_holds : DLNBridge.ZhuCongruenceInput.{u} :=
  DLNBeyl.zhuCongruence_of_beyl
    (DLNSchur.beylInflationSL2_of_large DLNSchur.largePrimeGaussLowerRelations)
    (DLNBridge.zhuProjectiveCongruence_of_NSKernel DLNBridge.nsProjectiveKernelAll_holds
      ZhuRep.zhuModularRepresentationInput_holds)

/-- **`ker ρ_V ⊇ Γ(N)` at every level** — for a nice VOA `V`, a modular datum `D`, a Zhu
datum `D'` on its labels and any level `N` of `D`, Zhu's representation is trivial on `Γ(N)`. -/
theorem zhu_kernelContainsGamma_at_level {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {V : VertexOperatorAlgebra 𝒱} (hV : VOA.Classification.COne.Nice V)
    (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
    (D' : VOA.ModularData V D.ι) (hZD : DLNBridge.IsZhuDatum D hD D') {N : ℕ}
    (hN : D.IsLevel N) : DLN.KernelContainsGamma D'.rep N :=
  DLNBridge.kernel_at_level zhuCongruenceInput_holds hV D hD D' hZD hN

end VOA.Huang.CongruenceNamed
