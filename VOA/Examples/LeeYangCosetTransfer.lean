/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.LeeYangCosetTransferFiltered
import VOA.Examples.LeeYangCosetTransferDimension
import VOA.Examples.LeeYangCosetTransferHodge

/-!
# Linear algebra for the conditional Lee–Yang coset transfer

This module collects three proved linear-algebra steps of the conditional reduction of
Lee–Yang graded unitarity to the affine case through the coset BRST–Koszul transfer:

* `InverseDS.GradedIsometricEmbedding.gradedUnitary_of_filteredIso` transfers graded unitarity
  through a real isometry whose weight maps take every filtration piece onto the ambient piece.
  `LeeYangCosetTransfer.gradedUnitary_of_filteredLinearEquiv` takes a linear equivalence directly.
* `LeeYangCosetTransfer.maps_eq_of_finrank_squeeze` identifies filtration pieces from filtered
  injectivity and matching dimension bounds. Target exhaustion yields surjectivity and the
  equivalence `LeeYangCosetTransfer.linearEquivOfFinrankSqueeze`.
* `LeeYangCosetTransfer.harmonicToCohomology_injective` proves the positive-norm injection.
  For a finite-dimensional square-zero complex, `LeeYangCosetTransfer.harmonicEquivCohomology`
  identifies harmonic vectors with cohomology and gives equality of dimensions.

These results do not construct the relative BRST complex, its positive Hodge form, the coset
embedding, or the character bounds, and do not prove graded unitarity of the Lee–Yang VOA.
Those concrete inputs remain outside this module; every linear, metric, and dimension hypothesis
used here appears explicitly in the corresponding declarations.
-/
