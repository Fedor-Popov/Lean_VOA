import VOA.Classification.COne.OrbIcoWRecVac08
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac37_jet_recurrence : JetRecurrence false 37 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac37_jet_pivot : JetPivot false 37 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac38_jet_recurrence : JetRecurrence false 38 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac38_jet_pivot : JetPivot false 38 := by decide +kernel
end VOA.Classification.COne.OrbIcoW
