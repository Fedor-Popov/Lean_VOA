import VOA.Classification.COne.OrbIcoWRecVac01
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac09_jet_recurrence : JetRecurrence false 9 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac09_jet_pivot : JetPivot false 9 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac10_jet_recurrence : JetRecurrence false 10 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac10_jet_pivot : JetPivot false 10 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac11_jet_recurrence : JetRecurrence false 11 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac11_jet_pivot : JetPivot false 11 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac12_jet_recurrence : JetRecurrence false 12 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac12_jet_pivot : JetPivot false 12 := by decide +kernel
end VOA.Classification.COne.OrbIcoW
