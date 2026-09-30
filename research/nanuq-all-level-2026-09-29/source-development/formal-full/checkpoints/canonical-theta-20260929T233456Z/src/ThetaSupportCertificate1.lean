import ThetaSupport

set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Nanuq.Theta

/- Generated proof obligations only; no stored split or positivity answers. -/
theorem support_checked_0_0_0_1 : checkSupport ⟨0,0,0,1⟩ = true := by decide +kernel
theorem support_checked_0_0_1_0 : checkSupport ⟨0,0,1,0⟩ = true := by decide +kernel
theorem support_checked_0_1_0_0 : checkSupport ⟨0,1,0,0⟩ = true := by decide +kernel
theorem support_checked_1_0_0_0 : checkSupport ⟨1,0,0,0⟩ = true := by decide +kernel
#check support_checked_1_0_0_0

#print axioms support_checked_1_0_0_0
end Nanuq.Theta
