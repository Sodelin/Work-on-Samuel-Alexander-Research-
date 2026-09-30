import ThetaFiniteSoundness

set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Nanuq.Theta

/- Each assertion is checked by kernel reduction of the executable
switching/quartet evaluator. This generator supplies no metric answers. -/

theorem checked_0_0_0_3 : checkTemplate ⟨0,0,0,3⟩ = true := by decide +kernel
theorem checked_0_0_1_2 : checkTemplate ⟨0,0,1,2⟩ = true := by decide +kernel
theorem checked_0_0_2_1 : checkTemplate ⟨0,0,2,1⟩ = true := by decide +kernel
theorem checked_0_0_3_0 : checkTemplate ⟨0,0,3,0⟩ = true := by decide +kernel
theorem checked_0_1_0_2 : checkTemplate ⟨0,1,0,2⟩ = true := by decide +kernel
theorem checked_0_1_1_1 : checkTemplate ⟨0,1,1,1⟩ = true := by decide +kernel
theorem checked_0_1_2_0 : checkTemplate ⟨0,1,2,0⟩ = true := by decide +kernel
theorem checked_0_2_0_1 : checkTemplate ⟨0,2,0,1⟩ = true := by decide +kernel
theorem checked_0_2_1_0 : checkTemplate ⟨0,2,1,0⟩ = true := by decide +kernel
theorem checked_0_3_0_0 : checkTemplate ⟨0,3,0,0⟩ = true := by decide +kernel
#check checked_0_3_0_0
theorem checked_1_0_0_2 : checkTemplate ⟨1,0,0,2⟩ = true := by decide +kernel
theorem checked_1_0_1_1 : checkTemplate ⟨1,0,1,1⟩ = true := by decide +kernel
theorem checked_1_0_2_0 : checkTemplate ⟨1,0,2,0⟩ = true := by decide +kernel
theorem checked_1_1_0_1 : checkTemplate ⟨1,1,0,1⟩ = true := by decide +kernel
theorem checked_1_1_1_0 : checkTemplate ⟨1,1,1,0⟩ = true := by decide +kernel
theorem checked_1_2_0_0 : checkTemplate ⟨1,2,0,0⟩ = true := by decide +kernel
theorem checked_2_0_0_1 : checkTemplate ⟨2,0,0,1⟩ = true := by decide +kernel
theorem checked_2_0_1_0 : checkTemplate ⟨2,0,1,0⟩ = true := by decide +kernel
theorem checked_2_1_0_0 : checkTemplate ⟨2,1,0,0⟩ = true := by decide +kernel
theorem checked_3_0_0_0 : checkTemplate ⟨3,0,0,0⟩ = true := by decide +kernel
#check checked_3_0_0_0

#print axioms checked_3_0_0_0
end Nanuq.Theta
