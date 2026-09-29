import Lake
open Lake DSL

package pureInductionAncestry

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib FiniteFixation

lean_lib FiniteEpigenetic

lean_lib PureInductionJoint

lean_lib SamuelAlexanderResearch where
  roots := #[`SamuelAlexanderResearch.SpeciesBridge]

lean_lib FeedbackDynamics

lean_lib ExtinctionPedigree

lean_lib ParentSchedules

lean_lib UniformParentCounting

lean_lib UniformParentProcess

lean_lib PureInductionR1R2

lean_lib PureInductionNoise

lean_lib PureInductionPaths

@[default_target]
lean_lib PureInductionAncestry

