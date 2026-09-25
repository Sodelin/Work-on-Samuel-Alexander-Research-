import Lake
open Lake DSL

package samuel_alexander_real

require samuel_alexander_research from ".."
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib RealBridges

@[default_target]
lean_lib PortEncoding

@[default_target]
lean_lib StatefulCAReal

@[default_target]
lean_lib WongGARG

@[default_target]
lean_lib WongAlexander

@[default_target]
lean_lib WongExamples

@[default_target]
lean_lib WongLocalArity

@[default_target]
lean_lib WongEventEncoding

@[default_target]
lean_lib WongBreakpointCells

@[default_target]
lean_lib WongIntervalNormalization

@[default_target]
lean_lib WongSimplification

@[default_target]
lean_lib WongDiamond

@[default_target]
lean_lib FiniteGenomeIdentifiability

@[default_target]
lean_lib FounderWindow

@[default_target]
lean_lib DirectedIAP

@[default_target]
lean_lib SeedIntersections

@[default_target]
lean_lib RealFounderWindow

@[default_target]
lean_lib FounderMaximal

@[default_target]
lean_lib SpeciesReindex

@[default_target]
lean_lib SpeciesSeed

@[default_target]
lean_lib RealSpeciesTheorem
