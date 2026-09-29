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

@[default_target]
lean_lib WongSampleTracing

@[default_target]
lean_lib WongRecordTracing

@[default_target]
lean_lib WongEventDecoding

@[default_target]
lean_lib WongLocalSimplification

@[default_target]
lean_lib WongMemoizedTracing

@[default_target]
lean_lib WongTimedHistory

@[default_target]
lean_lib WongMRCATruncation

@[default_target]
lean_lib WongIntervalCanonicalization

@[default_target]
lean_lib WongSimplificationNormalForm

@[default_target]
lean_lib WongBigARGDrift

@[default_target]
lean_lib WongCountChain

@[default_target]
lean_lib WongBigARGAbsorption

@[default_target]
lean_lib WongWaitingTimes

@[default_target]
lean_lib WongMarkedRecorder

@[default_target]
lean_lib WongMarkedLaw

@[default_target]
lean_lib WongMarkedProcess

@[default_target]
lean_lib WongMarkedMeasurable

@[default_target]
lean_lib WongAdaptiveSelection

@[default_target]
lean_lib WongMarkedDated

@[default_target]
lean_lib WongPedigreeBridge


@[default_target]
lean_lib WongPedigreeRobust

@[default_target]
lean_lib WongMarkedSupport

@[default_target]
lean_lib WongDatedSupport

@[default_target]
lean_lib PedigreeBlockModel

@[default_target]
lean_lib PedigreeBlockGraph

@[default_target]
lean_lib PedigreeBlockProbability

@[default_target]
lean_lib PedigreeBlockObservation

@[default_target]
lean_lib PedigreeBlockDependence

@[default_target]
lean_lib PedigreeBlockRecovery

@[default_target]
lean_lib PedigreeBlockAudit

@[default_target]
lean_lib PairingCore

@[default_target]
lean_lib PairingObservation

@[default_target]
lean_lib PairingObservationAudit
