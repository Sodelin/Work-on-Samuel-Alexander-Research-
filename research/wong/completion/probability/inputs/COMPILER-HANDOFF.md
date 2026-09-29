# Absorption proof compiler receipt, 2026-09-25

The embedded count-chain and Big-ARG absorption bridge have both passed Lean 4.33.1 with the pinned Mathlib dependency. The compiler slot was released to root after these checks. These are actual source and compiler receipts, not draft claims.

## Passed modules

- `WongBigARGDrift.lean`: prior scalar pass, two selected endpoints (`weighted_gap`, `potential_drift`) with standard axioms only, as recorded in CHECKPOINT.md and verification.json. Source SHA256 `167D448EB3E0C016E24A0590B2263F7685B244F21999B2B6303D105E09DFCB43`.
- `WongCountChain.lean`: `./Check.ps1 -File WongCountChain.lean`, exit 0. Ten selected endpoints, all with only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Constructs the actual normalized two-point kernel and `Kernel.traj` path law, proves initial/one-step integration, positive-state support, finite drift telescope, Borel-Cantelli eventual absorption given derived finite potential drift, and literal rate algebra. Five nonfatal lint/deprecation warnings.
- `WongBigARGAbsorption.lean`: `./Check.ps1 -File WongBigARGAbsorption.lean`, exit 0. Seven selected endpoints, all with only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Bridges the explicit finite scalar potential to the actual count-chain kernel; proves almost-sure eventual one and finite jump absorption for every normalized ratio and for literal rates `lambda_k=b*k`, `mu_k=a*k*(k-1)/2` with `a>0`, `b>=0`, `k>=2`, `theta=2*b/a`, initial count `n+2`. It also identifies the upward and downward singleton kernel masses with the literal rate ratios. Two nonfatal linter warnings.

Total selected endpoints across the three modules: 19 (2 scalar + 10 chain + 7 bridge). Zero reported compiler errors or `sorryAx` in the final stochastic module logs.

## SHA256 receipts

| File | SHA256 |
| --- | --- |
| `WongCountChain.lean` | `5F7629AF4619220F77DD0C6344DF4D3D096E3CA089E9F439C9CBF8808D6C59AE` |
| `WongCountChain.compile.log` | `7666A3E5D45D58A5F4AD09AB66B972ADDF1BDA9316CE012401A6085AA91AEDDD` |
| `WongCountChain.olean` | `E952662036F7C3282166CC5199951B0A913DF818A5578C7EEE4C2F1C6D29F168` |
| `WongBigARGAbsorption.lean` | `50B18CF23019C05C477C35CA38025D2516B662788D65E7C4CB6F98FECB3FF518` |
| `WongBigARGAbsorption.compile.log` | `76381E63971CF68D2D473C9DE9974703F4B47BE0D0397A0984A2FB440B7FC3F1` |
| `WongBigARGAbsorption.olean` | `4F7A2DA558E4B45F6FD2C13C6628713477E16FF04765824E5DE859EBE77F8BB6` |

## Scope limits

The theorem is an almost-sure finite **jump-index** absorption result for the stopped embedded count process. It does not construct continuous holding times, prove nonexplosion/finite physical stopping time, or derive the count process as a projection of the fully marked spatial ARG. Little ARG dynamics and exact expected event counts are separate obligations. State one is absorbing in this model; state zero is only a totalization case and is almost surely avoided from a positive initial count.

No dependency/cache files, global ledger, publication, or archive surface was modified by this lane. All writes are in this absorption directory.