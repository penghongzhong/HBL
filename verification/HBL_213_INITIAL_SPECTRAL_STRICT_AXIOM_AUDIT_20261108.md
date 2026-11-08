# HBL §2.13: pinned strict source-and-interface audit (8 November 2026)

Toolchain for each referenced workflow:
Lean **4.35.0-rc3** (compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`);
Mathlib **a98628e16c11f5167f16124105ddce53efa9bfe5**.
The strict-success workflows execute `lake env lean --trust=0 -DwarningAsError=true`,
check literal theorem types, and inspect every referenced declaration with
`#print axioms`, refusing `sorryAx` or anything outside
`propext`, `Classical.choice`, `Quot.sound`.
The conclusions below were independently read from the downloaded GitHub
Actions evidence ZIPs, not inferred from workflow names.

| Workflow | Checked source commit | Result and observed kernel report |
| --- | --- | --- |
| [42500440029](https://github.com/penghongzhong/HBL/actions/runs/42500440029) | `dc810e60f79e8857870450daf82fd29e6e5da736` | **Success**. `actual_Hartree_original_spectral_C1_trace_no_left_radius_loss` and `actual_Hartree_original_spectral_C1_and_residual_no_left_radius_loss`: each exactly `[propext, Classical.choice, Quot.sound]`, with possible universe annotations. `strict.log` empty. |
| [42501019413](https://github.com/penghongzhong/HBL/actions/runs/42501019413) | `1a904d490acdd93d95c4203a377d8d744d11afd4` | **Failure**, so **no axiom audit report exists** for this run. Five actual type/rewrite errors in `ActualHartreeMatchedSpectralLeftC1Exact.lean` at lines 73, 97, 99, 150 and 168. |
| [42501379178](https://github.com/penghongzhong/HBL/actions/runs/42501379178) | `46fff4a9aa99a5df546e81c57126a7a1126185e0` | **Failure**, so **no axiom audit report exists** for this run. Same five upstream errors at lines 73, 97, 99, 150, 168. |
| [42502178507](https://github.com/penghongzhong/HBL/actions/runs/42502178507) | `9ed7cfd296aa1ad697425a0ddbf353703770f5f4` | **Success** after repairs of failed left-C¹ source module. The exact matched left-C¹ equation and upper-defect theorems each report `[propext, Classical.choice, Quot.sound]`, modulo Lean universe annotations; `strict.log` empty. |
| [42503498370](https://github.com/penghongzhong/HBL/actions/runs/42503498370) | `62fb56046cf947a28c9205dfda42597b13be0614` | **Success** after repairing upper-flux imports. All four matched spectral upper-obstruction and flux theorems each report `[propext, Classical.choice, Quot.sound]`, modulo universe annotations; `strict.log` empty. |

Artifact evidence names are `hbl-spectral-c1-interface-trace-strict-evidence`,
`hbl-matched-spectral-left-C1-strict-evidence` and
`hbl-spectral-upper-flux-weighted-strict-evidence`.
The failed runs have `build.log` but no `audit.log`; the accepted
successors contain `audit.log`, full source, exact source hashes, and
empty `strict.log`.

**Mathematical boundary:** The accepted results concern fixed Kummer
source/spectral-response/left transmission and upper outgoing **defect**.
An outgoing mismatch is not silently set to zero. No strict run listed
here establishes the real moving four-region nonlinear Hartree residual
time-gain or physical Type-II blowup. Original manuscript acceptance
therefore remains **11/13**.
