# `Spike.Lib.Src`: numbers and safety of an `Accepted2` program's source run

What these modules prove: take a program in the v4.3 lowering fragment
(`Scc.Lower.Accepted2`, `Scc/Lower/Spec2.lean`) and run it single-threaded
under the source semantics (`Scc.Sem.SrcSem.source`), starting before the
setup block. Then:

1. **Numbers** (`SrcNumSP`): whenever thread 0 is at the output extern's
   element load (`PrintLd c l j`, i.e. `printL`'s `loadAt` of word `j` of
   label `l`), that cell has a message and its latest message holds a number.
2. **Safety** (`SrcSafeS`, per ISA): the consumer's two source-safety
   triggers hold. The `cell` trigger is vacuous, because no reachable thread
   has an acquire load, a release store or a spawn. The `xchg` trigger holds
   because an exchange site's cell has a message.

Both proofs go construct by construct over `Accepted2` (`decl2`, `body2`),
with no premise on the program beyond `Accepted2`. For `hello1o` every
remaining check is closed by `decide`/`rfl`.

## Main statements (namespace `Spike.Lib.LowerNode`)

| Statement | Module |
|---|---|
| `srcNumS_of_accepted2 hacc hn hset hsetup hloc hinit hH : SrcNumSP P p PrintLd` | `SrcNum2` |
| `srcNumS_hello1 hinit hH : SrcNumSP P Spike.Test.Hello1MainSrc.hello1o PrintLd` | `SrcNum2` |
| `printLd_loadC (hpw : pw.val = .loc ⟨l, 0⟩ 0) : PrintLd (PrintSrc.loadC pw wn m k) l (k / 8)` | `SrcNum2` |
| `srcNumS_a64 : SrcNumSP P p Ld → A64ConsumerS.SrcNumS P p I Ld` | `SrcNumWA` |
| `srcNumS_x64 : SrcNumSP P p Ld → X64ConsumerS.SrcNumS P p I Ld` | `SrcNumWX` |
| `srcSafeS_of_accepted2 hacc hH hinit I : A64ConsumerS.SrcSafeS P p I` | `SrcSafe2A` |
| `srcSafeS_of_accepted2X hacc hH hinit I : X64ConsumerS.SrcSafeS P p I` | `SrcSafe2X` |
| `hello1o_srcSafeS hH hinit I`, `hello1o_srcSafeSX hH hinit I` | `SrcSafe2A`, `SrcSafe2X` |
| `hello1o_accepted2 : Accepted2 hello1o = true` | `SrcSafe2` |
| `hello1o_noExit hU hinit h : ∀ x, Event.exit x ∉ s.trace` | `Hello1Out` |
| `hello1o_noExit_hook hU hinit : ∀ tr s, Reach tr s → ∀ x, Ev.exit x ∉ P.hooks.trace s` | `Hello1Out` |
| `noExit_hook_of_accepted2 hA hU hinit`, `hookOK_srcP1o hA arch : HookOK (srcP1o arch p) p` | `Accepted2Out` |
| `progInit_of_setupOf_some h cap`, `progInit_of_setupOf_none hA h cap` | `Accepted2Out` |

Consumer shape (checked in `Spike/Test/SrcNumA64.lean`, `SrcNumX64.lean`):

```lean
srcNumS_a64 (srcNumS_hello1 hinit (.inr hU)) : A64ConsumerS.SrcNumS P hello1o I PrintLd
hello1o_srcSafeS (.inr hU) hinit I            : A64ConsumerS.SrcSafeS P hello1o I
```

`printLd_loadC` connects the trigger to the control at which the consumer's
print proof (`Spike.Lib.PrintSrc`) does the element load for byte `k`.

## Premises the consumer supplies

- `hinit : ∀ c, P.init c → ∃ meW, c = Scc.Sem.SrcSem.setupStart P.cap meW`:
  the runs start at the source's start before the setup block.
- `hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p`: either no
  extern, or WeakCore's output hook. Extern steps (including `park`/`unpark`
  and the resulting `wake`) keep both invariants: `invN_ext`, `invN_wake`,
  `cfgB_ext`, `cfgB_wake`, `cfgNoS_extB`, `cfgNoS_wakeB`.
- For the general `srcNumS_of_accepted2` you also need: `hn` (every literal
  walk point has `numQ`), `hset`/`hsetup`/`hloc` (the setup block's type is
  compatible with its shape and is not a locative). `srcNumS_hello1`
  discharges all of these.
- `SrcNumS`'s own premise, thread 0's `promises = []`, is passed through
  unchanged. The wrappers add no premise.

## Layout

- Lowering walk (immediates, marks, groups, literal walks): `LowerEnvImm2Of`,
  `LowerMarks2`, `ImmIn`, `ImmIn2`, `LowerMarksImm2`, `ExternUnit`,
  `AbortImm2`, `Walk21`, `GroupAlg`, `NJ2`, `NJ2Srun`, `SstepLet`,
  `GroupShape`, `NJ3`, `NJL`, `NJLW`, `NJLC`, `NJLS`, `XchgLeaf`.
- Buffers and slices: `HeapMem`, `HeapLit`, `HeapBuf`, `SliceL`, `NJLB`, `NJLBS`.
- Safety: `NoAcq`, `SrcB`, `SrcSafe2`, `SrcSafe2A`, `SrcSafe2X`.
- Numbers: `SrcNumE`, `SrcNum`, `SrcNum2`, `SrcNumWA`, `SrcNumWX`.
- `hello1o`'s trace: `Hello1Out` (`stdout`, and no exit through an extern:
  `HookOK.wc`'s premise, under `UsesWc` and `hinit`); any `Accepted2`
  program's: `Accepted2Out`.

The A64 and X64 consumer modules cannot share one import closure. The A64
side is imported by `Spike.lean`; the X64 side is imported by
`Spike/X64.lean`.
