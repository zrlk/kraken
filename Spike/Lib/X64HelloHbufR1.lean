import Spike.Lib.X64HelloOLift

/-!
**hello.w on x86-64: `hbuf` from the pre-spawn relation**.

`X64HelloVBuf.helloSrc_frzL` turns `VBufR` at the single pre-spawn thread into
`BufAtSpawn`; `VBufR` is the last conjunct of `X64HelloOLift.XH`, the slot of
`X64HelloO.R1OH`. This module reads it off:

- `hbuf_XH`: `hbuf` (the binder of `clonePreH_of` / `HClW`) from `XH d s`.

x86-64 twin of `Spike/Lib/HelloHbufR1.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, `BufAtSpawn` is `X64HelloInst`'s.
Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only
live constants): `hbuf_R1OH`.
-/

namespace Spike.Lib.X64HelloHbufR1

open CoreLang CoreTerm TermRun
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloVBuf (helloSrc_frzL)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.X64HelloInst (BufAtSpawn)

/-- **`hbuf` from `XH`**: at the single pre-spawn thread with no promises,
every spawn source whose head word is a buffer location `lb` has
`BufAtSpawn s lb` (`helloSrc_frzL` at `XH`'s `VBufR`). -/
theorem hbuf_XH {d s} {th0 : TermRun.TTh} (h : XH d s) (hs : s.ths = #[th0]) (hp : th0.promises = [])
    {hd : Option (Nat × Word)} :
    ∀ (l : WeakMem.AllocLabel) (ws : List Word) (lb : WeakMem.AllocLabel),
      SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ →
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → BufAtSpawn s lb :=
  fun _ _ _ hS hh => helloSrc_frzL h.2.2.2.2 hs hp hS hh

end Spike.Lib.X64HelloHbufR1

/-- info: 'Spike.Lib.X64HelloHbufR1.hbuf_XH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHbufR1.hbuf_XH
