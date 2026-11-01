import Spike.Lib.HelloOLift

/-!
**hello's `hbuf` from the pre-spawn relation** (row 1).

`HelloVBuf.helloSrc_frzL` turns `VBufR` at the single pre-spawn thread into
`BufAtSpawn`; `VBufR` is the last conjunct of `HelloOLift.XH`, the slot of
`HelloO.R1OH`. This module reads it off:

- `hbuf_XH`: `hbuf` (the binder of `clonePreH_of` / `HClW`) from `XH d s`;
- `hbuf_R1OH`: the same from `R1OH arch Λ μ D XH d s`.
-/

namespace Spike.Lib.HelloHbufR1

open CoreLang CoreTerm TermRun
open Spike.Lib.HelloO (R1OH)
open Spike.Lib.HelloOLift (XH)
open Spike.Lib.HelloVBuf (helloSrc_frzL)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.HelloPreA (BufAtSpawn)

/-- **`hbuf` from `XH`**: at the single pre-spawn thread with no promises,
every spawn source whose head word is a buffer location `lb` has
`BufAtSpawn s lb` (`helloSrc_frzL` at `XH`'s `VBufR`). -/
theorem hbuf_XH {d s} {th0 : TermRun.TTh} (h : XH d s) (hs : s.ths = #[th0]) (hp : th0.promises = [])
    {hd : Option (Nat × Word)} :
    ∀ (l : WeakMem.AllocLabel) (ws : List Word) (lb : WeakMem.AllocLabel),
      SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ →
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → BufAtSpawn s lb :=
  fun _ _ _ hS hh => helloSrc_frzL h.2.2.2.2 hs hp hS hh

/-- **`hbuf` from `R1OH … XH`** (`hbuf_XH` at the slot). -/
theorem hbuf_R1OH {arch Λ μ D d s} {th0 : TermRun.TTh} (h : R1OH arch Λ μ D XH d s) (hs : s.ths = #[th0])
    (hp : th0.promises = []) {hd : Option (Nat × Word)} :
    ∀ (l : WeakMem.AllocLabel) (ws : List Word) (lb : WeakMem.AllocLabel),
      SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ →
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → BufAtSpawn s lb :=
  hbuf_XH h.2 hs hp

end Spike.Lib.HelloHbufR1

/-- info: 'Spike.Lib.HelloHbufR1.hbuf_R1OH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.HelloHbufR1.hbuf_R1OH
