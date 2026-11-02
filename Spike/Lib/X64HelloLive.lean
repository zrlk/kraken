/-
**hello.w: main has not returned while the process runs** (the `mainLive`
field of `X64WakeW1.WCompat` / `X64HelloW1StoreX.WStoreX` at `helloQ`):
`mainLiveH`, `X64WakeM0.mainLive_of` at `helloQ`'s pinned main post
(`X64HelloQ.hPT0`, `rfl`) and kernel relation (`X64HelloQ.hKR`), whose
`MainLive` conjunct is `X64HelloWriteK.krh_live`. Generic in every
parameter of `helloQ` (any record type, worker side, layout).

x86-64 twin of `Spike/Lib/HelloLive.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, the invariant parameters are x86-64's (`Inv2Params isa`).
-/
import Spike.Lib.X64HelloQ
import Spike.Lib.X64WakeM0

namespace Spike.Lib.X64HelloLive

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {ι : Type} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {P : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : WSideH ι}
  {r0 r1 : ι → Range}

/-- **`helloQ`'s kernel relation carries `MainLive`** (`X64WakeM0.LiveK`). -/
theorem liveK_H : X64WakeM0.LiveK (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1) :=
  fun _ _ _ h => X64HelloWriteK.krh_live h.1

/-- **`WCompat.mainLive` at `helloQ`**: while no thread has exited, main's
source has not returned. -/
theorem mainLiveH {Λ : Scc.Sem.Layout} :
    ∀ t s, (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).Post Λ t s → t.2.exited = none →
      SrcSem.mainExit s = [] :=
  fun _ _ h hx => X64WakeM0.mainLive_of (D := M) X64HelloQ.hPT0 liveK_H h hx

end Spike.Lib.X64HelloLive

/-- info: 'Spike.Lib.X64HelloLive.liveK_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloLive.liveK_H

/-- info: 'Spike.Lib.X64HelloLive.mainLiveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloLive.mainLiveH
