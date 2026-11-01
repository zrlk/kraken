/-
**hello.w: main has not returned while the process runs** (the `mainLive`
field of `WakeW1.WCompat` / `HelloW1StoreX.WStoreX` at `helloQ`):
`mainLiveH`, `WakeM0.mainLive_of` at `helloQ`'s pinned main post
(`HelloQ.hPT0`, `rfl`) and kernel relation (`HelloQ.hKR`), whose
`MainLive` conjunct is `A64HelloWriteK.krh_live`. Generic in every
parameter of `helloQ` (any record type, worker side, layout).
-/
import Spike.Lib.HelloQ
import Spike.Lib.WakeM0

namespace Spike.Lib.HelloLive

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {ι : Type} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {P : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : WSideH ι}
  {r0 r1 : ι → Range}

/-- **`helloQ`'s kernel relation carries `MainLive`** (`WakeM0.LiveK`). -/
theorem liveK_H : WakeM0.LiveK (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1) :=
  fun _ _ _ h => A64HelloWriteK.krh_live h.1

/-- **`WCompat.mainLive` at `helloQ`**: while no thread has exited, main's
source has not returned. -/
theorem mainLiveH {Λ : Scc.Sem.Layout} :
    ∀ t s, (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).Post Λ t s → t.2.exited = none →
      SrcSem.mainExit s = [] :=
  fun _ _ h hx => WakeM0.mainLive_of (D := M) HelloQ.hPT0 liveK_H h hx

end Spike.Lib.HelloLive

/-- info: 'Spike.Lib.HelloLive.liveK_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloLive.liveK_H

/-- info: 'Spike.Lib.HelloLive.mainLiveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloLive.mainLiveH
