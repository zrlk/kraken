/-
**The counter add at a frame-indexed counter add** (x86-64; the twin of `Spike/Lib/A64HelloCtrF.lean`'s live part):
the pieces of `OpenW.hnew0` per disjunct of a context built from counter adds at any frames and any allocation site
(`CtrOkS`, `X64HelloLand`'s `CtrAtF`).

At the counter add the frame run stays put (a buffer `newBuf` or a box `new`: `FrameRun.eq_of_site`), and
`ctrRow_allocS_c2` gives the row at the call's memory side, whose step writes the counter (`ctrAtF_wr`).

- `FrameRun.eq_of_site`, `site_not_ret`: a frame run from an allocation site is empty; the site is no `ret`.
- `ctrAtF_wr`: the counter add writes the counter (`hnew0`'s dismissal of the `CtrAtF` disjuncts).

## Where this differs from AArch64 (forced by the x86-64 shape)

- `ctrAtF_wr` takes the allocator's code from the layout (`hp : Lays exe cells kp`, `hend`, `hin`, under
  `Executable.ValidLayout exe`), as x86-64's `WakeCtr.ctrRow_allocS_c2` does, in place of AArch64's
  `hcode : ∀ ms0 q, Code ms0 q exe endPc` (x86-64 has no `Alloc.Code`); the row lands at `c2` (AArch64 `n4`).
- Not twinned (unreachable from the AArch64 root): `ctrRow_ofF`, `ctrRow_ofFT`, `newStM_ofSt`, and the private
  helpers `c_eq` and `ctrRow_land`, used only by `ctrRow_ofF`/`ctrRow_ofFT`.
-/
import Spike.Lib.X64HelloLand
import Spike.Lib.X64WakeCtr
import Spike.Lib.X64ConsumerA
import Spike.Lib.FrameNew

namespace Spike.Lib.X64.HelloPh.CtrF

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (Region FrameRun MemSide Arena AllocSite)
open Spike.Lib.X64ConsumerA (WrAt)
open Spike.Lib.X64.Alloc (Call allocIn)
open Spike.Lib.X64.WakeCtr (ctrRow_allocS_c2)
open Spike.Lib.X64.HelloPh.Land (CtrAtF)

variable {p : Prog}

/-- **A frame run from an allocation site is empty** (a buffer: `FrameRun.eq_of_newBuf`; a box:
`FrameRun.eq_of_new`). -/
theorem FrameRun.eq_of_site {N : Prop} {c : Ctl} {fs : List TermRun.Frame} {q' : Ctl × List TermRun.Frame}
    {x : String} {n : Nat} {τ : Ty} {e : Expr} (hr : FrameRun p (c, fs) q') (h : AllocSite N c x n τ e) :
    q' = (c, fs) := by
  rcases h with ⟨a, ta, ws, ht, hea, hk⟩ | ⟨-, a, ws, ht, -, -⟩
  · exact Spike.Lib.X64ConsumerA.FrameRun.eq_of_newBuf hr ht hea hk
  · obtain ⟨_, ht⟩ := ht
    exact Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht

/-- **An allocation site is no `ret`.** -/
theorem site_not_ret {N : Prop} {c : Ctl} {x : String} {n : Nat} {τ : Ty} {e : Expr} (h : AllocSite N c x n τ e) :
    ∀ a, c.term ≠ .ret a := by
  intro b hb
  rcases h with ⟨a, ta, ws, ht, -, -⟩ | ⟨-, a, ws, ⟨_, ht⟩, -, -⟩ <;> rw [ht] at hb <;> cases hb

variable {exe : _root_.Executable} {endPc : Int64} {cells : List (Directive × Nat)} {kp : Nat}
  {ref : List TermRun.Frame → MemSide isa}
  {Gc : List TermRun.Frame → MemSide isa → Region → (MachineData → Prop) → Call → Prop}

/-- **The counter add writes the counter** (`WakeCtr.ctrAt_wr` at `CtrAtF`), at reference sides whose counter is
the arena's (`hc`), the allocator's code from the layout (`hp`, `hend`, `hin`). -/
theorem ctrAtF_wr [Executable.ValidLayout exe] {ar : Arena} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hc : ∀ fs, (ref fs).ctr = ar.ctr) :
    ∀ s c fs, CtrAtF ref exe endPc Gc s c fs → WrAt s ar.ctrLoc := by
  rintro s c fs ⟨ms0, R, F, q, hms, -, hok, hAt⟩
  obtain ⟨k, op, g, -, -, -, -, h1, -⟩ := ctrRow_allocS_c2 hp hend hin hok.fst hok.oks hok.mem hAt
  have e : ms0.ctr = ar.ctr := (congrArg MemSide.ctr hms).trans (hc fs)
  refine .inr ⟨k, op, g, ?_⟩
  rw [h1, e]; rfl

end Spike.Lib.X64.HelloPh.CtrF

/-- info: 'Spike.Lib.X64.HelloPh.CtrF.FrameRun.eq_of_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtrF.FrameRun.eq_of_site

/-- info: 'Spike.Lib.X64.HelloPh.CtrF.site_not_ret' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtrF.site_not_ret

/-- info: 'Spike.Lib.X64.HelloPh.CtrF.ctrAtF_wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CtrF.ctrAtF_wr
