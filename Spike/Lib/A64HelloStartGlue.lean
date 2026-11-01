/-
**hello.w's start glue facts** (AArch64; hello twin of `A64WakeStartGlue`): the
pieces that join `HelloPh.StartWf.startEW_W0SH`, `Rt.startEF_segW` and
`HelloPh.MainWf.mainPreWH_W0SH` with `wc_main`'s entry. Unlike wake's, hello's glue
goes on through **`wc_rodata`'s segment** (`HelloM.hello_main_pre_segW` /
`hello_main_post_segW`, `A64HelloMain`, the source's rodata run and the publish
fence) before `bl wc_main`: `scc_rt_main` calls `wc_rodata` first.

Most of wake's glue is layout-generic and is reused as is (no hello copy):
`WakePh.StartGlue.StartEW.toF`, `hmemB_of_wordsNone` (`wc_main`'s box call;
rodata's buffer call takes `Alloc.hmem_of_wordsNone` / `hbuf_of_wordsNone`
directly), `hcellB_of_wordsNone`. wake's `room_gW`, `room_gW_top` are stated at
wake's value invariant `GOf2`, which pins wake's second limit word `pinA + 112`
(hello's TCB field `0`); hello uses their twins at `GOf2H`,
`HelloGOf2H.room_gWH`, `room_gWH_top`. This file has the pieces that are
fixed to wake's program:

- `X0WH L a`: `W0`'s per-state facts at hello (wake's `X0W` at `clonePcH`): off
  the clone's pc; at the take pc `a`, the site's range main's stack `r0Of`, not
  in private memory.
- `x0WH_of_freeNH`: `X0WH` at a free pc (`StartWf`'s `hX0`), the take pc the
  site's.
- `x0WH_inv`, `noCloneH_of`, `h0TakeH_of`, `h0TakeOwnH_of`: `X0WH` at an
  invariant inside `W0 … (X0WH L a)`, and from it `H0StmtH`'s clone clause,
  `H0TakeH`, `H0TakeOwnH` (`A64HelloWcInv3`).
-/
import Spike.Lib.A64HelloMainWf
import Spike.Lib.A64HelloWcPreWI
import Spike.Lib.A64HelloWcInv3
import Spike.Lib.A64WakeStartGlue

namespace Spike.Lib.A64.HelloPh.StartGlue

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Arena FragS)
open Spike.Lib.A64Consumer (Lbl Lsize Own)
open Spike.Lib.A64ConsumerA (SegInvS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeWf (W0)
open Spike.Lib.A64.HelloPh.WcW (freeNH)

/-! ## `W0`'s per-state facts -/

/-- **`h0`'s per-state facts at `W0`, at hello**: off the clone's pc
(`clonePcH`), and at the take pc `a` main's stack the site's range, not in
private memory (`¬ StackM`: not yet taken). -/
def X0WH (L : RuntimeLayout) (a : Int64) (s : State) : Prop :=
  pcOf s ≠ Spike.Lib.HelloPreA.clonePcH L ∧
    (pcOf s = a.toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s.st.1)

/-- **`X0WH` at a free pc** (`StartWf`'s `hX0`): off the clone's pc and off
the take pc `a`, the take site's. -/
theorem x0WH_of_freeNH {L : RuntimeLayout} {a : Int64}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (ha : a.toBitVec.toNat = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s, freeNH (pcOf s) = true → X0WH L a s :=
  fun _ h => ⟨Spike.Lib.A64.HelloPh.WcW.ne_clonePc_of_freeNH hlab h,
    fun he => absurd (he.trans ha) (Spike.Lib.A64.HelloPh.WcW.site_ne_of_freeNH hlab h)⟩

section Inv

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Ab Cl Ac : State → Prop}
  {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {K : State → State → Prop}
  {ms0 : List TermRun.Frame → Spike.Lib.MemSide isaLSE2} {inv0 : FragS isaLSE2} {L : RuntimeLayout}
  {a : Int64}

/-- **`X0WH` at an invariant inside `W0`.** -/
theorem x0WH_inv (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0WH L a)) K p L0 ms0 inv0) :
    ∀ s c fs, inv0 s c fs → X0WH L a s :=
  fun s c fs hi => (h s c fs hi).1.2.1

/-- **`H0StmtH`'s clone clause** at an invariant inside `W0 … (X0WH L a)`. -/
theorem noCloneH_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0WH L a)) K p L0 ms0 inv0) :
    ∀ s c fs, inv0 s c fs → pcOf s ≠ Spike.Lib.HelloPreA.clonePcH L :=
  fun s c fs hi => (x0WH_inv h s c fs hi).1

/-- **`H0TakeH`** at an invariant inside `W0 … (X0WH L a)`. -/
theorem h0TakeH_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0WH L a)) K p L0 ms0 inv0) :
    Spike.Lib.HelloPreA.H0TakeH L a inv0 :=
  fun s c fs hi hpc => ((x0WH_inv h s c fs hi).2 hpc).1

/-- **`H0TakeOwnH`** at an invariant inside `W0 … (X0WH L a)`. -/
theorem h0TakeOwnH_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0WH L a)) K p L0 ms0 inv0) :
    Spike.Lib.HelloPreA.H0TakeOwnH L a inv0 :=
  fun s c fs hi hpc => ((x0WH_inv h s c fs hi).2 hpc).2

end Inv

end Spike.Lib.A64.HelloPh.StartGlue

/-- info: 'Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH

/-- info: 'Spike.Lib.A64.HelloPh.StartGlue.h0TakeH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartGlue.h0TakeH_of

/-- info: 'Spike.Lib.A64.HelloPh.StartGlue.h0TakeOwnH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartGlue.h0TakeOwnH_of
