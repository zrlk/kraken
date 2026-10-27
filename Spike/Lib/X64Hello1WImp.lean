/-
**Two node obligations into one** (x86-64; the twin of the `.imp` lemmas of
`Spike/Test/A64Hello1W0N.lean`): an obligation inside `W` from one inside
`W1`, with the outside moves `K`, and one inside `W2`, with none, where
`W1 ∧ W2` lies inside `W`. The node lemmas give `W1` (`Wr`, their `SFacts`);
`W2` carries the per-state facts they do not.

- `NodeW.imp`, `BlkW.imp`: a node and a block node.
- `XProW.imp`, `XExitW.imp`: a prologue and an exit tail.
- `Alloc.AllocW.imp`, `Print.PrintW.imp`: `scc_rt_alloc` and `print`.
- `RdPreW.imp`, `RdPostW.imp`: `wc_rodata` up to and from the allocator's
  return.
- `WcBody1W.imp`, `Wc1W.imp`: `wc_main`'s body and `wc_main`.
- `MainPreW.imp`, `MainPostW.imp`, `MainX2W.imp`: `scc_rt_main` up to the
  allocator's return, from `.x13`, from `.x2`; `MainPostSW.imp`: from `.x13`
  at depth (fragments with frames).
-/
import Spike.Lib.X64Hello1SetupPost

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (FragS Frag Region MemSide)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W1 W2 : Frag isa} {K : State → State → Prop}

/-- **A node inside `W`** from one inside `W1` not moved by `K` and one
inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem NodeW.imp {n : ND} (h1 : NodeW W1 K exe endPc R F n) (h2 : NodeW W2 (fun _ _ => False) exe endPc R F n)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : NodeW W K exe endPc R F n := fun s c hA =>
  ⟨hw s c (h1 s c hA).1 (h2 s c hA).1, (h1 s c hA).2⟩

/-- **A block node inside `W`** from one inside `W1` not moved by `K` and
one inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem BlkW.imp {n : ND} {blk : List (Directive × Nat)} (h1 : BlkW W1 K exe endPc R F n blk)
    (h2 : BlkW W2 (fun _ _ => False) exe endPc R F n blk) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    BlkW W K exe endPc R F n blk := fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
  ⟨hw _ c (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1 (h2 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1,
    (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2⟩

namespace Flow

/-- **A prologue inside `W`** from two (`NodeW.imp`, `BlkW.imp`). -/
theorem XProW.imp {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop}
    (h1 : XProW W1 K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J)
    (h2 : XProW W2 (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨BlkW.imp h1.w0 h2.w0 hw, BlkW.imp h1.w1 h2.w1 hw, NodeW.imp h1.w2 h2.w2 hw, BlkW.imp h1.w3 h2.w3 hw,
    BlkW.imp h1.w4 h2.w4 hw⟩

/-- **An exit tail inside `W`** from two. -/
theorem XExitW.imp {n : ND} {sp b : Int} {k : Int64} {z0 z1 z2 : Nat}
    (h1 : XExitW W1 K exe endPc R F n sp b k z0 z1 z2)
    (h2 : XExitW W2 (fun _ _ => False) exe endPc R F n sp b k z0 z1 z2)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : XExitW W K exe endPc R F n sp b k z0 z1 z2 :=
  ⟨BlkW.imp h1.w0 h2.w0 hw, NodeW.imp h1.w1 h2.w1 hw⟩

end Flow

/-- **`scc_rt_alloc` inside `W`** from two (`NodeW.imp`, `BlkW.imp`). -/
theorem Alloc.AllocW.imp {ms : MemSide isa} {q : Alloc.Call}
    (h1 : Alloc.AllocW ms q W1 K exe endPc R F) (h2 : Alloc.AllocW ms q W2 (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Alloc.AllocW ms q W K exe endPc R F :=
  ⟨BlkW.imp h1.e h2.e hw, BlkW.imp h1.entry h2.entry hw, BlkW.imp h1.j1 h2.j1 hw, NodeW.imp h1.cnt h2.cnt hw,
    BlkW.imp h1.c1 h2.c1 hw, NodeW.imp h1.rmw h2.rmw hw, BlkW.imp h1.c2 h2.c2 hw, BlkW.imp h1.j2 h2.j2 hw,
    BlkW.imp h1.slow h2.slow hw, BlkW.imp h1.j3 h2.j3 hw, BlkW.imp h1.full h2.full hw, BlkW.imp h1.ok h2.ok hw,
    NodeW.imp h1.f1 h2.f1 hw, BlkW.imp h1.o1 h2.o1 hw, NodeW.imp h1.f2 h2.f2 hw, BlkW.imp h1.o2 h2.o2 hw,
    NodeW.imp h1.s2 h2.s2 hw, BlkW.imp h1.o3 h2.o3 hw, NodeW.imp h1.f3 h2.f3 hw, BlkW.imp h1.o4 h2.o4 hw,
    NodeW.imp h1.f4 h2.f4 hw, BlkW.imp h1.o5 h2.o5 hw, NodeW.imp h1.f5 h2.f5 hw, BlkW.imp h1.o6 h2.o6 hw,
    NodeW.imp h1.f6 h2.f6 hw, BlkW.imp h1.o7 h2.o7 hw, NodeW.imp h1.f7 h2.f7 hw, BlkW.imp h1.o8 h2.o8 hw,
    NodeW.imp h1.hdr h2.hdr hw, BlkW.imp h1.o9 h2.o9 hw, NodeW.imp h1.ret h2.ret hw⟩

/-- **`print` inside `W`** from two (`BlkW.imp`). -/
theorem Print.PrintW.imp {c0 : Ctl} {rbp0 ra : BitVec 64}
    (h1 : Print.PrintW c0 rbp0 ra W1 K exe endPc R F)
    (h2 : Print.PrintW c0 rbp0 ra W2 (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Print.PrintW c0 rbp0 ra W K exe endPc R F :=
  ⟨BlkW.imp h1.e h2.e hw, BlkW.imp h1.n1 h2.n1 hw, BlkW.imp h1.loop h2.loop hw, BlkW.imp h1.n3 h2.n3 hw,
    BlkW.imp h1.write h2.write hw, BlkW.imp h1.n5 h2.n5 hw, BlkW.imp h1.n6 h2.n6 hw,
    BlkW.imp h1.chk2 h2.chk2 hw, BlkW.imp h1.n8 h2.n8 hw, BlkW.imp h1.chk3 h2.chk3 hw,
    BlkW.imp h1.n10 h2.n10 hw, BlkW.imp h1.adv h2.adv hw, BlkW.imp h1.fail h2.fail hw,
    BlkW.imp h1.done h2.done hw⟩

namespace Flow.Hello1

/-- **`wc_rodata` up to the allocator's return inside `W`** from two. -/
theorem RdPreW.imp {ms : MemSide isa} {J0 Jc : AS → Ctl → Prop}
    (h1 : RdPreW W1 K exe endPc R F ms J0 Jc) (h2 : RdPreW W2 (fun _ _ => False) exe endPc R F ms J0 Jc)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : RdPreW W K exe endPc R F ms J0 Jc :=
  ⟨XProW.imp h1.pro h2.pro hw, BlkW.imp h1.e h2.e hw, fun q hok hq =>
    Alloc.AllocW.imp (h1.alloc q hok hq) (h2.alloc q hok hq) hw⟩

/-- **`wc_rodata` from the allocator's return inside `W`** from two. -/
theorem RdPostW.imp {Jp J1 J2 J3 J4 : AS → Ctl → Prop}
    (h1 : RdPostW W1 K exe endPc R F Jp J1 J2 J3 J4) (h2 : RdPostW W2 (fun _ _ => False) exe endPc R F Jp J1 J2 J3 J4)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : RdPostW W K exe endPc R F Jp J1 J2 J3 J4 :=
  ⟨BlkW.imp h1.s0 h2.s0 hw, NodeW.imp h1.l1 h2.l1 hw, BlkW.imp h1.s1 h2.s1 hw, NodeW.imp h1.x1 h2.x1 hw,
    BlkW.imp h1.s2 h2.s2 hw, NodeW.imp h1.l2 h2.l2 hw, BlkW.imp h1.s3 h2.s3 hw, NodeW.imp h1.x2 h2.x2 hw,
    BlkW.imp h1.s4 h2.s4 hw⟩

/-- **`wc_main`'s body inside `W`** from two. -/
theorem WcBody1W.imp {J : AS → Ctl → Prop}
    (h1 : WcBody1W W1 K exe endPc R F J) (h2 : WcBody1W W2 (fun _ _ => False) exe endPc R F J)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : WcBody1W W K exe endPc R F J :=
  ⟨BlkW.imp h1.e h2.e hw, NodeW.imp h1.mul h2.mul hw, BlkW.imp h1.e2 h2.e2 hw,
    fun g hg => Print.PrintW.imp (h1.print g hg) (h2.print g hg) hw, BlkW.imp h1.x15 h2.x15 hw⟩

/-- **`wc_main` inside `W`** from two. -/
theorem Wc1W.imp {ms : MemSide isa} {J0 : AS → Ctl → Prop}
    (h1 : Wc1W W1 K exe endPc R F ms J0) (h2 : Wc1W W2 (fun _ _ => False) exe endPc R F ms J0)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Wc1W W K exe endPc R F ms J0 :=
  ⟨XProW.imp h1.pro h2.pro hw, WcBody1W.imp h1.body h2.body hw⟩

/-- **`scc_rt_main` up to the allocator's return inside `W`** from two. -/
theorem MainPreW.imp {ms : MemSide isa} {J : AS → Ctl → Prop}
    (h1 : MainPreW W1 K exe endPc R F ms J) (h2 : MainPreW W2 (fun _ _ => False) exe endPc R F ms J)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : MainPreW W K exe endPc R F ms J :=
  ⟨XProW.imp h1.pro h2.pro hw, BlkW.imp h1.call h2.call hw, fun m0 σC => RdPreW.imp (h1.rd m0 σC) (h2.rd m0 σC) hw⟩

/-- **`scc_rt_main` from `.x2` inside `W`** from two. -/
theorem MainX2W.imp {ms : MemSide isa} {σC : AS} {Jr Jw : AS → Ctl → Prop}
    (h1 : MainX2W W1 K exe endPc R F ms σC Jr Jw) (h2 : MainX2W W2 (fun _ _ => False) exe endPc R F ms σC Jr Jw)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : MainX2W W K exe endPc R F ms σC Jr Jw :=
  ⟨BlkW.imp h1.x2 h2.x2 hw, fun g => Wc1W.imp (h1.wc g) (h2.wc g) hw, XExitW.imp h1.exit h2.exit hw⟩

/-- **`scc_rt_main` from `.x13` inside `W`** from two. -/
theorem MainPostW.imp {ms : MemSide isa} {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop}
    (h1 : MainPostW W1 K exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (h2 : MainPostW W2 (fun _ _ => False) exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : MainPostW W K exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw :=
  ⟨RdPostW.imp h1.rd h2.rd hw, BlkW.imp h1.x2 h2.x2 hw, fun g => Wc1W.imp (h1.wc g) (h2.wc g) hw,
    XExitW.imp h1.exit h2.exit hw⟩

/-- **`scc_rt_main` from `.x13` at depth inside `W`** from two, fragments
with frames: `W1 ∧ W2` inside `W` at every frame list. -/
theorem MainPostSW.imp {W W1 W2 : FragS isa} {ms : List TermRun.Frame → MemSide isa} {fr : TermRun.Frame}
    {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop}
    (h1 : MainPostSW W1 K exe endPc R F ms fr m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (h2 : MainPostSW W2 (fun _ _ => False) exe endPc R F ms fr m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (hw : ∀ s c fs, W1 s c fs → W2 s c fs → W s c fs) :
    MainPostSW W K exe endPc R F ms fr m0 σC Jp J1 J2 J3 J4 Jr Jw :=
  ⟨RdPostW.imp h1.rd h2.rd fun s c => hw s c [fr], MainX2W.imp h1.tl h2.tl fun s c => hw s c []⟩

end Flow.Hello1

end Spike.Lib.X64
