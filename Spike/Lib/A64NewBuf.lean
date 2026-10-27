/-
**A buffer allocation's call of `scc_rt_alloc` on AArch64, for any
program and any caller frame**: the call node of a lowered
`let x = newBuf a τ in e` (the arguments in `x0`, `x1`, `x2`, the return
address in `x30`) to the allocator's return at the landing pc or its heap
abort, as one segment inside `W`. The allocator's code comes from
`allocIn prog = true`; the caller's frame is `fs` bytes (`sp` at `-fs`), the
allocator's `allocFrame` below it.

- `allocFrame`, `allocAbortDepth`: the allocator's frame (160) and the depth
  below the caller's entry `sp` at its heap abort (`fs + 160`;
  `allocAbortDepth_48`: `wc_rodata`'s 48 give 208, the region bound of
  `hello1_rodata_pre_runW`).
- `NBX`, `nbX`: the exits: the return at the landing pc `pcR` (the
  allocator's return facts, the source past its allocation step, the
  caller's cells outside the allocator's region as at the call), and the
  heap abort.
- `AllocCtx`, `newBuf_callW_ctx`, `newBuf_callW`: the rule (the allocator's
  states asked in the call's context, or without it). The call's premises are asked at the call
  node's controls (`hq`), the return address is `pcR` (`hra`), the counter
  and the headers unmapped under `F` (`hmem`), a fresh label's allocation
  lands in `ms.xa` (`hxa`), the allocator's states inside `W` (`hW`);
  `wc_rodata`'s call is an instance (an `example`).
- `nbJc`, `newBuf_blkW`: the rule after the argument block ending in the
  call, the source taking a local run in the block.
- `Call.ret_hdrAt`: the returned base is the header's address plus 8 (the
  header is the word below the base); regression checks with a nonzero
  trace-word field.
-/
import Spike.Lib.A64Hello1Rodata

namespace Spike.Lib.A64.Flow

namespace NewBuf

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull mOf)

set_option linter.unusedSimpArgs false

/-! ## The allocator's frame -/

/-- The allocator's frame, in bytes below its entry `sp`. -/
def allocFrame : Int := 160

/-- **The depth of the heap abort** below the caller's entry `sp`, for a
caller frame of `fs` bytes: the allocator's frame below the caller's. -/
def allocAbortDepth (fs : Int) : Int := fs + allocFrame

/-- `wc_rodata`'s frame of 48 gives the region bound 208. -/
theorem allocAbortDepth_48 : allocAbortDepth 48 = 208 := rfl

/-! ## The exits -/

/-- The exits of a buffer allocation's call. -/
inductive NBX where
  | ret | abort

section Ex

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat) (R : Region)
  (fs : Int) (pcR : Int64) (Jc : AS → Ctl → Prop)

/-- **The exits**: the allocator's return at the landing pc `pcR` (some
call whose source control a state of the call node `Jc` had, the caller's
cells outside the allocator's region as in that state, the allocator's
return facts), and its heap abort (some call at its full arena, whose
source control a state of `Jc` had, the caller's cells outside the
allocator's region as in that state). -/
def nbX : NBX → ND
  | .ret => ⟨pcR, ⟨-fs, []⟩, fun σ c => ∃ q : {q : Call // q.OK ms lab},
      (∃ σC, Jc σC q.1.c0 ∧ ∀ k, R.Off k → ¬ (R.callee (-fs) (-160) 0).Off (k - -fs) → σ.slot k = σC.slot k) ∧
      (Alloc.E lab ms q.1 lbl .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-allocAbortDepth fs, []⟩, fun σ c => σ.regs.X0 = 2 ∧
      ∃ q : {q : Call // q.OK ms lab}, Jfull ms q.1 c ∧
        ∃ σC, Jc σC q.1.c0 ∧ ∀ k, R.Off k → ¬ (R.callee (-fs) (-160) 0).Off (k - -fs) → σ.slot k = σC.slot k⟩

end Ex

/-! ## The rule -/

/-- **The allocator's call context** at the memory `m`, for the call `q`
from the caller's frame of `fs` bytes in its region `R` at the call node's
invariant `Jc`: some caller's state `mC`, `σC` of `Jc` whose entry into the
allocator is at `q`'s entry, the caller's cells outside the allocator's
region as at the call (`call_nd_FWK`'s callee frame condition). -/
def AllocCtx (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (fs : Int) (Jc : AS → Ctl → Prop)
    (q : Call) (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-fs, []⟩ mC σC ∧ Jc σC c ∧ (Alloc.N lab ms q .e).J (enter (-fs) σC) c ∧
    CKept R (-fs) (-160) 0 mC m

section Rule

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **A buffer allocation's call is one segment inside `W`** in any valid
layout `exe` of a program with the allocator's code (`allocIn`): from the
allocator's entry with the caller's frame of `fs` bytes (`sp` at `-fs`,
16-aligned, the region reaching `allocAbortDepth fs` below the entry) at
the invariant `Jc`, to the return at `pcR` or the heap abort (`nbX`). At
each state of `Jc` the arguments are some call's (`hq`) and the return
address is `pcR` (`hra`); the counter and every header the call may store
are unmapped under `F` (`hmem`); a fresh label's allocation, in any frame
condition below `F` whose memories some state of the call node gives with
the caller's cells kept, lands in `ms.xa` (`hxa`); and the allocator's
states for every call with its premises returning to `pcR` are inside `W`
in its region, in the call's context (`hW`, `AllocCtx`). -/
theorem newBuf_callW_ctx {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {fs : Int} (hfs : fs % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hkc : -fs < R.hi)
    {pcR : Int64} {Jc : AS → Ctl → Prop}
    (hq : ∀ σ c, Jc σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧ σ.regs.X2.toBitVec = q.u ms)
    (hra : ∀ σ c, Jc σ c → σ.regs.X30.toBitVec = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs, []⟩ mC σC ∧ Jc σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs) σC) c ∧
        CKept R (-fs) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs) (-160) 0) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hW : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs) (-160) 0)
        (fun m => F m ∧ CallerCells R (-fs) (-160) 0 m ∧
          AllocCtx ms (_root_.Executable.labels exe).label R fs Jc q m)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_alloc", ⟨-fs, []⟩, Jc⟩)
      (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc x) s c) := by
  let lab := (_root_.Executable.labels exe).label
  have hlo' : R.lo ≤ -fs + -160 := by
    have := hlo; simp only [allocAbortDepth, allocFrame] at this; omega
  refine (call_nd_FWK (KC := False) (lo' := -160) (hi' := 0) (M := fun _ => True) (F₂ := F)
      (N := fun e : Empty => e.elim)
      (Ne := fun g : {q : Call // q.OK ms lab} => Alloc.N lab ms g.1 .e)
      (Ex := fun g : {q : Call // q.OK ms lab} => Alloc.E lab ms g.1 lbl)
      (E := nbX ms lab lbl R fs pcR Jc)
      hR hal hF hlo' (by decide) hkc (by decide) (by show (-fs) % 16 = 0; omega) (by decide) (by decide)
      (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hal' hlo2 hhi2 hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, hJC, ⟨-, -, h30', -⟩⟩ := hg
        have hgra : g.1.ra = pcR.toBitVec := by
          rw [← h30']; exact hra σC c hJC
        exact (seg_alloc_ofW hp hend hprog hF' hR' hal' hlo2 hhi2 g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (hxa g F' hFF hkeep)
          (allocW_mono (hW g.1 g.2 hgra) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_).mono_post ?_
  · intro σC c hJ
    obtain ⟨q, hok, hc, h0, h1, h2⟩ := hq σC c hJ
    exact ⟨⟨{ q with x29 := σC.regs.X29.toBitVec, ra := σC.regs.X30.toBitVec }, { hok with }⟩, rfl,
      hc.symm, rfl, rfl, h0, h1, h2⟩
  · rintro g y σC c σx c' σR hJC ⟨hc, -, h30', -⟩ hx hreg - hsl
    cases y
    · refine .inr ⟨NBX.ret, ?_, ?_, g, ⟨σC, hc ▸ hJC, hsl⟩, ?_⟩
      · show pcR = Int64.ofBitVec g.1.ra
        rw [← h30']
        show _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [hra σC c hJC, int64_ofBitVec_toBitVec]
      · show SO.le ⟨-fs, []⟩ ⟨-fs + 0, []⟩ = true
        simp [SO.le]
      · simp only [Alloc.E] at hx ⊢
        rw [hreg]; exact hx
    · obtain ⟨h2, hfull⟩ := hx
      refine .inr ⟨NBX.abort, rfl, ?_, ?_, g, hfull, σC, hc ▸ hJC, hsl⟩
      · show SO.le ⟨-allocAbortDepth fs, []⟩ ⟨-fs + -160, []⟩ = true
        simp only [SO.le, List.all_nil, Bool.and_true, decide_eq_true_eq]
        show -(fs + 160) = -fs + -160
        omega
      · show σR.regs.X0 = 2
        rw [hreg]; exact h2
  · rintro s c (⟨j, -⟩ | h)
    · exact j.elim
    · exact h

/-- **A buffer allocation's call is one segment inside `W`**
(`newBuf_callW_ctx` with the allocator's states inside `W` without the
call's context). -/
theorem newBuf_callW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {fs : Int} (hfs : fs % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hkc : -fs < R.hi)
    {pcR : Int64} {Jc : AS → Ctl → Prop}
    (hq : ∀ σ c, Jc σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧ σ.regs.X2.toBitVec = q.u ms)
    (hra : ∀ σ c, Jc σ c → σ.regs.X30.toBitVec = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs, []⟩ mC σC ∧ Jc σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs) σC) c ∧
        CKept R (-fs) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs) (-160) 0) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hW : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs) (-160) 0) (fun m => F m ∧ CallerCells R (-fs) (-160) 0 m)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_alloc", ⟨-fs, []⟩, Jc⟩)
      (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc x) s c) :=
  newBuf_callW_ctx hp hend hprog hF hR hal hfs hlo hkc hq hra hmem hxa
    fun q hok h => allocW_mono (hW q hok h) fun _ h => ⟨h.1, h.2.1⟩

/-- **The call node after the argument block** `B` from `pc` (offsets `o`):
the block's end from a state of `J1`. -/
def nbJc (lab : Label → Int64) (B : List Directive) (pc : Int64) (o : SO) (J1 : AS → Ctl → Prop) :
    AS → Ctl → Prop :=
  fun σ c => ∃ σ0, J1 σ0 c ∧ σ = (arun lab B ⟨pc, o, σ0⟩).σ

/-- **A buffer allocation, its argument block and call, is one segment
inside `W`**: `newBuf_callW` after the block `B` at `pc` (in the caller's
frame of `fs` bytes) ending in the call (`ha`: the allocator's entry, the
offsets kept), the source taking a local run from each control of `J` to
one of `J1` at the same state (`hloc`); the call's premises and the return
address are asked of the block's end from `J1` (`hq`, `hra`), the call
node's invariant is `nbJc`. -/
theorem newBuf_blkW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {fs : Int} (hfs : fs % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hkc : -fs < R.hi)
    {B : List Directive} {pc pcR : Int64} {lo hi : Int} {J J1 : AS → Ctl → Prop}
    (hne : B ≠ []) (hok : okBlk lo hi ⟨-fs, []⟩ B = true) (hlo0 : R.lo ≤ lo) (hhi0 : hi ≤ R.hi)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc B)
    (ha : ∀ σ, (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).pc =
        (_root_.Executable.labels exe).label "scc_rt_alloc" ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).so = ⟨-fs, []⟩)
    (hloc : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X0.toBitVec = q.h ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X1.toBitVec = q.k ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X2.toBitVec = q.u ms)
    (hra : ∀ σ c, J1 σ c →
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X30.toBitVec = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label B pc ⟨-fs, []⟩ J1 σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs) σC) c ∧
        CKept R (-fs) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs) (-160) 0) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hWB : BlkW W K exe endPc R F ⟨pc, ⟨-fs, []⟩, J⟩ B)
    (hW : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs) (-160) 0) (fun m => F m ∧ CallerCells R (-fs) (-160) 0 m ∧
        AllocCtx ms (_root_.Executable.labels exe).label R fs (nbJc (_root_.Executable.labels exe).label B pc
          ⟨-fs, []⟩ J1) q m)) :
    SegW W K p lbl ms (At exe endPc R F ⟨pc, ⟨-fs, []⟩, J⟩)
      (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR
        (nbJc (_root_.Executable.labels exe).label B pc ⟨-fs, []⟩ J1) x) s c) := by
  let lab := (_root_.Executable.labels exe).label
  let nC : ND := ⟨lab "scc_rt_alloc", ⟨-fs, []⟩, nbJc lab B pc ⟨-fs, []⟩ J1⟩
  refine SegW.seq (Q := At exe endPc R F nC)
    ((seg_ndW (N := fun _ : Unit => nC) (E := fun e : Empty => e.elim) hne hok hF hR hal hlo0 hhi0 hc hWB
      fun σ c hJ => ?_).mono_post fun s c h => ?_)
    (newBuf_callW_ctx hp hend hprog hF hR hal hfs hlo hkc
      (fun σ c ⟨σ0, hJ1, hσ⟩ => hσ ▸ hq σ0 c hJ1) (fun σ c ⟨σ0, hJ1, hσ⟩ => hσ ▸ hra σ0 c hJ1) hmem hxa hW)
  · obtain ⟨c', hr, hJ1⟩ := hloc σ c hJ
    refine ⟨c', hr, .inl ⟨(), (ha σ).1.symm, ?_, σ, hJ1, rfl⟩⟩
    rw [(ha σ).2]; show SO.le ⟨-fs, []⟩ ⟨-fs, []⟩ = true; simp [SO.le]
  · rcases h with ⟨_, h⟩ | ⟨x, _⟩
    · exact h
    · exact x.elim

open Hello1 (rN) in
/-- `wc_rodata`'s call of the allocator is an instance (frame 48, the
landing at `.sp0`, `hello1_alloc` for the allocator's code). -/
example {W : Frag isaLSE2} {K : State → State → Prop} {J0 : AS → Ctl → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hW : ∀ q : Call, q.ra = ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0").toBitVec →
      AllocW ms q W K exe endPc (R.callee (-48) (-160) 0) (fun m => F m ∧ CallerCells R (-48) (-160) 0 m))
    (hq : ∀ σ c, (rN (_root_.Executable.labels exe).label J0 .call).J σ c → ∃ q : Call,
      q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧ σ.regs.X2.toBitVec = q.u ms)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN (_root_.Executable.labels exe).label J0 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-48) (-160) 0) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F (rN (_root_.Executable.labels exe).label J0 .call))
      (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R 48
        ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0")
        (rN (_root_.Executable.labels exe).label J0 .call).J x) s c) :=
  newBuf_callW (fs := 48) hp hend hello1_alloc hF hR hal (by decide)
    (by rw [allocAbortDepth_48]; exact hlo) (by omega) hq (fun _ _ h => h.2.2.2.2) hmem hxa
    fun q _ h => hW q h

end Rule

/-! ## The header below the returned base -/

/-- **The returned base is the header's address plus 8**: with the call's
premises, the allocator's return value `heap + 16·old + off` is
`hdrAt old + 8`, the header the word below it. -/
theorem Call.ret_hdrAt {ms : MemSide isaLSE2} {lab : Label → Int64} {q : Call} (hq : q.OK ms lab)
    (old : Nat) : ms.heap + 16 * old + ms.off q.n q.τ = q.hdrAt ms old + 8 := by
  rw [hq.off]; simp only [Call.hdrAt]; omega

/-- A header with trace-word field 3 (`257 ||| 3 <<< 22`). -/
example : (mOf (257#64 ||| 3#64 <<< 22)).toNat = 3 := by decide

/-- With two elements and trace-word field 3, the header for the counter's
old value 5 sits `16·5 + 8·(2·3)` past the arena's base. -/
example {ms : MemSide isaLSE2} {q : Call} (hn : q.n = 2) (hh : q.h = 257#64 ||| 3#64 <<< 22) :
    q.hdrAt ms 5 = ms.heap + 80 + 48 := by
  have hm : (mOf q.h).toNat = 3 := by rw [hh]; decide
  simp only [Call.hdrAt, hn, hm]

end NewBuf

end Spike.Lib.A64.Flow
