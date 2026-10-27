/-
**A buffer allocation's call of `scc_rt_alloc` on x64, for any program
and any caller frame**: the x64 twin of `Spike/Lib/A64NewBuf.lean`. The
call node of a lowered `let x = newBuf a τ in e` (the arguments in `%rdi`,
`%rsi`, `%rdx`, the return address pushed below the caller's frame) to the
allocator's return at the landing pc or its heap abort, as one segment
inside `W`. The allocator's code comes from `allocIn cells = true`; the
caller's frame is `fs` bytes (`%rsp` at `-fs`), the pushed return address at
`-fs - 8`, the allocator's frame of `allocFrame` below it.

- `allocFrame`, `allocAbortDepth`: the allocator's frame (160) and the depth
  below the caller's entry `%rsp` at its heap abort (`fs + 8 + 160`;
  `allocAbortDepth_40`: `wc_rodata`'s 40 give 208, the region bound of
  `hello1_rodata_pre_segW`).
- `NBX`, `nbX`: the exits: the return at the landing pc `pcR` (the
  allocator's return facts, the source past its allocation step, `%rbp`
  and the caller's cells outside the allocator's region as at the call),
  and the heap abort.
- `newBuf_callW_ctx`: the rule. The call's premises are asked at the call
  node's controls (`hq`), the pushed return address is `pcR` (`hra`), the
  counter and the headers unmapped under `F` (`hmem`), a fresh label's
  allocation lands in `ms.xa` (`hxa`), the allocator's states inside `W`
  in the call's context (`hW`, `AllocCtx`); `newBuf_callW` without the
  context.
- `nbJc`, `newBuf_blkW`: the rule after the argument block ending in the
  call, the source taking a local run in the block.

Where x64 differs from AArch64: the return address is the pushed slot at
`-fs - 8`, not a register; the allocator's region reaches 8 above its
entry `%rsp` (the return address's cell); no 16-alignment is asked.
-/
import Spike.Lib.X64Hello1Rodata

namespace Spike.Lib.X64.Flow

namespace NewBuf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.X64.Flow.Hello1 (AG allocW_mono)

set_option linter.unusedSimpArgs false

/-! ## The allocator's frame -/

/-- The allocator's frame, in bytes below its entry `%rsp`. -/
def allocFrame : Int := 160

/-- **The depth of the heap abort** below the caller's entry `%rsp`, for a
caller frame of `fs` bytes: the pushed return address and the allocator's
frame below the caller's. -/
def allocAbortDepth (fs : Int) : Int := fs + 8 + allocFrame

/-- `wc_rodata`'s frame of 40 gives the region bound 208. -/
theorem allocAbortDepth_40 : allocAbortDepth 40 = 208 := rfl

/-! ## The exits -/

/-- The exits of a buffer allocation's call. -/
inductive NBX where
  | ret | abort

section Ex

variable (ms : MemSide isa) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat) (R : Region)
  (fs : Int) (pcR : Int64) (Jc : AS → Ctl → Prop)

/-- **The exits**: the allocator's return at the landing pc `pcR` (some
call whose source control a state of the call node `Jc` had, `%rbp` and
the caller's cells outside the allocator's region as in that state, the
allocator's return facts), and its heap abort (some call at its full
arena, whose source control a state of `Jc` had, the caller's cells
outside the allocator's region as in that state). -/
def nbX : NBX → ND
  | .ret => ⟨pcR, ⟨-fs, []⟩, fun σ c => ∃ q : AG ms lab,
      (∃ σC, Jc σC q.1.c0 ∧ σ.regs.rbp = σC.regs.rbp ∧
        ∀ k, R.Off k → ¬ (R.callee (-fs - 8) (-160) 8).Off (k - (-fs - 8)) → σ.slot k = σC.slot k) ∧
      (Alloc.E lab ms q.1 lbl .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-allocAbortDepth fs, []⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧
      ∃ q : AG ms lab, Jfull ms q.1 c ∧ ∃ σC, Jc σC q.1.c0 ∧
        ∀ k, R.Off k → ¬ (R.callee (-fs - 8) (-160) 8).Off (k - (-fs - 8)) → σ.slot k = σC.slot k⟩

end Ex

/-! ## The rule -/

/-- **The allocator's call context** at the memory `m`, for the call `q`
from the caller's frame of `fs` bytes in its region `R` at the call node's
invariant `Jc` (`%rsp` at `-fs - 8` past the pushed return address): some
caller's state `mC`, `σC` of `Jc` whose entry into the allocator is at
`q`'s entry, the caller's cells outside the allocator's region as at the
call (`call_nd_FWK`'s callee frame condition). -/
def AllocCtx (ms : MemSide isa) (lab : Label → Int64) (R : Region) (fs : Int) (Jc : AS → Ctl → Prop)
    (q : Call) (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-fs - 8, []⟩ mC σC ∧ Jc σC c ∧ (Alloc.N lab ms q .e).J (enter (-fs - 8) σC) c ∧
    CKept R (-fs - 8) (-160) 8 mC m

section Rule

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **A buffer allocation's call is one segment inside `W`** in any valid
layout `exe` of cells with the allocator's code (`allocIn`): from the
allocator's entry with the caller's frame of `fs` bytes (`%rsp` at
`-fs - 8` past the pushed return address, the region reaching
`allocAbortDepth fs` below the caller's entry) at the invariant `Jc`, to the
return at `pcR` or the heap abort (`nbX`). At each state of `Jc` the
arguments are some call's (`hq`) and the pushed return address is `pcR`
(`hra`); the counter and every header the call may store are unmapped
under `F` (`hmem`); a fresh label's allocation, in any frame condition below
`F` whose memories some state of the call node gives with the caller's
cells kept, lands in `ms.xa` (`hxa`); and the allocator's states for every
call with its premises returning to `pcR` are inside `W` in its region, in
the call's context (`hW`, `AllocCtx`). -/
theorem newBuf_callW_ctx {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hprog : Alloc.allocIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    {fs : Int} (hfs : fs % 8 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hhi : -fs ≤ R.hi)
    {pcR : Int64} {Jc : AS → Ctl → Prop}
    (hq : ∀ σ c, Jc σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms)
    (hra : ∀ σ c, Jc σ c → σ.slot (-fs - 8) = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs - 8, []⟩ mC σC ∧ Jc σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs - 8) σC) c ∧
        CKept R (-fs - 8) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs - 8) (-160) 8) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hW : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs - 8) (-160) 8)
        (fun m => F m ∧ CallerCells R (-fs - 8) (-160) 8 m ∧
          AllocCtx ms (_root_.Executable.labels exe).label R fs Jc q m)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_alloc", ⟨-fs - 8, []⟩, Jc⟩)
      (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc x) s c) := by
  let lab := (_root_.Executable.labels exe).label
  have e0 : (-fs - 8 : Int) - 0 = -fs - 8 := by omega
  have e00 : (-fs - 8 : Int) - 0 + 0 = -fs - 8 := by omega
  refine (call_nd_FWK (KC := False) (e0 := 0) (lo' := -160) (hi' := 8) (M := fun _ => True) (F₂ := F)
      (N := fun e : Empty => e.elim)
      (Ne := fun g : AG ms lab => Alloc.N lab ms g.1 .e)
      (Ex := fun g : AG ms lab => Alloc.E lab ms g.1 lbl)
      (E := nbX ms lab lbl R fs pcR Jc)
      hR hF (by show R.lo ≤ (-fs - 8) - 0 + -160; simp only [allocAbortDepth, allocFrame] at hlo; omega)
      (by decide) (by show (-fs - 8 : Int) - 0 < R.hi; omega)
      (by show (-fs - 8 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-fs - 8 : Int) - 0) % 8 = 0; omega)
      (by decide) (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, hJC, ⟨-, -, h0', -⟩⟩ := hg
        have hgra : g.1.ra = pcR.toBitVec := by
          rw [← h0', ← hra σC c hJC]
          show σC.slot ((-fs - 8) - 0 + 0) = _
          rw [e00]
        dsimp only at hR' hlo' hhi' hF' hkeep hcc ⊢
        simp only [e0] at hR' hlo' hhi' hF' hkeep hcc ⊢
        exact (Alloc.seg_allocW hp hend hprog hF' hR' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (hxa g F' hFF hkeep)
          (allocW_mono (hW g.1 g.2 hgra) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_).mono_post ?_
  · intro σC c hJ
    obtain ⟨q, hok, hc, h0, h1, h2⟩ := hq σC c hJ
    exact ⟨⟨{ q with fp := σC.regs.rbp.toBitVec, ra := σC.slot ((-fs - 8) - 0 + 0) }, { hok with }⟩, rfl,
      hc.symm, rfl, rfl, h0, h1, h2⟩
  · rintro g y σC c σx c' σR hJC ⟨hc, hfp, hra', -⟩ hx hreg - - hsl
    cases y
    · refine .inr ⟨NBX.ret, ?_, ?_, g, ⟨σC, hc ▸ hJC, ?_, ?_⟩, ?_⟩
      · show pcR = Int64.ofBitVec g.1.ra
        rw [← hra']
        show _ = Int64.ofBitVec (σC.slot ((-fs - 8) - 0 + 0))
        rw [e00, hra σC c hJC, int64_ofBitVec_toBitVec]
      · show SO.le ⟨-fs, []⟩ ⟨(-fs - 8) - 0 + 8, []⟩ = true
        simp only [SO.le, List.all_nil, Bool.and_true, decide_eq_true_eq]
        omega
      · simp only [Alloc.E] at hx
        obtain ⟨-, -, -, -, -, -, -, hbx⟩ := hx
        have : σR.regs.rbp.toBitVec = σC.regs.rbp.toBitVec := by rw [hreg, hbx, ← hfp]; rfl
        exact UInt64.eq_of_toBitVec_eq this
      · intro k hk hn
        exact hsl k hk (by show ¬ (R.callee (-fs - 8 - 0) (-160) 8).Off (k - (-fs - 8 - 0)); rw [e0]; exact hn)
      · simp only [Alloc.E] at hx ⊢
        rw [hreg]; exact hx
    · obtain ⟨h2, hfull⟩ := hx
      refine .inr ⟨NBX.abort, rfl, ?_, ?_, g, hfull, σC, hc ▸ hJC, fun k hk hn =>
        hsl k hk (by show ¬ (R.callee (-fs - 8 - 0) (-160) 8).Off (k - (-fs - 8 - 0)); rw [e0]; exact hn)⟩
      · show SO.le ⟨-allocAbortDepth fs, []⟩ ⟨(-fs - 8) - 0 + -160, []⟩ = true
        simp only [SO.le, List.all_nil, Bool.and_true, decide_eq_true_eq]
        unfold allocAbortDepth allocFrame
        omega
      · show σR.regs.rdi.toBitVec = 2#64
        rw [hreg]; exact h2
  · rintro s c (⟨j, -⟩ | h)
    · exact j.elim
    · exact h

/-- **A buffer allocation's call is one segment inside `W`**
(`newBuf_callW_ctx` with the allocator's states inside `W` without the
call's context). -/
theorem newBuf_callW {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hprog : Alloc.allocIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    {fs : Int} (hfs : fs % 8 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hhi : -fs ≤ R.hi)
    {pcR : Int64} {Jc : AS → Ctl → Prop}
    (hq : ∀ σ c, Jc σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms)
    (hra : ∀ σ c, Jc σ c → σ.slot (-fs - 8) = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs - 8, []⟩ mC σC ∧ Jc σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs - 8) σC) c ∧
        CKept R (-fs - 8) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs - 8) (-160) 8) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hW : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs - 8) (-160) 8) (fun m => F m ∧ CallerCells R (-fs - 8) (-160) 8 m)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_alloc", ⟨-fs - 8, []⟩, Jc⟩)
      (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc x) s c) :=
  newBuf_callW_ctx hp hend hprog hF hR hfs hlo hhi hq hra hmem hxa
    fun q hok h => allocW_mono (hW q hok h) fun _ h => ⟨h.1, h.2.1⟩

/-- **The call node after the argument block** `B` from `pc` (offsets `o`):
the block's end from a state of `J1`. -/
def nbJc (lab : Label → Int64) (B : List (Directive × Nat)) (pc : Int64) (o : SO) (J1 : AS → Ctl → Prop) :
    AS → Ctl → Prop :=
  fun σ c => ∃ σ0, J1 σ0 c ∧ σ = (arun lab B ⟨pc, o, σ0⟩).σ

/-- **A buffer allocation, its argument block and call, is one segment
inside `W`**: `newBuf_callW` after the block `B` at `pc` (offsets `o`, `%rsp`
at the caller's frame base `-fs`) ending in the call (`ha`: the allocator's
entry, the return address pushed, `%rsp` at `-fs - 8` with any other offsets
kept), the source taking a local run from each
control of `J` to one of `J1` at the same state (`hloc`); the call's
premises and the pushed return address are asked of the block's end from
`J1` (`hq`, `hra`), the call node's invariant is `nbJc`. -/
theorem newBuf_blkW {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hprog : Alloc.allocIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    {fs : Int} (hfs : fs % 8 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hhi : -fs ≤ R.hi)
    {B : List (Directive × Nat)} {pc pcR : Int64} {o : SO} {lo hi : Int} {J J1 : AS → Ctl → Prop}
    (hne : B ≠ []) (hok : okBlk lo hi o B = true) (hlo0 : R.lo ≤ lo) (hhi0 : hi ≤ R.hi)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc B)
    (ha : ∀ σ, (arun (_root_.Executable.labels exe).label B ⟨pc, o, σ⟩).pc =
        (_root_.Executable.labels exe).label "scc_rt_alloc" ∧
      SO.le ⟨-fs - 8, []⟩ (arun (_root_.Executable.labels exe).label B ⟨pc, o, σ⟩).so = true)
    (hloc : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, o, σ⟩).σ.regs.rdi.toBitVec = q.h ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, o, σ⟩).σ.regs.rsi.toBitVec = q.k ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, o, σ⟩).σ.regs.rdx.toBitVec = q.u ms)
    (hra : ∀ σ c, J1 σ c →
      (arun (_root_.Executable.labels exe).label B ⟨pc, o, σ⟩).σ.slot (-fs - 8) = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs - 8, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label B pc o J1 σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs - 8) σC) c ∧
        CKept R (-fs - 8) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs - 8) (-160) 8) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hWB : BlkW W K exe endPc R F ⟨pc, o, J⟩ B)
    (hW : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs - 8) (-160) 8) (fun m => F m ∧ CallerCells R (-fs - 8) (-160) 8 m ∧
        AllocCtx ms (_root_.Executable.labels exe).label R fs (nbJc (_root_.Executable.labels exe).label B pc o J1)
          q m)) :
    SegW W K p lbl ms (At exe endPc R F ⟨pc, o, J⟩)
      (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR
        (nbJc (_root_.Executable.labels exe).label B pc o J1) x) s c) := by
  let lab := (_root_.Executable.labels exe).label
  let nC : ND := ⟨lab "scc_rt_alloc", ⟨-fs - 8, []⟩, nbJc lab B pc o J1⟩
  refine SegW.seq (Q := At exe endPc R F nC)
    ((seg_ndW (N := fun _ : Unit => nC) (E := fun e : Empty => e.elim) hne hok hF hR hlo0 hhi0 hc hWB
      fun σ c hJ => ?_).mono_post fun s c h => ?_)
    (newBuf_callW_ctx hp hend hprog hF hR hfs hlo hhi
      (fun σ c ⟨σ0, hJ1, hσ⟩ => hσ ▸ hq σ0 c hJ1) (fun σ c ⟨σ0, hJ1, hσ⟩ => hσ ▸ hra σ0 c hJ1) hmem hxa hW)
  · obtain ⟨c', hr, hJ1⟩ := hloc σ c hJ
    refine ⟨c', hr, .inl ⟨(), (ha σ).1.symm, ?_, σ, hJ1, rfl⟩⟩
    exact (ha σ).2
  · rcases h with ⟨_, h⟩ | ⟨x, _⟩
    · exact h
    · exact x.elim

open Hello1 (rN aR) in
/-- `wc_rodata`'s call of the allocator is an instance (frame 40, the
landing at `.x13`, `hello1_allocIn` for the allocator's code). -/
example {W : Frag isa} {K : State → State → Prop} {J0 : AS → Ctl → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    (hW : ∀ q : Call, q.ra = ((_root_.Executable.labels exe).label ".Lwc_rodata.x13").toBitVec →
      AllocW ms q W K exe endPc (aR R) (fun m => F m ∧ CallerCells R (-48) (-160) 8 m))
    (hq : ∀ σ c, (rN (_root_.Executable.labels exe).label R J0 .call).J σ c → ∃ q : Call,
      q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN (_root_.Executable.labels exe).label R J0 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F (rN (_root_.Executable.labels exe).label R J0 .call))
      (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R 40
        ((_root_.Executable.labels exe).label ".Lwc_rodata.x13")
        (rN (_root_.Executable.labels exe).label R J0 .call).J x) s c) :=
  newBuf_callW (fs := 40) hp hend Alloc.hello1_allocIn hF hR (by decide)
    (by rw [allocAbortDepth_40]; exact hlo) (by omega) hq (fun _ _ h => h.2.2.2.2.2) hmem hxa
    fun q _ h => hW q h

end Rule

end NewBuf

end Spike.Lib.X64.Flow
