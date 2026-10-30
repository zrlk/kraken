/-
**`hello1.w`'s `wc_rodata` on x64**, inside `W`, in any valid layout of
`hello1Cells` (`Spike/Lib/X64Hello1Code.lean`), from checks decided once on
the cells (`decide +kernel`): the x64 twin of
`Spike/Lib/A64Hello1Rodata.lean`.

- `allocW_mono`: the allocator's obligations (`Spike.Lib.X64.Alloc`)
  under a stronger frame condition.
- `hello1_rodata_pre_segW`: `wc_rodata` from its entry (invariant `J0`):
  its prologue, the block passing the allocation's arguments, and the call
  of `scc_rt_alloc` (`call_nd_FWK`, the allocator's region based at the
  pushed return address, `-48`, its frame of 160 below: the region reaches
  `-208`). Exits: the allocator's return to `.x13`, and its heap abort; an
  allocation of a fresh label lands in `ms.xa` (`hxa`). The source is at a
  buffer allocation of two words with header `257` from the entry on
  (`hq`).
- `hello1_rodata_post_segW`: `wc_rodata` from `.x13` (the allocator's
  return; `%rsp` at the frame's base, `-40`, `%rbp` at the saved `%rbp`,
  `-8`, from an invariant fact, `hbp`; offsets from `%rsp` at
  `wc_rodata`'s entry) to its return: the two exchanges of the buffer's
  words (each load a hold, `holdLd_ndW`; each store the exchange,
  `xchgSt_ndW`), the results and the epilogue. The source's facts at each
  exchange stay given (`h1` … `h4`, over invariants `J1` … `J4` of
  `.x13`'s state), as does its run at the return (`hedge`).
-/
import Spike.Lib.X64Hello1Body
import Spike.Lib.X64Alloc

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_alloc` under a weaker frame condition -/

section Alloc

open Spike.Lib.X64.Flow.Ret0 (blkW_mono nodeW_mono)
open Spike.Lib.X64.Alloc

/-- The allocator's obligations under a weaker frame condition hold under a
stronger one. -/
theorem allocW_mono {ms : MemSide isa} {q : Call} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F F' : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}
    (h : AllocW ms q W K exe endPc R F) (hFF : ∀ m, F' m → F m) : AllocW ms q W K exe endPc R F' :=
  ⟨blkW_mono h.e hFF, blkW_mono h.entry hFF, blkW_mono h.j1 hFF, nodeW_mono h.cnt hFF, blkW_mono h.c1 hFF,
    nodeW_mono h.rmw hFF, blkW_mono h.c2 hFF, blkW_mono h.j2 hFF, blkW_mono h.slow hFF, blkW_mono h.j3 hFF,
    blkW_mono h.full hFF, blkW_mono h.ok hFF, nodeW_mono h.f1 hFF, blkW_mono h.o1 hFF, nodeW_mono h.f2 hFF,
    blkW_mono h.o2 hFF, nodeW_mono h.s2 hFF, blkW_mono h.o3 hFF, nodeW_mono h.f3 hFF, blkW_mono h.o4 hFF,
    nodeW_mono h.f4 hFF, blkW_mono h.o5 hFF, nodeW_mono h.f5 hFF, blkW_mono h.o6 hFF, nodeW_mono h.f6 hFF,
    blkW_mono h.o7 hFF, nodeW_mono h.f7 hFF, blkW_mono h.o8 hFF, nodeW_mono h.hdr hFF, blkW_mono h.o9 hFF,
    nodeW_mono h.ret hFF⟩

end Alloc

/-! ## `wc_rodata` up to the allocator's return -/

open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull)

/-- `wc_rodata`'s `.entry` block: the allocation's arguments, the call. -/
def rdE : List (Directive × Nat) := (parse("movq $257, %rdi
movq $2, %rsi
movq $3, %rdx
call scc_rt_alloc")).zip [7, 7, 7, 5]

/-- `wc_rodata`'s body offsets: `%rsp` at the frame's base, `%rbp` at the
saved `%rbp`. -/
abbrev oR : SO := ⟨-40, [(.rbp, -8)]⟩

block_spec rdE (-208) 8 oR rdE

/-- **`wc_rodata`'s entry block in `cells`**, `.x13` right after the call. -/
def rdEIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_rodata.entry" 0 rdE && labelGapB cells ".Lwc_rodata.entry" ".Lwc_rodata.x13" 26

theorem hello1_rdEIn : rdEIn SccCode.hello1Cells = true := by decide +kernel

/-- `wc_rodata`'s frame record as some entry state of `J0` left it: the
return address and the caller's `%rbp`. -/
def rdJ (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J0 σe c ∧ σ.slot 0 = σe.slot 0 ∧ σ.slot (-8) = σe.regs.rbp.toBitVec

/-- The allocator's ghost: a call with its premises. -/
abbrev AG (ms : MemSide isa) (lab : Label → Int64) : Type := {q : Call // q.OK ms lab}

/-- `wc_rodata`'s nodes up to the call. -/
inductive RN where
  | e | call

/-- `wc_rodata`'s exits up to the allocator's return. -/
inductive RX where
  | x13 | abort

section Rd

variable (ms : MemSide isa) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat) (R : Region)
  (J0 : AS → Ctl → Prop)

/-- **The nodes**: `.entry` (`%rbp` at the saved `%rbp`) and the
allocator's entry with its arguments, the return address `.x13` pushed. -/
def rN : RN → ND
  | .e => ⟨lab ".Lwc_rodata.entry", oR, wJ R (rdJ J0)⟩
  | .call => ⟨lab "scc_rt_alloc", ⟨-48, []⟩, fun σ c => rdJ J0 σ c ∧ σ.regs.get64 .rbp = R.addr (-8) ∧
      σ.regs.rdi.toBitVec = 257#64 ∧ σ.regs.rsi.toBitVec = 2#64 ∧ σ.regs.rdx.toBitVec = 3#64 ∧
      σ.slot (-48) = (lab ".Lwc_rodata.x13").toBitVec⟩

/-- **The exits**: the allocator's return at `.x13` (its return's facts,
the frame record and `%rbp` kept), and its heap abort. -/
def rX : RX → ND
  | .x13 => ⟨lab ".Lwc_rodata.x13", ⟨-40, []⟩, fun σ c => ∃ q : AG ms lab, rdJ J0 σ q.1.c0 ∧
      σ.regs.get64 .rbp = R.addr (-8) ∧ (Alloc.E lab ms q.1 lbl .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-208, []⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧
      ∃ q : AG ms lab, Jfull ms q.1 c ∧ ∃ σe, J0 σe q.1.c0⟩

end Rd

/-- The allocator's region at the call: based at the pushed return
address (`-48`), its frame of 160 below, the return address cell above. -/
abbrev aR (R : Region) : Region := R.callee (-48) (-160) 8

/-- **The allocator's call context in `wc_rodata`'s region `R`** at the
memory `m`: some caller's state `mC`, `σC` at the call node (`rN .call` at
the invariant `Jc`) whose entry into the allocator is at `q`'s entry, the
caller's cells outside the allocator's region as at the call
(`call_nd_FWK`'s callee frame condition). -/
def RdCtx (ms : MemSide isa) (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN lab R Jc .call).J σC c ∧ (Alloc.N lab ms q .e).J (enter (-48) σC) c ∧
    CKept R (-48) (-160) 8 mC m

/-- **`wc_rodata`'s states up to the allocator's return inside `W`**, none
moved by `K`: its prologue's, the entry block's, and the allocator's in its
region (for every call with its premises returning to `.x13`, the caller's cells outside it
holding values, in the call's context `RdCtx` at the call node's invariant
`Jc`, the source possibly advanced from `J0` in the entry block). -/
structure RdPreW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J0 Jc : AS → Ctl → Prop) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_rodata") 32 8
    ".Lwc_rodata.stk" 5 9 3 2 4 [] J0
  e : BlkW W K exe endPc R F (rN (_root_.Executable.labels exe).label R J0 .e) rdE
  alloc : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label →
    q.ra = ((_root_.Executable.labels exe).label ".Lwc_rodata.x13").toBitVec →
    AllocW ms q W K exe endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧ RdCtx ms (_root_.Executable.labels exe).label R Jc q m)

/-- `wc_rodata` up to the allocator's return is inside the trivial
predicate, with no outside moves. -/
theorem RdPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 Jc : AS → Ctl → Prop} :
    RdPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 Jc :=
  ⟨XProW.triv, BlkW.triv, fun q _ _ => Alloc.AllocW.triv ms q⟩

section RdFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` up to the allocator's return is one segment inside `W`**
in any valid layout of `hello1Cells`: from its entry (invariant `J0`,
`%rsp` at the region's offset 0, the limit word's facts for its frame of 32
below the saved `%rbp`, `hlim`) to the allocator's return at `.x13` or its
heap abort. The source at the entry is at a buffer allocation the
allocator's premises hold for, with header `257`, two elements of three
units (`hq`); the counter and the headers it may store are unmapped in
private memory under `F` (`hmem`); an allocation of a fresh label lands in
`ms.xa` (`hxa`, for every frame condition the call hands the allocator:
with its states, the caller's at the call and its cells outside the
allocator's region, as `at_leave` needs). Its states lie in `W`, none moved
by `K` (`hW`).
VACUOUS at the entry at `rodata`'s source (`hq` at `rdC0`): see X64Hello1RodataSetupG (`rdC0_not_call`). -/
theorem hello1_rodata_pre_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    {J0 : AS → Ctl → Prop} (hW : RdPreW W K exe endPc R F ms J0 J0)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec))
    (hq : ∀ σ c, J0 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN (_root_.Executable.labels exe).label R J0 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (rX ms (_root_.Executable.labels exe).label lbl R J0 y) s c) := by
  have hin := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e26 : lab ".Lwc_rodata.x13" = lab ".Lwc_rodata.entry" + Int64.ofNat 26 := label_labelGapB hp hgap
  refine SegW.seq (hello1_rodata_prologue_segW hp hend (nb := ⟨lab ".Lwc_rodata.entry", oR, rdJ J0⟩)
    hF hR (by omega) (by omega) rfl (by show SO.le oR (oF 32) = true; decide) hW.pro ?_)
    ((fn_segW (N := rN lab R J0) (E := rX ms lab lbl R J0) (fun i => ?_) RN.e).mono_pre
      fun _ _ h => At.reg_addr (r := .rbp) (k := -8) rfl h)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  cases i
  case e =>
    refine seg_ndW (by simp [rdE]) rdE_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.e
      fun σ c hJ => ⟨c, .refl c, .inl ⟨RN.call, ?_, ?_, ?_⟩⟩
    · simp only [rN]; rw [rdE_run]
    · simp only [rN]; rw [rdE_run]; rfl
    · simp only [rN] at hJ ⊢
      rw [rdE_run]
      obtain ⟨⟨σe, hJe, h0', h8⟩, hb⟩ := hJ
      refine ⟨⟨σe, hJe, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [upd_apply]; exact h0'
      · simp only [upd_apply]; exact h8
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; exact hb
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · rw [e26]
        simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
        rfl
  case call =>
    refine call_nd_FWK (KC := False) (e0 := 0) (lo' := -160) (hi' := 8) (M := fun _ => True)
      (Ne := fun g : AG ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AG ms lab => Alloc.E lab ms g.1 lbl)
      hR hF (by show R.lo ≤ -48 - 0 + -160; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, -, -, h48⟩, ⟨-, -, hra, -⟩⟩ := hg
        have hr : g.1.ra = (lab ".Lwc_rodata.x13").toBitVec := by
          rw [← hra, ← h48]; rfl
        exact (Alloc.seg_allocW hp hend Alloc.hello1_allocIn hF' hR' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (hxa g F' hFF hkeep)
          (allocW_mono (hW.alloc g.1 g.2 hr) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨σe, hJe, -, -⟩, -, h0, h1, h2, -⟩
      obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
      exact ⟨⟨{ q with fp := σC.regs.rbp.toBitVec, ra := σC.slot (-48 - 0 + 0) }, { hok with }⟩, rfl,
        hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
    · rintro g y σC c σx c' σR ⟨⟨σe, hJe, h0', h8⟩, hb, -, -, -, h48⟩ ⟨hc, hfp, hra, -⟩ hx hreg - - hsl
      cases y
      · refine .inr ⟨RX.x13, ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, g,
          ⟨σe, hc ▸ hJe, ?_, ?_⟩, ?_, ?_⟩
        · show lab ".Lwc_rodata.x13" = Int64.ofBitVec g.1.ra
          rw [← hra]
          show _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
          rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
        · rw [hsl 0 ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rN]; omega), h0']
        · rw [hsl (-8) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rN]; omega), h8]
        · simp only [Alloc.E] at hx
          obtain ⟨-, -, -, -, -, -, -, -, hbx⟩ := hx
          rw [← hb]
          simp only [Reg64s.get64]
          rw [hreg, hbx, ← hfp]; rfl
        · simp only [Alloc.E] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, hfull⟩ := hx
        refine .inr ⟨RX.abort, rfl, by show SO.le ⟨-208, []⟩ ⟨-48 - 0 + -160, []⟩ = true; decide, ?_,
          g, hfull, σe, hc ▸ hJe⟩
        show σR.regs.rdi.toBitVec = 2#64
        rw [hreg]; exact h2

end RdFn

/-! ## `wc_rodata` from the allocator's return -/

/-- `.x13`'s first block: the buffer's base saved, reloaded. -/
def rpB0 : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rcx")).zip [4, 4]

/-- `.x13`'s second block: the old first word saved, the base reloaded, the
new word built. -/
def rpB1 : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq -8(%rbp), %rcx
movabsq $8583909746840200520, %rax")).zip [4, 4, 10]

/-- `.x13`'s third block: the base reloaded. -/
def rpB2 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx")).zip [4]

/-- `.x13`'s fourth block: the old second word saved, the base reloaded,
the new word built. -/
def rpB3 : List (Directive × Nat) := (parse("movq %rax, -24(%rbp)
movq -8(%rbp), %rcx
movabsq $44634501743, %rax")).zip [4, 4, 10]

/-- `.x13`'s last block: the results, the epilogue, `ret`. -/
def rpB4 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $0, %rdx
movq $2, %rcx
movq $13, %rsi
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 7, 7, 7, 3, 1, 1]

block_spec rpB0 (-40) 8 oR rpB0
block_spec rpB1 (-40) 8 oR rpB1
block_spec rpB2 (-40) 8 oR rpB2
block_spec rpB3 (-40) 8 oR rpB3
block_spec rpB4 (-40) 8 oR rpB4

/-- **`.x13` in `cells`**: its blocks and the two exchanges' loads and
stores at their offsets. -/
def rpIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_rodata.x13" 0 rpB0 && blockAtB cells ".Lwc_rodata.x13" 8 [(ldDir .rcx 0 .rax, 3)] &&
  blockAtB cells ".Lwc_rodata.x13" 11 rpB1 && blockAtB cells ".Lwc_rodata.x13" 29 [(stDir .rcx 0 .rax, 3)] &&
  blockAtB cells ".Lwc_rodata.x13" 32 rpB2 && blockAtB cells ".Lwc_rodata.x13" 36 [(ldDir .rcx 8 .rax, 4)] &&
  blockAtB cells ".Lwc_rodata.x13" 40 rpB3 && blockAtB cells ".Lwc_rodata.x13" 58 [(stDir .rcx 8 .rax, 4)] &&
  blockAtB cells ".Lwc_rodata.x13" 62 rpB4

theorem hello1_rpIn : rpIn SccCode.hello1Cells = true := by decide +kernel

/-- The first word stored (`"Hello, w"`). -/
abbrev rpK1 : BitVec 64 := 0x77202c6f6c6c6548#64
/-- The second word stored (`"orld\n"`). -/
abbrev rpK2 : BitVec 64 := 0xa646c726f#64

/-- The frame's cells and `%rbp` from `.x13`'s state `σ0`: the base saved,
the frame record and the return address kept, `%rbp` kept. -/
def rdFr (σ0 σ : AS) : Prop :=
  σ.slot (-16) = σ0.regs.rax.toBitVec ∧ σ.slot (-8) = σ0.slot (-8) ∧ σ.slot 0 = σ0.slot 0 ∧
    σ.regs.rbp = σ0.regs.rbp

/-- `.x13`'s nodes. -/
inductive PN where
  | s0 | l1 | s1 | x1 | s2 | l2 | s3 | x2 | s4

/-- **`.x13`'s nodes**, from the invariant `Jp` at `.x13` and the source's
invariants `J1` … `J4` after each exchange's load and store (of `.x13`'s
state and the control). -/
def pN (lab : Label → Int64) (Jp J1 J2 J3 J4 : AS → Ctl → Prop) : PN → ND
  | .s0 => ⟨lab ".Lwc_rodata.x13", oR, Jp⟩
  | .l1 => ⟨lab ".Lwc_rodata.x13" + 8, oR, fun σ c => ∃ σ0, Jp σ0 c ∧
      rdFr σ0 σ ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .s1 => ⟨lab ".Lwc_rodata.x13" + 11, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧ J1 σ0 c ∧ rdFr σ0 σ⟩
  | .x1 => ⟨lab ".Lwc_rodata.x13" + 29, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J1 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.get64 .rax = rpK1 ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .s2 => ⟨lab ".Lwc_rodata.x13" + 32, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧ J2 σ0 c ∧ rdFr σ0 σ⟩
  | .l2 => ⟨lab ".Lwc_rodata.x13" + 36, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J2 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .s3 => ⟨lab ".Lwc_rodata.x13" + 40, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧ J3 σ0 c ∧ rdFr σ0 σ⟩
  | .x2 => ⟨lab ".Lwc_rodata.x13" + 58, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J3 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.get64 .rax = rpK2 ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .s4 => ⟨lab ".Lwc_rodata.x13" + 62, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧ J4 σ0 c ∧ rdFr σ0 σ⟩

/-- **`wc_rodata`'s states from the allocator's return inside `W`**, none
moved by `K`: one obligation per node. -/
structure RdPostW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Jp J1 J2 J3 J4 : AS → Ctl → Prop) : Prop where
  s0 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s0) rpB0
  l1 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .l1)
  s1 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s1) rpB1
  x1 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .x1)
  s2 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s2) rpB2
  l2 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .l2)
  s3 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s3) rpB3
  x2 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .x2)
  s4 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s4) rpB4

/-- `wc_rodata` from the allocator's return is inside the trivial
predicate, with no outside moves. -/
theorem RdPostW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {Jp J1 J2 J3 J4 : AS → Ctl → Prop} :
    RdPostW (fun _ _ => True) (fun _ _ => False) exe endPc R F Jp J1 J2 J3 J4 :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv⟩

/-- An access's address `k(%rcx)` with `%rcx` the base `.x13` started with
in `%rax`. -/
theorem bAddr_rcx_rax {r r0 : Reg64s} (h : r.get64 .rcx = r0.get64 .rax) (k : Int64) :
    bAddr r .rcx k = bAddr r0 .rax k := by
  simp only [bAddr, h]

section RpFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` from the allocator's return is one segment inside `W`**
in any valid layout of `hello1Cells`: from `.x13` (invariant `Jp` of the
state `σ0` there, `%rsp` at `-40`, `%rbp` at the saved `%rbp`, `hbp`) to
the caller's node `x` (pc the saved return address, `hra`; offsets at most
`⟨8, []⟩`). The two words at the buffer's base `%rax` and `%rax + 8` are
unmapped in private memory under `F` (`hmem`). The source runs the two
exchanges: at each load the source is at an exchange site of the word
(`h1`, `h3`) and at each store it holds it and stores the built word
(`rpK1`, `rpK2`; `h2`, `h4`), its invariants `J1` … `J4` of `σ0` and the
control in between; at the return, `x`'s invariant holds after a local run
of every state with `%rax` the base, `%rdx = 0`, `%rcx = 2`, `%rsi = 13`,
`%rbp` the saved `%rbp` and `%rsp` past the return address (`hedge`). Its
states lie in `W`, none moved by `K` (`hW`).
VACUOUS at .x13 at `rodata`'s source: see X64Hello1RodataSetupG (`hand_x13_empty`). -/
theorem hello1_rodata_post_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {Jp J1 J2 J3 J4 : AS → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hW : RdPostW W K exe endPc R F Jp J1 J2 J3 J4)
    (hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = R.addr (-8))
    (hra : ∀ σ0 c, Jp σ0 c → x.pc = Int64.ofBitVec (σ0.slot 0))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, F m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none)
    (h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x13", ⟨-40, []⟩, Jp⟩)
      (At exe endPc R F x) := by
  have hin := hello1_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  refine ((fn_segW (N := pN lab Jp J1 J2 J3 J4) (E := fun _ : Unit => x) (fun i => ?_) PN.s0).mono_post
    fun _ _ ⟨_, h⟩ => h).mono_pre fun _ _ h => At.rbp_addr h hbp
  cases i
  case s0 =>
    refine seg_ndW (by simp [rpB0]) rpB0_ok hF hR hlo hhi (code_field hp hend c0 (ofNat_zero' _)) hW.s0
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.l1, ?_, ?_, σ, hJ, ?_⟩⟩
    · simp only [pN]; rw [rpB0_run]
    · simp only [pN]; rw [rpB0_run]; rfl
    · simp only [pN]; rw [rpB0_run]
      refine ⟨⟨?_, ?_, ?_, rfl⟩, by dsimp only; rw [Reg64s.get64_set64_self]; try rfl⟩ <;> simp [Spike.Lib.upd_apply]
  case l1 =>
    refine holdLd_ndW (r := .rax) (b := .rcx) (k := 0) (by decide) hF (code_field hp hend c1 rfl) hW.l1
      fun m σ c hA hD ⟨σ0, hJ, hfr, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 0
    have hm := hmem σ0 c hJ 0 (.inl rfl)
    obtain ⟨x, sa, u, v, e, hx, hv, hh, hk⟩ := h1 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, hx, hr ▸ hv, hh, fun r w' hrd hrep =>
      .inl ⟨PN.s1, ?_, rfl, σ0, ⟨c, hJ⟩, hr ▸ hk r w' hrd hrep, hfr⟩⟩
    show lab ".Lwc_rodata.x13" + 11 = lab ".Lwc_rodata.x13" + 8 + Int64.ofNat 3
    rw [Int64.add_assoc]; rfl
  case s1 =>
    refine seg_ndW (by simp [rpB1]) rpB1_ok hF hR hlo hhi (code_field hp hend c2 rfl) hW.s1
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ⟨c, .refl c, .inl ⟨PN.x1, ?_, ?_, σ0, hJp, hJ, ?_⟩⟩
    · simp only [pN]; rw [rpB1_run, Int64.add_assoc]; rfl
    · simp only [pN]; rw [rpB1_run]; rfl
    · simp only [pN]; rw [rpB1_run]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, by dsimp only; rw [Reg64s.get64_set64_self]; try rfl, ?_⟩
      · simp only [Spike.Lib.upd_apply]; exact hfr.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.2.1
      · simp only [Reg64s.set64]; exact hfr.2.2.2
      · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self]; exact hfr.1
  case x1 =>
    refine xchgSt_ndW (r := .rax) (b := .rcx) (k := 0) (code_field hp hend c3 rfl) hW.x1
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, hax, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 0
    have hm := hmem σ0 c0' hJp 0 (.inl rfl)
    obtain ⟨x, sa, u, v, e, tv, wv, wold, hx, hv, hh, hev, hV, hk⟩ := h2 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, tv, wv, wold, hx, hr ▸ hv, hr ▸ hh, hev,
      by rw [hax]; exact hV, .inl ⟨PN.s2, ?_, rfl, σ0, ⟨c0', hJp⟩, hk, hfr⟩⟩
    show lab ".Lwc_rodata.x13" + 32 = lab ".Lwc_rodata.x13" + 29 + Int64.ofNat 3
    rw [Int64.add_assoc]; rfl
  case s2 =>
    refine seg_ndW (by simp [rpB2]) rpB2_ok hF hR hlo hhi (code_field hp hend c4 rfl) hW.s2
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ⟨c, .refl c, .inl ⟨PN.l2, ?_, ?_, σ0, hJp, hJ, ?_⟩⟩
    · simp only [pN]; rw [rpB2_run, Int64.add_assoc]; rfl
    · simp only [pN]; rw [rpB2_run]; rfl
    · simp only [pN]; rw [rpB2_run]
      exact ⟨⟨hfr.1, hfr.2.1, hfr.2.2.1, hfr.2.2.2⟩, by rw [Reg64s.get64_set64_self]; exact hfr.1⟩
  case l2 =>
    refine holdLd_ndW (r := .rax) (b := .rcx) (k := 8) (by decide) hF (code_field hp hend c5 rfl) hW.l2
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 8
    have hm := hmem σ0 c0' hJp 8 (.inr rfl)
    obtain ⟨x, sa, u, v, e, hx, hv, hh, hk⟩ := h3 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, hx, hr ▸ hv, hh, fun r w' hrd hrep =>
      .inl ⟨PN.s3, ?_, rfl, σ0, ⟨c0', hJp⟩, hr ▸ hk r w' hrd hrep, hfr⟩⟩
    show lab ".Lwc_rodata.x13" + 40 = lab ".Lwc_rodata.x13" + 36 + Int64.ofNat 4
    rw [Int64.add_assoc]; rfl
  case s3 =>
    refine seg_ndW (by simp [rpB3]) rpB3_ok hF hR hlo hhi (code_field hp hend c6 rfl) hW.s3
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ⟨c, .refl c, .inl ⟨PN.x2, ?_, ?_, σ0, hJp, hJ, ?_⟩⟩
    · simp only [pN]; rw [rpB3_run, Int64.add_assoc]; rfl
    · simp only [pN]; rw [rpB3_run]; rfl
    · simp only [pN]; rw [rpB3_run]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, by dsimp only; rw [Reg64s.get64_set64_self]; try rfl, ?_⟩
      · simp only [Spike.Lib.upd_apply]; exact hfr.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.2.1
      · simp only [Reg64s.set64]; exact hfr.2.2.2
      · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self]; exact hfr.1
  case x2 =>
    refine xchgSt_ndW (r := .rax) (b := .rcx) (k := 8) (code_field hp hend c7 rfl) hW.x2
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, hax, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 8
    have hm := hmem σ0 c0' hJp 8 (.inr rfl)
    obtain ⟨x, sa, u, v, e, tv, wv, wold, hx, hv, hh, hev, hV, hk⟩ := h4 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, tv, wv, wold, hx, hr ▸ hv, hr ▸ hh, hev,
      by rw [hax]; exact hV, .inl ⟨PN.s4, ?_, rfl, σ0, ⟨c0', hJp⟩, hk, hfr⟩⟩
    show lab ".Lwc_rodata.x13" + 62 = lab ".Lwc_rodata.x13" + 58 + Int64.ofNat 4
    rw [Int64.add_assoc]; rfl
  case s4 =>
    refine seg_ndW (by simp [rpB4]) rpB4_ok hF hR hlo hhi (code_field hp hend c8 rfl) hW.s4
      fun σ c ⟨σ0, ⟨c0', hJp⟩, hJ, hfr⟩ => ?_
    obtain ⟨h16, h8, h0, hbp'⟩ := hfr
    obtain ⟨c', hr, hx⟩ := hedge σ0 c hJ
      (arun lab rpB4 ⟨lab ".Lwc_rodata.x13" + 62, oR, σ⟩).σ
      (by rw [rpB4_run]; simp [Reg64s.set64, h16]) (by rw [rpB4_run]; simp [Reg64s.set64])
      (by rw [rpB4_run]; simp [Reg64s.set64]) (by rw [rpB4_run]; simp [Reg64s.set64])
      (by rw [rpB4_run]; simp [Reg64s.set64, h8]) (by rw [rpB4_run]; simp [Reg64s.set64, hbp'])
    refine ⟨c', hr, .inr ⟨(), ?_, ?_, hx⟩⟩
    · show x.pc = (arun lab rpB4 ⟨lab ".Lwc_rodata.x13" + 62, oR, σ⟩).pc
      rw [rpB4_run, hra σ0 c0' hJp, h0]
    · show x.o.le (arun lab rpB4 ⟨lab ".Lwc_rodata.x13" + 62, oR, σ⟩).so = true
      rw [rpB4_run]; exact ho

end RpFn

end Spike.Lib.X64.Flow.Hello1
