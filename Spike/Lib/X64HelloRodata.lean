/-
**`hello.w`'s `wc_rodata` on x86-64**, inside `W`, in any valid layout of `helloCells`
(`Spike/Lib/X64HelloCode.lean`), from checks decided once on the cells (`decide +kernel`). It is the x86-64 twin
of `Spike/Lib/A64HelloRodata.lean`, and the label-shifted twin of hello1's x86-64 forms with the source's local
runs (`X64Hello1RodataS`, `X64Hello1RodataPostS`) at hello's labels (`.Lwc_rodata.x15`, hello1's `.x13`).
hello1's blocks (`Hello1.rdE`, `rpB0` … `rpB4`), their specifications and the frame facts (`rdJ`, `rdFr`) are
reused; only the label-carrying pieces are restated.

hello.w's x86-64 `wc_rodata` is hello1.w's, byte for byte: the source's `let s = publish b` after the second
exchange is lowered to `# fence st: no code under TSO`, which emits no instruction. **Deviation from AArch64**:
AArch64's `wc_rodata` has a `dmb ishst` there, a node `.f` at which the source takes its publication
(`FenceRun.pub` under `ms.pub`). Here there is no fence node: the post segment has hello1's nine nodes, the
second exchange lands at `J4` (the control at `let s = publish b`), and the source takes its run at a `.st` fence
(`hfen`, `FenceRun` under `ms.pub`, into `J5`) as a source-only stutter before the row of the node after the
comment (`.x15 + 62`, `SegW.pubP`). The segment is therefore a `SegWP` (`Spike/Lib/X64SegWPub.lean`), and the
last block's source invariant is `J4P J4 J4x`: at the publication (`J4`), or past it (`J4x`, the publication's
targets, `hpubx`, each running locally into `J5`, `hlocx`).

- `hello_alloc`, `rdPro`, `hello_rdPro`, `rdEIn`, `hello_rdEIn`, `rpIn`, `hello_rpIn`: the checks.
- `rN`, `rX`, `RdCtx`, `RdPreW`: the nodes up to the call (the entry block's at `J0`, the call's at `J1`), the
  exits (the allocator's return at `.x15`; its heap abort, with the return address `.full + 12` its
  `call scc_rt_abort` pushed, at `-208`), the allocator's call context, and the states inside `W`.
- `rXF`, `hello_rodata_pre_runWF`: from `wc_rodata`'s entry at a level-ending call (hello's level 0): the heap
  abort is the only exit, the allocator's return being its allocation (`Flow.seg_alloc_ofW_atNR`).
- `pN`, `RdPostW`: `.x15`'s nodes (hello1's `pNL`) and their states inside `W`.
- `J4P`: the last block's source invariant, `J4` (at the publication) or `J4x` (past it).
- `hello_rodata_post_runW`: from `.x15` to the caller's node, the source advanced by a local run before each
  exchange's load and taking the publication as a stutter at `.x15 + 62` (a `SegWP`).

(`hello_rodata_pre_runW`, AArch64's form with the allocator's return exit, is not twinned: it is dead in hello.)
-/
import Spike.Lib.X64Hello1RodataPostS
import Spike.Lib.X64WakeWcPre
import Spike.Lib.X64HelloCode
import Spike.Lib.X64AllocNR
import Spike.Lib.X64SegWPub

namespace Spike.Lib.X64.Flow.HelloRd

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.X64.Flow.Hello1 (rdE rdE_ok rdE_run rdJ AG RN RX aR oR rdFr wJ rpB0 rpB0_ok rpB0_run rpB1 rpB1_ok
  rpB1_run rpB2 rpB2_ok rpB2_run rpB3 rpB3_ok rpB3_run rpB4 rpB4_ok rpB4_run rpK1 rpK2 bAddr_rcx_rax allocW_mono PN)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

theorem hello_alloc : Alloc.allocIn SccCode.helloCells = true := by decide +kernel

/-- `wc_rodata`'s prologue: a frame of 32 below the saved `%rbp`, nothing spilled. -/
abbrev rdPro : Bool := prologueIn SccCode.helloCells "wc_rodata" ".Lwc_rodata.chk" ".Lwc_rodata.entry" 32 8
  ".Lwc_rodata.stk" 5 9 3 2 4 []

theorem hello_rdPro : rdPro = true := by decide +kernel

/-- **`wc_rodata`'s entry block in `cells`**, `.x15` right after the call. -/
def rdEIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_rodata.entry" 0 rdE && labelGapB cells ".Lwc_rodata.entry" ".Lwc_rodata.x15" 26

theorem hello_rdEIn : rdEIn SccCode.helloCells = true := by decide +kernel

/-- **`.x15` in `cells`**: its blocks and the two exchanges' loads and stores at their offsets (hello1's
`rpIn` at `.x15`; the `# fence st` comment emits nothing, so the last block follows the second store). -/
def rpIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_rodata.x15" 0 rpB0 && blockAtB cells ".Lwc_rodata.x15" 8 [(ldDir .rcx 0 .rax, 3)] &&
  blockAtB cells ".Lwc_rodata.x15" 11 rpB1 && blockAtB cells ".Lwc_rodata.x15" 29 [(stDir .rcx 0 .rax, 3)] &&
  blockAtB cells ".Lwc_rodata.x15" 32 rpB2 && blockAtB cells ".Lwc_rodata.x15" 36 [(ldDir .rcx 8 .rax, 4)] &&
  blockAtB cells ".Lwc_rodata.x15" 40 rpB3 && blockAtB cells ".Lwc_rodata.x15" 58 [(stDir .rcx 8 .rax, 4)] &&
  blockAtB cells ".Lwc_rodata.x15" 62 rpB4

theorem hello_rpIn : rpIn SccCode.helloCells = true := by decide +kernel

/-! ## `wc_rodata` up to the allocator's call -/

section Rd

variable (ms : MemSide isa) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat) (R : Region)
  (J0 J1 : AS → Ctl → Prop)

/-- **The nodes**: `.entry` (at the entry's invariant `J0`, `%rbp` at the saved `%rbp`) and the allocator's
entry with its arguments (at `J1`, the source advanced in the block), the return address `.x15` pushed. -/
def rN : RN → ND
  | .e => ⟨lab ".Lwc_rodata.entry", oR, wJ R (rdJ J0)⟩
  | .call => ⟨lab "scc_rt_alloc", ⟨-48, []⟩, fun σ c => rdJ J1 σ c ∧ σ.regs.get64 .rbp = R.addr (-8) ∧
      σ.regs.rdi.toBitVec = 257#64 ∧ σ.regs.rsi.toBitVec = 2#64 ∧ σ.regs.rdx.toBitVec = 3#64 ∧
      σ.slot (-48) = (lab ".Lwc_rodata.x15").toBitVec⟩

/-- **The exits**: the allocator's return at `.x15` (its return's facts, the frame record and `%rbp` kept),
and its heap abort (the return address `.Lscc_rt_alloc.full + 12` its `call scc_rt_abort` pushed, at `-208`). -/
def rX : RX → ND
  | .x13 => ⟨lab ".Lwc_rodata.x15", ⟨-40, []⟩, fun σ c => ∃ q : AG ms lab, rdJ J1 σ q.1.c0 ∧
      σ.regs.get64 .rbp = R.addr (-8) ∧ (Alloc.E lab ms q.1 lbl .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-208, []⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧
      σ.slot (-208) = (lab ".Lscc_rt_alloc.full" + 12).toBitVec ∧
      ∃ q : AG ms lab, Jfull ms q.1 c ∧ ∃ σe, J1 σe q.1.c0⟩

/-- **The exits at a level-ending call**: `rX`'s, with no state at `.x15` (the allocator's return is its
allocation, landing in `ms.xa`: `Alloc.ENR`). -/
def rXF : RX → ND
  | .x13 => ⟨lab ".Lwc_rodata.x15", ⟨-40, []⟩, fun _ _ => False⟩
  | .abort => rX ms lab lbl R J1 .abort

end Rd

/-- **The allocator's call context in `wc_rodata`'s region `R`** at the memory `m` (`Hello1.RdCtx` at hello's
call node). -/
def RdCtx (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J0 J1 : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN lab R J0 J1 .call).J σC c ∧ (Alloc.N lab ms q .e).J (enter (-48) σC) c ∧
    CKept R (-48) (-160) 8 mC m

/-- **`wc_rodata`'s states up to the allocator's return inside `W`**, none moved by `K`: the prologue's, the
entry block's, and the allocator's in its region (`Hello1.RdPreW` at hello's labels). -/
structure RdPreW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J0 J1 : AS → Ctl → Prop) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_rodata") 32 8
    ".Lwc_rodata.stk" 5 9 3 2 4 [] J0
  e : BlkW W K exe endPc R F (rN (_root_.Executable.labels exe).label R J0 J1 .e) rdE
  alloc : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label →
    q.ra = ((_root_.Executable.labels exe).label ".Lwc_rodata.x15").toBitVec →
    AllocW ms q W K exe endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧ RdCtx ms (_root_.Executable.labels exe).label R J0 J1 q m)

/-- `wc_rodata` up to the allocator's return is inside the trivial predicate, with no outside moves. -/
theorem RdPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 J1 : AS → Ctl → Prop} :
    RdPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 J1 :=
  ⟨XProW.triv, BlkW.triv, fun q _ _ => Alloc.AllocW.triv ms q⟩

section RdFnF

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` up to the allocator's call is one segment inside `W` whose only exit is the heap abort**, in
any valid layout of `helloCells`, at a level-ending allocation (hello's level 0). It runs from the entry
(invariant `J0`, `%rsp` at the region's offset 0, the limit word's facts for its frame of 32 below the saved
`%rbp`, `hlim`) to the allocator's heap abort.
- The entry block takes a local run from each of `J0`'s controls to one of `J1` at the same state (`hloc`).
- At `J1` the source is at a buffer allocation the allocator's premises hold for: header `257`, two elements
  of three units (`hq`).
- The counter and the headers the allocator may store are unmapped in private memory under `F` (`hmem`).
- An allocation of a fresh label lands in `ms.xa` (`hxa`, for every frame condition the call hands the
  allocator); the allocator runs as `Flow.seg_alloc_ofW_atNR`, so no state reaches `.x15`.
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_rodata_pre_runWF {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop} (hW : RdPreW W K exe endPc R F ms J0 J1)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec))
    (hloc : ∀ σ c, J0 σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        (rN (_root_.Executable.labels exe).label R J0 J1 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J0⟩)
      (At exe endPc R F (rX ms (_root_.Executable.labels exe).label lbl R J1 .abort)) := by
  have hin := hello_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e26 : lab ".Lwc_rodata.x15" = lab ".Lwc_rodata.entry" + Int64.ofNat 26 := label_labelGapB hp hgap
  refine (SegW.seq (prologue_seg_ofW hp hend hello_rdPro (nb := ⟨lab ".Lwc_rodata.entry", oR, rdJ J0⟩)
    (by decide) hF hR
    (by show R.lo ≤ -8 - (32 : Int64).toInt; rw [show (32 : Int64).toInt = 32 from rfl]; omega) (by omega)
    (by decide) rfl (by show SO.le oR (oF 32) = true; decide) hW.pro ?_)
    ((fn_segW (N := rN lab R J0 J1) (E := rXF ms lab lbl R J1) (fun i => ?_) RN.e).mono_pre
      fun _ _ h => Hello1.At.reg_addr (r := .rbp) (k := -8) rfl h)).mono_post ?_
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  · cases i
    case e =>
      refine seg_ndW (by simp [rdE]) rdE_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.e
        fun σ c hJ => ?_
      obtain ⟨⟨σe, hJe, h0', h8⟩, hb⟩ := hJ
      obtain ⟨c', hr, hJ1⟩ := hloc σe c hJe
      refine ⟨c', hr, .inl ⟨RN.call, ?_, ?_, ?_⟩⟩
      · simp only [rN]; rw [rdE_run]
      · simp only [rN]; rw [rdE_run]; rfl
      · simp only [rN]
        rw [rdE_run]
        refine ⟨⟨σe, hJ1, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
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
      refine WakeWc.call_nd_FWKL (KC := False) (e0 := 0) (lo' := -160) (hi' := 8) (M := fun _ => True)
        (Ne := fun g : AG ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AG ms lab => Alloc.ENR lab ms g.1 lbl)
        hR hF (by show R.lo ≤ -48 - 0 + -160; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
        (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
        (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
        (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
          subst hR'e
          obtain ⟨σC, c, ⟨-, -, -, -, -, h48⟩, ⟨-, -, hra, -⟩⟩ := hg
          have hr : g.1.ra = (lab ".Lwc_rodata.x15").toBitVec := by
            rw [← hra, ← h48]; rfl
          exact (seg_alloc_ofW_atNR hp hend hello_alloc hF' hR' hlo' hhi' g.2
            (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
            (hxa g F' hFF hkeep)
            (allocW_mono (hW.alloc g.1 g.2 hr) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩) .e).mono_post
            fun _ _ h => ⟨.abort, h, trivial⟩)
        (fun _ => rfl) ?_ ?_
      · rintro σC c ⟨⟨σe, hJe, -, -⟩, -, h0, h1, h2, -⟩
        obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
        exact ⟨⟨{ q with fp := σC.regs.rbp.toBitVec, ra := σC.slot (-48 - 0 + 0) }, { hok with }⟩, rfl,
          hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
      · rintro g y σC c σx c' σR ⟨⟨σe, hJe, -, -⟩, -, -, -, -, -⟩ ⟨hc, -, -, -⟩ hx hreg - - - hin
        cases y
        · exact hx.elim
        · obtain ⟨h2, hfull, hs⟩ := hx
          refine .inr ⟨RX.abort, rfl, by show SO.le ⟨-208, []⟩ ⟨-48 - 0 + -160, []⟩ = true; decide, ?_, ?_,
            g, hfull, σe, hc ▸ hJe⟩
          · show σR.regs.rdi.toBitVec = 2#64
            rw [hreg]; exact h2
          · show σR.slot (-208) = _
            rw [hin (-208) (by simp only [Region.Off, Region.callee, rN]; omega)]
            exact hs
  · rintro s c ⟨y, hy⟩
    cases y
    · obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hy
      exact hJ.elim
    · exact hy

end RdFnF

/-! ## `wc_rodata` from the allocator's return -/

/-- **`.x15`'s nodes, the source advanced before each load** (hello1's `pNL` at `.x15`), from the invariant
`Jp` at `.x15`, the controls `Jp'` after the first block's run (at the first load) and `J2'` after the third's
(at the second load), and the source's invariants `J1` … `J4` after each exchange's load and store (of `.x15`'s
state and the control). There is no fence node: the source's `publish b` emits no code (see the module
docstring), so `J4` is the source invariant at the last block (`hello_rodata_post_runW` takes it at `J4P J4 J4x`). -/
def pN (lab : Label → Int64) (Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop) : PN → ND
  | .s0 => ⟨lab ".Lwc_rodata.x15", oR, Jp⟩
  | .l1 => ⟨lab ".Lwc_rodata.x15" + 8, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      Jp' σ0 c ∧ rdFr σ0 σ ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .s1 => ⟨lab ".Lwc_rodata.x15" + 11, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧ J1 σ0 c ∧ rdFr σ0 σ⟩
  | .x1 => ⟨lab ".Lwc_rodata.x15" + 29, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J1 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.get64 .rax = rpK1 ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .s2 => ⟨lab ".Lwc_rodata.x15" + 32, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧ J2 σ0 c ∧ rdFr σ0 σ⟩
  | .l2 => ⟨lab ".Lwc_rodata.x15" + 36, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J2' σ0 c ∧ rdFr σ0 σ ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .s3 => ⟨lab ".Lwc_rodata.x15" + 40, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧ J3 σ0 c ∧ rdFr σ0 σ⟩
  | .x2 => ⟨lab ".Lwc_rodata.x15" + 58, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J3 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.get64 .rax = rpK2 ∧ σ.regs.get64 .rcx = σ0.regs.get64 .rax⟩
  | .s4 => ⟨lab ".Lwc_rodata.x15" + 62, oR, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧ J4 σ0 c ∧ rdFr σ0 σ⟩

/-- **`wc_rodata`'s states from the allocator's return inside `W`**, none moved by `K`: one obligation per
node. -/
structure RdPostW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop) : Prop where
  s0 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s0) rpB0
  l1 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .l1)
  s1 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s1) rpB1
  x1 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .x1)
  s2 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s2) rpB2
  l2 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .l2)
  s3 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s3) rpB3
  x2 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .x2)
  s4 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s4) rpB4

/-- `wc_rodata` from the allocator's return is inside the trivial predicate, with no outside moves. -/
theorem RdPostW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop} :
    RdPostW (fun _ _ => True) (fun _ _ => False) exe endPc R F Jp Jp' J1 J2 J2' J3 J4 :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv⟩

/-- A state with its pc replaced by its own pc. -/
private theorem self_of_pc {s : State} {pc : Int64} (h : s.st.2 = pc) : ({ s with st := (s.st.1, pc) } : State) = s := by
  obtain ⟨⟩ := s; subst h; rfl

/-- **The last block's source invariant**: the control at the publication (`J4`, after the second exchange)
or one past it (`J4x`). `hello_rodata_post_runW` takes `pN`'s `J4` at `J4P J4 J4x`: the source publishes at
`.x15 + 62` before the last block's row (a stutter, `SegW.pubP`, into `J4x`), or has published already. `J4x`
is a parameter, not "some control running locally into `J5`": a control is pinned down at its row (the states
inside `W`, `RdPostW.s4`), and a local run cannot be inverted backwards. -/
def J4P (J4 J4x : AS → Ctl → Prop) (σ0 : AS) (c : Ctl) : Prop :=
  J4 σ0 c ∨ J4x σ0 c

section RpFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` from the allocator's return is one segment inside `W`** in any valid layout of `helloCells`:
from `.x15` (invariant `Jp` of the state `σ0` there, `%rsp` at `-40`, `%rbp` at the saved `%rbp`, `hbp`) to the
caller's node `x` (pc the saved return address, `hra`; offsets at most `⟨8, []⟩`). This is
`Hello1.hello1_rodata_post_runW` at hello's labels.
- The buffer's two words at `%rax` and `%rax + 8` are unmapped in private memory under `F` (`hmem`).
- The source runs locally in the first and third blocks (`hr0`, `hr2`), then the two exchanges (`h1` … `h4`,
  as in hello1).
- After the second exchange (`J4`, at `let s = publish b`) the source's run at a `.st` fence (`hfen`,
  `FenceRun` under `ms.pub`) lands in `J5`: a local run, or the publication and then a local run. There is no
  fence instruction, so the publication is taken as a source stutter before the last block's row (`SegW.pubP`,
  off a system call: `rpB4` starts with a `movq`); the segment is a `SegWP`. The publication's targets are in
  `J4x` (`hpubx`), each running locally into `J5` (`hlocx`).
- At the return, `x`'s invariant holds after a local run of every state with `%rax` the base, `%rdx = 0`,
  `%rcx = 2`, `%rsi = 13`, `%rbp` the saved `%rbp` and `%rsp` past the return address, from `J5` (`hedge`).
  `hedge` also knows that `.x15`'s state `σ0` is `Jp`'s: `J5` constrains the source alone, and the restored `%rbp`
  is `σ0.slot (-8)`, which only `Jp` (the frame at `.x15`) pins down.
- Its states lie in `W`, none moved by `K` (`hW`, at `J4P J4 J4x` for the last block). -/
theorem hello_rodata_post_runW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {Jp Jp' J1 J2 J2' J3 J4 J4x J5 : AS → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hW : RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 (J4P J4 J4x))
    (hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = R.addr (-8))
    (hra : ∀ σ0 c, Jp σ0 c → x.pc = Int64.ofBitVec (σ0.slot 0))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, F m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none)
    (hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c')
    (h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c')
    (h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hfen : ∀ σ0 c, J4 σ0 c → ∃ c', FenceRun p ms.pub .st c c' ∧ J5 σ0 c')
    (hpubx : ∀ σ0 c c₁, J4 σ0 c → PubStep .st c c₁ → J4x σ0 c₁)
    (hlocx : ∀ σ0 c, J4x σ0 c → ∃ c', LocalRun p c c' ∧ J5 σ0 c')
    (hedge : ∀ σ0 c, (∃ c0, Jp σ0 c0) → J5 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    Spike.Lib.X64SegWPub.SegWP W K p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x15", ⟨-40, []⟩, Jp⟩)
      (At exe endPc R F x) := by
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  -- the last block from the controls past the publication, or at it with a local fence run
  let J4L : AS → Ctl → Prop := fun σ0 c => J4 σ0 c ∧ ∃ c', LocalRun p c c' ∧ J5 σ0 c'
  have hB : SegW W K p lbl ms (At exe endPc R F (pN lab Jp Jp' J1 J2 J2' J3 (J4P J4L J4x) .s4))
      (At exe endPc R F x) := by
    refine (seg_ndW (n := pN lab Jp Jp' J1 J2 J2' J3 (J4P J4L J4x) .s4) (N := fun _ : Unit => x)
      (E := fun _ : Unit => x) (by simp [rpB4]) rpB4_ok hF hR hlo hhi
      (code_field hp hend c8 rfl)
      (fun s σ c he hn hd hpc hA hD ⟨σ0, hJp, hJ, hfr⟩ =>
        hW.s4 s σ c he hn hd hpc hA hD ⟨σ0, hJp, hJ.imp And.left id, hfr⟩)
      fun σ c ⟨σ0, ⟨c0', hJp⟩, hJ, hfr⟩ => ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨_, h⟩ => h
    obtain ⟨c₁, hr₁, hJ5⟩ := hJ.elim And.right (hlocx σ0 c)
    obtain ⟨h16, h8, h0, hbp'⟩ := hfr
    obtain ⟨c', hr, hx⟩ := hedge σ0 c₁ ⟨c0', hJp⟩ hJ5
      (arun lab rpB4 ⟨lab ".Lwc_rodata.x15" + 62, oR, σ⟩).σ
      (by rw [rpB4_run]; simp [Reg64s.set64, h16]) (by rw [rpB4_run]; simp [Reg64s.set64])
      (by rw [rpB4_run]; simp [Reg64s.set64]) (by rw [rpB4_run]; simp [Reg64s.set64])
      (by rw [rpB4_run]; simp [Reg64s.set64, h8]) (by rw [rpB4_run]; simp [Reg64s.set64, hbp'])
    refine ⟨c', hr₁.trans hr, .inr ⟨(), ?_, ?_, hx⟩⟩
    · show x.pc = (arun lab rpB4 ⟨lab ".Lwc_rodata.x15" + 62, oR, σ⟩).pc
      rw [rpB4_run, hra σ0 c0' hJp, h0]
    · show x.o.le (arun lab rpB4 ⟨lab ".Lwc_rodata.x15" + 62, oR, σ⟩).so = true
      rw [rpB4_run]; exact ho
  -- at the publication: a stutter into `hB`'s controls, or already past it
  have hC := SegW.pubP (P₀ := At exe endPc R F (pN lab Jp Jp' J1 J2 J2' J3 J4 .s4)) hB fun s c hs => by
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σ0, hJp, hJ4, hfr⟩ := hs
    have e0 : ∀ q : Int64, q + Int64.ofNat (cellOff rpB4 0) = q := fun q => by simp [cellOff]
    have hs0 := self_of_pc (s := s) (pc := (pN lab Jp Jp' J1 J2 J2' J3 (J4P J4 J4x) .s4).pc) hpc
    have hw := hW.s4 s σ c he hn hdc hpc hA hD ⟨σ0, hJp, .inl hJ4, hfr⟩ 0 (by simp [rpB4]) s.st.1
      (by simp only [List.take_zero, arun, List.foldl_nil]; exact hA) (DFrame.refl _ _)
    rw [e0, hs0] at hw
    refine ⟨hw.1, hw.2, ?_⟩
    obtain ⟨c', hfr', hJ5⟩ := hfen σ0 c hJ4
    cases hfr' with
    | loc hr => exact .inl ⟨he, hn, hdc, hpc, σ, hA, hD, σ0, hJp, .inl ⟨hJ4, c', hr, hJ5⟩, hfr⟩
    | pub hP hps _ =>
      refine .inr ⟨?_, hP, _, hps, he, hn, hdc, hpc, σ, hA, hD, σ0, hJp, .inr (hpubx σ0 c _ hJ4 hps), hfr⟩
      have hcell := code_field hp hend c8 rfl s he hn 0 (rpB4[0]'(by simp [rpB4])).1 (rpB4[0]'(by simp [rpB4])).2
        (List.getElem?_eq_getElem (by simp [rpB4]))
      have hns := Scc.Sem.X64.atSyscall_false_of_cellAt hcell (by intro w w' h; first | cases h | simp [rpB4] at h)
      have hs1 := self_of_pc (s := s) (pc := lab ".Lwc_rodata.x15" + Int64.ofNat 62) (hpc.trans rfl)
      try simp only [e0] at hns
      rw [hs1] at hns
      exact hns
  refine ((Spike.Lib.SegW.toP ((fn_segW (N := pN lab Jp Jp' J1 J2 J2' J3 (fun _ _ => False))
    (E := fun _ : Unit => pN lab Jp Jp' J1 J2 J2' J3 J4 .s4) (fun i => ?_) PN.s0).mono_pre
      fun _ _ h => Hello1.At.rbp_addr h hbp)).seq
    (Spike.Lib.X64SegWPub.SegWP.mono_pre hC fun _ _ ⟨_, h⟩ => .inl h))
  cases i
  case s0 =>
    refine seg_ndW (by simp [rpB0]) rpB0_ok hF hR hlo hhi (code_field hp hend c0 (ofNat_zero' _)) hW.s0
      fun σ c hJ => ?_
    obtain ⟨c', hr, hJ'⟩ := hr0 σ c hJ
    refine ⟨c', hr, .inl ⟨PN.l1, ?_, ?_, σ, ⟨c, hJ⟩, hJ', ?_⟩⟩
    · simp only [pN]; rw [rpB0_run]
    · simp only [pN]; rw [rpB0_run]; rfl
    · simp only [pN]; rw [rpB0_run]
      refine ⟨⟨?_, ?_, ?_, rfl⟩, by dsimp only; rw [Reg64s.get64_set64_self]; try rfl⟩ <;> simp [Spike.Lib.upd_apply]
  case l1 =>
    refine holdLd_ndW (r := .rax) (b := .rcx) (k := 0) (by decide) hF (code_field hp hend c1 rfl) hW.l1
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, hcx⟩ => ?_
    have hr := bAddr_rcx_rax hcx 0
    have hm := hmem σ0 c0' hJp 0 (.inl rfl)
    obtain ⟨x, sa, u, v, e, hx, hv, hh, hk⟩ := h1 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, hx, hr ▸ hv, hh, fun r w' hrd hrep =>
      .inl ⟨PN.s1, ?_, rfl, σ0, ⟨c0', hJp⟩, hr ▸ hk r w' hrd hrep, hfr⟩⟩
    show lab ".Lwc_rodata.x15" + 11 = lab ".Lwc_rodata.x15" + 8 + Int64.ofNat 3
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
    show lab ".Lwc_rodata.x15" + 32 = lab ".Lwc_rodata.x15" + 29 + Int64.ofNat 3
    rw [Int64.add_assoc]; rfl
  case s2 =>
    refine seg_ndW (by simp [rpB2]) rpB2_ok hF hR hlo hhi (code_field hp hend c4 rfl) hW.s2
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ?_
    obtain ⟨c', hr, hJ'⟩ := hr2 σ0 c hJ
    refine ⟨c', hr, .inl ⟨PN.l2, ?_, ?_, σ0, hJp, hJ', ?_⟩⟩
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
    show lab ".Lwc_rodata.x15" + 40 = lab ".Lwc_rodata.x15" + 36 + Int64.ofNat 4
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
      by rw [hax]; exact hV, .inr ⟨(), ?_, rfl, σ0, ⟨c0', hJp⟩, hk, hfr⟩⟩
    show lab ".Lwc_rodata.x15" + 62 = lab ".Lwc_rodata.x15" + 58 + Int64.ofNat 4
    rw [Int64.add_assoc]; rfl
  case s4 =>
    exact SegW.empty fun _ _ ⟨_, _, _, _, _, _, _, _, _, h, _⟩ => h

end RpFn

end Spike.Lib.X64.Flow.HelloRd

/-- info: 'Spike.Lib.X64.Flow.HelloRd.hello_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloRd.hello_alloc

/-- info: 'Spike.Lib.X64.Flow.HelloRd.hello_rpIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloRd.hello_rpIn

/--
info: 'Spike.Lib.X64.Flow.HelloRd.hello_rodata_pre_runWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloRd.hello_rodata_pre_runWF

/--
info: 'Spike.Lib.X64.Flow.HelloRd.hello_rodata_post_runW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloRd.hello_rodata_post_runW
