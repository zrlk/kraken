/-
**`wc_rodata` on x64 from its call to its return**: the prologue, the
allocation of the two-cell buffer (or the heap abort when the arena is
full), the two lane exchanges and the epilogue, with the `%fs` base kept
across every segment, ending at the caller's return address in the shape
of a setup call's post state. The x64 twin of
`Spike/Lib/A64Hello1RodataSetup.lean`.

- `callOK_tp`, `callOK_untp`, `limOk_tp`, `proW_tp`, `allocW_tp`,
  `rdPreW_tp`: the memory side's facts moved to a thread pointer
  (`tpXa`);
- `rdQ`, `rdQ_facts`: `wc_rodata`'s allocation call and what its
  obligations fix;
- `bAddr_rax_0`, `bAddr_rax_8`: the two lane addresses;
- `sJ0`, `sJ1`, `RdF`, `sJp`, `sJp'`, `sJh1`, `sJ2`, `sJ2'`, `sJh2`,
  `sJ4`: the source controls at each node;
- `rdPostS`, `sX`, `sXf`: the return node and its post state (the buffer
  at `%rax`, `%rdx = 0`, `%rcx = 2`, `%rsi = 13`, the caller's `%rbp`,
  `%rsp` past the return address and the `%fs` base);
- `x13_sJp`: the frame at the allocation's landing;
- `hello1_rodata_setupW`: from the setup entry `uN0 .. "wc_rodata" 32 g`
  to `sXf`, given the region reaches `240` bytes below the entry `%rsp`
  (the frame, the allocator and the heap abort).
-/
import Spike.Lib.X64Hello1RodataTP
import Spike.Lib.X64AbortHeapW
import Spike.Lib.Hello1RodataSrc
import Spike.Lib.Rt.X64Main

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk WcG limA)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull mOf)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdCA rdC1 rdC2 rdC3 rdC4 rdRet eW0 τ8 rdK1 rdK2 rdC0_run rdCN_newBuf
  rdCA_store rdC2_store rdC1_next rdC3_next rdC4_run)

set_option linter.unusedSimpArgs false

/-! ## The memory side with the allocation's landing at a thread pointer -/

section Tp

variable {ms : MemSide isa} {t : UInt64}

theorem callOK_tp {lab : Label → Int64} {q : Call} (h : q.OK ms lab) : q.OK (tpXa ms t) lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

theorem callOK_untp {lab : Label → Int64} {q : Call} (h : q.OK (tpXa ms t) lab) : q.OK ms lab :=
  ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt, h.mp,
    h.grow, h.hdr⟩

theorem limOk_tp {F : MachineData → Prop} {a Z : BitVec 64} (h : LimOk ms F a Z) : LimOk (tpXa ms t) F a Z :=
  ⟨h.rt, h.mp, h.unmapped, h.room⟩

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

theorem proW_tp {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    {J : AS → Ctl → Prop} (h : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J) :
    XProW W K exe endPc R F (tpXa ms t) pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨h.w0, h.w1, h.w2, h.w3, h.w4⟩

theorem allocW_tp {q : Call} (h : AllocW ms q W K exe endPc R F) : AllocW (tpXa ms t) q W K exe endPc R F :=
  ⟨h.e, h.entry, h.j1, h.cnt, h.c1, h.rmw, h.c2, h.j2, h.slow, h.j3, h.full, h.ok, h.f1, h.o1, h.f2, h.o2, h.s2,
    h.o3, h.f3, h.o4, h.f4, h.o5, h.f5, h.o6, h.f6, h.o7, h.f7, h.o8, h.hdr, h.o9, h.ret⟩

theorem rdPreW_tp {J0 Jc : AS → Ctl → Prop} (h : RdPreW W K exe endPc R F ms J0 Jc) :
    RdPreW W K exe endPc R F (tpXa ms t) J0 Jc :=
  ⟨proW_tp h.pro, h.e, fun q hok hq => allocW_tp (h.alloc q (callOK_untp hok) hq)⟩

end Tp

/-! ## The source's allocation -/

/-- **`rodata`'s allocation as the allocator's call**: at `rdCN`, `b` bound
to a buffer of `m = 2` lane words, header `257`. -/
def rdQ : Call :=
  ⟨rdCN, "b", .var "m", τ8, eW0, .intS (.lit 2), [TermRun.cst (.num 2)], 2, 257#64, 0#64, 0#64⟩

/-- **A call at `rdCN` is `rodata`'s allocation**: its binder, element
type, continuation and count. -/
theorem rdQ_facts {ms : MemSide isa} {lab : Label → Int64} {q : Call} (h : q.OK ms lab)
    (hc : q.c0 = rdCN) : q.x = "b" ∧ q.τ = τ8 ∧ q.e = eW0 ∧ q.n = 2 := by
  have ht := h.term
  have hv := h.ev
  have hn := h.num
  rw [hc] at ht hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := rdCN_newBuf
  rw [h1] at ht
  simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
  obtain ⟨hx, ⟨ha, hτ⟩, he⟩ := ht
  rw [← ha, h2] at hv
  simp only [Option.some.injEq, Prod.mk.injEq] at hv
  rw [← hv.2, h3] at hn
  simp only [Option.some.injEq] at hn
  exact ⟨hx.symm, hτ.symm, he.symm, hn.symm⟩

/-! ## Addresses off the buffer's base -/

theorem bAddr_rax_0 (r : Reg64s) : bAddr r .rax 0 = r.rax.toBitVec := by
  simp [bAddr, Reg64s.get64]

theorem bAddr_rax_8 (r : Reg64s) : bAddr r .rax 8 = r.rax.toBitVec + 8#64 := by
  simp [bAddr, Reg64s.get64]

/-! ## `wc_rodata`'s invariants -/

section Inv

variable (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isa)
  (F0 : MachineData → Prop) (g : WcG) (R : Region)

/-- **The entry's invariant**: `scc_rt_main`'s call of the setup block
(`uN0`, a frame of 32 checked). -/
abbrev sJ0 : AS → Ctl → Prop := (Spike.Lib.X64.Rt.uN0 lab ms F0 "wc_rodata" 32 g).J

/-- At the allocation: an entry state, the source at `rdCN`. -/
def sJ1 (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop := (∃ c0, J0 σ c0) ∧ c = rdCN

/-- **`.x13`'s facts** for label `l`: `%rax` its base `A`, in the arena's
cells, the frame record the caller's and `%rbp` at the saved `%rbp`. -/
def RdF (σ0 : AS) (l : WeakMem.AllocLabel) : Prop :=
  ∃ A old : Nat, lbl l = some A ∧ σ0.regs.rax.toNat = A ∧ A = ms.heap + 16 * old + ms.off 2 τ8 ∧
    old + ms.units 2 τ8 ≤ ms.cells ∧ σ0.slot (-8) = g.fp ∧ σ0.slot 0 = g.ra ∧ σ0.regs.get64 .rbp = R.addr (-8)

/-- At `.x13`: the source past the allocation. -/
def sJp (σ0 : AS) (c : Ctl) : Prop := ∃ l ini, RdF lbl ms g R σ0 l ∧ c = rdCA l ini

/-- Before the first exchange's load. -/
def sJp' (σ0 : AS) (c : Ctl) : Prop := ∃ l ini, RdF lbl ms g R σ0 l ∧ c = rdC1 l ini

/-- The first word held. -/
def sJh1 (σ0 : AS) (c : Ctl) : Prop := ∃ l ini w, RdF lbl ms g R σ0 l ∧
  c = { rdC1 l ini with hold := some ((bAddr σ0.regs .rax 0).toNat, w) }

/-- After the first exchange. -/
def sJ2 (σ0 : AS) (c : Ctl) : Prop := ∃ l ini wo0, RdF lbl ms g R σ0 l ∧ c = rdC2 l ini wo0

/-- Before the second exchange's load. -/
def sJ2' (σ0 : AS) (c : Ctl) : Prop := ∃ l ini wo0, RdF lbl ms g R σ0 l ∧ c = rdC3 l ini wo0

/-- The second word held. -/
def sJh2 (σ0 : AS) (c : Ctl) : Prop := ∃ l ini wo0 w, RdF lbl ms g R σ0 l ∧
  c = { rdC3 l ini wo0 with hold := some ((bAddr σ0.regs .rax 8).toNat, w) }

/-- After the second exchange. -/
def sJ4 (σ0 : AS) (c : Ctl) : Prop := ∃ l ini wo0 wo1, RdF lbl ms g R σ0 l ∧ c = rdC4 l ini wo0 wo1

/-- **The setup block's post** (`PostS` of `scc_rt_main`'s interface): the
source at `ret sl` for a buffer at label `l`, base `A` in the arena's cells,
in `%rax`, and `%rdx`, `%rcx`, `%rsi` the slice's other words as the code
leaves them. -/
def rdPostS (c : Ctl) (r : Reg64s) : Prop :=
  ∃ (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : TermRun.Word) (A old : Nat), c = rdRet l ini wo0 wo1 ∧
    lbl l = some A ∧ r.rax.toNat = A ∧ A = ms.heap + 16 * old + ms.off 2 τ8 ∧ old + ms.units 2 τ8 ≤ ms.cells ∧
    r.rdx.toBitVec = 0#64 ∧ r.rcx.toBitVec = 2#64 ∧ r.rsi.toBitVec = 13#64

/-- The return, `%rbp` restored (`%rsp` past the return address from the
offsets). -/
def sX : ND := ⟨Int64.ofBitVec g.ra, ⟨8, []⟩, fun σ c => rdPostS lbl ms c σ.regs ∧ σ.regs.rbp.toBitVec = g.fp⟩

/-- **The return as `scc_rt_main`'s interface has it** (as `uNx`): with
`%rsp` past the return address and the `%fs` base as at the call. -/
def sXf : ND := ⟨Int64.ofBitVec g.ra, ⟨8, []⟩, fun σ c =>
  rdPostS lbl ms c σ.regs ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.regs.rsp.toBitVec = g.sp + 8#64 ∧
    σ.regs.fsBase = g.tp⟩

end Inv

/-! ## The setup block as one segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **The allocator's return at `.x13` is `sJp`'s**: the label already
placed, its base in `%rax`, the source past the allocation. -/
theorem x13_sJp {lab : Label → Int64} {F0 : MachineData → Prop} {g : WcG} {t : UInt64} {σ : AS} {c : Ctl}
    (h : (rX (tpXa ms t) lab lbl R (sJ1 (sJ0 lab ms F0 g)) .x13).J σ c) :
    sJp lbl ms g R σ c := by
  obtain ⟨q, ⟨σe, ⟨⟨c0, ⟨⟨-, hfp, hra, -, -⟩, -⟩⟩, hc⟩, h0, h8⟩, hbp, l, ini, old, hv, hcl, hx0, hold, -⟩ := h
  obtain ⟨hx, hτ, he, hn⟩ := rdQ_facts (callOK_untp q.2) hc
  obtain ⟨-, x, hw, hxv⟩ := hv
  simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hw
  obtain ⟨A, hl, rfl⟩ := hw
  have hx0' : σ.regs.rax.toNat = ms.heap + 16 * old + ms.off 2 τ8 := by rw [← hn, ← hτ]; exact hx0
  have hold' : old + ms.units 2 τ8 ≤ ms.cells := by rw [← hn, ← hτ]; exact hold
  refine ⟨l, ini, ⟨A, old, hl, by omega, by omega, hold', h8.trans hfp, h0.trans hra, hbp⟩, ?_⟩
  rw [hc, hx, hτ, he, hn] at hcl
  exact hcl

/-- `R.addr 8` is `8` past `R.addr 0`. -/
theorem addr8 (R : Region) : R.addr 8 = R.addr 0 + 8#64 := by
  simp only [Region.addr]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide, BitVec.add_zero]

/-- **`wc_rodata` as `scc_rt_main`'s setup block is one segment inside
`W`** in any valid layout of `hello1Cells`, in a region of depth 240 (its
frame of 40, the allocator's 168 and the heap abort's 32 below that) with
the return address's cell above: from the call's entry (`uN0`, the source
at `rodata`'s body, `hc0`) to the return with `rdPostS`, `%rbp`, `%rsp`
and the `%fs` base as at the call (`sXf`). The allocation is `rdQ`, whose
premises hold (`hQ`, `hu`); the counter, the headers (`hmem`) and the
buffer's words (`hbuf`) are unmapped in private memory under `F`. An
allocation of a fresh label lands in `ms.xa` at the call's `%fs` base
(`hxa`). The heap abort's path is given per caller's state and source
control (`hstub`). The states lie in `W`, none moved by `K` (`hWpre`,
`hWpost`). -/
theorem hello1_rodata_setupW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        (rNL (_root_.Executable.labels exe).label R (sJ0 (_root_.Executable.labels exe).label ms F0 g)
          (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 g)) .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → TP g.tp s → ms.xa l b w s c)
    (hWpre : RdPreW W K exe endPc R F ms (sJ0 (_root_.Executable.labels exe).label ms F0 g)
      (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 g)))
    (hWpost : RdPostLW W K exe endPc R F (sJp lbl ms g R) (sJp' lbl ms g R) (sJh1 lbl ms g R) (sJ2 lbl ms g R)
      (sJ2' lbl ms g R) (sJh2 lbl ms g R) (sJ4 lbl ms g R))
    (hstub : ∀ m0 σC c0, σC.regs.rdi.toBitVec = 2#64 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-208 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-208 - 8) (-24) 16 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label ms F0 "wc_rodata" 32 g))
      (At exe endPc R F (sXf lbl ms g)) := by
  let lab := (_root_.Executable.labels exe).label
  let J0 := sJ0 lab ms F0 g
  let J1 := sJ1 J0
  let ms' := tpXa ms g.tp
  -- the bounds of the buffer's words
  have hA8 : ∀ σ0 l, RdF lbl ms g R σ0 l → (σ0.regs.rax.toBitVec + 8#64).toNat = σ0.regs.rax.toNat + 8 := by
    rintro σ0 l ⟨A, old, -, hx0, hA, hold, -, -, -⟩
    have hoff : ms.off 2 τ8 = 8 := by
      have h := hQ.off
      simp only [rdQ] at h
      rw [h]; decide
    have hcells := hQ.cells
    have hroom := hQ.room
    rw [BitVec.toNat_add, show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0]
    simp only [BitVec.toNat_ofNat]
    omega
  -- the first segment: up to the allocator's return
  have hpre : SegW (NoSetFsW W K) K p lbl ms' (At exe endPc R F ⟨lab "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (rX ms' lab lbl R J1 y) s c) :=
    hello1_rodata_pre_runW hp hend hF hR (by omega) hhi (rdPreW_tp (RdPreW.noSetFs hp hend hWpre))
      (fun σ c ⟨⟨_, _, _, hsp, htp⟩, hl⟩ => by
        rw [htp, hsp]; exact limOk_tp (hl.mono hFF))
      (fun σ c hJ => ⟨rdCN, by rw [hJ.1.1, hc0]; exact rdC0_run, ⟨c, hJ⟩, rfl⟩)
      (by
        rintro σ c ⟨-, rfl⟩
        refine ⟨rdQ, callOK_tp hQ, rfl, rfl, rfl, ?_⟩
        show BitVec.ofNat 64 (ms.units 2 τ8) = 3#64
        rw [hu])
      (fun q hq a ha m hm => hmem q (callOK_untp hq) a ha m hm)
      (fun q F' h1 h2 l b w s c hl hAt htp => hxa ⟨q.1, callOK_untp q.2⟩ F' h1 h2 l b w s c hl hAt htp)
  -- the second segment: from `.x13` to the return
  have hpost : SegW (NoSetFsW W K) K p lbl ms'
      (At exe endPc R F ⟨lab ".Lwc_rodata.x13", ⟨-40, []⟩, sJp lbl ms g R⟩)
      (At exe endPc R F (sX lbl ms g)) := by
    refine hello1_rodata_post_runW hp hend hF hR (by omega) hhi (show SO.le ⟨8, []⟩ ⟨8, []⟩ = true by decide)
      (RdPostLW.noSetFs hp hend hWpost)
      ?hbp ?hra ?hmem ?hr0 ?h1 ?h2 ?hr2 ?h3 ?h4 ?hedge
    case hbp =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, -, -, -, -, -, hbp⟩, -⟩
      exact hbp
    case hra =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, -, -, -, -, h0, -⟩, -⟩
      show Int64.ofBitVec g.ra = _
      rw [h0]
    case hmem =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, hx0, hA, hold, -, -, -⟩, -⟩ i hi m hm
      rcases hi with rfl | rfl
      · have := hbuf old hold 0 (.inl rfl) m hm
        rw [bAddr_rax_0]
        rw [show σ0.regs.rax.toBitVec = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + 0) by
          apply BitVec.eq_of_toNat_eq
          rw [show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0, BitVec.toNat_ofNat]
          have hroom := hQ.room
          have hcells := hQ.cells
          have hoff : ms.off 2 τ8 = 8 := by
            have h := hQ.off
            simp only [rdQ] at h
            rw [h]; decide
          omega]
        exact this
      · have := hbuf old hold 8 (.inr rfl) m hm
        rw [bAddr_rax_8]
        rw [show σ0.regs.rax.toBitVec + 8#64 = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + 8) by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          have hroom := hQ.room
          have hcells := hQ.cells
          have hoff : ms.off 2 τ8 = 8 := by
            have h := hQ.off
            simp only [rdQ] at h
            rw [h]; decide
          omega]
        exact this
    case hr0 =>
      rintro σ0 c ⟨l, ini, hRF, rfl⟩
      obtain ⟨A, old, hl, -⟩ := id hRF
      exact ⟨rdC1 l ini, .single (rdCA_store (p := p) (ini := ini) hl).1, l, ini, hRF, rfl⟩
    case h1 =>
      rintro σ0 c ⟨l, ini, hRF, rfl⟩
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, hh, -, -⟩ := rdCA_store (p := p) (ini := ini) hl
      refine ⟨_, _, _, _, _, hx, ?_, hh, fun r w' _ _ => ⟨l, ini, w', hRF, rfl⟩⟩
      rw [bAddr_rax_0, show σ0.regs.rax.toBitVec.toNat = A + 8 * 0 by
        rw [show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0]; omega]
      exact hv
    case h2 =>
      rintro σ0 c ⟨l, ini, w', hRF, rfl⟩
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, -, hev, hk⟩ := rdCA_store (p := p) (ini := ini) hl
      refine ⟨_, _, _, _, _, _, _, w', hx, ?_, rfl, hev, ?_, l, ini, w', hRF, (rdC1_next l ini w').symm⟩
      · rw [bAddr_rax_0, show σ0.regs.rax.toBitVec.toNat = A + 8 * 0 by
          rw [show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0]; omega]
        exact hv
      · rw [show (rpK1.setWidth 128).toNat = rdK1 by decide]; exact hk
    case hr2 =>
      rintro σ0 c ⟨l, ini, wo0, hRF, rfl⟩
      obtain ⟨A, old, hl, -⟩ := id hRF
      exact ⟨rdC3 l ini wo0, .single (rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl).1, l, ini, wo0, hRF, rfl⟩
    case h3 =>
      rintro σ0 c ⟨l, ini, wo0, hRF, rfl⟩
      have h8 := hA8 σ0 l hRF
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, hh, -, -⟩ := rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl
      refine ⟨_, _, _, _, _, hx, ?_, hh, fun r w' _ _ => ⟨l, ini, wo0, w', hRF, rfl⟩⟩
      rw [bAddr_rax_8, h8, hx0]
      exact hv
    case h4 =>
      rintro σ0 c ⟨l, ini, wo0, w', hRF, rfl⟩
      have h8 := hA8 σ0 l hRF
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, -, hev, hk⟩ := rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl
      refine ⟨_, _, _, _, _, _, _, w', hx, ?_, rfl, hev, ?_, l, ini, wo0, w', hRF, (rdC3_next l ini wo0 w').symm⟩
      · rw [bAddr_rax_8, h8, hx0]
        exact hv
      · rw [show (rpK2.setWidth 128).toNat = rdK2 by decide]; exact hk
    case hedge =>
      rintro σ0 c ⟨l, ini, wo0, wo1, ⟨A, old, hl, hx0, hA, hold, h8, -, -⟩, rfl⟩ σ' hax hdx hcx hsi hbp -
      refine ⟨rdRet l ini wo0 wo1, rdC4_run l ini wo0 wo1,
        ⟨l, ini, wo0, wo1, A, old, rfl, hl, ?_, hA, hold, hdx, hcx, hsi⟩, hbp.trans h8⟩
      show σ'.regs.rax.toBitVec.toNat = A
      rw [hax]; exact hx0
  -- composed, under the thread pointer's memory side
  have hA : SegW (NoSetFsW W K) K p lbl ms' (At exe endPc R F ⟨lab "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => At exe endPc R F (sX lbl ms g) s c ∨ At exe endPc R F (rX ms' lab lbl R J1 .abort) s c) := by
    refine SegW.seq_left (hpre.mono_post fun s c ⟨y, h⟩ => ?_) hpost
    cases y
    · obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, hJ⟩ := h
      exact .inl ⟨he, hn, hdc, hpc, σ, hAb, hD, x13_sJp hJ⟩
    · exact .inr h
  have hB := SegW.keepTPN (t := g.tp) hK hA
  -- the heap abort
  have hAb : SegW W K p lbl ms (At exe endPc R F (rX ms' lab lbl R J1 .abort)) (fun _ _ => False) := by
    refine Abort.Disp.seg_jabort2W rfl ?_ hF hR (by show R.lo ≤ -208 - 32; omega)
      (by show (-208 : Int) + 8 ≤ R.hi; omega) (by show (-208 : Int) % 8 = 0; decide) hK ?_
    · rintro σ c ⟨h2, -⟩
      exact h2
    · rintro m0 σC c0 ⟨h2, q, hf, σe, -, hc⟩
      exact hstub m0 σC c0 h2 ⟨q.1, callOK_untp q.2, hc, hf⟩
  have hC := SegW.seq_left (hB.mono_post (Q' := fun s c => At exe endPc R F (rX ms' lab lbl R J1 .abort) s c ∨
    (At exe endPc R F (sX lbl ms g) s c ∧ TP g.tp s)) fun s c ⟨h, ht⟩ =>
    h.elim (fun h => .inr ⟨h, ht⟩) fun h => .inl h) hAb
  refine (SegW.of_imp (L := R.addr 0 = g.sp) fun hL => (hC.mono_post fun s c h => ?_)).mono_pre
    fun s c h => ?_
  · rcases h with h | ⟨⟨he, hn, hdc, hpc, σ, hAb, hD, hJ, hbp⟩, ht⟩
    · exact h.elim
    refine ⟨he, hn, hdc, hpc, σ, hAb, hD, hJ, hbp, ?_, ?_⟩
    · have := hAb.so .rsp 8 rfl
      rw [addr8, hL] at this
      exact this
    · rw [← hAb.regs]; exact ht
  · obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, ⟨hc, hfp, hra, hsp, htp⟩, hl⟩ := id h
    refine ⟨⟨h, ?_⟩, ?_⟩
    · show s.st.1.regs.fsBase = g.tp
      rw [hAb.regs]; exact htp
    · rw [← hsp]; exact (hAb.so .rsp 0 rfl).symm

end Proof

end Spike.Lib.X64.Flow.Hello1
