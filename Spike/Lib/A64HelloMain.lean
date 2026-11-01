/-
**`hello.w`'s `scc_rt_main` on AArch64 up to `wc_main`**, inside `W`, in any valid layout of
`helloProg` (`Spike/Lib/A64HelloCode.lean`), from checks decided once on the program (`decide +kernel`). It is the
twin of `Spike/Lib/A64Hello1Main.lean`'s two halves at hello's `wc_rodata` (`Spike/Lib/A64HelloRodata.lean`, the
source's local runs and the publish fence). `wc_main` does not return before its `clone`, so, as in
`Spike/Lib/A64WakeMain.lean`, the call of `wc_main` ends in a segment of `wc_main` given as a premise (`hWc`).

hello.w's `scc_rt_main` is hello1.w's (frame 80, `x0` at the frame's base; `.0_entry`'s `bl wc_rodata`; `.sp0`'s
copy of `wc_rodata`'s four results and the saved `x0` to `x0`…`x4`, `bl wc_main`), at the same labels: hello1's
blocks, nodes and `mainIn` are reused, decided again on `helloProg`.

- `hMainPro`, `hello_mainPro`, `hello_mainIn`: the checks.
- `MainPreW`, `hello_main_pre_segW`: from `scc_rt_main`'s entry to `wc_rodata`'s allocator's return at its `.sp0`
  (or its heap abort), in `wc_rodata`'s region at the call. `wc_rodata`'s entry block takes the source's local run
  to `J1 σC` (`hloc`).
- `wcR`, `wcF`, `wcJ0`, `wcR_ok`: `wc_main`'s region (`D` deep), frame condition and entry invariant at the call.
- `MainPostW`, `hello_main_post_segW`: from `wc_rodata`'s `.sp0` (the rest of `wc_rodata`, the publish fence
  included), its return, `.sp0`'s block, the call of `wc_main`, then `wc_main`'s segment (`hWc`).
- `hello_main_xa_post`, `hello_main_hxa_of_post`: the bridge from the allocator's fresh-label landing to
  `wc_rodata`'s `.sp0` (`Hello1.hello1_main_xa_post` at hello's labels).
-/
import Spike.Lib.A64Hello1Main
import Spike.Lib.A64HelloRodata

namespace Spike.Lib.A64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk seg_oneW)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.A64.Flow.Hello1 (mB0 mB0_ok mB0_run mB1 mB1_ok mB1_run mainIn mJ mN0 mNC mR mF mRdJ0 mR_ok mS0 mWC
  AG aR rpK1 rpK2)
open Spike.Lib.A64.Flow.HelloRd (rN rX RdPreW RdPostW PN pN hello_rodata_pre_runW hello_rodata_post_runW)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

/-- `scc_rt_main`'s prologue: frame 80, `x0` (the thread pointer) at 0. -/
abbrev hMainPro : Bool := prologueIn SccCode.helloProg "scc_rt_main" ".L1_scc_rt_main.stack_check"
  ".L1_scc_rt_main.0_entry" 80 8 ".L1_scc_rt_main.stack_grow" [(.X0, 0)]

theorem hello_mainPro : hMainPro = true := by decide +kernel

/-- hello1's `scc_rt_main` blocks, at the same labels in `helloProg`. -/
theorem hello_mainIn : mainIn SccCode.helloProg = true := by decide +kernel

/-! ## `scc_rt_main` up to `wc_rodata`'s allocator's return -/

/-- **`scc_rt_main`'s states up to `wc_rodata`'s allocator's return inside `W`**, none moved by `K`: its
prologue's, the call block's, and `wc_rodata`'s in its region for every caller's state `σC` at the call (the
entry block's source run to `J1 σC`). -/
structure MainPreW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J : AS → Ctl → Prop)
    (J1 : AS → AS → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 80 8
    ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J
  call : BlkW W K exe endPc R F (mN0 (_root_.Executable.labels exe).label J) mB0
  rd : ∀ m0 σC, RdPreW W K exe endPc (mR R) (mF R F m0 σC) ms
    (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) (J1 σC)

/-- `scc_rt_main` up to the allocator's return is inside the trivial predicate, with no outside moves. -/
theorem MainPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J : AS → Ctl → Prop} {J1 : AS → AS → Ctl → Prop} :
    MainPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J J1 :=
  ⟨ProW.triv, BlkW.triv, fun _ _ => RdPreW.triv⟩

section MainPre

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` up to `wc_rodata`'s allocator's return is one segment inside `W`** in any valid layout of
`helloProg`: from its entry (invariant `J`, `sp` at the region's base) to `wc_rodata`'s exits
(`hello_rodata_pre_runW`) in its region at the call, for some caller's state there.
- The limit word's facts hold for both frames (`hlimM`, `hlimR`).
- `wc_rodata`'s entry block takes a local run of the source to `J1 σC` (`hloc`), where the source is at the
  buffer's allocation (`hq`).
- `hmem`, `hxa` as for `hello_rodata_pre_runW`, for every caller's state at the call.
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_main_pre_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {J1 : AS → AS → Ctl → Prop} (hW : MainPreW W K exe endPc R F ms J J1)
    (hlimM : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec))
    (hlimR : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8)
      (σ.regs.SP.toBitVec - (80 : Int64).toBitVec - (48 : Int64).toBitVec))
    (hloc : ∀ σC σ c, mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC σ c →
      ∃ c', LocalRun p c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ m0 σC, ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label
          (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) (J1 σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => ∃ m0 σC y, At exe endPc (mR R) (mF R F m0 σC)
        (rX ms (_root_.Executable.labels exe).label lbl (J1 σC) y) s c) := by
  have hin := hello_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨h0, -⟩, hg1⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e1 : lab ".L1_scc_rt_main.sp0" = lab ".L1_scc_rt_main.0_entry" + Int64.ofNat (4 * 1) :=
    label_labelGap hp hg1
  refine SegW.seq (prologue_seg_ofW hp hend hello_mainPro (nb := mN0 lab J) (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -80; omega) hhi (by simp [Spike.Lib.offOk]) rfl
    (by show SO.le ⟨-80, []⟩ (oFr 80) = true; decide) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mNC lab J))
      (seg_oneW (seg_ndW (by simp [mB0]) mB0_ok hF hR hal (by omega) hhi
        (code_of hp hend h0 (ofNat4_zero _)) hW.call fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)) ?_)
  · -- the prologue
    intro σ c hJ
    have hl := hlimM σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Ret0.setXReg_TPIDR]
  · simp only [mN0, mNC]; rw [mB0_run]
  · simp only [mN0, mNC]; rw [mB0_run]; rfl
  · simp only [mN0, mNC] at hJ ⊢
    rw [mB0_run]
    obtain ⟨σe, hJe, h16, h8, h80, hsp, htp⟩ := hJ
    refine ⟨⟨σe, hJe, h16, h8, h80, hsp, htp⟩, ?_⟩
    rw [e1]
    show BitVec.ofInt 64 _ = _
    rw [Ret0.ofInt_bmod]
    simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
    rfl
  · -- `wc_rodata` in its region
    refine SegW.mono_pre (P := fun s c => ∃ G : MachineData × AS, At exe endPc (mR R) (mF R F G.1 G.2)
      ⟨lab "wc_rodata", ⟨0, []⟩, mRdJ0 (mNC lab J).J G.2⟩ s c) (SegW.exists_pre fun G => ?_) ?_
    · obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi G.1 G.2
      refine (hello_rodata_pre_runW hp hend hF' hR' hal' (by show (-208 : Int) ≤ -208; decide)
        (by show (0 : Int) ≤ 0; decide) (hW.rd G.1 G.2) ?_ (hloc G.2) (hq G.2) ?_ (hxa G.1 G.2)).mono_post
        fun s c ⟨y, h⟩ => ⟨G.1, G.2, y, h⟩
      · rintro σ c ⟨rfl, ⟨σe, hJe, -, -, -, hsp, htp⟩, -⟩
        have h := (hlimR σe c hJe).mono (F' := mF R F G.1 G.2) fun m h => h.1
        have ht : tcbA (enter (-80) G.2).regs 8 = tcbA σe.regs 8 := by
          simp only [tcbA, enter, htp]
        rw [ht]
        show LimOk ms _ exe endPc _ (G.2.regs.SP.toBitVec - _)
        rw [hsp]; exact h
      · intro q hq' a ha
        exact fun m hm => hmem q hq' a ha m hm.1
    · intro s c h
      obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hc, hσ, hJ⟩ := at_enter (lo' := -208) (hi' := 0)
        (by show R.lo ≤ -80 + -208; omega) (by show (-80 : Int) < R.hi; omega) (by decide)
        (by show (-80 : Int) % 8 = 0; decide) h
      exact ⟨(m0, σC), he, hn, hdc, hpc, σ, hA, hD, hσ, hc ▸ hJ⟩

end MainPre

/-! ## `scc_rt_main` from `wc_rodata`'s `.sp0` into `wc_main` -/

/-- `wc_main`'s region at the call, `D` deep. -/
abbrev wcR (R : Region) (D : Int) : Region := R.callee (-80) (-D) 0

/-- **`wc_main`'s frame condition at the call** from the caller's state `m0`, `σC` (`at_enter`). -/
def wcF (R : Region) (D : Int) (F : MachineData → Prop) (m0 : MachineData) (σC : AS) (m : MachineData) : Prop :=
  F m ∧ CKept R (-80) (-D) 0 m0 m ∧ Abs R ⟨-80, []⟩ m0 σC

/-- `wc_main`'s entry invariant from the caller's state `σC` at the call node of invariant `Jc`. -/
def wcJ0 (Jc : AS → Ctl → Prop) (σC : AS) (σ : AS) (c : Ctl) : Prop := σ = enter (-80) σC ∧ Jc σC c

/-- **`scc_rt_main`'s states from `wc_rodata`'s `.sp0` up to the call of `wc_main` inside `W`**, none moved by
`K`: `wc_rodata`'s from `.sp0` in its region (the caller's state `m0`, `σC` at its call), and the `.sp0` block's.
`wc_main`'s own are in its segment (`hWc`). -/
structure MainPostW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (m0 : MachineData) (σC : AS)
    (Jp Jp' J1 J2 J2' J3 J4 J5 Jr : AS → Ctl → Prop) : Prop where
  rd : RdPostW W K exe endPc (mR R) (mF R F m0 σC) Jp Jp' J1 J2 J2' J3 J4 J5
  sp0 : BlkW W K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1

/-- `scc_rt_main` from `.sp0` to the call of `wc_main` is inside the trivial predicate, with no outside moves. -/
theorem MainPostW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {m0 : MachineData} {σC : AS} {Jp Jp' J1 J2 J2' J3 J4 J5 Jr : AS → Ctl → Prop} :
    MainPostW (fun _ _ => True) (fun _ _ => False) exe endPc R F m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 Jr :=
  ⟨RdPostW.triv, BlkW.triv⟩

section MainPost

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- `wc_main`'s region at the call is a region, 16-aligned, its frame condition stable. -/
theorem wcR_ok {D : Int} (hD : 0 ≤ D) (hD16 : D % 16 = 0) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hF : FStable R F) (hlo : R.lo ≤ -80 - D) (hhi : 0 ≤ R.hi) (m0 : MachineData) (σC : AS) :
    (wcR R D).OK ∧ (wcR R D).base.toNat % 16 = 0 ∧ FStable (wcR R D) (wcF R D F m0 σC) := by
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -80 + -D by omega) (by omega)
    (show (-80 : Int) < R.hi by omega)
  refine ⟨Region.callee_ok hR (by omega) (by omega) (by omega) (by omega), ?_,
    fstable_enter hR hF (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  have : (((wcR R D).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` into `wc_main` is one segment inside `W`** in any valid layout of
`helloProg`, for a caller's state `m0`, `σC` at `wc_rodata`'s call.
- `wc_rodata` from `.sp0` in its region (`hello_rodata_post_runW` to `scc_rt_main`'s `.sp0`, of invariant `Jr`;
  `hra`, `hmem`, `hr0`, `h1`, `h2`, `hr2`, `h3`, `h4`, the publish fence's `hfen`, and `hedge` as there).
- Leaving its region (`at_leave`), the `.sp0` block, the call of `wc_main` into its region at the call (`D` deep,
  `at_enter`).
- Then `wc_main`'s segment there to `Q m1 σ1` for every caller's state at the call (`hWc`, the instance's).
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_main_post_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    {D : Int} (hD : 0 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) {m0 : MachineData} {σC : AS} {Jp Jp' J1 J2 J2' J3 J4 J5 Jr : AS → Ctl → Prop}
    (hW : MainPostW W K exe endPc R F m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 Jr)
    (hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8)))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none)
    (hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c')
    (h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c')
    (h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hfen : ∀ σ0 c, J4 σ0 c → ∃ c', FenceRun p ms.pub .st c c' ∧ J5 σ0 c')
    (hedge : ∀ σ0 c, J5 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ Jr σ' c')
    {Q : MachineData → AS → Frag isaLSE2}
    (hWc : ∀ m1 σ1, (wcR R D).OK → (wcR R D).base.toNat % 16 = 0 → FStable (wcR R D) (wcF R D F m1 σ1) →
      SegW W K p lbl ms (At exe endPc (wcR R D) (wcF R D F m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1⟩) (Q m1 σ1)) :
    SegW W K p lbl ms
      (At exe endPc (mR R) (mF R F m0 σC) (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s0))
      (fun s c => ∃ m1 σ1, Q m1 σ1 s c) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hb1⟩, -⟩, hg2⟩ := hin
  have e2 : lab ".L1_scc_rt_main.sp1" = lab ".L1_scc_rt_main.sp0" + Int64.ofNat (4 * 10) :=
    label_labelGap hp hg2
  obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi m0 σC
  refine SegW.seq (Q := At exe endPc R F (mS0 lab R σC Jr))
    ((hello_rodata_post_runW hp hend hF' hR' hal' (by show (-208 : Int) ≤ -48; decide)
      (by show (0 : Int) ≤ 0; decide) (x := ⟨lab ".L1_scc_rt_main.sp0", ⟨0, []⟩, Jr⟩) rfl hW.rd hra hmem
      hr0 h1 h2 hr2 h3 h4 hfen hedge).mono_post fun s c h => ?_)
    (SegW.seq (Q := At exe endPc R F (mWC lab σC Jr))
      (seg_oneW (seg_ndW (by simp [mB1]) mB1_ok hF hR hal (by omega) hhi
        (code_of hp hend hb1 (ofNat4_zero _)) hW.sp0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)) ?_)
  · -- leaving `wc_rodata`'s region
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC', hJ, rfl, hσ⟩ :=
      at_leave (P := fun σ => σ = σC) rfl (fun m hm => ⟨hm.1, m0, σC, ⟨-80, []⟩, hm.2.1, hm.2.2, rfl⟩) h
    exact ⟨he, hn, hdc, hpc, σ, hA, hD, σx, hJ, hσ⟩
  · simp only [mS0, mWC]; rw [mB1_run]
  · simp only [mS0, mWC]; rw [mB1_run]; rfl
  · simp only [mS0, mWC] at hJ ⊢
    obtain ⟨σx, hJr, rfl⟩ := hJ
    rw [mB1_run]
    refine ⟨σx, hJr, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
    · show (leave (mR R) (-80) σC σx).slot (-80) = _
      simp only [leave]
      exact ite_eq_right (by simp only [Region.Off, Region.callee]; omega)
    · rw [e2]
      show BitVec.ofInt 64 _ = _
      rw [Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
      rfl
  · -- `wc_main` in its region
    refine SegW.mono_pre (P := fun s c => ∃ G : MachineData × AS, At exe endPc (wcR R D) (wcF R D F G.1 G.2)
      ⟨lab "wc_main", ⟨0, []⟩, wcJ0 (mWC lab σC Jr).J G.2⟩ s c) (SegW.exists_pre fun G => ?_) ?_
    · obtain ⟨hR'', hal'', hF''⟩ := wcR_ok hD hD16 hR hal hF hloD hhi G.1 G.2
      exact (hWc G.1 G.2 hR'' hal'' hF'').mono_post fun s c h => ⟨G.1, G.2, h⟩
    · intro s c h
      obtain ⟨m1, σ1, he, hn, hdc, hpc, σ, hA, hD', hc, hσ, hJ⟩ := at_enter (lo' := -D) (hi' := 0)
        (by show R.lo ≤ -80 + -D; omega) (by show (-80 : Int) < R.hi; omega) (by decide)
        (by show (-80 : Int) % 8 = 0; decide) h
      exact ⟨(m1, σ1), he, hn, hdc, hpc, σ, hA, hD', hσ, hc ▸ hJ⟩

end MainPost

/-! ## From the allocator's fresh-label landing to `wc_rodata`'s `.sp0`

`hello_main_pre_segW` ends at an allocation's continuation `ms.xa` (`hxa`); `hello_main_post_segW` starts at
`wc_rodata`'s `.sp0` in its region. The bridge leaves the allocator's region (`at_leave`) and lands at `.sp0` for
an invariant `Jp` the landing implies (`hJp`), so the choice of `ms.xa` stays the instance's. -/

section MainBridge

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The allocator's fresh-label landing is at `wc_rodata`'s `.sp0`**, in its region at `scc_rt_main`'s call
(caller's state `m0`, `σC`): from the continuation node `Ea` in the allocator's region, under a frame condition
`F'` the call hands it (as in `hello_main_pre_segW`'s `hxa`), the state is at `pN .s0` of an invariant `Jp` every
landing's state left to `wc_rodata` satisfies (`hJp`). -/
theorem hello_main_xa_post {J Jp Jp' J1' J2 J2' J3 J4 J5 : AS → Ctl → Prop} {J1 : AS → AS → Ctl → Prop}
    {m0 : MachineData} {σC : AS} {q : AG ms (_root_.Executable.labels exe).label} {F' : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat}
    (hFF : ∀ m, F' m → mF R F m0 σC m)
    (hkeep : ∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) (J1 σC)
        .call).J σ c ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧ CKept (mR R) (-48) (-160) 0 mC m)
    (hJp : ∀ σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) (J1 σC)
        .call).J σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp (leave (aR (mR R)) (-48) σ σx) c)
    {s : State} {c : Ctl} (h : At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c) :
    At exe endPc (mR R) (mF R F m0 σC) (pN (_root_.Executable.labels exe).label Jp Jp' J1' J2 J2' J3 J4 J5 .s0)
      s c := by
  have h' := at_leave (R := mR R) (kc := -48) (lo' := -160) (hi' := 0)
    (P := fun σ => ∃ c0,
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) (J1 σC)
        .call).J σ c0 ∧ (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0)
    rfl (fun m hm => by
      obtain ⟨mC, σ, c0, hA, h1, h2, hK⟩ := hkeep m hm
      exact ⟨hFF m hm, mC, σ, _, hK, hA, c0, h1, h2⟩) h
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σ', hJx, ⟨c0, h1, h2⟩, rfl⟩ := h'
  refine ⟨he, hn, hdc, ?_, _, hA, hD, hJp σx σ' c0 c hJx h1 h2⟩
  rw [hpc]
  show Int64.ofBitVec q.1.ra = (_root_.Executable.labels exe).label ".L19_wc_rodata.sp0"
  rw [← h2.2.2.1]
  show Int64.ofBitVec σ'.regs.X30.toBitVec = _
  rw [h1.2.2.2.2, int64_ofBitVec_toBitVec]

/-- **`hello_main_pre_segW`'s `hxa` from the landing at `.sp0`**: if every state at `wc_rodata`'s `.sp0` in its
region, for some caller's state `m0`, `σC` at the call (of an invariant `Jp m0 σC` the landings imply, `hJp`), is
one a fresh label's allocation continues in (`hpost`), the allocator's landings are (`hello_main_xa_post`). -/
theorem hello_main_hxa_of_post {J : AS → Ctl → Prop} {J1 : AS → AS → Ctl → Prop}
    {Jp Jp' J1' J2 J2' J3 J4 J5 : MachineData → AS → AS → Ctl → Prop}
    (hJp : ∀ m0 σC (q : AG ms (_root_.Executable.labels exe).label) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) (J1 σC)
        .call).J σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp m0 σC (leave (aR (mR R)) (-48) σ σx) c)
    (hpost : ∀ l b w s c, lbl l = none → (∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (pN (_root_.Executable.labels exe).label (Jp m0 σC) (Jp' m0 σC) (J1' m0 σC) (J2 m0 σC) (J2' m0 σC)
        (J3 m0 σC) (J4 m0 σC) (J5 m0 σC) .s0) s c) →
      ms.xa l b w s c) :
    ∀ m0 σC, ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label
          (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) (J1 σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c :=
  fun m0 σC q _ hFF hkeep l b w _ _ hl h =>
    hpost l b w _ _ hl ⟨m0, σC, hello_main_xa_post hFF hkeep (hJp m0 σC q l b w) h⟩

end MainBridge

end Spike.Lib.A64.Flow.HelloM

/-- info: 'Spike.Lib.A64.Flow.HelloM.hello_mainPro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_mainPro

/-- info: 'Spike.Lib.A64.Flow.HelloM.hello_mainIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_mainIn

/-- info: 'Spike.Lib.A64.Flow.HelloM.hello_main_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_main_pre_segW

/--
info: 'Spike.Lib.A64.Flow.HelloM.hello_main_post_segW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_main_post_segW

/--
info: 'Spike.Lib.A64.Flow.HelloM.hello_main_hxa_of_post' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_main_hxa_of_post
