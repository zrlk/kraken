/-
**The counter add's held state carries its own segment** (AArch64): from
`scc_rt_alloc`'s node `n4` after the counter's add (the held count, in the
allocator's region at the call), the levels' segment inside `W2` (`Sg2`) at
every family containing the starts `StartsN`, so the held pair is a
self-segment start (`SelfN`, `selfN_of`) and `pendA_of_selfN`'s `hQ`.
`allocHeld_sg2` replaces the planned call-site entry `newBuf_callW_ctxT`.

**No continuation past the return.** From `n4` the allocator does not reach
its caller at the held placement: the tail's only exit there is the heap
abort (`seg_allocW_tailA`); its return's row is the allocation (`Out.alloc`),
whose successor is in `xa`, i.e. a landing of `StartsN` at the next
placement (`xa_of_landN`, `landStk_hxa`), not a pair of this segment. So the
segment is the tail (`allocW2TX`, without the counter context), the abort
exit left into the caller's region (`at_leaveE`) and the heap abort path
(`seg_jabort2W`), which does not return.

**Not circular.** The segment asks `W2` and `msOfAX` at `IN … J'` (the tail
without the counter context `hctx`), the allocation fragment through `J'`
containing `StartsN` (the landings), the abort path's obligations: no
`PendA`, no `AllocCtx` at the add, no full `allocW2`, and no held pair in
`J'`, so no held pair's segment asks another's.

- `N_msOfAX`: the allocator's nodes read no `xa`, so `msOfAX` at any two
  families gives the same nodes;
- `callOK_msOfAX`, `code_msOfAX`: a call's premises and the allocator's
  code at any family;
- `HeldAb`: the tail's abort exit in the caller's region;
- `leaveOk_of_allocCtx`: `at_leaveE`'s frame premise from the call context;
- `AllocWT.noMsr`, `AllocWT.tpXa`, `code_tpXa`: the tail inside `NoMsrW` and
  the tail and code under `tpXa` (`SegW.keepTPN`'s premises);
- `allocHeld_seg`: the held pair's segment inside `W2` at a family `Jv`, from
  `n4` with the thread pointer `TP tp` (kept along the tail, `SegW.keepTPN`,
  so the allocation fragment `hxa` is asked at `TP tp`, as `landStk_hxa`);
- `allocHeld_sg2`: as `Sg2` at every family containing `StartsN`, from a
  fixed family `I0`'s nodes;
- `allocHeld_nr`: a held pair is not at a `ret` (`pendA_of_selfN`'s `hnr`).
-/
import Spike.Lib.LowerA64.AllocTailW2
import Spike.Lib.A64Hello1SetupTail

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun MemSide SegW SegWS Frag.at)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (BlkW NodeW At holdCtr DFrame FStable CKept Abs leave ND AS)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff TakeK)
open Spike.Lib.A64.Flow.NewBuf (AllocCtx)
open Spike.Lib.A64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.A64.Alloc (Call AllocWT N E AN)
open Spike.Lib.A64.AllocG (allocPhOk allocAbOk)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Flow (NoMsrW)

/-! ## The nodes at any family -/

section Fam

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own' : OwnS} {ar : Arena} {ab : Option (State → Prop)}

/-- **The allocator's nodes read no `xa`**: at `msOfAX` over any two
families they are the same. -/
theorem N_msOfAX {I I' : InvS} {L : Lbl} {ls : Lsize} {fs : List TermRun.Frame} (lab : Label → Int64)
    (q : Call) (i : AN) :
    N lab (msOfAX Λ μ p rd G own' ar I ab L ls fs) q i = N lab (msOfAX Λ μ p rd G own' ar I' ab L ls fs) q i := by
  cases ab <;> cases i <;> rfl

/-- **A call's premises at any family** (`msOfAX` differs only in `xa`). -/
theorem callOK_msOfAX {I I' : InvS} {L : Lbl} {ls : Lsize} {fs : List TermRun.Frame} {lab : Label → Int64}
    {q : Call} (h : q.OK (msOfAX Λ μ p rd G own' ar I ab L ls fs) lab) :
    q.OK (msOfAX Λ μ p rd G own' ar I' ab L ls fs) lab := by
  cases ab <;>
    exact ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt,
      h.mp, h.grow, h.hdr⟩

/-- **The allocator's code at any family** (its nodes' pcs read no memory
side). -/
theorem code_msOfAX {I I' : InvS} {L : Lbl} {ls : Lsize} {fs : List TermRun.Frame} {q : Call}
    {exe : _root_.Executable} {endPc : Int64}
    (h : Spike.Lib.A64.Alloc.Code (msOfAX Λ μ p rd G own' ar I ab L ls fs) q exe endPc) :
    Spike.Lib.A64.Alloc.Code (msOfAX Λ μ p rd G own' ar I' ab L ls fs) q exe endPc :=
  ⟨h.e, h.entry, h.n2, h.cnt, h.cnt1, h.cnt2, h.rmw, h.n4, h.n5, h.slow, h.n7, h.full, h.ok, h.ok1, h.ok2, h.n12,
    h.hdr, h.n13, h.ret⟩

end Fam

/-! ## The abort exit in the caller's region -/

/-- **The tail's abort exit in the caller's region** `R` (the allocator's
region `R.callee (-fr) (-160) 0`, the caller's frame of `fr` bytes): at
`scc_rt_abort` with `sp` at `-fr - 160`, the abstract state the caller's
`σC` of `P` left (`at_leaveE`'s node at `E … .abort`). -/
def HeldAb (lab : Label → Int64) (ms : MemSide isaLSE2) (q : Call) (lbl : WeakMem.AllocLabel → Option Nat)
    (R : Region) (fr : Int) (P : AS → Prop) : ND :=
  ⟨(E lab ms q lbl .abort).pc, ⟨-fr + -160, []⟩, fun σ c => ∃ σx σC, (E lab ms q lbl .abort).J σx c ∧ P σC ∧
    σ = leave (R.callee (-fr) (-160) 0) (-fr) σC σx⟩

/-- **`at_leaveE`'s frame premise from the allocator's call context**: a
frame condition giving the caller's `F` and the call's context `AllocCtx`
gives the caller's cells kept outside the allocator's region and a caller's
state of the call node at the call's source control `q.c0` (the allocator's
entry `N … .e` holds at `q.c0`). -/
theorem leaveOk_of_allocCtx {F F' : MachineData → Prop} {ms : MemSide isaLSE2} {lab : Label → Int64} {R : Region}
    {fr : Int} {Jc : AS → Ctl → Prop} {q : Call} (h : ∀ m, F' m → F m ∧ AllocCtx ms lab R fr Jc q m) :
    ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R (-fr) (-160) 0 m0 m ∧ Abs R o m0 σC ∧ Jc σC q.c0 := by
  intro m hm
  obtain ⟨hF, mC, σC, c, hA, hJ, he, hK⟩ := h m hm
  obtain rfl : c = q.c0 := he.1
  exact ⟨hF, mC, σC, _, hK, hA, hJ⟩

/-! ## The tail at cells other than `MSR`, under `tpXa` -/

section TP

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop} {ms : MemSide isaLSE2} {q : Call}

open Spike.Lib.A64.Flow (BlkW.noMsr NodeW.noMsr) in
/-- **`scc_rt_alloc`'s tail at its code is inside `NoMsrW W K`** (`AllocW.noMsr`'s tail). -/
theorem AllocWT.noMsr (h : AllocWT ms q W K exe endPc R F) (hc : Spike.Lib.A64.Alloc.Code ms q exe endPc) :
    AllocWT ms q (NoMsrW W K) K exe endPc R F :=
  ⟨BlkW.noMsr h.n4 hc.n4 (by decide), BlkW.noMsr h.n5 hc.n5 (by decide), BlkW.noMsr h.slow hc.slow (by decide),
    BlkW.noMsr h.n7 hc.n7 (by decide), BlkW.noMsr h.full hc.full (by decide), BlkW.noMsr h.ok hc.ok (by decide),
    NodeW.noMsr h.ok1 hc.ok1 (by simp) (by decide), NodeW.noMsr h.ok2 hc.ok2 (by simp) (by decide),
    BlkW.noMsr h.n12 hc.n12 (by decide), NodeW.noMsr h.hdr hc.hdr (by simp) (by decide),
    BlkW.noMsr h.n13 hc.n13 (by decide), NodeW.noMsr h.ret hc.ret (by simp) (by decide)⟩

/-- The tail's states under `tpXa` (its nodes read no `xa`). -/
theorem AllocWT.tpXa {t : UInt64} (h : AllocWT ms q W K exe endPc R F) : AllocWT (tpXa ms t) q W K exe endPc R F :=
  ⟨h.n4, h.n5, h.slow, h.n7, h.full, h.ok, h.ok1, h.ok2, h.n12, h.hdr, h.n13, h.ret⟩

/-- The allocator's code under `tpXa` (its nodes' pcs read no memory side). -/
theorem code_tpXa {t : UInt64} (h : Spike.Lib.A64.Alloc.Code ms q exe endPc) :
    Spike.Lib.A64.Alloc.Code (tpXa ms t) q exe endPc :=
  ⟨h.e, h.entry, h.n2, h.cnt, h.cnt1, h.cnt2, h.rmw, h.n4, h.n5, h.slow, h.n7, h.full, h.ok, h.ok1, h.ok2, h.n12,
    h.hdr, h.n13, h.ret⟩

end TP

/-! ## The held pair's segment -/

section Held

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F F' : MachineData → Prop} {q : Call} {a : Int64}

/-- **The counter add's held pair is one segment inside `W2`** at the family
`Jv`, the frames `fs`, into no pair: from `n4` in the allocator's region
`R.callee (-fr) (-160) 0` at `F'` (`allocW2TX`'s premises there), the tail
to its heap abort alone (`seg_allocW_tailA`, the allocation fragment `hxa`),
left into the caller's region `R` at `F` (`at_leaveE`, `hleave`), the heap
abort path (`seg_jabort2W`, its obligations `hstub`), which does not return
(`SegWS.liftS_noret`). See the module docstring: no `PendA`, no counter
context. -/
theorem allocHeld_seg {rS : Range} (hI : InstOk exe endPc prog lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {fr : Int}
    (hRc : (R.callee (-fr) (-160) 0).OK) (halc : (R.callee (-fr) (-160) 0).base.toNat % 16 = 0)
    (hloc : (R.callee (-fr) (-160) 0).lo ≤ -160) (hhic : 0 ≤ (R.callee (-fr) (-160) 0).hi)
    (hlc : (R.callee (-fr) (-160) 0).lo % 8 = 0) (hhc : (R.callee (-fr) (-160) 0).hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F' m → StackOff rS (R.callee (-fr) (-160) 0) m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {Jv : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hq : q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ m, F' m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) (hG0F : ∀ m, F' m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F' m0 → ∀ (s : State) c, DFrame (R.callee (-fr) (-160) 0) m0 s.st.1 →
      (c = q.c0 ∨ ∃ o, c = holdCtr (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs)
    (hF' : FStable (R.callee (-fr) (-160) 0) F')
    (hcode : Spike.Lib.A64.Alloc.Code (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q exe endPc)
    {tp : UInt64}
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc (R.callee (-fr) (-160) 0) F'
        (Spike.Lib.A64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q l b w) s c →
      TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).xa l b w s c)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hfr : fr % 16 = 0)
    (hlo : R.lo ≤ -fr + -160 - 48) (hkc : -fr + -160 < R.hi) {Pc : AS → Prop}
    (hleave : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R (-fr) (-160) 0 m0 m ∧ Abs R o m0 σC ∧ Pc σC)
    (hstub : ∀ m0 σC c0, (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q lbl R fr Pc).J σC c0 →
      Spike.Lib.A64.Abort.Disp.StubHW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) p lbl (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) exe endPc
        (R.callee (-fr + -160) (-48) 0)
        (fun m => F m ∧ CKept R (-fr + -160) (-48) 0 m0 m ∧ Abs R ⟨-fr + -160, []⟩ m0 σC) c0) :
    SegWS (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) (TakeK a rS) p lbl
      (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize)
      (Frag.at (fun s c => At exe endPc (R.callee (-fr) (-160) 0) F'
        (N (_root_.Executable.labels exe).label (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q
          .n4) s c ∧ TP tp s) fs)
      (fun _ _ _ => False) := by
  have hW := allocW2TX (Dt := Dt) hI hA hph habk hown hRc halc hloc hhic hlc hhc hsub hfit hFO hp
    (fun _ _ => hq) hra hraAb hmem hno hlt h64 hG0F hP
  have hq' : q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs)
      (_root_.Executable.labels exe).label := by rw [hI.labOk]; exact hq
  have hK : (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).K = some Scc.Sem.A64.abi := by
    cases ab <;> rfl
  -- the tail under `tpXa`, the thread pointer kept (`SegW.keepTPN`), so the landings are at `tp`
  have h1 := Spike.Lib.A64.Flow.SegW.keepTPN (t := tp) hK
    (Spike.Lib.A64.Alloc.seg_allocW_tailA (p := p) (ms := tpXa (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl
        lsize fs) tp) hF' hRc halc hloc hhic (Spike.Lib.LowerA64.callOK_tpXa hq') (code_tpXa hcode)
      (fun a h m hm => match h with
        | .inl h => hmem a (.inl (by rw [h]; cases ab <;> rfl)) m hm
        | .inr ⟨o, hle, he⟩ => hmem a (.inr ⟨o, by cases ab <;> exact hle, he⟩) m hm)
      (fun l b w s c hl hAt htp => hxa l b w s c hl hAt htp)
      (Spike.Lib.LowerA64.AllocWT.noMsr (Spike.Lib.LowerA64.AllocWT.tpXa hW) (code_tpXa hcode)) .n4)
  have h1 := (h1.mono_pre fun s c h => h).mono_post (Q' := At exe endPc (R.callee (-fr) (-160) 0) F'
    (Spike.Lib.A64.Alloc.E (_root_.Executable.labels exe).label
      (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q lbl .abort)) fun s c h => h.1
  have h2 := Spike.Lib.A64.Abort.Disp.seg_jabort2W (W := fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab)
      lbl lsize s c fs) (K := TakeK a rS) (p := p) (lbl := lbl) (Q := fun _ _ => False)
    (nC := HeldAb (_root_.Executable.labels exe).label
      (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q lbl R fr Pc) rfl
    (fun σ c h => by
      obtain ⟨σx, σC, hJ, -, rfl⟩ := h
      have h2 : σx.regs.X0 = 2 := hJ.1
      show (σx.regs.X0).toBitVec.toNat = 2
      rw [h2]; rfl) hF hR hal hlo hkc (by show (-fr + -160) % 16 = 0; omega) hK hstub
  have h3 : SegW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) (TakeK a rS) p lbl
      (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs)
      (fun s c => At exe endPc (R.callee (-fr) (-160) 0) F'
        (N (_root_.Executable.labels exe).label (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q
          .n4) s c ∧ TP tp s)
      (fun _ _ => False) :=
    ((h1.mono_post fun s c h => Or.inl (Spike.Lib.A64.Flow.at_leaveE (P := Pc) rfl rfl hleave h)).seq_left
      (E := fun _ _ => False) h2).mono_post fun _ _ h => h.elim id id
  exact SegWS.liftS_noret fs h3 (fun _ _ h => h) _

/-- **The counter add's held pair carries its own segment at every family
containing the starts** (`pendA_of_selfN`'s `hQ`; it replaces the planned
`newBuf_callW_ctxT`): at each family `J'` containing `StartsN … S0 Es`,
`allocHeld_seg` at `IN … J'` is the levels' segment `Sg2 … J' lbl lsize`
from the held pairs at `n4`, the nodes read at a fixed family `I0`
(`N_msOfAX`), so the entry does not depend on `J'`. The family-free
premises are asked at `I0`; the allocation fragment (`hxa`, from the
landings `StartsN`, as `landStk_hxa`) and the abort path's obligations
(`hstub`) at each `J'`. No held pair is asked in `J'` (the module
docstring). -/
theorem allocHeld_sg2 {rS : Range} (hI : InstOk exe endPc prog lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {fr : Int}
    (hRc : (R.callee (-fr) (-160) 0).OK) (halc : (R.callee (-fr) (-160) 0).base.toNat % 16 = 0)
    (hloc : (R.callee (-fr) (-160) 0).lo ≤ -160) (hhic : 0 ≤ (R.callee (-fr) (-160) 0).hi)
    (hlc : (R.callee (-fr) (-160) 0).lo % 8 = 0) (hhc : (R.callee (-fr) (-160) 0).hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F' m → StackOff rS (R.callee (-fr) (-160) 0) m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isaLSE2} {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {I0 : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hq : q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) o) →
      ∀ m, F' m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) (hG0F : ∀ m, F' m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F' m0 → ∀ (s : State) c, DFrame (R.callee (-fr) (-160) 0) m0 s.st.1 →
      (c = q.c0 ∨ ∃ o, c = holdCtr (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs)
    (hF' : FStable (R.callee (-fr) (-160) 0) F')
    (hcode : Spike.Lib.A64.Alloc.Code (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) q exe endPc)
    {tp : UInt64}
    (hxa : ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-fr) (-160) 0) F'
          (Spike.Lib.A64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q l b w)
          s c →
        TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs).xa l b w s c)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hfr : fr % 16 = 0)
    (hlo : R.lo ≤ -fr + -160 - 48) (hkc : -fr + -160 < R.hi) {Pc : AS → Prop}
    (hleave : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R (-fr) (-160) 0 m0 m ∧ Abs R o m0 σC ∧ Pc σC)
    (hstub : ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0, (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q lbl R fr Pc).J σC c0 →
      Spike.Lib.A64.Abort.Disp.StubHW
        (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) p lbl (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) exe endPc
        (R.callee (-fr + -160) (-48) 0)
        (fun m => F m ∧ CKept R (-fr + -160) (-48) 0 m0 m ∧ Abs R ⟨-fr + -160, []⟩ m0 σC) c0) :
    ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt (Ab lab) a ab J' lbl lsize
        (Frag.at (fun s c => At exe endPc (R.callee (-fr) (-160) 0) F'
          (N (_root_.Executable.labels exe).label (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) q
            .n4) s c ∧ TP tp s) fs) := by
  intro J' hJ'
  rw [N_msOfAX (I' := IN ar L0 ls0 J')]
  exact allocHeld_seg (Jv := IN ar L0 ls0 J') hI hA hph habk hown hRc halc hloc hhic hlc hhc hsub hfit hFO hp
    (callOK_msOfAX hq) hra hraAb (by cases ab <;> exact hmem) (by cases ab <;> exact hno) hlt h64 hG0F
    (by cases ab <;> exact hP) hF' (code_msOfAX hcode) (hxa J' hJ') hF hR hal hfr hlo hkc hleave
    (hstub J' hJ')

omit [Kraken.Executable.ValidLayout exe] in
/-- **A held pair is not at a `ret`** (`pendA_of_selfN`'s `hnr`): at `n4`
the control is the call's with the counter held (`holdCtr`), whose term is
the allocation `let x = newBuf a τ in e` (`Call.OK.term`). -/
theorem allocHeld_nr {ms : MemSide isaLSE2} {lab' : Label → Int64} (hq : q.OK ms lab') {lab'' : Label → Int64}
    {s : State} {c : Ctl} (h : At exe endPc R F (N lab'' ms q .n4) s c) : ∀ a, c.term ≠ .ret a := by
  obtain ⟨-, -, -, -, -, -, -, o, rfl, -⟩ := h
  intro a he
  have ht : (holdCtr ms q.c0 o).term = q.c0.term := rfl
  rw [ht, hq.term] at he
  cases he

end Held

/-- info: 'Spike.Lib.LowerA64.N_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms N_msOfAX

/-- info: 'Spike.Lib.LowerA64.callOK_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms callOK_msOfAX

/-- info: 'Spike.Lib.LowerA64.code_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms code_msOfAX

/-- info: 'Spike.Lib.LowerA64.leaveOk_of_allocCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leaveOk_of_allocCtx

/-- info: 'Spike.Lib.LowerA64.AllocWT.noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocWT.noMsr

/-- info: 'Spike.Lib.LowerA64.AllocWT.tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocWT.tpXa

/-- info: 'Spike.Lib.LowerA64.code_tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms code_tpXa

/-- info: 'Spike.Lib.LowerA64.allocHeld_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocHeld_seg

/-- info: 'Spike.Lib.LowerA64.allocHeld_sg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocHeld_sg2

/-- info: 'Spike.Lib.LowerA64.allocHeld_nr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocHeld_nr

end Spike.Lib.LowerA64
