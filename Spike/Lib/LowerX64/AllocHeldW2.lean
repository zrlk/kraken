/-
**The counter add's held state carries its own segment** (x86-64; the twin
of `Spike/Lib/LowerA64/AllocHeldW2.lean`): from `scc_rt_alloc`'s node `c2`
after the counter's add (the held count, in the allocator's region at the
call), the levels' segment inside `W2` (`Sg2`) at every family containing
the starts `StartsN`, so the held pair is a self-segment start (`SelfN`,
`selfN_of`) and `pendA_of_selfN`'s `hQ`.

**No continuation past the return.** From `c2` the allocator does not reach
its caller at the held placement: the tail's only exit there is the heap
abort (`seg_allocW_tailA`); its return's row is the allocation (`Out.alloc`),
whose successor is in `xa`, i.e. a landing of `StartsN` at the next
placement, not a pair of this segment. So the segment is the tail
(`allocW2TX`, without the counter context), the abort exit left into the
caller's region (`at_leave`) and the heap abort path (`seg_jabort2W`), which
does not return.

**Not circular.** The segment asks `W2` and `msOfAX` at `IN … J'` (the tail
without the counter context), the allocation fragment through `J'`
containing `StartsN` (the landings), the abort path's obligations: no
`PendA`, no `AllocCtx` at the add, no full `allocW2`, and no held pair in
`J'`, so no held pair's segment asks another's.

Where x86-64 differs from AArch64: the add's successor is `c2` (AArch64's
`n4`); the allocator's region is `R.callee (-fr - 8) (-160) 8` (the caller's
frame of `fr` bytes, then the pushed return address), 8-aligned; the code is
from the layout (`InstOk`'s `lays`, `endOk`), so there is no
`code_msOfAX`; the heap abort's node keeps `%rbp`'s slot (`⟨-160,
[(.rbp, -8)]⟩`), forgotten (`Abs.weaken`) before `at_leave` (x86-64 has no
`at_leaveE`), so `HeldAb` is at `%rsp` `-fr - 8 + -160`; the dispatcher's
region is `[-24, 16)` below the pushed return address (`seg_jabort2W`); and
the no-return segment is `SegWS.liftS` with the empty exit dropped (no
`SegWS.liftS_noret` on this side).

- `N_msOfAX`: the allocator's nodes read no `xa`, so `msOfAX` at any two
  families gives the same nodes;
- `callOK_msOfAX`: a call's premises at any family;
- `HeldAb`: the tail's abort exit in the caller's region;
- `leaveOk_of_allocCtx`: `at_leave`'s frame premise from the call context;
- `allocHeld_seg`: the held pair's segment inside `W2` at a family `Jv`;
- `allocHeld_sg2`: as `Sg2` at every family containing `StartsN`, from a
  fixed family `I0`'s nodes;
- `allocHeld_nr`: a held pair is not at a `ret` (`pendA_of_selfN`'s `hnr`).
-/
import Spike.Lib.LowerX64.AllocTailW2
import Spike.Lib.X64AbortHeapS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun MemSide SegW SegWS Frag.at)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (BlkW NodeW At holdCtr DFrame FStable CKept Abs leave ND AS)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff TakeK)
open Spike.Lib.X64.Flow.NewBuf (AllocCtx)
open Spike.Lib.X64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Alloc (Call AllocWT N E AN fnL)
open Spike.Lib.X64.AllocG (allocPhOk allocAbOk)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.X64.KeepTP (TP tpXa)

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

/-- **The allocator's nodes read no `xa`**: under `tpXa` they are the same. -/
theorem N_tpXa {ms : MemSide isa} {t : UInt64} (lab : Label → Int64) (q : Call) (i : AN) :
    N lab (tpXa ms t) q i = N lab ms q i := by
  cases i <;> rfl

/-- **The allocator's exits read no `xa`**: under `tpXa` they are the same. -/
theorem E_tpXa {ms : MemSide isa} {t : UInt64} (lab : Label → Int64) (q : Call)
    (lbl : WeakMem.AllocLabel → Option Nat) (x : Spike.Lib.X64.Alloc.AX) :
    E lab (tpXa ms t) q lbl x = E lab ms q lbl x := by
  cases x <;> rfl

/-- The tail's states under `tpXa` (`allocW_tpXa`): its nodes read no `xa`. -/
theorem allocWT_tpXa {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {W : Spike.Lib.Frag isa} {K : State → State → Prop} {ms : MemSide isa} {t : UInt64} {q : Call}
    (h : AllocWT ms q W K exe endPc R F) : AllocWT (tpXa ms t) q W K exe endPc R F :=
  ⟨h.c2, h.j2, h.slow, h.j3, h.full, h.ok, h.f1, h.o1, h.f2, h.o2, h.s2, h.o3, h.f3, h.o4, h.f4, h.o5, h.f5,
    h.o6, h.f6, h.o7, h.f7, h.o8, h.hdr, h.o9, h.ret⟩

end Fam

/-! ## The abort exit in the caller's region -/

/-- **The tail's abort exit in the caller's region** `R` (the allocator's
region `R.callee (-fr - 8) (-160) 8`, the caller's frame of `fr` bytes and
the pushed return address): at `scc_rt_abort` with `%rsp` at
`-fr - 8 + -160`, the abstract state the caller's `σC` of `P` left
(`at_leave`'s node at `E … .abort`, `%rbp`'s slot forgotten). -/
def HeldAb (lab : Label → Int64) (ms : MemSide isa) (q : Call) (lbl : WeakMem.AllocLabel → Option Nat)
    (R : Region) (fr : Int) (P : AS → Prop) : ND :=
  ⟨(E lab ms q lbl .abort).pc, ⟨-fr - 8 + -160, []⟩, fun σ c => ∃ σx σC, (E lab ms q lbl .abort).J σx c ∧ P σC ∧
    σ = leave (R.callee (-fr - 8) (-160) 8) (-fr - 8) σC σx⟩

/-- **`at_leave`'s frame premise from the allocator's call context**: a
frame condition giving the caller's `F` and the call's context `AllocCtx`
gives the caller's cells kept outside the allocator's region and a caller's
state of the call node at the call's control `q.c0` (the entry's `c = q.c0`). -/
theorem leaveOk_of_allocCtx {F F' : MachineData → Prop} {ms : MemSide isa} {lab : Label → Int64} {R : Region}
    {fr : Int} {Jc : AS → Ctl → Prop} {q : Call} (h : ∀ m, F' m → F m ∧ AllocCtx ms lab R fr Jc q m) :
    ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R (-fr - 8) (-160) 8 m0 m ∧ Abs R o m0 σC ∧ Jc σC q.c0 := by
  intro m hm
  obtain ⟨hF, mC, σC, c, hA, hJ, he, hK⟩ := h m hm
  obtain rfl : c = q.c0 := he.1
  exact ⟨hF, mC, σC, _, hK, hA, hJ⟩

/-! ## The held pair's segment -/

section Held

variable {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F F' : MachineData → Prop} {q : Call} {a : Int64}

/-- **The counter add's held pair is one segment inside `W2`** at the family
`Jv`, the frames `fs`, into no pair: from `c2` in the allocator's region
`R.callee (-fr - 8) (-160) 8` at `F'` (`allocW2TX`'s premises there), the
tail to its heap abort alone (`seg_allocW_tailA`, the allocation fragment
`hxa`), left into the caller's region `R` at `F` (`Abs.weaken`, `at_leave`,
`hleave`), the heap abort path (`seg_jabort2W`, its obligations `hstub`),
which does not return (`SegWS.liftS`, the empty exit dropped). The held
pair at `fsBase = tp`: the tail runs under `tpXa` inside `NoSetFsW`
(`allocNoSys`, `AllocWT.impK`, `allocWT_tpXa`, `SegW.keepTPN`), so `hxa` is
asked at `fsBase = tp` only. See the module docstring: no `PendA`, no
counter context. -/
theorem allocHeld_seg {rS : Range} (hI : InstOk exe endPc cells lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {fr : Int}
    (hRc : (R.callee (-fr - 8) (-160) 8).OK) (hR8c : (R.callee (-fr - 8) (-160) 8).base.toNat % 8 = 0)
    (hloc : (R.callee (-fr - 8) (-160) 8).lo ≤ -160) (hhic : 8 ≤ (R.callee (-fr - 8) (-160) 8).hi)
    (hlc : (R.callee (-fr - 8) (-160) 8).lo % 8 = 0) (hhc : (R.callee (-fr - 8) (-160) 8).hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F' m → StackOff rS (R.callee (-fr - 8) (-160) 8) m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {Jv : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hq : q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab fnL).toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ m, F' m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) (hG0F : ∀ m, F' m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F' m0 → ∀ (s : State) c, DFrame (R.callee (-fr - 8) (-160) 8) m0 s.st.1 →
      (c = q.c0 ∨ ∃ o, c = holdCtr (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs)
    (hF' : FStable (R.callee (-fr - 8) (-160) 8) F') {tp : UInt64}
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc (R.callee (-fr - 8) (-160) 8) F'
        (Spike.Lib.X64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q l b w) s c →
      TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).xa l b w s c)
    (hF : FStable R F) (hR : R.OK) (hfr : fr % 8 = 0)
    (hlo : R.lo ≤ -fr - 8 + -160 - 32) (hkc : -fr - 8 + -160 + 8 ≤ R.hi) {Pc : AS → Prop}
    (hleave : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R (-fr - 8) (-160) 8 m0 m ∧ Abs R o m0 σC ∧ Pc σC)
    (hstub : ∀ m0 σC c0, (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q lbl R fr Pc).J σC c0 →
      Spike.Lib.X64.Abort.Disp.StubHW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) p lbl (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) exe endPc
        (R.callee (-fr - 8 + -160 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-fr - 8 + -160 - 8) (-24) 16 m0 m ∧ Abs R ⟨-fr - 8 + -160, []⟩ m0 σC) c0) :
    SegWS (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) (TakeK a rS) p lbl
      (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize)
      (Frag.at (fun s c => At exe endPc (R.callee (-fr - 8) (-160) 8) F'
        (N (_root_.Executable.labels exe).label (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q
          .c2) s c ∧ TP tp s) fs)
      (fun _ _ _ => False) := by
  have hW := allocW2TX (Dt := Dt) hI hA hph habk hown hRc hR8c hloc hhic hlc hhc hsub hfit hFO hp
    (fun _ _ => hq) hra hraAb hmem hno hlt h64 hG0F hP
  have hWN := AllocWT.impK hW (allocNoSys (ms := msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs)
      (q := q) (R := R.callee (-fr - 8) (-160) 8) (F := F') hI hA).tail
    (W := Spike.Lib.X64.Flow.NoSetFsW _ (TakeK a rS)) fun s c hw hk hns =>
      ⟨hw, fun hat => absurd hat (by rw [hns]; decide), hk⟩
  have hq' : q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs)
      (_root_.Executable.labels exe).label := by rw [hI.labOk]; exact hq
  have hK : (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs).K = some Scc.Sem.X64.abi := by
    cases ab <;> rfl
  have h1 := (Spike.Lib.X64.Flow.SegW.keepTPN (t := tp) hK
    (Spike.Lib.X64.Alloc.seg_allocW_tailA (p := p) (ms := tpXa _ tp) hI.lays hI.endOk hA hF' hRc hloc hhic
      (callOK_tpXa hq')
      (fun a h m hm => match h with
        | .inl h => hmem a (.inl (by rw [h]; cases ab <;> rfl)) m hm
        | .inr ⟨o, hle, he⟩ => hmem a (.inr ⟨o, by cases ab <;> exact hle, he⟩) m hm)
      (fun l b w s c hl hAt hT => hxa l b w s c hl hAt hT) (allocWT_tpXa hWN) .c2)).mono_post
    (fun s c h => by rw [E_tpXa] at h; exact h.1) |>.mono_pre fun s c h => by
      show _ ∧ _; rw [Spike.Lib.X64.Alloc.TN.an, N_tpXa]; exact h
  have h2 := Spike.Lib.X64.Abort.Disp.seg_jabort2W (W := fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab)
      lbl lsize s c fs) (K := TakeK a rS) (p := p) (lbl := lbl) (Q := fun _ _ => False)
    (nC := HeldAb (_root_.Executable.labels exe).label
      (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q lbl R fr Pc) rfl
    (fun σ c h => by
      obtain ⟨σx, σC, hJ, -, rfl⟩ := h
      exact hJ.1) hF hR hlo hkc (by show (-fr - 8 + -160) % 8 = 0; omega) hK hstub
  have h3 : SegW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) (TakeK a rS) p lbl
      (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs)
      (fun s c => At exe endPc (R.callee (-fr - 8) (-160) 8) F'
        (N (_root_.Executable.labels exe).label (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q
          .c2) s c ∧ TP tp s)
      (fun _ _ => False) := by
    refine (h1.mono_post fun s c h => ?_).seq h2
    obtain ⟨he, hn, hdc, hpc, σ, hA', hD, hJ⟩ := h
    exact Spike.Lib.X64.at_leave (P := Pc)
      (x := ⟨(E (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q lbl .abort).pc, ⟨-160, []⟩,
        (E (_root_.Executable.labels exe).label
          (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q lbl .abort).J⟩) rfl hleave
      ⟨he, hn, hdc, hpc, σ, Abs.weaken
        (show Spike.Lib.X64.SO.le ⟨-160, []⟩ ⟨-160, [(.rbp, -8)]⟩ = true by decide) hA', hD, hJ⟩
  exact (SegWS.liftS fs h3 (fun _ _ h => h)).mono_post fun _ _ _ h => h.1.elim

/-- **The counter add's held pair carries its own segment at every family
containing the starts** (`pendA_of_selfN`'s `hQ`): at each family `J'`
containing `StartsN … S0 Es`, `allocHeld_seg` at `IN … J'` is the levels'
segment `Sg2 … J' lbl lsize` from the held pairs at `c2`, the nodes read at
a fixed family `I0` (`N_msOfAX`), so the entry does not depend on `J'`. The
family-free premises are asked at `I0`; the allocation fragment (`hxa`, from
the landings `StartsN`) and the abort path's obligations (`hstub`) at each
`J'`. No held pair is asked in `J'` (the module docstring). -/
theorem allocHeld_sg2 {rS : Range} (hI : InstOk exe endPc cells lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {fr : Int}
    (hRc : (R.callee (-fr - 8) (-160) 8).OK) (hR8c : (R.callee (-fr - 8) (-160) 8).base.toNat % 8 = 0)
    (hloc : (R.callee (-fr - 8) (-160) 8).lo ≤ -160) (hhic : 8 ≤ (R.callee (-fr - 8) (-160) 8).hi)
    (hlc : (R.callee (-fr - 8) (-160) 8).lo % 8 = 0) (hhc : (R.callee (-fr - 8) (-160) 8).hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F' m → StackOff rS (R.callee (-fr - 8) (-160) 8) m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isa} {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {I0 : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hq : q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab fnL).toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) o) →
      ∀ m, F' m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) (hG0F : ∀ m, F' m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F' m0 → ∀ (s : State) c, DFrame (R.callee (-fr - 8) (-160) 8) m0 s.st.1 →
      (c = q.c0 ∨ ∃ o, c = holdCtr (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs)
    (hF' : FStable (R.callee (-fr - 8) (-160) 8) F')
    {tp : UInt64}
    (hxa : ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-fr - 8) (-160) 8) F'
          (Spike.Lib.X64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q l b w)
          s c →
        TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs).xa l b w s c)
    (hF : FStable R F) (hR : R.OK) (hfr : fr % 8 = 0)
    (hlo : R.lo ≤ -fr - 8 + -160 - 32) (hkc : -fr - 8 + -160 + 8 ≤ R.hi) {Pc : AS → Prop}
    (hleave : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R (-fr - 8) (-160) 8 m0 m ∧ Abs R o m0 σC ∧ Pc σC)
    (hstub : ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0, (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q lbl R fr Pc).J σC c0 →
      Spike.Lib.X64.Abort.Disp.StubHW
        (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) p lbl (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) exe endPc
        (R.callee (-fr - 8 + -160 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-fr - 8 + -160 - 8) (-24) 16 m0 m ∧ Abs R ⟨-fr - 8 + -160, []⟩ m0 σC) c0) :
    ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt (Ab lab) a ab J' lbl lsize
        (Frag.at (fun s c => At exe endPc (R.callee (-fr - 8) (-160) 8) F'
          (N (_root_.Executable.labels exe).label (msOfAX Λ μ p rd G (fun s _ => own s) ar I0 ab lbl lsize fs) q
            .c2) s c ∧ TP tp s) fs) := by
  intro J' hJ'
  rw [N_msOfAX (I' := IN ar L0 ls0 J')]
  exact allocHeld_seg (Jv := IN ar L0 ls0 J') hI hA hph habk hown hRc hR8c hloc hhic hlc hhc hsub hfit hFO hp
    (callOK_msOfAX hq) hra hraAb (by cases ab <;> exact hmem) (by cases ab <;> exact hno) hlt h64 hG0F
    (by cases ab <;> exact hP) hF' (hxa J' hJ') hF hR hfr hlo hkc hleave (hstub J' hJ')

omit [Executable.ValidLayout exe] in
/-- **A held pair is not at a `ret`** (`pendA_of_selfN`'s `hnr`): at `c2`
the control is the call's with the counter held (`holdCtr`), whose term is
the allocation `let x = newBuf a τ in e` (`Call.OK.term`). -/
theorem allocHeld_nr {ms : MemSide isa} {lab' : Label → Int64} (hq : q.OK ms lab') {lab'' : Label → Int64}
    {s : State} {c : Ctl} (h : At exe endPc R F (N lab'' ms q .c2) s c) : ∀ a, c.term ≠ .ret a := by
  obtain ⟨-, -, -, -, -, -, -, o, rfl, -⟩ := h
  intro a he
  have ht : (holdCtr ms q.c0 o).term = q.c0.term := rfl
  rw [ht, hq.term] at he
  cases he

end Held

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.N_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms N_msOfAX

/-- info: 'Spike.Lib.LowerX64.callOK_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms callOK_msOfAX

/-- info: 'Spike.Lib.LowerX64.leaveOk_of_allocCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms leaveOk_of_allocCtx

/-- info: 'Spike.Lib.LowerX64.allocHeld_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocHeld_seg

/-- info: 'Spike.Lib.LowerX64.allocHeld_sg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocHeld_sg2

/-- info: 'Spike.Lib.LowerX64.allocHeld_nr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocHeld_nr

/-- info: 'Spike.Lib.LowerX64.allocWT_tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocWT_tpXa

end Spike.Lib.LowerX64
