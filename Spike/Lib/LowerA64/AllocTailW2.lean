/-
**`scc_rt_alloc`'s tail inside `W2`** (AArch64): the allocator's nodes
past the counter's add (`AllocWT`, `Spike/Lib/A64AllocTail.lean`) inside
`W2` with no counter context: no tail node writes the counter word
(`allocNoCtrT`), so `W2`'s write obligation needs no `CtrRow` there. With
`seg_allocW_tail`, the tail from the add's landing at `n4` is a segment
inside `W2` at any family, the first part of the counter add's landing's
own segment (`SelfN`).

- `AllocWT.imp`: `AllocWT` from two;
- `allocNoCtrT`: no tail node writes the counter word (the header's store
  is in the heap, above the counter);
- `allocW2T`: the tail's nodes inside `W2` at the frames `fs`, without
  `allocW2`'s `hctx`;
- `allocW2TX`: `allocW2T` at the rows' memory side `msOfAX … ab`.
-/
import Spike.Lib.LowerA64.AllocFnW2
import Spike.Lib.A64AllocTail

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun MemSide)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (BlkW NodeW At holdCtr DFrame)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.A64.Alloc (Call AllocW AllocWT N iAdrpH iAddH iHdr iRet b4 b5 b6 b7 b9 b11 b12 b13 b4_ok b5_ok
  b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)
open Spike.Lib.A64.AllocG (allocIn_spec allocSt allocAb allocArena allocPc allocPhOk allocAbOk blkW_noWr
  nodeW_noWr_si nodeW_wr_st hdr_addr)

section Imp

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2}
  {q : Call} {W W₁ W₂ : Spike.Lib.Frag isaLSE2} {K : State → State → Prop}

/-- **The tail inside `W`** from two (`NodeW.imp`, `BlkW.imp`). -/
theorem AllocWT.imp (h1 : AllocWT ms q W₁ K exe endPc R F) (h2 : AllocWT ms q W₂ (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W₁ s c → W₂ s c → W s c) : AllocWT ms q W K exe endPc R F :=
  ⟨Spike.Lib.A64.AllocG.BlkW.imp h1.n4 h2.n4 hw, Spike.Lib.A64.AllocG.BlkW.imp h1.n5 h2.n5 hw,
    Spike.Lib.A64.AllocG.BlkW.imp h1.slow h2.slow hw, Spike.Lib.A64.AllocG.BlkW.imp h1.n7 h2.n7 hw,
    Spike.Lib.A64.AllocG.BlkW.imp h1.full h2.full hw, Spike.Lib.A64.AllocG.BlkW.imp h1.ok h2.ok hw,
    Spike.Lib.A64.AllocG.NodeW.imp h1.ok1 h2.ok1 hw, Spike.Lib.A64.AllocG.NodeW.imp h1.ok2 h2.ok2 hw,
    Spike.Lib.A64.AllocG.BlkW.imp h1.n12 h2.n12 hw, Spike.Lib.A64.AllocG.NodeW.imp h1.hdr h2.hdr hw,
    Spike.Lib.A64.AllocG.BlkW.imp h1.n13 h2.n13 hw, Spike.Lib.A64.AllocG.NodeW.imp h1.ret h2.ret hw⟩

end Imp

section Tail

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isaLSE2} {q : Call}

set_option hygiene false in
/-- A block of the tail writing nothing. -/
local macro "tblk " hb:term:max ok:term:max : tactic =>
  `(tactic| exact Spike.Lib.A64.AllocG.BlkW.imp (blkW_noWr hI $hb (by pc_tac) $ok hR hal (by omega) (by omega))
    Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ hW => h _ hW)

set_option hygiene false in
/-- A single instruction of the tail without an event. -/
local macro "tsi " hb:term:max : tactic =>
  `(tactic| exact Spike.Lib.A64.AllocG.NodeW.imp (nodeW_noWr_si hI $hb rfl (by pc_tac))
    Spike.Lib.A64.Flow.NodeW.triv fun _ _ h _ hW => h _ hW)

/-- **No node of the allocator's tail writes the counter word**, for a
memory side with the arena's base (`hheap`), the counter below the heap
(`hlt`, `h64`), every header the code may store unmapped in private memory
(`hmem`, `hq`): every tail instruction writes nothing but the header's
store, whose word is in the heap (`hdr_addr`), above the counter. -/
theorem allocNoCtrT (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) {ar : Arena}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms lab)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocWT ms q (fun s _ => ¬ WrAt s ar.ctrLoc) (fun _ _ => False) exe endPc R F := by
  obtain ⟨-, -, -, -, -, -, -, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · tblk h7 b4_ok
  · tblk h8 b5_ok
  · tblk h9 b6_ok
  · tblk h10 b7_ok
  · tblk h11 b9_ok
  · tblk h12 b11_ok
  · tsi h13
  · tsi h14
  · tblk h15 b12_ok
  · refine Spike.Lib.A64.AllocG.NodeW.imp (nodeW_wr_st hI (t := .X9) (b := .X10) (i := 0) h16 rfl (by pc_tac)
      fun σ c m hJ hF => ?_) Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, h10⟩ := hJ
      exact hmem _ ⟨o.toNat, hle, hdr_addr (hq m hF) hle hn28 h10⟩ m hF
    · rintro s c ⟨σ, ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, h10⟩, hF, hL⟩ - hW
      have hA' := hdr_addr (hq _ hF) hle hn28 h10
      have he := congrArg (fun L : Loc => L.addr.toNat) (hL _ hW)
      simp only [Arena.ctrLoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at he
      rw [hA', Spike.Lib.A64.Alloc.Call.hdrAt, hheap] at he
      omega
  · tblk h17 b13_ok
  · exact Spike.Lib.A64.AllocG.NodeW.imp (Spike.Lib.LowerA64.BlkW.nodeW (blkW_noWr hI (blk := [iRet.toDir])
      (lo := -160) (hi := 0) h18 (by pc_tac) (by dsimp only [N]; decide) hR hal (by omega) (by omega))
      (List.cons_ne_nil _ _)) Spike.Lib.A64.Flow.NodeW.triv fun _ _ h _ hW => h _ hW

/-- **The allocator's tail inside `W2`** at the frames `fs`, any write tail
`Dt`, none moved by `K`: `allocW2`'s premises without its counter context
`hctx`, the tail writing no counter word (`allocNoCtrT`). -/
theorem allocW2T (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OK ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    {ar : Arena} (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {Jv : InvS}
    {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
    (hG0F : ∀ m, F m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F m0 → ∀ (s : State) c, DFrame R m0 s.st.1 → (c = q.c0 ∨ ∃ o, c = holdCtr ms q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs) :
    AllocWT ms q (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F := by
  have hSt := (allocSt (Λ := Λ) (rS := rS) hI hA hph hown hR hal hlo hhi hl hh hsub hfit hFO hq hra hmp hmem
    hno).tail
  have hAb := (allocAb hI hA hph habk hR hal hlo hhi hq hra hraAb hmem).tail
  have hAr := (allocArena (lbl := lbl) (p := p) hI hA hR hal hlo hhi hq hmem hctr hheap hoff).tail
  have hCt := allocNoCtrT hI hA hR hal hlo hhi hq (fun a h m hm => hmem a (.inr h) m hm) hheap hlt h64
  have hPl := (Spike.Lib.A64SetupPlaced.allocPlacedS (exe := exe) (endPc := endPc) (fs := fs) hP).tail
  have hPc := (allocPc (ms := ms) (q := q) (R := R) (F := F) hI hph).tail
  have hNs := (allocNoSys (ms := ms) (q := q) (R := R) (F := F) hI hA).tail
  have hCl := (allocCtl (exe := exe) (endPc := endPc) (R := R) (p := p)
    (fun m h => by rw [hI.labOk]; exact hq m h) hG0F).tail
  refine AllocWT.imp (AllocWT.imp (AllocWT.imp (AllocWT.imp (AllocWT.imp (AllocWT.imp
    (AllocWT.imp hSt hAb fun _ _ => And.intro) hAr fun _ _ => And.intro) hCt fun _ _ => And.intro)
    hPl fun _ _ => And.intro) hPc fun _ _ => And.intro) hNs fun _ _ => And.intro) hCl ?_
  rintro s c ⟨⟨⟨⟨⟨⟨hst, hab⟩, har⟩, hct⟩, hpl⟩, hpc⟩, hns⟩ ⟨hnr, hf, hrun⟩
  refine w2_of hp hf (hst.dt_mono fun _ h => h.elim) hab hnr (.of_placedS hpl) (fun c' fs' hr _ => ?_)
    (abortOkA_of_ne (hI.off s hpc).1.noAbort) (fun h => absurd h (by rw [hns]; decide))
  obtain ⟨rfl, rfl⟩ := hrun c' fs' hr
  exact ⟨fun L hL => (Classical.em (L = ar.ctrLoc)).elim .inl fun hne => har _ _ _ hr L hL hne lsize,
    fun hW => (hct hW).elim⟩

/-- **`allocW2T` at the rows' memory side** `msOfAX … ab` (as `allocW2X`,
`msOfAX_fields`, `msOfAX_mp`), with no counter context. -/
theorem allocW2TX (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {Jv : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hq : ∀ m, F m → q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) (hG0F : ∀ m, F m → FrOk2 q.c0 fs)
    (hP : ∀ m0, F m0 → ∀ (s : State) c, DFrame R m0 s.st.1 →
      (c = q.c0 ∨ ∃ o, c = holdCtr (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q.c0 o) →
      Placed Λ lbl s c ∧ FramesPlaced Λ lbl s fs) :
    AllocWT (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) q
      (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F := by
  obtain ⟨-, -, -, -, hheap, hctr, hunits, hoff, hcells, -⟩ :=
    msOfAX_fields (Λ := Λ) (μ := μ) (p := p) (rd := rd) (G := G) (own := fun s _ => own s) (ar := ar) (I := Jv)
      (lbl := lbl) (lsize := lsize) (fs := fs) ab
  refine allocW2T hI hA hph habk hown hR hal hlo hhi hl hh hsub hfit hFO hq hra hraAb (fun L h => msOfAX_mp h)
    ?_ ?_ hctr hheap (fun k τ => by rw [hoff]) hlt h64 hp hG0F hP
  · rw [hctr, hunits, hcells]; exact hmem
  · rw [hctr, hunits, hcells]; exact hno

end Tail

/-- info: 'Spike.Lib.LowerA64.AllocWT.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocWT.imp

/-- info: 'Spike.Lib.LowerA64.allocNoCtrT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocNoCtrT

/-- info: 'Spike.Lib.LowerA64.allocW2T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW2T

/-- info: 'Spike.Lib.LowerA64.allocW2TX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW2TX

end Spike.Lib.LowerA64
