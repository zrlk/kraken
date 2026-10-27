/-
**`scc_rt_alloc`'s tail inside `W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/AllocTailW2.lean`): the allocator's nodes past the
counter's add (`AllocWT`, `Spike/Lib/X64AllocTail.lean`) inside `W2` with
no counter context: no tail node writes the counter word (`allocNoCtrT`),
so `W2`'s write obligation needs no `CtrRow` there. With
`seg_allocW_tail`, the tail from the add's landing at `c2` is a segment
inside `W2` at any family, the first part of the counter add's landing's
own segment (`SelfN`).

- `AllocWT.imp`: `AllocWT` from two;
- `allocNoCtrT`: no tail node writes the counter word (the header's store
  is in the heap, above the counter);
- `allocW2T`: the tail's nodes inside `W2` at the frames `fs`, without
  `allocW2`'s `hctx`;
- `allocW2TX`: `allocW2T` at the rows' memory side `msOfAX … ab`.

Where x86-64 differs from AArch64: the region premises are the allocator's
frame's with the return address (`hR8`, `R.lo ≤ -160`, `8 ≤ R.hi`), the
return address's phase at `fnL`.
-/
import Spike.Lib.LowerX64.AllocFnW2
import Spike.Lib.X64AllocTail

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun MemSide)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (BlkW NodeW At ND holdCtr DFrame)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Alloc (Call AllocW AllocWT N iRet fnL bC2_ok bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok
  bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)
open Spike.Lib.X64.AllocG (allocIn_spec allocSt allocAb allocArena allocPc allocPhOk allocAbOk blkW_noWr
  nodeW_noWr_si nodeW_noWr_fi nodeW_wr_st hdr_addr)

section Imp

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isa}
  {q : Call} {W W₁ W₂ : Spike.Lib.Frag isa} {K : State → State → Prop}

/-- **The tail inside `W`** from two (`NodeW.imp`, `BlkW.imp`). -/
theorem AllocWT.imp (h1 : AllocWT ms q W₁ K exe endPc R F) (h2 : AllocWT ms q W₂ (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W₁ s c → W₂ s c → W s c) : AllocWT ms q W K exe endPc R F :=
  ⟨Spike.Lib.X64.AllocG.BlkW.imp h1.c2 h2.c2 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.j2 h2.j2 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.slow h2.slow hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.j3 h2.j3 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.full h2.full hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.ok h2.ok hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.f1 h2.f1 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o1 h2.o1 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.f2 h2.f2 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o2 h2.o2 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.s2 h2.s2 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o3 h2.o3 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.f3 h2.f3 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o4 h2.o4 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.f4 h2.f4 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o5 h2.o5 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.f5 h2.f5 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o6 h2.o6 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.f6 h2.f6 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o7 h2.o7 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.f7 h2.f7 hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o8 h2.o8 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.hdr h2.hdr hw,
    Spike.Lib.X64.AllocG.BlkW.imp h1.o9 h2.o9 hw,
    Spike.Lib.X64.AllocG.NodeW.imp h1.ret h2.ret hw⟩

/-- **A node inside `W`** from one inside `W₁` not moved by `K` and one
inside `W₂`, `W₁ ∧ W₂` with `K` not moving the state inside `W`. -/
theorem NodeW.impK {n : ND} (h1 : NodeW W₁ K exe endPc R F n) (h2 : NodeW W₂ (fun _ _ => False) exe endPc R F n)
    (hw : ∀ s c, W₁ s c → (∀ s', ¬ K s s') → W₂ s c → W s c) : NodeW W K exe endPc R F n := fun s c hA =>
  ⟨hw s c (h1 s c hA).1 (h1 s c hA).2 (h2 s c hA).1, (h1 s c hA).2⟩

/-- **A block node inside `W`** from one inside `W₁` not moved by `K` and
one inside `W₂`, `W₁ ∧ W₂` with `K` not moving the state inside `W`. -/
theorem BlkW.impK {n : ND} {blk : List (Directive × Nat)} (h1 : BlkW W₁ K exe endPc R F n blk)
    (h2 : BlkW W₂ (fun _ _ => False) exe endPc R F n blk) (hw : ∀ s c, W₁ s c → (∀ s', ¬ K s s') → W₂ s c → W s c) :
    BlkW W K exe endPc R F n blk := fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
  ⟨hw _ c (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1 (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2
    (h2 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1, (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2⟩

/-- **The tail inside `W`** from two, `K`'s standstill passed to `hw`
(`NodeW.impK`, `BlkW.impK`). -/
theorem AllocWT.impK (h1 : AllocWT ms q W₁ K exe endPc R F) (h2 : AllocWT ms q W₂ (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W₁ s c → (∀ s', ¬ K s s') → W₂ s c → W s c) : AllocWT ms q W K exe endPc R F :=
  ⟨    BlkW.impK h1.c2 h2.c2 hw,
    BlkW.impK h1.j2 h2.j2 hw,
    BlkW.impK h1.slow h2.slow hw,
    BlkW.impK h1.j3 h2.j3 hw,
    BlkW.impK h1.full h2.full hw,
    BlkW.impK h1.ok h2.ok hw,
    NodeW.impK h1.f1 h2.f1 hw,
    BlkW.impK h1.o1 h2.o1 hw,
    NodeW.impK h1.f2 h2.f2 hw,
    BlkW.impK h1.o2 h2.o2 hw,
    NodeW.impK h1.s2 h2.s2 hw,
    BlkW.impK h1.o3 h2.o3 hw,
    NodeW.impK h1.f3 h2.f3 hw,
    BlkW.impK h1.o4 h2.o4 hw,
    NodeW.impK h1.f4 h2.f4 hw,
    BlkW.impK h1.o5 h2.o5 hw,
    NodeW.impK h1.f5 h2.f5 hw,
    BlkW.impK h1.o6 h2.o6 hw,
    NodeW.impK h1.f6 h2.f6 hw,
    BlkW.impK h1.o7 h2.o7 hw,
    NodeW.impK h1.f7 h2.f7 hw,
    BlkW.impK h1.o8 h2.o8 hw,
    NodeW.impK h1.hdr h2.hdr hw,
    BlkW.impK h1.o9 h2.o9 hw,
    NodeW.impK h1.ret h2.ret hw⟩

end Imp

section Tail

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

set_option hygiene false in
/-- A block of the tail writing nothing. -/
local macro "tblk " hb:term:max ok:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.AllocG.BlkW.imp (blkW_noWr hI $hb (by pc_tac) $ok hR (by omega) (by omega))
    Spike.Lib.X64.BlkW.triv fun _ _ h _ hW => h _ hW)

set_option hygiene false in
/-- A single instruction of the tail without an event. -/
local macro "tsi " hb:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.AllocG.NodeW.imp (nodeW_noWr_si hI $hb rfl (by pc_tac))
    Spike.Lib.X64.NodeW.triv fun _ _ h _ hW => h _ hW)

set_option hygiene false in
/-- An instruction of the tail with undefined flags. -/
local macro "tfi " hb:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.AllocG.NodeW.imp (nodeW_noWr_fi hI $hb rfl (by pc_tac))
    Spike.Lib.X64.NodeW.triv fun _ _ h _ hW => h _ hW)

/-- **No node of the allocator's tail writes the counter word**, for a
memory side with the arena's base (`hheap`), the counter below the heap
(`hlt`, `h64`), every header the code may store unmapped in private memory
(`hmem`, `hq`): every tail instruction writes nothing but the header's
store, whose word is in the heap (`hdr_addr`), above the counter. -/
theorem allocNoCtrT (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) {ar : Arena}
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms lab)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocWT ms q (fun s _ => ¬ WrAt s ar.ctrLoc) (fun _ _ => False) exe endPc R F := by
  obtain ⟨-, -, -, -, -, -, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hI.labOk]
  · tblk h6 bC2_ok
  · tblk h7 bJ2_ok
  · tblk h8 bSlow_ok
  · tblk h9 bJ3_ok
  · tblk h10 bFull_ok
  · tblk h11 bO0_ok
  · tfi h12
  · tblk h13 bO1_ok
  · tfi h14
  · tblk h15 bO2_ok
  · tsi h16
  · tblk h17 bO3_ok
  · tfi h18
  · tblk h19 bO4_ok
  · tfi h20
  · tblk h21 bO5_ok
  · tfi h22
  · tblk h23 bO6_ok
  · tfi h24
  · tblk h25 bO7_ok
  · tfi h26
  · tblk h27 bO8_ok
  · refine Spike.Lib.X64.AllocG.NodeW.imp (nodeW_wr_st hI (b := .rcx) (k := 0) (r := .rax) h28 rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
      exact hmem _ ⟨o.toNat, hle, hdr_addr (hq m hF) hle hn28 hcx⟩ m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -⟩, -, -, hcx⟩, hF, hL⟩ - hW
      have hq' := hq _ hF
      have ha := congrArg (fun L : Loc => L.addr.toNat) (hL _ hW)
      simp only at ha
      rw [hdr_addr hq' hle hn28 hcx, Spike.Lib.X64.Alloc.Call.hdrAt, hheap] at ha
      have : ar.ctrLoc.addr.toNat = ar.ctr := by
        simp only [Arena.ctrLoc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
      omega
  · tblk h29 bO9_ok
  · exact Spike.Lib.X64.AllocG.NodeW.imp (Spike.Lib.LowerX64.BlkW.nodeW (blkW_noWr hI (blk := [(iRet.toDir, 1)])
      (lo := -160) (hi := 8) h30 rfl
      (show Spike.Lib.X64.okBlk (-160) 8 Spike.Lib.X64.Alloc.oE [(iRet.toDir, 1)] = true by decide) hR
      (by omega) (by omega)) (List.cons_ne_nil _ _)) Spike.Lib.X64.NodeW.triv fun _ _ h _ hW => h _ hW

/-- **The allocator's tail inside `W2`** at the frames `fs`, any write tail
`Dt`, none moved by `K`: `allocW2`'s premises without its counter context
`hctx`, the tail writing no counter word (`allocNoCtrT`). -/
theorem allocW2T (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OK ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab fnL).toBitVec.toNat)
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
  have hSt := (allocSt (Λ := Λ) (rS := rS) hI hA hph hown hR hR8 hlo hhi hl hh hsub hfit hFO hq hra hmp hmem
    hno).tail
  have hAb := (allocAb hI hA hph habk hR hlo hhi hq hra hraAb hmem).tail
  have hAr := (allocArena (lbl := lbl) (p := p) hI hA hR hlo hhi hq hmem hctr hheap hoff).tail
  have hCt := allocNoCtrT hI hA hR hlo hhi hq (fun a h m hm => hmem a (.inr h) m hm) hheap hlt h64
  have hPl := (Spike.Lib.X64SetupPlaced.allocPlacedS (exe := exe) (endPc := endPc) (fs := fs) hP).tail
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
theorem allocW2TX (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {Jv : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hq : ∀ m, F m → q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar Jv ab lbl lsize fs) lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab fnL).toBitVec.toNat)
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
  refine allocW2T hI hA hph habk hown hR hR8 hlo hhi hl hh hsub hfit hFO hq hra hraAb (fun L h => msOfAX_mp h)
    ?_ ?_ hctr hheap (fun k τ => by rw [hoff]) hlt h64 hp hG0F hP
  · rw [hctr, hunits, hcells]; exact hmem
  · rw [hctr, hunits, hcells]; exact hno

end Tail

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.AllocWT.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.AllocWT.imp

/-- info: 'Spike.Lib.LowerX64.allocNoCtrT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocNoCtrT

/-- info: 'Spike.Lib.LowerX64.allocW2T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2T

/-- info: 'Spike.Lib.LowerX64.allocW2TX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2TX

/-- info: 'Spike.Lib.LowerX64.AllocWT.impK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.AllocWT.impK
