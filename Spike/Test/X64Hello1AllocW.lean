/-
**`scc_rt_alloc`'s states at `hello1.x`'s instance** (x86-64): the
allocator's node obligations (`AllocW`, `Spike/Lib/X64Alloc.lean`) inside
the state's facts (`SFactsSt`) at any control, from `Wr` at the source
start's control (`dumN`, `BlkW.st`, `NodeW.st`,
`Spike/Test/X64Hello1W0N.lean`). The twin of
`Spike/Test/A64Hello1AllocW.lean`.

- `nodeW_si_postA`: a single instruction without an event after the take,
  in a region whose frame condition gives the stack range off it.
- `nodeW_st_postA`, `nodeW_xadd_postA`: a store and a `lock xadd` of an
  unowned word after the take, the word by the abstract state (the
  header's address is the held count's), mapped, unmapped in private memory
  and owned at no phase under the frame condition (AArch64's
  `nodeW_ldop_postA`).
- `BlkW.nodeW`: a node's states inside `W` from its block's (the first).
- `allocSt`: every node of `scc_rt_alloc` for a call `q` returning to
  `wc_rodata`'s `.x13`, in a region of the allocator's frame whose frame
  condition gives the stack range off it, the call's premises (`Call.OK`)
  and the counter and headers unmapped in private memory.
-/
import Spike.Test.X64Hello1W0N

namespace Spike.Test.X64Hello1W0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (FragS Frag MemSide Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW At ND AS SI FI bAddr xaddDir stDir mB eaddr_mB cellOff arun)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk nodeW_postO nodeW_fi_postO)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt after exec_store_agrees exec_xaddG_agrees eaddr)
open Spike.Lib.X64ConsumerA (SFactsSt)
open Spike.Lib.X64.Flow.Hello1.Inst
open SccCode (hello1Λ hello1Cells)

/-! ## A node from its block; a store and a `lock xadd` of an unowned word after the take -/

section Node

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node's states inside `W`**: the first of a block's. -/
theorem BlkW.nodeW {W : Frag isa} {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hne : blk ≠ []) : NodeW W K exe endPc R F n := by
  rintro s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩
  have hk : 0 < blk.length := List.length_pos_iff.mpr hne
  have := h s σ c he hn hd hp hA hF hJ 0 hk s.st.1 hA (Spike.Lib.X64.DFrame.refl _ _)
  have h0 : n.pc + Int64.ofNat (cellOff blk 0) = s.st.2 := by
    rw [hp]; exact Spike.Lib.X64.Flow.ofNat_zero' _
  rw [h0] at this
  exact this

/-- **A node at a single instruction without an event** (`SI`) after the
take, in a region whose frame condition gives the words of `rS` off it
(`hFO`), its next pc in its phase. -/
theorem nodeW_si_postA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {si : SI} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(si.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc hph) hO

/-- **A node at a store** `movq %r, k(%b)` after the take, in a region
whose frame condition gives the words of `rS` off it (`hFO`), its next pc
in its phase: the word at the abstract state's address mapped, unmapped in
private memory and owned at no phase (`ha`). -/
theorem nodeW_st_postA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64}
    {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨bAddr σ.regs b k, 8⟩ = true ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧ ∀ j w, (⟨bAddr σ.regs b k, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
    have hex := exec_store_agrees hc ha' hun (Spike.Lib.X64.agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) hmw
      (Spike.Lib.X64.Rt.next_same hI hpc hph _).2
      (.inl ⟨(Spike.Lib.X64.Rt.next_same hI hpc hph _).1, fun w h => by
        rw [Spike.Lib.X64.Rt.own_at hown hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown' htk hO

/-- **A node at an unowned word's `lock xaddq %r, k(%b)`** after the take,
as `nodeW_st_postA`: every leaf owns what the state owns, the word written
owned at no phase. -/
theorem nodeW_xadd_postA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64}
    {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(xaddDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨bAddr σ.regs b k, 8⟩ = true ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧ ∀ j w, (⟨bAddr σ.regs b k, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
    have hex := exec_xaddG_agrees (w := .W64) hc ha' hun (Spike.Lib.X64.agrees_of_decls hdc _ _)
    refine sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex (fun h => ?_)
      (.inl ⟨fun v _ => ⟨fun _ _ => trivial, (Spike.Lib.X64.Rt.next_same hI hpc hph _).1⟩,
        ⟨fun _ _ _ w h => by rw [Spike.Lib.X64.Rt.own_at hown hpc] at h; exact hno _ w h, fun _ => trivial⟩⟩)
      (fun v _ => ⟨fun _ _ => trivial, (Spike.Lib.X64.Rt.next_same hI hpc hph _).2⟩) hO
    cases h with
    | rmw h => rw [hmw] at h; cases h
    | rmwRet _ h => cases h

end Node

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL entryL cntL slowL fullL okL bPro bChk bJ1
  bC1 bC2 bJ2 bSlow bJ3 bFull bO0 bO1 bO2 bO3 bO4 bO5 bO6 bO7 bO8 bO9 bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok bJ2_ok
  bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Test.X64Hello1RtW (hello1_instOk)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {rS : Range} {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc` after the take, no `ret`, no dead target, at
the source start's control. -/
local macro "ablk " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact BlkW.st (Spike.Lib.X64.Rt.blkW_postO hello1_instOk (l := $l) (off := $k)
    (dead := fun _ => false) (ra := 0) (by decide +kernel) (by first | rfl | exact Spike.Lib.X64.Flow.ofNat_zero' _)
    $ok hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0)
    (by rw [Spike.Test.X64Hello1RtW.labT_eq_labX]; decide +kernel)
    (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "asi " si:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact NodeW.st (nodeW_si_postA hello1_instOk (si := $si) (z := $z) (l := $l) (off := $k)
    (p := labT $l + Int64.ofNat $k) (by decide +kernel) rfl
    (by first | rfl | exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm) (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by decide +kernel) (by decide +kernel) hR hR8 hl hh hsub hFO))

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "afi " fi:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact NodeW.st (nodeW_fi_postO hello1_instOk (fi := $fi) (z := $z) (l := $l) (off := $k)
    (p := labT $l + Int64.ofNat $k) (by decide +kernel) rfl rfl
    (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by decide +kernel) (by decide +kernel) hR hR8 hl hh hsub hFO))

/-- **`scc_rt_alloc`'s states carry the state's facts** at any control, none
moved by the take, for a call `q` returning to `wc_rodata`'s `.x13`
(`hra`), in a region of the allocator's frame (8-aligned) whose frame
condition gives the stack range off it (`hFO`) and the call's premises
(`hq`), the counter and every header the code may store unmapped in private
memory (`hmem`), owned at no phase (`hno`), the memory side's writable
words mapped (`hmp`). -/
theorem allocSt (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub hello1Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".Lwc_rodata.x13").toBitVec)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 hello1Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    AllocW ms q (fun s _ => SFactsSt hello1Λ μ0 own rS Tk s) (Kr rS) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  · ablk fnL 0 bPro_ok
  · ablk entryL 0 bChk_ok
  · ablk entryL 16 bJ1_ok
  · asi iCtr 7 cntL 0
  · ablk cntL 7 bC1_ok
  · refine NodeW.st (nodeW_xadd_postA hello1_instOk (fun _ => rfl) (b := .rcx) (k := 0) (r := .rax) (z := 5)
      (l := cntL) (off := 19) (p := labT cntL + Int64.ofNat 19) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by decide +kernel) (by decide +kernel) hR hR8 hl hh hsub hFO
      fun σ c m hJ hF => ?_)
    obtain ⟨-, c, -, hcx, -⟩ := hJ
    have hq' := hq m hF
    rw [hello1_labT] at hq'
    have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
      rw [← hq'.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
    rw [hb]
    exact ⟨hmp _ hq'.mp, hmem _ (.inl rfl) m hF, hno _ (.inl rfl)⟩
  · ablk cntL 24 bC2_ok
  · ablk cntL 59 bJ2_ok
  · ablk slowL 0 bSlow_ok
  · ablk slowL 16 bJ3_ok
  · ablk fullL 0 bFull_ok
  · ablk okL 0 bO0_ok
  · afi (.shr_cl .rax) 3 okL 11
  · ablk okL 14 bO1_ok
  · afi (.and_rr .rax .rcx) 3 okL 29
  · ablk okL 32 bO2_ok
  · asi iHeap 7 okL 36
  · ablk okL 43 bO3_ok
  · afi (.shl_cl .rax) 3 okL 58
  · ablk okL 61 bO4_ok
  · afi (.imul_rr .rax .rcx) 4 okL 88
  · ablk okL 92 bO5_ok
  · afi (.shl_cl .rax) 3 okL 107
  · ablk okL 110 bO6_ok
  · afi (.shl_cl .rax) 3 okL 125
  · ablk okL 128 bO7_ok
  · afi (.or_rr .rax .rcx) 3 okL 140
  · ablk okL 143 bO8_ok
  · refine NodeW.st (nodeW_st_postA hello1_instOk (fun _ => rfl) (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (l := okL) (off := 170) (p := labT okL + Int64.ofNat 170) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by decide +kernel) (by decide +kernel) hR hR8 hl hh hsub hFO
      fun σ c m hJ hF => ?_)
    obtain ⟨-, c, o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
    have hq' := hq m hF
    rw [hello1_labT] at hq'
    have hk := Spike.Lib.X64.Alloc.Call.k_toNat hq'.n_lt
    have hcl := hq'.cells
    have hra' : bAddr σ.regs .rcx 0 =
        Spike.Lib.X64.Alloc.H labT + o <<< 4 + (q.k * Spike.Lib.X64.Alloc.mOf q.h) <<< 3 := by
      rw [← hcx]; simp [bAddr, Reg64s.get64]
    have hAeq : (bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra', Spike.Lib.X64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.X64.Alloc.mOf_lt _)
        (by rw [hq'.heap]; exact hq'.room), hq'.heap, hk]
      rfl
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = bAddr σ.regs .rcx 0 := by
      rw [← hAeq]; simp
    obtain ⟨-, hmp', -⟩ := hq'.hdr o.toNat hle
    exact ⟨hmp _ (hofn ▸ hmp'), hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) m hF, hno _ (.inr ⟨o.toNat, hle, hAeq⟩)⟩
  · ablk okL 173 bO9_ok
  · refine NodeW.st (BlkW.nodeW (Spike.Lib.X64.Rt.blkW_postO hello1_instOk (l := okL) (off := 226)
      (blk := [(iRet.toDir, 1)]) (lo := -160) (hi := 8) (dead := fun _ => false)
      (ra := labT ".Lwc_rodata.x13") (by decide +kernel) rfl (by dsimp only [dumN, Spike.Lib.X64.Alloc.N]; decide)
      hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by decide +kernel)
      (hret_of_run (lo := -160) (hi := 8) (by dsimp only [dumN, Spike.Lib.X64.Alloc.N]; decide) fun σ c hJ => ?_)
      (fun _ _ _ => rfl) hsub hfit hFO) (List.cons_ne_nil _ _))
    obtain ⟨-, c, o, -, -, -, -, -, h0⟩ := hJ
    have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
    simp only [arun, List.foldl, Spike.Lib.X64.dstep, hc]
    simp only [iRet, Spike.Lib.X64.AI.tgt, dumN, Spike.Lib.X64.Alloc.N, Spike.Lib.X64.Alloc.oE]
    rw [h0, hra]
    exact Int64.ofBitVec_toBitVec _

end Alloc

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.X64Hello1W0.BlkW.nodeW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BlkW.nodeW

/--
info: 'Spike.Test.X64Hello1W0.nodeW_si_postA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_si_postA

/--
info: 'Spike.Test.X64Hello1W0.nodeW_st_postA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_st_postA

/--
info: 'Spike.Test.X64Hello1W0.nodeW_xadd_postA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_xadd_postA

/-- info: 'Spike.Test.X64Hello1W0.allocSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allocSt

end Spike.Test.X64Hello1W0
