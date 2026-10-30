/-
**`scc_rt_alloc`'s states at `hello1.w`'s instance** (AArch64): the
allocator's node obligations (`AllocW`, `Spike/Lib/A64Alloc.lean`) inside
the state's facts (`SFactsSt`) at any control, from `Wr` at the source
start's control (`dumN`, `BlkW.st`, `NodeW.st`,
`Spike/Test/A64Hello1W0N.lean`).

- `nodeW_si_postA`: a single instruction without an event after the take,
  in a region whose frame condition gives the stack range off it.
- `nodeW_st_postA`, `nodeW_ldop_postA`: a store and an RMW of an unowned
  word after the take, the word by the abstract state (the header's address
  is the held count's), mapped, unmapped in private memory and owned at no
  phase under the frame condition.
- `allocSt`: every node of `scc_rt_alloc` for a call `q` returning to
  `wc_rodata`'s `.sp0`, in a region of the allocator's frame whose frame
  condition gives the stack range off it, the call's premises (`Call.OK`)
  and the counter and headers unmapped in private memory.
-/
import Spike.Test.A64Hello1W0N
import Spike.Lib.LowerA64.NodeTp

namespace Spike.Test.A64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (FragS Frag MemSide Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW At ND AS)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Rt (InstOk cellOf next_same own_at nodeW_postO)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt after exec_str_agrees exec_ldop access_agrees)
open Spike.Lib.A64ConsumerA (SFactsSt)
open Spike.Lib.A64.Flow.Hello1.Inst
open SccCode (hello1Λ)

/-! ## A store and an RMW of an unowned word after the take -/

section Node

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A node at a single instruction without an event** (`SI`) after the
take, in a region whose frame condition gives the words of `rS` off it
(`hFO`), its next pc in its phase. -/
theorem nodeW_si_postA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [si.toDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at a store** `str Xt, [Xn, #i]` after the take, in a region
whose frame condition gives the words of `rS` off it (`hFO`), its next pc
in its phase: the word at the abstract state's address mapped, unmapped in
private memory and owned at no phase (`ha`). -/
theorem nodeW_st_postA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {t b : XReg} {i : Int64}
    {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩ = true ∧
      Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none ∧
      ∀ j w, (⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs b i = Spike.Lib.A64.Flow.rAddr σ.regs b i := by rw [hA.regs]
    have hex := exec_str_agrees hc ha' hun (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2
      (.inl ⟨(next_same hI hpc hph _).1, fun w h => by rw [own_at hown hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

/-- **A node at an unowned word's `ld<op><k> Xs, Xt, [Xn]`** after the take,
as `nodeW_st_postA`: every leaf owns what the state owns, the word written
owned at no phase. -/
theorem nodeW_ldop_postA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {op : AtomicOp}
    {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt prog l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨(σ.regs.getXReg b).toBitVec, 8⟩ = true ∧
      Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none ∧
      ∀ j w, (⟨(σ.regs.getXReg b).toBitVec, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
    have hex := exec_ldop hc (by rw [ha']; exact hun)
    rw [ha', access_agrees (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)] at hex
    refine sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex (fun h => ?_)
      (.inl ⟨fun v _ => ⟨fun _ _ => trivial, (next_same hI hpc hph _).1⟩,
        ⟨fun _ _ _ w h => by rw [own_at hown hpc] at h; exact hno _ w h, fun _ => trivial⟩⟩)
      (fun v _ => ⟨fun _ _ => trivial, (next_same hI hpc hph _).2⟩) hO
    cases h with
    | rmw h => rw [hmw] at h; cases h
    | rmwRet _ h => cases h

end Node

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Test.A64Hello1RtW (hello1_instOk)
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {rS : Range} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc` after the take, no `ret`, no dead target, at
the source start's control. -/
local macro "ablk " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact BlkW.st (Spike.Lib.A64.Rt.blkW_postO hello1_instOk (l := $l) (k := $k) (dead := fun _ => false)
    (ra := 0) (by decide +kernel) (by dsimp only [dumN, N]; decide +kernel) $ok hR hal (by omega) (by omega)
    (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by rw [Spike.Test.A64Hello1RtW.labT_eq_labX]; decide +kernel)
    (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "asi " si:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact NodeW.st (nodeW_si_postA hello1_instOk (si := $si) (l := $l) (k := $k)
    (p := labT $l + Int64.ofNat (4 * $k)) (by decide +kernel) rfl (by dsimp only [dumN, N]; decide +kernel)
    (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by decide +kernel) (by decide +kernel) hR hR8 hl hh hsub hFO))

/-- **`scc_rt_alloc`'s states carry the state's facts** at any control, none
moved by the take, for a call `q` returning to `wc_rodata`'s `.sp0`
(`hra`), in a region of the allocator's frame (8-aligned) whose frame
condition gives the stack range off it (`hFO`) and the call's premises
(`hq`), the counter and every header the code may store unmapped in private
memory (`hmem`), owned at no phase (`hno`), the memory side's writable
words mapped (`hmp`). -/
theorem allocSt (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub hello1Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".L18_wc_rodata.sp0").toBitVec)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 hello1Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    AllocW ms q (fun s _ => SFactsSt hello1Λ μ0 own rS Tk s) (Kr rS) hello1Exe hello1End R F := by
  have hR8 : R.base.toNat % 8 = 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  · ablk "scc_rt_alloc" 0 b0_ok
  · ablk ".L2_scc_rt_alloc.0_entry" 0 b1_ok
  · ablk ".L2_scc_rt_alloc.0_entry" 4 b2_ok
  · asi iAdrpC ".L2_scc_rt_alloc.1_cnt" 0
  · asi iAddC ".L2_scc_rt_alloc.1_cnt" 1
  · ablk ".L2_scc_rt_alloc.1_cnt" 2 b3_ok
  · refine NodeW.st (nodeW_ldop_postA hello1_instOk (fun _ => rfl) (op := .ADD) (kk := .acqRel) (rs := .X9)
      (rt := .X11) (b := .X10) (l := ".L2_scc_rt_alloc.1_cnt") (k := 5)
      (p := labT ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5)) (by decide +kernel) rfl
      (by dsimp only [dumN, N]; decide +kernel) (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by decide +kernel)
      (by decide +kernel) hR hR8 hl hh hsub hFO fun σ c m hJ hF => ?_)
    obtain ⟨-, c, -, h10, -⟩ := hJ
    have hq' := hq m hF
    have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
    rw [h10']
    exact ⟨hmp _ hq'.mp, hmem _ (.inl rfl) m hF, hno _ (.inl rfl)⟩
  · ablk ".L2_scc_rt_alloc.1_cnt" 6 b4_ok
  · ablk ".L2_scc_rt_alloc.1_cnt" 15 b5_ok
  · ablk ".L2_scc_rt_alloc.2_slow" 0 b6_ok
  · ablk ".L2_scc_rt_alloc.2_slow" 4 b7_ok
  · ablk ".L2_scc_rt_alloc.4_full" 0 b9_ok
  · ablk ".L2_scc_rt_alloc.5_ok" 0 b11_ok
  · asi iAdrpH ".L2_scc_rt_alloc.5_ok" 8
  · asi iAddH ".L2_scc_rt_alloc.5_ok" 9
  · ablk ".L2_scc_rt_alloc.5_ok" 10 b12_ok
  · refine NodeW.st (nodeW_st_postA hello1_instOk (fun _ => rfl) (t := .X9) (b := .X10) (i := 0)
      (l := ".L2_scc_rt_alloc.5_ok") (k := 41) (p := labT ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41))
      (by decide +kernel) rfl (by dsimp only [dumN, N]; decide +kernel) (fun _ _ hJ => hJ.1 ▸ cfacts_c0)
      (by decide +kernel) (by decide +kernel) hR hR8 hl hh hsub hFO fun σ c m hJ hF => ?_)
    obtain ⟨-, c, o, ⟨-, hle, -, hn28, -, hlo⟩, -, -, h10⟩ := hJ
    have hq' := hq m hF
    rw [hello1_labT] at hq'
    have hk := Spike.Lib.A64.Alloc.Call.k_toNat hq'.n_lt
    have hcl := hq'.cells
    have hra : Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 =
        Spike.Lib.A64.Alloc.H labT + o <<< 4 + (q.k * Spike.Lib.A64.Alloc.mOf q.h) <<< 3 := by
      rw [← h10]; simp [Spike.Lib.A64.Flow.rAddr, Reg64s.getXReg]
    have hAeq : (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra, Spike.Lib.A64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.A64.Alloc.mOf_lt _)
        (by rw [hq'.heap]; exact hq'.room), hq'.heap, hk]
      rfl
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 := by
      rw [← hAeq]; simp
    obtain ⟨-, hmp', -⟩ := hq'.hdr o.toNat hlo hle
    exact ⟨hmp _ (hofn ▸ hmp'), hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) m hF, hno _ (.inr ⟨o.toNat, hle, hAeq⟩)⟩
  · ablk ".L2_scc_rt_alloc.5_ok" 42 b13_ok
  · refine NodeW.st (Spike.Lib.LowerA64.BlkW.nodeW (Spike.Lib.A64.Rt.blkW_postO hello1_instOk
      (l := ".L2_scc_rt_alloc.5_ok") (k := 54) (blk := [iRet.toDir]) (lo := -160) (hi := 0)
      (dead := fun _ => false) (ra := labT ".L18_wc_rodata.sp0") (by decide +kernel)
      (by dsimp only [dumN, N]; decide +kernel) (by dsimp only [dumN, N]; decide) hR hal (by omega) (by omega)
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by decide +kernel)
      (hret_of_run (lo := -160) (hi := 0) (by dsimp only [dumN, N]; decide) fun σ c hJ => ?_) (fun _ _ _ => rfl)
      hl hh hsub hfit hFO) (List.cons_ne_nil _ _))
    obtain ⟨-, c, o, -, -, -, -, -, h30⟩ := hJ
    have hc : Spike.Lib.A64.Flow.classify iRet.toDir = some iRet := rfl
    simp only [Spike.Lib.A64.Flow.arun, List.foldl, Spike.Lib.A64.Flow.dstep, hc]
    simp [iRet, Spike.Lib.A64.Flow.AI.tgt, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, Reg64s.getXReg,
      h30, hra]

end Alloc

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.A64Hello1W0.nodeW_si_postA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_si_postA

/--
info: 'Spike.Test.A64Hello1W0.nodeW_st_postA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_st_postA

/--
info: 'Spike.Test.A64Hello1W0.nodeW_ldop_postA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_ldop_postA

/-- info: 'Spike.Test.A64Hello1W0.allocSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allocSt

end Spike.Test.A64Hello1W0
