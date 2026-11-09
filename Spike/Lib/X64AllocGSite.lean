/-
**`scc_rt_alloc` at any allocation site** (x86-64): `Spike/Lib/X64AllocG.lean`'s
`ctr_addr`, `hdr_addr` and `Spike/Lib/X64AllocGSt.lean`'s `allocSt` with
the call's premises `Call.OK` weakened to `Call.OKS`
(`Spike/Lib/X64AllocSite.lean`), the x86-64 side of the A64
`hdr_addrS`/`allocStS` (`Spike/Lib/A64AllocG{,St}.lean`). The proofs are
the released ones node for node, which stay untouched.

- `ctr_addrS`, `hdr_addrS`: the counter add's and the header store's
  addresses at any site.
- `allocStS`: `scc_rt_alloc`'s states carry the state's facts at any site.
-/
import Spike.Lib.X64AllocGSt
import Spike.Lib.X64AllocSite

namespace Spike.Lib.X64.AllocG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide FragS Frag Arena)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND At AS SI FI bAddr xaddDir stDir mB eaddr_mB cellOff arun)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk cellOf next_same own_at nodeW_postO nodeW_fi_postO)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt after exec_store_agrees exec_xaddG_agrees eaddr)
open Spike.Lib.X64ConsumerA (SFactsSt)
open Spike.Lib.X64.StubW (phOne)
open Spike.Lib.X64.W0G (AbortW0)

/-! ## The counter's and the header's addresses at any site -/

section Addr

variable {lab : Label → Int64} {ms : MemSide isa} {q : Spike.Lib.X64.Alloc.Call}

/-- **The counter's address** at the counter's add, at any site. -/
theorem ctr_addrS {σ : Spike.Lib.X64.AS} (hq : q.OKS ms lab)
    (hcx : σ.regs.rcx.toBitVec = (lab "scc_rt_heap_use").toBitVec) :
    bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
  rw [← hq.ctr, ← hcx]; simp [bAddr, Reg64s.get64]

/-- **The header's address** at the header's store, the counter's old
value `o`, at any site. -/
theorem hdr_addrS {σ : Spike.Lib.X64.AS} {o : BitVec 64} (hq : q.OKS ms lab)
    (hle : o.toNat + ms.units q.n q.τ ≤ ms.cells) (hn28 : q.n < 2 ^ 28)
    (hcx : σ.regs.rcx.toBitVec = Spike.Lib.X64.Alloc.H lab + o <<< 4 +
      (q.k * Spike.Lib.X64.Alloc.mOf q.h) <<< 3) :
    (bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o.toNat := by
  have hk := Spike.Lib.X64.Alloc.Call.k_toNat hq.n_lt
  have hcl := hq.cells
  have hra : bAddr σ.regs .rcx 0 =
      Spike.Lib.X64.Alloc.H lab + o <<< 4 + (q.k * Spike.Lib.X64.Alloc.mOf q.h) <<< 3 := by
    rw [← hcx]; simp [bAddr, Reg64s.get64]
  rw [hra, Spike.Lib.X64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.X64.Alloc.mOf_lt _)
    (by rw [hq.heap]; exact hq.room), hq.heap, hk]
  rfl

end Addr

/-! ## `scc_rt_alloc`'s nodes at any site -/

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok
  bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc` after the take, no `ret`, no dead target, at
the source start's control. -/
local macro "ablk " hb:term:max ok:term:max hp:term:max : tactic =>
  `(tactic| exact BlkW.st (Spike.Lib.X64.Rt.blkW_postO hI (lbl := Λ.static) (dead := fun _ => false) (ra := 0) $hb
    (by pc_tac) $ok hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0) $hp
    (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "asi " hb:term:max hp:term:max : tactic =>
  `(tactic| exact NodeW.st (nodeW_si_postA hI (lbl := Λ.static) $hb rfl (by pc_tac)
    (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec $hp).1 (phOne_spec $hp).2 hR hR8 hl hh hsub hFO))

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "afi " hb:term:max hp:term:max : tactic =>
  `(tactic| exact NodeW.st (nodeW_fi_postO hI (lbl := Λ.static) $hb rfl (by pc_tac)
    (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec $hp).1 (phOne_spec $hp).2 hR hR8 hl hh hsub hFO))

/-- **`scc_rt_alloc`'s states carry the state's facts** at any control, none
moved by `K`, its code passing the phase check (`hph`), for a call `q`
whose return address is in the phase of the function's entry (`hra`), the
owned words factoring through the phase (`hown`), in a region of the
allocator's frame (8-aligned) whose frame condition gives the stack range
off it (`hFO`) and the call's premises at any allocation site (`hq`,
`Call.OKS`), the counter and every header the code may store unmapped in
private memory (`hmem`), owned at no phase (`hno`), the memory side's
writable words mapped (`hmp`). `allocSt` at `Call.OKS`. -/
theorem allocStS (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OKS ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab fnL).toBitVec.toNat)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    AllocW ms q (fun s _ => SFactsSt Λ μ own rS Tk s) K exe endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31⟩ := allocPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · ablk h0 bPro_ok p0
  · ablk h1 bChk_ok p1
  · ablk h2 bJ1_ok p2
  · asi h3 p3
  · ablk h4 bC1_ok p4
  · refine NodeW.st (nodeW_xadd_postA hI hown (lbl := Λ.static) (b := .rcx) (k := 0) (r := .rax) h5 rfl rfl
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec p5).1 (phOne_spec p5).2 hR hR8 hl hh hsub hFO
      fun σ c m hJ hF => ?_)
    obtain ⟨-, c, -, hcx, -⟩ := hJ
    have hq' := hq m hF
    rw [ctr_addrS hq' hcx]
    exact ⟨hmp _ hq'.mp, hmem _ (.inl rfl) m hF, hno _ (.inl rfl)⟩
  · ablk h6 bC2_ok p6
  · ablk h7 bJ2_ok p7
  · ablk h8 bSlow_ok p8
  · ablk h9 bJ3_ok p9
  · ablk h10 bFull_ok p10
  · ablk h11 bO0_ok p11
  · afi h12 p12
  · ablk h13 bO1_ok p13
  · afi h14 p14
  · ablk h15 bO2_ok p15
  · asi h16 p16
  · ablk h17 bO3_ok p17
  · afi h18 p18
  · ablk h19 bO4_ok p19
  · afi h20 p20
  · ablk h21 bO5_ok p21
  · afi h22 p22
  · ablk h23 bO6_ok p23
  · afi h24 p24
  · ablk h25 bO7_ok p25
  · afi h26 p26
  · ablk h27 bO8_ok p27
  · refine NodeW.st (nodeW_st_postA hI hown (lbl := Λ.static) (b := .rcx) (k := 0) (r := .rax) h28 rfl rfl
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec p28).1 (phOne_spec p28).2 hR hR8 hl hh hsub hFO
      fun σ c m hJ hF => ?_)
    obtain ⟨-, c, o, ⟨-, hle, -, hn28, -, hlo⟩, -, -, hcx⟩ := hJ
    have hq' := hq m hF
    have hAeq := hdr_addrS hq' hle hn28 hcx
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = bAddr σ.regs .rcx 0 := by
      rw [← hAeq]; simp
    obtain ⟨-, hmp', -⟩ := hq'.hdr o.toNat hlo hle
    exact ⟨hmp _ (hofn ▸ hmp'), hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) m hF, hno _ (.inr ⟨o.toNat, hle, hAeq⟩)⟩
  · ablk h29 bO9_ok p29
  · have hL : lab Alloc.retL + Int64.ofNat 0 = lab Alloc.okL + Int64.ofNat 226 := by
      rw [← hI.labOk, Scc.Cert.Rt.X64.label_labelGapB hI.lays h30.1, Spike.Lib.X64.Flow.ofNat_zero']
    refine NodeW.st (Spike.Lib.LowerX64.BlkW.nodeW (Spike.Lib.X64.Rt.blkW_postO hI (lbl := Λ.static)
      (blk := [(iRet.toDir, 1)]) (lo := -160) (hi := 8) (dead := fun _ => false) (ra := Int64.ofBitVec q.ra)
      (l := Alloc.retL) (off := 0) h30.2 hL (by dsimp only [dumN, N]; decide) hR hlo hhi hR8 hl hh
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (by rw [hL]; exact blkPh_ret p30 (by rw [hra, p31]))
      (hret_of_run (lo := -160) (hi := 8) (by dsimp only [dumN, N]; decide) fun σ c hJ => ?_)
      (fun _ _ _ => rfl) hsub hfit hFO) (List.cons_ne_nil _ _))
    obtain ⟨-, c, o, -, -, -, -, -, h0, -⟩ := hJ
    have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
    simp only [arun, List.foldl, Spike.Lib.X64.dstep, hc]
    simp only [iRet, Spike.Lib.X64.AI.tgt, dumN, N, Spike.Lib.X64.Alloc.oE]
    rw [h0]

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.AllocG.ctr_addrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ctr_addrS

/-- info: 'Spike.Lib.X64.AllocG.hdr_addrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hdr_addrS

/-- info: 'Spike.Lib.X64.AllocG.allocStS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocStS

end Spike.Lib.X64.AllocG
