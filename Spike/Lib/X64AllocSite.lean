/-
**The x86-64 allocator at any allocation site** (the x86-64 side of AArch64's
`AllocSite` forms): `scc_rt_alloc` at a buffer
allocation or, where the memory side allows it (`ms.newOk`), a box `new` of
one object (`AllocSite`). `Spike/Lib/X64Alloc.lean` and
`Spike/Lib/X64AllocNodes.lean` (underpinning the released hello1 theorems)
are not edited; the generalised forms live here, with AArch64's names.

- `ctr_ndWS`: `ctr_ndW` (`lock xaddq`) with the source's site an `AllocSite`.
- `Call.OKS`, `Call.OK.toS`: the call's premises at a site.
- `seg_allocW_genR`: `seg_allocW_at` at `Call.OKS`, with the `ret` node's
  segment (`hret`) and the exits (`Ex`, the abort reached from `E`'s with
  `.full`'s pushed return address, `hab`) as parameters; `seg_allocW_gen`:
  the abort as `E`'s.

`Call.OK.toS` puts every buffer allocation (`seg_allocW_at`'s premise) under
`Call.OKS`; the box allocation's `ret` node (`hret`) is `X64AllocBox`'s.
-/
import Spike.Lib.X64Alloc

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **`ctr_ndW` at any allocation site** (`AllocSite`: a buffer allocation,
or, where the memory side allows it, `ms.newOk`, a box `new` of one
object): the same node, the source's site given as `AllocSite`. -/
theorem ctr_ndWS {W : Frag isa} {K : State → State → Prop} {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hr : r ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xaddDir b k r, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (τ : Ty) (e : Expr) (nn : Nat), AllocSite ms.newOk c x nn τ e ∧ c.hold = none ∧
        σ.regs.get64 r = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells → ms.lo (old.setWidth 64).toNat →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          ∀ fl, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, { ownStep r (old.setWidth 64) σ with status := fl }⟩
            (holdCtr ms c (old.setWidth 64))) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (xaddDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, hrt, hmp, hdm, x, τ, e, nn, hs, hh, hru, hX⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = BitVec.ofNat 64 ms.ctr :=
    (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xaddG_agrees (w := .W64) hc ha' hdm (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine .ctrRmw .acqRel _ _ x τ e nn hex hrt hmp hs hh
    (fun old => ?_) fun old hG _ hle hlo => ?_
  · simp only [hA.regs, hru]
  obtain ⟨hG', hL⟩ := hX old hG hle hlo
  exact ⟨hG', land_own rfl hr hF he hn hdc hpc hA hD (hL _)⟩

end Fn

end Spike.Lib.X64

namespace Spike.Lib.X64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')

-- As in `X64Alloc.lean`, whose proof `seg_allocW_gen` follows node for node.
set_option linter.unusedSimpArgs false

/-- **The call's premises at any allocation site** (`AllocSite`: the
buffer allocation `Call.OK` asks for, or, where the memory side allows it,
`ms.newOk`, a box `new` of one object of type `τ`): `Call.OK` with its
`term`, `ev` and `num` replaced by `site`. Everything but the `ret` node
(`seg_allocW_gen`) holds from these. -/
structure Call.OKS (ms : MemSide isa) (lab : Label → Int64) (q : Call) : Prop where
  site : AllocSite ms.newOk q.c0 q.x q.n q.τ q.e
  hold : q.c0.hold = none
  n_lt : q.n < 2 ^ 64
  ctr : (lab "scc_rt_heap_use").toBitVec = BitVec.ofNat 64 ms.ctr
  heap : (lab "scc_rt_heap").toBitVec.toNat = ms.heap
  room : ms.heap + 2 ^ 46 ≤ 2 ^ 64
  cells : ms.cells = 4194304
  units : ms.units q.n q.τ < 2 ^ 63
  off : ms.off q.n q.τ = 8 * (q.n * (mOf q.h).toNat) + 8
  accs : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us
  rt : ms.rt (BitVec.ofNat 64 ms.ctr).toNat
  mp : ms.mp (ctrLoc ms) true
  grow : ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells →
    ms.G (ctrLoc ms) ((old.setWidth 64 + q.u ms).setWidth 128)
  hdr : ∀ o, ms.lo o → o + ms.units q.n q.τ ≤ ms.cells →
    ms.rt (q.hdrAt ms o) ∧ ms.mp ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ true ∧
      ms.G ⟨BitVec.ofNat 64 (q.hdrAt ms o), 8⟩ (q.hdr.setWidth 128)

/-- A buffer allocation's premises are ones at its site. -/
theorem Call.OK.toS {ms : MemSide isa} {lab : Label → Int64} {q : Call} (h : q.OK ms lab) :
    q.OKS ms lab :=
  { h with site := .inl ⟨q.a, q.ta, q.ws, h.term, h.ev, h.num⟩ }

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region} {m0 : MachineData}
  {q : Call} {cells : List (Directive × Nat)}

set_option hygiene false in
/-- A block node at `l + k`: the block, its `okBlk`, its `W` obligation; the
edge is left. -/
local macro "anode " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at an instruction with undefined flags writing `%rax`, at `okL + k`
(`z` bytes), to node `j`; the invariant's facts are left. -/
local macro "fnode " fi:term:max k:term:max z:term:max j:term:max w:term:max : tactic =>
  `(tactic| refine flag_ndW (fi := $fi) rfl hF
    (code_field hp hend (by simp only [hin']) (l := okL) (off := $k) rfl) $w
      fun σ c hJ fl => ⟨c, .refl c, .inl ⟨$j, ofNat_add' _ $k $z, rfl, ?_⟩⟩)

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0`,
at any allocation site** (`Call.OKS`), to its exits `Ex`: the heap abort
reaching `Ex .abort` from `E`'s with the return address of `.full`'s `call
scc_rt_abort` in the slot it pushes, `-160` (`hab`), and whatever the `ret`
node reaches (`hret`, the one node whose step depends on the site:
`Out.alloc` at a buffer allocation, `X64.Alloc.seg_allocW_at`; a silent
`ret` keeping the hold at a box allocation). The x86-64 side of AArch64's
`seg_allocW_genR` (whose `hab` reads `x30`; here the word is `.full + 12`,
the `movq $2, %rdi` and the `call`). -/
theorem seg_allocW_genR {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OKS ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hW : AllocW ms q W K exe endPc R F) {Ex : AX → ND}
    (hab : ∀ am c, Hit (E (_root_.Executable.labels exe).label ms q lbl .abort) am c →
      am.σ.slot (-160) = ((_root_.Executable.labels exe).label fullL + 12).toBitVec → Hit (Ex .abort) am c)
    (hret : SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q .ret))
      (Next exe endPc R F (N (_root_.Executable.labels exe).label ms q) Ex)) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (Ex x) s c) := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := fnL) (b := entryL) (off := 23) hp (by simp only [hin'])
  have hk := Call.k_toNat hq.n_lt
  have hu := Call.u_toNat hq.units
  have hcl := hq.cells
  have hU := hq.units
  refine fn_segW (N := N _ ms q) (E := Ex) (fun i => ?_) i0
  cases i
  case e =>
    anode bPro bPro_ok fnL 0 hW.e
    dsimp only [N] at hJ ⊢
    rw [bPro_run]
    obtain ⟨rfl, h1, h2, h3, h4, h5⟩ := hJ
    refine .inl ⟨AN.entry, eEntry, rfl, rfl, ?_⟩
    simp [Fr, upd_apply, h1, h2, h3, h4, h5]
  case entry =>
    anode bChk bChk_ok entryL 0 hW.entry
    dsimp only [N] at hJ ⊢
    rw [bChk_run]
    obtain ⟨rfl, hFr⟩ := hJ
    have h24 := hFr.2.2.2.1
    rw [h24]
    split
    · rename_i h
      refine .inl ⟨AN.full, rfl, rfl, .inl ⟨rfl, ?_⟩⟩
      rw [hk] at h; omega
    · rename_i h
      refine .inl ⟨AN.j1, rfl, rfl, rfl, hFr, ?_⟩
      rw [hk] at h; omega
  case j1 =>
    anode bJ1 bJ1_ok entryL 16 hW.j1
    dsimp only [N] at hJ ⊢
    rw [bJ1_run]
    exact .inl ⟨AN.cnt, rfl, rfl, hJ⟩
  case cnt =>
    refine si_ndW (si := .leaRip .rax "scc_rt_heap_use") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := cntL) (off := 0) (ofNat_zero' _)) hW.cnt
      fun σ c hJ => ⟨c, .refl c, .inl ⟨AN.c1, rfl, rfl, hJ, ?_⟩⟩
    simp [SI.step, SI.regs, Reg64s.set64]
  case c1 =>
    anode bC1 bC1_ok cntL 7 hW.c1
    dsimp only [N] at hJ ⊢
    rw [bC1_run]
    obtain ⟨⟨rfl, ⟨h0, h8, h16, h24, h32⟩, hn28⟩, hax⟩ := hJ
    refine .inl ⟨AN.rmw, ofNat_add' _ 7 12, rfl, ⟨rfl, ?_, hn28⟩, ?_, ?_⟩
    · simp [Fr, upd_apply, h0, h8, h16, h24, h32]
    · simp [Reg64s.set64, Reg64s.get64, hax]
    · simp [Reg64s.set64, Reg64s.get64, h32]
  case rmw =>
    refine ctr_ndWS (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := cntL) (off := 19) rfl) hW.rmw fun m σ c _ hD hJ => ?_
    obtain ⟨⟨rfl, hFr, hn28⟩, hcx, hax⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
      rw [← hq.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
    rw [hb]
    refine ⟨rfl, hq.rt, hq.mp, hmem _ (.inl rfl) _ hD, q.x, q.τ, q.e, q.n, hq.site, hq.hold, by exact hax, fun old hG hle hlo => ⟨hq.grow old hG hle, fun fl =>
        .inl ⟨AN.c2, ofNat_add' _ 19 5, rfl, _, rfl, hle, hFr, hn28, ?_, hlo⟩⟩⟩
    simp [ownStep, Reg64s.set64]
  case c2 =>
    anode bC2 bC2_ok cntL 24 hW.c2
    dsimp only [N] at hJ ⊢
    rw [bC2_run]
    obtain ⟨o, rfl, ho, ⟨h0, h8, h16, h24, h32⟩, hn28, hax, hlo⟩ := hJ
    have hr : (σ.regs.rax.toNat : Int) = o.toNat := by rw [← hax]; rfl
    have hol := o.isLt
    rw [h32, hax, hr, hu]
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      have hlt : ms.cells < o.toNat + ms.units q.n q.τ := by
        rw [hcl]
        by_cases he : ms.units q.n q.τ + o.toNat = 4194304
        · refine absurd (BitVec.eq_of_toNat_eq ?_) h2
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits, hu] at he ⊢
          omega
        · omega
      refine .inl ⟨AN.slow, rfl, rfl, o, rfl, ho, hlt, ?_, ?_⟩
      · simp [Fr, upd_apply, h0, h8, h16, h24, h32]
      · simp [upd_apply]
    · rename_i h
      have hle : o.toNat + ms.units q.n q.τ ≤ ms.cells := by
        rw [hcl]
        by_cases he : ms.units q.n q.τ + o.toNat = 4194304
        · omega
        · refine Decidable.byContradiction fun hc => h ⟨by omega, fun h' => he ?_⟩
          have := congrArg BitVec.toNat h'
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits, hu] at this
          omega
      refine .inl ⟨AN.j2, ofNat_add' _ 24 35, rfl, o, rfl, hle, ?_, hn28, ?_, hlo⟩
      · simp [Fr, upd_apply, h0, h8, h16, h24, h32]
      · simp [upd_apply]
  case j2 =>
    anode bJ2 bJ2_ok cntL 59 hW.j2
    dsimp only [N] at hJ ⊢
    rw [bJ2_run]
    exact .inl ⟨AN.ok, rfl, rfl, hJ⟩
  case slow =>
    anode bSlow bSlow_ok slowL 0 hW.slow
    dsimp only [N] at hJ ⊢
    rw [bSlow_run]
    obtain ⟨o, hJ⟩ := hJ
    have ⟨_, ho, _, _, h48⟩ := hJ
    rw [h48]
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      refine absurd (BitVec.eq_of_toNat_eq ?_) h2
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Width.bits] at h1 ⊢
      have := o.isLt
      omega
    · exact .inl ⟨AN.j3, rfl, rfl, o, hJ⟩
  case j3 =>
    anode bJ3 bJ3_ok slowL 16 hW.j3
    dsimp only [N] at hJ ⊢
    rw [bJ3_run]
    obtain ⟨o, hc, ho, hx, -⟩ := hJ
    exact .inl ⟨AN.full, rfl, rfl, .inr ⟨o, hc, ho, hx⟩⟩
  case full =>
    anode bFull bFull_ok fullL 0 hW.full
    dsimp only [N] at hJ ⊢
    rw [bFull_run]
    exact .inr ⟨AX.abort, hab _ c ⟨rfl, rfl, by simp [Reg64s.set64, Reg64s.get64], hJ⟩
      (by simp [upd_apply])⟩
  case ok =>
    anode bO0 bO0_ok okL 0 hW.ok
    dsimp only [N] at hJ ⊢
    rw [bO0_run]
    obtain ⟨o, rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩ := hJ
    refine .inl ⟨AN.f1, rfl, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo]
  case f1 =>
    fnode (.shr_cl .rax) 11 3 AN.o1 hW.f1
    obtain ⟨o, hJo, ha, hc⟩ := hJ
    exact ⟨o, hJo, (shr_rax ha hc fl).trans (by rw [cl_vals.1])⟩
  case o1 =>
    anode bO1 bO1_ok okL 14 hW.o1
    dsimp only [N] at hJ ⊢
    rw [bO1_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ha⟩ := hJ
    refine .inl ⟨AN.f2, ofNat_add' _ 14 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, ha]
  case f2 =>
    fnode (.and_rr .rax .rcx) 29 3 AN.o2 hW.f2
    obtain ⟨o, hJo, ha, hc⟩ := hJ
    exact ⟨o, hJo, and_rax ha hc fl⟩
  case o2 =>
    anode bO2 bO2_ok okL 32 hW.o2
    dsimp only [N] at hJ ⊢
    rw [bO2_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ha⟩ := hJ
    refine .inl ⟨AN.s2, ofNat_add' _ 32 4, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, ha]
  case s2 =>
    refine si_ndW (si := .leaRip .rax "scc_rt_heap") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := okL) (off := 36) rfl) hW.s2
      fun σ c hJ => ⟨c, .refl c, .inl ⟨AN.o3, ofNat_add' _ 36 7, rfl, ?_⟩⟩
    obtain ⟨o, hJo, h72⟩ := hJ
    exact ⟨o, hJo, h72, by simp [SI.step, SI.regs, Reg64s.set64]⟩
  case o3 =>
    anode bO3 bO3_ok okL 43 hW.o3
    dsimp only [N] at hJ ⊢
    rw [bO3_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h72, ha⟩ := hJ
    refine .inl ⟨AN.f3, ofNat_add' _ 43 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h72, ha]
  case f3 =>
    fnode (.shl_cl .rax) 58 3 AN.o4 hW.f3
    obtain ⟨o, hJo, h72, h80, ha, hc⟩ := hJ
    exact ⟨o, hJo, h72, h80, (shl_rax ha hc fl).trans (by rw [cl_vals.2.1])⟩
  case o4 =>
    anode bO4 bO4_ok okL 61 hW.o4
    dsimp only [N] at hJ ⊢
    rw [bO4_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h72, h80, ha⟩ := hJ
    refine .inl ⟨AN.f4, ofNat_add' _ 61 27, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h72, h80, ha, BitVec.add_comm]
  case f4 =>
    fnode (.imul_rr .rax .rcx) 88 4 AN.o5 hW.f4
    obtain ⟨o, hJo, h96, ha, hc⟩ := hJ
    exact ⟨o, hJo, h96, imul_rax ha hc fl⟩
  case o5 =>
    anode bO5 bO5_ok okL 92 hW.o5
    dsimp only [N] at hJ ⊢
    rw [bO5_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h96, ha⟩ := hJ
    refine .inl ⟨AN.f5, ofNat_add' _ 92 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h96, ha]
  case f5 =>
    fnode (.shl_cl .rax) 107 3 AN.o6 hW.f5
    obtain ⟨o, hJo, h96, ha, hc⟩ := hJ
    exact ⟨o, hJo, h96, (shl_rax ha hc fl).trans (by rw [cl_vals.2.2.1])⟩
  case o6 =>
    anode bO6 bO6_ok okL 110 hW.o6
    dsimp only [N] at hJ ⊢
    rw [bO6_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, h96, ha⟩ := hJ
    refine .inl ⟨AN.f6, ofNat_add' _ 110 15, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo, h96, ha]
  case f6 =>
    fnode (.shl_cl .rax) 125 3 AN.o7 hW.f6
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    exact ⟨o, hJo, hb, (shl_rax ha hc fl).trans (by rw [cl_vals.2.2.2])⟩
  case o7 =>
    anode bO7 bO7_ok okL 128 hW.o7
    dsimp only [N] at hJ ⊢
    rw [bO7_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩, ha⟩ := hJ
    refine .inl ⟨AN.f7, ofNat_add' _ 128 12, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h96, h112, ha]
  case f7 =>
    fnode (.or_rr .rax .rcx) 140 3 AN.o8 hW.f7
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    exact ⟨o, hJo, hb, or_rax ha hc fl⟩
  case o8 =>
    anode bO8 bO8_ok okL 143 hW.o8
    dsimp only [N] at hJ ⊢
    rw [bO8_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩, ha⟩ := hJ
    refine .inl ⟨AN.hdr, ofNat_add' _ 143 27, rfl, o, ?_⟩
    simp [Jok, Fr, Jbase, upd_apply, Reg64s.set64, Reg64s.get64, h0, h8, h16, h24, h32, h48, hle, hn28, hlo,
      h96, h112, ha, BitVec.add_comm]
  case hdr =>
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := okL) (off := 170) rfl) hW.hdr fun m σ c _ hD hJ => ?_
    obtain ⟨o, hJo, hb, ha, hc⟩ := hJ
    have ⟨_, hle, _, hn28, _, hlo⟩ := hJo
    have hra : bAddr σ.regs .rcx 0 = H (_root_.Executable.labels exe).label + o <<< 4 + (q.k * mOf q.h) <<< 3 := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hAeq : (bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra, base_toNat (by omega) (by omega) (mOf_lt _) (by rw [hq.heap]; exact hq.room), hq.heap, hk]
      rfl
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = bAddr σ.regs .rcx 0 := by
      rw [← hAeq]; simp
    obtain ⟨hrt, hmp, hG⟩ := hq.hdr o.toNat hlo hle
    have hv : σ.regs.get64 .rax = q.hdr := ha
    refine ⟨hAeq ▸ hrt, hofn ▸ hmp, ?_, hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) _ hD, c, .refl c,
      .inl ⟨AN.o9, ofNat_add' _ 170 3, rfl, o, hJo, hb⟩⟩
    rw [← hofn, hv]
    exact hG
  case o9 =>
    anode bO9 bO9_ok okL 173 hW.o9
    dsimp only [N] at hJ ⊢
    rw [bO9_run]
    obtain ⟨o, ⟨rfl, hle, ⟨h0, h8, h16, h24, h32⟩, hn28, h48, hlo⟩, ⟨h96, h112⟩⟩ := hJ
    refine .inl ⟨AN.ret, ofNat_add' _ 173 53, rfl, o, rfl, hle, hn28, ?_, ?_, ?_, hlo⟩
    · simp [Reg64s.set64, Reg64s.get64, h96, h112]
      ac_rfl
    · simp [Reg64s.set64, Reg64s.get64, h8]
    · simp [upd_apply, h0]
  case ret => exact hret

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0`,
at any allocation site** (`Call.OKS`), to its exits `Ex`: the heap abort as
`E`'s (`hab`), and whatever the `ret` node reaches (`hret`, the one node
whose step depends on the site: `Out.alloc` at a buffer allocation,
`X64.Alloc.seg_allocW_at`; a silent `ret` keeping the hold at a box
allocation). The x86-64 side of AArch64's `seg_allocW_gen`:
`seg_allocW_genR` with `Ex .abort` `E`'s. -/
theorem seg_allocW_gen {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} {kp : Nat}
    (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi) (hq : q.OKS ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hW : AllocW ms q W K exe endPc R F) {Ex : AX → ND}
    (hab : Ex .abort = E (_root_.Executable.labels exe).label ms q lbl .abort)
    (hret : SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q .ret))
      (Next exe endPc R F (N (_root_.Executable.labels exe).label ms q) Ex)) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (Ex x) s c) :=
  seg_allocW_genR hp hend hin hF hR hlo hhi hq hmem hW (fun _ _ h _ => hab ▸ h) hret i0

end Proof

end Spike.Lib.X64.Alloc

/-- info: 'Spike.Lib.X64.Alloc.seg_allocW_genR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Alloc.seg_allocW_genR

/-- info: 'Spike.Lib.X64.Alloc.seg_allocW_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Alloc.seg_allocW_gen
