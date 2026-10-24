/-
**The runtime's callee segments, parametric in the program** (H2, segments
3 to 5): the hand `alloc_tcb_segW`, `stack_take_segW` and `thread_init_segW`
(`Spike/Lib/A64Ret0.lean`) with the code check (`allocTcbIn prog`, ...) a
premise instead of its `ret0` instance, so that each is proved once.

- The proofs are the hand ones; only the code premise moves. The node
  obligations (`TcbW`, `TakeW`, `TiW`) and the memory-side facts (`StOk`,
  `TcbOk`, `TakeOk`) stay premises; their discharge over the placement
  check is later work.
- **Oracle**: on `ret0` the hand theorems follow from these with the
  hand code checks (`Spike/Lib/Rt/A64SegsRet0.lean`).
-/
import Spike.Lib.Rt.A64Main

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_alloc_tcb` -/

section TcbProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb` inside `W`: the block, its `okBlk`, its code, its
obligation; the edge is left. -/
local macro "tnodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (code_of hp hend (by simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_alloc_tcb` is one segment inside `W`** (`alloc_tcb_seg`, its
states' obligations `hW`): in any valid layout of any program with its code (`hin`),
from its entry to its return, for any region holding its frame of 192 and
any frame condition implying `F0`, given: room for the TCB below `2^17`
(`hn`), the header word's facts (`hhdr`), and the counter's add's
(`htcb`). -/
theorem allocTcb_segW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hin : AllocTcb.allocTcbIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbG) (hn : q.n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F0 exe endPc (pinA (_root_.Executable.labels exe).label + q.n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F0 exe endPc q.n0) (hW : ∀ i, TcbW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin'
  have eEntry := label_labelGap hp hin'.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  refine fn_segW (N := tcbN _ q) (E := tcbX _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnodeW AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0 (hW TN.e)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnodeW AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0 (hW TN.entry)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnodeW AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 4 (hW TN.j1)
    dsimp only [tcbN, tcbX] at hJ ⊢
    rw [AllocTcb.atJ1_run]
    exact .inl ⟨TN.len, rfl, rfl, hJ⟩
  case len =>
    tnodeW AllocTcb.atLen AllocTcb.atLen_ok AllocTcb.lenL 0 (hW TN.len)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atLen_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.adrp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case adrp =>
    refine si_ndW (si := .adrp .X9 "scc_rt_pinned_next") hF
      (code_of hp hend hin'.1.1.1.1.1.1.1.1.1.1.2 rfl) (hW TN.adrp) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.add, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    exact (ofNat4_succ' _ 32).symm
  case add =>
    refine si_ndW (si := .addLo12 .X9 .X9 "scc_rt_pinned_next") hF
      (code_of hp hend hin'.1.1.1.1.1.1.1.1.1.2 rfl) (hW TN.add) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 33).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, AllocTcb.labStep_fr1 _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case arg =>
    tnodeW AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 34 (hW TN.arg)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walk (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.rmw, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownLdop_ndW hF (code_of hp hend hin'.1.1.1.1.1.1.1.2 rfl) htcb.own (hW TN.rmw) fun _ σ c _ _ hJ => ?_
    dsimp only [tcbN] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TN.bnd, (ofNat4_succ' _ 37).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact htcb.next.mono hFF
    · simpa [ldStep, AllocTcb.Fr1, AllocTcb.Fr0] using hJ
    · simp [ldStep]
  case bnd =>
    tnodeW AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 38 (hW TN.bnd)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walk (_root_.Executable.labels exe).label _ hJ h11 hn
    exact .inl ⟨TN.j2, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnodeW AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 47 (hW TN.j2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    rw [AllocTcb.atJ2_run]
    exact .inl ⟨TN.ok, rfl, rfl, hJ⟩
  case ok =>
    refine si_ndW (si := .adrp .X9 "scc_rt_pinned") hF
      (code_of hp hend hin'.1.1.1.1.2 (ofNat4_zero _)) (hW TN.ok) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok1, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    rfl
  case ok1 =>
    refine si_ndW (si := .addLo12 .X9 .X9 "scc_rt_pinned") hF
      (code_of hp hend hin'.1.1.1.2 rfl) (hW TN.ok1) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok2, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 1).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, AllocTcb.labStep_fr2 _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case ok2 =>
    tnodeW AllocTcb.atOk AllocTcb.atOk_ok AllocTcb.okL 2 (hW TN.ok2)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atOk_walk (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.hdr, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_ndW (code_of hp hend hin'.1.2 rfl) (hW TN.hdr) fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have ha : rAddr σ.regs .X10 0 = pinA (_root_.Executable.labels exe).label + q.n0 := by
      rw [← h10]; simp [rAddr, Reg64s.getXReg]
    rw [ha, Spike.Lib.A64.Alloc.getRegOrZr_x]
    refine ⟨hhdr.rt, hhdr.mp, ?_, hhdr.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TN.ret, (ofNat4_succ' _ 29).symm, rfl, rfl, hJ⟩⟩
    have : (σ.regs.getXReg .X9).toBitVec = AllocTcb.hdr0 ||| 1#64 <<< 36 := by
      rw [← h9]; simp [Reg64s.getXReg]
    rw [this]; exact hhdr.G
  case ret =>
    tnodeW AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 30 (hW TN.ret)
    dsimp only [tcbN, tcbX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩


end TcbProof

/-! ## `scc_rt_stack_take` -/

section TakeProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_stack_take` inside `W`: the block, its `okBlk`,
its code, its obligation; the edge is left. -/
local macro "knodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR hal hlo hhi
    (code_of hp hend (by simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_stack_take` is one segment inside `W`, the take its outside
move**: `stack_take_seg` with the take site the kernel's take of `rS`
(`TakeK`, `take_ndW`) instead of a `nop`, so at the return `rS` is in
private memory (`StackM`). Given the node obligations (`hW`), the region's
cells off `rS` (`hRS`), every aligned word of `rS` off the region (`hout`),
and the frame condition kept by the take (`hFt`). -/
theorem stackTake_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hin : StackTake.stackTakeIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TakeG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TakeW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (takeNG (_root_.Executable.labels exe).label q false .e))
      (fun s c => ∃ x, At exe endPc R (fun m => F m ∧ StackM rS m)
        (takeXG (_root_.Executable.labels exe).label q true x) s c) := by
  have hin' := hin
  simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hin'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hGap, -⟩, -⟩, -⟩, -⟩, hLfn⟩, -⟩, hLfr⟩, -⟩, hLlk⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    hLlk2⟩, -⟩, -⟩, hLnx⟩, -⟩, -⟩, -⟩, -⟩, hLst⟩, -⟩, -⟩, hGap2⟩, hNop⟩, -⟩ := hin'
  have eEntry := label_labelGap hp hGap
  have eSite := label_labelGap hp hGap2
  have hC := hin
  simp only [StackTake.stackTakeIn, Bool.and_eq_true] at hC
  let lab := (_root_.Executable.labels exe).label
  have hst : ∀ L σ, (AllocTcb.labStep (_root_.Executable.labels exe).label L σ).slot = σ.slot ∧
      (AllocTcb.labStep (_root_.Executable.labels exe).label L σ).regs.SP = σ.regs.SP :=
    fun L σ => ⟨(AllocTcb.labStep_spec _ L σ).2.1, (AllocTcb.labStep_spec _ L σ).2.2.1⟩
  have hAbs : ∀ {m : MachineData} {σ : Flow.AS} {pm : _root_.Mem 64}, Flow.Abs R StackTake.oI m σ →
      Flow.Abs R StackTake.oI (takeMem pm rS m) σ := fun hA =>
    ⟨hA.regs, hA.status, hA.so, fun k hk => by rw [loadInt_takeMem (hRS k hk)]; exact hA.slot k hk⟩
  have hSM := stackM_stable hfit hout
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R) (Fg := takeF F rS)
      (N := takeNG lab q) (E := takeXG lab q)
    (fun b i => ?_) false TK.e).mono_pre fun s c h => ?_).mono_post fun s c h => ?_
  rotate_left
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, nofun⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, rfl, hJ⟩
  have hFb : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m → F0 m := fun m h => hFF m h.1
  have hWb : ∀ i, TakeW W (TakeK (lab StackTake.siteL) rS) exe endPc R (takeF F rS b) (StackM rS) q i :=
    fun i => (hW i).mono fun m h => h.1
  cases i
  case e =>
    refine seg_fixW b ?_
    knodeW StackTake.stPro StackTake.stPro_ok StackTake.fnL 0 (hWb TK.e)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stPro_walk lab _ hJ
    exact .inl ⟨TK.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine seg_fixW b ?_
    knodeW StackTake.stInit StackTake.stInit_ok StackTake.entryL 0 (hWb TK.entry)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stInit_walk lab _ hJ
    exact .inl ⟨TK.cls, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case cls =>
    refine seg_fixW b ?_
    knodeW StackTake.stCls StackTake.stCls_ok StackTake.clsL 0 (hWb TK.cls)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stCls_walk lab _ hJ
    exact .inl ⟨TK.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ1 StackTake.stJ1_ok StackTake.clsL 4 (hWb TK.j1)
    dsimp only [takeNG] at hJ ⊢
    rw [StackTake.stJ1_run]
    exact .inl ⟨TK.d0, by dsimp only [takeNG]; rw [ofNat4_zero], rfl, hJ⟩
  case d0 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.d2
      (labPair_segW hp hend hLfn hFb rfl rfl (hWb TK.d0).1 (hWb TK.d0).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_free_n" σ
      simpa [StackTake.Fr1, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case d2 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFreeN StackTake.stFreeN_ok StackTake.doneL 2 (hWb TK.d2)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFreeN_walk lab _ hJ h9
    exact .inl ⟨TK.d7, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case d7 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.d9
      (labPair_segW hp hend hLfr hFb rfl rfl (hWb TK.d7).1 (hWb TK.d7).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_⟩)
    obtain ⟨h1, h2⟩ := hst "scc_rt_stack_free" σ
    simpa [StackTake.Fr2, StackTake.Fr1, StackTake.Fr0, h1, h2] using h
  case d9 =>
    refine seg_fixW b ?_
    knodeW StackTake.stFree StackTake.stFree_ok StackTake.doneL 9 (hWb TK.d9)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stFree_walk lab _ hJ
    exact .inl ⟨TK.d14, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case d14 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.d16
      (labPair_segW hp hend hLlk hFb rfl rfl (hWb TK.d14).1 (hWb TK.d14).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_lock" σ
      simpa [StackTake.Fr2, StackTake.Fr1, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case d16 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLock StackTake.stLock_ok StackTake.doneL 16 (hWb TK.d16)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stLock_walk lab _ hJ h9
    exact .inl ⟨TK.sp0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case sp0 =>
    refine seg_fixW b ?_
    knodeW StackTake.stSwp StackTake.stSwp_ok StackTake.spinL 0 (hWb TK.sp0)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSwp_walk lab _ hJ
    exact .inl ⟨TK.swp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case swp =>
    refine seg_fixW b ?_
    refine ownSwp_ndW hFb (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 rfl) htk.ownLock
      (hWb TK.swp) fun _ σ c _ _ hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.sp3, (ofNat4_succ' _ 2).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [getRegOrZr_x9, h9]; exact htk.lock1.mono hFFb
    · simpa [ldStep, StackTake.Fr3, StackTake.Fr2, StackTake.Fr1, StackTake.Fr0] using hJ
    · simp [ldStep]
  case sp3 =>
    refine seg_fixW b ?_
    knodeW StackTake.stSpin StackTake.stSpin_ok StackTake.spinL 3 (hWb TK.sp3)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stSpin_walk lab _ hJ h11
    exact .inl ⟨TK.lk0, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case lk0 =>
    refine seg_fixW b ?_
    knodeW StackTake.stLdN StackTake.stLdN_ok StackTake.lockedL 0 (hWb TK.lk0)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := StackTake.stLdN_walk lab _ hJ
    exact .inl ⟨TK.ldn, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case ldn =>
    refine seg_fixW b ?_
    refine ownLdr_ndW hFb (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 rfl) htk.ownFreeN
      (hWb TK.ldn) fun _ σ c _ _ hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h10⟩ := hJ
    refine ⟨by rw [rAddr_x10 h10]; simp [lab], htk.freeN.mono hFFb,
      .inl ⟨TK.lk2, (ofNat4_succ' _ 1).symm, rfl, rfl, ?_, ?_⟩⟩
    · simpa [ldStep, StackTake.Fr3, StackTake.Fr2, StackTake.Fr1, StackTake.Fr0] using hJ
    · simp [ldStep]
  case lk2 =>
    refine seg_fixW b ?_
    knodeW StackTake.stEmpty StackTake.stEmpty_ok StackTake.lockedL 2 (hWb TK.lk2)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stEmpty_walk lab _ hJ h9
    exact .inl ⟨TK.b0, by rw [h1]; dsimp only [takeNG]; rw [ofNat4_zero], by rw [h2]; rfl, rfl, h3.fr0⟩
  case b0 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.b2
      (labPair_segW hp hend hLlk2 hFb rfl rfl (hWb TK.b0).1 (hWb TK.b0).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_lock" σ
      simpa [StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case b2 =>
    refine seg_fixW b ?_
    knodeW StackTake.stUnl StackTake.stUnl_ok StackTake.bumpL 2 (hWb TK.b2)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stUnl_walk lab _ hJ h9
    exact .inl ⟨TK.unl, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case unl =>
    refine seg_fixW b ?_
    refine ownStlr_ndW (A := lockA lab) (code_of hp hend hC.1.1.1.1.1.1.1.1.1.1.1.2 rfl)
      (hWb TK.unl) fun _ σ c _ _ hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.b6, (ofNat4_succ' _ 5).symm, rfl, rfl, hJ⟩⟩
    rw [getRegOrZr_x9, h9]; exact htk.lock0.mono hFFb
  case b6 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.b8
      (labPair_segW hp hend hLnx hFb rfl rfl (hWb TK.b6).1 (hWb TK.b6).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stack_next" σ
      simpa [StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case b8 =>
    refine seg_fixW b ?_
    knodeW StackTake.stAdd StackTake.stAdd_ok StackTake.bumpL 8 (hWb TK.b8)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stAdd_walk lab _ hJ h9
    exact .inl ⟨TK.nxt, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case nxt =>
    refine seg_fixW b ?_
    refine ownLdop_ndW hFb (code_of hp hend hC.1.1.1.1.1.1.1.1.2 rfl) htk.ownNext (hWb TK.nxt) fun _ σ c _ _ hJ => ?_
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TK.b12, (ofNat4_succ' _ 11).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact htk.next.mono hFFb
    · simpa [ldStep, StackTake.Fr0] using hJ
    · simp [ldStep]
  case b12 =>
    refine seg_fixW b ?_
    knodeW StackTake.stBnd StackTake.stBnd_ok StackTake.bumpL 12 (hWb TK.b12)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stBnd_walk lab _ hJ h11 hk
    exact .inl ⟨TK.b21, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case b21 =>
    refine seg_fixW b ?_
    knodeW StackTake.stJ2 StackTake.stJ2_ok StackTake.bumpL 21 (hWb TK.b21)
    dsimp only [takeNG] at hJ ⊢
    rw [StackTake.stJ2_run]
    exact .inl ⟨TK.ok0, by dsimp only [takeNG]; rw [ofNat4_zero], rfl, hJ⟩
  case ok0 =>
    refine seg_fixW b ?_
    refine seg_givenW TK.ok2
      (labPair_segW hp hend hLst hFb rfl rfl (hWb TK.ok0).1 (hWb TK.ok0).2 fun σ c ⟨h0, h⟩ => ⟨h0, ?_, ?_⟩)
    · obtain ⟨h1, h2⟩ := hst "scc_rt_stacks" σ
      simpa [StackTake.Fr4, StackTake.Fr0, h1, h2] using h
    · exact (AllocTcb.labStep_spec lab _ σ).1
  case ok2 =>
    refine seg_fixW b ?_
    knodeW StackTake.stOk StackTake.stOk_ok StackTake.okL 2 (hWb TK.ok2)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stOk_walk lab _ hJ h9
    exact .inl ⟨TK.tk, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case tk =>
    refine seg_fixW b ?_
    knodeW StackTake.stSite StackTake.stSite_ok StackTake.takenL 0 (hWb TK.tk)
    dsimp only [takeNG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := StackTake.stSite_walk lab _ hJ
    exact .inl ⟨TK.site, by rw [h1]; exact eSite, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case site =>
    refine seg_movedW (j := TK.ret) ((take_ndW (n' := takeNG lab q true TK.ret) rfl
      (fun s he hn => code_of hp hend hNop
        (ofNat4_zero _) s he hn) (hWb TK.site) (fun m σ pm hA hD => ⟨hAbs hA, hFt m pm hD.1, fun _ => stackM_takeMem⟩)
      fun σ c hJ => ⟨rfl, c, .refl c, rfl, hJ.1, hJ.2.1⟩).mono_post fun _ _ h => ⟨true, h⟩)
  case ret =>
    cases b
    · exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => Bool.false_ne_true h
    refine seg_fixW true ?_
    knodeW StackTake.stRet StackTake.stRet_ok StackTake.siteL 1 (blkW_mono (F := fun m => F m ∧ StackM rS m)
      (F' := takeF F rS true) (hW TK.ret) fun m h => ⟨h.1, h.2 rfl⟩)
    dsimp only [takeNG, takeXG] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := StackTake.stRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩


end TakeProof

/-! ## `scc_rt_thread_init` -/

section TiWProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_init` inside `W`. -/
local macro "inodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR hal (by omega) hhi
    (code_of hp hend (by simp only [ThreadInit.threadInitIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_thread_init` is one segment inside `W`, the take its outside
move**: `thread_init_seg` with `stack_take_segW` at the call, so at the
return the stack range `rS` is in private memory (`StackM`). Given the node
obligations (`hW`), the region's cells off `rS` (`hRS`), every aligned word
of `rS` off the region (`hout`), and the frame condition kept by the take
(`hFt`). -/
theorem threadInit_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hin : ThreadInit.threadInitIn prog = true) (hsp : tiSpIn prog = true)
    (hst : StackTake.stackTakeIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 exe endPc (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TiW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [ThreadInit.threadInitIn, Bool.and_eq_true] at hin'
  have eEntry := label_labelGap hp hin'.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  have eSp := label_labelGap hp hsp
  let lab := (_root_.Executable.labels exe).label
  have hSM := stackM_stable hfit hout
  -- the take's callee region, and `rS` off it
  have hb' := Region.callee_base (hi' := 0) hR (show R.lo ≤ -48 + -208 by omega) (by decide)
    (show (-48 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48) (-208) 0).Off k → ∀ i < 8,
      (R.callee (-48) (-208) 0).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ -48 + -208 by omega) (show (-48 : Int) + 0 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48) (-208) 0).base.toNat + (R.callee (-48) (-208) 0).lo ∨
        ((R.callee (-48) (-208) 0).base.toNat : Int) + (R.callee (-48) (-208) 0).hi ≤ a := fun a h8 ha ha7 => by
    show (a : Int) + 8 ≤ ((R.callee (-48) (-208) 0).base.toNat : Int) + -208 ∨
      ((R.callee (-48) (-208) 0).base.toNat : Int) + 0 ≤ a
    rcases hout a h8 ha ha7 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R) (Fg := takeF F rS)
      (N := tiNG (_root_.Executable.labels exe).label q) (E := tiXG (_root_.Executable.labels exe).label q)
      (fun b i => ?_) false TI.e).mono_pre fun s c h => ?_).mono_post
    fun s c h => ?_
  rotate_left
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, nofun⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, hJ⟩
  have hFb : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m → F0 m := fun m h => hFF m h.1
  cases i
  case e =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0 (blkW_mono (hW TI.e) fun m h => h.1)
    dsimp only [tiNG, tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiCall ThreadInit.tiCall_ok ThreadInit.entryL 0 (blkW_mono (hW TI.entry) fun m h => h.1)
    dsimp only [tiNG, tiN] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiCall_walk lab _ hJ
    refine .inl ⟨TI.call, h1.symm, ?_, ⟨rfl, h2, h3⟩, ?_⟩
    · rw [ThreadInit.tiCall_run]; rfl
    · rw [ThreadInit.tiCall_run]
      simp only [ofInt_bmod]
      rw [eSp, show Int64.ofNat (4 * 2) = 8 from rfl, Int64.toBitVec_add,
        show ∀ y : Int, y + 4 + 4 = y + 8 from fun y => by omega, BitVec.ofInt_add,
        Spike.Lib.int64_ofInt_toInt]; rfl
  case call =>
    refine seg_fixW true ?_
    refine call_nd_FW (lo' := -208) (hi' := 0) (M := StackM rS) (Ne := fun g => takeNG lab (tiTake q g) false .e)
      (Ex := fun g => takeXG lab (tiTake q g) true)
      hR hal hFb (by show R.lo ≤ -48 + -208; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide)
      (TakeK.kstable fun m pm ⟨hD, _⟩ => ⟨hFt m pm hD, fun _ => stackM_takeMem⟩)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h.1, fun _ => hM⟩)
      (fun R' F' hR' hal' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h30⟩, ⟨-, -, -, h30', -⟩⟩ := hg'
        exact (stackTake_segW hp hend hst hF' hR' hal' hlo' hhi' (fun m h => hFF m (hFF' m h).1) (tiTake q g') hk htk
          (fun i => (hW TI.call g' (h30'.symm.trans h30) i).mono fun m h => (hFF' m h).1) hRS' hfit hout'
          (takeMem_of_kstable hK' exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, -, h0⟩, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, hfr, -⟩, h30⟩ ⟨-, hsp', -, h30', -⟩ ⟨-, rfl, hPost⟩ hregs - hslot
      obtain ⟨hsp, h16, h8, h48⟩ := hfr
      have hk' : ∀ k : Int, k % 8 = 0 → -48 ≤ k → k ≤ -8 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hslot k ⟨h1, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [tiNG, tiN] at h; omega
      refine .inl ⟨TI.sp, ?_, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · show lab ThreadInit.spL = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.SP.toBitVec = _
        rw [hregs, hPost.1, ← hsp']; exact hsp
      · rw [hk' (-16) (by decide) (by decide) (by decide)]; exact h16
      · rw [hk' (-8) (by decide) (by decide) (by decide)]; exact h8
      · rw [hk' (-48) (by decide) (by decide) (by decide)]; exact h48
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2
  case sp =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiSp ThreadInit.tiSp_ok ThreadInit.spL 0 (blkW_tiS (hW TI.sp))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ, h0⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ h0
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st0 =>
    refine seg_fixW b ?_
    have hc : blockAt prog ThreadInit.spL (11 + 3 * 0) [strDir .X9 .X10 0] = true :=
      (show parseAArch64("str x9, [x10]") = [strDir .X9 .X10 0] by decide) ▸ hin'.1.1.1.1.1.1.1.1.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_tiS (hW TI.st0)) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 0, q.tcb) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 0) = BitVec.ofNat 64 (8 * 0) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f1, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f1 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF1 ThreadInit.tiF1_ok ThreadInit.spL 12 (blkW_tiS (hW TI.f1))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st1 =>
    refine seg_fixW b ?_
    have hc : blockAt prog ThreadInit.spL (11 + 3 * 1) [strDir .X9 .X10 8] = true :=
      (show parseAArch64("str x9, [x10, #8]") = [strDir .X9 .X10 8] by decide) ▸ hin'.1.1.1.1.1.1.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_tiS (hW TI.st1)) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 1, tiBase (_root_.Executable.labels exe).label q + 4096#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 8) = BitVec.ofNat 64 (8 * 1) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f2, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f2 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF2 ThreadInit.tiF2_ok ThreadInit.spL 15 (blkW_tiS (hW TI.f2))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF2_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st2 =>
    refine seg_fixW b ?_
    have hc : blockAt prog ThreadInit.spL (11 + 3 * 2) [strDir .X9 .X10 16] = true :=
      (show parseAArch64("str x9, [x10, #16]") = [strDir .X9 .X10 16] by decide) ▸ hin'.1.1.1.1.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_tiS (hW TI.st2)) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 2, 0#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 16) = BitVec.ofNat 64 (8 * 2) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f3, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f3 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF3 ThreadInit.tiF3_ok ThreadInit.spL 18 (blkW_tiS (hW TI.f3))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF3_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st3 =>
    refine seg_fixW b ?_
    have hc : blockAt prog ThreadInit.spL (11 + 3 * 3) [strDir .X9 .X10 24] = true :=
      (show parseAArch64("str x9, [x10, #24]") = [strDir .X9 .X10 24] by decide) ▸ hin'.1.1.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_tiS (hW TI.st3)) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 3, 0#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 24) = BitVec.ofNat 64 (8 * 3) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f4, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f4 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF4 ThreadInit.tiF4_ok ThreadInit.spL 21 (blkW_tiS (hW TI.f4))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st4 =>
    refine seg_fixW b ?_
    have hc : blockAt prog ThreadInit.spL (11 + 3 * 4) [strDir .X9 .X10 32] = true :=
      (show parseAArch64("str x9, [x10, #32]") = [strDir .X9 .X10 32] by decide) ▸ hin'.1.1.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_tiS (hW TI.st4)) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 4, tiBase (_root_.Executable.labels exe).label q) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 32) = BitVec.ofNat 64 (8 * 4) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.f5, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case f5 =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiF5 ThreadInit.tiF5_ok ThreadInit.spL 24 (blkW_tiS (hW TI.f5))
    dsimp only [tiNG, tiA, tiN] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st5 =>
    refine seg_fixW b ?_
    have hc : blockAt prog ThreadInit.spL (11 + 3 * 5) [strDir .X9 .X10 40] = true :=
      (show parseAArch64("str x9, [x10, #40]") = [strDir .X9 .X10 40] by decide) ▸ hin'.1.2
    refine rtst_ndW (code_of hp hend hc rfl) (nodeW_tiS (hW TI.st5)) fun m σ c _ hD hJ => ?_
    dsimp only [tiNG, tiA, tiN] at hJ
    obtain ⟨rfl, rfl, hJ, h9, h10⟩ := hJ
    have hfi := hfld (8 * 5, tiBase (_root_.Executable.labels exe).label q + 16384#64) (by simp [ThreadInit.fields])
    rw [rAddr_x10 h10, show BitVec.ofInt 64 (Int64.toInt 40) = BitVec.ofNat 64 (8 * 5) by decide,
      getRegOrZr_x9, h9]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0, .refl q.c0,
      .inl ⟨TI.ret, (ofNat4_succ' _ _).symm, rfl, rfl, rfl, hJ⟩⟩
  case ret =>
    refine seg_fixW b ?_
    inodeW ThreadInit.tiRet ThreadInit.tiRet_ok ThreadInit.spL 27 (blkW_tiS (hW TI.ret))
    dsimp only [tiNG, tiA, tiN, tiXG, tiX] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩


end TiWProof

/-! ## `_start` and `scc_rt_start` up to the switch -/

section StartProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`_start` inside `W`** (hand `entry_segW`), in any valid layout of any
program with `_start`'s branch (`hin`). -/
theorem entry_segW' {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hin : blockAt prog "_start" 0 entryB = true) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 0 ≤ R.hi) (c0 : Ctl)
    (hW : BlkW W K exe endPc R F (entryN (_root_.Executable.labels exe).label c0) entryB) :
    SegW W K p lbl ms (At exe endPc R F (entryN (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) :=
  seg_oneW (seg_ndW (by simp [entryB]) entryB_ok hF hR hal hlo hhi
    (code_of hp hend hin (ofNat4_zero _)) hW fun σ c hJ => ⟨c, .refl c, .inl ⟨(), by
      dsimp only [entryN, startN0]; rw [entryB_run], by
      dsimp only [entryN, startN0]; rw [entryB_run]; exact (by decide : Abort.oE.le Abort.oE = true), by
      dsimp only [entryN, startN0] at hJ ⊢; exact hJ⟩⟩)

/-- **`scc_rt_start` up to `.sp2` inside `W`** (`start_sp2_seg`, its states'
obligations `hW`). The call of `scc_rt_alloc_tcb` asks no closure under `K`
of it (`call_nd_FWK` with `KC := False`): no outside move is in it. -/
theorem startSp2_segW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hin : startCallIn prog = true) (hstart : startIn prog = true)
    (hat : AllocTcb.allocTcbIn prog = true)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0) (hW : Sp0W W K exe endPc R F n0 c0) :
    SegW W K p lbl ms (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0))
      (At exe endPc R F (Ret0.startN2 (_root_.Executable.labels exe).label n0 c0)) := by
  let lab := (_root_.Executable.labels exe).label
  simp only [startCallIn, Bool.and_eq_true] at hin
  have esp2 := label_labelGap hp hin.2
  have hlo48 : R.lo ≤ -48 := by omega
  refine SegW.seq (start_seg_ofW hp hend hstart hK hF hR hal hlo48 hhi (nC := Ret0.startN1 lab c0) rfl rfl hW.start
      fun _ _ h => h)
    (SegW.seq (Q := At exe endPc R F (startNC lab c0)) ?_ ?_)
  · -- the call's block
    refine seg_oneW (seg_ndW (by simp [startCall]) startCall_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1 rfl) hW.blk fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [Ret0.startN1, Ret0.startNC]; rw [startCall_run]
    · dsimp only [Ret0.startN1, Ret0.startNC]; rw [startCall_run]; rfl
    · dsimp only [Ret0.startN1, Ret0.startNC] at hJ ⊢; rw [startCall_run]
      refine ⟨hJ, rfl, rfl, ?_⟩
      simp only [ofInt_bmod]
      rw [show lab ".L0_scc_rt_start.sp2" = _ from esp2,
        show Int64.ofNat (4 * 13) = Int64.ofNat (4 * 9) + 16 from rfl, ← Int64.add_assoc, Int64.toBitVec_add,
        show ∀ y : Int, y + 4 + 4 + 4 + 4 = y + 16 from fun y => by omega, BitVec.ofInt_add,
        Spike.Lib.int64_ofInt_toInt]; rfl
  · -- `scc_rt_alloc_tcb`
    refine seg_oneW (call_nd_FWK (KC := False) (lo' := -192) (hi' := 0) (M := fun _ => True)
      (Ne := fun g => tcbN lab ⟨g, n0, c0⟩ .e) (Ex := fun g => tcbX lab ⟨g, n0, c0⟩)
      hR hal hF (by show R.lo ≤ -48 + -192; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, h30⟩, ⟨-, -, -, h30', -⟩⟩ := hg'
        exact (allocTcb_segW hp hend hat hF' hR' hal' hlo' hhi' hFF ⟨g', n0, c0⟩ hn hhdr htcb
          fun i => (hW.tcb g' (h30'.symm.trans h30) i).mono hFF).mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨rfl, h0, h1, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl,
        rfl, rfl, rfl, rfl, h0, h1⟩
    · rintro g x σC c σx c' σR ⟨-, -, -, h30⟩ ⟨-, -, -, h30', -⟩ ⟨rfl, hPost⟩ hregs - -
      refine .inl ⟨(), ?_, rfl, rfl, ?_⟩
      · show lab ".L0_scc_rt_start.sp2" = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2

/-- **`scc_rt_start` from `.sp2` to the switch, inside `W`, the take its
outside move** (`start_sp2_sw_seg`, its states' obligations `hW`, with
`thread_init_segW` at the call): at the switch the stack range `rS` is in
private memory (`StackM`). Given the take's facts at the region (`hRS`,
`hfit`, `hout`, `hFt`). -/
theorem startSp2Sw_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hin : startTailIn prog = true) (hti : ThreadInit.threadInitIn prog = true)
    (hsp : tiSpIn prog = true) (hst : StackTake.stackTakeIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hW : Sp2W W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (Ret0.startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN5 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  let top := stacksA lab + k0 + 16384#64
  simp only [startTailIn, Bool.and_eq_true] at hin
  have esp3 := label_labelGap hp hin.1.1.1.1.2
  have hlo48 : R.lo ≤ -48 := by omega
  have hSM := stackM_stable hfit hout
  have hF2 : FStable R (fun m => F m ∧ StackM rS m) := fun m m' h hd => ⟨hF m m' h.1 hd, hSM m m' h.2 hd⟩
  -- `scc_rt_thread_init`'s region, and `rS` off it
  have hb' := Region.callee_base (hi' := 0) hR (show R.lo ≤ -48 + -256 by omega) (by decide)
    (show (-48 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48) (-256) 0).Off k → ∀ i < 8,
      (R.callee (-48) (-256) 0).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ -48 + -256 by omega) (show (-48 : Int) + 0 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48) (-256) 0).base.toNat + (R.callee (-48) (-256) 0).lo ∨
        ((R.callee (-48) (-256) 0).base.toNat : Int) + (R.callee (-48) (-256) 0).hi ≤ a := fun a h8 ha ha7 => by
    show (a : Int) + 8 ≤ ((R.callee (-48) (-256) 0).base.toNat : Int) + -256 ∨
      ((R.callee (-48) (-256) 0).base.toNat : Int) + 0 ≤ a
    rcases hout a h8 ha ha7 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  refine SegW.seq (Q := At exe endPc R F (startNC2 lab tcb c0)) ?_
    (SegW.seq (Q := At exe endPc R (fun m => F m ∧ StackM rS m) (Ret0.startN3 lab tcb top c0)) ?_
      (SegW.seq (Q := At exe endPc R (fun m => F m ∧ StackM rS m) (Ret0.startN4 lab tcb top c0)) ?_ ?_))
  · -- `.sp2`'s block
    refine seg_oneW (seg_ndW (by simp [startCall2]) startCall2_ok hF hR hal hlo48 hhi
      (code_of hp hend hin.1.1.1.1.1 (ofNat4_zero _)) hW.b2 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [Ret0.startN2, startNC2]; rw [startCall2_run]
    · dsimp only [Ret0.startN2, startNC2]; rw [startCall2_run]; rfl
    · dsimp only [Ret0.startN2, startNC2] at hJ ⊢; rw [startCall2_run]
      obtain ⟨rfl, h0⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
      · simp [Spike.Lib.upd_apply, h0, Spike.Lib.int64_ofInt_toInt]; try rfl
      · simp [Spike.Lib.upd_apply, h0]; try rfl
      · simp only [ofInt_bmod]
        rw [show lab sp3L = _ from esp3, show Int64.ofNat (4 * 3) = 12 from rfl, Int64.toBitVec_add,
          show ∀ y : Int, y + 4 + 4 + 4 = y + 12 from fun y => by omega, BitVec.ofInt_add,
          Spike.Lib.int64_ofInt_toInt]; rfl
  · -- `scc_rt_thread_init`
    refine seg_oneW (call_nd_FW (lo' := -256) (hi' := 0) (M := StackM rS)
      (Ne := fun g => tiN lab ⟨g, tcb, k0, c0⟩ .e) (Ex := fun g => tiX lab ⟨g, tcb, k0, c0⟩)
      hR hal hF (by show R.lo ≤ -48 + -256; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide)
      (TakeK.kstable hFt)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h, hM⟩)
      (fun R' F' hR' hal' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h30⟩, ⟨-, -, -, h30', -⟩⟩ := hg'
        exact (threadInit_segW hp hend hti hsp hst hF' hR' hal' hlo' hhi' hFF' ⟨g', tcb, k0, c0⟩ hk hfld htk
          (fun i => (hW.ti g' (h30'.symm.trans h30) i).mono hFF') hRS' hfit hout'
          (takeMem_of_kstable hK' exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, h0, -⟩, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, -, h32⟩, h30⟩ ⟨-, -, -, h30', -⟩ ⟨rfl, hPost⟩ hregs - hslot
      refine .inl ⟨(), ?_, rfl, rfl, ?_, ?_⟩
      · show lab sp3L = Int64.ofBitVec g.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · show σR.regs.X0.toBitVec = _
        rw [hregs]; exact hPost.2.2.2
      · rw [hslot (-32) ⟨by decide, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [startNC2] at h; omega]
        exact h32
  · -- `.sp3`'s block
    refine seg_oneW (seg_ndW (by simp [startSw0]) startSw0_ok hF2 hR hal hlo48 hhi
      (code_of hp hend hin.1.1.1.2 (ofNat4_zero _)) hW.b3 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [Ret0.startN3, Ret0.startN4]; rw [startSw0_run]; simp only [Int64.add_assoc]; rfl
    · dsimp only [Ret0.startN3, Ret0.startN4]; rw [startSw0_run]; rfl
    · dsimp only [Ret0.startN3, Ret0.startN4] at hJ ⊢; rw [startSw0_run]
      obtain ⟨rfl, h0, h32⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩ <;> simp [Spike.Lib.upd_apply, h0, h32]
  · -- `msr tpidr_el0, x10`
    refine seg_oneW (si_ndW (si := .msr .X10) hF2 (code_of hp hend hin.1.1.2 rfl) hW.msr fun σ c hJ =>
      ⟨c, .refl c, .inl ⟨(), (ofNat4_succ' _ 4).symm, rfl, ?_⟩⟩)
    obtain ⟨rfl, h9, h10⟩ := hJ
    refine ⟨rfl, h9, ?_⟩
    show UInt64.ofBitVec (σ.regs.getRegOrZr (.low (.reg .X10) .W64)) = _
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]; exact congrArg UInt64.ofBitVec h10

end StartProof

/-! ## From the switch on, `scc_rt_main` parametric -/

section SwitchU

/-- No write inside the new region (depth `L`) breaks `swF`, when the limit
word lies outside the region below `top`. -/
theorem swF_stableL {top a v : BitVec 64} {L : Int} (hfit : a.toNat + 8 ≤ 2 ^ 64)
    (hout : (a.toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ a.toNat) :
    FStable (swR v (-L) 0) (swF top a v) := by
  rintro m m' ⟨rfl, h⟩ hd
  exact ⟨rfl, (hd a hfit hout).trans h⟩

/-- **The frame condition after the switch** into a region of depth `L`:
`swF`, and the stack range off the new region in private memory. -/
def swFSL (L : Int) (rS : Scc.Sem.Range) (top a v : BitVec 64) (m : MachineData) : Prop :=
  swF top a v m ∧ StackOff rS (swR v (-L) 0) m

/-- `movz x29, #0; bl scc_rt_main` at any offsets: covered. -/
theorem startMain_okL (lo hi : Int) : Flow.okBlk lo hi SO.entry startMain = true := by
  simp [Flow.okBlk, startMain, Flow.classify, Flow.AI.ok, Flow.RegOnly, Flow.soReg, Flow.AI.isTerm, SO.entry,
    Flow.regDst, Flow.SO.write, Flow.zrB, Flow.AI.so]

/-- **The switch's and `scc_rt_main`'s states inside `W`**, `scc_rt_main`
parametric (`mc`) and its user function an interface: the switch, the block
after it, `scc_rt_main`'s own states and the user function's segment, in the
new region of depth `L` (for every value of the new `sp`). -/
structure SwUW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2)
    (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int) (mc : MainCode) (D : Int) (ZU : Int64)
    (Post : Ctl → BitVec 64 → Prop) : Prop where
  sw : NodeW W K exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
    (startN6 (_root_.Executable.labels exe).label tcb top c0) startMain
  main : ∀ v, MainUW W K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) ms mc Post
    ⟨top, UInt64.ofBitVec tcb, c0⟩
  user : ∀ v, UserCallW W K p lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
    mc.fn mc.Z D ZU Post ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **From the switch on, inside `W`, `scc_rt_main` parametric** (hand
`start_switch_segW`): the switch into the new region of depth `L` (holding
`scc_rt_main`'s frame `Z` and the user function's `D`), `bl scc_rt_main`,
then `mainU_segW`. The new stack's cells hold values at the switch since the
stack range is in private memory then (`hFS`) and the new region lies in it
(`hsub`). -/
theorem startSwitchU_segW {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hin : startTailIn prog = true)
    {mc : MainCode} (hmain : mainUIn prog mc = true) (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : mc.Z.toInt + D ≤ L)
    (hK : ms.K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec))
    (hlimU : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : SwUW W K p lbl exe endPc R F ms rS tcb top c0 L mc D ZU Post)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (UInt64.ofBitVec tcb)
  have hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-L) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k := by
    intro m hD
    refine ⟨fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8).getD 0), fun k hk => ?_⟩
    obtain ⟨h8, ha, ha7⟩ := hsub k hk
    have h := hFS m hD _ h8 ha ha7
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, hj, by simp only [hj, Option.getD_some]⟩
  refine sw_seqW (lo := -L) (hi := 0) (F' := swFSL L rS top a) (n' := startN6 lab tcb top c0)
    (sw_ndW rfl (code_of hp hend hin.1.2 rfl) (ofNat4_succ' _ 5).symm rfl hW.sw fun m σ c _ hD hJ => ?_)
    fun v hv hR => ?_
  · obtain ⟨rfl, h9, htp⟩ := hJ
    obtain ⟨hsp, -, htp'⟩ := swStep (startN5 lab tcb top c).o ((startN5 lab tcb top c).pc + Int64.ofNat 4) σ
    rw [hsp, h9]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨h16, hok, ⟨⟨rfl, hlimM.unmapped m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl, hsp.trans h9,
      htp'.trans htp⟩
  · let g : MainG := ⟨top, UInt64.ofBitVec tcb, c0⟩
    have hF2 : FStable (swR v (-L) 0) (swFSL L rS top a v) := fun m m' h hd =>
      ⟨swF_stableL hfit hout m m' h.1 hd, stackOff_stable hfitS m m' h.2 hd⟩
    refine SegW.seq (Q := At exe endPc (swR v (-L) 0) (swFSL L rS top a v) (mainN0 lab g))
      (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL (-L) 0) hF2 hR hv (Int.le_refl _) (Int.le_refl _)
        (code_of hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      (mainU_segW hp hend hmain hZ16 hZ hk hD0 hD8 hK hF2 hR hv (show -L ≤ -mc.Z.toInt - D by omega)
        (Int.le_refl _) g ⟨hlimM.rt, hlimM.mp, fun _ h => h.1.2, hlimM.room⟩
        ⟨hlimU.rt, hlimU.mp, fun _ h => h.1.2, hlimU.room⟩ (hW.user v)
        (fun s c x hP hAt => hexit _ _ s c x hP hAt) (hW.main v))
    · dsimp only [startN6, mainN0]; rw [startMain_run]
    · dsimp only [startN6, mainN0]; rw [startMain_run]; rfl
    · dsimp only [startN6, mainN0] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩ <;> simp_all [setXReg_TPIDR, Reg64s.setXReg_SP] <;> rfl

end SwitchU

/-! ## `scc_rt_start` whole, `scc_rt_main` parametric -/

section StartU

/-- **`scc_rt_start`'s states inside `W`**, `scc_rt_main` parametric: up to
`.sp2`, from `.sp2` to the switch, and from the switch on (with the stack
range in private memory) into the new region of depth `L`. -/
structure StartAllUW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isaLSE2) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl) (L : Int)
    (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) : Prop where
  s1 : Sp0W W K exe endPc R F n0 c0
  s2 : Sp2W W K exe endPc R F rS n0 k0 c0
  s3 : SwUW W K p lbl exe endPc R (fun m => F m ∧ StackM rS m) ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L mc D ZU Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_start` never returns, inside `W`, the take its outside move,
`scc_rt_main` parametric** (hand `start_segW`): `startSp2_segW`, then
`startSp2Sw_segW`, then `startSwitchU_segW`, in any valid layout of any
program with the runtime's code checks and `scc_rt_main`'s (`hmain`). -/
theorem startU_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hcall : startCallIn prog = true) (hstart : startIn prog = true)
    (hat : AllocTcb.allocTcbIn prog = true) (htail : startTailIn prog = true)
    (hti : ThreadInit.threadInitIn prog = true) (hsp : tiSpIn prog = true)
    (hst : StackTake.stackTakeIn prog = true)
    {mc : MainCode} (hmain : mainUIn prog mc = true) (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hkm : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : mc.Z.toInt + D ≤ L)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (h16 : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - mc.Z.toBitVec - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllUW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl exe endPc R F ms rS
      n0 k0 c0 L mc D ZU Post)
    {Q : Frag isaLSE2} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (startSp2_segW hp hend hcall hstart hat hK hF hR hal (by omega) hhi n0 c0 hn hhdr htcb hW.s1).seq
    ((startSp2Sw_segW hp hend htail hti hsp hst hF hR hal hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS
      hFt).seq
      (startSwitchU_segW hp hend htail hmain hZ16 hZ hkm hD0 hD8 hL hK _ _ c0 h16 hok (fun _ h => h.2) hfitS hsub
        hfit hout (hlimM.mono fun _ h => h.1) (hlimU.mono fun _ h => h.1) hexit hW.s3))

end StartU

end Spike.Lib.A64.Rt
