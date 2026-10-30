/-
**`scc_rt_alloc_tcb` at a header `h` with the counter's owned value at the
node's states** (AArch64): `allocTcbG_segW` with its `OwnAt` (every state
at the counter's `ldadd`) weakened to the `ldadd` node's states
(`TcbOkGA.own`). `scc_rt_alloc_tcb` runs twice in wake.w, at the same pc
with different old values (`0`, `80`), so `OwnAt` at one pc cannot hold at
an owned-words map telling the calls apart by `sp` (`ownG`); the node's
states carry the call's frame, so at them it can.

- `ownLdop_ndWA` (in `Rt.A64OwnA`): `ownLdop_ndW` with the owned value at the
  node's states;
- `TcbOkGA`: `TcbOkG` with `own` at `tcbNG q .rmw`'s states;
- `TcbOkGA.of_tcbOkG`: `TcbOkG` gives it;
- `allocTcbG_segWA`: `allocTcbG_segW` at `TcbOkGA`.
-/
import Spike.Lib.Rt.A64RtTcbG

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer

set_option linter.unusedSimpArgs false

/-- **The counter's add at `q`, owned at the `ldadd` node's states**
(`TcbOkG` with `own` at `tcbNG q .rmw`'s states in the callee's region `R`
under its frame condition `F`). -/
structure TcbOkGA (ms : MemSide isaLSE2) (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (q : TcbGG) : Prop where
  next : StOk ms F0 exe endPc (pnA (_root_.Executable.labels exe).label) (q.n0 + AllocTcb.lenOf q.h)
  own : ∀ s c, At exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .rmw) s c →
    (⟨pnA (_root_.Executable.labels exe).label, 8⟩, q.n0.setWidth 128) ∈ ms.own s

/-- `TcbOkG` (owned at every state at the pc) gives `TcbOkGA`. -/
theorem TcbOkGA.of_tcbOkG {ms : MemSide isaLSE2} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TcbGG} (h : TcbOkG ms F0 exe endPc q.h q.n0) : TcbOkGA ms F0 exe endPc R F q :=
  ⟨h.next, fun s _ hA => h.own s hA.1 hA.2.1 hA.2.2.2.1⟩

/-- `TcbOkGA` under a stronger frame condition. -/
theorem TcbOkGA.mono {ms : MemSide isaLSE2} {F0 F F' : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : TcbGG} (h : TcbOkGA ms F0 exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    TcbOkGA ms F0 exe endPc R F' q :=
  ⟨h.next, fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.own s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩⟩

section TcbProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb` inside `W` (`A64RtTcbG`'s). -/
local macro "tnodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (code_of hp hend (by simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_alloc_tcb` at `h` is one segment inside `W`, the counter
owned at the `ldadd` node's states** (`allocTcbG_segW` at `TcbOkGA`). -/
theorem allocTcbG_segWA {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hin : AllocTcb.allocTcbIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbGG) (hn : q.n0.toNat + (AllocTcb.lenOf q.h).toNat ≤ 131072)
    (hhdr : StOk ms F0 exe endPc (hdrA (_root_.Executable.labels exe).label q) (q.h ||| 1#64 <<< 36))
    (htcb : TcbOkGA ms F0 exe endPc R F q) (hW : ∀ i, TcbWG W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbXG (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin'
  have eEntry := label_labelGap hp hin'.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  refine fn_segW (N := tcbNG _ q) (E := tcbXG _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnodeW AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0 (hW TN.e)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnodeW AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0 (hW TN.entry)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnodeW AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 4 (hW TN.j1)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    rw [AllocTcb.atJ1_run]
    exact .inl ⟨TN.len, rfl, rfl, hJ⟩
  case len =>
    tnodeW AllocTcb.atLen AllocTcb.atLen_ok AllocTcb.lenL 0 (hW TN.len)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atLen_walkG (_root_.Executable.labels exe).label _ hJ
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
      exact ⟨rfl, AllocTcb.labStep_fr1G _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case arg =>
    tnodeW AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 34 (hW TN.arg)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walkG (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.rmw, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownLdop_ndWA hF (code_of hp hend hin'.1.1.1.1.1.1.1.2 rfl) htcb.own (hW TN.rmw) fun _ σ c _ _ hJ => ?_
    dsimp only [tcbNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TN.bnd, (ofNat4_succ' _ 37).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact htcb.next.mono hFF
    · simpa [ldStep, AllocTcb.Fr1G, AllocTcb.Fr0G] using hJ
    · simp [ldStep]
  case bnd =>
    tnodeW AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 38 (hW TN.bnd)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walkG (_root_.Executable.labels exe).label _ hJ h11 hn
    exact .inl ⟨TN.j2, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnodeW AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 47 (hW TN.j2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
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
      exact ⟨rfl, AllocTcb.labStep_fr2G _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case ok2 =>
    tnodeW AllocTcb.atOk AllocTcb.atOk_ok AllocTcb.okL 2 (hW TN.ok2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atOk_walkG (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.hdr, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_ndW (code_of hp hend hin'.1.2 rfl) (hW TN.hdr) fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have ha : rAddr σ.regs .X10 0 = hdrA (_root_.Executable.labels exe).label q := by
      rw [← h10]; simp [rAddr, Reg64s.getXReg]
    rw [ha, Spike.Lib.A64.Alloc.getRegOrZr_x]
    refine ⟨hhdr.rt, hhdr.mp, ?_, hhdr.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TN.ret, (ofNat4_succ' _ 29).symm, rfl, rfl, hJ⟩⟩
    have : (σ.regs.getXReg .X9).toBitVec = q.h ||| 1#64 <<< 36 := by
      rw [← h9]; simp [Reg64s.getXReg]
    rw [this]; exact hhdr.G
  case ret =>
    tnodeW AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 30 (hW TN.ret)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

end TcbProof

end Spike.Lib.A64.Rt

/-- info: 'Spike.Lib.A64.Rt.allocTcbG_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.allocTcbG_segWA
