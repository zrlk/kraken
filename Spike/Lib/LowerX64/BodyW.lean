/-
**A lowered body's blocks inside the consumer's facts** (x86-64); the twin
of `Spike/Lib/LowerA64/BodyW.lean`: the `hWb`/`hWs` obligations of
`fn0_seg` (`Spike/Lib/LowerX64/Fn.lean`), discharged for any program with
an instance's facts (`InstOk`, `Spike/Lib/Rt/X64RtW.lean`).

The segment's controls move with the source (each node's control a local
run from the function's entry `c0` reaches), so the fragment here is the
one before `SegW.lag` (`Spike/Lib/SegLag.lean`) holds the control back at
`c0`: `BodyW0` pairs a `Quiet` control with `SFacts` at `c0`. Under
`SegW.lag` with `C := (· = c0)` it gives `SFacts` at the held-back control
(`bodyW0_lag`).

- `blkAt_of_bodyBlks`, `mem_bodyBlks`, `blockAt_of_bodyBlks`,
  `okBlk_bodyBlks`: a block of the body is the checked `+`'s, its store or
  the return's, at the sizes `bodyIn` checks; `bodyIn` places it; its cover
  at the body's offsets.
- `blkW_body0`: a block of the body at any node with the body's offsets
  whose controls a local run from `c0` reaches, the saved pair `fp`/`ra`
  in their cells, is inside `BodyW0` (`blkW_postO` at `c0`; the return
  block's `ret` to `ra` by `FrJ`, the others without `ret`).
- `hWb_of`, `hWs_of`: `fn0_seg`'s `hWb`, `hWs` from it.
- `quiet_c0`: their `hQ` for an `Accepted0` program from the consumer's
  start `X64Consumer.c0` (`quiet_of_accepted0`, `Spike/Lib/Quiet0.lean`).

Where x86-64 differs from AArch64:
- a block of the body is its directives zipped with the sizes the listing
  gives (`sizesAt`), which may be fewer; `bodyIn` checks they are not, so
  `mem_bodyBlks` and `okBlk_bodyBlks` take `bodyIn` (AArch64: the blocks
  are the directives, from the context alone), and `blockAt_of_bodyBlks`
  gives `blockAtB`;
- the body's offsets are `oB fr` (`%rbp`-based) and its cover is in
  `[-size, 16)`, so the region's top is at least `16` (AArch64: `0`); the
  frame's hypotheses are `FrameOk fr` and `fr.size ≤ 2 ^ 31` (no `% 16`);
- the region's base is `8`-aligned (`blkW_postO`'s `hR8`; AArch64: `16`);
- the return block's target is the cell `8` of the frame record
  (`arun_epi`; AArch64: `x30` restored from the cell `-8`).
-/
import Spike.Lib.LowerX64.BodyPh
import Spike.Lib.LowerX64.BodyIn
import Spike.Lib.LowerX64.Node
import Spike.Lib.Rt.X64RtW
import Spike.Lib.SegLag
import Spike.Lib.Quiet0

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (blockAtB)
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (CFacts SFacts blkPh hret_of_run noRetBlk noRet_false Own Lbl)
open Spike.Lib.X64.Rt (InstOk blkW_postO)
open Spike.Lib.X64.Flow.Ret0 (StackOff)

/-! ## The body's blocks -/

section Blocks

variable {cells : List (Directive × Nat)} {fr : Scc.Emit.X64.Frame} {l : String}

/-- **A block of the body is placed**: its directives `ds` (the checked
`+`'s, its store or the return's) at the sizes the listing gives, which
`blkAt` checks at its offset. -/
theorem blkAt_of_bodyBlks :
    ∀ {is : List Scc.IR.Inst} {k : Nat} {ws : List Scc.IR.Operand} {j : Nat} {blk : List (Directive × Nat)},
    bodyIn cells fr l k is ws = true → (j, blk) ∈ bodyBlks cells fr l k is ws →
    ∃ ds, blk = ds.zip (sizesAt cells l j ds.length) ∧ blkAt cells l j ds = true ∧
      ((∃ a b la lb, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧ ds = addDirs fr la lb) ∨
        (∃ d o, rsOf fr d = some o ∧ ds = [stDir o]) ∨
        (∃ w lw, getOp fr .rax w = .ok lw ∧ ds = retDirs lw))
  | [], k, ws, j, blk, hi, h => by
    match ws, hi, h with
    | [w], hi, h =>
      cases hg : getOp fr .rax w with
      | error e => simp [bodyBlks, hg] at h
      | ok lw =>
        simp only [bodyBlks, hg, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [bodyIn, hg] at hi
        exact ⟨_, rfl, hi, .inr (.inr ⟨w, lw, hg, rfl⟩)⟩
    | [], _, h => simp [bodyBlks] at h
    | _ :: _ :: _, _, h => simp [bodyBlks] at h
  | i :: is, k, ws, j, blk, hi, h => by
    cases i
    case addChk d a b =>
      cases ha : getOp fr .rax a <;> cases hb : getOp fr .rcx b <;> cases hd : rsOf fr d <;>
        simp only [bodyBlks, ha, hb, hd, List.not_mem_nil] at h
      case ok.ok.some la lb o =>
        simp only [bodyIn, ha, hb, hd, Bool.and_eq_true] at hi
        obtain ⟨⟨h1, h2⟩, h3⟩ := hi
        simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
        · exact ⟨_, rfl, h1, .inl ⟨a, b, la, lb, ha, hb, rfl⟩⟩
        · exact ⟨[stDir o], rfl, h2, .inr (.inl ⟨d, o, hd, rfl⟩)⟩
        · exact blkAt_of_bodyBlks h3 h
    all_goals simp [bodyBlks] at h

/-- **A block of the body** is the checked `+`'s, its store or the
return's, at sizes of its length. -/
theorem mem_bodyBlks {is : List Scc.IR.Inst} {k : Nat} {ws : List Scc.IR.Operand} {j : Nat}
    {blk : List (Directive × Nat)} (hi : bodyIn cells fr l k is ws = true) (h : (j, blk) ∈ bodyBlks cells fr l k is ws) :
    (∃ a b la lb zs, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
        zs.length = (addDirs fr la lb).length ∧ blk = (addDirs fr la lb).zip zs) ∨
      (∃ d o z, rsOf fr d = some o ∧ blk = [(stDir o, z)]) ∨
      (∃ w lw zs, getOp fr .rax w = .ok lw ∧ zs.length = (retDirs lw).length ∧ blk = (retDirs lw).zip zs) := by
  obtain ⟨ds, rfl, hb, hs⟩ := blkAt_of_bodyBlks hi h
  simp only [blkAt, Bool.and_eq_true, beq_iff_eq] at hb
  rcases hs with ⟨a, b, la, lb, ha, hb', rfl⟩ | ⟨d, o, hd, rfl⟩ | ⟨w, lw, hg, rfl⟩
  · exact .inl ⟨a, b, la, lb, _, ha, hb', hb.1, rfl⟩
  · obtain ⟨z, hz⟩ := length_one hb.1
    exact .inr (.inl ⟨d, o, z, hd, by rw [hz]; rfl⟩)
  · exact .inr (.inr ⟨w, lw, _, hg, hb.1, rfl⟩)

/-- **`bodyIn` places every block of the body** at its offset. -/
theorem blockAt_of_bodyBlks {is : List Scc.IR.Inst} {k : Nat} {ws : List Scc.IR.Operand} {j : Nat}
    {blk : List (Directive × Nat)} (hi : bodyIn cells fr l k is ws = true) (h : (j, blk) ∈ bodyBlks cells fr l k is ws) :
    blockAtB cells l j blk = true := by
  obtain ⟨ds, rfl, hb, -⟩ := blkAt_of_bodyBlks hi h
  simp only [blkAt, Bool.and_eq_true] at hb
  exact hb.2

/-- **A block of the body is covered** at the body's offsets. -/
theorem okBlk_bodyBlks (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {is : List Scc.IR.Inst} {k : Nat}
    {ws : List Scc.IR.Operand} {j : Nat} {blk : List (Directive × Nat)} (hi : bodyIn cells fr l k is ws = true)
    (h : (j, blk) ∈ bodyBlks cells fr l k is ws) :
    okBlk (-(fr.size : Int)) 16 (oB fr) blk = true := by
  rcases mem_bodyBlks hi h with ⟨a, b, la, lb, zs, ha, hb, hz, rfl⟩ | ⟨d, o, z, hd, rfl⟩ |
    ⟨w, lw, zs, hg, hz, rfl⟩
  · obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    have hz' := hz
    rw [addDirs, dirs_append, dirs_append, hda, hdb, dirs_addChecked] at hz'
    match zs, hz' with
    | [z0, z1, z2, z3], _ =>
    have hsplit : (addDirs fr la lb).zip [z0, z1, z2, z3] =
        (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs (addChecked (ovfL fr))).zip [z2, z3]) := by
      rw [addDirs, dirs_append, dirs_append, hda, hdb, dirs_addChecked]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_addChecked (by simp [oB, SO.kill, rm]) _
  · obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hd
    have ho : (Int64.ofInt o).toInt = o := toInt_ofInt_small (by omega) (by omega)
    have hc : classify (stDir o) = some (AI.st .rbp (Int64.ofInt o) .rax) := rfl
    simp only [okBlk, hc, AI.ok, AI.isTerm, oB, SO.get, lk, ho, offOk]
    simp
    omega
  · obtain ⟨dl, hdl⟩ := dirs_getOp hg
    have hds : retDirs lw = dirs lw ++ epi := by rw [retDirs, dirs_append, dirs_epiItems]
    rw [hds, hdl] at hz
    match zs, hz with
    | [z0, z1, z2, z3], _ =>
    have hsplit : (retDirs lw).zip [z0, z1, z2, z3] = (dirs lw).zip [z0] ++ epi.zip [z1, z2, z3] := by
      rw [hds, hdl]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) hg (by simp [hdl])]
    exact okBlk_epi (by omega) z1 z2 z3

end Blocks

/-- **No `ret` but at the end**: in a covered block a `ret` is the last
instruction, so a block whose last instruction is not one has none. -/
theorem noRet_of_last (lab : String → Int64) {lo hi : Int} {blk : List (Directive × Nat)} {am : AM}
    (h : okBlk lo hi am.so blk = true) (hl : ∀ d, blk.getLast? = some d → classify d.1 ≠ some .ret) :
    ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret → False := by
  intro k hk hr
  obtain ⟨a, ha, -, hterm⟩ := okBlk_get lab (am := am) h hk
  rw [hr] at ha
  cases ha
  by_cases hk1 : k + 1 < blk.length
  · exact absurd (hterm hk1) (by simp [AI.isTerm])
  · have he : blk.getLast? = some blk[k] := by
      rw [List.getLast?_eq_getElem?]
      simp only [show blk.length - 1 = k by omega, List.getElem?_eq_getElem hk]
    exact hl _ he hr

/-! ## The blocks inside `SFacts` at the entry -/

/-- **The body's fragment before the lag**: a `Quiet` control, the state
in `SFacts` at the function's entry control `c0`. -/
def BodyW0 (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (rS : Range) (Tk : State → Prop) (lbl : Lbl)
    (c0 : Ctl) : Frag isa :=
  fun s c => Quiet c ∧ SFacts Λ μ own rS Tk lbl s c0

/-- **The lag of a segment inside `BodyW0`**: with the control held back at
`c0`, the segment is inside `SFacts` (`SegW.lag`, `C := (· = c0)`), under a
memory side with the kernel model `Scc.Sem.X64.abi` (`hK`: `SFacts`' default write
tail, no `write`, rules out a `write` to the output). -/
theorem bodyW0_lag {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
    {c0 : Ctl} {K : State → State → Prop} {p : Prog} {al : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isa} {P Q : Frag isa} (hK : ms.K = some Scc.Sem.X64.abi)
    (h : SegW (BodyW0 Λ μ own rS Tk lbl c0) K p al ms P Q) :
    SegW (fun s c => SFacts Λ μ own rS Tk lbl s c) K p al ms (Lag p (· = c0) P) (Lag p (· = c0) Q) :=
  h.lag (fun _ _ h => h.1)
    (fun _ _ h K' hK' ha buf n hd => by
      rw [hK] at hK'; cases hK'
      exact h.2.wrTail ha 1 buf n hd)
    fun _ _ _ h _ hc => hc ▸ h.2

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl} {fr : Scc.Emit.X64.Frame} {l : String}
  {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} {fp ra : BitVec 64}

/-- **A block of the body is inside `BodyW0`** at any node with the body's
offsets (`hno`) whose controls a local run from `c0` reaches, the saved
pair in its cells (`hJ`): `blkW_postO` at `c0` (its facts `hC0`), the
block placed by `bodyIn` (`hbody`), its phase check `bodyPhOk` with no dead
target and the return address `ra` (`hph`), the controls a local run from
`c0` reaches `Quiet` (`hQ`). -/
theorem blkW_body0 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) (hbody : bodyIn cells fr l 0 is ws = true)
    (hph : bodyPhOk okPc ph (fun _ => false) lab cells fr l is ws (Int64.ofBitVec ra) = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {n : ND} (hno : n.o = oB fr) (hJ : ∀ σ c, n.J σ c → LocalRun p c0 c ∧ FrJ fp ra σ.slot)
    {blk : List (Directive × Nat)} (hin : InBody lab cells fr l is ws n.pc blk) :
    BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F n blk := by
  have hphb := blkPh_of_inBody hin hph
  obtain ⟨j, hpc, hj⟩ := hin
  have hok : okBlk (-(fr.size : Int)) 16 n.o blk = true := hno ▸ okBlk_bodyBlks hf h1 hbody hj
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩
  have hret : ∀ σ c, n'.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n'.pc, n'.o, σ⟩).σ.slot
        (arun lab (blk.take k) ⟨n'.pc, n'.o, σ⟩).so.sp) = Int64.ofBitVec ra := by
    rcases mem_bodyBlks hbody hj with ⟨a, b, la, lb, zs, ha, hb, hz, rfl⟩ | ⟨d, o, z, hd, rfl⟩ |
      ⟨w, lw, zs, hg, hz, rfl⟩
    · intro σ _ _ k hk hr
      refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd => ?_) k hk hr).elim
      obtain ⟨da, hda⟩ := dirs_getOp ha
      obtain ⟨db, hdb⟩ := dirs_getOp hb
      rw [addDirs, dirs_append, dirs_append, hda, hdb, dirs_addChecked] at hz hd
      match zs, hz with
      | [z0, z1, z2, z3], _ =>
      simp only [List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_left,
        List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hd
      subst hd
      rw [show X64.classify (Scc.Emit.X64.i64 (.jcc .c (ovfL fr))) = some (.jcc .c (ovfL fr)) from rfl]
      simp
    · have hn : noRetBlk [(stDir o, z)] = true := by
        simp [noRetBlk, show classify (stDir o) = some (AI.st .rbp (Int64.ofInt o) .rax) from rfl]
      exact fun _ _ _ k hk hr => (noRet_false hn k hk hr).elim
    · obtain ⟨dl, hdl⟩ := dirs_getOp hg
      have hds : retDirs lw = dirs lw ++ epi := by rw [retDirs, dirs_append, dirs_epiItems]
      rw [hds, hdl] at hz
      match zs, hz with
      | [z0, z1, z2, z3], _ =>
      have hsplit : (retDirs lw).zip [z0, z1, z2, z3] = (dirs lw).zip [z0] ++ epi.zip [z1, z2, z3] := by
        rw [hds, hdl]; rfl
      refine hret_of_run hok fun σ c ⟨_, c1, hJ1⟩ => ?_
      have hfj := (hJ σ c1 hJ1).2
      show (arun lab ((retDirs lw).zip [z0, z1, z2, z3]) ⟨n.pc, n.o, σ⟩).pc = _
      rw [hno, hsplit, arun_append]
      obtain ⟨v, -, hrun⟩ := arun_getOp hf h1 (by decide) hg lab n.pc σ (zs := [z0]) (by simp [hdl])
      rw [hrun, show oB fr = oR (-(fr.size : Int)) from rfl]
      rw [(arun_epi lab (n.pc + Int64.ofNat [z0].sum) (-(fr.size : Int))
        { σ with regs := σ.regs.set64 .rax v } z1 z2 z3).1]
      exact congrArg Int64.ofBitVec hfj.2
  have H := blkW_postO (n := n') (dead := fun _ => false) (ra := Int64.ofBitVec ra) (l := l) (off := j) hI
    (blockAt_of_bodyBlks hbody hj) hpc.symm hok hR hlo hhi hR8 hl hh (fun _ _ h => h.1 ▸ hC0) (hpc ▸ hphb)
    hret (fun _ _ _ => rfl) hsub hfit hFO
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨hW, hK⟩ := H s σ c0 he hn hd hp hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
  exact ⟨⟨hQ c (hJ σ c hJn).1, hW⟩, hK⟩

/-- **`fn0_seg`'s `hWb`**: the body's blocks at its nodes inside `BodyW0`. -/
theorem hWb_of {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) (hbody : bodyIn cells fr l 0 is ws = true)
    (hph : bodyPhOk okPc ph (fun _ => false) lab cells fr l is ws (Int64.ofBitVec ra) = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {al : WeakMem.AllocLabel → Option Nat} :
    ∀ pc t s blk, CdOf exe endPc pc blk → InBody (_root_.Executable.labels exe).label cells fr l is ws pc blk →
      BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F (bodyN p al fr fp ra c0 pc t s) blk :=
  fun _ _ _ _ _ hin => blkW_body0 hI hf h1 hbody hph hR hR8 hlo hhi hl hh hsub hfit hFO hC0 hQ rfl
    (fun _ _ (h : _ ∧ _ ∧ _) => ⟨h.2.2, h.2.1⟩) (hI.labOk ▸ hin)

/-- **`fn0_seg`'s `hWs`**: the body's blocks at its pending stores inside
`BodyW0`. -/
theorem hWs_of {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) (hbody : bodyIn cells fr l 0 is ws = true)
    (hph : bodyPhOk okPc ph (fun _ => false) lab cells fr l is ws (Int64.ofBitVec ra) = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {al : WeakMem.AllocLabel → Option Nat} :
    ∀ pc t s k blk, CdOf exe endPc pc blk → InBody (_root_.Executable.labels exe).label cells fr l is ws pc blk →
      BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F (pendN p al fr fp ra c0 pc t s k) blk :=
  fun _ _ _ _ _ _ hin => blkW_body0 hI hf h1 hbody hph hR hR8 hlo hhi hl hh hsub hfit hFO hC0 hQ rfl
    (fun _ _ (h : _ ∧ _ ∧ _) => ⟨h.2.2, h.2.1⟩) (hI.labOk ▸ hin)

end W

/-- **`hWb_of`'s and `hWs_of`'s `hQ`** for an `Accepted0` program from the
consumer's start: every control a local run reaches is `Quiet`. -/
theorem quiet_c0 {p : Prog} (hp : Scc.Lower.Accepted0 p = true) :
    ∀ c, LocalRun p Spike.Lib.X64Consumer.c0 c → Quiet c :=
  quiet_of_accepted0 hp rfl rfl

end Spike.Lib.LowerX64
