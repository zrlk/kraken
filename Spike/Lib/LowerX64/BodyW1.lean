/-
**A call-free `Accepted1` body's blocks inside the consumer's facts**
(x86-64): `body1_seg`'s `hCd`, `hW`, `hWp` (`fn1_seg`'s `hCd`, `hWb`, `hWs`)
at the code predicate `Cd1` (`Spike/Lib/LowerX64/Blocks1.lean`), as
`Spike/Lib/LowerX64/BodyW.lean` for an `Accepted0` body; the twin of
`Spike/Lib/LowerA64/BodyW1.lean`.

- `kind1_cases`: a construct's block is a checked `+`'s, a saturating
  `-`'s, an `if`'s compare-and-branch, a store, a `jmp` or a `ret`'s, at
  sizes of its length.
- `blkW_postO'`: `blkW_postO` with the block's code given directly (`Cd1`
  places a block by `blockAt`, not `blockAtB`).
- `hret_kind1`: a construct's block returns only to the saved `ra` (`FrJ`)
  at a node with the frame's offsets.
- `blkW_body1`: a construct's block at `Cd1` at any node with the frame's
  offsets whose controls a local run from `c0` reaches, the saved pair in
  their cells, is inside `BodyW0` (only the `ret`'s block returns, to `ra`
  by `FrJ`).
- `hWb1_of`, `hWs1_of`, `cdOf_cd1`: `body1_seg`'s obligations from it;
  `quiet_c1`: their `hQ` for a main-only `Accepted1` program from the
  consumer's start (`quiet_of_accepted1main`).
-/
import Spike.Lib.LowerX64.Blocks1
import Spike.Lib.LowerX64.BodyW
import Spike.Lib.Quiet1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (blockAt)
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (CFacts SFacts blkPh hret_of_run noRetBlk noRet_false Own Lbl blkPh_sound blkW_sfacts)
open Spike.Lib.X64.Rt (InstOk owned_off)
open Spike.Lib.X64.Flow.Ret0 (StackOff stackOff_stable)

/-- **A construct's block, case by case**: a checked `+`'s, a saturating
`-`'s or an `if`'s compare-and-branch (operand loads), a store, a `jmp`, or
a `ret`'s, at sizes of its length. -/
theorem kind1_cases {fr : Scc.Emit.X64.Frame} {blk : List (Directive × Nat)} (hk : Kind1 fr blk) :
    (∃ a b la lb zs, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      ((zs.length = (addDirs fr la lb).length ∧ blk = (addDirs fr la lb).zip zs) ∨
        (zs.length = (subDirs la lb).length ∧ blk = (subDirs la lb).zip zs) ∨
        ∃ T, zs.length = (brDirs la lb T).length ∧ blk = (brDirs la lb T).zip zs)) ∨
      (∃ d o z, rsOf fr d = some o ∧ blk = [(stDir o, z)]) ∨
      (∃ F z, blk = (jmpDirs F).zip [z]) ∨
      (∃ w lw zs, getOp fr .rax w = .ok lw ∧ zs.length = (retDirs lw).length ∧ blk = (retDirs lw).zip zs) := by
  have e := zip_fst_snd blk
  have hl : (blk.map (·.2)).length = (blk.map (·.1)).length := by simp
  rcases hk with ⟨a, b, la, lb, ha, hb, h | h | ⟨T, h⟩⟩ | ⟨d, o, hd, h⟩ | ⟨F, h⟩ | ⟨w, lw, hg, h⟩ <;>
    rw [h] at e hl
  · exact .inl ⟨a, b, la, lb, _, ha, hb, .inl ⟨hl, e.symm⟩⟩
  · exact .inl ⟨a, b, la, lb, _, ha, hb, .inr (.inl ⟨hl, e.symm⟩)⟩
  · exact .inl ⟨a, b, la, lb, _, ha, hb, .inr (.inr ⟨T, hl, e.symm⟩)⟩
  · obtain ⟨z, hz⟩ := length_one (zs := blk.map (·.2)) (by simpa using hl)
    rw [hz] at e
    exact .inr (.inl ⟨d, o, z, hd, e.symm⟩)
  · obtain ⟨z, hz⟩ := length_one (zs := blk.map (·.2)) (by simpa [jmpDirs] using hl)
    rw [hz] at e
    exact .inr (.inr (.inl ⟨F, z, e.symm⟩))
  · exact .inr (.inr (.inr ⟨w, lw, _, hg, hl, e.symm⟩))

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl} {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64}

omit [Kraken.Executable.ValidLayout exe] in
/-- **`blkW_postO` at a block's code** (`hcode`) rather than its
`blockAtB` placement: the block covered (`hok`) and passing its phase check
at its pc (`hph`) is inside `SFacts`, the words of `rS` off its region from
the frame condition (`hFO`). -/
theorem blkW_postO' {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hlo hhi hC hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact owned_off hR hR8 hl hh hsub (stackOff_stable hfit _ _ (hFO _ hF) hD) hc

/-- **`body1_seg`'s `hCd`**: a block at `Cd1` is in the code. -/
theorem cdOf_cd1 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {ra' : Int64} :
    ∀ pc blk, Cd1 cells okPc ph lab fr ra' pc blk → CdOf exe endPc pc blk := by
  rintro _ _ ⟨_, l, k, off, hpc, hb, _⟩ s hs hn
  have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
  rwa [hI.labOk, hpc] at this

omit [Kraken.Executable.ValidLayout exe] in
/-- **A construct's block returns only to the saved `ra`** (`blkW_postO`'s
`hret`): at a node with the frame's offsets (`hno`) whose controls have the
saved pair in their cells (`hfj`), only the `ret`'s block has a `ret`, its
return address the slot `8`. -/
theorem hret_kind1 (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {n : ND} (hno : n.o = oB fr)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List (Directive × Nat)} (hk : Kind1 fr blk) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) = Int64.ofBitVec ra := by
  have hok : okBlk (-(fr.size : Int)) 16 n.o blk = true := hno ▸ kind1_ok hf h1 hk
  rcases kind1_cases hk with ⟨a, b, la, lb, zs, ha, hb', ⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨T, hz, rfl⟩⟩ |
    ⟨d, o, z, hd, rfl⟩ | ⟨F, z, rfl⟩ | ⟨w, lw, zs, hg, hz, rfl⟩
  · intro σ _ _ k hk hr
    refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd => ?_) k hk hr).elim
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb'
    rw [addDirs, dirs_append, dirs_append, hda, hdb, dirs_addChecked] at hz hd
    match zs, hz with
    | [z0, z1, z2, z3], _ =>
    simp only [List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_left,
      List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hd
    subst hd
    rw [show X64.classify (Scc.Emit.X64.i64 (.jcc .c (ovfL fr))) = some (.jcc .c (ovfL fr)) from rfl]
    simp
  · intro σ _ _ k hk hr
    refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd => ?_) k hk hr).elim
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb'
    rw [subDirs, dirs_append, dirs_append, hda, hdb, dirs_subSat] at hz hd
    match zs, hz with
    | [z0, z1, z2, z3, z4], _ =>
    simp only [List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_left,
      List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hd
    subst hd
    simp [Scc.Emit.X64.i64, Scc.Emit.X64.op, Scc.Emit.X64.xr, Scc.Emit.X64.rax64, Scc.Emit.X64.lw,
      X64.classify, RegOnly]
  · intro σ _ _ k hk hr
    refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd => ?_) k hk hr).elim
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb'
    rw [brDirs, dirs_append, dirs_append, hda, hdb, dirs_cmpJe] at hz hd
    match zs, hz with
    | [z0, z1, z2, z3], _ =>
    simp only [List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_left,
      List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hd
    subst hd
    rw [show X64.classify (Scc.Emit.X64.i64 (.jcc .z T)) = some (.jcc .z T) from rfl]
    simp
  · have hn : noRetBlk [(stDir o, z)] = true := by
      simp [noRetBlk, show classify (stDir o) = some (AI.st .rbp (Int64.ofInt o) .rax) from rfl]
    exact fun _ _ _ k hk hr => (noRet_false hn k hk hr).elim
  · have hn : noRetBlk ((jmpDirs F).zip [z]) = true := by
      simp [noRetBlk, jmpDirs, show classify (Scc.Emit.X64.i64 (.jmp (Scc.Emit.X64.rel F))) = some (AI.jmp F)
        from rfl]
    exact fun _ _ _ k hk hr => (noRet_false hn k hk hr).elim
  · obtain ⟨dl, hdl⟩ := dirs_getOp hg
    have hds : retDirs lw = dirs lw ++ epi := by rw [retDirs, dirs_append, dirs_epiItems]
    rw [hds, hdl] at hz
    match zs, hz with
    | [z0, z1, z2, z3], _ =>
    have hsplit : (retDirs lw).zip [z0, z1, z2, z3] = (dirs lw).zip [z0] ++ epi.zip [z1, z2, z3] := by
      rw [hds, hdl]; rfl
    refine hret_of_run hok fun σ c1 hJ1 => ?_
    have hfj := hfj σ c1 hJ1
    show (arun lab ((retDirs lw).zip [z0, z1, z2, z3]) ⟨n.pc, n.o, σ⟩).pc = _
    rw [hno, hsplit, arun_append]
    obtain ⟨v, -, hrun⟩ := arun_getOp hf h1 (by decide) hg lab n.pc σ (zs := [z0]) (by simp [hdl])
    rw [hrun, show oB fr = oR (-(fr.size : Int)) from rfl]
    rw [(arun_epi lab (n.pc + Int64.ofNat [z0].sum) (-(fr.size : Int))
      { σ with regs := σ.regs.set64 .rax v } z1 z2 z3).1]
    exact congrArg Int64.ofBitVec hfj.2

/-- **A construct's block of a call-free `Accepted1` body is inside
`BodyW0`** at any node with the frame's offsets (`hno`) whose controls a
local run from `c0` reaches, the saved pair in its cells (`hJ`): the block
at `Cd1` (placed, its phase check passed, its kind). -/
theorem blkW_body1 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {n : ND} (hno : n.o = oB fr) (hJ : ∀ σ c, n.J σ c → LocalRun p c0 c ∧ FrJ fp ra σ.slot)
    {blk : List (Directive × Nat)} (hcd : Cd1 cells okPc ph lab fr (Int64.ofBitVec ra) n.pc blk) :
    BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := cdOf_cd1 hI _ _ hcd
  obtain ⟨hk, l, j, off, hpc, hb, hphb⟩ := hcd
  have hok : okBlk (-(fr.size : Int)) 16 n.o blk = true := hno ▸ kind1_ok hf h1 hk
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩
  have hret := hret_kind1 (lab := lab) (n := n') hf h1 hno (fun σ _ ⟨_, c1, hJ1⟩ => (hJ σ c1 hJ1).2) hk
  have H := blkW_postO' (n := n') (dead := fun _ => false) (ra := Int64.ofBitVec ra) hI hcode hok hR hlo hhi
    hR8 hl hh (fun _ _ h => h.1 ▸ hC0) (hpc ▸ hphb) hret (fun _ _ _ => rfl) hsub hfit hFO
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨hW, hK⟩ := H s σ c0 he hn hd hp hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
  exact ⟨⟨hQ c (hJ σ c hJn).1, hW⟩, hK⟩

/-- **`body1_seg`'s `hW`**: the body's blocks at its nodes inside
`BodyW0`. -/
theorem hWb1_of {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {al : WeakMem.AllocLabel → Option Nat} :
    ∀ pc t s blk, Cd1 cells okPc ph lab fr (Int64.ofBitVec ra) pc blk →
      BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F (bodyN p al fr fp ra c0 pc t s) blk :=
  fun _ _ _ _ hcd => blkW_body1 hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hC0 hQ rfl
    (fun _ _ (h : _ ∧ _ ∧ _) => ⟨h.2.2, h.2.1⟩) hcd

/-- **`body1_seg`'s `hWp`**: the body's blocks at its pending stores
inside `BodyW0`. -/
theorem hWs1_of {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {al : WeakMem.AllocLabel → Option Nat} :
    ∀ pc t s k blk, Cd1 cells okPc ph lab fr (Int64.ofBitVec ra) pc blk →
      BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F (pendN p al fr fp ra c0 pc t s k) blk :=
  fun _ _ _ _ _ hcd => blkW_body1 hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hC0 hQ rfl
    (fun _ _ (h : _ ∧ _ ∧ _) => ⟨h.2.2, h.2.1⟩) hcd

end W

/-- **`hWb1_of`'s and `hWs1_of`'s `hQ`** for a main-only `Accepted1`
program from the consumer's start: every control a local run reaches is
`Quiet`. -/
theorem quiet_c1 {d : Decl} (hp : Scc.Lower.Accepted1 [d] = true) :
    ∀ c, LocalRun [d] Spike.Lib.X64Consumer.c0 c → Quiet c :=
  quiet_of_accepted1main hp rfl rfl

end Spike.Lib.LowerX64
