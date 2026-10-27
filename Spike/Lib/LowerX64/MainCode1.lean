/-
**The user `main`'s code and phase facts of a one-block `Accepted1`
program from `PlaceOK`** (x86-64): the twin of
`Spike/Lib/LowerA64/MainCode1.lean`, from A12's checks of every
stack-checked function (`Scc.Cert.Code1X64.fnCode1Ok`,
`Scc.Cert.Ph1X64.fnPh1Ok`).

`mainPh1_ofPlaceOK`: on a one-block `Accepted1` program that lowers and
emits, whose output passes `PlaceOK`, `main`'s lowered body `r` (`lower1`
of the source body) is the function `func1 main [] r` of the lowered IR,
numbered from `n` (`starts`); at its frame `fr` (`frOf`, valid, a multiple
of 16 and, by `MainFrame1Ok`, at most 4096 bytes) the program holds its
prologue at `bareMC.fn` (at the listing's cell sizes) and its blocks
(`blocksOk`) with their runs' phase facts (`blocksPh`, at the code labels,
every label read resolving, the return address `raL`); the prologue's
`ProPh` at the runtime's layout, and with a checked `+` the local overflow
block with its `blkPh`. The labels of the layout agree with the code labels
(`hlab_ofPlaceOK`).

Where x86-64 differs from AArch64: A12's `fnOk1` bounds the frame only by
`2^31`; the bound of 4096 bytes the stack-check segment needs is the
separate `MainFrame1Ok`, decided per program. The prologue's cell sizes
are existential (`sizesAt`), and a function's label numbering is its
`starts` entry, not its index.
-/
import Spike.Lib.LowerX64.MainPh
import Scc.Cert.Ph1X64
import Scc.Cert.PlaceOKX64
import Scc.Lower.InvProg1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (blocksOk spills hasAddChk chkL starts fnOk1 fnOk1_of_fnCode1Ok fnOk1_facts)
open Scc.Cert.Ph1X64 (blocksPh fnPh1Ok_parts fnPhF_of_fnPhAll1 fnPhF_facts)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (blkPh)
open Scc.Emit.X64 (labelOf)
open Scc.Lower.Inv (lower1 Res1 func1)
open Scc.Sem.X64 (codeLabel)

/-- A function without parameters stores none in its prologue. -/
theorem spills_nil (fr : Scc.Emit.X64.Frame) : spills fr [] [] = some [] := by
  simp [spills]

/-- **The frame bound of `main`'s `func1`** (x86-64): the lowered `main`'s
frame is at most 4096 bytes, the reach of the stack-check segment's probe.
A12's `fnOk1` checks only `size < 2^31`, so this is decided per program
(on AArch64, A12's checks give `≤ 4095`). -/
def MainFrame1Ok (cfg : Scc.Config) (d : Decl) : Bool :=
  match lower1 [(d.arg, .unit, [])] 0 d.body with
  | some r => decide ((frOf (Scc.Lower.X64.lowerAll cfg [d]).low.ir
      (func1 (Scc.Lower.Names.user "main") [] r)).size ≤ 4096)
  | none => false

/-- `MainFrame1Ok` at `main`'s lowered body bounds its frame. -/
theorem mainFrame1Ok_size {cfg : Scc.Config} {d : Decl} (h : MainFrame1Ok cfg d = true) {r : Res1}
    (hr : lower1 [(d.arg, .unit, [])] 0 d.body = some r) :
    (frOf (Scc.Lower.X64.lowerAll cfg [d]).low.ir (func1 (Scc.Lower.Names.user "main") [] r)).size ≤ 4096 := by
  simpa [MainFrame1Ok, hr] using h

/-- Every function of `fs` has a label number in `starts`. -/
theorem mem_starts (ir : Scc.IR.Program) {f : Scc.IR.Func} :
    ∀ {fs : List Scc.IR.Func} (m : Nat), f ∈ fs → ∃ n, (f, n) ∈ starts ir m fs
  | [], _, h => by cases h
  | g :: fs, m, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨m, by simp [starts]⟩
    · obtain ⟨n, hn⟩ := mem_starts ir (m + Scc.Cert.Code1X64.fnLabs ir g) h
      exact ⟨n, by simp only [starts]; exact List.mem_cons_of_mem _ hn⟩

/-- **The prologue's cell sizes of a parameterless function** passing
`fnOk1`: exactly five. -/
theorem fnOk1_sizes_nil {cells : List (Directive × Nat)} {tbl : List Scc.Cert.NeedX64.Row}
    {ir : Scc.IR.Program} {n : Nat} {f : Scc.IR.Func} (h : fnOk1 cells tbl ir n f = true)
    (hp : f.params = []) :
    ∃ zl zf z1 z2 zs, Spike.Lib.LowerX64.sizesAt cells (chkL f) 0 (5 + f.params.length) =
      [zl, zf, z1, z2, zs] := by
  unfold fnOk1 at h
  split at h
  · next zl zf z1 z2 zs zps _ hz =>
    cases zps with
    | nil => exact ⟨zl, zf, z1, z2, zs, hz⟩
    | cons z zps => simp [hp, spills] at h
  · cases h

/-- **`main`'s lowered IR on a one-block `Accepted1` program** (x86-64):
`lowerAll`'s IR is the runtime functions then `func1 main [] r`. -/
theorem lowerAll_accepted1main_x64 (cfg : Scc.Config) {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true)
    {e : Scc.Lower.X64.Emitted} (h : Scc.Lower.X64.lowerAll? cfg [d] = .ok e) :
    ∃ r rt, lower1 [(d.arg, .unit, [])] 0 d.body = some r ∧
      (Scc.Lower.X64.lowerAll cfg [d]).low.ir =
        Scc.Lower.Inv.progOf cfg.layout rt [func1 (Scc.Lower.Names.user "main") [] r] ∧
      func1 (Scc.Lower.Names.user "main") [] r ∈ (Scc.Lower.X64.lowerAll cfg [d]).low.ir.funcs := by
  obtain ⟨r, rt, hr, -, hir, -⟩ := Scc.Lower.Inv.lowerIR_accepted1main cfg hd (lowerAll?_low_x64 h)
  have hir' : (Scc.Lower.X64.lowerAll cfg [d]).low.ir =
      Scc.Lower.Inv.progOf cfg.layout rt [func1 (Scc.Lower.Names.user "main") [] r] := by
    simp only [Scc.Lower.X64.lowerAll, h]
    exact hir
  refine ⟨r, rt, hr, hir', ?_⟩
  rw [hir']
  simp [Scc.Lower.Inv.progOf]

/-- **`main`'s code and phase facts from `PlaceOK`** on a one-block
`Accepted1` program (see the module docstring), at the layout
`RuntimeLayout.ofPlaceOK h i` (any immediates `i`). -/
theorem mainPh1_ofPlaceOK {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true)
    (hfr : MainFrame1Ok cfg d = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs
    let ir := (Scc.Lower.X64.lowerAll cfg [d]).low.ir
    let L := RuntimeLayout.ofPlaceOK h i
    let okPc := Spike.Lib.X64.PhRec.okPc L
    let ph := Spike.Lib.X64.PhRec.ph L
    ∃ (fr : Scc.Emit.X64.Frame) (r : Res1) (n : Nat) (zl zf z1 z2 zs : Nat),
      lower1 [(d.arg, .unit, [])] 0 d.body = some r ∧
      (func1 (Scc.Lower.Names.user "main") [] r, n) ∈ starts ir 0 ir.funcs ∧
      fr = frOf ir (func1 (Scc.Lower.Names.user "main") [] r) ∧
      FrameOk fr ∧ fr.size ≤ 4096 ∧ fr.size % 16 = 0 ∧
      proInC o.prog fr Spike.Lib.X64.Rt.bareMC.fn (labelOf (Scc.Lower.Names.user "main") "entry")
        zl zf z1 z2 zs = true ∧
      blocksOk o.prog fr n ((func1 (Scc.Lower.Names.user "main") [] r).blocks.zip
        (Scc.IR.StackMap.callMaps (func1 (Scc.Lower.Names.user "main") [] r))) = true ∧
      blocksPh okPc ph (labC Λ.code.lo o.prog) (fun l => (codeLabel Λ.code.lo o.prog l).isSome) o.prog fr
        (L.lab raL) n ((func1 (Scc.Lower.Names.user "main") [] r).blocks.zip
          (Scc.IR.StackMap.callMaps (func1 (Scc.Lower.Names.user "main") [] r))) = true ∧
      (∀ l a, codeLabel Λ.code.lo o.prog l = some a → L.lab l = Int64.ofNat a) ∧
      ProPh okPc ph L.lab Spike.Lib.X64.Rt.bareMC.fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr)
        zl zf z1 z2 zs [] ∧
      (hasAddChk (func1 (Scc.Lower.Names.user "main") [] r) = true →
        Scc.Cert.Rt.X64.blockAtB o.prog (ovfL fr) 0 ovfBlk = true ∧
        blkPh okPc ph (fun _ => false) L.lab (L.lab (ovfL fr) + Int64.ofNat 0) 0
          Spike.Lib.X64.Abort.Local.lb = true) := by
  intro o ir L okPc ph
  obtain ⟨r, rt, hr, -, hmem⟩ := lowerAll_accepted1main_x64 cfg hd hlow
  obtain ⟨n, hn⟩ := mem_starts ir 0 hmem
  have hlab : ∀ l a, codeLabel Λ.code.lo o.prog l = some a → L.lab l = Int64.ofNat a :=
    Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i
  have hir := lowerAll_place_ir cfg [d] sizes labelOffs
  have hc1 := fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h hir) hn rfl
  obtain ⟨zl, zf, z1, z2, zs, hz⟩ := fnOk1_sizes_nil hc1 rfl
  obtain ⟨-, hpro, -, h16, hbo, hovf, -⟩ := fnOk1_facts hc1 rfl hz (spills_nil _)
  obtain ⟨hra, hall⟩ := fnPh1Ok_parts (fnPh1_of_placeOKAt h hir)
  have hF := fnPhF_of_fnPhAll1 hall hn rfl
  obtain ⟨rfn, rsc, rpro, hpp, hbp, hovp⟩ := fnPhF_facts hF hz (spills_nil _)
  rw [labC_eq hlab hra] at hbp
  have hpr := List.all_eq_true.mp rpro
  have e := fun (blk : List (Directive × Nat))
      (hsub : ∀ L ∈ blkLabs blk, L ∈ proLabs (Int64.ofInt (frOf ir (func1 (Scc.Lower.Names.user "main") [] r)).size)
        (proL (frOf ir (func1 (Scc.Lower.Names.user "main") [] r))) zl z1 z2 zs []) =>
    (List.all_eq_true.mpr fun L hL => hpr L (hsub L hL) :
      (blkLabs blk).all (fun l => (codeLabel Λ.code.lo o.prog l).isSome) = true)
  refine ⟨_, r, n, zl, zf, z1, z2, zs, hr, hn, rfl, ⟨_, _, rfl, rfl⟩, mainFrame1Ok_size hfr hr, h16,
    user_main_eq_bareMC_fn ▸ hpro, hbo, hbp, hlab, ?_, ?_⟩
  · rw [← user_main_eq_bareMC_fn]
    apply proPh_of_proPhOk
    simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at hpp ⊢
    rw [labC_eq hlab rfn, labC_eq hlab rsc] at hpp
    obtain ⟨⟨⟨⟨⟨hd', lea⟩, ld1⟩, ld2⟩, cmp⟩, frr⟩ := hpp
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ld1⟩, ld2⟩, ?_⟩, ?_⟩
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact hd'
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact lea
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact cmp
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact frr
  · intro ha
    obtain ⟨rab, rlb, hb⟩ := hovp ha
    rw [labC_eq hlab rab, blkPh_labC hlab rlb, ovfBlk_eq_lb] at hb
    exact ⟨(hovf ha).2, hb⟩

end Spike.Lib.LowerX64
