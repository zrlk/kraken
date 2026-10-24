import Scc.Cert.PlaceOKA64

/-!
# A9 by keyed lookups (AArch64)

`a9` (`Scc/Cert/PlaceOKA64.lean`) checks every lowered function's prologue,
body and phase facts. Written for the proofs, it finds a label at every
block (`blockAt`, `labelGap`: `labelIdx` by `Directive`'s decidable
equality, a string comparison per label of the program) and a code address
at every label read (`codeOf`); in the kernel those scans are most of
`prog_placeOK_9`'s cost.

`a9fast` is the same check (`a9fast_eq`) written for the kernel:

* each label of the program is encoded once, into a number (`key`), in one
  table of its index and the directives after it (`tailTab`); a lookup
  compares numbers (`findT`, `findT_tailTab`);
* a body's blocks are read from the run after its label, found once
  (`chkK`, `bodyInG`);
* the code addresses come from the keyed table of `Scc/Cert/Rt/PhasesA64.lean`
  (`codeT`, `codeT_eq`).

A certificate proves `prog_placeOK_9` by `a9_of_fast` and the kernel's
evaluation of `a9fast`.
-/

namespace Scc.Cert.PlaceOK.A64

open Kraken Spike.Lib.A64.Flow Scc.Emit.A64 Spike.Lib.LowerA64 Scc.Cert.Link.A64
open Scc.Cert.Rt.A64 (key key_inj memR memR_iff isIns insRun insRun_eq labelIdx run blockAt labelGap codeT codeT_eq)

/-! ## The labels' table -/

/-- `tailTab` for the code generator. -/
def tailTabImpl : List Directive → Nat → List (Nat × Nat × List Directive)
  | [], _ => []
  | .label m :: ds, i => (key m, i, ds) :: tailTabImpl ds (i + 1)
  | _ :: ds, i => tailTabImpl ds (i + 1)

/-- **The program's labels**: each label's `key` with its index (from `i`)
and the directives after it, in program order. -/
@[implemented_by tailTabImpl] def tailTab (prog : List Directive) : Nat → List (Nat × Nat × List Directive) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat × List Directive)) (fun _ => [])
    (fun d ds r i => match d with
      | .label m => (key m, i, ds) :: r (i + 1)
      | _ => r (i + 1)) prog

/-- `findT` for the code generator. -/
def findTImpl (k : Nat) : List (Nat × Nat × List Directive) → Option (Nat × List Directive)
  | [] => none
  | p :: T => if k == p.1 then some p.2 else findTImpl k T

/-- The index and tail of the first entry of key `k`. -/
@[implemented_by findTImpl] def findT (k : Nat) (T : List (Nat × Nat × List Directive)) :
    Option (Nat × List Directive) :=
  List.rec (motive := fun _ => Option (Nat × List Directive)) none
    (fun p _ r => if Nat.beq k p.1 then some p.2 else r) T

theorem findT_tailTab (l : Label) : ∀ (prog : List Directive) (i : Nat),
    findT (key l) (tailTab prog i) = (labelIdx prog l).map fun n => (i + n, prog.drop (n + 1))
  | [], _ => rfl
  | d :: ds, i => by
    have ih := findT_tailTab l ds (i + 1)
    simp only [findT, tailTab] at ih ⊢
    cases d with
    | label m =>
      by_cases hm : m = l
      · subst hm; simp [labelIdx, Nat.beq_refl]
      · have hk : Nat.beq (key l) (key m) = false := by
          cases h : Nat.beq (key l) (key m)
          · rfl
          · exact absurd (key_inj (Nat.eq_of_beq_eq_true h)).symm hm
        simp only [hk, ih, labelIdx, Directive.label.injEq, hm, ite_false, Option.map_map, Function.comp_def,
          Bool.false_eq_true, List.drop_succ_cons]
        congr 1; funext n; simp only [Prod.mk.injEq, and_true]; omega
    | _ =>
      simp only [ih, labelIdx, reduceCtorEq, ite_false, Option.map_map, Function.comp_def, List.drop_succ_cons]
      congr 1; funext n; simp only [Prod.mk.injEq, and_true]; omega

/-! ## Blocks and gaps -/

/-- `b` is the run `r` from its `k`-th instruction on (a prefix). -/
def blkR (r : List Directive) (k : Nat) (b : List Directive) : Bool :=
  decide (((r.drop k).take b.length) = b)

/-- **`blockAt` at a label, keyed**: the run after the label found once. -/
def chkK (T : List (Nat × Nat × List Directive)) (l : Label) : Nat → List Directive → Bool :=
  match findT (key l) T with
  | some (_, t) => blkR (insRun t)
  | none => fun _ _ => false

theorem chkK_eq (prog : List Directive) (l : Label) : chkK (tailTab prog 0) l = blockAt prog l := by
  funext k b
  unfold chkK blockAt run
  rw [findT_tailTab]
  cases labelIdx prog l <;> simp [blkR, insRun_eq]

/-- **`labelGap`, keyed.** -/
def labelGapK (T : List (Nat × Nat × List Directive)) (a b : Label) (n : Nat) : Bool :=
  match findT (key a) T, findT (key b) T with
  | some (i, t), some (j, _) => j == i + 1 + n && (t.take n).all isIns
  | _, _ => false

theorem labelGapK_eq (prog : List Directive) (a b : Label) (n : Nat) :
    labelGapK (tailTab prog 0) a b n = labelGap prog a b n := by
  unfold labelGapK labelGap
  rw [findT_tailTab, findT_tailTab]
  cases labelIdx prog a <;> cases labelIdx prog b <;> simp

/-! ## The prologue and the body -/

/-- **`prologueIn`, keyed.** -/
def prologueInK (T : List (Nat × Nat × List Directive)) (fn sc entry : Label) (Z lim : Int64) (L : Label)
    (ps : List (XReg × Int64)) : Bool :=
  labelGapK T fn sc 0 && chkK T sc 0 (chkHead Z) && chkK T sc 2 [ldrDir .X10 .X10 lim] &&
  chkK T sc 3 (chkBr L) && chkK T sc 5 (frameSet Z ps) && labelGapK T sc entry (9 + ps.length)

theorem prologueInK_eq (prog : List Directive) (fn sc entry : Label) (Z lim : Int64) (L : Label)
    (ps : List (XReg × Int64)) :
    prologueInK (tailTab prog 0) fn sc entry Z lim L ps = prologueIn prog fn sc entry Z lim L ps := by
  simp only [prologueInK, prologueIn, labelGapK_eq, chkK_eq]

/-- **`proInC`, keyed.** -/
def proInK (T : List (Nat × Nat × List Directive)) (c : FnCtx) (fn entry : Label) : Bool :=
  prologueInK T fn (c.local "stack_check") entry (Int64.ofInt c.frame)
    (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c) []

theorem proInK_eq (prog : List Directive) (c : FnCtx) (fn entry : Label) :
    proInK (tailTab prog 0) c fn entry = proInC prog c fn entry := by
  simp only [proInK, proInC, prologueInK_eq]

/-! ## The slots, keyed

A function's context (`fnCtx`) removes repeated registers by `List.contains`
on strings (`funcRegs`), and `slotOff` finds a register's slot by
`List.idxOf?`; each string comparison costs the kernel both strings' UTF-8
encodings. `fnCtxK` and `slotOffK` are the same functions (`fnCtxK_eq`,
`slotOffK_eq`) comparing the registers' `key`s. -/

/-- `funcRegs` before removing repeats (`funcRegs_eq_foldl`). -/
def regsAll (f : Scc.IR.Func) : List Scc.IR.Reg :=
  let op : Scc.IR.Operand → List Scc.IR.Reg := fun | .reg r => [r] | .imm _ => []
  let inst : Scc.IR.Inst → List Scc.IR.Reg
    | .mov d s => d :: op s
    | .bin _ d a b => d :: op a ++ op b
    | .un _ d a => d :: op a
    | .ext _ _ d a => d :: op a
    | .setc _ d a b => d :: op a ++ op b
    | .select _ d a b t e => d :: op a ++ op b ++ op t ++ op e
    | .addChk d a b => d :: op a ++ op b
    | .subSat d a b => d :: op a ++ op b
    | .la d _ => [d]
    | .getTp d => [d]
    | .load _ _ d a => [d, a.base]
    | .store _ _ a v => a.base :: op v
    | .rmw _ d a v => d :: a.base :: op v
    | .fence _ => []
    | .call ds _ args => ds ++ args.flatMap op
    | .syscall d _ args _ => d :: args.flatMap op
    | .clone d s t _ a => d :: op s ++ op t ++ op a
    | .slotAddr d s => [d, s]
    | .site _ args => args.flatMap op
    | .comment _ => []
  let term : Scc.IR.Term → List Scc.IR.Reg
    | .ret vs => vs.flatMap op
    | .jmp _ => []
    | .br _ a b _ _ => op a ++ op b
    | .tail _ args => args.flatMap op
    | .switchTo s t _ a => op s ++ op t ++ op a
    | .unreachable => []
  f.params ++ f.blocks.flatMap (fun b => b.insts.flatMap inst ++ term b.term)

theorem funcRegs_eq_foldl (f : Scc.IR.Func) :
    funcRegs f = (regsAll f).foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) [] := rfl

/-- `dedupK` for the code generator. -/
def dedupKImpl : List Scc.IR.Reg → List Nat → List Scc.IR.Reg → List Scc.IR.Reg
  | [], _, acc => acc
  | r :: rs, ks, acc =>
    if memR (key r) ks then dedupKImpl rs ks acc else dedupKImpl rs (key r :: ks) (acc ++ [r])

/-- **The first occurrences** of `rs`' registers after `acc`, `ks` the keys of
`acc`'s. -/
@[implemented_by dedupKImpl] def dedupK (rs : List Scc.IR.Reg) : List Nat → List Scc.IR.Reg → List Scc.IR.Reg :=
  List.rec (motive := fun _ => List Nat → List Scc.IR.Reg → List Scc.IR.Reg) (fun _ acc => acc)
    (fun r _ ih ks acc => if memR (key r) ks then ih ks acc else ih (key r :: ks) (acc ++ [r])) rs

theorem dedupK_eq : ∀ (rs : List Scc.IR.Reg) (ks : List Nat) (acc : List Scc.IR.Reg),
    (∀ k, k ∈ ks ↔ ∃ r ∈ acc, key r = k) →
    dedupK rs ks acc = rs.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) acc
  | [], _, _, _ => rfl
  | r :: rs, ks, acc, h => by
    have hm : memR (key r) ks = acc.contains r := by
      apply Bool.eq_iff_iff.mpr
      rw [memR_iff, h, List.contains_iff_mem]
      exact ⟨fun ⟨m, hm, hk⟩ => key_inj hk ▸ hm, fun hr => ⟨r, hr, rfl⟩⟩
    have ih1 := dedupK_eq rs ks acc h
    have ih2 := dedupK_eq rs (key r :: ks) (acc ++ [r]) (by
      intro k
      simp only [List.mem_cons, h, List.mem_append, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | ⟨m, hm, rfl⟩)
        · exact ⟨r, .inr rfl, rfl⟩
        · exact ⟨m, .inl hm, rfl⟩
      · rintro ⟨m, hm | rfl, rfl⟩
        · exact .inr ⟨m, hm, rfl⟩
        · exact .inl rfl)
    simp only [dedupK] at ih1 ih2 ⊢
    rw [List.foldl_cons, hm]
    cases acc.contains r
    · exact ih2
    · exact ih1

/-- **`funcRegs`, keyed.** -/
def funcRegsK (f : Scc.IR.Func) : List Scc.IR.Reg := dedupK (regsAll f) [] []

theorem funcRegsK_eq (f : Scc.IR.Func) : funcRegsK f = funcRegs f := by
  rw [funcRegsK, funcRegs_eq_foldl, dedupK_eq _ _ _ (by simp)]

/-- **`fnCtx`, keyed** (`fnCtxK_eq`). -/
def fnCtxK (abortFn : String) (growth : Option Scc.IR.Growth) (areas : List (Scc.IR.Sym × Nat))
    (fi : Nat) (f : Scc.IR.Func) : FnCtx :=
  let slots := funcRegsK f
  let out := outWords areas f
  { fi, name := f.name, slots, blocks := f.blocks.map (·.label),
    frame := 8 * out + align16 (8 * slots.length + 16), out,
    inArea := ((areas.find? (·.1 == f.name)).map (·.2)).getD 0, abortFn,
    maps := growth.isSome }

theorem fnCtxK_eq (abortFn : String) (growth : Option Scc.IR.Growth) (areas : List (Scc.IR.Sym × Nat))
    (fi : Nat) (f : Scc.IR.Func) : fnCtxK abortFn growth areas fi f = fnCtx abortFn growth areas fi f := by
  simp only [fnCtxK, fnCtx, funcRegsK_eq]

/-- `idxK` for the code generator. -/
def idxKImpl (k : Nat) : List Nat → Option Nat
  | [] => none
  | a :: ks => if k == a then some 0 else (idxKImpl k ks).map (· + 1)

/-- The index of the first `k`. -/
@[implemented_by idxKImpl] def idxK (k : Nat) (ks : List Nat) : Option Nat :=
  List.rec (motive := fun _ => Option Nat) none (fun a _ r => if Nat.beq k a then some 0 else r.map (· + 1)) ks

theorem idxK_eq (r : Scc.IR.Reg) : ∀ rs : List Scc.IR.Reg, idxK (key r) (rs.map key) = rs.idxOf? r
  | [] => rfl
  | a :: rs => by
    have ih := idxK_eq r rs
    simp only [idxK] at ih
    rw [List.idxOf?_cons]
    by_cases h : a = r
    · subst h; simp [idxK]
    · have hk : key r ≠ key a := fun he => h (key_inj he).symm
      simp only [idxK, List.map_cons, Nat.beq_eq] at ih ⊢
      simp [hk, h, ih]

/-- **`slotOff`, keyed**: `ks` the keys of `c`'s slots. -/
def slotOffK (c : FnCtx) (ks : List Nat) (r : Scc.IR.Reg) : Except String Int :=
  match idxK (key r) ks with
  | some i => .ok (8 * (c.out + i))
  | none => .error s!"scc (arm): unknown register {r} in function {c.name}"

theorem slotOffK_eq (c : FnCtx) : slotOffK c (c.slots.map key) = c.slotOff := by
  funext r
  simp only [slotOffK, FnCtx.slotOff, idxK_eq]
  rfl

/-- `getOp` at a slot function `so` (`getOpS_slotOff`). -/
def getOpS (so : Scc.IR.Reg → Except String Int) (t : XReg) : Scc.IR.Operand → Except String (List Item)
  | .reg r => do return ldrOff .W64 t spW64 (← so r)
  | .imm v => .ok (movImm t v.toNat)

theorem getOpS_slotOff (c : FnCtx) (t : XReg) : getOpS c.slotOff t = c.getOp t := by
  funext w; cases w <;> rfl

/-! ## The body -/

/-- **`bodyIn` at a block check `chk`** and a slot function `so`
(`bodyIn prog cx l` at `blockAt prog l` and `cx.slotOff`, `bodyIn_eq_G`). -/
def bodyInG (chk : Nat → List Directive → Bool) (cx : FnCtx) (so : Scc.IR.Reg → Except String Int) :
    Nat → List Scc.IR.Inst → List Scc.IR.Operand → Bool
  | k, [], [w] =>
    match getOpS so .X0 w with
    | .ok lw => chk k (directives (lw ++ cx.leave ++ [ret]))
    | .error _ => false
  | k, .addChk d a b :: is, ws =>
    match getOpS so .X9 a, getOpS so .X10 b, so d with
    | .ok la, .ok lb, .ok off =>
      chk k (addDirs cx la lb) && chk (k + (addDirs cx la lb).length) (strDirs off) &&
        bodyInG chk cx so (k + (addDirs cx la lb).length + 1) is ws
    | _, _, _ => false
  | _, _, _ => false

theorem bodyIn_eq_G (prog : List Directive) (cx : FnCtx) (l : Label) :
    bodyIn prog cx l = bodyInG (blockAt prog l) cx cx.slotOff := by
  funext k is ws
  induction is generalizing k with
  | nil => cases ws with
    | nil => simp [bodyIn, bodyInG]
    | cons w ws => cases ws <;> simp only [bodyIn, bodyInG, getOpS_slotOff] <;> cases cx.getOp .X0 w <;> rfl
  | cons i is ih =>
    cases i <;> simp only [bodyIn, bodyInG, ih, getOpS_slotOff] <;>
      cases cx.getOp .X9 _ <;> cases cx.getOp .X10 _ <;> cases cx.slotOff _ <;> rfl

/-- **`bodyBlks` at a slot function `so`** (`bodyBlks_eq_S`). -/
def bodyBlksS (cx : FnCtx) (so : Scc.IR.Reg → Except String Int) :
    Nat → List Scc.IR.Inst → List Scc.IR.Operand → List (Nat × List Directive)
  | k, [], [w] =>
    match getOpS so .X0 w with
    | .ok lw => [(k, directives (lw ++ cx.leave ++ [ret]))]
    | .error _ => []
  | k, .addChk d a b :: is, ws =>
    match getOpS so .X9 a, getOpS so .X10 b, so d with
    | .ok la, .ok lb, .ok off =>
      (k, addDirs cx la lb) :: (k + (addDirs cx la lb).length, strDirs off) ::
        bodyBlksS cx so (k + (addDirs cx la lb).length + 1) is ws
    | _, _, _ => []
  | _, _, _ => []

theorem bodyBlks_eq_S (cx : FnCtx) : bodyBlks cx = bodyBlksS cx cx.slotOff := by
  funext k is ws
  induction is generalizing k with
  | nil => cases ws with
    | nil => simp [bodyBlks, bodyBlksS]
    | cons w ws => cases ws <;> simp only [bodyBlks, bodyBlksS, getOpS_slotOff] <;> cases cx.getOp .X0 w <;> rfl
  | cons i is ih =>
    cases i <;> simp only [bodyBlks, bodyBlksS, ih, getOpS_slotOff] <;>
      cases cx.getOp .X9 _ <;> cases cx.getOp .X10 _ <;> cases cx.slotOff _ <;> rfl

/-! ## The code part -/

/-- **`fnCodeOk`, keyed** at a labels' table `T`. -/
def fnCodeOkK (T : List (Nat × Nat × List Directive)) (ir : Scc.IR.Program) : Bool :=
  let areas := Scc.IR.StackMap.argAreas ir argRegs.length
  ir.funcs.zipIdx.all fun (f, fi) =>
    match f.params, f.checkStack, f.blocks with
    | [], true, [⟨"entry", is, .ret [w]⟩] =>
      if is.all isAddChk then
        let c := fnCtxK ir.abortFn ir.growth areas fi f
        proInK T c f.name (c.prefix ++ "0_entry") &&
          bodyInG (chkK T (c.prefix ++ "0_entry")) c (slotOffK c (c.slots.map key)) 0 is [w] &&
          (is.isEmpty || chkK T (c.local "abort_overflow") 0 ovfBlk)
      else true
    | _, _, _ => true

theorem fnCodeOkK_eq (prog : List Directive) (ir : Scc.IR.Program) :
    fnCodeOkK (tailTab prog 0) ir = fnCodeOk prog ir := by
  simp only [fnCodeOkK, fnCodeOk, fnCtxK_eq, slotOffK_eq, proInK_eq, chkK_eq, bodyIn_eq_G]
  congr 1

/-! ## The phase part -/

/-- **`fnPh1` at a slot function `so`**, the body's blocks computed once
(`fnPh1S_eq`). -/
def fnPh1S (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (cx : FnCtx)
    (so : Scc.IR.Reg → Except String Int) (fn : String) (is : List Scc.IR.Inst) (w : Scc.IR.Operand)
    (ra : Int64) : Bool :=
  let bs := bodyBlksS cx so 0 is [w]
  res fn && res (cx.local "stack_check") && res (cx.prefix ++ "0_entry") &&
    (proLabs (Int64.ofInt cx.frame) (proL cx) []).all res &&
    bs.all (fun x => (blkLabs x.2).all res) &&
    proPhOk okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [] &&
    (is.isEmpty || (res (cx.local "abort_overflow") && (blkLabs ovfBlk).all res &&
      Spike.Lib.A64Consumer.blkPh okPc ph (fun _ => false) lab
        (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0 ovfBlk)) &&
    bs.all fun x =>
      Spike.Lib.A64Consumer.blkPh okPc ph (fun _ => false) lab (lab (cx.prefix ++ "0_entry") + Int64.ofNat (4 * x.1))
        ra x.2

theorem fnPh1S_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (cx : FnCtx)
    (fn : String) (is : List Scc.IR.Inst) (w : Scc.IR.Operand) (ra : Int64) :
    fnPh1S okPc ph lab res cx cx.slotOff fn is w ra = fnPh1 okPc ph lab res cx fn is w ra := by
  simp only [fnPh1S, fnPh1, bodyBlks_eq_S]

/-- **`fnPhAll`, keyed** (the contexts by `fnCtxK`, the slots by `slotOffK`). -/
def fnPhAllK (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  let areas := Scc.IR.StackMap.argAreas ir argRegs.length
  ir.funcs.zipIdx.all fun (f, fi) =>
    match f.params, f.checkStack, f.blocks with
    | [], true, [⟨"entry", is, .ret [w]⟩] =>
      if is.all isAddChk then
        let c := fnCtxK ir.abortFn ir.growth areas fi f
        fnPh1S okPc ph lab res c (slotOffK c (c.slots.map key)) f.name is w ra
      else true
    | _, _, _ => true

theorem fnPhAllK_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (ir : Scc.IR.Program) (ra : Int64) : fnPhAllK okPc ph lab res ir ra = fnPhAll okPc ph lab res ir ra := by
  simp only [fnPhAllK, fnPhAll, fnCtxK_eq, slotOffK_eq, fnPh1S_eq]
  congr 1

/-- **`fnPhOk`, keyed**: the code labels by `codeT`. -/
def fnPhOkK (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) (ir : Scc.IR.Program) : Bool :=
  match Scc.Cert.Rt.A64.phTabBy (codeT lo prog), Scc.Cert.Rt.A64.sitesBy (codeT lo prog) Λ with
  | some T, some ss =>
    (codeT lo prog raL).isSome &&
      fnPhAllK (fun pc => !ss.contains pc) T.ph (fun l => Int64.ofNat ((codeT lo prog l).getD 0))
        (fun l => (codeT lo prog l).isSome) ir (Int64.ofNat ((codeT lo prog raL).getD 0) + 4)
  | _, _ => false

theorem fnPhOkK_eq (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) (ir : Scc.IR.Program) :
    fnPhOkK lo Λ prog ir = fnPhOk lo Λ prog ir := by
  simp only [fnPhOkK, fnPhAllK_eq, codeT_eq]
  rfl

/-! ## A9 -/

/-- **A9 for the kernel** (`a9fast_eq`). -/
def a9fast (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir => fnCodeOkK (tailTab o.prog 0) ir && fnPhOkK t.Λ.code.lo t.Λ o.prog ir
  | none => false

theorem a9fast_eq (o : Out) (t : Tables) : a9fast o t = a9 o t := by
  unfold a9fast a9
  cases o.place.ir with
  | some ir => simp only [fnCodeOkK_eq, fnPhOkK_eq]
  | none => rfl

/-- **A9 from `a9fast`** (a certificate's `prog_placeOK_9`). -/
theorem a9_of_fast {o : Out} {t : Tables} (h : a9fast o t = true) : a9 o t = true :=
  a9fast_eq o t ▸ h

end Scc.Cert.PlaceOK.A64
