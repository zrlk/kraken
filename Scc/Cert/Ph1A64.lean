import Scc.Cert.Code1A64
import Spike.Lib.LowerA64.PhCheck

/-!
# The phases of every stack-checked function (AArch64; A12's `fnPh1Ok`)

A9's phase part (`Spike.Lib.LowerA64.fnPhOk`) checks the `func0`-shaped
functions only. This file checks the phase facts of **every** stack-checked
function of the lowered IR, the same set as `Scc.Cert.Code1A64.fnCode1Ok`,
at the same contexts (`ctxOf`), at A6's tables (`phOf`, `okPcOf`) and the
program's code labels (`labC`), fail-closed:

* the prologue's (`proPhOk`, with the parameters' stores `spills`);
* every block's code (`blockItems`, as `blocksOk` numbers it), split into
  its label-free runs (`runs`: the first after the block's label, every
  later one after the label inside the block, a call's return label say):
  each run's `runPhB` at its label (`blkPh`, an instruction it does not
  cover checked as falling through), the return address the one after
  `scc_rt_main`'s `bl` (`raL` plus 4), and each run's label in that return
  address's phase (so the facts hold at any return address of the phase,
  `blocksPh_ra`);
* with a checked `+`, the local overflow block's `blkPh` (as `fnPh1`);
* every label these read resolves (`res`: the function's, its stack
  check's, the runs' labels and their branch and call targets, `blkLabs`),
  so that `labC` is the loader's label on them.

`fnPh1Ok_parts`, `fnPhF_of_fnPhAll1` and `blocksPh_block` (`blocksPh_blockPh`
with the runs' phases) project it to one function and one block;
`blocksPh_ra` moves it to another return address of the phase; `runPhB_get` to one instruction of a run, and
`blkPh_of_runPhB` to `blkPh` of a sub-run of covered instructions.
-/

namespace Scc.Cert.Ph1A64

open Kraken
open Scc.Emit.A64
open Scc.Cert.Code1A64 (blockItems kAfter spills hasAddChk ctxOf)
open Spike.Lib.A64.Flow (classify)
open Spike.Lib.A64Consumer (blkPh aiTgts)
open Spike.Lib.LowerA64 (proL ovfBlk proPhOk proLabs blkLabs labC raL)
open Scc.Cert.Link.A64 (codeOf)

/-! ## Label-free runs -/

/-- The label-free runs of a code segment, after the label `l`, `acc` the
current run reversed: each run with the label it follows. -/
def runsAux (l : Label) (acc : List Directive) : List Directive → List (Label × List Directive)
  | [] => [(l, acc.reverse)]
  | .label l' :: ds => (l, acc.reverse) :: runsAux l' [] ds
  | d :: ds => runsAux l (d :: acc) ds

/-- **The label-free runs of the segment `ds` after the label `l`**: split at
every label of `ds`, each run with the label it follows. -/
def runs (l : Label) (ds : List Directive) : List (Label × List Directive) := runsAux l [] ds

/-! ## The checks -/

/-- **A run's phase check**: `blkPh` with no dead target, except that an
instruction `blkPh` does not cover (`classify` is `none`: a load or store
off the thread pointer, a system call) is checked as falling through, its
next pc in the run's phase. Every pc is off the sites and in the phase of
the run's first pc, and so is every target. On a sub-run of covered
instructions it gives `blkPh` (`blkPh_of_runPhB`). -/
def runPhB (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (pc ra : Int64)
    (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    okPc (pc + Int64.ofNat (4 * k)).toBitVec.toNat &&
    ph (pc + Int64.ofNat (4 * k)).toBitVec.toNat == ph pc.toBitVec.toNat &&
    match blk[k]? with
    | some d =>
      (match classify d with
       | some a => aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a
       | none => [pc + Int64.ofNat (4 * k) + Int64.ofNat 4]).all fun t =>
        ph t.toBitVec.toNat == ph pc.toBitVec.toNat
    | none => false

/-- One run's phase facts: its label and its targets resolve, and its
`runPhB` at its label, the return address `ra`. -/
def runPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (ra : Int64)
    (r : Label × List Directive) : Bool :=
  res r.1 && (blkLabs r.2).all res && runPhB okPc ph lab (lab r.1) ra r.2

/-- **Every block's runs' phase facts**, the blocks' first instruction
numbered `k` (as `blocksOk`), each run's label in the phase of the return
address `ra` (so the facts hold at any return address of that phase,
`blocksPh_ra`: a call's return label, say). -/
def blocksPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (c : FnCtx)
    (ra : Int64) : Nat → List Scc.IR.Block → Bool
  | _, [] => true
  | k, b :: bs =>
    (match c.blockLabel b.label, blockItems c k b with
     | .ok l, .ok code => (runs l (directives code)).all fun r =>
        runPh okPc ph lab res ra r && ph (lab r.1).toBitVec.toNat == ph ra.toBitVec.toNat
     | _, _ => false) &&
    blocksPh okPc ph lab res c ra (k + b.insts.length + 1) bs

/-- **One stack-checked function's phase facts** at its context `c`: the
prologue's with the parameters' stores, every block's runs', with a checked
`+` the overflow block's, every label read resolving. -/
def fnPhF (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (c : FnCtx)
    (f : Scc.IR.Func) (ra : Int64) : Bool :=
  match spills c f.params with
  | some ps =>
    res f.name && res (c.local "stack_check") &&
    (proLabs (Int64.ofInt c.frame) (proL c) ps).all res &&
    proPhOk okPc ph lab (c.local "stack_check") (Int64.ofInt c.frame) (proL c) ps &&
    blocksPh okPc ph lab res c ra 0 f.blocks &&
    (!hasAddChk f || (res (c.local "abort_overflow") && (blkLabs ovfBlk).all res &&
      blkPh okPc ph (fun _ => false) lab (lab (c.local "abort_overflow") + Int64.ofNat (4 * 0)) 0 ovfBlk))
  | none => false

/-- **Every stack-checked function's phase facts** (the functions
`fnCode1Ok` checks, at their contexts recomputed from `ir`). -/
def fnPhAll1 (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  ir.funcs.zipIdx.all fun (f, fi) => !f.checkStack || fnPhF okPc ph lab res (ctxOf ir fi f) f ra

/-- **A12's phase part**: at A6's phase table and sites of the program at
`lo` (`false` if either is missing) and its code labels, every stack-checked
function's phase facts, the return address after `scc_rt_main`'s `bl`
(`raL` plus 4). -/
def fnPh1Ok (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) (ir : Scc.IR.Program) : Bool :=
  match Scc.Cert.Rt.A64.phTabOf lo prog, Scc.Cert.Rt.A64.sitesOf lo prog Λ with
  | some T, some ss =>
    (codeOf lo prog raL).isSome &&
      fnPhAll1 (fun pc => !ss.contains pc) T.ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) ir
        (labC lo prog raL + 4)
  | _, _ => false

/-! ## Its parts -/

/-- **`fnPh1Ok`'s parts** at A6's `phOf`/`okPcOf`. -/
theorem fnPh1Ok_parts {lo : Nat} {Λ : Scc.Sem.Layout} {prog : Program} {ir : Scc.IR.Program}
    (h : fnPh1Ok lo Λ prog ir = true) :
    (codeOf lo prog raL).isSome = true ∧
      fnPhAll1 (Scc.Cert.Rt.A64.okPcOf lo prog Λ) (Scc.Cert.Rt.A64.phOf lo prog) (labC lo prog)
        (fun l => (codeOf lo prog l).isSome) ir (labC lo prog raL + 4) = true := by
  unfold fnPh1Ok at h
  split at h
  · next T ss hT hs =>
    simp only [Bool.and_eq_true] at h
    have hph : Scc.Cert.Rt.A64.phOf lo prog = T.ph := by unfold Scc.Cert.Rt.A64.phOf; rw [hT]
    have hok : Scc.Cert.Rt.A64.okPcOf lo prog Λ = fun pc => !ss.contains pc := by
      funext pc; unfold Scc.Cert.Rt.A64.okPcOf; rw [hs]
    rw [hph, hok]
    exact h
  · cases h

/-- **`fnPhF` of a stack-checked function** of `ir`, from `fnPhAll1`. -/
theorem fnPhF_of_fnPhAll1 {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {ir : Scc.IR.Program} {ra : Int64} (h : fnPhAll1 okPc ph lab res ir ra = true)
    {f : Scc.IR.Func} {fi : Nat} (hf : (f, fi) ∈ ir.funcs.zipIdx) (hc : f.checkStack = true) :
    fnPhF okPc ph lab res (ctxOf ir fi f) f ra = true := by
  have := List.all_eq_true.mp h _ hf
  simpa [hc] using this

/-- **The facts of `fnPhF`** for a function with the parameters' stores
`ps`. -/
theorem fnPhF_facts {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {c : FnCtx} {f : Scc.IR.Func} {ra : Int64} (h : fnPhF okPc ph lab res c f ra = true)
    {ps : List (XReg × Int64)} (hps : spills c f.params = some ps) :
    res f.name = true ∧ res (c.local "stack_check") = true ∧
    (proLabs (Int64.ofInt c.frame) (proL c) ps).all res = true ∧
    proPhOk okPc ph lab (c.local "stack_check") (Int64.ofInt c.frame) (proL c) ps = true ∧
    blocksPh okPc ph lab res c ra 0 f.blocks = true ∧
    (hasAddChk f = true → res (c.local "abort_overflow") = true ∧ (blkLabs ovfBlk).all res = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (c.local "abort_overflow") + Int64.ofNat (4 * 0)) 0 ovfBlk = true) := by
  unfold fnPhF at h
  rw [hps] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun ha => ?_⟩
  have := h6.resolve_left (by simp [ha])
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **A block's runs' phase facts and phases**, from `blocksPh`: the block
`b` after the blocks `pre`, at the same label and code as `blocksOk_block`,
every run's label in the phase of `ra`. -/
theorem blocksPh_blockPh {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {c : FnCtx} {ra : Int64} :
    ∀ {k : Nat} {pre post : List Scc.IR.Block} {b : Scc.IR.Block},
      blocksPh okPc ph lab res c ra k (pre ++ b :: post) = true →
      ∃ l code, c.blockLabel b.label = .ok l ∧ blockItems c (k + kAfter pre) b = .ok code ∧
        ∀ r ∈ runs l (directives code), runPh okPc ph lab res ra r = true ∧
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat
  | k, [], post, b, h => by
    simp only [List.nil_append, blocksPh, Bool.and_eq_true] at h
    revert h
    cases hl : c.blockLabel b.label <;> cases hc : blockItems c k b <;> simp
    exact fun h _ => ⟨_, by simpa [kAfter] using hc, fun r hr => by simpa using h r hr⟩
  | k, p :: pre, post, b, h => by
    simp only [List.cons_append, blocksPh, Bool.and_eq_true] at h
    obtain ⟨l, code, h1, h2, h3⟩ := blocksPh_blockPh h.2
    refine ⟨l, code, h1, ?_, h3⟩
    simpa [kAfter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2

/-- **A block's runs' phase facts**, from `blocksPh`: the block `b` after
the blocks `pre`, at the same label and code as `blocksOk_block`. -/
theorem blocksPh_block {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {c : FnCtx} {ra : Int64} {k : Nat} {pre post : List Scc.IR.Block} {b : Scc.IR.Block}
    (h : blocksPh okPc ph lab res c ra k (pre ++ b :: post) = true) :
    ∃ l code, c.blockLabel b.label = .ok l ∧ blockItems c (k + kAfter pre) b = .ok code ∧
      ∀ r ∈ runs l (directives code), runPh okPc ph lab res ra r = true := by
  obtain ⟨l, code, h1, h2, h3⟩ := blocksPh_blockPh h
  exact ⟨l, code, h1, h2, fun r hr => (h3 r hr).1⟩

/-- **`runPhB` at another return address** of the same phase: only a
`ret`'s target reads it. -/
theorem runPhB_ra {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra ra' : Int64}
    {blk : List Directive} (h : runPhB okPc ph lab pc ra blk = true)
    (hra : ph ra'.toBitVec.toNat = ph ra.toBitVec.toNat) :
    runPhB okPc ph lab pc ra' blk = true := by
  have key : ∀ (o : Option Spike.Lib.A64.Flow.AI) (f p : Int64),
      ((match o with | some a => aiTgts lab f ra a | none => [f]).all fun t =>
        ph t.toBitVec.toNat == ph p.toBitVec.toNat) = true →
      ((match o with | some a => aiTgts lab f ra' a | none => [f]).all fun t =>
        ph t.toBitVec.toNat == ph p.toBitVec.toNat) = true := by
    intro o f p
    cases o with
    | none => exact id
    | some a => cases a <;> simp_all [aiTgts]
  unfold runPhB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have hk' := h k hk
  revert hk'
  generalize blk[k]? = od
  cases od with
  | none => exact id
  | some d =>
    simp only [Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨h1, key _ _ _ h2⟩

/-- **`blocksPh` at another return address** of the same phase. -/
theorem blocksPh_ra {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {c : FnCtx} {ra ra' : Int64} (hra : ph ra'.toBitVec.toNat = ph ra.toBitVec.toNat) :
    ∀ {k : Nat} {bs : List Scc.IR.Block}, blocksPh okPc ph lab res c ra k bs = true →
      blocksPh okPc ph lab res c ra' k bs = true
  | _, [], _ => rfl
  | k, b :: bs, h => by
    simp only [blocksPh, Bool.and_eq_true] at h ⊢
    refine ⟨?_, blocksPh_ra hra h.2⟩
    have h1 := h.1
    revert h1
    split
    · intro h1
      rw [List.all_eq_true] at h1 ⊢
      intro r hr
      have := h1 r hr
      simp only [runPh, Bool.and_eq_true, beq_iff_eq] at this ⊢
      exact ⟨⟨this.1.1, runPhB_ra this.1.2 hra⟩, this.2.trans hra.symm⟩
    · exact id

/-! ## A run's instructions -/

/-- **One instruction of a run** passing `runPhB`: its pc off the sites and
in the run's phase, and its targets (the next pc if `classify` does not
cover it) in that phase. -/
theorem runPhB_get {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {blk : List Directive} (h : runPhB okPc ph lab pc ra blk = true) {k : Nat} (hk : k < blk.length) :
    okPc (pc + Int64.ofNat (4 * k)).toBitVec.toNat = true ∧
    ph (pc + Int64.ofNat (4 * k)).toBitVec.toNat = ph pc.toBitVec.toNat ∧
    ∀ t ∈ (match classify blk[k] with
       | some a => aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a
       | none => [pc + Int64.ofNat (4 * k) + Int64.ofNat 4]),
      ph t.toBitVec.toNat = ph pc.toBitVec.toNat := by
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  rw [List.getElem?_eq_getElem hk] at this
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **`blkPh` of a sub-run of covered instructions**: in a run `xs ++ ys ++
zs` passing `runPhB`, with every instruction of `ys` covered, `ys` at its
pc passes `blkPh` (no dead target). -/
theorem blkPh_of_runPhB {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {xs ys zs : List Directive} (h : runPhB okPc ph lab pc ra (xs ++ ys ++ zs) = true)
    (hc : ∀ d ∈ ys, (classify d).isSome = true) :
    blkPh okPc ph (fun _ => false) lab (pc + Int64.ofNat (4 * xs.length)) ra ys = true := by
  have hpc : ∀ k, pc + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * k) = pc + Int64.ofNat (4 * (xs.length + k)) := by
    intro k; rw [Int64.add_assoc, ← Int64.ofNat_add, Nat.mul_add]
  unfold blkPh
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.mp hk
  have hlen : xs.length + k < (xs ++ ys ++ zs).length := by simp; omega
  obtain ⟨h1, h2, h3⟩ := runPhB_get h hlen
  have hget : (xs ++ ys ++ zs)[xs.length + k] = ys[k] := by
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact List.getElem_append_left hk'
  have h0 : ph (pc + Int64.ofNat (4 * xs.length)).toBitVec.toNat = ph pc.toBitVec.toNat := by
    have hlen0 : xs.length + 0 < (xs ++ ys ++ zs).length := by simp; omega
    simpa using (runPhB_get h hlen0).2.1
  rw [hget] at h3
  rw [List.getElem?_eq_getElem hk', hpc]
  have hcl := hc ys[k] (List.getElem_mem hk')
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hcl
  rw [ha] at h3
  simp only [ha, Bool.and_eq_true, beq_iff_eq, Bool.or_false, List.all_eq_true, h0]
  refine ⟨⟨h1, h2⟩, fun t ht => ?_⟩
  exact h3 t ht

/-! ## Runs and segments -/

/-- A run of `runsAux` is label-free. -/
theorem runsAux_noLabel : ∀ (l : Label) (acc ds : List Directive), (∀ d ∈ acc, ∀ l', d ≠ .label l') →
    ∀ r ∈ runsAux l acc ds, ∀ d ∈ r.2, ∀ l', d ≠ .label l'
  | l, acc, [], hacc, r, hr => by
    simp only [runsAux, List.mem_singleton] at hr; subst hr
    intro d hd; exact hacc d (List.mem_reverse.mp hd)
  | l, acc, .label l' :: ds, hacc, r, hr => by
    simp only [runsAux, List.mem_cons] at hr
    rcases hr with rfl | hr
    · intro d hd; exact hacc d (List.mem_reverse.mp hd)
    · exact runsAux_noLabel l' [] ds (by simp) r hr
  | l, acc, .instr i :: ds, hacc, r, hr => by
    simp only [runsAux] at hr
    refine runsAux_noLabel l (.instr i :: acc) ds ?_ r hr
    intro d hd l'' he
    rcases List.mem_cons.mp hd with rfl | hd
    · cases he
    · exact hacc d hd l'' he
  | l, acc, .byteArray a :: ds, hacc, r, hr => by
    simp only [runsAux] at hr
    refine runsAux_noLabel l (.byteArray a :: acc) ds ?_ r hr
    intro d hd l'' he
    rcases List.mem_cons.mp hd with rfl | hd
    · cases he
    · exact hacc d hd l'' he

/-- **The first run** of a segment `xs ++ .label l' :: ys` with `xs`
label-free is `xs`, after `l`, and the rest are `ys`'s after `l'`. -/
theorem runsAux_label : ∀ (l l' : Label) (acc xs ys : List Directive), (∀ d ∈ xs, ∀ l'', d ≠ .label l'') →
    runsAux l acc (xs ++ .label l' :: ys) = (l, acc.reverse ++ xs) :: runsAux l' [] ys
  | l, l', acc, [], ys, _ => by simp [runsAux]
  | l, l', acc, d :: xs, ys, h => by
    have hd : ∀ l'', d ≠ .label l'' := h d (List.mem_cons_self ..)
    have ih := runsAux_label l l' (d :: acc) xs ys fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    cases d with
    | label l'' => exact absurd rfl (hd l'')
    | instr i => simp only [List.cons_append, runsAux]; rw [ih]; simp
    | byteArray a => simp only [List.cons_append, runsAux]; rw [ih]; simp

/-- **The runs split at a label**: the runs of `P ++ .label m :: S` are
`P`'s, then `S`'s after `m`. -/
theorem runsAux_append_label : ∀ (l m : Label) (acc P S : List Directive),
    runsAux l acc (P ++ .label m :: S) = runsAux l acc P ++ runsAux m [] S
  | l, m, acc, [], S => by simp [runsAux]
  | l, m, acc, .label l' :: P, S => by simp [runsAux, runsAux_append_label l' m [] P S]
  | l, m, acc, .instr i :: P, S => by simp [runsAux, runsAux_append_label l m _ P S]
  | l, m, acc, .byteArray a :: P, S => by simp [runsAux, runsAux_append_label l m _ P S]

/-- **The last run** of a segment: its label-free tail `ys`, after the
segment's last label `L` (`X` ends with it), or after `l` when the segment
has no label. -/
theorem runsAux_last : ∀ (l : Label) (acc P : List Directive), ∃ L X ys,
    (runsAux l acc P).getLast? = some (L, ys) ∧ acc.reverse ++ P = X ++ ys ∧
      ((X = [] ∧ L = l) ∨ ∃ X', X = X' ++ [.label L])
  | l, acc, [] => ⟨l, [], acc.reverse, by simp [runsAux]⟩
  | l, acc, .label l' :: P => by
    obtain ⟨L, X, ys, h1, h2, h3⟩ := runsAux_last l' [] P
    simp only [List.reverse_nil, List.nil_append] at h2
    refine ⟨L, acc.reverse ++ .label l' :: X, ys, ?_, by simp [h2], ?_⟩
    · simp [runsAux, List.getLast?_cons, h1]
    · right
      rcases h3 with ⟨rfl, rfl⟩ | ⟨X', rfl⟩
      · exact ⟨acc.reverse, by simp⟩
      · exact ⟨acc.reverse ++ .label l' :: X', by simp⟩
  | l, acc, .instr i :: P => by
    obtain ⟨L, X, ys, h1, h2, h3⟩ := runsAux_last l (.instr i :: acc) P
    exact ⟨L, X, ys, by simpa [runsAux] using h1, by simpa using h2, h3⟩
  | l, acc, .byteArray a :: P => by
    obtain ⟨L, X, ys, h1, h2, h3⟩ := runsAux_last l (.byteArray a :: acc) P
    exact ⟨L, X, ys, by simpa [runsAux] using h1, by simpa using h2, h3⟩

/-- The first run of a segment is after its label. -/
theorem runsAux_head : ∀ (l : Label) (acc S : List Directive), ∃ ys, (l, ys) ∈ runsAux l acc S
  | l, acc, [] => ⟨acc.reverse, by simp [runsAux]⟩
  | l, acc, .label _ :: _ => ⟨acc.reverse, by simp [runsAux]⟩
  | l, acc, .instr i :: S => by
    obtain ⟨ys, h⟩ := runsAux_head l (.instr i :: acc) S
    exact ⟨ys, by simpa [runsAux] using h⟩
  | l, acc, .byteArray a :: S => by
    obtain ⟨ys, h⟩ := runsAux_head l (.byteArray a :: acc) S
    exact ⟨ys, by simpa [runsAux] using h⟩

/-- The runs of a label-free segment: the segment itself. -/
theorem runsAux_nil : ∀ (l : Label) (acc xs : List Directive), (∀ d ∈ xs, ∀ l'', d ≠ .label l'') →
    runsAux l acc xs = [(l, acc.reverse ++ xs)]
  | l, acc, [], _ => by simp [runsAux]
  | l, acc, d :: xs, h => by
    have hd : ∀ l'', d ≠ .label l'' := h d (List.mem_cons_self ..)
    have ih := runsAux_nil l (d :: acc) xs fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    cases d with
    | label l'' => exact absurd rfl (hd l'')
    | instr i => simp only [runsAux]; rw [ih]; simp
    | byteArray a => simp only [runsAux]; rw [ih]; simp

end Scc.Cert.Ph1A64
