import Scc.Cert.Code1X64
import Spike.Lib.LowerX64.PhCheck

/-!
# The phases of every stack-checked function (x86-64; A12's `fnPh1Ok`)

The twin of `Scc/Cert/Ph1A64.lean`. A9's phase part
(`Spike.Lib.LowerX64.fnPhOk`) checks the `func0`-shaped functions only. This
file checks the phase facts of **every** stack-checked function of the
lowered IR, the same set as `Scc.Cert.Code1X64.fnCode1Ok`, at the same
frames and label numbers (`frOf`, `starts`), at A6's tables (`phOf`,
`okPcOf`) and the cells' code labels (`labC`), fail-closed:

* the prologue's (`proPhOk`, with the parameters' stores `spills`, at the
  listing's sizes);
* every block's code (`blockItems`, as `blocksOk` numbers it), read off the
  listing with its sizes (`segCells`: the cells after the block's label, as
  many as the code has directives; `segIn` makes them the code), split into
  its label-free runs (`runs`: the first after the block's label, every
  later one after the label inside the block, a call's safepoint label say):
  each run's `runPhB` at its label (`blkPh`, an instruction it does not
  cover checked as falling through), the return address the one after
  `scc_rt_main`'s `call` (`raL`), each run's label in that return
  address's phase;
* with a checked `+`, the local overflow block's `blkPh` (as `fnPh1`);
* every label these read resolves (`res`: the function's, its stack
  check's, the runs' labels and their branch and call targets, `blkLabs`),
  so that `labC` is the loader's label on them.

`fnPh1Ok_parts`, `fnPhF_of_fnPhAll1` and `blocksPh_block` (`blocksPh_blockPh`
with the runs' phases) project it to one function and one block;
`blocksPh_ra` moves it to another return address of the same phase; `runPhB_get` to one instruction of a run, and
`blkPh_of_runPhB` to `blkPh` of a sub-run of covered instructions.
-/

namespace Scc.Cert.Ph1X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Emit.X64 (Frame labelOf directives)
open Scc.Cert.Rt.X64 (after)
open Scc.Cert.Code1X64 (blockItems nAfter spills hasAddChk chkL starts segIn segIn_iff)
open Spike.Lib.X64 (cellOff classify AI)
open Spike.Lib.X64Consumer (blkPh aiTgts)
open Spike.Lib.LowerX64 (proL ovfL ovfBlk sizesAt frOf proPhOk proLabs blkLabs labC raL)
open Scc.Sem.X64 (codeLabel)

/-! ## Label-free runs -/

/-- The label-free runs of a sized code segment, after the label `l`, `acc`
the current run reversed: each run with the label it follows. -/
def runsAux (l : Label) (acc : List (Directive × Nat)) :
    List (Directive × Nat) → List (Label × List (Directive × Nat))
  | [] => [(l, acc.reverse)]
  | (.label l', _) :: ds => (l, acc.reverse) :: runsAux l' [] ds
  | d :: ds => runsAux l (d :: acc) ds

/-- **The label-free runs of the sized segment `ds` after the label `l`**:
split at every label of `ds`, each run with the label it follows. -/
def runs (l : Label) (ds : List (Directive × Nat)) : List (Label × List (Directive × Nat)) := runsAux l [] ds

/-- **The `n` cells after the first `label l`** (none if `l` is absent). -/
def segCells (cells : List (Directive × Nat)) (l : Label) (n : Nat) : List (Directive × Nat) :=
  match after l cells with
  | some t => t.take n
  | none => []

/-- **`segIn` reads the segment off the cells**: the cells `segCells` gives
are the segment's directives, with their sizes. -/
theorem segCells_map {cells : List (Directive × Nat)} {l : Label} {ds : List Directive}
    (h : segIn cells l ds = true) : (segCells cells l ds.length).map (·.1) = ds := by
  obtain ⟨i, hi, ht, -⟩ := segIn_iff.mp h
  unfold segCells
  rw [Scc.Cert.Rt.X64.after_eq, hi]
  exact ht

/-! ## The checks -/

/-- **A run's phase check**: `blkPh` with no dead target, except that an
instruction `blkPh` does not cover (`classify` is `none`: a load or store
off the thread pointer, a system call) is checked as falling through, its
next pc in the run's phase. Every pc is off the sites and in the phase of
the run's first pc, and so is every target. On a sub-run of covered
instructions it gives `blkPh` (`blkPh_of_runPhB`). -/
def runPhB (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (pc ra : Int64)
    (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    okPc (pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat &&
    ph (pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat == ph pc.toBitVec.toNat &&
    match blk[k]? with
    | some dz =>
      (match classify dz.1 with
       | some a => aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) ra a
       | none => [pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2]).all fun t =>
        ph t.toBitVec.toNat == ph pc.toBitVec.toNat
    | none => false

/-- One run's phase facts: its label and its targets resolve, and its
`runPhB` at its label, the return address `ra`. -/
def runPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (ra : Int64)
    (r : Label × List (Directive × Nat)) : Bool :=
  res r.1 && (blkLabs r.2).all res && runPhB okPc ph lab (lab r.1) ra r.2

/-- **Every block's runs' phase facts**, the blocks' local labels numbered
from `n` on (as `blocksOk`), every run's label in the phase of the return
address `ra` (so that the facts hold at any return address of that phase,
`blocksPh_ra`: a call's return label, say). -/
def blocksPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (fr : Frame) (ra : Int64) :
    Nat → List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) → Bool
  | _, [] => true
  | n, (b, ms) :: bs =>
    match blockItems fr n b ms with
    | .ok (code, n') =>
      (runs (labelOf fr.fn b.label)
          (segCells cells (labelOf fr.fn b.label) (directives code).length)).all (fun r =>
            runPh okPc ph lab res ra r && ph (lab r.1).toBitVec.toNat == ph ra.toBitVec.toNat) &&
        blocksPh okPc ph lab res cells fr ra n' bs
    | .error _ => false

/-- **One stack-checked function's phase facts**, its local labels numbered
from `n`: the prologue's with the parameters' stores, every block's runs',
with a checked `+` the overflow block's, every label read resolving. -/
def fnPhF (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) (n : Nat) (f : Scc.IR.Func) (ra : Int64) : Bool :=
  match sizesAt cells (chkL f) 0 (5 + f.params.length) with
  | zl :: zf :: z1 :: z2 :: zs :: zps =>
    match spills (frOf ir f) f.params zps with
    | some ps =>
      res f.name && res (chkL f) &&
      (proLabs (Int64.ofInt (frOf ir f).size) (proL (frOf ir f)) zl z1 z2 zs ps).all res &&
      proPhOk okPc ph lab f.name (chkL f) (Int64.ofInt (frOf ir f).size) (proL (frOf ir f)) zl zf z1 z2 zs ps &&
      blocksPh okPc ph lab res cells (frOf ir f) ra n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) &&
      (!hasAddChk f || (res (ovfL (frOf ir f)) && (blkLabs ovfBlk).all res &&
        blkPh okPc ph (fun _ => false) lab (lab (ovfL (frOf ir f)) + Int64.ofNat 0) 0 ovfBlk))
    | none => false
  | _ => false

/-- **Every stack-checked function's phase facts** (the functions
`fnCode1Ok` checks, at their frames and label numbers recomputed from
`ir`). -/
def fnPhAll1 (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  (starts ir 0 ir.funcs).all fun (f, n) => !f.checkStack || fnPhF okPc ph lab res cells ir n f ra

/-- **A12's phase part**: at A6's phase table and sites of the cells at
`lo` (`false` if either is missing) and the cells' code labels, every
stack-checked function's phase facts, the return address after
`scc_rt_main`'s `call` (`raL`). -/
def fnPh1Ok (lo : Nat) (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (ir : Scc.IR.Program) : Bool :=
  match Scc.Cert.Rt.X64.phTabOf lo cells, Scc.Cert.Rt.X64.sitesOf lo cells Λ with
  | some T, some ss =>
    (codeLabel lo cells raL).isSome &&
      fnPhAll1 (fun pc => !ss.contains pc) T.ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells ir
        (labC lo cells raL)
  | _, _ => false

/-! ## Its parts -/

/-- **`fnPh1Ok`'s parts** at A6's `phOf`/`okPcOf`. -/
theorem fnPh1Ok_parts {lo : Nat} {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)} {ir : Scc.IR.Program}
    (h : fnPh1Ok lo Λ cells ir = true) :
    (codeLabel lo cells raL).isSome = true ∧
      fnPhAll1 (Scc.Cert.Rt.X64.okPcOf lo cells Λ) (Scc.Cert.Rt.X64.phOf lo cells) (labC lo cells)
        (fun l => (codeLabel lo cells l).isSome) cells ir (labC lo cells raL) = true := by
  unfold fnPh1Ok at h
  split at h
  · next T ss hT hs =>
    simp only [Bool.and_eq_true] at h
    have hph : Scc.Cert.Rt.X64.phOf lo cells = T.ph := by unfold Scc.Cert.Rt.X64.phOf; rw [hT]
    have hok : Scc.Cert.Rt.X64.okPcOf lo cells Λ = fun pc => !ss.contains pc := by
      funext pc; unfold Scc.Cert.Rt.X64.okPcOf; rw [hs]
    rw [hph, hok]
    exact h
  · cases h

/-- **`fnPhF` of a stack-checked function** of `ir`, from `fnPhAll1`. -/
theorem fnPhF_of_fnPhAll1 {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {cells : List (Directive × Nat)} {ir : Scc.IR.Program} {ra : Int64}
    (h : fnPhAll1 okPc ph lab res cells ir ra = true)
    {f : Scc.IR.Func} {n : Nat} (hf : (f, n) ∈ starts ir 0 ir.funcs) (hc : f.checkStack = true) :
    fnPhF okPc ph lab res cells ir n f ra = true := by
  have := List.all_eq_true.mp h _ hf
  simpa [hc] using this

/-- **The facts of `fnPhF`** at the prologue's cells' sizes and the
parameters' stores `ps`. -/
theorem fnPhF_facts {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {cells : List (Directive × Nat)} {ir : Scc.IR.Program} {n : Nat} {f : Scc.IR.Func} {ra : Int64}
    (h : fnPhF okPc ph lab res cells ir n f ra = true) {zl zf z1 z2 zs : Nat} {zps : List Nat}
    (hz : sizesAt cells (chkL f) 0 (5 + f.params.length) = zl :: zf :: z1 :: z2 :: zs :: zps)
    {ps : List (Reg64 × Int64 × Nat)} (hps : spills (frOf ir f) f.params zps = some ps) :
    res f.name = true ∧ res (chkL f) = true ∧
    (proLabs (Int64.ofInt (frOf ir f).size) (proL (frOf ir f)) zl z1 z2 zs ps).all res = true ∧
    proPhOk okPc ph lab f.name (chkL f) (Int64.ofInt (frOf ir f).size) (proL (frOf ir f)) zl zf z1 z2 zs ps = true ∧
    blocksPh okPc ph lab res cells (frOf ir f) ra n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) = true ∧
    (hasAddChk f = true → res (ovfL (frOf ir f)) = true ∧ (blkLabs ovfBlk).all res = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (ovfL (frOf ir f)) + Int64.ofNat 0) 0 ovfBlk = true) := by
  unfold fnPhF at h
  rw [hz] at h
  simp only [hps, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun ha => ?_⟩
  have := h6.resolve_left (by simp [ha])
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **A block's runs' phase facts and phases**, from `blocksPh`: the block
`b` after the blocks `pre`, at the same code as `blocksOk_block`, every
run's label in the phase of `ra`. -/
theorem blocksPh_blockPh {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {cells : List (Directive × Nat)} {fr : Frame} {ra : Int64} :
    ∀ {n : Nat} {pre post : List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry))} {b : Scc.IR.Block}
      {ms : List (Option Scc.IR.StackMap.Entry)},
      blocksPh okPc ph lab res cells fr ra n (pre ++ (b, ms) :: post) = true →
      ∃ code n', blockItems fr (nAfter fr n pre) b ms = .ok (code, n') ∧
        ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
          runPh okPc ph lab res ra r = true ∧ ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat
  | n, [], post, b, ms, h => by
    simp only [List.nil_append, blocksPh] at h
    revert h
    cases hc : blockItems fr n b ms with
    | error => simp
    | ok r =>
      obtain ⟨code, n'⟩ := r
      simp only [Bool.and_eq_true, List.all_eq_true]
      exact fun h => ⟨code, n', by simpa [nAfter] using hc, fun r hr => by simpa using h.1 r hr⟩
  | n, (p, pm) :: pre, post, b, ms, h => by
    simp only [List.cons_append, blocksPh] at h
    revert h
    cases hc : blockItems fr n p pm with
    | error => simp
    | ok r =>
      obtain ⟨code, n'⟩ := r
      simp only [Bool.and_eq_true]
      intro h
      obtain ⟨c, m, h1, h2⟩ := blocksPh_blockPh h.2
      exact ⟨c, m, by simpa [nAfter, hc] using h1, h2⟩

/-- **A block's runs' phase facts**, from `blocksPh`: the block `b` after
the blocks `pre`, at the same code as `blocksOk_block`. -/
theorem blocksPh_block {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {cells : List (Directive × Nat)} {fr : Frame} {ra : Int64} {n : Nat}
    {pre post : List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry))} {b : Scc.IR.Block}
    {ms : List (Option Scc.IR.StackMap.Entry)}
    (h : blocksPh okPc ph lab res cells fr ra n (pre ++ (b, ms) :: post) = true) :
    ∃ code n', blockItems fr (nAfter fr n pre) b ms = .ok (code, n') ∧
      ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
        runPh okPc ph lab res ra r = true := by
  obtain ⟨code, n', h1, h2⟩ := blocksPh_blockPh h
  exact ⟨code, n', h1, fun r hr => (h2 r hr).1⟩

/-! ## A run's instructions -/

/-- **One instruction of a run** passing `runPhB`: its pc off the sites and
in the run's phase, and its targets (the next pc if `classify` does not
cover it) in that phase. -/
theorem runPhB_get {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {blk : List (Directive × Nat)} (h : runPhB okPc ph lab pc ra blk = true) {k : Nat} (hk : k < blk.length) :
    okPc (pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat = true ∧
    ph (pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat = ph pc.toBitVec.toNat ∧
    ∀ t ∈ (match classify blk[k].1 with
       | some a => aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a
       | none => [pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2]),
      ph t.toBitVec.toNat = ph pc.toBitVec.toNat := by
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  rw [List.getElem?_eq_getElem hk] at this
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **`runPhB` at another return address** of the same phase: only a
`ret`'s target reads it. -/
theorem runPhB_ra {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra ra' : Int64}
    {blk : List (Directive × Nat)} (h : runPhB okPc ph lab pc ra blk = true)
    (hra : ph ra'.toBitVec.toNat = ph ra.toBitVec.toNat) :
    runPhB okPc ph lab pc ra' blk = true := by
  have key : ∀ (o : Option AI) (f p : Int64),
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
    {cells : List (Directive × Nat)} {fr : Frame} {ra ra' : Int64}
    (hra : ph ra'.toBitVec.toNat = ph ra.toBitVec.toNat) :
    ∀ {n : Nat} {bs : List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry))},
      blocksPh okPc ph lab res cells fr ra n bs = true → blocksPh okPc ph lab res cells fr ra' n bs = true
  | _, [], _ => rfl
  | n, (b, ms) :: bs, h => by
    simp only [blocksPh] at h ⊢
    revert h
    cases blockItems fr n b ms with
    | error => exact id
    | ok r =>
      obtain ⟨code, n'⟩ := r
      simp only [Bool.and_eq_true]
      intro h
      refine ⟨?_, blocksPh_ra hra h.2⟩
      rw [List.all_eq_true] at h ⊢
      intro r hr
      have := h.1 r hr
      simp only [runPh, Bool.and_eq_true, beq_iff_eq] at this ⊢
      exact ⟨⟨this.1.1, runPhB_ra this.1.2 hra⟩, this.2.trans hra.symm⟩

/-- The byte offset of a cell of the middle part of `xs ++ ys ++ zs`. -/
theorem cellOff_mid {xs ys zs : List (Directive × Nat)} {k : Nat} (hk : k ≤ ys.length) :
    cellOff (xs ++ ys ++ zs) (xs.length + k) = cellOff (xs ++ ys ++ zs) xs.length + cellOff ys k := by
  unfold cellOff
  rw [List.append_assoc, List.take_length_add_append, List.take_left' rfl,
    List.take_append_of_le_length hk]
  simp

/-- **`blkPh` of a sub-run of covered instructions**: in a run `xs ++ ys ++
zs` passing `runPhB`, with every instruction of `ys` covered, `ys` at its
pc passes `blkPh` (no dead target). -/
theorem blkPh_of_runPhB {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {xs ys zs : List (Directive × Nat)} (h : runPhB okPc ph lab pc ra (xs ++ ys ++ zs) = true)
    (hc : ∀ d ∈ ys, (classify d.1).isSome = true) :
    blkPh okPc ph (fun _ => false) lab (pc + Int64.ofNat (cellOff (xs ++ ys ++ zs) xs.length)) ra ys = true := by
  have hpc : ∀ k, k ≤ ys.length → pc + Int64.ofNat (cellOff (xs ++ ys ++ zs) xs.length) + Int64.ofNat (cellOff ys k) =
      pc + Int64.ofNat (cellOff (xs ++ ys ++ zs) (xs.length + k)) := by
    intro k hk; rw [cellOff_mid hk, Int64.add_assoc, ← Int64.ofNat_add]
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
  have h0 : ph (pc + Int64.ofNat (cellOff (xs ++ ys ++ zs) xs.length)).toBitVec.toNat = ph pc.toBitVec.toNat := by
    have hlen0 : xs.length + 0 < (xs ++ ys ++ zs).length := by simp; omega
    simpa using (runPhB_get h hlen0).2.1
  rw [hget] at h3
  rw [List.getElem?_eq_getElem hk', hpc k (by omega)]
  have hcl := hc ys[k] (List.getElem_mem hk')
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hcl
  rw [ha] at h3
  simp only [ha, Bool.and_eq_true, beq_iff_eq, Bool.or_false, List.all_eq_true, h0]
  exact ⟨⟨h1, h2⟩, fun t ht => h3 t ht⟩

/-! ## Runs and segments -/

/-- A run of `runsAux` is label-free. -/
theorem runsAux_noLabel : ∀ (l : Label) (acc ds : List (Directive × Nat)), (∀ d ∈ acc, d.1.isLabel = false) →
    ∀ r ∈ runsAux l acc ds, ∀ d ∈ r.2, d.1.isLabel = false
  | l, acc, [], hacc, r, hr => by
    simp only [runsAux, List.mem_singleton] at hr; subst hr
    intro d hd; exact hacc d (List.mem_reverse.mp hd)
  | l, acc, (.label l', _) :: ds, hacc, r, hr => by
    simp only [runsAux, List.mem_cons] at hr
    rcases hr with rfl | hr
    · intro d hd; exact hacc d (List.mem_reverse.mp hd)
    · exact runsAux_noLabel l' [] ds (by simp) r hr
  | l, acc, (.instr i, z) :: ds, hacc, r, hr => by
    simp only [runsAux] at hr
    refine runsAux_noLabel l ((.instr i, z) :: acc) ds ?_ r hr
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · rfl
    · exact hacc d hd
  | l, acc, (.byteArray a, z) :: ds, hacc, r, hr => by
    simp only [runsAux] at hr
    refine runsAux_noLabel l ((.byteArray a, z) :: acc) ds ?_ r hr
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · rfl
    · exact hacc d hd

/-- **The first run** of a segment `xs ++ (.label l', z) :: ys` with `xs`
label-free is `xs`, after `l`, and the rest are `ys`'s after `l'`. -/
theorem runsAux_label : ∀ (l l' : Label) (z : Nat) (acc xs ys : List (Directive × Nat)),
    (∀ d ∈ xs, d.1.isLabel = false) →
    runsAux l acc (xs ++ (.label l', z) :: ys) = (l, acc.reverse ++ xs) :: runsAux l' [] ys
  | l, l', z, acc, [], ys, _ => by simp [runsAux]
  | l, l', z, acc, d :: xs, ys, h => by
    have hd : d.1.isLabel = false := h d (List.mem_cons_self ..)
    have ih := runsAux_label l l' z (d :: acc) xs ys fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    obtain ⟨d, zd⟩ := d
    cases d with
    | label l'' => cases hd
    | instr i => simp only [List.cons_append, runsAux]; rw [ih]; simp
    | byteArray a => simp only [List.cons_append, runsAux]; rw [ih]; simp

/-- **The runs split at a label**: the runs of `P ++ (.label m, z) :: S` are
`P`'s, then `S`'s after `m`. -/
theorem runsAux_append_label : ∀ (l m : Label) (z : Nat) (acc P S : List (Directive × Nat)),
    runsAux l acc (P ++ (.label m, z) :: S) = runsAux l acc P ++ runsAux m [] S
  | l, m, z, acc, [], S => by simp [runsAux]
  | l, m, z, acc, (.label l', _) :: P, S => by simp [runsAux, runsAux_append_label l' m z [] P S]
  | l, m, z, acc, (.instr i, w) :: P, S => by simp [runsAux, runsAux_append_label l m z _ P S]
  | l, m, z, acc, (.byteArray a, w) :: P, S => by simp [runsAux, runsAux_append_label l m z _ P S]

/-- **The last run** of a segment: its label-free tail `ys`, after the
segment's last label `L` (`X` ends with it), or after `l` when the segment
has no label. -/
theorem runsAux_last : ∀ (l : Label) (acc P : List (Directive × Nat)), ∃ L X ys,
    (runsAux l acc P).getLast? = some (L, ys) ∧ acc.reverse ++ P = X ++ ys ∧
      ((X = [] ∧ L = l) ∨ ∃ X' z, X = X' ++ [(.label L, z)])
  | l, acc, [] => ⟨l, [], acc.reverse, by simp [runsAux]⟩
  | l, acc, (.label l', z) :: P => by
    obtain ⟨L, X, ys, h1, h2, h3⟩ := runsAux_last l' [] P
    simp only [List.reverse_nil, List.nil_append] at h2
    refine ⟨L, acc.reverse ++ (.label l', z) :: X, ys, ?_, by simp [h2], ?_⟩
    · simp [runsAux, List.getLast?_cons, h1]
    · right
      rcases h3 with ⟨rfl, rfl⟩ | ⟨X', z', rfl⟩
      · exact ⟨acc.reverse, z, by simp⟩
      · exact ⟨acc.reverse ++ (.label l', z) :: X', z', by simp⟩
  | l, acc, (.instr i, w) :: P => by
    obtain ⟨L, X, ys, h1, h2, h3⟩ := runsAux_last l ((.instr i, w) :: acc) P
    exact ⟨L, X, ys, by simpa [runsAux] using h1, by simpa using h2, h3⟩
  | l, acc, (.byteArray a, w) :: P => by
    obtain ⟨L, X, ys, h1, h2, h3⟩ := runsAux_last l ((.byteArray a, w) :: acc) P
    exact ⟨L, X, ys, by simpa [runsAux] using h1, by simpa using h2, h3⟩

/-- The first run of a segment is after its label. -/
theorem runsAux_head : ∀ (l : Label) (acc S : List (Directive × Nat)), ∃ ys, (l, ys) ∈ runsAux l acc S
  | l, acc, [] => ⟨acc.reverse, by simp [runsAux]⟩
  | l, acc, (.label _, _) :: _ => ⟨acc.reverse, by simp [runsAux]⟩
  | l, acc, (.instr i, w) :: S => by
    obtain ⟨ys, h⟩ := runsAux_head l ((.instr i, w) :: acc) S
    exact ⟨ys, by simpa [runsAux] using h⟩
  | l, acc, (.byteArray a, w) :: S => by
    obtain ⟨ys, h⟩ := runsAux_head l ((.byteArray a, w) :: acc) S
    exact ⟨ys, by simpa [runsAux] using h⟩

/-- The runs of a label-free segment: the segment itself. -/
theorem runsAux_nil : ∀ (l : Label) (acc xs : List (Directive × Nat)), (∀ d ∈ xs, d.1.isLabel = false) →
    runsAux l acc xs = [(l, acc.reverse ++ xs)]
  | l, acc, [], _ => by simp [runsAux]
  | l, acc, d :: xs, h => by
    have hd : d.1.isLabel = false := h d (List.mem_cons_self ..)
    have ih := runsAux_nil l (d :: acc) xs fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    obtain ⟨d, zd⟩ := d
    cases d with
    | label l'' => cases hd
    | instr i => simp only [runsAux]; rw [ih]; simp
    | byteArray a => simp only [runsAux]; rw [ih]; simp

end Scc.Cert.Ph1X64
