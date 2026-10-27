/-
**The prologue's edge into a compiled block's body** (x86-64): `ProEdge2`
(`Spike/Lib/LowerX64/ProgC2.lean`) from the caller's facts at the entry,
for any number of parameter words (`prologue_body_segTP` of
`Spike/Lib/LowerX64/FnC.lean` generalised from one word).

- `SpillAt`, `SpillsAt`, `ParamSpillN`: the prologue's parameter spill
  `ps` for the parameter registers `prs` (cell sizes `zs`): the `k`th
  register stored from `argRegs[k]` at its cell (`rsOf`, `%rbp` at `-8`), a
  cell of the frame;
- `paramSpillN_of_spills`: `spills`' result is one;
- `xStSlots_off`, `xStSlots_paramN`: after the stores, a cell of none of
  them unchanged, and the `k`th register's cell the entry's `argRegs[k]`;
- `xFrRegs_arg`: the head, the check and the frame's set-up keep the
  argument registers;
- `proEdge2_of`: `ProEdge2` at an entry invariant `J` whose states give the
  stack limit's facts, the saved `%rbp` `fp` and return address `ra`, the
  `%fs` base `tp`, the ghost's local run, and the body's entry node's source
  facts at every slot map with the parameter registers' cells the argument
  registers; `proEdge2_ofSpills` at a compiled block's `spills` (`paramsR`).
-/
import Spike.Lib.LowerX64.ProgC2
import Spike.Lib.Src.ParamsNodup

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (xStSlots xS1 xFrRegs hdRegs)
open Scc.Lower.InvX64
open Scc.Emit.X64 (argRegs)
open Spike.Lib.LowerNode

/-- **One parameter's store** (`ParamSpillN`'s): the register `q.1.1`
stored from `q.1.2` at offset `s.2.1` from the frame record (`%rbp` at
`-8`), its cell `s.2.1` (`rsOf fr`), a cell of the frame. -/
def SpillAt (fr : Scc.Emit.X64.Frame) (q : (Scc.IR.Reg × Reg64) × Nat) (s : Reg64 × Int64 × Nat) : Prop :=
  s.1 = q.1.2 ∧ rsOf fr q.1.1 = some s.2.1.toInt ∧ s.2.1.toInt ≤ -8 ∧
    offOk (-8 - (fr.size : Int)) 0 (-8 + s.2.1.toInt) = true

/-- `SpillAt` pairwise along two lists of the same length. -/
def SpillsAt (fr : Scc.Emit.X64.Frame) : List ((Scc.IR.Reg × Reg64) × Nat) → List (Reg64 × Int64 × Nat) → Prop
  | [], [] => True
  | q :: l, s :: ps => SpillAt fr q s ∧ SpillsAt fr l ps
  | _, _ => False

/-- **The prologue's parameter spill** `ps` for the parameter registers
`prs` (the stores' sizes `zs`) of a function with frame `fr`, any number of
them up to `argRegs.length`: the `k`th register `prs[k]` stored from
`argRegs[k]` (`SpillAt`). -/
def ParamSpillN (fr : Scc.Emit.X64.Frame) (ps : List (Reg64 × Int64 × Nat)) (prs : List Scc.IR.Reg)
    (zs : List Nat) : Prop :=
  prs.length ≤ argRegs.length ∧ zs.length = prs.length ∧ SpillsAt fr ((prs.zip argRegs).zip zs) ps

/-- A successful `mapM` in `Option`, element by element: each result
`SpillAt` its argument when each successful `f` is. -/
theorem spillsAt_of_mapM {fr : Scc.Emit.X64.Frame}
    {f : (Scc.IR.Reg × Reg64) × Nat → Option (Reg64 × Int64 × Nat)}
    (hf : ∀ q s, f q = some s → SpillAt fr q s) :
    ∀ {l : List ((Scc.IR.Reg × Reg64) × Nat)} {ys : List (Reg64 × Int64 × Nat)}, l.mapM f = some ys →
      SpillsAt fr l ys
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; trivial
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some ys' =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        exact ⟨hf a b ha, spillsAt_of_mapM hf hl⟩

/-- **`spills`' result is a `ParamSpillN`** (at a frame of `FrameOk`, at
most `2 ^ 31` bytes). -/
theorem paramSpillN_of_spills {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {prs : List Scc.IR.Reg} {zs : List Nat} {ps : List (Reg64 × Int64 × Nat)}
    (h : Scc.Cert.Code1X64.spills fr prs zs = some ps) : ParamSpillN fr ps prs zs := by
  unfold Scc.Cert.Code1X64.spills at h
  split at h
  · rename_i hle
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hle
    refine ⟨hle.1, hle.2, spillsAt_of_mapM (fun q s hq => ?_) h⟩
    obtain ⟨⟨pr, r⟩, z⟩ := q
    cases ho : rsOf fr pr with
    | none => simp [ho] at hq
    | some o =>
      simp only [ho, Option.map_some, Option.some.injEq] at hq
      subst hq
      obtain ⟨h8, hm, hle'⟩ := rsOf_bounds hf ho
      have hoo : (Int64.ofInt o).toInt = o := toInt_ofInt_small (by omega) (by omega)
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp only [hoo]; exact ho
      · simp only [hoo]; omega
      · simp only [hoo, offOk, decide_eq_true_eq]; omega
  · cases h

/-- **After the parameters' stores, a cell none of them writes is
unchanged.** -/
theorem xStSlots_off (regs : Reg64s) :
    ∀ (ps : List (Reg64 × Int64 × Nat)) (sl : Int → BitVec 64) (k : Int), (∀ q ∈ ps, -8 + q.2.1.toInt ≠ k) →
      xStSlots regs ps sl k = sl k
  | [], _, _, _ => rfl
  | q :: ps, sl, k, h => by
    simp only [xStSlots]
    rw [xStSlots_off regs ps _ k fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]
    have := h q List.mem_cons_self
    simp [upd_apply, Ne.symm this]

/-- Every store of `SpillsAt` is `SpillAt` some register of `l`. -/
theorem SpillsAt.mem {fr : Scc.Emit.X64.Frame} :
    ∀ {l : List ((Scc.IR.Reg × Reg64) × Nat)} {ps : List (Reg64 × Int64 × Nat)}, SpillsAt fr l ps →
      ∀ s ∈ ps, ∃ q ∈ l, SpillAt fr q s
  | [], [], _, s, hs => absurd hs List.not_mem_nil
  | q :: l, s' :: ps, ⟨hq, hr⟩, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨q, List.mem_cons_self, hq⟩
    · obtain ⟨q', hq', h'⟩ := SpillsAt.mem hr s hs
      exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- **After a `SpillsAt`'s stores, every parameter register's cell holds
its argument register**, the registers distinct. -/
theorem xStSlots_paramN {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (regs : Reg64s) :
    ∀ {l : List ((Scc.IR.Reg × Reg64) × Nat)} {ps : List (Reg64 × Int64 × Nat)}, SpillsAt fr l ps →
      (l.map (·.1.1)).Nodup →
      ∀ (sl : Int → BitVec 64), ∀ q ∈ l, ∀ k, rsOf fr q.1.1 = some k →
        xStSlots regs ps sl (-8 + k) = regs.get64 q.1.2
  | [], [], _, _, _, q, hq, _, _ => absurd hq List.not_mem_nil
  | a :: l, s :: ps, ⟨hs, hrest⟩, hnd, sl, q, hq, k, hk => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [xStSlots]
    rcases List.mem_cons.1 hq with rfl | hq
    · obtain ⟨hs1, hrs, -, -⟩ := hs
      rw [hrs] at hk
      cases hk
      rw [xStSlots_off]
      · simp [upd_apply, hs1]
      · intro s' hs' he
        obtain ⟨a', ha', -, hrs', -, -⟩ := hrest.mem s' hs'
        have he' : s'.2.1.toInt = s.2.1.toInt := by omega
        rw [he'] at hrs'
        exact hnd.1 ⟨a', ha', rsOf_inj hf hrs' hrs⟩
    · exact xStSlots_paramN hf regs hrest hnd.2 _ q hq k hk
  | [], _ :: _, h, _, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _, _ => h.elim

/-- The cells a `ParamSpillN`'s stores write are below the saved `%rbp`. -/
theorem ParamSpillN.le8 {fr : Scc.Emit.X64.Frame} {ps : List (Reg64 × Int64 × Nat)} {prs : List Scc.IR.Reg}
    {zs : List Nat} (h : ParamSpillN fr ps prs zs) : ∀ q ∈ ps, q.2.1.toInt ≤ -8 := by
  intro q hq
  obtain ⟨_, _, -, -, h8, -⟩ := h.2.2.mem q hq
  exact h8

/-- The parameter registers of a `ParamSpillN`, its zip's first
components. -/
theorem ParamSpillN.map_fst {fr : Scc.Emit.X64.Frame} {ps : List (Reg64 × Int64 × Nat)}
    {prs : List Scc.IR.Reg} {zs : List Nat} (h : ParamSpillN fr ps prs zs) :
    ((prs.zip argRegs).zip zs).map (·.1.1) = prs := by
  have hl : (prs.zip argRegs).length ≤ zs.length := by
    rw [List.length_zip, h.2.1]; omega
  rw [show (fun q : (Scc.IR.Reg × Reg64) × Nat => q.1.1) = (·.1) ∘ (·.1) from rfl, ← List.map_map,
    List.map_fst_zip hl, List.map_fst_zip h.1]

/-- An element of a list no longer than `zs` is paired in its zip with
`zs`. -/
theorem mem_zip_of_le {α β : Type} :
    ∀ {l : List α} {zs : List β} {x : α}, l.length ≤ zs.length → x ∈ l → ∃ z, (x, z) ∈ l.zip zs
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | _ :: _, [], _, h, _ => by simp at h
  | a :: l, z :: zs, x, h, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨z, by simp⟩
    · obtain ⟨z', hz'⟩ := mem_zip_of_le (l := l) (zs := zs) (by simp at h; omega) hx
      exact ⟨z', by simp [hz']⟩

/-- **The head, the check and the frame's set-up keep the argument
registers.** -/
theorem xFrRegs_arg (Z : Int64) (v : BitVec 64) (r0 : Reg64s) :
    ∀ r ∈ argRegs, (xFrRegs Z v r0).get64 r = r0.get64 r := by
  intro r hr
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]

section Edge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}

/-- **The prologue's edge into a compiled block's body** (`ProEdge2`) from
the entry's facts: at every state of `J`, the stack limit's facts, the
saved `%rbp` `fp` and return address `ra` (at `0`), the `%fs` base `tp`,
the ghost's local run, and at every slot map with the parameter registers
`prs` (the spill's, `ParamSpillN`, distinct) holding the argument
registers and the frame record, the body's entry node's source facts
(`NJB` from no known values or buffers, `SlotRepAt`). -/
theorem proEdge2_of {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) {prs : List Scc.IR.Reg} {zs : List Nat}
    (hsp : ParamSpillN c.fr c.ps prs zs) (hnd : prs.Nodup) {ms0 : MemSide isa} {F : MachineData → Prop}
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {J : AS → Ctl → Prop}
    (hedge : ∀ σ c', J σ c' →
      (ms0.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        ms0.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, ms0.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt c.fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧ σ.regs.fsBase = tp ∧ LocalRun p c0 c' ∧
      ∀ sl : Int → BitVec 64,
        (∀ pr r, (pr, r) ∈ prs.zip argRegs → ∀ k, rsOf c.fr pr = some k → sl k = σ.regs.get64 r) →
        FrJ fp ra sl →
        (∃ L sm B, NJB p lbl (rsOf c.fr) c.lits [] [] L sm lsize B d.body (ofEnv2 c.env) sl c') ∧
          SlotRepAt i lbl (rsOf c.fr) sl c') :
    ProEdge2 p lbl lsize ms0 F c fp ra tp c0 J := by
  intro σ c' hJ
  obtain ⟨⟨hrt, hmp, hld, hG⟩, hfp, hra, htp, hc0, hN⟩ := hedge σ c' hJ
  refine ⟨hrt, hmp, hld, fun v hv => ⟨hG v hv, fun σ' hr hsl => ?_⟩⟩
  have hfr : FrJ fp ra (shSl σ'.slot) := by
    have h0 := xStSlots_off σ'.regs c.ps (xS1 σ).slot (-8)
      fun q hq => by have := hsp.le8 q hq; omega
    have h8 := xStSlots_off σ'.regs c.ps (xS1 σ).slot 0
      fun q hq => by have := hsp.le8 q hq; omega
    refine ⟨?_, ?_⟩
    · show σ'.slot (-8 + 0) = fp
      rw [hsl, show (-8 + 0 : Int) = -8 from rfl, h0, ← hfp]; simp [xS1, upd_apply]
    · show σ'.slot (-8 + 8) = ra
      rw [hsl, show (-8 + 8 : Int) = 0 from rfl, h8, ← hra]; simp [xS1, upd_apply]
  have hpar : ∀ pr r, (pr, r) ∈ prs.zip argRegs → ∀ k, rsOf c.fr pr = some k →
      shSl σ'.slot k = σ.regs.get64 r := by
    intro pr r hm k hk
    obtain ⟨z, hm'⟩ := mem_zip_of_le (zs := zs) (by have := hsp.2.1; rw [List.length_zip]; omega) hm
    show σ'.slot (-8 + k) = _
    rw [hsl, xStSlots_paramN c.hf σ'.regs hsp.2.2 (by rw [hsp.map_fst]; exact hnd) _ ((pr, r), z) hm' k hk, hr,
      xFrRegs_arg _ _ _ r (List.of_mem_zip hm).2]
  obtain ⟨hNJ, hrep⟩ := hN (shSl σ'.slot) hpar hfr
  refine ⟨⟨hNJ, hfr, hc0, hrep⟩, ?_⟩
  rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]

/-- **`proEdge2_of` at a compiled block's spill** (`spills` at its
parameter registers `paramsR d na` and any cell sizes `zs`,
`paramSpillN_of_spills`, `paramsR_nodup`). -/
theorem proEdge2_ofSpills {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) {na : Nat} {zs : List Nat}
    (hs : Scc.Cert.Code1X64.spills c.fr (Spike.Lib.LowerShape.paramsR d na) zs = some c.ps)
    {ms0 : MemSide isa} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    {J : AS → Ctl → Prop}
    (hedge : ∀ σ c', J σ c' →
      (ms0.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        ms0.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, ms0.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt c.fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧ σ.regs.fsBase = tp ∧ LocalRun p c0 c' ∧
      ∀ sl : Int → BitVec 64,
        (∀ pr r, (pr, r) ∈ (Spike.Lib.LowerShape.paramsR d na).zip argRegs → ∀ k, rsOf c.fr pr = some k →
          sl k = σ.regs.get64 r) →
        FrJ fp ra sl →
        (∃ L sm B, NJB p lbl (rsOf c.fr) c.lits [] [] L sm lsize B d.body (ofEnv2 c.env) sl c') ∧
          SlotRepAt i lbl (rsOf c.fr) sl c') :
    ProEdge2 p lbl lsize ms0 F c fp ra tp c0 J :=
  proEdge2_of c (paramSpillN_of_spills c.hf c.h1 hs) (Spike.Lib.LowerShape.paramsR_nodup d na) hedge

end Edge

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.paramSpillN_of_spills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.paramSpillN_of_spills

/-- info: 'Spike.Lib.LowerX64.proEdge2_ofSpills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proEdge2_ofSpills

/-- info: 'Spike.Lib.LowerX64.proEdge2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proEdge2_of
