/-
**The edges of an `Accepted2` body's code-carrying constructs** (AArch64):
`Spike/Lib/LowerA64/Node.lean`'s and `Node1.lean`'s block edges at the
nodes with buffers and slices (`bodyN2`, `pendN2`, `abortN2`,
`Spike/Lib/LowerA64/Node2.lean`), the machine halves (`add_block`,
`sub_block`, `br_block`, …) reused, the source halves at `NJB`
(`NJB.add_ok`, `NJB.sub_ok`, `NJB.ifeq`, `NJL.add_ovf`).

- `add_edge2`: a checked `+` to the pending store, or on carry to the
  overflow abort label;
- `sub_edge2`: a saturating `-` to the pending store;
- `store_edge2`: the pending store's `str` to the next node;
- `br_edge2`, `jmp_edge2`: an `if`'s compare-and-branch, and `b F`;
- `ret_edge2`: a one-word `ret` through `x0` and the epilogue to `retN2`;
- `ret_edgeN2`: a `ret` of any number of words, each placed at one operand,
  through `retLoads` (`arun_retLoads`, `okBlk_retLoads`) and the epilogue.

The edges are stated at a lowering environment's source layout
(`ofEnv2 env`), where a one-word operand's scalar `litMask` follows from the
node (`NJB.litMask_one`); the walk's `InLits` at the operands are premises.
-/
import Spike.Lib.LowerA64.Node1
import Spike.Lib.LowerA64.Node2
import Spike.Lib.Src.NJLB2
import Spike.Lib.LowerA64.Body2Arms

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal SEnv sevalAt lookupS)
open Spike.Lib.LowerNode
open Scc.Lower (litAt)

set_option linter.unusedSimpArgs false

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {c0 : Ctl}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **The checked `+`'s edge** at `bodyN2`: to the pending store with the
walk's next layouts, known values and buffers, or on carry to the overflow
abort label. -/
theorem add_edge2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : cx.slotOff d = .ok off) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {env : Scc.Lower.Env} {ta tb : Ty}
    (hsa : sevalAt (ofEnv2 env) a = some (ta, [.one pa])) (hsb : sevalAt (ofEnv2 env) b = some (tb, [.one pb]))
    (hia : InLits lits a) (hib : InLits lits b)
    (hfr : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS (ofEnv2 env) y).isSome)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (himm : ImmIn i (ofEnv2 env) (.let_ x (.add a b) e))
    (hT : T (.let_ x (.add a b) e))
    (htot' : ∀ y ∈ Scc.Sem.exprFv e, (lookupS ((x, .int, [.one (.reg d)]) :: ofEnv2 env) y).isSome)
    (hlb' : LocBaseRegAt ((x, .int, [.one (.reg d)]) :: ofEnv2 env) e)
    (himm' : ImmIn i ((x, .int, [.one (.reg d)]) :: ofEnv2 env) e) :
    BlkEdge p lab (-(cx.frame : Int)) 0
      (bodyN2 p lbl lsize i cx fp ra c0 pc (.let_ x (.add a b) e) (ofEnv2 env) lits cs bufs)
      (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow")))
      (fun _ : Unit => pendN2 p lbl lsize i cx fp ra c0
        (pc + Int64.ofNat (4 * (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))).length))
        e ((x, .int, [.one (.reg d)]) :: ofEnv2 env) ((x, .leaf none) :: lits) (Scc.Lower.csAfter x cs (.add a b))
        (Scc.Lower.bufsAfter x cs bufs (.add a b)) (off - cx.frame))
      (fun _ : Unit => abortN2 i T p lbl cx lab fp ra c0) := by
  have hne : directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow")) ≠ [] := by
    simp [directives_append, directives_addChecked]
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx)
      (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_addChecked _
  refine ⟨hne, hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  have hma := hJ.litMask_one hsa hia
  have hmb := hJ.litMask_one hsb hib
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, h9, hsl⟩ :=
    add_block hf h1 h16 ha hb (cx.local "abort_overflow") lab pc σ
  have hrd : rsOf cx d = some (off - cx.frame) := by simp [rsOf, hd]
  have hfr' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rsOf cx r = some k' →
      k' ≠ off - cx.frame := by
    intro q hq pl hpl o ho r k' hor hr' hk
    subst hk
    exact hfr q hq pl hpl o ho r hor (rsOf_inj hr' hrd)
  by_cases hlt : va.toNat + vb.toNat < 2 ^ 64
  · -- the source past the `+`: the node's invariant at the control itself
    obtain ⟨c2, hr2, hj2, hn2, hb2, hm2, hS2⟩ := hJ.add_ok hsa hsb hia hib hma hmb hva hvb hlt
      hrd hfr' (v := va + vb) (by rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hlt)
    refine ⟨c2, hr2, .inl ⟨(), ?_, ?_, ?_, ?_, hc0.trans hr2, ?_⟩⟩
    · show pc + _ = _
      rw [hpc]; simp [hlt]
    · show SO.le (oF cx) _ = true
      rw [hso]; exact so_le_refl _ rfl
    · show ∃ L sm B, NJB p lbl (rsOf cx) _ _ _ L sm lsize B e _ (upd _ (off - cx.frame) _) c2
      rw [hsl, h9]
      exact ⟨L, sm, B, NJB.of_nodeJE hj2 hn2 hb2 hm2 hS2⟩
    · show FrJ fp ra _
      rw [hsl]; exact hfj
    · show SlotRepAt i lbl (rsOf cx) (upd _ (off - cx.frame) _) c2
      rw [hsl, h9]
      exact SlotRepAt.of_nodeJE hj2 htot' hlb' himm'
  · obtain ⟨c1, hr, hab, hS, ht⟩ := hJ.add_ovf_term hsa hsb hia hib hma hmb hva hvb (by omega) htot
    refine ⟨c1, hr, .inr ⟨(), ?_, ?_, ?_, hc0.trans hr⟩⟩
    · show _ = _
      rw [hpc]; simp [hlt]; rfl
    · show SO.le (oF cx) _ = true
      rw [hso]; exact so_le_refl _ rfl
    · show AbJ2 i T lbl cx fp ra _ c1
      rw [AbJ2, hsl]; exact ⟨⟨_, lits, hab, hS, ht ▸ himm.retype c1.env,
        ht ▸ (LocBaseRegAt.let_add hsa hsb hlb').retype c1.env, ht ▸ hT⟩, hfj⟩

/-- **The saturating `-`'s edge** at `bodyN2`: to the pending store with the
walk's next layouts, known values and buffers. -/
theorem sub_edge2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : cx.slotOff d = .ok off) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {env : Scc.Lower.Env} {ta tb : Ty}
    (hsa : sevalAt (ofEnv2 env) a = some (ta, [.one pa])) (hsb : sevalAt (ofEnv2 env) b = some (tb, [.one pb]))
    (hia : InLits lits a) (hib : InLits lits b)
    (hfr : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    {i : Expr → String → Nat → Option Nat}
    (htot' : ∀ y ∈ Scc.Sem.exprFv e, (lookupS ((x, .int, [.one (.reg d)]) :: ofEnv2 env) y).isSome)
    (hlb' : LocBaseRegAt ((x, .int, [.one (.reg d)]) :: ofEnv2 env) e)
    (himm' : ImmIn i ((x, .int, [.one (.reg d)]) :: ofEnv2 env) e) :
    BlkEdge p lab (-(cx.frame : Int)) 0
      (bodyN2 p lbl lsize i cx fp ra c0 pc (.let_ x (.sub a b) e) (ofEnv2 env) lits cs bufs)
      (directives (la ++ lb ++ subSat .X9 .X9 .X10))
      (fun _ : Unit => pendN2 p lbl lsize i cx fp ra c0
          (pc + Int64.ofNat (4 * (directives (la ++ lb ++ subSat .X9 .X9 .X10)).length))
          e ((x, .int, [.one (.reg d)]) :: ofEnv2 env) ((x, .leaf none) :: lits) (Scc.Lower.csAfter x cs (.sub a b))
          (Scc.Lower.bufsAfter x cs bufs (.sub a b)) (off - cx.frame)) (fun e : Empty => e.elim) := by
  have hne : directives (la ++ lb ++ subSat .X9 .X9 .X10) ≠ [] := by
    simp [directives_append, directives_subSat]
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (la ++ lb ++ subSat .X9 .X9 .X10)) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_subSat
  refine ⟨hne, hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  have hma := hJ.litMask_one hsa hia
  have hmb := hJ.litMask_one hsb hib
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, h9, hsl⟩ :=
    sub_block hf h1 h16 ha hb lab pc σ
  have hrd : rsOf cx d = some (off - cx.frame) := by simp [rsOf, hd]
  have hfr' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rsOf cx r = some k' →
      k' ≠ off - cx.frame := by
    intro q hq pl hpl o ho r k' hor hr' hk
    subst hk
    exact hfr q hq pl hpl o ho r hor (rsOf_inj hr' hrd)
  -- the source past the `-`: the node's invariant at the control itself
  obtain ⟨c2, hr2, hj2, hn2, hb2, hm2, hS2⟩ :=
    hJ.sub_ok hsa hsb hia hib hma hmb hva hvb hrd hfr' h9
  refine ⟨c2, hr2, .inl ⟨(), ?_, ?_, ?_, ?_, hc0.trans hr2, ?_⟩⟩
  · show pc + _ = _
    rw [hpc]
  · show SO.le (oF cx) _ = true
    rw [hso]; exact so_le_refl _ rfl
  · show ∃ L sm B, NJB p lbl (rsOf cx) _ _ _ L sm lsize B e _ (upd _ (off - cx.frame) _) c2
    rw [hsl]
    exact ⟨L, sm, B, NJB.of_nodeJE hj2 hn2 hb2 hm2 hS2⟩
  · show FrJ fp ra _
    rw [hsl]; exact hfj
  · show SlotRepAt i lbl (rsOf cx) (upd _ (off - cx.frame) _) c2
    rw [hsl]
    exact SlotRepAt.of_nodeJE hj2 htot' hlb' himm'

/-- **The pending store `str x9, [sp, #off]`'s edge** at `pendN2`: to the
next node. -/
theorem store_edge2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {d : Scc.IR.Reg} {off : Int} (hd : cx.slotOff d = .ok off) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {t : Expr} {s : SEnv} {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(cx.frame : Int)) 0 (pendN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs (off - cx.frame))
      (directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)])
      (fun _ : Unit => bodyN2 p lbl lsize i cx fp ra c0 (pc + 4) t s lits cs bufs) (fun e : Empty => e.elim) := by
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hds : directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)] =
      [(.X9, Int64.ofInt off)].map fun q => spStr q.1 q.2 := rfl
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx)
      (directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)]) = true := by
    rw [hds]
    refine okBlk_spStrs (by simp [oF]; omega) fun q hq => ?_
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [oF, ho, offOk, decide_eq_true_eq]
    omega
  refine ⟨by rw [hds]; simp, hok, fun σ c ⟨hJ, hfj, hc0, hsr⟩ =>
    ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_, ?_, hc0, ?_⟩⟩⟩
  all_goals simp only [hds, List.map_cons, List.map_nil, arun, List.foldl, pendN2, oF] at *
  all_goals rw [dstep_spStr]
  · rfl
  · exact so_le_refl _ rfl
  · show ∃ L sm B, NJB _ _ _ _ _ _ L sm lsize B _ _ (upd σ.slot _ _) c
    rw [ho, show -(cx.frame : Int) + off = off - cx.frame by omega]
    exact hJ
  · obtain ⟨h16', h8'⟩ := hfj
    have hk1 : (-16 : Int) ≠ -(cx.frame : Int) + (Int64.ofInt off).toInt := by rw [ho]; omega
    have hk2 : (-8 : Int) ≠ -(cx.frame : Int) + (Int64.ofInt off).toInt := by rw [ho]; omega
    show upd σ.slot _ _ (-16) = fp ∧ upd σ.slot _ _ (-8) = ra
    simp only [upd_apply, hk1, hk2, ↓reduceIte, h16', h8', and_self]
  · show SlotRepAt _ _ _ (upd σ.slot _ _) c
    rw [ho, show -(cx.frame : Int) + off = off - cx.frame by omega]
    exact hsr

/-- **An `if`'s compare-and-branch's edge** at `bodyN2`: the internal nodes
indexed by the comparison's outcome, the layouts unchanged. -/
theorem br_edge2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    (T : Label) {pc : Int64} (lab : Label → Int64) {fp ra : BitVec 64} {a b : At} {yes no : Expr}
    {env : Scc.Lower.Env} {ta tb : Ty}
    (hsa : sevalAt (ofEnv2 env) a = some (ta, [.one pa])) (hsb : sevalAt (ofEnv2 env) b = some (tb, [.one pb]))
    (hia : InLits lits a) (hib : InLits lits b) {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(cx.frame : Int)) 0
      (bodyN2 p lbl lsize i cx fp ra c0 pc (.ifeq a b yes no) (ofEnv2 env) lits cs bufs)
      (brDirs la lb T)
      (fun bb : Bool =>
        if bb then bodyN2 p lbl lsize i cx fp ra c0 (lab T) yes (ofEnv2 env) lits cs bufs
        else bodyN2 p lbl lsize i cx fp ra c0 (pc + Int64.ofNat (4 * (brDirs la lb T).length)) no (ofEnv2 env) lits cs
          bufs)
      (fun e : Empty => e.elim) := by
  have hne : brDirs la lb T ≠ [] := by simp [brDirs, directives_append, directives_cmpJcc]
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (brDirs la lb T) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [brDirs, directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_cmpJcc T
  refine ⟨hne, hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, hsr⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, hsl⟩ :=
    br_block hf h1 h16 ha hb T lab pc σ
  have hJ' := hJ.ifeq hsa hsb hia hib (hJ.litMask_one hsa hia) (hJ.litMask_one hsb hib) hva hvb
  refine ⟨c, .refl c, .inl ⟨decide (va = vb), ?_⟩⟩
  by_cases h : va = vb
  · have : va.toNat = vb.toNat := by rw [h]
    simp only [h, decide_true, ite_true] at hpc ⊢
    refine ⟨hpc.symm, ?_, ?_⟩
    · rw [hso]; exact so_le_refl _ rfl
    · show (∃ L sm B, NJB _ _ _ _ _ _ L sm lsize B _ _ _ c) ∧ _ ∧ _ ∧ _
      rw [hsl]
      exact ⟨⟨L, sm, B, by simpa [this] using hJ'⟩, hfj, hc0, hsr⟩
  · have : va.toNat ≠ vb.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [h, decide_false, Bool.false_eq_true, ite_false] at hpc ⊢
    refine ⟨hpc.symm, ?_, ?_⟩
    · rw [hso]; exact so_le_refl _ rfl
    · show (∃ L sm B, NJB _ _ _ _ _ _ L sm lsize B _ _ _ c) ∧ _ ∧ _ ∧ _
      rw [hsl]
      exact ⟨⟨L, sm, B, by simpa [this] using hJ'⟩, hfj, hc0, hsr⟩

/-- **`b F`'s edge** at `bodyN2`. -/
theorem jmp_edge2 {cx : FnCtx} (Fl : Label) {pc : Int64} (lab : Label → Int64) {fp ra : BitVec 64} {t : Expr}
    {s : SEnv} {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) (jmpDirs Fl)
      (fun _ : Unit => bodyN2 p lbl lsize i cx fp ra c0 (lab Fl) t s lits cs bufs) (fun e : Empty => e.elim) := by
  refine ⟨by simp [jmpDirs, directives, jmp, ins], okBlk_jmp Fl, fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩⟩
  · show _ = (arun _ (jmpDirs Fl) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩).pc
    rw [arun_jmp]; rfl
  · show SO.le (oF cx) (arun _ (jmpDirs Fl) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩).so = true
    rw [arun_jmp]; exact so_le_refl _ rfl
  · show (bodyN2 p lbl lsize i cx fp ra c0 _ t s lits cs bufs).J
      (arun _ (jmpDirs Fl) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩).σ c
    rw [arun_jmp]; exact hJ

/-- **A one-word `ret a`'s edge** at `bodyN2`: through the load into `x0` and
the epilogue to `retN2`. -/
theorem ret_edge2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa : Scc.IR.Operand} {l : List Item} (ha : cx.getOp .X0 pa = .ok l) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {a : At} {s : SEnv} {t : Ty}
    (hsa : sevalAt s a = some (t, [.one pa])) {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN2 p lbl lsize i cx fp ra c0 pc (.ret a) s lits cs bufs)
      (directives (l ++ cx.leave ++ [ret])) (fun _ : Unit => retN2 p lbl fp ra c0) (fun e : Empty => e.elim) := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  have hds := directives_leave hf h1 l
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (l ++ cx.leave ++ [ret])) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [hds, okBlk_getOp hf h1 h16 ha]
    have := okBlk_epi (F := Int64.ofInt cx.frame) (by rw [hF64]; omega) (by rw [hF64]; omega)
    rwa [hF64] at this
  refine ⟨by rw [hds]; simp [epi], hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  obtain ⟨c1, hr, hj, -, -, -, -⟩ := hJ
  obtain ⟨t', ws, he, -, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm _ _) hsa
  obtain ⟨v, hv, hrun⟩ := arun_getOp hf h1 ha lab pc σ
  match ws, hw with
  | [w], ⟨⟨v', hv', hrep⟩, _⟩ =>
  rw [hv] at hv'
  cases hv'
  refine ⟨c1, hr, .inl ⟨(), ?_⟩⟩
  show Hit (retN2 p lbl fp ra c0) (arun _ (directives (l ++ cx.leave ++ [ret])) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c1
  rw [hds, arun_append, hrun]
  obtain ⟨hpc, hso, hsl, -, h29, h30, hr0⟩ := arun_epi lab
    (pc + Int64.ofNat (4 * (directives l).length)) (-(cx.frame : Int)) { σ with regs := σ.regs.setXReg .X0 v }
    (Int64.ofInt cx.frame)
  have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
    rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  have h16' : (Int64.ofInt cx.frame - 16).toInt = cx.frame - 16 := by
    rw [Int64.toInt_sub, show (16 : Int64).toInt = 16 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc h30
  rw [h16', show -(cx.frame : Int) + (cx.frame - 16) = -16 by omega] at h29
  rw [hF64, show -(cx.frame : Int) + cx.frame = 0 by omega] at hso
  obtain ⟨hfp, hra⟩ := hfj
  refine ⟨?_, ?_, ⟨a, t', [w], hj.1, hj.2.1, he, by simp only [List.length_singleton]; decide,
    fun j hj' _ => ?_, ?_, ?_⟩, hc0.trans hr⟩
  · rw [hpc]; simp [retN2, hra]
  · rw [hso]; rfl
  · match j, hj' with
    | 0, _ =>
      have := hr0 .X0 (by decide) (by decide)
      simp only [Reg64s.getXReg_X0] at this
      rw [show argRegs[0] = .X0 from rfl, Reg64s.getXReg_X0, this]; simpa using hrep
  · rw [h29]; exact hfp
  · rw [h30]; exact hra

/-! ## A `ret` of any number of words -/

/-- **A `ret`'s loads run** (`retLoads`): each target register gets its
operand's value (`opdVal` at `rsOf`, the slots unchanged) when the targets are
distinct; the other registers are unchanged. -/
theorem arun_retLoads {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (lab : Label → Int64) :
    ∀ (ps : List (Scc.IR.Operand × XReg)) {ls : List Item}, retLoads cx ps = .ok ls → ∀ (pc : Int64) (σ : AS),
      ∃ R : Reg64s,
        arun lab (directives ls) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩ =
          ⟨pc + Int64.ofNat (4 * (directives ls).length), ⟨-(cx.frame : Int), []⟩, { σ with regs := R }⟩ ∧
        (∀ r, r ∉ ps.map Prod.snd → R.getXReg r = σ.regs.getXReg r) ∧
        ((ps.map Prod.snd).Nodup → ∀ q ∈ ps, ∃ v : BitVec 64, opdVal (rsOf cx) σ.slot q.1 = some v.toNat ∧
          R.getXReg q.2 = .ofBitVec v)
  | [], ls, h, pc, σ => by
    simp only [retLoads, Except.ok.injEq] at h
    subst h
    refine ⟨σ.regs, ?_, fun _ _ => rfl, fun _ q hq => by cases hq⟩
    simp [directives, arun]
  | (o, r) :: ps, ls, h, pc, σ => by
    simp only [retLoads, bind, Except.bind] at h
    cases hl : cx.getOp r o with
    | error e => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h
      cases hr : retLoads cx ps with
      | error e => rw [hr] at h; cases h
      | ok ls' =>
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨v, hv, hrun⟩ := arun_getOp hf h1 hl lab pc σ
        obtain ⟨R, hR, hoth, hval⟩ := arun_retLoads hf h1 lab ps hr
          (pc + Int64.ofNat (4 * (directives l).length)) { σ with regs := σ.regs.setXReg r v }
        refine ⟨R, ?_, fun r' hr' => ?_, fun hnd q hq => ?_⟩
        · rw [directives_append, arun_append, hrun, hR]
          simp only [directives_append, List.length_append, AM.mk.injEq, and_true]
          rw [Int64.add_assoc, ← Int64.ofNat_add]
          congr 2
          omega
        · simp only [List.map_cons, List.mem_cons, not_or] at hr'
          rw [hoth r' hr'.2, Reg64s.getXReg_setXReg]
          simp [hr'.1]
        · simp only [List.map_cons, List.nodup_cons] at hnd
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨v, hv, by rw [hoth r hnd.1, Reg64s.getXReg_setXReg]; simp⟩
          · exact hval hnd.2 q hq

theorem okBlk_retLoads {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (ds : List Directive) :
    ∀ (ps : List (Scc.IR.Operand × XReg)) {ls : List Item}, retLoads cx ps = .ok ls →
      okBlk (-(cx.frame : Int)) 0 ⟨-(cx.frame : Int), []⟩ (directives ls ++ ds) =
        okBlk (-(cx.frame : Int)) 0 ⟨-(cx.frame : Int), []⟩ ds
  | [], ls, h => by
    simp only [retLoads, Except.ok.injEq] at h
    subst h
    rfl
  | (o, r) :: ps, ls, h => by
    simp only [retLoads, bind, Except.bind] at h
    cases hl : cx.getOp r o with
    | error e => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h
      cases hr : retLoads cx ps with
      | error e => rw [hr] at h; cases h
      | ok ls' =>
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [directives_append, List.append_assoc, okBlk_getOp hf h1 h16 hl, okBlk_retLoads hf h1 h16 ds ps hr]

/-- Words placed one operand each: as many words as operands. -/
theorem wordsRep_one_length {lbl : WeakMem.AllocLabel → Option Nat} {val : Scc.IR.Operand → Option Nat} :
    ∀ {ws : List TermRun.Word} {vs : List Scc.IR.Operand}, Spike.Lib.Form.WordsRep lbl val ws (vs.map .one) →
      ws.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, wordsRep_one_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Words placed one operand each: the `j`-th word at the `j`-th operand. -/
theorem wordsRep_one_get {lbl : WeakMem.AllocLabel → Option Nat} {val : Scc.IR.Operand → Option Nat} :
    ∀ {ws : List TermRun.Word} {vs : List Scc.IR.Operand}, Spike.Lib.Form.WordsRep lbl val ws (vs.map .one) →
      ∀ j (hw : j < ws.length) (hv : j < vs.length), ∃ v, val vs[j] = some v ∧ Scc.Sem.ValRep lbl ws[j].val v
  | [], [], _, j, hw, _ => absurd hw (Nat.not_lt_zero _)
  | _ :: _, _ :: _, h, 0, _, _ => h.1
  | _ :: _, _ :: _, h, j + 1, hw, hv =>
      wordsRep_one_get h.2 j (by simpa using hw) (by simpa using hv)
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

theorem map_snd_zip_sublist {α β : Type _} : ∀ (l : List α) (l' : List β), ((l.zip l').map Prod.snd).Sublist l'
  | [], _ => List.nil_sublist _
  | _ :: _, [] => List.Sublist.slnil
  | _ :: l, _ :: l' => (map_snd_zip_sublist l l').cons_cons _

theorem argRegs_nodup : argRegs.Nodup := by decide

theorem argRegs_ne {r : XReg} (h : r ∈ argRegs) : r ≠ .X29 ∧ r ≠ .X30 := by
  have : ∀ r ∈ argRegs, r ≠ .X29 ∧ r ≠ .X30 := by decide
  exact this r h

/-- **A `ret`'s edge for any number of words** at `bodyN2`: `a`'s words, each
placed at one operand, loaded into `x0`, `x1`, … (`retLoads`), then the
epilogue to `retN2`. -/
theorem ret_edgeN2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls)
    (hn : vs.length ≤ argRegs.length) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {a : At} {s : SEnv} {t : Ty}
    (hsa : sevalAt s a = some (t, vs.map .one)) {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN2 p lbl lsize i cx fp ra c0 pc (.ret a) s lits cs bufs)
      (directives (ls ++ cx.leave ++ [ret])) (fun _ : Unit => retN2 p lbl fp ra c0) (fun e : Empty => e.elim) := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  have hds := directives_leave hf h1 ls
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (ls ++ cx.leave ++ [ret])) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [hds, okBlk_retLoads hf h1 h16 _ _ hl]
    have := okBlk_epi (F := Int64.ofInt cx.frame) (by rw [hF64]; omega) (by rw [hF64]; omega)
    rwa [hF64] at this
  refine ⟨by rw [hds]; simp [epi], hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  obtain ⟨c1, hr, hj, -, -, -, -⟩ := hJ
  obtain ⟨t', ws, he, -, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm _ _) hsa
  obtain ⟨R, hrun, -, hval⟩ := arun_retLoads hf h1 lab _ hl pc σ
  have hsnd : ((vs.zip argRegs).map Prod.snd).Nodup := by
    exact argRegs_nodup.sublist (map_snd_zip_sublist _ _)
  have hwl : ws.length = vs.length := wordsRep_one_length hw
  refine ⟨c1, hr, .inl ⟨(), ?_⟩⟩
  show Hit (retN2 p lbl fp ra c0) (arun _ (directives (ls ++ cx.leave ++ [ret])) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c1
  rw [hds, arun_append, hrun]
  obtain ⟨hpc, hso, hsl, -, h29, h30, hr0⟩ := arun_epi lab
    (pc + Int64.ofNat (4 * (directives ls).length)) (-(cx.frame : Int)) { σ with regs := R }
    (Int64.ofInt cx.frame)
  have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
    rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  have h16' : (Int64.ofInt cx.frame - 16).toInt = cx.frame - 16 := by
    rw [Int64.toInt_sub, show (16 : Int64).toInt = 16 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc h30
  rw [h16', show -(cx.frame : Int) + (cx.frame - 16) = -16 by omega] at h29
  rw [hF64, show -(cx.frame : Int) + cx.frame = 0 by omega] at hso
  obtain ⟨hfp, hra⟩ := hfj
  refine ⟨?_, ?_, ⟨a, t', ws, hj.1, hj.2.1, he, by omega, fun j hj' hr' => ?_, ?_, ?_⟩, hc0.trans hr⟩
  · rw [hpc]; simp [retN2, hra]
  · rw [hso]; rfl
  · have hjv : j < vs.length := by omega
    have hmem : (vs[j], argRegs[j]) ∈ vs.zip argRegs := by
      have hz : (vs.zip argRegs)[j]'(by simp; omega) = (vs[j], argRegs[j]) := List.getElem_zip
      rw [← hz]
      exact List.getElem_mem _
    obtain ⟨v, hv, hR⟩ := hval hsnd _ hmem
    obtain ⟨v', hv', hrep⟩ := wordsRep_one_get hw j hj' hjv
    rw [hv] at hv'
    cases hv'
    have hne := argRegs_ne (List.getElem_mem hr')
    rw [hr0 _ hne.1 hne.2]
    simp only at hR
    rw [hR]; simpa using hrep
  · rw [h29]; exact hfp
  · rw [h30]; exact hra

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.add_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms add_edge2

/-- info: 'Spike.Lib.LowerA64.sub_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sub_edge2

/-- info: 'Spike.Lib.LowerA64.store_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms store_edge2

/-- info: 'Spike.Lib.LowerA64.br_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms br_edge2

/-- info: 'Spike.Lib.LowerA64.jmp_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms jmp_edge2

/-- info: 'Spike.Lib.LowerA64.ret_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ret_edge2

/-- info: 'Spike.Lib.LowerA64.arun_retLoads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arun_retLoads

/-- info: 'Spike.Lib.LowerA64.okBlk_retLoads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms okBlk_retLoads

/-- info: 'Spike.Lib.LowerA64.ret_edgeN2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ret_edgeN2

end Spike.Lib.LowerA64
