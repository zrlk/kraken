/-
**Per-construct edges of an `Accepted2` body** (x86-64) at the node
invariant with buffers and slices (`bodyN2`, `pendN2`, `abortN2`, `retN2`,
`Node2.lean`); the machine halves are `Node.lean`'s and `Node1.lean`'s
(`add_block`, `sub_block`, `br_block`, `arun_jmp`, the store), the source
halves `NJB`'s (`Spike/Lib/Src/NJLB.lean`, `NJLB2.lean`).

- `add_edge2`: the checked `+` lands at the pending store (`pendN2`, the
  walk's next layouts) or, on carry, at the overflow abort (`abortN2`,
  `NJB.add_ovf_term`);
- `sub_edge2`, `store_edge2`, `br_edge2`, `jmp_edge2`: as `Node.lean`'s and
  `Node1.lean`'s at `bodyN2`/`pendN2`;
- `ret_edgeN2`: a `ret` of up to six words (`retDirs` of `getOps` into
  `retRegs`) lands at `retN2`, each word in its result register;
- the code-free moves `atom_move2`, `nameI_move2`, `pair_move2`,
  `pack_move2`, `asLanes_move2`, `asLanesV_move2`, `split_move2`,
  `unpack_move2`: `bodyN2`'s invariant past the form, at the walk's next
  layouts, known values and buffers.

The operands' leaf facts (`litMask … = [true]`) are premises here; at a
lowering environment (`ofEnv2`) `NJB.litMask_one` gives them.
-/
import Spike.Lib.LowerX64.Node2
import Spike.Lib.LowerX64.Node1
import Spike.Lib.LowerX64.BlocksC1
import Spike.Lib.Src.NJLB2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Scc.Lower (LitV litAt csAfter bufsAfter unbuf pairOk)

set_option linter.unusedSimpArgs false

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {c0 : Ctl}
  {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop}
  {lits : List (String × LitV)} {cs bufs : List (String × Nat)}

/-! ## Edges -/

/-- **The checked `+`'s edge at `bodyN2`**. -/
theorem add_edge2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ addChecked (ovfL fr))).length) (lab : String → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hla : InLits lits a) (hlb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (himm : ImmIn i s (.let_ x (.add a b) e))
    (hT : T (.let_ x (.add a b) e))
    (htot' : ∀ y ∈ Scc.Sem.exprFv e, (lookupS ((x, .int, [.one (.reg d)]) :: s) y).isSome)
    (hlb' : LocBaseRegAt ((x, .int, [.one (.reg d)]) :: s) e) (himm' : ImmIn i ((x, .int, [.one (.reg d)]) :: s) e) :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN2 p lbl lsize i fr fp ra c0 pc (.let_ x (.add a b) e) s lits cs bufs)
      ((dirs (la ++ lb ++ addChecked (ovfL fr))).zip zs)
      (fun _ : Unit => pendN2 p lbl lsize i fr fp ra c0 (pc + Int64.ofNat zs.sum)
        e ((x, .int, [.one (.reg d)]) :: s) ((x, .leaf none) :: lits) (csAfter x cs (.add a b))
        (bufsAfter x cs bufs (.add a b)) off)
      (fun _ : Unit => abortN2 i T p lbl fr lab fp ra c0) := by
  obtain ⟨hne, hok, -⟩ := add_edge (p := p) (lbl := lbl) (c0 := c0) (fp := fp) (ra := ra) (x := x) (e := e) (pc := pc)
    hf h1 ha hb hd hz lab hsa hsb hfr htot himm hT
  refine ⟨hne, hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, h9, hsl⟩ :=
    add_block hf h1 ha hb (ovfL fr) lab pc σ hz
  have hfr' : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rsOf fr r = some k' → k' ≠ off := by
    intro q hq pl hpl o ho r k' hor hr' hk
    subst hk
    exact hfr q hq pl hpl o ho r hor (rsOf_inj hf hr' hd)
  by_cases hlt : va.toNat + vb.toNat < 2 ^ 64
  · -- the source past the `+`: the node's invariant at the control itself
    obtain ⟨c2, hr2, hj2, hn2, hb2, hm2, hS2⟩ := hJ.add_ok hsa hsb hla hlb hma hmb hva hvb hlt hd hfr'
      (v := va + vb) (by rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hlt)
    refine ⟨c2, hr2, .inl ⟨(), ?_, ?_, ?_, ?_, hc0.trans hr2, ?_⟩⟩
    · show pc + _ = _
      rw [hpc]; simp [hlt]
    · show SO.le (oB fr) _ = true
      rw [hso]; exact so_le_oB fr
    · show ∃ L sm B, NJB p lbl (rsOf fr) _ _ _ L sm lsize B e _ (upd _ off _) c2
      rw [hsl, h9]
      exact ⟨L, sm, B, NJB.of_nodeJE hj2 hn2 hb2 hm2 hS2⟩
    · show FrJ fp ra _
      rw [hsl]; exact hfj
    · show SlotRepAt i lbl (rsOf fr) (upd _ off _) c2
      rw [hsl, h9]
      exact SlotRepAt.of_nodeJE hj2 htot' hlb' himm'
  · obtain ⟨c1, hr, hab, hS, ht⟩ := hJ.add_ovf_term hsa hsb hla hlb hma hmb hva hvb (by omega) htot
    refine ⟨c1, hr, .inr ⟨(), ?_, ?_, ?_, hc0.trans hr⟩⟩
    · show _ = _
      rw [hpc]; simp [hlt]; rfl
    · show SO.le (oB fr) _ = true
      rw [hso]; exact so_le_oB fr
    · show AbJ2 i T lbl fr fp ra _ c1
      rw [AbJ2, hsl]; exact ⟨⟨_, lits, hab, hS, ht ▸ himm.retype c1.env,
        ht ▸ (LocBaseRegAt.let_add hsa hsb hlb').retype c1.env, ht ▸ hT⟩, hfj⟩

/-- **The saturating `-`'s edge at `bodyN2`**. -/
theorem sub_edge2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ subSatItems)).length) (lab : String → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hla : InLits lits a) (hlb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d) {i : Expr → String → Nat → Option Nat}
    (htot' : ∀ y ∈ Scc.Sem.exprFv e, (lookupS ((x, .int, [.one (.reg d)]) :: s) y).isSome)
    (hlb' : LocBaseRegAt ((x, .int, [.one (.reg d)]) :: s) e) (himm' : ImmIn i ((x, .int, [.one (.reg d)]) :: s) e) :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN2 p lbl lsize i fr fp ra c0 pc (.let_ x (.sub a b) e) s lits cs bufs)
      ((dirs (la ++ lb ++ subSatItems)).zip zs)
      (fun _ : Unit => pendN2 p lbl lsize i fr fp ra c0 (pc + Int64.ofNat zs.sum)
        e ((x, .int, [.one (.reg d)]) :: s) ((x, .leaf none) :: lits) (csAfter x cs (.sub a b))
        (bufsAfter x cs bufs (.sub a b)) off) (fun e : Empty => e.elim) := by
  obtain ⟨hne, hok, -⟩ := sub_edge (p := p) (lbl := lbl) (c0 := c0) (fp := fp) (ra := ra) (x := x) (e := e) (pc := pc)
    hf h1 ha hb hd hz lab hsa hsb hfr
  refine ⟨hne, hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, h9, hsl⟩ :=
    sub_block hf h1 ha hb lab pc σ hz
  have hfr' : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rsOf fr r = some k' → k' ≠ off := by
    intro q hq pl hpl o ho r k' hor hr' hk
    subst hk
    exact hfr q hq pl hpl o ho r hor (rsOf_inj hf hr' hd)
  -- the source past the `-`: the node's invariant at the control itself
  obtain ⟨c2, hr2, hj2, hn2, hb2, hm2, hS2⟩ := hJ.sub_ok hsa hsb hla hlb hma hmb hva hvb hd hfr' h9
  refine ⟨c2, hr2, .inl ⟨(), ?_, ?_, ?_, ?_, hc0.trans hr2, ?_⟩⟩
  · show pc + _ = _
    rw [hpc]
  · show SO.le (oB fr) _ = true
    rw [hso]; exact so_le_oB fr
  · show ∃ L sm B, NJB p lbl (rsOf fr) _ _ _ L sm lsize B e _ (upd _ off _) c2
    rw [hsl]
    exact ⟨L, sm, B, NJB.of_nodeJE hj2 hn2 hb2 hm2 hS2⟩
  · show FrJ fp ra _
    rw [hsl]; exact hfj
  · show SlotRepAt i lbl (rsOf fr) (upd _ off _) c2
    rw [hsl]
    exact SlotRepAt.of_nodeJE hj2 htot' hlb' himm'

/-- **The store's edge** from `pendN2` to `bodyN2`. -/
theorem store_edge2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {d : Scc.IR.Reg}
    {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {z : Nat} (lab : String → Int64) {fp ra : BitVec 64}
    {t : Expr} {s : SEnv} {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(fr.size : Int)) 16 (pendN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs off) [(stDir off, z)]
      (fun _ : Unit => bodyN2 p lbl lsize i fr fp ra c0 (pc + Int64.ofNat z) t s lits cs bufs)
      (fun e : Empty => e.elim) := by
  obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hc : classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  obtain ⟨hne, hok, -⟩ := store_edge (p := p) (lbl := lbl) (c0 := c0) (fp := fp) (ra := ra) (t := t) (s := s)
    (z := z) (pc := pc) hf h1 hd lab
  have hrun : ∀ σ : AS, arun lab [(stDir off, z)] ⟨pc, oB fr, σ⟩ =
      ⟨pc + Int64.ofNat z, oB fr, { σ with slot := upd σ.slot off (σ.regs.get64 .rax) }⟩ := by
    intro σ
    simp [arun, dstep, hc, AI.tgt, AI.so, AI.step, oB, SO.get, lk, ho]
  refine ⟨hne, hok, fun σ c ⟨hJ, hfj, hc0, hsr⟩ =>
    ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_, ?_, hc0, ?_⟩⟩⟩
  all_goals simp only [pendN2, bodyN2, hrun]
  · exact so_le_oB fr
  · exact hJ
  · obtain ⟨h0', h8'⟩ := hfj
    have hk1 : (0 : Int) ≠ off := by omega
    have hk2 : (8 : Int) ≠ off := by omega
    show upd σ.slot _ _ 0 = fp ∧ upd σ.slot _ _ 8 = ra
    simp only [upd_apply, Ne.symm hk1, Ne.symm hk2, hk1, hk2, ↓reduceIte, h0', h8', and_self]
  · exact hsr

/-- **An `if`'s compare-and-branch's edge at `bodyN2`**: the internal nodes
indexed by the comparison's outcome, the walk's state unchanged. -/
theorem br_edge2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    (T : String) {pc : Int64} {zs : List Nat} (hz : zs.length = (brDirs la lb T).length) (lab : String → Int64)
    {fp ra : BitVec 64} {a b : At} {yes no : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hla : InLits lits a) (hlb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN2 p lbl lsize i fr fp ra c0 pc (.ifeq a b yes no) s lits cs bufs)
      ((brDirs la lb T).zip zs)
      (fun bb : Bool =>
        if bb then bodyN2 p lbl lsize i fr fp ra c0 (lab T) yes s lits cs bufs
        else bodyN2 p lbl lsize i fr fp ra c0 (pc + Int64.ofNat zs.sum) no s lits cs bufs)
      (fun e : Empty => e.elim) := by
  obtain ⟨hne, hok, -⟩ := br_edge (p := p) (lbl := lbl) (c0 := c0) (fp := fp) (ra := ra) (yes := yes)
    (no := no) (pc := pc)
    hf h1 ha hb T hz lab hsa hsb
  refine ⟨hne, hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, hsr⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, hsl⟩ :=
    br_block hf h1 ha hb T lab pc σ hz
  have hJ' := hJ.ifeq hsa hsb hla hlb hma hmb hva hvb
  refine ⟨c, .refl c, .inl ⟨decide (va = vb), ?_⟩⟩
  by_cases h : va = vb
  · have : va.toNat = vb.toNat := by rw [h]
    simp only [h, decide_true, ite_true] at hpc ⊢
    refine ⟨hpc.symm, ?_, ?_⟩
    · rw [hso]; exact so_le_oB fr
    · show (∃ L sm B, NJB _ _ _ _ _ _ L sm lsize B _ _ _ c) ∧ _ ∧ _ ∧ _
      rw [hsl]
      exact ⟨⟨L, sm, B, by simpa [this] using hJ'⟩, hfj, hc0, hsr⟩
  · have : va.toNat ≠ vb.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [h, decide_false, Bool.false_eq_true, ite_false] at hpc ⊢
    refine ⟨hpc.symm, ?_, ?_⟩
    · rw [hso]; exact so_le_oB fr
    · show (∃ L sm B, NJB _ _ _ _ _ _ L sm lsize B _ _ _ c) ∧ _ ∧ _ ∧ _
      rw [hsl]
      exact ⟨⟨L, sm, B, by simpa [this] using hJ'⟩, hfj, hc0, hsr⟩

/-- **`jmp F`'s edge at `bodyN2`**. -/
theorem jmp_edge2 {fr : Scc.Emit.X64.Frame} (Fl : String) {pc : Int64} {z : Nat} (lab : String → Int64)
    {fp ra : BitVec 64} {t : Expr} {s : SEnv} {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) ((jmpDirs Fl).zip [z])
      (fun _ : Unit => bodyN2 p lbl lsize i fr fp ra c0 (lab Fl) t s lits cs bufs) (fun e : Empty => e.elim) := by
  refine ⟨by simp [jmpDirs], okBlk_jmp Fl, fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩⟩
  · show _ = (arun _ ((jmpDirs Fl).zip [z]) ⟨pc, oB fr, σ⟩).pc
    rw [arun_jmp]; rfl
  · show SO.le (oB fr) (arun _ ((jmpDirs Fl).zip [z]) ⟨pc, oB fr, σ⟩).so = true
    rw [arun_jmp]; exact so_le_oB fr
  · show (bodyN2 p lbl lsize i fr fp ra c0 _ t s lits cs bufs).J (arun _ ((jmpDirs Fl).zip [z]) ⟨pc, oB fr, σ⟩).σ c
    rw [arun_jmp]; exact hJ

/-! ## The return of up to six words -/

/-- **An operand's load is a result word's instruction** (`RW`): a frame
cell inside `[-size, 16)` or an immediate, valued as the operand. -/
theorem getOp_rw {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {t : Reg64}
    {o : Scc.IR.Operand} {l : List Item} (ha : getOp fr t o = .ok l) :
    ∃ w : RW, dirs l = [w.dir t] ∧ w.ok (-(fr.size : Int)) 16 = true ∧
      ∀ sl, opdVal (rsOf fr) sl o = some (w.val sl).toNat := by
  rcases getOp_cases ha with ⟨r, off, rfl, hs, hl⟩ | ⟨v, rfl, hl⟩
  · obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hs
    have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
    refine ⟨.slot (Int64.ofInt off), by rw [hl]; rfl, ?_, fun sl => ?_⟩
    · simp only [RW.ok, offOk, ho, decide_eq_true_eq]; omega
    · simp [opdVal, hs, RW.val, ho]
  · exact ⟨.imm v, by rw [hl]; rfl, rfl, fun sl => by simp [opdVal, RW.val]⟩

/-- **Operands' loads into registers are result words' instructions**
(`getOps`), one per operand. -/
theorem getOps_rw {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) :
    ∀ {vs : List Scc.IR.Operand} {rs : List Reg64} {lw : List Item}, getOps fr (vs.zip rs) = .ok lw →
      vs.length ≤ rs.length →
      ∃ rws : List RW, rws.length = vs.length ∧ dirs lw = wordDirs (rs.zip rws) ∧
        (∀ w ∈ rws, w.ok (-(fr.size : Int)) 16 = true) ∧
        ∀ j (hj : j < vs.length) (hj' : j < rws.length) sl,
          opdVal (rsOf fr) sl vs[j] = some (rws[j].val sl).toNat
  | [], rs, lw, h, _ => by
    cases h
    exact ⟨[], rfl, by simp [dirs, wordDirs], by simp, fun j hj => absurd hj (by simp)⟩
  | v :: vs, r :: rs, lw, h, hn => by
    simp only [List.zip_cons_cons, getOps] at h
    obtain ⟨la, ha, h⟩ := exc_bind_ok h
    obtain ⟨lr, hr, h⟩ := exc_bind_ok h
    cases h
    obtain ⟨w, hdw, hok, hv⟩ := getOp_rw hf h1 ha
    obtain ⟨rws, hlen, hd, hoks, hvs⟩ := getOps_rw hf h1 hr (by simp at hn; omega)
    refine ⟨w :: rws, by simp [hlen], ?_, ?_, fun j hj hj' sl => ?_⟩
    · show dirs (la ++ lr) = _
      rw [dirs_append, hdw, hd]; rfl
    · intro w' hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact hok
      · exact hoks w' hw'
    · match j, hj, hj' with
      | 0, _, _ => exact hv sl
      | j + 1, hj, hj' => exact hvs j (by simpa using hj) (by simpa using hj') sl
  | _ :: _, [], _, _, hn => by simp at hn

/-- **Words at one-word placements**, by index. -/
theorem wordsRep_ones {val : Scc.IR.Operand → Option Nat} :
    ∀ {ws : List TermRun.Word} {vs : List Scc.IR.Operand}, WordsRep lbl val ws (vs.map .one) →
      ws.length = vs.length ∧
        ∀ j (h1 : j < ws.length) (h2 : j < vs.length), ∃ v, val vs[j] = some v ∧ ValRep lbl ws[j].val v
  | [], [], _ => ⟨rfl, fun j h => absurd h (by simp)⟩
  | w :: ws, v :: vs, h => by
    obtain ⟨hw, hr⟩ := h
    obtain ⟨hl, hi⟩ := wordsRep_ones hr
    refine ⟨by simp [hl], fun j h1 h2 => ?_⟩
    match j, h1, h2 with
    | 0, _, _ => exact hw
    | j + 1, h1, h2 => exact hi j (by simpa using h1) (by simpa using h2)
  | [], _ :: _, h => by simp [WordsRep] at h
  | _ :: _, [], h => by simp [WordsRep] at h

/-- **`ret a`'s edge for up to six words at `bodyN2`**: `a`'s one-word
placements `vs` loaded into the result registers (`getOps` into `retRegs`),
the epilogue, `ret`; lands at `retN2` with each word in its register. -/
theorem ret_edgeN2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {vs : List Scc.IR.Operand} {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (retDirs lw).length) (lab : String → Int64) {fp ra : BitVec 64} {a : At} {s : SEnv}
    {t : Ty} (hsa : sevalAt s a = some (t, vs.map .one)) {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN2 p lbl lsize i fr fp ra c0 pc (.ret a) s lits cs bufs)
      ((retDirs lw).zip zs) (fun _ : Unit => retN2 p lbl fp ra c0) (fun e : Empty => e.elim) := by
  have hrr : Scc.Emit.X64.retRegs = Spike.Lib.X64.retRegs := rfl
  rw [hrr] at hl hn
  obtain ⟨rws, hlen, hd, hoks, hvs⟩ := getOps_rw hf h1 hl hn
  have hblk : retDirs lw = retBlk rws := by
    rw [retDirs, dirs_append, dirs_epiItems, hd]; rfl
  rw [hblk] at hz ⊢
  have hne : (retBlk rws).zip zs ≠ [] := by
    intro h
    have h' := congrArg List.length h
    simp only [List.length_zip, List.length_nil, ← hz, Nat.min_self] at h'
    rw [h'] at hz
    simp [retBlk, epi] at hz
  refine ⟨hne, retBlk_ok (by omega) hoks hz, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  obtain ⟨c1, hr, hj, -, -, -, -⟩ := hJ
  obtain ⟨t', ws, he, -, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm _ _) hsa
  obtain ⟨hwl, hwi⟩ := wordsRep_ones hw
  obtain ⟨hfp, hra⟩ := hfj
  refine ⟨c1, hr, .inl ⟨(), retBlk_hit lab pc (-(fr.size : Int)) σ rws hz (by simp [retN2, hra]) rfl ?_⟩⟩
  intro σ' hsl _ hbp _ hreg
  refine ⟨⟨a, t', ws, hj.1, hj.2.1, he, by rw [hwl]; exact hn, fun j hj1 hj2 => ?_, ?_⟩, hc0.trans hr⟩
  · have hjv : j < vs.length := hwl ▸ hj1
    have hjr : j < rws.length := hlen ▸ hjv
    obtain ⟨v, hv, hrep⟩ := hwi j hj1 hjv
    rw [hvs j hjv hjr σ.slot] at hv
    cases hv
    have hm : (Spike.Lib.X64.retRegs[j]'(hrr ▸ hj2), rws[j]) ∈ Spike.Lib.X64.retRegs.zip rws := by
      rw [List.mem_iff_getElem]
      exact ⟨j, by simp; omega, by simp⟩
    have := hreg _ _ hm
    simp only [hrr]
    rw [this]; exact hrep
  · rw [hbp, hfp]

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.add_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms add_edge2

/-- info: 'Spike.Lib.LowerX64.sub_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sub_edge2

/-- info: 'Spike.Lib.LowerX64.store_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms store_edge2

/-- info: 'Spike.Lib.LowerX64.br_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms br_edge2

/-- info: 'Spike.Lib.LowerX64.jmp_edge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms jmp_edge2

/-- info: 'Spike.Lib.LowerX64.ret_edgeN2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ret_edgeN2

end Spike.Lib.LowerX64
