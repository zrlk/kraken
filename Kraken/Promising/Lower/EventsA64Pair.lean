/-
**The AArch64 pair rows on the fuel-free machine.** Completes
`Lower/EventsA64Inf.lean` for the 16-byte rows of
the lowering table (`isaLSE2`).

- `instrSemInf_ldp_lse2`, `instrSemInf_stp_lse2`: a 16-aligned `ldp`/`stp`
  on a declared 16-byte location (`pairIsOneLoc`; `exec_ldp_lse2`/
  `exec_stp_lse2`) whose declarations agree on `⟨a, 16⟩` is **one** 16-byte
  read/write: FEAT_LSE2's single-copy-atomic pair.
- `CASP`: `caspTree` (herd's `casp`, not single-copy atomic as a pair) is two
  `rmw` events, one per 8-byte half, in either order, both inside the one
  instruction step. `RmwStep` is one RMW event in closed form (the rule
  `run_rmw_iff` uses, for any continuation: `run_rmw_cont_iff`);
  `CaspRun` is the two events in one of the two orders; `run_caspTree_iff`
  characterises every run of the whole tree, both orders, by outcome `succ`
  (chosen up front; a run whose reads disagree with it is dead), and
  `instrSemInf_casp` is the machine step.
- `instrSemInf_casp16`: a `CASP` of `X` registers on a 16-aligned declared
  16-byte location is **one** 16-byte RMW event (`exec_casp16`; Arm ARM
  B2.2.1), as `isaLSE2` performs it.
-/
import Kraken.Promising.Lower.EventsA64Inf

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-! ## LSE2 `LDP`/`STP`: one 16-byte event -/

section Pair16

variable (A : Arch) (tid : Nat) {c c' : Config isaLSE2} {t : Thread isaLSE2}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **16-aligned `ldp Xt1, Xt2, [Xn, #i]` on a declared 16-byte location**:
one plain 16-byte read of `⟨a, 16⟩`; `Xt1` gets the low half. -/
theorem instrSemInf_ldp_lse2 {dst1 dst2 : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .LDP dst1 dst2 ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 (((stOf t).st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (h16 : a % 16#64 = 0#64) (hone : pairIsOneLoc (stOf t).decls a .W64 = true)
    (hdm1 : Mem.loadInt (stOf t).st.1.dmem a 8 = none)
    (hdm2 : Mem.loadInt (stOf t).st.1.dmem (a + 8#64) 8 = none)
    (hag : (stOf t).decls.AgreesAt a 16) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) .plain false ⟨a, 16⟩ ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := ((stOf t).st.1.regs.setRegOrZr dst1 (v.setWidth 64)).setRegOrZr dst2 ((v >>> 64).setWidth 64) }) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (by rw [exec_ldp_lse2 hc ha h16 hone hdm1 hdm2, access_agrees hag])

/-- **16-aligned `stp Xt1, Xt2, [Xn, #i]` on a declared 16-byte location**:
one plain 16-byte write of `Xt2 : Xt1` to `⟨a, 16⟩`. -/
theorem instrSemInf_stp_lse2 {src1 src2 : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .STP src1 src2 ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 (((stOf t).st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (h16 : a % 16#64 = 0#64) (hone : pairIsOneLoc (stOf t).decls a .W64 = true)
    (hdm1 : Mem.loadInt (stOf t).st.1.dmem a 8 = none)
    (hdm2 : Mem.loadInt (stOf t).st.1.dmem (a + 8#64) 8 = none)
    (hag : (stOf t).decls.AgreesAt a 16) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .plain false ⟨a, 16⟩
        ((((stOf t).st.1.regs.getRegOrZr src2).setWidth 128 <<< 64) |||
          ((stOf t).st.1.regs.getRegOrZr src1).setWidth 128) none ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (by rw [exec_stp_lse2 hc ha h16 hone hdm1 hdm2, access_agrees hag])

end Pair16

/-! ## `CASP`: two RMW events in one step -/

section Casp

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **One RMW event in closed form**, from context `c` to `cf`, reading
`old`: the atomic read, then no write (`op old = none`) or the paired write
(as in `run_rmw_iff`). -/
def RmwStep (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) (op : Val → Option Val) (old : Val)
    (cf : Ctx) : Prop :=
  ∃ tr c1, (tr, old, c1) ∈ readSuccs A iv (rmwFenceOpt A c)
      (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet ∧
    ((op old = none ∧ cf = rmwFenceOpt A c1) ∨
     (∃ new c2, op old = some new ∧
        c2 ∈ writeSuccs A tid iv c1 (A.rmwKind k).storeKind true l new (some tr) (c1.loadViews.getLastD 0) ∧
        cf = rmwFenceOpt A (rmwBump (A.rmwKind k) noRet l { c2 with rmwWrote := true })))

/-- **An RMW followed by any tree**: one `RmwStep`, then a run of the
continuation at the value read. -/
theorem run_rmw_cont_iff {σ : Type} {c : Ctx} {k : RmwKind} {noRet : Bool} {l : Loc}
    {op : Val → Option Val} {ret : Val → EvTree σ} {x : Except String (σ × Ctx)} :
    x ∈ runTree A tid iv c (.rmw k noRet l op ret) ↔
      ∃ old cf, RmwStep A tid iv c k noRet l op old cf ∧ x ∈ runTree A tid iv cf (ret old) := by
  simp only [runTree, List.mem_flatMap]
  constructor
  · rintro ⟨⟨tr, old, c1⟩, hx, h⟩
    dsimp only at h
    cases hop : op old with
    | none =>
      simp only [hop] at h
      exact ⟨old, _, ⟨tr, c1, hx, .inl ⟨hop, rfl⟩⟩, h⟩
    | some new =>
      simp only [hop, List.mem_flatMap] at h
      obtain ⟨c2, h2, h⟩ := h
      exact ⟨old, _, ⟨tr, c1, hx, .inr ⟨new, c2, hop, h2, rfl⟩⟩, h⟩
  · rintro ⟨old, cf, ⟨tr, c1, hx, h⟩, hr⟩
    refine ⟨(tr, old, c1), hx, ?_⟩
    dsimp only
    rcases h with ⟨hop, rfl⟩ | ⟨new, c2, hop, h2, rfl⟩
    · simp only [hop]; exact hr
    · simp only [hop, List.mem_flatMap]
      exact ⟨c2, h2, hr⟩

/-- The operation of one `CASP` half on outcome `succ`: on success, write
`new` iff the half matches `cmp`; on failure, never write. -/
def caspHalfOp (succ : Bool) (cmp new : BitVec 64) (old : Val) : Option Val :=
  ((if succ then (fun o : BitVec 64 => if o == cmp then some new else none) else fun _ => none)
    (old.setWidth 64)).map (·.setWidth 128)

/-- **The two events of a `CASP` on outcome `succ`**, from `c` to `cf`,
reading `v1` (low half, at `a`) and `v2` (high half, at `a + 8`): low half
first, or high half first. -/
def CaspRun (c : Ctx) (k : RmwKind) (a : BitVec 64) (cmp1 cmp2 new1 new2 : BitVec 64) (succ : Bool)
    (v1 v2 : Val) (cf : Ctx) : Prop :=
  (∃ c1, RmwStep A tid iv c k false ⟨a, 8⟩ (caspHalfOp succ cmp1 new1) v1 c1 ∧
    RmwStep A tid iv c1 k false ⟨a + 8#64, 8⟩ (caspHalfOp succ cmp2 new2) v2 cf) ∨
  (∃ c1, RmwStep A tid iv c k false ⟨a + 8#64, 8⟩ (caspHalfOp succ cmp2 new2) v2 c1 ∧
    RmwStep A tid iv c1 k false ⟨a, 8⟩ (caspHalfOp succ cmp1 new1) v1 cf)

/-- **Every run of a `CASP` tree, both orders** (both halves' declarations
agreeing): an outcome `succ`, two `RmwStep`s in one of the two orders
(`CaspRun`), reads that agree with `succ` (both halves match iff `succ`), and
the continuation at the halves read. -/
theorem run_caspTree_iff {σ : Type} {ds : Decls} {k : RmwKind} {a : BitVec 64} {cmp1 cmp2 new1 new2 : BitVec 64}
    {f : BitVec 64 → BitVec 64 → σ} {c c' : Ctx} {st : σ}
    (hag1 : ds.AgreesAt a 8) (hag2 : ds.AgreesAt (a + 8#64) 8) :
    .ok (st, c') ∈ runTree A tid iv c
        (caspTree ds k a (w := .W64) cmp1 cmp2 new1 new2 fun o1 o2 => .done (f o1 o2)) ↔
      ∃ (succ : Bool) (v1 v2 : Val), CaspRun A tid iv c k a cmp1 cmp2 new1 new2 succ v1 v2 c' ∧
        (v1.setWidth 64 == cmp1 && v2.setWidth 64 == cmp2) = succ ∧ st = f (v1.setWidth 64) (v2.setWidth 64) := by
  have hb : (MemWidth.W64.bytesv : BitVec 64) = 8#64 := rfl
  unfold caspTree
  simp only [run_choose_iff, hb, access_agrees hag1, access_agrees hag2, MemWidth.bytes]
  constructor
  · rintro ⟨succ, rev, h⟩
    refine ⟨succ.val == 1, ?_⟩
    revert h
    match rev with
    | ⟨0, _⟩ =>
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [run_rmw_cont_iff]
      rintro ⟨v1, c1, h1, h⟩
      rw [run_rmw_cont_iff] at h
      obtain ⟨v2, cf, h2, h⟩ := h
      split at h
      case isFalse => simp [runTree] at h
      rename_i hg
      rw [run_done_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨v1, v2, .inl ⟨c1, ?_, ?_⟩, by simpa using hg, rfl⟩
      · revert h1; cases succ.val == 1 <;> exact id
      · revert h2; cases succ.val == 1 <;> exact id
    | ⟨1, _⟩ =>
      simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
      rw [run_rmw_cont_iff]
      rintro ⟨v2, c1, h2, h⟩
      rw [run_rmw_cont_iff] at h
      obtain ⟨v1, cf, h1, h⟩ := h
      split at h
      case isFalse => simp [runTree] at h
      rename_i hg
      rw [run_done_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨v1, v2, .inr ⟨c1, ?_, ?_⟩, by simpa using hg, rfl⟩
      · revert h2; cases succ.val == 1 <;> exact id
      · revert h1; cases succ.val == 1 <;> exact id
    | ⟨_ + 2, hr⟩ => exact absurd hr (by omega)
  · rintro ⟨succ, v1, v2, hrun, hg, rfl⟩
    refine ⟨if succ then 1 else 0, ?_⟩
    have hs : ((if succ then (1 : Fin 2) else 0).val == 1) = succ := by cases succ <;> rfl
    rcases hrun with ⟨c1, h1, h2⟩ | ⟨c1, h2, h1⟩
    · refine ⟨0, ?_⟩
      simp only [Fin.isValue, Fin.val_zero, beq_self_eq_true, ↓reduceIte]
      rw [run_rmw_cont_iff]
      refine ⟨v1, c1, by rw [hs]; exact h1, ?_⟩
      rw [run_rmw_cont_iff]
      refine ⟨v2, c', by rw [hs]; exact h2, ?_⟩
      simp only [hs]
      split
      · rw [run_done_iff]; exact ⟨rfl, rfl⟩
      · rename_i hn; simp [hg, MemWidth.bits] at hn
    · refine ⟨1, ?_⟩
      simp only [Fin.isValue, Fin.val_one, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
      rw [run_rmw_cont_iff]
      refine ⟨v2, c1, by rw [hs]; exact h2, ?_⟩
      rw [run_rmw_cont_iff]
      refine ⟨v1, c', by rw [hs]; exact h1, ?_⟩
      simp only [hs]
      split
      · rw [run_done_iff]; exact ⟨rfl, rfl⟩
      · rename_i hn; simp [hg, MemWidth.bits] at hn

end Casp

/-- Declarations that agree on an 8-byte access at `a` have no 16-byte
location at `a`. -/
theorem caspIsOneLoc_false_of_agreesAt {ds : Decls} {a : BitVec 64} (h : ds.AgreesAt a 8) :
    caspIsOneLoc ds a = false := by
  unfold Decls.AgreesAt Decls.resolve at h
  unfold caspIsOneLoc
  cases hf : ds.locs.find? (·.addr == a) with
  | none => rfl
  | some l =>
    rw [hf] at h
    by_cases hb : l.bytes = 16
    · simp [hb] at h
    · simp [hb]

section CaspMachine

variable (A : Arch) (tid : Nat) {c c' : Config isaLSE2} {t : Thread isaLSE2}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **`casp Xs1, Xs2, Xt1, Xt2, [Xn]`** (any kind `k`), both halves unmapped
and their declarations agreeing: one instruction step carrying **two** RMW
events, one per half, in either order (`CaspRun`), on an outcome `succ` the
reads agree with; then `finishInstr` with `Xs1`/`Xs2` := the halves read. -/
theorem instrSemInf_casp {rs1 rs2 rt1 rt2 : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .CASP k rs1 rs2 rt1 rt2 (.low (.reg n) .W64)⟩) sz)
    (hdm1 : Mem.loadInt (stOf t).st.1.dmem ((stOf t).st.1.regs.getXReg n).toBitVec 8 = none)
    (hdm2 : Mem.loadInt (stOf t).st.1.dmem (((stOf t).st.1.regs.getXReg n).toBitVec + 8#64) 8 = none)
    (hag1 : (stOf t).decls.AgreesAt ((stOf t).st.1.regs.getXReg n).toBitVec 8)
    (hag2 : (stOf t).decls.AgreesAt (((stOf t).st.1.regs.getXReg n).toBitVec + 8#64) 8) :
    InstrSemInf A tid c c' ↔ ∃ (succ : Bool) (v1 v2 : Val), ∃ cf th,
      CaspRun A tid (ivOf t) (ctx0 tid t c.mem) k ((stOf t).st.1.regs.getXReg n).toBitVec
        ((stOf t).st.1.regs.getRegOrZr rs1) ((stOf t).st.1.regs.getRegOrZr rs2)
        ((stOf t).st.1.regs.getRegOrZr rt1) ((stOf t).st.1.regs.getRegOrZr rt2) succ v1 v2 cf ∧
      (v1.setWidth 64 == (stOf t).st.1.regs.getRegOrZr rs1 &&
        v2.setWidth 64 == (stOf t).st.1.regs.getRegOrZr rs2) = succ ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with
          regs := ((stOf t).st.1.regs.setRegOrZr rs1 (v1.setWidth 64)).setRegOrZr rs2 (v2.setWidth 64) }) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem := by
  rw [instrSemInf_iff_of_exec A tid ht (exec_casp hc hdm1 hdm2 (caspIsOneLoc_false_of_agreesAt hag1))]
  constructor
  · rintro ⟨th, mem', ⟨st, cf, hr, hth, rfl⟩, hcert, rfl⟩
    obtain ⟨succ, v1, v2, hrun, hg, rfl⟩ := (run_caspTree_iff A tid _ hag1 hag2).mp hr
    exact ⟨succ, v1, v2, cf, th, hrun, hg, hth, hcert, rfl⟩
  · rintro ⟨succ, v1, v2, cf, th, hrun, hg, hth, hcert, rfl⟩
    exact ⟨th, cf.mem, ⟨_, cf, (run_caspTree_iff A tid _ hag1 hag2).mpr ⟨succ, v1, v2, hrun, hg, rfl⟩,
      hth, rfl⟩, hcert, rfl⟩

/-- **`casp Xs1, Xs2, Xt1, Xt2, [Xn]`** (any kind `k`) on a 16-aligned declared
16-byte location `a`, both halves unmapped and the declarations agreeing on
`⟨a, 16⟩`: one instruction step carrying **one** 16-byte RMW event
(`exec_casp16`), single-copy atomic; `Xs1`/`Xs2` := the low/high half read. -/
theorem instrSemInf_casp16 {rs1 rs2 rt1 rt2 : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .CASP k rs1 rs2 rt1 rt2 (.low (.reg n) .W64)⟩) sz)
    (hdm1 : Mem.loadInt (stOf t).st.1.dmem ((stOf t).st.1.regs.getXReg n).toBitVec 8 = none)
    (hdm2 : Mem.loadInt (stOf t).st.1.dmem (((stOf t).st.1.regs.getXReg n).toBitVec + 8#64) 8 = none)
    (h16 : ((stOf t).st.1.regs.getXReg n).toBitVec % 16#64 = 0#64)
    (hone : caspIsOneLoc (stOf t).decls ((stOf t).st.1.regs.getXReg n).toBitVec = true)
    (hag : (stOf t).decls.AgreesAt ((stOf t).st.1.regs.getXReg n).toBitVec 16) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem)) (A.rmwKind k).loadKind false
          ⟨((stOf t).st.1.regs.getXReg n).toBitVec, 16⟩ false ∧
      ((¬(old.setWidth 64 = (stOf t).st.1.regs.getRegOrZr rs1 ∧
            (old >>> 64).setWidth 64 = (stOf t).st.1.regs.getRegOrZr rs2) ∧ cf = rmwFenceOpt A c1) ∨
       (∃ c2, old.setWidth 64 = (stOf t).st.1.regs.getRegOrZr rs1 ∧
            (old >>> 64).setWidth 64 = (stOf t).st.1.regs.getRegOrZr rs2 ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind k).storeKind true
            ⟨((stOf t).st.1.regs.getXReg n).toBitVec, 16⟩
            (((stOf t).st.1.regs.getRegOrZr rt2).setWidth 128 <<< 64 ||| ((stOf t).st.1.regs.getRegOrZr rt1).setWidth 128)
            (some tr) (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind k) false ⟨((stOf t).st.1.regs.getXReg n).toBitVec, 16⟩
            { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with
          regs := ((stOf t).st.1.regs.setRegOrZr rs1 (old.setWidth 64)).setRegOrZr rs2 ((old >>> 64).setWidth 64) })
        cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem := by
  rw [instrSemInf_rmw_at A tid ht (by rw [exec_casp16 hc hdm1 hdm2 h16 hone, access_agrees hag])]
  simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨tr, old, c1, cf, th, hr, (⟨hn, rfl⟩ | ⟨new, c2, hs, hw, rfl⟩), hth, hcert, rfl⟩
    · refine ⟨tr, old, c1, _, th, hr, .inl ⟨fun h => ?_, rfl⟩, hth, hcert, rfl⟩
      simp [h] at hn
    · split at hs
      · rename_i hm; cases hs; exact ⟨tr, old, c1, _, th, hr, .inr ⟨c2, hm.1, hm.2, hw, rfl⟩, hth, hcert, rfl⟩
      · cases hs
  · rintro ⟨tr, old, c1, cf, th, hr, (⟨hn, rfl⟩ | ⟨c2, h1, h2, hw, rfl⟩), hth, hcert, rfl⟩
    · exact ⟨tr, old, c1, _, th, hr, .inl ⟨by simp [hn], rfl⟩, hth, hcert, rfl⟩
    · exact ⟨tr, old, c1, _, th, hr, .inr ⟨_, c2, by simp [h1, h2], hw, rfl⟩, hth, hcert, rfl⟩

end CaspMachine

end Kraken.Promising.Lower.A64
