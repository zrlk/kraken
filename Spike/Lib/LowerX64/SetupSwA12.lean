/-
**The setup words A11 fixes are the lowering's** (x86-64): on an `Accepted2`
program with a setup block whose output passes `placeOKAt`, every `sw` with
the runtime's code at `setupMC sw` (`rtCodeOkS`, A11) is `setupWords2 p`,
the setup block's value words. A12 checks `scc_rt_main`'s code at the IR's
`mainThread0 (entry2 p) (setupWords2 p)`: after `.Lscc_rt_main.entry`, the
`call` of the setup block, its return label, its `setupWords2 p` result
stores, then a register load (`mainCode_dirs`). A11 holds the marshalling
block `marshal sw` (`sw` stores, then a load) at the same cells (the label
gap from `.entry` to `.x2`), so the store runs agree (`stRun_unique`).

- `IsSt`, `IsLdR`: a store of a register to memory, a move into a register.
- `mainCode_dirs`: the code of `scc_rt_main`'s block after a setup block.
- `stRun_unique`: two store runs ended by a non-store in one list agree.
- `sw_eq_setupWords2`: A11's `sw` is `setupWords2 p`.
- `valWords_of_rtCodeOkS`: the setup block's result has `sw` value words.
-/
import Spike.Lib.LowerX64.EmitOut
import Spike.Lib.LowerX64.SetupSw
import Spike.Lib.LowerX64.NumQOfPlaceOK
import Spike.Lib.LowerX64.LowerProgC2X
import Spike.Lib.LowerX64.MainCode1
import Spike.Lib.SetupWords2
import Spike.Lib.RtMainMem

namespace Spike.Lib.LowerX64

open Scc.Emit.X64

/-! ## Stores and register moves -/

/-- **A store of a register to memory**: `movq %r, a`. -/
def IsSt (d : Directive) : Prop := ∃ (a : AddrExpr) (r : Reg64), d = i64 (.mov (xm a) (or_ r))

/-- **A move into a register**: `movq src, %r`. -/
def IsLdR (d : Directive) : Prop := ∃ (r : Reg64) (src : _root_.Operand .W64), d = i64 (.mov (xr r) src)

theorem not_isSt_of_isLdR {d : Directive} (h : IsLdR d) : ¬ IsSt d := by
  rintro ⟨a, r, rfl⟩
  obtain ⟨r', src, he⟩ := h
  simp [i64, op, xr, xm] at he

/-- A slot lookup leaves the state as it is. -/
theorem slot_state {fr : Frame} {x : Scc.IR.Reg} {s s1 : S} {a : AddrExpr} (h : fr.slot x s = .ok (a, s1)) :
    s1 = s := by
  unfold Frame.slot at h
  obtain ⟨o, t, e1, e2⟩ := bind_inv_E h
  have ht : t = s := by
    unfold Frame.slotOff at e1
    cases hf : List.find? (fun y => y.fst == x) fr.slots with
    | none => rw [hf] at e1; cases e1
    | some v => obtain ⟨_, k⟩ := v; rw [hf] at e1; cases e1; rfl
  subst ht
  cases e2; rfl

/-- A load emits one move into its register. -/
theorem ld_out {fr : Frame} {a : Scc.IR.Operand} {r : Reg64} {s s' : S} {u : Unit}
    (h : ld fr a r s = .ok (u, s')) : ∃ d, IsLdR d ∧ s'.out = .d d :: s.out := by
  cases a with
  | reg x =>
    simp only [ld] at h
    obtain ⟨ad, s1, h1, h2⟩ := bind_inv_E h
    have hs1 := slot_state h1
    subst hs1
    cases h2
    exact ⟨_, ⟨r, _, rfl⟩, rfl⟩
  | imm v =>
    simp only [ld] at h
    cases h
    exact ⟨_, ⟨r, _, rfl⟩, rfl⟩

/-- A store emits one store of its register. -/
theorem st_out {fr : Frame} {r : Reg64} {x : Scc.IR.Reg} {s s' : S} {u : Unit}
    (h : st fr r x s = .ok (u, s')) : ∃ d, IsSt d ∧ s'.out = .d d :: s.out := by
  simp only [st] at h
  obtain ⟨ad, s1, h1, h2⟩ := bind_inv_E h
  have hs1 := slot_state h1
  subst hs1
  cases h2
  exact ⟨_, ⟨ad, r, rfl⟩, rfl⟩

/-- **The results' stores** of a call: one store per pair. -/
theorem stores_out (fr : Frame) :
    ∀ (l : List (Scc.IR.Reg × Reg64)) {s s' : S} {u : PUnit},
      forIn (m := E) l PUnit.unit (fun (x : Scc.IR.Reg × Reg64) (_ : PUnit) => do
        st fr x.2 x.1; pure (ForInStep.yield PUnit.unit)) s = .ok (u, s') →
      ∃ sr : List Directive, sr.length = l.length ∧ (∀ d ∈ sr, IsSt d) ∧ s'.out = (sr.map .d).reverse ++ s.out
  | [], s, s', u, h => by
    simp only [List.forIn_nil] at h
    cases h
    exact ⟨[], rfl, by simp, rfl⟩
  | x :: l, s, s', u, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, s1, h1, h2⟩ := bind_inv_E h
    obtain ⟨u1, t, e1, e2⟩ := bind_inv_E h1
    obtain ⟨d, hd, ht⟩ := st_out e1
    cases e2
    obtain ⟨sr, hl, hs, hout⟩ := stores_out fr l h2
    refine ⟨d :: sr, by simp [hl], ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hd
      · exact hs y hy
    · rw [hout, ht]; simp

/-- A guard that succeeds leaves the state as it is. -/
theorem guard_state {c : Prop} [Decidable c] {e : String} {s s' : S} {u : PUnit}
    (h : (if c then (throw e : E PUnit) else pure PUnit.unit) s = .ok (u, s')) : s' = s := by
  split at h
  · cases h
  · cases h; rfl

/-- A call without arguments moves nothing. -/
theorem callArgs_nil {fr : Frame} {what : String} {s s' : S} {u : Unit}
    (h : callArgs fr [] what s = .ok (u, s')) : s' = s := by
  unfold callArgs loadArgs at h
  simp at h
  cases h; rfl

theorem ld_pre (fr : Frame) (a : Scc.IR.Operand) (r : Reg64) : Pre (ld fr a r) := by
  unfold ld; pre_tac

/-- A loop whose body starts with a load emits that load first. -/
theorem forIn_ld_head {β : Type} {fr : Frame} (fa : β → Scc.IR.Operand) (fr' : β → Reg64) (k : β → E PUnit)
    (hk : ∀ b, Pre (k b)) (b : β) (l : List β) {s s' : S} {u : PUnit}
    (h : forIn (m := E) (b :: l) PUnit.unit (fun (x : β) (_ : PUnit) => do
      ld fr (fa x) (fr' x); k x; pure (ForInStep.yield PUnit.unit)) s = .ok (u, s')) :
    ∃ d c, IsLdR d ∧ s'.out = c ++ .d d :: s.out := by
  rw [List.forIn_cons] at h
  obtain ⟨r, s1, h1, h2⟩ := bind_inv_E h
  obtain ⟨u1, t, e1, e2⟩ := bind_inv_E h1
  obtain ⟨d, hd, ht⟩ := ld_out e1
  obtain ⟨u2, t2, e3, e4⟩ := bind_inv_E e2
  cases e4
  obtain ⟨c1, hc1⟩ := (hk b).out _ _ _ e3
  obtain ⟨c2, hc2⟩ := (Pre.forIn' _ (fun x _ => Pre.bind' (ld_pre fr (fa x) (fr' x))
    fun _ => Pre.bind' (hk x) fun _ => Pre.pure' _) l _).out _ _ _ h2
  exact ⟨d, c2 ++ c1, hd, by rw [hc2, hc1, ht]; simp⟩

/-- **A call with arguments moves into a register first**: its first item
is a load (of the first stack argument into `%rax`, else of the first
register argument). -/
theorem callArgs_head {fr : Frame} {args : List Scc.IR.Operand} (hne : args ≠ []) {what : String} {s s' : S}
    {u : Unit} (h : callArgs fr args what s = .ok (u, s')) : ∃ d c, IsLdR d ∧ s'.out = c ++ .d d :: s.out := by
  unfold callArgs at h
  split at h
  · obtain ⟨_, _, h0, -⟩ := bind_inv_E h
    cases h0
  obtain ⟨u1, s1, h1, h2⟩ := bind_inv_E h
  have hL : Pre (loadArgs fr argRegs (args.take argRegs.length) what) := by unfold loadArgs; pre_tac
  cases hd : (args.drop argRegs.length).zipIdx with
  | cons y ys =>
    rw [hd] at h1
    obtain ⟨d, c, hd, hc⟩ := forIn_ld_head (fr := fr) (fun x => x.1) (fun _ => .rax)
      (fun x => ins (i64 (.mov (xm (mem .rsp (8 * (x.2 : Int)))) (or_ .rax)))) (fun _ => Pre.item' _) y ys
      (by exact h1)
    obtain ⟨c2, hc2⟩ := hL.out _ _ _ h2
    exact ⟨d, c2 ++ c, hd, by rw [hc2, hc]; simp⟩
  | nil =>
    rw [hd] at h1
    simp only [List.forIn_nil] at h1
    cases h1
    unfold loadArgs at h2
    split at h2
    · obtain ⟨_, _, h0, -⟩ := bind_inv_E h2
      cases h0
    obtain ⟨a, rs, ha⟩ := List.exists_cons_of_ne_nil hne
    subst ha
    have hz : (List.take argRegs.length (a :: rs)).zip argRegs =
        (a, .rdi) :: (List.take 5 rs).zip [.rsi, .rdx, .rcx, .r8, .r9] := rfl
    rw [hz] at h2
    exact forIn_ld_head (β := Scc.IR.Operand × Reg64) (fr := fr) (fun x => x.1) (fun x => x.2)
      (fun _ => pure PUnit.unit) (fun _ => Pre.pure' _) (a, .rdi)
      ((List.take 5 rs).zip [.rsi, .rdx, .rcx, .r8, .r9]) (by simpa using h2)

/-- **The code of a `call`**, with the stack maps on, sharpened: at most
six results; the arguments' moves, `call g`, the safepoint label, then one
store per result. -/
theorem emitInst_call_out {fr : Frame} (hm : fr.maps = true) {sm : Option Scc.IR.StackMap.Entry}
    {ds : List Scc.IR.Reg} {g : Scc.IR.Sym} {args : List Scc.IR.Operand} {s s' : S}
    (h : emitInst fr sm (.call ds g args) s = .ok ((), s')) :
    ∃ (what : String) (s1 : S) (k : Nat) (sr : List Directive), callArgs fr args what s = .ok ((), s1) ∧
      sr.length = ds.length ∧ (∀ d ∈ sr, IsSt d) ∧
      s'.out = (sr.map .d).reverse ++ .d (.label s!".L{fr.fn}.x{k}") :: .d (i64 (.call (rel g))) :: s1.out := by
  simp only [emitInst] at h
  split at h
  · obtain ⟨_, _, h0, -⟩ := bind_inv_E h
    cases h0
  next hle =>
  obtain ⟨u1, s1, h1, h⟩ := bind_inv_E h
  obtain ⟨u2, s2, h2, h⟩ := bind_inv_E h
  have hs2 : s2 = { s1 with out := Item.d (i64 (.call (rel g))) :: s1.out } := by
    cases h2; rfl
  subst hs2
  obtain ⟨u3, s3, h3, h⟩ := bind_inv_E h
  have hs3 : ∃ k : Nat, s3.out = Item.d (.label s!".L{fr.fn}.x{k}") :: Item.d (i64 (.call (rel g))) :: s1.out := by
    unfold safepoint at h3
    simp only [hm, ite_true] at h3
    obtain ⟨l, t1, e1, h3⟩ := bind_inv_E h3
    cases e1
    obtain ⟨u, t2, e2, h3⟩ := bind_inv_E h3
    cases e2
    obtain ⟨st1, t3, e3, h3⟩ := bind_inv_E h3
    have := mapM_slotOff_state fr _ e3
    subst this
    obtain ⟨hp1, t4, e4, h3⟩ := bind_inv_E h3
    have := mapM_slotOff_state fr _ e4
    subst this
    cases h3
    exact ⟨s1.next, rfl⟩
  obtain ⟨k, hk⟩ := hs3
  obtain ⟨u4, s4, h4, h⟩ := bind_inv_E h
  cases h
  obtain ⟨sr, hl, hs, hout⟩ := stores_out fr _ h4
  refine ⟨_, s1, k, sr, h1, ?_, hs, by rw [hout, hk]⟩
  rw [hl, List.length_zip]
  simp only [gt_iff_lt, Nat.not_lt] at hle
  omega

/-- `scc_rt_main`'s instructions after a setup block of `sw` words. -/
theorem mainInsts_setup (sw : Nat) :
    Scc.Lower.Inv.mainInsts ⟨.setupTid, true⟩ sw =
      [.call (Scc.Lower.Inv.mainDs ⟨.setupTid, true⟩ sw) (Scc.Lower.Names.user "rodata") [],
       .call [Scc.Lower.Inv.regName "v" sw] (Scc.Lower.Names.user "main") (Scc.Lower.Inv.mainArgs ⟨.setupTid, true⟩ sw),
       .syscall (Scc.Lower.Inv.regName "r" (sw + 1)) .exitGroup [.reg (Scc.Lower.Inv.regName "v" sw)]] := by
  rfl

/-- **The code of `scc_rt_main`'s block after a setup block of `sw` words**
(stack maps on, a map per instruction): the setup block's `call`, its
return label, `sw` result stores, then a move into a register (the user
function's first argument). -/
theorem mainCode_dirs {fr : Frame} (hm : fr.maps = true) {sw n : Nat} {ms : List (Option Scc.IR.StackMap.Entry)}
    (hms : ms.length = 3) {code : List Item} {n' : Nat}
    (h : Scc.Cert.Code1X64.blockItems fr n ⟨"entry", Scc.Lower.Inv.mainInsts ⟨.setupTid, true⟩ sw, .unreachable⟩ ms =
      .ok (code, n')) :
    ∃ (k : Nat) (sr : List Directive) (d : Directive) (rest : List Directive),
      directives code = i64 (.call (rel (Scc.Lower.Names.user "rodata"))) :: .label s!".L{fr.fn}.x{k}" ::
        (sr ++ d :: rest) ∧ sr.length = sw ∧ (∀ x ∈ sr, IsSt x) ∧ IsLdR d := by
  unfold Scc.Cert.Code1X64.blockItems at h
  split at h
  case h_2 => cases h
  rename_i s hs
  cases h
  obtain ⟨m1, m2, m3, rfl⟩ : ∃ m1 m2 m3, ms = [m1, m2, m3] := by
    match ms, hms with
    | [m1, m2, m3], _ => exact ⟨m1, m2, m3, rfl⟩
  rw [blockCode_eq, mainInsts_setup] at hs
  simp only [StateT.run] at hs
  obtain ⟨u0, s3, h3, h4⟩ := bind_inv_E hs
  rw [instsCode_cons] at h3
  obtain ⟨u1, s1, e1, h3⟩ := bind_inv_E h3
  rw [instsCode_cons] at h3
  obtain ⟨u2, s2, e2, h3⟩ := bind_inv_E h3
  obtain ⟨c3, hc3⟩ := (instsCode_pre fr _ _).out _ _ _ h3
  obtain ⟨c4, hc4⟩ := (emitTerm_pre fr _).out _ _ _ h4
  obtain ⟨w1, t1, k, sr, hca1, hl, hst, ho1⟩ := emitInst_call_out hm e1
  have := callArgs_nil hca1
  subst this
  obtain ⟨w2, t2, k2, sr2, hca2, -, -, ho2⟩ := emitInst_call_out hm e2
  obtain ⟨d, c, hd, hc⟩ := callArgs_head (by simp [Scc.Lower.Inv.mainArgs]) hca2
  refine ⟨k, sr, d, directives ((sr2.map Item.d).reverse ++
      [Item.d (.label s!".L{fr.fn}.x{k2}"), Item.d (i64 (.call (rel (Scc.Lower.Names.user "main"))))] ++ c).reverse ++
      directives (c4 ++ c3).reverse, ?_, ?_, hst, hd⟩
  · rw [hc4, hc3, ho2, hc, ho1]
    simp [directives, List.filterMap_append, List.filterMap_map, Function.comp_def]
  · have : Scc.Lower.mainSetup ⟨.setupTid, true⟩ sw = sw := rfl
    rw [hl]; simp [Scc.Lower.Inv.mainDs, this]

/-! ## The two store runs agree -/

theorem getElem?_of_prefix {α : Type} {P L : List α} (h : P <+: L) {i : Nat} (hi : i < P.length) :
    L[i]? = P[i]? := by
  obtain ⟨t, rfl⟩ := h
  exact List.getElem?_append_left hi

/-- **Two store runs ended by a non-store in one list agree**: stores `xs`
then a non-store `y`, and stores `ys` then a non-store `z`, both prefixes
of `L`, have as many stores. -/
theorem stRun_unique {L xs ys r1 r2 : List Directive} {y z : Directive} (h1 : xs ++ y :: r1 <+: L)
    (h2 : ys ++ z :: r2 <+: L) (hx : ∀ d ∈ xs, IsSt d) (hy : ¬ IsSt y) (hys : ∀ d ∈ ys, IsSt d)
    (hz : ¬ IsSt z) : xs.length = ys.length := by
  have key : ∀ {xs ys r1 r2 : List Directive} {y z : Directive}, xs ++ y :: r1 <+: L → ys ++ z :: r2 <+: L →
      ¬ IsSt y → (∀ d ∈ ys, IsSt d) → ¬ xs.length < ys.length := by
    intro xs ys r1 r2 y z h1 h2 hy hys hlt
    have e1 := getElem?_of_prefix h1 (i := xs.length) (by simp)
    have e2 := getElem?_of_prefix h2 (i := xs.length) (by simp; omega)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at e1
    rw [List.getElem?_append_left hlt] at e2
    rw [e1] at e2
    simp only [List.getElem?_cons_zero] at e2
    exact hy (hys _ (List.mem_of_getElem? e2.symm))
  have a := key h1 h2 hy hys
  have b := key h2 h1 hz hx
  omega

/-! ## The marshalling block at A11 -/

open Spike.Lib.X64.Rt (marshal xLd argXs retXs swOff) in
/-- **The marshalling block's directives**: `sw` stores, then a move into
a register (the first argument's load). -/
theorem marshal_dirs (sw : Nat) (fn : Label) :
    ∃ (S : List Directive) (y : Directive) (R : List Directive), (marshal sw fn).map (·.1) = S ++ y :: R ∧
      S.length = sw ∧ (∀ d ∈ S, IsSt d) ∧ IsLdR y := by
  have hst : ∀ i, IsSt (Spike.Lib.X64.Flow.xSt (retXs.getD i .rax, swOff i, 4)).1 :=
    fun i => ⟨_, _, rfl⟩
  cases sw with
  | zero =>
    exact ⟨[], (xLd (argXs.getD 0 .rdi, -8, 4)).1, (Spike.Lib.X64.callB fn).map (·.1), by simp [marshal], rfl,
      by simp, ⟨_, _, rfl⟩⟩
  | succ k =>
    refine ⟨((List.range (k + 1)).map fun i => Spike.Lib.X64.Flow.xSt (retXs.getD i .rax, swOff i, 4)).map (·.1),
      (xLd (argXs.getD 0 .rdi, swOff 0, 4)).1,
      ((((List.range k).map fun i => xLd (argXs.getD (i + 1) .rdi, swOff (i + 1), 4)) ++
        [xLd (argXs.getD (k + 1) .rdi, -8, 4)] ++ Spike.Lib.X64.callB fn)).map (·.1), ?_, by simp, ?_, ⟨_, _, rfl⟩⟩
    · simp [marshal, List.range_succ_eq_map]
    · intro d hd
      simp only [List.map_map, List.mem_map, Function.comp] at hd
      obtain ⟨i, -, rfl⟩ := hd
      exact hst i

/-- **The store runs at `scc_rt_main`'s setup return agree**: A12's
segment after `.entry` (a non-label, a label, stores `sr`, a register
move) and A11's gap from `.entry` to `sp0` and marshalling block at `sp0`
fix `sr.length` to the marshalling block's words. -/
theorem sw_eq_of_cells {cells : List (Directive × Nat)} {E sp0 lk fn : Label} {cd d : Directive}
    {sr rest : List Directive} {sw' : Nat}
    (hseg : Scc.Cert.Code1X64.segIn cells E (cd :: .label lk :: (sr ++ d :: rest)) = true)
    (hcd : cd.isLabel = false) (hst : ∀ x ∈ sr, IsSt x) (hd : IsLdR d)
    (hgap : Scc.Cert.Rt.X64.labelGapB cells E sp0 5 = true)
    (hblk : Scc.Cert.Rt.X64.blockAtB cells sp0 0 (Spike.Lib.X64.Rt.marshal sw' fn) = true) : sr.length = sw' := by
  unfold Scc.Cert.Code1X64.segIn at hseg
  split at hseg
  case h_2 => cases hseg
  rename_i i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hseg
  have hpre := hseg.1
  obtain ⟨c1, c2, T, hT⟩ : ∃ c1 c2 T, cells.drop (i + 1) = c1 :: c2 :: T := by
    cases h : cells.drop (i + 1) with
    | nil => rw [h] at hpre; simp at hpre
    | cons c1 T1 =>
      cases T1 with
      | nil => rw [h] at hpre; simp at hpre
      | cons c2 T => exact ⟨c1, c2, T, rfl⟩
  rw [hT] at hpre
  simp only [List.length_cons, List.take_succ_cons, List.map_cons, List.cons.injEq] at hpre
  obtain ⟨h1, h2, h3⟩ := hpre
  -- the gap: `sp0` two cells after `.entry`
  have hrun : (Scc.Cert.Rt.X64.run cells E).length = 1 := by
    unfold Scc.Cert.Rt.X64.run
    simp only [hi]
    rw [hT]
    simp [List.takeWhile_cons, h1, h2, Directive.isLabel]
    split <;> simp_all [Directive.isLabel]
  unfold Scc.Cert.Rt.X64.labelGapB Scc.Cert.Rt.X64.labelGap at hgap
  rw [hrun, hi] at hgap
  split at hgap
  case h_2 => simp at hgap
  rename_i i' j hi' hj
  cases hi'
  simp only [Bool.and_eq_true, beq_iff_eq] at hgap
  have hj2 : j = i + 2 := by omega
  subst hj2
  -- the marshalling block at the cells after `sp0`
  unfold Scc.Cert.Rt.X64.blockAtB at hblk
  rw [Scc.Cert.Rt.X64.after_eq, hj] at hblk
  have hT3 : cells.drop (i + 2 + 1) = T := by
    rw [show i + 2 + 1 = (i + 1) + 2 by omega, ← List.drop_drop, hT]; rfl
  simp only [Option.map_some, hT3, Scc.Cert.Rt.X64.dropBytes, decide_eq_true_eq] at hblk
  have hm : (Spike.Lib.X64.Rt.marshal sw' fn).map (·.1) <+: T.map (·.1) := by
    have : Spike.Lib.X64.Rt.marshal sw' fn <+: T := by
      rw [← hblk]
      exact (List.take_prefix _ _).trans (by rw [Scc.Cert.Rt.X64.cellRun_eq]; exact List.takeWhile_prefix _)
    exact this.map _
  have hs : sr ++ d :: rest <+: T.map (·.1) := by
    rw [← h3]
    exact (List.take_prefix _ _).map _
  obtain ⟨S, y, R, hSR, hSl, hSst, hy⟩ := marshal_dirs sw' fn
  rw [hSR] at hm
  rw [← hSl]
  exact stRun_unique hs hm hst (not_isSt_of_isLdR hd) hSst (not_isSt_of_isLdR hy)

/-! ## A11's `sw` is the lowering's -/

/-- A right fold pushing one element per step has one per element. -/
theorem foldr_snd_length {α β γ : Type} (g : α → β × List γ → β × List γ)
    (hg : ∀ i p, (g i p).2.length = p.2.length + 1) (x : β × List γ) :
    ∀ l : List α, (l.foldr g x).2.length = x.2.length + l.length
  | [] => rfl
  | i :: l => by simp only [List.foldr_cons, hg, foldr_snd_length g hg x l, List.length_cons]; omega

/-- **A one-block function's call maps**: one map per instruction. -/
theorem callMaps_single {f : Scc.IR.Func} {b : Scc.IR.Block} (hb : f.blocks = [b]) :
    ∃ ms, Scc.IR.StackMap.callMaps f = [ms] ∧ ms.length = b.insts.length := by
  refine ⟨_, by simp only [Scc.IR.StackMap.callMaps, Scc.IR.StackMap.callLives, hb, List.map_cons, List.map_nil]; rfl,
    ?_⟩
  rw [List.length_map]
  exact (foldr_snd_length _ (fun i p => by obtain ⟨a, c⟩ := p; rfl) _ _).trans (by simp)

open Spike.Lib.X64.Rt (rtCodeOkS setupMC) in
/-- **A11's setup words are the lowering's** (x86-64): on an `Accepted2`
program with a setup block whose output passes `placeOKAt`, every `sw`
with the runtime's code at `setupMC sw` is `setupWords2 p`. -/
theorem sw_eq_setupWords2 {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) {sw : Nat}
    (hc : rtCodeOkS (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (setupMC sw) = true) :
    Spike.Lib.LowerNode.setupWords2 p = sw := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_x64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.setupTid, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  rw [he] at hrt
  generalize hir' : (Scc.Lower.X64.lowerAll cfg p).low.ir = ir at hir
  have hf : Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p) ∈ ir.funcs := by
    rw [hir]
    exact List.mem_append_left _ (Spike.Lib.mainThread0_mem hrt)
  obtain ⟨n, hn⟩ := mem_starts ir 0 hf
  have h12 := Scc.Cert.PlaceOK.X64.fnCode1_of_placeOKAt h
    ((Scc.Cert.PlaceOK.X64.place_ir_ofEmitted _ _ _).trans (congrArg some hir'))
  have hok := Scc.Cert.Code1X64.fnOk1_of_fnCode1Ok h12 hn rfl
  have hm : (frOf ir (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).maps =
      true := by
    show ir.growth.isSome = true
    rw [hir]; rfl
  obtain ⟨ms, hms, hml⟩ := callMaps_single (f := Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩
    (Spike.Lib.LowerNode.setupWords2 p)) rfl
  unfold Scc.Cert.Code1X64.fnOk1 at hok
  split at hok
  case h_2 => cases hok
  rename_i b0 bs zl zf z1 z2 zs zps hb hz
  split at hok
  case h_2 => cases hok
  simp only [Bool.and_eq_true] at hok
  have hbl : Scc.Cert.Code1X64.blocksOk (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes
      labelOffs).prog (frOf ir (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))) n
      ([] ++ (⟨"entry", Scc.Lower.Inv.mainInsts ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p),
        .unreachable⟩, ms) :: []) = true := by
    have := hok.1.1.1.2
    rw [hms] at this
    exact this
  obtain ⟨code, n', hbi, hseg⟩ := Scc.Cert.Code1X64.blocksOk_block hbl
  obtain ⟨k, sr, d, rest, hdirs, hsl, hst, hd⟩ := mainCode_dirs hm (by rw [hml]; rfl) hbi
  rw [hdirs] at hseg
  have hR := Scc.Cert.Rt.X64.rtIn_sound hc
  unfold Spike.Lib.X64.Rt.rtCodeTabS at hR
  have hM := (Scc.Cert.Rt.X64.RtAll.append (Scc.Cert.Rt.X64.RtAll.append (Scc.Cert.Rt.X64.RtAll.append
    (Scc.Cert.Rt.X64.RtAll.append hR).1).1).1).2
  have hgap := hM.2.2.2.2.2.1
  have hblk := hM.2.2.2.2.2.2.1.1
  rw [← hsl]
  exact sw_eq_of_cells hseg rfl hst hd hgap hblk

open Spike.Lib.X64.Rt (rtCodeOkS setupMC) in
/-- **The setup block's result has A11's `sw` value words** (x86-64): the
premise `hw` of `hPlS_ofSPostC` / `hPl_setupArgs` at the setup block's
result type, from the placement check alone. -/
theorem valWords_of_rtCodeOkS {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) {ty : CoreLang.Ty} (hs : Scc.Lower.setupOf p = some ty) {sw : Nat}
    (hc : rtCodeOkS (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (setupMC sw) = true) :
    Scc.Obj.valWords ty = some sw := by
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hs]; rfl
  obtain ⟨dr, hfr, hrt⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hs
  obtain ⟨k, hk⟩ := setupValWords_of_placeOK h hp ty hs
  rw [← sw_eq_setupWords2 h hp hs' hc, ← hrt]
  exact Spike.Lib.LowerNode.valWords_setupWords2 hs' hfr (by rw [hrt, hk]; rfl)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.sw_eq_setupWords2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sw_eq_setupWords2

/-- info: 'Spike.Lib.LowerX64.valWords_of_rtCodeOkS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms valWords_of_rtCodeOkS

end Spike.Lib.LowerX64
