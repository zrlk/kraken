/-
**`hello.w` on x86-64, the closed run (step shapes)**: the per-instruction
lemmas the chunks of the run (`HelloRootL0XClosedC1` …) are made of.

- `Leaf t s`: `s` is a leaf of the tree `t` through choices only; `sgLeaf`:
  a segment of one such instruction (with `sgX`, its form between `mk`
  states, off the system calls and the sites).
- `stores B L`: the private memory `B` after the 8-byte stores `L` (latest
  first); `look b L`: the last value `L` stored at `b`; `loadInt_look`,
  `loadInt_look_none`: loads through them (all addresses 8-aligned, so two
  slots are equal or disjoint). `copy_in`, `copy_out`: loads through the
  take's `copyRange ∅`. `ent_none`, `stack_some`: the entry stack.
- `hx_*`: `isa.exec` of one cell at an `mk` state is the `done` of the next
  `mk` state (register operations, stack loads and stores, `push`, `pop`,
  `call`, `ret`, `jmp`, `jcc`, `leaq L(%rip)`); `lx_*`: the leaf with every
  undefined flag `false` (logic operations, `xorl`, `imul`, shifts by `%cl`).
- `sgLoadS`, `sgStoreS`, `sgRmwS`: the shared accesses, memory written out.
-/
import Spike.Test.HelloRootL0XClosedBase
import Spike.Lib.X64Cfg

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.Fwd

/-! ## Leaves -/

/-- `s'` is a leaf of `t` reached through choices only. -/
def Leaf {σ : Type} : EvTree σ → σ → Prop
  | .done s, s' => s = s'
  | .choose _ k, s' => ∃ i, Leaf (k i) s'
  | _, _ => False

theorem run_leaf {σ : Type} (A : Arch) (tid : Nat) (iv : InstrViews) (c : Ctx) :
    ∀ (t : EvTree σ) (s' : σ), Leaf t s' → .ok (s', c) ∈ runTree A tid iv c t
  | .done s, s', h => by
    cases h
    exact Live.TicketStep.run_done_exists A tid iv c s
  | .choose _ k, s', h => by
    obtain ⟨i, hi⟩ := h
    exact (Lower.run_choose_iff A tid iv).mpr ⟨i, run_leaf A tid iv c (k i) s' hi⟩
  | .fault _, _, h => h.elim
  | .load .., _, h => h.elim
  | .store .., _, h => h.elim
  | .rmw .., _, h => h.elim
  | .fence .., _, h => h.elim

/-- **One instruction, a leaf through choices.** -/
theorem sgLeaf {P P1 : State → Prop} {M : Memory} {X : Kernel.KState}
    (h : ∀ s, P s → (kernel 2).atSys s = false ∧ (∀ k a, μ0.site k = some a → pcOf s ≠ a) ∧
      ∃ t s', isa.exec s = some t ∧ Leaf t s' ∧ P1 s') : Sg P M X P1 M X := by
  intro c s hP hs hm hx
  obtain ⟨hsys, hsite, t, s', hex, hl, hP1⟩ := h s hP
  obtain ⟨s'', d, hP1', hst, h', hm', hk'⟩ := fwd_treeP (P := fun x => x = s') hs hsys hsite hex fun th _ hp _ =>
    ⟨s', Live.TicketStep.ctx0 0 th c.1.mem, rfl, run_leaf _ 0 _ _ t s' hl, rfl, hp⟩
  subst hP1'
  exact ⟨_, d, hP1, run_of_step hst, h', hm'.trans hm, hk'.1.trans hx, hk'.2⟩

/-- A `done` is a leaf. -/
theorem lf {s s' : State} (h : isa.exec s = some (.done s')) : ∃ t, isa.exec s = some t ∧ Leaf t s' :=
  ⟨_, h, rfl⟩

/-- **One instruction between `mk` states**, off the system calls and the sites. -/
theorem sgX (hparse : Parse) {R R' : Reg64s} {F F' : StatusFlags} {D D' : DataMem} {pc pc' : Nat}
    {d : Directive} {z : Nat} {M : Memory} {X : Kernel.KState} (hc : CellAt (mk R F D pc) d z)
    (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) (hs : pc < 2 ^ 64 ∧ pc ≠ 4200314 ∧ pc ≠ 4200354)
    (hex : ∃ t, isa.exec (mk R F D pc) = some t ∧ Leaf t (mk R' F' D' pc')) :
    Sg (· = mk R F D pc) M X (· = mk R' F' D' pc') M X :=
  sgLeaf fun s e => by
    subst e
    obtain ⟨t, h1, h2⟩ := hex
    exact ⟨atSyscall_false_of_cellAt hc hd, hsiteMk hparse R F D hs.1 hs.2, t, _, h1, h2, rfl⟩

/-! ## Private memory -/

/-- `B` after the 8-byte stores `L`, the latest first. -/
def stores (B : DataMem) : List (BitVec 64 × BitVec 64) → DataMem
  | [] => B
  | p :: L => Mem.storeInt (stores B L) p.1 8 p.2.toInt

/-- The last value `L` stored at `b`. -/
def look (b : BitVec 64) : List (BitVec 64 × BitVec 64) → Option (BitVec 64)
  | [] => none
  | p :: L => if p.1 = b then some p.2 else look b L

/-- Every slot of `L` is 8-aligned. -/
def Al (L : List (BitVec 64 × BitVec 64)) : Bool := L.all fun p => p.1.toNat % 8 == 0

theorem al_disj {a b : BitVec 64} (ha : a.toNat % 8 = 0) (hb : b.toNat % 8 = 0) (h : a ≠ b) :
    a.toNat + 8 ≤ 2 ^ 64 ∧ b.toNat + 8 ≤ 2 ^ 64 ∧ (a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) := by
  have h' : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
  have := a.isLt; have := b.isLt
  omega

theorem loadInt_look {B : DataMem} :
    ∀ {L : List (BitVec 64 × BitVec 64)} {b v : BitVec 64}, Al L = true → b.toNat % 8 = 0 → look b L = some v →
      Mem.loadInt (stores B L) b 8 = some (v.toNat : Int)
  | [], _, _, _, _, h => by cases h
  | p :: L, b, v, hal, hb, h => by
    simp only [Al, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hal
    simp only [look] at h
    by_cases e : p.1 = b
    · rw [ite_eq_left e] at h
      cases h
      subst e
      exact Spike.Lib.X64.loadInt_storeInt8_same _ _ _
    · rw [ite_eq_right e] at h
      obtain ⟨h1, h2, h3⟩ := al_disj hal.1 hb e
      show Mem.loadInt (Mem.storeInt (stores B L) p.1 8 p.2.toInt) b 8 = _
      rw [Spike.Lib.X64.loadInt_storeInt8_disj _ _ _ _ h1 h2 h3]
      exact loadInt_look hal.2 hb h

theorem loadInt_look_none {B : DataMem} :
    ∀ {L : List (BitVec 64 × BitVec 64)} {b : BitVec 64}, Al L = true → b.toNat % 8 = 0 → look b L = none →
      Mem.loadInt (stores B L) b 8 = Mem.loadInt B b 8
  | [], _, _, _, _ => rfl
  | p :: L, b, hal, hb, h => by
    simp only [Al, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hal
    simp only [look] at h
    by_cases e : p.1 = b
    · rw [ite_eq_left e] at h; cases h
    · rw [ite_eq_right e] at h
      obtain ⟨h1, h2, h3⟩ := al_disj hal.1 hb e
      show Mem.loadInt (Mem.storeInt (stores B L) p.1 8 p.2.toInt) b 8 = _
      rw [Spike.Lib.X64.loadInt_storeInt8_disj _ _ _ _ h1 h2 h3]
      exact loadInt_look_none hal.2 hb h

/-- A mapped slot: one `L` stored. -/
theorem ex_look {B : DataMem} {L : List (BitVec 64 × BitVec 64)} {b v : BitVec 64} (hal : Al L = true)
    (hb : b.toNat % 8 = 0) (h : look b L = some v) : ∃ j, Mem.loadInt (stores B L) b 8 = some j :=
  ⟨_, loadInt_look hal hb h⟩

/-- A mapped slot: mapped in the base. -/
theorem ex_base {B : DataMem} {L : List (BitVec 64 × BitVec 64)} {b : BitVec 64} (hal : Al L = true)
    (hb : b.toNat % 8 = 0) (h : look b L = none) (hB : ∃ j, Mem.loadInt B b 8 = some j) :
    ∃ j, Mem.loadInt (stores B L) b 8 = some j := by
  rw [loadInt_look_none hal hb h]; exact hB

/-- A load whose first byte is unmapped is unmapped. -/
theorem loadInt_none {m : DataMem} {a : BitVec 64} (h : m.get? (a + BitVec.ofNat 64 0) = none) :
    Mem.loadInt m a 8 = none := by
  unfold Mem.loadInt Mem.loadBytes
  have h' : m[a]? = none := by simpa [Std.ExtHashMap.get?_eq_getElem?] using h
  rw [show List.range 8 = 0 :: List.range' 1 7 from rfl, List.map_cons]
  simp [List.allSome, h']

/-- The entry stack's memory. -/
abbrev Ent : DataMem := Entry.linux.stackMem

/-- **Entry stack words**: mapped. -/
theorem stack_some {a : BitVec 64} (h1 : 140737488285696 ≤ a.toNat) (h2 : a.toNat + 8 ≤ 140737488351232) :
    ∃ j, Mem.loadInt Ent a 8 = some j := by
  rw [← Option.isSome_iff_exists]
  unfold Mem.loadInt
  rw [Option.isSome_map]
  unfold Mem.loadBytes
  rw [List.allSome_isSome_iff]
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
  have hi8 := List.mem_range.mp hi
  rw [Spike.Lib.X64.Flow.Ret0.Correct.stackMem_get, ite_eq_left_of_eq_true _ _ (eq_true ?_)]
  · rfl
  · have hl : Entry.linux.stack.lo = 140737488285696 := rfl
    rw [hl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-- **Off the entry stack**: unmapped. -/
theorem ent_none {a : BitVec 64} (h : ¬ ((a + BitVec.ofNat 64 0 - BitVec.ofNat 64 Entry.linux.stack.lo).toNat < 65536)) :
    Mem.loadInt Ent a 8 = none :=
  loadInt_none (by rw [Spike.Lib.X64.Flow.Ret0.Correct.stackMem_get, ite_eq_right h])

theorem get_copyRange (src D : DataMem) (r : Range) (a : BitVec 64) :
    (Kernel.copyRange src D r).get? a = if a ∈ Kernel.addrs r then some (Kernel.byte src a) else D.get? a := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?]
  exact Kernel.get_foldl_insert src _ a D

theorem toNat_add_small {b : BitVec 64} {i : Nat} (hi : i < 8) (hb : b.toNat + 8 ≤ 2 ^ 64) :
    (b + BitVec.ofNat 64 i).toNat = b.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **Off the taken range**: the load is the old one. -/
theorem copy_out {src D : DataMem} {r : Range} {b : BitVec 64} (hr : r.lo + r.size ≤ 2 ^ 64)
    (hb : b.toNat + 8 ≤ 2 ^ 64) (h : b.toNat + 8 ≤ r.lo ∨ r.lo + r.size ≤ b.toNat) :
    Mem.loadInt (Kernel.copyRange src D r) b 8 = Mem.loadInt D b 8 := by
  unfold Mem.loadInt Mem.loadBytes
  congr 2
  refine List.map_congr_left fun i hi => ?_
  have hi8 := List.mem_range.mp hi
  rw [get_copyRange, ite_eq_right]
  rw [Kernel.mem_addrs_iff hr, Range.contains, toNat_add_small hi8 hb]
  omega

/-- **In the range taken from the pool**: zero. -/
theorem copy_in {D : DataMem} {r : Range} {b : BitVec 64} (hr : r.lo + r.size ≤ 2 ^ 64)
    (h : r.lo ≤ b.toNat ∧ b.toNat + 8 ≤ r.lo + r.size) :
    Mem.loadInt (Kernel.copyRange ∅ D r) b 8 = some 0 := by
  unfold Mem.loadInt Mem.loadBytes
  rw [List.map_congr_left (g := fun _ => some 0) fun i hi => ?_]
  · rfl
  · have hi8 := List.mem_range.mp hi
    rw [get_copyRange, ite_eq_left]
    · simp [Kernel.byte]
    · rw [Kernel.mem_addrs_iff hr, Range.contains, toNat_add_small hi8 (by omega)]
      omega

/-! ## One cell, `done` -/

section Hx

variable {R R' : Reg64s} {F F' : StatusFlags} {D : DataMem} {pc pc' sz : Nat}

theorem after_mk' (R : Reg64s) (F : StatusFlags) (D : DataMem) (pc sz : Nat) (md : MachineData) (hz : md.zmms = {}) :
    after (mk R F D pc) sz md = mk md.regs md.status md.dmem (pc + sz) := by
  obtain ⟨r, z, f, d⟩ := md
  simp only at hz; subst hz
  simp only [after, mk, Int64.ofNat_add]

/-- A register operation. -/
theorem hx_reg {w : Width} {op : Operation w} (h : Spike.Lib.X64.RegOnly op = true)
    (hc : CellAt (mk R F D pc) (.instr (.regular .W64 w op)) sz)
    (hR : (Spike.Lib.X64.regRes op { regs := R, status := F, dmem := ∅ }).regs = R')
    (hF : (Spike.Lib.X64.regRes op { regs := R, status := F, dmem := ∅ }).status = F') (hp : pc + sz = pc') :
    isa.exec (mk R F D pc) = some (.done (mk R' F' D pc')) := by
  rw [Spike.Lib.X64.exec_reg h hc, Spike.Lib.X64.regRes_eq h, after_mk' _ _ _ _ _ _ rfl]
  subst hR hF hp; rfl

/-- `mov r64, o(%b)`, the slot mapped. -/
theorem hx_ld {r : Reg .W64} {b : Reg64} {o : Int64} {a : BitVec 64} {j : Int}
    (hc : CellAt (mk R F D pc) (op64 (.mov (.reg r) (.mem { base := some (.reg b), idx := none, disp := .int64 o })))
      sz)
    (ha : BitVec.ofInt 64 ((R.get64 b).toInt + o.toInt) = a) (hdm : Mem.loadInt D a 8 = some j)
    (hR : R.set r (BitVec.ofInt 64 j) = R') (hp : pc + sz = pc') :
    isa.exec (mk R F D pc) = some (.done (mk R' F D pc')) := by
  rw [exec_load_mapped hc ((eaddr_reg_disp _ _ _ _).trans ha) hdm, after_mk' _ _ _ _ _ _ rfl]
  subst hR hp; rfl

/-- `mov o(%b), r64`, the slot mapped. -/
theorem hx_st {r : Reg .W64} {b : Reg64} {o : Int64} {a v : BitVec 64}
    (hc : CellAt (mk R F D pc) (op64 (.mov (.mem { base := some (.reg b), idx := none, disp := .int64 o }) (.reg r)))
      sz)
    (ha : BitVec.ofInt 64 ((R.get64 b).toInt + o.toInt) = a) (hdm : ∃ j, Mem.loadInt D a 8 = some j)
    (hv : R.get r = v) (hp : pc + sz = pc') :
    isa.exec (mk R F D pc) = some (.done (mk R F (Mem.storeInt D a 8 v.toInt) pc')) := by
  obtain ⟨j, hj⟩ := hdm
  rw [exec_store_mapped hc ((eaddr_reg_disp _ _ _ _).trans ha) hj, after_mk' _ _ _ _ _ _ rfl]
  subst hv hp; rfl

/-- `push r64`, the slot mapped. -/
theorem hx_push {r : Reg64} {a v : BitVec 64} (hc : CellAt (mk R F D pc) (op64 (.push (.reg (.low r .W64)))) sz)
    (ha : R.get64 .rsp - 8#64 = a) (hdm : ∃ j, Mem.loadInt D a 8 = some j) (hv : R.get64 r = v)
    (hR : R.set64 .rsp a = R') (hp : pc + sz = pc') :
    isa.exec (mk R F D pc) = some (.done (mk R' F (Mem.storeInt D a 8 v.toInt) pc')) := by
  subst ha
  obtain ⟨j, hj⟩ := hdm
  rw [Spike.Lib.X64.exec_push_mapped hc hj, after_mk' _ _ _ _ _ _ rfl]
  subst hv hR hp; rfl

/-- `pop r64`, the slot mapped. -/
theorem hx_pop {r : Reg64} {a : BitVec 64} {j : Int} (hc : CellAt (mk R F D pc) (op64 (.pop (.reg (.low r .W64)))) sz)
    (ha : R.get64 .rsp = a) (hdm : Mem.loadInt D a 8 = some j)
    (hR : (R.set64 .rsp (R.get64 .rsp + 8#64)).set64 r (BitVec.ofInt 64 j) = R') (hp : pc + sz = pc') :
    isa.exec (mk R F D pc) = some (.done (mk R' F D pc')) := by
  subst ha
  rw [Spike.Lib.X64.exec_pop_mapped hc hdm, after_mk' _ _ _ _ _ _ rfl]
  subst hR hp; rfl

/-- `call L`, the slot mapped. -/
theorem hx_call {L : Label} {a v : BitVec 64} {t : Nat}
    (hc : CellAt (mk R F D pc) (op64 (.call (.rel (.sub (.label L) .after_current_instruction)))) sz)
    (hL : (_root_.Executable.labels st0.exe).label L = Int64.ofNat t)
    (ha : R.get64 .rsp - 8#64 = a) (hdm : ∃ j, Mem.loadInt D a 8 = some j)
    (hv : (Int64.ofNat pc + Int64.ofNat sz).toBitVec = v) (hR : R.set64 .rsp a = R') :
    isa.exec (mk R F D pc) = some (.done (mk R' F (Mem.storeInt D a 8 v.toInt) t)) := by
  subst ha
  obtain ⟨j, hj⟩ := hdm
  have hL' : labelAddr (mk R F D pc) L = Int64.ofNat t := hL
  rw [exec_call_label hc hj, hL']
  subst hv hR; rfl

/-- `ret`, the slot mapped. -/
theorem hx_ret {a : BitVec 64} {j : Int} {t : Nat} (hc : CellAt (mk R F D pc) (op64 .ret) sz)
    (ha : R.get64 .rsp = a) (hdm : Mem.loadInt D a 8 = some j)
    (hR : R.set64 .rsp (R.get64 .rsp + 8#64) = R') (ht : Int64.ofBitVec (BitVec.ofInt 64 j) = Int64.ofNat t) :
    isa.exec (mk R F D pc) = some (.done (mk R' F D t)) := by
  subst ha
  rw [exec_ret hc hdm, ht]
  subst hR; rfl

/-- `jmp L`. -/
theorem hx_jmp {L : Label} {t : Nat}
    (hc : CellAt (mk R F D pc) (op64 (.jmp (.rel (.sub (.label L) .after_current_instruction)))) sz)
    (hL : (_root_.Executable.labels st0.exe).label L = Int64.ofNat t) :
    isa.exec (mk R F D pc) = some (.done (mk R F D t)) := by
  have hL' : labelAddr (mk R F D pc) L = Int64.ofNat t := hL
  rw [exec_jmp_label hc, hL']

/-- `jcc L`, taken. -/
theorem hx_jccT {cc : CondCode} {L : Label} {t : Nat} (hc : CellAt (mk R F D pc) (op64 (.jcc cc L)) sz)
    (hcc : cc.interp F = true) (hL : (_root_.Executable.labels st0.exe).label L = Int64.ofNat t) :
    isa.exec (mk R F D pc) = some (.done (mk R F D t)) := by
  have hL' : labelAddr (mk R F D pc) L = Int64.ofNat t := hL
  rw [exec_jcc hc]
  simp only [mk] at hcc ⊢
  rw [ite_eq_left hcc, hL']

/-- `jcc L`, not taken. -/
theorem hx_jccN {cc : CondCode} {L : Label} (hc : CellAt (mk R F D pc) (op64 (.jcc cc L)) sz)
    (hcc : cc.interp F = false) (hp : pc + sz = pc') :
    isa.exec (mk R F D pc) = some (.done (mk R F D pc')) := by
  rw [exec_jcc hc]
  simp only [mk] at hcc ⊢
  rw [ite_eq_right (by rw [hcc]; decide), ← hp, Int64.ofNat_add]

/-- `leaq L(%rip), r64`. -/
theorem hx_leaRip {d : Reg .W64} {L : Label} {t : Nat}
    (hc : CellAt (mk R F D pc)
      (op64 (.lea d { base := some .rip, idx := none, disp := .sub (.label L) .after_current_instruction })) sz)
    (hL : (_root_.Executable.labels st0.exe).label L = Int64.ofNat t)
    (hR : R.set d (Int64.ofNat t).toBitVec = R') (hp : pc + sz = pc') :
    isa.exec (mk R F D pc) = some (.done (mk R' F D pc')) := by
  have hL' : labelAddr (mk R F D pc) L = Int64.ofNat t := hL
  rw [exec_lea_rip_label hc, hL', after_mk' _ _ _ _ _ _ rfl]
  subst hR hp; rfl

/-! ## One cell, undefined flags `false` -/

/-- A logic operation (`and`, `or`, `xor`): `AF` clear. -/
theorem lx_logic {d : Reg .W64} {v : BitVec 64}
    (hex : isa.exec (mk R F D pc) = some (.choose 2 fun i => .done (logicPost (mk R F D pc) sz d v (i.val == 1))))
    (hR : R.set d v = R') (hF : logicFlags v false = F') (hp : pc + sz = pc') :
    ∃ t, isa.exec (mk R F D pc) = some t ∧ Leaf t (mk R' F' D pc') := by
  refine ⟨_, hex, ⟨0, ?_⟩⟩
  show after (mk R F D pc) sz { regs := R.set d v, status := logicFlags v false, dmem := D } = _
  rw [after_mk' _ _ _ _ _ _ rfl]
  subst hR hF hp; rfl

/-- `xorl r32, r32`: `AF` clear. -/
theorem lx_xor32 {d : Reg .W32}
    (hex : isa.exec (mk R F D pc) = some (.choose 2 fun i => .done (after (mk R F D pc) sz
      { regs := R.set d 0#32, status := .from_result 0#32 { cf := false, af := i.val == 1, of := false },
        dmem := D })))
    (hR : R.set d 0#32 = R') (hF : StatusFlags.from_result 0#32 { cf := false, af := false, of := false } = F')
    (hp : pc + sz = pc') :
    ∃ t, isa.exec (mk R F D pc) = some t ∧ Leaf t (mk R' F' D pc') := by
  refine ⟨_, hex, ⟨0, ?_⟩⟩
  show after (mk R F D pc) sz _ = _
  rw [after_mk' _ _ _ _ _ _ rfl]
  subst hR hF hp; rfl

/-- `imul r64, r64'`: `SF`, `ZF`, `AF`, `PF` clear. -/
theorem lx_imul {d : Reg .W64} {a b : BitVec 64}
    (hex : isa.exec (mk R F D pc) = some (.choose 2 fun sf => .choose 2 fun zf => .choose 2 fun af =>
      .choose 2 fun pf => .done (imulPost (mk R F D pc) sz d a b (sf.val == 1) (zf.val == 1) (af.val == 1)
        (pf.val == 1))))
    (hR : R.set d (a * b) = R')
    (hF : ({ cf := imulOvf a b, pf := false, af := false, zf := false, sf := false, of := imulOvf a b } : StatusFlags)
      = F') (hp : pc + sz = pc') :
    ∃ t, isa.exec (mk R F D pc) = some t ∧ Leaf t (mk R' F' D pc') := by
  refine ⟨_, hex, ⟨0, 0, 0, 0, ?_⟩⟩
  show after (mk R F D pc) sz _ = _
  rw [after_mk' _ _ _ _ _ _ rfl]
  subst hR hF hp; rfl

/-- `shr r64, %cl`, count neither 0 nor 1: `AF`, `OF` clear. -/
theorem lx_shr {R R' : Reg64s} {F F' : StatusFlags} {D : DataMem} {pc pc' sz : Nat} {d : Reg .W64}
    (hc : CellAt (mk R F D pc) (op64 (.shr (.reg d) .cl)) sz) (hk0 : clCount (mk R F D pc) ≠ 0)
    (hk1 : clCount (mk R F D pc) ≠ 1)
    (hR : R.set d (R.get d >>> ((R.rcx.toBitVec.take 8).toNat &&& 63)) = R')
    (hF : StatusFlags.from_result (R.get d >>> ((R.rcx.toBitVec.take 8).toNat &&& 63))
      { cf := BitVec.getLsbD (R.get d) (((R.rcx.toBitVec.take 8).toNat &&& 63) - 1), af := false, of := false } = F')
    (hp : pc + sz = pc') :
    ∃ t, isa.exec (mk R F D pc) = some t ∧ Leaf t (mk R' F' D pc') := by
  have hlt := clCount_lt (mk R F D pc)
  have hk' : (clCount (mk R F D pc) == 0) = false := by simpa using hk0
  have hk1' : (clCount (mk R F D pc) == 1) = false := by simpa using hk1
  refine ⟨_, exec_of_cellAt hc, ?_⟩
  simp only [clCount] at hk' hlt hk1'
  simp [Directive.interp, Instr.interp, Operation.interp, MachineData.set, MachineData.setReg, hk', hlt, hk1',
      RegOrMem.interp, ShiftCountExpr.interpMasked, ShiftCountExpr.interp, toEv, EvTree.map, Leaf]
  refine Or.inl (Or.inl ?_)
  subst hR hF hp
  simp only [mk, Int64.ofNat_add]
  all_goals rfl

/-- `shl r64, %cl`, count neither 0 nor 1: `AF`, `OF` clear. -/
theorem lx_shl {R R' : Reg64s} {F F' : StatusFlags} {D : DataMem} {pc pc' sz : Nat} {d : Reg .W64}
    (hc : CellAt (mk R F D pc) (op64 (.shl (.reg d) .cl)) sz) (hk0 : clCount (mk R F D pc) ≠ 0)
    (hk1 : clCount (mk R F D pc) ≠ 1)
    (hR : R.set d (R.get d <<< ((R.rcx.toBitVec.take 8).toNat &&& 63)) = R')
    (hF : StatusFlags.from_result (R.get d <<< ((R.rcx.toBitVec.take 8).toNat &&& 63))
      { cf := BitVec.getMsbD (R.get d) (((R.rcx.toBitVec.take 8).toNat &&& 63) - 1), af := false, of := false } = F')
    (hp : pc + sz = pc') :
    ∃ t, isa.exec (mk R F D pc) = some t ∧ Leaf t (mk R' F' D pc') := by
  have hlt := clCount_lt (mk R F D pc)
  have hk' : (clCount (mk R F D pc) == 0) = false := by simpa using hk0
  have hk1' : (clCount (mk R F D pc) == 1) = false := by simpa using hk1
  refine ⟨_, exec_of_cellAt hc, ?_⟩
  simp only [clCount] at hk' hlt hk1'
  simp [Directive.interp, Instr.interp, Operation.interp, MachineData.set, MachineData.setReg, hk', hlt, hk1',
      RegOrMem.interp, ShiftCountExpr.interpMasked, ShiftCountExpr.interp, toEv, EvTree.map, Leaf]
  refine Or.inl (Or.inl ?_)
  subst hR hF hp
  simp only [mk, Int64.ofNat_add]
  all_goals rfl

end Hx

/-! ## Shared accesses -/

section Sh

variable {R R' : Reg64s} {F F' : StatusFlags} {D : DataMem} {pc pc' sz : Nat} {M : Memory} {X : Kernel.KState}

theorem decls_mk (R : Reg64s) (F : StatusFlags) (D : DataMem) (pc : Nat) : (mk R F D pc).decls = {} := rfl

/-- `mov r64, [m]`, the address unmapped: reads `M`'s last write of it. -/
theorem sgLdSh (hparse : Parse) {r : Reg .W64} {m : AddrExpr} {a : BitVec 64} {val : Val}
    (hc : CellAt (mk R F D pc) (op64 (.mov (.reg r) (.mem m))) sz) (hs : pc < 2 ^ 64 ∧ pc ≠ 4200314 ∧ pc ≠ 4200354)
    (ha : eaddr (mk R F D pc) sz m = a) (hdm : Mem.loadInt D a 8 = none) (hv : M.finalVal ⟨a, 8⟩ = val)
    (hR : R.set r (val.setWidth 64) = R') (hp : pc + sz = pc') :
    Sg (· = mk R F D pc) M X (· = mk R' F D pc') M X :=
  segP_load ⟨a, 8⟩ fun s e => by
    subst e
    refine ⟨atSyscall_false_of_cellAt hc (by intro _ _ h; cases h), hsiteMk hparse R F D hs.1 hs.2, .plain, _,
      exec_load_agrees hc ha hdm (Spike.Lib.X64.agrees_of_decls (decls_mk R F D pc) a 8), ?_⟩
    show after (mk R F D pc) sz _ = _
    rw [after_mk' _ _ _ _ _ _ rfl, hv]
    subst hR hp; rfl

/-- `movq %fs:m, r64`, the address unmapped: reads `M`'s last write of it. -/
theorem sgFsSh (hparse : Parse) {r : Reg .W64} {m : AddrExpr} {a : BitVec 64} {val : Val}
    (hc : CellAt (mk R F D pc) (op64 (.movfs (.reg r) (.mem m))) sz) (hs : pc < 2 ^ 64 ∧ pc ≠ 4200314 ∧ pc ≠ 4200354)
    (ha : fsAddr (mk R F D pc) sz m = a) (hdm : Mem.loadInt D a 8 = none) (hv : M.finalVal ⟨a, 8⟩ = val)
    (hR : R.set r (val.setWidth 64) = R') (hp : pc + sz = pc') :
    Sg (· = mk R F D pc) M X (· = mk R' F D pc') M X :=
  segP_load ⟨a, 8⟩ fun s e => by
    subst e
    refine ⟨atSyscall_false_of_cellAt hc (by intro _ _ h; cases h), hsiteMk hparse R F D hs.1 hs.2, .plain, _,
      exec_movfs_load_agrees hc ha hdm (Spike.Lib.X64.agrees_of_decls (decls_mk R F D pc) a 8), ?_⟩
    show after (mk R F D pc) sz _ = _
    rw [after_mk' _ _ _ _ _ _ rfl, hv]
    subst hR hp; rfl

/-- `mov [m], r64`, the address unmapped: the write `val` is appended. -/
theorem sgStSh (hparse : Parse) {r : Reg .W64} {m : AddrExpr} {a : BitVec 64} {val : Val}
    (hc : CellAt (mk R F D pc) (op64 (.mov (.mem m) (.reg r))) sz) (hs : pc < 2 ^ 64 ∧ pc ≠ 4200314 ∧ pc ≠ 4200354)
    (ha : eaddr (mk R F D pc) sz m = a) (hdm : Mem.loadInt D a 8 = none) (hv : (R.get r).setWidth 128 = val)
    (hp : pc + sz = pc') :
    Sg (· = mk R F D pc) M X (· = mk R F D pc') (M.append { loc := ⟨a, 8⟩, val := val, tid := 0 }).1 X :=
  segP_store ⟨a, 8⟩ val fun s e => by
    subst e
    have hx := exec_store_agrees hc ha hdm (Spike.Lib.X64.agrees_of_decls (decls_mk R F D pc) a 8)
    rw [show (mk R F D pc).st.1.regs = R from rfl, hv] at hx
    refine ⟨atSyscall_false_of_cellAt hc (by intro _ _ h; cases h), hsiteMk hparse R F D hs.1 hs.2, .plain, _,
      hx, ?_⟩
    show after (mk R F D pc) sz _ = _
    rw [after_mk' _ _ _ _ _ _ rfl]
    subst hp; rfl

/-- `lock xadd r64, [m]`, the address unmapped: reads `old`, appends `old + r`. -/
theorem sgXaddSh (hparse : Parse) {r : Reg .W64} {m : AddrExpr} {a : BitVec 64} {old nv : Val}
    (hc : CellAt (mk R F D pc) (op64 (.xadd true (.mem m) r)) sz) (hs : pc < 2 ^ 64 ∧ pc ≠ 4200314 ∧ pc ≠ 4200354)
    (ha : eaddr (mk R F D pc) sz m = a) (hdm : Mem.loadInt D a 8 = none) (hv : M.finalVal ⟨a, 8⟩ = old)
    (hn : (old.setWidth 64 + R.get r).setWidth 128 = nv) (hR : R.set r (old.setWidth 64) = R')
    (hF : LockBinOp.add.status (old.setWidth 64) (R.get r) (old.setWidth 64 + R.get r) false = F')
    (hp : pc + sz = pc') :
    Sg (· = mk R F D pc) M X (· = mk R' F' D pc') (M.append { loc := ⟨a, 8⟩, val := nv, tid := 0 }).1 X := by
  have h := segP_rmw (I := isa) (A := Arch.tso) (H := kernel 2) (rv := regVal) (pl := privLoad) (pcf := pcOf)
    (μ := μ0) (tid := 0) (P := (· = mk R F D pc)) (P1 := (· = mk R' F' D pc')) (M := M) (X := X) rfl ⟨a, 8⟩
    (fun old => (old.setWidth 64 + R.get r).setWidth 128) fun s e => by
      subst e
      refine ⟨atSyscall_false_of_cellAt hc (by intro _ _ h; cases h), hsiteMk hparse R F D hs.1 hs.2, .acqRel,
        fun (v : Val) => after (mk R F D pc) sz { regs := R.set r (v.setWidth 64), status := LockBinOp.add.status (v.setWidth 64) (R.get r) (v.setWidth 64 + R.get r) false, dmem := D },
        (by rw [exec_xadd hc ha hdm, access_agrees (Spike.Lib.X64.agrees_of_decls (decls_mk R F D pc) a 8)] <;> rfl), ?_⟩
      show after (mk R F D pc) sz _ = _
      rw [after_mk' _ _ _ _ _ _ rfl, hv]
      subst hR hF hp; rfl
  rw [hv, hn] at h
  exact h

/-- `xchg r64, [m]`, the address unmapped: reads `old`, appends `r`. -/
theorem sgXchgSh (hparse : Parse) {r : Reg .W64} {m : AddrExpr} {a : BitVec 64} {old nv : Val}
    (hc : CellAt (mk R F D pc) (op64 (.xchg r (.mem m))) sz) (hs : pc < 2 ^ 64 ∧ pc ≠ 4200314 ∧ pc ≠ 4200354)
    (ha : eaddr (mk R F D pc) sz m = a) (hdm : Mem.loadInt D a 8 = none) (hv : M.finalVal ⟨a, 8⟩ = old)
    (hn : (R.get r).setWidth 128 = nv) (hR : R.set r (old.setWidth 64) = R') (hp : pc + sz = pc') :
    Sg (· = mk R F D pc) M X (· = mk R' F D pc') (M.append { loc := ⟨a, 8⟩, val := nv, tid := 0 }).1 X := by
  have h := segP_rmw (I := isa) (A := Arch.tso) (H := kernel 2) (rv := regVal) (pl := privLoad) (pcf := pcOf)
    (μ := μ0) (tid := 0) (P := (· = mk R F D pc)) (P1 := (· = mk R' F D pc')) (M := M) (X := X) rfl ⟨a, 8⟩
    (fun _ => (R.get r).setWidth 128) fun s e => by
      subst e
      refine ⟨atSyscall_false_of_cellAt hc (by intro _ _ h; cases h), hsiteMk hparse R F D hs.1 hs.2, .acqRel,
        fun (v : Val) => after (mk R F D pc) sz { regs := R.set r (v.setWidth 64), status := F, dmem := D },
        (by rw [exec_xchg hc ha hdm, access_agrees (Spike.Lib.X64.agrees_of_decls (decls_mk R F D pc) a 8)] <;> rfl), ?_⟩
      show after (mk R F D pc) sz _ = _
      rw [after_mk' _ _ _ _ _ _ rfl, hv]
      subst hR hp; rfl
  rw [hn] at h
  exact h

end Sh

end Spike.Test.HelloRootL0XClosed

/-- info: 'Spike.Test.HelloRootL0XClosed.sgX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sgX
/-- info: 'Spike.Test.HelloRootL0XClosed.sgLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sgLeaf
/-- info: 'Spike.Test.HelloRootL0XClosed.loadInt_look' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.loadInt_look
/-- info: 'Spike.Test.HelloRootL0XClosed.copy_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.copy_in
/-- info: 'Spike.Test.HelloRootL0XClosed.copy_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.copy_out
/-- info: 'Spike.Test.HelloRootL0XClosed.hx_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.hx_ret
/-- info: 'Spike.Test.HelloRootL0XClosed.lx_shl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.lx_shl
/-- info: 'Spike.Test.HelloRootL0XClosed.lx_shr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.lx_shr
/-- info: 'Spike.Test.HelloRootL0XClosed.sgLdSh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sgLdSh
/-- info: 'Spike.Test.HelloRootL0XClosed.sgFsSh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sgFsSh
/-- info: 'Spike.Test.HelloRootL0XClosed.sgStSh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sgStSh
/-- info: 'Spike.Test.HelloRootL0XClosed.sgXaddSh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sgXaddSh
/-- info: 'Spike.Test.HelloRootL0XClosed.sgXchgSh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sgXchgSh
