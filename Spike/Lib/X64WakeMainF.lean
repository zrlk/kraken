/-
**main's flag load facts** (x86-64): the x64 twin of
`Spike/Lib/A64WakeMainF.lean`. The node obligations of main's post-spawn
segments (`WaitLoop.LoopW`, `Park.ParkGW`, `X64WakeMainSegW.ParentW`, the
`exit_group` tail's) at `W := fun s c => FlagW lbl lsize q s c`, `q` the pc
after `wc_waitLoop`'s flag load `movq (%rcx), %rax` (the loop's `n5` node,
`.Lwc_waitLoop.entry + 7`). The loop's control `c0` is at `wlBody`, its flag
word inside its label (`Flag0`); past the load the source is at `wlIf` with
`d` read as `1`, and the parent's control is at neither (`FlagOff`). At `c0`
the state's instruction is no load of the flag's word but the flag load (a
block runs to `.done`, a `syscall` faults, an `xchg` is an RMW, the
prologue's limit load reads `%fs:8 = tp + 8 ≠ A`, the park's thread-pointer
load `%fs:0 = tp ≠ A`), which lands at `q` with the value in `%rax`; at `q`
`%rax ≠ 1`; every other pc of `c0` is off `q` (`RunsNe`, decided on the
listing at `flagRuns`, `wake_flagRuns`).

- `FlagW` (x86-64: `%rax` for `x9`), `FlagOff`, `Flag0`, `flag0_of`,
  `flagOff_past`, `flagW_mk`, `flagW_off`, `runsNe_at`.
- `blkW_flag`, `nodeW_flag`, `blkW_off`, `nodeW_off`, `xchg_noLoad`,
  `syscall_noLoad`.
- `tp8_ne`: the limit word `tp + 8`, outside every placed label, is not the
  flag's word.
- `flagRuns`, `flag_chk`, `wake_flagRuns`; `loopW_flag`, `parkGW_flag`,
  `parentW_flag`, `exitW0_flag`, `exitW1_flag`.

**Deviations from the A64 file.** `FlagW` is defined here (A64's lives in
`WakeInst`; there is no x86-64 `WakeInst` yet) and reads `%rax`, where the
x86-64 loop loads the flag; `q = label ".Lwc_waitLoop.entry" + 7` (after
`b4`'s 4 bytes and the load's 3). The limit load is the prologue's `w2`
node, covered inside `loopW_flag` (premise `htp8`); there is no
`tlsW_flag`. The park's entry loads the thread pointer `%fs:0`, so
`parkGW_flag` needs `tp ≠ A` (`htp`; A64's park has no such load). The code
comes from `waitIn` as in `X64WakeMainS`; no alignment premise. The runs
check is decided here (`flag_chk`) rather than in a separate runs file.
-/
import Spike.Lib.X64WakeMainS
import Spike.Lib.X64WakeM0
import Spike.Lib.X64RunsOff
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64WakeMainF

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)
open Scc.Sem (ValRep LocRep)
open Spike.Lib.X64WakeMainSegW (ParentW exitN exitNP)
open Spike.Lib.X64WakeM0 (wlBody wlIf)
open Spike.Lib.X64WakeOff (RunsNe)
open Spike.Lib.X64.RunsOff (runsNeChk runsNeQ_of_chk)

/-- **main's flag load** at placement `lbl`/`lsize`, `q` the pc after
`wc_waitLoop`'s flag load (the x86-64 `WakeInst.FlagW`, `%rax` for `x9`):
- at `wlIf`, `d` is bound to a word representing `1` (`FE`);
- at `wlBody`, `c` is bound to one untagged locative inside its placed
  label (`FA`);
- at `wlBody`, a load of the word `c` represents continues, on every value,
  at `q` with the value's low 64 bits in `%rax` (`FG`);
- at `wlBody` and `q`, `%rax` is not `1` (`FX`). -/
def FlagW (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (q : Int64)
    (s : State) (c : Ctl) : Prop :=
  (c.term = wlIf → ∀ t w', TermRun.lookupE c.env "d" = some (t, [w']) → ValRep lbl w'.val 1) ∧
  (c.term = wlBody → ∃ t w sa, TermRun.lookupE c.env "c" = some (t, [w]) ∧ w.val = .loc sa 0 ∧
    (lbl sa.label).isSome ∧ sa.offset < lsize sa.label) ∧
  (c.term = wlBody → ∀ t w (A' : BitVec 64) kl (k' : Val → EvTree State),
    TermRun.lookupE c.env "c" = some (t, [w]) → ValRep lbl w.val A'.toNat →
    isa.exec s = some (.load kl false ⟨A', 8⟩ k') →
    ∀ v, ∃ s', k' v = .done s' ∧ s'.st.2 = q ∧ s'.st.1.regs.rax.toBitVec = v.setWidth 64) ∧
  (c.term = wlBody → s.st.2 = q → s.st.1.regs.rax.toBitVec ≠ 1#64)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64} {c0 : Ctl}
  {A : BitVec 64}

/-! ## The controls -/

/-- **A control off the flag load**: not at `wlBody`, and at `wlIf` with
`d` bound to a word representing `1`. -/
def FlagOff (lbl : WeakMem.AllocLabel → Option Nat) (c : Ctl) : Prop :=
  c.term ≠ wlBody ∧ (c.term = wlIf → ∀ t w', TermRun.lookupE c.env "d" = some (t, [w']) → ValRep lbl w'.val 1)

/-- **The flag load's control**: at `wlBody`, `c` bound to one untagged
locative inside its placed label, every word representing which is `A`. -/
def Flag0 (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (c0 : Ctl)
    (A : BitVec 64) : Prop :=
  c0.term = wlBody ∧ (∃ t w sa, TermRun.lookupE c0.env "c" = some (t, [w]) ∧ w.val = .loc sa 0 ∧
    (lbl sa.label).isSome ∧ sa.offset < lsize sa.label) ∧
  ∀ t w (A' : BitVec 64), TermRun.lookupE c0.env "c" = some (t, [w]) → ValRep lbl w.val A'.toNat → A' = A

theorem wlBody_ne_wlIf : wlBody ≠ wlIf := by
  intro h; unfold wlBody wlIf at h; cases h

/-- `wlBody`'s load binds `d` from `c` and continues at `wlIf`. -/
theorem shape_of {x : String} {a : At} {e : Expr} (hwb : c0.term = wlBody)
    (hterm : c0.term = .let_ x (.load true a) e) : x = "d" ∧ a = .var "c" ∧ e = wlIf := by
  rw [hwb] at hterm; unfold wlBody at hterm; cases hterm; exact ⟨rfl, rfl, rfl⟩

/-- **`Flag0` at the loop's control**: at `wlBody` (`hwb`), its load's word
`w` an untagged locative with base `A` (`hloc`), inside its label (`hin`). -/
theorem flag0_of {x : String} {a : At} {e : Expr} {ty : Ty} {w : TermRun.Word} (hwb : c0.term = wlBody)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hloc : LocRep lbl w.val A.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    Flag0 lbl lsize c0 A := by
  obtain ⟨-, rfl, -⟩ := shape_of hwb hterm
  have hl : TermRun.lookupE c0.env "c" = some (ty, [w]) := hev
  obtain ⟨sa, hw, hsz⟩ := hin
  rw [hw] at hloc
  obtain ⟨-, hb, ho⟩ := hloc
  refine ⟨hwb, ⟨ty, w, sa, hl, hw, by rw [hb]; rfl, hsz⟩, fun t w' A' hl' hv => ?_⟩
  rw [hl] at hl'
  cases hl'
  rw [hw] at hv
  obtain ⟨-, y, hy, hA'⟩ := hv
  have hy' : (lbl sa.label).map (· + 8 * sa.offset) = some y := hy
  rw [hb, Option.map_some, Option.some.injEq] at hy'
  have h1 : @Eq Nat 0 (8 * sa.offset) := ho
  have h2 : @Eq Nat (A.toNat + 8 * sa.offset) y := hy'
  have h3 : @Eq Nat A'.toNat (y + 0) := hA'
  exact BitVec.eq_of_toNat_eq (by omega)

/-- **Past the load the control is off it**: at `wlIf`, `d` read as `1`. -/
theorem flagOff_past {x : String} {a : At} {e : Expr} {ty : Ty} {ms : MemSide isa} {c : Ctl}
    (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e)
    (h : Spike.Lib.X64.WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c) :
    FlagOff lbl c := by
  obtain ⟨rfl, -, rfl⟩ := shape_of hwb hterm
  obtain ⟨w', ⟨-, hw'⟩, rfl⟩ := h
  refine ⟨fun h => wlBody_ne_wlIf h.symm, fun _ t w'' hl => ?_⟩
  simp only [TermRun.lookupE, List.find?, beq_self_eq_true, Option.map_some, Option.some.injEq,
    Prod.mk.injEq, List.cons.injEq, and_true] at hl
  obtain ⟨-, rfl⟩ := hl
  exact hw'

/-- **`FlagW` from its pieces**: the control `c0` or off the flag load; at
`c0`, a load of `A` lands at `q` with the value in `%rax` (`hG`), and at `q`
`%rax ≠ 1` (`hX`). -/
theorem flagW_mk {s : State} {c : Ctl} (h0 : Flag0 lbl lsize c0 A) (hc : c = c0 ∨ FlagOff lbl c)
    (hG : c = c0 → ∀ kl (k' : Val → EvTree State), isa.exec s = some (.load kl false ⟨A, 8⟩ k') →
      ∀ v, ∃ s', k' v = .done s' ∧ s'.st.2 = q ∧ s'.st.1.regs.rax.toBitVec = v.setWidth 64)
    (hX : c = c0 → s.st.2 = q → s.st.1.regs.rax.toBitVec ≠ 1#64) : FlagW lbl lsize q s c := by
  unfold FlagW
  rcases hc with rfl | ⟨hb, hE⟩
  · obtain ⟨hwb, hA, hu⟩ := h0
    refine ⟨fun h => absurd (hwb.symm.trans h) wlBody_ne_wlIf, fun _ => hA,
      fun _ t w A' kl k' hl hv he => ?_, fun _ => hX rfl⟩
    obtain rfl := hu t w A' hl hv
    exact hG rfl kl k' he
  · exact ⟨hE, fun h => absurd h hb, fun h => absurd h hb, fun h => absurd h hb⟩

/-- **`FlagW` off the flag load.** -/
theorem flagW_off {s : State} {c : Ctl} (h : FlagOff lbl c) : FlagW lbl lsize q s c :=
  ⟨h.2, fun e => absurd e h.1, fun e => absurd e h.1, fun e => absurd e h.1⟩

/-- **A pc of a byte run is not `q`.** -/
theorem runsNe_at {lab : String → Int64} {runs : List (String × Nat × Nat)} (h : RunsNe lab q runs)
    {l : String} {lo hi j : Nat} (hq : (l, lo, hi) ∈ runs) (h1 : lo ≤ j) (h2 : j < hi) {p : Int64}
    (hp : p = lab l + Int64.ofNat j) : p ≠ q := by
  subst hp; exact h _ hq j h1 h2

/-! ## Blocks and nodes -/

/-- **A covered block's states are in `FlagW`**: they run to `.done`; their
controls are `c0` or off the flag load, and at `c0` `%rax ≠ 1` wherever the
pc is `q` (`hX`). -/
theorem blkW_flag {n : ND} {lo hi : Int} {blk : List (Directive × Nat)} (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (h0 : Flag0 lbl lsize c0 A)
    (hc : ∀ σ c, n.J σ c → c = c0 ∨ FlagOff lbl c)
    (hX : ∀ σ k m, n.J σ c0 → k < blk.length →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      n.pc + Int64.ofNat (cellOff blk k) = q → m.regs.rax.toBitVec ≠ 1#64) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA _
  subst he
  obtain ⟨s', hx⟩ := blk_exec_done hok hR hlo hhi (hcode s rfl hn) hk hA
  refine ⟨flagW_mk h0 (hc σ c hJ) (fun _ _ _ h => by rw [hx] at h; cases h) fun hc0 hq => ?_, fun _ h => h⟩
  subst hc0
  exact hX σ k m hJ hk hA hq

/-- **A node's states are in `FlagW`**: controls `c0` or off the flag load;
at `c0`, `hG` and `hX` of `flagW_mk`. -/
theorem nodeW_flag {n : ND} (h0 : Flag0 lbl lsize c0 A) (hc : ∀ σ c, n.J σ c → c = c0 ∨ FlagOff lbl c)
    (hG : ∀ s, At exe endPc R F n s c0 → ∀ kl (k' : Val → EvTree State),
      isa.exec s = some (.load kl false ⟨A, 8⟩ k') →
      ∀ v, ∃ s', k' v = .done s' ∧ s'.st.2 = q ∧ s'.st.1.regs.rax.toBitVec = v.setWidth 64)
    (hX : ∀ s, At exe endPc R F n s c0 → s.st.2 = q → s.st.1.regs.rax.toBitVec ≠ 1#64) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F n := by
  intro s c hAt
  obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := id hAt
  exact ⟨flagW_mk h0 (hc σ c hJ) (fun h => by subst h; exact hG s hAt) (fun h => by subst h; exact hX s hAt),
    fun _ h => h⟩

/-- **A block whose controls are off the flag load.** -/
theorem blkW_off {n : ND} {blk : List (Directive × Nat)} (h : ∀ σ c, n.J σ c → FlagOff lbl c) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
  exact ⟨flagW_off (h σ c hJ), fun _ h => h⟩

/-- **A node whose controls are off the flag load.** -/
theorem nodeW_off {n : ND} (h : ∀ σ c, n.J σ c → FlagOff lbl c) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, -, -, hJ⟩
  exact ⟨flagW_off (h σ c hJ), fun _ h => h⟩

/-- A `syscall` is no load. -/
theorem syscall_noLoad {s : State} {sz : Nat} (hc : CellAt s (op64 .syscall) sz) {kl : LoadKind} {L : Loc}
    {k' : Val → EvTree State} : isa.exec s ≠ some (.load kl false L k') := by
  rw [exec_syscall hc]; intro h; cases h

/-- An `xchg` is no load. -/
theorem xchg_noLoad {s : State} {sz : Nat} {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt s (op64 (.xchg r (.mem m))) sz) {kl : LoadKind} {L : Loc}
    {k' : Val → EvTree State} : isa.exec s ≠ some (.load kl false L k') := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s sz m) 8 with
  | none =>
    rw [exec_xchg hc rfl hm]; intro h
    have h' := Option.some.inj h
    unfold EvTree.access at h'
    split at h' <;> cases h'
  | some j =>
    obtain ⟨s', h'⟩ := exec_xchg_mapped hc rfl hm
    rw [h']; intro h; cases h

/-- **The limit word is not the flag's**: `tp + 8` is outside every placed
label (`hrt`), the flag's word `A` the base of its label `w`, which has a
word (`hin`). -/
theorem tp8_ne {tp : BitVec 64} {w : TermRun.Word}
    (hrt : ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains (tp + 8#64).toNat)
    (hloc : LocRep lbl w.val A.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    tp + 8#64 ≠ A := by
  intro h
  obtain ⟨sa, hw, hsz⟩ := hin
  rw [hw] at hloc
  obtain ⟨-, hb, -⟩ := hloc
  have h1 : @LT.lt Nat _ sa.offset (lsize sa.label) := hsz
  refine hrt ⟨sa.label, A.toNat, hb, ?_⟩
  show A.toNat ≤ (tp + 8#64).toNat ∧ (tp + 8#64).toNat < A.toNat + 8 * lsize sa.label
  rw [h]; omega

/-! ## main's post-spawn pcs -/

/-- **main's pcs at the flag load's control other than `q`**: `waitRuns`
without `q` (byte `7` of `.entry`; `.then1` is past the load) and
`scc_rt_park`'s. -/
def flagRuns : List (String × Nat × Nat) :=
  [("wc_waitLoop", 0, 31), (".Lwc_waitLoop.entry", 0, 7), (".Lwc_waitLoop.entry", 8, 29),
    (".Lwc_waitLoop.else2", 0, 5), (".Lwc_waitLoop.x16", 0, 10)] ++ Spike.Lib.X64.Flow.Park.parkRuns

/-- `flagRuns` misses `q` at wake. -/
theorem flag_chk : runsNeChk SccCode.wakeCells flagRuns [(".Lwc_waitLoop.entry", 7)] = true := by
  decide +kernel

/-- **`q` is off `flagRuns`** in every layout of wake. -/
theorem wake_flagRuns [Executable.ValidLayout exe] {kp : Nat} (hl : Lays exe SccCode.wakeCells kp) :
    RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label ".Lwc_waitLoop.entry" + Int64.ofNat 7) flagRuns :=
  runsNeQ_of_chk hl flag_chk

set_option hygiene false in
/-- A block's `hX` from `flagRuns`: the run `(l, lo, hi)`, the node's offset
`c` in it, the block. -/
local macro "ne_blk " l:term:max lo:term:max hi:term:max c:term:max b:term:max : tactic =>
  `(tactic| (intro _ k _ _ hk _ hq
             have hb := (show ∀ k < ($b).length, $lo ≤ $c + cellOff $b k ∧ $c + cellOff $b k < $hi by decide) k hk
             exact absurd hq <| runsNe_at hflag (l := $l) (lo := $lo) (hi := $hi) (j := $c + cellOff $b k)
               (by simp [flagRuns, Spike.Lib.X64.Flow.Park.parkRuns]) hb.1 hb.2
               (by rw [ofNat_add']
                   refine congrArg (· + Int64.ofNat (cellOff $b k)) ?_
                   all_goals try simp only [Spike.Lib.X64.WaitLoop.N, Spike.Lib.X64.WaitLoop.x16N, xProN1, xProN2,
                     xProN3, xProN4, Spike.Lib.X64.Flow.Park.N, Int64.add_assoc]
                   all_goals first | rfl | exact (ofNat_zero' _).symm | simp)))

set_option hygiene false in
/-- A node's `hX` from `flagRuns`: the run `(l, lo, hi)`, the node's offset
`c` in it. -/
local macro "ne_one " l:term:max lo:term:max hi:term:max c:term:max : tactic =>
  `(tactic| (intro s hAt hq
             obtain ⟨_, _, _, hpc, _⟩ := hAt
             exact absurd hq <| runsNe_at hflag (l := $l) (lo := $lo) (hi := $hi) (j := $c)
               (by simp [flagRuns, Spike.Lib.X64.Flow.Park.parkRuns]) (by omega) (by omega)
               (by rw [hpc]
                   all_goals try simp only [Spike.Lib.X64.WaitLoop.N, xProN2, Spike.Lib.X64.Flow.Park.N,
                     Spike.Lib.X64.Flow.Park.pcSys, Int64.add_assoc]
                   all_goals first | rfl | exact (ofNat_zero' _).symm | simp)))

section Loop

open Spike.Lib.X64.WaitLoop

variable {x : String} {a : At} {e : Expr} {ty : Ty} {w : TermRun.Word} {ms : MemSide isa}
  {fp ra tp sp : BitVec 64}

/-- **`wc_waitLoop`'s states are in `FlagW`** (`LoopW`, at `seg_waitLoopW`'s
region bounds), `q` the `n5` node's pc: the loop's control at `wlBody`
(`hwb`), its load's word `w` the untagged locative with base `A` inside its
label (`hloc`, `hin'`), every pc of `c0` but `q` off `q` (`hflag`), and the
prologue's limit word not the flag's (`htp8`). -/
theorem loopW_flag [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hq : q = (_root_.Executable.labels exe).label ".Lwc_waitLoop.entry" + Int64.ofNat 7)
    (hflag : RunsNe (_root_.Executable.labels exe).label q flagRuns)
    (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e)
    (hev : TermRun.evalAt c0.env a = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hin' : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) (htp8 : tp + 8#64 ≠ A) :
    LoopW (fun s c => FlagW lbl lsize q s c) ms exe endPc R F c0 x e ty
      (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A fp ra tp sp := by
  have h0 := flag0_of (lsize := lsize) hwb hterm hev hloc hin'
  have hP := fun c => flagOff_past (lbl := lbl) (ty := ty) (ms := ms) (c := c) hwb hterm
  have hnp : ¬ Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c0 := fun h =>
    (hP c0 h).1 hwb
  have hin2 := hin
  simp only [waitIn, Bool.and_eq_true, and_assoc] at hin2
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, -⟩ := hin2
  have hpro2 := hpro
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hpro2
  obtain ⟨g0, p0, p1, p2, p3, p4, -⟩ := hpro2
  have e0 := label_labelGapB hp g0
  have e4 : (_root_.Executable.labels exe).label "wc_waitLoop" + 1 + 3 =
      (_root_.Executable.labels exe).label ".Lwc_waitLoop.chk" := by
    rw [e0, Int64.add_assoc]; rfl
  have hlo' : R.lo ≤ -8 - (16 : Int64).toInt := by
    have : (16 : Int64).toInt = 16 := by decide
    omega
  have hhi' : (0 : Int) ≤ R.hi := by omega
  refine {
    pro := {
      w0 := blkW_flag (xHead_ok (lo := -8 - (16 : Int64).toInt) (hi := 0) (by decide) (Int.le_refl _)) hR hlo'
        hhi' (code_field hp hend p0 (ofNat_zero' _)) h0 (fun _ _ hJ => .inl hJ.1)
        (by ne_blk "wc_waitLoop" 0 31 0 xHead)
      w1 := blkW_flag (xLea_ok (lo := -8 - (16 : Int64).toInt) (hi := 0) 16 5) hR hlo' hhi'
        (code_field hp hend p1 (by show _ = _ + 1 + 3; rw [e4, ofNat_zero'])) h0
        (fun _ _ ⟨_, hJ, _⟩ => .inl hJ.1) (by ne_blk "wc_waitLoop" 0 31 4 (xLea 16 5))
      w2 := nodeW_flag h0 (fun _ _ ⟨_, hJ, _⟩ => .inl hJ.1)
        (fun s ⟨he, hn, hdc, hpc, σ, hA, _, hJ⟩ kl k' hx => ?_) (by ne_one "wc_waitLoop" 0 31 9)
      w3 := blkW_flag (xCmp_ok (lo := -8 - (16 : Int64).toInt) (hi := 0) _ ".Lwc_waitLoop.stk" 3 2) hR hlo' hhi'
        (code_field hp hend p3 (by show _ = _ + 1 + 3 + _ + _; rw [e4, ofNat_add'])) h0
        (fun _ _ ⟨_, _, hJ, _⟩ => .inl hJ.1) (by ne_blk "wc_waitLoop" 0 31 18 (xCmp ".Lwc_waitLoop.stk" 3 2))
      w4 := blkW_flag (xFr_ok (lo := -8 - (16 : Int64).toInt) (hi := 0) 16 4 [(.rdi, -8, 4)] (by decide)) hR
        hlo' hhi' (code_field hp hend p4 (by
          show _ = _ + 1 + 3 + _ + _ + _ + _; rw [e4, ofNat_add', ofNat_add', ofNat_add'])) h0
        (fun _ _ ⟨_, _, hJ, _⟩ => .inl hJ.1) (by ne_blk "wc_waitLoop" 0 31 23 (xFr 16 4 [(.rdi, -8, 4)])) }
    entry := blkW_flag b4_ok hR hlo hhi (code_field hp hend h4 (ofNat_zero' _)) h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk ".Lwc_waitLoop.entry" 0 7 0 b4)
    ld := nodeW_flag h0 (fun _ _ hJ => .inl hJ.1.1)
      (fun s ⟨he, hn, hdc, hpc, σ, hA, _, hJ⟩ kl k' hx => ?_) (by ne_one ".Lwc_waitLoop.entry" 0 7 4)
    n5 := blkW_flag b5_ok hR hlo hhi (code_field hp hend h5 rfl) h0
      (fun _ c hJ => by
        obtain ⟨-, ⟨-, hp⟩ | ⟨-, rfl⟩⟩ := hJ
        · exact .inr (hP c hp)
        · exact .inl rfl)
      (fun σ k m hJ hk hA hpq => by
        rcases k with _ | k
        · obtain ⟨-, ⟨-, hp⟩ | ⟨h1, -⟩⟩ := hJ
          · exact (hnp hp).elim
          · rw [hA.regs]; exact h1
        · have hb := (show ∀ k < b5.length, 0 < k → 8 ≤ 7 + cellOff b5 k ∧ 7 + cellOff b5 k < 29 by decide)
            (k + 1) hk (Nat.succ_pos _)
          refine absurd hpq (runsNe_at hflag (l := ".Lwc_waitLoop.entry") (lo := 8) (hi := 29)
            (by simp [flagRuns]) hb.1 hb.2 ?_)
          rw [ofNat_add']; simp only [N]; rfl)
    n6 := blkW_flag b6_ok hR hlo hhi (code_field hp hend h6 rfl) h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk ".Lwc_waitLoop.entry" 8 29 27 b6)
    then1 := blkW_flag b7_ok hR hlo hhi (code_field hp hend h7 (ofNat_zero' _)) h0
      (fun _ c hJ => .inr (hP c hJ.2.1)) (fun _ _ _ hJ => (hnp hJ.2.1).elim)
    else2 := blkW_flag b8_ok hR hlo hhi (code_field hp hend h8 (ofNat_zero' _)) h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk ".Lwc_waitLoop.else2" 0 5 0 b8)
    x16 := blkW_flag b9_ok hR hlo hhi (code_field hp hend h9 (ofNat_zero' _)) h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk ".Lwc_waitLoop.x16" 0 10 0 b9) }
  -- the prologue's limit load `movq %fs:8, %r11`: `tp + 8`, not the flag's word
  · have hc : CellAt s (fsDir .r11 8) 9 :=
      (code_field hp hend p2 (by show _ = _ + 1 + 3 + _; rw [e4]) s he hn).cell0 rfl rfl hpc
    obtain ⟨σ0, hJ0, rfl⟩ := hJ
    have ha : fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = tp + 8#64 := by
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs, xS2, xS1, hdRegs, Reg64s.set64,
        hJ0.2.2.2.2.2]
    cases hm : Mem.loadInt s.st.1.dmem (tp + 8#64) 8 with
    | some j => rw [exec_movfs_load_mapped hc ha hm] at hx; cases hx
    | none =>
      rw [exec_movfs_load_agrees hc ha hm (agrees_of_decls hdc _ _)] at hx
      injection hx with hx
      injection hx with _ _ hL
      injection hL with hA'
      exact (htp8 hA').elim
  -- the flag load `movq (%rcx), %rax`: lands at `q` with the value in `%rax`
  · have hc : CellAt s (ldDir .rcx 0 .rax) 3 := (code_field hp hend hld rfl s he hn).cell0 rfl rfl hpc
    have ha : eaddr s 3 (mB .rcx 0) = A := (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs, hJ.2]; simp)
    cases hm : Mem.loadInt s.st.1.dmem A 8 with
    | some j => rw [exec_load_mapped hc ha hm] at hx; cases hx
    | none =>
      rw [exec_load_agrees hc ha hm (agrees_of_decls hdc _ _)] at hx
      simp only [Option.some.injEq] at hx
      obtain ⟨-, -, -, rfl⟩ := hx
      refine fun v => ⟨_, rfl, ?_, ?_⟩
      · show s.st.2 + Int64.ofNat 3 = q
        rw [hpc, hq]; simp only [N, Int64.add_assoc]; rfl
      · simp [Reg64s.set, Reg64s.set64]

/-- **The exit tail's block is in `FlagW`**: past the load. -/
theorem exitW0_flag {blk : List (Directive × Nat)} (hwb : c0.term = wlBody)
    (hterm : c0.term = .let_ x (.load true a) e) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (exitN c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A fp ra tp sp) blk :=
  blkW_off fun _ _ hJ => flagOff_past hwb hterm hJ.1

/-- **The exit tail's `syscall` state is in `FlagW`**: past the load. -/
theorem exitW1_flag (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (exitNP (exitN c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A fp ra tp sp)) :=
  nodeW_off fun _ _ ⟨_, _, hJ, _⟩ => flagOff_past hwb hterm hJ.1

end Loop

section Park

open Spike.Lib.X64.Flow.Park

set_option hygiene false in
/-- A park node's control is the loop's `c0`. -/
local macro "parkC" : term =>
  `(fun _ _ h => .inl (by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1))

/-- **`scc_rt_park`'s states are in `FlagW`**: their control is the loop's
`c0`, their instructions no load of the flag's word (blocks, the `xchg`s,
the `syscall`, the thread pointer's load at `tp ≠ A`, `htp`), their pcs off
`q` (`hflag`). -/
theorem parkGW_flag {rbp0 ra tp : BitVec 64} (hR : R.OK) (hlo : R.lo ≤ -56) (hhi : 8 ≤ R.hi)
    (hcode : Code c0 rbp0 ra tp exe endPc)
    (hflag : RunsNe (_root_.Executable.labels exe).label q flagRuns) (h0 : Flag0 lbl lsize c0 A)
    (htp : tp ≠ A) :
    ParkGW (fun s c => FlagW lbl lsize q s c) exe endPc R F c0 rbp0 ra tp := by
  refine {
    e := blkW_flag b0_ok hR hlo hhi hcode.e h0 parkC (by ne_blk "scc_rt_park" 0 8 0 b0)
    fsl := nodeW_flag h0 parkC (fun s ⟨he, hn, hdc, hpc, σ, hA, _, hJ⟩ kl k' hx => ?_)
      (by ne_one ".Lscc_rt_park.entry" 0 50 0)
    n1 := blkW_flag b1_ok hR hlo hhi hcode.n1 h0 parkC (by ne_blk ".Lscc_rt_park.entry" 0 50 9 b1)
    xchg1 := nodeW_flag h0 parkC
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (xchg_noLoad ((hcode.xchg1 s he hn).cell0 rfl rfl hpc) hx).elim)
      (by ne_one ".Lscc_rt_park.entry" 0 50 24)
    n2 := blkW_flag b2_ok hR hlo hhi hcode.n2 h0 parkC (by ne_blk ".Lscc_rt_park.entry" 0 50 28 b2)
    n3 := blkW_flag b3_ok hR hlo hhi hcode.n3 h0 parkC (by ne_blk ".Lscc_rt_park.entry" 0 50 48 b3)
    wait := blkW_flag b4_ok hR hlo hhi hcode.wait h0 parkC (by ne_blk ".Lscc_rt_park.wait" 0 92 0 b4)
    sys := nodeW_flag h0 parkC
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (syscall_noLoad ((hcode.sys s he hn).cell0 rfl rfl hpc) hx).elim)
      (by ne_one ".Lscc_rt_park.wait" 0 92 62)
    n5 := blkW_flag b5_ok hR hlo hhi hcode.n5 h0 parkC (by ne_blk ".Lscc_rt_park.wait" 0 92 64 b5)
    xchg2 := nodeW_flag h0 parkC
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (xchg_noLoad ((hcode.xchg2 s he hn).cell0 rfl rfl hpc) hx).elim)
      (by ne_one ".Lscc_rt_park.wait" 0 92 79)
    n6 := blkW_flag b6_ok hR hlo hhi hcode.n6 h0 parkC (by ne_blk ".Lscc_rt_park.wait" 0 92 83 b6)
    done := blkW_flag b7_ok hR hlo hhi hcode.done h0 parkC (by ne_blk ".Lscc_rt_park.done" 0 5 0 b7) }
  -- the thread pointer's load `movq %fs:0, %rax`: `tp`, not the flag's word
  have hc : CellAt s (fsDir .rax 0) 9 := (hcode.fsl s he hn).cell0 rfl rfl hpc
  have ha : fsAddr s 9 { base := none, idx := none, disp := .int64 0 } = tp := by
    simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs, hJ.2.2.2]
  cases hm : Mem.loadInt s.st.1.dmem tp 8 with
  | some j => rw [exec_movfs_load_mapped hc ha hm] at hx; cases hx
  | none =>
    rw [exec_movfs_load_agrees hc ha hm (agrees_of_decls hdc _ _)] at hx
    injection hx with hx
    injection hx with _ _ hL
    injection hL with hA'
    exact (htp hA').elim

end Park

/-- **The parent's states are in `FlagW`**: its control `cP` is at neither
`wlBody` nor `wlIf` (`hcPf`). -/
theorem parentW_flag {cP : Ctl} {fp ra tp : BitVec 64} (hcPf : cP.term ≠ wlBody ∧ cP.term ≠ wlIf) :
    ParentW (fun s c => FlagW lbl lsize q s c) exe endPc R F cP A fp ra tp :=
  have hP : FlagOff lbl cP := ⟨hcPf.1, fun h => absurd h hcPf.2⟩
  { wts := nodeW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wje := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wx22 := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wbs := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
    wsp := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP }

end Spike.Lib.X64WakeMainF

/-- info: 'Spike.Lib.X64WakeMainF.loopW_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainF.loopW_flag
/-- info: 'Spike.Lib.X64WakeMainF.parkGW_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainF.parkGW_flag
/-- info: 'Spike.Lib.X64WakeMainF.tp8_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainF.tp8_ne
/-- info: 'Spike.Lib.X64WakeMainF.wake_flagRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainF.wake_flagRuns
